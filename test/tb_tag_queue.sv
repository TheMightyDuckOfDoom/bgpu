// Copyright 2025 Tobias Senti
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

/// Testbench for Tag Queue
module tb_tag_queue #(
    // Simulation parameters
    parameter int unsigned MaxWaitCycles = 0,
    parameter int unsigned MaxSimCycles  = 2000,
    parameter int unsigned TagsToFree    = 100,

    // Simulation time parameters
    parameter time ClkPeriod = 10ns,
    parameter time ApplDelay = 1ns,
    parameter time AcqDelay  = 8ns,

    /// Number of inflight instructions per warp
    parameter int unsigned NumTags = 16
) ();

    // #######################################################################################
    // # Local Parameters                                                                    #
    // #######################################################################################

    localparam int unsigned TagWidth = $clog2(NumTags);

    // #######################################################################################
    // # Type Definitions                                                                    #
    // #######################################################################################

    typedef logic [TagWidth-1:0] tag_t;

    // #######################################################################################
    // # Signals                                                                             #
    // #######################################################################################

    // Clock and Reset
    logic clk, rst_n;

    // Free signals
    logic free;
    tag_t free_tag;

    // Get signals
    logic get, valid;
    tag_t tag_out;

    // #######################################################################################
    // # Clock generation                                                                    #
    // #######################################################################################

    clk_rst_gen #(
        .ClkPeriod   ( ClkPeriod ),
        .RstClkCycles( 3         )
    ) i_clk_rst_gen (
        .clk_o ( clk   ),
        .rst_no( rst_n )
    );

    // #######################################################################################
    // # Stimulus                                                                            #
    // #######################################################################################

    // Random subordinate to get a tag
    rand_stream_slv #(
        .data_t       ( tag_t         ),
        .ApplDelay    ( ApplDelay     ),
        .AcqDelay     ( AcqDelay      ),
        .MinWaitCycles( 0             ),
        .MaxWaitCycles( MaxWaitCycles ),
        .Enqueue      ( 1'b1          )
    ) i_get_sub (
        .clk_i ( clk   ),
        .rst_ni( rst_n ),

        .data_i ( tag_out ),
        .valid_i( valid   ),
        .ready_o( get     )
    );

    initial begin
        int unsigned wait_cycles, index, random_free;

        // Wait for reset
        @(posedge clk);
        while(!rst_n) @(posedge clk);

        while(1) begin
            @(posedge clk);
            #ApplDelay;
            free = 1'b0;

            wait_cycles = $urandom_range(0, MaxWaitCycles);
            if (wait_cycles > 0) begin
                repeat(wait_cycles) @(posedge clk);
                #ApplDelay;
            end

            // Randomly choose to free a tag if there are any in the queue
            if (i_get_sub.gen_queue.queue.size() > 0) begin
                random_free = $urandom_range(0, 1);
                free = random_free[0];
                if (free) begin
                    // Get random tag from queue
                    index    = $urandom_range(1, i_get_sub.gen_queue.queue.size());
                    while (index > 0) begin
                        i_get_sub.gen_queue.queue.push_back(i_get_sub.gen_queue.queue.pop_front());
                        index--;
                    end

                    free_tag = i_get_sub.gen_queue.queue.pop_front();
                    if (free_tag == tag_out)
                        free = 1'b0;
                end
            end
        end
    end

    // #######################################################################################
    // # DUT Instantiation                                                                   #
    // #######################################################################################

    tag_queue #(
        .NumTags(NumTags)
    ) i_tag_queue (
        .clk_i ( clk   ),
        .rst_ni( rst_n ),

        .free_i( free     ),
        .tag_i ( free_tag ),

        .get_i  ( get     ),
        .valid_o( valid   ),
        .tag_o  ( tag_out )
    );

    // #######################################################################################
    // # Testbench logic                                                                     #
    // #######################################################################################

    initial begin
        int unsigned got_tags, freed_tags, cycles, occurances;

        cycles      = 0;
        got_tags    = 0;
        freed_tags  = 0;

        // Wait for reset
        @(posedge clk);
        wait(!rst_n);

        while(cycles < MaxSimCycles && freed_tags < TagsToFree) begin
            @(posedge clk);
            cycles++;

            #ApplDelay;
            #1ns;

            if (get && valid) begin
                got_tags++;
                $display("Got tag: %0d at cycle %0d", tag_out, cycles);
                assert (i_get_sub.gen_queue.queue.size() < NumTags)
                    else $error("Queue size exceeded: %0d >= %0d", i_get_sub.gen_queue.queue.size(),
                        NumTags);

                occurances = 0;
                for (int unsigned i = 0; i < i_get_sub.gen_queue.queue.size(); i++) begin
                    if (i_get_sub.gen_queue.queue[i] == tag_out) begin
                        occurances++;
                    end
                end
                assert (occurances == 0)
                    else $error("Tag %0d found %0d times in queue, expected 0", tag_out,
                        occurances);
            end

            // Check if we freed a tag
            if (free) begin
                freed_tags++;
                $display("Freed tag: %0d at cycle %0d", free_tag, cycles);
            end

        end

        $display("Simulation finished after %0d cycles", cycles);
        $display("Got %0d tags, Freed %0d tags", got_tags, freed_tags);

        assert (got_tags > 0)
            else $error("At least one tag should have been got during the simulation");

        assert (freed_tags > 0)
            else $error("At least one tag should have been freed during the simulation");

        assert (got_tags >= freed_tags)
            else $error("Got tags (%0d) should be greater than or equal to freed tags (%0d)",
            got_tags, freed_tags);

        $finish;
    end

endmodule : tb_tag_queue
