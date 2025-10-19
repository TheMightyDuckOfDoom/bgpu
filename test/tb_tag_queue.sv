// Copyright 2025 Tobias Senti
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

/// Testbench for Tag Queue
module tb_tag_queue #(
    // Simulation parameters
    parameter int unsigned MaxWaitCycles = 1,
    parameter int unsigned MaxSimCycles  = 10000,
    parameter int unsigned TagsToFree    = 1000,

    // Simulation time parameters
    parameter time ClkPeriod = 10ns,
    parameter time ApplDelay = 1ns,
    parameter time AcqDelay  = 8ns,

    /// Number of inflight instructions per warp
    parameter int unsigned NumTags = 16,
    /// Number of tags to get at the same time
    parameter int unsigned NumTagOut = 2,
    /// Number of tags to free at the same time
    parameter int unsigned NumTagIn = 2
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
    logic [NumTagIn-1:0] free;
    tag_t [NumTagIn-1:0] free_tag;

    // Get signals
    logic [NumTagOut-1:0] get, valid;
    tag_t [NumTagOut-1:0] tag_out;

    tag_t tag_out_queue[$];

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
    for (genvar i = 0; i < NumTagOut; i++) begin : gen_get_sub
        rand_stream_slv #(
            .data_t       ( tag_t         ),
            .ApplDelay    ( ApplDelay     ),
            .AcqDelay     ( AcqDelay      ),
            .MinWaitCycles( 1             ),
            .MaxWaitCycles( MaxWaitCycles ),
            .Enqueue      ( 1'b0          )
        ) i_get_sub (
            .clk_i ( clk   ),
            .rst_ni( rst_n ),

            .data_i ( tag_out[i] ),
            .valid_i( valid  [i] ),
            .ready_o( get    [i] )
        );

        initial begin
            while(1) begin
                @(posedge clk);
                #AcqDelay;
                if (get[i] && valid[i]) begin
                    tag_out_queue.push_back(tag_out[i]);
                end
            end
        end
    end

    initial begin
        int unsigned wait_cycles, index, random_free;

        // Wait for reset
        @(posedge clk);
        while(!rst_n) @(posedge clk);

        while(1) begin
            @(posedge clk);
            #ApplDelay;
            free = '0;

            wait_cycles = $urandom_range(0, MaxWaitCycles);
            if (wait_cycles > 0) begin
                repeat(wait_cycles) @(posedge clk);
                #ApplDelay;
            end

            for(int i = 0; i < NumTagIn; i++) begin : loop_free_tags
                // Randomly choose to free a tag if there are any in the queue
                if (tag_out_queue.size() > 0) begin
                    random_free = $urandom_range(0, 1);
                    free[i] = random_free[0];
                    if (free[i]) begin
                        // Get random tag from queue
                        index    = $urandom_range(1, tag_out_queue.size());
                        while (index > 0) begin
                            tag_out_queue.push_back(tag_out_queue.pop_front());
                            index--;
                        end

                        free_tag[i] = tag_out_queue.pop_front();
                    end
                end
            end : loop_free_tags
        end
    end

    // #######################################################################################
    // # DUT Instantiation                                                                   #
    // #######################################################################################

    tag_queue #(
        .NumTags  ( NumTags   ),
        .NumTagOut( NumTagOut ),
        .NumTagIn ( NumTagIn  )
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
            $display("Cycle: %0d", cycles);

            #AcqDelay;

            for (int unsigned i = 0; i < NumTagOut; i++) begin : loop_tag_outs
                if (get[i] && valid[i]) begin : got_tag
                    got_tags++;
                    $display("[%0d] Got tag: %0d at cycle %0d", i, tag_out[i], cycles);
                    
                    assert (tag_out_queue.size() < NumTags)
                        else $error("Queue size exceeded: %0d >= %0d", tag_out_queue.size(),
                            NumTags);

                    // Check that no other output got the same tag
                    for (int unsigned j = 0; j < NumTagOut; j++) begin
                        if ((j != i) && get[j] && valid[j]) begin
                            assert (tag_out[i] != tag_out[j])
                                else $error("Tag %0d found on multiple outputs (%0d and %0d)",
                                    tag_out[i], i, j);
                        end
                    end

                    occurances = 0;
                    for (int unsigned tidx = 0; tidx < tag_out_queue.size(); tidx++) begin
                        if (tag_out_queue[tidx] == tag_out[i]) begin
                            occurances++;
                        end
                    end
                    assert (occurances == 0)
                        else $error("Tag %0d found %0d times in queue, expected 0", tag_out[i],
                            occurances);
                end : got_tag
            end : loop_tag_outs

            // Check if we freed a tag
            for (int unsigned i = 0; i < NumTagIn; i++) begin : loop_free_tags_check
                if (free[i]) begin
                    freed_tags++;
                    $display("[%0d] Freed tag: %0d at cycle %0d", i, free_tag[i], cycles);
                end
            end : loop_free_tags_check

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
        
        assert (freed_tags == TagsToFree)
            else $error("Did not free enough tags: %0d != %0d", freed_tags, TagsToFree);

        $finish;
    end

endmodule : tb_tag_queue
