// Copyright 2026 Tobias Senti
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

/// Testbench for Fop Time-Multiplexer
// Does not check the numeric results, just if the time-multiplexing works
module tb_fop_tmux #(
    // Simulation parameters
    parameter int unsigned MaxWaitCycles  = 1,
    parameter int unsigned MaxSimCycles   = 10000,
    parameter int unsigned RequestsToMake = 1000,

    // Simulation time parameters
    parameter time ClkPeriod = 10ns,
    parameter time ApplDelay = 1ns,
    parameter time AcqDelay  = 8ns,

    // Number of threads in a warp
    parameter int unsigned WarpWidth = 8,
    // Number of FOp-Units present
    parameter int unsigned NumFopUnits = 2,
    // Width of the Operands
    parameter int unsigned DataWidth = 32,
    // Width of the Tag
    parameter int unsigned TagWidth = 4
) ();

    // #######################################################################################
    // # Type Definitions                                                                    #
    // #######################################################################################

    // Data
    typedef logic [DataWidth-1:0] data_t;

    // Tag
    typedef logic [TagWidth-1:0] tag_t;

    // Request
    typedef struct packed {
        logic  [WarpWidth-1:0] valid;
        tag_t                  tag;
        data_t [WarpWidth-1:0] operand_a;
        data_t [WarpWidth-1:0] operand_b;
    } request_t;

    // #######################################################################################
    // # Signals                                                                             #
    // #######################################################################################

    // Clock and Reset
    logic clk, rst_n;

    // Request
    request_t req;
    logic req_valid, req_ready;

    // Responses
    logic  [WarpWidth-1:0] res_valid;
    tag_t  [WarpWidth-1:0] res_tag;
    data_t [WarpWidth-1:0] res_result;

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
    // # Stream Master and Subordinates                                                      #
    // #######################################################################################

    // Request
    rand_stream_mst #(
        .data_t       ( request_t     ),
        .ApplDelay    ( ApplDelay     ),
        .AcqDelay     ( AcqDelay      ),
        .MinWaitCycles( 0             ),
        .MaxWaitCycles( MaxWaitCycles )
    ) i_fetch_req (
        .clk_i  ( clk       ),
        .rst_ni ( rst_n     ),
        .valid_o( req_valid ),
        .data_o ( req       ),
        .ready_i( req_ready )
    );

    // #######################################################################################
    // # DUT                                                                                 #
    // #######################################################################################

    fop_tmux #(
        .WarpWidth  ( WarpWidth   ),
        .NumFopUnits( NumFopUnits ),
        .DataWidth  ( DataWidth   ),
        .tag_t      ( tag_t       )
    ) i_div (
        .clk_i ( clk   ),
        .rst_ni( rst_n ),

        .tag_i      ( req.tag                    ),
        .ready_o    ( req_ready                  ),
        .valid_i    ( req_valid ? req.valid : '0 ),
        .operand_a_i( req.operand_a              ),
        .operand_b_i( req.operand_b              ),

        .valid_o ( res_valid  ),
        .tag_o   ( res_tag    ),
        .result_o( res_result )
    );

    // ########################################################################################
    // # Simulation Logic                                                                     #
    // ########################################################################################

    initial begin : simulation_logic
        int unsigned requests_issued, cycles;
        int unsigned results_received [WarpWidth];

        cycles           = 0;
        requests_issued  = 0;
        for (int i = 0; i < WarpWidth; i++)
            results_received[i] = 0;

        $timeformat(-9, 0, "ns", 12);
        // configure VCD dump
        $dumpfile("fop_tmux.vcd");
        $dumpvars();

        while (cycles < MaxSimCycles && requests_issued < RequestsToMake) begin
            @(posedge clk);
            #AcqDelay;

            if (req_valid && req_ready) begin
                requests_issued++;
                $display("Cycle %0d: Issued request: Valid: %b Tag: %0d",
                    cycles, req.valid, req.tag);
            end

            for (int i = 0; i < WarpWidth; i++) begin
                if (res_valid[i]) begin
                    results_received[i]++;
                    $display("Cycle %0d: Result %0d: Tag: %0d",
                        cycles, i, res_tag[i]);
                end
            end

            cycles++;
        end

        assert (cycles < MaxSimCycles)
        else $error("Reached MaxSimCycles: %d", cycles);

        assert (requests_issued == RequestsToMake)
        else $error("Only made %d requests", requests_issued);

        for (int i = 0; i < WarpWidth; i++) begin
            assert (results_received[i] > 0)
            else $error("%d: received 0 responses!", i);

            $display("%0d: Received %0d results", i, results_received[i]);
        end

        $display("Finished after %d cycles!", cycles);
        $finish;
    end : simulation_logic

    // Check Logic
    for (genvar i = 0; i < WarpWidth; i++) begin : gen_check_logic
        tag_t requests [$];
        tag_t results  [$];

        initial begin : capture_request
            while (1) begin
                @(posedge clk);
                #AcqDelay;
                if (req_valid && req_ready && req.valid[i]) begin
                    requests.push_back(req.tag);
                end
            end
        end : capture_request

        initial begin : capture_response
            while (1) begin
                @(posedge clk);
                #AcqDelay;
                if (res_valid[i]) begin
                    results.push_back(res_tag[i]);
                end
            end
        end : capture_response

        initial begin : check_result
            tag_t exp, act;
            while (1) begin
                @(posedge clk);
                if ((requests.size() == 0) || (results.size() == 0))
                    continue;

                exp = requests.pop_front();
                act = results.pop_front();

                if (exp !== act) begin
                    $error("%d: Expected: Tag: %0d != Actual: Tag: %0d",
                        i, exp, act);
                end
            end
        end : check_result
    end : gen_check_logic

endmodule : tb_fop_tmux
