/**
 * branch_predictor.sv - Simple Branch Predictor for eCPU
 * 
 * A simple branch predictor that always predicts not taken.
 * This is a placeholder for future more sophisticated implementations.
 *
 * Author: Ethan
 * Date: 2024
 */

`default_nettype none

module branch_predictor #(
    parameter int ADDR_WIDTH = 32        // Address width
)(
    // Clock and reset
    input  wire logic                   clk_i,          // System clock
    input  wire logic                   rst_i,          // Active-high reset
    
    // Prediction request
    input  wire logic [ADDR_WIDTH-1:0] pc_i,           // PC for prediction
    output wire logic                   prediction_o,   // Predicted taken (1) or not taken (0)
    output wire logic [ADDR_WIDTH-1:0] target_o,       // Predicted target address
    
    // Prediction update
    input  wire logic                   update_i,       // Update prediction
    input  wire logic [ADDR_WIDTH-1:0] update_pc_i,    // PC being updated
    input  wire logic                   actual_taken_i, // Actual branch result
    input  wire logic [ADDR_WIDTH-1:0] actual_target_i // Actual target address
);

    // Simple predictor: always predict not taken
    assign prediction_o = 1'b0;
    assign target_o = {ADDR_WIDTH{1'b0}};
    
    // Update logic (placeholder for future implementation)
    // For now, just ignore updates

endmodule

`default_nettype wire