/**
 * fetch.sv - Fetch Stage for eCPU
 * 
 * Pipeline stage that handles instruction fetching:
 * - Program counter (PC) generation and updating
 * - Instruction memory interface via Wishbone B4
 * - Branch/jump target handling
 * - Pipeline stall support
 *
 * Author: Ethan
 * Date: 2024
 */

`default_nettype none

module fetch #(
    parameter int XLEN = 32,              // Data width (32-bit for RV32I)
    parameter int ADDR_WIDTH = 32,        // Address width
    parameter bit ENABLE_BRANCH_PREDICTION = 1  // Enable branch prediction
)(
    // Clock and reset
    input  wire logic                    clk_i,            // System clock
    input  wire logic                    rst_i,            // Active-high reset
    
    // Control signals
    input  wire logic                    stall_i,          // Pipeline stall
    input  wire logic                    branch_taken_i,   // Branch taken from execute stage
    input  wire logic [ADDR_WIDTH-1:0]  branch_target_i,  // Branch target address
    
    // Branch prediction interface
    input  wire logic                    bp_prediction_i,  // Branch prediction
    input  wire logic [ADDR_WIDTH-1:0]  bp_target_i,      // Predicted target
    
    // Instruction memory interface (Wishbone B4)
    output wire logic                    imem_cyc_o,       // Cycle signal
    output wire logic                    imem_stb_o,       // Strobe signal
    output wire logic                    imem_we_o,        // Write enable (always 0)
    output wire logic [ADDR_WIDTH-1:0]  imem_adr_o,       // Address
    output wire logic [XLEN-1:0]        imem_dat_o,       // Data out (unused)
    output wire logic [XLEN/8-1:0]      imem_sel_o,       // Byte select
    input  wire logic                    imem_ack_i,       // Acknowledge
    input  wire logic [XLEN-1:0]        imem_dat_i,       // Instruction data
    input  wire logic                    imem_err_i,       // Error signal
    
    // Outputs to decode stage
    output logic [ADDR_WIDTH-1:0]       pc_o,             // Program counter
    output logic [XLEN-1:0]             instr_o,          // Instruction
    output logic                         instr_valid_o,    // Instruction valid
    output logic                         stall_o           // Stall output
);

    // Internal signals
    logic [ADDR_WIDTH-1:0] pc_reg;
    logic [ADDR_WIDTH-1:0] pc_next;
    logic [ADDR_WIDTH-1:0] pc_plus_4;
    logic                  fetch_valid;
    logic                  pc_update_enable;
    
    // PC increment
    assign pc_plus_4 = pc_reg + 32'd4;
    
    // ========================================
    // PC Next Logic
    // ========================================
    
    always_comb begin
        if (branch_taken_i) begin
            // Branch/jump taken - use target address
            pc_next = branch_target_i;
        end else if (ENABLE_BRANCH_PREDICTION && bp_prediction_i) begin
            // Branch prediction says take branch
            pc_next = bp_target_i;
        end else begin
            // Normal increment
            pc_next = pc_plus_4;
        end
    end
    
    // ========================================
    // PC Register
    // ========================================
    
    // PC update enable: update when not stalled and memory access completes
    assign pc_update_enable = !stall_i && (imem_ack_i || !imem_cyc_o);
    
    always_ff @(posedge clk_i) begin
        if (rst_i) begin
            pc_reg <= {ADDR_WIDTH{1'b0}};  // Start at address 0
        end else if (pc_update_enable) begin
            pc_reg <= pc_next;
        end
        // Hold PC during stall
    end
    
    // ========================================
    // Instruction Memory Interface
    // ========================================
    
    // Memory access control
    assign fetch_valid = !stall_i;
    
    // Wishbone signals
    assign imem_cyc_o = fetch_valid;
    assign imem_stb_o = fetch_valid;
    assign imem_we_o = 1'b0;                    // Never write to instruction memory
    assign imem_adr_o = pc_reg;                 // Current PC
    assign imem_dat_o = {XLEN{1'b0}};          // No data output for reads
    assign imem_sel_o = 4'b1111;               // Full word access
    
    // ========================================
    // Output Logic
    // ========================================
    
    // Pass through PC and instruction
    assign pc_o = pc_reg;
    assign instr_o = imem_dat_i;
    assign instr_valid_o = imem_ack_i && !imem_err_i;
    assign stall_o = stall_i;
    
    // ========================================
    // Debug and Verification Support
    // ========================================
    
    `ifdef DEBUG
        always_ff @(posedge clk_i) begin
            if (!rst_i && pc_update_enable) begin
                $display("DEBUG FETCH: PC=0x%08x -> 0x%08x, Instr=0x%08x, Valid=%b", 
                    pc_reg, pc_next, imem_dat_i, instr_valid_o);
                
                if (branch_taken_i) begin
                    $display("DEBUG FETCH: Branch taken to 0x%08x", branch_target_i);
                end
                
                if (ENABLE_BRANCH_PREDICTION && bp_prediction_i) begin
                    $display("DEBUG FETCH: Branch predicted to 0x%08x", bp_target_i);
                end
            end
        end
    `endif
    
    // ========================================
    // Assertions for Verification
    // ========================================
    
    `ifdef FORMAL
        // Formal verification properties
        
        // PC should be word-aligned
        property pc_aligned;
            @(posedge clk_i) disable iff (rst_i)
            pc_reg[1:0] == 2'b00;
        endproperty
        
        // PC should increment by 4 when no branch
        property pc_increment;
            @(posedge clk_i) disable iff (rst_i)
            (!branch_taken_i && !bp_prediction_i && pc_update_enable) |=> 
            (pc_reg == $past(pc_reg) + 32'd4);
        endproperty
        
        // Branch target should be used when branch taken
        property branch_target_used;
            @(posedge clk_i) disable iff (rst_i)
            (branch_taken_i && pc_update_enable) |=> 
            (pc_reg == $past(branch_target_i));
        endproperty
        
        // No write to instruction memory
        property no_write_to_imem;
            @(posedge clk_i) disable iff (rst_i)
            imem_we_o == 1'b0;
        endproperty
        
        // Wishbone protocol consistency
        property wishbone_protocol;
            @(posedge clk_i) disable iff (rst_i)
            imem_stb_o |-> imem_cyc_o;
        endproperty
        
        // Bind assertions
        assert property (pc_aligned) else $error("PC not word-aligned");
        assert property (pc_increment) else $error("PC increment failed");
        assert property (branch_target_used) else $error("Branch target not used");
        assert property (no_write_to_imem) else $error("Write to instruction memory");
        assert property (wishbone_protocol) else $error("Wishbone protocol violation");
    `endif

endmodule

`default_nettype wire 