/**
 * writeback.sv - Writeback Stage for eCPU
 * 
 * Final pipeline stage that selects the appropriate data to write back
 * to the register file (ALU result or memory data)
 *
 * Author: Ethan
 * Date: 2024
 */

`default_nettype none

module writeback #(
    parameter int XLEN = 32,              // Data width (32-bit for RV32I)
    parameter int REG_ADDR_WIDTH = 5,     // Register address width
    parameter int ILEN = 32               // Instruction width
)(
    // Clock and reset
    input  wire logic                        clk_i,         // System clock
    input  wire logic                        rst_i,         // Active-high reset
    
    // Inputs from memory stage
    input  wire logic [REG_ADDR_WIDTH-1:0]  rd_addr_i,     // Destination register address
    input  wire logic [XLEN-1:0]            alu_result_i,  // ALU result
    input  wire logic [XLEN-1:0]            mem_data_i,    // Memory read data
    input  wire logic                        reg_write_i,   // Register write enable
    input  wire logic [ILEN-1:0]            instr_i,       // Instruction for decoding
    
    // Outputs to register file
    output wire logic [REG_ADDR_WIDTH-1:0]  rd_addr_o,     // Destination register address
    output wire logic [XLEN-1:0]            rd_data_o,     // Data to write to register
    output wire logic                        reg_write_o    // Register write enable
);

    // ========================================
    // Instruction Decoding
    // ========================================
    
    // RISC-V instruction encoding
    logic [6:0] opcode;
    logic is_load_instr;
    
    assign opcode = instr_i[6:0];
    
    // RISC-V Load instructions have opcode 0000011 (0x03)
    assign is_load_instr = (opcode == 7'b0000011);
    
    // ========================================
    // Data Selection Logic
    // ========================================
    
    always_comb begin
        if (is_load_instr) begin
            rd_data_o = mem_data_i;     // Load instruction - use memory data
        end else begin
            rd_data_o = alu_result_i;   // ALU/other instruction - use ALU result
        end
    end
    
    // ========================================
    // Pass-through Control Signals
    // ========================================
    
    assign rd_addr_o = rd_addr_i;
    assign reg_write_o = reg_write_i;
    
    // ========================================
    // Debug and Verification Support
    // ========================================
    
    `ifdef DEBUG
        // Debug: Display writeback operation
        always_ff @(posedge clk_i) begin
            if (!rst_i && reg_write_i && rd_addr_i != 5'b00000) begin
                $display("DEBUG WB: Writing 0x%08x to x%0d (mem_to_reg=%b)", 
                    rd_data_o, rd_addr_i, mem_to_reg_i);
            end
        end
    `endif
    
    // ========================================
    // Assertions for Verification
    // ========================================
    
    `ifdef FORMAL
        // Formal verification properties
        
        // Register x0 should never be written
        property no_write_to_x0;
            @(posedge clk_i) disable iff (rst_i)
            reg_write_o |-> (rd_addr_o != 5'b00000);
        endproperty
        
        // Data selection should be consistent
        property data_selection_consistent;
            @(posedge clk_i) disable iff (rst_i)
            mem_to_reg_i |-> (rd_data_o == mem_data_i) &&
            !mem_to_reg_i |-> (rd_data_o == alu_result_i);
        endproperty
        
        // Address and write enable pass-through
        property passthrough_signals;
            @(posedge clk_i) disable iff (rst_i)
            (rd_addr_o == rd_addr_i) && (reg_write_o == reg_write_i);
        endproperty
        
        // Bind assertions
        assert property (no_write_to_x0) else $error("Attempting to write to x0");
        assert property (data_selection_consistent) else $error("Inconsistent data selection");
        assert property (passthrough_signals) else $error("Signal passthrough failed");
    `endif

endmodule

`default_nettype wire 