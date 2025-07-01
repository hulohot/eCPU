/**
 * eCPU_top.sv - Top-level RISC-V RV32I CPU Module
 * 
 * This is the top-level module for the eCPU RISC-V RV32I implementation.
 * It instantiates all pipeline stages and connects them together.
 *
 * Author: Ethan
 * Date: 2024
 */

`default_nettype none

module eCPU_top #(
    parameter int XLEN = 32,                    // Data width (32-bit for RV32I)
    parameter int ILEN = 32,                    // Instruction width
    parameter int ADDR_WIDTH = 32,              // Address width
    parameter int REG_ADDR_WIDTH = 5,           // Register address width (32 registers = 5 bits)
    parameter int IMEM_SIZE = 16384,            // Instruction memory size (64KB / 4)
    parameter int DMEM_SIZE = 16384,            // Data memory size (64KB / 4)
    parameter bit ENABLE_BRANCH_PREDICTION = 1  // Enable branch prediction
)(
    // Clock and reset
    input  wire logic                   clk_i,          // System clock
    input  wire logic                   rst_i,          // Active-high reset
    
    // Wishbone instruction memory interface
    output wire logic                   imem_cyc_o,     // Cycle signal
    output wire logic                   imem_stb_o,     // Strobe signal
    output wire logic                   imem_we_o,      // Write enable (always 0 for instruction fetch)
    output wire logic [ADDR_WIDTH-1:0] imem_adr_o,     // Address
    output wire logic [XLEN-1:0]       imem_dat_o,     // Data out (unused for instruction fetch)
    output wire logic [XLEN/8-1:0]     imem_sel_o,     // Byte select
    input  wire logic                   imem_ack_i,     // Acknowledge
    input  wire logic [XLEN-1:0]       imem_dat_i,     // Instruction data
    input  wire logic                   imem_err_i,     // Error signal
    
    // Wishbone data memory interface
    output wire logic                   dmem_cyc_o,     // Cycle signal
    output wire logic                   dmem_stb_o,     // Strobe signal
    output wire logic                   dmem_we_o,      // Write enable
    output wire logic [ADDR_WIDTH-1:0] dmem_adr_o,     // Address
    output wire logic [XLEN-1:0]       dmem_dat_o,     // Data out
    output wire logic [XLEN/8-1:0]     dmem_sel_o,     // Byte select
    input  wire logic                   dmem_ack_i,     // Acknowledge
    input  wire logic [XLEN-1:0]       dmem_dat_i,     // Data in
    input  wire logic                   dmem_err_i,     // Error signal
    
    // Debug interface
    output wire logic [ADDR_WIDTH-1:0] debug_pc_o,     // Current PC for debugging
    output wire logic [ILEN-1:0]       debug_instr_o,  // Current instruction
    output wire logic                   debug_valid_o,  // Debug info valid
    
    // Performance counters
    output wire logic [63:0]            cycle_count_o,  // Cycle counter
    output wire logic [63:0]            instr_count_o,  // Instruction counter
    output wire logic [63:0]            stall_count_o   // Stall counter
);

    // Internal pipeline signals
    
    // Fetch stage signals
    logic [ADDR_WIDTH-1:0] pc_f;
    logic [ILEN-1:0]       instr_f;
    logic                  instr_valid_f;
    logic                  stall_f;
    
    // Decode stage signals
    logic [ADDR_WIDTH-1:0] pc_d;
    logic [ILEN-1:0]       instr_d;
    logic                  instr_valid_d;
    logic [REG_ADDR_WIDTH-1:0] rs1_addr_d;
    logic [REG_ADDR_WIDTH-1:0] rs2_addr_d;
    logic [REG_ADDR_WIDTH-1:0] rd_addr_d;
    logic [XLEN-1:0]       rs1_data_d;
    logic [XLEN-1:0]       rs2_data_d;
    logic [XLEN-1:0]       rs1_data_regfile;
    logic [XLEN-1:0]       rs2_data_regfile;
    logic [XLEN-1:0]       imm_d;
    logic [3:0]            alu_op_d;
    logic                  alu_src_d;
    logic                  reg_write_d;
    logic                  mem_read_d;
    logic                  mem_write_d;
    logic [2:0]            mem_size_d;
    logic                  branch_d;
    logic                  jump_d;
    logic [2:0]            branch_type_d;
    logic                  stall_d;
    
    // Execute stage signals
    logic [ADDR_WIDTH-1:0] pc_e;
    logic [ILEN-1:0]       instr_e;
    logic                  instr_valid_e;
    logic [REG_ADDR_WIDTH-1:0] rd_addr_e;
    logic [XLEN-1:0]       alu_result_e;
    logic [XLEN-1:0]       rs2_data_e;
    logic                  reg_write_e;
    logic                  mem_read_e;
    logic                  mem_write_e;
    logic [2:0]            mem_size_e;
    logic                  branch_taken_e;
    logic [ADDR_WIDTH-1:0] branch_target_e;
    logic                  stall_e;
    
    // Memory stage signals
    logic [ADDR_WIDTH-1:0] pc_m;
    logic [ILEN-1:0]       instr_m;
    logic                  instr_valid_m;
    logic [REG_ADDR_WIDTH-1:0] rd_addr_m;
    logic [XLEN-1:0]       alu_result_m;
    logic [XLEN-1:0]       mem_data_m;
    logic                  reg_write_m;
    logic                  stall_m;
    
    // Writeback stage signals
    logic [REG_ADDR_WIDTH-1:0] rd_addr_w;
    logic [XLEN-1:0]       rd_data_w;
    logic                  reg_write_w;
    
    // Hazard detection and forwarding signals
    logic                  hazard_stall;
    logic [1:0]            forward_a;
    logic [1:0]            forward_b;
    
    // Branch prediction signals
    logic                  bp_prediction;
    logic [ADDR_WIDTH-1:0] bp_target;
    logic                  bp_update;
    logic                  bp_actual;
    logic [ADDR_WIDTH-1:0] bp_pc;
    
    // Performance counter registers
    logic [63:0] cycle_counter;
    logic [63:0] instr_counter;
    logic [63:0] stall_counter;
    
    // ========================================
    // Performance Counters
    // ========================================
    
    always_ff @(posedge clk_i) begin
        if (rst_i) begin
            cycle_counter <= 64'h0;
            instr_counter <= 64'h0;
            stall_counter <= 64'h0;
        end else begin
            cycle_counter <= cycle_counter + 64'h1;
            
            if (instr_valid_m && !stall_m) begin
                instr_counter <= instr_counter + 64'h1;
            end
            
            if (hazard_stall) begin
                stall_counter <= stall_counter + 64'h1;
            end
        end
    end
    
    assign cycle_count_o = cycle_counter;
    assign instr_count_o = instr_counter;
    assign stall_count_o = stall_counter;
    
    // ========================================
    // Debug Interface
    // ========================================
    
    assign debug_pc_o = pc_m;
    assign debug_instr_o = instr_m;
    assign debug_valid_o = instr_valid_m;
    
    // ========================================
    // Register File Instantiation
    // ========================================
    
    regfile #(
        .XLEN(XLEN),
        .REG_ADDR_WIDTH(REG_ADDR_WIDTH),
        .NUM_REGS(32)
    ) u_regfile (
        .clk_i(clk_i),
        .rst_i(rst_i),
        
        // Read ports
        .rs1_addr_i(rs1_addr_d),
        .rs1_data_o(rs1_data_regfile),
        .rs2_addr_i(rs2_addr_d),
        .rs2_data_o(rs2_data_regfile),
        
        // Write port
        .rd_addr_i(rd_addr_w),
        .rd_data_i(rd_data_w),
        .rd_we_i(reg_write_w)
    );
    
    // ========================================
    // Pipeline Stage Instantiations
    // ========================================
    
    // Instruction Fetch Stage
    fetch #(
        .XLEN(XLEN),
        .ADDR_WIDTH(ADDR_WIDTH),
        .ENABLE_BRANCH_PREDICTION(ENABLE_BRANCH_PREDICTION)
    ) u_fetch (
        .clk_i(clk_i),
        .rst_i(rst_i),
        
        // Control signals
        .stall_i(hazard_stall),
        .branch_taken_i(branch_taken_e),
        .branch_target_i(branch_target_e),
        
        // Branch prediction interface
        .bp_prediction_i(bp_prediction),
        .bp_target_i(bp_target),
        
        // Instruction memory interface (Wishbone)
        .imem_cyc_o(imem_cyc_o),
        .imem_stb_o(imem_stb_o),
        .imem_we_o(imem_we_o),
        .imem_adr_o(imem_adr_o),
        .imem_dat_o(imem_dat_o),
        .imem_sel_o(imem_sel_o),
        .imem_ack_i(imem_ack_i),
        .imem_dat_i(imem_dat_i),
        .imem_err_i(imem_err_i),
        
        // Outputs to decode stage
        .pc_o(pc_f),
        .instr_o(instr_f),
        .instr_valid_o(instr_valid_f),
        .stall_o(stall_f)
    );
    
    // Instruction Decode Stage
    decode #(
        .XLEN(XLEN),
        .ILEN(ILEN),
        .ADDR_WIDTH(ADDR_WIDTH),
        .REG_ADDR_WIDTH(REG_ADDR_WIDTH)
    ) u_decode (
        .clk_i(clk_i),
        .rst_i(rst_i),
        
        // Inputs from fetch stage
        .pc_i(pc_f),
        .instr_i(instr_f),
        .instr_valid_i(instr_valid_f),
        .stall_i(hazard_stall),
        
        // Register file interface (data comes from register file)
        .rs1_data_i(rs1_data_regfile),
        .rs2_data_i(rs2_data_regfile),
        .rs1_addr_o(rs1_addr_d),  // Address to register file
        .rs2_addr_o(rs2_addr_d),  // Address to register file
        
        // Writeback interface
        .rd_addr_wb_i(rd_addr_w),
        .rd_data_wb_i(rd_data_w),
        .reg_write_wb_i(reg_write_w),
        
        // Outputs to execute stage
        .pc_o(pc_d),
        .instr_o(instr_d),
        .instr_valid_o(instr_valid_d),
        .rs1_addr_reg_o(),  // Not used - internal signal
        .rs2_addr_reg_o(),  // Not used - internal signal
        .rd_addr_o(rd_addr_d),
        .rs1_data_o(rs1_data_d),
        .rs2_data_o(rs2_data_d),
        .imm_o(imm_d),
        .alu_op_o(alu_op_d),
        .alu_src_o(alu_src_d),
        .reg_write_o(reg_write_d),
        .mem_read_o(mem_read_d),
        .mem_write_o(mem_write_d),
        .mem_size_o(mem_size_d),
        .branch_o(branch_d),
        .jump_o(jump_d),
        .branch_type_o(branch_type_d),
        .stall_o(stall_d)
    );
    
    // Execute Stage
    execute #(
        .XLEN(XLEN),
        .ILEN(ILEN),
        .ADDR_WIDTH(ADDR_WIDTH),
        .REG_ADDR_WIDTH(REG_ADDR_WIDTH)
    ) u_execute (
        .clk_i(clk_i),
        .rst_i(rst_i),
        
        // Inputs from decode stage
        .pc_i(pc_d),
        .instr_i(instr_d),
        .instr_valid_i(instr_valid_d),
        .rs1_data_i(rs1_data_d),
        .rs2_data_i(rs2_data_d),
        .rd_addr_i(rd_addr_d),
        .imm_i(imm_d),
        .alu_op_i(alu_op_d),
        .alu_src_i(alu_src_d),
        .reg_write_i(reg_write_d),
        .mem_read_i(mem_read_d),
        .mem_write_i(mem_write_d),
        .mem_size_i(mem_size_d),
        .branch_i(branch_d),
        .jump_i(jump_d),
        .branch_type_i(branch_type_d),
        .stall_i(hazard_stall),
        
        // Forwarding inputs
        .forward_a_i(forward_a),
        .forward_b_i(forward_b),
        .alu_result_mem_i(alu_result_m),
        .rd_data_wb_i(rd_data_w),
        
        // Outputs to memory stage
        .pc_o(pc_e),
        .instr_o(instr_e),
        .instr_valid_o(instr_valid_e),
        .rd_addr_o(rd_addr_e),
        .alu_result_o(alu_result_e),
        .rs2_data_o(rs2_data_e),
        .reg_write_o(reg_write_e),
        .mem_read_o(mem_read_e),
        .mem_write_o(mem_write_e),
        .mem_size_o(mem_size_e),
        .branch_taken_o(branch_taken_e),
        .branch_target_o(branch_target_e),
        .stall_o(stall_e)
    );
    
    // Memory Stage
    memory #(
        .XLEN(XLEN),
        .ILEN(ILEN),
        .ADDR_WIDTH(ADDR_WIDTH),
        .REG_ADDR_WIDTH(REG_ADDR_WIDTH)
    ) u_memory (
        .clk_i(clk_i),
        .rst_i(rst_i),
        
        // Inputs from execute stage
        .pc_i(pc_e),
        .instr_i(instr_e),
        .instr_valid_i(instr_valid_e),
        .rd_addr_i(rd_addr_e),
        .alu_result_i(alu_result_e),
        .rs2_data_i(rs2_data_e),
        .reg_write_i(reg_write_e),
        .mem_read_i(mem_read_e),
        .mem_write_i(mem_write_e),
        .mem_size_i(mem_size_e),
        .stall_i(hazard_stall),
        
        // Data memory interface (Wishbone)
        .dmem_cyc_o(dmem_cyc_o),
        .dmem_stb_o(dmem_stb_o),
        .dmem_we_o(dmem_we_o),
        .dmem_adr_o(dmem_adr_o),
        .dmem_dat_o(dmem_dat_o),
        .dmem_sel_o(dmem_sel_o),
        .dmem_ack_i(dmem_ack_i),
        .dmem_dat_i(dmem_dat_i),
        .dmem_err_i(dmem_err_i),
        
        // Outputs to writeback stage
        .pc_o(pc_m),
        .instr_o(instr_m),
        .instr_valid_o(instr_valid_m),
        .rd_addr_o(rd_addr_m),
        .alu_result_o(alu_result_m),
        .mem_data_o(mem_data_m),
        .reg_write_o(reg_write_m),
        .stall_o(stall_m)
    );
    
    // Writeback Stage
    writeback #(
        .XLEN(XLEN),
        .REG_ADDR_WIDTH(REG_ADDR_WIDTH),
        .ILEN(ILEN)
    ) u_writeback (
        .clk_i(clk_i),
        .rst_i(rst_i),
        
        // Inputs from memory stage
        .rd_addr_i(rd_addr_m),
        .alu_result_i(alu_result_m),
        .mem_data_i(mem_data_m),
        .reg_write_i(reg_write_m),
        .instr_i(instr_m),
        
        // Outputs to register file
        .rd_addr_o(rd_addr_w),
        .rd_data_o(rd_data_w),
        .reg_write_o(reg_write_w)
    );
    
    // Hazard Detection Unit
    hazard_unit #(
        .REG_ADDR_WIDTH(REG_ADDR_WIDTH)
    ) u_hazard_unit (
        // Inputs from decode stage
        .rs1_addr_d_i(rs1_addr_d),
        .rs2_addr_d_i(rs2_addr_d),
        
        // Inputs from execute stage
        .rd_addr_e_i(rd_addr_e),
        .mem_read_e_i(mem_read_e),
        .reg_write_e_i(reg_write_e),
        
        // Inputs from memory stage
        .rd_addr_m_i(rd_addr_m),
        .reg_write_m_i(reg_write_m),
        
        // Control outputs
        .stall_o(hazard_stall),
        .forward_a_o(forward_a),
        .forward_b_o(forward_b)
    );
    
    // Branch Predictor (if enabled)
    generate
        if (ENABLE_BRANCH_PREDICTION) begin : gen_branch_predictor
            branch_predictor #(
                .ADDR_WIDTH(ADDR_WIDTH)
            ) u_branch_predictor (
                .clk_i(clk_i),
                .rst_i(rst_i),
                
                // Prediction request
                .pc_i(pc_f),
                .prediction_o(bp_prediction),
                .target_o(bp_target),
                
                // Prediction update
                .update_i(bp_update),
                .update_pc_i(bp_pc),
                .actual_taken_i(bp_actual),
                .actual_target_i(branch_target_e)
            );
            
            // Connect branch predictor update signals
            assign bp_update = branch_taken_e;
            assign bp_actual = branch_taken_e;
            assign bp_pc = pc_e;
        end else begin : gen_no_branch_predictor
            assign bp_prediction = 1'b0;
            assign bp_target = {ADDR_WIDTH{1'b0}};
        end
    endgenerate

endmodule

`default_nettype wire 