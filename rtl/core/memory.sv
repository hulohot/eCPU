/**
 * memory.sv - Memory Stage for eCPU
 * 
 * Pipeline stage that handles memory operations (load/store)
 * - Interfaces with data memory via Wishbone B4
 * - Supports word, halfword, and byte access
 * - Handles memory alignment and byte selection
 *
 * Author: Ethan
 * Date: 2024
 */

`default_nettype none

module memory #(
    parameter int XLEN = 32,              // Data width (32-bit for RV32I)
    parameter int ILEN = 32,              // Instruction width
    parameter int ADDR_WIDTH = 32,        // Address width
    parameter int REG_ADDR_WIDTH = 5      // Register address width
)(
    // Clock and reset
    input  wire logic                        clk_i,         // System clock
    input  wire logic                        rst_i,         // Active-high reset
    
    // Inputs from execute stage
    input  wire logic [ADDR_WIDTH-1:0]      pc_i,          // Program counter
    input  wire logic [ILEN-1:0]            instr_i,       // Instruction
    input  wire logic                        instr_valid_i, // Instruction valid
    input  wire logic [REG_ADDR_WIDTH-1:0]  rd_addr_i,     // Destination register
    input  wire logic [XLEN-1:0]            alu_result_i,  // ALU result (address for load/store)
    input  wire logic [XLEN-1:0]            rs2_data_i,    // Store data
    input  wire logic                        reg_write_i,   // Register write enable
    input  wire logic                        mem_read_i,    // Memory read enable
    input  wire logic                        mem_write_i,   // Memory write enable
    input  wire logic [2:0]                  mem_size_i,    // Memory operation size
    input  wire logic                        stall_i,       // Pipeline stall
    
    // Data memory interface (Wishbone B4)
    output wire logic                        dmem_cyc_o,    // Cycle signal
    output wire logic                        dmem_stb_o,    // Strobe signal
    output wire logic                        dmem_we_o,     // Write enable
    output wire logic [ADDR_WIDTH-1:0]      dmem_adr_o,    // Address
    output wire logic [XLEN-1:0]            dmem_dat_o,    // Data out
    output wire logic [XLEN/8-1:0]          dmem_sel_o,    // Byte select
    input  wire logic                        dmem_ack_i,    // Acknowledge
    input  wire logic [XLEN-1:0]            dmem_dat_i,    // Data in
    input  wire logic                        dmem_err_i,    // Error signal
    
    // Outputs to writeback stage
    output logic [ADDR_WIDTH-1:0]           pc_o,          // Program counter
    output logic [ILEN-1:0]                 instr_o,       // Instruction
    output logic                             instr_valid_o, // Instruction valid
    output logic [REG_ADDR_WIDTH-1:0]       rd_addr_o,     // Destination register
    output logic [XLEN-1:0]                 alu_result_o,  // ALU result
    output logic [XLEN-1:0]                 mem_data_o,    // Memory read data
    output logic                             reg_write_o,   // Register write enable
    output logic                             stall_o        // Stall output
);

    // Memory operation size encoding
    typedef enum logic [2:0] {
        MEM_BYTE      = 3'b000,  // LB/SB
        MEM_HALFWORD  = 3'b001,  // LH/SH
        MEM_WORD      = 3'b010,  // LW/SW
        MEM_BYTE_U    = 3'b100,  // LBU
        MEM_HALFWORD_U = 3'b101   // LHU
    } mem_size_t;
    
    // Internal signals
    logic [XLEN-1:0] aligned_store_data;
    logic [3:0] byte_select;
    logic [XLEN-1:0] load_data_raw;
    logic [XLEN-1:0] load_data_processed;
    logic [1:0] byte_offset;
    logic mem_operation;
    logic mem_misaligned;
    
    // Extract byte offset from address
    assign byte_offset = alu_result_i[1:0];
    
    // Check for memory operation
    assign mem_operation = mem_read_i || mem_write_i;
    
    // Check for misaligned access
    always_comb begin
        mem_misaligned = 1'b0;
        case (mem_size_i)
            MEM_HALFWORD, MEM_HALFWORD_U: mem_misaligned = byte_offset[0];
            MEM_WORD: mem_misaligned = (byte_offset != 2'b00);
            default: mem_misaligned = 1'b0; // Byte access is always aligned
        endcase
    end
    
    // ========================================
    // Store Data Alignment
    // ========================================
    
    always_comb begin
        aligned_store_data = {XLEN{1'b0}};
        case (mem_size_i)
            MEM_BYTE, MEM_BYTE_U: begin
                case (byte_offset)
                    2'b00: aligned_store_data = {24'h0, rs2_data_i[7:0]};
                    2'b01: aligned_store_data = {16'h0, rs2_data_i[7:0], 8'h0};
                    2'b10: aligned_store_data = {8'h0, rs2_data_i[7:0], 16'h0};
                    2'b11: aligned_store_data = {rs2_data_i[7:0], 24'h0};
                endcase
            end
            MEM_HALFWORD, MEM_HALFWORD_U: begin
                case (byte_offset[1])
                    1'b0: aligned_store_data = {16'h0, rs2_data_i[15:0]};
                    1'b1: aligned_store_data = {rs2_data_i[15:0], 16'h0};
                endcase
            end
            MEM_WORD: begin
                aligned_store_data = rs2_data_i;
            end
            default: aligned_store_data = rs2_data_i;
        endcase
    end
    
    // ========================================
    // Byte Select Generation
    // ========================================
    
    always_comb begin
        byte_select = 4'b0000;
        case (mem_size_i)
            MEM_BYTE, MEM_BYTE_U: begin
                case (byte_offset)
                    2'b00: byte_select = 4'b0001;
                    2'b01: byte_select = 4'b0010;
                    2'b10: byte_select = 4'b0100;
                    2'b11: byte_select = 4'b1000;
                endcase
            end
            MEM_HALFWORD, MEM_HALFWORD_U: begin
                case (byte_offset[1])
                    1'b0: byte_select = 4'b0011;
                    1'b1: byte_select = 4'b1100;
                endcase
            end
            MEM_WORD: begin
                byte_select = 4'b1111;
            end
            default: byte_select = 4'b1111;
        endcase
    end
    
    // ========================================
    // Wishbone Interface
    // ========================================
    
    assign dmem_cyc_o = mem_operation && !mem_misaligned && instr_valid_i && !stall_i;
    assign dmem_stb_o = mem_operation && !mem_misaligned && instr_valid_i && !stall_i;
    assign dmem_we_o = mem_write_i;
    assign dmem_adr_o = {alu_result_i[ADDR_WIDTH-1:2], 2'b00}; // Word-aligned address
    assign dmem_dat_o = aligned_store_data;
    assign dmem_sel_o = byte_select;
    
    // ========================================
    // Load Data Processing
    // ========================================
    
    assign load_data_raw = dmem_dat_i;
    
    always_comb begin
        load_data_processed = {XLEN{1'b0}};
        
        if (mem_read_i && dmem_ack_i) begin
            case (mem_size_i)
                MEM_BYTE: begin
                    case (byte_offset)
                        2'b00: load_data_processed = {{24{load_data_raw[7]}}, load_data_raw[7:0]};
                        2'b01: load_data_processed = {{24{load_data_raw[15]}}, load_data_raw[15:8]};
                        2'b10: load_data_processed = {{24{load_data_raw[23]}}, load_data_raw[23:16]};
                        2'b11: load_data_processed = {{24{load_data_raw[31]}}, load_data_raw[31:24]};
                    endcase
                end
                MEM_BYTE_U: begin
                    case (byte_offset)
                        2'b00: load_data_processed = {24'h0, load_data_raw[7:0]};
                        2'b01: load_data_processed = {24'h0, load_data_raw[15:8]};
                        2'b10: load_data_processed = {24'h0, load_data_raw[23:16]};
                        2'b11: load_data_processed = {24'h0, load_data_raw[31:24]};
                    endcase
                end
                MEM_HALFWORD: begin
                    case (byte_offset[1])
                        1'b0: load_data_processed = {{16{load_data_raw[15]}}, load_data_raw[15:0]};
                        1'b1: load_data_processed = {{16{load_data_raw[31]}}, load_data_raw[31:16]};
                    endcase
                end
                MEM_HALFWORD_U: begin
                    case (byte_offset[1])
                        1'b0: load_data_processed = {16'h0, load_data_raw[15:0]};
                        1'b1: load_data_processed = {16'h0, load_data_raw[31:16]};
                    endcase
                end
                MEM_WORD: begin
                    load_data_processed = load_data_raw;
                end
                default: load_data_processed = load_data_raw;
            endcase
        end
    end
    
    // ========================================
    // Pipeline Register
    // ========================================
    
    always_ff @(posedge clk_i) begin
        if (rst_i) begin
            pc_o <= {ADDR_WIDTH{1'b0}};
            instr_o <= {ILEN{1'b0}};
            instr_valid_o <= 1'b0;
            rd_addr_o <= {REG_ADDR_WIDTH{1'b0}};
            alu_result_o <= {XLEN{1'b0}};
            mem_data_o <= {XLEN{1'b0}};
            reg_write_o <= 1'b0;
            stall_o <= 1'b0;
        end else if (!stall_i) begin
            pc_o <= pc_i;
            instr_o <= instr_i;
            instr_valid_o <= instr_valid_i;
            rd_addr_o <= rd_addr_i;
            alu_result_o <= alu_result_i;
            mem_data_o <= load_data_processed;
            reg_write_o <= reg_write_i;
            stall_o <= 1'b0;
        end else begin
            // Hold current values during stall
            stall_o <= stall_i;
        end
    end
    
    // ========================================
    // Debug and Verification Support
    // ========================================
    
    `ifdef DEBUG
        always_ff @(posedge clk_i) begin
            if (!rst_i && mem_operation && instr_valid_i) begin
                if (mem_misaligned) begin
                    $display("DEBUG MEM: Misaligned access at 0x%08x, size=%0d", alu_result_i, mem_size_i);
                end else if (mem_read_i && dmem_ack_i) begin
                    $display("DEBUG MEM: Load from 0x%08x = 0x%08x (processed: 0x%08x)", 
                        alu_result_i, load_data_raw, load_data_processed);
                end else if (mem_write_i && dmem_ack_i) begin
                    $display("DEBUG MEM: Store to 0x%08x = 0x%08x (aligned: 0x%08x)", 
                        alu_result_i, rs2_data_i, aligned_store_data);
                end
            end
        end
    `endif
    
    // ========================================
    // Assertions for Verification
    // ========================================
    
    `ifdef FORMAL
        // Formal verification properties
        
        // No memory operation for misaligned access
        property no_mem_op_if_misaligned;
            @(posedge clk_i) disable iff (rst_i)
            mem_misaligned |-> !(dmem_cyc_o || dmem_stb_o);
        endproperty
        
        // Wishbone signals consistency
        property wishbone_consistency;
            @(posedge clk_i) disable iff (rst_i)
            dmem_stb_o |-> dmem_cyc_o;
        endproperty
        
        // Write enable only for store operations
        property write_enable_for_stores;
            @(posedge clk_i) disable iff (rst_i)
            dmem_we_o |-> mem_write_i;
        endproperty
        
        // Address alignment for wishbone
        property address_alignment;
            @(posedge clk_i) disable iff (rst_i)
            dmem_cyc_o |-> (dmem_adr_o[1:0] == 2'b00);
        endproperty
        
        // Bind assertions
        assert property (no_mem_op_if_misaligned) else $error("Memory operation on misaligned access");
        assert property (wishbone_consistency) else $error("Wishbone protocol violation");
        assert property (write_enable_for_stores) else $error("Write enable without store");
        assert property (address_alignment) else $error("Unaligned wishbone address");
    `endif

endmodule

`default_nettype wire 