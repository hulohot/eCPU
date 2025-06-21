/**
 * regfile.sv - Register File for eCPU
 * 
 * 32 x 32-bit register file for RISC-V RV32I
 * - Dual read ports, single write port
 * - Register x0 is hardwired to zero
 * - Synchronous write, asynchronous read
 *
 * Author: Ethan  
 * Date: 2024
 */

`default_nettype none

module regfile #(
    parameter int XLEN = 32,              // Data width (32-bit for RV32I)
    parameter int REG_ADDR_WIDTH = 5,     // Register address width (32 regs = 5 bits)
    parameter int NUM_REGS = 32           // Number of registers
)(
    // Clock and reset
    input  wire logic                        clk_i,        // System clock
    input  wire logic                        rst_i,        // Active-high reset
    
    // Read port 1 (rs1)
    input  wire logic [REG_ADDR_WIDTH-1:0]  rs1_addr_i,   // Read address 1
    output wire logic [XLEN-1:0]            rs1_data_o,   // Read data 1
    
    // Read port 2 (rs2) 
    input  wire logic [REG_ADDR_WIDTH-1:0]  rs2_addr_i,   // Read address 2
    output wire logic [XLEN-1:0]            rs2_data_o,   // Read data 2
    
    // Write port (rd)
    input  wire logic [REG_ADDR_WIDTH-1:0]  rd_addr_i,    // Write address
    input  wire logic [XLEN-1:0]            rd_data_i,    // Write data
    input  wire logic                        rd_we_i       // Write enable
);

    // Register array (x1-x31, x0 is handled separately)
    logic [XLEN-1:0] registers [1:NUM_REGS-1];
    
    // ========================================
    // Register Write Logic
    // ========================================
    
    always_ff @(posedge clk_i) begin
        if (rst_i) begin
            // Reset all registers to zero
            for (int i = 1; i < NUM_REGS; i++) begin
                registers[i] <= {XLEN{1'b0}};
            end
        end else if (rd_we_i && rd_addr_i != 5'b00000) begin
            // Write to register (except x0 which is always zero)
            registers[rd_addr_i] <= rd_data_i;
        end
        // Note: x0 is not stored in the array and always reads as zero
    end
    
    // ========================================
    // Register Read Logic (Asynchronous)
    // ========================================
    
    // Read port 1 (rs1)
    always_comb begin
        if (rs1_addr_i == 5'b00000) begin
            rs1_data_o = {XLEN{1'b0}};           // x0 always reads zero
        end else begin
            rs1_data_o = registers[rs1_addr_i];   // Read from register array
        end
    end
    
    // Read port 2 (rs2)
    always_comb begin
        if (rs2_addr_i == 5'b00000) begin
            rs2_data_o = {XLEN{1'b0}};           // x0 always reads zero
        end else begin
            rs2_data_o = registers[rs2_addr_i];   // Read from register array
        end
    end
    
    // ========================================
    // Debug and Verification Support
    // ========================================
    
    `ifdef DEBUG
        // Debug: Register file dump function
        function void dump_registers();
            $display("=== Register File Dump ===");
            $display("x0  (zero): %08h", 32'h0);
            for (int i = 1; i < NUM_REGS; i++) begin
                $display("x%-2d      : %08h", i, registers[i]);
            end
            $display("========================");
        endfunction
        
        // Debug: Check specific register
        function logic [XLEN-1:0] get_register(input logic [REG_ADDR_WIDTH-1:0] addr);
            if (addr == 5'b00000) begin
                return {XLEN{1'b0}};
            end else begin
                return registers[addr];
            end
        endfunction
    `endif
    
    // ========================================
    // Assertions for Verification
    // ========================================
    
    `ifdef FORMAL
        // Formal verification properties
        
        // x0 always reads zero
        property x0_always_zero_rs1;
            @(posedge clk_i) disable iff (rst_i)
            (rs1_addr_i == 5'b00000) |-> (rs1_data_o == {XLEN{1'b0}});
        endproperty
        
        property x0_always_zero_rs2;
            @(posedge clk_i) disable iff (rst_i)
            (rs2_addr_i == 5'b00000) |-> (rs2_data_o == {XLEN{1'b0}});
        endproperty
        
        // Write to x0 should be ignored
        property x0_unwritable;
            @(posedge clk_i) disable iff (rst_i)
            (rd_we_i && rd_addr_i == 5'b00000) |=> 
            (rs1_addr_i == 5'b00000) ? (rs1_data_o == {XLEN{1'b0}}) : 1'b1;
        endproperty
        
        // Register write should be visible on next cycle
        property write_read_consistency;
            logic [REG_ADDR_WIDTH-1:0] addr;
            logic [XLEN-1:0] data;
            @(posedge clk_i) disable iff (rst_i)
            (rd_we_i && rd_addr_i != 5'b00000, addr = rd_addr_i, data = rd_data_i) |=> 
            ((rs1_addr_i == addr) ? (rs1_data_o == data) : 1'b1) &&
            ((rs2_addr_i == addr) ? (rs2_data_o == data) : 1'b1);
        endproperty
        
        // Reset should clear all registers
        property reset_clears_registers;
            @(posedge clk_i) 
            rst_i |=> 
            (rs1_addr_i != 5'b00000) ? (rs1_data_o == {XLEN{1'b0}}) : 1'b1 &&
            (rs2_addr_i != 5'b00000) ? (rs2_data_o == {XLEN{1'b0}}) : 1'b1;
        endproperty
        
        // Bind assertions
        assert property (x0_always_zero_rs1) else $error("x0 not zero on rs1");
        assert property (x0_always_zero_rs2) else $error("x0 not zero on rs2");
        assert property (x0_unwritable) else $error("x0 is writable");
        assert property (write_read_consistency) else $error("Write-read inconsistency");
        assert property (reset_clears_registers) else $error("Reset doesn't clear registers");
    `endif
    
    // ========================================
    // Coverage Points
    // ========================================
    
    `ifdef COVERAGE
        // Coverage for all register addresses
        covergroup reg_addr_cg @(posedge clk_i);
            rs1_addr_cp: coverpoint rs1_addr_i {
                bins zero = {0};
                bins non_zero[] = {[1:31]};
            }
            rs2_addr_cp: coverpoint rs2_addr_i {
                bins zero = {0};
                bins non_zero[] = {[1:31]};  
            }
            rd_addr_cp: coverpoint rd_addr_i iff (rd_we_i) {
                bins zero = {0};
                bins non_zero[] = {[1:31]};
            }
        endgroup
        
        // Coverage for write enable scenarios
        covergroup write_scenarios_cg @(posedge clk_i);
            write_enable_cp: coverpoint rd_we_i {
                bins enabled = {1};
                bins disabled = {0};
            }
            write_to_x0_cp: coverpoint (rd_we_i && rd_addr_i == 5'b00000) {
                bins write_to_x0 = {1};
                bins normal_write = {0};
            }
        endgroup
        
        reg_addr_cg reg_addr_cg_inst = new();
        write_scenarios_cg write_scenarios_cg_inst = new();
    `endif

endmodule

`default_nettype wire 