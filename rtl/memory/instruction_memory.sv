/**
 * instruction_memory.sv - Instruction Memory Model for eCPU
 * 
 * Simple synchronous instruction memory with Wishbone B4 interface
 * - Read-only memory for instruction storage
 * - 32-bit word-aligned access only
 * - Supports parameterizable memory size
 *
 * Author: Ethan
 * Date: 2024
 */

`default_nettype none

module instruction_memory #(
    parameter int ADDR_WIDTH = 32,        // Address width
    parameter int DATA_WIDTH = 32,        // Data width (32-bit words)
    parameter int MEM_SIZE = 16384,       // Memory size in words (64KB / 4)
    parameter string INIT_FILE = ""       // Optional initialization file
)(
    // Clock and reset
    input  wire logic                    clk_i,     // System clock
    input  wire logic                    rst_i,     // Active-high reset
    
    // Wishbone B4 interface
    input  wire logic                    cyc_i,     // Cycle signal
    input  wire logic                    stb_i,     // Strobe signal
    input  wire logic                    we_i,      // Write enable (ignored - read-only)
    input  wire logic [ADDR_WIDTH-1:0]  adr_i,     // Address
    input  wire logic [DATA_WIDTH-1:0]  dat_i,     // Data input (ignored)
    input  wire logic [DATA_WIDTH/8-1:0] sel_i,    // Byte select (ignored - word only)
    output wire logic                    ack_o,     // Acknowledge
    output wire logic [DATA_WIDTH-1:0]  dat_o,     // Data output
    output wire logic                    err_o      // Error signal
);

    // Memory array
    logic [DATA_WIDTH-1:0] memory [0:MEM_SIZE-1];
    
    // Internal signals
    logic valid_access;
    logic [ADDR_WIDTH-3:0] word_addr;  // Word address is 2 bits narrower than byte address
    logic access_active;
    
    // Word address calculation (divide byte address by 4)
    assign word_addr = adr_i[ADDR_WIDTH-1:2];
    
    // Valid access check  
    assign valid_access = cyc_i && stb_i && (word_addr < (ADDR_WIDTH-2)'(MEM_SIZE)) && (adr_i[1:0] == 2'b00);
    
    // Error signal - asserted for misaligned access or out of bounds
    assign err_o = cyc_i && stb_i && (!valid_access || we_i);
    
    // ========================================
    // Memory Initialization
    // ========================================
    
    initial begin
        // Initialize memory to NOP instructions (ADDI x0, x0, 0)
        for (int i = 0; i < MEM_SIZE; i++) begin
            memory[i] = 32'h00000013;  // ADDI x0, x0, 0 (NOP)
        end
        
        // Load initialization file if specified
        if (INIT_FILE != "") begin
            $readmemh(INIT_FILE, memory);
            $display("Instruction memory loaded from: %s", INIT_FILE);
        end
    end
    
    // ========================================
    // Wishbone Interface Logic
    // ========================================
    
    // Access tracking
    always_ff @(posedge clk_i) begin
        if (rst_i) begin
            access_active <= 1'b0;
        end else begin
            if (cyc_i && stb_i && !access_active) begin
                access_active <= 1'b1;
            end else if (ack_o || err_o) begin
                access_active <= 1'b0;
            end
        end
    end
    
    // Acknowledge generation (single cycle latency)
    assign ack_o = cyc_i && stb_i && valid_access && !we_i;
    
    // Data output
    always_comb begin
        if (valid_access && !we_i) begin
            dat_o = memory[word_addr[$clog2(MEM_SIZE)-1:0]];
        end else begin
            dat_o = {DATA_WIDTH{1'b0}};
        end
    end
    
    // ========================================
    // Debug and Verification Support
    // ========================================
    
    `ifdef DEBUG
        // Debug: Memory dump function
        function void dump_memory(input int start_addr, input int end_addr);
            $display("=== Instruction Memory Dump ===");
            for (int i = start_addr; i <= end_addr && i < MEM_SIZE; i++) begin
                $display("0x%08x: 0x%08x", i*4, memory[i]);
            end
            $display("===============================");
        endfunction
        
        // Debug: Load instruction at address
        function logic [DATA_WIDTH-1:0] load_instruction(input logic [ADDR_WIDTH-1:0] addr);
            logic [ADDR_WIDTH-1:0] word_idx = addr[ADDR_WIDTH-1:2];
            if (word_idx < MEM_SIZE && addr[1:0] == 2'b00) begin
                return memory[word_idx];
            end else begin
                return {DATA_WIDTH{1'b0}};
            end
        endfunction
        
        // Debug: Write instruction (for testing)
        function void write_instruction(input logic [ADDR_WIDTH-1:0] addr, input logic [DATA_WIDTH-1:0] data);
            logic [ADDR_WIDTH-1:0] word_idx = addr[ADDR_WIDTH-1:2];
            if (word_idx < MEM_SIZE && addr[1:0] == 2'b00) begin
                memory[word_idx] = data;
                $display("DEBUG: Wrote 0x%08x to instruction memory[0x%08x]", data, addr);
            end else begin
                $display("DEBUG: Invalid instruction memory write to 0x%08x", addr);
            end
        endfunction
    `endif
    
    // ========================================
    // Assertions for Verification
    // ========================================
    
    `ifdef FORMAL
        // Formal verification properties
        
        // Acknowledge should only be asserted for valid reads
        property ack_valid_read;
            @(posedge clk_i) disable iff (rst_i)
            ack_o |-> (cyc_i && stb_i && !we_i && valid_access);
        endproperty
        
        // Error should be asserted for writes or invalid access
        property err_on_invalid;
            @(posedge clk_i) disable iff (rst_i)
            (cyc_i && stb_i && (we_i || !valid_access)) |-> err_o;
        endproperty
        
        // Data output should be stable when ack is asserted
        property data_stable_on_ack;
            @(posedge clk_i) disable iff (rst_i)
            ack_o |-> $stable(dat_o);
        endproperty
        
        // No acknowledge and error at the same time
        property no_ack_and_err;
            @(posedge clk_i) disable iff (rst_i)
            !(ack_o && err_o);
        endproperty
        
        // Bind assertions
        assert property (ack_valid_read) else $error("Invalid acknowledge");
        assert property (err_on_invalid) else $error("Missing error signal");
        assert property (data_stable_on_ack) else $error("Data not stable on ack");
        assert property (no_ack_and_err) else $error("Ack and error asserted together");
    `endif

endmodule

`default_nettype wire 