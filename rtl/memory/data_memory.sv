/**
 * data_memory.sv - Data Memory Model for eCPU
 * 
 * Byte-addressable data memory with Wishbone B4 interface
 * - Supports word, halfword, and byte access
 * - Read and write operations
 * - Parameterizable memory size
 *
 * Author: Ethan
 * Date: 2024
 */

`default_nettype none

module data_memory #(
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
    input  wire logic                    we_i,      // Write enable
    input  wire logic [ADDR_WIDTH-1:0]  adr_i,     // Address
    input  wire logic [DATA_WIDTH-1:0]  dat_i,     // Data input
    input  wire logic [DATA_WIDTH/8-1:0] sel_i,    // Byte select
    output wire logic                    ack_o,     // Acknowledge
    output wire logic [DATA_WIDTH-1:0]  dat_o,     // Data output
    output wire logic                    err_o      // Error signal
);

    // Memory array (byte-addressable)
    logic [7:0] memory [0:MEM_SIZE*4-1];
    
    // Internal signals
    logic valid_access;
    logic [ADDR_WIDTH-1:0] byte_addr;
    logic access_active;
    logic [DATA_WIDTH-1:0] read_data;
    logic [DATA_WIDTH-1:0] write_data;
    logic [3:0] write_mask;
    
    // Address calculation
    assign byte_addr = adr_i;
    
    // Valid access check (within memory bounds)
    assign valid_access = cyc_i && stb_i && (byte_addr < (MEM_SIZE * 4));
    
    // Error signal - asserted for out of bounds access
    assign err_o = cyc_i && stb_i && !valid_access;
    
    // ========================================
    // Memory Initialization
    // ========================================
    
    initial begin
        // Initialize memory to zeros
        for (int i = 0; i < MEM_SIZE * 4; i++) begin
            memory[i] = 8'h00;
        end
        
        // Load initialization file if specified
        if (INIT_FILE != "") begin
            $readmemh(INIT_FILE, memory);
            $display("Data memory loaded from: %s", INIT_FILE);
        end
    end
    
    // ========================================
    // Read Logic
    // ========================================
    
    always_comb begin
        read_data = {DATA_WIDTH{1'b0}};
        
        if (valid_access && !we_i) begin
            // Read data from memory (always read full word)
            read_data[7:0]   = memory[byte_addr + 0];
            read_data[15:8]  = memory[byte_addr + 1];
            read_data[23:16] = memory[byte_addr + 2];
            read_data[31:24] = memory[byte_addr + 3];
        end
    end
    
    // ========================================
    // Write Logic
    // ========================================
    
    // Generate write mask from sel_i
    assign write_mask = sel_i;
    
    // Prepare write data
    always_comb begin
        write_data = dat_i;
    end
    
    // Write operation
    always_ff @(posedge clk_i) begin
        if (rst_i) begin
            // Memory contents preserved during reset
        end else if (valid_access && we_i && cyc_i && stb_i) begin
            // Write bytes based on select signals
            if (write_mask[0]) memory[byte_addr + 0] <= write_data[7:0];
            if (write_mask[1]) memory[byte_addr + 1] <= write_data[15:8];
            if (write_mask[2]) memory[byte_addr + 2] <= write_data[23:16];
            if (write_mask[3]) memory[byte_addr + 3] <= write_data[31:24];
        end
    end
    
    // ========================================
    // Wishbone Interface Logic
    // ========================================
    
    // Access tracking for single-cycle operations
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
    assign ack_o = cyc_i && stb_i && valid_access;
    
    // Data output
    assign dat_o = read_data;
    
    // ========================================
    // Debug and Verification Support
    // ========================================
    
    `ifdef DEBUG
        // Debug: Memory dump function
        function void dump_memory(input int start_addr, input int end_addr);
            $display("=== Data Memory Dump ===");
            for (int i = start_addr; i <= end_addr && i < (MEM_SIZE * 4); i += 4) begin
                $display("0x%08x: 0x%02x%02x%02x%02x", 
                    i, 
                    memory[i+3], memory[i+2], memory[i+1], memory[i+0]);
            end
            $display("========================");
        endfunction
        
        // Debug: Read word from memory
        function logic [DATA_WIDTH-1:0] read_word(input logic [ADDR_WIDTH-1:0] addr);
            logic [DATA_WIDTH-1:0] result;
            if (addr < (MEM_SIZE * 4)) begin
                result[7:0]   = memory[addr + 0];
                result[15:8]  = memory[addr + 1];
                result[23:16] = memory[addr + 2];
                result[31:24] = memory[addr + 3];
                return result;
            end else begin
                return {DATA_WIDTH{1'b0}};
            end
        endfunction
        
        // Debug: Write word to memory
        function void write_word(input logic [ADDR_WIDTH-1:0] addr, input logic [DATA_WIDTH-1:0] data);
            if (addr < (MEM_SIZE * 4)) begin
                memory[addr + 0] = data[7:0];
                memory[addr + 1] = data[15:8];
                memory[addr + 2] = data[23:16];
                memory[addr + 3] = data[31:24];
                $display("DEBUG: Wrote 0x%08x to data memory[0x%08x]", data, addr);
            end else begin
                $display("DEBUG: Invalid data memory write to 0x%08x", addr);
            end
        endfunction
        
        // Debug: Read byte from memory
        function logic [7:0] read_byte(input logic [ADDR_WIDTH-1:0] addr);
            if (addr < (MEM_SIZE * 4)) begin
                return memory[addr];
            end else begin
                return 8'h00;
            end
        endfunction
        
        // Debug: Write byte to memory
        function void write_byte(input logic [ADDR_WIDTH-1:0] addr, input logic [7:0] data);
            if (addr < (MEM_SIZE * 4)) begin
                memory[addr] = data;
                $display("DEBUG: Wrote 0x%02x to data memory[0x%08x]", data, addr);
            end else begin
                $display("DEBUG: Invalid data memory byte write to 0x%08x", addr);
            end
        endfunction
    `endif
    
    // ========================================
    // Assertions for Verification
    // ========================================
    
    `ifdef FORMAL
        // Formal verification properties
        
        // Acknowledge should only be asserted for valid access
        property ack_valid_access;
            @(posedge clk_i) disable iff (rst_i)
            ack_o |-> (cyc_i && stb_i && valid_access);
        endproperty
        
        // Error should be asserted for invalid access
        property err_on_invalid;
            @(posedge clk_i) disable iff (rst_i)
            (cyc_i && stb_i && !valid_access) |-> err_o;
        endproperty
        
        // Data output should be stable when ack is asserted for reads
        property data_stable_on_read_ack;
            @(posedge clk_i) disable iff (rst_i)
            (ack_o && !we_i) |-> $stable(dat_o);
        endproperty
        
        // No acknowledge and error at the same time
        property no_ack_and_err;
            @(posedge clk_i) disable iff (rst_i)
            !(ack_o && err_o);
        endproperty
        
        // Write only occurs with valid access and write enable
        property valid_write_only;
            @(posedge clk_i) disable iff (rst_i)
            $changed(memory) |-> $past(valid_access && we_i && cyc_i && stb_i);
        endproperty
        
        // Bind assertions
        assert property (ack_valid_access) else $error("Invalid acknowledge");
        assert property (err_on_invalid) else $error("Missing error for invalid access");
        assert property (data_stable_on_read_ack) else $error("Data not stable on read ack");
        assert property (no_ack_and_err) else $error("Ack and error asserted together");
        assert property (valid_write_only) else $error("Invalid write operation");
    `endif

endmodule

`default_nettype wire 