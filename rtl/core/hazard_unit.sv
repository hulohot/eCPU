/**
 * hazard_unit.sv - Hazard Detection and Forwarding Unit for eCPU
 * 
 * Detects and resolves pipeline hazards:
 * - Data hazards (RAW - Read After Write)
 * - Load-use hazards (require pipeline stall)
 * - Implements forwarding logic to minimize stalls
 *
 * Author: Ethan
 * Date: 2024
 */

`default_nettype none

module hazard_unit #(
    parameter int REG_ADDR_WIDTH = 5      // Register address width
)(
    // Inputs from decode stage
    input  wire logic [REG_ADDR_WIDTH-1:0]  rs1_addr_d_i,   // Source register 1 (decode)
    input  wire logic [REG_ADDR_WIDTH-1:0]  rs2_addr_d_i,   // Source register 2 (decode)
    
    // Inputs from execute stage
    input  wire logic [REG_ADDR_WIDTH-1:0]  rd_addr_e_i,    // Destination register (execute)
    input  wire logic                        mem_read_e_i,   // Memory read (execute)
    input  wire logic                        reg_write_e_i,  // Register write enable (execute)
    
    // Inputs from memory stage
    input  wire logic [REG_ADDR_WIDTH-1:0]  rd_addr_m_i,    // Destination register (memory)
    input  wire logic                        reg_write_m_i,  // Register write enable (memory)
    
    // Control outputs
    output wire logic                        stall_o,        // Pipeline stall signal
    output wire logic [1:0]                  forward_a_o,    // Forwarding control for operand A
    output wire logic [1:0]                  forward_b_o     // Forwarding control for operand B
);

    // Forwarding control encoding
    typedef enum logic [1:0] {
        FORWARD_NONE = 2'b00,    // No forwarding - use register file data
        FORWARD_MEM  = 2'b01,    // Forward from memory stage
        FORWARD_WB   = 2'b10     // Forward from writeback stage (future extension)
    } forward_t;
    
    // ========================================
    // Load-Use Hazard Detection
    // ========================================
    
    // Load-use hazard occurs when:
    // 1. Execute stage has a load instruction (mem_read_e_i)
    // 2. Decode stage instruction uses the register being loaded
    logic load_use_hazard;
    
    always_comb begin
        load_use_hazard = 1'b0;
        
        if (mem_read_e_i && reg_write_e_i && (rd_addr_e_i != 5'b00000)) begin
            // Check if decode stage instruction uses the register being loaded
            if ((rs1_addr_d_i == rd_addr_e_i) || (rs2_addr_d_i == rd_addr_e_i)) begin
                load_use_hazard = 1'b1;
            end
        end
    end
    
    // Stall pipeline for load-use hazards
    assign stall_o = load_use_hazard;
    
    // ========================================
    // Data Forwarding Logic
    // ========================================
    
    // Forwarding for operand A (rs1)
    always_comb begin
        forward_a_o = FORWARD_NONE;
        
        // Forward from memory stage (EX/MEM -> EX)
        if (reg_write_m_i && (rd_addr_m_i != 5'b00000) && (rd_addr_m_i == rs1_addr_d_i)) begin
            forward_a_o = FORWARD_MEM;
        end
        // Note: Execute stage forwarding would need different timing
        // For now, memory stage forwarding covers most cases
    end
    
    // Forwarding for operand B (rs2)
    always_comb begin
        forward_b_o = FORWARD_NONE;
        
        // Forward from memory stage (EX/MEM -> EX)
        if (reg_write_m_i && (rd_addr_m_i != 5'b00000) && (rd_addr_m_i == rs2_addr_d_i)) begin
            forward_b_o = FORWARD_MEM;
        end
        // Note: Execute stage forwarding would need different timing
        // For now, memory stage forwarding covers most cases
    end
    
    // ========================================
    // Debug and Verification Support
    // ========================================
    
    `ifdef DEBUG
        // Debug: Display hazard detection information
        always_comb begin
            if (load_use_hazard) begin
                $display("DEBUG HAZARD: Load-use hazard detected - rd_e=x%0d, rs1_d=x%0d, rs2_d=x%0d", 
                    rd_addr_e_i, rs1_addr_d_i, rs2_addr_d_i);
            end
            
            if (forward_a_o != FORWARD_NONE) begin
                $display("DEBUG FORWARD: Forwarding operand A from stage %0d to rs1=x%0d", 
                    forward_a_o, rs1_addr_d_i);
            end
            
            if (forward_b_o != FORWARD_NONE) begin
                $display("DEBUG FORWARD: Forwarding operand B from stage %0d to rs2=x%0d", 
                    forward_b_o, rs2_addr_d_i);
            end
        end
    `endif
    
    // ========================================
    // Assertions for Verification
    // ========================================
    
    `ifdef FORMAL
        // Formal verification properties
        
        // Stall should only occur for load-use hazards
        property stall_only_for_load_use;
            stall_o |-> load_use_hazard;
        endproperty
        
        // Load-use hazard detection correctness
        property load_use_detection;
            (mem_read_e_i && reg_write_e_i && (rd_addr_e_i != 5'b00000) &&
             ((rs1_addr_d_i == rd_addr_e_i) || (rs2_addr_d_i == rd_addr_e_i))) 
            |-> load_use_hazard;
        endproperty
        
        // Forward A when memory stage writes to rs1
        property forward_a_mem_stage;
            (reg_write_m_i && (rd_addr_m_i != 5'b00000) && (rd_addr_m_i == rs1_addr_d_i))
            |-> (forward_a_o == FORWARD_MEM);
        endproperty
        
        // Forward B when memory stage writes to rs2
        property forward_b_mem_stage;
            (reg_write_m_i && (rd_addr_m_i != 5'b00000) && (rd_addr_m_i == rs2_addr_d_i))
            |-> (forward_b_o == FORWARD_MEM);
        endproperty
        
        // No forwarding to/from x0
        property no_forward_x0;
            (rd_addr_m_i == 5'b00000) |-> 
            (forward_a_o == FORWARD_NONE) && (forward_b_o == FORWARD_NONE);
        endproperty
        
        // Bind assertions
        assert property (stall_only_for_load_use) else $error("Invalid stall condition");
        assert property (load_use_detection) else $error("Load-use hazard not detected");
        assert property (forward_a_mem_stage) else $error("Missing forward A from memory");
        assert property (forward_b_mem_stage) else $error("Missing forward B from memory");
        assert property (no_forward_x0) else $error("Forwarding involving x0");
    `endif

endmodule

`default_nettype wire 