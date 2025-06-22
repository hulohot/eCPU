/**
 * execute.sv - Execute Stage for eCPU
 * 
 * Pipeline stage that performs ALU operations and handles:
 * - Arithmetic and logical operations
 * - Branch target calculation
 * - Data forwarding to resolve hazards
 * - Control flow decision making
 *
 * Author: Ethan
 * Date: 2024
 */

`default_nettype none

module execute #(
    parameter int XLEN = 32,              // Data width (32-bit for RV32I)
    parameter int ILEN = 32,              // Instruction width
    parameter int ADDR_WIDTH = 32,        // Address width
    parameter int REG_ADDR_WIDTH = 5      // Register address width
)(
    // Clock and reset
    input  wire logic                        clk_i,            // System clock
    input  wire logic                        rst_i,            // Active-high reset
    
    // Inputs from decode stage
    input  wire logic [ADDR_WIDTH-1:0]      pc_i,             // Program counter
    input  wire logic [ILEN-1:0]            instr_i,          // Instruction
    input  wire logic                        instr_valid_i,    // Instruction valid
    input  wire logic [XLEN-1:0]            rs1_data_i,       // Source register 1 data
    input  wire logic [XLEN-1:0]            rs2_data_i,       // Source register 2 data
    input  wire logic [REG_ADDR_WIDTH-1:0]  rd_addr_i,        // Destination register
    input  wire logic [XLEN-1:0]            imm_i,            // Immediate value
    input  wire logic [3:0]                 alu_op_i,         // ALU operation
    input  wire logic                        reg_write_i,      // Register write enable
    input  wire logic                        mem_read_i,       // Memory read enable
    input  wire logic                        mem_write_i,      // Memory write enable
    input  wire logic [2:0]                 mem_size_i,       // Memory operation size
    input  wire logic                        branch_i,         // Branch instruction
    input  wire logic                        jump_i,           // Jump instruction
    input  wire logic [2:0]                 branch_type_i,    // Branch type
    input  wire logic                        stall_i,          // Pipeline stall
    
    // Forwarding inputs
    input  wire logic [1:0]                 forward_a_i,      // Forward control for operand A
    input  wire logic [1:0]                 forward_b_i,      // Forward control for operand B
    input  wire logic [XLEN-1:0]           alu_result_mem_i, // ALU result from memory stage
    input  wire logic [XLEN-1:0]           rd_data_wb_i,     // Register data from writeback
    
    // Outputs to memory stage
    output logic [ADDR_WIDTH-1:0]          pc_o,             // Program counter
    output logic [ILEN-1:0]                instr_o,          // Instruction
    output logic                            instr_valid_o,    // Instruction valid
    output logic [REG_ADDR_WIDTH-1:0]      rd_addr_o,        // Destination register
    output logic [XLEN-1:0]                alu_result_o,     // ALU result
    output logic [XLEN-1:0]                rs2_data_o,       // Store data (forwarded rs2)
    output logic                            reg_write_o,      // Register write enable
    output logic                            mem_read_o,       // Memory read enable
    output logic                            mem_write_o,      // Memory write enable
    output logic [2:0]                     mem_size_o,       // Memory operation size
    output logic                            branch_taken_o,   // Branch taken
    output logic [ADDR_WIDTH-1:0]          branch_target_o,  // Branch target address
    output logic                            stall_o           // Stall output
);

    // Branch type encoding
    typedef enum logic [2:0] {
        BRANCH_EQ  = 3'b000,    // BEQ
        BRANCH_NE  = 3'b001,    // BNE
        BRANCH_LT  = 3'b100,    // BLT
        BRANCH_GE  = 3'b101,    // BGE
        BRANCH_LTU = 3'b110,    // BLTU
        BRANCH_GEU = 3'b111     // BGEU
    } branch_type_t;
    
    // Forwarding control encoding
    typedef enum logic [1:0] {
        FORWARD_NONE = 2'b00,    // No forwarding
        FORWARD_MEM  = 2'b01,    // Forward from memory stage
        FORWARD_WB   = 2'b10     // Forward from writeback stage
    } forward_t;
    
    // Internal signals
    logic [XLEN-1:0] operand_a;
    logic [XLEN-1:0] operand_b;
    logic [XLEN-1:0] operand_b_forwarded;
    logic [XLEN-1:0] alu_result;
    logic            alu_zero;
    logic            alu_negative;
    logic            alu_overflow;
    logic            alu_carry;
    logic            branch_condition;
    logic [ADDR_WIDTH-1:0] branch_target;
    logic            take_branch;
    logic            take_jump;
    
    // ========================================
    // Operand Forwarding Logic
    // ========================================
    
    // Forward operand A (rs1)
    always_comb begin
        case (forward_a_i)
            FORWARD_MEM:  operand_a = alu_result_mem_i;
            FORWARD_WB:   operand_a = rd_data_wb_i;
            default:      operand_a = rs1_data_i;
        endcase
    end
    
    // Forward operand B (rs2) 
    always_comb begin
        case (forward_b_i)
            FORWARD_MEM:  operand_b_forwarded = alu_result_mem_i;
            FORWARD_WB:   operand_b_forwarded = rd_data_wb_i;
            default:      operand_b_forwarded = rs2_data_i;
        endcase
    end
    
    // Select between forwarded rs2 and immediate for operand B
    assign operand_b = (alu_op_i[3]) ? imm_i : operand_b_forwarded; // Simple heuristic for immediate ops
    
    // ========================================
    // ALU Instantiation
    // ========================================
    
    alu #(
        .XLEN(XLEN)
    ) u_alu (
        .operand_a_i(operand_a),
        .operand_b_i(operand_b),
        .alu_op_i(alu_op_i),
        .result_o(alu_result),
        .zero_o(alu_zero),
        .negative_o(alu_negative),
        .overflow_o(alu_overflow),
        .carry_o(alu_carry)
    );
    
    // ========================================
    // Branch Condition Evaluation
    // ========================================
    
    always_comb begin
        branch_condition = 1'b0;
        
        if (branch_i) begin
            case (branch_type_i)
                BRANCH_EQ:  branch_condition = alu_zero;
                BRANCH_NE:  branch_condition = !alu_zero;
                BRANCH_LT:  branch_condition = alu_negative;
                BRANCH_GE:  branch_condition = !alu_negative;
                BRANCH_LTU: branch_condition = !alu_carry;
                BRANCH_GEU: branch_condition = alu_carry;
                default:    branch_condition = 1'b0;
            endcase
        end
    end
    
    // ========================================
    // Branch Target Calculation
    // ========================================
    
    // Branch target = PC + immediate (for branches)
    // Jump target = PC + immediate (for JAL) or rs1 + immediate (for JALR)
    always_comb begin
        if (jump_i) begin
            // For JAL: PC + immediate
            // For JALR: rs1 + immediate (detected by different ALU operation)
            if (alu_op_i == 4'b1011) begin // ALU_COPY operation indicates JALR
                branch_target = operand_a + imm_i;
            end else begin
                branch_target = pc_i + imm_i;
            end
        end else begin
            // Branch: PC + immediate
            branch_target = pc_i + imm_i;
        end
    end
    
    // ========================================
    // Control Flow Decision
    // ========================================
    
    assign take_branch = branch_i && branch_condition;
    assign take_jump = jump_i;
    assign branch_taken_o = take_branch || take_jump;
    assign branch_target_o = branch_target;
    
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
            rs2_data_o <= {XLEN{1'b0}};
            reg_write_o <= 1'b0;
            mem_read_o <= 1'b0;
            mem_write_o <= 1'b0;
            mem_size_o <= 3'b000;
            stall_o <= 1'b0;
        end else if (!stall_i) begin
            pc_o <= pc_i;
            instr_o <= instr_i;
            instr_valid_o <= instr_valid_i;
            rd_addr_o <= rd_addr_i;
            alu_result_o <= alu_result;
            rs2_data_o <= operand_b_forwarded; // Pass forwarded rs2 for stores
            reg_write_o <= reg_write_i;
            mem_read_o <= mem_read_i;
            mem_write_o <= mem_write_i;
            mem_size_o <= mem_size_i;
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
            if (!rst_i && instr_valid_i && !stall_i) begin
                $display("DEBUG EX: PC=0x%08x, ALU=%s(0x%08x, 0x%08x)=0x%08x", 
                    pc_i, alu_op_i == 4'b0000 ? "ADD" : 
                          alu_op_i == 4'b0001 ? "SUB" : 
                          alu_op_i == 4'b0010 ? "AND" : 
                          alu_op_i == 4'b0011 ? "OR" : "???",
                    operand_a, operand_b, alu_result);
                
                if (branch_taken_o) begin
                    $display("DEBUG EX: Branch taken to 0x%08x", branch_target_o);
                end
            end
        end
    `endif
    
    // ========================================
    // Assertions for Verification
    // ========================================
    
    `ifdef FORMAL
        // Formal verification properties
        
        // Branch taken should only occur for branch or jump instructions
        property branch_taken_valid;
            @(posedge clk_i) disable iff (rst_i)
            branch_taken_o |-> (branch_i || jump_i);
        endproperty
        
        // ALU result should be stable during stall
        property alu_stable_during_stall;
            @(posedge clk_i) disable iff (rst_i)
            stall_i |-> $stable(alu_result_o);
        endproperty
        
        // Forwarding should not use invalid values
        property valid_forwarding;
            @(posedge clk_i) disable iff (rst_i)
            (forward_a_i != FORWARD_NONE) |-> $isunknown(operand_a) == 1'b0;
        endproperty
        
        // Bind assertions
        assert property (branch_taken_valid) else $error("Invalid branch taken");
        assert property (alu_stable_during_stall) else $error("ALU result not stable during stall");
        assert property (valid_forwarding) else $error("Invalid forwarding value");
    `endif

endmodule

`default_nettype wire 