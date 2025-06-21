/**
 * alu.sv - Arithmetic Logic Unit for eCPU
 * 
 * Implements all arithmetic and logical operations for RISC-V RV32I
 * ALU operations: ADD, SUB, AND, OR, XOR, SLT, SLTU, SLL, SRL, SRA
 *
 * Author: Ethan
 * Date: 2024
 */

`default_nettype none

module alu #(
    parameter int XLEN = 32  // Data width (32-bit for RV32I)
)(
    // Inputs
    input  wire logic [XLEN-1:0]     operand_a_i,  // First operand
    input  wire logic [XLEN-1:0]     operand_b_i,  // Second operand
    input  wire logic [3:0]          alu_op_i,     // ALU operation selector
    
    // Outputs
    output wire logic [XLEN-1:0]     result_o,     // ALU result
    output wire logic                zero_o,       // Zero flag (result == 0)
    output wire logic                negative_o,   // Negative flag (result[31] == 1)
    output wire logic                overflow_o,   // Overflow flag
    output wire logic                carry_o       // Carry flag
);

    // ALU operation codes
    typedef enum logic [3:0] {
        ALU_ADD  = 4'b0000,  // Addition
        ALU_SUB  = 4'b0001,  // Subtraction
        ALU_AND  = 4'b0010,  // Bitwise AND
        ALU_OR   = 4'b0011,  // Bitwise OR
        ALU_XOR  = 4'b0100,  // Bitwise XOR
        ALU_SLT  = 4'b0101,  // Set Less Than (signed)
        ALU_SLTU = 4'b0110,  // Set Less Than Unsigned
        ALU_SLL  = 4'b0111,  // Shift Left Logical
        ALU_SRL  = 4'b1000,  // Shift Right Logical
        ALU_SRA  = 4'b1001,  // Shift Right Arithmetic
        ALU_LUI  = 4'b1010,  // Load Upper Immediate (pass operand_b)
        ALU_COPY = 4'b1011   // Copy operand_a (for AUIPC, JAL, JALR)
    } alu_op_t;

    // Internal signals
    logic [XLEN-1:0]   add_result;
    logic [XLEN-1:0]   sub_result;
    logic [XLEN-1:0]   and_result;
    logic [XLEN-1:0]   or_result;
    logic [XLEN-1:0]   xor_result;
    logic [XLEN-1:0]   slt_result;
    logic [XLEN-1:0]   sltu_result;
    logic [XLEN-1:0]   sll_result;
    logic [XLEN-1:0]   srl_result;
    logic [XLEN-1:0]   sra_result;
    
    logic [XLEN:0]     add_extended;  // Extended for carry detection
    logic [XLEN:0]     sub_extended;  // Extended for borrow detection
    
    // Shift amount (only lower 5 bits for 32-bit words)
    logic [4:0] shift_amount;
    assign shift_amount = operand_b_i[4:0];
    
    // ========================================
    // Arithmetic Operations
    // ========================================
    
    // Addition with carry detection
    assign add_extended = {1'b0, operand_a_i} + {1'b0, operand_b_i};
    assign add_result = add_extended[XLEN-1:0];
    
    // Subtraction with borrow detection
    assign sub_extended = {1'b0, operand_a_i} - {1'b0, operand_b_i};
    assign sub_result = sub_extended[XLEN-1:0];
    
    // ========================================
    // Logical Operations
    // ========================================
    
    assign and_result = operand_a_i & operand_b_i;
    assign or_result  = operand_a_i | operand_b_i;
    assign xor_result = operand_a_i ^ operand_b_i;
    
    // ========================================
    // Comparison Operations
    // ========================================
    
    // Set Less Than (signed)
    assign slt_result = ($signed(operand_a_i) < $signed(operand_b_i)) ? {{(XLEN-1){1'b0}}, 1'b1} : {XLEN{1'b0}};
    
    // Set Less Than Unsigned
    assign sltu_result = (operand_a_i < operand_b_i) ? {{(XLEN-1){1'b0}}, 1'b1} : {XLEN{1'b0}};
    
    // ========================================
    // Shift Operations
    // ========================================
    
    // Shift Left Logical
    assign sll_result = operand_a_i << shift_amount;
    
    // Shift Right Logical
    assign srl_result = operand_a_i >> shift_amount;
    
    // Shift Right Arithmetic (sign extension)
    assign sra_result = $signed(operand_a_i) >>> shift_amount;
    
    // ========================================
    // Result Multiplexer
    // ========================================
    
    always_comb begin
        case (alu_op_i)
            ALU_ADD:  result_o = add_result;
            ALU_SUB:  result_o = sub_result;
            ALU_AND:  result_o = and_result;
            ALU_OR:   result_o = or_result;
            ALU_XOR:  result_o = xor_result;
            ALU_SLT:  result_o = slt_result;
            ALU_SLTU: result_o = sltu_result;
            ALU_SLL:  result_o = sll_result;
            ALU_SRL:  result_o = srl_result;
            ALU_SRA:  result_o = sra_result;
            ALU_LUI:  result_o = operand_b_i;        // Load Upper Immediate
            ALU_COPY: result_o = operand_a_i;        // Copy operand A
            default:  result_o = {XLEN{1'b0}};       // Default to zero
        endcase
    end
    
    // ========================================
    // Flag Generation
    // ========================================
    
    assign zero_o     = (result_o == {XLEN{1'b0}});
    assign negative_o = result_o[XLEN-1];
    
    // Carry flag (for ADD operation)
    assign carry_o = (alu_op_i == ALU_ADD) ? add_extended[XLEN] : 1'b0;
    
    // Overflow flag (for ADD/SUB operations)
    // Overflow occurs when:
    // - ADD: both operands have same sign, result has different sign
    // - SUB: operands have different signs, result has same sign as subtrahend
    always_comb begin
        case (alu_op_i)
            ALU_ADD: begin
                overflow_o = (operand_a_i[XLEN-1] == operand_b_i[XLEN-1]) && 
                           (result_o[XLEN-1] != operand_a_i[XLEN-1]);
            end
            ALU_SUB: begin
                overflow_o = (operand_a_i[XLEN-1] != operand_b_i[XLEN-1]) && 
                           (result_o[XLEN-1] == operand_b_i[XLEN-1]);
            end
            default: overflow_o = 1'b0;
        endcase
    end

    // ========================================
    // Assertions for Verification
    // ========================================
    
    `ifdef FORMAL
        // Formal verification properties
        
        // Addition properties
        property add_commutative;
            @(posedge clk_i) disable iff (rst_i)
            (alu_op_i == ALU_ADD) |-> 
            ##1 (result_o == (operand_a_i + operand_b_i));
        endproperty
        
        // Subtraction properties
        property sub_identity;
            @(posedge clk_i) disable iff (rst_i)
            (alu_op_i == ALU_SUB && operand_a_i == operand_b_i) |-> 
            ##1 (result_o == {XLEN{1'b0}});
        endproperty
        
        // Logical operation properties
        property and_with_zero;
            @(posedge clk_i) disable iff (rst_i)
            (alu_op_i == ALU_AND && (operand_a_i == {XLEN{1'b0}} || operand_b_i == {XLEN{1'b0}})) |-> 
            ##1 (result_o == {XLEN{1'b0}});
        endproperty
        
        property or_with_all_ones;
            @(posedge clk_i) disable iff (rst_i)
            (alu_op_i == ALU_OR && (operand_a_i == {XLEN{1'b1}} || operand_b_i == {XLEN{1'b1}})) |-> 
            ##1 (result_o == {XLEN{1'b1}});
        endproperty
        
        // Bind assertions
        assert property (add_commutative) else $error("ALU ADD not commutative");
        assert property (sub_identity) else $error("ALU SUB identity failed");
        assert property (and_with_zero) else $error("ALU AND with zero failed");
        assert property (or_with_all_ones) else $error("ALU OR with all ones failed");
    `endif

endmodule

`default_nettype wire