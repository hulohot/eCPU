/**
 * decode.sv - Decode Stage for eCPU
 * 
 * Pipeline stage that decodes RISC-V RV32I instructions and generates
 * control signals for the execute stage:
 * - Instruction field extraction (rd, rs1, rs2, immediate)
 * - Control signal generation (ALU operation, memory operations, etc.)
 * - Register file interface
 * - Immediate value generation with sign extension
 *
 * Author: Ethan
 * Date: 2024
 */

`default_nettype none

module decode #(
    parameter int XLEN = 32,              // Data width (32-bit for RV32I)
    parameter int ILEN = 32,              // Instruction width
    parameter int ADDR_WIDTH = 32,        // Address width
    parameter int REG_ADDR_WIDTH = 5      // Register address width
)(
    // Clock and reset
    input  wire logic                        clk_i,           // System clock
    input  wire logic                        rst_i,           // Active-high reset
    
    // Inputs from fetch stage
    input  wire logic [ADDR_WIDTH-1:0]      pc_i,            // Program counter
    input  wire logic [ILEN-1:0]            instr_i,         // Instruction
    input  wire logic                        instr_valid_i,   // Instruction valid
    input  wire logic                        stall_i,         // Pipeline stall
    
    // Register file interface
    input  wire logic [XLEN-1:0]            rs1_data_i,      // Register file rs1 data
    input  wire logic [XLEN-1:0]            rs2_data_i,      // Register file rs2 data
    output wire logic [REG_ADDR_WIDTH-1:0]  rs1_addr_o,      // Register file rs1 address
    output wire logic [REG_ADDR_WIDTH-1:0]  rs2_addr_o,      // Register file rs2 address
    
    // Writeback interface
    input  wire logic [REG_ADDR_WIDTH-1:0]  rd_addr_wb_i,    // Writeback register address
    input  wire logic [XLEN-1:0]            rd_data_wb_i,    // Writeback register data
    input  wire logic                        reg_write_wb_i,  // Writeback register write enable
    
    // Outputs to execute stage
    output logic [ADDR_WIDTH-1:0]           pc_o,            // Program counter
    output logic [ILEN-1:0]                 instr_o,         // Instruction
    output logic                             instr_valid_o,   // Instruction valid
    output logic [REG_ADDR_WIDTH-1:0]       rs1_addr_reg_o,  // Rs1 address for register file
    output logic [REG_ADDR_WIDTH-1:0]       rs2_addr_reg_o,  // Rs2 address for register file
    output logic [REG_ADDR_WIDTH-1:0]       rd_addr_o,       // Destination register
    output logic [XLEN-1:0]                 rs1_data_o,      // Source register 1 data
    output logic [XLEN-1:0]                 rs2_data_o,      // Source register 2 data
    output logic [XLEN-1:0]                 imm_o,           // Immediate value
    output logic [3:0]                      alu_op_o,        // ALU operation
    output logic                             alu_src_o,       // ALU source: 0=register, 1=immediate
    output logic                             reg_write_o,     // Register write enable
    output logic                             mem_read_o,      // Memory read enable
    output logic                             mem_write_o,     // Memory write enable
    output logic [2:0]                      mem_size_o,      // Memory operation size
    output logic                             branch_o,        // Branch instruction
    output logic                             jump_o,          // Jump instruction
    output logic [2:0]                      branch_type_o,   // Branch type
    output logic                             stall_o          // Stall output
);

    // RISC-V instruction formats
    typedef enum logic [2:0] {
        FMT_R = 3'b000,    // R-type (register-register)
        FMT_I = 3'b001,    // I-type (immediate)
        FMT_S = 3'b010,    // S-type (store)
        FMT_B = 3'b011,    // B-type (branch)
        FMT_U = 3'b100,    // U-type (upper immediate)
        FMT_J = 3'b101     // J-type (jump)
    } instr_format_t;
    
    // RISC-V opcodes
    typedef enum logic [6:0] {
        OP_LUI     = 7'b0110111,  // Load Upper Immediate
        OP_AUIPC   = 7'b0010111,  // Add Upper Immediate to PC
        OP_JAL     = 7'b1101111,  // Jump and Link
        OP_JALR    = 7'b1100111,  // Jump and Link Register
        OP_BRANCH  = 7'b1100011,  // Branch instructions
        OP_LOAD    = 7'b0000011,  // Load instructions
        OP_STORE   = 7'b0100011,  // Store instructions
        OP_IMM     = 7'b0010011,  // Immediate arithmetic
        OP_REG     = 7'b0110011   // Register arithmetic
    } opcode_t;
    
    // ALU operations (matching alu.sv)
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
    logic [6:0]  opcode;
    logic [2:0]  funct3;
    logic [6:0]  funct7;
    logic [4:0]  rs1_addr;
    logic [4:0]  rs2_addr;
    logic [4:0]  rd_addr;
    logic [31:0] immediate;
    logic [2:0]  instr_format;
    
    // Control signals
    logic        reg_write;
    logic        mem_read;
    logic        mem_write;
    logic [2:0]  mem_size;
    logic        branch;
    logic        jump;
    logic [2:0]  branch_type;
    logic [3:0]  alu_op;
    logic        alu_src;
    
    // ========================================
    // Instruction Field Extraction
    // ========================================
    
    assign opcode   = instr_i[6:0];
    assign rd_addr  = instr_i[11:7];
    assign funct3   = instr_i[14:12];
    assign rs1_addr = instr_i[19:15];
    assign rs2_addr = instr_i[24:20];
    assign funct7   = instr_i[31:25];
    
    // ========================================
    // Instruction Format Detection
    // ========================================
    
    always_comb begin
        case (opcode)
            OP_LUI, OP_AUIPC:                instr_format = FMT_U;
            OP_JAL:                           instr_format = FMT_J;
            OP_JALR, OP_LOAD, OP_IMM:        instr_format = FMT_I;
            OP_BRANCH:                        instr_format = FMT_B;
            OP_STORE:                         instr_format = FMT_S;
            OP_REG:                           instr_format = FMT_R;
            default:                          instr_format = FMT_I;
        endcase
    end
    
    // ========================================
    // Immediate Generation
    // ========================================
    
    always_comb begin
        immediate = 32'h0;
        
        case (instr_format)
            FMT_I: begin
                // I-type: sign-extend bits [31:20]
                immediate = {{20{instr_i[31]}}, instr_i[31:20]};
            end
            FMT_S: begin
                // S-type: sign-extend {bits[31:25], bits[11:7]}
                immediate = {{20{instr_i[31]}}, instr_i[31:25], instr_i[11:7]};
            end
            FMT_B: begin
                // B-type: sign-extend {bit[31], bit[7], bits[30:25], bits[11:8], 1'b0}
                immediate = {{19{instr_i[31]}}, instr_i[31], instr_i[7], instr_i[30:25], instr_i[11:8], 1'b0};
            end
            FMT_U: begin
                // U-type: {bits[31:12], 12'b0}
                immediate = {instr_i[31:12], 12'h0};
            end
            FMT_J: begin
                // J-type: sign-extend {bit[31], bits[19:12], bit[20], bits[30:21], 1'b0}
                immediate = {{11{instr_i[31]}}, instr_i[31], instr_i[19:12], instr_i[20], instr_i[30:21], 1'b0};
            end
            default: immediate = 32'h0;
        endcase
    end
    
    // ========================================
    // Control Signal Generation
    // ========================================
    
    always_comb begin
        // Default values
        reg_write    = 1'b0;
        mem_read     = 1'b0;
        mem_write    = 1'b0;
        mem_size     = 3'b010; // Word access by default
        branch       = 1'b0;
        jump         = 1'b0;
        branch_type  = 3'b000;
        alu_op       = ALU_ADD;
        alu_src      = 1'b0;    // Default to register
        
        case (opcode)
            OP_LUI: begin
                reg_write = 1'b1;
                alu_op = ALU_LUI;
                alu_src = 1'b1; // Use immediate
            end
            
            OP_AUIPC: begin
                reg_write = 1'b1;
                alu_op = ALU_ADD; // PC + immediate
                alu_src = 1'b1; // Use immediate
            end
            
            OP_JAL: begin
                reg_write = 1'b1;
                jump = 1'b1;
                alu_op = ALU_ADD; // PC + 4 for return address
                alu_src = 1'b1; // Use immediate
            end
            
            OP_JALR: begin
                reg_write = 1'b1;
                jump = 1'b1;
                alu_op = ALU_COPY; // rs1 + immediate for target
                alu_src = 1'b1; // Use immediate
            end
            
            OP_BRANCH: begin
                branch = 1'b1;
                branch_type = funct3;
                alu_src = 1'b0; // Use register (rs2) for comparison
                case (funct3)
                    3'b000: alu_op = ALU_SUB; // BEQ - subtract and check zero
                    3'b001: alu_op = ALU_SUB; // BNE - subtract and check not zero
                    3'b100: alu_op = ALU_SLT; // BLT - signed less than
                    3'b101: alu_op = ALU_SLT; // BGE - signed greater equal (inverted)
                    3'b110: alu_op = ALU_SLTU; // BLTU - unsigned less than
                    3'b111: alu_op = ALU_SLTU; // BGEU - unsigned greater equal (inverted)
                    default: alu_op = ALU_SUB;
                endcase
            end
            
            OP_LOAD: begin
                reg_write = 1'b1;
                mem_read = 1'b1;
                alu_op = ALU_ADD; // rs1 + immediate for address
                alu_src = 1'b1; // Use immediate for address calculation
                case (funct3)
                    3'b000: mem_size = 3'b000; // LB
                    3'b001: mem_size = 3'b001; // LH
                    3'b010: mem_size = 3'b010; // LW
                    3'b100: mem_size = 3'b100; // LBU
                    3'b101: mem_size = 3'b101; // LHU
                    default: mem_size = 3'b010;
                endcase
            end
            
            OP_STORE: begin
                mem_write = 1'b1;
                alu_op = ALU_ADD; // rs1 + immediate for address
                alu_src = 1'b1; // Use immediate for address calculation
                case (funct3)
                    3'b000: mem_size = 3'b000; // SB
                    3'b001: mem_size = 3'b001; // SH
                    3'b010: mem_size = 3'b010; // SW
                    default: mem_size = 3'b010;
                endcase
            end
            
            OP_IMM: begin
                reg_write = 1'b1;
                alu_src = 1'b1; // Use immediate for immediate instructions
                case (funct3)
                    3'b000: alu_op = ALU_ADD;  // ADDI
                    3'b010: alu_op = ALU_SLT;  // SLTI
                    3'b011: alu_op = ALU_SLTU; // SLTIU
                    3'b100: alu_op = ALU_XOR;  // XORI
                    3'b110: alu_op = ALU_OR;   // ORI
                    3'b111: alu_op = ALU_AND;  // ANDI
                    3'b001: alu_op = ALU_SLL;  // SLLI
                    3'b101: begin
                        if (funct7[5]) alu_op = ALU_SRA; // SRAI
                        else           alu_op = ALU_SRL; // SRLI
                    end
                    default: alu_op = ALU_ADD;
                endcase
            end
            
            OP_REG: begin
                reg_write = 1'b1;
                alu_src = 1'b0; // Use register for register-register instructions
                case (funct3)
                    3'b000: begin
                        if (funct7[5]) alu_op = ALU_SUB; // SUB
                        else           alu_op = ALU_ADD; // ADD
                    end
                    3'b001: alu_op = ALU_SLL;  // SLL
                    3'b010: alu_op = ALU_SLT;  // SLT
                    3'b011: alu_op = ALU_SLTU; // SLTU
                    3'b100: alu_op = ALU_XOR;  // XOR
                    3'b101: begin
                        if (funct7[5]) alu_op = ALU_SRA; // SRA
                        else           alu_op = ALU_SRL; // SRL
                    end
                    3'b110: alu_op = ALU_OR;   // OR
                    3'b111: alu_op = ALU_AND;  // AND
                    default: alu_op = ALU_ADD;
                endcase
            end
            
            default: begin
                // Unknown instruction - NOP
                reg_write = 1'b0;
                alu_op = ALU_ADD;
            end
        endcase
    end
    
    // ========================================
    // Register File Interface
    // ========================================
    
    assign rs1_addr_o = rs1_addr;
    assign rs2_addr_o = rs2_addr;
    
    // ========================================
    // Stall Signal (Combinational)
    // ========================================
    
    // Stall output should immediately reflect stall input
    assign stall_o = stall_i;
    
    // ========================================
    // Pipeline Register
    // ========================================
    
    always_ff @(posedge clk_i) begin
        if (rst_i) begin
            pc_o <= {ADDR_WIDTH{1'b0}};
            instr_o <= {ILEN{1'b0}};
            instr_valid_o <= 1'b0;
            rs1_addr_reg_o <= {REG_ADDR_WIDTH{1'b0}};
            rs2_addr_reg_o <= {REG_ADDR_WIDTH{1'b0}};
            rd_addr_o <= {REG_ADDR_WIDTH{1'b0}};
            rs1_data_o <= {XLEN{1'b0}};
            rs2_data_o <= {XLEN{1'b0}};
            imm_o <= {XLEN{1'b0}};
            alu_op_o <= ALU_ADD;
            alu_src_o <= 1'b0;
            reg_write_o <= 1'b0;
            mem_read_o <= 1'b0;
            mem_write_o <= 1'b0;
            mem_size_o <= 3'b000;
            branch_o <= 1'b0;
            jump_o <= 1'b0;
            branch_type_o <= 3'b000;
        end else if (!stall_i) begin
            pc_o <= pc_i;
            instr_o <= instr_i;
            instr_valid_o <= instr_valid_i;
            rs1_addr_reg_o <= rs1_addr;
            rs2_addr_reg_o <= rs2_addr;
            rd_addr_o <= rd_addr;
            rs1_data_o <= rs1_data_i;
            rs2_data_o <= rs2_data_i;
            imm_o <= immediate;
            alu_op_o <= alu_op;
            alu_src_o <= alu_src;
            reg_write_o <= reg_write;
            mem_read_o <= mem_read;
            mem_write_o <= mem_write;
            mem_size_o <= mem_size;
            branch_o <= branch;
            jump_o <= jump;
            branch_type_o <= branch_type;
        end
        // When stalled, hold current values (no updates needed as they're preserved automatically)
    end
    
    // ========================================
    // Debug and Verification Support
    // ========================================
    
    `ifdef DEBUG
        always_ff @(posedge clk_i) begin
            if (!rst_i && instr_valid_i && !stall_i) begin
                $display("DEBUG DEC: PC=0x%08x, Instr=0x%08x, Op=%s, rd=x%0d, rs1=x%0d, rs2=x%0d, imm=0x%08x",
                    pc_i, instr_i,
                    opcode == OP_LUI ? "LUI" :
                    opcode == OP_AUIPC ? "AUIPC" :
                    opcode == OP_JAL ? "JAL" :
                    opcode == OP_JALR ? "JALR" :
                    opcode == OP_BRANCH ? "BRANCH" :
                    opcode == OP_LOAD ? "LOAD" :
                    opcode == OP_STORE ? "STORE" :
                    opcode == OP_IMM ? "IMM" :
                    opcode == OP_REG ? "REG" : "UNKNOWN",
                    rd_addr, rs1_addr, rs2_addr, immediate);
            end
        end
    `endif

endmodule

`default_nettype wire 