#include <iostream>
#include <cstdint>
#include <exception>
#include <map>
#include <sstream>
#include <string>
#include <cassert>
#include <list>
#include <memory>
#include <bitset>
#include <iomanip>

enum PAGE_SWAP_ALGO {
    FIFO,
    RND,
    LRU,
    CLOCK
};
double waterline;
constexpr uint32_t DISK_SIZE = 12 * 1024 * 1024;
constexpr uint PAGE_BIT_SIZE = 12;
constexpr uint PAGE_SIZE = ~(0xFFFFFFFF << PAGE_BIT_SIZE) + 1;
PAGE_SWAP_ALGO page_swap_algo = FIFO;

std::string timestamp_to_date(uint32_t timestamp) {
    const auto tp = std::chrono::system_clock::time_point(
        std::chrono::seconds(timestamp)
    );

    const std::time_t time = std::chrono::system_clock::to_time_t(tp);
    const std::tm* local_time = std::localtime(&time);


    std::ostringstream oss;
    oss << std::put_time(local_time, "%Y-%m-%d %H:%M:%S");
    return oss.str();
}

static void write_raw(std::vector<std::byte> &memory_, const uint32_t paddr, const uint32_t data) {
    // 小端机
    memory_[paddr] = static_cast<std::byte>(data & 0x000000FF);
    memory_[paddr + 1] = static_cast<std::byte>((data & 0x0000FF00) >> 8);
    memory_[paddr + 2] = static_cast<std::byte>((data & 0x00FF0000) >> 16);
    memory_[paddr + 3] = static_cast<std::byte>((data & 0xFF000000) >> 24);
}


static uint32_t read_raw(std::vector<std::byte> &memory_, const uint32_t paddr) {
    const auto b1 = static_cast<uint32_t>(memory_[paddr]);
    const auto b2 = static_cast<uint32_t>(memory_[paddr + 1]);
    const auto b3 = static_cast<uint32_t>(memory_[paddr + 2]);
    const auto b4 = static_cast<uint32_t>(memory_[paddr + 3]);
    return (b4 << 24) | (b3 << 16) | (b2 << 8) | b1;
}

enum FaultType {
    DIV, // divide fault
    GP, // general protection fault
    PF, // page fault
    SGV, // segmentation fault;
    UD, // Invalid Instruction Exception
};

class Fault final : std::exception {
public:
    const uint32_t vaddr;
    const FaultType type;

    Fault(const uint32_t vaddr_, const FaultType type_): vaddr(vaddr_), type(type_) {}


    const char* what() const noexcept override {
        std::map<FaultType, std::string> fault_name_map = {
            std::make_pair(FaultType::DIV, "divide error"),
            std::make_pair(FaultType::GP, "general protection fault"),
            std::make_pair(FaultType::PF, "page fault"),
            std::make_pair(FaultType::SGV, "segmentation fault"),
            std::make_pair(FaultType::UD, "invalid instruction"),

        };
        std::ostringstream oss;
        oss << "Unhandled Interrupt: " << fault_name_map[type]
        << "\n\t" << "paddr: " << vaddr << "\n";
        const auto str = new char[128];
        const std::string msg = oss.str();
        strncpy(str, msg.c_str(), std::min(static_cast<size_t>(128), msg.size()));
        return str;
    }
};

class PageTable {
public:
    struct PageTableEntry {
        uint32_t ppn{};
        bool dirty{};
        bool present{};
        bool us{}; // false->user true->supervisor
        bool wr{}; // false->ready only true->wr
        bool nx{}; // false->unexecutable true->executable
    };


    explicit PageTable(const uint32_t memory_size): pt_(std::vector<PageTableEntry>(memory_size)) {
    }

    static uint32_t get_page_number(const uint32_t addr) {
        constexpr uint32_t PAGE_NUMBER_MASK = 0xFFFFFFFF << PAGE_BIT_SIZE;
        return (addr & PAGE_NUMBER_MASK) >> PAGE_BIT_SIZE;
    }

    static uint32_t get_off(const uint32_t addr) {
        constexpr uint32_t OFF_MASK = ~(0xFFFFFFFF << PAGE_BIT_SIZE);
        return addr & OFF_MASK;
    }

    void set_mapping(const uint32_t vaddr, const uint32_t ppn, bool nx = true, bool us = false, const bool wr = true) {
        auto page_number = get_page_number(vaddr);
        pt_[page_number].ppn = vaddr;
        pt_[page_number].dirty = false;
        pt_[page_number].present = true;
        pt_[page_number].us = us;
        pt_[page_number].wr = wr;
        pt_[page_number].nx = nx;
    }

    void set_ppn(const uint32_t vaddr, const uint32_t ppn) {
        const auto page_number = get_page_number(vaddr);
        pt_[page_number].ppn = ppn;
    }

    uint32_t translate(const uint32_t vaddr) const {
        const uint32_t vpn = get_page_number(vaddr);
        const uint32_t offset = get_off(vaddr);
        const uint32_t ppn = pt_[vpn].ppn;
        return ppn << PAGE_BIT_SIZE | offset;
    }

    bool is_dirty(const uint32_t vaddr) const {
        const auto page_number = get_page_number(vaddr);
        return pt_[page_number].dirty;
    }

    bool is_present(const uint32_t vaddr) const {
        const auto page_number = get_page_number(vaddr);
        return pt_[page_number].present;
    }

    bool is_supervisor(const uint32_t vaddr) const {
        const auto page_number = get_page_number(vaddr);
        return pt_[page_number].us;
    }

    bool is_write(const uint32_t vaddr) const {
        const auto page_number = get_page_number(vaddr);
        return pt_[page_number].wr;
    }

    bool is_exec(const uint32_t vaddr) const {
        const auto page_number = get_page_number(vaddr);
        return pt_[page_number].nx;
    }

    void set_dirty(const uint32_t vaddr, bool dirty) {
        const auto page_number = get_page_number(vaddr);
        pt_[page_number].dirty = dirty;
    }

    void set_present(const uint32_t vaddr, bool present) {
        const auto page_number = get_page_number(vaddr);
        pt_[page_number].present = false;
    }

    uint32_t alloc_physical_page() {
        if (free_list.empty()) {
            throw std::runtime_error("尽管这种情况几乎不会出现，但是如果真出现了，那就上OOM Killer上吧");
        }
        const uint32_t back = free_list.back();
        free_list.pop_back();
        return back;
    }

    void return_physical_page(uint32_t ppn) {
        free_list.push_back(ppn);
    }

private:
    std::list<uint32_t> free_list;   // 由内核管理的空闲链表感觉不如用位图

private:
    std::vector<PageTableEntry> pt_;
};

class MMU {
public:
    MMU(PageTable& pt, std::vector<std::byte> &memory): memory_(memory), pt_(pt) {}

private:
    std::vector<std::byte> &memory_;
    PageTable& pt_;



public:
    void write(const uint32_t vaddr, const uint32_t mdr) const {
        if (!pt_.is_write(vaddr)) {
            throw Fault(vaddr, FaultType::GP);
        }
        if (!pt_.is_present(vaddr)) {
            throw Fault(vaddr, FaultType::PF);
        }
        pt_.set_dirty(vaddr, true);
        const uint32_t paddr = pt_.translate(vaddr);
        write_raw(memory_, paddr, mdr);
    }

    uint32_t read(const uint32_t vaddr) const {
        if (!pt_.is_present(vaddr)) {
            throw Fault(vaddr, FaultType::PF);
        }
        const uint32_t paddr = pt_.translate(vaddr);
        return read_raw(memory_, paddr);
    }

    uint32_t read_instruction(const uint32_t vaddr) const {
        if (!pt_.is_present(vaddr)) {
            throw Fault(vaddr, FaultType::PF);
        }
        if (!pt_.is_exec(vaddr)) {
            throw Fault(vaddr, FaultType::GP);
        }
        return read(vaddr);
    }
};

enum InstructionType {
    NOP,
    MOV_IL,   // mov_il 8 | reg 8 | imm 16  立即数     -> 寄存器低位
    MOV_IH,   // mov_il 8 | reg 8 | imm 16  立即数     -> 寄存器高位
    MOV_M,    // mov_m  8 | 8 | reg_a 8 | reg_b 8 |   -> reg_b->[reg_a]
    MOV_R,    // mov_r 8  | 8 | reg_a 8 | reg_b 8 |   -> [reg_a]-> reg_b
    JMP_I,    // jmp 8 |  imm 24  |                   -> 立即数无条件跳转
    JMP_R,    // jmp 8 |  16  | reg                   -> 无条件跳转寄存器
    HLT,

};

class CPU {


    static uint32_t low_24(const uint32_t value) {
        return value & 0x00FFFFFF;
    }

    // heigh -> low
    static uint32_t get_byte(const uint32_t value, int idx) {
        assert(0 <= idx && idx < 4);
        const uint32_t shf_bits = 8 * (3 - idx);
        return (value& (0x000000FF << shf_bits)) >> shf_bits;
    }

    static uint16_t low_word(const uint32_t value) {
        return (value & 0x0000FFFF);
    }

    uint32_t &get_reg(const uint8_t reg) {
        assert(reg < 4);
        assert(reg != 0);
        const std::array reg_arr = {
            &eax, &eax, &ebx, &ecx, &edx
        };
        return *reg_arr[reg];
    }

    void _fetch_instruction() {
        ir = mmu.read_instruction(ip);
        ip += 4;
    }

    // is read access
    void _decode_instruction() {
        i_type = static_cast<InstructionType>(get_byte(ir, 0));
        switch (i_type) {
            case MOV_IL:
            case MOV_IH:
                reg_addr[1] = get_byte(ir, 1);
                operand = low_word(ir);
                break;
            case MOV_R:     //  内存 -> 寄存器
            case MOV_M:     // 寄存器 -> 内存
                reg_addr[2] = get_byte(ir, 2);
                reg_addr[3] = get_byte(ir, 3);
                break;
            case JMP_I:
                operand = low_24(ir);
                break;
            case JMP_R:
                reg_addr[3] = get_byte(ir, 3);
                break;
            case NOP:
            case HLT:
                break;
            default:
                throw Fault(ip, FaultType::UD);
        }

        // switch (i_type) {
        //     case MOV_IL:
        //         reg_addr[1] = get_byte(ir, 1);
        //         break;
        //     case MOV_IH:
        //         reg_addr[0] = get_byte(ir, 0);
        //         break;
        // }
    }


    void _calculate_operand(uint32_t &read_addr, uint32_t &write_addr) {  // 生成地址
        switch (i_type) {
            case MOV_R:
                read_addr = get_reg(reg_addr[2]);
                write_addr = 0;
                break;
            case MOV_M:
                write_addr = get_reg(reg_addr[2]);
                read_addr = 0;
                break;
            default:
                break;
        }
    }

    void _fetch_operand() { // 访存
        if (i_type != MOV_R) {
            return;
        }
        mdr = mmu.read(mar);
    }

    void _execute_instruction() { // 执行
        switch (i_type) {
            case MOV_IL: {
                auto &reg = get_reg(reg_addr[1]);
                reg = reg & 0xFFFF0000;
                reg = reg | (operand & 0x0000FFFF);
                break;
            }
            case MOV_IH: {
                auto &reg = get_reg(reg_addr[1]);
                reg = reg & 0x0000FFFF;
                reg = reg | ((operand & 0x0000FFFF) << 16);
                break;
            }
            case MOV_R: { //  内存 -> 寄存器
                auto &reg = get_reg(reg_addr[3]);
                reg = mdr;
                break;
            }
            case MOV_M: { // 寄存器 -> 内存
                const auto &reg = get_reg(reg_addr[3]);
                mdr = reg;
                break;
            }
            case JMP_I: {
                ip = operand;
                break;
            }
            case JMP_R: {
                const auto &reg = get_reg(reg_addr[3]);
                ip = reg;
                break;
            }
            case HLT:
               shutdown = true;
            default:
                break;
        }
    }

    void _write_operand() const { // 写回
        if (i_type != MOV_M) {
            return;
        }
        mmu.write(mar, mdr);
    }

public:
    CPU(PageTable &pt,  std::vector<std::byte> &memory_, const uint32_t init_ip = 0x7c00, const uint32_t mem_size = 32 * 1024 * 1024)
        : memory(memory_), cr3(pt), eax(0), ebx(0),
          ecx(0), edx(0), ip(init_ip), mmu(pt, memory) {
    }


    void step() {
        assert(!shutdown);
        uint32_t read_addr, write_addr;
        _fetch_instruction();
        _decode_instruction();
        _calculate_operand(read_addr, write_addr);
        mar = read_addr;
        _fetch_operand();
        _execute_instruction();
        mar = write_addr;
        _write_operand();
    }

    friend std::ostream &operator<<(std::ostream &os, const CPU &cpu) {
        const std::ios_base::fmtflags flags = os.flags();
        os  << "eax: " << cpu.eax
            << "; ebx: " << cpu.ebx
            << "; ecx: " << cpu.ecx
            << "; edx: " << cpu.edx
            << "; ip: " << cpu.ip << "\n";
        os << std::hex;
        os << "last: " << cpu.ir;
        os.flags(flags);
        return os;
    }

public:
    std::vector<std::byte> &memory;
    bool shutdown = false;
private:
    PageTable &cr3;
    uint32_t eax;
    uint32_t ebx;
    uint32_t ecx;
    uint32_t edx;
    uint32_t ip;

    MMU mmu;

    // 内部寄存器，用户不可见
    uint32_t ir{};  // 你懂的IR
    InstructionType i_type = NOP;
    uint32_t mar = 0; // 你懂的MAR
    uint32_t mdr = 0; // MDR
    uint32_t reg_addr[4]{};   // 寄存器地址 指令 4 byte，所以0位置永远不会使用
    uint32_t operand{};       // 操作数



};

enum InodeType {
    INODE_FILE,
    INODE_DIR,
    INODE_SLINK
};

struct Inode {
    int ref_count;
    InodeType type;
    uint32_t size;
    uint16_t mod;
    uint32_t uid;
    uint32_t gid;
    uint32_t atime;
    uint32_t mtime;
    uint32_t ctime;
    uint32_t addr[12];
    std::unique_ptr<std::array<uint32_t, 1024>> addr1;
    bool del_flag = false;

    char type2c() const {
        switch (type) {
            case INODE_FILE:
                return '-';
            case INODE_DIR:
                return 'd';
            case INODE_SLINK:
                return 's';
            default:
                return '-';
        }
    }

    char mod2c(const int idx) const {
        assert(idx >= 0 && idx < 9);
        char c = '-';
        if (mod & (static_cast<uint16_t>(0b100000000) >> idx)) {
            constexpr char sym[] = {'r', 'w', 'x'};
            c = sym[idx % 3];
        }
        return c;
    }

    friend std::ostream &operator<<(std::ostream &os, const Inode &inode) {
        os << inode.type2c();
        for (int i = 0; i < 9; i++) {
            os << inode.mod2c(i);
        }
        os << "\t" << inode.size
        << "\t" << inode.uid
        << "\t" << inode.gid
        << "\t" <<  timestamp_to_date(inode.mtime);
        return os;
    }
};


class FileSystem {
private:
public:
    // 连续分配一块
    uint32_t _alloc() {
        uint32_t idx = 0;
        for (size_t i = 0; i < bitmap.size(); ++i) {
            if (!bitmap[i]) {
                idx = i;
                break;
            }
        }

        if (idx == 0) {
            return 0;
        }

        bitmap[idx] = true;
        return idx * PAGE_SIZE;
    }

    void _alloc_indirect(Inode &inode, const uint32_t block_idx) {
        assert(block_idx < 1024);
        inode.addr1 = std::make_unique<std::array<uint32_t, 1024>>();
        for (int i = 0; i < block_idx; i++) {
            inode.addr1->at(i) = _alloc();
            assert(inode.addr[i] != 0);
        }
    }

    void _alloc_index(Inode &inode, const uint32_t block_idx) {
        // 14 三级表 13 二级表 12 一级表
        for (uint32_t i = 0; i <= std::min(static_cast<uint32_t>(11), block_idx - 1); i++) {
            if (inode.addr[i] == 0) {
                inode.addr[i] = _alloc();
                assert(inode.addr[i] != 0);
            }
        }
        if (block_idx > 11) {
            _alloc_indirect(inode, block_idx - 11);
        }
    }

    std::array<std::byte, PAGE_SIZE> _read_block(const uint32_t block_idx) {
        assert(bitmap[block_idx]);
        std::array<std::byte, PAGE_SIZE> block{};
        const uint32_t idx = block_idx * PAGE_SIZE;
        for (uint32_t i = 0; i < PAGE_SIZE; i++) {
            block[i] = disk[idx + i];
        }
        return block;
    }

    void _write_block(const uint32_t block_idx, const std::array<std::byte, PAGE_SIZE> &data) {
        assert(bitmap[block_idx]);
        const uint32_t idx = block_idx * PAGE_SIZE;
        for (uint32_t i = 0; i < PAGE_SIZE; i++) {
            disk[idx + i] = data[i];
        }
    }

    // 根据索引计算块索引，向上取整
    static uint32_t block_cell(const uint32_t idx) {
        return idx / PAGE_SIZE + (idx % PAGE_SIZE ? 1 : 0);
    }

    static uint32_t get_real_block_idx(const Inode &inode, uint32_t block_idx, const bool read = false) {
        assert(!read || (block_idx < block_cell(inode.size)));
        if (block_idx <= 11) {
            return inode.addr[block_idx] / PAGE_SIZE;
        }
        block_idx -= 11;
        return inode.addr1->at(block_idx) / PAGE_SIZE;
    }

    // 返回最终大小
    uint32_t _write(Inode &inode, const uint32_t idx, const std::vector<std::byte> &data) {
        const uint32_t data_size = data.size();
        uint32_t logic_block_idx = idx / PAGE_SIZE; // 逻辑地址
        const uint32_t file_size = std::max(inode.size, idx + data_size); // 文件最终大小
        _alloc_index(inode, block_cell(file_size));

        uint32_t block_idx = get_real_block_idx(inode, logic_block_idx); // 真实地址

        // 读取
        const uint32_t offset = idx % PAGE_SIZE; // 块内偏移
        std::array<std::byte, PAGE_SIZE> block = _read_block(block_idx);  // 先读
        uint32_t data_idx = 0;
        for (uint32_t i = offset; i < std::min(PAGE_SIZE, data_size); i++) {
            block[i] = data[data_idx++];
        }
        _write_block(block_idx, block);                                    // 再写回


        // 还剩下，则继续写入，继续写入的部分将正好可以按照块直接写, 不完全覆盖部分将单独处理，这里是完全覆盖
        const int left_data_block_size = static_cast<int>((data_size - data_idx) / PAGE_SIZE); // 数据剩下的块大小
        for (int i = 0; i < left_data_block_size; i++) {
            assert(data_idx < data_size);
            logic_block_idx++;
            block_idx = get_real_block_idx(inode, logic_block_idx);     // 下n块的真实地址
            for (int j = 0; j < PAGE_SIZE; j++) {
                block[i] = data[data_idx++];
            }
            _write_block(block_idx, block);
        }

        // 处理剩下的尾巴
        if (data_idx < data_size) {
            logic_block_idx++;
            block_idx = get_real_block_idx(inode, logic_block_idx); // 真实地址
            block = _read_block(block_idx);  // 先读
            for (int i = 0; i < data_size - data_idx; i++) {
                block[i] = data[data_idx++];
            }
            _write_block(block_idx, block); // 写回
        }

        return file_size;
    }

    std::vector<std::byte> _read(const Inode &inode, const uint32_t idx, const uint32_t size) {
        std::vector<std::byte> bytes(size);
        uint32_t logical_block_idx = idx / PAGE_SIZE;
        uint32_t block_idx = get_real_block_idx(inode, logical_block_idx, true);

        uint32_t data_idx = 0;

        // 处理开头不规矩部分
        std::array<std::byte, PAGE_SIZE> block = _read_block(block_idx);
        const uint32_t offset = idx % PAGE_SIZE;
        for (uint32_t i = offset; i < std::min(PAGE_SIZE, size); i++) {
            bytes[data_idx++] = block[i];
        }


        // 处理剩下的
        const uint32_t left_block_size = (size - data_idx) / PAGE_SIZE;
        for (uint32_t i = 0; i < left_block_size; i++) {
            assert(data_idx < size);
            logical_block_idx++;
            block_idx = get_real_block_idx(inode, logical_block_idx, true);
            block = _read_block(block_idx);
            const uint32_t data_idx_cpy = data_idx;
            for (uint32_t j = 0; j < std::min(PAGE_SIZE, size - data_idx_cpy); j++) {
                bytes[data_idx++] = block[j];
            }
        }

        // 处理剩下的尾巴
        if (data_idx < size) {
            logical_block_idx++;
            block_idx = get_real_block_idx(inode, logical_block_idx); // 真实地址
            block = _read_block(block_idx);  // 先读
            for (uint32_t j = 0; j < size; j++) {
                bytes[data_idx++] = block[j];
            }
        }

        return bytes;
    }

    uint32_t _create_inode(const InodeType type, const uint16_t mod, const uint32_t uid, const uint32_t gid) {
        const auto it = std::ranges::find_if(std::as_const(inodes), [] (const Inode &node) {return node.del_flag;});
        uint32_t ino;
        if (it == inodes.cend()) {
            const auto now = std::chrono::system_clock::now();
            uint32_t timestamp = std::chrono::duration_cast<std::chrono::seconds>(
                now.time_since_epoch()
            ).count();
            inodes.emplace_back(1, type, 0, mod, uid, gid, timestamp, timestamp, timestamp);
            ino = inodes.size() - 1;
        } else {
            const auto now = std::chrono::system_clock::now();
            uint32_t timestamp = std::chrono::duration_cast<std::chrono::seconds>(
                now.time_since_epoch()
            ).count();
            inodes.emplace(it ,1, type, 0, mod, uid, gid, timestamp, timestamp, timestamp);
            ino = it - inodes.cbegin();
        }
        return ino;
    }

    Inode &_stat(const uint32_t ino) {
        assert(ino < inodes.size());
        assert(!inodes[ino].del_flag);
        return inodes[ino]; // should be ok....
    }

public:
    void mkdir()


public:
    FileSystem(): disk() {
        bitmap[0] = true; // 0号位置表示无效
    }

private:
    std::vector<Inode> inodes;
    std::bitset<DISK_SIZE / PAGE_SIZE> bitmap;
    std::array<std::byte, DISK_SIZE> disk;


};



enum REG {
    NUL = 0,
    EAX = 1,
    EBX = 2,
    ECX = 3,
    EDX = 4
};


uint32_t make_instruction(const InstructionType type, const std::array<REG, 4> regs, const uint32_t imm) {
    assert(regs[0] == NUL);
    for (int i = 1; i < 4; i++) {
        assert(regs[i] < 4);
    }

    uint32_t instruction = 0;
    instruction |= static_cast<uint32_t>(type) << 24;
    switch (type) {
        case MOV_IL:
        case MOV_IH:
            assert(regs[1] != NUL);
            instruction |= regs[1] << 16;
            instruction |= imm & 0x0000FFFF;
            break;
        case MOV_M:
        case MOV_R:
            assert(regs[3] != NUL);
            assert(regs[2] != NUL);
            instruction |= regs[3];
            instruction |= regs[2] << 8;
            break;
        case JMP_I:
            instruction |= (imm & 0x00FFFFFF);
            break;
        case JMP_R:
            assert(regs[3] != NUL);
            instruction |= regs[3];
            break;
        case NOP:
        case HLT:
            break;
        default:
            throw std::runtime_error("unknown instruction");
    }
    return instruction;

}
PageTable init_pt(const uint32_t vmem_size) {
    PageTable pt(vmem_size);
    pt.set_mapping(0, 0);
    return pt;
}

std::vector<std::byte> init_memory(const uint32_t pmem_size) {
    std::vector<std::byte> memory(pmem_size);
    /*
     *  0  NOP
     *  4  MOV_IL eax, 1
     *  8  MOV_IH eax, 1
     *  12 MOV_IL ecx, 4
     *  16 MOV_IH ecx, 0
     *  20 MOV_R  ecx, ebx     ebx = [ecx]
     *  24 MOV_IL ecx, 40
     *  28 MOV_M  ecx, ebx     [ecx] = ebx
     *  32 JMP 36
     *  36 JMP ecx
     *  40 NOP
     *  44 HLT
     */
    std::vector<uint32_t> codes = {
        make_instruction(NOP, {NUL, NUL, NUL, NUL}, 0),
        make_instruction(MOV_IL, {NUL, EAX, NUL, NUL}, 1),
        make_instruction(MOV_IH, {NUL, EAX, NUL, NUL}, 1),
        make_instruction(MOV_IL, {NUL, ECX, NUL, NUL}, 4),
        make_instruction(MOV_IH, {NUL, ECX, NUL, NUL}, 0),
        make_instruction(MOV_R, {NUL, NUL, ECX, EBX}, 1),
        make_instruction(MOV_IL, {NUL, ECX, NUL, NUL}, 40),
        make_instruction(MOV_M, {NUL, NUL, ECX, EBX}, 1),
        make_instruction(JMP_I, {NUL, NUL, NUL, NUL}, 36),
        make_instruction(JMP_R, {NUL, NUL, NUL, ECX}, 0),
        make_instruction(NOP, {NUL, NUL, NUL, NUL}, 0),
        make_instruction(HLT, {NUL, NUL, NUL, NUL}, 0),
    };
    uint32_t paddr = 0;
    for (const uint32_t code : codes) {
        // std::cout << std::hex << code << std::endl;
        write_raw(memory, paddr, code);

        paddr += 4;
    }

    paddr = 0;
    for (const uint32_t code : codes) {
        std::cout << std::hex << read_raw(memory, paddr) << std::endl;
        paddr += 4;
    }

    return memory;
}



static bool needs_reclaim(const uint32_t mem_size, const uint32_t curr_size) {
    assert(waterline > 0 && waterline < 1);
    assert(mem_size >= curr_size);
    const uint32_t total_pages = mem_size / PAGE_SIZE;
    return (1.0 * curr_size / total_pages) > waterline;
}


// 普通改进版CLOCK算法
void swap_clock(PageTable &pt, std::vector<std::byte> &memory, const Fault &fault) {
    static std::list<PageTable::PageTableEntry *> dirty_list;
    static std::list<PageTable::PageTableEntry *> clean_list;
    uint32_t ppn;
    if (!needs_reclaim(memory.size(), dirty_list.size() + clean_list.size())) {
        ppn = pt.alloc_physical_page();
    } else {

        ppn = 1;
    }

    pt.set_ppn(fault.vaddr, ppn);
    pt.set_present(fault.vaddr, true);
}


// Linux采用的双层链表改进的CLOCK算法


void page_fault_handler(PageTable &pt, std::vector<std::byte> &memory, const Fault &fault) {
    uint32_t ppn = PageTable::get_page_number(fault.vaddr);
}



int main() {
    auto *fs = new FileSystem();
    std::vector<std::byte> p;
    for (int i = 0; i < PAGE_SIZE * 14; i++) {
        p.push_back(static_cast<std::byte>(i % 256));
    }
    const uint32_t ino = fs->_create_inode(InodeType::INODE_FILE, 0b111111111, 1, 1);
    Inode &inode = fs->_stat(ino);
    const uint32_t size = fs->_write(inode, 1, p);
    inode.size = size;
    std::cout << inode << std::endl;
    auto result = fs->_read(inode, 0, 4096);
    for (auto byte : result) {
        std::cout << static_cast<uint16_t>(byte) << " " ;
    }
    std::cout << std::endl;
    result = fs->_read(inode, 4096 * 13, 4097);
    for (auto byte : result) {
        std::cout << static_cast<uint16_t>(byte) << " " ;
    }
    delete fs;
    // fs._write()
}



// int main() {
//     waterline = 0.8;
//     page_swap_algo = FIFO;
//     std::cout << "dist size: " << DISK_SIZE << std::endl;
//     std::cout << "page size: " << PAGE_SIZE << std::endl;
//     constexpr uint32_t vmem_size = 16 * 1024 * 1024;
//     constexpr uint32_t pmem_size = 1 * 1024 * 1024;
//     constexpr uint32_t pages = vmem_size / PAGE_SIZE;
//     std::cout << "pages: " << pages << std::endl;
//     std::cout << "pmem_size: " << (pmem_size / 1024 / 1024) << "MB" << std::endl;
//
//     PageTable pt = init_pt(vmem_size);
//     pt.set_present(0, false);
//     std::vector<std::byte> memory = init_memory(pmem_size);
//     CPU cpu(pt, memory, 0);
//     std::cout << std::dec;
//     try {
//         while (!cpu.shutdown) {
// IRET:
//             cpu.step();
//             std::cout << cpu << std::endl;
//         }
//     } catch (const Fault& fault) {
//         if (fault.type == PF) {
//             page_fault_handler(pt, memory, fault);
//             goto IRET;
//         }
//         printf(fault.what());
//     }
//     return 0;
// }
