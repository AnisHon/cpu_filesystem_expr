#include <algorithm>
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
#include <chrono>
#include <iomanip>
#include <cstring>
#include <filesystem>
#include <ranges>
#include <utility>

#define RED "\033[31m"
#define RESET "\033[0m"

enum PAGE_SWAP_ALGO {
    FIFO,
    RND,
    LRU,
    CLOCK
};
uint32_t waterline;
constexpr uint32_t DISK_SIZE = 12 * 1024 * 1024;
constexpr unsigned int PAGE_BIT_SIZE = 12;
constexpr unsigned int PAGE_SIZE = ~(0xFFFFFFFF << PAGE_BIT_SIZE) + 1;
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

std::vector<std::string> split_string(const std::string &s, const char delimiter) {
    std::vector<std::string> tokens;
    std::string token;
    std::istringstream tokenStream(s);

    while (std::getline(tokenStream, token, delimiter)) {
        if (token.empty()) {
            continue;
        }
        tokens.push_back(token);
    }

    return tokens;
}
std::string normalizePath(const std::vector<std::string>& pathComponents) {
    std::vector<std::string> normalized;

    for (const auto& component : pathComponents) {
        if (component == ".") {
            continue;
        } else if (component == "..") {
            if (!normalized.empty()) {
                normalized.pop_back();
            }
        } else {
            normalized.push_back(component);
        }
    }

    std::string result;
    for (const auto& dir : normalized) {
        result += "/" + dir;
    }

    return result.empty() ? "/" : result;
}

std::string calculateFinalPath(const std::string& currentPath, const std::string& changePath) {
    if (changePath.empty()) {
        return currentPath;
    }

    // 处理绝对路径
    if (changePath[0] == '/') {
        return normalizePath(split_string(changePath, '/'));
    }

    // 处理相对路径
    std::vector<std::string> currentComponents = split_string(currentPath, '/');
    std::vector<std::string> changeComponents = split_string(changePath, '/');

    currentComponents.insert(currentComponents.end(),
                            changeComponents.begin(),
                            changeComponents.end());
    return normalizePath(currentComponents);
}

static void write_raw(std::vector<std::byte> &memory_, const uint32_t paddr, const uint32_t data) {
    // 小端机
    memory_[paddr] = static_cast<std::byte>(data & 0x000000FF);
    memory_[paddr + 1] = static_cast<std::byte>((data & 0x0000FF00) >> 8);
    memory_[paddr + 2] = static_cast<std::byte>((data & 0x00FF0000) >> 16);
    memory_[paddr + 3] = static_cast<std::byte>((data & 0xFF000000) >> 24);
}


static uint32_t read_raw(const std::vector<std::byte> &memory_, const uint32_t paddr) {
    const auto b1 = static_cast<uint32_t>(memory_[paddr]);
    const auto b2 = static_cast<uint32_t>(memory_[paddr + 1]);
    const auto b3 = static_cast<uint32_t>(memory_[paddr + 2]);
    const auto b4 = static_cast<uint32_t>(memory_[paddr + 3]);
    return (b4 << 24) | (b3 << 16) | (b2 << 8) | b1;
}

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

    [[nodiscard]] char type2c() const {
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

    [[nodiscard]] bool get_mod(const int idx) const {
        assert(idx >= 0 && idx < 9);
        return static_cast<bool>(mod & (static_cast<uint16_t>(0b100000000) >> idx));
    }

    [[nodiscard]] char mod2c(const int idx) const {
        assert(idx >= 0 && idx < 9);
        char c = '-';
        if (get_mod(idx)) {
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

struct FileAttr {
    InodeType type;
    uint16_t mod;
    uint32_t uid;
    uint32_t gid;
};

class FileBlockLayer {
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

    static void _update_ctime(Inode &node) {
        const auto now = std::chrono::system_clock::now();
        const uint32_t timestamp = std::chrono::duration_cast<std::chrono::seconds>(
            now.time_since_epoch()
        ).count();
        node.ctime = timestamp;
    }

    static void _update_mtime(Inode &node) {
        const auto now = std::chrono::system_clock::now();
        const uint32_t timestamp = std::chrono::duration_cast<std::chrono::seconds>(
            now.time_since_epoch()
        ).count();
        node.mtime = timestamp;
    }

    static void _update_atime(Inode &node) {
        const auto now = std::chrono::system_clock::now();
        const uint32_t timestamp = std::chrono::duration_cast<std::chrono::seconds>(
            now.time_since_epoch()
        ).count();
        node.atime = timestamp;
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

    [[nodiscard]] std::array<std::byte, PAGE_SIZE> _read_block(const uint32_t block_idx) const {
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
    uint32_t write(Inode &inode, const uint32_t idx, const std::vector<std::byte> &data) {
        const uint32_t data_size = data.size();
        uint32_t logic_block_idx = idx / PAGE_SIZE; // 逻辑地址
        const uint32_t file_size = std::max(inode.size, idx + data_size); // 文件最终大小
        _alloc_index(inode, block_cell(file_size));

        uint32_t block_idx = get_real_block_idx(inode, logic_block_idx); // 真实地址

        // 读取
        const uint32_t offset = idx % PAGE_SIZE; // 块内偏移
        std::array<std::byte, PAGE_SIZE> block = _read_block(block_idx);  // 先读
        uint32_t data_idx = 0;
        for (uint32_t i = offset; i < PAGE_SIZE && data_idx < data_size; i++) {
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
                block[j] = data[data_idx++];
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

        // 更新修改时间
        _update_ctime(inode);
        _update_mtime(inode);
        return file_size;
    }

    std::vector<std::byte> read(Inode &inode, const uint32_t idx, const uint32_t size) const {
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
            for (uint32_t j = 0; j < size - data_idx; j++) {
                bytes[data_idx++] = block[j];
            }
        }


        // 更新访问时间
        _update_atime(inode);
        _update_mtime(inode);
        return bytes;
    }

    uint32_t create_inode(const InodeType type, const uint16_t mod, const uint32_t uid, const uint32_t gid) {
        const auto it =
            std::find_if(inodes.cbegin() + 1, inodes.cend(), [] (const Inode &node) {return node.del_flag;});
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

    Inode &stat(const uint32_t ino) {
        assert(ino != 0);
        assert(ino < inodes.size());
        assert(!inodes[ino].del_flag);
        return inodes[ino]; // should be ok....
    }

    void trunc(const uint32_t ino, const uint32_t size) {
        assert(ino != 0);
        assert(ino < inodes.size());
        assert(!inodes[ino].del_flag);
        inodes[ino].size = size; // should be ok....
    }

    [[nodiscard]] bool exist(const uint32_t ino) const {
        if (ino >= inodes.size()) {
            return false;
        }

        return !inodes[ino].del_flag;
    }


public:
    FileBlockLayer(): disk() {
        bitmap[0] = true; // 0号位置表示无效
        inodes.emplace_back(0, InodeType::INODE_FILE, 0, 0, 0, 0, 0, 0, false); // 0 inode表示无效
    }

private:
    std::vector<Inode> inodes;
    std::bitset<DISK_SIZE / PAGE_SIZE> bitmap;
    std::array<std::byte, DISK_SIZE> disk;


};

struct FileDesc {
    uint32_t fpos;
    uint8_t mod;
    uint32_t ino;
};

class FileSystem {


struct DirRec {
    uint32_t ino;
    uint16_t rec_len;   // 记录长度
    uint8_t name_len;
    const char *name;
};

private:

    static std::list<DirRec> bytes2rec(const std::vector<std::byte> &bytes) {
        std::list<DirRec> records;
        uint32_t ptr = 0;
        while (ptr < bytes.size()) {
            uint32_t ino = (static_cast<uint32_t>(bytes[ptr]) << 24)
            | (static_cast<uint32_t>(bytes[ptr + 1]) << 16)
            | (static_cast<uint32_t>(bytes[ptr + 2]) << 8)
            | (static_cast<uint32_t>(bytes[ptr + 3]));
            uint16_t rec_len = (static_cast<uint16_t>(bytes[ptr + 4]) << 8)
            | (static_cast<uint16_t>(bytes[ptr + 5]));
            uint8_t name_len = (static_cast<uint8_t>(bytes[ptr + 6]));
            records.emplace_back(ino, rec_len, name_len, reinterpret_cast<const char *>(&bytes[ptr + 7]));
            ptr += rec_len;
        }


        return records;
    }

    // 顺序查找name的函数
    [[nodiscard]] uint32_t _scan_dir(const uint32_t pino, const std::string &name) const {
        assert(pino != 0);
        Inode &inode = block_layer->stat(pino);
        uint32_t ino = 0;
        const auto data = block_layer->read(inode, 0, inode.size);

        for (const auto recs = bytes2rec(data); const auto rec : recs) {
            if (rec.ino == 0) {
                continue;
            }
            if (std::string(rec.name, rec.name_len) == name) {
                ino = rec.ino;
            }
        }
        return ino;
    }

    static void bytes2rec(const std::list<DirRec> & recs, std::vector<std::byte> &bytes) {
        uint32_t ptr = 0;
        for (const auto & [ino, rec_len, name_len, name] : recs) {
            assert(ptr + rec_len <= bytes.size());
            bytes[ptr] = static_cast<std::byte>(ino >> 24);
            bytes[ptr + 1] = static_cast<std::byte>((ino & 0x00FF0000) >> 16);
            bytes[ptr + 2] = static_cast<std::byte>((ino & 0x0000FF00) >> 8);
            bytes[ptr + 3] = static_cast<std::byte>(ino & 0x000000FF);
            bytes[ptr + 4] = static_cast<std::byte>(rec_len >> 8);
            bytes[ptr + 5] = static_cast<std::byte>(rec_len & 0x00FF);
            bytes[ptr + 6] = static_cast<std::byte>(name_len);
            for (int i = 0; i < name_len; ++i) {
                bytes[ptr + 7 + i] = static_cast<std::byte>(name[i]);
            }
            ptr += rec_len;
        }
    }

    void _create_rec(const uint32_t ino, const DirRec &dir_rec) const {
        Inode &inode = block_layer->stat(ino);
        auto data = block_layer->read(inode, 0, inode.size);
        auto recs = bytes2rec(data);
        auto curr = recs.begin();
        for (; curr != recs.end(); ++curr) {
            if (const auto &rec = *curr; rec.ino != 0 || rec.rec_len < dir_rec.rec_len) {
                continue;
            }
            break;
        }

        assert(curr != recs.end());
        if (curr->rec_len - dir_rec.rec_len > 8) {
            recs.emplace(curr, 0, curr->rec_len - dir_rec.rec_len, 0, nullptr);
            curr->rec_len = dir_rec.rec_len;
        }
        curr->ino = dir_rec.ino;
        curr->name_len = dir_rec.name_len;
        curr->name = dir_rec.name;

        bytes2rec(recs, data);
        block_layer->write(inode, 0, data);

    }

    void _assign_empty_dir(const uint32_t ino) const {
        Inode &inode = block_layer->stat(ino);
        std::vector<std::byte> data(PAGE_SIZE);
        const std::list<DirRec> recs = {{
            .ino = 0,
            .rec_len = PAGE_SIZE,
            .name_len = 0,
            .name = "0",    // just in case
        }};
        bytes2rec(recs, data);
        inode.size = block_layer->write(inode, 0, data);

    }

    void _init_empty_dir(const uint32_t ino, const uint32_t pino, const FileAttr &meta) const {
        DirRec dir_rec = {
            .ino = pino,     // 4
            .rec_len = 9,    // 2
            .name_len = 2,   // 1
            .name = ".."     // 2
        };
        _create_rec(ino, dir_rec);
        dir_rec = {
            .ino = ino,      // 4
            .rec_len = 8,    // 2
            .name_len = 1,   // 1
            .name = "."      // 1
        };
        _create_rec(ino, dir_rec);
    }

    [[nodiscard]] uint32_t _locate(uint32_t pino, const std::vector<std::string> &filenames) const {
        assert(pino != 0);
        for (const auto &filename : filenames) {
            if (pino == 0) {
                break;
            }
            pino = _scan_dir(pino, filename);
        }
        return pino;
    }

    [[nodiscard]] uint32_t _make(uint32_t pino, const std::string &path, const FileAttr &meta) const {
        assert(pino != 0);
        std::vector<std::string> filenames = split_string(path, '/');
        assert(!filenames.empty());

        const std::string &name = filenames.back();
        filenames.pop_back();

        pino = _locate(pino, filenames);
        if (pino == 0) {
            return 0;
        }

        const uint32_t new_ino = block_layer->create_inode(meta.type, meta.mod, meta.uid, meta.gid);

        const DirRec dir_rec = {
            .ino = new_ino,
            .rec_len = static_cast<uint16_t>(name.size() + 4 + 2 + 1),
            .name_len = static_cast<uint8_t>(name.size()),
            .name = name.c_str(),
        };
        _create_rec(pino, dir_rec);
        return new_ino;
    }




    [[nodiscard]] std::vector<DirRec> _list(const uint32_t ino) const {
        Inode &inode = block_layer->stat(ino);
        const auto data = block_layer->read(inode, 0, inode.size);
        const auto recs = bytes2rec(data);

        std:std::vector<DirRec> result;

        const std::insert_iterator<std::vector<DirRec>> iter(result, result.begin());
        std::ranges::copy_if(recs, iter, [] (const auto &rec) {return rec.ino != 0;});
        return result;
    }

    void _rm_recursive(const uint32_t ino) const {
        for (const auto & [cino, rec_len, name_len, name] : _list(ino)) {
            const auto& cname = std::string(name, name_len);
            if (cname == "." || cname == "..") {
                continue;
            }
            _rm_rec(ino, cname);
        }
    }
    void _rm_rec(const uint32_t pino, const std::string &name) const {
        if (name == "." || name == "..") {
            return;
        }
        Inode &inode = block_layer->stat(pino);
        auto data = block_layer->read(inode, 0, inode.size);
        auto recs = bytes2rec(data);
        const auto it =
            std::ranges::find_if(recs,
                [&](const DirRec &rec) {return std::string(rec.name, rec.name_len) == name;});

        assert(it->ino != root_ino);
        if (it == recs.end()) {
            throw std::runtime_error("No such file or directory: " + name);
        }
        const auto &rec_inode = block_layer->stat(it->ino);
        if (it->ino && rec_inode.type == INODE_DIR) {
            _rm_recursive(it->ino);
        }


        it->ino = 0;
        bytes2rec(recs, data);
        block_layer->write(inode, 0, data);
    }

    [[nodiscard]] bool _check_mod(const uint32_t ino, const uint8_t mode, const uint32_t uid, const uint32_t gid) const {
        const Inode &inode = block_layer->stat(ino);
        const bool read = static_cast<bool>(mode & 0b100);
        const bool write = static_cast<bool>(mode & 0b010);
        const bool exec = static_cast<bool>(mode & 0b001);
        int beg_idx;
        if (inode.uid == uid) {    // 当前用户
            beg_idx = 0;
        } else if (inode.gid == gid) { // 当前用户组
            beg_idx = 3;
        } else {    // 啥都不是
            beg_idx = 6;
        }

        const bool imod_read = inode.get_mod(beg_idx);
        const bool imod_write = inode.get_mod(beg_idx + 1);
        const bool imod_exec = inode.get_mod(beg_idx + 2);

        if (read && !imod_read || write && !imod_write || exec && !imod_exec) {
            return false;
        }
        return true;
    }



public:
    FileSystem(): block_layer(new FileBlockLayer())
    , root_ino(block_layer->create_inode(INODE_DIR, 0b111101101, 0, 0)) {
        // 初始化最初的 / 文件夹
        _assign_empty_dir(root_ino);
        _init_empty_dir(root_ino, root_ino, {
            .mod = 0b111101101,
            .uid = 0,
            .gid = 0,
        });
    };


    [[nodiscard]] uint32_t mkdir(const uint32_t pino, const std::string &path, const FileAttr &meta) const {
        assert(pino != 0);
        FileAttr fa = meta;
        fa.type = INODE_DIR;
        if (!block_layer->exist(pino)) {
            throw std::runtime_error("No such file or directory");
        }
        if (const auto *file_desc = open(pino, path, 0b010, fa); file_desc != nullptr) {
            delete file_desc;
            throw std::runtime_error("Object exists");
        }
        if (block_layer->stat(pino).type != INODE_DIR) {
            throw std::runtime_error("Object not a directory");
        }


        const uint32_t ino = _make(pino, path, fa);
        _assign_empty_dir(ino);
        _init_empty_dir(ino, pino, meta);
        return ino;
    }

    [[nodiscard]] uint32_t touch_file(const uint32_t pino, const std::string &path, const FileAttr &meta) const { // 创建文件
        assert(pino != 0);
        FileAttr fa = meta;
        fa.type = INODE_FILE;
        if (!block_layer->exist(pino)) {
            throw std::runtime_error("No such file or directory");
        }
        if (const auto *file_desc = open(pino, path, 0b010, fa); file_desc != nullptr) {
            delete file_desc;
            throw std::runtime_error("Object exists");
        }
        if (block_layer->stat(pino).type != INODE_DIR) {
            throw std::runtime_error("Object not a directory");
        }
        const uint32_t ino = _make(pino, path, fa);
        return ino;
    }



    [[nodiscard]] FileDesc *open(const uint32_t pino, const std::string &path, const uint8_t mode, const FileAttr &meta) const {
        assert(pino != 0);
        if (!block_layer->exist(pino)) {
            throw std::runtime_error("No such file or directory");
        }
        const std::vector<std::string> filenames = split_string(path, '/');
        const uint32_t ino = _locate(pino, filenames);

        if (ino == 0) {
            return nullptr;
        }

        if (!_check_mod(ino, mode, meta.uid, meta.gid)) {
            throw std::runtime_error("Permission denied");
        }

        return new FileDesc{0, mode, ino};
    }

    static void fclose(const FileDesc *fd) {
        delete fd;
    }

    [[nodiscard]] std::vector<DirRec> list(const uint32_t ino, const FileAttr &meta) const {
        if (!block_layer->exist(ino)) {
            throw std::runtime_error("No such file or directory");
        }
        const Inode &inode = block_layer->stat(ino);
        if (!_check_mod(ino, 0b100, meta.uid, meta.gid)) {
            throw std::runtime_error("Permission denied");
        }
        if (inode.type != INODE_DIR) {
            throw std::runtime_error("not a directory");
        }


        return _list(ino);
    }




    void rm(uint32_t pino, const std::string &path, const FileAttr &meta) const {
        if (!block_layer->exist(pino)) {
            throw std::runtime_error("No such file or directory");
        }
        if (!_check_mod(pino, 0b010, meta.uid, meta.gid)) {
            throw std::runtime_error("Permission denied");
        }


        assert(pino != 0);
        std::vector<std::string> filenames = split_string(path, '/');
        assert(!filenames.empty());
        const std::string &name = filenames.back();
        filenames.pop_back();

        pino = _locate(pino, filenames);
        if (pino == 0) {
            throw std::runtime_error("No such file or directory");
        }

        _rm_rec(pino, name);
    }

    void fwirte(FileDesc *file_desc, const std::vector<std::byte> &bytes) const {
        assert(file_desc != nullptr);
        assert(file_desc->ino != 0);
        assert(block_layer->exist(file_desc->ino));
        Inode &inode = block_layer->stat(file_desc->ino);
        assert(inode.type == INODE_FILE);
        inode.size = block_layer->write(inode, file_desc->fpos, bytes);
        file_desc->fpos += bytes.size();
    }

    std::vector<std::byte> fread(FileDesc *file_desc, const uint32_t bytes) const {
        assert(file_desc != nullptr);
        assert(file_desc->ino != 0);
        assert(block_layer->exist(file_desc->ino));
        const auto &data =
            block_layer->read(block_layer->stat(file_desc->ino), file_desc->fpos, bytes);
        file_desc->fpos += bytes;
        return data;

    }

    void fseek(FileDesc *file_desc, const uint32_t pos) const {
        assert(file_desc != nullptr);
        assert(file_desc->ino != 0);
        assert(block_layer->exist(file_desc->ino));
        file_desc->fpos = pos;
    }

    uint32_t ftell(const FileDesc *file_desc) const {
        assert(file_desc != nullptr);
        assert(file_desc->ino != 0);
        assert(block_layer->exist(file_desc->ino));
        return file_desc->fpos;
    }

    [[nodiscard]] const Inode &stat(const uint32_t pino, const std::string &path, const FileAttr &meta) const {
        const auto *fd = open(pino, path, 0b100, meta);
        if (fd == nullptr) {
            throw std::runtime_error("No such file or directory");
        }
        return block_layer->stat(fd->ino);
    }

    [[nodiscard]] bool is_dir(const uint32_t ino) const {
        return block_layer->stat(ino).type == INODE_DIR;
    }
    [[nodiscard]] const Inode &stat(const uint32_t ino) const {
        return block_layer->stat(ino);
    }

    void trunc(FileDesc *fd, const uint32_t size) const {
        block_layer->trunc(fd->ino, size);
        if (fd->fpos >= size) {
            fd->fpos = size;
        }
    }

    ~FileSystem() {
        delete block_layer;
    }

private:
    FileBlockLayer *block_layer;

public:
    const uint32_t root_ino;
};
















namespace fmode {
    enum FILE_MODE {
        R = 0b100,
        W = 0b010,
        X = 0b001,
        RW = 0b110,
        RWX = 0b111,
    };
}


struct Account {
    uint32_t uid;
    uint32_t gid;
    std::string username;
    std::string password;
    std::string user_dir;
};
std::vector<Account> accounts = {
    {.uid=0, .gid=0, .username="root", .password="password", .user_dir="/root", },
    {.uid=1, .gid=1, .username="tom", .password="123", .user_dir="/tom", },
    {.uid=2, .gid=1, .username="jack", .password="123", .user_dir="/jack", },
    {.uid=3, .gid=2, .username="mask", .password="123", .user_dir="/mask", },
};

uint32_t current_user_idx;



uint32_t working_dir_ino;
std::string working_dir;
const FileSystem fs;

void file_create(const std::string &path, const bool is_dir, const uint16_t mode) {
    assert(!path.empty());
    FileAttr meta = {
        .uid = accounts[current_user_idx].uid,
        .gid = accounts[current_user_idx].gid
    };
    uint32_t pino;
    if (path[0] == '/') {
        pino = fs.root_ino;
    } else {
        pino = working_dir_ino;
    }
    meta.mod = mode;
    if (is_dir) {
        (void)fs.mkdir(pino, path, meta);
    } else {
        (void)fs.touch_file(pino, path, meta);
    }

}

void file_create(const std::string &path, const bool is_dir) {
    if (is_dir) {
        file_create(path, is_dir, 0b111101101);
    } else {
        file_create(path, is_dir, 0b110100100);
    }
}



FileDesc *file_open(const std::string &path, const uint8_t mode, const bool dir = true) {
    assert(!path.empty());
    const FileAttr meta = {
        .uid = accounts[current_user_idx].uid,
        .gid = accounts[current_user_idx].gid
    };
    uint32_t pino;
    if (path[0] == '/') {
        pino = fs.root_ino;
    } else {
        pino = working_dir_ino;
    }
    auto *fd = fs.open(pino, path, mode, meta);
    if (fd == nullptr) {
        throw std::runtime_error("no such file");
    }
    if (dir && !fs.is_dir(fd->ino)) {
        throw std::runtime_error("Object is a file");
    }
    return fd;
}

uint32_t get_ino(const std::string &path) {
    const FileDesc *fd = file_open(path, fmode::R);
    const uint32_t ino = fd->ino;
    FileSystem::fclose(fd);
    return ino;
}

const Inode &stat(const std::string &path) {
    assert(!path.empty());
    const FileAttr meta = {
        .uid = accounts[current_user_idx].uid,
        .gid = accounts[current_user_idx].gid
    };
    uint32_t pino;
    if (path[0] == '/') {
        pino = fs.root_ino;
    } else {
        pino = working_dir_ino;
    }
    return fs.stat(pino, path, meta);
}

void ls(const std::string &path) {
    assert(!path.empty());
    const FileAttr meta = {
        .uid = accounts[current_user_idx].uid,
        .gid = accounts[current_user_idx].gid
    };
    const FileDesc *fd= file_open(path, fmode::R);

    for (const auto recs = fs.list(fd->ino, meta); const auto &rec : recs | std::views::reverse) {
        std::cout << std::setw(20) << std::left << std::string(rec.name, rec.name_len);
    }
    std::cout << std::endl;
    FileSystem::fclose(fd);
}

void ll(const std::string &path) {
    assert(!path.empty());
    assert(!path.empty());
    const FileAttr meta = {
        .uid = accounts[current_user_idx].uid,
        .gid = accounts[current_user_idx].gid
    };
    const FileDesc *fd= file_open(path, fmode::R);

    for (const auto recs = fs.list(fd->ino, meta); const auto &rec : recs | std::views::reverse) {
        const Inode &inode = fs.stat(rec.ino);
        const auto &it =
            std::ranges::find_if(accounts, [&inode](const Account& account) {return account.uid == inode.uid;});
        std::cout << inode << std::setw(20) << "\t" << it->username << "\t" << std::string(rec.name, rec.name_len) << std::endl;
    }
    FileSystem::fclose(fd);
}

void rm(const std::string &path) {
    if (path == working_dir) {
        throw std::runtime_error("rm: refusing to remove '.' or '..' directory");
    }

    if (path == "." || path == "..") {
        throw std::runtime_error("rm: refusing to remove '.' or '..' directory");
    }
}

std::vector<std::byte> readb(const std::string &path, const uint32_t off, uint32_t size = 0) {
    FileDesc *fd = file_open(path, fmode::R, false);
    const auto &inode = fs.stat(fd->ino);
    if (inode.type == INODE_DIR) {
        throw std::runtime_error("cat: Object is a directory");
    }
    fs.fseek(fd, off);
    if (size == 0) {
        size = inode.size;
    }
    const auto result = fs.fread(fd, size);
    FileSystem::fclose(fd);
    return result;
}


void cat(const std::string &path) {
    for (const auto result = readb(path, 0); auto byte : result) {
        std::cout << static_cast<char>(byte);
    }
    std::cout << std::endl;
}

void writeb(const std::string &path, const std::vector<std::byte> &bytes, const uint32_t off) {
    FileDesc *fd = file_open(path, fmode::R, false);
    const auto &inode = fs.stat(fd->ino);
    if (inode.type == INODE_DIR) {
        throw std::runtime_error("write: Object is a directory");
    }
    fs.fseek(fd, off);
    fs.fwirte(fd, bytes);
    FileSystem::fclose(fd);
}
void write(const std::string &path, const std::string &text, const bool append) {
    std::vector<std::byte> data;
    const auto &node = stat(path);
    for (auto chr : text) {
        data.push_back(static_cast<std::byte>(chr));
    }
    uint32_t off;
    if (append && node.size) {
        off = node.size;
    } else {
        off = 0;
    }
    writeb(path, data, off);
}



void truncate(const std::string &path) {
    auto *fd = file_open(path, fmode::R, false);
    const auto &inode = fs.stat(fd->ino);
    if (inode.type == INODE_DIR) {
        throw std::runtime_error("write: Object is a directory");
    }
    fs.trunc(fd, 0);
    FileSystem::fclose(fd);
}

void cd(const std::string &path) {
    assert(!path.empty());
    const auto *fd = file_open(path, fmode::X);
    if (const auto &inode =fs.stat(fd->ino); inode.type == INODE_FILE) {
        throw std::runtime_error("cd: Object is a file");
    }

    working_dir = calculateFinalPath(working_dir, path);
    if (path[0] == '/') {
        working_dir = path;
    }
    working_dir_ino = fd->ino;

}

void init_user_disk() {
    for (const auto & account : accounts) {
        (void)fs.mkdir(fs.root_ino, account.user_dir, {
            .type = INODE_DIR,
            .mod = 0b111101000,
            .uid = account.uid,
            .gid = account.gid
        });
    }
}

void expr2() {
    std::ios::sync_with_stdio(true);
    init_user_disk();
    std::string buff;
    bool is_login = false;
    while (!is_login) {
        std::cout << "login: ";
        getline(std::cin, buff);
        auto user_it =
            std::ranges::find_if(accounts, [&](const Account &acc) {return acc.username == buff;});
        std::cout << "password: ";

        getline(std::cin, buff);
        if (user_it == accounts.end() || user_it->password != buff) {
            std::cout << "Authentication failed" << std::endl;
        } else {
            is_login = true;
            current_user_idx = user_it - accounts.begin();
            working_dir = user_it->user_dir;
            working_dir_ino = get_ino(user_it->user_dir);
        }
    }

    constexpr bool stop = false;
    while (!stop) {
        std::cout << accounts[current_user_idx].username << "@PC:" << working_dir << "$  ";
        std::getline(std::cin, buff);
        const auto &commands = split_string(buff, ' ');
        if (commands.empty()) {
            continue;
        }

        try {
            if (commands[0] == "ls") {
                if (commands.size() > 2) {
                    throw std::runtime_error("Invalid command");
                }
                if (commands.size() == 2) {
                    ls(commands[1]);
                } else {
                    ls(working_dir);
                }

            } else if (commands[0] == "ll") {
                if (commands.size() > 2) {
                    throw std::runtime_error("Invalid command");
                }
                if (commands.size() == 2) {
                    ll(commands[1]);
                } else {
                    ll(working_dir);
                }
            } else if (commands[0] == "pwd") {
                std::cout << working_dir << std::endl;
            } else if (commands[0] == "mkdir") {
                if (commands.size() != 2) {
                    throw std::runtime_error("Invalid command");
                }
                file_create(commands[1], true);

            } else if (commands[0] == "touch") {
                if (commands.size() != 2) {
                    throw std::runtime_error("Invalid command");
                }
                file_create(commands[1], false);
            }else if (commands[1] == "rm") {
                if (commands.size() != 2) {
                    throw std::runtime_error("Invalid command");
                }
            } else if (commands[0] == "cat") {
                if (commands.size() != 2) {
                    throw std::runtime_error("Invalid command");
                }
                cat(commands[1]);
            } else if (commands[0] == "write") {
                if (commands.size() < 2 || commands.size() > 3) {
                    throw std::runtime_error("Invalid command");
                }
                if (commands.size() == 2) {
                    truncate(commands[1]);
                }
                if (commands.size() == 3) {
                    write(commands[1], commands[2], true);
                }

            } else if (commands[0] == "cd") {
                if (commands.size() != 2) {
                    throw std::runtime_error("Invalid command");
                }
                cd(commands[1]);
            } else {
                throw std::runtime_error("Invalid command");
            }
        } catch (const std::runtime_error &e) {
            std::cerr << RED << e.what() << RESET << std::endl;
        }

    }
}


static std::list<uint32_t> page_queue;
PAGE_SWAP_ALGO algo = LRU;

void lru_access(const uint32_t vpn) {
    if (algo != LRU) {
        return;
    }
    const auto it = std::find(page_queue.cbegin(), page_queue.cend(), vpn);
    if (it != page_queue.end()) {
        page_queue.erase(it);
        page_queue.push_back(vpn);
    }
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


    [[nodiscard]] const char* what() const noexcept override {
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
        bool accessed{};
        bool present{};
        bool us{}; // false->user true->supervisor
        bool wr{}; // false->ready only true->wr
        bool nx{}; // false->unexecutable true->executable
    };

    struct FileMapping {
        std::string path;
        uint32_t offset{};
        bool swap_region{};
    };


    explicit PageTable(const uint32_t memory_size, const uint32_t pmem_size): pt_(std::vector<PageTableEntry>(memory_size)) {
        for (uint32_t i = 0; i < pmem_size / PAGE_SIZE; i++) {
            free_list.push_back(i);
        }
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
        const auto page_number = get_page_number(vaddr);
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

    [[nodiscard]] uint32_t get_ppn(const uint32_t vaddr) const {
        const auto page_number = get_page_number(vaddr);
        return pt_[page_number].ppn;
    }

    [[nodiscard]] uint32_t translate(const uint32_t vaddr) const {
        const uint32_t vpn = get_page_number(vaddr);
        const uint32_t offset = get_off(vaddr);
        const uint32_t ppn = pt_[vpn].ppn;
        return ppn << PAGE_BIT_SIZE | offset;
    }

    [[nodiscard]] bool is_accessed(const uint32_t vaddr) const {
        const auto page_number = get_page_number(vaddr);
        return pt_[page_number].accessed;
    }

    [[nodiscard]] bool is_dirty(const uint32_t vaddr) const {
        const auto page_number = get_page_number(vaddr);
        return pt_[page_number].dirty;
    }

    [[nodiscard]] bool is_present(const uint32_t vaddr) const {
        const auto page_number = get_page_number(vaddr);
        return pt_[page_number].present;
    }

    [[nodiscard]] bool is_supervisor(const uint32_t vaddr) const {
        const auto page_number = get_page_number(vaddr);
        return pt_[page_number].us;
    }

    [[nodiscard]] bool is_write(const uint32_t vaddr) const {
        const auto page_number = get_page_number(vaddr);
        return pt_[page_number].wr;
    }

    [[nodiscard]] bool is_exec(const uint32_t vaddr) const {
        const auto page_number = get_page_number(vaddr);
        return pt_[page_number].nx;
    }

    void set_accessed(const uint32_t vaddr, const bool accessed) {
        const auto page_number = get_page_number(vaddr);
        pt_[page_number].accessed = accessed;
    }

    void set_dirty(const uint32_t vaddr, const bool dirty) {
        const auto page_number = get_page_number(vaddr);
        pt_[page_number].dirty = dirty;
    }

    void set_present(const uint32_t vaddr, const bool present) {
        const auto page_number = get_page_number(vaddr);
        pt_[page_number].present = present;
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
    std::vector<PageTableEntry> pt_;
public:
    std::map<uint32_t, FileMapping> file_mapping;
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
        lru_access(PageTable::get_page_number(vaddr));
        pt_.set_dirty(vaddr, true);
        pt_.set_accessed(vaddr, true);
        const uint32_t paddr = pt_.translate(vaddr);
        write_raw(memory_, paddr, mdr);
    }

    [[nodiscard]] uint32_t read(const uint32_t vaddr) const {
        if (!pt_.is_present(vaddr)) {
            throw Fault(vaddr, FaultType::PF);
        }
        lru_access(PageTable::get_page_number(vaddr));
        pt_.set_accessed(vaddr, true);
        const uint32_t paddr = pt_.translate(vaddr);
        return read_raw(memory_, paddr);
    }

    [[nodiscard]] uint32_t read_instruction(const uint32_t vaddr) const {
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
PageTable init_pt(const uint32_t vmem_size, const uint32_t pmem_size) {
    PageTable pt(vmem_size, pmem_size);
    return pt;
}


void init_code(const std::string &path, const int pages_cnt) {
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
        // make_instruction(HLT, {NUL, NUL, NUL, NUL}, 0),
    };
    codes.resize(pages_cnt * PAGE_SIZE / 4);
    std::vector<std::byte> bytes(PAGE_SIZE * pages_cnt);
    uint32_t paddr = 0;
    for (const uint32_t code : codes) {
        if (paddr >= pages_cnt * PAGE_SIZE) {
            break;
        }
        // std::cout << std::hex << code << std::endl;
        // write_raw(memory, paddr, code);
        bytes[paddr] = (static_cast<std::byte>((code & 0xFF000000) >> 24));
        bytes[paddr + 1] = (static_cast<std::byte>((code & 0x00FF0000) >> 16));
        bytes[paddr + 2] = (static_cast<std::byte>((code & 0x0000FF00) >> 8));
        bytes[paddr + 3] = (static_cast<std::byte>(code));
        paddr += 4;
    }

    file_create(path, false, 0b111111111);
    writeb(path, bytes, 0);

    for (const uint32_t code1 : codes) {
        std::cout << std::hex << code1 << std::endl;
    }
    int i = 0;
    for (auto byte : readb(path, 4096, PAGE_SIZE)) {
        if (i++ % 4 == 0) {
            std::cout << std::endl;
        }
        if (i > codes.size() * 4) {
            break;
        }
        std::cout << std::left << std::setw(2) << std::hex << static_cast<uint32_t>(byte) << "";
    };
    std::cout << std::dec << std::endl;
}

void init_code2(const std::string &path) {
    constexpr int pages_cnt = 5;
    std::vector<uint32_t> codes = {
        make_instruction(MOV_IL, {NUL, EAX, NUL, NUL}, PAGE_SIZE * 0),
        make_instruction(MOV_M, {NUL, NUL, EAX, EBX}, 0),
        make_instruction(MOV_IL, {NUL, EAX, NUL, NUL}, PAGE_SIZE * 1),
        make_instruction(MOV_M, {NUL, NUL, EAX, EBX}, 0),
        make_instruction(MOV_IL, {NUL, EAX, NUL, NUL}, PAGE_SIZE * 2),
        make_instruction(MOV_M, {NUL, NUL, EAX, EBX}, 0),
        make_instruction(MOV_IL, {NUL, EAX, NUL, NUL}, PAGE_SIZE * 3),
        make_instruction(MOV_M, {NUL, NUL, EAX, EBX}, 0),
        make_instruction(MOV_IL, {NUL, EAX, NUL, NUL}, PAGE_SIZE * 0),
        make_instruction(MOV_M, {NUL, NUL, EAX, EBX}, 0),
        make_instruction(MOV_IL, {NUL, EAX, NUL, NUL}, PAGE_SIZE * 1),
        make_instruction(MOV_M, {NUL, NUL, EAX, EBX}, 0),
        make_instruction(MOV_IL, {NUL, EAX, NUL, NUL}, PAGE_SIZE * 4),
        make_instruction(MOV_M, {NUL, NUL, EAX, EBX}, 0),
        make_instruction(MOV_IL, {NUL, EAX, NUL, NUL}, PAGE_SIZE * 0),
        make_instruction(MOV_M, {NUL, NUL, EAX, EBX}, 0),
        make_instruction(MOV_IL, {NUL, EAX, NUL, NUL}, PAGE_SIZE * 1),
        make_instruction(MOV_M, {NUL, NUL, EAX, EBX}, 0),
        make_instruction(MOV_IL, {NUL, EAX, NUL, NUL}, PAGE_SIZE * 2),
        make_instruction(MOV_M, {NUL, NUL, EAX, EBX}, 0),
        make_instruction(MOV_IL, {NUL, EAX, NUL, NUL}, PAGE_SIZE * 3),
        make_instruction(MOV_M, {NUL, NUL, EAX, EBX}, 0),
        make_instruction(MOV_IL, {NUL, EAX, NUL, NUL}, PAGE_SIZE * 4),
        make_instruction(MOV_M, {NUL, NUL, EAX, EBX}, 0),
        make_instruction(HLT, {NUL, NUL, NUL, NUL}, 0),
    };
    codes.resize(pages_cnt * PAGE_SIZE / 4);
    std::vector<std::byte> bytes(PAGE_SIZE * pages_cnt);
    uint32_t paddr = 0;
    for (const uint32_t code : codes) {
        if (paddr >= pages_cnt * PAGE_SIZE) {
            break;
        }
        // std::cout << std::hex << code << std::endl;
        // write_raw(memory, paddr, code);
        bytes[paddr] = (static_cast<std::byte>((code & 0xFF000000) >> 24));
        bytes[paddr + 1] = (static_cast<std::byte>((code & 0x00FF0000) >> 16));
        bytes[paddr + 2] = (static_cast<std::byte>((code & 0x0000FF00) >> 8));
        bytes[paddr + 3] = (static_cast<std::byte>(code));
        paddr += 4;
    }

    file_create(path, false, 0b111111111);
    writeb(path, bytes, 0);
}

std::vector<std::byte> init_memory(const uint32_t pmem_size) {
    std::vector<std::byte> memory(pmem_size);


    //
    // paddr = 0;
    // for (const uint32_t code : codes) {
    //     std::cout << std::hex << read_raw(memory, paddr) << std::endl;
    //     paddr += 4;
    // }

    return memory;
}

void load_code(const std::string &path, PageTable &pt) {
    const auto &inode = stat(path);
    const uint32_t pages_cnt = inode.size / PAGE_SIZE;

    for (uint32_t i = 0; i < pages_cnt; i++) {
        pt.set_mapping(i * PAGE_SIZE, 0, true, true, true);
        pt.set_present(i * PAGE_SIZE, false);
        pt.file_mapping[i] = {
            .path = calculateFinalPath(working_dir, path),
            .offset = i * PAGE_SIZE,
            .swap_region = false
        };
    }
}


static void write_back(PageTable &pt, const std::vector<std::byte> &memory, const uint32_t vpn) {
    PageTable::FileMapping mp;
    if (pt.file_mapping.contains(vpn)) {
        mp = pt.file_mapping.at(vpn);
        if (mp.swap_region) {
            goto SWAP_BACK;
        }
    }
    mp = pt.file_mapping[vpn] = {
        .path = "/" + std::to_string(vpn) + ".page",
        .offset = 0,
        .swap_region = true
    };
    file_create(mp.path, false, 0b111111111);

SWAP_BACK:

    pt.set_present(vpn, false);
    pt.set_dirty(vpn, false);

    std::vector<std::byte> page_cpy(PAGE_SIZE);
    const uint32_t ppn = pt.translate(vpn * PAGE_SIZE);
    const uint32_t paddr = ppn;
    for (uint32_t i = 0; i < PAGE_SIZE; i += 4) {
        const uint32_t data = read_raw(memory, paddr);
        page_cpy[i] = static_cast<std::byte>((data & 0xFF000000) >> 24);
        page_cpy[i + 1] = static_cast<std::byte>((data & 0x00FF0000) >> 16);
        page_cpy[i + 2] = static_cast<std::byte>((data & 0x0000FF00) >> 8);
        page_cpy[i + 3] = static_cast<std::byte>((data & 0x000000FF));
    }


    assert(page_cpy.size() == PAGE_SIZE);
    writeb(mp.path, page_cpy, mp.offset);
}

static void load_page(const PageTable &pt, std::vector<std::byte> &memory, const uint32_t vpn) {
    assert(!pt.is_present(vpn * PAGE_SIZE));
    if (!pt.file_mapping.contains(vpn)) {
        throw std::runtime_error("No Page File Mapping");
    }
    const uint32_t paddr = pt.translate(vpn * PAGE_SIZE);
    const auto &fmp = pt.file_mapping.at(vpn);
    const auto &bytes = readb(fmp.path, fmp.offset, PAGE_SIZE);
    assert(bytes.size() == PAGE_SIZE);
    for (uint32_t i = 0; i < PAGE_SIZE; i += 4) {
        write_raw(memory, paddr + i,
            (static_cast<uint32_t>(bytes[i]) << 24)
            | (static_cast<uint32_t>(bytes[i + 1]) << 16)
            | (static_cast<uint32_t>(bytes[i + 2]) << 8)
            | static_cast<uint32_t>(bytes[i + 3]));
    }
}


static bool needs_reclaim(const uint32_t mem_size, const uint32_t curr_size) {
    assert(mem_size >= curr_size);
    return curr_size >= waterline;
}



void swap_fifo(PageTable &pt, std::vector<std::byte> &memory, const Fault &fault) {

    if (!needs_reclaim(memory.size(), page_queue.size())) {
        const auto ppn = pt.alloc_physical_page();
        pt.set_ppn(fault.vaddr, ppn);
        load_page(pt, memory, PageTable::get_page_number(fault.vaddr));
        pt.set_present(fault.vaddr, true);
        page_queue.push_back(PageTable::get_page_number(fault.vaddr));
        return;
    }
    const auto swap_vpn = page_queue.front();
    page_queue.pop_front();
    const auto swap_vaddr = swap_vpn * PAGE_SIZE;
    write_back(pt, memory, swap_vpn);

    pt.set_ppn(fault.vaddr, pt.get_ppn(swap_vpn));
    load_page(pt, memory, fault.vaddr / PAGE_SIZE);
    pt.set_present(swap_vaddr, false);

}
void swap_lru(PageTable &pt, std::vector<std::byte> &memory, const Fault &fault) {
    swap_fifo(pt, memory, fault);
}

// 普通改进版CLOCK算法
void swap_clock(PageTable &pt, std::vector<std::byte> &memory, const Fault &fault) {
    static std::list<uint32_t> p_list;

    if (!needs_reclaim(memory.size(), p_list.size())) {
        const auto ppn = pt.alloc_physical_page();
        pt.set_ppn(fault.vaddr, ppn);
        load_page(pt, memory, PageTable::get_page_number(fault.vaddr));
        pt.set_present(fault.vaddr, true);
        p_list.push_back(PageTable::get_page_number(fault.vaddr));
        return;
    }
    auto it = p_list.begin();
    typeof(it) write_back_page;
    int cycle = 0;
    while (true) {
        const uint32_t vaddr = *it * PAGE_SIZE;
        if (!pt.is_dirty(vaddr) && !pt.is_accessed(vaddr)) {
            break;
        }
        if (pt.is_dirty(vaddr) && !pt.is_accessed(vaddr)) {
            write_back_page = it;
        }
        if (pt.is_accessed(vaddr)) {
            pt.set_accessed(vaddr, false);
        }

        if (it == p_list.end()) {
            it = p_list.begin();
            cycle++;
        }

        if (cycle >= 2) {
            break;
        }
        ++it;
    }

    if (cycle >= 2) {
        pt.set_ppn(fault.vaddr, pt.get_ppn(*write_back_page));
        write_back(pt, memory, *write_back_page);
        load_page(pt, memory, fault.vaddr / PAGE_SIZE);
        p_list.erase(write_back_page);
    } else {
        pt.set_ppn(fault.vaddr, pt.get_ppn(*it));
        load_page(pt, memory, fault.vaddr / PAGE_SIZE);
        pt.set_present(*it * PAGE_SIZE, false);
        p_list.erase(it);
    }
    pt.set_present(fault.vaddr, true);
}


// Linux采用的双层链表改进的CLOCK算法


void page_fault_handler(PageTable &pt, std::vector<std::byte> &memory, const Fault &fault) {
    switch (page_swap_algo) {
        case LRU:
            swap_lru(pt, memory, fault);
            break;
        case FIFO:
            swap_fifo(pt, memory, fault);
            break;
        case CLOCK:
            swap_clock(pt, memory, fault);
            break;
        default:
            throw std::invalid_argument("invalid page swap algo");
    }
}


void expr1() {
    page_swap_algo = LRU;
    current_user_idx = 0;
    working_dir = "/";
    working_dir_ino = fs.root_ino;
    constexpr uint32_t vmem_size = 16 * 1024 * 1024;
    constexpr uint32_t pmem_size = 1 * 1024 * 1024;
    constexpr uint32_t pages = vmem_size / PAGE_SIZE;

    waterline = 3;  // 2个页
    std::cout << "dist size: " << DISK_SIZE << std::endl;
    std::cout << "page size: " << PAGE_SIZE << std::endl;

    std::cout << "pages: " << pages << std::endl;
    std::cout << "pmem_size: " << (pmem_size / 1024 / 1024) << "MB" << std::endl;

    PageTable pt = init_pt(vmem_size, pmem_size);
    pt.set_present(0, false);
    std::vector<std::byte> memory = init_memory(pmem_size);
    CPU cpu(pt, memory, 0);
    std::cout << std::dec;

    init_code("/code1", 3);
    init_code2("/code2");
    load_code("/code2", pt);
    while (!cpu.shutdown) {
        try {
            cpu.step();
            std::cout << cpu << std::endl;
        } catch (const Fault& fault) {
            if (fault.type == PF) {
                std::cout << fault.vaddr << std::endl;
                page_fault_handler(pt, memory, fault);
            } else {
                printf(fault.what());
                return;
            }
        }
    }
}

int main() {



    expr1();
    // expr2();
    return 0;
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
