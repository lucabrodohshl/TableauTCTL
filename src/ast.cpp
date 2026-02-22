// ============================================================================
// ast.cpp — Implementation of tctl AST, interning, and pretty-printing
// ============================================================================

#include "tctl/ast.hpp"

#include <algorithm>
#include <cassert>
#include <sstream>
#include <stdexcept>

namespace tctl {

// ── node_kind_name ──────────────────────────────────────────────────────────

const char* node_kind_name(NodeKind k) noexcept {
    switch (k) {
        case NodeKind::True:    return "true";
        case NodeKind::False:   return "false";
        case NodeKind::Atom:    return "Atom";
        case NodeKind::Not:     return "!";
        case NodeKind::And:     return "&";
        case NodeKind::Or:      return "|";
        case NodeKind::Implies: return "->";
        case NodeKind::Iff:     return "<->";
        case NodeKind::EX:      return "EX";
        case NodeKind::AX:      return "AX";
        case NodeKind::EU:      return "EU";
        case NodeKind::AU:      return "AU";
        case NodeKind::ER:      return "ER";
        case NodeKind::AR:      return "AR";
        case NodeKind::EF:      return "EF";
        case NodeKind::AF:      return "AF";
        case NodeKind::EG:      return "EG";
        case NodeKind::AG:      return "AG";
        // TCTL timed operators
        case NodeKind::TimedEU: return "EU[]";
        case NodeKind::TimedAU: return "AU[]";
        case NodeKind::TimedER: return "ER[]";
        case NodeKind::TimedAR: return "AR[]";
        case NodeKind::TimedEF: return "EF[]";
        case NodeKind::TimedAF: return "AF[]";
        case NodeKind::TimedEG: return "EG[]";
        case NodeKind::TimedAG: return "AG[]";
        case NodeKind::IntVar:      return "IntVar";
        case NodeKind::IntConst:    return "IntConst";
        case NodeKind::IntPlus:     return "+";
        case NodeKind::IntMinus:    return "-";
        case NodeKind::IntTimes:    return "*";
        case NodeKind::IntLessEq:   return "<=";
        case NodeKind::IntLess:     return "<";
        case NodeKind::IntGreaterEq: return ">=";
        case NodeKind::IntGreater:  return ">";
        case NodeKind::IntEqual:    return "=";
    }
    return "?";
}

// ── FormulaNode equality ────────────────────────────────────────────────────

bool FormulaNode::operator==(const FormulaNode& o) const noexcept {
    return kind == o.kind &&
           atom_name == o.atom_name &&
           int_value == o.int_value &&
           children[0] == o.children[0] &&
           children[1] == o.children[1] &&
           time_lower == o.time_lower &&
           time_upper == o.time_upper;
}

// ── FormulaNodeHash ─────────────────────────────────────────────────────────
// Combine kind, atom_name, int_value, and children via FNV-like mixing.

std::size_t FormulaNodeHash::operator()(const FormulaNode& n) const noexcept {
    std::size_t h = static_cast<std::size_t>(n.kind);
    h ^= std::hash<std::string>{}(n.atom_name) + 0x9e3779b9 + (h << 6) + (h >> 2);
    h ^= std::hash<std::int64_t>{}(n.int_value) + 0x9e3779b9 + (h << 6) + (h >> 2);
    h ^= std::hash<FormulaId>{}(n.children[0]) + 0x9e3779b9 + (h << 6) + (h >> 2);
    h ^= std::hash<FormulaId>{}(n.children[1]) + 0x9e3779b9 + (h << 6) + (h >> 2);
    // Include time interval in hash for TCTL nodes (with strictness)
    h ^= std::hash<std::int64_t>{}(n.time_lower.value) + 0x9e3779b9 + (h << 6) + (h >> 2);
    h ^= std::hash<bool>{}(n.time_lower.is_strict) + 0x9e3779b9 + (h << 6) + (h >> 2);
    h ^= std::hash<bool>{}(n.time_upper.is_infinity) + 0x9e3779b9 + (h << 6) + (h >> 2);
    h ^= std::hash<std::int64_t>{}(n.time_upper.value) + 0x9e3779b9 + (h << 6) + (h >> 2);
    h ^= std::hash<bool>{}(n.time_upper.is_strict) + 0x9e3779b9 + (h << 6) + (h >> 2);
    return h;
}

// ── FormulaFactory ──────────────────────────────────────────────────────────

FormulaFactory::FormulaFactory() {
    // Reserve slot 0 and 1 for canonical true/false so they always exist.
    // This also warms the intern table.
    make_true();
    make_false();
}

FormulaId FormulaFactory::intern(FormulaNode node) {
    // Check if a structurally identical node already exists.
    auto it = intern_.find(node);
    if (it != intern_.end()) {
        return it->second;
    }
    // Allocate a new id (index into nodes_).
    FormulaId id = static_cast<FormulaId>(nodes_.size());
    nodes_.push_back(std::move(node));
    intern_[nodes_.back()] = id;
    return id;
}

// ── make_* helpers ──────────────────────────────────────────────────────────

FormulaId FormulaFactory::make_true() {
    FormulaNode n;
    n.kind = NodeKind::True;
    return intern(std::move(n));
}

FormulaId FormulaFactory::make_false() {
    FormulaNode n;
    n.kind = NodeKind::False;
    return intern(std::move(n));
}

FormulaId FormulaFactory::make_atom(const std::string& name) {
    FormulaNode n;
    n.kind = NodeKind::Atom;
    n.atom_name = name;
    return intern(std::move(n));
}

FormulaId FormulaFactory::make_not(FormulaId child) {
    FormulaNode n;
    n.kind = NodeKind::Not;
    n.children[0] = child;
    return intern(std::move(n));
}

FormulaId FormulaFactory::make_and(FormulaId lhs, FormulaId rhs) {
    FormulaNode n;
    n.kind = NodeKind::And;
    n.children[0] = lhs;
    n.children[1] = rhs;
    return intern(std::move(n));
}

FormulaId FormulaFactory::make_or(FormulaId lhs, FormulaId rhs) {
    FormulaNode n;
    n.kind = NodeKind::Or;
    n.children[0] = lhs;
    n.children[1] = rhs;
    return intern(std::move(n));
}

FormulaId FormulaFactory::make_implies(FormulaId lhs, FormulaId rhs) {
    FormulaNode n;
    n.kind = NodeKind::Implies;
    n.children[0] = lhs;
    n.children[1] = rhs;
    return intern(std::move(n));
}

FormulaId FormulaFactory::make_iff(FormulaId lhs, FormulaId rhs) {
    FormulaNode n;
    n.kind = NodeKind::Iff;
    n.children[0] = lhs;
    n.children[1] = rhs;
    return intern(std::move(n));
}

FormulaId FormulaFactory::make_ex(FormulaId child) {
    FormulaNode n;
    n.kind = NodeKind::EX;
    n.children[0] = child;
    return intern(std::move(n));
}

FormulaId FormulaFactory::make_ax(FormulaId child) {
    FormulaNode n;
    n.kind = NodeKind::AX;
    n.children[0] = child;
    return intern(std::move(n));
}

FormulaId FormulaFactory::make_eu(FormulaId lhs, FormulaId rhs) {
    FormulaNode n;
    n.kind = NodeKind::EU;
    n.children[0] = lhs;
    n.children[1] = rhs;
    return intern(std::move(n));
}

FormulaId FormulaFactory::make_au(FormulaId lhs, FormulaId rhs) {
    FormulaNode n;
    n.kind = NodeKind::AU;
    n.children[0] = lhs;
    n.children[1] = rhs;
    return intern(std::move(n));
}

FormulaId FormulaFactory::make_er(FormulaId lhs, FormulaId rhs) {
    FormulaNode n;
    n.kind = NodeKind::ER;
    n.children[0] = lhs;
    n.children[1] = rhs;
    return intern(std::move(n));
}

FormulaId FormulaFactory::make_ar(FormulaId lhs, FormulaId rhs) {
    FormulaNode n;
    n.kind = NodeKind::AR;
    n.children[0] = lhs;
    n.children[1] = rhs;
    return intern(std::move(n));
}

FormulaId FormulaFactory::make_ef(FormulaId child) {
    FormulaNode n;
    n.kind = NodeKind::EF;
    n.children[0] = child;
    return intern(std::move(n));
}

FormulaId FormulaFactory::make_af(FormulaId child) {
    FormulaNode n;
    n.kind = NodeKind::AF;
    n.children[0] = child;
    return intern(std::move(n));
}

FormulaId FormulaFactory::make_eg(FormulaId child) {
    FormulaNode n;
    n.kind = NodeKind::EG;
    n.children[0] = child;
    return intern(std::move(n));
}

FormulaId FormulaFactory::make_ag(FormulaId child) {
    FormulaNode n;
    n.kind = NodeKind::AG;
    n.children[0] = child;
    return intern(std::move(n));
}

// ── TCTL: Timed temporal operators ──────────────────────────────────────────

FormulaId FormulaFactory::make_timed_eu(FormulaId lhs, FormulaId rhs,
                                         TimeBound lower, TimeBound upper) {
    FormulaNode n;
    n.kind = NodeKind::TimedEU;
    n.children[0] = lhs;
    n.children[1] = rhs;
    n.time_lower = lower;
    n.time_upper = upper;
    return intern(std::move(n));
}

FormulaId FormulaFactory::make_timed_au(FormulaId lhs, FormulaId rhs,
                                         TimeBound lower, TimeBound upper) {
    FormulaNode n;
    n.kind = NodeKind::TimedAU;
    n.children[0] = lhs;
    n.children[1] = rhs;
    n.time_lower = lower;
    n.time_upper = upper;
    return intern(std::move(n));
}

FormulaId FormulaFactory::make_timed_er(FormulaId lhs, FormulaId rhs,
                                         TimeBound lower, TimeBound upper) {
    FormulaNode n;
    n.kind = NodeKind::TimedER;
    n.children[0] = lhs;
    n.children[1] = rhs;
    n.time_lower = lower;
    n.time_upper = upper;
    return intern(std::move(n));
}

FormulaId FormulaFactory::make_timed_ar(FormulaId lhs, FormulaId rhs,
                                         TimeBound lower, TimeBound upper) {
    FormulaNode n;
    n.kind = NodeKind::TimedAR;
    n.children[0] = lhs;
    n.children[1] = rhs;
    n.time_lower = lower;
    n.time_upper = upper;
    return intern(std::move(n));
}

FormulaId FormulaFactory::make_timed_ef(FormulaId child, 
                                         TimeBound lower, TimeBound upper) {
    FormulaNode n;
    n.kind = NodeKind::TimedEF;
    n.children[0] = child;
    n.time_lower = lower;
    n.time_upper = upper;
    return intern(std::move(n));
}

FormulaId FormulaFactory::make_timed_af(FormulaId child,
                                         TimeBound lower, TimeBound upper) {
    FormulaNode n;
    n.kind = NodeKind::TimedAF;
    n.children[0] = child;
    n.time_lower = lower;
    n.time_upper = upper;
    return intern(std::move(n));
}

FormulaId FormulaFactory::make_timed_eg(FormulaId child,
                                         TimeBound lower, TimeBound upper) {
    FormulaNode n;
    n.kind = NodeKind::TimedEG;
    n.children[0] = child;
    n.time_lower = lower;
    n.time_upper = upper;
    return intern(std::move(n));
}

FormulaId FormulaFactory::make_timed_ag(FormulaId child,
                                         TimeBound lower, TimeBound upper) {
    FormulaNode n;
    n.kind = NodeKind::TimedAG;
    n.children[0] = child;
    n.time_lower = lower;
    n.time_upper = upper;
    return intern(std::move(n));
}

// ── Integer expressions ─────────────────────────────────────────────────────

FormulaId FormulaFactory::make_int_var(const std::string& name) {
    FormulaNode n;
    n.kind = NodeKind::IntVar;
    n.atom_name = name;
    return intern(std::move(n));
}

FormulaId FormulaFactory::make_int_const(std::int64_t value) {
    FormulaNode n;
    n.kind = NodeKind::IntConst;
    n.int_value = value;
    return intern(std::move(n));
}

FormulaId FormulaFactory::make_int_plus(FormulaId lhs, FormulaId rhs) {
    FormulaNode n;
    n.kind = NodeKind::IntPlus;
    n.children[0] = lhs;
    n.children[1] = rhs;
    return intern(std::move(n));
}

FormulaId FormulaFactory::make_int_minus(FormulaId lhs, FormulaId rhs) {
    FormulaNode n;
    n.kind = NodeKind::IntMinus;
    n.children[0] = lhs;
    n.children[1] = rhs;
    return intern(std::move(n));
}

FormulaId FormulaFactory::make_int_times(FormulaId lhs, FormulaId rhs) {
    FormulaNode n;
    n.kind = NodeKind::IntTimes;
    n.children[0] = lhs;
    n.children[1] = rhs;
    return intern(std::move(n));
}

// ── Arithmetic constraints ──────────────────────────────────────────────────

FormulaId FormulaFactory::make_int_less_eq(FormulaId lhs, FormulaId rhs) {
    FormulaNode n;
    n.kind = NodeKind::IntLessEq;
    n.children[0] = lhs;
    n.children[1] = rhs;
    return intern(std::move(n));
}

FormulaId FormulaFactory::make_int_less(FormulaId lhs, FormulaId rhs) {
    FormulaNode n;
    n.kind = NodeKind::IntLess;
    n.children[0] = lhs;
    n.children[1] = rhs;
    return intern(std::move(n));
}

FormulaId FormulaFactory::make_int_greater_eq(FormulaId lhs, FormulaId rhs) {
    FormulaNode n;
    n.kind = NodeKind::IntGreaterEq;
    n.children[0] = lhs;
    n.children[1] = rhs;
    return intern(std::move(n));
}

FormulaId FormulaFactory::make_int_greater(FormulaId lhs, FormulaId rhs) {
    FormulaNode n;
    n.kind = NodeKind::IntGreater;
    n.children[0] = lhs;
    n.children[1] = rhs;
    return intern(std::move(n));
}

FormulaId FormulaFactory::make_int_equal(FormulaId lhs, FormulaId rhs) {
    FormulaNode n;
    n.kind = NodeKind::IntEqual;
    n.children[0] = lhs;
    n.children[1] = rhs;
    return intern(std::move(n));
}

// ── Accessors ───────────────────────────────────────────────────────────────

const FormulaNode& FormulaFactory::node(FormulaId id) const {
    if (id >= nodes_.size()) {
        throw std::out_of_range("FormulaFactory::node: invalid FormulaId");
    }
    return nodes_[id];
}

std::size_t FormulaFactory::size() const noexcept {
    return nodes_.size();
}

// ── Pretty-printing ─────────────────────────────────────────────────────────
// Produces a fully parenthesised string for unambiguity.

std::string FormulaFactory::to_string(FormulaId id) const {
    const FormulaNode& n = node(id);

    switch (n.kind) {
        case NodeKind::True:
            return "true";
        case NodeKind::False:
            return "false";
        case NodeKind::Atom:
            return n.atom_name;
        case NodeKind::Not:
            return "(!" + to_string(n.children[0]) + ")";
        case NodeKind::And:
            return "(" + to_string(n.children[0]) + " & " + to_string(n.children[1]) + ")";
        case NodeKind::Or:
            return "(" + to_string(n.children[0]) + " | " + to_string(n.children[1]) + ")";
        case NodeKind::Implies:
            return "(" + to_string(n.children[0]) + " -> " + to_string(n.children[1]) + ")";
        case NodeKind::Iff:
            return "(" + to_string(n.children[0]) + " <-> " + to_string(n.children[1]) + ")";
        case NodeKind::EX:
            return "EX " + to_string(n.children[0]);
        case NodeKind::AX:
            return "AX " + to_string(n.children[0]);
        case NodeKind::EU:
            return "E(" + to_string(n.children[0]) + " U " + to_string(n.children[1]) + ")";
        case NodeKind::AU:
            return "A(" + to_string(n.children[0]) + " U " + to_string(n.children[1]) + ")";
        case NodeKind::ER:
            return "E(" + to_string(n.children[0]) + " R " + to_string(n.children[1]) + ")";
        case NodeKind::AR:
            return "A(" + to_string(n.children[0]) + " R " + to_string(n.children[1]) + ")";
        case NodeKind::EF:
            return "EF " + to_string(n.children[0]);
        case NodeKind::AF:
            return "AF " + to_string(n.children[0]);
        case NodeKind::EG:
            return "EG " + to_string(n.children[0]);
        case NodeKind::AG:
            return "AG " + to_string(n.children[0]);
        // TCTL timed operators (canonical)
        case NodeKind::TimedEU: {
            std::string interval = n.time_lower.to_string_lower() + "," + 
                                   n.time_upper.to_string_upper();
            return "E(" + to_string(n.children[0]) + " U" + interval + " " + 
                   to_string(n.children[1]) + ")";
        }
        case NodeKind::TimedAU: {
            std::string interval = n.time_lower.to_string_lower() + "," + 
                                   n.time_upper.to_string_upper();
            return "A(" + to_string(n.children[0]) + " U" + interval + " " + 
                   to_string(n.children[1]) + ")";
        }
        case NodeKind::TimedER: {
            std::string interval = n.time_lower.to_string_lower() + "," + 
                                   n.time_upper.to_string_upper();
            return "E(" + to_string(n.children[0]) + " R" + interval + " " + 
                   to_string(n.children[1]) + ")";
        }
        case NodeKind::TimedAR: {
            std::string interval = n.time_lower.to_string_lower() + "," + 
                                   n.time_upper.to_string_upper();
            return "A(" + to_string(n.children[0]) + " R" + interval + " " + 
                   to_string(n.children[1]) + ")";
        }
        // TCTL timed operators (sugar)
        case NodeKind::TimedEF: {
            std::string interval = n.time_lower.to_string_lower() + "," + 
                                   n.time_upper.to_string_upper();
            return "EF" + interval + " " + to_string(n.children[0]);
        }
        case NodeKind::TimedAF: {
            std::string interval = n.time_lower.to_string_lower() + "," + 
                                   n.time_upper.to_string_upper();
            return "AF" + interval + " " + to_string(n.children[0]);
        }
        case NodeKind::TimedEG: {
            std::string interval = n.time_lower.to_string_lower() + "," + 
                                   n.time_upper.to_string_upper();
            return "EG" + interval + " " + to_string(n.children[0]);
        }
        case NodeKind::TimedAG: {
            std::string interval = n.time_lower.to_string_lower() + "," + 
                                   n.time_upper.to_string_upper();
            return "AG" + interval + " " + to_string(n.children[0]);
        }
        case NodeKind::IntVar:
            return n.atom_name;
        case NodeKind::IntConst:
            return std::to_string(n.int_value);
        case NodeKind::IntPlus:
            return "(" + to_string(n.children[0]) + " + " + to_string(n.children[1]) + ")";
        case NodeKind::IntMinus:
            return "(" + to_string(n.children[0]) + " - " + to_string(n.children[1]) + ")";
        case NodeKind::IntTimes:
            return "(" + to_string(n.children[0]) + " * " + to_string(n.children[1]) + ")";
        case NodeKind::IntLessEq:
            return "(" + to_string(n.children[0]) + " <= " + to_string(n.children[1]) + ")";
        case NodeKind::IntLess:
            return "(" + to_string(n.children[0]) + " < " + to_string(n.children[1]) + ")";
        case NodeKind::IntGreaterEq:
            return "(" + to_string(n.children[0]) + " >= " + to_string(n.children[1]) + ")";
        case NodeKind::IntGreater:
            return "(" + to_string(n.children[0]) + " > " + to_string(n.children[1]) + ")";
        case NodeKind::IntEqual:
            return "(" + to_string(n.children[0]) + " = " + to_string(n.children[1]) + ")";
    }
    return "<?>";
}

// ── FormulaSet ──────────────────────────────────────────────────────────────
// Maintains a sorted, unique vector of FormulaIds for deterministic
// representation of formula sets (e.g., tableau states).

void FormulaSet::insert(FormulaId id) {
    auto pos = std::lower_bound(data_.begin(), data_.end(), id);
    if (pos == data_.end() || *pos != id) {
        data_.insert(pos, id);
    }
}

bool FormulaSet::contains(FormulaId id) const noexcept {
    return std::binary_search(data_.begin(), data_.end(), id);
}

bool FormulaSet::empty() const noexcept {
    return data_.empty();
}

std::size_t FormulaSet::size() const noexcept {
    return data_.size();
}

const std::vector<FormulaId>& FormulaSet::elements() const noexcept {
    return data_;
}

bool FormulaSet::operator==(const FormulaSet& o) const noexcept {
    return data_ == o.data_;
}

bool FormulaSet::operator<(const FormulaSet& o) const noexcept {
    return data_ < o.data_;
}

}  // namespace tctl
