// ============================================================================
// tableau.cpp — One-Pass Context-Based tctl Tableau Engine Implementation
// ============================================================================
//
// This file implements the tctl tableau satisfiability algorithm exactly as
// specified in the prompt, based on Abuin et al., TIME 2020.
//
// KEY DESIGN DECISIONS:
// ─────────────────────
// 1. Pure rewrite rules: Each rule mechanically transforms Γ without
//    semantic reasoning about the formula meaning.
//
// 2. Context propagation: AX formulas are moved to the context and
//    propagated to ALL successors.
//
// 3. Loop detection: When a node's (Γ, context) matches an ancestor,
//    we have a potential loop.
//
// 4. Eventuality checking: Loops are accepted ONLY if all active
//    eventualities E(φ U ψ) and A(φ U ψ) have ψ appearing in some
//    node within the loop.
//
// 5. Totality: Models are total. If no successors are required,
//    we create a stutter successor seeded from universal obligations.
//
// ============================================================================

#include "tctl/tableau.hpp"
#include "tctl/zone.hpp"

#include <algorithm>
#include <cassert>
#include <functional>
#include <iostream>
#include <sstream>

#ifdef TCTL_USE_OPENMP
#include <omp.h>
#endif

// #define TABLEAU_DEBUG 1  // Uncomment for debug output
#ifdef TABLEAU_DEBUG
#include <iostream>
#endif

namespace tctl {

// ============================================================================
// Result string conversion
// ============================================================================

const char* result_to_string(const Result& r) noexcept {
    switch (r.verdict) {
        case Result::Value::Satisfiable:   return "SATISFIABLE";
        case Result::Value::Unsatisfiable: return "UNSATISFIABLE";
        case Result::Value::Timeout:       return "TIMEOUT";
    }
    return "?";
}

// ============================================================================
// Context implementation
// ============================================================================

void Context::add_next_all(FormulaId id) {
    // Insert maintaining sorted order (no duplicates).
    auto pos = std::lower_bound(nextAll.begin(), nextAll.end(), id);
    if (pos == nextAll.end() || *pos != id) {
        nextAll.insert(pos, id);
    }
}

void Context::merge(const Context& other) {
    for (FormulaId id : other.nextAll) {
        add_next_all(id);
    }
}

// ============================================================================
// ContextHash implementation
// ============================================================================

std::size_t ContextHash::operator()(const Context& ctx) const noexcept {
    std::size_t h = 0;
    for (FormulaId id : ctx.nextAll) {
        h ^= std::hash<FormulaId>{}(id) + 0x9e3779b9 + (h << 6) + (h >> 2);
    }
    return h;
}

// ============================================================================
// NodeKeyHash implementation
// ============================================================================

std::size_t NodeKeyHash::operator()(const NodeKey& key) const noexcept {
    std::size_t h = 0;
    for (FormulaId id : key.gamma.elements()) {
        h ^= std::hash<FormulaId>{}(id) + 0x9e3779b9 + (h << 6) + (h >> 2);
    }
    h ^= ContextHash{}(key.ctx) + 0x9e3779b9 + (h << 6) + (h >> 2);
    return h;
}

// ============================================================================
// TableauNode implementation
// ============================================================================

bool TableauNode::is_ancestor_of(const TableauNode* other) const {
    const TableauNode* curr = other->parent;
    while (curr != nullptr) {
        if (curr == this) return true;
        curr = curr->parent;
    }
    return false;
}

// ============================================================================
// TableauStats implementation
// ============================================================================

std::string TableauStats::to_string() const {
    std::ostringstream oss;
    oss << "nodes=" << nodes_created.load()
        << " open=" << nodes_open.load()
        << " closed=" << nodes_closed.load()
        << " max_depth=" << max_depth.load()
        << " memo_hits=" << memo_hits.load()
        << " loop_checks=" << loop_checks.load();
    return oss.str();
}

// ============================================================================
// KripkeModel implementation
// ============================================================================

std::string KripkeModel::to_string() const {
    std::ostringstream oss;
    oss << "Kripke model with " << states.size() << " state(s):\n";
    oss << "  Initial state: s" << initial_state << "\n";

    for (const auto& state : states) {
        oss << "  s" << state.id << ": {";
        bool first = true;
        for (const auto& atom : state.atoms) {
            if (!first) oss << ", ";
            oss << atom;
            first = false;
        }
        oss << "} -> {";
        first = true;
        for (auto succ : state.successors) {
            if (!first) oss << ", ";
            oss << "s" << succ;
            first = false;
        }
        oss << "}\n";
    }
    return oss.str();
}

std::string KripkeModel::to_json() const {
    std::ostringstream oss;
    oss << "{\n";
    oss << "  \"initial_state\": " << initial_state << ",\n";
    oss << "  \"states\": [\n";
    for (std::size_t i = 0; i < states.size(); ++i) {
        const auto& s = states[i];
        oss << "    {\n";
        oss << "      \"id\": " << s.id << ",\n";
        oss << "      \"atoms\": [";
        bool first = true;
        for (const auto& a : s.atoms) {
            if (!first) oss << ", ";
            oss << "\"" << a << "\"";
            first = false;
        }
        oss << "],\n";
        oss << "      \"successors\": [";
        first = true;
        for (auto succ : s.successors) {
            if (!first) oss << ", ";
            oss << succ;
            first = false;
        }
        oss << "]\n";
        oss << "    }";
        if (i + 1 < states.size()) oss << ",";
        oss << "\n";
    }
    oss << "  ]\n";
    oss << "}\n";
    return oss.str();
}

std::string KripkeModel::to_dot() const {
    std::ostringstream oss;
    oss << "digraph KripkeModel {\n";
    oss << "  rankdir=LR;\n";
    oss << "  node [shape=circle fontname=\"Helvetica\"];\n";
    // invisible entry arrow into initial state
    oss << "  __init [shape=none label=\"\"];\n";
    oss << "  __init -> s" << initial_state << ";\n";
    for (const auto& s : states) {
        std::string shape = (s.id == initial_state) ? "doublecircle" : "circle";
        oss << "  s" << s.id << " [shape=" << shape << " label=\"s" << s.id << "\\n{";
        bool first = true;
        for (const auto& a : s.atoms) {
            if (!first) oss << ", ";
            oss << a;
            first = false;
        }
        oss << "}\"];\n";
        for (auto succ : s.successors) {
            oss << "  s" << s.id << " -> s" << succ << ";\n";
        }
    }
    oss << "}\n";
    return oss.str();
}

// ============================================================================
// TableauEngine implementation
// ============================================================================

TableauEngine::TableauEngine(FormulaFactory& factory)
    : factory_(factory) {}

TableauEngine::~TableauEngine() = default;

// ── Node allocation (thread-safe) ───────────────────────────────────────────

TableauNode* TableauEngine::alloc_node() {
    auto node = std::make_unique<TableauNode>();
    node->id = next_node_id_.fetch_add(1, std::memory_order_relaxed);
    TableauNode* raw = node.get();
    {
        std::lock_guard<std::mutex> lk(alloc_mutex_);
        nodes_.push_back(std::move(node));
    }
    stats_.nodes_created.fetch_add(1, std::memory_order_relaxed);
    return raw;
}

// ============================================================================
// TCTL clock allocation and zone helpers
// ============================================================================

// Pre-scan the formula DAG to find all TimedEU/TimedAU nodes and allocate
// one clock per syntactic timed-until.  Also compute per-clock max constants
// for zone extrapolation (k-normalization).
void TableauEngine::allocate_clocks(FormulaId formula) {
    // BFS/DFS over the formula DAG.
    std::unordered_set<FormulaId> visited;
    std::vector<FormulaId> stack;
    stack.push_back(formula);

    while (!stack.empty()) {
        FormulaId fid = stack.back();
        stack.pop_back();
        if (fid == kInvalidId || visited.count(fid)) continue;
        visited.insert(fid);

        const FormulaNode& n = factory_.node(fid);

        if (n.kind == NodeKind::TimedEU || n.kind == NodeKind::TimedAU ||
            n.kind == NodeKind::TimedER || n.kind == NodeKind::TimedAR) {
            if (clock_of_.find(fid) == clock_of_.end()) {
                ClockId clk = static_cast<ClockId>(num_clocks_);
                clock_of_[fid] = clk;
                num_clocks_++;
            }
        }

        if (n.children[0] != kInvalidId) stack.push_back(n.children[0]);
        if (n.children[1] != kInvalidId) stack.push_back(n.children[1]);
    }

    // Build per-clock max constant table for extrapolation.
    max_constants_.assign(num_clocks_, 0);   // max_constants_[0] = 0 (reference)
    for (const auto& [fid, clk] : clock_of_) {
        const FormulaNode& n = factory_.node(fid);
        std::int32_t lo = static_cast<std::int32_t>(n.time_lower.value);
        std::int32_t hi = n.time_upper.is_infinity ? 0
                          : static_cast<std::int32_t>(n.time_upper.value);
        std::int32_t m = std::max(lo, hi);
        if (m > max_constants_[clk]) max_constants_[clk] = m;
    }
}

// Apply interval constraints to zone for a specific clock.
// lower bound: clock >= lower.value (strict if lower.is_strict)
// upper bound: clock <= upper.value (strict if upper.is_strict), unless infinity
// Returns false if zone becomes empty after applying.
bool TableauEngine::apply_interval(Zone& zone, ClockId clock,
                                    const TimeBound& lower, const TimeBound& upper) {
    // Lower bound
    if (lower.value > 0 || lower.is_strict) {
        zone.add_lower_bound(clock, static_cast<std::int32_t>(lower.value), lower.is_strict);
        if (zone.is_empty()) return false;
    }

    // Upper bound
    if (!upper.is_infinity) {
        zone.add_upper_bound(clock, static_cast<std::int32_t>(upper.value), upper.is_strict);
        if (zone.is_empty()) return false;
    }

    return true;
}

// Build canonical zone string for memoization key.
std::string TableauEngine::zone_canonical_string(const Zone& zone) {
    return zone.to_string();
}

// Check deadline feasibility: for each active timed obligation with a finite
// upper bound, verify that the zone can still satisfy clock <= upper.
bool TableauEngine::check_deadline_feasibility(const Zone& zone,
                                                const std::set<FormulaId>& active_timed) {
    for (FormulaId fid : active_timed) {
        const FormulaNode& n = factory_.node(fid);
        if (n.kind != NodeKind::TimedEU && n.kind != NodeKind::TimedAU) continue;

        const TimeBound& upper = n.time_upper;
        if (upper.is_infinity) continue;  // No deadline

        auto it = clock_of_.find(fid);
        if (it == clock_of_.end()) continue;
        ClockId clk = it->second;

        // Check if zone can still satisfy clock ≤ upper (or < upper)
        Zone test_zone = zone;
        test_zone.add_upper_bound(clk, static_cast<std::int32_t>(upper.value), upper.is_strict);
        if (test_zone.is_empty()) {
            return false;  // Deadline impossible
        }
    }
    return true;
}

// Check if a timed eventuality is fulfilled at a node:
// ψ ∈ Γ AND Sat(zone ∧ (clock ∈ I)).
bool TableauEngine::timed_eventuality_fulfilled(FormulaId eventuality,
                                                 const TableauNode* node) const {
    const FormulaNode& n = factory_.node(eventuality);

    if (n.kind != NodeKind::TimedEU && n.kind != NodeKind::TimedAU) {
        // Not a timed eventuality — delegate to untimed check.
        return eventuality_fulfilled(eventuality, node->gamma);
    }

    FormulaId psi = n.children[1];
    if (!node->gamma.contains(psi)) return false;

    // Check that clock satisfies interval
    auto it = clock_of_.find(eventuality);
    if (it == clock_of_.end()) return true;  // No clock → trivially ok
    ClockId clk = it->second;

    Zone test_zone = node->zone;
    // Apply lower bound
    const TimeBound& lower = n.time_lower;
    if (lower.value > 0 || lower.is_strict) {
        test_zone.add_lower_bound(clk, static_cast<std::int32_t>(lower.value), lower.is_strict);
    }
    // Apply upper bound
    const TimeBound& upper = n.time_upper;
    if (!upper.is_infinity) {
        test_zone.add_upper_bound(clk, static_cast<std::int32_t>(upper.value), upper.is_strict);
    }

    return !test_zone.is_empty();
}

// ============================================================================
// check() — Main entry point
// ============================================================================
//
// Algorithm:
//   1. Create initial node with Γ = {input_formula}, empty context.
//   2. Run DFS from the initial node.
//   3. If DFS finds an open branch, return SAT.
//   4. Otherwise return UNSAT.

Result TableauEngine::check(FormulaId normalized_formula) {
    // Reset state from previous runs.
    nodes_.clear();
    memo_.clear();
    stats_.reset();
    model_.reset();
    model_set_.store(false, std::memory_order_relaxed);
    stop_.store(false, std::memory_order_relaxed);
    next_node_id_.store(0, std::memory_order_relaxed);

    // ── TCTL clock allocation ───────────────────────────────────────────
    clock_of_.clear();
    num_clocks_ = 1;  // clock 0 is the reference clock
    allocate_clocks(normalized_formula);

    // Create the initial node.
    TableauNode* root = alloc_node();
    root->gamma.insert(normalized_formula);
    root->depth = 0;

    // Set up initial zone: universe over allocated clocks.
    if (num_clocks_ > 1) {
        root->zone = Zone::universe(num_clocks_);
    }

    // Set up deadline and start timer.
    timed_out_.store(false, std::memory_order_relaxed);
    const auto t_start = std::chrono::steady_clock::now();
    if (timeout_.count() > 0) {
        deadline_ = t_start + timeout_;
    }

#ifdef TCTL_USE_OPENMP
    if (num_threads_ > 0) omp_set_num_threads(num_threads_);
#endif

    // Run DFS with a fresh BranchState.
    BranchState bs;
    bool sat = false;

#ifdef TCTL_USE_OPENMP
    // Launch a parallel region with a single initial thread entering
    // dfs().  Inside dfs(), child exploration may spawn OpenMP tasks.
    #pragma omp parallel shared(sat, bs, root) if(num_threads_ != 1)
    {
        #pragma omp single nowait
        {
            sat = dfs(root, bs);
        }
    }
#else
    sat = dfs(root, bs);
#endif

    const double elapsed = std::chrono::duration<double>(
        std::chrono::steady_clock::now() - t_start).count();

    if (timed_out_.load(std::memory_order_relaxed))
        return Result(Result::Value::Timeout, elapsed);
    return Result(sat ? Result::Value::Satisfiable : Result::Value::Unsatisfiable, elapsed);
}

// ============================================================================
// dfs() — Depth-first search with backtracking
// ============================================================================
//
// Returns true if this node (or any of its descendants) leads to a SAT branch.

// ============================================================================
// compute_zone_key() — Normalized zone string for memo / loop detection
// ============================================================================
// Free clocks NOT in active_timed (irrelevant clock state) and then
// extrapolate active ones.  This ensures zones that differ only in
// irrelevant clock values map to the same key.

std::string TableauEngine::compute_zone_key(const TableauNode* node) const {
    if (num_clocks_ <= 1) return {};
    Zone key_zone = node->zone;
    for (const auto& [fid, clk] : clock_of_) {
        if (node->active_timed.find(fid) == node->active_timed.end()) {
            key_zone.free(clk);
        }
    }
    key_zone.extrapolate(max_constants_);
    return zone_canonical_string(key_zone);
}

// ============================================================================
// dfs() — Depth-first search with backtracking (branch-local state)
// ============================================================================
//
// BranchState holds the ancestor stack/set for this thread's DFS path.
// Each spawned OpenMP task receives its own copy of BranchState so that
// loop detection (ancestor matching) never crosses thread boundaries.
//
// Memoization uses a concurrent map with striped locking.  The memo
// value is a MemoEntry with an atomic status field:
//   0 = Unknown  → exploration in progress somewhere
//   1 = Open     → SAT (fast-return true)
//   2 = Closed   → UNSAT (fast-return false)
// Loop detection is purely based on the current thread's BranchState
// ancestor stack — we never infer "loop" from another thread's Unknown.

bool TableauEngine::dfs(TableauNode* node, BranchState& bs) {
#ifdef TABLEAU_DEBUG
    std::cerr << "DFS node " << node->id << " depth=" << node->depth 
              << " gamma_size=" << node->gamma.size()
              << " children=" << node->children.size()
              << " delay=" << node->is_delay_successor << "\n";
    for (FormulaId fid : node->gamma.elements()) {
        std::cerr << "  gamma: " << factory_.to_string(fid) << " (id=" << fid << ")\n";
    }
    std::cerr << "  zone: " << node->zone.to_string() << "\n";
    if (!node->active_timed.empty()) {
        std::cerr << "  active_timed:";
        for (FormulaId fid : node->active_timed) std::cerr << " " << fid;
        std::cerr << "\n";
    }
#endif
    // ── Early stop (another thread already found SAT) ────────────────────
    if (stop_.load(std::memory_order_relaxed)) {
        node->status = NodeStatus::Closed;
        return false;
    }

    // ── Timeout check ────────────────────────────────────────────────────
    if (timeout_.count() > 0 && (node->id & 0x10) == 0) {
        if (std::chrono::steady_clock::now() >= deadline_) {
            timed_out_.store(true, std::memory_order_relaxed);
            node->status = NodeStatus::Closed;
            return false;
        }
    }

    // ── Depth limit to prevent stack overflow ───────────────────────────
    static const std::uint32_t MAX_DEPTH = 10000;
    if (node->depth > MAX_DEPTH) {
        node->status = NodeStatus::Closed;
        stats_.nodes_closed.fetch_add(1, std::memory_order_relaxed);
        return false;
    }

    // ── Compute normalized zone key ─────────────────────────────────────
    std::string zone_key = compute_zone_key(node);
    NodeKey key{node->gamma, node->ctx, zone_key};

    // ── Check memo (striped lock) ───────────────────────────────────────
    std::size_t stripe = memo_stripe(key);
    std::shared_ptr<MemoEntry> memo_entry;
    {
        std::lock_guard<std::mutex> lk(memo_locks_[stripe]);
        auto memo_it = memo_.find(key);
        if (memo_it != memo_.end()) {
            memo_entry = memo_it->second;
        }
    }

    if (memo_entry) {
        int st = memo_entry->status.load(std::memory_order_acquire);
        if (st == MemoEntry::kClosed) {
            stats_.memo_hits.fetch_add(1, std::memory_order_relaxed);
            node->status = NodeStatus::Closed;
            stats_.nodes_closed.fetch_add(1, std::memory_order_relaxed);
            return false;
        }
        if (st == MemoEntry::kOpen) {
            stats_.memo_hits.fetch_add(1, std::memory_order_relaxed);
            node->status = NodeStatus::Open;
            stats_.nodes_open.fetch_add(1, std::memory_order_relaxed);
            return true;
        }
        // st == Unknown: another thread is exploring this key.
        // Only treat as a loop if the node is on THIS branch's ancestor stack.
        // Otherwise, proceed conservatively (explore independently).
    }

    // ── Loop detection (branch-local) ───────────────────────────────────
    TableauNode* loop_ancestor = find_loop_ancestor(node, bs);
    if (loop_ancestor != nullptr) {
        stats_.loop_checks.fetch_add(1, std::memory_order_relaxed);

        if (check_eventuality_coverage(loop_ancestor, node)) {
            node->status = NodeStatus::Open;
            stats_.nodes_open.fetch_add(1, std::memory_order_relaxed);
            return true;
        } else {
            node->status = NodeStatus::Closed;
            stats_.nodes_closed.fetch_add(1, std::memory_order_relaxed);
            return false;
        }
    }

    // ── Insert into memo as Unknown (in-progress) ───────────────────────
    if (!memo_entry) {
        memo_entry = std::make_shared<MemoEntry>();
        std::lock_guard<std::mutex> lk(memo_locks_[stripe]);
        // Double-check: another thread may have inserted between our
        // check above and now.
        auto [it, inserted] = memo_.emplace(key, memo_entry);
        if (!inserted) {
            memo_entry = it->second;
            int st = memo_entry->status.load(std::memory_order_acquire);
            if (st == MemoEntry::kClosed) {
                stats_.memo_hits.fetch_add(1, std::memory_order_relaxed);
                node->status = NodeStatus::Closed;
                stats_.nodes_closed.fetch_add(1, std::memory_order_relaxed);
                return false;
            }
            if (st == MemoEntry::kOpen) {
                stats_.memo_hits.fetch_add(1, std::memory_order_relaxed);
                node->status = NodeStatus::Open;
                stats_.nodes_open.fetch_add(1, std::memory_order_relaxed);
                return true;
            }
            // Unknown — proceed to explore
        }
    }

    // ── Push onto ancestor stack ────────────────────────────────────────
    bs.push(node);

    // Track max depth.
    stats_.update_max_depth(node->depth);

    // ── Expand the node (apply rewrite rules) ───────────────────────────
    bool expanded = expand_node(node);

    if (!expanded) {
        node->status = NodeStatus::Closed;
        stats_.nodes_closed.fetch_add(1, std::memory_order_relaxed);
        memo_entry->status.store(MemoEntry::kClosed, std::memory_order_release);
        bs.pop(node);
        return false;
    }

    // ── Generate successors ─────────────────────────────────────────────
    generate_successors(node);

    // ── If no children, this is a leaf ──────────────────────────────────
    if (node->children.empty()) {
        node->status = NodeStatus::Open;
        stats_.nodes_open.fetch_add(1, std::memory_order_relaxed);
        memo_entry->status.store(MemoEntry::kOpen, std::memory_order_release);
        bs.pop(node);

        if (extract_model_) {
            extract_model_from_branch(node);
        }
        return true;
    }

    // ── Process children ────────────────────────────────────────────────
    bool result = false;
    const std::size_t n_children = node->children.size();

#ifdef TCTL_USE_OPENMP
    // Only parallelize when there are >= 2 children, depth is below
    // the limit, and we are inside a parallel region.
    const bool do_parallel = (n_children >= 2)
                           && (static_cast<int>(node->depth) < par_depth_limit_)
                           && (omp_get_num_threads() > 1)
                           && (num_threads_ != 1);
#else
    const bool do_parallel = false;
#endif

    if (node->kind == TableauNodeKind::OR) {
        // OR node: need at least one open child.
        if (do_parallel) {
#ifdef TCTL_USE_OPENMP
            std::atomic<bool> any_sat{false};
            for (std::size_t ci = 0; ci < n_children; ++ci) {
                // Copy branch state per task.
                BranchState child_bs = bs;
                TableauNode* child = node->children[ci];
                #pragma omp task firstprivate(child_bs, child) shared(any_sat)
                {
                    if (!any_sat.load(std::memory_order_relaxed)) {
                        if (dfs(child, child_bs)) {
                            any_sat.store(true, std::memory_order_relaxed);
                        }
                    }
                }
            }
            #pragma omp taskwait
            result = any_sat.load(std::memory_order_relaxed);
#endif
        } else {
            // Sequential OR
            for (std::size_t ci = 0; ci < n_children; ++ci) {
                if (dfs(node->children[ci], bs)) {
                    result = true;
                    break;
                }
            }
        }
    } else {
        // AND node: need all children open.
        if (do_parallel) {
#ifdef TCTL_USE_OPENMP
            std::atomic<bool> all_sat{true};
            for (std::size_t ci = 0; ci < n_children; ++ci) {
                BranchState child_bs = bs;
                TableauNode* child = node->children[ci];
                #pragma omp task firstprivate(child_bs, child) shared(all_sat)
                {
                    if (all_sat.load(std::memory_order_relaxed)) {
                        if (!dfs(child, child_bs)) {
                            all_sat.store(false, std::memory_order_relaxed);
                        }
                    }
                }
            }
            #pragma omp taskwait
            result = all_sat.load(std::memory_order_relaxed);
#endif
        } else {
            // Sequential AND
            result = true;
            for (std::size_t ci = 0; ci < n_children; ++ci) {
                if (!dfs(node->children[ci], bs)) {
                    result = false;
                    break;
                }
            }
        }
    }

    // ── Update status and memo ──────────────────────────────────────────
    if (result) {
        node->status = NodeStatus::Open;
        stats_.nodes_open.fetch_add(1, std::memory_order_relaxed);
        memo_entry->status.store(MemoEntry::kOpen, std::memory_order_release);
    } else {
        node->status = NodeStatus::Closed;
        stats_.nodes_closed.fetch_add(1, std::memory_order_relaxed);
        memo_entry->status.store(MemoEntry::kClosed, std::memory_order_release);
    }

    // ── Pop from ancestor stack ─────────────────────────────────────────
    bs.pop(node);

    return result;
}

// ============================================================================
// expand_node() — Apply rewrite rules until saturation
// ============================================================================
//
// This function applies the tableau rules in a specific order:
//   (0) Contradiction check (close if false ∈ Γ or p, !p ∈ Γ)
//   (1) Remove true from Γ
//   (2) ∧-rule (non-branching)
//   (3) AX-rule (move to context)
//   (4) ∨-rule (branching) - creates OR node
//   (5) EU-rule (branching) - creates OR node
//   (6) AU-rule (branching) - creates OR node
//
// Returns false if the node should be closed (contradiction).
// After expansion, the node's gamma contains only:
//   - Literals (atoms or negated atoms)
//   - EX formulas
//   - Negated EU/AU formulas (handled specially)

bool TableauEngine::expand_node(TableauNode* node) {
    // We iterate until no more rules apply. Changes to gamma may enable
    // new rule applications.


    bool changed = true;
    while (changed) {
        changed = false;

        // ── (0) CONTRADICTION CHECK ─────────────────────────────────────
        // Check if false is in Γ.
        // Check if both p and !p are in Γ for some atom p.
        if (has_contradiction(node)) {
            return false;  // Close this node.
        }

        // ── (1) REMOVE TRUE ─────────────────────────────────────────────
        // true is trivially satisfied; remove it from Γ.
        {
            FormulaId true_id = factory_.make_true();
            if (node->gamma.contains(true_id)) {
                FormulaSet new_gamma;
                for (FormulaId id : node->gamma.elements()) {
                    if (id != true_id) {
                        new_gamma.insert(id);
                    }
                }
                node->gamma = std::move(new_gamma);
                changed = true;
            }
        }

        // ── (2) ∧-RULE (AND, non-branching) ─────────────────────────────
        // If (φ & ψ) ∈ Γ:
        //   Γ := (Γ \ {φ&ψ}) ∪ {φ, ψ}
        {
            FormulaId and_formula = kInvalidId;
            for (FormulaId id : node->gamma.elements()) {
                const FormulaNode& n = factory_.node(id);
                if (n.kind == NodeKind::And) {
                    and_formula = id;
                    break;
                }
            }

            if (and_formula != kInvalidId) {
                const FormulaNode& n = factory_.node(and_formula);
                FormulaSet new_gamma;
                for (FormulaId id : node->gamma.elements()) {
                    if (id != and_formula) {
                        new_gamma.insert(id);
                    }
                }
                new_gamma.insert(n.children[0]);
                new_gamma.insert(n.children[1]);
                node->gamma = std::move(new_gamma);
                changed = true;
                continue;  // Restart to check for more rules.
            }
        }

        // ── (3) AX-RULE ─────────────────────────────────────────────────
        // If AX φ ∈ Γ:
        //   Remove AX φ from Γ
        //   Add φ to Context.nextAll
        {
            FormulaId ax_formula = kInvalidId;
            for (FormulaId id : node->gamma.elements()) {
                const FormulaNode& n = factory_.node(id);
                if (n.kind == NodeKind::AX) {
                    ax_formula = id;
                    break;
                }
            }

            if (ax_formula != kInvalidId) {
                const FormulaNode& n = factory_.node(ax_formula);
                FormulaSet new_gamma;
                for (FormulaId id : node->gamma.elements()) {
                    if (id != ax_formula) {
                        new_gamma.insert(id);
                    }
                }
                node->gamma = std::move(new_gamma);
                node->ctx.add_next_all(n.children[0]);
                changed = true;
                continue;
            }
        }

        // ── (3b) TCTL ACTIVATION RULE ───────────────────────────────────
        // If a timed-until ξ ∈ Γ and ξ ∉ activeTimed:
        //   mark ξ active, reset its clock.
        if (num_clocks_ > 1) {
            FormulaId timed_to_activate = kInvalidId;
            for (FormulaId id : node->gamma.elements()) {
                const FormulaNode& n = factory_.node(id);
                if ((n.kind == NodeKind::TimedEU || n.kind == NodeKind::TimedAU ||
                     n.kind == NodeKind::TimedER || n.kind == NodeKind::TimedAR) &&
                    node->active_timed.find(id) == node->active_timed.end()) {
                    timed_to_activate = id;
                    break;
                }
            }

            if (timed_to_activate != kInvalidId) {
                node->active_timed.insert(timed_to_activate);
                auto it = clock_of_.find(timed_to_activate);
                if (it != clock_of_.end()) {
                    node->zone.reset(it->second);
                    node->clock_resets.push_back(it->second);
                    if (node->zone.is_empty()) {
                        return false;  // Zone became empty
                    }
                }
                changed = true;
                continue;
            }
        }

        // ── (4) ∨-RULE (OR, branching) ──────────────────────────────────
        // If (φ | ψ) ∈ Γ:
        //   Create two children:
        //     Child1: (Γ \ {φ|ψ}) ∪ {φ}
        //     Child2: (Γ \ {φ|ψ}) ∪ {ψ}
        //   This node becomes an OR node.
        {
            FormulaId or_formula = kInvalidId;
            for (FormulaId id : node->gamma.elements()) {
                const FormulaNode& n = factory_.node(id);
                if (n.kind == NodeKind::Or) {
                    or_formula = id;
                    break;
                }
            }

            if (or_formula != kInvalidId) {
                const FormulaNode& n = factory_.node(or_formula);

                // Build the base gamma without the OR formula.
                FormulaSet base_gamma;
                for (FormulaId id : node->gamma.elements()) {
                    if (id != or_formula) {
                        base_gamma.insert(id);
                    }
                }

                // Child 1: base + φ
                TableauNode* child1 = alloc_node();
                child1->gamma = base_gamma;
                child1->gamma.insert(n.children[0]);
                child1->ctx = node->ctx;
                child1->parent = node;
                child1->depth = node->depth + 1;
                child1->active_eventualities = node->active_eventualities;
                child1->zone = node->zone;
                child1->active_timed = node->active_timed;

                child1->committed_timed = node->committed_timed;

                // Child 2: base + ψ
                TableauNode* child2 = alloc_node();
                child2->gamma = base_gamma;
                child2->gamma.insert(n.children[1]);
                child2->ctx = node->ctx;
                child2->parent = node;
                child2->depth = node->depth + 1;
                child2->active_eventualities = node->active_eventualities;
                child2->zone = node->zone;
                child2->active_timed = node->active_timed;

                child2->committed_timed = node->committed_timed;

                node->children.push_back(child1);
                node->children.push_back(child2);
                node->kind = TableauNodeKind::OR;

                // Don't clear gamma - keep original state for loop detection.
                return true;  // Expansion complete via children.
            }
        }

        // ── (5) EU-RULE (E Until, branching) ────────────────────────────
        // If E(φ U ψ) ∈ Γ:
        //   Let e = E(φ U ψ)
        //   Branch:
        //     STOP: (Γ \ {e}) ∪ {ψ}         — eventuality fulfilled
        //     GO:   (Γ \ {e}) ∪ {φ, EX e}   — postpone eventuality
        {
            FormulaId eu_formula = kInvalidId;
            for (FormulaId id : node->gamma.elements()) {
                const FormulaNode& n = factory_.node(id);
                if (n.kind == NodeKind::EU) {
                    eu_formula = id;
                    break;
                }
            }

            if (eu_formula != kInvalidId) {
                const FormulaNode& n = factory_.node(eu_formula);
                FormulaId phi = n.children[0];  // The "until" condition
                FormulaId psi = n.children[1];  // The goal

                // Build base gamma without the EU formula.
                FormulaSet base_gamma;
                for (FormulaId id : node->gamma.elements()) {
                    if (id != eu_formula) {
                        base_gamma.insert(id);
                    }
                }

                // STOP child: ψ (eventuality fulfilled)
                TableauNode* stop_child = alloc_node();
                stop_child->gamma = base_gamma;
                stop_child->gamma.insert(psi);
                stop_child->ctx = node->ctx;
                stop_child->parent = node;
                stop_child->depth = node->depth + 1;
                stop_child->active_eventualities = node->active_eventualities;
                // Remove this eventuality from active set (fulfilled).
                stop_child->active_eventualities.erase(eu_formula);
                stop_child->zone = node->zone;
                stop_child->active_timed = node->active_timed;

                stop_child->committed_timed = node->committed_timed;

                // GO child: φ, EX e (postpone)
                TableauNode* go_child = alloc_node();
                go_child->gamma = base_gamma;
                go_child->gamma.insert(phi);
                go_child->gamma.insert(factory_.make_ex(eu_formula));
                go_child->ctx = node->ctx;
                go_child->parent = node;
                go_child->depth = node->depth + 1;
                go_child->active_eventualities = node->active_eventualities;
                // Add this eventuality to active set (postponed).
                go_child->active_eventualities.insert(eu_formula);
                go_child->zone = node->zone;
                go_child->active_timed = node->active_timed;

                go_child->committed_timed = node->committed_timed;

                node->children.push_back(stop_child);
                node->children.push_back(go_child);
                node->kind = TableauNodeKind::OR;

                return true;
            }
        }

        // ── (6) AU-RULE (A Until, branching) ────────────────────────────
        // If A(φ U ψ) ∈ Γ:
        //   Let a = A(φ U ψ)
        //   Branch:
        //     STOP: (Γ \ {a}) ∪ {ψ}         — eventuality fulfilled
        //     GO:   (Γ \ {a}) ∪ {φ, AX a}   — postpone eventuality
        {
            FormulaId au_formula = kInvalidId;
            for (FormulaId id : node->gamma.elements()) {
                const FormulaNode& n = factory_.node(id);
                if (n.kind == NodeKind::AU) {
                    au_formula = id;
                    break;
                }
            }

            if (au_formula != kInvalidId) {
                const FormulaNode& n = factory_.node(au_formula);
                FormulaId phi = n.children[0];
                FormulaId psi = n.children[1];

                FormulaSet base_gamma;
                for (FormulaId id : node->gamma.elements()) {
                    if (id != au_formula) {
                        base_gamma.insert(id);
                    }
                }

                // STOP child: ψ (fulfilled)
                TableauNode* stop_child = alloc_node();
                stop_child->gamma = base_gamma;
                stop_child->gamma.insert(psi);
                stop_child->ctx = node->ctx;
                stop_child->parent = node;
                stop_child->depth = node->depth + 1;
                stop_child->active_eventualities = node->active_eventualities;
                stop_child->active_eventualities.erase(au_formula);
                stop_child->zone = node->zone;
                stop_child->active_timed = node->active_timed;

                stop_child->committed_timed = node->committed_timed;

                // GO child: φ, AX a (postpone via AX)
                TableauNode* go_child = alloc_node();
                go_child->gamma = base_gamma;
                go_child->gamma.insert(phi);
                go_child->gamma.insert(factory_.make_ax(au_formula));
                go_child->ctx = node->ctx;
                go_child->parent = node;
                go_child->depth = node->depth + 1;
                go_child->active_eventualities = node->active_eventualities;
                go_child->active_eventualities.insert(au_formula);
                go_child->zone = node->zone;
                go_child->active_timed = node->active_timed;

                go_child->committed_timed = node->committed_timed;

                node->children.push_back(stop_child);
                node->children.push_back(go_child);
                node->kind = TableauNodeKind::OR;

                return true;
            }
        }

        // ── (6b) ER-RULE (Existential Release, branching, greatest fixpoint) ──
        // If E(φ R ψ) ∈ Γ:
        //   E(φ R ψ) ≡ ψ ∧ (φ ∨ EX E(φ R ψ))
        //   Branch 1: (Γ \ {er}) ∪ {ψ, φ}           — release now
        //   Branch 2: (Γ \ {er}) ∪ {ψ, EX E(φ R ψ)} — persist
        //   No eventuality tracking (greatest fixpoint).
        {
            FormulaId er_formula = kInvalidId;
            for (FormulaId id : node->gamma.elements()) {
                const FormulaNode& n = factory_.node(id);
                if (n.kind == NodeKind::ER) {
                    er_formula = id;
                    break;
                }
            }

            if (er_formula != kInvalidId) {
                const FormulaNode& n = factory_.node(er_formula);
                FormulaId phi = n.children[0];
                FormulaId psi = n.children[1];

                FormulaSet base_gamma;
                for (FormulaId id : node->gamma.elements()) {
                    if (id != er_formula) {
                        base_gamma.insert(id);
                    }
                }

                // Branch 1 (RELEASE): ψ ∧ φ
                TableauNode* release_child = alloc_node();
                release_child->gamma = base_gamma;
                release_child->gamma.insert(psi);
                release_child->gamma.insert(phi);
                release_child->ctx = node->ctx;
                release_child->parent = node;
                release_child->depth = node->depth + 1;
                release_child->active_eventualities = node->active_eventualities;
                release_child->zone = node->zone;
                release_child->active_timed = node->active_timed;

                release_child->committed_timed = node->committed_timed;

                // Branch 2 (PERSIST): ψ ∧ EX E(φ R ψ)
                TableauNode* persist_child = alloc_node();
                persist_child->gamma = base_gamma;
                persist_child->gamma.insert(psi);
                persist_child->gamma.insert(factory_.make_ex(er_formula));
                persist_child->ctx = node->ctx;
                persist_child->parent = node;
                persist_child->depth = node->depth + 1;
                persist_child->active_eventualities = node->active_eventualities;
                persist_child->zone = node->zone;
                persist_child->active_timed = node->active_timed;

                persist_child->committed_timed = node->committed_timed;

                node->children.push_back(release_child);
                node->children.push_back(persist_child);
                node->kind = TableauNodeKind::OR;

                return true;
            }
        }

        // ── (6c) AR-RULE (Universal Release, branching, greatest fixpoint) ──
        // If A(φ R ψ) ∈ Γ:
        //   A(φ R ψ) ≡ ψ ∧ (φ ∨ AX A(φ R ψ))
        //   Branch 1: (Γ \ {ar}) ∪ {ψ, φ}           — release now
        //   Branch 2: (Γ \ {ar}) ∪ {ψ, AX A(φ R ψ)} — persist
        //   No eventuality tracking (greatest fixpoint).
        {
            FormulaId ar_formula = kInvalidId;
            for (FormulaId id : node->gamma.elements()) {
                const FormulaNode& n = factory_.node(id);
                if (n.kind == NodeKind::AR) {
                    ar_formula = id;
                    break;
                }
            }

            if (ar_formula != kInvalidId) {
                const FormulaNode& n = factory_.node(ar_formula);
                FormulaId phi = n.children[0];
                FormulaId psi = n.children[1];

                FormulaSet base_gamma;
                for (FormulaId id : node->gamma.elements()) {
                    if (id != ar_formula) {
                        base_gamma.insert(id);
                    }
                }

                // Branch 1 (RELEASE): ψ ∧ φ
                TableauNode* release_child = alloc_node();
                release_child->gamma = base_gamma;
                release_child->gamma.insert(psi);
                release_child->gamma.insert(phi);
                release_child->ctx = node->ctx;
                release_child->parent = node;
                release_child->depth = node->depth + 1;
                release_child->active_eventualities = node->active_eventualities;
                release_child->zone = node->zone;
                release_child->active_timed = node->active_timed;

                release_child->committed_timed = node->committed_timed;

                // Branch 2 (PERSIST): ψ ∧ AX A(φ R ψ)
                TableauNode* persist_child = alloc_node();
                persist_child->gamma = base_gamma;
                persist_child->gamma.insert(psi);
                persist_child->gamma.insert(factory_.make_ax(ar_formula));
                persist_child->ctx = node->ctx;
                persist_child->parent = node;
                persist_child->depth = node->depth + 1;
                persist_child->active_eventualities = node->active_eventualities;
                persist_child->zone = node->zone;
                persist_child->active_timed = node->active_timed;

                persist_child->committed_timed = node->committed_timed;

                node->children.push_back(release_child);
                node->children.push_back(persist_child);
                node->kind = TableauNodeKind::OR;

                return true;
            }
        }

        // ── (7) TIMED EU-RULE (Timed E Until, branching) ────────────────
        // If E(φ U_I ψ) ∈ Γ (TimedEU):
        //   SAT branch: (Γ \ {ξ}) ∪ {ψ}, zone ∩ (clock ∈ I), deactivate ξ
        //   CONT branch: (Γ \ {ξ}) ∪ {φ, EX ξ}, keep ξ active
        {
            FormulaId teu_formula = kInvalidId;
            for (FormulaId id : node->gamma.elements()) {
                const FormulaNode& n = factory_.node(id);
                if (n.kind == NodeKind::TimedEU) {
                    teu_formula = id;
                    break;
                }
            }

            if (teu_formula != kInvalidId) {
                const FormulaNode& n = factory_.node(teu_formula);
                FormulaId phi = n.children[0];
                FormulaId psi = n.children[1];

                FormulaSet base_gamma;
                for (FormulaId id : node->gamma.elements()) {
                    if (id != teu_formula) {
                        base_gamma.insert(id);
                    }
                }

                auto clock_it = clock_of_.find(teu_formula);

                // SAT child: ψ, zone ∩ (clock ∈ I)
                TableauNode* sat_child = alloc_node();
                sat_child->gamma = base_gamma;
                sat_child->gamma.insert(psi);
                sat_child->ctx = node->ctx;
                sat_child->parent = node;
                sat_child->depth = node->depth + 1;
                sat_child->active_eventualities = node->active_eventualities;
                sat_child->active_eventualities.erase(teu_formula);
                sat_child->zone = node->zone;
                sat_child->active_timed = node->active_timed;

                sat_child->committed_timed = node->committed_timed;
                sat_child->active_timed.erase(teu_formula);

                // Apply interval constraints to SAT child's zone
                if (clock_it != clock_of_.end()) {
                    bool feasible = apply_interval(sat_child->zone, clock_it->second,
                                                    n.time_lower, n.time_upper);
                    if (!feasible) {
                        // SAT branch infeasible, but we still create it
                        // (it will be closed by the zone emptiness check)
                    }
                }

                // CONT child: φ, EX ξ, keep ξ active
                TableauNode* cont_child = alloc_node();
                cont_child->gamma = base_gamma;
                cont_child->gamma.insert(phi);
                cont_child->gamma.insert(factory_.make_ex(teu_formula));
                cont_child->ctx = node->ctx;
                cont_child->parent = node;
                cont_child->depth = node->depth + 1;
                cont_child->active_eventualities = node->active_eventualities;
                cont_child->active_eventualities.insert(teu_formula);
                cont_child->zone = node->zone;
                cont_child->active_timed = node->active_timed;

                cont_child->committed_timed = node->committed_timed;
                // ξ stays active

                node->children.push_back(sat_child);
                node->children.push_back(cont_child);
                node->kind = TableauNodeKind::OR;

                return true;
            }
        }

        // ── (8) TIMED AU-RULE (Timed A Until, branching) ────────────────
        // If A(φ U_I ψ) ∈ Γ (TimedAU):
        //   SAT branch: (Γ \ {ξ}) ∪ {ψ}, zone ∩ (clock ∈ I), deactivate ξ
        //   CONT branch: (Γ \ {ξ}) ∪ {φ, AX ξ}, keep ξ active
        {
            FormulaId tau_formula = kInvalidId;
            for (FormulaId id : node->gamma.elements()) {
                const FormulaNode& n = factory_.node(id);
                if (n.kind == NodeKind::TimedAU) {
                    tau_formula = id;
                    break;
                }
            }

            if (tau_formula != kInvalidId) {
                const FormulaNode& n = factory_.node(tau_formula);
                FormulaId phi = n.children[0];
                FormulaId psi = n.children[1];

                FormulaSet base_gamma;
                for (FormulaId id : node->gamma.elements()) {
                    if (id != tau_formula) {
                        base_gamma.insert(id);
                    }
                }

                auto clock_it = clock_of_.find(tau_formula);

                // SAT child: ψ, zone ∩ (clock ∈ I)
                TableauNode* sat_child = alloc_node();
                sat_child->gamma = base_gamma;
                sat_child->gamma.insert(psi);
                sat_child->ctx = node->ctx;
                sat_child->parent = node;
                sat_child->depth = node->depth + 1;
                sat_child->active_eventualities = node->active_eventualities;
                sat_child->active_eventualities.erase(tau_formula);
                sat_child->zone = node->zone;
                sat_child->active_timed = node->active_timed;

                sat_child->committed_timed = node->committed_timed;
                sat_child->active_timed.erase(tau_formula);

                if (clock_it != clock_of_.end()) {
                    apply_interval(sat_child->zone, clock_it->second,
                                   n.time_lower, n.time_upper);
                }

                // CONT child: φ, AX ξ, keep ξ active
                TableauNode* cont_child = alloc_node();
                cont_child->gamma = base_gamma;
                cont_child->gamma.insert(phi);
                cont_child->gamma.insert(factory_.make_ax(tau_formula));
                cont_child->ctx = node->ctx;
                cont_child->parent = node;
                cont_child->depth = node->depth + 1;
                cont_child->active_eventualities = node->active_eventualities;
                cont_child->active_eventualities.insert(tau_formula);
                cont_child->zone = node->zone;
                cont_child->active_timed = node->active_timed;

                cont_child->committed_timed = node->committed_timed;

                node->children.push_back(sat_child);
                node->children.push_back(cont_child);
                node->kind = TableauNodeKind::OR;

                return true;
            }
        }

        // ── (8c) TIMED AR-RULE: A(φ R_I ψ) — zone-splitting ────────────────────
        // A(φ R_I ψ) = ¬E(¬φ U_I ¬ψ): ψ must hold throughout I on all paths;
        // the obligation is released when φ also holds, or lifted after I.
        //
        //   POST: drop TimedAR (past interval, obligation lifted)
        //   PRE:  {AX TimedAR}            (before interval, propagate universally)
        //   IN-ESCAPE: {φ, ψ}             (Release triggered: φ ∧ ψ, drop obligation)
        //   IN-FORBID: {ψ, AX TimedAR}   (ψ required, continue universally)
        {
            FormulaId timed_ar = kInvalidId;
            for (FormulaId id : node->gamma.elements()) {
                const FormulaNode& n = factory_.node(id);
                if (n.kind == NodeKind::TimedAR) {
                    timed_ar = id;
                    break;
                }
            }

            if (timed_ar != kInvalidId) {
                const FormulaNode& ar_node = factory_.node(timed_ar);
                FormulaId phi = ar_node.children[0];   // release trigger
                FormulaId psi = ar_node.children[1];   // safety invariant
                const TimeBound& lower = ar_node.time_lower;
                const TimeBound& upper = ar_node.time_upper;

                auto clock_it = clock_of_.find(timed_ar);
                ClockId clk = (clock_it != clock_of_.end()) ? clock_it->second : 0;

                FormulaSet base_gamma;
                for (FormulaId id : node->gamma.elements()) {
                    if (id != timed_ar) base_gamma.insert(id);
                }

                // Zone splits
                Zone z_pre = node->zone;
                if (lower.is_strict) {
                    z_pre.add_upper_bound(clk, static_cast<std::int32_t>(lower.value), false);
                } else {
                    z_pre.add_upper_bound(clk, static_cast<std::int32_t>(lower.value), true);
                }
                bool pre_ok = !z_pre.is_empty();

                Zone z_in = node->zone;
                z_in.add_lower_bound(clk, static_cast<std::int32_t>(lower.value), lower.is_strict);
                if (!upper.is_infinity) {
                    z_in.add_upper_bound(clk, static_cast<std::int32_t>(upper.value), upper.is_strict);
                }
                bool in_ok = !z_in.is_empty();

                Zone z_post;
                bool post_ok = false;
                if (!upper.is_infinity) {
                    z_post = node->zone;
                    if (upper.is_strict) {
                        z_post.add_lower_bound(clk, static_cast<std::int32_t>(upper.value), false);
                    } else {
                        z_post.add_lower_bound(clk, static_cast<std::int32_t>(upper.value), true);
                    }
                    post_ok = !z_post.is_empty();
                }

                node->kind = TableauNodeKind::OR;

                // Suppress POST when the formula has not yet been through
                // IN-FORBID (where ψ was verified).  If z_in is non-empty
                // and the formula is uncommitted, POST would bypass the
                // safety invariant.
                bool committed = node->committed_timed.count(timed_ar) > 0;
                bool suppress_post = in_ok && !committed;

                // POST: drop TimedAR (obligation lifted past interval)
                if (post_ok && !suppress_post) {
                    TableauNode* c = alloc_node();
                    c->gamma = base_gamma;
                    c->ctx = node->ctx;
                    c->parent = node;
                    c->depth = node->depth + 1;
                    c->active_eventualities = node->active_eventualities;
                    c->zone = z_post;
                    c->active_timed = node->active_timed;
                    c->committed_timed = node->committed_timed;
                    c->active_timed.erase(timed_ar);
                    c->committed_timed.erase(timed_ar);
                    node->children.push_back(c);
                }

                // PRE: AX TimedAR (universal: every successor must maintain it)
                if (pre_ok) {
                    TableauNode* c = alloc_node();
                    c->gamma = base_gamma;
                    c->gamma.insert(factory_.make_ax(timed_ar));
                    c->ctx = node->ctx;
                    c->parent = node;
                    c->depth = node->depth + 1;
                    c->active_eventualities = node->active_eventualities;
                    c->zone = z_pre;
                    c->active_timed = node->active_timed;
                    c->committed_timed = node->committed_timed;
                    node->children.push_back(c);
                }

                // IN children
                if (in_ok) {
                    // ESCAPE-IN: {φ, ψ} — Release triggered, drop obligation
                    TableauNode* esc = alloc_node();
                    esc->gamma = base_gamma;
                    esc->gamma.insert(phi);
                    esc->gamma.insert(psi);
                    esc->ctx = node->ctx;
                    esc->parent = node;
                    esc->depth = node->depth + 1;
                    esc->active_eventualities = node->active_eventualities;
                    esc->zone = z_in;
                    esc->active_timed = node->active_timed;
                    esc->committed_timed = node->committed_timed;
                    esc->active_timed.erase(timed_ar);
                    esc->committed_timed.erase(timed_ar);
                    node->children.push_back(esc);

                    // FORBID-IN: {ψ, AX TimedAR} — ψ required, continue universally
                    TableauNode* fbd = alloc_node();
                    fbd->gamma = base_gamma;
                    fbd->gamma.insert(psi);
                    fbd->gamma.insert(factory_.make_ax(timed_ar));
                    fbd->ctx = node->ctx;
                    fbd->parent = node;
                    fbd->depth = node->depth + 1;
                    fbd->active_eventualities = node->active_eventualities;
                    fbd->zone = z_in;
                    fbd->active_timed = node->active_timed;
                    fbd->committed_timed = node->committed_timed;
                    fbd->committed_timed.insert(timed_ar);  // mark committed
                    node->children.push_back(fbd);
                }

                if (node->children.empty()) {
                    return false;  // All zones empty → close
                }
                return true;
            }
        }

        // ── (9c) TIMED ER-RULE: E(φ R_I ψ) — zone-splitting ────────────────────
        // E(φ R_I ψ) = ¬A(¬φ U_I ¬ψ): ψ must hold on some existential path through I;
        // the obligation is released when φ also holds, or lifted after I.
        //
        //   POST: drop TimedER (past interval, obligation lifted)
        //   PRE:  {EX TimedER}            (before interval, propagate existentially)
        //   IN-ESCAPE: {φ, ψ}             (Release triggered: φ ∧ ψ, drop obligation)
        //   IN-FORBID: {ψ, EX TimedER}   (ψ required on some path, continue)
        {
            FormulaId timed_er = kInvalidId;
            for (FormulaId id : node->gamma.elements()) {
                const FormulaNode& n = factory_.node(id);
                if (n.kind == NodeKind::TimedER) {
                    timed_er = id;
                    break;
                }
            }

            if (timed_er != kInvalidId) {
                const FormulaNode& er_node = factory_.node(timed_er);
                FormulaId phi = er_node.children[0];   // release trigger
                FormulaId psi = er_node.children[1];   // safety invariant
                const TimeBound& lower = er_node.time_lower;
                const TimeBound& upper = er_node.time_upper;

                auto clock_it = clock_of_.find(timed_er);
                ClockId clk = (clock_it != clock_of_.end()) ? clock_it->second : 0;

                FormulaSet base_gamma;
                for (FormulaId id : node->gamma.elements()) {
                    if (id != timed_er) base_gamma.insert(id);
                }

                // Zone splits
                Zone z_pre = node->zone;
                if (lower.is_strict) {
                    z_pre.add_upper_bound(clk, static_cast<std::int32_t>(lower.value), false);
                } else {
                    z_pre.add_upper_bound(clk, static_cast<std::int32_t>(lower.value), true);
                }
                bool pre_ok = !z_pre.is_empty();

                Zone z_in = node->zone;
                z_in.add_lower_bound(clk, static_cast<std::int32_t>(lower.value), lower.is_strict);
                if (!upper.is_infinity) {
                    z_in.add_upper_bound(clk, static_cast<std::int32_t>(upper.value), upper.is_strict);
                }
                bool in_ok = !z_in.is_empty();

                Zone z_post;
                bool post_ok = false;
                if (!upper.is_infinity) {
                    z_post = node->zone;
                    if (upper.is_strict) {
                        z_post.add_lower_bound(clk, static_cast<std::int32_t>(upper.value), false);
                    } else {
                        z_post.add_lower_bound(clk, static_cast<std::int32_t>(upper.value), true);
                    }
                    post_ok = !z_post.is_empty();
                }

                node->kind = TableauNodeKind::OR;

                // Suppress POST when the formula has not yet been through
                // IN-FORBID (where ψ was verified).
                bool committed = node->committed_timed.count(timed_er) > 0;
                bool suppress_post = in_ok && !committed;

                // POST: drop TimedER (obligation lifted past interval)
                if (post_ok && !suppress_post) {
                    TableauNode* c = alloc_node();
                    c->gamma = base_gamma;
                    c->ctx = node->ctx;
                    c->parent = node;
                    c->depth = node->depth + 1;
                    c->active_eventualities = node->active_eventualities;
                    c->zone = z_post;
                    c->active_timed = node->active_timed;
                    c->committed_timed = node->committed_timed;
                    c->active_timed.erase(timed_er);
                    c->committed_timed.erase(timed_er);
                    node->children.push_back(c);
                }

                // PRE: EX TimedER (existential: some successor must maintain it)
                if (pre_ok) {
                    TableauNode* c = alloc_node();
                    c->gamma = base_gamma;
                    c->gamma.insert(factory_.make_ex(timed_er));
                    c->ctx = node->ctx;
                    c->parent = node;
                    c->depth = node->depth + 1;
                    c->active_eventualities = node->active_eventualities;
                    c->zone = z_pre;
                    c->active_timed = node->active_timed;
                    c->committed_timed = node->committed_timed;
                    node->children.push_back(c);
                }

                // IN children
                if (in_ok) {
                    // ESCAPE-IN: {φ, ψ} — Release triggered, drop obligation
                    TableauNode* esc = alloc_node();
                    esc->gamma = base_gamma;
                    esc->gamma.insert(phi);
                    esc->gamma.insert(psi);
                    esc->ctx = node->ctx;
                    esc->parent = node;
                    esc->depth = node->depth + 1;
                    esc->active_eventualities = node->active_eventualities;
                    esc->zone = z_in;
                    esc->active_timed = node->active_timed;
                    esc->committed_timed = node->committed_timed;
                    esc->active_timed.erase(timed_er);
                    esc->committed_timed.erase(timed_er);
                    node->children.push_back(esc);

                    // FORBID-IN: {ψ, EX TimedER} — ψ required, continue existentially
                    TableauNode* fbd = alloc_node();
                    fbd->gamma = base_gamma;
                    fbd->gamma.insert(psi);
                    fbd->gamma.insert(factory_.make_ex(timed_er));
                    fbd->ctx = node->ctx;
                    fbd->parent = node;
                    fbd->depth = node->depth + 1;
                    fbd->active_eventualities = node->active_eventualities;
                    fbd->zone = z_in;
                    fbd->active_timed = node->active_timed;
                    fbd->committed_timed = node->committed_timed;
                    fbd->committed_timed.insert(timed_er);  // mark committed
                    node->children.push_back(fbd);
                }

                if (node->children.empty()) {
                    return false;  // All zones empty → close
                }
                return true;
            }
        }

        // ¬E(φ U ψ) and ¬A(φ U ψ) appear as Not(EU) and Not(AU) in NNF.
        // These require special handling in tctl tableaux.
        //
        // ¬E(φ U ψ) ≡ A(¬ψ W (¬φ ∧ ¬ψ)) ≡ AG ¬ψ ∨ A(¬ψ U (¬φ ∧ ¬ψ))
        // ¬A(φ U ψ) ≡ E(¬ψ W (¬φ ∧ ¬ψ)) ≡ EG ¬ψ ∨ E(¬ψ U (¬φ ∧ ¬ψ))
        //
        // For simplicity in the one-pass tableau, we expand these using
        // the weak-until equivalence. However, since we don't have W
        // directly, we expand as follows:
        //
        // ¬E(φ U ψ): Either ψ is false now (and we continue with ¬φ∨¬ψ, AX ¬EU),
        //            or ψ and φ are both false and we're done.
        //
        // Following the paper's approach, we handle ¬EU and ¬AU by expanding:
        // ¬E(φ U ψ) branches to:
        //   (¬ψ ∧ ¬φ) - safe stopping point
        //   (¬ψ ∧ AX ¬E(φ U ψ)) - continue avoiding EU
        {
            FormulaId not_eu = kInvalidId;
            for (FormulaId id : node->gamma.elements()) {
                const FormulaNode& n = factory_.node(id);
                if (n.kind == NodeKind::Not) {
                    const FormulaNode& inner = factory_.node(n.children[0]);
                    if (inner.kind == NodeKind::EU) {
                        not_eu = id;
                        break;
                    }
                }
            }

            if (not_eu != kInvalidId) {
                const FormulaNode& not_node = factory_.node(not_eu);
                FormulaId eu_inside = not_node.children[0];
                const FormulaNode& eu_node = factory_.node(eu_inside);
                FormulaId phi = eu_node.children[0];
                FormulaId psi = eu_node.children[1];

                // ¬E(φ U ψ) expands to:
                //   STOP: ¬ψ ∧ ¬φ  (both false, safe)
                //   GO:   ¬ψ ∧ AX ¬E(φ U ψ) (continue avoiding)

                FormulaId neg_phi = get_negation(phi);
                FormulaId neg_psi = get_negation(psi);

                FormulaSet base_gamma;
                for (FormulaId id : node->gamma.elements()) {
                    if (id != not_eu) {
                        base_gamma.insert(id);
                    }
                }

                // STOP: ¬ψ ∧ ¬φ
                TableauNode* stop_child = alloc_node();
                stop_child->gamma = base_gamma;
                stop_child->gamma.insert(neg_psi);
                stop_child->gamma.insert(neg_phi);
                stop_child->ctx = node->ctx;
                stop_child->parent = node;
                stop_child->depth = node->depth + 1;
                stop_child->active_eventualities = node->active_eventualities;
                stop_child->zone = node->zone;
                stop_child->active_timed = node->active_timed;

                stop_child->committed_timed = node->committed_timed;

                // GO: ¬ψ ∧ AX ¬E(φ U ψ)
                TableauNode* go_child = alloc_node();
                go_child->gamma = base_gamma;
                go_child->gamma.insert(neg_psi);
                go_child->gamma.insert(factory_.make_ax(not_eu));
                go_child->ctx = node->ctx;
                go_child->parent = node;
                go_child->depth = node->depth + 1;
                go_child->active_eventualities = node->active_eventualities;
                go_child->zone = node->zone;
                go_child->active_timed = node->active_timed;

                go_child->committed_timed = node->committed_timed;

                node->children.push_back(stop_child);
                node->children.push_back(go_child);
                node->kind = TableauNodeKind::OR;

                return true;
            }
        }

        // Handle ¬A(φ U ψ)
        {
            FormulaId not_au = kInvalidId;
            for (FormulaId id : node->gamma.elements()) {
                const FormulaNode& n = factory_.node(id);
                if (n.kind == NodeKind::Not) {
                    const FormulaNode& inner = factory_.node(n.children[0]);
                    if (inner.kind == NodeKind::AU) {
                        not_au = id;
                        break;
                    }
                }
            }

            if (not_au != kInvalidId) {
                const FormulaNode& not_node = factory_.node(not_au);
                FormulaId au_inside = not_node.children[0];
                const FormulaNode& au_node = factory_.node(au_inside);
                FormulaId phi = au_node.children[0];
                FormulaId psi = au_node.children[1];

                // ¬A(φ U ψ) ≡ E(¬ψ W (¬φ ∧ ¬ψ))
                // Expands to:
                //   STOP: ¬ψ ∧ ¬φ
                //   GO:   ¬ψ ∧ EX ¬A(φ U ψ)

                FormulaId neg_phi = get_negation(phi);
                FormulaId neg_psi = get_negation(psi);

                FormulaSet base_gamma;
                for (FormulaId id : node->gamma.elements()) {
                    if (id != not_au) {
                        base_gamma.insert(id);
                    }
                }

                // STOP: ¬ψ ∧ ¬φ
                TableauNode* stop_child = alloc_node();
                stop_child->gamma = base_gamma;
                stop_child->gamma.insert(neg_psi);
                stop_child->gamma.insert(neg_phi);
                stop_child->ctx = node->ctx;
                stop_child->parent = node;
                stop_child->depth = node->depth + 1;
                stop_child->active_eventualities = node->active_eventualities;
                stop_child->zone = node->zone;
                stop_child->active_timed = node->active_timed;

                stop_child->committed_timed = node->committed_timed;

                // GO: ¬ψ ∧ EX ¬A(φ U ψ)
                TableauNode* go_child = alloc_node();
                go_child->gamma = base_gamma;
                go_child->gamma.insert(neg_psi);
                go_child->gamma.insert(factory_.make_ex(not_au));
                go_child->ctx = node->ctx;
                go_child->parent = node;
                go_child->depth = node->depth + 1;
                go_child->active_eventualities = node->active_eventualities;
                go_child->zone = node->zone;
                go_child->active_timed = node->active_timed;

                go_child->committed_timed = node->committed_timed;

                node->children.push_back(stop_child);
                node->children.push_back(go_child);
                node->kind = TableauNodeKind::OR;

                return true;
            }
        }
    }

    // Node is saturated (no more rules apply).

    // ── TCTL zone-based closure checks after saturation ─────────────────
    if (num_clocks_ > 1) {
        // Check zone emptiness
        if (node->zone.is_empty()) {
            return false;
        }
        // Check deadline feasibility for all active timed obligations
        if (!check_deadline_feasibility(node->zone, node->active_timed)) {
            return false;
        }
    }

    return true;
}

// ============================================================================
// has_contradiction() — Check for propositional and arithmetic contradictions
// ============================================================================
//
// Rule (0): Close if:
//   - false ∈ Γ, OR
//   - p and !p both ∈ Γ for some atom p, OR
//   - The arithmetic constraints in Γ are unsatisfiable (Z3 check).
//
// Arithmetic constraints are state predicates with per-state valuations:
// - Each state assigns integer values to variables (x, y, z, ...)
// - Constraints are evaluated at individual states using that state's valuation
// - Different states can have different values for the same variable
// - We only check constraints in THIS node's gamma, not ancestors
//
// IMPLEMENTATION: Use Z3 to check consistency of all state constraints:
// - Boolean literals (atoms and negated atoms) -> Z3 boolean variables
// - Arithmetic constraints (x<=5, etc.) -> Z3 integer constraints
// - Temporal formulas (EX, EU, etc.) are IGNORED - they're not state predicates

bool TableauEngine::has_contradiction(TableauNode* node) {
    const FormulaSet& gamma = node->gamma;

    // First-class SMT check: encode the entire state-predicate fragment of Γ
    // (propositional + arithmetic, with full boolean structure) into Z3.
    // Temporal formulas are ignored here by design.
    Z3Checker z3_checker(factory_);
    bool has_state_predicates = false;

    for (FormulaId id : gamma.elements()) {
        has_state_predicates = z3_checker.add_state_formula(id) || has_state_predicates;
    }

    if (!has_state_predicates) {
        return false;
    }

    Z3Result result = z3_checker.check();
    return result == Z3Result::UNSAT;
}

// ============================================================================
// generate_successors() — Create successor nodes from EX formulas
// ============================================================================
//
// Rule (6) SUCCESSOR GENERATION:
//   After saturation (no more ∧, ∨, EU, AU, AX rules apply):
//   - Collect all EX φ in Γ.
//   - Let U = context.nextAll (universal obligations).
//   - For each EX φ: create successor with Γ_successor = {φ} ∪ U.
//   - If no EX and U is non-empty: create one successor with Γ_successor = U.
//   - If no EX and U is empty: no successors needed (leaf).
//
// Rule (7) TOTALITY:
//   Models are total, so every state needs at least one successor.
//   If we have no EX formulas but we have context obligations, we propagate them.
//   If we have neither, we're at a leaf (no temporal obligations).

void TableauEngine::generate_successors(TableauNode* node) {
    // If node already has children (from branching rules), don't generate more.
    if (!node->children.empty()) {
        return;
    }

    // Collect all EX formulas.
    std::vector<FormulaId> ex_formulas;
    for (FormulaId id : node->gamma.elements()) {
        const FormulaNode& n = factory_.node(id);
        if (n.kind == NodeKind::EX) {
            ex_formulas.push_back(id);
        }
    }

    // Get universal obligations from context.
    const std::vector<FormulaId>& universal = node->ctx.nextAll;

    // ── TCTL: Generate delay successor if we have timed obligations ─────
    // Delay successor: zone' = zone.up(), Γ/ctx/activeTimed unchanged.
    // Guard: after up(), all active finite-upper deadlines must remain feasible.
    bool has_timed = (num_clocks_ > 1 && !node->active_timed.empty());

    if (has_timed) {
        Zone delayed_zone = node->zone;
        delayed_zone.up();

        // Check that delay doesn't violate any upper deadlines
        bool delay_ok = !delayed_zone.is_empty() &&
                        check_deadline_feasibility(delayed_zone, node->active_timed);

        // ── Constrain delay for timed release (TimedAR / TimedER) ────────
        // A(φ R_I ψ) or E(φ R_I ψ): ψ is the safety invariant that must
        // hold throughout I.  If ψ does not hold at the current state
        // (either ψ is the constant False, or ¬ψ ∈ Γ), the delay must
        // NOT advance the clock into the interval, because otherwise
        // the path would pass through I without enforcing ψ.
        //
        // Constraint: keep clock before interval start:
        //   I = (a, …)  → clock ≤ a
        //   I = [a, …)  → clock < a
        if (delay_ok) {
            for (FormulaId fid : node->active_timed) {
                const FormulaNode& fn = factory_.node(fid);
                if (fn.kind != NodeKind::TimedAR &&
                    fn.kind != NodeKind::TimedER) continue;

                FormulaId psi = fn.children[1];   // safety invariant
                const FormulaNode& psi_fn = factory_.node(psi);

                // Check if ψ does NOT hold at this state:
                //   (a) ψ is the constant False, or
                //   (b) ¬ψ ∈ Γ
                bool psi_violated = (psi_fn.kind == NodeKind::False);
                if (!psi_violated) {
                    FormulaId neg_psi = get_negation(psi);
                    psi_violated = node->gamma.contains(neg_psi);
                }
                if (!psi_violated) continue;

                auto cit = clock_of_.find(fid);
                if (cit == clock_of_.end()) continue;
                ClockId clk = cit->second;

                const TimeBound& lower = fn.time_lower;
                if (lower.is_strict) {
                    // (a, …) → keep clock ≤ a
                    delayed_zone.add_upper_bound(
                        clk, static_cast<std::int32_t>(lower.value), false);
                } else {
                    // [a, …) → keep clock < a
                    delayed_zone.add_upper_bound(
                        clk, static_cast<std::int32_t>(lower.value), true);
                }

                if (delayed_zone.is_empty()) {
                    delay_ok = false;
                    break;
                }
            }
        }

        if (delay_ok) {
            // Create a delay successor with the same Γ, ctx, activeTimed
            TableauNode* delay_succ = alloc_node();
            delay_succ->gamma = node->gamma;
            delay_succ->ctx = node->ctx;
            delay_succ->parent = node;
            delay_succ->depth = node->depth + 1;
            delay_succ->active_eventualities = node->active_eventualities;
            delay_succ->zone = delayed_zone;
            delay_succ->active_timed = node->active_timed;

            delay_succ->committed_timed = node->committed_timed;
            delay_succ->is_delay_successor = true;
            
            node->children.push_back(delay_succ);
        }
    }

    if (ex_formulas.empty() && universal.empty()) {
        // No temporal successors needed (beyond possible delay above).
        if (node->children.empty()) {
            // leaf: no delay and no successors
            return;
        }
        // Only has delay successor — OR-choose delay vs nothing
        node->kind = TableauNodeKind::OR;
        return;
    }

    if (ex_formulas.empty()) {
        // No existential requirements, but we have universal obligations.
        // Create one successor (stutter) with just the universal obligations.
        TableauNode* succ = alloc_node();
        for (FormulaId id : universal) {
            succ->gamma.insert(id);
        }
        succ->ctx = Context{};  // Fresh context for successor.
        succ->parent = node;
        succ->depth = node->depth + 1;
        succ->active_eventualities = node->active_eventualities;
        succ->zone = node->zone;  // Zone unchanged on discrete step
        succ->active_eventualities = node->active_eventualities;
        //succ->active_timed = node->active_timed;
        // Clean active_timed: keep if formula or its negation is in Γ
        for (FormulaId at : node->active_timed) {
            if (succ->gamma.contains(at) ||
                succ->gamma.contains(factory_.make_not(at))) {
                succ->active_timed.insert(at);
                // Propagate committed status for kept formulas
                if (node->committed_timed.count(at) > 0) {
                    succ->committed_timed.insert(at);
                }
            }
        }
                

        node->children.push_back(succ);

        if (has_timed && node->children.size() > 1) {
            // OR-choose between delay and discrete step
            node->kind = TableauNodeKind::OR;
        } else {
            node->kind = TableauNodeKind::AND;
        }
    } else {
        // We have EX formulas. Create one successor per EX formula.
        for (FormulaId ex_id : ex_formulas) {
            const FormulaNode& ex_node = factory_.node(ex_id);
            FormulaId phi = ex_node.children[0];

            TableauNode* succ = alloc_node();
            succ->gamma.insert(phi);
            for (FormulaId u : universal) {
                succ->gamma.insert(u);
            }
            succ->ctx = Context{};  // Fresh context.
            succ->parent = node;
            succ->depth = node->depth + 1;
            succ->zone = node->zone;  // Zone unchanged on discrete step
            
            //succ->active_timed = node->active_timed;
            succ->active_eventualities = node->active_eventualities;
            // Clean active_timed: keep if formula or its negation is in Γ
            for (FormulaId at : node->active_timed) {
                if (succ->gamma.contains(at) ||
                    succ->gamma.contains(factory_.make_not(at))) {
                    succ->active_timed.insert(at);
                    // Propagate committed status for kept formulas
                    if (node->committed_timed.count(at) > 0) {
                        succ->committed_timed.insert(at);
                    }
                }
            }
            node->children.push_back(succ);
        }

        if (has_timed && node->children.size() > ex_formulas.size()) {
            // We have both delay and discrete successors — OR among all
            node->kind = TableauNodeKind::OR;
        } else {
            node->kind = TableauNodeKind::AND;
        }
    }
}

// ============================================================================
// find_loop_ancestor() — Find an ancestor with matching (Γ, context)
// ============================================================================

TableauNode* TableauEngine::find_loop_ancestor(TableauNode* node,
                                                const BranchState& bs) {
    // Check if this (Γ, context, zone) configuration appears in the
    // branch-local ancestor chain.  Uses the same normalized zone key as
    // dfs() memoization — free inactive clocks and extrapolate active ones.
    std::string nz = compute_zone_key(node);
    NodeKey node_key{node->gamma, node->ctx, nz};

    for (TableauNode* ancestor : bs.stack) {
        if (ancestor == node) continue;

        std::string az = compute_zone_key(ancestor);
        NodeKey ancestor_key{ancestor->gamma, ancestor->ctx, az};
        if (node_key == ancestor_key) {
            return ancestor;
        }
    }
    return nullptr;
}

// ============================================================================
// check_eventuality_coverage() — Validate loop eventualities
// ============================================================================
//
// Rule (9) LOOP / EVENTUALITY CHECK:
// A loop is accepted ONLY if for every active eventuality E(φ U ψ) or A(φ U ψ)
// in the loop, ψ appears in Γ of some node along the loop path.
//
// Active eventualities are those In the "GO" branch (postponed).

bool TableauEngine::check_eventuality_coverage(TableauNode* loop_start,
                                                TableauNode* loop_end) {
    stats_.eventualities_checked.fetch_add(1, std::memory_order_relaxed);

    // Collect all nodes in the loop (from loop_start to loop_end).
    std::vector<TableauNode*> loop_nodes;
    TableauNode* curr = loop_end;
    while (curr != nullptr) {
        loop_nodes.push_back(curr);
        if (curr == loop_start) break;
        curr = curr->parent;
    }

    if (loop_nodes.empty()) {
        return true;  // No loop, accept.
    }

    // CRITICAL: If the loop doesn't actually form a cycle through the tree
    // (i.e., loop_start wasn't found in the parent chain), this is not a valid loop.
    if (loop_nodes.back() != loop_start) {
        // This can happen if we're comparing gammas across different branches.
        // Not a real ancestor loop - treat as unfulfillable.
        return false;
    }

    // Collect all active eventualities in the loop.
    // ONLY use active_eventualities tracking (maintained by EU/AU STOP/GO
    // branches).  Do NOT scan intermediate branching-node gammas for EU/AU
    // formulas: those gammas still contain the EU/AU that was expanded into
    // STOP/GO children, but non-branching rules (AND, AX) may have already
    // decomposed the goal formula ψ, making it impossible to find ψ in any
    // saturated gamma.  active_eventualities only includes eventualities
    // that were actually POSTPONED (GO branch), which is the correct set.
    std::set<FormulaId> all_eventualities;
    for (TableauNode* n : loop_nodes) {
        for (FormulaId ev : n->active_eventualities) {
            all_eventualities.insert(ev);
        }
    }

    // For each eventuality, check if it's fulfilled somewhere in the loop.
    for (FormulaId ev : all_eventualities) {
        bool fulfilled = false;
        for (TableauNode* n : loop_nodes) {
            const FormulaNode& ev_n = factory_.node(ev);
            if (ev_n.kind == NodeKind::TimedEU || ev_n.kind == NodeKind::TimedAU) {
                if (timed_eventuality_fulfilled(ev, n)) {
                    fulfilled = true;
                    break;
                }
            } else if (eventuality_fulfilled(ev, n->gamma)) {
                fulfilled = true;
                break;
            }
        }
        if (!fulfilled) {
            return false;  // Unfulfilled eventuality → bad loop.
        }
    }

    // ── Time-divergence (anti-Zeno) check ──────────────────────────────
    // For every timed safety formula (TimedAR/TimedER) — i.e., a timed
    // entry in active_timed that is NOT a positive eventuality goal — the
    // loop must include at least one node whose zone *guarantees* the
    // clock has reached the formula's lower bound.  A loop that stays
    // entirely in the PRE region (clock < lower) is a Zeno path and must
    // be rejected.
    {
        // All fids in active_timed across the loop.
        std::set<FormulaId> all_active_timed;
        for (TableauNode* n : loop_nodes)
            for (FormulaId fid : n->active_timed)
                all_active_timed.insert(fid);

        // Positive EU/AU goals are handled by timed_eventuality_fulfilled;
        // collect them so the Zeno check can skip them.
        std::set<FormulaId> positive_goals;
        for (TableauNode* n : loop_nodes)
            for (FormulaId fid : n->active_eventualities)
                positive_goals.insert(fid);

        for (FormulaId fid : all_active_timed) {
            if (positive_goals.count(fid)) continue;   // positive EU goal — skip

            const FormulaNode& tfn = factory_.node(fid);
            if (tfn.kind != NodeKind::TimedEU && tfn.kind != NodeKind::TimedAU &&
                tfn.kind != NodeKind::TimedER && tfn.kind != NodeKind::TimedAR)
                continue;

            const TimeBound& lower = tfn.time_lower;
            // lower = [0, …) is trivially reachable at time 0 — no Zeno concern.
            if (lower.value == 0 && !lower.is_strict) continue;

            auto cit = clock_of_.find(fid);
            if (cit == clock_of_.end()) continue;
            ClockId ck = cit->second;

            // Check if any loop node's zone GUARANTEES x_ck is in the interval.
            // get_bound(0, ck): bound on x_0 - x_ck <= d  →  x_ck >= -d.value
            bool committed = false;
            for (TableauNode* n : loop_nodes) {
                Bound lb = n->zone.get_bound(kReferenceClock, ck);
                if (lb.is_infinity()) continue;   // only x_ck >= 0: not committed

                std::int64_t gmin = -static_cast<std::int64_t>(lb.value);
                bool gstrict      = lb.is_strict;

                if (lower.is_strict) {
                    // need x_ck > lower.value
                    committed = (gmin > lower.value) ||
                                (gmin == lower.value && gstrict);
                } else {
                    // need x_ck >= lower.value
                    committed = (gmin > lower.value) || (gmin == lower.value);
                }
                if (committed) break;
            }

            if (!committed) {
                return false;  // Zeno loop: stays in PRE zone
            }
        }
    }

    return true;  // All eventualities fulfilled, no Zeno → good loop.
}

// ============================================================================
// collect_eventualities() — Find EU/AU formulas in a set
// ============================================================================

void TableauEngine::collect_eventualities(const FormulaSet& gamma,
                                           std::set<FormulaId>& eventualities) const {
    for (FormulaId id : gamma.elements()) {
        const FormulaNode& n = factory_.node(id);
        if (n.kind == NodeKind::EU || n.kind == NodeKind::AU ||
            n.kind == NodeKind::TimedEU || n.kind == NodeKind::TimedAU) {
            eventualities.insert(id);
        }
    }
}

// ============================================================================
// eventuality_fulfilled() — Check if ψ from E(φ U ψ) or A(φ U ψ) is in Γ
// ============================================================================

bool TableauEngine::eventuality_fulfilled(FormulaId eventuality,
                                           const FormulaSet& gamma) const {
    const FormulaNode& n = factory_.node(eventuality);

    if (n.kind == NodeKind::EU || n.kind == NodeKind::AU ||
        n.kind == NodeKind::TimedEU || n.kind == NodeKind::TimedAU) {
        FormulaId psi = n.children[1];  // The goal formula.
        return gamma.contains(psi);
    }

    return true;  // Not an eventuality, trivially fulfilled.
}

// ============================================================================
// get_negation() — Get the NNF negation of a formula
// ============================================================================

FormulaId TableauEngine::get_negation(FormulaId id) {
    const FormulaNode& n = factory_.node(id);

    switch (n.kind) {
        case NodeKind::True:
            return factory_.make_false();
        case NodeKind::False:
            return factory_.make_true();
        case NodeKind::Atom:
            return factory_.make_not(id);
        case NodeKind::Not:
            // !!φ = φ
            return n.children[0];
        
        // ── Arithmetic constraints: flip comparison operators ───────────
        case NodeKind::IntLessEq:
            return factory_.make_int_greater(n.children[0], n.children[1]);
        case NodeKind::IntLess:
            return factory_.make_int_greater_eq(n.children[0], n.children[1]);
        case NodeKind::IntGreaterEq:
            return factory_.make_int_less(n.children[0], n.children[1]);
        case NodeKind::IntGreater:
            return factory_.make_int_less_eq(n.children[0], n.children[1]);
        case NodeKind::IntEqual: {
            FormulaId less = factory_.make_int_less(n.children[0], n.children[1]);
            FormulaId greater = factory_.make_int_greater(n.children[0], n.children[1]);
            return factory_.make_or(less, greater);
        }
        
        // ── De Morgan's laws for And/Or ─────────────────────────────────
        // ¬(a ∧ b) = ¬a ∨ ¬b
        // ¬(a ∨ b) = ¬a ∧ ¬b
        // Push negation inward so that the resulting formula is in NNF and
        // can be decomposed by the And/Or expansion rules.
        case NodeKind::And:
            return factory_.make_or(get_negation(n.children[0]),
                                    get_negation(n.children[1]));
        case NodeKind::Or:
            return factory_.make_and(get_negation(n.children[0]),
                                     get_negation(n.children[1]));
        
        default:
            // For temporal formulas, wrap in Not.
            // The normalization phase should have already pushed negations
            // into the formula during NNF conversion.
            return factory_.make_not(id);
    }
}

// ============================================================================
// is_literal() / is_atom()
// ============================================================================

bool TableauEngine::is_literal(FormulaId id) const {
    const FormulaNode& n = factory_.node(id);
    if (n.kind == NodeKind::Atom) return true;
    if (n.kind == NodeKind::Not) {
        const FormulaNode& inner = factory_.node(n.children[0]);
        return inner.kind == NodeKind::Atom;
    }
    return false;
}

bool TableauEngine::is_atom(FormulaId id) const {
    return factory_.node(id).kind == NodeKind::Atom;
}

// ============================================================================
// extract_model_from_branch() — Build Kripke model from SAT branch
// ============================================================================

void TableauEngine::extract_model_from_branch(TableauNode* leaf) {
    // Ensure only one thread stores a model (first SAT branch wins).
    bool expected = false;
    if (!model_set_.compare_exchange_strong(expected, true,
                                            std::memory_order_acq_rel)) {
        return;  // Another thread already set the model.
    }

    // Collect the path from root to leaf.
    std::vector<TableauNode*> path;
    TableauNode* curr = leaf;
    while (curr != nullptr) {
        path.push_back(curr);
        curr = curr->parent;
    }
    std::reverse(path.begin(), path.end());

    // Build states from path nodes (simplified).
    KripkeModel model;
    std::map<TableauNode*, std::uint32_t> node_to_state;

    for (std::size_t i = 0; i < path.size(); ++i) {
        TableauNode* n = path[i];
        KripkeState state;
        state.id = static_cast<std::uint32_t>(i);

        // Collect positive atoms.
        for (FormulaId id : n->gamma.elements()) {
            if (is_atom(id)) {
                state.atoms.insert(factory_.node(id).atom_name);
            }
        }

        node_to_state[n] = state.id;
        model.states.push_back(std::move(state));
    }

    // Add transitions.
    for (std::size_t i = 0; i + 1 < path.size(); ++i) {
        model.states[i].successors.push_back(static_cast<std::uint32_t>(i + 1));
    }

    // Ensure totality: last state loops to itself.
    if (!model.states.empty()) {
        auto& last = model.states.back();
        if (last.successors.empty()) {
            last.successors.push_back(last.id);
        }
    }

    model.initial_state = 0;
    {
        std::lock_guard<std::mutex> lk(model_mutex_);
        model_ = std::move(model);
    }
}

// ============================================================================
// model_description() / stats()
// ============================================================================

std::string TableauEngine::model_description() const {
    if (model_.has_value()) {
        return model_->to_string();
    }
    return "(no model)";
}

std::string TableauEngine::stats() const {
    return stats_.to_string();
}

}  // namespace tctl
