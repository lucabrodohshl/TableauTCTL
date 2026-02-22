// ============================================================================
// parser.cpp — Recursive-descent tctl parser
// ============================================================================
//
// Implementation notes
// --------------------
//
// This parser consumes tokens from a Lexer and builds an AST via
// FormulaFactory.  The recursive-descent structure mirrors the grammar
// directly:
//
//   parse()           calls parse_iff()  and then expects Eof.
//   parse_iff()       handles  <->  (left-associative).
//   parse_implies()   handles  ->   (right-associative via recursion).
//   parse_or()        handles  |    (left-associative).
//   parse_and()       handles  &    (left-associative).
//   parse_unary()     handles  !, EX, AX, EF, AF, EG, AG  (prefix).
//   parse_primary()   handles  atoms, true, false, E(…U…), A(…U…), parens.
//
// All error messages follow the required format:
//   <line>: ERROR: <message> at column <n>
//
// ============================================================================

#include "tctl/parser.hpp"

#include <iostream>
#include <stdexcept>

namespace tctl {

// ── Constructor ─────────────────────────────────────────────────────────────

Parser::Parser(Lexer& lexer, FormulaFactory& factory)
    : lex_(lexer), fac_(factory) {}

// ── Error helpers ───────────────────────────────────────────────────────────

void Parser::error(const Token& tok, const std::string& msg) {
    throw std::runtime_error(
        std::to_string(tok.pos.line) + ": ERROR: " + msg +
        " at column " + std::to_string(tok.pos.column));
}

Token Parser::expect(TokenKind kind, const std::string& context) {
    Token t = lex_.next();
    if (t.kind != kind) {
        error(t, "expected " + std::string(token_kind_name(kind)) +
                 " " + context + ", got '" + t.text + "'");
    }
    return t;
}

// ── parse ───────────────────────────────────────────────────────────────────
// Entry point: parse one formula then require end-of-input.

FormulaId Parser::parse() {
    FormulaId f = parse_formula();
    const Token& t = lex_.peek();
    if (t.kind != TokenKind::Eof) {
        error(t, "unexpected token '" + t.text + "' after formula");
    }
    return f;
}

FormulaId Parser::parse_formula() {
    return parse_iff();
}

// ── parse_iff ───────────────────────────────────────────────────────────────
// iff_expr ::= impl_expr ( '<->' impl_expr )*
// Left-associative: a <-> b <-> c  =  (a <-> b) <-> c

FormulaId Parser::parse_iff() {
    FormulaId lhs = parse_implies();
    while (lex_.peek().kind == TokenKind::DoubleArrow) {
        lex_.next();  // consume '<->'
        FormulaId rhs = parse_implies();
        lhs = fac_.make_iff(lhs, rhs);
    }
    return lhs;
}

// ── parse_implies ───────────────────────────────────────────────────────────
// impl_expr ::= or_expr ( '->' impl_expr )?
// Right-associative: a -> b -> c  =  a -> (b -> c)
// Achieved by recursing on the right-hand side.

FormulaId Parser::parse_implies() {
    FormulaId lhs = parse_or();
    if (lex_.peek().kind == TokenKind::Arrow) {
        lex_.next();  // consume '->'
        // Right-associative: recurse into parse_implies (not parse_or).
        FormulaId rhs = parse_implies();
        return fac_.make_implies(lhs, rhs);
    }
    return lhs;
}

// ── parse_or ────────────────────────────────────────────────────────────────
// or_expr ::= and_expr ( '|' and_expr )*

FormulaId Parser::parse_or() {
    FormulaId lhs = parse_and();
    while (lex_.peek().kind == TokenKind::Pipe) {
        lex_.next();  // consume '|'
        FormulaId rhs = parse_and();
        lhs = fac_.make_or(lhs, rhs);
    }
    return lhs;
}

// ── parse_and ───────────────────────────────────────────────────────────────
// and_expr ::= unary ( '&' unary )*

FormulaId Parser::parse_and() {
    FormulaId lhs = parse_unary();
    while (lex_.peek().kind == TokenKind::Amp) {
        lex_.next();  // consume '&'
        FormulaId rhs = parse_unary();
        lhs = fac_.make_and(lhs, rhs);
    }
    return lhs;
}

// ── parse_unary ─────────────────────────────────────────────────────────────
// unary ::= '!' unary
//         | 'EX' unary | 'AX' unary
//         | 'EF' unary | 'AF' unary | 'EF' '[' interval ']' unary
//         | 'EG' unary | 'AG' unary | 'EG' '[' interval ']' unary
//         | primary
//
// All unary prefix operators bind tighter than any binary operator and
// are right-associative among themselves, which is handled naturally by
// the recursive call.
//
// TCTL extension: EF[a,b], AF[a,b], EG[a,b], AG[a,b] with time intervals.

FormulaId Parser::parse_unary() {
    const Token& t = lex_.peek();

    switch (t.kind) {
        case TokenKind::Bang: {
            lex_.next();
            return fac_.make_not(parse_unary());
        }
        case TokenKind::KwEX: {
            lex_.next();
            return fac_.make_ex(parse_unary());
        }
        case TokenKind::KwAX: {
            lex_.next();
            return fac_.make_ax(parse_unary());
        }
        case TokenKind::KwEF: {
            lex_.next();
            // Check for timed variant: EF[a,b], EF(a,b), or EF<c, EF<=c, etc.
            if (has_time_interval()) {
                TimeInterval iv = parse_time_interval();
                return fac_.make_timed_ef(parse_unary(), iv.lower, iv.upper);
            }
            if (has_relational_bound()) {
                TimeInterval iv = parse_relational_bound();
                return fac_.make_timed_ef(parse_unary(), iv.lower, iv.upper);
            }
            return fac_.make_ef(parse_unary());
        }
        case TokenKind::KwAF: {
            lex_.next();
            // Check for timed variant: AF[a,b], AF(a,b), or AF<c, AF<=c, etc.
            if (has_time_interval()) {
                TimeInterval iv = parse_time_interval();
                return fac_.make_timed_af(parse_unary(), iv.lower, iv.upper);
            }
            if (has_relational_bound()) {
                TimeInterval iv = parse_relational_bound();
                return fac_.make_timed_af(parse_unary(), iv.lower, iv.upper);
            }
            return fac_.make_af(parse_unary());
        }
        case TokenKind::KwEG: {
            lex_.next();
            // Check for timed variant: EG[a,b], EG(a,b), or EG<c, EG<=c, etc.
            if (has_time_interval()) {
                TimeInterval iv = parse_time_interval();
                return fac_.make_timed_eg(parse_unary(), iv.lower, iv.upper);
            }
            if (has_relational_bound()) {
                TimeInterval iv = parse_relational_bound();
                return fac_.make_timed_eg(parse_unary(), iv.lower, iv.upper);
            }
            return fac_.make_eg(parse_unary());
        }
        case TokenKind::KwAG: {
            lex_.next();
            // Check for timed variant: AG[a,b], AG(a,b), or AG<c, AG<=c, etc.
            if (has_time_interval()) {
                TimeInterval iv = parse_time_interval();
                return fac_.make_timed_ag(parse_unary(), iv.lower, iv.upper);
            }
            if (has_relational_bound()) {
                TimeInterval iv = parse_relational_bound();
                return fac_.make_timed_ag(parse_unary(), iv.lower, iv.upper);
            }
            return fac_.make_ag(parse_unary());
        }
        default:
            return parse_primary();
    }
}

// ── TCTL: Time interval parsing ─────────────────────────────────────────────

bool Parser::has_time_interval() {
    // A time interval starts with '[' or '(' followed by an integer literal.
    // '[' = closed lower bound, '(' = open lower bound
    TokenKind k = lex_.peek().kind;
    if (k != TokenKind::LBracket && k != TokenKind::LParen) {
        return false;
    }
    
    // Use peek2 to check if next token after '[' or '(' is an integer
    Token next = lex_.peek2();
    return next.kind == TokenKind::IntLiteral;
}

Parser::TimeInterval Parser::parse_time_interval() {
    // Expect: '[' lower ',' upper ']' (closed-closed)
    //      or '(' lower ',' upper ')' (open-open)
    //      or '[' lower ',' upper ')' (closed-open)
    //      or '(' lower ',' upper ']' (open-closed)
    Token start = lex_.next();
    bool lower_strict = (start.kind == TokenKind::LParen);  // '(' means strict/open
    
    // Parse lower bound (must be integer)
    Token lower_tok = expect(TokenKind::IntLiteral, "as lower bound of time interval");
    std::int64_t lower_val = std::stoll(lower_tok.text);
    
    expect(TokenKind::Comma, "in time interval");
    
    // Parse upper bound (integer or 'inf')
    TimeBound upper;
    Token upper_tok = lex_.next();  // Consume and copy by value
    if (upper_tok.kind == TokenKind::IntLiteral) {
        upper.value = std::stoll(upper_tok.text);
        upper.is_infinity = false;
    } else if (upper_tok.kind == TokenKind::KwInf) {
        upper.is_infinity = true;
        upper.value = 0;
    } else {
        error(upper_tok, "expected integer or 'inf' as upper bound of time interval");
    }
    
    // Parse closing bracket to determine upper strictness
    Token end = lex_.next();
    if (end.kind == TokenKind::RBracket) {
        if (upper.is_infinity) {
            error(end, "infinity upper bound must use ')' not ']'; "
                       "closed interval at infinity is not meaningful");
        }
        upper.is_strict = false;  // ']' = closed
    } else if (end.kind == TokenKind::RParen) {
        upper.is_strict = true;   // ')' = open/strict
    } else {
        error(end, "expected ']' or ')' to close time interval");
    }
    
    TimeBound lower{lower_val, lower_strict, false};
    
    // Validate: lower < upper (point intervals a=b are not allowed)
    if (!upper.is_infinity && lower_val > upper.value) {
        error(start, "time interval requires lower < upper");
    }
    if (!upper.is_infinity && lower_val == upper.value) {
        error(start, "point intervals (a = b) are not allowed; require a < b");
    }
    if (lower_val < 0) {
        error(start, "time interval lower bound must be non-negative");
    }
    
    return TimeInterval{lower, upper};
}

bool Parser::has_relational_bound() {
    // Relational bound starts with a comparison operator: <, <=, >, >=
    TokenKind k = lex_.peek().kind;
    return k == TokenKind::Less || k == TokenKind::LessEq ||
           k == TokenKind::Greater || k == TokenKind::GreaterEq;
}

Parser::TimeInterval Parser::parse_relational_bound() {
    // Parse relational bound: <c, <=c, >c, >=c
    // Semantics:
    //   <c   → (0, c)   = lower=0 closed, upper=c open
    //   <=c  → [0, c]   = lower=0 closed, upper=c closed  
    //   >c   → (c, inf) = lower=c open, upper=inf
    //   >=c  → [c, inf) = lower=c closed, upper=inf (with strictness doesn't matter for inf)
    
    Token op = lex_.next();
    Token val_tok = expect(TokenKind::IntLiteral, "as relational time bound");
    std::int64_t c = std::stoll(val_tok.text);
    
    TimeBound lower, upper;
    
    switch (op.kind) {
        case TokenKind::Less:      // <c → (0, c)
            lower = TimeBound::closed(0);
            upper = TimeBound::open(c);
            break;
        case TokenKind::LessEq:    // <=c → [0, c]
            lower = TimeBound::closed(0);
            upper = TimeBound::closed(c);
            break;
        case TokenKind::Greater:   // >c → (c, inf)
            lower = TimeBound::open(c);
            upper = TimeBound::infinity();
            upper.is_strict = true;  // infinity is always open
            break;
        case TokenKind::GreaterEq: // >=c → [c, inf)
            lower = TimeBound::closed(c);
            upper = TimeBound::infinity();
            upper.is_strict = true;  // infinity is always open
            break;
        default:
            error(op, "expected comparison operator for relational time bound");
    }
    
    return TimeInterval{lower, upper};
}

// ── parse_primary ───────────────────────────────────────────────────────────
// primary ::= 'true' | 'false' 
//           | int_expr comp_op int_expr   (arithmetic constraint)
//           | IDENTIFIER      (if not followed by arith/comp op)
//           | 'E' '(' formula 'U' formula ')'
//           | 'E' '(' formula 'U' '[' interval ']' formula ')'  (TCTL)
//           | 'A' '(' formula 'U' formula ')'
//           | 'A' '(' formula 'U' '[' interval ']' formula ')'  (TCTL)
//           | '(' formula ')'

FormulaId Parser::parse_primary() {
    Token t = lex_.peek();

    // ── Standard tctl formula parsing (keywords and parens) ──────────────
    if (t.kind == TokenKind::KwTrue ||
        t.kind == TokenKind::KwFalse ||
        t.kind == TokenKind::KwE ||
        t.kind == TokenKind::KwA) {
        // These are definitely tctl formulas
        t = lex_.next();

        switch (t.kind) {
            case TokenKind::KwTrue:
                return fac_.make_true();

            case TokenKind::KwFalse:
                return fac_.make_false();

            // ── E(φ U ψ), E(φ U[a,b] ψ), E(φ R ψ), E(φ R[a,b] ψ) ─────
            case TokenKind::KwE: {
                expect(TokenKind::LParen, "after 'E'");
                FormulaId lhs = parse_formula();
                // Check for U or R operator
                const Token& op_tok = lex_.peek();
                if (op_tok.kind == TokenKind::KwR) {
                    lex_.next();  // consume 'R'
                    // Check for timed variant: R[a,b]
                    if (has_time_interval()) {
                        TimeInterval iv = parse_time_interval();
                        FormulaId rhs = parse_formula();
                        expect(TokenKind::RParen, "closing E(... R[a,b] ...)");
                        return fac_.make_timed_er(lhs, rhs, iv.lower, iv.upper);
                    }
                    FormulaId rhs = parse_formula();
                    expect(TokenKind::RParen, "closing E(... R ...)");
                    return fac_.make_er(lhs, rhs);
                }
                expect(TokenKind::KwU, "in E(... U/R ...)");
                // Check for timed variant: U[a,b]
                if (has_time_interval()) {
                    TimeInterval iv = parse_time_interval();
                    FormulaId rhs = parse_formula();
                    expect(TokenKind::RParen, "closing E(... U[a,b] ...)");
                    return fac_.make_timed_eu(lhs, rhs, iv.lower, iv.upper);
                }
                FormulaId rhs = parse_formula();
                expect(TokenKind::RParen, "closing E(... U ...)");
                return fac_.make_eu(lhs, rhs);
            }

            // ── A(φ U ψ), A(φ U[a,b] ψ), A(φ R ψ), A(φ R[a,b] ψ) ─────
            case TokenKind::KwA: {
                expect(TokenKind::LParen, "after 'A'");
                FormulaId lhs = parse_formula();
                // Check for U or R operator
                const Token& op_tok = lex_.peek();
                if (op_tok.kind == TokenKind::KwR) {
                    lex_.next();  // consume 'R'
                    // Check for timed variant: R[a,b]
                    if (has_time_interval()) {
                        TimeInterval iv = parse_time_interval();
                        FormulaId rhs = parse_formula();
                        expect(TokenKind::RParen, "closing A(... R[a,b] ...)");
                        return fac_.make_timed_ar(lhs, rhs, iv.lower, iv.upper);
                    }
                    FormulaId rhs = parse_formula();
                    expect(TokenKind::RParen, "closing A(... R ...)");
                    return fac_.make_ar(lhs, rhs);
                }
                expect(TokenKind::KwU, "in A(... U/R ...)");
                // Check for timed variant: U[a,b]
                if (has_time_interval()) {
                    TimeInterval iv = parse_time_interval();
                    FormulaId rhs = parse_formula();
                    expect(TokenKind::RParen, "closing A(... U[a,b] ...)");
                    return fac_.make_timed_au(lhs, rhs, iv.lower, iv.upper);
                }
                FormulaId rhs = parse_formula();
                expect(TokenKind::RParen, "closing A(... U ...)");
                return fac_.make_au(lhs, rhs);
            }

            default:
                break;
        }
    }

    // ── Parenthesised tctl formula ────────────────────────────────────────
    if (t.kind == TokenKind::LParen) {
        lex_.next(); // consume '('
        FormulaId inner = parse_formula();
        expect(TokenKind::RParen, "closing '('");
        return inner;
    }

    // ── Arithmetic island {...} ──────────────────────────────────────────
    // Allow arithmetic expressions/constraints with parentheses using { } notation
    // Syntax: {arith_expr comp_op arith_expr} or {expr}  
    if (t.kind == TokenKind::LBrace) {
        lex_.next(); // consume '{'
        
        // Parse first arithmetic expression
        FormulaId lhs = parse_int_expr();
        
        // Check if there's a comparison operator inside the braces
        const Token& inside = lex_.peek();
        if (is_comparison_op(inside.kind)) {
            TokenKind op_kind = inside.kind;
            lex_.next(); // consume comparison  
            FormulaId rhs = parse_int_expr();
            expect(TokenKind::RBrace, "closing arithmetic island '}'");
            
            // Build and return the constraint
            switch (op_kind) {
                case TokenKind::LessEq:
                    return fac_.make_int_less_eq(lhs, rhs);
                case TokenKind::Less:
                    return fac_.make_int_less(lhs, rhs);
                case TokenKind::GreaterEq:
                    return fac_.make_int_greater_eq(lhs, rhs);
                case TokenKind::Greater:
                    return fac_.make_int_greater(lhs, rhs);
                case TokenKind::Equal:
                    return fac_.make_int_equal(lhs, rhs);
                default:
                    break;
            }
        }
        
        // No comparison inside braces - expect it after
        expect(TokenKind::RBrace, "closing arithmetic island '}'");
        
        // Now check for comparison operator after the braces
        const Token& after = lex_.peek();
        if (is_comparison_op(after.kind)) {
            TokenKind op_kind = after.kind;
            lex_.next(); // consume comparison
            FormulaId rhs = parse_int_expr();
            
            switch (op_kind) {
                case TokenKind::LessEq:
                    return fac_.make_int_less_eq(lhs, rhs);
                case TokenKind::Less:
                    return fac_.make_int_less(lhs, rhs);
                case TokenKind::GreaterEq:
                    return fac_.make_int_greater_eq(lhs, rhs);
                case TokenKind::Greater:
                    return fac_.make_int_greater(lhs, rhs);
                case TokenKind::Equal:
                    return fac_.make_int_equal(lhs, rhs);
                default:
                    break;
            }
        }
        
        // If used in arithmetic context without comparison, just return the expression
        return lhs;
    }

    // ── Check if this is an arithmetic constraint ──────────────────────
    // Try to parse as arithmetic constraint if it starts with int-like tokens
    if (is_int_start(t.kind)) {
        // Tentatively parse as int_expr
        FormulaId lhs = parse_int_expr();
        
        // Check for comparison operator
        const Token& op_tok = lex_.peek();
        if (is_comparison_op(op_tok.kind)) {
            TokenKind op_kind = op_tok.kind;  // Copy the kind before consuming!
            lex_.next(); // consume comparison operator
            FormulaId rhs = parse_int_expr();
            
            // Build constraint based on operator type
            switch (op_kind) {
                case TokenKind::LessEq:
                    return fac_.make_int_less_eq(lhs, rhs);
                case TokenKind::Less:
                    return fac_.make_int_less(lhs, rhs);
                case TokenKind::GreaterEq:
                    return fac_.make_int_greater_eq(lhs, rhs);
                case TokenKind::Greater:
                    return fac_.make_int_greater(lhs, rhs);
                case TokenKind::Equal:
                    return fac_.make_int_equal(lhs, rhs);
                default:
                    break;
            }
        }
        
        // If lhs was actually just an identifier and no comparison, 
        // check if it's a simple variable (treat as atom)
        const FormulaNode& n = fac_.node(lhs);
        if (n.kind == NodeKind::IntVar) {
            // Convert to boolean atom
            return fac_.make_atom(n.atom_name);
        }
        
        // If we have a parenthesized tctl formula that was misparsed 
        // as arithmetic, we'll have an error here. This happens when
        // parse_int_expr is called on something like "( boolean_formula )".
        // We should detect this case and re-parse.
        // For now, just treat any other case as an error.
        
        // Otherwise, this is an error (arithmetic expression without comparison)
        Token err_tok = lex_.peek();
        error(err_tok, "expected comparison operator after arithmetic expression");
    }

    // Should not reach here
    Token err_tok = lex_.next();
    error(err_tok, "unexpected token '" + err_tok.text + "'");
}

// ── Arithmetic expression parsing ───────────────────────────────────────────

bool Parser::is_int_start(TokenKind kind) const {
    return kind == TokenKind::Identifier || 
           kind == TokenKind::IntLiteral;
    // Note: LParen is NOT included here, as toplevel parens are always tctl formulas
    // Arithmetic parens are handled inside parse_int_factor
}

bool Parser::is_comparison_op(TokenKind kind) const {
    return kind == TokenKind::LessEq ||
           kind == TokenKind::Less ||
           kind == TokenKind::GreaterEq ||
           kind == TokenKind::Greater ||
           kind == TokenKind::Equal;
}

// int_expr ::= int_term (('+' | '-') int_term)*
FormulaId Parser::parse_int_expr() {
    FormulaId lhs = parse_int_term();
    
    while (true) {
        const Token& t = lex_.peek();
        if (t.kind == TokenKind::Plus) {
            lex_.next();
            FormulaId rhs = parse_int_term();
            lhs = fac_.make_int_plus(lhs, rhs);
        } else if (t.kind == TokenKind::Minus) {
            lex_.next();
            FormulaId rhs = parse_int_term();
            lhs = fac_.make_int_minus(lhs, rhs);
        } else {
            break;
        }
    }
    
    return lhs;
}

// int_term ::= int_factor ('*' int_factor)*
FormulaId Parser::parse_int_term() {
    FormulaId lhs = parse_int_factor();
    
    while (lex_.peek().kind == TokenKind::Star) {
        lex_.next();
        FormulaId rhs = parse_int_factor();
        lhs = fac_.make_int_times(lhs, rhs);
    }
    
    return lhs;
}

// int_factor ::= IDENTIFIER | IntLiteral | '(' int_expr ')' | '[' int_expr ']'
FormulaId Parser::parse_int_factor() {
    Token t = lex_.next();
    
    if (t.kind == TokenKind::Identifier) {
        return fac_.make_int_var(t.text);
    } else if (t.kind == TokenKind::IntLiteral) {
        std::int64_t value = std::stoll(t.text);
        return fac_.make_int_const(value);
    } else if (t.kind == TokenKind::LParen) {
        FormulaId inner = parse_int_expr();
        expect(TokenKind::RParen, "closing '(' in arithmetic expression");
        return inner;
    } else if (t.kind == TokenKind::LBracket) {
        FormulaId inner = parse_int_expr();
        expect(TokenKind::RBracket, "closing ']' in arithmetic expression");
        return inner;
    } else {
        error(t, "expected identifier, integer, '(', or '[' in arithmetic expression");
    }
}

// ── Free function convenience ───────────────────────────────────────────────

FormulaId parse_formula(const std::string& input, FormulaFactory& factory,
                        std::uint32_t line) {
    Lexer lex(input, line);
    Parser parser(lex, factory);
    return parser.parse();
}

}  // namespace tctl
