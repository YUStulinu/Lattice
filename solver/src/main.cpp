// lattice: solve a DIMACS CNF file.
//
//   lattice [--proof FILE] [--text-proof] [--no-elim] [--restarts glucose|luby|auto]
//           [--timeout SECONDS] [--trace FILE] [-v] [--quiet] file.cnf
//
// Prints "s SATISFIABLE" with "v" lines, "s UNSATISFIABLE" or "s UNKNOWN", and exits with 10,
// 20 or 0 as SAT competition solvers do. A last line "c stats {json}" summarises the run.
#include <cctype>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <string>
#include <vector>

#include "solver.hpp"

using namespace lattice;

namespace {

bool parse_dimacs(const char* path, Solver& s, std::string& err) {
    FILE* f = std::fopen(path, "rb");
    if (!f) {
        err = "cannot open file";
        return false;
    }
    std::vector<char> buf(1 << 20);
    std::vector<Lit> clause;
    bool header = false, in_comment = false, negative = false, in_number = false, done = false;
    long long num = 0;
    size_t n;
    std::string line_start;
    bool at_line_start = true;
    while (!done && (n = std::fread(buf.data(), 1, buf.size(), f)) > 0) {
        for (size_t i = 0; i < n; i++) {
            const char ch = buf[i];
            if (in_comment) {
                if (ch == '\n') in_comment = false, at_line_start = true;
                continue;
            }
            if (at_line_start && (ch == 'c' || ch == 'p')) {
                // Comment or header line: skip it (the header's counts are not needed).
                if (ch == 'p') header = true;
                in_comment = true;
                continue;
            }
            if (at_line_start && ch == '%') {  // SATLIB files end with "%" and a stray "0"
                done = true;
                break;
            }
            at_line_start = (ch == '\n');
            if (ch == '-') {
                negative = true;
            } else if (ch >= '0' && ch <= '9') {
                num = num * 10 + (ch - '0');
                in_number = true;
            } else if (in_number) {
                if (num == 0) {
                    s.add_clause(clause);
                    clause.clear();
                } else {
                    clause.push_back(from_dimacs(static_cast<int>(negative ? -num : num)));
                }
                num = 0, negative = false, in_number = false;
            } else if (!std::isspace(static_cast<unsigned char>(ch))) {
                err = std::string("unexpected character '") + ch + "'";
                std::fclose(f);
                return false;
            }
        }
    }
    if (in_number) {
        if (num == 0) {
            s.add_clause(clause);
            clause.clear();
        } else {
            clause.push_back(from_dimacs(static_cast<int>(negative ? -num : num)));
        }
    }
    if (!clause.empty()) s.add_clause(clause);
    std::fclose(f);
    if (!header) {
        err = "no 'p cnf' header";
        return false;
    }
    return true;
}

bool check_model(const Solver& s) {
    for (const auto& c : s.original) {
        bool sat = false;
        for (Lit l : c)
            if (s.model_value(var(l)) != sign(l)) {
                sat = true;
                break;
            }
        if (!sat) return false;
    }
    return true;
}

}  // namespace

int main(int argc, char** argv) {
    Options opt;
    std::string proof_path, trace_path, file;
    bool text_proof = false, quiet = false;
    for (int i = 1; i < argc; i++) {
        const std::string a = argv[i];
        auto next = [&]() -> std::string {
            if (i + 1 >= argc) {
                std::fprintf(stderr, "missing value for %s\n", a.c_str());
                std::exit(1);
            }
            return argv[++i];
        };
        if (a == "--proof") proof_path = next();
        else if (a == "--text-proof") text_proof = true;
        else if (a == "--no-elim") opt.elim = false;
        else if (a == "--timeout") opt.timeout = std::atof(next().c_str());
        else if (a == "--trace") trace_path = next();
        else if (a == "-v") opt.verbose = true;
        else if (a == "--quiet") quiet = true;
        else if (a == "--restarts") {
            const std::string r = next();
            opt.restarts = r == "luby" ? Restarts::Luby : r == "glucose" ? Restarts::Glucose : Restarts::Auto;
        } else if (!a.empty() && a[0] == '-') {
            std::fprintf(stderr, "unknown option %s\n", a.c_str());
            return 1;
        } else {
            file = a;
        }
    }
    if (file.empty()) {
        std::fprintf(stderr, "usage: lattice [options] file.cnf\n");
        return 1;
    }
    Solver s(opt);
    if (!proof_path.empty() && !s.proof.open(proof_path, !text_proof)) {
        std::fprintf(stderr, "cannot write %s\n", proof_path.c_str());
        return 1;
    }
    if (!trace_path.empty()) s.trace.open(trace_path);
    const double t0 = now_seconds();
    std::string err;
    if (!parse_dimacs(file.c_str(), s, err)) {
        std::fprintf(stderr, "%s: %s\n", file.c_str(), err.c_str());
        return 1;
    }
    const double parsed = now_seconds();
    const Result r = s.solve();
    s.proof.close();
    s.trace.close();
    int code = 0;
    if (r == Result::Sat) {
        if (!check_model(s)) {
            std::printf("c ERROR: the model does not satisfy the formula\ns UNKNOWN\n");
            return 1;
        }
        std::printf("s SATISFIABLE\n");
        if (!quiet) {
            std::string line = "v";
            for (Var v = 0; v < s.num_vars(); v++) {
                line += ' ' + std::to_string(s.model_value(v) ? static_cast<int>(v + 1) : -static_cast<int>(v + 1));
                if (line.size() > 70) {
                    std::printf("%s\n", line.c_str());
                    line = "v";
                }
            }
            std::printf("%s 0\n", line.c_str());
        }
        code = 10;
    } else if (r == Result::Unsat) {
        std::printf("s UNSATISFIABLE\n");
        code = 20;
    } else {
        std::printf("s UNKNOWN\n");
    }
    const Stats& st = s.stats;
    std::printf("c stats {\"vars\": %u, \"clauses\": %zu, \"parse_s\": %.3f, \"solve_s\": %.3f, \"elim_s\": %.3f, \"conflicts\": %llu, "
                "\"decisions\": %llu, \"propagations\": %llu, \"restarts\": %llu, \"reductions\": %llu, \"elim_vars\": %llu, "
                "\"subsumed\": %llu, \"strengthened\": %llu, \"minimised\": %llu, \"learnt_literals\": %llu, \"proof_lines\": %llu}\n",
                s.num_vars(), s.num_original(), parsed - t0, st.solve_seconds, st.elim_seconds, static_cast<unsigned long long>(st.conflicts),
                static_cast<unsigned long long>(st.decisions), static_cast<unsigned long long>(st.propagations),
                static_cast<unsigned long long>(st.restarts), static_cast<unsigned long long>(st.reductions),
                static_cast<unsigned long long>(st.elim_vars), static_cast<unsigned long long>(st.subsumed),
                static_cast<unsigned long long>(st.strengthened), static_cast<unsigned long long>(st.minimised_literals),
                static_cast<unsigned long long>(st.learnt_literals), static_cast<unsigned long long>(s.proof.lines));
    return code;
}
