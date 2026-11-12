cmake_minimum_required(VERSION 3.16)
project(LDProver VERSION 1.8.0 LANGUAGES CXX)

set(CMAKE_CXX_STANDARD 20)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_CXX_EXTENSIONS OFF)

if(MSVC)
  add_compile_options(/W4 /permissive-)
else()
  add_compile_options(-Wall -Wextra -Wpedantic -Werror=return-type)
endif()

include_directories(${CMAKE_CURRENT_SOURCE_DIR}/include)

# Module 1: Core Board, Ruleset, Target Tokens, Canonical History (FR-1, FR-2, C-7)
add_library(ldprover_core STATIC
  src/core/position.cc
  src/core/problem_parser.cc
)

# Module 2: Terminal Evaluator & Benson UCA (FR-3)
add_library(ldprover_terminal STATIC
  src/terminal/benson_uca.cc
)
target_link_libraries(ldprover_terminal PUBLIC ldprover_core)

# Module 3: Relevance-Zone (RZ) Isolation & Dual-Chain Closure (FR-5)
add_library(ldprover_rz STATIC
  src/rz/relevance_zone.cc
)
target_link_libraries(ldprover_rz PUBLIC ldprover_core ldprover_terminal)

# Module 4: Context-Isolated BoardTT & Radix-Tree PatternTT (FR-6)
add_library(ldprover_tt STATIC
  src/tt/transposition_table.cc
)
target_link_libraries(ldprover_tt PUBLIC ldprover_core ldprover_rz)

# Module 5: df-pn Search Engine with Progressive Widening & FastCapture (FR-4, FR-7)
add_library(ldprover_dfpn STATIC
  src/search/dfpn_solver.cc
)
target_link_libraries(ldprover_dfpn PUBLIC ldprover_core ldprover_terminal ldprover_rz ldprover_tt)

# Module 6: Independent lproof/1 Proof DAG Serializer, SGF Writer & Checker (FR-8, FR-9)
# Strict architectural isolation: ProofChecker does NOT link or invoke ldprover_dfpn.
add_library(ldprover_proof STATIC
  src/proof/proof_checker.cc
)
target_link_libraries(ldprover_proof PUBLIC ldprover_core ldprover_terminal ldprover_rz)

# CLI Entrypoint: tprover solve | check | bench (FR-10)
add_executable(tprover
  src/cli/tprover_main.cc
)
target_link_libraries(tprover PRIVATE
  ldprover_core
  ldprover_terminal
  ldprover_rz
  ldprover_tt
  ldprover_dfpn
  ldprover_proof
)
