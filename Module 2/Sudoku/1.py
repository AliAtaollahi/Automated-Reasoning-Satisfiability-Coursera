import argparse
import subprocess
import re
import matplotlib.pyplot as plt
import numpy as np

def generate_smt2(smt2_filename, puzzle_filename):
    domain_conditions = []
    for i in range(1, 10):
        for j in range(1, 10):
            domain_conditions.append(f"(and (>= (A {i} {j}) 1) (<= (A {i} {j}) 9))")
    domain_assert = "(assert (and\n    " + "\n    ".join(domain_conditions) + "\n))"
    
    row_conditions = []
    for i in range(1, 10):
        row_cells = [f"(A {i} {j})" for j in range(1, 10)]
        row_conditions.append(f"(distinct {' '.join(row_cells)})")
    row_assert = "(assert (and\n    " + "\n    ".join(row_conditions) + "\n))"
    
    col_conditions = []
    for j in range(1, 10):
        col_cells = [f"(A {i} {j})" for i in range(1, 10)]
        col_conditions.append(f"(distinct {' '.join(col_cells)})")
    col_assert = "(assert (and\n    " + "\n    ".join(col_conditions) + "\n))"
    
    block_conditions = []
    for br in range(3):
        for bc in range(3):
            block_cells = []
            for i in range(3):
                for j in range(3):
                    row_index = 3 * br + i + 1
                    col_index = 3 * bc + j + 1
                    block_cells.append(f"(A {row_index} {col_index})")
            block_conditions.append(f"(distinct {' '.join(block_cells)})")
    block_assert = "(assert (and\n    " + "\n    ".join(block_conditions) + "\n))"
    
    fixed_constraints = []
    try:
        with open(puzzle_filename, "r") as pf:
            lines = pf.readlines()
        for i, line in enumerate(lines, start=1):
            entries = line.strip().split()
            for j, entry in enumerate(entries, start=1):
                if entry not in ['-', '.']:
                    fixed_constraints.append(f"(assert (= (A {i} {j}) {entry}))")
    except FileNotFoundError:
        print(f"Puzzle file '{puzzle_filename}' not found. No fixed constraints will be added.")
    fixed_assert = "\n".join(fixed_constraints)
    
    get_value_command = "(get-value (" + " ".join(f"(A {i} {j})" for i in range(1, 10) for j in range(1, 10)) + "))"
    
    smt2_content = f"""
; 9×9 Sudoku-like constraints with given clues
(declare-fun A (Int Int) Int)

; Domain constraints
{domain_assert}

; Row constraints
{row_assert}

; Column constraints
{col_assert}

; Block constraints
{block_assert}

; Fixed cell constraints
{fixed_assert}

(check-sat)
{get_value_command}
(exit)
"""
    with open(smt2_filename, "w") as f:
        f.write(smt2_content.strip())
    
    print(f"SMT2 file '{smt2_filename}' has been generated.")

def visualize_sudoku(grid):
    fig, ax = plt.subplots(figsize=(6,6))
    ax.set_xticks(np.arange(10)-0.5)
    ax.set_yticks(np.arange(10)-0.5)
    ax.set_xticklabels([])
    ax.set_yticklabels([])
    
    for i in range(0, 10, 3):
        ax.axhline(i-0.5, color='black', linewidth=2)
        ax.axvline(i-0.5, color='black', linewidth=2)
    
    for i in range(9):
        for j in range(9):
            ax.text(j, i, grid[i][j], va='center', ha='center', fontsize=12)
    
    ax.grid(True, which='both', color='gray', linestyle='-', linewidth=0.5)
    ax.set_xlim(-0.5, 8.5)
    ax.set_ylim(8.5, -0.5)
    
    plt.savefig("sudoku_solution.png")
    plt.close()

def run_z3_and_visualize(filename):
    try:
        output = subprocess.check_output(["z3", filename]).decode("utf-8")
    except FileNotFoundError:
        print("Error: Z3 is not installed or not found in PATH.")
        return
    
    if "unsat" in output:
        print("Z3 says the problem is unsatisfiable.")
        return
    elif "sat" not in output:
        print("Z3 did not return 'sat'—something is unusual.")
        return
    
    pattern = re.compile(r'\(A\s+(\d+)\s+(\d+)\)\s+(\d+)')
    matches = pattern.findall(output)
    
    model_dict = {}
    for match in matches:
        i, j, val = match
        i, j, val = int(i), int(j), int(val)
        model_dict[(i, j)] = val
    
    grid = []
    for i in range(1, 10):
        row = []
        for j in range(1, 10):
            cell_value = model_dict.get((i, j), 0)
            row.append(cell_value)
        grid.append(row)
    
    visualize_sudoku(grid)

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Sudoku SMT2 Generator and Solver")
    parser.add_argument("--smt2", type=str, default="1.smt2", help="Output SMT2 filename")
    parser.add_argument("--input", type=str, default="input.txt", help="Input puzzle filename")
    args = parser.parse_args()
    
    generate_smt2(args.smt2, args.input)
    run_z3_and_visualize(args.smt2)
