import argparse
import subprocess
import re

def generate_truck_smt2(smt2_filename):
    trucks = range(1, 9)
    items = ['n', 'p', 's', 'c', 'd']
    totals = {'n': 4, 's': 8, 'c': 10, 'd': 20}
    weights = {'n': 800, 'p': 1100, 's': 1000, 'c': 2500, 't': 400, 'd': 200}

    decls = "\n".join(f"(declare-const x_{it}{i} Int)" for i in trucks for it in items)

    domain = "\n  ".join(f"(>= x_{it}{i} 0)" for i in trucks for it in items)
    domain_constraint = f"(assert (and\n  {domain}\n))"

    total_constraints = "\n".join(
        f"(assert (= (+ {' '.join(f'x_{it}{i}' for i in trucks)}) {tot}))"
        for it, tot in totals.items()
    )

    cooling_constraints = "\n".join(f"(assert (= x_s{i} 0))" for i in range(4, 9))

    capacity_constraints_list = []
    for i in trucks:
        weight_expr = " ".join(f"(* {weights[it]} x_{it}{i})" for it in items)
        capacity_constraints_list.append(f"(assert (<= (+ {weight_expr}) 8000))")
        pallet_expr = " ".join(f"x_{it}{i}" for it in items)
        capacity_constraints_list.append(f"(assert (<= (+ {pallet_expr}) 8))")
    capacity_constraints = "\n".join(capacity_constraints_list)

    nuzzle_constraints = "\n".join(f"(assert (<= x_n{i} 1))" for i in trucks)

    explosive_constraints = "\n".join(f"(assert (or (= x_p{i} 0) (= x_c{i} 0)))" for i in trucks)

    prittles_expr = " ".join(f"x_p{i}" for i in trucks)
    objective = f"(maximize (+ {prittles_expr}))"

    smt2_content = f"""(set-option :produce-models true)
(set-logic QF_LIA)

; Each truck i has integer variables:
;   x_n_i = # of nuzzles, x_p_i = # of prittles, x_s_i = # of skipples,
;   x_c_i = # of crottles, x_d_i = # of duppies.
; We'll declare them for i=1..8.
{decls}

; Domain constraints: all variables ≥ 0.
{domain_constraint}

; Total item constraints:
; 4 nuzzles, 8 skipples, 10 crottles, 7 tynnels, 20 duppies
{total_constraints}

; We want to maximize prittles, so no fixed total for x_p_i.

; Skipples need cooling: only 3 of the 8 trucks are cooled.
; For simplicity, assume trucks 1,2,3 are cooled; set x_s4..x_s8 = 0:
{cooling_constraints}

; Each truck’s capacity ≤ 8000 kg, and ≤ 8 pallets:
{capacity_constraints}

; Nuzzle constraint: at most 2 nuzzles per truck:
{nuzzle_constraints}

; No prittles and crottles together
{explosive_constraints}

; Objective: maximize the total number of prittles
{objective}

(check-sat)
(get-objectives)
(get-model)
"""
    with open(smt2_filename, "w") as f:
        f.write(smt2_content.strip())
    print(f"SMT2 file '{smt2_filename}' has been generated.")

def run_z3(smt2_filename):
    try:
        output = subprocess.check_output(["z3", smt2_filename], universal_newlines=True)
    except FileNotFoundError:
        print("Error: Z3 is not installed or not found in PATH.")
        return None
    return output

def parse_z3_output(output):
    obj_match = re.search(r'\(objectives\s+\(\(\+ [^)]+\)\s+(\d+)\)\)', output, re.MULTILINE)
    objective_value = int(obj_match.group(1)) if obj_match else None

    model_pattern = re.compile(r'\(define-fun\s+(\S+)\s+\(\)\s+Int\s+(\d+)\)')
    model_matches = model_pattern.findall(output)
    model_dict = {var: int(val) for var, val in model_matches}
    
    return objective_value, model_dict

def print_model_by_truck(model_dict):
    trucks = range(1, 9)
    item_labels = {
        'n': "nuzzles",
        'p': "prittles",
        's': "skipples",
        'c': "crottles",
        't': "tynnels",
        'd': "duppies"
    }
    for i in trucks:
        assignments = []
        for it in ['n', 'p', 's', 'c', 't', 'd']:
            var = f"x_{it}{i}"
            val = model_dict.get(var, "N/A")
            assignments.append(f"{item_labels[it]} ({var}) = {val}")
        print(f"Truck {i}: " + ", ".join(assignments))

def main():
    parser = argparse.ArgumentParser(description="Truck SMT2 Generator and Z3 Runner")
    parser.add_argument("--smt2", type=str, default="1.smt2", help="Output SMT2 filename")
    args = parser.parse_args()
    
    generate_truck_smt2(args.smt2)
    output = run_z3(args.smt2)
    if output is None:
        return
    
    objective_value, model_dict = parse_z3_output(output)
    print_model_by_truck(model_dict)

if __name__ == "__main__":
    main()
