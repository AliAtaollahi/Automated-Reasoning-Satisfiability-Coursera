import subprocess
import re

def generate_smt_constraints():
    iterations = 10
    variables = ""
    constraints = ""
    
    variables += """
;; Parameter n (in 1..10)
(declare-const n Int)
(assert (and (>= n 1) (<= n 10)))

;; Initial state
(declare-const a0 Int)
(declare-const b0 Int)
(assert (= a0 1))
(assert (= b0 1))
"""
    
    for i in range(1, iterations + 1):
        variables += f"""
(declare-const c{i} Bool)
(declare-const a{i} Int)
(declare-const b{i} Int)
"""
        
        constraints += f"""
;; Iteration {i}
(assert (ite c{i} 
              (and (= a{i} (+ a{i-1} (* 2 b{i-1})))  ; then: a := a + 2*b
                   (= b{i} (+ b{i-1} {i})))        ; b := b + i
              (and (= a{i} (+ a{i-1} {i}))          ; else: a := a + i
                   (= b{i} (+ a{i-1} b{i-1})))))
"""
    
    constraints += f"""
;; Crash condition: crash if b{iterations} equals 600+n.
(assert (= b{iterations} (+ 600 n)))
"""
    
    smt2_content = f"""
; SMT Constraints

(declare-fun T () Int)

{variables}

{constraints}

(check-sat)
(get-model)
(exit)
"""
    
    return smt2_content

smt_content = generate_smt_constraints()
with open("1.smt2", "w") as f:
    f.write(smt_content)

safe_values = []
for n in range(1, 11):
    with open("1.smt2", "w") as f:
        f.write(generate_smt_constraints().replace("(declare-const n Int)", f"(declare-const n Int)\n(assert (= n {n}))"))
    
    result = subprocess.run(["z3", "1.smt2"], capture_output=True, text=True)
    output = result.stdout
    
    if "unsat" in output:
        safe_values.append(str(n))
    else:
        match = re.search(r'\(define-fun n \(\) Int\s+(\d+)\)', output)
        if match:
            found_n = match.group(1)
            with open("1.smt2", "w") as f:
                f.write(generate_smt_constraints().replace("(declare-const n Int)", f"(declare-const n Int)\n(assert (not (= n {found_n})))"))
                
            result = subprocess.run(["z3", "1.smt2"], capture_output=True, text=True)
            output = result.stdout
            if "unsat" in output:
                safe_values.append(str(n))

print("".join(safe_values))
