import subprocess

def generate_smt_schedule():
    jobs = range(1, 11)
    deps = {
        3: [1, 2],
        6: [2, 4],
        7: [1, 4, 5],
        8: [3, 6],
        9: [6, 7],
        10: [8, 9]
    }
    
    job_constraints = ""
    for i in jobs:
        job_constraints += f"(declare-fun S{i} () Int)\n"
        job_constraints += f"(declare-fun E{i} () Int)\n"
        job_constraints += f"(assert (>= S{i} 0))\n"
        job_constraints += f"(assert (= E{i} (+ S{i} {i+10})))\n"
        job_constraints += f"(assert (<= E{i} T))\n"
    
    dep_constraints = ""
    for j, prereqs in deps.items():
        for p in prereqs:
            dep_constraints += f"(assert (>= S{j} E{p}))\n"
    
    # Existing additional constraint: job 7 should not start earlier than job 8
    extra_constraint = "(assert (>= S7 S8))\n"
    
    # New constraint: jobs 3, 4, and 5 cannot overlap
    # For each pair, either one finishes before the other starts.
    special_equipment = ""
    for (i, j) in [(3, 4), (3, 5), (4, 5)]:
        special_equipment += f"(assert (or (<= E{i} S{j}) (<= E{j} S{i})))\n"
    
    smt2_content = f"""
; Scheduling constraints for 10 jobs with additional requirements

(declare-fun T () Int)

{job_constraints}

; Dependencies
{dep_constraints}

{extra_constraint}

; Special equipment: jobs 3, 4, and 5 cannot run concurrently
{special_equipment}

(minimize T)
(check-sat)
(get-model)
(exit)
"""
    return smt2_content

# Generate the SMT2 content, write it to a file, and run Z3
smt_content = generate_smt_schedule()
with open("3.smt2", "w") as f:
    f.write(smt_content)

result = subprocess.run(["z3", "3.smt2"], capture_output=True, text=True)
print(result.stdout)
