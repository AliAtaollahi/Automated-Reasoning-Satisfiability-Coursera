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
    
    # Additional constraint: job 7 should not start earlier than job 8
    additional_constraint = "(assert (>= S7 S8))\n"

    smt2_content = f"""
; Scheduling constraints for 10 jobs with an extra constraint: job 7 not starting before job 8

(declare-fun T () Int)

{job_constraints}

; Dependencies
{dep_constraints}

{additional_constraint}

(minimize T)
(check-sat)
(get-model)
(exit)
"""
    return smt2_content

# Write the SMT2 file and run Z3
smt_content = generate_smt_schedule()
with open("2.smt2", "w") as f:
    f.write(smt_content)

result = subprocess.run(["z3", "2.smt2"], capture_output=True, text=True)
print(result.stdout)
