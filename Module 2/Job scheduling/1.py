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

    smt2_content = f"""
; Scheduling constraints for 10 jobs

(declare-fun T () Int)

{job_constraints}

; Dependencies
{dep_constraints}

(minimize T)
(check-sat)
(get-model)
(exit)
"""
    return smt2_content

# Generate SMT2 content and write it to a file
smt_content = generate_smt_schedule()
with open("1.smt2", "w") as f:
    f.write(smt_content)

# Run Z3 on the generated file
result = subprocess.run(["z3", "1.smt2"], capture_output=True, text=True)
print(result.stdout)
