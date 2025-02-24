import subprocess
import re

def parse_model(z3_output):
    pattern = re.compile(r'\(= x!0 (\d+)\) \(= x!1 (\d+)\)')
    matches = pattern.findall(z3_output)
    return [(int(x0), int(x1)) for x0, x1 in matches]

def generate_negation(model):
    negation = "(not (and {}))".format(
        " ".join(f"(= (p {x0} {x1}) true)" for x0, x1 in model)
    )
    return negation

def run_z3(filename="1.smt2"):
    result = subprocess.run(["z3", filename], capture_output=True, text=True)
    return result.stdout

def generate_smt2(negations, filename="1.smt2"):
    horizontal_conditions = """
    (and
        {0}
    )
    """.format(
        "\n        ".join(
            f"(or (not (p {i} {j})) (not (p {i} {k})))"
            for i in range(1, 9)
            for j in range(1, 9)
            for k in range(j + 1, 9)
        )
    )

    vertical_conditions = """
    (and
        {0}
    )
    """.format(
        "\n        ".join(
            f"(or (not (p {i} {j})) (not (p {k} {j})))"
            for j in range(1, 9)
            for i in range(1, 9)
            for k in range(i + 1, 9)
        )
    )

    row_conditions = """
    (and
        {0}
    )
    """.format(
        "\n        ".join(
            f"(or {' '.join(f'(p {i} {j})' for j in range(1, 9))})"
            for i in range(1, 9)
        )
    )

    col_conditions = """
    (and
        {0}
    )
    """.format(
        "\n        ".join(
            f"(or {' '.join(f'(p {i} {j})' for i in range(1, 9))})"
            for j in range(1, 9)
        )
    )

    diagnosis_conditions = """
    (and
        {0}
    )
    """.format(
        "\n        ".join(
            f"(or (not (p {i} {j})) (not (p {i_prime} {j_prime})))"
            for i in range(1, 9)
            for i_prime in range(i + 1, 9)
            for j in range(1, 9)
            for j_prime in range(1, 9)
            if abs(i - i_prime) == abs(j - j_prime)
        )
    )

    negation_conditions = "\n        ".join(negations)

    smt2_content = f"""
(declare-fun p (Int Int) Bool)

(assert {horizontal_conditions})
(assert {vertical_conditions})
(assert {row_conditions})
(assert {col_conditions})
(assert {diagnosis_conditions})

; Adding negated models to prevent duplicates
(assert (and
    {negation_conditions}
))

(check-sat)
(get-model)
(exit)
"""

    with open(filename, "w") as f:
        f.write(smt2_content)

def main():
    negations = []
    models = []

    while True:
        generate_smt2(negations)
        output = run_z3()

        if "unsat" in output:
            break

        model = parse_model(output)
        models.append(model)

        negation = generate_negation(model)
        negations.append(negation)

    for idx, model in enumerate(models):
        print(f"Model {idx + 1}: {model}")

if __name__ == "__main__":
    main()
