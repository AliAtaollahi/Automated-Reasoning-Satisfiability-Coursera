import subprocess
import re
import matplotlib.pyplot as plt
import os

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

(assert (and
    {negation_conditions}
))

(check-sat)
(get-model)
(exit)
"""

    with open(filename, "w") as f:
        f.write(smt2_content)

def visualize_model(model, index, output_folder="output"):
    if not os.path.exists(output_folder):
        os.makedirs(output_folder)

    board = [[0 for _ in range(8)] for _ in range(8)]
    for (row, col) in model:
        board[row-1][col-1] = 1

    fig, ax = plt.subplots()
    ax.matshow([[((i + j) % 2) for j in range(8)] for i in range(8)], cmap='binary')

    for i in range(8):
        for j in range(8):
            if board[i][j] == 1:
                ax.text(j, i, '♛', va='center', ha='center', fontsize=20, color='red')

    plt.xticks(range(8))
    plt.yticks(range(8))
    plt.grid(False)
    plt.savefig(f"{output_folder}/model_{index + 1}.png")
    plt.close()

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
        visualize_model(model, idx)

if __name__ == "__main__":
    main()
