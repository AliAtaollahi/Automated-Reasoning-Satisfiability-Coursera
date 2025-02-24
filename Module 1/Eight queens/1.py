def generate_smt2(filename="1.smt2"):
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

    inverted_diagnosis_conditions = "(not (= p q))"  

    smt2_content = f"""
(declare-fun p (Int Int) Bool)

; Placeholder for horizontal condition
(assert ; horizontal
    {horizontal_conditions}
)

; Placeholder for vertical condition
(assert ; vertical
    {vertical_conditions}
)

; Placeholder for row condition
(assert ; row
    {row_conditions}
)

; Placeholder for column condition
(assert ; column
    {col_conditions}
)

; Placeholder for diagnosis condition
(assert ; diagnosis
    {diagnosis_conditions}
)

; Placeholder for inverted-diagnosis condition
(assert ; inverted-diagnosis
    (and
        {inverted_diagnosis_conditions}
    )
)

(check-sat)
(get-model)
(exit)
"""

    with open(filename, "w") as f:
        f.write(smt2_content)

    print(f"SMT2 file '{filename}' has been generated.")

generate_smt2()