"""Compare the 2024 slide estimates with the repository's rounded estimator results."""
from decimal import Decimal
from pathlib import Path


def estimator_rows():
    path = Path(__file__).resolve().parents[1] / "docs/LWE_ESTIMATOR.md"
    section = path.read_text().split("## Kyber\n", 1)[1].split("\n## ", 1)[0]
    rows = {}
    for line in section.splitlines():
        if line.startswith("| `dual`") or line.startswith("| `dual_hybrid`"):
            name, *cells = line.strip("|").split("|")
            rows[name.strip(" `")] = [Decimal(cell.strip(" *")) for cell in cells]
    return rows


def main():
    rows = estimator_rows()
    print("| Kyber | PS (2024) | dual | dual hybrid | PS − dual | PS − hybrid |")
    print("| --- | ---: | ---: | ---: | ---: | ---: |")
    for size, ps, dual, hybrid in zip(
        (512, 768, 1024), (185, 273, 376), rows["dual"], rows["dual_hybrid"], strict=True
    ):
        print(f"| {size} | {ps} | {dual} | {hybrid} | {ps-dual} | {ps-hybrid} |")


if __name__ == "__main__":
    main()
