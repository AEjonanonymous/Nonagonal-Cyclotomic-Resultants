# Regular Nonagon Cyclotomic Resultants and Subfield Formalization

**Overview**
This repository provides a machine-verified Lean 4 formalization isolating the composite $3\times3$ symmetry of the regular nonagon ($n=9$) entirely within the integer polynomial ring $\mathbb{Z}[x]$. The framework avoids transcendental functions, floating-point real numbers, and analysis libraries.

**Informal Claim and Formal Statement Alignment**
* **Informal Claim:** The vertex structure of the regular nonagon contains a cubic subfield generator ($x^3 - 3x + 1 = 0$) derived via cyclotomic resultants and polynomial evaluation over $\mathbb{Z}[x]$.
* **Formal Counterpart (`closed_form_evaluation`):** Proves that substituting the root sum $\zeta + \zeta^{-1}$ into `target_cubic` ($X^3 - 3X + 1$) evaluates identically to zero under the root condition of the 9th cyclotomic polynomial $\Phi_9(z) = z^6 + z^3 + 1 = 0$.

**Research Significance**
For researchers in automated reasoning and algebraic number theory, this framework offers a non-circular template for formalizing higher-order composite polygon symmetries. By restricting operations to pure ring theory; utilizing Eisenstein's criterion (`shifted_cubic_irreducible`), Gauss's pullback isomorphism (`target_cubic_irreducible_int`), and Chebyshev-analogue degree bounds (`chebyshev_natDegree_le`), the work demonstrates that complex geometric subfield structures can be cleanly verified without heavy analysis dependencies.

**Formal Verification Pipeline**
* **Step 1:** Base ring definitions for `phi_nine` ($X^6+X^3+1$), `target_cubic` ($X^3-3X+1$), and `shifted_cubic` ($X^3-3X^2+3$) in $\mathbb{Z}[x]$.
* **Step 2:** Linear variable substitution ($x \mapsto x-1$) and prime $p=3$ Eisenstein irreducibility proof for `shifted_cubic` (`shifted_cubic_irreducible`).
* **Step 3:** Integer irreducibility pullback isomorphism for `target_cubic` (`target_cubic_irreducible_int`).
* **Step 4:** Inductive degree bounds for the chord sequence `chebyshev_rel` (`chebyshev_natDegree_le`).
* **Step 5:** Homomorphic evaluation into $\mathbb{Q}(\zeta_9)$ proving exact root cancellation (`closed_form_evaluation`).

**Citation**
* Reed, Jonathan $f(n)$. (2026). Algebraic Closure and Composite Chord Symmetry of the Regular Nonagon via Cyclotomic Polynomial Resultants in Lean 4 with Comparator. Zenodo. https://doi.org/10.5281/zenodo.22644489

**License**

This project is released under the MIT License.
---

Copyright © 2026 Jonathan f(n) Reed. All rights reserved.
