import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HomogeneousLocalization.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace NumberField GroundTheory.Arith.SchemeCoh

universe u

noncomputable section

namespace SectionsLatticeFS

open ProjScheme

/- English proof (translation)
Introduce `A _ N n ρ x j hj s`. Use `set k := CP.chartIndex x.1`. Establish `hk : x.1.rep k ≠ 0` using `rep_chartIndex_ne_zero x.1`. Establish `hP : (MvPolynomial.X k : MvPolynomial (Fin (N + 1)) A) ^ n ∈ ProjSpace.grading A N n` using `(MvPolynomial.mem_homogeneousSubmodule _ _).mpr (MvPolynomial.isHomogeneous_X_pow k n)`. Use `set w := (self A N).evalGlobalSection (twistN A N n) x (polySection hP)`.

Use `set ek := fsFrameCoord n ρ x`. Use `set ej := fibreEquivComplex ((self A N).evalAtPoint x) (point_mem_stdOpen x hj) (isBasisOn_frame (A := A) j n)`. Establish `hev : evalAt ρ x.1.rep ((MvPolynomial.X k : MvPolynomial (Fin (N + 1)) A) ^ n) = x.1.rep k ^ n` using `by simp [evalAt]`. Establish `hwk : ek w = 1`. Establish `h1` using `h A N n ρ _ hP x k hk`.

Rewrite `h1` using `[hev]`. Conclude with `mul_right_cancel₀ (pow_ne_zero n hk) (h1.trans (one_mul _).symm)`. Establish `hwj : ej w * x.1.rep j ^ n = x.1.rep k ^ n`. Establish `h1` using `h A N n ρ _ hP x j hj`. Rewrite `h1` using `[hev]`. Then use the resulting hypothesis.

Establish `hs : s = ek s • w`. Apply `ek.injective` to reduce the goal to its premises. Rewrite using `[LinearEquiv.map_smul, hwk, smul_eq_mul, mul_one]`. Establish `hnj : ‖ej w‖ * ‖x.1.rep j‖ ^ n = ‖x.1.rep k‖ ^ n`. Rewrite using `[← norm_pow, ← norm_pow, ← norm_mul, hwj]`.

Establish `hfs : fsFibreNorm n ρ x s = ‖ek s‖ * ‖x.1.rep k‖ ^ n / norm2 x.1.rep ^ n` using `rfl`. Rewrite using `[hfs]`. Use `conv_rhs => rw [hs, LinearEquiv.map_smul, smul_eq_mul, norm_mul, mul_assoc, hnj]`.
-/
theorem FSIndex.proof (h : FSCoord.Statement.{u}) : FSIndex.Statement.{u} := by
  intro A _ N n ρ x j hj s
  set k := CP.chartIndex x.1
  have hk : x.1.rep k ≠ 0 := rep_chartIndex_ne_zero x.1
  have hP : (MvPolynomial.X k : MvPolynomial (Fin (N + 1)) A) ^ n ∈ ProjSpace.grading A N n :=
    (MvPolynomial.mem_homogeneousSubmodule _ _).mpr (MvPolynomial.isHomogeneous_X_pow k n)
  set w := (self A N).evalGlobalSection (twistN A N n) x (polySection hP)
  set ek := fsFrameCoord n ρ x
  set ej := fibreEquivComplex ((self A N).evalAtPoint x) (point_mem_stdOpen x hj)
    (isBasisOn_frame (A := A) j n)
  have hev : evalAt ρ x.1.rep ((MvPolynomial.X k : MvPolynomial (Fin (N + 1)) A) ^ n) =
      x.1.rep k ^ n := by simp [evalAt]
  have hwk : ek w = 1 := by
    have h1 := h A N n ρ _ hP x k hk
    rw [hev] at h1
    exact mul_right_cancel₀ (pow_ne_zero n hk) (h1.trans (one_mul _).symm)
  have hwj : ej w * x.1.rep j ^ n = x.1.rep k ^ n := by
    have h1 := h A N n ρ _ hP x j hj
    rwa [hev] at h1

  have hs : s = ek s • w := by
    apply ek.injective
    rw [LinearEquiv.map_smul, hwk, smul_eq_mul, mul_one]
  have hnj : ‖ej w‖ * ‖x.1.rep j‖ ^ n = ‖x.1.rep k‖ ^ n := by
    rw [← norm_pow, ← norm_pow, ← norm_mul, hwj]
  have hfs : fsFibreNorm n ρ x s = ‖ek s‖ * ‖x.1.rep k‖ ^ n / norm2 x.1.rep ^ n := rfl
  rw [hfs]
  conv_rhs => rw [hs, LinearEquiv.map_smul, smul_eq_mul, norm_mul, mul_assoc, hnj]

/- English proof (translation)
The claim follows from `FSIndex.proof h _ _ _ _ _ _ pointQ_rep_ne_zero _`.
-/
example (h : FSCoord.Statement.{0}) (s : (self (𝓞 ℚ) 1).Fibre (twistN (𝓞 ℚ) 1 1) pointQ) :
    fsFibreNorm 1 _ pointQ s =
      ‖fibreEquivComplex ((self (𝓞 ℚ) 1).evalAtPoint pointQ) (point_mem_stdOpen pointQ pointQ_rep_ne_zero)
          (isBasisOn_frame (A := 𝓞 ℚ) 0 1) s‖ * ‖pointQ.1.rep 0‖ ^ 1 / norm2 pointQ.1.rep ^ 1 :=
  FSIndex.proof h _ _ _ _ _ _ pointQ_rep_ne_zero _

end SectionsLatticeFS

end

end GroundTheory.Heights₂.Heights
