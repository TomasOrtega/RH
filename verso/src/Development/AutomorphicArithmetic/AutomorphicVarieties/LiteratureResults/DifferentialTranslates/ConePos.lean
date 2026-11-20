import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.SecondFromFirstStatement

noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af
open scoped ComplexOrder MatrixOrder

namespace UpperTheory.V.Lit.Dr

/- English proof (translation)
Use `open scoped Matrix.Norms.L2Operator in`. Rewrite using `[← Matrix.isStrictlyPositive_iff_posDef, CStarAlgebra.isStrictlyPositive_iff_eq_mul_star_self]`.
-/
private theorem posDef_iff_mul_star {n : Type} [Fintype n] [DecidableEq n] (M : Matrix n n ℂ) :
    M.PosDef ↔ ∃ B : Matrix n n ℂ, IsUnit B ∧ M = B * star B := by
  open scoped Matrix.Norms.L2Operator in
  rw [← Matrix.isStrictlyPositive_iff_posDef, CStarAlgebra.isStrictlyPositive_iff_eq_mul_star_self]

/- English proof (translation)
Simplify using `only [posDef_iff_mul_star, mul_one]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨g, rfl⟩ w`. Use `⟨g.val.map (Pi.evalRingHom (fun _ => ℂ) w), ?_, ?_⟩` and prove the remaining obligations. Conclude with `g.isUnit.map (Pi.evalRingHom (fun _ : ι => ℂ) w).mapMatrix`.

Use extensionality with `i j`. Simplify using `[Matrix.mul_apply, Finset.sum_apply]`. Introduce `h choose B hB hM using h`. Establish `hu : IsUnit (Matrix.of fun i j w => B w i j : Matrix n n (ι → ℂ))`. Rewrite using `[Matrix.isUnit_iff_isUnit_det, Pi.isUnit_iff]`.

Introduce `w`. Use `RingHom.map_det (Pi.evalRingHom (fun _ : ι => ℂ) w) (Matrix.of fun i j w => B w i j : Matrix n n (ι → ℂ))` as an intermediate fact. Rewrite `this` using `[Pi.evalRingHom_apply]`. Rewrite using `[this, ← Matrix.isUnit_iff_isUnit_det]`. Conclude with `hB w`.

Use `⟨hu.unit, ?_⟩` and prove the remaining obligations. Use extensionality with `i j w`. Use `congrFun (congrFun (hM w) i) j` as an intermediate fact. Simplify using `only [Matrix.of_apply] at this`. Rewrite using `[this]`.

Simplify using `[Matrix.mul_apply, Finset.sum_apply]`.
-/
private theorem pi_iff {n ι : Type} [Fintype n] [DecidableEq n] (M : Matrix n n (ι → ℂ)) :
    (∃ g : GL n (ι → ℂ), g.val * 1 * star g.val = M) ↔ ∀ w, (Matrix.of fun i j => M i j w).PosDef := by
  simp only [posDef_iff_mul_star, mul_one]
  constructor
  · rintro ⟨g, rfl⟩ w
    refine ⟨g.val.map (Pi.evalRingHom (fun _ => ℂ) w), ?_, ?_⟩
    · exact g.isUnit.map (Pi.evalRingHom (fun _ : ι => ℂ) w).mapMatrix
    · ext i j
      simp [Matrix.mul_apply, Finset.sum_apply]
  · intro h
    choose B hB hM using h
    have hu : IsUnit (Matrix.of fun i j w => B w i j : Matrix n n (ι → ℂ)) := by
      rw [Matrix.isUnit_iff_isUnit_det, Pi.isUnit_iff]
      intro w
      have := RingHom.map_det (Pi.evalRingHom (fun _ : ι => ℂ) w) (Matrix.of fun i j w => B w i j : Matrix n n (ι → ℂ))
      rw [Pi.evalRingHom_apply] at this
      rw [this, ← Matrix.isUnit_iff_isUnit_det]
      exact hB w
    refine ⟨hu.unit, ?_⟩
    ext i j w
    have := congrFun (congrFun (hM w) i) j
    simp only [Matrix.of_apply] at this
    rw [this]
    simp [Matrix.mul_apply, Finset.sum_apply]

/- English proof (translation)
Introduce `E _ _ a p`. Use `Iff.trans ?_ (pi_iff (Matrix.of p.1))` and prove the remaining obligations. Conclude with `exists_congr fun g => Subtype.ext_iff`.
-/
theorem conePos : ConePos := by
  intro E _ _ a p
  refine Iff.trans ?_ (pi_iff (Matrix.of p.1))
  exact exists_congr fun g => Subtype.ext_iff

end UpperTheory.V.Lit.Dr
