import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StarMulOfMemKc

noncomputable section
namespace GlobalTheory.CartanInt.UnitLog
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU GlobalTheory.IndefiniteRowSideFullHecke.CartanCoshPower GlobalTheory.CartanInt Matrix MeasureTheory
open scoped Matrix.Norms.L2Operator

/- English proof (translation)
Establish `h` using `A.l2_opNorm_mulVec (EuclideanSpace.single b (1 : ℂ))`. Establish `h2` using `PiLp.norm_apply_le ((EuclideanSpace.equiv n ℂ).symm (A *ᵥ (EuclideanSpace.single b (1 : ℂ)))) a`. Simplify using `only [EuclideanSpace.norm_single, norm_one, mul_one] at h`. Use `le_trans ?_ (h2.trans h)` and prove the remaining obligations. Simplify using the standard rewrite rules.
-/
theorem norm_entry_le {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) (a b : n) :
    ‖A a b‖ ≤ ‖A‖ := by
  have h := A.l2_opNorm_mulVec (EuclideanSpace.single b (1 : ℂ))
  have h2 := PiLp.norm_apply_le ((EuclideanSpace.equiv n ℂ).symm (A *ᵥ (EuclideanSpace.single b (1 : ℂ)))) a
  simp only [EuclideanSpace.norm_single, norm_one, mul_one] at h
  refine le_trans ?_ (h2.trans h)
  simp

/- English proof (translation)
Establish `hn : IsStarNormal u` using `isStarNormal_of_mem_unitary hu`. Establish `hfin : (spectrum ℂ u).Finite` using `Matrix.finite_spectrum u`. Establish `hsph : ∀ z ∈ spectrum ℂ u, ‖z‖ = 1` using `fun z hz => by`. Simplify using `using spectrum.subset_circle_of_unitary hu hz`. Use `⟨cfc (fun z : ℂ => (Complex.arg z : ℂ)) u, ?_, ?_, ?_, fun J h1 h2 => h1.cfc h2 _⟩` and prove the remaining obligations.

Rewrite using `[← Matrix.star_eq_conjTranspose, ← cfc_star]`. Use `cfc_congr fun z _ => ?_` and prove the remaining obligations. Simplify using the standard rewrite rules. Use `norm_cfc_le Real.pi_pos.le fun z _ => ?_` and prove the remaining obligations. Simplify using `using Complex.abs_arg_le_pi z`.

Rewrite using `[← cfc_const_mul Complex.I _ u (hf := hfin.continuousOn _), ← CFC.exp_eq_normedSpace_exp (𝕜 := ℂ), ← Complex.exp_eq_exp_ℂ, ← cfc_comp' Complex.exp _ u (hf := hfin.continuousOn _)] conv_lhs => rw [← cfc_id' ℂ u]`. Use `cfc_congr fun z hz => ?_` and prove the remaining obligations. Use `Complex.norm_mul_exp_arg_mul_I z` as an intermediate fact. Rewrite `this` using `[hsph z hz, mul_comm _ Complex.I]`. Simplify using `using this.symm`.
-/
theorem exists_log {n : Type} [Fintype n] [DecidableEq n] (u : Matrix n n ℂ)
    (hu : u ∈ unitary (Matrix n n ℂ)) :
    ∃ H : Matrix n n ℂ, Hᴴ = H ∧ ‖H‖ ≤ Real.pi ∧ u = NormedSpace.exp (Complex.I • H) ∧
      ∀ J, Commute u J → Commute (star u) J → Commute H J := by
  have hn : IsStarNormal u := isStarNormal_of_mem_unitary hu
  have hfin : (spectrum ℂ u).Finite := Matrix.finite_spectrum u
  have hsph : ∀ z ∈ spectrum ℂ u, ‖z‖ = 1 := fun z hz => by
    simpa using spectrum.subset_circle_of_unitary hu hz
  refine ⟨cfc (fun z : ℂ => (Complex.arg z : ℂ)) u, ?_, ?_, ?_, fun J h1 h2 => h1.cfc h2 _⟩
  · rw [← Matrix.star_eq_conjTranspose, ← cfc_star]
    refine cfc_congr fun z _ => ?_
    simp
  · refine norm_cfc_le Real.pi_pos.le fun z _ => ?_
    simpa using Complex.abs_arg_le_pi z
  · rw [← cfc_const_mul Complex.I _ u (hf := hfin.continuousOn _),
      ← CFC.exp_eq_normedSpace_exp (𝕜 := ℂ), ← Complex.exp_eq_exp_ℂ,
      ← cfc_comp' Complex.exp _ u (hf := hfin.continuousOn _)]
    conv_lhs => rw [← cfc_id' ℂ u]
    refine cfc_congr fun z hz => ?_
    have := Complex.norm_mul_exp_arg_mul_I z
    rw [hsph z hz, mul_comm _ Complex.I] at this
    simpa using this.symm

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Use extensionality with `a b`. Establish `h1` using `h a b`. Apply the tactic sequence `rcases a with i | i <;> rcases b with j | j <;>`.

Simplify using `[sameBlock, Formalism.UG.Jpq, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]`. Introduce `h a b hab`. Establish `h1` using `congrFun (congrFun h.eq a) b`. Apply the tactic sequence `rcases a with i | i <;> rcases b with j | j <;>`. Simplify using `[sameBlock, Formalism.UG.Jpq, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply] at h1 hab ⊢`.

Take the linear combination `(-1 / 2 : ℂ) * h1`. Take the linear combination `(1 / 2 : ℂ) * h1`.
-/
theorem isKC_iff_commute {p q : ℕ} (X : Mat p q) : IsKC X ↔ Commute X (Formalism.UG.Jpq p q) := by
  constructor
  · intro h
    ext a b
    have h1 := h a b
    rcases a with i | i <;> rcases b with j | j <;>
      simp_all [sameBlock, Formalism.UG.Jpq, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]
  · intro h a b hab
    have h1 := congrFun (congrFun h.eq a) b
    rcases a with i | i <;> rcases b with j | j <;>
      simp [sameBlock, Formalism.UG.Jpq, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply] at h1 hab ⊢
    · linear_combination (-1 / 2 : ℂ) * h1
    · linear_combination (1 / 2 : ℂ) * h1

/- English proof (translation)
Introduce `p q k hk`. Establish `hu : (UpqT.mat k : Mat p q) ∈ unitary (Mat p q)` using `Matrix.mem_unitaryGroup_iff'.2 (star_mul_of_mem_Kc hk)`. Take `⟨H, h1, h2, h3, h4⟩` from `exists_log _ hu`. Use `⟨H, h1, (isKC_iff_commute H).2 (h4 _ ((isKC_iff_commute _).1 hk) ?_), fun a b => (norm_entry_le H a b).trans h2, h3⟩` and prove the remaining obligations. Rewrite using `[Matrix.star_eq_conjTranspose, ← mat_inv_of_mem_Kc hk]`.

Conclude with `(isKC_iff_commute _).1 ((Ksg p q).inv_mem hk)`.
-/
theorem exists_unitlog : ∀ (p q : ℕ) (k : UpqT p q), k ∈ Kc p q → ∃ H : Mat p q, Hᴴ = H ∧ IsKC H ∧
    (∀ a b, ‖H a b‖ ≤ Real.pi) ∧ UpqT.mat k = NormedSpace.exp (Complex.I • H) := by
  intro p q k hk
  have hu : (UpqT.mat k : Mat p q) ∈ unitary (Mat p q) :=
    Matrix.mem_unitaryGroup_iff'.2 (star_mul_of_mem_Kc hk)
  obtain ⟨H, h1, h2, h3, h4⟩ := exists_log _ hu
  refine ⟨H, h1, (isKC_iff_commute H).2 (h4 _ ((isKC_iff_commute _).1 hk) ?_),
    fun a b => (norm_entry_le H a b).trans h2, h3⟩
  rw [Matrix.star_eq_conjTranspose, ← mat_inv_of_mem_Kc hk]
  exact (isKC_iff_commute _).1 ((Ksg p q).inv_mem hk)

end GlobalTheory.CartanInt.UnitLog
