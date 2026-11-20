import Mathlib
import Formalism.SatakeDualWeyl.Statement
import Lemmata.MiscLemmasI.Imports

open Matrix
open scoped ComplexOrder

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.WbDefC

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[Formalism.UG.cT, Matrix.conjTranspose_apply]`.
-/
theorem cT_eq_conjTranspose {m k : Type} (P : Matrix m k ℂ) :
    Formalism.UG.cT (starRingEnd ℂ) P = Pᴴ := by
  ext i j
  simp [Formalism.UG.cT, Matrix.conjTranspose_apply]

/- English proof (translation)
Establish `hr : w ∘ Sum.inr = 0` using `funext hw`. Use extensionality with `x`. Break down `x with i | j` into its components or cases. Simplify using `[Formalism.UG.Jpq, Matrix.fromBlocks_mulVec, hr]`. Simplify using `[Formalism.UG.Jpq, Matrix.fromBlocks_mulVec, hr, hw]`.
-/
theorem jpq_mulVec_of_inr {p q : ℕ} (w : Fin p ⊕ Fin q → ℂ) (hw : ∀ j, w (Sum.inr j) = 0) :
    Formalism.UG.Jpq p q *ᵥ w = w := by
  have hr : w ∘ Sum.inr = 0 := funext hw
  ext x
  rcases x with i | j
  · simp [Formalism.UG.Jpq, Matrix.fromBlocks_mulVec, hr]
  · simp [Formalism.UG.Jpq, Matrix.fromBlocks_mulVec, hr, hw]

/- English proof (translation)
Take `⟨e, P, hP⟩` from `hJ`. Rewrite `hP` using `[cT_eq_conjTranspose]`. Use `set Q : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ := (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) with hQ`. Use `set Qi : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ := ((P⁻¹ : GL (Fin p ⊕ Fin q) ℂ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) with hQi`. Establish `hQQi : Q * Qi = 1`.

Rewrite using `[hQ, hQi, ← Units.val_mul, mul_inv_cancel, Units.val_one]`. Establish `key : ∀ v : n → ℂ, star v ⬝ᵥ (J *ᵥ v) = star (Qi *ᵥ (v ∘ e.symm)) ⬝ᵥ (Formalism.UG.Jpq p q *ᵥ (Qi *ᵥ (v ∘ e.symm)))`. Introduce `v`. Establish `hv : Q *ᵥ (Qi *ᵥ (v ∘ e.symm)) = v ∘ e.symm`. Rewrite using `[Matrix.mulVec_mulVec, hQQi, Matrix.one_mulVec]`.

Use `conv_rhs =>`. Rewrite using `[← hP, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hv, dotProduct_mulVec, ← Matrix.star_mulVec, hv, Matrix.reindex_apply, Matrix.submatrix_mulVec_equiv]`. Simplify using `only [dotProduct]`. Conclude with `Fintype.sum_equiv e _ _ (fun i => by simp [Function.comp_def])`. Assume the negation of the conclusion as `hlt`.

Use `push_neg at hlt`. Set `L : (ι → ℂ) →ₗ[ℂ] (Fin q → ℂ)` to `(LinearMap.funLeft ℂ ℂ Sum.inr) ∘ₗ (Matrix.mulVecLin Qi) ∘ₗ (LinearMap.funLeft ℂ ℂ e.symm) ∘ₗ (Fintype.linearCombination ℂ u)`. Establish `hker : LinearMap.ker L ≠ ⊥` using `LinearMap.ker_ne_bot_of_finrank_lt (by simpa using hlt)`. Take `⟨d, hdk, hd0⟩` from `(Submodule.ne_bot_iff _).1 hker`. Establish `hLd : L d = 0` using `hdk`.

Establish `hyr : ∀ j, (Qi *ᵥ ((∑ a, d a • u a) ∘ e.symm)) (Sum.inr j) = 0`. Introduce `j`. Use `congrFun hLd j` as an intermediate fact. Simplify using `only [L, LinearMap.comp_apply, Matrix.mulVecLin_apply, Fintype.linearCombination_apply] at this`. Conclude with `this`.

Establish `hform` using `hneg d`. Rewrite `hform` using `[key, jpq_mulVec_of_inr _ hyr]`. Use `set y := Qi *ᵥ ((∑ a, d a • u a) ∘ e.symm) with hy`. Establish `hnn : 0 ≤ star y ⬝ᵥ y` using `dotProduct_star_self_nonneg y`. Establish `hz : star y ⬝ᵥ y = 0`.

Rewrite `hnn` using `[Complex.nonneg_iff]`. Apply `Complex.ext` to reduce the goal to its premises. Simplify using `only [Complex.zero_re]`. Combine the linear relations using `[hnn.1]`. Simplify using `using hnn.2.symm`.

Establish `hy0 : y = 0` using `dotProduct_star_self_eq_zero.1 hz`. Establish `hv0 : (∑ a, d a • u a) ∘ e.symm = 0`. Rewrite using `[← Matrix.one_mulVec ((∑ a, d a • u a) ∘ e.symm), ← hQQi, ← Matrix.mulVec_mulVec, ← hy, hy0, Matrix.mulVec_zero]`. Establish `hsum : ∑ a, d a • u a = 0`. Use function extensionality and compare the values at `x`.

Use `congrFun hv0 (e x)` as an intermediate fact. Simplify using `using this`. Conclude with `hd0 (funext (Fintype.linearIndependent_iff.1 hu d hsum))`.
-/
theorem sigNeg_card_le {n ι : Type} [Fintype n] [DecidableEq n] [Fintype ι]
    (J : Matrix n n ℂ) (p q : ℕ) (hJ : Formalism.UG.HasSignature J p q) (u : ι → n → ℂ)
    (hu : LinearIndependent ℂ u)
    (hneg : ∀ d : ι → ℂ, (star (∑ a, d a • u a) ⬝ᵥ (J *ᵥ ∑ a, d a • u a)).re ≤ 0) :
    Fintype.card ι ≤ q := by
  classical
  obtain ⟨e, P, hP⟩ := hJ
  rw [cT_eq_conjTranspose] at hP
  set Q : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ := (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) with hQ
  set Qi : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ := ((P⁻¹ : GL (Fin p ⊕ Fin q) ℂ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) with hQi
  have hQQi : Q * Qi = 1 := by
    rw [hQ, hQi, ← Units.val_mul, mul_inv_cancel, Units.val_one]

  have key : ∀ v : n → ℂ, star v ⬝ᵥ (J *ᵥ v) =
      star (Qi *ᵥ (v ∘ e.symm)) ⬝ᵥ (Formalism.UG.Jpq p q *ᵥ (Qi *ᵥ (v ∘ e.symm))) := by
    intro v
    have hv : Q *ᵥ (Qi *ᵥ (v ∘ e.symm)) = v ∘ e.symm := by
      rw [Matrix.mulVec_mulVec, hQQi, Matrix.one_mulVec]
    conv_rhs =>
      rw [← hP, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hv, dotProduct_mulVec,
        ← Matrix.star_mulVec, hv, Matrix.reindex_apply, Matrix.submatrix_mulVec_equiv]
    simp only [dotProduct]
    exact Fintype.sum_equiv e _ _ (fun i => by simp [Function.comp_def])
  by_contra hlt
  push_neg at hlt
  let L : (ι → ℂ) →ₗ[ℂ] (Fin q → ℂ) :=
    (LinearMap.funLeft ℂ ℂ Sum.inr) ∘ₗ (Matrix.mulVecLin Qi) ∘ₗ
      (LinearMap.funLeft ℂ ℂ e.symm) ∘ₗ (Fintype.linearCombination ℂ u)
  have hker : LinearMap.ker L ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt (by simpa using hlt)
  obtain ⟨d, hdk, hd0⟩ := (Submodule.ne_bot_iff _).1 hker
  have hLd : L d = 0 := hdk
  have hyr : ∀ j, (Qi *ᵥ ((∑ a, d a • u a) ∘ e.symm)) (Sum.inr j) = 0 := by
    intro j
    have := congrFun hLd j
    simp only [L, LinearMap.comp_apply, Matrix.mulVecLin_apply, Fintype.linearCombination_apply] at this
    exact this
  have hform := hneg d
  rw [key, jpq_mulVec_of_inr _ hyr] at hform
  set y := Qi *ᵥ ((∑ a, d a • u a) ∘ e.symm) with hy
  have hnn : 0 ≤ star y ⬝ᵥ y := dotProduct_star_self_nonneg y
  have hz : star y ⬝ᵥ y = 0 := by
    rw [Complex.nonneg_iff] at hnn
    apply Complex.ext
    · simp only [Complex.zero_re]; linarith [hnn.1]
    · simpa using hnn.2.symm
  have hy0 : y = 0 := dotProduct_star_self_eq_zero.1 hz
  have hv0 : (∑ a, d a • u a) ∘ e.symm = 0 := by
    rw [← Matrix.one_mulVec ((∑ a, d a • u a) ∘ e.symm), ← hQQi, ← Matrix.mulVec_mulVec, ← hy, hy0,
      Matrix.mulVec_zero]
  have hsum : ∑ a, d a • u a = 0 := by
    funext x
    have := congrFun hv0 (e x)
    simpa using this
  exact hd0 (funext (Fintype.linearIndependent_iff.1 hu d hsum))

/- English proof (translation)
Apply the tactic sequence `first | exact Bl.SecondBlockLemmaJ.goal1 .. | (apply Bl.SecondBlockLemmaJ.goal1 <;> assumption) | (intros; apply Bl.SecondBlockLemmaJ.goal1 <;> assumption) | (apply @Bl.SecondBlockLemmaJ.goal1 <;> assumption) | (intros; apply @Bl.SecondBlockLemmaJ.goal1 <;> assumption) | (apply @ …`.
-/
theorem linIndep_map {K L ι n : Type} [Field K] [Field L] [Fintype ι] [Fintype n] [DecidableEq ι]
    [DecidableEq n] (τ : K →+* L) (c : ι → n → K) (hc : LinearIndependent K c) :
    LinearIndependent L (fun a => fun i => τ (c a i)) := by
  first | exact Bl.SecondBlockLemmaJ.goal1 .. | (apply Bl.SecondBlockLemmaJ.goal1 <;> assumption) | (intros; apply Bl.SecondBlockLemmaJ.goal1 <;> assumption) | (apply @Bl.SecondBlockLemmaJ.goal1 <;> assumption) | (intros; apply @Bl.SecondBlockLemmaJ.goal1 <;> assumption) | (apply @Bl.SecondBlockLemmaJ.goal1 <;> first | assumption | infer_instance)

end PI.UnitaryGroupMassFormula.CntFormula.WbDefC
