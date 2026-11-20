import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SeriesKillsAvg
open GlobalTheory.GLq GlobalTheory.MirAvg Polynomial

noncomputable section

namespace GlobalTheory.MirAvg

open Matrix

variable {g : ℕ} [Fact g.Prime]

/- English proof (translation)
Establish `he : (Pi.single i (1 : ZMod g) : Fin r → ZMod g) ≠ 0`. Introduce `h`. Use `congrFun h i` as an intermediate fact. Simplify using `at this`. Set `f` to `(LinearEquiv.toSpanNonzeroSingleton (ZMod g) (Fin r → ZMod g) _ he).symm.trans (LinearEquiv.toSpanNonzeroSingleton (ZMod g) (Fin r → ZMod g) a ha)`.

Take `⟨e, hef⟩` from `Submodule.exists_linearEquiv_restrict_eq f`. Establish `h1 : e (Pi.single i 1) = a`. Use `hef ⟨_, Submodule.mem_span_singleton_self _⟩` as an intermediate fact. Rewrite using `[← this]`. Simplify using `only [f, LinearEquiv.trans_apply]`.

Rewrite using `[← LinearEquiv.toSpanNonzeroSingleton_one (ZMod g) (Fin r → ZMod g) _ he, LinearEquiv.symm_apply_apply, LinearEquiv.toSpanNonzeroSingleton_one]`. Use `⟨⟨LinearMap.toMatrix' e.toLinearMap, LinearMap.toMatrix' e.symm.toLinearMap, ?_, ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[← LinearMap.toMatrix'_comp]`. Simplify using the standard rewrite rules. Rewrite using `[← LinearMap.toMatrix'_comp]`.

Simplify using the standard rewrite rules. Use `show LinearMap.toMatrix' e.toLinearMap *ᵥ _ = a`. Rewrite using `[LinearMap.toMatrix'_mulVec]`. Conclude with `h1`.
-/
theorem exists_gl_mulVec_single_eq {r : ℕ} (i : Fin r) {a : Fin r → ZMod g} (ha : a ≠ 0) :
    ∃ y : Gn g r, (y : Mt g r) *ᵥ Pi.single i 1 = a := by
  have he : (Pi.single i (1 : ZMod g) : Fin r → ZMod g) ≠ 0 := by
    intro h; have := congrFun h i; simp at this
  let f := (LinearEquiv.toSpanNonzeroSingleton (ZMod g) (Fin r → ZMod g) _ he).symm.trans
    (LinearEquiv.toSpanNonzeroSingleton (ZMod g) (Fin r → ZMod g) a ha)
  obtain ⟨e, hef⟩ := Submodule.exists_linearEquiv_restrict_eq f
  have h1 : e (Pi.single i 1) = a := by
    have := hef ⟨_, Submodule.mem_span_singleton_self _⟩
    rw [← this]
    simp only [f, LinearEquiv.trans_apply]
    rw [← LinearEquiv.toSpanNonzeroSingleton_one (ZMod g) (Fin r → ZMod g) _ he, LinearEquiv.symm_apply_apply,
      LinearEquiv.toSpanNonzeroSingleton_one]
  refine ⟨⟨LinearMap.toMatrix' e.toLinearMap, LinearMap.toMatrix' e.symm.toLinearMap, ?_, ?_⟩, ?_⟩
  · rw [← LinearMap.toMatrix'_comp]; simp
  · rw [← LinearMap.toMatrix'_comp]; simp
  · show LinearMap.toMatrix' e.toLinearMap *ᵥ _ = a
    rw [LinearMap.toMatrix'_mulVec]; exact h1

/- English proof (translation)
Establish `hAB : (y : Mt g r) * (↑y⁻¹ : Mt g r) = 1` using `y.mul_inv`. Establish `hBA : (↑y⁻¹ : Mt g r) * (y : Mt g r) = 1` using `y.inv_mul`. Simplify using `only [mirSet, if_true, Units.val_mul]`. Prove the components needed by the constructor for the conclusion. Introduce `h x`.

Take `⟨c, hc⟩` from `h ((y : Mt g r) *ᵥ x)`. Use `⟨c, ?_⟩` and prove the remaining obligations. Use `congrArg (fun v => (↑y⁻¹ : Mt g r) *ᵥ v) hc` as an intermediate fact. Simplify using `only [mulVec_sub, mulVec_smul, mulVec_mulVec, ← Matrix.mul_assoc, hBA, Matrix.one_mul] at this`. Rewrite `this` using `[Matrix.mul_assoc, hBA, Matrix.mul_one, one_mulVec]`.

Conclude with `this`. Introduce `h x`. Take `⟨c, hc⟩` from `h ((↑y⁻¹ : Mt g r) *ᵥ x)`. Use `⟨c, ?_⟩` and prove the remaining obligations. Use `congrArg (fun v => (y : Mt g r) *ᵥ v) hc` as an intermediate fact.

Simplify using `only [mulVec_sub, mulVec_smul, mulVec_mulVec, ← Matrix.mul_assoc, hAB, Matrix.one_mul, one_mulVec] at this`. Rewrite using `[← this]`.
-/
theorem mirSet_true_conj {r : ℕ} (a : Fin r → ZMod g) (y z : Gn g r) :
    mirSet a true (y * z * y⁻¹) ↔ mirSet ((↑y⁻¹ : Mt g r) *ᵥ a) true z := by
  have hAB : (y : Mt g r) * (↑y⁻¹ : Mt g r) = 1 := y.mul_inv
  have hBA : (↑y⁻¹ : Mt g r) * (y : Mt g r) = 1 := y.inv_mul
  simp only [mirSet, if_true, Units.val_mul]
  constructor
  · intro h x
    obtain ⟨c, hc⟩ := h ((y : Mt g r) *ᵥ x)
    refine ⟨c, ?_⟩
    have := congrArg (fun v => (↑y⁻¹ : Mt g r) *ᵥ v) hc
    simp only [mulVec_sub, mulVec_smul, mulVec_mulVec, ← Matrix.mul_assoc, hBA, Matrix.one_mul] at this
    rw [Matrix.mul_assoc, hBA, Matrix.mul_one, one_mulVec] at this
    exact this
  · intro h x
    obtain ⟨c, hc⟩ := h ((↑y⁻¹ : Mt g r) *ᵥ x)
    refine ⟨c, ?_⟩
    have := congrArg (fun v => (y : Mt g r) *ᵥ v) hc
    simp only [mulVec_sub, mulVec_smul, mulVec_mulVec, ← Matrix.mul_assoc, hAB, Matrix.one_mul, one_mulVec] at this
    rw [← this]

/- English proof (translation)
Establish `hAB : (y : Mt g r) * (↑y⁻¹ : Mt g r) = 1` using `y.mul_inv`. Establish `hBA : (↑y⁻¹ : Mt g r) * (y : Mt g r) = 1` using `y.inv_mul`. Simplify using `only [mirSet, Bool.false_eq_true, if_false, Units.val_mul]`. Prove the components needed by the constructor for the conclusion. Introduce `h x hx`.

Rewrite `hx` using `[← dotProduct_mulVec]`. Use `h _ hx` as an intermediate fact. Use `congrArg (fun v => (↑y⁻¹ : Mt g r) *ᵥ v) this` as an intermediate fact. Simplify using `only [mulVec_mulVec, ← Matrix.mul_assoc, hBA, Matrix.one_mul] at this`. Rewrite `this` using `[Matrix.mul_assoc, hBA, Matrix.mul_one, one_mulVec]`.

Conclude with `this`. Introduce `h x hx`. Establish `h2 : (a ᵥ* (y : Mt g r)) ⬝ᵥ ((↑y⁻¹ : Mt g r) *ᵥ x) = 0`. Rewrite using `[← dotProduct_mulVec, mulVec_mulVec, hAB, one_mulVec]`. Conclude with `hx`.

Use `h _ h2` as an intermediate fact. Use `congrArg (fun v => (y : Mt g r) *ᵥ v) this` as an intermediate fact. Simplify using `only [mulVec_mulVec, hAB, one_mulVec] at this`. Rewrite using `[Matrix.mul_assoc]`. Conclude with `this`.
-/
theorem mirSet_false_conj {r : ℕ} (a : Fin r → ZMod g) (y z : Gn g r) :
    mirSet a false (y * z * y⁻¹) ↔ mirSet (a ᵥ* (y : Mt g r)) false z := by
  have hAB : (y : Mt g r) * (↑y⁻¹ : Mt g r) = 1 := y.mul_inv
  have hBA : (↑y⁻¹ : Mt g r) * (y : Mt g r) = 1 := y.inv_mul
  simp only [mirSet, Bool.false_eq_true, if_false, Units.val_mul]
  constructor
  · intro h x hx
    rw [← dotProduct_mulVec] at hx
    have := h _ hx
    have := congrArg (fun v => (↑y⁻¹ : Mt g r) *ᵥ v) this
    simp only [mulVec_mulVec, ← Matrix.mul_assoc, hBA, Matrix.one_mul] at this
    rw [Matrix.mul_assoc, hBA, Matrix.mul_one, one_mulVec] at this
    exact this
  · intro h x hx
    have h2 : (a ᵥ* (y : Mt g r)) ⬝ᵥ ((↑y⁻¹ : Mt g r) *ᵥ x) = 0 := by
      rw [← dotProduct_mulVec, mulVec_mulVec, hAB, one_mulVec]; exact hx
    have := h _ h2
    have := congrArg (fun v => (y : Mt g r) *ᵥ v) this
    simp only [mulVec_mulVec, hAB, one_mulVec] at this
    rw [Matrix.mul_assoc]; exact this

open Classical in
/- English proof (translation)
Unfold `mirEl`. Rewrite using `[MonoidAlgebra.coeff_sum, Finset.sum_apply', Finset.sum_eq_single x]`. Simplify using `[MonoidAlgebra.coeff_single]`. Introduce `h _ hne`. Simplify using `[MonoidAlgebra.coeff_single, Finsupp.single_apply, hne]`.

Introduce `h`. Conclude with `absurd (Finset.mem_univ x) h`.
-/
theorem mirEl_coeff {r : ℕ} (θ : (ZMod g)ˣ →* ℂˣ) (a : Fin r → ZMod g) (b : Bool) (x : Gn g r) :
    (mirEl θ a b).coeff x = if mirSet a b x then ((θ (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) else 0 := by
  unfold mirEl
  rw [MonoidAlgebra.coeff_sum, Finset.sum_apply', Finset.sum_eq_single x]
  · simp [MonoidAlgebra.coeff_single]
  · intro h _ hne; simp [MonoidAlgebra.coeff_single, Finsupp.single_apply, hne]
  · intro h; exact absurd (Finset.mem_univ x) h

/- English proof (translation)
Unfold `tr`. Simplify using `only [mirEl_coeff]`. Rewrite using `[← Equiv.sum_comp (MulAut.conj y).toEquiv]`. Use `Finset.sum_congr rfl fun z _ => ?_` and prove the remaining obligations. Simplify using `only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply]`.

Establish `hd : Matrix.GeneralLinearGroup.det (y * z * y⁻¹) = Matrix.GeneralLinearGroup.det z`. Rewrite using `[map_mul, map_mul, map_inv, mul_comm (Matrix.GeneralLinearGroup.det y), mul_inv_cancel_right]`. Rewrite using `[hd, hψ z y]`. Simplify using `only [H z]`.
-/
theorem tr_mirEl_conj {r : ℕ} (ψ : Gn g r → ℂ) (hψ : IsClass ψ) (θ : (ZMod g)ˣ →* ℂˣ)
    (a a' : Fin r → ZMod g) (b : Bool) (y : Gn g r) (H : ∀ z, mirSet a b (y * z * y⁻¹) ↔ mirSet a' b z) :
    tr (mirEl θ a b) ψ = tr (mirEl θ a' b) ψ := by
  classical
  unfold tr
  simp only [mirEl_coeff]
  rw [← Equiv.sum_comp (MulAut.conj y).toEquiv]
  refine Finset.sum_congr rfl fun z _ => ?_
  simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply]
  have hd : Matrix.GeneralLinearGroup.det (y * z * y⁻¹) = Matrix.GeneralLinearGroup.det z := by
    rw [map_mul, map_mul, map_inv, mul_comm (Matrix.GeneralLinearGroup.det y), mul_inv_cancel_right]
  rw [hd, hψ z y]
  simp only [H z]

end GlobalTheory.MirAvg

open GlobalTheory.GLq GlobalTheory.MirAvg Matrix in

/- English proof (translation)
Introduce `g _ n ψ hψ θ a ha b`. Consider the cases of `b with`. Consider the case `true`. Take `⟨y, hy⟩` from `exists_gl_mulVec_single_eq (0 : Fin (n + 1)) ha`. Use `tr_mirEl_conj ψ hψ θ a _ true y fun z => ?_` and prove the remaining obligations.

Rewrite using `[mirSet_true_conj, if_pos rfl, ← hy, mulVec_mulVec, y.inv_mul, one_mulVec]`. Consider the case `false`. Take `⟨P, hP⟩` from `exists_gl_mulVec_single_eq (Fin.last n) ha`. Set `y : Gn g (n + 1)` to `⟨(↑P⁻¹ : Mt g (n + 1))ᵀ, (P : Mt g (n + 1))ᵀ, by rw [← transpose_mul, P.mul_inv, transpose_one], by rw [← transpose_mul, P.inv_mul, transpose_one]⟩`. Use `tr_mirEl_conj ψ hψ θ a _ false y fun z => ?_` and prove the remaining obligations.

Rewrite using `[mirSet_false_conj]`. Establish `: a ᵥ* (y : Mt g (n + 1)) = Pi.single (Fin.last n) 1` using `by show a ᵥ* (↑P⁻¹ : Mt g (n + 1))ᵀ = _`. Rewrite using `[vecMul_transpose, ← hP, mulVec_mulVec, P.inv_mul, one_mulVec]`. Rewrite using `[this]`. Both sides reduce to the same expression.
-/
theorem GlobalTheory.MirAvg.tr_mirEl_indep : ∀ (g : ℕ) [Fact g.Prime] (n : ℕ) (ψ : Gn g (n + 1) → ℂ), IsClass ψ → ∀ (θ : (ZMod g)ˣ →* ℂˣ)
    (a : Fin (n + 1) → ZMod g), a ≠ 0 → ∀ b : Bool,
      tr (mirEl θ a b) ψ = tr (mirEl θ (if b then Pi.single 0 1 else Pi.single (Fin.last n) 1) b) ψ := by
  intro g _ n ψ hψ θ a ha b
  cases b with
  | true =>
    obtain ⟨y, hy⟩ := exists_gl_mulVec_single_eq (0 : Fin (n + 1)) ha
    refine tr_mirEl_conj ψ hψ θ a _ true y fun z => ?_
    rw [mirSet_true_conj, if_pos rfl, ← hy, mulVec_mulVec, y.inv_mul, one_mulVec]
  | false =>
    obtain ⟨P, hP⟩ := exists_gl_mulVec_single_eq (Fin.last n) ha
    let y : Gn g (n + 1) := ⟨(↑P⁻¹ : Mt g (n + 1))ᵀ, (P : Mt g (n + 1))ᵀ,
      by rw [← transpose_mul, P.mul_inv, transpose_one], by rw [← transpose_mul, P.inv_mul, transpose_one]⟩
    refine tr_mirEl_conj ψ hψ θ a _ false y fun z => ?_
    rw [mirSet_false_conj]
    have : a ᵥ* (y : Mt g (n + 1)) = Pi.single (Fin.last n) 1 := by
      show a ᵥ* (↑P⁻¹ : Mt g (n + 1))ᵀ = _
      rw [vecMul_transpose, ← hP, mulVec_mulVec, P.inv_mul, one_mulVec]
    rw [this]; rfl
