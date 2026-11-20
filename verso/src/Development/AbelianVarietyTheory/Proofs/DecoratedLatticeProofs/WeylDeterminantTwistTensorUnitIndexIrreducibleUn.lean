import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EvalAtOneExtremalMul
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsIrreducibleSmallRepUnitary
import Formalism.LocalToGlobal.Columns.PolyFnLemmas
open MvPolynomial Formalism.BasicNotions Formalism.L2.Forms Formalism.L2.Ker GlobalTheory.KJInf MeasureTheory
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.KJInf

/- English proof (translation)
Establish `: (lft (fun _ : Unit => u)).comp (rename (Prod.mk ())) = (rename (Prod.mk ())).comp (Formalism.GradedWeylDivisibility.rowAct ℂ (n` using `a) u) := by`. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce `v`. Simplify using `[lft, Formalism.GradedWeylDivisibility.rowAct, rename_X, aeval_X, map_sum]`. Conclude with `congrArg (fun φ => φ f) this`.
-/
theorem lft_rename_unit {a : ℕ} (u : Matrix (Fin a) (Fin a) ℂ) (f : MvPolynomial (Fin a × Fin a) ℂ) :
    lft (fun _ : Unit => u) (rename (Prod.mk ()) f) = rename (Prod.mk ()) (Formalism.GradedWeylDivisibility.rowAct ℂ u f) := by
  have : (lft (fun _ : Unit => u)).comp (rename (Prod.mk ())) = (rename (Prod.mk ())).comp (Formalism.GradedWeylDivisibility.rowAct ℂ (n := a) u) := by
    apply MvPolynomial.algHom_ext
    intro v
    simp [lft, Formalism.GradedWeylDivisibility.rowAct, rename_X, aeval_X, map_sum]
  exact congrArg (fun φ => φ f) this

/- English proof (translation)
Unfold `frDet`. Rewrite using `[AlgHom.map_det]`. Establish `: (lft (fun _ : Unit => u)).mapMatrix (Matrix.of fun α s : Fin a => (X ((), α, s) : PY Unit a)) = u.map C * Matrix.of fun α s : Fin a => (X ((), α, s) : PY Unit a)`. Use extensionality with `i j`. Simplify using `[lft, aeval_X, Matrix.mul_apply]`.

Rewrite using `[this, Matrix.det_mul, RingHom.map_det]`. Both sides reduce to the same expression.
-/
theorem lft_frDet_unit {a : ℕ} (u : Matrix (Fin a) (Fin a) ℂ) :
    lft (fun _ : Unit => u) (frDet ℂ a ()) = C u.det * frDet ℂ a () := by
  unfold frDet
  rw [AlgHom.map_det]
  have : (lft (fun _ : Unit => u)).mapMatrix (Matrix.of fun α s : Fin a => (X ((), α, s) : PY Unit a)) =
      u.map C * Matrix.of fun α s : Fin a => (X ((), α, s) : PY Unit a) := by
    ext i j
    simp [lft, aeval_X, Matrix.mul_apply]
  rw [this, Matrix.det_mul, RingHom.map_det]
  rfl

/- English proof (translation)
Establish `h : frDet ℂ a () = rename (Prod.mk ()) (Matrix.mvPolynomialX (Fin a) (Fin a) ℂ).det`. Unfold `frDet`. Rewrite using `[AlgHom.map_det]`. Use `congr 1`. Use extensionality with `i j`.

Simplify using `[Matrix.mvPolynomialX]`. Rewrite using `[h]`. Introduce `e`. Apply `Matrix.det_mvPolynomialX_ne_zero (Fin a) ℂ` to reduce the goal to its premises. Conclude with `rename_injective _ (Prod.mk_right_injective ()) (e.trans (map_zero _).symm)`.
-/
theorem frDet_unit_ne_zero (a : ℕ) : frDet ℂ a () ≠ 0 := by
  have h : frDet ℂ a () = rename (Prod.mk ()) (Matrix.mvPolynomialX (Fin a) (Fin a) ℂ).det := by
    unfold frDet
    rw [AlgHom.map_det]
    congr 1
    ext i j
    simp [Matrix.mvPolynomialX]
  rw [h]
  intro e
  apply Matrix.det_mvPolynomialX_ne_zero (Fin a) ℂ
  exact rename_injective _ (Prod.mk_right_injective ()) (e.trans (map_zero _).symm)

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Unfold `CSpan`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨f, hf, rfl⟩`. Use `⟨f (), hf (), ?_⟩` and prove the remaining obligations.

Simplify using `[ten]`. Introduce and unpack `_ ⟨f, hf, rfl⟩`. Apply `Submodule.subset_span` to reduce the goal to its premises. Use `⟨fun _ => f, fun _ => hf, ?_⟩` and prove the remaining obligations. Simplify using `[ten]`.
-/
theorem CSpan_unit {a : ℕ} (lam : Unit → DomWeight a) :
    CSpan lam = (delSq ℂ a (lam ())).map (rename (R := ℂ) (Prod.mk ())).toLinearMap := by
  apply le_antisymm
  · unfold CSpan
    rw [Submodule.span_le]
    rintro _ ⟨f, hf, rfl⟩
    refine ⟨f (), hf (), ?_⟩
    simp [ten]
  · rintro _ ⟨f, hf, rfl⟩
    apply Submodule.subset_span
    refine ⟨fun _ => f, fun _ => hf, ?_⟩
    simp [ten]

/- English proof (translation)
Introduce `a _ lam n`. Use `set D : PY Unit a := ∏ τ, frDet ℂ a τ ^ n τ with hDdef`. Establish `hD : D = frDet ℂ a () ^ n ()` using `by simp [D]`. Establish `hD0 : D ≠ 0` using `hD ▸ pow_ne_zero _ (frDet_unit_ne_zero a)`. Set `φ : MvPolynomial (Fin a × Fin a) ℂ →ₗ[ℂ] PY Unit a` to `LinearMap.mulRight ℂ D ∘ₗ (rename (R := ℂ) (Prod.mk ())).toLinearMap`.

Establish `hφ : ∀ f, φ f = rename (Prod.mk ()) f * D` using `fun f => rfl`. Establish `hVn : Vn lam n = (delSq ℂ a (lam ())).map φ`. Rewrite using `[Vn, CSpan_unit, ← Submodule.map_comp]`. Establish `hinj : Function.Injective φ`. Introduce `f g e`.

Rewrite `e` using `[hφ, hφ]`. Conclude with `rename_injective _ (Prod.mk_right_injective ()) (mul_right_cancel₀ hD0 e)`. Establish `hdel : delSq ℂ a (lam ()) = Formalism.GradedWeylDivisibility.dualWeyl ℂ a a (lam ()).natW`. Rewrite using `[← Formalism.L2.Col.nablaSq_eq_delSq]`. Both sides reduce to the same expression.

Establish `hanti : Antitone (lam ()).natW` using `fun i j hij => by`. Use `(lam ()).anti hij` as an intermediate fact. Simplify using `only [DomWeight.natW]`. Use linear arithmetic over natural numbers and integers. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Rewrite `h` using `[hVn]`. Establish `h2 : delSq ℂ a (lam ()) = ⊥` using `Submodule.map_injective_of_injective hinj (h.trans (Submodule.map_bot _).symm)`. Establish `hne : nablaSq ℂ a (lam ()) ≠ ⊥` using `Submodule.nontrivial_iff_ne_bot.mp inferInstance`. Conclude with `hne (by rw [Formalism.L2.Col.nablaSq_eq_delSq]; exact h2)`.

Introduce `U hU hst`. Set `M : Submodule ℂ (MvPolynomial (Fin a × Fin a) ℂ)` to `U.comap φ`. Establish `hMU : M.map φ = U`. Apply `Submodule.map_comap_eq_self` to reduce the goal to its premises. Use `hU.trans ?_` and prove the remaining obligations.

Rewrite using `[hVn]`. Conclude with `LinearMap.map_le_range`. Establish `hMd : M ≤ delSq ℂ a (lam ())`. Introduce `f hf`. Establish `h1 : φ f ∈ (delSq ℂ a (lam ())).map φ` using `hVn ▸ hU hf`.

Take `⟨g, hg, e⟩` from `h1`. Conclude with `hinj e ▸ hg`. Establish `hrow : ∀ u ∈ Matrix.unitaryGroup (Fin a) ℂ, ∀ f ∈ M, Formalism.GradedWeylDivisibility.rowAct ℂ u f ∈ M`. Introduce `u hu f hf`. Establish `h1` using `hst (fun _ => u) (fun _ => hu) (φ f) hf`.

Establish `hdet : u.det ≠ 0`. Establish `h` using `(Matrix.mem_unitaryGroup_iff.mp hu)`. Establish `h'` using `congrArg Matrix.det h`. Rewrite `h'` using `[Matrix.det_mul, Matrix.det_one]`. Conclude with `left_ne_zero_of_mul_eq_one h'`.

Establish `e : lft (fun _ : Unit => u) (φ f) = (u.det ^ n ()) • φ (Formalism.GradedWeylDivisibility.rowAct ℂ u f)`. Rewrite using `[hφ, hφ, map_mul, lft_rename_unit, hD, map_pow, lft_frDet_unit, smul_eq_C_mul, map_pow, mul_pow]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `h1` using `[e]`. Conclude with `(U.smul_mem_iff (pow_ne_zero _ hdet)).1 h1`.

Distinguish the cases in `hM : M = ⊥`. Use `left`. Rewrite using `[← hMU, hM, Submodule.map_bot]`. Use `right`. Apply `le_antisymm hU` to reduce the goal to its premises.

Rewrite using `[hVn, ← hMU]`. Apply `Submodule.map_mono` to reduce the goal to its premises. Rewrite using `[hdel]`. Conclude with `GlobalTheory.Branching.dualWeyl_le_of_rowDivClosed le_rfl _ hanti M (hdel ▸ hMd) (GlobalTheory.Branching.rowDivClosed_of_rowAct_stable M (GlobalTheory.Branching.rowAct_mem_of_unitary_stable M hrow)) hM`.
-/
theorem Vn_unit_irreducible : ∀ (a : ℕ), 0 < a → ∀ (lam : Unit → DomWeight a) (n : Unit → ℕ), Vn lam n ≠ ⊥ ∧
    ∀ U : Submodule ℂ (PY Unit a), U ≤ Vn lam n → (∀ k, IsUni k → ∀ F ∈ U, lft k F ∈ U) → U = ⊥ ∨ U = Vn lam n := by
  intro a _ lam n
  set D : PY Unit a := ∏ τ, frDet ℂ a τ ^ n τ with hDdef
  have hD : D = frDet ℂ a () ^ n () := by simp [D]
  have hD0 : D ≠ 0 := hD ▸ pow_ne_zero _ (frDet_unit_ne_zero a)
  let φ : MvPolynomial (Fin a × Fin a) ℂ →ₗ[ℂ] PY Unit a :=
    LinearMap.mulRight ℂ D ∘ₗ (rename (R := ℂ) (Prod.mk ())).toLinearMap
  have hφ : ∀ f, φ f = rename (Prod.mk ()) f * D := fun f => rfl
  have hVn : Vn lam n = (delSq ℂ a (lam ())).map φ := by
    rw [Vn, CSpan_unit, ← Submodule.map_comp]
  have hinj : Function.Injective φ := by
    intro f g e
    rw [hφ, hφ] at e
    exact rename_injective _ (Prod.mk_right_injective ()) (mul_right_cancel₀ hD0 e)
  have hdel : delSq ℂ a (lam ()) = Formalism.GradedWeylDivisibility.dualWeyl ℂ a a (lam ()).natW := by
    rw [← Formalism.L2.Col.nablaSq_eq_delSq]; rfl
  have hanti : Antitone (lam ()).natW := fun i j hij => by
    have := (lam ()).anti hij
    simp only [DomWeight.natW]
    omega
  constructor
  · intro h
    rw [hVn] at h
    have h2 : delSq ℂ a (lam ()) = ⊥ :=
      Submodule.map_injective_of_injective hinj (h.trans (Submodule.map_bot _).symm)
    have hne : nablaSq ℂ a (lam ()) ≠ ⊥ := Submodule.nontrivial_iff_ne_bot.mp inferInstance
    exact hne (by rw [Formalism.L2.Col.nablaSq_eq_delSq]; exact h2)
  · intro U hU hst
    let M : Submodule ℂ (MvPolynomial (Fin a × Fin a) ℂ) := U.comap φ
    have hMU : M.map φ = U := by
      apply Submodule.map_comap_eq_self
      refine hU.trans ?_
      rw [hVn]
      exact LinearMap.map_le_range
    have hMd : M ≤ delSq ℂ a (lam ()) := by
      intro f hf
      have h1 : φ f ∈ (delSq ℂ a (lam ())).map φ := hVn ▸ hU hf
      obtain ⟨g, hg, e⟩ := h1
      exact hinj e ▸ hg
    have hrow : ∀ u ∈ Matrix.unitaryGroup (Fin a) ℂ, ∀ f ∈ M, Formalism.GradedWeylDivisibility.rowAct ℂ u f ∈ M := by
      intro u hu f hf
      have h1 := hst (fun _ => u) (fun _ => hu) (φ f) hf
      have hdet : u.det ≠ 0 := by
        have h := (Matrix.mem_unitaryGroup_iff.mp hu)
        have h' := congrArg Matrix.det h
        rw [Matrix.det_mul, Matrix.det_one] at h'
        exact left_ne_zero_of_mul_eq_one h'
      have e : lft (fun _ : Unit => u) (φ f) = (u.det ^ n ()) • φ (Formalism.GradedWeylDivisibility.rowAct ℂ u f) := by
        rw [hφ, hφ, map_mul, lft_rename_unit, hD, map_pow, lft_frDet_unit, smul_eq_C_mul, map_pow, mul_pow]
        ring
      rw [e] at h1
      exact (U.smul_mem_iff (pow_ne_zero _ hdet)).1 h1
    by_cases hM : M = ⊥
    · left
      rw [← hMU, hM, Submodule.map_bot]
    · right
      apply le_antisymm hU
      rw [hVn, ← hMU]
      apply Submodule.map_mono
      rw [hdel]
      exact GlobalTheory.Branching.dualWeyl_le_of_rowDivClosed le_rfl _ hanti M (hdel ▸ hMd)
        (GlobalTheory.Branching.rowDivClosed_of_rowAct_stable M (GlobalTheory.Branching.rowAct_mem_of_unitary_stable M hrow)) hM
end GlobalTheory.KJInf
