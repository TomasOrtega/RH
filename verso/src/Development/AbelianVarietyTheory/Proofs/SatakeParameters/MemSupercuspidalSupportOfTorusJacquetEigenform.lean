import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIwVecTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.DepthZeroJacquetInjective
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCuspidalIffCompositions
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PrincipalSeriesSubquotientOfCharacters
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JordanHolderMultiplicityJacquetEqBorelJacquetOfS
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InstAddCommGroupTwo
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.ThetaGL GlobalTheory.TameIwahori ValuativeRel

open GlobalTheory.SmGL.EmptyBlocks GlobalTheory.SmGL.Exponents

namespace GlobalTheory.EigenSupport

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem jac_mk {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)]
    [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] {V : Type} [AddCommGroup V] [Module ℂ V]
    (e : (a : α) × m a ≃ n) (π : Representation ℂ (GL n k) V) (g : Levi k m) (v : V) :
    jac e π g (Submodule.Quotient.mk v) =
      (((deltaHalf k m g)⁻¹ : ℂˣ) : ℂ) • (Submodule.Quotient.mk (π (leviEmb k e g) v) : Jacquet π (unipRad k e)) := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem jacB_mk {n : Type} [Fintype n] [DecidableEq n] [LinearOrder n] {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL n k) V) (t : n → kˣ) (v : V) :
    jacB π t (Submodule.Quotient.mk v) =
      (((deltaHalf k (fun _ : n => Unit) (leviTorus k n t))⁻¹ : ℂˣ) : ℂ) •
        (Submodule.Quotient.mk (π (leviEmb k (points n) (leviTorus k n t)) v) : Jacquet π (unipB k n)) := rfl

/- English proof (translation)
Use function extensionality and compare the values at `j`. Use extensionality with `a b`. Rewrite using `[val_torusToLevi]`. Simplify using `[leviTorus, points, Matrix.diagonal]`.
-/
theorem leviTorus_eq {n : Type} [Fintype n] [DecidableEq n] [LinearOrder n] (t : n → kˣ) :
    leviTorus k n t = torusToLevi k (points n) t := by
  funext j; ext a b
  rw [val_torusToLevi]
  simp [leviTorus, points, Matrix.diagonal]

/- English proof (translation)
Use function extensionality and compare the values at `j`. Use extensionality with `a b`. Rewrite using `[val_torusToLevi]`. Use `fin_cases a`. Use `fin_cases b`.

Simplify using `[Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_one]`.
-/
theorem eq_torusToLevi (n : ℕ) (g : Levi k (fun _ : Fin n => Fin 1)) :
    g = torusToLevi k (Equiv.sigmaUnique (Fin n) fun _ => Fin 1) (fun j => Matrix.GeneralLinearGroup.det (g j)) := by
  funext j; ext a b
  rw [val_torusToLevi]
  fin_cases a; fin_cases b
  simp [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_one]

/- English proof (translation)
Rewrite using `[deltaHalf_apply, deltaHalf_apply]`. Use `Finset.prod_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[modExp_fin (fun _ : Fin n => Fin 1) (fun _ => by simp), modExp_fin (fun _ : Fin n => Unit) (fun _ => by simp)]`. Conclude with `congrArg _ (congrFun ((leviTorus k (Fin n)).symm_apply_apply (fun j => Matrix.GeneralLinearGroup.det (g j))) a).symm`.
-/
theorem deltaHalf_eq (n : ℕ) (g : Levi k (fun _ : Fin n => Fin 1)) :
    deltaHalf k (fun _ : Fin n => Fin 1) g =
      deltaHalf k (fun _ : Fin n => Unit) (leviTorus k (Fin n) (fun j => Matrix.GeneralLinearGroup.det (g j))) := by
  rw [deltaHalf_apply, deltaHalf_apply]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [modExp_fin (fun _ : Fin n => Fin 1) (fun _ => by simp), modExp_fin (fun _ : Fin n => Unit) (fun _ => by simp)]
  exact congrArg _ (congrFun ((leviTorus k (Fin n)).symm_apply_apply (fun j => Matrix.GeneralLinearGroup.det (g j))) a).symm

/- English proof (translation)
Set `f` to `Equiv.sigmaUnique (Fin n) fun _ : Fin n => Fin 1`. Establish `hmono : StrictMono (blk f)` using `fun a b h => by simpa [blk, f] using h`. Establish `h : unipRad k f = unipB k (Fin n)` using `unipRad_eq k f hmono`. Set `l' : Jacquet π (unipRad k f) →ₗ[ℂ] ℂ` to `(twKer π (unipRad k f) 1).liftQ (l ∘ₗ (twKer π (unipB k (Fin n)) 1).mkQ) (by`. Rewrite using `[h]`.

Introduce `x hx`. Simplify using `[(Submodule.Quotient.mk_eq_zero _).mpr hx])`. Establish `hl' : ∀ v : V, l' (Submodule.Quotient.mk v) = l (Submodule.Quotient.mk v)` using `fun v => rfl`. Set `χ : Levi k (fun _ : Fin n => Fin 1) →* ℂˣ` to `leviChar _ ψ`. Establish `key : ∀ (g : Levi k (fun _ : Fin n => Fin 1)) (v : V), l' (jac f π g (Submodule.Quotient.mk v)) = (χ g : ℂ) * l' (Submodule.Quotient.mk v)`.

Introduce `g v`. Use `set t : Fin n → kˣ := fun j => Matrix.GeneralLinearGroup.det (g j) with ht`. Establish `h1` using `hl t (Submodule.Quotient.mk v)`. Rewrite `h1` using `[jacB_mk, map_smul, leviTorus_eq, leviEmb_torusToLevi, ← leviTorus_eq]`. Establish `hEmb : leviEmb k f g = diagT k (Fin n) t` using `by conv_lhs => rw [eq_torusToLevi n g]`.

Conclude with `leviEmb_torusToLevi k f t`. Rewrite using `[jac_mk, map_smul, hl', hl', deltaHalf_eq n g, hEmb, ← ht]`. Establish `hc : (χ g : ℂ) = (torusChar ψ t : ℂ)`. Simplify using `[χ, leviChar_apply, torusChar_apply, t]`. Rewrite using `[hc, ← h1]`.

Use `⟨n, fun _ => 1, f, i, rfl, ℂ, inferInstance, inferInstance, ofChar χ, isIrreducible_ofChar χ, ?_, ?_⟩` and prove the remaining obligations. Use `IsSubquotient.of_surjective ⟨l', fun g => ?_⟩ ?_` and prove the remaining obligations. Apply `Submodule.linearMap_qext` to reduce the goal to its premises. Use extensionality with `v`. Simplify using `only [LinearMap.comp_apply, Submodule.mkQ_apply]`.

Rewrite using `[key, ofChar_apply]`. Choose the witnesses or unpack the hypotheses as in `⟨x, hx⟩ : ∃ x, l x ≠ 0 := by`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Conclude with `hl0 (LinearMap.ext hc)`.

Take `⟨v, rfl⟩` from `Submodule.Quotient.mk_surjective _ x`. Introduce `c`. Use `⟨(c / l (Submodule.Quotient.mk v)) • Submodule.Quotient.mk v, ?_⟩` and prove the remaining obligations. Use `show l' _ = c`. Rewrite using `[map_smul, hl', smul_eq_mul, div_mul_cancel₀ _ hx]`.

Introduce `g y`. Rewrite using `[ofChar_apply]`. Simplify using `[χ, leviChar_apply, Pi.mulSingle_apply, apply_ite, Finset.prod_ite_eq']`.
-/
theorem inSupport_of_eigenform (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin n) k) V) (ψ : Fin n → kˣ →* ℂˣ)
    (l : Jacquet π (unipB k (Fin n)) →ₗ[ℂ] ℂ) (hl0 : l ≠ 0)
    (hl : ∀ t y, l (jacB π t y) = (torusChar ψ t : ℂ) * l y) (i : Fin n) : InSupport π (ψ i) := by
  let f := Equiv.sigmaUnique (Fin n) fun _ : Fin n => Fin 1
  have hmono : StrictMono (blk f) := fun a b h => by simpa [blk, f] using h
  have h : unipRad k f = unipB k (Fin n) := unipRad_eq k f hmono
  let l' : Jacquet π (unipRad k f) →ₗ[ℂ] ℂ :=
    (twKer π (unipRad k f) 1).liftQ (l ∘ₗ (twKer π (unipB k (Fin n)) 1).mkQ) (by
      rw [h]; intro x hx
      simp [(Submodule.Quotient.mk_eq_zero _).mpr hx])
  have hl' : ∀ v : V, l' (Submodule.Quotient.mk v) = l (Submodule.Quotient.mk v) := fun v => rfl
  let χ : Levi k (fun _ : Fin n => Fin 1) →* ℂˣ := leviChar _ ψ
  have key : ∀ (g : Levi k (fun _ : Fin n => Fin 1)) (v : V),
      l' (jac f π g (Submodule.Quotient.mk v)) = (χ g : ℂ) * l' (Submodule.Quotient.mk v) := by
    intro g v
    set t : Fin n → kˣ := fun j => Matrix.GeneralLinearGroup.det (g j) with ht
    have h1 := hl t (Submodule.Quotient.mk v)
    rw [jacB_mk, map_smul, leviTorus_eq, leviEmb_torusToLevi, ← leviTorus_eq] at h1
    have hEmb : leviEmb k f g = diagT k (Fin n) t := by
      conv_lhs => rw [eq_torusToLevi n g]
      exact leviEmb_torusToLevi k f t
    rw [jac_mk, map_smul, hl', hl', deltaHalf_eq n g, hEmb, ← ht]
    have hc : (χ g : ℂ) = (torusChar ψ t : ℂ) := by
      simp [χ, leviChar_apply, torusChar_apply, t]
    rw [hc, ← h1]
  refine ⟨n, fun _ => 1, f, i, rfl, ℂ, inferInstance, inferInstance, ofChar χ, isIrreducible_ofChar χ, ?_, ?_⟩
  · refine IsSubquotient.of_surjective ⟨l', fun g => ?_⟩ ?_
    · apply Submodule.linearMap_qext
      ext v
      simp only [LinearMap.comp_apply, Submodule.mkQ_apply]
      rw [key, ofChar_apply]
    · obtain ⟨x, hx⟩ : ∃ x, l x ≠ 0 := by
        by_contra hc; push_neg at hc; exact hl0 (LinearMap.ext hc)
      obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      intro c
      refine ⟨(c / l (Submodule.Quotient.mk v)) • Submodule.Quotient.mk v, ?_⟩
      show l' _ = c
      rw [map_smul, hl', smul_eq_mul, div_mul_cancel₀ _ hx]
  · intro g y
    rw [ofChar_apply]
    simp [χ, leviChar_apply, Pi.mulSingle_apply, apply_ite, Finset.prod_ite_eq']

end GlobalTheory.EigenSupport

/- English proof (translation)
Introduce `k _ _ _ _ n V _ _ π ψ l hl0 hl i`. Conclude with `GlobalTheory.EigenSupport.inSupport_of_eigenform n V π ψ l hl0 hl i`.
-/
theorem GlobalTheory.EigenSupport.inSupport_of_torus_eigenform : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V) (ψ : Fin n → kˣ →* ℂˣ) (l : Jacquet π (unipB k (Fin n)) →ₗ[ℂ] ℂ), l ≠ 0 → (∀ t y, l (jacB π t y) = (torusChar ψ t : ℂ) * l y) → ∀ i, InSupport π (ψ i) := by
  intro k _ _ _ _ n V _ _ π ψ l hl0 hl i
  exact GlobalTheory.EigenSupport.inSupport_of_eigenform n V π ψ l hl0 hl i
