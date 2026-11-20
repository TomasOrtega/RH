import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmulMemLatOIdem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSBHalfHalfExtensionLatticeIndicatorFnStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section
namespace GlobalTheory.CosetRow

section ThetaExt
variable {D : D7} {m n : ℕ}

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h i j`. Establish `h1` using `h i j`. Establish `h2` using `hx i j`. Simplify using `only [Matrix.add_apply, mul_add] at h1`.

Take the linear combination `h1 - h2`. Introduce `h i j`. Establish `h1` using `h i j`. Establish `h2` using `hx i j`. Simplify using `only [Matrix.add_apply, mul_add]`.

Take the linear combination `h1 + h2`.
-/
theorem isHalf_add_right_iff {e : AE D} {t x : Mx D m n} (hx : IsHalf e x) :
    IsHalf e (t + x) ↔ IsHalf e t := by
  constructor
  · intro h i j
    have h1 := h i j
    have h2 := hx i j
    simp only [Matrix.add_apply, mul_add] at h1
    linear_combination h1 - h2
  · intro h i j
    have h1 := h i j
    have h2 := hx i j
    simp only [Matrix.add_apply, mul_add]
    linear_combination h1 + h2

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [Matrix.smul_apply, smul_eq_mul]`. Conclude with `hx i j`.
-/
theorem smul_of_isHalf {e : AE D} {x : Mx D m n} (hx : IsHalf e x) : e • x = x := by
  ext i j
  simp only [Matrix.smul_apply, smul_eq_mul]
  exact hx i j

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply]`. Rewrite using `[← hx i j, ← mul_assoc, h, zero_mul]`.
-/
theorem smul_eq_zero_of_isHalf {e e' : AE D} (h : e' * e = 0) {x : Mx D m n} (hx : IsHalf e x) : e' • x = 0 := by
  ext i j
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply]
  rw [← hx i j, ← mul_assoc, h, zero_mul]

/- English proof (translation)
Introduce `i j`. Simplify using `only [Matrix.smul_apply, smul_eq_mul]`. Rewrite using `[← mul_assoc, he]`.
-/
theorem isHalf_smul_idem {e : AE D} (he : e * e = e) (t : Mx D m n) : IsHalf e (e • t) := by
  intro i j
  simp only [Matrix.smul_apply, smul_eq_mul]
  rw [← mul_assoc, he]

def extLin (e₀ e₁ : AE D) (Λ : AddSubgroup (Mx D m n)) : (Mx D m n → ℂ) →ₗ[ℂ] (Mx D m n → ℂ) where
  toFun := extFn e₀ e₁ Λ
  map_add' Φ Ψ := by
    funext t
    simp only [extFn, Pi.add_apply]
    split_ifs <;> ring
  map_smul' c Φ := by
    funext t
    simp only [extFn, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> ring

/- English proof (translation)
Use function extensionality and compare the values at `t`. Establish `hx' : IsHalf (e₀ + e₁) x`. Rewrite using `[add_comm]`. Conclude with `GlobalTheory.VecProd.half_add_of_right h10 hx`. Simplify using `only [extFn]`.

Rewrite using `[isHalf_add_right_iff hx', smul_add, smul_add, smul_of_isHalf hx, smul_eq_zero_of_isHalf h10 hx, add_zero]`.
-/
theorem extFn_shift {e₀ e₁ : AE D} (h10 : e₁ * e₀ = 0) (Λ : AddSubgroup (Mx D m n)) (Φ : Mx D m n → ℂ)
    {x : Mx D m n} (hx : IsHalf e₀ x) :
    extFn e₀ e₁ Λ (fun t => Φ (t + x)) = fun t => extFn e₀ e₁ Λ Φ (t + x) := by
  funext t
  have hx' : IsHalf (e₀ + e₁) x := by
    rw [add_comm]; exact GlobalTheory.VecProd.half_add_of_right h10 hx
  simp only [extFn]
  rw [isHalf_add_right_iff hx', smul_add, smul_add, smul_of_isHalf hx, smul_eq_zero_of_isHalf h10 hx, add_zero]

/- English proof (translation)
Use function extensionality and compare the values at `t`. Simplify using `only [extFn]`. Use `split_ifs with h`. Rewrite using `[hg t h]`. Expand and normalize the polynomial expressions, which then agree.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem extFn_modul {e₀ e₁ : AE D} (Λ : AddSubgroup (Mx D m n)) (Φ : Mx D m n → ℂ) (g : Mx D m n → ℂ)
    (hg : ∀ t, IsHalf (e₀ + e₁) t → g t = g (e₀ • t)) :
    extFn e₀ e₁ Λ (fun t => g t * Φ t) = fun t => g t * extFn e₀ e₁ Λ Φ t := by
  funext t
  simp only [extFn]
  split_ifs with h
  · rw [hg t h]; ring
  · ring

/- English proof (translation)
Use function extensionality and compare the values at `t`. Simplify using `only [extFn, halfInd]`. Distinguish the cases in `ht : IsHalf (e₀ + e₁) t`. Establish `hdec : t = e₀ • t + e₁ • t`. Rewrite using `[← add_smul, smul_of_isHalf ht]`.

Establish `hiff : (e₀ • t ∈ Λ ∧ e₁ • t ∈ Λ) ↔ t ∈ Λ`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h0, h1⟩`. Rewrite using `[hdec]`. Conclude with `Λ.add_mem h0 h1`.

Introduce `h`. Conclude with `⟨hΛ0 t h, hΛ1 t h⟩`. Establish `a0` using `isHalf_smul_idem h00 t`. Establish `a1` using `isHalf_smul_idem h11 t`. Rewrite using `[if_pos ht]`.

Apply the tactic sequence `by_cases h0 : e₀ • t ∈ Λ <;> by_cases h1 : e₁ • t ∈ Λ`. Rewrite using `[if_pos ⟨h0, a0⟩, if_pos ⟨h1, a1⟩, if_pos ⟨hiff.1 ⟨h0, h1⟩, ht⟩, one_mul]`. Rewrite using `[if_pos ⟨h0, a0⟩, if_neg (fun h => h1 h.1), if_neg (fun h => h1 (hiff.2 h.1).2), mul_zero]`. Rewrite using `[if_neg (fun h => h0 h.1), if_pos ⟨h1, a1⟩, if_neg (fun h => h0 (hiff.2 h.1).1), zero_mul]`. Rewrite using `[if_neg (fun h => h0 h.1), if_neg (fun h => h1 h.1), if_neg (fun h => h0 (hiff.2 h.1).1), zero_mul]`.

Simplify using `only [if_neg ht]`. Rewrite using `[if_neg (fun h => ht h.2)]`.
-/
theorem extFn_halfInd {e₀ e₁ : AE D} (h00 : e₀ * e₀ = e₀) (h11 : e₁ * e₁ = e₁) {Λ : AddSubgroup (Mx D m n)}
    (hΛ0 : ∀ u ∈ Λ, e₀ • u ∈ Λ) (hΛ1 : ∀ u ∈ Λ, e₁ • u ∈ Λ) :
    extFn e₀ e₁ Λ (halfInd e₀ Λ) = halfInd (e₀ + e₁) Λ := by
  funext t
  simp only [extFn, halfInd]
  by_cases ht : IsHalf (e₀ + e₁) t
  · have hdec : t = e₀ • t + e₁ • t := by
      rw [← add_smul, smul_of_isHalf ht]
    have hiff : (e₀ • t ∈ Λ ∧ e₁ • t ∈ Λ) ↔ t ∈ Λ := by
      constructor
      · rintro ⟨h0, h1⟩; rw [hdec]; exact Λ.add_mem h0 h1
      · intro h; exact ⟨hΛ0 t h, hΛ1 t h⟩
    have a0 := isHalf_smul_idem h00 t
    have a1 := isHalf_smul_idem h11 t
    rw [if_pos ht]
    by_cases h0 : e₀ • t ∈ Λ <;> by_cases h1 : e₁ • t ∈ Λ
    · rw [if_pos ⟨h0, a0⟩, if_pos ⟨h1, a1⟩, if_pos ⟨hiff.1 ⟨h0, h1⟩, ht⟩, one_mul]
    · rw [if_pos ⟨h0, a0⟩, if_neg (fun h => h1 h.1), if_neg (fun h => h1 (hiff.2 h.1).2), mul_zero]
    · rw [if_neg (fun h => h0 h.1), if_pos ⟨h1, a1⟩, if_neg (fun h => h0 (hiff.2 h.1).1), zero_mul]
    · rw [if_neg (fun h => h0 h.1), if_neg (fun h => h1 h.1), if_neg (fun h => h0 (hiff.2 h.1).1), zero_mul]
  · simp only [if_neg ht]
    rw [if_neg (fun h => ht h.2)]

/- English proof (translation)
Introduce `D m n ψ B hs Λ e₀ e₁ f₀ Φ f h00 h11 h01 hΛ0 hΛ1 hB hex h`. Establish `h10 : e₁ * e₀ = 0` using `by rw [mul_comm]; exact h01`. Establish `hsb : ∀ Ψ, IsSBHalf e₀ Λ Ψ → IsSBHalf (e₀ + e₁) Λ (extFn e₀ e₁ Λ Ψ)` using `fun Ψ hΨ => GlobalTheory.T.isSBHalf_halfExtensionLatticeIndicatorFn h00 h11 h01 hΛ0 hΛ1 hΨ`. Use `⟨hex, fun T hT => ?_⟩` and prove the remaining obligations. Establish `hT₀ : IsPlaceModel ψ B hs e₀ Λ 1 f₀ (T ∘ₗ extLin e₀ e₁ Λ)`.

Use `⟨fun Ψ hΨ x hx => ?_, fun Ψ hΨ y hy => ?_, ?_⟩` and prove the remaining obligations. Establish `hx' : IsHalf (e₀ + e₁) x`. Rewrite using `[add_comm]`. Conclude with `GlobalTheory.VecProd.half_add_of_right h10 hx`. Simplify using `only [LinearMap.comp_apply]`.

Express the relevant statement in the definitionally equal form `T (extFn e₀ e₁ Λ (fun t => Ψ (t + x))) = hs x (T (extFn e₀ e₁ Λ Ψ))`. Rewrite using `[extFn_shift h10 Λ Ψ hx]`. Conclude with `hT.trans _ (hsb Ψ hΨ) x hx'`. Establish `hy' : IsHalf (cA D (e₀ + e₁)) y`. Rewrite using `[add_comm]`.

Conclude with `GlobalTheory.VecProd.half_conj_add_of_right h10 hy`. Simplify using `only [LinearMap.comp_apply]`. Express the relevant statement in the definitionally equal form `T (extFn e₀ e₁ Λ (fun t => ψ (B t y) * Ψ t)) = hs y (T (extFn e₀ e₁ Λ Ψ))`. Rewrite using `[extFn_modul Λ Ψ (fun t => ψ (B t y)) (fun t ht => by simp only [hB t y ht hy])]`. Conclude with `hT.modul _ (hsb Ψ hΨ) y hy'`.

Simplify using `only [LinearMap.comp_apply, one_smul]`. Express the relevant statement in the definitionally equal form `T (extFn e₀ e₁ Λ (halfInd e₀ Λ)) = f₀`. Rewrite using `[extFn_halfInd h00 h11 hΛ0 hΛ1]`. Simplify using `using hT.vac`. Conclude with `h.2 _ hT₀`.
-/
theorem isThetaAt_extFn : ∀ {D : D7} {m n : ℕ} {ψ : AddChar (AF D.host.F) ℂ} {B : Mx D m n → Mx D m n → AF D.host.F} {hs : Mx D m n → (Mx D m n → ℂ) → (Mx D m n → ℂ)} {Λ : AddSubgroup (Mx D m n)} {e₀ e₁ : AE D} {f₀ Φ f : Mx D m n → ℂ}, e₀ * e₀ = e₀ → e₁ * e₁ = e₁ → e₀ * e₁ = 0 → (∀ u ∈ Λ, e₀ • u ∈ Λ) → (∀ u ∈ Λ, e₁ • u ∈ Λ) → (∀ t y, IsHalf (e₀ + e₁) t → IsHalf (cA D e₀) y → B t y = B (e₀ • t) y) → (∃ T, IsPlaceModel ψ B hs (e₀ + e₁) Λ 1 f₀ T) → IsThetaAt ψ B hs e₀ Λ 1 f₀ Φ f → IsThetaAt ψ B hs (e₀ + e₁) Λ 1 f₀ (GlobalTheory.CosetRow.extFn e₀ e₁ Λ Φ) f := by
  intro D m n ψ B hs Λ e₀ e₁ f₀ Φ f h00 h11 h01 hΛ0 hΛ1 hB hex h
  have h10 : e₁ * e₀ = 0 := by rw [mul_comm]; exact h01
  have hsb : ∀ Ψ, IsSBHalf e₀ Λ Ψ → IsSBHalf (e₀ + e₁) Λ (extFn e₀ e₁ Λ Ψ) := fun Ψ hΨ =>
    GlobalTheory.T.isSBHalf_halfExtensionLatticeIndicatorFn h00 h11 h01 hΛ0 hΛ1 hΨ
  refine ⟨hex, fun T hT => ?_⟩
  have hT₀ : IsPlaceModel ψ B hs e₀ Λ 1 f₀ (T ∘ₗ extLin e₀ e₁ Λ) := by
    refine ⟨fun Ψ hΨ x hx => ?_, fun Ψ hΨ y hy => ?_, ?_⟩
    · have hx' : IsHalf (e₀ + e₁) x := by
        rw [add_comm]; exact GlobalTheory.VecProd.half_add_of_right h10 hx
      simp only [LinearMap.comp_apply]
      change T (extFn e₀ e₁ Λ (fun t => Ψ (t + x))) = hs x (T (extFn e₀ e₁ Λ Ψ))
      rw [extFn_shift h10 Λ Ψ hx]
      exact hT.trans _ (hsb Ψ hΨ) x hx'
    · have hy' : IsHalf (cA D (e₀ + e₁)) y := by
        rw [add_comm]; exact GlobalTheory.VecProd.half_conj_add_of_right h10 hy
      simp only [LinearMap.comp_apply]
      change T (extFn e₀ e₁ Λ (fun t => ψ (B t y) * Ψ t)) = hs y (T (extFn e₀ e₁ Λ Ψ))
      rw [extFn_modul Λ Ψ (fun t => ψ (B t y)) (fun t ht => by simp only [hB t y ht hy])]
      exact hT.modul _ (hsb Ψ hΨ) y hy'
    · simp only [LinearMap.comp_apply, one_smul]
      change T (extFn e₀ e₁ Λ (halfInd e₀ Λ)) = f₀
      rw [extFn_halfInd h00 h11 hΛ0 hΛ1]
      simpa using hT.vac
  exact h.2 _ hT₀

end ThetaExt

end GlobalTheory.CosetRow

end
