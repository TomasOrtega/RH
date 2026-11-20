import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RestrictHalfApply
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.ExportSeries
open Formalism.IndefR.Links (PolF)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

noncomputable section

namespace GlobalTheory.ExportSeries

namespace RestrictHalfModel

variable {D : D7} {m n : ℕ}

/- English proof (translation)
The claim follows from `GlobalTheory.SplitScalar.isHalf_iff e u`.
-/
theorem isHalf_iff' (e : AE D) (u : Mx D m n) : IsHalf e u ↔ e • u = u := GlobalTheory.SplitScalar.isHalf_iff e u

/- English proof (translation)
Rewrite using `[isHalf_iff', smul_smul, he]`.
-/
theorem isHalf_smul {e : AE D} (he : e * e = e) (u : Mx D m n) : IsHalf e (e • u) := by
  rw [isHalf_iff', smul_smul, he]

/- English proof (translation)
Unfold `halfInd`. Establish `hz` using `isHalf_smul he z`. Establish `ht` using `isHalf_smul he t`. Distinguish the cases in `h1 : e • t ∈ Λ`. Rewrite using `[if_pos ⟨by simpa using Λ.add_mem h h1, hz⟩, if_pos ⟨h1, ht⟩]`.

Rewrite using `[if_neg fun h2 => h1 (by simpa using Λ.sub_mem h2.1 h), if_neg fun h2 => h1 h2.1]`.
-/
theorem halfInd_smul_congr {e : AE D} (he : e * e = e) (Λ : AddSubgroup (Mx D m n)) {z t : Mx D m n}
    (h : e • z - e • t ∈ Λ) : halfInd e Λ (e • z) = halfInd e Λ (e • t) := by
  unfold halfInd
  have hz := isHalf_smul he z
  have ht := isHalf_smul he t
  by_cases h1 : e • t ∈ Λ
  · rw [if_pos ⟨by simpa using Λ.add_mem h h1, hz⟩, if_pos ⟨h1, ht⟩]
  · rw [if_neg fun h2 => h1 (by simpa using Λ.sub_mem h2.1 h), if_neg fun h2 => h1 h2.1]

/- English proof (translation)
Rewrite `hx` using `[isHalf_iff']`. Establish `h0 : b • x = 0`. Rewrite using `[← hx, smul_smul, mul_comm, hab, zero_smul]`. Conclude with `⟨h0, by rw [add_smul, hx, h0, add_zero]⟩`.
-/
theorem smul_of_half {a' b : AE D} (hab : a' * b = 0) {x : Mx D m n} (hx : IsHalf a' x) :
    b • x = 0 ∧ (a' + b) • x = x := by
  rw [isHalf_iff'] at hx
  have h0 : b • x = 0 := by
    rw [← hx, smul_smul, mul_comm, hab, zero_smul]
  exact ⟨h0, by rw [add_smul, hx, h0, add_zero]⟩

/- English proof (translation)
Rewrite using `[isHalf_iff', isHalf_iff', smul_add, hu, add_left_inj]`.
-/
theorem isHalf_add_iff {e : AE D} {t u : Mx D m n} (hu : e • u = u) : IsHalf e (t + u) ↔ IsHalf e t := by
  rw [isHalf_iff', isHalf_iff', smul_add, hu, add_left_inj]

/- English proof (translation)
Take `⟨-, k, hk, hinv, hlat⟩` from `hΦ`. Use `⟨fun t ht => ?_, k, hk, fun u hu hhu t => ?_, fun t ht => ?_⟩` and prove the remaining obligations. Rewrite `ht` using `[restrictHalf_apply]`. Assume the negation of the conclusion as `h`. Conclude with `ht (by rw [if_neg h, mul_zero])`.

Rewrite `hhu` using `[isHalf_iff']`. Simplify using `only [restrictHalf_apply]`. Establish `e1 : a' • (t + k • u) = a' • t + k • (a' • u)` using `by rw [smul_add, smul_comm]`. Establish `e2 : (a' + b) • (k • u) = k • u` using `by rw [smul_comm, hhu]`. Rewrite using `[e1, hinv _ (hΛ a' ha' u hu) (isHalf_smul ha' u), halfInd_smul_congr hb Λ (z := t + k • u) (t := t) (by`.

Rewrite using `[smul_add, add_sub_cancel_left, smul_comm]`. Conclude with `Λ.nsmul_mem (hΛ b hb u hu) k)]`. Simplify using `only [isHalf_add_iff e2]`. Rewrite `ht` using `[restrictHalf_apply]`. Establish `h1 : Φ (a' • t) ≠ 0` using `fun h => ht (by rw [h, zero_mul, zero_mul])`.

Establish `h2 : halfInd b Λ (b • t) ≠ 0` using `fun h => ht (by rw [h, mul_zero, zero_mul])`. Establish `h3 : IsHalf (a' + b) t`. Assume the negation of the conclusion as `h`. Conclude with `ht (by rw [if_neg h, mul_zero])`. Establish `h2' : b • t ∈ Λ`.

Unfold `halfInd at h2`. Assume the negation of the conclusion as `h`. Conclude with `h2 (if_neg fun h' => h h'.1)`. Rewrite `h3` using `[isHalf_iff', add_smul]`. Rewrite using `[← h3, smul_add]`.

Conclude with `Λ.add_mem (hlat _ h1) (Λ.nsmul_mem h2' k)`.
-/
theorem isSBHalf_restrictHalf {a' b : AE D} (ha' : a' * a' = a') (hb : b * b = b) {Λ : AddSubgroup (Mx D m n)}
    (hΛ : ∀ e : AE D, e * e = e → ∀ u ∈ Λ, e • u ∈ Λ) {Φ : Mx D m n → ℂ} (hΦ : IsSBHalf a' Λ Φ) :
    IsSBHalf (a' + b) Λ (restrictHalf a' b Λ Φ) := by
  obtain ⟨-, k, hk, hinv, hlat⟩ := hΦ
  refine ⟨fun t ht => ?_, k, hk, fun u hu hhu t => ?_, fun t ht => ?_⟩
  · rw [restrictHalf_apply] at ht
    by_contra h
    exact ht (by rw [if_neg h, mul_zero])
  · rw [isHalf_iff'] at hhu
    simp only [restrictHalf_apply]
    have e1 : a' • (t + k • u) = a' • t + k • (a' • u) := by rw [smul_add, smul_comm]
    have e2 : (a' + b) • (k • u) = k • u := by rw [smul_comm, hhu]
    rw [e1, hinv _ (hΛ a' ha' u hu) (isHalf_smul ha' u), halfInd_smul_congr hb Λ (z := t + k • u) (t := t) (by
      rw [smul_add, add_sub_cancel_left, smul_comm]
      exact Λ.nsmul_mem (hΛ b hb u hu) k)]
    simp only [isHalf_add_iff e2]
  · rw [restrictHalf_apply] at ht
    have h1 : Φ (a' • t) ≠ 0 := fun h => ht (by rw [h, zero_mul, zero_mul])
    have h2 : halfInd b Λ (b • t) ≠ 0 := fun h => ht (by rw [h, mul_zero, zero_mul])
    have h3 : IsHalf (a' + b) t := by
      by_contra h
      exact ht (by rw [if_neg h, mul_zero])
    have h2' : b • t ∈ Λ := by
      unfold halfInd at h2
      by_contra h
      exact h2 (if_neg fun h' => h h'.1)
    rw [isHalf_iff', add_smul] at h3
    rw [← h3, smul_add]
    exact Λ.add_mem (hlat _ h1) (Λ.nsmul_mem h2' k)

end RestrictHalfModel

open RestrictHalfModel in

/- English proof (translation)
Introduce `D S T ψ Λ f₀ a' b T₀ ha' hb hab hΛ hT`. Establish `hsb : ∀ Φ, IsSBHalf a' Λ Φ → IsSBHalf (a' + b) Λ (restrictHalf a' b Λ Φ)` using `fun Φ hΦ => isSBHalf_restrictHalf ha' hb hΛ hΦ`. Use `⟨fun Φ hΦ x hx => ?_, fun Φ hΦ y hy => ?_, ?_⟩` and prove the remaining obligations. Take `⟨hbx, hax⟩` from `smul_of_half hab hx`. Establish `hxa : IsHalf (a' + b) x` using `(isHalf_iff' _ _).2 hax`.

Establish `e : restrictHalf a' b Λ (fun t => Φ (t + x)) = fun t => restrictHalf a' b Λ Φ (t + x)`. Use function extensionality and compare the values at `z`. Simplify using `only [restrictHalf_apply]`. Rewrite using `[smul_add, (isHalf_iff' _ _).1 hx, smul_add b, hbx, add_zero, isHalf_add_iff hax]`. Rewrite using `[LinearMap.comp_apply, LinearMap.comp_apply, e]`.

Conclude with `hT.trans _ (hsb Φ hΦ) x hxa`. Establish `hy' : IsHalf (cA D (a' + b)) y`. Rewrite `hy`, the goal using `[isHalf_iff']`. Rewrite using `[map_add, add_smul, hy, ← hy, smul_smul, ← map_mul, mul_comm, hab, map_zero, zero_smul, add_zero]`. Establish `e : restrictHalf a' b Λ (fun t => ψ (symplO S T t y) * Φ t) = fun t => ψ (symplO S T t y) * restrictHalf a' b Λ Φ t`.

Use function extensionality and compare the values at `z`. Simplify using `only [restrictHalf_apply]`. Rewrite using `[GlobalTheory.SplitScalar.symplO_smul, (isHalf_iff' _ _).1 hy]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[LinearMap.comp_apply, LinearMap.comp_apply, e]`.

Conclude with `hT.modul _ (hsb Φ hΦ) y hy'`. Establish `e : restrictHalf a' b Λ ((1 : ℂ) • halfInd a' Λ) = (1 : ℂ) • halfInd (a' + b) Λ`. Use function extensionality and compare the values at `t`. Simplify using `only [one_smul, restrictHalf_apply]`. Unfold `halfInd`.

Establish `i1` using `isHalf_smul ha' t`. Establish `i2` using `isHalf_smul hb t`. Distinguish the cases in `hat : IsHalf (a' + b) t`. Establish `ht' : t = a' • t + b • t` using `by rw [← add_smul]; exact ((isHalf_iff' _ _).1 hat).symm`. Distinguish the cases in `ht : t ∈ Λ`.

Rewrite using `[if_pos ⟨hΛ a' ha' t ht, i1⟩, if_pos ⟨hΛ b hb t ht, i2⟩, if_pos hat, if_pos ⟨ht, hat⟩]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[if_neg (show ¬ (t ∈ Λ ∧ IsHalf (a' + b) t) from fun h => ht h.1), if_pos hat, mul_one]`. Distinguish the cases in `h1 : a' • t ∈ Λ`. Rewrite using `[if_neg (show ¬ (b • t ∈ Λ ∧ IsHalf b (b • t)) from fun h => ht (by rw [ht']; exact Λ.add_mem h1 h.1)), mul_zero]`.

Rewrite using `[if_neg (show ¬ (a' • t ∈ Λ ∧ IsHalf a' (a' • t)) from fun h => h1 h.1), zero_mul]`. Rewrite using `[if_neg hat, mul_zero, if_neg fun h => hat h.2]`. Rewrite using `[LinearMap.comp_apply, e]`. Conclude with `hT.vac`.
-/
theorem isPlaceModel_comp_restrictHalf : ∀ {D : D7} {S T : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {Λ : AddSubgroup (WO S T)} {f₀ : WO S T → ℂ} {a' b : AE D} {T₀ : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)}, a' * a' = a' → b * b = b → a' * b = 0 → (∀ e : AE D, e * e = e → ∀ u ∈ Λ, e • u ∈ Λ) → IsPlaceModel ψ (symplO S T) (heisO ψ S T) (a' + b) Λ 1 f₀ T₀ → IsPlaceModel ψ (symplO S T) (heisO ψ S T) a' Λ 1 f₀ (T₀ ∘ₗ restrictHalf a' b Λ) := by
  intro D S T ψ Λ f₀ a' b T₀ ha' hb hab hΛ hT
  have hsb : ∀ Φ, IsSBHalf a' Λ Φ → IsSBHalf (a' + b) Λ (restrictHalf a' b Λ Φ) :=
    fun Φ hΦ => isSBHalf_restrictHalf ha' hb hΛ hΦ
  refine ⟨fun Φ hΦ x hx => ?_, fun Φ hΦ y hy => ?_, ?_⟩
  · obtain ⟨hbx, hax⟩ := smul_of_half hab hx
    have hxa : IsHalf (a' + b) x := (isHalf_iff' _ _).2 hax
    have e : restrictHalf a' b Λ (fun t => Φ (t + x)) = fun t => restrictHalf a' b Λ Φ (t + x) := by
      funext z
      simp only [restrictHalf_apply]
      rw [smul_add, (isHalf_iff' _ _).1 hx, smul_add b, hbx, add_zero, isHalf_add_iff hax]
    rw [LinearMap.comp_apply, LinearMap.comp_apply, e]
    exact hT.trans _ (hsb Φ hΦ) x hxa
  · have hy' : IsHalf (cA D (a' + b)) y := by
      rw [isHalf_iff'] at hy ⊢
      rw [map_add, add_smul, hy, ← hy, smul_smul, ← map_mul, mul_comm, hab, map_zero, zero_smul, add_zero]
    have e : restrictHalf a' b Λ (fun t => ψ (symplO S T t y) * Φ t) =
        fun t => ψ (symplO S T t y) * restrictHalf a' b Λ Φ t := by
      funext z
      simp only [restrictHalf_apply]
      rw [GlobalTheory.SplitScalar.symplO_smul, (isHalf_iff' _ _).1 hy]
      ring
    rw [LinearMap.comp_apply, LinearMap.comp_apply, e]
    exact hT.modul _ (hsb Φ hΦ) y hy'
  · have e : restrictHalf a' b Λ ((1 : ℂ) • halfInd a' Λ) = (1 : ℂ) • halfInd (a' + b) Λ := by
      funext t
      simp only [one_smul, restrictHalf_apply]
      unfold halfInd
      have i1 := isHalf_smul ha' t
      have i2 := isHalf_smul hb t
      by_cases hat : IsHalf (a' + b) t
      · have ht' : t = a' • t + b • t := by rw [← add_smul]; exact ((isHalf_iff' _ _).1 hat).symm
        by_cases ht : t ∈ Λ
        · rw [if_pos ⟨hΛ a' ha' t ht, i1⟩, if_pos ⟨hΛ b hb t ht, i2⟩, if_pos hat, if_pos ⟨ht, hat⟩]
          ring
        · rw [if_neg (show ¬ (t ∈ Λ ∧ IsHalf (a' + b) t) from fun h => ht h.1), if_pos hat, mul_one]
          by_cases h1 : a' • t ∈ Λ
          · rw [if_neg (show ¬ (b • t ∈ Λ ∧ IsHalf b (b • t)) from fun h => ht (by rw [ht']; exact Λ.add_mem h1 h.1)),
              mul_zero]
          · rw [if_neg (show ¬ (a' • t ∈ Λ ∧ IsHalf a' (a' • t)) from fun h => h1 h.1), zero_mul]
      · rw [if_neg hat, mul_zero, if_neg fun h => hat h.2]
    rw [LinearMap.comp_apply, e]
    exact hT.vac

end GlobalTheory.ExportSeries

end
