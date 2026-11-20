import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TiedAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TensorOneApply

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.AdForm GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocMod.TOneModel

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k)
  {S T : HSp D} {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']

/- English proof (translation)
Establish `h : p.ι 1 = p.e` using `by simpa using p.ι_π 1`. Rewrite using `[← h, p.π_ι]`.
-/
theorem pi_e : p.π p.e = 1 := by
  have h : p.ι 1 = p.e := by simpa using p.ι_π 1
  rw [← h, p.π_ι]

/- English proof (translation)
Establish `h` using `congrArg p.π he`. Rewrite `h` using `[map_mul, pi_e, mul_one, map_zero]`. Then use the resulting hypothesis.
-/
theorem pi_of_mul {e : AE D} (he : e * p.e = 0) : p.π e = 0 := by
  have h := congrArg p.π he
  rwa [map_mul, pi_e, mul_one, map_zero] at h

/- English proof (translation)
Unfold `Place.up Place.down`. Rewrite using `[← Matrix.mul_assoc, ← Matrix.mul_assoc, FT.βγ, Matrix.one_mul, Matrix.mul_assoc, FS.βγ, Matrix.mul_one]`. Use extensionality with `i j`. Simplify using `only [Matrix.map_apply]`. Conclude with `p.ι_π _`.
-/
theorem up_down_eq (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (t : WO S T) :
    p.up FS FT (p.down FS FT t) = t.map (fun a => p.e * a) := by
  unfold Place.up Place.down
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, FT.βγ, Matrix.one_mul, Matrix.mul_assoc, FS.βγ, Matrix.mul_one]
  ext i j
  simp only [Matrix.map_apply]
  exact p.ι_π _

/- English proof (translation)
Unfold `Place.down`. Establish `h : (x : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map p.π = 0`. Use extensionality with `i j`. Simplify using `only [Matrix.map_apply, Matrix.zero_apply]`. Rewrite using `[← hx i j, map_mul, pi_of_mul p he, zero_mul]`.

Rewrite using `[h, Matrix.mul_zero, Matrix.zero_mul]`.
-/
theorem down_half_zero (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) {e : AE D} (he : e * p.e = 0) {x : WO S T}
    (hx : IsHalf e x) : p.down FS FT x = 0 := by
  unfold Place.down
  have h : (x : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map p.π = 0 := by
    ext i j
    simp only [Matrix.map_apply, Matrix.zero_apply]
    rw [← hx i j, map_mul, pi_of_mul p he, zero_mul]
  rw [h, Matrix.mul_zero, Matrix.zero_mul]

/- English proof (translation)
Introduce `i j`. Establish `h : p.e * x i j = 0` using `by rw [← hx i j, ← mul_assoc, mul_comm p.e e, he, zero_mul]`. Rewrite using `[add_mul, hx i j, h, add_zero]`.
-/
theorem half_sum {e : AE D} (he : e * p.e = 0) {x : WO S T} (hx : IsHalf e x) : IsHalf (e + p.e) x := by
  intro i j
  have h : p.e * x i j = 0 := by rw [← hx i j, ← mul_assoc, mul_comm p.e e, he, zero_mul]
  rw [add_mul, hx i j, h, add_zero]

/- English proof (translation)
Introduce `i j`. Establish `h : cA D p.e * y i j = 0`. Rewrite using `[← hy i j, ← mul_assoc, ← map_mul, mul_comm p.e e, he, map_zero, zero_mul]`. Rewrite using `[map_add, add_mul, hy i j, h, add_zero]`.
-/
theorem half_sum_conj {e : AE D} (he : e * p.e = 0) {y : WO S T} (hy : IsHalf (cA D e) y) :
    IsHalf (cA D (e + p.e)) y := by
  intro i j
  have h : cA D p.e * y i j = 0 := by
    rw [← hy i j, ← mul_assoc, ← map_mul, mul_comm p.e e, he, map_zero, zero_mul]
  rw [map_add, add_mul, hy i j, h, add_zero]

/- English proof (translation)
Unfold `hO`. Use `Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun c _ => Finset.sum_eq_zero fun d _ => ?_` and prove the remaining obligations. Establish `h1 : cA D (y c b) = e * cA D (y c b)` using `by conv_lhs => rw [← hy c b, map_mul, Formalism.L2.Theta.cA_cA]`. Rewrite using `[h1, ← hw d a]`. Take the linear combination `(incA D (S.gram⁻¹ a b) * cA D (y c b) * incA D (T.gram c d) * w d a) * he`.
-/
theorem hO_zero {e : AE D} (he : e * p.e = 0) {w y : WO S T} (hw : IsHalf p.e w) (hy : IsHalf (cA D e) y) :
    hO S T w y = 0 := by
  unfold hO
  refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun c _ =>
    Finset.sum_eq_zero fun d _ => ?_
  have h1 : cA D (y c b) = e * cA D (y c b) := by
    conv_lhs => rw [← hy c b, map_mul, Formalism.L2.Theta.cA_cA]
  rw [h1, ← hw d a]
  linear_combination (incA D (S.gram⁻¹ a b) * cA D (y c b) * incA D (T.gram c d) * w d a) * he

/- English proof (translation)
Establish `h : hO S T (t - w) y = hO S T t y - hO S T w y`. Simplify using `only [hO, Matrix.sub_apply, mul_sub, Finset.sum_sub_distrib]`. Unfold `symplO`. Rewrite using `[h, hO_zero p he hw hy, sub_zero]`.
-/
theorem symplO_sub_half {e : AE D} (he : e * p.e = 0) (t : WO S T) {w y : WO S T} (hw : IsHalf p.e w)
    (hy : IsHalf (cA D e) y) : symplO S T (t - w) y = symplO S T t y := by
  have h : hO S T (t - w) y = hO S T t y - hO S T w y := by
    simp only [hO, Matrix.sub_apply, mul_sub, Finset.sum_sub_distrib]
  unfold symplO
  rw [h, hO_zero p he hw hy, sub_zero]

end GlobalTheory.LocMod.TOneModel

namespace GlobalTheory.LocMod.TOneModel

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k)
  {S T : HSp D} {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']

/- English proof (translation)
Use function extensionality and compare the values at `t`. Simplify using `only [Place.tensorOne_apply, Place.tensorAt]`. Rewrite using `[GlobalTheory.LocMod.Witness.down_add p FS FT t x, down_half_zero p FS FT he hx, add_zero, sub_add_eq_add_sub]`.
-/
theorem tensorOne_trans (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) {e : AE D} (he : e * p.e = 0)
    (Φ : WO S T → ℂ) {x : WO S T} (hx : IsHalf e x) :
    p.tensorOne FS FT (fun t => Φ (t + x)) = fun t => p.tensorOne FS FT Φ (t + x) := by
  funext t
  simp only [Place.tensorOne_apply, Place.tensorAt]
  rw [GlobalTheory.LocMod.Witness.down_add p FS FT t x, down_half_zero p FS FT he hx, add_zero, sub_add_eq_add_sub]

/- English proof (translation)
Use function extensionality and compare the values at `t`. Simplify using `only [Place.tensorOne_apply, Place.tensorAt]`. Rewrite using `[symplO_sub_half p he t (GlobalTheory.LocMod.Witness.up_half p FS FT _) hy, mul_assoc]`.
-/
theorem tensorOne_modul (ψ : AddChar (AF D.host.F) ℂ) (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) {e : AE D}
    (he : e * p.e = 0) (Φ : WO S T → ℂ) {y : WO S T} (hy : IsHalf (cA D e) y) :
    p.tensorOne FS FT (fun t => ψ (symplO S T t y) * Φ t) = fun t => ψ (symplO S T t y) * p.tensorOne FS FT Φ t := by
  funext t
  simp only [Place.tensorOne_apply, Place.tensorAt]
  rw [symplO_sub_half p he t (GlobalTheory.LocMod.Witness.up_half p FS FT _) hy, mul_assoc]

open Classical in
/- English proof (translation)
Unfold `Place.intInd`. Rewrite using `[Set.indicator_apply]`. Conclude with `if_congr (hint x) rfl rfl`.
-/
theorem intInd_eq (FS : Frame k S.rank Y') (FT : Frame k T.rank Y)
    (hint : ∀ x : Matrix Y Y' k, (∀ r q, x r q ∈ 𝒪[k]) ↔ p.up FS FT x ∈ stdHom S T) (x : Matrix Y Y' k) :
    Place.intInd Y Y' x = if p.up FS FT x ∈ stdHom S T then 1 else 0 := by
  classical
  unfold Place.intInd
  rw [Set.indicator_apply]
  exact if_congr (hint x) rfl rfl

/- English proof (translation)
Use function extensionality and compare the values at `t`. Simplify using `only [one_smul]`. Rewrite using `[Place.tensorOne_apply]`. Simplify using `only [Place.tensorAt]`. Rewrite using `[intInd_eq p FS FT hint, up_down_eq p FS FT t]`.

Use `set M : WO S T := t.map (fun a => p.e * a) with hMdef`. Establish `key : ((t - M ∈ stdHom S T ∧ IsHalf e (t - M)) ∧ M ∈ stdHom S T) ↔ (t ∈ stdHom S T ∧ IsHalf (e + p.e) t)`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨h1, h2⟩, h3⟩`. Use `⟨by simpa using add_mem h1 h3, fun i j => ?_⟩` and prove the remaining obligations.

Establish `h` using `h2 i j`. Simplify using `only [hMdef, Matrix.sub_apply, Matrix.map_apply] at h`. Take the linear combination `h + t i j * he`. Introduce and unpack `⟨h1, h2⟩`. Establish `h3 : M ∈ stdHom S T` using `hstab t h1`.

Use `⟨⟨sub_mem h1 h3, fun i j => ?_⟩, h3⟩` and prove the remaining obligations. Simplify using `only [hMdef, Matrix.sub_apply, Matrix.map_apply]`. Take the linear combination `h2 i j - t i j * he`. Unfold `halfInd`. Distinguish the cases in `hR : t ∈ stdHom S T ∧ IsHalf (e + p.e) t`.

Take `⟨⟨h1, h2⟩, h3⟩` from `key.2 hR`. Rewrite using `[if_pos hR, if_pos ⟨h1, h2⟩, if_pos h3, mul_one]`. Rewrite using `[if_neg hR]`. Distinguish the cases in `h3 : M ∈ stdHom S T`. Rewrite using `[if_pos h3, mul_one, if_neg fun h => hR (key.1 ⟨h, h3⟩)]`.

Rewrite using `[if_neg h3, mul_zero]`.
-/
theorem tensorOne_vac (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) {e : AE D} (he : e * p.e = 0)
    (hint : ∀ x : Matrix Y Y' k, (∀ r q, x r q ∈ 𝒪[k]) ↔ p.up FS FT x ∈ stdHom S T)
    (hstab : ∀ u ∈ stdHom S T, u.map (fun a => p.e * a) ∈ stdHom S T) :
    p.tensorOne FS FT ((1 : ℂ) • halfInd e (stdHom S T)) = (1 : ℂ) • halfInd (e + p.e) (stdHom S T) := by
  classical
  funext t
  simp only [one_smul]
  rw [Place.tensorOne_apply]
  simp only [Place.tensorAt]
  rw [intInd_eq p FS FT hint, up_down_eq p FS FT t]
  set M : WO S T := t.map (fun a => p.e * a) with hMdef
  have key : ((t - M ∈ stdHom S T ∧ IsHalf e (t - M)) ∧ M ∈ stdHom S T) ↔ (t ∈ stdHom S T ∧ IsHalf (e + p.e) t) := by
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨by simpa using add_mem h1 h3, fun i j => ?_⟩
      have h := h2 i j
      simp only [hMdef, Matrix.sub_apply, Matrix.map_apply] at h
      linear_combination h + t i j * he
    · rintro ⟨h1, h2⟩
      have h3 : M ∈ stdHom S T := hstab t h1
      refine ⟨⟨sub_mem h1 h3, fun i j => ?_⟩, h3⟩
      simp only [hMdef, Matrix.sub_apply, Matrix.map_apply]
      linear_combination h2 i j - t i j * he
  unfold halfInd
  by_cases hR : t ∈ stdHom S T ∧ IsHalf (e + p.e) t
  · obtain ⟨⟨h1, h2⟩, h3⟩ := key.2 hR
    rw [if_pos hR, if_pos ⟨h1, h2⟩, if_pos h3, mul_one]
  · rw [if_neg hR]
    by_cases h3 : M ∈ stdHom S T
    · rw [if_pos h3, mul_one, if_neg fun h => hR (key.1 ⟨h, h3⟩)]
    · rw [if_neg h3, mul_zero]

/- English proof (translation)
Introduce `D k _ _ _ _ p ψ S T Y Y' _ _ _ _ FS FT e he hint hstab f₀ T' hT' hsb`. Use `⟨fun Φ hΦ x hx => ?_, fun Φ hΦ y hy => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[LinearMap.comp_apply, tensorOne_trans p FS FT he Φ hx]`. Conclude with `hT'.trans (p.tensorOne FS FT Φ) (hsb Φ hΦ) x (half_sum p he hx)`. Rewrite using `[LinearMap.comp_apply, tensorOne_modul p ψ FS FT he Φ hy]`.

Conclude with `hT'.modul (p.tensorOne FS FT Φ) (hsb Φ hΦ) y (half_sum_conj p he hy)`. Rewrite using `[LinearMap.comp_apply, tensorOne_vac p FS FT he hint hstab]`. Conclude with `hT'.vac`.
-/
theorem isPlaceModel_tensorOne : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (e : AE D), e * p.e = 0 → (∀ x : Matrix Y Y' k, (∀ r q, x r q ∈ 𝒪[k]) ↔ p.up FS FT x ∈ stdHom S T) → (∀ u ∈ stdHom S T, u.map (fun a => p.e * a) ∈ stdHom S T) → ∀ (f₀ : WO S T → ℂ) (T' : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)), IsPlaceModel ψ (symplO S T) (heisO ψ S T) (e + p.e) (stdHom S T) 1 f₀ T' → (∀ Φ, IsSBHalf e (stdHom S T) Φ → IsSBHalf (e + p.e) (stdHom S T) (p.tensorAt FS FT Φ (Place.intInd Y Y'))) → IsPlaceModel ψ (symplO S T) (heisO ψ S T) e (stdHom S T) 1 f₀ (T' ∘ₗ p.tensorOne FS FT) := by
  intro D k _ _ _ _ p ψ S T Y Y' _ _ _ _ FS FT e he hint hstab f₀ T' hT' hsb
  refine ⟨fun Φ hΦ x hx => ?_, fun Φ hΦ y hy => ?_, ?_⟩
  · rw [LinearMap.comp_apply, tensorOne_trans p FS FT he Φ hx]
    exact hT'.trans (p.tensorOne FS FT Φ) (hsb Φ hΦ) x (half_sum p he hx)
  · rw [LinearMap.comp_apply, tensorOne_modul p ψ FS FT he Φ hy]
    exact hT'.modul (p.tensorOne FS FT Φ) (hsb Φ hΦ) y (half_sum_conj p he hy)
  · rw [LinearMap.comp_apply, tensorOne_vac p FS FT he hint hstab]
    exact hT'.vac

end GlobalTheory.LocMod.TOneModel

end
