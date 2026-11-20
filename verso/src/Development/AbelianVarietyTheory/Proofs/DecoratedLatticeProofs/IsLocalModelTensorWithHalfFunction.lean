import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TiedAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TensorOneApply

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.AdForm GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocMod.TensorModel

variable {D : D7}

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a x`. Rewrite using `[show cA D (cA D (a ⊗ₜ[D.host.F] x)) = a ⊗ₜ[D.host.F] star (star x) from rfl, star_star]`. Consider the case `add x y hx hy => rw [map_add, map_add, hx, hy]`.
-/
theorem cA_invol (z : AE D) : cA D (cA D z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    rw [show cA D (cA D (a ⊗ₜ[D.host.F] x)) = a ⊗ₜ[D.host.F] star (star x) from rfl, star_star]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/- English proof (translation)
Unfold `symplO hO`. Simplify using `only [Matrix.add_apply, mul_add, Finset.sum_add_distrib, map_add]`.
-/
theorem symplO_add_left' (S T : HSp D) (x x' y : WO S T) :
    symplO S T (x + x') y = symplO S T x y + symplO S T x' y := by
  unfold symplO hO
  simp only [Matrix.add_apply, mul_add, Finset.sum_add_distrib, map_add]

/- English proof (translation)
Introduce `i j` and use `by have h0 : e * u i j = 0 := by calc e * u i j = e * (e' * u i j) := by rw [hu i j] _ = 0 := by rw [← mul_assoc, he, zero_mul] rw [add_mul, h0, zero_add, hu i j]`.
-/
theorem half_sum {m n : ℕ} {e e' : AE D} (he : e * e' = 0) {u : Mx D m n} (hu : IsHalf e' u) : IsHalf (e + e') u :=
  fun i j => by
    have h0 : e * u i j = 0 := by
      calc e * u i j = e * (e' * u i j) := by rw [hu i j]
        _ = 0 := by rw [← mul_assoc, he, zero_mul]
    rw [add_mul, h0, zero_add, hu i j]

/- English proof (translation)
Rewrite using `[map_add]`. Use `half_sum ?_ hu` and prove the remaining obligations. Rewrite using `[← map_mul, he, map_zero]`.
-/
theorem half_sum_cA {m n : ℕ} {e e' : AE D} (he : e * e' = 0) {u : Mx D m n} (hu : IsHalf (cA D e') u) :
    IsHalf (cA D (e + e')) u := by
  rw [map_add]
  refine half_sum ?_ hu
  rw [← map_mul, he, map_zero]

/- English proof (translation)
Establish `h0 : hO S T s y = 0`. Unfold `hO`. Use `Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun c _ => Finset.sum_eq_zero fun d _ => ?_` and prove the remaining obligations. Establish `h1 : cA D (y c b) = e' * cA D (y c b)` using `by conv_lhs => rw [← hy c b]`. Rewrite using `[map_mul, cA_invol]`.

Establish `h2 : s d a = e * s d a` using `(hs d a).symm`. Rewrite using `[h1, h2]`. Take the linear combination `(incA D (S.gram⁻¹ a b) * cA D (y c b) * incA D (T.gram c d) * s d a) * he`. Unfold `symplO`. Rewrite using `[h0, mul_zero, map_zero]`.
-/
theorem symplO_half_zero {S T : HSp D} {e e' : AE D} (he : e * e' = 0) {s y : WO S T} (hs : IsHalf e s)
    (hy : IsHalf (cA D e') y) : symplO S T s y = 0 := by
  have h0 : hO S T s y = 0 := by
    unfold hO
    refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun c _ =>
      Finset.sum_eq_zero fun d _ => ?_
    have h1 : cA D (y c b) = e' * cA D (y c b) := by
      conv_lhs => rw [← hy c b]
      rw [map_mul, cA_invol]
    have h2 : s d a = e * s d a := (hs d a).symm
    rw [h1, h2]
    linear_combination (incA D (S.gram⁻¹ a b) * cA D (y c b) * incA D (T.gram c d) * s d a) * he
  unfold symplO
  rw [h0, mul_zero, map_zero]

/- English proof (translation)
Introduce `D k _ _ _ _ p ψ S T Y Y' _ _ _ _ FS FT e he Φ hΦ f₀ T' hP hθ hSB`. Establish `hup : ∀ x, IsHalf (e + p.e) (p.up FS FT x)` using `fun x => half_sum he (Witness.up_half p FS FT x)`. Use `⟨fun Ψ => ?_, fun x Ψ Ψ' h => ?_, fun y hy Ψ Ψ' h => ?_⟩` and prove the remaining obligations. Conclude with `hθ _ (hSB Ψ.1 Ψ.2)`. Establish `key : p.tensorAt FS FT Φ Ψ'.1 = fun t => p.tensorAt FS FT Φ Ψ.1 (t + p.up FS FT x)`.

Use function extensionality and compare the values at `t`. Simplify using `only [Place.tensorAt]`. Rewrite using `[Witness.down_add, Witness.down_up, Witness.up_add, h, add_sub_add_right_eq_sub]`. Simplify using `only [LinearMap.comp_apply, Place.tensorL_apply]`. Rewrite using `[key]`.

Conclude with `hP.trans _ (hSB Ψ.1 Ψ.2) _ (hup x)`. Establish `key : p.tensorAt FS FT Φ Ψ'.1 = fun t => ψ (symplO S T t y) * p.tensorAt FS FT Φ Ψ.1 t`. Use function extensionality and compare the values at `t`. Simplify using `only [Place.tensorAt]`. Rewrite using `[h]`.

Distinguish the cases in `h0 : Φ (t - p.up FS FT (p.down FS FT t)) = 0`. Rewrite using `[h0]`. Expand and normalize the polynomial expressions, which then agree. Establish `e1 : symplO S T t y = symplO S T (t - p.up FS FT (p.down FS FT t)) y + symplO S T (p.up FS FT (p.down FS FT t)) y`. Rewrite using `[← symplO_add_left', sub_add_cancel]`.

Rewrite using `[e1, symplO_half_zero he (hΦ _ h0) hy, zero_add]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [LinearMap.comp_apply, Place.tensorL_apply]`. Rewrite using `[key]`. Conclude with `hP.modul _ (hSB Ψ.1 Ψ.2) _ (half_sum_cA he hy)`.
-/
theorem isModel_tensor : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (e : AE D), e * p.e = 0 → ∀ Φ : WO S T → ℂ, (∀ t, Φ t ≠ 0 → IsHalf e t) → ∀ (f₀ : WO S T → ℂ) (T' : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)), IsPlaceModel ψ (symplO S T) (heisO ψ S T) (e + p.e) (stdHom S T) 1 f₀ T' → (∀ Φ', IsSBHalf (e + p.e) (stdHom S T) Φ' → IsThetaFunO ψ S T (T' Φ')) → (∀ Ψ ∈ SB (Matrix Y Y' k), IsSBHalf (e + p.e) (stdHom S T) (p.tensorAt FS FT Φ Ψ)) → p.IsModel ψ FS FT (T' ∘ₗ p.tensorL FS FT Φ) := by
  intro D k _ _ _ _ p ψ S T Y Y' _ _ _ _ FS FT e he Φ hΦ f₀ T' hP hθ hSB
  have hup : ∀ x, IsHalf (e + p.e) (p.up FS FT x) := fun x => half_sum he (Witness.up_half p FS FT x)
  refine ⟨fun Ψ => ?_, fun x Ψ Ψ' h => ?_, fun y hy Ψ Ψ' h => ?_⟩
  · exact hθ _ (hSB Ψ.1 Ψ.2)
  · have key : p.tensorAt FS FT Φ Ψ'.1 = fun t => p.tensorAt FS FT Φ Ψ.1 (t + p.up FS FT x) := by
      funext t
      simp only [Place.tensorAt]
      rw [Witness.down_add, Witness.down_up, Witness.up_add, h, add_sub_add_right_eq_sub]
    simp only [LinearMap.comp_apply, Place.tensorL_apply]
    rw [key]
    exact hP.trans _ (hSB Ψ.1 Ψ.2) _ (hup x)
  · have key : p.tensorAt FS FT Φ Ψ'.1 = fun t => ψ (symplO S T t y) * p.tensorAt FS FT Φ Ψ.1 t := by
      funext t
      simp only [Place.tensorAt]
      rw [h]
      by_cases h0 : Φ (t - p.up FS FT (p.down FS FT t)) = 0
      · rw [h0]; ring
      · have e1 : symplO S T t y = symplO S T (t - p.up FS FT (p.down FS FT t)) y +
            symplO S T (p.up FS FT (p.down FS FT t)) y := by
          rw [← symplO_add_left', sub_add_cancel]
        rw [e1, symplO_half_zero he (hΦ _ h0) hy, zero_add]
        ring
    simp only [LinearMap.comp_apply, Place.tensorL_apply]
    rw [key]
    exact hP.modul _ (hSB Ψ.1 Ψ.2) _ (half_sum_cA he hy)

end GlobalTheory.LocMod.TensorModel
end
