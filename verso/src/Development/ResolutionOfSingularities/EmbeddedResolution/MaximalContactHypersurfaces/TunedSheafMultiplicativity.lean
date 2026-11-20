import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealSheaf
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.TunedSheaf
universe u v w

open AlgebraicGeometry CategoryTheory

namespace FunctorialResolution.EmbeddedResolution

/- English proof (translation)
Introduce `L`. Rewrite using `[← List.prod_map_mul]`. Simplify using `[pow_add]`.
-/
private theorem listProd_map_pow_mul_listProd_map_pow {M : Type u} [CommMonoid M] (f : ℕ → M) (c d : ℕ → ℕ) :
    ∀ L : List ℕ, ((L.map fun j => f j ^ c j).prod * (L.map fun j => f j ^ d j).prod)
      = (L.map fun j => f j ^ (c j + d j)).prod := by
  intro L
  rw [← List.prod_map_mul]
  simp [pow_add]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
private theorem ideal_iSup {X : Scheme.{u}} {ι : Type v} (f : ι → X.IdealSheafData)
    (U : X.affineOpens) : (⨆ i, f i).ideal U = ⨆ i, (f i).ideal U := by simp

/- English proof (translation)
Use `Scheme.IdealSheafData.le_def.mpr fun U => ?_` and prove the remaining obligations. Use `show (⨆ i, f i).ideal U * (⨆ j, g j).ideal U ≤ h.ideal U`. Rewrite using `[ideal_iSup, ideal_iSup, Submodule.iSup_mul]`. Use `iSup_le fun i => ?_` and prove the remaining obligations. Rewrite using `[Submodule.mul_iSup]`.

Use `iSup_le fun j => ?_` and prove the remaining obligations. Conclude with `Scheme.IdealSheafData.le_def.mp (H i j) U`.
-/
private theorem iSup_mul_iSup_le {X : Scheme.{u}} {ι : Type v} {κ : Type w}
    (f : ι → X.IdealSheafData) (g : κ → X.IdealSheafData) (h : X.IdealSheafData)
    (H : ∀ i j, f i * g j ≤ h) : (⨆ i, f i) * (⨆ j, g j) ≤ h := by
  refine Scheme.IdealSheafData.le_def.mpr fun U => ?_
  show (⨆ i, f i).ideal U * (⨆ j, g j).ideal U ≤ h.ideal U
  rw [ideal_iSup, ideal_iSup, Submodule.iSup_mul]
  refine iSup_le fun i => ?_
  rw [Submodule.mul_iSup]
  refine iSup_le fun j => ?_
  exact Scheme.IdealSheafData.le_def.mp (H i j) U

/- English proof (translation)
Introduce `k _ _ _ X p _ _ I m _ _ s`. Rewrite using `[tunedSheaf_eq_iSup, tunedSheaf_eq_iSup]`. Use `iSup_le fun c => ?_` and prove the remaining obligations. Conclude with `le_iSup_of_le ⟨c.1, le_trans (Nat.le_succ s) c.2⟩ le_rfl`.
-/
theorem tunedSheaf_succ_le : TunedSheafSuccLe.{u} := by
  intro k _ _ _ X p _ _ I m _ _ s
  rw [tunedSheaf_eq_iSup, tunedSheaf_eq_iSup]
  refine iSup_le fun c => ?_
  exact le_iSup_of_le ⟨c.1, le_trans (Nat.le_succ s) c.2⟩ le_rfl

/- English proof (translation)
Introduce `k _ _ _ X p _ _ I m _ _ s t`. Rewrite using `[tunedSheaf_eq_iSup, tunedSheaf_eq_iSup, tunedSheaf_eq_iSup]`. Use `iSup_mul_iSup_le _ _ _ fun c d => ?_` and prove the remaining obligations. Use `le_iSup_of_le ⟨fun j => c.1 j + d.1 j, ?_⟩ (le_of_eq ?_)` and prove the remaining obligations. Use `show s + t ≤ ∑ j ∈ Finset.range m, (m - j) * (c.1 j + d.1 j)`.

Establish `hsum : ∑ j ∈ Finset.range m, (m - j) * (c.1 j + d.1 j) = (∑ j ∈ Finset.range m, (m - j) * c.1 j) + ∑ j ∈ Finset.range m, (m - j) * d.1 j`. Rewrite using `[← Finset.sum_add_distrib]`. Conclude with `Finset.sum_congr rfl fun j _ => Nat.mul_add _ _ _`. Establish `h1` using `c.2`. Establish `h2` using `d.2`.

Use linear arithmetic over natural numbers and integers. Conclude with `listProd_map_pow_mul_listProd_map_pow (fun j => derivIdealSheafIterate k p j I) c.1 d.1 (List.range m)`.
-/
theorem tunedSheaf_mul_le_add : TunedSheafMulLeAdd.{u} := by
  intro k _ _ _ X p _ _ I m _ _ s t
  rw [tunedSheaf_eq_iSup, tunedSheaf_eq_iSup, tunedSheaf_eq_iSup]
  refine iSup_mul_iSup_le _ _ _ fun c d => ?_
  refine le_iSup_of_le ⟨fun j => c.1 j + d.1 j, ?_⟩ (le_of_eq ?_)
  · show s + t ≤ ∑ j ∈ Finset.range m, (m - j) * (c.1 j + d.1 j)
    have hsum : ∑ j ∈ Finset.range m, (m - j) * (c.1 j + d.1 j)
        = (∑ j ∈ Finset.range m, (m - j) * c.1 j) + ∑ j ∈ Finset.range m, (m - j) * d.1 j := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => Nat.mul_add _ _ _
    have h1 := c.2
    have h2 := d.2
    omega
  · exact listProd_map_pow_mul_listProd_map_pow (fun j => derivIdealSheafIterate k p j I) c.1 d.1 (List.range m)

end FunctorialResolution.EmbeddedResolution
