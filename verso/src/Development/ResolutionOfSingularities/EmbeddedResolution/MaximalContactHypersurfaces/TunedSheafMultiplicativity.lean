import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealSheaf
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.TunedSheaf
universe u v w

open AlgebraicGeometry CategoryTheory

namespace FunctorialResolution.EmbeddedResolution

/- English proof (authored)
Pair the factors at each position in the two list products. Commutativity allows this grouping. The product of those two powers is the power with the sum of their exponents, giving the displayed list product.
-/
private theorem listProd_map_pow_mul_listProd_map_pow {M : Type u} [CommMonoid M] (f : ℕ → M) (c d : ℕ → ℕ) :
    ∀ L : List ℕ, ((L.map fun j => f j ^ c j).prod * (L.map fun j => f j ^ d j).prod)
      = (L.map fun j => f j ^ (c j + d j)).prod := by
  intro L
  rw [← List.prod_map_mul]
  simp [pow_add]

/- English proof (authored)
The supremum of ideal sheaves is evaluated on each affine open by taking the supremum of the section ideals. Applying this description to the given family gives the formula.
-/
private theorem ideal_iSup {X : Scheme.{u}} {ι : Type v} (f : ι → X.IdealSheafData)
    (U : X.affineOpens) : (⨆ i, f i).ideal U = ⨆ i, (f i).ideal U := by simp

/- English proof (authored)
On an affine open the section ideal of the product is the product of the section ideals, and each supremum is computed on section ideals. Multiplication of ideals distributes over the suprema. The resulting pairwise products all lie in the target section ideal by hypothesis, so their supremum does too.
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

/- English proof (authored)
Each exponent function admitted at the successor threshold has weight at least the original threshold. Its product term therefore also occurs in the supremum at the original threshold. Taking the supremum proves the containment.
-/
theorem tunedSheaf_succ_le : TunedSheafSuccLe.{u} := by
  intro k _ _ _ X p _ _ I m _ _ s
  rw [tunedSheaf_eq_iSup, tunedSheaf_eq_iSup]
  refine iSup_le fun c => ?_
  exact le_iSup_of_le ⟨c.1, le_trans (Nat.le_succ s) c.2⟩ le_rfl

/- English proof (authored)
Expand both tuned sheaves as suprema of products of derivative ideal powers. It suffices to bound each pair of product terms. Their product is the term obtained by adding the exponent functions. The weighted sum of the added exponents is the sum of their weights and is therefore at least the sum of the two thresholds. This term appears in the target supremum, giving the containment.
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
