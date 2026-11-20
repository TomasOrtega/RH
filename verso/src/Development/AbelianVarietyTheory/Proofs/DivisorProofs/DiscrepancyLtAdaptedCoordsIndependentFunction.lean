import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CentreAtOfIsAt
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameFormsResidueIndependence
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SncChartKltCriterion
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

set_option autoImplicit false

namespace GlobalTheory.Discrepancy

/- English proof (translation)
Introduce `Y _ _ q n _ B y U hy z J w u hc hJ F hind φ f a c hφ hf ha hc1 E hE`. Use `haveI := SmoothOfRelativeDimension.smooth n q`. Establish `hn : topologicalKrullDim Y = n`. Establish `hd (V : Y.Opens) (hV : IsAffineOpen V) (hne : (V : Set Y).Nonempty) : topologicalKrullDim (V : Set Y) = n`. Rewrite using `[topologicalKrullDim_eq_of_isEmbedding hV.fromSpec.isOpenEmbedding.isEmbedding hV.range_fromSpec]`.

Conclude with `(PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim (R := Γ(Y, V))).trans (SmoothDim.ringKrullDim_affineOpen ℂ _ q _ inferInstance V hV hne)`. Use `le_antisymm (topologicalKrullDim_le_of_forall_exists_isOpen fun x => ?_) ?_` and prove the remaining obligations. Take `⟨V, hV, hx, -⟩` from `TopologicalSpace.Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens (TopologicalSpace.Opens.mem_top x)`. Conclude with `⟨V, V.isOpen, hx, (hd V hV ⟨x, hx⟩).le⟩`. Take `⟨V, hV, hx, -⟩` from `TopologicalSpace.Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens (TopologicalSpace.Opens.mem_top y)`.

Conclude with `(hd V hV ⟨_, hx⟩).ge.trans (topologicalKrullDim_subspace_le _ _)`. Establish `hunit : ∀ g : Y.functionFieldˣ, UnitAt y (g : Y.functionField) → E.ord g = 0`. Introduce and unpack `g ⟨b, hb, hbg⟩`. Establish `h1 : (g : Y.functionField) ∈ E.ring` using `hE _ ⟨b, hbg⟩`. Establish `h2 : ((g⁻¹ : Y.functionFieldˣ) : Y.functionField) ∈ E.ring` using `hE _ ⟨↑(hb.unit⁻¹), by`.

Rewrite using `[map_units_inv, IsUnit.unit_spec, hbg]`. Use the proof step `simp⟩`. Establish `e1` using `(E.ord_nonneg_iff g).2 h1`. Establish `e2` using `(E.ord_nonneg_iff _).2 h2`. Rewrite `e2` using `[E.ord_inv]`.

Use linear arithmetic over natural numbers and integers. Establish `hfφ : E.ord f = E.ord φ`. Establish `hg : UnitAt y ((f * φ⁻¹ : Y.functionFieldˣ) : Y.functionField)`. Simplify `hf` using `[div_eq_mul_inv]`. Establish `h0` using `hunit _ hg`.

Establish `: f = (f * φ⁻¹) * φ` using `by group`. Rewrite using `[this, E.ord_mul, h0, zero_add]`. Distinguish the cases in `hyF : y ∈ Y.basicOpen F`. Establish `hφu : UnitAt y (φ : Y.functionField)` using `hφ ▸ (unitAt_fnOf_iff hy _ F).2 hyF`. Establish `hfu : UnitAt y (f : Y.functionField)`.

Use `UnitAt.mul hf hφu` as an intermediate fact. Rewrite `this` using `[div_mul_cancel₀ _ φ.ne_zero]`. Then use the resulting hypothesis. Establish `h0` using `hunit f hfu`. Establish `key` using `(IsSncChart.neg_one_lt_formOrd_sub_sum ℂ Y q n B y U hy z J w u hc E hE a).1 ha`. Rewrite using `[h0]`.

Simplify using `using key`. Establish `hmax : ∀ j : Option J, Y.presheaf.germ U y hy (j.elim F fun j => z j) ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk y)`. Introduce and unpack `(_ | ⟨j, hj⟩)`. Conclude with `(IsLocalRing.mem_maximalIdeal _).2 (mem_nonunits_iff.2 fun h => hyF ((Scheme.mem_basicOpen Y F y hy).2 h))`. Conclude with `(IsLocalRing.mem_maximalIdeal _).2 (mem_nonunits_iff.2 fun h => hJ j hj ((Scheme.mem_basicOpen Y (z j) y hy).2 h))`.

Establish `hv : ∀ j : Option J, ((j.elim φ fun j => u j : Y.functionFieldˣ) : Y.functionField) = algebraMap (Y.presheaf.stalk y) Y.functionField (Y.presheaf.germ U y hy (j.elim F fun j => z j))`. Introduce and unpack `(_ | ⟨j, hj⟩)`. Simplify using `only [Option.elim]`. Rewrite using `[hφ, algebraMap_germ]`. Simplify using `only [Option.elim]`.

Rewrite using `[hc.val j hj, algebraMap_germ]`. Establish `hc' : ∀ j : Option J, (j.elim c fun j => a j) < 1`. Introduce and unpack `(_ | ⟨j, hj⟩)`. Conclude with `hc1`. Conclude with `ha j hj`.

Establish `key` using `GlobalTheory.IndepDiscrep.neg_one_lt_formOrd_sub_sum Y q n hn y U hy (dOn q z) hc.frame (Option J) (fun j => Y.presheaf.germ U y hy (j.elim F fun j => z j)) hmax (fun j => j.elim φ fun j => u j) (fun j => j.elim c fun j => a j) (hind hmax) hv hc' E hE`. Rewrite `key` using `[Fintype.sum_option]`. Simplify using `only [Option.elim] at key`. Rewrite `key` using `[Finset.sum_coe_sort J (fun j => a j * (E.ord (u j) : ℚ))]`. Rewrite using `[hfφ]`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem IsSncChart.neg_one_lt_formOrd_sub_sum_sub_ord_of_indep : ∀ (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp ℂ) (n : ℕ) [SmoothOfRelativeDimension n q] (B : Closeds Y) (y : Y) (U : Y.Opens) (hy : y ∈ U) (z : Fin n → Γ(Y, U)) (J : Finset (Fin n)) (w : Fin n → Y) (u : Fin n → Y.functionFieldˣ), IsSncChart q n B y U hy z J w u → (∀ j ∈ J, y ∉ Y.basicOpen (z j)) → ∀ F : Γ(Y, U), (∀ h : ∀ j : Option J, Y.presheaf.germ U y hy (j.elim F fun j => z j) ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk y), LinearIndependent (IsLocalRing.ResidueField (Y.presheaf.stalk y)) (fun j : Option J => ((IsLocalRing.maximalIdeal (Y.presheaf.stalk y)).toCotangent ⟨Y.presheaf.germ U y hy (j.elim F fun j => z j), h j⟩ : IsLocalRing.CotangentSpace (Y.presheaf.stalk y)))) → ∀ (φ f : Y.functionFieldˣ) (a : Fin n → ℚ) (c : ℚ), (φ : Y.functionField) = fnOf U (gen_mem hy) F → UnitAt y ((f : Y.functionField) / φ) → (∀ j ∈ J, a j < 1) → c < 1 → ∀ E : DivOver q, E.Through y → -1 < (E.formOrd (formOf U (gen_mem hy) (dOn q z)) : ℚ) - ∑ j ∈ J, a j * E.ord (u j) - c * E.ord f := by
  intro Y _ _ q n _ B y U hy z J w u hc hJ F hind φ f a c hφ hf ha hc1 E hE
  classical
  haveI := SmoothOfRelativeDimension.smooth n q
  have hn : topologicalKrullDim Y = n := by
    have hd (V : Y.Opens) (hV : IsAffineOpen V) (hne : (V : Set Y).Nonempty) :
        topologicalKrullDim (V : Set Y) = n := by
      rw [topologicalKrullDim_eq_of_isEmbedding hV.fromSpec.isOpenEmbedding.isEmbedding
        hV.range_fromSpec]
      exact (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim (R := Γ(Y, V))).trans
        (SmoothDim.ringKrullDim_affineOpen ℂ _ q _ inferInstance V hV hne)
    refine le_antisymm (topologicalKrullDim_le_of_forall_exists_isOpen fun x => ?_) ?_
    · obtain ⟨V, hV, hx, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens
        (TopologicalSpace.Opens.mem_top x)
      exact ⟨V, V.isOpen, hx, (hd V hV ⟨x, hx⟩).le⟩
    · obtain ⟨V, hV, hx, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens
        (TopologicalSpace.Opens.mem_top y)
      exact (hd V hV ⟨_, hx⟩).ge.trans (topologicalKrullDim_subspace_le _ _)

  have hunit : ∀ g : Y.functionFieldˣ, UnitAt y (g : Y.functionField) → E.ord g = 0 := by
    rintro g ⟨b, hb, hbg⟩
    have h1 : (g : Y.functionField) ∈ E.ring := hE _ ⟨b, hbg⟩
    have h2 : ((g⁻¹ : Y.functionFieldˣ) : Y.functionField) ∈ E.ring := hE _ ⟨↑(hb.unit⁻¹), by
      rw [map_units_inv, IsUnit.unit_spec, hbg]; simp⟩
    have e1 := (E.ord_nonneg_iff g).2 h1
    have e2 := (E.ord_nonneg_iff _).2 h2
    rw [E.ord_inv] at e2
    omega
  have hfφ : E.ord f = E.ord φ := by
    have hg : UnitAt y ((f * φ⁻¹ : Y.functionFieldˣ) : Y.functionField) := by
      simpa [div_eq_mul_inv] using hf
    have h0 := hunit _ hg
    have : f = (f * φ⁻¹) * φ := by group
    rw [this, E.ord_mul, h0, zero_add]
  by_cases hyF : y ∈ Y.basicOpen F
  · have hφu : UnitAt y (φ : Y.functionField) := hφ ▸ (unitAt_fnOf_iff hy _ F).2 hyF
    have hfu : UnitAt y (f : Y.functionField) := by
      have := UnitAt.mul hf hφu
      rwa [div_mul_cancel₀ _ φ.ne_zero] at this
    have h0 := hunit f hfu
    have key := (IsSncChart.neg_one_lt_formOrd_sub_sum ℂ Y q n B y U hy z J w u hc E hE a).1 ha
    rw [h0]
    simpa using key
  · have hmax : ∀ j : Option J, Y.presheaf.germ U y hy (j.elim F fun j => z j) ∈
        IsLocalRing.maximalIdeal (Y.presheaf.stalk y) := by
      rintro (_ | ⟨j, hj⟩)
      · exact (IsLocalRing.mem_maximalIdeal _).2
          (mem_nonunits_iff.2 fun h => hyF ((Scheme.mem_basicOpen Y F y hy).2 h))
      · exact (IsLocalRing.mem_maximalIdeal _).2
          (mem_nonunits_iff.2 fun h => hJ j hj ((Scheme.mem_basicOpen Y (z j) y hy).2 h))
    have hv : ∀ j : Option J, ((j.elim φ fun j => u j : Y.functionFieldˣ) : Y.functionField) =
        algebraMap (Y.presheaf.stalk y) Y.functionField
          (Y.presheaf.germ U y hy (j.elim F fun j => z j)) := by
      rintro (_ | ⟨j, hj⟩)
      · simp only [Option.elim]
        rw [hφ, algebraMap_germ]
      · simp only [Option.elim]
        rw [hc.val j hj, algebraMap_germ]
    have hc' : ∀ j : Option J, (j.elim c fun j => a j) < 1 := by
      rintro (_ | ⟨j, hj⟩)
      · exact hc1
      · exact ha j hj
    have key := GlobalTheory.IndepDiscrep.neg_one_lt_formOrd_sub_sum Y q n hn y U hy (dOn q z) hc.frame
      (Option J) (fun j => Y.presheaf.germ U y hy (j.elim F fun j => z j)) hmax
      (fun j => j.elim φ fun j => u j) (fun j => j.elim c fun j => a j) (hind hmax) hv hc' E hE
    rw [Fintype.sum_option] at key
    simp only [Option.elim] at key
    rw [Finset.sum_coe_sort J (fun j => a j * (E.ord (u j) : ℚ))] at key
    rw [hfφ]
    linarith

end GlobalTheory.Discrepancy
