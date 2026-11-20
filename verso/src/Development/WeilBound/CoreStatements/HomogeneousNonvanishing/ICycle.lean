import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ConjugateHermitianLineIsometries
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M GlobalTheory.CompanionTheory.Ar.Cmp Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)

namespace PositivityTheory.UnitarySelfGeneration

/- English proof (translation)
Establish `: u * f ∈ W` using `by simpa using W.add_mem (hP h) (W.mul_mem_left v hg)`. Conclude with `(hW.mem_or_mem this).resolve_left hu`.
-/
theorem icyc_mem {R : Type*} [CommRing R] {P W : Ideal R} (hW : W.IsPrime) (hP : P ≤ W) {f g u v : R}
    (hu : u ∉ W) (h : u * f - v * g ∈ P) (hg : g ∈ W) : f ∈ W := by
  have : u * f ∈ W := by simpa using W.add_mem (hP h) (W.mul_mem_left v hg)
  exact (hW.mem_or_mem this).resolve_left hu

/- English proof (translation)
Introduce and unpack `W ⟨⟨⟨hWp, hle⟩, hmin⟩, hr⟩`. Establish `hPW : P ≤ W` using `le_sup_left.trans hle`. Establish `hf : f ∈ W` using `hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self f))`. Use `⟨⟨⟨hWp, sup_le hPW ?_⟩, ?_⟩, hr⟩` and prove the remaining obligations. Take `⟨u, v, hu, -, huv⟩` from `h' W hWp hPW hr`.

Rewrite using `[Ideal.span_singleton_le_iff_mem]`. Conclude with `icyc_mem hWp hPW hu huv hf`. Introduce and unpack `W' ⟨hW'p, hle'⟩ hWW`. Establish `hPW' : P ≤ W'` using `le_sup_left.trans hle'`. Establish `hr' : IsRelevant W'` using `fun k => (hr k).imp fun i hi hi' => hi (hWW hi')`.

Take `⟨u, v, hu, -, huv⟩` from `h W' hW'p hPW' hr'`. Use `hmin ⟨hW'p, sup_le hPW' ?_⟩ hWW` and prove the remaining obligations. Rewrite using `[Ideal.span_singleton_le_iff_mem]`. Conclude with `icyc_mem hW'p hPW' hu huv (hle' (Ideal.mem_sup_right (Ideal.mem_span_singleton_self g)))`.
-/
theorem icyc_sub {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (f g : MRing ι)
    (h : ∀ W : Ideal (MRing ι), W.IsPrime → P ≤ W → IsRelevant W →
      ∃ u v : MRing ι, u ∉ W ∧ v ∉ W ∧ u * f - v * g ∈ P)
    (h' : ∀ W : Ideal (MRing ι), W.IsPrime → P ≤ W → IsRelevant W →
      ∃ u v : MRing ι, u ∉ W ∧ v ∉ W ∧ u * g - v * f ∈ P) : divSupp P f ⊆ divSupp P g := by
  rintro W ⟨⟨⟨hWp, hle⟩, hmin⟩, hr⟩
  have hPW : P ≤ W := le_sup_left.trans hle
  have hf : f ∈ W := hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self f))
  refine ⟨⟨⟨hWp, sup_le hPW ?_⟩, ?_⟩, hr⟩
  · obtain ⟨u, v, hu, -, huv⟩ := h' W hWp hPW hr
    rw [Ideal.span_singleton_le_iff_mem]
    exact icyc_mem hWp hPW hu huv hf
  · rintro W' ⟨hW'p, hle'⟩ hWW
    have hPW' : P ≤ W' := le_sup_left.trans hle'
    have hr' : IsRelevant W' := fun k => (hr k).imp fun i hi hi' => hi (hWW hi')
    obtain ⟨u, v, hu, -, huv⟩ := h W' hW'p hPW' hr'
    refine hmin ⟨hW'p, sup_le hPW' ?_⟩ hWW
    rw [Ideal.span_singleton_le_iff_mem]
    exact icyc_mem hW'p hPW' hu huv (hle' (Ideal.mem_sup_right (Ideal.mem_span_singleton_self g)))

/- English proof (translation)
Rewrite using `[Ideal.map_le_iff_le_comap]`. Use `sup_le (le_sup_left.trans Ideal.le_comap_map) ?_` and prove the remaining obligations. Rewrite using `[Ideal.span_singleton_le_iff_mem, Ideal.mem_comap]`. Establish `hU : IsUnit (algebraMap R (Localization.AtPrime W) u)` using `IsLocalization.map_units (Localization.AtPrime W) (⟨u, hu⟩ : W.primeCompl)`. Rewrite using `[← Ideal.unit_mul_mem_iff_mem _ hU, ← map_mul]`.

Apply `Ideal.mem_map_of_mem` to reduce the goal to its premises. Use `(P ⊔ Ideal.span {g}).add_mem (Ideal.mem_sup_left h) (Ideal.mem_sup_right (Ideal.mul_mem_left _ v (Ideal.mem_span_singleton_self g)))` as an intermediate fact. Simplify using `using this`.
-/
theorem icyc_map {R : Type*} [CommRing R] (W : Ideal R) [W.IsPrime] (P : Ideal R) (f g u v : R)
    (hu : u ∉ W) (h : u * f - v * g ∈ P) :
    Ideal.map (algebraMap R (Localization.AtPrime W)) (P ⊔ Ideal.span {f}) ≤
      Ideal.map (algebraMap R (Localization.AtPrime W)) (P ⊔ Ideal.span {g}) := by
  rw [Ideal.map_le_iff_le_comap]
  refine sup_le (le_sup_left.trans Ideal.le_comap_map) ?_
  rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap]
  have hU : IsUnit (algebraMap R (Localization.AtPrime W) u) :=
    IsLocalization.map_units (Localization.AtPrime W) (⟨u, hu⟩ : W.primeCompl)
  rw [← Ideal.unit_mul_mem_iff_mem _ hU, ← map_mul]
  apply Ideal.mem_map_of_mem
  have := (P ⊔ Ideal.span {g}).add_mem (Ideal.mem_sup_left h)
    (Ideal.mem_sup_right (Ideal.mul_mem_left _ v (Ideal.mem_span_singleton_self g)))
  simpa using this

/- English proof (translation)
Use `LinearEquiv.length_eq ?_` and prove the remaining obligations. Conclude with `((LocalizedModule.equivTensorProduct W.primeCompl (R ⧸ J)).trans (Algebra.TensorProduct.quotIdealMapEquivTensorQuot (Localization.AtPrime W) J).toLinearEquiv.symm)`.
-/
theorem icyc_len {R : Type*} [CommRing R] (W : Ideal R) [W.IsPrime] (J : Ideal R) :
    Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (R ⧸ J)) =
      Module.length (Localization.AtPrime W)
        (Localization.AtPrime W ⧸ Ideal.map (algebraMap R (Localization.AtPrime W)) J) := by
  refine LinearEquiv.length_eq ?_
  exact ((LocalizedModule.equivTensorProduct W.primeCompl (R ⧸ J)).trans
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot (Localization.AtPrime W) J).toLinearEquiv.symm)

/- English proof (translation)
Introduce `K _ ι _ P f g h`. Take `⟨-, -, h⟩` from `h`. Establish `h' : ∀ W : Ideal (MRing ι), W.IsPrime → P ≤ W → IsRelevant W → ∃ u v : MRing ι, u ∉ W ∧ v ∉ W ∧ u * g - v * f ∈ P`. Introduce `W hW hP hr`. Take `⟨u, v, hu, hv, huv⟩` from `h W hW hP hr`.

Conclude with `⟨v, u, hv, hu, by simpa using P.neg_mem huv⟩`. Use `⟨Set.Subset.antisymm (icyc_sub P f g h h') (icyc_sub P g f h' h), fun W hW => ?_⟩` and prove the remaining obligations. Establish `hWp : W.IsPrime` using `hW.1.1.1`. Establish `hPW : P ≤ W` using `le_sup_left.trans hW.1.1.2`. Take `⟨u, v, hu, hv, huv⟩` from `h W hWp hPW hW.2`.

Unfold `multAt`. Rewrite using `[dif_pos hWp, dif_pos hWp]`. Use `congr 1`. Rewrite using `[icyc_len, icyc_len]`. Establish `e : Ideal.map (algebraMap (MRing ι) (Localization.AtPrime W)) (P ⊔ Ideal.span {f}) = Ideal.map (algebraMap (MRing ι) (Localization.AtPrime W)) (P ⊔ Ideal.span {g})` using `le_antisymm (icyc_map W P f g u v hu huv) (icyc_map W P g f v u hv (by simpa using P.neg_mem huv))`.

Rewrite using `[e]`.
-/
theorem i_cycle : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (f g : MRing ι), UnitRatio P f g → divSupp P f = divSupp P g ∧ ∀ W ∈ divSupp P f, multAt (P ⊔ Ideal.span {f}) W = multAt (P ⊔ Ideal.span {g}) W := by
  intro K _ ι _ P f g h
  obtain ⟨-, -, h⟩ := h
  have h' : ∀ W : Ideal (MRing ι), W.IsPrime → P ≤ W → IsRelevant W →
      ∃ u v : MRing ι, u ∉ W ∧ v ∉ W ∧ u * g - v * f ∈ P := by
    intro W hW hP hr
    obtain ⟨u, v, hu, hv, huv⟩ := h W hW hP hr
    exact ⟨v, u, hv, hu, by simpa using P.neg_mem huv⟩
  refine ⟨Set.Subset.antisymm (icyc_sub P f g h h') (icyc_sub P g f h' h), fun W hW => ?_⟩
  have hWp : W.IsPrime := hW.1.1.1
  have hPW : P ≤ W := le_sup_left.trans hW.1.1.2
  obtain ⟨u, v, hu, hv, huv⟩ := h W hWp hPW hW.2
  unfold multAt
  rw [dif_pos hWp, dif_pos hWp]
  congr 1
  rw [icyc_len, icyc_len]
  have e : Ideal.map (algebraMap (MRing ι) (Localization.AtPrime W)) (P ⊔ Ideal.span {f}) =
      Ideal.map (algebraMap (MRing ι) (Localization.AtPrime W)) (P ⊔ Ideal.span {g}) :=
    le_antisymm (icyc_map W P f g u v hu huv) (icyc_map W P g f v u hv (by simpa using P.neg_mem huv))
  rw [e]

end PositivityTheory.UnitarySelfGeneration
