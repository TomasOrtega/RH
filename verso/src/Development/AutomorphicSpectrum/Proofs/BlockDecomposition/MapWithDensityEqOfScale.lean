import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TopoPolish

open MeasureTheory MeasureTheory.Measure
open scoped ENNReal NNReal

namespace GlobalTheory.CompanionTheory.QuotVan

def HaarNM : Prop := ∀ {Q : Type} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
  [LocallyCompactSpace Q] [SecondCountableTopology Q] [T2Space Q] [MeasurableSpace Q] [BorelSpace Q]
  (νQ : Measure Q) [νQ.IsHaarMeasure] (N M : Subgroup Q) [N.Normal]
  (_ : IsClosed (N : Set Q)) (_ : IsClosed (M : Set Q))
  (_ : ∀ q : Q, ∃ u ∈ N, ∃ m ∈ M, q = u * m) (_ : N ⊓ M = ⊥)
  (νN : Measure N) [νN.IsHaarMeasure] (νM : Measure M) [νM.IsHaarMeasure],
  ∃ δ : M → ℝ≥0∞, Measurable δ ∧ (∀ m, δ m ≠ ∞) ∧
    νQ = ((νN.prod νM).withDensity fun p => δ p.2).map (fun p : N × M => (p.1 : Q) * (p.2 : Q))

/- English proof (translation)
Use extensionality with `A hA`. Rewrite using `[map_apply hS hA, withDensity_apply _ (hS hA), withDensity_apply _ hA]`. Establish `key : ∫⁻ x, (A.indicator f) x ∂(ρ.map S) = a * ∫⁻ x, A.indicator f x ∂ρ`. Rewrite using `[hρ, lintegral_smul_measure]`. Both sides reduce to the same expression.

Rewrite `key` using `[lintegral_map (hf.indicator hA) hS]`. Establish `h2 : (fun x => A.indicator f (S x)) = fun x => a * (S ⁻¹' A).indicator f x`. Use function extensionality and compare the values at `x`. Distinguish the cases in `hx : S x ∈ A`. Establish `hx' : x ∈ S ⁻¹' A` using `hx`.

Rewrite using `[Set.indicator_of_mem hx, Set.indicator_of_mem hx', hfS]`. Establish `hx' : x ∉ S ⁻¹' A` using `hx`. Rewrite using `[Set.indicator_of_notMem hx, Set.indicator_of_notMem hx', mul_zero]`. Rewrite `key` using `[h2, lintegral_const_mul _ (hf.indicator (hS hA)), lintegral_indicator (hS hA), lintegral_indicator hA]`. Conclude with `(ENNReal.mul_right_inj ha0 hat).1 key`.
-/
theorem map_withDensity_eq_of_scale {X : Type*} [MeasurableSpace X] (ρ : Measure X) (S : X → X)
    (hS : Measurable S) (f : X → ℝ≥0∞) (hf : Measurable f) (a : ℝ≥0∞) (ha0 : a ≠ 0) (hat : a ≠ ∞)
    (hρ : ρ.map S = a • ρ) (hfS : ∀ x, f (S x) = a * f x) :
    (ρ.withDensity f).map S = ρ.withDensity f := by
  ext A hA
  rw [map_apply hS hA, withDensity_apply _ (hS hA), withDensity_apply _ hA]
  have key : ∫⁻ x, (A.indicator f) x ∂(ρ.map S) = a * ∫⁻ x, A.indicator f x ∂ρ := by
    rw [hρ, lintegral_smul_measure]; rfl
  rw [lintegral_map (hf.indicator hA) hS] at key
  have h2 : (fun x => A.indicator f (S x)) = fun x => a * (S ⁻¹' A).indicator f x := by
    funext x
    by_cases hx : S x ∈ A
    · have hx' : x ∈ S ⁻¹' A := hx
      rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx', hfS]
    · have hx' : x ∉ S ⁻¹' A := hx
      rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx', mul_zero]
  rw [h2, lintegral_const_mul _ (hf.indicator (hS hA)), lintegral_indicator (hS hA),
    lintegral_indicator hA] at key
  exact (ENNReal.mul_right_inj ha0 hat).1 key

section
variable {Q : Type} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]

noncomputable def conjCE (N : Subgroup Q) [N.Normal] (g : Q) : N ≃ₜ* N where
  toMulEquiv := MulAut.conjNormal g
  continuous_toFun := by
    refine continuous_induced_rng.2 ?_
    have : Continuous fun u : N => g * (u : Q) * g⁻¹ := by fun_prop
    exact this
  continuous_invFun := by
    refine continuous_induced_rng.2 ?_
    have : Continuous fun u : N => g⁻¹ * (u : Q) * g⁻¹⁻¹ := by fun_prop
    exact this

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem conjCE_coe (N : Subgroup Q) [N.Normal] (g : Q) (u : N) :
    ((conjCE N g u : N) : Q) = g * u * g⁻¹ := rfl

/- English proof (translation)
Use extensionality with `u`. Simplify using `[conjCE_coe, mul_assoc]`.
-/
theorem conjCE_mul (N : Subgroup Q) [N.Normal] (g h : Q) :
    conjCE N (g * h) = (conjCE N h).trans (conjCE N g) := by
  ext u
  simp [conjCE_coe, mul_assoc]

variable [MeasurableSpace Q] [BorelSpace Q] [SecondCountableTopology Q] [T2Space Q]
variable (N M : Subgroup Q) [N.Normal] [LocallyCompactSpace N] [SecondCountableTopology N]
  [SecondCountableTopology M]

noncomputable def modInv (m : M) : ℝ≥0∞ :=
  ((mulEquivHaarChar (conjCE N (m : Q)) : ℝ≥0) : ℝ≥0∞)⁻¹

/- English proof (translation)
Establish `h` using `(mulEquivHaarChar_pos (conjCE N (m : Q))).ne'`. Simplify using `[modInv, h]`.
-/
theorem modInv_ne_top (m : M) : modInv N M m ≠ ∞ := by
  have h := (mulEquivHaarChar_pos (conjCE N (m : Q))).ne'
  simp [modInv, h]

/- English proof (translation)
Simplify using `[modInv]`.
-/
theorem modInv_ne_zero (m : M) : modInv N M m ≠ 0 := by
  simp [modInv]

/- English proof (translation)
Establish `h1` using `(mulEquivHaarChar_pos (conjCE N (m : Q))).ne'`. Establish `h2` using `(mulEquivHaarChar_pos (conjCE N (m' : Q))).ne'`. Simplify using `only [modInv, Subgroup.coe_mul, conjCE_mul, mulEquivHaarChar_trans, ENNReal.coe_mul]`. Rewrite using `[ENNReal.mul_inv (Or.inr ENNReal.coe_ne_top) (Or.inl ENNReal.coe_ne_top), mul_comm]`.
-/
theorem modInv_mul (m m' : M) : modInv N M (m * m') = modInv N M m * modInv N M m' := by
  have h1 := (mulEquivHaarChar_pos (conjCE N (m : Q))).ne'
  have h2 := (mulEquivHaarChar_pos (conjCE N (m' : Q))).ne'
  simp only [modInv, Subgroup.coe_mul, conjCE_mul, mulEquivHaarChar_trans, ENNReal.coe_mul]
  rw [ENNReal.mul_inv (Or.inr ENNReal.coe_ne_top) (Or.inl ENNReal.coe_ne_top), mul_comm]

/- English proof (translation)
Take `⟨K, hK, hK1⟩` from `exists_compact_mem_nhds (1 : N)`. Use `haveI : ν.Regular := regular_of_isMulLeftInvariant hK ⟨1, mem_interior_iff_mem_nhds.2 hK1⟩ hK.measure_lt_top.ne`. Establish `h` using `mulEquivHaarChar_smul_map ν (conjCE N (m : Q))`. Establish `hc : ((mulEquivHaarChar (conjCE N (m : Q)) : ℝ≥0) : ℝ≥0∞) ≠ 0`. Simplify using `using (mulEquivHaarChar_pos (conjCE N (m : Q))).ne'`.

Rewrite `h` using `[ENNReal.smul_def]`. Use `conv_rhs => rw [← h]`. Rewrite using `[smul_smul, modInv, ENNReal.inv_mul_cancel hc ENNReal.coe_ne_top, one_smul]`.
-/
theorem map_conj (ν : Measure N) [ν.IsHaarMeasure] (m : M) :
    ν.map (conjCE N (m : Q)) = modInv N M m • ν := by
  obtain ⟨K, hK, hK1⟩ := exists_compact_mem_nhds (1 : N)
  haveI : ν.Regular := regular_of_isMulLeftInvariant hK ⟨1, mem_interior_iff_mem_nhds.2 hK1⟩
    hK.measure_lt_top.ne
  have h := mulEquivHaarChar_smul_map ν (conjCE N (m : Q))
  have hc : ((mulEquivHaarChar (conjCE N (m : Q)) : ℝ≥0) : ℝ≥0∞) ≠ 0 := by
    simpa using (mulEquivHaarChar_pos (conjCE N (m : Q))).ne'
  rw [ENNReal.smul_def] at h
  conv_rhs => rw [← h]
  rw [smul_smul, modInv, ENNReal.inv_mul_cancel hc ENNReal.coe_ne_top, one_smul]

/- English proof (translation)
Set `ν : Measure N` to `haar`. Take `⟨K, hK, hK1⟩` from `exists_compact_mem_nhds (1 : N)`. Establish `hs : IsOpen (interior K)` using `isOpen_interior`. Establish `hs0 : ν (interior K) ≠ 0` using `(hs.measure_pos ν ⟨1, mem_interior_iff_mem_nhds.2 hK1⟩).ne'`. Establish `hst : ν (interior K) ≠ ∞` using `((measure_mono interior_subset).trans_lt hK.measure_lt_top).ne`.

Set `F : M × N → N` to `fun p => conjCE N (p.1 : Q) p.2`. Establish `hF : Continuous F`. Use `continuous_induced_rng.2 ?_` and prove the remaining obligations. Establish `: Continuous fun p : M × N => (p.1 : Q) * (p.2 : Q) * (p.1 : Q)⁻¹` using `by fun_prop`. Conclude with `this`.

Establish `hB : MeasurableSet (F ⁻¹' interior K)` using `(hs.preimage hF).measurableSet`. Establish `hm` using `measurable_measure_prodMk_left (ν := ν) hB`. Establish `he : modInv N M = fun m => ν (Prod.mk m ⁻¹' (F ⁻¹' interior K)) / ν (interior K)`. Use function extensionality and compare the values at `m`. Establish `h` using `congrArg (fun μ : Measure N => μ (interior K)) (map_conj N M ν m)`.

Simplify using `only [Measure.smul_apply, smul_eq_mul] at h`. Rewrite `h` using `[map_apply (map_continuous _).measurable hs.measurableSet]`. Establish `h3 : Prod.mk m ⁻¹' (F ⁻¹' interior K) = conjCE N (m : Q) ⁻¹' interior K` using `rfl`. Rewrite using `[h3, h, ENNReal.mul_div_cancel_right hs0 hst]`. Rewrite using `[he]`.

Conclude with `hm.div_const _`.
-/
theorem measurable_modInv : Measurable (modInv N M) := by
  let ν : Measure N := haar
  obtain ⟨K, hK, hK1⟩ := exists_compact_mem_nhds (1 : N)
  have hs : IsOpen (interior K) := isOpen_interior
  have hs0 : ν (interior K) ≠ 0 := (hs.measure_pos ν ⟨1, mem_interior_iff_mem_nhds.2 hK1⟩).ne'
  have hst : ν (interior K) ≠ ∞ :=
    ((measure_mono interior_subset).trans_lt hK.measure_lt_top).ne
  let F : M × N → N := fun p => conjCE N (p.1 : Q) p.2
  have hF : Continuous F := by
    refine continuous_induced_rng.2 ?_
    have : Continuous fun p : M × N => (p.1 : Q) * (p.2 : Q) * (p.1 : Q)⁻¹ := by fun_prop
    exact this
  have hB : MeasurableSet (F ⁻¹' interior K) := (hs.preimage hF).measurableSet
  have hm := measurable_measure_prodMk_left (ν := ν) hB
  have he : modInv N M = fun m => ν (Prod.mk m ⁻¹' (F ⁻¹' interior K)) / ν (interior K) := by
    funext m
    have h := congrArg (fun μ : Measure N => μ (interior K)) (map_conj N M ν m)
    simp only [Measure.smul_apply, smul_eq_mul] at h
    rw [map_apply (map_continuous _).measurable hs.measurableSet] at h
    have h3 : Prod.mk m ⁻¹' (F ⁻¹' interior K) = conjCE N (m : Q) ⁻¹' interior K := rfl
    rw [h3, h, ENNReal.mul_div_cancel_right hs0 hst]
  rw [he]
  exact hm.div_const _

/- English proof (translation)
Establish `hS1 : Measurable fun x : N => u * conjCE N (m : Q) x` using `(continuous_const.mul (map_continuous _)).measurable`. Establish `hS2 : Measurable fun x : M => m * x` using `(continuous_const.mul continuous_id).measurable`. Use `map_withDensity_eq_of_scale _ _ (hS1.prodMap hS2) _ ((measurable_modInv N M).comp measurable_snd) (modInv N M m) (modInv_ne_zero N M m) (modInv_ne_top N M m) ?_ ?_` and prove the remaining obligations. Establish `h1 : νN.map (fun x : N => u * conjCE N (m : Q) x) = modInv N M m • νN`. Establish `h0 : (fun x : N => u * conjCE N (m : Q) x) = (fun x => u * x) ∘ conjCE N (m : Q)` using `rfl`.

Rewrite using `[h0, ← map_map (measurable_const_mul u) (map_continuous _).measurable, map_conj, Measure.map_smul, map_mul_left_eq_self]`. Establish `h2 : νM.map (fun x : M => m * x) = νM` using `map_mul_left_eq_self νM m`. Establish `h3` using `map_prod_map νN νM hS1 hS2`. Rewrite `h3` using `[h1, h2]`. Use `show map (Prod.map _ _) _ = _`.

Rewrite using `[← h3, prod_smul_left]`. Introduce `x`. Conclude with `modInv_mul N M m x.2`.
-/
theorem map_translate (νN : Measure N) [νN.IsHaarMeasure] (νM : Measure M) [νM.IsHaarMeasure]
    [LocallyCompactSpace M] (u : N) (m : M) :
    ((νN.prod νM).withDensity fun p => modInv N M p.2).map
        (fun p : N × M => (u * conjCE N (m : Q) p.1, m * p.2)) =
      (νN.prod νM).withDensity fun p => modInv N M p.2 := by
  have hS1 : Measurable fun x : N => u * conjCE N (m : Q) x :=
    (continuous_const.mul (map_continuous _)).measurable
  have hS2 : Measurable fun x : M => m * x := (continuous_const.mul continuous_id).measurable
  refine map_withDensity_eq_of_scale _ _ (hS1.prodMap hS2) _
    ((measurable_modInv N M).comp measurable_snd) (modInv N M m) (modInv_ne_zero N M m)
    (modInv_ne_top N M m) ?_ ?_
  · have h1 : νN.map (fun x : N => u * conjCE N (m : Q) x) = modInv N M m • νN := by
      have h0 : (fun x : N => u * conjCE N (m : Q) x) = (fun x => u * x) ∘ conjCE N (m : Q) := rfl
      rw [h0, ← map_map (measurable_const_mul u) (map_continuous _).measurable, map_conj,
        Measure.map_smul, map_mul_left_eq_self]
    have h2 : νM.map (fun x : M => m * x) = νM := map_mul_left_eq_self νM m
    have h3 := map_prod_map νN νM hS1 hS2
    rw [h1, h2] at h3
    show map (Prod.map _ _) _ = _
    rw [← h3, prod_smul_left]
  · intro x
    exact modInv_mul N M m x.2

end

/- English proof (translation)
Introduce and unpack `⟨u, m⟩ ⟨u', m'⟩ h`. Establish `h' : (u : Q) * m = u' * m'` using `h`. Establish `h1 : (u' : Q)⁻¹ * u = m' * (m : Q)⁻¹`. Rewrite using `[inv_mul_eq_iff_eq_mul, ← mul_assoc, eq_mul_inv_iff_mul_eq]`. Conclude with `h'`.

Establish `h2 : (u' : Q)⁻¹ * u ∈ N ⊓ M` using `⟨N.mul_mem (N.inv_mem u'.2) u.2, by rw [h1]; exact M.mul_mem m'.2 (M.inv_mem m.2)⟩`. Rewrite `h2` using `[hinf, Subgroup.mem_bot]`. Establish `hu : (u : Q) = u'` using `(inv_mul_eq_one.1 h2).symm`. Establish `hm : (m : Q) = m'`. Rewrite `h'` using `[hu]`.

Conclude with `mul_left_cancel h'`. Conclude with `Prod.ext (Subtype.ext hu) (Subtype.ext hm)`.
-/
theorem mulMap_injective {Q : Type} [Group Q] (N M : Subgroup Q) (hinf : N ⊓ M = ⊥) :
    Function.Injective (fun p : N × M => (p.1 : Q) * (p.2 : Q)) := by
  rintro ⟨u, m⟩ ⟨u', m'⟩ h
  have h' : (u : Q) * m = u' * m' := h
  have h1 : (u' : Q)⁻¹ * u = m' * (m : Q)⁻¹ := by
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, eq_mul_inv_iff_mul_eq]
    exact h'
  have h2 : (u' : Q)⁻¹ * u ∈ N ⊓ M :=
    ⟨N.mul_mem (N.inv_mem u'.2) u.2, by rw [h1]; exact M.mul_mem m'.2 (M.inv_mem m.2)⟩
  rw [hinf, Subgroup.mem_bot] at h2
  have hu : (u : Q) = u' := (inv_mul_eq_one.1 h2).symm
  have hm : (m : Q) = m' := by
    rw [hu] at h'
    exact mul_left_cancel h'
  exact Prod.ext (Subtype.ext hu) (Subtype.ext hm)

/- English proof (translation)
Introduce `Q _ _ _ _ _ _ _ _ νQ _ N M _ hNc hMc hdec hinf νN _ νM _`. Use `haveI : LocallyCompactSpace N := hNc.isClosedEmbedding_subtypeVal.locallyCompactSpace`. Use `haveI : LocallyCompactSpace M := hMc.isClosedEmbedding_subtypeVal.locallyCompactSpace`. Use `haveI : SecondCountableTopology N := Topology.IsEmbedding.subtypeVal.secondCountableTopology`. Use `haveI : SecondCountableTopology M := Topology.IsEmbedding.subtypeVal.secondCountableTopology`.

Use `haveI : PolishSpace N := PI.VolStabS.TopoPolish.polish_of_lcsc N`. Use `haveI : PolishSpace M := PI.VolStabS.TopoPolish.polish_of_lcsc M`. Set `φ : N × M → Q` to `fun p => (p.1 : Q) * (p.2 : Q)`. Establish `φc : Continuous φ` using `by fun_prop`. Establish `φemb : MeasurableEmbedding φ` using `φc.measurableEmbedding (mulMap_injective N M hinf)`.

Set `f : N × M → ℝ≥0∞` to `fun p => modInv N M p.2`. Establish `hf : Measurable f` using `(measurable_modInv N M).comp measurable_snd`. Set `ρ : Measure (N × M)` to `(νN.prod νM).withDensity f`. Set `ν' : Measure Q` to `ρ.map φ`. Use `haveI : SigmaFinite ρ := SigmaFinite.withDensity_of_ne_top (Filter.Eventually.of_forall fun p => modInv_ne_top N M p.2)`.

Use `haveI : SigmaFinite ν' := φemb.sigmaFinite_map`. Use `haveI : ν'.IsMulLeftInvariant := ⟨fun q => by`. Take `⟨u, hu, m, hm, rfl⟩` from `hdec q`. Establish `hS1 : Measurable fun x : N => (⟨u, hu⟩ : N) * conjCE N m x` using `(continuous_const.mul (map_continuous _)).measurable`. Establish `hS2 : Measurable fun x : M => (⟨m, hm⟩ : M) * x` using `(continuous_const.mul continuous_id).measurable`.

Establish `hS : Measurable fun p : N × M => ((⟨u, hu⟩ : N) * conjCE N m p.1, (⟨m, hm⟩ : M) * p.2)` using `hS1.prodMap hS2`. Establish `hcomm : (fun x => u * m * x) ∘ φ = φ ∘ fun p : N × M => ((⟨u, hu⟩ : N) * conjCE N m p.1, (⟨m, hm⟩ : M) * p.2)`. Use function extensionality and compare the values at `p`. Use `show (u * m) * ((p.1 : Q) * p.2) = (u * ((m * p.1) * m⁻¹)) * (m * p.2)`. Use `group`.

Use `show map (fun x => u * m * x) (map φ ρ) = map φ ρ`. Rewrite using `[map_map (measurable_const_mul _) φemb.measurable, hcomm, ← map_map φemb.measurable hS]`. Conclude with `congrArg (map φ) (map_translate N M νN νM ⟨u, hu⟩ ⟨m, hm⟩)⟩`. Establish `hν0 : ν' Set.univ ≠ 0`. Introduce `h0`.

Rewrite `h0` using `[φemb.map_apply, Set.preimage_univ]`. Establish `hac : (νN.prod νM) ≪ ρ` using `withDensity_absolutelyContinuous' hf.aemeasurable (Filter.Eventually.of_forall fun p => modInv_ne_zero N M p.2)`. Conclude with `(isOpen_univ.measure_pos (νN.prod νM) Set.univ_nonempty).ne' (hac h0)`. Take `⟨n, hn⟩ : ∃ n, ν' (spanningSets (ν' + νQ) n) ≠ 0` from `by by_contra! h`. Conclude with `hν0 (by rw [← iUnion_spanningSets (ν' + νQ)]; exact measure_iUnion_null h)`.

Establish `hfin` using `measure_spanningSets_lt_top (ν' + νQ) n`. Rewrite `hfin` using `[Measure.add_apply]`. Take `⟨h1, h2⟩` from `ENNReal.add_lt_top.1 hfin`. Establish `key` using `measure_eq_div_smul νQ ν' hn h1.ne`. Establish `hc : νQ (spanningSets (ν' + νQ) n) / ν' (spanningSets (ν' + νQ) n) ≠ ∞` using `ENNReal.div_ne_top h2.ne hn`.

Generalize the expression as in `νQ (spanningSets (ν' + νQ) n) / ν' (spanningSets (ν' + νQ) n) = c at key hc`. Use `⟨fun m => c * modInv N M m, (measurable_modInv N M).const_mul c, fun m => ENNReal.mul_ne_top hc (modInv_ne_top N M m), key.trans ?_⟩` and prove the remaining obligations. Establish `h3 : (fun p : N × M => c * modInv N M p.2) = c • f` using `rfl`. Rewrite using `[h3, withDensity_smul c hf, Measure.map_smul]`.
-/
theorem haarNM : HaarNM := by
  intro Q _ _ _ _ _ _ _ _ νQ _ N M _ hNc hMc hdec hinf νN _ νM _
  haveI : LocallyCompactSpace N := hNc.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : LocallyCompactSpace M := hMc.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology N := Topology.IsEmbedding.subtypeVal.secondCountableTopology
  haveI : SecondCountableTopology M := Topology.IsEmbedding.subtypeVal.secondCountableTopology
  haveI : PolishSpace N := PI.VolStabS.TopoPolish.polish_of_lcsc N
  haveI : PolishSpace M := PI.VolStabS.TopoPolish.polish_of_lcsc M
  let φ : N × M → Q := fun p => (p.1 : Q) * (p.2 : Q)
  have φc : Continuous φ := by fun_prop
  have φemb : MeasurableEmbedding φ := φc.measurableEmbedding (mulMap_injective N M hinf)
  let f : N × M → ℝ≥0∞ := fun p => modInv N M p.2
  have hf : Measurable f := (measurable_modInv N M).comp measurable_snd
  let ρ : Measure (N × M) := (νN.prod νM).withDensity f
  let ν' : Measure Q := ρ.map φ
  haveI : SigmaFinite ρ := SigmaFinite.withDensity_of_ne_top
    (Filter.Eventually.of_forall fun p => modInv_ne_top N M p.2)
  haveI : SigmaFinite ν' := φemb.sigmaFinite_map
  haveI : ν'.IsMulLeftInvariant := ⟨fun q => by
    obtain ⟨u, hu, m, hm, rfl⟩ := hdec q
    have hS1 : Measurable fun x : N => (⟨u, hu⟩ : N) * conjCE N m x :=
      (continuous_const.mul (map_continuous _)).measurable
    have hS2 : Measurable fun x : M => (⟨m, hm⟩ : M) * x :=
      (continuous_const.mul continuous_id).measurable
    have hS : Measurable fun p : N × M => ((⟨u, hu⟩ : N) * conjCE N m p.1, (⟨m, hm⟩ : M) * p.2) :=
      hS1.prodMap hS2
    have hcomm : (fun x => u * m * x) ∘ φ =
        φ ∘ fun p : N × M => ((⟨u, hu⟩ : N) * conjCE N m p.1, (⟨m, hm⟩ : M) * p.2) := by
      funext p
      show (u * m) * ((p.1 : Q) * p.2) = (u * ((m * p.1) * m⁻¹)) * (m * p.2)
      group
    show map (fun x => u * m * x) (map φ ρ) = map φ ρ
    rw [map_map (measurable_const_mul _) φemb.measurable, hcomm, ← map_map φemb.measurable hS]
    exact congrArg (map φ) (map_translate N M νN νM ⟨u, hu⟩ ⟨m, hm⟩)⟩
  have hν0 : ν' Set.univ ≠ 0 := by
    intro h0
    rw [φemb.map_apply, Set.preimage_univ] at h0
    have hac : (νN.prod νM) ≪ ρ := withDensity_absolutelyContinuous' hf.aemeasurable
      (Filter.Eventually.of_forall fun p => modInv_ne_zero N M p.2)
    exact (isOpen_univ.measure_pos (νN.prod νM) Set.univ_nonempty).ne' (hac h0)
  obtain ⟨n, hn⟩ : ∃ n, ν' (spanningSets (ν' + νQ) n) ≠ 0 := by
    by_contra! h
    exact hν0 (by rw [← iUnion_spanningSets (ν' + νQ)]; exact measure_iUnion_null h)
  have hfin := measure_spanningSets_lt_top (ν' + νQ) n
  rw [Measure.add_apply] at hfin
  obtain ⟨h1, h2⟩ := ENNReal.add_lt_top.1 hfin
  have key := measure_eq_div_smul νQ ν' hn h1.ne
  have hc : νQ (spanningSets (ν' + νQ) n) / ν' (spanningSets (ν' + νQ) n) ≠ ∞ :=
    ENNReal.div_ne_top h2.ne hn
  generalize νQ (spanningSets (ν' + νQ) n) / ν' (spanningSets (ν' + νQ) n) = c at key hc
  refine ⟨fun m => c * modInv N M m, (measurable_modInv N M).const_mul c,
    fun m => ENNReal.mul_ne_top hc (modInv_ne_top N M m), key.trans ?_⟩
  have h3 : (fun p : N × M => c * modInv N M p.2) = c • f := rfl
  rw [h3, withDensity_smul c hf, Measure.map_smul]

end GlobalTheory.CompanionTheory.QuotVan
