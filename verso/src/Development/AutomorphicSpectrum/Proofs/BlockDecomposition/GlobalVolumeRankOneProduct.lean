import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HypOneZeroZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LinearlyIndependentFramesOpen
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GramFibreMeasureFreeTupleNeZeroFinite
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsFibreMeasuresArchimedeanGramMap
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.LBSubm
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRing
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHaarMeasure
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CompletionIsLocalRing
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InfiniteAdelesLocalRingTotallyReal
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.FreeLocal

open Set

section Gen

variable {V X Y : Type} [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V] [T2Space V]
  [LocallyCompactSpace V] [SecondCountableTopology V] [TopologicalSpace X] [MeasurableSpace X]
  {μ : Measure V} {ν : Measure X} {f : V → Y} {ι : X → Y} {U : Set V} {fib : X → Measure V}

/- English proof (translation)
Take `⟨g, hg1, hgc, hgs, -⟩` from `exists_continuousMap_one_of_isCompact_subset_isOpen hK hU hKU`. Establish `hI` using `(h.2.2 g g.continuous hgc hgs).1 b (mem_univ b)`. Combine the equalities or inequalities in the displayed calculation. Distinguish the cases in `hv : v ∈ K`. Simplify using `[indicator_of_mem hv, hg1 hv]`.

Simplify using `[indicator_of_notMem hv]`. Use `_ < ⊤ := hI.lintegral_lt_top`.
-/
theorem fib_lt_top (h : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι U ν univ fib) (hU : IsOpen U) (b : X)
    {K : Set V} (hK : IsCompact K) (hKU : K ⊆ U) : fib b K < ⊤ := by
  obtain ⟨g, hg1, hgc, hgs, -⟩ := exists_continuousMap_one_of_isCompact_subset_isOpen hK hU hKU
  have hI := (h.2.2 g g.continuous hgc hgs).1 b (mem_univ b)
  calc fib b K = ∫⁻ v, K.indicator 1 v ∂(fib b) := (lintegral_indicator_one hK.measurableSet).symm
    _ ≤ ∫⁻ v, ENNReal.ofReal (g v) ∂(fib b) := lintegral_mono fun v => by
        by_cases hv : v ∈ K
        · simp [indicator_of_mem hv, hg1 hv]
        · simp [indicator_of_notMem hv]
    _ < ⊤ := hI.lintegral_lt_top

/- English proof (translation)
Establish `hc : fib b Uᶜ = 0` using `measure_mono_null (compl_subset_compl.2 inter_subset_right) (h.1 b)`. Use `haveI : LocallyCompactSpace U := hU.locallyCompactSpace`. Establish `hσ : IsSigmaCompact U` using `isSigmaCompact_iff_sigmaCompactSpace.2 inferInstance`. Take `⟨K, hKc, hKU⟩` from `hσ`. Establish `hsub : ∀ n, K n ⊆ U` using `fun n => hKU ▸ subset_iUnion K n`.

Use `Measure.FiniteSpanningSetsIn.sigmaFinite (μ := fib b) (C := univ) { set := fun n => K n ∪ Uᶜ, set_mem := fun _ => mem_univ _, finite := fun n => ?_, spanning := ?_ }` and prove the remaining obligations. Conclude with `(measure_union_le _ _).trans_lt (ENNReal.add_lt_top.2 ⟨fib_lt_top h hU b (hKc n) (hsub n), by simp [hc]⟩)`. Use `eq_univ_of_forall fun x => ?_` and prove the remaining obligations. Distinguish the cases in `hx : x ∈ U`. Rewrite `hx` using `[← hKU]`.

Take `⟨n, hn⟩` from `mem_iUnion.1 hx`. Conclude with `mem_iUnion.2 ⟨n, Or.inl hn⟩`. Conclude with `mem_iUnion.2 ⟨0, Or.inr hx⟩`.
-/
theorem sigmaFinite_fib (h : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι U ν univ fib) (hU : IsOpen U)
    (b : X) : SigmaFinite (fib b) := by
  have hc : fib b Uᶜ = 0 :=
    measure_mono_null (compl_subset_compl.2 inter_subset_right) (h.1 b)
  haveI : LocallyCompactSpace U := hU.locallyCompactSpace
  have hσ : IsSigmaCompact U := isSigmaCompact_iff_sigmaCompactSpace.2 inferInstance
  obtain ⟨K, hKc, hKU⟩ := hσ
  have hsub : ∀ n, K n ⊆ U := fun n => hKU ▸ subset_iUnion K n
  refine Measure.FiniteSpanningSetsIn.sigmaFinite
    (μ := fib b) (C := univ)
    { set := fun n => K n ∪ Uᶜ, set_mem := fun _ => mem_univ _, finite := fun n => ?_, spanning := ?_ }
  · exact (measure_union_le _ _).trans_lt
      (ENNReal.add_lt_top.2 ⟨fib_lt_top h hU b (hKc n) (hsub n), by simp [hc]⟩)
  · refine eq_univ_of_forall fun x => ?_
    by_cases hx : x ∈ U
    · rw [← hKU] at hx
      obtain ⟨n, hn⟩ := mem_iUnion.1 hx
      exact mem_iUnion.2 ⟨n, Or.inl hn⟩
    · exact mem_iUnion.2 ⟨0, Or.inr hx⟩

end Gen

section Rat

variable {F E : Type} [Field F] [Field E] [Algebra F E]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[gramR, gramE, hE, hR, hform, ratTup, JR, sigR, inclR, Matrix.map_apply, mul_assoc]`.
-/
theorem gramR_ratTup_eq (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {M n : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (X : Fin n → Fin M → E) :
    gramR R σ J (ratTup (F := F) R X) = (gramE σ J X).map (inclR R) := by
  ext i j
  simp [gramR, gramE, hE, hR, hform, ratTup, JR, sigR, inclR, Matrix.map_apply, mul_assoc]

/- English proof (translation)
Establish `h0 : X 0 ≠ 0` using `hX.ne_zero 0`. Take `⟨i, hi⟩` from `Function.ne_iff.1 h0`. Establish `hu : IsUnit (inclR (F` using `F) R (X 0 i)) := (isUnit_iff_ne_zero.2 hi).map _`. Use `Fintype.linearIndependent_iff.2 fun g hg k => ?_` and prove the remaining obligations. Establish `hk : k = 0` using `Subsingleton.elim _ _`.

Substitute `hk` using the available equality. Establish `h1` using `congrFun hg i`. Simplify using `only [Fin.sum_univ_one, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, ratTup] at h1`. Conclude with `(hu.mul_left_eq_zero).1 h1`.
-/
theorem ratTup_free (R : Type) [CommRing R] [Algebra F R] {M : ℕ} (X : Fin 1 → Fin M → E)
    (hX : LinearIndependent E X) : LinearIndependent (R ⊗[F] E) (ratTup (F := F) R X) := by
  have h0 : X 0 ≠ 0 := hX.ne_zero 0
  obtain ⟨i, hi⟩ := Function.ne_iff.1 h0
  have hu : IsUnit (inclR (F := F) R (X 0 i)) := (isUnit_iff_ne_zero.2 hi).map _
  refine Fintype.linearIndependent_iff.2 fun g hg k => ?_
  have hk : k = 0 := Subsingleton.elim _ _
  subst hk
  have h1 := congrFun hg i
  simp only [Fin.sum_univ_one, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, ratTup] at h1
  exact (hu.mul_left_eq_zero).1 h1

end Rat

section Arch

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Take `⟨n, m, eV, eH, f', hV, hH, hf', hG, hsurj⟩` from `GlobalTheory.ArchGramFibre.exists_submersion_coords F E σ hCM M a J hJ`. Establish `: BorelSpace (Ainf F ⊗[F] E)` using `⟨rfl⟩`. Establish `: BorelSpace (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HermR (Ainf F) σ a)` using `⟨rfl⟩`. Establish `: ContinuousAdd (Fin a → Fin M → Ainf F ⊗[F] E)` using `⟨by`. Establish `e : (fun p : (Fin a → Fin M → Ainf F ⊗[F] E) × (Fin a → Fin M → Ainf F ⊗[F] E) => p.1 + p.2) = fun p => eV.symm (eV p.1 + eV p.2)`.

Use function extensionality and compare the values at `p`. Rewrite using `[← hV, Homeomorph.symm_apply_apply]`. Rewrite using `[e]`. Use the proof step `fun_prop⟩`. Establish `: ContinuousAdd (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HermR (Ainf F) σ a)` using `⟨by`.

Establish `e : (fun p : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HermR (Ainf F) σ a × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HermR (Ainf F) σ a => p.1 + p.2) = fun p => eH.symm (eH p.1 + eH p.2)`. Use function extensionality and compare the values at `p`. Rewrite using `[← hH, Homeomorph.symm_apply_apply]`. Rewrite using `[e]`. Use the proof step `fun_prop⟩`.

Establish `hμ' : (μ.map eV).IsAddHaarMeasure` using `Measure.isAddHaarMeasure_map μ (AddMonoidHom.mk' eV hV) eV.continuous eV.surjective (eV.map_cocompact).le`. Establish `hν' : (ν.map eH).IsAddHaarMeasure` using `Measure.isAddHaarMeasure_map ν (AddMonoidHom.mk' eH hH) eH.continuous eH.surjective (eH.map_cocompact).le`. Establish `hW' : IsOpen (eV.symm ⁻¹' W)` using `hW.preimage eV.symm.continuous`. Establish `hx0W : eV x ∈ eV.symm ⁻¹' W` using `by show eV.symm (eV x) ∈ W`. Rewrite using `[Homeomorph.symm_apply_apply]`.

Conclude with `hxW`. Take `⟨c, hc0, hct, N', hN', hlb'⟩` from `PI.VolStabS.submLB_holds n m _ _ hμ' hν' f' hf' (eV x) (hsurj x hx) _ hW' hx0W`. Establish `hfx0 : f' (eV x) = eH S0`. Establish `h1 : eH.symm (f' (eV x)) = S0` using `Subtype.ext ((hG x).trans hxS)`. Rewrite using `[← h1, Homeomorph.apply_symm_apply]`.

Establish `hN : eH ⁻¹' N' ∈ 𝓝 S0` using `eH.continuous.continuousAt.preimage_mem_nhds (hfx0 ▸ hN')`. Use `⟨c, hc0, hct, _, hN, fun S hSN hSm => ?_⟩` and prove the remaining obligations. Establish `hS'm : MeasurableSet (eH.symm ⁻¹' S)` using `eH.symm.continuous.measurable hSm`. Establish `hS'N : eH.symm ⁻¹' S ⊆ N'` using `fun z hz => by`. Use `hSN hz` as an intermediate fact.

Rewrite `this` using `[mem_preimage, Homeomorph.apply_symm_apply]`. Then use the resulting hypothesis. Establish `h` using `hlb' _ hS'N hS'm`. Rewrite `h` using `[show (ν.map eH) = ν.map eH.toMeasurableEquiv from rfl, show (μ.map eV) = μ.map eV.toMeasurableEquiv from rfl, MeasurableEquiv.map_apply, MeasurableEquiv.map_apply]`. Establish `e1 : eH.toMeasurableEquiv ⁻¹' (eH.symm ⁻¹' S) = S`. Use extensionality with `z`.

Simplify using the standard rewrite rules. Establish `e2 : eV.toMeasurableEquiv ⁻¹' (f' ⁻¹' (eH.symm ⁻¹' S) ∩ eV.symm ⁻¹' W) = (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.gramR (Ainf F) σ J) ⁻¹' (Subtype.val '' S) ∩ W`. Use extensionality with `X`. Simplify using `only [mem_preimage, mem_inter_iff, Homeomorph.toMeasurableEquiv_coe, Homeomorph.symm_apply_apply, mem_image]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨h1, h2⟩`. Conclude with `⟨⟨_, h1, hG X⟩, h2⟩`. Introduce and unpack `⟨⟨s, hs, hsX⟩, h2⟩`. Use `⟨?_, h2⟩` and prove the remaining obligations. Establish `: s = eH.symm (f' (eV X))` using `Subtype.ext (hsX.trans (hG X).symm)`.

Rewrite using `[← this]`. Conclude with `hs`. Rewrite `h` using `[e1, e2]`. Conclude with `h`.
-/
theorem arch_lb (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M a : ℕ) (J : Matrix (Fin M) (Fin M) E)
    (hJ : IsHermND σ J) (μ : Measure (Fin a → Fin M → Ainf F ⊗[F] E))
    (ν : Measure (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HermR (Ainf F) σ a)) (hμ : μ.IsAddHaarMeasure) (hν : ν.IsAddHaarMeasure)
    (x : Fin a → Fin M → Ainf F ⊗[F] E) (S0 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HermR (Ainf F) σ a)
    (hx : LinearIndependent (Ainf F ⊗[F] E) x)
    (hxS : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.gramR (Ainf F) σ J x = (S0 : Matrix (Fin a) (Fin a) (Ainf F ⊗[F] E)))
    (W : Set (Fin a → Fin M → Ainf F ⊗[F] E)) (hW : IsOpen W) (hxW : x ∈ W) :
    ∃ c : ℝ≥0∞, 0 < c ∧ c ≠ ⊤ ∧ ∃ N ∈ 𝓝 S0, ∀ S ⊆ N, MeasurableSet S →
      c * ν S ≤ μ ((Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.gramR (Ainf F) σ J) ⁻¹' (Subtype.val '' S) ∩ W) := by
  obtain ⟨n, m, eV, eH, f', hV, hH, hf', hG, hsurj⟩ :=
    GlobalTheory.ArchGramFibre.exists_submersion_coords F E σ hCM M a J hJ
  have : BorelSpace (Ainf F ⊗[F] E) := ⟨rfl⟩
  have : BorelSpace (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HermR (Ainf F) σ a) := ⟨rfl⟩
  have : ContinuousAdd (Fin a → Fin M → Ainf F ⊗[F] E) := ⟨by
    have e : (fun p : (Fin a → Fin M → Ainf F ⊗[F] E) × (Fin a → Fin M → Ainf F ⊗[F] E) =>
        p.1 + p.2) = fun p => eV.symm (eV p.1 + eV p.2) := by
      funext p; rw [← hV, Homeomorph.symm_apply_apply]
    rw [e]; fun_prop⟩
  have : ContinuousAdd (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HermR (Ainf F) σ a) := ⟨by
    have e : (fun p : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HermR (Ainf F) σ a × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HermR (Ainf F) σ a => p.1 + p.2) =
        fun p => eH.symm (eH p.1 + eH p.2) := by
      funext p; rw [← hH, Homeomorph.symm_apply_apply]
    rw [e]; fun_prop⟩
  have hμ' : (μ.map eV).IsAddHaarMeasure :=
    Measure.isAddHaarMeasure_map μ (AddMonoidHom.mk' eV hV) eV.continuous eV.surjective
      (eV.map_cocompact).le
  have hν' : (ν.map eH).IsAddHaarMeasure :=
    Measure.isAddHaarMeasure_map ν (AddMonoidHom.mk' eH hH) eH.continuous eH.surjective
      (eH.map_cocompact).le
  have hW' : IsOpen (eV.symm ⁻¹' W) := hW.preimage eV.symm.continuous
  have hx0W : eV x ∈ eV.symm ⁻¹' W := by
    show eV.symm (eV x) ∈ W
    rw [Homeomorph.symm_apply_apply]
    exact hxW
  obtain ⟨c, hc0, hct, N', hN', hlb'⟩ :=
    PI.VolStabS.submLB_holds n m _ _ hμ' hν' f' hf' (eV x) (hsurj x hx) _ hW' hx0W
  have hfx0 : f' (eV x) = eH S0 := by
    have h1 : eH.symm (f' (eV x)) = S0 := Subtype.ext ((hG x).trans hxS)
    rw [← h1, Homeomorph.apply_symm_apply]
  have hN : eH ⁻¹' N' ∈ 𝓝 S0 := eH.continuous.continuousAt.preimage_mem_nhds (hfx0 ▸ hN')
  refine ⟨c, hc0, hct, _, hN, fun S hSN hSm => ?_⟩
  have hS'm : MeasurableSet (eH.symm ⁻¹' S) := eH.symm.continuous.measurable hSm
  have hS'N : eH.symm ⁻¹' S ⊆ N' := fun z hz => by
    have := hSN hz
    rwa [mem_preimage, Homeomorph.apply_symm_apply] at this
  have h := hlb' _ hS'N hS'm
  rw [show (ν.map eH) = ν.map eH.toMeasurableEquiv from rfl,
    show (μ.map eV) = μ.map eV.toMeasurableEquiv from rfl,
    MeasurableEquiv.map_apply, MeasurableEquiv.map_apply] at h
  have e1 : eH.toMeasurableEquiv ⁻¹' (eH.symm ⁻¹' S) = S := by
    ext z
    simp
  have e2 : eV.toMeasurableEquiv ⁻¹' (f' ⁻¹' (eH.symm ⁻¹' S) ∩ eV.symm ⁻¹' W) =
      (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.gramR (Ainf F) σ J) ⁻¹' (Subtype.val '' S) ∩ W := by
    ext X
    simp only [mem_preimage, mem_inter_iff, Homeomorph.toMeasurableEquiv_coe,
      Homeomorph.symm_apply_apply, mem_image]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨⟨_, h1, hG X⟩, h2⟩
    · rintro ⟨⟨s, hs, hsX⟩, h2⟩
      refine ⟨?_, h2⟩
      have : s = eH.symm (f' (eV X)) := Subtype.ext (hsX.trans (hG X).symm)
      rw [← this]
      exact hs
  rw [e1, e2] at h
  exact h

end Arch

section Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Establish `hO` using `GlobalTheory.CompanionTheory.WeilSiegel.FreeOpen.isOpen_free F E σ hCM R hR n M`. Take `⟨h1, h2, h3, h4, -⟩` from `hR`. Take `⟨t1, t2, t3, t4, -, -, -, t8, -, -⟩` from `GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM R`. Use `haveI := t2`. Use `haveI := t3`.

Use `haveI := t4`. Use `haveI := t8 n M`. Conclude with `sigmaFinite_fib hm hO S`.
-/
theorem sigmaFinite_free (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R]
    (hR : IsLocR R) (n : ℕ) (μ : Measure (Fin n → Fin M → R ⊗[F] E)) (ν : Measure (HermR R σ n))
    (m : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)) (hm : IsGramFibFree R σ J n μ ν m)
    (S : HermR R σ n) : SigmaFinite (m S) := by
  have hO := GlobalTheory.CompanionTheory.WeilSiegel.FreeOpen.isOpen_free F E σ hCM R hR n M
  obtain ⟨h1, h2, h3, h4, -⟩ := hR
  obtain ⟨t1, t2, t3, t4, -, -, -, t8, -, -⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM R
  haveI := t2
  haveI := t3
  haveI := t4
  haveI := t8 n M
  exact sigmaFinite_fib hm hO S

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hCM M J hJ _ h₀ d b laminf lam hinf hlam minf hminf m hm`. Establish `hLi : IsLocR (Ainf F)` using `GlobalTheory.CompanionTheory.SW.isLocR_Ainf F hCM.1`. Establish `hLv : ∀ v, IsLocR (Fv F v)` using `GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F`. Use `haveI hBi : BorelSpace (Ainf F) := ⟨rfl⟩`. Use `haveI hBv : ∀ v, BorelSpace (Fv F v) := fun v => ⟨rfl⟩`.

Use `⟨sigmaFinite_free σ hCM J (Ainf F) hLi 1 _ _ minf hminf _, fun v => sigmaFinite_free σ hCM J (Fv F v) (hLv v) 1 _ _ (m v) (hm v) _, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨X₀, hX₀, hg⟩`. Establish `hgram : ∀ (R : Type) [CommRing R] [Algebra F R], gramR R σ J (ratTup (F` using `F) R X₀) = (hermOf R σ (0 : Matrix (Fin 1) (Fin 1) E) h₀ : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) := fun R _ _ => by`. Rewrite using `[gramR_ratTup_eq, hg]`. Both sides reduce to the same expression.

Prove the components needed by the constructor for the conclusion. Take `⟨h1, h2, h3, h4, hA, hRed, hU, -⟩` from `hLi haveI := h1 haveI := h2 haveI := h3 haveI := h4 haveI := hA haveI := hRed haveI : FiniteDimensional F E := Module.Finite.of_basis b`. Establish `hUo : IsOpen {r : Ainf F | IsUnit r}`. Use `hU.isOpen_range` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal.

Use extensionality with `r`. Simplify using `[IsUnit]`. Establish `hH` using `GlobalTheory.CompanionTheory.SW.coord_measures_haar F E σ hCM (Ainf F) d b laminf hinf.1`. Use `haveI := hH.2.1 1 M`. Set `ν' : Measure (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HermR (Ainf F) σ 1)` to `coordHerm (Ainf F) σ b laminf 1`.

Use `haveI : ν'.IsAddHaarMeasure := hH.2.2 1`. Conclude with `(GlobalTheory.LocalFibreNonzero.fib_tens σ (PI.VolStabS.sigma_invol σ hCM.2.2.2) J hJ.1 1 (Ainf F) hUo (GlobalTheory.CompanionTheory.WeilSiegel.FreeOpen.lip_of_artinian_reduced (Ainf F)) _ ν' minf hminf (ratTup (F := F) (Ainf F) X₀) _ (ratTup_free (Ainf F) X₀ hX₀) (fun W hW hxW = …`. Introduce `v`. Take `⟨h1, h2, h3, h4, -⟩` from `hLv v`. Use `haveI := h1`.

Use `haveI := h2`. Use `haveI := h3`. Use `haveI := h4`. Establish `hH` using `GlobalTheory.CompanionTheory.SW.coord_measures_haar F E σ hCM (Fv F v) d b (lam v) (hlam v).1`. Conclude with `(GlobalTheory.LocalFibreNonzero.fibre_nonzero_finite F E σ hCM M J hJ v 1 _ _ (hH.2.1 1 M) (hH.2.2 1) (m v) (hm v) (ratTup (F := F) (Fv F v) X₀) _ (ratTup_free (Fv F v) X₀ hX₀) (hgram (Fv F v))).1`.
-/
theorem free_fibre_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 3 ≤ M → ∀ (h₀ : ∀ a b : Fin 1, σ ((0 : Matrix (Fin 1) (Fin 1) E) b a) = (0 : Matrix (Fin 1) (Fin 1) E) a b), ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (laminf : Measure (Ainf F)) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), IsStdInf laminf → (∀ v, IsStdV v (lam v)) → ∀ (minf : HermR (Ainf F) σ 1 → Measure (Fin 1 → Fin M → Ainf F ⊗[F] E)), IsGramFibFree (Ainf F) σ J 1 (coordW (Ainf F) b laminf 1 M) (coordHerm (Ainf F) σ b laminf 1) minf → ∀ (m : ∀ v : HeightOneSpectrum (𝓞 F), HermR (Fv F v) σ 1 → Measure (Fin 1 → Fin M → Fv F v ⊗[F] E)), (∀ v, IsGramFibFree (Fv F v) σ J 1 (coordW (Fv F v) b (lam v) 1 M) (coordHerm (Fv F v) σ b (lam v) 1) (m v)) → SigmaFinite (minf (hermOf (Ainf F) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀)) ∧ (∀ v, SigmaFinite (m v (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀))) ∧ ((framesE σ J (0 : Matrix (Fin 1) (Fin 1) E)).Nonempty → minf (hermOf (Ainf F) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀) ≠ 0 ∧ ∀ v, m v (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀) ≠ 0) := by
  intro F E _ _ _ _ _ σ hCM M J hJ _ h₀ d b laminf lam hinf hlam minf hminf m hm
  have hLi : IsLocR (Ainf F) := GlobalTheory.CompanionTheory.SW.isLocR_Ainf F hCM.1
  have hLv : ∀ v, IsLocR (Fv F v) := GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F
  haveI hBi : BorelSpace (Ainf F) := ⟨rfl⟩
  haveI hBv : ∀ v, BorelSpace (Fv F v) := fun v => ⟨rfl⟩
  refine ⟨sigmaFinite_free σ hCM J (Ainf F) hLi 1 _ _ minf hminf _,
    fun v => sigmaFinite_free σ hCM J (Fv F v) (hLv v) 1 _ _ (m v) (hm v) _, ?_⟩
  rintro ⟨X₀, hX₀, hg⟩
  have hgram : ∀ (R : Type) [CommRing R] [Algebra F R],
      gramR R σ J (ratTup (F := F) R X₀) = (hermOf R σ (0 : Matrix (Fin 1) (Fin 1) E) h₀ :
        Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) := fun R _ _ => by
    rw [gramR_ratTup_eq, hg]
    rfl
  constructor
  · obtain ⟨h1, h2, h3, h4, hA, hRed, hU, -⟩ := hLi
    haveI := h1
    haveI := h2
    haveI := h3
    haveI := h4
    haveI := hA
    haveI := hRed
    haveI : FiniteDimensional F E := Module.Finite.of_basis b
    have hUo : IsOpen {r : Ainf F | IsUnit r} := by
      have := hU.isOpen_range
      convert this using 1
      ext r
      simp [IsUnit]
    have hH := GlobalTheory.CompanionTheory.SW.coord_measures_haar F E σ hCM (Ainf F) d b laminf hinf.1
    haveI := hH.2.1 1 M
    let ν' : Measure (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HermR (Ainf F) σ 1) := coordHerm (Ainf F) σ b laminf 1
    haveI : ν'.IsAddHaarMeasure := hH.2.2 1
    exact (GlobalTheory.LocalFibreNonzero.fib_tens σ (PI.VolStabS.sigma_invol σ hCM.2.2.2) J hJ.1 1 (Ainf F)
      hUo (GlobalTheory.CompanionTheory.WeilSiegel.FreeOpen.lip_of_artinian_reduced (Ainf F)) _ ν' minf hminf
      (ratTup (F := F) (Ainf F) X₀) _ (ratTup_free (Ainf F) X₀ hX₀)
      (fun W hW hxW => arch_lb F E σ hCM M 1 J hJ _ _ (hH.2.1 1 M) (hH.2.2 1) _ _
        (ratTup_free (Ainf F) X₀ hX₀) (hgram (Ainf F)) W hW hxW)).1
  · intro v
    obtain ⟨h1, h2, h3, h4, -⟩ := hLv v
    haveI := h1
    haveI := h2
    haveI := h3
    haveI := h4
    have hH := GlobalTheory.CompanionTheory.SW.coord_measures_haar F E σ hCM (Fv F v) d b (lam v) (hlam v).1
    exact (GlobalTheory.LocalFibreNonzero.fibre_nonzero_finite F E σ hCM M J hJ v 1 _ _ (hH.2.1 1 M) (hH.2.2 1)
      (m v) (hm v) (ratTup (F := F) (Fv F v) X₀) _ (ratTup_free (Fv F v) X₀ hX₀) (hgram (Fv F v))).1

end Main

end GlobalTheory.CompanionTheory.WeilSiegel.FreeLocal
