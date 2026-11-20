import Mathlib
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.ThickFrames
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.SplitLoc
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.SphIso
import GroundTheory.AutomorphicForms.CompactFormulaCountable

open MeasureTheory NumberField IsDedekindDomain ValuativeRel
open GroundTheory.Automorphic GroundTheory.Automorphic.Spherical GroundTheory.Global GroundTheory.Global.SemiLocal PositivityTheory.Rg.Tf.Geo

namespace UpperTheory.ConvolutionTheory.L1

/- English proof (translation)
Establish `e` using `Measure.isMulLeftInvariant_eq_smul m m'`. Establish `e2 : m K = (Measure.haarScalarFactor m m' • m') K` using `by rw [← e]`. Rewrite `e2` using `[h, Measure.smul_apply, h', ENNReal.smul_def, smul_eq_mul, mul_one]`. Establish `e3 : Measure.haarScalarFactor m m' = 1` using `by exact_mod_cast e2.symm`. Rewrite `e` using `[e3, one_smul]`.

Conclude with `e`.
-/
private theorem haar_uniq {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] {K : Set G} {m m' : Measure G}
    (hm : m.IsHaarMeasure) (hm' : m'.IsHaarMeasure) (h : m K = 1) (h' : m' K = 1) : m = m' := by
  have e := Measure.isMulLeftInvariant_eq_smul m m'
  have e2 : m K = (Measure.haarScalarFactor m m' • m') K := by rw [← e]
  rw [h, Measure.smul_apply, h', ENNReal.smul_def, smul_eq_mul, mul_one] at e2
  have e3 : Measure.haarScalarFactor m m' = 1 := by exact_mod_cast e2.symm
  rw [e3, one_smul] at e
  exact e

/- English proof (translation)
Use `haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) R) := inferInstanceAs (SecondCountableTopology (Fin n → Fin n → R))`. Use `haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) R)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology`. Conclude with `Units.isEmbedding_embedProduct.secondCountableTopology`.
-/
private theorem gl_sc (R : Type*) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [SecondCountableTopology R] (n : ℕ) : SecondCountableTopology (GL (Fin n) R) := by
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) R) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → R))
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) R)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

variable {K : Type} [Field K] [NumberField K] {n : ℕ} {v : HeightOneSpectrum (𝓞 K)}

/- English proof (translation)
Take `⟨ms', bs', m', hm', h1', H, hH, S⟩` from `hs`. Take `rfl : ms' = ms` from `bs'.measurable_eq.trans bs.measurable_eq.symm`. Use `haveI := gl_sc (v.adicCompletion K) n`. Take `rfl` from `haar_uniq hm hm' h1 h1'`. Conclude with `⟨H, hH, S⟩`.
-/
private theorem sph_at [ms : MeasurableSpace (GL (Fin n) (v.adicCompletion K))]
    [bs : BorelSpace (GL (Fin n) (v.adicCompletion K))] (m : Measure (GL (Fin n) (v.adicCompletion K)))
    (hm : m.IsHaarMeasure) (h1 : m (GLnLocal.integralGL (v.adicCompletion K) n) = 1)
    {p : MvPolynomial (Fin n) ℂ} {h : GL (Fin n) (v.adicCompletion K) → ℂ} (hs : GM.IsSph v p h) :
    ∃ H : SphericalHecke m (F := v.adicCompletion K) (n := n), (∀ x, (H : HeckeAlgebra m) x = h x) ∧
      satakeTransform m H = polyEmb n (MvPolynomial.aeval (fun i : Fin n => MvPolynomial.esymm (Fin n) ℂ (i + 1)) p) := by
  obtain ⟨ms', bs', m', hm', h1', H, hH, S⟩ := hs
  obtain rfl : ms' = ms := bs'.measurable_eq.trans bs.measurable_eq.symm
  haveI := gl_sc (v.adicCompletion K) n
  obtain rfl := haar_uniq hm hm' h1 h1'
  exact ⟨H, hH, S⟩

end UpperTheory.ConvolutionTheory.L1

open UpperTheory.ConvolutionTheory.L1

/- English proof (translation)
Use `⟨?_, fun K _ _ n v => ⟨?_, ?_, ?_⟩⟩` and prove the remaining obligations. Introduce `F E _ _ _ _ _ v w hs n p h hsph`. Take `⟨ms, bs, m, hm, hk, H, hH, S⟩` from `hsph`. Take `⟨⟨e, he⟩, hint, -, -, -⟩` from `UpperTheory.ConvolutionTheory.L1.splitLoc F E v w hs n`. Set `c : v.adicCompletion F ≃+* w.1.adicCompletion E` to `RingEquiv.ofBijective (completionMap v w.1) ⟨(completionMap v w.1).injective, hs⟩`.

Establish `he0 : w.1.asIdeal.ramificationIdx (𝓞 F) ≠ 0` using `(Ideal.ramificationIdx_pos w.1.asIdeal (𝓞 F)).ne'`. Establish `hv : ∀ x, c x ∈ 𝒪[w.1.adicCompletion E] ↔ x ∈ 𝒪[v.adicCompletion F]` using `fun x => by`. Establish `h1 : ∀ y : w.1.adicCompletion E, y ∈ 𝒪[w.1.adicCompletion E] ↔ Valued.v y ≤ 1` using `fun y => by`. Use `ValuativeRel.isEquiv (valuation (w.1.adicCompletion E)) Valued.v y 1` as an intermediate fact. Rewrite `this` using `[map_one, map_one]`.

Conclude with `(Valuation.mem_integer_iff _ _).trans this`. Establish `h2 : ∀ y : v.adicCompletion F, y ∈ 𝒪[v.adicCompletion F] ↔ Valued.v y ≤ 1` using `fun y => by`. Use `ValuativeRel.isEquiv (valuation (v.adicCompletion F)) Valued.v y 1` as an intermediate fact. Rewrite `this` using `[map_one, map_one]`. Conclude with `(Valuation.mem_integer_iff _ _).trans this`.

Rewrite using `[h1, h2]`. Express the relevant statement in the definitionally equal form `Valued.v (completionMap v w.1 x) ≤ 1 ↔ _`. Rewrite using `[valued_completionMap]`. Conclude with `pow_le_one_iff_of_nonneg zero_le he0`. Establish `hee : ∀ g, e g = mapIso c n g` using `fun g => he g`.

Take `⟨ms', bs', m', hm', h1, H', hH', S'⟩` from `exists_transport e (fun g => by rw [he]; exact hint g) (fun g => by rw [hee]; exact iwasawaExponent_mapIso c hv g) (qF_eq_of_iso c hv) hk H`. Conclude with `⟨ms', bs', m', hm', h1, H', fun x => (hH' x).trans ((hH _).trans (by rw [he])), S'.trans S⟩`. Introduce and unpack `p h ⟨_, _, m, _, -, H, hH, -⟩`. Take `rfl : (fun x => (H : HeckeAlgebra m) x) = h` from `funext hH`. Conclude with `⟨(H : HeckeAlgebra m).mem.1.continuous, (H : HeckeAlgebra m).mem.2⟩`.

Introduce `p h h' hs hs'`. Take `⟨ms, bs, m, hm, h1, H, hH, S⟩` from `id hs`. Take `⟨H', hH', S'⟩` from `sph_at m hm h1 hs'`. Take `rfl` from `satakeTransform_injective (S.trans S'.symm)`. Conclude with `funext fun x => (hH x).symm.trans (hH' x)`.

Introduce `_ _ m hm h1 p p' h h' hs hs'`. Take `⟨H, hH, S⟩` from `sph_at m hm h1 hs`. Take `⟨H', hH', S'⟩` from `sph_at m hm h1 hs'`. Use `⟨_, inferInstance, m, hm, h1, H * H', fun x => ?_, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `∫ y, (H : HeckeAlgebra m) y * (H' : HeckeAlgebra m) (y⁻¹ * x) ∂m = _`.

Simplify using `only [hH, hH']`. Both sides reduce to the same expression. Rewrite using `[map_mul, S, S', map_mul, map_mul]`.
-/
theorem UpperTheory.ConvolutionTheory.L1.sphLaws :
    UpperTheory.ConvolutionTheory.L1.SphLaws := by
  refine ⟨?_, fun K _ _ n v => ⟨?_, ?_, ?_⟩⟩
  · intro F E _ _ _ _ _ v w hs n p h hsph
    obtain ⟨ms, bs, m, hm, hk, H, hH, S⟩ := hsph
    obtain ⟨⟨e, he⟩, hint, -, -, -⟩ := UpperTheory.ConvolutionTheory.L1.splitLoc F E v w hs n
    let c : v.adicCompletion F ≃+* w.1.adicCompletion E :=
      RingEquiv.ofBijective (completionMap v w.1) ⟨(completionMap v w.1).injective, hs⟩
    have he0 : w.1.asIdeal.ramificationIdx (𝓞 F) ≠ 0 := (Ideal.ramificationIdx_pos w.1.asIdeal (𝓞 F)).ne'
    have hv : ∀ x, c x ∈ 𝒪[w.1.adicCompletion E] ↔ x ∈ 𝒪[v.adicCompletion F] := fun x => by
      have h1 : ∀ y : w.1.adicCompletion E, y ∈ 𝒪[w.1.adicCompletion E] ↔ Valued.v y ≤ 1 := fun y => by
        have := ValuativeRel.isEquiv (valuation (w.1.adicCompletion E)) Valued.v y 1
        rw [map_one, map_one] at this
        exact (Valuation.mem_integer_iff _ _).trans this
      have h2 : ∀ y : v.adicCompletion F, y ∈ 𝒪[v.adicCompletion F] ↔ Valued.v y ≤ 1 := fun y => by
        have := ValuativeRel.isEquiv (valuation (v.adicCompletion F)) Valued.v y 1
        rw [map_one, map_one] at this
        exact (Valuation.mem_integer_iff _ _).trans this
      rw [h1, h2]
      change Valued.v (completionMap v w.1 x) ≤ 1 ↔ _
      rw [valued_completionMap]
      exact pow_le_one_iff_of_nonneg zero_le he0
    have hee : ∀ g, e g = mapIso c n g := fun g => he g
    obtain ⟨ms', bs', m', hm', h1, H', hH', S'⟩ := exists_transport e (fun g => by rw [he]; exact hint g)
      (fun g => by rw [hee]; exact iwasawaExponent_mapIso c hv g) (qF_eq_of_iso c hv) hk H
    exact ⟨ms', bs', m', hm', h1, H', fun x => (hH' x).trans ((hH _).trans (by rw [he])), S'.trans S⟩
  · rintro p h ⟨_, _, m, _, -, H, hH, -⟩
    obtain rfl : (fun x => (H : HeckeAlgebra m) x) = h := funext hH
    exact ⟨(H : HeckeAlgebra m).mem.1.continuous, (H : HeckeAlgebra m).mem.2⟩
  · intro p h h' hs hs'
    obtain ⟨ms, bs, m, hm, h1, H, hH, S⟩ := id hs
    obtain ⟨H', hH', S'⟩ := sph_at m hm h1 hs'
    obtain rfl := satakeTransform_injective (S.trans S'.symm)
    exact funext fun x => (hH x).symm.trans (hH' x)
  · intro _ _ m hm h1 p p' h h' hs hs'
    obtain ⟨H, hH, S⟩ := sph_at m hm h1 hs
    obtain ⟨H', hH', S'⟩ := sph_at m hm h1 hs'
    refine ⟨_, inferInstance, m, hm, h1, H * H', fun x => ?_, ?_⟩
    · change ∫ y, (H : HeckeAlgebra m) y * (H' : HeckeAlgebra m) (y⁻¹ * x) ∂m = _
      simp only [hH, hH']
      rfl
    · rw [map_mul, S, S', map_mul, map_mul]
