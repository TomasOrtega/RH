import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import GroundTheory.GlobalFields.TateThesis.AdeleScaling

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.ModuAdele

open scoped Pointwise

/- English proof (translation)
Use `letI : MeasurableSpace (AdeleRing (𝓞 K) K) := GroundTheory.Global.measurableSpace_adeleRing K`. Take `⟨s, hsc, hs0⟩ : ∃ s : Set (AdeleRing (𝓞 K) K), IsCompact s ∧ s ∈ nhds (0 : AdeleRing (𝓞 K) K)` from `exists_compact_mem_nhds 0`. Establish `hpos : 0 ≤ (GroundTheory.Global.IdeleGroup.ideleModule K a : ℝ)` using `(GroundTheory.Global.IdeleGroup.ideleModule K a).2.le`. Use `set r : NNReal := ⟨_, hpos⟩ with hr`. Use `set μ := GroundTheory.Global.adeleMeasure K with hμ`.

Use `set ν : Measure (AdeleRing (𝓞 K) K) := Measure.addHaar with hν`. Establish `e1` using `Measure.measure_isAddInvariant_eq_smul_of_isCompact_closure μ ν hsc.closure`. Establish `e2` using `Measure.measure_isAddInvariant_eq_smul_of_isCompact_closure μ ν (hsc.smul a).closure`. Establish `hm` using `GroundTheory.Global.adeleMeasure_smul a s`. Use `set c := μ.addHaarScalarFactor ν`.

Establish `hμs : μ s ≠ 0` using `(Measure.measure_pos_of_mem_nhds _ hs0).ne'`. Establish `hνs : ν s ≠ 0` using `(Measure.measure_pos_of_mem_nhds _ hs0).ne'`. Establish `hνs' : ν s ≠ ⊤` using `hsc.measure_lt_top.ne`. Establish `hc : (c : ENNReal) ≠ 0`. Introduce `h0`.

Apply `hμs` to reduce the goal to its premises. Rewrite using `[e1, ENNReal.smul_def, smul_eq_mul, h0, zero_mul]`. Establish `h` using `distribHaarChar_eq_of_measure_smul_eq_mul (g := a) (μ := ν) (s := s) hνs hνs' (r := r) (by`. Rewrite `hm` using `[e1, e2, ENNReal.smul_def, ENNReal.smul_def, smul_eq_mul, smul_eq_mul, ENNReal.ofReal_eq_coe_nnreal hpos]`. Establish `hm' : (c : ENNReal) * ν (a • s) = (c : ENNReal) * ((r : ENNReal) * ν s)`.

Combine the equalities or inequalities in the displayed calculation. Conclude with `(ENNReal.mul_right_inj hc ENNReal.coe_ne_top).1 hm')`. Rewrite using `[h]`. Both sides reduce to the same expression.
-/
theorem distribHaarChar_adeleRing (K : Type) [Field K] [NumberField K] (a : (AdeleRing (𝓞 K) K)ˣ) :
    (distribHaarChar (AdeleRing (𝓞 K) K) a : ℝ) = (GroundTheory.Global.IdeleGroup.ideleModule K a : ℝ) := by
  letI : MeasurableSpace (AdeleRing (𝓞 K) K) := GroundTheory.Global.measurableSpace_adeleRing K
  obtain ⟨s, hsc, hs0⟩ : ∃ s : Set (AdeleRing (𝓞 K) K), IsCompact s ∧ s ∈ nhds (0 : AdeleRing (𝓞 K) K) :=
    exists_compact_mem_nhds 0
  have hpos : 0 ≤ (GroundTheory.Global.IdeleGroup.ideleModule K a : ℝ) := (GroundTheory.Global.IdeleGroup.ideleModule K a).2.le
  set r : NNReal := ⟨_, hpos⟩ with hr
  set μ := GroundTheory.Global.adeleMeasure K with hμ
  set ν : Measure (AdeleRing (𝓞 K) K) := Measure.addHaar with hν
  have e1 := Measure.measure_isAddInvariant_eq_smul_of_isCompact_closure μ ν hsc.closure
  have e2 := Measure.measure_isAddInvariant_eq_smul_of_isCompact_closure μ ν (hsc.smul a).closure
  have hm := GroundTheory.Global.adeleMeasure_smul a s
  set c := μ.addHaarScalarFactor ν
  have hμs : μ s ≠ 0 := (Measure.measure_pos_of_mem_nhds _ hs0).ne'
  have hνs : ν s ≠ 0 := (Measure.measure_pos_of_mem_nhds _ hs0).ne'
  have hνs' : ν s ≠ ⊤ := hsc.measure_lt_top.ne
  have hc : (c : ENNReal) ≠ 0 := by
    intro h0
    apply hμs
    rw [e1, ENNReal.smul_def, smul_eq_mul, h0, zero_mul]
  have h := distribHaarChar_eq_of_measure_smul_eq_mul (g := a) (μ := ν) (s := s) hνs hνs'
    (r := r) (by
      rw [e1, e2, ENNReal.smul_def, ENNReal.smul_def, smul_eq_mul, smul_eq_mul,
        ENNReal.ofReal_eq_coe_nnreal hpos] at hm
      have hm' : (c : ENNReal) * ν (a • s) = (c : ENNReal) * ((r : ENNReal) * ν s) := by
        calc (c : ENNReal) * ν (a • s) = (r : ENNReal) * ((c : ENNReal) * ν s) := hm
          _ = (c : ENNReal) * ((r : ENNReal) * ν s) := by ring
      exact (ENNReal.mul_right_inj hc ENNReal.coe_ne_top).1 hm')
  rw [h]
  rfl

end GlobalTheory.ModuAdele

/- English proof (translation)
Introduce `F E _ _ _ _ _ x`. Establish `hf : (Function.mulSupport fun v : HeightOneSpectrum (𝓞 F) => ‖evFin F v (Algebra.norm (AF F) x.1)‖₊).Finite`. Simplify `GlobalTheory.Doubling.finite_mulSupport_absEv x` using `only [GlobalTheory.Doubling.absEv_unitFin]`. Apply `NNReal.eq` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `(distribHaarChar (AdeleRing (𝓞 F) F) (Units.map (Algebra.norm (AF F) : AE F E →* AF F) x) : ℝ) = _`.

Rewrite using `[GlobalTheory.ModuAdele.distribHaarChar_adeleRing, GroundTheory.Global.IdeleGroup.ideleModule_eq, GlobalTheory.Doubling.absE_apply]`. Simplify using `only [GlobalTheory.Doubling.absEv_unitFin, GlobalTheory.Doubling.absEw_unitInf]`. Rewrite using `[NNReal.coe_mul, NNReal.coe_prod]`. Use `congr 1`. Rewrite using `[show ((∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖evFin F v (Algebra.norm (AF F) x.1)‖₊ : ℝ≥0) : ℝ) = ∏ᶠ v : HeightOneSpectrum (𝓞 F), ((‖evFin F v (Algebra.norm (AF F) x.1)‖₊ : ℝ≥0) : ℝ) from NNReal.toRealHom.toMonoidHom.map_finprod hf]`.

Both sides reduce to the same expression.
-/
theorem GlobalTheory.ModuAdele.modu_norm_eq_absE : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (x : (AE F E)ˣ),
    (adeleClass F).modu (Units.map (Algebra.norm (AF F) : AE F E →* AF F) x) = absE F E x := by
  intro F E _ _ _ _ _ x
  have hf : (Function.mulSupport fun v : HeightOneSpectrum (𝓞 F) =>
      ‖evFin F v (Algebra.norm (AF F) x.1)‖₊).Finite := by
    simpa only [GlobalTheory.Doubling.absEv_unitFin] using GlobalTheory.Doubling.finite_mulSupport_absEv x
  apply NNReal.eq
  change (distribHaarChar (AdeleRing (𝓞 F) F) (Units.map (Algebra.norm (AF F) : AE F E →* AF F) x) : ℝ) = _
  rw [GlobalTheory.ModuAdele.distribHaarChar_adeleRing, GroundTheory.Global.IdeleGroup.ideleModule_eq, GlobalTheory.Doubling.absE_apply]
  simp only [GlobalTheory.Doubling.absEv_unitFin, GlobalTheory.Doubling.absEw_unitInf]
  rw [NNReal.coe_mul, NNReal.coe_prod]
  congr 1
  rw [show ((∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖evFin F v (Algebra.norm (AF F) x.1)‖₊ : ℝ≥0) : ℝ) =
      ∏ᶠ v : HeightOneSpectrum (𝓞 F), ((‖evFin F v (Algebra.norm (AF F) x.1)‖₊ : ℝ≥0) : ℝ) from
      NNReal.toRealHom.toMonoidHom.map_finprod hf]
  rfl
