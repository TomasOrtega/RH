import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SpanRhoTEqTop
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PiEqOfFinPart
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilDatumAtPlaceEqLatticeIntertwinerMulDetChar
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.InertFrameLoc

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.InertFrameLoc

section Rigid

variable {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))

/- English proof (translation)
Take `⟨a, ha, ha0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot w.ne_bot`. Use `set t : w.adicCompletion E := algebraMap E _ (a : E) with ht`. Establish `hft : f t = t` using `h1 _`. Establish `ht1 : Valued.v t < 1`. Rewrite using `[ht, GlobalTheory.Idele.valued_algebraMap]`.

Conclude with `(HeightOneSpectrum.valuation_lt_one_iff_mem w a).2 ha`. Establish `htz : t ≠ 0`. Rewrite using `[ht, map_ne_zero, Ne, RingOfIntegers.coe_eq_zero_iff]`. Conclude with `ha0`. Establish `key : ∀ (n : ℕ) z, Valued.v z ≤ Valued.v t ^ n → Valued.v (f z) ≤ Valued.v t ^ n`.

Introduce `n z hz`. Establish `htn : t ^ n ≠ 0` using `pow_ne_zero _ htz`. Establish `hz' : z = t ^ n * (z / t ^ n)` using `by field_simp`. Rewrite using `[hz', map_mul, map_pow, hft, Valuation.map_mul, Valuation.map_pow]`. Use `mul_le_of_le_one_right' (h2 _ ?_)` and prove the remaining obligations.

Rewrite using `[map_div₀, map_pow]`. Conclude with `div_le_one_of_le₀ hz zero_le'`. Establish `hcont : Continuous f`. Use `continuous_of_continuousAt_zero f (Metric.tendsto_nhds.2 fun ε hε => ?_)` and prove the remaining obligations. Establish `h1' : ‖t‖ < 1` using `Valued.toNormedField.norm_lt_one_iff.2 ht1`.

Take `⟨m, hm⟩` from `exists_pow_lt_of_lt_one hε h1'`. Establish `hne : Valued.v t ^ m ≠ 0` using `pow_ne_zero _ ((map_ne_zero _).2 htz)`. Use `filter_upwards [(GlobalTheory.Idele.isOpen_valued_le (K := E) w (WithZero.log (Valued.v t ^ m))).mem_nhds (x := 0) (by simp)] with z hz`. Rewrite using `[map_zero, dist_zero_right]`. Use `(Valued.toNormedField.norm_le_iff.2 ?_).trans_lt ((norm_pow t m).trans_lt hm)` and prove the remaining obligations.

Rewrite using `[map_pow]`. Use `key m z ?_` and prove the remaining obligations. Establish `hz' : Valued.v z ≤ WithZero.exp (WithZero.log (Valued.v t ^ m))` using `hz`. Rewrite `hz'` using `[WithZero.exp_log hne]`. Then use the resulting hypothesis. Conclude with `RingHom.coe_inj ((HeightOneSpectrum.denseRange_algebraMap E w).equalizer hcont continuous_id (funext fun x => h1 x))`.
-/
theorem ringHom_eq_id_of_int (f : w.adicCompletion E →+* w.adicCompletion E)
    (h1 : ∀ x : E, f (algebraMap E _ x) = algebraMap E _ x)
    (h2 : ∀ z, Valued.v z ≤ 1 → Valued.v (f z) ≤ 1) : f = RingHom.id _ := by
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot w.ne_bot
  set t : w.adicCompletion E := algebraMap E _ (a : E) with ht
  have hft : f t = t := h1 _
  have ht1 : Valued.v t < 1 := by
    rw [ht, GlobalTheory.Idele.valued_algebraMap]
    exact (HeightOneSpectrum.valuation_lt_one_iff_mem w a).2 ha
  have htz : t ≠ 0 := by
    rw [ht, map_ne_zero, Ne, RingOfIntegers.coe_eq_zero_iff]
    exact ha0
  have key : ∀ (n : ℕ) z, Valued.v z ≤ Valued.v t ^ n → Valued.v (f z) ≤ Valued.v t ^ n := by
    intro n z hz
    have htn : t ^ n ≠ 0 := pow_ne_zero _ htz
    have hz' : z = t ^ n * (z / t ^ n) := by field_simp
    rw [hz', map_mul, map_pow, hft, Valuation.map_mul, Valuation.map_pow]
    refine mul_le_of_le_one_right' (h2 _ ?_)
    rw [map_div₀, map_pow]
    exact div_le_one_of_le₀ hz zero_le'
  have hcont : Continuous f := by
    refine continuous_of_continuousAt_zero f (Metric.tendsto_nhds.2 fun ε hε => ?_)
    have h1' : ‖t‖ < 1 := Valued.toNormedField.norm_lt_one_iff.2 ht1
    obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hε h1'
    have hne : Valued.v t ^ m ≠ 0 := pow_ne_zero _ ((map_ne_zero _).2 htz)
    filter_upwards [(GlobalTheory.Idele.isOpen_valued_le (K := E) w (WithZero.log (Valued.v t ^ m))).mem_nhds
      (x := 0) (by simp)] with z hz
    rw [map_zero, dist_zero_right]
    refine (Valued.toNormedField.norm_le_iff.2 ?_).trans_lt ((norm_pow t m).trans_lt hm)
    rw [map_pow]
    refine key m z ?_
    have hz' : Valued.v z ≤ WithZero.exp (WithZero.log (Valued.v t ^ m)) := hz
    rwa [WithZero.exp_log hne] at hz'
  exact RingHom.coe_inj ((HeightOneSpectrum.denseRange_algebraMap E w).equalizer hcont continuous_id
    (funext fun x => h1 x))

end Rigid

end GlobalTheory.InertFrameLoc

namespace GlobalTheory.InertFrameLoc

section Cond

open GlobalTheory.EmbChart

variable {D : D7} {v : HeightOneSpectrum (𝓞 D.host.F)} {w : HeightOneSpectrum (𝓞 D.host.E)}

/- English proof (translation)
Rewrite using `[tensAt_mul_right, compFin_tensAt]`.
-/
theorem tensAt_mul_tensAt (y y' : Fv D.host.F v ⊗[D.host.F] D.host.E) :
    tensAt D.host.E v y * tensAt D.host.E v y' = tensAt D.host.E v (y * y') := by
  rw [tensAt_mul_right, compFin_tensAt]

/- English proof (translation)
Use `show evFin D.host.F v 1 ⊗ₜ x = _`. Rewrite using `[map_one]`.
-/
theorem compFin_incA (x : D.host.E) :
    compFin D.host.F D.host.E v (incA D x) = (1 : Fv D.host.F v) ⊗ₜ[D.host.F] x := by
  show evFin D.host.F v 1 ⊗ₜ x = _
  rw [map_one]

/- English proof (translation)
Rewrite using `[tensAt_mul_right, one_mul, compFin_incA]`.
-/
theorem tensAt_one_mul_incA (x : D.host.E) :
    tensAt D.host.E v 1 * incA D x = tensAt D.host.E v ((1 : Fv D.host.F v) ⊗ₜ[D.host.F] x) := by
  rw [tensAt_mul_right, one_mul, compFin_incA]

/- English proof (translation)
Use `show tensAt D.host.E v ((GlobalTheory.LFun.InertChart.complEquiv hw h).symm (z * z')) = tensAt D.host.E v ((GlobalTheory.LFun.InertChart.complEquiv hw h).symm z) * tensAt D.host.E v ((GlobalTheory.LFun.InertChart.complEquiv hw h).symm z')`. Rewrite using `[map_mul, tensAt_mul_tensAt]`.
-/
theorem secW_mul (hw : IsInertAt D.host.F D.host.E v w) (h : w.under (𝓞 D.host.F) = v)
    (z z' : w.adicCompletion D.host.E) : secW hw h (z * z') = secW hw h z * secW hw h z' := by
  show tensAt D.host.E v ((GlobalTheory.LFun.InertChart.complEquiv hw h).symm (z * z')) =
    tensAt D.host.E v ((GlobalTheory.LFun.InertChart.complEquiv hw h).symm z) *
      tensAt D.host.E v ((GlobalTheory.LFun.InertChart.complEquiv hw h).symm z')
  rw [map_mul, tensAt_mul_tensAt]

/- English proof (translation)
Rewrite using `[RingEquiv.symm_apply_eq]`. Use `show _ = GlobalTheory.LFun.toCompl h ((1 : Fv D.host.F v) ⊗ₜ[D.host.F] x)`. Rewrite using `[GlobalTheory.LFun.toCompl_tmul, map_one, one_mul]`.
-/
theorem complEquiv_symm_algebraMap (hw : IsInertAt D.host.F D.host.E v w) (h : w.under (𝓞 D.host.F) = v)
    (x : D.host.E) : (GlobalTheory.LFun.InertChart.complEquiv hw h).symm (algebraMap D.host.E _ x) =
      (1 : Fv D.host.F v) ⊗ₜ[D.host.F] x := by
  rw [RingEquiv.symm_apply_eq]
  show _ = GlobalTheory.LFun.toCompl h ((1 : Fv D.host.F v) ⊗ₜ[D.host.F] x)
  rw [GlobalTheory.LFun.toCompl_tmul, map_one, one_mul]

/- English proof (translation)
Use `Or.inr ⟨rfl, ⟨v, atPlace v 1, ⟨GlobalTheory.AdelicU.singleFin v 1, rfl, GlobalTheory.AdelicU.evalV_singleFin_self v 1, fun u hu => GlobalTheory.AdelicU.evalV_singleFin_ne hu 1⟩, rfl⟩, fun x hx => ?_⟩` and prove the remaining obligations. Rewrite using `[tensAt_one_mul_incA, finPart_tensAt_mem_iff, GlobalTheory.LFun.InertChart.mem_intLoc_iff hw h, GlobalTheory.LFun.toCompl_tmul, map_one, one_mul]`. Use `show _ ↔ ¬ (Valued.v (algebraMap D.host.E (w.adicCompletion D.host.E) (x : D.host.E)⁻¹) ≤ 1)`. Establish `h0 : w.valuation D.host.E (x : D.host.E) ≠ 0` using `(map_ne_zero _).2 (RingOfIntegers.coe_ne_zero_iff.2 hx)`. Rewrite using `[GlobalTheory.Idele.valued_algebraMap, map_inv₀, not_le, one_lt_inv₀ (zero_lt_iff.2 h0), HeightOneSpectrum.valuation_lt_one_iff_mem]`.
-/
theorem isPrimeIdem_tensAt (hw : IsInertAt D.host.F D.host.E v w) (h : w.under (𝓞 D.host.F) = v) :
    IsPrimeIdem w (tensAt D.host.E v 1) (tensAt D.host.E v 1) := by
  refine Or.inr ⟨rfl, ⟨v, atPlace v 1, ⟨GlobalTheory.AdelicU.singleFin v 1, rfl, GlobalTheory.AdelicU.evalV_singleFin_self v 1,
    fun u hu => GlobalTheory.AdelicU.evalV_singleFin_ne hu 1⟩, rfl⟩, fun x hx => ?_⟩
  rw [tensAt_one_mul_incA, finPart_tensAt_mem_iff, GlobalTheory.LFun.InertChart.mem_intLoc_iff hw h, GlobalTheory.LFun.toCompl_tmul,
    map_one, one_mul]
  show _ ↔ ¬ (Valued.v (algebraMap D.host.E (w.adicCompletion D.host.E) (x : D.host.E)⁻¹) ≤ 1)
  have h0 : w.valuation D.host.E (x : D.host.E) ≠ 0 := (map_ne_zero _).2 (RingOfIntegers.coe_ne_zero_iff.2 hx)
  rw [GlobalTheory.Idele.valued_algebraMap, map_inv₀, not_le, one_lt_inv₀ (zero_lt_iff.2 h0),
    HeightOneSpectrum.valuation_lt_one_iff_mem]

end Cond

/- English proof (translation)
Introduce `D ψ v w hw h c ϖ k hψ hconj hU hk z`. Establish `he` using `isPrimeIdem_tensAt (D := D) hw h`. Take `⟨ϖ0, σ0, q0, π0, hU0, -, hch, hV⟩` from `GlobalTheory.InertLoc.exists_chart (GlobalTheory.WeilAtPlace.conjPl_eq_of_inert hw h) he`. Establish `hsec_e : ∀ y, GlobalTheory.EmbChart.tensAt D.host.E v 1 * secW hw h y = secW hw h y` using `fun y => by show GlobalTheory.EmbChart.tensAt D.host.E v 1 * GlobalTheory.EmbChart.tensAt D.host.E v _ = GlobalTheory.EmbChart.tensAt D.host.E v _`. Rewrite using `[tensAt_mul_tensAt, one_mul]`.

Set `f0 : w.adicCompletion D.host.E →+* w.adicCompletion D.host.E` to `{ toFun := fun z => π0 (secW hw h z) map_one' := by show π0 (GlobalTheory.EmbChart.tensAt D.host.E v ((GlobalTheory.LFun.InertChart.complEquiv hw h).symm 1)) = 1`. Rewrite using `[map_one]`. Conclude with `hch.pi_idem`. Use the proof step `map_mul' := fun z z' => by show π0 (secW hw h (z * z')) = π0 (secW hw h z) * π0 (secW hw h z')`. Rewrite using `[secW_mul, map_mul]`.

Use the proof step `map_zero' := by show π0 (secW hw h 0) = 0`. Rewrite using `[map_zero, map_zero]`. Use the proof step `map_add' := fun z z' => by show π0 (secW hw h (z + z')) = π0 (secW hw h z) + π0 (secW hw h z')`. Rewrite using `[map_add, map_add] }`. Establish `hf0 : f0 = RingHom.id _` using `ringHom_eq_id_of_int w f0 (fun x => by show π0 (GlobalTheory.EmbChart.tensAt D.host.E v ((GlobalTheory.LFun.InertChart.complEquiv hw h).symm (algebraMap D.host.E _ x))) = _`.

Rewrite using `[complEquiv_symm_algebraMap, ← tensAt_one_mul_incA, map_mul, hch.pi_idem, one_mul, hch.2.2.2.1])`. Use the proof step `(fun z hz => by`. Use `(hch.2.2.2.2.2 (secW hw h z)).1 ?_` and prove the remaining obligations. Rewrite using `[hsec_e]`. Use `show finPart D (GlobalTheory.EmbChart.tensAt D.host.E v ((GlobalTheory.LFun.InertChart.complEquiv hw h).symm z)) ∈ intAE D`.

Rewrite using `[GlobalTheory.EmbChart.finPart_tensAt_mem_iff, GlobalTheory.LFun.InertChart.mem_intLoc_iff hw h]`. Use `show (GlobalTheory.LFun.InertChart.complEquiv hw h) ((GlobalTheory.LFun.InertChart.complEquiv hw h).symm z) ∈ Ov D.host.E w`. Rewrite using `[RingEquiv.apply_symm_apply]`. Conclude with `hz)`. Establish `hpi : ∀ z, π0 (secW hw h z) = z` using `fun z => RingHom.congr_fun hf0 z`.

Establish `hsec : ∀ z, hch.sec z = secW hw h z` using `fun z => hch.ext (hch.mul_sec z) (hsec_e z) (by rw [hch.pi_sec, hpi])`. Establish `hσc : ∀ x : D.host.E, σ0 (algebraMap D.host.E _ x) = c (algebraMap D.host.E _ x)` using `fun x => by`. Combine the equalities or inequalities in the displayed calculation. Establish `hg` using `ringHom_eq_id_of_int w (c.comp σ0) (fun x => by`. Rewrite using `[RingHom.comp_apply, hσc, hU.1])`.

Use the proof step `(fun z hz => by`. Rewrite using `[RingHom.comp_apply, hU.2.1, hU0.2.1]`. Conclude with `hz)`. Establish `hσ : ∀ z, σ0 z = c z` using `fun z => by`. Establish `h1 : c (σ0 z) = z` using `RingHom.congr_fun hg z`.

Combine the equalities or inequalities in the displayed calculation. Establish `hth : ∀ z, GlobalTheory.InertLoc.th ψ hch k z = thW ψ hw h (k * c k) z` using `fun z => by`. Rewrite using `[GlobalTheory.InertLoc.th_apply, thW_apply, hσ, hsec]`. Take `⟨β, -, hβ, -⟩` from `hV D.sp.X'`. Establish `hi : 0 < D.sp.X'.rank`.

Establish `h1` using `D.R.m_add_three_le_k`. Rewrite using `[D.sp.X'_rank, Formalism.BasicNotions.Ranks.rankX', Formalism.BasicNotions.Ranks.r]`. Use linear arithmetic over natural numbers and integers. Use `GlobalTheory.InertLoc.th_cond hψ hch hU0.2.1 hβ ⟨0, hi⟩ hk z` as an intermediate fact. Simplify `this` using `only [hth]`.
-/
theorem thW_cond : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : IsInertAt D.host.F D.host.E v w) (h : w.under (𝓞 D.host.F) = v) (c : w.adicCompletion D.host.E →+* w.adicCompletion D.host.E) (ϖ : w.adicCompletion D.host.E) (k : w.adicCompletion D.host.E), IsStdChar D ψ (-1) → IsConjAt D.sp.cm.sig h c → IsUnramInv ϖ c (qV D.host.F v) → GlobalTheory.InertLoc.IsGen D w k → ∀ z, (∀ u ∈ Formalism.UG.intL (w.adicCompletion D.host.E), thW ψ hw h (k * c k) (z * u) = 1) ↔ z ∈ Formalism.UG.intL (w.adicCompletion D.host.E) := by
  intro D ψ v w hw h c ϖ k hψ hconj hU hk z
  have he := isPrimeIdem_tensAt (D := D) hw h
  obtain ⟨ϖ0, σ0, q0, π0, hU0, -, hch, hV⟩ := GlobalTheory.InertLoc.exists_chart (GlobalTheory.WeilAtPlace.conjPl_eq_of_inert hw h) he
  have hsec_e : ∀ y, GlobalTheory.EmbChart.tensAt D.host.E v 1 * secW hw h y = secW hw h y := fun y => by
    show GlobalTheory.EmbChart.tensAt D.host.E v 1 * GlobalTheory.EmbChart.tensAt D.host.E v _ = GlobalTheory.EmbChart.tensAt D.host.E v _
    rw [tensAt_mul_tensAt, one_mul]
  let f0 : w.adicCompletion D.host.E →+* w.adicCompletion D.host.E :=
    { toFun := fun z => π0 (secW hw h z)
      map_one' := by
        show π0 (GlobalTheory.EmbChart.tensAt D.host.E v ((GlobalTheory.LFun.InertChart.complEquiv hw h).symm 1)) = 1
        rw [map_one]
        exact hch.pi_idem
      map_mul' := fun z z' => by
        show π0 (secW hw h (z * z')) = π0 (secW hw h z) * π0 (secW hw h z')
        rw [secW_mul, map_mul]
      map_zero' := by
        show π0 (secW hw h 0) = 0
        rw [map_zero, map_zero]
      map_add' := fun z z' => by
        show π0 (secW hw h (z + z')) = π0 (secW hw h z) + π0 (secW hw h z')
        rw [map_add, map_add] }
  have hf0 : f0 = RingHom.id _ := ringHom_eq_id_of_int w f0 (fun x => by
      show π0 (GlobalTheory.EmbChart.tensAt D.host.E v ((GlobalTheory.LFun.InertChart.complEquiv hw h).symm (algebraMap D.host.E _ x))) = _
      rw [complEquiv_symm_algebraMap, ← tensAt_one_mul_incA, map_mul, hch.pi_idem, one_mul, hch.2.2.2.1])
    (fun z hz => by
      refine (hch.2.2.2.2.2 (secW hw h z)).1 ?_
      rw [hsec_e]
      show finPart D (GlobalTheory.EmbChart.tensAt D.host.E v ((GlobalTheory.LFun.InertChart.complEquiv hw h).symm z)) ∈ intAE D
      rw [GlobalTheory.EmbChart.finPart_tensAt_mem_iff, GlobalTheory.LFun.InertChart.mem_intLoc_iff hw h]
      show (GlobalTheory.LFun.InertChart.complEquiv hw h) ((GlobalTheory.LFun.InertChart.complEquiv hw h).symm z) ∈ Ov D.host.E w
      rw [RingEquiv.apply_symm_apply]
      exact hz)
  have hpi : ∀ z, π0 (secW hw h z) = z := fun z => RingHom.congr_fun hf0 z
  have hsec : ∀ z, hch.sec z = secW hw h z := fun z =>
    hch.ext (hch.mul_sec z) (hsec_e z) (by rw [hch.pi_sec, hpi])
  have hσc : ∀ x : D.host.E, σ0 (algebraMap D.host.E _ x) = c (algebraMap D.host.E _ x) := fun x => by
    calc σ0 (algebraMap D.host.E _ x) = σ0 (π0 (incA D x)) := by rw [hch.2.2.2.1]
      _ = π0 (cA D (incA D x)) := (hch.2.2.2.2.1 _).symm
      _ = algebraMap D.host.E _ (D.sp.cm.sig x) := hch.2.2.2.1 (D.sp.cm.sig x)
      _ = c (algebraMap D.host.E _ x) := (GlobalTheory.LFun.InertChart.conj_algebraMap hconj x).symm
  have hg := ringHom_eq_id_of_int w (c.comp σ0) (fun x => by
      rw [RingHom.comp_apply, hσc, hU.1])
    (fun z hz => by
      rw [RingHom.comp_apply, hU.2.1, hU0.2.1]
      exact hz)
  have hσ : ∀ z, σ0 z = c z := fun z => by
    have h1 : c (σ0 z) = z := RingHom.congr_fun hg z
    calc σ0 z = c (c (σ0 z)) := (hU.1 _).symm
      _ = c z := by rw [h1]
  have hth : ∀ z, GlobalTheory.InertLoc.th ψ hch k z = thW ψ hw h (k * c k) z := fun z => by
    rw [GlobalTheory.InertLoc.th_apply, thW_apply, hσ, hsec]
  obtain ⟨β, -, hβ, -⟩ := hV D.sp.X'
  have hi : 0 < D.sp.X'.rank := by
    have h1 := D.R.m_add_three_le_k
    rw [D.sp.X'_rank, Formalism.BasicNotions.Ranks.rankX', Formalism.BasicNotions.Ranks.r]
    omega
  have := GlobalTheory.InertLoc.th_cond hψ hch hU0.2.1 hβ ⟨0, hi⟩ hk z
  simpa only [hth] using this

end GlobalTheory.InertFrameLoc
