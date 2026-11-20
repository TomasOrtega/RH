import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.ColumnConjugationMeasure
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFiniteMeasureQuotMeasure

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [local instance] GlobalTheory.CuspRep.CuspidalL2GL.discreteTopology_latticeGL

namespace PositivityTheory.AdelicQuotientData

namespace FundamentalDomainCentre

set_option synthInstance.maxHeartbeats 400000

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {k : ℕ}

abbrev fdL (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (k : ℕ) : Set (GA E k) :=
  GlobalTheory.AutomorphicL2Unitary.stdDom (latticeGL E k)

abbrev rhoZ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (k : ℕ) : Measure (GA E k) :=
  Measure.sum fun n : ℤ => Measure.dirac (splitCentre E k 1 ^ (-n))

instance rhoZ_sFinite : SFinite (rhoZ E k) := by
  unfold rhoZ
  infer_instance

/- English proof (translation)
Use `first`. Consider the case `(rw [rhoZ, lintegral_sum_measure]; simp only [lintegral_dirac])`. Consider the case `simp only [rhoZ, lintegral_sum_measure, lintegral_dirac]`.
-/
theorem lint_rhoZ (F : GA E k → ℝ≥0∞) : ∫⁻ r, F r ∂rhoZ E k = ∑' n : ℤ, F (splitCentre E k 1 ^ (-n)) := by
  first
  | (rw [rhoZ, lintegral_sum_measure]; simp only [lintegral_dirac])
  | simp only [rhoZ, lintegral_sum_measure, lintegral_dirac]

/- English proof (translation)
Establish `h1 : (0 : ℝ) < k` using `by exact_mod_cast (show 0 < k by omega)`. Establish `h2 : (0 : ℝ) < Module.finrank ℚ E`. Establish `: 0 < Module.finrank ℚ E` using `by first`. Consider the case `exact Module.finrank_pos`. Consider the case `exact Module.finrank_pos (R := ℚ) (M := E)`.

Consider the case `exact FiniteDimensional.finrank_pos`. Conclude with `this` after adjusting the coercions. Conclude with `mul_pos h1 h2`.
-/
theorem degree_rank_pos (hk : 1 ≤ k) : (0 : ℝ) < (k : ℝ) * (Module.finrank ℚ E : ℝ) := by
  have h1 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have h2 : (0 : ℝ) < Module.finrank ℚ E := by
    have : 0 < Module.finrank ℚ E := by
      first
      | exact Module.finrank_pos
      | exact Module.finrank_pos (R := ℚ) (M := E)
      | exact FiniteDimensional.finrank_pos
    exact_mod_cast this
  exact mul_pos h1 h2

/- English proof (translation)
Take `⟨hpos, hmul, -⟩` from `hD E k`. Establish `h` using `hmul 1 1`. Rewrite `h` using `[mul_one (1 : GA E k)]`. Establish `hp` using `hpos 1`. Establish `h' : Dt (1 : GA E k) * Dt (1 : GA E k) = Dt (1 : GA E k) * 1` using `by rw [mul_one]; exact h.symm`.

Conclude with `mul_left_cancel₀ hp.ne' h'`.
-/
theorem dt_one (hD : D0) : Dt (1 : GA E k) = 1 := by
  obtain ⟨hpos, hmul, -⟩ := hD E k
  have h := hmul 1 1
  rw [mul_one (1 : GA E k)] at h
  have hp := hpos 1
  have h' : Dt (1 : GA E k) * Dt (1 : GA E k) = Dt (1 : GA E k) * 1 := by rw [mul_one]; exact h.symm
  exact mul_left_cancel₀ hp.ne' h'

/- English proof (translation)
Rewrite using `[← GlobalTheory.CuspRep.CuspidalL2GL.splitCentre_intCast]`. Conclude with `(hD E k).2.2.2.2.2.2.1 n`.
-/
theorem dt_split_centre_zpow (hD : D0) (n : ℤ) :
    Dt (splitCentre E k 1 ^ n) = Real.exp ((k : ℝ) * (Module.finrank ℚ E : ℝ) * (n : ℝ)) := by
  rw [← GlobalTheory.CuspRep.CuspidalL2GL.splitCentre_intCast]
  exact (hD E k).2.2.2.2.2.2.1 n

/- English proof (translation)
Rewrite using `[← GlobalTheory.CuspRep.CuspidalL2GL.splitCentre_intCast]`. Conclude with `GlobalTheory.CuspRep.CuspidalL2GL.splitCentre_comm _ _`.
-/
theorem split_centre_commute (n : ℤ) (g : GA E k) : splitCentre E k 1 ^ n * g = g * splitCentre E k 1 ^ n := by
  rw [← GlobalTheory.CuspRep.CuspidalL2GL.splitCentre_intCast]
  exact GlobalTheory.CuspRep.CuspidalL2GL.splitCentre_comm _ _

/- English proof (translation)
Use `⟨⟨0, 1, fun h01 => ?_⟩⟩` and prove the remaining obligations. Use `haveI : Subsingleton (Ad E) := subsingleton_of_zero_eq_one h01`. Establish `h1 : splitCentre E k 1 = 1` using `by first`. Consider the case `exact Units.ext (Matrix.ext fun i j => Subsingleton.elim _ _)`. Consider the case `exact Subsingleton.elim _ _`.

Establish `h2 : Dt (splitCentre E k 1) = Real.exp ((k : ℝ) * (Module.finrank ℚ E : ℝ) * 1)` using `(hD E k).2.2.2.2.2.2.1 1`. Rewrite `h2` using `[h1, dt_one (E := E) (k := k) hD]`. Establish `h3` using `Real.exp_lt_exp.2 (show (0 : ℝ) < (k : ℝ) * (Module.finrank ℚ E : ℝ) * 1 by rw [mul_one]; exact degree_rank_pos (E := E) hk)`. Rewrite `h3` using `[Real.exp_zero]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem adeles_nontrivial (hD : D0) (hk : 1 ≤ k) : Nontrivial (Ad E) := by
  refine ⟨⟨0, 1, fun h01 => ?_⟩⟩
  haveI : Subsingleton (Ad E) := subsingleton_of_zero_eq_one h01
  have h1 : splitCentre E k 1 = 1 := by
    first
    | exact Units.ext (Matrix.ext fun i j => Subsingleton.elim _ _)
    | exact Subsingleton.elim _ _
  have h2 : Dt (splitCentre E k 1) = Real.exp ((k : ℝ) * (Module.finrank ℚ E : ℝ) * 1) :=
    (hD E k).2.2.2.2.2.2.1 1
  rw [h1, dt_one (E := E) (k := k) hD] at h2
  have h3 := Real.exp_lt_exp.2
    (show (0 : ℝ) < (k : ℝ) * (Module.finrank ℚ E : ℝ) * 1 by rw [mul_one]; exact degree_rank_pos (E := E) hk)
  rw [Real.exp_zero] at h3
  linarith

/- English proof (translation)
Use `haveI := adeles_nontrivial (E := E) hD hk`. Introduce `γ γ' h`. Use `Units.ext (Matrix.ext fun i j => ?_)` and prove the remaining obligations. Establish `h1 : (ratGL E k γ : Matrix (Fin k) (Fin k) (Ad E)) i j = (ratGL E k γ' : Matrix (Fin k) (Fin k) (Ad E)) i j` using `by rw [h]`. Use `first`.

Consider the case `exact (algebraMap E (Ad E)).injective h1`. Consider the case `exact RingHom.injective _ h1`. Consider the case `(simp [ratGL] at h1; exact h1)`.
-/
theorem rational_GL_injective (hD : D0) (hk : 1 ≤ k) : Function.Injective (ratGL E k) := by
  haveI := adeles_nontrivial (E := E) hD hk
  intro γ γ' h
  refine Units.ext (Matrix.ext fun i j => ?_)
  have h1 : (ratGL E k γ : Matrix (Fin k) (Fin k) (Ad E)) i j =
      (ratGL E k γ' : Matrix (Fin k) (Fin k) (Ad E)) i j := by rw [h]
  first
  | exact (algebraMap E (Ad E)).injective h1
  | exact RingHom.injective _ h1
  | (simp [ratGL] at h1; exact h1)

/- English proof (translation)
Take `⟨-, hmul, -, hrat, -⟩` from `hD E k`. Establish `h1` using `congrArg Dt h`. Rewrite `h1` using `[hmul, hmul, hrat, hrat, one_mul, one_mul, dt_split_centre_zpow (E := E) (k := k) hD, dt_split_centre_zpow (E := E) (k := k) hD]`. Establish `h2 : ((n : ℤ) : ℝ) = ((n' : ℤ) : ℝ)` using `mul_left_cancel₀ (degree_rank_pos (E := E) hk).ne' (Real.exp_injective h1)`. Establish `hn : n = n'` using `by exact_mod_cast h2`.

Substitute `hn` using the available equality. Conclude with `⟨rational_GL_injective hD hk (mul_right_cancel h), rfl⟩`.
-/
theorem rational_centre_injective (hD : D0) (hk : 1 ≤ k) {γ γ' : GL (Fin k) E} {n n' : ℤ}
    (h : ratGL E k γ * splitCentre E k 1 ^ n = ratGL E k γ' * splitCentre E k 1 ^ n') : γ = γ' ∧ n = n' := by
  obtain ⟨-, hmul, -, hrat, -⟩ := hD E k
  have h1 := congrArg Dt h
  rw [hmul, hmul, hrat, hrat, one_mul, one_mul, dt_split_centre_zpow (E := E) (k := k) hD,
    dt_split_centre_zpow (E := E) (k := k) hD] at h1
  have h2 : ((n : ℤ) : ℝ) = ((n' : ℤ) : ℝ) :=
    mul_left_cancel₀ (degree_rank_pos (E := E) hk).ne' (Real.exp_injective h1)
  have hn : n = n' := by exact_mod_cast h2
  subst hn
  exact ⟨rational_GL_injective hD hk (mul_right_cancel h), rfl⟩

/- English proof (translation)
Take `⟨⟨x, hx⟩, hxg, huniq⟩` from `GlobalTheory.AutomorphicL2Unitary.existsUnique_stdDom (latticeGL E k) g`. Take `⟨γ, n, rfl⟩` from `GlobalTheory.CuspRep.CuspidalL2GL.mem_latticeGL_iff.1 hx`. Establish `hmem : ratGL E k γ * splitCentre E k 1 ^ n * g ∈ fdL E k` using `hxg`. Rewrite using `[tsum_eq_single (γ, n)]`. Conclude with `Set.indicator_of_mem hmem _`.

Introduce and unpack `⟨γ', n'⟩ hne`. Establish `hnm : ratGL E k γ' * splitCentre E k 1 ^ n' * g ∉ fdL E k`. Introduce `hm'`. Establish `hm : ratGL E k γ' * splitCentre E k 1 ^ n' ∈ latticeGL E k` using `GlobalTheory.CuspRep.CuspidalL2GL.mem_latticeGL_iff.2 ⟨γ', n', rfl⟩`. Take `⟨e1, e2⟩` from `rational_centre_injective hD hk (congrArg Subtype.val (huniq ⟨_, hm⟩ hm'))`.

Conclude with `hne (by rw [e1, e2])`. Use `first`. Consider the case `exact Set.indicator_of_notMem hnm _`. Consider the case `exact Set.indicator_of_not_mem hnm _`.
-/
theorem fundamental_domain_tsum (hD : D0) (hk : 1 ≤ k) (g : GA E k) :
    ∑' p : GL (Fin k) E × ℤ, (fdL E k).indicator (1 : GA E k → ℝ≥0∞)
      (ratGL E k p.1 * splitCentre E k 1 ^ p.2 * g) = 1 := by
  obtain ⟨⟨x, hx⟩, hxg, huniq⟩ := GlobalTheory.AutomorphicL2Unitary.existsUnique_stdDom (latticeGL E k) g
  obtain ⟨γ, n, rfl⟩ := GlobalTheory.CuspRep.CuspidalL2GL.mem_latticeGL_iff.1 hx
  have hmem : ratGL E k γ * splitCentre E k 1 ^ n * g ∈ fdL E k := hxg
  rw [tsum_eq_single (γ, n)]
  · exact Set.indicator_of_mem hmem _
  · rintro ⟨γ', n'⟩ hne
    have hnm : ratGL E k γ' * splitCentre E k 1 ^ n' * g ∉ fdL E k := by
      intro hm'
      have hm : ratGL E k γ' * splitCentre E k 1 ^ n' ∈ latticeGL E k :=
        GlobalTheory.CuspRep.CuspidalL2GL.mem_latticeGL_iff.2 ⟨γ', n', rfl⟩
      obtain ⟨e1, e2⟩ := rational_centre_injective hD hk (congrArg Subtype.val (huniq ⟨_, hm⟩ hm'))
      exact hne (by rw [e1, e2])
    first
    | exact Set.indicator_of_notMem hnm _
    | exact Set.indicator_of_not_mem hnm _

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2⟩`. Rewrite `h1` using `[← Real.exp_add, Real.one_le_exp_iff]`. Rewrite `h2` using `[← Real.exp_add, Real.exp_lt_exp]`. Rewrite using `[eq_comm, Int.floor_eq_iff, le_div_iff₀ hc, div_lt_iff₀ hc]`.

Move the coercions through the operations in `at h1 h2`. Prove the components needed by the constructor for the conclusion. Apply the tactic sequence `first | linarith | nlinarith`. Apply the tactic sequence `first | linarith | nlinarith`. Introduce `h`.

Rewrite `h` using `[eq_comm, Int.floor_eq_iff, le_div_iff₀ hc, div_lt_iff₀ hc]`. Take `⟨h1, h2⟩` from `h`. Rewrite using `[← Real.exp_add, Real.one_le_exp_iff, Real.exp_lt_exp]`. Use `push_cast`. Prove the components needed by the constructor for the conclusion.

Apply the tactic sequence `first | linarith | nlinarith`. Apply the tactic sequence `first | linarith | nlinarith`.
-/
theorem exp_band_iff_floor {c L : ℝ} (hc : 0 < c) (n : ℤ) :
    (1 ≤ Real.exp (c * ((-n : ℤ) : ℝ)) * Real.exp L ∧
      Real.exp (c * ((-n : ℤ) : ℝ)) * Real.exp L < Real.exp (c * 1)) ↔ n = ⌊L / c⌋ := by
  constructor
  · rintro ⟨h1, h2⟩
    rw [← Real.exp_add, Real.one_le_exp_iff] at h1
    rw [← Real.exp_add, Real.exp_lt_exp] at h2
    rw [eq_comm, Int.floor_eq_iff, le_div_iff₀ hc, div_lt_iff₀ hc]
    push_cast at h1 h2
    constructor
    · first | linarith | nlinarith
    · first | linarith | nlinarith
  · intro h
    rw [eq_comm, Int.floor_eq_iff, le_div_iff₀ hc, div_lt_iff₀ hc] at h
    obtain ⟨h1, h2⟩ := h
    rw [← Real.exp_add, Real.one_le_exp_iff, Real.exp_lt_exp]
    push_cast
    constructor
    · first | linarith | nlinarith
    · first | linarith | nlinarith

/- English proof (translation)
Take `⟨hpos, hmul, -⟩` from `hD E k`. Establish `e2 : Dt (splitCentre E k 1) = Real.exp ((k : ℝ) * (Module.finrank ℚ E : ℝ) * 1)` using `(hD E k).2.2.2.2.2.2.1 1`. Use `show (1 ≤ Dt (splitCentre E k 1 ^ (-n) * g) ∧ Dt (splitCentre E k 1 ^ (-n) * g) < Dt (splitCentre E k 1)) ↔ _`. Rewrite using `[hmul, dt_split_centre_zpow (E := E) (k := k) hD, e2]`. Establish `h` using `exp_band_iff_floor (degree_rank_pos (E := E) hk) n (L := Real.log (Dt g))`.

Rewrite `h` using `[Real.exp_log (hpos g)]`. Conclude with `h`.
-/
theorem split_centre_band_iff (hD : D0) (hk : 1 ≤ k) (n : ℤ) (g : GA E k) :
    splitCentre E k 1 ^ (-n) * g ∈ band E k ↔
      n = ⌊Real.log (Dt g) / ((k : ℝ) * (Module.finrank ℚ E : ℝ))⌋ := by
  obtain ⟨hpos, hmul, -⟩ := hD E k
  have e2 : Dt (splitCentre E k 1) = Real.exp ((k : ℝ) * (Module.finrank ℚ E : ℝ) * 1) :=
    (hD E k).2.2.2.2.2.2.1 1
  show (1 ≤ Dt (splitCentre E k 1 ^ (-n) * g) ∧ Dt (splitCentre E k 1 ^ (-n) * g) < Dt (splitCentre E k 1)) ↔ _
  rw [hmul, dt_split_centre_zpow (E := E) (k := k) hD, e2]
  have h := exp_band_iff_floor (degree_rank_pos (E := E) hk) n (L := Real.log (Dt g))
  rw [Real.exp_log (hpos g)] at h
  exact h

end FundamentalDomainCentre

set_option synthInstance.maxHeartbeats 400000 in
/- English proof (translation)
Introduce `hQ1 hD hN3 E _ _ _ k μ _ hk`. Take `⟨hpos, hmul, hcont, hrat, huu, -⟩` from `hD E k`. Take `⟨hsf, hinv, hae⟩` from `(hN3 E k).2.1 k le_rfl`. Establish `hlint` using `(hN3 E k).2.2.1`. Establish `hF : MeasurableSet (FundamentalDomainCentre.fdL E k)` using `GlobalTheory.AutomorphicL2Unitary.measurableSet_stdDom (latticeGL E k)`.

Apply the tactic sequence `have hβ₁ : Measurable ((FundamentalDomainCentre.fdL E k).indicator (1 : GA E k → ℝ≥0∞)) := by first | exact measurable_one.indicator hF | exact measurable_const.indicator hF`. Use `⟨⟨fun g => ∑' n : ℤ, (FundamentalDomainCentre.fdL E k).indicator (1 : GA E k → ℝ≥0∞) (splitCentre E k 1 ^ n * g), Measurable.ennreal_tsum fun n => hβ₁.comp (measurable_const_mul _), fun g => ?_⟩, fun β hβ => ?_⟩` and prove the remaining obligations. Establish `hm : Measurable fun h : GA E k => ∑' n : ℤ, (FundamentalDomainCentre.fdL E k).indicator (1 : GA E k → ℝ≥0∞) (splitCentre E k 1 ^ n * (h * g))` using `Measurable.ennreal_tsum fun n => hβ₁.comp ((measurable_const_mul _).comp (measurable_mul_const g))`. Use `(hlint _ hm).trans ?_` and prove the remaining obligations. Use `Eq.trans ?_ (FundamentalDomainCentre.fundamental_domain_tsum hD hk g)` and prove the remaining obligations.

Rewrite using `[ENNReal.tsum_prod']`. Use `tsum_congr fun γ => tsum_congr fun n => ?_` and prove the remaining obligations. Use `show (FundamentalDomainCentre.fdL E k).indicator (1 : GA E k → ℝ≥0∞) (splitCentre E k 1 ^ n * (ratGL E k γ * g)) = (FundamentalDomainCentre.fdL E k).indicator (1 : GA E k → ℝ≥0∞) (ratGL E k γ * splitCentre E k 1 ^ n * g)`. Rewrite using `[← mul_assoc, FundamentalDomainCentre.split_centre_commute]`. Establish `hDm : Measurable (Dt : GA E k → ℝ)` using `hcont.measurable`.

Establish `hband : MeasurableSet (band E k)` using `(measurableSet_le measurable_const hDm).inter (measurableSet_lt hDm measurable_const)`. Apply the tactic sequence `have hΦ : Measurable ((band E k).indicator (1 : GA E k → ℝ≥0∞)) := by first | exact measurable_one.indicator hband | exact measurable_const.indicator hband`. Establish `hH : ∀ᵐ h ∂nuB E k k, h ∈ {x : GA E k | Dt x = 1}` using `by filter_upwards [hae] with h hh0`. Take `⟨γ, u, -, hu, hh⟩` from `hh0`. Use `show Dt h = 1`.

Rewrite using `[hh, hmul, hrat, huu k u hu, one_mul]`. Establish `hΦH : ∀ h ∈ {x : GA E k | Dt x = 1}, ∀ g, (band E k).indicator (1 : GA E k → ℝ≥0∞) (h * g) = (band E k).indicator (1 : GA E k → ℝ≥0∞) g`. Introduce `h hh g`. Establish `hh' : Dt h = 1` using `hh`. Establish `hiff : h * g ∈ band E k ↔ g ∈ band E k` using `by show (1 ≤ Dt (h * g) ∧ Dt (h * g) < Dt (splitCentre E k 1)) ↔ (1 ≤ Dt g ∧ Dt g < Dt (splitCentre E k 1))`.

Rewrite using `[hmul, hh', one_mul]`. Distinguish the cases in `hg : g ∈ band E k`. Apply the tactic sequence `rw [Set.indicator_of_mem hg, Set.indicator_of_mem (hiff.2 hg)] first | rfl | simp`. Rewrite using `[Set.indicator_of_notMem hg, Set.indicator_of_notMem (mt hiff.1 hg)]`. Establish `hone : ∀ g, ∫⁻ r, ∫⁻ h, (FundamentalDomainCentre.fdL E k).indicator (1 : GA E k → ℝ≥0∞) (r⁻¹ * h * g) ∂nuB E k k ∂FundamentalDomainCentre.rhoZ E k = 1`.

Introduce `g`. Apply the tactic sequence `first | rw [FundamentalDomainCentre.lint_rhoZ] | simp only [FundamentalDomainCentre.lint_rhoZ]`. Use `Eq.trans ?_ (FundamentalDomainCentre.fundamental_domain_tsum hD hk g)` and prove the remaining obligations. Rewrite using `[ENNReal.tsum_prod', ENNReal.tsum_comm]`. Use `tsum_congr fun n => ?_` and prove the remaining obligations.

Establish `hm : Measurable fun h : GA E k => (FundamentalDomainCentre.fdL E k).indicator (1 : GA E k → ℝ≥0∞) ((splitCentre E k 1 ^ (-n))⁻¹ * h * g)` using `hβ₁.comp ((measurable_mul_const g).comp (measurable_const_mul _))`. Use `(hlint _ hm).trans (tsum_congr fun γ => ?_)` and prove the remaining obligations. Use `show (FundamentalDomainCentre.fdL E k).indicator (1 : GA E k → ℝ≥0∞) ((splitCentre E k 1 ^ (-n))⁻¹ * ratGL E k γ * g) = (FundamentalDomainCentre.fdL E k).indicator (1 : GA E k → ℝ≥0∞) (ratGL E k γ * splitCentre E k 1 ^ n * g)`. Rewrite using `[_root_.zpow_neg, inv_inv, FundamentalDomainCentre.split_centre_commute]`. Establish `hin : ∀ g, ∫⁻ r, (band E k).indicator (1 : GA E k → ℝ≥0∞) (r * g) ∂FundamentalDomainCentre.rhoZ E k = 1`.

Introduce `g`. Apply the tactic sequence `first | rw [FundamentalDomainCentre.lint_rhoZ] | simp only [FundamentalDomainCentre.lint_rhoZ]`. Rewrite using `[tsum_eq_single ⌊Real.log (Dt g) / ((k : ℝ) * (Module.finrank ℚ E : ℝ))⌋]`. Conclude with `Set.indicator_of_mem ((FundamentalDomainCentre.split_centre_band_iff hD hk _ g).2 rfl) _`. Introduce `n hn`.

Conclude with `Set.indicator_of_notMem (fun hb => hn ((FundamentalDomainCentre.split_centre_band_iff hD hk n g).1 hb)) _`. Establish `hfin : IsFiniteMeasure (GlobalTheory.AutomorphicL2Unitary.quotMeasure (latticeGL E k) μ)` using `by first`. Consider the case `exact GlobalTheory.CovolGL.isFiniteMeasure_quotMeasure E k μ`. Consider the case `exact @GlobalTheory.CovolGL.isFiniteMeasure_quotMeasure E _ _ k _ μ ‹_›`. Consider the case `exact (GlobalTheory.CovolGL.finvol E k μ).1`.

Establish `hfinF : μ (FundamentalDomainCentre.fdL E k) < ∞` using `lt_of_eq_of_lt (GlobalTheory.AutomorphicL2Unitary.quotMeasure_univ (GlobalTheory.AutomorphicL2Unitary.isFundamentalDomain_stdDom (latticeGL E k) μ)).symm hfin.measure_univ_lt_top`. Establish `hQ` using `hQ1 (GA E k) μ (nuB E k k) (FundamentalDomainCentre.rhoZ E k) {x : GA E k | Dt x = 1} β ((FundamentalDomainCentre.fdL E k).indicator (1 : GA E k → ℝ≥0∞)) hinv hH hβ hβ₁ hone ((band E k).indicator (1 : GA E k → ℝ≥0∞)) hΦ hΦH`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[lintegral_one, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, lintegral_indicator_one hF]`. Use `_ < ∞ := hfinF`.
-/
theorem fundamental_domain_of : Q1 → D0 → N3 → W0 := by
  intro hQ1 hD hN3 E _ _ _ k μ _ hk
  obtain ⟨hpos, hmul, hcont, hrat, huu, -⟩ := hD E k
  obtain ⟨hsf, hinv, hae⟩ := (hN3 E k).2.1 k le_rfl
  have hlint := (hN3 E k).2.2.1
  have hF : MeasurableSet (FundamentalDomainCentre.fdL E k) := GlobalTheory.AutomorphicL2Unitary.measurableSet_stdDom (latticeGL E k)
  have hβ₁ : Measurable ((FundamentalDomainCentre.fdL E k).indicator (1 : GA E k → ℝ≥0∞)) := by
    first | exact measurable_one.indicator hF | exact measurable_const.indicator hF
  refine ⟨⟨fun g => ∑' n : ℤ, (FundamentalDomainCentre.fdL E k).indicator (1 : GA E k → ℝ≥0∞) (splitCentre E k 1 ^ n * g),
    Measurable.ennreal_tsum fun n => hβ₁.comp (measurable_const_mul _), fun g => ?_⟩, fun β hβ => ?_⟩
  · have hm : Measurable fun h : GA E k =>
        ∑' n : ℤ, (FundamentalDomainCentre.fdL E k).indicator (1 : GA E k → ℝ≥0∞) (splitCentre E k 1 ^ n * (h * g)) :=
      Measurable.ennreal_tsum fun n => hβ₁.comp ((measurable_const_mul _).comp (measurable_mul_const g))
    refine (hlint _ hm).trans ?_
    refine Eq.trans ?_ (FundamentalDomainCentre.fundamental_domain_tsum hD hk g)
    rw [ENNReal.tsum_prod']
    refine tsum_congr fun γ => tsum_congr fun n => ?_
    show (FundamentalDomainCentre.fdL E k).indicator (1 : GA E k → ℝ≥0∞) (splitCentre E k 1 ^ n * (ratGL E k γ * g)) =
      (FundamentalDomainCentre.fdL E k).indicator (1 : GA E k → ℝ≥0∞) (ratGL E k γ * splitCentre E k 1 ^ n * g)
    rw [← mul_assoc, FundamentalDomainCentre.split_centre_commute]
  · have hDm : Measurable (Dt : GA E k → ℝ) := hcont.measurable
    have hband : MeasurableSet (band E k) :=
      (measurableSet_le measurable_const hDm).inter (measurableSet_lt hDm measurable_const)
    have hΦ : Measurable ((band E k).indicator (1 : GA E k → ℝ≥0∞)) := by
      first | exact measurable_one.indicator hband | exact measurable_const.indicator hband
    have hH : ∀ᵐ h ∂nuB E k k, h ∈ {x : GA E k | Dt x = 1} := by
      filter_upwards [hae] with h hh0
      obtain ⟨γ, u, -, hu, hh⟩ := hh0
      show Dt h = 1
      rw [hh, hmul, hrat, huu k u hu, one_mul]
    have hΦH : ∀ h ∈ {x : GA E k | Dt x = 1}, ∀ g,
        (band E k).indicator (1 : GA E k → ℝ≥0∞) (h * g) = (band E k).indicator (1 : GA E k → ℝ≥0∞) g := by
      intro h hh g
      have hh' : Dt h = 1 := hh
      have hiff : h * g ∈ band E k ↔ g ∈ band E k := by
        show (1 ≤ Dt (h * g) ∧ Dt (h * g) < Dt (splitCentre E k 1)) ↔
          (1 ≤ Dt g ∧ Dt g < Dt (splitCentre E k 1))
        rw [hmul, hh', one_mul]
      by_cases hg : g ∈ band E k
      · rw [Set.indicator_of_mem hg, Set.indicator_of_mem (hiff.2 hg)]
        first | rfl | simp
      · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem (mt hiff.1 hg)]
    have hone : ∀ g, ∫⁻ r, ∫⁻ h, (FundamentalDomainCentre.fdL E k).indicator (1 : GA E k → ℝ≥0∞) (r⁻¹ * h * g)
        ∂nuB E k k ∂FundamentalDomainCentre.rhoZ E k = 1 := by
      intro g
      first | rw [FundamentalDomainCentre.lint_rhoZ] | simp only [FundamentalDomainCentre.lint_rhoZ]
      refine Eq.trans ?_ (FundamentalDomainCentre.fundamental_domain_tsum hD hk g)
      rw [ENNReal.tsum_prod', ENNReal.tsum_comm]
      refine tsum_congr fun n => ?_
      have hm : Measurable fun h : GA E k =>
          (FundamentalDomainCentre.fdL E k).indicator (1 : GA E k → ℝ≥0∞) ((splitCentre E k 1 ^ (-n))⁻¹ * h * g) :=
        hβ₁.comp ((measurable_mul_const g).comp (measurable_const_mul _))
      refine (hlint _ hm).trans (tsum_congr fun γ => ?_)
      show (FundamentalDomainCentre.fdL E k).indicator (1 : GA E k → ℝ≥0∞) ((splitCentre E k 1 ^ (-n))⁻¹ * ratGL E k γ * g) =
        (FundamentalDomainCentre.fdL E k).indicator (1 : GA E k → ℝ≥0∞) (ratGL E k γ * splitCentre E k 1 ^ n * g)
      rw [_root_.zpow_neg, inv_inv, FundamentalDomainCentre.split_centre_commute]
    have hin : ∀ g, ∫⁻ r, (band E k).indicator (1 : GA E k → ℝ≥0∞) (r * g) ∂FundamentalDomainCentre.rhoZ E k = 1 := by
      intro g
      first | rw [FundamentalDomainCentre.lint_rhoZ] | simp only [FundamentalDomainCentre.lint_rhoZ]
      rw [tsum_eq_single ⌊Real.log (Dt g) / ((k : ℝ) * (Module.finrank ℚ E : ℝ))⌋]
      · exact Set.indicator_of_mem ((FundamentalDomainCentre.split_centre_band_iff hD hk _ g).2 rfl) _
      · intro n hn
        exact Set.indicator_of_notMem (fun hb => hn ((FundamentalDomainCentre.split_centre_band_iff hD hk n g).1 hb)) _
    have hfin : IsFiniteMeasure (GlobalTheory.AutomorphicL2Unitary.quotMeasure (latticeGL E k) μ) := by
      first
      | exact GlobalTheory.CovolGL.isFiniteMeasure_quotMeasure E k μ
      | exact @GlobalTheory.CovolGL.isFiniteMeasure_quotMeasure E _ _ k _ μ ‹_›
      | exact (GlobalTheory.CovolGL.finvol E k μ).1
    have hfinF : μ (FundamentalDomainCentre.fdL E k) < ∞ :=
      lt_of_eq_of_lt (GlobalTheory.AutomorphicL2Unitary.quotMeasure_univ (GlobalTheory.AutomorphicL2Unitary.isFundamentalDomain_stdDom (latticeGL E k) μ)).symm
        hfin.measure_univ_lt_top
    have hQ := hQ1 (GA E k) μ (nuB E k k) (FundamentalDomainCentre.rhoZ E k) {x : GA E k | Dt x = 1} β
      ((FundamentalDomainCentre.fdL E k).indicator (1 : GA E k → ℝ≥0∞)) hinv hH hβ hβ₁ hone
      ((band E k).indicator (1 : GA E k → ℝ≥0∞)) hΦ hΦH
    calc μ.withDensity β (band E k)
        = ∫⁻ g, (band E k).indicator (1 : GA E k → ℝ≥0∞) g ∂μ.withDensity β :=
          (lintegral_indicator_one hband).symm
      _ = ∫⁻ g, ∫⁻ r, (band E k).indicator (1 : GA E k → ℝ≥0∞) (r * g) ∂FundamentalDomainCentre.rhoZ E k
          ∂μ.withDensity ((FundamentalDomainCentre.fdL E k).indicator (1 : GA E k → ℝ≥0∞)) := hQ
      _ = ∫⁻ _, 1 ∂μ.withDensity ((FundamentalDomainCentre.fdL E k).indicator (1 : GA E k → ℝ≥0∞)) := lintegral_congr hin
      _ = μ (FundamentalDomainCentre.fdL E k) := by
          rw [lintegral_one, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
            lintegral_indicator_one hF]
      _ < ∞ := hfinF

end PositivityTheory.AdelicQuotientData

end
