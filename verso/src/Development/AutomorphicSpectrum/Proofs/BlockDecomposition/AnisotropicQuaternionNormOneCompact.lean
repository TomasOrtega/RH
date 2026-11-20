import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PlaneSupports.PlaneSupp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianPlaneStrongApprox
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup

noncomputable section

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published GlobalTheory.CompanionTheory.PlaneSA Topology
open scoped TensorProduct Quaternion

namespace GlobalTheory.CompanionTheory.PlaneSA

/- English proof (translation)
Take `⟨c, hc⟩` from `NormedField.exists_one_lt_norm K`. Establish `hcpos : 0 < ‖c‖` using `lt_trans zero_lt_one hc`. Establish `hq0 : q 0 = 0`. Use `hh 0 0` as an intermediate fact. Simplify using `using this`.

Use `set S : Set (K × K × K × K) := {v | ‖c‖⁻¹ ≤ ‖v‖ ∧ ‖v‖ ≤ 1} with hS`. Establish `hScl : IsClosed S` using `(isClosed_le continuous_const continuous_norm).inter (isClosed_le continuous_norm continuous_const)`. Establish `hSc : IsCompact S`. Use `IsCompact.of_isClosed_subset (isCompact_closedBall (0 : K × K × K × K) 1) hScl ?_` and prove the remaining obligations. Introduce `v hv`.

Simplify `hv.2` using `[mem_closedBall_zero_iff]`. Establish `hpos : ∀ v ∈ S, (0 : ℝ) < ‖q v‖`. Introduce `v hv`. Rewrite using `[norm_pos_iff]`. Introduce `hv0`.

Establish `h1` using `h0 v hv0`. Establish `h2` using `hv.1`. Rewrite `h2` using `[h1, norm_zero]`. Conclude with `absurd h2 (not_le.2 (inv_pos.2 hcpos))`. Take `⟨m, hm, hmS⟩` from `hSc.exists_forall_le' (hq.norm.continuousOn) hpos`.

Establish `hbound : {v | q v = 1} ⊆ Metric.closedBall (0 : K × K × K × K) (1 + m⁻¹)`. Introduce `v hv`. Establish `hv1 : q v = 1` using `hv`. Establish `hvne : v ≠ 0`. Introduce and unpack `rfl`.

Rewrite `hv1` using `[hq0]`. Conclude with `zero_ne_one hv1`. Take `⟨a, ha, hlt, hge, -⟩` from `rescale_to_shell hc one_pos hvne`. Establish `hmem : a • v ∈ S` using `⟨by simpa [one_div] using hge, hlt.le⟩`. Establish `h1` using `hmS _ hmem`.

Rewrite `h1` using `[hh, hv1, mul_one, norm_pow]`. Rewrite `hlt` using `[norm_smul]`. Rewrite using `[mem_closedBall_zero_iff]`. Assume the negation of the conclusion as `hcon`. Establish `hcon' : 1 + m⁻¹ < ‖v‖` using `not_le.1 hcon`.

Establish `hminv : 0 < m⁻¹` using `inv_pos.2 hm`. Establish `ht1 : 1 < ‖v‖` using `by linarith`. Establish `hapos : 0 ≤ ‖a‖` using `norm_nonneg a`. Establish `h3 : (‖a‖ * ‖v‖) ^ 2 < 1`. Establish `: 0 ≤ ‖a‖ * ‖v‖` using `by positivity`.

Use the polynomial consequences of the given equalities and inequalities. Establish `h4 : m * ‖v‖ ^ 2 ≤ (‖a‖ * ‖v‖) ^ 2`. Rewrite using `[mul_pow]`. Conclude with `mul_le_mul_of_nonneg_right h1 (by positivity)`. Establish `h5 : m * ‖v‖ < 1`.

Establish `: m * ‖v‖ < m * ‖v‖ ^ 2`. Apply `mul_lt_mul_of_pos_left _ hm` to reduce the goal to its premises. Use the polynomial consequences of the given equalities and inequalities. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h6 : m * (1 + m⁻¹) < m * ‖v‖` using `mul_lt_mul_of_pos_left hcon' hm`.

Establish `h7 : m * (1 + m⁻¹) = m + 1`. Clear the denominators using the available nonvanishing facts. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `IsCompact.of_isClosed_subset (isCompact_closedBall _ _) (isClosed_eq hq continuous_const) hbound`.
-/
theorem isCompact_level_one_of_anisotropic {K : Type} [NontriviallyNormedField K] [ProperSpace K]
    (q : K × K × K × K → K) (hq : Continuous q)
    (hh : ∀ (c : K) (v : K × K × K × K), q (c • v) = c ^ 2 * q v)
    (h0 : ∀ v, q v = 0 → v = 0) : IsCompact {v | q v = 1} := by
  obtain ⟨c, hc⟩ := NormedField.exists_one_lt_norm K
  have hcpos : 0 < ‖c‖ := lt_trans zero_lt_one hc
  have hq0 : q 0 = 0 := by
    have := hh 0 0
    simpa using this
  set S : Set (K × K × K × K) := {v | ‖c‖⁻¹ ≤ ‖v‖ ∧ ‖v‖ ≤ 1} with hS
  have hScl : IsClosed S :=
    (isClosed_le continuous_const continuous_norm).inter (isClosed_le continuous_norm continuous_const)
  have hSc : IsCompact S := by
    refine IsCompact.of_isClosed_subset (isCompact_closedBall (0 : K × K × K × K) 1) hScl ?_
    intro v hv
    simpa [mem_closedBall_zero_iff] using hv.2
  have hpos : ∀ v ∈ S, (0 : ℝ) < ‖q v‖ := by
    intro v hv
    rw [norm_pos_iff]
    intro hv0
    have h1 := h0 v hv0
    have h2 := hv.1
    rw [h1, norm_zero] at h2
    exact absurd h2 (not_le.2 (inv_pos.2 hcpos))
  obtain ⟨m, hm, hmS⟩ := hSc.exists_forall_le' (hq.norm.continuousOn) hpos
  have hbound : {v | q v = 1} ⊆ Metric.closedBall (0 : K × K × K × K) (1 + m⁻¹) := by
    intro v hv
    have hv1 : q v = 1 := hv
    have hvne : v ≠ 0 := by
      rintro rfl
      rw [hq0] at hv1
      exact zero_ne_one hv1
    obtain ⟨a, ha, hlt, hge, -⟩ := rescale_to_shell hc one_pos hvne
    have hmem : a • v ∈ S := ⟨by simpa [one_div] using hge, hlt.le⟩
    have h1 := hmS _ hmem
    rw [hh, hv1, mul_one, norm_pow] at h1
    rw [norm_smul] at hlt
    rw [mem_closedBall_zero_iff]
    by_contra hcon
    have hcon' : 1 + m⁻¹ < ‖v‖ := not_le.1 hcon
    have hminv : 0 < m⁻¹ := inv_pos.2 hm
    have ht1 : 1 < ‖v‖ := by linarith
    have hapos : 0 ≤ ‖a‖ := norm_nonneg a
    have h3 : (‖a‖ * ‖v‖) ^ 2 < 1 := by
      have : 0 ≤ ‖a‖ * ‖v‖ := by positivity
      nlinarith
    have h4 : m * ‖v‖ ^ 2 ≤ (‖a‖ * ‖v‖) ^ 2 := by
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_right h1 (by positivity)
    have h5 : m * ‖v‖ < 1 := by
      have : m * ‖v‖ < m * ‖v‖ ^ 2 := by
        apply mul_lt_mul_of_pos_left _ hm
        nlinarith
      linarith
    have h6 : m * (1 + m⁻¹) < m * ‖v‖ := mul_lt_mul_of_pos_left hcon' hm
    have h7 : m * (1 + m⁻¹) = m + 1 := by
      field_simp
    linarith
  exact IsCompact.of_isClosed_subset (isCompact_closedBall _ _)
    (isClosed_eq hq continuous_const) hbound

/- English proof (translation)
Use `set D := algebraMap F K d`. Use `set B := algebraMap F K β`. Set `q : K × K × K × K → K` to `fun v => v.1 ^ 2 - D * v.2.1 ^ 2 - B * v.2.2.1 ^ 2 + D * B * v.2.2.2 ^ 2`. Establish `hq : Continuous q` using `by fun_prop`. Establish `hh : ∀ (c : K) (v : K × K × K × K), q (c • v) = c ^ 2 * q v`.

Introduce `c v`. Simplify using `only [q, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `h0 : ∀ v, q v = 0 → v = 0`. Introduce and unpack `⟨a, b, e, f⟩ hv`.

Use `h (⟨a, b, e, f⟩ : Q d β K) hv` as an intermediate fact. Establish `h1` using `congrArg QuaternionAlgebra.re this`. Establish `h2` using `congrArg QuaternionAlgebra.imI this`. Establish `h3` using `congrArg QuaternionAlgebra.imJ this`. Establish `h4` using `congrArg QuaternionAlgebra.imK this`.

Simplify using `at h1 h2 h3 h4`. Simplify using `[h1, h2, h3, h4]`. Establish `hc` using `isCompact_level_one_of_anisotropic q hq hh h0`. Conclude with `(qHomeo (d := d) (β := β) (R := K)).isCompact_preimage.2 hc`.
-/
theorem isCompact_qn_eq_one_of_normed {F : Type} [Field F] (d β : F)
    {K : Type} [NontriviallyNormedField K] [ProperSpace K] [Algebra F K]
    (h : ∀ x : Q d β K, qn x = 0 → x = 0) : IsCompact {x : Q d β K | qn x = 1} := by
  set D := algebraMap F K d
  set B := algebraMap F K β
  let q : K × K × K × K → K := fun v =>
    v.1 ^ 2 - D * v.2.1 ^ 2 - B * v.2.2.1 ^ 2 + D * B * v.2.2.2 ^ 2
  have hq : Continuous q := by fun_prop
  have hh : ∀ (c : K) (v : K × K × K × K), q (c • v) = c ^ 2 * q v := by
    intro c v
    simp only [q, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring
  have h0 : ∀ v, q v = 0 → v = 0 := by
    rintro ⟨a, b, e, f⟩ hv
    have := h (⟨a, b, e, f⟩ : Q d β K) hv
    have h1 := congrArg QuaternionAlgebra.re this
    have h2 := congrArg QuaternionAlgebra.imI this
    have h3 := congrArg QuaternionAlgebra.imJ this
    have h4 := congrArg QuaternionAlgebra.imK this
    simp at h1 h2 h3 h4
    simp [h1, h2, h3, h4]
  have hc := isCompact_level_one_of_anisotropic q hq hh h0
  exact (qHomeo (d := d) (β := β) (R := K)).isCompact_preimage.2 hc

/- English proof (translation)
Consider the cases of `s with`. Consider the case `inl w`. Use `letI : NontriviallyNormedField w.Completion := { (inferInstance : NormedField w.Completion) with non_trivial := ⟨2, by`. Rewrite using `[← (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _), map_ofNat]`. Use the proof step `simp⟩ }`.

Use `haveI : ProperSpace w.Completion := ProperSpace.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace w.Completion`. Conclude with `isCompact_qn_eq_one_of_normed (K := w.Completion) d β h`. Consider the case `inr v`. Use `letI : NontriviallyNormedField (v.adicCompletion F) := Valued.toNontriviallyNormedField _ _`. Use `haveI : ProperSpace (v.adicCompletion F) := GlobalTheory.AdelicUnitaryTop.properSpace_adicCompletion F v`.

Conclude with `isCompact_qn_eq_one_of_normed (K := v.adicCompletion F) d β h`.
-/
theorem isCompact_qn_eq_one_at_place {F : Type} [Field F] [NumberField F] (d β : F) (s : Pl F)
    (h : ∀ x : Q d β (Kp s), qn x = 0 → x = 0) : IsCompact {x : Q d β (Kp s) | qn x = 1} := by
  cases s with
  | inl w =>
    letI : NontriviallyNormedField w.Completion :=
      { (inferInstance : NormedField w.Completion) with
        non_trivial := ⟨2, by
          rw [← (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _),
            map_ofNat]
          simp⟩ }
    haveI : ProperSpace w.Completion :=
      ProperSpace.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace w.Completion
    exact isCompact_qn_eq_one_of_normed (K := w.Completion) d β h
  | inr v =>
    letI : NontriviallyNormedField (v.adicCompletion F) := Valued.toNontriviallyNormedField _ _
    haveI : ProperSpace (v.adicCompletion F) := GlobalTheory.AdelicUnitaryTop.properSpace_adicCompletion F v
    exact isCompact_qn_eq_one_of_normed (K := v.adicCompletion F) d β h

end GlobalTheory.CompanionTheory.PlaneSA
