import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeReferenceFrame.IdemLiftOfSteps
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalEndomorphisms.HenselRoot

noncomputable section

open NumberField IsDedekindDomain Polynomial

namespace PI.ScRefExists.Id

/- English proof (translation)
Introduce `F _ _ v g α β hg hgv hα hβ`. Use `haveI : CharZero (v.adicCompletion F) := charZero_of_injective_algebraMap (algebraMap F (v.adicCompletion F)).injective`. Establish `memO : ∀ x : v.adicCompletion F, x ∈ v.adicCompletionIntegers F ↔ Valued.v x ≤ 1` using `fun x => by`. Rewrite using `[HeightOneSpectrum.mem_adicCompletionIntegers]`. Set `ϖ : v.adicCompletionIntegers F` to `⟨((g : ℕ) : v.adicCompletion F), (memO _).2 hgv.le⟩`.

Set `aO : v.adicCompletionIntegers F` to `⟨α, (memO _).2 hα⟩`. Set `bO : v.adicCompletionIntegers F` to `⟨β, (memO _).2 hβ⟩`. Establish `hϖ : ϖ ≠ 0`. Introduce `h`. Establish `h' : ((g : ℕ) : v.adicCompletion F) = 0` using `congrArg Subtype.val h`.

Conclude with `(Nat.cast_ne_zero.mpr (by omega : g ≠ 0)) h'`. Establish `h1 : ‖(ϖ : v.adicCompletion F)‖ < 1` using `Valued.toNormedField.norm_lt_one_iff.mpr hgv`. Use `haveI := PI.LocalEndW.isAdicComplete v ϖ hϖ h1`. Set `f : Polynomial (v.adicCompletionIntegers F)` to `X ^ 2 - C (1 + ϖ * aO) * X + C (ϖ * bO)`. Establish `hf : f.Monic` using `by simp only [f]; monicity!`.

Establish `h0 : f.eval 0 ∈ Ideal.span {ϖ}`. Establish `e : f.eval 0 = bO * ϖ`. Simplify using `only [f, eval_add, eval_sub, eval_pow, eval_X, eval_mul, eval_C]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, Ideal.mem_span_singleton']`.

Conclude with `⟨bO, rfl⟩`. Establish `hd : f.derivative.eval 0 = -(1 + ϖ * aO)` using `by simp [f]`. Establish `hm : Ideal.Quotient.mk (Ideal.span {ϖ}) (-(1 + ϖ * aO)) = -1`. Rewrite using `[← map_one (Ideal.Quotient.mk (Ideal.span {ϖ})), ← map_neg, Ideal.Quotient.eq, Ideal.mem_span_singleton']`. Conclude with `⟨-aO, by ring⟩`.

Take `⟨ρ, hρ, hρI⟩` from `HenselianRing.is_henselian (I := Ideal.span {ϖ}) f hf 0 h0 (by rw [hd, hm]; exact isUnit_one.neg)`. Rewrite `hρI` using `[sub_zero, Ideal.mem_span_singleton']`. Take `⟨r0, rfl⟩` from `hρI`. Establish `hroot : (r0 * ϖ) ^ 2 - (1 + ϖ * aO) * (r0 * ϖ) + ϖ * bO = 0`. Establish `h : f.eval (r0 * ϖ) = 0` using `hρ`.

Simplify `h` using `only [f, eval_add, eval_sub, eval_pow, eval_X, eval_mul, eval_C]`. Establish `hu : IsUnit (1 + ϖ * (aO - 2 * r0))`. Rewrite using `[HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]`. Establish `hy : Valued.v ((aO - 2 * r0 : v.adicCompletionIntegers F) : v.adicCompletion F) ≤ 1` using `(memO _).1 (aO - 2 * r0).2`. Establish `hlt : Valued.v ((ϖ : v.adicCompletion F) * ((aO - 2 * r0 : v.adicCompletionIntegers F) : v.adicCompletion F)) < 1`.

Rewrite using `[map_mul]`. Conclude with `lt_of_le_of_lt (mul_le_of_le_one_right' hy) hgv`. Conclude with `(Valued.v).map_one_add_of_lt hlt`. Take `⟨U, hU⟩` from `hu`. Take `⟨wO, hwO⟩ : ∃ w : v.adicCompletionIntegers F, w = ((U⁻¹ : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F)` from `⟨_, rfl⟩`.

Establish `huw : (1 + ϖ * (aO - 2 * r0)) * wO = 1` using `by rw [← hU, hwO]; exact U.mul_inv`. Take `⟨c1, hc1⟩ : ∃ c : v.adicCompletionIntegers F, c = -(aO - 2 * r0) * wO` from `⟨_, rfl⟩`. Take `⟨c2, hc2⟩ : ∃ c : v.adicCompletionIntegers F, c = r0 * wO` from `⟨_, rfl⟩`. Establish `hA : (1 + ϖ * aO) * (1 + ϖ * c1) ^ 2 - 2 * (1 + ϖ * c1) * (ϖ * c2) = 1 + ϖ * c1`. Rewrite using `[hc1, hc2]`.

Take the linear combination `((1 + ϖ * (-(aO - 2 * r0) * wO)) * (1 - (1 + ϖ * aO))) * huw`. Establish `hB : (ϖ * c2) ^ 2 - ϖ * bO * (1 + ϖ * c1) ^ 2 = -(ϖ * c2)`. Rewrite using `[hc1, hc2]`. Take the linear combination `(-(r0 * ϖ) * wO + ϖ * bO * (2 * wO - ((1 + ϖ * (aO - 2 * r0)) * wO - 1))) * huw + (-wO ^ 2) * hroot`. Establish `hC : (ϖ * c2) ^ 2 - (1 + ϖ * aO) * (ϖ * c2) * (1 + ϖ * c1) + ϖ * bO * (1 + ϖ * c1) ^ 2 = 0`.

Rewrite using `[hc1, hc2]`. Take the linear combination `((1 + ϖ * aO) * (r0 * ϖ) * wO - 2 * (ϖ * bO) * wO + ϖ * bO * ((1 + ϖ * (aO - 2 * r0)) * wO - 1)) * huw + wO ^ 2 * hroot`. Use `⟨(c1 : v.adicCompletion F), (c2 : v.adicCompletion F), (memO _).1 c1.2, (memO _).1 c2.2, ?_, ?_, ?_⟩` and prove the remaining obligations. Establish `e` using `congrArg (v.adicCompletionIntegers F).subtype hA`. Simplify using `only [map_add, map_sub, map_mul, map_pow, map_one, map_ofNat] at e`.

Conclude with `e`. Establish `e` using `congrArg (v.adicCompletionIntegers F).subtype hB`. Simplify using `only [map_add, map_sub, map_mul, map_pow, map_one, map_ofNat, map_neg] at e`. Conclude with `e`. Establish `e` using `congrArg (v.adicCompletionIntegers F).subtype hC`.

Simplify using `only [map_add, map_sub, map_mul, map_pow, map_one, map_ofNat, map_zero] at e`. Conclude with `e`.
-/
theorem locIdem : LocIdem := by
  intro F _ _ v g α β hg hgv hα hβ
  classical
  haveI : CharZero (v.adicCompletion F) :=
    charZero_of_injective_algebraMap (algebraMap F (v.adicCompletion F)).injective
  have memO : ∀ x : v.adicCompletion F, x ∈ v.adicCompletionIntegers F ↔ Valued.v x ≤ 1 := fun x => by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  let ϖ : v.adicCompletionIntegers F := ⟨((g : ℕ) : v.adicCompletion F), (memO _).2 hgv.le⟩
  let aO : v.adicCompletionIntegers F := ⟨α, (memO _).2 hα⟩
  let bO : v.adicCompletionIntegers F := ⟨β, (memO _).2 hβ⟩
  have hϖ : ϖ ≠ 0 := by
    intro h
    have h' : ((g : ℕ) : v.adicCompletion F) = 0 := congrArg Subtype.val h
    exact (Nat.cast_ne_zero.mpr (by omega : g ≠ 0)) h'
  have h1 : ‖(ϖ : v.adicCompletion F)‖ < 1 := Valued.toNormedField.norm_lt_one_iff.mpr hgv
  haveI := PI.LocalEndW.isAdicComplete v ϖ hϖ h1
  let f : Polynomial (v.adicCompletionIntegers F) := X ^ 2 - C (1 + ϖ * aO) * X + C (ϖ * bO)
  have hf : f.Monic := by simp only [f]; monicity!
  have h0 : f.eval 0 ∈ Ideal.span {ϖ} := by
    have e : f.eval 0 = bO * ϖ := by
      simp only [f, eval_add, eval_sub, eval_pow, eval_X, eval_mul, eval_C]; ring
    rw [e, Ideal.mem_span_singleton']
    exact ⟨bO, rfl⟩
  have hd : f.derivative.eval 0 = -(1 + ϖ * aO) := by simp [f]
  have hm : Ideal.Quotient.mk (Ideal.span {ϖ}) (-(1 + ϖ * aO)) = -1 := by
    rw [← map_one (Ideal.Quotient.mk (Ideal.span {ϖ})), ← map_neg, Ideal.Quotient.eq,
      Ideal.mem_span_singleton']
    exact ⟨-aO, by ring⟩
  obtain ⟨ρ, hρ, hρI⟩ := HenselianRing.is_henselian (I := Ideal.span {ϖ}) f hf 0 h0
    (by rw [hd, hm]; exact isUnit_one.neg)
  rw [sub_zero, Ideal.mem_span_singleton'] at hρI
  obtain ⟨r0, rfl⟩ := hρI
  have hroot : (r0 * ϖ) ^ 2 - (1 + ϖ * aO) * (r0 * ϖ) + ϖ * bO = 0 := by
    have h : f.eval (r0 * ϖ) = 0 := hρ
    simpa only [f, eval_add, eval_sub, eval_pow, eval_X, eval_mul, eval_C] using h
  have hu : IsUnit (1 + ϖ * (aO - 2 * r0)) := by
    rw [HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
    have hy : Valued.v ((aO - 2 * r0 : v.adicCompletionIntegers F) : v.adicCompletion F) ≤ 1 :=
      (memO _).1 (aO - 2 * r0).2
    have hlt : Valued.v ((ϖ : v.adicCompletion F) *
        ((aO - 2 * r0 : v.adicCompletionIntegers F) : v.adicCompletion F)) < 1 := by
      rw [map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_right' hy) hgv
    exact (Valued.v).map_one_add_of_lt hlt
  obtain ⟨U, hU⟩ := hu
  obtain ⟨wO, hwO⟩ : ∃ w : v.adicCompletionIntegers F, w = ((U⁻¹ : (v.adicCompletionIntegers F)ˣ) :
      v.adicCompletionIntegers F) := ⟨_, rfl⟩
  have huw : (1 + ϖ * (aO - 2 * r0)) * wO = 1 := by rw [← hU, hwO]; exact U.mul_inv
  obtain ⟨c1, hc1⟩ : ∃ c : v.adicCompletionIntegers F, c = -(aO - 2 * r0) * wO := ⟨_, rfl⟩
  obtain ⟨c2, hc2⟩ : ∃ c : v.adicCompletionIntegers F, c = r0 * wO := ⟨_, rfl⟩
  have hA : (1 + ϖ * aO) * (1 + ϖ * c1) ^ 2 - 2 * (1 + ϖ * c1) * (ϖ * c2) = 1 + ϖ * c1 := by
    rw [hc1, hc2]
    linear_combination ((1 + ϖ * (-(aO - 2 * r0) * wO)) * (1 - (1 + ϖ * aO))) * huw
  have hB : (ϖ * c2) ^ 2 - ϖ * bO * (1 + ϖ * c1) ^ 2 = -(ϖ * c2) := by
    rw [hc1, hc2]
    linear_combination (-(r0 * ϖ) * wO + ϖ * bO * (2 * wO - ((1 + ϖ * (aO - 2 * r0)) * wO - 1))) * huw
      + (-wO ^ 2) * hroot
  have hC : (ϖ * c2) ^ 2 - (1 + ϖ * aO) * (ϖ * c2) * (1 + ϖ * c1) + ϖ * bO * (1 + ϖ * c1) ^ 2 = 0 := by
    rw [hc1, hc2]
    linear_combination ((1 + ϖ * aO) * (r0 * ϖ) * wO - 2 * (ϖ * bO) * wO
      + ϖ * bO * ((1 + ϖ * (aO - 2 * r0)) * wO - 1)) * huw + wO ^ 2 * hroot
  refine ⟨(c1 : v.adicCompletion F), (c2 : v.adicCompletion F), (memO _).1 c1.2, (memO _).1 c2.2,
    ?_, ?_, ?_⟩
  · have e := congrArg (v.adicCompletionIntegers F).subtype hA
    simp only [map_add, map_sub, map_mul, map_pow, map_one, map_ofNat] at e
    exact e
  · have e := congrArg (v.adicCompletionIntegers F).subtype hB
    simp only [map_add, map_sub, map_mul, map_pow, map_one, map_ofNat, map_neg] at e
    exact e
  · have e := congrArg (v.adicCompletionIntegers F).subtype hC
    simp only [map_add, map_sub, map_mul, map_pow, map_one, map_ofNat, map_zero] at e
    exact e

end PI.ScRefExists.Id
