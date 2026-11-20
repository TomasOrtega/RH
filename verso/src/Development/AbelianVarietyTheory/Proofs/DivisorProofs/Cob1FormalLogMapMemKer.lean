import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.FormalExpMulFormalExpNeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalLogCoeffMemOfSubOneMemDpStatement

set_option autoImplicit false

noncomputable section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
  GlobalTheory.FormalCalc

namespace GlobalTheory.CobLog

section SlopeTestRemainingChoices

variable {R S : Type} [CommRing R] [CommRing S] {d : ℕ}

/- English proof (translation)
The claim follows from `hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _`.
-/
theorem hasSubst_inl : HasSubst (fun i : Fin d => (X (Sum.inl i) : MvPowerSeries (Fin d ⊕ Fin d) R)) :=
  hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _

/- English proof (translation)
The claim follows from `hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _`.
-/
theorem hasSubst_inr : HasSubst (fun i : Fin d => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) R)) :=
  hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _

/- English proof (translation)
Unfold `inL`. Rewrite using `[map_subst hasSubst_inl]`. Simplify using the standard rewrite rules.
-/
theorem map_inL (φ : R →+* S) (f : MvPowerSeries (Fin d) R) : map φ (inL f) = inL (map φ f) := by
  unfold inL
  rw [map_subst hasSubst_inl]
  simp

/- English proof (translation)
Unfold `inR`. Rewrite using `[map_subst hasSubst_inr]`. Simplify using the standard rewrite rules.
-/
theorem map_inR (φ : R →+* S) (f : MvPowerSeries (Fin d) R) : map φ (inR f) = inR (map φ f) := by
  unfold inR
  rw [map_subst hasSubst_inr]
  simp

/- English proof (translation)
Rewrite using `[GlobalTheory.FormalCalc.constantCoeff_subst_of_zero ha ha0, hf, map_one]`.
-/
theorem constantCoeff_subst_one {σ τ : Type} {a : σ → MvPowerSeries τ R} (ha : HasSubst a)
    (ha0 : ∀ i, constantCoeff (a i) = 0) {f : MvPowerSeries σ R} (hf : constantCoeff f = 1) :
    constantCoeff (subst a f) = 1 := by
  rw [GlobalTheory.FormalCalc.constantCoeff_subst_of_zero ha ha0, hf, map_one]

/- English proof (translation)
The claim follows from `constantCoeff_subst_one hasSubst_inl (fun _ => constantCoeff_X _) hf`.
-/
theorem constantCoeff_inL {f : MvPowerSeries (Fin d) R} (hf : constantCoeff f = 1) :
    constantCoeff (inL f) = 1 :=
  constantCoeff_subst_one hasSubst_inl (fun _ => constantCoeff_X _) hf

/- English proof (translation)
The claim follows from `constantCoeff_subst_one hasSubst_inr (fun _ => constantCoeff_X _) hf`.
-/
theorem constantCoeff_inR {f : MvPowerSeries (Fin d) R} (hf : constantCoeff f = 1) :
    constantCoeff (inR f) = 1 :=
  constantCoeff_subst_one hasSubst_inr (fun _ => constantCoeff_X _) hf

end SlopeTestRemainingChoices

/- English proof (translation)
Introduce `p _ B O Q _ _ _ _ _ θ hF d μ' hμ g hg hmul`. Establish `hsμ : HasSubst μ'` using `hasSubst_of_constantCoeff_zero hμ`. Establish `hμQ : ∀ i, constantCoeff (up Q μ' i) = 0` using `fun i => by`. Simplify using `[up, hμ i]`. Establish `hsμQ : HasSubst (up Q μ')` using `hasSubst_of_constantCoeff_zero hμQ`.

Use `set a : MvPowerSeries (Fin d ⊕ Fin d) B := subst μ' g with ha_def`. Use `set b : MvPowerSeries (Fin d ⊕ Fin d) B := inL g * inR g with hb_def`. Establish `ha1 : constantCoeff a = 1` using `constantCoeff_subst_one hsμ hμ hg`. Establish `hbL : constantCoeff (inL g) = 1` using `constantCoeff_inL hg`. Establish `hbR : constantCoeff (inR g) = 1` using `constantCoeff_inR hg`.

Establish `hb1 : constantCoeff b = ((1 : Bˣ) : B)` using `by simp [hb_def, hbL, hbR]`. Use `set h : MvPowerSeries (Fin d ⊕ Fin d) B := a * invOfUnit b 1 with hh_def`. Establish `hab : a = h * b`. Rewrite using `[hh_def, mul_assoc, invOfUnit_mul b 1 hb1, mul_one]`. Establish `hh1 : constantCoeff h = 1`.

Rewrite using `[hh_def, map_mul, ha1, constantCoeff_invOfUnit]`. Simplify using the standard rewrite rules. Establish `hG : constantCoeff (map (algebraMap B Q) g) = 1` using `by simp [hg]`. Establish `key : cob1 (up Q μ') (formalLog (map (algebraMap B Q) g)) = formalLog (map (algebraMap B Q) h)`. Unfold `cob1`.

Establish `e1 : subst (up Q μ') (formalLog (map (algebraMap B Q) g)) = formalLog (map (algebraMap B Q) a)`. Rewrite using `[subst_formalLog hsμQ hG, ha_def, map_subst hsμ]`. Both sides reduce to the same expression. Establish `e2 : inL (formalLog (map (algebraMap B Q) g)) = formalLog (map (algebraMap B Q) (inL g))`. Rewrite using `[map_inL]`.

Conclude with `subst_formalLog hasSubst_inl hG`. Establish `e3 : inR (formalLog (map (algebraMap B Q) g)) = formalLog (map (algebraMap B Q) (inR g))`. Rewrite using `[map_inR]`. Conclude with `subst_formalLog hasSubst_inr hG`. Establish `hmh : constantCoeff (map (algebraMap B Q) h) = 1` using `by simp [hh1]`.

Establish `hmL : constantCoeff (map (algebraMap B Q) (inL g)) = 1` using `by simp [hbL]`. Establish `hmR : constantCoeff (map (algebraMap B Q) (inR g)) = 1` using `by simp [hbR]`. Establish `e4 : formalLog (map (algebraMap B Q) a) = formalLog (map (algebraMap B Q) h) + formalLog (map (algebraMap B Q) (inL g)) + formalLog (map (algebraMap B Q) (inR g))`. Rewrite using `[hab, hb_def, ← mul_assoc, map_mul, map_mul, formalLog_mul (by rw [map_mul, hmh, hmL, mul_one]) hmR, formalLog_mul hmh hmL]`. Rewrite using `[e1, e2, e3, e4]`.

Normalize the expressions using the abelian group laws. Establish `hθb : IsUnit (map θ b)` using `isUnit_iff_constantCoeff.mpr (by simp [hb_def, hbL, hbR])`. Establish `hθh : map θ h = 1`. Establish `h1 : map θ a = map θ b`. Rewrite using `[ha_def, map_subst hsμ, hmul, hb_def, map_mul, map_inL, map_inR]`.

Rewrite `h1` using `[hab, map_mul]`. Conclude with `(IsUnit.mul_left_inj hθb).1 (h1.trans (one_mul _).symm)`. Establish `hJ : ∀ x ∈ RingHom.ker θ, ∃ y ∈ RingHom.ker θ, x ^ p = p * y`. Introduce `x hx`. Take `⟨y, hy, hxy⟩` from `hF.pd x (RingHom.mem_ker.1 hx)`.

Conclude with `⟨y, RingHom.mem_ker.2 hy, hxy⟩`. Establish `hker : ∀ α, coeff α (h - 1) ∈ RingHom.ker θ`. Introduce `α`. Rewrite using `[RingHom.mem_ker, ← coeff_map, map_sub, hθh, map_one, sub_self, map_zero]`. Rewrite using `[key]`.

Conclude with `GlobalTheory.T.formalLog_coeff_mem_of_sub_one_mem_dp p B O Q θ hF (RingHom.ker θ) hJ (Fin d ⊕ Fin d) h hh1 hker`.
-/
theorem cob1_formalLog_mem_ker : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q]
    [CommRing O] [Algebra B Q] [Algebra ℚ Q] (θ : B →+* O), IsFrame p Q θ → ∀ (d : ℕ)
    (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B), (∀ i, constantCoeff (μ' i) = 0) →
    ∀ g : MvPowerSeries (Fin d) B, constantCoeff g = 1 →
    subst (fun i => map θ (μ' i)) (map θ g) = inL (map θ g) * inR (map θ g) →
    In (RingHom.ker θ) (cob1 (up Q μ') (formalLog (map (algebraMap B Q) g))) := by
  intro p _ B O Q _ _ _ _ _ θ hF d μ' hμ g hg hmul
  have hsμ : HasSubst μ' := hasSubst_of_constantCoeff_zero hμ
  have hμQ : ∀ i, constantCoeff (up Q μ' i) = 0 := fun i => by
    simp [up, hμ i]
  have hsμQ : HasSubst (up Q μ') := hasSubst_of_constantCoeff_zero hμQ
  set a : MvPowerSeries (Fin d ⊕ Fin d) B := subst μ' g with ha_def
  set b : MvPowerSeries (Fin d ⊕ Fin d) B := inL g * inR g with hb_def
  have ha1 : constantCoeff a = 1 := constantCoeff_subst_one hsμ hμ hg
  have hbL : constantCoeff (inL g) = 1 := constantCoeff_inL hg
  have hbR : constantCoeff (inR g) = 1 := constantCoeff_inR hg
  have hb1 : constantCoeff b = ((1 : Bˣ) : B) := by simp [hb_def, hbL, hbR]
  set h : MvPowerSeries (Fin d ⊕ Fin d) B := a * invOfUnit b 1 with hh_def
  have hab : a = h * b := by
    rw [hh_def, mul_assoc, invOfUnit_mul b 1 hb1, mul_one]
  have hh1 : constantCoeff h = 1 := by
    rw [hh_def, map_mul, ha1, constantCoeff_invOfUnit]
    simp

  have hG : constantCoeff (map (algebraMap B Q) g) = 1 := by simp [hg]
  have key : cob1 (up Q μ') (formalLog (map (algebraMap B Q) g)) =
      formalLog (map (algebraMap B Q) h) := by
    unfold cob1
    have e1 : subst (up Q μ') (formalLog (map (algebraMap B Q) g)) =
        formalLog (map (algebraMap B Q) a) := by
      rw [subst_formalLog hsμQ hG, ha_def, map_subst hsμ]
      rfl
    have e2 : inL (formalLog (map (algebraMap B Q) g)) = formalLog (map (algebraMap B Q) (inL g)) := by
      rw [map_inL]
      exact subst_formalLog hasSubst_inl hG
    have e3 : inR (formalLog (map (algebraMap B Q) g)) = formalLog (map (algebraMap B Q) (inR g)) := by
      rw [map_inR]
      exact subst_formalLog hasSubst_inr hG
    have hmh : constantCoeff (map (algebraMap B Q) h) = 1 := by simp [hh1]
    have hmL : constantCoeff (map (algebraMap B Q) (inL g)) = 1 := by simp [hbL]
    have hmR : constantCoeff (map (algebraMap B Q) (inR g)) = 1 := by simp [hbR]
    have e4 : formalLog (map (algebraMap B Q) a) = formalLog (map (algebraMap B Q) h) +
        formalLog (map (algebraMap B Q) (inL g)) + formalLog (map (algebraMap B Q) (inR g)) := by
      rw [hab, hb_def, ← mul_assoc, map_mul, map_mul,
        formalLog_mul (by rw [map_mul, hmh, hmL, mul_one]) hmR, formalLog_mul hmh hmL]
    rw [e1, e2, e3, e4]
    abel

  have hθb : IsUnit (map θ b) := isUnit_iff_constantCoeff.mpr (by simp [hb_def, hbL, hbR])
  have hθh : map θ h = 1 := by
    have h1 : map θ a = map θ b := by
      rw [ha_def, map_subst hsμ, hmul, hb_def, map_mul, map_inL, map_inR]
    rw [hab, map_mul] at h1
    exact (IsUnit.mul_left_inj hθb).1 (h1.trans (one_mul _).symm)
  have hJ : ∀ x ∈ RingHom.ker θ, ∃ y ∈ RingHom.ker θ, x ^ p = p * y := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := hF.pd x (RingHom.mem_ker.1 hx)
    exact ⟨y, RingHom.mem_ker.2 hy, hxy⟩
  have hker : ∀ α, coeff α (h - 1) ∈ RingHom.ker θ := by
    intro α
    rw [RingHom.mem_ker, ← coeff_map, map_sub, hθh, map_one, sub_self, map_zero]
  rw [key]
  exact GlobalTheory.T.formalLog_coeff_mem_of_sub_one_mem_dp p B O Q θ hF (RingHom.ker θ) hJ (Fin d ⊕ Fin d) h hh1 hker

end GlobalTheory.CobLog
