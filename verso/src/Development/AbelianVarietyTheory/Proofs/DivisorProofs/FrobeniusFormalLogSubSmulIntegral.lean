import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.FormalExpMulFormalExpNeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusSubstMapCongrPowModPStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalLogCoeffMemOfSubOneMemDpStatement
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.FormalCalc

namespace GlobalTheory.QLog

/- English proof (translation)
Introduce `p _ B O Q _ _ _ _ _ θ hF σB s hs hσ d g hg`. Establish `hp : p ≠ 0` using `(Fact.out : p.Prime).ne_zero`. Establish `hp2 : 2 ≤ p` using `(Fact.out : p.Prime).two_le`. Establish `hXB : HasSubst (fun i : Fin d => (X i : MvPowerSeries (Fin d) B) ^ p)` using `HasSubst.X_pow hp`. Establish `hXQ : HasSubst (fun i : Fin d => (X i : MvPowerSeries (Fin d) Q) ^ p)` using `HasSubst.X_pow hp`.

Establish `hX0 : ∀ i : Fin d, constantCoeff ((X i : MvPowerSeries (Fin d) B) ^ p) = 0` using `fun i => by`. Simplify using `[hp]`. Use `set v := subst (fun i : Fin d => (X i : MvPowerSeries (Fin d) B) ^ p) (map σB g) with hv`. Establish `hv1 : constantCoeff v = 1`. Rewrite using `[hv, constantCoeff_subst_of_zero hXB hX0]`.

Simplify using `[hg]`. Establish `hgp1 : constantCoeff (g ^ p) = 1` using `by simp [hg]`. Take `⟨u, hu⟩` from `isUnit_iff_constantCoeff.mpr (hgp1 ▸ isUnit_one : IsUnit (constantCoeff (g ^ p)))`. Use `set k : MvPowerSeries (Fin d) B := ↑u⁻¹ with hk`. Establish `hgk : g ^ p * k = 1` using `by rw [hk, ← hu, Units.mul_inv]`.

Establish `hk1 : constantCoeff k = 1`. Use `congrArg constantCoeff hgk` as an intermediate fact. Rewrite `this` using `[map_mul, hgp1, one_mul, map_one]`. Then use the resulting hypothesis. Establish `hc` using `fun α => GlobalTheory.T.frobenius_subst_map_congr_pow_mod_p p B σB hσ d g α`. Use `choose r hr using hc`.

Use `set R : MvPowerSeries (Fin d) B := fun α => r α with hR`. Establish `hvR : v - g ^ p = C (p : B) * R`. Use extensionality with `α`. Rewrite using `[coeff_C_mul, hr α]`. Both sides reduce to the same expression.

Use `set h := v * k with hh`. Establish `hh1 : constantCoeff h = 1` using `by rw [hh, map_mul, hv1, hk1, one_mul]`. Establish `hhv : h * g ^ p = v` using `by rw [hh, mul_assoc, mul_comm k, hgk, mul_one]`. Establish `hhJ : ∀ α, coeff α (h - 1) ∈ Ideal.span {(p : B)}`. Introduce `α`.

Establish `: h - 1 = C (p : B) * (R * k)`. Rewrite using `[hh, ← hgk, ← sub_mul, hvR, mul_assoc]`. Rewrite using `[this, coeff_C_mul]`. Conclude with `Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)`. Establish `hJ : ∀ x ∈ Ideal.span {(p : B)}, ∃ y ∈ Ideal.span {(p : B)}, x ^ p = p * y`.

Introduce `x hx`. Take `⟨a, rfl⟩` from `Ideal.mem_span_singleton'.1 hx`. Use `⟨(p : B) ^ (p - 1) * a ^ p, Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ (Ideal.mem_span_singleton_self _) _ (by omega)), ?_⟩` and prove the remaining obligations. Rewrite using `[mul_pow, ← mul_assoc, ← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ p), mul_comm]`. Establish `hlog` using `GlobalTheory.T.formalLog_coeff_mem_of_sub_one_mem_dp p B O Q θ hF _ hJ (Fin d) h hh1 hhJ`.

Use `set ι := algebraMap B Q with hι`. Establish `hG1 : constantCoeff (map ι g) = 1` using `by simp [hg]`. Establish `hmapG : map s (map ι g) = map ι (map σB g)`. Use extensionality with `α`. Simplify using `[coeff_map, hs]`.

Establish `hmapv : map ι v = subst (fun i : Fin d => (X i : MvPowerSeries (Fin d) Q) ^ p) (map ι (map σB g))`. Rewrite using `[hv, map_subst hXB]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Simplify using the standard rewrite rules.

Establish `hσG1 : constantCoeff (map ι (map σB g)) = 1` using `by simp [hg]`. Establish `key : frob p s (formalLog (map ι g)) - (p : Q) • formalLog (map ι g) = formalLog (map ι h)`. Rewrite using `[frob, map_formalLog s hG1, hmapG, subst_formalLog hXQ hσG1, ← hmapv, ← hhv, map_mul, map_pow, formalLog_mul (by simp [hh1]) (by simp [hg]), formalLog_pow p hG1, Nat.cast_smul_eq_nsmul, add_sub_cancel_right]`. Rewrite using `[key]`. Introduce `α`.

Take `⟨b, -, hb⟩` from `hlog α`. Conclude with `⟨b, trivial, hb⟩`.
-/
theorem in_frob_formalLog_sub_smul : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q]
    [CommRing O] [Algebra B Q] [Algebra ℚ Q] (θ : B →+* O), IsFrame p Q θ → ∀ (σB : B →+* B)
    (s : Q →+* Q), (∀ b, s (algebraMap B Q b) = algebraMap B Q (σB b)) →
    (∀ b, (p : B) ∣ σB b - b ^ p) → ∀ (d : ℕ) (g : MvPowerSeries (Fin d) B), constantCoeff g = 1 →
    In (⊤ : Ideal B) (frob p s (formalLog (map (algebraMap B Q) g)) -
      (p : Q) • formalLog (map (algebraMap B Q) g)) := by
  intro p _ B O Q _ _ _ _ _ θ hF σB s hs hσ d g hg
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hXB : HasSubst (fun i : Fin d => (X i : MvPowerSeries (Fin d) B) ^ p) := HasSubst.X_pow hp
  have hXQ : HasSubst (fun i : Fin d => (X i : MvPowerSeries (Fin d) Q) ^ p) := HasSubst.X_pow hp
  have hX0 : ∀ i : Fin d, constantCoeff ((X i : MvPowerSeries (Fin d) B) ^ p) = 0 := fun i => by
    simp [hp]
  set v := subst (fun i : Fin d => (X i : MvPowerSeries (Fin d) B) ^ p) (map σB g) with hv
  have hv1 : constantCoeff v = 1 := by
    rw [hv, constantCoeff_subst_of_zero hXB hX0]
    simp [hg]
  have hgp1 : constantCoeff (g ^ p) = 1 := by simp [hg]
  obtain ⟨u, hu⟩ := isUnit_iff_constantCoeff.mpr (hgp1 ▸ isUnit_one : IsUnit (constantCoeff (g ^ p)))
  set k : MvPowerSeries (Fin d) B := ↑u⁻¹ with hk
  have hgk : g ^ p * k = 1 := by rw [hk, ← hu, Units.mul_inv]
  have hk1 : constantCoeff k = 1 := by
    have := congrArg constantCoeff hgk
    rwa [map_mul, hgp1, one_mul, map_one] at this

  have hc := fun α => GlobalTheory.T.frobenius_subst_map_congr_pow_mod_p p B σB hσ d g α
  choose r hr using hc
  set R : MvPowerSeries (Fin d) B := fun α => r α with hR
  have hvR : v - g ^ p = C (p : B) * R := by
    ext α
    rw [coeff_C_mul, hr α]
    rfl
  set h := v * k with hh
  have hh1 : constantCoeff h = 1 := by rw [hh, map_mul, hv1, hk1, one_mul]
  have hhv : h * g ^ p = v := by rw [hh, mul_assoc, mul_comm k, hgk, mul_one]
  have hhJ : ∀ α, coeff α (h - 1) ∈ Ideal.span {(p : B)} := by
    intro α
    have : h - 1 = C (p : B) * (R * k) := by
      rw [hh, ← hgk, ← sub_mul, hvR, mul_assoc]
    rw [this, coeff_C_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  have hJ : ∀ x ∈ Ideal.span {(p : B)}, ∃ y ∈ Ideal.span {(p : B)}, x ^ p = p * y := by
    intro x hx
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 hx
    refine ⟨(p : B) ^ (p - 1) * a ^ p,
      Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ (Ideal.mem_span_singleton_self _) _
        (by omega)), ?_⟩
    rw [mul_pow, ← mul_assoc, ← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ p), mul_comm]
  have hlog := GlobalTheory.T.formalLog_coeff_mem_of_sub_one_mem_dp p B O Q θ hF _ hJ (Fin d) h hh1 hhJ

  set ι := algebraMap B Q with hι
  have hG1 : constantCoeff (map ι g) = 1 := by simp [hg]
  have hmapG : map s (map ι g) = map ι (map σB g) := by
    ext α
    simp [coeff_map, hs]
  have hmapv : map ι v = subst (fun i : Fin d => (X i : MvPowerSeries (Fin d) Q) ^ p)
      (map ι (map σB g)) := by
    rw [hv, map_subst hXB]
    congr 1
    funext i
    simp
  have hσG1 : constantCoeff (map ι (map σB g)) = 1 := by simp [hg]
  have key : frob p s (formalLog (map ι g)) - (p : Q) • formalLog (map ι g) =
      formalLog (map ι h) := by
    rw [frob, map_formalLog s hG1, hmapG, subst_formalLog hXQ hσG1, ← hmapv, ← hhv, map_mul,
      map_pow, formalLog_mul (by simp [hh1]) (by simp [hg]), formalLog_pow p hG1,
      Nat.cast_smul_eq_nsmul, add_sub_cancel_right]
  rw [key]
  intro α
  obtain ⟨b, -, hb⟩ := hlog α
  exact ⟨b, trivial, hb⟩

end GlobalTheory.QLog
