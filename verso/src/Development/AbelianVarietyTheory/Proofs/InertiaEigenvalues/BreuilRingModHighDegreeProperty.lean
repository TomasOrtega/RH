import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ImageStableDegreeBounds

noncomputable section

namespace GlobalTheory.BK

open PowerSeries Filter

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K]

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Separate the alternatives or extract the components of the hypothesis. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact.

Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem wS_eq_one_of_lt (l : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K] {e n : ℕ}
    (hn : n < l * e) : wS K e n = 1 := by
  have hp : l.Prime := Fact.out
  have h1 : n / e < l := by
    rcases Nat.eq_zero_or_pos e with rfl | he
    · simpa using hp.pos
    · exact Nat.div_lt_of_lt_mul (by rwa [mul_comm] at hn)
  have hc : Nat.Coprime l (n / e).factorial :=
    (Nat.Prime.coprime_iff_not_dvd hp).2 fun h => absurd (hp.dvd_factorial.1 h) (by omega)
  unfold wS
  rw [norm_natCast_eq l, Padic.norm_natCast_eq_one_iff]
  first | exact hc | exact hc.symm

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem norm_coeff_N_mul_wS_le (e : ℕ) (f : K⟦X⟧) (n : ℕ) :
    ‖coeff n (N K f)‖ * wS K e n ≤ ‖coeff n f‖ * wS K e n := by
  rw [coeff_N, norm_mul, mul_assoc]
  exact mul_le_of_le_one_left (mul_nonneg (norm_nonneg _) (wS_nonneg _ _))
    (IsUltrametricDist.norm_natCast_le_one K n)

/- English proof (translation)
Supply the required witnesses or components.
-/
theorem N_mem_S {e : ℕ} {f : K⟦X⟧} (hf : f ∈ S O K e) : N K f ∈ S O K e :=
  ⟨fun n => (norm_coeff_N_mul_wS_le e f n).trans (hf.1 n),
    squeeze_zero (fun n => mul_nonneg (norm_nonneg _) (wS_nonneg e n))
      (norm_coeff_N_mul_wS_le e f) hf.2⟩

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations.

Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Express the relevant assertion in an equivalent form by its definition.

Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. Fix the arbitrary inputs or assume the hypotheses. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components.

Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Assume the hypotheses and unpack their components.

Establish an intermediate fact. Supply the required witnesses or components. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem ringModHigh : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K]
    [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) [Fact l.Prime]
    [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a], GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.RingModHigh O K l e := by
  intro O K _ _ _ _ _ _ l e a _ _ _ _
  refine ⟨?_, ?_, ?_⟩
  · intro f hf
    refine ⟨⟨N K (f : K⟦X⟧), N_mem_S f.2⟩, ?_, rfl⟩
    refine GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.mem_SHigh.2 (X_pow_dvd_iff.2 fun m hm => ?_)
    change coeff m (N K (f : K⟦X⟧)) = 0
    rw [coeff_N, X_pow_dvd_iff.1 (GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.mem_SHigh.1 hf) m hm, mul_zero]
  · intro f
    constructor
    · intro hf
      set g : K⟦X⟧ := ((trunc (l * e) f : Polynomial K) : K⟦X⟧) with hgdef
      have hg : ∀ n, coeff n g = if n < l * e then coeff n f else 0 := by
        intro n
        rw [hgdef, Polynomial.coeff_coe, coeff_trunc]
      have gA : g ∈ A O K := fun n => by
        rw [hg]
        split_ifs with h
        · have := hf.1 n
          rwa [wS_eq_one_of_lt l h, mul_one] at this
        · simp
      refine ⟨g, gA, ⟨f - g, (S O K e).sub_mem hf (A_le_S l e gA)⟩,
        GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.mem_SHigh.2 (X_pow_dvd_iff.2 fun m hm => ?_), by simp⟩
      change coeff m (f - g) = 0
      rw [map_sub, hg, if_pos hm, sub_self]
    · rintro ⟨g, hg, h, -, rfl⟩
      exact (S O K e).add_mem (A_le_S l e hg) h.2
  · intro f
    constructor
    · rintro ⟨hfA, h, hh, rfl⟩
      obtain ⟨g, hg⟩ := GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.mem_SHigh.1 hh
      refine ⟨g, fun n => ?_, by rw [hg, ← pow_mul, mul_comm e l]⟩
      have := hfA (n + l * e)
      rwa [hg, coeff_X_pow_mul] at this
    · rintro ⟨g, hg, rfl⟩
      have hm : ((X : K⟦X⟧) ^ e) ^ l * g ∈ A O K :=
        (A O K).mul_mem ((A O K).pow_mem ((A O K).pow_mem HasU.X_mem e) l) hg
      exact ⟨hm, ⟨_, A_le_S l e hm⟩,
        GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.mem_SHigh.2 ⟨g, by
          change ((X : K⟦X⟧) ^ e) ^ l * g = _
          rw [← pow_mul, mul_comm e l]⟩, rfl⟩

end GlobalTheory.BK
