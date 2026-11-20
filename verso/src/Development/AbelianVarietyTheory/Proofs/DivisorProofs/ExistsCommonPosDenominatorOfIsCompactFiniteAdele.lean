import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne

noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum GlobalTheory.LKTrip GlobalTheory.LKMid
open scoped TensorProduct Classical RestrictedProduct

namespace GlobalTheory.AfPCpctDen

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem natCast_mul_apply {p : ℕ} (n : ℕ) (a : AfP p) (v : AwayP p) :
    (LevelExists.rp ((n : AfP p) * a)).1 v = (n : v.1.adicCompletion ℚ) * (LevelExists.rp a).1 v :=
  rfl

/- English proof (translation)
The claim follows from `natCast_mem _ n`.
-/
theorem natCast_mem_int (v : HeightOneSpectrum ℤ) (n : ℕ) :
    (n : v.adicCompletion ℚ) ∈ v.adicCompletionIntegers ℚ :=
  natCast_mem _ n

/- English proof (translation)
Take `⟨b, hb, hbx⟩` from `adicCompletion.mul_nonZeroDivisor_mem_adicCompletionIntegers v x`. Establish `hb0 : b ≠ 0` using `nonZeroDivisors.ne_zero hb`. Use `⟨b.natAbs, Int.natAbs_pos.mpr hb0, ?_⟩` and prove the remaining obligations. Break down `Int.natAbs_eq b with h | h` into its components or cases. Establish `e : ((b.natAbs : ℕ) : v.adicCompletion ℚ) = algebraMap ℤ (v.adicCompletion ℚ) b` using `by conv_rhs => rw [h]`.

Simplify using the standard rewrite rules. Rewrite using `[e, mul_comm]`. Conclude with `hbx`. Establish `e : ((b.natAbs : ℕ) : v.adicCompletion ℚ) = -algebraMap ℤ (v.adicCompletion ℚ) b` using `by conv_rhs => rw [h]`. Simplify using the standard rewrite rules.

Rewrite using `[e, neg_mul, mul_comm]`. Conclude with `neg_mem hbx`.
-/
theorem exists_nat_local (v : HeightOneSpectrum ℤ) (x : v.adicCompletion ℚ) :
    ∃ n : ℕ, 0 < n ∧ (n : v.adicCompletion ℚ) * x ∈ v.adicCompletionIntegers ℚ := by
  obtain ⟨b, hb, hbx⟩ := adicCompletion.mul_nonZeroDivisor_mem_adicCompletionIntegers v x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  refine ⟨b.natAbs, Int.natAbs_pos.mpr hb0, ?_⟩
  rcases Int.natAbs_eq b with h | h
  · have e : ((b.natAbs : ℕ) : v.adicCompletion ℚ) = algebraMap ℤ (v.adicCompletion ℚ) b := by
      conv_rhs => rw [h]
      simp
    rw [e, mul_comm]
    exact hbx
  · have e : ((b.natAbs : ℕ) : v.adicCompletion ℚ) = -algebraMap ℤ (v.adicCompletion ℚ) b := by
      conv_rhs => rw [h]
      simp
    rw [e, neg_mul, mul_comm]
    exact neg_mem hbx

/- English proof (translation)
Use `choose m hm0 hm using fun v : AwayP p => exists_nat_local v.1 ((LevelExists.rp a).1 v)`. Establish `hS : {v : AwayP p | ¬ (LevelExists.rp a).1 v ∈ v.1.adicCompletionIntegers ℚ}.Finite` using `Filter.eventually_cofinite.mp (LevelExists.rp a).2`. Use `⟨∏ v ∈ hS.toFinset, m v, Finset.prod_pos (fun v _ => hm0 v), fun w => ?_⟩` and prove the remaining obligations. Rewrite using `[natCast_mul_apply]`. Distinguish the cases in `hw : w ∈ hS.toFinset`.

Take `⟨k, hk⟩` from `Finset.dvd_prod_of_mem m hw`. Rewrite using `[hk, Nat.cast_mul, mul_comm ((m w : ℕ) : w.1.adicCompletion ℚ), mul_assoc]`. Conclude with `mul_mem (natCast_mem_int w.1 k) (hm w)`. Establish `hw' : (LevelExists.rp a).1 w ∈ w.1.adicCompletionIntegers ℚ`. Assume the negation of the conclusion as `h`.

Conclude with `hw (hS.mem_toFinset.mpr h)`. Conclude with `mul_mem (natCast_mem_int w.1 _) hw'`.
-/
theorem exists_nat_adele {p : ℕ} (a : AfP p) :
    ∃ n : ℕ, 0 < n ∧ (n : AfP p) * a ∈ LevelExists.intAfP p := by
  choose m hm0 hm using fun v : AwayP p => exists_nat_local v.1 ((LevelExists.rp a).1 v)
  have hS : {v : AwayP p | ¬ (LevelExists.rp a).1 v ∈ v.1.adicCompletionIntegers ℚ}.Finite :=
    Filter.eventually_cofinite.mp (LevelExists.rp a).2
  refine ⟨∏ v ∈ hS.toFinset, m v, Finset.prod_pos (fun v _ => hm0 v), fun w => ?_⟩
  rw [natCast_mul_apply]
  by_cases hw : w ∈ hS.toFinset
  · obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem m hw
    rw [hk, Nat.cast_mul, mul_comm ((m w : ℕ) : w.1.adicCompletion ℚ), mul_assoc]
    exact mul_mem (natCast_mem_int w.1 k) (hm w)
  · have hw' : (LevelExists.rp a).1 w ∈ w.1.adicCompletionIntegers ℚ := by
      by_contra h
      exact hw (hS.mem_toFinset.mpr h)
    exact mul_mem (natCast_mem_int w.1 _) hw'

/- English proof (translation)
Use `choose m hm0 hm using fun a : AfP p => exists_nat_adele a`. Take `⟨t, ht⟩` from `hS.elim_finite_subcover (fun a => (fun x => (m a : AfP p) * x) ⁻¹' (LevelExists.intAfP p : Set (AfP p))) (fun a => (LevelExists.isOpen_intAfP p).preimage (continuous_const_mul _)) (fun x _ => Set.mem_iUnion.mpr ⟨x, hm x⟩)`. Use `⟨∏ a ∈ t, m a, Finset.prod_pos (fun a _ => hm0 a), fun f hf => ?_⟩` and prove the remaining obligations. Take `⟨a, ha, hfa⟩` from `Set.mem_iUnion₂.mp (ht hf)`. Take `⟨k, hk⟩` from `Finset.dvd_prod_of_mem m ha`.

Establish `hfa' : (m a : AfP p) * f ∈ LevelExists.intAfP p` using `hfa`. Rewrite using `[hk, Nat.cast_mul, mul_comm ((m a : ℕ) : AfP p), mul_assoc]`. Conclude with `mul_mem (natCast_mem _ k) hfa'`.
-/
theorem exists_den (p : ℕ) (S : Set (AfP p)) (hS : IsCompact S) :
    ∃ D : ℕ, 0 < D ∧ ∀ a ∈ S, (D : AfP p) * a ∈ LevelExists.intAfP p := by
  choose m hm0 hm using fun a : AfP p => exists_nat_adele a
  obtain ⟨t, ht⟩ := hS.elim_finite_subcover
    (fun a => (fun x => (m a : AfP p) * x) ⁻¹' (LevelExists.intAfP p : Set (AfP p)))
    (fun a => (LevelExists.isOpen_intAfP p).preimage (continuous_const_mul _))
    (fun x _ => Set.mem_iUnion.mpr ⟨x, hm x⟩)
  refine ⟨∏ a ∈ t, m a, Finset.prod_pos (fun a _ => hm0 a), fun f hf => ?_⟩
  obtain ⟨a, ha, hfa⟩ := Set.mem_iUnion₂.mp (ht hf)
  obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem m ha
  have hfa' : (m a : AfP p) * f ∈ LevelExists.intAfP p := hfa
  rw [hk, Nat.cast_mul, mul_comm ((m a : ℕ) : AfP p), mul_assoc]
  exact mul_mem (natCast_mem _ k) hfa'

/- English proof (translation)
The claim follows from `exists_den`.
-/
theorem main : ∀ (p : ℕ) (S : Set (AfP p)), IsCompact S → ∃ D : ℕ, 0 < D ∧ ∀ a ∈ S, (D : AfP p) * a ∈ LevelExists.intAfP p :=
  exists_den

end GlobalTheory.AfPCpctDen
