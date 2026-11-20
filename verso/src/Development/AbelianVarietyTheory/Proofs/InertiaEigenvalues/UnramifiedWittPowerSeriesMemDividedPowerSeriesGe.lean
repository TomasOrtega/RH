import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NatCastNeZeroPs

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per

namespace GlobalTheory.CrysPrism

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Establish an intermediate fact. Establish an intermediate fact.

Use linear arithmetic over natural numbers and integers. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Use linear arithmetic over natural numbers and integers.
-/
theorem pow_dvd_factorial_mul (l r : ℕ) (hl : 1 ≤ l) : l ^ r ∣ (l * r).factorial := by
  induction r with
  | zero => simp
  | succ r ih =>
    have h1 : l * (r + 1) = (l * (r + 1) - 1) + 1 := by
      have : 1 ≤ l * (r + 1) := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
      omega
    rw [h1, Nat.factorial_succ, ← h1, pow_succ, mul_comm (l ^ r) l]
    refine Nat.mul_dvd_mul (Dvd.intro (r + 1) rfl) (ih.trans (Nat.factorial_dvd_factorial ?_))
    rw [Nat.mul_succ]; omega

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Simplify using the standard rewrite rules. Assume the negation of the conclusion and derive a contradiction. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Move the embeddings inside the algebraic operations. Both sides reduce to the same expression. Rewrite the conclusion using the stated equalities.
-/
theorem inclS_mem_SdSet (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O]
    [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K]
    [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (x : (Wq l a)⟦X⟧) :
    inclS t K x ∈ SdSet t K e := by
  have hl1 : 1 ≤ l := (Fact.out : l.Prime).one_lt.le
  have he : 0 < e := Nat.pos_of_ne_zero (NeZero.ne e)
  refine ⟨fun n => ((n / e).factorial : Wq l a) * coeff n x, fun r => ?_, fun τ n => ?_⟩
  · rw [Filter.eventually_cofinite]
    refine (Set.finite_lt_nat (e * (l * r))).subset fun n hn => ?_
    simp only [Set.mem_setOf_eq] at hn ⊢
    by_contra hlt
    apply hn
    have hle : l * r ≤ n / e := (Nat.le_div_iff_mul_le he).2 (by rw [mul_comm]; omega)
    obtain ⟨k, hk⟩ := (pow_dvd_factorial_mul l r hl1).trans (Nat.factorial_dvd_factorial hle)
    refine Dvd.dvd.mul_right ⟨(k : Wq l a), ?_⟩ _
    rw [hk]; push_cast; rfl
  · rw [inclS_apply, coeff_toAc, map_mul, map_natCast, map_mul, map_natCast]

end GlobalTheory.CrysPrism
