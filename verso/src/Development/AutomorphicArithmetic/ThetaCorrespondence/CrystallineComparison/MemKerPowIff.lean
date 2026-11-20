import Development.AutomorphicArithmetic.ThetaCorrespondence.CrystallineComparison.CFDefs
import Development.WeilBound.CoreStatements.PeriodRingComparison.RationalRingEquivalences.IsLogCore

noncomputable section

namespace Formalism.BasicNotions.CmpTie.LogF

open Reformulated.AutPerF

variable (l : ℕ) [Fact l.Prime]

abbrev B : Type := BdRPlus l (Cmp6.OC l)

/- English proof (translation)
Rewrite using `[BdRPlus.ker_thetaC, ← RingHom.mem_ker, BdRPlus.ker_eval]`. Both sides reduce to the same expression.
-/
theorem mem_ker_pow_iff (x : B l) (n : ℕ) :
    x ∈ RingHom.ker (BdRPlus.thetaC l (PadicComplexInt l)) ^ n ↔ BdRPlus.eval l (Cmp6.OC l) n x = 0 := by
  rw [BdRPlus.ker_thetaC, ← RingHom.mem_ker, BdRPlus.ker_eval]
  rfl

/- English proof (translation)
Unfold `truncLog`. Rewrite using `[Finset.sum_Ico_eq_sum_range]`. Simplify using `only [Nat.add_sub_cancel]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[Algebra.smul_def]`.

Use `congr 2`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Expand and normalize the polynomial expressions, which then agree.
-/
theorem truncLog_eq (N : ℕ) (x : AinfInv l (Cmp6.OC l) ⧸ AinfInv.kerTheta l (Cmp6.OC l) ^ N) :
    truncLog N x = ∑ i ∈ Finset.Ico 1 (N + 1), algebraMap ℚ _ ((-1) ^ (i + 1) / i) * x ^ i := by
  unfold truncLog
  rw [Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Algebra.smul_def]
  congr 2
  · push_cast
    ring
  · ring

abbrev u (ε : PreTilt ↥(PadicComplexInt l) l) : B l :=
  algebraMap (Ainf l (Cmp6.OC l)) (B l) (WittVector.teichmuller l ε)

abbrev sA (ε : PreTilt ↥(PadicComplexInt l) l) (n : ℕ) : B l :=
  ∑ i ∈ Finset.Ico 1 n, algebraMap ℚ (B l) ((-1) ^ (i + 1) / i) * (u l ε - 1) ^ i

/- English proof (translation)
Establish `hk : u l ε - 1 ∈ RingHom.ker (BdRPlus.thetaC l (PadicComplexInt l))`. Rewrite using `[BdRPlus.ker_thetaC, RingHom.mem_ker, map_sub, h, map_one, sub_self]`. Establish `hX : BdRPlus.eval l (Cmp6.OC l) n ((u l ε - 1) ^ n) = 0` using `(mem_ker_pow_iff l _ n).1 (Ideal.pow_mem_pow hk n)`. Rewrite using `[mem_ker_pow_iff, map_sub, BdRPlus.eval_log, truncLog_eq, map_sum]`. Simplify using `only [map_mul, map_pow, RingHom.map_rat_algebraMap]`.

Break down `Nat.eq_zero_or_pos n with rfl | hn` into its components or cases. Simplify using the standard rewrite rules. Rewrite using `[Finset.sum_Ico_succ_top hn, add_sub_cancel_left, ← map_pow, hX, mul_zero]`.
-/
theorem log_sub_mem (ε : PreTilt ↥(PadicComplexInt l) l) (h : BdRPlus.theta l (Cmp6.OC l) (u l ε) = 1) (n : ℕ) :
    BdRPlus.log (u l ε) h - sA l ε n ∈ RingHom.ker (BdRPlus.thetaC l (PadicComplexInt l)) ^ n := by
  have hk : u l ε - 1 ∈ RingHom.ker (BdRPlus.thetaC l (PadicComplexInt l)) := by
    rw [BdRPlus.ker_thetaC, RingHom.mem_ker, map_sub, h, map_one, sub_self]
  have hX : BdRPlus.eval l (Cmp6.OC l) n ((u l ε - 1) ^ n) = 0 :=
    (mem_ker_pow_iff l _ n).1 (Ideal.pow_mem_pow hk n)
  rw [mem_ker_pow_iff, map_sub, BdRPlus.eval_log, truncLog_eq, map_sum]
  simp only [map_mul, map_pow, RingHom.map_rat_algebraMap]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [Finset.sum_Ico_succ_top hn, add_sub_cancel_left, ← map_pow, hX, mul_zero]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h, rfl⟩ n`. Conclude with `log_sub_mem l ε h n`. Introduce `hy`. Establish `h1` using `hy 1`.

Establish `h2` using `hy 2`. Establish `hu : BdRPlus.theta l (Cmp6.OC l) (u l ε) = 1`. Establish `h3` using `sub_mem (by simpa using h1) (Ideal.pow_le_self two_ne_zero h2)`. Establish `h4 : u l ε - 1 ∈ RingHom.ker (BdRPlus.theta l (Cmp6.OC l))`. Rewrite using `[← BdRPlus.ker_thetaC]`.

Simplify using `using h3`. Rewrite `h4` using `[RingHom.mem_ker, map_sub, map_one, sub_eq_zero]`. Conclude with `h4`. Use `⟨hu, ?_⟩` and prove the remaining obligations. Apply `BdRPlus.ext_eval` to reduce the goal to its premises.

Introduce `n`. Establish `h5` using `sub_mem (hy n) (log_sub_mem l ε hu n)`. Rewrite `h5` using `[sub_sub_sub_cancel_right, mem_ker_pow_iff, map_sub, sub_eq_zero]`. Conclude with `h5`.
-/
theorem isLog_iff (ε : PreTilt ↥(PadicComplexInt l) l) (y : B l) :
    (∃ h : BdRPlus.theta l (Cmp6.OC l) (u l ε) = 1, y = BdRPlus.log (u l ε) h) ↔ Cmp6.IsLogA l ε y := by
  constructor
  · rintro ⟨h, rfl⟩ n
    exact log_sub_mem l ε h n
  · intro hy
    have h1 := hy 1
    have h2 := hy 2
    have hu : BdRPlus.theta l (Cmp6.OC l) (u l ε) = 1 := by
      have h3 := sub_mem (by simpa using h1) (Ideal.pow_le_self two_ne_zero h2)
      have h4 : u l ε - 1 ∈ RingHom.ker (BdRPlus.theta l (Cmp6.OC l)) := by
        rw [← BdRPlus.ker_thetaC]
        simpa using h3
      rw [RingHom.mem_ker, map_sub, map_one, sub_eq_zero] at h4
      exact h4
    refine ⟨hu, ?_⟩
    apply BdRPlus.ext_eval
    intro n
    have h5 := sub_mem (hy n) (log_sub_mem l ε hu n)
    rw [sub_sub_sub_cancel_right, mem_ker_pow_iff, map_sub, sub_eq_zero] at h5
    exact h5

end Formalism.BasicNotions.CmpTie.LogF
