import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocFacts

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc Formalism.L2.SG.TermDef GlobalTheory.LocOver
open scoped Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocOver

open Formalism.L2.SG.Pf Formalism.L2.SG.Pf.BBTie

/- English proof (translation)
Establish `halg : IsAlgebraic ℤ x` using `(IsFractionRing.isAlgebraic_iff ℤ ℚ D.host.E).2 (Algebra.IsAlgebraic.isAlgebraic x)`. Take `⟨y, hy0, hint⟩` from `halg.exists_integral_multiple`. Take `⟨n, hn⟩ : ∃ n : ℕ, n = y.natAbs` from `⟨_, rfl⟩`. Establish `hn0 : n ≠ 0` using `by rw [hn]; exact Int.natAbs_ne_zero.2 hy0`. Establish `hint' : IsIntegral ℤ ((n : D.host.E) * x)`.

Apply the tactic sequence `rcases Int.natAbs_eq y with h | h <;> rw [← hn] at h`. Establish `e : y • x = (n : D.host.E) * x`. Rewrite using `[zsmul_eq_mul, h, Int.cast_natCast]`. Rewrite using `[← e]`. Conclude with `hint`.

Establish `e : y • x = -((n : D.host.E) * x)`. Rewrite using `[zsmul_eq_mul, h, Int.cast_neg, Int.cast_natCast, neg_mul]`. Use `hint.neg` as an intermediate fact. Rewrite `this` using `[e, neg_neg]`. Conclude with `this`.

Set `w : 𝓞 D.host.E` to `⟨(n : D.host.E) * x, hint'⟩`. Establish `hfin : {p : PlF D | Loc.resChar p ∣ n}.Finite`. Establish `hne : (Ideal.span {((n : ℕ) : 𝓞 D.host.F)} : Ideal (𝓞 D.host.F)) ≠ 0`. Rewrite using `[Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]`. Conclude with `hn0` after adjusting the coercions.

Use `(Ideal.finite_factors hne).subset ?_` and prove the remaining obligations. Introduce `p hp`. Simplify using `only [Set.mem_setOf_eq] at hp ⊢`. Rewrite using `[Ideal.dvd_span_singleton, bt_natCast_mem_iff]`. Conclude with `hp`.

Use `hfin.subset ?_` and prove the remaining obligations. Introduce `p hp`. Simplify using `only [Set.mem_setOf_eq] at hp ⊢`. Assume the negation of the conclusion as `hnd`. Apply `hp` to reduce the goal to its premises.

Take `⟨_, w', hw'O, hw'⟩` from `bt_nat_unit Z p n hnd`. Establish `hwO` using `bt_iota_int Z p w`. Establish `e : (D.s.atP p).ιE x = w' * (D.s.atP p).ιE (w : D.host.E)` using `by show _ = w' * (D.s.atP p).ιE ((n : D.host.E) * x)`. Rewrite using `[map_mul, map_natCast, ← mul_assoc, hw', one_mul]`. Rewrite using `[e]`.

Conclude with `Subring.mul_mem _ hw'O hwO`.
-/
theorem iota_int_cofinite {D : D7} (Z : LocDat D) (x : D.host.E) :
    {p : PlF D | (D.s.atP p).ιE x ∉ (Z.M p).L.O}.Finite := by
  have halg : IsAlgebraic ℤ x :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ D.host.E).2 (Algebra.IsAlgebraic.isAlgebraic x)
  obtain ⟨y, hy0, hint⟩ := halg.exists_integral_multiple
  obtain ⟨n, hn⟩ : ∃ n : ℕ, n = y.natAbs := ⟨_, rfl⟩
  have hn0 : n ≠ 0 := by rw [hn]; exact Int.natAbs_ne_zero.2 hy0
  have hint' : IsIntegral ℤ ((n : D.host.E) * x) := by
    rcases Int.natAbs_eq y with h | h <;> rw [← hn] at h
    · have e : y • x = (n : D.host.E) * x := by
        rw [zsmul_eq_mul, h, Int.cast_natCast]
      rw [← e]; exact hint
    · have e : y • x = -((n : D.host.E) * x) := by
        rw [zsmul_eq_mul, h, Int.cast_neg, Int.cast_natCast, neg_mul]
      have := hint.neg
      rw [e, neg_neg] at this
      exact this
  let w : 𝓞 D.host.E := ⟨(n : D.host.E) * x, hint'⟩
  have hfin : {p : PlF D | Loc.resChar p ∣ n}.Finite := by
    have hne : (Ideal.span {((n : ℕ) : 𝓞 D.host.F)} : Ideal (𝓞 D.host.F)) ≠ 0 := by
      rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
      exact_mod_cast hn0
    refine (Ideal.finite_factors hne).subset ?_
    intro p hp
    simp only [Set.mem_setOf_eq] at hp ⊢
    rw [Ideal.dvd_span_singleton, bt_natCast_mem_iff]
    exact hp
  refine hfin.subset ?_
  intro p hp
  simp only [Set.mem_setOf_eq] at hp ⊢
  by_contra hnd
  apply hp
  obtain ⟨_, w', hw'O, hw'⟩ := bt_nat_unit Z p n hnd
  have hwO := bt_iota_int Z p w
  have e : (D.s.atP p).ιE x = w' * (D.s.atP p).ιE (w : D.host.E) := by
    show _ = w' * (D.s.atP p).ιE ((n : D.host.E) * x)
    rw [map_mul, map_natCast, ← mul_assoc, hw', one_mul]
  rw [e]
  exact Subring.mul_mem _ hw'O hwO

/- English proof (translation)
Introduce `D Z f g A hA hg`. Use `⟨fun p a b => Ring.inverse (frFac Z.δ p a) * frFac Z.δ p b * (D.s.atP p).ιE (A a b), ?_, ?_⟩` and prove the remaining obligations. Introduce `p`. Use `⟨⟨fun a b hab => ?_, fun a => ?_⟩, fun b => ?_⟩` and prove the remaining obligations. Simplify using `[hA.1 a b hab]`.

Use `show Ring.inverse (frFac Z.δ p a) * frFac Z.δ p a * (D.s.atP p).ιE (A a a) = 1`. Rewrite using `[hA.2 a, map_one, mul_one, Ring.inverse_mul_cancel _ (bt_frFac_unit Z p a)]`. Simplify using `only [scaled]`. Rewrite using `[hg b, map_sum, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations.

Rewrite using `[baseChange_smul₂, smul_smul, smul_smul]`. Use `congr 1`. Establish `h` using `Ring.inverse_mul_cancel _ (bt_frFac_unit Z p a)`. Take the linear combination `(-(frFac Z.δ p b * (D.s.atP p).ιE (A a b))) * h`. Establish `hD` using `locDiffC_holds D Z`.

Use `(Set.Finite.biUnion (Set.finite_univ (α := Fin (D.R.rS + 1) × Fin (D.R.rS + 1))) (fun ab _ => iota_int_cofinite Z (A ab.1 ab.2))).subset ?_` and prove the remaining obligations. Introduce `p hp`. Simplify using `only [Set.mem_setOf_eq, not_forall] at hp`. Take `⟨a, b, hab⟩` from `hp`. Simplify using `only [Set.mem_iUnion, Set.mem_setOf_eq, Set.mem_univ, exists_true_left]`.

Use `⟨(a, b), ?_⟩` and prove the remaining obligations. Introduce `hι`. Apply `hab` to reduce the goal to its premises. Break down `lt_or_ge b a with h | h` into its components or cases. Simplify using `[hA.1 a b h]`.

Take `⟨k, hk, hkb⟩` from `bt_frFac_step Z p hD a b h`. Establish `e : Ring.inverse (frFac Z.δ p a) * frFac Z.δ p b * (D.s.atP p).ιE (A a b) = k * (D.s.atP p).ιE (A a b)`. Rewrite using `[hkb, mul_comm k, ← mul_assoc, Ring.inverse_mul_cancel _ (bt_frFac_unit Z p a), one_mul]`. Rewrite using `[e]`. Conclude with `Subring.mul_mem _ hk hι`.
-/
theorem tri_scaled : ∀ (D : D7) (Z : LocDat D), ∀ (f g : Fin (D.R.rS + 1) → (VS D).V)
    (A : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E), Uni A → Chg f A g →
    ∃ Ap : ∀ p : PlF D, Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep,
      (∀ p, Uni (Ap p) ∧ Chg (scaled Z p f) (Ap p) (scaled Z p g)) ∧
      {p : PlF D | ¬ ∀ a b, Ap p a b ∈ (Z.M p).L.O}.Finite := by
  intro D Z f g A hA hg
  refine ⟨fun p a b => Ring.inverse (frFac Z.δ p a) * frFac Z.δ p b * (D.s.atP p).ιE (A a b), ?_, ?_⟩
  · intro p
    refine ⟨⟨fun a b hab => ?_, fun a => ?_⟩, fun b => ?_⟩
    · simp [hA.1 a b hab]
    · show Ring.inverse (frFac Z.δ p a) * frFac Z.δ p a * (D.s.atP p).ιE (A a a) = 1
      rw [hA.2 a, map_one, mul_one, Ring.inverse_mul_cancel _ (bt_frFac_unit Z p a)]
    · simp only [scaled]
      rw [hg b, map_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [baseChange_smul₂, smul_smul, smul_smul]
      congr 1
      have h := Ring.inverse_mul_cancel _ (bt_frFac_unit Z p a)
      linear_combination (-(frFac Z.δ p b * (D.s.atP p).ιE (A a b))) * h
  · have hD := locDiffC_holds D Z
    refine (Set.Finite.biUnion (Set.finite_univ (α := Fin (D.R.rS + 1) × Fin (D.R.rS + 1)))
      (fun ab _ => iota_int_cofinite Z (A ab.1 ab.2))).subset ?_
    intro p hp
    simp only [Set.mem_setOf_eq, not_forall] at hp
    obtain ⟨a, b, hab⟩ := hp
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, Set.mem_univ, exists_true_left]
    refine ⟨(a, b), ?_⟩
    intro hι
    apply hab
    rcases lt_or_ge b a with h | h
    · simp [hA.1 a b h]
    · obtain ⟨k, hk, hkb⟩ := bt_frFac_step Z p hD a b h
      have e : Ring.inverse (frFac Z.δ p a) * frFac Z.δ p b * (D.s.atP p).ιE (A a b) =
          k * (D.s.atP p).ιE (A a b) := by
        rw [hkb, mul_comm k, ← mul_assoc, Ring.inverse_mul_cancel _ (bt_frFac_unit Z p a), one_mul]
      rw [e]
      exact Subring.mul_mem _ hk hι

end GlobalTheory.LocOver
