import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSumSmulSeparatingInertia
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

namespace GlobalTheory

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct Pointwise in

/- English proof (translation)
Introduce `Γ _ _ B _ _ htame`. Use `haveI := Fintype.ofFinite Γ`. Set `A` to `FixedPoints.subring B Γ`. Use `haveI : Algebra.IsInvariant A B Γ := ⟨fun b hb => ⟨⟨b, hb⟩, rfl⟩⟩`. Use `haveI := Algebra.IsInvariant.isIntegral A B Γ`.

Establish `tr_inv : ∀ b : B, ∑ g : Γ, g • b ∈ A`. Introduce `b h`. Rewrite using `[Finset.smul_sum]`. Repeatedly rewrite using `[← mul_smul]`. Conclude with `Equiv.sum_comp (Equiv.mulLeft h) (fun g => g • b)`.

Set `T : Ideal A` to `Ideal.span {t | ∃ b : B, (t : B) = ∑ g : Γ, g • b}`. Establish `hT : ∀ t ∈ T, ∃ b : B, (t : B) = ∑ g : Γ, g • b`. Introduce `t ht`. Proceed by induction on `ht using Submodule.span_induction with`. Consider the case `mem t ht => exact ht`.

Consider the case `zero => exact ⟨0, by simp⟩`. Consider the case `add t u _ _ htb hub`. Take `⟨b, hb⟩` from `htb`. Take `⟨c, hc⟩` from `hub`. Conclude with `⟨b + c, by simp [hb, hc, Finset.sum_add_distrib]⟩`.

Consider the case `smul a t _ htb`. Take `⟨b, hb⟩` from `htb`. Use `⟨(a : B) * b, ?_⟩` and prove the remaining obligations. Simplify using `only [smul_eq_mul, Subring.coe_mul, hb, Finset.mul_sum, smul_mul']`. Use `Finset.sum_congr rfl fun g _ => ?_` and prove the remaining obligations.

Rewrite using `[a.2 g]`. It suffices to establish `h1 : (1 : A) ∈ T by`. Take `⟨b, hb⟩` from `hT 1 h1`. Conclude with `⟨b, by rw [finsum_eq_sum_of_fintype, ← hb]; rfl⟩`. Assume the negation of the conclusion as `h1`.

Take `⟨m, hm, hTm⟩` from `Ideal.exists_le_maximal T ((Ideal.ne_top_iff_one T).mpr h1)`. Establish `hker : RingHom.ker (algebraMap A B) ≤ m`. Introduce `z hz`. Establish `: z = 0` using `Subtype.ext hz`. Rewrite using `[this]`.

Conclude with `m.zero_mem`. Take `⟨Q, hQ, hQm⟩` from `Ideal.exists_ideal_over_maximal_of_isIntegral m hker`. Take `⟨n, c, d, s, hs, hsep⟩` from `_root_.GlobalTheory.exists_sum_smul_separating_inertia Γ B Q hQ.isPrime`. Establish `trace_mem : ∀ j, ∑ g : Γ, g • c j ∈ Q`. Introduce `j`.

Establish `hmemT : (⟨∑ g : Γ, g • c j, tr_inv (c j)⟩ : A) ∈ T` using `Ideal.subset_span ⟨c j, rfl⟩`. Use `hTm hmemT` as an intermediate fact. Rewrite `this` using `[← hQm, Ideal.mem_comap]`. Conclude with `this`. Establish `hz : ∑ g : Γ, ∑ j, d j * g • c j ∈ Q`.

Rewrite using `[Finset.sum_comm]`. Conclude with `Q.sum_mem fun j _ => by`. Rewrite using `[← Finset.mul_sum]`. Conclude with `Q.mul_mem_left _ (trace_mem j)`. Establish `hdiff : ∑ g : Γ, (∑ j, d j * g • c j - if g ∈ Q.inertia Γ then s else 0) ∈ Q`.

Use `Q.sum_mem fun g _ => ?_` and prove the remaining obligations. Use `split_ifs with hg`. Conclude with `(hsep g).1 hg`. Simplify using `using (hsep g).2 hg`. Rewrite `hdiff` using `[Finset.sum_sub_distrib, Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]`.

Establish `hcs` using `Q.sub_mem hz hdiff`. Rewrite `hcs` using `[sub_sub_cancel]`. Break down `hQ.isPrime.mem_or_mem hcs with hc | hc` into its components or cases. Apply `htame Q hQ.isPrime` to reduce the goal to its premises. Use `hc using 2` and compare the differences between its conclusion and the goal.

Rewrite using `[Nat.card_eq_fintype_card, Fintype.card_subtype]`. Conclude with `hs hc`.
-/
theorem _root_.GlobalTheory.exists_finsum_smul_eq_one_of_tame :
    ∀ (Γ : Type) [Group Γ] [Finite Γ] (B : Type) [CommRing B] [MulSemiringAction Γ B],
      (∀ q : Ideal B, q.IsPrime → (Nat.card (q.inertia Γ) : B) ∉ q) →
        ∃ b : B, ∑ᶠ g : Γ, g • b = 1 := by
  intro Γ _ _ B _ _ htame
  classical
  haveI := Fintype.ofFinite Γ
  let A := FixedPoints.subring B Γ
  haveI : Algebra.IsInvariant A B Γ := ⟨fun b hb => ⟨⟨b, hb⟩, rfl⟩⟩
  haveI := Algebra.IsInvariant.isIntegral A B Γ
  have tr_inv : ∀ b : B, ∑ g : Γ, g • b ∈ A := by
    intro b h
    rw [Finset.smul_sum]
    simp_rw [← mul_smul]
    exact Equiv.sum_comp (Equiv.mulLeft h) (fun g => g • b)
  let T : Ideal A := Ideal.span {t | ∃ b : B, (t : B) = ∑ g : Γ, g • b}
  have hT : ∀ t ∈ T, ∃ b : B, (t : B) = ∑ g : Γ, g • b := by
    intro t ht
    induction ht using Submodule.span_induction with
    | mem t ht => exact ht
    | zero => exact ⟨0, by simp⟩
    | add t u _ _ htb hub =>
      obtain ⟨b, hb⟩ := htb
      obtain ⟨c, hc⟩ := hub
      exact ⟨b + c, by simp [hb, hc, Finset.sum_add_distrib]⟩
    | smul a t _ htb =>
      obtain ⟨b, hb⟩ := htb
      refine ⟨(a : B) * b, ?_⟩
      simp only [smul_eq_mul, Subring.coe_mul, hb, Finset.mul_sum, smul_mul']
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [a.2 g]
  suffices h1 : (1 : A) ∈ T by
    obtain ⟨b, hb⟩ := hT 1 h1
    exact ⟨b, by rw [finsum_eq_sum_of_fintype, ← hb]; rfl⟩
  by_contra h1
  obtain ⟨m, hm, hTm⟩ := Ideal.exists_le_maximal T ((Ideal.ne_top_iff_one T).mpr h1)
  have hker : RingHom.ker (algebraMap A B) ≤ m := by
    intro z hz
    have : z = 0 := Subtype.ext hz
    rw [this]
    exact m.zero_mem
  obtain ⟨Q, hQ, hQm⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral m hker
  obtain ⟨n, c, d, s, hs, hsep⟩ := _root_.GlobalTheory.exists_sum_smul_separating_inertia Γ B Q hQ.isPrime
  have trace_mem : ∀ j, ∑ g : Γ, g • c j ∈ Q := by
    intro j
    have hmemT : (⟨∑ g : Γ, g • c j, tr_inv (c j)⟩ : A) ∈ T :=
      Ideal.subset_span ⟨c j, rfl⟩
    have := hTm hmemT
    rw [← hQm, Ideal.mem_comap] at this
    exact this
  have hz : ∑ g : Γ, ∑ j, d j * g • c j ∈ Q := by
    rw [Finset.sum_comm]
    exact Q.sum_mem fun j _ => by
      rw [← Finset.mul_sum]
      exact Q.mul_mem_left _ (trace_mem j)
  have hdiff : ∑ g : Γ, (∑ j, d j * g • c j - if g ∈ Q.inertia Γ then s else 0) ∈ Q := by
    refine Q.sum_mem fun g _ => ?_
    split_ifs with hg
    · exact (hsep g).1 hg
    · simpa using (hsep g).2 hg
  rw [Finset.sum_sub_distrib, Finset.sum_ite, Finset.sum_const_zero, add_zero,
    Finset.sum_const, nsmul_eq_mul] at hdiff
  have hcs := Q.sub_mem hz hdiff
  rw [sub_sub_cancel] at hcs
  rcases hQ.isPrime.mem_or_mem hcs with hc | hc
  · apply htame Q hQ.isPrime
    convert hc using 2
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  · exact hs hc

end GlobalTheory
