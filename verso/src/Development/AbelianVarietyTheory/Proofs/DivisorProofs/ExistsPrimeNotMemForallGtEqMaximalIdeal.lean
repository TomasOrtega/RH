import Mathlib
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringLiftOfSpecialFibre

open IsLocalRing

namespace GlobalTheory

/- English proof (translation)
Establish `hnil : ¬ IsNilpotent x` using `fun h => hx (IsNilpotent.eq_zero h)`. Use `haveI : Nontrivial (Localization.Away x) := (IsLocalization.injective (Localization.Away x) (powers_le_nonZeroDivisors_of_noZeroDivisors hx)).nontrivial`. Take `⟨M, hM⟩` from `Ideal.exists_maximal (Localization.Away x)`. Use `set q : Ideal C := M.comap (algebraMap C (Localization.Away x)) with hqdef`. Establish `hMp : M.IsPrime` using `hM.isPrime`.

Establish `hqd` using `(IsLocalization.isPrime_iff_isPrime_disjoint (Submonoid.powers x) (Localization.Away x) M).mp hMp`. Establish `hqp : q.IsPrime` using `hqd.1`. Establish `hxq : x ∉ q` using `fun h => Set.disjoint_left.mp hqd.2 (Submonoid.mem_powers x) h`. Establish `habove : ∀ P : Ideal C, P.IsPrime → q < P → x ∈ P`. Introduce `P hP hlt`.

Assume the negation of the conclusion as `hxP`. Establish `hdisj : Disjoint (Submonoid.powers x : Set C) P`. Rewrite using `[Set.disjoint_left]`. Introduce and unpack `_ ⟨n, rfl⟩ h`. Conclude with `hxP (hP.mem_of_pow_mem n h)`.

Establish `hPL` using `IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers x) (Localization.Away x) P hP hdisj`. Establish `hcomap` using `IsLocalization.comap_map_of_isPrime_disjoint (Submonoid.powers x) (Localization.Away x) hP hdisj`. Establish `hMle : M ≤ P.map (algebraMap C (Localization.Away x))`. Rewrite using `[← IsLocalization.map_comap (Submonoid.powers x) (Localization.Away x) M]`. Conclude with `Ideal.map_mono hlt.le`.

Establish `heq` using `hM.eq_of_le hPL.ne_top hMle`. Establish `: q = P` using `by rw [hqdef, heq]; exact hcomap`. Conclude with `hlt.ne this`. Use `⟨q, hqp, hxq, fun P hP hlt => ?_⟩` and prove the remaining obligations. Use `set f := Ideal.Quotient.mk q with hfdef`.

Establish `hsurj : Function.Surjective f` using `Ideal.Quotient.mk_surjective`. Establish `hker : RingHom.ker f = q` using `Ideal.mk_ker`. Use `haveI : IsDomain (C ⧸ q) := Ideal.Quotient.isDomain q`. Use `set m' : Ideal (C ⧸ q) := (maximalIdeal C).map f with hm'`. Establish `hqm : q ≤ maximalIdeal C` using `le_maximalIdeal hqp.ne_top`.

Establish `hm'p : m'.IsPrime` using `Ideal.map_isPrime_of_surjective hsurj (hker.symm ▸ hqm)`. Establish `hx0 : f x ≠ 0`. Rewrite using `[Ne, Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `hxq`. Establish `hht : m'.height ≤ 1`.

Use `height_le_one_of_forall_mem m' hx0 ?_` and prove the remaining obligations. Introduce `p' hp' hp'0 _`. Establish `hcp : (p'.comap f).IsPrime` using `Ideal.comap_isPrime f p'`. Establish `hqc : q < p'.comap f`. Use `lt_of_le_of_ne ?_ ?_` and prove the remaining obligations.

Introduce `a ha`. Simplify using `[Ideal.mem_comap, hfdef, Ideal.Quotient.eq_zero_iff_mem.mpr ha]`. Introduce `e`. Apply `hp'0` to reduce the goal to its premises. Rewrite using `[← Ideal.map_comap_of_surjective f hsurj p', ← e]`.

Conclude with `(Ideal.map_eq_bot_iff_le_ker _).mpr hker.ge`. Conclude with `habove _ hcp hqc`. Establish `hPp' : (P.map f).IsPrime` using `Ideal.map_isPrime_of_surjective hsurj (hker.symm ▸ hlt.le)`. Establish `hP0 : P.map f ≠ ⊥`. Introduce `e`.

Rewrite `e` using `[Ideal.map_eq_bot_iff_le_ker, hker]`. Conclude with `hlt.ne (le_antisymm hlt.le e)`. Establish `hPm : P.map f ≤ m'` using `Ideal.map_mono (le_maximalIdeal hP.ne_top)`. Establish `hPeq : P.map f = m'`. Assume the negation of the conclusion as `hne`.

Establish `h1` using `Ideal.height_add_one_le_of_lt_of_isPrime (bot_lt_iff_ne_bot.mpr hP0)`. Establish `h2` using `Ideal.height_add_one_le_of_lt_of_isPrime (lt_of_le_of_ne hPm hne)`. Establish `h3 : (⊥ : Ideal (C ⧸ q)).height + 1 + 1 ≤ 1` using `(add_le_add h1 le_rfl).trans (h2.trans hht)`. Simplify using `at h3`. Conclude with `absurd h3 (by decide)`.

Establish `hPc : P = (P.map f).comap f`. Rewrite using `[Ideal.comap_map_of_surjective' f hsurj, hker, sup_eq_left.mpr hlt.le]`. Establish `hmc : maximalIdeal C = m'.comap f`. Rewrite using `[hm', Ideal.comap_map_of_surjective' f hsurj, hker, sup_eq_left.mpr hqm]`. Rewrite using `[hPc, hPeq, ← hmc]`.
-/
theorem exists_prime_not_mem_forall_gt_eq_maximalIdeal (C : Type) [CommRing C] [IsDomain C]
    [IsLocalRing C] [IsNoetherianRing C] (x : C) (hx : x ≠ 0) (hxm : x ∈ maximalIdeal C) :
    ∃ q : Ideal C, q.IsPrime ∧ x ∉ q ∧ ∀ P : Ideal C, P.IsPrime → q < P → P = maximalIdeal C := by
  classical

  have hnil : ¬ IsNilpotent x := fun h => hx (IsNilpotent.eq_zero h)
  haveI : Nontrivial (Localization.Away x) :=
    (IsLocalization.injective (Localization.Away x)
      (powers_le_nonZeroDivisors_of_noZeroDivisors hx)).nontrivial
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (Localization.Away x)
  set q : Ideal C := M.comap (algebraMap C (Localization.Away x)) with hqdef
  have hMp : M.IsPrime := hM.isPrime
  have hqd := (IsLocalization.isPrime_iff_isPrime_disjoint (Submonoid.powers x)
    (Localization.Away x) M).mp hMp
  have hqp : q.IsPrime := hqd.1
  have hxq : x ∉ q := fun h =>
    Set.disjoint_left.mp hqd.2 (Submonoid.mem_powers x) h

  have habove : ∀ P : Ideal C, P.IsPrime → q < P → x ∈ P := by
    intro P hP hlt
    by_contra hxP
    have hdisj : Disjoint (Submonoid.powers x : Set C) P := by
      rw [Set.disjoint_left]
      rintro _ ⟨n, rfl⟩ h
      exact hxP (hP.mem_of_pow_mem n h)
    have hPL := IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers x)
      (Localization.Away x) P hP hdisj
    have hcomap := IsLocalization.comap_map_of_isPrime_disjoint (Submonoid.powers x)
      (Localization.Away x) hP hdisj
    have hMle : M ≤ P.map (algebraMap C (Localization.Away x)) := by
      rw [← IsLocalization.map_comap (Submonoid.powers x) (Localization.Away x) M]
      exact Ideal.map_mono hlt.le
    have heq := hM.eq_of_le hPL.ne_top hMle
    have : q = P := by rw [hqdef, heq]; exact hcomap
    exact hlt.ne this
  refine ⟨q, hqp, hxq, fun P hP hlt => ?_⟩

  set f := Ideal.Quotient.mk q with hfdef
  have hsurj : Function.Surjective f := Ideal.Quotient.mk_surjective
  have hker : RingHom.ker f = q := Ideal.mk_ker
  haveI : IsDomain (C ⧸ q) := Ideal.Quotient.isDomain q
  set m' : Ideal (C ⧸ q) := (maximalIdeal C).map f with hm'
  have hqm : q ≤ maximalIdeal C := le_maximalIdeal hqp.ne_top
  have hm'p : m'.IsPrime := Ideal.map_isPrime_of_surjective hsurj (hker.symm ▸ hqm)
  have hx0 : f x ≠ 0 := by
    rw [Ne, Ideal.Quotient.eq_zero_iff_mem]; exact hxq
  have hht : m'.height ≤ 1 := by
    refine height_le_one_of_forall_mem m' hx0 ?_
    intro p' hp' hp'0 _
    have hcp : (p'.comap f).IsPrime := Ideal.comap_isPrime f p'
    have hqc : q < p'.comap f := by
      refine lt_of_le_of_ne ?_ ?_
      · intro a ha
        simp [Ideal.mem_comap, hfdef, Ideal.Quotient.eq_zero_iff_mem.mpr ha]
      · intro e
        apply hp'0
        rw [← Ideal.map_comap_of_surjective f hsurj p', ← e]
        exact (Ideal.map_eq_bot_iff_le_ker _).mpr hker.ge
    exact habove _ hcp hqc
  have hPp' : (P.map f).IsPrime := Ideal.map_isPrime_of_surjective hsurj (hker.symm ▸ hlt.le)
  have hP0 : P.map f ≠ ⊥ := by
    intro e
    rw [Ideal.map_eq_bot_iff_le_ker, hker] at e
    exact hlt.ne (le_antisymm hlt.le e)
  have hPm : P.map f ≤ m' := Ideal.map_mono (le_maximalIdeal hP.ne_top)
  have hPeq : P.map f = m' := by
    by_contra hne
    have h1 := Ideal.height_add_one_le_of_lt_of_isPrime (bot_lt_iff_ne_bot.mpr hP0)
    have h2 := Ideal.height_add_one_le_of_lt_of_isPrime (lt_of_le_of_ne hPm hne)
    have h3 : (⊥ : Ideal (C ⧸ q)).height + 1 + 1 ≤ 1 := (add_le_add h1 le_rfl).trans (h2.trans hht)
    simp at h3
    exact absurd h3 (by decide)
  have hPc : P = (P.map f).comap f := by
    rw [Ideal.comap_map_of_surjective' f hsurj, hker, sup_eq_left.mpr hlt.le]
  have hmc : maximalIdeal C = m'.comap f := by
    rw [hm', Ideal.comap_map_of_surjective' f hsurj, hker, sup_eq_left.mpr hqm]
  rw [hPc, hPeq, ← hmc]

end GlobalTheory
