import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.IsClassFieldHilbert
import Mathlib.GroupTheory.Nilpotent
import Mathlib.GroupTheory.Sylow

open NumberField IsDedekindDomain IntermediateField UpperTheory.V.Kum UpperTheory.V.CF
open scoped Pointwise

/- English proof (translation)
Introduce `p _ P _ _ hP K hK`. Establish `hnil : Group.IsNilpotent P` using `hP.isNilpotent`. Establish `hN : K.Normal` using `Subgroup.NormalizerCondition.normal_of_coatom K normalizerCondition_of_isNilpotent hK`. Use `⟨hN, ?_⟩` and prove the remaining obligations. Establish `hQp : IsPGroup p (P ⧸ K)` using `hP.to_quotient K`.

Establish `hne : Nontrivial (P ⧸ K)`. Rewrite using `[QuotientGroup.nontrivial_iff]`. Conclude with `hK.1`. Establish `hdvd : p ∣ Nat.card (P ⧸ K)`. Take `⟨n, hn⟩` from `IsPGroup.iff_card.mp hQp`.

Establish `h1 : 1 < Nat.card (P ⧸ K)` using `Finite.one_lt_card`. Break down `n with _ | n` into its components or cases. Rewrite `h1` using `[hn, pow_zero]`. Conclude with `absurd h1 (lt_irrefl 1)`. Rewrite using `[hn, pow_succ]`.

Conclude with `dvd_mul_left _ _`. Take `⟨x, hx⟩` from `exists_prime_orderOf_dvd_card' (G := P ⧸ K) p hdvd`. Establish `htop : Subgroup.zpowers x = ⊤`. Establish `h1 : K ≤ (Subgroup.zpowers x).comap (QuotientGroup.mk' K)`. Introduce `k hk`.

Rewrite using `[Subgroup.mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff k).mpr hk]`. Conclude with `one_mem _`. Break down `hK.le_iff.mp h1 with h | h` into its components or cases. Rewrite using `[eq_top_iff]`. Introduce `y _`.

Take `⟨g, rfl⟩` from `QuotientGroup.mk_surjective y`. Establish `: g ∈ (Subgroup.zpowers x).comap (QuotientGroup.mk' K)`. Rewrite using `[h]`. Conclude with `Subgroup.mem_top g`. Conclude with `this`.

It suffices to derive a contradiction. Take `⟨g, rfl⟩` from `QuotientGroup.mk_surjective x`. Establish `: g ∈ (Subgroup.zpowers ((g : P ⧸ K))).comap (QuotientGroup.mk' K)` using `Subgroup.mem_zpowers _`. Rewrite `this` using `[h]`. Rewrite `hx` using `[(QuotientGroup.eq_one_iff g).mpr this, orderOf_one]`.

Conclude with `(Fact.out : p.Prime).one_lt.ne hx`. Establish `hcard : Nat.card (P ⧸ K) = p`. Rewrite using `[← Subgroup.card_top, ← htop, Nat.card_zpowers, hx]`. Establish `hidx : K.index = p`. Rewrite using `[Subgroup.index, hcard]`.

Use `⟨hidx, ?_⟩` and prove the remaining obligations. Establish `hcomm : ∀ a b : P ⧸ K, a * b = b * a`. Introduce `a b`. Establish `ha : a ∈ Subgroup.zpowers x` using `htop ▸ Subgroup.mem_top a`. Establish `hb : b ∈ Subgroup.zpowers x` using `htop ▸ Subgroup.mem_top b`.

Take `⟨m, rfl⟩` from `Subgroup.mem_zpowers_iff.mp ha`. Take `⟨n, rfl⟩` from `Subgroup.mem_zpowers_iff.mp hb`. Conclude with `(Commute.zpow_zpow_self x m n).eq`. Use `sup_le ?_ ?_` and prove the remaining obligations. Rewrite using `[Subgroup.closure_le]`.

Introduce and unpack `_ ⟨g, rfl⟩`. Use `show g ^ p ∈ K`. Rewrite using `[← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, ← hcard]`. Conclude with `pow_card_eq_one'`. Rewrite using `[commutator, Subgroup.commutator_le]`.

Introduce `a _ b _`. Rewrite using `[← QuotientGroup.eq_one_iff, commutatorElement_def, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_inv, hcomm (a : P ⧸ K) (b : P ⧸ K), mul_assoc, mul_assoc, mul_inv_cancel_left, mul_inv_cancel]`.
-/
theorem UpperTheory.V.CF.phiLe :
    ∀ (p : ℕ) [Fact p.Prime] (P : Type) [Group P] [Finite P], IsPGroup p P → ∀ K : Subgroup P, IsCoatom K → K.Normal ∧ K.index = p ∧ phi p P ≤ K := by
  intro p _ P _ _ hP K hK
  have hnil : Group.IsNilpotent P := hP.isNilpotent
  have hN : K.Normal :=
    Subgroup.NormalizerCondition.normal_of_coatom K normalizerCondition_of_isNilpotent hK
  refine ⟨hN, ?_⟩
  have hQp : IsPGroup p (P ⧸ K) := hP.to_quotient K
  have hne : Nontrivial (P ⧸ K) := by
    rw [QuotientGroup.nontrivial_iff]
    exact hK.1
  have hdvd : p ∣ Nat.card (P ⧸ K) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hQp
    have h1 : 1 < Nat.card (P ⧸ K) := Finite.one_lt_card
    rcases n with _ | n
    · rw [hn, pow_zero] at h1
      exact absurd h1 (lt_irrefl 1)
    · rw [hn, pow_succ]
      exact dvd_mul_left _ _
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := P ⧸ K) p hdvd
  have htop : Subgroup.zpowers x = ⊤ := by
    have h1 : K ≤ (Subgroup.zpowers x).comap (QuotientGroup.mk' K) := by
      intro k hk
      rw [Subgroup.mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff k).mpr hk]
      exact one_mem _
    rcases hK.le_iff.mp h1 with h | h
    · rw [eq_top_iff]
      intro y _
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
      have : g ∈ (Subgroup.zpowers x).comap (QuotientGroup.mk' K) := by
        rw [h]
        exact Subgroup.mem_top g
      exact this
    · exfalso
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
      have : g ∈ (Subgroup.zpowers ((g : P ⧸ K))).comap (QuotientGroup.mk' K) :=
        Subgroup.mem_zpowers _
      rw [h] at this
      rw [(QuotientGroup.eq_one_iff g).mpr this, orderOf_one] at hx
      exact (Fact.out : p.Prime).one_lt.ne hx
  have hcard : Nat.card (P ⧸ K) = p := by
    rw [← Subgroup.card_top, ← htop, Nat.card_zpowers, hx]
  have hidx : K.index = p := by
    rw [Subgroup.index, hcard]
  refine ⟨hidx, ?_⟩
  have hcomm : ∀ a b : P ⧸ K, a * b = b * a := by
    intro a b
    have ha : a ∈ Subgroup.zpowers x := htop ▸ Subgroup.mem_top a
    have hb : b ∈ Subgroup.zpowers x := htop ▸ Subgroup.mem_top b
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact (Commute.zpow_zpow_self x m n).eq
  refine sup_le ?_ ?_
  · rw [Subgroup.closure_le]
    rintro _ ⟨g, rfl⟩
    show g ^ p ∈ K
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, ← hcard]
    exact pow_card_eq_one'
  · rw [commutator, Subgroup.commutator_le]
    intro a _ b _
    rw [← QuotientGroup.eq_one_iff, commutatorElement_def, QuotientGroup.mk_mul,
      QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_inv,
      hcomm (a : P ⧸ K) (b : P ⧸ K), mul_assoc, mul_assoc, mul_inv_cancel_left, mul_inv_cancel]
