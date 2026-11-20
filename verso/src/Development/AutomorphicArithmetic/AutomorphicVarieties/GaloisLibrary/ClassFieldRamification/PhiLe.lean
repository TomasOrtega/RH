import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.IsClassFieldHilbert
import Mathlib.GroupTheory.Nilpotent
import Mathlib.GroupTheory.Sylow

open NumberField IsDedekindDomain IntermediateField UpperTheory.V.Kum UpperTheory.V.CF
open scoped Pointwise

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Separate the alternatives or extract the components of the hypothesis. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Separate the alternatives or extract the components of the hypothesis. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. It suffices to derive a contradiction.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
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
