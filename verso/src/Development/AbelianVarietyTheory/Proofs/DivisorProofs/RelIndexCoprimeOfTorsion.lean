import Mathlib
open NumberField IsDedekindDomain

namespace GlobalTheory.FGIndex

/- English proof (translation)
Use `haveI : AddGroup.FG B := (AddGroup.fg_iff_addSubgroup_fg B).2 hB`. Use `haveI : AddGroup.FG (B ⧸ A.addSubgroupOf B) := AddGroup.fg_of_surjective (QuotientAddGroup.mk'_surjective _)`. Establish `hq : ∀ q : B ⧸ A.addSubgroupOf B, ∃ n : ℕ, n.Coprime l ∧ n • q = 0`. Introduce `q`. Proceed by induction on `q using QuotientAddGroup.induction_on with`.

Consider the case `H b`. Take `⟨n, hn, hnA⟩` from `h b b.2`. Use `⟨n, hn, ?_⟩` and prove the remaining obligations. Rewrite using `[← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]`. Simplify using `using hnA`.

Use `haveI : Finite (B ⧸ A.addSubgroupOf B) := by`. Apply `AddCommGroup.finite_of_fg_torsion` to reduce the goal to its premises. Introduce `q`. Take `⟨n, hn, hnq⟩` from `hq q`. Establish `hn0 : 0 < n`.

Break down `Nat.eq_zero_or_pos n with h0 | h0` into its components or cases. Rewrite `hn` using `[h0, Nat.coprime_zero_left]`. Conclude with `absurd hn hl.one_lt.ne'`. Conclude with `h0`. Conclude with `isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨n, hn0, hnq⟩`.

Establish `h0 : A.relIndex B ≠ 0`. Rewrite using `[AddSubgroup.relIndex, AddSubgroup.index]`. Conclude with `Nat.card_pos.ne'`. Use `⟨h0, ?_⟩` and prove the remaining obligations. Rewrite using `[Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hl]`.

Introduce `hd`. Use `haveI : Fact l.Prime := ⟨hl⟩`. Rewrite `hd` using `[AddSubgroup.relIndex, AddSubgroup.index]`. Take `⟨x, hx⟩` from `exists_prime_addOrderOf_dvd_card' (G := B ⧸ A.addSubgroupOf B) l hd`. Take `⟨n, hn, hnx⟩` from `hq x`.

Establish `: l ∣ n` using `hx ▸ addOrderOf_dvd_of_nsmul_eq_zero hnx`. Conclude with `(Nat.Prime.coprime_iff_not_dvd hl).1 (Nat.coprime_comm.1 hn) this`.
-/
theorem relIndex_ne_zero_coprime {G : Type} [AddCommGroup G] (A B : AddSubgroup G) (l : ℕ) (hl : l.Prime)
    (_hAB : A ≤ B) (hB : B.FG) (h : ∀ z ∈ B, ∃ n : ℕ, n.Coprime l ∧ n • z ∈ A) :
    A.relIndex B ≠ 0 ∧ (A.relIndex B).Coprime l := by
  haveI : AddGroup.FG B := (AddGroup.fg_iff_addSubgroup_fg B).2 hB
  haveI : AddGroup.FG (B ⧸ A.addSubgroupOf B) :=
    AddGroup.fg_of_surjective (QuotientAddGroup.mk'_surjective _)
  have hq : ∀ q : B ⧸ A.addSubgroupOf B, ∃ n : ℕ, n.Coprime l ∧ n • q = 0 := by
    intro q
    induction q using QuotientAddGroup.induction_on with
    | H b =>
      obtain ⟨n, hn, hnA⟩ := h b b.2
      refine ⟨n, hn, ?_⟩
      rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
      simpa using hnA
  haveI : Finite (B ⧸ A.addSubgroupOf B) := by
    apply AddCommGroup.finite_of_fg_torsion
    intro q
    obtain ⟨n, hn, hnq⟩ := hq q
    have hn0 : 0 < n := by
      rcases Nat.eq_zero_or_pos n with h0 | h0
      · rw [h0, Nat.coprime_zero_left] at hn; exact absurd hn hl.one_lt.ne'
      · exact h0
    exact isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨n, hn0, hnq⟩
  have h0 : A.relIndex B ≠ 0 := by
    rw [AddSubgroup.relIndex, AddSubgroup.index]
    exact Nat.card_pos.ne'
  refine ⟨h0, ?_⟩
  rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hl]
  intro hd
  haveI : Fact l.Prime := ⟨hl⟩
  rw [AddSubgroup.relIndex, AddSubgroup.index] at hd
  obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' (G := B ⧸ A.addSubgroupOf B) l hd
  obtain ⟨n, hn, hnx⟩ := hq x
  have : l ∣ n := hx ▸ addOrderOf_dvd_of_nsmul_eq_zero hnx
  exact (Nat.Prime.coprime_iff_not_dvd hl).1 (Nat.coprime_comm.1 hn) this

/- English proof (translation)
Introduce `A B l hl hAB hB h` and use `relIndex_ne_zero_coprime A B l hl hAB hB h`.
-/
theorem main : ∀ {G : Type} [AddCommGroup G] (A B : AddSubgroup G) (l : ℕ), l.Prime → A ≤ B → B.FG →
    (∀ z ∈ B, ∃ n : ℕ, n.Coprime l ∧ n • z ∈ A) → A.relIndex B ≠ 0 ∧ (A.relIndex B).Coprime l :=
  fun A B l hl hAB hB h => relIndex_ne_zero_coprime A B l hl hAB hB h

end GlobalTheory.FGIndex
