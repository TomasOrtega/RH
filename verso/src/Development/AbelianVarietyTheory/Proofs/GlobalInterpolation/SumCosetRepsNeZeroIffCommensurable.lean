import Mathlib

namespace GlobalTheory.Proof.sum_coset_reps_ne_zero_iff_commensurable

/- English proof (translation)
Use `haveI : Finite (N ⧸ M.addSubgroupOf N) := Nat.finite_of_card_ne_zero hidx`. Use `letI : Fintype (N ⧸ M.addSubgroupOf N) := Fintype.ofFinite _`. Set `φ : V × (N ⧸ M.addSubgroupOf N) → V ⧸ M` to `fun p => QuotientAddGroup.mk (p.1 + ((p.2.out : N) : V))`. Establish `hout : ∀ v : V, f (QuotientAddGroup.mk v : V ⧸ M).out = f v`. Introduce `v`.

Establish `h : -v + (QuotientAddGroup.mk v : V ⧸ M).out ∈ M`. Rewrite using `[← QuotientAddGroup.eq]`. Simplify using the standard rewrite rules. Use `hf v _ (hMN h)` as an intermediate fact. Simplify using `using this`.

Rewrite using `[finsum_eq_sum_of_support_subset (s := (S ×ˢ Finset.univ).image φ)]`. Rewrite using `[Finset.sum_image]`. Rewrite using `[Finset.sum_product]`. Establish `: ∀ s ∈ S, ∑ q : N ⧸ M.addSubgroupOf N, f (φ (s, q)).out = (M.relIndex N : K) * f s`. Introduce `s _`.

Establish `: ∀ q : N ⧸ M.addSubgroupOf N, f (φ (s, q)).out = f s`. Introduce `q`. Simplify using `only [φ]`. Rewrite using `[hout, hf _ _ (q.out).2]`. Simplify using `only [this, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]`.

Rewrite using `[← Nat.card_eq_fintype_card]`. Both sides reduce to the same expression. Rewrite using `[Finset.sum_congr rfl this, Finset.mul_sum]`. Introduce and unpack `⟨s, q⟩ hp ⟨s', q'⟩ hp' h`. Simplify using `only [Finset.coe_product, Set.mem_prod, Finset.mem_coe] at hp hp'`.

Simplify using `only [φ, QuotientAddGroup.eq] at h`. Establish `hs : s = s'`. Apply `hinj s hp.1 s' hp'.1` to reduce the goal to its premises. Establish `h1` using `N.add_mem (N.sub_mem (q'.out).2 (q.out).2) (N.neg_mem (hMN h))`. Use `h1 using 1` and compare the differences between its conclusion and the goal.

Normalize the expressions using the abelian group laws. Substitute `hs` using the available equality. Establish `hq : q = q'`. Rewrite using `[← Quotient.out_eq q, ← Quotient.out_eq q']`. Apply `QuotientAddGroup.eq.2` to reduce the goal to its premises.

Rewrite using `[AddSubgroup.mem_addSubgroupOf]`. Use `h using 1` and compare the differences between its conclusion and the goal. Use `push_cast`. Normalize the expressions using the abelian group laws. Rewrite using `[hq]`.

Introduce `c hc`. Take `⟨s, hs, hn⟩` from `hcov c.out hc`. Simplify using `only [Finset.coe_image, Set.mem_image]`. Use `⟨(s, QuotientAddGroup.mk ⟨c.out - s, hn⟩), by simp [hs], ?_⟩` and prove the remaining obligations. Establish `h : -(QuotientAddGroup.mk (⟨c.out - s, hn⟩ : N) : N ⧸ M.addSubgroupOf N).out + (⟨c.out - s, hn⟩ : N) ∈ M.addSubgroupOf N`.

Rewrite using `[← QuotientAddGroup.eq]`. Simplify using the standard rewrite rules. Rewrite `h` using `[AddSubgroup.mem_addSubgroupOf]`. Use `conv_rhs => rw [← Quotient.out_eq c]`. Apply `QuotientAddGroup.eq.2` to reduce the goal to its premises.

Use `h using 1` and compare the differences between its conclusion and the goal. Use `push_cast`. Normalize the expressions using the abelian group laws.
-/
theorem finsum_quot_eq {V K : Type} [AddCommGroup V] [Field K] (f : V → K) (M N : AddSubgroup V)
    (S : Finset V) (hMN : M ≤ N) (hidx : M.relIndex N ≠ 0)
    (hf : ∀ v, ∀ u ∈ N, f (v + u) = f v)
    (hinj : ∀ s ∈ S, ∀ s' ∈ S, s - s' ∈ N → s = s')
    (hcov : ∀ v, f v ≠ 0 → ∃ s ∈ S, v - s ∈ N) :
    ∑ᶠ c : V ⧸ M, f c.out = (M.relIndex N : K) * ∑ s ∈ S, f s := by
  classical
  haveI : Finite (N ⧸ M.addSubgroupOf N) := Nat.finite_of_card_ne_zero hidx
  letI : Fintype (N ⧸ M.addSubgroupOf N) := Fintype.ofFinite _
  let φ : V × (N ⧸ M.addSubgroupOf N) → V ⧸ M :=
    fun p => QuotientAddGroup.mk (p.1 + ((p.2.out : N) : V))
  have hout : ∀ v : V, f (QuotientAddGroup.mk v : V ⧸ M).out = f v := by
    intro v
    have h : -v + (QuotientAddGroup.mk v : V ⧸ M).out ∈ M := by
      rw [← QuotientAddGroup.eq]; simp
    have := hf v _ (hMN h)
    simpa using this
  rw [finsum_eq_sum_of_support_subset (s := (S ×ˢ Finset.univ).image φ)]
  · rw [Finset.sum_image]
    · rw [Finset.sum_product]
      have : ∀ s ∈ S, ∑ q : N ⧸ M.addSubgroupOf N, f (φ (s, q)).out = (M.relIndex N : K) * f s := by
        intro s _
        have : ∀ q : N ⧸ M.addSubgroupOf N, f (φ (s, q)).out = f s := by
          intro q
          simp only [φ]
          rw [hout, hf _ _ (q.out).2]
        simp only [this, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        rw [← Nat.card_eq_fintype_card]
        rfl
      rw [Finset.sum_congr rfl this, Finset.mul_sum]
    · rintro ⟨s, q⟩ hp ⟨s', q'⟩ hp' h
      simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe] at hp hp'
      simp only [φ, QuotientAddGroup.eq] at h
      have hs : s = s' := by
        apply hinj s hp.1 s' hp'.1
        have h1 := N.add_mem (N.sub_mem (q'.out).2 (q.out).2) (N.neg_mem (hMN h))
        convert h1 using 1
        abel
      subst hs
      have hq : q = q' := by
        rw [← Quotient.out_eq q, ← Quotient.out_eq q']
        apply QuotientAddGroup.eq.2
        rw [AddSubgroup.mem_addSubgroupOf]
        convert h using 1
        push_cast
        abel
      rw [hq]
  · intro c hc
    obtain ⟨s, hs, hn⟩ := hcov c.out hc
    simp only [Finset.coe_image, Set.mem_image]
    refine ⟨(s, QuotientAddGroup.mk ⟨c.out - s, hn⟩), by simp [hs], ?_⟩
    have h : -(QuotientAddGroup.mk (⟨c.out - s, hn⟩ : N) : N ⧸ M.addSubgroupOf N).out
        + (⟨c.out - s, hn⟩ : N) ∈ M.addSubgroupOf N := by
      rw [← QuotientAddGroup.eq]; simp
    rw [AddSubgroup.mem_addSubgroupOf] at h
    conv_rhs => rw [← Quotient.out_eq c]
    apply QuotientAddGroup.eq.2
    convert h using 1
    push_cast
    abel

/- English proof (translation)
Introduce `V K _ _ _ f N N' S S' h1 h2 hf hf' hi hc hi' hc'`. Establish `e1 : (N ⊓ N').relIndex N ≠ 0` using `by rwa [AddSubgroup.inf_relIndex_left]`. Establish `e2 : (N ⊓ N').relIndex N' ≠ 0` using `by rwa [AddSubgroup.inf_relIndex_right]`. Establish `a` using `finsum_quot_eq f (N ⊓ N') N S inf_le_left e1 hf hi hc`. Establish `b` using `finsum_quot_eq f (N ⊓ N') N' S' inf_le_right e2 hf' hi' hc'`.

Establish `c1 : (((N ⊓ N').relIndex N : ℕ) : K) ≠ 0` using `Nat.cast_ne_zero.2 e1`. Establish `c2 : (((N ⊓ N').relIndex N' : ℕ) : K) ≠ 0` using `Nat.cast_ne_zero.2 e2`. Rewrite using `[← mul_ne_zero_iff_left c1, ← a, b, mul_ne_zero_iff_left c2]`.
-/
theorem sum_reps_ne_zero_iff : ∀ (V K : Type) [AddCommGroup V] [Field K] [CharZero K] (f : V → K) (N N' : AddSubgroup V) (S S' : Finset V), N'.relIndex N ≠ 0 → N.relIndex N' ≠ 0 → (∀ v, ∀ u ∈ N, f (v + u) = f v) → (∀ v, ∀ u ∈ N', f (v + u) = f v) → (∀ s ∈ S, ∀ s' ∈ S, s - s' ∈ N → s = s') → (∀ v, f v ≠ 0 → ∃ s ∈ S, v - s ∈ N) → (∀ s ∈ S', ∀ s' ∈ S', s - s' ∈ N' → s = s') → (∀ v, f v ≠ 0 → ∃ s ∈ S', v - s ∈ N') → (∑ s ∈ S, f s ≠ 0 ↔ ∑ s ∈ S', f s ≠ 0) := by
  intro V K _ _ _ f N N' S S' h1 h2 hf hf' hi hc hi' hc'
  have e1 : (N ⊓ N').relIndex N ≠ 0 := by rwa [AddSubgroup.inf_relIndex_left]
  have e2 : (N ⊓ N').relIndex N' ≠ 0 := by rwa [AddSubgroup.inf_relIndex_right]
  have a := finsum_quot_eq f (N ⊓ N') N S inf_le_left e1 hf hi hc
  have b := finsum_quot_eq f (N ⊓ N') N' S' inf_le_right e2 hf' hi' hc'
  have c1 : (((N ⊓ N').relIndex N : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.2 e1
  have c2 : (((N ⊓ N').relIndex N' : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.2 e2
  rw [← mul_ne_zero_iff_left c1, ← a, b, mul_ne_zero_iff_left c2]

end GlobalTheory.Proof.sum_coset_reps_ne_zero_iff_commensurable
