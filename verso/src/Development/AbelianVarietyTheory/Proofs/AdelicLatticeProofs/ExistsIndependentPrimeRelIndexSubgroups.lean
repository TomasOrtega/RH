import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.MemPowSub
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

/- English proof (translation)
Use `haveI : Fact p.Prime := ⟨hp⟩`. Use `set c : E ⧸ K.subgroupOf E := QuotientGroup.mk (⟨x, hxE⟩ : E) with hc`. Establish `ho : orderOf c = p`. Apply `orderOf_eq_prime` to reduce the goal to its premises. Rewrite using `[hc, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]`.

Simplify using `using hxp`. Rewrite using `[hc, Ne, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]`. Conclude with `hxK`. Establish `hall : ∀ y : E ⧸ K.subgroupOf E, y ∈ Submonoid.powers c`. Introduce `y`.

Take `⟨y, rfl⟩` from `QuotientGroup.mk_surjective y`. Take `⟨k, hk⟩` from `hgen y y.2`. Use `⟨k, ?_⟩` and prove the remaining obligations. Simplify using `only [hc]`. Rewrite using `[← QuotientGroup.mk_pow, eq_comm, QuotientGroup.eq_iff_div_mem, Subgroup.mem_subgroupOf]`.

Simplify using `using hk`. Rewrite using `[Subgroup.relIndex, Subgroup.index, ← ho]`. Conclude with `(orderOf_eq_card_of_forall_mem_powers hall).symm`.
-/
theorem relIndex_eq_prime_of_generated {G : Type} [CommGroup G] {p : ℕ} (hp : p.Prime)
    (E K : Subgroup G) (x : G) (hxE : x ∈ E) (hxK : x ∉ K) (hxp : x ^ p ∈ K)
    (hgen : ∀ y ∈ E, ∃ k : ℕ, y / x ^ k ∈ K) : K.relIndex E = p := by
  haveI : Fact p.Prime := ⟨hp⟩
  set c : E ⧸ K.subgroupOf E := QuotientGroup.mk (⟨x, hxE⟩ : E) with hc
  have ho : orderOf c = p := by
    apply orderOf_eq_prime
    · rw [hc, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      simpa using hxp
    · rw [hc, Ne, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      exact hxK
  have hall : ∀ y : E ⧸ K.subgroupOf E, y ∈ Submonoid.powers c := by
    intro y
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨k, hk⟩ := hgen y y.2
    refine ⟨k, ?_⟩
    simp only [hc]
    rw [← QuotientGroup.mk_pow, eq_comm, QuotientGroup.eq_iff_div_mem, Subgroup.mem_subgroupOf]
    simpa using hk
  rw [Subgroup.relIndex, Subgroup.index, ← ho]
  exact (orderOf_eq_card_of_forall_mem_powers hall).symm

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero`. Use `⟨∅, rfl, by simp, by simp, ⊤, by simp, by simp⟩` and prove the remaining obligations. Consider the case `succ k ih`. Take `⟨T, hT, hg, hA, D, hD, hDi⟩` from `ih (by omega)`.

Establish `hx : ∃ x ∈ U, x ∈ D ∧ x ∉ H`. Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Establish `heq : D ⊓ U = H ⊓ U`. Use extensionality with `x`.

Simplify using `only [Subgroup.mem_inf]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, b⟩`. Conclude with `⟨hcon x b a, b⟩`. Introduce and unpack `⟨a, b⟩`.

Conclude with `⟨(hD x).2 fun i hi => h1 i (hg i hi) ⟨b, a⟩, b⟩`. Establish `h4 : D.relIndex U = H.relIndex U`. Rewrite using `[← Subgroup.inf_relIndex_right D U, heq, Subgroup.inf_relIndex_right]`. Rewrite `h4` using `[hDi, hH]`. Use `Nat.pow_right_injective hp.two_le h4` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Take `⟨x, hxU, hxD, hxH⟩` from `hx`. Take `⟨j, hj, hxj⟩` from `h3 x hxU hxH`. Establish `hjT : j ∉ T` using `fun h => hxj ((hD x).1 hxD j h)`. Use `⟨insert j T, by rw [Finset.card_insert_of_notMem hjT, hT], ?_, ?_, K j ⊓ D, ?_, ?_⟩` and prove the remaining obligations.

Introduce `i hi`. Break down `Finset.mem_insert.1 hi with rfl | hi` into its components or cases. Conclude with `hj`. Conclude with `hg i hi`. Introduce `i hi`.

Break down `Finset.mem_insert.1 hi with rfl | hi` into its components or cases. Use `⟨x, hxU, hxj, fun l hl hli => ?_⟩` and prove the remaining obligations. Break down `Finset.mem_insert.1 hl with rfl | hl` into its components or cases. Conclude with `absurd rfl hli`. Conclude with `(hD x).1 hxD l hl`.

Take `⟨u, huU, hui, hu⟩` from `hA i hi`. Take `⟨n, hn⟩` from `h2' j hj x hxU hxj u huU`. Use `⟨u / x ^ n, U.div_mem huU (U.pow_mem hxU n), ?_, fun l hl hli => ?_⟩` and prove the remaining obligations. Introduce `h`. Apply `hui` to reduce the goal to its premises.

Use `(K i).mul_mem h ((K i).pow_mem ((hD x).1 hxD i hi) n)` as an intermediate fact. Simplify using `using this`. Break down `Finset.mem_insert.1 hl with rfl | hl` into its components or cases. Conclude with `hn`. Conclude with `(K l).div_mem (hu l hl hli) ((K l).pow_mem ((hD x).1 hxD l hl) n)`.

Introduce `y`. Simplify using `only [Subgroup.mem_inf, hD, Finset.forall_mem_insert]`. Establish `h5 : (K j).relIndex (D ⊓ U) = p` using `relIndex_eq_prime_of_generated hp (D ⊓ U) (K j) x ⟨hxD, hxU⟩ hxj (h2 j hj x hxU) (fun y hy => h2' j hj x hxU hxj y hy.2)`. Rewrite using `[← Subgroup.relIndex_inf_mul_relIndex, h5, hDi, pow_succ, mul_comm]`.
-/
theorem exists_independent_prime_relIndex_subgroups (p : ℕ) (G ι : Type) [CommGroup G] [DecidableEq ι]
    (U H : Subgroup G) (K : ι → Subgroup G) (good : ι → Prop) (m : ℕ) (hp : p.Prime)
    (hH : H.relIndex U = p ^ m) (h1 : ∀ i, good i → U ⊓ H ≤ K i)
    (h2 : ∀ i, good i → ∀ x ∈ U, x ^ p ∈ K i)
    (h2' : ∀ i, good i → ∀ x ∈ U, x ∉ K i → ∀ y ∈ U, ∃ k : ℕ, y / x ^ k ∈ K i)
    (h3 : ∀ x ∈ U, x ∉ H → ∃ i, good i ∧ x ∉ K i) (k : ℕ) (hk : k ≤ m) :
    ∃ T : Finset ι, T.card = k ∧ (∀ i ∈ T, good i) ∧
      (∀ i ∈ T, ∃ u ∈ U, u ∉ K i ∧ ∀ j ∈ T, j ≠ i → u ∈ K j) ∧
      ∃ D : Subgroup G, (∀ x, x ∈ D ↔ ∀ i ∈ T, x ∈ K i) ∧ D.relIndex U = p ^ k := by
  induction k with
  | zero =>
    refine ⟨∅, rfl, by simp, by simp, ⊤, by simp, by simp⟩
  | succ k ih =>
    obtain ⟨T, hT, hg, hA, D, hD, hDi⟩ := ih (by omega)
    have hx : ∃ x ∈ U, x ∈ D ∧ x ∉ H := by
      by_contra hcon
      push Not at hcon
      have heq : D ⊓ U = H ⊓ U := by
        ext x
        simp only [Subgroup.mem_inf]
        constructor
        · rintro ⟨a, b⟩
          exact ⟨hcon x b a, b⟩
        · rintro ⟨a, b⟩
          exact ⟨(hD x).2 fun i hi => h1 i (hg i hi) ⟨b, a⟩, b⟩
      have h4 : D.relIndex U = H.relIndex U := by
        rw [← Subgroup.inf_relIndex_right D U, heq, Subgroup.inf_relIndex_right]
      rw [hDi, hH] at h4
      have := Nat.pow_right_injective hp.two_le h4
      omega
    obtain ⟨x, hxU, hxD, hxH⟩ := hx
    obtain ⟨j, hj, hxj⟩ := h3 x hxU hxH
    have hjT : j ∉ T := fun h => hxj ((hD x).1 hxD j h)
    refine ⟨insert j T, by rw [Finset.card_insert_of_notMem hjT, hT], ?_, ?_, K j ⊓ D, ?_, ?_⟩
    · intro i hi
      rcases Finset.mem_insert.1 hi with rfl | hi
      · exact hj
      · exact hg i hi
    · intro i hi
      rcases Finset.mem_insert.1 hi with rfl | hi
      · refine ⟨x, hxU, hxj, fun l hl hli => ?_⟩
        rcases Finset.mem_insert.1 hl with rfl | hl
        · exact absurd rfl hli
        · exact (hD x).1 hxD l hl
      · obtain ⟨u, huU, hui, hu⟩ := hA i hi
        obtain ⟨n, hn⟩ := h2' j hj x hxU hxj u huU
        refine ⟨u / x ^ n, U.div_mem huU (U.pow_mem hxU n), ?_, fun l hl hli => ?_⟩
        · intro h
          apply hui
          have := (K i).mul_mem h ((K i).pow_mem ((hD x).1 hxD i hi) n)
          simpa using this
        · rcases Finset.mem_insert.1 hl with rfl | hl
          · exact hn
          · exact (K l).div_mem (hu l hl hli) ((K l).pow_mem ((hD x).1 hxD l hl) n)
    · intro y
      simp only [Subgroup.mem_inf, hD, Finset.forall_mem_insert]
    · have h5 : (K j).relIndex (D ⊓ U) = p :=
        relIndex_eq_prime_of_generated hp (D ⊓ U) (K j) x ⟨hxD, hxU⟩ hxj (h2 j hj x hxU)
          (fun y hy => h2' j hj x hxU hxj y hy.2)
      rw [← Subgroup.relIndex_inf_mul_relIndex, h5, hDi, pow_succ, mul_comm]

/- English proof (translation)
Introduce `p G ι _ _ U H K good m hp hH h1 h2 h2' h3`. Take `⟨T, a, b, c, -⟩` from `exists_independent_prime_relIndex_subgroups p G ι U H K good m hp hH h1 h2 h2' h3 m le_rfl`. Conclude with `⟨T, a, b, c⟩`.
-/
theorem exists_indep_prime_index : ∀ (p : ℕ) (G ι : Type) [CommGroup G] [DecidableEq ι] (U H : Subgroup G) (K : ι → Subgroup G) (good : ι → Prop) (m : ℕ), p.Prime → H.relIndex U = p ^ m → (∀ i, good i → U ⊓ H ≤ K i) → (∀ i, good i → ∀ x ∈ U, x ^ p ∈ K i) → (∀ i, good i → ∀ x ∈ U, x ∉ K i → ∀ y ∈ U, ∃ k : ℕ, y / x ^ k ∈ K i) → (∀ x ∈ U, x ∉ H → ∃ i, good i ∧ x ∉ K i) → ∃ T : Finset ι, T.card = m ∧ (∀ i ∈ T, good i) ∧ ∀ i ∈ T, ∃ u ∈ U, u ∉ K i ∧ ∀ j ∈ T, j ≠ i → u ∈ K j := by
  intro p G ι _ _ U H K good m hp hH h1 h2 h2' h3
  obtain ⟨T, a, b, c, -⟩ :=
    exists_independent_prime_relIndex_subgroups p G ι U H K good m hp hH h1 h2 h2' h3 m le_rfl
  exact ⟨T, a, b, c⟩

end GlobalTheory.CNorm
