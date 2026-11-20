import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.StabiliserCardinality

namespace GlobalTheory.Proof.DoubleCosetCountGlobalInterpolation

open GlobalTheory.IndefiniteRowSideFullHecke.StabiliserCardinality

/- English proof (translation)
Establish `hex : ∀ d : {d : DoubleCoset.Quotient (Γ : Set G) (U : Set G) // DoubleCoset.mk Γ K d.out = DoubleCoset.mk Γ K y}, ∃ k : K, DoubleCoset.mk Γ U (y * k) = d.1`. Introduce and unpack `⟨d, hd⟩`. Take `⟨a, ha, k, hk, h⟩` from `(DoubleCoset.eq Γ K _ _).1 hd.symm`. Use `⟨⟨k, hk⟩, ?_⟩` and prove the remaining obligations. Use `Eq.trans ?_ (DoubleCoset.out_eq' Γ U d)` and prove the remaining obligations.

Conclude with `(DoubleCoset.eq Γ U _ _).2 ⟨a, ha, 1, U.one_mem, by rw [h]; group⟩`. Use `choose κ hκ using hex`. Rewrite using `[← Nat.card_prod, Subgroup.relIndex, Subgroup.index]`. Use `Nat.card_congr (Equiv.ofBijective (fun p => ((⟨y⁻¹ * p.2.1 * y, ((mem_stab Γ K y _).1 p.2.2).2⟩ * κ p.1 : K) : K ⧸ U.subgroupOf K)) ⟨?_, ?_⟩)` and prove the remaining obligations. Introduce and unpack `⟨d, s, hs⟩ ⟨e, t, ht⟩ h`.

Establish `hs'` using `((mem_stab Γ K y _).1 hs).1`. Establish `ht'` using `((mem_stab Γ K y _).1 ht).1`. Establish `h1` using `QuotientGroup.eq.1 h`. Rewrite `h1` using `[Subgroup.mem_subgroupOf]`. Simplify using `only [Subgroup.coe_mul, Subgroup.coe_inv] at h1`.

Establish `hde : d = e`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[← hκ d, ← hκ e]`. Conclude with `(DoubleCoset.eq Γ U _ _).2 ⟨t⁻¹ * s, Γ.mul_mem (Γ.inv_mem ht') hs', _, h1, by group⟩`. Substitute `hde` using the available equality.

Establish `h2 : s⁻¹ * t ∈ stab Γ U (y * κ d)`. Use `(mem_stab Γ U _ _).2 ⟨Γ.mul_mem (Γ.inv_mem hs') ht', ?_⟩` and prove the remaining obligations. Use `h1 using 1` and compare the differences between its conclusion and the goal. Use `group`. Rewrite `h2` using `[hfree, Subgroup.mem_bot, inv_mul_eq_one]`.

Substitute `h2` using the available equality. Both sides reduce to the same expression. Introduce `q`. Proceed by induction on `q using QuotientGroup.induction_on with`. Consider the case `H k`.

Establish `hd : DoubleCoset.mk Γ K (DoubleCoset.mk Γ U (y * k)).out = DoubleCoset.mk Γ K y`. Take `⟨a, ha, u, hu, h⟩` from `(DoubleCoset.eq Γ U _ _).1 (DoubleCoset.out_eq' Γ U (DoubleCoset.mk Γ U (y * k))).symm`. Use `symm`. Conclude with `(DoubleCoset.eq Γ K _ _).2 ⟨a, ha, k * u, K.mul_mem k.2 (hUK hu), h.trans (by group)⟩`. Take `⟨a, ha, u, hu, h⟩` from `(DoubleCoset.eq Γ U _ _).1 (hκ ⟨_, hd⟩)`.

Establish `hk : y⁻¹ * a * y = k * u⁻¹ * (κ ⟨_, hd⟩ : G)⁻¹`. Generalize the expression as in `(κ ⟨_, hd⟩ : G) = m at h ⊢`. Rewrite using `[show (k : G) = y⁻¹ * (y * k) by group, h]`. Use `group`. Establish `hs : a ∈ stab Γ K y`.

Use `(mem_stab Γ K y _).2 ⟨ha, ?_⟩` and prove the remaining obligations. Rewrite using `[hk]`. Conclude with `K.mul_mem (K.mul_mem k.2 (K.inv_mem (hUK hu))) (K.inv_mem (κ _).2)`. Use `⟨⟨⟨_, hd⟩, ⟨a, hs⟩⟩, QuotientGroup.eq.2 ?_⟩` and prove the remaining obligations. Rewrite using `[Subgroup.mem_subgroupOf]`.

Simplify using `only [Subgroup.coe_mul, Subgroup.coe_inv]`. Rewrite using `[hk]`. Use `hu using 1` and compare the differences between its conclusion and the goal. Use `group`.
-/
theorem card_fiber_mul_card_stab {G : Type} [Group G] (Γ U K : Subgroup G) (hUK : U ≤ K)
    (hfree : ∀ x : G, stab Γ U x = ⊥) (y : G) :
    Nat.card {d : DoubleCoset.Quotient (Γ : Set G) (U : Set G) //
        DoubleCoset.mk Γ K d.out = DoubleCoset.mk Γ K y} * Nat.card (stab Γ K y) =
      U.relIndex K := by
  have hex : ∀ d : {d : DoubleCoset.Quotient (Γ : Set G) (U : Set G) //
        DoubleCoset.mk Γ K d.out = DoubleCoset.mk Γ K y},
      ∃ k : K, DoubleCoset.mk Γ U (y * k) = d.1 := by
    rintro ⟨d, hd⟩
    obtain ⟨a, ha, k, hk, h⟩ := (DoubleCoset.eq Γ K _ _).1 hd.symm
    refine ⟨⟨k, hk⟩, ?_⟩
    refine Eq.trans ?_ (DoubleCoset.out_eq' Γ U d)
    exact (DoubleCoset.eq Γ U _ _).2 ⟨a, ha, 1, U.one_mem, by rw [h]; group⟩
  choose κ hκ using hex
  rw [← Nat.card_prod, Subgroup.relIndex, Subgroup.index]
  refine Nat.card_congr (Equiv.ofBijective
    (fun p => ((⟨y⁻¹ * p.2.1 * y, ((mem_stab Γ K y _).1 p.2.2).2⟩ * κ p.1 : K) :
      K ⧸ U.subgroupOf K)) ⟨?_, ?_⟩)
  · rintro ⟨d, s, hs⟩ ⟨e, t, ht⟩ h
    have hs' := ((mem_stab Γ K y _).1 hs).1
    have ht' := ((mem_stab Γ K y _).1 ht).1
    have h1 := QuotientGroup.eq.1 h
    rw [Subgroup.mem_subgroupOf] at h1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h1
    have hde : d = e := by
      apply Subtype.ext
      rw [← hκ d, ← hκ e]
      exact (DoubleCoset.eq Γ U _ _).2 ⟨t⁻¹ * s, Γ.mul_mem (Γ.inv_mem ht') hs', _, h1, by group⟩
    subst hde
    have h2 : s⁻¹ * t ∈ stab Γ U (y * κ d) := by
      refine (mem_stab Γ U _ _).2 ⟨Γ.mul_mem (Γ.inv_mem hs') ht', ?_⟩
      convert h1 using 1
      group
    rw [hfree, Subgroup.mem_bot, inv_mul_eq_one] at h2
    subst h2
    rfl
  · intro q
    induction q using QuotientGroup.induction_on with
    | H k =>
      have hd : DoubleCoset.mk Γ K (DoubleCoset.mk Γ U (y * k)).out = DoubleCoset.mk Γ K y := by
        obtain ⟨a, ha, u, hu, h⟩ := (DoubleCoset.eq Γ U _ _).1
          (DoubleCoset.out_eq' Γ U (DoubleCoset.mk Γ U (y * k))).symm
        symm
        exact (DoubleCoset.eq Γ K _ _).2
          ⟨a, ha, k * u, K.mul_mem k.2 (hUK hu), h.trans (by group)⟩
      obtain ⟨a, ha, u, hu, h⟩ := (DoubleCoset.eq Γ U _ _).1 (hκ ⟨_, hd⟩)
      have hk : y⁻¹ * a * y = k * u⁻¹ * (κ ⟨_, hd⟩ : G)⁻¹ := by
        generalize (κ ⟨_, hd⟩ : G) = m at h ⊢
        rw [show (k : G) = y⁻¹ * (y * k) by group, h]
        group
      have hs : a ∈ stab Γ K y := by
        refine (mem_stab Γ K y _).2 ⟨ha, ?_⟩
        rw [hk]
        exact K.mul_mem (K.mul_mem k.2 (K.inv_mem (hUK hu))) (K.inv_mem (κ _).2)
      refine ⟨⟨⟨_, hd⟩, ⟨a, hs⟩⟩, QuotientGroup.eq.2 ?_⟩
      rw [Subgroup.mem_subgroupOf]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [hk]
      convert hu using 1
      group

/- English proof (translation)
Introduce `G _ Γ U K hUK hfi _ hfin hfree rep hrep`. Establish `hne : U.relIndex K ≠ 0` using `hfi.index_ne_zero`. Set `π : DoubleCoset.Quotient (Γ : Set G) (U : Set G) → DoubleCoset.Quotient (Γ : Set G) (K : Set G)` to `fun d => DoubleCoset.mk Γ K d.out`. Establish `key : ∀ c, Nat.card {d // π d = c} * Nat.card (stab Γ K (rep c)) = U.relIndex K`. Introduce `c`.

Use `card_fiber_mul_card_stab Γ U K hUK hfree (rep c)` as an intermediate fact. Rewrite `this` using `[hrep c]`. Conclude with `this`. Establish `: ∀ c, Finite {d // π d = c}` using `fun c => Nat.finite_of_card_ne_zero fun h => hne (by rw [← key c, h, zero_mul])`. Use `⟨Finite.of_equiv _ (Equiv.sigmaFiberEquiv π), ?_⟩` and prove the remaining obligations.

Rewrite using `[← Nat.card_congr (Equiv.sigmaFiberEquiv π), Nat.card_sigma, Finset.mul_sum, Nat.cast_sum]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Establish `hs : (Nat.card (stab Γ K (rep c)) : ℚ) ≠ 0`. Use `hfin (rep c)` as an intermediate fact. Conclude with `Nat.card_pos.ne'` after adjusting the coercions.

Rewrite using `[← key c]`. Use `push_cast`. Clear the denominators using the available nonvanishing facts.
-/
theorem doubleCosetCount : DoubleCosetCount := by
  intro G _ Γ U K hUK hfi _ hfin hfree rep hrep
  have hne : U.relIndex K ≠ 0 := hfi.index_ne_zero
  let π : DoubleCoset.Quotient (Γ : Set G) (U : Set G) →
      DoubleCoset.Quotient (Γ : Set G) (K : Set G) := fun d => DoubleCoset.mk Γ K d.out
  have key : ∀ c, Nat.card {d // π d = c} * Nat.card (stab Γ K (rep c)) = U.relIndex K := by
    intro c
    have := card_fiber_mul_card_stab Γ U K hUK hfree (rep c)
    rw [hrep c] at this
    exact this
  have : ∀ c, Finite {d // π d = c} := fun c =>
    Nat.finite_of_card_ne_zero fun h => hne (by rw [← key c, h, zero_mul])
  refine ⟨Finite.of_equiv _ (Equiv.sigmaFiberEquiv π), ?_⟩
  rw [← Nat.card_congr (Equiv.sigmaFiberEquiv π), Nat.card_sigma, Finset.mul_sum, Nat.cast_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  have hs : (Nat.card (stab Γ K (rep c)) : ℚ) ≠ 0 := by
    have := hfin (rep c)
    exact_mod_cast Nat.card_pos.ne'
  rw [← key c]
  push_cast
  field_simp

end GlobalTheory.Proof.DoubleCosetCountGlobalInterpolation
