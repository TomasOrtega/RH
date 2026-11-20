import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAdmissibleIntegralBasisChangeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionFieldOneVariableTranscendentalFiniteAndEStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionFieldPlaceSumOrderEqFinrankStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniquePlaceOrdEqOneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionFieldPlaceRestrictionExistsPowStatement

open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

namespace GlobalTheory.Nef

/- English proof (translation)
Rewrite using `[eq_top_iff]`. Introduce and unpack `y -`. Establish `hm : (k⟮(⟨x, IntermediateField.mem_adjoin_simple_self k x⟩ : k⟮x⟯)⟯).map (k⟮x⟯.val) = k⟮x⟯`. Rewrite using `[IntermediateField.adjoin_map]`. Simplify using the standard rewrite rules.

Establish `hy : (y : F) ∈ (k⟮(⟨x, IntermediateField.mem_adjoin_simple_self k x⟩ : k⟮x⟯)⟯).map (k⟮x⟯.val)`. Rewrite using `[hm]`. Conclude with `y.2`. Take `⟨z, hz, hzy⟩` from `hy`. Establish `: z = y` using `Subtype.ext hzy`.

Conclude with `this ▸ hz`.
-/
theorem adjoin_gen_eq_top {k F : Type} [Field k] [Field F] [Algebra k F] (x : F) :
    k⟮(⟨x, IntermediateField.mem_adjoin_simple_self k x⟩ : k⟮x⟯)⟯ = ⊤ := by
  rw [eq_top_iff]
  rintro y -
  have hm : (k⟮(⟨x, IntermediateField.mem_adjoin_simple_self k x⟩ : k⟮x⟯)⟯).map (k⟮x⟯.val) = k⟮x⟯ := by
    rw [IntermediateField.adjoin_map]; simp
  have hy : (y : F) ∈ (k⟮(⟨x, IntermediateField.mem_adjoin_simple_self k x⟩ : k⟮x⟯)⟯).map (k⟮x⟯.val) := by
    rw [hm]; exact y.2
  obtain ⟨z, hz, hzy⟩ := hy
  have : z = y := Subtype.ext hzy
  exact this ▸ hz

/- English proof (translation)
Unfold `ord at h`. Distinguish the cases in `h0 : v.1 t = 0`. Rewrite `h` using `[h0]`. Simplify using `at h`. Establish `hl : WithZero.log (v.1 t) < WithZero.log (1 : WithZero (Multiplicative ℤ))` using `by simp; omega`.

Conclude with `(WithZero.log_lt_log h0 one_ne_zero).1 hl`.
-/
theorem val_lt_one_of_ord_eq_one {k F : Type} [Field k] [Field F] [Algebra k F] (v : Place k F) (t : F)
    (h : ord v t = 1) : v.1 t < 1 := by
  unfold ord at h
  by_cases h0 : v.1 t = 0
  · rw [h0] at h; simp at h
  · have hl : WithZero.log (v.1 t) < WithZero.log (1 : WithZero (Multiplicative ℤ)) := by
      simp; omega
    exact (WithZero.log_lt_log h0 one_ne_zero).1 hl

end GlobalTheory.Nef

namespace GlobalTheory.Nef

/- English proof (translation)
Introduce `k F _ _ _ _ _ hF x hx`. Use `haveI : FiniteDimensional k⟮x⟯ F := (GlobalTheory.T.functionFieldOneVariable_transcendental_finite_and_ext k F hF).1 x hx`. Use `set t : k⟮x⟯ := ⟨x, IntermediateField.mem_adjoin_simple_self k x⟩ with ht`. Establish `htx : algebraMap k⟮x⟯ F t = x` using `rfl`. Establish `htr : Transcendental k t`.

Introduce `ha`. Conclude with `hx ((IntermediateField.isAlgebraic_iff).1 ha)`. Establish `htop : k⟮t⟯ = ⊤` using `adjoin_gen_eq_top x`. Establish `hL : IsFF k k⟮x⟯`. Use `⟨t, htr, ?_⟩` and prove the remaining obligations.

Rewrite using `[htop]`. Conclude with `Module.finite_of_finrank_eq_succ (IntermediateField.finrank_top)`. Take `⟨v0, hv0, huniq⟩` from `GlobalTheory.T.existsUnique_place_ord_eq_one_of_transcendental_generator k k⟮x⟯ t htr htop`. Take `⟨ρ, hρ⟩` from `(GlobalTheory.T.functionFieldPlace_restriction_exists_pow k k⟮x⟯ F).1`. Establish `ht0 : t ≠ 0`.

Introduce `h`. Apply `hx` to reduce the goal to its premises. Rewrite using `[← htx, h, map_zero]`. Conclude with `isAlgebraic_zero`. Take `⟨hfin, hsum⟩` from `GlobalTheory.T.functionFieldPlace_sum_order_eq_finrank k k⟮x⟯ F hL ρ hρ v0 t ht0 hv0`.

Establish `hset : {v : Place k F | v.1 x < 1} = {p | ρ p = v0}`. Use extensionality with `p`. Take `⟨e, he, hpow, -⟩` from `(GlobalTheory.T.functionFieldPlace_restriction_exists_pow k k⟮x⟯ F).2 ρ hρ p`. Simplify using `only [Set.mem_setOf_eq]`. Express the relevant statement in the definitionally equal form `p.1 (algebraMap k⟮x⟯ F t) < 1 ↔ ρ p = v0`.

Rewrite using `[hpow t]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Apply `huniq` to reduce the goal to its premises. Assume the negation of the conclusion as `hn`.

Conclude with `absurd h (not_lt.2 (one_le_pow₀ (not_lt.1 hn)))`. Introduce `h`. Rewrite using `[h]`. Conclude with `pow_lt_one₀ zero_le' (val_lt_one_of_ord_eq_one v0 t hv0) he.ne'`. Rewrite using `[hset]`.

Conclude with `⟨hfin, by simpa [htx] using hsum⟩`.
-/
theorem zeros_finite_sum_eq_degree : ∀ (k F : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field F] [Algebra k F], IsFF k F →
    ∀ x : F, Transcendental k x → {v : Place k F | v.1 x < 1}.Finite ∧
      ∑ᶠ v ∈ {v : Place k F | v.1 x < 1}, ord v x = Module.finrank k⟮x⟯ F := by
  intro k F _ _ _ _ _ hF x hx
  haveI : FiniteDimensional k⟮x⟯ F := (GlobalTheory.T.functionFieldOneVariable_transcendental_finite_and_ext k F hF).1 x hx
  set t : k⟮x⟯ := ⟨x, IntermediateField.mem_adjoin_simple_self k x⟩ with ht
  have htx : algebraMap k⟮x⟯ F t = x := rfl
  have htr : Transcendental k t := by
    intro ha
    exact hx ((IntermediateField.isAlgebraic_iff).1 ha)
  have htop : k⟮t⟯ = ⊤ := adjoin_gen_eq_top x
  have hL : IsFF k k⟮x⟯ := by
    refine ⟨t, htr, ?_⟩
    rw [htop]
    exact Module.finite_of_finrank_eq_succ (IntermediateField.finrank_top)
  obtain ⟨v0, hv0, huniq⟩ := GlobalTheory.T.existsUnique_place_ord_eq_one_of_transcendental_generator k k⟮x⟯ t htr htop
  obtain ⟨ρ, hρ⟩ := (GlobalTheory.T.functionFieldPlace_restriction_exists_pow k k⟮x⟯ F).1
  have ht0 : t ≠ 0 := by
    intro h; apply hx; rw [← htx, h, map_zero]; exact isAlgebraic_zero
  obtain ⟨hfin, hsum⟩ := GlobalTheory.T.functionFieldPlace_sum_order_eq_finrank k k⟮x⟯ F hL ρ hρ v0 t ht0 hv0
  have hset : {v : Place k F | v.1 x < 1} = {p | ρ p = v0} := by
    ext p
    obtain ⟨e, he, hpow, -⟩ := (GlobalTheory.T.functionFieldPlace_restriction_exists_pow k k⟮x⟯ F).2 ρ hρ p
    simp only [Set.mem_setOf_eq]
    change p.1 (algebraMap k⟮x⟯ F t) < 1 ↔ ρ p = v0
    rw [hpow t]
    constructor
    · intro h
      apply huniq
      by_contra hn
      exact absurd h (not_lt.2 (one_le_pow₀ (not_lt.1 hn)))
    · intro h
      rw [h]
      exact pow_lt_one₀ zero_le' (val_lt_one_of_ord_eq_one v0 t hv0) he.ne'
  rw [hset]
  exact ⟨hfin, by simpa [htx] using hsum⟩

end GlobalTheory.Nef
