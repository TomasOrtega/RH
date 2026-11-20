import Mathlib
open Pointwise

namespace GlobalTheory

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Rewrite using `[pow_zero, Ideal.span_singleton_one]`. Use `haveI : Subsingleton (O ⧸ (⊤ : Ideal O)) := Ideal.Quotient.subsingleton_iff.mpr rfl`. Rewrite using `[Module.length_eq_zero]`.

Conclude with `bot_le`. Consider the case `succ n ih => set S : Submodule O O := Ideal.span {p ^ (n + 1)} with hS set T : Submodule O O := Ideal.span {p ^ n} with hT`. Establish `hST : S ≤ T` using `Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow p n.le_succ)`. Set `v : O ⧸ S` to `S.mkQ (p ^ n)`. Establish `hker : (Ideal.span {p} : Submodule O O) ≤ LinearMap.ker (LinearMap.toSpanSingleton O (O ⧸ S) v)`.

Introduce `x hx`. Take `⟨c, rfl⟩` from `Ideal.mem_span_singleton'.mp hx`. Rewrite using `[LinearMap.mem_ker, LinearMap.toSpanSingleton_apply]`. Simplify using `only [v, Submodule.mkQ_apply, ← Submodule.Quotient.mk_smul, smul_eq_mul]`. Rewrite using `[Submodule.Quotient.mk_eq_zero, hS, Ideal.mem_span_singleton']`.

Conclude with `⟨c, by ring⟩`. Set `ψ : (O ⧸ (Ideal.span {p} : Submodule O O)) →ₗ[O] O ⧸ S` to `(Ideal.span {p} : Submodule O O).liftQ (LinearMap.toSpanSingleton O (O ⧸ S) v) hker`. Set `N : Submodule O (O ⧸ S)` to `LinearMap.range ψ`. Establish `hN : N = T.map S.mkQ`. Simplify using `only [N, ψ, Submodule.range_liftQ, hT, Ideal.span, Submodule.map_span, Set.image_singleton]`.

Rewrite using `[← LinearMap.span_singleton_eq_range]`. Establish `h1` using `Module.length_eq_add_of_exact N.subtype N.mkQ N.injective_subtype N.mkQ_surjective (LinearMap.exact_subtype_mkQ N)`. Establish `hle : Module.length O N ≤ Module.length O (O ⧸ Ideal.span {p})` using `Module.length_le_of_surjective ψ.rangeRestrict ψ.surjective_rangeRestrict`. Establish `heq : Module.length O ((O ⧸ S) ⧸ N) = Module.length O (O ⧸ Ideal.span {p ^ n})`. Rewrite using `[hN]`.

Conclude with `(Submodule.quotientQuotientEquivQuotient S T hST).length_eq`. Express the relevant statement in the definitionally equal form `Module.length O (O ⧸ S) ≤ _`. Rewrite using `[h1, heq]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem length_quotient_span_pow_le (O : Type) [CommRing O] (p : O) (n : ℕ) :
    Module.length O (O ⧸ Ideal.span {p ^ n}) ≤ (n : ℕ∞) * Module.length O (O ⧸ Ideal.span {p}) := by
  induction n with
  | zero =>
    rw [pow_zero, Ideal.span_singleton_one]
    haveI : Subsingleton (O ⧸ (⊤ : Ideal O)) := Ideal.Quotient.subsingleton_iff.mpr rfl
    rw [Module.length_eq_zero]
    exact bot_le
  | succ n ih =>
    set S : Submodule O O := Ideal.span {p ^ (n + 1)} with hS
    set T : Submodule O O := Ideal.span {p ^ n} with hT
    have hST : S ≤ T := Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow p n.le_succ)
    let v : O ⧸ S := S.mkQ (p ^ n)
    have hker : (Ideal.span {p} : Submodule O O) ≤ LinearMap.ker (LinearMap.toSpanSingleton O (O ⧸ S) v) := by
      intro x hx
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hx
      rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply]
      simp only [v, Submodule.mkQ_apply, ← Submodule.Quotient.mk_smul, smul_eq_mul]
      rw [Submodule.Quotient.mk_eq_zero, hS, Ideal.mem_span_singleton']
      exact ⟨c, by ring⟩
    let ψ : (O ⧸ (Ideal.span {p} : Submodule O O)) →ₗ[O] O ⧸ S :=
      (Ideal.span {p} : Submodule O O).liftQ (LinearMap.toSpanSingleton O (O ⧸ S) v) hker
    let N : Submodule O (O ⧸ S) := LinearMap.range ψ
    have hN : N = T.map S.mkQ := by
      simp only [N, ψ, Submodule.range_liftQ, hT, Ideal.span, Submodule.map_span, Set.image_singleton]
      rw [← LinearMap.span_singleton_eq_range]
    have h1 := Module.length_eq_add_of_exact N.subtype N.mkQ N.injective_subtype N.mkQ_surjective
      (LinearMap.exact_subtype_mkQ N)
    have hle : Module.length O N ≤ Module.length O (O ⧸ Ideal.span {p}) :=
      Module.length_le_of_surjective ψ.rangeRestrict ψ.surjective_rangeRestrict
    have heq : Module.length O ((O ⧸ S) ⧸ N) = Module.length O (O ⧸ Ideal.span {p ^ n}) := by
      rw [hN]
      exact (Submodule.quotientQuotientEquivQuotient S T hST).length_eq
    change Module.length O (O ⧸ S) ≤ _
    rw [h1, heq]
    calc Module.length O N + Module.length O (O ⧸ Ideal.span {p ^ n})
        ≤ Module.length O (O ⧸ Ideal.span {p}) + (n : ℕ∞) * Module.length O (O ⧸ Ideal.span {p}) :=
          add_le_add hle ih
      _ = ((n + 1 : ℕ) : ℕ∞) * Module.length O (O ⧸ Ideal.span {p}) := by
          push_cast; ring

/- English proof (translation)
Introduce `O _ p n` and use `length_quotient_span_pow_le O p n`.
-/
theorem main : ∀ (O : Type) [CommRing O] (p : O) (n : ℕ),
    Module.length O (O ⧸ Ideal.span {p ^ n}) ≤ (n : ℕ∞) * Module.length O (O ⧸ Ideal.span {p}) :=
  fun O _ p n => length_quotient_span_pow_le O p n

end GlobalTheory
