import Mathlib

namespace GlobalTheory.SaturatedComplement

/- English proof (translation)
Establish `htf : Module.IsTorsionFree O (M ⧸ N)`. Rewrite using `[Module.isTorsionFree_iff_smul_eq_zero]`. Introduce `a q hq`. Take `⟨x, rfl⟩` from `Submodule.Quotient.mk_surjective N q`. Distinguish the cases in `ha : a = 0`.

Conclude with `Or.inl ha`. Use `right`. Rewrite `hq` using `[← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]`. Rewrite using `[Submodule.Quotient.mk_eq_zero]`. Conclude with `h a x ha hq`.

Take `⟨s, hs⟩` from `Module.projective_lifting_property N.mkQ LinearMap.id N.mkQ_surjective`. Establish `hsec : ∀ q, N.mkQ (s q) = q` using `fun q => by`. Simplify using `using LinearMap.congr_fun hs q`. Use `⟨LinearMap.range s, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Submodule.disjoint_def]`.

Introduce and unpack `x hxN ⟨q, rfl⟩`. Establish `hq : q = 0`. Rewrite using `[← hsec q, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]`. Conclude with `hxN`. Rewrite using `[hq, map_zero]`.

Rewrite using `[codisjoint_iff, eq_top_iff]`. Introduce `x _`. Establish `hx : x - s (N.mkQ x) ∈ N`. Rewrite using `[← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub, ← Submodule.mkQ_apply, ← Submodule.mkQ_apply, hsec, sub_self]`. Use `Submodule.add_mem_sup hx (LinearMap.mem_range_self s (N.mkQ x))` as an intermediate fact.

Simplify using `using this`.
-/
theorem exists_isCompl_of_saturated {O M : Type} [CommRing O] [IsDomain O]
    [IsPrincipalIdealRing O] [AddCommGroup M] [Module O M] [Module.Finite O M]
    (N : Submodule O M) (h : ∀ (a : O) (x : M), a ≠ (0 : O) → a • x ∈ N → x ∈ N) :
    ∃ C : Submodule O M, IsCompl N C := by
  have htf : Module.IsTorsionFree O (M ⧸ N) := by
    rw [Module.isTorsionFree_iff_smul_eq_zero]
    intro a q hq
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective N q
    by_cases ha : a = 0
    · exact Or.inl ha
    · right
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hq
      rw [Submodule.Quotient.mk_eq_zero]
      exact h a x ha hq
  obtain ⟨s, hs⟩ := Module.projective_lifting_property N.mkQ LinearMap.id N.mkQ_surjective
  have hsec : ∀ q, N.mkQ (s q) = q := fun q => by
    simpa using LinearMap.congr_fun hs q
  refine ⟨LinearMap.range s, ?_, ?_⟩
  · rw [Submodule.disjoint_def]
    rintro x hxN ⟨q, rfl⟩
    have hq : q = 0 := by
      rw [← hsec q, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact hxN
    rw [hq, map_zero]
  · rw [codisjoint_iff, eq_top_iff]
    intro x _
    have hx : x - s (N.mkQ x) ∈ N := by
      rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub, ← Submodule.mkQ_apply,
        ← Submodule.mkQ_apply, hsec, sub_self]
    have := Submodule.add_mem_sup hx (LinearMap.mem_range_self s (N.mkQ x))
    simpa using this

end GlobalTheory.SaturatedComplement
