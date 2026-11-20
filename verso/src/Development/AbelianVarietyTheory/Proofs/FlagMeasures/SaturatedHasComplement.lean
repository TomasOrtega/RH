import Mathlib

namespace GlobalTheory.SaturatedSublatticeComplement

universe u_1 u_2

open Module

/- English proof (translation)
Set `N' : Submodule R M` to `N.comap M.subtype`. Use `haveI : Module.Finite R M := Module.Finite.iff_fg.mpr hM`. Use `haveI : IsTorsionFree R (M ⧸ N') := by`. Use `Module.IsTorsionFree.of_smul_eq_zero ?_` and prove the remaining obligations. Introduce `r q hq`.

Distinguish the cases in `hr : r = 0`. Conclude with `Or.inl hr`. Use `right`. Take `⟨m, rfl⟩` from `N'.mkQ_surjective q`. Establish `h1 : r • m ∈ N'`.

Rewrite using `[← Submodule.Quotient.mk_eq_zero]`. Simplify using `using hq`. Establish `h2 : (m : V) ∈ N` using `hsat r m hr m.2 (by simpa [N'] using h1)`. Conclude with `(Submodule.Quotient.mk_eq_zero N').mpr (by simpa [N'] using h2)`. Use `haveI : Module.FinitePresentation R (M ⧸ N') := Module.finitePresentation_of_finite R _`.

Use `haveI : Module.Projective R (M ⧸ N') := Module.Flat.projective_of_finitePresentation`. Take `⟨g, hg⟩` from `Module.projective_lifting_property N'.mkQ LinearMap.id N'.mkQ_surjective`. Establish `hg' : ∀ q, N'.mkQ (g q) = q` using `fun q => LinearMap.congr_fun hg q`. Use `⟨(LinearMap.range g).map M.subtype, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[eq_bot_iff]`.

Introduce and unpack `x ⟨hxA, hxN⟩`. Take `⟨_, ⟨q, rfl⟩, rfl⟩` from `hxA`. Establish `hmem : g q ∈ N'` using `by simpa [N'] using hxN`. Establish `hq0 : q = 0`. Rewrite using `[← hg' q]`.

Conclude with `(Submodule.Quotient.mk_eq_zero N').mpr hmem`. Simplify using `[hq0]`. Apply `le_antisymm` to reduce the goal to its premises. Conclude with `sup_le (by`. Introduce and unpack `x ⟨y, -, rfl⟩`.

Conclude with `y.2) hNM`. Introduce `x hx`. Set `m : M` to `⟨x, hx⟩`. Establish `hd : m - g (N'.mkQ m) ∈ N'`. Rewrite using `[← Submodule.Quotient.mk_eq_zero]`.

Use `hg' (N'.mkQ m)` as an intermediate fact. Simplify using `only [Submodule.mkQ_apply] at this ⊢`. Rewrite using `[Submodule.Quotient.mk_sub, this, sub_self]`. Establish `hx' : x = (g (N'.mkQ m) : V) + ((m - g (N'.mkQ m) : M) : V)` using `by simp [m]`. Rewrite using `[hx']`.

Conclude with `Submodule.add_mem_sup ⟨g (N'.mkQ m), ⟨_, rfl⟩, rfl⟩ (by simpa [N'] using hd)`.
-/
theorem saturated_has_complement {R : Type u_1} {V : Type u_2} [CommRing R] [IsDedekindDomain R]
    [AddCommGroup V] [Module R V] (N M : Submodule R V) (hNM : N ≤ M) (hM : M.FG)
    (hsat : ∀ (r : R) (y : V), r ≠ 0 → y ∈ M → r • y ∈ N → y ∈ N) :
    ∃ A : Submodule R V, A ⊓ N = ⊥ ∧ A ⊔ N = M := by
  classical
  let N' : Submodule R M := N.comap M.subtype
  haveI : Module.Finite R M := Module.Finite.iff_fg.mpr hM
  haveI : IsTorsionFree R (M ⧸ N') := by
    refine Module.IsTorsionFree.of_smul_eq_zero ?_
    intro r q hq
    by_cases hr : r = 0
    · exact Or.inl hr
    right
    obtain ⟨m, rfl⟩ := N'.mkQ_surjective q
    have h1 : r • m ∈ N' := by
      rw [← Submodule.Quotient.mk_eq_zero]
      simpa using hq
    have h2 : (m : V) ∈ N := hsat r m hr m.2 (by simpa [N'] using h1)
    exact (Submodule.Quotient.mk_eq_zero N').mpr (by simpa [N'] using h2)
  haveI : Module.FinitePresentation R (M ⧸ N') := Module.finitePresentation_of_finite R _
  haveI : Module.Projective R (M ⧸ N') := Module.Flat.projective_of_finitePresentation
  obtain ⟨g, hg⟩ := Module.projective_lifting_property N'.mkQ LinearMap.id N'.mkQ_surjective
  have hg' : ∀ q, N'.mkQ (g q) = q := fun q => LinearMap.congr_fun hg q
  refine ⟨(LinearMap.range g).map M.subtype, ?_, ?_⟩
  · rw [eq_bot_iff]
    rintro x ⟨hxA, hxN⟩
    obtain ⟨_, ⟨q, rfl⟩, rfl⟩ := hxA
    have hmem : g q ∈ N' := by simpa [N'] using hxN
    have hq0 : q = 0 := by
      rw [← hg' q]
      exact (Submodule.Quotient.mk_eq_zero N').mpr hmem
    simp [hq0]
  · apply le_antisymm
    · exact sup_le (by
        rintro x ⟨y, -, rfl⟩
        exact y.2) hNM
    · intro x hx
      let m : M := ⟨x, hx⟩
      have hd : m - g (N'.mkQ m) ∈ N' := by
        rw [← Submodule.Quotient.mk_eq_zero]
        have := hg' (N'.mkQ m)
        simp only [Submodule.mkQ_apply] at this ⊢
        rw [Submodule.Quotient.mk_sub, this, sub_self]
      have hx' : x = (g (N'.mkQ m) : V) + ((m - g (N'.mkQ m) : M) : V) := by simp [m]
      rw [hx']
      exact Submodule.add_mem_sup ⟨g (N'.mkQ m), ⟨_, rfl⟩, rfl⟩ (by simpa [N'] using hd)

/- English proof (translation)
Introduce `N M h1 h2 h3` and use `saturated_has_complement N M h1 h2 h3`.
-/
theorem main : ∀ {R : Type u_1} {V : Type u_2} [inst : CommRing R] [IsDedekindDomain R]
    [inst_2 : AddCommGroup V] [inst_3 : Module R V] (N M : Submodule R V), N ≤ M →
    Submodule.FG M → (∀ (r : R) (y : V), r ≠ (0 : R) → y ∈ M → r • y ∈ N → y ∈ N) →
    ∃ (A : Submodule R V), A ⊓ N = ⊥ ∧ A ⊔ N = M :=
  fun N M h1 h2 h3 => saturated_has_complement N M h1 h2 h3

end GlobalTheory.SaturatedSublatticeComplement
