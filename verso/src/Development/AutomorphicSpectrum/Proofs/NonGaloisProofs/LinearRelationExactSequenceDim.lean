import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.ChainRows
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

namespace GlobalTheory.CompanionTheory.InertiaEigenvalues

/- English proof (translation)
Introduce `k _ H M N Q _ _ _ _ _ _ _ _ _ _ a b R hinj hex hN hQ h0 hb`. Set `p1 : R →ₗ[k] N` to `(LinearMap.fst k N Q).comp R.subtype`. Set `p2 : R →ₗ[k] Q` to `(LinearMap.snd k N Q).comp R.subtype`. Establish `p1bij : Function.Bijective p1`. Prove the components needed by the constructor for the conclusion.

Rewrite using `[injective_iff_map_eq_zero]`. Introduce and unpack `⟨⟨n, q⟩, hr⟩ h`. Establish `hn : n = 0` using `h`. Substitute `hn` using the available equality. Establish `hq : q = 0` using `h0 q hr`.

Substitute `hq` using the available equality. Both sides reduce to the same expression. Introduce `n`. Take `⟨q, hq⟩` from `hN n`. Conclude with `⟨⟨(n, q), hq⟩, rfl⟩`.

Set `e : R ≃ₗ[k] N` to `LinearEquiv.ofBijective p1 p1bij`. Set `δ : N →ₗ[k] Q` to `p2.comp e.symm.toLinearMap`. Establish `hδ : ∀ x : R, δ (p1 x) = p2 x`. Introduce `x`. Establish `h : e.symm (p1 x) = x` using `e.symm_apply_apply x`.

Use `show p2 (e.symm (p1 x)) = p2 x`. Rewrite using `[h]`. Establish `hsurj : Function.Surjective δ`. Introduce `q`. Take `⟨n, hn⟩` from `hQ q`.

Conclude with `⟨n, hδ ⟨(n, q), hn⟩⟩`. Establish `hker : LinearMap.ker δ = LinearMap.range b`. Use extensionality with `n`. Rewrite using `[LinearMap.mem_ker, ← hb n]`. Take `⟨q, hq⟩` from `hN n`.

Establish `h1 : δ n = q` using `hδ ⟨(n, q), hq⟩`. Rewrite using `[h1]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `rfl`. Conclude with `hq`.

Introduce `h`. Establish `h2 : ((n, q) - (n, 0) : N × Q) ∈ R` using `R.sub_mem hq h`. Establish `h3 : ((n, q) - (n, 0) : N × Q) = (0, q)` using `by simp`. Rewrite `h2` using `[h3]`. Conclude with `h0 q h2`.

Use `⟨Module.Finite.of_surjective δ hsurj, ?_⟩` and prove the remaining obligations. Establish `e1` using `LinearMap.finrank_range_add_finrank_ker δ`. Establish `e2` using `LinearMap.finrank_range_add_finrank_ker b`. Rewrite `e1` using `[LinearMap.range_eq_top.2 hsurj, finrank_top, hker]`. Rewrite `e2` using `[← hex]`.

Establish `e3 : finrank k (LinearMap.range a) = finrank k H` using `LinearMap.finrank_range_of_inj hinj`. Rewrite `e2` using `[e3]`. Use linear arithmetic over natural numbers and integers.
-/
theorem finrank_along_relation : ∀ (k : Type) [Field k] (H M N Q : Type) [AddCommGroup H] [Module k H] [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N] [AddCommGroup Q] [Module k Q] [Module.Finite k M] [Module.Finite k N] (a : H →ₗ[k] M) (b : M →ₗ[k] N) (R : Submodule k (N × Q)), Function.Injective a → LinearMap.range a = LinearMap.ker b → (∀ n, ∃ q, (n, q) ∈ R) → (∀ q, ∃ n, (n, q) ∈ R) → (∀ q, (0, q) ∈ R → q = 0) → (∀ n, (n, 0) ∈ R ↔ n ∈ LinearMap.range b) → Module.Finite k Q ∧ finrank k Q + finrank k M = finrank k H + finrank k N := by
  intro k _ H M N Q _ _ _ _ _ _ _ _ _ _ a b R hinj hex hN hQ h0 hb
  let p1 : R →ₗ[k] N := (LinearMap.fst k N Q).comp R.subtype
  let p2 : R →ₗ[k] Q := (LinearMap.snd k N Q).comp R.subtype
  have p1bij : Function.Bijective p1 := by
    constructor
    · rw [injective_iff_map_eq_zero]
      rintro ⟨⟨n, q⟩, hr⟩ h
      have hn : n = 0 := h
      subst hn
      have hq : q = 0 := h0 q hr
      subst hq
      rfl
    · intro n
      obtain ⟨q, hq⟩ := hN n
      exact ⟨⟨(n, q), hq⟩, rfl⟩
  let e : R ≃ₗ[k] N := LinearEquiv.ofBijective p1 p1bij
  let δ : N →ₗ[k] Q := p2.comp e.symm.toLinearMap
  have hδ : ∀ x : R, δ (p1 x) = p2 x := by
    intro x
    have h : e.symm (p1 x) = x := e.symm_apply_apply x
    show p2 (e.symm (p1 x)) = p2 x
    rw [h]
  have hsurj : Function.Surjective δ := by
    intro q
    obtain ⟨n, hn⟩ := hQ q
    exact ⟨n, hδ ⟨(n, q), hn⟩⟩
  have hker : LinearMap.ker δ = LinearMap.range b := by
    ext n
    rw [LinearMap.mem_ker, ← hb n]
    obtain ⟨q, hq⟩ := hN n
    have h1 : δ n = q := hδ ⟨(n, q), hq⟩
    rw [h1]
    constructor
    · rintro rfl
      exact hq
    · intro h
      have h2 : ((n, q) - (n, 0) : N × Q) ∈ R := R.sub_mem hq h
      have h3 : ((n, q) - (n, 0) : N × Q) = (0, q) := by simp
      rw [h3] at h2
      exact h0 q h2
  refine ⟨Module.Finite.of_surjective δ hsurj, ?_⟩
  have e1 := LinearMap.finrank_range_add_finrank_ker δ
  have e2 := LinearMap.finrank_range_add_finrank_ker b
  rw [LinearMap.range_eq_top.2 hsurj, finrank_top, hker] at e1
  rw [← hex] at e2
  have e3 : finrank k (LinearMap.range a) = finrank k H := LinearMap.finrank_range_of_inj hinj
  rw [e3] at e2
  omega

end GlobalTheory.CompanionTheory.InertiaEigenvalues
