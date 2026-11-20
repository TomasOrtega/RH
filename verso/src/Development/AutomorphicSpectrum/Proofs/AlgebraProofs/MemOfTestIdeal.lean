import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LieLatticeData
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LocallyFreeTestPointMembershipStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LocFreeMapMkQIff

open GlobalTheory.CompanionTheory.Ar.Num

namespace GlobalTheory.CompanionTheory.Ar.Num.HaTest

/- English proof (translation)
Introduce `o Ω _ _ _ R p hp hp0 hN hF hI L hL v hm htest`. Set `e : Ω ≃ₗ[Ω] (Unit → Ω)` to `(LinearEquiv.funUnique Unit Ω Ω).symm`. Establish `hL' : LocFree R 1 (L.map e.toLinearMap.toAddMonoidHom)` using `LatticeGoodness.locFree_map_equiv R e hL`. Establish `hmem : ∀ x : Ω, e x ∈ L.map e.toLinearMap.toAddMonoidHom ↔ x ∈ L`. Introduce `x`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, hyx⟩`. Establish `: y = x` using `e.injective hyx`. Rewrite using `[← this]` and apply the resulting hypothesis. Introduce `hx`.

Conclude with `⟨x, hx, rfl⟩`. Use `(hmem v).1 (GlobalTheory.T.locally_free_test_point_membership R p hp hp0 hN hF hI 1 _ hL' (e v) ?_ ?_)` and prove the remaining obligations. Take `⟨m, hm⟩` from `hm`. Use `⟨m, ?_⟩` and prove the remaining obligations. Establish `: (p : Ω) ^ m • e v = e ((p : Ω) ^ m * v)`.

Rewrite using `[← smul_eq_mul, map_smul]`. Rewrite using `[this]`. Conclude with `(hmem _).2 hm`. Introduce `C _ _ _ _ RC ht`. Set `g : C →+ (Unit → C)` to `(LinearEquiv.funUnique Unit C C).symm.toLinearMap.toAddMonoidHom`.

Establish `hg : bcMap Ω C Unit (e v) = g (algebraMap Ω C v)`. Use function extensionality and compare the values at `u`. Simplify using `[bcMap, e, g]`. Rewrite using `[hg]`. Establish `h1` using `AddSubgroup.mem_map_of_mem g (htest C RC ht)`.

Unfold `spanOver at h1 ⊢`. Rewrite `h1` using `[AddMonoidHom.map_closure]`. Use `(AddSubgroup.closure_mono ?_) h1` and prove the remaining obligations. Introduce and unpack `_ ⟨_, ⟨a, ha, _, ⟨x, hx, rfl⟩, rfl⟩, rfl⟩`. Use `⟨a, ha, bcMap Ω C Unit (e x), ⟨e x, (hmem x).2 hx, rfl⟩, ?_⟩` and prove the remaining obligations.

Use function extensionality and compare the values at `u`. Simplify using `[bcMap, e, g]`.
-/
theorem mem_of_test_ideal : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω) (p : ℕ), p.Prime → (p : Ω) ≠ 0 → IsNoetherianRing R → IsFractionRing R Ω → IsIntegrallyClosedIn R Ω → ∀ (L : AddSubgroup Ω), LocFree R 1 L → ∀ v : Ω, (∃ m : ℕ, (p : Ω) ^ m * v ∈ L) → (∀ (C : Type) [Field C] [Algebra o C] [Algebra Ω C] [IsScalarTower o Ω C] (RC : Subalgebra o C), IsTestPt p R RC → algebraMap Ω C v ∈ spanOver RC (algebraMap Ω C '' L)) → v ∈ L := by
  intro o Ω _ _ _ R p hp hp0 hN hF hI L hL v hm htest
  let e : Ω ≃ₗ[Ω] (Unit → Ω) := (LinearEquiv.funUnique Unit Ω Ω).symm
  have hL' : LocFree R 1 (L.map e.toLinearMap.toAddMonoidHom) :=
    LatticeGoodness.locFree_map_equiv R e hL
  have hmem : ∀ x : Ω, e x ∈ L.map e.toLinearMap.toAddMonoidHom ↔ x ∈ L := by
    intro x
    constructor
    · rintro ⟨y, hy, hyx⟩
      have : y = x := e.injective hyx
      rwa [← this]
    · intro hx
      exact ⟨x, hx, rfl⟩
  refine (hmem v).1 (GlobalTheory.T.locally_free_test_point_membership R p hp hp0 hN hF hI 1 _ hL' (e v) ?_ ?_)
  · obtain ⟨m, hm⟩ := hm
    refine ⟨m, ?_⟩
    have : (p : Ω) ^ m • e v = e ((p : Ω) ^ m * v) := by
      rw [← smul_eq_mul, map_smul]
    rw [this]
    exact (hmem _).2 hm
  · intro C _ _ _ _ RC ht
    let g : C →+ (Unit → C) :=
      (LinearEquiv.funUnique Unit C C).symm.toLinearMap.toAddMonoidHom
    have hg : bcMap Ω C Unit (e v) = g (algebraMap Ω C v) := by
      funext u
      simp [bcMap, e, g]
    rw [hg]
    have h1 := AddSubgroup.mem_map_of_mem g (htest C RC ht)
    unfold spanOver at h1 ⊢
    rw [AddMonoidHom.map_closure] at h1
    refine (AddSubgroup.closure_mono ?_) h1
    rintro _ ⟨_, ⟨a, ha, _, ⟨x, hx, rfl⟩, rfl⟩, rfl⟩
    refine ⟨a, ha, bcMap Ω C Unit (e x), ⟨e x, (hmem x).2 hx, rfl⟩, ?_⟩
    funext u
    simp [bcMap, e, g]

end GlobalTheory.CompanionTheory.Ar.Num.HaTest
