import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsExcisionNbhdSelf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyProdRingProjectionsBijectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalVanishingCohomologyStatement
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory.EtC.CurveNbhdExcision

/- English proof (translation)
Use `⟨fun a b => ?_⟩` and prove the remaining obligations. Establish `hfs : RingHom.fst Z Z = RingHom.snd Z Z` using `RingHom.ext fun _ => Subsingleton.elim _ _`. Establish `key : ∀ z : Ht q (sp Z) n i, z = 0`. Introduce `z`. Take `⟨y, hy⟩` from `(GlobalTheory.T.etaleCohomology_prod_ring_projections_bijective q Z Z n i).2 (z, 0)`.

Simplify using `only [Prod.mk.injEq] at hy`. Rewrite using `[← hy.1, ← hy.2, hfs]`. Rewrite using `[key a, key b]`.
-/
theorem ht_subsingleton_of_subsingleton (q : ℕ) (Z : Type) [CommRing Z] [Subsingleton Z] (n i : ℤ) :
    Subsingleton (Ht q (sp Z) n i) := by
  refine ⟨fun a b => ?_⟩
  have hfs : RingHom.fst Z Z = RingHom.snd Z Z := RingHom.ext fun _ => Subsingleton.elim _ _
  have key : ∀ z : Ht q (sp Z) n i, z = 0 := by
    intro z
    obtain ⟨y, hy⟩ := (GlobalTheory.T.etaleCohomology_prod_ring_projections_bijective q Z Z n i).2 (z, 0)
    simp only [Prod.mk.injEq] at hy
    rw [← hy.1, ← hy.2, hfs]
  rw [key a, key b]

/- English proof (translation)
Establish `h : IsUnit (algebraMap B (Localization.Away (0 : B)) 0)` using `IsLocalization.Away.algebraMap_isUnit _`. Rewrite `h` using `[map_zero, isUnit_zero_iff]`. Conclude with `subsingleton_of_zero_eq_one h`.
-/
theorem away_zero_subsingleton (B : Type) [CommRing B] : Subsingleton (Localization.Away (0 : B)) := by
  have h : IsUnit (algebraMap B (Localization.Away (0 : B)) 0) := IsLocalization.Away.algebraMap_isUnit _
  rw [map_zero, isUnit_zero_iff] at h
  exact subsingleton_of_zero_eq_one h

/- English proof (translation)
Introduce `q _ k B _ _ _ _ _ _ hq f hf n i hn x`. Distinguish the cases in `hu : IsUnit f`. Use `haveI := away_zero_subsingleton B`. Use `⟨Localization.Away (0 : B), inferInstance, inferInstance, ⟨Algebra.Etale.of_isLocalizationAway 0, ?_, ?_⟩, ?_⟩` and prove the remaining obligations. Introduce `a'`.

Conclude with `⟨0, by rw [Subsingleton.elim (a' - _) 0]; exact Ideal.zero_mem _⟩`. Introduce `a _`. Rewrite using `[Ideal.span_singleton_eq_top.mpr hu]`. Conclude with `Submodule.mem_top`. Use `haveI := ht_subsingleton_of_subsingleton q (Localization.Away (0 : B)) n i`.

Conclude with `Subsingleton.elim _ _`. Take `⟨A', i1, i2, i3, hN, hx⟩` from `GlobalTheory.T.etale_local_vanishing_cohomology q k B hq f hf hu n i (by omega) x`. Conclude with `⟨A', i1, i2, ⟨i3, hN.1, hN.2⟩, hx⟩`.
-/
theorem main : ∀ (q : ℕ) [NeZero q] (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B], IsUnit (q : k) → ∀ f : B, f ≠ 0 → ∀ (n i : ℤ), 0 < n → ∀ x : Ht q (sp B) n i, ∃ (A' : Type) (_ : CommRing A') (_ : Algebra B A'), IsExcisionNbhd B A' f ∧ pull _ (spMap (algebraMap B A')) _ _ x = 0 := by
  intro q _ k B _ _ _ _ _ _ hq f hf n i hn x
  by_cases hu : IsUnit f
  · haveI := away_zero_subsingleton B
    refine ⟨Localization.Away (0 : B), inferInstance, inferInstance, ⟨Algebra.Etale.of_isLocalizationAway 0, ?_, ?_⟩, ?_⟩
    · intro a'
      exact ⟨0, by rw [Subsingleton.elim (a' - _) 0]; exact Ideal.zero_mem _⟩
    · intro a _
      rw [Ideal.span_singleton_eq_top.mpr hu]
      exact Submodule.mem_top
    · haveI := ht_subsingleton_of_subsingleton q (Localization.Away (0 : B)) n i
      exact Subsingleton.elim _ _
  · obtain ⟨A', i1, i2, i3, hN, hx⟩ := GlobalTheory.T.etale_local_vanishing_cohomology q k B hq f hf hu n i (by omega) x
    exact ⟨A', i1, i2, ⟨i3, hN.1, hN.2⟩, hx⟩

end GlobalTheory.EtC.CurveNbhdExcision
