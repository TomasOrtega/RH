import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaLiftHasPointAtLocalisationSamePlaceStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeStandardTwistStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.RowPointLoc

/- English proof (translation)
Establish `hm : Ideal.map (f : A →+* B) (IsLocalRing.maximalIdeal A) ≤ IsLocalRing.maximalIdeal B`. Rewrite using `[Ideal.map_le_iff_le_comap]`. Introduce `x hx`. Simplify using `only [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hx ⊢`. Introduce `hu`.

Apply `hx` to reduce the goal to its premises. Use `hu.map (f.symm : B →+* A)` as an intermediate fact. Simplify using `using this`. Use `continuous_of_continuousAt_zero (f : A →+ B) ?_` and prove the remaining obligations. Rewrite using `[ContinuousAt, map_zero]`.

Introduce `s hs`. Take `⟨n, hn⟩` from `((isAdic_iff.1 hB).2 s hs)`. Establish `hopen` using `(isAdic_iff.1 hA).1 n`. Use `Filter.mem_map.2 (Filter.mem_of_superset (hopen.mem_nhds (Ideal.zero_mem _)) ?_)` and prove the remaining obligations. Introduce `x hx`.

Apply `hn` to reduce the goal to its premises. Establish `h1 : f x ∈ Ideal.map (f : A →+* B) (IsLocalRing.maximalIdeal A ^ n)` using `Ideal.mem_map_of_mem _ hx`. Rewrite `h1` using `[Ideal.map_pow]`. Conclude with `Ideal.pow_right_mono hm n h1`.
-/
theorem continuous_of_adic {A B : Type} [CommRing A] [IsLocalRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [CommRing B] [IsLocalRing B] [TopologicalSpace B] [IsTopologicalRing B]
    (hA : IsAdic (IsLocalRing.maximalIdeal A)) (hB : IsAdic (IsLocalRing.maximalIdeal B)) (f : A ≃+* B) :
    Continuous f := by
  have hm : Ideal.map (f : A →+* B) (IsLocalRing.maximalIdeal A) ≤ IsLocalRing.maximalIdeal B := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    simp only [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hx ⊢
    intro hu
    apply hx
    have := hu.map (f.symm : B →+* A)
    simpa using this
  refine continuous_of_continuousAt_zero (f : A →+ B) ?_
  rw [ContinuousAt, map_zero]
  intro s hs
  obtain ⟨n, hn⟩ := ((isAdic_iff.1 hB).2 s hs)
  have hopen := (isAdic_iff.1 hA).1 n
  refine Filter.mem_map.2 (Filter.mem_of_superset (hopen.mem_nhds (Ideal.zero_mem _)) ?_)
  intro x hx
  apply hn
  have h1 : f x ∈ Ideal.map (f : A →+* B) (IsLocalRing.maximalIdeal A ^ n) := Ideal.mem_map_of_mem _ hx
  rw [Ideal.map_pow] at h1
  exact Ideal.pow_right_mono hm n h1

/- English proof (translation)
Introduce `hL D P h42 _ i σ hne`. Take `⟨Q, hQ⟩` from `((h42 i) σ hne).1.2`. Take `⟨i', hi', P', x', hth, hx⟩` from `GlobalTheory.T.theta_lift_has_point_at_localisation_same_place D P.M P.H.hecke P.H.av P.H.cover (GlobalTheory.T.hecke_standard_twist hL D P) i σ Q hQ`. Take `⟨hj, hw⟩` from `(D.nd.locs_mem _ _ i').1 hi'`. Establish `hl : D.nd.l i' = D.nd.l i` using `by rw [← D.nd.w_l i', ← D.nd.w_l i, hw]`.

Take `⟨φ, hφ⟩` from `P.H.hecke.sameO i' i hj hw`. Use `⟨i', hj, hl, fun w _ => P.locW_eq i' i σ w, ⟨φ, ?_, fun z => (hφ z).symm⟩, P', x', hth, hx⟩` and prove the remaining obligations. Conclude with `continuous_of_adic (D.nd.O_adic i') (D.nd.O_adic i) φ`.
-/
theorem main : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D), Formalism.MainNotions.SumRepresentations.Conclusion42 D → Formalism.MainNotions.SumRepresentations.Conclusion41 D → RowPoint D.nd D.naut := by
  intro hL D P h42 _ i σ hne
  obtain ⟨Q, hQ⟩ := ((h42 i) σ hne).1.2
  obtain ⟨i', hi', P', x', hth, hx⟩ :=
    GlobalTheory.T.theta_lift_has_point_at_localisation_same_place D P.M P.H.hecke P.H.av P.H.cover (GlobalTheory.T.hecke_standard_twist hL D P) i σ Q hQ
  obtain ⟨hj, hw⟩ := (D.nd.locs_mem _ _ i').1 hi'
  have hl : D.nd.l i' = D.nd.l i := by rw [← D.nd.w_l i', ← D.nd.w_l i, hw]
  obtain ⟨φ, hφ⟩ := P.H.hecke.sameO i' i hj hw
  refine ⟨i', hj, hl, fun w _ => P.locW_eq i' i σ w, ⟨φ, ?_, fun z => (hφ z).symm⟩, P', x', hth, hx⟩
  exact continuous_of_adic (D.nd.O_adic i') (D.nd.O_adic i) φ

end GlobalTheory.RowPointLoc
