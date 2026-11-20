import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.MatchSmulAlt

noncomputable section

open MeasureTheory PositivityTheory.Rg.Tf.Geo

namespace UpperTheory.Gal.InertialTypesAlt.L

/- English proof (translation)
Unfold `quotInt`. Use `split_ifs with h`. Simplify using `only [Pi.smul_apply, smul_eq_mul, mul_assoc]`. Conclude with `integral_const_mul _ _`. Simplify using the standard rewrite rules.
-/
private theorem quotInt_smul {G T X : Type*} [Group G] [MeasurableSpace G] [MeasurableSpace T] [MeasurableSpace X]
    (μ : Measure X) (u : X → G) (j : T → G) (ν : Measure T) (c : ℂ) (Φ : X → ℂ) :
    quotInt μ u j ν (c • Φ) = c * quotInt μ u j ν Φ := by
  unfold quotInt
  split_ifs with h
  · simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]
    exact integral_const_mul _ _
  · simp

/- English proof (translation)
Unfold `orb`. Conclude with `quotInt_smul μ id (fun t : Subgroup.centralizer {γ} => (t : GL (Fin n) R)) ν c (fun x => f (x⁻¹ * γ * x))`.
-/
private theorem orb_smul {n : ℕ} {R : Type*} [CommRing R] [TopologicalSpace R] [MeasurableSpace (GL (Fin n) R)]
    (μ : Measure (GL (Fin n) R)) (γ : GL (Fin n) R) (ν : Measure (Subgroup.centralizer {γ})) (c : ℂ)
    (f : GL (Fin n) R → ℂ) : orb μ γ ν (c • f) = c * orb μ γ ν f := by
  unfold orb
  exact quotInt_smul μ id (fun t : Subgroup.centralizer {γ} => (t : GL (Fin n) R)) ν c
    (fun x => f (x⁻¹ * γ * x))

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ n v c hc φ f h`. Introduce `_ _ _ _ mE mF h1 h2 h3 h4 γ hγ ν hν`. Take `⟨hA, hB⟩` from `h mE mF h1 h2 h3 h4 γ hγ ν hν`. Use `⟨fun δ hδ => ?_, fun hn => ?_⟩` and prove the remaining obligations. Rewrite using `[hA δ hδ, one_mul, orb_smul]`.

Use `hB hn` as an intermediate fact. Rewrite `this` using `[orb_smul]`. Conclude with `(mul_eq_zero.1 this).resolve_left hc`.
-/
theorem matchSmul : MatchSmul := by
  intro F E _ _ _ _ _ σ n v c hc φ f h
  intro _ _ _ _ mE mF h1 h2 h3 h4 γ hγ ν hν
  obtain ⟨hA, hB⟩ := h mE mF h1 h2 h3 h4 γ hγ ν hν
  refine ⟨fun δ hδ => ?_, fun hn => ?_⟩
  · rw [hA δ hδ, one_mul, orb_smul]
  · have := hB hn
    rw [orb_smul] at this
    exact (mul_eq_zero.1 this).resolve_left hc

end UpperTheory.Gal.InertialTypesAlt.L

end
