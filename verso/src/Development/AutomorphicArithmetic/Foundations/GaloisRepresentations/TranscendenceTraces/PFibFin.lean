import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Extract witnesses or component facts from the available result. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Both sides reduce to the same expression.
-/
private theorem fib_spec_finite (Ω B : Type) [Field Ω] [CommRing B] [Algebra Ω B] [Module.Finite Ω B] :
    (fib (Ω := Ω) (Spec.map (CommRingCat.ofHom (algebraMap Ω B))) (𝟙 (gp Ω))).Finite := by
  apply (Set.finite_range (fun g : B →ₐ[Ω] Ω => Spec.map (CommRingCat.ofHom (g : B →+* Ω)))).subset
  intro z hz
  have hz' : z ≫ Spec.map (CommRingCat.ofHom (algebraMap Ω B)) = 𝟙 _ := hz
  obtain ⟨φ, rfl⟩ : ∃ φ, Spec.map φ = z := ⟨Spec.preimage z, Spec.map_preimage z⟩
  rw [← Spec.map_comp, ← Spec.map_id] at hz'
  have h2 := Spec.map_injective hz'
  refine ⟨{ φ.hom with commutes' := fun c => ?_ }, ?_⟩
  · have := congrArg (fun g => g.hom c) h2
    simpa using this
  · rfl

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. Replace the relevant objects with their definitions. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem UpperTheory.Gal.TranscendenceTraces.fibFin_of :
    Chart → FibFin := by
  intro hC
  unfold Chart at hC
  unfold FibFin
  intro V U r _ Ω _ x
  obtain ⟨B, iB, iAB, v, hfin, hpb⟩ := hC r Ω x
  haveI := hfin
  have h := (fib_bijOn hpb (𝟙 (gp Ω))).image_eq
  rw [Category.id_comp] at h
  rw [← h]
  exact (fib_spec_finite Ω B).image _
