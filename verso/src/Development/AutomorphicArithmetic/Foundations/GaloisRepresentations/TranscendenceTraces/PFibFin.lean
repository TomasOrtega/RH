import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

/- English proof (translation)
Apply `(Set.finite_range (fun g : B →ₐ[Ω] Ω => Spec.map (CommRingCat.ofHom (g : B →+* Ω)))).subset` to reduce the goal to its premises. Introduce `z hz`. Establish `hz' : z ≫ Spec.map (CommRingCat.ofHom (algebraMap Ω B)) = 𝟙 _` using `hz`. Take `⟨φ, rfl⟩ : ∃ φ, Spec.map φ = z` from `⟨Spec.preimage z, Spec.map_preimage z⟩`. Rewrite `hz'` using `[← Spec.map_comp, ← Spec.map_id]`.

Establish `h2` using `Spec.map_injective hz'`. Use `⟨{ φ.hom with commutes' := fun c => ?_ }, ?_⟩` and prove the remaining obligations. Use `congrArg (fun g => g.hom c) h2` as an intermediate fact. Simplify using `using this`. Both sides reduce to the same expression.
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
Introduce `hC`. Unfold `Chart at hC`. Unfold `FibFin`. Introduce `V U r _ Ω _ x`. Take `⟨B, iB, iAB, v, hfin, hpb⟩` from `hC r Ω x`.

Use `haveI := hfin`. Establish `h` using `(fib_bijOn hpb (𝟙 (gp Ω))).image_eq`. Rewrite `h` using `[Category.id_comp]`. Rewrite using `[← h]`. Conclude with `(fib_spec_finite Ω B).image _`.
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
