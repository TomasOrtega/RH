import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import GroundTheory.AutomorphicForms.MultiplicityOne.Injective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WhitMulLocGLDiagPowOfFixed
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFixedOfMemISup
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Spherical
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix

namespace GlobalTheory.GLFinPlaces

/- English proof (translation)
Establish `hent : ∀ M : Matrix (Fin a) (Fin a) (Af E), ∀ᶠ w in Filter.cofinite, ∀ i j, (M i j) w ∈ w.adicCompletionIntegers E`. Introduce `M`. Rewrite using `[Filter.eventually_all]`. Introduce `i`. Rewrite using `[Filter.eventually_all]`.

Introduce `j`. Conclude with `(M i j).2`. Establish `h` using `(hent (k : Matrix (Fin a) (Fin a) (Af E))).and (hent ((k⁻¹ : GL (Fin a) (Af E)) : Matrix (Fin a) (Fin a) (Af E)))`. Rewrite `h` using `[Filter.eventually_cofinite]`. Use `h.subset ?_` and prove the remaining obligations.

Introduce `w hw`. Simplify using `only [Set.mem_setOf_eq] at hw ⊢`. Introduce `hg`. Apply `hw` to reduce the goal to its premises. Establish `key : ∀ M : Matrix (Fin a) (Fin a) (Af E), (∀ i j, (M i j) w ∈ w.adicCompletionIntegers E) → M.map (pLoc E w) ∈ (RingHom.mapMatrix (m` using `Fin a) (Ov E w).subtype).range := by`.

Introduce `M hM`. Conclude with `⟨Matrix.of fun i j => (⟨(M i j) w, hM i j⟩ : Ov E w), by ext i j; rfl⟩`. Use `P.glint_mem_range_of_integral _ _ ?_ ?_` and prove the remaining obligations. Conclude with `key _ hg.1`. Rewrite using `[← map_inv]`.

Conclude with `key _ hg.2`.
-/
theorem gl_mem_int_cofinite (E : Type) [Field E] [NumberField E] (a : ℕ) (k : GL (Fin a) (Af E)) :
    {w : HeightOneSpectrum (𝓞 E) | GeneralLinearGroup.map (pLoc E w) k ∉ KGL w a}.Finite := by
  have hent : ∀ M : Matrix (Fin a) (Fin a) (Af E), ∀ᶠ w in Filter.cofinite,
      ∀ i j, (M i j) w ∈ w.adicCompletionIntegers E := by
    intro M
    rw [Filter.eventually_all]; intro i
    rw [Filter.eventually_all]; intro j
    exact (M i j).2
  have h := (hent (k : Matrix (Fin a) (Fin a) (Af E))).and (hent ((k⁻¹ : GL (Fin a) (Af E)) : Matrix (Fin a) (Fin a) (Af E)))
  rw [Filter.eventually_cofinite] at h
  refine h.subset ?_
  intro w hw
  simp only [Set.mem_setOf_eq] at hw ⊢
  intro hg
  apply hw
  have key : ∀ M : Matrix (Fin a) (Fin a) (Af E), (∀ i j, (M i j) w ∈ w.adicCompletionIntegers E) →
      M.map (pLoc E w) ∈ (RingHom.mapMatrix (m := Fin a) (Ov E w).subtype).range := by
    intro M hM
    exact ⟨Matrix.of fun i j => (⟨(M i j) w, hM i j⟩ : Ov E w), by ext i j; rfl⟩
  refine P.glint_mem_range_of_integral _ _ ?_ ?_
  · exact key _ hg.1
  · rw [← map_inv]
    exact key _ hg.2

end GlobalTheory.GLFinPlaces
