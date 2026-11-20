import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import GroundTheory.AutomorphicForms.MultiplicityOne.Injective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WhitMulLocGLDiagPowOfFixed
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFixedOfMemISup
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Spherical
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix

namespace GlobalTheory

/- English proof (translation)
Introduce `E _ _ a S k`. Proceed by induction on `S using Finset.induction_on with`. Consider the case `empty => exact ⟨k, fun w _ => rfl, fun w hw => absurd hw (Finset.notMem_empty w)⟩`. Consider the case `insert w S hwS ih`. Take `⟨k', h1, h2⟩` from `ih`.

Use `⟨k' * (locGL E a w (GeneralLinearGroup.map (pLoc E w) k'))⁻¹, ?_, ?_⟩` and prove the remaining obligations. Introduce `v hv`. Establish `hvw : v ≠ w` using `fun e => hv (e ▸ Finset.mem_insert_self _ _)`. Rewrite using `[map_mul, map_inv, pLoc_locGL_of_ne hvw, inv_one, mul_one]`. Conclude with `h1 v (fun h => hv (Finset.mem_insert_of_mem h))`.

Introduce `v hv`. Rewrite using `[map_mul, map_inv]`. Distinguish the cases in `hvw : v = w`. Substitute `hvw` using the available equality. Rewrite using `[pLoc_locGL, mul_inv_cancel]`.

Rewrite using `[pLoc_locGL_of_ne hvw, inv_one, mul_one]`. Conclude with `h2 v ((Finset.mem_insert.1 hv).resolve_left hvw)`.
-/
theorem outsideS_elt : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (k : GL (Fin a) (Af E)), ∃ k' : GL (Fin a) (Af E), (∀ w ∉ S, GeneralLinearGroup.map (pLoc E w) k' = GeneralLinearGroup.map (pLoc E w) k) ∧ ∀ w ∈ S, GeneralLinearGroup.map (pLoc E w) k' = 1 := by
  intro E _ _ a S k
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨k, fun w _ => rfl, fun w hw => absurd hw (Finset.notMem_empty w)⟩
  | insert w S hwS ih =>
    obtain ⟨k', h1, h2⟩ := ih
    refine ⟨k' * (locGL E a w (GeneralLinearGroup.map (pLoc E w) k'))⁻¹, ?_, ?_⟩
    · intro v hv
      have hvw : v ≠ w := fun e => hv (e ▸ Finset.mem_insert_self _ _)
      rw [map_mul, map_inv, pLoc_locGL_of_ne hvw, inv_one, mul_one]
      exact h1 v (fun h => hv (Finset.mem_insert_of_mem h))
    · intro v hv
      rw [map_mul, map_inv]
      by_cases hvw : v = w
      · subst hvw; rw [pLoc_locGL, mul_inv_cancel]
      · rw [pLoc_locGL_of_ne hvw, inv_one, mul_one]
        exact h2 v ((Finset.mem_insert.1 hv).resolve_left hvw)

end GlobalTheory
