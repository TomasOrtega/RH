import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.HighestVectorsRegularLine

noncomputable section

open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD

namespace GlobalTheory.CompanionTheory.SignLine

/- English proof (translation)
Introduce `V _ _ S A hA hS h1`. Use `haveI : FiniteDimensional ℂ S := Module.finite_of_finrank_pos (by rw [h1]; exact one_pos)`. Take `⟨v, hv0, hv⟩` from `finrank_eq_one_iff'.mp h1`. Use `set B : S →ₗ[ℂ] S := A.restrict hS with hBdef`. Take `⟨c, hc⟩` from `hv (B v)`.

Establish `hBw : ∀ w : S, B w = c • w`. Introduce `w`. Take `⟨d, rfl⟩` from `hv w`. Rewrite using `[map_smul, ← hc, smul_comm]`. Establish `hcc : c * c = 1`.

Establish `h2 : B (B v) = v`. Apply `Subtype.ext` to reduce the goal to its premises. Use `show A (A (v : V)) = v`. Use `congrArg (fun f : V →ₗ[ℂ] V => f v) hA` as an intermediate fact. Simplify using `using this`.

Rewrite `h2` using `[hBw (B v), hBw v, smul_smul]`. Establish `h3 : (c * c - 1) • v = 0` using `by rw [sub_smul, h2, one_smul, sub_self]`. Break down `smul_eq_zero.mp h3 with h | h` into its components or cases. Conclude with `sub_eq_zero.mp h`. Conclude with `absurd h hv0`.

Use `⟨c, mul_self_eq_one_iff.mp hcc, ?_⟩` and prove the remaining obligations. Establish `hB : B = c • LinearMap.id` using `LinearMap.ext fun w => by rw [hBw]; rfl`. Rewrite using `[trOn, dif_pos hS]`. Express the relevant statement in the definitionally equal form `LinearMap.trace ℂ S B = c`. Rewrite using `[hB, map_smul, LinearMap.trace_id]`.

Simplify using `[h1]`.
-/
theorem signOne : PositivityTheory.RgBcC.RealD.SignOne := by
  intro V _ _ S A hA hS h1
  haveI : FiniteDimensional ℂ S := Module.finite_of_finrank_pos (by rw [h1]; exact one_pos)
  obtain ⟨v, hv0, hv⟩ := finrank_eq_one_iff'.mp h1
  set B : S →ₗ[ℂ] S := A.restrict hS with hBdef
  obtain ⟨c, hc⟩ := hv (B v)
  have hBw : ∀ w : S, B w = c • w := by
    intro w
    obtain ⟨d, rfl⟩ := hv w
    rw [map_smul, ← hc, smul_comm]
  have hcc : c * c = 1 := by
    have h2 : B (B v) = v := by
      apply Subtype.ext
      show A (A (v : V)) = v
      have := congrArg (fun f : V →ₗ[ℂ] V => f v) hA
      simpa using this
    rw [hBw (B v), hBw v, smul_smul] at h2
    have h3 : (c * c - 1) • v = 0 := by rw [sub_smul, h2, one_smul, sub_self]
    rcases smul_eq_zero.mp h3 with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hv0
  refine ⟨c, mul_self_eq_one_iff.mp hcc, ?_⟩
  have hB : B = c • LinearMap.id := LinearMap.ext fun w => by rw [hBw]; rfl
  rw [trOn, dif_pos hS]
  change LinearMap.trace ℂ S B = c
  rw [hB, map_smul, LinearMap.trace_id]
  simp [h1]

end GlobalTheory.CompanionTheory.SignLine
