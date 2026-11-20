import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceReducedAway
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceReducedAwayZariski
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Matrix

noncomputable section

/- English proof (translation)
Take `⟨y₀, hy₀⟩` from `hne`. Take `⟨u, hu, hsub⟩` from `isOpen_pi_iff'.mp hS y₀ hy₀`. Assume the negation of the conclusion as `h`. Use `push Not at h`. Apply `hF` to reduce the goal to its premises.

Establish `hinf : ∀ i, (u i).Infinite` using `fun i => infinite_of_mem_nhds (y₀ i) ((hu i).1.mem_nhds (hu i).2)`. Use `(funext_set_iff (p := F) (q := 0) u hinf).mpr fun y hy => ?_` and prove the remaining obligations. Rewrite using `[map_zero]`. Conclude with `h y (hsub hy)`.
-/
theorem exists_eval_ne_zero_of_isOpen_pi {σ : Type*} [Finite σ] {F : MvPolynomial σ ℂ} (hF : F ≠ 0)
    {S : Set (σ → ℂ)} (hS : IsOpen S) (hne : S.Nonempty) : ∃ y ∈ S, eval y F ≠ 0 := by
  obtain ⟨y₀, hy₀⟩ := hne
  obtain ⟨u, hu, hsub⟩ := isOpen_pi_iff'.mp hS y₀ hy₀
  by_contra h
  push Not at h
  apply hF
  have hinf : ∀ i, (u i).Infinite := fun i =>
    infinite_of_mem_nhds (y₀ i) ((hu i).1.mem_nhds (hu i).2)
  refine (funext_set_iff (p := F) (q := 0) u hinf).mpr fun y hy => ?_
  rw [map_zero]
  exact h y (hsub hy)

/- English proof (translation)
Introduce `n d J q hJ`. Take `⟨F, hF, hgood⟩` from `hZ n d J q hJ`. Set `e : Matrix (Fin d) (Fin n) ℂ → (Fin d × Fin n → ℂ)` to `fun L ij => L ij.1 ij.2`. Set `φ : (Fin d × Fin n → ℂ) → Matrix (Fin d) (Fin n) ℂ` to `fun y => Matrix.of fun i j => y (i, j)`. Establish `he : Continuous e` using `continuous_pi fun ij => continuous_id.matrix_elem ij.1 ij.2`.

Establish `hφ : Continuous φ` using `continuous_pi fun i => continuous_pi fun j => continuous_apply (i, j)`. Use `⟨{L | eval (e L) F ≠ 0}, ?_, ?_, fun L hL => hgood L hL⟩` and prove the remaining obligations. Conclude with `isOpen_ne_fun ((MvPolynomial.continuous_eval F).comp he) continuous_const`. Rewrite using `[dense_iff_inter_open]`. Introduce and unpack `U hU ⟨L₀, hL₀⟩`.

Take `⟨y, hyU, hyF⟩` from `exists_eval_ne_zero_of_isOpen_pi hF (hU.preimage hφ) ⟨e L₀, hL₀⟩`. Conclude with `⟨φ y, hyU, hyF⟩`.
-/
theorem SliceReducedAway.proof (hZ : SliceReducedAwayZariski.Statement) :
    SliceReducedAway.Statement := by
  intro n d J q hJ
  obtain ⟨F, hF, hgood⟩ := hZ n d J q hJ
  let e : Matrix (Fin d) (Fin n) ℂ → (Fin d × Fin n → ℂ) := fun L ij => L ij.1 ij.2
  let φ : (Fin d × Fin n → ℂ) → Matrix (Fin d) (Fin n) ℂ := fun y => Matrix.of fun i j => y (i, j)
  have he : Continuous e := continuous_pi fun ij => continuous_id.matrix_elem ij.1 ij.2
  have hφ : Continuous φ :=
    continuous_pi fun i => continuous_pi fun j => continuous_apply (i, j)
  refine ⟨{L | eval (e L) F ≠ 0}, ?_, ?_, fun L hL => hgood L hL⟩
  · exact isOpen_ne_fun ((MvPolynomial.continuous_eval F).comp he) continuous_const
  · rw [dense_iff_inter_open]
    rintro U hU ⟨L₀, hL₀⟩
    obtain ⟨y, hyU, hyF⟩ :=
      exists_eval_ne_zero_of_isOpen_pi hF (hU.preimage hφ) ⟨e L₀, hL₀⟩
    exact ⟨φ y, hyU, hyF⟩

end

end GroundTheory.Heights₂.Heights
