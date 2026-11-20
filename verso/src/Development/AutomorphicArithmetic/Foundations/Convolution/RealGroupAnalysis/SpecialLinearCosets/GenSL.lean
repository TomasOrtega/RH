import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.GoodU

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H UpperTheory.ConvolutionTheory.R2.I
open scoped Classical

/- English proof (translation)
Introduce `K _ H hu hl`. Establish `hdet : ∀ g : Matrix.SpecialLinearGroup (Fin 2) K, g.1 0 0 * g.1 1 1 - g.1 0 1 * g.1 1 0 = 1` using `fun g => by`. Establish `h` using `g.2`. Rewrite `h` using `[Matrix.det_fin_two]`. Then use the resulting hypothesis. Establish `nU : ∀ b : K, ∃ g ∈ H, g.1 = !![1, b; 0, 1]` using `fun b => ⟨⟨!![1, b; 0, 1], by simp [Matrix.det_fin_two]⟩, hu _ b rfl, rfl⟩`.

Establish `nL : ∀ c : K, ∃ g ∈ H, g.1 = !![1, 0; c, 1]` using `fun c => ⟨⟨!![1, 0; c, 1], by simp [Matrix.det_fin_two]⟩, hl _ c rfl, rfl⟩`. Establish `key : ∀ g : Matrix.SpecialLinearGroup (Fin 2) K, g.1 1 0 ≠ 0 → g ∈ H`. Introduce `g hc`. Take `⟨x, hx, hx'⟩` from `nU ((g.1 0 0 - 1) / g.1 1 0)`. Take `⟨l, hl1, hl'⟩` from `nL (g.1 1 0)`.

Take `⟨y, hy, hy'⟩` from `nU ((g.1 1 1 - 1) / g.1 1 0)`. Establish `hd` using `hdet g`. Establish `e : g = x * l * y`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hx', hl', hy']`.

Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;>`. Apply the tactic sequence `simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> first | ring1 | linear_combination (-1 : K) * hd`. Rewrite using `[e]`. Conclude with `H.mul_mem (H.mul_mem hx hl1) hy`.

Use `eq_top_iff.2 fun g _ => ?_` and prove the remaining obligations. Distinguish the cases in `hc : g.1 1 0 = 0`. Take `⟨l, hl1, hl'⟩` from `nL 1`. Establish `hd` using `hdet g`. Establish `ha : g.1 0 0 ≠ 0`.

Introduce `h0`. Rewrite `hd` using `[h0, hc]`. Simplify using `at hd`. Establish `h2 : l * g ∈ H`. Apply `key` to reduce the goal to its premises.

Rewrite using `[Matrix.SpecialLinearGroup.coe_mul, hl']`. Simplify `ha` using `[Matrix.mul_apply, Fin.sum_univ_two, hc]`. Establish `e : g = l⁻¹ * (l * g)` using `by group`. Rewrite using `[e]`. Conclude with `H.mul_mem (H.inv_mem hl1) h2`.

Conclude with `key g hc`.
-/
theorem UpperTheory.ConvolutionTheory.R2.I.genSL :
    ∀ (K : Type) [Field K] (H : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K)),
      (∀ (g : Matrix.SpecialLinearGroup (Fin 2) K) (b : K), g.1 = !![1, b; 0, 1] → g ∈ H) →
      (∀ (g : Matrix.SpecialLinearGroup (Fin 2) K) (c : K), g.1 = !![1, 0; c, 1] → g ∈ H) → H = ⊤ := by
  intro K _ H hu hl
  have hdet : ∀ g : Matrix.SpecialLinearGroup (Fin 2) K,
      g.1 0 0 * g.1 1 1 - g.1 0 1 * g.1 1 0 = 1 := fun g => by
    have h := g.2
    rwa [Matrix.det_fin_two] at h
  have nU : ∀ b : K, ∃ g ∈ H, g.1 = !![1, b; 0, 1] := fun b =>
    ⟨⟨!![1, b; 0, 1], by simp [Matrix.det_fin_two]⟩, hu _ b rfl, rfl⟩
  have nL : ∀ c : K, ∃ g ∈ H, g.1 = !![1, 0; c, 1] := fun c =>
    ⟨⟨!![1, 0; c, 1], by simp [Matrix.det_fin_two]⟩, hl _ c rfl, rfl⟩
  have key : ∀ g : Matrix.SpecialLinearGroup (Fin 2) K, g.1 1 0 ≠ 0 → g ∈ H := by
    intro g hc
    obtain ⟨x, hx, hx'⟩ := nU ((g.1 0 0 - 1) / g.1 1 0)
    obtain ⟨l, hl1, hl'⟩ := nL (g.1 1 0)
    obtain ⟨y, hy, hy'⟩ := nU ((g.1 1 1 - 1) / g.1 1 0)
    have hd := hdet g
    have e : g = x * l * y := by
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hx', hl', hy']
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;>
          first | ring1 | linear_combination (-1 : K) * hd
    rw [e]
    exact H.mul_mem (H.mul_mem hx hl1) hy
  refine eq_top_iff.2 fun g _ => ?_
  by_cases hc : g.1 1 0 = 0
  · obtain ⟨l, hl1, hl'⟩ := nL 1
    have hd := hdet g
    have ha : g.1 0 0 ≠ 0 := by
      intro h0
      rw [h0, hc] at hd
      simp at hd
    have h2 : l * g ∈ H := by
      apply key
      rw [Matrix.SpecialLinearGroup.coe_mul, hl']
      simpa [Matrix.mul_apply, Fin.sum_univ_two, hc] using ha
    have e : g = l⁻¹ * (l * g) := by group
    rw [e]
    exact H.mul_mem (H.inv_mem hl1) h2
  · exact key g hc
