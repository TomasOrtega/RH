import Mathlib
open scoped Topology

namespace GlobalTheory

/- English proof (translation)
Simplify using `only [Matrix.det_apply']`. Apply `DifferentiableOn.fun_sum` to reduce the goal to its premises. Introduce `σ _`. Apply `DifferentiableOn.mul (differentiableOn_const _)` to reduce the goal to its premises. Establish `key : ∀ t : Finset (Fin g), DifferentiableOn ℂ (fun y => ∏ i ∈ t, A y (σ i) i) U`.

Introduce `t`. Use `Finset.induction_on t ?_ ?_` and prove the remaining obligations. Simplify using `using (differentiableOn_const (1 : ℂ) : DifferentiableOn ℂ (fun _ : X => (1 : ℂ)) U)`. Introduce `a t ha ih`. Simplify using `only [Finset.prod_insert ha]`.

Conclude with `(h _ _).mul ih`. Conclude with `key _`.
-/
theorem differentiableOn_det_of_entries_frameCoord {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    {g : ℕ} {U : Set X} (A : X → Matrix (Fin g) (Fin g) ℂ)
    (h : ∀ a b, DifferentiableOn ℂ (fun s => A s a b) U) :
    DifferentiableOn ℂ (fun s => (A s).det) U := by
  simp only [Matrix.det_apply']
  apply DifferentiableOn.fun_sum
  intro σ _
  apply DifferentiableOn.mul (differentiableOn_const _)
  have key : ∀ t : Finset (Fin g), DifferentiableOn ℂ (fun y => ∏ i ∈ t, A y (σ i) i) U := by
    intro t
    refine Finset.induction_on t ?_ ?_
    · simpa using (differentiableOn_const (1 : ℂ) : DifferentiableOn ℂ (fun _ : X => (1 : ℂ)) U)
    · intro a t ha ih
      simp only [Finset.prod_insert ha]
      exact (h _ _).mul ih
  exact key _

/- English proof (translation)
Introduce `n g U E F hE hF hdet`. Set `Emat : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ` to `fun s => Matrix.of fun k i => E s i k`. Set `Fmat : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ` to `fun s => Matrix.of fun k j => F s j k`. Use `⟨fun s i j => ((Emat s)⁻¹ * Fmat s) i j, ?_, ?_⟩` and prove the remaining obligations. Establish `hEe : ∀ i k, DifferentiableOn ℂ (fun s => E s i k) U` using `fun i k => differentiableOn_pi.1 (differentiableOn_pi.1 hE i) k`.

Establish `hFe : ∀ i k, DifferentiableOn ℂ (fun s => F s i k) U` using `fun i k => differentiableOn_pi.1 (differentiableOn_pi.1 hF i) k`. Establish `hdetD : DifferentiableOn ℂ (fun s => (Emat s).det) U` using `differentiableOn_det_of_entries_frameCoord Emat (fun a b => by simpa [Emat] using hEe b a)`. Establish `hadj : ∀ a b, DifferentiableOn ℂ (fun s => (Emat s).adjugate a b) U`. Introduce `a b`. Simplify using `only [Matrix.adjugate_apply]`.

Apply `differentiableOn_det_of_entries_frameCoord` to reduce the goal to its premises. Introduce `r c`. Distinguish the cases in `hr : r = b`. Substitute `hr` using the available equality. Simplify using `only [Matrix.updateRow_self]`.

Conclude with `differentiableOn_const _`. Simplify using `only [Matrix.updateRow_ne hr]`. Simplify `hEe c r` using `[Emat]`. Establish `hinv : ∀ a b, DifferentiableOn ℂ (fun s => (Emat s)⁻¹ a b) U`. Introduce `a b`.

Establish `hc : ∀ s ∈ U, ((Emat s).det)⁻¹ * (Emat s).adjugate a b = (Emat s)⁻¹ a b`. Introduce `s _`. Rewrite using `[Matrix.inv_def, Ring.inverse_eq_inv']`. Simplify using `[Matrix.smul_apply]`. Conclude with `((hdetD.inv (fun s hs => hdet s hs)).mul (hadj a b)).congr (fun s hs => (hc s hs).symm)`.

Rewrite using `[differentiableOn_pi]`. Introduce `i`. Rewrite using `[differentiableOn_pi]`. Introduce `j`. Simplify using `only [Matrix.mul_apply]`.

Apply `DifferentiableOn.fun_sum` to reduce the goal to its premises. Introduce `k _`. Conclude with `(hinv i k).mul (by simpa [Fmat] using hFe j k)`. Introduce `s hs j`. Establish `h1 : Emat s * ((Emat s)⁻¹ * Fmat s) = Fmat s` using `Matrix.mul_nonsing_inv_cancel_left _ _ (isUnit_iff_ne_zero.mpr (hdet s hs))`.

Use function extensionality and compare the values at `k`. Establish `h2` using `congrFun (congrFun h1 k) j`. Simplify using `only [Matrix.mul_apply, Matrix.of_apply, Emat, Fmat] at h2`. Rewrite using `[Finset.sum_apply]`. Simplify using `only [Pi.smul_apply, smul_eq_mul]`.

Rewrite using `[← h2]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `i _`. Simplify using `only [Matrix.mul_apply, Emat, Fmat, Matrix.of_apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem holomorphic_coordinates_in_holomorphic_frame : ∀ (n g : ℕ) (U : Set (Fin n → ℂ))
    (E F : (Fin n → ℂ) → Fin g → Fin g → ℂ), DifferentiableOn ℂ E U → DifferentiableOn ℂ F U →
    (∀ s ∈ U, (Matrix.of fun k i => E s i k).det ≠ 0) →
    ∃ τ : (Fin n → ℂ) → Fin g → Fin g → ℂ, DifferentiableOn ℂ τ U ∧
      ∀ s ∈ U, ∀ j, F s j = ∑ i, τ s i j • E s i := by
  intro n g U E F hE hF hdet
  let Emat : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ := fun s => Matrix.of fun k i => E s i k
  let Fmat : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ := fun s => Matrix.of fun k j => F s j k
  refine ⟨fun s i j => ((Emat s)⁻¹ * Fmat s) i j, ?_, ?_⟩
  · have hEe : ∀ i k, DifferentiableOn ℂ (fun s => E s i k) U :=
      fun i k => differentiableOn_pi.1 (differentiableOn_pi.1 hE i) k
    have hFe : ∀ i k, DifferentiableOn ℂ (fun s => F s i k) U :=
      fun i k => differentiableOn_pi.1 (differentiableOn_pi.1 hF i) k
    have hdetD : DifferentiableOn ℂ (fun s => (Emat s).det) U :=
      differentiableOn_det_of_entries_frameCoord Emat (fun a b => by simpa [Emat] using hEe b a)
    have hadj : ∀ a b, DifferentiableOn ℂ (fun s => (Emat s).adjugate a b) U := by
      intro a b
      simp only [Matrix.adjugate_apply]
      apply differentiableOn_det_of_entries_frameCoord
      intro r c
      by_cases hr : r = b
      · subst hr
        simp only [Matrix.updateRow_self]
        exact differentiableOn_const _
      · simp only [Matrix.updateRow_ne hr]
        simpa [Emat] using hEe c r
    have hinv : ∀ a b, DifferentiableOn ℂ (fun s => (Emat s)⁻¹ a b) U := by
      intro a b
      have hc : ∀ s ∈ U, ((Emat s).det)⁻¹ * (Emat s).adjugate a b = (Emat s)⁻¹ a b := by
        intro s _
        rw [Matrix.inv_def, Ring.inverse_eq_inv']
        simp [Matrix.smul_apply]
      exact ((hdetD.inv (fun s hs => hdet s hs)).mul (hadj a b)).congr (fun s hs => (hc s hs).symm)
    rw [differentiableOn_pi]; intro i
    rw [differentiableOn_pi]; intro j
    simp only [Matrix.mul_apply]
    apply DifferentiableOn.fun_sum
    intro k _
    exact (hinv i k).mul (by simpa [Fmat] using hFe j k)
  · intro s hs j
    have h1 : Emat s * ((Emat s)⁻¹ * Fmat s) = Fmat s :=
      Matrix.mul_nonsing_inv_cancel_left _ _ (isUnit_iff_ne_zero.mpr (hdet s hs))
    funext k
    have h2 := congrFun (congrFun h1 k) j
    simp only [Matrix.mul_apply, Matrix.of_apply, Emat, Fmat] at h2
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [← h2]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Matrix.mul_apply, Emat, Fmat, Matrix.of_apply]
    ring

end GlobalTheory
