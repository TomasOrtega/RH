import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIndexOfGammaLe
open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology

noncomputable section

namespace GlobalTheory.OddFrame

/- English proof (translation)
Assume the negation of the conclusion as `hneg`. Use `push_neg at hneg`. Establish `h0 : F j = 0` using `(hF j).eq_zero_of_neg hneg`. Take `⟨τ, hτ⟩` from `hdet`. Apply `hτ` to reduce the goal to its premises.

Apply `Matrix.det_eq_zero_of_column_eq_zero j` to reduce the goal to its premises. Introduce `i`. Simplify using `[evM, h0, SlashAction.zero_slash]`.
-/
theorem weights_nonneg_of_det {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex] {r : ℕ} {s : Fin r → SL(2, ℤ)}
    {w : Fin r → ℤ} {F : Fin r → ℍ → ℂ} (hF : ∀ j, IsMF Γ (w j) (F j))
    (hdet : ∃ τ, (evM s w F τ).det ≠ 0) (j : Fin r) : 0 ≤ w j := by
  by_contra hneg
  push_neg at hneg
  have h0 : F j = 0 := (hF j).eq_zero_of_neg hneg
  obtain ⟨τ, hτ⟩ := hdet
  apply hτ
  apply Matrix.det_eq_zero_of_column_eq_zero j
  intro i
  simp [evM, h0, SlashAction.zero_slash]

/- English proof (translation)
Establish `hM : evM s (Function.update w j₀ w') (Function.update F j₀ G) τ = (evM s w F τ).updateCol j₀ (fun i => (G ∣[w'] s i) τ)`. Use extensionality with `i j`. Distinguish the cases in `hj : j = j₀`. Substitute `hj` using the available equality. Simplify using `[evM, Matrix.updateCol_apply]`.

Simplify using `[evM, Matrix.updateCol_apply, hj, Function.update_of_ne hj]`. Rewrite using `[hM, ← Matrix.det_updateCol_smul]`. Establish `hc : (E τ • fun i => (G ∣[w'] s i) τ) = fun i => ∑ j, (fun j => e j τ) j • (evM s w F τ) i j`. Use extensionality with `i`. Simplify using `[evM, hrel]`.

Rewrite using `[hc, Matrix.det_updateCol_sum, smul_eq_mul]`.
-/
theorem mul_det_evM_update {r : ℕ} (s : Fin r → SL(2, ℤ)) (w : Fin r → ℤ) (F : Fin r → ℍ → ℂ)
    (j₀ : Fin r) (w' : ℤ) (G E : ℍ → ℂ) (e : Fin r → ℍ → ℂ)
    (hrel : ∀ (x : SL(2, ℤ)) (τ : ℍ), E τ * (G ∣[w'] x) τ = ∑ j, e j τ * (F j ∣[w j] x) τ) (τ : ℍ) :
    E τ * (evM s (Function.update w j₀ w') (Function.update F j₀ G) τ).det =
      e j₀ τ * (evM s w F τ).det := by
  have hM : evM s (Function.update w j₀ w') (Function.update F j₀ G) τ =
      (evM s w F τ).updateCol j₀ (fun i => (G ∣[w'] s i) τ) := by
    ext i j
    by_cases hj : j = j₀
    · subst hj; simp [evM, Matrix.updateCol_apply]
    · simp [evM, Matrix.updateCol_apply, hj, Function.update_of_ne hj]
  rw [hM, ← Matrix.det_updateCol_smul]
  have hc : (E τ • fun i => (G ∣[w'] s i) τ) =
      fun i => ∑ j, (fun j => e j τ) j • (evM s w F τ) i j := by
    ext i
    simp [evM, hrel]
  rw [hc, Matrix.det_updateCol_sum, smul_eq_mul]

/- English proof (translation)
Introduce `n`. Proceed by induction on `n using Nat.strong_induction_on with`. Consider the case `_ n ih`. Introduce `w F hn hF hdet`. Distinguish the cases in `hR : Reduces Γ w F`.

Use `swap`. Conclude with `⟨w, F, hF, hdet, hR⟩`. Take `⟨j₀, w₀, G, E, e, hlt, hodd, hG, he, hne, hrel⟩` from `hR`. Use `set w₁ := Function.update w j₀ w₀ with hw₁`. Use `set F₁ := Function.update F j₀ G with hF₁`.

Establish `hF' : ∀ j, Odd (w₁ j) ∧ IsMF Γ (w₁ j) (F₁ j)`. Introduce `j`. Distinguish the cases in `hj : j = j₀`. Substitute `hj` using the available equality. Simplify using `[w₁, F₁, hodd, hG]`.

Simplify using `only [w₁, F₁, Function.update_of_ne hj]`. Conclude with `hF j`. Establish `hdet' : ∃ τ, (evM s w₁ F₁ τ).det ≠ 0`. Establish `hd0 : (fun τ => (evM s w F τ).det) ≠ 0`. Take `⟨τ, hτ⟩` from `hdet`.

Introduce `h`. Conclude with `hτ (congrFun h τ)`. Establish `hmd : MDiff (fun τ => (evM s w F τ).det)` using `mdiff_det_evM s w (fun j => (hF j).2.2.1)`. Establish `hprod : e j₀ * (fun τ => (evM s w F τ).det) ≠ 0`. Rewrite using `[Ne, UpperHalfPlane.mul_eq_zero_iff (he j₀) hmd]`.

Use `push_neg`. Conclude with `⟨hne, hd0⟩`. Choose the witnesses or unpack the hypotheses as in `⟨τ, hτ⟩ : ∃ τ, e j₀ τ * (evM s w F τ).det ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`.

Conclude with `hprod (funext fun τ => by simpa using h τ)`. Use `⟨τ, fun h0 => hτ ?_⟩` and prove the remaining obligations. Rewrite using `[← mul_det_evM_update s w F j₀ w₀ G E e hrel τ]`. Rewrite `h0` using `[show w₁ = Function.update w j₀ w₀ from rfl, show F₁ = Function.update F j₀ G from rfl]`. Rewrite using `[h0, mul_zero]`.

Establish `hnn` using `weights_nonneg_of_det (fun j => (hF j).2) hdet`. Establish `hnn'` using `weights_nonneg_of_det (fun j => (hF' j).2) hdet'`. Establish `hlt' : ∑ j, (w₁ j).toNat < n`. Rewrite using `[← hn]`. Apply `Finset.sum_lt_sum` to reduce the goal to its premises.

Introduce `j _`. Distinguish the cases in `hj : j = j₀`. Substitute `hj` using the available equality. Simplify using `only [w₁, Function.update_self]`. Use linear arithmetic over natural numbers and integers.

Simplify using `only [w₁, Function.update_of_ne hj]`. Conclude with `le_rfl`. Use `⟨j₀, Finset.mem_univ _, ?_⟩` and prove the remaining obligations. Use `hnn' j₀` as an intermediate fact. Simplify using `only [w₁, Function.update_self] at this ⊢`.

Use `hnn j₀` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Conclude with `ih _ hlt' w₁ F₁ rfl hF' hdet'`.
-/
theorem oddFrame_descent_of_weight_sum (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (r : ℕ) (s : Fin r → SL(2, ℤ)) :
    ∀ (n : ℕ) (w : Fin r → ℤ) (F : Fin r → ℍ → ℂ), ∑ j, (w j).toNat = n →
      (∀ j, Odd (w j) ∧ IsMF Γ (w j) (F j)) → (∃ τ, (evM s w F τ).det ≠ 0) →
      ∃ (w' : Fin r → ℤ) (F' : Fin r → ℍ → ℂ), (∀ j, Odd (w' j) ∧ IsMF Γ (w' j) (F' j)) ∧
        (∃ τ, (evM s w' F' τ).det ≠ 0) ∧ ¬ Reduces Γ w' F' := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro w F hn hF hdet
  by_cases hR : Reduces Γ w F
  swap
  · exact ⟨w, F, hF, hdet, hR⟩
  obtain ⟨j₀, w₀, G, E, e, hlt, hodd, hG, he, hne, hrel⟩ := hR
  set w₁ := Function.update w j₀ w₀ with hw₁
  set F₁ := Function.update F j₀ G with hF₁
  have hF' : ∀ j, Odd (w₁ j) ∧ IsMF Γ (w₁ j) (F₁ j) := by
    intro j
    by_cases hj : j = j₀
    · subst hj; simp [w₁, F₁, hodd, hG]
    · simp only [w₁, F₁, Function.update_of_ne hj]; exact hF j
  have hdet' : ∃ τ, (evM s w₁ F₁ τ).det ≠ 0 := by
    have hd0 : (fun τ => (evM s w F τ).det) ≠ 0 := by
      obtain ⟨τ, hτ⟩ := hdet
      intro h; exact hτ (congrFun h τ)
    have hmd : MDiff (fun τ => (evM s w F τ).det) := mdiff_det_evM s w (fun j => (hF j).2.2.1)
    have hprod : e j₀ * (fun τ => (evM s w F τ).det) ≠ 0 := by
      rw [Ne, UpperHalfPlane.mul_eq_zero_iff (he j₀) hmd]
      push_neg; exact ⟨hne, hd0⟩
    obtain ⟨τ, hτ⟩ : ∃ τ, e j₀ τ * (evM s w F τ).det ≠ 0 := by
      by_contra h
      push_neg at h
      exact hprod (funext fun τ => by simpa using h τ)
    refine ⟨τ, fun h0 => hτ ?_⟩
    rw [← mul_det_evM_update s w F j₀ w₀ G E e hrel τ]
    rw [show w₁ = Function.update w j₀ w₀ from rfl, show F₁ = Function.update F j₀ G from rfl] at h0
    rw [h0, mul_zero]
  have hnn := weights_nonneg_of_det (fun j => (hF j).2) hdet
  have hnn' := weights_nonneg_of_det (fun j => (hF' j).2) hdet'
  have hlt' : ∑ j, (w₁ j).toNat < n := by
    rw [← hn]
    apply Finset.sum_lt_sum
    · intro j _
      by_cases hj : j = j₀
      · subst hj; simp only [w₁, Function.update_self]; omega
      · simp only [w₁, Function.update_of_ne hj]; exact le_rfl
    · refine ⟨j₀, Finset.mem_univ _, ?_⟩
      have := hnn' j₀
      simp only [w₁, Function.update_self] at this ⊢
      have := hnn j₀
      omega
  exact ih _ hlt' w₁ F₁ rfl hF' hdet'

/- English proof (translation)
Introduce `Γ r s w F hΓ hF hdet`. Conclude with `oddFrame_descent_of_weight_sum Γ r s _ w F rfl hF hdet`.
-/
theorem descent : ∀ (Γ : Subgroup SL(2, ℤ)) (r : ℕ) (s : Fin r → SL(2, ℤ)) (w : Fin r → ℤ) (F : Fin r → ℍ → ℂ),
    Γ.FiniteIndex → (∀ j, Odd (w j) ∧ IsMF Γ (w j) (F j)) → (∃ τ, (evM s w F τ).det ≠ 0) →
    ∃ (w' : Fin r → ℤ) (F' : Fin r → ℍ → ℂ), (∀ j, Odd (w' j) ∧ IsMF Γ (w' j) (F' j)) ∧
      (∃ τ, (evM s w' F' τ).det ≠ 0) ∧ ¬ Reduces Γ w' F' := by
  intro Γ r s w F hΓ hF hdet
  exact oddFrame_descent_of_weight_sum Γ r s _ w F rfl hF hdet

end GlobalTheory.OddFrame
