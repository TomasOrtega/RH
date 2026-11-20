import Formalism.GradedWeylDivisibility.StatementA

namespace Formalism.GradedWeylDivisibility

open MvPolynomial

def idPoint (R : Type*) [CommRing R] (r n : ℕ) : Fin r × Fin n → R :=
  fun v => if v.1.val = v.2.val then 1 else 0

/- English proof (translation)
Unfold `lpMinor`. Rewrite using `[RingHom.map_det]`. Use `Matrix.det_one (R := R) (n := Fin s)` and compare the differences between its conclusion and the goal. Use extensionality with `p q`. Simplify using `[RingHom.mapMatrix_apply, idPoint, Matrix.one_apply]`.

Conclude with `if_congr Fin.val_inj rfl rfl`.
-/
theorem eval_idPoint_lpMinor (R : Type*) [CommRing R] {r n : ℕ} (s : ℕ) (hr : s ≤ r)
    (hn : s ≤ n) : eval (idPoint R r n) (lpMinor R s hr hn) = 1 := by
  unfold lpMinor
  rw [RingHom.map_det]
  convert Matrix.det_one (R := R) (n := Fin s)
  ext p q
  simp [RingHom.mapMatrix_apply, idPoint, Matrix.one_apply]
  exact if_congr Fin.val_inj rfl rfl

/- English proof (translation)
Establish `h1 : (∑ q : Fin s, (Pi.single (Fin.castLE hr (σ q)) 1 : Fin r → ℕ)) = ∑ q : Fin s, (Pi.single (Fin.castLE hr q) 1 : Fin r → ℕ)` using `Equiv.sum_comp σ (fun q => (Pi.single (Fin.castLE hr q) 1 : Fin r → ℕ))`. Rewrite using `[h1]`. Use function extensionality and compare the values at `a`. Rewrite using `[Finset.sum_apply]`. Simplify using `only [Pi.single_apply]`.

Use `split_ifs with h`. Rewrite using `[Finset.sum_eq_single ⟨a.val, h⟩]`. Conclude with `if_pos (Fin.ext rfl)`. Introduce `b _ hb`. Rewrite using `[if_neg]`.

Introduce `hab`. Substitute `hab` using the available equality. Conclude with `hb (Fin.ext rfl)`. Introduce `hn`. Conclude with `absurd (Finset.mem_univ _) hn`.

Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `b _`. Rewrite using `[if_neg]`. Introduce `hab`. Substitute `hab` using the available equality.

Conclude with `h b.isLt`.
-/
theorem hwrow_sum_single_castLE {r s : ℕ} (hr : s ≤ r) (σ : Equiv.Perm (Fin s)) :
    (∑ q : Fin s, (Pi.single (Fin.castLE hr (σ q)) 1 : Fin r → ℕ)) =
      fun a => if a.val < s then 1 else 0 := by
  have h1 : (∑ q : Fin s, (Pi.single (Fin.castLE hr (σ q)) 1 : Fin r → ℕ)) =
      ∑ q : Fin s, (Pi.single (Fin.castLE hr q) 1 : Fin r → ℕ) :=
    Equiv.sum_comp σ (fun q => (Pi.single (Fin.castLE hr q) 1 : Fin r → ℕ))
  rw [h1]
  funext a
  rw [Finset.sum_apply]
  simp only [Pi.single_apply]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨a.val, h⟩]
    · exact if_pos (Fin.ext rfl)
    · intro b _ hb
      rw [if_neg]
      intro hab
      subst hab
      exact hb (Fin.ext rfl)
    · intro hn
      exact absurd (Finset.mem_univ _) hn
  · apply Finset.sum_eq_zero
    intro b _
    rw [if_neg]
    intro hab
    subst hab
    exact h b.isLt

/- English proof (translation)
Unfold `lpMinor`. Rewrite using `[Matrix.det_apply]`. Apply `IsWeightedHomogeneous.sum` to reduce the goal to its premises. Introduce `σ _`. Establish `hk : IsWeightedHomogeneous (rowW r n) (∏ i, (Matrix.of fun p q : Fin s => (X (Fin.castLE hr p, Fin.castLE hn q) : MvPolynomial (Fin r × Fin n) R)) (σ i) i) (fun a : Fin r => if a.val < s then 1 else 0)`.

Rewrite using `[← hwrow_sum_single_castLE hr σ]`. Apply `IsWeightedHomogeneous.prod` to reduce the goal to its premises. Introduce `i _`. Simplify using `only [Matrix.of_apply]`. Conclude with `isWeightedHomogeneous_X R (rowW r n) _`.

Rewrite `hk`, the goal using `[← mem_weightedHomogeneousSubmodule]`. Rewrite using `[Units.smul_def]`. Conclude with `zsmul_mem hk _`.
-/
theorem lpMinor_rowHom (R : Type*) [CommRing R] {r n : ℕ} (s : ℕ) (hr : s ≤ r) (hn : s ≤ n) :
    IsWeightedHomogeneous (rowW r n) (lpMinor R s hr hn)
      (fun a => if a.val < s then 1 else 0) := by
  unfold lpMinor
  rw [Matrix.det_apply]
  apply IsWeightedHomogeneous.sum
  intro σ _
  have hk : IsWeightedHomogeneous (rowW r n)
      (∏ i, (Matrix.of fun p q : Fin s =>
        (X (Fin.castLE hr p, Fin.castLE hn q) : MvPolynomial (Fin r × Fin n) R)) (σ i) i)
      (fun a : Fin r => if a.val < s then 1 else 0) := by
    rw [← hwrow_sum_single_castLE hr σ]
    apply IsWeightedHomogeneous.prod
    intro i _
    simp only [Matrix.of_apply]
    exact isWeightedHomogeneous_X R (rowW r n) _
  rw [← mem_weightedHomogeneousSubmodule] at hk ⊢
  rw [Units.smul_def]
  exact zsmul_mem hk _

end Formalism.GradedWeylDivisibility
