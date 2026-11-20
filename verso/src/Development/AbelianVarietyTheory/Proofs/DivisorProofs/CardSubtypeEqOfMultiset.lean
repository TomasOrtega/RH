import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCyclotomicExtensionQI

open Matrix GlobalTheory.LKTrip Finset

namespace GlobalTheory.SigDiag

/- English proof (translation)
Establish `h3` using `hA.roots_charpoly_eq_eigenvalues`. Rewrite `h3` using `[Matrix.charpoly_diagonal, Polynomial.roots_prod]`. Establish `h4` using `congrArg (Multiset.map Complex.re) h3`. Simplify using `only [Polynomial.roots_X_sub_C, Multiset.map_map] at h4`. Simplify `h4.symm` using `[Function.comp_def, Multiset.bind_singleton]`.

Simplify using `[Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero]`.
-/
theorem eigenvalues_multiset_eq {n : ℕ} (r : Fin n → ℝ)
    (hA : (Matrix.diagonal (fun i => ((r i : ℝ) : ℂ))).IsHermitian) :
    Multiset.map hA.eigenvalues univ.val = Multiset.map r univ.val := by
  have h3 := hA.roots_charpoly_eq_eigenvalues
  rw [Matrix.charpoly_diagonal, Polynomial.roots_prod] at h3
  · have h4 := congrArg (Multiset.map Complex.re) h3
    simp only [Polynomial.roots_X_sub_C, Multiset.map_map] at h4
    simpa [Function.comp_def, Multiset.bind_singleton] using h4.symm
  · simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero]

/- English proof (translation)
Rewrite using `[Fintype.card_subtype, Fintype.card_subtype]`. Establish `e : ∀ k : Fin n → ℝ, (univ.filter fun i => P (k i)).card = Multiset.countP P (Multiset.map k univ.val)`. Introduce `k`. Rewrite using `[Multiset.countP_map, Finset.card_def, Finset.filter_val]`. Rewrite using `[e f, e g, h]`.
-/
theorem card_subtype_eq_of_multiset {n : ℕ} {f g : Fin n → ℝ}
    (h : Multiset.map f univ.val = Multiset.map g univ.val) (P : ℝ → Prop) [DecidablePred P] :
    Fintype.card {i // P (f i)} = Fintype.card {i // P (g i)} := by
  rw [Fintype.card_subtype, Fintype.card_subtype]
  have e : ∀ k : Fin n → ℝ, (univ.filter fun i => P (k i)).card =
      Multiset.countP P (Multiset.map k univ.val) := by
    intro k
    rw [Multiset.countP_map, Finset.card_def, Finset.filter_val]
  rw [e f, e g, h]

end GlobalTheory.SigDiag

namespace GlobalTheory.LKTrip

/- English proof (translation)
Introduce `n r hA`. Establish `h` using `GlobalTheory.SigDiag.eigenvalues_multiset_eq r hA`. Conclude with `⟨GlobalTheory.SigDiag.card_subtype_eq_of_multiset h (fun x => 0 < x), GlobalTheory.SigDiag.card_subtype_eq_of_multiset h (fun x => x < 0)⟩`.
-/
theorem sigPosH_sigNegH_diagonal : ∀ (n : ℕ) (r : Fin n → ℝ)
    (hA : (Matrix.diagonal (fun i => ((r i : ℝ) : ℂ))).IsHermitian),
    sigPosH hA = Fintype.card {i // 0 < r i} ∧ sigNegH hA = Fintype.card {i // r i < 0} := by
  intro n r hA
  have h := GlobalTheory.SigDiag.eigenvalues_multiset_eq r hA
  exact ⟨GlobalTheory.SigDiag.card_subtype_eq_of_multiset h (fun x => 0 < x),
    GlobalTheory.SigDiag.card_subtype_eq_of_multiset h (fun x => x < 0)⟩

end GlobalTheory.LKTrip
