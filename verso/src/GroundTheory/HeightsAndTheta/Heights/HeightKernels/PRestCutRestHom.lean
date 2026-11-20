import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsRest
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

namespace KRest

/- English proof (translation)
Unfold `RestTerms.vandermondeOf`. Use `IsHomogeneous.prod _ _ _ fun i _ => ?_` and prove the remaining obligations. Establish `h` using `IsHomogeneous.prod (Finset.Ioi i) (fun j => v i - v j) (fun _ => 1) fun j _ => (hv i).sub (hv j)`. Simplify using `using h`.
-/
theorem isHomogeneous_vandermondeOf {σ R : Type*} [CommRing R] {m : ℕ}
    (v : Fin m → MvPolynomial σ R) (hv : ∀ i, (v i).IsHomogeneous 1) :
    (RestTerms.vandermondeOf v).IsHomogeneous (∑ i : Fin m, (Finset.Ioi i).card) := by
  unfold RestTerms.vandermondeOf
  refine IsHomogeneous.prod _ _ _ fun i _ => ?_
  have h := IsHomogeneous.prod (Finset.Ioi i) (fun j => v i - v j) (fun _ => 1)
    fun j _ => (hv i).sub (hv j)
  simpa using h

/- English proof (translation)
Break down `r with _ | r` into its components or cases. Simplify using the standard rewrite rules. Break down `a with _ | a` into its components or cases. Simplify using the standard rewrite rules. Establish `h1 : r + 1 + (a + 1) - 1 = r + a + 1` using `by omega`.

Rewrite using `[h1, Nat.add_sub_cancel, Nat.add_sub_cancel]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem add_mul_add_sub_one (r a : ℕ) :
    (r + a) * (r + a - 1) = r * (r - 1) + a * (a - 1) + 2 * (r * a) := by
  rcases r with _ | r
  · simp
  rcases a with _ | a
  · simp
  have h1 : r + 1 + (a + 1) - 1 = r + a + 1 := by omega
  rw [h1, Nat.add_sub_cancel, Nat.add_sub_cancel]
  ring

end KRest

/- English proof (translation)
Introduce `f r a c`. Establish `hy : ∀ τ i, (RestTerms.yRoot f r a c τ i).IsHomogeneous 1` using `fun τ i => isHomogeneous_C_mul_X _ _`. Establish `hz : ∀ τ i, (RestTerms.zRoot f r a c τ i).IsHomogeneous 1` using `fun τ i => isHomogeneous_X _ _`. Establish `hμ : (RestTerms.smallBlockMu f r a c).IsHomogeneous 1` using `IsHomogeneous.sum _ _ _ fun τ _ => IsHomogeneous.sum _ _ _ fun i _ => hy τ i`. Use `set dy := ∑ i : Fin r, (Finset.Ioi i).card with hdy`.

Use `set dz := ∑ i : Fin a, (Finset.Ioi i).card with hdz`. Establish `hfib : (RestTerms.fibreClass f r a c).IsHomogeneous (f * (dy + dz))`. Establish `h` using `IsHomogeneous.prod (Finset.univ : Finset (Fin f)) (fun τ => RestTerms.vandermondeOf (RestTerms.yRoot f r a c τ) * RestTerms.vandermondeOf (RestTerms.zRoot f r a c τ)) (fun _ => dy + dz) fun τ _ => (KRest.isHomogeneous_vandermondeOf _ (hy τ)).mul (KRest.isHomogeneous_vandermondeOf …`. Simplify `h` using `[RestTerms.fibreClass, Finset.sum_const, Finset.card_univ, Fintype.card_fin]`. Establish `hdy2 : dy * 2 = r * (r - 1)` using `KRest.sum_card_Ioi_mul_two r`.

Establish `hdz2 : dz * 2 = a * (a - 1)` using `KRest.sum_card_Ioi_mul_two a`. Establish `hdeg : 1 * (f * (r * a)) + f * (dy + dz) = RestTerms.topDegree f (r + a)`. Establish `hS : (r + a) * (r + a - 1) / 2 = r * a + (dy + dz)`. Rewrite using `[KRest.add_mul_add_sub_one, ← hdy2, ← hdz2]`. Establish `: dy * 2 + dz * 2 + 2 * (r * a) = 2 * (r * a + (dy + dz))` using `by ring`.

Rewrite using `[this, Nat.mul_div_cancel_left _ two_pos]`. Rewrite using `[RestTerms.topDegree, hS]`. Expand and normalize the polynomial expressions, which then agree. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← hdeg]`.

Conclude with `(hμ.pow _).mul hfib`. Establish `h` using `(hμ.pow (f * (r * a) + 1)).mul hfib`. Establish `he : 1 * (f * (r * a) + 1) + f * (dy + dz) = RestTerms.topDegree f (r + a) + 1`. Rewrite using `[← hdeg]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite `h` using `[he]`. Conclude with `h`.
-/
theorem RestCutRestHom.proof : RestCutRestHom.Statement := by
  intro f r a c

  have hy : ∀ τ i, (RestTerms.yRoot f r a c τ i).IsHomogeneous 1 := fun τ i =>
    isHomogeneous_C_mul_X _ _
  have hz : ∀ τ i, (RestTerms.zRoot f r a c τ i).IsHomogeneous 1 := fun τ i =>
    isHomogeneous_X _ _

  have hμ : (RestTerms.smallBlockMu f r a c).IsHomogeneous 1 :=
    IsHomogeneous.sum _ _ _ fun τ _ => IsHomogeneous.sum _ _ _ fun i _ => hy τ i

  set dy := ∑ i : Fin r, (Finset.Ioi i).card with hdy
  set dz := ∑ i : Fin a, (Finset.Ioi i).card with hdz
  have hfib : (RestTerms.fibreClass f r a c).IsHomogeneous (f * (dy + dz)) := by
    have h := IsHomogeneous.prod (Finset.univ : Finset (Fin f))
      (fun τ => RestTerms.vandermondeOf (RestTerms.yRoot f r a c τ) *
        RestTerms.vandermondeOf (RestTerms.zRoot f r a c τ)) (fun _ => dy + dz)
      fun τ _ => (KRest.isHomogeneous_vandermondeOf _ (hy τ)).mul
        (KRest.isHomogeneous_vandermondeOf _ (hz τ))
    simpa [RestTerms.fibreClass, Finset.sum_const, Finset.card_univ, Fintype.card_fin] using h

  have hdy2 : dy * 2 = r * (r - 1) := KRest.sum_card_Ioi_mul_two r
  have hdz2 : dz * 2 = a * (a - 1) := KRest.sum_card_Ioi_mul_two a
  have hdeg : 1 * (f * (r * a)) + f * (dy + dz) = RestTerms.topDegree f (r + a) := by
    have hS : (r + a) * (r + a - 1) / 2 = r * a + (dy + dz) := by
      rw [KRest.add_mul_add_sub_one, ← hdy2, ← hdz2]
      have : dy * 2 + dz * 2 + 2 * (r * a) = 2 * (r * a + (dy + dz)) := by ring
      rw [this, Nat.mul_div_cancel_left _ two_pos]
    rw [RestTerms.topDegree, hS]
    ring
  refine ⟨?_, ?_⟩
  · rw [← hdeg]
    exact (hμ.pow _).mul hfib
  · have h := (hμ.pow (f * (r * a) + 1)).mul hfib
    have he : 1 * (f * (r * a) + 1) + f * (dy + dz) = RestTerms.topDegree f (r + a) + 1 := by
      rw [← hdeg]; ring
    rw [he] at h
    exact h

end GroundTheory.Heights₂.Heights
