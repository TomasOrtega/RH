import Formalism.HermitianCurvature.HermitianCurvatureProofs.TLPlanAsm
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BasicLift

namespace Formalism.FourierDecayAlt.TL

open Matrix Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr

/- English proof (translation)
Introduce `hstep hlet A S _ _ _ _ _ _ r n L st Lf w hA hL hn`. Proceed by induction on `w with`. Consider the case `nil`. Introduce `_ e`. Establish `h1 : ((ofWord L st ([] : List (Letter ℂ S))).F * bTA L ([] : List (Letter ℂ S))) = 1`.

Simplify using `[ofWord, bTA, bT, Start.frame]`. Rewrite using `[h1, Matrix.one_apply]`. Use `split_ifs`. Simplify using `using hL.one`. Conclude with `hL.zero _ _`.

Consider the case `cons l w ih`. Introduce `hw e`. Establish `hw' : admitted st w`. Take `⟨h1, h2, h3, h4⟩` from `hw`. Use `⟨?_, fun l' hl' => h2 l' (List.mem_cons_of_mem _ hl'), fun l' hl' => h3 l' (List.mem_cons_of_mem _ hl'), h4.of_cons⟩` and prove the remaining obligations.

Simplify using `only [List.map_cons, List.nodup_cons] at h1`. Conclude with `h1.2`. Rewrite using `[hstep A S r L st l w hA hw e, Matrix.mul_apply]`. Use `Finset.sum_induction _ (Lf _ _) (fun a b ha hb => hL.add ha hb) (hL.zero _ _) ?_` and prove the remaining obligations. Introduce `f _`.

Establish `hcoef : Lf n (9 * (r + 1) * n) ((∑ i : Fin 2, eU l.intersection_update_fsHerm_neg_one i 0 * letterCol L st l w i : SlopeTestRemainingChoices S A) e f)`. Rewrite using `[Matrix.sum_apply]`. Use `Finset.sum_induction _ (Lf _ _) (fun a b ha hb => hL.add ha hb) (hL.zero _ _) ?_` and prove the remaining obligations. Introduce `i _`. Rewrite using `[Matrix.mul_apply]`.

Use `Finset.sum_induction _ (Lf _ _) (fun a b ha hb => hL.add ha hb) (hL.zero _ _) ?_` and prove the remaining obligations. Introduce `g _`. Simplify using `only [eU, Matrix.of_apply]`. Use `split_ifs`. Rewrite using `[one_mul]`.

Conclude with `hlet A S r n L st Lf l w hA hL hn hw i g f`. Rewrite using `[zero_mul]`. Conclude with `hL.zero _ _`. Use `hL.mono ?_ ?_ (hL.mul hcoef (ih hw' f))` and prove the remaining obligations. Simplify using `only [List.length_cons]`.

Conclude with `le_of_eq (by ring)`. Simplify using `only [List.length_cons]`. Conclude with `le_of_eq (by ring)`.
-/
theorem wordLiftOfParts : WordLiftOfParts := by
  intro hstep hlet A S _ _ _ _ _ _ r n L st Lf w hA hL hn
  induction w with
  | nil =>
    intro _ e
    have h1 : ((ofWord L st ([] : List (Letter ℂ S))).F * bTA L ([] : List (Letter ℂ S))) = 1 := by
      simp [ofWord, bTA, bT, Start.frame]
    rw [h1, Matrix.one_apply]
    split_ifs
    · simpa using hL.one
    · exact hL.zero _ _
  | cons l w ih =>
    intro hw e
    have hw' : admitted st w := by
      obtain ⟨h1, h2, h3, h4⟩ := hw
      refine ⟨?_, fun l' hl' => h2 l' (List.mem_cons_of_mem _ hl'),
        fun l' hl' => h3 l' (List.mem_cons_of_mem _ hl'), h4.of_cons⟩
      simp only [List.map_cons, List.nodup_cons] at h1
      exact h1.2
    rw [hstep A S r L st l w hA hw e, Matrix.mul_apply]
    refine Finset.sum_induction _ (Lf _ _) (fun a b ha hb => hL.add ha hb) (hL.zero _ _) ?_
    intro f _
    have hcoef : Lf n (9 * (r + 1) * n) ((∑ i : Fin 2, eU l.intersection_update_fsHerm_neg_one i 0 * letterCol L st l w i : SlopeTestRemainingChoices S A) e f) := by
      rw [Matrix.sum_apply]
      refine Finset.sum_induction _ (Lf _ _) (fun a b ha hb => hL.add ha hb) (hL.zero _ _) ?_
      intro i _
      rw [Matrix.mul_apply]
      refine Finset.sum_induction _ (Lf _ _) (fun a b ha hb => hL.add ha hb) (hL.zero _ _) ?_
      intro g _
      simp only [eU, Matrix.of_apply]
      split_ifs
      · rw [one_mul]
        exact hlet A S r n L st Lf l w hA hL hn hw i g f
      · rw [zero_mul]
        exact hL.zero _ _
    refine hL.mono ?_ ?_ (hL.mul hcoef (ih hw' f))
    · simp only [List.length_cons]
      exact le_of_eq (by ring)
    · simp only [List.length_cons]
      exact le_of_eq (by ring)

end Formalism.FourierDecayAlt.TL

/- English proof (translation)
The claim follows from `Submodule.subset_span (Or.inl ⟨α, β, γ, h1, h2, h3, by rw [Matrix.mul_assoc]; rfl⟩)`.
-/
example {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [Fintype S] [DecidableEq S] (st : Formalism.FourierDecayAlt.Fr.Start A)
    (X φ τ α β γ : Formalism.FourierDecayAlt.Wd.SlopeTestRemainingChoices S A) (h1 : Formalism.FourierDecayAlt.TL.kMat st α) (h2 : Formalism.FourierDecayAlt.TL.kMat st β) (h3 : Formalism.FourierDecayAlt.TL.kMat st γ) :
    Matrix.of (fun i j => ∑ k, α i k * ((X * β - β * X) * γ) k j) ∈ Formalism.FourierDecayAlt.TL.dSpan st X φ τ :=
  Submodule.subset_span (Or.inl ⟨α, β, γ, h1, h2, h3, by rw [Matrix.mul_assoc]; rfl⟩)
