import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SchubGamApply
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

namespace GlobalTheory.Schubert

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

/- English proof (translation)
Establish `he : GlobalTheory.AllWt.exOf Dw la 0 (some ⟨τ.1, Fin.cast (GlobalTheory.PointChern.mult_of_mem Dw τ.2).symm i⟩) = (GlobalTheory.AllWt.wtOf Dw la 0).1 (τ.1, (i : ℕ))` using `rfl`. Rewrite using `[he, GlobalTheory.AllWt.wtOf_big la 0 τ i i.2]`. Unfold `flagRoot`. Rewrite using `[dif_pos τ.2]`. Simplify using `only [sub_zero, map_neg, neg_mul, neg_neg]`.

Both sides reduce to the same expression.
-/
theorem flagRoot_term_big {H : Host E} (Dw : Datum H) (la : GlobalTheory.AllWt.Weight Dw) (τ : GlobalTheory.AllWt.Psi H)
    (i : Fin Dw.p) :
    C (-(GlobalTheory.AllWt.exOf Dw la 0 (some ⟨τ.1, Fin.cast (GlobalTheory.PointChern.mult_of_mem Dw τ.2).symm i⟩) : ℝ)) *
        flagRoot Dw ⟨τ.1, Fin.cast (GlobalTheory.PointChern.mult_of_mem Dw τ.2).symm i⟩ =
      -(C ((la τ (Fin.castAdd Dw.q i) : ℤ) : ℝ) * X (τ, Fin.castAdd Dw.q i)) := by
  have he : GlobalTheory.AllWt.exOf Dw la 0 (some ⟨τ.1, Fin.cast (GlobalTheory.PointChern.mult_of_mem Dw τ.2).symm i⟩) =
      (GlobalTheory.AllWt.wtOf Dw la 0).1 (τ.1, (i : ℕ)) := rfl
  rw [he, GlobalTheory.AllWt.wtOf_big la 0 τ i i.2]
  unfold flagRoot
  rw [dif_pos τ.2]
  simp only [sub_zero, map_neg, neg_mul, neg_neg]
  rfl

/- English proof (translation)
Establish `he : GlobalTheory.AllWt.exOf Dw la 0 (some ⟨conjEmb τ.1, Fin.cast (GlobalTheory.PointChern.mult_of_not_mem Dw (GlobalTheory.AllWt.conj_not_mem τ)).symm i⟩) = (GlobalTheory.AllWt.wtOf Dw la 0).1 (conjEmb τ.1, (i : ℕ))` using `rfl`. Establish `hj : (⟨Dw.p + (Dw.q - 1 - (i : ℕ)), by omega⟩ : Fin (Dw.p + Dw.q)) = Fin.natAdd Dw.p (Fin.rev i)` using `by ext; simp [Fin.val_rev]; omega`. Rewrite using `[he, GlobalTheory.AllWt.wtOf_small la 0 τ i i.2, hj]`. Unfold `flagRoot`. Rewrite using `[dif_neg (GlobalTheory.AllWt.conj_not_mem τ)]`.

Establish `hτ : (⟨conjEmb (conjEmb τ.1), GlobalTheory.AllWt.conj_mem (GlobalTheory.AllWt.conj_not_mem τ)⟩ : GlobalTheory.AllWt.Psi H) = τ` using `Subtype.ext (GlobalTheory.AllWt.conjEmb_conjEmb _)`. Establish `hx : ((⟨conjEmb (conjEmb τ.1), GlobalTheory.AllWt.conj_mem (GlobalTheory.AllWt.conj_not_mem τ)⟩ : GlobalTheory.AllWt.Psi H), (⟨Dw.p + (Dw.q - 1 - (i : ℕ)), by omega⟩ : Fin (Dw.p + Dw.q))) = (τ, Fin.natAdd Dw.p (Fin.rev i))`. Rewrite using `[hτ, hj]`. Simplify using `only [Fin.val_cast] at *`. Rewrite using `[hx]`.

Simplify using `only [sub_zero, Int.cast_neg, neg_neg, mul_neg]`.
-/
theorem flagRoot_term_small {H : Host E} (Dw : Datum H) (la : GlobalTheory.AllWt.Weight Dw) (τ : GlobalTheory.AllWt.Psi H)
    (i : Fin Dw.q) :
    C (-(GlobalTheory.AllWt.exOf Dw la 0
          (some ⟨conjEmb τ.1, Fin.cast (GlobalTheory.PointChern.mult_of_not_mem Dw (GlobalTheory.AllWt.conj_not_mem τ)).symm i⟩) : ℝ)) *
        flagRoot Dw ⟨conjEmb τ.1, Fin.cast (GlobalTheory.PointChern.mult_of_not_mem Dw (GlobalTheory.AllWt.conj_not_mem τ)).symm i⟩ =
      -(C ((la τ (Fin.natAdd Dw.p (Fin.rev i)) : ℤ) : ℝ) * X (τ, Fin.natAdd Dw.p (Fin.rev i))) := by
  have he : GlobalTheory.AllWt.exOf Dw la 0
      (some ⟨conjEmb τ.1, Fin.cast (GlobalTheory.PointChern.mult_of_not_mem Dw (GlobalTheory.AllWt.conj_not_mem τ)).symm i⟩) =
      (GlobalTheory.AllWt.wtOf Dw la 0).1 (conjEmb τ.1, (i : ℕ)) := rfl
  have hj : (⟨Dw.p + (Dw.q - 1 - (i : ℕ)), by omega⟩ : Fin (Dw.p + Dw.q)) = Fin.natAdd Dw.p (Fin.rev i) := by
    ext; simp [Fin.val_rev]; omega
  rw [he, GlobalTheory.AllWt.wtOf_small la 0 τ i i.2, hj]
  unfold flagRoot
  rw [dif_neg (GlobalTheory.AllWt.conj_not_mem τ)]
  have hτ : (⟨conjEmb (conjEmb τ.1), GlobalTheory.AllWt.conj_mem (GlobalTheory.AllWt.conj_not_mem τ)⟩ : GlobalTheory.AllWt.Psi H) = τ :=
    Subtype.ext (GlobalTheory.AllWt.conjEmb_conjEmb _)
  have hx : ((⟨conjEmb (conjEmb τ.1), GlobalTheory.AllWt.conj_mem (GlobalTheory.AllWt.conj_not_mem τ)⟩ : GlobalTheory.AllWt.Psi H),
      (⟨Dw.p + (Dw.q - 1 - (i : ℕ)), by omega⟩ : Fin (Dw.p + Dw.q))) = (τ, Fin.natAdd Dw.p (Fin.rev i)) := by
    rw [hτ, hj]
  simp only [Fin.val_cast] at *
  rw [hx]
  simp only [sub_zero, Int.cast_neg, neg_neg, mul_neg]

/- English proof (translation)
Simplify using `only [flagMap, map_sum, map_mul, aeval_C, aeval_X, MvPolynomial.algebraMap_eq]`. Rewrite using `[Fintype.sum_sigma, ← Fintype.sum_subtype_add_sum_subtype (fun τ : E →+* ℂ => τ (H.rt : E) = H.rt0)]`. Set `e : GlobalTheory.AllWt.Psi H ≃ {τ : E →+* ℂ // ¬ τ (H.rt : E) = H.rt0}` to `{ toFun := fun τ => ⟨conjEmb τ.1, GlobalTheory.AllWt.conj_not_mem τ⟩ invFun := fun τ => ⟨conjEmb τ.1, GlobalTheory.AllWt.conj_mem τ.2⟩ left_inv := fun τ => Subtype.ext (GlobalTheory.AllWt.conjEmb_conjEmb _) right_inv := fun τ => Subtype.ext (GlobalTheory.AllWt.conjEmb_conjEmb _) …`. Rewrite using `[← e.sum_comp]`. Unfold `Formalism.DegreeFormula.linRoot`.

Rewrite using `[Fintype.sum_prod_type]`. Simplify using `only [Fin.sum_univ_add, Finset.sum_add_distrib, neg_add]`. Use `congr 1`. Rewrite using `[← Finset.sum_neg_distrib]`. Use `Finset.sum_congr rfl fun τ _ => ?_` and prove the remaining obligations.

Rewrite using `[← Fin.sum_congr' (fun i => C (-(GlobalTheory.AllWt.exOf Dw la 0 (some ⟨τ.1, i⟩) : ℝ)) * flagRoot Dw ⟨τ.1, i⟩) (GlobalTheory.PointChern.mult_of_mem Dw τ.2).symm, ← Finset.sum_neg_distrib]`. Conclude with `Finset.sum_congr rfl fun i _ => flagRoot_term_big Dw la τ i`. Rewrite using `[← Finset.sum_neg_distrib]`. Use `Finset.sum_congr rfl fun τ _ => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `∑ i : Fin (Dw.mult (conjEmb τ.1)), C (-(GlobalTheory.AllWt.exOf Dw la 0 (some ⟨conjEmb τ.1, i⟩) : ℝ)) * flagRoot Dw ⟨conjEmb τ.1, i⟩ = _`.

Rewrite using `[← Fin.sum_congr' (fun i => C (-(GlobalTheory.AllWt.exOf Dw la 0 (some ⟨conjEmb τ.1, i⟩) : ℝ)) * flagRoot Dw ⟨conjEmb τ.1, i⟩) (GlobalTheory.PointChern.mult_of_not_mem Dw (GlobalTheory.AllWt.conj_not_mem τ)).symm, ← Equiv.sum_comp (Fin.revPerm (n := Dw.q)) (fun i => C ((la τ (Fin …`. Conclude with `Finset.sum_congr rfl fun i _ => flagRoot_term_small Dw la τ i`.
-/
theorem chernRootSubstitution_weightLineBundle_eq_linRoot (H : Host E) (Dw : Datum H) (la : GlobalTheory.AllWt.Weight Dw) :
    flagMap Dw (∑ x : GlobalTheory.GoodMetric.Root Dw.mult,
        MvPolynomial.C (-(GlobalTheory.AllWt.exOf Dw la 0 (some x) : ℝ)) * MvPolynomial.X x) =
      Formalism.DegreeFormula.linRoot (fun τ i => (la τ i : ℝ)) := by
  simp only [flagMap, map_sum, map_mul, aeval_C, aeval_X, MvPolynomial.algebraMap_eq]
  rw [Fintype.sum_sigma, ← Fintype.sum_subtype_add_sum_subtype (fun τ : E →+* ℂ => τ (H.rt : E) = H.rt0)]
  let e : GlobalTheory.AllWt.Psi H ≃ {τ : E →+* ℂ // ¬ τ (H.rt : E) = H.rt0} :=
    { toFun := fun τ => ⟨conjEmb τ.1, GlobalTheory.AllWt.conj_not_mem τ⟩
      invFun := fun τ => ⟨conjEmb τ.1, GlobalTheory.AllWt.conj_mem τ.2⟩
      left_inv := fun τ => Subtype.ext (GlobalTheory.AllWt.conjEmb_conjEmb _)
      right_inv := fun τ => Subtype.ext (GlobalTheory.AllWt.conjEmb_conjEmb _) }
  rw [← e.sum_comp]
  unfold Formalism.DegreeFormula.linRoot
  rw [Fintype.sum_prod_type]
  simp only [Fin.sum_univ_add, Finset.sum_add_distrib, neg_add]
  congr 1
  · rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [← Fin.sum_congr' (fun i => C (-(GlobalTheory.AllWt.exOf Dw la 0 (some ⟨τ.1, i⟩) : ℝ)) * flagRoot Dw ⟨τ.1, i⟩)
      (GlobalTheory.PointChern.mult_of_mem Dw τ.2).symm, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ => flagRoot_term_big Dw la τ i
  · rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun τ _ => ?_
    change ∑ i : Fin (Dw.mult (conjEmb τ.1)), C (-(GlobalTheory.AllWt.exOf Dw la 0 (some ⟨conjEmb τ.1, i⟩) : ℝ)) *
        flagRoot Dw ⟨conjEmb τ.1, i⟩ = _
    rw [← Fin.sum_congr' (fun i => C (-(GlobalTheory.AllWt.exOf Dw la 0 (some ⟨conjEmb τ.1, i⟩) : ℝ)) *
        flagRoot Dw ⟨conjEmb τ.1, i⟩) (GlobalTheory.PointChern.mult_of_not_mem Dw (GlobalTheory.AllWt.conj_not_mem τ)).symm,
      ← Equiv.sum_comp (Fin.revPerm (n := Dw.q)) (fun i => C ((la τ (Fin.natAdd Dw.p i) : ℤ) : ℝ) *
        X (τ, Fin.natAdd Dw.p i)), ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ => flagRoot_term_small Dw la τ i

end GlobalTheory.Schubert
