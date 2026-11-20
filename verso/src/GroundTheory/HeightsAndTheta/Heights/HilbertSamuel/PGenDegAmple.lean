import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsGenDegAmple
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsGenericFibreVar
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsMultiDegreePositive
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenDegTwist
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PIntersectionRecursion
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I1

noncomputable section

namespace GenDegAmple

open GroundTheory.Heights₂.Heights.NumbersDVR

/- English proof (translation)
Unfold `hilbFn`. Use `split_ifs`. Conclude with `Int.natCast_nonneg _`. Conclude with `le_rfl`.
-/
theorem hilbFn_nonneg {F : Type} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
    [∀ k, Fintype (ι k)] (q : Ideal (MRing ι F)) (m : K → ℤ) : 0 ≤ hilbFn q m := by
  unfold hilbFn
  split_ifs
  · exact Int.natCast_nonneg _
  · exact le_rfl

/- English proof (translation)
Unfold `eventualValue`. Use `split_ifs with h`. Take `⟨m, hm⟩` from `h.choose_spec.exists`. Rewrite using `[← hm]`. Conclude with `hf m`.

Conclude with `le_rfl`.
-/
theorem eventualValue_nonneg {K : Type} [Fintype K] (f : (K → ℤ) → ℤ) (hf : ∀ m, 0 ≤ f m) :
    0 ≤ eventualValue f := by
  unfold eventualValue
  split_ifs with h
  · obtain ⟨m, hm⟩ := h.choose_spec.exists
    rw [← hm]
    exact hf m
  · exact le_rfl

/- English proof (translation)
Proceed by induction on `e with`. Consider the case `zero`. Introduce `q _ _ r`. Unfold `intNum mixedDiff`. Rewrite using `[List.ofFn_zero, List.foldr_nil]`.

Conclude with `eventualValue_nonneg _ (hilbFn_nonneg q)`. Consider the case `succ e ih`. Introduce `q hq hd r`. Take `⟨i, hX⟩` from `hq.relevant (r 0)`. Establish `hd' : ringKrullDim (MRing ι F ⧸ q) = ((e + 1 + Fintype.card K : ℕ) : WithBot ℕ∞)` using `hd`.

Establish `hsplit : (fun j : Fin (e + 1) => unitDeg (r j)) = Matrix.vecCons (unitDeg (r 0)) (fun j : Fin e => unitDeg (r j.succ))`. Use function extensionality and compare the values at `j`. Apply the tactic sequence `refine Fin.cases ?_ (fun j => ?_) j <;> simp`. Rewrite using `[hsplit, IntersectionRecursion.proof F K ι q e hq hd' (r 0) i hX]`. Use `finsum_nonneg fun W => ?_` and prove the remaining obligations.

Use `split_ifs with h`. Conclude with `mul_nonneg (Int.natCast_nonneg _) (ih W h.1 h.2.2 _)`. Conclude with `le_rfl`.
-/
theorem unit_nonneg {F : Type} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
    [∀ k, Fintype (ι k)] (e : ℕ) : ∀ q : Ideal (MRing ι F), NumbersDVR.IsMultiProjPrime q →
    ringKrullDim (MRing ι F ⧸ q) = ((e + Fintype.card K : ℕ) : WithBot ℕ∞) →
    ∀ r : Fin e → K, 0 ≤ intNum F q (fun j => unitDeg (r j)) := by
  induction e with
  | zero =>
    intro q _ _ r
    unfold intNum mixedDiff
    rw [List.ofFn_zero, List.foldr_nil]
    exact eventualValue_nonneg _ (hilbFn_nonneg q)
  | succ e ih =>
    intro q hq hd r
    obtain ⟨i, hX⟩ := hq.relevant (r 0)
    have hd' : ringKrullDim (MRing ι F ⧸ q) = ((e + 1 + Fintype.card K : ℕ) : WithBot ℕ∞) := hd
    have hsplit : (fun j : Fin (e + 1) => unitDeg (r j)) =
        Matrix.vecCons (unitDeg (r 0)) (fun j : Fin e => unitDeg (r j.succ)) := by
      funext j
      refine Fin.cases ?_ (fun j => ?_) j <;> simp
    rw [hsplit, IntersectionRecursion.proof F K ι q e hq hd' (r 0) i hX]
    refine finsum_nonneg fun W => ?_
    split_ifs with h
    · exact mul_nonneg (Int.natCast_nonneg _) (ih W h.1 h.2.2 _)
    · exact le_rfl

end GenDegAmple

/- English proof (translation)
Introduce `K _ ι _ Ω _ y D d hV hd`. Establish `hPV` using `hVar K ι Ω y D hV`. Establish `hP` using `(Bridge.isMultiProjPrime_iff _).mpr hPV.1`. Establish `hrel : FieldNumbers.relDim (KH.genIdeal y) = D`. Rewrite using `[FieldNumbers.relDim_of_ringKrullDim_eq _ _ hPV.2]`.

Simplify using `only [Nat.cast_add, add_sub_cancel_right]`. Both sides reduce to the same expression. Use `set f := intNumMultilinear (KH.genIdeal y) D hP.multiHomog hP.relevant hrel with hf`. Establish `hg : ∀ b, genDeg (mCoordIdeal y) D b = f (fun _ => b)` using `fun b => by`. Rewrite using `[hf, intNumMultilinear_apply, genDeg]`.

Reduce the equality to equality of the corresponding arguments. Establish `hN : ∀ r : Fin D → K, 0 ≤ f (fun j => unitDeg (r j))` using `fun r => by`. Rewrite using `[hf, intNumMultilinear_apply]`. Conclude with `GenDegAmple.unit_nonneg D _ hP hPV.2 r`. Establish `hH : 0 < f (fun _ => fun _ => (1 : ℤ))`.

Rewrite using `[hf, intNumMultilinear_apply]`. Conclude with `hPos ℚ K ι _ D hP hPV.2`. Establish `hsum : ∀ b : K → ℤ, (fun _ : Fin D => b) = fun _ => ∑ k, b k • unitDeg k` using `fun b => by`. Use function extensionality and compare the values at `_ k'`. Simplify using `[unitDeg, Finset.sum_apply, Pi.single_apply]`.

Establish `expand : ∀ b : K → ℤ, f (fun _ => b) = ∑ r : Fin D → K, (∏ j, b (r j)) * f (fun j => unitDeg (r j))` using `fun b => by`. Rewrite using `[hsum b, f.map_sum]`. Use `Finset.sum_congr rfl fun r _ => ?_` and prove the remaining obligations. Rewrite using `[f.map_smul_univ (fun j => b (r j)) (fun j => unitDeg (r j)), smul_eq_mul]`. Rewrite using `[hg, expand d]`.

Establish `hH'` using `hH`. Rewrite `hH'` using `[expand (fun _ => (1 : ℤ))]`. Simplify using `only [Finset.prod_const_one, one_mul] at hH'`. Use `lt_of_lt_of_le hH' (Finset.sum_le_sum fun r _ => ?_)` and prove the remaining obligations. Establish `hp : (1 : ℤ) ≤ ∏ j, d (r j)`.

Combine the equalities or inequalities in the displayed calculation. Conclude with `le_mul_of_one_le_left (hN r) hp`.
-/
theorem GenDegAmple.proof (hVar : GenericFibreVar.Statement) (hPos : MultiDegreePositive.Statement) :
    GenDegAmple.Statement := by
  intro K _ ι _ Ω _ y D d hV hd
  classical
  have hPV := hVar K ι Ω y D hV
  have hP := (Bridge.isMultiProjPrime_iff _).mpr hPV.1
  have hrel : FieldNumbers.relDim (KH.genIdeal y) = D := by
    rw [FieldNumbers.relDim_of_ringKrullDim_eq _ _ hPV.2]
    simp only [Nat.cast_add, add_sub_cancel_right]
    rfl
  set f := intNumMultilinear (KH.genIdeal y) D hP.multiHomog hP.relevant hrel with hf
  have hg : ∀ b, genDeg (mCoordIdeal y) D b = f (fun _ => b) := fun b => by
    rw [hf, intNumMultilinear_apply, genDeg]
    congr
  have hN : ∀ r : Fin D → K, 0 ≤ f (fun j => unitDeg (r j)) := fun r => by
    rw [hf, intNumMultilinear_apply]
    exact GenDegAmple.unit_nonneg D _ hP hPV.2 r
  have hH : 0 < f (fun _ => fun _ => (1 : ℤ)) := by
    rw [hf, intNumMultilinear_apply]
    exact hPos ℚ K ι _ D hP hPV.2
  have hsum : ∀ b : K → ℤ, (fun _ : Fin D => b) = fun _ => ∑ k, b k • unitDeg k := fun b => by
    funext _ k'
    simp [unitDeg, Finset.sum_apply, Pi.single_apply]
  have expand : ∀ b : K → ℤ,
      f (fun _ => b) = ∑ r : Fin D → K, (∏ j, b (r j)) * f (fun j => unitDeg (r j)) := fun b => by
    rw [hsum b, f.map_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [f.map_smul_univ (fun j => b (r j)) (fun j => unitDeg (r j)), smul_eq_mul]
  rw [hg, expand d]
  have hH' := hH
  rw [expand (fun _ => (1 : ℤ))] at hH'
  simp only [Finset.prod_const_one, one_mul] at hH'
  refine lt_of_lt_of_le hH' (Finset.sum_le_sum fun r _ => ?_)
  have hp : (1 : ℤ) ≤ ∏ j, d (r j) := by
    calc (1 : ℤ) = ∏ _j : Fin D, (1 : ℤ) := Finset.prod_const_one.symm
      _ ≤ ∏ j, d (r j) := Finset.prod_le_prod (fun _ _ => zero_le_one) (fun j _ => hd (r j))
  exact le_mul_of_one_le_left (hN r) hp

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
