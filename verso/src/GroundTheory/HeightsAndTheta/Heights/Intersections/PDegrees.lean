import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.AnalyticResolutionHypothesesProjectiveLine
import GroundTheory.HeightsAndTheta.Heights.Intersections.IsSmoothMetricOfIsSmoothHerm
import GroundTheory.HeightsAndTheta.Heights.Intersections.CompsDim
import GroundTheory.HeightsAndTheta.Heights.Intersections.StResExists
import GroundTheory.HeightsAndTheta.Heights.Intersections.PZIntAdd
import GroundTheory.HeightsAndTheta.Heights.Intersections.StZIntPoint
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Assembly
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedF
import ReciprocityTheory.AnalyticForms.PotentialTheory.Stokes
import ReciprocityTheory.AnalyticForms.PotentialTheory.PLCurveA
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

open MvPolynomial
open GroundTheory.Heights₂.Heights.NumbersDVR (MRing IsMultiHomog IsMultiProjPrime divCycle intNum cycEval)
open GroundTheory.Heights₂.Heights.FieldNumbers (CutRegular.full IntNumSymm.full IntNumAdd.full IntNumBase.full
  homFracDegZero)

set_option linter.unusedSectionVars false

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

/- English proof (translation)
Unfold `zInt`. Use `split_ifs with h`. Unfold `Res.int`. Rewrite using `[← ReciprocityTheory.AnForm.M.mIntConstPot h.some.atlas c (fun j => h.some.pot (φ j)) (fun x => g (h.some.pt x))]`. Use `ReciprocityTheory.AnForm.M.PLC.mInt_congr_phi _ _ _ (fun i a b => ?_) _` and prove the remaining obligations.

Apply the tactic sequence `cases i using Fin.cases <;> rfl`. Both sides reduce to the same expression.
-/
theorem zInt_cons_const (P : Ideal (MRing ι ℂ)) (e : ℕ) (c : ℝ) (φ : Fin e → MCone ι → ℝ)
    (g : MCone ι → ℝ) : zInt P (e + 1) (Fin.cons (fun _ => c) φ) g = 0 := by
  unfold zInt
  split_ifs with h
  · unfold Res.int
    rw [← ReciprocityTheory.AnForm.M.mIntConstPot h.some.atlas c (fun j => h.some.pot (φ j))
      (fun x => g (h.some.pt x))]
    refine ReciprocityTheory.AnForm.M.PLC.mInt_congr_phi _ _ _ (fun i a b => ?_) _
    cases i using Fin.cases <;> rfl
  · rfl

/- English proof (translation)
Assemble the required witnesses or components as `⟨hz.1, fun f hf => hz.2 f (h hf)⟩`.
-/
theorem zPts_anti {P W : Ideal (MRing ι ℂ)} (h : P ≤ W) {z : MCone ι} (hz : z ∈ zPts W) :
    z ∈ zPts P :=
  ⟨hz.1, fun f hf => hz.2 f (h hf)⟩

/- English proof (translation)
Introduce `z hz`. Take `⟨U, hU, G, hG, hGU⟩` from `hL z (zPts_anti h hz)`. Conclude with `⟨U, hU, G, hG, fun w hw => hGU w ⟨hw.1, zPts_anti h hw.2⟩⟩`.
-/
theorem isSmoothMetric_mono {P W : Ideal (MRing ι ℂ)} (h : P ≤ W) {L : HLine ι}
    (hL : IsSmoothMetric P L) : IsSmoothMetric W L := by
  intro z hz
  obtain ⟨U, hU, G, hG, hGU⟩ := hL z (zPts_anti h hz)
  exact ⟨U, hU, G, hG, fun w hw => hGU w ⟨hw.1, zPts_anti h hw.2⟩⟩

/- English proof (translation)
Introduce `z hz`. Take `⟨U, hU, G, hG, hGU⟩` from `hA z hz`. Take `⟨V, hV, H, hH, hHV⟩` from `hB z hz`. Use `⟨U ∩ V, Filter.inter_mem hU hV, G + H, (hG.mono Set.inter_subset_left).add (hH.mono Set.inter_subset_right), fun w hw => ?_⟩` and prove the remaining obligations. Establish `hw0 : ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0` using `hw.2.1`.

Use `show Real.log (A.h w * B.h w) = G w + H w`. Rewrite using `[Real.log_mul (A.pos w hw0).ne' (B.pos w hw0).ne', ← hGU w ⟨hw.1.1, hw.2⟩, ← hHV w ⟨hw.1.2, hw.2⟩]`. Both sides reduce to the same expression.
-/
theorem isSmoothMetric_tensor {P : Ideal (MRing ι ℂ)} {A B : HLine ι} (hA : IsSmoothMetric P A)
    (hB : IsSmoothMetric P B) :
    IsSmoothMetric P (ReciprocityTheory.ChartRestriction.G.Geo.HermLine.tensor A B) := by
  intro z hz
  obtain ⟨U, hU, G, hG, hGU⟩ := hA z hz
  obtain ⟨V, hV, H, hH, hHV⟩ := hB z hz
  refine ⟨U ∩ V, Filter.inter_mem hU hV, G + H,
    (hG.mono Set.inter_subset_left).add (hH.mono Set.inter_subset_right), fun w hw => ?_⟩
  have hw0 : ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0 := hw.2.1
  show Real.log (A.h w * B.h w) = G w + H w
  rw [Real.log_mul (A.pos w hw0).ne' (B.pos w hw0).ne', ← hGU w ⟨hw.1.1, hw.2⟩,
    ← hHV w ⟨hw.1.2, hw.2⟩]
  rfl

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun _ _ _ _ => rfl, fun _ _ => ⟨Set.univ, Filter.univ_mem, fun _ => 1, contDiffOn_const, fun _ _ => rfl⟩⟩`.
-/
theorem isSmoothFn_one (P : Ideal (MRing ι ℂ)) : IsSmoothFn P (fun _ => (1 : ℝ)) :=
  ⟨fun _ _ _ _ => rfl, fun _ _ => ⟨Set.univ, Filter.univ_mem, fun _ => 1, contDiffOn_const,
    fun _ _ => rfl⟩⟩

/- English proof (translation)
Use function extensionality and compare the values at `i`. Consider the cases of `i using Fin.lastCases with`. Consider the case `last => simp`. Consider the case `cast i`. Simplify using `only [Function.comp_apply, finRotate_apply, Fin.coeSucc_eq_succ, Fin.cons_succ, Fin.snoc_castSucc]`.
-/
theorem cons_comp_finRotate {n : ℕ} (c : K → ℤ) (bs : Fin n → K → ℤ) :
    (Fin.cons c bs : Fin (n + 1) → K → ℤ) ∘ finRotate (n + 1) =
      Fin.snoc (α := fun _ => K → ℤ) bs c := by
  funext i
  cases i using Fin.lastCases with
  | last => simp
  | cast i =>
    simp only [Function.comp_apply, finRotate_apply, Fin.coeSucc_eq_succ, Fin.cons_succ,
      Fin.snoc_castSucc]

/- English proof (translation)
Take `⟨s, hs, hsP⟩` from `exists_form hP.1 c`. Establish `hW : ∀ W ∈ comps P s, IsProjVar W e` using `fun W hW => isProjVar_of_mem_comps hP hs hsP hW`. Establish `h1` using `hPL1 K ι P e L E s (fun _ => 1) hP (hRes K ι P (e + 1) hP) (fun W hW' => hRes K ι W e (hW W hW')) hL hE ⟨c, hEc, hs, hsP⟩ (isSmoothFn_one P)`. Rewrite `h1` using `[zInt_cons_const]`. Establish `hfin : (comps P s).Finite` using `(Ideal.finite_minimalPrimes_of_isNoetherianRing _ (P ⊔ Ideal.span {s})).subset fun W h => h.1`.

Establish `hsupp : Function.support (fun W => divCycle P s W * intNum ℂ W fun j => (L j).a) ⊆ (hfin.toFinset : Set (Ideal (MRing ι ℂ)))`. Introduce `W hW`. Rewrite using `[Set.Finite.coe_toFinset]`. Assume the negation of the conclusion as `h`. Conclude with `hW (by simp only [divCycle, dif_neg (show ¬ (W ∈ (P ⊔ Ideal.span {s}).minimalPrimes ∧ GroundTheory.Heights₂.Heights.NumbersDVR.IsRelevant W) from h), zero_mul])`.

Establish `hsum : (∑ᶠ W ∈ comps P s, (divCycle P s W : ℝ) * zInt W e (fun j => logH (L j)) (fun _ => 1)) = ((cycEval (fun W => intNum ℂ W fun j => (L j).a) (divCycle P s) : ℤ) : ℝ)`. Rewrite using `[finsum_mem_eq_finite_toFinset_sum _ hfin, cycEval, finsum_eq_sum_of_support_subset _ hsupp]`. Use `push_cast`. Use `Finset.sum_congr rfl fun W hWm => ?_` and prove the remaining obligations. Rewrite `hWm` using `[Set.Finite.mem_toFinset]`.

Rewrite using `[ih W L (hW W hWm) fun j => isSmoothMetric_mono (le_sup_left.trans hWm.1.1.2) (hL j)]`. Establish `hcut` using `CutRegular.full ℂ K ι P hP.1 e (relDim_of_isProjVar hP) c s hs hsP fun j => (L j).a`. Establish `hsymm` using `IntNumSymm.full ℂ K ι P (e + 1) (Fin.cons (fun k => (c k : ℤ)) fun j => (L j).a) (finRotate (e + 1))`. Rewrite `hsymm` using `[cons_comp_finRotate, hcut]`. Rewrite using `[← hsymm]`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem degrees_step (hPL1 : PoincareLelongAlt.Statement) (hRes : ResExists.Statement) {e : ℕ}
    (ih : ∀ (W : Ideal (MRing ι ℂ)) (L : Fin e → HLine ι), IsProjVar W e →
      (∀ j, IsSmoothMetric W (L j)) →
      zInt W e (fun j => logH (L j)) (fun _ => 1) = (intNum ℂ W (fun j => (L j).a) : ℝ))
    {P : Ideal (MRing ι ℂ)} (hP : IsProjVar P (e + 1)) (L : Fin e → HLine ι)
    (hL : ∀ j, IsSmoothMetric P (L j)) (E : HLine ι) (c : K → ℕ) (hEc : ∀ k, E.a k = c k)
    (hE : IsSmoothMetric P E) :
    zInt P (e + 1) (Fin.cons (logH E) fun j => logH (L j)) (fun _ => 1) =
      (intNum ℂ P (Fin.cons (fun k => (c k : ℤ)) fun j => (L j).a) : ℝ) := by
  obtain ⟨s, hs, hsP⟩ := exists_form hP.1 c
  have hW : ∀ W ∈ comps P s, IsProjVar W e := fun W hW => isProjVar_of_mem_comps hP hs hsP hW
  have h1 := hPL1 K ι P e L E s (fun _ => 1) hP (hRes K ι P (e + 1) hP)
    (fun W hW' => hRes K ι W e (hW W hW')) hL hE ⟨c, hEc, hs, hsP⟩ (isSmoothFn_one P)
  rw [zInt_cons_const] at h1
  have hfin : (comps P s).Finite :=
    (Ideal.finite_minimalPrimes_of_isNoetherianRing _ (P ⊔ Ideal.span {s})).subset fun W h => h.1
  have hsupp : Function.support (fun W => divCycle P s W * intNum ℂ W fun j => (L j).a) ⊆
      (hfin.toFinset : Set (Ideal (MRing ι ℂ))) := by
    intro W hW
    rw [Set.Finite.coe_toFinset]
    by_contra h
    exact hW (by simp only [divCycle, dif_neg (show ¬ (W ∈ (P ⊔ Ideal.span {s}).minimalPrimes ∧
      GroundTheory.Heights₂.Heights.NumbersDVR.IsRelevant W) from h), zero_mul])
  have hsum : (∑ᶠ W ∈ comps P s, (divCycle P s W : ℝ) * zInt W e (fun j => logH (L j)) (fun _ => 1)) =
      ((cycEval (fun W => intNum ℂ W fun j => (L j).a) (divCycle P s) : ℤ) : ℝ) := by
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin, cycEval, finsum_eq_sum_of_support_subset _ hsupp]
    push_cast
    refine Finset.sum_congr rfl fun W hWm => ?_
    rw [Set.Finite.mem_toFinset] at hWm
    rw [ih W L (hW W hWm) fun j => isSmoothMetric_mono
      (le_sup_left.trans hWm.1.1.2) (hL j)]
  have hcut := CutRegular.full ℂ K ι P hP.1 e (relDim_of_isProjVar hP) c s hs hsP fun j => (L j).a
  have hsymm := IntNumSymm.full ℂ K ι P (e + 1) (Fin.cons (fun k => (c k : ℤ)) fun j => (L j).a)
    (finRotate (e + 1))
  rw [cons_comp_finRotate, hcut] at hsymm
  rw [← hsymm]
  linarith

/- English proof (translation)
Proceed by induction on `e with`. Consider the case `zero`. Introduce `P L hP _`. Rewrite using `[hPt K ι P _ hP (hRes K ι P 0 hP)]`. Establish `hrel : GroundTheory.Heights₂.Heights.FieldNumbers.relDim P = 0`.

Rewrite using `[relDim_of_isProjVar hP]`. Both sides reduce to the same expression. Take `⟨hfd, hb⟩` from `IntNumBase.full ℂ K ι P hP.1 hrel`. Use `hP.1.isPrime` as an intermediate fact. Establish `hbot : homFracDegZero P = ⊥` using `IntermediateField.eq_bot_of_isAlgClosed_of_isAlgebraic _`.

Establish `h1 : Module.finrank ℂ (homFracDegZero P) = 1` using `IntermediateField.finrank_eq_one_iff.mpr hbot`. Establish `hL0 : (fun j => (L j).a) = (![] : Fin 0 → K → ℤ)` using `Subsingleton.elim _ _`. Rewrite using `[hL0, hb, h1]`. Evaluate the numerical expressions. Consider the case `succ e ih`.

Introduce `P M hP hM`. Use `set A := M 0`. Use `set L : Fin e → HLine ι := fun j => M j.succ`. Establish `hL : ∀ j, IsSmoothMetric P (L j)` using `fun j => hM j.succ`. Establish `hlog : (fun j => logH (M j)) = Fin.cons (logH A) fun j => logH (L j)`.

Use function extensionality and compare the values at `j`. Apply the tactic sequence `cases j using Fin.cases <;> rfl`. Establish `hdeg : (fun j => (M j).a) = (Fin.cons A.a fun j => (L j).a : Fin (e + 1) → K → ℤ)`. Use function extensionality and compare the values at `j`. Apply the tactic sequence `cases j using Fin.cases <;> rfl`.

Rewrite using `[hlog, hdeg]`. Establish `ih' : ∀ (W : Ideal (MRing ι ℂ)) (L : Fin e → HLine ι), IsProjVar W e → (∀ j, IsSmoothMetric W (L j)) → zInt W e (fun j => logH (L j)) (fun _ => 1) = (intNum ℂ W (fun j => (L j).a) : ℝ)` using `ih`. Set `b : K → ℕ` to `fun k => (-(A.a k)).toNat`. Set `B : HLine ι` to `ReciprocityTheory.ChartRestriction.G.Geo.HermLine.sqMetric b`. Establish `hB : IsSmoothMetric P B` using `isSmoothMetric_of_isSmoothHerm P B (ReciprocityTheory.ChartRestriction.G.Geo.isSmoothHerm_sqMetric b)`.

Establish `hA : IsSmoothMetric P A` using `hM 0`. Set `c : K → ℕ` to `fun k => (A.a k + b k).toNat`. Establish `hc : ∀ k, (ReciprocityTheory.ChartRestriction.G.Geo.HermLine.tensor A B).a k = c k`. Introduce `k`. Use `show A.a k + (b k : ℤ) = ((A.a k + b k).toNat : ℤ)`.

Simplify using `only [b]`. Use linear arithmetic over natural numbers and integers. Establish `hC` using `degrees_step hPL1 hRes ih' hP L hL _ c hc (isSmoothMetric_tensor hA hB)`. Establish `hBs` using `degrees_step hPL1 hRes ih' hP L hL B b (fun k => rfl) hB`. Establish `hsum` using `ZIntAdd.proof K ι P e L A B hP (hRes K ι P (e + 1) hP) hL hA hB`.

Establish `hadd` using `IntNumAdd.full ℂ K ι P hP.1.multiHomog hP.1.relevant (e + 1) (relDim_of_isProjVar hP) (Fin.cons A.a fun j => (L j).a) 0 A.a (fun k => (b k : ℤ))`. Simplify using `only [Fin.update_cons_zero] at hadd`. Establish `hcs : (fun k => ((c k : ℕ) : ℤ)) = A.a + fun k => (b k : ℤ)`. Use function extensionality and compare the values at `k`. Simplify using `only [c, b, Pi.add_apply]`.

Use linear arithmetic over natural numbers and integers. Rewrite `hC` using `[hcs, hadd]`. Move the coercions through the operations in `at hC`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem degrees_of (hPL1 : PoincareLelongAlt.Statement) (hRes : ResExists.Statement) (hPt : ZIntPoint.Statement) (e : ℕ) :
    ∀ (P : Ideal (MRing ι ℂ)) (L : Fin e → HLine ι), IsProjVar P e → (∀ j, IsSmoothMetric P (L j)) →
      zInt P e (fun j => logH (L j)) (fun _ => 1) = (intNum ℂ P (fun j => (L j).a) : ℝ) := by
  induction e with
  | zero =>
    intro P L hP _
    rw [hPt K ι P _ hP (hRes K ι P 0 hP)]
    have hrel : GroundTheory.Heights₂.Heights.FieldNumbers.relDim P = 0 := by
      rw [relDim_of_isProjVar hP]
      rfl
    obtain ⟨hfd, hb⟩ := IntNumBase.full ℂ K ι P hP.1 hrel
    have := hP.1.isPrime
    have hbot : homFracDegZero P = ⊥ := IntermediateField.eq_bot_of_isAlgClosed_of_isAlgebraic _
    have h1 : Module.finrank ℂ (homFracDegZero P) = 1 := IntermediateField.finrank_eq_one_iff.mpr hbot
    have hL0 : (fun j => (L j).a) = (![] : Fin 0 → K → ℤ) := Subsingleton.elim _ _
    rw [hL0, hb, h1]
    norm_num
  | succ e ih =>
    intro P M hP hM
    set A := M 0
    set L : Fin e → HLine ι := fun j => M j.succ
    have hL : ∀ j, IsSmoothMetric P (L j) := fun j => hM j.succ
    have hlog : (fun j => logH (M j)) = Fin.cons (logH A) fun j => logH (L j) := by
      funext j
      cases j using Fin.cases <;> rfl
    have hdeg : (fun j => (M j).a) = (Fin.cons A.a fun j => (L j).a : Fin (e + 1) → K → ℤ) := by
      funext j
      cases j using Fin.cases <;> rfl
    rw [hlog, hdeg]
    have ih' : ∀ (W : Ideal (MRing ι ℂ)) (L : Fin e → HLine ι), IsProjVar W e →
        (∀ j, IsSmoothMetric W (L j)) →
        zInt W e (fun j => logH (L j)) (fun _ => 1) = (intNum ℂ W (fun j => (L j).a) : ℝ) := ih
    let b : K → ℕ := fun k => (-(A.a k)).toNat
    let B : HLine ι := ReciprocityTheory.ChartRestriction.G.Geo.HermLine.sqMetric b
    have hB : IsSmoothMetric P B :=
      isSmoothMetric_of_isSmoothHerm P B (ReciprocityTheory.ChartRestriction.G.Geo.isSmoothHerm_sqMetric b)
    have hA : IsSmoothMetric P A := hM 0
    let c : K → ℕ := fun k => (A.a k + b k).toNat
    have hc : ∀ k, (ReciprocityTheory.ChartRestriction.G.Geo.HermLine.tensor A B).a k = c k := by
      intro k
      show A.a k + (b k : ℤ) = ((A.a k + b k).toNat : ℤ)
      simp only [b]
      omega
    have hC := degrees_step hPL1 hRes ih' hP L hL _ c hc (isSmoothMetric_tensor hA hB)
    have hBs := degrees_step hPL1 hRes ih' hP L hL B b (fun k => rfl) hB
    have hsum := ZIntAdd.proof K ι P e L A B hP (hRes K ι P (e + 1) hP) hL hA hB
    have hadd := IntNumAdd.full ℂ K ι P hP.1.multiHomog hP.1.relevant (e + 1) (relDim_of_isProjVar hP)
      (Fin.cons A.a fun j => (L j).a) 0 A.a (fun k => (b k : ℤ))
    simp only [Fin.update_cons_zero] at hadd
    have hcs : (fun k => ((c k : ℕ) : ℤ)) = A.a + fun k => (b k : ℤ) := by
      funext k
      simp only [c, b, Pi.add_apply]
      omega
    rw [hcs, hadd] at hC
    push_cast at hC
    linarith

/- English proof (translation)
Introduce `K _ _ ι _ P e L hP _ hL`. Conclude with `degrees_of hPL1 hRes hPt e P L hP hL`.
-/
theorem Degrees.proof (hPL1 : PoincareLelongAlt.Statement) (hRes : ResExists.Statement) (hPt : ZIntPoint.Statement) :
    Degrees.Statement := by
  intro K _ _ ι _ P e L hP _ hL
  exact degrees_of hPL1 hRes hPt e P L hP hL

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
