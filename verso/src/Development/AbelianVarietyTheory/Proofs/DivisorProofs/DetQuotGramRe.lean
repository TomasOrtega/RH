import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieBaseIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieBaseAt
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GradedWeight

open Matrix GlobalTheory.HermFrame GlobalTheory.Twist
open scoped ComplexOrder

/- English proof (translation)
Use `set K := M.submatrix (finSumFinEquiv (m := n) (n := 1)) finSumFinEquiv with hK`. Establish `h₁ : K.toBlocks₁₁.det ≠ 0` using `(posDef_subGram hM).det_pos.ne'`. Use `invertibleOfIsUnitDet _ h₁.isUnit` as an intermediate fact. Establish `e : K.det = K.toBlocks₁₁.det * (quotGram K).det` using `by conv_lhs => rw [← fromBlocks_toBlocks K]`. Rewrite using `[det_fromBlocks₁₁, invOf_eq_nonsing_inv, quotGram]`.

Establish `e₁ : ReciprocityTheory.ChartRestriction.G.FD.lminor M (Fin.last n).succ = K.det` using `(det_submatrix_equiv_self _ M).symm`. Establish `e₂ : ReciprocityTheory.ChartRestriction.G.FD.lminor M (Fin.last n).castSucc = K.toBlocks₁₁.det` using `rfl`. Rewrite using `[GlobalTheory.GradedNorm.grSq, e₁, e₂, e, mul_div_cancel_left₀ _ h₁]`.
-/
theorem det_quotGram_re {n : ℕ} (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (hM : (M.submatrix finSumFinEquiv finSumFinEquiv).PosDef) :
    (quotGram (M.submatrix (finSumFinEquiv (m := n) (n := 1)) finSumFinEquiv)).det.re =
      GlobalTheory.GradedNorm.grSq M (Fin.last n) := by
  set K := M.submatrix (finSumFinEquiv (m := n) (n := 1)) finSumFinEquiv with hK
  have h₁ : K.toBlocks₁₁.det ≠ 0 := (posDef_subGram hM).det_pos.ne'
  have := invertibleOfIsUnitDet _ h₁.isUnit
  have e : K.det = K.toBlocks₁₁.det * (quotGram K).det := by
    conv_lhs => rw [← fromBlocks_toBlocks K]
    rw [det_fromBlocks₁₁, invOf_eq_nonsing_inv, quotGram]
  have e₁ : ReciprocityTheory.ChartRestriction.G.FD.lminor M (Fin.last n).succ = K.det :=
    (det_submatrix_equiv_self _ M).symm
  have e₂ : ReciprocityTheory.ChartRestriction.G.FD.lminor M (Fin.last n).castSucc = K.toBlocks₁₁.det := rfl
  rw [GlobalTheory.GradedNorm.grSq, e₁, e₂, e, mul_div_cancel_left₀ _ h₁]

/- English proof (translation)
Establish `hc : y ∈ ptsIn p σ c.U` using `mem_ptsIn.2 (hle (mem_ptsIn.1 hy))`. Use extensionality with `a b`. Rewrite using `[← h.form_frame _ hy, ← h.form_frame _ hc, he, he, h.form_resM _ _ _ hy]`.
-/
theorem G_eq_of_res {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {E : X.Modules} {r : ℕ}
    (h : Met p σ E r) (c c' : Chart E r) (hle : c'.U ≤ c.U) (he : ∀ a, c'.e a = resM E hle (c.e a))
    {y : CxPts p σ} (hy : y ∈ ptsIn p σ c'.U) : h.G c' y = h.G c y := by
  have hc : y ∈ ptsIn p σ c.U := mem_ptsIn.2 (hle (mem_ptsIn.1 hy))
  ext a b
  rw [← h.form_frame _ hy, ← h.form_frame _ hc, he, he, h.form_resM _ _ _ hy]

/- English proof (translation)
Proceed by induction on `j using Fin.induction with`. Consider the case `zero`. Establish `hz` using `VB.isVB_zero_iff.1 (fl.isVB 0)`. Use `⟨Fin.elim0, fun V hV => ⟨fun a b _ => funext fun i => i.elim0, fun t => ⟨0, ?_⟩⟩, fun a => a.elim0⟩` and prove the remaining obligations. Rewrite using `[map_zero]`.

Conclude with `(congr(($(hz.eq_of_src (𝟙 _) 0)).app V t)).symm`. Consider the case `succ i ih`. Take `⟨e, he, ee⟩` from `ih fun l hl => hs l (by simp at hl ⊢; omega)`. Establish `hf` using `(VBExt.isFrame_sumElim (VMetric.stepSeq_shortExact fl i) (t := fun _ : Fin 1 => s i) he (hs i (by simp))).comp_equiv (finSumFinEquiv (m := i) (n := 1)).symm`. Use `⟨_, hf, fun a => ?_⟩` and prove the remaining obligations.

Take `⟨b, rfl⟩` from `(finSumFinEquiv (m := i) (n := 1)).surjective a`. Rewrite using `[Function.comp_apply, Equiv.symm_apply_apply]`. Break down `b with b | b` into its components or cases. Use `Eq.trans ?_ (ee b)` and prove the remaining obligations. Rewrite using `[← fl.step_ι i]`.

Both sides reduce to the same expression. Take `rfl : b = 0` from `Subsingleton.elim _ _`. Both sides reduce to the same expression.
-/
theorem exists_frame {X : Scheme.{0}} {E : X.Modules} {m : ℕ} (fl : Vert.Flag E m) {W : X.Opens}
    (s : ∀ l : Fin m, Γ(fl.F l.succ, W)) (j : Fin (m + 1))
    (hs : ∀ l : Fin m, (l : ℕ) < j → IsFrame fun _ : Fin 1 => (fl.π l).app W (s l)) :
    ∃ e : Fin j → Γ(fl.F j, W), IsFrame e ∧ ∀ a : Fin j, (fl.ι j).app W (e a) =
      (fl.ι (Fin.castLE (Nat.le_of_lt_succ j.2) a).succ).app W (s (Fin.castLE (Nat.le_of_lt_succ j.2) a)) := by
  induction j using Fin.induction with
  | zero =>
    have hz := VB.isVB_zero_iff.1 (fl.isVB 0)
    refine ⟨Fin.elim0, fun V hV => ⟨fun a b _ => funext fun i => i.elim0, fun t => ⟨0, ?_⟩⟩, fun a => a.elim0⟩
    rw [map_zero]
    exact (congr(($(hz.eq_of_src (𝟙 _) 0)).app V t)).symm
  | succ i ih =>
    obtain ⟨e, he, ee⟩ := ih fun l hl => hs l (by simp at hl ⊢; omega)
    have hf := (VBExt.isFrame_sumElim (VMetric.stepSeq_shortExact fl i) (t := fun _ : Fin 1 => s i) he
      (hs i (by simp))).comp_equiv (finSumFinEquiv (m := i) (n := 1)).symm
    refine ⟨_, hf, fun a => ?_⟩
    obtain ⟨b, rfl⟩ := (finSumFinEquiv (m := i) (n := 1)).surjective a
    rw [Function.comp_apply, Equiv.symm_apply_apply]
    rcases b with b | b
    · refine Eq.trans ?_ (ee b)
      rw [← fl.step_ι i]
      rfl
    · obtain rfl : b = 0 := Subsingleton.elim _ _
      rfl

/- English proof (translation)
Introduce `k _ X p E m h H fl i σ y W hy cs hW s hs`. Establish `hf (l : Fin m) (hl : l ≤ i) : IsFrame fun _ : Fin 1 => (fl.π l).app W (s l)`. Use `(cs l).isFrame.res (hW l hl)` as an intermediate fact. Use `this using 2 with a` and compare the differences between its conclusion and the goal. Rewrite using `[Subsingleton.elim a 0]`.

Conclude with `hs l hl`. Take `⟨e, he, ee⟩` from `exists_frame fl s i.castSucc fun l hl => hf l (le_of_lt hl)`. Set `a : VBExt.AdaptedChart (VMetric.stepSeq fl i) i 1` to `⟨W, e, fun _ => s i, he, hf i le_rfl⟩`. Establish `e₁` using `Met.quot_G ((h.stepMet fl i).met σ) (VMetric.stepSeq_shortExact fl i) (fl.isVB i.castSucc) (fl.isVB_gr i) a hy`. Establish `e₂` using `G_eq_of_res ((h.grMet fl i).met σ) (cs i) a.quot (hW i le_rfl) (fun b => by`.

Rewrite using `[Subsingleton.elim b 0]`. Conclude with `hs i le_rfl) hy`. Establish `hp` using `Met.posDef_gram_frame ((h.stepMet fl i).met σ) (VMetric.stepSeq_shortExact fl i) a hy`. Establish `key (b : Fin i ⊕ Fin 1) : (fl.ι i.succ).app W (a.frame b) = (fl.ι (Fin.castLE i.isLt (finSumFinEquiv b)).succ).app W (s (Fin.castLE i.isLt (finSumFinEquiv b)))`. Break down `b with b | b` into its components or cases.

Use `Eq.trans ?_ (ee b)` and prove the remaining obligations. Rewrite using `[← fl.step_ι i]`. Both sides reduce to the same expression. Take `rfl : b = 0` from `Subsingleton.elim _ _`. Both sides reduce to the same expression.

Establish `e₃ : ((h.stepMet fl i).met σ).gram a.frame y = ((h.met σ).gram (fun l : Fin (i + 1) => (fl.ι (Fin.castLE i.isLt l).succ).app W (s (Fin.castLE i.isLt l))) y).submatrix finSumFinEquiv finSumFinEquiv`. Use extensionality with `b c`. Use `(Met.form_restrict _ (fl.isSubbundle i.succ) (fl.isVB i.succ) _ _ hy).trans ?_` and prove the remaining obligations. Conclude with `congrArg₂ (fun u v => (h.met σ).form u v y) (key b) (key c)`. Rewrite `hp`, `e₁` using `[e₃]`.

Rewrite using `[← det_quotGram_re _ hp, ← e₁]`. Express the relevant statement in the definitionally equal form `Real.exp (- -Real.log (((h.grMet fl i).met σ).G (cs i) y).det.re) = _`. Rewrite using `[neg_neg, ← e₂]`. Conclude with `Real.exp_log (det_re_pos (((h.grMet fl i).met σ).posDef _ y hy))`.
-/
theorem exp_neg_grLB_φ : ∀ {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {E : X.Modules} {m : ℕ} (h : VMetric p E m)
    (H : h.IsCInf) (fl : Vert.Flag E m) (i : Fin m) (σ : k →+* ℂ) (y : CxPts p σ) (W : X.Opens),
    y ∈ ptsIn p σ W → ∀ (cs : ∀ l : Fin m, (fl.root l).ι) (hW : ∀ l : Fin m, l ≤ i → W ≤ (cs l).U)
    (s : ∀ l : Fin m, Γ(fl.F l.succ, W)),
    (∀ (l : Fin m) (hl : l ≤ i), (fl.π l).app W (s l) = Twist.resM _ (hW l hl) ((cs l).e 0)) →
    Real.exp (-((VMetric.grLB fl i H).φ σ).φ (cs i) y) =
      GlobalTheory.GradedNorm.grSq ((h.met σ).gram (fun l : Fin (i + 1) => (fl.ι (Fin.castLE i.isLt l).succ).app W
        (s (Fin.castLE i.isLt l))) y) (Fin.last i) := by
  intro k _ X p E m h H fl i σ y W hy cs hW s hs
  have hf (l : Fin m) (hl : l ≤ i) : IsFrame fun _ : Fin 1 => (fl.π l).app W (s l) := by
    have := (cs l).isFrame.res (hW l hl)
    convert this using 2 with a
    rw [Subsingleton.elim a 0]
    exact hs l hl
  obtain ⟨e, he, ee⟩ := exists_frame fl s i.castSucc fun l hl => hf l (le_of_lt hl)
  let a : VBExt.AdaptedChart (VMetric.stepSeq fl i) i 1 := ⟨W, e, fun _ => s i, he, hf i le_rfl⟩
  have e₁ := Met.quot_G ((h.stepMet fl i).met σ) (VMetric.stepSeq_shortExact fl i)
    (fl.isVB i.castSucc) (fl.isVB_gr i) a hy
  have e₂ := G_eq_of_res ((h.grMet fl i).met σ) (cs i) a.quot (hW i le_rfl) (fun b => by
    rw [Subsingleton.elim b 0]; exact hs i le_rfl) hy
  have hp := Met.posDef_gram_frame ((h.stepMet fl i).met σ) (VMetric.stepSeq_shortExact fl i) a hy
  have key (b : Fin i ⊕ Fin 1) : (fl.ι i.succ).app W (a.frame b) =
      (fl.ι (Fin.castLE i.isLt (finSumFinEquiv b)).succ).app W (s (Fin.castLE i.isLt (finSumFinEquiv b))) := by
    rcases b with b | b
    · refine Eq.trans ?_ (ee b)
      rw [← fl.step_ι i]
      rfl
    · obtain rfl : b = 0 := Subsingleton.elim _ _
      rfl
  have e₃ : ((h.stepMet fl i).met σ).gram a.frame y = ((h.met σ).gram (fun l : Fin (i + 1) =>
      (fl.ι (Fin.castLE i.isLt l).succ).app W (s (Fin.castLE i.isLt l))) y).submatrix
        finSumFinEquiv finSumFinEquiv := by
    ext b c
    refine (Met.form_restrict _ (fl.isSubbundle i.succ) (fl.isVB i.succ) _ _ hy).trans ?_
    exact congrArg₂ (fun u v => (h.met σ).form u v y) (key b) (key c)
  rw [e₃] at hp e₁
  rw [← det_quotGram_re _ hp, ← e₁]
  change Real.exp (- -Real.log (((h.grMet fl i).met σ).G (cs i) y).det.re) = _
  rw [neg_neg, ← e₂]
  exact Real.exp_log (det_re_pos (((h.grMet fl i).met σ).posDef _ y hy))

end GlobalTheory.GradedWeight
