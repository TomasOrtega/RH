import Mathlib
import Formalism.SharpRestriction.ParConsts
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalDegreeUpperC
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ScaleFamilySizeRelationsEventually
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.BTLeFiveQuarters
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow

noncomputable section

namespace GlobalTheory.LowRow

/- English proof (translation)
Introduce `eps Fm`. Take `⟨x0, h0⟩` from `GlobalTheory.ShNums.size_rel Fm`. Use `⟨x0, fun x hx1 hx i j => ?_⟩` and prove the remaining obligations. Take `⟨-, -, -, heta, hw, h4, h2b, -, hw1, hsum⟩` from `h0 x hx hx1 i`. Establish `SZ` using `Fm.sizes x hx1 i`.

Establish `P` using `Fm.params x hx1 i`. Generalize the expression as in `Fm.L x i = L at *`. Generalize the expression as in `Fm.D x i = D at *`. Take `⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hG, -, -⟩` from `SZ`. Establish `hxp : 0 < L.sc.x` using `by linarith`.

Establish `hb : 0 < L.sc.b` using `Real.exp_pos _`. Establish `hb' : 0 < L.sc.b'` using `div_pos (mul_pos hxp hb) (Real.exp_pos _)`. Establish `he` using `L.etaSz_pos`. Establish `hSc` using `L.Sc_pos`. Establish `hq : L.sc.b' / L.sc.x ≤ L.sc.b'` using `div_le_self hb'.le (by linarith)`.

Establish `hq0 : 0 < L.sc.b' / L.sc.x` using `div_pos hb' hxp`. Establish `hwj : ∀ τ, wj D (j.1 + 1) τ = (((D.hc τ).e j : ℚ) : ℝ)`. Introduce `τ`. Unfold `wj`. Rewrite using `[dif_pos (by omega)]`.

Both sides reduce to the same expression. Establish `hwin : ∀ τ, 0 < wj D (j.1 + 1) τ ∧ wj D (j.1 + 1) τ ≤ 2 * L.sc.b`. Introduce `τ`. Distinguish the cases in `h1 : (D.eTau τ : D.R.GG) ∈ D.host.thickPlaces`. Use `L.win_thick (j.1 + 1) (by omega) (by omega) τ h1` as an intermediate fact.

Apply the tactic sequence `constructor <;> linarith [this.1, this.2]`. Distinguish the cases in `h2 : (D.eTau τ : D.R.GG) ∈ D.host.topPlaces`. Take `⟨t, ht, e⟩` from `Finset.mem_image.mp h2`. Establish `a` using `L.win_top (j.1 + 1) (by omega) (by omega) τ ⟨t, ht⟩ e.symm`. Establish `a3` using `L.bT_ge ⟨t, ht⟩`.

Establish `a4` using `GlobalTheory.Ggeo.bT_le_five_quarters P ⟨t, ht⟩`. Apply the tactic sequence `constructor <;> linarith [a.1, a.2]`. Establish `a` using `L.win_thin (j.1 + 1) (by omega) (by omega) τ ⟨(D.eTau τ).2, h2, h1⟩`. Apply the tactic sequence `constructor <;> linarith [a.1, a.2]`. Use `⟨fun τ => ⟨?_, ?_, fun l => ?_, fun l => ?_⟩, fun l => (hG l l).1⟩` and prove the remaining obligations.

Rewrite using `[← hwj]`. Conclude with `(hwin τ).1`. Rewrite using `[← hwj]`. Conclude with `(hwin τ).2`. Use `L.cloud_v τ l` as an intermediate fact.

Conclude with `⟨this.1, by linarith [this.2]⟩`. Use `L.be_close τ l j` as an intermediate fact. Move the coercions through the operations in `at this`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem weightSizes_along : ∀ (eps : ℝ) (Fm : FamP eps), ∃ x0 : ℝ, ∀ x, Fm.x1 < x → x0 ≤ x →
    ∀ (i : Fm.Ix x) j, Sizes (Fm.D x i) j (Fm.L x i).sc.b := by
  intro eps Fm
  obtain ⟨x0, h0⟩ := GlobalTheory.ShNums.size_rel Fm
  refine ⟨x0, fun x hx1 hx i j => ?_⟩
  obtain ⟨-, -, -, heta, hw, h4, h2b, -, hw1, hsum⟩ := h0 x hx hx1 i
  have SZ := Fm.sizes x hx1 i
  have P := Fm.params x hx1 i
  generalize Fm.L x i = L at *
  generalize Fm.D x i = D at *
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hG, -, -⟩ := SZ
  have hxp : 0 < L.sc.x := by linarith
  have hb : 0 < L.sc.b := Real.exp_pos _
  have hb' : 0 < L.sc.b' := div_pos (mul_pos hxp hb) (Real.exp_pos _)
  have he := L.etaSz_pos
  have hSc := L.Sc_pos
  have hq : L.sc.b' / L.sc.x ≤ L.sc.b' := div_le_self hb'.le (by linarith)
  have hq0 : 0 < L.sc.b' / L.sc.x := div_pos hb' hxp
  have hwj : ∀ τ, wj D (j.1 + 1) τ = (((D.hc τ).e j : ℚ) : ℝ) := by
    intro τ
    unfold wj
    rw [dif_pos (by omega)]
    rfl
  have hwin : ∀ τ, 0 < wj D (j.1 + 1) τ ∧ wj D (j.1 + 1) τ ≤ 2 * L.sc.b := by
    intro τ
    by_cases h1 : (D.eTau τ : D.R.GG) ∈ D.host.thickPlaces
    · have := L.win_thick (j.1 + 1) (by omega) (by omega) τ h1
      constructor <;> linarith [this.1, this.2]
    by_cases h2 : (D.eTau τ : D.R.GG) ∈ D.host.topPlaces
    · obtain ⟨t, ht, e⟩ := Finset.mem_image.mp h2
      have a := L.win_top (j.1 + 1) (by omega) (by omega) τ ⟨t, ht⟩ e.symm
      have a3 := L.bT_ge ⟨t, ht⟩
      have a4 := GlobalTheory.Ggeo.bT_le_five_quarters P ⟨t, ht⟩
      constructor <;> linarith [a.1, a.2]
    · have a := L.win_thin (j.1 + 1) (by omega) (by omega) τ ⟨(D.eTau τ).2, h2, h1⟩
      constructor <;> linarith [a.1, a.2]
  refine ⟨fun τ => ⟨?_, ?_, fun l => ?_, fun l => ?_⟩, fun l => (hG l l).1⟩
  · rw [← hwj]; exact (hwin τ).1
  · rw [← hwj]; exact (hwin τ).2
  · have := L.cloud_v τ l
    exact ⟨this.1, by linarith [this.2]⟩
  · have := L.be_close τ l j
    push_cast at this
    linarith

end GlobalTheory.LowRow
