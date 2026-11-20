import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CuspidalExponentialDecay
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.SiegelSpaceAlgebraHolds
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.IndCount
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfH
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.LeadMCoeffEqZero

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.ManyForms

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => simpa using hP`. Consider the case `succ m ih`. Rewrite using `[pow_succ, ← mul_assoc, succ_nsmul, ← add_assoc]`. Conclude with `(siegelSpaceAlgebra_holds r X _ L c).2.2.2 _ ih Q hQ`.
-/
theorem mul_pow_mem_SSgt {r : ℕ} (X : Data E r) {G L : Wt X.Ψ r} {c : ℝ}
    {P Q : Frame X.Ψ r → ℂ} (hP : P ∈ X.SSgt G c) (hQ : X.IsBddSec L Q) (m : ℕ) :
    P * Q ^ m ∈ X.SSgt (G + m • L) c := by
  induction m with
  | zero => simpa using hP
  | succ m ih =>
    rw [pow_succ, ← mul_assoc, succ_nsmul, ← add_assoc]
    exact (siegelSpaceAlgebra_holds r X _ L c).2.2.2 _ ih Q hQ

/- English proof (translation)
Proceed by induction on `S using Finset.induction_on with`. Consider the case `empty => simpa using hP`. Consider the case `insert a S ha ih`. Rewrite using `[Finset.prod_insert ha, Finset.sum_insert ha, mul_comm (s a ^ α a), ← mul_assoc, add_comm (α a), add_nsmul, ← add_assoc]`. Conclude with `mul_pow_mem_SSgt X ih (hs a) _`.
-/
theorem mul_prod_mem_SSgt {r : ℕ} (X : Data E r) {G L : Wt X.Ψ r} {c : ℝ} {ι : Type}
    {P : Frame X.Ψ r → ℂ} {s : ι → Frame X.Ψ r → ℂ} (hP : P ∈ X.SSgt G c)
    (hs : ∀ k, X.IsBddSec L (s k)) (α : ι → ℕ) (S : Finset ι) :
    P * ∏ k ∈ S, s k ^ α k ∈ X.SSgt (G + (∑ k ∈ S, α k) • L) c := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using hP
  | insert a S ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, mul_comm (s a ^ α a), ← mul_assoc,
      add_comm (α a), add_nsmul, ← add_assoc]
    exact mul_pow_mem_SSgt X ih (hs a) _

/- English proof (translation)
Establish `h : multiLt n (T + 1) = Y.multiLe n T`. Use extensionality with `α`. Rewrite using `[GlobalTheory.LeadIndep.mem_multiLt, Y.mem_multiLe_iff, Nat.lt_succ_iff]`. Rewrite using `[h, Y.ind_count]`.
-/
theorem card_multiLt_succ (n T : ℕ) : (multiLt n (T + 1)).card = (T + n).choose n := by
  have h : multiLt n (T + 1) = Y.multiLe n T := by
    ext α
    rw [GlobalTheory.LeadIndep.mem_multiLt, Y.mem_multiLe_iff, Nat.lt_succ_iff]
  rw [h, Y.ind_count]

/- English proof (translation)
Introduce `r X Xa Fl G T c _ hint`. Use `choose F hF hFv using fun j : Fin Fl.δ => hint (Pi.single j 1)`. Use `set M := multiLt (nd X) (T + 1) with hM`. Use `set S : Finset (Fin Fl.δ) := Finset.univ with hS`. Establish `hcard : (S ×ˢ M).card = Fl.δ * (T + nd X).choose (nd X)`.

Rewrite using `[Finset.card_product, hM, card_multiLt_succ, hS, Finset.card_univ, Fintype.card_fin]`. Set `e` to `(Finset.equivFinOfCardEq hcard).symm`. Set `fP : Fin Fl.δ → (Fin (nd X) → ℕ) → Frame X.Ψ r → ℂ` to `fun j α => F j * (∏ k, Fl.s k ^ α k) * Fl.w0 ^ (T - ∑ q, α q)`. Use `⟨fun q => fP (e q).1.1 (e q).1.2, fun q => ?_, fun a ha => ?_⟩` and prove the remaining obligations. Establish `hα : ∑ q', (e q).1.2 q' ≤ T` using `Nat.lt_succ_iff.mp (GlobalTheory.LeadIndep.mem_multiLt.mp (Finset.mem_product.mp (e q).2).2)`.

Establish `h` using `mul_pow_mem_SSgt X (mul_prod_mem_SSgt X (hF (e q).1.1) (fun k => (Fl.s_van k).1.1) (e q).1.2 Finset.univ) Fl.weightForm_vanishes.1.1 (T - ∑ q', (e q).1.2 q')`. Rewrite `h` using `[add_assoc, ← add_nsmul, Nat.add_sub_cancel' hα]`. Then use the resulting hypothesis. Set `cc : (Fin (nd X) → ℕ) → Fin Fl.δ → ℂ` to `fun α j => if h : (j, α) ∈ S ×ˢ M then a (e.symm ⟨(j, α), h⟩) else 0`. Establish `hc : ∀ q, cc (e q).1.2 (e q).1.1 = a q`. Introduce `q`.

Establish `h : ((e q).1.1, (e q).1.2) ∈ S ×ˢ M` using `(e q).2`. Simplify using `only [cc, dif_pos h]`. Conclude with `congrArg a (e.symm_apply_apply q)`. Establish `hcomb : ∀ x, leadM X Fl.s Fl.w0 F T (T + 1) cc x = ∑ q, a q * fP (e q).1.1 (e q).1.2 x`. Introduce `x`.

Establish `h1 : leadM X Fl.s Fl.w0 F T (T + 1) cc x = ∑ p ∈ S ×ˢ M, cc p.2 p.1 * fP p.1 p.2 x`. Rewrite using `[Finset.sum_product_right]`. Use `Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Simplify using `only [fP, monoM, Pi.mul_apply, Pi.pow_apply, Finset.prod_apply]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[h1, ← Finset.sum_coe_sort (S ×ˢ M), ← e.sum_comp]`. Use `Finset.sum_congr rfl fun q _ => ?_` and prove the remaining obligations. Rewrite using `[hc q]`. Establish `hind` using `GlobalTheory.LeadIndep.leadM_coeff_eq_zero r X Xa Fl G T (T + 1) Fl.δ F (fun k => (hF k).1.1.1) (fun u hu => by`. Use function extensionality and compare the values at `j`.

Use `hu j` as an intermediate fact. Simplify `this) cc` using `[hFv, Pi.single_apply]`. Use the proof step `(fun j => by`. Establish `h0 : (0 : V (nd X)) ∈ OmF X (Fl.xs j)` using `by show cpt X (Fl.xs j) 0 ∈ X.dom`. Rewrite using `[IW.cpt_zero]`.

Conclude with `Fl.xs_mem j`. Use `Asymptotics.IsBigO.of_bound 0 ?_` and prove the remaining obligations. Use `filter_upwards [(OntoB.isOpen_OmF X (Fl.xs j)).mem_nhds h0] with z hz`. Rewrite using `[zero_mul, norm_le_zero_iff, hcomb]`. Conclude with `ha _ hz)`.

Use function extensionality and compare the values at `q`. Rewrite using `[← hc q]`. Conclude with `hind _ (Finset.mem_product.mp (e q).2).2 _`.
-/
theorem exists_indep_forms : ∀ (r : ℕ) (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa) (G : Wt X.Ψ r) (T : ℕ) (c : ℝ), 0 ≤ c →
    (∀ v : Fin Fl.δ → ℂ, ∃ F ∈ X.SSgt G c, ∀ j, F (Fl.xs j) = v j) →
    ∃ f : Fin (Fl.δ * (T + nd X).choose (nd X)) → Frame X.Ψ r → ℂ,
      (∀ q, f q ∈ X.SSgt (G + T • Xa.L) c) ∧
      ∀ u : Fin (Fl.δ * (T + nd X).choose (nd X)) → ℂ, (∀ x ∈ X.dom, ∑ q, u q * f q x = 0) → u = 0 := by
  classical
  intro r X Xa Fl G T c _ hint
  choose F hF hFv using fun j : Fin Fl.δ => hint (Pi.single j 1)
  set M := multiLt (nd X) (T + 1) with hM
  set S : Finset (Fin Fl.δ) := Finset.univ with hS
  have hcard : (S ×ˢ M).card = Fl.δ * (T + nd X).choose (nd X) := by
    rw [Finset.card_product, hM, card_multiLt_succ, hS, Finset.card_univ, Fintype.card_fin]
  let e := (Finset.equivFinOfCardEq hcard).symm
  let fP : Fin Fl.δ → (Fin (nd X) → ℕ) → Frame X.Ψ r → ℂ :=
    fun j α => F j * (∏ k, Fl.s k ^ α k) * Fl.w0 ^ (T - ∑ q, α q)
  refine ⟨fun q => fP (e q).1.1 (e q).1.2, fun q => ?_, fun a ha => ?_⟩
  · have hα : ∑ q', (e q).1.2 q' ≤ T :=
      Nat.lt_succ_iff.mp (GlobalTheory.LeadIndep.mem_multiLt.mp (Finset.mem_product.mp (e q).2).2)
    have h := mul_pow_mem_SSgt X
      (mul_prod_mem_SSgt X (hF (e q).1.1) (fun k => (Fl.s_van k).1.1) (e q).1.2 Finset.univ)
      Fl.weightForm_vanishes.1.1 (T - ∑ q', (e q).1.2 q')
    rwa [add_assoc, ← add_nsmul, Nat.add_sub_cancel' hα] at h
  · let cc : (Fin (nd X) → ℕ) → Fin Fl.δ → ℂ := fun α j =>
      if h : (j, α) ∈ S ×ˢ M then a (e.symm ⟨(j, α), h⟩) else 0
    have hc : ∀ q, cc (e q).1.2 (e q).1.1 = a q := by
      intro q
      have h : ((e q).1.1, (e q).1.2) ∈ S ×ˢ M := (e q).2
      simp only [cc, dif_pos h]
      exact congrArg a (e.symm_apply_apply q)
    have hcomb : ∀ x, leadM X Fl.s Fl.w0 F T (T + 1) cc x =
        ∑ q, a q * fP (e q).1.1 (e q).1.2 x := by
      intro x
      have h1 : leadM X Fl.s Fl.w0 F T (T + 1) cc x =
          ∑ p ∈ S ×ˢ M, cc p.2 p.1 * fP p.1 p.2 x := by
        rw [Finset.sum_product_right]
        refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun j _ => ?_
        simp only [fP, monoM, Pi.mul_apply, Pi.pow_apply, Finset.prod_apply]
        ring
      rw [h1, ← Finset.sum_coe_sort (S ×ˢ M), ← e.sum_comp]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [hc q]
    have hind := GlobalTheory.LeadIndep.leadM_coeff_eq_zero r X Xa Fl G T (T + 1) Fl.δ F
      (fun k => (hF k).1.1.1)
      (fun u hu => by
        funext j
        have := hu j
        simpa [hFv, Pi.single_apply] using this) cc
      (fun j => by
        have h0 : (0 : V (nd X)) ∈ OmF X (Fl.xs j) := by
          show cpt X (Fl.xs j) 0 ∈ X.dom
          rw [IW.cpt_zero]
          exact Fl.xs_mem j
        refine Asymptotics.IsBigO.of_bound 0 ?_
        filter_upwards [(OntoB.isOpen_OmF X (Fl.xs j)).mem_nhds h0] with z hz
        rw [zero_mul, norm_le_zero_iff, hcomb]
        exact ha _ hz)
    funext q
    rw [← hc q]
    exact hind _ (Finset.mem_product.mp (e q).2).2 _

end GlobalTheory.ManyForms
