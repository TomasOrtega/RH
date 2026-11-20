import Formalism.LocalToGlobal.CharacterGerms.ConstantCoeffSinglePointZero

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj

namespace VP

section Inv

variable {C : Type} [Field C] {V : VF C} {σ : Type}

/- English proof (translation)
Simplify using `[VF.Ge, AddValuation.map_inv, hc]`.
-/
theorem inv_int {c : C} (hc : V.v c = 0) : V.Ge 0 c⁻¹ := by
  simp [VF.Ge, AddValuation.map_inv, hc]

/- English proof (translation)
Establish `hc0 : MvPowerSeries.constantCoeff U ≠ 0`. Introduce `h`. Simplify using `[h] at h0`. Use `⟨U⁻¹, ?_, MvPowerSeries.inv_mul_cancel _ hc0⟩` and prove the remaining obligations. Establish `hge0 : V.Ge 0 (0 : C)` using `by simp [VF.Ge]`.

Establish `hmul : ∀ a b : C, V.Ge 0 a → V.Ge 0 b → V.Ge 0 (a * b)`. Introduce `a b ha hb`. Unfold `VF.Ge at *`. Rewrite using `[AddValuation.map_mul]`. Simplify using `using add_le_add ha hb`.

Establish `hadd : ∀ a b : C, V.Ge 0 a → V.Ge 0 b → V.Ge 0 (a + b)` using `fun a b ha hb => le_trans (le_min ha hb) (V.v.map_add a b)`. Establish `hneg : ∀ a : C, V.Ge 0 a → V.Ge 0 (-a)`. Introduce `a ha`. Unfold `VF.Ge at *`. Rewrite using `[AddValuation.map_neg]` and apply the resulting hypothesis.

Introduce `μ`. Proceed by induction on `μ using WellFoundedLT.induction with`. Consider the case `_ μ ih`. Rewrite using `[MvPowerSeries.coeff_inv]`. Use `split_ifs with hμ`.

Conclude with `inv_int h0`. Use `hmul _ _ (hneg _ (inv_int h0)) ?_` and prove the remaining obligations. Use `Finset.sum_induction _ (V.Ge 0) hadd hge0 (fun x _ => ?_)` and prove the remaining obligations. Use `split_ifs with hlt`. Conclude with `hmul _ _ (hU x.1) (ih x.2 hlt)`.

Conclude with `hge0`.
-/
theorem intInv {U : MvPowerSeries σ C} (hU : IntS V U) (h0 : V.v (MvPowerSeries.constantCoeff U) = 0) :
    ∃ U' : MvPowerSeries σ C, IntS V U' ∧ U' * U = 1 := by
  have hc0 : MvPowerSeries.constantCoeff U ≠ 0 := by
    intro h
    simp [h] at h0
  refine ⟨U⁻¹, ?_, MvPowerSeries.inv_mul_cancel _ hc0⟩
  have hge0 : V.Ge 0 (0 : C) := by simp [VF.Ge]
  have hmul : ∀ a b : C, V.Ge 0 a → V.Ge 0 b → V.Ge 0 (a * b) := by
    intro a b ha hb
    unfold VF.Ge at *
    rw [AddValuation.map_mul]
    simpa using add_le_add ha hb
  have hadd : ∀ a b : C, V.Ge 0 a → V.Ge 0 b → V.Ge 0 (a + b) :=
    fun a b ha hb => le_trans (le_min ha hb) (V.v.map_add a b)
  have hneg : ∀ a : C, V.Ge 0 a → V.Ge 0 (-a) := by
    intro a ha
    unfold VF.Ge at *
    rwa [AddValuation.map_neg]
  intro μ
  induction μ using WellFoundedLT.induction with
  | _ μ ih =>
    rw [MvPowerSeries.coeff_inv]
    split_ifs with hμ
    · exact inv_int h0
    · refine hmul _ _ (hneg _ (inv_int h0)) ?_
      refine Finset.sum_induction _ (V.Ge 0) hadd hge0 (fun x _ => ?_)
      split_ifs with hlt
      · exact hmul _ _ (hU x.1) (ih x.2 hlt)
      · exact hge0

/- English proof (translation)
Establish `hge : ∀ c : C, (c = 0 ∨ c = 1) → V.Ge 0 c`. Introduce and unpack `c (rfl | rfl)`. Simplify using `[VF.Ge]`. Simplify using `[VF.Ge]`. Establish `hone : IntS V (1 : MvPowerSeries σ C)`.

Introduce `μ`. Rewrite using `[MvPowerSeries.coeff_one]`. Use `split_ifs`. Conclude with `hge 1 (Or.inr rfl)`. Conclude with `hge 0 (Or.inl rfl)`.

Establish `hmul : ∀ F G : MvPowerSeries σ C, IntS V F → IntS V G → IntS V (F * G)`. Introduce `F G hF hG μ`. Rewrite using `[MvPowerSeries.coeff_mul]`. Use `Finset.sum_induction _ (V.Ge 0) (fun a b ha hb => ?_) (hge 0 (Or.inl rfl)) (fun q _ => ?_)` and prove the remaining obligations. Conclude with `le_trans (le_min ha hb) (V.v.map_add a b)`.

Establish `h1` using `add_le_add (hF q.1) (hG q.2)`. Unfold `VF.Ge`. Rewrite using `[AddValuation.map_mul]`. Simplify using `using h1`. Proceed by induction on `s using Finset.induction_on with`.

Consider the case `empty => simpa using hone`. Consider the case `insert a s ha ih`. Rewrite using `[Finset.prod_insert ha]`. Conclude with `hmul _ _ (h a (Finset.mem_insert_self _ _)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))`.
-/
theorem IntS_prod {ι : Type} (s : Finset ι) {F : ι → MvPowerSeries σ C} (h : ∀ i ∈ s, IntS V (F i)) :
    IntS V (∏ i ∈ s, F i) := by
  classical
  have hge : ∀ c : C, (c = 0 ∨ c = 1) → V.Ge 0 c := by
    rintro c (rfl | rfl)
    · simp [VF.Ge]
    · simp [VF.Ge]
  have hone : IntS V (1 : MvPowerSeries σ C) := by
    intro μ
    rw [MvPowerSeries.coeff_one]
    split_ifs
    · exact hge 1 (Or.inr rfl)
    · exact hge 0 (Or.inl rfl)
  have hmul : ∀ F G : MvPowerSeries σ C, IntS V F → IntS V G → IntS V (F * G) := by
    intro F G hF hG μ
    rw [MvPowerSeries.coeff_mul]
    refine Finset.sum_induction _ (V.Ge 0) (fun a b ha hb => ?_) (hge 0 (Or.inl rfl)) (fun q _ => ?_)
    · exact le_trans (le_min ha hb) (V.v.map_add a b)
    · have h1 := add_le_add (hF q.1) (hG q.2)
      unfold VF.Ge
      rw [AddValuation.map_mul]
      simpa using h1
  induction s using Finset.induction_on with
  | empty => simpa using hone
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact hmul _ _ (h a (Finset.mem_insert_self _ _)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/- English proof (translation)
Introduce `μ`. Rewrite using `[MvPowerSeries.coeff_X]`. Use `split_ifs`. Simplify using `[VF.Ge]`. Simplify using `[VF.Ge]`.
-/
theorem IntS_X (s : σ) : IntS V (MvPowerSeries.X s : MvPowerSeries σ C) := by
  intro μ
  rw [MvPowerSeries.coeff_X]
  split_ifs
  · simp [VF.Ge]
  · simp [VF.Ge]

end Inv

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}

/- English proof (translation)
Establish `hs : MvPowerSeries.HasSubst (fun p : Fin m × Fin dd => a p.1 p.2)` using `MvPowerSeries.hasSubst_of_constantCoeff_zero (fun p => ha p.1 p.2)`. Unfold `ev`. Rewrite using `[MvPowerSeries.constantCoeff_subst hs, finsum_eq_single _ 0]`. Simplify using the standard rewrite rules. Introduce `d hd`.

Choose the witnesses or unpack the hypotheses as in `⟨s, hs'⟩ : ∃ s, d s ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `hd (Finsupp.ext h)`. Establish `h0 : MvPowerSeries.constantCoeff (d.prod fun s e => (a s.1 s.2) ^ e) = 0`.

Rewrite using `[Finsupp.prod, map_prod]`. Conclude with `Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hs') (by rw [map_pow, ha, zero_pow hs'])`. Rewrite using `[h0, smul_zero]`.
-/
private theorem cc_ev_lemma {m n : ℕ} (a : Fin m → Pt C n dd)
    (ha : ∀ j i, MvPowerSeries.constantCoeff (a j i) = 0) (f : PS C m dd) :
    MvPowerSeries.constantCoeff (ev a f) = MvPowerSeries.constantCoeff f := by
  have hs : MvPowerSeries.HasSubst (fun p : Fin m × Fin dd => a p.1 p.2) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun p => ha p.1 p.2)
  unfold ev
  rw [MvPowerSeries.constantCoeff_subst hs, finsum_eq_single _ 0]
  · simp
  · intro d hd
    obtain ⟨s, hs'⟩ : ∃ s, d s ≠ 0 := by
      by_contra h
      push_neg at h
      exact hd (Finsupp.ext h)
    have h0 : MvPowerSeries.constantCoeff (d.prod fun s e => (a s.1 s.2) ^ e) = 0 := by
      rw [Finsupp.prod, map_prod]
      exact Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hs') (by rw [map_pow, ha, zero_pow hs'])
    rw [h0, smul_zero]

/- English proof (translation)
Establish `hax` using `Y.gauge.ax0`. Apply the tactic sequence `have e : MvPowerSeries.constantCoeff (ev (n := 1) ![0, pt C dd 0] Y.h) = MvPowerSeries.constantCoeff Y.h := cc_ev_lemma _ (fun j i => by fin_cases j <;> simp [pt]) _`. Rewrite using `[← e, hax, map_zero]`.
-/
theorem cc_h (Y : FBChart C V O dd) : MvPowerSeries.constantCoeff Y.h = 0 := by
  have hax := Y.gauge.ax0
  have e : MvPowerSeries.constantCoeff (ev (n := 1) ![0, pt C dd 0] Y.h) = MvPowerSeries.constantCoeff Y.h :=
    cc_ev_lemma _ (fun j i => by fin_cases j <;> simp [pt]) _
  rw [← e, hax, map_zero]

/- English proof (translation)
Unfold `ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.FB.hL`. Rewrite using `[cc_ev_lemma _ ?_ _]`. Conclude with `cc_h Y`. Introduce `j i fin_cases j`. Simplify using `[pt]`.

Use `show MvPowerSeries.constantCoeff (comp1 (Y.B.actK C Y.w0) (pt C dd 0) i) = 0`. Simplify using `only [comp1]`. Rewrite using `[cc_ev_lemma _ (fun j i => by rw [Fin.fin_one_eq_zero j]; simp [pt]) _]`. Simplify using `[ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.FB.actK, MvPowerSeries.constantCoeff_map, Y.B.A.const]`.
-/
theorem cc_hL (Y : FBChart C V O dd) : MvPowerSeries.constantCoeff (Y.B.hL C Y.h Y.w0) = 0 := by
  unfold ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.FB.hL
  rw [cc_ev_lemma _ ?_ _]
  · exact cc_h Y
  · intro j i
    fin_cases j
    · simp [pt]
    · show MvPowerSeries.constantCoeff (comp1 (Y.B.actK C Y.w0) (pt C dd 0) i) = 0
      simp only [comp1]
      rw [cc_ev_lemma _ (fun j i => by rw [Fin.fin_one_eq_zero j]; simp [pt]) _]
      simp [ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.FB.actK, MvPowerSeries.constantCoeff_map, Y.B.A.const]

end VP

end Formalism.L2.FormalSeriesBounds
