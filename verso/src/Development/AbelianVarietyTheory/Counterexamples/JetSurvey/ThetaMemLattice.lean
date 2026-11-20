import Mathlib
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.RStatement
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.RPfVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.WeightFloorInequalities
import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.FormAtOfClause
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.NuAlgLeOfCharts

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.DepthBoundTest

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1

variable {D : D7}

/- English proof (translation)
Proceed by induction on `q with`. Consider the case `zero => simp`. Consider the case `succ q ih`. Rewrite using `[← add_assoc, Nat.choose_succ_succ' (p + q) 1, Nat.choose_succ_succ' q 1, ih]`. Simplify using `only [Nat.choose_one_right]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem choose_two_add (p q : ℕ) : (p + q).choose 2 = p * q + p.choose 2 + q.choose 2 := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [← add_assoc, Nat.choose_succ_succ' (p + q) 1, Nat.choose_succ_succ' q 1, ih]
    simp only [Nat.choose_one_right]
    ring

/- English proof (translation)
Establish `h : D.R.r = (D.R.sigW j).1 + (D.R.sigW j).2`. Use `hj.1` as an intermediate fact. Use `hj.2` as an intermediate fact. Unfold `Ranks.r Ranks.sigW`. Simplify using `only`.

Use linear arithmetic over natural numbers and integers. Unfold `WeightFamilies.dimY`. Rewrite using `[h, choose_two_add, Nat.choose_two_right, Nat.choose_two_right]`.
-/
theorem dimY_eq_flag {j : ℕ} (hj : InR D j) : WeightFamilies.dimY D j = D.R.f * D.R.r.choose 2 := by
  have h : D.R.r = (D.R.sigW j).1 + (D.R.sigW j).2 := by
    have := hj.1; have := hj.2
    unfold Ranks.r Ranks.sigW; simp only; omega
  unfold WeightFamilies.dimY
  rw [h, choose_two_add, Nat.choose_two_right, Nat.choose_two_right]

variable {L : SizeData₂ D} {P : ParameterChoice' D L}

/- English proof (translation)
Establish `h1` using `hj.1`. Establish `h2` using `hj.2`. Establish `hk : 5 ≤ D.R.k` using `by have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega`. Establish `ht : 5 ≤ D.R.t` using `by have := D.R.rank_add_five_le; omega`. Establish `hi' : i.1 = D.R.k + j - 2`.

Establish `: (D.R.sigW j).1 = D.R.k + j - 1` using `rfl`. Use linear arithmetic over natural numbers and integers. Establish `e1 : ((kaR Tp hK j).aP τ i : ℤ) = D.what₂.kaBig j τ i` using `kaWt_big D hK _ j h1 h2 τ i`. Establish `e2` using `(hK j h1 h2 τ).1 i`. Establish `hc : ((i.1 : ℕ) : ℚ) = (D.R.k : ℚ) + j - 1 - 1`.

Rewrite using `[hi', Nat.cast_sub (by omega)]; push_cast; ring`. Establish `hn : ¬ (i.1 < D.R.k - 1)` using `by omega`. Establish `hb : i.1 - (D.R.k - 1) < D.R.m` using `by omega`. Rewrite `e2` using `[DV.aPlusQ_eq, hc]`. Unfold `DV.sigPar DV.eQ at e2`.

Rewrite `e2` using `[dif_neg hn, dif_pos hb, dif_pos ⟨h1, h2⟩]`. Establish `hf : (⟨i.1 - (D.R.k - 1), hb⟩ : Fin D.R.m) = ⟨j - 1, by omega⟩` using `Fin.ext (by simp only; omega)`. Rewrite `e2` using `[hf]`. Establish `h3` using `(abs_le.1 (P.e_centred τ ⟨j - 1, by omega⟩)).1`. Establish `h4` using `Tp.heightBound_ge_order_sq`.

Establish `e3` using `congrArg (fun x : ℚ => (x : ℝ)) e2`. Move the coercions through the operations in `at e3 h3`. Establish `ht' : (5 : ℝ) ≤ D.R.t` using `by exact_mod_cast ht`. Establish `: 2 * (Tp.TO : ℝ) ^ 2 ≤ (D.what₂.kaBig j τ i : ℝ)` using `by linarith`. Rewrite using `[e1]`.

Conclude with `this` after adjusting the coercions.
-/
theorem two_sq_le_last (Tp : ParamsT D L P) (hK : DV.KapDef D) {j : ℕ} (hj : InR D j) (τ : D.what₂.Tau)
    (i : Fin (D.R.sigW j).1) (hi : i.1 + 1 = (D.R.sigW j).1) :
    2 * (Tp.TO : ℤ) ^ 2 ≤ ((kaR Tp hK j).aP τ i : ℤ) := by
  have h1 := hj.1
  have h2 := hj.2
  have hk : 5 ≤ D.R.k := by have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega
  have ht : 5 ≤ D.R.t := by have := D.R.rank_add_five_le; omega
  have hi' : i.1 = D.R.k + j - 2 := by
    have : (D.R.sigW j).1 = D.R.k + j - 1 := rfl
    omega
  have e1 : ((kaR Tp hK j).aP τ i : ℤ) = D.what₂.kaBig j τ i := kaWt_big D hK _ j h1 h2 τ i
  have e2 := (hK j h1 h2 τ).1 i
  have hc : ((i.1 : ℕ) : ℚ) = (D.R.k : ℚ) + j - 1 - 1 := by
    rw [hi', Nat.cast_sub (by omega)]; push_cast; ring
  have hn : ¬ (i.1 < D.R.k - 1) := by omega
  have hb : i.1 - (D.R.k - 1) < D.R.m := by omega
  rw [DV.aPlusQ_eq, hc] at e2
  unfold DV.sigPar DV.eQ at e2
  rw [dif_neg hn, dif_pos hb, dif_pos ⟨h1, h2⟩] at e2
  have hf : (⟨i.1 - (D.R.k - 1), hb⟩ : Fin D.R.m) = ⟨j - 1, by omega⟩ := Fin.ext (by simp only; omega)
  rw [hf] at e2
  have h3 := (abs_le.1 (P.e_centred τ ⟨j - 1, by omega⟩)).1
  have h4 := Tp.heightBound_ge_order_sq
  have e3 := congrArg (fun x : ℚ => (x : ℝ)) e2
  push_cast at e3 h3
  have ht' : (5 : ℝ) ≤ D.R.t := by exact_mod_cast ht
  have : 2 * (Tp.TO : ℝ) ^ 2 ≤ (D.what₂.kaBig j τ i : ℝ) := by linarith
  rw [e1]; exact_mod_cast this

/- English proof (translation)
Introduce `τ i hi`. Establish `ha` using `two_sq_le_last Tp hK hj τ i hi`. Establish `hd : WeightFamilies.dimY D j = Tp.Dp` using `by rw [dimY_eq_flag hj, Tp.Dp_eq]`. Establish `h40 : 40 * (((WeightFamilies.dimY D j : ℕ) : ℤ) + 2) ≤ Tp.TO` using `by rw [hd]; exact_mod_cast Tp.TO_40`. Establish `hc : (((WeightFamilies.dimY D j : ℕ) : ℤ) + 2) * Tp.nWn + 2 * D.R.r ≤ Tp.TO` using `by rw [hd]; exact_mod_cast Tp.TO_nW`.

Establish `key` using `(ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.weight_floor_inequalities _ _ (WeightFamilies.dimY D j) _ _ Tp.TO (WeightAlgebra.Tp D j Tp.TO) (by unfold WeightAlgebra.Tp; push_cast; ring) (by positivity) h40 hc ha rfl).1`. Use `show 1 ≤ ofGaps (lGapP D (kaR Tp hK j) Tp.TO Tp.nWn τ) i`. Rewrite using `[ofGaps_last _ _ (by omega)]`. Unfold `lGapP`. Rewrite using `[if_neg (by omega)]`.

Establish `: (2 : ℤ) ≤ (WeightAlgebra.Tp D j Tp.TO : ℤ)` using `by unfold WeightAlgebra.Tp; push_cast; omega`. Use linear arithmetic over natural numbers and integers.
-/
theorem lastPos_run (Tp : ParamsT D L P) (hK : DV.KapDef D) {j : ℕ} (hj : InR D j) : (lR Tp hK j).LastPos := by
  intro τ i hi
  have ha := two_sq_le_last Tp hK hj τ i hi
  have hd : WeightFamilies.dimY D j = Tp.Dp := by rw [dimY_eq_flag hj, Tp.Dp_eq]
  have h40 : 40 * (((WeightFamilies.dimY D j : ℕ) : ℤ) + 2) ≤ Tp.TO := by rw [hd]; exact_mod_cast Tp.TO_40
  have hc : (((WeightFamilies.dimY D j : ℕ) : ℤ) + 2) * Tp.nWn + 2 * D.R.r ≤ Tp.TO := by rw [hd]; exact_mod_cast Tp.TO_nW
  have key := (ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.weight_floor_inequalities _ _ (WeightFamilies.dimY D j) _ _ Tp.TO (WeightAlgebra.Tp D j Tp.TO)
    (by unfold WeightAlgebra.Tp; push_cast; ring) (by positivity) h40 hc ha rfl).1
  show 1 ≤ ofGaps (lGapP D (kaR Tp hK j) Tp.TO Tp.nWn τ) i
  rw [ofGaps_last _ _ (by omega)]
  unfold lGapP
  rw [if_neg (by omega)]
  have : (2 : ℤ) ≤ (WeightAlgebra.Tp D j Tp.TO : ℤ) := by unfold WeightAlgebra.Tp; push_cast; omega
  omega

/- English proof (translation)
Establish `hc : f ∈ cutR T.C j (lR Tp hK j)`. Rewrite using `[cutR_eq T.C hj]`. Conclude with `h.thCusp j hj _ _ (dom_wtA _) (ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.lastPos_wtA h hj _ (lastPos_run Tp hK hj)) f hf`. Conclude with `⟨⟨f, hc⟩, Submodule.subset_span hf, rfl⟩`.
-/
theorem theta_mem_lattice (Tp : ParamsT D L P) (hK : DV.KapDef D) {T : Top D} (h : LawsP T) {j : ℕ} (hj : InR D j)
    {f : T.R j} (hf : f ∈ T.th j (lR Tp hK j)) :
    ∃ F ∈ (recPJ h j hj).thAll (lR Tp hK j), F.1 = f := by
  have hc : f ∈ cutR T.C j (lR Tp hK j) := by
    rw [cutR_eq T.C hj]
    exact h.thCusp j hj _ _ (dom_wtA _) (ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.lastPos_wtA h hj _ (lastPos_run Tp hK hj)) f hf
  exact ⟨⟨f, hc⟩, Submodule.subset_span hf, rfl⟩

section Record

variable {B : WeightFamilies.Prov D} {Q : ModuliIntegralCharts.Prov D} {j : ℕ} (X : WeightAlgebra.PJ D B Q j)

/- English proof (translation)
Establish `hs' : (s : B.KO) ≠ 0` using `fun h => hs (RingOfIntegers.coe_eq_zero_iff.1 h)`. Establish `e : ∀ t : 𝓞 B.KO, X.depth t w la y = ⨅ F : X.thAll w, X.vAt la y (X.inc w (t • F.1))`. Introduce `t`. Unfold `WeightAlgebra.PJ.depth WeightAlgebra.PJ.WWc WeightAlgebra.PJ.scaled`. Apply `le_antisymm` to reduce the goal to its premises.

Conclude with `le_iInf fun F => iInf₂_le _ ⟨F.1, F.2, rfl⟩`. Use `le_iInf₂ ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨F, hF, rfl⟩`. Conclude with `iInf_le (fun F : X.thAll w => X.vAt la y (X.inc w (t • F.1))) ⟨F, hF⟩`. Establish `e2 : ∀ F : X.thAll w, X.vAt la y (X.inc w (s • F.1)) = X.vAt la y (X.inc w ((1 : 𝓞 B.KO) • F.1)) + (((vAdd la (s : B.KO) : ℤ) : ℝ) : EReal)`.

Introduce `F`. Establish `: s • F.1 = (s : B.KO) • F.1` using `(algebraMap_smul B.KO s F.1).symm`. Rewrite using `[this, map_smul, X.vAt_smul la y _ _ hs', one_smul, add_comm]`. Rewrite using `[e s, e 1]`. Repeatedly rewrite using `[e2]`.

Use `set c : ℝ := ((vAdd la (s : B.KO) : ℤ) : ℝ)`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[← EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot c)) (Or.inl (EReal.coe_ne_top c))]`. Use `le_iInf fun F => ?_` and prove the remaining obligations. Rewrite using `[EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot c)) (Or.inl (EReal.coe_ne_top c))]`.

Conclude with `iInf_le _ F`. Conclude with `le_iInf fun F => add_le_add (iInf_le _ F) le_rfl`.
-/
theorem depth_scale (s : 𝓞 B.KO) (hs : s ≠ 0) (w : WeightFamilies.Wt D j) (la : HeightOneSpectrum (𝓞 B.KO)) (y : X.Pt la) :
    X.depth s w la y = X.depth 1 w la y + (((vAdd la (s : B.KO) : ℤ) : ℝ) : EReal) := by
  have hs' : (s : B.KO) ≠ 0 := fun h => hs (RingOfIntegers.coe_eq_zero_iff.1 h)
  have e : ∀ t : 𝓞 B.KO, X.depth t w la y = ⨅ F : X.thAll w, X.vAt la y (X.inc w (t • F.1)) := by
    intro t
    unfold WeightAlgebra.PJ.depth WeightAlgebra.PJ.WWc WeightAlgebra.PJ.scaled
    apply le_antisymm
    · exact le_iInf fun F => iInf₂_le _ ⟨F.1, F.2, rfl⟩
    · refine le_iInf₂ ?_
      rintro _ ⟨F, hF, rfl⟩
      exact iInf_le (fun F : X.thAll w => X.vAt la y (X.inc w (t • F.1))) ⟨F, hF⟩
  have e2 : ∀ F : X.thAll w, X.vAt la y (X.inc w (s • F.1)) =
      X.vAt la y (X.inc w ((1 : 𝓞 B.KO) • F.1)) + (((vAdd la (s : B.KO) : ℤ) : ℝ) : EReal) := by
    intro F
    have : s • F.1 = (s : B.KO) • F.1 := (algebraMap_smul B.KO s F.1).symm
    rw [this, map_smul, X.vAt_smul la y _ _ hs', one_smul, add_comm]
  rw [e s, e 1]
  simp_rw [e2]
  set c : ℝ := ((vAdd la (s : B.KO) : ℤ) : ℝ)
  apply le_antisymm
  · rw [← EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot c)) (Or.inl (EReal.coe_ne_top c))]
    refine le_iInf fun F => ?_
    rw [EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot c)) (Or.inl (EReal.coe_ne_top c))]
    exact iInf_le _ F
  · exact le_iInf fun F => add_le_add (iInf_le _ F) le_rfl

end Record

/- English proof (translation)
The claim follows from `h.pins.2.1.1`.
-/
theorem level_eq {T : Top D} (h : LawsP T) : (T.Q.l.M : ℕ) = D.host.g 0 * D.host.g 1 := h.pins.2.1.1

/- English proof (translation)
Use `⟨?_, fun f hf => theta_mem_lattice Tp hK h hj hf, rfl, level_eq h⟩` and prove the remaining obligations. Establish `hv` using `RPfVal.vAdd_sW (recB h.toLawsCore) hinj EX (lR Tp hK j) la hg`. Establish `hnn` using `RPfVal.nnW_not_mem (recB h.toLawsCore) hinj EX (lR Tp hK j) la hg`. Establish `hne : (runOf Tp hK (recB h.toLawsCore) hinj EX nuWW j).S.sW ≠ 0`. Use `mul_ne_zero (fun h0 => hnn (h0 ▸ la.asIdeal.zero_mem)) ?_` and prove the remaining obligations.

Establish `hq : D.host.q.Prime` using `D.host.hyp.1`. Establish `hd : D.host.d.Prime` using `D.host.hyp.2.1`. Conclude with `Nat.cast_ne_zero.2 (Nat.mul_ne_zero (Nat.mul_ne_zero (pow_ne_zero _ D.host.QS_pos.ne') (pow_ne_zero _ hq.ne_zero)) (pow_ne_zero _ hd.ne_zero))`. Rewrite using `[depth_scale _ _ hne, ← hv]`. Both sides reduce to the same expression.
-/
theorem main (Tp : ParamsT D L P) (hK : DV.KapDef D) {T : Top D} (h : LawsP T)
    (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (nuWW : ℕ → HeightOneSpectrum (𝓞 T.Q.c.F) → ℝ)
    {j : ℕ} (hj : InR D j) (la : HeightOneSpectrum (𝓞 T.Q.c.F))
    (hg : ∀ i : Fin 2, ((D.host.g i : ℕ) : 𝓞 T.Q.c.F) ∉ la.asIdeal) (y : (recPJ h j hj).Pt la) :
    (recPJ h j hj).depth (runOf Tp hK (recB h.toLawsCore) hinj EX nuWW j).S.sW (lR Tp hK j) la y =
        (recPJ h j hj).depth 1 (lR Tp hK j) la y + (((ramOverZ la : ℝ) * clOf (lR Tp hK j) la : ℝ) : EReal) ∧
      (∀ f ∈ T.th j (lR Tp hK j), ∃ F ∈ (recPJ h j hj).thAll (lR Tp hK j), F.1 = f) ∧
      (lR Tp hK j).n = Tp.nWn ∧ (T.Q.l.M : ℕ) = D.host.g 0 * D.host.g 1 := by
  refine ⟨?_, fun f hf => theta_mem_lattice Tp hK h hj hf, rfl, level_eq h⟩
  have hv := RPfVal.vAdd_sW (recB h.toLawsCore) hinj EX (lR Tp hK j) la hg
  have hnn := RPfVal.nnW_not_mem (recB h.toLawsCore) hinj EX (lR Tp hK j) la hg
  have hne : (runOf Tp hK (recB h.toLawsCore) hinj EX nuWW j).S.sW ≠ 0 := by
    refine mul_ne_zero (fun h0 => hnn (h0 ▸ la.asIdeal.zero_mem)) ?_
    have hq : D.host.q.Prime := D.host.hyp.1
    have hd : D.host.d.Prime := D.host.hyp.2.1
    exact Nat.cast_ne_zero.2 (Nat.mul_ne_zero (Nat.mul_ne_zero (pow_ne_zero _ D.host.QS_pos.ne') (pow_ne_zero _ hq.ne_zero))
      (pow_ne_zero _ hd.ne_zero))
  rw [depth_scale _ _ hne, ← hv]
  rfl

end GlobalTheory.DepthBoundTest
