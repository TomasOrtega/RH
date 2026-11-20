import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Generic
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.TheoremZeroOfReducedInputs
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LiftIndexPowFourLeDegree
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.AdmissibleModuleIffLatticeQuotients
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.MaximalCuspKernels.KerExistsStatement
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SupBoundPageRows
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LocalUnfoldBStatementHolds
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ModelWeightSizeSpreadBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.WeightFloorInequalities
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.RunIn GlobalTheory.Shares

noncomputable section

namespace GlobalTheory.Shares.WtDic

variable {D : D7}

/- English proof (translation)
The claim follows from `D.eTau.injective (Subtype.ext ((factEmb D.R D.host).1.1 h))`.
-/
theorem tauEmb_inj {t t' : D.what₂.Tau} (h : DV.tauEmb D t = DV.tauEmb D t') : t = t' :=
  D.eTau.injective (Subtype.ext ((factEmb D.R D.host).1.1 h))

/- English proof (translation)
The claim follows from `RingHom.ext fun x => by simp [conjEmb]`.
-/
theorem conjEmb_conjEmb {E : Type} [Field E] (τ : E →+* ℂ) : conjEmb (conjEmb τ) = τ :=
  RingHom.ext fun x => by simp [conjEmb]

/- English proof (translation)
Introduce `h`. Establish `h1 : conjEmb (DV.tauEmb D t') = D.host.emb (((D.eTau t' : D.R.Psi) : D.R.GG) * D.R.cc)`. Rewrite using `[Formalism.L2.Geo.emb_mul_cc_comp]`. Use `RingHom.ext fun x => ?_` and prove the remaining obligations. Conclude with `(Formalism.MainNotions.WeightFamilies.emb_conj D (DV.tauEmb D t') x).symm`.

Establish `h2` using `(Formalism.L2.Geo.exists_tauEmb_iff D _).1 ⟨t, (h.trans h1).symm⟩`. Conclude with `(Formalism.L2.Geo.mem_Psi_iff_mul_cc_notMem _).1 (D.eTau t').2 h2`.
-/
theorem tauEmb_ne_conj (t t' : D.what₂.Tau) : DV.tauEmb D t ≠ conjEmb (DV.tauEmb D t') := by
  intro h
  have h1 : conjEmb (DV.tauEmb D t') =
      D.host.emb (((D.eTau t' : D.R.Psi) : D.R.GG) * D.R.cc) := by
    rw [Formalism.L2.Geo.emb_mul_cc_comp]
    refine RingHom.ext fun x => ?_
    exact (Formalism.MainNotions.WeightFamilies.emb_conj D (DV.tauEmb D t') x).symm
  have h2 := (Formalism.L2.Geo.exists_tauEmb_iff D _).1 ⟨t, (h.trans h1).symm⟩
  exact (Formalism.L2.Geo.mem_Psi_iff_mul_cc_notMem _).1 (D.eTau t').2 h2

/- English proof (translation)
Unfold `wtA`. Rewrite using `[Finset.sum_eq_single t]`. Simplify using `[tauEmb_ne_conj]`. Introduce `t' _ ht'`. Establish `: DV.tauEmb D t ≠ DV.tauEmb D t'` using `fun h => ht' (tauEmb_inj h).symm`.

Simplify using `[tauEmb_ne_conj, this]`. Simplify using the standard rewrite rules.
-/
theorem wtA_tau {j : ℕ} (w : WeightFamilies.Wt D j) (t : D.what₂.Tau) (i : ℕ) :
    wtA w (DV.tauEmb D t, i) = ext0 (w.aP t) i := by
  classical
  unfold wtA
  rw [Finset.sum_eq_single t]
  · simp [tauEmb_ne_conj]
  · intro t' _ ht'
    have : DV.tauEmb D t ≠ DV.tauEmb D t' := fun h => ht' (tauEmb_inj h).symm
    simp [tauEmb_ne_conj, this]
  · simp

/- English proof (translation)
Unfold `wtA`. Rewrite using `[Finset.sum_eq_single t]`. Simplify using `[(tauEmb_ne_conj _ _).symm]`. Introduce `t' _ ht'`. Establish `: conjEmb (DV.tauEmb D t) ≠ conjEmb (DV.tauEmb D t')` using `fun h => ht' (tauEmb_inj (by`.

Use `congrArg conjEmb h` as an intermediate fact. Rewrite using `[conjEmb_conjEmb, conjEmb_conjEmb] at this)).symm` and apply the resulting hypothesis. Simplify using `[(tauEmb_ne_conj _ _).symm, this]`. Simplify using the standard rewrite rules.
-/
theorem wtA_conj {j : ℕ} (w : WeightFamilies.Wt D j) (t : D.what₂.Tau) (i : ℕ) :
    wtA w (conjEmb (DV.tauEmb D t), i) = ext0 (w.aM t) i := by
  classical
  unfold wtA
  rw [Finset.sum_eq_single t]
  · simp [(tauEmb_ne_conj _ _).symm]
  · intro t' _ ht'
    have : conjEmb (DV.tauEmb D t) ≠ conjEmb (DV.tauEmb D t') := fun h => ht' (tauEmb_inj (by
      have := congrArg conjEmb h
      rwa [conjEmb_conjEmb, conjEmb_conjEmb] at this)).symm
    simp [(tauEmb_ne_conj _ _).symm, this]
  · simp

/- English proof (translation)
Apply the tactic sequence `unfold ext0; split_ifs <;> rfl`.
-/
theorem matrixExtendByZero_mul {p : ℕ} (c : ℕ) (f : Fin p → ℕ) (i : ℕ) : ext0 (fun k => c * f k) i = c * ext0 f i := by
  unfold ext0; split_ifs <;> rfl

/- English proof (translation)
Simplify using `only [wtA, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun t _ => ?_` and prove the remaining obligations. Establish `h1 : ext0 ((wsmul c w).aP t) x.2 = c * ext0 (w.aP t) x.2` using `matrixExtendByZero_mul _ _ _`. Establish `h2 : ext0 ((wsmul c w).aM t) x.2 = c * ext0 (w.aM t) x.2` using `matrixExtendByZero_mul _ _ _`. Rewrite using `[h1, h2]`.

Apply the tactic sequence `split_ifs <;> ring`.
-/
theorem wtA_wsmul {j : ℕ} (c : ℕ) (w : WeightFamilies.Wt D j) (x : (D.host.E →+* ℂ) × ℕ) :
    wtA (wsmul c w) x = c * wtA w x := by
  simp only [wtA, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  have h1 : ext0 ((wsmul c w).aP t) x.2 = c * ext0 (w.aP t) x.2 := matrixExtendByZero_mul _ _ _
  have h2 : ext0 ((wsmul c w).aM t) x.2 = c * ext0 (w.aM t) x.2 := matrixExtendByZero_mul _ _ _
  rw [h1, h2]
  split_ifs <;> ring

/- English proof (translation)
Simplify using `only [wtA]`. Use `Finset.sum_eq_zero fun t _ => ?_` and prove the remaining obligations. Apply the tactic sequence `have h1 : ext0 ((wscalar D j n hn).aP t) x.2 = 0 := by unfold ext0; split_ifs <;> rfl`. Apply the tactic sequence `have h2 : ext0 ((wscalar D j n hn).aM t) x.2 = 0 := by unfold ext0; split_ifs <;> rfl`. Rewrite using `[h1, h2]`.

Simplify using the standard rewrite rules.
-/
theorem wtA_wscalar (j n : ℕ) (hn : Even n) (x : (D.host.E →+* ℂ) × ℕ) : wtA (wscalar D j n hn) x = 0 := by
  simp only [wtA]
  refine Finset.sum_eq_zero fun t _ => ?_
  have h1 : ext0 ((wscalar D j n hn).aP t) x.2 = 0 := by unfold ext0; split_ifs <;> rfl
  have h2 : ext0 ((wscalar D j n hn).aM t) x.2 = 0 := by unfold ext0; split_ifs <;> rfl
  rw [h1, h2]
  simp

/- English proof (translation)
Use function extensionality and compare the values at `τ a`. Establish `hn : (wadd u u').n / 2 = u.n / 2 + u'.n / 2`. Establish `h1` using `u.n_even`. Establish `h2` using `u'.n_even`. Rewrite using `[n_wadd]`.

Rewrite `h1`, `h2` using `[Nat.even_iff]`. Use linear arithmetic over natural numbers and integers. Simplify using `only [laR, laU, Pi.add_apply, wtA_wadd, hn]`. Apply the tactic sequence `split_ifs <;> push_cast <;> ring`.
-/
theorem laR_wadd (T : Top D) (j : ℕ) (k : (T.U j T.σ₀).Comp) (u u' : WeightFamilies.Wt D j) :
    laR T j (wadd u u') k = laR T j u k + laR T j u' k := by
  funext τ a
  have hn : (wadd u u').n / 2 = u.n / 2 + u'.n / 2 := by
    have h1 := u.n_even
    have h2 := u'.n_even
    rw [n_wadd]
    rw [Nat.even_iff] at h1 h2
    omega
  simp only [laR, laU, Pi.add_apply, wtA_wadd, hn]
  split_ifs <;> push_cast <;> ring

/- English proof (translation)
Use function extensionality and compare the values at `τ a`. Establish `hn : (wsmul m u).n / 2 = m * (u.n / 2)`. Take `⟨s, hs⟩` from `u.n_even`. Use `show m * u.n / 2 = _`. Rewrite using `[hs, ← two_mul, Nat.mul_div_cancel_left _ two_pos, Nat.mul_left_comm, Nat.mul_div_cancel_left _ two_pos]`.

Simplify using `only [laR, laU, Pi.smul_apply, wtA_wsmul, hn, nsmul_eq_mul]`. Apply the tactic sequence `split_ifs <;> push_cast <;> ring`.
-/
theorem laR_wsmul (T : Top D) (j : ℕ) (k : (T.U j T.σ₀).Comp) (m : ℕ) (u : WeightFamilies.Wt D j) :
    laR T j (wsmul m u) k = m • laR T j u k := by
  funext τ a
  have hn : (wsmul m u).n / 2 = m * (u.n / 2) := by
    obtain ⟨s, hs⟩ := u.n_even
    show m * u.n / 2 = _
    rw [hs, ← two_mul, Nat.mul_div_cancel_left _ two_pos, Nat.mul_left_comm, Nat.mul_div_cancel_left _ two_pos]
  simp only [laR, laU, Pi.smul_apply, wtA_wsmul, hn, nsmul_eq_mul]
  split_ifs <;> push_cast <;> ring

/- English proof (translation)
Establish `e : {p : Fin r × Fin r // p.2 < p.1} ≃ Σ a : Fin r, Finset.Iio a` using `{ toFun := fun p => ⟨p.1.1, p.1.2, Finset.mem_Iio.2 p.2⟩ invFun := fun x => ⟨(x.1, x.2.1), Finset.mem_Iio.1 x.2.2⟩ left_inv := fun _ => rfl right_inv := fun _ => rfl }`. Rewrite using `[Fintype.card_congr e, Fintype.card_sigma]`. Simplify using `only [Fintype.card_coe, Fin.card_Iio]`. Rewrite using `[Fin.sum_univ_eq_sum_range (fun i => i) r, Finset.sum_range_id]`.
-/
theorem card_lower (r : ℕ) : Fintype.card {p : Fin r × Fin r // p.2 < p.1} = r * (r - 1) / 2 := by
  have e : {p : Fin r × Fin r // p.2 < p.1} ≃ Σ a : Fin r, Finset.Iio a :=
    { toFun := fun p => ⟨p.1.1, p.1.2, Finset.mem_Iio.2 p.2⟩
      invFun := fun x => ⟨(x.1, x.2.1), Finset.mem_Iio.1 x.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Fintype.card_congr e, Fintype.card_sigma]
  simp only [Fintype.card_coe, Fin.card_Iio]
  rw [Fin.sum_univ_eq_sum_range (fun i => i) r, Finset.sum_range_id]

/- English proof (translation)
Rewrite using `[← Nat.choose_two_right, ← Nat.choose_two_right, ← Nat.choose_two_right]`. Proceed by induction on `q with`. Consider the case `zero => simp`. Consider the case `succ q ih`. Rewrite using `[← add_assoc, Nat.choose_succ_succ' (p + q) 1, Nat.choose_succ_succ' q 1, ih]`.

Simplify using `only [Nat.choose_one_right]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem choose_split (p q : ℕ) : (p + q) * (p + q - 1) / 2 = p * q + p * (p - 1) / 2 + q * (q - 1) / 2 := by
  rw [← Nat.choose_two_right, ← Nat.choose_two_right, ← Nat.choose_two_right]
  induction q with
  | zero => simp
  | succ q ih =>
    rw [← add_assoc, Nat.choose_succ_succ' (p + q) 1, Nat.choose_succ_succ' q 1, ih]
    simp only [Nat.choose_one_right]
    ring

/- English proof (translation)
Introduce `D T h j hj k`. Take `⟨hr, hk, -⟩` from `h.unf j hj T.σ₀ T.good_σ₀`. Take `⟨hp0, hΨ⟩` from `hk k`. Take `⟨hp, hq, -⟩` from `h.pins.2.2.2 j hj`. Establish `hc : Fintype.card ((T.U j T.σ₀).X k).Ψ = D.R.f`.

Establish `h1` using `GlobalTheory.RunIn.WtSize.two_mul_card_cm ((T.U j T.σ₀).X k)`. Rewrite `h1` using `[ReciprocityTheory.ChartRestriction.G.PullbackSections.PfTorusFrame.finrank_eq D]`. Use linear arithmetic over natural numbers and integers. Use `⟨laR_wadd T j k, laR_wsmul T j k, fun u v m => ?_, fun i => ?_, ?_, hp0.trans hq, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[addL, laR_wadd, laR_wsmul]`.

Use function extensionality and compare the values at `τ a`. Establish `hn : (etWt D j i).n / 2 = i * (g0 D / 2)` using `by show g0 D * i / 2 = _`. Unfold `g0`. Rewrite using `[mul_assoc 2, mul_assoc 2, Nat.mul_div_cancel_left _ two_pos, Nat.mul_div_cancel_left _ two_pos, mul_comm]`. Establish `hw : ∀ x, wtA (etWt D j i) x = 0` using `wtA_wscalar _ _ _`.

Simplify using `only [laR, laU, Pi.smul_apply, hw, hn, nsmul_eq_mul, de2W]`. Apply the tactic sequence `split_ifs <;> simp`. Rewrite using `[nd, Fintype.card_prod, hc, card_lower, WeightFamilies.dimY, ← choose_split, hr, hp, hq]`. Rewrite using `[← hc, Fintype.card_coe]`. Set `f : D.what₂.Tau → ((T.U j T.σ₀).X k).Ψ` to `fun t => ⟨DV.tauEmb D t, (hΨ _).2 (h.pins.1.2.2.2 t)⟩`.

Establish `hf : Function.Bijective f`. Use `⟨fun t t' e => tauEmb_inj (congrArg Subtype.val e), fun τ => ?_⟩` and prove the remaining obligations. Take `⟨t, ht⟩` from `ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.exists_tau_of_inPsi T.Q h.pins.1 τ.1 ((hΨ _).1 τ.2)`. Conclude with `⟨t, Subtype.ext ht.symm⟩`. Establish `hinv : ∀ τ, Function.invFun (relab T.Q.c T.σ₀) τ = τ` using `fun τ => Function.leftInverse_invFun (GlobalTheory.RunIn.WtSize.relab_bijective T.Q.c T.σ₀).1 τ`.

Use `⟨(Equiv.ofBijective f hf).symm, fun u τ a => ?_⟩` and prove the remaining obligations. Take `⟨t, rfl⟩` from `(Equiv.ofBijective f hf).surjective τ`. Rewrite using `[Equiv.symm_apply_apply]`. Establish `e : ((Equiv.ofBijective f hf) t).1 = DV.tauEmb D t` using `rfl`. Simplify using `only [laR, laU, hinv, e, wtA_tau, wtA_conj]`.
-/
theorem weights_dictionary : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (k : (T.U j T.σ₀).Comp), (∀ u u' : WeightFamilies.Wt D j, laR T j (wadd u u') k = laR T j u k + laR T j u' k) ∧ (∀ (m : ℕ) (u : WeightFamilies.Wt D j), laR T j (wsmul m u) k = m • laR T j u k) ∧ (∀ (u v : WeightFamilies.Wt D j) (m : ℕ), laR T j (addL u v m) k = laR T j u k + m • laR T j v k) ∧ (∀ i : ℕ, laR T j (etWt D j i) k = (i * (g0 D / 2)) • de2W ((T.U j T.σ₀).X k)) ∧ nd ((T.U j T.σ₀).X k) = WeightFamilies.dimY D j ∧ ((T.U j T.σ₀).X k).p0 = (D.R.sigW j).2 ∧ ((T.U j T.σ₀).X k).Ψ.card = D.R.f ∧ ∃ tt : ((T.U j T.σ₀).X k).Ψ ≃ D.what₂.Tau, ∀ (u : WeightFamilies.Wt D j) (τ : ((T.U j T.σ₀).X k).Ψ) (a : Fin D.R.r), laR T j u k τ a = if ((T.U j T.σ₀).X k).p0 ≤ (a : ℕ) then (ext0 (u.aP (tt τ)) ((a : ℕ) - ((T.U j T.σ₀).X k).p0) : ℤ) + ((u.n / 2 : ℕ) : ℤ) else -(ext0 (u.aM (tt τ)) (((T.U j T.σ₀).X k).p0 - 1 - (a : ℕ)) : ℤ) - ((u.n / 2 : ℕ) : ℤ) := by
  intro D T h j hj k
  obtain ⟨hr, hk, -⟩ := h.unf j hj T.σ₀ T.good_σ₀
  obtain ⟨hp0, hΨ⟩ := hk k
  obtain ⟨hp, hq, -⟩ := h.pins.2.2.2 j hj
  have hc : Fintype.card ((T.U j T.σ₀).X k).Ψ = D.R.f := by
    have h1 := GlobalTheory.RunIn.WtSize.two_mul_card_cm ((T.U j T.σ₀).X k)
    rw [ReciprocityTheory.ChartRestriction.G.PullbackSections.PfTorusFrame.finrank_eq D] at h1
    omega
  refine ⟨laR_wadd T j k, laR_wsmul T j k, fun u v m => ?_, fun i => ?_, ?_, hp0.trans hq, ?_, ?_⟩
  · rw [addL, laR_wadd, laR_wsmul]
  · funext τ a
    have hn : (etWt D j i).n / 2 = i * (g0 D / 2) := by
      show g0 D * i / 2 = _
      unfold g0
      rw [mul_assoc 2, mul_assoc 2, Nat.mul_div_cancel_left _ two_pos, Nat.mul_div_cancel_left _ two_pos, mul_comm]
    have hw : ∀ x, wtA (etWt D j i) x = 0 := wtA_wscalar _ _ _
    simp only [laR, laU, Pi.smul_apply, hw, hn, nsmul_eq_mul, de2W]
    split_ifs <;> simp
  · rw [nd, Fintype.card_prod, hc, card_lower, WeightFamilies.dimY, ← choose_split, hr, hp, hq]
  · rw [← hc, Fintype.card_coe]
  · let f : D.what₂.Tau → ((T.U j T.σ₀).X k).Ψ := fun t => ⟨DV.tauEmb D t, (hΨ _).2 (h.pins.1.2.2.2 t)⟩
    have hf : Function.Bijective f := by
      refine ⟨fun t t' e => tauEmb_inj (congrArg Subtype.val e), fun τ => ?_⟩
      obtain ⟨t, ht⟩ := ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.exists_tau_of_inPsi T.Q h.pins.1 τ.1 ((hΨ _).1 τ.2)
      exact ⟨t, Subtype.ext ht.symm⟩
    have hinv : ∀ τ, Function.invFun (relab T.Q.c T.σ₀) τ = τ := fun τ =>
      Function.leftInverse_invFun (GlobalTheory.RunIn.WtSize.relab_bijective T.Q.c T.σ₀).1 τ
    refine ⟨(Equiv.ofBijective f hf).symm, fun u τ a => ?_⟩
    obtain ⟨t, rfl⟩ := (Equiv.ofBijective f hf).surjective τ
    rw [Equiv.symm_apply_apply]
    have e : ((Equiv.ofBijective f hf) t).1 = DV.tauEmb D t := rfl
    simp only [laR, laU, hinv, e, wtA_tau, wtA_conj]

end GlobalTheory.Shares.WtDic
