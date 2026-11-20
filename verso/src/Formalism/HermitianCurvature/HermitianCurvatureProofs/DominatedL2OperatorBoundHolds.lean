import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFTopDom
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutDomCutInt
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutLemB
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutFpmDecay
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDCCLower

namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def bcE (r : ℕ) : (Fin (r + 1) → ℂ) ≃ᵐ (Fin r → ℂ) × ℂ :=
  (MeasurableEquiv.piFinSuccAbove (fun _ => ℂ) (Fin.last r)).trans MeasurableEquiv.prodComm

/- English proof (translation)
Apply the tactic sequence `ext j <;> simp [bcE, MeasurableEquiv.piFinSuccAbove_apply] <;> rfl`.
-/
theorem bcE_apply (r : ℕ) (c : Fin (r + 1) → ℂ) : bcE r c = ((fun j => c j.castSucc), c (Fin.last r)) := by
  ext j <;> simp [bcE, MeasurableEquiv.piFinSuccAbove_apply] <;> rfl

/- English proof (translation)
Establish `h` using `(Measure.measurePreserving_swap (μ := (volume : Measure ℂ)) (ν := Measure.pi fun _ : Fin r => (volume : Measure ℂ))).comp (measurePreserving_piFinSuccAbove (fun _ : Fin (r + 1) => (volume : Measure ℂ)) (Fin.last r))`. Conclude with `h`.
-/
theorem bcE_mp (r : ℕ) : MeasurePreserving (bcE r) volume volume := by
  have h := (Measure.measurePreserving_swap (μ := (volume : Measure ℂ))
    (ν := Measure.pi fun _ : Fin r => (volume : Measure ℂ))).comp
    (measurePreserving_piFinSuccAbove (fun _ : Fin (r + 1) => (volume : Measure ℂ)) (Fin.last r))
  exact h

/- English proof (translation)
Conclude with `ae_all_iff.2 fun a => Measure.ae_eval_ne (fun _ => (volume : Measure ℂ)) a 0`.
-/
theorem ae_ne_zero_all (r : ℕ) : ∀ᵐ c : Fin (r + 1) → ℂ, ∀ a, c a ≠ 0 := by
  exact ae_all_iff.2 fun a => Measure.ae_eval_ne (fun _ => (volume : Measure ℂ)) a 0

section place

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

/- English proof (translation)
Proceed by induction on `L with`. Consider the case `nil => intro a b`. Simplify using `[D.ptEntry]`. Consider the case `cons t L ih`. Introduce `a b`.

Apply the tactic sequence `rcases a with _ | a <;> rcases b with _ | b <;> simp [D.ptEntry, ih]`.
-/
private theorem ptEntry_map_one_eq_ite_getD (L : List ℂ) :
    ∀ a b : ℕ, D.ptEntry (L.map fun t => ((1 : ℕ), t)) a b = if a = b then L.getD a 0 else 0 := by
  induction L with
  | nil => intro a b; simp [D.ptEntry]
  | cons t L ih =>
    intro a b
    rcases a with _ | a <;> rcases b with _ | b <;> simp [D.ptEntry, ih]

/- English proof (translation)
Establish `hb : TBB.bigPt r c = (List.ofFn c).map fun t => ((1 : ℕ), t)`. Simplify using `[TBB.bigPt, List.map_ofFn, Function.comp_def]`. Use extensionality with `a b`. Rewrite using `[D.ptMatN, hb, ptEntry_map_one_eq_ite_getD, Matrix.diagonal_apply]`. Distinguish the cases in `h : a = b`.

Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using `[h, Fin.val_inj]`.
-/
private theorem ptMatN_bigPt_eq_diagonal (r n : ℕ) (c : Fin (r + 1) → ℂ) :
    D.ptMatN (TBB.bigPt r c) n = Matrix.diagonal fun i : Fin n => (List.ofFn c).getD i 0 := by
  have hb : TBB.bigPt r c = (List.ofFn c).map fun t => ((1 : ℕ), t) := by
    simp [TBB.bigPt, List.map_ofFn, Function.comp_def]
  ext a b
  rw [D.ptMatN, hb, ptEntry_map_one_eq_ite_getD, Matrix.diagonal_apply]
  by_cases h : a = b
  · subst h; simp
  · simp [h, Fin.val_inj]

/- English proof (translation)
Simplify using `[List.getD_eq_getElem?_getD, hj]`.
-/
private theorem ofFn_getD_eq_apply {m : ℕ} (c : Fin m → ℂ) (j : ℕ) (hj : j < m) :
    (List.ofFn c).getD j 0 = c ⟨j, hj⟩ := by
  simp [List.getD_eq_getElem?_getD, hj]

/- English proof (translation)
Simplify using `only [TBB.Gp, D.ptG, ptMatN_bigPt_eq_diagonal, Matrix.det_diagonal]`. Establish `h1 : ∀ i : Fin (P.r + 1), (List.ofFn c).getD i 0 = c i` using `fun i => ofFn_getD_eq_apply c i i.isLt`. Establish `h2 : ∀ i : Fin P.r, (List.ofFn c).getD i 0 = c i.castSucc` using `fun i => ofFn_getD_eq_apply c i (by omega)`. Simplify using `only [h1, h2]`.
-/
theorem Gp_bigPt_eq (p : KB.Pl P Wp Wq) (c : Fin (P.r + 1) → ℂ) :
    TBB.Gp p (TBB.bigPt P.r c) =
      Complex.normSq (∏ i, c i) - TBB.TTp p * Complex.normSq (∏ i : Fin P.r, c i.castSucc) := by
  simp only [TBB.Gp, D.ptG, ptMatN_bigPt_eq_diagonal, Matrix.det_diagonal]
  have h1 : ∀ i : Fin (P.r + 1), (List.ofFn c).getD i 0 = c i := fun i => ofFn_getD_eq_apply c i i.isLt
  have h2 : ∀ i : Fin P.r, (List.ofFn c).getD i 0 = c i.castSucc := fun i =>
    ofFn_getD_eq_apply c i (by omega)
  simp only [h1, h2]

/- English proof (translation)
Repeatedly rewrite using `[Gp_bigPt_eq]`. Use `fun_prop`.
-/
theorem Gp_bigPt_continuous (p : KB.Pl P Wp Wq) : Continuous fun c : Fin (P.r + 1) → ℂ => TBB.Gp p (TBB.bigPt P.r c) := by
  simp_rw [Gp_bigPt_eq]
  fun_prop

/- English proof (translation)
Use `⟨fun b hb => ?_, ?_⟩` and prove the remaining obligations. Rewrite `hb` using `[TBB.bigPt, List.mem_ofFn]`. Take `⟨l, rfl⟩` from `hb`. Conclude with `⟨le_rfl, hd l⟩`. Simplify using `[D.ptSize, TBB.bigPt, List.map_ofFn, Function.comp_def]`.

Use linear arithmetic over natural numbers and integers.
-/
private theorem isLocPt_bigPt_of_ne_zero (r : ℕ) (c : Fin (r + 1) → ℂ) (hd : ∀ a, c a ≠ 0) :
    D.IsLocPt (TBB.bigPt r c) (r + 1) := by
  refine ⟨fun b hb => ?_, ?_⟩
  · rw [TBB.bigPt, List.mem_ofFn] at hb
    obtain ⟨l, rfl⟩ := hb
    exact ⟨le_rfl, hd l⟩
  · simp [D.ptSize, TBB.bigPt, List.map_ofFn, Function.comp_def]
    omega

/- English proof (translation)
Unfold `bcWeight`. Use `split_ifs with h`. Establish `h0 : Complex.normSq q.2 - T * T' = 0` using `by linarith`. Rewrite using `[h0, zero_pow (by omega), mul_zero]`. Both sides reduce to the same expression.
-/
private theorem bcWeight_eq_zero_of_normSq_le {k r : ℕ} (hk : 2 ≤ k) (T T' : ℝ) (q : (Fin r → ℂ) × ℂ)
    (hq : Complex.normSq q.2 ≤ T * T') : bcWeight k r T T' q = 0 := by
  unfold bcWeight
  split_ifs with h
  · have h0 : Complex.normSq q.2 - T * T' = 0 := by linarith
    rw [h0, zero_pow (by omega), mul_zero]
  · rfl

/- English proof (translation)
Rewrite using `[Gp_bigPt_eq, Fin.prod_univ_castSucc, Complex.normSq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem gp_bigPt_eq_normSq_prod_mul_sub (p : KB.Pl P Wp Wq) (c : Fin (P.r + 1) → ℂ) :
    TBB.Gp p (TBB.bigPt P.r c) = Complex.normSq (∏ i : Fin P.r, c i.castSucc) *
      (Complex.normSq (c (Fin.last P.r)) - TBB.TTp p) := by
  rw [Gp_bigPt_eq, Fin.prod_univ_castSucc, Complex.normSq_mul]
  ring

/- English proof (translation)
Establish `hloc` using `isLocPt_bigPt_of_ne_zero P.r c hd`. Establish `hTT : TBB.TTp p = Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z'` using `rfl`. Establish `hpos : 0 < Complex.normSq (∏ i : Fin P.r, c i.castSucc)` using `Complex.normSq_pos.2 (Finset.prod_ne_zero_iff.2 fun i _ => hd _)`. Establish `hRR : p.RR F (P.r + 1) [] (TBB.bigPt P.r c) (TBB.bigPt P.r c) = B.hsInner (p.V F (TBB.bigPt P.r c)) (p.V F (TBB.bigPt P.r c))`. Unfold `KB.Pl.RR D.RRplace`.

Rewrite using `[dif_pos ⟨hloc, hloc⟩, dif_neg (by omega), if_pos rfl, if_pos rfl]`. Both sides reduce to the same expression. Establish `hEw : TBB.Ew p (fun _ => 1) F (P.r + 1) [] (TBB.bigPt P.r c) = Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) (TBB.bigPt P.r c)) * Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) (TBB.bigPt P.r c)) * ‖B.hsVec (p.V F (TBB.bigPt P.r c))‖ ^ 2`. Rewrite using `[TBB.Ew, TBB.NP, hRR, B.hsInner, JCTx2.inner_self_real, ← Complex.ofReal_mul, Complex.ofReal_re]`. Simplify using `[TBB.normC]`.

Rewrite using `[hEw]`. Distinguish the cases in `hζ : TBB.TTp p < Complex.normSq (c (Fin.last P.r))`. Establish `hG : 0 < TBB.Gp p (TBB.bigPt P.r c)`. Rewrite using `[gp_bigPt_eq_normSq_prod_mul_sub]`. Conclude with `mul_pos hpos (by linarith)`.

Establish `hn` using `nPt_bigPt P.k P.r (Tz P.k P.r p.T.base.z) (Tz P.k P.r p.T.base.z') c (by rw [← hTT]; exact hζ.le)`. Rewrite using `[hTT, hn, Real.mul_self_sqrt (bcWeight_nonneg0 _ _ _ _ _), hsVec_norm_V_bigPt p F c hd hG]`. Use `replace hζ := not_lt.1 hζ`. Establish `hG : ¬ 0 < TBB.Gp p (TBB.bigPt P.r c)`. Rewrite using `[gp_bigPt_eq_normSq_prod_mul_sub]`.

Introduce `h`. Use `(pos_iff_pos_of_mul_pos h).1 hpos` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hV0 : p.V F (TBB.bigPt P.r c) = 0`. Unfold `KB.Pl.V D.vecV`.

Rewrite using `[dif_neg]`. Conclude with `fun hh => hG hh.2`. Establish `h0 : B.hsVec (0 : Wq →L[ℂ] Wp) = 0`. Simplify using `using JCTx2.hsVec_smul' (0 : ℂ) (0 : Wq →L[ℂ] Wp)`. Rewrite using `[bcWeight_eq_zero_of_normSq_le p.hl.2.2 _ _ _ (by exact hζ), hV0, h0]`.

Simplify using the standard rewrite rules.
-/
theorem ew_eq_weight (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (c : Fin (P.r + 1) → ℂ)
    (hd : ∀ a, c a ≠ 0) :
    TBB.Ew p (fun _ => 1) F (P.r + 1) [] (TBB.bigPt P.r c) =
      bcWeight P.k P.r (Tz P.k P.r p.T.base.z) (Tz P.k P.r p.T.base.z') ((fun j => c j.castSucc), c (Fin.last P.r)) *
        ‖B.hsVec (B.JF p.T.base F (bigCell P.k P.r (fun j => c j.castSucc) (p.T.base.μsec (c (Fin.last P.r)))))‖ ^ 2 := by
  have hloc := isLocPt_bigPt_of_ne_zero P.r c hd
  have hTT : TBB.TTp p = Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z' := rfl
  have hpos : 0 < Complex.normSq (∏ i : Fin P.r, c i.castSucc) :=
    Complex.normSq_pos.2 (Finset.prod_ne_zero_iff.2 fun i _ => hd _)
  have hRR : p.RR F (P.r + 1) [] (TBB.bigPt P.r c) (TBB.bigPt P.r c) =
      B.hsInner (p.V F (TBB.bigPt P.r c)) (p.V F (TBB.bigPt P.r c)) := by
    unfold KB.Pl.RR D.RRplace
    rw [dif_pos ⟨hloc, hloc⟩, dif_neg (by omega), if_pos rfl, if_pos rfl]
    rfl
  have hEw : TBB.Ew p (fun _ => 1) F (P.r + 1) [] (TBB.bigPt P.r c) =
      Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) (TBB.bigPt P.r c)) *
        Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) (TBB.bigPt P.r c)) *
        ‖B.hsVec (p.V F (TBB.bigPt P.r c))‖ ^ 2 := by
    rw [TBB.Ew, TBB.NP, hRR, B.hsInner, JCTx2.inner_self_real, ← Complex.ofReal_mul, Complex.ofReal_re]
    simp [TBB.normC]
  rw [hEw]
  by_cases hζ : TBB.TTp p < Complex.normSq (c (Fin.last P.r))
  · have hG : 0 < TBB.Gp p (TBB.bigPt P.r c) := by
      rw [gp_bigPt_eq_normSq_prod_mul_sub]
      exact mul_pos hpos (by linarith)
    have hn := nPt_bigPt P.k P.r (Tz P.k P.r p.T.base.z) (Tz P.k P.r p.T.base.z') c
      (by rw [← hTT]; exact hζ.le)
    rw [hTT, hn, Real.mul_self_sqrt (bcWeight_nonneg0 _ _ _ _ _), hsVec_norm_V_bigPt p F c hd hG]
  · replace hζ := not_lt.1 hζ
    have hG : ¬ 0 < TBB.Gp p (TBB.bigPt P.r c) := by
      rw [gp_bigPt_eq_normSq_prod_mul_sub]
      intro h
      have := (pos_iff_pos_of_mul_pos h).1 hpos
      linarith
    have hV0 : p.V F (TBB.bigPt P.r c) = 0 := by
      unfold KB.Pl.V D.vecV
      rw [dif_neg]
      exact fun hh => hG hh.2
    have h0 : B.hsVec (0 : Wq →L[ℂ] Wp) = 0 := by
      simpa using JCTx2.hsVec_smul' (0 : ℂ) (0 : Wq →L[ℂ] Wp)
    rw [bcWeight_eq_zero_of_normSq_le p.hl.2.2 _ _ _ (by exact hζ), hV0, h0]
    simp

/- English proof (translation)
Take `⟨cc, -, -, ⟨C, hB1⟩, -⟩` from `Formalism.FourierDecayAlt.P.b_any_of_xi P.k P.r Wp Wq p.T.base A hAB`. Take `⟨c4, hc4⟩` from `hH 4 (by norm_num)`. Establish `hfin : B.normSq p.T.base H ≠ ⊤` using `(hB1 H H c4 c4 (hH 5 le_rfl) (hH 5 le_rfl) hc4 hc4).1`. Use `set g : (Fin P.r → ℂ) × ℂ → ℝ := fun q => bcWeight P.k P.r (Tz P.k P.r p.T.base.z) (Tz P.k P.r p.T.base.z') q * ‖B.hsVec (B.JF p.T.base H (B.gq p.T.base q))‖ ^ 2 with hg`. Establish `hg0 : ∀ q, 0 ≤ g q` using `fun q => mul_nonneg (bcWeight_nonneg0 _ _ _ _ q) (sq_nonneg _)`.

Establish `hmeas : AEStronglyMeasurable g volume`. Establish `hc` using `jgq_continuousOn p.T.base hT (hH 0 (by norm_num))`. Establish `h2 : ContinuousOn (fun q => ‖B.hsVec (B.JF p.T.base H (B.gq p.T.base q))‖ ^ 2) (JF.QDom P.k P.r p.T.base.z p.T.base.z')` using `((JCTx2.hsVec_cont'.comp_continuousOn hc).norm).pow 2`. Simplify `aesm_weight_smul p.T.base h2` using `[hg, smul_eq_mul]`. Establish `hint : Integrable g volume`.

Use `⟨hmeas, ?_⟩` and prove the remaining obligations. Rewrite using `[hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hg0)]`. Establish `hns : B.normSq p.T.base H = ∫⁻ q, ENNReal.ofReal (g q)` using `rfl`. Rewrite using `[← hns]`. Conclude with `lt_top_iff_ne_top.2 hfin`.

Establish `hcomp : Integrable (g ∘ bcE P.r) volume` using `((bcE_mp P.r).integrable_comp_emb (bcE P.r).measurableEmbedding).2 hint`. Use `hcomp.congr ?_` and prove the remaining obligations. Use `filter_upwards [ae_ne_zero_all P.r] with c hc`. Simplify using `only [Function.comp, bcE_apply, hg, B.gq]`. Conclude with `(ew_eq_weight p H c hc).symm`.
-/
theorem ew_integrable (p : KB.Pl P Wp Wq) {A : ℝ} {H : B.Mat P.k P.r → (Wq →L[ℂ] Wp)} (hAB : B.AB P.k P.r ≤ A)
    (hT : JF.TransportedAlt P.k P.r A 0) (hH : ∀ j : ℕ, j ≤ 5 → B.InCC A j H) :
    Integrable (fun c : Fin (P.r + 1) → ℂ => TBB.Ew p (fun _ => 1) H (P.r + 1) [] (TBB.bigPt P.r c)) := by
  obtain ⟨cc, -, -, ⟨C, hB1⟩, -⟩ := Formalism.FourierDecayAlt.P.b_any_of_xi P.k P.r Wp Wq p.T.base A hAB
  obtain ⟨c4, hc4⟩ := hH 4 (by norm_num)
  have hfin : B.normSq p.T.base H ≠ ⊤ := (hB1 H H c4 c4 (hH 5 le_rfl) (hH 5 le_rfl) hc4 hc4).1
  set g : (Fin P.r → ℂ) × ℂ → ℝ := fun q =>
    bcWeight P.k P.r (Tz P.k P.r p.T.base.z) (Tz P.k P.r p.T.base.z') q *
      ‖B.hsVec (B.JF p.T.base H (B.gq p.T.base q))‖ ^ 2 with hg
  have hg0 : ∀ q, 0 ≤ g q := fun q => mul_nonneg (bcWeight_nonneg0 _ _ _ _ q) (sq_nonneg _)
  have hmeas : AEStronglyMeasurable g volume := by
    have hc := jgq_continuousOn p.T.base hT (hH 0 (by norm_num))
    have h2 : ContinuousOn (fun q => ‖B.hsVec (B.JF p.T.base H (B.gq p.T.base q))‖ ^ 2)
        (JF.QDom P.k P.r p.T.base.z p.T.base.z') :=
      ((JCTx2.hsVec_cont'.comp_continuousOn hc).norm).pow 2
    simpa [hg, smul_eq_mul] using aesm_weight_smul p.T.base h2
  have hint : Integrable g volume := by
    refine ⟨hmeas, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hg0)]
    have hns : B.normSq p.T.base H = ∫⁻ q, ENNReal.ofReal (g q) := rfl
    rw [← hns]
    exact lt_top_iff_ne_top.2 hfin
  have hcomp : Integrable (g ∘ bcE P.r) volume :=
    ((bcE_mp P.r).integrable_comp_emb (bcE P.r).measurableEmbedding).2 hint
  refine hcomp.congr ?_
  filter_upwards [ae_ne_zero_all P.r] with c hc
  simp only [Function.comp, bcE_apply, hg, B.gq]
  exact (ew_eq_weight p H c hc).symm

end place

/- English proof (translation)
Establish `hya : 0 ≤ y ^ a * E` using `mul_nonneg (pow_nonneg hy _) hE`. Break down `le_total y 1 with h | h` into its components or cases. Establish `h1 : y ^ (a - b) ≤ 1` using `pow_le_one₀ hy h`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_right h1 hE]`. Establish `h1 : y ^ (a - b) ≤ y ^ a` using `pow_le_pow_right₀ h (Nat.sub_le a b)`.

Use polynomial arithmetic with `[mul_le_mul_of_nonneg_right h1 hE]`.
-/
theorem nf_pow_bound (y : ℝ) (hy : 0 ≤ y) (a b : ℕ) (E : ℝ) (hE : 0 ≤ E) : y ^ (a - b) * E ≤ E + y ^ a * E := by
  have hya : 0 ≤ y ^ a * E := mul_nonneg (pow_nonneg hy _) hE
  rcases le_total y 1 with h | h
  · have h1 : y ^ (a - b) ≤ 1 := pow_le_one₀ hy h
    nlinarith [mul_le_mul_of_nonneg_right h1 hE]
  · have h1 : y ^ (a - b) ≤ y ^ a := pow_le_pow_right₀ h (Nat.sub_le a b)
    nlinarith [mul_le_mul_of_nonneg_right h1 hE]

/- English proof (translation)
Establish `h4 : R ≤ R ^ 4` using `le_self_pow₀ hR1 (by norm_num)`. Establish `h2 : x ≤ x ^ 2` using `le_self_pow₀ hx1 (by norm_num)`. Establish `h3 : x ≤ x ^ 3` using `le_self_pow₀ hx1 (by norm_num)`. Establish `hS : x * (N + 1) ≤ N * x ^ 2 + x ^ 3` using `by nlinarith`. Establish `hx0 : 0 ≤ x * (N + 1)` using `mul_nonneg (by linarith) (by linarith)`.

Establish `hR0 : 0 ≤ R ^ 4` using `by positivity`. Establish `hmain : R * (x * (N + 1)) ≤ R ^ 4 * (N * x ^ 2 + x ^ 3)` using `mul_le_mul h4 hS hx0 hR0`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem nf_arith_d (C₁ R x N : ℝ) (hC₁ : 0 ≤ C₁) (hR1 : 1 ≤ R) (hx1 : 1 ≤ x) (hN0 : 0 ≤ N) :
    C₁ * R * x * (N + 1) ≤ C₁ * (R ^ 4 * (N * x ^ 2 + x ^ 3)) := by
  have h4 : R ≤ R ^ 4 := le_self_pow₀ hR1 (by norm_num)
  have h2 : x ≤ x ^ 2 := le_self_pow₀ hx1 (by norm_num)
  have h3 : x ≤ x ^ 3 := le_self_pow₀ hx1 (by norm_num)
  have hS : x * (N + 1) ≤ N * x ^ 2 + x ^ 3 := by nlinarith
  have hx0 : 0 ≤ x * (N + 1) := mul_nonneg (by linarith) (by linarith)
  have hR0 : 0 ≤ R ^ 4 := by positivity
  have hmain : R * (x * (N + 1)) ≤ R ^ 4 * (N * x ^ 2 + x ^ 3) := mul_le_mul h4 hS hx0 hR0
  calc C₁ * R * x * (N + 1) = C₁ * (R * (x * (N + 1))) := by ring
    _ ≤ C₁ * (R ^ 4 * (N * x ^ 2 + x ^ 3)) := mul_le_mul_of_nonneg_left hmain hC₁

/- English proof (translation)
Establish `h4 : R ≤ R ^ 4` using `le_self_pow₀ hR1 (by norm_num)`. Establish `hx3 : 0 ≤ x ^ 3` using `pow_nonneg (by linarith) 3`. Establish `hNx : 0 ≤ N * x ^ 2` using `mul_nonneg hN0 (sq_nonneg x)`. Establish `hR4 : 0 ≤ R ^ 4` using `by positivity`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_right h4 hx3, mul_nonneg hR4 hNx]`.
-/
theorem nf_arith_low (R x N : ℝ) (hR1 : 1 ≤ R) (hx1 : 1 ≤ x) (hN0 : 0 ≤ N) :
    R * x ^ 3 ≤ R ^ 4 * (N * x ^ 2 + x ^ 3) := by
  have h4 : R ≤ R ^ 4 := le_self_pow₀ hR1 (by norm_num)
  have hx3 : 0 ≤ x ^ 3 := pow_nonneg (by linarith) 3
  have hNx : 0 ≤ N * x ^ 2 := mul_nonneg hN0 (sq_nonneg x)
  have hR4 : 0 ≤ R ^ 4 := by positivity
  nlinarith [mul_le_mul_of_nonneg_right h4 hx3, mul_nonneg hR4 hNx]

/- English proof (translation)
Establish `hs : 3 ≤ 2 * r + k + 1` using `by linarith`. Establish `hs3 : 9 * (2 * r + k + 1) ≤ (2 * r + k + 1) ^ 3`. Use polynomial arithmetic with `[mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * r + k + 1) (by linarith : (0 : ℝ) ≤ 2 * r + k + 1 - 3)) (by linarith : (0 : ℝ) ≤ 2 * r + k + 1 + 3)]`. Establish `h1 : (r + 1) * (9 * (2 * r + k + 1)) ≤ (r + 1) * (2 * r + k + 1) ^ 3` using `mul_le_mul_of_nonneg_left hs3 (by linarith)`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left (by linarith : k + r ≤ 2 * r + k + 1) (by linarith : (0 : ℝ) ≤ r + 1)]`.
-/
theorem nf_arith_ab (r k : ℝ) (hr : 0 ≤ r) (hk : 2 ≤ k) :
    2 * (k + r) * (r + 1) + 1 ≤ 20 * ((r + 1) * (2 * r + k + 1) ^ 3) := by
  have hs : 3 ≤ 2 * r + k + 1 := by linarith
  have hs3 : 9 * (2 * r + k + 1) ≤ (2 * r + k + 1) ^ 3 := by
    nlinarith [mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * r + k + 1)
      (by linarith : (0 : ℝ) ≤ 2 * r + k + 1 - 3)) (by linarith : (0 : ℝ) ≤ 2 * r + k + 1 + 3)]
  have h1 : (r + 1) * (9 * (2 * r + k + 1)) ≤ (r + 1) * (2 * r + k + 1) ^ 3 :=
    mul_le_mul_of_nonneg_left hs3 (by linarith)
  nlinarith [mul_le_mul_of_nonneg_left (by linarith : k + r ≤ 2 * r + k + 1) (by linarith : (0 : ℝ) ≤ r + 1)]

/- English proof (translation)
Establish `hx2 : 0 < R * x ^ 2` using `mul_pos (by linarith) (pow_pos (by linarith) 2)`. Use polynomial arithmetic with `[mul_lt_mul_of_pos_left (by linarith : (9 : ℝ) < 20 * x) hx2]`.
-/
theorem nf_arith_thr (R x : ℝ) (hR1 : 1 ≤ R) (hx1 : 1 ≤ x) : x ^ 2 * (9 * R) < 20 * (R * x ^ 3) := by
  have hx2 : 0 < R * x ^ 2 := mul_pos (by linarith) (pow_pos (by linarith) 2)
  nlinarith [mul_lt_mul_of_pos_left (by linarith : (9 : ℝ) < 20 * x) hx2]

/- English proof (translation)
Rewrite using `[ew_eq_weight p _ c hd, ew_eq_weight p H c hd, JCTx2.JF_cutF, JCTx2.hsVec_smul', norm_smul]`. Distinguish the cases in `hζ : TBB.TTp p < Complex.normSq (c (Fin.last P.r))`. Establish `hGf : Gf P.k P.r p.T.base.z p.T.base.z' (bigCell P.k P.r (fun j => c j.castSucc) (p.T.base.μsec (c (Fin.last P.r)))) = TBB.Gp p (TBB.bigPt P.r c)`. Conclude with `TBBx2.Gf_of_Zhat _ _ _ (TBB.bigPt P.r c) (by exact PBM.zhat_bigCell_pt p.T.base c hζ)`. Simplify using `only [div_one]`.

Rewrite using `[hGf, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_pow]`. Expand and normalize the polynomial expressions, which then agree. Use `replace hζ := not_lt.1 hζ`. Rewrite using `[bcWeight_eq_zero_of_normSq_le p.hl.2.2 _ _ _ (by exact hζ)]`. Simplify using the standard rewrite rules.
-/
private theorem ew_cutF_pow_bigPt_eq_norm_gp_pow_mul {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (p : KB.Pl P Wp Wq) (H : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (q₀ : ℕ) (c : Fin (P.r + 1) → ℂ)
    (hd : ∀ a, c a ≠ 0) :
    TBB.Ew p (fun _ => 1) (D.cutF p.T.base (fun x => x ^ q₀) H 1) (P.r + 1) [] (TBB.bigPt P.r c) =
      ‖TBB.Gp p (TBB.bigPt P.r c)‖ ^ (2 * q₀) * TBB.Ew p (fun _ => 1) H (P.r + 1) [] (TBB.bigPt P.r c) := by
  rw [ew_eq_weight p _ c hd, ew_eq_weight p H c hd, JCTx2.JF_cutF, JCTx2.hsVec_smul', norm_smul]
  by_cases hζ : TBB.TTp p < Complex.normSq (c (Fin.last P.r))
  · have hGf : Gf P.k P.r p.T.base.z p.T.base.z'
        (bigCell P.k P.r (fun j => c j.castSucc) (p.T.base.μsec (c (Fin.last P.r)))) =
          TBB.Gp p (TBB.bigPt P.r c) := by
      exact TBBx2.Gf_of_Zhat _ _ _ (TBB.bigPt P.r c) (by exact PBM.zhat_bigCell_pt p.T.base c hζ)
    simp only [div_one]
    rw [hGf, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_pow]
    ring
  · replace hζ := not_lt.1 hζ
    rw [bcWeight_eq_zero_of_normSq_le p.hl.2.2 _ _ _ (by exact hζ)]
    simp

/- English proof (translation)
Introduce `Cb C₁`. Use `⟨C₁ + 20, ?_⟩` and prove the remaining obligations. Introduce `Wp Wq _ _ _ _ _ _ P p f A₀ p₀ χ N hN Th hTh`. Take `⟨-, -, hCk, hCC, hbud, -⟩` from `hN`. Take `⟨-, -, hglob, hord⟩` from `hTh`.

Establish `hk : (2 : ℝ) ≤ P.k` using `by exact_mod_cast p.hl.2.2`. Establish `hr0 : (0 : ℝ) ≤ P.r` using `Nat.cast_nonneg _`. Establish `hx : CutMP.nDim P.k P.r = (2 * (P.r : ℝ) + P.k + 1)` using `by unfold CutMP.nDim; push_cast; ring`. Establish `hR1 : (1 : ℝ) ≤ ((P.r : ℝ) + 1)` using `by linarith`. Establish `hx1 : (1 : ℝ) ≤ (2 * (P.r : ℝ) + P.k + 1)` using `by linarith`.

Establish `hN0 : (0 : ℝ) ≤ N` using `Nat.cast_nonneg N`. Establish `hC₁ : 0 ≤ C₁`. Assume the negation of the conclusion as `h`. Establish `h1 : (0 : ℝ) < CutMP.nDim P.k P.r * ((N : ℝ) + 1)` using `by rw [hx]; positivity`. Establish `h2 : C₁ * CutMP.nDim P.k P.r * ((N : ℝ) + 1) < 0`.

Rewrite using `[mul_assoc]`. Conclude with `mul_neg_of_neg_of_pos (not_le.1 h) h1`. Establish `h3 : (0 : ℝ) ≤ (B.opOrder Th : ℝ)` using `Nat.cast_nonneg _`. Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨d, hd⟩ : ∃ d : ℝ, d = C₁ * ((P.r : ℝ) + 1) * CutMP.nDim P.k P.r * ((N : ℝ) + 1)` from `⟨_, rfl⟩`.

Rewrite `hglob` using `[← hd]`. Establish `hd0 : 0 ≤ d`. Rewrite using `[hd, hx]`. Conclude with `mul_nonneg (mul_nonneg (mul_nonneg hC₁ (by linarith)) (by linarith)) (by linarith)`. Establish `hdS : d ≤ C₁ * (((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3))`.

Rewrite using `[hd, hx]`. Conclude with `nf_arith_d C₁ _ _ _ hC₁ hR1 hx1 hN0`. Establish `hM0 : (0 : ℝ) ≤ (((2 * P.r + 2) * p₀ : ℕ) : ℝ)` using `Nat.cast_nonneg _`. Establish `e1 : (C₁ + 20) * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) = C₁ * (((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3)) + 20 * (((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k …` using `by ring`. Establish `hlow` using `nf_arith_low ((P.r : ℝ) + 1) (2 * (P.r : ℝ) + P.k + 1) N hR1 hx1 hN0`.

Establish `hab` using `nf_arith_ab (P.r : ℝ) (P.k : ℝ) hr0 hk`. Establish `hthr` using `nf_arith_thr ((P.r : ℝ) + 1) (2 * (P.r : ℝ) + P.k + 1) hR1 hx1`. Establish `hA2 : 20 * (((P.r : ℝ) + 1) * (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A₀ - d - (((2 * P.r + 2) * p₀ : ℕ) : ℝ)` using `by linarith`. Establish `hAB2 : B.AB P.k P.r ≤ A₀ - d - (((2 * P.r + 2) * p₀ : ℕ) : ℝ)` using `by unfold B.AB; linarith`. Establish `hAB1 : B.AB P.k P.r ≤ A₀ - d` using `by linarith`.

Establish `hMc : (((2 * P.r + 2) * p₀ : ℕ) : ℝ) = (2 * (P.r : ℝ) + 2) * p₀` using `by push_cast; ring`. Establish `hT2 : JF.TransportedAlt P.k P.r (A₀ - d - (((2 * P.r + 2) * p₀ : ℕ) : ℝ)) 0`. Unfold `JF.TransportedAlt`. Rewrite using `[lt_div_iff₀ (by positivity)]`. Use `push_cast`.

Combine the linear relations using `[hMc]`. Establish `hT1 : JF.TransportedAlt P.k P.r (A₀ - d) 0`. Unfold `JF.TransportedAlt`. Rewrite using `[lt_div_iff₀ (by positivity)]`. Use `push_cast`.

Combine the linear relations using `[hMc]`. Take `⟨-, hH1⟩` from `CutMP.class_lower_decay_holds P.k P.r Wp Wq Th d A₀ hd0 hglob f hCk hCC`. Establish `hH2 : ∀ m : ℕ, B.InCC (A₀ - d - (((2 * P.r + 2) * p₀ : ℕ) : ℝ)) m (D.cutF p.T.base (fun x => x ^ p₀) (B.opApply Th f) 1)`. Establish `heq : D.cutF p.T.base (fun x => x ^ p₀) (B.opApply Th f) 1 = fun g => ((Gf P.k P.r p.T.base.z p.T.base.z' g ^ p₀ : ℝ) : ℂ) • B.opApply Th f g`. Use function extensionality and compare the values at `g`.

Simplify using `[D.cutF]`. Rewrite using `[heq]`. Conclude with `inCC_Gpow_smul _ _ p₀ hH1`. Establish `I1` using `ew_integrable p hAB1 hT1 (fun j _ => hH1 j)`. Establish `I2` using `ew_integrable p hAB2 hT2 (fun j _ => hH2 j)`.

Establish `hkey : ∀ᵐ c : Fin (P.r + 1) → ℂ, TBB.Ew p (fun _ => 1) (D.cutF p.T.base (fun x => x ^ p₀) (B.opApply Th f) 1) (P.r + 1) [] (TBB.bigPt P.r c) = ‖TBB.Gp p (TBB.bigPt P.r c)‖ ^ (2 * p₀) * TBB.Ew p (fun _ => 1) (B.opApply Th f) (P.r + 1) [] (TBB.bigPt P.r c)` using `by filter_upwards [ae_ne_zero_all P.r] with c hc`. Conclude with `ew_cutF_pow_bigPt_eq_norm_gp_pow_mul p _ p₀ c hc`. Establish `hnn : ∀ᵐ c : Fin (P.r + 1) → ℂ, 0 ≤ TBB.Ew p (fun _ => 1) (B.opApply Th f) (P.r + 1) [] (TBB.bigPt P.r c)` using `by filter_upwards [ae_ne_zero_all P.r] with c hc`. Rewrite using `[ew_eq_weight p _ c hc]`. Conclude with `mul_nonneg (bcWeight_nonneg0 _ _ _ _ _) (sq_nonneg _)`.

Use `Integrable.mono' (I1.add I2) ?_ ?_` and prove the remaining obligations. Conclude with `((Gp_bigPt_continuous p).norm.pow _).aestronglyMeasurable.mul I1.aestronglyMeasurable`. Use `filter_upwards [hkey, hnn] with c h1 h2`. Rewrite using `[Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (pow_nonneg (norm_nonneg _) _) h2), Pi.add_apply, h1]`. Conclude with `nf_pow_bound _ (norm_nonneg _) _ _ _ h2`.
-/
theorem dominated_L2_operator_bound_holds : DominatedL2OperatorBound := by
  intro Cb C₁
  refine ⟨C₁ + 20, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p f A₀ p₀ χ N hN Th hTh
  obtain ⟨-, -, hCk, hCC, hbud, -⟩ := hN
  obtain ⟨-, -, hglob, hord⟩ := hTh
  have hk : (2 : ℝ) ≤ P.k := by exact_mod_cast p.hl.2.2
  have hr0 : (0 : ℝ) ≤ P.r := Nat.cast_nonneg _
  have hx : CutMP.nDim P.k P.r = (2 * (P.r : ℝ) + P.k + 1) := by unfold CutMP.nDim; push_cast; ring
  have hR1 : (1 : ℝ) ≤ ((P.r : ℝ) + 1) := by linarith
  have hx1 : (1 : ℝ) ≤ (2 * (P.r : ℝ) + P.k + 1) := by linarith
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hC₁ : 0 ≤ C₁ := by
    by_contra h
    have h1 : (0 : ℝ) < CutMP.nDim P.k P.r * ((N : ℝ) + 1) := by rw [hx]; positivity
    have h2 : C₁ * CutMP.nDim P.k P.r * ((N : ℝ) + 1) < 0 := by
      rw [mul_assoc]; exact mul_neg_of_neg_of_pos (not_le.1 h) h1
    have h3 : (0 : ℝ) ≤ (B.opOrder Th : ℝ) := Nat.cast_nonneg _
    linarith
  obtain ⟨d, hd⟩ : ∃ d : ℝ, d = C₁ * ((P.r : ℝ) + 1) * CutMP.nDim P.k P.r * ((N : ℝ) + 1) := ⟨_, rfl⟩
  rw [← hd] at hglob
  have hd0 : 0 ≤ d := by
    rw [hd, hx]
    exact mul_nonneg (mul_nonneg (mul_nonneg hC₁ (by linarith)) (by linarith)) (by linarith)
  have hdS : d ≤ C₁ * (((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3)) := by
    rw [hd, hx]; exact nf_arith_d C₁ _ _ _ hC₁ hR1 hx1 hN0
  have hM0 : (0 : ℝ) ≤ (((2 * P.r + 2) * p₀ : ℕ) : ℝ) := Nat.cast_nonneg _
  have e1 : (C₁ + 20) * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) = C₁ * (((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3)) + 20 * (((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3)) := by ring
  have hlow := nf_arith_low ((P.r : ℝ) + 1) (2 * (P.r : ℝ) + P.k + 1) N hR1 hx1 hN0
  have hab := nf_arith_ab (P.r : ℝ) (P.k : ℝ) hr0 hk
  have hthr := nf_arith_thr ((P.r : ℝ) + 1) (2 * (P.r : ℝ) + P.k + 1) hR1 hx1
  have hA2 : 20 * (((P.r : ℝ) + 1) * (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A₀ - d - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) := by linarith
  have hAB2 : B.AB P.k P.r ≤ A₀ - d - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) := by unfold B.AB; linarith
  have hAB1 : B.AB P.k P.r ≤ A₀ - d := by linarith
  have hMc : (((2 * P.r + 2) * p₀ : ℕ) : ℝ) = (2 * (P.r : ℝ) + 2) * p₀ := by push_cast; ring
  have hT2 : JF.TransportedAlt P.k P.r (A₀ - d - (((2 * P.r + 2) * p₀ : ℕ) : ℝ)) 0 := by
    unfold JF.TransportedAlt
    rw [lt_div_iff₀ (by positivity)]
    push_cast
    linarith [hMc]
  have hT1 : JF.TransportedAlt P.k P.r (A₀ - d) 0 := by
    unfold JF.TransportedAlt
    rw [lt_div_iff₀ (by positivity)]
    push_cast
    linarith [hMc]
  obtain ⟨-, hH1⟩ := CutMP.class_lower_decay_holds P.k P.r Wp Wq Th d A₀ hd0 hglob f hCk hCC
  have hH2 : ∀ m : ℕ, B.InCC (A₀ - d - (((2 * P.r + 2) * p₀ : ℕ) : ℝ)) m (D.cutF p.T.base (fun x => x ^ p₀) (B.opApply Th f) 1) := by
    have heq : D.cutF p.T.base (fun x => x ^ p₀) (B.opApply Th f) 1 =
        fun g => ((Gf P.k P.r p.T.base.z p.T.base.z' g ^ p₀ : ℝ) : ℂ) • B.opApply Th f g := by
      funext g; simp [D.cutF]
    rw [heq]
    exact inCC_Gpow_smul _ _ p₀ hH1
  have I1 := ew_integrable p hAB1 hT1 (fun j _ => hH1 j)
  have I2 := ew_integrable p hAB2 hT2 (fun j _ => hH2 j)
  have hkey : ∀ᵐ c : Fin (P.r + 1) → ℂ,
      TBB.Ew p (fun _ => 1) (D.cutF p.T.base (fun x => x ^ p₀) (B.opApply Th f) 1) (P.r + 1) []
          (TBB.bigPt P.r c) =
        ‖TBB.Gp p (TBB.bigPt P.r c)‖ ^ (2 * p₀) *
          TBB.Ew p (fun _ => 1) (B.opApply Th f) (P.r + 1) [] (TBB.bigPt P.r c) := by
    filter_upwards [ae_ne_zero_all P.r] with c hc
    exact ew_cutF_pow_bigPt_eq_norm_gp_pow_mul p _ p₀ c hc
  have hnn : ∀ᵐ c : Fin (P.r + 1) → ℂ,
      0 ≤ TBB.Ew p (fun _ => 1) (B.opApply Th f) (P.r + 1) [] (TBB.bigPt P.r c) := by
    filter_upwards [ae_ne_zero_all P.r] with c hc
    rw [ew_eq_weight p _ c hc]
    exact mul_nonneg (bcWeight_nonneg0 _ _ _ _ _) (sq_nonneg _)
  refine Integrable.mono' (I1.add I2) ?_ ?_
  · exact ((Gp_bigPt_continuous p).norm.pow _).aestronglyMeasurable.mul I1.aestronglyMeasurable
  · filter_upwards [hkey, hnn] with c h1 h2
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (pow_nonneg (norm_nonneg _) _) h2), Pi.add_apply, h1]
    exact nf_pow_bound _ (norm_nonneg _) _ _ _ h2

end

end Formalism.FourierDecayAlt.P.CutBP
