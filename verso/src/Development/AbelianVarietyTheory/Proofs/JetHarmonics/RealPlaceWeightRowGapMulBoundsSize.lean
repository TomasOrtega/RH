import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.DepthNumbersThresholdEq
import Development.AbelianVarietyTheory.Definitions.Jets.CmQuadraticFormEqAlternatingForm
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.LocalToGlobal.LatticeGeometry.CmTypeMeetsConjugatePair
import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.OrientationExclusive

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GoodDepth.Gap

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.FormalSeriesBounds GlobalTheory.GoodDepth GlobalTheory.RunDepth

variable {D : D7}

/- English proof (translation)
The claim follows from `D.eTau.injective (Subtype.ext ((factEmb D.R D.host).1.1 h))`.
-/
theorem emb_inj {t t' : D.what₂.Tau} (h : DV.tauEmb D t = DV.tauEmb D t') : t = t' :=
  D.eTau.injective (Subtype.ext ((factEmb D.R D.host).1.1 h))

/- English proof (translation)
Introduce `h`. Establish `h1 : ReciprocityTheory.ChartRestriction.G.Geo.Tor.conjEmb (DV.tauEmb D t') = D.host.emb (((D.eTau t' : D.R.Psi) : D.R.GG) * D.R.cc)`. Rewrite using `[Formalism.L2.Geo.emb_mul_cc_comp]`. Use `RingHom.ext fun x => ?_` and prove the remaining obligations. Conclude with `(Formalism.MainNotions.WeightFamilies.emb_conj D (DV.tauEmb D t') x).symm`.

Establish `h2` using `(Formalism.L2.Geo.exists_tauEmb_iff D _).1 ⟨t, (h.trans h1).symm⟩`. Conclude with `(Formalism.L2.Geo.mem_Psi_iff_mul_cc_notMem _).1 (D.eTau t').2 h2`.
-/
theorem emb_ne_conj (t t' : D.what₂.Tau) :
    DV.tauEmb D t ≠ ReciprocityTheory.ChartRestriction.G.Geo.Tor.conjEmb (DV.tauEmb D t') := by
  intro h
  have h1 : ReciprocityTheory.ChartRestriction.G.Geo.Tor.conjEmb (DV.tauEmb D t') =
      D.host.emb (((D.eTau t' : D.R.Psi) : D.R.GG) * D.R.cc) := by
    rw [Formalism.L2.Geo.emb_mul_cc_comp]
    refine RingHom.ext fun x => ?_
    exact (Formalism.MainNotions.WeightFamilies.emb_conj D (DV.tauEmb D t') x).symm
  have h2 := (Formalism.L2.Geo.exists_tauEmb_iff D _).1 ⟨t, (h.trans h1).symm⟩
  exact (Formalism.L2.Geo.mem_Psi_iff_mul_cc_notMem _).1 (D.eTau t').2 h2

/- English proof (translation)
Unfold `wtA`. Rewrite using `[Finset.sum_eq_single t]`. Simplify using `[emb_ne_conj]`. Introduce `t' _ ht'`. Establish `: DV.tauEmb D t ≠ DV.tauEmb D t'` using `fun h => ht' (emb_inj h).symm`.

Simplify using `[emb_ne_conj, this]`. Simplify using the standard rewrite rules.
-/
theorem wtA_emb {j : ℕ} (w : WeightFamilies.Wt D j) (t : D.what₂.Tau) (i : ℕ) :
    wtA w (DV.tauEmb D t, i) = ext0 (w.aP t) i := by
  classical
  unfold wtA
  rw [Finset.sum_eq_single t]
  · simp [emb_ne_conj]
  · intro t' _ ht'
    have : DV.tauEmb D t ≠ DV.tauEmb D t' := fun h => ht' (emb_inj h).symm
    simp [emb_ne_conj, this]
  · simp

/- English proof (translation)
Establish `hT0 : 0 < T` using `by linarith`. Establish `htη0 : 0 < t * η` using `mul_pos (by linarith) (by linarith)`. Establish `h4 : t * η * x ≤ w2` using `(le_div_iff₀ (by linarith)).1 h3`. Establish `h5 : t * η ≤ w` using `by nlinarith`. Prove the components needed by the constructor for the conclusion.

Establish `e : (1 - (Dd + 4) / T) * w = (T - Dd - 4) * w / T` using `by field_simp; ring`. Rewrite using `[e, div_le_iff₀ hT0]`. Establish `a1 : (T - Dd - 2) * (w - η - (T + Dd + 2)) ≤ (T - Dd - 2) * ((T + Dd + 2) * G)` using `mul_le_mul_of_nonneg_left (by linarith) (by linarith)`. Establish `a2 : 0 ≤ (Dd + 2) ^ 2 * G` using `by positivity`. Establish `a3 : T * η ≤ t * η` using `mul_le_mul_of_nonneg_right hTt (by linarith)`.

Establish `a4 : T * T ≤ t * η` using `mul_le_mul hTt (by linarith) hT0.le (by linarith)`. Establish `a5 : 0 ≤ (Dd + 2) * η` using `mul_nonneg (by linarith) (by linarith)`. Establish `a6 : 0 ≤ (Dd + 2) ^ 2` using `by positivity`. Use the polynomial consequences of the given equalities and inequalities. Establish `a1 : 0 ≤ (Dd + 2) * G` using `by positivity`.

Use the polynomial consequences of the given equalities and inequalities.
-/
theorem real_bounds {T Dd G y w η t S S' η' w2 x : ℝ} (hT : 40 * (Dd + 2) ≤ T) (hD : 0 ≤ Dd) (hG : 0 ≤ G)
    (h1 : (T + Dd + 2) * G ≤ y) (h2 : y < (T + Dd + 2) * (G + 1)) (hy1 : w - η ≤ y) (hy2 : y ≤ S + w + η + 1)
    (hTt : T ≤ t) (htη : t ≤ η) (h3 : t * η ≤ w2 / x) (hx : 1 < x) (hw : w2 ≤ w)
    (hS : S ≤ 2 * S') (hS' : 0 ≤ S') (hη : η ≤ 2 * η') :
    (1 - (Dd + 4) / T) * w ≤ T * G ∧ T * G ≤ w + 100 * (S' + η') := by
  have hT0 : 0 < T := by linarith
  have htη0 : 0 < t * η := mul_pos (by linarith) (by linarith)
  have h4 : t * η * x ≤ w2 := (le_div_iff₀ (by linarith)).1 h3
  have h5 : t * η ≤ w := by nlinarith
  constructor
  · have e : (1 - (Dd + 4) / T) * w = (T - Dd - 4) * w / T := by field_simp; ring
    rw [e, div_le_iff₀ hT0]
    have a1 : (T - Dd - 2) * (w - η - (T + Dd + 2)) ≤ (T - Dd - 2) * ((T + Dd + 2) * G) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    have a2 : 0 ≤ (Dd + 2) ^ 2 * G := by positivity
    have a3 : T * η ≤ t * η := mul_le_mul_of_nonneg_right hTt (by linarith)
    have a4 : T * T ≤ t * η := mul_le_mul hTt (by linarith) hT0.le (by linarith)
    have a5 : 0 ≤ (Dd + 2) * η := mul_nonneg (by linarith) (by linarith)
    have a6 : 0 ≤ (Dd + 2) ^ 2 := by positivity
    nlinarith
  · have a1 : 0 ≤ (Dd + 2) * G := by positivity
    nlinarith

/- English proof (translation)
Establish `h1 : (1 : ℝ) ≤ (⌊a⌋₊ : ℝ)` using `by exact_mod_cast (Nat.one_le_floor_iff a).2 h`. Establish `h2` using `Nat.lt_floor_add_one a`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem le_two_floor {a : ℝ} (h : 1 ≤ a) : a ≤ 2 * (⌊a⌋₊ : ℝ) := by
  have h1 : (1 : ℝ) ≤ (⌊a⌋₊ : ℝ) := by exact_mod_cast (Nat.one_le_floor_iff a).2 h
  have h2 := Nat.lt_floor_add_one a
  linarith

variable {L : SizeData₂ D} {Pm : ParameterChoice' D L}

/- English proof (translation)
Unfold `WeightAlgebra.gapZ`. Rewrite using `[dif_pos h2]`. Prove the components needed by the constructor for the conclusion. Use `(kaR Tp hK j).aPlus_antitone τ (show (⟨D.R.k - 2, h1⟩ : Fin _) ≤ ⟨D.R.k - 2 + 1, h2⟩ from Nat.le_succ _)` as an intermediate fact. Establish `h3 : (((kaR Tp hK j).aP τ ⟨D.R.k - 2 + 1, h2⟩ : ℕ) : ℤ) ≤ (kaR Tp hK j).aP τ ⟨D.R.k - 2, h1⟩`.

Conclude with `this` after adjusting the coercions. Conclude with `sub_nonneg.2 h3`. Unfold `kaR`. Rewrite using `[kaWt_big D hK _ j hj.1 hj.2, kaWt_big D hK _ j hj.1 hj.2, Int.cast_sub, (hK j hj.1 hj.2 τ).1, (hK j hj.1 hj.2 τ).1, DV.aPlusQ_eq, DV.aPlusQ_eq]`. Establish `e0 : D.R.k - 2 + 1 - (D.R.k - 1) = 0` using `by omega`.

Establish `s1 : DV.sigPar D τ (D.R.k - 2) = (D.hc τ).v ⟨D.R.k - 2, hv⟩`. Unfold `DV.sigPar`. Rewrite using `[dif_pos hv]`. Establish `s2 : DV.sigPar D τ (D.R.k - 2 + 1) = -(D.hc τ).b ⟨0, hm⟩`. Unfold `DV.sigPar`.

Rewrite using `[dif_neg (by omega), dif_pos (by omega)]`. Use `congr 2`. Conclude with `Fin.ext e0`. Simplify using `only [s1, s2]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem gap_kappa (Tp : ParamsT D L Pm) (hK : DV.KapDef D) {j : ℕ} (hj : InR D j) (τ : D.what₂.Tau)
    (h1 : D.R.k - 2 < (D.R.sigW j).1) (h2 : D.R.k - 2 + 1 < (D.R.sigW j).1) (hv : D.R.k - 2 < D.R.k - 1) (hm : 0 < D.R.m) :
    0 ≤ WeightAlgebra.gapZ ((kaR Tp hK j).aP τ) ⟨D.R.k - 2, h1⟩ ∧
    ((WeightAlgebra.gapZ ((kaR Tp hK j).aP τ) ⟨D.R.k - 2, h1⟩ : ℤ) : ℚ) = (D.hc τ).v ⟨D.R.k - 2, hv⟩ + (D.hc τ).b ⟨0, hm⟩ - 1 := by
  unfold WeightAlgebra.gapZ
  rw [dif_pos h2]
  constructor
  · have := (kaR Tp hK j).aPlus_antitone τ (show (⟨D.R.k - 2, h1⟩ : Fin _) ≤ ⟨D.R.k - 2 + 1, h2⟩ from Nat.le_succ _)
    have h3 : (((kaR Tp hK j).aP τ ⟨D.R.k - 2 + 1, h2⟩ : ℕ) : ℤ) ≤ (kaR Tp hK j).aP τ ⟨D.R.k - 2, h1⟩ := by
      exact_mod_cast this
    exact sub_nonneg.2 h3
  · unfold kaR
    rw [kaWt_big D hK _ j hj.1 hj.2, kaWt_big D hK _ j hj.1 hj.2, Int.cast_sub, (hK j hj.1 hj.2 τ).1,
      (hK j hj.1 hj.2 τ).1, DV.aPlusQ_eq, DV.aPlusQ_eq]
    have e0 : D.R.k - 2 + 1 - (D.R.k - 1) = 0 := by omega
    have s1 : DV.sigPar D τ (D.R.k - 2) = (D.hc τ).v ⟨D.R.k - 2, hv⟩ := by
      unfold DV.sigPar; rw [dif_pos hv]
    have s2 : DV.sigPar D τ (D.R.k - 2 + 1) = -(D.hc τ).b ⟨0, hm⟩ := by
      unfold DV.sigPar
      rw [dif_neg (by omega), dif_pos (by omega)]
      congr 2
      exact Fin.ext e0
    simp only [s1, s2]
    push_cast
    ring

/- English proof (translation)
Establish `e : D.R.k - 1 = D.R.k - 2 + 1` using `by omega`. Use `show wtA (lR Tp hK j) (DV.tauEmb D (plOf D z), D.R.k - 2) - wtA (lR Tp hK j) (DV.tauEmb D (plOf D z), D.R.k - 1) = _`. Rewrite using `[wtA_emb, wtA_emb, e]`. Unfold `ext0`. Rewrite using `[dif_pos h1, dif_pos h2]`.

Use `show ofGaps (lGapP D (kaR Tp hK j) Tp.TO Tp.nWn (plOf D z)) ⟨D.R.k - 2, h1⟩ - ofGaps (lGapP D (kaR Tp hK j) Tp.TO Tp.nWn (plOf D z)) ⟨D.R.k - 2 + 1, h2⟩ = _`. Rewrite using `[ofGaps_succ _ ⟨D.R.k - 2, h1⟩ h2, Nat.add_sub_cancel]`. Unfold `lGapP`. Rewrite using `[if_pos h2]`.
-/
theorem gapW_eq (Tp : ParamsT D L Pm) (hK : DV.KapDef D) {j : ℕ} (z : RPl D.R)
    (h1 : D.R.k - 2 < (D.R.sigW j).1) (h2 : D.R.k - 2 + 1 < (D.R.sigW j).1) (hk : 2 ≤ D.R.k) :
    gapW (numOf D L) (fun z => DV.tauEmb D (plOf D z)) (wtA (lR Tp hK j)) z =
      (Int.fdiv (WeightAlgebra.gapZ ((kaR Tp hK j).aP (plOf D z)) ⟨D.R.k - 2, h1⟩ + 2) (WeightAlgebra.Tp D j Tp.TO)).toNat := by
  have e : D.R.k - 1 = D.R.k - 2 + 1 := by omega
  show wtA (lR Tp hK j) (DV.tauEmb D (plOf D z), D.R.k - 2) - wtA (lR Tp hK j) (DV.tauEmb D (plOf D z), D.R.k - 1) = _
  rw [wtA_emb, wtA_emb, e]
  unfold ext0
  rw [dif_pos h1, dif_pos h2]
  show ofGaps (lGapP D (kaR Tp hK j) Tp.TO Tp.nWn (plOf D z)) ⟨D.R.k - 2, h1⟩ -
    ofGaps (lGapP D (kaR Tp hK j) Tp.TO Tp.nWn (plOf D z)) ⟨D.R.k - 2 + 1, h2⟩ = _
  rw [ofGaps_succ _ ⟨D.R.k - 2, h1⟩ h2, Nat.add_sub_cancel]
  unfold lGapP
  rw [if_pos h2]

/- English proof (translation)
Establish `a1` using `Tp.split`. Establish `a2` using `Tp.nP_eq`. Establish `a4` using `Tp.nW_40`. Establish `hf : 1 ≤ D.R.f`. Establish `h0 : 0 < D.R.toFrame.ord` using `D.R.toFrame.ord_pos`.

Establish `h1 : D.R.f = 2 * D.R.toFrame.ord` using `rfl`. Use linear arithmetic over natural numbers and integers. Establish `a5 : Tp.TO * 1 ≤ Tp.TO * Tp.nWn` using `Nat.mul_le_mul_left _ (by omega)`. Establish `a6 : 1 * D.R.r ≤ 8 * D.R.f * D.R.r` using `Nat.mul_le_mul_right _ (by omega)`. Use linear arithmetic over natural numbers and integers.
-/
theorem TO_le_t (Tp : ParamsT D L Pm) : Tp.TO ≤ D.R.t := by
  have a1 := Tp.split
  have a2 := Tp.nP_eq
  have a4 := Tp.nW_40
  have hf : 1 ≤ D.R.f := by
    have h0 : 0 < D.R.toFrame.ord := D.R.toFrame.ord_pos
    have h1 : D.R.f = 2 * D.R.toFrame.ord := rfl
    omega
  have a5 : Tp.TO * 1 ≤ Tp.TO * Tp.nWn := Nat.mul_le_mul_left _ (by omega)
  have a6 : 1 * D.R.r ≤ 8 * D.R.f * D.R.r := Nat.mul_le_mul_right _ (by omega)
  omega

/- English proof (translation)
Introduce `D L Pm Tp hK j hj z hw`. Establish `hj1` using `hj.1`. Establish `hj2` using `hj.2`. Establish `hk : 5 ≤ D.R.k` using `by have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega`. Establish `hs : (D.R.sigW j).1 = D.R.k + j - 1` using `rfl`.

Establish `h1 : D.R.k - 2 < (D.R.sigW j).1` using `by omega`. Establish `h2 : D.R.k - 2 + 1 < (D.R.sigW j).1` using `by omega`. Establish `hv : D.R.k - 2 < D.R.k - 1` using `by omega`. Establish `hm : 0 < D.R.m` using `by omega`. Establish `hjm : j - 1 < D.R.m` using `by omega`.

Rewrite using `[gapW_eq Tp hK z h1 h2 (by omega)]`. Take `⟨g0, g1⟩` from `gap_kappa Tp hK hj (plOf D z) h1 h2 hv hm`. Generalize the expression as in `WeightAlgebra.gapZ ((kaR Tp hK j).aP (plOf D z)) ⟨D.R.k - 2, h1⟩ = c at g0 g1 ⊢`. Establish `hT' : WeightAlgebra.Tp D j Tp.TO = Tp.TO + Tp.Dp + 2`. Unfold `WeightAlgebra.Tp`.

Rewrite using `[GlobalTheory.DepthBoundProbe.dimY_eq Tp hj]`. Rewrite using `[hT', Int.fdiv_eq_ediv_of_nonneg _ (Nat.cast_nonneg _)]`. Establish `hpos : (0 : ℤ) < ((Tp.TO + Tp.Dp + 2 : ℕ) : ℤ)` using `by positivity`. Establish `q0 : 0 ≤ (c + 2) / ((Tp.TO + Tp.Dp + 2 : ℕ) : ℤ)` using `Int.ediv_nonneg (by omega) hpos.le`. Establish `q1` using `Int.mul_ediv_self_le (x := c + 2) hpos.ne'`.

Establish `q2` using `Int.lt_mul_ediv_self_add (x := c + 2) hpos`. Establish `q3` using `Int.toNat_of_nonneg q0`. Generalize the expression as in `((c + 2) / ((Tp.TO + Tp.Dp + 2 : ℕ) : ℤ)).toNat = G at q3 ⊢`. Rewrite `q1`, `q2` using `[← q3]`. Establish `r1 : ((Tp.TO : ℝ) + Tp.Dp + 2) * (G : ℝ) ≤ (c : ℝ) + 2` using `by exact_mod_cast q1`.

Establish `r2 : (c : ℝ) + 2 < ((Tp.TO : ℝ) + Tp.Dp + 2) * (G : ℝ) + ((Tp.TO : ℝ) + Tp.Dp + 2)` using `by exact_mod_cast q2`. Establish `g2 : (c : ℝ) = (((D.hc (plOf D z)).v ⟨D.R.k - 2, hv⟩ : ℚ) : ℝ) + (((D.hc (plOf D z)).b ⟨0, hm⟩ : ℚ) : ℝ) - 1`. Conclude with `congrArg (fun q : ℚ => (q : ℝ)) g1` after adjusting the coercions. Establish `hwe : (numOf D L).w j z = (((D.hc (plOf D z)).e ⟨j - 1, hjm⟩ : ℚ) : ℝ)`. Unfold `NumDatum.w NumDatum.eQ`.

Use `congr 1`. Use `split_ifs with h`. Both sides reduce to the same expression. Apply the tactic sequence `exact absurd (by first | exact hjm | exact ⟨hj1, hj2⟩) h`. Establish `c1` using `L.cloud_v (plOf D z) ⟨D.R.k - 2, hv⟩`.

Establish `c2` using `abs_le.1 (L.be_close (plOf D z) ⟨0, hm⟩ ⟨j - 1, hjm⟩)`. Rewrite `c2` using `[Rat.cast_sub]`. Establish `hT40 : 40 * ((Tp.Dp : ℝ) + 2) ≤ Tp.TO` using `by exact_mod_cast Tp.TO_40`. Establish `hD : (0 : ℝ) ≤ Tp.Dp` using `Nat.cast_nonneg _`. Establish `hT2 : (1 : ℝ) ≤ (Tp.TO : ℝ) ^ 2` using `one_le_pow₀ (by linarith)`.

Establish `hDel` using `le_two_floor (hT2.trans Tp.Del_TO)`. Establish `hh0 : (1 : ℝ) ≤ LevelStarExponents.h0 L`. Use `Tp.heightBound_ge_order_sq` as an intermediate fact. Establish `: (0 : ℝ) ≤ D.R.t` using `Nat.cast_nonneg _`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hh` using `le_two_floor hh0`. Establish `hmR : (0 : ℝ) < D.R.m` using `by exact_mod_cast hm`. Use `real_bounds (y := (c : ℝ) + 2) (η := L.etaSz) (t := D.R.t) (S := L.Sc) hT40 hD (Nat.cast_nonneg _) r1 (by linarith) (by rw [hwe]; linarith [c1.1, c2.1]) (by rw [hwe]; linarith [c1.2, c2.2]) (by exact_mod_cast TO_le_t Tp) Pm.t_le_eta Pm.teta L.sc.one_lt_alt hw ?_ ?_ ?_` and prove the remaining obligations. Rewrite using `[L.Sc_eq] show _ ≤ 2 * ((D.R.k : ℝ) * (4 * ((⌊(D.s.Del : ℝ)⌋₊ : ℕ) : ℝ)))`. Establish `: (0 : ℝ) ≤ D.R.k` using `Nat.cast_nonneg _`.

Use the polynomial consequences of the given equalities and inequalities. Unfold `NumDatum.Sc`. Check the signs of the components of the expression. Use `show _ ≤ 2 * ((D.R.m : ℝ) * ((⌊LevelStarExponents.h0 L⌋₊ : ℕ) : ℝ))`. Establish `e : L.etaSz = D.R.m * LevelStarExponents.h0 L` using `by unfold LevelStarExponents.h0; field_simp`.

Rewrite using `[e]`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem gap_bounds : ∀ (D : D7) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (j : ℕ), InR D j → ∀ z : RPl D.R, L.sc.w'' D.R.n ≤ (numOf D L).w j z →
  (1 - ((Tp.Dp : ℝ) + 4) / Tp.TO) * (numOf D L).w j z ≤ (Tp.TO : ℝ) * gapW (numOf D L) (fun z => DV.tauEmb D (plOf D z)) (wtA (lR Tp hK j)) z ∧
  (Tp.TO : ℝ) * gapW (numOf D L) (fun z => DV.tauEmb D (plOf D z)) (wtA (lR Tp hK j)) z ≤ (numOf D L).w j z + 100 * ((numOf D L).Sc + (numOf D L).eta) := by
  intro D L Pm Tp hK j hj z hw
  have hj1 := hj.1
  have hj2 := hj.2
  have hk : 5 ≤ D.R.k := by have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega
  have hs : (D.R.sigW j).1 = D.R.k + j - 1 := rfl
  have h1 : D.R.k - 2 < (D.R.sigW j).1 := by omega
  have h2 : D.R.k - 2 + 1 < (D.R.sigW j).1 := by omega
  have hv : D.R.k - 2 < D.R.k - 1 := by omega
  have hm : 0 < D.R.m := by omega
  have hjm : j - 1 < D.R.m := by omega
  rw [gapW_eq Tp hK z h1 h2 (by omega)]
  obtain ⟨g0, g1⟩ := gap_kappa Tp hK hj (plOf D z) h1 h2 hv hm
  generalize WeightAlgebra.gapZ ((kaR Tp hK j).aP (plOf D z)) ⟨D.R.k - 2, h1⟩ = c at g0 g1 ⊢
  have hT' : WeightAlgebra.Tp D j Tp.TO = Tp.TO + Tp.Dp + 2 := by
    unfold WeightAlgebra.Tp; rw [GlobalTheory.DepthBoundProbe.dimY_eq Tp hj]
  rw [hT', Int.fdiv_eq_ediv_of_nonneg _ (Nat.cast_nonneg _)]
  have hpos : (0 : ℤ) < ((Tp.TO + Tp.Dp + 2 : ℕ) : ℤ) := by positivity
  have q0 : 0 ≤ (c + 2) / ((Tp.TO + Tp.Dp + 2 : ℕ) : ℤ) := Int.ediv_nonneg (by omega) hpos.le
  have q1 := Int.mul_ediv_self_le (x := c + 2) hpos.ne'
  have q2 := Int.lt_mul_ediv_self_add (x := c + 2) hpos
  have q3 := Int.toNat_of_nonneg q0
  generalize ((c + 2) / ((Tp.TO + Tp.Dp + 2 : ℕ) : ℤ)).toNat = G at q3 ⊢
  rw [← q3] at q1 q2
  have r1 : ((Tp.TO : ℝ) + Tp.Dp + 2) * (G : ℝ) ≤ (c : ℝ) + 2 := by exact_mod_cast q1
  have r2 : (c : ℝ) + 2 < ((Tp.TO : ℝ) + Tp.Dp + 2) * (G : ℝ) + ((Tp.TO : ℝ) + Tp.Dp + 2) := by exact_mod_cast q2
  have g2 : (c : ℝ) = (((D.hc (plOf D z)).v ⟨D.R.k - 2, hv⟩ : ℚ) : ℝ) + (((D.hc (plOf D z)).b ⟨0, hm⟩ : ℚ) : ℝ) - 1 := by
    exact_mod_cast congrArg (fun q : ℚ => (q : ℝ)) g1
  have hwe : (numOf D L).w j z = (((D.hc (plOf D z)).e ⟨j - 1, hjm⟩ : ℚ) : ℝ) := by
    unfold NumDatum.w NumDatum.eQ
    congr 1
    split_ifs with h
    · rfl
    · exact absurd (by first | exact hjm | exact ⟨hj1, hj2⟩) h
  have c1 := L.cloud_v (plOf D z) ⟨D.R.k - 2, hv⟩
  have c2 := abs_le.1 (L.be_close (plOf D z) ⟨0, hm⟩ ⟨j - 1, hjm⟩)
  rw [Rat.cast_sub] at c2
  have hT40 : 40 * ((Tp.Dp : ℝ) + 2) ≤ Tp.TO := by exact_mod_cast Tp.TO_40
  have hD : (0 : ℝ) ≤ Tp.Dp := Nat.cast_nonneg _
  have hT2 : (1 : ℝ) ≤ (Tp.TO : ℝ) ^ 2 := one_le_pow₀ (by linarith)
  have hDel := le_two_floor (hT2.trans Tp.Del_TO)
  have hh0 : (1 : ℝ) ≤ LevelStarExponents.h0 L := by
    have := Tp.heightBound_ge_order_sq
    have : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
    linarith
  have hh := le_two_floor hh0
  have hmR : (0 : ℝ) < D.R.m := by exact_mod_cast hm
  refine real_bounds (y := (c : ℝ) + 2) (η := L.etaSz) (t := D.R.t) (S := L.Sc) hT40 hD (Nat.cast_nonneg _) r1
    (by linarith) (by rw [hwe]; linarith [c1.1, c2.1]) (by rw [hwe]; linarith [c1.2, c2.2])
    (by exact_mod_cast TO_le_t Tp) Pm.t_le_eta Pm.teta L.sc.one_lt_alt hw ?_ ?_ ?_
  · rw [L.Sc_eq]
    show _ ≤ 2 * ((D.R.k : ℝ) * (4 * ((⌊(D.s.Del : ℝ)⌋₊ : ℕ) : ℝ)))
    have : (0 : ℝ) ≤ D.R.k := Nat.cast_nonneg _
    nlinarith
  · unfold NumDatum.Sc; positivity
  · show _ ≤ 2 * ((D.R.m : ℝ) * ((⌊LevelStarExponents.h0 L⌋₊ : ℕ) : ℝ))
    have e : L.etaSz = D.R.m * LevelStarExponents.h0 L := by unfold LevelStarExponents.h0; field_simp
    rw [e]
    nlinarith

end GlobalTheory.GoodDepth.Gap
