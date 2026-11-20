import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.LocalBesselAndTopKernel
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Formalism.HermitianCurvature.HeisenbergConjugationMeasurePreserving
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LevelPrimeSplitsCompletelyInCmField
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FinprodPlacesOverTypePrimesSplit
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalIndicesColumnRowLevelsExact
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StdLatIsOrthoLatticeAndMassProperties
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ProdSubEqProdFactorial
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowHCParameterIsHCParamAndFormalDegreePos
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsFdegSmulOfIsDS
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsDiscreteSeriesFormalDegreeProduct
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqExistsIffDsExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.FormalDegreeCompactDualIff

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.FourierDecayAlt NumberField Finset

noncomputable section

namespace GlobalTheory.CritLevel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Take `⟨t, ht⟩` from `R.m_even`. Use `R.two_le_m` as an intermediate fact. Simplify using `only [Ranks.rS]`. Use linear arithmetic over natural numbers and integers.
-/
theorem m_eq (R : Ranks) : R.m = 2 * R.rS + 2 := by
  obtain ⟨t, ht⟩ := R.m_even
  have := R.two_le_m
  simp only [Ranks.rS]; omega

/- English proof (translation)
Simplify using `[Sz.sfac]`.
-/
theorem sfac_cast (n : ℕ) : (Sz.sfac n : ℝ) = ∏ i ∈ range n, (i.factorial : ℝ) := by
  simp [Sz.sfac]

/- English proof (translation)
The claim follows from `prod_pos fun _ _ => prod_pos fun _ hb => sub_pos.2 (h (mem_filter.1 hb).2)`.
-/
theorem vand_pos {n : ℕ} {x : Fin n → ℝ} (h : StrictAnti x) : 0 < vand x :=
  prod_pos fun _ _ => prod_pos fun _ hb => sub_pos.2 (h (mem_filter.1 hb).2)

/- English proof (translation)
Establish `hk` using `D.R.m_add_three_le_k`. Take `⟨c, hc⟩` from `D.R.k_even`. Use `⟨?_, fun a => ?_⟩` and prove the remaining obligations. Take `⟨n, hn⟩ : ∃ n, D.R.k = n + 1` from `⟨D.R.k - 1, by omega⟩`. Establish `key : ∀ (d i : ℕ) (h : i + d + 1 < D.R.k), (D.hcW w τ).u ⟨i + d + 1, h⟩ < (D.hcW w τ).u ⟨i, by omega⟩`.

Establish `step : ∀ (i : ℕ) (h : i + 1 < D.R.k), (D.hcW w τ).u ⟨i + 1, h⟩ < (D.hcW w τ).u ⟨i, by omega⟩` using `fun i h => lt_trans ((D.hcW w τ).v_gt_u ⟨i, by omega⟩) ((D.hcW w τ).u_gt_v ⟨i, by omega⟩)`. Introduce `d`. Proceed by induction on `d with`. Consider the case `zero => intro i h`. Conclude with `step i h`.

Consider the case `succ d ih => intro i h; exact lt_trans (step (i + d + 1) h) (ih i (by omega))`. Introduce `i j hij`. Establish `hlt : i.val < j.val` using `hij`. Use `key (j.val - i.val - 1) i.val (by omega)` as an intermediate fact. Establish `e : (D.hcW w τ).u ⟨i.val + (j.val - i.val - 1) + 1, by omega⟩ = (D.hcW w τ).u j` using `congrArg _ (Fin.ext (by simp; omega))`.

Rewrite `this` using `[e]`. Unfold `uS`. Conclude with `this` after adjusting the coercions. Take `⟨z, hz⟩` from `(D.hcW w τ).u_half a`. Use `⟨z - c + 1, ?_⟩` and prove the remaining obligations.

Unfold `uS`. Rewrite using `[hz, hc]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem isHCParam_uS (D : D7) (w : D.what₂.Word) (τ : D.what₂.Tau) : Formalism.QuantumDeterminants.IsHCParam (uS D w τ) := by
  have hk := D.R.m_add_three_le_k
  obtain ⟨c, hc⟩ := D.R.k_even
  refine ⟨?_, fun a => ?_⟩
  · obtain ⟨n, hn⟩ : ∃ n, D.R.k = n + 1 := ⟨D.R.k - 1, by omega⟩
    have key : ∀ (d i : ℕ) (h : i + d + 1 < D.R.k),
        (D.hcW w τ).u ⟨i + d + 1, h⟩ < (D.hcW w τ).u ⟨i, by omega⟩ := by
      have step : ∀ (i : ℕ) (h : i + 1 < D.R.k), (D.hcW w τ).u ⟨i + 1, h⟩ < (D.hcW w τ).u ⟨i, by omega⟩ :=
        fun i h => lt_trans ((D.hcW w τ).v_gt_u ⟨i, by omega⟩) ((D.hcW w τ).u_gt_v ⟨i, by omega⟩)
      intro d
      induction d with
      | zero => intro i h; exact step i h
      | succ d ih => intro i h; exact lt_trans (step (i + d + 1) h) (ih i (by omega))
    intro i j hij
    have hlt : i.val < j.val := hij
    have := key (j.val - i.val - 1) i.val (by omega)
    have e : (D.hcW w τ).u ⟨i.val + (j.val - i.val - 1) + 1, by omega⟩ = (D.hcW w τ).u j :=
      congrArg _ (Fin.ext (by simp; omega))
    rw [e] at this
    unfold uS
    exact_mod_cast this
  · obtain ⟨z, hz⟩ := (D.hcW w τ).u_half a
    refine ⟨z - c + 1, ?_⟩
    unfold uS
    rw [hz, hc]; push_cast; ring

/- English proof (translation)
Establish `hka : 0 < D.host.ka` using `div_pos Real.pi_pos hv`. Establish `hg : 0 ≤ gg D` using `by unfold gg; positivity`. Establish `hm` using `m_eq D.R`. Establish `e0 : D.R.m * (D.R.m - 1) / 2 = (D.R.rS + 1) * (2 * D.R.rS + 1)`. Establish `: D.R.m * (D.R.m - 1) = 2 * ((D.R.rS + 1) * (2 * D.R.rS + 1))`.

Rewrite using `[hm, show 2 * D.R.rS + 2 - 1 = 2 * D.R.rS + 1 by omega]; ring`. Use linear arithmetic over natural numbers and integers. Establish `e1 : D.R.m - 1 = 2 * D.R.rS + 1` using `by omega`. Establish `hmR : (D.R.m : ℝ) = 2 * D.R.rS + 2` using `by exact_mod_cast hm`. Unfold `Tcrit Sz.Tcrit Sz.TcritPow`.

Rewrite using `[e0, e1, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_neg hka.le]`. Use `congr 5`. Use `congr 1`. Rewrite using `[hmR]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hmR]`. Use `push_cast`. Rewrite using `[hmR]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem tcrit_eq (D : D7) (hv : 0 < D.host.v) (u : D.what₂.Word) (τ : D.what₂.Tau) :
    Tcrit D u τ = Sz.Tcrit D.R.k D.R.m D.host.ka D.host.rdE (gg D) (VV D τ) (vand (uS D u τ)) := by
  have hka : 0 < D.host.ka := div_pos Real.pi_pos hv
  have hg : 0 ≤ gg D := by unfold gg; positivity
  have hm := m_eq D.R
  have e0 : D.R.m * (D.R.m - 1) / 2 = (D.R.rS + 1) * (2 * D.R.rS + 1) := by
    have : D.R.m * (D.R.m - 1) = 2 * ((D.R.rS + 1) * (2 * D.R.rS + 1)) := by
      rw [hm, show 2 * D.R.rS + 2 - 1 = 2 * D.R.rS + 1 by omega]; ring
    omega
  have e1 : D.R.m - 1 = 2 * D.R.rS + 1 := by omega
  have hmR : (D.R.m : ℝ) = 2 * D.R.rS + 2 := by exact_mod_cast hm
  unfold Tcrit Sz.Tcrit Sz.TcritPow
  rw [e0, e1, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_neg hka.le]
  congr 5
  · congr 1
    rw [hmR]; push_cast; ring
  · rw [hmR]; push_cast; rw [hmR]; ring

def sizeData (D : D7) (u : D.what₂.Word) : Sz.SizeData D.what₂.Tau where
  k := D.R.k
  r := D.R.rS
  v := D.host.v
  dF := (2 * D.host.v) ^ D.R.f
  Lv := fun M => Formalism.HermitianLatticesTheory.lValEta D.host.E M
  vol := fun M => Cnt.massU D.host.E M
  g1 := D.host.g 0
  g2 := D.host.g 1
  T := (D.mem u).A.T
  dsig := D.dsig
  Vu := fun τ => vand (uS D u τ)
  du := D.duS u

/- English proof (translation)
Establish `hS : ∀ i, StandardLattice.SplitsF D (D.host.g i)` using `fun i => (GlobalTheory.ColClassCompare.split_g_iff D i).2 (GlobalTheory.IndefiniteRowSideFullHecke.SplitColumnClasses.splitsCompletely_g D i)`. Establish `hp` using `GlobalTheory.TypedPlacesProduct.finprod_typed_places D (fun x => ∏ i ∈ Icc 1 D.R.k, (x ^ i - 1)) hS`. Establish `e : ∀ i, Sz.colIdx D.R.k (D.host.g i) = ∏ j ∈ Icc 1 D.R.k, ((D.host.g i : ℝ) ^ j - 1)` using `fun i => by`. Establish `: (0 : ℝ) < D.host.g i` using `by exact_mod_cast (D.host.g_prime i).pos`. Unfold `Sz.colIdx Sz.glCard`.

Rewrite using `[GlobalTheory.prod_pow_sub_pow_eq_mul_prod_Icc]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[e, e]`. Conclude with `hp`.
-/
theorem gaG_eq (D : D7) : gaG D = Sz.colIdx D.R.k (D.host.g 0) ^ D.R.f * Sz.colIdx D.R.k (D.host.g 1) ^ D.R.f := by
  have hS : ∀ i, StandardLattice.SplitsF D (D.host.g i) := fun i =>
    (GlobalTheory.ColClassCompare.split_g_iff D i).2 (GlobalTheory.IndefiniteRowSideFullHecke.SplitColumnClasses.splitsCompletely_g D i)
  have hp := GlobalTheory.TypedPlacesProduct.finprod_typed_places D (fun x => ∏ i ∈ Icc 1 D.R.k, (x ^ i - 1)) hS
  have e : ∀ i, Sz.colIdx D.R.k (D.host.g i) = ∏ j ∈ Icc 1 D.R.k, ((D.host.g i : ℝ) ^ j - 1) := fun i => by
    have : (0 : ℝ) < D.host.g i := by exact_mod_cast (D.host.g_prime i).pos
    unfold Sz.colIdx Sz.glCard
    rw [GlobalTheory.prod_pow_sub_pow_eq_mul_prod_Icc]
    field_simp
  rw [e, e]
  exact hp

/- English proof (translation)
Establish `hS : ∀ i, StandardLattice.SplitsF D (D.host.g i)` using `fun i => (GlobalTheory.ColClassCompare.split_g_iff D i).2 (GlobalTheory.IndefiniteRowSideFullHecke.SplitColumnClasses.splitsCompletely_g D i)`. Establish `hp` using `GlobalTheory.TypedPlacesProduct.finprod_typed_places D (fun x => LocalBesselAndTopKernel.cardGL x D.R.r / (x ^ LocalBesselAndTopKernel.dimNS D * x ^ (D.R.k * (D.R.k - 1) / 2))) hS`. Establish `hr : D.R.k + 2 * D.R.rS + 1 = D.R.r` using `by have := dimS_eq D.R; omega`. Unfold `Sz.rowIdx`. Rewrite using `[hr]`.

Conclude with `hp`.
-/
theorem idxRows_eq (D : D7) : LocalBesselAndTopKernel.idxRows D =
    Sz.rowIdx D.R.k D.R.rS (D.host.g 0) ^ D.R.f * Sz.rowIdx D.R.k D.R.rS (D.host.g 1) ^ D.R.f := by
  have hS : ∀ i, StandardLattice.SplitsF D (D.host.g i) := fun i =>
    (GlobalTheory.ColClassCompare.split_g_iff D i).2 (GlobalTheory.IndefiniteRowSideFullHecke.SplitColumnClasses.splitsCompletely_g D i)
  have hp := GlobalTheory.TypedPlacesProduct.finprod_typed_places D
    (fun x => LocalBesselAndTopKernel.cardGL x D.R.r / (x ^ LocalBesselAndTopKernel.dimNS D * x ^ (D.R.k * (D.R.k - 1) / 2))) hS
  have hr : D.R.k + 2 * D.R.rS + 1 = D.R.r := by have := dimS_eq D.R; omega
  unfold Sz.rowIdx
  rw [hr]
  exact hp

/- English proof (translation)
Introduce `u`. Establish `hk` using `D.R.m_add_three_le_k`. Establish `hm2` using `D.R.two_le_m`. Establish `hm` using `m_eq D.R`. Establish `hst` using `GlobalTheory.Mass.StdMass.main D.host.E D.sp.cm.cmUnram`.

Use `set S := sizeData D u with hS`. Establish `hf : S.f = D.R.f` using `D.what₂.card_Tau`. Establish `hSm : S.m = D.R.m` using `hm.symm`. Establish `hn : S.n = D.R.r` using `by show D.R.k + S.m - 1 = D.R.r`. Rewrite using `[hSm]`.

Both sides reduce to the same expression. Establish `hVu : ∀ τ, 0 < vand (uS D u τ)` using `fun τ => vand_pos (isHCParam_uS D u τ).1`. Establish `hOk : S.Ok` using `⟨show 1 ≤ D.R.k by omega, hv, by rw [hf]; rfl, (D.host.g_prime 0).two_le, (D.host.g_prime 1).two_le, (D.mem u).A.T_prime.two_le, (hst D.R.k).2.2.1, hVu⟩`. Establish `hMR : S.MassRatios`. Introduce `M h1 _`.

Establish `h1' : D.R.k < M` using `h1`. Establish `h` using `hM M (by omega) _ _ _ _ _ _ (hst M).1 (hst (M - 1)).1 (hst M).2.1 (hst (M - 1)).2.1`. Rewrite `h` using `[StandardLattice.mass_ratio_eq]`. Use `replace h := (div_eq_iff (hst (M - 1)).2.2.1.ne').1 h`. Rewrite using `[hf]`.

Use `h.trans ?_` and prove the remaining obligations. Unfold `StandardLattice.ratioH`. Rewrite using `[Real.rpow_neg (hOk.hdF ▸ by positivity), ← Real.sqrt_eq_rpow, div_eq_mul_inv]`. Both sides reduce to the same expression. Establish `hLB : S.LBound`.

Introduce `M h1 _`. Establish `h1' : D.R.k < M` using `h1`. Rewrite using `[hf]`. Conclude with `⟨StandardLattice.lVal_pos D M (by omega), StandardLattice.massIdentity_holds D M (by omega)⟩`. Establish `hCC : S.ColumnCount`.

Establish `h` using `(hR _ _ _ (hst D.R.k).1).1 (hst D.R.k).2.1 u`. Rewrite `h` using `[gaG_eq, ← sfac_cast]`. Unfold `Sz.SizeData.ColumnCount Sz.SizeData.idxCol`. Rewrite using `[hf]`. Conclude with `h`.

Establish `hD : S.Dstar = D.what₂.Dstar`. Establish `h` using `(hR _ _ _ (hst D.R.r).1).2 (hst D.R.r).2.1`. Rewrite `h` using `[idxRows_eq]`. Unfold `Sz.SizeData.Dstar Sz.SizeData.idxRow`. Rewrite using `[hf, hn]`.

Conclude with `h.symm`. Establish `hA` using `Final.sz_propA _ S hOk hMR hCC`. Take `⟨hE0, hE⟩` from `Final.sz_eaSize _ S hOk hLB (show 2 ≤ D.R.k by omega) hg0 hg1`. Establish `hpow : ∀ τ, 0 < S.TcritPow τ ∧ (Tcrit D u τ / Tr D u) ^ D.R.k = S.TcritPow τ / (S.T : ℝ) ^ S.k`. Introduce `τ`.

Establish `hrd : S.rd = D.host.rdE` using `by show 2 * (D.host.rdE / 2) = _`. Expand and normalize the polynomial expressions, which then agree. Establish `hVV : S.VV τ = VV D τ`. Unfold `Sz.SizeData.VV VV`. Rewrite using `[hn, sfac_cast]`.

Both sides reduce to the same expression. Establish `hpos : 0 < S.TcritPow τ`. Establish `h1 : 0 < S.ka` using `div_pos Real.pi_pos hv`. Establish `h2 : 0 < S.rd` using `mul_pos two_pos hv`. Establish `h3 : 0 < S.g`.

Establish `a : (0 : ℝ) < D.host.g 0` using `by exact_mod_cast (D.host.g_prime 0).pos`. Establish `b : (0 : ℝ) < D.host.g 1` using `by exact_mod_cast (D.host.g_prime 1).pos`. Conclude with `mul_pos a b`. Establish `h4 : 0 < S.VV τ`. Rewrite using `[hVV]; exact mul_pos (D.dsig_pos τ) (prod_pos fun i _ => by positivity)`.

Establish `h5 : 0 < S.Vu τ` using `hVu τ`. Unfold `Sz.SizeData.TcritPow Sz.TcritPow`. Check the signs of the components of the expression. Use `⟨hpos, ?_⟩` and prove the remaining obligations. Establish `e : Tcrit D u τ = S.TcritPow τ ^ ((1 : ℝ) / (D.R.k : ℝ))`.

Rewrite using `[tcrit_eq D hv]`. Unfold `Sz.SizeData.TcritPow Sz.Tcrit`. Rewrite using `[hrd, hVV, hSm]`. Both sides reduce to the same expression. Rewrite using `[div_pow, e, one_div, Real.rpow_inv_natCast_pow hpos.le (by omega)]`.

Both sides reduce to the same expression. Establish `hP : 0 ≤ ∏ τ, S.TcritPow τ / (S.T : ℝ) ^ S.k` using `prod_nonneg fun τ _ => div_nonneg (hpow τ).1.le (by positivity)`. Establish `e2 : (2 : ℝ) ^ ((3 : ℝ) - D.R.k) = 8 / 2 ^ S.k`. Rewrite using `[Real.rpow_sub two_pos, Real.rpow_natCast]`. Evaluate the numerical expressions.

Both sides reduce to the same expression. Rewrite using `[prod_congr rfl fun τ _ => (hpow τ).2, e2, ← hD, ← hf]`. Express the relevant statement in the definitionally equal form `_ ≤ S.Dstar / S.du ∧ S.Dstar / S.du ≤ _`. Rewrite using `[hA]`. Rewrite `hE` using `[abs_le]`.

Use `⟨mul_le_mul_of_nonneg_right ?_ hP, mul_le_mul_of_nonneg_right ?_ hP⟩` and prove the remaining obligations. Conclude with `(Real.le_log_iff_exp_le hE0).1 hE.1`. Conclude with `(Real.log_le_iff_le_exp hE0).1 hE.2`.
-/
theorem ratio_ranks (D : D7) (hM : UnitaryVolumeMass.stMassRatio D) (hR : LocalBesselAndTopKernel.FamilyMidVolume D) (hv : 0 < D.host.v)
    (hg0 : 4 ≤ D.host.g 0) (hg1 : 4 ≤ D.host.g 1) : UnitaryVolumeMass.cTvA D := by
  intro u
  have hk := D.R.m_add_three_le_k
  have hm2 := D.R.two_le_m
  have hm := m_eq D.R
  have hst := GlobalTheory.Mass.StdMass.main D.host.E D.sp.cm.cmUnram
  set S := sizeData D u with hS
  have hf : S.f = D.R.f := D.what₂.card_Tau
  have hSm : S.m = D.R.m := hm.symm
  have hn : S.n = D.R.r := by
    show D.R.k + S.m - 1 = D.R.r
    rw [hSm]; rfl
  have hVu : ∀ τ, 0 < vand (uS D u τ) := fun τ => vand_pos (isHCParam_uS D u τ).1
  have hOk : S.Ok := ⟨show 1 ≤ D.R.k by omega, hv, by rw [hf]; rfl, (D.host.g_prime 0).two_le,
    (D.host.g_prime 1).two_le, (D.mem u).A.T_prime.two_le, (hst D.R.k).2.2.1, hVu⟩
  have hMR : S.MassRatios := by
    intro M h1 _
    have h1' : D.R.k < M := h1
    have h := hM M (by omega) _ _ _ _ _ _ (hst M).1 (hst (M - 1)).1 (hst M).2.1 (hst (M - 1)).2.1
    rw [StandardLattice.mass_ratio_eq] at h
    replace h := (div_eq_iff (hst (M - 1)).2.2.1.ne').1 h
    rw [hf]
    refine h.trans ?_
    unfold StandardLattice.ratioH
    rw [Real.rpow_neg (hOk.hdF ▸ by positivity), ← Real.sqrt_eq_rpow, div_eq_mul_inv]
    rfl
  have hLB : S.LBound := by
    intro M h1 _
    have h1' : D.R.k < M := h1
    rw [hf]
    exact ⟨StandardLattice.lVal_pos D M (by omega), StandardLattice.massIdentity_holds D M (by omega)⟩
  have hCC : S.ColumnCount := by
    have h := (hR _ _ _ (hst D.R.k).1).1 (hst D.R.k).2.1 u
    rw [gaG_eq, ← sfac_cast] at h
    unfold Sz.SizeData.ColumnCount Sz.SizeData.idxCol
    rw [hf]
    exact h
  have hD : S.Dstar = D.what₂.Dstar := by
    have h := (hR _ _ _ (hst D.R.r).1).2 (hst D.R.r).2.1
    rw [idxRows_eq] at h
    unfold Sz.SizeData.Dstar Sz.SizeData.idxRow
    rw [hf, hn]
    exact h.symm
  have hA := Final.sz_propA _ S hOk hMR hCC
  obtain ⟨hE0, hE⟩ := Final.sz_eaSize _ S hOk hLB (show 2 ≤ D.R.k by omega) hg0 hg1
  have hpow : ∀ τ, 0 < S.TcritPow τ ∧ (Tcrit D u τ / Tr D u) ^ D.R.k = S.TcritPow τ / (S.T : ℝ) ^ S.k := by
    intro τ
    have hrd : S.rd = D.host.rdE := by
      show 2 * (D.host.rdE / 2) = _
      ring
    have hVV : S.VV τ = VV D τ := by
      unfold Sz.SizeData.VV VV
      rw [hn, sfac_cast]; rfl
    have hpos : 0 < S.TcritPow τ := by
      have h1 : 0 < S.ka := div_pos Real.pi_pos hv
      have h2 : 0 < S.rd := mul_pos two_pos hv
      have h3 : 0 < S.g := by
        have a : (0 : ℝ) < D.host.g 0 := by exact_mod_cast (D.host.g_prime 0).pos
        have b : (0 : ℝ) < D.host.g 1 := by exact_mod_cast (D.host.g_prime 1).pos
        exact mul_pos a b
      have h4 : 0 < S.VV τ := by
        rw [hVV]; exact mul_pos (D.dsig_pos τ) (prod_pos fun i _ => by positivity)
      have h5 : 0 < S.Vu τ := hVu τ
      unfold Sz.SizeData.TcritPow Sz.TcritPow
      positivity
    refine ⟨hpos, ?_⟩
    have e : Tcrit D u τ = S.TcritPow τ ^ ((1 : ℝ) / (D.R.k : ℝ)) := by
      rw [tcrit_eq D hv]
      unfold Sz.SizeData.TcritPow Sz.Tcrit
      rw [hrd, hVV, hSm]; rfl
    rw [div_pow, e, one_div, Real.rpow_inv_natCast_pow hpos.le (by omega)]
    rfl
  have hP : 0 ≤ ∏ τ, S.TcritPow τ / (S.T : ℝ) ^ S.k :=
    prod_nonneg fun τ _ => div_nonneg (hpow τ).1.le (by positivity)
  have e2 : (2 : ℝ) ^ ((3 : ℝ) - D.R.k) = 8 / 2 ^ S.k := by
    rw [Real.rpow_sub two_pos, Real.rpow_natCast]; norm_num; rfl
  rw [prod_congr rfl fun τ _ => (hpow τ).2, e2, ← hD, ← hf]
  change _ ≤ S.Dstar / S.du ∧ S.Dstar / S.du ≤ _
  rw [hA]
  rw [abs_le] at hE
  refine ⟨mul_le_mul_of_nonneg_right ?_ hP, mul_le_mul_of_nonneg_right ?_ hP⟩
  · exact (Real.le_log_iff_exp_le hE0).1 hE.1
  · exact (Real.log_le_iff_le_exp hE0).1 hE.2

/- English proof (translation)
Unfold `vand Sz.Vand`. Use `prod_bij (fun a _ => a.val + 1) (fun a _ => by have := a.2; simp) (fun a _ b _ e => Fin.ext (by omega)) (fun b hb => ⟨⟨b - 1, by have := mem_Icc.1 hb; omega⟩, mem_univ _, by have := mem_Icc.1 hb; simp; omega⟩) fun a _ => ?_` and prove the remaining obligations. Use `prod_bij (fun c _ => c.val + 1) (fun c hc => ?_) (fun a _ b _ e => Fin.ext (by omega)) (fun b hb => ⟨⟨b - 1, by have := mem_Ioc.1 hb; omega⟩, ?_, by have := mem_Ioc.1 hb; simp; omega⟩) fun c _ => by rw [h, h]` and prove the remaining obligations. Establish `h1 : a.val < c.val` using `(mem_filter.1 hc).2`. Use `c.2` as an intermediate fact.

Rewrite using `[mem_Ioc]`. Use linear arithmetic over natural numbers and integers. Use `mem_Ioc.1 hb` as an intermediate fact. Use `mem_filter.2 ⟨mem_univ _, ?_⟩` and prove the remaining obligations. Use `show a.val < b - 1`.

Use linear arithmetic over natural numbers and integers.
-/
theorem vand_eq_Vand {n : ℕ} (x : Fin n → ℝ) (y : ℕ → ℝ) (h : ∀ i : Fin n, x i = y (i + 1)) :
    vand x = Sz.Vand n y := by
  unfold vand Sz.Vand
  refine prod_bij (fun a _ => a.val + 1) (fun a _ => by have := a.2; simp) (fun a _ b _ e => Fin.ext (by omega))
    (fun b hb => ⟨⟨b - 1, by have := mem_Icc.1 hb; omega⟩, mem_univ _, by have := mem_Icc.1 hb; simp; omega⟩)
    fun a _ => ?_
  refine prod_bij (fun c _ => c.val + 1) (fun c hc => ?_) (fun a _ b _ e => Fin.ext (by omega))
    (fun b hb => ⟨⟨b - 1, by have := mem_Ioc.1 hb; omega⟩, ?_, by have := mem_Ioc.1 hb; simp; omega⟩)
    fun c _ => by rw [h, h]
  · have h1 : a.val < c.val := (mem_filter.1 hc).2
    have := c.2
    rw [mem_Ioc]; omega
  · have := mem_Ioc.1 hb
    refine mem_filter.2 ⟨mem_univ _, ?_⟩
    show a.val < b - 1
    omega

open Classical in

def cfg (D : D7) (u : D.what₂.Word) (τ : D.what₂.Tau) : Sz.Cfg where
  k := D.R.k
  m := D.R.m
  Del := D.s.Del
  vlast := vOne D τ (D.R.k - 1)
  b := bOne D τ
  a := uOne D u τ 1
  top := decide (IsTop D τ)
  bp := bTop D τ

def letters (D : D7) (u : D.what₂.Word) (i : ℕ) : ℝ :=
  if h : 1 ≤ i ∧ i - 1 < D.R.k - 2 then (if D.s.letter u ⟨i - 1, h.2⟩ then 1 else 0) else 0

/- English proof (translation)
Use `⟨fun i => ?_, ?_⟩` and prove the remaining obligations. Apply the tactic sequence `unfold letters split_ifs <;> simp`. Unfold `letters`. Rewrite using `[dif_neg (by omega)]`.
-/
theorem isWord_letters (D : D7) (u : D.what₂.Word) : Sz.IsWord D.R.k (letters D u) := by
  refine ⟨fun i => ?_, ?_⟩
  · unfold letters
    split_ifs <;> simp
  · unfold letters
    rw [dif_neg (by omega)]

/- English proof (translation)
Establish `hk` using `D.R.m_add_three_le_k`. Establish `key : ∀ d i : ℕ, 1 ≤ i → i + d = D.R.k - 1 → vOne D τ i = vOne D τ (D.R.k - 1) + 4 * (D.s.Del : ℝ) * d`. Introduce `d`. Proceed by induction on `d with`. Consider the case `zero => intro i _ h`.

Simplify using `[← h]`. Consider the case `succ d ih`. Introduce `i h1 h`. Establish `h3` using `ih (i + 1) (by omega) (by omega)`. Establish `h4` using `D.s.cloud_gap u τ (i - 1) (by omega)`.

Simplify using `only [D.hcW_v] at h4`. Establish `h5 : vOne D τ i - vOne D τ (i + 1) = 4 * (D.s.Del : ℝ)`. Unfold `vOne`. Rewrite using `[dif_pos ⟨h1, by omega⟩, dif_pos ⟨by omega, by omega⟩]`. Establish `e : (⟨i + 1 - 1, by omega⟩ : Fin (D.R.k - 1)) = ⟨i - 1 + 1, by omega⟩` using `Fin.ext (by simp only; omega)`.

Rewrite using `[e]`. Conclude with `h4` after adjusting the coercions. Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[key (D.R.k - 1 - i) i h1 (by omega), Nat.cast_sub h2, Nat.cast_sub (by omega)]`.

Simplify using `[Sz.Cfg.v, cfg]`.
-/
theorem cfg_v (D : D7) (u : D.what₂.Word) (τ : D.what₂.Tau) {i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ D.R.k - 1) :
    (cfg D u τ).v i = vOne D τ i := by
  have hk := D.R.m_add_three_le_k
  have key : ∀ d i : ℕ, 1 ≤ i → i + d = D.R.k - 1 →
      vOne D τ i = vOne D τ (D.R.k - 1) + 4 * (D.s.Del : ℝ) * d := by
    intro d
    induction d with
    | zero => intro i _ h; simp [← h]
    | succ d ih =>
      intro i h1 h
      have h3 := ih (i + 1) (by omega) (by omega)
      have h4 := D.s.cloud_gap u τ (i - 1) (by omega)
      simp only [D.hcW_v] at h4
      have h5 : vOne D τ i - vOne D τ (i + 1) = 4 * (D.s.Del : ℝ) := by
        unfold vOne
        rw [dif_pos ⟨h1, by omega⟩, dif_pos ⟨by omega, by omega⟩]
        have e : (⟨i + 1 - 1, by omega⟩ : Fin (D.R.k - 1)) = ⟨i - 1 + 1, by omega⟩ := Fin.ext (by simp only; omega)
        rw [e]
        exact_mod_cast h4
      push_cast
      linarith
  rw [key (D.R.k - 1 - i) i h1 (by omega), Nat.cast_sub h2, Nat.cast_sub (by omega)]
  simp [Sz.Cfg.v, cfg]

/- English proof (translation)
Establish `hk` using `D.R.m_add_three_le_k`. Establish `hm` using `m_eq D.R`. Rewrite using `[show D.R.k + D.R.m - 1 = 2 * D.R.rS + D.R.k + 1 by omega]`. Use `vand_eq_Vand _ _ fun i => ?_` and prove the remaining obligations. Establish `hi` using `i.2`.

Unfold `lamSH lamS Sz.Cfg.lam`. Simplify using `only [Fin.val_cast]`. Distinguish the cases in `h : i.val < D.R.k - 1`. Rewrite using `[dif_pos h, if_pos (show i.val + 1 < (cfg D u τ).k from (by omega : i.val + 1 < D.R.k)), cfg_v D u τ (by omega) (by omega)]`. Unfold `vOne`.

Rewrite using `[dif_pos ⟨by omega, by omega⟩]`. Both sides reduce to the same expression. Rewrite using `[dif_neg h, dif_pos (by omega), if_neg (show ¬ i.val + 1 < (cfg D u τ).k from (by omega : ¬ i.val + 1 < D.R.k))] show _ = -bOne D τ (i.val + 1 + 1 - D.R.k)`. Unfold `bOne`. Rewrite using `[dif_pos ⟨by omega, by omega⟩]`.

Use `congr 3`. Simplify using `only [Fin.mk.injEq]`. Use linear arithmetic over natural numbers and integers.
-/
theorem cfg_lam (D : D7) (u : D.what₂.Word) (τ : D.what₂.Tau) :
    vand (lamSH D.R (D.hc τ)) = Sz.Vand (D.R.k + D.R.m - 1) (cfg D u τ).lam := by
  have hk := D.R.m_add_three_le_k
  have hm := m_eq D.R
  rw [show D.R.k + D.R.m - 1 = 2 * D.R.rS + D.R.k + 1 by omega]
  refine vand_eq_Vand _ _ fun i => ?_
  have hi := i.2
  unfold lamSH lamS Sz.Cfg.lam
  simp only [Fin.val_cast]
  by_cases h : i.val < D.R.k - 1
  · rw [dif_pos h, if_pos (show i.val + 1 < (cfg D u τ).k from (by omega : i.val + 1 < D.R.k)), cfg_v D u τ (by omega) (by omega)]
    unfold vOne
    rw [dif_pos ⟨by omega, by omega⟩]
    rfl
  · rw [dif_neg h, dif_pos (by omega), if_neg (show ¬ i.val + 1 < (cfg D u τ).k from (by omega : ¬ i.val + 1 < D.R.k))]
    show _ = -bOne D τ (i.val + 1 + 1 - D.R.k)
    unfold bOne
    rw [dif_pos ⟨by omega, by omega⟩]
    congr 3
    simp only [Fin.mk.injEq]
    omega

/- English proof (translation)
Establish `hk` using `D.R.m_add_three_le_k`. Use `vand_eq_Vand _ _ fun i => ?_` and prove the remaining obligations. Establish `hi` using `i.2`. Establish `e : uS D u τ i = uOne D u τ (i.val + 1)`. Unfold `uOne`.

Rewrite using `[dif_pos ⟨by omega, by omega⟩]`. Both sides reduce to the same expression. Unfold `Sz.Cfg.u`. Distinguish the cases in `h1 : i.val + 1 = 1`. Rewrite using `[if_pos h1, e, h1]`.

Both sides reduce to the same expression. Rewrite using `[if_neg h1]`. Distinguish the cases in `h2 : i.val + 1 = D.R.k`. Rewrite using `[if_pos (show i.val + 1 = (cfg D u τ).k from h2), e, h2]`. Unfold `Sz.Cfg.ulast`.

Distinguish the cases in `ht : IsTop D τ`. Rewrite using `[if_pos (by simpa [cfg] using ht)] show _ = - -uOne D D.u₀ τ D.R.k`. Unfold `uOne uS`. Rewrite using `[neg_neg, dif_pos ⟨by omega, le_rfl⟩, dif_pos ⟨by omega, le_rfl⟩, D.hcW_last u τ (by omega), D.hcW_last D.u₀ τ (by omega)]`. Rewrite using `[if_neg (by simpa [cfg] using ht)]`.

Conclude with `hl ht`. Rewrite using `[if_neg (show ¬ i.val + 1 = (cfg D u τ).k from h2), Nat.add_sub_cancel, cfg_v D u τ (by omega) (by omega)]`. Establish `h3` using `D.s.u_letter u τ (i.val - 1) (by omega)`. Simplify using `only [D.hcW_v] at h3`. Establish `e2 : (⟨i.val - 1 + 1, by omega⟩ : Fin D.R.k) = i` using `Fin.ext (by simp only; omega)`.

Rewrite `h3` using `[e2]`. Unfold `uS vOne letters`. Rewrite using `[h3, dif_pos ⟨by omega, by omega⟩, dif_pos ⟨by omega, by omega⟩]`. Apply the tactic sequence `split_ifs <;> simp [cfg]`.
-/
theorem cfg_u (D : D7) (u : D.what₂.Word) (τ : D.what₂.Tau)
    (hl : ¬ IsTop D τ → uOne D u τ D.R.k = vOne D τ (D.R.k - 1) - 1 / 2) :
    vand (uS D u τ) = Sz.Vand D.R.k ((cfg D u τ).u (letters D u)) := by
  have hk := D.R.m_add_three_le_k
  refine vand_eq_Vand _ _ fun i => ?_
  have hi := i.2
  have e : uS D u τ i = uOne D u τ (i.val + 1) := by
    unfold uOne
    rw [dif_pos ⟨by omega, by omega⟩]
    rfl
  unfold Sz.Cfg.u
  by_cases h1 : i.val + 1 = 1
  · rw [if_pos h1, e, h1]; rfl
  rw [if_neg h1]
  by_cases h2 : i.val + 1 = D.R.k
  · rw [if_pos (show i.val + 1 = (cfg D u τ).k from h2), e, h2]
    unfold Sz.Cfg.ulast
    by_cases ht : IsTop D τ
    · rw [if_pos (by simpa [cfg] using ht)]
      show _ = - -uOne D D.u₀ τ D.R.k
      unfold uOne uS
      rw [neg_neg, dif_pos ⟨by omega, le_rfl⟩, dif_pos ⟨by omega, le_rfl⟩, D.hcW_last u τ (by omega),
        D.hcW_last D.u₀ τ (by omega)]
    · rw [if_neg (by simpa [cfg] using ht)]
      exact hl ht
  · rw [if_neg (show ¬ i.val + 1 = (cfg D u τ).k from h2), Nat.add_sub_cancel, cfg_v D u τ (by omega) (by omega)]
    have h3 := D.s.u_letter u τ (i.val - 1) (by omega)
    simp only [D.hcW_v] at h3
    have e2 : (⟨i.val - 1 + 1, by omega⟩ : Fin D.R.k) = i := Fin.ext (by simp only; omega)
    rw [e2] at h3
    unfold uS vOne letters
    rw [h3, dif_pos ⟨by omega, by omega⟩, dif_pos ⟨by omega, by omega⟩]
    split_ifs <;> simp [cfg]

/- English proof (translation)
Establish `hpar` using `GlobalTheory.Mem.Vol.lamSH_isHCParam D.R (D.hc τ)`. Take `⟨H, i1, i2, σ, hσ⟩` from `GlobalTheory.Published.discreteSeriesUpqExists_iff.1 hE _ (epsSH D.R) _ hpar`. Take `⟨d, hd⟩` from `GlobalTheory.Mem.Vol.exists_isFdeg_smul_of_isDS _ (epsSH D.R) _ H σ hσ _ (D.s.cdScale_pos _ (epsSH D.R))`. Establish `: Nontrivial H` using `hσ.2.1`. Take `⟨w, hw⟩` from `exists_ne (0 : H)`.

Establish `h1` using `GlobalTheory.Published.formalDegreeCompactDual_iff.1 hF D.cd D.s.cdScale hT.cdScale_tie _ (epsSH D.R) _ hpar H σ w hσ hw`. Rewrite `h1` using `[GlobalTheory.Mem.Vol.fdegOf_eq_of_isFdeg _ σ d hd w hw, hT.dsig_tie τ H σ d hσ hd]`. Unfold `VV`. Rewrite using `[h1, ← dimS_eq D.R, Formalism.QuantumDeterminants.fdegHC, GlobalTheory.WeylDimU.prod_sub_eq_prod_factorial, div_mul_cancel₀ _ (prod_pos fun i _ => by positivity).ne']`. Conclude with `prod_congr rfl fun a _ => prod_congr rfl fun b hb => abs_of_pos (sub_pos.2 (hpar.1 (mem_filter.1 hb).2))`.
-/
theorem vv_eq (hE : GlobalTheory.Published.DiscreteSeriesUpqExists) (hF : GlobalTheory.Published.FormalDegreeCompactDual) (D : D7)
    (hT : Ties D) (τ : D.what₂.Tau) : VV D τ = vand (lamSH D.R (D.hc τ)) := by
  have hpar := GlobalTheory.Mem.Vol.lamSH_isHCParam D.R (D.hc τ)
  obtain ⟨H, i1, i2, σ, hσ⟩ := GlobalTheory.Published.discreteSeriesUpqExists_iff.1 hE _ (epsSH D.R) _ hpar
  obtain ⟨d, hd⟩ := GlobalTheory.Mem.Vol.exists_isFdeg_smul_of_isDS _ (epsSH D.R) _ H σ hσ _ (D.s.cdScale_pos _ (epsSH D.R))
  have : Nontrivial H := hσ.2.1
  obtain ⟨w, hw⟩ := exists_ne (0 : H)
  have h1 := GlobalTheory.Published.formalDegreeCompactDual_iff.1 hF D.cd D.s.cdScale hT.cdScale_tie _ (epsSH D.R) _ hpar H σ w hσ hw
  rw [GlobalTheory.Mem.Vol.fdegOf_eq_of_isFdeg _ σ d hd w hw, hT.dsig_tie τ H σ d hσ hd] at h1
  unfold VV
  rw [h1, ← dimS_eq D.R, Formalism.QuantumDeterminants.fdegHC, GlobalTheory.WeylDimU.prod_sub_eq_prod_factorial,
    div_mul_cancel₀ _ (prod_pos fun i _ => by positivity).ne']
  exact prod_congr rfl fun a _ => prod_congr rfl fun b hb =>
    abs_of_pos (sub_pos.2 (hpar.1 (mem_filter.1 hb).2))

/- English proof (translation)
Establish `hkR : (5 : ℝ) ≤ k` using `by exact_mod_cast hk`. Establish `hB0 : 0 < B` using `lt_of_lt_of_le (by positivity) hB`. Establish `h1 : ka ^ (m - 1) ≤ (k : ℝ) ^ (m - 1)` using `pow_le_pow_left₀ hka0.le (by linarith) _`. Establish `h2 : (8 : ℝ) ≤ (k : ℝ) ^ 2` using `by nlinarith`. Establish `h3 : (k : ℝ) ^ (3 * r) * (k : ℝ) ^ (m - 1) * (k : ℝ) ^ 2 ≤ B ^ (m - 4)`.

Rewrite using `[← pow_add, ← pow_add]`. Combine the equalities or inequalities in the displayed calculation. Establish `h4 : B ^ (m - 4) * B ^ 4 = B ^ m` using `by rw [← pow_add]; congr 1; omega`. Establish `h5 : (k : ℝ) ^ (3 * r) * ka ^ (m - 1) * 8 * ae ≤ P`. Combine the equalities or inequalities in the displayed calculation.

Establish `hP0 : 0 ≤ P` using `le_trans (by positivity) hP`. Rewrite using `[le_div_iff₀ ha0]`. Combine the equalities or inequalities in the displayed calculation. Clear the denominators using the available nonvanishing facts. Use `_ ≤ c * (ka ^ (m - 1))⁻¹ * P := by gcongr`.
-/
theorem num_bound (k m r : ℕ) (B P ae c ka : ℝ) (hm : m = 2 * r + 2) (h40 : 40 ≤ m) (hk : 5 ≤ k)
    (hB : (k : ℝ) ^ 40 ≤ B) (hP : B ^ m ≤ P) (ha0 : 0 < ae) (ha : ae ≤ B ^ 4) (hc : 1 / 8 ≤ c) (hka0 : 0 < ka)
    (hka : ka ≤ 4) : (k : ℝ) ^ (3 * r) ≤ c * (ka ^ (m - 1))⁻¹ * P / ae := by
  have hkR : (5 : ℝ) ≤ k := by exact_mod_cast hk
  have hB0 : 0 < B := lt_of_lt_of_le (by positivity) hB
  have h1 : ka ^ (m - 1) ≤ (k : ℝ) ^ (m - 1) := pow_le_pow_left₀ hka0.le (by linarith) _
  have h2 : (8 : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith
  have h3 : (k : ℝ) ^ (3 * r) * (k : ℝ) ^ (m - 1) * (k : ℝ) ^ 2 ≤ B ^ (m - 4) := by
    rw [← pow_add, ← pow_add]
    calc (k : ℝ) ^ (3 * r + (m - 1) + 2) ≤ (k : ℝ) ^ (40 * (m - 4)) := pow_le_pow_right₀ (by linarith) (by omega)
      _ = ((k : ℝ) ^ 40) ^ (m - 4) := pow_mul _ _ _
      _ ≤ B ^ (m - 4) := pow_le_pow_left₀ (by positivity) hB _
  have h4 : B ^ (m - 4) * B ^ 4 = B ^ m := by rw [← pow_add]; congr 1; omega
  have h5 : (k : ℝ) ^ (3 * r) * ka ^ (m - 1) * 8 * ae ≤ P :=
    calc (k : ℝ) ^ (3 * r) * ka ^ (m - 1) * 8 * ae
        ≤ (k : ℝ) ^ (3 * r) * (k : ℝ) ^ (m - 1) * (k : ℝ) ^ 2 * B ^ 4 := by gcongr
      _ ≤ B ^ (m - 4) * B ^ 4 := by gcongr
      _ ≤ P := h4 ▸ hP
  have hP0 : 0 ≤ P := le_trans (by positivity) hP
  rw [le_div_iff₀ ha0]
  calc (k : ℝ) ^ (3 * r) * ae = 1 / 8 * (ka ^ (m - 1))⁻¹ * ((k : ℝ) ^ (3 * r) * ka ^ (m - 1) * 8 * ae) := by
        field_simp
    _ ≤ c * (ka ^ (m - 1))⁻¹ * P := by
        gcongr

set_option maxHeartbeats 1600000 in

/- English proof (translation)
Introduce and unpack `⟨hH, hD, -⟩ u τ`. Take `⟨-, -, -, -, -, -, hmL, hbD, -, -, -, hg0, -, hg1, -, hbj, -, -, hv, hDel, hgap, -, -, hClm, -⟩` from `hH`. Take `⟨hvw, -, ha, ha', hl, htop, -⟩` from `hD`. Establish `hk` using `D.R.m_add_three_le_k`. Establish `hm2` using `D.R.two_le_m`.

Establish `hm` using `m_eq D.R`. Establish `hkR : (5 : ℝ) ≤ D.R.k` using `by exact_mod_cast (by omega : 5 ≤ D.R.k)`. Establish `hmR : (40 : ℝ) ≤ D.R.m` using `hCl.trans hClm`. Establish `hf : (1 : ℝ) ≤ D.R.f`. Establish `: 1 ≤ D.R.f` using `le_trans (by omega) D.R.m_le_f`.

Conclude with `this` after adjusting the coercions. Establish `hn : (1 : ℝ) ≤ D.R.r`. Establish `: 1 ≤ D.R.r` using `by unfold Ranks.r; omega`. Conclude with `this` after adjusting the coercions. Establish `hL : 1 ≤ large₂.sc.L` using `Real.one_le_rpow large₂.sc.one_lt_alt.le large₂.sc.eps_pos.le`.

Establish `hb : 1 ≤ large₂.sc.b` using `Real.one_le_exp (by linarith)`. Establish `hlog : Real.log large₂.sc.b = large₂.sc.L` using `Real.log_exp _`. Establish `hD1 : (1 : ℝ) ≤ D.s.Del` using `le_trans (Real.one_le_rpow (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (by linarith) hf) hL) (by linarith)) hDel`. Use `set B := bOne D τ 1 with hBdef`. Establish `hB : (D.R.k : ℝ) ^ 40 ≤ B`.

Use `le_trans ?_ ((le_max_left _ _).trans (hbj τ 1 le_rfl (by omega)).1)` and prove the remaining obligations. Rewrite using `[← Real.rpow_natCast]`. Conclude with `Real.rpow_le_rpow_of_exponent_le (by linarith) (by exact_mod_cast hCl)`. Establish `hk2 : 3 * (D.R.k : ℝ) ≤ B`. Use `le_trans ?_ hB` and prove the remaining obligations.

Combine the equalities or inequalities in the displayed calculation. Establish `hB1 : 1 ≤ B` using `by linarith`. Establish `hkD : 0 < (D.R.k : ℝ) * D.s.Del` using `by positivity`. Establish `hBD : 40 * (D.R.m * D.R.k * D.s.Del) ≤ B` using `le_trans (mul_le_mul_of_nonneg_right hCl (by positivity)) (hbD τ 1 le_rfl (by omega))`. Establish `hBD' : 8 * ((D.R.k : ℝ) * D.s.Del) ≤ B` using `by nlinarith`.

Establish `hg : ∀ j, 1 ≤ j → j < D.R.m → bOne D τ j + 1 ≤ bOne D τ (j + 1)` using `fun j h1 h2 => by`. Establish `h3` using `hgap τ j h1 h2`. Establish `h4 : (1 : ℝ) ≤ Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * large₂.sc.L` using `one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (by linarith) (one_le_pow₀ hn)) (one_le_pow₀ hf)) hL`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hmono : ∀ j, 1 ≤ j → j ≤ D.R.m → B ≤ bOne D τ j`.

Introduce `j h1`. Proceed by induction on `j, h1 using Nat.le_induction with`. Consider the case `base => intro _`. Conclude with `le_rfl`. Consider the case `succ j h1 ih => intro h2; linarith [ih (by omega), hg j h1 h2]`.

Use `set c := cfg D u τ with hc`. Establish `hv1 : c.v 1 = vOne D τ 1` using `cfg_v D u τ le_rfl (by omega)`. Establish `htp : c.top = true ↔ IsTop D τ` using `by simp [hc, cfg]`. Establish `hOk : c.Ok`. Use `⟨show 4 ≤ D.R.k by omega, hm2, hD1, (hvw τ _ (by omega) le_rfl).1, ?_, hB1, hg, ?_, fun h => ?_⟩` and prove the remaining obligations.

Rewrite using `[hv1]; exact (hvw τ 1 le_rfl (by omega)).2`. Rewrite using `[hv1]`. Conclude with `ha u τ`. Use `htop τ (htp.1 h)` as an intermediate fact. Conclude with `⟨this.2, show bTop D τ ≤ B - 3 by linarith [this.1]⟩`.

Establish `hSm : c.Small large₂.sc.b`. Use `⟨hb, ?_, fun j h1 h2 => ?_, ?_⟩` and prove the remaining obligations. Use `show 4 * (D.R.m : ℝ) * D.R.k * D.s.Del / B ≤ 1 / 10`. Rewrite using `[div_le_iff₀ (by linarith)]`. Combine the linear equalities and inequalities to obtain the conclusion.

Use `(hbj τ j h1 h2).2` as an intermediate fact. Rewrite `this` using `[Real.rpow_two]`. Then use the resulting hypothesis. Use `show 2 * (D.R.m : ℝ) * Real.log large₂.sc.b / D.R.k ≤ 1 / 10`. Rewrite using `[hlog, div_le_iff₀ (by linarith)]`. Establish `h1 : (D.R.m : ℝ) * large₂.sc.L ≤ (D.R.m : ℝ) ^ 2 * large₂.sc.L` using `by gcongr; nlinarith`.

Establish `h2 : 40 * ((D.R.m : ℝ) ^ 2 * large₂.sc.L) ≤ Cl * ((D.R.m : ℝ) ^ 2 * large₂.sc.L)` using `by gcongr`. Establish `h3 : 0 ≤ (D.R.m : ℝ) * large₂.sc.L` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hpi` using `Real.pi_pos`. Establish `hpi4` using `Real.pi_le_four`.

Establish `hrd : D.host.rdE = 2 * D.host.v` using `by unfold Host.v; ring`. Establish `hgg : 2 * Real.pi ≤ gg D`. Establish `h1 : (5 : ℝ) ≤ ((D.R.k : ℝ) * large₂.sc.b) ^ 8` using `le_trans (by nlinarith) (le_self_pow₀ (by nlinarith) (by norm_num))`. Unfold `gg`. Use the polynomial consequences of the given equalities and inequalities.

Establish `hV : 0 < VV D τ` using `mul_pos (D.dsig_pos τ) (prod_pos fun i _ => by positivity)`. Establish `hlow` using `Final.sz_tcritLower c D.R.rS large₂.sc.b (letters D u) D.host.ka D.host.rdE (gg D) (VV D τ) hOk hm hSm (isWord_letters D u) (by linarith) (by rw [hrd]; unfold Host.ka; field_simp) hgg (by show (1 - 1 / 2) * Sz.Vand (D.R.k + D.R.m - 1) c.lam ≤ _`. Rewrite using `[← cfg_lam D u τ, ← hVV]`. Use the proof step `linarith)`. Express the relevant statement in the definitionally equal form `_ * gg D ^ D.R.m * (D.host.ka ^ (D.R.m - 1))⁻¹ * _ / _ ≤ Sz.Tcrit D.R.k D.R.m _ _ _ _ (Sz.Vand D.R.k _) at hlow`.

Rewrite `hlow` using `[← cfg_u D u τ (hl u τ), ← tcrit_eq D (by linarith)]`. Establish `hg0' : 0 < gg D` using `by linarith`. Establish `hvone` using `(hvw τ 1 le_rfl (by omega)).1`. Establish `hae : 0 < c.aeff ∧ c.aeff ≤ B ^ 4 ∧ 0 ≤ c.vthp ∧ c.vthp ≤ 1`. Unfold `Sz.Cfg.aeff Sz.Cfg.vthp`.

Distinguish the cases in `ht : IsTop D τ`. Rewrite using `[if_pos (htp.2 ht), if_pos (htp.2 ht)]`. Take `⟨t1, t2⟩` from `htop τ ht`. Take `⟨t, ht⟩` from `ht`. Establish `ha0 : 0 < uOne D u τ 1` using `by linarith [ha u τ]`.

Establish `hbp : 0 < bTop D τ` using `by linarith`. Establish `hBt : large₂.sc.b' ≤ B`. Establish `h1` using `large₂.top_b τ t (by omega) ht`. Establish `h2` using `large₂.bT_ge t`. Establish `h3 : B = (((D.hc τ).b ⟨0, by omega⟩ : ℚ) : ℝ)`.

Rewrite using `[hBdef]; unfold bOne; rw [dif_pos ⟨le_rfl, by omega⟩]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hbB : large₂.sc.b ≤ B ^ 2` using `(Real.sqrt_le_left (by linarith)).1 (hb'.trans hBt)`. Establish `hu1 : uOne D u τ 1 ≤ B ^ 3`. Establish `h1` using `(large₂.top_u τ t (by omega) ht).1`.

Establish `h2` using `(large₂.aT_win t).2`. Establish `h3 : uOne D u τ 1 = (((D.hc τ).u ⟨0, by omega⟩ : ℚ) : ℝ)`. Unfold `uOne uS`. Rewrite using `[dif_pos ⟨le_rfl, by omega⟩, ← D.hcW_first u τ (by omega)]`. Establish `hx1` using `large₂.sc.one_lt_alt`.

Establish `h4 : large₂.sc.a ≤ D.R.k * B ^ 2`. Unfold `Scale.a`. Use `gcongr`. Establish `h5 : 0 ≤ large₂.sc.a` using `by unfold Scale.a; positivity`. Establish `h6 : large₂.sc.a / ((D.R.k : ℝ) * large₂.sc.x ^ (Scale.A / 2)) ≤ large₂.sc.a` using `div_le_self h5 (one_le_mul_of_one_le_of_one_le (by linarith) (Real.one_le_rpow hx1.le (by unfold Scale.A; norm_num)))`.

Establish `h7 : (D.R.k : ℝ) ≤ D.R.k * B ^ 2` using `le_mul_of_one_le_right (by linarith) (one_le_pow₀ hB1)`. Establish `h8 : 3 * (D.R.k : ℝ) * B ^ 2 ≤ B * B ^ 2` using `by gcongr`. Establish `h9 : B * B ^ 2 = B ^ 3` using `by ring`. Combine the linear equalities and inequalities to obtain the conclusion. Use `⟨div_pos (mul_pos ha0 hbp) hkD, ?_, ?_, ?_⟩` and prove the remaining obligations.

Use `show uOne D u τ 1 * bTop D τ / ((D.R.k : ℝ) * D.s.Del) ≤ B ^ 4`. Use `(div_le_self (by positivity) (by nlinarith)).trans ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Use `show 0 ≤ 4 * (D.R.k : ℝ) * D.s.Del / bTop D τ`. Check the signs of the components of the expression.

Use `show 4 * (D.R.k : ℝ) * D.s.Del / bTop D τ ≤ 1`. Rewrite using `[div_le_one hbp]`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[if_neg (fun h => ht (htp.1 h)), if_neg (fun h => ht (htp.1 h)), hv1]`. Establish `h1` using `ha u τ`.

Establish `h2` using `ha' u τ ht`. Establish `h3 : B ≤ B ^ 4` using `le_self_pow₀ hB1 (by norm_num)`. Use `⟨?_, ?_, le_rfl, zero_le_one⟩` and prove the remaining obligations. Use `show 0 < uOne D u τ 1 - vOne D τ 1`. Combine the linear equalities and inequalities to obtain the conclusion.

Use `show uOne D u τ 1 - vOne D τ 1 ≤ B ^ 4`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hc1 : 1 / 8 ≤ Sz.cOne c large₂.sc.b`. Unfold `Sz.cOne`. Establish `h1` using `Real.add_one_le_exp (-(2 * c.m * Real.log large₂.sc.b / c.k))`.

Establish `h2` using `hSm.hmu`. Rewrite using `[le_div_iff₀ (by linarith [hae.2.2.1])]`. Combine the linear relations using `[hae.2.2.2]`. Establish `hP : B ^ D.R.m ≤ c.prodb`. Use `prod_le_prod (s := Icc 1 D.R.m) (f := fun _ => B) (g := bOne D τ) (fun _ _ => by linarith) fun j hj => hmono j (mem_Icc.1 hj).1 (mem_Icc.1 hj).2` as an intermediate fact.

Rewrite `this` using `[prod_const, Nat.card_Icc, Nat.add_sub_cancel]`. Conclude with `this`. Establish `hka0 : 0 < D.host.ka` using `div_pos hpi (by linarith)`. Establish `hka : D.host.ka ≤ 4` using `(div_le_self hpi.le hv).trans hpi4`. Establish `hnum` using `num_bound D.R.k D.R.m D.R.rS B c.prodb c.aeff _ _ hm (by exact_mod_cast hmR) (by omega) hB hP hae.1 hae.2.1 hc1 hka0 hka`.

Rewrite using `[Real.rpow_neg hg0'.le, Real.rpow_natCast, le_inv_mul_iff₀ (by positivity)]`. Use `le_trans ?_ hlow` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.
-/
theorem tcrit_low (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 : ℝ) (hCl : 40 ≤ Cl)
    (hVV : ∀ τ, VV D τ = vand (lamSH D.R (D.hc τ))) (hb' : Real.sqrt large₂.sc.b ≤ large₂.sc.b') (hx : large₂.sc.x ≤ D.R.k) :
    UnitaryVolumeMass.stTcritLow D large₂ C' Cl Cg cb Cu cT CT C0 := by
  rintro ⟨hH, hD, -⟩ u τ
  obtain ⟨-, -, -, -, -, -, hmL, hbD, -, -, -, hg0, -, hg1, -, hbj, -, -, hv, hDel, hgap, -, -, hClm, -⟩ := hH
  obtain ⟨hvw, -, ha, ha', hl, htop, -⟩ := hD
  have hk := D.R.m_add_three_le_k
  have hm2 := D.R.two_le_m
  have hm := m_eq D.R
  have hkR : (5 : ℝ) ≤ D.R.k := by exact_mod_cast (by omega : 5 ≤ D.R.k)
  have hmR : (40 : ℝ) ≤ D.R.m := hCl.trans hClm
  have hf : (1 : ℝ) ≤ D.R.f := by
    have : 1 ≤ D.R.f := le_trans (by omega) D.R.m_le_f
    exact_mod_cast this
  have hn : (1 : ℝ) ≤ D.R.r := by
    have : 1 ≤ D.R.r := by unfold Ranks.r; omega
    exact_mod_cast this
  have hL : 1 ≤ large₂.sc.L := Real.one_le_rpow large₂.sc.one_lt_alt.le large₂.sc.eps_pos.le
  have hb : 1 ≤ large₂.sc.b := Real.one_le_exp (by linarith)
  have hlog : Real.log large₂.sc.b = large₂.sc.L := Real.log_exp _
  have hD1 : (1 : ℝ) ≤ D.s.Del :=
    le_trans (Real.one_le_rpow (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (by linarith) hf) hL)
      (by linarith)) hDel
  set B := bOne D τ 1 with hBdef
  have hB : (D.R.k : ℝ) ^ 40 ≤ B := by
    refine le_trans ?_ ((le_max_left _ _).trans (hbj τ 1 le_rfl (by omega)).1)
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by exact_mod_cast hCl)
  have hk2 : 3 * (D.R.k : ℝ) ≤ B := by
    refine le_trans ?_ hB
    calc 3 * (D.R.k : ℝ) ≤ (D.R.k : ℝ) ^ 2 := by nlinarith
      _ ≤ _ := pow_le_pow_right₀ (by linarith) (by norm_num)
  have hB1 : 1 ≤ B := by linarith
  have hkD : 0 < (D.R.k : ℝ) * D.s.Del := by positivity
  have hBD : 40 * (D.R.m * D.R.k * D.s.Del) ≤ B :=
    le_trans (mul_le_mul_of_nonneg_right hCl (by positivity)) (hbD τ 1 le_rfl (by omega))
  have hBD' : 8 * ((D.R.k : ℝ) * D.s.Del) ≤ B := by nlinarith
  have hg : ∀ j, 1 ≤ j → j < D.R.m → bOne D τ j + 1 ≤ bOne D τ (j + 1) := fun j h1 h2 => by
    have h3 := hgap τ j h1 h2
    have h4 : (1 : ℝ) ≤ Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * large₂.sc.L :=
      one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le
        (one_le_mul_of_one_le_of_one_le (by linarith) (one_le_pow₀ hn)) (one_le_pow₀ hf)) hL
    linarith
  have hmono : ∀ j, 1 ≤ j → j ≤ D.R.m → B ≤ bOne D τ j := by
    intro j h1
    induction j, h1 using Nat.le_induction with
    | base => intro _; exact le_rfl
    | succ j h1 ih => intro h2; linarith [ih (by omega), hg j h1 h2]
  set c := cfg D u τ with hc
  have hv1 : c.v 1 = vOne D τ 1 := cfg_v D u τ le_rfl (by omega)
  have htp : c.top = true ↔ IsTop D τ := by simp [hc, cfg]
  have hOk : c.Ok := by
    refine ⟨show 4 ≤ D.R.k by omega, hm2, hD1, (hvw τ _ (by omega) le_rfl).1, ?_, hB1, hg, ?_, fun h => ?_⟩
    · rw [hv1]; exact (hvw τ 1 le_rfl (by omega)).2
    · rw [hv1]; exact ha u τ
    · have := htop τ (htp.1 h)
      exact ⟨this.2, show bTop D τ ≤ B - 3 by linarith [this.1]⟩
  have hSm : c.Small large₂.sc.b := by
    refine ⟨hb, ?_, fun j h1 h2 => ?_, ?_⟩
    · show 4 * (D.R.m : ℝ) * D.R.k * D.s.Del / B ≤ 1 / 10
      rw [div_le_iff₀ (by linarith)]
      linarith
    · have := (hbj τ j h1 h2).2
      rwa [Real.rpow_two] at this
    · show 2 * (D.R.m : ℝ) * Real.log large₂.sc.b / D.R.k ≤ 1 / 10
      rw [hlog, div_le_iff₀ (by linarith)]
      have h1 : (D.R.m : ℝ) * large₂.sc.L ≤ (D.R.m : ℝ) ^ 2 * large₂.sc.L := by gcongr; nlinarith
      have h2 : 40 * ((D.R.m : ℝ) ^ 2 * large₂.sc.L) ≤ Cl * ((D.R.m : ℝ) ^ 2 * large₂.sc.L) := by gcongr
      have h3 : 0 ≤ (D.R.m : ℝ) * large₂.sc.L := by positivity
      linarith
  have hpi := Real.pi_pos
  have hpi4 := Real.pi_le_four
  have hrd : D.host.rdE = 2 * D.host.v := by unfold Host.v; ring
  have hgg : 2 * Real.pi ≤ gg D := by
    have h1 : (5 : ℝ) ≤ ((D.R.k : ℝ) * large₂.sc.b) ^ 8 :=
      le_trans (by nlinarith) (le_self_pow₀ (by nlinarith) (by norm_num))
    unfold gg
    nlinarith
  have hV : 0 < VV D τ := mul_pos (D.dsig_pos τ) (prod_pos fun i _ => by positivity)
  have hlow := Final.sz_tcritLower c D.R.rS large₂.sc.b (letters D u) D.host.ka D.host.rdE (gg D) (VV D τ) hOk hm hSm
    (isWord_letters D u) (by linarith) (by rw [hrd]; unfold Host.ka; field_simp) hgg (by
      show (1 - 1 / 2) * Sz.Vand (D.R.k + D.R.m - 1) c.lam ≤ _
      rw [← cfg_lam D u τ, ← hVV]
      linarith)
  change _ * gg D ^ D.R.m * (D.host.ka ^ (D.R.m - 1))⁻¹ * _ / _ ≤
    Sz.Tcrit D.R.k D.R.m _ _ _ _ (Sz.Vand D.R.k _) at hlow
  rw [← cfg_u D u τ (hl u τ), ← tcrit_eq D (by linarith)] at hlow
  have hg0' : 0 < gg D := by linarith
  have hvone := (hvw τ 1 le_rfl (by omega)).1
  have hae : 0 < c.aeff ∧ c.aeff ≤ B ^ 4 ∧ 0 ≤ c.vthp ∧ c.vthp ≤ 1 := by
    unfold Sz.Cfg.aeff Sz.Cfg.vthp
    by_cases ht : IsTop D τ
    · rw [if_pos (htp.2 ht), if_pos (htp.2 ht)]
      obtain ⟨t1, t2⟩ := htop τ ht
      obtain ⟨t, ht⟩ := ht
      have ha0 : 0 < uOne D u τ 1 := by linarith [ha u τ]
      have hbp : 0 < bTop D τ := by linarith
      have hBt : large₂.sc.b' ≤ B := by
        have h1 := large₂.top_b τ t (by omega) ht
        have h2 := large₂.bT_ge t
        have h3 : B = (((D.hc τ).b ⟨0, by omega⟩ : ℚ) : ℝ) := by
          rw [hBdef]; unfold bOne; rw [dif_pos ⟨le_rfl, by omega⟩]
        linarith
      have hbB : large₂.sc.b ≤ B ^ 2 := (Real.sqrt_le_left (by linarith)).1 (hb'.trans hBt)
      have hu1 : uOne D u τ 1 ≤ B ^ 3 := by
        have h1 := (large₂.top_u τ t (by omega) ht).1
        have h2 := (large₂.aT_win t).2
        have h3 : uOne D u τ 1 = (((D.hc τ).u ⟨0, by omega⟩ : ℚ) : ℝ) := by
          unfold uOne uS
          rw [dif_pos ⟨le_rfl, by omega⟩, ← D.hcW_first u τ (by omega)]
        have hx1 := large₂.sc.one_lt_alt
        have h4 : large₂.sc.a ≤ D.R.k * B ^ 2 := by
          unfold Scale.a
          gcongr
        have h5 : 0 ≤ large₂.sc.a := by unfold Scale.a; positivity
        have h6 : large₂.sc.a / ((D.R.k : ℝ) * large₂.sc.x ^ (Scale.A / 2)) ≤ large₂.sc.a :=
          div_le_self h5 (one_le_mul_of_one_le_of_one_le (by linarith)
            (Real.one_le_rpow hx1.le (by unfold Scale.A; norm_num)))
        have h7 : (D.R.k : ℝ) ≤ D.R.k * B ^ 2 := le_mul_of_one_le_right (by linarith) (one_le_pow₀ hB1)
        have h8 : 3 * (D.R.k : ℝ) * B ^ 2 ≤ B * B ^ 2 := by gcongr
        have h9 : B * B ^ 2 = B ^ 3 := by ring
        linarith
      refine ⟨div_pos (mul_pos ha0 hbp) hkD, ?_, ?_, ?_⟩
      · show uOne D u τ 1 * bTop D τ / ((D.R.k : ℝ) * D.s.Del) ≤ B ^ 4
        refine (div_le_self (by positivity) (by nlinarith)).trans ?_
        calc uOne D u τ 1 * bTop D τ ≤ B ^ 3 * B := by gcongr; linarith
          _ = B ^ 4 := by ring
      · show 0 ≤ 4 * (D.R.k : ℝ) * D.s.Del / bTop D τ
        positivity
      · show 4 * (D.R.k : ℝ) * D.s.Del / bTop D τ ≤ 1
        rw [div_le_one hbp]
        linarith
    · rw [if_neg (fun h => ht (htp.1 h)), if_neg (fun h => ht (htp.1 h)), hv1]
      have h1 := ha u τ
      have h2 := ha' u τ ht
      have h3 : B ≤ B ^ 4 := le_self_pow₀ hB1 (by norm_num)
      refine ⟨?_, ?_, le_rfl, zero_le_one⟩
      · show 0 < uOne D u τ 1 - vOne D τ 1
        linarith
      · show uOne D u τ 1 - vOne D τ 1 ≤ B ^ 4
        linarith
  have hc1 : 1 / 8 ≤ Sz.cOne c large₂.sc.b := by
    unfold Sz.cOne
    have h1 := Real.add_one_le_exp (-(2 * c.m * Real.log large₂.sc.b / c.k))
    have h2 := hSm.hmu
    rw [le_div_iff₀ (by linarith [hae.2.2.1])]
    linarith [hae.2.2.2]
  have hP : B ^ D.R.m ≤ c.prodb := by
    have := prod_le_prod (s := Icc 1 D.R.m) (f := fun _ => B) (g := bOne D τ) (fun _ _ => by linarith)
      fun j hj => hmono j (mem_Icc.1 hj).1 (mem_Icc.1 hj).2
    rw [prod_const, Nat.card_Icc, Nat.add_sub_cancel] at this
    exact this
  have hka0 : 0 < D.host.ka := div_pos hpi (by linarith)
  have hka : D.host.ka ≤ 4 := (div_le_self hpi.le hv).trans hpi4
  have hnum := num_bound D.R.k D.R.m D.R.rS B c.prodb c.aeff _ _ hm (by exact_mod_cast hmR) (by omega) hB hP
    hae.1 hae.2.1 hc1 hka0 hka
  rw [Real.rpow_neg hg0'.le, Real.rpow_natCast, le_inv_mul_iff₀ (by positivity)]
  refine le_trans ?_ hlow
  calc gg D ^ D.R.m * (D.R.k : ℝ) ^ (3 * D.R.rS)
      ≤ gg D ^ D.R.m * (Sz.cOne c large₂.sc.b * (D.host.ka ^ (D.R.m - 1))⁻¹ * c.prodb / c.aeff) := by gcongr
    _ = _ := by ring

end GlobalTheory.CritLevel
