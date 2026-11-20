import Formalism.HermitianCurvature.HermitianCurvatureProofs.OpLEqZeroOfEventually
import Formalism.FormalDegreeBessel.FormalDegreeRatio.GroupFactorizationHolds
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactGroupHaarExists
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OppositeWeylSubgroupClosed
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TheoremPIntegralOfPlaces

open Matrix MeasureTheory Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerC

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerA Formalism.FourierDecayAlt.P5.HerB

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section Minors

variable {k r : ℕ}

def pc (c : Fin r → ℂ) : ℂ := ∏ a : Fin r with a.val < (Fin.last r).val, c a

/- English proof (translation)
Unfold `pc`. Conclude with `continuous_finset_prod _ fun a _ => continuous_apply a`.
-/
theorem pc_continuous : Continuous (pc (r := r)) := by
  unfold pc
  exact continuous_finset_prod _ fun a _ => continuous_apply a

/- English proof (translation)
The claim follows from `Finset.prod_ne_zero_iff.2 fun a _ => hc a`.
-/
theorem pc_ne_zero {c : Fin r → ℂ} (hc : c ∈ OmX r) : pc c ≠ 0 := Finset.prod_ne_zero_iff.2 fun a _ => hc a

/- English proof (translation)
Take `⟨μ, _, rfl⟩` from `(Formalism.FourierDecayAlt.P.TwoByOneBlock.UWb_iff g).1 (Formalism.FourierDecayAlt.P5.Rad.glev_last_uwb hg)`. Establish `e : wCell k r (Fin.last r) c * Formalism.FourierDecayAlt.B2.embWb k r μ = bigCell k r c μ`. Rewrite using `[Formalism.FourierDecayAlt.P5.Rad.wCell_last_eq, ← (Formalism.FourierDecayAlt.P.bruhat_big_cell_factorization k r c μ).1]`. Rewrite using `[e]`. Establish `hmin` using `big_cell_minors_holds k r z z' c μ hz hz'`.

Establish `hζ : herm (Hpk k r) (bigCell k r c μ *ᵥ z') z = zetaL k r z z' (Fin.last r) (Formalism.FourierDecayAlt.B2.embWb k r μ)`. Rewrite using `[Formalism.FourierDecayAlt.P5.Rad.zetaL_last, ← Formalism.FourierDecayAlt.P.TwoByOneBlock.jV_wbPart hz', Formalism.FourierDecayAlt.P.BigCellHermitian.bigCell_mulVec_jV, Formalism.FourierDecayAlt.P.TwoByOneBlock.emb_mulVec_jV]`. Establish `hr : Dmin k r z z' (bigCell k r c μ) ⟨r, by omega⟩ = pc c` using `hmin.1 (Fin.last r)`. Use `⟨hr, ?_⟩` and prove the remaining obligations. Establish `hzeta` using `hmin.2.2 hc`.

Rewrite `hzeta` using `[hζ]`. Unfold `Formalism.QuantumDeterminants.zeta at hzeta`. Rewrite `hzeta` using `[hr]`. Establish `h2` using `div_mul_cancel₀ (Dmin k r z z' (bigCell k r c μ) (Fin.last (r + 1))) (pc_ne_zero hc)`. Rewrite `h2` using `[hzeta]`.

Conclude with `h2.symm`.
-/
theorem dmin_wCell {z z' : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hz' : inWb k r z') {c : Fin r → ℂ}
    (hc : c ∈ OmX r) {g : Mx k r} (hg : g ∈ Glev k r (Fin.last r)) :
    Dmin k r z z' (wCell k r (Fin.last r) c * g) ⟨r, by omega⟩ = pc c ∧
      Dmin k r z z' (wCell k r (Fin.last r) c * g) (Fin.last (r + 1)) = zetaL k r z z' (Fin.last r) g * pc c := by
  obtain ⟨μ, _, rfl⟩ := (Formalism.FourierDecayAlt.P.TwoByOneBlock.UWb_iff g).1 (Formalism.FourierDecayAlt.P5.Rad.glev_last_uwb hg)
  have e : wCell k r (Fin.last r) c * Formalism.FourierDecayAlt.B2.embWb k r μ = bigCell k r c μ := by
    rw [Formalism.FourierDecayAlt.P5.Rad.wCell_last_eq, ← (Formalism.FourierDecayAlt.P.bruhat_big_cell_factorization k r c μ).1]
  rw [e]
  have hmin := big_cell_minors_holds k r z z' c μ hz hz'
  have hζ : herm (Hpk k r) (bigCell k r c μ *ᵥ z') z = zetaL k r z z' (Fin.last r) (Formalism.FourierDecayAlt.B2.embWb k r μ) := by
    rw [Formalism.FourierDecayAlt.P5.Rad.zetaL_last, ← Formalism.FourierDecayAlt.P.TwoByOneBlock.jV_wbPart hz', Formalism.FourierDecayAlt.P.BigCellHermitian.bigCell_mulVec_jV,
      Formalism.FourierDecayAlt.P.TwoByOneBlock.emb_mulVec_jV]
  have hr : Dmin k r z z' (bigCell k r c μ) ⟨r, by omega⟩ = pc c := hmin.1 (Fin.last r)
  refine ⟨hr, ?_⟩
  have hzeta := hmin.2.2 hc
  rw [hζ] at hzeta
  unfold Formalism.QuantumDeterminants.zeta at hzeta
  rw [hr] at hzeta
  have h2 := div_mul_cancel₀ (Dmin k r z z' (bigCell k r c μ) (Fin.last (r + 1))) (pc_ne_zero hc)
  rw [hzeta] at h2
  exact h2.symm

end Minors

/- English proof (translation)
Introduce `Wp Wq _ _ _ _ _ _ P z z' π π' D F Φ _hP hz hz' hπ hπ' hF hΦ`. Substitute `hz hz' hπ hπ'` using the available equality. Take `⟨⟨_, ε, hε, hG⟩, hC⟩` from `hF`. Establish `hW` using `Formalism.FourierDecayAlt.P.weyl_subgroup_closed P.k P.r`. Establish `hN` using `Formalism.FourierDecayAlt.P.unipotent_radical_closed P.k P.r`.

Establish `hGV` using `Formalism.FourierDecayAlt.P.unitary_group_closed P.k P.r`. Use `Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite D.haarW` as an intermediate fact. Use `Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite D.haarN` as an intermediate fact. Use `Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite D.haarW'` as an intermediate fact. Establish `hcont : Continuous (fun h : Mx P.k P.r => Dmin P.k P.r D.z D.z' h (Fin.last (P.r + 1)))` using `(Formalism.FourierDecayAlt.P.JCx1.contDiff_Dmin D.z D.z' (Fin.last (P.r + 1))).continuous`.

Take `⟨R0, hR0⟩` from `hC.isCompact.exists_bound_of_continuousOn hcont.continuousOn`. Establish `hae : ∀ᵐ (p : (Mt P.k P.r × Mt P.k P.r) × (Mt P.k P.r × Mt P.k P.r)) ∂((D.μW.prod D.μN).prod (D.μW'.prod D.μN)), (Matrix.of p.1.1 ∈ UWset P.k P.r D.z ∧ Matrix.of p.1.2 ∈ Formalism.QuantumDeterminants.Nset P.k P.r) ∧ (Matrix.of p.2.1 ∈ UWset P.k P.r D.z' ∧ Matrix.of p.2.2 ∈ Formal …`. Establish `hw : ∀ᵐ (a : Mt P.k P.r) ∂D.μW, Matrix.of a ∈ UWset P.k P.r D.z` using `(measure_eq_zero_iff_ae_notMem.1 D.haarW.conc).mono fun a ha => not_not.1 ha`. Establish `hn : ∀ᵐ (a : Mt P.k P.r) ∂D.μN, Matrix.of a ∈ Formalism.QuantumDeterminants.Nset P.k P.r` using `(measure_eq_zero_iff_ae_notMem.1 D.haarN.conc).mono fun a ha => not_not.1 ha`. Establish `hw' : ∀ᵐ (a : Mt P.k P.r) ∂D.μW', Matrix.of a ∈ UWset P.k P.r D.z'` using `(measure_eq_zero_iff_ae_notMem.1 D.haarW'.conc).mono fun a ha => not_not.1 ha`.

Establish `h1 : ∀ᵐ (q : Mt P.k P.r × Mt P.k P.r) ∂(D.μW.prod D.μN), Matrix.of q.1 ∈ UWset P.k P.r D.z ∧ Matrix.of q.2 ∈ Formalism.QuantumDeterminants.Nset P.k P.r` using `(Measure.quasiMeasurePreserving_fst.ae hw).and (Measure.quasiMeasurePreserving_snd.ae hn)`. Establish `h2 : ∀ᵐ (q : Mt P.k P.r × Mt P.k P.r) ∂(D.μW'.prod D.μN), Matrix.of q.1 ∈ UWset P.k P.r D.z' ∧ Matrix.of q.2 ∈ Formalism.QuantumDeterminants.Nset P.k P.r` using `(Measure.quasiMeasurePreserving_fst.ae hw').and (Measure.quasiMeasurePreserving_snd.ae hn)`. Conclude with `(Measure.quasiMeasurePreserving_fst.ae h1).and (Measure.quasiMeasurePreserving_snd.ae h2)`. Introduce `c hc`. Use `set p0 : ℝ := ‖pc c‖ with hp0`.

Establish `hp0pos : 0 < p0` using `norm_pos_iff.2 (pc_ne_zero hc)`. Use `set U : Set (Fin P.r → ℂ) := {c' | p0 / 2 < ‖pc c'‖ ∧ ‖pc c'‖ < 2 * p0} with hU`. Establish `hUo : IsOpen U` using `(isOpen_lt continuous_const (continuous_norm.comp pc_continuous)).inter (isOpen_lt (continuous_norm.comp pc_continuous) continuous_const)`. Establish `hcU : c ∈ U` using `⟨by linarith, by linarith⟩`. Use `set e' : ℝ := ε / (2 * p0) ^ 2 with he'`.

Use `set R' : ℝ := R0 / (p0 / 2) with hR'`. Establish `he'pos : 0 < e'` using `div_pos hε (by positivity)`. Use `⟨U, hUo, hcU, {g | g ∈ Glev P.k P.r (Fin.last P.r) ∧ e' ≤ GGl P.k P.r D.z D.z' g ∧ ‖zetaL P.k P.r D.z D.z' (Fin.last P.r) g‖ ≤ R'}, isCompact_zeta_le D.z D.z' D.z_mem D.z'_mem D.T_pos D.T'_pos e' R', fun g hg => lt_of_lt_of_le he'pos hg.2.1, ?_⟩` and prove the remaining obligations. Introduce `c' hc' g hg hgK`. Distinguish the cases in `hd : (c', g) ∈ DomR P.k P.r D.z D.z'`.

Use `swap`. Conclude with `radSp_zero_off Φ (x := (c', g)) hd`. Rewrite using `[hΦ (c', g) hd]`. Unfold `resG`. Establish `hc'O : c' ∈ OmX P.r` using `hd.1`.

Use `set x : Mx P.k P.r := wCell P.k P.r (Fin.last P.r) c' * g with hx`. Take `⟨hDr, hDl⟩` from `dmin_wCell D.z_mem D.z'_mem hc'O hg`. Rewrite `hDr`, `hDl` using `[← hx]`. Establish `hxG : x ∈ B.GV P.k P.r` using `hGV.mul_mem _ (Formalism.FourierDecayAlt.P.Qx3.wlist_glev hc'O _).1 _ hg.1`. Establish `hF0 : ∀ y ∈ B.GV P.k P.r, Dmin P.k P.r D.z D.z' y ⟨P.r, by omega⟩ = pc c' → Dmin P.k P.r D.z D.z' y (Fin.last (P.r + 1)) = zetaL P.k P.r D.z D.z' (Fin.last P.r) g * pc c' → F y = 0`.

Introduce `y hy hyr hyl`. Assume the negation of the conclusion as `hFy`. Apply `hgK` to reduce the goal to its premises. Establish `hsupp : y ∈ tsupport F` using `subset_tsupport F hFy`. Establish `hb` using `hR0 y hsupp`.

Establish `hGy` using `hG y hy hFy`. Rewrite `hb` using `[hyl]`. Establish `hGy' : Gf P.k P.r D.z D.z' y = Complex.normSq (pc c') * GGl P.k P.r D.z D.z' g`. Unfold `Formalism.QuantumDeterminants.Gf GGl`. Rewrite using `[hyr, hyl, Complex.normSq_mul]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hpc1 : p0 / 2 < ‖pc c'‖` using `hc'.1`. Establish `hpc2 : ‖pc c'‖ < 2 * p0` using `hc'.2`. Establish `hpcpos : 0 < ‖pc c'‖` using `by linarith`. Establish `hns : Complex.normSq (pc c') = ‖pc c'‖ ^ 2` using `by rw [Complex.sq_norm]`.

Use `⟨hg, ?_, ?_⟩` and prove the remaining obligations. Establish `hGG : ε ≤ ‖pc c'‖ ^ 2 * GGl P.k P.r D.z D.z' g` using `by rw [← hns, ← hGy']; exact hGy`. Establish `hGGpos : 0 < GGl P.k P.r D.z D.z' g` using `hd.2.2`. Establish `hsq : ‖pc c'‖ ^ 2 ≤ (2 * p0) ^ 2` using `by nlinarith`. Rewrite using `[he', div_le_iff₀ (by positivity)]`.

Use the polynomial consequences of the given equalities and inequalities. Rewrite `hb` using `[norm_mul]`. Establish `hz0 : 0 ≤ ‖zetaL P.k P.r D.z D.z' (Fin.last P.r) g‖` using `norm_nonneg _`. Establish `hR0nn : 0 ≤ R0` using `le_trans (by positivity) hb`. Rewrite using `[hR', le_div_iff₀ (by positivity)]`.

Use the polynomial consequences of the given equalities and inequalities. Establish `hJ0 : B.JF D F x = 0`. Unfold `B.JF besselJ`. Use `integral_eq_zero_of_ae (hae.mono fun p hp => ?_)` and prove the remaining obligations. Take `⟨⟨ha, hn⟩, ⟨ha', hn'⟩⟩` from `hp`.

Use `set a := Matrix.of p.1.1`. Use `set n := Matrix.of p.1.2`. Use `set a' := Matrix.of p.2.1`. Use `set n' := Matrix.of p.2.2`. Establish `hainv : a⁻¹ ∈ UWset P.k P.r D.z` using `(hW D.z).inv_mem _ ha`.

Establish `hninv : n⁻¹ ∈ Formalism.QuantumDeterminants.Nset P.k P.r` using `hN.inv_mem _ hn`. Establish `hs1 : a⁻¹ * n⁻¹ ∈ Formalism.QuantumDeterminants.Sset P.k P.r D.z` using `⟨a⁻¹, hainv, n⁻¹, hninv, rfl⟩`. Establish `hs2 : n' ∈ Formalism.QuantumDeterminants.Sset P.k P.r D.z'` using `⟨1, (hW D.z').one_mem, n', hn', (one_mul _).symm⟩`. Establish `hs3 : (1 : Mx P.k P.r) ∈ Formalism.QuantumDeterminants.Sset P.k P.r D.z` using `⟨1, (hW D.z).one_mem, 1, hN.one_mem, (mul_one _).symm⟩`. Establish `hs4 : a' ∈ Formalism.QuantumDeterminants.Sset P.k P.r D.z'` using `⟨a', ha', 1, hN.one_mem, (mul_one _).symm⟩`.

Establish `hinvD : ∀ l, Dmin P.k P.r D.z D.z' (a⁻¹ * n⁻¹ * x * n' * a') l = Dmin P.k P.r D.z D.z' x l`. Introduce `l`. Establish `e1` using `diagonal_inverse_holds P.k P.r D.z D.z' D.z_mem D.z'_mem 1 hs3 a' hs4 (a⁻¹ * n⁻¹ * x * n') l`. Rewrite `e1` using `[one_mul]`. Rewrite using `[e1]`.

Conclude with `diagonal_inverse_holds P.k P.r D.z D.z' D.z_mem D.z'_mem _ hs1 n' hs2 x l`. Establish `hyG : a⁻¹ * n⁻¹ * x * n' * a' ∈ B.GV P.k P.r` using `hGV.mul_mem _ (hGV.mul_mem _ (hGV.mul_mem _ (hGV.mul_mem _ hainv.1 _ hninv.1) _ hxG) _ hn'.1) _ ha'.1`. Establish `hFy : F (a⁻¹ * n⁻¹ * x * n' * a') = 0` using `hF0 _ hyG (by rw [hinvD]; exact hDr) (by rw [hinvD]; exact hDl)`. Establish `hxy : (Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ * x * Matrix.of p.2.2 * Matrix.of p.2.1 = a⁻¹ * n⁻¹ * x * n' * a'` using `rfl`. Simplify using `only [hxy, hFy, ContinuousLinearMap.comp_zero, ContinuousLinearMap.zero_comp, smul_zero, Pi.zero_apply]`.

Rewrite using `[hJ0, smul_zero]`.
-/
theorem jfCptLocAll : JFCptLocAll := by
  intro Wp Wq _ _ _ _ _ _ P z z' π π' D F Φ _hP hz hz' hπ hπ' hF hΦ
  subst hz hz' hπ hπ'
  obtain ⟨⟨_, ε, hε, hG⟩, hC⟩ := hF
  have hW := Formalism.FourierDecayAlt.P.weyl_subgroup_closed P.k P.r
  have hN := Formalism.FourierDecayAlt.P.unipotent_radical_closed P.k P.r
  have hGV := Formalism.FourierDecayAlt.P.unitary_group_closed P.k P.r
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite D.haarW
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite D.haarN
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite D.haarW'

  have hcont : Continuous (fun h : Mx P.k P.r => Dmin P.k P.r D.z D.z' h (Fin.last (P.r + 1))) :=
    (Formalism.FourierDecayAlt.P.JCx1.contDiff_Dmin D.z D.z' (Fin.last (P.r + 1))).continuous
  obtain ⟨R0, hR0⟩ := hC.isCompact.exists_bound_of_continuousOn hcont.continuousOn

  have hae : ∀ᵐ (p : (Mt P.k P.r × Mt P.k P.r) × (Mt P.k P.r × Mt P.k P.r)) ∂((D.μW.prod D.μN).prod (D.μW'.prod D.μN)),
      (Matrix.of p.1.1 ∈ UWset P.k P.r D.z ∧ Matrix.of p.1.2 ∈ Formalism.QuantumDeterminants.Nset P.k P.r) ∧
        (Matrix.of p.2.1 ∈ UWset P.k P.r D.z' ∧ Matrix.of p.2.2 ∈ Formalism.QuantumDeterminants.Nset P.k P.r) := by
    have hw : ∀ᵐ (a : Mt P.k P.r) ∂D.μW, Matrix.of a ∈ UWset P.k P.r D.z :=
      (measure_eq_zero_iff_ae_notMem.1 D.haarW.conc).mono fun a ha => not_not.1 ha
    have hn : ∀ᵐ (a : Mt P.k P.r) ∂D.μN, Matrix.of a ∈ Formalism.QuantumDeterminants.Nset P.k P.r :=
      (measure_eq_zero_iff_ae_notMem.1 D.haarN.conc).mono fun a ha => not_not.1 ha
    have hw' : ∀ᵐ (a : Mt P.k P.r) ∂D.μW', Matrix.of a ∈ UWset P.k P.r D.z' :=
      (measure_eq_zero_iff_ae_notMem.1 D.haarW'.conc).mono fun a ha => not_not.1 ha
    have h1 : ∀ᵐ (q : Mt P.k P.r × Mt P.k P.r) ∂(D.μW.prod D.μN), Matrix.of q.1 ∈ UWset P.k P.r D.z ∧ Matrix.of q.2 ∈ Formalism.QuantumDeterminants.Nset P.k P.r :=
      (Measure.quasiMeasurePreserving_fst.ae hw).and (Measure.quasiMeasurePreserving_snd.ae hn)
    have h2 : ∀ᵐ (q : Mt P.k P.r × Mt P.k P.r) ∂(D.μW'.prod D.μN), Matrix.of q.1 ∈ UWset P.k P.r D.z' ∧ Matrix.of q.2 ∈ Formalism.QuantumDeterminants.Nset P.k P.r :=
      (Measure.quasiMeasurePreserving_fst.ae hw').and (Measure.quasiMeasurePreserving_snd.ae hn)
    exact (Measure.quasiMeasurePreserving_fst.ae h1).and (Measure.quasiMeasurePreserving_snd.ae h2)
  intro c hc
  set p0 : ℝ := ‖pc c‖ with hp0
  have hp0pos : 0 < p0 := norm_pos_iff.2 (pc_ne_zero hc)
  set U : Set (Fin P.r → ℂ) := {c' | p0 / 2 < ‖pc c'‖ ∧ ‖pc c'‖ < 2 * p0} with hU
  have hUo : IsOpen U :=
    (isOpen_lt continuous_const (continuous_norm.comp pc_continuous)).inter
      (isOpen_lt (continuous_norm.comp pc_continuous) continuous_const)
  have hcU : c ∈ U := ⟨by linarith, by linarith⟩
  set e' : ℝ := ε / (2 * p0) ^ 2 with he'
  set R' : ℝ := R0 / (p0 / 2) with hR'
  have he'pos : 0 < e' := div_pos hε (by positivity)
  refine ⟨U, hUo, hcU, {g | g ∈ Glev P.k P.r (Fin.last P.r) ∧ e' ≤ GGl P.k P.r D.z D.z' g ∧
      ‖zetaL P.k P.r D.z D.z' (Fin.last P.r) g‖ ≤ R'},
    isCompact_zeta_le D.z D.z' D.z_mem D.z'_mem D.T_pos D.T'_pos e' R', fun g hg => lt_of_lt_of_le he'pos hg.2.1, ?_⟩
  intro c' hc' g hg hgK
  by_cases hd : (c', g) ∈ DomR P.k P.r D.z D.z'
  swap
  · exact radSp_zero_off Φ (x := (c', g)) hd
  rw [hΦ (c', g) hd]
  unfold resG
  have hc'O : c' ∈ OmX P.r := hd.1
  set x : Mx P.k P.r := wCell P.k P.r (Fin.last P.r) c' * g with hx
  obtain ⟨hDr, hDl⟩ := dmin_wCell D.z_mem D.z'_mem hc'O hg
  rw [← hx] at hDr hDl
  have hxG : x ∈ B.GV P.k P.r := hGV.mul_mem _ (Formalism.FourierDecayAlt.P.Qx3.wlist_glev hc'O _).1 _ hg.1

  have hF0 : ∀ y ∈ B.GV P.k P.r, Dmin P.k P.r D.z D.z' y ⟨P.r, by omega⟩ = pc c' →
      Dmin P.k P.r D.z D.z' y (Fin.last (P.r + 1)) = zetaL P.k P.r D.z D.z' (Fin.last P.r) g * pc c' → F y = 0 := by
    intro y hy hyr hyl
    by_contra hFy
    apply hgK
    have hsupp : y ∈ tsupport F := subset_tsupport F hFy
    have hb := hR0 y hsupp
    have hGy := hG y hy hFy
    rw [hyl] at hb
    have hGy' : Gf P.k P.r D.z D.z' y = Complex.normSq (pc c') * GGl P.k P.r D.z D.z' g := by
      unfold Formalism.QuantumDeterminants.Gf GGl
      rw [hyr, hyl, Complex.normSq_mul]
      ring
    have hpc1 : p0 / 2 < ‖pc c'‖ := hc'.1
    have hpc2 : ‖pc c'‖ < 2 * p0 := hc'.2
    have hpcpos : 0 < ‖pc c'‖ := by linarith
    have hns : Complex.normSq (pc c') = ‖pc c'‖ ^ 2 := by rw [Complex.sq_norm]
    refine ⟨hg, ?_, ?_⟩
    ·
      have hGG : ε ≤ ‖pc c'‖ ^ 2 * GGl P.k P.r D.z D.z' g := by rw [← hns, ← hGy']; exact hGy
      have hGGpos : 0 < GGl P.k P.r D.z D.z' g := hd.2.2
      have hsq : ‖pc c'‖ ^ 2 ≤ (2 * p0) ^ 2 := by nlinarith
      rw [he', div_le_iff₀ (by positivity)]
      nlinarith
    ·
      rw [norm_mul] at hb
      have hz0 : 0 ≤ ‖zetaL P.k P.r D.z D.z' (Fin.last P.r) g‖ := norm_nonneg _
      have hR0nn : 0 ≤ R0 := le_trans (by positivity) hb
      rw [hR', le_div_iff₀ (by positivity)]
      nlinarith
  have hJ0 : B.JF D F x = 0 := by
    unfold B.JF besselJ
    refine integral_eq_zero_of_ae (hae.mono fun p hp => ?_)
    obtain ⟨⟨ha, hn⟩, ⟨ha', hn'⟩⟩ := hp
    set a := Matrix.of p.1.1
    set n := Matrix.of p.1.2
    set a' := Matrix.of p.2.1
    set n' := Matrix.of p.2.2
    have hainv : a⁻¹ ∈ UWset P.k P.r D.z := (hW D.z).inv_mem _ ha
    have hninv : n⁻¹ ∈ Formalism.QuantumDeterminants.Nset P.k P.r := hN.inv_mem _ hn
    have hs1 : a⁻¹ * n⁻¹ ∈ Formalism.QuantumDeterminants.Sset P.k P.r D.z := ⟨a⁻¹, hainv, n⁻¹, hninv, rfl⟩
    have hs2 : n' ∈ Formalism.QuantumDeterminants.Sset P.k P.r D.z' := ⟨1, (hW D.z').one_mem, n', hn', (one_mul _).symm⟩
    have hs3 : (1 : Mx P.k P.r) ∈ Formalism.QuantumDeterminants.Sset P.k P.r D.z := ⟨1, (hW D.z).one_mem, 1, hN.one_mem, (mul_one _).symm⟩
    have hs4 : a' ∈ Formalism.QuantumDeterminants.Sset P.k P.r D.z' := ⟨a', ha', 1, hN.one_mem, (mul_one _).symm⟩
    have hinvD : ∀ l, Dmin P.k P.r D.z D.z' (a⁻¹ * n⁻¹ * x * n' * a') l = Dmin P.k P.r D.z D.z' x l := by
      intro l
      have e1 := diagonal_inverse_holds P.k P.r D.z D.z' D.z_mem D.z'_mem 1 hs3 a' hs4 (a⁻¹ * n⁻¹ * x * n') l
      rw [one_mul] at e1
      rw [e1]
      exact diagonal_inverse_holds P.k P.r D.z D.z' D.z_mem D.z'_mem _ hs1 n' hs2 x l
    have hyG : a⁻¹ * n⁻¹ * x * n' * a' ∈ B.GV P.k P.r :=
      hGV.mul_mem _ (hGV.mul_mem _ (hGV.mul_mem _ (hGV.mul_mem _ hainv.1 _ hninv.1) _ hxG) _ hn'.1) _ ha'.1
    have hFy : F (a⁻¹ * n⁻¹ * x * n' * a') = 0 :=
      hF0 _ hyG (by rw [hinvD]; exact hDr) (by rw [hinvD]; exact hDl)
    have hxy : (Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ * x * Matrix.of p.2.2 * Matrix.of p.2.1 =
        a⁻¹ * n⁻¹ * x * n' * a' := rfl
    simp only [hxy, hFy, ContinuousLinearMap.comp_zero, ContinuousLinearMap.zero_comp, smul_zero, Pi.zero_apply]
  rw [hJ0, smul_zero]

/- English proof (translation)
The claim follows from `herCptTopAll_of_jf jfCptLocAll`.
-/
theorem herCptTopAll : HerCptTopAll := herCptTopAll_of_jf jfCptLocAll

/- English proof (translation)
The claim follows from `thmPActualCpt_of_jf jfCptLocAll hSF`.
-/
theorem thmPActualCpt_of_stepForm (hSF : StepFormCptAll) : ThmPActualCpt := thmPActualCpt_of_jf jfCptLocAll hSF

end Formalism.FourierDecayAlt.P5.HerC
