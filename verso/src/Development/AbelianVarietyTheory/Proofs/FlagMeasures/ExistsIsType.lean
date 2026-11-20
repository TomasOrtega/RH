import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Formalism.HermitianCurvature.WeylElementCommutesLevelOne
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ContinuousMulMt
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DifferentialOperatorBracket
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SupExistsOfInterlaced
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CapelliDetFrameIndep

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.CapelliOfHC

open PI.UpqRep PI.HwUniqW GlobalTheory.BesselFrame GlobalTheory.SupNonzero

variable {k r : ℕ} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
  {z : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (W →L[ℂ] W)}

/- English proof (translation)
Establish `hunit : IsUnit g`. Establish `hgg` using `(Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.uh_inv (Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.uh_eq ▸ hg.1)).2`. Conclude with `⟨⟨g, g⁻¹, hgg.1, hgg.2⟩, rfl⟩`. Establish `hs : ∀ a b : Fin k, Matrix.single a b (Z a b) = Z a b • Matrix.single a b (1 : ℂ)` using `fun a b => by`. Rewrite using `[Matrix.smul_single, smul_eq_mul, mul_one]`.

Establish `hu : ∀ a b : Fin k, Q.unitB (Formalism.QuantumDeterminants.Hpk k r) (fun a => g *ᵥ bvec (bl k r a)) a b = g * incl k r * Matrix.single a b (1 : ℂ) * ((incl k r)ᴴ * g⁻¹)` using `fun a b => by`. Rewrite using `[unitB_eq, co_eq hg.1]`. Rewrite using `[blockW_eq, ← exp_corner (incl k r) (incl k r)ᴴ incl_incl, ← Matrix.exp_conj g _ hunit]`. Use `congr 1`. Use `conv_lhs => rw [Matrix.matrix_eq_sum_single Z]`.

Simplify using `only [hu, hs, Finset.smul_sum, Matrix.mul_sum, Matrix.sum_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc, smul_smul]`.
-/
private theorem conj_blockW_exp_eq_exp_unitB {g : Mx k r} (hg : IsFrameW k r z g) (Z : Matrix (Fin k) (Fin k) ℂ) (t : ℝ) :
    g * blockW k r (NormedSpace.exp ((t : ℂ) • Z)) * g⁻¹ = NormedSpace.exp ((t : ℂ) •
      ∑ a, ∑ b, Z a b • Q.unitB (Formalism.QuantumDeterminants.Hpk k r) (fun a => g *ᵥ bvec (bl k r a)) a b) := by
  have hunit : IsUnit g := by
    have hgg := (Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.uh_inv (Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.uh_eq ▸ hg.1)).2
    exact ⟨⟨g, g⁻¹, hgg.1, hgg.2⟩, rfl⟩
  have hs : ∀ a b : Fin k, Matrix.single a b (Z a b) = Z a b • Matrix.single a b (1 : ℂ) := fun a b => by
    rw [Matrix.smul_single, smul_eq_mul, mul_one]
  have hu : ∀ a b : Fin k, Q.unitB (Formalism.QuantumDeterminants.Hpk k r) (fun a => g *ᵥ bvec (bl k r a)) a b =
      g * incl k r * Matrix.single a b (1 : ℂ) * ((incl k r)ᴴ * g⁻¹) := fun a b => by
    rw [unitB_eq, co_eq hg.1]
  rw [blockW_eq, ← exp_corner (incl k r) (incl k r)ᴴ incl_incl, ← Matrix.exp_conj g _ hunit]
  congr 1
  conv_lhs => rw [Matrix.matrix_eq_sum_single Z]
  simp only [hu, hs, Finset.smul_sum, Matrix.mul_sum, Matrix.sum_mul, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.mul_assoc, smul_smul]

/- English proof (translation)
Take `⟨g, hg, hU⟩` from `h₀`. Establish `hB : Q.IsFrameOf k r [z] (fun a => g *ᵥ bvec (bl k r a))` using `isFrameOf hg`. Use `⟨fun a => g *ᵥ bvec (bl k r a), hB, ?_⟩` and prove the remaining obligations. Establish `hgl` using `(Formalism.FourierDecayAlt.P.frame_general_linear W k r k z π _ hR hB).1`. Use `qdet_eigen hU _ hgl ?_` and prove the remaining obligations.

Introduce `Z hZ v`. Use `set X : Mx k r := ∑ a, ∑ b, Z a b • Q.unitB (Formalism.QuantumDeterminants.Hpk k r) (fun a => g *ᵥ bvec (bl k r a)) a b with hXdef`. Establish `hadj : (Formalism.QuantumDeterminants.Hpk k r)⁻¹ * Xᴴ * Formalism.QuantumDeterminants.Hpk k r = -X`. Simplify using `only [hXdef, Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, Finset.mul_sum, Finset.sum_mul, Matrix.mul_smul, Matrix.smul_mul, Formalism.FourierDecayAlt.P.QrCap.unitB_adj]`. Rewrite using `[Finset.sum_comm, ← Finset.sum_neg_distrib]`.

Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.sum_neg_distrib]`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Establish `h1` using `congrFun (congrFun hZ a) b`. Simplify using `only [Matrix.conjTranspose_apply, Matrix.neg_apply] at h1`.

Rewrite using `[h1, neg_smul]`. Establish `hX1 : Formalism.QuantumDeterminants.hpart1 (Formalism.QuantumDeterminants.Hpk k r) X = X`. Rewrite using `[Formalism.QuantumDeterminants.hpart1, hadj, sub_neg_eq_add, ← two_smul ℂ X, smul_smul]`. Evaluate the numerical expressions. Establish `hX2 : Formalism.QuantumDeterminants.hpart2 (Formalism.QuantumDeterminants.Hpk k r) X = 0`.

Rewrite using `[Formalism.QuantumDeterminants.hpart2, hadj, add_neg_cancel, smul_zero]`. Establish `hsum` using `Formalism.FourierDecayAlt.P.HermitianFormSums.ec_sum Formalism.FourierDecayAlt.P.elementary_lie_elements hR (Finset.univ : Finset (Fin k × Fin k)) (fun p => Z p.1 p.2) (fun p => Q.unitB (Formalism.QuantumDeterminants.Hpk k r) (fun a => g *ᵥ bvec (bl k r a)) p.1 p.2) (fun p => For …`. Rewrite `hsum` using `[← Finset.univ_product_univ, Finset.sum_product]`. Establish `hXlie : Formalism.FourierDecayAlt.P.QrD.InLieW k r z X`. Establish `h` using `hsum.1.1`.

Rewrite `h` using `[hX1]`. Then use the resulting hypothesis. Establish `hec : ∑ a, ∑ b, Z a b • Qr.EB π (fun a => g *ᵥ bvec (bl k r a)) a b v = Formalism.FourierDecayAlt.P.QrD.dOp π X v`. Establish `h` using `hsum.2`. Establish `h' : Formalism.FourierDecayAlt.P.QrD.ecOp π X = Formalism.FourierDecayAlt.P.QrD.dOp π X`. Rewrite using `[Formalism.FourierDecayAlt.P.QrD.ecOp, hX1, hX2, Formalism.FourierDecayAlt.P.SkewHermitianParts.dOp_zero, smul_zero, add_zero]`.

Rewrite `h` using `[h']`. Rewrite using `[h]`. Simplify using `only [Finset.sum_product, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply]`. Both sides reduce to the same expression. Establish `hexp : ∀ t : ℝ, g * blockW k r (NormedSpace.exp ((t : ℂ) • Z)) * g⁻¹ = NormedSpace.exp ((t : ℂ) • X)` using `fun t => conj_blockW_exp_eq_exp_unitB hg Z t`.

Establish `hd` using `Formalism.FourierDecayAlt.P.QrD.dOp_hasDeriv hR.1 hR.2 hXlie`. Establish `hd' : HasDerivAt (fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • X)) v) (Formalism.FourierDecayAlt.P.QrD.dOp π X v) 0`. Establish `h2` using `((ContinuousLinearMap.apply ℂ W v).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hd`. Simplify `h2` using `[Function.comp_def]`. Rewrite using `[hec]`.

Use `hd' using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `t`. Simplify using `only [hexp t]`.
-/
theorem exists_eigen {u₀ : Fin k → ℝ} (hR : Qr.IsRepW k r z π) (h₀ : IsHCTypeW k r z u₀ π) :
    ∃ B : Fin k → (Fin (2 * r + k + 1) → ℂ), Q.IsFrameOf k r [z] B ∧ ∃ v : W, v ≠ 0 ∧
      ∀ Y : ℂ, Formalism.REAL.qdet (Qr.EB π B) (Y + ((k : ℂ) - 1) / 2) v = (∏ s, (Y + (u₀ s : ℂ))) • v := by
  obtain ⟨g, hg, hU⟩ := h₀
  have hB : Q.IsFrameOf k r [z] (fun a => g *ᵥ bvec (bl k r a)) := isFrameOf hg
  refine ⟨fun a => g *ᵥ bvec (bl k r a), hB, ?_⟩
  have hgl := (Formalism.FourierDecayAlt.P.frame_general_linear W k r k z π _ hR hB).1
  refine qdet_eigen hU _ hgl ?_
  intro Z hZ v
  set X : Mx k r := ∑ a, ∑ b, Z a b • Q.unitB (Formalism.QuantumDeterminants.Hpk k r) (fun a => g *ᵥ bvec (bl k r a)) a b with hXdef
  have hadj : (Formalism.QuantumDeterminants.Hpk k r)⁻¹ * Xᴴ * Formalism.QuantumDeterminants.Hpk k r = -X := by
    simp only [hXdef, Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, Finset.mul_sum, Finset.sum_mul,
      Matrix.mul_smul, Matrix.smul_mul, Formalism.FourierDecayAlt.P.QrCap.unitB_adj]
    rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    have h1 := congrFun (congrFun hZ a) b
    simp only [Matrix.conjTranspose_apply, Matrix.neg_apply] at h1
    rw [h1, neg_smul]
  have hX1 : Formalism.QuantumDeterminants.hpart1 (Formalism.QuantumDeterminants.Hpk k r) X = X := by
    rw [Formalism.QuantumDeterminants.hpart1, hadj, sub_neg_eq_add, ← two_smul ℂ X, smul_smul]
    norm_num
  have hX2 : Formalism.QuantumDeterminants.hpart2 (Formalism.QuantumDeterminants.Hpk k r) X = 0 := by
    rw [Formalism.QuantumDeterminants.hpart2, hadj, add_neg_cancel, smul_zero]
  have hsum := Formalism.FourierDecayAlt.P.HermitianFormSums.ec_sum Formalism.FourierDecayAlt.P.elementary_lie_elements hR (Finset.univ : Finset (Fin k × Fin k))
    (fun p => Z p.1 p.2) (fun p => Q.unitB (Formalism.QuantumDeterminants.Hpk k r) (fun a => g *ᵥ bvec (bl k r a)) p.1 p.2)
    (fun p => Formalism.FourierDecayAlt.P.QrD.frame_lie hB p.1 p.2) 0 (Formalism.FourierDecayAlt.P.SkewHermitianParts.inGl_zero z)
  rw [← Finset.univ_product_univ, Finset.sum_product] at hsum
  have hXlie : Formalism.FourierDecayAlt.P.QrD.InLieW k r z X := by
    have h := hsum.1.1
    rwa [hX1] at h
  have hec : ∑ a, ∑ b, Z a b • Qr.EB π (fun a => g *ᵥ bvec (bl k r a)) a b v = Formalism.FourierDecayAlt.P.QrD.dOp π X v := by
    have h := hsum.2
    have h' : Formalism.FourierDecayAlt.P.QrD.ecOp π X = Formalism.FourierDecayAlt.P.QrD.dOp π X := by
      rw [Formalism.FourierDecayAlt.P.QrD.ecOp, hX1, hX2, Formalism.FourierDecayAlt.P.SkewHermitianParts.dOp_zero, smul_zero, add_zero]
    rw [h'] at h
    rw [h]
    simp only [Finset.sum_product, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply]
    rfl
  have hexp : ∀ t : ℝ, g * blockW k r (NormedSpace.exp ((t : ℂ) • Z)) * g⁻¹ = NormedSpace.exp ((t : ℂ) • X) :=
    fun t => conj_blockW_exp_eq_exp_unitB hg Z t
  have hd := Formalism.FourierDecayAlt.P.QrD.dOp_hasDeriv hR.1 hR.2 hXlie
  have hd' : HasDerivAt (fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • X)) v) (Formalism.FourierDecayAlt.P.QrD.dOp π X v) 0 := by
    have h2 := ((ContinuousLinearMap.apply ℂ W v).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hd
    simpa [Function.comp_def] using h2
  rw [hec]
  convert hd' using 1
  funext t
  simp only [hexp t]

/- English proof (translation)
Introduce `k r Wp _ _ _ z π u₀ hz hT h₀`. Take `⟨h1, hmul, hnorm, hcont⟩` from `Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.piW_facts hT h₀`. Establish `hR : Qr.IsRepW k r z π` using `⟨⟨h1, hmul⟩, continuousOn_clm_apply.2 hcont⟩`. Establish `⟨g, hg, hU⟩` using `h₀`. Establish `hirr : ∀ S : Submodule ℂ Wp, (∀ h ∈ Formalism.QuantumDeterminants.UWset k r z, ∀ v ∈ S, π h v ∈ S) → S = ⊥ ∨ S = ⊤`.

Introduce `S hS`. Use `hU.2.2.2.2.2.1 S le_top ?_` and prove the remaining obligations. Introduce `h hh v hv`. Establish `hh' : hᴴ * h = 1`. Use `(Matrix.mem_unitaryGroup_iff').1 hh.1` as an intermediate fact.

Rewrite `this` using `[Matrix.star_eq_conjTranspose]`. Then use the resulting hypothesis. Conclude with `hS _ (Formalism.FourierDecayAlt.P.QrCap.emb_uw hg.1 hg.2.1 _ hg.2.2 hh') v hv`. Take `⟨B, hB, v0, hv0, heig⟩` from `exists_eigen hR h₀`. Establish `hgl` using `(Formalism.FourierDecayAlt.P.frame_general_linear Wp k r k z π B hR hB).1`. Establish `key : ∀ (w : ℂ) (v : Wp), Formalism.REAL.qdet (Qr.EB π B) w v = (∏ s, (w - ((k : ℂ) - 1) / 2 + (u₀ s : ℂ))) • v`.

Introduce `w`. Use `set c : ℂ := ∏ s, (w - ((k : ℂ) - 1) / 2 + (u₀ s : ℂ)) with hc`. Use `set S : Submodule ℂ Wp := LinearMap.ker (Formalism.REAL.qdet (Qr.EB π B) w - c • (1 : Module.End ℂ Wp)) with hSdef`. Establish `hmem : ∀ v, v ∈ S ↔ Formalism.REAL.qdet (Qr.EB π B) w v = c • v` using `fun v => by`. Rewrite using `[hSdef, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero]`.

Establish `hv0S : v0 ∈ S`. Rewrite using `[hmem]`. Use `heig (w - ((k : ℂ) - 1) / 2)` as an intermediate fact. Rewrite `this` using `[sub_add_cancel]`. Then use the resulting hypothesis. Establish `hstab : Qr.Stab (Qr.EB π B) S`.

Introduce `a b v hv`. Rewrite `hv`, the goal using `[hmem]`. Establish `hcomm` using `Formalism.REAL.qDetCentral (Module.End ℂ Wp) k (Qr.EB π B) hgl w a b`. Use `congrArg (fun T : Module.End ℂ Wp => T v) hcomm` as an intermediate fact. Simplify using `only [Module.End.mul_apply] at this`.

Rewrite using `[this, hv, map_smul]`. Establish `hUW` using `Formalism.FourierDecayAlt.P.lie_stabilizer Wp k r z π B hz hT hR hB S hstab`. Break down `hirr S hUW with hbot | htop` into its components or cases. Conclude with `absurd (by rw [hbot] at hv0S; exact (Submodule.mem_bot ℂ).1 hv0S) hv0`. Introduce `v`.

Conclude with `(hmem v).1 (htop ▸ Submodule.mem_top)`. Use `⟨fun i => if h : i - 1 < k then u₀ ⟨i - 1, h⟩ else 0, hU.1, ⟨h1, hmul⟩, continuousOn_clm_apply.2 hcont, hnorm, hirr, ?_⟩` and prove the remaining obligations. Introduce `Bs hBs w v`. Rewrite using `[(Formalism.FourierDecayAlt.P.frame_general_linear Wp k r k z π Bs hR hBs).2, GlobalTheory.capelli_det_frame_indep Wp k r z π Bs B hz hT hR hBs hB, key]`. Use `congr 1`.

Use `Finset.prod_bij' (fun s _ => s.val + 1) (fun i hi => ⟨i - 1, by simp only [Finset.mem_Icc] at hi; omega⟩) ?_ ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `s _`. Simplify using `only [Finset.mem_Icc]`. Use linear arithmetic over natural numbers and integers. Introduce `i _`.

Conclude with `Finset.mem_univ _`. Introduce `s _`. Conclude with `Fin.ext (by simp)`. Introduce `i hi`. Simplify using `only [Finset.mem_Icc] at hi`.

Use `show i - 1 + 1 = i`. Use linear arithmetic over natural numbers and integers. Introduce `s _`. Simplify using `only [Nat.add_sub_cancel, s.isLt, dite_true, Fin.eta]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_isType : ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u₀ : Fin k → ℝ), Formalism.QuantumDeterminants.inWb k r z → 0 < Formalism.QuantumDeterminants.Tz k r z → PI.UpqRep.IsHCTypeW k r z u₀ π → ∃ u : ℕ → ℝ, Q.IsType k r z π u := by
  intro k r Wp _ _ _ z π u₀ hz hT h₀
  obtain ⟨h1, hmul, hnorm, hcont⟩ := Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.piW_facts hT h₀
  have hR : Qr.IsRepW k r z π := ⟨⟨h1, hmul⟩, continuousOn_clm_apply.2 hcont⟩
  have ⟨g, hg, hU⟩ := h₀
  have hirr : ∀ S : Submodule ℂ Wp, (∀ h ∈ Formalism.QuantumDeterminants.UWset k r z, ∀ v ∈ S, π h v ∈ S) → S = ⊥ ∨ S = ⊤ := by
    intro S hS
    refine hU.2.2.2.2.2.1 S le_top ?_
    intro h hh v hv
    have hh' : hᴴ * h = 1 := by
      have := (Matrix.mem_unitaryGroup_iff').1 hh.1
      rwa [Matrix.star_eq_conjTranspose] at this
    exact hS _ (Formalism.FourierDecayAlt.P.QrCap.emb_uw hg.1 hg.2.1 _ hg.2.2 hh') v hv
  obtain ⟨B, hB, v0, hv0, heig⟩ := exists_eigen hR h₀
  have hgl := (Formalism.FourierDecayAlt.P.frame_general_linear Wp k r k z π B hR hB).1
  have key : ∀ (w : ℂ) (v : Wp), Formalism.REAL.qdet (Qr.EB π B) w v =
      (∏ s, (w - ((k : ℂ) - 1) / 2 + (u₀ s : ℂ))) • v := by
    intro w
    set c : ℂ := ∏ s, (w - ((k : ℂ) - 1) / 2 + (u₀ s : ℂ)) with hc
    set S : Submodule ℂ Wp := LinearMap.ker (Formalism.REAL.qdet (Qr.EB π B) w - c • (1 : Module.End ℂ Wp)) with hSdef
    have hmem : ∀ v, v ∈ S ↔ Formalism.REAL.qdet (Qr.EB π B) w v = c • v := fun v => by
      rw [hSdef, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero]
    have hv0S : v0 ∈ S := by
      rw [hmem]
      have := heig (w - ((k : ℂ) - 1) / 2)
      rwa [sub_add_cancel] at this
    have hstab : Qr.Stab (Qr.EB π B) S := by
      intro a b v hv
      rw [hmem] at hv ⊢
      have hcomm := Formalism.REAL.qDetCentral (Module.End ℂ Wp) k (Qr.EB π B) hgl w a b
      have := congrArg (fun T : Module.End ℂ Wp => T v) hcomm
      simp only [Module.End.mul_apply] at this
      rw [this, hv, map_smul]
    have hUW := Formalism.FourierDecayAlt.P.lie_stabilizer Wp k r z π B hz hT hR hB S hstab
    rcases hirr S hUW with hbot | htop
    · exact absurd (by rw [hbot] at hv0S; exact (Submodule.mem_bot ℂ).1 hv0S) hv0
    · intro v
      exact (hmem v).1 (htop ▸ Submodule.mem_top)
  refine ⟨fun i => if h : i - 1 < k then u₀ ⟨i - 1, h⟩ else 0, hU.1, ⟨h1, hmul⟩, continuousOn_clm_apply.2 hcont,
    hnorm, hirr, ?_⟩
  intro Bs hBs w v
  rw [(Formalism.FourierDecayAlt.P.frame_general_linear Wp k r k z π Bs hR hBs).2,
    GlobalTheory.capelli_det_frame_indep Wp k r z π Bs B hz hT hR hBs hB, key]
  congr 1
  refine Finset.prod_bij' (fun s _ => s.val + 1) (fun i hi => ⟨i - 1, by simp only [Finset.mem_Icc] at hi; omega⟩)
    ?_ ?_ ?_ ?_ ?_
  · intro s _
    simp only [Finset.mem_Icc]
    omega
  · intro i _
    exact Finset.mem_univ _
  · intro s _
    exact Fin.ext (by simp)
  · intro i hi
    simp only [Finset.mem_Icc] at hi
    show i - 1 + 1 = i
    omega
  · intro s _
    simp only [Nat.add_sub_cancel, s.isLt, dite_true, Fin.eta]
    ring

end GlobalTheory.CapelliOfHC

end
