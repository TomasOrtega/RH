import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsE8WeightedBundle
import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMember
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsArBaseAway
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPolAVHypSRetract
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSharpPowOf
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmpleFormBundlePowerOfPosDef
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LineBundleIsoLinCombSymmBiadditiveSubstitution
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.BiadditiveOfTrivAxes
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Poinc.Sep.E8Fibration.AmpleBound

open Matrix

/- English proof (translation)
Simplify using `only [Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem quad_smul {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) (x : Fin n → ℝ) :
    (t • x) ⬝ᵥ M *ᵥ (t • x) = t ^ 2 * (x ⬝ᵥ M *ᵥ x) := by
  simp only [Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul]
  ring

/- English proof (translation)
Establish `hq : ∀ x : Fin n → ℝ, x ≠ 0 → 0 < x ⬝ᵥ E *ᵥ x` using `fun x hx => by`. Simplify using `using hE.dotProduct_mulVec_pos hx`. Establish `hc : ContinuousOn (fun x : Fin n → ℝ => (x ⬝ᵥ A *ᵥ x) / (x ⬝ᵥ E *ᵥ x)) (Metric.sphere 0 1)`. Use `ContinuousOn.div (by fun_prop) (by fun_prop) fun x hx => (hq x ?_).ne'` and prove the remaining obligations. Introduce and unpack `rfl`.

Simplify using `at hx`. Take `⟨C, hC⟩` from `(isCompact_sphere (0 : Fin n → ℝ) 1).exists_bound_of_continuousOn hc`. Use `⟨⌈C⌉₊ + 1, fun κ hκ => PosDef.of_dotProduct_mulVec_pos ?_ fun x hx => ?_⟩` and prove the remaining obligations. Simplify using `only [Matrix.IsHermitian, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, hE.1.eq, hA.eq, star_trivial]`. Establish `hx0 : 0 < ‖x‖` using `norm_pos_iff.2 hx`.

Establish `hy : ‖x‖⁻¹ • x ∈ Metric.sphere (0 : Fin n → ℝ) 1`. Rewrite using `[mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hx0.ne']`. Establish `hb` using `hC _ hy`. Rewrite `hb` using `[quad_smul, quad_smul, mul_div_mul_left _ _ (pow_ne_zero 2 (inv_ne_zero hx0.ne'))]`. Establish `hqx` using `hq x hx`.

Establish `h1 : (x ⬝ᵥ A *ᵥ x) / (x ⬝ᵥ E *ᵥ x) ≤ C` using `le_trans (le_abs_self _) (by rwa [Real.norm_eq_abs] at hb)`. Establish `h2 : (x ⬝ᵥ A *ᵥ x) ≤ C * (x ⬝ᵥ E *ᵥ x)` using `(div_le_iff₀ hqx).1 h1`. Establish `h3 : C < (κ : ℝ)`. Use `Nat.le_ceil C` as an intermediate fact. Establish `: ((⌈C⌉₊ + 1 : ℕ) : ℝ) ≤ κ` using `by exact_mod_cast hκ`.

Move the coercions through the operations in `at this`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h4 : C * (x ⬝ᵥ E *ᵥ x) < κ * (x ⬝ᵥ E *ᵥ x)` using `mul_lt_mul_of_pos_right h3 hqx`. Establish `h5 : x ⬝ᵥ ((κ : ℝ) • E) *ᵥ x = κ * (x ⬝ᵥ E *ᵥ x)` using `by first`. Consider the case `rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]`.

Consider the case `rw [Matrix.smul_mulVec_assoc, dotProduct_smul, smul_eq_mul]`. Consider the case `simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc, mul_left_comm]`. Simplify using `only [star_trivial, Matrix.sub_mulVec, dotProduct_sub, h5]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem exists_nat_posDef {n : ℕ} (E A : Matrix (Fin n) (Fin n) ℝ) (hE : E.PosDef) (hA : A.IsHermitian) :
    ∃ κ₀ : ℕ, ∀ κ : ℕ, κ₀ ≤ κ → ((κ : ℝ) • E - A).PosDef := by
  have hq : ∀ x : Fin n → ℝ, x ≠ 0 → 0 < x ⬝ᵥ E *ᵥ x := fun x hx => by
    simpa using hE.dotProduct_mulVec_pos hx
  have hc : ContinuousOn (fun x : Fin n → ℝ => (x ⬝ᵥ A *ᵥ x) / (x ⬝ᵥ E *ᵥ x)) (Metric.sphere 0 1) := by
    refine ContinuousOn.div (by fun_prop) (by fun_prop) fun x hx => (hq x ?_).ne'
    rintro rfl
    simp at hx
  obtain ⟨C, hC⟩ := (isCompact_sphere (0 : Fin n → ℝ) 1).exists_bound_of_continuousOn hc
  refine ⟨⌈C⌉₊ + 1, fun κ hκ => PosDef.of_dotProduct_mulVec_pos ?_ fun x hx => ?_⟩
  · simp only [Matrix.IsHermitian, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, hE.1.eq, hA.eq, star_trivial]
  · have hx0 : 0 < ‖x‖ := norm_pos_iff.2 hx
    have hy : ‖x‖⁻¹ • x ∈ Metric.sphere (0 : Fin n → ℝ) 1 := by
      rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hx0.ne']
    have hb := hC _ hy
    rw [quad_smul, quad_smul, mul_div_mul_left _ _ (pow_ne_zero 2 (inv_ne_zero hx0.ne'))] at hb
    have hqx := hq x hx
    have h1 : (x ⬝ᵥ A *ᵥ x) / (x ⬝ᵥ E *ᵥ x) ≤ C := le_trans (le_abs_self _) (by rwa [Real.norm_eq_abs] at hb)
    have h2 : (x ⬝ᵥ A *ᵥ x) ≤ C * (x ⬝ᵥ E *ᵥ x) := (div_le_iff₀ hqx).1 h1
    have h3 : C < (κ : ℝ) := by
      have := Nat.le_ceil C
      have : ((⌈C⌉₊ + 1 : ℕ) : ℝ) ≤ κ := by exact_mod_cast hκ
      push_cast at this
      linarith
    have h4 : C * (x ⬝ᵥ E *ᵥ x) < κ * (x ⬝ᵥ E *ᵥ x) := mul_lt_mul_of_pos_right h3 hqx
    have h5 : x ⬝ᵥ ((κ : ℝ) • E) *ᵥ x = κ * (x ⬝ᵥ E *ᵥ x) := by
      first
        | rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
        | rw [Matrix.smul_mulVec_assoc, dotProduct_smul, smul_eq_mul]
        | simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc, mul_left_comm]
    simp only [star_trivial, Matrix.sub_mulVec, dotProduct_sub, h5]
    linarith

/- English proof (translation)
Establish `key : ∀ m : Matrix (Fin 8) (Fin 8) ℤ, ∃ κ₀ : ℕ, ∀ κ : ℕ, κ₀ ≤ κ → ((((κ : ℤ) • W - m.transpose * W * m) + ((κ : ℤ) • W - m.transpose * W * m).transpose).map (Int.cast : ℤ → ℝ)).PosDef`. Introduce `m`. Establish `hs : (m.transpose * (W + W.transpose) * m).transpose = m.transpose * (W + W.transpose) * m`. Simplify using `only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_add, add_comm, Matrix.mul_assoc]`. Establish `hA : ((m.transpose * (W + W.transpose) * m).map (Int.cast : ℤ → ℝ)).IsHermitian`.

Use `Matrix.IsHermitian.ext fun i j => ?_` and prove the remaining obligations. Simplify using `only [Matrix.map_apply, star_trivial]`. Conclude with `congrArg (Int.cast : ℤ → ℝ) (congrFun (congrFun hs i) j)`. Take `⟨κ₀, h⟩` from `exists_nat_posDef _ _ hW.1 hA`. Use `⟨κ₀, fun κ hκ => ?_⟩` and prove the remaining obligations.

Establish `e : (((κ : ℤ) • W - m.transpose * W * m) + ((κ : ℤ) • W - m.transpose * W * m).transpose).map (Int.cast : ℤ → ℝ) = (κ : ℝ) • (W + W.transpose).map (Int.cast : ℤ → ℝ) - (m.transpose * (W + W.transpose) * m).map (Int.cast : ℤ → ℝ)`. Establish `e' : ((κ : ℤ) • W - m.transpose * W * m) + ((κ : ℤ) • W - m.transpose * W * m).transpose = (κ : ℤ) • (W + W.transpose) - m.transpose * (W + W.transpose) * m`. Simplify using `only [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_add, Matrix.add_mul, smul_add, Matrix.mul_assoc]`. Normalize the expressions using the abelian group laws. Rewrite using `[e']`.

Use extensionality with `a b`. Simplify using `only [Matrix.map_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`.

Conclude with `h κ hκ`. Take `⟨κ₀, h₀⟩` from `key (actMat W 0)`. Take `⟨κ₁, h₁⟩` from `key (actMat W 1)`. Use `⟨max κ₀ κ₁, fun i => ?_⟩` and prove the remaining obligations. Use `fin_cases i`.

Conclude with `h₀ _ (le_max_left _ _)`. Conclude with `h₁ _ (le_max_right _ _)`.
-/
theorem exists_kappa (W : Matrix (Fin 8) (Fin 8) ℤ) (hW : IsE8 W) :
    ∃ κ : ℕ, ∀ i : Fin 2,
      ((((κ : ℤ) • W - (actMat W i).transpose * W * actMat W i) +
        ((κ : ℤ) • W - (actMat W i).transpose * W * actMat W i).transpose).map (Int.cast : ℤ → ℝ)).PosDef := by
  have key : ∀ m : Matrix (Fin 8) (Fin 8) ℤ, ∃ κ₀ : ℕ, ∀ κ : ℕ, κ₀ ≤ κ →
      ((((κ : ℤ) • W - m.transpose * W * m) + ((κ : ℤ) • W - m.transpose * W * m).transpose).map
        (Int.cast : ℤ → ℝ)).PosDef := by
    intro m
    have hs : (m.transpose * (W + W.transpose) * m).transpose = m.transpose * (W + W.transpose) * m := by
      simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_add, add_comm,
        Matrix.mul_assoc]
    have hA : ((m.transpose * (W + W.transpose) * m).map (Int.cast : ℤ → ℝ)).IsHermitian := by
      refine Matrix.IsHermitian.ext fun i j => ?_
      simp only [Matrix.map_apply, star_trivial]
      exact congrArg (Int.cast : ℤ → ℝ) (congrFun (congrFun hs i) j)
    obtain ⟨κ₀, h⟩ := exists_nat_posDef _ _ hW.1 hA
    refine ⟨κ₀, fun κ hκ => ?_⟩
    have e : (((κ : ℤ) • W - m.transpose * W * m) + ((κ : ℤ) • W - m.transpose * W * m).transpose).map
        (Int.cast : ℤ → ℝ) = (κ : ℝ) • (W + W.transpose).map (Int.cast : ℤ → ℝ) -
          (m.transpose * (W + W.transpose) * m).map (Int.cast : ℤ → ℝ) := by
      have e' : ((κ : ℤ) • W - m.transpose * W * m) + ((κ : ℤ) • W - m.transpose * W * m).transpose =
          (κ : ℤ) • (W + W.transpose) - m.transpose * (W + W.transpose) * m := by
        simp only [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_mul, Matrix.transpose_transpose,
          Matrix.mul_add, Matrix.add_mul, smul_add, Matrix.mul_assoc]
        abel
      rw [e']
      ext a b
      simp only [Matrix.map_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
      push_cast
      ring
    rw [e]
    exact h κ hκ
  obtain ⟨κ₀, h₀⟩ := key (actMat W 0)
  obtain ⟨κ₁, h₁⟩ := key (actMat W 1)
  refine ⟨max κ₀ κ₁, fun i => ?_⟩
  fin_cases i
  · exact h₀ _ (le_max_left _ _)
  · exact h₁ _ (le_max_right _ _)

end GlobalTheory.Poinc.Sep.E8Fibration.AmpleBound

namespace GlobalTheory.Poinc.Sep.E8Fibration.AmpleBound

open GlobalTheory.SS GlobalTheory.CechPic

set_option maxRecDepth 20000 in

/- English proof (translation)
Introduce `W hW`. Take `⟨κ, hκ⟩` from `exists_kappa W hW`. Use `⟨κ, ?_⟩` and prove the remaining obligations. Introduce `gQ K _ _ P' B _ _ M pr hPP hpr hE act _ hact i`. Take `⟨hB, -, ⟨cub⟩, ha, -⟩` from `hPP`.

Establish `hG : Out.GlobalFnsSt` using `GlobalTheory.globalFns_holds`. Set `c` to `GlobalTheory.EighthPowerFactor.siegOne hG hB M.isLB gQ`. Establish `hdiag : Out.RelAmple c.A c.diag` using `GlobalTheory.EighthPowerFactor.relAmple_diag_lam hB M.isLB ⟨cub.t, cub.isGen⟩ ha`. Establish `hamp` using `GlobalTheory.PosDefAmple.relAmple_linComb_of_posDef hG gQ 1 8 K _ (Sp K) (𝟙 _) c P'.A pr ((κ : ℤ) • W - (actMat W i).transpose * W * actMat W i) hpr.1 hpr.2 hdiag (hκ i)`. Use `P'.isAb.proper` as an intermediate fact.

Establish `hL` using `P'.isLB`. Establish `hT` using `LB.isLB_linComb hL (K := Fin 2) ![𝟙 P'.A.left, (act i).left] ![(κ : ℤ), -1]`. Use `GlobalTheory.PosDefAmple.relAmple_of_nsmul hT (LB.isLB_linComb c.isLB _ _) (N := 1) le_rfl ?_ hamp` and prove the remaining obligations. Rewrite using `[one_smul]`. Use `set f := act i with hf`.

Use `set m := actMat W i with hm`. Establish `hflat` using `LB.isLB_linComb M.isLB (K := (Fin 8 × Fin 8) × Fin 4) (fun k => lamPts (pr k.1.1) (pr k.1.2) k.2) (fun k => -(W k.1.1 k.1.2 * negε k.2))`. Establish `hPL : cls P'.L hL = ∑ uv : Fin 8 × Fin 8, W uv.1 uv.2 • pull (lift (pr uv.1) (pr uv.2)).left (cls c.P c.isLB)`. Rewrite using `[(cls_eq_iff hL hflat).2 hE, cls_linComb M.isLB, Fintype.sum_prod_type]`. Use `Finset.sum_congr rfl fun uv _ => ?_` and prove the remaining obligations.

Establish `hlam : cls c.P c.isLB = lam (cls M.L M.isLB) (fst B B) (snd B B)` using `cls_cube_two M.isLB _ _ c.isLB`. Use `erw [hlam]`. Use `erw [pull_lam, lift_fst, lift_snd]`. Rewrite using `[Fin.sum_univ_four]`. Simplify using `only [lam, lamPts, negε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, smul_sub, smul_add, Matrix.vecHead, Matrix.vecTail, Function.comp_apply, Fin.succ_zero_eq_one, Fin.succ_one_eq_two]`.

Use `module`. Establish `hsub` using `(cls_eq_iff (LB.isLB_linComb c.isLB _ _) (LB.isLB_linComb c.isLB _ _)).2 (GlobalTheory.BilinCalc.main (Sp K) c.A c.P c.isLB (GlobalTheory.Biadditive.biadditive_of_triv_axes hG (Sp K) c.A c.diag c.ab (pull_isLB c.isLB _) hdiag c.P c.isLB c.rig₁ c.rig₂) c.symm P'.A 8 8 pr W (m.tran …`. Simplify using `only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]))`. Rewrite `hsub` using `[cls_linComb c.isLB, cls_linComb c.isLB]`. Establish `hpf : pull f.left (cls P'.L hL) = ∑ uv : Fin 8 × Fin 8, (m.transpose * W * m) uv.1 uv.2 • pull (lift (pr uv.1) (pr uv.2)).left (cls c.P c.isLB)`.

Rewrite using `[hPL, map_sum]`. Use `Eq.trans (Finset.sum_congr rfl fun uv _ => ?_) hsub.symm` and prove the remaining obligations. Rewrite using `[map_zsmul, ← pull_comp, ← Over.comp_left, comp_lift, hact i uv.1, hact i uv.2]`. Both sides reduce to the same expression. Rewrite using `[cls_linComb hL, cls_linComb c.isLB, Fin.sum_univ_two]`.

Simplify using `only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.vecHead]`. Rewrite using `[pull_id, hpf, hPL]`. Simplify using `only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, sub_smul, mul_smul, Finset.sum_sub_distrib, Finset.smul_sum]`. Rewrite using `[sub_eq_add_neg, ← Finset.sum_neg_distrib]`. Use `congr 1`.

Use `Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations. Use `first`. Consider the case `exact neg_one_smul ℤ _`. Consider the case `exact neg_one_zsmul _`. Consider the case `simp`.
-/
theorem exists_bound_relAmple : ∀ (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∃ κ : ℕ, ∀ (gQ : ℕ) (K : Type) [Field K] [IsAlgClosed K] (P' : PolAV (Sp K))
  (B : Over (Sp K)) [GrpObj B] [IsCommMonObj B] (M : RigLB B) (pr : Fin 8 → (P'.A ⟶ B)),
  E8Fibration.IsPPFib B gQ M → E8Fibration.IsProd pr → E8Fibration.IsE8WeightedBundle W pr P'.L M.L →
  ∀ act : Fin 2 → (P'.A ⟶ P'.A), (∀ i, IsMonHom (act i)) → (∀ i, E8Fibration.ActsBy pr (act i) (E8Fibration.actMat W i)) →
  ∀ i, Out.RelAmple P'.A (LB.LinComb P'.L (K := Fin 2) ![𝟙 P'.A.left, (act i).left] ![(κ : ℤ), -1]) := by
  intro W hW
  obtain ⟨κ, hκ⟩ := exists_kappa W hW
  refine ⟨κ, ?_⟩
  intro gQ K _ _ P' B _ _ M pr hPP hpr hE act _ hact i
  obtain ⟨hB, -, ⟨cub⟩, ha, -⟩ := hPP
  have hG : Out.GlobalFnsSt := GlobalTheory.globalFns_holds
  let c := GlobalTheory.EighthPowerFactor.siegOne hG hB M.isLB gQ
  have hdiag : Out.RelAmple c.A c.diag :=
    GlobalTheory.EighthPowerFactor.relAmple_diag_lam hB M.isLB ⟨cub.t, cub.isGen⟩ ha
  have hamp := GlobalTheory.PosDefAmple.relAmple_linComb_of_posDef hG gQ 1 8 K _ (Sp K) (𝟙 _) c P'.A pr
    ((κ : ℤ) • W - (actMat W i).transpose * W * actMat W i) hpr.1 hpr.2 hdiag (hκ i)
  have := P'.isAb.proper
  have hL := P'.isLB
  have hT := LB.isLB_linComb hL (K := Fin 2) ![𝟙 P'.A.left, (act i).left] ![(κ : ℤ), -1]
  refine GlobalTheory.PosDefAmple.relAmple_of_nsmul hT (LB.isLB_linComb c.isLB _ _) (N := 1) le_rfl ?_ hamp
  rw [one_smul]
  set f := act i with hf
  set m := actMat W i with hm
  have hflat := LB.isLB_linComb M.isLB (K := (Fin 8 × Fin 8) × Fin 4)
    (fun k => lamPts (pr k.1.1) (pr k.1.2) k.2) (fun k => -(W k.1.1 k.1.2 * negε k.2))
  have hPL : cls P'.L hL = ∑ uv : Fin 8 × Fin 8,
      W uv.1 uv.2 • pull (lift (pr uv.1) (pr uv.2)).left (cls c.P c.isLB) := by
    rw [(cls_eq_iff hL hflat).2 hE, cls_linComb M.isLB, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun uv _ => ?_
    have hlam : cls c.P c.isLB = lam (cls M.L M.isLB) (fst B B) (snd B B) := cls_cube_two M.isLB _ _ c.isLB
    erw [hlam]
    erw [pull_lam, lift_fst, lift_snd]
    rw [Fin.sum_univ_four]
    simp only [lam, lamPts, negε, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, smul_sub, smul_add, Matrix.vecHead, Matrix.vecTail,
      Function.comp_apply, Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
    module
  have hsub := (cls_eq_iff (LB.isLB_linComb c.isLB _ _) (LB.isLB_linComb c.isLB _ _)).2
    (GlobalTheory.BilinCalc.main (Sp K) c.A c.P c.isLB
      (GlobalTheory.Biadditive.biadditive_of_triv_axes hG (Sp K) c.A c.diag c.ab (pull_isLB c.isLB _) hdiag c.P c.isLB
        c.rig₁ c.rig₂)
      c.symm P'.A 8 8 pr W (m.transpose * W * m) m (by
        simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_add, Matrix.add_mul,
          Matrix.mul_assoc]))
  rw [cls_linComb c.isLB, cls_linComb c.isLB] at hsub
  have hpf : pull f.left (cls P'.L hL) = ∑ uv : Fin 8 × Fin 8,
      (m.transpose * W * m) uv.1 uv.2 • pull (lift (pr uv.1) (pr uv.2)).left (cls c.P c.isLB) := by
    rw [hPL, map_sum]
    refine Eq.trans (Finset.sum_congr rfl fun uv _ => ?_) hsub.symm
    rw [map_zsmul, ← pull_comp, ← Over.comp_left, comp_lift, hact i uv.1, hact i uv.2]
    rfl
  rw [cls_linComb hL, cls_linComb c.isLB, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.vecHead]
  rw [pull_id, hpf, hPL]
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, sub_smul, mul_smul, Finset.sum_sub_distrib,
    Finset.smul_sum]
  rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  first
    | exact neg_one_smul ℤ _
    | exact neg_one_zsmul _
    | simp

end GlobalTheory.Poinc.Sep.E8Fibration.AmpleBound
