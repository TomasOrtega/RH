import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsIsFundU
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralFundamentalDomainEqIteratedDecomp

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf GlobalTheory.Unf.FB

namespace GlobalTheory.Unf.FB

variable {D : D7}

/- English proof (translation)
Use function extensionality and compare the values at `j`. Simplify using `only [Matrix.vecMul, dotProduct, ell]`. Rewrite using `[Finset.sum_eq_single (Fin.last σ)]`. Simplify using the standard rewrite rules. Introduce `i _ hi`.

Rewrite using `[if_neg (fun h => hi (Fin.ext (by simp only [Fin.val_last]; omega))), zero_mul]`. Simplify using the standard rewrite rules.
-/
theorem ell_vecMul_last {σ n : ℕ} (b : Mx D (σ + 1) n) : ell D (σ + 1) ᵥ* b = b (Fin.last σ) := by
  funext j
  simp only [Matrix.vecMul, dotProduct, ell]
  rw [Finset.sum_eq_single (Fin.last σ)]
  · simp
  · intro i _ hi
    rw [if_neg (fun h => hi (Fin.ext (by simp only [Fin.val_last]; omega))), zero_mul]
  · simp

/- English proof (translation)
Rewrite using `[zEll, Matrix.vecMulVec_mul, ell_vecMul_last]`.
-/
theorem zEll_mul_eq {σ n : ℕ} (L : HSp D) (ζ : Fin L.rank → D.host.E) (b : Mx D (σ + 1) n) :
    zEll L (σ + 1) ζ ⬝ b = vecMulVec (ratV ζ) (b (Fin.last σ)) := by
  rw [zEll, Matrix.vecMulVec_mul, ell_vecMul_last]

def splitLine {σ n : ℕ} (L : HSp D) (ζ : Fin L.rank → D.host.E) (i₀ : Fin L.rank) (h1 : ∀ i : Fin L.rank, i = i₀)
    (h0 : ζ i₀ ≠ 0) : Mx D (σ + 1) n ≃+ Mx D σ n × Mx D L.rank n where
  toFun b := (Matrix.of fun i j => b (Fin.castSucc i) j, zEll L (σ + 1) ζ ⬝ b)
  invFun p := Matrix.of fun i j => Fin.lastCases (incA D (ζ i₀)⁻¹ * p.2 i₀ j) (fun i => p.1 i j) i
  left_inv b := by
    ext i j
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simp only [Matrix.of_apply, Fin.lastCases_last, zEll_mul_eq, vecMulVec_apply, ratV]
      rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ h0, map_one, one_mul]
    · simp
  right_inv p := by
    refine Prod.ext ?_ ?_
    · ext i j; simp
    · ext k j
      simp only [zEll_mul_eq, vecMulVec_apply, ratV, Matrix.of_apply, Fin.lastCases_last]
      rw [h1 k, ← mul_assoc, ← map_mul, mul_inv_cancel₀ h0, map_one, one_mul]
  map_add' b b' := Prod.ext (by ext i j; simp) (Matrix.mul_add _ _ _)

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Use `Continuous.prodMk ?_ (continuous_const.matrix_mul continuous_id)` and prove the remaining obligations. Conclude with `continuous_pi fun i => continuous_pi fun j => (continuous_apply j).comp (continuous_apply _)`. Use `continuous_pi fun i => continuous_pi fun j => ?_` and prove the remaining obligations. Use `Fin.lastCases ?_ (fun i => ?_) i` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `Continuous fun p : Mx D σ n × Mx D L.rank n => Fin.lastCases (motive := fun _ => AE D) (incA D (ζ i₀)⁻¹ * p.2 i₀ j) (fun i => p.1 i j) (Fin.last σ)`. Simplify using `only [Fin.lastCases_last]`. Use `fun_prop`. Express the relevant statement in the definitionally equal form `Continuous fun p : Mx D σ n × Mx D L.rank n => Fin.lastCases (motive := fun _ => AE D) (incA D (ζ i₀)⁻¹ * p.2 i₀ j) (fun i => p.1 i j) (Fin.castSucc i)`. Simplify using `only [Fin.lastCases_castSucc]`.

Use `fun_prop`.
-/
theorem continuous_splitLine {σ n : ℕ} (L : HSp D) (ζ : Fin L.rank → D.host.E) (i₀ : Fin L.rank)
    (h1 : ∀ i : Fin L.rank, i = i₀) (h0 : ζ i₀ ≠ 0) :
    Continuous (splitLine (σ := σ) (n := n) L ζ i₀ h1 h0) ∧ Continuous (splitLine (σ := σ) (n := n) L ζ i₀ h1 h0).symm := by
  constructor
  · refine Continuous.prodMk ?_ (continuous_const.matrix_mul continuous_id)
    exact continuous_pi fun i => continuous_pi fun j => (continuous_apply j).comp (continuous_apply _)
  · refine continuous_pi fun i => continuous_pi fun j => ?_
    refine Fin.lastCases ?_ (fun i => ?_) i
    · change Continuous fun p : Mx D σ n × Mx D L.rank n => Fin.lastCases (motive := fun _ => AE D)
        (incA D (ζ i₀)⁻¹ * p.2 i₀ j) (fun i => p.1 i j) (Fin.last σ)
      simp only [Fin.lastCases_last]
      fun_prop
    · change Continuous fun p : Mx D σ n × Mx D L.rank n => Fin.lastCases (motive := fun _ => AE D)
        (incA D (ζ i₀)⁻¹ * p.2 i₀ j) (fun i => p.1 i j) (Fin.castSucc i)
      simp only [Fin.lastCases_castSucc]
      fun_prop

/- English proof (translation)
Rewrite using `[HypDec.incX_apply, HypDec.wittDecomp_inclAnisotropicHom_apply, OrthDec.resT_symm_apply, Matrix.mul_zero, zero_add, zl, zEll_mul_eq, Matrix.mul_vecMulVec, Matrix.mul_vecMulVec, OrthDec.jB, ← ratV_mulVec]`. Use extensionality with `k j`. Simplify using `[Matrix.mul_apply, Fin.sum_univ_castSucc, x0, xLast, vecMulVec_apply, vecB]`.
-/
theorem fourierBesselBasePoint_mul_eq {σ : ℕ} (B : BesLev D σ) (S : HSp D) (b : Mx D (σ + 1) S.rank) :
    x0 B ⬝ b = B.d.incX S (Matrix.of fun i j => b (Fin.castSucc i) j) +
      B.d.inc0 S ((B.o.resT S).symm (0, zl B ⬝ b)) := by
  rw [HypDec.incX_apply, HypDec.wittDecomp_inclAnisotropicHom_apply, OrthDec.resT_symm_apply, Matrix.mul_zero, zero_add, zl, zEll_mul_eq,
    Matrix.mul_vecMulVec, Matrix.mul_vecMulVec, OrthDec.jB, ← ratV_mulVec]
  ext k j
  simp [Matrix.mul_apply, Fin.sum_univ_castSucc, x0, xLast, vecMulVec_apply, vecB]

/- English proof (translation)
Rewrite using `[fourierBesselBasePoint_mul_eq, fourierBesselBasePoint_mul_eq]`. Simplify using `only [GlobalTheory.OrientedHeis.symplOH_add_left, GlobalTheory.OrientedHeis.symplOH_add_right, HypDec.symplOH_incX_incX, HypDec.wittDecomp_sympl_inclIsotropic_inclAnisotropic, HypDec.wittDecomp_sympl_inclAnisotropic_inclAnisotropic, zero_add]`. Rewrite using `[symplOH_skew S B.V (B.d.incX S _) (B.d.inc0 S _), HypDec.wittDecomp_sympl_inclIsotropic_inclAnisotropic, neg_zero, zero_add, OrthDec.symplOH_resT, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, symplOH_zero_left, zero_add]`.
-/
theorem heisSymplecticHalf_fourierBesselBasePoint_mul {σ : ℕ} (B : BesLev D σ) (S : HSp D) (b b' : Mx D (σ + 1) S.rank) :
    symplOH S B.V (x0 B ⬝ b) (x0 B ⬝ b') = symplOH S B.L (zl B ⬝ b) (zl B ⬝ b') := by
  rw [fourierBesselBasePoint_mul_eq, fourierBesselBasePoint_mul_eq]
  simp only [GlobalTheory.OrientedHeis.symplOH_add_left, GlobalTheory.OrientedHeis.symplOH_add_right, HypDec.symplOH_incX_incX,
    HypDec.wittDecomp_sympl_inclIsotropic_inclAnisotropic, HypDec.wittDecomp_sympl_inclAnisotropic_inclAnisotropic, zero_add]
  rw [symplOH_skew S B.V (B.d.incX S _) (B.d.inc0 S _), HypDec.wittDecomp_sympl_inclIsotropic_inclAnisotropic, neg_zero, zero_add,
    OrthDec.symplOH_resT, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, symplOH_zero_left, zero_add]

/- English proof (translation)
Use `⟨vecMulVec B.ζ (fun i : Fin (σ + 1) => if i.1 + 1 = σ + 1 then (1 : D.host.E) else 0), ?_⟩` and prove the remaining obligations. Use `Matrix.ext fun k i => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `incA D (B.ζ k * (if i.1 + 1 = σ + 1 then (1 : D.host.E) else 0)) = incA D (B.ζ k) * (if i.1 + 1 = σ + 1 then (1 : AE D) else 0)`. Use `split_ifs`. Rewrite using `[mul_one, mul_one]`.

Rewrite using `[mul_zero, mul_zero, map_zero]`.
-/
theorem zl_mem_ratMx {σ : ℕ} (B : BesLev D σ) : zl B ∈ ratMx D B.L.rank (σ + 1) := by
  refine ⟨vecMulVec B.ζ (fun i : Fin (σ + 1) => if i.1 + 1 = σ + 1 then (1 : D.host.E) else 0), ?_⟩
  refine Matrix.ext fun k i => ?_
  change incA D (B.ζ k * (if i.1 + 1 = σ + 1 then (1 : D.host.E) else 0)) =
    incA D (B.ζ k) * (if i.1 + 1 = σ + 1 then (1 : AE D) else 0)
  split_ifs
  · rw [mul_one, mul_one]
  · rw [mul_zero, mul_zero, map_zero]

/- English proof (translation)
Rewrite using `[fourierBesselBasePoint_mul_eq]`. Take `⟨g, rfl⟩` from `hγ`. Use `add_mem (ratMx_mul (rat_mem _) ⟨Matrix.of fun i j => g (Fin.castSucc i) j, rfl⟩) (ratMx_mul (rat_mem _) ?_)` and prove the remaining obligations. Rewrite using `[OrthDec.resT_symm_apply, Matrix.mul_zero, zero_add]`. Conclude with `ratMx_mul (rat_mem _) (ratMx_mul (zl_mem_ratMx B) (rat_mem _))`.
-/
theorem fourierBesselBasePoint_mul_mem_rationalAdelicMatrix {σ : ℕ} (B : BesLev D σ) (S : HSp D) {γ : Mx D (σ + 1) S.rank} (hγ : γ ∈ ratMx D (σ + 1) S.rank) :
    x0 B ⬝ γ ∈ ratMx D B.V.rank S.rank := by
  rw [fourierBesselBasePoint_mul_eq]
  obtain ⟨g, rfl⟩ := hγ
  refine add_mem (ratMx_mul (rat_mem _) ⟨Matrix.of fun i j => g (Fin.castSucc i) j, rfl⟩)
    (ratMx_mul (rat_mem _) ?_)
  rw [OrthDec.resT_symm_apply, Matrix.mul_zero, zero_add]
  exact ratMx_mul (rat_mem _) (ratMx_mul (zl_mem_ratMx B) (rat_mem _))

/- English proof (translation)
Take `⟨⟨g₁, hg₁⟩, ⟨g₂, hg₂⟩⟩` from `hp`. Use `⟨Matrix.of fun i j => Fin.lastCases ((ζ i₀)⁻¹ * g₂ i₀ j) (fun i => g₁ i j) i, ?_⟩` and prove the remaining obligations. Use `Matrix.ext fun i j => ?_` and prove the remaining obligations. Use `Fin.lastCases ?_ (fun i => ?_) i` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `incA D (Fin.lastCases (motive := fun _ => D.host.E) ((ζ i₀)⁻¹ * g₂ i₀ j) (fun i => g₁ i j) (Fin.last σ)) = Fin.lastCases (motive := fun _ => AE D) (incA D (ζ i₀)⁻¹ * p.2 i₀ j) (fun i => p.1 i j) (Fin.last σ)`.

Rewrite using `[Fin.lastCases_last, Fin.lastCases_last, map_mul, ← hg₂]`. Both sides reduce to the same expression. Express the relevant statement in the definitionally equal form `incA D (Fin.lastCases (motive := fun _ => D.host.E) ((ζ i₀)⁻¹ * g₂ i₀ j) (fun i => g₁ i j) (Fin.castSucc i)) = Fin.lastCases (motive := fun _ => AE D) (incA D (ζ i₀)⁻¹ * p.2 i₀ j) (fun i => p.1 i j) (Fin.castSucc i)`. Rewrite using `[Fin.lastCases_castSucc, Fin.lastCases_castSucc, ← hg₁]`. Both sides reduce to the same expression.
-/
theorem splitLine_symm_mem {σ n : ℕ} (L : HSp D) (ζ : Fin L.rank → D.host.E) (i₀ : Fin L.rank)
    (h1 : ∀ i : Fin L.rank, i = i₀) (h0 : ζ i₀ ≠ 0) {p : Mx D σ n × Mx D L.rank n}
    (hp : p ∈ (ratMx D σ n).prod (ratMx D L.rank n)) :
    (splitLine L ζ i₀ h1 h0).symm p ∈ ratMx D (σ + 1) n := by
  obtain ⟨⟨g₁, hg₁⟩, ⟨g₂, hg₂⟩⟩ := hp
  refine ⟨Matrix.of fun i j => Fin.lastCases ((ζ i₀)⁻¹ * g₂ i₀ j) (fun i => g₁ i j) i, ?_⟩
  refine Matrix.ext fun i j => ?_
  refine Fin.lastCases ?_ (fun i => ?_) i
  · change incA D (Fin.lastCases (motive := fun _ => D.host.E) ((ζ i₀)⁻¹ * g₂ i₀ j) (fun i => g₁ i j) (Fin.last σ)) =
      Fin.lastCases (motive := fun _ => AE D) (incA D (ζ i₀)⁻¹ * p.2 i₀ j) (fun i => p.1 i j) (Fin.last σ)
    rw [Fin.lastCases_last, Fin.lastCases_last, map_mul, ← hg₂]; rfl
  · change incA D (Fin.lastCases (motive := fun _ => D.host.E) ((ζ i₀)⁻¹ * g₂ i₀ j) (fun i => g₁ i j) (Fin.castSucc i)) =
      Fin.lastCases (motive := fun _ => AE D) (incA D (ζ i₀)⁻¹ * p.2 i₀ j) (fun i => p.1 i j) (Fin.castSucc i)
    rw [Fin.lastCases_castSucc, Fin.lastCases_castSucc, ← hg₁]; rfl

/- English proof (translation)
Take `⟨g, rfl⟩` from `hb`. Use `⟨⟨Matrix.of fun i j => g (Fin.castSucc i) j, rfl⟩, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `zEll L (σ + 1) ζ ⬝ rat g ∈ ratMx D L.rank n`. Use `ratMx_mul ⟨vecMulVec ζ (fun i : Fin (σ + 1) => if i.1 + 1 = σ + 1 then (1 : D.host.E) else 0), ?_⟩ (rat_mem _)` and prove the remaining obligations. Use `Matrix.ext fun k i => ?_` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `incA D (ζ k * (if i.1 + 1 = σ + 1 then (1 : D.host.E) else 0)) = incA D (ζ k) * (if i.1 + 1 = σ + 1 then (1 : AE D) else 0)`. Use `split_ifs`. Rewrite using `[mul_one, mul_one]`. Rewrite using `[mul_zero, mul_zero, map_zero]`.
-/
theorem splitLine_mem {σ n : ℕ} (L : HSp D) (ζ : Fin L.rank → D.host.E) (i₀ : Fin L.rank)
    (h1 : ∀ i : Fin L.rank, i = i₀) (h0 : ζ i₀ ≠ 0) {b : Mx D (σ + 1) n} (hb : b ∈ ratMx D (σ + 1) n) :
    splitLine L ζ i₀ h1 h0 b ∈ (ratMx D σ n).prod (ratMx D L.rank n) := by
  obtain ⟨g, rfl⟩ := hb
  refine ⟨⟨Matrix.of fun i j => g (Fin.castSucc i) j, rfl⟩, ?_⟩
  change zEll L (σ + 1) ζ ⬝ rat g ∈ ratMx D L.rank n
  refine ratMx_mul ⟨vecMulVec ζ (fun i : Fin (σ + 1) => if i.1 + 1 = σ + 1 then (1 : D.host.E) else 0), ?_⟩ (rat_mem _)
  refine Matrix.ext fun k i => ?_
  change incA D (ζ k * (if i.1 + 1 = σ + 1 then (1 : D.host.E) else 0)) =
    incA D (ζ k) * (if i.1 + 1 = σ + 1 then (1 : AE D) else 0)
  split_ifs
  · rw [mul_one, mul_one]
  · rw [mul_zero, mul_zero, map_zero]

set_option maxHeartbeats 2000000 in

/- English proof (translation)
Introduce `D ψ hψ σ S B vB vT vL f y hf hy`. Establish `hψn : ∀ a, ‖ψ a‖ = 1` using `hψ.1.2.1`. Establish `hL1 : B.L.rank = 1` using `B.line.1`. Set `i₀ : Fin B.L.rank` to `⟨0, by omega⟩`. Establish `h1 : ∀ i : Fin B.L.rank, i = i₀` using `fun i => Fin.ext (by have := i.2; simp only [i₀]; omega)`.

Establish `h0 : B.ζ i₀ ≠ 0`. Introduce `h`. Apply `B.line.2` to reduce the goal to its premises. Establish `: B.ζ = 0` using `funext fun i => by rw [h1 i, h]; rfl`. Rewrite using `[this]`.

Simplify using the standard rewrite rules. Use `set e := splitLine (σ := σ) (n := S.rank) B.L B.ζ i₀ h1 h0 with he_def`. Take `⟨he, hes⟩` from `continuous_splitLine (σ := σ) (n := S.rank) B.L B.ζ i₀ h1 h0`. Take `⟨i1, i2, i3, i4, i5, -⟩` from `lattice_Mx D (σ + 1) S.rank`. Take `⟨j1, j2, j3, j4, j5, -⟩` from `lattice_Mx D σ S.rank`.

Take `⟨k1, k2, k3, k4, k5, -⟩` from `lattice_Mx D B.L.rank S.rank`. Use `haveI : BorelSpace (Mx D (σ + 1) S.rank) := ⟨rfl⟩`. Use `haveI : BorelSpace (Mx D σ S.rank) := ⟨rfl⟩`. Use `haveI : BorelSpace (Mx D B.L.rank S.rank) := ⟨rfl⟩`. Use `haveI : Countable (ratMx D (σ + 1) S.rank) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance`.

Use `haveI := vT.covol.1`. Use `haveI := vL.covol.1`. Use `haveI := vB.covol.1`. Establish `hx : ∀ b : Mx D (σ + 1) S.rank, x0 B ⬝ b = B.d.incX S (e b).1 + B.d.inc0 S ((B.o.resT S).symm (0, (e b).2))` using `fun b => fourierBesselBasePoint_mul_eq B S b`. Use `set P := vT.μ.prod vL.μ with hP`.

Set `me : Mx D (σ + 1) S.rank ≃ᵐ Mx D σ S.rank × Mx D B.L.rank S.rank` to `{ toEquiv := e.toEquiv measurable_toFun := he.measurable measurable_invFun := hes.measurable }`. Establish `hmp : MeasurePreserving me (P.map e.symm) P` using `MeasurePreserving.symm me.symm ⟨me.symm.measurable, rfl⟩`. Establish `hmp' : MeasurePreserving e (P.map e.symm) P` using `hmp`. Establish `hν : (P.map e.symm).IsAddHaarMeasure` using `AddEquiv.isAddHaarMeasure_map P e.symm hes (by simpa using he)`. Establish `hPF : IsAddFundamentalDomain ((ratMx D σ S.rank).prod (ratMx D B.L.rank S.rank)) (vT.𝓕 ×ˢ vL.𝓕) P` using `GlobalTheory.CoordUnfold.isAddFundamentalDomain_prod vT.covol.2.1 vL.covol.2.1`.

Establish `hF' : IsAddFundamentalDomain (ratMx D (σ + 1) S.rank) (e ⁻¹' (vT.𝓕 ×ˢ vL.𝓕)) (P.map e.symm)`. Set `g : (ratMx D σ S.rank).prod (ratMx D B.L.rank S.rank) → ratMx D (σ + 1) S.rank` to `fun p => ⟨e.symm p, splitLine_symm_mem B.L B.ζ i₀ h1 h0 p.2⟩`. Establish `hg : Function.Bijective g`. Prove the components needed by the constructor for the conclusion. Introduce `a b hab`.

Conclude with `Subtype.ext (e.symm.injective (congrArg Subtype.val hab))`. Introduce `x`. Conclude with `⟨⟨e x, splitLine_mem B.L B.ζ i₀ h1 h0 x.2⟩, Subtype.ext (by simp [g])⟩`. Use `hPF.preimage_of_equiv hmp'.quasiMeasurePreserving hg ?_` and prove the remaining obligations. Introduce `p x`.

Simplify using `[g, AddSubgroup.vadd_def]`. Establish `hv : (P.map e.symm) (e ⁻¹' (vT.𝓕 ×ˢ vL.𝓕)) = 1`. Use `(hmp.measure_preimage_equiv _).trans ?_` and prove the remaining obligations. Rewrite using `[Measure.prod_prod, vT.covol.2.2, vL.covol.2.2, one_mul]`. Establish `hcov : IsCovolOne (ratMx D (σ + 1) S.rank) (P.map e.symm) (e ⁻¹' (vT.𝓕 ×ˢ vL.𝓕))` using `⟨hν, hF', hv⟩`.

Establish `hμeq : P.map e.symm = vB.μ` using `covolOne_measure_eq vB.covol hcov`. Establish `hfx : ∀ γ ∈ ratMx D (σ + 1) S.rank, ∀ b, f (x0 B ⬝ (γ + b)) = ψ (-(symplOH S B.V (x0 B ⬝ γ) (x0 B ⬝ b))) * f (x0 B ⬝ b)`. Introduce `γ hγ b`. Take `⟨δ, hδ⟩` from `fourierBesselBasePoint_mul_mem_rationalAdelicMatrix B S hγ`. Establish `e1` using `hf.1 δ (x0 B ⬝ b)`.

Rewrite `e1` using `[show ratW B.V S δ = x0 B ⬝ γ from hδ]`. Rewrite using `[Matrix.mul_add, e1]`. Establish `hyz : ∀ γ ∈ ratMx D (σ + 1) S.rank, ∀ b, y (zl B ⬝ (γ + b)) = ψ (-(symplOH S B.L (zl B ⬝ γ) (zl B ⬝ b))) * y (zl B ⬝ b)`. Introduce `γ hγ b`. Take `⟨δ, hδ⟩` from `ratMx_mul (zl_mem_ratMx B) hγ`.

Establish `e1` using `hy.1 δ (zl B ⬝ b)`. Rewrite `e1` using `[show ratW B.L S δ = zl B ⬝ γ from hδ]`. Rewrite using `[Matrix.mul_add, e1]`. Establish `hunit : ∀ a, ψ a * star (ψ a) = 1` using `fun a => by`. Rewrite using `[← starRingEnd_apply, RCLike.mul_conj, hψn]`.

Simplify using the standard rewrite rules. Use `set s := vT.𝓕 ×ˢ vL.𝓕 with hs`. Use `set G : Mx D (σ + 1) S.rank → ℂ := fun b => f (x0 B ⬝ b) * star (y (zl B ⬝ b)) with hG`. Establish `hGper : ∀ γ ∈ ratMx D (σ + 1) S.rank, ∀ b, G (γ + b) = G b`. Introduce `γ hγ b`.

Simplify using `only [hG]`. Rewrite using `[hfx γ hγ b, hyz γ hγ b, heisSymplecticHalf_fourierBesselBasePoint_mul, star_mul]`. Combine the equalities or inequalities in the displayed calculation. Establish `hx0c : Continuous fun b : Mx D (σ + 1) S.rank => x0 B ⬝ b` using `continuous_const.matrix_mul continuous_id`. Establish `hzlc : Continuous fun b : Mx D (σ + 1) S.rank => zl B ⬝ b` using `continuous_const.matrix_mul continuous_id`.

Establish `hGc : Continuous G` using `(hf.2.comp hx0c).mul (continuous_star.comp (hy.2.comp hzlc))`. Use `set H : Mx D σ S.rank × Mx D B.L.rank S.rank → ℂ := fun p => f (B.d.incX S p.1 + B.d.inc0 S ((B.o.resT S).symm (0, p.2))) * star (y p.2) with hH`. Establish `hGH : ∀ p, G (e.symm p) = H p`. Introduce `p`. Simplify using `only [hG, hH]`.

Rewrite using `[hx (e.symm p), AddEquiv.apply_symm_apply]`. Use `congr 3`. Conclude with `congrArg Prod.snd (e.apply_symm_apply p)`. Establish `hmix : ∀ w₀, B.d.mixT S ψ vT.μ vT.𝓕 f 0 w₀ = ∫ ξ in vT.𝓕, f (B.d.incX S ξ + B.d.inc0 S w₀) ∂vT.μ`. Introduce `w₀`.

Express the relevant statement in the definitionally equal form `∫ ξ in vT.𝓕, heisO ψ S B.V (B.d.incX S ξ) (heisO ψ S B.V (B.d.incAdj S 0) (heisO ψ S B.V (B.d.inc0 S w₀) f)) 0 ∂vT.μ = _`. Use `congr 1`. Use function extensionality and compare the values at `ξ`. Rewrite using `[HypDec.integrandT_eq, map_zero, symplOH_zero_right, AddChar.map_zero_eq_one, one_mul, add_zero]`. Establish `hGi : IntegrableOn G (e ⁻¹' s) (P.map e.symm)` using `covolOne_integrableOn hcov G hGc hGper`.

Establish `hHi : Integrable H ((vT.μ.restrict vT.𝓕).prod (vL.μ.restrict vL.𝓕))`. Rewrite using `[Measure.prod_restrict]`. Establish `h2` using `(hmp.integrableOn_comp_preimage me.measurableEmbedding (f := H) (s := s)).1 (by`. Establish `: H ∘ me = G` using `funext fun b => by`. Rewrite using `[Function.comp_apply, ← hGH]`.

Conclude with `congrArg G (e.symm_apply_apply b)`. Rewrite using `[this]`. Conclude with `hGi)`. Conclude with `h2`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Combine the equalities or inequalities in the displayed calculation. Establish `h3` using `hmp.setIntegral_preimage_emb me.measurableEmbedding H s`. Rewrite using `[← h3]`. Use `congrArg (fun F : Mx D (σ + 1) S.rank → ℂ => ∫ b in e ⁻¹' s, F b ∂(P.map e.symm)) (funext fun b => ?_)` and prove the remaining obligations. Rewrite using `[← hGH]`.

Conclude with `(congrArg G (e.symm_apply_apply b)).symm`. Use `_ = ∫ v in vL.𝓕, ∫ ξ in vT.𝓕, H (ξ, v) ∂vT.μ ∂vL.μ := by`. Rewrite using `[hP, ← Measure.prod_restrict]`. Conclude with `integral_prod_symm H hHi`. Use `_ = _ := by`.

Express the relevant statement in the definitionally equal form `_ = ∫ v in vL.𝓕, B.d.mixT S ψ vT.μ vT.𝓕 f 0 ((B.o.resT S).symm (0, v)) * star (y v) ∂vL.μ`. Use `congr 1`. Use function extensionality and compare the values at `v`. Rewrite using `[hmix, ← integral_mul_const]`. Establish `hψe : ∀ a, ‖ψ a‖ₑ = 1` using `fun a => by rw [← ofReal_norm_eq_enorm, hψn, ENNReal.ofReal_one] set K : Mx D σ S.rank × Mx D B.L.rank S.rank → ENNReal := fun p => ‖f (B.d.incX S p.1 + B.d.inc0 S ((B.o.resT S).symm (0, p.2)))‖ₑ with hK`.

Establish `hKc : Continuous K`. Use `(hf.2.comp ?_).enorm` and prove the remaining obligations. Simplify using `only [HypDec.incX_apply, HypDec.wittDecomp_inclAnisotropicHom_apply, OrthDec.resT_symm_apply]`. Conclude with `(continuous_const.matrix_mul continuous_fst).add (continuous_const.matrix_mul (continuous_const.add (continuous_const.matrix_mul continuous_snd)))`. Establish `hKe : ∀ b, K (e b) = ‖f (x0 B ⬝ b)‖ₑ` using `fun b => by rw [hK, hx b]`.

Establish `hper' : ∀ (γ : ratMx D (σ + 1) S.rank) (b : Mx D (σ + 1) S.rank), ‖f (x0 B ⬝ (γ +ᵥ b))‖ₑ = ‖f (x0 B ⬝ b)‖ₑ`. Introduce `γ b`. Rewrite using `[AddSubgroup.vadd_def, vadd_eq_add, hfx γ γ.2 b, enorm_mul, hψe, one_mul]`. Establish `hF'' : IsAddFundamentalDomain (ratMx D (σ + 1) S.rank) (e ⁻¹' s) vB.μ` using `hμeq ▸ hF'`. Combine the equalities or inequalities in the displayed calculation.

Use `lintegral_mono fun v => ?_` and prove the remaining obligations. Rewrite using `[hmix]`. Conclude with `enorm_integral_le_lintegral_enorm _`. Use `_ = ∫⁻ p in s, K p ∂P := by`. Rewrite using `[hP, ← Measure.prod_restrict, lintegral_prod_symm _ hKc.measurable.aemeasurable]`.

Use `_ = ∫⁻ b in e ⁻¹' s, K (e b) ∂(P.map e.symm) := (hmp'.setLIntegral_comp_preimage_emb me.measurableEmbedding K s).symm`. Use `_ = ∫⁻ b in e ⁻¹' s, ‖f (x0 B ⬝ b)‖ₑ ∂vB.μ := by`. Rewrite using `[hμeq]`. Use `congr 1`. Use function extensionality and compare the values at `b`.

Conclude with `hKe b`. Use `_ = ∫⁻ b in vB.𝓕, ‖f (x0 B ⬝ b)‖ₑ ∂vB.μ := hF''.setLIntegral_eq vB.covol.2.1 _ hper'`.
-/
theorem heis_base : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (σ : ℕ) (S : HSp D) (B : BesLev D σ) (vB : VolM D (σ + 1) S.rank) (vT : VolM D σ S.rank) (vL : VolM D B.L.rank S.rank) (f : WO S B.V → ℂ) (y : WO S B.L → ℂ), Quasi ψ S B.V f → Quasi ψ S B.L y → (∫ b in vB.𝓕, f (x0 B ⬝ b) * star (y (zl B ⬝ b)) ∂vB.μ = contractT B.o S vL.μ vL.𝓕 (B.d.mixT S ψ vT.μ vT.𝓕 f 0) y 0) ∧ ∫⁻ v in vL.𝓕, ‖B.d.mixT S ψ vT.μ vT.𝓕 f 0 ((B.o.resT S).symm (0, v))‖ₑ ∂vL.μ ≤ ∫⁻ b in vB.𝓕, ‖f (x0 B ⬝ b)‖ₑ ∂vB.μ := by
  intro D ψ hψ σ S B vB vT vL f y hf hy
  have hψn : ∀ a, ‖ψ a‖ = 1 := hψ.1.2.1
  have hL1 : B.L.rank = 1 := B.line.1
  let i₀ : Fin B.L.rank := ⟨0, by omega⟩
  have h1 : ∀ i : Fin B.L.rank, i = i₀ := fun i => Fin.ext (by have := i.2; simp only [i₀]; omega)
  have h0 : B.ζ i₀ ≠ 0 := by
    intro h
    apply B.line.2
    have : B.ζ = 0 := funext fun i => by rw [h1 i, h]; rfl
    rw [this]; simp
  set e := splitLine (σ := σ) (n := S.rank) B.L B.ζ i₀ h1 h0 with he_def
  obtain ⟨he, hes⟩ := continuous_splitLine (σ := σ) (n := S.rank) B.L B.ζ i₀ h1 h0
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := lattice_Mx D (σ + 1) S.rank
  obtain ⟨j1, j2, j3, j4, j5, -⟩ := lattice_Mx D σ S.rank
  obtain ⟨k1, k2, k3, k4, k5, -⟩ := lattice_Mx D B.L.rank S.rank
  haveI : BorelSpace (Mx D (σ + 1) S.rank) := ⟨rfl⟩
  haveI : BorelSpace (Mx D σ S.rank) := ⟨rfl⟩
  haveI : BorelSpace (Mx D B.L.rank S.rank) := ⟨rfl⟩
  haveI : Countable (ratMx D (σ + 1) S.rank) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  haveI := vT.covol.1
  haveI := vL.covol.1
  haveI := vB.covol.1

  have hx : ∀ b : Mx D (σ + 1) S.rank, x0 B ⬝ b = B.d.incX S (e b).1 + B.d.inc0 S ((B.o.resT S).symm (0, (e b).2)) := fun b => fourierBesselBasePoint_mul_eq B S b

  set P := vT.μ.prod vL.μ with hP
  let me : Mx D (σ + 1) S.rank ≃ᵐ Mx D σ S.rank × Mx D B.L.rank S.rank :=
    { toEquiv := e.toEquiv
      measurable_toFun := he.measurable
      measurable_invFun := hes.measurable }
  have hmp : MeasurePreserving me (P.map e.symm) P := MeasurePreserving.symm me.symm ⟨me.symm.measurable, rfl⟩
  have hmp' : MeasurePreserving e (P.map e.symm) P := hmp
  have hν : (P.map e.symm).IsAddHaarMeasure := AddEquiv.isAddHaarMeasure_map P e.symm hes (by simpa using he)
  have hPF : IsAddFundamentalDomain ((ratMx D σ S.rank).prod (ratMx D B.L.rank S.rank)) (vT.𝓕 ×ˢ vL.𝓕) P :=
    GlobalTheory.CoordUnfold.isAddFundamentalDomain_prod vT.covol.2.1 vL.covol.2.1
  have hF' : IsAddFundamentalDomain (ratMx D (σ + 1) S.rank) (e ⁻¹' (vT.𝓕 ×ˢ vL.𝓕)) (P.map e.symm) := by
    let g : (ratMx D σ S.rank).prod (ratMx D B.L.rank S.rank) → ratMx D (σ + 1) S.rank :=
      fun p => ⟨e.symm p, splitLine_symm_mem B.L B.ζ i₀ h1 h0 p.2⟩
    have hg : Function.Bijective g := by
      constructor
      · intro a b hab
        exact Subtype.ext (e.symm.injective (congrArg Subtype.val hab))
      · intro x
        exact ⟨⟨e x, splitLine_mem B.L B.ζ i₀ h1 h0 x.2⟩, Subtype.ext (by simp [g])⟩
    refine hPF.preimage_of_equiv hmp'.quasiMeasurePreserving hg ?_
    intro p x
    simp [g, AddSubgroup.vadd_def]
  have hv : (P.map e.symm) (e ⁻¹' (vT.𝓕 ×ˢ vL.𝓕)) = 1 := by
    refine (hmp.measure_preimage_equiv _).trans ?_
    rw [Measure.prod_prod, vT.covol.2.2, vL.covol.2.2, one_mul]
  have hcov : IsCovolOne (ratMx D (σ + 1) S.rank) (P.map e.symm) (e ⁻¹' (vT.𝓕 ×ˢ vL.𝓕)) := ⟨hν, hF', hv⟩
  have hμeq : P.map e.symm = vB.μ := covolOne_measure_eq vB.covol hcov

  have hfx : ∀ γ ∈ ratMx D (σ + 1) S.rank, ∀ b,
      f (x0 B ⬝ (γ + b)) = ψ (-(symplOH S B.V (x0 B ⬝ γ) (x0 B ⬝ b))) * f (x0 B ⬝ b) := by
    intro γ hγ b
    obtain ⟨δ, hδ⟩ := fourierBesselBasePoint_mul_mem_rationalAdelicMatrix B S hγ
    have e1 := hf.1 δ (x0 B ⬝ b)
    rw [show ratW B.V S δ = x0 B ⬝ γ from hδ] at e1
    rw [Matrix.mul_add, e1]
  have hyz : ∀ γ ∈ ratMx D (σ + 1) S.rank, ∀ b,
      y (zl B ⬝ (γ + b)) = ψ (-(symplOH S B.L (zl B ⬝ γ) (zl B ⬝ b))) * y (zl B ⬝ b) := by
    intro γ hγ b
    obtain ⟨δ, hδ⟩ := ratMx_mul (zl_mem_ratMx B) hγ
    have e1 := hy.1 δ (zl B ⬝ b)
    rw [show ratW B.L S δ = zl B ⬝ γ from hδ] at e1
    rw [Matrix.mul_add, e1]
  have hunit : ∀ a, ψ a * star (ψ a) = 1 := fun a => by
    rw [← starRingEnd_apply, RCLike.mul_conj, hψn]; simp
  set s := vT.𝓕 ×ˢ vL.𝓕 with hs
  set G : Mx D (σ + 1) S.rank → ℂ := fun b => f (x0 B ⬝ b) * star (y (zl B ⬝ b)) with hG
  have hGper : ∀ γ ∈ ratMx D (σ + 1) S.rank, ∀ b, G (γ + b) = G b := by
    intro γ hγ b
    simp only [hG]
    rw [hfx γ hγ b, hyz γ hγ b, heisSymplecticHalf_fourierBesselBasePoint_mul, star_mul]
    calc ψ (-symplOH S B.L (zl B ⬝ γ) (zl B ⬝ b)) * f (x0 B ⬝ b) *
          (star (y (zl B ⬝ b)) * star (ψ (-symplOH S B.L (zl B ⬝ γ) (zl B ⬝ b))))
        = (ψ (-symplOH S B.L (zl B ⬝ γ) (zl B ⬝ b)) * star (ψ (-symplOH S B.L (zl B ⬝ γ) (zl B ⬝ b)))) *
          (f (x0 B ⬝ b) * star (y (zl B ⬝ b))) := by ring
      _ = _ := by rw [hunit, one_mul]
  have hx0c : Continuous fun b : Mx D (σ + 1) S.rank => x0 B ⬝ b := continuous_const.matrix_mul continuous_id
  have hzlc : Continuous fun b : Mx D (σ + 1) S.rank => zl B ⬝ b := continuous_const.matrix_mul continuous_id
  have hGc : Continuous G := (hf.2.comp hx0c).mul (continuous_star.comp (hy.2.comp hzlc))
  set H : Mx D σ S.rank × Mx D B.L.rank S.rank → ℂ :=
    fun p => f (B.d.incX S p.1 + B.d.inc0 S ((B.o.resT S).symm (0, p.2))) * star (y p.2) with hH
  have hGH : ∀ p, G (e.symm p) = H p := by
    intro p
    simp only [hG, hH]
    rw [hx (e.symm p), AddEquiv.apply_symm_apply]
    congr 3
    exact congrArg Prod.snd (e.apply_symm_apply p)
  have hmix : ∀ w₀, B.d.mixT S ψ vT.μ vT.𝓕 f 0 w₀ = ∫ ξ in vT.𝓕, f (B.d.incX S ξ + B.d.inc0 S w₀) ∂vT.μ := by
    intro w₀
    change ∫ ξ in vT.𝓕, heisO ψ S B.V (B.d.incX S ξ) (heisO ψ S B.V (B.d.incAdj S 0)
      (heisO ψ S B.V (B.d.inc0 S w₀) f)) 0 ∂vT.μ = _
    congr 1
    funext ξ
    rw [HypDec.integrandT_eq, map_zero, symplOH_zero_right, AddChar.map_zero_eq_one, one_mul, add_zero]
  have hGi : IntegrableOn G (e ⁻¹' s) (P.map e.symm) := covolOne_integrableOn hcov G hGc hGper
  have hHi : Integrable H ((vT.μ.restrict vT.𝓕).prod (vL.μ.restrict vL.𝓕)) := by
    rw [Measure.prod_restrict]
    have h2 := (hmp.integrableOn_comp_preimage me.measurableEmbedding (f := H) (s := s)).1 (by
      have : H ∘ me = G := funext fun b => by
        rw [Function.comp_apply, ← hGH]
        exact congrArg G (e.symm_apply_apply b)
      rw [this]; exact hGi)
    exact h2
  refine ⟨?_, ?_⟩
  · calc ∫ b in vB.𝓕, f (x0 B ⬝ b) * star (y (zl B ⬝ b)) ∂vB.μ = ∫ b in vB.𝓕, G b ∂vB.μ := rfl
      _ = ∫ b in e ⁻¹' s, G b ∂(P.map e.symm) := (covolOne_integral_eq vB.covol hcov G hGper).symm
      _ = ∫ p in s, H p ∂P := by
        have h3 := hmp.setIntegral_preimage_emb me.measurableEmbedding H s
        rw [← h3]
        refine congrArg (fun F : Mx D (σ + 1) S.rank → ℂ => ∫ b in e ⁻¹' s, F b ∂(P.map e.symm)) (funext fun b => ?_)
        rw [← hGH]
        exact (congrArg G (e.symm_apply_apply b)).symm
      _ = ∫ v in vL.𝓕, ∫ ξ in vT.𝓕, H (ξ, v) ∂vT.μ ∂vL.μ := by
        rw [hP, ← Measure.prod_restrict]
        exact integral_prod_symm H hHi
      _ = _ := by
        change _ = ∫ v in vL.𝓕, B.d.mixT S ψ vT.μ vT.𝓕 f 0 ((B.o.resT S).symm (0, v)) * star (y v) ∂vL.μ
        congr 1
        funext v
        rw [hmix, ← integral_mul_const]
  · have hψe : ∀ a, ‖ψ a‖ₑ = 1 := fun a => by rw [← ofReal_norm_eq_enorm, hψn, ENNReal.ofReal_one]
    set K : Mx D σ S.rank × Mx D B.L.rank S.rank → ENNReal :=
      fun p => ‖f (B.d.incX S p.1 + B.d.inc0 S ((B.o.resT S).symm (0, p.2)))‖ₑ with hK
    have hKc : Continuous K := by
      refine (hf.2.comp ?_).enorm
      simp only [HypDec.incX_apply, HypDec.wittDecomp_inclAnisotropicHom_apply, OrthDec.resT_symm_apply]
      exact (continuous_const.matrix_mul continuous_fst).add (continuous_const.matrix_mul
        (continuous_const.add (continuous_const.matrix_mul continuous_snd)))
    have hKe : ∀ b, K (e b) = ‖f (x0 B ⬝ b)‖ₑ := fun b => by rw [hK, hx b]
    have hper' : ∀ (γ : ratMx D (σ + 1) S.rank) (b : Mx D (σ + 1) S.rank),
        ‖f (x0 B ⬝ (γ +ᵥ b))‖ₑ = ‖f (x0 B ⬝ b)‖ₑ := by
      intro γ b
      rw [AddSubgroup.vadd_def, vadd_eq_add, hfx γ γ.2 b, enorm_mul, hψe, one_mul]
    have hF'' : IsAddFundamentalDomain (ratMx D (σ + 1) S.rank) (e ⁻¹' s) vB.μ := hμeq ▸ hF'
    calc ∫⁻ v in vL.𝓕, ‖B.d.mixT S ψ vT.μ vT.𝓕 f 0 ((B.o.resT S).symm (0, v))‖ₑ ∂vL.μ
        ≤ ∫⁻ v in vL.𝓕, ∫⁻ ξ in vT.𝓕, K (ξ, v) ∂vT.μ ∂vL.μ := by
          refine lintegral_mono fun v => ?_
          rw [hmix]
          exact enorm_integral_le_lintegral_enorm _
      _ = ∫⁻ p in s, K p ∂P := by
        rw [hP, ← Measure.prod_restrict, lintegral_prod_symm _ hKc.measurable.aemeasurable]
      _ = ∫⁻ b in e ⁻¹' s, K (e b) ∂(P.map e.symm) :=
        (hmp'.setLIntegral_comp_preimage_emb me.measurableEmbedding K s).symm
      _ = ∫⁻ b in e ⁻¹' s, ‖f (x0 B ⬝ b)‖ₑ ∂vB.μ := by
        rw [hμeq]; congr 1; funext b; exact hKe b
      _ = ∫⁻ b in vB.𝓕, ‖f (x0 B ⬝ b)‖ₑ ∂vB.μ := hF''.setLIntegral_eq vB.covol.2.1 _ hper'

end GlobalTheory.Unf.FB
