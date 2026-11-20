import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HeisenbergDerivativeThetaFunctionLaws
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FockPolynomialVectorLawsStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FockPolynomialVectorTestThetaZeroEqThetaSeriesStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Ker.ColChange

variable {D : D7} {S T : HSp D}

/- English proof (translation)
Establish `key : a • z = ((a.re : ℝ) : ℂ) • z + ((a.im : ℝ) : ℂ) • (I • z)`. Rewrite using `[smul_smul, ← add_smul, Complex.re_add_im]`. Rewrite using `[key, ha, hs, hs]`.
-/
theorem real_smul_split {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (d : V → W)
    (ha : ∀ x y, d (x + y) = d x + d y) (hs : ∀ (t : ℝ) x, d ((t : ℂ) • x) = (t : ℂ) • d x) (a : ℂ) (z : V) :
    d (a • z) = (a.re : ℂ) • d z + (a.im : ℂ) • d (I • z) := by
  have key : a • z = ((a.re : ℝ) : ℂ) • z + ((a.im : ℝ) : ℂ) • (I • z) := by
    rw [smul_smul, ← add_smul, Complex.re_add_im]
  rw [key, ha, hs, hs]

/- English proof (translation)
Establish `hL` using `GlobalTheory.Ker.HeisDeriv.dRho_laws D S T C f hf τ`. Establish `hc : ∀ x : Matrix (Fin T.rank) (Fin S.rank) ℂ, cplxO 1 s x = I • (s * x)`. Introduce `x`. Simplify using `only [cplxO, Matrix.mul_one]`. Establish `hneg : ∀ x : Matrix (Fin T.rank) (Fin S.rank) ℂ, Formalism.IndefR.Datum.dRho (heisO C.ψ S T) C.θ τ (-x) f = -Formalism.IndefR.Datum.dRho (heisO C.ψ S T) C.θ τ x f`.

Introduce `x`. Establish `h1` using `(hL x).2.2.2.2.2.1 (-1)`. Simplify using `using h1`. Establish `hadd : ∀ x y : Matrix (Fin T.rank) (Fin S.rank) ℂ, crea (heisO C.ψ S T) C.θ τ (cplxO 1 s) (x + y) f = crea (heisO C.ψ S T) C.θ τ (cplxO 1 s) x f + crea (heisO C.ψ S T) C.θ τ (cplxO 1 s) y f`. Introduce `x y`.

Establish `hc : cplxO 1 s (x + y) = cplxO 1 s x + cplxO 1 s y`. Simplify using `only [cplxO, Matrix.mul_add, Matrix.add_mul, smul_add]`. Unfold `crea`. Rewrite using `[hc, (hL x).2.2.2.2.1 y, (hL (cplxO 1 s x)).2.2.2.2.1 (cplxO 1 s y)]`. Simplify using `only [smul_add]`.

Normalize the expressions using the abelian group laws. Establish `hreal : ∀ (t : ℝ) (x : Matrix (Fin T.rank) (Fin S.rank) ℂ), crea (heisO C.ψ S T) C.θ τ (cplxO 1 s) ((t : ℂ) • x) f = (t : ℂ) • crea (heisO C.ψ S T) C.θ τ (cplxO 1 s) x f`. Introduce `t x`. Establish `hc' : cplxO 1 s ((t : ℂ) • x) = (t : ℂ) • cplxO 1 s x`. Rewrite using `[hc, hc, Matrix.mul_smul, smul_comm]`.

Unfold `crea`. Rewrite using `[hc', (hL x).2.2.2.2.2.1 t, (hL (cplxO 1 s x)).2.2.2.2.2.1 t, smul_sub, smul_comm I (t : ℂ)]`. Establish `key` using `real_smul_split (fun x => crea (heisO C.ψ S T) C.θ τ (cplxO 1 s) x f) hadd hreal a z`. Establish `e1 : cplxO 1 s (I • z) = (if p then -z else z)`. Rewrite using `[hc, Matrix.mul_smul, hz]`.

Apply the tactic sequence `split_ifs <;> simp [smul_smul]`. Establish `e2 : cplxO 1 s z = (if p then I • z else -(I • z))`. Rewrite using `[hc, hz]`. Apply the tactic sequence `split_ifs <;> simp`. Establish `hI : crea (heisO C.ψ S T) C.θ τ (cplxO 1 s) (I • z) f = (if p then I else -I) • crea (heisO C.ψ S T) C.θ τ (cplxO 1 s) z f`.

Unfold `crea`. Rewrite using `[e1, e2]`. Use `split_ifs`. Rewrite using `[hneg]`. Simplify using `only [smul_sub, smul_neg, smul_smul, Complex.I_mul_I, neg_smul, one_smul, sub_neg_eq_add]`.

Normalize the expressions using the abelian group laws. Rewrite using `[hneg]`. Simplify using `only [smul_neg, smul_add, smul_smul, neg_mul, Complex.I_mul_I, neg_neg, neg_smul, one_smul, sub_neg_eq_add]`. Normalize the expressions using the abelian group laws. Rewrite using `[key, hI]`.

Use `split_ifs`. Rewrite using `[smul_smul, ← add_smul, Complex.re_add_im]`. Rewrite using `[smul_smul, ← add_smul]`. Use `congr 1`. Apply the tactic sequence `apply Complex.ext <;> simp`.
-/
theorem crea_smul (C : Ctx S T) {f : WO S T → ℂ} (hf : C.IsTh f) (τ : D.what₂.Tau)
    (s : Matrix (Fin T.rank) (Fin T.rank) ℂ) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (p : Prop) [Decidable p]
    (hz : s * z = (if p then (1 : ℂ) else -1) • z) (a : ℂ) :
    crea (heisO C.ψ S T) C.θ τ (cplxO 1 s) (a • z) f =
      (if p then a else conj a) • crea (heisO C.ψ S T) C.θ τ (cplxO 1 s) z f := by
  have hL := GlobalTheory.Ker.HeisDeriv.dRho_laws D S T C f hf τ
  have hc : ∀ x : Matrix (Fin T.rank) (Fin S.rank) ℂ, cplxO 1 s x = I • (s * x) := by
    intro x
    simp only [cplxO, Matrix.mul_one]
  have hneg : ∀ x : Matrix (Fin T.rank) (Fin S.rank) ℂ, Formalism.IndefR.Datum.dRho (heisO C.ψ S T) C.θ τ (-x) f = -Formalism.IndefR.Datum.dRho (heisO C.ψ S T) C.θ τ x f := by
    intro x
    have h1 := (hL x).2.2.2.2.2.1 (-1)
    simpa using h1
  have hadd : ∀ x y : Matrix (Fin T.rank) (Fin S.rank) ℂ,
      crea (heisO C.ψ S T) C.θ τ (cplxO 1 s) (x + y) f = crea (heisO C.ψ S T) C.θ τ (cplxO 1 s) x f + crea (heisO C.ψ S T) C.θ τ (cplxO 1 s) y f := by
    intro x y
    have hc : cplxO 1 s (x + y) = cplxO 1 s x + cplxO 1 s y := by
      simp only [cplxO, Matrix.mul_add, Matrix.add_mul, smul_add]
    unfold crea
    rw [hc, (hL x).2.2.2.2.1 y, (hL (cplxO 1 s x)).2.2.2.2.1 (cplxO 1 s y)]
    simp only [smul_add]
    abel
  have hreal : ∀ (t : ℝ) (x : Matrix (Fin T.rank) (Fin S.rank) ℂ),
      crea (heisO C.ψ S T) C.θ τ (cplxO 1 s) ((t : ℂ) • x) f = (t : ℂ) • crea (heisO C.ψ S T) C.θ τ (cplxO 1 s) x f := by
    intro t x
    have hc' : cplxO 1 s ((t : ℂ) • x) = (t : ℂ) • cplxO 1 s x := by
      rw [hc, hc, Matrix.mul_smul, smul_comm]
    unfold crea
    rw [hc', (hL x).2.2.2.2.2.1 t, (hL (cplxO 1 s x)).2.2.2.2.2.1 t, smul_sub, smul_comm I (t : ℂ)]
  have key := real_smul_split (fun x => crea (heisO C.ψ S T) C.θ τ (cplxO 1 s) x f) hadd hreal a z
  have e1 : cplxO 1 s (I • z) = (if p then -z else z) := by
    rw [hc, Matrix.mul_smul, hz]
    split_ifs <;> simp [smul_smul]
  have e2 : cplxO 1 s z = (if p then I • z else -(I • z)) := by
    rw [hc, hz]
    split_ifs <;> simp
  have hI : crea (heisO C.ψ S T) C.θ τ (cplxO 1 s) (I • z) f = (if p then I else -I) • crea (heisO C.ψ S T) C.θ τ (cplxO 1 s) z f := by
    unfold crea
    rw [e1, e2]
    split_ifs
    · rw [hneg]
      simp only [smul_sub, smul_neg, smul_smul, Complex.I_mul_I, neg_smul, one_smul,
        sub_neg_eq_add]
      abel
    · rw [hneg]
      simp only [smul_neg, smul_add, smul_smul, neg_mul, Complex.I_mul_I, neg_neg, neg_smul, one_smul,
        sub_neg_eq_add]
      abel
  rw [key, hI]
  split_ifs
  · rw [smul_smul, ← add_smul, Complex.re_add_im]
  · rw [smul_smul, ← add_smul]
    congr 1
    apply Complex.ext <;> simp

/- English proof (translation)
Establish `hL` using `GlobalTheory.Ker.HeisDeriv.dRho_laws D S T C f hf τ`. Establish `hadd : ∀ x y : Matrix (Fin T.rank) (Fin S.rank) ℂ, crea (heisO C.ψ S T) C.θ τ (cplxO 1 s) (x + y) f = crea (heisO C.ψ S T) C.θ τ (cplxO 1 s) x f + crea (heisO C.ψ S T) C.θ τ (cplxO 1 s) y f`. Introduce `x y`. Establish `hc : cplxO 1 s (x + y) = cplxO 1 s x + cplxO 1 s y`. Simplify using `only [cplxO, Matrix.mul_add, Matrix.add_mul, smul_add]`.

Unfold `crea`. Rewrite using `[hc, (hL x).2.2.2.2.1 y, (hL (cplxO 1 s x)).2.2.2.2.1 (cplxO 1 s y)]`. Simplify using `only [smul_add]`. Normalize the expressions using the abelian group laws. Set `F : Matrix (Fin T.rank) (Fin S.rank) ℂ →+ (WO S T → ℂ)` to `AddMonoidHom.mk' (fun x => crea (heisO C.ψ S T) C.θ τ (cplxO 1 s) x f) hadd`.

Conclude with `map_sum F z t`.
-/
theorem crea_sum (C : Ctx S T) {f : WO S T → ℂ} (hf : C.IsTh f) (τ : D.what₂.Tau)
    (s : Matrix (Fin T.rank) (Fin T.rank) ℂ) {ι : Type} (t : Finset ι) (z : ι → Matrix (Fin T.rank) (Fin S.rank) ℂ) :
    crea (heisO C.ψ S T) C.θ τ (cplxO 1 s) (∑ l ∈ t, z l) f =
      ∑ l ∈ t, crea (heisO C.ψ S T) C.θ τ (cplxO 1 s) (z l) f := by
  have hL := GlobalTheory.Ker.HeisDeriv.dRho_laws D S T C f hf τ
  have hadd : ∀ x y : Matrix (Fin T.rank) (Fin S.rank) ℂ,
      crea (heisO C.ψ S T) C.θ τ (cplxO 1 s) (x + y) f = crea (heisO C.ψ S T) C.θ τ (cplxO 1 s) x f + crea (heisO C.ψ S T) C.θ τ (cplxO 1 s) y f := by
    intro x y
    have hc : cplxO 1 s (x + y) = cplxO 1 s x + cplxO 1 s y := by
      simp only [cplxO, Matrix.mul_add, Matrix.add_mul, smul_add]
    unfold crea
    rw [hc, (hL x).2.2.2.2.1 y, (hL (cplxO 1 s x)).2.2.2.2.1 (cplxO 1 s y)]
    simp only [smul_add]
    abel
  let F : Matrix (Fin T.rank) (Fin S.rank) ℂ →+ (WO S T → ℂ) :=
    AddMonoidHom.mk' (fun x => crea (heisO C.ψ S T) C.θ τ (cplxO 1 s) x f) hadd
  exact map_sum F z t

/- English proof (translation)
Unfold `unitMap`. Repeatedly rewrite using `[inv_one, Matrix.mul_one]`. Establish `hrow : Matrix.single i j (1 : ℂ) * H⁻¹ = ∑ l, H⁻¹ j l • Matrix.single i l (1 : ℂ)`. Use extensionality with `a b`. Apply the tactic sequence `by_cases ha : i = a <;> simp [ha, Matrix.mul_apply, Matrix.single_apply, Matrix.sum_apply]`.

Rewrite using `[Matrix.mul_assoc, hrow, Matrix.mul_sum]`. Repeatedly rewrite using `[Matrix.mul_smul]`.
-/
theorem unitMap_expand {m n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (B : Matrix (Fin m) (Fin m) ℂ) (i : Fin m) (j : Fin n) :
    unitMap H B i j = ∑ l, H⁻¹ j l • unitMap 1 B i l := by
  unfold unitMap
  simp_rw [inv_one, Matrix.mul_one]
  have hrow : Matrix.single i j (1 : ℂ) * H⁻¹ = ∑ l, H⁻¹ j l • Matrix.single i l (1 : ℂ) := by
    ext a b
    by_cases ha : i = a <;> simp [ha, Matrix.mul_apply, Matrix.single_apply, Matrix.sum_apply]
  rw [Matrix.mul_assoc, hrow, Matrix.mul_sum]
  simp_rw [Matrix.mul_smul]

/- English proof (translation)
Establish `hdet : IsUnit (B τ).det`. Establish `h` using `congrArg Matrix.det (hB τ)`. Rewrite `h` using `[Matrix.det_mul, Matrix.det_mul]`. Rewrite using `[isUnit_iff_ne_zero]`. Introduce `h0`.

Rewrite `h` using `[h0, mul_zero]`. Unfold `sgnM at h`. Rewrite `h` using `[Matrix.det_diagonal]`. Apply the tactic sequence `exact (Finset.prod_ne_zero_iff.mpr (fun a _ => by unfold sgn; split_ifs <;> norm_num)) h.symm`. Unfold `Ctx.sB unitMap`.

Rewrite using `[inv_one, Matrix.mul_one, Matrix.mul_assoc, ← Matrix.mul_assoc (B τ)⁻¹, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mul, Matrix.mul_assoc, ← Matrix.mul_smul]`. Use `congr 1`. Unfold `sgnM`. Use extensionality with `a b`. Simplify using `only [Matrix.diagonal_mul, Matrix.smul_apply, Matrix.single_apply, smul_eq_mul]`.

Distinguish the cases in `h : i = a ∧ l = b`. Take `⟨rfl, rfl⟩` from `h`. Simplify using `only [and_self, if_true, mul_one]`. Unfold `sgn`. Apply the tactic sequence `split_ifs <;> norm_num`.

Simplify using `[h]`.
-/
theorem sB_unitMap (C : Ctx S T) {B : C.Bas} (hB : C.IsB B) (τ : D.what₂.Tau) (i : Fin T.rank) (l : Fin S.rank) :
    C.sB B τ * unitMap 1 (B τ) i l = (if (i : ℕ) < C.X.p0 then (1 : ℂ) else -1) • unitMap 1 (B τ) i l := by
  have hdet : IsUnit (B τ).det := by
    have h := congrArg Matrix.det (hB τ)
    rw [Matrix.det_mul, Matrix.det_mul] at h
    rw [isUnit_iff_ne_zero]
    intro h0
    rw [h0, mul_zero] at h
    unfold sgnM at h
    rw [Matrix.det_diagonal] at h
    exact (Finset.prod_ne_zero_iff.mpr (fun a _ => by unfold sgn; split_ifs <;> norm_num)) h.symm
  unfold Ctx.sB unitMap
  rw [inv_one, Matrix.mul_one, Matrix.mul_assoc, ← Matrix.mul_assoc (B τ)⁻¹, Matrix.nonsing_inv_mul _ hdet,
    Matrix.one_mul, Matrix.mul_assoc, ← Matrix.mul_smul]
  congr 1
  unfold sgnM
  ext a b
  simp only [Matrix.diagonal_mul, Matrix.smul_apply, Matrix.single_apply, smul_eq_mul]
  by_cases h : i = a ∧ l = b
  · obtain ⟨rfl, rfl⟩ := h
    simp only [and_self, if_true, mul_one]
    unfold sgn
    split_ifs <;> norm_num
  · simp [h]

/- English proof (translation)
Establish `hm` using `h.2`. Simplify using `only [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HR, Formalism.UG.UJ, Subgroup.mem_mk, Submonoid.mem_mk, Subsemigroup.mem_mk, Set.mem_ofPred_eq] at hm`. Establish `hJ : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (F` using `D.host.F) (AF D.host.F) S.gram = 1 := by`. Rewrite using `[C.m.gS]`. Simplify using `[Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR]`.

Simplify using `only [hJ, Matrix.mul_one] at hm`. Establish `hc : ∀ x : AE D, C.θ τ (infPart D (sigR (AF D.host.F) D.sp.cm.sig x)) = starRingEnd ℂ (C.θ τ (infPart D x))` using `fun x => GlobalTheory.FockCompare.comp_cA C.inf τ x`. Unfold `compAt`. Use extensionality with `i j`. Establish `e` using `congrArg (fun A => C.θ τ (infPart D (A i j))) hm`.

Simplify using `only [Matrix.mul_apply, map_sum, map_mul, Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply, hc] at e`. Simplify using `only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.map_apply, Complex.star_def]`. Use `e.trans ?_` and prove the remaining obligations. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality.

Simplify using the standard rewrite rules. Simplify using `[Matrix.one_apply_ne hij]`.
-/
theorem compAt_unitary (C : Ctx S T) (h : GA D S) (τ : D.what₂.Tau) :
    (compAt C.θ τ (mt S h))ᴴ * compAt C.θ τ (mt S h) = 1 := by
  have hm := h.2
  simp only [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HR, Formalism.UG.UJ, Subgroup.mem_mk, Submonoid.mem_mk, Subsemigroup.mem_mk,
    Set.mem_ofPred_eq] at hm
  have hJ : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (F := D.host.F) (AF D.host.F) S.gram = 1 := by
    rw [C.m.gS]
    simp [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR]
  simp only [hJ, Matrix.mul_one] at hm
  have hc : ∀ x : AE D, C.θ τ (infPart D (sigR (AF D.host.F) D.sp.cm.sig x)) =
      starRingEnd ℂ (C.θ τ (infPart D x)) := fun x => GlobalTheory.FockCompare.comp_cA C.inf τ x
  unfold compAt
  ext i j
  have e := congrArg (fun A => C.θ τ (infPart D (A i j))) hm
  simp only [Matrix.mul_apply, map_sum, map_mul, Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply, hc] at e
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.map_apply, Complex.star_def]
  refine e.trans ?_
  by_cases hij : i = j
  · subst hij
    simp
  · simp [Matrix.one_apply_ne hij]

def colU (C : Ctx S T) (h : GA D S) (σ : C.X.Ψ) : GL (Fin S.rank) ℂ :=
  have e : (compAt C.θ (C.m.e.symm σ) (mt S h))ᵀ * (compAt C.θ (C.m.e.symm σ) (mt S h)).map conj = 1 := by
    have := congrArg (fun M => M.map conj) (compAt_unitary C h (C.m.e.symm σ))
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] at this
    rw [← this]
    congr 1
    ext a b
    simp
  ⟨(compAt C.θ (C.m.e.symm σ) (mt S h)).map conj, (compAt C.θ (C.m.e.symm σ) (mt S h))ᵀ, mul_eq_one_comm.1 e, e⟩

def sub (C : Ctx S T) (h : GA D S) :
    MvPolynomial (FVar D T.rank S.rank) ℂ →ₐ[ℂ] MvPolynomial (FVar D T.rank S.rank) ℂ :=
  MvPolynomial.aeval fun v => ∑ l, (if (v.2.1 : ℕ) < C.X.p0 then conj (compAt C.θ v.1 (mt S h) l v.2.2)
    else compAt C.θ v.1 (mt S h) l v.2.2) • MvPolynomial.X (v.1, v.2.1, l)

/- English proof (translation)
Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce `v`. Take `⟨σ, i, k⟩` from `v`. Simplify using `only [AlgHom.comp_apply, sub, MvPolynomial.aeval_X, Ctx.toH, map_sum, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.aeval_C]`. Establish `hσ : C.m.e.symm (C.m.e σ) = σ` using `C.m.e.symm_apply_apply σ`.

Break down `hi : (rowIdx C.hr).symm i with a | b` into its components or cases. Establish `hlt : ¬ ((i : ℕ) < C.X.p0)`. Establish `hi' : i = rowIdx C.hr (Sum.inl a)` using `by rw [← hi, Equiv.apply_symm_apply]`. Establish `h1` using `rowIdx_inl C.hr a`. Rewrite `h1` using `[← hi']`.

Use linear arithmetic over natural numbers and integers. Simplify using `only [Harm.colActHom, Harm.colSubst_X_xVar, Harm.xForm_apply]`. Simplify using `only [MvPolynomial.algHom_C, MvPolynomial.algebraMap_eq, hlt, ↓reduceIte, Finset.mul_sum]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `x _`.

Simplify using `only [colU, Units.inv_mk, Matrix.transpose_apply, hσ]`. Expand and normalize the polynomial expressions, which then agree. Establish `hlt : ((i : ℕ) < C.X.p0)`. Establish `hi' : i = rowIdx C.hr (Sum.inr b)` using `by rw [← hi, Equiv.apply_symm_apply]`. Establish `h1` using `rowIdx_inr C.hr b`.

Rewrite `h1` using `[← hi']`. Establish `h2` using `b.2`. Use linear arithmetic over natural numbers and integers. Simplify using `only [Harm.colActHom, Harm.colSubst_X_yVar, Harm.yForm_apply]`. Simplify using `only [MvPolynomial.algHom_C, MvPolynomial.algebraMap_eq, hlt, ↓reduceIte, Finset.mul_sum]`.

Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `x _`. Simplify using `only [colU, Units.val_mk, Matrix.map_apply, hσ]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem toH_sub (C : Ctx S T) (h : GA D S) : C.toH.comp (sub C h) = (Harm.colActHom (colU C h)).comp C.toH := by
  apply MvPolynomial.algHom_ext
  intro v
  obtain ⟨σ, i, k⟩ := v
  simp only [AlgHom.comp_apply, sub, MvPolynomial.aeval_X, Ctx.toH, map_sum, MvPolynomial.smul_eq_C_mul, map_mul,
    MvPolynomial.aeval_C]
  have hσ : C.m.e.symm (C.m.e σ) = σ := C.m.e.symm_apply_apply σ
  rcases hi : (rowIdx C.hr).symm i with a | b
  · have hlt : ¬ ((i : ℕ) < C.X.p0) := by
      have hi' : i = rowIdx C.hr (Sum.inl a) := by rw [← hi, Equiv.apply_symm_apply]
      have h1 := rowIdx_inl C.hr a
      rw [← hi'] at h1
      omega
    simp only [Harm.colActHom, Harm.colSubst_X_xVar, Harm.xForm_apply]
    simp only [MvPolynomial.algHom_C, MvPolynomial.algebraMap_eq, hlt, ↓reduceIte, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    simp only [colU, Units.inv_mk, Matrix.transpose_apply, hσ]
    ring
  · have hlt : ((i : ℕ) < C.X.p0) := by
      have hi' : i = rowIdx C.hr (Sum.inr b) := by rw [← hi, Equiv.apply_symm_apply]
      have h1 := rowIdx_inr C.hr b
      rw [← hi'] at h1
      have h2 := b.2
      omega
    simp only [Harm.colActHom, Harm.colSubst_X_yVar, Harm.yForm_apply]
    simp only [MvPolynomial.algHom_C, MvPolynomial.algebraMap_eq, hlt, ↓reduceIte, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    simp only [colU, Units.val_mk, Matrix.map_apply, hσ]
    ring

/- English proof (translation)
Introduce `D S T C h`. Use `⟨colU C h, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `σ`. Rewrite using `[Matrix.mem_unitaryGroup_iff]`. Establish `hst : star ((colU C h σ : Matrix (Fin S.rank) (Fin S.rank) ℂ)) = (((colU C h σ)⁻¹ : GL (Fin S.rank) ℂ) : Matrix (Fin S.rank) (Fin S.rank) ℂ)`.

Use extensionality with `a b`. Simplify using `[colU, Matrix.star_apply]`. Rewrite using `[hst]`. Conclude with `(colU C h σ).mul_inv`. Introduce `hh`.

Simplify using `only [Formalism.L2.Theta.GfC, MonoidHom.mem_ker, Formalism.L2.Theta.infHom] at hh`. Establish `hinf : (Formalism.L2.Theta.mt S h).map (infPart D) = 1`. Establish `e` using `congrArg (fun g : GL (Fin S.rank) (Ainf D.host.F ⊗[D.host.F] D.host.E) => (g : Matrix (Fin S.rank) (Fin S.rank) (Ainf D.host.F ⊗[D.host.F] D.host.E))) hh`. Conclude with `e`. Use function extensionality and compare the values at `σ`.

Use extensionality with `a b`. Establish `e` using `congrFun (congrFun hinf a) b`. Simplify using `only [Matrix.map_apply] at e`. Simplify using `only [colU, compAt, Matrix.map_apply, e]`. Distinguish the cases in `hab : a = b`.

Substitute `hab` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Matrix.one_apply_ne hab]`. Introduce `Q Q' hQ B hB f hf`. Establish `hL` using `GlobalTheory.T.fockPolynomialVector_laws D S T C B hB`.

Establish `hQ' : Q' = sub C h Q`. Apply `(GlobalTheory.T.fockPolynomialVector_testTheta_zero_eq_thetaSeries D S T C).1.1` to reduce the goal to its premises. Establish `e` using `congrArg (fun F => F Q) (toH_sub C h)`. Simplify using `only [AlgHom.comp_apply] at e`. Rewrite using `[hQ, ← e]`.

Substitute `hQ'` using the available equality. Use `clear hQ`. Unfold `Ctx.fvec`. Proceed by induction on `Q using MvPolynomial.induction_on with`. Consider the case `C a`.

Establish `hCa : (MvPolynomial.C a : MvPolynomial (FVar D T.rank S.rank) ℂ) = a • 1`. Rewrite using `[MvPolynomial.smul_eq_C_mul, mul_one]`. Rewrite using `[hCa, map_smul, map_smul, (hL (fun τ => compAt C.θ τ (Formalism.L2.Theta.mt S h)) f hf 1).2.2.1, map_one (sub C h), map_smul, (hL (fun _ => 1) f hf 1).2.2.1]`. Consider the case `add p q hp hq => rw [map_add, map_add, map_add, hp, hq]`. Consider the case `mul_X p v hp`.

Establish `hg` using `(hL (fun _ => 1) f hf (sub C h p)).1`. Establish `hH : (compAt C.θ v.1 (Formalism.L2.Theta.mt S h))⁻¹ = (compAt C.θ v.1 (Formalism.L2.Theta.mt S h))ᴴ` using `Matrix.inv_eq_left_inv (compAt_unitary C h v.1)`. Establish `hsX : sub C h (MvPolynomial.X v) = ∑ l, (if (v.2.1 : ℕ) < C.X.p0 then conj (compAt C.θ v.1 (Formalism.L2.Theta.mt S h) l v.2.2) else compAt C.θ v.1 (Formalism.L2.Theta.mt S h) l v.2.2) • MvPolynomial.X (v.1, v.2.1, l)`. Unfold `sub`. Rewrite using `[MvPolynomial.aeval_X]`.

Rewrite using `[mul_comm, (hL (fun τ => compAt C.θ τ (Formalism.L2.Theta.mt S h)) f hf p).2.1 v, hp, map_mul, hsX, Finset.sum_mul, map_sum]`. Simplify using `only [smul_mul_assoc, map_smul, (hL (fun _ => 1) f hf (sub C h p)).2.1]`. Unfold `aPlusAll aPlus`. Simplify using `only`. Rewrite using `[unitMap_expand (compAt C.θ v.1 (Formalism.L2.Theta.mt S h)), hH, crea_sum C hg, Finset.smul_sum]`.

Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `l _`. Rewrite using `[crea_smul C hg v.1 (C.sB B v.1) (unitMap 1 (B v.1) v.2.1 l) ((v.2.1 : ℕ) < C.X.p0) (sB_unitMap C hB v.1 v.2.1 l), Matrix.conjTranspose_apply, smul_smul, smul_smul]`. Use `congr 1`. Apply the tactic sequence `split_ifs <;> simp [mul_comm]`.
-/
theorem col_change : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), ∀ h : GA D S, ∃ u : C.X.Ψ → GL (Fin S.rank) ℂ, (∀ σ, (u σ : Matrix (Fin S.rank) (Fin S.rank) ℂ) ∈ Matrix.unitaryGroup (Fin S.rank) ℂ) ∧ (h ∈ GfC S → u = 1) ∧ ∀ Q Q' : MvPolynomial (FVar D T.rank S.rank) ℂ, C.toH Q' = Harm.colActHom u (C.toH Q) → ∀ B, C.IsB B → ∀ f, C.IsTh f → pureTensorO C.ψ C.θ S T (fun _ => 1) (C.sB B) (fun τ => compAt C.θ τ (mt S h)) B f Q = C.fvec B f Q' := by
  intro D S T C h
  refine ⟨colU C h, ?_, ?_, ?_⟩
  · intro σ
    rw [Matrix.mem_unitaryGroup_iff]
    have hst : star ((colU C h σ : Matrix (Fin S.rank) (Fin S.rank) ℂ)) =
        (((colU C h σ)⁻¹ : GL (Fin S.rank) ℂ) : Matrix (Fin S.rank) (Fin S.rank) ℂ) := by
      ext a b
      simp [colU, Matrix.star_apply]
    rw [hst]
    exact (colU C h σ).mul_inv
  · intro hh
    simp only [Formalism.L2.Theta.GfC, MonoidHom.mem_ker, Formalism.L2.Theta.infHom] at hh
    have hinf : (Formalism.L2.Theta.mt S h).map (infPart D) = 1 := by
      have e := congrArg (fun g : GL (Fin S.rank) (Ainf D.host.F ⊗[D.host.F] D.host.E) =>
        (g : Matrix (Fin S.rank) (Fin S.rank) (Ainf D.host.F ⊗[D.host.F] D.host.E))) hh
      exact e
    funext σ
    ext a b
    have e := congrFun (congrFun hinf a) b
    simp only [Matrix.map_apply] at e
    simp only [colU, compAt, Matrix.map_apply, e]
    by_cases hab : a = b
    · subst hab
      simp
    · simp [Matrix.one_apply_ne hab]
  · intro Q Q' hQ B hB f hf
    have hL := GlobalTheory.T.fockPolynomialVector_laws D S T C B hB
    have hQ' : Q' = sub C h Q := by
      apply (GlobalTheory.T.fockPolynomialVector_testTheta_zero_eq_thetaSeries D S T C).1.1
      have e := congrArg (fun F => F Q) (toH_sub C h)
      simp only [AlgHom.comp_apply] at e
      rw [hQ, ← e]
    subst hQ'
    clear hQ
    unfold Ctx.fvec
    induction Q using MvPolynomial.induction_on with
    | C a =>
      have hCa : (MvPolynomial.C a : MvPolynomial (FVar D T.rank S.rank) ℂ) = a • 1 := by
        rw [MvPolynomial.smul_eq_C_mul, mul_one]
      rw [hCa, map_smul, map_smul, (hL (fun τ => compAt C.θ τ (Formalism.L2.Theta.mt S h)) f hf 1).2.2.1, map_one (sub C h),
        map_smul, (hL (fun _ => 1) f hf 1).2.2.1]
    | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]
    | mul_X p v hp =>
      have hg := (hL (fun _ => 1) f hf (sub C h p)).1
      have hH : (compAt C.θ v.1 (Formalism.L2.Theta.mt S h))⁻¹ = (compAt C.θ v.1 (Formalism.L2.Theta.mt S h))ᴴ :=
        Matrix.inv_eq_left_inv (compAt_unitary C h v.1)
      have hsX : sub C h (MvPolynomial.X v) = ∑ l, (if (v.2.1 : ℕ) < C.X.p0 then
          conj (compAt C.θ v.1 (Formalism.L2.Theta.mt S h) l v.2.2) else compAt C.θ v.1 (Formalism.L2.Theta.mt S h) l v.2.2) •
          MvPolynomial.X (v.1, v.2.1, l) := by
        unfold sub
        rw [MvPolynomial.aeval_X]
      rw [mul_comm, (hL (fun τ => compAt C.θ τ (Formalism.L2.Theta.mt S h)) f hf p).2.1 v, hp, map_mul, hsX,
        Finset.sum_mul, map_sum]
      simp only [smul_mul_assoc, map_smul, (hL (fun _ => 1) f hf (sub C h p)).2.1]
      unfold aPlusAll aPlus
      dsimp only
      rw [unitMap_expand (compAt C.θ v.1 (Formalism.L2.Theta.mt S h)), hH, crea_sum C hg, Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro l _
      rw [crea_smul C hg v.1 (C.sB B v.1) (unitMap 1 (B v.1) v.2.1 l) ((v.2.1 : ℕ) < C.X.p0)
        (sB_unitMap C hB v.1 v.2.1 l), Matrix.conjTranspose_apply, smul_smul, smul_smul]
      congr 1
      split_ifs <;> simp [mul_comm]

end GlobalTheory.Ker.ColChange

end
