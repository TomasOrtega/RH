import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SplitPart
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GaussianTwistedRealReadingEntireAndInjectiveStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfLintegralEqZero
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsInverseChart
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FoldrHolDEqIteratedFDeriv
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.AdForm.JetRead

open Complex
open scoped ComplexConjugate

section Pure

variable {ι : Type} [Fintype ι] {a b : ℕ}

def pr (z U : VCx ι a b) : ℂ := ∑ τ, ∑ i, ∑ j, z τ i j * conj (U τ i j)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem HV_eq (sc : ℝ) (z w : VCx ι a b) : HV sc z w = (sc : ℂ) * pr z w := rfl

/- English proof (translation)
Simplify using `only [pr, Pi.add_apply, add_mul, Finset.sum_add_distrib]`.
-/
theorem pr_add_left (z z' U : VCx ι a b) : pr (z + z') U = pr z U + pr z' U := by
  simp only [pr, Pi.add_apply, add_mul, Finset.sum_add_distrib]

/- English proof (translation)
Simplify using `only [pr, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]`.
-/
theorem pr_add_right (z U U' : VCx ι a b) : pr z (U + U') = pr z U + pr z U' := by
  simp only [pr, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]

/- English proof (translation)
Simplify using `only [pr, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]`.
-/
theorem pr_smul_left (c : ℂ) (z U : VCx ι a b) : pr (c • z) U = c * pr z U := by
  simp only [pr, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

/- English proof (translation)
Simplify using `only [pr, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring` and prove the remaining obligations.
-/
theorem pr_smul_right (c : ℂ) (z U : VCx ι a b) : pr z (c • U) = conj c * pr z U := by
  simp only [pr, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/- English proof (translation)
Simplify using `only [pr, map_sum, map_mul, Complex.conj_conj]`. Use `Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring` and prove the remaining obligations.
-/
theorem pr_swap (z U : VCx ι a b) : pr U z = conj (pr z U) := by
  simp only [pr, map_sum, map_mul, Complex.conj_conj]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

omit [Fintype ι] in
/- English proof (translation)
Use function extensionality and compare the values at `τ i j`. Simplify using `[Complex.real_smul]`.
-/
theorem real_smul_eq (t : ℝ) (v : VCx ι a b) : t • v = (t : ℂ) • v := by
  funext τ i j; simp [Complex.real_smul]

/- English proof (translation)
Rewrite using `[real_smul_eq, pr_add_left, pr_add_right, pr_add_right, pr_smul_left, pr_smul_left, pr_smul_right, pr_smul_right, Complex.conj_ofReal]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem pr_line (z v : VCx ι a b) (t : ℝ) :
    pr (z + t • v) (z + t • v) = pr z z + (t : ℂ) * (pr z v + pr v z) + (t : ℂ) ^ 2 * pr v v := by
  rw [real_smul_eq, pr_add_left, pr_add_right, pr_add_right, pr_smul_left, pr_smul_left, pr_smul_right,
    pr_smul_right, Complex.conj_ofReal]
  ring

def gs (sc : ℝ) (z : VCx ι a b) : ℂ := cexp (-((Real.pi : ℂ) / 2 * HV sc z z))

/- English proof (translation)
Simplify using `[gs, HV_eq]`.
-/
theorem gs_zero (sc : ℝ) : gs sc (0 : VCx ι a b) = 1 := by
  simp [gs, HV_eq]

/- English proof (translation)
Establish `h1 : HasDerivAt (fun t : ℝ => cexp ((t : ℂ) * K)) K 0`. Use `((hasDerivAt_id (0 : ℝ)).ofReal_comp.mul_const K).cexp` as an intermediate fact. Simplify using `using this`. Establish `hq : HasDerivAt (fun t : ℝ => -((Real.pi : ℂ) / 2 * ((sc : ℂ) * (pr z z + (t : ℂ) * (pr z v + pr v z) + (t : ℂ) ^ 2 * pr v v)))) (-((Real.pi : ℂ) / 2 * ((sc : ℂ) * (pr z v + pr v z)))) 0`. Establish `ht : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 0` using `(hasDerivAt_id (0 : ℝ)).ofReal_comp`.

Use `((((ht.mul_const (pr z v + pr v z)).const_add (pr z z)).add ((ht.pow 2).mul_const (pr v v))).const_mul (sc : ℂ)).const_mul ((Real.pi : ℂ) / 2) |>.neg` as an intermediate fact. Use `this.congr_deriv ?_` and prove the remaining obligations. Simplify using the standard rewrite rules. Establish `h2 : HasDerivAt (fun t : ℝ => gs sc (z + t • v)) (gs sc z * (-((Real.pi : ℂ) / 2 * ((sc : ℂ) * (pr z v + pr v z))))) 0`. Establish `e : (fun t : ℝ => gs sc (z + t • v)) = fun t : ℝ => cexp (-((Real.pi : ℂ) / 2 * ((sc : ℂ) * (pr z z + (t : ℂ) * (pr z v + pr v z) + (t : ℂ) ^ 2 * pr v v))))`.

Use function extensionality and compare the values at `t`. Rewrite using `[gs, HV_eq, pr_line]`. Rewrite using `[e]`. Conclude with `hq.cexp.congr_deriv (by simp [gs, HV_eq])`. Establish `hl : HasDerivAt (fun t : ℝ => z + t • v) v 0`.

Simplify using `using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add z`. Establish `h3 : HasDerivAt (fun t : ℝ => Φ (z + t • v)) (fderiv ℝ Φ z v) 0`. Use `(hΦ (z + (0 : ℝ) • v)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hl` as an intermediate fact. Rewrite `this` using `[zero_smul, add_zero]`. Conclude with `this`.

Conclude with `(h1.mul (h2.mul h3)).congr_deriv (by simp; ring)`.
-/
theorem hasDerivAt_line (sc : ℝ) (K : ℂ) (Φ : VCx ι a b → ℂ) (hΦ : Differentiable ℝ Φ) (z v : VCx ι a b) :
    HasDerivAt (fun t : ℝ => cexp ((t : ℂ) * K) * (gs sc (z + t • v) * Φ (z + t • v)))
      (gs sc z * ((K - (Real.pi / 2 : ℂ) * sc * (pr z v + pr v z)) * Φ z + fderiv ℝ Φ z v)) 0 := by
  have h1 : HasDerivAt (fun t : ℝ => cexp ((t : ℂ) * K)) K 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).ofReal_comp.mul_const K).cexp
    simpa using this
  have hq : HasDerivAt (fun t : ℝ => -((Real.pi : ℂ) / 2 * ((sc : ℂ) *
      (pr z z + (t : ℂ) * (pr z v + pr v z) + (t : ℂ) ^ 2 * pr v v))))
      (-((Real.pi : ℂ) / 2 * ((sc : ℂ) * (pr z v + pr v z)))) 0 := by
    have ht : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 0 := (hasDerivAt_id (0 : ℝ)).ofReal_comp
    have := ((((ht.mul_const (pr z v + pr v z)).const_add (pr z z)).add ((ht.pow 2).mul_const (pr v v))).const_mul
      (sc : ℂ)).const_mul ((Real.pi : ℂ) / 2) |>.neg
    refine this.congr_deriv ?_
    simp
  have h2 : HasDerivAt (fun t : ℝ => gs sc (z + t • v))
      (gs sc z * (-((Real.pi : ℂ) / 2 * ((sc : ℂ) * (pr z v + pr v z))))) 0 := by
    have e : (fun t : ℝ => gs sc (z + t • v)) = fun t : ℝ => cexp (-((Real.pi : ℂ) / 2 * ((sc : ℂ) *
        (pr z z + (t : ℂ) * (pr z v + pr v z) + (t : ℂ) ^ 2 * pr v v)))) := by
      funext t; rw [gs, HV_eq, pr_line]
    rw [e]
    exact hq.cexp.congr_deriv (by simp [gs, HV_eq])
  have hl : HasDerivAt (fun t : ℝ => z + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add z
  have h3 : HasDerivAt (fun t : ℝ => Φ (z + t • v)) (fderiv ℝ Φ z v) 0 := by
    have := (hΦ (z + (0 : ℝ) • v)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hl
    rw [zero_smul, add_zero] at this
    exact this
  exact (h1.mul (h2.mul h3)).congr_deriv (by simp; ring)

end Pure

section Adelic

variable {D : D7} {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

open GlobalTheory.FockCompare GlobalTheory.OrientedHeis

def zW (θ : InfFam D) (S T : HSp D) (δ : ℂ) (w : WO S T) : VCx D.what₂.Tau S.rank T.rank := -δ • piW θ T S w

def ux (τ : D.what₂.Tau) (u : Matrix (Fin T.rank) (Fin S.rank) ℂ) : VCx D.what₂.Tau S.rank T.rank :=
  fun τ' i j => if τ' = τ then u i j else 0

/- English proof (translation)
Establish `hex : ∃ w : Mx D T.rank S.rank, w.map (finPart D) = 0 ∧ ∀ τ, compAt θ τ w = y τ` using `⟨iotaW σ T S (fun τ i j => y τ i j), h.real_iota T S _, fun τ => by`. Use extensionality with `i j`. Conclude with `h.comp _ τ⟩`. Establish `hs` using `Classical.epsilon_spec hex`. Use `h.real_ext hs.1 (h.real_iota T S _) ?_` and prove the remaining obligations.

Rewrite using `[h.pi_iota]`. Use function extensionality and compare the values at `τ i j`. Conclude with `congrFun (congrFun (hs.2 τ) i) j`.
-/
theorem realPt_eq (h : GlobalTheory.FockCompare.Chart θ σ) (y : D.what₂.Tau → Matrix (Fin T.rank) (Fin S.rank) ℂ) :
    (realPt θ y : WO S T) = iotaW σ T S (fun τ i j => y τ i j) := by
  have hex : ∃ w : Mx D T.rank S.rank, w.map (finPart D) = 0 ∧ ∀ τ, compAt θ τ w = y τ :=
    ⟨iotaW σ T S (fun τ i j => y τ i j), h.real_iota T S _, fun τ => by
      ext i j; exact h.comp _ τ⟩
  have hs := Classical.epsilon_spec hex
  refine h.real_ext hs.1 (h.real_iota T S _) ?_
  rw [h.pi_iota]
  funext τ i j
  exact congrFun (congrFun (hs.2 τ) i) j

/- English proof (translation)
Unfold `zW`. Rewrite using `[AddMonoidHom.map_add, h.pi_iota, smul_add]`.
-/
theorem zW_add_iota (h : GlobalTheory.FockCompare.Chart θ σ) (δ : ℂ) (w : WO S T) (x : VCx D.what₂.Tau S.rank T.rank) :
    zW θ S T δ (w + iotaW σ T S x) = zW θ S T δ w + -δ • x := by
  unfold zW
  rw [AddMonoidHom.map_add, h.pi_iota, smul_add]

/- English proof (translation)
Unfold `zW`. Rewrite using `[AddMonoidHom.map_zero, smul_zero]`.
-/
theorem zW_zero (δ : ℂ) : zW θ S T δ (0 : WO S T) = 0 := by
  unfold zW; rw [AddMonoidHom.map_zero, smul_zero]

/- English proof (translation)
Establish `h2` using `h.real_iota T S x`. Use extensionality with `i j`. Establish `a1` using `congrFun (congrFun hw i) j`. Establish `a2` using `congrFun (congrFun h2 i) j`. Simplify using `only [Matrix.map_apply, Matrix.zero_apply] at a1 a2 ⊢`.

Rewrite using `[Matrix.add_apply, (finPart D).map_add, a1, a2, add_zero]`.
-/
theorem isReal_add_iota (h : GlobalTheory.FockCompare.Chart θ σ) {w : WO S T} (hw : w.map (finPart D) = 0) (x : VCx D.what₂.Tau S.rank T.rank) :
    (w + iotaW σ T S x).map (finPart D) = 0 := by
  have h2 := h.real_iota T S x
  ext i j
  have a1 := congrFun (congrFun hw i) j
  have a2 := congrFun (congrFun h2 i) j
  simp only [Matrix.map_apply, Matrix.zero_apply] at a1 a2 ⊢
  rw [Matrix.add_apply, (finPart D).map_add, a1, a2, add_zero]

/- English proof (translation)
Establish `hp : (realPt θ fun τ => Matrix.of fun i j => -(δ⁻¹ * zW θ S T δ w τ (Fin.cast rfl i) (Fin.cast rfl j)) : WO S T) = w`. Rewrite using `[realPt_eq h]`. Use `(congrArg (iotaW σ T S) ?_).trans (h.iota_pi hw)` and prove the remaining obligations. Use function extensionality and compare the values at `τ i j`. Simplify using `only [Matrix.of_apply, Fin.cast_eq_self, zW, Pi.smul_apply, smul_eq_mul]`.

Clear the denominators using the available nonvanishing facts. Rewrite using `[xiN, hp, gs, ← mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, one_mul]`.
-/
theorem eq_gs_xiN (h : GlobalTheory.FockCompare.Chart θ σ) {δ : ℂ} (hδ : δ ≠ 0) (sc : ℝ) (f : WO S T → ℂ) {w : WO S T}
    (hw : w.map (finPart D) = 0) :
    f w = gs sc (zW θ S T δ w) * xiN θ S T rfl rfl δ sc f (zW θ S T δ w) := by
  have hp : (realPt θ fun τ => Matrix.of fun i j => -(δ⁻¹ * zW θ S T δ w τ (Fin.cast rfl i) (Fin.cast rfl j)) : WO S T)
      = w := by
    rw [realPt_eq h]
    refine (congrArg (iotaW σ T S) ?_).trans (h.iota_pi hw)
    funext τ i j
    simp only [Matrix.of_apply, Fin.cast_eq_self, zW, Pi.smul_apply, smul_eq_mul]
    field_simp
  rw [xiN, hp, gs, ← mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, one_mul]

/- English proof (translation)
Establish `hL` using `isLineAt_lineAt h.inf τ u`. Use `h.real_ext (hL.2.1 t) (h.real_iota T S _) ?_` and prove the remaining obligations. Rewrite using `[h.pi_iota]`. Use function extensionality and compare the values at `τ' i j`. Establish `e` using `congrFun (congrFun (hL.2.2 t τ') i) j`.

Rewrite using `[piW_apply]`. Use `e.trans ?_` and prove the remaining obligations. Simplify using `only [ux, Pi.smul_apply]`. Apply the tactic sequence `split_ifs <;> simp [Complex.real_smul]`.
-/
theorem lineAt_eq (h : GlobalTheory.FockCompare.Chart θ σ) (τ : D.what₂.Tau) (u : Matrix (Fin T.rank) (Fin S.rank) ℂ) (t : ℝ) :
    (lineAt θ τ u t : WO S T) = iotaW σ T S (t • ux τ u) := by
  have hL := isLineAt_lineAt h.inf τ u
  refine h.real_ext (hL.2.1 t) (h.real_iota T S _) ?_
  rw [h.pi_iota]
  funext τ' i j
  have e := congrFun (congrFun (hL.2.2 t τ') i) j
  rw [piW_apply]
  refine e.trans ?_
  simp only [ux, Pi.smul_apply]
  split_ifs <;> simp [Complex.real_smul]

end Adelic

section Form

variable {D : D7} {θ : InfFam D} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

open GlobalTheory.FockCompare GlobalTheory.OrientedHeis

/- English proof (translation)
Establish `hS1 : ∀ a b, tauE D τ ((S.gram⁻¹) a b) = if a = b then 1 else 0` using `fun a b => by`. Apply the tactic sequence `rw [hP.gS, inv_one, Matrix.one_apply]; split_ifs <;> simp`. Establish `hT1 : ∀ a b, tauE D τ (T.gram a b) = if a = b then 1 else 0` using `fun a b => by`. Apply the tactic sequence `rw [hP.gT, Matrix.one_apply]; split_ifs <;> simp`. Establish `hs : ∑ a, ∑ b, ∑ e, ∑ d, tauE D τ (S.gram⁻¹ a b) * conj (y e b) * tauE D τ (T.gram e d) * x d a = ∑ i, ∑ j, x i j * conj (y i j)`.

Simplify using `only [hS1, hT1, ite_mul, mul_ite, one_mul, zero_mul, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]`. Establish `h1 : ∀ a : Fin S.rank, (∑ b : Fin S.rank, ∑ e : Fin T.rank, if a = b then conj (y e b) * x e a else 0) = ∑ e : Fin T.rank, conj (y e a) * x e a` using `fun a => by`. Rewrite using `[Finset.sum_eq_single a (fun b _ hb => by simp [Ne.symm hb]) (by simp)]`. Simplify using the standard rewrite rules. Simplify using `only [h1]`.

Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => mul_comm (conj (y i j)) (x i j)`. Unfold `formAt`. Rewrite using `[hs, hP.xi]`. Use `push_cast`.

Rewrite using `[Complex.re_eq_add_conj]`. Simplify using `only [map_mul, Complex.conj_I, map_inv₀, Complex.conj_ofReal]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem formAt_eq {δ : ℂ} {sc : ℝ} (hP : StdPair θ S T δ sc ψ) (τ : D.what₂.Tau) (x y : Fin T.rank → Fin S.rank → ℂ) :
    ((formAt S T τ x y : ℝ) : ℂ) = I * ((Real.sqrt D.host.d)⁻¹ : ℝ) * (∑ i, ∑ j, x i j * conj (y i j)) -
      I * ((Real.sqrt D.host.d)⁻¹ : ℝ) * conj (∑ i, ∑ j, x i j * conj (y i j)) := by
  have hS1 : ∀ a b, tauE D τ ((S.gram⁻¹) a b) = if a = b then 1 else 0 := fun a b => by
    rw [hP.gS, inv_one, Matrix.one_apply]; split_ifs <;> simp
  have hT1 : ∀ a b, tauE D τ (T.gram a b) = if a = b then 1 else 0 := fun a b => by
    rw [hP.gT, Matrix.one_apply]; split_ifs <;> simp
  have hs : ∑ a, ∑ b, ∑ e, ∑ d, tauE D τ (S.gram⁻¹ a b) * conj (y e b) * tauE D τ (T.gram e d) * x d a =
      ∑ i, ∑ j, x i j * conj (y i j) := by
    simp only [hS1, hT1, ite_mul, mul_ite, one_mul, zero_mul, mul_one, mul_zero, Finset.sum_ite_eq,
      Finset.mem_univ, if_true]
    have h1 : ∀ a : Fin S.rank, (∑ b : Fin S.rank, ∑ e : Fin T.rank,
        if a = b then conj (y e b) * x e a else 0) = ∑ e : Fin T.rank, conj (y e a) * x e a := fun a => by
      rw [Finset.sum_eq_single a (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
      simp
    simp only [h1]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => mul_comm (conj (y i j)) (x i j)
  unfold formAt
  rw [hs, hP.xi]
  push_cast
  rw [Complex.re_eq_add_conj]
  simp only [map_mul, Complex.conj_I, map_inv₀, Complex.conj_ofReal]
  ring

/- English proof (translation)
Use `show ((∑ τ, formAt S T τ (y τ) (U τ) : ℝ) : ℂ) = _`. Rewrite using `[Complex.ofReal_sum]`. Simplify using `only [formAt_eq hP]`. Rewrite using `[Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← map_sum, mul_sub]`. Both sides reduce to the same expression.
-/
theorem omO_eq {δ : ℂ} {sc : ℝ} (hP : StdPair θ S T δ sc ψ) (y U : VCx D.what₂.Tau S.rank T.rank) :
    ((omO S T y U : ℝ) : ℂ) = I * ((Real.sqrt D.host.d)⁻¹ : ℝ) * (pr y U - conj (pr y U)) := by
  show ((∑ τ, formAt S T τ (y τ) (U τ) : ℝ) : ℂ) = _
  rw [Complex.ofReal_sum]
  simp only [formAt_eq hP]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← map_sum, mul_sub]
  rfl

end Form

section Step

variable {D : D7} {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

open GlobalTheory.FockCompare GlobalTheory.OrientedHeis

def lamU (D : D7) {ι : Type} [Fintype ι] {a b : ℕ} (δ : ℂ) (U z : VCx ι a b) : ℂ :=
  2 * Real.pi * ((Real.sqrt D.host.d)⁻¹ : ℝ) * conj (pr z U / δ)

/- English proof (translation)
Simplify using `only [lamU, pr_add_left, add_div, map_add]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem lamU_add {ι : Type} [Fintype ι] {a b : ℕ} (δ : ℂ) (U z z' : VCx ι a b) :
    lamU D δ U (z + z') = lamU D δ U z + lamU D δ U z' := by
  simp only [lamU, pr_add_left, add_div, map_add]; ring

/- English proof (translation)
Simplify using `only [lamU, pr_smul_left, mul_div_assoc, map_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem lamU_smul {ι : Type} [Fintype ι] {a b : ℕ} (δ : ℂ) (U z : VCx ι a b) (t : ℂ) :
    lamU D δ U (t • z) = conj t * lamU D δ U z := by
  simp only [lamU, pr_smul_left, mul_div_assoc, map_mul]; ring

/- English proof (translation)
Simplify using `only [lamU, pr_smul_right, Complex.conj_I, mul_div_assoc, map_mul, map_neg]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem lamU_smul_dir {ι : Type} [Fintype ι] {a b : ℕ} (δ : ℂ) (U z : VCx ι a b) :
    lamU D δ (I • U) z = I * lamU D δ U z := by
  simp only [lamU, pr_smul_right, Complex.conj_I, mul_div_assoc, map_mul, map_neg]; ring

/- English proof (translation)
Establish `h` using `congrArg (fun x : ℝ => (x : ℂ)) hP.scale`. Simplify using `only [Complex.ofReal_mul, Complex.ofReal_pow] at h`. Rewrite using `[Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow, h]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sc_mul {δ : ℂ} {sc : ℝ} (hP : StdPair θ S T δ sc ψ) :
    (sc : ℂ) * (δ * conj δ) = 2 * ((Real.sqrt D.host.d)⁻¹ : ℝ) := by
  have h := congrArg (fun x : ℝ => (x : ℂ)) hP.scale
  simp only [Complex.ofReal_mul, Complex.ofReal_pow] at h
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow, h]
  push_cast; ring

/- English proof (translation)
Establish `hδ` using `hP.ne`. Use `set z := zW θ S T δ w with hz`. Use `set ω := omO S T (piW θ T S w) (ux τ u) with hω`. Establish `hfun : (fun t : ℝ => heisO ψ S T (lineAt θ τ u t) F w) = fun t : ℝ => cexp ((t : ℂ) * (-(Real.pi * I) * (ω : ℂ))) * (gs sc (z + t • (-δ • ux τ u)) * Φ (z + t • (-δ • ux τ u)))`. Use function extensionality and compare the values at `t`.

Rewrite using `[lineAt_eq h, heisO_iota h hP.std, hF _ (isReal_add_iota h hw _), zW_add_iota h, LinearMap.map_smul, smul_comm (-δ) t (ux τ u)]`. Use `congr 2`. Rewrite using `[smul_eq_mul, Complex.ofReal_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[Formalism.IndefR.Datum.dRho, hfun, (hasDerivAt_line sc _ Φ hΦ z _).deriv]`.

Use `congr 2`. Establish `hpw : piW θ T S w = (-δ)⁻¹ • z`. Rewrite using `[hz, zW, smul_smul, inv_mul_cancel₀ (neg_ne_zero.2 hδ), one_smul]`. Establish `hcδ : conj δ ≠ 0` using `(map_ne_zero _).2 hδ`. Establish `hsc` using `sc_mul hP`.

Use `congr 1`. Rewrite using `[hω, omO_eq hP, hpw, pr_smul_left, pr_swap z (-δ • ux τ u), pr_smul_right]`. Simplify using `only [lamU, map_mul, map_inv₀, map_neg, map_div₀, Complex.conj_conj]`. Generalize the expression as in `(((Real.sqrt D.host.d)⁻¹ : ℝ) : ℂ) = R at hsc ⊢`. Establish `hsc' : (sc : ℂ) = 2 * R / (δ * conj δ)`.

Rewrite using `[← hsc]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[hsc']`. Clear the denominators using the available nonvanishing facts. Put the polynomial expressions in normal form.

Rewrite using `[Complex.I_sq]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem dRho_read {δ : ℂ} {sc : ℝ} (hP : StdPair θ S T δ sc ψ) (h : GlobalTheory.FockCompare.Chart θ σ)
    (Φ : VCx D.what₂.Tau S.rank T.rank → ℂ) (hΦ : Differentiable ℝ Φ) (F : WO S T → ℂ)
    (hF : ∀ w : WO S T, w.map (finPart D) = 0 → F w = gs sc (zW θ S T δ w) * Φ (zW θ S T δ w))
    (τ : D.what₂.Tau) (u : Matrix (Fin T.rank) (Fin S.rank) ℂ) (w : WO S T) (hw : w.map (finPart D) = 0) :
    Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ u F w = gs sc (zW θ S T δ w) *
      (lamU D δ (ux τ u) (zW θ S T δ w) * Φ (zW θ S T δ w) + fderiv ℝ Φ (zW θ S T δ w) (-δ • ux τ u)) := by
  have hδ := hP.ne
  set z := zW θ S T δ w with hz
  set ω := omO S T (piW θ T S w) (ux τ u) with hω
  have hfun : (fun t : ℝ => heisO ψ S T (lineAt θ τ u t) F w) = fun t : ℝ =>
      cexp ((t : ℂ) * (-(Real.pi * I) * (ω : ℂ))) * (gs sc (z + t • (-δ • ux τ u)) * Φ (z + t • (-δ • ux τ u))) := by
    funext t
    rw [lineAt_eq h, heisO_iota h hP.std, hF _ (isReal_add_iota h hw _), zW_add_iota h, LinearMap.map_smul,
      smul_comm (-δ) t (ux τ u)]
    congr 2
    rw [smul_eq_mul, Complex.ofReal_mul]
    ring
  rw [Formalism.IndefR.Datum.dRho, hfun, (hasDerivAt_line sc _ Φ hΦ z _).deriv]
  congr 2
  have hpw : piW θ T S w = (-δ)⁻¹ • z := by
    rw [hz, zW, smul_smul, inv_mul_cancel₀ (neg_ne_zero.2 hδ), one_smul]
  have hcδ : conj δ ≠ 0 := (map_ne_zero _).2 hδ
  have hsc := sc_mul hP
  congr 1
  rw [hω, omO_eq hP, hpw, pr_smul_left, pr_swap z (-δ • ux τ u), pr_smul_right]
  simp only [lamU, map_mul, map_inv₀, map_neg, map_div₀, Complex.conj_conj]
  generalize (((Real.sqrt D.host.d)⁻¹ : ℝ) : ℂ) = R at hsc ⊢
  have hsc' : (sc : ℂ) = 2 * R / (δ * conj δ) := by
    rw [← hsc]; field_simp
  rw [hsc']
  field_simp
  ring_nf
  rw [Complex.I_sq]
  ring

end Step

section Crea

variable {D : D7} {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

open GlobalTheory.FockCompare GlobalTheory.OrientedHeis

def cK (D : D7) : ℂ := ((Real.sqrt (2 * Real.pi * (Real.sqrt D.host.d)⁻¹) : ℝ) : ℂ)⁻¹

def dOp (D : D7) {ι : Type} [Fintype ι] {a b : ℕ} (δ : ℂ) (l : DVar ι a b) (Φ : VCx ι a b → ℂ) (z : VCx ι a b) : ℂ :=
  lamU D δ (coordX l) z * Φ z +
    (1 / 2 : ℂ) * (fderiv ℝ Φ z (-δ • coordX l) - I * fderiv ℝ Φ z (I • (-δ • coordX l)))

/- English proof (translation)
Establish `hn : ‖tauE D τ D.host.xi0‖ = (Real.sqrt D.host.d)⁻¹`. Rewrite using `[hP.xi τ, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.2 (Real.sqrt_nonneg _))]`. Rewrite using `[fockScale, hn, cK]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem fockScale_inv {δ : ℂ} {sc : ℝ} (hP : StdPair θ S T δ sc ψ) (τ : D.what₂.Tau) :
    ((fockScale D τ : ℝ) : ℂ)⁻¹ = cK D / 2 := by
  have hn : ‖tauE D τ D.host.xi0‖ = (Real.sqrt D.host.d)⁻¹ := by
    rw [hP.xi τ, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_of_nonneg
      (inv_nonneg.2 (Real.sqrt_nonneg _))]
  rw [fockScale, hn, cK]
  push_cast
  ring

/- English proof (translation)
Take `⟨τ, i, j⟩` from `l`. Use function extensionality and compare the values at `τ' i' j'`. Simplify using `only [ux, unitMap, coordX, inv_one, Matrix.one_mul, Matrix.mul_one, Matrix.single_apply]`. Apply the tactic sequence `by_cases h1 : τ' = τ <;> by_cases h2 : i' = i <;> by_cases h3 : j' = j <;> simp_all [eq_comm]`.
-/
theorem ux_unitMap (l : FVar D T.rank S.rank) :
    ux (S := S) l.1 (unitMap (1 : Matrix (Fin S.rank) (Fin S.rank) ℂ) (1 : Matrix (Fin T.rank) (Fin T.rank) ℂ)
      l.2.1 l.2.2) = coordX l := by
  obtain ⟨τ, i, j⟩ := l
  funext τ' i' j'
  simp only [ux, unitMap, coordX, inv_one, Matrix.one_mul, Matrix.mul_one, Matrix.single_apply]
  by_cases h1 : τ' = τ <;> by_cases h2 : i' = i <;> by_cases h3 : j' = j <;> simp_all [eq_comm]

/- English proof (translation)
Use function extensionality and compare the values at `τ' i j`. Simplify using `only [ux, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem ux_smul (τ : D.what₂.Tau) (c : ℂ) (u : Matrix (Fin T.rank) (Fin S.rank) ℂ) :
    ux (S := S) τ (c • u) = c • ux τ u := by
  funext τ' i j
  simp only [ux, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul]
  split_ifs <;> simp

/- English proof (translation)
Establish `hc : cplxO (1 : Matrix (Fin S.rank) (Fin S.rank) ℂ) (1 : Matrix (Fin T.rank) (Fin T.rank) ℂ) (unitMap (1 : Matrix (Fin S.rank) (Fin S.rank) ℂ) (1 : Matrix (Fin T.rank) (Fin T.rank) ℂ) l.2.1 l.2.2) = I • unitMap (1 : Matrix (Fin S.rank) (Fin S.rank) ℂ) (1 : Matrix (Fin T.rank) (Fi …`. Simplify using `only [cplxO, Matrix.one_mul, Matrix.mul_one]`. Simplify using `only [aPlusAll, aPlus, crea, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]`. Rewrite using `[hc, dRho_read hP h Φ hΦ F hF _ _ w hw, dRho_read hP h Φ hΦ F hF _ _ w hw, ux_smul, ux_unitMap, lamU_smul_dir, smul_comm (-δ) I, fockScale_inv hP]`. Unfold `dOp`.

Take the linear combination `(-(cK D / 2) * gs sc (zW θ S T δ w) * lamU D δ (coordX l) (zW θ S T δ w) * Φ (zW θ S T δ w)) * Complex.I_mul_I`.
-/
theorem aPlus_read {δ : ℂ} {sc : ℝ} (hP : StdPair θ S T δ sc ψ) (h : GlobalTheory.FockCompare.Chart θ σ)
    (Φ : VCx D.what₂.Tau S.rank T.rank → ℂ) (hΦ : Differentiable ℝ Φ) (F : WO S T → ℂ)
    (hF : ∀ w : WO S T, w.map (finPart D) = 0 → F w = gs sc (zW θ S T δ w) * Φ (zW θ S T δ w))
    (l : FVar D T.rank S.rank) (w : WO S T) (hw : w.map (finPart D) = 0) :
    aPlusAll (heisO ψ S T) θ (fun _ => cplxO (1 : Matrix (Fin S.rank) (Fin S.rank) ℂ) (1 : Matrix (Fin T.rank) (Fin T.rank) ℂ))
      (fun _ => 1) (fun _ => 1) l F w = gs sc (zW θ S T δ w) * (cK D * dOp D δ l Φ (zW θ S T δ w)) := by
  have hc : cplxO (1 : Matrix (Fin S.rank) (Fin S.rank) ℂ) (1 : Matrix (Fin T.rank) (Fin T.rank) ℂ)
      (unitMap (1 : Matrix (Fin S.rank) (Fin S.rank) ℂ) (1 : Matrix (Fin T.rank) (Fin T.rank) ℂ) l.2.1 l.2.2) =
      I • unitMap (1 : Matrix (Fin S.rank) (Fin S.rank) ℂ) (1 : Matrix (Fin T.rank) (Fin T.rank) ℂ) l.2.1 l.2.2 := by
    simp only [cplxO, Matrix.one_mul, Matrix.mul_one]
  simp only [aPlusAll, aPlus, crea, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  rw [hc, dRho_read hP h Φ hΦ F hF _ _ w hw, dRho_read hP h Φ hΦ F hF _ _ w hw, ux_smul, ux_unitMap,
    lamU_smul_dir, smul_comm (-δ) I, fockScale_inv hP]
  unfold dOp
  linear_combination (-(cK D / 2) * gs sc (zW θ S T δ w) * lamU D δ (coordX l) (zW θ S T δ w) *
    Φ (zW θ S T δ w)) * Complex.I_mul_I

end Crea

section Main

variable {D : D7}

/- English proof (translation)
Unfold `cK`. Use `inv_ne_zero (Complex.ofReal_ne_zero.2 (Real.sqrt_ne_zero'.2 ?_))` and prove the remaining obligations. Establish `h1 : (0 : ℝ) < (D.host.d : ℝ)`. Use `D.host.qd_big.2` as an intermediate fact. Conclude with `(by omega : 0 < D.host.d)` after adjusting the coercions.

Check the signs of the components of the expression.
-/
theorem cK_ne_zero (D : D7) : cK D ≠ 0 := by
  unfold cK
  refine inv_ne_zero (Complex.ofReal_ne_zero.2 (Real.sqrt_ne_zero'.2 ?_))
  have h1 : (0 : ℝ) < (D.host.d : ℝ) := by
    have := D.host.qd_big.2
    exact_mod_cast (by omega : 0 < D.host.d)
  positivity

/- English proof (translation)
Unfold `dOp`. Rewrite using `[fderiv_const_mul hΦ]`. Simplify using `only [_root_.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem dOp_const_mul {ι : Type} [Fintype ι] {a b : ℕ} (δ : ℂ) (l : DVar ι a b) (c : ℂ) (Φ : VCx ι a b → ℂ)
    (z : VCx ι a b) (hΦ : DifferentiableAt ℝ Φ z) :
    dOp D δ l (fun z => c * Φ z) z = c * dOp D δ l Φ z := by
  unfold dOp
  rw [fderiv_const_mul hΦ]
  simp only [_root_.smul_apply, smul_eq_mul]
  ring

/- English proof (translation)
Substitute `hn` using the available equality. Both sides reduce to the same expression.
-/
theorem iter_cast {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] {X : Type} (G : W → ℂ) (L : List X) (n : ℕ)
    (hn : L.length = n) (v : X → W) (h : ∀ i : Fin n, i.val < L.length) :
    iteratedFDeriv ℂ n G 0 (fun i => v (L.get ⟨i, h i⟩)) = iteratedFDeriv ℂ L.length G 0 (fun i => v (L.get i)) := by
  subst hn; rfl

end Main

/- English proof (translation)
Introduce `D ψ θ S T a b hS hT δ sc hP`. Substitute `hS hT` using the available equality. Take `⟨σ, h⟩` from `GlobalTheory.RealLineAt.exists_inverse_chart hP.inf`. Use `⟨cK D * -δ, mul_ne_zero (cK_ne_zero D) (neg_ne_zero.2 hP.ne), fun f hf P => ?_⟩` and prove the remaining obligations. Establish `hG : Differentiable ℂ (xiN θ S T rfl rfl δ sc f)` using `(GlobalTheory.T.gaussianTwistedRealReading_entire_and_injective D ψ θ S T _ _ rfl rfl δ sc hP).1 f hf`.

Use `set G := xiN θ S T rfl rfl δ sc f with hG0`. Set `A` to `aPlusAll (heisO ψ S T) θ (fun _ => cplxO (1 : Matrix (Fin S.rank) (Fin S.rank) ℂ) (1 : Matrix (Fin T.rank) (Fin T.rank) ℂ)) (fun _ => 1) (fun _ => 1)`. Set `u : FVar D T.rank S.rank → VCx D.what₂.Tau S.rank T.rank` to `fun l => -δ • coordX l`. Set `lam : FVar D T.rank S.rank → VCx D.what₂.Tau S.rank T.rank → ℂ` to `fun l z => lamU D δ (coordX l) z`. Establish `hops` using `GlobalTheory.Ker.CreOp.foldr_creation_zero _ _ u lam G (fun l => ⟨fun x y => lamU_add δ _ x y, fun t x => lamU_smul δ _ x t⟩) hG (dOp D δ) (fun _ _ _ => rfl)`.

Establish `key : ∀ L : List (FVar D T.rank S.rank), ∀ w : WO S T, w.map (finPart D) = 0 → L.foldr (fun i g => A i g) f w = gs sc (zW θ S T δ w) * (cK D ^ L.length * L.foldr (dOp D δ) G (zW θ S T δ w))`. Introduce `L`. Proceed by induction on `L with`. Consider the case `nil`. Introduce `w hw`.

Rewrite using `[List.foldr_nil, List.foldr_nil, List.length_nil, pow_zero, one_mul]`. Conclude with `eq_gs_xiN h hP.ne sc f hw`. Consider the case `cons l L ih`. Introduce `w hw`. Establish `hd0 : Differentiable ℝ (L.foldr (dOp D δ) G)` using `(hops L).1.differentiable (by simp)`.

Establish `hd : Differentiable ℝ (fun z => cK D ^ L.length * L.foldr (dOp D δ) G z)` using `hd0.const_mul _`. Rewrite using `[List.foldr_cons]`. Use `(aPlus_read hP h _ hd _ ih l w hw).trans ?_` and prove the remaining obligations. Rewrite using `[dOp_const_mul δ l _ _ _ (hd0 _), List.foldr_cons, List.length_cons, pow_succ]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hval : ∀ k : FVar D T.rank S.rank →₀ ℕ, opPow A k f 0 = (cK D * -δ) ^ (Multiset.card (Finsupp.toMultiset k)) * derivAt0 G k`. Introduce `k`. Establish `hz : (0 : WO S T).map (finPart D) = 0` using `by ext i j; simp`. Rewrite using `[opPow, key _ 0 hz, zW_zero, gs_zero, one_mul, (hops _).2, derivAt0, iter_cast G _ _ (Multiset.length_toList _) coordX]`. Establish `hsm : (fun k_1 : Fin (Finsupp.toMultiset k).toList.length => u ((Finsupp.toMultiset k).toList.get k_1)) = fun k_1 => (-δ) • coordX ((Finsupp.toMultiset k).toList.get k_1)` using `rfl`.

Establish `hl : (cK D * -δ) ^ Multiset.card (Finsupp.toMultiset k) = (cK D * -δ) ^ (Finsupp.toMultiset k).toList.length` using `by rw [Multiset.length_toList]`. Rewrite using `[hsm, ContinuousMultilinearMap.map_smul_univ, Finset.prod_const, Finset.card_univ, Fintype.card_fin, hl, smul_eq_mul, mul_pow]`. Expand and normalize the polynomial expressions, which then agree. Establish `hid : (fun v : FVar D T.rank S.rank => (v.1, Fin.cast (rfl : T.rank = T.rank) v.2.1, Fin.cast (rfl : S.rank = S.rank) v.2.2)) = id`. Use function extensionality and compare the values at `v`.

Both sides reduce to the same expression. Rewrite using `[pureTensorO, pureTensorL, Module.Basis.constr_apply, Finsupp.sum, Finset.sum_apply, jetP]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[hid, Finsupp.mapDomain_id, jetC]`. Express the relevant statement in the definitionally equal form `P.coeff k • opPow A k f 0 = _`.

Rewrite using `[hval, smul_eq_mul]`. Use `congr 1`. Use `congr 1`. Rewrite using `[Finsupp.card_toMultiset, Finsupp.prod, Finsupp.sum, Finset.prod_pow_eq_pow_sum]`. Both sides reduce to the same expression.
-/
theorem pureTensorO_zero_eq_jetP : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (a b : ℕ) (hS : S.rank = a) (hT : T.rank = b) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∃ s : ℂ, s ≠ 0 ∧ ∀ f, IsHol θ S T ψ f → ∀ P, pureTensorO ψ θ S T (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 1) f P 0 = jetP S T hS hT s (xiN θ S T hS hT δ sc f) P := by
  intro D ψ θ S T a b hS hT δ sc hP
  subst hS hT
  obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hP.inf
  refine ⟨cK D * -δ, mul_ne_zero (cK_ne_zero D) (neg_ne_zero.2 hP.ne), fun f hf P => ?_⟩
  have hG : Differentiable ℂ (xiN θ S T rfl rfl δ sc f) := (GlobalTheory.T.gaussianTwistedRealReading_entire_and_injective D ψ θ S T _ _ rfl rfl δ sc hP).1 f hf
  set G := xiN θ S T rfl rfl δ sc f with hG0
  let A := aPlusAll (heisO ψ S T) θ
    (fun _ => cplxO (1 : Matrix (Fin S.rank) (Fin S.rank) ℂ) (1 : Matrix (Fin T.rank) (Fin T.rank) ℂ))
    (fun _ => 1) (fun _ => 1)
  let u : FVar D T.rank S.rank → VCx D.what₂.Tau S.rank T.rank := fun l => -δ • coordX l
  let lam : FVar D T.rank S.rank → VCx D.what₂.Tau S.rank T.rank → ℂ := fun l z => lamU D δ (coordX l) z
  have hops := GlobalTheory.Ker.CreOp.foldr_creation_zero _ _ u lam G
    (fun l => ⟨fun x y => lamU_add δ _ x y, fun t x => lamU_smul δ _ x t⟩) hG (dOp D δ) (fun _ _ _ => rfl)
  have key : ∀ L : List (FVar D T.rank S.rank), ∀ w : WO S T, w.map (finPart D) = 0 →
      L.foldr (fun i g => A i g) f w =
        gs sc (zW θ S T δ w) * (cK D ^ L.length * L.foldr (dOp D δ) G (zW θ S T δ w)) := by
    intro L
    induction L with
    | nil =>
      intro w hw
      rw [List.foldr_nil, List.foldr_nil, List.length_nil, pow_zero, one_mul]
      exact eq_gs_xiN h hP.ne sc f hw
    | cons l L ih =>
      intro w hw
      have hd0 : Differentiable ℝ (L.foldr (dOp D δ) G) := (hops L).1.differentiable (by simp)
      have hd : Differentiable ℝ (fun z => cK D ^ L.length * L.foldr (dOp D δ) G z) := hd0.const_mul _
      rw [List.foldr_cons]
      refine (aPlus_read hP h _ hd _ ih l w hw).trans ?_
      rw [dOp_const_mul δ l _ _ _ (hd0 _), List.foldr_cons, List.length_cons, pow_succ]
      ring
  have hval : ∀ k : FVar D T.rank S.rank →₀ ℕ, opPow A k f 0 =
      (cK D * -δ) ^ (Multiset.card (Finsupp.toMultiset k)) * derivAt0 G k := by
    intro k
    have hz : (0 : WO S T).map (finPart D) = 0 := by ext i j; simp
    rw [opPow, key _ 0 hz, zW_zero, gs_zero, one_mul, (hops _).2, derivAt0,
      iter_cast G _ _ (Multiset.length_toList _) coordX]
    have hsm : (fun k_1 : Fin (Finsupp.toMultiset k).toList.length => u ((Finsupp.toMultiset k).toList.get k_1)) =
        fun k_1 => (-δ) • coordX ((Finsupp.toMultiset k).toList.get k_1) := rfl
    have hl : (cK D * -δ) ^ Multiset.card (Finsupp.toMultiset k) =
        (cK D * -δ) ^ (Finsupp.toMultiset k).toList.length := by rw [Multiset.length_toList]
    rw [hsm, ContinuousMultilinearMap.map_smul_univ, Finset.prod_const, Finset.card_univ, Fintype.card_fin, hl,
      smul_eq_mul, mul_pow]
    ring
  have hid : (fun v : FVar D T.rank S.rank => (v.1, Fin.cast (rfl : T.rank = T.rank) v.2.1,
      Fin.cast (rfl : S.rank = S.rank) v.2.2)) = id := by
    funext v; rfl
  rw [pureTensorO, pureTensorL, Module.Basis.constr_apply, Finsupp.sum, Finset.sum_apply, jetP]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hid, Finsupp.mapDomain_id, jetC]
  change P.coeff k • opPow A k f 0 = _
  rw [hval, smul_eq_mul]
  congr 1
  congr 1
  rw [Finsupp.card_toMultiset, Finsupp.prod, Finsupp.sum, Finset.prod_pow_eq_pow_sum]
  rfl

end GlobalTheory.AdForm.JetRead
