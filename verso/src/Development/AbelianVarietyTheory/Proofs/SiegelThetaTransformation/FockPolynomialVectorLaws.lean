import Mathlib
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaKernelOrthonormalFrameInDomainPeriodLinearStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaFunctionSpaceHeisenbergLawsStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HeisenbergDerivativeThetaFunctionLaws
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RealPeriodMapHomeomorphRiemannFormDensity

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Ker.FockAlg

section Generic

variable {ι X : Type} {A : ι → (X → ℂ) → (X → ℂ)} {P : (X → ℂ) → Prop}

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => exact hf`. Consider the case `cons i l ih => exact hA i _ ih`.
-/
theorem foldr_mem (hA : ∀ i f, P f → P (A i f)) {f : X → ℂ} (hf : P f) (l : List ι) :
    P (l.foldr (fun i g => A i g) f) := by
  induction l with
  | nil => exact hf
  | cons i l ih => exact hA i _ ih

/- English proof (translation)
Proceed by induction on `h with`. Consider the case `nil => rfl`. Consider the case `cons x _ ih => simp only [List.foldr_cons, ih]`. Consider the case `swap x y l => simp only [List.foldr_cons]`. Conclude with `hc _ _ _ (foldr_mem hA hf l)`.

Consider the case `trans _ _ ih1 ih2 => exact ih1.trans ih2`.
-/
theorem foldr_perm (hA : ∀ i f, P f → P (A i f)) (hc : ∀ i j f, P f → A i (A j f) = A j (A i f))
    {f : X → ℂ} (hf : P f) {l l' : List ι} (h : l.Perm l') :
    l.foldr (fun i g => A i g) f = l'.foldr (fun i g => A i g) f := by
  induction h with
  | nil => rfl
  | cons x _ ih => simp only [List.foldr_cons, ih]
  | swap x y l => simp only [List.foldr_cons]; exact hc _ _ _ (foldr_mem hA hf l)
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

/- English proof (translation)
Establish `hm : MvPolynomial.monomial k c = c • MvPolynomial.basisMonomials ι ℂ k`. Rewrite using `[MvPolynomial.coe_basisMonomials, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]`. Rewrite using `[hm, map_smul]`. Unfold `pureTensorL`. Rewrite using `[Module.Basis.constr_basis]`.
-/
theorem pure_monomial (f : X → ℂ) (k : ι →₀ ℕ) (c : ℂ) :
    pureTensorL A f (MvPolynomial.monomial k c) = c • opPow A k f := by
  have hm : MvPolynomial.monomial k c = c • MvPolynomial.basisMonomials ι ℂ k := by
    rw [MvPolynomial.coe_basisMonomials, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  rw [hm, map_smul]
  unfold pureTensorL
  rw [Module.Basis.constr_basis]

/- English proof (translation)
Rewrite using `[← map_one MvPolynomial.C, MvPolynomial.C_apply, pure_monomial, one_smul]`. Simplify using `[opPow]`.
-/
theorem pure_one (f : X → ℂ) : pureTensorL A f 1 = f := by
  rw [← map_one MvPolynomial.C, MvPolynomial.C_apply, pure_monomial, one_smul]
  simp [opPow]

/- English proof (translation)
Proceed by induction on `Q using MvPolynomial.induction_on' with`. Consider the case `monomial k c`. Rewrite using `[pure_monomial]`. Conclude with `hsm c _ (foldr_mem hA hf _)`. Consider the case `add p q hp hq`.

Rewrite using `[map_add]`. Conclude with `hadd _ _ hp hq`.
-/
theorem pure_mem (hadd : ∀ f f', P f → P f' → P (f + f')) (hsm : ∀ (a : ℂ) f, P f → P (a • f))
    (hA : ∀ i f, P f → P (A i f)) {f : X → ℂ} (hf : P f) (Q : MvPolynomial ι ℂ) : P (pureTensorL A f Q) := by
  induction Q using MvPolynomial.induction_on' with
  | monomial k c =>
    rw [pure_monomial]
    exact hsm c _ (foldr_mem hA hf _)
  | add p q hp hq =>
    rw [map_add]
    exact hadd _ _ hp hq

/- English proof (translation)
Use `show List.foldr (fun i g => A i g) f (Finsupp.toMultiset (Finsupp.single v 1 + k)).toList = List.foldr (fun i g => A i g) f (v :: (Finsupp.toMultiset k).toList)`. Apply `foldr_perm hA hc hf` to reduce the goal to its premises. Rewrite using `[← Multiset.coe_eq_coe, Multiset.coe_toList, ← Multiset.cons_coe, Multiset.coe_toList, map_add, Finsupp.toMultiset_single, one_nsmul, Multiset.singleton_add]`.
-/
private theorem opPow_single_add (hA : ∀ i f, P f → P (A i f))
    (hc : ∀ i j f, P f → A i (A j f) = A j (A i f)) {f : X → ℂ} (hf : P f) (k : ι →₀ ℕ) (v : ι) :
    opPow A (Finsupp.single v 1 + k) f = A v (opPow A k f) := by
  show List.foldr (fun i g => A i g) f (Finsupp.toMultiset (Finsupp.single v 1 + k)).toList =
    List.foldr (fun i g => A i g) f (v :: (Finsupp.toMultiset k).toList)
  apply foldr_perm hA hc hf
  rw [← Multiset.coe_eq_coe, Multiset.coe_toList, ← Multiset.cons_coe, Multiset.coe_toList, map_add,
    Finsupp.toMultiset_single, one_nsmul, Multiset.singleton_add]

/- English proof (translation)
Proceed by induction on `Q using MvPolynomial.induction_on' with`. Consider the case `monomial k c`. Establish `hk : P (opPow A k f)` using `foldr_mem hA hf _`. Use `show pureTensorL A f (MvPolynomial.monomial (Finsupp.single v 1) 1 * MvPolynomial.monomial k c) = _`. Rewrite using `[MvPolynomial.monomial_mul, one_mul, pure_monomial, pure_monomial, opPow_single_add hA hc hf, Asm v c _ hk]`.

Consider the case `add p q hp hq`. Rewrite using `[mul_add, map_add, map_add, hp, hq, Aadd v _ _ (pure_mem hadd hsm hA hf p) (pure_mem hadd hsm hA hf q)]`.
-/
theorem pure_X_mul (hadd : ∀ f f', P f → P f' → P (f + f')) (hsm : ∀ (a : ℂ) f, P f → P (a • f))
    (hA : ∀ i f, P f → P (A i f)) (hc : ∀ i j f, P f → A i (A j f) = A j (A i f))
    (Aadd : ∀ i f f', P f → P f' → A i (f + f') = A i f + A i f')
    (Asm : ∀ i (a : ℂ) f, P f → A i (a • f) = a • A i f)
    {f : X → ℂ} (hf : P f) (Q : MvPolynomial ι ℂ) (v : ι) :
    pureTensorL A f (MvPolynomial.X v * Q) = A v (pureTensorL A f Q) := by
  induction Q using MvPolynomial.induction_on' with
  | monomial k c =>
    have hk : P (opPow A k f) := foldr_mem hA hf _
    show pureTensorL A f (MvPolynomial.monomial (Finsupp.single v 1) 1 * MvPolynomial.monomial k c) = _
    rw [MvPolynomial.monomial_mul, one_mul, pure_monomial, pure_monomial,
      opPow_single_add hA hc hf, Asm v c _ hk]
  | add p q hp hq =>
    rw [mul_add, map_add, map_add, hp, hq,
      Aadd v _ _ (pure_mem hadd hsm hA hf p) (pure_mem hadd hsm hA hf q)]

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => rfl`. Consider the case `cons i l ih`. Simplify using `only [List.foldr_cons]`. Rewrite using `[ih]`.

Conclude with `Aadd i _ _ (foldr_mem hA hf l) (foldr_mem hA hf' l)`.
-/
private theorem foldr_apply_add (hA : ∀ i f, P f → P (A i f))
    (Aadd : ∀ i f f', P f → P f' → A i (f + f') = A i f + A i f')
    {f f' : X → ℂ} (hf : P f) (hf' : P f') (l : List ι) :
    l.foldr (fun i g => A i g) (f + f') = l.foldr (fun i g => A i g) f + l.foldr (fun i g => A i g) f' := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    simp only [List.foldr_cons]
    rw [ih]
    exact Aadd i _ _ (foldr_mem hA hf l) (foldr_mem hA hf' l)

/- English proof (translation)
Proceed by induction on `Q using MvPolynomial.induction_on' with`. Consider the case `monomial k c`. Rewrite using `[pure_monomial, pure_monomial, pure_monomial, ← smul_add]`. Use `congr 1`. Conclude with `foldr_apply_add hA Aadd hf hf' _`.

Consider the case `add p q hp hq`. Rewrite using `[map_add, map_add, map_add, hp, hq]`. Normalize the expressions using the abelian group laws.
-/
theorem pure_add (hA : ∀ i f, P f → P (A i f))
    (Aadd : ∀ i f f', P f → P f' → A i (f + f') = A i f + A i f')
    {f f' : X → ℂ} (hf : P f) (hf' : P f') (Q : MvPolynomial ι ℂ) :
    pureTensorL A (f + f') Q = pureTensorL A f Q + pureTensorL A f' Q := by
  induction Q using MvPolynomial.induction_on' with
  | monomial k c =>
    rw [pure_monomial, pure_monomial, pure_monomial, ← smul_add]
    congr 1
    exact foldr_apply_add hA Aadd hf hf' _
  | add p q hp hq =>
    rw [map_add, map_add, map_add, hp, hq]
    abel

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => rfl`. Consider the case `cons i l ih`. Simplify using `only [List.foldr_cons]`. Rewrite using `[ih]`.

Conclude with `hR i _ (foldr_mem hA hf l)`.
-/
private theorem foldr_apply_comm (hA : ∀ i f, P f → P (A i f)) (R : (X → ℂ) → (X → ℂ))
    (hR : ∀ i f, P f → A i (R f) = R (A i f)) {f : X → ℂ} (hf : P f) (l : List ι) :
    l.foldr (fun i g => A i g) (R f) = R (l.foldr (fun i g => A i g) f) := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    simp only [List.foldr_cons]
    rw [ih]
    exact hR i _ (foldr_mem hA hf l)

/- English proof (translation)
Proceed by induction on `Q using MvPolynomial.induction_on' with`. Consider the case `monomial k c`. Rewrite using `[pure_monomial, pure_monomial, Rsm]`. Use `congr 1`. Conclude with `foldr_apply_comm hA R hR hf _`.

Consider the case `add p q hp hq`. Rewrite using `[map_add, map_add, hp, hq, Radd]`.
-/
theorem pure_comm (hA : ∀ i f, P f → P (A i f)) (R : (X → ℂ) → (X → ℂ))
    (Radd : ∀ f f', R (f + f') = R f + R f') (Rsm : ∀ (a : ℂ) f, R (a • f) = a • R f)
    (hR : ∀ i f, P f → A i (R f) = R (A i f))
    {f : X → ℂ} (hf : P f) (Q : MvPolynomial ι ℂ) :
    pureTensorL A (R f) Q = R (pureTensorL A f Q) := by
  induction Q using MvPolynomial.induction_on' with
  | monomial k c =>
    rw [pure_monomial, pure_monomial, Rsm]
    congr 1
    exact foldr_apply_comm hA R hR hf _
  | add p q hp hq =>
    rw [map_add, map_add, hp, hq, Radd]

end Generic

variable {D : D7} {S T : HSp D} (C : Ctx S T)

/- English proof (translation)
Conclude with `((GlobalTheory.T.thetaFunction_space_heisenberg_laws D S T C).2.1 f f' hf hf').1`.
-/
theorem th_add {f f' : WO S T → ℂ} (hf : C.IsTh f) (hf' : C.IsTh f') : C.IsTh (f + f') := by
  exact ((GlobalTheory.T.thetaFunction_space_heisenberg_laws D S T C).2.1 f f' hf hf').1

/- English proof (translation)
Conclude with `((GlobalTheory.T.thetaFunction_space_heisenberg_laws D S T C).2.2 f hf).1 a`.
-/
theorem th_smul (a : ℂ) {f : WO S T → ℂ} (hf : C.IsTh f) : C.IsTh (a • f) := by
  exact ((GlobalTheory.T.thetaFunction_space_heisenberg_laws D S T C).2.2 f hf).1 a

/- English proof (translation)
Unfold `Ctx.rho heisO`. Use function extensionality and compare the values at `w`. Simplify using `only [Pi.add_apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem rho_add (u : WO S T) (f f' : WO S T → ℂ) : C.rho u (f + f') = C.rho u f + C.rho u f' := by
  unfold Ctx.rho heisO
  funext w
  simp only [Pi.add_apply]
  ring

/- English proof (translation)
Unfold `Ctx.rho heisO`. Use function extensionality and compare the values at `w`. Simplify using `only [Pi.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem rho_smul (u : WO S T) (a : ℂ) (f : WO S T → ℂ) : C.rho u (a • f) = a • C.rho u f := by
  unfold Ctx.rho heisO
  funext w
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

variable (τ : D.what₂.Tau) (J : Matrix (Fin T.rank) (Fin S.rank) ℂ → Matrix (Fin T.rank) (Fin S.rank) ℂ)
  (z : Matrix (Fin T.rank) (Fin S.rank) ℂ)

/- English proof (translation)
Unfold `aPlus crea`. Rewrite using `[sub_eq_add_neg, ← neg_smul]`.
-/
theorem aPlus_eq (f : WO S T → ℂ) : aPlus (heisO C.ψ S T) C.θ τ J z f =
    ((fockScale D τ : ℂ)⁻¹) • (dRho (heisO C.ψ S T) C.θ τ z f + (-I) • dRho (heisO C.ψ S T) C.θ τ (J z) f) := by
  unfold aPlus crea
  rw [sub_eq_add_neg, ← neg_smul]

/- English proof (translation)
Establish `L` using `HeisDeriv.dRho_laws D S T C f hf τ`. Rewrite using `[aPlus_eq]`. Conclude with `th_smul C _ (th_add C (L z).1 (th_smul C _ (L (J z)).1))`.
-/
theorem aPlus_th {f : WO S T → ℂ} (hf : C.IsTh f) : C.IsTh (aPlus (heisO C.ψ S T) C.θ τ J z f) := by
  have L := HeisDeriv.dRho_laws D S T C f hf τ
  rw [aPlus_eq]
  exact th_smul C _ (th_add C (L z).1 (th_smul C _ (L (J z)).1))

/- English proof (translation)
Establish `L` using `HeisDeriv.dRho_laws D S T C f hf τ`. Rewrite using `[aPlus_eq, aPlus_eq, aPlus_eq, (L z).2.2.1 f' hf', (L (J z)).2.2.1 f' hf']`. Simplify using `only [smul_add]`. Normalize the expressions using the abelian group laws.
-/
theorem aPlus_add {f f' : WO S T → ℂ} (hf : C.IsTh f) (hf' : C.IsTh f') :
    aPlus (heisO C.ψ S T) C.θ τ J z (f + f') =
      aPlus (heisO C.ψ S T) C.θ τ J z f + aPlus (heisO C.ψ S T) C.θ τ J z f' := by
  have L := HeisDeriv.dRho_laws D S T C f hf τ
  rw [aPlus_eq, aPlus_eq, aPlus_eq, (L z).2.2.1 f' hf', (L (J z)).2.2.1 f' hf']
  simp only [smul_add]
  abel

/- English proof (translation)
Establish `L` using `HeisDeriv.dRho_laws D S T C f hf τ`. Rewrite using `[aPlus_eq, aPlus_eq, (L z).2.2.2.1 a, (L (J z)).2.2.2.1 a, smul_comm (-I) a, ← smul_add, smul_comm]`.
-/
theorem aPlus_smul (a : ℂ) {f : WO S T → ℂ} (hf : C.IsTh f) :
    aPlus (heisO C.ψ S T) C.θ τ J z (a • f) = a • aPlus (heisO C.ψ S T) C.θ τ J z f := by
  have L := HeisDeriv.dRho_laws D S T C f hf τ
  rw [aPlus_eq, aPlus_eq, (L z).2.2.2.1 a, (L (J z)).2.2.2.1 a, smul_comm (-I) a, ← smul_add, smul_comm]

/- English proof (translation)
Establish `L` using `HeisDeriv.dRho_laws D S T C f hf τ`. Rewrite using `[aPlus_eq, aPlus_eq, (L z).2.2.2.2.2.2.1 u hu, (L (J z)).2.2.2.2.2.2.1 u hu, rho_smul, rho_add, rho_smul]`.
-/
theorem aPlus_rho {u : WO S T} (hu : IsFinPt u) {f : WO S T → ℂ} (hf : C.IsTh f) :
    aPlus (heisO C.ψ S T) C.θ τ J z (C.rho u f) = C.rho u (aPlus (heisO C.ψ S T) C.θ τ J z f) := by
  have L := HeisDeriv.dRho_laws D S T C f hf τ
  rw [aPlus_eq, aPlus_eq, (L z).2.2.2.2.2.2.1 u hu, (L (J z)).2.2.2.2.2.2.1 u hu, rho_smul, rho_add, rho_smul]

/- English proof (translation)
Unfold `hx`. Rewrite using `[Matrix.mulVec_smul, smul_dotProduct, smul_eq_mul]`.
-/
private theorem hx_smul_left_bas_idx (x : Frame C.X.Ψ T.rank) (c : ℂ) (z w : Fin C.g → ℂ) :
    hx C.X C.bas C.idx x (c • z) w = c * hx C.X C.bas C.idx x z w := by
  unfold hx
  rw [Matrix.mulVec_smul, smul_dotProduct, smul_eq_mul]

/- English proof (translation)
Unfold `hx`. Rewrite using `[Matrix.mulVec_smul, star_smul, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]`. Both sides reduce to the same expression.
-/
private theorem hx_smul_right_conj (x : Frame C.X.Ψ T.rank) (c : ℂ) (z w : Fin C.g → ℂ) :
    hx C.X C.bas C.idx x z (c • w) = conj c * hx C.X C.bas C.idx x z w := by
  unfold hx
  rw [Matrix.mulVec_smul, star_smul, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]
  rfl

noncomputable abbrev eDir (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (τ' : D.what₂.Tau)
    (z' : Matrix (Fin T.rank) (Fin S.rank) ℂ) : ℝ :=
  EFR C.X (Pi.single (C.m.e τ) (fun k a => conj (z a k)) : WR C.X S.rank)
    (Pi.single (C.m.e τ') (fun k a => conj (z' a k)) : WR C.X S.rank)

/- English proof (translation)
Take `⟨-, hmem, -, hz, -⟩` from `(GlobalTheory.T.thetaKernel_orthonormalFrame_inDomain_periodLinear D S T C).2 B hB`. Establish `hE` using `(zR_laws D.host.E T.rank C.X C.g C.q0 C.hr C.bas C.idx S.rank C.sympl C.even (C.xB B) hmem).2.1`. Simplify using `only [eDir]`. Rewrite using `[← hE, ← hE, ← hE, ← hE, hz, hz]`. Simplify using `only [Pi.smul_apply, hx_smul_left_bas_idx, hx_smul_right_conj, Complex.conj_I]`.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `congr 1`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Simplify using `only [← mul_assoc, neg_mul, Complex.I_mul_I, neg_neg, one_mul]`. Rewrite using `[← Finset.mul_sum, ← Finset.mul_sum]`.

Simplify using the standard rewrite rules.
-/
theorem eDir_cplx {B : C.Bas} (hB : C.IsB B) (τ' : D.what₂.Tau) (z' : Matrix (Fin T.rank) (Fin S.rank) ℂ) :
    eDir C τ (cplxO 1 (C.sB B τ) z) τ' (cplxO 1 (C.sB B τ') z') = eDir C τ z τ' z' ∧
    eDir C τ (cplxO 1 (C.sB B τ) z) τ' z' = -eDir C τ z τ' (cplxO 1 (C.sB B τ') z') := by
  obtain ⟨-, hmem, -, hz, -⟩ := (GlobalTheory.T.thetaKernel_orthonormalFrame_inDomain_periodLinear D S T C).2 B hB
  have hE := (zR_laws D.host.E T.rank C.X C.g C.q0 C.hr C.bas C.idx S.rank C.sympl C.even (C.xB B) hmem).2.1
  simp only [eDir]
  rw [← hE, ← hE, ← hE, ← hE, hz, hz]
  simp only [Pi.smul_apply, hx_smul_left_bas_idx, hx_smul_right_conj, Complex.conj_I]
  refine ⟨?_, ?_⟩
  · congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [← mul_assoc, neg_mul, Complex.I_mul_I, neg_neg, one_mul]
  · rw [← Finset.mul_sum, ← Finset.mul_sum]
    simp

/- English proof (translation)
Establish `L` using `HeisDeriv.dRho_laws D S T C`. Rewrite using `[(L _ (th_add C hg (th_smul C q hh)) σ a).2.2.2.1 p, (L g hg σ a).2.2.1 _ (th_smul C q hh), (L h hh σ a).2.2.2.1 q, smul_add, smul_smul]`.
-/
private theorem dRho_smul_add_smul (σ : D.what₂.Tau) (a : Matrix (Fin T.rank) (Fin S.rank) ℂ) {g h : WO S T → ℂ}
    (hg : C.IsTh g) (hh : C.IsTh h) (p q : ℂ) :
    dRho (heisO C.ψ S T) C.θ σ a (p • (g + q • h)) =
      p • dRho (heisO C.ψ S T) C.θ σ a g + (p * q) • dRho (heisO C.ψ S T) C.θ σ a h := by
  have L := HeisDeriv.dRho_laws D S T C
  rw [(L _ (th_add C hg (th_smul C q hh)) σ a).2.2.2.1 p, (L g hg σ a).2.2.1 _ (th_smul C q hh),
    (L h hh σ a).2.2.2.1 q, smul_add, smul_smul]

/- English proof (translation)
Establish `L` using `HeisDeriv.dRho_laws D S T C f hf σ'`. Rewrite using `[aPlus_eq C σ' K' a', aPlus_eq C σ K a, dRho_smul_add_smul C σ a (L a').1 (L (K' a')).1, dRho_smul_add_smul C σ (K a) (L a').1 (L (K' a')).1]`. Apply the tactic sequence `match_scalars <;> ring_nf <;> (try rw [Complex.I_sq]) <;> ring_nf`.
-/
private theorem aPlus_aPlus_lemma_7 (σ : D.what₂.Tau) (K : Matrix (Fin T.rank) (Fin S.rank) ℂ → Matrix (Fin T.rank) (Fin S.rank) ℂ)
    (a : Matrix (Fin T.rank) (Fin S.rank) ℂ) (σ' : D.what₂.Tau)
    (K' : Matrix (Fin T.rank) (Fin S.rank) ℂ → Matrix (Fin T.rank) (Fin S.rank) ℂ)
    (a' : Matrix (Fin T.rank) (Fin S.rank) ℂ) {f : WO S T → ℂ} (hf : C.IsTh f) :
    aPlus (heisO C.ψ S T) C.θ σ K a (aPlus (heisO C.ψ S T) C.θ σ' K' a' f) =
      ((fockScale D σ : ℂ)⁻¹ * (fockScale D σ' : ℂ)⁻¹) •
        (dRho (heisO C.ψ S T) C.θ σ a (dRho (heisO C.ψ S T) C.θ σ' a' f)
          + (-I) • dRho (heisO C.ψ S T) C.θ σ a (dRho (heisO C.ψ S T) C.θ σ' (K' a') f)
          + (-I) • dRho (heisO C.ψ S T) C.θ σ (K a) (dRho (heisO C.ψ S T) C.θ σ' a' f)
          - dRho (heisO C.ψ S T) C.θ σ (K a) (dRho (heisO C.ψ S T) C.θ σ' (K' a') f)) := by
  have L := HeisDeriv.dRho_laws D S T C f hf σ'
  rw [aPlus_eq C σ' K' a', aPlus_eq C σ K a, dRho_smul_add_smul C σ a (L a').1 (L (K' a')).1,
    dRho_smul_add_smul C σ (K a) (L a').1 (L (K' a')).1]
  match_scalars <;> ring_nf <;> (try rw [Complex.I_sq]) <;> ring_nf

/- English proof (translation)
Establish `L` using `HeisDeriv.dRho_laws D S T C f hf`. Take `⟨h1, h2⟩` from `eDir_cplx C τ z hB τ' z'`. Rewrite using `[aPlus_aPlus_lemma_7 C τ _ z τ' _ z' hf, aPlus_aPlus_lemma_7 C τ' _ z' τ _ z hf]`. Establish `c1 : _ = ((2 * π * I * (eDir C τ z τ' z' : ℝ) : ℂ)) • f` using `(L τ z).2.2.2.2.2.2.2 τ' z'`. Establish `c2 : _ = ((2 * π * I * (eDir C τ z τ' (cplxO 1 (C.sB B τ') z') : ℝ) : ℂ)) • f` using `(L τ z).2.2.2.2.2.2.2 τ' (cplxO 1 (C.sB B τ') z')`.

Establish `c3 : _ = ((2 * π * I * (eDir C τ (cplxO 1 (C.sB B τ) z) τ' z' : ℝ) : ℂ)) • f` using `(L τ (cplxO 1 (C.sB B τ) z)).2.2.2.2.2.2.2 τ' z'`. Establish `c4 : _ = ((2 * π * I * (eDir C τ (cplxO 1 (C.sB B τ) z) τ' (cplxO 1 (C.sB B τ') z') : ℝ) : ℂ)) • f` using `(L τ (cplxO 1 (C.sB B τ) z)).2.2.2.2.2.2.2 τ' (cplxO 1 (C.sB B τ') z')`. Rewrite `c4` using `[h1]`. Rewrite `c3` using `[h2]`. Move the coercions through the operations in `at c3`.

Take the linear combination `(norm := module) ((fockScale D τ : ℂ)⁻¹ * (fockScale D τ' : ℂ)⁻¹) • (c1 - I • c2 - I • c3 - c4)`.
-/
theorem aPlus_comm {B : C.Bas} (hB : C.IsB B) (τ' : D.what₂.Tau) (z' : Matrix (Fin T.rank) (Fin S.rank) ℂ)
    {f : WO S T → ℂ} (hf : C.IsTh f) :
    aPlus (heisO C.ψ S T) C.θ τ (cplxO 1 (C.sB B τ)) z (aPlus (heisO C.ψ S T) C.θ τ' (cplxO 1 (C.sB B τ')) z' f) =
    aPlus (heisO C.ψ S T) C.θ τ' (cplxO 1 (C.sB B τ')) z' (aPlus (heisO C.ψ S T) C.θ τ (cplxO 1 (C.sB B τ)) z f) := by
  have L := HeisDeriv.dRho_laws D S T C f hf
  obtain ⟨h1, h2⟩ := eDir_cplx C τ z hB τ' z'
  rw [aPlus_aPlus_lemma_7 C τ _ z τ' _ z' hf, aPlus_aPlus_lemma_7 C τ' _ z' τ _ z hf]
  have c1 : _ = ((2 * π * I * (eDir C τ z τ' z' : ℝ) : ℂ)) • f := (L τ z).2.2.2.2.2.2.2 τ' z'
  have c2 : _ = ((2 * π * I * (eDir C τ z τ' (cplxO 1 (C.sB B τ') z') : ℝ) : ℂ)) • f :=
    (L τ z).2.2.2.2.2.2.2 τ' (cplxO 1 (C.sB B τ') z')
  have c3 : _ = ((2 * π * I * (eDir C τ (cplxO 1 (C.sB B τ) z) τ' z' : ℝ) : ℂ)) • f :=
    (L τ (cplxO 1 (C.sB B τ) z)).2.2.2.2.2.2.2 τ' z'
  have c4 : _ = ((2 * π * I * (eDir C τ (cplxO 1 (C.sB B τ) z) τ' (cplxO 1 (C.sB B τ') z') : ℝ) : ℂ)) • f :=
    (L τ (cplxO 1 (C.sB B τ) z)).2.2.2.2.2.2.2 τ' (cplxO 1 (C.sB B τ') z')
  rw [h1] at c4
  rw [h2] at c3
  push_cast at c3
  linear_combination (norm := module)
    ((fockScale D τ : ℂ)⁻¹ * (fockScale D τ' : ℂ)⁻¹) • (c1 - I • c2 - I • c3 - c4)

/- English proof (translation)
Introduce `D S T C B hB BS f hf Q`. Establish `hA : ∀ (BS' : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) i g, C.IsTh g → C.IsTh (aPlusAll (heisO C.ψ S T) C.θ (fun τ => cplxO 1 (C.sB B τ)) BS' B i g)` using `fun BS' i g hg => aPlus_th C i.1 (cplxO 1 (C.sB B i.1)) (unitMap (BS' i.1) (B i.1) i.2.1 i.2.2) hg`. Establish `hc : ∀ (BS' : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) i j g, C.IsTh g → aPlusAll (heisO C.ψ S T) C.θ (fun τ => cplxO 1 (C.sB B τ)) BS' B i (aPlusAll (heisO C.ψ S T) C.θ (fun τ => cplxO 1 (C.sB B τ)) BS' B j g) = aPlusAll (heisO C.ψ S T) C.θ (fun τ => cplxO 1 (C.sB B τ)) …` using `fun BS' i j g hg => aPlus_comm C i.1 (unitMap (BS' i.1) (B i.1) i.2.1 i.2.2) hB j.1 (unitMap (BS' j.1) (B j.1) j.2.1 j.2.2) hg`. Establish `hadd : ∀ (BS' : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) i g g', C.IsTh g → C.IsTh g' → aPlusAll (heisO C.ψ S T) C.θ (fun τ => cplxO 1 (C.sB B τ)) BS' B i (g + g') = aPlusAll (heisO C.ψ S T) C.θ (fun τ => cplxO 1 (C.sB B τ)) BS' B i g + aPlusAll (heisO C.ψ S T) C.θ (fun …` using `fun BS' i g g' hg hg' => aPlus_add C i.1 (cplxO 1 (C.sB B i.1)) (unitMap (BS' i.1) (B i.1) i.2.1 i.2.2) hg hg'`. Establish `hsm : ∀ (BS' : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) i (a : ℂ) g, C.IsTh g → aPlusAll (heisO C.ψ S T) C.θ (fun τ => cplxO 1 (C.sB B τ)) BS' B i (a • g) = a • aPlusAll (heisO C.ψ S T) C.θ (fun τ => cplxO 1 (C.sB B τ)) BS' B i g` using `fun BS' i a g hg => aPlus_smul C i.1 (cplxO 1 (C.sB B i.1)) (unitMap (BS' i.1) (B i.1) i.2.1 i.2.2) a hg`.

Establish `hr : ∀ (BS' : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) u, IsFinPt u → ∀ i g, C.IsTh g → aPlusAll (heisO C.ψ S T) C.θ (fun τ => cplxO 1 (C.sB B τ)) BS' B i (C.rho u g) = C.rho u (aPlusAll (heisO C.ψ S T) C.θ (fun τ => cplxO 1 (C.sB B τ)) BS' B i g)` using `fun BS' u hu i g hg => aPlus_rho C i.1 (cplxO 1 (C.sB B i.1)) (unitMap (BS' i.1) (B i.1) i.2.1 i.2.2) hu hg`. Establish `tadd : ∀ g g' : WO S T → ℂ, C.IsTh g → C.IsTh g' → C.IsTh (g + g')` using `fun _ _ h h' => th_add C h h'`. Establish `tsm : ∀ (a : ℂ) (g : WO S T → ℂ), C.IsTh g → C.IsTh (a • g)` using `fun a _ h => th_smul C a h`. Use `⟨pure_mem tadd tsm (hA BS) hf Q, fun v => pure_X_mul tadd tsm (hA BS) (hc BS) (hadd BS) (hsm BS) hf Q v, pure_one f, fun f' hf' => pure_add (hA _) (hadd _) hf hf' Q, fun a => ?_, fun u hu => ?_⟩` and prove the remaining obligations. Conclude with `pure_comm (hA _) (fun g => a • g) (fun g g' => smul_add a g g') (fun b g => smul_comm a b g) (fun i g hg => hsm _ i a g hg) hf Q`.

Conclude with `pure_comm (hA _) (C.rho u) (rho_add C u) (rho_smul C u) (hr _ u hu) hf Q`.
-/
theorem fock_vec_laws : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), ∀ B, C.IsB B → ∀ BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ, ∀ f, C.IsTh f → ∀ Q : MvPolynomial (FVar D T.rank S.rank) ℂ, C.IsTh (pureTensorO C.ψ C.θ S T (fun _ => 1) (C.sB B) BS B f Q) ∧ (∀ v, pureTensorO C.ψ C.θ S T (fun _ => 1) (C.sB B) BS B f (MvPolynomial.X v * Q) = aPlusAll (heisO C.ψ S T) C.θ (fun τ => cplxO 1 (C.sB B τ)) BS B v (pureTensorO C.ψ C.θ S T (fun _ => 1) (C.sB B) BS B f Q)) ∧ pureTensorO C.ψ C.θ S T (fun _ => 1) (C.sB B) BS B f 1 = f ∧ (∀ f', C.IsTh f' → C.fvec B (f + f') Q = C.fvec B f Q + C.fvec B f' Q) ∧ (∀ a : ℂ, C.fvec B (a • f) Q = a • C.fvec B f Q) ∧ ∀ u, IsFinPt u → C.fvec B (C.rho u f) Q = C.rho u (C.fvec B f Q) := by
  intro D S T C B hB BS f hf Q
  have hA : ∀ (BS' : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) i g, C.IsTh g →
      C.IsTh (aPlusAll (heisO C.ψ S T) C.θ (fun τ => cplxO 1 (C.sB B τ)) BS' B i g) :=
    fun BS' i g hg => aPlus_th C i.1 (cplxO 1 (C.sB B i.1)) (unitMap (BS' i.1) (B i.1) i.2.1 i.2.2) hg
  have hc : ∀ (BS' : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) i j g, C.IsTh g →
      aPlusAll (heisO C.ψ S T) C.θ (fun τ => cplxO 1 (C.sB B τ)) BS' B i
        (aPlusAll (heisO C.ψ S T) C.θ (fun τ => cplxO 1 (C.sB B τ)) BS' B j g) =
      aPlusAll (heisO C.ψ S T) C.θ (fun τ => cplxO 1 (C.sB B τ)) BS' B j
        (aPlusAll (heisO C.ψ S T) C.θ (fun τ => cplxO 1 (C.sB B τ)) BS' B i g) :=
    fun BS' i j g hg => aPlus_comm C i.1 (unitMap (BS' i.1) (B i.1) i.2.1 i.2.2) hB j.1
      (unitMap (BS' j.1) (B j.1) j.2.1 j.2.2) hg
  have hadd : ∀ (BS' : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) i g g', C.IsTh g → C.IsTh g' →
      aPlusAll (heisO C.ψ S T) C.θ (fun τ => cplxO 1 (C.sB B τ)) BS' B i (g + g') =
      aPlusAll (heisO C.ψ S T) C.θ (fun τ => cplxO 1 (C.sB B τ)) BS' B i g +
        aPlusAll (heisO C.ψ S T) C.θ (fun τ => cplxO 1 (C.sB B τ)) BS' B i g' :=
    fun BS' i g g' hg hg' => aPlus_add C i.1 (cplxO 1 (C.sB B i.1)) (unitMap (BS' i.1) (B i.1) i.2.1 i.2.2) hg hg'
  have hsm : ∀ (BS' : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) i (a : ℂ) g, C.IsTh g →
      aPlusAll (heisO C.ψ S T) C.θ (fun τ => cplxO 1 (C.sB B τ)) BS' B i (a • g) =
      a • aPlusAll (heisO C.ψ S T) C.θ (fun τ => cplxO 1 (C.sB B τ)) BS' B i g :=
    fun BS' i a g hg => aPlus_smul C i.1 (cplxO 1 (C.sB B i.1)) (unitMap (BS' i.1) (B i.1) i.2.1 i.2.2) a hg
  have hr : ∀ (BS' : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) u, IsFinPt u → ∀ i g, C.IsTh g →
      aPlusAll (heisO C.ψ S T) C.θ (fun τ => cplxO 1 (C.sB B τ)) BS' B i (C.rho u g) =
      C.rho u (aPlusAll (heisO C.ψ S T) C.θ (fun τ => cplxO 1 (C.sB B τ)) BS' B i g) :=
    fun BS' u hu i g hg => aPlus_rho C i.1 (cplxO 1 (C.sB B i.1)) (unitMap (BS' i.1) (B i.1) i.2.1 i.2.2) hu hg
  have tadd : ∀ g g' : WO S T → ℂ, C.IsTh g → C.IsTh g' → C.IsTh (g + g') := fun _ _ h h' => th_add C h h'
  have tsm : ∀ (a : ℂ) (g : WO S T → ℂ), C.IsTh g → C.IsTh (a • g) := fun a _ h => th_smul C a h
  refine ⟨pure_mem tadd tsm (hA BS) hf Q, fun v => pure_X_mul tadd tsm (hA BS) (hc BS) (hadd BS) (hsm BS) hf Q v,
    pure_one f, fun f' hf' => pure_add (hA _) (hadd _) hf hf' Q, fun a => ?_, fun u hu => ?_⟩
  · exact pure_comm (hA _) (fun g => a • g) (fun g g' => smul_add a g g') (fun b g => smul_comm a b g)
      (fun i g hg => hsm _ i a g hg) hf Q
  · exact pure_comm (hA _) (C.rho u) (rho_add C u) (rho_smul C u) (hr _ u hu) hf Q

end GlobalTheory.Ker.FockAlg
