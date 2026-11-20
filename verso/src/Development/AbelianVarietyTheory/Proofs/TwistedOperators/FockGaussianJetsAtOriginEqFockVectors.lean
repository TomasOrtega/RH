import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LamF
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FoldrHolDEqIteratedFDeriv
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockGaussianReadingDifferentiableStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockCreationOperatorMultiplierAntilinearStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockCreationOperatorReadingStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PureTensorOZeroEqJetP
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VacuumFockOfThetaSquareIntegrable
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FockTransl
open Formalism.L2.Ker (VCx DVar derivAt0)

noncomputable section

namespace GlobalTheory.FockTransl.Jet

open Complex

variable {D : D7}

/- English proof (translation)
Rewrite using `[Multiset.prod_map_toList]`. Proceed by induction on `m using Finsupp.induction with`. Consider the case `zero => simp`. Consider the case `single_add a n g' ha hn ih`. Rewrite using `[map_add, Multiset.map_add, Multiset.prod_add, ih, Finsupp.toMultiset_single, Finsupp.prod_add_index']`.

Simplify using `[Multiset.map_nsmul, Multiset.prod_nsmul]`. Simplify using the standard rewrite rules. Introduce `a b c`. Rewrite using `[pow_add]`.
-/
theorem list_prod_toMultiset {ι : Type} (m : ι →₀ ℕ) (g : ι → ℂ) :
    ((Finsupp.toMultiset m).toList.map g).prod = m.prod fun l n => g l ^ n := by
  rw [Multiset.prod_map_toList]
  induction m using Finsupp.induction with
  | zero => simp
  | single_add a n g' ha hn ih =>
    rw [map_add, Multiset.map_add, Multiset.prod_add, ih, Finsupp.toMultiset_single, Finsupp.prod_add_index']
    · simp [Multiset.map_nsmul, Multiset.prod_nsmul]
    · simp
    · intro a b c; rw [pow_add]

/- English proof (translation)
Unfold `crOp`. Rewrite using `[fderiv_const_mul hΦ]`. Simplify using `only [ContinuousLinearMap.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem crOp_const_mul {S T : HSp D} (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (l : DVar D.what₂.Tau S.rank T.rank)
    (c : ℂ) (Φ : VCx D.what₂.Tau S.rank T.rank → ℂ) (z : VCx D.what₂.Tau S.rank T.rank) (hΦ : DifferentiableAt ℝ Φ z) :
    crOp A B l (fun z => c * Φ z) z = c * crOp A B l Φ z := by
  unfold crOp
  rw [fderiv_const_mul hΦ]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

/- English proof (translation)
Introduce `D ψ θ σ hψ hσ S T A B`. Establish `L1 : ∀ (D : D7) (S T : HSp D) (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (l : DVar D.what₂.Tau S.rank T.rank), (∀ a b, GlobalTheory.FockTransl.Jet.lamF A B l (a + b) = GlobalTheory.FockTransl.Jet.lamF A B l a + GlobalTheory.FockTransl.Jet.lamF A B l b) ∧ ∀ (t …` using `GlobalTheory.T.fockCreationOperatorMultiplier_antilinear`. Establish `L2 : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (σ : (D.what₂.Tau → ℂ) →+ AE D), IsStdChar D ψ (-1) → GlobalTheory.FockCompare.Chart θ σ → ∀ (S T : HSp D) (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (h : WO S T → ℂ) (x : WO S T) (l : FVar D T.rank …` using `GlobalTheory.T.fock_creation_operator_reading`. Use `⟨fun m => m.prod fun l n => ((fockScale D l.1 : ℂ) / 2) ^ n, fun f hf x m => ?_⟩` and prove the remaining obligations. Use `set Aop := aPlusAll (heisO ψ S T) θ (fun τ => cplxO (A.cart τ) (B.cart τ)) A.onb B.onb with hAop`.

Establish `hent : Differentiable ℂ (rd ψ σ A B f x)` using `GlobalTheory.T.fockGaussianReading_differentiable D ψ θ σ hψ hσ S T A B f hf x`. Establish `hops` using `GlobalTheory.Ker.CreOp.foldr_creation_zero _ _ Formalism.L2.Ker.coordX (GlobalTheory.FockTransl.Jet.lamF A B) (rd ψ σ A B f x) (fun l => L1 D S T A B l) hent (GlobalTheory.FockTransl.Jet.crOp A B) (fun _ _ _ => rfl)`. Establish `key : ∀ L : List (FVar D T.rank S.rank), rd ψ σ A B (L.foldr (fun i g => Aop i g) f) x = fun z => (L.map fun l => 2 / (fockScale D l.1 : ℂ)).prod * L.foldr (GlobalTheory.FockTransl.Jet.crOp A B) (rd ψ σ A B f x) z`. Introduce `L`. Proceed by induction on `L with`.

Consider the case `nil => funext z`. Simplify using the standard rewrite rules. Consider the case `cons l L ih`. Use function extensionality and compare the values at `z`. Establish `hd0 : Differentiable ℝ (L.foldr (GlobalTheory.FockTransl.Jet.crOp A B) (rd ψ σ A B f x))` using `(hops L).1.differentiable (by simp)`.

Establish `hd : DifferentiableAt ℝ (rd ψ σ A B (L.foldr (fun i g => Aop i g) f) x) z`. Rewrite using `[ih]`. Conclude with `((hd0.const_mul _) z)`. Rewrite using `[List.foldr_cons, L2 D ψ θ σ hψ hσ S T A B _ x l z hd, ih, GlobalTheory.FockTransl.Jet.crOp_const_mul A B l _ _ z (hd0 z), List.foldr_cons, List.map_cons, List.prod_cons]`. Expand and normalize the polynomial expressions, which then agree.

Establish `h0 : ∀ h : WO S T → ℂ, rd ψ σ A B h x 0 = h x`. Introduce `h`. Establish `hz : fockPt σ A B (0 : VCx D.what₂.Tau S.rank T.rank) = 0`. Establish `e : (fun τ => fockMat A B τ ((0 : VCx D.what₂.Tau S.rank T.rank) τ)) = 0`. Use function extensionality and compare the values at `τ`.

Simplify using `[fockMat]`. Rewrite using `[fockPt, e]`. Conclude with `(FockCompare.iotaW σ T S).map_zero`. Simplify using `[rd, gq, hz, GlobalTheory.OrientedHeis.heisO_zero]`. Establish `hfs : ∀ l : FVar D T.rank S.rank, (fockScale D l.1 : ℂ) ≠ 0` using `fun l => GlobalTheory.VacuumFockLaws.fockScale_ne l.1`.

Establish `hval : opPow Aop m f x = (m.prod fun l n => (2 / (fockScale D l.1 : ℂ)) ^ n) * derivAt0 (rd ψ σ A B f x) m`. Rewrite using `[opPow, ← h0 (List.foldr _ f _), key]`. Use `beta_reduce`. Rewrite using `[(hops _).2, derivAt0, GlobalTheory.AdForm.JetRead.iter_cast _ _ _ (Multiset.length_toList _) Formalism.L2.Ker.coordX, list_prod_toMultiset]`. Establish `hpt : GlobalTheory.ChainFr.ptF ψ θ A B f (MvPolynomial.monomial m 1) x = opPow Aop m f x`.

Establish `e : MvPolynomial.basisMonomials (FVar D T.rank S.rank) ℂ m = MvPolynomial.monomial m 1`. Rewrite using `[MvPolynomial.coe_basisMonomials]`. Rewrite using `[GlobalTheory.ChainFr.ptF, pureTensorO, pureTensorL, ← e, Module.Basis.constr_basis]`. Rewrite using `[hpt, hval, ← mul_assoc, ← Finsupp.prod_mul]`. Establish `e1 : (m.prod fun l n => ((fockScale D l.1 : ℂ) / 2) ^ n * (2 / (fockScale D l.1 : ℂ)) ^ n) = 1`.

Use `Finset.prod_eq_one fun l _ => ?_` and prove the remaining obligations. Use `beta_reduce`. Rewrite using `[← mul_pow, div_mul_div_comm, mul_comm (fockScale D l.1 : ℂ) 2, div_self (mul_ne_zero two_ne_zero (hfs l)), one_pow]`. Rewrite using `[e1, one_mul]`.
-/
theorem jet_eq_fock : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (σ : (D.what₂.Tau → ℂ) →+ AE D), IsStdChar D ψ (-1) → GlobalTheory.FockCompare.Chart θ σ → ∀ (S T : HSp D) (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T), ∃ C : (FVar D T.rank S.rank →₀ ℕ) → ℂ, ∀ f : WO S T → ℂ, GlobalTheory.ChainFr.IsVacF ψ θ A B f → ∀ (x : WO S T) (m : FVar D T.rank S.rank →₀ ℕ), derivAt0 (rd ψ σ A B f x) m = C m * GlobalTheory.ChainFr.ptF ψ θ A B f (MvPolynomial.monomial m 1) x := by
  intro D ψ θ σ hψ hσ S T A B
  have L1 : ∀ (D : D7) (S T : HSp D) (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (l : DVar D.what₂.Tau S.rank T.rank), (∀ a b, GlobalTheory.FockTransl.Jet.lamF A B l (a + b) = GlobalTheory.FockTransl.Jet.lamF A B l a + GlobalTheory.FockTransl.Jet.lamF A B l b) ∧ ∀ (t : ℂ) a, GlobalTheory.FockTransl.Jet.lamF A B l (t • a) = conj t * GlobalTheory.FockTransl.Jet.lamF A B l a := GlobalTheory.T.fockCreationOperatorMultiplier_antilinear
  have L2 : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (σ : (D.what₂.Tau → ℂ) →+ AE D), IsStdChar D ψ (-1) → GlobalTheory.FockCompare.Chart θ σ → ∀ (S T : HSp D) (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (h : WO S T → ℂ) (x : WO S T) (l : FVar D T.rank S.rank) (z : VCx D.what₂.Tau S.rank T.rank), DifferentiableAt ℝ (rd ψ σ A B h x) z → rd ψ σ A B (aPlusAll (heisO ψ S T) θ (fun τ => cplxO (A.cart τ) (B.cart τ)) A.onb B.onb l h) x z = (2 / (fockScale D l.1 : ℂ)) * GlobalTheory.FockTransl.Jet.crOp A B l (rd ψ σ A B h x) z := GlobalTheory.T.fock_creation_operator_reading
  refine ⟨fun m => m.prod fun l n => ((fockScale D l.1 : ℂ) / 2) ^ n, fun f hf x m => ?_⟩
  set Aop := aPlusAll (heisO ψ S T) θ (fun τ => cplxO (A.cart τ) (B.cart τ)) A.onb B.onb with hAop
  have hent : Differentiable ℂ (rd ψ σ A B f x) := GlobalTheory.T.fockGaussianReading_differentiable D ψ θ σ hψ hσ S T A B f hf x
  have hops := GlobalTheory.Ker.CreOp.foldr_creation_zero _ _ Formalism.L2.Ker.coordX (GlobalTheory.FockTransl.Jet.lamF A B) (rd ψ σ A B f x)
    (fun l => L1 D S T A B l) hent (GlobalTheory.FockTransl.Jet.crOp A B) (fun _ _ _ => rfl)
  have key : ∀ L : List (FVar D T.rank S.rank), rd ψ σ A B (L.foldr (fun i g => Aop i g) f) x =
      fun z => (L.map fun l => 2 / (fockScale D l.1 : ℂ)).prod * L.foldr (GlobalTheory.FockTransl.Jet.crOp A B) (rd ψ σ A B f x) z := by
    intro L
    induction L with
    | nil => funext z; simp
    | cons l L ih =>
      funext z
      have hd0 : Differentiable ℝ (L.foldr (GlobalTheory.FockTransl.Jet.crOp A B) (rd ψ σ A B f x)) :=
        (hops L).1.differentiable (by simp)
      have hd : DifferentiableAt ℝ (rd ψ σ A B (L.foldr (fun i g => Aop i g) f) x) z := by
        rw [ih]; exact ((hd0.const_mul _) z)
      rw [List.foldr_cons, L2 D ψ θ σ hψ hσ S T A B _ x l z hd, ih, GlobalTheory.FockTransl.Jet.crOp_const_mul A B l _ _ z (hd0 z),
        List.foldr_cons, List.map_cons, List.prod_cons]
      ring
  have h0 : ∀ h : WO S T → ℂ, rd ψ σ A B h x 0 = h x := by
    intro h
    have hz : fockPt σ A B (0 : VCx D.what₂.Tau S.rank T.rank) = 0 := by
      have e : (fun τ => fockMat A B τ ((0 : VCx D.what₂.Tau S.rank T.rank) τ)) = 0 := by
        funext τ; simp [fockMat]
      rw [fockPt, e]; exact (FockCompare.iotaW σ T S).map_zero
    simp [rd, gq, hz, GlobalTheory.OrientedHeis.heisO_zero]
  have hfs : ∀ l : FVar D T.rank S.rank, (fockScale D l.1 : ℂ) ≠ 0 := fun l => GlobalTheory.VacuumFockLaws.fockScale_ne l.1
  have hval : opPow Aop m f x = (m.prod fun l n => (2 / (fockScale D l.1 : ℂ)) ^ n) * derivAt0 (rd ψ σ A B f x) m := by
    rw [opPow, ← h0 (List.foldr _ f _), key]
    beta_reduce
    rw [(hops _).2, derivAt0, GlobalTheory.AdForm.JetRead.iter_cast _ _ _ (Multiset.length_toList _) Formalism.L2.Ker.coordX,
      list_prod_toMultiset]
  have hpt : GlobalTheory.ChainFr.ptF ψ θ A B f (MvPolynomial.monomial m 1) x = opPow Aop m f x := by
    have e : MvPolynomial.basisMonomials (FVar D T.rank S.rank) ℂ m = MvPolynomial.monomial m 1 := by
      rw [MvPolynomial.coe_basisMonomials]
    rw [GlobalTheory.ChainFr.ptF, pureTensorO, pureTensorL, ← e, Module.Basis.constr_basis]
  rw [hpt, hval, ← mul_assoc, ← Finsupp.prod_mul]
  have e1 : (m.prod fun l n => ((fockScale D l.1 : ℂ) / 2) ^ n * (2 / (fockScale D l.1 : ℂ)) ^ n) = 1 := by
    refine Finset.prod_eq_one fun l _ => ?_
    beta_reduce
    rw [← mul_pow, div_mul_div_comm, mul_comm (fockScale D l.1 : ℂ) 2, div_self (mul_ne_zero two_ne_zero (hfs l)), one_pow]
  rw [e1, one_mul]

end GlobalTheory.FockTransl.Jet

end
