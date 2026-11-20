import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BottomTriangleRationalCoefficients
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BottomTriangleRationalCoefficientsStatement

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
open Formalism.IndefR.Datum GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting
open scoped ComplexOrder
noncomputable section
namespace GlobalTheory.RealRatAct
variable {σ : Type}
end GlobalTheory.RealRatAct
namespace GlobalTheory.RealRatAct
open Formalism.L2.Theta
variable {D : D7}
end GlobalTheory.RealRatAct
namespace GlobalTheory.RealRatAct
open Formalism.L2.Theta
variable {D : D7}
end GlobalTheory.RealRatAct
namespace GlobalTheory.RealRatAct
open Formalism.L2.Theta
variable {D : D7}
section Act
variable {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
  {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}
variable (hW : IsWeilDatumO ψ S T χS χT om) (hθ : IsInfFam θ) (hgS : ∀ τ, gramAt D S τ = -1)
  (hgT : ∀ τ, gramAt D T τ = 1) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
  (hv : ∀ ρ, IsFockVacAt (heisO ψ S T) θ ρ (cplxO (-1) 1) f) {K : IntermediateField ℚ ℂ}
  (hK : ∀ z ∈ K, starRingEnd ℂ z ∈ K)
include hW hθ hgS hgT hf hv
end Act
end GlobalTheory.RealRatAct
namespace GlobalTheory.RealRatAct
open Formalism.L2.Theta
variable {D : D7}
section Act
variable {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
  {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}
  (hW : IsWeilDatumO ψ S T χS χT om) (hθ : IsInfFam θ) (hgS : ∀ τ, gramAt D S τ = -1)
  (hgT : ∀ τ, gramAt D T τ = 1) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
  (hv : ∀ ρ, IsFockVacAt (heisO ψ S T) θ ρ (cplxO (-1) 1) f) {K : IntermediateField ℚ ℂ}
  (hK : ∀ z ∈ K, starRingEnd ℂ z ∈ K)
include hW hθ hgS hgT hf hv hK
end Act
end GlobalTheory.RealRatAct
namespace GlobalTheory.RealRatAct
open Formalism.L2.Theta
/- English proof (translation)
Introduce `D T _ L μ₀ sc G W i j A A' WW X _ _ _ hX`. Use `⟨galFld D.host.E, galFld_fin _, fun t γ hγ r hr hγr x k => ?_⟩` and prove the remaining obligations. Establish `h` using `hX.is`. Establish `hθ : IsInfFam W.θ` using `h.isVac.2.inf`. Establish `hWd` using `h.weil t`.

Establish `hgS : ∀ τ, gramAt D (GlobalTheory.Grid.neg A) τ = -1` using `fun τ => by`. Rewrite using `[gramAt, GlobalTheory.Grid.neg_gram, hX.std.1]`. Use extensionality with `a b`. Simplify using `only [Matrix.map_apply, Matrix.neg_apply, Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> simp`.

Establish `hgT : ∀ τ, gramAt D WW τ = 1` using `fun τ => by`. Rewrite using `[gramAt, hX.stdW.1]`. Simplify using the standard rewrite rules. Establish `hf` using `(GlobalTheory.ConstRatio.theta_f h t).1`. Establish `ho` using `GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum (h.idem t)`.

Establish `hv : ∀ ρ, IsFockVacAt (heisO W.ψ (GlobalTheory.Grid.neg A) WW) W.θ ρ (cplxO (-1) 1) (X.f t)` using `fun ρ => by`. Use `GlobalTheory.DatumFock.isFockVacAt_of_isThetaAt h.isVac.1.1.1 hθ ho.infPart_eq ho.conj.infPart_eq (h.fst t) h.isVac.2.theta hf (h.isVac.2.fock ρ)` as an intermediate fact. Simplify `this` using `[(hX.std.2.2 ρ).1, (hX.stdW.2.2 ρ).1]`. Take `⟨c, hc, Q, hQ, hact⟩` from `act_fin hWd hθ hgS hgT hf hv (fun z hz => conj_mem_galFld hz) Finset.univ r hr (fun ρ hρ => absurd (Finset.mem_univ ρ) hρ) (compAt_mem W.θ hθ hγ hγr) _ (monomial_mem _ k)`. Establish `hPT : ∀ P, pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) P = PT W.ψ W.θ (GlobalTheory.Grid.neg A) WW (X.f t) P` using `fun P => by`.

Establish `e1 : (fun τ => -X.rA.s τ) = fun _ => (-1 : Matrix (Fin A.rank) (Fin A.rank) ℂ)`. Use function extensionality and compare the values at `fun τ => by rw [(hX.std.2.2 τ).1]`. Establish `e2 : X.rW.s = fun _ => 1` using `funext fun τ => (hX.stdW.2.2 τ).1`. Establish `e3 : X.rA.B = fun _ => 1` using `funext fun τ => (hX.std.2.2 τ).2`. Establish `e4 : X.rW.B = fun _ => 1` using `funext fun τ => (hX.stdW.2.2 τ).2`.

Rewrite using `[e1, e2, e3, e4]`. Establish `e1r : (X.ω t) (1, r) = ((X.ω t).toSgn true) (1, r)` using `by show _ = (X.ω t) ((GlobalTheory.Grid.ofSgn true A).toMonoidHom 1, r)`. Rewrite using `[map_one]`. Establish `hQs : Q = ∑ k' ∈ Q.support, Q.coeff k' • MvPolynomial.monomial k' (1 : ℂ)`. Establish `h1` using `MvPolynomial.as_sum Q`.

Establish `h2 : ∑ v ∈ Q.support, MvPolynomial.monomial v (MvPolynomial.coeff v Q) = ∑ k' ∈ Q.support, Q.coeff k' • MvPolynomial.monomial k' (1 : ℂ)` using `Finset.sum_congr rfl fun k' _ => by rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]`. Conclude with `h1.trans h2`. Establish `hker : ∀ g, X.ker W.ψ W.θ t (MvPolynomial.monomial k 1) (x * r) g = ∑ k' ∈ Q.support, (c * Q.coeff k') * X.ker W.ψ W.θ t (MvPolynomial.monomial k' 1) x g`. Introduce `g`. Unfold `Tri.ker thetaKO`.

Establish `e : (X.ω t) (g, x * r) = (X.ω t) (g, x) * (X.ω t) (1, r)`. Rewrite using `[← map_mul, Prod.mk_mul_mk, mul_one]`. Simplify using `only [hPT]`. Rewrite using `[e, Module.End.mul_apply, e1r, hact]`. Use `conv_lhs => rw [hQs]`.

Rewrite using `[map_sum, Finset.smul_sum, map_sum, Finset.sum_apply]`. Use `Finset.sum_congr rfl fun k' _ => ?_` and prove the remaining obligations. Simplify using `only [map_smul, Pi.smul_apply, smul_eq_mul, mul_assoc]`. Establish `hint` using `(hX.integrable t).1`. Set `cc : (FVar D WW.rank A.rank →₀ ℕ) →₀ ℂ` to `Finsupp.onFinset Q.support (fun k' => c * Q.coeff k') fun k' hk' => by`.

Assume the negation of the conclusion as `hn`. Conclude with `hk' (by rw [MvPolynomial.notMem_support_iff.1 hn, mul_zero])`. Establish `hcc : ∀ k', cc k' = c * Q.coeff k'` using `fun k' => Finsupp.onFinset_apply`. Establish `hsub : cc.support ⊆ Q.support` using `Finsupp.support_onFinset_subset`. Use `⟨cc, fun k' => ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[hcc]`. Conclude with `(galFld D.host.E).mul_mem hc (coeff_mem hQ k')`. Unfold `Tri.I`. Repeatedly rewrite using `[hker]`. Rewrite using `[integral_finsetSum _ fun k' _ => (hint _ x).const_mul _]`.

Rewrite using `[← Finset.sum_subset hsub fun k' _ hk' => by`. Rewrite using `[← hcc, Finsupp.notMem_support_iff.1 hk']`. Use the proof step `simp]`. Use `Finset.sum_congr rfl fun k' _ => ?_` and prove the remaining obligations. Rewrite using `[integral_const_mul, hcc]`.
-/
theorem rationalAction_real_translate : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X →
    ∃ M₁ : IntermediateField ℚ ℂ, FiniteDimensional ℚ M₁ ∧ ∀ t, ∀ γ ∈ GQ WW, ∀ r ∈ GinfC WW, γ * r ∈ GfC WW → ∀ x k,
      ∃ c : (FVar D WW.rank A.rank →₀ ℕ) →₀ ℂ, (∀ k', c k' ∈ M₁) ∧
        X.I W.ψ W.θ t (MvPolynomial.monomial k 1) (x * r) = ∑ k' ∈ c.support, c k' * X.I W.ψ W.θ t (MvPolynomial.monomial k' 1) x := by
  intro D T _ L μ₀ sc G W i j A A' WW X _ _ _ hX
  refine ⟨galFld D.host.E, galFld_fin _, fun t γ hγ r hr hγr x k => ?_⟩
  have h := hX.is
  have hθ : IsInfFam W.θ := h.isVac.2.inf
  have hWd := h.weil t
  have hgS : ∀ τ, gramAt D (GlobalTheory.Grid.neg A) τ = -1 := fun τ => by
    rw [gramAt, GlobalTheory.Grid.neg_gram, hX.std.1]
    ext a b
    simp only [Matrix.map_apply, Matrix.neg_apply, Matrix.one_apply]
    split_ifs <;> simp
  have hgT : ∀ τ, gramAt D WW τ = 1 := fun τ => by
    rw [gramAt, hX.stdW.1]; simp
  have hf := (GlobalTheory.ConstRatio.theta_f h t).1
  have ho := GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum (h.idem t)
  have hv : ∀ ρ, IsFockVacAt (heisO W.ψ (GlobalTheory.Grid.neg A) WW) W.θ ρ (cplxO (-1) 1) (X.f t) := fun ρ => by
    have := GlobalTheory.DatumFock.isFockVacAt_of_isThetaAt h.isVac.1.1.1 hθ ho.infPart_eq ho.conj.infPart_eq (h.fst t)
      h.isVac.2.theta hf (h.isVac.2.fock ρ)
    simpa [(hX.std.2.2 ρ).1, (hX.stdW.2.2 ρ).1] using this
  obtain ⟨c, hc, Q, hQ, hact⟩ := act_fin hWd hθ hgS hgT hf hv (fun z hz => conj_mem_galFld hz) Finset.univ r hr
    (fun ρ hρ => absurd (Finset.mem_univ ρ) hρ) (compAt_mem W.θ hθ hγ hγr) _ (monomial_mem _ k)
  have hPT : ∀ P, pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) P =
      PT W.ψ W.θ (GlobalTheory.Grid.neg A) WW (X.f t) P := fun P => by
    have e1 : (fun τ => -X.rA.s τ) = fun _ => (-1 : Matrix (Fin A.rank) (Fin A.rank) ℂ) :=
      funext fun τ => by rw [(hX.std.2.2 τ).1]
    have e2 : X.rW.s = fun _ => 1 := funext fun τ => (hX.stdW.2.2 τ).1
    have e3 : X.rA.B = fun _ => 1 := funext fun τ => (hX.std.2.2 τ).2
    have e4 : X.rW.B = fun _ => 1 := funext fun τ => (hX.stdW.2.2 τ).2
    rw [e1, e2, e3, e4]
  have e1r : (X.ω t) (1, r) = ((X.ω t).toSgn true) (1, r) := by
    show _ = (X.ω t) ((GlobalTheory.Grid.ofSgn true A).toMonoidHom 1, r)
    rw [map_one]
  have hQs : Q = ∑ k' ∈ Q.support, Q.coeff k' • MvPolynomial.monomial k' (1 : ℂ) := by
    have h1 := MvPolynomial.as_sum Q
    have h2 : ∑ v ∈ Q.support, MvPolynomial.monomial v (MvPolynomial.coeff v Q) =
        ∑ k' ∈ Q.support, Q.coeff k' • MvPolynomial.monomial k' (1 : ℂ) :=
      Finset.sum_congr rfl fun k' _ => by rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
    exact h1.trans h2
  have hker : ∀ g, X.ker W.ψ W.θ t (MvPolynomial.monomial k 1) (x * r) g =
      ∑ k' ∈ Q.support, (c * Q.coeff k') * X.ker W.ψ W.θ t (MvPolynomial.monomial k' 1) x g := by
    intro g
    unfold Tri.ker thetaKO
    have e : (X.ω t) (g, x * r) = (X.ω t) (g, x) * (X.ω t) (1, r) := by
      rw [← map_mul, Prod.mk_mul_mk, mul_one]
    simp only [hPT]
    rw [e, Module.End.mul_apply, e1r, hact]
    conv_lhs => rw [hQs]
    rw [map_sum, Finset.smul_sum, map_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun k' _ => ?_
    simp only [map_smul, Pi.smul_apply, smul_eq_mul, mul_assoc]
  have hint := (hX.integrable t).1
  classical
  let cc : (FVar D WW.rank A.rank →₀ ℕ) →₀ ℂ :=
    Finsupp.onFinset Q.support (fun k' => c * Q.coeff k') fun k' hk' => by
      by_contra hn
      exact hk' (by rw [MvPolynomial.notMem_support_iff.1 hn, mul_zero])
  have hcc : ∀ k', cc k' = c * Q.coeff k' := fun k' => Finsupp.onFinset_apply
  have hsub : cc.support ⊆ Q.support := Finsupp.support_onFinset_subset
  refine ⟨cc, fun k' => ?_, ?_⟩
  · rw [hcc]
    exact (galFld D.host.E).mul_mem hc (coeff_mem hQ k')
  · unfold Tri.I
    simp_rw [hker]
    rw [integral_finsetSum _ fun k' _ => (hint _ x).const_mul _]
    rw [← Finset.sum_subset hsub fun k' _ hk' => by
      rw [← hcc, Finsupp.notMem_support_iff.1 hk']; simp]
    refine Finset.sum_congr rfl fun k' _ => ?_
    rw [integral_const_mul, hcc]
end GlobalTheory.RealRatAct
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @_root_.GlobalTheory.RealRatAct.rationalAction_real_translate | exact _root_.GlobalTheory.RealRatAct.rationalAction_real_translate | (intros; apply _root_.GlobalTheory.RealRatAct.rationalAction_real_translate <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.realTranslate_preserves_rationalAction : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X →
    ∃ M₁ : IntermediateField ℚ ℂ, FiniteDimensional ℚ M₁ ∧ ∀ t, ∀ γ ∈ GQ WW, ∀ r ∈ GinfC WW, γ * r ∈ GfC WW → ∀ x k,
      ∃ c : (FVar D WW.rank A.rank →₀ ℕ) →₀ ℂ, (∀ k', c k' ∈ M₁) ∧
        X.I W.ψ W.θ t (MvPolynomial.monomial k 1) (x * r) = ∑ k' ∈ c.support, c k' * X.I W.ψ W.θ t (MvPolynomial.monomial k' 1) x := by
  first | exact @_root_.GlobalTheory.RealRatAct.rationalAction_real_translate | exact _root_.GlobalTheory.RealRatAct.rationalAction_real_translate | (intros; apply _root_.GlobalTheory.RealRatAct.rationalAction_real_translate <;> assumption)
end
