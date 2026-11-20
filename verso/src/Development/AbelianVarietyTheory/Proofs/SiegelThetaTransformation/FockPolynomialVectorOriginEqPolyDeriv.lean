import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.L2NormFundamentalDomain
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.ColTorusA
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RealPointsClassicalModelRealVectorSpace
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaKernelOrthonormalFrameInDomainPeriodLinearStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FoldrHolDEqIteratedFDeriv
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AnnihilationCreationPeriodCoordinatesStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Ker.FockOrigin

/- English proof (translation)
Proceed by induction on `L with`. Consider the case `nil => simp`. Consider the case `cons a L ih`. Rewrite using `[List.map_cons, List.prod_cons, ih, List.map_cons, List.prod_cons, List.map_cons, ← Multiset.cons_coe, ← Multiset.singleton_add, map_add, Multiset.toFinsupp_singleton, MvPolynomial.X, MvPolynomial.C_mul', smul_mul_smul_comm, MvPolynomial.monomial_mul, one_mul]`.
-/
theorem prod_C_mul_X {σ σ' : Type} [DecidableEq σ'] (c : σ → ℂ) (f : σ → σ') (L : List σ) :
    (L.map fun v => MvPolynomial.C (c v) * MvPolynomial.X (f v)).prod =
      (L.map c).prod • MvPolynomial.monomial (Multiset.toFinsupp ((L.map f : List σ') : Multiset σ')) (1 : ℂ) := by
  induction L with
  | nil => simp
  | cons a L ih =>
    rw [List.map_cons, List.prod_cons, ih, List.map_cons, List.prod_cons, List.map_cons,
      ← Multiset.cons_coe, ← Multiset.singleton_add, map_add, Multiset.toFinsupp_singleton,
      MvPolynomial.X, MvPolynomial.C_mul', smul_mul_smul_comm, MvPolynomial.monomial_mul, one_mul]

/- English proof (translation)
Establish `h1` using `prod_C_mul_X (fun _ : σ => (1 : ℂ)) id (Finsupp.toMultiset m).toList`. Simplify using `only [map_one, one_mul, id, List.map_id, List.map_const', List.prod_replicate, one_pow, one_smul, Multiset.coe_toList, Finsupp.toMultiset_toFinsupp] at h1`. Rewrite using `[← h1, map_list_prod, List.map_map]`. Establish `h2 : (⇑(MvPolynomial.aeval (fun v => MvPolynomial.C (c v) * MvPolynomial.X (f v)) : MvPolynomial σ ℂ →ₐ[ℂ] MvPolynomial σ' ℂ) ∘ fun v => MvPolynomial.X v) = fun v => MvPolynomial.C (c v) * MvPolynomial.X (f v)`. Use function extensionality and compare the values at `v`.

Simplify using the standard rewrite rules. Rewrite using `[h2, prod_C_mul_X, I2.polyDeriv_smul, I2.polyDeriv_monomial_one, I2.pdTerm_eq_itD, Multiset.toFinsupp_toMultiset]`. Use `congr 1`. Use `congrFun (I2.ct_itD_perm hθ ?_) x` and prove the remaining obligations. Establish `h3 : ((Finsupp.toMultiset m).toList.map fun v => u (f v)) = ((Finsupp.toMultiset m).toList.map f).map u` using `by rw [List.map_map]; rfl`.

Rewrite using `[h3]`. Use `List.Perm.map u ?_` and prove the remaining obligations. Rewrite using `[← Multiset.coe_eq_coe, Multiset.coe_toList]`.
-/
theorem polyDeriv_aeval_monomial {σ σ' W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]
    (c : σ → ℂ) (f : σ → σ') (u : σ' → W) {θ : W → ℂ} (hθ : ContDiff ℂ (⊤ : ℕ∞) θ) (m : σ →₀ ℕ) (x : W) :
    polyDeriv (MvPolynomial.aeval (fun v => MvPolynomial.C (c v) * MvPolynomial.X (f v))
      (MvPolynomial.monomial m (1 : ℂ))) u θ x =
      ((Finsupp.toMultiset m).toList.map c).prod *
        I2.itD θ ((Finsupp.toMultiset m).toList.map fun v => u (f v)) x := by
  have h1 := prod_C_mul_X (fun _ : σ => (1 : ℂ)) id (Finsupp.toMultiset m).toList
  simp only [map_one, one_mul, id, List.map_id, List.map_const',
    List.prod_replicate, one_pow, one_smul, Multiset.coe_toList, Finsupp.toMultiset_toFinsupp] at h1
  rw [← h1, map_list_prod, List.map_map]
  have h2 : (⇑(MvPolynomial.aeval (fun v => MvPolynomial.C (c v) * MvPolynomial.X (f v)) :
      MvPolynomial σ ℂ →ₐ[ℂ] MvPolynomial σ' ℂ) ∘ fun v => MvPolynomial.X v) =
      fun v => MvPolynomial.C (c v) * MvPolynomial.X (f v) := by
    funext v; simp
  rw [h2, prod_C_mul_X, I2.polyDeriv_smul, I2.polyDeriv_monomial_one, I2.pdTerm_eq_itD,
    Multiset.toFinsupp_toMultiset]
  congr 1
  refine congrFun (I2.ct_itD_perm hθ ?_) x
  have h3 : ((Finsupp.toMultiset m).toList.map fun v => u (f v)) =
      ((Finsupp.toMultiset m).toList.map f).map u := by rw [List.map_map]; rfl
  rw [h3]
  refine List.Perm.map u ?_
  rw [← Multiset.coe_eq_coe, Multiset.coe_toList]

/- English proof (translation)
Introduce `D S T C B hB G θ hθ hG Q`. Take `⟨R, -, -, hadd, -⟩` from `GlobalTheory.KerReal.real_points D S T C`. Take `⟨-, -, -, -, hdir, -⟩` from `(GlobalTheory.T.thetaKernel_orthonormalFrame_inDomain_periodLinear D S T C).2 B hB`. Use `set x := C.xB B with hx0`. Set `f : FVar D T.rank S.rank → Harm.Var C.X.Ψ C.q0 C.X.p0 (Fin S.rank)` to `fun v => (C.m.e v.1, (rowIdx C.hr).symm v.2.1, v.2.2)`.

Set `c : FVar D T.rank S.rank → ℂ` to `fun v => ((2 / fockScale D v.1 : ℝ) : ℂ)`. Set `u : FVar D T.rank S.rank → Fin S.rank → Fin C.g → ℂ` to `fun v => letterDir C.X C.hr C.idx (f v)`. Set `lam : FVar D T.rank S.rank → (Fin S.rank → Fin C.g → ℂ) → ℂ` to `fun v z => -(π * ∑ k, hx C.X C.bas C.idx x (u v k) (z k))`. Set `Dl : FVar D T.rank S.rank → ((Fin S.rank → Fin C.g → ℂ) → ℂ) → (Fin S.rank → Fin C.g → ℂ) → ℂ` to `fun l Φ z => lam l z * Φ z + (1 / 2 : ℂ) * (fderiv ℝ Φ z (u l) - I * fderiv ℝ Φ z (I • u l))`. Establish `hlam : ∀ l, (∀ a b, lam l (a + b) = lam l a + lam l b) ∧ ∀ (t : ℂ) a, lam l (t • a) = conj t * lam l a`.

Introduce `l`. Use `⟨fun a b => ?_, fun t a => ?_⟩` and prove the remaining obligations. Simplify using `only [lam, GlobalTheory.Dict.hx, Pi.add_apply, mulVec_add, star_add, dotProduct_add, Finset.sum_add_distrib]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [lam, GlobalTheory.Dict.hx, Pi.smul_apply, mulVec_smul, star_smul, dotProduct_smul, smul_eq_mul, ← Finset.mul_sum, RCLike.star_def]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hops` using `GlobalTheory.Ker.CreOp.foldr_creation_zero _ _ u lam θ hlam hθ Dl (fun _ _ _ => rfl)`. Set `A` to `aPlusAll (heisO C.ψ S T) C.θ (fun τ => cplxO 1 (C.sB B τ)) (fun _ => 1) B`. Establish `key : ∀ L : List (FVar D T.rank S.rank), ∀ w, IsRealPt w → L.foldr (fun i g => A i g) G w = gaussR C.X C.bas C.idx x (C.zOf x w) * ((L.map c).prod * L.foldr Dl θ (C.zOf x w))`. Introduce `L`.

Proceed by induction on `L with`. Consider the case `nil => intro w hw`. Simplify using `using hG w hw`. Consider the case `cons a L ih`. Introduce `w hw`.

Establish `hd : Differentiable ℝ (L.foldr Dl θ)` using `(hops L).1.differentiable (by simp)`. Establish `h` using `(GlobalTheory.T.annihilation_creation_periodCoordinates D S T C B hB _ (fun z => (L.map c).prod * L.foldr Dl θ z) (hd.const_mul _) ih a.1 (unitMap 1 (B a.1) a.2.1 a.2.2) (u a) (hdir a.1 a.2.1 a.2.2).symm w hw).2`. Rewrite using `[List.foldr_cons]`. Express the relevant statement in the definitionally equal form `((fockScale D a.1 : ℂ)⁻¹) * crea (heisO C.ψ S T) C.θ a.1 (cplxO 1 (C.sB B a.1)) (unitMap 1 (B a.1) a.2.1 a.2.2) (L.foldr (fun i g => A i g) G) w = _`. Rewrite using `[h, fderiv_const_mul (hd _)]`.

Simplify using `only [List.foldr_cons, List.map_cons, List.prod_cons, _root_.smul_apply, smul_eq_mul]`. Simplify using `only [Dl, lam, c, ← hx0]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `h0 : C.zOf x 0 = 0`.

Establish `h1 : C.realPt 0 = 0`. Use `hadd 0 0` as an intermediate fact. Rewrite `this` using `[add_zero]`. Conclude with `left_eq_add.mp this`. Use function extensionality and compare the values at `k i`.

Simplify using `only [Ctx.zOf, h1, zR, Pi.zero_apply, mulVec_zero]`. Use `split_ifs`. Simplify using `[hermC]`. Both sides reduce to the same expression. Establish `hr0 : IsRealPt (0 : WO S T)`.

Unfold `IsRealPt`. Use extensionality with `i j`. Simplify using the standard rewrite rules. Establish `hg0 : gaussR C.X C.bas C.idx x (0 : Fin S.rank → Fin C.g → ℂ) = 1`. Simplify using `[gaussR, GlobalTheory.Dict.hx]`.

Establish `hsm` using `I2.contDiff_of_diff hθ`. Proceed by induction on `Q using MvPolynomial.induction_on' with`. Consider the case `add P P' hP hP'`. Rewrite using `[map_add, I2.polyDeriv_add, ← hP, ← hP', Ctx.fvec, map_add]`. Both sides reduce to the same expression.

Consider the case `monomial m a`. Establish `e : MvPolynomial.monomial m a = a • MvPolynomial.monomial m (1 : ℂ)`. Rewrite using `[MvPolynomial.smul_monomial, smul_eq_mul, mul_one]`. Rewrite using `[e, map_smul, I2.polyDeriv_smul, Ctx.fvec, map_smul, Pi.smul_apply, smul_eq_mul]`. Use `congr 1`.

Establish `h2 : pureTensorO C.ψ C.θ S T (fun _ => 1) (C.sB B) (fun _ => 1) B G (MvPolynomial.monomial m (1 : ℂ)) = opPow A m G`. Use `(MvPolynomial.basisMonomials (FVar D T.rank S.rank) ℂ).constr_basis ℂ (fun k => opPow A k G) m` as an intermediate fact. Rewrite `this` using `[MvPolynomial.coe_basisMonomials]`. Then use the resulting hypothesis. Rewrite using `[h2, opPow, key _ 0 hr0, h0, hg0, one_mul, (hops _).2]`. Use `Eq.trans ?_ (polyDeriv_aeval_monomial c f _ hsm m 0).symm` and prove the remaining obligations.

Use `congr 1`. Rewrite using `[I2.ct_iter_eq_itD_ofFn]`. Use `congr 1`. Conclude with `List.ofFn_getElem_eq_map _ u`.
-/
theorem fvec_zero_eq_polyDeriv : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), ∀ B, C.IsB B → ∀ (G : WO S T → ℂ) (θ : (Fin S.rank → Fin C.g → ℂ) → ℂ), Differentiable ℂ θ → (∀ w, IsRealPt w → G w = gaussR C.X C.bas C.idx (C.xB B) (C.zOf (C.xB B) w) * θ (C.zOf (C.xB B) w)) → ∀ Q : MvPolynomial (FVar D T.rank S.rank) ℂ, C.fvec B G Q 0 = polyDeriv (C.toH Q) (letterDir C.X C.hr C.idx) θ 0 := by
  intro D S T C B hB G θ hθ hG Q
  obtain ⟨R, -, -, hadd, -⟩ := GlobalTheory.KerReal.real_points D S T C
  obtain ⟨-, -, -, -, hdir, -⟩ := (GlobalTheory.T.thetaKernel_orthonormalFrame_inDomain_periodLinear D S T C).2 B hB
  set x := C.xB B with hx0
  let f : FVar D T.rank S.rank → Harm.Var C.X.Ψ C.q0 C.X.p0 (Fin S.rank) :=
    fun v => (C.m.e v.1, (rowIdx C.hr).symm v.2.1, v.2.2)
  let c : FVar D T.rank S.rank → ℂ := fun v => ((2 / fockScale D v.1 : ℝ) : ℂ)
  let u : FVar D T.rank S.rank → Fin S.rank → Fin C.g → ℂ := fun v => letterDir C.X C.hr C.idx (f v)
  let lam : FVar D T.rank S.rank → (Fin S.rank → Fin C.g → ℂ) → ℂ := fun v z =>
    -(π * ∑ k, hx C.X C.bas C.idx x (u v k) (z k))
  let Dl : FVar D T.rank S.rank → ((Fin S.rank → Fin C.g → ℂ) → ℂ) → (Fin S.rank → Fin C.g → ℂ) → ℂ :=
    fun l Φ z => lam l z * Φ z + (1 / 2 : ℂ) * (fderiv ℝ Φ z (u l) - I * fderiv ℝ Φ z (I • u l))
  have hlam : ∀ l, (∀ a b, lam l (a + b) = lam l a + lam l b) ∧
      ∀ (t : ℂ) a, lam l (t • a) = conj t * lam l a := by
    intro l
    refine ⟨fun a b => ?_, fun t a => ?_⟩
    · simp only [lam, GlobalTheory.Dict.hx, Pi.add_apply, mulVec_add, star_add, dotProduct_add,
        Finset.sum_add_distrib]
      ring
    · simp only [lam, GlobalTheory.Dict.hx, Pi.smul_apply, mulVec_smul, star_smul, dotProduct_smul,
        smul_eq_mul, ← Finset.mul_sum, RCLike.star_def]
      ring
  have hops := GlobalTheory.Ker.CreOp.foldr_creation_zero _ _ u lam θ hlam hθ Dl (fun _ _ _ => rfl)
  let A := aPlusAll (heisO C.ψ S T) C.θ (fun τ => cplxO 1 (C.sB B τ)) (fun _ => 1) B
  have key : ∀ L : List (FVar D T.rank S.rank), ∀ w, IsRealPt w →
      L.foldr (fun i g => A i g) G w =
        gaussR C.X C.bas C.idx x (C.zOf x w) * ((L.map c).prod * L.foldr Dl θ (C.zOf x w)) := by
    intro L
    induction L with
    | nil => intro w hw; simpa using hG w hw
    | cons a L ih =>
      intro w hw
      have hd : Differentiable ℝ (L.foldr Dl θ) := (hops L).1.differentiable (by simp)
      have h := (GlobalTheory.T.annihilation_creation_periodCoordinates D S T C B hB _ (fun z => (L.map c).prod * L.foldr Dl θ z)
        (hd.const_mul _) ih a.1 (unitMap 1 (B a.1) a.2.1 a.2.2) (u a) (hdir a.1 a.2.1 a.2.2).symm w hw).2
      rw [List.foldr_cons]
      change ((fockScale D a.1 : ℂ)⁻¹) * crea (heisO C.ψ S T) C.θ a.1 (cplxO 1 (C.sB B a.1))
        (unitMap 1 (B a.1) a.2.1 a.2.2) (L.foldr (fun i g => A i g) G) w = _
      rw [h, fderiv_const_mul (hd _)]
      simp only [List.foldr_cons, List.map_cons, List.prod_cons, _root_.smul_apply, smul_eq_mul]
      simp only [Dl, lam, c, ← hx0]
      push_cast
      ring
  have h0 : C.zOf x 0 = 0 := by
    have h1 : C.realPt 0 = 0 := by
      have := hadd 0 0
      rw [add_zero] at this
      exact left_eq_add.mp this
    funext k i
    simp only [Ctx.zOf, h1, zR, Pi.zero_apply, mulVec_zero]
    split_ifs
    · simp [hermC]
    · rfl
  have hr0 : IsRealPt (0 : WO S T) := by
    unfold IsRealPt
    ext i j
    simp
  have hg0 : gaussR C.X C.bas C.idx x (0 : Fin S.rank → Fin C.g → ℂ) = 1 := by
    simp [gaussR, GlobalTheory.Dict.hx]
  have hsm := I2.contDiff_of_diff hθ
  induction Q using MvPolynomial.induction_on' with
  | add P P' hP hP' =>
    rw [map_add, I2.polyDeriv_add, ← hP, ← hP', Ctx.fvec, map_add]
    rfl
  | monomial m a =>
    have e : MvPolynomial.monomial m a = a • MvPolynomial.monomial m (1 : ℂ) := by
      rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
    rw [e, map_smul, I2.polyDeriv_smul, Ctx.fvec, map_smul, Pi.smul_apply, smul_eq_mul]
    congr 1
    have h2 : pureTensorO C.ψ C.θ S T (fun _ => 1) (C.sB B) (fun _ => 1) B G
        (MvPolynomial.monomial m (1 : ℂ)) = opPow A m G := by
      have := (MvPolynomial.basisMonomials (FVar D T.rank S.rank) ℂ).constr_basis ℂ
        (fun k => opPow A k G) m
      rwa [MvPolynomial.coe_basisMonomials] at this
    rw [h2, opPow, key _ 0 hr0, h0, hg0, one_mul, (hops _).2]
    refine Eq.trans ?_ (polyDeriv_aeval_monomial c f _ hsm m 0).symm
    congr 1
    rw [I2.ct_iter_eq_itD_ofFn]
    congr 1
    exact List.ofFn_getElem_eq_map _ u

end GlobalTheory.Ker.FockOrigin
