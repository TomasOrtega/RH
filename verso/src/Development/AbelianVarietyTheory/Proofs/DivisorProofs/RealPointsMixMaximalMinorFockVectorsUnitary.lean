import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VacTheta
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.PureTensorLIntertwine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumRealPlacesFockVacuumCharacterStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnramifiedHeckeCharHalfExponentRestrictQuaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdeleAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FockPolynomialVectorBasisChangeEqSubstitutionStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OmPureTensorOOfFinite
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TransposeMemUnitary
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OmPureTensorOReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubstitutionMaximalMinorProductEqSumCauchyBinetStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryTensorPlacesSlotsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalMinorsMatrixMemUnitaryGroupStatement

open NumberField MeasureTheory
open scoped Classical ComplexOrder
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict

attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Introduce `D a d N n m hN hn K hK`. Substitute `hN hn` using the available equality. Establish `hr : (MvPolynomial.rename (fun k : Formalism.MainNotions.GL3Theta.Idx D n N => ((k.1, Fin.cast rfl k.2.1, Fin.cast rfl k.2.2) : D.what₂.Tau × Fin N × Fin n)) : MvPolynomial (Formalism.MainNotions.GL3Theta.Idx D n N) ℂ →ₐ[ℂ] _) = AlgHom.id ℂ _`. Simplify using `only [Fin.cast_eq_self, Prod.mk.eta]`. Conclude with `MvPolynomial.rename_id`.

Simplify using `only [hr, AlgHom.id_apply]`. Conclude with `⟨_, GlobalTheory.T.prod_unitary_mem_unitaryGroup_pi D.what₂.Tau {s : Fin n → Fin N // StrictMono s} m _ fun τ => GlobalTheory.T.maximalMinorsMatrix_mem_unitaryGroup (a := n) (K τ) (hK τ), fun T => by rw [GlobalTheory.T.substitution_maximalMinorProduct_eq_sum_cauchyBinet D K T]; r …`.
-/
theorem GlobalTheory.NormDict.RealB.subst_minorPol_unitary : ∀ (D : D7) {a d N n : ℕ} {m : D.what₂.Tau → ℕ} (hN : N = d) (hn : n = a) (K : D.what₂.Tau → Matrix (Fin N) (Fin N) ℂ), (∀ τ, K τ ∈ Matrix.unitaryGroup (Fin N) ℂ) → ∃ U : Matrix (Tup D a d m) (Tup D a d m) ℂ, U ∈ Matrix.unitaryGroup (Tup D a d m) ℂ ∧ ∀ T : Tup D a d m, GlobalTheory.CompactHowe.substF K (fun _ => (1 : Matrix (Fin n) (Fin n) ℂ)) (MvPolynomial.rename (fun k : Formalism.MainNotions.GL3Theta.Idx D a d => ((k.1, Fin.cast hN.symm k.2.1, Fin.cast hn.symm k.2.2) : D.what₂.Tau × Fin N × Fin n)) (minorPol D T)) = ∑ T', U T T' • MvPolynomial.rename (fun k : Formalism.MainNotions.GL3Theta.Idx D a d => ((k.1, Fin.cast hN.symm k.2.1, Fin.cast hn.symm k.2.2) : D.what₂.Tau × Fin N × Fin n)) (minorPol D T') := by
  intro D a d N n m hN hn K hK
  subst hN hn
  have hr : (MvPolynomial.rename (fun k : Formalism.MainNotions.GL3Theta.Idx D n N => ((k.1, Fin.cast rfl k.2.1, Fin.cast rfl k.2.2) : D.what₂.Tau × Fin N × Fin n)) : MvPolynomial (Formalism.MainNotions.GL3Theta.Idx D n N) ℂ →ₐ[ℂ] _) = AlgHom.id ℂ _ := by
    simp only [Fin.cast_eq_self, Prod.mk.eta]
    exact MvPolynomial.rename_id
  simp only [hr, AlgHom.id_apply]
  exact ⟨_, GlobalTheory.T.prod_unitary_mem_unitaryGroup_pi D.what₂.Tau {s : Fin n → Fin N // StrictMono s} m _ fun τ => GlobalTheory.T.maximalMinorsMatrix_mem_unitaryGroup (a := n) (K τ) (hK τ),
    fun T => by rw [GlobalTheory.T.substitution_maximalMinorProduct_eq_sum_cauchyBinet D K T]; rfl⟩

namespace GlobalTheory.NormDict.RealB

/- English proof (translation)
Introduce `D cc δ t0 Q P X hX k hk`. Establish `hF` using `hX.1`. Establish `hW` using `hX.2.weil`. Establish `hθ` using `hX.2.inf`. Set `K : D.what₂.Tau → Matrix (Fin X.B.rank) (Fin X.B.rank) ℂ` to `fun τ => compAt X.θ τ (Formalism.L2.Theta.mt X.B k)`.

Establish `hKu : ∀ τ, K τ ∈ Matrix.unitaryGroup (Fin X.B.rank) ℂ` using `fun τ => GlobalTheory.RealColAct.compAt_mem_unitary hθ hF.gramB k τ`. Take `⟨U₀, hU₀, hsub⟩` from `GlobalTheory.NormDict.RealB.subst_minorPol_unitary D (m := P.n) X.rkB X.rkA K hKu`. Establish `c1 : ∀ (V : HSp D) τ, compAt X.θ τ (Formalism.L2.Theta.mt V 1) = 1` using `fun V τ => Matrix.map_one (f := (X.θ τ).comp (infPart D)) (map_zero _) (map_one _)`. Establish `gr1 : ∀ (V : HSp D), V.gram = 1 → ∀ τ, gramAt D V τ = 1` using `fun V h τ => by`. Rewrite using `[gramAt, h, Matrix.map_one _ (map_zero _) (map_one _)]`.

Establish `cart : ∀ (V : HSp D), V.gram = 1 → ∀ τ, IsCartanInv (gramAt D V τ) 1` using `fun V h τ => by`. Rewrite using `[gr1 V h]; exact ⟨Matrix.mul_one _, by simp, by rw [Matrix.mul_one]; exact Matrix.PosDef.one⟩`. Take `⟨η, e1, e2, e3, e4⟩` from `GlobalTheory.T.exists_unramifiedHeckeChar_halfExponent_restrict_quadratic D`. Take `⟨x, hx, -⟩` from `GlobalTheory.VacuumCharacter.exists_root hθ X.A (fun τ => by rw [gr1 _ hF.gramA]; simp) 1 (one_mem _)`. Take `⟨y, hy, -⟩` from `GlobalTheory.VacuumCharacter.exists_root hθ X.B (fun τ => by rw [gr1 _ hF.gramB]; simp) k hk`.

Establish `hvac` using `GlobalTheory.T.weilDatum_realPlaces_fockVacuum_character D X.ψ hW.std X.A X.B X.θ hθ X.χA X.χB X.om η ⟨e1, e4, e3, e2⟩ hW (fun _ => 1) (fun _ => 1) (cart _ hF.gramA) (cart _ hF.gramB) 1 (one_mem _) k hk (fun τ => by rw [Matrix.one_mul, Matrix.mul_one]) (fun τ => by rw [Matrix.one …`. Choose the witnesses or unpack the hypotheses as in `⟨c, hc1, hcv⟩ : ∃ c : ℂ, ‖c‖ = 1 ∧ X.om (1, k) X.vac = c • X.vac := by`. Use `⟨_, ?_, hvac⟩` and prove the remaining obligations. Rewrite using `[norm_mul, Circle.norm_coe, one_mul, norm_prod]`. Use `Finset.prod_eq_one fun τ _ => ?_` and prove the remaining obligations.

Rewrite using `[GlobalTheory.KJReal.detPlus_one_one, inv_one, c1, Matrix.det_one, one_pow, mul_one, norm_pow]`. Establish `hd` using `Matrix.det_of_mem_unitary (hKu τ)`. Rewrite using `[show ‖(compAt X.θ τ (Formalism.L2.Theta.mt X.B k)).det‖ = 1 from CStarRing.norm_of_mem_unitary hd, one_pow]`. Use `⟨c • U₀, ?_, fun T => ?_⟩` and prove the remaining obligations. Rewrite `hU₀`, the goal using `[Matrix.mem_unitaryGroup_iff]`.

Rewrite using `[star_smul, Matrix.smul_mul, Matrix.mul_smul, hU₀, smul_smul, RCLike.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hc1]`. Simplify using the standard rewrite rules. Establish `e2` using `(GlobalTheory.OrientedHeis.om_pureTensorO D X.ψ X.θ X.A X.B X.χA X.χB X.om hW hθ (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 1 * 1) (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun τ => 1 * K τ) 1 k (fun τ => by rw [c1, Matrix.one_mul]) (fun τ => by rw [Matrix.one_mul, Matrix.mul …`. Establish `e3` using `GlobalTheory.T.fockPolynomialVector_basisChange_eq_substitution D X.ψ X.θ X.A X.B hW.std hθ (fun _ => 1) (fun _ => 1) (fun _ => 1) K X.vac hX.2.vac_theta (MvPolynomial.rename X.var (minorPol D T))`. Establish `e4` using `hsub T`.

Simplify using `only [inv_one, Matrix.transpose_one] at e3`. Express the relevant statement in the definitionally equal form `X.om (1, k) (pureTensorO X.ψ X.θ X.A X.B (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 1) X.vac _) = _`. Rewrite using `[e2, hcv, GlobalTheory.FiniteFock.pureTensorO_smul, e3]`. Express the relevant statement in the definitionally equal form `c • (pureTensorO X.ψ X.θ X.A X.B (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 1) X.vac) (GlobalTheory.CompactHowe.substF K (fun _ => 1) (MvPolynomial.rename (fun k : Formalism.MainNotions.GL3Theta.Idx D P.a P.d => ((k.1, Fin.cast X.rkB.symm k.2.1, Fin.cast X.rkA.symm k.2.2) : …`. Rewrite using `[e4, map_sum, Finset.smul_sum]`.

Use `Finset.sum_congr rfl fun T' _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, smul_smul, Matrix.smul_apply, smul_eq_mul]`. Both sides reduce to the same expression.
-/
theorem real_mix : ∀ {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ t0 : ℂ} {Q : ℕ} (P : Pair D cc δ t0 Q) (X : Data P), IsDict P X →
    ∀ k ∈ GinfC X.B, ∃ U : Matrix (Tup D P.a P.d P.n) (Tup D P.a P.d P.n) ℂ, U ∈ Matrix.unitaryGroup (Tup D P.a P.d P.n) ℂ ∧
      ∀ T, X.om (1, k) (X.fock T) = ∑ T', U T T' • X.fock T' := by
  intro D cc δ t0 Q P X hX k hk
  have hF := hX.1
  have hW := hX.2.weil
  have hθ := hX.2.inf
  let K : D.what₂.Tau → Matrix (Fin X.B.rank) (Fin X.B.rank) ℂ := fun τ => compAt X.θ τ (Formalism.L2.Theta.mt X.B k)
  have hKu : ∀ τ, K τ ∈ Matrix.unitaryGroup (Fin X.B.rank) ℂ := fun τ => GlobalTheory.RealColAct.compAt_mem_unitary hθ hF.gramB k τ
  obtain ⟨U₀, hU₀, hsub⟩ := GlobalTheory.NormDict.RealB.subst_minorPol_unitary D (m := P.n) X.rkB X.rkA K hKu
  have c1 : ∀ (V : HSp D) τ, compAt X.θ τ (Formalism.L2.Theta.mt V 1) = 1 := fun V τ =>
    Matrix.map_one (f := (X.θ τ).comp (infPart D)) (map_zero _) (map_one _)
  have gr1 : ∀ (V : HSp D), V.gram = 1 → ∀ τ, gramAt D V τ = 1 := fun V h τ => by
    rw [gramAt, h, Matrix.map_one _ (map_zero _) (map_one _)]
  have cart : ∀ (V : HSp D), V.gram = 1 → ∀ τ, IsCartanInv (gramAt D V τ) 1 := fun V h τ => by
    rw [gr1 V h]; exact ⟨Matrix.mul_one _, by simp, by rw [Matrix.mul_one]; exact Matrix.PosDef.one⟩
  obtain ⟨η, e1, e2, e3, e4⟩ := GlobalTheory.T.exists_unramifiedHeckeChar_halfExponent_restrict_quadratic D
  obtain ⟨x, hx, -⟩ := GlobalTheory.VacuumCharacter.exists_root hθ X.A (fun τ => by rw [gr1 _ hF.gramA]; simp) 1 (one_mem _)
  obtain ⟨y, hy, -⟩ := GlobalTheory.VacuumCharacter.exists_root hθ X.B (fun τ => by rw [gr1 _ hF.gramB]; simp) k hk
  have hvac := GlobalTheory.T.weilDatum_realPlaces_fockVacuum_character D X.ψ hW.std X.A X.B X.θ hθ X.χA X.χB X.om η ⟨e1, e4, e3, e2⟩ hW (fun _ => 1) (fun _ => 1)
    (cart _ hF.gramA) (cart _ hF.gramB) 1 (one_mem _) k hk (fun τ => by rw [Matrix.one_mul, Matrix.mul_one])
    (fun τ => by rw [Matrix.one_mul, Matrix.mul_one]) x y hx hy X.vac hX.2.vac_theta hX.2.vac_fock
  obtain ⟨c, hc1, hcv⟩ : ∃ c : ℂ, ‖c‖ = 1 ∧ X.om (1, k) X.vac = c • X.vac := by
    refine ⟨_, ?_, hvac⟩
    rw [norm_mul, Circle.norm_coe, one_mul, norm_prod]
    refine Finset.prod_eq_one fun τ _ => ?_
    rw [GlobalTheory.KJReal.detPlus_one_one, inv_one, c1, Matrix.det_one, one_pow, mul_one, norm_pow]
    have hd := Matrix.det_of_mem_unitary (hKu τ)
    rw [show ‖(compAt X.θ τ (Formalism.L2.Theta.mt X.B k)).det‖ = 1 from CStarRing.norm_of_mem_unitary hd, one_pow]
  refine ⟨c • U₀, ?_, fun T => ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff] at hU₀ ⊢
    rw [star_smul, Matrix.smul_mul, Matrix.mul_smul, hU₀, smul_smul, RCLike.star_def, Complex.mul_conj,
      Complex.normSq_eq_norm_sq, hc1]
    simp
  · have e2 := (GlobalTheory.OrientedHeis.om_pureTensorO D X.ψ X.θ X.A X.B X.χA X.χB X.om hW hθ (fun _ => 1) (fun _ => 1)
      (fun _ => 1) (fun _ => 1 * 1) (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun τ => 1 * K τ) 1 k
      (fun τ => by rw [c1, Matrix.one_mul]) (fun τ => by rw [Matrix.one_mul, Matrix.mul_one])
      (fun τ => by rw [c1, Matrix.one_mul]) (fun τ => by rw [Matrix.one_mul, Matrix.mul_one]) X.vac hX.2.vac_theta
      (MvPolynomial.rename X.var (minorPol D T))).2
    have e3 := GlobalTheory.T.fockPolynomialVector_basisChange_eq_substitution D X.ψ X.θ X.A X.B hW.std hθ (fun _ => 1) (fun _ => 1) (fun _ => 1) K X.vac hX.2.vac_theta
      (MvPolynomial.rename X.var (minorPol D T))
    have e4 := hsub T
    simp only [inv_one, Matrix.transpose_one] at e3
    change X.om (1, k) (pureTensorO X.ψ X.θ X.A X.B (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 1) X.vac _) = _
    rw [e2, hcv, GlobalTheory.FiniteFock.pureTensorO_smul, e3]
    change c • (pureTensorO X.ψ X.θ X.A X.B (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 1) X.vac) (GlobalTheory.CompactHowe.substF K (fun _ => 1) (MvPolynomial.rename (fun k : Formalism.MainNotions.GL3Theta.Idx D P.a P.d => ((k.1, Fin.cast X.rkB.symm k.2.1, Fin.cast X.rkA.symm k.2.2) : D.what₂.Tau × Fin X.B.rank × Fin X.A.rank)) (minorPol D T))) = _
    rw [e4, map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun T' _ => ?_
    rw [map_smul, smul_smul, Matrix.smul_apply, smul_eq_mul]
    rfl

end GlobalTheory.NormDict.RealB
