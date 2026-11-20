import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsCoreLat
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.EisRegularAtOfEisPoleLE
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqExistsIffDsExists
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdjointExchangeLawsThetaHeisenbergStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CoreChainAdjointLatticeExchangeStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SelfDualLatticeChangeOfLatticeLawsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationCommFockPolynomialVectors
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HomLatticeCompletionSelfAnnihilatorAtPlaces
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MapFinNeg
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulEqZeroOfInf
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GlobalFormOfSiegelWeil
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsFinCombSingleZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfinitePartEqZeroOfIsHalfIdempotentSumStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentSumOverFinitePlacesUniqueStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaFunctionFiniteHeisenbergCombinationStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLatticeVacuumSumHeisenbergTranslatesStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsFockVacuumAtFiniteHeisenbergCombinationStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SumHeisenbergTranslatesLatticeVacuumNeZeroStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CosetSumHeisenbergIsEigenvectorStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaIsLatticeVacuumFockPureTensorStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaChainUnitVacuumOtherLatticesExistsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRepresentativesHalfQuotientPairingTrivialD
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CorePairIntegralPointPairsTriviallyHalfStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HalfVectorSymplecticOrthogonalStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdjointExchangeIsLatticeVacuumCoreChainStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chain (IsVacVec ptOf)
open GlobalTheory.PairLift (adjO)
open scoped ComplexConjugate

noncomputable section

namespace GlobalTheory.CosDatum

attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a x => show a ⊗ₜ[D.host.F] star (star x) = _`. Rewrite using `[star_star]`. Consider the case `add x y hx hy => rw [map_add, map_add, hx, hy]`.
-/
theorem cA_cA₀ {D : D7} (z : AE D) : cA D (cA D z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => show a ⊗ₜ[D.host.F] star (star x) = _; rw [star_star]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/- English proof (translation)
Apply `AddSubgroup.closure_mono` to reduce the goal to its premises. Introduce and unpack `w ⟨α, hα, -, rest⟩`. Conclude with `⟨α, hα, fun v h => (h trivial).elim, rest⟩`.
-/
theorem latO_le_true {D : D7} (S T : HSp D) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E))
    (P : HeightOneSpectrum (𝓞 D.host.F) → Prop) : latO S T LS LT P ≤ latO S T LS LT fun _ => True := by
  apply AddSubgroup.closure_mono
  rintro w ⟨α, hα, -, rest⟩
  exact ⟨α, hα, fun v h => (h trivial).elim, rest⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun u hu => hf.1 u (h hu), fun e he u hu hh => hf.2 e he u (h hu) hh⟩`.
-/
theorem isLatVac_mono {D : D7} {m n : ℕ} {hs : Mx D m n → (Mx D m n → ℂ) → (Mx D m n → ℂ)} {Λ Λ' : AddSubgroup (Mx D m n)}
    (h : Λ' ≤ Λ) {f : Mx D m n → ℂ} (hf : IsLatVac hs Λ f) : IsLatVac hs Λ' f :=
  ⟨fun u hu => hf.1 u (h hu), fun e he u hu hh => hf.2 e he u (h hu) hh⟩

/- English proof (translation)
Introduce `h` and use `by have := ψ.map_add_eq_mul a (-a) rw [add_neg_cancel, ψ.map_zero_eq_one, h, zero_mul] at this exact one_ne_zero this`.
-/
theorem addChar_ne_zero {A : Type} [AddGroup A] (ψ : AddChar A ℂ) (a : A) : ψ a ≠ 0 := fun h => by
  have := ψ.map_add_eq_mul a (-a)
  rw [add_neg_cancel, ψ.map_zero_eq_one, h, zero_mul] at this
  exact one_ne_zero this

end GlobalTheory.CosDatum

namespace GlobalTheory.CoreOnto

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.CosDatum in

/- English proof (translation)
Introduce `D hq T L μ0 hL sc G W M hM i hi r r' hr hr' S S' MM MM' x₀ hx₀`. Establish `hψ : IsStdChar D W.ψ (-1)` using `W.ψ_std`. Establish `hθ : IsInfFam W.θ` using `W.θ_is`. Establish `hEx : ExchLaw D` using `GlobalTheory.T.adjointExchange_laws_thetaHeisenberg D`. Establish `hLE : LatExch` using `GlobalTheory.T.coreChain_adjoint_latticeExchange`.

Establish `hadj` using `GlobalTheory.AdjLawPf.adjLaw D W.ψ hψ (G.V (.core i)) (G.V (.core (i + 1)))`. Take `⟨e, he, -⟩` from `W.cosVec_is`. Take `⟨f₀, hf₀⟩` from `GlobalTheory.T.thetaChain_unitVacuum_otherLattices_exists D hq T L μ0 hL sc G W M hM i hi r r' S S' MM MM'`. Take `⟨R, hR1, hR2, hR3, hR4⟩` from `GlobalTheory.T.exists_representatives_half_quotient_pairing_trivial_depthLattice D hq T L μ0 hL sc G W M hM i hi e he`. Establish `hxi` using `GlobalTheory.T.corePair_integralPoint_pairs_trivially_half D hq T L μ0 hL sc G W M hM i hi e he x₀ hx₀`.

Establish `hhalf : ∀ z ∈ R, IsHalf e (adjO (G.V (.core i)) (G.V (.core (i + 1))) z)` using `fun z hz => by`. Use `hadj.half _ z (hR1 z hz).1` as an intermediate fact. Rewrite `this` using `[cA_cA₀]`. Then use the resulting hypothesis. Establish `hfin : ∀ z ∈ R, (adjO (G.V (.core i)) (G.V (.core (i + 1))) z).map (infPart D) = 0` using `fun z hz => GlobalTheory.T.infinitePart_eq_zero_of_isHalf_idempotentSum _ e he _ (Or.inl (hhalf z hz))`. Set `c : WO (G.pS (.core i)) (G.pT (.core i)) → ℂ` to `fun z => W.ψ (-symplO (G.pS (.core i)) (G.pT (.core i)) (e • x₀.map (incA D)) z)`.

Set `f : WO r.sp r'.sp → ℂ` to `∑ z ∈ R, c z • heisO W.ψ r.sp r'.sp (adjO (G.V (.core i)) (G.V (.core (i + 1))) z) f₀`. Establish `hexs : ∀ g : WO r.sp r'.sp → ℂ, exch (G.V (.core i)) (G.V (.core (i + 1))) (∑ z ∈ R, c z • heisO W.ψ r.sp r'.sp (adjO (G.V (.core i)) (G.V (.core (i + 1))) z) g) = ∑ z ∈ R, c z • heisO W.ψ (G.pS (.core i)) (G.pT (.core i)) z (exch (G.V (.core i)) (G.V (.core (i + 1))) g)`. Introduce `g`. Use function extensionality and compare the values at `x`. Establish `h2` using `fun z : WO (G.pS (.core i)) (G.pT (.core i)) => congrFun ((hEx W.ψ (G.V (.core i)) (G.V (.core (i + 1))) hψ).2.1 z g) x`.

Use `show (∑ z ∈ R, c z • heisO W.ψ r.sp r'.sp (adjO (G.V (.core i)) (G.V (.core (i + 1))) z) g) (adjO (G.V (.core i)) (G.V (.core (i + 1))) x) = _`. Rewrite using `[Finset.sum_apply, Finset.sum_apply]`. Use `Finset.sum_congr rfl fun z _ => ?_` and prove the remaining obligations. Rewrite using `[Pi.smul_apply, Pi.smul_apply, h2 z]`. Both sides reduce to the same expression.

Establish `hf₀th : IsThetaFunO W.ψ r.sp r'.sp f₀` using `hf₀.2.theta`. Establish `hcomb` using `GlobalTheory.T.isThetaFunction_finiteHeisenbergCombination W.ψ W.θ r.sp r'.sp hψ hθ f₀ hf₀th R c _ hfin`. Establish `hex0 : exch (G.V (.core i)) (G.V (.core (i + 1))) f₀ ≠ 0`. Introduce `h0`. Apply `GlobalTheory.SeeSaw.Inh.vac_ne_zero hf₀` to reduce the goal to its premises.

Use function extensionality and compare the values at `y`. Take `⟨x, rfl⟩` from `(hEx W.ψ _ _ hψ).2.2.2.1.2 y`. Conclude with `congrFun h0 x`. Establish `hRne : ∃ z ∈ R, c z ≠ 0`. Take `⟨y', hy', -⟩` from `hR2 0 (fun _ _ => mul_zero _) (fun u _ => by`.

Establish `h00 : symplO (G.pS (.core i)) (G.pT (.core i)) u 0 = 0` using `by unfold symplO hO; simp`. Rewrite using `[h00, AddChar.map_zero_eq_one])`. Conclude with `⟨y', hy', addChar_ne_zero _ _⟩`. Use `⟨f, ⟨hcomb.1, ?_, fun τ => GlobalTheory.T.isFockVacuumAt_finiteHeisenbergCombination W.ψ W.θ r.sp r'.sp hψ hθ _ τ f₀ hf₀th (hf₀.2.fock τ) R c _ hfin⟩, ?_, fun φ => ?_⟩` and prove the remaining obligations. Introduce `h0`.

Establish `h2 : exch (G.V (.core i)) (G.V (.core (i + 1))) f = 0` using `by rw [h0]; rfl`. Use `GlobalTheory.T.sum_heisenbergTranslates_latticeVacuum_ne_zero W.ψ (G.pS (.core i)) (G.pT (.core i)) (G.latS (.core i)) (G.latT (.core i)) G.pl.W0 e he R hR4 _ (GlobalTheory.T.adjointExchange_isLatticeVacuum_coreChain D hq T L μ0 hL sc G W M hM hEx hLE i hi r r' hr hr' f₀ hf₀.2.la …` and prove the remaining obligations. Rewrite using `[← hexs f₀]`. Conclude with `h2`. Use `show IsLatVac _ _ _`.

Use `GlobalTheory.T.isLatticeVacuum_sum_heisenbergTranslates W.ψ r.sp r'.sp _ f₀ (isLatVac_mono (latO_le_true _ _ _ _ _) hf₀.2.lat) R c _ ?_` and prove the remaining obligations. Introduce `z hz u hu`. Rewrite using `[GlobalTheory.T.half_vector_symplectic_orthogonal D hq T L μ0 hL sc G W M hM e he r.sp r'.sp _ _ u hu _ (hhalf z hz), AddChar.map_zero_eq_one]`. Establish `hpt : ptOf W.ψ W.θ MM MM' f φ = ∑ z ∈ R, c z • heisO W.ψ r.sp r'.sp (adjO (G.V (.core i)) (G.V (.core (i + 1))) z) (ptOf W.ψ W.θ MM MM' f₀ φ)` using `hcomb.2 (cart MM) (onb MM) (cart MM') (onb MM') φ`. Establish `hfl` using `GlobalTheory.T.isTheta_isLatticeVacuum_fockPureTensor W.ψ W.θ r.sp r'.sp hψ hθ _ _ _ f₀ hf₀th hf₀.2.lat (cart MM) (onb MM) (cart MM') (onb MM') φ`.

Establish `hgl` using `GlobalTheory.T.adjointExchange_isLatticeVacuum_coreChain D hq T L μ0 hL sc G W M hM hEx hLE i hi r r' hr hr' _ hfl.2`. Establish `hth : IsThetaFunO W.ψ r.sp r'.sp (ptOf W.ψ W.θ MM MM' f φ)`. Rewrite using `[hpt]`. Conclude with `(GlobalTheory.T.isThetaFunction_finiteHeisenbergCombination W.ψ W.θ r.sp r'.sp hψ hθ _ hfl.1 R c _ hfin).1`. Establish `hth'` using `(((GlobalTheory.T.selfDualLattice_changeOfLattice_laws D).2.2 W.ψ (G.V (.core i)) (G.V (.core (i + 1))) r r').1 _).1 hth`.

Establish `hΦth` using `((hEx W.ψ (G.V (.core i)) (G.V (.core (i + 1))) hψ).1 _).1 hth'`. Establish `hΦ` using `hexs (ptOf W.ψ W.θ MM MM' f₀ φ)`. Rewrite `hΦ` using `[← hpt]`. Rewrite `hΦth`, the goal using `[hΦ]`. Use `⟨⟨hΦth, GlobalTheory.T.isLatticeVacuum_sum_heisenbergTranslates W.ψ _ _ _ _ (isLatVac_mono (Λ' := depLat G (.core i)) (fun u hu => hu.1) hgl) R c (fun z => z) (fun z hz => (hR1 z hz).2)⟩, ?_⟩` and prove the remaining obligations.

Introduce `e' he' y hy hyd`. Take `rfl` from `GlobalTheory.T.idempotentSum_over_finite_places_unique _ _ _ he he'`. Conclude with `GlobalTheory.T.cosetSum_heisenberg_isEigenvector W.ψ _ _ (G.latS (.core i)) (G.latT (.core i)) G.pl.W0 e he (depLat G (.core i)) R _ hR1 hR2 hR3 hxi _ hgl y hy hyd`.
-/
theorem datumEx : DatumEx := by
  intro D hq T L μ0 hL sc G W M hM i hi r r' hr hr' S S' MM MM' x₀ hx₀
  have hψ : IsStdChar D W.ψ (-1) := W.ψ_std
  have hθ : IsInfFam W.θ := W.θ_is
  have hEx : ExchLaw D := GlobalTheory.T.adjointExchange_laws_thetaHeisenberg D
  have hLE : LatExch := GlobalTheory.T.coreChain_adjoint_latticeExchange
  have hadj := GlobalTheory.AdjLawPf.adjLaw D W.ψ hψ (G.V (.core i)) (G.V (.core (i + 1)))
  obtain ⟨e, he, -⟩ := W.cosVec_is
  obtain ⟨f₀, hf₀⟩ := GlobalTheory.T.thetaChain_unitVacuum_otherLattices_exists D hq T L μ0 hL sc G W M hM i hi r r' S S' MM MM'
  obtain ⟨R, hR1, hR2, hR3, hR4⟩ := GlobalTheory.T.exists_representatives_half_quotient_pairing_trivial_depthLattice D hq T L μ0 hL sc G W M hM i hi e he
  have hxi := GlobalTheory.T.corePair_integralPoint_pairs_trivially_half D hq T L μ0 hL sc G W M hM i hi e he x₀ hx₀
  have hhalf : ∀ z ∈ R, IsHalf e (adjO (G.V (.core i)) (G.V (.core (i + 1))) z) := fun z hz => by
    have := hadj.half _ z (hR1 z hz).1
    rwa [cA_cA₀] at this
  have hfin : ∀ z ∈ R, (adjO (G.V (.core i)) (G.V (.core (i + 1))) z).map (infPart D) = 0 := fun z hz =>
    GlobalTheory.T.infinitePart_eq_zero_of_isHalf_idempotentSum _ e he _ (Or.inl (hhalf z hz))
  let c : WO (G.pS (.core i)) (G.pT (.core i)) → ℂ :=
    fun z => W.ψ (-symplO (G.pS (.core i)) (G.pT (.core i)) (e • x₀.map (incA D)) z)
  let f : WO r.sp r'.sp → ℂ :=
    ∑ z ∈ R, c z • heisO W.ψ r.sp r'.sp (adjO (G.V (.core i)) (G.V (.core (i + 1))) z) f₀
  have hexs : ∀ g : WO r.sp r'.sp → ℂ,
      exch (G.V (.core i)) (G.V (.core (i + 1)))
        (∑ z ∈ R, c z • heisO W.ψ r.sp r'.sp (adjO (G.V (.core i)) (G.V (.core (i + 1))) z) g) =
      ∑ z ∈ R, c z • heisO W.ψ (G.pS (.core i)) (G.pT (.core i)) z (exch (G.V (.core i)) (G.V (.core (i + 1))) g) := by
    intro g
    funext x
    have h2 := fun z : WO (G.pS (.core i)) (G.pT (.core i)) =>
      congrFun ((hEx W.ψ (G.V (.core i)) (G.V (.core (i + 1))) hψ).2.1 z g) x
    show (∑ z ∈ R, c z • heisO W.ψ r.sp r'.sp (adjO (G.V (.core i)) (G.V (.core (i + 1))) z) g)
      (adjO (G.V (.core i)) (G.V (.core (i + 1))) x) = _
    rw [Finset.sum_apply, Finset.sum_apply]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [Pi.smul_apply, Pi.smul_apply, h2 z]
    rfl
  have hf₀th : IsThetaFunO W.ψ r.sp r'.sp f₀ := hf₀.2.theta
  have hcomb := GlobalTheory.T.isThetaFunction_finiteHeisenbergCombination W.ψ W.θ r.sp r'.sp hψ hθ f₀ hf₀th R c _ hfin
  have hex0 : exch (G.V (.core i)) (G.V (.core (i + 1))) f₀ ≠ 0 := by
    intro h0
    apply GlobalTheory.SeeSaw.Inh.vac_ne_zero hf₀
    funext y
    obtain ⟨x, rfl⟩ := (hEx W.ψ _ _ hψ).2.2.2.1.2 y
    exact congrFun h0 x
  have hRne : ∃ z ∈ R, c z ≠ 0 := by
    obtain ⟨y', hy', -⟩ := hR2 0 (fun _ _ => mul_zero _) (fun u _ => by
      have h00 : symplO (G.pS (.core i)) (G.pT (.core i)) u 0 = 0 := by unfold symplO hO; simp
      rw [h00, AddChar.map_zero_eq_one])
    exact ⟨y', hy', addChar_ne_zero _ _⟩
  refine ⟨f, ⟨hcomb.1, ?_, fun τ => GlobalTheory.T.isFockVacuumAt_finiteHeisenbergCombination W.ψ W.θ r.sp r'.sp hψ hθ _ τ f₀ hf₀th (hf₀.2.fock τ) R c _ hfin⟩,
    ?_, fun φ => ?_⟩
  · intro h0
    have h2 : exch (G.V (.core i)) (G.V (.core (i + 1))) f = 0 := by rw [h0]; rfl
    refine GlobalTheory.T.sum_heisenbergTranslates_latticeVacuum_ne_zero W.ψ (G.pS (.core i)) (G.pT (.core i)) (G.latS (.core i)) (G.latT (.core i)) G.pl.W0 e he R hR4
      _ (GlobalTheory.T.adjointExchange_isLatticeVacuum_coreChain D hq T L μ0 hL sc G W M hM hEx hLE i hi r r' hr hr' f₀ hf₀.2.lat) hex0 c hRne ?_
    rw [← hexs f₀]
    exact h2
  · show IsLatVac _ _ _
    refine GlobalTheory.T.isLatticeVacuum_sum_heisenbergTranslates W.ψ r.sp r'.sp _ f₀ (isLatVac_mono (latO_le_true _ _ _ _ _) hf₀.2.lat) R c _ ?_
    intro z hz u hu
    rw [GlobalTheory.T.half_vector_symplectic_orthogonal D hq T L μ0 hL sc G W M hM e he r.sp r'.sp _ _ u hu _ (hhalf z hz), AddChar.map_zero_eq_one]
  · have hpt : ptOf W.ψ W.θ MM MM' f φ = ∑ z ∈ R, c z • heisO W.ψ r.sp r'.sp
        (adjO (G.V (.core i)) (G.V (.core (i + 1))) z) (ptOf W.ψ W.θ MM MM' f₀ φ) :=
      hcomb.2 (cart MM) (onb MM) (cart MM') (onb MM') φ
    have hfl := GlobalTheory.T.isTheta_isLatticeVacuum_fockPureTensor W.ψ W.θ r.sp r'.sp hψ hθ _ _ _ f₀ hf₀th hf₀.2.lat (cart MM) (onb MM) (cart MM') (onb MM') φ
    have hgl := GlobalTheory.T.adjointExchange_isLatticeVacuum_coreChain D hq T L μ0 hL sc G W M hM hEx hLE i hi r r' hr hr' _ hfl.2
    have hth : IsThetaFunO W.ψ r.sp r'.sp (ptOf W.ψ W.θ MM MM' f φ) := by
      rw [hpt]; exact (GlobalTheory.T.isThetaFunction_finiteHeisenbergCombination W.ψ W.θ r.sp r'.sp hψ hθ _ hfl.1 R c _ hfin).1
    have hth' := (((GlobalTheory.T.selfDualLattice_changeOfLattice_laws D).2.2 W.ψ (G.V (.core i)) (G.V (.core (i + 1))) r r').1 _).1 hth
    have hΦth := ((hEx W.ψ (G.V (.core i)) (G.V (.core (i + 1))) hψ).1 _).1 hth'
    have hΦ := hexs (ptOf W.ψ W.θ MM MM' f₀ φ)
    rw [← hpt] at hΦ
    rw [hΦ] at hΦth ⊢
    refine ⟨⟨hΦth, GlobalTheory.T.isLatticeVacuum_sum_heisenbergTranslates W.ψ _ _ _ _ (isLatVac_mono (Λ' := depLat G (.core i)) (fun u hu => hu.1) hgl) R c (fun z => z)
      (fun z hz => (hR1 z hz).2)⟩, ?_⟩
    intro e' he' y hy hyd
    obtain rfl := GlobalTheory.T.idempotentSum_over_finite_places_unique _ _ _ he he'
    exact GlobalTheory.T.cosetSum_heisenberg_isEigenvector W.ψ _ _ (G.latS (.core i)) (G.latT (.core i)) G.pl.W0 e he (depLat G (.core i)) R _ hR1 hR2 hR3 hxi
      _ hgl y hy hyd

end GlobalTheory.CoreOnto

end
