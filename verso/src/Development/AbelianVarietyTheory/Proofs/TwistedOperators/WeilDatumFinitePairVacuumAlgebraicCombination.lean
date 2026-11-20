import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BottomExistsIntegrable
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsVacuumMovedThetaVacuum
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisOSumSmul
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurFiniteHeisenbergFockVacuumThetaFunctions
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaPairingInvariant
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CentralFlipVacuumEqMultipleOfTranslateMean
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompletedHomLatticeFinitelyGenerated
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompletedHomLatticeMultipleMemOpenLevel
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.AddNsmulResidueAssoc
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.OmAtSmulRight
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaKernelAlgebraicExpansion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisThetaLaws
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.DifferentiableOfChar
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilFinitePointPreservesFockVacuum
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RealLowestKTypeOfExtremalVectorCase
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContractionOfVacuumCombinationsProof
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitLocalPlaceLocalModelsLinearSubspace
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsNeZeroOfIsVacO
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

noncomputable section

namespace GlobalTheory.FinWeilAlg

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

/- English proof (translation)
Use function extensionality and compare the values at `z`. Simplify using `only [heisO, Pi.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem heisO_smul' (w : WO S T) (c : ℂ) (f : WO S T → ℂ) : heisO ψ S T w (c • f) = c • heisO ψ S T w f := by
  funext z
  simp only [heisO, Pi.smul_apply, smul_eq_mul]
  ring

/- English proof (translation)
Use function extensionality and compare the values at `z`. Simplify using `only [heisO, Finset.sum_apply, Finset.mul_sum]`.
-/
theorem heisO_sum' {ι : Type} (s : Finset ι) (w : WO S T) (F : ι → WO S T → ℂ) :
    heisO ψ S T w (∑ i ∈ s, F i) = ∑ i ∈ s, heisO ψ S T w (F i) := by
  funext z
  simp only [heisO, Finset.sum_apply, Finset.mul_sum]

/- English proof (translation)
Unfold `symplOH`. Rewrite using `[← add_mul, ← map_add, show (1 / 2 : D.host.F) + 1 / 2 = 1 by norm_num, map_one, one_mul]`.
-/
theorem symplOH_add_self (x y : WO S T) : symplOH S T x y + symplOH S T x y = symplO S T x y := by
  unfold symplOH
  rw [← add_mul, ← map_add, show (1 / 2 : D.host.F) + 1 / 2 = 1 by norm_num, map_one, one_mul]

/- English proof (translation)
Establish `hlaws` using `GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ S T`. Establish `hneg : heisO ψ S T (-u) v = c • v`. Establish `e` using `GlobalTheory.FinPl.ContrOpProof.heisO_neg_cancel ψ (-u) v`. Rewrite `e` using `[neg_neg, hu, heisO_smul']`. Break down `hc1 with rfl | rfl` into its components or cases.

Simplify using `using e`. Establish `e2` using `congrArg (fun g => (-1 : ℂ) • g) e`. Simplify using `using e2`. Establish `e1` using `GlobalTheory.VacSchurFin.thetaInner_heisenberg hψ hc (hlaws.1 (-u) v hv) hφ u`. Rewrite `e1` using `[GlobalTheory.FinPl.ContrOpProof.heisO_neg_cancel]`.

Rewrite using `[GlobalTheory.RawLift.thetaInner_smul_right, e1, hneg, GlobalTheory.RawLift.thetaInner_smul_left]`. Apply the tactic sequence `rcases hc1 with rfl | rfl <;> simp`.
-/
theorem thetaInner_sign_smul_heisenberg (hψ : IsStdChar D ψ (-1)) {μ : Measure (WO S T)} {𝓕 : Set (WO S T)}
    (hc : IsCovolOne (ratL T S) μ 𝓕) {v φ : WO S T → ℂ} (hv : IsThetaFunO ψ S T v) (hφ : IsThetaFunO ψ S T φ)
    {u : WO S T} {c : ℂ} (hc1 : c = 1 ∨ c = -1) (hu : heisO ψ S T u v = c • v) :
    GlobalTheory.RawLift.thetaIP μ 𝓕 v (c • heisO ψ S T u φ) = GlobalTheory.RawLift.thetaIP μ 𝓕 v φ := by
  have hlaws := GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ S T
  have hneg : heisO ψ S T (-u) v = c • v := by
    have e := GlobalTheory.FinPl.ContrOpProof.heisO_neg_cancel ψ (-u) v
    rw [neg_neg, hu, heisO_smul'] at e
    rcases hc1 with rfl | rfl
    · simpa using e
    · have e2 := congrArg (fun g => (-1 : ℂ) • g) e
      simpa using e2
  have e1 := GlobalTheory.VacSchurFin.thetaInner_heisenberg hψ hc (hlaws.1 (-u) v hv) hφ u
  rw [GlobalTheory.FinPl.ContrOpProof.heisO_neg_cancel] at e1
  rw [GlobalTheory.RawLift.thetaInner_smul_right, e1, hneg, GlobalTheory.RawLift.thetaInner_smul_left]
  rcases hc1 with rfl | rfl <;> simp

/- English proof (translation)
Take `⟨U, hU, hfix⟩` from `hφ.level`. Take `⟨N, hN, hNU⟩` from `(GlobalTheory.LatLevel.level_of_generators D S T ΛS ΛT hS hT (GlobalTheory.LatFinGen.latO_finitely_generated D S T ΛS ΛT hS hT)).1 U hU`. Conclude with `⟨N, hN, fun u hu => hfix _ (hNU u hu) (GlobalTheory.VacUnique.latO_inf S T _ _ _ (AddSubgroup.nsmul_mem _ hu N))⟩`.
-/
theorem exists_level {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT)
    {φ : WO S T → ℂ} (hφ : IsThetaFunO ψ S T φ) :
    ∃ N : ℕ, 0 < N ∧ ∀ u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E))
      (fun _ => True), heisO ψ S T (N • u) φ = φ := by
  obtain ⟨U, hU, hfix⟩ := hφ.level
  obtain ⟨N, hN, hNU⟩ := (GlobalTheory.LatLevel.level_of_generators D S T ΛS ΛT hS hT
    (GlobalTheory.LatFinGen.latO_finitely_generated D S T ΛS ΛT hS hT)).1 U hU
  exact ⟨N, hN, fun u hu => hfix _ (hNU u hu)
    (GlobalTheory.VacUnique.latO_inf S T _ _ _ (AddSubgroup.nsmul_mem _ hu N))⟩

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Establish `hψ : IsStdChar D ψ (-1)` using `hv.1`. Establish `hlaws` using `GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ S T`. Establish `hvth` using `hv.2.theta`. Establish `hlat` using `hv.2.lat`. Establish `hv0 : ∀ a b : ℂ, a • v = b • v → a = b`.

Introduce `a b h`. Take `⟨w, hw⟩` from `GlobalTheory.SmoothVac.exists_ne_zero_of_isVacO hv`. Use `congrFun h w` as an intermediate fact. Simplify using `only [Pi.smul_apply, smul_eq_mul] at this`. Conclude with `mul_right_cancel₀ hw this`.

Take `⟨hdual, -, hsign⟩` from `GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T ΛS ΛT hψ hS hT`. Take `⟨N, hN, hNfix⟩` from `exists_level hS hT hφ`. Use `set Λ := latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) with hΛ`. Establish `hinf : ∀ u ∈ Λ, u.map (infPart D) = 0` using `fun u hu => GlobalTheory.VacUnique.latO_inf S T _ _ _ hu`. Establish `hε : ∀ u : Λ, ∃ ε : ℂ, (ε = 1 ∨ ε = -1) ∧ heisO ψ S T u v = ε • v` using `fun u => by`.

Take `⟨ε, h1, h2⟩` from `hsign v hlat u u.2`. Conclude with `⟨ε, h1, h2 v hlat⟩`. Use `choose ε hε1 hε2 using hε`. Establish `hψsq : ∀ u u' : Λ, ψ (symplOH S T u u') * ψ (symplOH S T u u') = 1` using `fun u u' => by`. Rewrite using `[← AddChar.map_add_eq_mul, symplOH_add_self]`.

Conclude with `(hdual u (hinf u u.2)).1 u.2 u' u'.2`. Establish `hcoef : ∀ u u' : Λ, ε u' * ε u = ψ (symplOH S T u u') * ε (u + u')` using `fun u u' => by`. Apply `hv0` to reduce the goal to its premises. Establish `e1 : heisO ψ S T u (heisO ψ S T u' v) = (ε u' * ε u) • v`. Rewrite using `[hε2 u', heisO_smul', hε2 u, smul_smul]`.

Establish `e2 : heisO ψ S T u (heisO ψ S T u' v) = (ψ (symplOH S T u u') * ε (u + u')) • v`. Rewrite using `[hlaws.2.1, ← AddSubgroup.coe_add, hε2 (u + u'), smul_smul]`. Rewrite using `[← e1, e2]`. Establish `hhom : ∀ (u u' : Λ) (f : WO S T → ℂ), ε u • heisO ψ S T u (ε u' • heisO ψ S T u' f) = ε (u + u') • heisO ψ S T ((u + u' : Λ) : WO S T) f` using `fun u u' f => by`. Rewrite using `[heisO_smul', hlaws.2.1, smul_smul, smul_smul, AddSubgroup.coe_add]`.

Use `congr 1`. Rewrite using `[show ε u * ε u' * ψ (symplOH S T u u') = (ε u' * ε u) * ψ (symplOH S T u u') by ring, hcoef]`. Take the linear combination `ε (u + u') * hψsq u u'`. Establish `hk : ∀ t : Λ, ε ((2 * N) • t) • heisO ψ S T (((2 * N) • t : Λ) : WO S T) φ = φ` using `fun t => by`. Establish `e1 : ε ((2 * N) • t) = 1`.

Apply `hv0` to reduce the goal to its premises. Rewrite using `[← hε2, one_smul, AddSubgroup.coe_nsmul, mul_smul]`. Conclude with `hlat.1 _ (AddSubgroup.nsmul_mem _ t.2 N)`. Rewrite using `[e1, one_smul, AddSubgroup.coe_nsmul, mul_comm, mul_smul]`. Conclude with `hNfix _ (AddSubgroup.nsmul_mem _ t.2 2)`.

Use `set K : AddSubgroup Λ := (nsmulAddMonoidHom (α := Λ) (2 * N)).range with hK`. Establish `hfinQ : Finite (Λ ⧸ K)`. Take `⟨R, hR, hRdec⟩` from `GlobalTheory.LatFinMod.latO_finite_mod D S T ΛS ΛT hS.1.fg hT.1.fg (fun _ => True) (2 * N) (by omega)`. Use `haveI : Finite R := hR.to_subtype`. Use `Finite.of_surjective (fun r : R => if h : (r : WO S T) ∈ Λ then (QuotientAddGroup.mk (⟨r, h⟩ : Λ) : Λ ⧸ K) else 0) ?_` and prove the remaining obligations.

Introduce `q`. Take `⟨t, rfl⟩` from `QuotientAddGroup.mk_surjective q`. Take `⟨r, hr, u, hu, e⟩` from `hRdec t t.2`. Establish `hrΛ : r ∈ Λ`. Establish `: r = (t : WO S T) - (2 * N) • u` using `by rw [e]; abel`.

Rewrite using `[this]`. Conclude with `sub_mem t.2 (AddSubgroup.nsmul_mem _ hu _)`. Use `⟨⟨r, hr⟩, ?_⟩` and prove the remaining obligations. Simplify using `only [dif_pos hrΛ]`. Rewrite using `[QuotientAddGroup.eq]`.

Conclude with `⟨⟨u, hu⟩, Subtype.ext (by simp [e])⟩`. Use `haveI : Fintype (Λ ⧸ K) := Fintype.ofFinite _`. Take `⟨g, hg⟩ : ∃ g : Λ ⧸ K → WO S T → ℂ, ∀ q, g q = ε q.out • heisO ψ S T (q.out : WO S T) φ` from `⟨_, fun _ => rfl⟩`. Establish `hshift : ∀ (u : Λ) (q : Λ ⧸ K), ε u • heisO ψ S T u (g q) = g (QuotientAddGroup.mk u + q)` using `fun u q => by`. Establish `hmem : -(QuotientAddGroup.mk u + q : Λ ⧸ K).out + (u + q.out) ∈ K`.

Rewrite using `[← QuotientAddGroup.eq, QuotientAddGroup.out_eq', QuotientAddGroup.mk_add, QuotientAddGroup.out_eq']`. Take `⟨t, ht⟩` from `hmem`. Establish `e : u + q.out = (QuotientAddGroup.mk u + q : Λ ⧸ K).out + (2 * N) • t`. Rewrite `ht` using `[nsmulAddMonoidHom_apply]`. Rewrite using `[ht]`.

Normalize the expressions using the abelian group laws. Rewrite using `[hg, hg, hhom, e, ← hhom _ ((2 * N) • t) φ, hk]`. Establish `hinv : ∀ u : Λ, ε u • heisO ψ S T u (∑ q, g q) = ∑ q, g q` using `fun u => by`. Rewrite using `[heisO_sum', Finset.smul_sum]`. Repeatedly rewrite using `[hshift u]`.

Conclude with `Equiv.sum_comp (Equiv.addLeft (QuotientAddGroup.mk u : Λ ⧸ K)) g`. Establish `hPlat : IsLatVac (heisO ψ S T) Λ (∑ q, g q)`. Use `⟨fun u hu => ?_, fun e he u hu hh => ?_⟩` and prove the remaining obligations. Establish `h1 : ε ⟨2 • u, AddSubgroup.nsmul_mem _ hu 2⟩ = 1`. Apply `hv0` to reduce the goal to its premises.

Rewrite using `[← hε2, one_smul]`. Conclude with `hlat.1 u hu`. Use `hinv ⟨2 • u, AddSubgroup.nsmul_mem _ hu 2⟩` as an intermediate fact. Rewrite `this` using `[h1, one_smul]`. Then use the resulting hypothesis. Establish `h1 : ε ⟨u, hu⟩ = 1`.

Apply `hv0` to reduce the goal to its premises. Rewrite using `[← hε2, one_smul]`. Conclude with `hlat.2 e he u hu hh`. Use `hinv ⟨u, hu⟩` as an intermediate fact. Rewrite `this` using `[h1, one_smul]`. Then use the resulting hypothesis.

Establish `hgth : ∀ q, IsThetaFunO ψ S T (g q)` using `fun q => by`. Rewrite using `[hg]`. Conclude with `GlobalTheory.LocMod.LinSpace.isThetaFunO_smul _ (hlaws.1 _ _ hφ)`. Establish `hzero : IsThetaFunO ψ S T (0 : WO S T → ℂ)`. Simplify using `using GlobalTheory.LocMod.LinSpace.isThetaFunO_smul (0 : ℂ) hφ`.

Establish `hPth : ∀ s : Finset (Λ ⧸ K), IsThetaFunO ψ S T (∑ q ∈ s, g q)` using `fun s => Finset.sum_induction _ _ (fun a b ha hb => GlobalTheory.LocMod.LinSpace.isThetaFunO_add ha hb) hzero (fun q _ => hgth q)`. Establish `hPf : ∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) (∑ q, g q)` using `fun τ => by`. Use `GlobalTheory.FockTranslate.isFockVacAt_sum D ψ θ S T hψ.1 hv.2.inf φ hφ τ _ (hφf τ) (Λ ⧸ K) Finset.univ (fun q => (q.out : WO S T)) (fun q => ε q.out) (fun q _ => hinf _ q.out.2)` as an intermediate fact. Simplify `this` using `only [← hg]`. Take `⟨a, ha⟩` from `GlobalTheory.LevelSeries.eq_smul_vacuum hψ hv.2.inf hCS hCT hS hT hv (hPth _) hPlat hPf`.

Establish `hIP : ∀ s : Finset (Λ ⧸ K), GlobalTheory.RawLift.thetaIP μ 𝓕 v (∑ q ∈ s, g q) = (s.card : ℂ) * GlobalTheory.RawLift.thetaIP μ 𝓕 v φ`. Introduce `s`. Use `Finset.induction_on s (by simp [GlobalTheory.RawLift.thetaIP]) (fun q s hq ih => ?_)` and prove the remaining obligations. Rewrite using `[Finset.sum_insert hq, GlobalTheory.RawLift.RealLowRed.thetaInner_add_right hψ hc.2.2 hvth (hgth q) (hPth s), ih, hg, thetaInner_sign_smul_heisenberg hψ hc hvth hφ (hε1 _) (hε2 _), Finset.card_insert_of_notMem hq]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Establish `e : (∑ q : Λ ⧸ K, ε q.out • heisO ψ S T (q.out : WO S T) φ) = ∑ q, g q` using `Finset.sum_congr rfl fun q _ => (hg q).symm`. Use `⟨Λ ⧸ K, inferInstance, fun q => ε q.out, fun q => q.out, a, Fintype.card_pos_iff.2 ⟨0⟩, fun q => hε1 _, fun q => q.out.2, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[e, ha]`. Rewrite using `[e, hIP, Finset.card_univ]`.
-/
theorem average {θ : InfFam D} {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ}
    {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    {v : WO S T → ℂ} (hv : IsVacO ψ θ S T sS sT ΛS ΛT v) (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT)
    (hCS : ∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) (hCT : ∀ τ, IsCartanInv (gramAt D T τ) (sT τ))
    {μ : Measure (WO S T)} {𝓕 : Set (WO S T)} (hc : IsCovolOne (ratL T S) μ 𝓕)
    {φ : WO S T → ℂ} (hφ : IsThetaFunO ψ S T φ)
    (hφf : ∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) φ) :
    ∃ (ι : Type) (_ : Fintype ι) (c : ι → ℂ) (u : ι → WO S T) (a : ℂ), 0 < Fintype.card ι ∧
      (∀ i, c i = 1 ∨ c i = -1) ∧
      (∀ i, u i ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) ∧
      ∑ i, c i • heisO ψ S T (u i) φ = a • v ∧
      GlobalTheory.RawLift.thetaIP μ 𝓕 v (∑ i, c i • heisO ψ S T (u i) φ) =
        (Fintype.card ι : ℂ) * GlobalTheory.RawLift.thetaIP μ 𝓕 v φ := by
  classical
  have hψ : IsStdChar D ψ (-1) := hv.1
  have hlaws := GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ S T
  have hvth := hv.2.theta
  have hlat := hv.2.lat
  have hv0 : ∀ a b : ℂ, a • v = b • v → a = b := by
    intro a b h
    obtain ⟨w, hw⟩ := GlobalTheory.SmoothVac.exists_ne_zero_of_isVacO hv
    have := congrFun h w
    simp only [Pi.smul_apply, smul_eq_mul] at this
    exact mul_right_cancel₀ hw this
  obtain ⟨hdual, -, hsign⟩ := GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T ΛS ΛT hψ hS hT
  obtain ⟨N, hN, hNfix⟩ := exists_level hS hT hφ
  set Λ := latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) with hΛ
  have hinf : ∀ u ∈ Λ, u.map (infPart D) = 0 := fun u hu => GlobalTheory.VacUnique.latO_inf S T _ _ _ hu
  have hε : ∀ u : Λ, ∃ ε : ℂ, (ε = 1 ∨ ε = -1) ∧ heisO ψ S T u v = ε • v := fun u => by
    obtain ⟨ε, h1, h2⟩ := hsign v hlat u u.2
    exact ⟨ε, h1, h2 v hlat⟩
  choose ε hε1 hε2 using hε
  have hψsq : ∀ u u' : Λ, ψ (symplOH S T u u') * ψ (symplOH S T u u') = 1 := fun u u' => by
    rw [← AddChar.map_add_eq_mul, symplOH_add_self]
    exact (hdual u (hinf u u.2)).1 u.2 u' u'.2
  have hcoef : ∀ u u' : Λ, ε u' * ε u = ψ (symplOH S T u u') * ε (u + u') := fun u u' => by
    apply hv0
    have e1 : heisO ψ S T u (heisO ψ S T u' v) = (ε u' * ε u) • v := by
      rw [hε2 u', heisO_smul', hε2 u, smul_smul]
    have e2 : heisO ψ S T u (heisO ψ S T u' v) = (ψ (symplOH S T u u') * ε (u + u')) • v := by
      rw [hlaws.2.1, ← AddSubgroup.coe_add, hε2 (u + u'), smul_smul]
    rw [← e1, e2]
  have hhom : ∀ (u u' : Λ) (f : WO S T → ℂ), ε u • heisO ψ S T u (ε u' • heisO ψ S T u' f) =
      ε (u + u') • heisO ψ S T ((u + u' : Λ) : WO S T) f := fun u u' f => by
    rw [heisO_smul', hlaws.2.1, smul_smul, smul_smul, AddSubgroup.coe_add]
    congr 1
    rw [show ε u * ε u' * ψ (symplOH S T u u') = (ε u' * ε u) * ψ (symplOH S T u u') by ring, hcoef]
    linear_combination ε (u + u') * hψsq u u'
  have hk : ∀ t : Λ, ε ((2 * N) • t) • heisO ψ S T (((2 * N) • t : Λ) : WO S T) φ = φ := fun t => by
    have e1 : ε ((2 * N) • t) = 1 := by
      apply hv0
      rw [← hε2, one_smul, AddSubgroup.coe_nsmul, mul_smul]
      exact hlat.1 _ (AddSubgroup.nsmul_mem _ t.2 N)
    rw [e1, one_smul, AddSubgroup.coe_nsmul, mul_comm, mul_smul]
    exact hNfix _ (AddSubgroup.nsmul_mem _ t.2 2)
  set K : AddSubgroup Λ := (nsmulAddMonoidHom (α := Λ) (2 * N)).range with hK
  have hfinQ : Finite (Λ ⧸ K) := by
    obtain ⟨R, hR, hRdec⟩ := GlobalTheory.LatFinMod.latO_finite_mod D S T ΛS ΛT hS.1.fg hT.1.fg (fun _ => True) (2 * N)
      (by omega)
    haveI : Finite R := hR.to_subtype
    refine Finite.of_surjective (fun r : R => if h : (r : WO S T) ∈ Λ then
      (QuotientAddGroup.mk (⟨r, h⟩ : Λ) : Λ ⧸ K) else 0) ?_
    intro q
    obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective q
    obtain ⟨r, hr, u, hu, e⟩ := hRdec t t.2
    have hrΛ : r ∈ Λ := by
      have : r = (t : WO S T) - (2 * N) • u := by rw [e]; abel
      rw [this]; exact sub_mem t.2 (AddSubgroup.nsmul_mem _ hu _)
    refine ⟨⟨r, hr⟩, ?_⟩
    simp only [dif_pos hrΛ]
    rw [QuotientAddGroup.eq]
    exact ⟨⟨u, hu⟩, Subtype.ext (by simp [e])⟩
  haveI : Fintype (Λ ⧸ K) := Fintype.ofFinite _
  obtain ⟨g, hg⟩ : ∃ g : Λ ⧸ K → WO S T → ℂ, ∀ q, g q = ε q.out • heisO ψ S T (q.out : WO S T) φ :=
    ⟨_, fun _ => rfl⟩
  have hshift : ∀ (u : Λ) (q : Λ ⧸ K), ε u • heisO ψ S T u (g q) = g (QuotientAddGroup.mk u + q) := fun u q => by
    have hmem : -(QuotientAddGroup.mk u + q : Λ ⧸ K).out + (u + q.out) ∈ K := by
      rw [← QuotientAddGroup.eq, QuotientAddGroup.out_eq', QuotientAddGroup.mk_add, QuotientAddGroup.out_eq']
    obtain ⟨t, ht⟩ := hmem
    have e : u + q.out = (QuotientAddGroup.mk u + q : Λ ⧸ K).out + (2 * N) • t := by
      rw [nsmulAddMonoidHom_apply] at ht
      rw [ht]; abel
    rw [hg, hg, hhom, e, ← hhom _ ((2 * N) • t) φ, hk]
  have hinv : ∀ u : Λ, ε u • heisO ψ S T u (∑ q, g q) = ∑ q, g q := fun u => by
    rw [heisO_sum', Finset.smul_sum]
    simp_rw [hshift u]
    exact Equiv.sum_comp (Equiv.addLeft (QuotientAddGroup.mk u : Λ ⧸ K)) g
  have hPlat : IsLatVac (heisO ψ S T) Λ (∑ q, g q) := by
    refine ⟨fun u hu => ?_, fun e he u hu hh => ?_⟩
    · have h1 : ε ⟨2 • u, AddSubgroup.nsmul_mem _ hu 2⟩ = 1 := by
        apply hv0; rw [← hε2, one_smul]; exact hlat.1 u hu
      have := hinv ⟨2 • u, AddSubgroup.nsmul_mem _ hu 2⟩
      rwa [h1, one_smul] at this
    · have h1 : ε ⟨u, hu⟩ = 1 := by
        apply hv0; rw [← hε2, one_smul]; exact hlat.2 e he u hu hh
      have := hinv ⟨u, hu⟩
      rwa [h1, one_smul] at this
  have hgth : ∀ q, IsThetaFunO ψ S T (g q) := fun q => by
    rw [hg]; exact GlobalTheory.LocMod.LinSpace.isThetaFunO_smul _ (hlaws.1 _ _ hφ)
  have hzero : IsThetaFunO ψ S T (0 : WO S T → ℂ) := by
    simpa using GlobalTheory.LocMod.LinSpace.isThetaFunO_smul (0 : ℂ) hφ
  have hPth : ∀ s : Finset (Λ ⧸ K), IsThetaFunO ψ S T (∑ q ∈ s, g q) := fun s =>
    Finset.sum_induction _ _ (fun a b ha hb => GlobalTheory.LocMod.LinSpace.isThetaFunO_add ha hb) hzero (fun q _ => hgth q)
  have hPf : ∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) (∑ q, g q) := fun τ => by
    have := GlobalTheory.FockTranslate.isFockVacAt_sum D ψ θ S T hψ.1 hv.2.inf φ hφ τ _ (hφf τ) (Λ ⧸ K) Finset.univ
      (fun q => (q.out : WO S T)) (fun q => ε q.out) (fun q _ => hinf _ q.out.2)
    simpa only [← hg] using this
  obtain ⟨a, ha⟩ := GlobalTheory.LevelSeries.eq_smul_vacuum hψ hv.2.inf hCS hCT hS hT hv (hPth _) hPlat hPf
  have hIP : ∀ s : Finset (Λ ⧸ K), GlobalTheory.RawLift.thetaIP μ 𝓕 v (∑ q ∈ s, g q) =
      (s.card : ℂ) * GlobalTheory.RawLift.thetaIP μ 𝓕 v φ := by
    intro s
    refine Finset.induction_on s (by simp [GlobalTheory.RawLift.thetaIP]) (fun q s hq ih => ?_)
    rw [Finset.sum_insert hq, GlobalTheory.RawLift.RealLowRed.thetaInner_add_right hψ hc.2.2 hvth (hgth q) (hPth s), ih, hg,
      thetaInner_sign_smul_heisenberg hψ hc hvth hφ (hε1 _) (hε2 _), Finset.card_insert_of_notMem hq]
    push_cast; ring
  have e : (∑ q : Λ ⧸ K, ε q.out • heisO ψ S T (q.out : WO S T) φ) = ∑ q, g q :=
    Finset.sum_congr rfl fun q _ => (hg q).symm
  refine ⟨Λ ⧸ K, inferInstance, fun q => ε q.out, fun q => q.out, a, Fintype.card_pos_iff.2 ⟨0⟩,
    fun q => hε1 _, fun q => q.out.2, ?_, ?_⟩
  · rw [e, ha]
  · rw [e, hIP, Finset.card_univ]

/- English proof (translation)
The claim follows from `Finset.sum_induction _ _ (fun _ _ ha hb => ha.add hb) GlobalTheory.MovedAlg.IsAlgComb.zero h`.
-/
theorem isAlgComb_finset {f₀ : WO S T → ℂ} {ι : Type} (s : Finset ι) (F : ι → WO S T → ℂ)
    (h : ∀ i ∈ s, GlobalTheory.MovedAlg.IsAlgComb ψ S T f₀ (F i)) : GlobalTheory.MovedAlg.IsAlgComb ψ S T f₀ (∑ i ∈ s, F i) :=
  Finset.sum_induction _ _ (fun _ _ ha hb => ha.add hb) GlobalTheory.MovedAlg.IsAlgComb.zero h

/- English proof (translation)
Assemble the required witnesses or components as `⟨1, fun _ => 1, fun _ => 0, fun _ => isAlgebraic_one, fun _ => Matrix.map_zero _ (map_zero _), by simp [GlobalTheory.SplitScalar.heisO_zero]⟩`.
-/
theorem isAlgComb_self (f₀ : WO S T → ℂ) : GlobalTheory.MovedAlg.IsAlgComb ψ S T f₀ f₀ :=
  ⟨1, fun _ => 1, fun _ => 0, fun _ => isAlgebraic_one, fun _ => Matrix.map_zero _ (map_zero _), by
    simp [GlobalTheory.SplitScalar.heisO_zero]⟩

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `D ψ θ S T sS sT ΛS ΛT v χS χT om hv hS hT hCS hCT hom x hx h hh`. Distinguish the cases in `hG : om (x, h) v = 0`. Conclude with `⟨0, 0, GlobalTheory.MovedAlg.IsAlgComb.zero, by rw [hG, zero_smul]⟩`. Establish `hψ : IsStdChar D ψ (-1)` using `hv.1`. Establish `hθ` using `hv.2.inf`.

Establish `hvth` using `hv.2.theta`. Establish `hvf` using `hv.2.fock`. Establish `hlaws` using `GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ S T`. Take `⟨⟨p, hp⟩, -⟩` from `hv.2.norm`. Take `⟨hGth, hGf⟩` from `GlobalTheory.FockRealMove.om_fin_fockVac D ψ θ S T χS χT om hom hθ sS sT v hvth hvf x hx h hh`.

Establish `hv0 : v ≠ 0`. Take `⟨w, hw⟩` from `GlobalTheory.SmoothVac.exists_ne_zero_of_isVacO hv`. Introduce `h0`. Conclude with `hw (by rw [h0]; rfl)`. Choose the witnesses or unpack the hypotheses as in `⟨w, hw, hne⟩ : ∃ w : WO S T, w.map (infPart D) = 0 ∧ GlobalTheory.RawLift.thetaIP p.1 p.2 (om (x, h) v) (heisO ψ S T w v) ≠ 0 := by`.

Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Break down `GlobalTheory.VacSchurFin.irr_vac D ψ θ S T hψ hθ sS sT hCS hCT p.1 p.2 hp _ _ hGth hvth hGf hvf hcon with h1 | h1` into its components or cases. Use `exacts [hG h1, hv0 h1]`. Establish `hwth` using `hlaws.1 w v hvth`.

Establish `hwf` using `GlobalTheory.VacSchurFin.vac_heisO_fin hθ hw hvf`. Take `⟨hφth, hφf⟩` from `GlobalTheory.FockRealMove.om_fin_fockVac D ψ θ S T χS χT om hom hθ sS sT _ hwth hwf x⁻¹ (inv_mem hx) h⁻¹ (inv_mem hh)`. Establish `hback : om (x, h) (om (x⁻¹, h⁻¹) (heisO ψ S T w v)) = heisO ψ S T w v`. Rewrite using `[← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_inv_cancel, mul_inv_cancel, ← Prod.one_eq_mk, map_one, Module.End.one_apply]`. Establish `hip : GlobalTheory.RawLift.thetaIP p.1 p.2 v (om (x⁻¹, h⁻¹) (heisO ψ S T w v)) ≠ 0`.

Rewrite using `[← GlobalTheory.WeilPairing.thetaInner_weilRep D ψ S T χS χT om p.1 p.2 hom hp (x, h) _ _ hvth hφth, hback]`. Conclude with `hne`. Take `⟨ι, _, c, u, a, hcard, hc, hu, hsum, hIP⟩` from `average hv hS hT hCS hCT hp hφth hφf`. Establish `ha : a ≠ 0`. Introduce and unpack `rfl`.

Rewrite `hIP` using `[hsum, GlobalTheory.RawLift.thetaInner_smul_right, zero_mul, eq_comm, mul_eq_zero]`. Break down `hIP with h1 | h1` into its components or cases. Conclude with `absurd h1 (by exact_mod_cast hcard.ne')`. Conclude with `hip h1`. Establish `hψalg : ∀ u v : WO S T, u.map (infPart D) = 0 → v.map (infPart D) = 0 → IsAlgebraic ℚ (ψ (symplOH S T u v))` using `fun u v hu hv' => mem_algebraicClosure_iff.1 (GlobalTheory.BotFourier.psiH_mem hψ hS hT hu hv')`.

Establish `hF : om (x, h) (∑ i, c i • heisO ψ S T (u i) (om (x⁻¹, h⁻¹) (heisO ψ S T w v))) = ∑ i, c i • heisO ψ S T (actO S T x h (u i)) (heisO ψ S T w v)`. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, hom.om_heis x h (u i) _ hφth, hback]`. Use `⟨a⁻¹, ∑ i, c i • heisO ψ S T (actO S T x h (u i)) (heisO ψ S T w v), ?_, ?_⟩` and prove the remaining obligations.

Use `isAlgComb_finset _ _ fun i _ => ?_` and prove the remaining obligations. Use `GlobalTheory.MovedAlg.IsAlgComb.smul ?_ (GlobalTheory.MovedAlg.IsAlgComb.Heisenberg₂ hψalg (GlobalTheory.FinApprox.actO_fin _ _ (GlobalTheory.VacUnique.latO_inf S T _ _ _ (hu i))) (GlobalTheory.MovedAlg.IsAlgComb.Heisenberg₂ hψalg hw (isAlgComb_self v)))` and prove the remaining obligations. Apply the tactic sequence `rcases hc i with e | e <;> rw [e]`. Conclude with `isAlgebraic_one`. Conclude with `isAlgebraic_one.neg`.

Rewrite using `[← hF, hsum, map_smul, smul_smul, inv_mul_cancel₀ ha, one_smul]`.
-/
theorem om_vac_algComb : ∀ {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}
    {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} {v : WO S T → ℂ}
    {χS χT : (Formalism.L2.Theta.AE D)ˣ →* Circle} {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}, IsVacO ψ θ S T sS sT (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) v → IsSelfDualC S ΛS → IsSelfDualC T ΛT →
    (∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) → (∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) → IsWeilDatumO ψ S T χS χT om →
    ∀ x ∈ GfC S, ∀ h ∈ GfC T, ∃ (κ : ℂ) (F : WO S T → ℂ), GlobalTheory.MovedAlg.IsAlgComb ψ S T v F ∧ om (x, h) v = κ • F := by
  intro D ψ θ S T sS sT ΛS ΛT v χS χT om hv hS hT hCS hCT hom x hx h hh
  by_cases hG : om (x, h) v = 0
  · exact ⟨0, 0, GlobalTheory.MovedAlg.IsAlgComb.zero, by rw [hG, zero_smul]⟩
  have hψ : IsStdChar D ψ (-1) := hv.1
  have hθ := hv.2.inf
  have hvth := hv.2.theta
  have hvf := hv.2.fock
  have hlaws := GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ S T
  obtain ⟨⟨p, hp⟩, -⟩ := hv.2.norm
  obtain ⟨hGth, hGf⟩ := GlobalTheory.FockRealMove.om_fin_fockVac D ψ θ S T χS χT om hom hθ sS sT v hvth hvf x hx h hh
  have hv0 : v ≠ 0 := by
    obtain ⟨w, hw⟩ := GlobalTheory.SmoothVac.exists_ne_zero_of_isVacO hv
    intro h0
    exact hw (by rw [h0]; rfl)
  obtain ⟨w, hw, hne⟩ : ∃ w : WO S T, w.map (infPart D) = 0 ∧
      GlobalTheory.RawLift.thetaIP p.1 p.2 (om (x, h) v) (heisO ψ S T w v) ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    rcases GlobalTheory.VacSchurFin.irr_vac D ψ θ S T hψ hθ sS sT hCS hCT p.1 p.2 hp _ _ hGth hvth hGf hvf hcon with h1 | h1
    exacts [hG h1, hv0 h1]
  have hwth := hlaws.1 w v hvth
  have hwf := GlobalTheory.VacSchurFin.vac_heisO_fin hθ hw hvf
  obtain ⟨hφth, hφf⟩ := GlobalTheory.FockRealMove.om_fin_fockVac D ψ θ S T χS χT om hom hθ sS sT _ hwth hwf x⁻¹ (inv_mem hx)
    h⁻¹ (inv_mem hh)
  have hback : om (x, h) (om (x⁻¹, h⁻¹) (heisO ψ S T w v)) = heisO ψ S T w v := by
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_inv_cancel, mul_inv_cancel, ← Prod.one_eq_mk, map_one,
      Module.End.one_apply]
  have hip : GlobalTheory.RawLift.thetaIP p.1 p.2 v (om (x⁻¹, h⁻¹) (heisO ψ S T w v)) ≠ 0 := by
    rw [← GlobalTheory.WeilPairing.thetaInner_weilRep D ψ S T χS χT om p.1 p.2 hom hp (x, h) _ _ hvth hφth, hback]
    exact hne
  obtain ⟨ι, _, c, u, a, hcard, hc, hu, hsum, hIP⟩ := average hv hS hT hCS hCT hp hφth hφf
  have ha : a ≠ 0 := by
    rintro rfl
    rw [hsum, GlobalTheory.RawLift.thetaInner_smul_right, zero_mul, eq_comm, mul_eq_zero] at hIP
    rcases hIP with h1 | h1
    · exact absurd h1 (by exact_mod_cast hcard.ne')
    · exact hip h1
  have hψalg : ∀ u v : WO S T, u.map (infPart D) = 0 → v.map (infPart D) = 0 →
      IsAlgebraic ℚ (ψ (symplOH S T u v)) :=
    fun u v hu hv' => mem_algebraicClosure_iff.1 (GlobalTheory.BotFourier.psiH_mem hψ hS hT hu hv')
  have hF : om (x, h) (∑ i, c i • heisO ψ S T (u i) (om (x⁻¹, h⁻¹) (heisO ψ S T w v))) =
      ∑ i, c i • heisO ψ S T (actO S T x h (u i)) (heisO ψ S T w v) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, hom.om_heis x h (u i) _ hφth, hback]
  refine ⟨a⁻¹, ∑ i, c i • heisO ψ S T (actO S T x h (u i)) (heisO ψ S T w v), ?_, ?_⟩
  · refine isAlgComb_finset _ _ fun i _ => ?_
    refine GlobalTheory.MovedAlg.IsAlgComb.smul ?_ (GlobalTheory.MovedAlg.IsAlgComb.Heisenberg₂ hψalg
      (GlobalTheory.FinApprox.actO_fin _ _ (GlobalTheory.VacUnique.latO_inf S T _ _ _ (hu i)))
      (GlobalTheory.MovedAlg.IsAlgComb.Heisenberg₂ hψalg hw (isAlgComb_self v)))
    rcases hc i with e | e <;> rw [e]
    · exact isAlgebraic_one
    · exact isAlgebraic_one.neg
  · rw [← hF, hsum, map_smul, smul_smul, inv_mul_cancel₀ ha, one_smul]

end GlobalTheory.FinWeilAlg
