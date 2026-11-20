import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ExistsSmallSpherical
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicValuationThetaKernelJetBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HighestWeightBelow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VwNatCastNonneg
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JetKapIff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.KerFockMovedReal
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfOfMulFinOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsThetaAtOfVac
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PtYAndItYOfPair
import Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.RealRow
import Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.AttExp
import Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.RatReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Use `show (N.frC X τ)ᴴ * (G.V X).gram.map (tauE D τ) * N.frC X τ = 1`. Establish `h` using `congrArg (·.map (tauE D τ)) (N.fr_on X hX)`. Simplify using `only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] at h`. Rewrite using `[← h, Std.frC]`. Use `congr 2`.

Use extensionality with `a b`. Conclude with `(D.sp.cm.cmUnram.2.1 (tauE D τ) _).symm`.
-/
private theorem frC_on' {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GlobalTheory.ChiGrid.GridData L sc} {U₀ : Set T}
    (N : Std G U₀) (X : Node) (hX : DefNode D.R.m X) (τ : D.what₂.Tau) :
    (N.frC X τ)ᴴ * gramAt D (G.V X) τ * N.frC X τ = 1 := by
  show (N.frC X τ)ᴴ * (G.V X).gram.map (tauE D τ) * N.frC X τ = 1
  have h := congrArg (·.map (tauE D τ)) (N.fr_on X hX)
  simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] at h
  rw [← h, Std.frC]
  congr 2
  ext a b
  exact (D.sp.cm.cmUnram.2.1 (tauE D τ) _).symm

private noncomputable def kerLin {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GlobalTheory.ChiGrid.GridData L sc}
    (W : G.Weil) (B : VertexFrames G) (p : GlobalTheory.ChiGrid.Pair T) (f : WO (G.pS p) (G.pT p) → ℂ)
    (g : GA D (G.V p.small)) (h : GA D (G.V p.big)) : PolF D (G.pT p).rank (G.pS p).rank →ₗ[ℂ] ℂ :=
  LinearMap.proj (0 : WO (G.pS p) (G.pT p)) ∘ₗ W.om p (G.toPair p g h) ∘ₗ fockIn W B p f

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem kerLin_apply {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GlobalTheory.ChiGrid.GridData L sc}
    (W : G.Weil) (B : VertexFrames G) (p : GlobalTheory.ChiGrid.Pair T) (f : WO (G.pS p) (G.pT p) → ℂ)
    (g : GA D (G.V p.small)) (h : GA D (G.V p.big)) (Q : PolF D (G.pT p).rank (G.pS p).rank) :
    kerLin W B p f g h Q = W.ker p (fockIn W B p f Q) g h := rfl

/- English proof (translation)
Take `⟨x, hx, e⟩` from `Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hγ)`. Use `Subgroup.mem_subgroupOf.2 (Subgroup.mem_map.2 ⟨x, ?_, e⟩)` and prove the remaining obligations. Establish `hx' : Formalism.UG.cT _ (x : Matrix _ _ _) * V.gram * (x : Matrix _ _ _) = V.gram` using `hx`. Use `show Formalism.UG.cT _ (x : Matrix _ _ _) * (-V.gram) * (x : Matrix _ _ _) = -V.gram`. Rewrite using `[Matrix.mul_neg, Matrix.neg_mul, hx']`.
-/
private theorem negGA_GQ {D : D7} (V : HSp D) {γ : GA D V} (hγ : γ ∈ GQ V) : negGA V γ ∈ GQ (negSp V) := by
  obtain ⟨x, hx, e⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hγ)
  refine Subgroup.mem_subgroupOf.2 (Subgroup.mem_map.2 ⟨x, ?_, e⟩)
  have hx' : Formalism.UG.cT _ (x : Matrix _ _ _) * V.gram * (x : Matrix _ _ _) = V.gram := hx
  show Formalism.UG.cT _ (x : Matrix _ _ _) * (-V.gram) * (x : Matrix _ _ _) = -V.gram
  rw [Matrix.mul_neg, Matrix.neg_mul, hx']

/- English proof (translation)
Establish `hw` using `W.om_is p hp`. Establish `h12 : (G.toPair p γ γ').1 ∈ GQ (G.pS p) ∧ (G.toPair p γ γ').2 ∈ GQ (G.pT p)`. Consider the cases of `p with`. Consider the case `chi i j => exact ⟨negGA_GQ _ hγ', hγ⟩`. Consider the case `mu t i j => exact ⟨hγ, hγ'⟩`.

Consider the case `core i => exact ⟨negGA_GQ _ hγ', hγ⟩`. Consider the case `top t j => exact ⟨hγ, hγ'⟩`. Rewrite using `[GlobalTheory.FockReal.ker_mul]`. Conclude with `hw.om_aut _ h12.1 _ h12.2 _ (hw.om_pres (G.toPair p g h) f hf)`.
-/
private theorem ker_rat {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GlobalTheory.ChiGrid.GridData L sc}
    (W : G.Weil) (p : GlobalTheory.ChiGrid.Pair T) (hp : p.InRange D.R.m) (f : WO (G.pS p) (G.pT p) → ℂ)
    (hf : IsThetaFunO W.ψ (G.pS p) (G.pT p) f) (γ : GA D (G.V p.small)) (hγ : γ ∈ GQ (G.V p.small))
    (γ' : GA D (G.V p.big)) (hγ' : γ' ∈ GQ (G.V p.big)) (g : GA D (G.V p.small)) (h : GA D (G.V p.big)) :
    W.ker p f (γ * g) (γ' * h) = W.ker p f g h := by
  have hw := W.om_is p hp
  have h12 : (G.toPair p γ γ').1 ∈ GQ (G.pS p) ∧ (G.toPair p γ γ').2 ∈ GQ (G.pT p) := by
    cases p with
    | chi i j => exact ⟨negGA_GQ _ hγ', hγ⟩
    | mu t i j => exact ⟨hγ, hγ'⟩
    | core i => exact ⟨negGA_GQ _ hγ', hγ⟩
    | top t j => exact ⟨hγ, hγ'⟩
  rw [GlobalTheory.FockReal.ker_mul]
  exact hw.om_aut _ h12.1 _ h12.2 _ (hw.om_pres (G.toPair p g h) f hf)

/- English proof (translation)
Introduce `D T L sc G W U₀ N Z μ₀ hL t i hi d x r y r' U U' hU hU'`. Establish `hp : DefPair D.R.m (GlobalTheory.ChiGrid.Pair.chi i D.R.m : GlobalTheory.ChiGrid.Pair T)` using `⟨by omega, rfl⟩`. Establish `hR : (GlobalTheory.ChiGrid.Pair.chi i D.R.m : GlobalTheory.ChiGrid.Pair T).InRange D.R.m` using `⟨by omega, le_rfl⟩`. Take `⟨a, b, e₁, e₂, ha, hb, he₁, he₂⟩` from `UpperTheory.WildA.expEx (G := G) hL _ hp`. Take `⟨γ, hγ, k, hk, hm, hρ⟩` from `UpperTheory.WildA.ratReal W N.fr _ r U hU`.

Take `⟨γ', hγ', k', hk', hm', hρ'⟩` from `UpperTheory.WildA.ratReal W N.fr _ r' U' hU'`. Take `⟨hth, hvac⟩` from `GlobalTheory.T.gridFiniteDatumVector_theta_fockVacuum W Z hp d (Z.hasVec_of_defPair hL hp d)`. Establish `hrow` using `UpperTheory.WildA.realRow (W := W) N hL i hi a b ha hb e₁ e₂ he₁ he₂ (kerLin W N.frC _ (Z.vec d) ((x * N.u _ : FinPt G _) : GA D _) ((y * N.u _ : FinPt G _) : GA D _)) k hk k' hk'`. Establish `htab : jetTab W N.frC _ (Z.vec d) (r * x * N.u _) (r' * y * N.u _) = fun m => GlobalTheory.FockReal.realChar W (GlobalTheory.ChiGrid.Pair.chi i D.R.m : GlobalTheory.ChiGrid.Pair T) e₁ e₂ k k' * kerLin W N.frC _ (Z.vec d) ((x * N.u _ : FinPt G _) : GA D _) ((y * N.u _ : FinPt G _) …`. Use function extensionality and compare the values at `m`.

Rewrite using `[jetTab, kerFin, mul_assoc r, mul_assoc r', hm, hm', kerLin_apply, ker_rat W _ hR (fockIn W N.frC _ (Z.vec d) _) (GlobalTheory.Chain.InnerSteps.theta_pureTensorO W.ψ_std W.θ_is _ _ _ _ hth _) γ hγ γ' hγ']`. Conclude with `GlobalTheory.FockReal.ker_fockIn_real hL W N.frC hp (frC_on' N) a b ha hb e₁ e₂ he₁ he₂ _ hth hvac k hk k' hk' _ _ _`. Establish `h1 : GlobalTheory.DefStep.realAct W.θ N.fr _ k ∘ₗ GlobalTheory.DefStep.realAct W.θ N.fr _ k⁻¹ = LinearMap.id`. Rewrite using `[← Module.End.mul_eq_comp, ← map_mul, mul_inv_cancel, map_one]`. Both sides reduce to the same expression.

Rewrite using `[Normal.kkMap, Normal.kkMap, fockComp, fockComp, htab, hrow, ← hρ, ← hρ', LinearMap.smul_comp, LinearMap.comp_smul, LinearMap.comp_assoc, LinearMap.comp_assoc, h1, LinearMap.comp_id]`. Both sides reduce to the same expression.
-/
theorem UpperTheory.WildA.moveRow :
    ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GlobalTheory.ChiGrid.GridData L sc} {W : G.Weil} {U₀ : Set T} {N : Std G U₀} (Z : Normal W N) {μ₀ : T}, L.Is μ₀ → ∀ (t : T) (i : ℕ), i + 1 ≤ D.R.m →
      ∀ (d : FinDatum G t (GlobalTheory.ChiGrid.Pair.chi i D.R.m : GlobalTheory.ChiGrid.Pair T)) (x r : FinPt G ((GlobalTheory.ChiGrid.Pair.chi i D.R.m : GlobalTheory.ChiGrid.Pair T)).small) (y r' : FinPt G ((GlobalTheory.ChiGrid.Pair.chi i D.R.m : GlobalTheory.ChiGrid.Pair T)).big)
        (U : Matrix.unitaryGroup (Fin (G.V ((GlobalTheory.ChiGrid.Pair.chi i D.R.m : GlobalTheory.ChiGrid.Pair T)).small).rank) D.host.E) (U' : Matrix.unitaryGroup (Fin (G.V ((GlobalTheory.ChiGrid.Pair.chi i D.R.m : GlobalTheory.ChiGrid.Pair T)).big).rank) D.host.E),
        GlobalTheory.RatMoveJets.RatCoord _ (N.fr ((GlobalTheory.ChiGrid.Pair.chi i D.R.m : GlobalTheory.ChiGrid.Pair T)).small) r U → GlobalTheory.RatMoveJets.RatCoord _ (N.fr ((GlobalTheory.ChiGrid.Pair.chi i D.R.m : GlobalTheory.ChiGrid.Pair T)).big) r' U' →
        Z.kkMap 1 d (r * x) (r' * y) ∘ₗ rhoVr (tauE D) (wt G ((GlobalTheory.ChiGrid.Pair.chi i D.R.m : GlobalTheory.ChiGrid.Pair T)).small) (Unitary.toUnits U) =
          rhoVr (tauE D) (wt G ((GlobalTheory.ChiGrid.Pair.chi i D.R.m : GlobalTheory.ChiGrid.Pair T)).big) (Unitary.toUnits U') ∘ₗ Z.kkMap 1 d x y := by
  intro D T L sc G W U₀ N Z μ₀ hL t i hi d x r y r' U U' hU hU'
  have hp : DefPair D.R.m (GlobalTheory.ChiGrid.Pair.chi i D.R.m : GlobalTheory.ChiGrid.Pair T) := ⟨by omega, rfl⟩
  have hR : (GlobalTheory.ChiGrid.Pair.chi i D.R.m : GlobalTheory.ChiGrid.Pair T).InRange D.R.m := ⟨by omega, le_rfl⟩
  obtain ⟨a, b, e₁, e₂, ha, hb, he₁, he₂⟩ := UpperTheory.WildA.expEx (G := G) hL _ hp
  obtain ⟨γ, hγ, k, hk, hm, hρ⟩ := UpperTheory.WildA.ratReal W N.fr _ r U hU
  obtain ⟨γ', hγ', k', hk', hm', hρ'⟩ := UpperTheory.WildA.ratReal W N.fr _ r' U' hU'
  obtain ⟨hth, hvac⟩ := GlobalTheory.T.gridFiniteDatumVector_theta_fockVacuum W Z hp d (Z.hasVec_of_defPair hL hp d)
  have hrow := UpperTheory.WildA.realRow (W := W) N hL i hi a b ha hb e₁ e₂ he₁ he₂
    (kerLin W N.frC _ (Z.vec d) ((x * N.u _ : FinPt G _) : GA D _) ((y * N.u _ : FinPt G _) : GA D _)) k hk k' hk'
  have htab : jetTab W N.frC _ (Z.vec d) (r * x * N.u _) (r' * y * N.u _) = fun m =>
      GlobalTheory.FockReal.realChar W (GlobalTheory.ChiGrid.Pair.chi i D.R.m : GlobalTheory.ChiGrid.Pair T) e₁ e₂ k k' *
        kerLin W N.frC _ (Z.vec d) ((x * N.u _ : FinPt G _) : GA D _) ((y * N.u _ : FinPt G _) : GA D _)
          (GlobalTheory.FockReal.realSubst W N.frC (GlobalTheory.ChiGrid.Pair.chi i D.R.m : GlobalTheory.ChiGrid.Pair T) k k'
            (MvPolynomial.monomial (m.mapDomain (fvar G (GlobalTheory.ChiGrid.Pair.chi i D.R.m : GlobalTheory.ChiGrid.Pair T))) 1)) := by
    funext m
    rw [jetTab, kerFin, mul_assoc r, mul_assoc r', hm, hm', kerLin_apply,
      ker_rat W _ hR (fockIn W N.frC _ (Z.vec d) _)
        (GlobalTheory.Chain.InnerSteps.theta_pureTensorO W.ψ_std W.θ_is _ _ _ _ hth _) γ hγ γ' hγ']
    exact GlobalTheory.FockReal.ker_fockIn_real hL W N.frC hp (frC_on' N) a b ha hb e₁ e₂ he₁ he₂ _ hth hvac k hk k' hk' _ _ _
  have h1 : GlobalTheory.DefStep.realAct W.θ N.fr _ k ∘ₗ GlobalTheory.DefStep.realAct W.θ N.fr _ k⁻¹ = LinearMap.id := by
    rw [← Module.End.mul_eq_comp, ← map_mul, mul_inv_cancel, map_one]; rfl
  rw [Normal.kkMap, Normal.kkMap, fockComp, fockComp, htab, hrow, ← hρ, ← hρ', LinearMap.smul_comp, LinearMap.comp_smul,
    LinearMap.comp_assoc, LinearMap.comp_assoc, h1, LinearMap.comp_id]
  rfl
