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
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompactPairRealAverageFockEqJetOperator
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ThetaStepDistributionEquivariantRational
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.KJInf Formalism.L2.Ker MvPolynomial in
/- English proof (translation)
Establish `h1 : ∀ (J : (DVar ι a b →₀ ℕ) → ℂ) Q, jetLin (fun m => c * J m) Q = c • jetLin J Q` using `fun J Q => by`. Use `LinearMap.congr_fun (f := jetLin (fun m => c * J m)) (g := c • jetLin J) ((basisMonomials _ ℂ).ext fun m => ?_) Q` and prove the remaining obligations. Rewrite using `[coe_basisMonomials]`. Simplify using `only [LinearMap.smul_apply, GlobalTheory.KerT.RatLaw.jetLin_monomial, smul_monomial, smul_eq_mul]`. Establish `h2 : ∀ (J : (DVar ι a b →₀ ℕ) → ℂ), jetMap (fun m => c * J m) n P = c • jetMap J n P` using `fun J => by`.

Simplify using `only [jetMap, LinearMap.comp_apply, h1]`. Establish `h3 : GlobalTheory.KerT.RatLaw.tabFn (fun m => ℓ (monomial m 1)) = ℓ`. Use `(basisMonomials _ ℂ).ext fun m => ?_` and prove the remaining obligations. Rewrite using `[coe_basisMonomials]`. Conclude with `GlobalTheory.KerT.RatLaw.tabFn_monomial _ m`.

Rewrite using `[h2, GlobalTheory.KerT.RatLaw.jetMap_subst (J := fun m => ℓ (monomial m 1)) g h (fun m => by rw [h3]; rfl), smul_smul]`. Both sides reduce to the same expression.
-/
private theorem jet_smul_subst {ι : Type} [Fintype ι] {a b : ℕ} (c : ℂ) (ℓ : FP ι a b →ₗ[ℂ] ℂ)
    (g : ι → Matrix (Fin a) (Fin a) ℂ) (h : ι → Matrix (Fin b) (Fin b) ℂ) (n : ι → ℕ) (P : PY ι a) :
    jetMap (fun m => c * ℓ (mvZ g h (monomial m 1))) n P =
      (c * ∏ τ, (g τ).det ^ n τ) • lft h (jetMap (fun m => ℓ (monomial m 1)) n (lft g P)) := by
  have h1 : ∀ (J : (DVar ι a b →₀ ℕ) → ℂ) Q, jetLin (fun m => c * J m) Q = c • jetLin J Q := fun J Q => by
    refine LinearMap.congr_fun (f := jetLin (fun m => c * J m)) (g := c • jetLin J) ((basisMonomials _ ℂ).ext fun m => ?_) Q
    rw [coe_basisMonomials]
    simp only [LinearMap.smul_apply, GlobalTheory.KerT.RatLaw.jetLin_monomial, smul_monomial, smul_eq_mul]
  have h2 : ∀ (J : (DVar ι a b →₀ ℕ) → ℂ), jetMap (fun m => c * J m) n P = c • jetMap J n P := fun J => by
    simp only [jetMap, LinearMap.comp_apply, h1]
  have h3 : GlobalTheory.KerT.RatLaw.tabFn (fun m => ℓ (monomial m 1)) = ℓ := by
    refine (basisMonomials _ ℂ).ext fun m => ?_
    rw [coe_basisMonomials]
    exact GlobalTheory.KerT.RatLaw.tabFn_monomial _ m
  rw [h2, GlobalTheory.KerT.RatLaw.jetMap_subst (J := fun m => ℓ (monomial m 1)) g h (fun m => by rw [h3]; rfl), smul_smul]
  rfl

open GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.RowHoweAvg GlobalTheory.FockReal GlobalTheory.DefStep MvPolynomial in
/- English proof (translation)
Introduce `D T L sc G W U N μ0 hL i hi a b ha hb e₁ e₂ he₁ he₂ ℓ k hk k' hk'`. Establish `hi' : i < D.R.m` using `hi`. Establish `hp : DefPair D.R.m (.chi i D.R.m : Pair T)` using `⟨hi', rfl⟩`. Establish `hn` using `DefPair.nodes hp`. Establish `hX` using `GlobalTheory.SeeSaw.ontoUni_inB D W.θ (G.V (.grid i D.R.m)) (N.frC _) W.θ_is (GlobalTheory.RealType.frC_on N hn.1)`.

Establish `hY` using `GlobalTheory.SeeSaw.ontoUni_inB D W.θ (G.V (.grid (i + 1) D.R.m)) (N.frC _) W.θ_is (GlobalTheory.RealType.frC_on N hn.2)`. Establish `hJ` using `(wtOK_of_defPair G _ hp).2`. Establish `hm` using `fun τ => exps_match G hL hi' τ (ha τ) (hb τ) (he₁ τ) (he₂ τ)`. Set `f : D.what₂.Tau × Fin (G.V (.grid (i + 1) D.R.m)).rank × Fin (G.V (.grid i D.R.m)).rank → D.what₂.Tau × Fin (G.V (.grid i D.R.m)).rank × Fin (G.V (.grid (i + 1) D.R.m)).rank` to `fun k => (k.1, k.2.2, k.2.1)`. Set `ℓ' : FP D.what₂.Tau (G.V (.grid i D.R.m)).rank (G.V (.grid (i + 1) D.R.m)).rank →ₗ[ℂ] ℂ` to `ℓ ∘ₗ (rename f).toLinearMap`.

Establish `hJ' : (fun m => ℓ (MvPolynomial.monomial (m.mapDomain (fvar G (.chi i D.R.m : Pair T))) 1)) = fun m => ℓ' (monomial m 1)`. Use function extensionality and compare the values at `m`. Simplify using `only [ℓ', LinearMap.comp_apply, AlgHom.toLinearMap_apply, rename_monomial]`. Both sides reduce to the same expression. Establish `hinv : ∀ τ, (inB W.θ _ (N.frC (.grid i D.R.m)) k τ)⁻¹ = inB W.θ _ (N.frC (.grid i D.R.m)) k⁻¹ τ` using `fun τ => GlobalTheory.KJAvg.ontoUni_inv hX ⟨k, hk⟩ τ`.

Establish `e : ∀ P, realSubst W N.frC (.chi i D.R.m) k k' (rename f P) = rename f (mvZ (inB W.θ _ (N.frC (.grid i D.R.m)) k⁻¹) (inB W.θ _ (N.frC (.grid (i + 1) D.R.m)) k') P)` using `fun P => by`. Rewrite using `[← funext hinv, ← substF_rename]`. Establish `e1` using `fun τ => (map_conj_of_unitary (hX.uni ⟨k, hk⟩ τ)).1`. Establish `e2` using `fun τ => (map_conj_of_unitary (hY.uni ⟨k', hk'⟩ τ)).2`. Conclude with `congrArg₂ (fun x y => GlobalTheory.CompactHowe.substF x y (rename f P)) (funext e1) (funext e2)`.

Establish `hJ2 : (fun m => realChar W (.chi i D.R.m) e₁ e₂ k k' * ℓ (realSubst W N.frC (.chi i D.R.m) k k' (MvPolynomial.monomial (m.mapDomain (fvar G (.chi i D.R.m : Pair T))) 1))) = fun m => realChar W (.chi i D.R.m) e₁ e₂ k k' * ℓ' (mvZ (inB W.θ _ (N.frC (.grid i D.R.m)) k⁻¹) (inB W.θ _ …`. Use function extensionality and compare the values at `m`. Use `e (monomial m 1)` as an intermediate fact. Rewrite `this` using `[rename_monomial]`. Conclude with `congrArg (fun x => realChar W (.chi i D.R.m) e₁ e₂ k k' * ℓ x) this`.

Establish `hne : ∀ τ, (inB W.θ _ (N.frC (.grid i D.R.m)) k τ).det ≠ 0` using `fun τ => (Matrix.UnitaryGroup.det_isUnit ⟨_, hX.uni ⟨k, hk⟩ τ⟩).ne_zero`. Establish `hsc : realChar W (.chi i D.R.m) e₁ e₂ k k' * ∏ τ, (inB W.θ _ (N.frC (.grid i D.R.m)) k⁻¹ τ).det ^ nuEnd G (.chi i D.R.m : Pair T) τ = (∏ τ, (compAt W.θ τ (Formalism.L2.Theta.mt (G.V (.grid (i + 1) D.R.m)) k')).det ^ (wt G (.grid (i + 1) D.R.m) τ).detShift) * ∏ τ, (compAt W.θ τ (F …`. Simplify using `only [realChar, ← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun τ _ => ?_` and prove the remaining obligations. Establish `h1` using `hne τ`.

Rewrite using `[← det_inB W.θ N (.grid i D.R.m) k⁻¹, ← hinv, Matrix.det_nonsing_inv, Ring.inverse_eq_inv', ← zpow_natCast, ← (hm τ).2, ← (hm τ).1, zpow_add₀ (inv_ne_zero h1), _root_.inv_zpow _ (e₁ τ), mul_assoc, det_inB]`. Rewrite `h1` using `[det_inB]`. Conclude with `congrArg₂ (· * ·) rfl (mul_inv_cancel_left₀ (zpow_ne_zero _ h1) _)`. Establish `key : ∀ v : VV ℂ (wt G (.grid i D.R.m)), Formalism.L2.Ker.jetOp (wt G (.grid i D.R.m)) (wt G (.grid (i + 1) D.R.m)) (fun m => realChar W (.chi i D.R.m) e₁ e₂ k k' * ℓ' (mvZ (inB W.θ _ (N.frC (.grid i D.R.m)) k⁻¹) (inB W.θ _ (N.frC (.grid (i + 1) D.R.m)) k') (monomial m 1))) (nuEn …` using `fun v => by`. Establish `hk1` using `realAct_inv_coe W.θ N (.grid i D.R.m) k⁻¹ v`.

Rewrite `hk1` using `[inv_inv]`. Use `Subtype.ext ?_` and prove the remaining obligations. Rewrite using `[realAct_inv_coe, jetOp_coe hJ, jetOp_coe hJ, hk1, jet_smul_subst, map_smul, map_smul, smul_smul, hsc]`. Rewrite using `[hJ', hJ2]`. Conclude with `LinearMap.ext key`.
-/
theorem UpperTheory.WildA.realRow :
    ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GlobalTheory.ChiGrid.GridData L sc} {W : G.Weil} {U₀ : Set T} (N : Std G U₀) {μ₀ : T}, L.Is μ₀ → ∀ (i : ℕ), i + 1 ≤ D.R.m →
      ∀ (a b : D.what₂.Tau → ℚ), (∀ τ, HasInfExp D (G.chrS (GlobalTheory.ChiGrid.Pair.chi i D.R.m : GlobalTheory.ChiGrid.Pair T)) τ (a τ)) → (∀ τ, HasInfExp D (G.chrT (GlobalTheory.ChiGrid.Pair.chi i D.R.m : GlobalTheory.ChiGrid.Pair T)) τ (b τ)) →
      ∀ (e₁ e₂ : D.what₂.Tau → ℤ), (∀ τ, (e₁ τ : ℚ) = a τ + GlobalTheory.FockReal.sgnP (GlobalTheory.ChiGrid.Pair.chi i D.R.m : GlobalTheory.ChiGrid.Pair T) * (G.pS (GlobalTheory.ChiGrid.Pair.chi i D.R.m : GlobalTheory.ChiGrid.Pair T)).rank / 2) →
        (∀ τ, (e₂ τ : ℚ) = -(b τ + GlobalTheory.FockReal.sgnP (GlobalTheory.ChiGrid.Pair.chi i D.R.m : GlobalTheory.ChiGrid.Pair T) * (G.pT (GlobalTheory.ChiGrid.Pair.chi i D.R.m : GlobalTheory.ChiGrid.Pair T)).rank / 2)) →
      ∀ (ℓ : PolF D (G.pT (GlobalTheory.ChiGrid.Pair.chi i D.R.m : GlobalTheory.ChiGrid.Pair T)).rank (G.pS (GlobalTheory.ChiGrid.Pair.chi i D.R.m : GlobalTheory.ChiGrid.Pair T)).rank →ₗ[ℂ] ℂ) (k : GA D (G.V ((GlobalTheory.ChiGrid.Pair.chi i D.R.m : GlobalTheory.ChiGrid.Pair T)).small)), k ∈ GinfC (G.V ((GlobalTheory.ChiGrid.Pair.chi i D.R.m : GlobalTheory.ChiGrid.Pair T)).small) →
      ∀ k' : GA D (G.V ((GlobalTheory.ChiGrid.Pair.chi i D.R.m : GlobalTheory.ChiGrid.Pair T)).big), k' ∈ GinfC (G.V ((GlobalTheory.ChiGrid.Pair.chi i D.R.m : GlobalTheory.ChiGrid.Pair T)).big) →
        Formalism.L2.Ker.jetOp (wt G ((GlobalTheory.ChiGrid.Pair.chi i D.R.m : GlobalTheory.ChiGrid.Pair T)).small) (wt G ((GlobalTheory.ChiGrid.Pair.chi i D.R.m : GlobalTheory.ChiGrid.Pair T)).big) (fun m => GlobalTheory.FockReal.realChar W (GlobalTheory.ChiGrid.Pair.chi i D.R.m : GlobalTheory.ChiGrid.Pair T) e₁ e₂ k k' *
                  ℓ (GlobalTheory.FockReal.realSubst W N.frC (GlobalTheory.ChiGrid.Pair.chi i D.R.m : GlobalTheory.ChiGrid.Pair T) k k' (MvPolynomial.monomial (m.mapDomain (fvar G (GlobalTheory.ChiGrid.Pair.chi i D.R.m : GlobalTheory.ChiGrid.Pair T))) 1))) (nuEnd G (GlobalTheory.ChiGrid.Pair.chi i D.R.m : GlobalTheory.ChiGrid.Pair T)) =
          GlobalTheory.DefStep.realAct W.θ N.fr ((GlobalTheory.ChiGrid.Pair.chi i D.R.m : GlobalTheory.ChiGrid.Pair T)).big k'⁻¹ ∘ₗ
            Formalism.L2.Ker.jetOp (wt G ((GlobalTheory.ChiGrid.Pair.chi i D.R.m : GlobalTheory.ChiGrid.Pair T)).small) (wt G ((GlobalTheory.ChiGrid.Pair.chi i D.R.m : GlobalTheory.ChiGrid.Pair T)).big) (fun m => ℓ (MvPolynomial.monomial (m.mapDomain (fvar G (GlobalTheory.ChiGrid.Pair.chi i D.R.m : GlobalTheory.ChiGrid.Pair T))) 1)) (nuEnd G (GlobalTheory.ChiGrid.Pair.chi i D.R.m : GlobalTheory.ChiGrid.Pair T)) ∘ₗ
            GlobalTheory.DefStep.realAct W.θ N.fr ((GlobalTheory.ChiGrid.Pair.chi i D.R.m : GlobalTheory.ChiGrid.Pair T)).small k := by
  intro D T L sc G W U N μ0 hL i hi a b ha hb e₁ e₂ he₁ he₂ ℓ k hk k' hk'
  have hi' : i < D.R.m := hi
  have hp : DefPair D.R.m (.chi i D.R.m : Pair T) := ⟨hi', rfl⟩
  have hn := DefPair.nodes hp
  have hX := GlobalTheory.SeeSaw.ontoUni_inB D W.θ (G.V (.grid i D.R.m)) (N.frC _) W.θ_is (GlobalTheory.RealType.frC_on N hn.1)
  have hY := GlobalTheory.SeeSaw.ontoUni_inB D W.θ (G.V (.grid (i + 1) D.R.m)) (N.frC _) W.θ_is (GlobalTheory.RealType.frC_on N hn.2)
  have hJ := (wtOK_of_defPair G _ hp).2
  have hm := fun τ => exps_match G hL hi' τ (ha τ) (hb τ) (he₁ τ) (he₂ τ)
  let f : D.what₂.Tau × Fin (G.V (.grid (i + 1) D.R.m)).rank × Fin (G.V (.grid i D.R.m)).rank →
      D.what₂.Tau × Fin (G.V (.grid i D.R.m)).rank × Fin (G.V (.grid (i + 1) D.R.m)).rank := fun k => (k.1, k.2.2, k.2.1)
  let ℓ' : FP D.what₂.Tau (G.V (.grid i D.R.m)).rank (G.V (.grid (i + 1) D.R.m)).rank →ₗ[ℂ] ℂ := ℓ ∘ₗ (rename f).toLinearMap
  have hJ' : (fun m => ℓ (MvPolynomial.monomial (m.mapDomain (fvar G (.chi i D.R.m : Pair T))) 1)) =
      fun m => ℓ' (monomial m 1) := by
    funext m
    simp only [ℓ', LinearMap.comp_apply, AlgHom.toLinearMap_apply, rename_monomial]
    rfl
  have hinv : ∀ τ, (inB W.θ _ (N.frC (.grid i D.R.m)) k τ)⁻¹ = inB W.θ _ (N.frC (.grid i D.R.m)) k⁻¹ τ := fun τ =>
    GlobalTheory.KJAvg.ontoUni_inv hX ⟨k, hk⟩ τ
  have e : ∀ P, realSubst W N.frC (.chi i D.R.m) k k' (rename f P) =
      rename f (mvZ (inB W.θ _ (N.frC (.grid i D.R.m)) k⁻¹) (inB W.θ _ (N.frC (.grid (i + 1) D.R.m)) k') P) := fun P => by
    rw [← funext hinv, ← substF_rename]
    have e1 := fun τ => (map_conj_of_unitary (hX.uni ⟨k, hk⟩ τ)).1
    have e2 := fun τ => (map_conj_of_unitary (hY.uni ⟨k', hk'⟩ τ)).2
    exact congrArg₂ (fun x y => GlobalTheory.CompactHowe.substF x y (rename f P)) (funext e1) (funext e2)
  have hJ2 : (fun m => realChar W (.chi i D.R.m) e₁ e₂ k k' *
      ℓ (realSubst W N.frC (.chi i D.R.m) k k' (MvPolynomial.monomial (m.mapDomain (fvar G (.chi i D.R.m : Pair T))) 1))) =
      fun m => realChar W (.chi i D.R.m) e₁ e₂ k k' * ℓ' (mvZ (inB W.θ _ (N.frC (.grid i D.R.m)) k⁻¹)
        (inB W.θ _ (N.frC (.grid (i + 1) D.R.m)) k') (monomial m 1)) := by
    funext m
    have := e (monomial m 1)
    rw [rename_monomial] at this
    exact congrArg (fun x => realChar W (.chi i D.R.m) e₁ e₂ k k' * ℓ x) this
  have hne : ∀ τ, (inB W.θ _ (N.frC (.grid i D.R.m)) k τ).det ≠ 0 := fun τ =>
    (Matrix.UnitaryGroup.det_isUnit ⟨_, hX.uni ⟨k, hk⟩ τ⟩).ne_zero
  have hsc : realChar W (.chi i D.R.m) e₁ e₂ k k' *
      ∏ τ, (inB W.θ _ (N.frC (.grid i D.R.m)) k⁻¹ τ).det ^ nuEnd G (.chi i D.R.m : Pair T) τ =
      (∏ τ, (compAt W.θ τ (Formalism.L2.Theta.mt (G.V (.grid (i + 1) D.R.m)) k')).det ^ (wt G (.grid (i + 1) D.R.m) τ).detShift) *
      ∏ τ, (compAt W.θ τ (Formalism.L2.Theta.mt (G.V (.grid i D.R.m)) k⁻¹)).det ^ (wt G (.grid i D.R.m) τ).detShift := by
    simp only [realChar, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    have h1 := hne τ
    rw [← det_inB W.θ N (.grid i D.R.m) k⁻¹, ← hinv, Matrix.det_nonsing_inv, Ring.inverse_eq_inv', ← zpow_natCast,
      ← (hm τ).2, ← (hm τ).1, zpow_add₀ (inv_ne_zero h1), _root_.inv_zpow _ (e₁ τ), mul_assoc, det_inB]
    rw [det_inB] at h1
    exact congrArg₂ (· * ·) rfl (mul_inv_cancel_left₀ (zpow_ne_zero _ h1) _)
  have key : ∀ v : VV ℂ (wt G (.grid i D.R.m)),
      Formalism.L2.Ker.jetOp (wt G (.grid i D.R.m)) (wt G (.grid (i + 1) D.R.m))
        (fun m => realChar W (.chi i D.R.m) e₁ e₂ k k' * ℓ' (mvZ (inB W.θ _ (N.frC (.grid i D.R.m)) k⁻¹)
        (inB W.θ _ (N.frC (.grid (i + 1) D.R.m)) k') (monomial m 1))) (nuEnd G (.chi i D.R.m : Pair T)) v =
      realAct W.θ N.fr (.grid (i + 1) D.R.m) k'⁻¹ (Formalism.L2.Ker.jetOp (wt G (.grid i D.R.m)) (wt G (.grid (i + 1) D.R.m))
        (fun m => ℓ' (monomial m 1)) (nuEnd G (.chi i D.R.m : Pair T)) (realAct W.θ N.fr (.grid i D.R.m) k v)) := fun v => by
    have hk1 := realAct_inv_coe W.θ N (.grid i D.R.m) k⁻¹ v
    rw [inv_inv] at hk1
    refine Subtype.ext ?_
    rw [realAct_inv_coe, jetOp_coe hJ, jetOp_coe hJ, hk1, jet_smul_subst, map_smul, map_smul, smul_smul, hsc]
  rw [hJ', hJ2]
  exact LinearMap.ext key
