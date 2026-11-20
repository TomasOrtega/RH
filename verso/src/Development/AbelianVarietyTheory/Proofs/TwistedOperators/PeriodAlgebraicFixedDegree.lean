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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsVacuumConjOfNegHermitianSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockVectorNegHermitianSpaceConjMonomial
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaHeisenbergConjugationNegHermitianSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockJetsUnitVacuumEqUnitMulPeriodJets
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockVacEqJets
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormSqMulGaussianLatticeTranslateEqShifted
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsVacuumMovedThetaVacuum
import Formalism.LocalToGlobal.Columns.CoefficientsModP.LatticeBasisExistsHolds
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FrameGramUnitaryIdentityStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
noncomputable section

namespace GlobalTheory.BotTransJet

open GlobalTheory.Grid (neg)

/- English proof (translation)
Take `⟨p, hp, hz⟩` from `h`. Use `⟨p, hp, ?_⟩` and prove the remaining obligations. Use `Polynomial.aeval_algHom_apply ((starRingEnd ℂ).toRatAlgHom) z p` as an intermediate fact. Rewrite `this` using `[hz, map_zero]`. Simplify using `using this`.
-/
theorem conj_isAlgebraic {z : ℂ} (h : IsAlgebraic ℚ z) : IsAlgebraic ℚ (starRingEnd ℂ z) := by
  obtain ⟨p, hp, hz⟩ := h
  refine ⟨p, hp, ?_⟩
  have := Polynomial.aeval_algHom_apply ((starRingEnd ℂ).toRatAlgHom) z p
  rw [hz, map_zero] at this
  simpa using this

/- English proof (translation)
Rewrite using `[← mem_algebraicClosure_iff]`. Unfold `GL3Theta.applyAt0`. Use `sum_mem fun α _ => mul_mem (mul_mem ((mem_algebraicClosure_iff).2 (hP α)) ?_) (hG α)` and prove the remaining obligations. Conclude with `prod_mem fun _ _ => natCast_mem _ _`.
-/
theorem applyAt0_isAlgebraic {D : D7} {N N' : ℕ} {P : MvPolynomial (GL3Theta.Idx D N N') ℂ} {G : TaylorLogMetric.VC D N N' → ℂ}
    (hP : ∀ α, IsAlgebraic ℚ (P.coeff α)) (hG : TaylorLogMetric.CoefIn D G TaylorLogMetric.Qbar) : IsAlgebraic ℚ (GL3Theta.applyAt0 D P G) := by
  rw [← mem_algebraicClosure_iff]
  unfold GL3Theta.applyAt0
  refine sum_mem fun α _ => mul_mem (mul_mem ((mem_algebraicClosure_iff).2 (hP α)) ?_) (hG α)
  exact prod_mem fun _ _ => natCast_mem _ _

/- English proof (translation)
Rewrite using `[GlobalTheory.FockConj.pureTensorO_negSp_monomial ψ θ S T sS sT BS BT _ hψ hθ k 0]`. Establish `h` using `((GlobalTheory.CjNeg.theta_heis_neg D ψ hψ S T).2 u (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id f)).2`. Establish `hcc : GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id f) = f`. Use function extensionality and compare the values at `x`. Simplify using `[GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj]`.

Rewrite `h` using `[hcc]`. Establish `key : (fun w => starRingEnd ℂ (heisO ψ (negSp S) T u f w)) = heisO ψ S T u (fun w => starRingEnd ℂ (f w))`. Establish `hcj : GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id f = fun w => starRingEnd ℂ (f w)` using `rfl`. Rewrite using `[h, ← hcj]`. Use function extensionality and compare the values at `w`.

Simplify using `[GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj]`. Rewrite using `[key]`.
-/
theorem jet_negSp_heis {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ)
    (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (f : WO S T → ℂ) (u : WO S T) (k : FVar D T.rank S.rank →₀ ℕ) :
    pureTensorO ψ θ (negSp S) T (fun τ => -sS τ) sT BS BT (heisO ψ (negSp S) T u f) (MvPolynomial.monomial k 1) 0 =
      starRingEnd ℂ (pureTensorO ψ θ S T sS sT BS BT (heisO ψ S T u (fun w => starRingEnd ℂ (f w)))
        (MvPolynomial.monomial k 1) 0) := by
  rw [GlobalTheory.FockConj.pureTensorO_negSp_monomial ψ θ S T sS sT BS BT _ hψ hθ k 0]
  have h := ((GlobalTheory.CjNeg.theta_heis_neg D ψ hψ S T).2 u (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id f)).2
  have hcc : GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id f) = f := by
    funext x
    simp [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj]
  rw [hcc] at h
  have key : (fun w => starRingEnd ℂ (heisO ψ (negSp S) T u f w)) = heisO ψ S T u (fun w => starRingEnd ℂ (f w)) := by
    have hcj : GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id f = fun w => starRingEnd ℂ (f w) := rfl
    rw [h, ← hcj]
    funext w
    simp [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj]
  rw [key]

/- English proof (translation)
Use extensionality with `y`. Simplify using `only [SetLike.mem_coe, hL, lc_mem_colLat_one, Submodule.mem_one]`.
-/
theorem std_eq_colLat_one {D : D7} {n : ℕ} (L : Submodule (𝓞 D.host.E) (Fin n → D.host.E))
    (hL : ∀ y, y ∈ L ↔ ∀ i, ∃ b : 𝓞 D.host.E, (b : D.host.E) = y i) :
    (L : Set (Fin n → D.host.E)) = (colLat (1 : GL (Fin n) D.host.E) : Set _) := by
  ext y
  simp only [SetLike.mem_coe, hL, lc_mem_colLat_one, Submodule.mem_one]

/- English proof (translation)
Use `Even.mul_left ?_ _` and prove the remaining obligations. Establish `h1` using `hX.rank`. Establish `h2` using `hX.rank'`. Establish `h3` using `hX.is.rank`. Establish `h4` using `SqNum.ranks_exact D i j`.

Rewrite using `[← h3, h1, h2]`. Use `⟨SqNum.halfRank D i j - (D.R.m - (j.1 + 1)) / 2 - (D.R.m - j.1) / 2, ?_⟩` and prove the remaining obligations. Use linear arithmetic over natural numbers and integers.
-/
theorem even_bot {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW} (hX : IsBottomTri W i j X) : Even (A.rank * WW.rank) := by
  refine Even.mul_left ?_ _
  have h1 := hX.rank
  have h2 := hX.rank'
  have h3 := hX.is.rank
  have h4 := SqNum.ranks_exact D i j
  rw [← h3, h1, h2]
  refine ⟨SqNum.halfRank D i j - (D.R.m - (j.1 + 1)) / 2 - (D.R.m - j.1) / 2, ?_⟩
  omega

end GlobalTheory.BotTransJet

namespace GlobalTheory.BotTransJet

open GlobalTheory.Grid (neg)

/- English proof (translation)
Introduce `D T _ L μ₀ sc G W i j A A' WW X hP hI hL hX dg`. Establish `hIs` using `hX.is`. Establish `hψ : IsStdChar D W.ψ (-1)` using `hIs.isVac.1`. Establish `hθ : IsInfFam W.θ` using `hIs.isVac.2.inf`. Use `set f : WO A WW → ℂ := fun w => starRingEnd ℂ (X.vac w) with hfdef`.

Establish `hf0 : IsVacO W.ψ W.θ A WW X.rA.s X.rW.s X.rA.Λ X.rW.Λ f` using `GlobalTheory.VacConj.isVacO_conj_negSp W.ψ W.θ A WW X.rA.s X.rW.s _ _ X.vac hIs.isVac`. Establish `hf : IsVacO W.ψ W.θ A WW X.rA.s X.rW.s (colLat (1 : GL (Fin A.rank) D.host.E) : Set _) (colLat (1 : GL (Fin WW.rank) D.host.E) : Set _) f`. Rewrite using `[← std_eq_colLat_one X.rA.Λ hX.std.2.1, ← std_eq_colLat_one X.rW.Λ hX.stdW.2.1]`. Conclude with `hf0`. Establish `hS : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (1 : GL (Fin A.rank) D.host.E).1 * A.gram * (1 : GL (Fin A.rank) D.host.E).1 = 1`.

Rewrite using `[hX.std.1]`. Simplify using `[Formalism.UG.cT]`. Establish `hW : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (1 : GL (Fin WW.rank) D.host.E).1 * WW.gram * (1 : GL (Fin WW.rank) D.host.E).1 = 1`. Rewrite using `[hX.stdW.1]`. Simplify using `[Formalism.UG.cT]`.

Establish `hcA : ∀ τ, IsCartanInv (gramAt D A τ) (X.rA.s τ)` using `fun τ => (hIs.rigA.2.2 τ).1`. Establish `hcW : ∀ τ, IsCartanInv (gramAt D WW τ) (X.rW.s τ)` using `fun τ => (hIs.rigW.2.2 τ).1`. Establish `hBA : (fun τ => (1 : GL (Fin A.rank) D.host.E).1.map (tauE D τ)) = X.rA.B`. Use function extensionality and compare the values at `τ`. Rewrite using `[(hX.std.2.2 τ).2]`.

Simplify using the standard rewrite rules. Establish `hBW : (fun τ => (1 : GL (Fin WW.rank) D.host.E).1.map (tauE D τ)) = X.rW.B`. Use function extensionality and compare the values at `τ`. Rewrite using `[(hX.stdW.2.2 τ).2]`. Simplify using the standard rewrite rules.

Take `⟨δ, hC, hδ⟩` from `GlobalTheory.FunObj.exists_delta D`. Take `⟨t0, ht0⟩` from `((hI D).t0Ex D.host.ccK δ hC).1`. Establish `hev : Even (A.rank * WW.rank)` using `even_bot hX`. Take `⟨e0, he0, -⟩` from `GlobalTheory.Vacuum.exists_vacuum D D.host.ccK δ hC t0 ht0 A.rank WW.rank hev`. Take `⟨c, hc⟩` from `GlobalTheory.FockPos.fock_jets_eq_unit_mul_period_jets W.ψ W.θ A WW X.rA.s X.rW.s 1 1 hS hW hcA hcW δ t0 hC hδ ht0 e0 he0 f hf`.

Establish `hΩ : starRingEnd ℂ ((c : ℂ) * dg.prod fun τ n => GlobalTheory.FunObj.period δ τ ^ n) ≠ 0` using `(map_ne_zero _).2 (mul_ne_zero c.ne_zero (Finsupp.prod_ne_zero_iff.2 fun τ _ => pow_ne_zero _ (GlobalTheory.FunObj.period_ne_zero hδ τ)))`. Use `⟨_, hΩ, fun u hu k hk => ?_⟩` and prove the remaining obligations. Take `⟨m, a, s, ha, hs, hjet⟩` from `GlobalTheory.T.frame_gram_unitary_identity hP hI W.ψ W.θ A WW X.rA.s X.rW.s 1 1 hS hW hcA hcW δ t0 hC hδ ht0 e0 he0 f hf c (fun k => hc k) u hu`. Establish `hconj` using `jet_negSp_heis W.ψ W.θ hψ hθ A WW X.rA.s X.rW.s X.rA.B X.rW.B X.vac u k`. Establish `hprod : (k.prod fun v n => GlobalTheory.FunObj.period δ v.1 ^ n) = dg.prod fun τ n => GlobalTheory.FunObj.period δ τ ^ n`.

Rewrite using `[← hk, Finsupp.prod_mapDomain_index (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)]`. Establish `hcoef : TaylorLogMetric.CoefIn D (StandardLatticesGL3.comb D (TaylorLogMetric.tor0 D D.host.ccK δ) a s e0) TaylorLogMetric.Qbar` using `((hI D).alg D.host.ccK δ hC t0 ht0 A.rank WW.rank (StandardLatticesGL3.stdL D A.rank) (StandardLatticesGL3.stdL D WW.rank) (GlobalTheory.MovedVacuum.sd_stdL D _) (GlobalTheory.MovedVacuum.sd_stdL D _) hev e0 he0.2.2.2.1).2.2.1 m a s (fun l => (mem_algebraicClosure_iff).2 (ha l)) …`. Establish `hY : IsAlgebraic ℚ (GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) (StandardLatticesGL3.comb D (TaylorLogMetric.tor0 D D.host.ccK δ) a s e0))`. Use `applyAt0_isAlgebraic (fun α => ?_) hcoef` and prove the remaining obligations. Rewrite using `[MvPolynomial.coeff_monomial]`.

Use `split_ifs`. Conclude with `isAlgebraic_one`. Conclude with `isAlgebraic_zero`. Express the relevant statement in the definitionally equal form `IsAlgebraic ℚ (pureTensorO W.ψ W.θ (negSp A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (heisO W.ψ (negSp A) WW u X.vac) (MvPolynomial.monomial k 1) 0 / _)`. Rewrite using `[hconj, ← hBA, ← hBW, hjet k, hprod, show ∀ x y z : ℂ, x * (y * z) = (x * y) * z from fun _ _ _ => (mul_assoc _ _ _).symm, map_mul, mul_div_cancel_left₀ _ hΩ]`.

Conclude with `conj_isAlgebraic hY`.
-/
theorem jets_div_period_isAlgebraic : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, GlobalTheory.FunPr.Hypotheses₂ → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X →
    ∀ dg : D.what₂.Tau →₀ ℕ, ∃ Ω : ℂ, Ω ≠ 0 ∧ ∀ u : WO (GlobalTheory.Grid.neg A) WW, u.map (infPart D) = 0 →
      ∀ k : FVar D WW.rank A.rank →₀ ℕ, Finsupp.mapDomain Prod.fst k = dg →
        IsAlgebraic ℚ (pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B
          (heisO W.ψ (GlobalTheory.Grid.neg A) WW u X.vac) (MvPolynomial.monomial k 1) 0 / Ω) := by
  intro D T _ L μ₀ sc G W i j A A' WW X hP hI hL hX dg
  classical
  have hIs := hX.is
  have hψ : IsStdChar D W.ψ (-1) := hIs.isVac.1
  have hθ : IsInfFam W.θ := hIs.isVac.2.inf
  set f : WO A WW → ℂ := fun w => starRingEnd ℂ (X.vac w) with hfdef
  have hf0 : IsVacO W.ψ W.θ A WW X.rA.s X.rW.s X.rA.Λ X.rW.Λ f :=
    GlobalTheory.VacConj.isVacO_conj_negSp W.ψ W.θ A WW X.rA.s X.rW.s _ _ X.vac hIs.isVac
  have hf : IsVacO W.ψ W.θ A WW X.rA.s X.rW.s (colLat (1 : GL (Fin A.rank) D.host.E) : Set _)
      (colLat (1 : GL (Fin WW.rank) D.host.E) : Set _) f := by
    rw [← std_eq_colLat_one X.rA.Λ hX.std.2.1, ← std_eq_colLat_one X.rW.Λ hX.stdW.2.1]
    exact hf0
  have hS : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (1 : GL (Fin A.rank) D.host.E).1 * A.gram *
      (1 : GL (Fin A.rank) D.host.E).1 = 1 := by
    rw [hX.std.1]
    simp [Formalism.UG.cT]
  have hW : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (1 : GL (Fin WW.rank) D.host.E).1 * WW.gram *
      (1 : GL (Fin WW.rank) D.host.E).1 = 1 := by
    rw [hX.stdW.1]
    simp [Formalism.UG.cT]
  have hcA : ∀ τ, IsCartanInv (gramAt D A τ) (X.rA.s τ) := fun τ => (hIs.rigA.2.2 τ).1
  have hcW : ∀ τ, IsCartanInv (gramAt D WW τ) (X.rW.s τ) := fun τ => (hIs.rigW.2.2 τ).1
  have hBA : (fun τ => (1 : GL (Fin A.rank) D.host.E).1.map (tauE D τ)) = X.rA.B := by
    funext τ
    rw [(hX.std.2.2 τ).2]
    simp
  have hBW : (fun τ => (1 : GL (Fin WW.rank) D.host.E).1.map (tauE D τ)) = X.rW.B := by
    funext τ
    rw [(hX.stdW.2.2 τ).2]
    simp
  obtain ⟨δ, hC, hδ⟩ := GlobalTheory.FunObj.exists_delta D
  obtain ⟨t0, ht0⟩ := ((hI D).t0Ex D.host.ccK δ hC).1
  have hev : Even (A.rank * WW.rank) := even_bot hX
  obtain ⟨e0, he0, -⟩ := GlobalTheory.Vacuum.exists_vacuum D D.host.ccK δ hC t0 ht0 A.rank WW.rank hev
  obtain ⟨c, hc⟩ := GlobalTheory.FockPos.fock_jets_eq_unit_mul_period_jets W.ψ W.θ A WW X.rA.s X.rW.s 1 1 hS hW hcA hcW δ t0 hC hδ
    ht0 e0 he0 f hf
  have hΩ : starRingEnd ℂ ((c : ℂ) * dg.prod fun τ n => GlobalTheory.FunObj.period δ τ ^ n) ≠ 0 :=
    (map_ne_zero _).2 (mul_ne_zero c.ne_zero (Finsupp.prod_ne_zero_iff.2 fun τ _ =>
      pow_ne_zero _ (GlobalTheory.FunObj.period_ne_zero hδ τ)))
  refine ⟨_, hΩ, fun u hu k hk => ?_⟩
  obtain ⟨m, a, s, ha, hs, hjet⟩ := GlobalTheory.T.frame_gram_unitary_identity hP hI W.ψ W.θ A WW X.rA.s X.rW.s 1 1 hS hW hcA hcW δ t0 hC hδ ht0 e0 he0 f hf
    c (fun k => hc k) u hu
  have hconj := jet_negSp_heis W.ψ W.θ hψ hθ A WW X.rA.s X.rW.s X.rA.B X.rW.B X.vac u k
  have hprod : (k.prod fun v n => GlobalTheory.FunObj.period δ v.1 ^ n) = dg.prod fun τ n => GlobalTheory.FunObj.period δ τ ^ n := by
    rw [← hk, Finsupp.prod_mapDomain_index (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)]
  have hcoef : TaylorLogMetric.CoefIn D (StandardLatticesGL3.comb D (TaylorLogMetric.tor0 D D.host.ccK δ) a s e0) TaylorLogMetric.Qbar :=
    ((hI D).alg D.host.ccK δ hC t0 ht0 A.rank WW.rank (StandardLatticesGL3.stdL D A.rank) (StandardLatticesGL3.stdL D WW.rank)
      (GlobalTheory.MovedVacuum.sd_stdL D _) (GlobalTheory.MovedVacuum.sd_stdL D _) hev e0 he0.2.2.2.1).2.2.1 m a s
      (fun l => (mem_algebraicClosure_iff).2 (ha l)) hs
  have hY : IsAlgebraic ℚ (GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) (StandardLatticesGL3.comb D (TaylorLogMetric.tor0 D D.host.ccK δ) a s e0)) := by
    refine applyAt0_isAlgebraic (fun α => ?_) hcoef
    rw [MvPolynomial.coeff_monomial]
    split_ifs
    · exact isAlgebraic_one
    · exact isAlgebraic_zero
  change IsAlgebraic ℚ (pureTensorO W.ψ W.θ (negSp A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (heisO W.ψ (negSp A) WW u X.vac)
    (MvPolynomial.monomial k 1) 0 / _)
  rw [hconj, ← hBA, ← hBW, hjet k, hprod, show ∀ x y z : ℂ, x * (y * z) = (x * y) * z from fun _ _ _ => (mul_assoc _ _ _).symm,
    map_mul, mul_div_cancel_left₀ _ hΩ]
  exact conj_isAlgebraic hY

end GlobalTheory.BotTransJet
