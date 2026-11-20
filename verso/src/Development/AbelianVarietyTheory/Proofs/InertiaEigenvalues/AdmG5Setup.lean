import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoAndThreeForFamily
import Formalism.SharpRestriction.GlobalTheoremInputs
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.JointConditionTameBound
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CrysOnCond
import Formalism.SharpRestriction.LevelLetterCocycles.WachCoordinates
import Formalism.SharpRestriction.LevelLetterCocycles.RamifiedCoefficientChains
import Formalism.SharpRestriction.LevelLetterCocycles.ArcLiftingSetup
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.BaseSizes
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitBoundOfParamsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameDescentConditionsEveryLocalisation
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChebotarevDegreeOne
import Formalism.AdmissibleDesigns.AdmG5OfAdm51AdmG5
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.ResidualIrreducibleRankR
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

noncomputable section

namespace GlobalTheory.NLinkTameShape

/- English proof (translation)
Establish `hb : ((0 : ℕ) : ℝ) ≤ L.sc.b`. Simplify using `only [Nat.cast_zero]`. Unfold `Scale.b`. Conclude with `(Real.exp_pos _).le`. Establish `hL : 1 ≤ L.sc.L` using `by unfold Scale.L; exact Real.one_le_rpow L.sc.one_lt_alt.le L.sc.eps_pos.le`.

Establish `fa` using `hS.facts`. Conclude with `(GlobalTheory.T.split_bound_of_params hP.font hP.fin GlobalTheory.Published.cheb_holds D L HW F (rowC C₂) nch X 120 0 hS.canon P hL le_rfl hb (fa.admJ L hS.par) hS.par67 fa.toCore.admA fa.Conclusion1.1 fa.Conclusion1.2.2 fa.Conclusion2.1 fa.Conclusion2.2.2 fa.rhoBar fa.large.2.1 …`.
-/
theorem restPt_of (hP : Hypotheses₂) (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (nch : NChoice D) (HW : HWOf D.loc)
    (F : FonOf D.loc D.locA HW) (X : KillingConditions.HubData D) (C₂ : ℝ) (hS : Setup L nch HW X C₂) (i : D.nd.Loc)
    (hi : D.nd.l i ∉ TwistedPlaces.gset D) (π : D.nd.X i) (hπ : π ∈ D.nd.Zgood i) : RestPt i (X.r i) (X.ρ i) π := by
  have hb : ((0 : ℕ) : ℝ) ≤ L.sc.b := by
    simp only [Nat.cast_zero]; unfold Scale.b; exact (Real.exp_pos _).le
  have hL : 1 ≤ L.sc.L := by unfold Scale.L; exact Real.one_le_rpow L.sc.one_lt_alt.le L.sc.eps_pos.le
  have fa := hS.facts
  exact (GlobalTheory.T.split_bound_of_params hP.font hP.fin GlobalTheory.Published.cheb_holds D L HW F (rowC C₂) nch X 120 0 hS.canon P hL le_rfl hb
    (fa.admJ L hS.par) hS.par67 fa.toCore.admA fa.Conclusion1.1 fa.Conclusion1.2.2 fa.Conclusion2.1 fa.Conclusion2.2.2 fa.rhoBar fa.large.2.1
    fa.large.2.2 fa.nct fa.trip fa.same fa.block fa.muUnr fa.depthG).2.2.2.2.2.2.2.1 i hi π hπ

/- English proof (translation)
Use extensionality with `j`. Simplify using `[Formalism.MainNotions.N.K.SplitLatticeDiagonal.splitL, Matrix.mulVec_diagonal]`. Simplify using `[Formalism.MainNotions.N.K.SplitLatticeDiagonal.splitL, Matrix.mulVec_diagonal]`.
-/
theorem splitL_diagonal {K : Type} [Field K] (a b n : ℕ) (hn : n = a + b) (c : K) (y : Fin n → K) :
    Formalism.MainNotions.N.K.SplitLatticeDiagonal.splitL a b n hn ((Matrix.diagonal fun k : Fin n => if (k : ℕ) < a then 1 else c).mulVec y) =
      ((Formalism.MainNotions.N.K.SplitLatticeDiagonal.splitL a b n hn y).1, c • (Formalism.MainNotions.N.K.SplitLatticeDiagonal.splitL a b n hn y).2) := by
  ext j
  · simp [Formalism.MainNotions.N.K.SplitLatticeDiagonal.splitL, Matrix.mulVec_diagonal]
  · simp [Formalism.MainNotions.N.K.SplitLatticeDiagonal.splitL, Matrix.mulVec_diagonal]

/- English proof (translation)
Establish `hz : ∀ (u : (D.nd.O i)ˣ) (n : ℤ), IsLocalRing.residue (D.nd.O i) ((u ^ n : (D.nd.O i)ˣ) : D.nd.O i) = (IsLocalRing.residue (D.nd.O i) u) ^ n`. Introduce `u n`. Use `congrArg Units.val (map_zpow (Units.map (IsLocalRing.residue (D.nd.O i)).toMonoidHom) u n)` as an intermediate fact. Rewrite `this` using `[Units.val_zpow_eq_zpow_val]`. Simplify `this` using `only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe]`.

Establish `hs : ∀ (c : D.nd.O i) (M : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i)), (c • M).map (IsLocalRing.residue (D.nd.O i)) = IsLocalRing.residue (D.nd.O i) c • M.map (IsLocalRing.residue (D.nd.O i))` using `fun c M => by ext; simp`. Use `MonoidHom.ext fun g => LinearMap.ext fun u => funext fun k => ?_` and prove the remaining obligations. Simplify using `[rhoBarTw, twistRep, glRep, matRep, mapM, twistM, redRep, mapRep, Formalism.MainNotions.SumRepresentations.At.chiEpsBar, rhoO]`. Rewrite using `[hs, Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul, map_mul, hz, map_units_inv]`.
-/
theorem rhoBarTw_eq (D : D7) (i : D.nd.Loc) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
    (a : ℤ) : rhoBarTw D.nd ρ π a =
      twistRep (glRep (redRep D.nd i (ρ π))) (Formalism.MainNotions.SumRepresentations.At.chiEpsBar D.nd i a) := by
  have hz : ∀ (u : (D.nd.O i)ˣ) (n : ℤ), IsLocalRing.residue (D.nd.O i) ((u ^ n : (D.nd.O i)ˣ) : D.nd.O i) =
      (IsLocalRing.residue (D.nd.O i) u) ^ n := by
    intro u n
    have := congrArg Units.val (map_zpow (Units.map (IsLocalRing.residue (D.nd.O i)).toMonoidHom) u n)
    rw [Units.val_zpow_eq_zpow_val] at this
    simpa only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe] using this
  have hs : ∀ (c : D.nd.O i) (M : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i)),
      (c • M).map (IsLocalRing.residue (D.nd.O i)) =
        IsLocalRing.residue (D.nd.O i) c • M.map (IsLocalRing.residue (D.nd.O i)) := fun c M => by
    ext; simp
  refine MonoidHom.ext fun g => LinearMap.ext fun u => funext fun k => ?_
  simp [rhoBarTw, twistRep, glRep, matRep, mapM, twistM, redRep, mapRep, Formalism.MainNotions.SumRepresentations.At.chiEpsBar, rhoO]
  rw [hs, Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul, map_mul, hz, map_units_inv]

/- English proof (translation)
Introduce `hP D L P nch HW F Cm X C₂ hS i hi π hπ _ S hG`. Establish `R` using `restPt_of hP D L P nch HW F X C₂ hS i hi π hπ`. Establish `hHG : HG D.nd D.naut i` using `⟨π, (D.Zgood_tie i π).1 hπ⟩`. Establish `h32` using `hS.facts.Conclusion2.1 i hHG (X.r i) R.good`. Establish `hx` using `(GlobalTheory.TameDesign.main D i).2`.

Establish `hrb` using `isRhoBar_of_isRhoOf D i π (X.ρ i π) R.rho`. Introduce `v hv`. Establish `hl` using `D.nd.SQ_l i v hv`. Take `⟨ha, hb, hc⟩` from `h32 v hv hl`. Use `⟨(hx v hv).1, fun hq x => ?_, fun hk => ?_, fun hvS => ⟨?_, fun a => ?_⟩⟩` and prove the remaining obligations.

Take `⟨hprod, Pm, hPm⟩` from `ha hq x`. Use `⟨fun γ hγ => by simpa [rO, chi1] using hprod γ hγ, ?_⟩` and prove the remaining obligations. Set `ψ : (Fin D.R.nV → KK D.nd i) ≃ₗ[KK D.nd i] (Fin D.R.nV → KK D.nd i)` to `LinearEquiv.ofLinear (Matrix.toLin' ((Pm⁻¹ : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (KK D.nd i))) (Matrix.toLin' ((Pm : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (KK D.nd i))) (by rw [← Matrix.toLin'_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.toLin'_one]) (b …`. Use `⟨ψ.trans (Formalism.MainNotions.N.K.SplitLatticeDiagonal.splitL D.R.r D.R.t D.R.nV rfl), fun γ hγ u => ?_⟩` and prove the remaining obligations. Establish `hM` using `hPm γ hγ`.

Establish `h1 : ((Pm⁻¹ : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (KK D.nd i)) * mapM (toK D.nd i) (rO D.nd i (X.r i) x) γ = Matrix.diagonal (fun k : Fin D.R.nV => if (k : ℕ) < D.R.r then 1 else algebraMap (D.nd.O i) (KK D.nd i) (chi1 D.nd i γ)) * ((Pm⁻¹ : GL _ _) : Matrix (Fin D.R.nV) (F …`. Rewrite using `[← hM]`. Establish `e : Pm⁻¹ * mapRep (algebraMap (D.nd.O i) (Kf D.nd i)) (X.r i x) γ = (Pm⁻¹ * mapRep (algebraMap (D.nd.O i) (Kf D.nd i)) (X.r i x) γ * Pm) * Pm⁻¹` using `by group`. Establish `e2` using `congrArg (fun g : GL (Fin D.R.nV) (Kf D.nd i) => (g : Matrix (Fin D.R.nV) (Fin D.R.nV) (Kf D.nd i))) e`. Simplify using `only [Units.val_mul] at e2`.

Conclude with `e2`. Use `show Formalism.MainNotions.N.K.SplitLatticeDiagonal.splitL D.R.r D.R.t D.R.nV rfl (((Pm⁻¹ : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (KK D.nd i)).mulVec ((mapM (toK D.nd i) (rO D.nd i (X.r i) x) γ).mulVec u)) = _`. Rewrite using `[Matrix.mulVec_mulVec, h1, ← Matrix.mulVec_mulVec]`. Conclude with `splitL_diagonal D.R.r D.R.t D.R.nV rfl _ _`. Take `⟨k, hk⟩` from `hk`.

Establish `hvS : v ∈ D.nd.S i`. Use `(D.nd.S_def i v).2 ⟨?_, hl⟩` and prove the remaining obligations. Use `fin_cases k`. Conclude with `Or.inl hk`. Conclude with `Or.inr (Or.inl hk)`.

Take `⟨Pp, hU, hPp⟩` from `hb ⟨k, hk⟩ hvS`. Conclude with `⟨Pp, fun x γ hγ => hPp x γ hγ, hU⟩`. Conclude with `(hc hvS).1 (X.ρ i) π S (Formalism.MainNotions.SumRepresentations.At.inertia_props_of_idempotent_choice D.nd hG)`. Establish `H` using `(hc hvS).2 _ hrb a`. Take `⟨H0z, H1z, H2z⟩` from `H`.

Rewrite using `[rhoBarTw_eq]`. Use `letI : TopologicalSpace (IsLocalRing.ResidueField (D.nd.O i)) := ⊥`. Use `haveI : DiscreteTopology (IsLocalRing.ResidueField (D.nd.O i)) := ⟨rfl⟩`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Establish `e : H0 ((twistRep (glRep (redRep D.nd i (X.ρ i π))) (Formalism.MainNotions.SumRepresentations.At.chiEpsBar D.nd i a)).comp (decS D.nd v)) = ⊥` using `H0z`.

Rewrite using `[e]`. Use `infer_instance`. Use `H1z using 2` and compare the differences between its conclusion and the goal. Use `H2z using 2` and compare the differences between its conclusion and the goal.
-/
theorem main : Hypotheses₂ → ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (nch : NChoice D) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (X : KillingConditions.HubData D) (C₂ : ℝ), Setup L nch HW X C₂ → ∀ i, D.nd.l i ∉ TwistedPlaces.gset D → ∀ π ∈ D.nd.Zgood i, EmbeddingTypes.admG5 i (X.r i) (X.ρ i) π := by
  intro hP D L P nch HW F Cm X C₂ hS i hi π hπ _ S hG
  have R := restPt_of hP D L P nch HW F X C₂ hS i hi π hπ
  have hHG : HG D.nd D.naut i := ⟨π, (D.Zgood_tie i π).1 hπ⟩
  have h32 := hS.facts.Conclusion2.1 i hHG (X.r i) R.good
  have hx := (GlobalTheory.TameDesign.main D i).2
  have hrb := isRhoBar_of_isRhoOf D i π (X.ρ i π) R.rho
  intro v hv
  have hl := D.nd.SQ_l i v hv
  obtain ⟨ha, hb, hc⟩ := h32 v hv hl
  refine ⟨(hx v hv).1, fun hq x => ?_, fun hk => ?_, fun hvS => ⟨?_, fun a => ?_⟩⟩
  · obtain ⟨hprod, Pm, hPm⟩ := ha hq x
    refine ⟨fun γ hγ => by simpa [rO, chi1] using hprod γ hγ, ?_⟩
    let ψ : (Fin D.R.nV → KK D.nd i) ≃ₗ[KK D.nd i] (Fin D.R.nV → KK D.nd i) :=
      LinearEquiv.ofLinear (Matrix.toLin' ((Pm⁻¹ : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (KK D.nd i)))
        (Matrix.toLin' ((Pm : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (KK D.nd i)))
        (by rw [← Matrix.toLin'_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.toLin'_one])
        (by rw [← Matrix.toLin'_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.toLin'_one])
    refine ⟨ψ.trans (Formalism.MainNotions.N.K.SplitLatticeDiagonal.splitL D.R.r D.R.t D.R.nV rfl), fun γ hγ u => ?_⟩
    have hM := hPm γ hγ
    have h1 : ((Pm⁻¹ : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (KK D.nd i)) *
        mapM (toK D.nd i) (rO D.nd i (X.r i) x) γ =
        Matrix.diagonal (fun k : Fin D.R.nV => if (k : ℕ) < D.R.r then 1 else
          algebraMap (D.nd.O i) (KK D.nd i) (chi1 D.nd i γ)) *
          ((Pm⁻¹ : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (KK D.nd i)) := by
      rw [← hM]
      have e : Pm⁻¹ * mapRep (algebraMap (D.nd.O i) (Kf D.nd i)) (X.r i x) γ =
          (Pm⁻¹ * mapRep (algebraMap (D.nd.O i) (Kf D.nd i)) (X.r i x) γ * Pm) * Pm⁻¹ := by group
      have e2 := congrArg (fun g : GL (Fin D.R.nV) (Kf D.nd i) => (g : Matrix (Fin D.R.nV) (Fin D.R.nV) (Kf D.nd i))) e
      simp only [Units.val_mul] at e2
      exact e2
    show Formalism.MainNotions.N.K.SplitLatticeDiagonal.splitL D.R.r D.R.t D.R.nV rfl
        (((Pm⁻¹ : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (KK D.nd i)).mulVec
          ((mapM (toK D.nd i) (rO D.nd i (X.r i) x) γ).mulVec u)) = _
    rw [Matrix.mulVec_mulVec, h1, ← Matrix.mulVec_mulVec]
    exact splitL_diagonal D.R.r D.R.t D.R.nV rfl _ _
  · obtain ⟨k, hk⟩ := hk
    have hvS : v ∈ D.nd.S i := by
      refine (D.nd.S_def i v).2 ⟨?_, hl⟩
      fin_cases k
      · exact Or.inl hk
      · exact Or.inr (Or.inl hk)
    obtain ⟨Pp, hU, hPp⟩ := hb ⟨k, hk⟩ hvS
    exact ⟨Pp, fun x γ hγ => hPp x γ hγ, hU⟩
  · exact (hc hvS).1 (X.ρ i) π S (Formalism.MainNotions.SumRepresentations.At.inertia_props_of_idempotent_choice D.nd hG)
  · have H := (hc hvS).2 _ hrb a
    obtain ⟨H0z, H1z, H2z⟩ := H
    rw [rhoBarTw_eq]
    letI : TopologicalSpace (IsLocalRing.ResidueField (D.nd.O i)) := ⊥
    haveI : DiscreteTopology (IsLocalRing.ResidueField (D.nd.O i)) := ⟨rfl⟩
    refine ⟨?_, ?_, ?_⟩
    · have e : H0 ((twistRep (glRep (redRep D.nd i (X.ρ i π))) (Formalism.MainNotions.SumRepresentations.At.chiEpsBar D.nd i a)).comp (decS D.nd v)) = ⊥ := H0z
      rw [e]
      infer_instance
    · convert H1z using 2
    · convert H2z using 2

end GlobalTheory.NLinkTameShape

end
