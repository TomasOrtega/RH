import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThickLetterWordLatticeSurjectionHypotheses
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsNeZeroMemJumpTypeTwo
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GoodCoefficientRingIntegersPadicFiniteExtension
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChiCrysOfConstituent
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeightRegularOfExt
import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypes
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.LiftingConditionOfWindows

noncomputable section

namespace GlobalTheory.HTW.RecS.Model

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.HTW.Rec GlobalTheory.HTW.RecS

/- English proof (translation)
The claim follows from `(goodO_finExt_integers _ Cx.LL).1`.
-/
theorem coefExt_dvr {D : D7} (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : w ∈ placesOver D.host.E (D.nd.l i)) (Cx : TruncatedSeriesCountingIdentities.CoefExt D i w hw) :
    ∃ _ : IsDomain ↥(OL Cx.LL), IsDiscreteValuationRing ↥(OL Cx.LL) ∧ IsFractionRing ↥(OL Cx.LL) ↥Cx.LL.1 :=
  (goodO_finExt_integers _ Cx.LL).1

section Std

variable {l : ℕ} [Fact l.Prime] {K LL : FinExt l} {k : ℕ}

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨u, rfl⟩ j`. Conclude with `(u j).2`. Introduce `h`. Conclude with `⟨fun j => ⟨x j, h j⟩, rfl⟩`.
-/
theorem mem_stdG_OL (x : Fin k → ↥LL.1) : x ∈ stdG ↥(OL LL) ↥LL.1 k ↔ ∀ j, x j ∈ OL LL := by
  constructor
  · rintro ⟨u, rfl⟩ j
    exact (u j).2
  · intro h
    exact ⟨fun j => ⟨x j, h j⟩, rfl⟩

set_option synthInstance.maxHeartbeats 400000 in

def stdLat (M : ↥(GK K) →* Matrix (Fin k) (Fin k) ↥LL.1) (hO : ∀ g a b, M g a b ∈ OL LL)
    (hc : ∀ v, Continuous fun g => (M g).mulVec v) : Lat K LL where
  V := Fin k → ↥LL.1
  ρ := matRep M
  cont := hc
  L :=
    { T := stdG ↥(OL LL) ↥LL.1 k
      stable := fun g x hx => by
        rw [mem_stdG_OL] at hx ⊢
        intro j
        change ∑ b, M g j b * x b ∈ OL LL
        exact Subalgebra.sum_mem _ fun b _ => Subalgebra.mul_mem _ (hO g j b) (hx b)
      fg := by
        rw [stdG, LinearMap.range_eq_map]
        exact (Module.Finite.fg_top).map _
      free := Module.Free.of_equiv (LinearEquiv.ofInjective _ (stdG_inj Subtype.val_injective k))
      span := by
        rw [eq_top_iff, ← (Pi.basisFun ↥LL.1 (Fin k)).span_eq]
        apply Submodule.span_mono
        rintro _ ⟨j, rfl⟩
        refine ⟨Pi.single j 1, ?_⟩
        funext j'
        simp [Pi.single_apply] }

/- English proof (translation)
Assemble the required witnesses or components as `⟨LinearEquiv.refl _ _, fun _ _ => rfl⟩`.
-/
theorem stdLat_isMatRep (M : ↥(GK K) →* Matrix (Fin k) (Fin k) ↥LL.1) (hO : ∀ g a b, M g a b ∈ OL LL)
    (hc : ∀ v, Continuous fun g => (M g).mulVec v) : IsMatRep (stdLat M hO hc) M :=
  ⟨LinearEquiv.refl _ _, fun _ _ => rfl⟩

/- English proof (translation)
The claim follows from `Module.finrank_fin_fun _`.
-/
theorem finrank_stdLat (M : ↥(GK K) →* Matrix (Fin k) (Fin k) ↥LL.1) (hO : ∀ g a b, M g a b ∈ OL LL)
    (hc : ∀ v, Continuous fun g => (M g).mulVec v) : Module.finrank ↥LL.1 (stdLat M hO hc).V = k :=
  Module.finrank_fin_fun _

def latId (T : Lat K LL) : LatHom T.L T.L where
  f := LinearMap.id
  equiv _ _ := rfl
  cont := continuous_id
  T_le _ h := h

/- English proof (translation)
Introduce `y hy` and use `⟨y, hy, rfl⟩`.
-/
theorem latId_onto (T : Lat K LL) : (latId T).Onto := fun y hy => ⟨y, hy, rfl⟩

end Std

section LocRep

variable {D : D7} (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
  (Cx : TruncatedSeriesCountingIdentities.CoefExt D i w hw)

/- English proof (translation)
Establish `h1 : Br.loc D.nbr i w hw M g a b ∈ OL (D.nbr i w hw).LL` using `((D.nbr i w hw).eO (M (decS D.nd w (Br.iota D.nbr i w hw g)) a b)).2`. Express the relevant statement in the definitionally equal form `Cx.inc (Br.loc D.nbr i w hw M g a b) ∈ OL Cx.LL`. Conclude with `IsIntegral.map ((IntermediateField.inclusion Cx.le).restrictScalars ℤ_[D.nd.l i]) h1`.
-/
theorem locC_mem_OL {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (g : Br.G D.nbr i w hw)
    (a b : Fin k) : TruncatedSeriesCountingIdentities.locC Cx M g a b ∈ OL Cx.LL := by
  have h1 : Br.loc D.nbr i w hw M g a b ∈ OL (D.nbr i w hw).LL :=
    ((D.nbr i w hw).eO (M (decS D.nd w (Br.iota D.nbr i w hw g)) a b)).2
  change Cx.inc (Br.loc D.nbr i w hw M g a b) ∈ OL Cx.LL
  exact IsIntegral.map ((IntermediateField.inclusion Cx.le).restrictScalars ℤ_[D.nd.l i]) h1

end LocRep

section Glob

variable {D : D7} (i : D.nd.Loc) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)

/- English proof (translation)
Establish `h1 : Continuous fun g : GE D.nd => ((((chiU D.nd i 1)⁻¹ g : (D.nd.O i)ˣ)) : D.nd.O i)`. Establish `e : (fun g : GE D.nd => ((((chiU D.nd i 1)⁻¹ g : (D.nd.O i)ˣ)) : D.nd.O i)) = fun g => ((D.nd.chi i 1 g⁻¹ : (D.nd.O i)ˣ) : D.nd.O i)`. Use function extensionality and compare the values at `g`. Rewrite using `[map_inv]`. Both sides reduce to the same expression.

Rewrite using `[e]`. Conclude with `(D.nd.chi_cont i 1).comp continuous_inv`. Establish `hW : Continuous fun g => WpO D.nd i ρ π g` using `h1.smul hρ`. Establish `hε : Continuous fun g : GE D.nd => ((epsU D.nd i g : (D.nd.O i)ˣ) : D.nd.O i)` using `GlobalTheory.LocalInv.eps_cont D.nd i`. Conclude with `hε.smul (hW.comp continuous_inv).matrix_transpose`.
-/
theorem continuous_twistedDual_rhoO (hρ : Continuous fun g => rhoO D.nd i ρ π g) : Continuous fun g => T2O D.nd i ρ π g := by
  have h1 : Continuous fun g : GE D.nd => ((((chiU D.nd i 1)⁻¹ g : (D.nd.O i)ˣ)) : D.nd.O i) := by
    have e : (fun g : GE D.nd => ((((chiU D.nd i 1)⁻¹ g : (D.nd.O i)ˣ)) : D.nd.O i)) =
        fun g => ((D.nd.chi i 1 g⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) := by
      funext g
      rw [map_inv]
      rfl
    rw [e]
    exact (D.nd.chi_cont i 1).comp continuous_inv
  have hW : Continuous fun g => WpO D.nd i ρ π g := h1.smul hρ
  have hε : Continuous fun g : GE D.nd => ((epsU D.nd i g : (D.nd.O i)ˣ) : D.nd.O i) :=
    GlobalTheory.LocalInv.eps_cont D.nd i
  exact hε.smul (hW.comp continuous_inv).matrix_transpose

end Glob

section Sub

variable {D : D7} (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
  (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (Cx : TruncatedSeriesCountingIdentities.CoefExt D i w hw)

def phiK : KK D.nd i →+* ↥Cx.LL.1 := Cx.inc.comp (Br.toLLK (D.nbr i w hw))

/- English proof (translation)
Use `Matrix.ext fun a b => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Cx.inc ((D.nbr i w hw).toLL (M _ a b)) = Cx.inc (Br.toLLK (D.nbr i w hw) (toK D.nd i (M _ a b)))`. Rewrite using `[GlobalTheory.WordJumpsCompare.toLLK_toK]`. Both sides reduce to the same expression.
-/
theorem locC_eq_map {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (g : Br.G D.nbr i w hw) :
    TruncatedSeriesCountingIdentities.locC Cx M g = (mapM (toK D.nd i) M (decS D.nd w (Br.iota D.nbr i w hw g))).map (phiK i w hw Cx) := by
  refine Matrix.ext fun a b => ?_
  change Cx.inc ((D.nbr i w hw).toLL (M _ a b)) = Cx.inc (Br.toLLK (D.nbr i w hw) (toK D.nd i (M _ a b)))
  rw [GlobalTheory.WordJumpsCompare.toLLK_toK]
  rfl

/- English proof (translation)
Use extensionality with `a b`. Simplify using `[mapM, rDuO, twistM, dualM]`.
-/
theorem mapM_rDuO (h : GE D.nd) :
    mapM (toK D.nd i) (rDuO D.nd i r π) h = toK D.nd i (((chiU D.nd i 1 * epsU D.nd i) h : (D.nd.O i)ˣ) : D.nd.O i) •
      (mapM (toK D.nd i) (rO D.nd i r π) h⁻¹).transpose := by
  ext a b
  simp [mapM, rDuO, twistM, dualM]

/- English proof (translation)
Use extensionality with `a b`. Simplify using `[mapM, T2O, WpO, twistM, dualM]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem mapM_T2O (h : GE D.nd) :
    mapM (toK D.nd i) (T2O D.nd i ρ π) h = toK D.nd i (((chiU D.nd i 1 * epsU D.nd i) h : (D.nd.O i)ˣ) : D.nd.O i) •
      (mapM (toK D.nd i) (rhoO D.nd i ρ π) h⁻¹).transpose := by
  ext a b
  simp [mapM, T2O, WpO, twistM, dualM]
  ring

end Sub

section Sub2

variable {D : D7} (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
  (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (Cx : TruncatedSeriesCountingIdentities.CoefExt D i w hw)

/- English proof (translation)
Take `⟨e, he⟩` from `hd`. Set `A : Matrix (Fin D.R.r) (Fin D.R.nV) (KK D.nd i)` to `LinearMap.toMatrix' ((LinearMap.fst (KK D.nd i) _ _).comp e.toLinearMap)`. Set `B : Matrix (Fin D.R.nV) (Fin D.R.r) (KK D.nd i)` to `LinearMap.toMatrix' (e.symm.toLinearMap.comp (LinearMap.inl (KK D.nd i) _ _))`. Establish `hA : ∀ u, A.mulVec u = (e u).1` using `fun u => by simp [A, LinearMap.toMatrix'_mulVec]`. Establish `hAB : A * B = 1`.

Rewrite using `[← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_id]`. Use `congr 1`. Use `LinearMap.ext fun v => ?_` and prove the remaining obligations. Simplify using the standard rewrite rules. Establish `hint : ∀ h : GE D.nd, A * mapM (toK D.nd i) (rO D.nd i r π) h = mapM (toK D.nd i) (rhoO D.nd i ρ π) h * A`.

Introduce `h`. Apply `Matrix.toLin'.injective` to reduce the goal to its premises. Use `LinearMap.ext fun u => ?_` and prove the remaining obligations. Rewrite using `[Matrix.toLin'_apply, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hA, hA, he]`. Set `φ` to `phiK i w hw Cx`.

Set `At : Matrix (Fin D.R.nV) (Fin D.R.r) ↥Cx.LL.1` to `A.transpose.map φ`. Establish `hinj : Function.Injective At.mulVec`. Establish `h1 : B.transpose.map φ * At = 1`. Rewrite using `[← Matrix.map_mul, ← Matrix.transpose_mul, hAB, Matrix.transpose_one, Matrix.map_one _ (map_zero φ) (map_one φ)]`. Introduce `u v huv`.

Use `congrArg (B.transpose.map φ).mulVec huv` as an intermediate fact. Simplify `this` using `only [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]`. Use `⟨1, fun _ => π, LinearMap.pi fun _ => Matrix.mulVecLin At, ?_, fun g v => ?_⟩` and prove the remaining obligations. Introduce `u v huv`. Conclude with `hinj (congrFun huv 0)`.

Use function extensionality and compare the values at `a`. Express the relevant statement in the definitionally equal form `At.mulVec ((TruncatedSeriesCountingIdentities.locC Cx (T2O D.nd i ρ π) g).mulVec v) = (TruncatedSeriesCountingIdentities.locC Cx (rDuO D.nd i r π) g).mulVec (At.mulVec v)`. Rewrite using `[Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]`. Use `congr 1`. Rewrite using `[locC_eq_map, locC_eq_map, mapM_rDuO, mapM_T2O]`.

Establish `hK : ∀ (s : KK D.nd i) (h : GE D.nd), A.transpose * (s • (mapM (toK D.nd i) (rhoO D.nd i ρ π) h).transpose) = (s • (mapM (toK D.nd i) (rO D.nd i r π) h).transpose) * A.transpose`. Introduce `s h`. Rewrite using `[Matrix.mul_smul, Matrix.smul_mul, ← Matrix.transpose_mul, ← Matrix.transpose_mul, hint]`. Simplify using `only [At]`. Rewrite using `[← Matrix.map_mul, ← Matrix.map_mul, hK]`.
-/
theorem isSubOfSums_T2O (hd : TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π) :
    IsSubOfSums (matRep (TruncatedSeriesCountingIdentities.locC Cx (T2O D.nd i ρ π))) fun x : D.nd.X i => ⇑(TruncatedSeriesCountingIdentities.locC Cx (rDuO D.nd i r x)) := by
  obtain ⟨e, he⟩ := hd
  let A : Matrix (Fin D.R.r) (Fin D.R.nV) (KK D.nd i) :=
    LinearMap.toMatrix' ((LinearMap.fst (KK D.nd i) _ _).comp e.toLinearMap)
  let B : Matrix (Fin D.R.nV) (Fin D.R.r) (KK D.nd i) :=
    LinearMap.toMatrix' (e.symm.toLinearMap.comp (LinearMap.inl (KK D.nd i) _ _))
  have hA : ∀ u, A.mulVec u = (e u).1 := fun u => by simp [A, LinearMap.toMatrix'_mulVec]
  have hAB : A * B = 1 := by
    rw [← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_id]
    congr 1
    refine LinearMap.ext fun v => ?_
    simp
  have hint : ∀ h : GE D.nd, A * mapM (toK D.nd i) (rO D.nd i r π) h = mapM (toK D.nd i) (rhoO D.nd i ρ π) h * A := by
    intro h
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun u => ?_
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hA, hA, he]
  let φ := phiK i w hw Cx
  let At : Matrix (Fin D.R.nV) (Fin D.R.r) ↥Cx.LL.1 := A.transpose.map φ
  have hinj : Function.Injective At.mulVec := by
    have h1 : B.transpose.map φ * At = 1 := by
      rw [← Matrix.map_mul, ← Matrix.transpose_mul, hAB, Matrix.transpose_one, Matrix.map_one _ (map_zero φ) (map_one φ)]
    intro u v huv
    have := congrArg (B.transpose.map φ).mulVec huv
    simpa only [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec] using this
  refine ⟨1, fun _ => π, LinearMap.pi fun _ => Matrix.mulVecLin At, ?_, fun g v => ?_⟩
  · intro u v huv
    exact hinj (congrFun huv 0)
  · funext a
    change At.mulVec ((TruncatedSeriesCountingIdentities.locC Cx (T2O D.nd i ρ π) g).mulVec v) =
      (TruncatedSeriesCountingIdentities.locC Cx (rDuO D.nd i r π) g).mulVec (At.mulVec v)
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    congr 1
    rw [locC_eq_map, locC_eq_map, mapM_rDuO, mapM_T2O]
    have hK : ∀ (s : KK D.nd i) (h : GE D.nd),
        A.transpose * (s • (mapM (toK D.nd i) (rhoO D.nd i ρ π) h).transpose) =
          (s • (mapM (toK D.nd i) (rO D.nd i r π) h).transpose) * A.transpose := by
      intro s h
      rw [Matrix.mul_smul, Matrix.smul_mul, ← Matrix.transpose_mul, ← Matrix.transpose_mul, hint]
    simp only [At]
    rw [← Matrix.map_mul, ← Matrix.map_mul, hK]

end Sub2

/- English proof (translation)
Set `T` to `stdLat (TruncatedSeriesCountingIdentities.locC Cx (T2O D.nd i ρ π)) (locC_mem_OL i w hw Cx _) (fun v => locC_cont D i _ (continuous_twistedDual_rhoO i ρ π h.contρ) w hw Cx v)`. Conclude with `⟨T, T, latId T, isSubOfSums_T2O i r ρ π w hw Cx h.dec, stdLat_isMatRep _ _ _, latId_onto T, finrank_stdLat _ _ _⟩`.
-/
theorem exists_lattices {D : D7} (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
    (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (Cx : TruncatedSeriesCountingIdentities.CoefExt D i w hw)
    (h : PtIn i r ρ π) :
    ∃ (T₁ T₂ : Lat (D.nbr i w hw).Kw Cx.LL) (F : LatHom T₁.L T₂.L),
      IsSubOfTwistedDualSums i r w hw Cx T₁ ∧ IsTwistedDualOfGaloisRep i ρ π w hw Cx T₂ ∧ F.Onto ∧ Module.finrank ↥Cx.LL.1 T₂.V = D.R.r := by
  let T := stdLat (TruncatedSeriesCountingIdentities.locC Cx (T2O D.nd i ρ π)) (locC_mem_OL i w hw Cx _)
    (fun v => locC_cont D i _ (continuous_twistedDual_rhoO i ρ π h.contρ) w hw Cx v)
  exact ⟨T, T, latId T, isSubOfSums_T2O i r ρ π w hw Cx h.dec, stdLat_isMatRep _ _ _, latId_onto T,
    finrank_stdLat _ _ _⟩

end GlobalTheory.HTW.RecS.Model
