import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPullbackDegPreStrictLineBundleIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingActionOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsLieEigenbasisOfLocalizationsAtPrime
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.ChartLawPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasisBaseChange
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushRProdPtsResP

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.RealMult.Obj

attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.LieFrameLoc

/- English proof (translation)
Rewrite using `[← Category.assoc, Chart.spMap_comp]`. Use `congr 2`. Use `AlgHom.ext fun x => TrivSqZeroExt.ext ?_ ?_` and prove the remaining obligations. Simplify using `[Chart.scaleD]`. Simplify using `only [Chart.scaleD, AlgHom.comp_apply, TrivSqZeroExt.snd_map, LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem scaleD_scaleD {R : Type} [CommRing R] {G : Over (Sp R)} (a b : R)
    (y : Chart.sp (R₀ := R) (DualNumber R) ⟶ G) :
    Chart.spMap (Chart.scaleD a) ≫ Chart.spMap (Chart.scaleD b) ≫ y = Chart.spMap (Chart.scaleD (a * b)) ≫ y := by
  rw [← Category.assoc, Chart.spMap_comp]
  congr 2
  refine AlgHom.ext fun x => TrivSqZeroExt.ext ?_ ?_
  · simp [Chart.scaleD]
  · simp only [Chart.scaleD, AlgHom.comp_apply, TrivSqZeroExt.snd_map, LinearMap.smul_apply, LinearMap.id_apply,
      smul_eq_mul]
    ring

/- English proof (translation)
Establish `key : ∀ c : Fin n → R, Chart.prodPts c (fun i => Chart.spMap (Chart.scaleD (a i : R)) ≫ u i) = Chart.prodPts (fun i => c i * a i) u` using `fun c => by`. Unfold `Chart.prodPts`. Conclude with `congrArg List.prod (congrArg List.ofFn (funext fun i => scaleD_scaleD _ _ _))`. Use `⟨ht, fun w hw => ?_⟩` and prove the remaining obligations. Take `⟨c, hc, huniq⟩` from `hu.2 w hw`.

Use `⟨fun i => c i * ↑(a i)⁻¹, ?_, fun c' hc' => ?_⟩` and prove the remaining obligations. Rewrite `hc`, the goal using `[Chart.isLieComb_iff]`. Rewrite using `[key, hc]`. Use `congr 1`. Use function extensionality and compare the values at `i`.

Simplify using `[mul_assoc]`. Use `replace hc' := (Chart.isLieComb_iff _ _ _).mp hc'`. Rewrite `hc'` using `[key]`. Use `huniq _ ((Chart.isLieComb_iff _ _ _).mpr hc')` as an intermediate fact. Use function extensionality and compare the values at `i`.

Establish `hi` using `congrFun this i`. Rewrite using `[← hi]`. Simplify using `[mul_assoc]`.
-/
theorem isLieBasis_scale {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] {n : ℕ} {u : Fin n → (epsR R ⟶ G)}
    (hu : IsLieBasis u) (a : Fin n → Rˣ)
    (ht : ∀ i, IsTangent (Chart.spMap (Chart.scaleD (a i : R)) ≫ u i : epsR R ⟶ G)) :
    IsLieBasis (fun i => (Chart.spMap (Chart.scaleD (a i : R)) ≫ u i : epsR R ⟶ G)) := by
  have key : ∀ c : Fin n → R, Chart.prodPts c (fun i => Chart.spMap (Chart.scaleD (a i : R)) ≫ u i) =
      Chart.prodPts (fun i => c i * a i) u := fun c => by
    unfold Chart.prodPts
    exact congrArg List.prod (congrArg List.ofFn (funext fun i => scaleD_scaleD _ _ _))
  refine ⟨ht, fun w hw => ?_⟩
  obtain ⟨c, hc, huniq⟩ := hu.2 w hw
  refine ⟨fun i => c i * ↑(a i)⁻¹, ?_, fun c' hc' => ?_⟩
  · rw [Chart.isLieComb_iff] at hc ⊢
    rw [key, hc]
    congr 1
    funext i
    simp [mul_assoc]
  · replace hc' := (Chart.isLieComb_iff _ _ _).mp hc'
    rw [key] at hc'
    have := huniq _ ((Chart.isLieComb_iff _ _ _).mpr hc')
    funext i
    have hi := congrFun this i
    rw [← hi]
    simp [mul_assoc]

end GlobalTheory.LieFrameLoc

open GlobalTheory.LieFrameLoc in
open scoped CategoryTheory.Obj in

/- English proof (translation)
Introduce `R _ G _ hsm p _`. Use `haveI := hsm`. Establish `: ∀ s : R, Smooth (Chart.Gs G s).hom` using `fun s => show Smooth (pullback.snd G.hom _) from inferInstance`. Establish `hGp : Smooth (Chart.Gp (G` using `G) p).hom := show Smooth (pullback.snd G.hom _) from inferInstance`. Take `⟨n, u, hu⟩` from `Chart.exists_isLieBasis (Chart.Gp (G := G) p) hGp`.

Establish `lift : ∀ i, ∃ q ∈ p.primeCompl, ∃ w : epsR R ⟶ G, IsTangent w ∧ Chart.resP p w = Chart.spMap (Chart.scaleD (algebraMap R (Localization.AtPrime p) q)) ≫ u i`. Introduce `i`. Establish `hT : Chart.TanS (Chart.pushR G (u i))` using `(Chart.isTan_iff_tanS p (u i)).mp ((Chart.isTan_iff _).mpr (hu.1 i))`. Take `⟨q, hq, w, hw, he⟩` from `Chart.tan_prime_lift p hT`. Use `⟨q, hq, w, (Chart.isTan_iff _).mp hw, Chart.pushR_inj G ?_⟩` and prove the remaining obligations.

Rewrite using `[Chart.pushR_resP, he, Chart.pushR_spMap]`. Use `congr 2`. Use `choose q hq w hw hres using lift`. Use `⟨n, w, hw, fun G' _ ψ hψ v hv => ?_⟩` and prove the remaining obligations. Set `a : Fin n → (Localization.AtPrime p)ˣ` to `fun i => (IsLocalization.map_units _ ⟨q i, hq i⟩).unit`.

Establish `hres' : ∀ i, Chart.resP p (w i) = Chart.spMap (Chart.scaleD (a i : Localization.AtPrime p)) ≫ u i` using `hres`. Establish `htan : ∀ i, IsTangent (Chart.resP p (w i))` using `fun i => (Chart.isTan_iff _).mp ((Chart.isTan_iff_tanS p _).mpr (by`. Rewrite using `[Chart.pushR_resP]`. Conclude with `Chart.tanS_restrict _ ((Chart.isTan_iff _).mpr (hw i))))`. Establish `hbasis : IsLieBasis (G` using `Chart.Gp (G := G) p) (fun i => Chart.resP p (w i)) := by`.

Establish `e : (fun i => Chart.resP p (w i)) = fun i => Chart.spMap (Chart.scaleD (a i : Localization.AtPrime p)) ≫ u i`. Use function extensionality and compare the values at `hres'`. Rewrite using `[e]`. Conclude with `isLieBasis_scale hu a fun i => hres' i ▸ htan i`. Set `φp : Localization.AtPrime p →+* Localization.AtPrime p` to `RingHom.id _`.

Establish `hφ : φp.comp (algebraMap R (Localization.AtPrime p)) = algebraMap R (Localization.AtPrime p)` using `RingHom.id_comp _`. Establish `hsp : spMap (algebraMap R (Localization.AtPrime p)) = spMap φp ≫ Chart.fB R (Localization.AtPrime p)` using `by show Spec.map (CommRingCat.ofHom (algebraMap R (Localization.AtPrime p))) = Spec.map (CommRingCat.ofHom φp) ≫ Spec.map (CommRingCat.ofHom (algebraMap R (Localization.AtPrime p)))`. Rewrite using `[← Spec.map_comp, ← CommRingCat.ofHom_comp, hφ]`. Establish `h' : IsGrpPullback G' G (spMap φp ≫ Chart.fB R (Localization.AtPrime p)) ψ` using `hsp ▸ hψ`. Establish `hG` using `Chart.isGrpPullback_factor (Chart.fB R (Localization.AtPrime p)) (spMap φp) h'`.

Establish `hv' : ∀ j, (v j).left ≫ ψ = spMap (Chart.dualMapR (algebraMap R (Localization.AtPrime p))) ≫ (w j).left` using `hv`. Use `Chart.isLieBasis_baseChange φp hG hbasis fun j => ?_` and prove the remaining obligations. Apply `pullback.hom_ext` to reduce the goal to its premises. Rewrite using `[Category.assoc, pullback.lift_fst, hv' j, Category.assoc]`. Establish `e` using `congrArg (fun q => Over.Hom.left q) (Chart.pushR_resP (G := G) p (w j))`.

Simplify using `only [Chart.pushR_left, Over.comp_left] at e`. Rewrite using `[e, ← Category.assoc]`. Use `congr 1`. Use `show Spec.map (CommRingCat.ofHom (Chart.dualMapR (algebraMap R (Localization.AtPrime p)))) = Spec.map (CommRingCat.ofHom (Chart.dualMapR φp)) ≫ Spec.map (CommRingCat.ofHom (Chart.dualMapR (algebraMap R (Localization.AtPrime p))))`. Rewrite using `[← Spec.map_comp, ← CommRingCat.ofHom_comp, ← Chart.dualMapR_comp, hφ]`.

Rewrite using `[Category.assoc, pullback.lift_snd, ← Category.assoc, Over.w (v j), Category.assoc]`. Rewrite using `[show (Chart.resP p (w j)).left ≫ pullback.snd G.hom (Chart.fB R (Localization.AtPrime p)) = (Chart.sp (R₀ := Localization.AtPrime p) (DualNumber (Localization.AtPrime p))).hom from Over.w (Chart.resP p (w j))]`. Use `show Spec.map (CommRingCat.ofHom (algebraMap (Localization.AtPrime p) (DualNumber (Localization.AtPrime p)))) ≫ Spec.map (CommRingCat.ofHom φp) = Spec.map (CommRingCat.ofHom (Chart.dualMapR φp)) ≫ Spec.map (CommRingCat.ofHom (algebraMap (Localization.AtPrime p) (DualNumber (Local …`. Rewrite using `[← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]`. Use `congr 2`.

Apply the tactic sequence `refine RingHom.ext fun r => TrivSqZeroExt.ext ?_ ?_ <;> simp [φp, Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl']`.
-/
theorem GlobalTheory.exists_tangent_isLieBasis_atPrime : ∀ {R : Type} [CommRing R] (G : Over (Sp R)) [GrpObj G], Smooth G.hom → ∀ (p : Ideal R) [p.IsPrime],
    ∃ (n : ℕ) (w : Fin n → (epsR R ⟶ G)), (∀ i, IsTangent (w i)) ∧
      (∀ (G' : Over (Sp (Localization.AtPrime p))) [GrpObj G'] (ψ : G'.left ⟶ G.left),
        IsGrpPullback G' G (spMap (algebraMap R (Localization.AtPrime p))) ψ →
        ∀ v : Fin n → (epsR (Localization.AtPrime p) ⟶ G'),
          (∀ i, GlobalTheory.IsVecOver (algebraMap R (Localization.AtPrime p)) ψ (w i) (v i)) → IsLieBasis v) := by
  intro R _ G _ hsm p _
  haveI := hsm
  have : ∀ s : R, Smooth (Chart.Gs G s).hom := fun s => show Smooth (pullback.snd G.hom _) from inferInstance
  have hGp : Smooth (Chart.Gp (G := G) p).hom := show Smooth (pullback.snd G.hom _) from inferInstance
  obtain ⟨n, u, hu⟩ := Chart.exists_isLieBasis (Chart.Gp (G := G) p) hGp
  have lift : ∀ i, ∃ q ∈ p.primeCompl, ∃ w : epsR R ⟶ G, IsTangent w ∧
      Chart.resP p w = Chart.spMap (Chart.scaleD (algebraMap R (Localization.AtPrime p) q)) ≫ u i := by
    intro i
    have hT : Chart.TanS (Chart.pushR G (u i)) := (Chart.isTan_iff_tanS p (u i)).mp ((Chart.isTan_iff _).mpr (hu.1 i))
    obtain ⟨q, hq, w, hw, he⟩ := Chart.tan_prime_lift p hT
    refine ⟨q, hq, w, (Chart.isTan_iff _).mp hw, Chart.pushR_inj G ?_⟩
    rw [Chart.pushR_resP, he, Chart.pushR_spMap]
    congr 2
  choose q hq w hw hres using lift
  refine ⟨n, w, hw, fun G' _ ψ hψ v hv => ?_⟩
  let a : Fin n → (Localization.AtPrime p)ˣ := fun i => (IsLocalization.map_units _ ⟨q i, hq i⟩).unit
  have hres' : ∀ i, Chart.resP p (w i) = Chart.spMap (Chart.scaleD (a i : Localization.AtPrime p)) ≫ u i := hres
  have htan : ∀ i, IsTangent (Chart.resP p (w i)) := fun i =>
    (Chart.isTan_iff _).mp ((Chart.isTan_iff_tanS p _).mpr (by
      rw [Chart.pushR_resP]; exact Chart.tanS_restrict _ ((Chart.isTan_iff _).mpr (hw i))))
  have hbasis : IsLieBasis (G := Chart.Gp (G := G) p) (fun i => Chart.resP p (w i)) := by
    have e : (fun i => Chart.resP p (w i)) = fun i => Chart.spMap (Chart.scaleD (a i : Localization.AtPrime p)) ≫ u i :=
      funext hres'
    rw [e]
    exact isLieBasis_scale hu a fun i => hres' i ▸ htan i
  let φp : Localization.AtPrime p →+* Localization.AtPrime p := RingHom.id _
  have hφ : φp.comp (algebraMap R (Localization.AtPrime p)) = algebraMap R (Localization.AtPrime p) := RingHom.id_comp _
  have hsp : spMap (algebraMap R (Localization.AtPrime p)) = spMap φp ≫ Chart.fB R (Localization.AtPrime p) := by
    show Spec.map (CommRingCat.ofHom (algebraMap R (Localization.AtPrime p))) = Spec.map (CommRingCat.ofHom φp) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (Localization.AtPrime p)))
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hφ]
  have h' : IsGrpPullback G' G (spMap φp ≫ Chart.fB R (Localization.AtPrime p)) ψ := hsp ▸ hψ
  have hG := Chart.isGrpPullback_factor (Chart.fB R (Localization.AtPrime p)) (spMap φp) h'
  have hv' : ∀ j, (v j).left ≫ ψ = spMap (Chart.dualMapR (algebraMap R (Localization.AtPrime p))) ≫ (w j).left := hv
  refine Chart.isLieBasis_baseChange φp hG hbasis fun j => ?_
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, hv' j, Category.assoc]
    have e := congrArg (fun q => Over.Hom.left q) (Chart.pushR_resP (G := G) p (w j))
    simp only [Chart.pushR_left, Over.comp_left] at e
    rw [e, ← Category.assoc]
    congr 1
    show Spec.map (CommRingCat.ofHom (Chart.dualMapR (algebraMap R (Localization.AtPrime p)))) =
      Spec.map (CommRingCat.ofHom (Chart.dualMapR φp)) ≫
        Spec.map (CommRingCat.ofHom (Chart.dualMapR (algebraMap R (Localization.AtPrime p))))
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← Chart.dualMapR_comp, hφ]
  · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, Over.w (v j), Category.assoc]
    rw [show (Chart.resP p (w j)).left ≫ pullback.snd G.hom (Chart.fB R (Localization.AtPrime p)) =
      (Chart.sp (R₀ := Localization.AtPrime p) (DualNumber (Localization.AtPrime p))).hom from Over.w (Chart.resP p (w j))]
    show Spec.map (CommRingCat.ofHom (algebraMap (Localization.AtPrime p) (DualNumber (Localization.AtPrime p)))) ≫
        Spec.map (CommRingCat.ofHom φp) =
      Spec.map (CommRingCat.ofHom (Chart.dualMapR φp)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap (Localization.AtPrime p) (DualNumber (Localization.AtPrime p))))
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    refine RingHom.ext fun r => TrivSqZeroExt.ext ?_ ?_ <;> simp [φp, Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl']
