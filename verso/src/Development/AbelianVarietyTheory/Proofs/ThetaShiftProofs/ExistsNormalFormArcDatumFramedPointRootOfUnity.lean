import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Formalism.LocalToGlobal.ProjectiveLattices.ArcTheta
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsSmulPtSmulPt
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTangentOfIsLieImage
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameChangeExistsUniqueOfSamePoint
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsTangentModuleUniversalGroupStatement
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsOpenImmersionJKPowerSeries
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsIntegralElemOfIsAlgebraicInt
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FrameChangeExistsUniqueInvertible
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FrameChangeComposeInvertBaseChangeTriangularStatement
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueConstantTangentVectorsAlongArcStatement
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.LieImgIffIsLieCombStatement
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThetaGeneratorEqRootOfUnityMulStatement

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames

namespace GlobalTheory.ArcQ.NormalForm

open MonoidalCategory CartesianMonoidalCategory MonObj

/- English proof (translation)
Use `show (toUnit X ≫ η[M]).left = _`. Simplify using the standard rewrite rules.
-/
theorem one_left_eq {T : Scheme.{0}} {X : Over T} {M : Over T} [GrpObj M] :
    (1 : X ⟶ M).left = X.hom ≫ η[M].left := by
  show (toUnit X ≫ η[M]).left = _
  simp

namespace ExFr

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {S : Type} [CommRing S] {x : Sp S ⟶ Xo.X} {t' : SAB H (Sp S)} (m : SABMap t' Xo.univ.t x)

/- English proof (translation)
Rewrite using `[one_left_eq]`. Use `m.cm.e_comm` as an intermediate fact. Rewrite `this` using `[m.base]`. Conclude with `this`.
-/
theorem one_eq : η[t'.G].left ≫ m.φ = (1 : Over.mk x ⟶ Xo.univ.t.G).left := by
  rw [one_left_eq]
  have := m.cm.e_comm
  rw [m.base] at this
  exact this

/- English proof (translation)
Establish `hw : w.left ≫ t'.G.hom = spMap (algebraMap S (DualNumber S))` using `Over.w w`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Apply `m.cart.1.hom_ext` to reduce the goal to its premises. Rewrite using `[Category.assoc]`.

Conclude with `h.2.trans (one_eq m).symm`. Establish `a : η[t'.G].left ≫ t'.G.hom = 𝟙 _` using `Over.w η[t'.G]`. Rewrite using `[Category.assoc, hw, a, ← spMap_comp]`. Establish `: (TrivSqZeroExt.fstHom S S S).toRingHom.comp (algebraMap S (DualNumber S)) = RingHom.id S`. Use extensionality with `r`.

Simplify using `[TrivSqZeroExt.algebraMap_eq_inl]`. Rewrite using `[this]`. Conclude with `Spec.map_id _`. Introduce `h`. Use `⟨by rw [Category.assoc, m.cart.1.w, ← Category.assoc, hw], ?_⟩` and prove the remaining obligations.

Rewrite using `[← Category.assoc]`. Conclude with `(congrArg (· ≫ m.φ) h).trans (one_eq m)`.
-/
theorem tan_iff (w : epsR S ⟶ t'.G) : IsTanAt x (w.left ≫ m.φ) ↔ IsTangent w := by
  have hw : w.left ≫ t'.G.hom = spMap (algebraMap S (DualNumber S)) := Over.w w
  constructor
  · intro h
    apply m.cart.1.hom_ext
    · rw [Category.assoc]; exact h.2.trans (one_eq m).symm
    · have a : η[t'.G].left ≫ t'.G.hom = 𝟙 _ := Over.w η[t'.G]
      rw [Category.assoc, hw, a, ← spMap_comp]
      have : (TrivSqZeroExt.fstHom S S S).toRingHom.comp (algebraMap S (DualNumber S)) = RingHom.id S := by
        ext r; simp [TrivSqZeroExt.algebraMap_eq_inl]
      rw [this]
      exact Spec.map_id _
  · intro h
    refine ⟨by rw [Category.assoc, m.cart.1.w, ← Category.assoc, hw], ?_⟩
    rw [← Category.assoc]
    exact (congrArg (· ≫ m.φ) h).trans (one_eq m)

/- English proof (translation)
Rewrite using `[← spMap_comp]`. Use `congr 1`. Apply the tactic sequence `ext r <;> simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]`.
-/
theorem scale_over (s : S) : spMap (epsScaleR s) ≫ spMap (algebraMap S (DualNumber S)) =
    spMap (algebraMap S (DualNumber S)) := by
  rw [← spMap_comp]
  congr 1
  ext r <;> simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]

/- English proof (translation)
Establish `hw : w.left ≫ t'.G.hom = spMap (algebraMap S (DualNumber S))` using `Over.w w`. Establish `e : (w.left ≫ m.φ) ≫ (Xo.univ.t.act.act a).left = (w ≫ t'.act.act a).left ≫ m.φ`. Rewrite using `[Over.comp_left, Category.assoc, Category.assoc, m.act]`. Rewrite using `[e]`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Apply `m.cart.1.hom_ext` to reduce the goal to its premises. Rewrite using `[Category.assoc]`. Conclude with `h`. Rewrite using `[Over.w, Category.assoc, hw, scale_over]`.

Both sides reduce to the same expression. Introduce `h`. Rewrite using `[h, Category.assoc]`. Both sides reduce to the same expression.
-/
theorem eig_iff (w : epsR S ⟶ t'.G) (a : 𝓞 E) (s : S) :
    (w.left ≫ m.φ) ≫ (Xo.univ.t.act.act a).left = spMap (epsMul s) ≫ w.left ≫ m.φ ↔
      (w ≫ t'.act.act a).left = spMap (epsScaleR s) ≫ w.left := by
  have hw : w.left ≫ t'.G.hom = spMap (algebraMap S (DualNumber S)) := Over.w w
  have e : (w.left ≫ m.φ) ≫ (Xo.univ.t.act.act a).left = (w ≫ t'.act.act a).left ≫ m.φ := by
    rw [Over.comp_left, Category.assoc, Category.assoc, m.act]
  rw [e]
  constructor
  · intro h
    apply m.cart.1.hom_ext
    · rw [Category.assoc]; exact h
    · rw [Over.w, Category.assoc, hw, scale_over]; rfl
  · intro h
    rw [h, Category.assoc]; rfl

/- English proof (translation)
Assemble the required witnesses or components as `⟨Over.homMk (m.cart.1.lift v T.hom hv) (m.cart.1.lift_snd _ _ _), m.cart.1.lift_fst _ _ _⟩`.
-/
theorem exists_lift {T : Over (Sp S)} (v : T.left ⟶ Xo.univ.t.G.left) (hv : v ≫ Xo.univ.t.G.hom = T.hom ≫ x) :
    ∃ w : T ⟶ t'.G, w.left ≫ m.φ = v :=
  ⟨Over.homMk (m.cart.1.lift v T.hom hv) (m.cart.1.lift_snd _ _ _), m.cart.1.lift_fst _ _ _⟩

/- English proof (translation)
Use `map_list_prod (pushHom m.cart (epsR S)) (List.ofFn u)` as an intermediate fact. Rewrite `this` using `[List.map_ofFn]`. Conclude with `congrArg (fun q => q.left) this`.
-/
theorem push_prod {n : ℕ} (u : Fin n → (epsR S ⟶ t'.G)) :
    ((List.ofFn u).prod).left ≫ m.φ = ((List.ofFn fun i => pushHom m.cart (epsR S) (u i)).prod).left := by
  have := map_list_prod (pushHom m.cart (epsR S)) (List.ofFn u)
  rw [List.map_ofFn] at this
  exact congrArg (fun q => q.left) this

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨u, hu, hw⟩ choose u' hu' using fun i => exists_lift m (T := epsR S) (u i).left (Over.w (u i))`. Establish `e : u = fun i => pushHom m.cart (epsR S) (u' i)` using `funext fun i => Over.OverMorphism.ext (hu' i).symm`. Use `⟨u', fun i => ?_, Over.OverMorphism.ext ?_⟩` and prove the remaining obligations. Apply `m.cart.1.hom_ext` to reduce the goal to its premises.

Rewrite using `[Category.assoc]`. Conclude with `(hu' i).trans (hu i)`. Establish `hv : (v i).left ≫ t'.G.hom = spMap (algebraMap S (DualNumber S))` using `Over.w (v i)`. Rewrite using `[Over.w, Category.assoc, hv, scale_over]`. Both sides reduce to the same expression.

Apply `m.cart.1.hom_ext` to reduce the goal to its premises. Rewrite `hw` using `[e]`. Conclude with `hw.symm.trans (push_prod m u').symm`. Rewrite using `[Over.w, Over.w]`. Introduce and unpack `⟨u, hu, rfl⟩`.

Use `⟨fun i => pushHom m.cart (epsR S) (u i), fun i => ?_, (push_prod m u).symm⟩` and prove the remaining obligations. Use `show (u i).left ≫ m.φ = _`. Rewrite using `[hu, Category.assoc]`. Both sides reduce to the same expression.
-/
theorem comb_iff {n : ℕ} (v : Fin n → (epsR S ⟶ t'.G)) (cf : Fin n → S) (w : epsR S ⟶ t'.G) :
    IsCombAt x (fun i => (v i).left ≫ m.φ) cf (w.left ≫ m.φ) ↔ IsLieComb cf v w := by
  constructor
  · rintro ⟨u, hu, hw⟩
    choose u' hu' using fun i => exists_lift m (T := epsR S) (u i).left (Over.w (u i))
    have e : u = fun i => pushHom m.cart (epsR S) (u' i) := funext fun i => Over.OverMorphism.ext (hu' i).symm
    refine ⟨u', fun i => ?_, Over.OverMorphism.ext ?_⟩
    · apply m.cart.1.hom_ext
      · rw [Category.assoc]; exact (hu' i).trans (hu i)
      · have hv : (v i).left ≫ t'.G.hom = spMap (algebraMap S (DualNumber S)) := Over.w (v i)
        rw [Over.w, Category.assoc, hv, scale_over]; rfl
    · apply m.cart.1.hom_ext
      · rw [e] at hw
        exact hw.symm.trans (push_prod m u').symm
      · rw [Over.w, Over.w]
  · rintro ⟨u, hu, rfl⟩
    refine ⟨fun i => pushHom m.cart (epsR S) (u i), fun i => ?_, (push_prod m u).symm⟩
    show (u i).left ≫ m.φ = _
    rw [hu, Category.assoc]; rfl

end ExFr

section Gt

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.TorusModel

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {T T' : Over (Spec (CommRingCat.of R))}

/- English proof (translation)
Establish `vv : ∀ χ y J, Good D.P.L y J → val (LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ (g.s χ) (g'.s χ)) (LB.invGen D.P.L _ _ (DegPre.cubAtT D T (cP D _ χ) g.b g'.b))) (𝟙 T.left) y J = cv g χ y J * cv g' χ y J * (th D y J (cP D _ χ) g.b g'.b)⁻¹` using `fun χ y J hJ => (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_mul hJ _ _ _) ((val_inv _ _).trans (congrArg (·⁻¹) (val_cubAtT hJ _ _ _))))`. Take `⟨g'', hb, hv⟩` from `exists_pt (g.b * g'.b) (fun χ => LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ (g.s χ) (g'.s χ)) (LB.invGen D.P.L _ _ (DegPre.cubAtT D T (cP D _ χ) g.b g'.b))) (fun χ => mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ (g.isGen _) (g'.isGen _)) (invGen_isGen _ _ _ _ (pul …`. Use `(prod_sum₂ (K := Fin 4 ⊕ Fin 4) (K' := thK) (U := U) _ (prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _ (prod_pt g.b χ h) (prod_pt g'.b χ h)) (prod_neg _ _ (prod_cub (cP D _ χ) g.b g'.b h))).trans ?_` and prove the remaining obligations. Rewrite using `[prod_pt, _root_.mul_assoc (cP D _ χ)]`. Apply `Additive.ofMul.injective` to reduce the goal to its premises.

Simplify using `only [ofMul_mul, ofMul_inv]`. Use the proof step `abel) (fun y J hJ => by`. Establish `C : IsCub (th D (T` using `T) y J) := isCub_cubV D.cub hJ`. Use `(vv 0 y J hJ).trans ?_` and prove the remaining obligations. Rewrite using `[cv_zero g hJ, cv_zero g' hJ, cPoint_zero, C.face]; simp) (fun χ χ' y J hJ => by`.

Establish `C : IsCub (th D (T` using `T) y J) := isCub_cubV D.cub hJ`. Establish `e₁` using `congrArg Additive.ofMul (cv_add g hJ χ χ')`. Establish `e₂` using `congrArg Additive.ofMul (cv_add g' hJ χ χ')`. Establish `e₃` using `congrArg Additive.ofMul (C.compat (cP D _ χ) (cP D _ χ') g.b g'.b)`. Use `(congrArg₂ (· * ·) (vv _ y J hJ) rfl).trans (Eq.trans ?_ (congrArg₂ (· * ·) (vv _ y J hJ) (vv _ y J hJ)).symm)` and prove the remaining obligations.

Rewrite using `[cPoint_add]`. Apply `Additive.ofMul.injective` to reduce the goal to its premises. Simplify using `only [ofMul_mul, ofMul_inv] at e₁ e₂ e₃ ⊢`. Take the linear combination `(norm := abel) e₁ + e₂ - e₃)`. Conclude with `⟨g'', (TorusModel.isAdd_iff _ _ _).2 ⟨hb, fun χ y J hJ => (congrArg₂ (· * ·) ((hv χ _ _ y J hJ).trans (vv χ y J hJ)) rfl).trans (inv_mul_cancel_right _ _)⟩⟩`.
-/
theorem exists_isAdd (g g' : GtPt D T) : ∃ g'', g.IsAdd g' g'' := by
  have vv : ∀ χ y J, Good D.P.L y J → val (LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ (g.s χ) (g'.s χ))
      (LB.invGen D.P.L _ _ (DegPre.cubAtT D T (cP D _ χ) g.b g'.b))) (𝟙 T.left) y J =
      cv g χ y J * cv g' χ y J * (th D y J (cP D _ χ) g.b g'.b)⁻¹ := fun χ y J hJ =>
    (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_mul hJ _ _ _)
      ((val_inv _ _).trans (congrArg (·⁻¹) (val_cubAtT hJ _ _ _))))
  obtain ⟨g'', hb, hv⟩ := exists_pt (g.b * g'.b) (fun χ => LB.mulGen D.P.L _ _ _ _
      (LB.mulGen D.P.L _ _ _ _ (g.s χ) (g'.s χ)) (LB.invGen D.P.L _ _ (DegPre.cubAtT D T (cP D _ χ) g.b g'.b)))
    (fun χ => mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ (g.isGen _) (g'.isGen _))
      (invGen_isGen _ _ _ _ (pullGen_isGen _ _ _ _ D.cub.isGen _))) (fun χ U _ h => by
      refine (prod_sum₂ (K := Fin 4 ⊕ Fin 4) (K' := thK) (U := U) _
        (prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _ (prod_pt g.b χ h) (prod_pt g'.b χ h))
        (prod_neg _ _ (prod_cub (cP D _ χ) g.b g'.b h))).trans ?_
      rw [prod_pt, _root_.mul_assoc (cP D _ χ)]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel) (fun y J hJ => by
      have C : IsCub (th D (T := T) y J) := isCub_cubV D.cub hJ
      refine (vv 0 y J hJ).trans ?_
      rw [cv_zero g hJ, cv_zero g' hJ, cPoint_zero, C.face]; simp) (fun χ χ' y J hJ => by
      have C : IsCub (th D (T := T) y J) := isCub_cubV D.cub hJ
      have e₁ := congrArg Additive.ofMul (cv_add g hJ χ χ')
      have e₂ := congrArg Additive.ofMul (cv_add g' hJ χ χ')
      have e₃ := congrArg Additive.ofMul (C.compat (cP D _ χ) (cP D _ χ') g.b g'.b)
      refine (congrArg₂ (· * ·) (vv _ y J hJ) rfl).trans (Eq.trans ?_ (congrArg₂ (· * ·) (vv _ y J hJ) (vv _ y J hJ)).symm)
      rw [cPoint_add]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv] at e₁ e₂ e₃ ⊢
      linear_combination (norm := abel) e₁ + e₂ - e₃)
  exact ⟨g'', (TorusModel.isAdd_iff _ _ _).2 ⟨hb, fun χ y J hJ =>
    (congrArg₂ (· * ·) ((hv χ _ _ y J hJ).trans (vv χ y J hJ)) rfl).trans (inv_mul_cancel_right _ _)⟩⟩

/- English proof (translation)
Establish `vv : ∀ χ y J, Good D.P.L y J → val (LB.pullGen D.P.L _ _ (g.s χ) k.left) (𝟙 _) y J = val (g.s χ) k.left y J` using `fun χ y J hJ => (val_pull hJ _ _ _).trans (by rw [Category.id_comp])`. Take `⟨g', hb, hv⟩` from `exists_pt (k ≫ g.b) (fun χ => LB.pullGen D.P.L _ _ (g.s χ) k.left) (fun χ => pullGen_isGen _ _ _ _ (g.isGen χ) _) (fun χ U _ h => (FormalPoint.prod_gtφT k g.b χ h).trans (prod_pt _ χ h).symm) (fun y J hJ => (vv 0 y J hJ).trans ((val_corr hJ g.s_zero _).trans (val_one _))) (fun χ …`. Rewrite using `[vv _ y J hJ, vv _ y J hJ, vv _ y J hJ]`. Conclude with `FormalPoint.val_s_add g k hJ χ χ')`. Conclude with `⟨g', (isPull_iff _ _ _).2 ⟨hb, fun χ y J hJ => (hv χ _ _ y J hJ).trans (vv χ y J hJ)⟩⟩`.
-/
theorem exists_isPull (k : T' ⟶ T) (g : GtPt D T) : ∃ g' : GtPt D T', GtPt.IsPull k.left g g' := by
  have vv : ∀ χ y J, Good D.P.L y J → val (LB.pullGen D.P.L _ _ (g.s χ) k.left) (𝟙 _) y J =
      val (g.s χ) k.left y J := fun χ y J hJ => (val_pull hJ _ _ _).trans (by rw [Category.id_comp])
  obtain ⟨g', hb, hv⟩ := exists_pt (k ≫ g.b) (fun χ => LB.pullGen D.P.L _ _ (g.s χ) k.left)
    (fun χ => pullGen_isGen _ _ _ _ (g.isGen χ) _)
    (fun χ U _ h => (FormalPoint.prod_gtφT k g.b χ h).trans (prod_pt _ χ h).symm)
    (fun y J hJ => (vv 0 y J hJ).trans ((val_corr hJ g.s_zero _).trans (val_one _)))
    (fun χ χ' y J hJ => by
      rw [vv _ y J hJ, vv _ y J hJ, vv _ y J hJ]
      exact FormalPoint.val_s_add g k hJ χ χ')
  exact ⟨g', (isPull_iff _ _ _).2 ⟨hb, fun χ y J hJ => (hv χ _ _ y J hJ).trans (vv χ y J hJ)⟩⟩

/- English proof (translation)
Use `choose u hu using fun i => exists_isPull (D := D) (T := epsR R) (T' := epsR R) (Over.homMk (spMap (epsScaleR (cf i))) (ExFr.scale_over _)) (e i)`. Take `⟨z, hz⟩` from `ArcLieCompare.exists_isZero (D := D) (epsR R)`. Use `choose add hadd using fun g g' : GtPt D (epsR R) => exists_isAdd g g'`. Set `p : Fin (m + 1) → GtPt D (epsR R)` to `fun i => Fin.induction z (fun j q => add q (u j)) i`. Conclude with `⟨p (Fin.last m), u, p, hu, hz, fun i => hadd _ _, rfl⟩`.
-/
theorem exists_gtComb {m : ℕ} (cf : Fin m → R) (e : Fin m → GtPt D (epsR R)) : ∃ ν, GtComb cf e ν := by
  choose u hu using fun i => exists_isPull (D := D) (T := epsR R) (T' := epsR R)
    (Over.homMk (spMap (epsScaleR (cf i))) (ExFr.scale_over _)) (e i)
  obtain ⟨z, hz⟩ := ArcLieCompare.exists_isZero (D := D) (epsR R)
  choose add hadd using fun g g' : GtPt D (epsR R) => exists_isAdd g g'
  let p : Fin (m + 1) → GtPt D (epsR R) := fun i => Fin.induction z (fun j q => add q (u j)) i
  exact ⟨p (Fin.last m), u, p, hu, hz, fun i => hadd _ _, rfl⟩

end Gt

section Lie

variable {S : Type} [CommRing S] {G : Over (Sp S)} [GrpObj G]

def sc (s : S) : epsR S ⟶ epsR S := Over.homMk (spMap (epsScaleR s)) (ExFr.scale_over s)

/- English proof (translation)
Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Use `show spMap (epsScaleR s) ≫ spMap (epsScaleR t) = spMap (epsScaleR (s * t))`. Rewrite using `[← spMap_comp]`. Use `congr 1`. Apply the tactic sequence `ext r <;> simp [epsScaleR, _root_.mul_assoc]`.
-/
theorem sc_mul (s t : S) : sc s ≫ sc t = sc (s * t) := by
  apply Over.OverMorphism.ext
  show spMap (epsScaleR s) ≫ spMap (epsScaleR t) = spMap (epsScaleR (s * t))
  rw [← spMap_comp]
  congr 1
  ext r <;> simp [epsScaleR, _root_.mul_assoc]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨u, hu, rfl⟩`. Rewrite using `[show u = fun i => sc (cf i) ≫ v i from funext fun i => Over.OverMorphism.ext (hu i)]`. Introduce and unpack `rfl`. Conclude with `⟨_, fun i => rfl, rfl⟩`.
-/
theorem isLieComb_iff {n : ℕ} (cf : Fin n → S) (v : Fin n → (epsR S ⟶ G)) (w : epsR S ⟶ G) :
    IsLieComb cf v w ↔ w = (List.ofFn fun i => sc (cf i) ≫ v i).prod := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    rw [show u = fun i => sc (cf i) ≫ v i from funext fun i => Over.OverMorphism.ext (hu i)]
  · rintro rfl
    exact ⟨_, fun i => rfl, rfl⟩

/- English proof (translation)
Establish `h0 : spMap (epsScaleR (0 : S)) = spMap (algebraMap S (DualNumber S)) ≫ spMap (TrivSqZeroExt.fstHom S S S).toRingHom`. Rewrite using `[← spMap_comp]`. Use `congr 1`. Apply the tactic sequence `ext r <;> simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]`. Establish `h1 : spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ spMap (algebraMap S (DualNumber S)) = 𝟙 _` using `ArcLieCompare.epsRed_hom`.

Establish `h2 : (1 : epsR S ⟶ G).left = spMap (algebraMap S (DualNumber S)) ≫ η[G].left` using `one_left_eq`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Use `show spMap (epsScaleR (0 : S)) ≫ w.left = _`.

Rewrite using `[h2, h0, Category.assoc]`. Conclude with `congrArg (_ ≫ ·) h`. Introduce `h`. Establish `h3 : spMap (epsScaleR (0 : S)) ≫ w.left = _` using `(congrArg (·.left) h).trans h2`. Establish `h4` using `congrArg (spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ ·) h3`.

Simplify using `only [h0, ← Category.assoc, h1, Category.id_comp] at h4`. Conclude with `h4`.
-/
theorem isTangent_iff (w : epsR S ⟶ G) : IsTangent w ↔ sc 0 ≫ w = 1 := by
  have h0 : spMap (epsScaleR (0 : S)) = spMap (algebraMap S (DualNumber S)) ≫
      spMap (TrivSqZeroExt.fstHom S S S).toRingHom := by
    rw [← spMap_comp]
    congr 1
    ext r <;> simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]
  have h1 : spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ spMap (algebraMap S (DualNumber S)) = 𝟙 _ :=
    ArcLieCompare.epsRed_hom
  have h2 : (1 : epsR S ⟶ G).left = spMap (algebraMap S (DualNumber S)) ≫ η[G].left :=
    one_left_eq
  constructor
  · intro h
    apply Over.OverMorphism.ext
    show spMap (epsScaleR (0 : S)) ≫ w.left = _
    rw [h2, h0, Category.assoc]
    exact congrArg (_ ≫ ·) h
  · intro h
    have h3 : spMap (epsScaleR (0 : S)) ≫ w.left = _ := (congrArg (·.left) h).trans h2
    have h4 := congrArg (spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ ·) h3
    simp only [h0, ← Category.assoc, h1, Category.id_comp] at h4
    exact h4

/- English proof (translation)
Simplify using `only [isLieComb_iff, isTangent_iff, List.prod_ofFn] at hw hU h ⊢`. Establish `pre : ∀ (s : S) (v : Fin n → (epsR S ⟶ G)), sc s ≫ ∏ i, v i = ∏ i, sc s ≫ v i` using `fun s v => map_prod (preHom (G := G) (sc s)) v _`. Establish `hc : ∏ j, sc (0 : S) ≫ u j = 1`. Rewrite `hU` using `[h, pre]`. Simplify `hU` using `only [← Category.assoc, sc_mul, zero_mul]`.

Establish `key : ∀ (s : S) k, (sc s ≫ w k) * (sc 0 ≫ u k) = sc s ≫ u k` using `fun s k => by`. Rewrite using `[hw k, pre, ← Finset.mul_prod_erase _ _ (Finset.mem_univ k), _root_.mul_assoc]`. Rewrite `hc` using `[← Finset.prod_erase_mul _ _ (Finset.mem_univ k)]`. Rewrite using `[Finset.prod_congr rfl (g := fun j => sc (0 : S) ≫ u j) fun j hj => by`. Rewrite using `[← Category.assoc, sc_mul, Pi.single_eq_of_ne (Finset.ne_of_mem_erase hj), mul_zero], hc,`.

Use the proof step `← Category.assoc, sc_mul, Pi.single_eq_same, _root_.mul_one, _root_.mul_one]`. Use `⟨fun k => mul_eq_right.1 (key 0 k), ?_⟩` and prove the remaining obligations. Rewrite using `[h, ← Finset.prod_congr rfl fun k _ => key (X k) k, Finset.prod_mul_distrib, hc, _root_.mul_one]`.
-/
theorem tangent_parts [IsCommMonObj G] {n : ℕ} (u w : Fin n → (epsR S ⟶ G))
    (hw : ∀ k, IsLieComb (Pi.single k (1 : S)) u (w k)) (X : Fin n → S) (U : epsR S ⟶ G) (hU : IsTangent U)
    (h : IsLieComb X u U) : (∀ k, IsTangent (w k)) ∧ IsLieComb X w U := by
  simp only [isLieComb_iff, isTangent_iff, List.prod_ofFn] at hw hU h ⊢
  have pre : ∀ (s : S) (v : Fin n → (epsR S ⟶ G)), sc s ≫ ∏ i, v i = ∏ i, sc s ≫ v i := fun s v =>
    map_prod (preHom (G := G) (sc s)) v _
  have hc : ∏ j, sc (0 : S) ≫ u j = 1 := by
    rw [h, pre] at hU
    simpa only [← Category.assoc, sc_mul, zero_mul] using hU
  have key : ∀ (s : S) k, (sc s ≫ w k) * (sc 0 ≫ u k) = sc s ≫ u k := fun s k => by
    rw [hw k, pre, ← Finset.mul_prod_erase _ _ (Finset.mem_univ k), _root_.mul_assoc]
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ k)] at hc
    rw [Finset.prod_congr rfl (g := fun j => sc (0 : S) ≫ u j) fun j hj => by
      rw [← Category.assoc, sc_mul, Pi.single_eq_of_ne (Finset.ne_of_mem_erase hj), mul_zero], hc,
      ← Category.assoc, sc_mul, Pi.single_eq_same, _root_.mul_one, _root_.mul_one]
  refine ⟨fun k => mul_eq_right.1 (key 0 k), ?_⟩
  rw [h, ← Finset.prod_congr rfl fun k _ => key (X k) k, Finset.prod_mul_distrib, hc, _root_.mul_one]

variable {A : Type} [CommRing A] {G₀ : Over (Sp A)} [GrpObj G₀] {f : A →+* S} {F : G.left ⟶ G₀.left}
  (hF : IsGrpPullback G G₀ (spMap f) F)

/- English proof (translation)
Rewrite using `[← spMap_comp, ← spMap_comp]`. Use `congr 1`. Apply the tactic sequence `ext r <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]`.
-/
theorem dual_over (f : A →+* S) : spMap (dualMap f) ≫ spMap (algebraMap A (DualNumber A)) =
    spMap (algebraMap S (DualNumber S)) ≫ spMap f := by
  rw [← spMap_comp, ← spMap_comp]
  congr 1
  ext r <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

/- English proof (translation)
Rewrite using `[← spMap_comp, ← spMap_comp]`. Use `congr 1`. Apply the tactic sequence `ext r <;> simp [dualMap, epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]`.
-/
theorem dual_scale (f : A →+* S) (a : A) : spMap (dualMap f) ≫ spMap (epsScaleR a) =
    spMap (epsScaleR (f a)) ≫ spMap (dualMap f) := by
  rw [← spMap_comp, ← spMap_comp]
  congr 1
  ext r <;> simp [dualMap, epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]

include hF in
/- English proof (translation)
Establish `hv : v.left ≫ G₀.hom = spMap (algebraMap A (DualNumber A))` using `Over.w v`. Establish `e : (spMap (dualMap f) ≫ v.left) ≫ G₀.hom = (epsR S).hom ≫ spMap f`. Rewrite using `[Category.assoc, hv]`. Conclude with `dual_over f`. Conclude with `⟨Over.homMk (hF.1.lift _ _ e) (hF.1.lift_snd _ _ _), hF.1.lift_fst _ _ _⟩`.
-/
theorem exists_baseChange (v : epsR A ⟶ G₀) : ∃ u : epsR S ⟶ G, u.left ≫ F = spMap (dualMap f) ≫ v.left := by
  have hv : v.left ≫ G₀.hom = spMap (algebraMap A (DualNumber A)) := Over.w v
  have e : (spMap (dualMap f) ≫ v.left) ≫ G₀.hom = (epsR S).hom ≫ spMap f := by
    rw [Category.assoc, hv]; exact dual_over f
  exact ⟨Over.homMk (hF.1.lift _ _ e) (hF.1.lift_snd _ _ _), hF.1.lift_fst _ _ _⟩

include hF in
/- English proof (translation)
Rewrite `h`, the goal using `[isLieComb_iff]`. Set `U : Over.mk ((epsR S).hom ≫ spMap f) ⟶ epsR A` to `Over.homMk (spMap (dualMap f)) (dual_over f)`. Establish `e₁` using `map_list_prod (pushHom hF (epsR S)) (List.ofFn fun i => sc (f (cf i)) ≫ u i)`. Establish `e₂` using `map_list_prod (preHom (G := G₀) U) (List.ofFn fun i => sc (cf i) ≫ v i)`. Rewrite `e₁`, `e₂` using `[List.map_ofFn]`.

Establish `e₃ : (pushHom hF (epsR S)) ∘ (fun i => sc (f (cf i)) ≫ u i) = (preHom (G` using `G₀) U) ∘ fun i => sc (cf i) ≫ v i :=`. Use function extensionality and compare the values at `fun i => Over.OverMorphism.ext (by show (spMap (epsScaleR (f (cf i))) ≫ (u i).left) ≫ F = spMap (dualMap f) ≫ spMap (epsScaleR (cf i)) ≫ (v i).left`. Rewrite using `[Category.assoc, hu, ← Category.assoc, ← Category.assoc, dual_scale])`. Rewrite `e₁` using `[e₃, ← e₂, ← h]`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises.

Apply `hF.1.hom_ext` to reduce the goal to its premises. Conclude with `hw.trans (congrArg (·.left) e₁).symm`. Rewrite using `[Over.w, Over.w]`.
-/
theorem isLieComb_baseChange {n : ℕ} {cf : Fin n → A} {v : Fin n → (epsR A ⟶ G₀)} {w : epsR A ⟶ G₀}
    {u : Fin n → (epsR S ⟶ G)} {w' : epsR S ⟶ G} (hu : ∀ i, (u i).left ≫ F = spMap (dualMap f) ≫ (v i).left)
    (hw : w'.left ≫ F = spMap (dualMap f) ≫ w.left) (h : IsLieComb cf v w) : IsLieComb (fun i => f (cf i)) u w' := by
  rw [isLieComb_iff] at h ⊢
  let U : Over.mk ((epsR S).hom ≫ spMap f) ⟶ epsR A := Over.homMk (spMap (dualMap f)) (dual_over f)
  have e₁ := map_list_prod (pushHom hF (epsR S)) (List.ofFn fun i => sc (f (cf i)) ≫ u i)
  have e₂ := map_list_prod (preHom (G := G₀) U) (List.ofFn fun i => sc (cf i) ≫ v i)
  rw [List.map_ofFn] at e₁ e₂
  have e₃ : (pushHom hF (epsR S)) ∘ (fun i => sc (f (cf i)) ≫ u i) = (preHom (G := G₀) U) ∘ fun i => sc (cf i) ≫ v i :=
    funext fun i => Over.OverMorphism.ext (by
      show (spMap (epsScaleR (f (cf i))) ≫ (u i).left) ≫ F =
        spMap (dualMap f) ≫ spMap (epsScaleR (cf i)) ≫ (v i).left
      rw [Category.assoc, hu, ← Category.assoc, ← Category.assoc, dual_scale])
  rw [e₃, ← e₂, ← h] at e₁
  apply Over.OverMorphism.ext
  apply hF.1.hom_ext
  · exact hw.trans (congrArg (·.left) e₁).symm
  · rw [Over.w, Over.w]

include hF in
/- English proof (translation)
Rewrite `h`, the goal using `[isTangent_iff]`. Establish `h1 : IsLieComb (n` using `0) Fin.elim0 Fin.elim0 (sc 0 ≫ w) := by rw [isLieComb_iff, h]; simp`. Establish `h2` using `isLieComb_baseChange hF (u := Fin.elim0) (w' := sc 0 ≫ w') (fun i => i.elim0) (by show (spMap (epsScaleR (0 : S)) ≫ w'.left) ≫ F = spMap (dualMap f) ≫ spMap (epsScaleR 0) ≫ w.left`. Rewrite using `[Category.assoc, hw, ← Category.assoc, ← Category.assoc, dual_scale, map_zero]) h1`. Rewrite `h2` using `[isLieComb_iff]`.

Simplify using `using h2`.
-/
theorem isTangent_baseChange {w : epsR A ⟶ G₀} {w' : epsR S ⟶ G}
    (hw : w'.left ≫ F = spMap (dualMap f) ≫ w.left) (h : IsTangent w) : IsTangent w' := by
  rw [isTangent_iff] at h ⊢
  have h1 : IsLieComb (n := 0) Fin.elim0 Fin.elim0 (sc 0 ≫ w) := by rw [isLieComb_iff, h]; simp
  have h2 := isLieComb_baseChange hF (u := Fin.elim0) (w' := sc 0 ≫ w') (fun i => i.elim0) (by
    show (spMap (epsScaleR (0 : S)) ≫ w'.left) ≫ F = spMap (dualMap f) ≫ spMap (epsScaleR 0) ≫ w.left
    rw [Category.assoc, hw, ← Category.assoc, ← Category.assoc, dual_scale, map_zero]) h1
  rw [isLieComb_iff] at h2
  simpa using h2

end Lie

section Theta

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {S : Type} [CommRing S] {x : Sp S ⟶ Xo.X} {t : SAB H (Sp S)} (m : SABMap t Xo.univ.t x)

def Reads (s : LB.Sec (PPx x)) (s₁ : LB.Sec (Xo.univ.t.PP.L.pull m.φ)) : Prop :=
  ∀ g : t.G.left ⟶ Gx x, g ≫ (snd (Over.mk x) Xo.univ.t.G).left = m.φ →
    g ≫ (fst (Over.mk x) Xo.univ.t.G).left = t.G.hom →
    ∀ j (h : (Xo.univ.t.PP.L.pull m.φ).U j ≤ g ⁻¹ᵁ (PPx x).U (fun _ => j PUnit.unit)),
      s₁.f j = (g.appLE _ _ h).hom (s.f (fun _ => j PUnit.unit))

/- English proof (translation)
Set `a₀ : Over.mk (t.G.hom ≫ x) ⟶ Over.mk x` to `Over.homMk t.G.hom rfl`. Set `b₀ : Over.mk (t.G.hom ≫ x) ⟶ Xo.univ.t.G` to `Over.homMk m.φ m.cart.1.w`. Conclude with `⟨(lift a₀ b₀).left, congrArg (fun q => q.left) (lift_snd a₀ b₀), congrArg (fun q => q.left) (lift_fst a₀ b₀)⟩`.
-/
theorem exists_canon : ∃ g : t.G.left ⟶ Gx x, g ≫ (snd (Over.mk x) Xo.univ.t.G).left = m.φ ∧
    g ≫ (fst (Over.mk x) Xo.univ.t.G).left = t.G.hom := by
  let a₀ : Over.mk (t.G.hom ≫ x) ⟶ Over.mk x := Over.homMk t.G.hom rfl
  let b₀ : Over.mk (t.G.hom ≫ x) ⟶ Xo.univ.t.G := Over.homMk m.φ m.cart.1.w
  exact ⟨(lift a₀ b₀).left, congrArg (fun q => q.left) (lift_snd a₀ b₀), congrArg (fun q => q.left) (lift_fst a₀ b₀)⟩

/- English proof (translation)
Introduce `y hy` and use `Set.mem_iInter.2 fun _ => (congrArg (fun q => q y ∈ Xo.univ.t.PP.L.U (j PUnit.unit)) hg).mpr (mem_pull.1 hy)`.
-/
theorem canon_le {g : t.G.left ⟶ Gx x} (hg : g ≫ (snd (Over.mk x) Xo.univ.t.G).left = m.φ)
    (j : PUnit → Xo.univ.t.PP.L.ι) : (Xo.univ.t.PP.L.pull m.φ).U j ≤ g ⁻¹ᵁ (PPx x).U (fun _ => j PUnit.unit) :=
  fun y hy => Set.mem_iInter.2 fun _ => (congrArg (fun q => q y ∈ Xo.univ.t.PP.L.U (j PUnit.unit)) hg).mpr
    (mem_pull.1 hy)

/- English proof (translation)
Take `⟨g, hs, hf⟩` from `exists_canon m`. Use `⟨⟨fun (j : PUnit → Xo.univ.t.PP.L.ι) => (g.appLE _ _ (canon_le m hs j)).hom (s.f (fun _ => j PUnit.unit)), fun (j j' : PUnit → Xo.univ.t.PP.L.ι) => fn_ext fun y hy => ?_⟩, fun g' hs' hf' j h => ?_⟩` and prove the remaining obligations. Establish `a : (𝟙 _ ≫ g) y ∈ (PPx x).U (fun _ => j PUnit.unit)` using `canon_le m hs j hy.1`. Establish `a' : (𝟙 _ ≫ g) y ∈ (PPx x).U (fun _ => j' PUnit.unit)` using `canon_le m hs j' hy.2`. Establish `gg : gm (𝟙 _ ≫ g) y _ ((PPx x).g (fun _ => j PUnit.unit) (fun _ => j' PUnit.unit)) = gm (𝟙 _ ≫ m.φ) y (Xo.univ.t.PP.L.U (j PUnit.unit) ⊓ Xo.univ.t.PP.L.U (j' PUnit.unit)) (Xo.univ.t.PP.L.g (j PUnit.unit) (j' PUnit.unit))` using `(gm_linComb Xo.univ.t.PP.L (K := Fin 1) (fun _ => (snd (Over.mk x) Xo.univ.t.G).left) (fun _ => 1) (𝟙 _ ≫ g) y _ _ a a').trans (by rw [Fin.prod_univ_one, zpow_one, Category.assoc, hs])`.

Conclude with `(gs_res _ y _ hy _).trans ((gs_appLE g _ _ _ (𝟙 _) y hy.1 _).trans ((gs_compat s (𝟙 _ ≫ g) y a a').trans (Eq.symm ((gs_mul _ y _ hy _ _).trans (congrArg₂ (· * ·) ((gs_unit _ y _ hy _).trans (congrArg Units.val ((gm_pull_g _ m.φ (𝟙 _) y j j' hy.1 hy.2).trans gg.symm))) ((gs_res _ …`. Take `rfl : g' = g` from `pullback.hom_ext (hf'.trans hf.symm) (hs'.trans hs.symm)`. Both sides reduce to the same expression.
-/
theorem exists_reads (s : LB.Sec (PPx x)) : ∃ s₁, Reads m s s₁ := by
  obtain ⟨g, hs, hf⟩ := exists_canon m
  refine ⟨⟨fun (j : PUnit → Xo.univ.t.PP.L.ι) => (g.appLE _ _ (canon_le m hs j)).hom (s.f (fun _ => j PUnit.unit)),
    fun (j j' : PUnit → Xo.univ.t.PP.L.ι) => fn_ext fun y hy => ?_⟩, fun g' hs' hf' j h => ?_⟩
  · have a : (𝟙 _ ≫ g) y ∈ (PPx x).U (fun _ => j PUnit.unit) := canon_le m hs j hy.1
    have a' : (𝟙 _ ≫ g) y ∈ (PPx x).U (fun _ => j' PUnit.unit) := canon_le m hs j' hy.2
    have gg : gm (𝟙 _ ≫ g) y _ ((PPx x).g (fun _ => j PUnit.unit) (fun _ => j' PUnit.unit)) =
        gm (𝟙 _ ≫ m.φ) y (Xo.univ.t.PP.L.U (j PUnit.unit) ⊓ Xo.univ.t.PP.L.U (j' PUnit.unit))
          (Xo.univ.t.PP.L.g (j PUnit.unit) (j' PUnit.unit)) :=
      (gm_linComb Xo.univ.t.PP.L (K := Fin 1) (fun _ => (snd (Over.mk x) Xo.univ.t.G).left) (fun _ => 1)
        (𝟙 _ ≫ g) y _ _ a a').trans (by rw [Fin.prod_univ_one, zpow_one, Category.assoc, hs])
    exact (gs_res _ y _ hy _).trans ((gs_appLE g _ _ _ (𝟙 _) y hy.1 _).trans ((gs_compat s (𝟙 _ ≫ g) y a a').trans
      (Eq.symm ((gs_mul _ y _ hy _ _).trans (congrArg₂ (· * ·)
        ((gs_unit _ y _ hy _).trans (congrArg Units.val ((gm_pull_g _ m.φ (𝟙 _) y j j' hy.1 hy.2).trans gg.symm)))
        ((gs_res _ y _ hy _).trans (gs_appLE g _ _ _ (𝟙 _) y hy.2 _)))))))
  · obtain rfl : g' = g := pullback.hom_ext (hf'.trans hf.symm) (hs'.trans hs.symm)
    rfl

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h y j k h₁ h₂`. Establish `hy : y ∈ (L.pull F).U j ⊓ L'.U k` using `⟨h₁, h₂⟩`. Conclude with `(gs_res (𝟙 _) y _ hy _).symm.trans ((congrArg (gs (𝟙 _) y _) (h j k)).trans ((gs_mul _ y _ hy _ _).trans (congrArg₂ (· * ·) (gs_unit (𝟙 _) y _ hy _) (gs_res _ y _ hy _))))`. Introduce `h (j : PUnit → L.ι) k`.

Conclude with `fn_ext fun y hy => (gs_res _ y _ hy _).trans ((h y j k hy.1 hy.2).trans (Eq.symm ((gs_mul _ y _ hy _ _).trans (congrArg₂ (· * ·) (gs_unit (𝟙 _) y _ hy _) (gs_res _ y _ hy _)))))`.
-/
theorem isoMaps_iff {X : Scheme.{0}} {L : LB X} {X' : Scheme.{0}} {L' : LB X'} {F : X' ⟶ X}
    (w : LB.Iso L' (L.pull F)) (σ : LB.Sec L') (s : LB.Sec (L.pull F)) :
    IsoMaps w σ s ↔ ∀ (y : X') (j : PUnit → L.ι) k, y ∈ (L.pull F).U j → y ∈ L'.U k →
      gs (𝟙 _) y _ (s.f j) = (gw w (𝟙 _) y (j PUnit.unit) k).val * gs (𝟙 _) y _ (σ.f k) := by
  constructor
  · intro h y j k h₁ h₂
    have hy : y ∈ (L.pull F).U j ⊓ L'.U k := ⟨h₁, h₂⟩
    exact (gs_res (𝟙 _) y _ hy _).symm.trans ((congrArg (gs (𝟙 _) y _) (h j k)).trans ((gs_mul _ y _ hy _ _).trans
      (congrArg₂ (· * ·) (gs_unit (𝟙 _) y _ hy _) (gs_res _ y _ hy _))))
  · intro h (j : PUnit → L.ι) k
    exact fn_ext fun y hy => (gs_res _ y _ hy _).trans ((h y j k hy.1 hy.2).trans (Eq.symm ((gs_mul _ y _ hy _ _).trans
      (congrArg₂ (· * ·) (gs_unit (𝟙 _) y _ hy _) (gs_res _ y _ hy _)))))

/- English proof (translation)
Establish `le : ∀ j, F ⁻¹ᵁ L.U j ≤ (L.pull F).U (fun _ => j)` using `fun j y hy => mem_pull.2 hy`. Take `⟨σ, hσ⟩` from `sec_down ((isGen_iff w).1 hw) hL hL' (fun j => resG X' (le j) (s.f (fun _ => j))) fun y j j' h₁ h₂ => (gs_res (𝟙 _) y _ h₁ _).trans ((gs_compat s (𝟙 _) y (le j h₁) (le j' h₂)).trans (congrArg₂ (· * ·) (congrArg Units.val ((gm_pull_g L F (𝟙 _) y _ _ (le j h₁) (le j' h₂)).trans (by …`. Conclude with `⟨σ, (isoMaps_iff w σ s).2 fun y j k h₁ h₂ => (gs_res (𝟙 _) y (le _) (mem_pull.1 h₁) _).symm.trans (hσ _ (𝟙 _) y (j PUnit.unit) k (mem_pull.1 h₁) h₂)⟩`.
-/
theorem exists_isoMaps {X : Scheme.{0}} {L : LB X} {X' : Scheme.{0}} {L' : LB X'} {F : X' ⟶ X}
    (w : LB.Iso L' (L.pull F)) (hw : w.IsGen) (hL : L.IsLB) (hL' : L'.IsLB) (s : LB.Sec (L.pull F)) :
    ∃ σ, IsoMaps w σ s := by
  have le : ∀ j, F ⁻¹ᵁ L.U j ≤ (L.pull F).U (fun _ => j) := fun j y hy => mem_pull.2 hy
  obtain ⟨σ, hσ⟩ := sec_down ((isGen_iff w).1 hw) hL hL' (fun j => resG X' (le j) (s.f (fun _ => j)))
    fun y j j' h₁ h₂ => (gs_res (𝟙 _) y _ h₁ _).trans ((gs_compat s (𝟙 _) y (le j h₁) (le j' h₂)).trans
      (congrArg₂ (· * ·) (congrArg Units.val ((gm_pull_g L F (𝟙 _) y _ _ (le j h₁) (le j' h₂)).trans
        (by rw [Category.id_comp]))) (gs_res (𝟙 _) y _ h₂ _).symm))
  exact ⟨σ, (isoMaps_iff w σ s).2 fun y j k h₁ h₂ => (gs_res (𝟙 _) y (le _) (mem_pull.1 h₁) _).symm.trans
    (hσ _ (𝟙 _) y (j PUnit.unit) k (mem_pull.1 h₁) h₂)⟩

/- English proof (translation)
Take `⟨g, gs', gf⟩` from `exists_canon m`. Rewrite `hw`, the goal using `[isoMaps_iff]`. Introduce `y j k h₁ h₂`. Establish `a₁ : (𝟙 _ ≫ g) y ∈ (PPx x).U (fun _ => j PUnit.unit)` using `canon_le m gs' j h₁`. Establish `e` using `hw y j k h₁ h₂`.

Rewrite `e` using `[h g gs' gf j (canon_le m gs' j), gs_appLE g _ _ _ (𝟙 _) y h₁]`. Rewrite using `[h' g gs' gf j (canon_le m gs' j), gs_appLE g _ _ _ (𝟙 _) y h₁, hσ, gs_mul _ y _ h₂, gs_constFn _ _ _ y h₂, mul_left_comm]`. Use `(congrArg (gs _ y _) (hs _)).trans ((gs_mul _ y _ a₁ _ _).trans (congrArg₂ (· * ·) ?_ e))` and prove the remaining obligations. Conclude with `(gs_constFn (fst (Over.mk x) Xo.univ.t.G).left _ _ y a₁ a).trans (by rw [Category.assoc, gf])`.
-/
theorem isoMaps_scale {w : LB.Iso t.PP.L (Xo.univ.t.PP.L.pull m.φ)} {s s' : LB.Sec (PPx x)}
    {s₁ s₁' : LB.Sec (Xo.univ.t.PP.L.pull m.φ)} {σ σ' : LB.Sec t.PP.L} {a : S} (h : Reads m s s₁)
    (h' : Reads m s' s₁') (hs : ∀ i, s'.f i = scal x a i * s.f i)
    (hσ : ∀ i, σ'.f i = constFn t.G.hom _ a * σ.f i) (hw : IsoMaps w σ s₁) : IsoMaps w σ' s₁' := by
  obtain ⟨g, gs', gf⟩ := exists_canon m
  rw [isoMaps_iff] at hw ⊢
  intro y j k h₁ h₂
  have a₁ : (𝟙 _ ≫ g) y ∈ (PPx x).U (fun _ => j PUnit.unit) := canon_le m gs' j h₁
  have e := hw y j k h₁ h₂
  rw [h g gs' gf j (canon_le m gs' j), gs_appLE g _ _ _ (𝟙 _) y h₁] at e
  rw [h' g gs' gf j (canon_le m gs' j), gs_appLE g _ _ _ (𝟙 _) y h₁, hσ, gs_mul _ y _ h₂,
    gs_constFn _ _ _ y h₂, mul_left_comm]
  refine (congrArg (gs _ y _) (hs _)).trans ((gs_mul _ y _ a₁ _ _).trans (congrArg₂ (· * ·) ?_ e))
  exact (gs_constFn (fst (Over.mk x) Xo.univ.t.G).left _ _ y a₁ a).trans (by rw [Category.assoc, gf])

/- English proof (translation)
Take `⟨N, _, _, v, ρ, hv, htan, hcomb, -, -⟩` from `GlobalTheory.T.exists_tangent_module_universal_group E H Dw l Xo S x`. Use `choose b hb using fun k => (htan _).1 (hu k)`. Use `choose b' hb' using fun k => (htan _).1 (hu' k)`. Take `rfl : u = fun k => v (b k)` from `funext fun k => (hb k).symm`. Take `rfl : u' = fun k => v (b' k)` from `funext fun k => (hb' k).symm`.

Establish `e : ∀ i, ∑ k, X i k • b k = ∑ k, X i k • b' k` using `fun i => hv (((hcomb _ _ _ _).1 (h i)).symm.trans ((hcomb _ _ _ _).1 (h' i)))`. Establish `key : ∀ (c : Fin n → N) j, c j = ∑ i, X⁻¹ j i • ∑ k, X i k • c k` using `fun c j => by`. Simplify using `only [Finset.smul_sum, smul_smul]`. Rewrite using `[Finset.sum_comm]`. Simplify using `only [← Finset.sum_smul, ← Matrix.mul_apply, Matrix.nonsing_inv_mul X hX]`.

Simplify using `[Matrix.one_apply]`. Use function extensionality and compare the values at `j`. Rewrite using `[key b j, key b' j]`. Simplify using `only [e]`.
-/
theorem eq_of_isCombAt {n : ℕ} {u u' U : Fin n → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)}
    {X : Matrix (Fin n) (Fin n) S} (hX : IsUnit X.det) (hu : ∀ k, IsTanAt x (u k)) (hu' : ∀ k, IsTanAt x (u' k))
    (h : ∀ i, IsCombAt x u (X i) (U i)) (h' : ∀ i, IsCombAt x u' (X i) (U i)) : u = u' := by
  obtain ⟨N, _, _, v, ρ, hv, htan, hcomb, -, -⟩ := GlobalTheory.T.exists_tangent_module_universal_group E H Dw l Xo S x
  choose b hb using fun k => (htan _).1 (hu k)
  choose b' hb' using fun k => (htan _).1 (hu' k)
  obtain rfl : u = fun k => v (b k) := funext fun k => (hb k).symm
  obtain rfl : u' = fun k => v (b' k) := funext fun k => (hb' k).symm
  have e : ∀ i, ∑ k, X i k • b k = ∑ k, X i k • b' k := fun i =>
    hv (((hcomb _ _ _ _).1 (h i)).symm.trans ((hcomb _ _ _ _).1 (h' i)))
  have key : ∀ (c : Fin n → N) j, c j = ∑ i, X⁻¹ j i • ∑ k, X i k • c k := fun c j => by
    simp only [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_smul, ← Matrix.mul_apply, Matrix.nonsing_inv_mul X hX]
    simp [Matrix.one_apply]
  funext j
  rw [key b j, key b' j]
  simp only [e]

end Theta

/- English proof (translation)
Establish `h` using `IsLocalization.Away.algebraMap_isUnit (S := ArcS Dw K) (arcDet Dw K)`. Establish `h'` using `isUnit_of_dvd_unit (map_dvd _ (Finset.dvd_prod_of_mem (fun τ : E →+* ℂ => Matrix.det (Matrix.of fun i k : Fin (Dw.mult τ) => (MvPolynomial.X (⟨τ, i, k⟩ : ArcLt Dw) : MvPolynomial (ArcLt Dw) (LaurentSeries K)))) (Finset.mem_univ τ))) h`. Rewrite `h'` using `[RingHom.map_det]`. Conclude with `h'`.
-/
theorem isUnit_det_letM {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (Dw : Datum H) (K : Type)
    [Field K] (τ : E →+* ℂ) : IsUnit (letM Dw K τ).det := by
  have h := IsLocalization.Away.algebraMap_isUnit (S := ArcS Dw K) (arcDet Dw K)
  have h' := isUnit_of_dvd_unit (map_dvd _ (Finset.dvd_prod_of_mem (fun τ : E →+* ℂ => Matrix.det
    (Matrix.of fun i k : Fin (Dw.mult τ) => (MvPolynomial.X (⟨τ, i, k⟩ : ArcLt Dw) :
      MvPolynomial (ArcLt Dw) (LaurentSeries K)))) (Finset.mem_univ τ))) h
  rw [RingHom.map_det] at h'
  exact h'

/- English proof (translation)
Establish `: CharZero S` using `charZero_of_injective_ringHom (algebraMap c.F S).injective`. Set `: Algebra ℚ S` to `((algebraMap c.F S).comp (algebraMap ℚ c.F)).toAlgebra`. Establish `hm : Mono Y.m.φ` using `Y.m.cart.1.mono_fst_of_mono hj`. Take `⟨n, hn⟩` from `sabComp pullCubComp E H _ _ _ _ _ _ _ _ W.m m2`. Establish `cancel : ∀ (p : Sp S ⟶ Y.X) (_ : z ≫ Y.j = p) (n : SABMap t Y.t p), ∃ m' : SABMap t Y.oF.t z, n.φ = m'.φ ≫ Y.m.φ`.

Introduce `p hp n`. Substitute `hp` using the available equality. Conclude with `sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ Y.m n`. Take `⟨φ, hφ⟩` from `cancel _ hz n`. Choose the witnesses or unpack the hypotheses as in `⟨m, hm0⟩ : ∃ m : SABMap t Xo.univ.t yF.x, m.φ = φ.φ ≫ Y.m0.toSABMap.φ := by`.

Rewrite using `[← hzx]`. Conclude with `sabComp pullCubComp E H _ _ _ _ _ _ _ _ Y.m0.toSABMap φ`. Take `⟨w, gw', rw', -⟩` from `m.lin`. Take `⟨s₁, hs₁⟩` from `exists_reads m yF.s`. Take `⟨σ₁, hσ₁⟩` from `exists_isoMaps w gw' Xo.univ.t.PP.isLB t.PP.isLB s₁`.

Take `⟨ξ, N, hN, hξ, hσξ⟩` from `GlobalTheory.T.theta_generator_eq_rootOfUnity_mul_alt hL hL2 E H Dw l Xo c S t yF.x m m1 w w1 σ₁ σ' s₁ s1 yF.s yF.gen ⟨gw', rw'⟩ r1 hσ₁ i1 hs₁ hg`. Establish `hζ : ξ * ξ ^ (N - 1) = 1` using `by rw [← pow_succ', Nat.sub_add_cancel hN, hξ]`. Take `⟨y₀, hy₀⟩` from `(GlobalTheory.ArcQ.frChg_exists_unique_units E H Dw l Xo c _ (fun τ => (X τ)⁻¹) ξ yF).1 (fun τ => Matrix.isUnit_nonsing_inv_det _ (hX τ)) (IsUnit.of_mul_eq_one _ hζ)`. Establish `hchg : FrChg X (ξ ^ (N - 1)) y₀ yF`. Take `⟨c1, c2, -⟩` from `GlobalTheory.T.frameChange_compose_invert_baseChange_triangular E H Dw l Xo c S`.

Use `(c1 _ _ _ _ _ _ _ hy₀).2 ?_` and prove the remaining obligations. Rewrite using `[mul_comm, hζ, funext fun τ => Matrix.mul_nonsing_inv _ (hX τ)]`. Conclude with `c2 yF`. Take `⟨x₀, xo, u₀, tan₀, eig₀, bas₀, s₀, gen₀⟩` from `y₀`. Take `⟨hx, -, hs₀⟩` from `hy₀`.

Simplify using `only at hx hs₀`. Substitute `hx` using the available equality. Take `⟨s₁₀, hs₁₀⟩` from `exists_reads m s₀`. Establish `i1'` using `isoMaps_scale m hs₁ hs₁₀ ((GlobalTheory.Frames.ChgOf.secBC_id_iff _ _ _ _).1 hs₀) hσξ hσ₁`. Establish `core : ∀ (e' : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR K)) (v' : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (epsR (PowerSeries K) ⟶ W.t.G)) (u' : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (epsR S ⟶ t.G)), (∀ τ k, LieImg W (e' τ k) (v' τ k)) → (∀ τ k, (u' τ k).left ≫ m2.φ = spMap (dualM …`.

Introduce `e' v' u' h1 h2 h3 h4`. Use `⟨z, t, m, m2, φ.φ, hz, hzx, φ.cart.1.w, hm0.symm, hφ.symm.trans hn, fun τ k => ⟨v' τ k, (u' τ k).left, h1 τ k, ?_, h2 τ k, Over.w (u' τ k)⟩, θ, w, w2, σ', s₁₀, θ2, hθ, ⟨gw', rw'⟩, r2, i1', i2, ps, hs₁₀⟩` and prove the remaining obligations. Conclude with `congrFun (eq_of_isCombAt (hX τ) (fun k => (ExFr.tan_iff m _).2 (h3 τ k)) (tan₀ τ) (h4 τ) (hchg.2.1 τ)) k`. Use `choose u hu using fun τ k => exists_baseChange m2.cart (v τ k)`. Establish `hcomb : ∀ τ i, IsCombAt yF.x (fun k => (u τ k).left ≫ m.φ) (X τ i) (yF.u τ i)` using `fun τ i => by`.

Take `⟨vS, h1, h2⟩` from `hvS τ i`. Take `rfl : vS = fun k => (u τ k).left ≫ m.φ` from `funext fun k => by`. Take `⟨v'', b1, b2⟩` from `h1 k`. Establish `: v'' = (u τ k).left ≫ φ.φ`. Rewrite using `[← cancel_mono Y.m.φ, b1, Category.assoc, ← hφ, hn, ← Category.assoc (u τ k).left, hu, Category.assoc]`.

Rewrite using `[b2, this, hm0, Category.assoc]`. Conclude with `h2`. Use `⟨ξ ^ (N - 1), N, _, hN, by rw [← pow_mul, mul_comm, pow_mul, hξ, one_pow], hchg, fun ht => core e v u hv hu (fun τ k => isTangent_baseChange m2.cart (hu τ k) (((GlobalTheory.T.exists_unique_constant_tangent_vectors_along_arc hL.globalFns E H Dw l Xo c _ _ Y K _ _ χ W (e τ k)).2 _ …` and prove the remaining obligations. Use `choose e₀ he₀ using fun τ k => exists_gtComb (Pi.single k (1 : K)) (e τ)`. Use `choose v₀ hv₀ using fun τ k => (GlobalTheory.T.exists_unique_constant_tangent_vectors_along_arc hL.globalFns E H Dw l Xo c _ _ Y K _ _ χ W (e₀ τ k)).1.exists`.

Use `choose u' hu' using fun τ k => exists_baseChange m2.cart (v₀ τ k)`. Establish `hl : ∀ τ k, IsLieComb (Pi.single k (1 : S)) (u τ) (u' τ k)` using `fun τ k => by`. Establish `h` using `isLieComb_baseChange m2.cart (hu τ) (hu' τ k) ((GlobalTheory.T.lieImg_iff_isLieComb_of_gtComb hL.globalFns E H Dw l Xo c _ _ Y K _ _ χ W _ _ _ _ (v τ) _ (hv τ) (he₀ τ k)).1 (hv₀ τ k))`. Use `Eq.mp (congrArg (fun q => IsLieComb q (u τ) (u' τ k)) (funext fun j => ?_)) h` and prove the remaining obligations. Distinguish the cases in `hjk : j = k`.

Substitute `hjk` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Pi.single_eq_of_ne hjk]`. Establish `tp : ∀ τ i, (∀ k, IsTangent (u' τ k)) ∧ IsCombAt yF.x (fun k => (u' τ k).left ≫ m.φ) (X τ i) (yF.u τ i)` using `fun τ i => by`. Take `⟨U, hU⟩` from `ExFr.exists_lift m (T := epsR S) (yF.u τ i) (yF.tan τ i).1`.

Establish `h1` using `hcomb τ i`. Establish `h2` using `yF.tan τ i`. Rewrite `h1`, `h2`, the goal using `[← hU]`. Take `⟨b1, b2⟩` from `tangent_parts (u τ) (u' τ) (hl τ) _ U ((ExFr.tan_iff m U).1 h2) ((ExFr.comb_iff m _ _ U).1 h1)`. Conclude with `⟨b1, (ExFr.comb_iff m _ _ U).2 b2⟩`.

Conclude with `⟨e₀, he₀, core e₀ v₀ u' hv₀ hu' (fun τ k => (tp τ k).1 k) fun τ i => (tp τ i).2⟩`.
-/
theorem exists_frame (hL : Out.Laws) (hL2 : Out.Laws2) {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
    {Y : Model Xo c β} (hj : Mono Y.j) {K : Type} [Field K] {b : O →+* K} {a : ArcIn Dw l β K b}
    {χ : Sp (PowerSeries K) ⟶ Y.X} (W : Wit Y a χ)
    (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR K)) (th : a.D₀.P.L.Sec)
    {S : Type} [CommRing S] [IsDomain S] [Algebra c.F S] (f : PowerSeries K →+* S)
    (X : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S) (hX : ∀ τ, IsUnit (X τ).det) (yF : FrPt Xo c S)
    (z : Sp S ⟶ Xo.XF c) (hz : z ≫ Y.j = spMap f ≫ χ) (hzx : z ≫ pullback.fst _ _ = yF.x)
    (v : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (epsR (PowerSeries K) ⟶ W.t.G)) (hv : ∀ τ k, LieImg W (e τ k) (v τ k))
    (hvS : ∀ τ i, ∃ vS : Fin (Dw.mult τ) → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left),
      (∀ k, ∃ v'' : Sp (DualNumber S) ⟶ Y.oF.t.G.left,
        v'' ≫ Y.m.φ = spMap (dualMap f) ≫ (v τ k).left ≫ W.m.φ ∧ vS k = v'' ≫ Y.m0.toSABMap.φ) ∧
      IsCombAt yF.x vS (X τ i) (yF.u τ i))
    (θ : LB.Sec W.t.PP.L) (hθ : ThetaOf W th θ) (t : SAB H (Sp S)) (m1 : SABMap t Xo.univ.t yF.x)
    (m2 : SABMap t W.t (spMap f)) (w1 : LB.Iso t.PP.L (Xo.univ.t.PP.L.pull m1.φ))
    (w2 : LB.Iso t.PP.L (W.t.PP.L.pull m2.φ)) (σ' : LB.Sec t.PP.L) (s1 : LB.Sec (Xo.univ.t.PP.L.pull m1.φ))
    (θ2 : LB.Sec (W.t.PP.L.pull m2.φ)) (r1 : RigIso m1 w1) (r2 : RigIso m2 w2) (i1 : IsoMaps w1 σ' s1)
    (i2 : IsoMaps w2 σ' θ2) (ps : PullSec m2.φ θ θ2) (hg : Reads m1 yF.s s1) :
    ∃ (ζ : S) (N : ℕ) (y₀ : FrPt Xo c S), 0 < N ∧ ζ ^ N = 1 ∧ FrChg X ζ y₀ yF ∧
      ((∀ τ k, GtTanR (e τ k)) → IsArcFr W e th f y₀) ∧
      ∃ e₀ : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR K),
        (∀ τ k, GtComb (Pi.single k (1 : K)) (e τ) (e₀ τ k)) ∧ IsArcFr W e₀ th f y₀ := by
  have : CharZero S := charZero_of_injective_ringHom (algebraMap c.F S).injective
  let : Algebra ℚ S := ((algebraMap c.F S).comp (algebraMap ℚ c.F)).toAlgebra
  have hm : Mono Y.m.φ := Y.m.cart.1.mono_fst_of_mono hj
  obtain ⟨n, hn⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ W.m m2
  have cancel : ∀ (p : Sp S ⟶ Y.X) (_ : z ≫ Y.j = p) (n : SABMap t Y.t p),
      ∃ m' : SABMap t Y.oF.t z, n.φ = m'.φ ≫ Y.m.φ := by
    intro p hp n; subst hp; exact sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ Y.m n
  obtain ⟨φ, hφ⟩ := cancel _ hz n
  obtain ⟨m, hm0⟩ : ∃ m : SABMap t Xo.univ.t yF.x, m.φ = φ.φ ≫ Y.m0.toSABMap.φ := by
    rw [← hzx]; exact sabComp pullCubComp E H _ _ _ _ _ _ _ _ Y.m0.toSABMap φ
  obtain ⟨w, gw', rw', -⟩ := m.lin
  obtain ⟨s₁, hs₁⟩ := exists_reads m yF.s
  obtain ⟨σ₁, hσ₁⟩ := exists_isoMaps w gw' Xo.univ.t.PP.isLB t.PP.isLB s₁
  obtain ⟨ξ, N, hN, hξ, hσξ⟩ := GlobalTheory.T.theta_generator_eq_rootOfUnity_mul_alt hL hL2 E H Dw l Xo c S t yF.x m m1 w w1 σ₁ σ' s₁ s1 yF.s yF.gen
    ⟨gw', rw'⟩ r1 hσ₁ i1 hs₁ hg
  have hζ : ξ * ξ ^ (N - 1) = 1 := by rw [← pow_succ', Nat.sub_add_cancel hN, hξ]
  obtain ⟨y₀, hy₀⟩ := (GlobalTheory.ArcQ.frChg_exists_unique_units E H Dw l Xo c _ (fun τ => (X τ)⁻¹) ξ yF).1
    (fun τ => Matrix.isUnit_nonsing_inv_det _ (hX τ)) (IsUnit.of_mul_eq_one _ hζ)
  have hchg : FrChg X (ξ ^ (N - 1)) y₀ yF := by
    obtain ⟨c1, c2, -⟩ := GlobalTheory.T.frameChange_compose_invert_baseChange_triangular E H Dw l Xo c S
    refine (c1 _ _ _ _ _ _ _ hy₀).2 ?_
    rw [mul_comm, hζ, funext fun τ => Matrix.mul_nonsing_inv _ (hX τ)]
    exact c2 yF
  obtain ⟨x₀, xo, u₀, tan₀, eig₀, bas₀, s₀, gen₀⟩ := y₀
  obtain ⟨hx, -, hs₀⟩ := hy₀
  dsimp only at hx hs₀
  subst hx
  obtain ⟨s₁₀, hs₁₀⟩ := exists_reads m s₀
  have i1' := isoMaps_scale m hs₁ hs₁₀ ((GlobalTheory.Frames.ChgOf.secBC_id_iff _ _ _ _).1 hs₀) hσξ hσ₁
  have core : ∀ (e' : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR K))
      (v' : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (epsR (PowerSeries K) ⟶ W.t.G))
      (u' : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (epsR S ⟶ t.G)), (∀ τ k, LieImg W (e' τ k) (v' τ k)) →
      (∀ τ k, (u' τ k).left ≫ m2.φ = spMap (dualMap f) ≫ (v' τ k).left) → (∀ τ k, IsTangent (u' τ k)) →
      (∀ τ i, IsCombAt yF.x (fun k => (u' τ k).left ≫ m.φ) (X τ i) (yF.u τ i)) →
      IsArcFr W e' th f ⟨yF.x, xo, u₀, tan₀, eig₀, bas₀, s₀, gen₀⟩ := by
    intro e' v' u' h1 h2 h3 h4
    refine ⟨z, t, m, m2, φ.φ, hz, hzx, φ.cart.1.w, hm0.symm, hφ.symm.trans hn, fun τ k => ⟨v' τ k, (u' τ k).left,
      h1 τ k, ?_, h2 τ k, Over.w (u' τ k)⟩, θ, w, w2, σ', s₁₀, θ2, hθ, ⟨gw', rw'⟩, r2, i1', i2, ps, hs₁₀⟩
    exact congrFun (eq_of_isCombAt (hX τ) (fun k => (ExFr.tan_iff m _).2 (h3 τ k)) (tan₀ τ) (h4 τ) (hchg.2.1 τ)) k
  choose u hu using fun τ k => exists_baseChange m2.cart (v τ k)
  have hcomb : ∀ τ i, IsCombAt yF.x (fun k => (u τ k).left ≫ m.φ) (X τ i) (yF.u τ i) := fun τ i => by
    obtain ⟨vS, h1, h2⟩ := hvS τ i
    obtain rfl : vS = fun k => (u τ k).left ≫ m.φ := funext fun k => by
      obtain ⟨v'', b1, b2⟩ := h1 k
      have : v'' = (u τ k).left ≫ φ.φ := by
        rw [← cancel_mono Y.m.φ, b1, Category.assoc, ← hφ, hn, ← Category.assoc (u τ k).left, hu, Category.assoc]
      rw [b2, this, hm0, Category.assoc]
    exact h2
  refine ⟨ξ ^ (N - 1), N, _, hN, by rw [← pow_mul, mul_comm, pow_mul, hξ, one_pow], hchg, fun ht => core e v u hv hu
    (fun τ k => isTangent_baseChange m2.cart (hu τ k)
      (((GlobalTheory.T.exists_unique_constant_tangent_vectors_along_arc hL.globalFns E H Dw l Xo c _ _ Y K _ _ χ W (e τ k)).2 _ (hv τ k)).1 (ht τ k))) hcomb, ?_⟩
  choose e₀ he₀ using fun τ k => exists_gtComb (Pi.single k (1 : K)) (e τ)
  choose v₀ hv₀ using fun τ k => (GlobalTheory.T.exists_unique_constant_tangent_vectors_along_arc hL.globalFns E H Dw l Xo c _ _ Y K _ _ χ W (e₀ τ k)).1.exists
  choose u' hu' using fun τ k => exists_baseChange m2.cart (v₀ τ k)
  have hl : ∀ τ k, IsLieComb (Pi.single k (1 : S)) (u τ) (u' τ k) := fun τ k => by
    have h := isLieComb_baseChange m2.cart (hu τ) (hu' τ k)
      ((GlobalTheory.T.lieImg_iff_isLieComb_of_gtComb hL.globalFns E H Dw l Xo c _ _ Y K _ _ χ W _ _ _ _ (v τ) _ (hv τ) (he₀ τ k)).1 (hv₀ τ k))
    refine Eq.mp (congrArg (fun q => IsLieComb q (u τ) (u' τ k)) (funext fun j => ?_)) h
    by_cases hjk : j = k
    · subst hjk; simp
    · simp [Pi.single_eq_of_ne hjk]
  have tp : ∀ τ i, (∀ k, IsTangent (u' τ k)) ∧
      IsCombAt yF.x (fun k => (u' τ k).left ≫ m.φ) (X τ i) (yF.u τ i) := fun τ i => by
    obtain ⟨U, hU⟩ := ExFr.exists_lift m (T := epsR S) (yF.u τ i) (yF.tan τ i).1
    have h1 := hcomb τ i
    have h2 := yF.tan τ i
    rw [← hU] at h1 h2 ⊢
    obtain ⟨b1, b2⟩ := tangent_parts (u τ) (u' τ) (hl τ) _ U ((ExFr.tan_iff m U).1 h2) ((ExFr.comb_iff m _ _ U).1 h1)
    exact ⟨b1, (ExFr.comb_iff m _ _ U).2 b2⟩
  exact ⟨e₀, he₀, core e₀ v₀ u' hv₀ hu' (fun τ k => (tp τ k).1 k) fun τ i => (tp τ i).2⟩

/- English proof (translation)
The claim follows from `IsIntegral.isAlgebraic (R := ℤ) (IsIntegral.of_pow hN (by rw [h]; exact isIntegral_one))`.
-/
theorem algZ_of_pow {S : Type} [CommRing S] {ζ : S} {N : ℕ} (hN : 0 < N) (h : ζ ^ N = 1) : GlobalTheory.ArcConst.AlgZ ζ :=
  IsIntegral.isAlgebraic (R := ℤ) (IsIntegral.of_pow hN (by rw [h]; exact isIntegral_one))

end GlobalTheory.ArcQ.NormalForm

open GlobalTheory.ArcQ.NormalForm in

/- English proof (translation)
Introduce `hL hL2 E _ _ _ H Dw l Xo c K₁ _ _ _ d`. Take `⟨-, ⟨z, hz, hzx⟩, v, hv, hvS⟩` from `d.arcDatum_isArc_point_basis`. Take `⟨σ, fam, θ', θ, -, a1, a2, a3, a4, t, m1, m2, w1, w2, σ', s1, θ2, -, r1, r2, i1, i2, ps, hg⟩` from `d.isArc3`. Establish `: CharZero K₁` using `charZero_of_injective_ringHom (algebraMap c.F K₁).injective`. Establish `: IsDomain (ArcS Dw K₁)` using `GlobalTheory.ArcConst.isDomain Dw K₁`.

Take `⟨ξ, N, y₀, hN, hξ, hchg, h1, e₀, h2, h3⟩` from `exists_frame hL hL2 (GlobalTheory.ThetaShiftProofs.mono_j d.Y (mono_spMap_subtype _)) d.W d.e d.th (arcι Dw K₁) (letM Dw K₁) (isUnit_det_letM Dw K₁) d.yF z hz hzx v hv hvS θ ⟨σ, fam, θ', a1, a2, a3, a4⟩ t m1 m2 w1 w2 σ' s1 θ2 r1 r2 i1 i2 ps hg`. Take `⟨ζ, hζ⟩` from `GlobalTheory.ArcConst.exists_const Dw K₁ ξ (algZ_of_pow hN hξ)`. Establish `hζN : ζ ^ N = 1` using `GlobalTheory.ArcConst.arcι_C_injective Dw K₁ ((map_pow _ _ _).trans (((congrArg (· ^ N) hζ).symm.trans hξ).trans (map_one _).symm))`. Establish `hc : FrChg (letM Dw K₁) (GlobalTheory.ArcQ.cst Dw ζ) y₀ d.yF` using `(show ξ = GlobalTheory.ArcQ.cst Dw ζ from hζ) ▸ hchg`. Conclude with `⟨ζ, N, hN, hζN, fun ht => ⟨y₀, h1 ht, hc⟩, e₀, y₀, h2, h3, hc⟩`.
-/
theorem GlobalTheory.ArcQ.exists_normalForm : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K₁ : Type) [Field K₁] [Algebra c.F K₁] [Algebra c.F (ArcS Dw K₁)] (d : ArcDatum Xo c K₁), ∃ (ζ : K₁) (N : ℕ), 0 < N ∧ ζ ^ N = 1 ∧ ((∀ τ k, GtTanR (d.e τ k)) → d.Normal ζ) ∧ ∃ (e₀ : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt (d.a.restrict (c.V d.Wp).subtype).D₀ (epsR K₁)) (y₀ : FrPt Xo c (ArcS Dw K₁)), (∀ τ k, GtComb (Pi.single k (1 : K₁)) (d.e τ) (e₀ τ k)) ∧ IsArcFr d.W e₀ d.th (arcι Dw K₁) y₀ ∧ FrChg (letM Dw K₁) (GlobalTheory.ArcQ.cst Dw ζ) y₀ d.yF := by
  intro hL hL2 E _ _ _ H Dw l Xo c K₁ _ _ _ d
  obtain ⟨-, ⟨z, hz, hzx⟩, v, hv, hvS⟩ := d.arcDatum_isArc_point_basis
  obtain ⟨σ, fam, θ', θ, -, a1, a2, a3, a4, t, m1, m2, w1, w2, σ', s1, θ2, -, r1, r2, i1, i2, ps, hg⟩ := d.isArc3
  have : CharZero K₁ := charZero_of_injective_ringHom (algebraMap c.F K₁).injective
  have : IsDomain (ArcS Dw K₁) := GlobalTheory.ArcConst.isDomain Dw K₁
  obtain ⟨ξ, N, y₀, hN, hξ, hchg, h1, e₀, h2, h3⟩ := exists_frame hL hL2 (GlobalTheory.ThetaShiftProofs.mono_j d.Y (mono_spMap_subtype _))
    d.W d.e d.th (arcι Dw K₁) (letM Dw K₁) (isUnit_det_letM Dw K₁) d.yF z hz hzx v hv hvS θ
    ⟨σ, fam, θ', a1, a2, a3, a4⟩ t m1 m2 w1 w2 σ' s1 θ2 r1 r2 i1 i2 ps hg
  obtain ⟨ζ, hζ⟩ := GlobalTheory.ArcConst.exists_const Dw K₁ ξ (algZ_of_pow hN hξ)
  have hζN : ζ ^ N = 1 := GlobalTheory.ArcConst.arcι_C_injective Dw K₁
    ((map_pow _ _ _).trans (((congrArg (· ^ N) hζ).symm.trans hξ).trans (map_one _).symm))
  have hc : FrChg (letM Dw K₁) (GlobalTheory.ArcQ.cst Dw ζ) y₀ d.yF := (show ξ = GlobalTheory.ArcQ.cst Dw ζ from hζ) ▸ hchg
  exact ⟨ζ, N, hN, hζN, fun ht => ⟨y₀, h1 ht, hc⟩, e₀, y₀, h2, h3, hc⟩
