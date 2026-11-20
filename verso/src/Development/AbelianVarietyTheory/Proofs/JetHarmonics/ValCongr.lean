import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.SectionScalarValuation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBCorr
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermDJet
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ChartJetTrA
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExpansionValueZero

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

namespace GlobalTheory.GermBasic

/- English proof (translation)
Simplify using `only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]`.
-/
theorem spMap_comp_eq {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

section Point

variable {V : Type} [CommRing V] [IsDomain V] {G : Over (Sp V)} [GrpObj G] [IsCommMonObj G]
  {F : Type} [Field F] [Algebra (FractionRing V) F]

/- English proof (translation)
Establish `w : (snd (TFK (R` using `V) F) ((Over.pullback (jK V)).obj G)).left ≫ pullback.snd G.hom (jK V) = (fst (TFK (R := V) F) ((Over.pullback (jK V)).obj G)).left ≫ jFK (R := V) F := (Over.w (snd (TFK (R := V) F) ((Over.pullback (jK V)).obj G))).trans (Over.w (fst (TFK (R := V) F) ((Over.pullback (jK V)).obj G …`. Establish `h₃ : a ≫ (snd (TFK (R` using `V) F) ((Over.pullback (jK V)).obj G)).left = b ≫ (snd (TFK (R := V) F) ((Over.pullback (jK V)).obj G)).left := by`. Apply `pullback.hom_ext` to reduce the goal to its premises. Conclude with `(Category.assoc _ _ _).trans (h₂.trans (Category.assoc _ _ _).symm)`. Conclude with `(Category.assoc _ _ _).trans ((congrArg (a ≫ ·) w).trans ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ jFK (R := V) F) h₁).trans ((Category.assoc _ _ _).trans ((congrArg (b ≫ ·) w).symm.trans (Category.assoc _ _ _).symm)))))`.

Conclude with `pullback.hom_ext h₁ h₃`.
-/
theorem gf_ext {Z : Scheme.{0}} {a b : Z ⟶ (UnifPre.GF (R := V) (G := G) F).left}
    (h₁ : a ≫ (fst (TFK (R := V) F) ((Over.pullback (jK V)).obj G)).left =
      b ≫ (fst (TFK (R := V) F) ((Over.pullback (jK V)).obj G)).left)
    (h₂ : a ≫ UnifPre.gFK (R := V) (G := G) F = b ≫ UnifPre.gFK (R := V) (G := G) F) : a = b := by
  have w : (snd (TFK (R := V) F) ((Over.pullback (jK V)).obj G)).left ≫ pullback.snd G.hom (jK V) =
      (fst (TFK (R := V) F) ((Over.pullback (jK V)).obj G)).left ≫ jFK (R := V) F :=
    (Over.w (snd (TFK (R := V) F) ((Over.pullback (jK V)).obj G))).trans
      (Over.w (fst (TFK (R := V) F) ((Over.pullback (jK V)).obj G))).symm
  have h₃ : a ≫ (snd (TFK (R := V) F) ((Over.pullback (jK V)).obj G)).left =
      b ≫ (snd (TFK (R := V) F) ((Over.pullback (jK V)).obj G)).left := by
    apply pullback.hom_ext
    · exact (Category.assoc _ _ _).trans (h₂.trans (Category.assoc _ _ _).symm)
    · exact (Category.assoc _ _ _).trans ((congrArg (a ≫ ·) w).trans ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ jFK (R := V) F) h₁).trans ((Category.assoc _ _ _).trans
          ((congrArg (b ≫ ·) w).symm.trans (Category.assoc _ _ _).symm)))))
  exact pullback.hom_ext h₁ h₃

/- English proof (translation)
Set `T : Over (TK V).left` to `Over.mk (p ≫ jFK (R := V) F)`. Set `u : T ⟶ TFK (R` to `V) F := Over.homMk p rfl`. Set `v : T ⟶ (Over.pullback (jK V)).obj G` to `Over.homMk (pullback.lift g (p ≫ jFK (R := V) F) (h.trans (Category.assoc _ _ _).symm)) (pullback.lift_snd _ _ _)`. Use `⟨(lift u v).left, congrArg (fun q => q.left) (lift_fst u v), ?_⟩` and prove the remaining obligations. Conclude with `(Category.assoc _ _ _).symm.trans ((congrArg (fun q => q.left ≫ pullback.fst G.hom (jK V)) (lift_snd u v)).trans (pullback.lift_fst _ _ _))`.
-/
theorem gf_exists {Z : Scheme.{0}} (p : Z ⟶ Sp F) (g : Z ⟶ G.left) (h : g ≫ G.hom = p ≫ jFK (R := V) F ≫ jK V) :
    ∃ a : Z ⟶ (UnifPre.GF (R := V) (G := G) F).left,
      a ≫ (fst (TFK (R := V) F) ((Over.pullback (jK V)).obj G)).left = p ∧
      a ≫ UnifPre.gFK (R := V) (G := G) F = g := by
  let T : Over (TK V).left := Over.mk (p ≫ jFK (R := V) F)
  let u : T ⟶ TFK (R := V) F := Over.homMk p rfl
  let v : T ⟶ (Over.pullback (jK V)).obj G :=
    Over.homMk (pullback.lift g (p ≫ jFK (R := V) F) (h.trans (Category.assoc _ _ _).symm)) (pullback.lift_snd _ _ _)
  refine ⟨(lift u v).left, congrArg (fun q => q.left) (lift_fst u v), ?_⟩
  exact (Category.assoc _ _ _).symm.trans ((congrArg (fun q => q.left ≫ pullback.fst G.hom (jK V)) (lift_snd u v)).trans
    (pullback.lift_fst _ _ _))

variable [Algebra V F] [IsScalarTower V (FractionRing V) F]

/- English proof (translation)
Use `gf_exists _ _ ?_` and prove the remaining obligations. Establish `w : (z m).left ≫ G.hom = spMap (algebraMap V (Jet V κ m)) ≫ 𝟙 _` using `Over.w (z m)`. Establish `e : jFK (R` using `V) F ≫ jK V = spMap (algebraMap V F) := (spMap_comp_eq (algebraMap V (FractionRing V)) (algebraMap (FractionRing V) F)).trans (congrArg spMap (IsScalarTower.algebraMap_eq V (FractionRing V) F).symm)`. Rewrite using `[Category.assoc, w, e, Category.comp_id, spMap_comp_eq, spMap_comp_eq, JetTr.jetCoef_alg]`.
-/
theorem exists_jetPt {κ : Type} (z : JetPts G κ) (m : ℕ) :
    ∃ zF : Sp (Jet F κ m) ⟶ (UnifPre.GF (R := V) (G := G) F).left,
      zF ≫ (fst (TFK (R := V) F) ((Over.pullback (jK V)).obj G)).left = spMap (algebraMap F (Jet F κ m)) ∧
      zF ≫ UnifPre.gFK (R := V) (G := G) F = spMap (jetCoef (algebraMap V F) κ m) ≫ (z m).left := by
  refine gf_exists _ _ ?_
  have w : (z m).left ≫ G.hom = spMap (algebraMap V (Jet V κ m)) ≫ 𝟙 _ := Over.w (z m)
  have e : jFK (R := V) F ≫ jK V = spMap (algebraMap V F) :=
    (spMap_comp_eq (algebraMap V (FractionRing V)) (algebraMap (FractionRing V) F)).trans
      (congrArg spMap (IsScalarTower.algebraMap_eq V (FractionRing V) F).symm)
  rw [Category.assoc, w, e, Category.comp_id, spMap_comp_eq, spMap_comp_eq, JetTr.jetCoef_alg]

end Point

/- English proof (translation)
Establish `h : psTrunc m (∑ i, c i • f i) = ∑ i, MvPolynomial.C (c i) * psTrunc m (f i)`. Simplify using `only [psTrunc, map_sum, Finset.mul_sum, MvPolynomial.C_mul_monomial, map_smul, smul_eq_mul]`. Conclude with `Finset.sum_comm`. Rewrite using `[psJet, h, map_sum]`. Both sides reduce to the same expression.
-/
theorem psJet_sum {F κ : Type} [CommRing F] [Fintype κ] [DecidableEq κ] (m : ℕ) {l : ℕ} (c : Fin l → F)
    (f : Fin l → MvPowerSeries κ F) :
    psJet m (∑ i, c i • f i) = ∑ i, algebraMap F (Jet F κ m) (c i) * psJet m (f i) := by
  have h : psTrunc m (∑ i, c i • f i) = ∑ i, MvPolynomial.C (c i) * psTrunc m (f i) := by
    simp only [psTrunc, map_sum, Finset.mul_sum, MvPolynomial.C_mul_monomial, map_smul, smul_eq_mul]
    exact Finset.sum_comm
  rw [psJet, h, map_sum]
  rfl

/- English proof (translation)
Establish `hc : LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ t h) (LB.pullGen L _ _ t' h')` using `corr_of_val hL fun y J hJ => by rw [val_pull hJ, val_pull hJ, Category.id_comp, Category.id_comp, H y J hJ]`. Rewrite using `[← val_pull hJ, ← val_pull hJ, val_corr hJ hc]`.
-/
theorem val_congr {X Y Y' Z Z' : Scheme.{0}} {L : LB X} (hL : L.IsLB) {φ : Y ⟶ X} {φ' : Y' ⟶ X}
    (t : LB.Gen (LB.LinComb L (K := Fin 1) (fun _ => φ) (fun _ => (1 : ℤ))))
    (t' : LB.Gen (LB.LinComb L (K := Fin 1) (fun _ => φ') (fun _ => (1 : ℤ)))) (h : Z ⟶ Y) (h' : Z ⟶ Y')
    (H : ∀ y J, Good L y J → val t h y J = val t' h' y J) (r : Z' ⟶ Z) (y : Z') (J) (hJ : Good L y J) :
    val t (r ≫ h) y J = val t' (r ≫ h') y J := by
  have hc : LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ t h) (LB.pullGen L _ _ t' h') :=
    corr_of_val hL fun y J hJ => by rw [val_pull hJ, val_pull hJ, Category.id_comp, Category.id_comp, H y J hJ]
  rw [← val_pull hJ, ← val_pull hJ, val_corr hJ hc]

/- English proof (translation)
Introduce `V _ _ _ _ D A G _ _ U κ _ _ z hz τ hτ F _ _ _ _ q`. Establish `hL` using `U.LG.isLB`. Use `⟨fun σ' f f' hf hf' => ?_, fun l c σ f σ' hf hσ m => ?_, fun htr σ' => ?_⟩` and prove the remaining obligations. Use `GermFun.psJet_inj fun m => ?_` and prove the remaining obligations. Take `⟨a, a₁, a₂, ha⟩` from `hf m`.

Take `⟨b, b₁, b₂, hb⟩` from `hf' m`. Take `rfl : a = b` from `gf_ext (a₁.trans b₁.symm) (a₂.trans b₂.symm)`. Use `H1.cst_ext fun y => ?_` and prove the remaining obligations. Take `⟨J, hJ, -⟩` from `exists_good U.LG.L hL y (K := PEmpty) PEmpty.elim PEmpty.elim (fun k => k.elim) (fun k => k.elim)`. Conclude with `(Units.mul_left_inj _).1 ((ha y J hJ).symm.trans (hb y J hJ))`.

Take `⟨a, a₁, a₂⟩` from `exists_jetPt (F := F) z m`. Use `⟨a, a₁, a₂, fun y J hJ => ?_⟩` and prove the remaining obligations. Use `(SectionScalarValuation.sval_lin _ σ hσ a y hJ).trans ?_` and prove the remaining obligations. Establish `e : gs (𝟙 _) y ⊤ (toΓ _ (psJet m (∑ i, c i • f i))) = ∑ i, cst (𝟙 _) y (algebraMap F (Jet F κ m) (c i)) * cst (𝟙 _) y (psJet m (f i))`. Use `(congrArg (cst (𝟙 _) y) (psJet_sum m c f)).trans ((ExpansionValueZero.cst_sum _ _ _ _).trans ?_)` and prove the remaining obligations.

Conclude with `Finset.sum_congr rfl fun i _ => H1.cst_mul _ _ _ _`. Rewrite using `[e, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Take `⟨b, b₁, b₂, hb⟩` from `hf i m`. Take `rfl : a = b` from `gf_ext (a₁.trans b₁.symm) (a₂.trans b₂.symm)`.

Rewrite using `[hb y J hJ, _root_.mul_assoc]`. Use `congrArg₂ (· * ·) ?_ rfl` and prove the remaining obligations. Use `(gs_pull a _ y ⊤ trivial _).trans ?_` and prove the remaining obligations. Rewrite using `[a₁, ← ExpansionValueZero.cst_comp, Category.id_comp]`. Both sides reduce to the same expression.

Use `choose a a₁ a₂ using exists_jetPt (F := F) z`. Establish `hv : ∀ m, ∃ v : Jet F κ m, ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp (Jet F κ m)) (y : Z) (J), Good U.LG.L y J → sval σ' (r ≫ a m) y J = cst r y v * (val (τ m) (r ≫ spMap (jetCoef (algebraMap V F) κ m)) y J ^ q).val`. Introduce `m`. Take `⟨v, hv⟩` from `ExpansionValueZero.exists_coeff (A := Jet F κ m) hL σ' (a m) (GeneratorPullback.powGen U.LG.L _ _ (LB.pullGen U.LG.L _ _ (τ m) (spMap (jetCoef (algebraMap V F) κ m))) q) (powGen_isGen_of_isGen _ (pullGen_isGen _ _ _ _ (hτ m) _) q) (fun W _ h => by simp only [a₂ m, _root_.mul_one] …`. Use `⟨v, fun Z r y J hJ => (hv Z r y J hJ).trans ?_⟩` and prove the remaining obligations.

Rewrite using `[← val_pull hJ]`. Conclude with `congrArg (fun u => cst r y v * Units.val u) (map_pow _ _ _)`. Use `choose v hv using hv`. Establish `hc : ∀ m, (jetTrunc : Jet F κ (m + 1) →ₐ[F] Jet F κ m) (v (m + 1)) = v m`. Introduce `m`.

Set `ρ` to `spMap ((jetTrunc : Jet F κ (m + 1) →ₐ[F] Jet F κ m) : Jet F κ (m + 1) →+* Jet F κ m)`. Set `ρV` to `spMap ((jetTrunc : Jet V κ (m + 1) →ₐ[V] Jet V κ m) : Jet V κ (m + 1) →+* Jet V κ m)`. Establish `hρ : ρ ≫ spMap (jetCoef (algebraMap V F) κ (m + 1)) = spMap (jetCoef (algebraMap V F) κ m) ≫ ρV`. Rewrite using `[spMap_comp_eq, spMap_comp_eq, JetTr.jetCoef_trunc]`. Establish `hzt : ρV ≫ (z (m + 1)).left = (z m).left` using `congrArg (fun q => q.left) (hz.1 m)`.

Establish `ha : ρ ≫ a (m + 1) = a m` using `gf_ext (by rw [Category.assoc, a₁, a₁]; exact spMap_comp_alg _) (by rw [Category.assoc, a₂, a₂, ← Category.assoc, hρ, Category.assoc, hzt])`. Use `H1.cst_ext fun y => ?_` and prove the remaining obligations. Take `⟨J, hJ, -⟩` from `exists_good U.LG.L hL y (K := PEmpty) PEmpty.elim PEmpty.elim (fun k => k.elim) (fun k => k.elim)`. Establish `e₁` using `hv (m + 1) _ ρ y J hJ`. Establish `e₀` using `hv m _ (𝟙 _) y J hJ`.

Rewrite `e₀` using `[Category.id_comp, Category.id_comp]`. Rewrite `e₁` using `[ha, hρ, val_congr hL (τ (m + 1)) (τ m) ρV (𝟙 _) (htr m) _ y J hJ, Category.comp_id]`. Use `Eq.trans ?_ ((Units.mul_left_inj _).1 (e₁.symm.trans e₀))` and prove the remaining obligations. Conclude with `(ExpansionValueZero.cst_comp (𝟙 _) _ y _).symm.trans (congrArg (fun r => cst r y (v (m + 1))) (Category.id_comp _))`. Take `⟨f, hf⟩` from `GermD.exists_ps_of_jets v hc`.

Use `⟨f, fun m => ⟨a m, a₁ m, a₂ m, fun y J hJ => ?_⟩⟩` and prove the remaining obligations. Establish `e₀` using `hv m _ (𝟙 _) y J hJ`. Rewrite `e₀` using `[Category.id_comp, Category.id_comp, ← hf m]`. Conclude with `e₀`.
-/
theorem main : AGermSt := by
  intro V _ _ _ _ D A G _ _ U κ _ _ z hz τ hτ F _ _ _ _ q
  have hL := U.LG.isLB
  refine ⟨fun σ' f f' hf hf' => ?_, fun l c σ f σ' hf hσ m => ?_, fun htr σ' => ?_⟩
  · refine GermFun.psJet_inj fun m => ?_
    obtain ⟨a, a₁, a₂, ha⟩ := hf m
    obtain ⟨b, b₁, b₂, hb⟩ := hf' m
    obtain rfl : a = b := gf_ext (a₁.trans b₁.symm) (a₂.trans b₂.symm)
    refine H1.cst_ext fun y => ?_
    obtain ⟨J, hJ, -⟩ := exists_good U.LG.L hL y (K := PEmpty) PEmpty.elim PEmpty.elim (fun k => k.elim) (fun k => k.elim)
    exact (Units.mul_left_inj _).1 ((ha y J hJ).symm.trans (hb y J hJ))
  · obtain ⟨a, a₁, a₂⟩ := exists_jetPt (F := F) z m
    refine ⟨a, a₁, a₂, fun y J hJ => ?_⟩
    refine (SectionScalarValuation.sval_lin _ σ hσ a y hJ).trans ?_
    have e : gs (𝟙 _) y ⊤ (toΓ _ (psJet m (∑ i, c i • f i))) =
        ∑ i, cst (𝟙 _) y (algebraMap F (Jet F κ m) (c i)) * cst (𝟙 _) y (psJet m (f i)) := by
      refine (congrArg (cst (𝟙 _) y) (psJet_sum m c f)).trans ((ExpansionValueZero.cst_sum _ _ _ _).trans ?_)
      exact Finset.sum_congr rfl fun i _ => H1.cst_mul _ _ _ _
    rw [e, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    obtain ⟨b, b₁, b₂, hb⟩ := hf i m
    obtain rfl : a = b := gf_ext (a₁.trans b₁.symm) (a₂.trans b₂.symm)
    rw [hb y J hJ, _root_.mul_assoc]
    refine congrArg₂ (· * ·) ?_ rfl
    refine (gs_pull a _ y ⊤ trivial _).trans ?_
    rw [a₁, ← ExpansionValueZero.cst_comp, Category.id_comp]
    rfl
  · choose a a₁ a₂ using exists_jetPt (F := F) z
    have hv : ∀ m, ∃ v : Jet F κ m, ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp (Jet F κ m)) (y : Z) (J), Good U.LG.L y J →
        sval σ' (r ≫ a m) y J = cst r y v * (val (τ m) (r ≫ spMap (jetCoef (algebraMap V F) κ m)) y J ^ q).val := by
      intro m
      obtain ⟨v, hv⟩ := ExpansionValueZero.exists_coeff (A := Jet F κ m) hL σ' (a m)
        (GeneratorPullback.powGen U.LG.L _ _ (LB.pullGen U.LG.L _ _ (τ m) (spMap (jetCoef (algebraMap V F) κ m))) q)
        (powGen_isGen_of_isGen _ (pullGen_isGen _ _ _ _ (hτ m) _) q) (fun W _ h => by simp only [a₂ m, _root_.mul_one])
      refine ⟨v, fun Z r y J hJ => (hv Z r y J hJ).trans ?_⟩
      rw [← val_pull hJ]
      exact congrArg (fun u => cst r y v * Units.val u) (map_pow _ _ _)
    choose v hv using hv
    have hc : ∀ m, (jetTrunc : Jet F κ (m + 1) →ₐ[F] Jet F κ m) (v (m + 1)) = v m := by
      intro m
      let ρ := spMap ((jetTrunc : Jet F κ (m + 1) →ₐ[F] Jet F κ m) : Jet F κ (m + 1) →+* Jet F κ m)
      let ρV := spMap ((jetTrunc : Jet V κ (m + 1) →ₐ[V] Jet V κ m) : Jet V κ (m + 1) →+* Jet V κ m)
      have hρ : ρ ≫ spMap (jetCoef (algebraMap V F) κ (m + 1)) = spMap (jetCoef (algebraMap V F) κ m) ≫ ρV := by
        rw [spMap_comp_eq, spMap_comp_eq, JetTr.jetCoef_trunc]
      have hzt : ρV ≫ (z (m + 1)).left = (z m).left := congrArg (fun q => q.left) (hz.1 m)
      have ha : ρ ≫ a (m + 1) = a m := gf_ext
        (by rw [Category.assoc, a₁, a₁]; exact spMap_comp_alg _)
        (by rw [Category.assoc, a₂, a₂, ← Category.assoc, hρ, Category.assoc, hzt])
      refine H1.cst_ext fun y => ?_
      obtain ⟨J, hJ, -⟩ := exists_good U.LG.L hL y (K := PEmpty) PEmpty.elim PEmpty.elim (fun k => k.elim) (fun k => k.elim)
      have e₁ := hv (m + 1) _ ρ y J hJ
      have e₀ := hv m _ (𝟙 _) y J hJ
      rw [Category.id_comp, Category.id_comp] at e₀
      rw [ha, hρ, val_congr hL (τ (m + 1)) (τ m) ρV (𝟙 _) (htr m) _ y J hJ, Category.comp_id] at e₁
      refine Eq.trans ?_ ((Units.mul_left_inj _).1 (e₁.symm.trans e₀))
      exact (ExpansionValueZero.cst_comp (𝟙 _) _ y _).symm.trans (congrArg (fun r => cst r y (v (m + 1))) (Category.id_comp _))
    obtain ⟨f, hf⟩ := GermD.exists_ps_of_jets v hc
    refine ⟨f, fun m => ⟨a m, a₁ m, a₂ m, fun y J hJ => ?_⟩⟩
    have e₀ := hv m _ (𝟙 _) y J hJ
    rw [Category.id_comp, Category.id_comp, ← hf m] at e₀
    exact e₀

end GlobalTheory.GermBasic
