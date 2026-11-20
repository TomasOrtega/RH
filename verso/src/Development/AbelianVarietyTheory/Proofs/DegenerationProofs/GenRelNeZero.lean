import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Definitions.Degenerations.HomExtSt
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPowEqOneOfPosDefForm
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsInvariantNatLengthLattice
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsIsoPullCancel
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPowEqOfBaseChange
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsCommonField
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsEqNsmulOfForallAddChar
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.WeilIsGrpPullbackIff
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.EqOfDominantGeometricPointsOfUnramified
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsoEqOfMapsAlongSection
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsProjectiveRep
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoNormalizationPullbackOfToIntegralClosure

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LN

noncomputable section

namespace GlobalTheory.MatchRigid

/- English proof (translation)
Take `⟨P', g, hg, -, hm, s, hs⟩` from `hL.polBaseChange S _ t P`. Establish `hp : IsGrpPullback P'.A P.A t g` using `⟨hg, fun T x y x₀ y₀ hx hy => by`. Rewrite using `[(Over.OverMorphism.ext hx : x₀ = toBase hg.w x), (Over.OverMorphism.ext hy : y₀ = toBase hg.w y), ← hm]`. Use the proof step `rfl⟩`. Take `⟨w', hw'⟩` from `LBIso.symm (⟨s, hs⟩ : LBIso _ _)`.

Establish `hp' : IsGrpPullback P'.A P.A t (g ≫ θ.hom.left)` using `(hp.comp (isGrpPullback_of_iso θ)).congr (Category.comp_id _) rfl`. Take `⟨θ', hθ', e'⟩` from `grpPullback_iso hp' hp`. Take `⟨w₁, T⟩` from `exists_comp P.isLB w w' ((isGen_iff _).1 hw) ((isGen_iff _).1 hw') P.isLB P'.isLB`. Establish `g₁ : w₁.IsGen` using `(isGen_iff _).2 (T.pgen_comp P.isLB ((isGen_iff _).1 hw) ((isGen_iff _).1 hw'))`. Take `⟨wθ, -, hwθ, -, -⟩` from `exists_iso_pull_cancel P.isLB P'.isLB P'.isLB e' w₁ w' g₁ hw'`.

Establish `hMu : IsUnit (M : Γ(Sp F, ⊤))`. Simplify using `using (IsUnit.mk0 _ hF).map (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom`. Establish `key : θ'.hom = 𝟙 _`. Use `hL.serre _ P' M hM θ' hθ' (fun _ => ⟨⊤, trivial, ?_⟩) (fix_torsion_of_fix_geometric_of_isDominant hL.mulN P' M (by omega) hMu (𝟙 _) θ'.hom hθ' fun y hy => ?_)` and prove the remaining obligations. Take `⟨u, hu⟩` from `gen_of_iso ((isGen_iff wθ).1 hwθ) (P'.A.hom ⁻¹ᵁ ⊤).ι`.

Use `gen_chartPull (chartPullOut P'.L _ _ _ _ fun n => ?_) u hu` and prove the remaining obligations. Use `fin_cases n`. Use `exacts [rfl, (Category.comp_id _).symm]`. Set `ρ : Over.mk t ⟶ Over.mk (𝟙 _ ≫ t)` to `Over.homMk (𝟙 _) ((Category.id_comp _).trans (Category.id_comp _))`. Set `Φ : (Over.mk (𝟙 (Sp F)) ⟶ P'.A) →* (Over.mk t ⟶ P.A)` to `MonoidHom.mk' (fun y => ρ ≫ toBase hg.w y) (fun a b => by rw [hm, MonObj.comp_mul])`.

Establish `hΦ : ∀ y, (Φ y).left = y.left ≫ g` using `fun y => Category.id_comp _`. Establish `h` using `congrArg Over.Hom.left (hfix (Φ y) (by rw [← map_pow, hy, map_one]))`. Rewrite `h` using `[Over.comp_left, hΦ]`. Use `Over.OverMorphism.ext (hg.hom_ext ?_ (by rw [Over.w, Over.w]))` and prove the remaining obligations. Rewrite using `[Over.comp_left, Category.assoc, e', ← Category.assoc, h]`.

Rewrite `e'` using `[key, Over.id_left, Category.id_comp]`. Use `P.isAb.smooth` as an intermediate fact. Use `P.isAb.proper` as an intermediate fact. Use `IsSchemeTheoreticallyDominant.of_isDominant t` as an intermediate fact. Establish `: IsSchemeTheoreticallyDominant g` using `IsSchemeTheoreticallyDominant.of_isPullback hg.flip`.

Use `Over.OverMorphism.ext (hom_ext_of_isSchemeTheoreticallyDominant g P.A.hom ?_ (by rw [Over.w, Over.w]))` and prove the remaining obligations. Rewrite using `[← e', Over.id_left, Category.comp_id]`.
-/
theorem aut_eq_id (hL : Laws) {S : Scheme.{0}} [IsLocallyNoetherian S] [IsReduced S] (P : PolAV S) {F : Type} [Field F]
    [IsAlgClosed F] (t : Sp F ⟶ S) [IsDominant t] {M : ℕ} (hM : 3 ≤ M) (hF : (M : F) ≠ 0) (θ : P.A ≅ P.A)
    [IsMonHom θ.hom] (w : LB.Iso P.L (P.L.pull θ.hom.left)) (hw : w.IsGen)
    (hfix : ∀ x : Over.mk t ⟶ P.A, x ^ M = 1 → x ≫ θ.hom = x) : θ.hom = 𝟙 _ := by
  obtain ⟨P', g, hg, -, hm, s, hs⟩ := hL.polBaseChange S _ t P
  have hp : IsGrpPullback P'.A P.A t g := ⟨hg, fun T x y x₀ y₀ hx hy => by
    rw [(Over.OverMorphism.ext hx : x₀ = toBase hg.w x), (Over.OverMorphism.ext hy : y₀ = toBase hg.w y), ← hm]
    rfl⟩
  obtain ⟨w', hw'⟩ := LBIso.symm (⟨s, hs⟩ : LBIso _ _)
  have hp' : IsGrpPullback P'.A P.A t (g ≫ θ.hom.left) :=
    (hp.comp (isGrpPullback_of_iso θ)).congr (Category.comp_id _) rfl
  obtain ⟨θ', hθ', e'⟩ := grpPullback_iso hp' hp
  obtain ⟨w₁, T⟩ := exists_comp P.isLB w w' ((isGen_iff _).1 hw) ((isGen_iff _).1 hw') P.isLB P'.isLB
  have g₁ : w₁.IsGen := (isGen_iff _).2 (T.pgen_comp P.isLB ((isGen_iff _).1 hw) ((isGen_iff _).1 hw'))
  obtain ⟨wθ, -, hwθ, -, -⟩ := exists_iso_pull_cancel P.isLB P'.isLB P'.isLB e' w₁ w' g₁ hw'
  have hMu : IsUnit (M : Γ(Sp F, ⊤)) := by
    simpa using (IsUnit.mk0 _ hF).map (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom
  have key : θ'.hom = 𝟙 _ := by
    refine hL.serre _ P' M hM θ' hθ' (fun _ => ⟨⊤, trivial, ?_⟩)
      (fix_torsion_of_fix_geometric_of_isDominant hL.mulN P' M (by omega) hMu (𝟙 _) θ'.hom hθ' fun y hy => ?_)
    · obtain ⟨u, hu⟩ := gen_of_iso ((isGen_iff wθ).1 hwθ) (P'.A.hom ⁻¹ᵁ ⊤).ι
      refine gen_chartPull (chartPullOut P'.L _ _ _ _ fun n => ?_) u hu
      fin_cases n
      exacts [rfl, (Category.comp_id _).symm]
    · let ρ : Over.mk t ⟶ Over.mk (𝟙 _ ≫ t) := Over.homMk (𝟙 _) ((Category.id_comp _).trans (Category.id_comp _))
      let Φ : (Over.mk (𝟙 (Sp F)) ⟶ P'.A) →* (Over.mk t ⟶ P.A) :=
        MonoidHom.mk' (fun y => ρ ≫ toBase hg.w y) (fun a b => by rw [hm, MonObj.comp_mul])
      have hΦ : ∀ y, (Φ y).left = y.left ≫ g := fun y => Category.id_comp _
      have h := congrArg Over.Hom.left (hfix (Φ y) (by rw [← map_pow, hy, map_one]))
      rw [Over.comp_left, hΦ] at h
      refine Over.OverMorphism.ext (hg.hom_ext ?_ (by rw [Over.w, Over.w]))
      rw [Over.comp_left, Category.assoc, e', ← Category.assoc, h]
  rw [key, Over.id_left, Category.id_comp] at e'
  have := P.isAb.smooth
  have := P.isAb.proper
  have := IsSchemeTheoreticallyDominant.of_isDominant t
  have : IsSchemeTheoreticallyDominant g := IsSchemeTheoreticallyDominant.of_isPullback hg.flip
  refine Over.OverMorphism.ext (hom_ext_of_isSchemeTheoreticallyDominant g P.A.hom ?_ (by rw [Over.w, Over.w]))
  rw [← e', Over.id_left, Category.comp_id]

/- English proof (translation)
Use `o.hom` as an intermediate fact. Establish `hW` using `hL.weil S P M (Over.mk t)`. Use `ConjIdeal.fix_torsion_of_fix_conj_rel bar I hsup M hIJ (A := Γ((Over.mk t).left, ⊤)ˣ) (fun a => IsMonHom.monoidHom (o.act a) (Over.mk t)) (fun x => ?_) (fun a b x => ?_) (fun a b x => ?_) (fun x y c => WeilIs P.A P.L M x y c) hW.1 (fun x x' y c c' _ _ _ => hW.2.1 x x' y c c') (fu …` and prove the remaining obligations. Use `show x ≫ o.act 1 = x`. Rewrite using `[o.map_one, Category.comp_id]`.

Use `show x ≫ o.act (a + b) = (x ≫ o.act a) * (x ≫ o.act b)`. Rewrite using `[o.map_add, ← MonObj.comp_mul]`. Both sides reduce to the same expression. Use `show x ≫ o.act (a * b) = (x ≫ o.act b) ≫ o.act a`. Rewrite using `[o.map_mul, Category.assoc]`.

Use `(weilIs_rosati_iff hL.globalFns hL.cube P _ _ (o.rosati a) M x y hx hy c).2 ?_` and prove the remaining obligations. Rewrite using `[hbar]`. Conclude with `h`. Use `show (x ≫ o.act a) ≫ θ.hom = (x ≫ θ.hom) ≫ o.act a`. Rewrite using `[Category.assoc, hact, Category.assoc]`.

Conclude with `(weilIs_iso_iff hL.globalFns hL.cube P P θ w hw M x y hx hy c).2 h`.
-/
theorem fix_torsion (hL : Laws) {S : Scheme.{0}} [IsLocallyNoetherian S] (P : PolAV S) {F : Type} [Field F]
    [IsAlgClosed F] (t : Sp F ⟶ S) {M : ℕ} (hF : (M : F) ≠ 0) {O : Type} [CommRing O] [StarRing O] (o : P.OAct O)
    (bar : O ≃+* O) (hbar : ∀ a, star a = bar a) (I : Ideal O) (hsup : I ⊔ I.map bar = ⊤)
    (hIJ : I * I.map bar ≤ Ideal.span {(M : O)}) (θ : P.A ≅ P.A)
    [IsMonHom θ.hom] (w : LB.Iso P.L (P.L.pull θ.hom.left)) (hw : w.IsGen)
    (hact : ∀ a, o.act a ≫ θ.hom = θ.hom ≫ o.act a)
    (hfix : ∀ a ∈ I.map bar, ∀ x : Over.mk t ⟶ P.A, x ^ M = 1 → (x ≫ o.act a) ≫ θ.hom = x ≫ o.act a)
    (x : Over.mk t ⟶ P.A) (hx : x ^ M = 1) : x ≫ θ.hom = x := by
  have := o.hom
  have hW := hL.weil S P M (Over.mk t)
  refine ConjIdeal.fix_torsion_of_fix_conj_rel bar I hsup M hIJ (A := Γ((Over.mk t).left, ⊤)ˣ)
    (fun a => IsMonHom.monoidHom (o.act a) (Over.mk t)) (fun x => ?_) (fun a b x => ?_) (fun a b x => ?_)
    (fun x y c => WeilIs P.A P.L M x y c) hW.1 (fun x x' y c c' _ _ _ => hW.2.1 x x' y c c')
    (fun x hx h => ThetaRep.eq_one_of_weilIs hL P t hF x hx h) (fun a x y c hx hy h => ?_)
    (IsMonHom.monoidHom θ.hom (Over.mk t)) (fun a x _ => ?_) (fun x y c hx hy h => ?_) hfix x hx
  · show x ≫ o.act 1 = x
    rw [o.map_one, Category.comp_id]
  · show x ≫ o.act (a + b) = (x ≫ o.act a) * (x ≫ o.act b)
    rw [o.map_add, ← MonObj.comp_mul]
    rfl
  · show x ≫ o.act (a * b) = (x ≫ o.act b) ≫ o.act a
    rw [o.map_mul, Category.assoc]
  · refine (weilIs_rosati_iff hL.globalFns hL.cube P _ _ (o.rosati a) M x y hx hy c).2 ?_
    rw [hbar]
    exact h
  · show (x ≫ o.act a) ≫ θ.hom = (x ≫ θ.hom) ≫ o.act a
    rw [Category.assoc, hact, Category.assoc]
  · exact (weilIs_iso_iff hL.globalFns hL.cube P P θ w hw M x y hx hy c).2 h

/- English proof (translation)
Introduce and unpack `rfl`. Establish `z : Sp F` using `(default : PrimeSpectrum F)`. Use `choose j hj using fun k => exists_chart hM (pt k z)`. Use `choose j₀ hj₀ using fun k => exists_chart hM₀ (φ (pt k z))`. Use `((genRel_iff w t t₀ 0 z).1 h).2 j j₀ hj₀ hj` as an intermediate fact.

Rewrite `this` using `[map_zero, zero_mul]`. Conclude with `Units.ne_zero _ this`.
-/
theorem genRel_ne_zero {F : Type} [Field F] {B B₀ : Scheme.{0}} {M : LB B} {M₀ : LB B₀} (hM : M.IsLB) (hM₀ : M₀.IsLB)
    {φ : B ⟶ B₀} {w : LB.Iso M (M₀.pull φ)} {K : Type} [Fintype K] {pt : K → (Sp F ⟶ B)} {pt₀ : K → (Sp F ⟶ B₀)}
    {ε : K → ℤ} {t : LB.Gen (LB.LinComb M pt ε)} {t₀ : LB.Gen (LB.LinComb M₀ pt₀ ε)} {x : F}
    (h : GenRel w t t₀ x) : x ≠ 0 := by
  rintro rfl
  have z : Sp F := (default : PrimeSpectrum F)
  choose j hj using fun k => exists_chart hM (pt k z)
  choose j₀ hj₀ using fun k => exists_chart hM₀ (φ (pt k z))
  have := ((genRel_iff w t t₀ 0 z).1 h).2 j j₀ hj₀ hj
  rw [map_zero, zero_mul] at this
  exact Units.ne_zero _ this

section ThetaShiftProofs

open ArcTransport TorusExt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {c : Coeff l}
  {O : Type} [CommRing O] {β : O →+* c.F} {O' : Type} [CommRing O'] [IsDomain O'] {b : O →+* O'}
  (a : ArcIn D l β O' b) {R : Type} [CommRing R] [IsDomain R] {f : O' →+* R} {u : R}
  {P : DegPre R} [Module (𝓞 E) P.X]
  {φ : P.P.A.left ⟶ a.D₀.P.A.left} (w : LB.Iso P.P.L (a.D₀.P.L.pull φ)) (e : a.D₀.X ≃ₗ[𝓞 E] P.X)
  {F : Type} [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing O') F] (uF : F)

def IsTransport {n : ℕ} (q₀ : QkPt a.D₀ F n) (q : QkPt P F n) : Prop :=
  q.y = e q₀.y ∧ ∀ z, GenRel w (q.g.s (e z)) (q₀.g.s z) (uF ^ (a.be q₀.y z / n))

/- English proof (translation)
The claim follows from `((Int.natCast_dvd_natCast.2 hn).mul_left 2).trans (a.be_dvd y z)`.
-/
theorem dvd_be {n : ℕ} (hn : n ∣ l.M') (y z : a.D₀.X) : (n : ℤ) ∣ a.be y z :=
  ((Int.natCast_dvd_natCast.2 hn).mul_left 2).trans (a.be_dvd y z)

/- English proof (translation)
Establish `h₁ : (2 : ℤ) ∣ a.be x x` using `(Dvd.intro _ rfl).trans (a.be_dvd x x)`. Establish `h₂ : (2 : ℤ) ∣ a.be χ χ` using `(Dvd.intro _ rfl).trans (a.be_dvd χ χ)`. Establish `h₃` using `a.be_symm χ x`. Simplify using `only [map_add, LinearMap.add_apply]`. Use linear arithmetic over natural numbers and integers.
-/
theorem be_half (x χ : a.D₀.X) : a.be (x + χ) (x + χ) / 2 = a.be x χ + a.be x x / 2 + a.be χ χ / 2 := by
  have h₁ : (2 : ℤ) ∣ a.be x x := (Dvd.intro _ rfl).trans (a.be_dvd x x)
  have h₂ : (2 : ℤ) ∣ a.be χ χ := (Dvd.intro _ rfl).trans (a.be_dvd χ χ)
  have h₃ := a.be_symm χ x
  simp only [map_add, LinearMap.add_apply]
  omega

variable {a w e uF}

/- English proof (translation)
Simplify using `only [GtRel, Units.val_zpow_eq_zpow_val, Units.val_mk0]`. Conclude with `Iff.rfl`.
-/
theorem gtRel_zpow (h0 : uF ≠ 0) (m : a.D₀.X → ℤ) (g₀ : GtPtF a.D₀ F) (g : GtPtF P F) :
    GtRel w e.toAddEquiv (fun z => Units.mk0 uF h0 ^ m z) g₀ g ↔
      ∀ z, GenRel w (g.s (e z)) (g₀.s z) (uF ^ m z) := by
  simp only [GtRel, Units.val_zpow_eq_zpow_val, Units.val_mk0]
  exact Iff.rfl

variable [IsAlgClosed F] {oP : letI := H.starRing; P.OAct (𝓞 E)}
  {he : eSec P.P.A ≫ φ = spMap f ≫ eSec a.D₀.P.A} (hW : Match a f u P oP φ he w e)
  (hF : ∀ x, algebraMap (FractionRing O') F (algebraMap O' _ x) = algebraMap (FractionRing R) F (algebraMap R _ (f x)))
  (hu : uF = algebraMap (FractionRing R) F (algebraMap R _ u))

include hW hF hu

/- English proof (translation)
Use `a.nontriv` as an intermediate fact. Take `⟨y, hy⟩` from `exists_ne (0 : a.D₀.X)`. Establish `h` using `genRel_ne_zero P.P.isLB a.D₀.P.isLB (hW.2.2.2.2.2 F uF hF hu y)`. Establish `h₁ : (2 : ℤ) ∣ a.be y y` using `(Dvd.intro _ rfl).trans (a.be_dvd y y)`. Establish `h₂` using `a.be_pos y hy`.

Introduce and unpack `rfl`. Conclude with `h (zero_zpow _ (by omega))`.
-/
theorem u_ne_zero : uF ≠ 0 := by
  have := a.nontriv
  obtain ⟨y, hy⟩ := exists_ne (0 : a.D₀.X)
  have h := genRel_ne_zero P.P.isLB a.D₀.P.isLB (hW.2.2.2.2.2 F uF hF hu y)
  have h₁ : (2 : ℤ) ∣ a.be y y := (Dvd.intro _ rfl).trans (a.be_dvd y y)
  have h₂ := a.be_pos y hy
  rintro rfl
  exact h (zero_zpow _ (by omega))

/- English proof (translation)
Establish `h0` using `u_ne_zero hW hF hu`. Take `⟨gp, hw, hr, -, hc, hψ⟩` from `id hW`. Use `GtRel.isIota gp (base_comm hF) (e := e.toAddEquiv) hc ((isGen_iff w).1 hw) hr (v := fun y => Units.mk0 uF h0 ^ (a.be y y / 2)) (fun χ => ?_) (fun χ => ?_) h hι` and prove the remaining obligations. Rewrite using `[Units.val_zpow_eq_zpow_val]`. Conclude with `hψ F uF hF hu χ`.

Rewrite using `[be_half, zpow_add, zpow_add]`.
-/
theorem isIota_of_rel {x : a.D₀.X} {g₀ : GtPtF a.D₀ F} {g : GtPtF P F}
    (h : GtRel w e.toAddEquiv (fun z => Units.mk0 uF (u_ne_zero hW hF hu) ^ a.be x z) g₀ g) (hι : GtPtF.IsIota x g₀) :
    GtPtF.IsIota (e x) g := by
  have h0 := u_ne_zero hW hF hu
  obtain ⟨gp, hw, hr, -, hc, hψ⟩ := id hW
  refine GtRel.isIota gp (base_comm hF) (e := e.toAddEquiv) hc ((isGen_iff w).1 hw) hr
    (v := fun y => Units.mk0 uF h0 ^ (a.be y y / 2)) (fun χ => ?_) (fun χ => ?_) h hι
  · rw [Units.val_zpow_eq_zpow_val]
    exact hψ F uF hF hu χ
  · rw [be_half, zpow_add, zpow_add]

/- English proof (translation)
Establish `h0` using `u_ne_zero hW hF hu`. Establish `hι'` using `fun x g₀ g => isIota_of_rel hW hF hu (x := x) (g₀ := g₀) (g := g)`. Take `⟨gp, hw, hr, -, hc, hψ⟩` from `id hW`. Establish `hT` using `base_comm hF`. Establish `hw'` using `(isGen_iff w).1 hw`.

Establish `ex : ∀ (i : ℕ) (g₀ : GtPtF a.D₀ F), ∃ g : GtPtF P F, GtRel w e.toAddEquiv (fun z => Units.mk0 uF h0 ^ ((i : ℤ) * (a.be q₀.y z / n))) g₀ g` using `fun i g₀ => exists_gtRel gp hT (e := e.toAddEquiv) hc hw' hG _ (fun x y => by`. Rewrite using `[map_add, Int.add_ediv_of_dvd_left (dvd_be a hn _ _), mul_add, zpow_add]) g₀`. Use `choose dn hdn using ex`. Take `⟨h, ⟨gs, g₀, gst, gl⟩, hι⟩` from `q₀.eq`. Use `⟨⟨e q₀.y, dn 1 q₀.g, dn n h, ⟨fun i => dn i (gs i), ?_, fun i => ?_, congrArg (dn n) gl⟩, hι' _ h _ ?_ hι⟩, rfl, ?_⟩` and prove the remaining obligations.

Conclude with `GtRel.isZero gp hT (e := e.toAddEquiv) hc hw' (fun χ => by simp) (hdn _ _) g₀`. Use `GtRel.isAdd gp hT (e := e.toAddEquiv) hc hw' hG (fun χ => ?_) (hdn _ _) (hdn _ _) (hdn _ _) (gst i)` and prove the remaining obligations. Rewrite using `[← zpow_add, ← add_mul]`. Simplify using the standard rewrite rules. Use `hdn n h` as an intermediate fact.

Simplify using `only [Int.mul_ediv_cancel' (dvd_be a hn _ _)] at this`. Conclude with `this`. Use `hdn 1 q₀.g` as an intermediate fact. Simplify using `only [Nat.cast_one, _root_.one_mul] at this`. Conclude with `(gtRel_zpow h0 _ _ _).1 this`.
-/
theorem exists_transport (hG : GlobalFnsSt) {n : ℕ} (hn : n ∣ l.M') (q₀ : QkPt a.D₀ F n) :
    ∃ q : QkPt P F n, IsTransport a w e uF q₀ q := by
  have h0 := u_ne_zero hW hF hu
  have hι' := fun x g₀ g => isIota_of_rel hW hF hu (x := x) (g₀ := g₀) (g := g)
  obtain ⟨gp, hw, hr, -, hc, hψ⟩ := id hW
  have hT := base_comm hF
  have hw' := (isGen_iff w).1 hw
  have ex : ∀ (i : ℕ) (g₀ : GtPtF a.D₀ F), ∃ g : GtPtF P F,
      GtRel w e.toAddEquiv (fun z => Units.mk0 uF h0 ^ ((i : ℤ) * (a.be q₀.y z / n))) g₀ g :=
    fun i g₀ => exists_gtRel gp hT (e := e.toAddEquiv) hc hw' hG _ (fun x y => by
      rw [map_add, Int.add_ediv_of_dvd_left (dvd_be a hn _ _), mul_add, zpow_add]) g₀
  choose dn hdn using ex
  obtain ⟨h, ⟨gs, g₀, gst, gl⟩, hι⟩ := q₀.eq
  refine ⟨⟨e q₀.y, dn 1 q₀.g, dn n h, ⟨fun i => dn i (gs i), ?_, fun i => ?_, congrArg (dn n) gl⟩, hι' _ h _ ?_ hι⟩,
    rfl, ?_⟩
  · exact GtRel.isZero gp hT (e := e.toAddEquiv) hc hw' (fun χ => by simp) (hdn _ _) g₀
  · refine GtRel.isAdd gp hT (e := e.toAddEquiv) hc hw' hG (fun χ => ?_) (hdn _ _) (hdn _ _) (hdn _ _) (gst i)
    rw [← zpow_add, ← add_mul]
    simp
  · have := hdn n h
    simp only [Int.mul_ediv_cancel' (dvd_be a hn _ _)] at this
    exact this
  · have := hdn 1 q₀.g
    simp only [Nat.cast_one, _root_.one_mul] at this
    exact (gtRel_zpow h0 _ _ _).1 this

omit [IsAlgClosed F] hW hF hu in

/- English proof (translation)
The claim follows from `(h.2 0).1 2`.
-/
theorem IsTransport.b_comp {n : ℕ} {q₀ : QkPt a.D₀ F n} {q : QkPt P F n} (h : IsTransport a w e uF q₀ q) :
    q.g.b.left ≫ φ = q₀.g.b.left := (h.2 0).1 2

/- English proof (translation)
Establish `h0` using `u_ne_zero hW hF hu`. Establish `hι'` using `fun x g₀ g => isIota_of_rel hW hF hu (x := x) (g₀ := g₀) (g := g)`. Take `⟨gp, hw, hr, -, hc, hψ⟩` from `id hW`. Establish `hT` using `base_comm hF`. Establish `hw'` using `(isGen_iff w).1 hw`.

Take `⟨z, hy, g₀, hι, hadd⟩` from `H`. Take `⟨g, hg⟩` from `exists_gtRel gp hT (e := e.toAddEquiv) hc hw' hG (fun χ => Units.mk0 uF h0 ^ a.be z χ) (fun x y => by rw [map_add, zpow_add]) g₀`. Use `⟨e z, by rw [h'.1, h.1, hy, map_add, map_nsmul], g, hι' z g₀ g hg hι, ?_⟩` and prove the remaining obligations. Use `GtRel.isAdd gp hT (e := e.toAddEquiv) hc hw' hG (fun χ => ?_) ((gtRel_zpow h0 _ _ _).2 h.2) hg ((gtRel_zpow h0 _ _ _).2 h'.2) hadd` and prove the remaining obligations. Rewrite using `[← zpow_add, hy, map_add, map_nsmul, LinearMap.add_apply, LinearMap.smul_apply, nsmul_eq_mul, Int.add_mul_ediv_left _ _ (Int.natCast_ne_zero.2 hn₀.ne')]`.
-/
theorem IsTransport.equiv (hG : GlobalFnsSt) {n : ℕ} (hn₀ : 0 < n) (hn : n ∣ l.M') {q₀ q₀' : QkPt a.D₀ F n}
    {q q' : QkPt P F n} (h : IsTransport a w e uF q₀ q) (h' : IsTransport a w e uF q₀' q')
    (H : QkPt.Equiv a.D₀ F q₀ q₀') : QkPt.Equiv P F q q' := by
  have h0 := u_ne_zero hW hF hu
  have hι' := fun x g₀ g => isIota_of_rel hW hF hu (x := x) (g₀ := g₀) (g := g)
  obtain ⟨gp, hw, hr, -, hc, hψ⟩ := id hW
  have hT := base_comm hF
  have hw' := (isGen_iff w).1 hw
  obtain ⟨z, hy, g₀, hι, hadd⟩ := H
  obtain ⟨g, hg⟩ := exists_gtRel gp hT (e := e.toAddEquiv) hc hw' hG
    (fun χ => Units.mk0 uF h0 ^ a.be z χ) (fun x y => by rw [map_add, zpow_add]) g₀
  refine ⟨e z, by rw [h'.1, h.1, hy, map_add, map_nsmul], g, hι' z g₀ g hg hι, ?_⟩
  refine GtRel.isAdd gp hT (e := e.toAddEquiv) hc hw' hG (fun χ => ?_) ((gtRel_zpow h0 _ _ _).2 h.2) hg
    ((gtRel_zpow h0 _ _ _).2 h'.2) hadd
  rw [← zpow_add, hy, map_add, map_nsmul, LinearMap.add_apply, LinearMap.smul_apply, nsmul_eq_mul,
    Int.add_mul_ediv_left _ _ (Int.natCast_ne_zero.2 hn₀.ne')]

/- English proof (translation)
Establish `h0` using `u_ne_zero hW hF hu`. Take `⟨gp, hw, -, -, hc, -⟩` from `hW`. Take `⟨h₁, h₂⟩` from `GtRel.torus gp (base_comm hF) (e := e.toAddEquiv) hc ((isGen_iff w).1 hw) ((gtRel_zpow h0 _ _ _).2 h.2) ht.1 ht.2`. Use `⟨h₁, fun χ j hj hle => (h₂ χ j hj hle).trans ?_⟩` and prove the remaining obligations. Rewrite using `[hy, map_zero, LinearMap.zero_apply, Int.zero_ediv, zpow_zero, Units.val_one, _root_.one_mul]`.

Both sides reduce to the same expression.
-/
theorem IsTransport.torus {n : ℕ} {q₀ : QkPt a.D₀ F n} {q : QkPt P F n} (h : IsTransport a w e uF q₀ q)
    (hy : q₀.y = 0) {t : a.D₀.X → F} (ht : IsTorusPtF q₀.g t) : IsTorusPtF q.g fun χ => t (e.symm χ) := by
  have h0 := u_ne_zero hW hF hu
  obtain ⟨gp, hw, -, -, hc, -⟩ := hW
  obtain ⟨h₁, h₂⟩ := GtRel.torus gp (base_comm hF) (e := e.toAddEquiv) hc ((isGen_iff w).1 hw)
    ((gtRel_zpow h0 _ _ _).2 h.2) ht.1 ht.2
  refine ⟨h₁, fun χ j hj hle => (h₂ χ j hj hle).trans ?_⟩
  rw [hy, map_zero, LinearMap.zero_apply, Int.zero_ediv, zpow_zero, Units.val_one, _root_.one_mul]
  rfl

end ThetaShiftProofs

section Rigid

open ArcTransport hiding IsTransport exists_transport
open TorusExt

attribute [local instance] gtGroup

/- English proof (translation)
Take `⟨z, hz, hg⟩` from `(equiv_iff hP _ _).1 h`. Rewrite `hz` using `[hy, hy', zero_add, eq_comm, ← natCast_zsmul, smul_eq_zero_iff_right (Int.natCast_ne_zero.2 hn)]`. Rewrite using `[hg, hz, map_zero, add_zero]`.
-/
theorem g_eq_of_equiv {R : Type} [CommRing R] [IsDomain R] {P : DegPre R} (hP : P.TauBimult) {F : Type} [Field F]
    [Algebra (FractionRing R) F] {n : ℕ} (hn : n ≠ 0) {q q' : QkPt P F n} (h : QkPt.Equiv P F q q') (hy : q.y = 0)
    (hy' : q'.y = 0) : q'.g = q.g := by
  obtain ⟨z, hz, hg⟩ := (equiv_iff hP _ _).1 h
  rw [hy, hy', zero_add, eq_comm, ← natCast_zsmul, smul_eq_zero_iff_right (Int.natCast_ne_zero.2 hn)] at hz
  rw [hg, hz, map_zero, add_zero]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {c : Coeff l}

/- English proof (translation)
Establish `h₁ : H.rt0 ∈ KA l` using `IntermediateField.subset_adjoin _ _ (by simp)`. Establish `h₂ : zeta l.A ∈ KA l` using `IntermediateField.subset_adjoin _ _ (by simp)`. Establish `key : ∀ (x : ℂ) (n : ℕ), 0 < n → x ^ n ∈ W → x ∈ W` using `fun x n hn hx => by`. Rewrite `hx`, the goal using `[← W.valuation_le_one_iff]`. Rewrite `hx` using `[map_pow]`.

Conclude with `(pow_le_one_iff hn.ne').1 hx`. Establish `m₁ : H.rt0 ∈ W` using `key _ 2 two_pos (by rw [H.sqrt_neg_disc_sq]; exact neg_mem (natCast_mem W _))`. Establish `m₂ : zeta l.A ∈ W` using `key _ l.A l.A_pos (by`. Rewrite using `[show zeta l.A ^ l.A = 1 from (Complex.isPrimitiveRoot_exp l.A l.A_pos.ne').pow_eq_one]`. Conclude with `one_mem W)`.

Conclude with `⟨⟨⟨_, c.le h₁⟩, m₁⟩, ⟨⟨_, c.le h₂⟩, m₂⟩, rfl, rfl⟩`.
-/
theorem exists_rt_zeta (c : Coeff l) (W : ValuationSubring ℂ) :
    ∃ r z : c.V W, (((c.V W).subtype r : c.F) : ℂ) = H.rt0 ∧ (((c.V W).subtype z : c.F) : ℂ) = zeta l.A := by
  have h₁ : H.rt0 ∈ KA l := IntermediateField.subset_adjoin _ _ (by simp)
  have h₂ : zeta l.A ∈ KA l := IntermediateField.subset_adjoin _ _ (by simp)
  have key : ∀ (x : ℂ) (n : ℕ), 0 < n → x ^ n ∈ W → x ∈ W := fun x n hn hx => by
    rw [← W.valuation_le_one_iff] at hx ⊢
    rw [map_pow] at hx
    exact (pow_le_one_iff hn.ne').1 hx
  have m₁ : H.rt0 ∈ W := key _ 2 two_pos (by rw [H.sqrt_neg_disc_sq]; exact neg_mem (natCast_mem W _))
  have m₂ : zeta l.A ∈ W := key _ l.A l.A_pos (by
    rw [show zeta l.A ^ l.A = 1 from (Complex.isPrimitiveRoot_exp l.A l.A_pos.ne').pow_eq_one]; exact one_mem W)
  exact ⟨⟨⟨_, c.le h₁⟩, m₁⟩, ⟨⟨_, c.le h₂⟩, m₂⟩, rfl, rfl⟩

variable {O : Type} [CommRing O] {β : O →+* c.F} {O' : Type} [CommRing O'] [IsDomain O'] {b : O →+* O'}
  {a : ArcIn D l β O' b} {R : Type} [CommRing R] [IsDomain R] {f : O' →+* R} {u : R}
  {P : DegPre R} [Module (𝓞 E) P.X] {oP : letI := H.starRing; P.OAct (𝓞 E)}
  {φ₁ φ₂ : P.P.A.left ⟶ a.D₀.P.A.left} {he₁ : eSec P.P.A ≫ φ₁ = spMap f ≫ eSec a.D₀.P.A}
  {he₂ : eSec P.P.A ≫ φ₂ = spMap f ≫ eSec a.D₀.P.A}
  {w₁ : LB.Iso P.P.L (a.D₀.P.L.pull φ₁)} {w₂ : LB.Iso P.P.L (a.D₀.P.L.pull φ₂)} {e₁ e₂ : a.D₀.X ≃ₗ[𝓞 E] P.X}
  {F : Type} [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Algebra (FractionRing O') F] {uF : F}
  (hP : P.TauBimult) (W₁ : Match a f u P oP φ₁ he₁ w₁ e₁) (W₂ : Match a f u P oP φ₂ he₂ w₂ e₂)
  (hF : ∀ x, algebraMap (FractionRing O') F (algebraMap O' _ x) = algebraMap (FractionRing R) F (algebraMap R _ (f x)))
  (hu : uF = algebraMap (FractionRing R) F (algebraMap R _ u))
  (hrz : ∃ r z : O, ((β r : c.F) : ℂ) = H.rt0 ∧ ((β z : c.F) : ℂ) = zeta l.A)
  (hlev : ∀ v ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), ∀ (q₀ : QkPt a.D₀ F l.M)
    (q₁ q₂ : QkPt P F l.M), QkExt (algebraMap _ F) (a.eta v) q₀ → IsTransport a w₁ e₁ uF q₀ q₁ →
      IsTransport a w₂ e₂ uF q₀ q₂ → QkPt.Equiv P F q₁ q₂)

include hP W₁ W₂ hF hu hrz hlev

/- English proof (translation)
Use `letI := H.starRing`. Establish `h₀ : 0 < l.M` using `lt_of_lt_of_le three_pos l.three_le`. Establish `h₁ : l.M ∣ l.M'` using `Nat.dvd_lcm_left _ _`. Take `⟨r, z, hr, hz⟩` from `hrz`. Take `⟨-, I, -, -, hI⟩` from `a.geom F r z hr hz _ rfl`.

Take `⟨v, hv⟩` from `I.onto _ h₀ p`. Establish `hm : x • v ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La)` using `Submodule.smul_mem_smul hx trivial`. Take `⟨q, hq, -⟩` from `existsUnique_qkExt a.bimult (algebraMap (FractionRing O') F) (RingHom.comp_id _) (a.eta (x • v))`. Establish `e : QkPt.Equiv a.D₀ F q (qkSmul a.bimult hG a.oa x p)` using `equiv_trans a.bimult (hI _ hm q hq) (equiv_trans a.bimult (equiv_symm a.bimult ((qkAct_iff a.bimult hG a.oa _ _ _).1 (I.lin _ h₀ x v))) (qkSmul_congr a.bimult hG a.oa x hv))`. Take `⟨q₁, t₁⟩` from `exists_transport W₁ hF hu hG h₁ (qkSmul a.bimult hG a.oa x p)`.

Take `⟨q₂, t₂⟩` from `exists_transport W₂ hF hu hG h₁ (qkSmul a.bimult hG a.oa x p)`. Take `⟨q₁', t₁'⟩` from `exists_transport W₁ hF hu hG h₁ q`. Take `⟨q₂', t₂'⟩` from `exists_transport W₂ hF hu hG h₁ q`. Conclude with `⟨q₁, q₂, t₁, t₂, equiv_trans hP (equiv_symm hP (t₁'.equiv W₁ hF hu hG h₀ h₁ t₁ e)) (equiv_trans hP (hlev _ hm q q₁' q₂' hq t₁' t₂') (t₂'.equiv W₂ hF hu hG h₀ h₁ t₂ e))⟩`.
-/
theorem exists_equiv (hG : GlobalFnsSt) {x : 𝓞 E} (hx : x ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) (p : QkPt a.D₀ F l.M) :
    letI := H.starRing
    ∃ q₁ q₂ : QkPt P F l.M, IsTransport a w₁ e₁ uF (qkSmul a.bimult hG a.oa x p) q₁ ∧
      IsTransport a w₂ e₂ uF (qkSmul a.bimult hG a.oa x p) q₂ ∧ QkPt.Equiv P F q₁ q₂ := by
  letI := H.starRing
  have h₀ : 0 < l.M := lt_of_lt_of_le three_pos l.three_le
  have h₁ : l.M ∣ l.M' := Nat.dvd_lcm_left _ _
  obtain ⟨r, z, hr, hz⟩ := hrz
  obtain ⟨-, I, -, -, hI⟩ := a.geom F r z hr hz _ rfl
  obtain ⟨v, hv⟩ := I.onto _ h₀ p
  have hm : x • v ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La) := Submodule.smul_mem_smul hx trivial
  obtain ⟨q, hq, -⟩ := existsUnique_qkExt a.bimult (algebraMap (FractionRing O') F) (RingHom.comp_id _) (a.eta (x • v))
  have e : QkPt.Equiv a.D₀ F q (qkSmul a.bimult hG a.oa x p) :=
    equiv_trans a.bimult (hI _ hm q hq) (equiv_trans a.bimult
      (equiv_symm a.bimult ((qkAct_iff a.bimult hG a.oa _ _ _).1 (I.lin _ h₀ x v))) (qkSmul_congr a.bimult hG a.oa x hv))
  obtain ⟨q₁, t₁⟩ := exists_transport W₁ hF hu hG h₁ (qkSmul a.bimult hG a.oa x p)
  obtain ⟨q₂, t₂⟩ := exists_transport W₂ hF hu hG h₁ (qkSmul a.bimult hG a.oa x p)
  obtain ⟨q₁', t₁'⟩ := exists_transport W₁ hF hu hG h₁ q
  obtain ⟨q₂', t₂'⟩ := exists_transport W₂ hF hu hG h₁ q
  exact ⟨q₁, q₂, t₁, t₂, equiv_trans hP (equiv_symm hP (t₁'.equiv W₁ hF hu hG h₀ h₁ t₁ e))
    (equiv_trans hP (hlev _ hm q q₁' q₂' hq t₁' t₂') (t₂'.equiv W₂ hF hu hG h₀ h₁ t₂ e))⟩

/- English proof (translation)
Use `letI := H.starRing`. Establish `h₀ : l.M ≠ 0` using `(lt_of_lt_of_le three_pos l.three_le).ne'`. Establish `: NeZero (l.M : F)` using `⟨hM⟩`. Take `⟨ζ, hζ⟩` from `HasEnoughRootsOfUnity.exists_primitiveRoot F l.M`. Use `ConjIdeal.trans_symm_congr_one H.bar (fun x => star_star x) l.Mb l.coprime h₀ hζ e₁ e₂ (fun x hx y => ?_) (fun t ht x hx χ => ?_) y` and prove the remaining obligations.

Take `⟨p, rfl⟩` from `exists_qkPt (F := F) hL.mulN (Or.inr hL.polBaseChange) a.bimult h₀ y`. Take `⟨q₁, q₂, t₁, t₂, z, hz, -⟩` from `exists_equiv hP W₁ W₂ hF hu hrz hlev hL.globalFns hx p`. Conclude with `⟨z, t₂.1.symm.trans (hz.trans (congrArg (· + l.M • z) t₁.1))⟩`. Set `t' : Multiplicative a.D₀.X →* Fˣ` to `t.toMonoidHom.toHomUnits`. Establish `ht' : t' ^ l.M = 1` using `MonoidHom.ext fun v => Units.ext (ht v.toAdd)`.

Set `p : QkPt a.D₀ F l.M` to `qkMk a.bimult 0 (torusPt a.D₀ F (Additive.ofMul t')) (by`. Rewrite using `[← map_nsmul, ← ofMul_pow, ht', ofMul_one, map_zero, map_zero])`. Take `⟨q₁, q₂, t₁, t₂, hq⟩` from `exists_equiv hP W₁ W₂ hF hu hrz hlev hL.globalFns hx p`. Establish `hy : (qkSmul a.bimult hL.globalFns a.oa x p).y = 0` using `smul_zero x`. Establish `hT` using `(isTorusPtF_torusPt t').gtSmul hL.globalFns a.oa x`.

Establish `s₁` using `t₁.torus W₁ hF hu hy hT`. Establish `s₂` using `t₂.torus W₂ hF hu hy hT`. Rewrite `s₂` using `[g_eq_of_equiv hP h₀ hq (by rw [t₁.1, hy, map_zero]) (by rw [t₂.1, hy, map_zero])]`. Conclude with `congrFun (s₁.fun_unique s₂) χ`.
-/
theorem lattice_congr (hL : Laws) (hM : (l.M : F) ≠ 0) (y : a.D₀.X) :
    ∃ z, e₁.trans e₂.symm y = y + l.M • z := by
  letI := H.starRing
  have h₀ : l.M ≠ 0 := (lt_of_lt_of_le three_pos l.three_le).ne'
  have : NeZero (l.M : F) := ⟨hM⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot F l.M
  refine ConjIdeal.trans_symm_congr_one H.bar (fun x => star_star x) l.Mb l.coprime h₀ hζ e₁ e₂ (fun x hx y => ?_)
    (fun t ht x hx χ => ?_) y
  · obtain ⟨p, rfl⟩ := exists_qkPt (F := F) hL.mulN (Or.inr hL.polBaseChange) a.bimult h₀ y
    obtain ⟨q₁, q₂, t₁, t₂, z, hz, -⟩ := exists_equiv hP W₁ W₂ hF hu hrz hlev hL.globalFns hx p
    exact ⟨z, t₂.1.symm.trans (hz.trans (congrArg (· + l.M • z) t₁.1))⟩
  · let t' : Multiplicative a.D₀.X →* Fˣ := t.toMonoidHom.toHomUnits
    have ht' : t' ^ l.M = 1 := MonoidHom.ext fun v => Units.ext (ht v.toAdd)
    let p : QkPt a.D₀ F l.M := qkMk a.bimult 0 (torusPt a.D₀ F (Additive.ofMul t')) (by
      rw [← map_nsmul, ← ofMul_pow, ht', ofMul_one, map_zero, map_zero])
    obtain ⟨q₁, q₂, t₁, t₂, hq⟩ := exists_equiv hP W₁ W₂ hF hu hrz hlev hL.globalFns hx p
    have hy : (qkSmul a.bimult hL.globalFns a.oa x p).y = 0 := smul_zero x
    have hT := (isTorusPtF_torusPt t').gtSmul hL.globalFns a.oa x
    have s₁ := t₁.torus W₁ hF hu hy hT
    have s₂ := t₂.torus W₂ hF hu hy hT
    rw [g_eq_of_equiv hP h₀ hq (by rw [t₁.1, hy, map_zero]) (by rw [t₂.1, hy, map_zero])] at s₂
    exact congrFun (s₁.fun_unique s₂) χ

/- English proof (translation)
Set `σ : a.D₀.X ≃ₗ[ℤ] a.D₀.X` to `(e₁.trans e₂.symm).toAddEquiv.toIntLinearEquiv`. Establish `hd : ∀ y, a.be (σ y) (σ y) = a.be y y` using `fun y => by`. Use `hbe (e₁ y)` as an intermediate fact. Rewrite `this` using `[e₁.symm_apply_apply]`. Conclude with `this.symm`.

Establish `hσ : ∀ y z, a.be (σ y) (σ z) = a.be y z` using `fun y z => by`. Establish `h` using `hd (y + z)`. Establish `h₁` using `a.be_symm (σ z) (σ y)`. Establish `h₂` using `a.be_symm z y`. Simplify using `only [map_add, LinearMap.add_apply, hd] at h`.

Use linear arithmetic over natural numbers and integers. Take `⟨n, hn, hσn⟩` from `latFinOrdSt _ a.be a.be_symm a.be_pos σ hσ`. Establish `h` using `latMinkowski _ σ n l.M hn hσn l.three_le (lattice_congr hP W₁ W₂ hF hu hrz hlev hL hM)`. Use `LinearEquiv.ext fun y => ?_` and prove the remaining obligations. Establish `hy : e₂.symm (e₁ y) = y` using `congrArg (fun s : a.D₀.X ≃ₗ[ℤ] a.D₀.X => s y) h`.

Conclude with `e₂.symm_apply_eq.1 hy`.
-/
theorem lattice_eq (hL : Laws) (hM : (l.M : F) ≠ 0)
    (hbe : ∀ y, a.be (e₁.symm y) (e₁.symm y) = a.be (e₂.symm y) (e₂.symm y)) : e₁ = e₂ := by
  let σ : a.D₀.X ≃ₗ[ℤ] a.D₀.X := (e₁.trans e₂.symm).toAddEquiv.toIntLinearEquiv
  have hd : ∀ y, a.be (σ y) (σ y) = a.be y y := fun y => by
    have := hbe (e₁ y)
    rw [e₁.symm_apply_apply] at this
    exact this.symm
  have hσ : ∀ y z, a.be (σ y) (σ z) = a.be y z := fun y z => by
    have h := hd (y + z)
    have h₁ := a.be_symm (σ z) (σ y)
    have h₂ := a.be_symm z y
    simp only [map_add, LinearMap.add_apply, hd] at h
    omega
  obtain ⟨n, hn, hσn⟩ := latFinOrdSt _ a.be a.be_symm a.be_pos σ hσ
  have h := latMinkowski _ σ n l.M hn hσn l.three_le (lattice_congr hP W₁ W₂ hF hu hrz hlev hL hM)
  refine LinearEquiv.ext fun y => ?_
  have hy : e₂.symm (e₁ y) = y := congrArg (fun s : a.D₀.X ≃ₗ[ℤ] a.D₀.X => s y) h
  exact e₂.symm_apply_eq.1 hy

/- English proof (translation)
Use `letI := H.starRing`. Establish `h₀ : l.M ≠ 0` using `(lt_of_lt_of_le three_pos l.three_le).ne'`. Take `⟨p₁, g₁, -, a₁, -, -⟩` from `id W₁`. Take `⟨p₂, g₂, -, a₂, -, -⟩` from `id W₂`. Take `⟨θ, hθ, hφ⟩` from `grpPullback_iso p₁ p₂`.

Take `⟨wθ, -, hg, -, -⟩` from `exists_iso_pull_cancel a.D₀.P.isLB P.P.isLB P.P.isLB hφ w₁ w₂ g₁ g₂`. Establish `hact : ∀ x, oP.onB.act x ≫ θ.hom = θ.hom ≫ oP.onB.act x` using `fun x => by`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Apply `p₂.1.hom_ext` to reduce the goal to its premises. Rewrite using `[Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, hφ, a₁, a₂, ← Category.assoc, hφ]`.

Rewrite using `[Over.w, Over.w]`. Set `j : R →+* F` to `(algebraMap (FractionRing R) F).comp (algebraMap R _)`. Establish `hj : Function.Injective j` using `(algebraMap (FractionRing R) F).injective.comp (IsFractionRing.injective R _)`. Establish `: IsDominant (spMap j)` using `⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical j).2 (by`. Rewrite using `[(RingHom.injective_iff_ker_eq_bot j).1 hj]`.

Conclude with `bot_le)⟩`. Establish `: IsDominant (jFK (R` using `R) F ≫ jK R) := by`. Rewrite using `[show jFK (R := R) F ≫ jK R = spMap j from (spMap_comp _ _).symm]`. Conclude with `this`. Establish `hT` using `base_comm hF`.

Establish `key : θ.hom = 𝟙 _`. Use `aut_eq_id hL P.P (jFK (R := R) F ≫ jK R) l.three_le hM θ wθ hg (fix_torsion hL P.P _ hM oP.onB H.bar (fun _ => rfl) l.Mb l.coprime l.prod.le θ wθ hg hact fun x hx y hy => ?_)` and prove the remaining obligations. Set `Φ : (TF (R` to `R) F ⟶ P.P.A) →* (TF (R := O') F ⟶ a.D₀.P.A) := MonoidHom.mk' (pushF p₁ hT) (pushF_mul p₁ hT)`. Take `⟨p, hp, hb⟩` from `exists_qkPt_of_torsion a.bimult h₀ (b := Φ y) (by rw [← map_pow, hy, map_one])`. Take `⟨q₁, q₂, t₁, t₂, hq⟩` from `exists_equiv hP W₁ W₂ hF hu hrz hlev hL.globalFns hx p`.

Establish `hy : (qkSmul a.bimult hL.globalFns a.oa x p).y = 0` using `(congrArg (x • ·) hp).trans (smul_zero x)`. Establish `hg` using `g_eq_of_equiv hP h₀ hq (by rw [t₁.1, hy, map_zero]) (by rw [t₂.1, hy, map_zero])`. Establish `b₀ : (qkSmul a.bimult hL.globalFns a.oa x p).g.b.left = (y ≫ oP.onB.act x).left ≫ φ₁`. Use `(congrArg Over.Hom.left (gtSmul_b hL.globalFns a.oa x p.g)).trans ?_` and prove the remaining obligations. Rewrite using `[hb, Over.comp_left, Over.comp_left, Category.assoc, a₁, ← Category.assoc]`.

Both sides reduce to the same expression. Establish `b₁ : q₁.g.b.left = (y ≫ oP.onB.act x).left` using `p₁.1.hom_ext (t₁.b_comp.trans b₀) (by rw [Over.w, Over.w])`. Use `Over.OverMorphism.ext (p₂.1.hom_ext ?_ (by rw [Over.w, Over.w]))` and prove the remaining obligations. Rewrite using `[Over.comp_left, Category.assoc, hφ, ← b₀, ← t₂.b_comp, hg, b₁]`. Rewrite using `[← hφ, key, Over.id_left, Category.id_comp]`.
-/
theorem map_eq [IsNoetherianRing R] (hL : Laws) (hM : (l.M : F) ≠ 0) : φ₁ = φ₂ := by
  letI := H.starRing
  have h₀ : l.M ≠ 0 := (lt_of_lt_of_le three_pos l.three_le).ne'
  obtain ⟨p₁, g₁, -, a₁, -, -⟩ := id W₁
  obtain ⟨p₂, g₂, -, a₂, -, -⟩ := id W₂
  obtain ⟨θ, hθ, hφ⟩ := grpPullback_iso p₁ p₂
  obtain ⟨wθ, -, hg, -, -⟩ := exists_iso_pull_cancel a.D₀.P.isLB P.P.isLB P.P.isLB hφ w₁ w₂ g₁ g₂
  have hact : ∀ x, oP.onB.act x ≫ θ.hom = θ.hom ≫ oP.onB.act x := fun x => by
    apply Over.OverMorphism.ext
    apply p₂.1.hom_ext
    · rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, hφ, a₁, a₂, ← Category.assoc, hφ]
    · rw [Over.w, Over.w]
  let j : R →+* F := (algebraMap (FractionRing R) F).comp (algebraMap R _)
  have hj : Function.Injective j := (algebraMap (FractionRing R) F).injective.comp (IsFractionRing.injective R _)
  have : IsDominant (spMap j) :=
    ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical j).2 (by
      rw [(RingHom.injective_iff_ker_eq_bot j).1 hj]; exact bot_le)⟩
  have : IsDominant (jFK (R := R) F ≫ jK R) := by
    rw [show jFK (R := R) F ≫ jK R = spMap j from (spMap_comp _ _).symm]
    exact this
  have hT := base_comm hF
  have key : θ.hom = 𝟙 _ := by
    refine aut_eq_id hL P.P (jFK (R := R) F ≫ jK R) l.three_le hM θ wθ hg
      (fix_torsion hL P.P _ hM oP.onB H.bar (fun _ => rfl) l.Mb l.coprime l.prod.le θ wθ hg hact fun x hx y hy => ?_)
    let Φ : (TF (R := R) F ⟶ P.P.A) →* (TF (R := O') F ⟶ a.D₀.P.A) := MonoidHom.mk' (pushF p₁ hT) (pushF_mul p₁ hT)
    obtain ⟨p, hp, hb⟩ := exists_qkPt_of_torsion a.bimult h₀ (b := Φ y) (by rw [← map_pow, hy, map_one])
    obtain ⟨q₁, q₂, t₁, t₂, hq⟩ := exists_equiv hP W₁ W₂ hF hu hrz hlev hL.globalFns hx p
    have hy : (qkSmul a.bimult hL.globalFns a.oa x p).y = 0 := (congrArg (x • ·) hp).trans (smul_zero x)
    have hg := g_eq_of_equiv hP h₀ hq (by rw [t₁.1, hy, map_zero]) (by rw [t₂.1, hy, map_zero])
    have b₀ : (qkSmul a.bimult hL.globalFns a.oa x p).g.b.left = (y ≫ oP.onB.act x).left ≫ φ₁ := by
      refine (congrArg Over.Hom.left (gtSmul_b hL.globalFns a.oa x p.g)).trans ?_
      rw [hb, Over.comp_left, Over.comp_left, Category.assoc, a₁, ← Category.assoc]
      rfl
    have b₁ : q₁.g.b.left = (y ≫ oP.onB.act x).left :=
      p₁.1.hom_ext (t₁.b_comp.trans b₀) (by rw [Over.w, Over.w])
    refine Over.OverMorphism.ext (p₂.1.hom_ext ?_ (by rw [Over.w, Over.w]))
    rw [Over.comp_left, Category.assoc, hφ, ← b₀, ← t₂.b_comp, hg, b₁]
  rw [← hφ, key, Over.id_left, Category.id_comp]

end Rigid

/- English proof (translation)
Introduce `hL _ E _ _ _ H D l c W₀ O' _ _ _ b a R _ _ _ f u hf P _ oP φ₁ φ₂ he₁ he₂ w₁ w₂ e₁ e₂ hP W₁ W₂ hbe hlev`. Set `F` to `AlgebraicClosure (FractionRing R)`. Set `g : O' →+* F` to `((algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R))).comp f`. Establish `hg : Function.Injective g` using `((algebraMap (FractionRing R) F).injective.comp (IsFractionRing.injective R _)).comp hf`. Use `letI : Algebra (FractionRing O') F := (IsFractionRing.lift (K := FractionRing O') hg).toAlgebra`.

Establish `hF : ∀ x, algebraMap (FractionRing O') F (algebraMap O' _ x) = algebraMap (FractionRing R) F (algebraMap R _ (f x))` using `fun x => IsFractionRing.lift_algebraMap (K := FractionRing O') hg x`. Establish `hM : (l.M : F) ≠ 0`. Rewrite using `[← map_natCast g, map_ne_zero_iff g hg]`. Conclude with `Nat.cast_ne_zero.2 (lt_of_lt_of_le three_pos l.three_le).ne'`. Establish `hl` using `fun v hv q₀ q₁ q₂ hq (t₁ : IsTransport a w₁ e₁ _ q₀ q₁) (t₂ : IsTransport a w₂ e₂ _ q₀ q₂) => hlev F _ hF rfl v hv q₀ q₁ q₂ hq t₁.1 t₂.1 t₁.2 t₂.2`.

Establish `hφ` using `map_eq hP W₁ W₂ hF rfl (exists_rt_zeta c W₀) hl hL hM`. Use `⟨hφ, lattice_eq hP W₁ W₂ hF rfl (exists_rt_zeta c W₀) hl hL hM hbe, ?_⟩` and prove the remaining obligations. Substitute `hφ` using the available equality. Conclude with `heq_of_eq (rigidified_iso_unique hL.globalFns P.P a.D₀.P.isLB φ₁ w₁ w₂ W₁.2.1 W₂.2.1 _ _ W₁.2.2.1 W₂.2.2.1)`.
-/
theorem rigid : Laws → Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (c : Coeff l) (W₀ : ValuationSubring ℂ) (O' : Type) [CommRing O'] [IsDomain O'] [CharZero O'] (b : c.V W₀ →+* O') (a : ArcIn D l (c.V W₀).subtype O' b) (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (f : O' →+* R) (u : R), Function.Injective f → ∀ (P : DegPre R) [Module (𝓞 E) P.X] (oP : letI := H.starRing; P.OAct (𝓞 E)) (φ₁ φ₂ : P.P.A.left ⟶ a.D₀.P.A.left) (he₁ : eSec P.P.A ≫ φ₁ = spMap f ≫ eSec a.D₀.P.A) (he₂ : eSec P.P.A ≫ φ₂ = spMap f ≫ eSec a.D₀.P.A) (w₁ : LB.Iso P.P.L (a.D₀.P.L.pull φ₁)) (w₂ : LB.Iso P.P.L (a.D₀.P.L.pull φ₂)) (e₁ e₂ : a.D₀.X ≃ₗ[𝓞 E] P.X), P.TauBimult → Match a f u P oP φ₁ he₁ w₁ e₁ → Match a f u P oP φ₂ he₂ w₂ e₂ → (∀ y, a.be (e₁.symm y) (e₁.symm y) = a.be (e₂.symm y) (e₂.symm y)) → (∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Algebra (FractionRing O') F] (uF : F), (∀ x, algebraMap (FractionRing O') F (algebraMap O' _ x) = algebraMap (FractionRing R) F (algebraMap R _ (f x))) → uF = algebraMap (FractionRing R) F (algebraMap R _ u) → ∀ v ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), ∀ (q₀ : QkPt a.D₀ F l.M) (q₁ q₂ : QkPt P F l.M), QkExt (algebraMap _ F) (a.eta v) q₀ → q₁.y = e₁ q₀.y → q₂.y = e₂ q₀.y → (∀ z, GenRel w₁ (q₁.g.s (e₁ z)) (q₀.g.s z) (uF ^ (a.be q₀.y z / l.M))) → (∀ z, GenRel w₂ (q₂.g.s (e₂ z)) (q₀.g.s z) (uF ^ (a.be q₀.y z / l.M))) → QkPt.Equiv P F q₁ q₂) → φ₁ = φ₂ ∧ e₁ = e₂ ∧ HEq w₁ w₂ := by
  intro hL _ E _ _ _ H D l c W₀ O' _ _ _ b a R _ _ _ f u hf P _ oP φ₁ φ₂ he₁ he₂ w₁ w₂ e₁ e₂ hP W₁ W₂ hbe hlev
  let F := AlgebraicClosure (FractionRing R)
  let g : O' →+* F := ((algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R))).comp f
  have hg : Function.Injective g :=
    ((algebraMap (FractionRing R) F).injective.comp (IsFractionRing.injective R _)).comp hf
  letI : Algebra (FractionRing O') F := (IsFractionRing.lift (K := FractionRing O') hg).toAlgebra
  have hF : ∀ x, algebraMap (FractionRing O') F (algebraMap O' _ x) =
      algebraMap (FractionRing R) F (algebraMap R _ (f x)) :=
    fun x => IsFractionRing.lift_algebraMap (K := FractionRing O') hg x
  have hM : (l.M : F) ≠ 0 := by
    rw [← map_natCast g, map_ne_zero_iff g hg]
    exact Nat.cast_ne_zero.2 (lt_of_lt_of_le three_pos l.three_le).ne'
  have hl := fun v hv q₀ q₁ q₂ hq (t₁ : IsTransport a w₁ e₁ _ q₀ q₁) (t₂ : IsTransport a w₂ e₂ _ q₀ q₂) =>
    hlev F _ hF rfl v hv q₀ q₁ q₂ hq t₁.1 t₂.1 t₁.2 t₂.2
  have hφ := map_eq hP W₁ W₂ hF rfl (exists_rt_zeta c W₀) hl hL hM
  refine ⟨hφ, lattice_eq hP W₁ W₂ hF rfl (exists_rt_zeta c W₀) hl hL hM hbe, ?_⟩
  subst hφ
  exact heq_of_eq (rigidified_iso_unique hL.globalFns P.P a.D₀.P.isLB φ₁ w₁ w₂ W₁.2.1 W₂.2.1 _ _ W₁.2.2.1 W₂.2.2.1)

end GlobalTheory.MatchRigid
