import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiltGraded
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AbPartActIsAdj
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FormallyUnramifiedEtaleCompletion
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IsSymmetricOfSymmetryGenerator
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsEqNsmul
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.RankMulFinrank
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TorsionSectionExtendsAbLocus
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.DeterminantConditionSpreadsOfDensePoints
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.AdmBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LinearUniformisationTorsionIsomorphism
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSiegelObjectLoweredLevel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelPointsCompatOfTateIsometriesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGradedTateIsoLowerDatumStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateIsoSpreadGenericNoetherianDomainStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LowDat.LowObj

section Triple

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {R : Type} [CommRing R] [IsDomain R]
  [IsLocalRing R] {I : Ideal R} {t : SAB H (Sp R)}

open GlobalTheory.CechPic in
/- English proof (translation)
Establish `h0` using `(cls_eq_zero_iff (LB.isLB_linComb hL _ _)).2 ⟨u, hu⟩`. Rewrite `h0` using `[cls_linComb hL, Fin.sum_univ_four]`. Establish `h1 : pull (eSec B) (cls _ hL) = 0` using `(cls_eq_zero_iff (pull_isLB hL _)).2 ⟨r, hr⟩`. Establish `h2 : pull (toUnit B ≫ η[B]).left (cls _ hL) = 0`. Rewrite using `[Over.comp_left, pull_comp]`.

Conclude with `(congrArg _ h1).trans (map_zero _)`. Use `(cls_eq_iff hL (LB.isLB_linComb hL _ _)).1 (Eq.trans ?_ (cls_cube_two hL _ _ _).symm)` and prove the remaining obligations. Establish `pm : ∀ a b : B ⟶ B, padd B a b = a * b` using `fun _ _ => rfl`. Simplify using `only [pm, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, h2, pull_id, smul_zero, add_zero, one_smul, neg_smul, Fin.isValue] at h0`. Rewrite using `[lam, Hom.one_def, h2, Over.id_left, pull_id, add_zero, eq_comm, ← sub_eq_zero, ← h0]`.

Normalize the expressions using the abelian group laws.
-/
theorem prim_of_gen {S : Scheme.{0}} (B : Over S) [GrpObj B] [IsCommMonObj B] (w : B ⟶ B) (L : LB B.left) (hL : L.IsLB)
    (r : LB.Gen (L.pull (eSec B))) (hr : r.IsGen)
    (u : LB.Gen (LB.LinComb L (K := Fin 4) ![(padd B (𝟙 _) w).left, 𝟙 B.left, w.left, (toUnit B ≫ η[B]).left]
      ![1, -2, -1, 2])) (hu : u.IsGen) : LBIso L (cubeLB B ![𝟙 _, w] L) := by
  have h0 := (cls_eq_zero_iff (LB.isLB_linComb hL _ _)).2 ⟨u, hu⟩
  rw [cls_linComb hL, Fin.sum_univ_four] at h0
  have h1 : pull (eSec B) (cls _ hL) = 0 := (cls_eq_zero_iff (pull_isLB hL _)).2 ⟨r, hr⟩
  have h2 : pull (toUnit B ≫ η[B]).left (cls _ hL) = 0 := by
    rw [Over.comp_left, pull_comp]
    exact (congrArg _ h1).trans (map_zero _)
  refine (cls_eq_iff hL (LB.isLB_linComb hL _ _)).1 (Eq.trans ?_ (cls_cube_two hL _ _ _).symm)
  have pm : ∀ a b : B ⟶ B, padd B a b = a * b := fun _ _ => rfl
  simp only [pm, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, h2, pull_id, smul_zero, add_zero,
    one_smul, neg_smul, Fin.isValue] at h0
  rw [lam, Hom.one_def, h2, Over.id_left, pull_id, add_zero, eq_comm, ← sub_eq_zero, ← h0]
  abel

/- English proof (translation)
Use `letI := H.starRing`. Take `⟨u, hu, -⟩` from `P.w0`. Conclude with `prim_of_gen _ _ _ P.D.toPre.P.isLB P.D.toPre.rig P.D.toPre.rig_gen u hu`.
-/
theorem abPart_prim (P : PELUnif I t) :
    LBIso P.D.toPre.P.L (cubeLB P.D.toPre.P.A ![𝟙 _, (GlobalTheory.LocM.abPartAct P).act H.w0] P.D.toPre.P.L) := by
  letI := H.starRing
  obtain ⟨u, hu, -⟩ := P.w0
  exact prim_of_gen _ _ _ P.D.toPre.P.isLB P.D.toPre.rig P.D.toPre.rig_gen u hu

def abTriple (P : PELUnif I t) : SAB H (Sp R) where
  G := P.D.toPre.P.A
  semi := isSemiAbelian_of_isAbelianScheme _ P.D.toPre.P.isAb
  act := GlobalTheory.LocM.abPartAct P
  PP := ⟨P.D.toPre.P.L, P.D.toPre.rig, P.D.toPre.P.isLB, P.D.toPre.rig_gen⟩
  cub := P.D.toPre.cub
  sym := isSymmetric_of_symmetry_generator _ P.D.toPre.sym P.D.toPre.sym_gen P.D.toPre.sym_rig
  adj := fun a => by
    have h := GlobalTheory.LocM.abPartAct_isAdj E H R I t P a
    rwa [← GlobalTheory.LocM.bar_eq_star H] at h
  prim := abPart_prim P

end Triple

section Generic

variable (R : Type) [CommRing R] [IsDomain R] (F : Type) [Field F] [Algebra (FractionRing R) F]

/- English proof (translation)
Rewrite using `[← Spec.map_comp]`. Both sides reduce to the same expression.
-/
theorem jFR_eq : jFK (R := R) F ≫ jK R =
    spMap ((algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R))) := by
  rw [← Spec.map_comp]; rfl

/- English proof (translation)
The claim follows from `(algebraMap (FractionRing R) F).injective.comp (IsFractionRing.injective R _)`.
-/
theorem inj_jFR : Function.Injective ((algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R))) :=
  (algebraMap (FractionRing R) F).injective.comp (IsFractionRing.injective R _)

/- English proof (translation)
Rewrite using `[jFR_eq]`. Conclude with `(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2 (by`. Conclude with `((RingHom.injective_iff_ker_eq_bot _).1 (inj_jFR R F)).le.trans bot_le)`.
-/
theorem dense_jFR : DenseRange (jFK (R := R) F ≫ jK R :) := by
  rw [jFR_eq]
  exact (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2 (by
    exact ((RingHom.injective_iff_ker_eq_bot _).1 (inj_jFR R F)).le.trans bot_le)

variable {R F}

/- English proof (translation)
Use `haveI : IsReduced (𝟙_ (Over (Sp R))).left := (inferInstance : IsReduced (Sp R))`. Use `haveI : IsDominant (jFK (R := R) F ≫ jK R) := ⟨dense_jFR R F⟩`. Establish `e : (toUnit (TF (R` using `R) F)).left = jFK (R := R) F ≫ jK R := (Category.comp_id _).symm.trans (Over.w (toUnit (TF (R := R) F)))`. Use `Over.OverMorphism.ext (ext_of_isDominant_of_isSeparated G.hom ((Over.w _).trans (Over.w _).symm) (jFK (R := R) F ≫ jK R) ?_)` and prove the remaining obligations. Rewrite using `[← e]`.

Conclude with `congrArg (·.left) h`.
-/
theorem section_ext {G : Over (Sp R)} [IsSeparated G.hom] {s s' : 𝟙_ (Over (Sp R)) ⟶ G}
    (h : toUnit (TF (R := R) F) ≫ s = toUnit (TF (R := R) F) ≫ s') : s = s' := by
  haveI : IsReduced (𝟙_ (Over (Sp R))).left := (inferInstance : IsReduced (Sp R))
  haveI : IsDominant (jFK (R := R) F ≫ jK R) := ⟨dense_jFR R F⟩
  have e : (toUnit (TF (R := R) F)).left = jFK (R := R) F ≫ jK R :=
    (Category.comp_id _).symm.trans (Over.w (toUnit (TF (R := R) F)))
  refine Over.OverMorphism.ext (ext_of_isDominant_of_isSeparated G.hom ((Over.w _).trans (Over.w _).symm)
    (jFK (R := R) F ≫ jK R) ?_)
  rw [← e]
  exact congrArg (·.left) h

/- English proof (translation)
Take `⟨y, hy⟩` from `GlobalTheory.UnifDvrCompare.exists_point_of_fixed (F := FractionRing R) x.left hσ`. Use `haveI : Epi (spMap (algebraMap (FractionRing R) F)) := by`. Establish `h1 : Surjective (spMap (algebraMap (FractionRing R) F))` using `⟨fun x => ⟨IsLocalRing.closedPoint F, Subsingleton.elim _ _⟩⟩`. Conclude with `Flat.epi_of_flat_of_surjective _`. Set `y' : TK R ⟶ G` to `Over.homMk y (by`.

Rewrite using `[← cancel_epi (spMap (algebraMap (FractionRing R) F)), ← Category.assoc, hy]`. Conclude with `Over.w x)`. Set `u : TF (R` to `R) F ⟶ TK R := Over.homMk (jFK (R := R) F) rfl`. Use `haveI : Epi u := by haveI : Epi u.left := inferInstanceAs (Epi (spMap (algebraMap (FractionRing R) F)))`. Conclude with `Over.epi_of_epi_left _`.

Establish `hu : u ≫ y' = x` using `Over.OverMorphism.ext hy`. Establish `hy' : y' ^ n = 1`. Rewrite using `[← cancel_epi u, MonObj.comp_pow, hu, hx, MonObj.comp_one]`. Use `haveI : IsDominant (jK R) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2 (by show RingHom.ker (algebraMap R (FractionRing R)) ≤ _`. Rewrite using `[(RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R _)]`.

Conclude with `bot_le)⟩`. Use `haveI : IsPreimmersion (jK R) := IsPreimmersion.of_isLocalization (nonZeroDivisors R)`. Use `haveI : Flat (jK R) := by`. Rewrite using `[HasRingHomProperty.Spec_iff (P := @Flat)]`. Conclude with `RingHom.flat_algebraMap_iff.2 (IsLocalization.flat _ (nonZeroDivisors R))`.

Take `⟨s, hs, hs'⟩` from `GlobalTheory.exists_section_of_pow_eq_one (GlobalTheory.Published.SemiAbelianHomExtension.isNormalScheme_spec R) (jK R) G n (by simpa using hn.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) (TK R) y' hy' (𝟙 _) (Category.id_comp _)`. Use `⟨Over.homMk s hs, Over.OverMorphism.ext ?_⟩` and prove the remaining obligations. Establish `e : (toUnit (TF (R` using `R) F)).left = jFK (R := R) F ≫ jK R := (Category.comp_id _).symm.trans (Over.w (toUnit (TF (R := R) F)))`. Rewrite using `[Over.comp_left, e, ← hy]`. Conclude with `(Category.assoc _ _ _).trans (congrArg _ (hs'.trans (Category.id_comp _)))`.
-/
theorem exists_section [IsNoetherianRing R] [IsIntegrallyClosed R] [IsGalois (FractionRing R) F]
    (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] [IsProper G.hom] (n : ℕ) (hn : IsUnit (n : R))
    (x : TF (R := R) F ⟶ G) (hx : x ^ n = 1)
    (hσ : ∀ σ : F ≃ₐ[FractionRing R] F, spMap (σ : F →+* F) ≫ x.left = x.left) :
    ∃ s : 𝟙_ (Over (Sp R)) ⟶ G, toUnit _ ≫ s = x := by
  obtain ⟨y, hy⟩ := GlobalTheory.UnifDvrCompare.exists_point_of_fixed (F := FractionRing R) x.left hσ
  haveI : Epi (spMap (algebraMap (FractionRing R) F)) := by
    have h1 : Surjective (spMap (algebraMap (FractionRing R) F)) :=
      ⟨fun x => ⟨IsLocalRing.closedPoint F, Subsingleton.elim _ _⟩⟩
    exact Flat.epi_of_flat_of_surjective _
  let y' : TK R ⟶ G := Over.homMk y (by
    rw [← cancel_epi (spMap (algebraMap (FractionRing R) F)), ← Category.assoc, hy]
    exact Over.w x)
  let u : TF (R := R) F ⟶ TK R := Over.homMk (jFK (R := R) F) rfl
  haveI : Epi u := by
    haveI : Epi u.left := inferInstanceAs (Epi (spMap (algebraMap (FractionRing R) F)))
    exact Over.epi_of_epi_left _
  have hu : u ≫ y' = x := Over.OverMorphism.ext hy
  have hy' : y' ^ n = 1 := by
    rw [← cancel_epi u, MonObj.comp_pow, hu, hx, MonObj.comp_one]
  haveI : IsDominant (jK R) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2 (by
    show RingHom.ker (algebraMap R (FractionRing R)) ≤ _
    rw [(RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R _)]
    exact bot_le)⟩
  haveI : IsPreimmersion (jK R) := IsPreimmersion.of_isLocalization (nonZeroDivisors R)
  haveI : Flat (jK R) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.2 (IsLocalization.flat _ (nonZeroDivisors R))
  obtain ⟨s, hs, hs'⟩ := GlobalTheory.exists_section_of_pow_eq_one (GlobalTheory.Published.SemiAbelianHomExtension.isNormalScheme_spec R)
    (jK R) G n (by simpa using hn.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) (TK R) y' hy' (𝟙 _)
    (Category.id_comp _)
  refine ⟨Over.homMk s hs, Over.OverMorphism.ext ?_⟩
  have e : (toUnit (TF (R := R) F)).left = jFK (R := R) F ≫ jK R :=
    (Category.comp_id _).symm.trans (Over.w (toUnit (TF (R := R) F)))
  rw [Over.comp_left, e, ← hy]
  exact (Category.assoc _ _ _).trans (congrArg _ (hs'.trans (Category.id_comp _)))

/- English proof (translation)
Take `⟨z, hz, g, hg, ha⟩` from `h`. Rewrite `hz` using `[hp, hq, zero_add, eq_comm, ← natCast_zsmul, smul_eq_zero_iff_right (Int.natCast_ne_zero.2 hk.ne')]`. Substitute `hz` using the available equality. Establish `c0 : D.c 0 = 1`. Use `D.c_add 0 0` as an intermediate fact.

Rewrite `this` using `[add_zero]`. Conclude with `mul_eq_left.1 this.symm`. Rewrite using `[ha.1, hg.1, DegPre.cF, c0, MonObj.comp_one]`. Conclude with `_root_.mul_one p.g.b`.
-/
theorem b_eq_of_equiv {D : DegPre R} {k : ℕ} (hk : 0 < k) {p q : QkPt D F k} (h : QkPt.Equiv D F p q) (hp : p.y = 0)
    (hq : q.y = 0) : q.g.b = p.g.b := by
  obtain ⟨z, hz, g, hg, ha⟩ := h
  rw [hp, hq, zero_add, eq_comm, ← natCast_zsmul, smul_eq_zero_iff_right (Int.natCast_ne_zero.2 hk.ne')] at hz
  subst hz
  have c0 : D.c 0 = 1 := by
    have := D.c_add 0 0
    rw [add_zero] at this
    exact mul_eq_left.1 this.symm
  rw [ha.1, hg.1, DegPre.cF, c0, MonObj.comp_one]
  exact _root_.mul_one p.g.b

end Generic

section Family

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]

/- English proof (translation)
Simplify using `only [spMap, ← Spec.map_comp]`. Both sides reduce to the same expression.
-/
theorem spMap_four {A B C D F : Type} [CommRing A] [CommRing B] [CommRing C] [CommRing D] [CommRing F] (a : A →+* B)
    (b : B →+* C) (c : C →+* D) (d : D →+* F) :
    spMap d ≫ spMap c ≫ spMap b ≫ spMap a = spMap ((d.comp (c.comp b)).comp a) := by
  simp only [spMap, ← Spec.map_comp]; rfl

/- English proof (translation)
Simplify using `[baseKA]`.
-/
theorem rho_val (l : Level H) : ((baseKA l).ρ : ℂ) = H.rt0 := by simp [baseKA]

/- English proof (translation)
The claim follows from `Subtype.ext (by simp only [IntermediateField.coe_inclusion, rho_val])`.
-/
theorem rho_eq (l : Level H) (c : Coeff l) :
    (IntermediateField.inclusion (ka_le l c)) (baseKA (lowLevel l)).ρ = (IntermediateField.inclusion c.le) (baseKA l).ρ :=
  Subtype.ext (by simp only [IntermediateField.coe_inclusion, rho_val])

def lowF (C : UChart.Fam Xo c R) (F : Type) [Field F] [Algebra (FractionRing R) F] : KA (lowLevel l) →+* F :=
  (toF C F).comp (IntermediateField.inclusion (ka_le l c)).toRingHom

/- English proof (translation)
Rewrite using `[Category.assoc]`. Conclude with `(congrArg (_ ≫ jK R ≫ ·) (spMap_comp _ _)).trans (spMap_four _ _ _ _)`.
-/
theorem jFR_lowS (C : UChart.Fam Xo c R) (F : Type) [Field F] [Algebra (FractionRing R) F] :
    (jFK (R := R) F ≫ jK R) ≫ lowS C = spMap (lowF C F) := by
  rw [Category.assoc]
  exact (congrArg (_ ≫ jK R ≫ ·) (spMap_comp _ _)).trans (spMap_four _ _ _ _)

/- English proof (translation)
Use `haveI := hR.1.1`. Use `haveI := hR.2`. Set `β : KA l →+* F` to `(toF C F).comp (IntermediateField.inclusion c.le).toRingHom`. Establish `hx : (jFK (R` using `R) F ≫ C.y ≫ pullback.fst _ _) ≫ Xo.s = spMap β := by`. Rewrite using `[Category.assoc, Category.assoc, pullback.condition, reassoc_of% C.y_over]`.

Conclude with `spMap_four _ _ _ _`. Establish `hdet` using `(Xo.univ.geom F _ β hx).1`. Establish `key : ∀ τ n, LieMult Xo.univ.t.act (jFK (R` using `R) F ≫ C.y ≫ pullback.fst _ _) τ n → LieMult (GlobalTheory.LocM.abPartAct C.P) (jFK (R := R) F ≫ jK R) τ (n - Module.finrank (𝓞 E) C.P.D.toPre.X) := by`. Introduce `τ n h`. Establish `h₁` using `(lieMult_iff_of_isGrpPullback m2.cart tK.act Xo.univ.t.act m2.act (jFK (R := R) F) τ n).2 h`.

Establish `h₂` using `(lieMult_iff_of_isGrpPullback m1.cart tK.act C.t.act m1.act (jFK (R := R) F) τ n).1 h₁`. Rewrite `h₂`, the goal using `[jFR_eq]`. Take `⟨m, hm, rfl⟩` from `GlobalTheory.CharRank.lieMult_unif_loc H R C.t C.P F _ (inj_jFR R F) τ n h₂`. Rewrite using `[Nat.add_sub_cancel]`. Conclude with `hm`.

Introduce `τ`. Establish `hρ : lowF C F (baseKA (lowLevel l)).ρ = β (baseKA l).ρ` using `congrArg (toF C F) (rho_eq l c)`. Rewrite using `[hρ, hp, hq]`. Conclude with `⟨fun h => key τ _ ((hdet τ).1 h), fun h => key τ _ ((hdet τ).2 h)⟩`.
-/
theorem detCond_generic (hR : GlobalTheory.Mum.Base R) (C : UChart.Fam Xo c R) (D' : Datum H)
    (hp : D'.p = Dw.p - Module.finrank (𝓞 E) C.P.D.toPre.X) (hq : D'.q = Dw.q - Module.finrank (𝓞 E) C.P.D.toPre.X)
    (tK : SAB H (Sp (FractionRing R))) (m1 : SABMap tK C.t (jK R))
    (m2 : SABMap tK Xo.univ.t (C.y ≫ pullback.fst _ _)) (F : Type) [Field F] [IsAlgClosed F]
    [Algebra (FractionRing R) F] :
    DetCond D' (GlobalTheory.LocM.abPartAct C.P) (jFK (R := R) F ≫ jK R) (lowF C F (baseKA (lowLevel l)).ρ) := by
  haveI := hR.1.1
  haveI := hR.2
  let β : KA l →+* F := (toF C F).comp (IntermediateField.inclusion c.le).toRingHom
  have hx : (jFK (R := R) F ≫ C.y ≫ pullback.fst _ _) ≫ Xo.s = spMap β := by
    rw [Category.assoc, Category.assoc, pullback.condition, reassoc_of% C.y_over]
    exact spMap_four _ _ _ _
  have hdet := (Xo.univ.geom F _ β hx).1
  have key : ∀ τ n, LieMult Xo.univ.t.act (jFK (R := R) F ≫ C.y ≫ pullback.fst _ _) τ n →
      LieMult (GlobalTheory.LocM.abPartAct C.P) (jFK (R := R) F ≫ jK R) τ (n - Module.finrank (𝓞 E) C.P.D.toPre.X) := by
    intro τ n h
    have h₁ := (lieMult_iff_of_isGrpPullback m2.cart tK.act Xo.univ.t.act m2.act (jFK (R := R) F) τ n).2 h
    have h₂ := (lieMult_iff_of_isGrpPullback m1.cart tK.act C.t.act m1.act (jFK (R := R) F) τ n).1 h₁
    rw [jFR_eq] at h₂ ⊢
    obtain ⟨m, hm, rfl⟩ := GlobalTheory.CharRank.lieMult_unif_loc H R C.t C.P F _ (inj_jFR R F) τ n h₂
    rw [Nat.add_sub_cancel]
    exact hm
  intro τ
  have hρ : lowF C F (baseKA (lowLevel l)).ρ = β (baseKA l).ρ := congrArg (toF C F) (rho_eq l c)
  rw [hρ, hp, hq]
  exact ⟨fun h => key τ _ ((hdet τ).1 h), fun h => key τ _ ((hdet τ).2 h)⟩

/- English proof (translation)
Establish `hd : (H.d : k) ≠ 0` using `Nat.cast_ne_zero.2 H.d_prime.ne_zero`. Establish `hb : (IsCMField.ringOfIntegersComplexConj E) H.rt = -H.rt`. Rewrite using `[← GlobalTheory.CharRank.bar_rt_neg H]`. Conclude with `RingOfIntegers.ext (by rw [H.bar_eq]; rfl)`. Establish `hr` using `GlobalTheory.LieRankSum.rank_mul_finrank E S P.A P.g P.smoothDim act k x (fun τ => if τ H.rt = ρ then D.p else D.q) (D.p + D.q) (fun τ => by`.

Establish `hs : τ H.rt ^ 2 = ρ ^ 2` using `by rw [← map_pow, H.rt_sq, hρ, map_neg, map_natCast]`. Establish `h0 : ρ ≠ -ρ` using `fun e => hd (by`. Establish `: ρ = 0` using `by linear_combination (1 / 2 : k) * e`. Rewrite `hρ` using `[this]`. Take the linear combination `hρ)`.

Establish `e : (τ.comp (IsCMField.ringOfIntegersComplexConj E : 𝓞 E →+* 𝓞 E)) H.rt = -τ H.rt`. Rewrite using `[← map_neg, ← hb]`. Both sides reduce to the same expression. Rewrite using `[e]`. Distinguish the cases in `hτ : τ H.rt = ρ`.

Use `⟨by rw [if_pos hτ]; exact (h τ).1 hτ, ?_⟩` and prove the remaining obligations. Rewrite using `[if_pos hτ, if_neg (by rw [hτ]; exact h0.symm)]`. Use `⟨by rw [if_neg hτ]; exact (h τ).2 hτ, ?_⟩` and prove the remaining obligations. Rewrite using `[if_neg hτ, if_pos (by rw [(sq_eq_sq_iff_eq_or_eq_neg.1 hs).resolve_left hτ, neg_neg]), add_comm])`. Use `D.fin` as an intermediate fact.

Use `D.proj` as an intermediate fact. Establish `: Module.Finite ℤ D.La` using `Module.Finite.trans (𝓞 E) D.La`. Establish `: Module.IsTorsionFree ℤ D.La` using `Module.IsTorsionFree.trans_faithfulSMul ℤ (𝓞 E) D.La`. Establish `: Module.Free ℤ D.La` using `Module.free_of_finite_type_torsion_free'`. Rewrite using `[← hr, GlobalTheory.finrank_int_eq_mul_of_finite (O := 𝓞 E), D.rank, RingOfIntegers.rank, mul_comm]`.
-/
theorem finrank_eq_of_detCond (D : Datum H) {S : Scheme.{0}} (P : PolAV S) (act : OAct (𝓞 E) P.A) {k : Type} [Field k]
    [IsAlgClosed k] [CharZero k] (x : Sp k ⟶ S) (ρ : k) (hρ : ρ ^ 2 = -(H.d : k)) (h : DetCond D act x ρ) :
    Module.finrank ℤ D.La = 2 * P.g := by
  classical
  have hd : (H.d : k) ≠ 0 := Nat.cast_ne_zero.2 H.d_prime.ne_zero
  have hb : (IsCMField.ringOfIntegersComplexConj E) H.rt = -H.rt := by
    rw [← GlobalTheory.CharRank.bar_rt_neg H]
    exact RingOfIntegers.ext (by rw [H.bar_eq]; rfl)
  have hr := GlobalTheory.LieRankSum.rank_mul_finrank E S P.A P.g P.smoothDim act k x
    (fun τ => if τ H.rt = ρ then D.p else D.q) (D.p + D.q) (fun τ => by
      have hs : τ H.rt ^ 2 = ρ ^ 2 := by rw [← map_pow, H.rt_sq, hρ, map_neg, map_natCast]
      have h0 : ρ ≠ -ρ := fun e => hd (by
        have : ρ = 0 := by linear_combination (1 / 2 : k) * e
        rw [this] at hρ
        linear_combination hρ)
      have e : (τ.comp (IsCMField.ringOfIntegersComplexConj E : 𝓞 E →+* 𝓞 E)) H.rt = -τ H.rt := by
        rw [← map_neg, ← hb]; rfl
      rw [e]
      by_cases hτ : τ H.rt = ρ
      · refine ⟨by rw [if_pos hτ]; exact (h τ).1 hτ, ?_⟩
        rw [if_pos hτ, if_neg (by rw [hτ]; exact h0.symm)]
      · refine ⟨by rw [if_neg hτ]; exact (h τ).2 hτ, ?_⟩
        rw [if_neg hτ, if_pos (by rw [(sq_eq_sq_iff_eq_or_eq_neg.1 hs).resolve_left hτ, neg_neg]), add_comm])
  have := D.fin
  have := D.proj
  have : Module.Finite ℤ D.La := Module.Finite.trans (𝓞 E) D.La
  have : Module.IsTorsionFree ℤ D.La := Module.IsTorsionFree.trans_faithfulSMul ℤ (𝓞 E) D.La
  have : Module.Free ℤ D.La := Module.free_of_finite_type_torsion_free'
  rw [← hr, GlobalTheory.finrank_int_eq_mul_of_finite (O := 𝓞 E), D.rank, RingOfIntegers.rank, mul_comm]

/- English proof (translation)
Use `haveI := hR.2`. Establish `hM : 0 < l.M'` using `(lowLevel l).A_pos`. Establish `hT` using `GlobalTheory.FlatTors.torsionIso_holds E H R _ hR.1 C.t C.P`. Take `⟨f, f₁, -, f₃, -⟩` from `hT F l.M' hM`. Take `⟨f', f₁', -, f₃', -⟩` from `hT F' l.M' hM`.

Establish `hx` using `GlobalTheory.T.levelPoints_compat_of_tateIsometries Xo c R hR C tK m1 m2 F F' σ I I' h h' a _ _ ((f₁ _ _).2 rfl) ((f₁' _ _).2 rfl)`. Rewrite `hx` using `[(f₃ _ _).2 e, (f₃' _ _).2 e']`. Take `⟨r, hr, -⟩` from `GlobalTheory.TorusExt.existsUnique_qkExt C.P.D.tau_bimult σ.toRingHom (RingHom.ext σ.commutes) q`. Establish `h₁` using `(GlobalTheory.TorsionExt.qkToAkU_iff_of_qkExt GlobalTheory.firstFiveLaws R _ hR.1 C.P.D C.P.A C.t.G C.t.semi C.P.U F F' σ l.M' hM q r _ _ hr hx).1 ((f₁ _ _).2 rfl)`. Rewrite using `[b_eq_of_equiv hM ((f₃' _ _).1 ((f₁' _ _).1 h₁).symm) (hr.1.trans hq) hq']`.

Conclude with `hr.2.1`.
-/
theorem b_eq_of_level (hR : GlobalTheory.Mum.Base R) (C : UChart.Fam Xo c R)
    (tK : SAB H (Sp (FractionRing R))) (m1 : SABMap tK C.t (jK R)) (m2 : SABMap tK Xo.univ.t (C.y ≫ pullback.fst _ _))
    {F F' : Type} [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Field F'] [IsAlgClosed F']
    [Algebra (FractionRing R) F'] (σ : F →ₐ[FractionRing R] F')
    (I : (letI := H.starRing; TateIsoQ Dw C.P.D.toPre C.P.oD F))
    (I' : (letI := H.starRing; TateIsoQ Dw C.P.D.toPre C.P.oD F'))
    (h : XFLevel C tK m1 m2 F I) (h' : XFLevel C tK m1 m2 F' I') (a : Dw.La)
    (q : QkPt C.P.D.toPre F l.M') (q' : QkPt C.P.D.toPre F' l.M')
    (e : QkPt.Equiv _ F (I.ev l.M' a) q) (e' : QkPt.Equiv _ F' (I'.ev l.M' a) q') (hq : q.y = 0) (hq' : q'.y = 0) :
    q'.g.b.left = spMap σ.toRingHom ≫ q.g.b.left := by
  haveI := hR.2
  have hM : 0 < l.M' := (lowLevel l).A_pos
  have hT := GlobalTheory.FlatTors.torsionIso_holds E H R _ hR.1 C.t C.P
  obtain ⟨f, f₁, -, f₃, -⟩ := hT F l.M' hM
  obtain ⟨f', f₁', -, f₃', -⟩ := hT F' l.M' hM
  have hx := GlobalTheory.T.levelPoints_compat_of_tateIsometries Xo c R hR C tK m1 m2 F F' σ I I' h h' a _ _ ((f₁ _ _).2 rfl) ((f₁' _ _).2 rfl)
  rw [(f₃ _ _).2 e, (f₃' _ _).2 e'] at hx
  obtain ⟨r, hr, -⟩ := GlobalTheory.TorusExt.existsUnique_qkExt C.P.D.tau_bimult σ.toRingHom (RingHom.ext σ.commutes) q
  have h₁ := (GlobalTheory.TorsionExt.qkToAkU_iff_of_qkExt GlobalTheory.firstFiveLaws R _ hR.1 C.P.D C.P.A C.t.G C.t.semi C.P.U F F' σ
    l.M' hM q r _ _ hr hx).1 ((f₁ _ _).2 rfl)
  rw [b_eq_of_equiv hM ((f₃' _ _).1 ((f₁' _ _).1 h₁).symm) (hr.1.trans hq) hq']
  exact hr.2.1

end Family

section Main

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero`. Rewrite using `[zero_smul, pow_zero]`. Establish `h` using `I.add n 0 0`. Rewrite `h` using `[add_zero]`.

Conclude with `mul_eq_left.1 h.symm`. Consider the case `succ m ih => rw [succ_nsmul, I.add, ih, pow_succ]`.
-/
theorem ev_nsmul {D : Datum H} {k : Type} [Field k] {Q : Type} [Group Q] {act : 𝓞 E → Q → Q}
    {e : ℕ → Q → Q → kˣ → Prop} (I : TateIso D k Q act e) (n m : ℕ) (v : D.La) : I.ev n (m • v) = I.ev n v ^ m := by
  induction m with
  | zero =>
    rw [zero_smul, pow_zero]
    have h := I.add n 0 0
    rw [add_zero] at h
    exact mul_eq_left.1 h.symm
  | succ m ih => rw [succ_nsmul, I.add, ih, pow_succ]

/- English proof (translation)
Establish `hM : 0 < l.M` using `by have := l.three_le; omega`. Establish `hm : 0 < m` using `Nat.pos_of_ne_zero fun h => by`. Use `(lowLevel l).A_pos` as an intermediate fact. Simplify using `only [lowLevel] at this`. Rewrite `this` using `[hk, h, mul_zero]`.

Conclude with `lt_irrefl 0 this`. Rewrite using `[ev_nsmul, hk, I.tower _ _ hM hm]`. Take `⟨c', hc'⟩` from `GlobalTheory.CM.RationalTorsion.exists_eq_nsmul D l l.prod hfm hw`. Establish `h1 : w = em • w + l.M • c'` using `by rw [← hc', ← add_smul, add_comm, hfe, one_smul]`. Use `conv_rhs => rw [h1]`.

Conclude with `(GlobalTheory.CM.RationalTorsion.ev_add_smul I hM _ _).symm`.
-/
theorem ev_eta {D : Datum H} (l : Level H) {k : Type} [Field k] {Q : Type} [Group Q] {act : 𝓞 E → Q → Q}
    {e : ℕ → Q → Q → kˣ → Prop} (I : TateIso D k Q act e) {fm em : 𝓞 E} (hfm : fm ∈ l.Mb)
    (hfe : fm + em = 1) {m : ℕ} (hk : l.M' = l.M * m) {w : D.La}
    (hw : w ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La)) :
    I.ev l.M' (m • (em • w)) = I.ev l.M w := by
  have hM : 0 < l.M := by have := l.three_le; omega
  have hm : 0 < m := Nat.pos_of_ne_zero fun h => by
    have := (lowLevel l).A_pos
    simp only [lowLevel] at this
    rw [hk, h, mul_zero] at this
    exact lt_irrefl 0 this
  rw [ev_nsmul, hk, I.tower _ _ hM hm]
  obtain ⟨c', hc'⟩ := GlobalTheory.CM.RationalTorsion.exists_eq_nsmul D l l.prod hfm hw
  have h1 : w = em • w + l.M • c' := by rw [← hc', ← add_smul, add_comm, hfe, one_smul]
  conv_rhs => rw [h1]
  exact (GlobalTheory.CM.RationalTorsion.ev_add_smul I hM _ _).symm

/- English proof (translation)
Simplify using `[baseKA]`.
-/
theorem zeta_val (l : Level H) : ((baseKA l).ζ : ℂ) = zeta l.A := by simp [baseKA]

/- English proof (translation)
The claim follows from `(Category.comp_id _).symm.trans (Over.w (toUnit T))`.
-/
theorem toUnit_left {S : Scheme.{0}} (T : Over S) : (toUnit T).left = T.hom :=
  (Category.comp_id _).symm.trans (Over.w (toUnit T))

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c R _ _ _ hR C Z D' f hZ hlow hrk hp hq tK m1 m2 hI`. Use `letI := H.starRing`. Use `haveI := hR.1.1`. Use `haveI := hR.2`. Use `haveI : IsIntegrallyClosed R := hR.1.2.2.1`.

Use `haveI : CharZero (FractionRing R) := charZero_of_injective_algebraMap (IsFractionRing.injective R _)`. Set `F0` to `AlgebraicClosure (FractionRing R)`. Use `haveI : CharZero F0 := charZero_of_injective_algebraMap (algebraMap (FractionRing R) F0).injective`. Take `⟨I0, hX0, hG0⟩` from `hI F0`. Rewrite `hp`, `hq` using `[hrk]`.

Establish `hdet0` using `detCond_generic hR C D' hp hq tK m1 m2 F0`. Establish `hρ0 : lowF C F0 (baseKA (lowLevel l)).ρ ^ 2 = -(H.d : F0)`. Rewrite using `[← map_pow, (baseKA _).ρ_sq, map_neg, map_natCast]`. Establish `hg` using `finrank_eq_of_detCond D' C.P.D.toPre.P (GlobalTheory.LocM.abPartAct C.P) _ _ hρ0 hdet0`. Establish `hy : ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (I : TateIsoQ Dw C.P.D.toPre C.P.oD F), FiltGraded C Z F I → ∀ n, 0 < n → ∀ a : perp Dw Z, ∃ q : QkPt C.P.D.toPre F n, QkPt.Equiv _ F (I.ev n a) q ∧ q.y = 0` using `fun F _ _ I h n hn a => (h n hn a).2 ⟨a, a.2, 0, by simp⟩`.

Take `⟨J0, hJ0ζ, hJ0b⟩` from `GlobalTheory.T.exists_gradedTateIso_lowerDatum Dw D' Z f hlow R hR C.t C.P F0 hg I0 (hy F0 I0 hG0)`. Establish `hM : 0 < l.M'` using `(lowLevel l).A_pos`. Establish `hunit : IsUnit (l.M' : R)`. Simplify using `using (isUnit_iff_ne_zero.2 (Nat.cast_ne_zero.2 hM.ne') : IsUnit ((l.M' : ℕ) : c.F)).map C.b`. Use `haveI := C.P.D.toPre.P.isAb.proper`.

Establish `hfix : ∀ (a : perp Dw Z) (σ : F0 ≃ₐ[FractionRing R] F0), spMap (σ : F0 →+* F0) ≫ (J0.ev l.M' (f a)).left = (J0.ev l.M' (f a)).left`. Introduce `a σ`. Take `⟨q, hq1, hq2⟩` from `hy F0 I0 hG0 l.M' hM a`. Rewrite using `[← hJ0b l.M' hM a q hq1 hq2]`. Conclude with `(b_eq_of_level hR C tK m1 m2 σ.toAlgHom I0 I0 hX0 hX0 a q q hq1 hq1 hq2 hq2).symm`.

Establish `hsec : ∀ w : D'.La, ∃ s : 𝟙_ (Over (Sp R)) ⟶ C.P.D.toPre.P.A, toUnit _ ≫ s = J0.ev l.M' w`. Introduce `w`. Take `⟨a, rfl⟩` from `hlow.1 w`. Conclude with `exists_section C.P.D.toPre.P.A l.M' hunit _ ((J0.onto _ hM _).2 ⟨_, rfl⟩) (hfix a)`. Use `choose sA hsA using hsec`.

Take `⟨fm, hfm, em, hem, hfe⟩ : ∃ x ∈ l.Mb, ∃ y ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E), x + y = 1` from `Submodule.mem_sup.1 (by rw [l.coprime]; trivial)`. Take `⟨m, hk⟩ : l.M ∣ l.M'` from `Nat.dvd_lcm_left _ _`. Establish `hζ0 : (J0.ζ l.M' : F0) = lowF C F0 (baseKA (lowLevel l)).ζ`. Rewrite using `[hJ0ζ, hX0.1]`. Conclude with `congrArg (toF C F0) (Subtype.ext (by`.

Simplify using `only [IntermediateField.coe_inclusion, zeta_val]`. Use the proof step `rfl))`. Set `o' : Obj D' (lowLevel l) (baseKA (lowLevel l)) (lowS C)` to `{ t := abTriple C.P proper := C.P.D.toPre.P.isAb.proper ample := C.P.D.toPre.P.ample ktriv := C.P.D.toPre.P.ktriv eta := fun w => sA (m • (em • w)) eta_add := fun a b => section_ext (F := F0) (by erw [MonObj.comp_mul, hsA, hsA, hsA, smul_add, smul_add]; exact J0.add _ _ _) eta_ke …`. Take `⟨c', hc'⟩` from `GlobalTheory.CM.RationalTorsion.exists_eq_nsmul D' l (by rw [mul_comm]; exact l.prod) hem ha`. Use `erw [MonObj.comp_one, hsA]`.

Conclude with `(J0.ker _ hM _).2 ⟨c', by rw [hc', smul_smul, hk, mul_comm]⟩)`. Use `etaA := sA`. Use `etaA_add := fun a b => section_ext (F := F0) (by erw [MonObj.comp_mul, hsA, hsA, hsA]; exact J0.add _ _ _)`. Use `etaA_ker := fun a => section_ext (F := F0) (by erw [MonObj.comp_one, hsA]`. Conclude with `(J0.ker _ hM _).2 ⟨a, rfl⟩)`.

Use `geom := by`. Introduce `k _ _ x β hx`. Use `haveI : CharZero k := charZero_of_injective_ringHom (f := β.comp (algebraMap ℚ (KA (lowLevel l)))) (RingHom.injective _)`. Use `⟨GlobalTheory.DetSpread.detCond_of_dense E H D' (Sp R) C.P.D.toPre.P.A C.P.D.toPre.P.g (GlobalTheory.LocM.abPartAct C.P) (KA (lowLevel l)) (lowS C) (baseKA (lowLevel l)).ρ C.P.D.toPre.P.smoothDim (baseKA (lowLevel l)).ρ_sq ((dense_jFR R F0).mono ?_) k x β hx, ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨p, rfl⟩`.

Conclude with `⟨F0, inferInstance, inferInstance, inferInstance, jFK (R := R) F0 ≫ jK R, lowF C F0, ⟨p, rfl⟩, jFR_lowS C F0, hdet0⟩`. Take `⟨I, hIζ, hIev⟩` from `GlobalTheory.T.tateIso_spread_generic_noetherian_domain D' R C.P.D.toPre.P (fun a => C.P.oD.onB.act a) (KA (lowLevel l)) (lowS C) (baseKA (lowLevel l)).ζ l.M' hM hg sA F0 (jFK (R := R) F0 ≫ jK R) (lowF C F0) (dense_jFR R F0) (jFR_lowS C F0) J0 hζ0 hsA k x β hx`. Use `⟨I, hIζ, hIev, fun w hw => ?_⟩` and prove the remaining obligations. Conclude with `(hIev _).trans (ev_eta l I hfm hfe hk hw) }`. Use `⟨o', 𝟙 _, GlobalTheory.SiegLower.isGrpPullback_id _, fun x => (Category.comp_id _).trans (Category.id_comp _).symm, GlobalTheory.SiegLower.lbIso_pull_id C.P.D.toPre.P.isLB, ?_⟩` and prove the remaining obligations.

Introduce `F _ _ _ I hX hG`. Take `⟨J, hJζ, hJb⟩` from `GlobalTheory.T.exists_gradedTateIso_lowerDatum Dw D' Z f hlow R hR C.t C.P F hg I (hy F I hG)`. Establish `key : ∀ w, toUnit _ ≫ sA w = J.ev l.M' w`. Introduce `w`. Take `⟨a, rfl⟩` from `hlow.1 w`.

Take `⟨σ⟩ : Nonempty (F0 →ₐ[FractionRing R] F)` from `⟨IsAlgClosed.lift⟩`. Take `⟨q, hq1, hq2⟩` from `hy F I hG l.M' hM a`. Take `⟨q0, h01, h02⟩` from `hy F0 I0 hG0 l.M' hM a`. Establish `e1` using `b_eq_of_level hR C tK m1 m2 σ I0 I hX0 hX a q0 q h01 hq1 h02 hq2`. Rewrite `e1` using `[hJb l.M' hM a q hq1 hq2, hJ0b l.M' hM a q0 h01 h02]`.

Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Rewrite using `[Over.comp_left, e1, ← hsA (f a), Over.comp_left, ← Category.assoc, toUnit_left, toUnit_left]`. Establish `e : spMap σ.toRingHom ≫ jFK (R` using `R) F0 = jFK (R := R) F := by`. Rewrite using `[← Spec.map_comp]`. Conclude with `congrArg (fun g => Spec.map (CommRingCat.ofHom g)) (RingHom.ext fun r => σ.commutes r)`.

Use `show (jFK (R := R) F ≫ jK R) ≫ _ = (spMap σ.toRingHom ≫ jFK (R := R) F0 ≫ jK R) ≫ _`. Rewrite using `[← Category.assoc (spMap _), e]`. Use `⟨J, fun n => hJζ n, key, fun w hw => ?_, fun n hn a => ?_⟩` and prove the remaining obligations. Use `show toUnit _ ≫ sA (m • (em • w)) = _`. Rewrite using `[key]`.

Conclude with `ev_eta l J hfm hfe hk hw`. Take `⟨q, hq1, hq2⟩` from `hy F I hG n hn a`. Conclude with `⟨q, hq1, hq2, by rw [hJb n hn a q hq1 hq2]; exact (Category.comp_id _).symm⟩`.
-/
theorem exists_lowObj : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l)
  (c : Coeff l) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (C : GlobalTheory.UChart.Fam Xo c R)
  (Z : Submodule (𝓞 E) Dw.La) (D' : Datum H) (f : GlobalTheory.LowDat.perp Dw Z →ₗ[𝓞 E] D'.La),
  GlobalTheory.LowDat.IsIsoSat Dw Z → GlobalTheory.LowDat.IsLower Dw D' Z f →
  Module.finrank (𝓞 E) Z = Module.finrank (𝓞 E) C.P.D.toPre.X →
  D'.p = Dw.p - Module.finrank (𝓞 E) Z → D'.q = Dw.q - Module.finrank (𝓞 E) Z →
  ∀ (tK : SAB H (Sp (FractionRing R))) (m1 : SABMap tK C.t (jK R)) (m2 : SABMap tK Xo.univ.t (C.y ≫ pullback.fst _ _)),
  (∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F],
    ∃ I : (letI := H.starRing; TateIsoQ Dw C.P.D.toPre C.P.oD F),
      GlobalTheory.LowDat.XFLevel C tK m1 m2 F I ∧ GlobalTheory.LowDat.FiltGraded C Z F I) →
  ∃ (o' : Obj D' (GlobalTheory.LowDat.lowLevel l) (baseKA (GlobalTheory.LowDat.lowLevel l)) (GlobalTheory.LowDat.lowS C))
    (φB : o'.t.G.left ⟶ C.P.D.toPre.P.A.left),
    IsGrpPullback o'.t.G C.P.D.toPre.P.A (𝟙 _) φB ∧
    (letI := H.starRing; ∀ x : 𝓞 E, (o'.t.act.act x).left ≫ φB = φB ≫ (C.P.oD.onB.act x).left) ∧
    (∃ w : LB.Iso o'.t.PP.L (C.P.D.toPre.P.L.pull φB), w.IsGen) ∧
    ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F]
      (I : (letI := H.starRing; TateIsoQ Dw C.P.D.toPre C.P.oD F)),
      GlobalTheory.LowDat.XFLevel C tK m1 m2 F I → GlobalTheory.LowDat.FiltGraded C Z F I →
      ∃ I' : GlobalTheory.LowDat.LowTate C D' o' F, GlobalTheory.LowDat.LowGraded C Z D' f o' φB F I I' := by
  intro E _ _ _ H Dw l Xo c R _ _ _ hR C Z D' f hZ hlow hrk hp hq tK m1 m2 hI
  letI := H.starRing
  haveI := hR.1.1
  haveI := hR.2
  haveI : IsIntegrallyClosed R := hR.1.2.2.1
  haveI : CharZero (FractionRing R) := charZero_of_injective_algebraMap (IsFractionRing.injective R _)
  let F0 := AlgebraicClosure (FractionRing R)
  haveI : CharZero F0 := charZero_of_injective_algebraMap (algebraMap (FractionRing R) F0).injective
  obtain ⟨I0, hX0, hG0⟩ := hI F0
  rw [hrk] at hp hq
  have hdet0 := detCond_generic hR C D' hp hq tK m1 m2 F0
  have hρ0 : lowF C F0 (baseKA (lowLevel l)).ρ ^ 2 = -(H.d : F0) := by
    rw [← map_pow, (baseKA _).ρ_sq, map_neg, map_natCast]
  have hg := finrank_eq_of_detCond D' C.P.D.toPre.P (GlobalTheory.LocM.abPartAct C.P) _ _ hρ0 hdet0
  have hy : ∀ (F : Type) [Field F] [Algebra (FractionRing R) F]
      (I : TateIsoQ Dw C.P.D.toPre C.P.oD F), FiltGraded C Z F I → ∀ n, 0 < n → ∀ a : perp Dw Z,
      ∃ q : QkPt C.P.D.toPre F n, QkPt.Equiv _ F (I.ev n a) q ∧ q.y = 0 :=
    fun F _ _ I h n hn a => (h n hn a).2 ⟨a, a.2, 0, by simp⟩
  obtain ⟨J0, hJ0ζ, hJ0b⟩ := GlobalTheory.T.exists_gradedTateIso_lowerDatum Dw D' Z f hlow R hR C.t C.P F0 hg I0 (hy F0 I0 hG0)
  have hM : 0 < l.M' := (lowLevel l).A_pos
  have hunit : IsUnit (l.M' : R) := by
    simpa using (isUnit_iff_ne_zero.2 (Nat.cast_ne_zero.2 hM.ne') : IsUnit ((l.M' : ℕ) : c.F)).map C.b
  haveI := C.P.D.toPre.P.isAb.proper
  have hfix : ∀ (a : perp Dw Z) (σ : F0 ≃ₐ[FractionRing R] F0),
      spMap (σ : F0 →+* F0) ≫ (J0.ev l.M' (f a)).left = (J0.ev l.M' (f a)).left := by
    intro a σ
    obtain ⟨q, hq1, hq2⟩ := hy F0 I0 hG0 l.M' hM a
    rw [← hJ0b l.M' hM a q hq1 hq2]
    exact (b_eq_of_level hR C tK m1 m2 σ.toAlgHom I0 I0 hX0 hX0 a q q hq1 hq1 hq2 hq2).symm
  have hsec : ∀ w : D'.La, ∃ s : 𝟙_ (Over (Sp R)) ⟶ C.P.D.toPre.P.A, toUnit _ ≫ s = J0.ev l.M' w := by
    intro w
    obtain ⟨a, rfl⟩ := hlow.1 w
    exact exists_section C.P.D.toPre.P.A l.M' hunit _ ((J0.onto _ hM _).2 ⟨_, rfl⟩) (hfix a)
  choose sA hsA using hsec
  obtain ⟨fm, hfm, em, hem, hfe⟩ : ∃ x ∈ l.Mb, ∃ y ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E), x + y = 1 :=
    Submodule.mem_sup.1 (by rw [l.coprime]; trivial)
  obtain ⟨m, hk⟩ : l.M ∣ l.M' := Nat.dvd_lcm_left _ _
  have hζ0 : (J0.ζ l.M' : F0) = lowF C F0 (baseKA (lowLevel l)).ζ := by
    rw [hJ0ζ, hX0.1]
    exact congrArg (toF C F0) (Subtype.ext (by
      simp only [IntermediateField.coe_inclusion, zeta_val]; rfl))
  let o' : Obj D' (lowLevel l) (baseKA (lowLevel l)) (lowS C) :=
    { t := abTriple C.P
      proper := C.P.D.toPre.P.isAb.proper
      ample := C.P.D.toPre.P.ample
      ktriv := C.P.D.toPre.P.ktriv
      eta := fun w => sA (m • (em • w))
      eta_add := fun a b => section_ext (F := F0) (by
        erw [MonObj.comp_mul, hsA, hsA, hsA, smul_add, smul_add]; exact J0.add _ _ _)
      eta_ker := fun a ha => section_ext (F := F0) (by
        obtain ⟨c', hc'⟩ := GlobalTheory.CM.RationalTorsion.exists_eq_nsmul D' l (by rw [mul_comm]; exact l.prod) hem ha
        erw [MonObj.comp_one, hsA]
        exact (J0.ker _ hM _).2 ⟨c', by rw [hc', smul_smul, hk, mul_comm]⟩)
      etaA := sA
      etaA_add := fun a b => section_ext (F := F0) (by erw [MonObj.comp_mul, hsA, hsA, hsA]; exact J0.add _ _ _)
      etaA_ker := fun a => section_ext (F := F0) (by
        erw [MonObj.comp_one, hsA]
        exact (J0.ker _ hM _).2 ⟨a, rfl⟩)
      geom := by
        intro k _ _ x β hx
        haveI : CharZero k := charZero_of_injective_ringHom (f := β.comp (algebraMap ℚ (KA (lowLevel l))))
          (RingHom.injective _)
        refine ⟨GlobalTheory.DetSpread.detCond_of_dense E H D' (Sp R) C.P.D.toPre.P.A C.P.D.toPre.P.g
          (GlobalTheory.LocM.abPartAct C.P) (KA (lowLevel l)) (lowS C) (baseKA (lowLevel l)).ρ C.P.D.toPre.P.smoothDim
          (baseKA (lowLevel l)).ρ_sq ((dense_jFR R F0).mono ?_) k x β hx, ?_⟩
        · rintro _ ⟨p, rfl⟩
          exact ⟨F0, inferInstance, inferInstance, inferInstance, jFK (R := R) F0 ≫ jK R, lowF C F0, ⟨p, rfl⟩,
            jFR_lowS C F0, hdet0⟩
        obtain ⟨I, hIζ, hIev⟩ := GlobalTheory.T.tateIso_spread_generic_noetherian_domain D' R C.P.D.toPre.P (fun a => C.P.oD.onB.act a) (KA (lowLevel l)) (lowS C)
          (baseKA (lowLevel l)).ζ l.M' hM hg sA F0 (jFK (R := R) F0 ≫ jK R) (lowF C F0) (dense_jFR R F0)
          (jFR_lowS C F0) J0 hζ0 hsA k x β hx
        refine ⟨I, hIζ, hIev, fun w hw => ?_⟩
        exact (hIev _).trans (ev_eta l I hfm hfe hk hw) }
  refine ⟨o', 𝟙 _, GlobalTheory.SiegLower.isGrpPullback_id _, fun x => (Category.comp_id _).trans (Category.id_comp _).symm,
    GlobalTheory.SiegLower.lbIso_pull_id C.P.D.toPre.P.isLB, ?_⟩
  intro F _ _ _ I hX hG
  obtain ⟨J, hJζ, hJb⟩ := GlobalTheory.T.exists_gradedTateIso_lowerDatum Dw D' Z f hlow R hR C.t C.P F hg I (hy F I hG)
  have key : ∀ w, toUnit _ ≫ sA w = J.ev l.M' w := by
    intro w
    obtain ⟨a, rfl⟩ := hlow.1 w
    obtain ⟨σ⟩ : Nonempty (F0 →ₐ[FractionRing R] F) := ⟨IsAlgClosed.lift⟩
    obtain ⟨q, hq1, hq2⟩ := hy F I hG l.M' hM a
    obtain ⟨q0, h01, h02⟩ := hy F0 I0 hG0 l.M' hM a
    have e1 := b_eq_of_level hR C tK m1 m2 σ I0 I hX0 hX a q0 q h01 hq1 h02 hq2
    rw [hJb l.M' hM a q hq1 hq2, hJ0b l.M' hM a q0 h01 h02] at e1
    apply Over.OverMorphism.ext
    rw [Over.comp_left, e1, ← hsA (f a), Over.comp_left, ← Category.assoc, toUnit_left, toUnit_left]
    have e : spMap σ.toRingHom ≫ jFK (R := R) F0 = jFK (R := R) F := by
      rw [← Spec.map_comp]
      exact congrArg (fun g => Spec.map (CommRingCat.ofHom g)) (RingHom.ext fun r => σ.commutes r)
    show (jFK (R := R) F ≫ jK R) ≫ _ = (spMap σ.toRingHom ≫ jFK (R := R) F0 ≫ jK R) ≫ _
    rw [← Category.assoc (spMap _), e]
  refine ⟨J, fun n => hJζ n, key, fun w hw => ?_, fun n hn a => ?_⟩
  · show toUnit _ ≫ sA (m • (em • w)) = _
    rw [key]
    exact ev_eta l J hfm hfe hk hw
  · obtain ⟨q, hq1, hq2⟩ := hy F I hG n hn a
    exact ⟨q, hq1, hq2, by rw [hJb n hn a q hq1 hq2]; exact (Category.comp_id _).symm⟩

end Main

end GlobalTheory.LowDat.LowObj
