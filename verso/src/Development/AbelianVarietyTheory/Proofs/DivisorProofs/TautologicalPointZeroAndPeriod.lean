import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExtId
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoEqOneAlongAxesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RefinesPolarisedDataBaseChangeSymmetric
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueThickTorusLevelWeightExpansion
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AdicBaseIffDomainAdicNormalPair
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.GtPtsVal
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

noncomputable section

namespace GlobalTheory.TInj

/- English proof (translation)
Use `congrArg (fun q => q.hom a) (Scheme.ΓSpecIso_inv_naturality f)` as an intermediate fact. Simplify using `only [CommRingCat.hom_comp, RingHom.comp_apply] at this`. Conclude with `this.symm`.
-/
theorem appTop_spec_inv {R S : CommRingCat} (f : R ⟶ S) (a : R) :
    (Spec.map f).appTop.hom ((Scheme.ΓSpecIso R).inv.hom a) = (Scheme.ΓSpecIso S).inv.hom (f.hom a) := by
  have := congrArg (fun q => q.hom a) (Scheme.ΓSpecIso_inv_naturality f)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
  exact this.symm

/- English proof (translation)
Establish `h` using `T.τ₀_add 0 0 a z J hJ`. Establish `f : cubV T.cub z J (T.c₀ 0) (T.c₀ 0) (T.c₀ a) = 1`. Rewrite using `[T.c₀_zero]`. Conclude with `(isCub_cubV T.cub hJ).face _ _`. Rewrite `h` using `[add_zero, f, _root_.mul_one]`.

Conclude with `(T.τ₀_symm a 0 z J hJ).trans (mul_eq_left.1 h.symm)`.
-/
theorem tautologicalChart_baseGenerator_zero_right {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) (a : Fin T.r → ℤ)
    (z J) (hJ : Good T.M.L z J) : val (T.τ₀ a 0) (𝟙 _) z J = 1 := by
  have h := T.τ₀_add 0 0 a z J hJ
  have f : cubV T.cub z J (T.c₀ 0) (T.c₀ 0) (T.c₀ a) = 1 := by
    rw [T.c₀_zero]; exact (isCub_cubV T.cub hJ).face _ _
  rw [add_zero, f, _root_.mul_one] at h
  exact (T.τ₀_symm a 0 z J hJ).trans (mul_eq_left.1 h.symm)

/- English proof (translation)
Establish `ht : (toUnit (TF (R` using `V) F)).left = (TF (R := V) F).hom := by`. Simplify using `using Over.w (toUnit (TF (R := V) F))`. Use `ext1`. Apply `hpb.1.hom_ext` to reduce the goal to its premises. Rewrite using `[hg, DVR.cP, Over.comp_left, Category.assoc, hc, ← Category.assoc, ht, Category.assoc]`.

Rewrite using `[Over.w g.b, Over.w (DVR.cP D (TF (R := V) F) x)]`.
-/
theorem base_eq {o W V : Type} [CommRing o] [CommRing W] [IsLocalRing W] [CommRing V] [IsDomain V] {T : TautBase o W}
    {ω : W →+* V} {D : DegPre V} {β : D.P.A.left ⟶ T.B.left} (hpb : IsGrpPullback D.P.A T.B (spMap ω) β)
    {F : Type} [Field F] [Algebra (FractionRing V) F] {x : D.X} {a : Fin T.r → ℤ}
    (hc : (D.c x).left ≫ β = spMap ω ≫ (T.c₀ a).left) (g : GtPtF D F)
    (hg : g.b.left ≫ β = (TF (R := V) F).hom ≫ spMap ω ≫ (T.c₀ a).left) : g.b = DVR.cP D (TF (R := V) F) x := by
  have ht : (toUnit (TF (R := V) F)).left = (TF (R := V) F).hom := by
    simpa using Over.w (toUnit (TF (R := V) F))
  ext1
  apply hpb.1.hom_ext
  · rw [hg, DVR.cP, Over.comp_left, Category.assoc, hc, ← Category.assoc, ht, Category.assoc]
  · rw [Over.w g.b, Over.w (DVR.cP D (TF (R := V) F) x)]

end GlobalTheory.TInj

/- English proof (translation)
Introduce `o W _ _ _ T I _ ε n V _ _ D ω s e β ββ w hB hF F _ _ g`. Establish `hF'` using `hF`. Take `⟨hpb, -, -, hc, hτ⟩` from `hF`. Use `⟨fun h => ?_, fun y h => ?_⟩` and prove the remaining obligations. Take `⟨hb, hv⟩` from `h`.

Establish `hb' : g.b = 1`. Use `GlobalTheory.TInj.base_eq hpb (x := 0) (a := 0) (by rw [hc 0, map_zero, smul_zero]) g hb` as an intermediate fact. Rewrite `this` using `[cPoint_zero]`. Then use the resulting hypothesis. Use `(isZero_iff g).2 ⟨hb', fun χ z J' hJ' => ?_⟩` and prove the remaining obligations. Use `choose I₀ hI using fun ψ : (TF (R := V) F).left ⟶ T.B.left => exists_chart T.M.isLB (ψ z)`.

Establish `hJ : Good T.M.L z I₀` using `hI`. Take `⟨k, hk, hval⟩` from `hv χ`. Rewrite using `[hval z I₀ J' hJ hJ']`. Establish `k1 : k = 1` using `Units.ext (by rw [hk]; simp)`. Establish `l1` using `(GlobalTheory.T.mumford_bundle_iso_eq_one_along_axes T ε n V D ω s e β ββ w hB hF' (TF (R := V) F) (DegPre.cF D F χ) z I₀ J' hJ hJ').2`.

Establish `t1 : val (T.τ₀ ((n : ℤ) • e χ) 0) ((TF (R` using `V) F).hom ≫ spMap ω) z I₀ = 1 := by`. Apply `Units.ext` to reduce the goal to its premises. Establish `v` using `GlobalTheory.LevelExpansion.val_comp (T.τ₀ ((n : ℤ) • e χ) 0) ((TF (R := V) F).hom ≫ spMap ω) (𝟙 _) hJ`. Rewrite `v` using `[Category.comp_id]`. Establish `t0` using `GlobalTheory.TInj.tautologicalChart_baseGenerator_zero_right T ((n : ℤ) • e χ) _ _ (GlobalTheory.LevelExpansion.good_comp ((TF (R := V) F).hom ≫ spMap ω) hJ)`.

Rewrite using `[v]`. Use `erw [t0]`. Rewrite using `[Units.val_one, map_one, Units.val_one]`. Rewrite using `[hb', l1, t1, k1]`. Simplify using `[unitOn]`.

Take `⟨hb, hv⟩` from `h`. Establish `hb' : g.b = DVR.cP D (TF (R` using `V) F) y := GlobalTheory.TInj.base_eq hpb (hc y) g hb`. Use `(isIota_iff y g).2 ⟨hb', fun χ z J' hJ' => ?_⟩` and prove the remaining obligations. Use `choose I₀ hI using fun ψ : (TF (R := V) F).left ⟶ T.B.left => exists_chart T.M.isLB (ψ z)`. Establish `hJ : Good T.M.L z I₀` using `hI`.

Take `⟨k, hk, hval⟩` from `hv χ`. Take `⟨k₀, hk₀, hval₀⟩` from `hτ χ y`. Establish `e₀` using `hval₀ (jFK (R := V) F z) (fun ψ => I₀ (jFK (R := V) F ≫ ψ)) (fun ψ => J' (jFK (R := V) F ≫ ψ)) (GlobalTheory.LevelExpansion.good_comp _ hJ) (GlobalTheory.LevelExpansion.good_comp _ hJ')`. Rewrite using `[hval z I₀ J' hJ hJ', Category.id_comp, GlobalTheory.DegCompare.val_tau_symm _ hJ' y χ]`. Establish `v` using `GlobalTheory.LevelExpansion.val_comp (D.tau χ y) (jFK (R := V) F) (𝟙 _) hJ'`.

Rewrite `v` using `[Category.comp_id]`. Establish `hl : (lift (DegPre.cF D F χ) g.b).left = jFK (R` using `V) F ≫ (lift (toUnit (TK V) ≫ D.c χ) (toUnit (TK V) ≫ D.c y)).left := by`. Rewrite using `[hb']`. Establish `: lift (DegPre.cF D F χ) (DVR.cP D (TF (R` using `V) F) y) = (Over.homMk (jFK (R := V) F) rfl : TF (R := V) F ⟶ TK V) ≫ lift (toUnit (TK V) ≫ D.c χ) (toUnit (TK V) ≫ D.c y) := by`. Rewrite using `[comp_lift, ← Category.assoc, ← Category.assoc, toUnit_unique (_ ≫ toUnit _) (toUnit _)]`.

Both sides reduce to the same expression. Rewrite using `[this, Over.comp_left]`. Both sides reduce to the same expression. Establish `hL` using `GlobalTheory.HalfBC.lamVal_comp w (jFK (R := V) F) (lift (toUnit (TK V) ≫ D.c χ) (toUnit (TK V) ≫ D.c y)).left z I₀ J' hJ hJ'`. Establish `vt : (val (T.τ₀ ((n : ℤ) • e χ) ((n : ℤ) • e y)) ((TF (R` using `V) F).hom ≫ spMap ω) z I₀).val = (Scheme.Hom.stalkMap (jFK (R := V) F) z).hom (val (T.τ₀ ((n : ℤ) • e χ) ((n : ℤ) • e y)) ((TK V).hom ≫ spMap ω) (jFK (R := V) F z) (fun ψ => I₀ (jFK (R := V) F ≫ ψ))).val := by`.

Use `GlobalTheory.LevelExpansion.val_comp (T.τ₀ ((n : ℤ) • e χ) ((n : ℤ) • e y)) (jFK (R := V) F) ((TK V).hom ≫ spMap ω) hJ` as an intermediate fact. Rewrite `this` using `[← Category.assoc]`. Conclude with `this`. Establish `hkk : (algebraMap (FractionRing V) F) (k₀ : FractionRing V) = (k : F)`. Rewrite using `[hk, hk₀, map_prod]`.

Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_zpow₀, map_zsmul, smul_eq_mul]`. Establish `hg : gm (𝟙 (TF (R` using `V) F).left) z ⊤ (unitOn k) = Units.map (Scheme.Hom.stalkMap (jFK (R := V) F) z).hom.toMonoidHom (gm (𝟙 (TK V).left) (jFK (R := V) F z) ⊤ (unitOn k₀)) := by`. Rewrite using `[← GlobalTheory.ConstFam.gm_comp_stalkMap _ _ z ⊤ trivial, Category.comp_id]`. Use `gm_comp_top (𝟙 (TF (R := V) F).left) (jFK (R := V) F) z (unitOn k₀) (unitOn k) (by` as an intermediate fact.

Simplify using `only [unitOn, Units.coe_map, MonoidHom.coe_coe]`. Conclude with `(GlobalTheory.TInj.appTop_spec_inv (CommRingCat.ofHom (algebraMap (FractionRing V) F)) (k₀ : FractionRing V)).trans (congrArg _ hkk))`. Rewrite `this` using `[Category.id_comp]`. Conclude with `this.symm`. Apply `Units.ext` to reduce the goal to its premises.

Rewrite using `[v, e₀]`. Simplify using `only [Units.val_mul, map_mul]`. Rewrite using `[hg, hl, hL, vt]`. Both sides reduce to the same expression.
-/
theorem GlobalTheory.TInj.tautPt_zero_iota : ∀ {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) {I : Type} [Fintype I] (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (n : ℕ) (V : Type) [CommRing V] [IsDomain V] (D : DegPre V) (ω : W →+* V) (s : I → V) (e : D.X ≃+ (Fin T.r → ℤ)) (β : D.P.A.left ⟶ T.B.left) (ββ : (G2 D.P.A).left ⟶ (G2 T.B).left) (w : LB.Iso (abelian₂ D.P.A D.P.L) ((abelian₂ T.B T.M.L).pull ββ)), D.TauBimult → From T ω s ε n D e β ββ w → ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (g : GtPtF D F), (TautPt T ω s ε n D e β ββ w F 0 g → g.IsZero) ∧ ∀ y : D.X, TautPt T ω s ε n D e β ββ w F ((n : ℤ) • e y) g → GtPtF.IsIota y g := by
  intro o W _ _ _ T I _ ε n V _ _ D ω s e β ββ w hB hF F _ _ g
  have hF' := hF
  obtain ⟨hpb, -, -, hc, hτ⟩ := hF
  refine ⟨fun h => ?_, fun y h => ?_⟩
  · obtain ⟨hb, hv⟩ := h
    have hb' : g.b = 1 := by
      have := GlobalTheory.TInj.base_eq hpb (x := 0) (a := 0) (by rw [hc 0, map_zero, smul_zero]) g hb
      rwa [cPoint_zero] at this
    refine (isZero_iff g).2 ⟨hb', fun χ z J' hJ' => ?_⟩
    choose I₀ hI using fun ψ : (TF (R := V) F).left ⟶ T.B.left => exists_chart T.M.isLB (ψ z)
    have hJ : Good T.M.L z I₀ := hI
    obtain ⟨k, hk, hval⟩ := hv χ
    rw [hval z I₀ J' hJ hJ']
    have k1 : k = 1 := Units.ext (by rw [hk]; simp)
    have l1 := (GlobalTheory.T.mumford_bundle_iso_eq_one_along_axes T ε n V D ω s e β ββ w hB hF' (TF (R := V) F) (DegPre.cF D F χ) z I₀ J' hJ hJ').2
    have t1 : val (T.τ₀ ((n : ℤ) • e χ) 0) ((TF (R := V) F).hom ≫ spMap ω) z I₀ = 1 := by
      apply Units.ext
      have v := GlobalTheory.LevelExpansion.val_comp (T.τ₀ ((n : ℤ) • e χ) 0) ((TF (R := V) F).hom ≫ spMap ω) (𝟙 _) hJ
      rw [Category.comp_id] at v
      have t0 := GlobalTheory.TInj.tautologicalChart_baseGenerator_zero_right T ((n : ℤ) • e χ) _ _ (GlobalTheory.LevelExpansion.good_comp ((TF (R := V) F).hom ≫ spMap ω) hJ)
      rw [v]
      erw [t0]
      rw [Units.val_one, map_one, Units.val_one]
    rw [hb', l1, t1, k1]
    simp [unitOn]
  · obtain ⟨hb, hv⟩ := h
    have hb' : g.b = DVR.cP D (TF (R := V) F) y := GlobalTheory.TInj.base_eq hpb (hc y) g hb
    refine (isIota_iff y g).2 ⟨hb', fun χ z J' hJ' => ?_⟩
    choose I₀ hI using fun ψ : (TF (R := V) F).left ⟶ T.B.left => exists_chart T.M.isLB (ψ z)
    have hJ : Good T.M.L z I₀ := hI
    obtain ⟨k, hk, hval⟩ := hv χ
    obtain ⟨k₀, hk₀, hval₀⟩ := hτ χ y
    have e₀ := hval₀ (jFK (R := V) F z) (fun ψ => I₀ (jFK (R := V) F ≫ ψ)) (fun ψ => J' (jFK (R := V) F ≫ ψ))
      (GlobalTheory.LevelExpansion.good_comp _ hJ) (GlobalTheory.LevelExpansion.good_comp _ hJ')
    rw [hval z I₀ J' hJ hJ', Category.id_comp, GlobalTheory.DegCompare.val_tau_symm _ hJ' y χ]
    have v := GlobalTheory.LevelExpansion.val_comp (D.tau χ y) (jFK (R := V) F) (𝟙 _) hJ'
    rw [Category.comp_id] at v
    have hl : (lift (DegPre.cF D F χ) g.b).left =
        jFK (R := V) F ≫ (lift (toUnit (TK V) ≫ D.c χ) (toUnit (TK V) ≫ D.c y)).left := by
      rw [hb']
      have : lift (DegPre.cF D F χ) (DVR.cP D (TF (R := V) F) y) =
          (Over.homMk (jFK (R := V) F) rfl : TF (R := V) F ⟶ TK V) ≫
            lift (toUnit (TK V) ≫ D.c χ) (toUnit (TK V) ≫ D.c y) := by
        rw [comp_lift, ← Category.assoc, ← Category.assoc, toUnit_unique (_ ≫ toUnit _) (toUnit _)]; rfl
      rw [this, Over.comp_left]; rfl
    have hL := GlobalTheory.HalfBC.lamVal_comp w (jFK (R := V) F)
      (lift (toUnit (TK V) ≫ D.c χ) (toUnit (TK V) ≫ D.c y)).left z I₀ J' hJ hJ'
    have vt : (val (T.τ₀ ((n : ℤ) • e χ) ((n : ℤ) • e y)) ((TF (R := V) F).hom ≫ spMap ω) z I₀).val =
        (Scheme.Hom.stalkMap (jFK (R := V) F) z).hom (val (T.τ₀ ((n : ℤ) • e χ) ((n : ℤ) • e y))
          ((TK V).hom ≫ spMap ω) (jFK (R := V) F z) (fun ψ => I₀ (jFK (R := V) F ≫ ψ))).val := by
      have := GlobalTheory.LevelExpansion.val_comp (T.τ₀ ((n : ℤ) • e χ) ((n : ℤ) • e y)) (jFK (R := V) F) ((TK V).hom ≫ spMap ω) hJ
      rw [← Category.assoc] at this
      exact this
    have hkk : (algebraMap (FractionRing V) F) (k₀ : FractionRing V) = (k : F) := by
      rw [hk, hk₀, map_prod]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [map_zpow₀, map_zsmul, smul_eq_mul]
    have hg : gm (𝟙 (TF (R := V) F).left) z ⊤ (unitOn k) =
        Units.map (Scheme.Hom.stalkMap (jFK (R := V) F) z).hom.toMonoidHom
          (gm (𝟙 (TK V).left) (jFK (R := V) F z) ⊤ (unitOn k₀)) := by
      rw [← GlobalTheory.ConstFam.gm_comp_stalkMap _ _ z ⊤ trivial, Category.comp_id]
      have := gm_comp_top (𝟙 (TF (R := V) F).left) (jFK (R := V) F) z (unitOn k₀) (unitOn k) (by
        simp only [unitOn, Units.coe_map, MonoidHom.coe_coe]
        exact (GlobalTheory.TInj.appTop_spec_inv (CommRingCat.ofHom (algebraMap (FractionRing V) F)) (k₀ : FractionRing V)).trans
          (congrArg _ hkk))
      rw [Category.id_comp] at this
      exact this.symm
    apply Units.ext
    rw [v, e₀]
    simp only [Units.val_mul, map_mul]
    rw [hg, hl, hL, vt]
    rfl
