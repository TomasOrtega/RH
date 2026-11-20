import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeatOperatorShiftDivMonomial
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdNeg
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocalC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullUUnitsCompatGeneric
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section
namespace GlobalTheory.ShiftGen

open ReciprocityTheory.ChartRestriction.G.DVR

variable {R : Type} [CommRing R] [IsDomain R]

/- English proof (translation)
Establish `hL` using `D.P.isLB`. Take `⟨e, he⟩` from `exists_gen_of_local (V := R) D.P.L hL (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1)`. Take `⟨j, hj, le', hψ⟩` from `h`. Establish `le : (⊤ : (Spec (CommRingCat.of R)).Opens) ≤ LB.wchart D.P.L (K` using `PUnit) (fun _ => (D.c χ).left) j := fun y hy => Set.mem_iInter.2 fun _ => hj hy`. Establish `hx : D.xK χ = jK R ≫ (D.c χ).left`.

Simplify using `[DegPre.xK, ptK]`. Establish `hto : ∀ a, DegPre.toOpen (R` using `R) ⊤ a = (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a := fun a => by`. Simplify using `[DegPre.toOpen]`. Set `cu : Γ(Spec (CommRingCat.of R), ⊤)ˣ` to `Units.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom.toMonoidHom u`. Set `c : Γ(Spec (CommRingCat.of R), ⊤)ˣ` to `cu * (res le (e.s j))⁻¹`.

Use `⟨DVR.scaleGen c e, DVR.scaleGen_isGen c e he, fun Z r z J hJ => ?_⟩` and prove the remaining obligations. Establish `m₁ : r z ∈ LB.wchart D.P.L (K` using `PUnit) (fun _ => D.xK χ) j := le' trivial`. Establish `m₂ : (r ≫ jK R) z ∈ LB.wchart D.P.L (K` using `PUnit) (fun _ => (D.c χ).left) j := le trivial`. Establish `e₁ : val (D.psi χ) r z J = _` using `gen_trans (D.psi_gen χ) r z (hJ.mem _ r) m₁`. Establish `e₂ : val (DVR.scaleGen c e) (r ≫ jK R) z J = _` using `gen_trans (DVR.scaleGen_isGen c e he) (r ≫ jK R) z (hJ.mem _ _) m₂`.

Establish `e₃ : trF (L` using `D.P.L) (K := PUnit) (fun _ => D.xK χ) (fun _ => -1) r z (fun _ => J (r ≫ D.xK χ)) j = trF (L := D.P.L) (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1) (r ≫ jK R) z (fun _ => J ((r ≫ jK R) ≫ (D.c χ).left)) j := by`. Establish `hq : r ≫ D.xK χ = (r ≫ jK R) ≫ (D.c χ).left` using `(congrArg (r ≫ ·) hx).trans (Category.assoc _ _ _).symm`. Simplify using `only [trF]`. Rewrite using `[hq]`. Establish `e₄ : (gm r z (LB.wchart D.P.L (K` using `PUnit) (fun _ => D.xK χ) j) ((D.psi χ).s j)).val = gs (r ≫ jK R) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (u * a)) := by`.

Use `(gs_unit r z _ m₁ _).symm.trans ((gs_res r z le' trivial _).symm.trans ?_)` and prove the remaining obligations. Use `(congrArg (gs r z _) hψ.symm).trans ((gs_pull r (jK R) z ⊤ trivial _).trans ?_)` and prove the remaining obligations. Rewrite using `[hto]`. Establish `e₅ : gm (r ≫ jK R) z (LB.wchart D.P.L (K` using `PUnit) (fun _ => (D.c χ).left) j) ((DVR.scaleGen c e).s j) = gm (r ≫ jK R) z ⊤ cu := by`. Use `(map_mul _ _ _).trans ((congrArg₂ (· * ·) (gm_res (r ≫ jK R) z le_top m₂ c) (gm_res (r ≫ jK R) z le trivial (e.s j)).symm).trans ?_)` and prove the remaining obligations.

Rewrite using `[← map_mul]`. Conclude with `congrArg _ (inv_mul_cancel_right _ _)`. Establish `e₆ : (gm (r ≫ jK R) z ⊤ cu).val = gs (r ≫ jK R) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom u)` using `(gs_unit _ z ⊤ trivial cu).symm`. Rewrite using `[e₁, e₂, Units.val_mul, Units.val_mul]`. Use `erw [e₃, e₄, e₅]`.

Rewrite using `[e₆, map_mul, gs_mul _ z ⊤ trivial]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_psi_gen [IsLocalRing R] (D : DegPre R) (χ : D.X) (u : Rˣ) (a : R) (h : PsiCoord D χ (u * a)) :
    ∃ (e : LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1))), e.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (TK R).left) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J →
        (val (D.psi χ) r z J).val = gs (r ≫ jK R) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a) *
          (val e (r ≫ jK R) z J).val := by
  have hL := D.P.isLB
  obtain ⟨e, he⟩ := exists_gen_of_local (V := R) D.P.L hL (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1)
  obtain ⟨j, hj, le', hψ⟩ := h
  have le : (⊤ : (Spec (CommRingCat.of R)).Opens) ≤ LB.wchart D.P.L (K := PUnit) (fun _ => (D.c χ).left) j :=
    fun y hy => Set.mem_iInter.2 fun _ => hj hy
  have hx : D.xK χ = jK R ≫ (D.c χ).left := by
    simp [DegPre.xK, ptK]
  have hto : ∀ a, DegPre.toOpen (R := R) ⊤ a = (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a := fun a => by
    simp [DegPre.toOpen]
  let cu : Γ(Spec (CommRingCat.of R), ⊤)ˣ := Units.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom.toMonoidHom u
  let c : Γ(Spec (CommRingCat.of R), ⊤)ˣ := cu * (res le (e.s j))⁻¹
  refine ⟨DVR.scaleGen c e, DVR.scaleGen_isGen c e he, fun Z r z J hJ => ?_⟩
  have m₁ : r z ∈ LB.wchart D.P.L (K := PUnit) (fun _ => D.xK χ) j := le' trivial
  have m₂ : (r ≫ jK R) z ∈ LB.wchart D.P.L (K := PUnit) (fun _ => (D.c χ).left) j := le trivial
  have e₁ : val (D.psi χ) r z J = _ := gen_trans (D.psi_gen χ) r z (hJ.mem _ r) m₁
  have e₂ : val (DVR.scaleGen c e) (r ≫ jK R) z J = _ :=
    gen_trans (DVR.scaleGen_isGen c e he) (r ≫ jK R) z (hJ.mem _ _) m₂
  have e₃ : trF (L := D.P.L) (K := PUnit) (fun _ => D.xK χ) (fun _ => -1) r z (fun _ => J (r ≫ D.xK χ)) j =
      trF (L := D.P.L) (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1) (r ≫ jK R) z
        (fun _ => J ((r ≫ jK R) ≫ (D.c χ).left)) j := by
    have hq : r ≫ D.xK χ = (r ≫ jK R) ≫ (D.c χ).left :=
      (congrArg (r ≫ ·) hx).trans (Category.assoc _ _ _).symm
    simp only [trF]
    rw [hq]
  have e₄ : (gm r z (LB.wchart D.P.L (K := PUnit) (fun _ => D.xK χ) j) ((D.psi χ).s j)).val =
      gs (r ≫ jK R) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (u * a)) := by
    refine (gs_unit r z _ m₁ _).symm.trans ((gs_res r z le' trivial _).symm.trans ?_)
    refine (congrArg (gs r z _) hψ.symm).trans ((gs_pull r (jK R) z ⊤ trivial _).trans ?_)
    rw [hto]
  have e₅ : gm (r ≫ jK R) z (LB.wchart D.P.L (K := PUnit) (fun _ => (D.c χ).left) j) ((DVR.scaleGen c e).s j) =
      gm (r ≫ jK R) z ⊤ cu := by
    refine (map_mul _ _ _).trans ((congrArg₂ (· * ·) (gm_res (r ≫ jK R) z le_top m₂ c)
      (gm_res (r ≫ jK R) z le trivial (e.s j)).symm).trans ?_)
    rw [← map_mul]
    exact congrArg _ (inv_mul_cancel_right _ _)
  have e₆ : (gm (r ≫ jK R) z ⊤ cu).val = gs (r ≫ jK R) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom u) :=
    (gs_unit _ z ⊤ trivial cu).symm
  rw [e₁, e₂, Units.val_mul, Units.val_mul]
  erw [e₃, e₄, e₅]
  rw [e₆, map_mul, gs_mul _ z ⊤ trivial]
  ring

/- English proof (translation)
Establish `C : IsCub (th D (T` using `T) z J) := isCub_cubV D.cub hJ`. Establish `h0 : cP D T 0 = 1` using `by simpa using cPoint_nsmul D T 0 0`. Establish `h` using `tau_mul σ hJ hB 0 0 mu`. Rewrite `h` using `[h0, C.face, _root_.mul_one, add_zero]`. Rewrite using `[tau_symm σ hJ]`.

Conclude with `mul_eq_left.1 h.symm`.
-/
theorem val_tau_zero (D : DegPre R) (hB : D.TauBimult) (F : Type) [Field F] [Algebra (FractionRing R) F]
    {T : Over (Spec (CommRingCat.of R))} (σ : T ⟶ TF (R := R) F) {z : T.left}
    {J : (T.left ⟶ D.P.A.left) → D.P.L.ι} (hJ : Good D.P.L z J) (mu : D.X) :
    val (D.tau mu 0) (σ.left ≫ jFK (R := R) F) z J = 1 := by
  have C : IsCub (th D (T := T) z J) := isCub_cubV D.cub hJ
  have h0 : cP D T 0 = 1 := by simpa using cPoint_nsmul D T 0 0
  have h := tau_mul σ hJ hB 0 0 mu
  rw [h0, C.face, _root_.mul_one, add_zero] at h
  rw [tau_symm σ hJ]
  exact mul_eq_left.1 h.symm

/- English proof (translation)
Take `⟨e, he, hv⟩` from `exists_psi_gen D y v a h`. Establish `c₁ : ∀ χ, D.P.A.hom ≫ (D.c χ).left = (SectionScalarValuation.cQ D D.P.A χ).left` using `fun χ => by simp [SectionScalarValuation.cQ]`. Establish `c₂ : D.P.A.hom ≫ eSec D.P.A = (1 : D.P.A ⟶ D.P.A).left`. Rewrite using `[Hom.one_def]`. Simplify using `[eSec]`.

Establish `h0 : SectionScalarValuation.cQ D D.P.A 0 = 1` using `by simpa using SectionScalarValuation.cQ_nsmul D D.P.A 0 0`. Take `⟨eB, heB, veB⟩` from `SectionScalarValuation.exists_eB D N 0 y (LB.mulGen D.P.L _ _ _ _ (GeneratorPullback.powGen D.P.L _ _ e N) (GeneratorPullback.powGen D.P.L (K := PUnit) (fun _ => eSec D.P.A) (fun _ => 1) D.rig N)) (mulGen_isGen _ _ _ _ _ _ _ (powGen_isGen _ _ _ _ he N) (powGen_isGen _ _ _ _ D.rig …`. Simplify using `only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fintype.prod_unique, c₁, c₂, h0, _root_.one_mul]`. Apply `Additive.ofMul.injective` to reduce the goal to its premises. Simplify using `only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]`.

Use the proof step `module)`. Use `⟨eB, heB, fun u hu hc z J hJ => ?_⟩` and prove the remaining obligations. Establish `vp : ∀ {K : Type} [Fintype K] {Y : Scheme.{0}} {φ : K → (Y ⟶ D.P.A.left)} {ε : K → ℤ} (t : LB.Gen (LB.LinComb D.P.L φ ε)) (r : (DegPre.BF D F).left ⟶ Y), val (GeneratorPullback.powGen D.P.L φ ε t N) r z J = val t r z J ^ N` using `fun t r => map_pow _ _ _`. Establish `w₁ : ((fst (TF (R` using `R) F) D.P.A).left ≫ jFK (R := R) F) ≫ jK R = (DegPre.prB D F).left ≫ D.P.A.hom := (Category.assoc _ _ _).trans ((Over.w (fst (TF (R := R) F) D.P.A)).trans (Over.w (DegPre.prB D F)).symm)`. Establish `w₂ : (toUnit (TK R)).left = jK R` using `(Category.comp_id _).symm.trans (Over.w (toUnit (TK R)))`.

Establish `G` using `(gen_fe (F := F) GlobalTheory.SemiRigid.globalFns N y 0).2 u hu hc _ (𝟙 _) z J hJ`. Establish `v₁` using `veB _ (DegPre.prB D F) z J hJ`. Establish `p₁` using `hv _ ((fst (TF (R := R) F) D.P.A).left ≫ jFK (R := R) F) z J hJ`. Establish `p₂ : val D.rigK ((fst (TF (R` using `R) F) D.P.A).left ≫ jFK (R := R) F) z J = val (K := PUnit) (φ := fun _ => eSec D.P.A) (ε := fun _ => 1) D.rig ((DegPre.prB D F).left ≫ D.P.A.hom) z J := by`. Use `(val_pull hJ _ _ _).trans ?_` and prove the remaining obligations.

Rewrite using `[← w₁]`. Conclude with `congrArg (fun q => val (K := PUnit) (φ := fun _ => eSec D.P.A) (ε := fun _ => 1) D.rig (((fst (TF (R := R) F) D.P.A).left ≫ jFK (R := R) F) ≫ q) z J) w₂`. Rewrite `p₁` using `[w₁]`. Rewrite `G` using `[Over.id_left, Category.id_comp, val_famMult _ hJ, val_tau_zero D hB F _ hJ, vp, vp, p₂, uVal_id, comp_cP, _root_.one_mul]`. Rewrite `v₁` using `[val_mul hJ, vp, vp]`.

Establish `q : gs ((DegPre.prB D F).left ≫ D.P.A.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (a ^ N)) = gs ((DegPre.prB D F).left ≫ D.P.A.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a) ^ N`. Rewrite using `[gs_eq _ z ⊤ trivial, gs_eq _ z ⊤ trivial, map_pow, map_pow, map_pow]`. Rewrite using `[G, v₁, q]`. Simplify using `only [Units.val_mul, Units.val_pow_eq_pow_val, p₁, th, cP, SectionScalarValuation.cQ]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_integral_gen [IsLocalRing R] (D : DegPre R) (hB : D.TauBimult) (y : D.X) (N : ℕ) (v : Rˣ) (a : R)
    (h : PsiCoord D y (v * a)) (F : Type) [Field F] [Algebra (FractionRing R) F] :
    ∃ uR : LB.Gen (LB.LinComb D.P.L (Sum.elim (D.famφB (0 + N • y))
        (fun i => (𝟙 D.P.A * SectionScalarValuation.cQ D D.P.A y).left ≫ D.famφB 0 i)) (DegPre.deltaε N)), uR.IsGen ∧
      ∀ (u : LB.Gen (LB.LinComb D.P.L (DegPre.deltaφ D F N 0 y) (DegPre.deltaε N))), u.IsGen →
        LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (DegPre.zF D F).left) (DegPre.famMult D F N y 0) →
        ∀ (z : (DegPre.BF D F).left) (J : ((DegPre.BF D F).left ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J →
          (val u (𝟙 _) z J).val = gs ((DegPre.prB D F).left ≫ D.P.A.hom) z ⊤
            ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (a ^ N)) * (val uR (DegPre.prB D F).left z J).val := by
  obtain ⟨e, he, hv⟩ := exists_psi_gen D y v a h
  have c₁ : ∀ χ, D.P.A.hom ≫ (D.c χ).left = (SectionScalarValuation.cQ D D.P.A χ).left := fun χ => by simp [SectionScalarValuation.cQ]
  have c₂ : D.P.A.hom ≫ eSec D.P.A = (1 : D.P.A ⟶ D.P.A).left := by
    rw [Hom.one_def]; simp [eSec]
  have h0 : SectionScalarValuation.cQ D D.P.A 0 = 1 := by simpa using SectionScalarValuation.cQ_nsmul D D.P.A 0 0
  obtain ⟨eB, heB, veB⟩ := SectionScalarValuation.exists_eB D N 0 y
    (LB.mulGen D.P.L _ _ _ _ (GeneratorPullback.powGen D.P.L _ _ e N)
      (GeneratorPullback.powGen D.P.L (K := PUnit) (fun _ => eSec D.P.A) (fun _ => 1) D.rig N))
    (mulGen_isGen _ _ _ _ _ _ _ (powGen_isGen _ _ _ _ he N) (powGen_isGen _ _ _ _ D.rig_gen N)) (fun U _ h => by
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fintype.prod_unique, c₁, c₂, h0, _root_.one_mul]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
      module)
  refine ⟨eB, heB, fun u hu hc z J hJ => ?_⟩
  have vp : ∀ {K : Type} [Fintype K] {Y : Scheme.{0}} {φ : K → (Y ⟶ D.P.A.left)} {ε : K → ℤ}
      (t : LB.Gen (LB.LinComb D.P.L φ ε)) (r : (DegPre.BF D F).left ⟶ Y),
      val (GeneratorPullback.powGen D.P.L φ ε t N) r z J = val t r z J ^ N := fun t r => map_pow _ _ _
  have w₁ : ((fst (TF (R := R) F) D.P.A).left ≫ jFK (R := R) F) ≫ jK R = (DegPre.prB D F).left ≫ D.P.A.hom :=
    (Category.assoc _ _ _).trans ((Over.w (fst (TF (R := R) F) D.P.A)).trans (Over.w (DegPre.prB D F)).symm)
  have w₂ : (toUnit (TK R)).left = jK R := (Category.comp_id _).symm.trans (Over.w (toUnit (TK R)))
  have G := (gen_fe (F := F) GlobalTheory.SemiRigid.globalFns N y 0).2 u hu hc _ (𝟙 _) z J hJ
  have v₁ := veB _ (DegPre.prB D F) z J hJ
  have p₁ := hv _ ((fst (TF (R := R) F) D.P.A).left ≫ jFK (R := R) F) z J hJ
  have p₂ : val D.rigK ((fst (TF (R := R) F) D.P.A).left ≫ jFK (R := R) F) z J =
      val (K := PUnit) (φ := fun _ => eSec D.P.A) (ε := fun _ => 1) D.rig ((DegPre.prB D F).left ≫ D.P.A.hom) z J := by
    refine (val_pull hJ _ _ _).trans ?_
    rw [← w₁]
    exact congrArg (fun q => val (K := PUnit) (φ := fun _ => eSec D.P.A) (ε := fun _ => 1) D.rig
      (((fst (TF (R := R) F) D.P.A).left ≫ jFK (R := R) F) ≫ q) z J) w₂
  rw [w₁] at p₁
  rw [Over.id_left, Category.id_comp, val_famMult _ hJ, val_tau_zero D hB F _ hJ, vp, vp, p₂, uVal_id, comp_cP,
    _root_.one_mul] at G
  rw [val_mul hJ, vp, vp] at v₁
  have q : gs ((DegPre.prB D F).left ≫ D.P.A.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (a ^ N)) =
      gs ((DegPre.prB D F).left ≫ D.P.A.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a) ^ N := by
    rw [gs_eq _ z ⊤ trivial, gs_eq _ z ⊤ trivial, map_pow, map_pow, map_pow]
  rw [G, v₁, q]
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, p₁, th, cP, SectionScalarValuation.cQ]
  ring

/- English proof (translation)
Introduce `E _ _ _ H k _ _ m d t P gam hM y N _`. Take `⟨v, n, -, hc⟩` from `hM y`. Establish `hT : lift (toUnit P.D.toPre.P.A ≫ P.D.toPre.c y) (𝟙 P.D.toPre.P.A) ≫ μ[P.D.toPre.P.A] = 𝟙 P.D.toPre.P.A * SectionScalarValuation.cQ P.D.toPre P.D.toPre.P.A y` using `mul_comm (SectionScalarValuation.cQ P.D.toPre P.D.toPre.P.A y) (𝟙 P.D.toPre.P.A)`. Rewrite using `[hT]`. Take `⟨uR, h₁, h₂⟩` from `exists_integral_gen P.D.toPre P.D.tau_bimult y N v _ hc (FractionRing (ChartRing k m d))`.

Use `⟨fun i => n i * N, uR, h₁, fun u hu hcu z J hJ => ?_⟩` and prove the remaining obligations. Rewrite using `[h₂ u hu hcu z J hJ, ← Finset.prod_pow]`. Simplify using `only [pow_mul]`.
-/
theorem exists_integral_gen_monomial : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [CharZero k] (m d : ℕ) (t : SAB H (Sp (ChartRing k m d))) (P : PELUnif (maximalIdeal (ChartRing k m d)) t) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre (bdParam k m d) gam → ∀ (y : P.D.toPre.X) (N : ℕ), 1 ≤ N → ∃ (Nv : Fin m → ℕ) (uR : LB.Gen (LB.LinComb P.D.toPre.P.L (Sum.elim (P.D.toPre.famφB (0 + N • y)) (fun i => (lift (toUnit P.D.toPre.P.A ≫ P.D.toPre.c y) (𝟙 P.D.toPre.P.A) ≫ μ[P.D.toPre.P.A]).left ≫ P.D.toPre.famφB 0 i)) (DegPre.deltaε N))), uR.IsGen ∧ ∀ (u : LB.Gen (LB.LinComb P.D.toPre.P.L (DegPre.deltaφ P.D.toPre (FractionRing (ChartRing k m d)) N 0 y) (DegPre.deltaε N))), u.IsGen → LB.Gen.Corr P.D.toPre.P.L _ _ _ _ (LB.pullGen P.D.toPre.P.L _ _ u (DegPre.zF P.D.toPre (FractionRing (ChartRing k m d))).left) (DegPre.famMult P.D.toPre (FractionRing (ChartRing k m d)) N y 0) → ∀ (z : (DegPre.BF P.D.toPre (FractionRing (ChartRing k m d))).left) (J : ((DegPre.BF P.D.toPre (FractionRing (ChartRing k m d))).left ⟶ P.D.toPre.P.A.left) → P.D.toPre.P.L.ι), Good P.D.toPre.P.L z J → (val u (𝟙 _) z J).val = gs ((DegPre.prB P.D.toPre (FractionRing (ChartRing k m d))).left ≫ P.D.toPre.P.A.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom (∏ i, bdParam k m d i ^ Nv i)) * (val uR (DegPre.prB P.D.toPre (FractionRing (ChartRing k m d))).left z J).val := by
  intro E _ _ _ H k _ _ m d t P gam hM y N _
  obtain ⟨v, n, -, hc⟩ := hM y
  have hT : lift (toUnit P.D.toPre.P.A ≫ P.D.toPre.c y) (𝟙 P.D.toPre.P.A) ≫ μ[P.D.toPre.P.A] =
      𝟙 P.D.toPre.P.A * SectionScalarValuation.cQ P.D.toPre P.D.toPre.P.A y :=
    mul_comm (SectionScalarValuation.cQ P.D.toPre P.D.toPre.P.A y) (𝟙 P.D.toPre.P.A)
  rw [hT]
  obtain ⟨uR, h₁, h₂⟩ := exists_integral_gen P.D.toPre P.D.tau_bimult y N v _ hc (FractionRing (ChartRing k m d))
  refine ⟨fun i => n i * N, uR, h₁, fun u hu hcu z J hJ => ?_⟩
  rw [h₂ u hu hcu z J hJ, ← Finset.prod_pow]
  simp only [pow_mul]

end GlobalTheory.ShiftGen
