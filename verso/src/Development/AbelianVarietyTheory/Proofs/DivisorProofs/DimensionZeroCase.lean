import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPolAVSectionInverseImage
import Development.AbelianVarietyTheory.Definitions.Divisors.ToricPeriodBlockIsSymm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.NotGoodClassZeroSucc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAbelianKeyValueNormOne
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnitCharts
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

noncomputable section

namespace GlobalTheory.MBLow.DimZero

section Basics

variable {R : Type} [CommRing R] [IsDomain R]

/- English proof (translation)
The claim follows from `GlobalTheory.ZM.Model.isIso_of_dim_zero D.P.A D.P.isAb (hg ▸ D.P.smoothDim)`.
-/
theorem isIso_hom (D : DegPre R) (hg : D.P.g = 0) : IsIso D.P.A.hom :=
  GlobalTheory.ZM.Model.isIso_of_dim_zero D.P.A D.P.isAb (hg ▸ D.P.smoothDim)

/- English proof (translation)
Use `haveI := isIso_hom D hg`. Use `⟨fun f f' => Over.OverMorphism.ext ?_⟩` and prove the remaining obligations. Rewrite using `[← cancel_mono D.P.A.hom, Over.w f, Over.w f']`.
-/
theorem hom_subsingleton (D : DegPre R) (hg : D.P.g = 0) (T : Over (Sp R)) : Subsingleton (T ⟶ D.P.A) := by
  haveI := isIso_hom D hg
  refine ⟨fun f f' => Over.OverMorphism.ext ?_⟩
  rw [← cancel_mono D.P.A.hom, Over.w f, Over.w f']

/- English proof (translation)
Use `haveI := hom_subsingleton D hg (TF (R := R) F)`. Conclude with `⟨fun x y => ν.eA.injective (Subsingleton.elim _ _)⟩`.
-/
theorem subsingleton_A {F : Type} [Field F] [Algebra (FractionRing R) F] {D : DegPre R} {N : NumD F} (ν : NumOf D F N)
    (hg : D.P.g = 0) : Subsingleton N.A := by
  haveI := hom_subsingleton D hg (TF (R := R) F)
  exact ⟨fun x y => ν.eA.injective (Subsingleton.elim _ _)⟩

/- English proof (translation)
Use `haveI : IsIso D.P.A.hom := isIso_hom D hg`. Establish `he : eSec D.P.A ≫ D.P.A.hom = 𝟙 _` using `Over.w η[D.P.A]`. Establish `he' : D.P.A.hom ≫ eSec D.P.A = 𝟙 _`. Rewrite using `[← cancel_mono D.P.A.hom, Category.assoc, Category.id_comp]`. Conclude with `(congrArg _ he).trans (Category.comp_id _)`.

Take `⟨s, hs⟩` from `GlobalTheory.MBLow.AbKey.exists_unit_sec D.P.L (D.P.A.hom ≫ eSec D.P.A) he' (LB.pullGen D.P.L (fun _ : PUnit => eSec D.P.A) (fun _ => 1) D.rig D.P.A.hom) (DVR.pullGen_isGen _ _ _ _ D.rig_gen _)`. Take `⟨r, hr⟩` from `ν.th_gen s`. Establish `hu : ∀ j, IsUnit (ν.th.f j)` using `fun j => isUnit_of_mul_isUnit_right (hr j ▸ hs j)`. Introduce `h0`. Establish `h` using `ν.th_eq 1`.

Rewrite `h` using `[h0, zero_mul]`. Establish `hU : ⊤ ≤ (ν.eA 1).left ⁻¹ᵁ D.P.L.U (ν.J (ν.eA 1).left)` using `ν.good _`. Establish `hx : ⊤ ≤ (ν.eA 1).left ⁻¹ᵁ LB.wchart D.P.L (fun _ : Fin 1 => 𝟙 D.P.A.left) (fun _ => ν.J ((ν.eA 1).left ≫ 𝟙 _))` using `fun y hy => Set.mem_iInter.2 fun _ => by`. Rewrite using `[Category.comp_id]`. Conclude with `hU hy`.

Unfold `sF valF at h`. Rewrite `h` using `[dif_pos hx]`. Conclude with `(((hu _).map _).map _).ne_zero h.symm`.
-/
theorem th_one_ne_zero {F : Type} [Field F] [Algebra (FractionRing R) F] {D : DegPre R} {N : NumD F} (ν : NumOf D F N)
    (hg : D.P.g = 0) : N.th 1 ≠ 0 := by
  haveI : IsIso D.P.A.hom := isIso_hom D hg
  have he : eSec D.P.A ≫ D.P.A.hom = 𝟙 _ := Over.w η[D.P.A]
  have he' : D.P.A.hom ≫ eSec D.P.A = 𝟙 _ := by
    rw [← cancel_mono D.P.A.hom, Category.assoc, Category.id_comp]
    exact (congrArg _ he).trans (Category.comp_id _)
  obtain ⟨s, hs⟩ := GlobalTheory.MBLow.AbKey.exists_unit_sec D.P.L (D.P.A.hom ≫ eSec D.P.A) he'
    (LB.pullGen D.P.L (fun _ : PUnit => eSec D.P.A) (fun _ => 1) D.rig D.P.A.hom)
    (DVR.pullGen_isGen _ _ _ _ D.rig_gen _)
  obtain ⟨r, hr⟩ := ν.th_gen s
  have hu : ∀ j, IsUnit (ν.th.f j) := fun j => isUnit_of_mul_isUnit_right (hr j ▸ hs j)
  intro h0
  have h := ν.th_eq 1
  rw [h0, zero_mul] at h
  have hU : ⊤ ≤ (ν.eA 1).left ⁻¹ᵁ D.P.L.U (ν.J (ν.eA 1).left) := ν.good _
  have hx : ⊤ ≤ (ν.eA 1).left ⁻¹ᵁ LB.wchart D.P.L (fun _ : Fin 1 => 𝟙 D.P.A.left)
      (fun _ => ν.J ((ν.eA 1).left ≫ 𝟙 _)) := fun y hy => Set.mem_iInter.2 fun _ => by
    rw [Category.comp_id]; exact hU hy
  unfold sF valF at h
  rw [dif_pos hx] at h
  exact (((hu _).map _).map _).ne_zero h.symm

end Basics

section Classical

variable {g : ℕ}

/- English proof (translation)
Simplify using `[dotProduct]`.
-/
theorem dot_empty [IsEmpty (Fin g)] (u v : Fin g → ℂ) : u ⬝ᵥ v = 0 := by
  simp [dotProduct]

/- English proof (translation)
Unfold `thetaChar`. Rewrite using `[tsum_fintype, Fintype.sum_unique]`. Simplify using `[dot_empty]`.
-/
theorem thetaChar_empty [IsEmpty (Fin g)] (τ : Matrix (Fin g) (Fin g) ℂ) (a b z : Fin g → ℂ) :
    thetaChar τ a b z = 1 := by
  unfold thetaChar
  rw [tsum_fintype, Fintype.sum_unique]
  simp [dot_empty]

/- English proof (translation)
Simplify using `[autV, dot_empty]`.
-/
theorem autV_empty [IsEmpty (Fin g)] (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ) (M N : Fin g → ℤ) (z : Fin g → ℂ) :
    autV τ a b M N z = 1 := by
  simp [autV, dot_empty]

/- English proof (translation)
Assemble the required witnesses or components as `⟨by ext i; exact isEmptyElim i, fun x hx => (hx (Subsingleton.elim _ _)).elim⟩`.
-/
theorem posDef_empty [IsEmpty (Fin g)] (A : Matrix (Fin g) (Fin g) ℝ) : A.PosDef :=
  ⟨by ext i; exact isEmptyElim i, fun x hx => (hx (Subsingleton.elim _ _)).elim⟩

/- English proof (translation)
Introduce `x _` and use `((hasFDerivAt_const (f x) x).congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => congrArg f (Subsingleton.elim y x))).differentiableAt.differentiableWithinAt`.
-/
theorem differentiableOn_empty [IsEmpty (Fin g)] (f : (Fin g → ℂ) → ℂ) (s : Set (Fin g → ℂ)) :
    DifferentiableOn ℂ f s := fun x _ =>
  ((hasFDerivAt_const (f x) x).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun y => congrArg f (Subsingleton.elim y x))).differentiableAt.differentiableWithinAt

def abZero (B : NumB ℂ) (g : ℕ) (hg : g = 0) (hA : Subsingleton B.A) (hth : B.th 1 ≠ 0) : AB B g where
  τ := 0
  a := 0
  b := 0
  c := B.th 1
  symm := by ext i; haveI : IsEmpty (Fin g) := hg ▸ inferInstance; exact isEmptyElim i
  pos := by haveI : IsEmpty (Fin g) := hg ▸ inferInstance; exact posDef_empty _
  ha i := by haveI : IsEmpty (Fin g) := hg ▸ inferInstance; exact isEmptyElim i
  hb i := by haveI : IsEmpty (Fin g) := hg ▸ inferInstance; exact isEmptyElim i
  hc := hth
  ex _ := 1
  ex_add _ _ := (mul_one 1).symm
  onto x := ⟨0, Subsingleton.elim _ _⟩
  ker z := by
    haveI : IsEmpty (Fin g) := hg ▸ inferInstance
    exact ⟨fun _ => ⟨0, 0, Subsingleton.elim _ _⟩, fun _ => rfl⟩
  fr _ := 1
  fr_zero := rfl
  fr_per M N z := by
    haveI : IsEmpty (Fin g) := hg ▸ inferInstance
    simp [autV_empty]
  th z := by
    haveI : IsEmpty (Fin g) := hg ▸ inferInstance
    simp [thetaChar_empty]

end Classical

section Geo

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} [Algebra (FractionRing R) ℂ] {N : NumD ℂ} {g : ℕ}

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem valF_eq_valR {F : Type} [Field F] {X : Scheme.{0}} (x : Sp F ⟶ X) (U : X.Opens) (f : Γ(X, U)) :
    valF x U f = valR x U f := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem val_res {X : Scheme.{0}} {U V : X.Opens} (e : V ≤ U) (u : Γ(X, U)ˣ) : (res e u).val = resG X e u.val := rfl

def frZ (ν : NumOf D ℂ N) (i : D.P.L.ι) : ℂ :=
  valF (ν.eA 1).left (D.P.L.U i ⊓ D.P.L.U (ν.J (ν.eA 1).left)) (D.P.L.g i (ν.J (ν.eA 1).left)).val * ν.rg

/- English proof (translation)
Unfold `frZ`. Use `set x := (ν.eA 1).left`. Use `set k := ν.J x`. Establish `hk : ⊤ ≤ x ⁻¹ᵁ D.P.L.U k` using `ν.good x`. Establish `h3 : ⊤ ≤ x ⁻¹ᵁ (D.P.L.U i ⊓ D.P.L.U j ⊓ D.P.L.U k)` using `fun y hy => ⟨h hy, hk hy⟩`.

Establish `c` using `congrArg (fun u => valR x _ (Units.val u)) (D.P.isLB.cocycle i j k)`. Simplify using `only [Units.val_mul] at c`. Rewrite `c` using `[GlobalTheory.ZH.CrdCalc.valR_mul x _ h3, val_res, val_res, val_res, GlobalTheory.ZH.CrdCalc.valR_res x _ h3, GlobalTheory.ZH.CrdCalc.valR_res x _ h3, GlobalTheory.ZH.CrdCalc.valR_res x _ h3]`. Simplify using `only [valF_eq_valR]`. Rewrite using `[← c]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem frZ_compat (ν : NumOf D ℂ N) (i j : D.P.L.ι) (h : ⊤ ≤ (ν.eA 1).left ⁻¹ᵁ (D.P.L.U i ⊓ D.P.L.U j)) :
    frZ ν i = valF (ν.eA 1).left (D.P.L.U i ⊓ D.P.L.U j) (D.P.L.g i j).val * frZ ν j := by
  unfold frZ
  set x := (ν.eA 1).left
  set k := ν.J x
  have hk : ⊤ ≤ x ⁻¹ᵁ D.P.L.U k := ν.good x
  have h3 : ⊤ ≤ x ⁻¹ᵁ (D.P.L.U i ⊓ D.P.L.U j ⊓ D.P.L.U k) := fun y hy => ⟨h hy, hk hy⟩
  have c := congrArg (fun u => valR x _ (Units.val u)) (D.P.isLB.cocycle i j k)
  simp only [Units.val_mul] at c
  rw [GlobalTheory.ZH.CrdCalc.valR_mul x _ h3, val_res, val_res, val_res, GlobalTheory.ZH.CrdCalc.valR_res x _ h3,
    GlobalTheory.ZH.CrdCalc.valR_res x _ h3, GlobalTheory.ZH.CrdCalc.valR_res x _ h3] at c
  simp only [valF_eq_valR]
  rw [← c]
  ring

/- English proof (translation)
Unfold `frZ`. Use `set x := (ν.eA 1).left`. Use `set k := ν.J x`. Establish `hk : ⊤ ≤ x ⁻¹ᵁ D.P.L.U k` using `ν.good x`. Establish `c` using `congrArg (fun u => valR x _ (Units.val u)) (D.P.isLB.g_self k)`.

Simplify using `only [val_res, Units.val_one] at c`. Rewrite `c` using `[GlobalTheory.ZH.CrdCalc.valR_res x _ hk, GlobalTheory.ZH.CrdCalc.valR_eq x _ hk, map_one]`. Rewrite using `[valF_eq_valR, c, _root_.one_mul]`.
-/
theorem frZ_self (ν : NumOf D ℂ N) : frZ ν (ν.J (ν.eA 1).left) = ν.rg := by
  unfold frZ
  set x := (ν.eA 1).left
  set k := ν.J x
  have hk : ⊤ ≤ x ⁻¹ᵁ D.P.L.U k := ν.good x
  have c := congrArg (fun u => valR x _ (Units.val u)) (D.P.isLB.g_self k)
  simp only [val_res, Units.val_one] at c
  rw [GlobalTheory.ZH.CrdCalc.valR_res x _ hk, GlobalTheory.ZH.CrdCalc.valR_eq x _ hk, map_one] at c
  rw [valF_eq_valR, c, _root_.one_mul]

/- English proof (translation)
Use `haveI := hom_subsingleton D hg (TE R ℂ)`. Introduce `U f hU`. Establish `hb : b = (Over.homMk (spMap (algebraMap ℂ (DualNumber ℂ))) rfl : TE R ℂ ⟶ TF (R` using `R) ℂ) ≫ ν.eA (d.ex 0) := Subsingleton.elim _ _`. Establish `hl : (lift (Over.homMk (spMap (algebraMap ℂ (DualNumber ℂ))) rfl : TE R ℂ ⟶ TF (R` using `R) ℂ) b).left = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ ptB ν d 0 := by`. Rewrite using `[hb]`.

Establish `e : lift (Over.homMk (spMap (algebraMap ℂ (DualNumber ℂ))) rfl : TE R ℂ ⟶ TF (R` using `R) ℂ) ((Over.homMk (spMap (algebraMap ℂ (DualNumber ℂ))) rfl : TE R ℂ ⟶ TF (R := R) ℂ) ≫ ν.eA (d.ex 0)) = (Over.homMk (spMap (algebraMap ℂ (DualNumber ℂ))) rfl : TE R ℂ ⟶ TF (R := R) ℂ) ≫ lift (𝟙 (TF (R := R) ℂ)) (ν.eA (d.ex 0)) := by`. Rewrite using `[comp_lift, Category.comp_id]`. Rewrite using `[e]`. Both sides reduce to the same expression. Rewrite using `[hl, (GlobalTheory.ZH.CrdCalc.valR_spMap _ _ U hU).2, map_zero, TrivSqZeroExt.inr_zero, add_zero, TrivSqZeroExt.algebraMap_eq_inl]`.

Both sides reduce to the same expression.
-/
theorem isD_zero (ν : NumOf D ℂ N) (hg : D.P.g = 0) (d : AB N.toNumB g) (b : TE R ℂ ⟶ D.P.A) : IsD ν d 0 b := by
  haveI := hom_subsingleton D hg (TE R ℂ)
  intro U f hU
  have hb : b = (Over.homMk (spMap (algebraMap ℂ (DualNumber ℂ))) rfl : TE R ℂ ⟶ TF (R := R) ℂ) ≫ ν.eA (d.ex 0) :=
    Subsingleton.elim _ _
  have hl : (lift (Over.homMk (spMap (algebraMap ℂ (DualNumber ℂ))) rfl : TE R ℂ ⟶ TF (R := R) ℂ) b).left =
      spMap (algebraMap ℂ (DualNumber ℂ)) ≫ ptB ν d 0 := by
    rw [hb]
    have e : lift (Over.homMk (spMap (algebraMap ℂ (DualNumber ℂ))) rfl : TE R ℂ ⟶ TF (R := R) ℂ)
        ((Over.homMk (spMap (algebraMap ℂ (DualNumber ℂ))) rfl : TE R ℂ ⟶ TF (R := R) ℂ) ≫ ν.eA (d.ex 0)) =
        (Over.homMk (spMap (algebraMap ℂ (DualNumber ℂ))) rfl : TE R ℂ ⟶ TF (R := R) ℂ) ≫
          lift (𝟙 (TF (R := R) ℂ)) (ν.eA (d.ex 0)) := by
      rw [comp_lift, Category.comp_id]
    rw [e]
    rfl
  rw [hl, (GlobalTheory.ZH.CrdCalc.valR_spMap _ _ U hU).2, map_zero, TrivSqZeroExt.inr_zero, add_zero,
    TrivSqZeroExt.algebraMap_eq_inl]
  rfl

def geoZero (ν : NumOf D ℂ N) (hg : D.P.g = 0) (d : AB N.toNumB g) (hg' : g = 0) (hex : ∀ z, d.ex z = 1)
    (hfr : ∀ z, d.fr z = 1) : Geo ν d where
  frG i _ := frZ ν i
  hol U f := by
    haveI : IsEmpty (Fin g) := hg' ▸ inferInstance
    exact ⟨isOpen_discrete _, differentiableOn_empty _ _⟩
  fr_hol i := by
    haveI : IsEmpty (Fin g) := hg' ▸ inferInstance
    exact differentiableOn_empty _ _
  fr_compat i j z h := by
    rw [hex] at h ⊢
    exact frZ_compat ν i j h
  fr_eq z := by
    rw [hex, hfr, Units.val_one, _root_.one_mul]
    exact (frZ_self ν).symm
  dif b _ := ⟨0, isD_zero ν hg d b⟩

end Geo

section Main

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} [Algebra (FractionRing R) ℂ] {N : NumD ℂ}

/- English proof (translation)
Introduce `vB b MB k₀ _ _ _ hk`. Use `haveI : IsEmpty (Fin D.P.g) := hg ▸ inferInstance`. Rewrite using `[Matrix.det_isEmpty, one_pow, hc, mul_comm]`. Conclude with `⟨one_ne_zero, hk.1 hg⟩`.
-/
theorem keyOK_zero (κ : Rule) (ν : NumOf D ℂ N) (hg : D.P.g = 0) (d : AB N.toNumB D.P.g) (hc : d.c = N.th 1) :
    KeyOK κ ν d := by
  intro vB b MB k₀ _ _ _ hk
  haveI : IsEmpty (Fin D.P.g) := hg ▸ inferInstance
  rw [Matrix.det_isEmpty, one_pow, hc, mul_comm]
  exact ⟨one_ne_zero, hk.1 hg⟩

/- English proof (translation)
Introduce `κ R _ _ _ _ D _ _ _ N ν hg`. Set `d` to `abZero N.toNumB D.P.g hg (subsingleton_A ν hg) (th_one_ne_zero ν hg)`. Conclude with `⟨d, geoZero ν hg d hg (fun _ => rfl) (fun _ => rfl), keyOK_zero κ ν hg d rfl⟩`.
-/
theorem main : ∀ κ : Rule, AllC fun {R} _ _ {D} _ {N} ν => D.P.g = 0 →
    ∃ (d : AB N.toNumB D.P.g) (_ : Geo ν d), KeyOK κ ν d := by
  intro κ R _ _ _ _ D _ _ _ N ν hg
  let d := abZero N.toNumB D.P.g hg (subsingleton_A ν hg) (th_one_ne_zero ν hg)
  exact ⟨d, geoZero ν hg d hg (fun _ => rfl) (fun _ => rfl), keyOK_zero κ ν hg d rfl⟩

end Main

end GlobalTheory.MBLow.DimZero
