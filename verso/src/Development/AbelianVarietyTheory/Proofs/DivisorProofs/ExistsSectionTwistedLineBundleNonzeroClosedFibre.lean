import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegExp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.SectionArithmetic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocalC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullUUnitsCompatGeneric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionTranslateTensorFibreNonvanishingStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.TwistGen

/- English proof (translation)
Unfold `twistLB`. Use `congr 1`. Use function extensionality and compare the values at `k`. Use `fin_cases k`. Use `show (ρ ▷ A).left ≫ (snd T A).left = (snd T' A).left`.

Rewrite using `[← Over.comp_left, whiskerRight_snd]`. Use `show (ρ ▷ A).left ≫ (translPt A c).left = (translPt A (ρ ≫ c)).left`. Rewrite using `[← Over.comp_left]`. Use `congr 1`. Simplify using `[translPt, comp_lift_assoc]`.
-/
theorem whisker_eq_twistLB {S : Scheme.{0}} (A : Over S) [GrpObj A] (L : LB A.left) (q : ℕ)
    {T T' : Over S} (ρ : T' ⟶ T) (c : T ⟶ A) :
    LB.LinComb L (K := Fin 2) (fun k => (ρ ▷ A).left ≫ ![(snd T A).left, (translPt A c).left] k)
      ![(q : ℤ) - 1, 1] = twistLB A L q (ρ ≫ c) := by
  unfold twistLB
  congr 1
  funext k
  fin_cases k
  · show (ρ ▷ A).left ≫ (snd T A).left = (snd T' A).left
    rw [← Over.comp_left, whiskerRight_snd]
  · show (ρ ▷ A).left ≫ (translPt A c).left = (translPt A (ρ ≫ c)).left
    rw [← Over.comp_left]
    congr 1
    simp [translPt, comp_lift_assoc]

/- English proof (translation)
Take `⟨(j : K → L.ι), hj⟩` from `TopologicalSpace.Opens.mem_iSup.1 hy`. Rewrite `hj` using `[hs j]`. Use `erw [Scheme.basicOpen_res] at hj`. Conclude with `TopologicalSpace.Opens.mem_iSup.2 ⟨j, (Scheme.preimage_basicOpen h (s.f j)).ge hj.2⟩`.
-/
theorem mem_of_isPullSecLC {X Y Y' : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (h : Y' ⟶ Y) (s : LB.Sec (LB.LinComb L φ ε)) (s' : LB.Sec (LB.LinComb L (fun k => h ≫ φ k) ε))
    (hs : IsPullSecLC L φ ε h s s') (y : Y') (hy : y ∈ nonzeroLocus s') : h y ∈ nonzeroLocus s := by
  obtain ⟨(j : K → L.ι), hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
  rw [hs j] at hj
  erw [Scheme.basicOpen_res] at hj
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨j, (Scheme.preimage_basicOpen h (s.f j)).ge hj.2⟩

/- English proof (translation)
Set `T` to `𝟙_ (Over (Spec (CommRingCat.of R)))`. Set `A` to `D.P.A`. Set `iota : A.left ⟶ (T ⊗ A).left` to `(lift (toUnit A) (𝟙 A)).left`. Establish `hsec : snd T A ≫ lift (toUnit A) (𝟙 A) = 𝟙 (T ⊗ A)`. Use `CartesianMonoidalCategory.hom_ext _ _ ?_ ?_` and prove the remaining obligations.

Conclude with `(toUnit_unique _ _)`. Rewrite using `[Category.assoc, lift_snd, Category.comp_id, Category.id_comp]`. Establish `hiota : iota ((snd T A).left z) = z`. Establish `e : (snd T A).left ≫ iota = 𝟙 _` using `by rw [← Over.comp_left, hsec]; rfl`. Establish `e'` using `congrArg (fun f => f.base z) e`.

Conclude with `e'`. Take `⟨u₀, hu₀⟩` from `DVR.exists_gen_of_local (V := R) D.P.L D.P.isLB (K := Fin 2) (![(D.c α).left, η[A].left] : Fin 2 → (Spec (CommRingCat.of R) ⟶ A.left)) ![-1, 1]`. Set `u` to `LB.pullGen D.P.L _ _ u₀ (toUnit A).left`. Establish `hu : u.IsGen` using `DVR.pullGen_isGen_of_isGen _ _ u₀ hu₀ _`. Set `s₁` to `pullMulSec s iota u hu`.

Establish `hF : FormEq (Sum.elim (fun k => iota ≫ ![(snd T A).left, (translPt A (D.c α)).left] k) (fun k => (toUnit A).left ≫ (![(D.c α).left, η[A].left] : Fin 2 → (Spec (CommRingCat.of R) ⟶ A.left)) k)) (Sum.elim ![((2 : ℕ) : ℤ) - 1, 1] ![-1, 1]) (D.famφB α) (DegPre.famε 2)`. Establish `e₁ : iota ≫ (snd T A).left = 𝟙 _`. Rewrite using `[← Over.comp_left, lift_snd]`. Both sides reduce to the same expression. Establish `e₂ : iota ≫ (translPt A (D.c α)).left = (padd A (𝟙 A) (toUnit A ≫ D.c α)).left`.

Rewrite using `[← Over.comp_left]`. Use `congr 1`. Use `show lift (toUnit A) (𝟙 A) ≫ ((fst T A ≫ D.c α) * snd T A) = 𝟙 A * (toUnit A ≫ D.c α)`. Rewrite using `[Hom.mul_def, Hom.mul_def, ← Category.assoc, comp_lift, lift_snd, ← Category.assoc, lift_fst]`. Use `show (toUnit A ≫ D.c α) * 𝟙 A = 𝟙 A * (toUnit A ≫ D.c α)`.

Conclude with `mul_comm _ _`. Introduce `U _ hh`. Simplify using `only [Fintype.prod_sum_type, Fin.prod_univ_two, Fin.prod_univ_four, Sum.elim_inl, Sum.elim_inr, DegPre.famφB, DegPre.famε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, e₁, e₂]`. Simplify using `only [_root_.mul_assoc]`. Both sides reduce to the same expression.

Take `⟨σ, hσ⟩` from `exists_sec D.P.isLB hF s₁`. Use `⟨σ, ?_⟩` and prove the remaining obligations. Use `set xx := (snd T A).left z`. Use `choose J hJ using fun χ : A.left ⟶ A.left => exists_chart D.P.isLB (χ xx)`. Take `⟨(k : Fin 2 → D.P.L.ι), hk⟩` from `TopologicalSpace.Opens.mem_iSup.1 hz`.

Establish `hv : IsUnit (sval s (𝟙 A.left ≫ iota) xx J)`. Use `H1.SectionArithmetic.isUnit_sval s (𝟙 A.left ≫ iota) xx hJ k ?_` and prove the remaining obligations. Rewrite using `[Category.id_comp, hiota]`. Conclude with `hk`. Establish `hval : IsUnit (sval σ (𝟙 A.left) xx J)`.

Rewrite using `[hσ _ _ xx J hJ, sval_pullMulSec s iota u hu (𝟙 A.left) xx hJ]`. Conclude with `hv.mul (Units.isUnit _)`. Establish `hm` using `(Good.mem hJ (D.famφB α) (𝟙 A.left))`. Rewrite `hval` using `[sval]`. Use `erw [gs_eq (𝟙 A.left) xx _ hm] at hval`.

Use `TopologicalSpace.Opens.mem_iSup.2 ⟨fun k => J (𝟙 A.left ≫ D.famφB α k), ?_⟩` and prove the remaining obligations. Conclude with `(A.left.mem_basicOpen _ xx hm).2 hval`.
-/
theorem transfer {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R) (α : D.X)
    (s : LB.Sec (twistLB D.P.A D.P.L 2 (D.c α)))
    (z : (𝟙_ (Over (Spec (CommRingCat.of R))) ⊗ D.P.A).left) (hz : z ∈ nonzeroLocus s) :
    ∃ σ : D.SecB 2 α, (snd _ D.P.A).left z ∈ nonzeroLocus σ := by
  let T := 𝟙_ (Over (Spec (CommRingCat.of R)))
  let A := D.P.A
  let iota : A.left ⟶ (T ⊗ A).left := (lift (toUnit A) (𝟙 A)).left
  have hsec : snd T A ≫ lift (toUnit A) (𝟙 A) = 𝟙 (T ⊗ A) := by
    refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
    · exact (toUnit_unique _ _)
    · rw [Category.assoc, lift_snd, Category.comp_id, Category.id_comp]
  have hiota : iota ((snd T A).left z) = z := by
    have e : (snd T A).left ≫ iota = 𝟙 _ := by rw [← Over.comp_left, hsec]; rfl
    have e' := congrArg (fun f => f.base z) e
    exact e'
  obtain ⟨u₀, hu₀⟩ := DVR.exists_gen_of_local (V := R) D.P.L D.P.isLB (K := Fin 2)
    (![(D.c α).left, η[A].left] : Fin 2 → (Spec (CommRingCat.of R) ⟶ A.left)) ![-1, 1]
  let u := LB.pullGen D.P.L _ _ u₀ (toUnit A).left
  have hu : u.IsGen := DVR.pullGen_isGen_of_isGen _ _ u₀ hu₀ _
  let s₁ := pullMulSec s iota u hu
  have hF : FormEq (Sum.elim (fun k => iota ≫ ![(snd T A).left, (translPt A (D.c α)).left] k)
      (fun k => (toUnit A).left ≫ (![(D.c α).left, η[A].left] : Fin 2 → (Spec (CommRingCat.of R) ⟶ A.left)) k))
      (Sum.elim ![((2 : ℕ) : ℤ) - 1, 1] ![-1, 1]) (D.famφB α) (DegPre.famε 2) := by
    have e₁ : iota ≫ (snd T A).left = 𝟙 _ := by
      rw [← Over.comp_left, lift_snd]; rfl
    have e₂ : iota ≫ (translPt A (D.c α)).left = (padd A (𝟙 A) (toUnit A ≫ D.c α)).left := by
      rw [← Over.comp_left]
      congr 1
      show lift (toUnit A) (𝟙 A) ≫ ((fst T A ≫ D.c α) * snd T A) = 𝟙 A * (toUnit A ≫ D.c α)
      rw [Hom.mul_def, Hom.mul_def, ← Category.assoc, comp_lift, lift_snd, ← Category.assoc, lift_fst]
      show (toUnit A ≫ D.c α) * 𝟙 A = 𝟙 A * (toUnit A ≫ D.c α)
      exact mul_comm _ _
    intro U _ hh
    simp only [Fintype.prod_sum_type, Fin.prod_univ_two, Fin.prod_univ_four, Sum.elim_inl, Sum.elim_inr,
      DegPre.famφB, DegPre.famε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, e₁, e₂]
    simp only [_root_.mul_assoc]; rfl
  obtain ⟨σ, hσ⟩ := exists_sec D.P.isLB hF s₁
  refine ⟨σ, ?_⟩
  set xx := (snd T A).left z
  choose J hJ using fun χ : A.left ⟶ A.left => exists_chart D.P.isLB (χ xx)
  obtain ⟨(k : Fin 2 → D.P.L.ι), hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hz
  have hv : IsUnit (sval s (𝟙 A.left ≫ iota) xx J) := by
    refine H1.SectionArithmetic.isUnit_sval s (𝟙 A.left ≫ iota) xx hJ k ?_
    rw [Category.id_comp, hiota]; exact hk
  have hval : IsUnit (sval σ (𝟙 A.left) xx J) := by
    rw [hσ _ _ xx J hJ, sval_pullMulSec s iota u hu (𝟙 A.left) xx hJ]
    exact hv.mul (Units.isUnit _)
  have hm := (Good.mem hJ (D.famφB α) (𝟙 A.left))
  rw [sval] at hval
  erw [gs_eq (𝟙 A.left) xx _ hm] at hval
  refine TopologicalSpace.Opens.mem_iSup.2 ⟨fun k => J (𝟙 A.left ≫ D.famφB α k), ?_⟩
  exact (A.left.mem_basicOpen _ xx hm).2 hval

/- English proof (translation)
Introduce `R _ _ _ _ _ D α x hx`. Set `S` to `Spec (CommRingCat.of R)`. Set `tk : Spec (CommRingCat.of (IsLocalRing.ResidueField R)) ⟶ S` to `Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))`. Set `T : Over S` to `𝟙_ (Over S)`. Set `ρ : Over.mk (tk ≫ T.hom) ⟶ Over.mk T.hom` to `Over.homMk tk rfl`.

Choose the witnesses or unpack the hypotheses as in `⟨y, hy⟩ : ∃ y : (Over.mk (tk ≫ T.hom) ⊗ D.P.A).left, (snd _ D.P.A).left y = x := by`. Take `⟨p⟩ : Nonempty (Spec (CommRingCat.of (IsLocalRing.ResidueField R)))` from `inferInstance`. Take `⟨z, -, hz⟩` from `Scheme.Pullback.exists_preimage_pullback (f := tk ≫ T.hom) (g := D.P.A.hom) p x (by`. Rewrite using `[hx]`. Conclude with `IsLocalRing.PrimeSpectrum.comap_residue R p)`.

Conclude with `⟨z, hz⟩`. Establish `hg` using `GlobalTheory.T.exists_section_translateTensor_fibre_nonvanishing S D.P _ (tk ≫ T.hom) (ρ ≫ D.c α) y`. Rewrite `hg` using `[← whisker_eq_twistLB]`. Take `⟨sb, hsb⟩` from `hg`. Take `⟨s, hs⟩` from `(GlobalTheory.abelianSchemeLaws_all.2.secTwist S D.P 2 (by norm_num) R T.hom (D.c α)).2 sb`.

Establish `hz` using `mem_of_isPullSecLC D.P.L _ _ _ s sb hs y hsb`. Take `⟨σ, hσ⟩` from `transfer D α s _ hz`. Use `⟨σ, ?_⟩` and prove the remaining obligations. Establish `e : (snd T D.P.A).left ((ρ ▷ D.P.A).left y) = x`. Rewrite using `[← hy]`.

Establish `e'` using `congrArg (fun f => f.left.base y) (whiskerRight_snd ρ D.P.A)`. Conclude with `e'`. Rewrite `hσ` using `[e]`. Then use the resulting hypothesis.
-/
theorem exists_sec_nonzeroLocus_closedFibre : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R],
    IsAdicComplete (IsLocalRing.maximalIdeal R) R → ∀ (D : DegPre R) (α : D.X) (x : D.P.A.left),
    D.P.A.hom x = IsLocalRing.closedPoint R → ∃ σ : D.SecB 2 α, x ∈ nonzeroLocus σ := by
  intro R _ _ _ _ _ D α x hx
  let S := Spec (CommRingCat.of R)
  let tk : Spec (CommRingCat.of (IsLocalRing.ResidueField R)) ⟶ S :=
    Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))
  let T : Over S := 𝟙_ (Over S)
  let ρ : Over.mk (tk ≫ T.hom) ⟶ Over.mk T.hom := Over.homMk tk rfl
  obtain ⟨y, hy⟩ : ∃ y : (Over.mk (tk ≫ T.hom) ⊗ D.P.A).left, (snd _ D.P.A).left y = x := by
    obtain ⟨p⟩ : Nonempty (Spec (CommRingCat.of (IsLocalRing.ResidueField R))) := inferInstance
    obtain ⟨z, -, hz⟩ := Scheme.Pullback.exists_preimage_pullback (f := tk ≫ T.hom) (g := D.P.A.hom) p x (by
      rw [hx]; exact IsLocalRing.PrimeSpectrum.comap_residue R p)
    exact ⟨z, hz⟩
  have hg := GlobalTheory.T.exists_section_translateTensor_fibre_nonvanishing S D.P _ (tk ≫ T.hom) (ρ ≫ D.c α) y
  rw [← whisker_eq_twistLB] at hg
  obtain ⟨sb, hsb⟩ := hg
  obtain ⟨s, hs⟩ := (GlobalTheory.abelianSchemeLaws_all.2.secTwist S D.P 2 (by norm_num) R T.hom (D.c α)).2 sb
  have hz := mem_of_isPullSecLC D.P.L _ _ _ s sb hs y hsb
  obtain ⟨σ, hσ⟩ := transfer D α s _ hz
  refine ⟨σ, ?_⟩
  have e : (snd T D.P.A).left ((ρ ▷ D.P.A).left y) = x := by
    rw [← hy]
    have e' := congrArg (fun f => f.left.base y) (whiskerRight_snd ρ D.P.A)
    exact e'
  rwa [e] at hσ

end GlobalTheory.TwistGen
