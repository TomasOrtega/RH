import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.VRatioGtStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.OneCHyp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.JetLemmaStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.IsUnivChart
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LiftOUnique
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.SquareUnits

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace TwistUnit

open ReciprocityTheory.ChartRestriction.G.H1.SquareUnits TopologicalSpace

section Field

variable {S : Scheme.{0}} [IsLocallyNoetherian S] {K : Type} [Field K] (t : Spec (CommRingCat.of K) ⟶ S)

/- English proof (translation)
Take `⟨V, hpV, c, hc⟩` from `hsq S P (Over.mk t) x₁ x₂ (IsLocalRing.closedPoint K)`. Establish `hV : V = ⊤` using `eq_top_iff.2 fun q _ => by`. Use `spec_pt_eq q (IsLocalRing.closedPoint K)` as an intermediate fact. Rewrite using `[this]`. Conclude with `hpV`.

Substitute `hV` using the available equality. Take `⟨s, hs⟩` from `exists_sec_of_pullGen (Z := (Over.mk t ⊗ P.A).left) ((fst (Over.mk t) P.A).left ⁻¹ᵁ ⊤).ι c hc`. Set `e` to `IsOpenImmersion.lift ((fst (Over.mk t) P.A).left ⁻¹ᵁ ⊤).ι (𝟙 _) (by rintro _ ⟨q, rfl⟩; rw [Scheme.Opens.range_ι]; trivial)`. Establish `he : e ≫ ((fst (Over.mk t) P.A).left ⁻¹ᵁ ⊤).ι = 𝟙 _` using `IsOpenImmersion.lift_fac _ _ _`. Use `UnitAt.congr P.isLB ?_ ⟨SectionArithmetic.pullSec s e, fun J hJ => ?_⟩` and prove the remaining obligations.

Use `formEq_of_add fun U _ hh => ?_` and prove the remaining obligations. Simplify using `only [← Category.assoc, he, Category.id_comp]`. Rewrite using `[SectionArithmetic.sval_pullSec s e (𝟙 _) y hJ]`. Conclude with `hs _ y J hJ`.
-/
theorem unitAt_square (hsq : SquareSt) (P : PolAV S) (x₁ x₂ : Over.mk t ⟶ P.A) (y : (Over.mk t ⊗ P.A).left) :
    UnitAt P.L ![(translPt P.A (x₁ * x₂)).left, (snd (Over.mk t) P.A).left,
      (translPt P.A x₁).left, (translPt P.A x₂).left] ![1, 1, -1, -1] y := by
  obtain ⟨V, hpV, c, hc⟩ := hsq S P (Over.mk t) x₁ x₂ (IsLocalRing.closedPoint K)
  have hV : V = ⊤ := eq_top_iff.2 fun q _ => by
    have := spec_pt_eq q (IsLocalRing.closedPoint K)
    rw [this]; exact hpV
  subst hV
  obtain ⟨s, hs⟩ := exists_sec_of_pullGen (Z := (Over.mk t ⊗ P.A).left)
    ((fst (Over.mk t) P.A).left ⁻¹ᵁ ⊤).ι c hc
  let e := IsOpenImmersion.lift ((fst (Over.mk t) P.A).left ⁻¹ᵁ ⊤).ι (𝟙 _)
    (by rintro _ ⟨q, rfl⟩; rw [Scheme.Opens.range_ι]; trivial)
  have he : e ≫ ((fst (Over.mk t) P.A).left ⁻¹ᵁ ⊤).ι = 𝟙 _ :=
    IsOpenImmersion.lift_fac _ _ _
  refine UnitAt.congr P.isLB ?_ ⟨SectionArithmetic.pullSec s e, fun J hJ => ?_⟩
  · refine formEq_of_add fun U _ hh => ?_
    simp only [← Category.assoc, he, Category.id_comp]
  · rw [SectionArithmetic.sval_pullSec s e (𝟙 _) y hJ]
    exact hs _ y J hJ

/- English proof (translation)
The claim follows from `| 0 => by refine UnitAt.congr P.isLB (formEq_of_add fun U _ hh => ?_) (unitAt_square t hsq P b b y) simp [Fin.sum_univ_succ, pow_two] module | n + 1 => by refine UnitAt.congr P.isLB (formEq_of_add fun U _ hh => ?_) ((unitAt_iter hsq P b y n).mul (unitAt_square t hsq P (b ^ (n + 2 …`.
-/
theorem unitAt_iter (hsq : SquareSt) (P : PolAV S) (b : Over.mk t ⟶ P.A) (y : (Over.mk t ⊗ P.A).left) :
    ∀ n : ℕ, UnitAt P.L ![(translPt P.A (b ^ (n + 2))).left, (snd (Over.mk t) P.A).left,
      (translPt P.A b).left] ![1, (n : ℤ) + 1, -((n : ℤ) + 2)] y
  | 0 => by
    refine UnitAt.congr P.isLB (formEq_of_add fun U _ hh => ?_) (unitAt_square t hsq P b b y)
    simp [Fin.sum_univ_succ, pow_two]
    module
  | n + 1 => by
    refine UnitAt.congr P.isLB (formEq_of_add fun U _ hh => ?_)
      ((unitAt_iter hsq P b y n).mul (unitAt_square t hsq P (b ^ (n + 2)) b y))
    have e : b ^ (n + 2) * b = b ^ (n + 1 + 2) := by rw [← pow_succ]
    simp [Fin.sum_univ_succ, e]
    module

end Field

/- English proof (translation)
Establish `: IsIso (P.A.hom ⁻¹ᵁ ⊤).ι` using `inferInstanceAs (IsIso P.A.left.topIso.hom)`. Set `h : Y ⟶ (P.A.hom ⁻¹ᵁ ⊤).toScheme` to `g ≫ inv (P.A.hom ⁻¹ᵁ ⊤).ι`. Establish `hι : h ≫ (P.A.hom ⁻¹ᵁ ⊤).ι = g` using `by show (g ≫ inv (P.A.hom ⁻¹ᵁ ⊤).ι) ≫ (P.A.hom ⁻¹ᵁ ⊤).ι = g`. Rewrite using `[Category.assoc, IsIso.inv_hom_id, Category.comp_id]`. Take `⟨hgen, -⟩` from `hample _ P n hn`.

Take `⟨M, s, hcov⟩` from `hgen ⊤ (isAffineOpen_top _)`. Take `⟨i, hi⟩ : ∃ i, h y ∈ nonzeroLocus (s i)` from `Opens.mem_iSup.1 (by rw [hcov]; trivial)`. Take `⟨j, hj⟩` from `Opens.mem_iSup.1 hi`. Use `UnitAt.congr P.isLB (φ := fun _ : Fin n => h ≫ (P.A.hom ⁻¹ᵁ ⊤).ι) (ε := fun _ => 1) (formEq_of_add fun U _ hh => ?_) ⟨SectionArithmetic.pullSec (s i) h, fun J hJ => ?_⟩` and prove the remaining obligations. Simplify using `only [hι]`.

Simplify using the standard rewrite rules. Use `(congrArg IsUnit (SectionArithmetic.sval_pullSec (s i) h (𝟙 _) y hJ)).mpr ?_` and prove the remaining obligations. Rewrite using `[Category.id_comp]`. Conclude with `SectionArithmetic.isUnit_sval (s i) h y hJ j hj`.
-/
theorem unitAt_pow (hample : AmpleSt) {S : Scheme.{0}} [IsLocallyNoetherian S] [IsAffine S] (P : PolAV S) (n : ℕ)
    (hn : 4 ≤ n) {Y : Scheme.{0}} (g : Y ⟶ P.A.left) (y : Y) :
    UnitAt P.L (K := Fin 1) (fun _ => g) (fun _ => (n : ℤ)) y := by
  have : IsIso (P.A.hom ⁻¹ᵁ ⊤).ι := inferInstanceAs (IsIso P.A.left.topIso.hom)
  let h : Y ⟶ (P.A.hom ⁻¹ᵁ ⊤).toScheme := g ≫ inv (P.A.hom ⁻¹ᵁ ⊤).ι
  have hι : h ≫ (P.A.hom ⁻¹ᵁ ⊤).ι = g := by
    show (g ≫ inv (P.A.hom ⁻¹ᵁ ⊤).ι) ≫ (P.A.hom ⁻¹ᵁ ⊤).ι = g
    rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  obtain ⟨hgen, -⟩ := hample _ P n hn
  obtain ⟨M, s, hcov⟩ := hgen ⊤ (isAffineOpen_top _)
  obtain ⟨i, hi⟩ : ∃ i, h y ∈ nonzeroLocus (s i) := Opens.mem_iSup.1 (by rw [hcov]; trivial)
  obtain ⟨j, hj⟩ := Opens.mem_iSup.1 hi
  refine UnitAt.congr P.isLB (φ := fun _ : Fin n => h ≫ (P.A.hom ⁻¹ᵁ ⊤).ι) (ε := fun _ => 1)
    (formEq_of_add fun U _ hh => ?_) ⟨SectionArithmetic.pullSec (s i) h, fun J hJ => ?_⟩
  · simp only [hι]
    simp
  · refine (congrArg IsUnit (SectionArithmetic.sval_pullSec (s i) h (𝟙 _) y hJ)).mpr ?_
    rw [Category.id_comp]
    exact SectionArithmetic.isUnit_sval (s i) h y hJ j hj

/- English proof (translation)
Assemble the required witnesses or components as `⟨SectionArithmetic.pullSec (Geo.Tor.genSec G hG) h, fun J hJ => by rw [SectionArithmetic.sval_pullSec _ h (𝟙 _) y hJ, sval_genSec G hG _ y hJ] exact Units.isUnit _⟩`.
-/
theorem unitAt_gen {X Y W : Scheme.{0}} {L : LB X} {I : Type} [Fintype I] {φ : I → (W ⟶ X)} {ε : I → ℤ}
    (G : LB.Gen (LB.LinComb L φ ε)) (hG : G.IsGen) (h : Y ⟶ W) (y : Y) :
    UnitAt L (fun i => h ≫ φ i) ε y :=
  ⟨SectionArithmetic.pullSec (Geo.Tor.genSec G hG) h, fun J hJ => by
    rw [SectionArithmetic.sval_pullSec _ h (𝟙 _) y hJ, sval_genSec G hG _ y hJ]
    exact Units.isUnit _⟩

/- English proof (translation)
Use `choose J' hJ' using fun ψ : Y ⟶ X => exists_chart hL (ψ (r z))`. Establish `hG : Good L (r z) J'` using `hJ'`. Establish `hm` using `hG.mem φ (𝟙 Y)`. Establish `hu` using `hs J' hG`. Establish `hu'` using `(congrArg IsUnit (gs_eq (𝟙 Y) (r z) _ hm (s.f fun i => J' (𝟙 Y ≫ φ i)))).mp hu`.

Conclude with `SectionArithmetic.isUnit_sval s r z hJ (fun i => J' (𝟙 Y ≫ φ i)) ((Y.mem_basicOpen _ (r z) hm).2 hu')`.
-/
theorem isUnit_sval_of {X Y Z : Scheme.{0}} {L : LB X} (hL : L.IsLB) {I : Type} [Fintype I] {φ : I → (Y ⟶ X)}
    {ε : I → ℤ} (s : LB.Sec (LB.LinComb L φ ε)) (r : Z ⟶ Y) (z : Z)
    (hs : ∀ J, Good L (r z) J → IsUnit (sval s (𝟙 Y) (r z) J)) (J : (Z ⟶ X) → L.ι) (hJ : Good L z J) :
    IsUnit (sval s r z J) := by
  choose J' hJ' using fun ψ : Y ⟶ X => exists_chart hL (ψ (r z))
  have hG : Good L (r z) J' := hJ'
  have hm := hG.mem φ (𝟙 Y)
  have hu := hs J' hG
  have hu' := (congrArg IsUnit (gs_eq (𝟙 Y) (r z) _ hm (s.f fun i => J' (𝟙 Y ≫ φ i)))).mp hu
  exact SectionArithmetic.isUnit_sval s r z hJ (fun i => J' (𝟙 Y ≫ φ i)) ((Y.mem_basicOpen _ (r z) hm).2 hu')

/- English proof (translation)
Take `⟨j, hj⟩` from `exists_chart_top L hL φ ε`. Establish `le : (⊤ : (Spec (CommRingCat.of R)).Opens) ≤ LB.wchart L φ j` using `hj.ge`. Use `⟨((Spec (CommRingCat.of R)).presheaf.map (homOfLE le).op).hom ((show Γ(Spec (CommRingCat.of R), LB.wchart L φ j) from s.f j) * (show Γ(Spec (CommRingCat.of R), LB.wchart L φ j)ˣ from G.s j)⁻¹.val), fun Z r z J hJ => ?_⟩` and prove the remaining obligations. Establish `hz : r z ∈ LB.wchart L φ j` using `le trivial`. Rewrite using `[gs_res r z le trivial, gs_mul r z _ hz, gs_unit r z _ hz, map_inv]`.

Establish `e₁ : sval s r z J = _` using `sec_trans s r z (hJ.mem φ r) hz`. Establish `e₂ : val G r z J = _` using `gen_trans hG r z (hJ.mem φ r) hz`. Rewrite using `[e₁, e₂, Units.val_mul]`. Use `Units.inv_mul (gm r z (LB.wchart L φ j) (G.s j))` as an intermediate fact. Take the linear combination `(-((trF φ ε r z (fun k => J (r ≫ φ k)) j).val * gs r z (LB.wchart L φ j) (s.f j))) * this`.
-/
theorem exists_ratio_local {R : Type} [CommRing R] [IsLocalRing R] {X : Scheme.{0}} {L : LB X} (hL : L.IsLB)
    {I : Type} [Fintype I] {φ : I → (Spec (CommRingCat.of R) ⟶ X)} {ε : I → ℤ}
    (s : LB.Sec (LB.LinComb L φ ε)) (G : LB.Gen (LB.LinComb L φ ε)) (hG : G.IsGen) :
    ∃ x : Γ(Spec (CommRingCat.of R), ⊤), ∀ (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of R)) (z : Z) (J),
      Good L z J → sval s r z J = gs r z ⊤ x * (val G r z J).val := by
  obtain ⟨j, hj⟩ := exists_chart_top L hL φ ε
  have le : (⊤ : (Spec (CommRingCat.of R)).Opens) ≤ LB.wchart L φ j := hj.ge
  refine ⟨((Spec (CommRingCat.of R)).presheaf.map (homOfLE le).op).hom
    ((show Γ(Spec (CommRingCat.of R), LB.wchart L φ j) from s.f j) *
      (show Γ(Spec (CommRingCat.of R), LB.wchart L φ j)ˣ from G.s j)⁻¹.val), fun Z r z J hJ => ?_⟩
  have hz : r z ∈ LB.wchart L φ j := le trivial
  rw [gs_res r z le trivial, gs_mul r z _ hz, gs_unit r z _ hz, map_inv]
  have e₁ : sval s r z J = _ := sec_trans s r z (hJ.mem φ r) hz
  have e₂ : val G r z J = _ := gen_trans hG r z (hJ.mem φ r) hz
  rw [e₁, e₂, Units.val_mul]
  have := Units.inv_mul (gm r z (LB.wchart L φ j) (G.s j))
  linear_combination (-((trF φ ε r z (fun k => J (r ≫ φ k)) j).val * gs r z (LB.wchart L φ j) (s.f j))) * this

/- English proof (translation)
Take `⟨-, -, hsurj, -, -⟩` from `hmul S P n hn`. Set `W` to `pullback (mulA P.A n).left c.left`. Take `⟨w, -⟩` from `Surjective.surj (f := pullback.snd (mulA P.A n).left c.left) (IsLocalRing.closedPoint κ)`. Take `⟨g, hg⟩` from `Spec.map_surjective (R := CommRingCat.of κ) (S := W.residueField w) (W.fromSpecResidueField w ≫ pullback.snd (mulA P.A n).left c.left)`. Use `⟨W.residueField w, inferInstance, g.hom, W.fromSpecResidueField w ≫ pullback.fst (mulA P.A n).left c.left, ?_⟩` and prove the remaining obligations.

Rewrite using `[Category.assoc, pullback.condition, ← Category.assoc, ← hg]`. Both sides reduce to the same expression.
-/
theorem exists_div_ext (hmul : MulNSt) {S : Scheme.{0}} [IsLocallyNoetherian S] (P : PolAV S) (n : ℕ) (hn : 1 ≤ n)
    {κ : Type} [Field κ] (t : Spec (CommRingCat.of κ) ⟶ S) (c : Over.mk t ⟶ P.A) :
    ∃ (K : Type) (_ : Field K) (g : κ →+* K) (b : Spec (CommRingCat.of K) ⟶ P.A.left),
      b ≫ (mulA P.A n).left = Spec.map (CommRingCat.ofHom g) ≫ c.left := by
  obtain ⟨-, -, hsurj, -, -⟩ := hmul S P n hn
  let W := pullback (mulA P.A n).left c.left
  obtain ⟨w, -⟩ := Surjective.surj (f := pullback.snd (mulA P.A n).left c.left) (IsLocalRing.closedPoint κ)
  obtain ⟨g, hg⟩ := Spec.map_surjective (R := CommRingCat.of κ) (S := W.residueField w)
    (W.fromSpecResidueField w ≫ pullback.snd (mulA P.A n).left c.left)
  refine ⟨W.residueField w, inferInstance, g.hom, W.fromSpecResidueField w ≫ pullback.fst (mulA P.A n).left c.left, ?_⟩
  rw [Category.assoc, pullback.condition, ← Category.assoc, ← hg]
  rfl

/- English proof (translation)
Establish `hL` using `D.P.isLB`. Take `⟨K, _, g₀, b₀, hb₀⟩` from `exists_div_ext hLaws.mulN D.P k (by omega) (Spec.map (CommRingCat.ofHom ((residue O).comp f))) (SectionScalarValuation.cQ D _ χ)`. Set `g : O →+* K` to `g₀.comp (residue O)`. Establish `hg : IsLocalHom g` using `inferInstance`. Establish `hgf : IsLocalHom (g.comp f)` using `inferInstance`.

Set `T : Over (Spec (CommRingCat.of R))` to `Over.mk (Spec.map (CommRingCat.ofHom (g.comp f)))`. Set `τ₀ : T ⟶ Over.mk (Spec.map (CommRingCat.ofHom ((residue O).comp f)))` to `Over.homMk (Spec.map (CommRingCat.ofHom g₀)) (by show Spec.map (CommRingCat.ofHom g₀) ≫ Spec.map (CommRingCat.ofHom ((residue O).comp f)) = Spec.map (CommRingCat.ofHom (g.comp f))`. Rewrite using `[← Spec.map_comp]`. Use the proof step `rfl)`. Set `τ : T ⟶ Over.mk (Spec.map (CommRingCat.ofHom f))` to `Over.homMk (Spec.map (CommRingCat.ofHom g)) (by show Spec.map (CommRingCat.ofHom g) ≫ Spec.map (CommRingCat.ofHom f) = Spec.map (CommRingCat.ofHom (g.comp f))`.

Rewrite using `[← Spec.map_comp]`. Use the proof step `rfl)`. Establish `hb₁ : b₀ ≫ (mulA D.P.A k).left = (SectionScalarValuation.cQ D T χ).left` using `hb₀.trans (congrArg (fun q => q.left) (SectionScalarValuation.comp_cQ D τ₀ χ))`. Establish `hw : b₀ ≫ D.P.A.hom = T.hom`. Rewrite using `[← Over.w (mulA D.P.A k), ← Category.assoc, hb₁, Over.w]`.

Set `b : T ⟶ D.P.A` to `Over.homMk b₀ hw`. Establish `hb : b ^ k = SectionScalarValuation.cQ D T χ`. Establish `e : b ^ k = b ≫ mulA D.P.A k` using `(congrArg (· ^ k) (Category.comp_id b).symm).trans (MonObj.comp_pow (𝟙 D.P.A) k b).symm`. Rewrite using `[e]`. Conclude with `Over.OverMorphism.ext hb₁`.

Set `ρ : T ⟶ T ⊗ D.P.A` to `lift (𝟙 T) (τ ≫ m)`. Set `z : Spec (CommRingCat.of K)` to `closedPoint K`. Take `⟨G, hG⟩` from `exists_gen_of_local D.P.L hL (K := Fin 2) ![(SectionScalarValuation.cQ D T χ).left, (1 : T ⟶ D.P.A).left] ![-1, 1]`. Establish `u₁` using `unitAt_iter (Spec.map (CommRingCat.ofHom (g.comp f))) hLaws.square D.P b (ρ.left z) (k - 2)`. Establish `u₂` using `unitAt_pow hLaws.ample D.P k hk (translPt D.P.A b).left (ρ.left z)`.

Establish `u₃` using `unitAt_gen G hG (fst T D.P.A).left (ρ.left z)`. Establish `hk2 : k - 2 + 2 = k` using `by omega`. Establish `hk2' : ((k - 2 : ℕ) : ℤ) = (k : ℤ) - 2` using `by omega`. Rewrite `u₁` using `[hk2, hb, hk2']`. Establish `q₁ : translPt D.P.A (SectionScalarValuation.cQ D T χ) = snd T D.P.A * SectionScalarValuation.cQ D (T ⊗ D.P.A) χ`.

Rewrite using `[mul_comm, ← SectionScalarValuation.comp_cQ D (fst T D.P.A)]`. Both sides reduce to the same expression. Establish `q₂ : (fst T D.P.A).left ≫ (SectionScalarValuation.cQ D T χ).left = (SectionScalarValuation.cQ D (T ⊗ D.P.A) χ).left` using `congrArg (fun q => q.left) (SectionScalarValuation.comp_cQ D (fst T D.P.A) χ)`. Establish `q₃ : (fst T D.P.A).left ≫ (1 : T ⟶ D.P.A).left = (1 : T ⊗ D.P.A ⟶ D.P.A).left` using `congrArg (fun q : T ⊗ D.P.A ⟶ D.P.A => q.left) (MonObj.comp_one (M := D.P.A) (fst T D.P.A))`. Choose the witnesses or unpack the hypotheses as in `⟨s', hs'⟩ : UnitAt D.P.L (fun i => (snd T D.P.A).left ≫ DegPre.famφB D χ i) (DegPre.famε k) (ρ.left z) := by`.

Use `UnitAt.congr hL (fun U _ h => ?_) ((u₁.mul u₂).mul u₃)` and prove the remaining obligations. Use `Eq.trans ?_ (SectionScalarValuation.prod_famB D (snd T D.P.A) χ k h).symm` and prove the remaining obligations. Rewrite using `[← q₁, ← q₂, ← q₃, Fintype.prod_sum_type, Fintype.prod_sum_type, Fin.prod_univ_three, Fin.prod_univ_one, Fin.prod_univ_two]`. Use `show h (translPt D.P.A (SectionScalarValuation.cQ D T χ)).left ^ (1 : ℤ) * h (snd T D.P.A).left ^ ((k : ℤ) - 2 + 1) * h (translPt D.P.A b).left ^ (-((k : ℤ) - 2 + 2)) * h (translPt D.P.A b).left ^ (k : ℤ) * (h ((fst T D.P.A).left ≫ (SectionScalarValuation.cQ D T χ).left) ^ (-1 : …`. Apply `Additive.ofMul.injective` to reduce the goal to its premises.

Simplify using `only [ofMul_mul, ofMul_inv, ofMul_zpow]`. Use `module`. Use `choose J hJ using fun ψ : Spec (CommRingCat.of K) ⟶ D.P.A.left => exists_chart hL (ψ z)`. Establish `hJ' : Good D.P.L z J` using `hJ`. Establish `hu` using `isUnit_sval_of hL s' ρ.left z hs' J hJ'`.

Take `⟨n, r, σ, hσ⟩` from `hTW R D k (by omega) χ K (g.comp f) hgf s'`. Establish `e` using `SectionScalarValuation.sval_lin (fun l => (fst T D.P.A).left.appTop.hom (r l)) (fun l => DVR.pullSec D.P.L _ _ (σ l) (snd T D.P.A).left) (fun j => hσ j) ρ.left z hJ'`. Rewrite `hu` using `[e]`. Take `⟨l, -, hl⟩` from `IsLocalRing.exists_of_isUnit_sum hu`. Use `⟨σ l, K, inferInstance, g, hg, z, J, hJ', ?_⟩` and prove the remaining obligations.

Establish `hl'` using `isUnit_of_mul_isUnit_right hl`. Rewrite `hl'` using `[SectionScalarValuation.sval_pullSec _ _ _ _ _ z hJ', ← Over.comp_left, lift_snd]`. Conclude with `hl'`.
-/
theorem exists_unit_secB (hLaws : Laws) (hTW : TwistBCSpanStatement) {R : Type} [CommRing R] [IsDomain R]
    [IsLocalRing R] [IsNoetherianRing R] (D : DegPre R) (k : ℕ) (hk : 4 ≤ k) (χ : D.X)
    {O : Type} [CommRing O] [IsLocalRing O] (f : R →+* O) [IsLocalHom f]
    (m : Over.mk (Spec.map (CommRingCat.ofHom f)) ⟶ D.P.A) :
    ∃ (σ : D.SecB k χ) (K : Type) (_ : Field K) (g : O →+* K), IsLocalHom g ∧
      ∃ (z : Spec (CommRingCat.of K)) (J : (Spec (CommRingCat.of K) ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J ∧
        IsUnit (sval σ (Spec.map (CommRingCat.ofHom g) ≫ m.left) z J) := by
  have hL := D.P.isLB
  obtain ⟨K, _, g₀, b₀, hb₀⟩ := exists_div_ext hLaws.mulN D.P k (by omega)
    (Spec.map (CommRingCat.ofHom ((residue O).comp f))) (SectionScalarValuation.cQ D _ χ)
  let g : O →+* K := g₀.comp (residue O)
  have hg : IsLocalHom g := inferInstance
  have hgf : IsLocalHom (g.comp f) := inferInstance
  let T : Over (Spec (CommRingCat.of R)) := Over.mk (Spec.map (CommRingCat.ofHom (g.comp f)))
  let τ₀ : T ⟶ Over.mk (Spec.map (CommRingCat.ofHom ((residue O).comp f))) :=
    Over.homMk (Spec.map (CommRingCat.ofHom g₀)) (by
      show Spec.map (CommRingCat.ofHom g₀) ≫ Spec.map (CommRingCat.ofHom ((residue O).comp f)) =
        Spec.map (CommRingCat.ofHom (g.comp f))
      rw [← Spec.map_comp]; rfl)
  let τ : T ⟶ Over.mk (Spec.map (CommRingCat.ofHom f)) :=
    Over.homMk (Spec.map (CommRingCat.ofHom g)) (by
      show Spec.map (CommRingCat.ofHom g) ≫ Spec.map (CommRingCat.ofHom f) =
        Spec.map (CommRingCat.ofHom (g.comp f))
      rw [← Spec.map_comp]; rfl)
  have hb₁ : b₀ ≫ (mulA D.P.A k).left = (SectionScalarValuation.cQ D T χ).left :=
    hb₀.trans (congrArg (fun q => q.left) (SectionScalarValuation.comp_cQ D τ₀ χ))
  have hw : b₀ ≫ D.P.A.hom = T.hom := by
    rw [← Over.w (mulA D.P.A k), ← Category.assoc, hb₁, Over.w]
  let b : T ⟶ D.P.A := Over.homMk b₀ hw
  have hb : b ^ k = SectionScalarValuation.cQ D T χ := by
    have e : b ^ k = b ≫ mulA D.P.A k :=
      (congrArg (· ^ k) (Category.comp_id b).symm).trans (MonObj.comp_pow (𝟙 D.P.A) k b).symm
    rw [e]
    exact Over.OverMorphism.ext hb₁
  let ρ : T ⟶ T ⊗ D.P.A := lift (𝟙 T) (τ ≫ m)
  let z : Spec (CommRingCat.of K) := closedPoint K
  obtain ⟨G, hG⟩ := exists_gen_of_local D.P.L hL (K := Fin 2)
    ![(SectionScalarValuation.cQ D T χ).left, (1 : T ⟶ D.P.A).left] ![-1, 1]
  have u₁ := unitAt_iter (Spec.map (CommRingCat.ofHom (g.comp f))) hLaws.square D.P b (ρ.left z) (k - 2)
  have u₂ := unitAt_pow hLaws.ample D.P k hk (translPt D.P.A b).left (ρ.left z)
  have u₃ := unitAt_gen G hG (fst T D.P.A).left (ρ.left z)
  have hk2 : k - 2 + 2 = k := by omega
  have hk2' : ((k - 2 : ℕ) : ℤ) = (k : ℤ) - 2 := by omega
  rw [hk2, hb, hk2'] at u₁
  have q₁ : translPt D.P.A (SectionScalarValuation.cQ D T χ) = snd T D.P.A * SectionScalarValuation.cQ D (T ⊗ D.P.A) χ := by
    rw [mul_comm, ← SectionScalarValuation.comp_cQ D (fst T D.P.A)]; rfl
  have q₂ : (fst T D.P.A).left ≫ (SectionScalarValuation.cQ D T χ).left = (SectionScalarValuation.cQ D (T ⊗ D.P.A) χ).left :=
    congrArg (fun q => q.left) (SectionScalarValuation.comp_cQ D (fst T D.P.A) χ)
  have q₃ : (fst T D.P.A).left ≫ (1 : T ⟶ D.P.A).left = (1 : T ⊗ D.P.A ⟶ D.P.A).left :=
    congrArg (fun q : T ⊗ D.P.A ⟶ D.P.A => q.left) (MonObj.comp_one (M := D.P.A) (fst T D.P.A))
  obtain ⟨s', hs'⟩ : UnitAt D.P.L (fun i => (snd T D.P.A).left ≫ DegPre.famφB D χ i) (DegPre.famε k) (ρ.left z) := by
    refine UnitAt.congr hL (fun U _ h => ?_) ((u₁.mul u₂).mul u₃)
    refine Eq.trans ?_ (SectionScalarValuation.prod_famB D (snd T D.P.A) χ k h).symm
    rw [← q₁, ← q₂, ← q₃, Fintype.prod_sum_type, Fintype.prod_sum_type, Fin.prod_univ_three, Fin.prod_univ_one,
      Fin.prod_univ_two]
    show h (translPt D.P.A (SectionScalarValuation.cQ D T χ)).left ^ (1 : ℤ) * h (snd T D.P.A).left ^ ((k : ℤ) - 2 + 1) *
      h (translPt D.P.A b).left ^ (-((k : ℤ) - 2 + 2)) * h (translPt D.P.A b).left ^ (k : ℤ) *
      (h ((fst T D.P.A).left ≫ (SectionScalarValuation.cQ D T χ).left) ^ (-1 : ℤ) *
        h ((fst T D.P.A).left ≫ (1 : T ⟶ D.P.A).left) ^ (1 : ℤ)) = _
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
    module
  choose J hJ using fun ψ : Spec (CommRingCat.of K) ⟶ D.P.A.left => exists_chart hL (ψ z)
  have hJ' : Good D.P.L z J := hJ
  have hu := isUnit_sval_of hL s' ρ.left z hs' J hJ'
  obtain ⟨n, r, σ, hσ⟩ := hTW R D k (by omega) χ K (g.comp f) hgf s'
  have e := SectionScalarValuation.sval_lin (fun l => (fst T D.P.A).left.appTop.hom (r l))
      (fun l => DVR.pullSec D.P.L _ _ (σ l) (snd T D.P.A).left) (fun j => hσ j) ρ.left z hJ'
  rw [e] at hu
  obtain ⟨l, -, hl⟩ := IsLocalRing.exists_of_isUnit_sum hu
  refine ⟨σ l, K, inferInstance, g, hg, z, J, hJ', ?_⟩
  have hl' := isUnit_of_mul_isUnit_right hl
  rw [SectionScalarValuation.sval_pullSec _ _ _ _ _ z hJ', ← Over.comp_left, lift_snd] at hl'
  exact hl'

end TwistUnit

open TwistUnit in

/- English proof (translation)
Introduce `hLaws hTW V _ _ _ ϖ hϖ D Q _ F _ _ _ v hv k hk χ m`. Establish `hL` using `D.toPre.P.isLB`. Take `⟨σ, K, _, g, hg, z₀, J₀, hJ₀, hu⟩` from `exists_unit_secB hLaws hTW D.toPre k hk χ (TWO.fO v hϖ hv) m`. Establish `hformF : FormEq (fun i => (DegPre.prB D.toPre F).left ≫ D.toPre.famφB χ i) (DegPre.famε k) (DegPre.famφ D.toPre F χ) (DegPre.famε k)` using `fun U _ g => Finset.prod_congr rfl fun i _ => by rw [GC.famφ_eq]`. Take `⟨s, hs⟩` from `exists_sec hL hformF (SectionArithmetic.pullSec σ (DegPre.prB D.toPre F).left)`.

Establish `hs' : ∀ (Z : Scheme.{0}) (ρ : Z ⟶ (DegPre.BF D.toPre F).left) (z : Z) (J), Good D.toPre.P.L z J → sval s ρ z J = sval σ (ρ ≫ (DegPre.prB D.toPre F).left) z J` using `fun Z ρ z J hJ => (hs Z ρ z J hJ).trans (SectionArithmetic.sval_pullSec _ _ ρ z hJ)`. Take `⟨G₀, hG₀⟩` from `exists_gen_of_local (V := TWO.Ov v) D.toPre.P.L hL (fun i => m.left ≫ DegPre.famφB D.toPre χ i) (DegPre.famε k)`. Take `⟨x₀, hx₀⟩` from `exists_ratio_local (R := TWO.Ov v) hL (SectionArithmetic.pullSec σ m.left) G₀ hG₀`. Establish `key : ∀ {E : Type} [CommRing E] (φ : TWO.Ov v →+* E) (z : Spec (CommRingCat.of E)), gs (Spec.map (CommRingCat.ofHom φ)) z ⊤ x₀ = gs (𝟙 _) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of E)).inv.hom (φ ((Scheme.ΓSpecIso (CommRingCat.of (TWO.Ov v))).hom.hom x₀)))` using `fun φ z => by`. Establish `e` using `gs_pull (𝟙 _) (Spec.map (CommRingCat.ofHom φ)) z ⊤ trivial x₀`.

Rewrite `e` using `[Category.id_comp]`. Conclude with `e.symm.trans (congrArg (gs (𝟙 _) z ⊤) (TWM.appTop_specMap (CommRingCat.ofHom φ) x₀))`. Establish `hx₀u : IsUnit ((Scheme.ΓSpecIso (CommRingCat.of (TWO.Ov v))).hom.hom x₀)`. Establish `e` using `hx₀ _ (Spec.map (CommRingCat.ofHom g)) z₀ J₀ hJ₀`. Rewrite `e` using `[SectionArithmetic.sval_pullSec _ _ _ z₀ hJ₀]`.

Establish `h₁` using `isUnit_of_mul_isUnit_left ((congrArg IsUnit e).mp hu)`. Rewrite `h₁` using `[key]`. Use `isUnit_of_map_unit g _ (IsUnit.mk0 _ fun h0 => ?_)` and prove the remaining obligations. Rewrite `h₁` using `[h0, map_zero, gs_eq _ _ ⊤ trivial, map_zero, map_zero]`. Conclude with `not_isUnit_zero h₁`.

Use `⟨s, ⟨1, fun _ => 1, fun _ => σ, fun _ => s, fun _ => ?_, fun _ => ?_, fun j => ?_⟩, G₀, hG₀, TWM.ιr (v := v) x₀, ?_, fun z J hJ => ?_⟩` and prove the remaining obligations. Conclude with `SectionScalarValuation.secScal_of_sval hL fun y J hJ => (hs' _ (𝟙 _) y J hJ).symm`. Rewrite using `[AddValuation.map_one]`. Conclude with `le_rfl`. Rewrite using `[Fin.sum_univ_one, DVR.constBF_eq, map_one]`.

Simplify using `[resTop]`. Conclude with `TWO.v_unit v hx₀u.unit`. Rewrite using `[hs' _ _ z J hJ, ← Over.comp_left, lift_snd, Over.comp_left, ← SectionArithmetic.sval_pullSec σ m.left _ z hJ]`. Conclude with `(hx₀ _ _ z J hJ).trans (congrArg (· * _) (key (algebraMap (TWO.Ov v) F) z))`.
-/
theorem exists_integral_section_unit_at : Laws → TwistBCSpanStatement → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V) (hϖ : Irreducible ϖ) (D : DegData V (maximalIdeal V)) (Q : D.toPre.X → ℤ), QForm.IsQ D.toPre ϖ Q → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] (v : AddValuation F (WithTop ℚ)) (hv : ValOver ϖ F v) (k : ℕ), 4 ≤ k → ∀ (χ : D.toPre.X) (m : TWM.TO hϖ hv ⟶ D.toPre.P.A), ∃ s : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F χ) (DegPre.famε k)), VGe D F v k χ s 0 ∧ (∃ G₀ : LB.Gen (LB.LinComb D.toPre.P.L (fun i => (m).left ≫ DegPre.famφB D.toPre (χ) i) (DegPre.famε (k))), G₀.IsGen ∧ ∃ x : F, v x = ((0 : ℚ) : WithTop ℚ) ∧ ∀ (z : (TF (R := V) F).left) (J), Good D.toPre.P.L z J → sval (s) (lift (𝟙 (TF (R := V) F)) (TWM.ιS hϖ hv ≫ m)).left z J = gs (𝟙 _) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom x) * (val G₀ (TWM.ιS hϖ hv).left z J).val) := by
  intro hLaws hTW V _ _ _ ϖ hϖ D Q _ F _ _ _ v hv k hk χ m
  have hL := D.toPre.P.isLB
  obtain ⟨σ, K, _, g, hg, z₀, J₀, hJ₀, hu⟩ := exists_unit_secB hLaws hTW D.toPre k hk χ (TWO.fO v hϖ hv) m
  have hformF : FormEq (fun i => (DegPre.prB D.toPre F).left ≫ D.toPre.famφB χ i) (DegPre.famε k)
      (DegPre.famφ D.toPre F χ) (DegPre.famε k) := fun U _ g =>
    Finset.prod_congr rfl fun i _ => by rw [GC.famφ_eq]
  obtain ⟨s, hs⟩ := exists_sec hL hformF (SectionArithmetic.pullSec σ (DegPre.prB D.toPre F).left)
  have hs' : ∀ (Z : Scheme.{0}) (ρ : Z ⟶ (DegPre.BF D.toPre F).left) (z : Z) (J), Good D.toPre.P.L z J →
      sval s ρ z J = sval σ (ρ ≫ (DegPre.prB D.toPre F).left) z J := fun Z ρ z J hJ =>
    (hs Z ρ z J hJ).trans (SectionArithmetic.sval_pullSec _ _ ρ z hJ)
  obtain ⟨G₀, hG₀⟩ := exists_gen_of_local (V := TWO.Ov v) D.toPre.P.L hL
    (fun i => m.left ≫ DegPre.famφB D.toPre χ i) (DegPre.famε k)
  obtain ⟨x₀, hx₀⟩ := exists_ratio_local (R := TWO.Ov v) hL (SectionArithmetic.pullSec σ m.left) G₀ hG₀
  have key : ∀ {E : Type} [CommRing E] (φ : TWO.Ov v →+* E) (z : Spec (CommRingCat.of E)),
      gs (Spec.map (CommRingCat.ofHom φ)) z ⊤ x₀ = gs (𝟙 _) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of E)).inv.hom
        (φ ((Scheme.ΓSpecIso (CommRingCat.of (TWO.Ov v))).hom.hom x₀))) := fun φ z => by
    have e := gs_pull (𝟙 _) (Spec.map (CommRingCat.ofHom φ)) z ⊤ trivial x₀
    rw [Category.id_comp] at e
    exact e.symm.trans (congrArg (gs (𝟙 _) z ⊤) (TWM.appTop_specMap (CommRingCat.ofHom φ) x₀))
  have hx₀u : IsUnit ((Scheme.ΓSpecIso (CommRingCat.of (TWO.Ov v))).hom.hom x₀) := by
    have e := hx₀ _ (Spec.map (CommRingCat.ofHom g)) z₀ J₀ hJ₀
    rw [SectionArithmetic.sval_pullSec _ _ _ z₀ hJ₀] at e
    have h₁ := isUnit_of_mul_isUnit_left ((congrArg IsUnit e).mp hu)
    rw [key] at h₁
    refine isUnit_of_map_unit g _ (IsUnit.mk0 _ fun h0 => ?_)
    rw [h0, map_zero, gs_eq _ _ ⊤ trivial, map_zero, map_zero] at h₁
    exact not_isUnit_zero h₁
  refine ⟨s, ⟨1, fun _ => 1, fun _ => σ, fun _ => s, fun _ => ?_, fun _ => ?_, fun j => ?_⟩, G₀, hG₀,
    TWM.ιr (v := v) x₀, ?_, fun z J hJ => ?_⟩
  · exact SectionScalarValuation.secScal_of_sval hL fun y J hJ => (hs' _ (𝟙 _) y J hJ).symm
  · rw [AddValuation.map_one]; exact le_rfl
  · rw [Fin.sum_univ_one, DVR.constBF_eq, map_one]
    simp [resTop]
  · exact TWO.v_unit v hx₀u.unit
  · rw [hs' _ _ z J hJ, ← Over.comp_left, lift_snd, Over.comp_left, ← SectionArithmetic.sval_pullSec σ m.left _ z hJ]
    exact (hx₀ _ _ z J hJ).trans (congrArg (· * _) (key (algebraMap (TWO.Ov v) F) z))

end GlobalTheory
