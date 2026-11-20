import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.SectionArithmetic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TopologicalSpace Opposite

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.H1.SquareUnits

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic

variable {X Y Z : Scheme.{0}}

def UnitAt (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ) (y : Y) : Prop :=
  ∃ s : LB.Sec (LB.LinComb L φ ε), ∀ J, Good L y J → IsUnit (sval s (𝟙 Y) y J)

variable {L : LB X} {K K' : Type} [Fintype K] [Fintype K']

/- English proof (translation)
Take `⟨s, hs⟩` from `h`. Take `⟨s', hs'⟩` from `h'`. Conclude with `⟨mulSec s s', fun J hJ => by rw [sval_mulSec s s' _ y hJ]; exact (hs J hJ).mul (hs' J hJ)⟩`.
-/
theorem UnitAt.mul {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ} {y : Y}
    (h : UnitAt L φ ε y) (h' : UnitAt L φ' ε' y) : UnitAt L (Sum.elim φ φ') (Sum.elim ε ε') y := by
  obtain ⟨s, hs⟩ := h
  obtain ⟨s', hs'⟩ := h'
  exact ⟨mulSec s s', fun J hJ => by rw [sval_mulSec s s' _ y hJ]; exact (hs J hJ).mul (hs' J hJ)⟩

/- English proof (translation)
Take `⟨s, hs⟩` from `h`. Take `⟨s', hs'⟩` from `exists_sec hL hf s`. Conclude with `⟨s', fun J hJ => by rw [hs' Y (𝟙 Y) y J hJ]; exact hs J hJ⟩`.
-/
theorem UnitAt.congr (hL : L.IsLB) {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ} {y : Y}
    (hf : FormEq φ ε φ' ε') (h : UnitAt L φ ε y) : UnitAt L φ' ε' y := by
  obtain ⟨s, hs⟩ := h
  obtain ⟨s', hs'⟩ := exists_sec hL hf s
  exact ⟨s', fun J hJ => by rw [hs' Y (𝟙 Y) y J hJ]; exact hs J hJ⟩

/- English proof (translation)
Introduce `U _ h`. Apply `Additive.ofMul.injective` to reduce the goal to its premises. Simplify `H (Additive U) (fun ψ => Additive.ofMul (h ψ))` using `only [ofMul_prod, ofMul_zpow]`.
-/
theorem formEq_of_add {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}
    (H : ∀ (U : Type) [AddCommGroup U] (h : (Y ⟶ X) → U), ∑ k, ε k • h (φ k) = ∑ k, ε' k • h (φ' k)) :
    FormEq φ ε φ' ε' := by
  intro U _ h
  apply Additive.ofMul.injective
  simpa only [ofMul_prod, ofMul_zpow] using H (Additive U) (fun ψ => Additive.ofMul (h ψ))

/- English proof (translation)
Establish `l : ∀ j : K → L.ι, LB.wchart L (fun k => h ≫ φ k) j ≤ LB.wchart (LB.LinComb L φ ε) (K` using `PUnit) (fun _ => h) (fun _ => j) := fun _ _ hy => Set.mem_iInter.2 fun _ => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k`. Establish `e1 : ∀ (j : K → L.ι) (y : Y'), y ∈ LB.wchart L (fun k => h ≫ φ k) j → gs (𝟙 Y') y _ (res (l j) (c.s (fun _ => j))).val = (gm (𝟙 Y') y (LB.wchart (LB.LinComb L φ ε) (K` using `PUnit) (fun _ => h) (fun _ => j)) (c.s (fun _ => j))).val := fun j y hj => (gs_unit _ y _ hj _).trans (congrArg Units.val (gm_res _ y (l j) hj _))`. Use `⟨⟨fun j => (res (l j) (c.s (fun _ => j))).val, fun j j' => fn_ext fun y hy => ?_⟩, ?_⟩` and prove the remaining obligations. Use `((gs_res (𝟙 Y') y _ hy _).trans (e1 j y hy.1)).trans (Eq.trans ?_ ((gs_mul (𝟙 Y') y _ hy _ _).trans (congrArg₂ (· * ·) ((gs_unit (𝟙 Y') y _ hy _).trans (congrArg Units.val (gm_linComb L _ _ (𝟙 Y') y j j' hy.1 hy.2))) ((gs_res (𝟙 Y') y _ hy _).trans (e1 j' y hy.2)))).symm)` and prove the remaining obligations. Establish `m : ∀ j : K → L.ι, y ∈ LB.wchart L (fun k => h ≫ φ k) j → (𝟙 Y' ≫ h) y ∈ LB.wchart L φ j` using `fun j hj => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hj k`.

Rewrite using `[gen_trans hc (𝟙 Y') y (l j hy.1) (l j' hy.2), Units.val_mul]`. Use `congr 2`. Simplify using `only [trF, Finset.univ_unique, Finset.prod_singleton, zpow_one]`. Conclude with `(gm_linComb L φ ε (𝟙 Y' ≫ h) y j j' (m j hy.1) (m j' hy.2)).trans (by simp only [Category.assoc])`. Introduce `r z J hJ`.

Establish `hm` using `hJ.mem (fun k => h ≫ φ k) r`. Conclude with `(congrArg IsUnit (gs_unit r z _ hm _)).mpr (Units.isUnit _)`.
-/
theorem exists_sec_of_pullGen {Y' : Scheme.{0}} {φ : K → (Y ⟶ X)} {ε : K → ℤ} (h : Y' ⟶ Y)
    (c : LB.Gen ((LB.LinComb L φ ε).pull h)) (hc : c.IsGen) :
    ∃ s : LB.Sec (LB.LinComb L (fun k => h ≫ φ k) ε), ∀ (r : Z ⟶ Y') (z : Z) (J : (Z ⟶ X) → L.ι),
      Good L z J → IsUnit (sval s r z J) := by
  have l : ∀ j : K → L.ι, LB.wchart L (fun k => h ≫ φ k) j ≤
      LB.wchart (LB.LinComb L φ ε) (K := PUnit) (fun _ => h) (fun _ => j) :=
    fun _ _ hy => Set.mem_iInter.2 fun _ => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k
  have e1 : ∀ (j : K → L.ι) (y : Y'), y ∈ LB.wchart L (fun k => h ≫ φ k) j →
      gs (𝟙 Y') y _ (res (l j) (c.s (fun _ => j))).val =
        (gm (𝟙 Y') y (LB.wchart (LB.LinComb L φ ε) (K := PUnit) (fun _ => h) (fun _ => j)) (c.s (fun _ => j))).val :=
    fun j y hj => (gs_unit _ y _ hj _).trans (congrArg Units.val (gm_res _ y (l j) hj _))
  refine ⟨⟨fun j => (res (l j) (c.s (fun _ => j))).val, fun j j' => fn_ext fun y hy => ?_⟩, ?_⟩
  · refine ((gs_res (𝟙 Y') y _ hy _).trans (e1 j y hy.1)).trans (Eq.trans ?_ ((gs_mul (𝟙 Y') y _ hy _ _).trans
      (congrArg₂ (· * ·) ((gs_unit (𝟙 Y') y _ hy _).trans
        (congrArg Units.val (gm_linComb L _ _ (𝟙 Y') y j j' hy.1 hy.2))) ((gs_res (𝟙 Y') y _ hy _).trans
          (e1 j' y hy.2)))).symm)
    have m : ∀ j : K → L.ι, y ∈ LB.wchart L (fun k => h ≫ φ k) j → (𝟙 Y' ≫ h) y ∈ LB.wchart L φ j :=
      fun j hj => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hj k
    rw [gen_trans hc (𝟙 Y') y (l j hy.1) (l j' hy.2), Units.val_mul]
    congr 2
    simp only [trF, Finset.univ_unique, Finset.prod_singleton, zpow_one]
    exact (gm_linComb L φ ε (𝟙 Y' ≫ h) y j j' (m j hy.1) (m j' hy.2)).trans (by simp only [Category.assoc])
  · intro r z J hJ
    have hm := hJ.mem (fun k => h ≫ φ k) r
    exact (congrArg IsUnit (gs_unit r z _ hm _)).mpr (Units.isUnit _)

section Square

variable {k : Type} [Field k]

/- English proof (translation)
Establish `h1 : PrimeSpectrum.asIdeal (R` using `k) q = ⊥ := @Ideal.eq_bot_of_prime k _ _ (PrimeSpectrum.isPrime (R := k) q)`. Establish `h2 : PrimeSpectrum.asIdeal (R` using `k) q' = ⊥ := @Ideal.eq_bot_of_prime k _ _ (PrimeSpectrum.isPrime (R := k) q')`. Conclude with `PrimeSpectrum.ext (h1.trans h2.symm)`.
-/
theorem spec_pt_eq (q q' : Spec (CommRingCat.of k)) : q = q' := by
  have h1 : PrimeSpectrum.asIdeal (R := k) q = ⊥ := @Ideal.eq_bot_of_prime k _ _ (PrimeSpectrum.isPrime (R := k) q)
  have h2 : PrimeSpectrum.asIdeal (R := k) q' = ⊥ := @Ideal.eq_bot_of_prime k _ _ (PrimeSpectrum.isPrime (R := k) q')
  exact PrimeSpectrum.ext (h1.trans h2.symm)

/- English proof (translation)
Take `⟨V, hpV, c, hc⟩` from `hsq (Spec (CommRingCat.of k)) P (baseOver (Spec (CommRingCat.of k))) x₁ x₂ (IsLocalRing.closedPoint k)`. Establish `hV : V = ⊤` using `eq_top_iff.2 fun q _ => by rw [spec_pt_eq q (IsLocalRing.closedPoint k)]; exact hpV`. Substitute `hV` using the available equality. Take `⟨s, hs⟩` from `exists_sec_of_pullGen (Z := (baseOver (Spec (CommRingCat.of k)) ⊗ P.A).left) ((fst (baseOver (Spec (CommRingCat.of k))) P.A).left ⁻¹ᵁ ⊤).ι c hc`. Set `e` to `IsOpenImmersion.lift ((fst (baseOver (Spec (CommRingCat.of k))) P.A).left ⁻¹ᵁ ⊤).ι (𝟙 _) (by rintro _ ⟨q, rfl⟩; rw [Scheme.Opens.range_ι]; trivial)`.

Establish `he : e ≫ ((fst (baseOver (Spec (CommRingCat.of k))) P.A).left ⁻¹ᵁ ⊤).ι = 𝟙 _` using `IsOpenImmersion.lift_fac _ _ _`. Use `UnitAt.congr P.isLB ?_ ⟨pullSec s e, fun J hJ => ?_⟩` and prove the remaining obligations. Use `formEq_of_add fun U _ hh => ?_` and prove the remaining obligations. Simplify using `only [← Category.assoc, he, Category.id_comp]`. Rewrite using `[sval_pullSec s e (𝟙 _) y hJ]`.

Conclude with `hs _ y J hJ`.
-/
theorem unitAt_square (hsq : SquareSt) (P : PolAV (Spec (CommRingCat.of k)))
    (x₁ x₂ : baseOver (Spec (CommRingCat.of k)) ⟶ P.A) (y : (baseOver (Spec (CommRingCat.of k)) ⊗ P.A).left) :
    UnitAt P.L ![(translPt P.A (x₁ * x₂)).left, (snd (baseOver (Spec (CommRingCat.of k))) P.A).left,
      (translPt P.A x₁).left, (translPt P.A x₂).left] ![1, 1, -1, -1] y := by
  obtain ⟨V, hpV, c, hc⟩ := hsq (Spec (CommRingCat.of k)) P (baseOver (Spec (CommRingCat.of k))) x₁ x₂
    (IsLocalRing.closedPoint k)
  have hV : V = ⊤ := eq_top_iff.2 fun q _ => by rw [spec_pt_eq q (IsLocalRing.closedPoint k)]; exact hpV
  subst hV
  obtain ⟨s, hs⟩ := exists_sec_of_pullGen (Z := (baseOver (Spec (CommRingCat.of k)) ⊗ P.A).left)
    ((fst (baseOver (Spec (CommRingCat.of k))) P.A).left ⁻¹ᵁ ⊤).ι c hc
  let e := IsOpenImmersion.lift ((fst (baseOver (Spec (CommRingCat.of k))) P.A).left ⁻¹ᵁ ⊤).ι (𝟙 _)
    (by rintro _ ⟨q, rfl⟩; rw [Scheme.Opens.range_ι]; trivial)
  have he : e ≫ ((fst (baseOver (Spec (CommRingCat.of k))) P.A).left ⁻¹ᵁ ⊤).ι = 𝟙 _ :=
    IsOpenImmersion.lift_fac _ _ _
  refine UnitAt.congr P.isLB ?_ ⟨pullSec s e, fun J hJ => ?_⟩
  · refine formEq_of_add fun U _ hh => ?_
    simp only [← Category.assoc, he, Category.id_comp]
  · rw [sval_pullSec s e (𝟙 _) y hJ]
    exact hs _ y J hJ

/- English proof (translation)
The claim follows from `| 0 => by refine UnitAt.congr P.isLB (formEq_of_add fun U _ hh => ?_) (unitAt_square hsq P b b y) simp [Fin.sum_univ_succ, pow_two] module | n + 1 => by refine UnitAt.congr P.isLB (formEq_of_add fun U _ hh => ?_) ((unitAt_iter hsq P b y n).mul (unitAt_square hsq P (b ^ (n + 2)) b …`.
-/
theorem unitAt_iter (hsq : SquareSt) (P : PolAV (Spec (CommRingCat.of k)))
    (b : baseOver (Spec (CommRingCat.of k)) ⟶ P.A) (y : (baseOver (Spec (CommRingCat.of k)) ⊗ P.A).left) :
    ∀ n : ℕ, UnitAt P.L ![(translPt P.A (b ^ (n + 2))).left, (snd (baseOver (Spec (CommRingCat.of k))) P.A).left,
      (translPt P.A b).left] ![1, (n : ℤ) + 1, -((n : ℤ) + 2)] y
  | 0 => by
    refine UnitAt.congr P.isLB (formEq_of_add fun U _ hh => ?_) (unitAt_square hsq P b b y)
    simp [Fin.sum_univ_succ, pow_two]
    module
  | n + 1 => by
    refine UnitAt.congr P.isLB (formEq_of_add fun U _ hh => ?_)
      ((unitAt_iter hsq P b y n).mul (unitAt_square hsq P (b ^ (n + 2)) b y))
    have e : b ^ (n + 2) * b = b ^ (n + 1 + 2) := by rw [← pow_succ]
    simp [Fin.sum_univ_succ, e]
    module

end Square

end ReciprocityTheory.ChartRestriction.G.H1.SquareUnits
