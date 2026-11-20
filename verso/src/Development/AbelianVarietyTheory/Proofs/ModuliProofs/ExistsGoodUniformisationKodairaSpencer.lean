import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsSymm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CauchyRiemannIffDifferentiableOnComplex

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

noncomputable section
namespace GlobalTheory.KSInh

variable {g : ℕ} {A₀ : Over (Sp ℂ)} [GrpObj A₀] {L₀ : LB A₀.left} (u : HolUnif A₀ L₀ g)

/- English proof (translation)
Use extensionality with `z`. Unfold `dom`. Simplify using `only [Category.comp_id]`.
-/
theorem dom_id (W : A₀.left.Opens) : dom u (𝟙 _) W = {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ W} := by
  ext z
  unfold dom
  simp only [Category.comp_id]

/- English proof (translation)
Use function extensionality and compare the values at `z`. Unfold `fn`. Rewrite using `[Category.comp_id]`.
-/
theorem fn_id (W : A₀.left.Opens) (f : Γ(A₀.left, W)) :
    fn u (𝟙 _) W f = fun z => valAt' (u.ex z).left W f := by
  funext z
  unfold fn
  rw [Category.comp_id]

/- English proof (translation)
Rewrite using `[dom_id]`. Conclude with `(u.hol W 0).1`.
-/
theorem isOpen_dom (W : A₀.left.Opens) : IsOpen (dom u (𝟙 _) W) := by
  rw [dom_id]
  exact (u.hol W 0).1

/- English proof (translation)
Rewrite using `[dom_id, fn_id]`. Conclude with `(u.hol W f).2`.
-/
theorem differentiableOn_fn (W : A₀.left.Opens) (f : Γ(A₀.left, W)) :
    DifferentiableOn ℂ (fn u (𝟙 _) W f) (dom u (𝟙 _) W) := by
  rw [dom_id, fn_id]
  exact (u.hol W f).2

/- English proof (translation)
The claim follows from `(differentiableOn_fn u W f).differentiableAt ((isOpen_dom u W).mem_nhds hz)`.
-/
theorem differentiableAt_fn (W : A₀.left.Opens) (f : Γ(A₀.left, W)) {z : Fin g → ℂ} (hz : z ∈ dom u (𝟙 _) W) :
    DifferentiableAt ℂ (fn u (𝟙 _) W f) z :=
  (differentiableOn_fn u W f).differentiableAt ((isOpen_dom u W).mem_nhds hz)

/- English proof (translation)
Rewrite using `[u.ex_add, (u.ker _).2 l.2, _root_.mul_one]`.
-/
theorem ex_add_period (l : u.Λ) (z : Fin g → ℂ) : u.ex (z + l) = u.ex z := by
  rw [u.ex_add, (u.ker _).2 l.2, _root_.mul_one]

/- English proof (translation)
Establish `hd : ∀ (W : A₀.left.Opens) (k : Γ(A₀.left, W)), ⊤ ≤ ((u.ex z).left ≫ 𝟙 _) ⁻¹ᵁ W → DifferentiableAt ℂ (fn u (𝟙 _) W k) z` using `fun W k hW => differentiableAt_fn u W k hW`. Use `⟨fun W hW f f' => ?_, fun W hW f f' => ?_, fun W W' h hW' f => ?_⟩` and prove the remaining obligations. Establish `e : fn u (𝟙 _) W (f + f') = fn u (𝟙 _) W f + fn u (𝟙 _) W f'`. Use function extensionality and compare the values at `y`. Simplify using `only [fn, valAt', Pi.add_apply]`.

Use `split_ifs with hy`. Simplify using `only [valAt, map_add]`. Conclude with `(add_zero 0).symm`. Use `show fderiv ℂ (fn u (𝟙 _) W (f + f')) z w = fderiv ℂ (fn u (𝟙 _) W f) z w + fderiv ℂ (fn u (𝟙 _) W f') z w`. Rewrite using `[e, fderiv_add (hd W f hW) (hd W f' hW)]`.

Both sides reduce to the same expression. Establish `e : fn u (𝟙 _) W (f * f') = fn u (𝟙 _) W f * fn u (𝟙 _) W f'`. Use function extensionality and compare the values at `y`. Simplify using `only [fn, valAt', Pi.mul_apply]`. Use `split_ifs with hy`.

Simplify using `only [valAt, map_mul]`. Conclude with `(mul_zero 0).symm`. Use `show fderiv ℂ (fn u (𝟙 _) W (f * f')) z w = fn u (𝟙 _) W f z * fderiv ℂ (fn u (𝟙 _) W f') z w + fn u (𝟙 _) W f' z * fderiv ℂ (fn u (𝟙 _) W f) z w`. Rewrite using `[e, fderiv_mul (hd W f hW) (hd W f' hW)]`. Both sides reduce to the same expression.

Use `show fderiv ℂ (fn u (𝟙 _) W' (resG A₀.left h f)) z w = fderiv ℂ (fn u (𝟙 _) W f) z w`. Establish `hev : fn u (𝟙 _) W' (resG A₀.left h f) =ᶠ[nhds z] fn u (𝟙 _) W f` using `by filter_upwards [(isOpen_dom u W').mem_nhds hW'] with y hy`. Establish `hyW' : ⊤ ≤ ((u.ex y).left ≫ 𝟙 _) ⁻¹ᵁ W'` using `hy`. Establish `hy' : ⊤ ≤ ((u.ex y).left ≫ 𝟙 _) ⁻¹ᵁ W` using `hyW'.trans (Scheme.Hom.preimage_mono _ h)`. Simplify using `only [fn, valAt', dif_pos hyW', dif_pos hy']`.

Unfold `valAt resG`. Establish `key : A₀.left.presheaf.map (homOfLE h).op ≫ Scheme.Hom.appLE ((u.ex y).left ≫ 𝟙 _) W' ⊤ hyW' = Scheme.Hom.appLE ((u.ex y).left ≫ 𝟙 _) W ⊤ hy'` using `Scheme.Hom.map_appLE _ _ _`. Rewrite using `[← key]`. Both sides reduce to the same expression. Rewrite using `[hev.fderiv_eq]`.

Use `base z r := by show fderiv ℂ (fn u (𝟙 _) ⊤ (constFn A₀.hom ⊤ r)) z w = 0`. Choose the witnesses or unpack the hypotheses as in `⟨K, hK⟩ : ∃ K : ℂ, ∀ y, fn u (𝟙 _) ⊤ (constFn A₀.hom ⊤ r) y = K := by`. Use `⟨(Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom ((Scheme.Hom.appLE (𝟙_ (Over (Sp ℂ))).hom ⊤ ⊤ (Scheme.Hom.preimage_top _).ge).hom ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom r)), fun y => ?_⟩` and prove the remaining obligations. Establish `ht : ⊤ ≤ ((u.ex y).left ≫ 𝟙 _) ⁻¹ᵁ (⊤ : A₀.left.Opens)` using `(Scheme.Hom.preimage_top _).ge`. Establish `key : Scheme.Hom.appLE A₀.hom ⊤ ⊤ (Scheme.Hom.preimage_top _).ge ≫ Scheme.Hom.appLE ((u.ex y).left ≫ 𝟙 _) ⊤ ⊤ ht = Scheme.Hom.appLE (𝟙_ (Over (Sp ℂ))).hom ⊤ ⊤ (Scheme.Hom.preimage_top _).ge`.

Rewrite using `[Scheme.Hom.appLE_comp_appLE]`. Use `congr 1`. Simplify using the standard rewrite rules. Simplify using `only [fn, valAt', dif_pos ht]`. Unfold `valAt constFn`.

Rewrite using `[← key]`. Both sides reduce to the same expression. Establish `e : fn u (𝟙 _) ⊤ (constFn A₀.hom ⊤ r) = fun _ => K` using `funext hK`. Rewrite using `[e]`. Simplify using the standard rewrite rules.

Use `hol W f := ((cauchyRiemann_iff_differentiableOn_complex g _ _ (isOpen_dom u W)).2 (differentiableOn_fn u W f)).2 w`. Use `per l W f z _ := by show fderiv ℂ (fn u (𝟙 _) W f) (z + l) w = fderiv ℂ (fn u (𝟙 _) W f) z w + fderiv ℂ (fn u (𝟙 _) W f) z ((0 : Matrix (Fin g) (Fin g) ℂ).mulVec (star (l : Fin g → ℂ)))`. Establish `hp : (fun y => fn u (𝟙 _) W f (y + l)) = fn u (𝟙 _) W f`. Use function extensionality and compare the values at `y`. Unfold `fn`.

Rewrite using `[ex_add_period]`. Rewrite using `[Matrix.zero_mulVec, map_zero, add_zero, ← fderiv_comp_add_right, hp]`.
-/
theorem ksRel_const (w : Fin g → ℂ) :
    KSRel u A₀.hom (𝟙 _) (fun _ => 0) 0 (fun z W f => fderiv ℂ (fn u (𝟙 _) W f) z w) where
  der z := by
    have hd : ∀ (W : A₀.left.Opens) (k : Γ(A₀.left, W)), ⊤ ≤ ((u.ex z).left ≫ 𝟙 _) ⁻¹ᵁ W →
        DifferentiableAt ℂ (fn u (𝟙 _) W k) z :=
      fun W k hW => differentiableAt_fn u W k hW
    refine ⟨fun W hW f f' => ?_, fun W hW f f' => ?_, fun W W' h hW' f => ?_⟩
    · have e : fn u (𝟙 _) W (f + f') = fn u (𝟙 _) W f + fn u (𝟙 _) W f' := by
        funext y
        simp only [fn, valAt', Pi.add_apply]
        split_ifs with hy
        · simp only [valAt, map_add]
        · exact (add_zero 0).symm
      show fderiv ℂ (fn u (𝟙 _) W (f + f')) z w =
        fderiv ℂ (fn u (𝟙 _) W f) z w + fderiv ℂ (fn u (𝟙 _) W f') z w
      rw [e, fderiv_add (hd W f hW) (hd W f' hW)]
      rfl
    · have e : fn u (𝟙 _) W (f * f') = fn u (𝟙 _) W f * fn u (𝟙 _) W f' := by
        funext y
        simp only [fn, valAt', Pi.mul_apply]
        split_ifs with hy
        · simp only [valAt, map_mul]
        · exact (mul_zero 0).symm
      show fderiv ℂ (fn u (𝟙 _) W (f * f')) z w =
        fn u (𝟙 _) W f z * fderiv ℂ (fn u (𝟙 _) W f') z w + fn u (𝟙 _) W f' z * fderiv ℂ (fn u (𝟙 _) W f) z w
      rw [e, fderiv_mul (hd W f hW) (hd W f' hW)]
      rfl
    · show fderiv ℂ (fn u (𝟙 _) W' (resG A₀.left h f)) z w = fderiv ℂ (fn u (𝟙 _) W f) z w
      have hev : fn u (𝟙 _) W' (resG A₀.left h f) =ᶠ[nhds z] fn u (𝟙 _) W f := by
        filter_upwards [(isOpen_dom u W').mem_nhds hW'] with y hy
        have hyW' : ⊤ ≤ ((u.ex y).left ≫ 𝟙 _) ⁻¹ᵁ W' := hy
        have hy' : ⊤ ≤ ((u.ex y).left ≫ 𝟙 _) ⁻¹ᵁ W := hyW'.trans (Scheme.Hom.preimage_mono _ h)
        simp only [fn, valAt', dif_pos hyW', dif_pos hy']
        unfold valAt resG
        have key : A₀.left.presheaf.map (homOfLE h).op ≫ Scheme.Hom.appLE ((u.ex y).left ≫ 𝟙 _) W' ⊤ hyW' =
            Scheme.Hom.appLE ((u.ex y).left ≫ 𝟙 _) W ⊤ hy' :=
          Scheme.Hom.map_appLE _ _ _
        rw [← key]
        rfl
      rw [hev.fderiv_eq]
  base z r := by
    show fderiv ℂ (fn u (𝟙 _) ⊤ (constFn A₀.hom ⊤ r)) z w = 0
    obtain ⟨K, hK⟩ : ∃ K : ℂ, ∀ y, fn u (𝟙 _) ⊤ (constFn A₀.hom ⊤ r) y = K := by
      refine ⟨(Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom
        ((Scheme.Hom.appLE (𝟙_ (Over (Sp ℂ))).hom ⊤ ⊤ (Scheme.Hom.preimage_top _).ge).hom
          ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom r)), fun y => ?_⟩
      have ht : ⊤ ≤ ((u.ex y).left ≫ 𝟙 _) ⁻¹ᵁ (⊤ : A₀.left.Opens) := (Scheme.Hom.preimage_top _).ge
      have key : Scheme.Hom.appLE A₀.hom ⊤ ⊤ (Scheme.Hom.preimage_top _).ge ≫ Scheme.Hom.appLE ((u.ex y).left ≫ 𝟙 _) ⊤ ⊤ ht =
          Scheme.Hom.appLE (𝟙_ (Over (Sp ℂ))).hom ⊤ ⊤ (Scheme.Hom.preimage_top _).ge := by
        rw [Scheme.Hom.appLE_comp_appLE]
        congr 1
        simp
      simp only [fn, valAt', dif_pos ht]
      unfold valAt constFn
      rw [← key]
      rfl
    have e : fn u (𝟙 _) ⊤ (constFn A₀.hom ⊤ r) = fun _ => K := funext hK
    rw [e]
    simp
  hol W f :=
    ((cauchyRiemann_iff_differentiableOn_complex g _ _ (isOpen_dom u W)).2 (differentiableOn_fn u W f)).2 w
  per l W f z _ := by
    show fderiv ℂ (fn u (𝟙 _) W f) (z + l) w =
      fderiv ℂ (fn u (𝟙 _) W f) z w + fderiv ℂ (fn u (𝟙 _) W f) z ((0 : Matrix (Fin g) (Fin g) ℂ).mulVec (star (l : Fin g → ℂ)))
    have hp : (fun y => fn u (𝟙 _) W f (y + l)) = fn u (𝟙 _) W f := by
      funext y
      unfold fn
      rw [ex_add_period]
    rw [Matrix.zero_mulVec, map_zero, add_zero, ← fderiv_comp_add_right, hp]

/- English proof (translation)
Introduce `hT P₀`. Take `⟨rig, hrig⟩ : ∃ rig : LB.Gen (P₀.L.pull (eSec P₀.A)), rig.IsGen` from `P₀.rigid`. Take `⟨u, Hm, χ, _, hAH, -, ht₁, ht₂, hend, hth, -⟩` from `hT P₀ rig hrig`. Conclude with `⟨u, Hm, χ, ⟨hAH, ht₁, ht₂, hend, fun n θ hθ => ((hth n).2 θ hθ).exists⟩, fun w => ksRel_const u w⟩`.
-/
theorem exists_goodU_ksRel : ThetaUnifAV → ∀ P₀ : Out.PolAV (Sp ℂ), ∃ (u : HolUnif P₀.A P₀.L P₀.g) (Hm : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ : u.Λ → ℂ), GoodU u Hm χ ∧ ∀ w : Fin P₀.g → ℂ, KSRel u P₀.A.hom (𝟙 _) (fun _ => 0) 0 (fun z W f => fderiv ℂ (fn u (𝟙 _) W f) z w) := by
  intro hT P₀
  obtain ⟨rig, hrig⟩ : ∃ rig : LB.Gen (P₀.L.pull (eSec P₀.A)), rig.IsGen := P₀.rigid
  obtain ⟨u, Hm, χ, _, hAH, -, ht₁, ht₂, hend, hth, -⟩ := hT P₀ rig hrig
  exact ⟨u, Hm, χ, ⟨hAH, ht₁, ht₂, hend, fun n θ hθ => ((hth n).2 θ hθ).exists⟩, fun w => ksRel_const u w⟩

end GlobalTheory.KSInh
end
