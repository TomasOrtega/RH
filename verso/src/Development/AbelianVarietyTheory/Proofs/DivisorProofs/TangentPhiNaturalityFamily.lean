import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiCompactZeroSec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoToBidualOfLocalFrames
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent)
open GlobalTheory.SqZeroPt GlobalTheory.PDivGroup GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.LieKer

/- English proof (translation)
Take `⟨m, f, hf⟩` from `Module.Finite.exists_fin' O W`. Take `⟨s, hs⟩` from `Module.projective_lifting_property f LinearMap.id hf`. Establish `e : w = ∑ i, (s w i) • f (Pi.single i 1)` using `by conv_lhs => rw [← LinearMap.id_apply (R := O) w, ← hs]`. Rewrite using `[LinearMap.comp_apply]`. Use `conv_lhs => rw [pi_eq_sum_univ (s w)]`.

Simplify using `only [map_sum, map_smul]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Use `congr 2`. Use extensionality with `j`. Simplify using `[Pi.single_apply, eq_comm]`.

Rewrite using `[e]`. Use `Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul ?_ Submodule.mem_top` and prove the remaining obligations. Conclude with `hw (LinearMap.proj i ∘ₗ s)`.
-/
theorem mem_smul_top_of_forms {O W : Type} [CommRing O] [AddCommGroup W] [Module O W]
    [Module.Finite O W] [Module.Projective O W] (I : Ideal O) (w : W)
    (hw : ∀ l : W →ₗ[O] O, l w ∈ I) : w ∈ (I • ⊤ : Submodule O W) := by
  obtain ⟨m, f, hf⟩ := Module.Finite.exists_fin' O W
  obtain ⟨s, hs⟩ := Module.projective_lifting_property f LinearMap.id hf
  have e : w = ∑ i, (s w i) • f (Pi.single i 1) := by
    conv_lhs => rw [← LinearMap.id_apply (R := O) w, ← hs]
    rw [LinearMap.comp_apply]
    conv_lhs => rw [pi_eq_sum_univ (s w)]
    simp only [map_sum, map_smul]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 2
    ext j
    simp [Pi.single_apply, eq_comm]
  rw [e]
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul ?_ Submodule.mem_top
  exact hw (LinearMap.proj i ∘ₗ s)

end GlobalTheory.LieKer

namespace GlobalTheory.LieKer

open GlobalTheory.PDiv

/- English proof (translation)
Use `ext1`. Express the relevant statement in the definitionally equal form `Spec.map _ ≫ Spec.map _ = Spec.map _`. Rewrite using `[← Spec.map_comp]`. Use `congr 1`. Use `CommRingCat.hom_ext (RingHom.ext fun x => ?_)` and prove the remaining obligations.

Simplify using the standard rewrite rules.
-/
theorem zeroSec_sqZeroMap {O : Type} [CommRing O] {M N : Type} [AddCommGroup M] [Module O M]
    [Module Oᵐᵒᵖ M] [IsCentralScalar O M] [AddCommGroup N] [Module O N] [Module Oᵐᵒᵖ N]
    [IsCentralScalar O N] (l : M →ₗ[O] N) :
    zeroSec O N ≫ GlobalTheory.GrpTangent.sqZeroMap l = zeroSec O M := by
  ext1
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  refine CommRingCat.hom_ext (RingHom.ext fun x => ?_)
  simp

/- English proof (translation)
Introduce `p O _ G A _ t hfin hproj hnat hsurj hcn n w hw`. Use `mem_smul_top_of_forms _ w fun l => ?_` and prove the remaining obligations. Take `⟨v, hv, hl⟩` from `hsurj l`. Set `M` to `ModPow p O n`. Set `mk : O →ₗ[O] M` to `(Ideal.Quotient.mkₐ O (Ideal.span {(p : O) ^ n})).toLinearMap`.

Establish `h' : zeroSec O M ≫ (GlobalTheory.GrpTangent.sqZeroMap mk ≫ v) = η[A]`. Rewrite using `[← Category.assoc, zeroSec_sqZeroMap, hv]`. Establish `e1` using `hnat O M mk v hv h' w`. Establish `htan : IsTangent v`. Use `congrArg Over.Hom.left hv` as an intermediate fact.

Simplify using `only [Over.comp_left, zeroSec, Over.homMk_left] at this`. Conclude with `this`. Establish `hpow : (GlobalTheory.GrpTangent.sqZeroMap mk ≫ v : SpAlg O (TrivSqZeroExt O M) ⟶ A) ^ p ^ n = 1`. Establish `hs : GlobalTheory.GrpTangent.sqZeroMap mk ≫ GlobalTheory.GrpTangent.epsScale (((p ^ n : ℕ) : O)) = GlobalTheory.GrpTangent.sqZeroMap mk ≫ GlobalTheory.GrpTangent.epsScale 0` using `by ext1`. Express the relevant statement in the definitionally equal form `Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _`.

Rewrite using `[← Spec.map_comp, ← Spec.map_comp]`. Use `congr 1`. Use `CommRingCat.hom_ext (RingHom.ext fun x => ?_)` and prove the remaining obligations. Use `ext`. Simplify using `[ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsScaleR]`.

Simplify using `[ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsScaleR, mk]`. Rewrite using `[← MonObj.comp_pow, GlobalTheory.GrpTangent.pow_eq_epsScale_comp htan, ← Category.assoc, hs, Category.assoc, GlobalTheory.GrpTangent.epsScale_zero_comp htan, MonObj.comp_one]`. Take `⟨φ, hφy⟩` from `t.surj n (TrivSqZeroExt O M) _ hpow`. Establish `hφ : (TrivSqZeroExt.fstHom O O M).comp φ = Bialgebra.counitAlgHom O (G.A n)`. Establish `H : spOver ((TrivSqZeroExt.fstHom O O M).comp φ) ≫ t.y n = 1`.

Rewrite using `[← spOver_comp, Category.assoc, hφy]`. Use `ext1`. Simplify using `only [Over.comp_left]`. Establish `e : (spOver (TrivSqZeroExt.fstHom O O M)).left ≫ (GlobalTheory.GrpTangent.sqZeroMap mk).left = spMap (TrivSqZeroExt.fstHom O O O).toRingHom`. Express the relevant statement in the definitionally equal form `Spec.map _ ≫ Spec.map _ = Spec.map _`.

Rewrite using `[← Spec.map_comp]`. Use `congr 1`. Use `CommRingCat.hom_ext (RingHom.ext fun x => ?_)` and prove the remaining obligations. Simplify using the standard rewrite rules. Rewrite using `[← Category.assoc, e]`.

Use `(htan : _).trans ?_` and prove the remaining obligations. Establish `hu : (toUnit (Over.mk (spMap (algebraMap O O)))).left = 𝟙 (Sp O)`. Rewrite using `[Over.toUnit_left]`. Conclude with `Spec.map_id _`. Express the relevant statement in the definitionally equal form `η[A].left = (toUnit (Over.mk (spMap (algebraMap O O))) ≫ η[A]).left`.

Rewrite using `[Over.comp_left, hu]`. Conclude with `(Category.id_comp _).symm`. Conclude with `AlgHom.ext fun a => ((t.eq_one_iff n _).1 H a).trans (by simp)`. Establish `e2` using `hcn M n φ hφ w`. Establish `e3 : Phi (GlobalTheory.GrpTangent.sqZeroMap mk ≫ v) h' w = 0`.

Establish `tr : ∀ (z : TM O M ⟶ A) (hz : zeroSec O M ≫ z = η[A]), spOver φ ≫ t.y n = z → Phi z hz w = Phi (spOver φ ≫ t.y n) (zeroSec_spOver_y t n φ hφ) w`. Introduce and unpack `z hz rfl`. Both sides reduce to the same expression. Rewrite using `[tr _ h' hφy, e2, hw, map_zero]`. Rewrite `e1` using `[e3, hl]`.

Conclude with `(Ideal.Quotient.eq_zero_iff_mem).1 e1.symm`.
-/
theorem ker_cn_le : ∀ (p : ℕ) (O : Type) [CommRing O] (G : GlobalTheory.PDivGroup p O) (A : Over (Sp O)) [GrpObj A] (t : G.TorsionTower A), Module.Finite O (Wmod A) → Module.Projective O (Wmod A) → (∀ (M N : Type) [AddCommGroup M] [Module O M] [Module Oᵐᵒᵖ M] [IsCentralScalar O M] [AddCommGroup N] [Module O N] [Module Oᵐᵒᵖ N] [IsCentralScalar O N] (l : M →ₗ[O] N) (z : TM O M ⟶ A) (h : zeroSec O M ≫ z = η[A]) (h' : zeroSec O N ≫ (GlobalTheory.GrpTangent.sqZeroMap l ≫ z) = η[A]) (w : Wmod A), Phi (GlobalTheory.GrpTangent.sqZeroMap l ≫ z) h' w = l (Phi z h w)) → (∀ (l : Wmod A →ₗ[O] O), ∃ (v : TM O O ⟶ A) (h : zeroSec O O ≫ v = η[A]), ∀ w, Phi v h w = l w) → (∀ (M : Type) [AddCommGroup M] [Module O M] [Module Oᵐᵒᵖ M] [IsCentralScalar O M] (n : ℕ) (φ : G.A n →ₐ[O] TrivSqZeroExt O M) (hφ : (TrivSqZeroExt.fstHom O O M).comp φ = Bialgebra.counitAlgHom O (G.A n)) (w : Wmod A), Phi (spOver φ ≫ t.y n) (zeroSec_spOver_y t n φ hφ) w = GlobalTheory.AugCot.sqZeroEquiv (Bialgebra.counitAlgHom O (G.A n)) M ⟨φ, hφ⟩ (cn t n w)) → ∀ (n : ℕ) (w : Wmod A), cn t n w = 0 → w ∈ (Ideal.span {(p : O) ^ n} • ⊤ : Submodule O (Wmod A)) := by
  intro p O _ G A _ t hfin hproj hnat hsurj hcn n w hw
  refine mem_smul_top_of_forms _ w fun l => ?_
  obtain ⟨v, hv, hl⟩ := hsurj l
  let M := ModPow p O n
  let mk : O →ₗ[O] M := (Ideal.Quotient.mkₐ O (Ideal.span {(p : O) ^ n})).toLinearMap
  have h' : zeroSec O M ≫ (GlobalTheory.GrpTangent.sqZeroMap mk ≫ v) = η[A] := by
    rw [← Category.assoc, zeroSec_sqZeroMap, hv]
  have e1 := hnat O M mk v hv h' w
  have htan : IsTangent v := by
    have := congrArg Over.Hom.left hv
    simp only [Over.comp_left, zeroSec, Over.homMk_left] at this
    exact this
  have hpow : (GlobalTheory.GrpTangent.sqZeroMap mk ≫ v : SpAlg O (TrivSqZeroExt O M) ⟶ A) ^ p ^ n = 1 := by
    have hs : GlobalTheory.GrpTangent.sqZeroMap mk ≫ GlobalTheory.GrpTangent.epsScale (((p ^ n : ℕ) : O)) =
        GlobalTheory.GrpTangent.sqZeroMap mk ≫ GlobalTheory.GrpTangent.epsScale 0 := by
      ext1
      change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
      rw [← Spec.map_comp, ← Spec.map_comp]
      congr 1
      refine CommRingCat.hom_ext (RingHom.ext fun x => ?_)
      ext
      · simp [ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsScaleR]
      · simp [ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsScaleR, mk]
    rw [← MonObj.comp_pow, GlobalTheory.GrpTangent.pow_eq_epsScale_comp htan, ← Category.assoc, hs,
      Category.assoc, GlobalTheory.GrpTangent.epsScale_zero_comp htan, MonObj.comp_one]
  obtain ⟨φ, hφy⟩ := t.surj n (TrivSqZeroExt O M) _ hpow
  have hφ : (TrivSqZeroExt.fstHom O O M).comp φ = Bialgebra.counitAlgHom O (G.A n) := by
    have H : spOver ((TrivSqZeroExt.fstHom O O M).comp φ) ≫ t.y n = 1 := by
      rw [← spOver_comp, Category.assoc, hφy]
      ext1
      simp only [Over.comp_left]
      have e : (spOver (TrivSqZeroExt.fstHom O O M)).left ≫ (GlobalTheory.GrpTangent.sqZeroMap mk).left =
          spMap (TrivSqZeroExt.fstHom O O O).toRingHom := by
        change Spec.map _ ≫ Spec.map _ = Spec.map _
        rw [← Spec.map_comp]
        congr 1
        refine CommRingCat.hom_ext (RingHom.ext fun x => ?_)
        simp
      rw [← Category.assoc, e]
      refine (htan : _).trans ?_
      have hu : (toUnit (Over.mk (spMap (algebraMap O O)))).left = 𝟙 (Sp O) := by
        rw [Over.toUnit_left]; exact Spec.map_id _
      change η[A].left = (toUnit (Over.mk (spMap (algebraMap O O))) ≫ η[A]).left
      rw [Over.comp_left, hu]
      exact (Category.id_comp _).symm
    exact AlgHom.ext fun a => ((t.eq_one_iff n _).1 H a).trans (by simp)
  have e2 := hcn M n φ hφ w
  have e3 : Phi (GlobalTheory.GrpTangent.sqZeroMap mk ≫ v) h' w = 0 := by
    have tr : ∀ (z : TM O M ⟶ A) (hz : zeroSec O M ≫ z = η[A]), spOver φ ≫ t.y n = z →
        Phi z hz w = Phi (spOver φ ≫ t.y n) (zeroSec_spOver_y t n φ hφ) w := by
      rintro z hz rfl; rfl
    rw [tr _ h' hφy, e2, hw, map_zero]
  rw [e3, hl] at e1
  exact (Ideal.Quotient.eq_zero_iff_mem).1 e1.symm

end GlobalTheory.LieKer
