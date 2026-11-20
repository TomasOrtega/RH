import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreimageRegSet
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FlatBCSec
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

set_option autoImplicit false

namespace GlobalTheory.Desc.FlatLin

/- English proof (translation)
Simplify using `only [ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX, cst, RingHom.comp_apply, fnOf, Scheme.Hom.appLE, CommRingCat.hom_comp]`. Use `erw [TopCat.Presheaf.germ_res_apply]`. Both sides reduce to the same expression.
-/
theorem fnOf_algX {X : Scheme.{0}} [IsIntegral X] {R : Type} [CommRing R] (p : X ⟶ Sp R) (U : X.Opens)
    (hU : genericPoint X ∈ U) (r : R) :
    fnOf U hU (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p U r) = cst p r := by
  simp only [ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX, cst, RingHom.comp_apply, fnOf, Scheme.Hom.appLE,
    CommRingCat.hom_comp]
  erw [TopCat.Presheaf.germ_res_apply]
  rfl

/- English proof (translation)
Take `⟨l, h1, h2⟩` from `h`. Rewrite `h1` using `[Category.comp_id]`. Substitute `h1` using the available equality. Establish `eY : gp Y (closedPoint (Y.presheaf.stalk (genericPoint Y))) = genericPoint Y` using `Scheme.fromSpecStalk_closedPoint`. Establish `hc : (spMap θ) (closedPoint (Y.presheaf.stalk (genericPoint Y))) = closedPoint (X.presheaf.stalk (genericPoint X))` using `Subsingleton.elim (α := PrimeSpectrum X.functionField) _ _`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem gen_map {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] {π : Y ⟶ X}
    {θ : X.functionField →+* Y.functionField} (h : PFF (𝟙 _) π θ) : π (genericPoint Y) = genericPoint X := by
  obtain ⟨l, h1, h2⟩ := h
  rw [Category.comp_id] at h1
  subst h1
  have eY : gp Y (closedPoint (Y.presheaf.stalk (genericPoint Y))) = genericPoint Y :=
    Scheme.fromSpecStalk_closedPoint
  have hc : (spMap θ) (closedPoint (Y.presheaf.stalk (genericPoint Y))) =
      closedPoint (X.presheaf.stalk (genericPoint X)) :=
    Subsingleton.elim (α := PrimeSpectrum X.functionField) _ _
  calc π (genericPoint Y) = π (gp Y (closedPoint (Y.presheaf.stalk (genericPoint Y)))) := by rw [eY]
    _ = (gp Y ≫ π) (closedPoint (Y.presheaf.stalk (genericPoint Y))) := (Scheme.Hom.comp_apply _ _ _).symm
    _ = (spMap θ ≫ gp X) (closedPoint (Y.presheaf.stalk (genericPoint Y))) := by rw [h2]
    _ = gp X (spMap θ (closedPoint (Y.presheaf.stalk (genericPoint Y)))) := Scheme.Hom.comp_apply _ _ _
    _ = genericPoint X := by rw [hc]; exact Scheme.fromSpecStalk_closedPoint

/- English proof (translation)
Rewrite using `[GaussPt.theta_fnOf h U hU (e hV) a]`. Simplify using `only [fnOf, Scheme.Hom.appLE, CommRingCat.hom_comp, RingHom.comp_apply]`. Use `erw [TopCat.Presheaf.germ_res_apply]`.
-/
theorem fnOf_appLE {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] {π : Y ⟶ X}
    {θ : X.functionField →+* Y.functionField} (h : PFF (𝟙 _) π θ) (U : X.Opens) (V : Y.Opens)
    (e : V ≤ π ⁻¹ᵁ U) (hU : genericPoint X ∈ U) (hV : genericPoint Y ∈ V) (a : Γ(X, U)) :
    fnOf V hV ((π.appLE U V e).hom a) = θ (fnOf U hU a) := by
  rw [GaussPt.theta_fnOf h U hU (e hV) a]
  simp only [fnOf, Scheme.Hom.appLE, CommRingCat.hom_comp, RingHom.comp_apply]
  erw [TopCat.Presheaf.germ_res_apply]

/- English proof (translation)
Introduce `T D _ _ a ha H _ H' _ π θ hpb hθ n u hu r hr`. Use `letI : Algebra T D := a.toAlgebra`. Use `haveI : Module.Flat T D := ha`. Establish `hη : π (genericPoint H'.left) = genericPoint H.left` using `gen_map hθ`. Take `⟨U, hUa, hηU, -⟩` from `(TopologicalSpace.Opens.isBasis_iff_nbhd.1 H.left.isBasis_affineOpens) (show genericPoint H.left ∈ (⊤ : H.left.Opens) from trivial)`.

Use `haveI : Nonempty U := ⟨⟨_, hηU⟩⟩`. Use `haveI := functionField_isFractionRing_of_isAffineOpen H.left U hUa`. Take `⟨s, hs⟩` from `IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors Γ(H.left, U)) u`. Use `choose A hA using hs`. Establish `hA' : ∀ i, fnOf U hηU (A i) = fnOf U hηU s * u i` using `fun i => by`.

Use `hA i` as an intermediate fact. Rewrite `this` using `[Algebra.smul_def]`. Conclude with `this`. Establish `hs0 : fnOf U hηU s ≠ 0` using `IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.2`. Use `letI : Algebra T Γ(H.left, U) := (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX H.hom U).toAlgebra`.

Set `f : (Fin n → T) →ₗ[T] Γ(H.left, U)` to `{ toFun := fun c => ∑ i, c i • A i map_add' := fun c d => by simp [add_smul, Finset.sum_add_distrib] map_smul' := fun t c => by simp [Finset.smul_sum, smul_smul] }`. Establish `hf : Function.Injective f`. Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce `c hc`. Apply `hu c` to reduce the goal to its premises.

Establish `h1` using `congrArg (fnOf U hηU) hc`. Simplify using `only [f, LinearMap.coe_mk, AddHom.coe_mk, map_sum, map_zero, Algebra.smul_def, map_mul, RingHom.algebraMap_toAlgebra, fnOf_algX, hA'] at h1`. Establish `e : fnOf U hηU s * ∑ i, cst H.hom (c i) * u i = 0`. Rewrite using `[Finset.mul_sum, ← h1]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Expand and normalize the polynomial expressions, which then agree. Conclude with `(mul_eq_zero.1 e).resolve_left hs0`. Establish `hfD : Function.Injective (f.lTensor D)` using `Module.Flat.lTensor_preserves_injective_linearMap f hf`. Set `x` to `(TensorProduct.piScalarRight T T D (Fin n)).symm r`. Establish `hx : f.lTensor D x = ∑ i, r i ⊗ₜ[T] A i` using `by conv_lhs => rw [show x = ∑ i, (TensorProduct.piScalarRight T T D (Fin n)).symm (Pi.single i (r i)) by`.

Simplify using `only [x, ← map_sum, Finset.univ_sum_single]]`. Simplify using `only [TensorProduct.piScalarRight_symm_single, map_sum, LinearMap.lTensor_tmul]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Use `congr 1`. Simplify using `[f, Pi.single_apply]`.

Set `V' : H'.left.Opens` to `π ⁻¹ᵁ U ⊓ H'.hom ⁻¹ᵁ ⊤`. Establish `hV' : genericPoint H'.left ∈ V'` using `⟨show π _ ∈ U by rw [hη]; exact hηU, trivial⟩`. Set `E` to `ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.eTens H.hom H'.hom π hpb U hUa`. Set `y : TensorProduct T Γ(H.left, U) D` to `TensorProduct.comm T D Γ(H.left, U) (f.lTensor D x)`. Establish `hy : y = ∑ i, A i ⊗ₜ[T] r i`.

Simplify using `only [y, hx, map_sum, TensorProduct.comm_tmul]`. Establish `hEy : fnOf V' hV' (E y) = 0`. Rewrite using `[hy, map_sum, map_sum]`. Establish `step : ∀ i, fnOf V' hV' (E (A i ⊗ₜ[T] r i)) = θ (fnOf U hηU s * u i) * cst H'.hom (r i)` using `fun i => by`. Rewrite using `[show E (A i ⊗ₜ[T] r i) = _ from ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.eTens_tmul H.hom H'.hom π hpb U hUa (A i) (r i)]`.

Rewrite using `[map_mul, fnOf_appLE hθ U V' inf_le_left hηU hV', fnOf_algX, hA']`. Rewrite using `[Finset.sum_congr rfl fun i _ => step i]`. Establish `e : ∑ i, θ (fnOf U hηU s * u i) * cst H'.hom (r i) = θ (fnOf U hηU s) * ∑ i, cst H'.hom (r i) * θ (u i)`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[map_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, hr, mul_zero]`. Establish `hy0 : y = 0`. Establish `: E y = 0` using `fnOf_injective V' hV' (by rw [hEy, map_zero])`.

Conclude with `E.injective (this.trans E.map_zero.symm)`. Establish `hx0 : x = 0`. Apply `hfD` to reduce the goal to its premises. Rewrite using `[map_zero]`. Conclude with `(TensorProduct.comm T D Γ(H.left, U)).injective (hy0.trans (map_zero _).symm)`.

Establish `: r = (TensorProduct.piScalarRight T T D (Fin n)) x` using `by simp only [x, LinearEquiv.apply_symm_apply]`. Rewrite using `[this, hx0, map_zero]`.
-/
theorem linDisj_of_flat : ∀ (T D : Type) [CommRing T] [CommRing D] (a : T →+* D), a.Flat → ∀ (H : Over (Sp T)) [IsIntegral H.left] (H' : Over (Sp D)) [IsIntegral H'.left] (π : H'.left ⟶ H.left) (θ : H.left.functionField →+* H'.left.functionField), IsPullback π H'.hom H.hom (spMap a) → PFF (𝟙 _) π θ → LinDisj (GlobalTheory.Desc.cst H.hom) (GlobalTheory.Desc.cst H'.hom) θ := by
  intro T D _ _ a ha H _ H' _ π θ hpb hθ n u hu r hr
  classical
  letI : Algebra T D := a.toAlgebra
  haveI : Module.Flat T D := ha
  have hη : π (genericPoint H'.left) = genericPoint H.left := gen_map hθ
  obtain ⟨U, hUa, hηU, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.1 H.left.isBasis_affineOpens)
    (show genericPoint H.left ∈ (⊤ : H.left.Opens) from trivial)
  haveI : Nonempty U := ⟨⟨_, hηU⟩⟩
  haveI := functionField_isFractionRing_of_isAffineOpen H.left U hUa
  obtain ⟨s, hs⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors Γ(H.left, U)) u
  choose A hA using hs
  have hA' : ∀ i, fnOf U hηU (A i) = fnOf U hηU s * u i := fun i => by
    have := hA i; rw [Algebra.smul_def] at this; exact this
  have hs0 : fnOf U hηU s ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.2
  letI : Algebra T Γ(H.left, U) := (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX H.hom U).toAlgebra
  let f : (Fin n → T) →ₗ[T] Γ(H.left, U) :=
    { toFun := fun c => ∑ i, c i • A i
      map_add' := fun c d => by simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun t c => by simp [Finset.smul_sum, smul_smul] }
  have hf : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro c hc
    apply hu c
    have h1 := congrArg (fnOf U hηU) hc
    simp only [f, LinearMap.coe_mk, AddHom.coe_mk, map_sum, map_zero, Algebra.smul_def, map_mul,
      RingHom.algebraMap_toAlgebra, fnOf_algX, hA'] at h1
    have e : fnOf U hηU s * ∑ i, cst H.hom (c i) * u i = 0 := by
      rw [Finset.mul_sum, ← h1]; refine Finset.sum_congr rfl fun i _ => ?_; ring
    exact (mul_eq_zero.1 e).resolve_left hs0
  have hfD : Function.Injective (f.lTensor D) := Module.Flat.lTensor_preserves_injective_linearMap f hf
  let x := (TensorProduct.piScalarRight T T D (Fin n)).symm r
  have hx : f.lTensor D x = ∑ i, r i ⊗ₜ[T] A i := by
    conv_lhs => rw [show x = ∑ i, (TensorProduct.piScalarRight T T D (Fin n)).symm (Pi.single i (r i)) by
      simp only [x, ← map_sum, Finset.univ_sum_single]]
    simp only [TensorProduct.piScalarRight_symm_single, map_sum, LinearMap.lTensor_tmul]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    simp [f, Pi.single_apply]
  let V' : H'.left.Opens := π ⁻¹ᵁ U ⊓ H'.hom ⁻¹ᵁ ⊤
  have hV' : genericPoint H'.left ∈ V' := ⟨show π _ ∈ U by rw [hη]; exact hηU, trivial⟩
  let E := ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.eTens H.hom H'.hom π hpb U hUa
  let y : TensorProduct T Γ(H.left, U) D := TensorProduct.comm T D Γ(H.left, U) (f.lTensor D x)
  have hy : y = ∑ i, A i ⊗ₜ[T] r i := by
    simp only [y, hx, map_sum, TensorProduct.comm_tmul]
  have hEy : fnOf V' hV' (E y) = 0 := by
    rw [hy, map_sum, map_sum]
    have step : ∀ i, fnOf V' hV' (E (A i ⊗ₜ[T] r i)) = θ (fnOf U hηU s * u i) * cst H'.hom (r i) := fun i => by
      rw [show E (A i ⊗ₜ[T] r i) = _ from ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.eTens_tmul H.hom H'.hom π hpb U hUa (A i) (r i)]
      rw [map_mul, fnOf_appLE hθ U V' inf_le_left hηU hV', fnOf_algX, hA']
    rw [Finset.sum_congr rfl fun i _ => step i]
    have e : ∑ i, θ (fnOf U hηU s * u i) * cst H'.hom (r i) =
        θ (fnOf U hηU s) * ∑ i, cst H'.hom (r i) * θ (u i) := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_; rw [map_mul]; ring
    rw [e, hr, mul_zero]
  have hy0 : y = 0 := by
    have : E y = 0 := fnOf_injective V' hV' (by rw [hEy, map_zero])
    exact E.injective (this.trans E.map_zero.symm)
  have hx0 : x = 0 := by
    apply hfD
    rw [map_zero]
    exact (TensorProduct.comm T D Γ(H.left, U)).injective (hy0.trans (map_zero _).symm)
  have : r = (TensorProduct.piScalarRight T T D (Fin n)) x := by simp only [x, LinearEquiv.apply_symm_apply]
  rw [this, hx0, map_zero]

end GlobalTheory.Desc.FlatLin
