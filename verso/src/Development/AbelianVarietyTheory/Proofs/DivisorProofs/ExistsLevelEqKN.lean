import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Classify
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.T2SpaceTensorRatFiniteAlgebraModuleTopology
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField Matrix IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.DiscreteGroups.LocalClassField
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo
open scoped TensorProduct
open scoped Classical

open scoped RestrictedProduct
set_option autoImplicit false
noncomputable section

namespace GlobalTheory.LKGeo.KNLevel

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {κ : Type} [Fintype κ] [DecidableEq κ]

abbrev bA (b : Module.Basis κ ℤ D.La) : Module.Basis κ (AfP p) (AfP p ⊗[ℚ] VQ D) :=
  Algebra.TensorProduct.basis (AfP p) (Algebra.TensorProduct.basis ℚ b)

/- English proof (translation)
Simplify using `[bA, Algebra.TensorProduct.basis_apply, inAf]`.
-/
theorem bA_apply (b : Module.Basis κ ℤ D.La) (i : κ) : bA (p := p) b i = inAf D (b i) := by
  simp [bA, Algebra.TensorProduct.basis_apply, inAf]

/- English proof (translation)
Proceed by induction on `hu using AddSubgroup.closure_induction with`. Consider the case `mem u hu`. Take `⟨a, x, ha, rfl⟩` from `hu`. Introduce `v`. Rewrite using `[Algebra.TensorProduct.basis_repr_tmul, Finsupp.smul_apply, Finsupp.mapRange_apply, Algebra.TensorProduct.basis_repr_tmul, Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul, one_smul, eq_intCast (algebraMap ℤ ℚ), map_intCast, map_mul, map_intCast]`.

Conclude with `mul_mem (ha v) (intCast_mem _ _)`. Consider the case `zero => intro v`. Rewrite using `[map_zero, Finsupp.zero_apply, map_zero]`. Conclude with `zero_mem _`. Consider the case `add u u' _ _ hu hu' => intro v`.

Rewrite using `[map_add, Finsupp.add_apply, map_add]`. Conclude with `add_mem (hu v) (hu' v)`. Consider the case `neg u _ hu => intro v`. Rewrite using `[map_neg, Finsupp.neg_apply, map_neg]`. Conclude with `neg_mem (hu v)`.
-/
theorem repr_isIntAf (b : Module.Basis κ ℤ D.La) (u : AfP p ⊗[ℚ] VQ D) (hu : u ∈ LaHat D) (i : κ) :
    IsIntAf ((bA b).repr u i) := by
  induction hu using AddSubgroup.closure_induction with
  | mem u hu =>
    obtain ⟨a, x, ha, rfl⟩ := hu
    intro v
    rw [Algebra.TensorProduct.basis_repr_tmul, Finsupp.smul_apply, Finsupp.mapRange_apply,
      Algebra.TensorProduct.basis_repr_tmul, Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul, one_smul,
      eq_intCast (algebraMap ℤ ℚ), map_intCast, map_mul, map_intCast]
    exact mul_mem (ha v) (intCast_mem _ _)
  | zero => intro v; rw [map_zero, Finsupp.zero_apply, map_zero]; exact zero_mem _
  | add u u' _ _ hu hu' => intro v; rw [map_add, Finsupp.add_apply, map_add]; exact add_mem (hu v) (hu' v)
  | neg u _ hu => intro v; rw [map_neg, Finsupp.neg_apply, map_neg]; exact neg_mem (hu v)

/- English proof (translation)
Rewrite using `[← (bA b).sum_repr u]`. Use `sum_mem fun i _ => AddSubgroup.subset_closure ⟨(bA b).repr u i, b i, hu i, ?_⟩` and prove the remaining obligations. Rewrite using `[Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one, Algebra.TensorProduct.basis_apply]`.
-/
theorem mem_laHat_of_repr (b : Module.Basis κ ℤ D.La) (u : AfP p ⊗[ℚ] VQ D)
    (hu : ∀ i, IsIntAf ((bA b).repr u i)) : u ∈ LaHat D := by
  rw [← (bA b).sum_repr u]
  refine sum_mem fun i _ => AddSubgroup.subset_closure ⟨(bA b).repr u i, b i, hu i, ?_⟩
  rw [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one,
    Algebra.TensorProduct.basis_apply]

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun h i => repr_isIntAf b u h i, mem_laHat_of_repr b u⟩`.
-/
theorem mem_laHat_iff (b : Module.Basis κ ℤ D.La) (u : AfP p ⊗[ℚ] VQ D) :
    u ∈ LaHat D ↔ ∀ i, IsIntAf ((bA b).repr u i) :=
  ⟨fun h i => repr_isIntAf b u h i, mem_laHat_of_repr b u⟩

variable {G : HTGroup p}

def matL (b : Module.Basis κ ℤ D.La) (L : Link D G) : (AfP p ⊗[ℚ] G.C) →ₗ[AfP p] Matrix κ κ (AfP p) :=
  (LinearMap.toMatrix (bA b) (bA b)).toLinearMap ∘ₗ (actOn L.rep (AfP p)).toLinearMap

/- English proof (translation)
Establish `h : actOn L.rep (AfP p) (a ⊗ₜ c) = a • (L.rep c).baseChange (AfP p)`. Simplify using `[actOn, Algebra.TensorProduct.lift_tmul, Algebra.smul_def]`. Both sides reduce to the same expression. Simplify using `only [matL, LinearMap.coe_comp, LinearEquiv.coe_coe, AlgHom.toLinearMap_apply, Function.comp_apply, h, map_smul, LinearMap.toMatrix_baseChange]`.
-/
theorem matL_tmul (b : Module.Basis κ ℤ D.La) (L : Link D G) (a : AfP p) (c : G.C) :
    matL b L (a ⊗ₜ c) = a • (LinearMap.toMatrix (Algebra.TensorProduct.basis ℚ b)
      (Algebra.TensorProduct.basis ℚ b) (L.rep c)).map (algebraMap ℚ (AfP p)) := by
  have h : actOn L.rep (AfP p) (a ⊗ₜ c) = a • (L.rep c).baseChange (AfP p) := by
    simp [actOn, Algebra.TensorProduct.lift_tmul, Algebra.smul_def]
    rfl
  simp only [matL, LinearMap.coe_comp, LinearEquiv.coe_coe, AlgHom.toLinearMap_apply, Function.comp_apply, h,
    map_smul, LinearMap.toMatrix_baseChange]

end GlobalTheory.LKGeo.KNLevel

namespace GlobalTheory.LKGeo.KNLevel

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {κ : Type} [Fintype κ] [DecidableEq κ] {G : HTGroup p}

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem isIntAf_iff (a : AfP p) : IsIntAf a ↔ a ∈ LevelExists.intAfP p := Iff.rfl

/- English proof (translation)
Rewrite using `[bA_apply]`. Use `AddSubgroup.subset_closure ⟨1, b j, fun v => ?_, rfl⟩` and prove the remaining obligations. Rewrite using `[map_one]`. Conclude with `one_mem _`.
-/
theorem bA_mem (b : Module.Basis κ ℤ D.La) (j : κ) : bA (p := p) b j ∈ LaHat D := by
  rw [bA_apply]
  refine AddSubgroup.subset_closure ⟨1, b j, fun v => ?_, rfl⟩
  rw [map_one]; exact one_mem _

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem actG_eq (L : Link D G) (g : G.GAf) :
    L.actG g = actOn L.rep (AfP p) (((g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 : (AfP p ⊗[ℚ] G.C)ˣ) :
      AfP p ⊗[ℚ] G.C) := rfl

/- English proof (translation)
Rewrite using `[actG_eq]`. Simplify using `only [matL, LinearMap.coe_comp, LinearEquiv.coe_coe, AlgHom.toLinearMap_apply, Function.comp_apply, LinearMap.toMatrix_apply]`.
-/
theorem matL_apply (b : Module.Basis κ ℤ D.La) (L : Link D G) (g : G.GAf) (i j : κ) :
    matL b L (((g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C) i j =
      (bA b).repr (L.actG g (bA b j)) i := by
  rw [actG_eq]
  simp only [matL, LinearMap.coe_comp, LinearEquiv.coe_coe, AlgHom.toLinearMap_apply, Function.comp_apply,
    LinearMap.toMatrix_apply]

/- English proof (translation)
Take `⟨w, hw, e⟩` from `h (bA b j) (bA_mem b j)`. Rewrite using `[matL_apply, e, map_add, map_nsmul, Finsupp.add_apply, Finsupp.smul_apply, isIntAf_iff]`. Conclude with `add_mem (repr_isIntAf b _ (bA_mem b j) i) (nsmul_mem (repr_isIntAf b w hw i) N)`.
-/
theorem int_of_congOne (b : Module.Basis κ ℤ D.La) (L : Link D G) {N : ℕ} {g : G.GAf} (h : L.CongOne N g)
    (i j : κ) :
    IsIntAf (matL b L (((g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C) i j) := by
  obtain ⟨w, hw, e⟩ := h (bA b j) (bA_mem b j)
  rw [matL_apply, e, map_add, map_nsmul, Finsupp.add_apply, Finsupp.smul_apply, isIntAf_iff]
  exact add_mem (repr_isIntAf b _ (bA_mem b j) i) (nsmul_mem (repr_isIntAf b w hw i) N)

/- English proof (translation)
Introduce `v hv`. Use `set X := matL b L (((g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C) with hXdef`. Use `set W : Matrix κ κ (AfP p) := (N : ℚ)⁻¹ • (X - 1) with hW`. Use `set c : κ → AfP p := ⇑((bA b).repr v) with hc`. Establish `hcI : ∀ j, c j ∈ LevelExists.intAfP p` using `fun j => repr_isIntAf b v hv j`.

Use `⟨(bA b).equivFun.symm (W *ᵥ c), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[mem_laHat_iff b]`. Introduce `i`. Rewrite using `[← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply, isIntAf_iff]`. Conclude with `sum_mem fun j _ => mul_mem (h i j) (hcI j)`.

Establish `hN' : (N : ℚ) ≠ 0` using `by exact_mod_cast hN.ne'`. Establish `hX : X = 1 + N • W`. Rewrite using `[hW, ← Nat.cast_smul_eq_nsmul ℚ, smul_smul, mul_inv_cancel₀ hN', one_smul, add_sub_cancel]`. Apply `(bA b).equivFun.injective` to reduce the goal to its premises. Establish `e1 : (bA b).equivFun (L.actG g v) = X *ᵥ c`.

Rewrite using `[Module.Basis.equivFun_apply, hc, hXdef, actG_eq]`. Conclude with `(LinearMap.toMatrix_mulVec_repr (bA b) (bA b) _ v).symm`. Rewrite using `[e1, map_add, map_nsmul, LinearEquiv.apply_symm_apply, hX, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, Module.Basis.equivFun_apply]`.
-/
theorem congOne_of_mat (b : Module.Basis κ ℤ D.La) (L : Link D G) {N : ℕ} (hN : 0 < N) {g : G.GAf}
    (h : ∀ i j, IsIntAf (((N : ℚ)⁻¹ • (matL b L (((g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 : (AfP p ⊗[ℚ] G.C)ˣ) :
      AfP p ⊗[ℚ] G.C) - 1)) i j)) : L.CongOne N g := by
  intro v hv
  set X := matL b L (((g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C) with hXdef
  set W : Matrix κ κ (AfP p) := (N : ℚ)⁻¹ • (X - 1) with hW
  set c : κ → AfP p := ⇑((bA b).repr v) with hc
  have hcI : ∀ j, c j ∈ LevelExists.intAfP p := fun j => repr_isIntAf b v hv j
  refine ⟨(bA b).equivFun.symm (W *ᵥ c), ?_, ?_⟩
  · rw [mem_laHat_iff b]
    intro i
    rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply, isIntAf_iff]
    exact sum_mem fun j _ => mul_mem (h i j) (hcI j)
  · have hN' : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
    have hX : X = 1 + N • W := by
      rw [hW, ← Nat.cast_smul_eq_nsmul ℚ, smul_smul, mul_inv_cancel₀ hN', one_smul, add_sub_cancel]
    apply (bA b).equivFun.injective
    have e1 : (bA b).equivFun (L.actG g v) = X *ᵥ c := by
      rw [Module.Basis.equivFun_apply, hc, hXdef, actG_eq]
      exact (LinearMap.toMatrix_mulVec_repr (bA b) (bA b) _ v).symm
    rw [e1, map_add, map_nsmul, LinearEquiv.apply_symm_apply, hX, Matrix.add_mulVec, Matrix.one_mulVec,
      Matrix.smul_mulVec, Module.Basis.equivFun_apply]

end GlobalTheory.LKGeo.KNLevel

namespace GlobalTheory.LKGeo.KNLevel

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {κ : Type} [Fintype κ] [DecidableEq κ] {G : HTGroup p}

section Top

local instance instTopT : TopologicalSpace (AfP p ⊗[ℚ] G.C) := moduleTopology (AfP p) _
local instance instModTopT : IsModuleTopology (AfP p) (AfP p ⊗[ℚ] G.C) := ⟨rfl⟩
local instance instTopRingT : IsTopologicalRing (AfP p ⊗[ℚ] G.C) := IsModuleTopology.isTopologicalRing (AfP p) _

/- English proof (translation)
The claim follows from `IsModuleTopology.continuous_of_linearMap (matL b L)`.
-/
theorem continuous_matL (b : Module.Basis κ ℤ D.La) (L : Link D G) : Continuous (matL b L) :=
  IsModuleTopology.continuous_of_linearMap (matL b L)

/- English proof (translation)
Use `set bQ := Algebra.TensorProduct.basis ℚ b`. Use `set T : G.C →ₗ[ℚ] Matrix κ κ ℚ := (LinearMap.toMatrix bQ bQ).toLinearMap ∘ₗ L.rep.toLinearMap with hT`. Establish `hker : LinearMap.ker T = ⊥`. Rewrite using `[LinearMap.ker_eq_bot]`. Conclude with `(LinearMap.toMatrix bQ bQ).injective.comp L.rep_inj`.

Take `⟨T', hT'⟩` from `LinearMap.exists_leftInverse_of_injective T hker`. Establish `hTT : ∀ c, T' (T c) = c` using `fun c => by`. Use `congrArg (fun f => f c) hT'` as an intermediate fact. Simplify using `using this`. Use `⟨fun X => ∑ i, ∑ j, X i j • ((1 : AfP p) ⊗ₜ[ℚ] T' (Matrix.single i j 1)), ?_, ?_⟩` and prove the remaining obligations.

Conclude with `continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => Continuous.smul (f := fun X : Matrix κ κ (AfP p) => X i j) (g := fun _ => (1 : AfP p) ⊗ₜ[ℚ] T' (Matrix.single i j 1)) (continuous_id.matrix_elem i j) continuous_const`. Introduce `y`. Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add x y hx hy => dsimp only at hx hy ⊢`.

Rewrite using `[map_add]`. Simplify using `only [Matrix.add_apply, add_smul, Finset.sum_add_distrib, hx, hy]`. Consider the case `tmul a c`. Rewrite using `[matL_tmul]`. Establish `e1 : a ⊗ₜ[ℚ] c = a • ((1 : AfP p) ⊗ₜ[ℚ] T' (T c))`.

Rewrite using `[hTT, TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]`. Rewrite using `[e1, Matrix.matrix_eq_sum_single (T c)]`. Simplify using `only [map_sum, TensorProduct.tmul_sum, Finset.smul_sum, Matrix.smul_apply, Matrix.map_apply]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[show Matrix.single i j (T c i j) = (T c i j) • Matrix.single i j (1 : ℚ) by`.

Rewrite using `[Matrix.smul_single, smul_eq_mul, _root_.mul_one], map_smul, TensorProduct.tmul_smul,`. Use the proof step `← algebraMap_smul (AfP p) (T c i j), smul_smul, smul_eq_mul]`. Both sides reduce to the same expression.
-/
theorem exists_leftInv (b : Module.Basis κ ℤ D.La) (L : Link D G) :
    ∃ lam : Matrix κ κ (AfP p) → AfP p ⊗[ℚ] G.C, Continuous lam ∧ ∀ y, lam (matL b L y) = y := by
  set bQ := Algebra.TensorProduct.basis ℚ b
  set T : G.C →ₗ[ℚ] Matrix κ κ ℚ := (LinearMap.toMatrix bQ bQ).toLinearMap ∘ₗ L.rep.toLinearMap with hT
  have hker : LinearMap.ker T = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    exact (LinearMap.toMatrix bQ bQ).injective.comp L.rep_inj
  obtain ⟨T', hT'⟩ := LinearMap.exists_leftInverse_of_injective T hker
  have hTT : ∀ c, T' (T c) = c := fun c => by
    have := congrArg (fun f => f c) hT'
    simpa using this
  refine ⟨fun X => ∑ i, ∑ j, X i j • ((1 : AfP p) ⊗ₜ[ℚ] T' (Matrix.single i j 1)), ?_, ?_⟩
  · exact continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ =>
      Continuous.smul (f := fun X : Matrix κ κ (AfP p) => X i j)
        (g := fun _ => (1 : AfP p) ⊗ₜ[ℚ] T' (Matrix.single i j 1)) (continuous_id.matrix_elem i j) continuous_const
  · intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy =>
      dsimp only at hx hy ⊢
      rw [map_add]
      simp only [Matrix.add_apply, add_smul, Finset.sum_add_distrib, hx, hy]
    | tmul a c =>
      rw [matL_tmul]
      have e1 : a ⊗ₜ[ℚ] c = a • ((1 : AfP p) ⊗ₜ[ℚ] T' (T c)) := by
        rw [hTT, TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
      rw [e1, Matrix.matrix_eq_sum_single (T c)]
      simp only [map_sum, TensorProduct.tmul_sum, Finset.smul_sum, Matrix.smul_apply, Matrix.map_apply]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [show Matrix.single i j (T c i j) = (T c i j) • Matrix.single i j (1 : ℚ) by
        rw [Matrix.smul_single, smul_eq_mul, _root_.mul_one], map_smul, TensorProduct.tmul_smul,
        ← algebraMap_smul (AfP p) (T c i j), smul_smul, smul_eq_mul]
      rfl

/- English proof (translation)
Use `set b0 := Module.finBasis ℚ G.C`. Use `set bC := Algebra.TensorProduct.basis (AfP p) b0`. Establish `h1 : b0.repr 1 ≠ 0` using `(LinearEquiv.map_ne_zero_iff b0.repr).2 one_ne_zero`. Take `⟨k, hk⟩` from `Finsupp.ne_iff.1 h1`. Rewrite `hk` using `[Finsupp.zero_apply]`.

Use `⟨fun y => algebraMap ℚ (AfP p) (b0.repr 1 k)⁻¹ * bC.coord k y, ?_, ?_⟩` and prove the remaining obligations. Conclude with `continuous_const.mul (IsModuleTopology.continuous_of_linearMap (bC.coord k))`. Introduce `s`. Establish `e : algebraMap (AfP p) (AfP p ⊗[ℚ] G.C) s = s ⊗ₜ[ℚ] (1 : G.C)`. Rewrite using `[Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]`.

Simplify using `only [e, Module.Basis.coord_apply, bC, Algebra.TensorProduct.basis_repr_tmul, Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul]`. Rewrite using `[mul_comm s, ← _root_.mul_assoc, ← map_mul, inv_mul_cancel₀ hk, map_one, _root_.one_mul]`.
-/
theorem exists_simInv :
    ∃ mu : AfP p ⊗[ℚ] G.C → AfP p, Continuous mu ∧ ∀ s, mu (algebraMap (AfP p) (AfP p ⊗[ℚ] G.C) s) = s := by
  set b0 := Module.finBasis ℚ G.C
  set bC := Algebra.TensorProduct.basis (AfP p) b0
  have h1 : b0.repr 1 ≠ 0 := (LinearEquiv.map_ne_zero_iff b0.repr).2 one_ne_zero
  obtain ⟨k, hk⟩ := Finsupp.ne_iff.1 h1
  rw [Finsupp.zero_apply] at hk
  refine ⟨fun y => algebraMap ℚ (AfP p) (b0.repr 1 k)⁻¹ * bC.coord k y, ?_, ?_⟩
  · exact continuous_const.mul (IsModuleTopology.continuous_of_linearMap (bC.coord k))
  · intro s
    have e : algebraMap (AfP p) (AfP p ⊗[ℚ] G.C) s = s ⊗ₜ[ℚ] (1 : G.C) := by
      rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
    simp only [e, Module.Basis.coord_apply, bC, Algebra.TensorProduct.basis_repr_tmul, Finsupp.smul_apply,
      Finsupp.mapRange_apply, smul_eq_mul]
    rw [mul_comm s, ← _root_.mul_assoc, ← map_mul, inv_mul_cancel₀ hk, map_one, _root_.one_mul]

/- English proof (translation)
Take `⟨lam, hlam, hl⟩` from `exists_leftInv b L`. Use `set box : Set (Matrix κ κ (AfP p)) := Set.univ.pi fun _ => Set.univ.pi fun _ => (LevelExists.intAfP p : Set (AfP p)) with hbox`. Establish `hset : {y : AfP p ⊗[ℚ] G.C | ∀ i j, IsIntAf (matL b L y i j)} = matL b L ⁻¹' box`. Use extensionality with `y`. Prove the components needed by the constructor for the conclusion.

Introduce `h i _ j _`. Conclude with `h i j`. Introduce `h i j`. Conclude with `h i trivial j trivial`. Establish `hOcl : IsClosed (LevelExists.intAfP p : Set (AfP p))` using `AddSubgroup.isClosed_of_isOpen (LevelExists.intAfP p).toAddSubgroup (LevelExists.isOpen_intAfP p)`.

Establish `hboxcl : IsClosed box` using `isClosed_set_pi fun _ _ => isClosed_set_pi fun _ _ => hOcl`. Establish `hboxc : IsCompact box` using `isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => LevelExists.isCompact_intAfP p`. Rewrite using `[hset]`. Use `(hboxc.image hlam).of_isClosed_subset (hboxcl.preimage (continuous_matL b L)) ?_` and prove the remaining obligations. Introduce `y hy`.

Conclude with `⟨matL b L y, hy, hl y⟩`.
-/
theorem isCompact_intSet (b : Module.Basis κ ℤ D.La) (L : Link D G) :
    IsCompact {y : AfP p ⊗[ℚ] G.C | ∀ i j, IsIntAf (matL b L y i j)} := by
  obtain ⟨lam, hlam, hl⟩ := exists_leftInv b L
  set box : Set (Matrix κ κ (AfP p)) :=
    Set.univ.pi fun _ => Set.univ.pi fun _ => (LevelExists.intAfP p : Set (AfP p)) with hbox
  have hset : {y : AfP p ⊗[ℚ] G.C | ∀ i j, IsIntAf (matL b L y i j)} = matL b L ⁻¹' box := by
    ext y
    constructor
    · intro h i _ j _; exact h i j
    · intro h i j; exact h i trivial j trivial
  have hOcl : IsClosed (LevelExists.intAfP p : Set (AfP p)) :=
    AddSubgroup.isClosed_of_isOpen (LevelExists.intAfP p).toAddSubgroup (LevelExists.isOpen_intAfP p)
  have hboxcl : IsClosed box := isClosed_set_pi fun _ _ => isClosed_set_pi fun _ _ => hOcl
  have hboxc : IsCompact box := isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => LevelExists.isCompact_intAfP p
  rw [hset]
  refine (hboxc.image hlam).of_isClosed_subset (hboxcl.preimage (continuous_matL b L)) ?_
  intro y hy
  exact ⟨matL b L y, hy, hl y⟩

/- English proof (translation)
Introduce `p _ D G L N hN`. Use `haveI := D.freeLa`. Use `haveI := D.finLa`. Use `set b := Module.Free.chooseBasis ℤ D.La`. Use `haveI : T2Space (AfP p) := inferInstanceAs (T2Space (Πʳ v : AwayP p, [v.1.adicCompletion ℚ, v.1.adicCompletionIntegers ℚ]))`.

Use `haveI : T2Space (AfP p ⊗[ℚ] G.C) := LevelExists.t2Space_tensor_rat_finite_algebra_moduleTopology (AfP p) G.C`. Use `set xg : G.GAf → AfP p ⊗[ℚ] G.C := fun g => (((g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C) with hxgdef`. Establish `hxg : Continuous xg` using `Units.continuous_val.comp (continuous_fst.comp continuous_subtype_val)`. Establish `hxgi : Continuous (fun g : G.GAf => xg g⁻¹)` using `hxg.comp continuous_inv`. Use `set box : Set (Matrix (Module.Free.ChooseBasisIndex ℤ D.La) (Module.Free.ChooseBasisIndex ℤ D.La) (AfP p)) := Set.univ.pi fun _ => Set.univ.pi fun _ => (LevelExists.intAfP p : Set (AfP p)) with hbox`.

Establish `hboxo : IsOpen box` using `isOpen_set_pi Set.finite_univ fun _ _ => isOpen_set_pi Set.finite_univ fun _ _ => LevelExists.isOpen_intAfP p`. Use `set F : Matrix (Module.Free.ChooseBasisIndex ℤ D.La) (Module.Free.ChooseBasisIndex ℤ D.La) (AfP p) → Matrix (Module.Free.ChooseBasisIndex ℤ D.La) (Module.Free.ChooseBasisIndex ℤ D.La) (AfP p) := fun X => (N : ℚ)⁻¹ • (X - 1) with hFdef`. Establish `hF : Continuous F`. Establish `e : F = fun X => algebraMap ℚ (AfP p) (N : ℚ)⁻¹ • (X - 1)`. Use function extensionality and compare the values at `X`.

Rewrite using `[hFdef, algebraMap_smul]`. Rewrite using `[e]`. Use `fun_prop`. Use `set U : Set G.GAf := {g | F (matL b L (xg g)) ∈ box ∧ F (matL b L (xg g⁻¹)) ∈ box} with hU`. Establish `hUo : IsOpen U` using `(hboxo.preimage (hF.comp ((continuous_matL b L).comp hxg))).inter (hboxo.preimage (hF.comp ((continuous_matL b L).comp hxgi)))`.

Establish `hm1 : matL b L (xg 1) = 1`. Establish `: xg 1 = 1` using `rfl`. Rewrite using `[this]`. Simplify using `[matL, LinearMap.toMatrix_one]`. Establish `h1U : (1 : G.GAf) ∈ U`.

Establish `h0 : F (matL b L (xg 1)) ∈ box`. Rewrite using `[hm1, hFdef]`. Simplify using `only [sub_self, smul_zero]`. Conclude with `fun i _ j _ => zero_mem _`. Use `⟨h0, ?_⟩` and prove the remaining obligations.

Rewrite using `[inv_one]`. Conclude with `h0`. Establish `hUK : U ⊆ L.KN N` using `fun g hg => ⟨congOne_of_mat b L hN (fun i j => hg.1 i trivial j trivial), congOne_of_mat b L hN (fun i j => hg.2 i trivial j trivial)⟩`. Establish `hopen : IsOpen (L.KN N : Set G.GAf)` using `Subgroup.isOpen_of_mem_nhds _ (g := 1) (Filter.mem_of_superset (hUo.mem_nhds h1U) hUK)`. Take `⟨mu, hmu, hmuj⟩` from `exists_simInv (p := p) (G := G)`.

Use `set P' := {y : AfP p ⊗[ℚ] G.C | ∀ i j, IsIntAf (matL b L y i j)} with hP'def`. Establish `hP' : IsCompact P'` using `isCompact_intSet b L`. Establish `hσ : Continuous (fun y : AfP p ⊗[ℚ] G.C ↦ (starT G.star (AfP p) y).unop)`. Set `σl : (AfP p ⊗[ℚ] G.C) →ₗ[AfP p] (AfP p ⊗[ℚ] G.C)` to `{ toFun := fun y ↦ (starT G.star (AfP p) y).unop map_add' := fun x y ↦ by simp only [map_add, MulOpposite.unop_add] map_smul' := by`. Introduce `r x`.

Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a y`. Simplify using `only [TensorProduct.smul_tmul', smul_eq_mul, starT_tmul, RingHom.id_apply]`. Consider the case `add x y hx hy => simp only [smul_add, map_add, MulOpposite.unop_add, hx, hy, RingHom.id_apply] }`.

Conclude with `IsModuleTopology.continuous_of_linearMap σl`. Establish `hj : Continuous (algebraMap (AfP p) (AfP p ⊗[ℚ] G.C))` using `IsModuleTopology.continuous_of_linearMap (Algebra.linearMap (AfP p) (AfP p ⊗[ℚ] G.C))`. Use `set S₁ := (fun y : AfP p ⊗[ℚ] G.C => mu (y * (starT G.star (AfP p) y).unop)) '' P' with hS₁def`. Establish `hS₁ : IsCompact S₁` using `hP'.image (hmu.comp (continuous_id.mul hσ))`. Establish `hGcl : IsClosed (UPts G.star (AfP p) : Set ((AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ))`.

Apply `isClosed_eq` to reduce the goal to its premises. Conclude with `(Units.continuous_val.comp continuous_fst).mul (hσ.comp (Units.continuous_val.comp continuous_fst))`. Conclude with `hj.comp (Units.continuous_val.comp continuous_snd)`. Set `gE : G.GAf → ((AfP p ⊗[ℚ] G.C) × (AfP p ⊗[ℚ] G.C)ᵐᵒᵖ) × (AfP p × (AfP p)ᵐᵒᵖ)` to `fun x ↦ (Units.embedProduct _ x.1.1, Units.embedProduct _ x.1.2)`. Establish `hg : Topology.IsClosedEmbedding gE` using `(Units.isClosedEmbedding_embedProduct.prodMap Units.isClosedEmbedding_embedProduct).comp hGcl.isClosedEmbedding_subtypeVal`.

Use `set C' := (P' ×ˢ (MulOpposite.opHomeomorph.symm ⁻¹' P')) ×ˢ (S₁ ×ˢ (MulOpposite.opHomeomorph.symm ⁻¹' S₁)) with hC'`. Establish `hK0 : IsCompact (gE ⁻¹' C')` using `hg.isCompact_preimage ((hP'.prod (MulOpposite.opHomeomorph.symm.isCompact_preimage.2 hP')).prod (hS₁.prod (MulOpposite.opHomeomorph.symm.isCompact_preimage.2 hS₁)))`. Establish `hsub : (L.KN N : Set G.GAf) ⊆ gE ⁻¹' C'`. Introduce `g hgK`. Establish `hx : xg g ∈ P'` using `int_of_congOne b L hgK.1`.

Establish `hxi : xg g⁻¹ ∈ P'` using `int_of_congOne b L hgK.2`. Establish `hm : ∀ h : G.GAf, mu (xg h * (starT G.star (AfP p) (xg h)).unop) = (((h : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).2 : (AfP p)ˣ) : AfP p)`. Introduce `h`. Establish `e : xg h * (starT G.star (AfP p) (xg h)).unop = algebraMap (AfP p) (AfP p ⊗[ℚ] G.C) (((h : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).2 : (AfP p)ˣ) : AfP p)` using `h.2`. Rewrite using `[e, hmuj]`.

Use `⟨⟨hx, hxi⟩, ⟨xg g, hx, hm g⟩, ⟨xg g⁻¹, hxi, hm g⁻¹⟩⟩` and prove the remaining obligations. Establish `hKcl : IsClosed (L.KN N : Set G.GAf)` using `Subgroup.isClosed_of_isOpen _ hopen`. Conclude with `⟨⟨⟨L.KN N, hopen⟩, hK0.of_isClosed_subset hKcl hsub⟩, rfl⟩`.
-/
theorem exists_level_eq_KN : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (N : ℕ),
    0 < N → ∃ Lv : G.Level, Lv.K.toSubgroup = L.KN N := by
  intro p _ D G L N hN
  haveI := D.freeLa
  haveI := D.finLa
  set b := Module.Free.chooseBasis ℤ D.La
  haveI : T2Space (AfP p) := inferInstanceAs
    (T2Space (Πʳ v : AwayP p, [v.1.adicCompletion ℚ, v.1.adicCompletionIntegers ℚ]))
  haveI : T2Space (AfP p ⊗[ℚ] G.C) := LevelExists.t2Space_tensor_rat_finite_algebra_moduleTopology (AfP p) G.C
  set xg : G.GAf → AfP p ⊗[ℚ] G.C :=
    fun g => (((g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C) with hxgdef
  have hxg : Continuous xg := Units.continuous_val.comp (continuous_fst.comp continuous_subtype_val)
  have hxgi : Continuous (fun g : G.GAf => xg g⁻¹) := hxg.comp continuous_inv

  set box : Set (Matrix (Module.Free.ChooseBasisIndex ℤ D.La) (Module.Free.ChooseBasisIndex ℤ D.La) (AfP p)) :=
    Set.univ.pi fun _ => Set.univ.pi fun _ => (LevelExists.intAfP p : Set (AfP p)) with hbox
  have hboxo : IsOpen box := isOpen_set_pi Set.finite_univ fun _ _ =>
    isOpen_set_pi Set.finite_univ fun _ _ => LevelExists.isOpen_intAfP p
  set F : Matrix (Module.Free.ChooseBasisIndex ℤ D.La) (Module.Free.ChooseBasisIndex ℤ D.La) (AfP p) →
      Matrix (Module.Free.ChooseBasisIndex ℤ D.La) (Module.Free.ChooseBasisIndex ℤ D.La) (AfP p) :=
    fun X => (N : ℚ)⁻¹ • (X - 1) with hFdef
  have hF : Continuous F := by
    have e : F = fun X => algebraMap ℚ (AfP p) (N : ℚ)⁻¹ • (X - 1) := by
      funext X; rw [hFdef, algebraMap_smul]
    rw [e]
    fun_prop
  set U : Set G.GAf := {g | F (matL b L (xg g)) ∈ box ∧ F (matL b L (xg g⁻¹)) ∈ box} with hU
  have hUo : IsOpen U := (hboxo.preimage (hF.comp ((continuous_matL b L).comp hxg))).inter
    (hboxo.preimage (hF.comp ((continuous_matL b L).comp hxgi)))
  have hm1 : matL b L (xg 1) = 1 := by
    have : xg 1 = 1 := rfl
    rw [this]
    simp [matL, LinearMap.toMatrix_one]
  have h1U : (1 : G.GAf) ∈ U := by
    have h0 : F (matL b L (xg 1)) ∈ box := by
      rw [hm1, hFdef]
      simp only [sub_self, smul_zero]
      exact fun i _ j _ => zero_mem _
    refine ⟨h0, ?_⟩
    rw [inv_one]; exact h0
  have hUK : U ⊆ L.KN N := fun g hg =>
    ⟨congOne_of_mat b L hN (fun i j => hg.1 i trivial j trivial),
      congOne_of_mat b L hN (fun i j => hg.2 i trivial j trivial)⟩
  have hopen : IsOpen (L.KN N : Set G.GAf) :=
    Subgroup.isOpen_of_mem_nhds _ (g := 1) (Filter.mem_of_superset (hUo.mem_nhds h1U) hUK)

  obtain ⟨mu, hmu, hmuj⟩ := exists_simInv (p := p) (G := G)
  set P' := {y : AfP p ⊗[ℚ] G.C | ∀ i j, IsIntAf (matL b L y i j)} with hP'def
  have hP' : IsCompact P' := isCompact_intSet b L
  have hσ : Continuous (fun y : AfP p ⊗[ℚ] G.C ↦ (starT G.star (AfP p) y).unop) := by
    let σl : (AfP p ⊗[ℚ] G.C) →ₗ[AfP p] (AfP p ⊗[ℚ] G.C) :=
      { toFun := fun y ↦ (starT G.star (AfP p) y).unop
        map_add' := fun x y ↦ by simp only [map_add, MulOpposite.unop_add]
        map_smul' := by
          intro r x
          induction x using TensorProduct.induction_on with
          | zero => simp
          | tmul a y =>
            simp only [TensorProduct.smul_tmul', smul_eq_mul, starT_tmul, RingHom.id_apply]
          | add x y hx hy => simp only [smul_add, map_add, MulOpposite.unop_add, hx, hy, RingHom.id_apply] }
    exact IsModuleTopology.continuous_of_linearMap σl
  have hj : Continuous (algebraMap (AfP p) (AfP p ⊗[ℚ] G.C)) :=
    IsModuleTopology.continuous_of_linearMap (Algebra.linearMap (AfP p) (AfP p ⊗[ℚ] G.C))
  set S₁ := (fun y : AfP p ⊗[ℚ] G.C => mu (y * (starT G.star (AfP p) y).unop)) '' P' with hS₁def
  have hS₁ : IsCompact S₁ := hP'.image (hmu.comp (continuous_id.mul hσ))
  have hGcl : IsClosed (UPts G.star (AfP p) : Set ((AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ)) := by
    apply isClosed_eq
    · exact (Units.continuous_val.comp continuous_fst).mul
        (hσ.comp (Units.continuous_val.comp continuous_fst))
    · exact hj.comp (Units.continuous_val.comp continuous_snd)
  let gE : G.GAf → ((AfP p ⊗[ℚ] G.C) × (AfP p ⊗[ℚ] G.C)ᵐᵒᵖ) × (AfP p × (AfP p)ᵐᵒᵖ) :=
    fun x ↦ (Units.embedProduct _ x.1.1, Units.embedProduct _ x.1.2)
  have hg : Topology.IsClosedEmbedding gE :=
    (Units.isClosedEmbedding_embedProduct.prodMap Units.isClosedEmbedding_embedProduct).comp
      hGcl.isClosedEmbedding_subtypeVal
  set C' := (P' ×ˢ (MulOpposite.opHomeomorph.symm ⁻¹' P')) ×ˢ
    (S₁ ×ˢ (MulOpposite.opHomeomorph.symm ⁻¹' S₁)) with hC'
  have hK0 : IsCompact (gE ⁻¹' C') := hg.isCompact_preimage ((hP'.prod
      (MulOpposite.opHomeomorph.symm.isCompact_preimage.2 hP')).prod
      (hS₁.prod (MulOpposite.opHomeomorph.symm.isCompact_preimage.2 hS₁)))
  have hsub : (L.KN N : Set G.GAf) ⊆ gE ⁻¹' C' := by
    intro g hgK
    have hx : xg g ∈ P' := int_of_congOne b L hgK.1
    have hxi : xg g⁻¹ ∈ P' := int_of_congOne b L hgK.2
    have hm : ∀ h : G.GAf, mu (xg h * (starT G.star (AfP p) (xg h)).unop) =
        (((h : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).2 : (AfP p)ˣ) : AfP p) := by
      intro h
      have e : xg h * (starT G.star (AfP p) (xg h)).unop =
          algebraMap (AfP p) (AfP p ⊗[ℚ] G.C) (((h : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).2 : (AfP p)ˣ) : AfP p) := h.2
      rw [e, hmuj]
    refine ⟨⟨hx, hxi⟩, ⟨xg g, hx, hm g⟩, ⟨xg g⁻¹, hxi, hm g⁻¹⟩⟩
  have hKcl : IsClosed (L.KN N : Set G.GAf) := Subgroup.isClosed_of_isOpen _ hopen
  exact ⟨⟨⟨L.KN N, hopen⟩, hK0.of_isClosed_subset hKcl hsub⟩, rfl⟩

end Top

end GlobalTheory.LKGeo.KNLevel
