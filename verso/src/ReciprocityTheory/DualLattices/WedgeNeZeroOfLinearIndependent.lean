import ReciprocityTheory.DualLattices.SmallLevelClassSet

noncomputable section

open Module Submodule

namespace ReciprocityTheory.PGsh

attribute [local instance] extModR

section Wedge

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/- English proof (translation)
Set `f` to `(ExteriorAlgebra.ιMulti K k).compLinearMap W.subtype`. Establish `key : ∀ ψ : Module.Dual K (ExteriorAlgebra K V), ψ (f w) = ψ (bW.det w • f bW)`. Introduce `ψ`. Establish `h` using `AlternatingMap.eq_smul_basis_det bW (ψ.compAlternatingMap f)`. Use `congrArg (fun g => g w) h` as an intermediate fact.

Simplify using `only [LinearMap.compAlternatingMap_apply, AlternatingMap.smul_apply, smul_eq_mul] at this`. Rewrite using `[this, map_smul, smul_eq_mul, mul_comm]`. Establish `: f w - bW.det w • f bW = 0`. Rewrite using `[← Module.forall_dual_apply_eq_zero_iff K]`. Introduce `ψ`.

Rewrite using `[map_sub, key, sub_self]`. Conclude with `sub_eq_zero.mp this`.
-/
theorem wedge_eq_det_smul_basis {k : ℕ} {W : Submodule K V} (bW : Basis (Fin k) K W) (w : Fin k → W) :
    ExteriorAlgebra.ιMulti K k (fun j => (w j : V)) =
      bW.det w • ExteriorAlgebra.ιMulti K k (fun j => (bW j : V)) := by
  let f := (ExteriorAlgebra.ιMulti K k).compLinearMap W.subtype
  have key : ∀ ψ : Module.Dual K (ExteriorAlgebra K V), ψ (f w) = ψ (bW.det w • f bW) := by
    intro ψ
    have h := AlternatingMap.eq_smul_basis_det bW (ψ.compAlternatingMap f)
    have := congrArg (fun g => g w) h
    simp only [LinearMap.compAlternatingMap_apply, AlternatingMap.smul_apply, smul_eq_mul] at this
    rw [this, map_smul, smul_eq_mul, mul_comm]
  have : f w - bW.det w • f bW = 0 := by
    rw [← Module.forall_dual_apply_eq_zero_iff K]
    intro ψ; rw [map_sub, key, sub_self]
  exact sub_eq_zero.mp this

/- English proof (translation)
Establish `hw' : ∀ j, w j ∈ span K (Set.range b)` using `fun j => span_le_restrictScalars R K _ (hw j)`. Use `choose c hc using fun j => (Submodule.mem_span_range_iff_exists_fun R).mp (hw j)`. Set `bW` to `Basis.span hb`. Set `w' : Fin k → span K (Set.range b)` to `fun j => ⟨w j, hw' j⟩`. Establish `hw'eq : ∀ j, w' j = ∑ i, algebraMap R K (c j i) • bW i`.

Introduce `j`. Use `ext`. Simplify using `only [w', bW, Submodule.coe_sum, Submodule.coe_smul, Basis.span_apply, ← hc j]`. Simplify using `[algebraMap_smul]`. Establish `hrepr : ∀ j i, bW.repr (w' j) i = algebraMap R K (c j i)`.

Introduce `j i`. Rewrite using `[hw'eq j, map_sum]`. Simplify using `only [map_smul, Basis.repr_self, Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul, Finsupp.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]`. Use `⟨(Matrix.of fun i j => c j i).det, ?_⟩` and prove the remaining obligations. Establish `h1` using `wedge_eq_det_smul_basis bW w'`.

Establish `hdet : bW.det w' = algebraMap R K (Matrix.of fun i j => c j i).det`. Rewrite using `[Basis.det_apply, RingHom.map_det]`. Use `congr 1`. Use extensionality with `i j`. Simplify using `[Basis.toMatrix_apply, hrepr]`.

Simplify `h1` using `[w', bW, Basis.span_apply, hdet]`.
-/
theorem exists_wedge_eq_integral_smul {R : Type*} [CommRing R] [Algebra R K] [Module R V] [IsScalarTower R K V]
    {k : ℕ} {b w : Fin k → V} (hb : LinearIndependent K b)
    (hw : ∀ j, w j ∈ span R (Set.range b)) :
    ∃ r : R, ExteriorAlgebra.ιMulti K k w = algebraMap R K r • ExteriorAlgebra.ιMulti K k b := by
  have hw' : ∀ j, w j ∈ span K (Set.range b) := fun j => span_le_restrictScalars R K _ (hw j)
  choose c hc using fun j => (Submodule.mem_span_range_iff_exists_fun R).mp (hw j)
  let bW := Basis.span hb
  let w' : Fin k → span K (Set.range b) := fun j => ⟨w j, hw' j⟩
  have hw'eq : ∀ j, w' j = ∑ i, algebraMap R K (c j i) • bW i := by
    intro j; ext
    simp only [w', bW, Submodule.coe_sum, Submodule.coe_smul, Basis.span_apply, ← hc j]
    simp [algebraMap_smul]
  have hrepr : ∀ j i, bW.repr (w' j) i = algebraMap R K (c j i) := by
    intro j i
    rw [hw'eq j, map_sum]
    simp only [map_smul, Basis.repr_self, Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul,
      Finsupp.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
  refine ⟨(Matrix.of fun i j => c j i).det, ?_⟩
  have h1 := wedge_eq_det_smul_basis bW w'
  have hdet : bW.det w' = algebraMap R K (Matrix.of fun i j => c j i).det := by
    rw [Basis.det_apply, RingHom.map_det]
    congr 1; ext i j; simp [Basis.toMatrix_apply, hrepr]
  simpa [w', bW, Basis.span_apply, hdet] using h1

/- English proof (translation)
Establish `h` using `(exteriorPower.ιMulti_family_linearIndependent_field (n := k) hb).ne_zero (Set.powersetCard.ofFinEmbEquiv (OrderIso.refl (Fin k)).toOrderEmbedding)`. Introduce `h0`. Apply `h` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises. Simplify `h0` using `[exteriorPower.ιMulti_family]`.
-/
theorem wedge_ne_zero_of_linearIndependent {k : ℕ} {b : Fin k → V} (hb : LinearIndependent K b) :
    ExteriorAlgebra.ιMulti K k b ≠ 0 := by
  have h := (exteriorPower.ιMulti_family_linearIndependent_field (n := k) hb).ne_zero
    (Set.powersetCard.ofFinEmbEquiv (OrderIso.refl (Fin k)).toOrderEmbedding)
  intro h0; apply h
  apply Subtype.ext
  simpa [exteriorPower.ιMulti_family] using h0

variable {R : Type*} [CommRing R] [Algebra R K] [Module R V] [IsScalarTower R K V]

end Wedge

end ReciprocityTheory.PGsh
