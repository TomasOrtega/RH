import Mathlib
import GroundTheory.AutomorphicForms.DefiniteClassNumber.AdelicLattice

set_option linter.unusedSectionVars false

noncomputable section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open Module Matrix TensorProduct Topology NumberField IsDedekindDomain GroundTheory.Automorphic
  GroundTheory.Global

attribute [local instance] tensorTopology finite_of_isQuadraticExtension isModuleTopology_tensor
  isTopologicalRing_tensor

variable {K : Type*} [Field K] [NumberField K]
variable {E : Type*} [Field E] [NumberField E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {κ : Type*} [Fintype κ] (b : Basis κ K E)

section Core

variable (ι) in

def stdSub : AddSubgroup (ι → FinAdele K ⊗[K] E) where
  carrier := stdLattice ι (FinAdele K) b (intAdeles K)
  add_mem' hx hy := stdLattice_add b hx hy
  zero_mem' := (mem_stdLattice_iff b _ _).2 fun a => by
    rw [vecCoords_zero]
    exact zero_mem _
  neg_mem' {x} hx := (mem_stdLattice_iff b _ _).2 fun a => by
    rw [vecCoords_neg]
    exact neg_mem (((mem_stdLattice_iff b _ _).1 hx) a)

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_stdSub {x : ι → FinAdele K ⊗[K] E} :
    x ∈ stdSub ι b ↔ x ∈ stdLattice ι (FinAdele K) b (intAdeles K) := Iff.rfl

variable (ι) in

def integralCore : AddSubgroup (ι → FinAdele K ⊗[K] E) where
  carrier := {u | ∀ β : 𝓞 E, ((1 : FinAdele K) ⊗ₜ[K] (β : E)) • u ∈ stdSub ι b}
  add_mem' {u v} hu hv β := by
    rw [smul_add]
    exact add_mem (hu β) (hv β)
  zero_mem' β := by
    rw [smul_zero]
    exact zero_mem _
  neg_mem' {u} hu β := by
    rw [smul_neg]
    exact neg_mem (hu β)

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_integralCore {u : ι → FinAdele K ⊗[K] E} :
    u ∈ integralCore ι b ↔ ∀ β : 𝓞 E, ((1 : FinAdele K) ⊗ₜ[K] (β : E)) • u ∈ stdSub ι b := Iff.rfl

/- English proof (translation)
Introduce `u hu`. Use `hu 1` as an intermediate fact. Rewrite `this` using `[RingOfIntegers.coe_eq_algebraMap, map_one, ← Algebra.TensorProduct.one_def, one_smul]`. Then use the resulting hypothesis.
-/
theorem integralCore_le : integralCore ι b ≤ stdSub ι b := by
  intro u hu
  have := hu 1
  rwa [RingOfIntegers.coe_eq_algebraMap, map_one, ← Algebra.TensorProduct.one_def, one_smul] at this

/- English proof (translation)
Introduce `β'`. Rewrite using `[smul_smul, Algebra.TensorProduct.tmul_mul_tmul, mul_one]`. Use `hu (β' * β)` as an intermediate fact. Rewrite `this` using `[RingOfIntegers.coe_eq_algebraMap, map_mul]`. Then use the resulting hypothesis.
-/
theorem smul_mem_integralCore {u : ι → FinAdele K ⊗[K] E} (hu : u ∈ integralCore ι b) (β : 𝓞 E) :
    ((1 : FinAdele K) ⊗ₜ[K] (β : E)) • u ∈ integralCore ι b := by
  intro β'
  rw [smul_smul, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  have := hu (β' * β)
  rwa [RingOfIntegers.coe_eq_algebraMap, map_mul] at this

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `only [Pi.smul_apply, smul_eq_mul, zsmul_eq_mul, mul_assoc]`.
-/
theorem zsmul_smul_vec {R : Type*} [CommRing R] (n : ℤ) (z : R) (u : ι → R) :
    (n • z) • u = n • (z • u) := by
  funext i
  simp only [Pi.smul_apply, smul_eq_mul, zsmul_eq_mul, mul_assoc]

/- English proof (translation)
Use `⟨fun h s => h _, fun h β => ?_⟩` and prove the remaining obligations. Establish `hβ : (β : E) = ∑ s, ((RingOfIntegers.basis E).repr β s) • ((RingOfIntegers.basis E s : 𝓞 E) : E)`. Use `congrArg (algebraMap (𝓞 E) E) ((RingOfIntegers.basis E).sum_repr β)` as an intermediate fact. Rewrite `this` using `[map_sum]`. Simplify using `only [map_zsmul] at this`.

Conclude with `this.symm`. Rewrite using `[hβ, tmul_sum, Finset.sum_smul]`. Use `AddSubgroup.sum_mem _ fun s _ => ?_` and prove the remaining obligations. Rewrite using `[tmul_smul, zsmul_smul_vec]`. Conclude with `zsmul_mem (h s) _`.
-/
theorem mem_integralCore_iff_basis {u : ι → FinAdele K ⊗[K] E} :
    u ∈ integralCore ι b ↔ ∀ s, ((1 : FinAdele K) ⊗ₜ[K]
      ((RingOfIntegers.basis E s : 𝓞 E) : E)) • u ∈ stdSub ι b := by
  refine ⟨fun h s => h _, fun h β => ?_⟩
  have hβ : (β : E) = ∑ s, ((RingOfIntegers.basis E).repr β s) •
      ((RingOfIntegers.basis E s : 𝓞 E) : E) := by
    have := congrArg (algebraMap (𝓞 E) E) ((RingOfIntegers.basis E).sum_repr β)
    rw [map_sum] at this
    simp only [map_zsmul] at this
    exact this.symm
  rw [hβ, tmul_sum, Finset.sum_smul]
  refine AddSubgroup.sum_mem _ fun s _ => ?_
  rw [tmul_smul, zsmul_smul_vec]
  exact zsmul_mem (h s) _

/- English proof (translation)
Establish `: (integralCore ι b : Set (ι → FinAdele K ⊗[K] E)) = ⋂ s, (fun u => ((1 : FinAdele K) ⊗ₜ[K] ((RingOfIntegers.basis E s : 𝓞 E) : E)) • u) ⁻¹' stdLattice ι (FinAdele K) b (intAdeles K)`. Use extensionality with `u`. Simplify using `only [Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]`. Conclude with `mem_integralCore_iff_basis b`. Rewrite using `[this]`.

Conclude with `isOpen_iInter_of_finite fun s => (isOpen_stdLattice (FinAdele K) b (isOpen_integralFiniteAdeles (R := 𝓞 K) (K := K))).preimage (continuous_const_smul _)`.
-/
theorem isOpen_integralCore :
    IsOpen (integralCore ι b : Set (ι → FinAdele K ⊗[K] E)) := by
  have : (integralCore ι b : Set (ι → FinAdele K ⊗[K] E)) = ⋂ s, (fun u => ((1 : FinAdele K) ⊗ₜ[K]
      ((RingOfIntegers.basis E s : 𝓞 E) : E)) • u) ⁻¹' stdLattice ι (FinAdele K) b (intAdeles K) := by
    ext u
    simp only [Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]
    exact mem_integralCore_iff_basis b
  rw [this]
  exact isOpen_iInter_of_finite fun s =>
    (isOpen_stdLattice (FinAdele K) b (isOpen_integralFiniteAdeles (R := 𝓞 K) (K := K))).preimage
      (continuous_const_smul _)

/- English proof (translation)
Establish `: T2Space (FinAdele K)` using `t2Space_finiteAdeleRing K`. Establish `: T2Space (FinAdele K ⊗[K] E)` using `t2Space_tensor (FinAdele K)`. Establish `: (integralCore ι b : Set (ι → FinAdele K ⊗[K] E)) = ⋂ β : 𝓞 E, (fun u => ((1 : FinAdele K) ⊗ₜ[K] (β : E)) • u) ⁻¹' stdLattice ι (FinAdele K) b (intAdeles K)`. Use extensionality with `u`. Simplify using `only [Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]`.

Conclude with `mem_integralCore b`. Rewrite using `[this]`. Conclude with `isClosed_iInter fun β => (isCompact_stdLattice (FinAdele K) b (isCompact_integralFiniteAdeles K)).isClosed.preimage (continuous_const_smul _)`.
-/
theorem isClosed_integralCore :
    IsClosed (integralCore ι b : Set (ι → FinAdele K ⊗[K] E)) := by
  have : T2Space (FinAdele K) := t2Space_finiteAdeleRing K
  have : T2Space (FinAdele K ⊗[K] E) := t2Space_tensor (FinAdele K)
  have : (integralCore ι b : Set (ι → FinAdele K ⊗[K] E)) = ⋂ β : 𝓞 E, (fun u =>
      ((1 : FinAdele K) ⊗ₜ[K] (β : E)) • u) ⁻¹' stdLattice ι (FinAdele K) b (intAdeles K) := by
    ext u
    simp only [Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]
    exact mem_integralCore b
  rw [this]
  exact isClosed_iInter fun β =>
    (isCompact_stdLattice (FinAdele K) b (isCompact_integralFiniteAdeles K)).isClosed.preimage
      (continuous_const_smul _)

/- English proof (translation)
The claim follows from `(isCompact_stdLattice (FinAdele K) b (isCompact_integralFiniteAdeles K)).of_isClosed_subset (isClosed_integralCore b) (integralCore_le b)`.
-/
theorem isCompact_integralCore :
    IsCompact (integralCore ι b : Set (ι → FinAdele K ⊗[K] E)) :=
  (isCompact_stdLattice (FinAdele K) b (isCompact_integralFiniteAdeles K)).of_isClosed_subset
    (isClosed_integralCore b) (integralCore_le b)

/- English proof (translation)
Establish `hW : {t : FinAdele K | t • stdVec (FinAdele K) b a ∈ integralCore ι b} ∈ 𝓝 (0 : FinAdele K)`. Use `((isOpen_integralCore b).preimage (continuous_id.smul continuous_const)).mem_nhds ?_` and prove the remaining obligations. Use `show (0 : FinAdele K) • stdVec (FinAdele K) b a ∈ integralCore ι b`. Rewrite using `[zero_smul]`. Conclude with `zero_mem _`.

Take `⟨d, hd0, hd⟩` from `exists_forall_mul_mem_of_mem_nhds hW`. Use `⟨algebraMap (𝓞 K) K d, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Ne, ← RingOfIntegers.coe_eq_algebraMap, RingOfIntegers.coe_eq_zero_iff]`. Conclude with `hd0`. Use `hd 1 (one_mem _)` as an intermediate fact.

Rewrite `this` using `[mul_one]`. Then use the resulting hypothesis.
-/
theorem exists_smul_stdVec_mem_integralCore (a : ι × κ) :
    ∃ d : K, d ≠ 0 ∧ algebraMap K (FinAdele K) d • stdVec (FinAdele K) b a ∈ integralCore ι b := by
  have hW : {t : FinAdele K | t • stdVec (FinAdele K) b a ∈ integralCore ι b} ∈
      𝓝 (0 : FinAdele K) := by
    refine ((isOpen_integralCore b).preimage (continuous_id.smul continuous_const)).mem_nhds ?_
    show (0 : FinAdele K) • stdVec (FinAdele K) b a ∈ integralCore ι b
    rw [zero_smul]
    exact zero_mem _
  obtain ⟨d, hd0, hd⟩ := exists_forall_mul_mem_of_mem_nhds hW
  refine ⟨algebraMap (𝓞 K) K d, ?_, ?_⟩
  · rw [Ne, ← RingOfIntegers.coe_eq_algebraMap, RingOfIntegers.coe_eq_zero_iff]
    exact hd0
  · have := hd 1 (one_mem _)
    rwa [mul_one] at this

end Core

section Stabilizer

variable (H : Matrix ι ι E)

def coreStabilizer : Subgroup (unitaryPoints K E H (FinAdele K)) where
  carrier := {g | ∀ u ∈ integralCore ι b, unitaryMat g *ᵥ u ∈ integralCore ι b ∧
    unitaryMat g⁻¹ *ᵥ u ∈ integralCore ι b}
  one_mem' u hu := by
    have h1 : unitaryMat (1 : unitaryPoints K E H (FinAdele K)) = 1 := rfl
    simp only [inv_one, h1, Matrix.one_mulVec]
    exact ⟨hu, hu⟩
  mul_mem' {g h} hg hh u hu := by
    refine ⟨?_, ?_⟩
    · rw [unitaryMat_mul, ← Matrix.mulVec_mulVec]
      exact (hg _ (hh u hu).1).1
    · rw [_root_.mul_inv_rev, unitaryMat_mul, ← Matrix.mulVec_mulVec]
      exact (hh _ (hg u hu).2).2
  inv_mem' {g} hg u hu := by
    rw [inv_inv]
    exact ⟨(hg u hu).2, (hg u hu).1⟩

variable {H}

variable (H)

/- English proof (translation)
Establish `hΛo` using `isOpen_integralCore (ι := ι) b`. Establish `hΛc` using `isCompact_integralCore (ι := ι) b`. Establish `hA` using `continuous_unitaryMat_mulVec (K := K) H (FinAdele K) (ι := ι)`. Establish `hsub : ({1} : Set (unitaryPoints K E H (FinAdele K))) ×ˢ (integralCore ι b : Set (ι → FinAdele K ⊗[K] E)) ⊆ (fun p : unitaryPoints K E H (FinAdele K) × (ι → FinAdele K ⊗[K] E) => unitaryMat p.1 *ᵥ p.2) ⁻¹' (integralCore ι b : Set (ι → FinAdele K ⊗[K] E))`. Introduce and unpack `⟨g, x⟩ ⟨hg, hx⟩`.

Rewrite `hg` using `[Set.mem_singleton_iff]`. Substitute `hg` using the available equality. Use `show unitaryMat (1 : unitaryPoints K E H (FinAdele K)) *ᵥ x ∈ integralCore ι b`. Rewrite using `[show unitaryMat (1 : unitaryPoints K E H (FinAdele K)) = 1 from rfl, Matrix.one_mulVec]`. Conclude with `hx`.

Take `⟨u, v, hu, -, h1u, hΛv, huv⟩` from `generalized_tube_lemma isCompact_singleton hΛc (hΛo.preimage hA) hsub`. Establish `h1 : (1 : unitaryPoints K E H (FinAdele K)) ∈ u` using `h1u rfl`. Establish `hmem : ∀ g ∈ u, ∀ x ∈ integralCore ι b, unitaryMat g *ᵥ x ∈ integralCore ι b`. Introduce `g hg x hx`. Use `huv (Set.mk_mem_prod hg (hΛv hx))` as an intermediate fact.

Rewrite `this` using `[Set.mem_preimage]`. Conclude with `this`. Establish `h1' : (1 : unitaryPoints K E H (FinAdele K)) ∈ (fun g => g⁻¹) ⁻¹' u` using `by show (1 : unitaryPoints K E H (FinAdele K))⁻¹ ∈ u`. Rewrite using `[inv_one]`. Conclude with `h1`.

Establish `hW : u ∩ (fun g => g⁻¹) ⁻¹' u ∈ 𝓝 (1 : unitaryPoints K E H (FinAdele K))` using `Filter.inter_mem (hu.mem_nhds h1) ((hu.preimage continuous_inv).mem_nhds h1')`. Use `Subgroup.isOpen_of_mem_nhds _ (Filter.mem_of_superset hW ?_)` and prove the remaining obligations. Introduce and unpack `g ⟨hg, hg'⟩ x hx`. Conclude with `⟨hmem g hg x hx, hmem g⁻¹ hg' x hx⟩`.
-/
theorem isOpen_coreStabilizer :
    IsOpen (coreStabilizer b H : Set (unitaryPoints K E H (FinAdele K))) := by
  have hΛo := isOpen_integralCore (ι := ι) b
  have hΛc := isCompact_integralCore (ι := ι) b
  have hA := continuous_unitaryMat_mulVec (K := K) H (FinAdele K) (ι := ι)
  have hsub : ({1} : Set (unitaryPoints K E H (FinAdele K))) ×ˢ
      (integralCore ι b : Set (ι → FinAdele K ⊗[K] E)) ⊆
      (fun p : unitaryPoints K E H (FinAdele K) × (ι → FinAdele K ⊗[K] E) =>
        unitaryMat p.1 *ᵥ p.2) ⁻¹' (integralCore ι b : Set (ι → FinAdele K ⊗[K] E)) := by
    rintro ⟨g, x⟩ ⟨hg, hx⟩
    rw [Set.mem_singleton_iff] at hg
    subst hg
    show unitaryMat (1 : unitaryPoints K E H (FinAdele K)) *ᵥ x ∈ integralCore ι b
    rw [show unitaryMat (1 : unitaryPoints K E H (FinAdele K)) = 1 from rfl, Matrix.one_mulVec]
    exact hx
  obtain ⟨u, v, hu, -, h1u, hΛv, huv⟩ :=
    generalized_tube_lemma isCompact_singleton hΛc (hΛo.preimage hA) hsub
  have h1 : (1 : unitaryPoints K E H (FinAdele K)) ∈ u := h1u rfl
  have hmem : ∀ g ∈ u, ∀ x ∈ integralCore ι b, unitaryMat g *ᵥ x ∈ integralCore ι b := by
    intro g hg x hx
    have := huv (Set.mk_mem_prod hg (hΛv hx))
    rw [Set.mem_preimage] at this
    exact this
  have h1' : (1 : unitaryPoints K E H (FinAdele K)) ∈ (fun g => g⁻¹) ⁻¹' u := by
    show (1 : unitaryPoints K E H (FinAdele K))⁻¹ ∈ u
    rw [inv_one]
    exact h1
  have hW : u ∩ (fun g => g⁻¹) ⁻¹' u ∈ 𝓝 (1 : unitaryPoints K E H (FinAdele K)) :=
    Filter.inter_mem (hu.mem_nhds h1) ((hu.preimage continuous_inv).mem_nhds h1')
  refine Subgroup.isOpen_of_mem_nhds _ (Filter.mem_of_superset hW ?_)
  rintro g ⟨hg, hg'⟩ x hx
  exact ⟨hmem g hg x hx, hmem g⁻¹ hg' x hx⟩

/- English proof (translation)
Establish `hΛ` using `isClosed_integralCore (ι := ι) b`. Establish `hA` using `continuous_unitaryMat_mulVec (K := K) H (FinAdele K) (ι := ι)`. Establish `: (coreStabilizer b H : Set (unitaryPoints K E H (FinAdele K))) = ⋂ x ∈ (integralCore ι b : Set (ι → FinAdele K ⊗[K] E)), ({g | unitaryMat g *ᵥ x ∈ integralCore ι b} ∩ {g | unitaryMat g⁻¹ *ᵥ x ∈ integralCore ι b})`. Use extensionality with `g`. Simplify using `only [SetLike.mem_coe, Set.mem_iInter, Set.mem_inter_iff, Set.mem_setOf_eq]`.

Conclude with `Iff.rfl`. Rewrite using `[this]`. Use `isClosed_biInter fun x _ => IsClosed.inter ?_ ?_` and prove the remaining obligations. Conclude with `hΛ.preimage (hA.comp (continuous_id.prodMk continuous_const))`. Conclude with `hΛ.preimage (hA.comp (continuous_inv.prodMk continuous_const))`.
-/
theorem isClosed_coreStabilizer :
    IsClosed (coreStabilizer b H : Set (unitaryPoints K E H (FinAdele K))) := by
  have hΛ := isClosed_integralCore (ι := ι) b
  have hA := continuous_unitaryMat_mulVec (K := K) H (FinAdele K) (ι := ι)
  have : (coreStabilizer b H : Set (unitaryPoints K E H (FinAdele K))) =
      ⋂ x ∈ (integralCore ι b : Set (ι → FinAdele K ⊗[K] E)),
        ({g | unitaryMat g *ᵥ x ∈ integralCore ι b} ∩ {g | unitaryMat g⁻¹ *ᵥ x ∈ integralCore ι b}) := by
    ext g
    simp only [SetLike.mem_coe, Set.mem_iInter, Set.mem_inter_iff, Set.mem_setOf_eq]
    exact Iff.rfl
  rw [this]
  refine isClosed_biInter fun x _ => IsClosed.inter ?_ ?_
  · exact hΛ.preimage (hA.comp (continuous_id.prodMk continuous_const))
  · exact hΛ.preimage (hA.comp (continuous_inv.prodMk continuous_const))

/- English proof (translation)
Establish `: T2Space (FinAdele K)` using `t2Space_finiteAdeleRing K`. Use `choose d hd0 hd using exists_smul_stdVec_mem_integralCore (ι := ι) b`. Use `set C : ι → Set (FinAdele K) := fun j => (fun y : κ → FinAdele K => ∑ k, algebraMap K (FinAdele K) (b.repr 1 k * (d (j, k))⁻¹) * y k) '' Set.pi Set.univ fun _ => (intAdeles K : Set (FinAdele K)) with hCdef`. Establish `hC : ∀ j, IsCompact (C j)` using `fun j => (isCompact_univ_pi fun _ => isCompact_integralFiniteAdeles K).image (continuous_finsetSum _ fun k _ => continuous_const.mul (continuous_apply k))`. Establish `hbig : IsCompact (unitaryCoords H (FinAdele K) b ⁻¹' Set.pi Set.univ fun p : ι × ι × κ => C p.2.1)` using `(isClosedEmbedding_unitaryCoords H (FinAdele K) b hH).isCompact_preimage (isCompact_univ_pi fun p => hC _)`.

Use `hbig.of_isClosed_subset (isClosed_coreStabilizer b H) ?_` and prove the remaining obligations. Introduce and unpack `g hg ⟨i, j, m⟩ -`. Use `set B := Algebra.TensorProduct.basis (FinAdele K) b`. Establish `hcol : ∀ k, algebraMap K (FinAdele K) (d (j, k)) * B.repr (unitaryMat g i j * ((1 : FinAdele K) ⊗ₜ b k)) m ∈ intAdeles K`. Introduce `k`.

Establish `h1` using `integralCore_le b ((hg _ (hd (j, k))).1)`. Rewrite `h1` using `[mem_stdSub, mulVec_smul, mem_stdLattice_iff]`. Establish `h2` using `h1 (i, m)`. Rewrite `h2` using `[vecCoords_smul]`. Use `h2 using 2` and compare the differences between its conclusion and the goal.

Simplify using `only [vecCoords, stdVec, Matrix.mulVec_single, Pi.smul_apply, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, Matrix.col_apply, B]`. Use `⟨fun k => algebraMap K (FinAdele K) (d (j, k)) * B.repr (unitaryMat g i j * ((1 : FinAdele K) ⊗ₜ b k)) m, fun k _ => hcol k, ?_⟩` and prove the remaining obligations. Establish `hone : (1 : FinAdele K ⊗[K] E) = ∑ k, algebraMap K (FinAdele K) (b.repr 1 k) • ((1 : FinAdele K) ⊗ₜ b k)` using `by conv_lhs => rw [Algebra.TensorProduct.one_def, ← b.sum_repr 1]`. Rewrite using `[TensorProduct.tmul_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations.

Rewrite using `[TensorProduct.tmul_smul, algebraMap_smul]`. Use `show _ = unitaryCoords H (FinAdele K) b g (i, j, m)`. Rewrite using `[unitaryCoords_apply]`. Use `conv_rhs => rw [← mul_one (unitaryMat g i j), hone]`. Simplify using `only [Finset.mul_sum, mul_smul_comm, map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul]`.

Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[← mul_assoc, ← map_mul, mul_assoc, inv_mul_cancel₀ (hd0 (j, k)), mul_one]`.
-/
theorem isCompact_coreStabilizer (hH : IsUnit H.det) :
    IsCompact (coreStabilizer b H : Set (unitaryPoints K E H (FinAdele K))) := by
  classical
  have : T2Space (FinAdele K) := t2Space_finiteAdeleRing K
  choose d hd0 hd using exists_smul_stdVec_mem_integralCore (ι := ι) b
  set C : ι → Set (FinAdele K) := fun j => (fun y : κ → FinAdele K =>
    ∑ k, algebraMap K (FinAdele K) (b.repr 1 k * (d (j, k))⁻¹) * y k) ''
      Set.pi Set.univ fun _ => (intAdeles K : Set (FinAdele K)) with hCdef
  have hC : ∀ j, IsCompact (C j) := fun j =>
    (isCompact_univ_pi fun _ => isCompact_integralFiniteAdeles K).image
      (continuous_finsetSum _ fun k _ => continuous_const.mul (continuous_apply k))
  have hbig : IsCompact (unitaryCoords H (FinAdele K) b ⁻¹'
      Set.pi Set.univ fun p : ι × ι × κ => C p.2.1) :=
    (isClosedEmbedding_unitaryCoords H (FinAdele K) b hH).isCompact_preimage
      (isCompact_univ_pi fun p => hC _)
  refine hbig.of_isClosed_subset (isClosed_coreStabilizer b H) ?_
  rintro g hg ⟨i, j, m⟩ -
  set B := Algebra.TensorProduct.basis (FinAdele K) b
  have hcol : ∀ k, algebraMap K (FinAdele K) (d (j, k)) *
      B.repr (unitaryMat g i j * ((1 : FinAdele K) ⊗ₜ b k)) m ∈ intAdeles K := by
    intro k
    have h1 := integralCore_le b ((hg _ (hd (j, k))).1)
    rw [mem_stdSub, mulVec_smul, mem_stdLattice_iff] at h1
    have h2 := h1 (i, m)
    rw [vecCoords_smul] at h2
    convert h2 using 2
    simp only [vecCoords, stdVec, Matrix.mulVec_single, Pi.smul_apply, MulOpposite.smul_eq_mul_unop,
      MulOpposite.unop_op, Matrix.col_apply, B]
  refine ⟨fun k => algebraMap K (FinAdele K) (d (j, k)) *
    B.repr (unitaryMat g i j * ((1 : FinAdele K) ⊗ₜ b k)) m, fun k _ => hcol k, ?_⟩
  have hone : (1 : FinAdele K ⊗[K] E) =
      ∑ k, algebraMap K (FinAdele K) (b.repr 1 k) • ((1 : FinAdele K) ⊗ₜ b k) := by
    conv_lhs => rw [Algebra.TensorProduct.one_def, ← b.sum_repr 1]
    rw [TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [TensorProduct.tmul_smul, algebraMap_smul]
  show _ = unitaryCoords H (FinAdele K) b g (i, j, m)
  rw [unitaryCoords_apply]
  conv_rhs => rw [← mul_one (unitaryMat g i j), hone]
  simp only [Finset.mul_sum, mul_smul_comm, map_sum, map_smul, Finsupp.coe_finsetSum,
    Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← mul_assoc, ← map_mul, mul_assoc, inv_mul_cancel₀ (hd0 (j, k)), mul_one]

end Stabilizer

section CoreLattice

variable (H : Matrix ι ι E)

def coreLattice (g : unitaryPoints K E H (FinAdele K)) : AddSubgroup (ι → K ⊗[K] E) where
  carrier := {x | unitaryMat g⁻¹ *ᵥ toFinAdele K E ι x ∈ integralCore ι b}
  zero_mem' := by
    show unitaryMat g⁻¹ *ᵥ toFinAdele K E ι 0 ∈ integralCore ι b
    rw [map_zero, mulVec_zero]
    exact zero_mem _
  add_mem' {x y} hx hy := by
    show unitaryMat g⁻¹ *ᵥ toFinAdele K E ι (x + y) ∈ integralCore ι b
    rw [map_add, mulVec_add]
    exact add_mem hx hy
  neg_mem' {x} hx := by
    show unitaryMat g⁻¹ *ᵥ toFinAdele K E ι (-x) ∈ integralCore ι b
    rw [map_neg, mulVec_neg]
    exact neg_mem hx

variable {H}

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_coreLattice {g : unitaryPoints K E H (FinAdele K)} {x : ι → K ⊗[K] E} :
    x ∈ coreLattice b H g ↔ unitaryMat g⁻¹ *ᵥ toFinAdele K E ι x ∈ integralCore ι b := Iff.rfl

/- English proof (translation)
Establish `key : ∀ β : 𝓞 E, unitaryMat g⁻¹ *ᵥ toFinAdele K E ι (((1 : K) ⊗ₜ[K] (β : E)) • x) = ((1 : FinAdele K) ⊗ₜ[K] (β : E)) • (unitaryMat g⁻¹ *ᵥ toFinAdele K E ι x)`. Introduce `β`. Rewrite using `[toFinAdele_mul_smul, tensorMap_tmul, map_one, mulVec_smul]`. Rewrite using `[mem_coreLattice, mem_integralCore]`. Use `forall_congr' fun β => ?_` and prove the remaining obligations.

Rewrite using `[mem_adelicLattice, key]`. Both sides reduce to the same expression.
-/
theorem mem_coreLattice_iff {g : unitaryPoints K E H (FinAdele K)} {x : ι → K ⊗[K] E} :
    x ∈ coreLattice b H g ↔ ∀ β : 𝓞 E, ((1 : K) ⊗ₜ[K] (β : E)) • x ∈ adelicLattice b H g := by
  have key : ∀ β : 𝓞 E, unitaryMat g⁻¹ *ᵥ toFinAdele K E ι (((1 : K) ⊗ₜ[K] (β : E)) • x) =
      ((1 : FinAdele K) ⊗ₜ[K] (β : E)) • (unitaryMat g⁻¹ *ᵥ toFinAdele K E ι x) := by
    intro β
    rw [toFinAdele_mul_smul, tensorMap_tmul, map_one, mulVec_smul]
  rw [mem_coreLattice, mem_integralCore]
  refine forall_congr' fun β => ?_
  rw [mem_adelicLattice, key]
  rfl

/- English proof (translation)
Rewrite using `[mem_coreLattice, toFinAdele_mul_smul, tensorMap_tmul, map_one, mulVec_smul]`. Conclude with `smul_mem_integralCore b hx β`.
-/
theorem smul_mem_coreLattice {g : unitaryPoints K E H (FinAdele K)} {x : ι → K ⊗[K] E}
    (hx : x ∈ coreLattice b H g) (β : 𝓞 E) : ((1 : K) ⊗ₜ[K] (β : E)) • x ∈ coreLattice b H g := by
  rw [mem_coreLattice, toFinAdele_mul_smul, tensorMap_tmul, map_one, mulVec_smul]
  exact smul_mem_integralCore b hx β

/- English proof (translation)
Introduce `_ hx` and use `integralCore_le b hx`.
-/
theorem coreLattice_le_adelicLattice (g : unitaryPoints K E H (FinAdele K)) :
    coreLattice b H g ≤ adelicLattice b H g := fun _ hx => integralCore_le b hx

/- English proof (translation)
Rewrite using `[mem_coreLattice, mem_coreLattice, toFinAdele_mulVec, _root_.mul_inv_rev, unitaryMat_mul, mulVec_mulVec, Matrix.mul_assoc, unitaryMat_inv_mul, Matrix.mul_one]`.
-/
theorem mulVec_mem_coreLattice_iff (γ : unitaryPoints K E H K) (g : unitaryPoints K E H (FinAdele K))
    (x : ι → K ⊗[K] E) :
    unitaryMat γ *ᵥ x ∈ coreLattice b H (finDiag H γ * g) ↔ x ∈ coreLattice b H g := by
  rw [mem_coreLattice, mem_coreLattice, toFinAdele_mulVec, _root_.mul_inv_rev, unitaryMat_mul,
    mulVec_mulVec, Matrix.mul_assoc, unitaryMat_inv_mul, Matrix.mul_one]

variable (H) in

def transCore (g : unitaryPoints K E H (FinAdele K)) : Set (ι → FinAdele K ⊗[K] E) :=
  {z | unitaryMat g⁻¹ *ᵥ z ∈ integralCore ι b}

/- English proof (translation)
The claim follows from `(isOpen_integralCore b).preimage (continuous_const.matrix_mulVec continuous_id)`.
-/
theorem isOpen_transCore (g : unitaryPoints K E H (FinAdele K)) : IsOpen (transCore b H g) :=
  (isOpen_integralCore b).preimage (continuous_const.matrix_mulVec continuous_id)

/- English proof (translation)
The claim follows from `(isClosed_integralCore b).preimage (continuous_const.matrix_mulVec continuous_id)`.
-/
theorem isClosed_transCore (g : unitaryPoints K E H (FinAdele K)) : IsClosed (transCore b H g) :=
  (isClosed_integralCore b).preimage (continuous_const.matrix_mulVec continuous_id)

/- English proof (translation)
Establish `himage : toFinAdele K E ι '' (coreLattice b H g : Set (ι → K ⊗[K] E)) = transCore b H g ∩ Set.range (toFinAdele K E ι)`. Use extensionality with `z`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, hx, rfl⟩`. Conclude with `⟨hx, x, rfl⟩`.

Introduce and unpack `⟨hz, x, rfl⟩`. Conclude with `⟨x, hz, rfl⟩`. Apply `le_antisymm` to reduce the goal to its premises. Conclude with `closure_minimal (by rw [himage]; exact Set.inter_subset_left) (isClosed_transCore b g)`. Rewrite using `[himage]`.

Conclude with `denseRange_toFinAdele.open_subset_closure_inter (isOpen_transCore b g)`.
-/
theorem closure_image_coreLattice (g : unitaryPoints K E H (FinAdele K)) :
    closure (toFinAdele K E ι '' (coreLattice b H g : Set (ι → K ⊗[K] E))) = transCore b H g := by
  have himage : toFinAdele K E ι '' (coreLattice b H g : Set (ι → K ⊗[K] E)) =
      transCore b H g ∩ Set.range (toFinAdele K E ι) := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨hx, x, rfl⟩
    · rintro ⟨hz, x, rfl⟩
      exact ⟨x, hz, rfl⟩
  apply le_antisymm
  · exact closure_minimal (by rw [himage]; exact Set.inter_subset_left) (isClosed_transCore b g)
  · rw [himage]
    exact denseRange_toFinAdele.open_subset_closure_inter (isOpen_transCore b g)

/- English proof (translation)
Establish `hT : transCore b H g = transCore b H g'`. Rewrite using `[← closure_image_coreLattice, ← closure_image_coreLattice, h]`. Introduce `u hu`. Prove the components needed by the constructor for the conclusion. Establish `: unitaryMat g' *ᵥ u ∈ transCore b H g'` using `by show unitaryMat g'⁻¹ *ᵥ (unitaryMat g' *ᵥ u) ∈ integralCore ι b`.

Rewrite using `[mulVec_mulVec, unitaryMat_inv_mul, one_mulVec]`. Conclude with `hu`. Rewrite `this` using `[← hT]`. Express the relevant statement in the definitionally equal form `unitaryMat g⁻¹ *ᵥ (unitaryMat g' *ᵥ u) ∈ integralCore ι b at this`. Rewrite `this` using `[mulVec_mulVec]`.

Rewrite using `[unitaryMat_mul]`. Conclude with `this`. Establish `: unitaryMat g *ᵥ u ∈ transCore b H g` using `by show unitaryMat g⁻¹ *ᵥ (unitaryMat g *ᵥ u) ∈ integralCore ι b`. Rewrite using `[mulVec_mulVec, unitaryMat_inv_mul, one_mulVec]`. Conclude with `hu`.

Rewrite `this` using `[hT]`. Express the relevant statement in the definitionally equal form `unitaryMat g'⁻¹ *ᵥ (unitaryMat g *ᵥ u) ∈ integralCore ι b at this`. Rewrite `this` using `[mulVec_mulVec]`. Rewrite using `[_root_.mul_inv_rev, inv_inv, unitaryMat_mul]`. Conclude with `this`.
-/
theorem mem_coreStabilizer_of_coreLattice_eq {g g' : unitaryPoints K E H (FinAdele K)}
    (h : coreLattice b H g = coreLattice b H g') : g⁻¹ * g' ∈ coreStabilizer b H := by
  have hT : transCore b H g = transCore b H g' := by
    rw [← closure_image_coreLattice, ← closure_image_coreLattice, h]
  intro u hu
  constructor
  · have : unitaryMat g' *ᵥ u ∈ transCore b H g' := by
      show unitaryMat g'⁻¹ *ᵥ (unitaryMat g' *ᵥ u) ∈ integralCore ι b
      rw [mulVec_mulVec, unitaryMat_inv_mul, one_mulVec]
      exact hu
    rw [← hT] at this
    change unitaryMat g⁻¹ *ᵥ (unitaryMat g' *ᵥ u) ∈ integralCore ι b at this
    rw [mulVec_mulVec] at this
    rw [unitaryMat_mul]
    exact this
  · have : unitaryMat g *ᵥ u ∈ transCore b H g := by
      show unitaryMat g⁻¹ *ᵥ (unitaryMat g *ᵥ u) ∈ integralCore ι b
      rw [mulVec_mulVec, unitaryMat_inv_mul, one_mulVec]
      exact hu
    rw [hT] at this
    change unitaryMat g'⁻¹ *ᵥ (unitaryMat g *ᵥ u) ∈ integralCore ι b at this
    rw [mulVec_mulVec] at this
    rw [_root_.mul_inv_rev, inv_inv, unitaryMat_mul]
    exact this

/- English proof (translation)
Take `⟨k, hk, rfl⟩ : ∃ k ∈ coreStabilizer b H, g' = g * k` from `⟨g⁻¹ * g', h, by group⟩`. Use extensionality with `x`. Rewrite using `[mem_coreLattice, mem_coreLattice, _root_.mul_inv_rev, unitaryMat_mul, ← mulVec_mulVec]`. Prove the components needed by the constructor for the conclusion. Introduce `hx`.

Conclude with `(hk _ hx).2`. Introduce `hx`. Use `(hk _ hx).1` as an intermediate fact. Rewrite `this` using `[mulVec_mulVec, unitaryMat_mul_inv, one_mulVec]`. Then use the resulting hypothesis.
-/
theorem coreLattice_eq_of_mem_coreStabilizer {g g' : unitaryPoints K E H (FinAdele K)}
    (h : g⁻¹ * g' ∈ coreStabilizer b H) : coreLattice b H g = coreLattice b H g' := by
  obtain ⟨k, hk, rfl⟩ : ∃ k ∈ coreStabilizer b H, g' = g * k := ⟨g⁻¹ * g', h, by group⟩
  ext x
  rw [mem_coreLattice, mem_coreLattice, _root_.mul_inv_rev, unitaryMat_mul, ← mulVec_mulVec]
  constructor
  · intro hx
    exact (hk _ hx).2
  · intro hx
    have := (hk _ hx).1
    rwa [mulVec_mulVec, unitaryMat_mul_inv, one_mulVec] at this

/- English proof (translation)
Assemble the required witnesses or components as `⟨mem_coreStabilizer_of_coreLattice_eq b, coreLattice_eq_of_mem_coreStabilizer b⟩`.
-/
theorem coreLattice_eq_iff {g g' : unitaryPoints K E H (FinAdele K)} :
    coreLattice b H g = coreLattice b H g' ↔ g⁻¹ * g' ∈ coreStabilizer b H :=
  ⟨mem_coreStabilizer_of_coreLattice_eq b, coreLattice_eq_of_mem_coreStabilizer b⟩

variable (H) in

/- English proof (translation)
Use `choose D hD0 hD using fun s => exists_int_smul_includeRight_mem b H ((RingOfIntegers.basis E s : 𝓞 E) : E)`. Use `⟨∏ s, D s, Finset.prod_ne_zero_iff.2 fun s _ => hD0 s, fun g x hx => ?_⟩` and prove the remaining obligations. Rewrite using `[mem_coreLattice_iff]`. Introduce `β`. Establish `hβ : (β : E) = ∑ s, ((RingOfIntegers.basis E).repr β s) • ((RingOfIntegers.basis E s : 𝓞 E) : E)`.

Use `congrArg (algebraMap (𝓞 E) E) ((RingOfIntegers.basis E).sum_repr β)` as an intermediate fact. Rewrite `this` using `[map_sum]`. Simplify using `only [map_zsmul] at this`. Conclude with `this.symm`. Rewrite using `[hβ, tmul_sum, Finset.sum_smul]`.

Use `AddSubgroup.sum_mem _ fun s _ => ?_` and prove the remaining obligations. Rewrite using `[tmul_smul, zsmul_smul_vec]`. Use `zsmul_mem ?_ _` and prove the remaining obligations. Establish `hN : ((∏ s, D s : ℤ) : K) = ((∏ t ∈ Finset.univ.erase s, D t : ℤ) : K) * (D s : K)`. Rewrite using `[← Int.cast_mul, Finset.prod_erase_mul _ _ (Finset.mem_univ s)]`.

Establish `hcomm : ∀ (z : K ⊗[K] E) (c : K) (y : ι → K ⊗[K] E), z • (c • y) = c • (z • y)`. Introduce `z c y`. Use function extensionality and compare the values at `i`. Simplify using `only [Pi.smul_apply, smul_eq_mul, mul_smul_comm]`. Rewrite using `[hN, hcomm, mul_smul]`.

Establish `h1` using `hD s g x hx`. Rewrite `h1` using `[Algebra.TensorProduct.includeRight_apply]`. Establish `h2` using `intSmul_mem_adelicLattice h1 ((∏ t ∈ Finset.univ.erase s, D t : ℤ) : 𝓞 K)`. Rewrite `h2` using `[RingOfIntegers.coe_eq_algebraMap, map_intCast]`. Then use the resulting hypothesis.
-/
theorem exists_int_smul_mem_coreLattice : ∃ N : ℤ, N ≠ 0 ∧
    ∀ (g : unitaryPoints K E H (FinAdele K)) (x : ι → K ⊗[K] E), x ∈ adelicLattice b H g →
      (N : K) • x ∈ coreLattice b H g := by
  classical
  choose D hD0 hD using fun s => exists_int_smul_includeRight_mem b H
    ((RingOfIntegers.basis E s : 𝓞 E) : E)
  refine ⟨∏ s, D s, Finset.prod_ne_zero_iff.2 fun s _ => hD0 s, fun g x hx => ?_⟩
  rw [mem_coreLattice_iff]
  intro β
  have hβ : (β : E) = ∑ s, ((RingOfIntegers.basis E).repr β s) •
      ((RingOfIntegers.basis E s : 𝓞 E) : E) := by
    have := congrArg (algebraMap (𝓞 E) E) ((RingOfIntegers.basis E).sum_repr β)
    rw [map_sum] at this
    simp only [map_zsmul] at this
    exact this.symm
  rw [hβ, tmul_sum, Finset.sum_smul]
  refine AddSubgroup.sum_mem _ fun s _ => ?_
  rw [tmul_smul, zsmul_smul_vec]
  refine zsmul_mem ?_ _
  have hN : ((∏ s, D s : ℤ) : K) = ((∏ t ∈ Finset.univ.erase s, D t : ℤ) : K) * (D s : K) := by
    rw [← Int.cast_mul, Finset.prod_erase_mul _ _ (Finset.mem_univ s)]
  have hcomm : ∀ (z : K ⊗[K] E) (c : K) (y : ι → K ⊗[K] E), z • (c • y) = c • (z • y) := by
    intro z c y
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, mul_smul_comm]
  rw [hN, hcomm, mul_smul]
  have h1 := hD s g x hx
  rw [Algebra.TensorProduct.includeRight_apply] at h1
  have h2 := intSmul_mem_adelicLattice h1 ((∏ t ∈ Finset.univ.erase s, D t : ℤ) : 𝓞 K)
  rwa [RingOfIntegers.coe_eq_algebraMap, map_intCast] at h2

end CoreLattice

end GroundTheory.Heights₂.Heights.FiniteCovolume
