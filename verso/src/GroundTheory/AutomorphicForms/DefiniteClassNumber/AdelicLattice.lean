import Mathlib
import GroundTheory.AutomorphicForms.DefiniteClassNumber.Places
import GroundTheory.AutomorphicForms.AdelicUnitaryGroups.LatticeCompact
import GroundTheory.AutomorphicForms.StrongApproximationSLDense
import GroundTheory.GlobalFields.Adele.Topology

noncomputable section

namespace GroundTheory.Automorphic

open Module Matrix TensorProduct Topology NumberField IsDedekindDomain GroundTheory.Global

attribute [local instance] tensorTopology finite_of_isQuadraticExtension isModuleTopology_tensor
  isTopologicalRing_tensor

variable {K : Type*} [Field K] [NumberField K]
variable {E : Type*} [CommRing E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {κ : Type*} [Fintype κ] (b : Basis κ K E)

variable (K) in

abbrev FinAdele := FiniteAdeleRing (𝓞 K) K

section Coordinates

variable {R : Type*} [CommRing R] [Algebra K R]

omit [NumberField K] [Algebra.IsQuadraticExtension K E] [Fintype ι] [DecidableEq ι] [Fintype κ] in
/- English proof (translation)
Simplify using `[vecCoords]`.
-/
theorem vecCoords_add (x y : ι → R ⊗[K] E) (a : ι × κ) :
    vecCoords R b (x + y) a = vecCoords R b x a + vecCoords R b y a := by
  simp [vecCoords]

omit [NumberField K] [Algebra.IsQuadraticExtension K E] [Fintype ι] [DecidableEq ι] [Fintype κ] in
/- English proof (translation)
Simplify using `[vecCoords]`.
-/
theorem vecCoords_neg (x : ι → R ⊗[K] E) (a : ι × κ) :
    vecCoords R b (-x) a = -vecCoords R b x a := by
  simp [vecCoords]

omit [NumberField K] [Algebra.IsQuadraticExtension K E] [Fintype ι] [DecidableEq ι] [Fintype κ] in
/- English proof (translation)
Simplify using `[vecCoords]`.
-/
theorem vecCoords_zero (a : ι × κ) : vecCoords R b (0 : ι → R ⊗[K] E) a = 0 := by
  simp [vecCoords]

omit [NumberField K] [Algebra.IsQuadraticExtension K E] [Fintype ι] [DecidableEq ι] [Fintype κ] in
/- English proof (translation)
Simplify using `[vecCoords]`.
-/
theorem vecCoords_smul (c : R) (x : ι → R ⊗[K] E) (a : ι × κ) :
    vecCoords R b (c • x) a = c * vecCoords R b x a := by
  simp [vecCoords]

omit [NumberField K] [Algebra.IsQuadraticExtension K E] [Fintype ι] [DecidableEq ι] [Fintype κ] in
/- English proof (translation)
Assemble the required witnesses or components as `⟨fun h a => h a.1 a.2, fun h i k => h (i, k)⟩`.
-/
theorem mem_stdLattice_iff (O : Subring R) (x : ι → R ⊗[K] E) :
    x ∈ stdLattice ι R b O ↔ ∀ a, vecCoords R b x a ∈ O :=
  ⟨fun h a => h a.1 a.2, fun h i k => h (i, k)⟩

omit [NumberField K] [Algebra.IsQuadraticExtension K E] [Fintype ι] [Fintype κ] in
/- English proof (translation)
Take `⟨i, k⟩` from `a`. Take `⟨j, l⟩` from `c`. Simplify using `only [vecCoords, stdVec, Pi.single_apply]`. Distinguish the cases in `hij : j = i`. Substitute `hij` using the available equality.

Simplify using `only [if_true]`. Rewrite using `[← Algebra.TensorProduct.basis_apply, Basis.repr_self, Finsupp.single_apply]`. Apply the tactic sequence `by_cases h : k = l <;> simp [h]`. Establish `: ¬ (i, k) = (j, l)` using `fun h => hij (congrArg Prod.fst h).symm`. Simplify using `[hij, this]`.
-/
theorem vecCoords_stdVec [DecidableEq κ] (a c : ι × κ) :
    vecCoords R b (stdVec R b a) c = if a = c then 1 else 0 := by
  obtain ⟨i, k⟩ := a
  obtain ⟨j, l⟩ := c
  simp only [vecCoords, stdVec, Pi.single_apply]
  by_cases hij : j = i
  · subst hij
    simp only [if_true]
    rw [← Algebra.TensorProduct.basis_apply, Basis.repr_self, Finsupp.single_apply]
    by_cases h : k = l <;> simp [h]
  · have : ¬ (i, k) = (j, l) := fun h => hij (congrArg Prod.fst h).symm
    simp [hij, this]

end Coordinates

variable (K E ι) in

def toFinAdele : (ι → K ⊗[K] E) →+ (ι → FinAdele K ⊗[K] E) :=
  AddMonoidHom.compLeft (tensorMap E (Algebra.ofId K (FinAdele K))).toRingHom.toAddMonoidHom ι

omit [Algebra.IsQuadraticExtension K E] [Fintype ι] [DecidableEq ι] in
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem toFinAdele_apply (x : ι → K ⊗[K] E) (i : ι) :
    toFinAdele K E ι x i = tensorMap E (Algebra.ofId K (FinAdele K)) (x i) := rfl

omit [Algebra.IsQuadraticExtension K E] [Fintype ι] [DecidableEq ι] [Fintype κ] in
/- English proof (translation)
Simplify using `only [vecCoords, toFinAdele_apply, repr_tensorMap]`. Both sides reduce to the same expression.
-/
theorem vecCoords_toFinAdele (x : ι → K ⊗[K] E) (a : ι × κ) :
    vecCoords (FinAdele K) b (toFinAdele K E ι x) a = algebraMap K (FinAdele K) (vecCoords K b x a) := by
  simp only [vecCoords, toFinAdele_apply, repr_tensorMap]
  rfl

omit [Algebra.IsQuadraticExtension K E] [Fintype ι] [DecidableEq ι] in
/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `only [toFinAdele_apply, Pi.smul_apply, map_smul, algebraMap_smul]`.
-/
theorem toFinAdele_smul (k : K) (x : ι → K ⊗[K] E) :
    toFinAdele K E ι (k • x) = algebraMap K (FinAdele K) k • toFinAdele K E ι x := by
  funext i
  simp only [toFinAdele_apply, Pi.smul_apply, map_smul, algebraMap_smul]

omit [Algebra.IsQuadraticExtension K E] [Fintype ι] [DecidableEq ι] in
/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `only [toFinAdele_apply, Pi.smul_apply, smul_eq_mul, map_mul]`.
-/
theorem toFinAdele_mul_smul (z : K ⊗[K] E) (x : ι → K ⊗[K] E) :
    toFinAdele K E ι (z • x) = tensorMap E (Algebra.ofId K (FinAdele K)) z • toFinAdele K E ι x := by
  funext i
  simp only [toFinAdele_apply, Pi.smul_apply, smul_eq_mul, map_mul]

def finDiag (H : Matrix ι ι E) : unitaryPoints K E H K →* unitaryPoints K E H (FinAdele K) :=
  unitaryMap K E H (Algebra.ofId K (FinAdele K))

/- English proof (translation)
Use function extensionality and compare the values at `i`. Rewrite using `[toFinAdele_apply, finDiag, unitaryMat_unitaryMap]`. Conclude with `RingHom.map_mulVec (tensorMap E (Algebra.ofId K (FinAdele K))).toRingHom (unitaryMat γ) x i`.
-/
theorem toFinAdele_mulVec {H : Matrix ι ι E} (γ : unitaryPoints K E H K)
    (x : ι → K ⊗[K] E) :
    toFinAdele K E ι (unitaryMat γ *ᵥ x) = unitaryMat (finDiag H γ) *ᵥ toFinAdele K E ι x := by
  funext i
  rw [toFinAdele_apply, finDiag, unitaryMat_unitaryMap]
  exact RingHom.map_mulVec (tensorMap E (Algebra.ofId K (FinAdele K))).toRingHom (unitaryMat γ) x i

omit [Fintype ι] [DecidableEq ι] in

/- English proof (translation)
Set `b` to `Module.finBasis K E`. Set `Φ` to `vecCoordsHomeomorph (ι := ι) (FinAdele K) b`. Establish `hd : DenseRange (Pi.map fun _ : ι => Pi.map fun _ : Fin (Module.finrank K E) => algebraMap K (FinAdele K))` using `DenseRange.piMap fun _ => DenseRange.piMap fun _ => AdelicGLn.denseRange_algebraMap_finiteAdeleRing K`. Establish `hrange : Set.range (Φ ∘ toFinAdele K E ι) = Set.range (Pi.map fun _ : ι => Pi.map fun _ : Fin (Module.finrank K E) => algebraMap K (FinAdele K))`. Use extensionality with `y`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, rfl⟩`. Use `⟨fun i k => vecCoords K b x (i, k), ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i k`. Simplify using `only [Φ, Function.comp_apply, Pi.map_apply, vecCoordsHomeomorph, Homeomorph.piCongrRight_apply, tensorCoordsHomeomorph_apply]`.

Conclude with `(vecCoords_toFinAdele b x (i, k)).symm`. Introduce and unpack `⟨c, rfl⟩`. Use `⟨vecOfCoords b K fun a => c a.1 a.2, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i k`. Simplify using `only [Φ, Function.comp_apply, Pi.map_apply, vecCoordsHomeomorph, Homeomorph.piCongrRight_apply, tensorCoordsHomeomorph_apply]`.

Use `vecCoords_toFinAdele b (vecOfCoords b K fun a => c a.1 a.2) (i, k)` as an intermediate fact. Rewrite `this` using `[vecCoords_vecOfCoords]`. Conclude with `this`. Establish `h1 : DenseRange (Φ ∘ toFinAdele K E ι)`. Unfold `DenseRange`.

Rewrite using `[hrange]`. Conclude with `hd`. Establish `h2 : toFinAdele K E ι = Φ.symm ∘ (Φ ∘ toFinAdele K E ι)`. Use function extensionality and compare the values at `x`. Simplify using the standard rewrite rules.

Rewrite using `[h2]`. Conclude with `Φ.symm.surjective.denseRange.comp h1 Φ.symm.continuous`.
-/
theorem denseRange_toFinAdele : DenseRange (toFinAdele K E ι) := by
  let b := Module.finBasis K E
  let Φ := vecCoordsHomeomorph (ι := ι) (FinAdele K) b
  have hd : DenseRange (Pi.map fun _ : ι => Pi.map fun _ : Fin (Module.finrank K E) => algebraMap K (FinAdele K)) :=
    DenseRange.piMap fun _ => DenseRange.piMap fun _ =>
      AdelicGLn.denseRange_algebraMap_finiteAdeleRing K
  have hrange : Set.range (Φ ∘ toFinAdele K E ι) =
      Set.range (Pi.map fun _ : ι => Pi.map fun _ : Fin (Module.finrank K E) => algebraMap K (FinAdele K)) := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      refine ⟨fun i k => vecCoords K b x (i, k), ?_⟩
      funext i k
      simp only [Φ, Function.comp_apply, Pi.map_apply, vecCoordsHomeomorph,
        Homeomorph.piCongrRight_apply, tensorCoordsHomeomorph_apply]
      exact (vecCoords_toFinAdele b x (i, k)).symm
    · rintro ⟨c, rfl⟩
      refine ⟨vecOfCoords b K fun a => c a.1 a.2, ?_⟩
      funext i k
      simp only [Φ, Function.comp_apply, Pi.map_apply, vecCoordsHomeomorph,
        Homeomorph.piCongrRight_apply, tensorCoordsHomeomorph_apply]
      have := vecCoords_toFinAdele b (vecOfCoords b K fun a => c a.1 a.2) (i, k)
      rw [vecCoords_vecOfCoords] at this
      exact this
  have h1 : DenseRange (Φ ∘ toFinAdele K E ι) := by
    unfold DenseRange
    rw [hrange]
    exact hd
  have h2 : toFinAdele K E ι = Φ.symm ∘ (Φ ∘ toFinAdele K E ι) := by
    funext x
    simp
  rw [h2]
  exact Φ.symm.surjective.denseRange.comp h1 Φ.symm.continuous

/- English proof (translation)
Set `ω` to `integralBasis K`. Set `m : ℤ` to `∏ z ∈ s, ∏ t, ((ω.repr z t).den : ℤ)`. Use `⟨m, ?_, fun z hz => ?_⟩` and prove the remaining obligations. Conclude with `Finset.prod_ne_zero_iff.2 fun z _ => Finset.prod_ne_zero_iff.2 fun t _ => by`. Conclude with `(ω.repr z t).den_nz` after adjusting the coercions.

Establish `hω : ∀ t, IsIntegral ℤ (ω t)` using `fun t => by`. Rewrite using `[integralBasis_apply]`. Conclude with `RingOfIntegers.isIntegral_coe _`. Establish `hdvd : ∀ t, ((ω.repr z t).den : ℤ) ∣ m` using `fun t => (Finset.dvd_prod_of_mem (fun t => ((ω.repr z t).den : ℤ)) (Finset.mem_univ t)).trans (Finset.dvd_prod_of_mem (fun z => ∏ t, ((ω.repr z t).den : ℤ)) hz)`. Establish `hz' : (m : K) * z = ∑ t, ((m * ω.repr z t : ℚ) : K) * ω t` using `by conv_lhs => rw [← ω.sum_repr z]`.

Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun t _ => ?_` and prove the remaining obligations. Rewrite using `[Rat.smul_def]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[hz']`. Use `IsIntegral.sum _ fun t _ => IsIntegral.mul ?_ (hω t)` and prove the remaining obligations. Take `⟨k, hk⟩` from `hdvd t`. Establish `: (m * ω.repr z t : ℚ) = (k * (ω.repr z t).num : ℤ)`. Rewrite using `[hk]`.

Use `push_cast`. Rewrite using `[mul_comm ((ω.repr z t).den : ℚ) k, mul_assoc, Rat.den_mul_eq_num]`. Rewrite using `[this, Rat.cast_intCast]`. Conclude with `isIntegral_algebraMap (x := ((k * (ω.repr z t).num : ℤ)))`.
-/
theorem exists_int_mul_isIntegral (s : Finset K) :
    ∃ m : ℤ, m ≠ 0 ∧ ∀ z ∈ s, IsIntegral ℤ ((m : K) * z) := by
  classical
  let ω := integralBasis K
  let m : ℤ := ∏ z ∈ s, ∏ t, ((ω.repr z t).den : ℤ)
  refine ⟨m, ?_, fun z hz => ?_⟩
  · exact Finset.prod_ne_zero_iff.2 fun z _ => Finset.prod_ne_zero_iff.2 fun t _ => by
      exact_mod_cast (ω.repr z t).den_nz
  · have hω : ∀ t, IsIntegral ℤ (ω t) := fun t => by
      rw [integralBasis_apply]
      exact RingOfIntegers.isIntegral_coe _
    have hdvd : ∀ t, ((ω.repr z t).den : ℤ) ∣ m := fun t =>
      (Finset.dvd_prod_of_mem (fun t => ((ω.repr z t).den : ℤ)) (Finset.mem_univ t)).trans
        (Finset.dvd_prod_of_mem (fun z => ∏ t, ((ω.repr z t).den : ℤ)) hz)
    have hz' : (m : K) * z = ∑ t, ((m * ω.repr z t : ℚ) : K) * ω t := by
      conv_lhs => rw [← ω.sum_repr z]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [Rat.smul_def]
      push_cast
      ring
    rw [hz']
    refine IsIntegral.sum _ fun t _ => IsIntegral.mul ?_ (hω t)
    obtain ⟨k, hk⟩ := hdvd t
    have : (m * ω.repr z t : ℚ) = (k * (ω.repr z t).num : ℤ) := by
      rw [hk]
      push_cast
      rw [mul_comm ((ω.repr z t).den : ℚ) k, mul_assoc, Rat.den_mul_eq_num]
    rw [this, Rat.cast_intCast]
    exact isIntegral_algebraMap (x := ((k * (ω.repr z t).num : ℤ)))

section Lattice

variable (H : Matrix ι ι E)

variable (K) in

abbrev intAdeles : Subring (FinAdele K) := integralFiniteAdeles (𝓞 K) K

omit [Algebra.IsQuadraticExtension K E] [DecidableEq ι] [Fintype ι] [Fintype κ] in
/- English proof (translation)
Rewrite `*` using `[mem_stdLattice_iff]`. Introduce `a`. Rewrite using `[vecCoords_add]`. Conclude with `add_mem (hx a) (hy a)`.
-/
theorem stdLattice_add {x y : ι → FinAdele K ⊗[K] E} (hx : x ∈ stdLattice ι (FinAdele K) b (intAdeles K))
    (hy : y ∈ stdLattice ι (FinAdele K) b (intAdeles K)) :
    x + y ∈ stdLattice ι (FinAdele K) b (intAdeles K) := by
  rw [mem_stdLattice_iff] at *
  intro a
  rw [vecCoords_add]
  exact add_mem (hx a) (hy a)

omit [Algebra.IsQuadraticExtension K E] [DecidableEq ι] [Fintype ι] [Fintype κ] in
/- English proof (translation)
Rewrite `*` using `[mem_stdLattice_iff]`. Introduce `a`. Rewrite using `[vecCoords_smul]`. Conclude with `mul_mem hc (hx a)`.
-/
theorem stdLattice_smul {x : ι → FinAdele K ⊗[K] E} (hx : x ∈ stdLattice ι (FinAdele K) b (intAdeles K))
    {c : FinAdele K} (hc : c ∈ intAdeles K) : c • x ∈ stdLattice ι (FinAdele K) b (intAdeles K) := by
  rw [mem_stdLattice_iff] at *
  intro a
  rw [vecCoords_smul]
  exact mul_mem hc (hx a)

omit [Algebra.IsQuadraticExtension K E] [DecidableEq ι] [Fintype ι] [Fintype κ] in
/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`. Rewrite using `[Finset.sum_empty, mem_stdLattice_iff]`. Introduce `a`. Rewrite using `[vecCoords_zero]`.

Conclude with `zero_mem _`. Consider the case `insert a s ha ih`. Rewrite using `[Finset.sum_insert ha]`. Conclude with `stdLattice_add b (hx a (Finset.mem_insert_self a s)) (ih fun c hc => hx c (Finset.mem_insert_of_mem hc))`.
-/
theorem stdLattice_sum {s : Finset (ι × κ)} {x : ι × κ → ι → FinAdele K ⊗[K] E}
    (hx : ∀ a ∈ s, x a ∈ stdLattice ι (FinAdele K) b (intAdeles K)) :
    ∑ a ∈ s, x a ∈ stdLattice ι (FinAdele K) b (intAdeles K) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, mem_stdLattice_iff]
    intro a
    rw [vecCoords_zero]
    exact zero_mem _
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact stdLattice_add b (hx a (Finset.mem_insert_self a s))
      (ih fun c hc => hx c (Finset.mem_insert_of_mem hc))

omit [Algebra.IsQuadraticExtension K E] [Fintype ι] [Fintype κ] in
/- English proof (translation)
Rewrite using `[mem_stdLattice_iff]`. Introduce `c`. Rewrite using `[vecCoords_stdVec]`. Use `split_ifs`. Conclude with `one_mem _`.

Conclude with `zero_mem _`.
-/
theorem stdVec_mem_stdLattice [DecidableEq κ] (a : ι × κ) :
    stdVec (FinAdele K) b a ∈ stdLattice ι (FinAdele K) b (intAdeles K) := by
  rw [mem_stdLattice_iff]
  intro c
  rw [vecCoords_stdVec]
  split_ifs
  · exact one_mem _
  · exact zero_mem _

omit [NumberField K] in
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem unitaryMat_mul {R : Type*} [CommRing R] [Algebra K R] (g g' : unitaryPoints K E H R) :
    unitaryMat (g * g') = unitaryMat g * unitaryMat g' := rfl

omit [NumberField K] in
/- English proof (translation)
Use `show (((g⁻¹ : unitaryPoints K E H R) : GL ι (R ⊗[K] E)) : Matrix ι ι (R ⊗[K] E)) * ((g : GL ι (R ⊗[K] E)) : Matrix ι ι (R ⊗[K] E)) = 1`. Rewrite using `[Subgroup.coe_inv, Units.inv_mul]`.
-/
theorem unitaryMat_inv_mul {R : Type*} [CommRing R] [Algebra K R] (g : unitaryPoints K E H R) :
    unitaryMat g⁻¹ * unitaryMat g = 1 := by
  show (((g⁻¹ : unitaryPoints K E H R) : GL ι (R ⊗[K] E)) : Matrix ι ι (R ⊗[K] E)) *
    ((g : GL ι (R ⊗[K] E)) : Matrix ι ι (R ⊗[K] E)) = 1
  rw [Subgroup.coe_inv, Units.inv_mul]

omit [NumberField K] in
/- English proof (translation)
Use `show ((g : GL ι (R ⊗[K] E)) : Matrix ι ι (R ⊗[K] E)) * (((g⁻¹ : unitaryPoints K E H R) : GL ι (R ⊗[K] E)) : Matrix ι ι (R ⊗[K] E)) = 1`. Rewrite using `[Subgroup.coe_inv, Units.mul_inv]`.
-/
theorem unitaryMat_mul_inv {R : Type*} [CommRing R] [Algebra K R] (g : unitaryPoints K E H R) :
    unitaryMat g * unitaryMat g⁻¹ = 1 := by
  show ((g : GL ι (R ⊗[K] E)) : Matrix ι ι (R ⊗[K] E)) *
    (((g⁻¹ : unitaryPoints K E H R) : GL ι (R ⊗[K] E)) : Matrix ι ι (R ⊗[K] E)) = 1
  rw [Subgroup.coe_inv, Units.mul_inv]

def adelicLattice (g : unitaryPoints K E H (FinAdele K)) : AddSubgroup (ι → K ⊗[K] E) where
  carrier := {x | unitaryMat g⁻¹ *ᵥ toFinAdele K E ι x ∈ stdLattice ι (FinAdele K) b (intAdeles K)}
  zero_mem' := by
    show unitaryMat g⁻¹ *ᵥ toFinAdele K E ι 0 ∈ stdLattice ι (FinAdele K) b (intAdeles K)
    rw [map_zero, mulVec_zero, mem_stdLattice_iff]
    intro a
    rw [vecCoords_zero]
    exact zero_mem _
  add_mem' := by
    intro x y hx hy
    show unitaryMat g⁻¹ *ᵥ toFinAdele K E ι (x + y) ∈ stdLattice ι (FinAdele K) b (intAdeles K)
    rw [map_add, mulVec_add]
    exact stdLattice_add b hx hy
  neg_mem' := by
    intro x hx
    show unitaryMat g⁻¹ *ᵥ toFinAdele K E ι (-x) ∈ stdLattice ι (FinAdele K) b (intAdeles K)
    rw [map_neg, mulVec_neg, mem_stdLattice_iff]
    intro a
    rw [vecCoords_neg]
    exact neg_mem (((mem_stdLattice_iff b _ _).1 hx) a)

variable {H b}

omit [Fintype κ] in
/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_adelicLattice {g : unitaryPoints K E H (FinAdele K)} {x : ι → K ⊗[K] E} :
    x ∈ adelicLattice b H g ↔
      unitaryMat g⁻¹ *ᵥ toFinAdele K E ι x ∈ stdLattice ι (FinAdele K) b (intAdeles K) := Iff.rfl

omit [Fintype κ] in

/- English proof (translation)
Rewrite using `[mem_adelicLattice, toFinAdele_smul, mulVec_smul]`. Conclude with `stdLattice_smul b hx (algebraMap_integers_mem_integralFiniteAdeles K z)`.
-/
theorem intSmul_mem_adelicLattice {g : unitaryPoints K E H (FinAdele K)} {x : ι → K ⊗[K] E}
    (hx : x ∈ adelicLattice b H g) (z : 𝓞 K) : (z : K) • x ∈ adelicLattice b H g := by
  rw [mem_adelicLattice, toFinAdele_smul, mulVec_smul]
  exact stdLattice_smul b hx (algebraMap_integers_mem_integralFiniteAdeles K z)

end Lattice

section Topology

variable {H : Matrix ι ι E} {b}

omit [Fintype ι] [DecidableEq ι] in
/- English proof (translation)
Establish `: (fun z : ι → FinAdele K ⊗[K] E => vecCoords (FinAdele K) b z a) = fun z => tensorCoordsHomeomorph (FinAdele K) b (z a.1) a.2`. Use function extensionality and compare the values at `z`. Rewrite using `[tensorCoordsHomeomorph_apply]`. Both sides reduce to the same expression. Rewrite using `[this]`.

Conclude with `(continuous_apply a.2).comp ((tensorCoordsHomeomorph (FinAdele K) b).continuous.comp (continuous_apply a.1))`.
-/
theorem continuous_vecCoords_finAdele (a : ι × κ) :
    Continuous fun z : ι → FinAdele K ⊗[K] E => vecCoords (FinAdele K) b z a := by
  have : (fun z : ι → FinAdele K ⊗[K] E => vecCoords (FinAdele K) b z a) =
      fun z => tensorCoordsHomeomorph (FinAdele K) b (z a.1) a.2 := by
    funext z
    rw [tensorCoordsHomeomorph_apply]
    rfl
  rw [this]
  exact (continuous_apply a.2).comp ((tensorCoordsHomeomorph (FinAdele K) b).continuous.comp
    (continuous_apply a.1))

variable (b H) in

def transLattice (g : unitaryPoints K E H (FinAdele K)) : Set (ι → FinAdele K ⊗[K] E) :=
  {z | unitaryMat g⁻¹ *ᵥ z ∈ stdLattice ι (FinAdele K) b (intAdeles K)}

omit [Fintype κ] in
/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_transLattice {g : unitaryPoints K E H (FinAdele K)} {z : ι → FinAdele K ⊗[K] E} :
    z ∈ transLattice b H g ↔ unitaryMat g⁻¹ *ᵥ z ∈ stdLattice ι (FinAdele K) b (intAdeles K) :=
  Iff.rfl

/- English proof (translation)
The claim follows from `(isOpen_stdLattice (FinAdele K) b (isOpen_integralFiniteAdeles (R := 𝓞 K) (K := K))).preimage (continuous_const.matrix_mulVec continuous_id)`.
-/
theorem isOpen_transLattice (g : unitaryPoints K E H (FinAdele K)) : IsOpen (transLattice b H g) :=
  (isOpen_stdLattice (FinAdele K) b (isOpen_integralFiniteAdeles (R := 𝓞 K) (K := K))).preimage
    (continuous_const.matrix_mulVec continuous_id)

/- English proof (translation)
Establish `: T2Space (FinAdele K)` using `t2Space_finiteAdeleRing K`. Establish `: T2Space (FinAdele K ⊗[K] E)` using `t2Space_tensor (FinAdele K)`. Conclude with `(isCompact_stdLattice (FinAdele K) b (isCompact_integralFiniteAdeles K)).isClosed.preimage (continuous_const.matrix_mulVec continuous_id)`.
-/
theorem isClosed_transLattice (g : unitaryPoints K E H (FinAdele K)) :
    IsClosed (transLattice b H g) := by
  have : T2Space (FinAdele K) := t2Space_finiteAdeleRing K
  have : T2Space (FinAdele K ⊗[K] E) := t2Space_tensor (FinAdele K)
  exact (isCompact_stdLattice (FinAdele K) b (isCompact_integralFiniteAdeles K)).isClosed.preimage
    (continuous_const.matrix_mulVec continuous_id)

/- English proof (translation)
Establish `himage : toFinAdele K E ι '' (adelicLattice b H g : Set (ι → K ⊗[K] E)) = transLattice b H g ∩ Set.range (toFinAdele K E ι)`. Use extensionality with `z`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, hx, rfl⟩`. Conclude with `⟨hx, x, rfl⟩`.

Introduce and unpack `⟨hz, x, rfl⟩`. Conclude with `⟨x, hz, rfl⟩`. Apply `le_antisymm` to reduce the goal to its premises. Conclude with `closure_minimal (by rw [himage]; exact Set.inter_subset_left) (isClosed_transLattice g)`. Rewrite using `[himage]`.

Conclude with `denseRange_toFinAdele.open_subset_closure_inter (isOpen_transLattice g)`.
-/
theorem closure_image_adelicLattice (g : unitaryPoints K E H (FinAdele K)) :
    closure (toFinAdele K E ι '' (adelicLattice b H g : Set (ι → K ⊗[K] E))) = transLattice b H g := by
  have himage : toFinAdele K E ι '' (adelicLattice b H g : Set (ι → K ⊗[K] E)) =
      transLattice b H g ∩ Set.range (toFinAdele K E ι) := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨hx, x, rfl⟩
    · rintro ⟨hz, x, rfl⟩
      exact ⟨x, hz, rfl⟩
  apply le_antisymm
  · exact closure_minimal (by rw [himage]; exact Set.inter_subset_left) (isClosed_transLattice g)
  · rw [himage]
    exact denseRange_toFinAdele.open_subset_closure_inter (isOpen_transLattice g)

end Topology

section Integrality

variable {H : Matrix ι ι E} {b}

omit [Fintype κ] [DecidableEq ι] in
/- English proof (translation)
The claim follows from `hermTrace_tensorMap (Algebra.ofId K (FinAdele K)) x y`.
-/
theorem algebraMap_hermTrace (x y : ι → K ⊗[K] E) :
    algebraMap K (FinAdele K) (hermTrace K H K x y) =
      hermTrace K H (FinAdele K) (toFinAdele K E ι x) (toFinAdele K E ι y) :=
  hermTrace_tensorMap (Algebra.ofId K (FinAdele K)) x y

omit [Algebra.IsQuadraticExtension K E] in
/- English proof (translation)
Take `⟨z, hz⟩` from `exists_eq_of_forall_mem_adicCompletionIntegers K t fun v => h v`. Rewrite using `[← hz]`. Conclude with `RingOfIntegers.isIntegral_coe z`.
-/
theorem isIntegral_of_algebraMap_mem {t : K} (h : algebraMap K (FinAdele K) t ∈ intAdeles K) :
    IsIntegral ℤ t := by
  obtain ⟨z, hz⟩ := exists_eq_of_forall_mem_adicCompletionIntegers K t fun v => h v
  rw [← hz]
  exact RingOfIntegers.isIntegral_coe z

omit [Algebra.IsQuadraticExtension K E] in
/- English proof (translation)
The claim follows from `algebraMap_integers_mem_integralFiniteAdeles K ⟨t, h⟩`.
-/
theorem algebraMap_mem_of_isIntegral {t : K} (h : IsIntegral ℤ t) :
    algebraMap K (FinAdele K) t ∈ intAdeles K :=
  algebraMap_integers_mem_integralFiniteAdeles K ⟨t, h⟩

variable (H b) in

/- English proof (translation)
Take `⟨d, hd0, hd⟩` from `exists_int_mul_isIntegral (Finset.univ.image fun p : (ι × κ) × (ι × κ) => traceGram H b p.1 p.2)`. Use `⟨d, hd0, fun g x y hx hy => isIntegral_of_algebraMap_mem ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, algebraMap_hermTrace, ← hermTrace_mulVec g⁻¹, hermTrace_eq_sum_traceGram (H := H) (b := b) (FinAdele K), Finset.mul_sum]`. Use `Subring.sum_mem _ fun a _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.mul_sum]`.

Use `Subring.sum_mem _ fun c _ => ?_` and prove the remaining obligations. Establish `h1` using `((mem_stdLattice_iff b _ _).1 hx) a`. Establish `h2` using `((mem_stdLattice_iff b _ _).1 hy) c`. Establish `h3` using `algebraMap_mem_of_isIntegral (hd _ (Finset.mem_image_of_mem _ (Finset.mem_univ (a, c))))`. Rewrite `h3` using `[map_mul, map_intCast]`.

Establish `: algebraMap K (FinAdele K) d * (vecCoords (FinAdele K) b (unitaryMat g⁻¹ *ᵥ toFinAdele K E ι x) a * vecCoords (FinAdele K) b (unitaryMat g⁻¹ *ᵥ toFinAdele K E ι y) c * algebraMap K (FinAdele K) (traceGram H b a c)) = vecCoords (FinAdele K) b (unitaryMat g⁻¹ *ᵥ toFinAdele K E ι x …`. Rewrite using `[map_intCast]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Conclude with `mul_mem (mul_mem h1 h2) h3`.
-/
theorem exists_int_isIntegral_hermTrace : ∃ d : ℤ, d ≠ 0 ∧
    ∀ (g : unitaryPoints K E H (FinAdele K)) (x y : ι → K ⊗[K] E), x ∈ adelicLattice b H g →
      y ∈ adelicLattice b H g → IsIntegral ℤ ((d : K) * hermTrace K H K x y) := by
  classical
  obtain ⟨d, hd0, hd⟩ := exists_int_mul_isIntegral
    (Finset.univ.image fun p : (ι × κ) × (ι × κ) => traceGram H b p.1 p.2)
  refine ⟨d, hd0, fun g x y hx hy => isIntegral_of_algebraMap_mem ?_⟩
  rw [map_mul, algebraMap_hermTrace, ← hermTrace_mulVec g⁻¹,
    hermTrace_eq_sum_traceGram (H := H) (b := b) (FinAdele K), Finset.mul_sum]
  refine Subring.sum_mem _ fun a _ => ?_
  rw [Finset.mul_sum]
  refine Subring.sum_mem _ fun c _ => ?_
  have h1 := ((mem_stdLattice_iff b _ _).1 hx) a
  have h2 := ((mem_stdLattice_iff b _ _).1 hy) c
  have h3 := algebraMap_mem_of_isIntegral (hd _ (Finset.mem_image_of_mem _
    (Finset.mem_univ (a, c))))
  rw [map_mul, map_intCast] at h3
  have : algebraMap K (FinAdele K) d * (vecCoords (FinAdele K) b
      (unitaryMat g⁻¹ *ᵥ toFinAdele K E ι x) a * vecCoords (FinAdele K) b
      (unitaryMat g⁻¹ *ᵥ toFinAdele K E ι y) c * algebraMap K (FinAdele K) (traceGram H b a c)) =
      vecCoords (FinAdele K) b (unitaryMat g⁻¹ *ᵥ toFinAdele K E ι x) a *
        vecCoords (FinAdele K) b (unitaryMat g⁻¹ *ᵥ toFinAdele K E ι y) c *
        ((d : FinAdele K) * algebraMap K (FinAdele K) (traceGram H b a c)) := by
    rw [map_intCast]; ring
  rw [this]
  exact mul_mem (mul_mem h1 h2) h3

end Integrality

section Dual

variable {H : Matrix ι ι E} {b}

omit [DecidableEq ι] in
/- English proof (translation)
The claim follows from `continuous_finsetSum _ fun _ _ => continuous_finsetSum _ fun c _ => (continuous_const.mul (continuous_vecCoords_finAdele c)).mul continuous_const`.
-/
theorem continuous_sum_coords_mul (p : ι → FinAdele K ⊗[K] E)
    (C : ι × κ → ι × κ → FinAdele K) :
    Continuous fun z : ι → FinAdele K ⊗[K] E =>
      ∑ a, ∑ c, vecCoords (FinAdele K) b p a * vecCoords (FinAdele K) b z c * C a c :=
  continuous_finsetSum _ fun _ _ => continuous_finsetSum _ fun c _ =>
    (continuous_const.mul (continuous_vecCoords_finAdele c)).mul continuous_const

variable (H b) in

/- English proof (translation)
Use `set M := traceGram H b`. Use `set A : Matrix (ι × κ) (ι × κ) K := c • Mᵀ`. Establish `hA : IsUnit A.det`. Rewrite using `[Matrix.det_smul, Matrix.det_transpose]`. Conclude with `(IsUnit.pow _ (isUnit_iff_ne_zero.2 hc)).mul hM`.

Use `set N := A⁻¹`. Take `⟨m, hm0, hm⟩` from `exists_int_mul_isIntegral (Finset.univ.image fun p : (ι × κ) × (ι × κ) => N p.1 p.2)`. Use `⟨m, hm0, fun g y hy => ?_⟩` and prove the remaining obligations. Use `set φ := algebraMap K (FinAdele K)`. Use `set p := toFinAdele K E ι y`.

Use `set u := unitaryMat g⁻¹ *ᵥ p`. Establish `hT2 : T2Space (FinAdele K)` using `t2Space_finiteAdeleRing K`. Establish `hS : ∀ a, φ c * hermTrace K H (FinAdele K) p (unitaryMat g *ᵥ stdVec (FinAdele K) b a) ∈ intAdeles K`. Establish `hclosed : IsClosed {z : ι → FinAdele K ⊗[K] E | φ c * hermTrace K H (FinAdele K) p z ∈ intAdeles K}`. Establish `hfun : (fun z : ι → FinAdele K ⊗[K] E => φ c * hermTrace K H (FinAdele K) p z) = fun z => φ c * ∑ a, ∑ c', vecCoords (FinAdele K) b p a * vecCoords (FinAdele K) b z c' * φ (M a c')`.

Use function extensionality and compare the values at `z`. Rewrite using `[hermTrace_eq_sum_traceGram (H := H) (b := b) (FinAdele K)]`. Establish `hcont : Continuous fun z : ι → FinAdele K ⊗[K] E => φ c * hermTrace K H (FinAdele K) p z`. Rewrite using `[hfun]`. Conclude with `continuous_const.mul (continuous_sum_coords_mul p fun a c' => φ (M a c'))`.

Conclude with `(isCompact_integralFiniteAdeles K).isClosed.preimage hcont`. Establish `hsub : toFinAdele K E ι '' (adelicLattice b H g : Set (ι → K ⊗[K] E)) ⊆ {z | φ c * hermTrace K H (FinAdele K) p z ∈ intAdeles K}`. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Use `show φ c * hermTrace K H (FinAdele K) p (toFinAdele K E ι x) ∈ intAdeles K`. Rewrite using `[← algebraMap_hermTrace, ← map_mul]`.

Conclude with `algebraMap_mem_of_isIntegral (hy x hx)`. Establish `hcl` using `closure_minimal hsub hclosed`. Rewrite `hcl` using `[closure_image_adelicLattice]`. Introduce `a`. Apply `hcl` to reduce the goal to its premises.

Rewrite using `[mem_transLattice, mulVec_mulVec, unitaryMat_inv_mul, one_mulVec]`. Conclude with `stdVec_mem_stdLattice b a`. Use `set cu : ι × κ → FinAdele K := fun a => vecCoords (FinAdele K) b u a`. Establish `hAu : ∀ a, (A.map φ *ᵥ cu) a ∈ intAdeles K`. Introduce `a`.

Establish `h` using `hS a`. Rewrite `h` using `[← hermTrace_mulVec g⁻¹, mulVec_mulVec, unitaryMat_inv_mul, one_mulVec, hermTrace_eq_sum_traceGram (H := H) (b := b) (FinAdele K)]`. Simplify using `only [vecCoords_stdVec, mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true] at h`. Use `h using 1` and compare the differences between its conclusion and the goal. Simplify using `only [mulVec, dotProduct, Matrix.map_apply, A, Matrix.smul_apply, Matrix.transpose_apply, smul_eq_mul, map_mul, Finset.mul_sum, cu]`.

Use `Finset.sum_congr rfl fun a' _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Establish `hcu : cu = N.map φ *ᵥ (A.map φ *ᵥ cu)`. Rewrite using `[mulVec_mulVec, ← Matrix.map_mul, Matrix.nonsing_inv_mul A hA, Matrix.map_one φ (map_zero φ) (map_one φ), one_mulVec]`. Rewrite using `[mem_adelicLattice, toFinAdele_smul, mulVec_smul, mem_stdLattice_iff]`.

Introduce `a`. Rewrite using `[vecCoords_smul]`. Express the relevant statement in the definitionally equal form `φ m * cu a ∈ intAdeles K`. Rewrite using `[hcu, mulVec, dotProduct, Finset.mul_sum]`. Use `Subring.sum_mem _ fun a' _ => ?_` and prove the remaining obligations.

Rewrite using `[Matrix.map_apply, ← mul_assoc, ← map_mul]`. Conclude with `mul_mem (algebraMap_mem_of_isIntegral (hm _ (Finset.mem_image_of_mem _ (Finset.mem_univ (a, a'))))) (hAu a')`.
-/
theorem exists_int_smul_mem_of_forall_isIntegral [DecidableEq κ] (hM : IsUnit (traceGram H b).det) (c : K)
    (hc : c ≠ 0) :
    ∃ m : ℤ, m ≠ 0 ∧ ∀ (g : unitaryPoints K E H (FinAdele K)) (y : ι → K ⊗[K] E),
      (∀ x ∈ adelicLattice b H g, IsIntegral ℤ (c * hermTrace K H K y x)) →
        (m : K) • y ∈ adelicLattice b H g := by
  classical
  set M := traceGram H b
  set A : Matrix (ι × κ) (ι × κ) K := c • Mᵀ
  have hA : IsUnit A.det := by
    rw [Matrix.det_smul, Matrix.det_transpose]
    exact (IsUnit.pow _ (isUnit_iff_ne_zero.2 hc)).mul hM
  set N := A⁻¹
  obtain ⟨m, hm0, hm⟩ := exists_int_mul_isIntegral
    (Finset.univ.image fun p : (ι × κ) × (ι × κ) => N p.1 p.2)
  refine ⟨m, hm0, fun g y hy => ?_⟩
  set φ := algebraMap K (FinAdele K)
  set p := toFinAdele K E ι y
  set u := unitaryMat g⁻¹ *ᵥ p
  have hT2 : T2Space (FinAdele K) := t2Space_finiteAdeleRing K

  have hS : ∀ a, φ c * hermTrace K H (FinAdele K) p (unitaryMat g *ᵥ stdVec (FinAdele K) b a) ∈
      intAdeles K := by
    have hclosed : IsClosed {z : ι → FinAdele K ⊗[K] E |
        φ c * hermTrace K H (FinAdele K) p z ∈ intAdeles K} := by
      have hfun : (fun z : ι → FinAdele K ⊗[K] E => φ c * hermTrace K H (FinAdele K) p z) =
          fun z => φ c * ∑ a, ∑ c', vecCoords (FinAdele K) b p a * vecCoords (FinAdele K) b z c' *
            φ (M a c') := by
        funext z
        rw [hermTrace_eq_sum_traceGram (H := H) (b := b) (FinAdele K)]
      have hcont : Continuous fun z : ι → FinAdele K ⊗[K] E =>
          φ c * hermTrace K H (FinAdele K) p z := by
        rw [hfun]
        exact continuous_const.mul (continuous_sum_coords_mul p fun a c' => φ (M a c'))
      exact (isCompact_integralFiniteAdeles K).isClosed.preimage hcont
    have hsub : toFinAdele K E ι '' (adelicLattice b H g : Set (ι → K ⊗[K] E)) ⊆
        {z | φ c * hermTrace K H (FinAdele K) p z ∈ intAdeles K} := by
      rintro _ ⟨x, hx, rfl⟩
      show φ c * hermTrace K H (FinAdele K) p (toFinAdele K E ι x) ∈ intAdeles K
      rw [← algebraMap_hermTrace, ← map_mul]
      exact algebraMap_mem_of_isIntegral (hy x hx)
    have hcl := closure_minimal hsub hclosed
    rw [closure_image_adelicLattice] at hcl
    intro a
    apply hcl
    rw [mem_transLattice, mulVec_mulVec, unitaryMat_inv_mul, one_mulVec]
    exact stdVec_mem_stdLattice b a

  set cu : ι × κ → FinAdele K := fun a => vecCoords (FinAdele K) b u a
  have hAu : ∀ a, (A.map φ *ᵥ cu) a ∈ intAdeles K := by
    intro a
    have h := hS a
    rw [← hermTrace_mulVec g⁻¹, mulVec_mulVec, unitaryMat_inv_mul, one_mulVec,
      hermTrace_eq_sum_traceGram (H := H) (b := b) (FinAdele K)] at h
    simp only [vecCoords_stdVec, mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, if_true] at h
    convert h using 1
    simp only [mulVec, dotProduct, Matrix.map_apply, A, Matrix.smul_apply, Matrix.transpose_apply,
      smul_eq_mul, map_mul, Finset.mul_sum, cu]
    refine Finset.sum_congr rfl fun a' _ => ?_
    ring
  have hcu : cu = N.map φ *ᵥ (A.map φ *ᵥ cu) := by
    rw [mulVec_mulVec, ← Matrix.map_mul, Matrix.nonsing_inv_mul A hA, Matrix.map_one φ (map_zero φ)
      (map_one φ), one_mulVec]
  rw [mem_adelicLattice, toFinAdele_smul, mulVec_smul, mem_stdLattice_iff]
  intro a
  rw [vecCoords_smul]
  change φ m * cu a ∈ intAdeles K
  rw [hcu, mulVec, dotProduct, Finset.mul_sum]
  refine Subring.sum_mem _ fun a' _ => ?_
  rw [Matrix.map_apply, ← mul_assoc, ← map_mul]
  exact mul_mem (algebraMap_mem_of_isIntegral (hm _ (Finset.mem_image_of_mem _
    (Finset.mem_univ (a, a'))))) (hAu a')

end Dual

section Generation

variable {H : Matrix ι ι E} {b}

/- English proof (translation)
Use `set W0 : Set (FinAdele K) := {t | ∀ a : ι × κ, t • (unitaryMat g⁻¹ *ᵥ stdVec (FinAdele K) b a) ∈ stdLattice ι (FinAdele K) b (intAdeles K)}`. Establish `hW0 : W0 ∈ 𝓝 (0 : FinAdele K)`. Establish `hopen : IsOpen W0`. Establish `: W0 = ⋂ a : ι × κ, (fun t : FinAdele K => t • (unitaryMat g⁻¹ *ᵥ stdVec (FinAdele K) b a)) ⁻¹' stdLattice ι (FinAdele K) b (intAdeles K)`. Use extensionality with `t`.

Simplify using `[W0]`. Rewrite using `[this]`. Conclude with `isOpen_iInter_of_finite fun a => (isOpen_stdLattice (FinAdele K) b (isOpen_integralFiniteAdeles (R := 𝓞 K) (K := K))).preimage (continuous_id.smul continuous_const)`. Use `hopen.mem_nhds fun a => ?_` and prove the remaining obligations. Rewrite using `[zero_smul, mem_stdLattice_iff]`.

Introduce `c`. Rewrite using `[vecCoords_zero]`. Conclude with `zero_mem _`. Take `⟨d, hd0, hd⟩` from `exists_forall_mul_mem_of_mem_nhds hW0`. Use `set r : ℕ := Ideal.absNorm (Ideal.span {d})`.

Establish `hr0 : r ≠ 0`. Rewrite using `[Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]`. Conclude with `hd0`. Take `⟨e, he⟩` from `Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {d}))`. Use `⟨r, by exact_mod_cast hr0, fun x hx => ?_⟩` and prove the remaining obligations.

Rewrite using `[mem_adelicLattice, toFinAdele_smul, mulVec_smul]`. Establish `hx' : toFinAdele K E ι x = ∑ a, algebraMap K (FinAdele K) (vecCoords K b x a) • stdVec (FinAdele K) b a` using `by conv_lhs => rw [← sum_coords_smul_stdVec b (toFinAdele K E ι x)]`. Simplify using `only [vecCoords_toFinAdele]`. Rewrite using `[hx', mulVec_sum, Finset.smul_sum]`. Use `stdLattice_sum b fun a _ => ?_` and prove the remaining obligations.

Rewrite using `[mulVec_smul, smul_smul]`. Establish `hre : ((r : ℤ) : K) = algebraMap (𝓞 K) K e * algebraMap (𝓞 K) K d`. Rewrite using `[← map_mul, he, map_natCast, Int.cast_natCast]`. Establish `: algebraMap K (FinAdele K) ((r : ℤ) : K) * algebraMap K (FinAdele K) (vecCoords K b x a) = algebraMap K (FinAdele K) (algebraMap (𝓞 K) K d) * algebraMap K (FinAdele K) (algebraMap (𝓞 K) K e * vecCoords K b x a)`. Rewrite using `[hre]`.

Simplify using `only [← map_mul]`. Use `congr 1`. Rewrite using `[map_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`.

Conclude with `hd _ (algebraMap_mem_of_isIntegral ((RingOfIntegers.isIntegral_coe e).mul (hx a))) a`.
-/
theorem exists_int_smul_mem_adelicLattice [DecidableEq κ] (g : unitaryPoints K E H (FinAdele K)) :
    ∃ r : ℤ, r ≠ 0 ∧ ∀ x : ι → K ⊗[K] E, (∀ a, IsIntegral ℤ (vecCoords K b x a)) →
      (r : K) • x ∈ adelicLattice b H g := by
  classical
  set W0 : Set (FinAdele K) := {t | ∀ a : ι × κ, t • (unitaryMat g⁻¹ *ᵥ stdVec (FinAdele K) b a) ∈
    stdLattice ι (FinAdele K) b (intAdeles K)}
  have hW0 : W0 ∈ 𝓝 (0 : FinAdele K) := by
    have hopen : IsOpen W0 := by
      have : W0 = ⋂ a : ι × κ, (fun t : FinAdele K => t • (unitaryMat g⁻¹ *ᵥ
          stdVec (FinAdele K) b a)) ⁻¹' stdLattice ι (FinAdele K) b (intAdeles K) := by
        ext t
        simp [W0]
      rw [this]
      exact isOpen_iInter_of_finite fun a =>
        (isOpen_stdLattice (FinAdele K) b (isOpen_integralFiniteAdeles (R := 𝓞 K) (K := K))).preimage
          (continuous_id.smul continuous_const)
    refine hopen.mem_nhds fun a => ?_
    rw [zero_smul, mem_stdLattice_iff]
    intro c
    rw [vecCoords_zero]
    exact zero_mem _
  obtain ⟨d, hd0, hd⟩ := exists_forall_mul_mem_of_mem_nhds hW0
  set r : ℕ := Ideal.absNorm (Ideal.span {d})
  have hr0 : r ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact hd0
  obtain ⟨e, he⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {d}))
  refine ⟨r, by exact_mod_cast hr0, fun x hx => ?_⟩
  rw [mem_adelicLattice, toFinAdele_smul, mulVec_smul]
  have hx' : toFinAdele K E ι x =
      ∑ a, algebraMap K (FinAdele K) (vecCoords K b x a) • stdVec (FinAdele K) b a := by
    conv_lhs => rw [← sum_coords_smul_stdVec b (toFinAdele K E ι x)]
    simp only [vecCoords_toFinAdele]
  rw [hx', mulVec_sum, Finset.smul_sum]
  refine stdLattice_sum b fun a _ => ?_
  rw [mulVec_smul, smul_smul]
  have hre : ((r : ℤ) : K) = algebraMap (𝓞 K) K e * algebraMap (𝓞 K) K d := by
    rw [← map_mul, he, map_natCast, Int.cast_natCast]
  have : algebraMap K (FinAdele K) ((r : ℤ) : K) * algebraMap K (FinAdele K) (vecCoords K b x a) =
      algebraMap K (FinAdele K) (algebraMap (𝓞 K) K d) *
        algebraMap K (FinAdele K) (algebraMap (𝓞 K) K e * vecCoords K b x a) := by
    rw [hre]
    simp only [← map_mul]
    congr 1
    rw [map_mul]
    ring
  rw [this]
  exact hd _ (algebraMap_mem_of_isIntegral ((RingOfIntegers.isIntegral_coe e).mul (hx a))) a

variable (H b) in

/- English proof (translation)
Take `⟨D, hD0, hD⟩` from `exists_int_mul_isIntegral (Finset.univ.image fun p : κ × κ × κ => b.repr β p.1 * b.repr (b p.1 * b p.2.1) p.2.2)`. Use `⟨D, hD0, fun g x hx => ?_⟩` and prove the remaining obligations. Rewrite using `[mem_adelicLattice, toFinAdele_smul, toFinAdele_mul_smul, mulVec_smul, mulVec_smul, mem_stdLattice_iff]`. Introduce `a`. Rewrite using `[vecCoords_smul]`.

Establish `hx'` using `(mem_stdLattice_iff b _ _).1 hx`. Use `set u := unitaryMat g⁻¹ *ᵥ toFinAdele K E ι x`. Establish `hz : tensorMap E (Algebra.ofId K (FinAdele K)) (Algebra.TensorProduct.includeRight β) = (1 : FinAdele K) ⊗ₜ[K] β`. Rewrite using `[tensorMap_includeRight, Algebra.TensorProduct.includeRight_apply]`. Establish `hcoord : vecCoords (FinAdele K) b (((1 : FinAdele K) ⊗ₜ[K] β : FinAdele K ⊗[K] E) • u) a = ∑ k, ∑ l, algebraMap K (FinAdele K) (b.repr β k) * vecCoords (FinAdele K) b u (a.1, l) * algebraMap K (FinAdele K) (b.repr (b k * b l) a.2)`.

Simplify using `only [vecCoords, Pi.smul_apply, smul_eq_mul]`. Rewrite using `[repr_mul]`. Simplify using `only [repr_one_tmul]`. Rewrite using `[hz, hcoord, Finset.mul_sum]`. Use `Subring.sum_mem _ fun k _ => ?_` and prove the remaining obligations.

Rewrite using `[Finset.mul_sum]`. Use `Subring.sum_mem _ fun l _ => ?_` and prove the remaining obligations. Establish `h1` using `algebraMap_mem_of_isIntegral (hD _ (Finset.mem_image_of_mem _ (Finset.mem_univ (k, l, a.2))))`. Establish `: algebraMap K (FinAdele K) (D : K) * (algebraMap K (FinAdele K) (b.repr β k) * vecCoords (FinAdele K) b u (a.1, l) * algebraMap K (FinAdele K) (b.repr (b k * b l) a.2)) = algebraMap K (FinAdele K) ((D : K) * (b.repr β k * b.repr (b k * b l) a.2)) * vecCoords (FinAdele K) b u (a. …`. Simplify using `only [map_mul]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Conclude with `mul_mem h1 (hx' (a.1, l))`.
-/
theorem exists_int_smul_includeRight_mem (β : E) : ∃ D : ℤ, D ≠ 0 ∧
    ∀ (g : unitaryPoints K E H (FinAdele K)) (x : ι → K ⊗[K] E), x ∈ adelicLattice b H g →
      (D : K) • ((Algebra.TensorProduct.includeRight (R := K) (A := K) β : K ⊗[K] E) • x) ∈ adelicLattice b H g := by
  classical
  obtain ⟨D, hD0, hD⟩ := exists_int_mul_isIntegral
    (Finset.univ.image fun p : κ × κ × κ => b.repr β p.1 * b.repr (b p.1 * b p.2.1) p.2.2)
  refine ⟨D, hD0, fun g x hx => ?_⟩
  rw [mem_adelicLattice, toFinAdele_smul, toFinAdele_mul_smul, mulVec_smul, mulVec_smul,
    mem_stdLattice_iff]
  intro a
  rw [vecCoords_smul]
  have hx' := (mem_stdLattice_iff b _ _).1 hx
  set u := unitaryMat g⁻¹ *ᵥ toFinAdele K E ι x
  have hz : tensorMap E (Algebra.ofId K (FinAdele K)) (Algebra.TensorProduct.includeRight β) =
      (1 : FinAdele K) ⊗ₜ[K] β := by
    rw [tensorMap_includeRight, Algebra.TensorProduct.includeRight_apply]
  have hcoord : vecCoords (FinAdele K) b (((1 : FinAdele K) ⊗ₜ[K] β : FinAdele K ⊗[K] E) • u) a =
      ∑ k, ∑ l, algebraMap K (FinAdele K) (b.repr β k) * vecCoords (FinAdele K) b u (a.1, l) *
        algebraMap K (FinAdele K) (b.repr (b k * b l) a.2) := by
    simp only [vecCoords, Pi.smul_apply, smul_eq_mul]
    rw [repr_mul]
    simp only [repr_one_tmul]
  rw [hz, hcoord, Finset.mul_sum]
  refine Subring.sum_mem _ fun k _ => ?_
  rw [Finset.mul_sum]
  refine Subring.sum_mem _ fun l _ => ?_
  have h1 := algebraMap_mem_of_isIntegral (hD _ (Finset.mem_image_of_mem _
    (Finset.mem_univ (k, l, a.2))))
  have : algebraMap K (FinAdele K) (D : K) * (algebraMap K (FinAdele K) (b.repr β k) *
      vecCoords (FinAdele K) b u (a.1, l) * algebraMap K (FinAdele K) (b.repr (b k * b l) a.2)) =
      algebraMap K (FinAdele K) ((D : K) * (b.repr β k * b.repr (b k * b l) a.2)) *
        vecCoords (FinAdele K) b u (a.1, l) := by
    simp only [map_mul]
    ring
  rw [this]
  exact mul_mem h1 (hx' (a.1, l))

end Generation

end GroundTheory.Automorphic
