import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.Statements
import GroundTheory.GlobalFields.ComplexMultiplication.AlgebraicityGalois
import GroundTheory.GlobalFields.ComplexMultiplication.AlgebraicityDescent
import GroundTheory.GlobalFields.ComplexMultiplication.JInvariantSurjective
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ChowlaSelberg

open NumberField GroundTheory.Global GroundTheory.Global.Elliptic GroundTheory.Arith.Abelian Module IntermediateField
open scoped nonZeroDivisors Real UpperHalfPlane

noncomputable section

/- English proof (translation)
Take `⟨L, C, hC⟩` from `exists_variableChange_eq_weierstrassCurve W`. Conclude with `⟨_, L, C⁻¹, inv_smul_eq_of_smul_eq C hC, rfl⟩`.
-/
theorem exists_isPeriodLattice (W : WeierstrassCurve ℂ) [W.IsElliptic] :
    ∃ Λ, IsPeriodLattice W Λ := by
  obtain ⟨L, C, hC⟩ := exists_variableChange_eq_weierstrassCurve W
  exact ⟨_, L, C⁻¹, inv_smul_eq_of_smul_eq C hC, rfl⟩

section Model

variable {K : Type} [Field K] [NumberField K] [Algebra K ℂ] [IsTotallyComplex K]

def unitCMCurve (hK : finrank ℚ K = 2) : CMCurve K :=
  CMCurve.ofLattice (algebraMap K ℂ) (idealPeriodPair (algebraMap K ℂ) hK 1)
    (latticeEnd_idealPeriodPair (algebraMap K ℂ) hK 1)

/- English proof (translation)
Take `⟨ι, hι, -⟩` from `existsUnique_normalized (algebraMap K ℂ) hK E`. Use `set f : isogEnd W := vcEndEquiv C⁻¹ (inv_smul_eq_of_smul_eq C hC) (ι a) with hfdef`. Establish `hf : endConst W f = algebraMap K ℂ (a : K)`. Rewrite using `[hfdef, endConst_vcEndEquiv, hι]`. Establish `hf0 : f ≠ 0`.

Rewrite using `[hfdef]`. Conclude with `(map_ne_zero_iff _ (RingEquiv.injective _)).2 ((map_ne_zero_iff _ ι.injective).2 ha)`. Establish `hiso : IsIsogeny W W f.1` using `(mem_isogHom_iff.mp f.2).resolve_left fun h ↦ hf0 (Subtype.ext h)`. Use `⟨⟨f.1, hiso⟩, ?_⟩` and prove the remaining obligations. Establish `h1` using `homConst_toHom (⟨f.1, hiso⟩ : Isogeny W W)`.

Establish `h2 : Isogeny.toHom (⟨f.1, hiso⟩ : Isogeny W W) = f` using `Subtype.ext rfl`. Rewrite `h1` using `[h2]`. Conclude with `h1.symm.trans hf`.
-/
theorem exists_isogeny_invConst (hK : finrank ℚ K = 2) (E : CMCurve K) {W : WeierstrassCurve ℂ}
    [W.IsElliptic] (C : WeierstrassCurve.VariableChange ℂ) (hC : C • W = E.curve) (a : 𝓞 K)
    (ha : a ≠ 0) : ∃ ψ : Isogeny W W, invConst ψ = algebraMap K ℂ (a : K) := by
  obtain ⟨ι, hι, -⟩ := existsUnique_normalized (algebraMap K ℂ) hK E
  set f : isogEnd W := vcEndEquiv C⁻¹ (inv_smul_eq_of_smul_eq C hC) (ι a) with hfdef
  have hf : endConst W f = algebraMap K ℂ (a : K) := by
    rw [hfdef, endConst_vcEndEquiv, hι]
  have hf0 : f ≠ 0 := by
    rw [hfdef]
    exact (map_ne_zero_iff _ (RingEquiv.injective _)).2
      ((map_ne_zero_iff _ ι.injective).2 ha)
  have hiso : IsIsogeny W W f.1 :=
    (mem_isogHom_iff.mp f.2).resolve_left fun h ↦ hf0 (Subtype.ext h)
  refine ⟨⟨f.1, hiso⟩, ?_⟩
  have h1 := homConst_toHom (⟨f.1, hiso⟩ : Isogeny W W)
  have h2 : Isogeny.toHom (⟨f.1, hiso⟩ : Isogeny W W) = f := Subtype.ext rfl
  rw [h2] at h1
  exact h1.symm.trans hf

/- English proof (translation)
Use `set E := unitCMCurve hK`. Take `⟨W, hW, C, hC, hdesc⟩` from `E.exists_model_endomorphisms_defined hK`. Use `⟨K⟮E.curve.j⟯, W, hW, ?_, fun a ha ↦ ?_⟩` and prove the remaining obligations. Conclude with `IntermediateField.adjoin.finiteDimensional (ELL.isAlgebraic_j_over hK E.toEll).isIntegral`. Take `⟨ψ, hψ⟩` from `exists_isogeny_invConst hK E C hC a ha`.

Take `⟨φ, hφ⟩` from `hdesc ψ`. Use `⟨φ, (algebraMap K⟮E.curve.j⟯ ℂ).injective ?_⟩` and prove the remaining obligations. Rewrite using `[← invConst_map, hφ]`. Conclude with `hψ.trans (IsScalarTower.algebraMap_apply K K⟮E.curve.j⟯ ℂ _)`.
-/
theorem exists_model (hK : finrank ℚ K = 2) :
    ∃ (L : IntermediateField K ℂ) (W : WeierstrassCurve L) (_ : W.IsElliptic),
      FiniteDimensional K L ∧
        ∀ a : 𝓞 K, a ≠ 0 → ∃ φ : Isogeny W W, invConst φ = algebraMap K L (a : K) := by
  set E := unitCMCurve hK
  obtain ⟨W, hW, C, hC, hdesc⟩ := E.exists_model_endomorphisms_defined hK
  refine ⟨K⟮E.curve.j⟯, W, hW, ?_, fun a ha ↦ ?_⟩
  · exact IntermediateField.adjoin.finiteDimensional
      (ELL.isAlgebraic_j_over hK E.toEll).isIntegral
  · obtain ⟨ψ, hψ⟩ := exists_isogeny_invConst hK E C hC a ha
    obtain ⟨φ, hφ⟩ := hdesc ψ
    refine ⟨φ, (algebraMap K⟮E.curve.j⟯ ℂ).injective ?_⟩
    rw [← invConst_map, hφ]
    exact hψ.trans (IsScalarTower.algebraMap_apply K K⟮E.curve.j⟯ ℂ _)

omit [IsTotallyComplex K] in

/- English proof (translation)
The claim follows from `Module.Finite.trans K L`.
-/
theorem numberField_of_finiteDimensional (L : IntermediateField K ℂ) [FiniteDimensional K L] :
    NumberField L where
  to_finiteDimensional := Module.Finite.trans K L

def CMFamily.ofModel (hK : finrank ℚ K = 2) : CMFamily K :=
  haveI : FiniteDimensional K (exists_model hK).choose :=
    (exists_model hK).choose_spec.choose_spec.choose_spec.1
  haveI := numberField_of_finiteDimensional (exists_model hK).choose
  haveI : (exists_model hK).choose_spec.choose.IsElliptic :=
    (exists_model hK).choose_spec.choose_spec.choose
  { k := (exists_model hK).choose
    E := (exists_model hK).choose_spec.choose
    normalised := (exists_model hK).choose_spec.choose_spec.choose_spec.2
    periodLattice := fun s ↦
      (exists_isPeriodLattice ((exists_model hK).choose_spec.choose.map s)).choose
    isPeriodLattice := fun s ↦
      (exists_isPeriodLattice ((exists_model hK).choose_spec.choose.map s)).choose_spec }

end Model

abbrev cyclo3 : Type := CyclotomicField 3 ℚ

instance : NeZero ((3 : ℕ) : ℚ) := ⟨by norm_num⟩

instance : IsCyclotomicExtension {3} ℚ cyclo3 := CyclotomicField.isCyclotomicExtension 3 ℚ

instance : NumberField cyclo3 := IsCyclotomicExtension.numberField {3} ℚ _

/- English proof (translation)
Rewrite using `[IsCyclotomicExtension.finrank (n := 3) cyclo3 (Polynomial.cyclotomic.irreducible_rat (by norm_num))]`. Evaluate the decidable proposition.
-/
theorem finrank_cyclo3 : finrank ℚ cyclo3 = 2 := by
  rw [IsCyclotomicExtension.finrank (n := 3) cyclo3
    (Polynomial.cyclotomic.irreducible_rat (by norm_num))]
  decide

instance : Algebra.IsQuadraticExtension ℚ cyclo3 := ⟨finrank_cyclo3⟩

instance : IsTotallyComplex cyclo3 :=
  IsCyclotomicExtension.Rat.isTotallyComplex (n := 3) cyclo3 (by norm_num)

def primeDiscriminantCyclo3 : PrimeDiscriminant cyclo3 where
  d := 3
  prime := Nat.prime_three
  mod_four := rfl
  discr_eq := by
    rw [IsCyclotomicExtension.Rat.discr_prime 3 cyclo3]
    norm_num

def cyclo3Embedding : cyclo3 →+* ℂ := (IsAlgClosed.lift : cyclo3 →ₐ[ℚ] ℂ).toRingHom

def cmFamilyCyclo3 : CMFamily cyclo3 :=
  letI : Algebra cyclo3 ℂ := cyclo3Embedding.toAlgebra
  CMFamily.ofModel finrank_cyclo3

/- English proof (translation)
Assemble the required witnesses or components as `⟨latticeOfTau UpperHalfPlane.I, 2, two_ne_zero⟩`.
-/
theorem PhScale.witness : ∃ (_ : PeriodPair) (c : ℂ), c ≠ 0 :=
  ⟨latticeOfTau UpperHalfPlane.I, 2, two_ne_zero⟩

def twoI : ℍ := ⟨2 * Complex.I, by simp⟩

/- English proof (translation)
Rewrite using `[PeriodPair.mem_lattice]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, b, h⟩`. Establish `him` using `congrArg Complex.im h`. Simplify using `[twoI] at him`.

Conclude with `⟨a, by exact_mod_cast (by linarith : (m : ℝ) = a + a)⟩`. Introduce and unpack `⟨k, rfl⟩`. Conclude with `⟨k, n, by simp [twoI]; ring⟩`.
-/
theorem mem_lattice_twoI (m n : ℤ) :
    ((m : ℂ) * Complex.I + n) ∈ (latticeOfTau twoI).lattice ↔ Even m := by
  rw [PeriodPair.mem_lattice]
  constructor
  · rintro ⟨a, b, h⟩
    have him := congrArg Complex.im h
    simp [twoI] at him
    exact ⟨a, by exact_mod_cast (by linarith : (m : ℝ) = a + a)⟩
  · rintro ⟨k, rfl⟩
    exact ⟨k, n, by simp [twoI]; ring⟩

/- English proof (translation)
Rewrite using `[PeriodPair.mem_lattice]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨m, n, rfl⟩`. Conclude with `⟨m, n, by simp⟩`. Introduce and unpack `⟨m, n, rfl⟩`.

Conclude with `⟨m, n, by simp⟩`.
-/
theorem mem_lattice_I {z : ℂ} :
    z ∈ (latticeOfTau UpperHalfPlane.I).lattice ↔ ∃ m n : ℤ, z = (m : ℂ) * Complex.I + n := by
  rw [PeriodPair.mem_lattice]
  constructor
  · rintro ⟨m, n, rfl⟩
    exact ⟨m, n, by simp⟩
  · rintro ⟨m, n, rfl⟩
    exact ⟨m, n, by simp⟩

/- English proof (translation)
Establish `hle : (latticeOfTau twoI).lattice ≤ (latticeOfTau UpperHalfPlane.I).lattice`. Introduce `z hz`. Take `⟨a, b, rfl⟩` from `PeriodPair.mem_lattice.1 hz`. Conclude with `mem_lattice_I.2 ⟨2 * a, b, by simp [twoI]; ring⟩`. Use `⟨latticeOfTau twoI, latticeOfTau UpperHalfPlane.I, 2, Nat.prime_two, hle, ?_⟩` and prove the remaining obligations.

Rewrite using `[AddSubgroup.relIndex_eq_two_iff]`. Use `⟨Complex.I, mem_lattice_I.2 ⟨1, 0, by simp⟩, fun b hb ↦ ?_⟩` and prove the remaining obligations. Take `⟨m, n, rfl⟩` from `mem_lattice_I.1 hb`. Establish `e : (m : ℂ) * Complex.I + n + Complex.I = ((m + 1 : ℤ) : ℂ) * Complex.I + n` using `by push_cast; ring`. Simplify using `only [Submodule.mem_toAddSubgroup]`.

Rewrite using `[e, mem_lattice_twoI, mem_lattice_twoI, Int.even_add_one]`. The claim follows by propositional logic.
-/
theorem DeltaRatioIntegral.witness :
    ∃ (L L' : PeriodPair) (p : ℕ), p.Prime ∧ L.lattice ≤ L'.lattice ∧
      L.lattice.toAddSubgroup.relIndex L'.lattice.toAddSubgroup = p := by
  have hle : (latticeOfTau twoI).lattice ≤ (latticeOfTau UpperHalfPlane.I).lattice := by
    intro z hz
    obtain ⟨a, b, rfl⟩ := PeriodPair.mem_lattice.1 hz
    exact mem_lattice_I.2 ⟨2 * a, b, by simp [twoI]; ring⟩
  refine ⟨latticeOfTau twoI, latticeOfTau UpperHalfPlane.I, 2, Nat.prime_two, hle, ?_⟩
  rw [AddSubgroup.relIndex_eq_two_iff]
  refine ⟨Complex.I, mem_lattice_I.2 ⟨1, 0, by simp⟩, fun b hb ↦ ?_⟩
  obtain ⟨m, n, rfl⟩ := mem_lattice_I.1 hb
  have e : (m : ℂ) * Complex.I + n + Complex.I = ((m + 1 : ℤ) : ℂ) * Complex.I + n := by
    push_cast; ring
  simp only [Submodule.mem_toAddSubgroup]
  rw [e, mem_lattice_twoI, mem_lattice_twoI, Int.even_add_one]
  tauto

def cmLatticeCyclo3 : PeriodPair := idealPeriodPair cyclo3Embedding finrank_cyclo3 1

/- English proof (translation)
The claim follows from `latticeEnd_idealPeriodPair cyclo3Embedding finrank_cyclo3 1`.
-/
theorem latticeEnd_cmLatticeCyclo3 : latticeEnd cmLatticeCyclo3 = cmRing cyclo3Embedding :=
  latticeEnd_idealPeriodPair cyclo3Embedding finrank_cyclo3 1

/- English proof (translation)
Simplify using `[IsCyclotomicExtension.zeta_spec 3 ℚ cyclo3]`.
-/
theorem zeta_three_isPrimitiveRoot : IsPrimitiveRoot (IsCyclotomicExtension.zeta 3 ℚ cyclo3) (3 ^ (0 + 1)) := by
  simp [IsCyclotomicExtension.zeta_spec 3 ℚ cyclo3]

instance : IsCyclotomicExtension {3 ^ (0 + 1)} ℚ cyclo3 := by
  simpa using (inferInstance : IsCyclotomicExtension {3} ℚ cyclo3)

def primeCyclo3 : Ideal (𝓞 cyclo3) := Ideal.span {zeta_three_isPrimitiveRoot.toInteger - 1}

/- English proof (translation)
The claim follows from `IsCyclotomicExtension.Rat.absNorm_span_zeta_sub_one (p := 3) (k := 0) zeta_three_isPrimitiveRoot`.
-/
theorem absNorm_primeCyclo3 : Ideal.absNorm primeCyclo3 = 3 :=
  IsCyclotomicExtension.Rat.absNorm_span_zeta_sub_one (p := 3) (k := 0) zeta_three_isPrimitiveRoot

/- English proof (translation)
The claim follows from `mem_nonZeroDivisors_of_ne_zero fun h ↦ by have := absNorm_primeCyclo3 rw [h, Submodule.zero_eq_bot, Ideal.absNorm_bot] at this exact absurd this (by norm_num)`.
-/
theorem primeCyclo3_mem : primeCyclo3 ∈ (Ideal (𝓞 cyclo3))⁰ :=
  mem_nonZeroDivisors_of_ne_zero fun h ↦ by
    have := absNorm_primeCyclo3
    rw [h, Submodule.zero_eq_bot, Ideal.absNorm_bot] at this
    exact absurd this (by norm_num)

/- English proof (translation)
Assemble the required witnesses or components as `⟨cyclo3Embedding, cmLatticeCyclo3, ⟨primeCyclo3, primeCyclo3_mem⟩, latticeEnd_cmLatticeCyclo3, Ideal.isPrime_of_irreducible_absNorm (by rw [absNorm_primeCyclo3]; exact Nat.prime_three), by rw [absNorm_primeCyclo3]; exact Nat.prime_three⟩`.
-/
theorem WUnitOffPrime.witness :
    ∃ (σ : cyclo3 →+* ℂ) (L : PeriodPair) (𝔭 : (Ideal (𝓞 cyclo3))⁰),
      latticeEnd L = cmRing σ ∧ (𝔭 : Ideal (𝓞 cyclo3)).IsPrime ∧
        (Ideal.absNorm (𝔭 : Ideal (𝓞 cyclo3))).Prime :=
  ⟨cyclo3Embedding, cmLatticeCyclo3, ⟨primeCyclo3, primeCyclo3_mem⟩, latticeEnd_cmLatticeCyclo3,
    Ideal.isPrime_of_irreducible_absNorm (by rw [absNorm_primeCyclo3]; exact Nat.prime_three),
    by rw [absNorm_primeCyclo3]; exact Nat.prime_three⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨primeDiscriminantCyclo3, cyclo3Embedding, cmLatticeCyclo3, ⟨primeCyclo3, primeCyclo3_mem⟩, latticeEnd_cmLatticeCyclo3⟩`.
-/
theorem WIdeal.witness :
    ∃ (_ : PrimeDiscriminant cyclo3) (σ : cyclo3 →+* ℂ) (L : PeriodPair) (_ : (Ideal (𝓞 cyclo3))⁰),
      latticeEnd L = cmRing σ :=
  ⟨primeDiscriminantCyclo3, cyclo3Embedding, cmLatticeCyclo3, ⟨primeCyclo3, primeCyclo3_mem⟩,
    latticeEnd_cmLatticeCyclo3⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨primeDiscriminantCyclo3, cyclo3Embedding, _, 1, 2, rfl, one_lt_two⟩`.
-/
theorem ClassEpstein.witness :
    ∃ (_ : PrimeDiscriminant cyclo3) (_ : cyclo3 →+* ℂ) (C : ClassGroup (𝓞 cyclo3))
      (𝔟 : (FractionalIdeal (𝓞 cyclo3)⁰ cyclo3)ˣ) (s : ℝ), ClassGroup.mk cyclo3 𝔟 = C ∧ 1 < s :=
  ⟨primeDiscriminantCyclo3, cyclo3Embedding, _, 1, 2, rfl, one_lt_two⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨(primeDiscriminantCyclo3, cmFamilyCyclo3)⟩`.
-/
theorem MeanOverEmbeddings.witness : Nonempty (PrimeDiscriminant cyclo3 × CMFamily cyclo3) :=
  ⟨(primeDiscriminantCyclo3, cmFamilyCyclo3)⟩

end

end GroundTheory.Heights₂.Heights.ChowlaSelberg
