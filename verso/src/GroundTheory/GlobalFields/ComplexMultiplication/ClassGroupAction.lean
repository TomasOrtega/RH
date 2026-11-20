import Mathlib
import GroundTheory.GlobalFields.ComplexMultiplication.ClassGroupActionLattice
import GroundTheory.GlobalFields.ComplexMultiplication.JInvariantHomothety

open NumberField Module WeierstrassCurve GroundTheory.Arith.Abelian
open scoped nonZeroDivisors

noncomputable section

namespace GroundTheory.Global
namespace Elliptic

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result. Fix the arbitrary inputs or assume the hypotheses.

A detailed English derivation is pending.
-/
theorem exists_variableChange_iff_homothetic (L L' : PeriodPair) :
    (∃ C : VariableChange ℂ, C • weierstrassCurve L = weierstrassCurve L') ↔
      ∃ c : ℂ, c ≠ 0 ∧ (L'.lattice : Set ℂ) = (c * ·) '' L.lattice := by
  rw [← weierstrassCurve_j_eq_iff]
  constructor
  · rintro ⟨C, hC⟩
    obtain ⟨h₂, h₃⟩ := g₂_g₃_of_variableChange hC
    exact weierstrassCurve_j_eq_of_g₂_g₃ (C.u⁻¹).ne_zero h₂ h₃
  · intro h
    exact exists_variableChange_of_j_eq _ _ h

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. By extensionality, compare the relevant components. Prove the components needed by the constructor for the conclusion.

Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Use the resulting assumption. Fix the arbitrary inputs or assume the hypotheses.

Extract witnesses or component facts from the available result. A detailed English derivation is pending.
-/
theorem latticeEnd_eq_of_homothetic {L L' : PeriodPair} {c : ℂ} (hc : c ≠ 0)
    (h : (L'.lattice : Set ℂ) = (c * ·) '' L.lattice) : latticeEnd L' = latticeEnd L := by
  have hmem : ∀ z, z ∈ L'.lattice ↔ ∃ l ∈ L.lattice, c * l = z := fun z ↦ by
    rw [← SetLike.mem_coe, h]; rfl
  ext α
  show (∀ l ∈ L'.lattice, α * l ∈ L'.lattice) ↔ (∀ l ∈ L.lattice, α * l ∈ L.lattice)
  constructor
  · intro hα l hl
    obtain ⟨l', hl', e⟩ := (hmem _).1 (hα (c * l) ((hmem _).2 ⟨l, hl, rfl⟩))
    have : l' = α * l := mul_left_cancel₀ hc (by rw [e]; ring)
    rwa [← this]
  · intro hα l hl
    obtain ⟨l', hl', rfl⟩ := (hmem l).1 hl
    exact (hmem _).2 ⟨α * l', hα l' hl', by ring⟩

variable {K : Type*} [Field K] [NumberField K] (σ : K →+* ℂ)

/- English proof (translation)
Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Establish an intermediate fact.

Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Rewrite the hypotheses and the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem idealLattice_mul_homothetic (I J : FractionalIdeal (𝓞 K)⁰ K) {c : ℂ} {Λ : Submodule ℤ ℂ}
    (h : (Λ : Set ℂ) = (c * ·) '' idealLattice σ I) :
    ((idealLattice σ J * Λ : Submodule ℤ ℂ) : Set ℂ) = (c * ·) '' idealLattice σ (J * I) := by
  have hΛ : Λ = (idealLattice σ I).map (LinearMap.mulLeft ℤ c) := by
    apply SetLike.coe_injective
    rw [h, Submodule.map_coe]
    rfl
  have key : idealLattice σ J * (idealLattice σ I).map (LinearMap.mulLeft ℤ c) =
      (idealLattice σ J * idealLattice σ I).map (LinearMap.mulLeft ℤ c) := by
    apply le_antisymm
    · rw [Submodule.mul_le]
      intro m hm x hx
      obtain ⟨n, hn, rfl⟩ := Submodule.mem_map.1 hx
      refine Submodule.mem_map.2 ⟨m * n, Submodule.mul_mem_mul hm hn, ?_⟩
      simp only [LinearMap.mulLeft_apply]
      ring
    · rw [Submodule.map_le_iff_le_comap, Submodule.mul_le]
      intro m hm n hn
      rw [Submodule.mem_comap, LinearMap.mulLeft_apply, show c * (m * n) = m * (c * n) by ring]
      exact Submodule.mul_mem_mul hm (Submodule.mem_map.2 ⟨n, hn, rfl⟩)
  rw [hΛ, key, idealLattice_mul, Submodule.map_coe]
  rfl

variable (K)

structure CMCurve where

  curve : WeierstrassCurve ℂ
  [isElliptic : curve.IsElliptic]

  endIso : Nonempty (isogEnd curve ≃+* 𝓞 K)

attribute [instance] CMCurve.isElliptic

def CMCurve.setoid : Setoid (CMCurve K) where
  r E E' := ∃ C : VariableChange ℂ, C • E.curve = E'.curve
  iseqv :=
    { refl := fun E ↦ ⟨1, one_smul _ _⟩
      symm := fun ⟨C, h⟩ ↦ ⟨C⁻¹, inv_smul_eq_of_smul_eq C h⟩
      trans := fun ⟨C, h⟩ ⟨C', h'⟩ ↦ ⟨C' * C, by rw [mul_smul, h, h']⟩ }

def ELL : Type _ := Quotient (CMCurve.setoid K)

variable {K}

def CMCurve.toEll (E : CMCurve K) : ELL K := Quotient.mk (CMCurve.setoid K) E

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem CMCurve.toEll_eq_iff (E E' : CMCurve K) :
    E.toEll = E'.toEll ↔ ∃ C : VariableChange ℂ, C • E.curve = E'.curve :=
  Quotient.eq (r := CMCurve.setoid K)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ELL.exists_eq (x : ELL K) : ∃ E : CMCurve K, E.toEll = x :=
  Quotient.exists_rep x

def CMCurve.ofLattice (L : PeriodPair) (hL : latticeEnd L = cmRing σ) : CMCurve K where
  curve := weierstrassCurve L
  endIso := ⟨(latticeEndEquiv L).symm.trans ((RingEquiv.subringCongr hL).trans (cmRingEquiv σ).symm)⟩

def ellOf (L : PeriodPair) (hL : latticeEnd L = cmRing σ) : ELL K := (CMCurve.ofLattice σ L hL).toEll

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem ellOf_eq_ellOf_iff {L L' : PeriodPair} (hL : latticeEnd L = cmRing σ)
    (hL' : latticeEnd L' = cmRing σ) :
    ellOf σ L hL = ellOf σ L' hL' ↔ ∃ c : ℂ, c ≠ 0 ∧ (L'.lattice : Set ℂ) = (c * ·) '' L.lattice := by
  rw [ellOf, ellOf, CMCurve.toEll_eq_iff]
  exact exists_variableChange_iff_homothetic L L'

section Quadratic

variable (hK : finrank ℚ K = 2) [IsTotallyComplex K]
include hK

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem exists_idealLattice_of_ringEquiv (L : PeriodPair) (e : latticeEnd L ≃+* 𝓞 K) :
    ∃ (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (c : ℂ), c ≠ 0 ∧
      (L.lattice : Set ℂ) = (c * ·) '' idealLattice σ I :=
  exists_idealLattice_of_latticeEnd_eq σ hK L (latticeEnd_eq_cmRing_of_ringEquiv σ hK L e)

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Supply the required witnesses or components.
-/
theorem CMCurve.exists_lattice (E : CMCurve K) :
    ∃ (L : PeriodPair) (C : VariableChange ℂ) (hL : latticeEnd L = cmRing σ),
      C • E.curve = weierstrassCurve L ∧ (CMCurve.ofLattice σ L hL).toEll = E.toEll := by
  obtain ⟨L, C, hC⟩ := exists_variableChange_eq_weierstrassCurve E.curve
  have hL : latticeEnd L = cmRing σ := latticeEnd_eq_cmRing_of_ringEquiv σ hK L
    ((latticeEndEquiv L).trans ((vcEndEquiv C hC).symm.trans E.endIso.some))
  refine ⟨L, C, hL, hC, ?_⟩
  rw [CMCurve.toEll_eq_iff]
  exact ⟨C⁻¹, inv_smul_eq_of_smul_eq C hC⟩

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem latticeEnd_ideal (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    latticeEnd (idealPeriodPair σ hK I) = cmRing σ :=
  latticeEnd_idealPeriodPair σ hK I

def ellOfIdeal (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : ELL K :=
  ellOf σ (idealPeriodPair σ hK I⁻¹) (latticeEnd_ideal σ hK I⁻¹)

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem ellOfIdeal_eq_iff (I J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ellOfIdeal σ hK I = ellOfIdeal σ hK J ↔ ClassGroup.mk K I = ClassGroup.mk K J := by
  rw [ellOfIdeal, ellOfIdeal, ellOf_eq_ellOf_iff, lattice_idealPeriodPair, lattice_idealPeriodPair,
    ← classGroup_mk_eq_iff σ hK, map_inv, map_inv, inv_inj]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem ellOf_eq_ellOfIdeal {L : PeriodPair} (hL : latticeEnd L = cmRing σ)
    {I : (FractionalIdeal (𝓞 K)⁰ K)ˣ} {c : ℂ} (hc : c ≠ 0)
    (h : (L.lattice : Set ℂ) = (c * ·) '' idealLattice σ I) :
    ellOf σ L hL = ellOfIdeal σ hK I⁻¹ := by
  rw [ellOfIdeal, ellOf_eq_ellOf_iff, inv_inv, lattice_idealPeriodPair]
  refine ⟨c⁻¹, inv_ne_zero hc, ?_⟩
  rw [h, Set.image_image]
  simp [inv_mul_cancel_left₀ hc]

/- English proof (translation)
Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem ellOfIdeal_surjective (x : ELL K) : ∃ I, ellOfIdeal σ hK I = x := by
  obtain ⟨E, rfl⟩ := ELL.exists_eq x
  obtain ⟨L, C, hL, -, hE⟩ := E.exists_lattice σ hK
  obtain ⟨I, c, hc, h⟩ := exists_idealLattice_of_latticeEnd_eq σ hK L hL
  exact ⟨I⁻¹, by rw [← hE, ← ellOf, ellOf_eq_ellOfIdeal σ hK hL hc h]⟩

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem classGroup_mk_surjective (a : ClassGroup (𝓞 K)) :
    ∃ I : (FractionalIdeal (𝓞 K)⁰ K)ˣ, ClassGroup.mk K I = a :=
  ClassGroup.induction (K := K) (P := fun a ↦ ∃ I, ClassGroup.mk K I = a) (fun I ↦ ⟨I, rfl⟩) a

def classToEll (a : ClassGroup (𝓞 K)) : ELL K :=
  ellOfIdeal σ hK (classGroup_mk_surjective hK a).choose

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem classToEll_mk (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    classToEll σ hK (ClassGroup.mk K I) = ellOfIdeal σ hK I :=
  (ellOfIdeal_eq_iff σ hK _ _).2 (classGroup_mk_surjective hK _).choose_spec

def ellEquiv : ClassGroup (𝓞 K) ≃ ELL K :=
  Equiv.ofBijective (classToEll σ hK)
    ⟨fun a b hab ↦ by
      obtain ⟨I, rfl⟩ := classGroup_mk_surjective hK a
      obtain ⟨J, rfl⟩ := classGroup_mk_surjective hK b
      rwa [classToEll_mk, classToEll_mk, ellOfIdeal_eq_iff] at hab,
    fun x ↦ by
      obtain ⟨I, rfl⟩ := ellOfIdeal_surjective σ hK x
      exact ⟨ClassGroup.mk K I, classToEll_mk σ hK I⟩⟩

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ellEquiv_mk (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ellEquiv σ hK (ClassGroup.mk K I) = ellOfIdeal σ hK I :=
  classToEll_mk σ hK I

def ellMulAction : MulAction (ClassGroup (𝓞 K)) (ELL K) :=
  (ellEquiv σ hK).symm.mulAction (ClassGroup (𝓞 K))

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem ellMulAction_smul (a : ClassGroup (𝓞 K)) (x : ELL K) :
    (ellMulAction σ hK).smul a x = ellEquiv σ hK (a * (ellEquiv σ hK).symm x) :=
  rfl

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Introduce a local definition for the expression. Introduce a local definition for the expression. Establish an intermediate fact.

Rewrite the hypotheses and the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.

Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Supply the required witnesses or components. Assume the hypotheses and unpack their components. Supply the required witnesses or components.

Reduce the conclusion to the remaining proof obligations. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem exists_lattice_mul (L : PeriodPair) (hL : latticeEnd L = cmRing σ)
    (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ∃ L' : PeriodPair, L'.lattice = idealLattice σ ↑𝔞⁻¹ * L.lattice ∧ latticeEnd L' = cmRing σ := by
  obtain ⟨I, c, hc, h⟩ := exists_idealLattice_of_latticeEnd_eq σ hK L hL
  have h' := idealLattice_mul_homothetic σ (I : FractionalIdeal (𝓞 K)⁰ K) (↑𝔞⁻¹) h
  let P := idealPeriodPair σ hK (𝔞⁻¹ * I)
  let L' : PeriodPair :=
    { ω₁ := c * P.ω₁
      ω₂ := c * P.ω₂
      indep := by
        have := P.indep
        rw [LinearIndependent.pair_iff] at this ⊢
        intro s t hst
        apply this s t
        have hst' : c * (s • P.ω₁ + t • P.ω₂) = 0 := by
          rw [← hst]; simp only [Complex.real_smul]; ring
        exact (mul_eq_zero.1 hst').resolve_left hc }
  have hlat : (L'.lattice : Set ℂ) = (c * ·) '' P.lattice := by
    ext z
    simp only [SetLike.mem_coe, PeriodPair.mem_lattice, Set.mem_image, L']
    constructor
    · rintro ⟨m, n, rfl⟩
      exact ⟨m * P.ω₁ + n * P.ω₂, ⟨m, n, rfl⟩, by ring⟩
    · rintro ⟨w, ⟨m, n, rfl⟩, rfl⟩
      exact ⟨m, n, by ring⟩
  refine ⟨L', ?_, ?_⟩
  · apply SetLike.coe_injective
    rw [hlat, h', lattice_idealPeriodPair, Units.val_mul]
  · rw [latticeEnd_eq_of_homothetic hc hlat]
    exact latticeEnd_ideal σ hK _

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem classGroup_smul_ellOf (L L' : PeriodPair) (hL : latticeEnd L = cmRing σ)
    (hL' : latticeEnd L' = cmRing σ) (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (h : L'.lattice = idealLattice σ ↑𝔞⁻¹ * L.lattice) :
    (ellMulAction σ hK).smul (ClassGroup.mk K 𝔞) (ellOf σ L hL) = ellOf σ L' hL' := by
  obtain ⟨I, c, hc, hI⟩ := exists_idealLattice_of_latticeEnd_eq σ hK L hL
  have h' := idealLattice_mul_homothetic σ (I : FractionalIdeal (𝓞 K)⁰ K) (↑𝔞⁻¹) hI
  rw [← h, ← Units.val_mul] at h'
  have e1 : ellOf σ L hL = ellEquiv σ hK (ClassGroup.mk K I⁻¹) := by
    rw [ellEquiv_mk]; exact ellOf_eq_ellOfIdeal σ hK hL hc hI
  have e2 : ellOf σ L' hL' = ellEquiv σ hK (ClassGroup.mk K (𝔞⁻¹ * I)⁻¹) := by
    rw [ellEquiv_mk]; exact ellOf_eq_ellOfIdeal σ hK hL' hc h'
  rw [ellMulAction_smul, e1, e2, Equiv.symm_apply_apply]
  congr 1
  rw [mul_inv_rev, inv_inv, map_mul, mul_comm]

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities.
-/
theorem existsUnique_smul_eq (x y : ELL K) :
    ∃! a : ClassGroup (𝓞 K), (ellMulAction σ hK).smul a x = y := by
  refine ⟨(ellEquiv σ hK).symm y * ((ellEquiv σ hK).symm x)⁻¹, ?_, ?_⟩
  · simp only [ellMulAction_smul, inv_mul_cancel_right, Equiv.apply_symm_apply]
  · intro a ha
    rw [ellMulAction_smul] at ha
    rw [← ha, Equiv.symm_apply_apply, mul_inv_cancel_right]

/- English proof (translation)
Equip the data with the indicated structure. Supply the required witnesses or components.
-/
theorem ell_isPretransitive :
    letI := ellMulAction σ hK
    MulAction.IsPretransitive (ClassGroup (𝓞 K)) (ELL K) := by
  letI := ellMulAction σ hK
  exact ⟨fun x y ↦ (existsUnique_smul_eq σ hK x y).exists⟩

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Assume the hypotheses and unpack their components. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem ell_smul_eq_self_iff (a : ClassGroup (𝓞 K)) (x : ELL K) :
    (ellMulAction σ hK).smul a x = x ↔ a = 1 := by
  constructor
  · intro h
    exact (existsUnique_smul_eq σ hK x x).unique h
      (by rw [ellMulAction_smul, one_mul, Equiv.apply_symm_apply])
  · rintro rfl
    rw [ellMulAction_smul, one_mul, Equiv.apply_symm_apply]

/- English proof (translation)
Introduce a local definition for the expression. Rewrite the conclusion using the stated equalities.
-/
theorem card_ell : Nat.card (ELL K) = classNumber K := by
  let τ : K →+* ℂ := (IsAlgClosed.lift : K →ₐ[ℚ] ℂ).toRingHom
  rw [← Nat.card_congr (ellEquiv τ hK), classNumber, Nat.card_eq_fintype_card]

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem finite_ell : Finite (ELL K) :=
  Finite.of_equiv _ (ellEquiv (IsAlgClosed.lift : K →ₐ[ℚ] ℂ).toRingHom hK)

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Introduce a local definition for the expression. Establish an intermediate fact. Introduce a local definition for the expression.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Supply the required witnesses or components.
-/
theorem existsUnique_normalized (E : CMCurve K) :
    ∃! ι : 𝓞 K ≃+* isogEnd E.curve,
      ∀ a : 𝓞 K, endConst E.curve (ι a) = σ (algebraMap (𝓞 K) K a) := by
  obtain ⟨L, C, hL, hC, -⟩ := E.exists_lattice σ hK
  have hrange : (endConst E.curve).range = cmRing σ := by rw [range_endConst hC, hL]
  let e₀ : isogEnd E.curve ≃+* (endConst E.curve).range :=
    RingEquiv.ofBijective (endConst E.curve).rangeRestrict
      ⟨fun f g h ↦ endConst_injective (congrArg Subtype.val h),
        (endConst E.curve).rangeRestrict_surjective⟩
  have he₀ : ∀ f, (e₀ f : ℂ) = endConst E.curve f := fun _ ↦ rfl
  let ι : 𝓞 K ≃+* isogEnd E.curve :=
    (cmRingEquiv σ).trans ((RingEquiv.subringCongr hrange).symm.trans e₀.symm)
  have hι : ∀ a : 𝓞 K, endConst E.curve (ι a) = σ (algebraMap (𝓞 K) K a) := by
    intro a
    rw [← he₀, ← cmRingEquiv_apply]
    simp [ι]
  exact ⟨ι, hι, fun ι' hι' ↦ RingEquiv.ext fun a ↦ endConst_injective ((hι' a).trans (hι a).symm)⟩

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem normalized_ofLattice (L : PeriodPair) (hL : latticeEnd L = cmRing σ) (a : 𝓞 K) :
    endConst (weierstrassCurve L)
      (latticeEndEquiv L ⟨σ (algebraMap (𝓞 K) K a), hL ▸ ⟨a, rfl⟩⟩) = σ (algebraMap (𝓞 K) K a) :=
  endConst_latticeEndEquiv L _

end Quadratic

end Elliptic
end GroundTheory.Global
