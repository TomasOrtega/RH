import Mathlib

open NumberField IsDedekindDomain Pointwise
open scoped nonZeroDivisors

namespace ReciprocityTheory.Neutral.Bridge.HCF

section classGroup

variable {R R' : Type*} [CommRing R] [IsDedekindDomain R] [CommRing R'] [IsDedekindDomain R']

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem map_mem_nzd (g : R ≃+* R') (I : (Ideal R)⁰) : (I : Ideal R).map g ∈ (Ideal R')⁰ := by
  refine mem_nonZeroDivisors_of_ne_zero ?_
  rw [Ne, Ideal.zero_eq_bot, Ideal.map_eq_bot_iff_of_injective g.injective, ← Ideal.zero_eq_bot]
  exact nonZeroDivisors.coe_ne_zero I

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Reduce the equality to equality of the corresponding arguments. Reduce the claim to the hypotheses of an applicable result.

Simplify using the standard rewrite rules. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.

Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules.

Assume the hypotheses and unpack their components. Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Supply the required witnesses or components.

Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem classGroup_mulEquiv_mk0 (g : R ≃+* R') (I : (Ideal R)⁰) :
    ClassGroup.mulEquiv g (ClassGroup.mk0 I) = ClassGroup.mk0 ⟨(I : Ideal R).map g, map_mem_nzd g I⟩ := by
  apply (ClassGroup.equiv (FractionRing R')).injective
  rw [ClassGroup.mulEquiv_apply, MulEquiv.apply_symm_apply, ClassGroup.equiv_mk0, ClassGroup.equiv_mk0]
  simp only [QuotientGroup.mk'_apply]
  erw [QuotientGroup.congr_mk]
  congr 1
  apply Units.ext
  simp only [Units.coe_mapEquiv, RingEquiv.coe_toMulEquiv, FractionalIdeal.coe_mk0]
  apply Subtype.ext
  rw [FractionalIdeal.ringEquivOfRingEquiv_apply_val]
  ext x
  simp only [Submodule.mem_map, FractionalIdeal.val_eq_coe, FractionalIdeal.mem_coe, FractionalIdeal.mem_coeIdeal]
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨z, hz, rfl⟩ := hy
    refine ⟨g z, Ideal.mem_map_of_mem _ hz, ?_⟩
    simp [IsFractionRing.semilinearEquivOfRingEquiv]
  · rintro ⟨y, hy, rfl⟩
    rw [Ideal.mem_map_of_equiv] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    refine ⟨algebraMap R (FractionRing R) z, ?_, ?_⟩
    · exact ⟨z, hz, rfl⟩
    · simp [IsFractionRing.semilinearEquivOfRingEquiv]

/- English proof (translation)
Reduce the argument to an intermediate assertion. By extensionality, compare the relevant components. Extract witnesses or component facts from the available result. Fix the arbitrary inputs or assume the hypotheses. Proceed by induction.

Treat this case separately. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Rewrite the hypotheses and the conclusion using the stated equalities.

Assume the hypotheses and unpack their components. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Establish an intermediate fact.

Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem classGroup_hom_ext {G : Type*} [Monoid G] (f₁ f₂ : ClassGroup R →* G)
    (h : ∀ v : HeightOneSpectrum R, f₁ (ClassGroup.mk0 ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩) =
      f₂ (ClassGroup.mk0 ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩)) : f₁ = f₂ := by
  suffices key : ∀ I : Ideal R, ∀ hI : I ∈ (Ideal R)⁰, f₁ (ClassGroup.mk0 ⟨I, hI⟩) = f₂ (ClassGroup.mk0 ⟨I, hI⟩) by
    ext c
    obtain ⟨⟨I, hI⟩, rfl⟩ := ClassGroup.mk0_surjective c
    exact key I hI
  intro I
  induction I using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => intro hI; exact absurd hI (zero_notMem_nonZeroDivisors)
  | h₂ u hu =>
    intro hI
    have : (⟨u, hI⟩ : (Ideal R)⁰) = 1 := Subtype.ext (by simpa using hu)
    rw [this, map_one, map_one, map_one]
  | h₃ I p hI' hp ih =>
    intro hI
    have hp0 : p ∈ (Ideal R)⁰ := mem_nonZeroDivisors_of_ne_zero hp.ne_zero
    have hI0 : I ∈ (Ideal R)⁰ := by
      rw [mem_nonZeroDivisors_iff_ne_zero] at hI ⊢
      rintro rfl; exact hI (mul_zero p)
    have : (⟨p * I, hI⟩ : (Ideal R)⁰) = ⟨p, hp0⟩ * ⟨I, hI0⟩ := rfl
    rw [this, map_mul, map_mul, map_mul, ih hI0]
    congr 1
    have hpp : p.IsPrime := Ideal.isPrime_of_prime hp
    have hpb : p ≠ ⊥ := hp.ne_zero
    exact h ⟨p, hpp, hpb⟩

end classGroup

section inertia

variable (K : Type*) {L : Type*} [Field K] [Field L] [Algebra K L]

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Supply the required witnesses or components.

Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Prove the components needed by the constructor for the conclusion.

Assume the hypotheses and unpack their components. Supply the required witnesses or components. Assume the hypotheses and unpack their components. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem mem_inertia_map_iff (A : ValuationSubring L) (g : L ≃ₐ[K] L) :
    g ∈ (A.inertiaSubgroup K).map (A.decompositionSubgroup K).subtype ↔
      g • A = A ∧ ∀ x ∈ A, g x - x ∈ A.nonunits := by
  have key : ∀ (hg : g ∈ A.decompositionSubgroup K), (⟨g, hg⟩ : A.decompositionSubgroup K) ∈ A.inertiaSubgroup K ↔
      ∀ x ∈ A, g x - x ∈ A.nonunits := by
    intro hg
    rw [ValuationSubring.inertiaSubgroup, MonoidHom.mem_ker, RingEquiv.ext_iff]
    simp only [MulSemiringAction.toRingAut_apply, MulSemiringAction.toRingEquiv_apply_apply, RingAut.one_apply]
    constructor
    · intro h x hx
      have h1 := h (IsLocalRing.residue A ⟨x, hx⟩)
      rw [← IsLocalRing.ResidueField.residue_smul, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff] at h1
      rw [ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal]
      exact ⟨_, h1⟩
    · intro h r
      obtain ⟨⟨x, hx⟩, rfl⟩ := IsLocalRing.residue_surjective r
      rw [← IsLocalRing.ResidueField.residue_smul, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
      obtain ⟨_, h2⟩ := ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.mp (h x hx)
      exact h2
  constructor
  · rintro ⟨⟨g', hg'⟩, hin, rfl⟩
    exact ⟨hg', (key hg').mp hin⟩
  · rintro ⟨hg, hx⟩
    exact ⟨⟨g, hg⟩, (key hg).mpr hx, rfl⟩

end inertia

end ReciprocityTheory.Neutral.Bridge.HCF
