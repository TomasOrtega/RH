import Mathlib

open NumberField IsDedekindDomain Pointwise
open scoped nonZeroDivisors

namespace ReciprocityTheory.Neutral.Bridge.HCF

section classGroup

variable {R R' : Type*} [CommRing R] [IsDedekindDomain R] [CommRing R'] [IsDedekindDomain R']

/- English proof (translation)
Use `mem_nonZeroDivisors_of_ne_zero ?_` and prove the remaining obligations. Rewrite using `[Ne, Ideal.zero_eq_bot, Ideal.map_eq_bot_iff_of_injective g.injective, ← Ideal.zero_eq_bot]`. Conclude with `nonZeroDivisors.coe_ne_zero I`.
-/
theorem map_mem_nzd (g : R ≃+* R') (I : (Ideal R)⁰) : (I : Ideal R).map g ∈ (Ideal R')⁰ := by
  refine mem_nonZeroDivisors_of_ne_zero ?_
  rw [Ne, Ideal.zero_eq_bot, Ideal.map_eq_bot_iff_of_injective g.injective, ← Ideal.zero_eq_bot]
  exact nonZeroDivisors.coe_ne_zero I

/- English proof (translation)
Apply `(ClassGroup.equiv (FractionRing R')).injective` to reduce the goal to its premises. Rewrite using `[ClassGroup.mulEquiv_apply, MulEquiv.apply_symm_apply, ClassGroup.equiv_mk0, ClassGroup.equiv_mk0]`. Simplify using `only [QuotientGroup.mk'_apply]`. Use `erw [QuotientGroup.congr_mk]`. Use `congr 1`.

Apply `Units.ext` to reduce the goal to its premises. Simplify using `only [Units.coe_mapEquiv, RingEquiv.coe_toMulEquiv, FractionalIdeal.coe_mk0]`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[FractionalIdeal.ringEquivOfRingEquiv_apply_val]`. Use extensionality with `x`.

Simplify using `only [Submodule.mem_map, FractionalIdeal.val_eq_coe, FractionalIdeal.mem_coe, FractionalIdeal.mem_coeIdeal]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, rfl⟩`. Take `⟨z, hz, rfl⟩` from `hy`. Use `⟨g z, Ideal.mem_map_of_mem _ hz, ?_⟩` and prove the remaining obligations.

Simplify using `[IsFractionRing.semilinearEquivOfRingEquiv]`. Introduce and unpack `⟨y, hy, rfl⟩`. Rewrite `hy` using `[Ideal.mem_map_of_equiv]`. Take `⟨z, hz, rfl⟩` from `hy`. Use `⟨algebraMap R (FractionRing R) z, ?_, ?_⟩` and prove the remaining obligations.

Conclude with `⟨z, hz, rfl⟩`. Simplify using `[IsFractionRing.semilinearEquivOfRingEquiv]`.
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
It suffices to establish `key : ∀ I : Ideal R, ∀ hI : I ∈ (Ideal R)⁰, f₁ (ClassGroup.mk0 ⟨I, hI⟩) = f₂ (ClassGroup.mk0 ⟨I, hI⟩) by`. Use extensionality with `c`. Take `⟨⟨I, hI⟩, rfl⟩` from `ClassGroup.mk0_surjective c`. Conclude with `key I hI`. Introduce `I`.

Proceed by induction on `I using UniqueFactorizationMonoid.induction_on_prime with`. Consider the case `h₁ => intro hI`. Conclude with `absurd hI (zero_notMem_nonZeroDivisors)`. Consider the case `h₂ u hu`. Introduce `hI`.

Establish `: (⟨u, hI⟩ : (Ideal R)⁰) = 1` using `Subtype.ext (by simpa using hu)`. Rewrite using `[this, map_one, map_one, map_one]`. Consider the case `h₃ I p hI' hp ih`. Introduce `hI`. Establish `hp0 : p ∈ (Ideal R)⁰` using `mem_nonZeroDivisors_of_ne_zero hp.ne_zero`.

Establish `hI0 : I ∈ (Ideal R)⁰`. Rewrite `hI`, the goal using `[mem_nonZeroDivisors_iff_ne_zero]`. Introduce and unpack `rfl`. Conclude with `hI (mul_zero p)`. Establish `: (⟨p * I, hI⟩ : (Ideal R)⁰) = ⟨p, hp0⟩ * ⟨I, hI0⟩` using `rfl`.

Rewrite using `[this, map_mul, map_mul, map_mul, ih hI0]`. Use `congr 1`. Establish `hpp : p.IsPrime` using `Ideal.isPrime_of_prime hp`. Establish `hpb : p ≠ ⊥` using `hp.ne_zero`. Conclude with `h ⟨p, hpp, hpb⟩`.
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
Establish `key : ∀ (hg : g ∈ A.decompositionSubgroup K), (⟨g, hg⟩ : A.decompositionSubgroup K) ∈ A.inertiaSubgroup K ↔ ∀ x ∈ A, g x - x ∈ A.nonunits`. Introduce `hg`. Rewrite using `[ValuationSubring.inertiaSubgroup, MonoidHom.mem_ker, RingEquiv.ext_iff]`. Simplify using `only [MulSemiringAction.toRingAut_apply, MulSemiringAction.toRingEquiv_apply_apply, RingAut.one_apply]`. Prove the components needed by the constructor for the conclusion.

Introduce `h x hx`. Establish `h1` using `h (IsLocalRing.residue A ⟨x, hx⟩)`. Rewrite `h1` using `[← IsLocalRing.ResidueField.residue_smul, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]`. Rewrite using `[ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal]`. Conclude with `⟨_, h1⟩`.

Introduce `h r`. Take `⟨⟨x, hx⟩, rfl⟩` from `IsLocalRing.residue_surjective r`. Rewrite using `[← IsLocalRing.ResidueField.residue_smul, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]`. Take `⟨_, h2⟩` from `ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.mp (h x hx)`. Conclude with `h2`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨g', hg'⟩, hin, rfl⟩`. Conclude with `⟨hg', (key hg').mp hin⟩`. Introduce and unpack `⟨hg, hx⟩`. Conclude with `⟨⟨g, hg⟩, (key hg).mpr hx, rfl⟩`.
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
