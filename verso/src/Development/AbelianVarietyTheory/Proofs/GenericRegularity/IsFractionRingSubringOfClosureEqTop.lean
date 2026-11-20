import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIntegralClosureOfEssFiniteTypeField

namespace GlobalTheory

/- English proof (translation)
Establish `: FaithfulSMul S Ω` using `(faithfulSMul_iff_algebraMap_injective S Ω).mpr hinj`. Use `IsFractionRing.of_field S Ω fun z => ?_` and prove the remaining obligations. Establish `hz : z ∈ Subfield.closure t` using `by rw [ht]; exact Subfield.mem_top z`. Take `⟨y, hy, w, hw, rfl⟩` from `Subfield.mem_closure_iff.mp hz`. Establish `hsub : Subring.closure t ≤ (algebraMap S Ω).range` using `Subring.closure_le.mpr (by rw [RingHom.coe_range]; exact hS)`.

Take `⟨a, rfl⟩` from `RingHom.mem_range.mp (hsub hy)`. Take `⟨b, rfl⟩` from `RingHom.mem_range.mp (hsub hw)`. Conclude with `⟨a, b, rfl⟩`.
-/
private theorem isFractionRing_of_closure_subset_range {Ω S : Type*} [Field Ω] [CommRing S]
    [Algebra S Ω] {t : Set Ω} (ht : Subfield.closure t = ⊤)
    (hinj : Function.Injective (algebraMap S Ω)) (hS : t ⊆ Set.range (algebraMap S Ω)) :
    IsFractionRing S Ω := by
  have : FaithfulSMul S Ω := (faithfulSMul_iff_algebraMap_injective S Ω).mpr hinj
  refine IsFractionRing.of_field S Ω fun z => ?_
  have hz : z ∈ Subfield.closure t := by rw [ht]; exact Subfield.mem_top z
  obtain ⟨y, hy, w, hw, rfl⟩ := Subfield.mem_closure_iff.mp hz
  have hsub : Subring.closure t ≤ (algebraMap S Ω).range :=
    Subring.closure_le.mpr (by rw [RingHom.coe_range]; exact hS)
  obtain ⟨a, rfl⟩ := RingHom.mem_range.mp (hsub hy)
  obtain ⟨b, rfl⟩ := RingHom.mem_range.mp (hsub hw)
  exact ⟨a, b, rfl⟩

/- English proof (translation)
Use `isFractionRing_of_closure_subset_range ht Subtype.val_injective fun x hx => ?_` and prove the remaining obligations. Conclude with `⟨⟨x, hD hx⟩, rfl⟩`.
-/
theorem isFractionRing_subring_of_closure_eq_top {Ω : Type*} [Field Ω] {t : Set Ω}
    (ht : Subfield.closure t = ⊤) (D : Subring Ω) (hD : t ⊆ D) : IsFractionRing D Ω :=
  by
    refine isFractionRing_of_closure_subset_range ht Subtype.val_injective fun x hx => ?_
    exact ⟨⟨x, hD hx⟩, rfl⟩

/- English proof (translation)
Introduce `O Ω _ _ _ _ _ _ hinj s hs`. Establish `: CharZero Ω` using `charZero_of_injective_algebraMap hinj`. Use `set R : Subalgebra O Ω := Algebra.adjoin O (s : Set Ω) with hRdef`. Establish `hsR : (s : Set Ω) ⊆ R` using `Algebra.subset_adjoin`. Establish `hOR : ∀ a, algebraMap O Ω a ∈ R` using `fun a => R.algebraMap_mem a`.

Establish `htR : Set.range (algebraMap O Ω) ∪ (s : Set Ω) ⊆ Set.range (algebraMap R Ω)`. Introduce and unpack `x (⟨a, rfl⟩ | hx)`. Conclude with `⟨⟨_, hOR a⟩, rfl⟩`. Conclude with `⟨⟨x, hsR hx⟩, rfl⟩`. Establish `: IsFractionRing R Ω` using `isFractionRing_of_closure_subset_range hs Subtype.val_injective htR`.

Establish `: Algebra.FiniteType O R` using `(Subalgebra.fg_iff_finiteType R).mp (Subalgebra.fg_adjoin_finset s)`. Establish `: Algebra.EssFiniteType R Ω` using `Algebra.EssFiniteType.of_isLocalization Ω (nonZeroDivisors R)`. Establish `hfin : Module.Finite R (integralClosure R Ω)` using `finite_integralClosure_of_essFiniteType_field O R Ω`. Use `set B : Subalgebra R Ω := integralClosure R Ω with hBdef`. Establish `hRB : ∀ x, x ∈ R → x ∈ B` using `fun x hx => B.algebraMap_mem ⟨x, hx⟩`.

Establish `htB : Set.range (algebraMap O Ω) ∪ (s : Set Ω) ⊆ Set.range (algebraMap B Ω)`. Introduce and unpack `x (⟨a, rfl⟩ | hx)`. Conclude with `⟨⟨_, hRB _ (hOR a)⟩, rfl⟩`. Conclude with `⟨⟨x, hRB _ (hsR hx)⟩, rfl⟩`. Establish `hBfrac : IsFractionRing B Ω` using `isFractionRing_of_closure_subset_range hs Subtype.val_injective htB`.

Establish `hBic : IsIntegrallyClosed B`. Use `(isIntegrallyClosed_iff Ω).mpr fun {x} hx => ?_` and prove the remaining obligations. Establish `hx' : x ∈ integralClosure B Ω` using `hx`. Rewrite `hx'` using `[hBdef, integralClosure_idem]`. Take `⟨y, rfl⟩` from `Algebra.mem_bot.mp hx'`.

Conclude with `⟨y, rfl⟩`. Establish `hkey : ∀ (L : Type) [Field L] (W : ValuationSubring L) (φ : B →+* L), (∀ y (hy : y ∈ R), φ (algebraMap R B ⟨y, hy⟩) ∈ W) → ∀ x, φ x ∈ W`. Introduce `L _ W φ hφ x`. Set `φR : R →+* W` to `(φ.comp (algebraMap R B)).codRestrict W.toSubring fun r => hφ r.1 r.2`. Establish `hx : IsIntegral W (φ x)` using `IsIntegral.map_of_comp_eq φR φ (by ext r; rfl) (Algebra.IsIntegral.isIntegral x)`.

Take `⟨y, hy⟩` from `(isIntegrallyClosed_iff L).mp inferInstance hx`. Rewrite using `[← hy]`. Conclude with `y.2`. Use `⟨B.restrictScalars O, fun x hx => hRB x (hsR hx), ?_, ?_, ?_, hBfrac, ?_, ?_⟩` and prove the remaining obligations. Establish `hBO : Algebra.FiniteType O B` using `Algebra.FiniteType.trans (S := R) inferInstance inferInstance`.

Conclude with `hBO`. Establish `: Module.IsTorsionFree O (B.restrictScalars O)`. Use `Module.IsTorsionFree.of_smul_eq_zero fun r m h => ?_` and prove the remaining obligations. Establish `h'` using `congrArg Subtype.val h`. Rewrite `h'` using `[Subalgebra.coe_smul, Algebra.smul_def, ZeroMemClass.coe_zero, mul_eq_zero]`.

Break down `h' with h' | h'` into its components or cases. Conclude with `Or.inl (hinj (by rw [h', map_zero]))`. Conclude with `Or.inr (Subtype.ext h')`. Use `infer_instance`. Conclude with `hBic`.

Introduce `D hDic hDO hDs x hx`. Establish `hRD : R.toSubring ≤ D`. Rewrite using `[hRdef, Algebra.adjoin_eq_ring_closure]`. Conclude with `Subring.closure_le.mpr (Set.union_subset (by rintro _ ⟨a, rfl⟩; exact hDO a) hDs)`. Establish `: IsFractionRing D Ω` using `isFractionRing_subring_of_closure_eq_top hs D (Set.union_subset (by rintro _ ⟨a, rfl⟩; exact hDO a) hDs)`.

Establish `hxi : IsIntegral R x` using `hx`. Establish `hxD : IsIntegral D x` using `IsIntegral.map_of_comp_eq (Subring.inclusion hRD : R →+* D) (RingHom.id Ω) (by ext r; rfl) hxi`. Take `⟨y, hy⟩` from `(isIntegrallyClosed_iff Ω).mp hDic hxD`. Rewrite using `[← hy]`. Conclude with `y.2`.

Introduce `L _ W φ hO hs' x`. Set `ψ : B →+* L` to `φ`. Use `hkey L W ψ (fun y hy => ?_) x` and prove the remaining obligations. Proceed by induction on `hy using Algebra.adjoin_induction with`. Consider the case `mem z hz => exact hs' ⟨z, hRB z (hsR hz)⟩ hz`.

Consider the case `algebraMap a => exact hO a`. Consider the case `add y z hy hz ihy ihz`. Establish `e : (⟨y + z, add_mem hy hz⟩ : R) = ⟨y, hy⟩ + ⟨z, hz⟩` using `rfl`. Rewrite using `[e, map_add, RingHom.map_add ψ]`. Conclude with `add_mem ihy ihz`.

Consider the case `mul y z hy hz ihy ihz`. Establish `e : (⟨y * z, mul_mem hy hz⟩ : R) = ⟨y, hy⟩ * ⟨z, hz⟩` using `rfl`. Rewrite using `[e, map_mul, RingHom.map_mul ψ]`. Conclude with `mul_mem ihy ihz`.
-/
theorem exists_normalisation_adjoin_finset_dvr :
    ∀ (O Ω : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] [Field Ω] [Algebra O Ω], Function.Injective (algebraMap O Ω) → ∀ (s : Finset Ω), Subfield.closure (Set.range (algebraMap O Ω) ∪ (s : Set Ω)) = ⊤ → ∃ A : Subalgebra O Ω, (s : Set Ω) ⊆ A ∧ Algebra.FiniteType O A ∧ Module.Flat O A ∧ IsIntegrallyClosed A ∧ IsFractionRing A Ω ∧ (∀ D : Subring Ω, IsIntegrallyClosed D → (∀ a, algebraMap O Ω a ∈ D) → (s : Set Ω) ⊆ D → (A : Set Ω) ⊆ D) ∧ ∀ (L : Type) [Field L] (W : ValuationSubring L) (φ : A →+* L), (∀ a, φ (algebraMap O A a) ∈ W) → (∀ (x : A), (x : Ω) ∈ s → φ x ∈ W) → ∀ x, φ x ∈ W := by
  intro O Ω _ _ _ _ _ _ hinj s hs
  classical
  have : CharZero Ω := charZero_of_injective_algebraMap hinj
  set R : Subalgebra O Ω := Algebra.adjoin O (s : Set Ω) with hRdef
  have hsR : (s : Set Ω) ⊆ R := Algebra.subset_adjoin
  have hOR : ∀ a, algebraMap O Ω a ∈ R := fun a => R.algebraMap_mem a
  have htR : Set.range (algebraMap O Ω) ∪ (s : Set Ω) ⊆ Set.range (algebraMap R Ω) := by
    rintro x (⟨a, rfl⟩ | hx)
    · exact ⟨⟨_, hOR a⟩, rfl⟩
    · exact ⟨⟨x, hsR hx⟩, rfl⟩
  have : IsFractionRing R Ω := isFractionRing_of_closure_subset_range hs Subtype.val_injective htR
  have : Algebra.FiniteType O R := (Subalgebra.fg_iff_finiteType R).mp (Subalgebra.fg_adjoin_finset s)
  have : Algebra.EssFiniteType R Ω := Algebra.EssFiniteType.of_isLocalization Ω (nonZeroDivisors R)
  have hfin : Module.Finite R (integralClosure R Ω) :=
    finite_integralClosure_of_essFiniteType_field O R Ω
  set B : Subalgebra R Ω := integralClosure R Ω with hBdef
  have hRB : ∀ x, x ∈ R → x ∈ B := fun x hx => B.algebraMap_mem ⟨x, hx⟩
  have htB : Set.range (algebraMap O Ω) ∪ (s : Set Ω) ⊆ Set.range (algebraMap B Ω) := by
    rintro x (⟨a, rfl⟩ | hx)
    · exact ⟨⟨_, hRB _ (hOR a)⟩, rfl⟩
    · exact ⟨⟨x, hRB _ (hsR hx)⟩, rfl⟩
  have hBfrac : IsFractionRing B Ω := isFractionRing_of_closure_subset_range hs Subtype.val_injective htB
  have hBic : IsIntegrallyClosed B := by
    refine (isIntegrallyClosed_iff Ω).mpr fun {x} hx => ?_
    have hx' : x ∈ integralClosure B Ω := hx
    rw [hBdef, integralClosure_idem] at hx'
    obtain ⟨y, rfl⟩ := Algebra.mem_bot.mp hx'
    exact ⟨y, rfl⟩
  have hkey : ∀ (L : Type) [Field L] (W : ValuationSubring L) (φ : B →+* L),
      (∀ y (hy : y ∈ R), φ (algebraMap R B ⟨y, hy⟩) ∈ W) → ∀ x, φ x ∈ W := by
    intro L _ W φ hφ x
    let φR : R →+* W := (φ.comp (algebraMap R B)).codRestrict W.toSubring fun r => hφ r.1 r.2
    have hx : IsIntegral W (φ x) :=
      IsIntegral.map_of_comp_eq φR φ (by ext r; rfl) (Algebra.IsIntegral.isIntegral x)
    obtain ⟨y, hy⟩ := (isIntegrallyClosed_iff L).mp inferInstance hx
    rw [← hy]
    exact y.2
  refine ⟨B.restrictScalars O, fun x hx => hRB x (hsR hx), ?_, ?_, ?_, hBfrac, ?_, ?_⟩
  · have hBO : Algebra.FiniteType O B := Algebra.FiniteType.trans (S := R) inferInstance inferInstance
    exact hBO
  · have : Module.IsTorsionFree O (B.restrictScalars O) := by
      refine Module.IsTorsionFree.of_smul_eq_zero fun r m h => ?_
      have h' := congrArg Subtype.val h
      rw [Subalgebra.coe_smul, Algebra.smul_def, ZeroMemClass.coe_zero, mul_eq_zero] at h'
      rcases h' with h' | h'
      · exact Or.inl (hinj (by rw [h', map_zero]))
      · exact Or.inr (Subtype.ext h')
    infer_instance
  · exact hBic
  · intro D hDic hDO hDs x hx
    have hRD : R.toSubring ≤ D := by
      rw [hRdef, Algebra.adjoin_eq_ring_closure]
      exact Subring.closure_le.mpr (Set.union_subset (by rintro _ ⟨a, rfl⟩; exact hDO a) hDs)
    have : IsFractionRing D Ω := isFractionRing_subring_of_closure_eq_top hs D
      (Set.union_subset (by rintro _ ⟨a, rfl⟩; exact hDO a) hDs)
    have hxi : IsIntegral R x := hx
    have hxD : IsIntegral D x :=
      IsIntegral.map_of_comp_eq (Subring.inclusion hRD : R →+* D) (RingHom.id Ω) (by ext r; rfl) hxi
    obtain ⟨y, hy⟩ := (isIntegrallyClosed_iff Ω).mp hDic hxD
    rw [← hy]
    exact y.2
  · intro L _ W φ hO hs' x
    let ψ : B →+* L := φ
    refine hkey L W ψ (fun y hy => ?_) x
    induction hy using Algebra.adjoin_induction with
    | mem z hz => exact hs' ⟨z, hRB z (hsR hz)⟩ hz
    | algebraMap a => exact hO a
    | add y z hy hz ihy ihz =>
      have e : (⟨y + z, add_mem hy hz⟩ : R) = ⟨y, hy⟩ + ⟨z, hz⟩ := rfl
      rw [e, map_add, RingHom.map_add ψ]
      exact add_mem ihy ihz
    | mul y z hy hz ihy ihz =>
      have e : (⟨y * z, mul_mem hy hz⟩ : R) = ⟨y, hy⟩ * ⟨z, hz⟩ := rfl
      rw [e, map_mul, RingHom.map_mul ψ]
      exact mul_mem ihy ihz

end GlobalTheory
