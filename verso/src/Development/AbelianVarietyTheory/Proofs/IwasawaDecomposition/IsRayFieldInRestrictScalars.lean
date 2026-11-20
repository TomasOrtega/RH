import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.QuadraticFieldDiscPrimeThreeModFour

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Host GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Fld
open scoped nonZeroDivisors IntermediateField

namespace GlobalTheory.Mem.Fld

/- English proof (translation)
Establish `hmem : ∀ x : K, (K.val : K →+* ℂ) x ∈ M.restrictScalars ℚ` using `fun x => by`. Rewrite using `[IntermediateField.mem_restrictScalars]`. Conclude with `M.algebraMap_mem x`. Establish `: NumberField (M.restrictScalars ℚ)` using `hM`. Use `⟨hmem, inferInstance, ?_⟩` and prove the remaining obligations.

Use `letI := algOf (K.val : K →+* ℂ) (M.restrictScalars ℚ) hmem`. Conclude with `h.of_algEquiv { toFun := fun y => ⟨y.1, y.2⟩ invFun := fun y => ⟨y.1, y.2⟩ left_inv := fun _ => rfl right_inv := fun _ => rfl map_mul' := fun _ _ => rfl map_add' := fun _ _ => rfl commutes' := fun _ => rfl }`.
-/
theorem IsRayField.isRayFieldIn_restrictScalars {K : IntermediateField ℚ ℂ} [NumberField K]
    {M : IntermediateField K ℂ} [hM : NumberField M] {𝔮 : Ideal (𝓞 K)} (h : IsRayField K M 𝔮) :
    IsRayFieldIn (K.val : K →+* ℂ) 𝔮 (M.restrictScalars ℚ) := by
  have hmem : ∀ x : K, (K.val : K →+* ℂ) x ∈ M.restrictScalars ℚ := fun x => by
    rw [IntermediateField.mem_restrictScalars]
    exact M.algebraMap_mem x
  have : NumberField (M.restrictScalars ℚ) := hM
  refine ⟨hmem, inferInstance, ?_⟩
  letI := algOf (K.val : K →+* ℂ) (M.restrictScalars ℚ) hmem
  exact h.of_algEquiv
    { toFun := fun y => ⟨y.1, y.2⟩
      invFun := fun y => ⟨y.1, y.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl
      map_add' := fun _ _ => rfl
      commutes' := fun _ => rfl }

/- English proof (translation)
Establish `hset : FieldSize.weberSet L 1 = {L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2)}`. Use extensionality with `w`. Simplify using `only [FieldSize.weberSet, Nat.cast_one, div_one, Set.mem_insert_iff, Set.mem_ofPred_eq, Set.mem_singleton_iff]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `(hw | ⟨z, hz, hz', -⟩)`.

Conclude with `hw`. Conclude with `absurd hz hz'`. Conclude with `fun hw => Or.inl hw`. Establish `hΔ0 : L.g₂ ^ 3 - 27 * L.g₃ ^ 2 ≠ 0`. Rewrite using `[← latticeCurve_Δ L]`.

Conclude with `latticeCurve_Δ_ne_zero L`. Establish `hj : (latticeCurve L).j = 1728 * (L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2))`. Rewrite using `[WeierstrassCurve.j, Units.val_inv_eq_inv_val, WeierstrassCurve.coe_Δ', latticeCurve_c₄, latticeCurve_Δ]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.

Establish `h1728 : ∀ S : IntermediateField K ℂ, (1728 : ℂ) ∈ S` using `fun S => by`. Simplify using the standard rewrite rules. Rewrite using `[hset, hj]`. Use `set w := L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2)`. Apply `le_antisymm` to reduce the goal to its premises.

Rewrite using `[IntermediateField.adjoin_le_iff, Set.singleton_subset_iff, SetLike.mem_coe]`. Establish `hw : (1728 : ℂ)⁻¹ * (1728 * w) = w` using `by field_simp`. Establish `hm : (1728 : ℂ)⁻¹ * (1728 * w) ∈ K⟮1728 * w⟯` using `mul_mem (inv_mem (h1728 _)) (IntermediateField.mem_adjoin_simple_self K _)`. Rewrite `hm` using `[hw]`. Then use the resulting hypothesis. Rewrite using `[IntermediateField.adjoin_le_iff, Set.singleton_subset_iff, SetLike.mem_coe]`.

Conclude with `mul_mem (h1728 _) (IntermediateField.mem_adjoin_simple_self K _)`.
-/
theorem adjoin_weberSet_one (K : Type) [Field K] [CharZero K] [Algebra K ℂ] (L : PeriodPair) :
    IntermediateField.adjoin K (FieldSize.weberSet L 1) = K⟮(latticeCurve L).j⟯ := by
  have hset : FieldSize.weberSet L 1 = {L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2)} := by
    ext w
    simp only [FieldSize.weberSet, Nat.cast_one, div_one, Set.mem_insert_iff, Set.mem_ofPred_eq,
      Set.mem_singleton_iff]
    constructor
    · rintro (hw | ⟨z, hz, hz', -⟩)
      · exact hw
      · exact absurd hz hz'
    · exact fun hw => Or.inl hw
  have hΔ0 : L.g₂ ^ 3 - 27 * L.g₃ ^ 2 ≠ 0 := by
    rw [← latticeCurve_Δ L]; exact latticeCurve_Δ_ne_zero L
  have hj : (latticeCurve L).j = 1728 * (L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2)) := by
    rw [WeierstrassCurve.j, Units.val_inv_eq_inv_val, WeierstrassCurve.coe_Δ', latticeCurve_c₄,
      latticeCurve_Δ]
    field_simp
    ring
  have h1728 : ∀ S : IntermediateField K ℂ, (1728 : ℂ) ∈ S := fun S => by
    simp
  rw [hset, hj]
  set w := L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2)
  apply le_antisymm
  · rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff, SetLike.mem_coe]
    have hw : (1728 : ℂ)⁻¹ * (1728 * w) = w := by field_simp
    have hm : (1728 : ℂ)⁻¹ * (1728 * w) ∈ K⟮1728 * w⟯ :=
      mul_mem (inv_mem (h1728 _)) (IntermediateField.mem_adjoin_simple_self K _)
    rwa [hw] at hm
  · rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff, SetLike.mem_coe]
    exact mul_mem (h1728 _) (IntermediateField.mem_adjoin_simple_self K _)

/- English proof (translation)
Introduce `hW d F A hd h4 h3 hG`. Use `set x := sqrtNegNat d with hxdef`. Establish `hx : x ^ 2 = -(d : ℂ)` using `sqrtNegNat_sq d`. Establish `hint : IsIntegral ℚ x`. Use `⟨Polynomial.X ^ 2 + Polynomial.C (d : ℚ), Polynomial.monic_X_pow_add_C _ two_ne_zero, ?_⟩` and prove the remaining obligations.

Simplify using `[hx]`. Establish `: FiniteDimensional ℚ ℚ⟮x⟯` using `IntermediateField.adjoin.finiteDimensional hint`. Establish `hNF : NumberField ℚ⟮x⟯` using `NumberField.mk`. Take `⟨-, hfin, habs⟩` from `isGalois_finrank_discr_adjoin_sqrt_neg_prime d x hd h4 hx`. Establish `hd0 : 0 < d` using `hd.pos`.

Establish `hTC : IsTotallyComplex ℚ⟮x⟯` using `isTotallyComplex_of_sq_eq_neg hd0 (x := IntermediateField.AdjoinSimple.gen ℚ x) (Subtype.ext (by simpa using hx))`. Establish `hdisc : discr ℚ⟮x⟯ = -(d : ℤ)`. Establish `hnc : NumberField.InfinitePlace.nrComplexPlaces ℚ⟮x⟯ = 1`. Use `IsTotallyComplex.finrank (K := ℚ⟮x⟯)` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Establish `hs` using `sign_discr (K := ℚ⟮x⟯)`. Rewrite `hs` using `[hnc, pow_one]`. Establish `hneg : discr ℚ⟮x⟯ < 0` using `Int.sign_eq_neg_one_iff_neg.1 hs`. Establish `h` using `Int.natAbs_eq (discr ℚ⟮x⟯)`. Rewrite `h` using `[habs]`.

Use linear arithmetic over natural numbers and integers. Establish `hG'` using `hG`. Take `⟨-, -, L, hL, -, -, -⟩` from `hG`. Establish `hlat : ∀ z, z ∈ L.lattice ↔ ∃ a : 𝓞 ℚ⟮x⟯, algebraMap ℚ⟮x⟯ ℂ (a : ℚ⟮x⟯) = z`. Introduce `z`.

Rewrite using `[hL z]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hz, hzi⟩`. Establish `hi : IsIntegral ℤ (⟨z, hz⟩ : ℚ⟮x⟯)` using `(isIntegral_algHom_iff ((ℚ⟮x⟯).val.toRingHom.toIntAlgHom) Subtype.val_injective).1 hzi`. Conclude with `⟨⟨⟨z, hz⟩, hi⟩, rfl⟩`.

Introduce and unpack `⟨a, rfl⟩`. Conclude with `⟨(a : ℚ⟮x⟯).2, (RingOfIntegers.isIntegral_coe a).map ((ℚ⟮x⟯).val.toRingHom.toIntAlgHom)⟩`. Establish `hdlt : discr ℚ⟮x⟯ < -4` using `by rw [hdisc]; omega`. Take `⟨_, hAb, hRay⟩` from `hW ℚ⟮x⟯ hfin hdlt L hlat 1 one_pos`. Establish `hone : Ideal.span {((1 : ℕ) : 𝓞 ℚ⟮x⟯)} = ⊤` using `by simp`.

Rewrite `hRay` using `[hone]`. Establish `hRF : IsRayField ℚ⟮x⟯ (IntermediateField.adjoin ℚ⟮x⟯ (FieldSize.weberSet L 1)) ⊤` using `⟨hAb, hRay⟩`. Use `⟨hNF, hdisc, hfin, ?_⟩` and prove the remaining obligations. Establish `hIn` using `hRF.isRayFieldIn_restrictScalars`. Rewrite `hIn` using `[adjoin_weberSet_one]`.

Establish `hEq : (ℚ⟮x⟯⟮(latticeCurve L).j⟯).restrictScalars ℚ = hilbertField d F`. Rewrite using `[hilbertField_eq hG' hL]`. Conclude with `IntermediateField.adjoin_simple_adjoin_simple ℚ (latticeCurve L).j (α := x)`. Rewrite using `[← hEq]`. Conclude with `hIn`.
-/
theorem isRayFieldIn_hilbertField : WeberRayFieldSt → ∀ (d : ℕ) (F : IntermediateField ℚ ℂ) (A : WeierstrassCurve F),
    d.Prime → d % 4 = 3 → 3 < d → IsGoodCMCurve d F A → ∃ _ : NumberField ℚ⟮sqrtNegNat d⟯,
      discr ℚ⟮sqrtNegNat d⟯ = -(d : ℤ) ∧ Module.finrank ℚ ℚ⟮sqrtNegNat d⟯ = 2 ∧
        IsRayFieldIn (ℚ⟮sqrtNegNat d⟯.val : ℚ⟮sqrtNegNat d⟯ →+* ℂ) ⊤ (hilbertField d F) := by
  intro hW d F A hd h4 h3 hG
  set x := sqrtNegNat d with hxdef
  have hx : x ^ 2 = -(d : ℂ) := sqrtNegNat_sq d
  have hint : IsIntegral ℚ x := by
    refine ⟨Polynomial.X ^ 2 + Polynomial.C (d : ℚ), Polynomial.monic_X_pow_add_C _ two_ne_zero, ?_⟩
    simp [hx]
  have : FiniteDimensional ℚ ℚ⟮x⟯ := IntermediateField.adjoin.finiteDimensional hint
  have hNF : NumberField ℚ⟮x⟯ := NumberField.mk
  obtain ⟨-, hfin, habs⟩ := isGalois_finrank_discr_adjoin_sqrt_neg_prime d x hd h4 hx
  have hd0 : 0 < d := hd.pos
  have hTC : IsTotallyComplex ℚ⟮x⟯ :=
    isTotallyComplex_of_sq_eq_neg hd0 (x := IntermediateField.AdjoinSimple.gen ℚ x)
      (Subtype.ext (by simpa using hx))
  have hdisc : discr ℚ⟮x⟯ = -(d : ℤ) := by
    have hnc : NumberField.InfinitePlace.nrComplexPlaces ℚ⟮x⟯ = 1 := by
      have := IsTotallyComplex.finrank (K := ℚ⟮x⟯)
      omega
    have hs := sign_discr (K := ℚ⟮x⟯)
    rw [hnc, pow_one] at hs
    have hneg : discr ℚ⟮x⟯ < 0 := Int.sign_eq_neg_one_iff_neg.1 hs
    have h := Int.natAbs_eq (discr ℚ⟮x⟯)
    rw [habs] at h
    omega
  have hG' := hG
  obtain ⟨-, -, L, hL, -, -, -⟩ := hG
  have hlat : ∀ z, z ∈ L.lattice ↔ ∃ a : 𝓞 ℚ⟮x⟯, algebraMap ℚ⟮x⟯ ℂ (a : ℚ⟮x⟯) = z := by
    intro z
    rw [hL z]
    constructor
    · rintro ⟨hz, hzi⟩
      have hi : IsIntegral ℤ (⟨z, hz⟩ : ℚ⟮x⟯) :=
        (isIntegral_algHom_iff ((ℚ⟮x⟯).val.toRingHom.toIntAlgHom) Subtype.val_injective).1 hzi
      exact ⟨⟨⟨z, hz⟩, hi⟩, rfl⟩
    · rintro ⟨a, rfl⟩
      exact ⟨(a : ℚ⟮x⟯).2,
        (RingOfIntegers.isIntegral_coe a).map ((ℚ⟮x⟯).val.toRingHom.toIntAlgHom)⟩
  have hdlt : discr ℚ⟮x⟯ < -4 := by rw [hdisc]; omega
  obtain ⟨_, hAb, hRay⟩ := hW ℚ⟮x⟯ hfin hdlt L hlat 1 one_pos
  have hone : Ideal.span {((1 : ℕ) : 𝓞 ℚ⟮x⟯)} = ⊤ := by simp
  rw [hone] at hRay
  have hRF : IsRayField ℚ⟮x⟯ (IntermediateField.adjoin ℚ⟮x⟯ (FieldSize.weberSet L 1)) ⊤ := ⟨hAb, hRay⟩
  refine ⟨hNF, hdisc, hfin, ?_⟩
  have hIn := hRF.isRayFieldIn_restrictScalars
  rw [adjoin_weberSet_one] at hIn
  have hEq : (ℚ⟮x⟯⟮(latticeCurve L).j⟯).restrictScalars ℚ = hilbertField d F := by
    rw [hilbertField_eq hG' hL]
    exact IntermediateField.adjoin_simple_adjoin_simple ℚ (latticeCurve L).j (α := x)
  rw [← hEq]
  exact hIn

end GlobalTheory.Mem.Fld
