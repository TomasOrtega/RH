import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.LocDensSAChar

noncomputable section

open NumberField
open scoped nonZeroDivisors

namespace PI.VolStabSW

/- English proof (translation)
Establish `hw : w = (∑ i, (integralBasis F).repr (w * y⁻¹) i • integralBasis F i) * y`. Rewrite using `[(integralBasis F).sum_repr, mul_assoc, inv_mul_cancel₀ hy, mul_one]`. Rewrite using `[hw, Finset.sum_mul, map_sum]`. Use `Finset.sum_eq_zero (fun i _ => ?_)` and prove the remaining obligations. Rewrite using `[smul_mul_assoc, map_rat_smul, h0 i, smul_zero]`.
-/
private theorem addHom_eq_zero_of_integralBasis_mul {F : Type} [Field F] [NumberField F] (g : F →+ ℂ)
    {y : F} (hy : y ≠ 0) (h0 : ∀ i, g (integralBasis F i * y) = 0) (w : F) : g w = 0 := by
  have hw : w = (∑ i, (integralBasis F).repr (w * y⁻¹) i • integralBasis F i) * y := by
    rw [(integralBasis F).sum_repr, mul_assoc, inv_mul_cancel₀ hy, mul_one]
  rw [hw, Finset.sum_mul, map_sum]
  refine Finset.sum_eq_zero (fun i _ => ?_)
  rw [smul_mul_assoc, map_rat_smul, h0 i, smul_zero]

/- English proof (translation)
Take `⟨s, hs⟩` from `hfg`. Take `⟨b, hb⟩` from `IsLocalization.exist_integer_multiples_of_finset (M := (𝓞 F)⁰) (S := F) s`. Establish `hB0 : algebraMap (𝓞 F) F b ≠ 0` using `IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.2`. Set `T : Submodule ℤ F` to `{ carrier := {a | ∃ r : 𝓞 F, algebraMap (𝓞 F) F b * a = algebraMap (𝓞 F) F r} add_mem' := by`. Introduce and unpack `a a' ⟨r, hr⟩ ⟨r', hr'⟩`.

Conclude with `⟨r + r', by rw [mul_add, hr, hr', map_add]⟩`. Use the proof step `zero_mem' := ⟨0, by rw [mul_zero, map_zero]⟩`. Use the proof step `smul_mem' := by`. Introduce and unpack `n a ⟨r, hr⟩`. Conclude with `⟨n • r, by rw [mul_smul_comm, hr, map_zsmul]⟩ }`.

Establish `hsT : Submodule.span ℤ (s : Set F) ≤ T`. Rewrite using `[Submodule.span_le]`. Introduce `a ha`. Take `⟨r, hr⟩` from `hb a ha`. Conclude with `⟨r, by rw [hr, Algebra.smul_def]⟩`.

Use `⟨(algebraMap (𝓞 F) F b)⁻¹, inv_ne_zero hB0, fun a ha => ?_⟩` and prove the remaining obligations. Establish `has : a ∈ Submodule.span ℤ (s : Set F)` using `by rw [hs]; exact ha`. Take `⟨r, hr⟩` from `hsT has`. Use `⟨r, ?_⟩` and prove the remaining obligations. Establish `hrr : ((r : 𝓞 F) : F) = algebraMap (𝓞 F) F r`.

Both sides reduce to the same expression. Rewrite using `[hrr, ← hr, ← mul_assoc, inv_mul_cancel₀ hB0, one_mul]`.
-/
private theorem exists_mul_integers_of_fg {F : Type} [Field F] [NumberField F]
    (Λ : Submodule (𝓞 F) F) (hfg : (Λ.restrictScalars ℤ).FG) :
    ∃ c : F, c ≠ 0 ∧ ∀ a ∈ Λ, ∃ r : 𝓞 F, a = c * r := by
  obtain ⟨s, hs⟩ := hfg
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset (M := (𝓞 F)⁰) (S := F) s
  have hB0 : algebraMap (𝓞 F) F b ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.2
  let T : Submodule ℤ F :=
    { carrier := {a | ∃ r : 𝓞 F, algebraMap (𝓞 F) F b * a = algebraMap (𝓞 F) F r}
      add_mem' := by
        rintro a a' ⟨r, hr⟩ ⟨r', hr'⟩
        exact ⟨r + r', by rw [mul_add, hr, hr', map_add]⟩
      zero_mem' := ⟨0, by rw [mul_zero, map_zero]⟩
      smul_mem' := by
        rintro n a ⟨r, hr⟩
        exact ⟨n • r, by rw [mul_smul_comm, hr, map_zsmul]⟩ }
  have hsT : Submodule.span ℤ (s : Set F) ≤ T := by
    rw [Submodule.span_le]
    intro a ha
    obtain ⟨r, hr⟩ := hb a ha
    exact ⟨r, by rw [hr, Algebra.smul_def]⟩
  refine ⟨(algebraMap (𝓞 F) F b)⁻¹, inv_ne_zero hB0, fun a ha => ?_⟩
  have has : a ∈ Submodule.span ℤ (s : Set F) := by rw [hs]; exact ha
  obtain ⟨r, hr⟩ := hsT has
  refine ⟨r, ?_⟩
  have hrr : ((r : 𝓞 F) : F) = algebraMap (𝓞 F) F r := by
    rfl
  rw [hrr, ← hr, ← mul_assoc, inv_mul_cancel₀ hB0, one_mul]

/- English proof (translation)
Set `φ : F →ₗ[ℤ] (Module.Free.ChooseBasisIndex ℤ (𝓞 F) → ℂ)` to `{ toFun := fun y i => g (integralBasis F i * y) map_add' := fun y y' => by funext i; simp only [mul_add, map_add, Pi.add_apply] map_smul' := fun n y => by`. Use function extensionality and compare the values at `i`. Simplify using `only [mul_smul_comm, map_zsmul, RingHom.id_apply, Pi.smul_apply] }`. Set `ψ : (Module.Free.ChooseBasisIndex ℤ (𝓞 F) → ℤ) →ₗ[ℤ] (Module.Free.ChooseBasisIndex ℤ (𝓞 F) → ℂ)` to `{ toFun := fun z i => (z i : ℂ) map_add' := fun z z' => by funext i; simp only [Pi.add_apply, Int.cast_add] map_smul' := fun n z => by`. Use function extensionality and compare the values at `i`.

Simplify using `only [Pi.smul_apply, smul_eq_mul, Int.cast_mul, RingHom.id_apply, zsmul_eq_mul] }`. Establish `hφ : Function.Injective φ`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `y hy`. Assume the negation of the conclusion as `hy0`.

Take `⟨w, hw⟩` from `hne`. Conclude with `hw (addHom_eq_zero_of_integralBasis_mul g hy0 (fun i => congrFun hy i) w)`. Establish `hrange : (Λ.restrictScalars ℤ).map φ ≤ LinearMap.range ψ`. Introduce and unpack `_ ⟨y, hy, rfl⟩`. Establish `hmem : ∀ i, integralBasis F i * y ∈ Λ` using `fun i => by`.

Establish `h` using `Λ.smul_mem (RingOfIntegers.basis F i) hy`. Rewrite `h` using `[Algebra.smul_def, ← integralBasis_apply]`. Then use the resulting hypothesis. Use `choose n hn using fun i => hg _ (hmem i)`. Conclude with `⟨n, funext fun i => (hn i).symm⟩`. Establish `hQ : (((Λ.restrictScalars ℤ).map φ).comap ψ).FG` using `IsNoetherian.noetherian _`.

Establish `hmap : (((Λ.restrictScalars ℤ).map φ).comap ψ).map ψ = (Λ.restrictScalars ℤ).map φ`. Apply `le_antisymm` to reduce the goal to its premises. Introduce and unpack `x ⟨z, hz, rfl⟩`. Conclude with `hz`. Introduce `x hx`.

Take `⟨z, rfl⟩` from `hrange hx`. Conclude with `⟨z, hx, rfl⟩`. Establish `hfg` using `hQ.map ψ`. Rewrite `hfg` using `[hmap]`. Conclude with `Submodule.fg_of_fg_map_injective φ hφ hfg`.
-/
private theorem fg_of_addHom_intValued {F : Type} [Field F] [NumberField F] (Λ : Submodule (𝓞 F) F)
    (g : F →+ ℂ) (hg : ∀ a ∈ Λ, ∃ n : ℤ, g a = n) (hne : ∃ w, g w ≠ 0) :
    (Λ.restrictScalars ℤ).FG := by
  classical
  let φ : F →ₗ[ℤ] (Module.Free.ChooseBasisIndex ℤ (𝓞 F) → ℂ) :=
    { toFun := fun y i => g (integralBasis F i * y)
      map_add' := fun y y' => by funext i; simp only [mul_add, map_add, Pi.add_apply]
      map_smul' := fun n y => by
        funext i; simp only [mul_smul_comm, map_zsmul, RingHom.id_apply, Pi.smul_apply] }
  let ψ : (Module.Free.ChooseBasisIndex ℤ (𝓞 F) → ℤ) →ₗ[ℤ]
      (Module.Free.ChooseBasisIndex ℤ (𝓞 F) → ℂ) :=
    { toFun := fun z i => (z i : ℂ)
      map_add' := fun z z' => by funext i; simp only [Pi.add_apply, Int.cast_add]
      map_smul' := fun n z => by
        funext i
        simp only [Pi.smul_apply, smul_eq_mul, Int.cast_mul, RingHom.id_apply, zsmul_eq_mul] }
  have hφ : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro y hy
    by_contra hy0
    obtain ⟨w, hw⟩ := hne
    exact hw (addHom_eq_zero_of_integralBasis_mul g hy0 (fun i => congrFun hy i) w)
  have hrange : (Λ.restrictScalars ℤ).map φ ≤ LinearMap.range ψ := by
    rintro _ ⟨y, hy, rfl⟩
    have hmem : ∀ i, integralBasis F i * y ∈ Λ := fun i => by
      have h := Λ.smul_mem (RingOfIntegers.basis F i) hy
      rwa [Algebra.smul_def, ← integralBasis_apply] at h
    choose n hn using fun i => hg _ (hmem i)
    exact ⟨n, funext fun i => (hn i).symm⟩
  have hQ : (((Λ.restrictScalars ℤ).map φ).comap ψ).FG := IsNoetherian.noetherian _
  have hmap : (((Λ.restrictScalars ℤ).map φ).comap ψ).map ψ = (Λ.restrictScalars ℤ).map φ := by
    apply le_antisymm
    · rintro x ⟨z, hz, rfl⟩
      exact hz
    · intro x hx
      obtain ⟨z, rfl⟩ := hrange hx
      exact ⟨z, hx, rfl⟩
  have hfg := hQ.map ψ
  rw [hmap] at hfg
  exact Submodule.fg_of_fg_map_injective φ hφ hfg

/- English proof (translation)
Introduce `F _ _ Λ _ hnp g hg`. Assume the negation of the conclusion as `hall`. Take `⟨c, hc0, hc⟩` from `exists_mul_integers_of_fg Λ (fg_of_addHom_intValued Λ g hg (not_forall.mp hall))`. Conclude with `hnp c hc0 hc`.
-/
theorem addIntF_holds : AddIntF := by
  intro F _ _ Λ _ hnp g hg
  by_contra hall
  obtain ⟨c, hc0, hc⟩ := exists_mul_integers_of_fg Λ (fg_of_addHom_intValued Λ g hg (not_forall.mp hall))
  exact hnp c hc0 hc

/- English proof (translation)
The claim follows from `chInf_of hL addIntF_holds`.
-/
theorem chInf_of_lift (hL : ChLift) : ChInf :=
  chInf_of hL addIntF_holds

end PI.VolStabSW
