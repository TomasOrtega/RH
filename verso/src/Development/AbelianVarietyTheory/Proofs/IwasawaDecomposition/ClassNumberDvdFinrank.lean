import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypeNormOfKummer
import Development.AbelianVarietyTheory.Proofs.HeightProofs.HeckeIdealEqOfRay

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.NT GlobalTheory.Mem.Fld GlobalTheory.FieldSize
open scoped nonZeroDivisors

namespace GlobalTheory.Mem.ClassDvd

/- English proof (translation)
Distinguish the cases in `ht : m = ⊤`. Take `⟨I, hI⟩` from `ClassGroup.mk0_surjective c`. Conclude with `⟨I, by rw [ht, ← Ideal.one_eq_top]; exact isCoprime_one_right, hI⟩`. Take `⟨J, hJ⟩` from `ClassGroup.mk0_surjective c⁻¹`. Establish `hJ0 : (J : Ideal R) ≠ 0` using `nonZeroDivisors.coe_ne_zero J`.

Take `⟨a, ha⟩` from `IsDedekindDomain.exists_sup_span_eq (I := (J : Ideal R) * m) (J := J) Ideal.mul_le_left (mul_ne_zero hJ0 hm)`. Take `⟨M, hM⟩ : (J : Ideal R) ∣ Ideal.span {a}` from `Ideal.dvd_iff_le.2 (ha ▸ le_sup_right)`. Establish `h1 : m ⊔ M = ⊤`. Apply `mul_left_cancel₀ hJ0` to reduce the goal to its premises. Rewrite using `[Ideal.mul_sup, ← hM, ha, Ideal.mul_top]`.

Establish `hM0 : M ≠ 0`. Introduce and unpack `rfl`. Conclude with `ht (by simpa using h1)`. Use `⟨⟨M, mem_nonZeroDivisors_of_ne_zero hM0⟩, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Ideal.isCoprime_iff_sup_eq, sup_comm]`.

Conclude with `h1`. Establish `ha0 : a ≠ 0`. Introduce and unpack `rfl`. Conclude with `mul_ne_zero hJ0 hM0 (by simpa using hM.symm)`. Rewrite using `[← inv_inv c, ← hJ, ClassGroup.mk0_eq_mk0_inv_iff]`.

Conclude with `⟨a, ha0, by rw [hM, mul_comm]⟩`.
-/
theorem classGroup_exists_integral_ideal_coprime {R : Type} [CommRing R] [IsDedekindDomain R] {m : Ideal R} (hm : m ≠ ⊥)
    (c : ClassGroup R) : ∃ I : (Ideal R)⁰, IsCoprime (I : Ideal R) m ∧ ClassGroup.mk0 I = c := by
  by_cases ht : m = ⊤
  · obtain ⟨I, hI⟩ := ClassGroup.mk0_surjective c
    exact ⟨I, by rw [ht, ← Ideal.one_eq_top]; exact isCoprime_one_right, hI⟩
  obtain ⟨J, hJ⟩ := ClassGroup.mk0_surjective c⁻¹
  have hJ0 : (J : Ideal R) ≠ 0 := nonZeroDivisors.coe_ne_zero J
  obtain ⟨a, ha⟩ := IsDedekindDomain.exists_sup_span_eq (I := (J : Ideal R) * m) (J := J) Ideal.mul_le_left
    (mul_ne_zero hJ0 hm)
  obtain ⟨M, hM⟩ : (J : Ideal R) ∣ Ideal.span {a} := Ideal.dvd_iff_le.2 (ha ▸ le_sup_right)
  have h1 : m ⊔ M = ⊤ := by
    apply mul_left_cancel₀ hJ0
    rw [Ideal.mul_sup, ← hM, ha, Ideal.mul_top]
  have hM0 : M ≠ 0 := by
    rintro rfl
    exact ht (by simpa using h1)
  refine ⟨⟨M, mem_nonZeroDivisors_of_ne_zero hM0⟩, ?_, ?_⟩
  · rw [Ideal.isCoprime_iff_sup_eq, sup_comm]; exact h1
  · have ha0 : a ≠ 0 := by
      rintro rfl
      exact mul_ne_zero hJ0 hM0 (by simpa using hM.symm)
    rw [← inv_inv c, ← hJ, ClassGroup.mk0_eq_mk0_inv_iff]
    exact ⟨a, ha0, by rw [hM, mul_comm]⟩

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] {𝔮 : Ideal (𝓞 K)}

/- English proof (translation)
Proceed by induction on `I using UniqueFactorizationMonoid.induction_on_prime with`. Consider the case `h₁ => exact fun h => absurd rfl h`. Consider the case `h₂ I hI`. Introduce `_ _`. Take `rfl : I = 1` from `by rw [Ideal.one_eq_top]; exact Ideal.isUnit_iff.1 hI`.

Conclude with `⟨1, fun χ => by rw [GlobalTheory.NT.Model.heckeIdeal_top]; simp⟩`. Consider the case `h₃ I p hI0 hp ih`. Introduce `_ hc`. Take `⟨σ, hσ⟩` from `ih hI0 hc.of_mul_left_right`. Set `v : HeightOneSpectrum (𝓞 K)` to `⟨p, Ideal.isPrime_of_prime hp, hp.ne_zero⟩`.

Establish `hv : ¬ v.asIdeal ∣ 𝔮` using `fun h => hp.not_isUnit (hc.of_mul_left_left.isUnit_of_dvd h)`. Take `⟨τ, hτ⟩` from `GlobalTheory.NT.exists_isFrob L v`. Use `⟨τ * σ, fun χ => ?_⟩` and prove the remaining obligations. Establish `h1` using `GlobalTheory.NT.Model.heckeIdeal_prime L χ v`. Rewrite `h1` using `[heckeVal_of_unramIn L χ (hR.1 v hv) hτ]`.

Rewrite using `[GlobalTheory.NT.Model.heckeIdeal_mul L χ hp.ne_zero hI0, hσ]`. Express the relevant statement in the definitionally equal form `heckeIdeal L χ v.asIdeal * _ = _`. Rewrite using `[h1]`. Simplify using the standard rewrite rules.
-/
theorem exists_symbol [IsGalois K L] (hR : IsRay L 𝔮) (I : Ideal (𝓞 K)) :
    I ≠ ⊥ → IsCoprime I 𝔮 → ∃ σ : L ≃ₐ[K] L, ∀ χ : (L ≃ₐ[K] L) →* ℂˣ, heckeIdeal L χ I = (χ σ : ℂˣ) := by
  induction I using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => exact fun h => absurd rfl h
  | h₂ I hI =>
    intro _ _
    obtain rfl : I = 1 := by rw [Ideal.one_eq_top]; exact Ideal.isUnit_iff.1 hI
    exact ⟨1, fun χ => by rw [GlobalTheory.NT.Model.heckeIdeal_top]; simp⟩
  | h₃ I p hI0 hp ih =>
    intro _ hc
    obtain ⟨σ, hσ⟩ := ih hI0 hc.of_mul_left_right
    let v : HeightOneSpectrum (𝓞 K) := ⟨p, Ideal.isPrime_of_prime hp, hp.ne_zero⟩
    have hv : ¬ v.asIdeal ∣ 𝔮 := fun h => hp.not_isUnit (hc.of_mul_left_left.isUnit_of_dvd h)
    obtain ⟨τ, hτ⟩ := GlobalTheory.NT.exists_isFrob L v
    refine ⟨τ * σ, fun χ => ?_⟩
    have h1 := GlobalTheory.NT.Model.heckeIdeal_prime L χ v
    rw [heckeVal_of_unramIn L χ (hR.1 v hv) hτ] at h1
    rw [GlobalTheory.NT.Model.heckeIdeal_mul L χ hp.ne_zero hI0, hσ]
    change heckeIdeal L χ v.asIdeal * _ = _
    rw [h1]; simp

/- English proof (translation)
Introduce `K L _ _ _ _ _ 𝔮 h𝔮 h`. Use `h.1` as an intermediate fact. Establish `hR : IsRay L 𝔮` using `h.2`. Set `S : Submonoid ((L ≃ₐ[K] L) × ClassGroup (𝓞 K))` to `{ carrier := {x | ∃ I : (Ideal (𝓞 K))⁰, IsCoprime (I : Ideal (𝓞 K)) 𝔮 ∧ ClassGroup.mk0 I = x.2 ∧ ∀ χ : (L ≃ₐ[K] L) →* ℂˣ, heckeIdeal L χ I = (χ x.1 : ℂˣ)} one_mem' := ⟨1, isCoprime_one_left, map_one _, fun χ => by`. Rewrite using `[OneMemClass.coe_one, GlobalTheory.NT.Model.heckeIdeal_top]`.

Use the proof step `simp⟩`. Use the proof step `mul_mem' := by`. Introduce and unpack `x y ⟨I, hI, hIc, hx⟩ ⟨J, hJ, hJc, hy⟩`. Use `⟨I * J, hI.mul_left hJ, by rw [map_mul, hIc, hJc]; rfl, fun χ => ?_⟩` and prove the remaining obligations. Rewrite using `[Submonoid.coe_mul, GlobalTheory.NT.Model.heckeIdeal_mul L χ (nonZeroDivisors.coe_ne_zero I) (nonZeroDivisors.coe_ne_zero J), hx, hy]`.

Simplify using `}`. Set `H : Subgroup ((L ≃ₐ[K] L) × ClassGroup (𝓞 K))` to `{ S with inv_mem' := by`. Introduce `x hx`. Establish `: x⁻¹ = x ^ (orderOf x - 1)`. Rewrite using `[inv_eq_iff_mul_eq_one, ← pow_succ', Nat.sub_add_cancel (orderOf_pos x), pow_orderOf_eq_one]`.

Rewrite using `[this]`. Conclude with `S.pow_mem hx _ }`. Establish `h1 : Function.Bijective ((MonoidHom.fst _ _).comp H.subtype)`. Use `⟨(injective_iff_map_eq_one _).2 ?_, fun σ => ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨⟨σ, c⟩, I, hI, hIc, hx⟩ hσ`.

Take `rfl : σ = 1` from `hσ`. Take `⟨α, β, hp, he⟩` from `(hR.2.2 I (nonZeroDivisors.coe_ne_zero I) hI).1 fun χ => by simpa using hx χ`. Establish `hc : ClassGroup.mk0 I = ClassGroup.mk0 1` using `ClassGroup.mk0_eq_mk0_iff.2 ⟨β, α, hp.2.1, hp.1, by simpa [mul_comm] using he⟩`. Rewrite `hc` using `[map_one]`. Take `rfl : c = 1` from `hIc.symm.trans hc`.

Both sides reduce to the same expression. Take `⟨I, hI0, hI, hx⟩` from `RayDegree.exists_ideal hR σ`. Set `J : (Ideal (𝓞 K))⁰` to `⟨I, mem_nonZeroDivisors_of_ne_zero hI0⟩`. Conclude with `⟨⟨(σ, ClassGroup.mk0 J), J, hI, rfl, hx⟩, rfl⟩`. Establish `h2 : Function.Surjective ((MonoidHom.snd _ _).comp H.subtype)` using `fun c => by`.

Take `⟨I, hI, hc⟩` from `classGroup_exists_integral_ideal_coprime h𝔮 c`. Take `⟨σ, hσ⟩` from `exists_symbol hR I (nonZeroDivisors.coe_ne_zero I) hI`. Conclude with `⟨⟨(σ, c), I, hI, hc, hσ⟩, rfl⟩`. Rewrite using `[← IsGalois.card_aut_eq_finrank, ← Nat.card_eq_of_bijective _ h1, classNumber, ← Nat.card_eq_fintype_card]`. Conclude with `Subgroup.card_dvd_of_surjective _ h2`.
-/
theorem classNumber_dvd_finrank : ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (𝔮 : Ideal (𝓞 K)), 𝔮 ≠ ⊥ → IsRayField K L 𝔮 → classNumber K ∣ Module.finrank K L := by
  intro K L _ _ _ _ _ 𝔮 h𝔮 h
  have := h.1
  have hR : IsRay L 𝔮 := h.2
  let S : Submonoid ((L ≃ₐ[K] L) × ClassGroup (𝓞 K)) :=
    { carrier := {x | ∃ I : (Ideal (𝓞 K))⁰, IsCoprime (I : Ideal (𝓞 K)) 𝔮 ∧ ClassGroup.mk0 I = x.2 ∧
        ∀ χ : (L ≃ₐ[K] L) →* ℂˣ, heckeIdeal L χ I = (χ x.1 : ℂˣ)}
      one_mem' := ⟨1, isCoprime_one_left, map_one _, fun χ => by
        rw [OneMemClass.coe_one, GlobalTheory.NT.Model.heckeIdeal_top]; simp⟩
      mul_mem' := by
        rintro x y ⟨I, hI, hIc, hx⟩ ⟨J, hJ, hJc, hy⟩
        refine ⟨I * J, hI.mul_left hJ, by rw [map_mul, hIc, hJc]; rfl, fun χ => ?_⟩
        rw [Submonoid.coe_mul, GlobalTheory.NT.Model.heckeIdeal_mul L χ (nonZeroDivisors.coe_ne_zero I)
          (nonZeroDivisors.coe_ne_zero J), hx, hy]; simp }
  let H : Subgroup ((L ≃ₐ[K] L) × ClassGroup (𝓞 K)) :=
    { S with
      inv_mem' := by
        intro x hx
        have : x⁻¹ = x ^ (orderOf x - 1) := by
          rw [inv_eq_iff_mul_eq_one, ← pow_succ', Nat.sub_add_cancel (orderOf_pos x), pow_orderOf_eq_one]
        rw [this]
        exact S.pow_mem hx _ }
  have h1 : Function.Bijective ((MonoidHom.fst _ _).comp H.subtype) := by
    refine ⟨(injective_iff_map_eq_one _).2 ?_, fun σ => ?_⟩
    · rintro ⟨⟨σ, c⟩, I, hI, hIc, hx⟩ hσ
      obtain rfl : σ = 1 := hσ
      obtain ⟨α, β, hp, he⟩ := (hR.2.2 I (nonZeroDivisors.coe_ne_zero I) hI).1 fun χ => by simpa using hx χ
      have hc : ClassGroup.mk0 I = ClassGroup.mk0 1 :=
        ClassGroup.mk0_eq_mk0_iff.2 ⟨β, α, hp.2.1, hp.1, by simpa [mul_comm] using he⟩
      rw [map_one] at hc
      obtain rfl : c = 1 := hIc.symm.trans hc
      rfl
    · obtain ⟨I, hI0, hI, hx⟩ := RayDegree.exists_ideal hR σ
      let J : (Ideal (𝓞 K))⁰ := ⟨I, mem_nonZeroDivisors_of_ne_zero hI0⟩
      exact ⟨⟨(σ, ClassGroup.mk0 J), J, hI, rfl, hx⟩, rfl⟩
  have h2 : Function.Surjective ((MonoidHom.snd _ _).comp H.subtype) := fun c => by
    obtain ⟨I, hI, hc⟩ := classGroup_exists_integral_ideal_coprime h𝔮 c
    obtain ⟨σ, hσ⟩ := exists_symbol hR I (nonZeroDivisors.coe_ne_zero I) hI
    exact ⟨⟨(σ, c), I, hI, hc, hσ⟩, rfl⟩
  rw [← IsGalois.card_aut_eq_finrank, ← Nat.card_eq_of_bijective _ h1, classNumber, ← Nat.card_eq_fintype_card]
  exact Subgroup.card_dvd_of_surjective _ h2

end GlobalTheory.Mem.ClassDvd

end
