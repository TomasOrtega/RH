import Mathlib
import ReciprocityTheory.GaloisValuations.Global
import Formalism.LocalToGlobal.NormalizedHeckeFactors.RingHomOfBaseOrderToFraction
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RootEqOfClose
import ReciprocityTheory.ClassFieldTheory.GlobalClassField.IsFrobAtMulOfMemInertiaGroup
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteGaloisInertiaLiftsAbsoluteInertiaRat
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemOfInteger
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2

namespace GlobalTheory.TameSurj

open Ideal in
/- English proof (translation)
Introduce `E L _ _ _ _ _ P Q _ _ m ϖ hϖ2 π hπQ hπm`. Break down `Nat.eq_zero_or_pos m with rfl | hm` into its components or cases. Conclude with `Nat.zero_le _`. Establish `hQ0 : Q ≠ ⊥` using `Ideal.ne_bot_of_liesOver_of_ne_bot P.ne_bot Q`. Use `haveI : Q.IsMaximal := (inferInstance : Q.IsPrime).isMaximal hQ0`.

Establish `hunder : ∀ y : 𝓞 E, algebraMap (𝓞 E) (𝓞 L) y ∈ Q ↔ y ∈ P.asIdeal` using `fun y => by`. Rewrite using `[Ideal.over_def Q P.asIdeal, Ideal.mem_under]`. Establish `hϖP : ϖ ∈ P.asIdeal` using `(hunder ϖ).mp (hπm ▸ Q.pow_mem_of_mem hπQ m hm)`. Take `⟨J, hJ⟩` from `Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hϖP)`. Establish `hJP : ¬ J ≤ P.asIdeal`.

Introduce `h`. Apply `hϖ2` to reduce the goal to its premises. Establish `h2 : span {ϖ} ≤ P.asIdeal ^ 2`. Rewrite using `[hJ, pow_two]`. Conclude with `Ideal.mul_mono_right h`.

Conclude with `h2 (Ideal.mem_span_singleton_self ϖ)`. Take `⟨s, hsJ, hsP⟩` from `SetLike.not_le_iff_exists.mp hJP`. Establish `hprim : (Q ^ m).IsPrimary`. Apply `Ideal.isPrimary_of_isMaximal_radical` to reduce the goal to its premises. Rewrite using `[Ideal.radical_pow Q hm.ne', (inferInstance : Q.IsPrime).radical]`.

Use `infer_instance`. Establish `hle : P.asIdeal.map (algebraMap (𝓞 E) (𝓞 L)) ≤ Q ^ m`. Rewrite using `[Ideal.map_le_iff_le_comap]`. Introduce `x hx`. Rewrite using `[Ideal.mem_comap]`.

Establish `hxs : x * s ∈ span {ϖ}` using `hJ ▸ Ideal.mul_mem_mul hx hsJ`. Take `⟨c, hc⟩` from `Ideal.mem_span_singleton'.mp hxs`. Establish `hmem : algebraMap (𝓞 E) (𝓞 L) x * algebraMap (𝓞 E) (𝓞 L) s ∈ Q ^ m`. Rewrite using `[← map_mul, ← hc, map_mul, ← hπm]`. Conclude with `Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow hπQ m)`.

Break down `(Ideal.isPrimary_iff.mp hprim).2 hmem with h | h` into its components or cases. Conclude with `h`. It suffices to derive a contradiction. Rewrite `h` using `[Ideal.radical_pow Q hm.ne', (inferInstance : Q.IsPrime).radical]`. Conclude with `hsP ((hunder s).mp h)`.

Establish `hp : P.asIdeal.map (algebraMap (𝓞 E) (𝓞 L)) ≠ ⊥` using `Ideal.map_ne_bot_of_ne_bot P.ne_bot`. Rewrite using `[Ideal.IsDedekindDomain.ramificationIdx_eq_multiplicity P.asIdeal Q hp]`. Apply `FiniteMultiplicity.le_multiplicity_of_pow_dvd` to reduce the goal to its premises. Conclude with `FiniteMultiplicity.of_not_isUnit (Ideal.isUnit_iff.not.mpr (inferInstance : Q.IsPrime).ne_top) hp`. Conclude with `Ideal.dvd_iff_le.mpr hle`.
-/
theorem ram_le : ∀ {E L : Type} [Field E] [NumberField E] [Field L] [NumberField L] [Algebra E L] (P : HeightOneSpectrum (𝓞 E)) (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver P.asIdeal] (m : ℕ) (ϖ : 𝓞 E), ϖ ∉ P.asIdeal ^ 2 → ∀ π : 𝓞 L, π ∈ Q → π ^ m = algebraMap (𝓞 E) (𝓞 L) ϖ → m ≤ Q.ramificationIdx (𝓞 E) := by
  intro E L _ _ _ _ _ P Q _ _ m ϖ hϖ2 π hπQ hπm
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact Nat.zero_le _
  have hQ0 : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot P.ne_bot Q
  haveI : Q.IsMaximal := (inferInstance : Q.IsPrime).isMaximal hQ0
  have hunder : ∀ y : 𝓞 E, algebraMap (𝓞 E) (𝓞 L) y ∈ Q ↔ y ∈ P.asIdeal := fun y => by
    rw [Ideal.over_def Q P.asIdeal, Ideal.mem_under]
  have hϖP : ϖ ∈ P.asIdeal := (hunder ϖ).mp (hπm ▸ Q.pow_mem_of_mem hπQ m hm)
  obtain ⟨J, hJ⟩ := Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hϖP)
  have hJP : ¬ J ≤ P.asIdeal := by
    intro h
    apply hϖ2
    have h2 : span {ϖ} ≤ P.asIdeal ^ 2 := by
      rw [hJ, pow_two]
      exact Ideal.mul_mono_right h
    exact h2 (Ideal.mem_span_singleton_self ϖ)
  obtain ⟨s, hsJ, hsP⟩ := SetLike.not_le_iff_exists.mp hJP
  have hprim : (Q ^ m).IsPrimary := by
    apply Ideal.isPrimary_of_isMaximal_radical
    rw [Ideal.radical_pow Q hm.ne', (inferInstance : Q.IsPrime).radical]
    infer_instance
  have hle : P.asIdeal.map (algebraMap (𝓞 E) (𝓞 L)) ≤ Q ^ m := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap]
    have hxs : x * s ∈ span {ϖ} := hJ ▸ Ideal.mul_mem_mul hx hsJ
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hxs
    have hmem : algebraMap (𝓞 E) (𝓞 L) x * algebraMap (𝓞 E) (𝓞 L) s ∈ Q ^ m := by
      rw [← map_mul, ← hc, map_mul, ← hπm]
      exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow hπQ m)
    rcases (Ideal.isPrimary_iff.mp hprim).2 hmem with h | h
    · exact h
    · exfalso
      rw [Ideal.radical_pow Q hm.ne', (inferInstance : Q.IsPrime).radical] at h
      exact hsP ((hunder s).mp h)
  have hp : P.asIdeal.map (algebraMap (𝓞 E) (𝓞 L)) ≠ ⊥ := Ideal.map_ne_bot_of_ne_bot P.ne_bot
  rw [Ideal.IsDedekindDomain.ramificationIdx_eq_multiplicity P.asIdeal Q hp]
  apply FiniteMultiplicity.le_multiplicity_of_pow_dvd
  · exact FiniteMultiplicity.of_not_isUnit (Ideal.isUnit_iff.not.mpr (inferInstance : Q.IsPrime).ne_top) hp
  · exact Ideal.dvd_iff_le.mpr hle

variable {Ω : Type} [Field Ω]

/- English proof (translation)
The claim follows from `(A.valuation_le_one_iff _).mpr (mem_of_isIntegral_int A (x.isIntegral_coe.map (algebraMap L Ω).toIntAlgHom))`.
-/
theorem val_int_le {L : Type} [Field L] [NumberField L] [Algebra L Ω] (A : ValuationSubring Ω) (x : 𝓞 L) :
    A.valuation (algebraMap L Ω (x : L)) ≤ 1 :=
  (A.valuation_le_one_iff _).mpr (mem_of_isIntegral_int A (x.isIntegral_coe.map (algebraMap L Ω).toIntAlgHom))

def primeOf {L : Type} [Field L] [NumberField L] [Algebra L Ω] (A : ValuationSubring Ω) : Ideal (𝓞 L) where
  carrier := {x | A.valuation (algebraMap L Ω (x : L)) < 1}
  add_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq, map_add] at ha hb ⊢
    exact Valuation.map_add_lt _ ha hb
  zero_mem' := by simp
  smul_mem' c b hb := by
    simp only [Set.mem_setOf_eq, smul_eq_mul, map_mul, Valuation.map_mul] at hb ⊢
    calc A.valuation (algebraMap L Ω (c : L)) * A.valuation (algebraMap L Ω (b : L))
        ≤ 1 * A.valuation (algebraMap L Ω (b : L)) := mul_le_mul_left (val_int_le A c) _
      _ < 1 := by rw [one_mul]; exact hb

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_primeOf {L : Type} [Field L] [NumberField L] [Algebra L Ω] {A : ValuationSubring Ω} {x : 𝓞 L} :
    x ∈ primeOf (L := L) A ↔ A.valuation (algebraMap L Ω (x : L)) < 1 := Iff.rfl

/- English proof (translation)
The claim follows from `_root_.GlobalTheory.DenominatorExists.exists_denominator`.
-/
theorem den : ∀ {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] (A : ValuationSubring Ω) (x : L), A.valuation (algebraMap L Ω x) ≤ 1 → ∃ s t : 𝓞 L, A.valuation (algebraMap L Ω (s : L)) = 1 ∧ (s : L) * x = t :=
  _root_.GlobalTheory.DenominatorExists.exists_denominator

instance isPrime_primeOf {L : Type} [Field L] [NumberField L] [Algebra L Ω] (A : ValuationSubring Ω) :
    (primeOf (L := L) A).IsPrime where
  ne_top' h := by
    have : (1 : 𝓞 L) ∈ primeOf (L := L) A := h ▸ Submodule.mem_top
    rw [mem_primeOf] at this
    simp at this
  mem_or_mem' {a b} hab := by
    rw [mem_primeOf, mem_primeOf]
    rw [mem_primeOf] at hab
    by_contra hn
    simp only [not_or, not_lt] at hn
    have ha := le_antisymm (val_int_le A a) hn.1
    have hb := le_antisymm (val_int_le A b) hn.2
    simp only [map_mul, Valuation.map_mul, ha, hb, one_mul] at hab
    exact lt_irrefl _ hab

open ReciprocityTheory.DiscreteGroups.GlobalClassField in
/- English proof (translation)
Establish `h` using `mem_inertiaGroup.mp hτ x`. Rewrite `h` using `[mem_primeOf]`. Establish `e : ((galRestrict (𝓞 E) E L (𝓞 L) τ x - x : 𝓞 L) : L) = τ x - x`. Express the relevant statement in the definitionally equal form `algebraMap (𝓞 L) L (_ - x) = _`. Rewrite using `[map_sub, algebraMap_galRestrict_apply]`.

Rewrite `h` using `[e, map_sub]`. Conclude with `h`.
-/
theorem inert_val {E L : Type} [Field E] [NumberField E] [Field L] [NumberField L] [Algebra E L] [Algebra L Ω]
    {A : ValuationSubring Ω} {τ : L ≃ₐ[E] L} (hτ : τ ∈ inertiaGroup E L (primeOf (L := L) A)) (x : 𝓞 L) :
    A.valuation (algebraMap L Ω (τ x) - algebraMap L Ω x) < 1 := by
  have h := mem_inertiaGroup.mp hτ x
  rw [mem_primeOf] at h
  have e : ((galRestrict (𝓞 E) E L (𝓞 L) τ x - x : 𝓞 L) : L) = τ x - x := by
    change algebraMap (𝓞 L) L (_ - x) = _
    rw [map_sub, algebraMap_galRestrict_apply]
  rw [e, map_sub] at h
  exact h

open ReciprocityTheory.DiscreteGroups.GlobalClassField in
/- English proof (translation)
Take `⟨s, t, hs1, e⟩` from `den A x hx`. Establish `hs` using `inert_val hτ s`. Establish `ht` using `inert_val hτ t`. Establish `hτs : A.valuation (algebraMap L Ω (τ s)) = 1`. Establish `e2 : algebraMap L Ω (τ s) = algebraMap L Ω s + (algebraMap L Ω (τ s) - algebraMap L Ω s)` using `by ring`.

Rewrite using `[e2, Valuation.map_add_eq_of_lt_left, hs1]`. Rewrite using `[hs1]`. Conclude with `hs`. Establish `he' : τ s * τ x = τ t` using `by rw [← map_mul, e]`. Establish `key : algebraMap L Ω (τ s) * (algebraMap L Ω (τ x) - algebraMap L Ω x) = (algebraMap L Ω (τ t) - algebraMap L Ω t) + algebraMap L Ω x * (algebraMap L Ω s - algebraMap L Ω (τ s))`.

Rewrite using `[← he', ← e]`. Simplify using `only [map_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `hv : A.valuation (algebraMap L Ω (τ s) * (algebraMap L Ω (τ x) - algebraMap L Ω x)) < 1`. Rewrite using `[key]`.

Use `Valuation.map_add_lt _ ht ?_` and prove the remaining obligations. Rewrite using `[Valuation.map_mul, Valuation.map_sub_swap]`. Combine the equalities or inequalities in the displayed calculation. Rewrite `hv` using `[Valuation.map_mul, hτs, one_mul]`. Then use the resulting hypothesis.
-/
theorem inert_val_of_le {E L : Type} [Field E] [NumberField E] [Field L] [NumberField L] [Algebra E L] [Algebra L Ω]
    {A : ValuationSubring Ω} {τ : L ≃ₐ[E] L} (hτ : τ ∈ inertiaGroup E L (primeOf (L := L) A)) (x : L)
    (hx : A.valuation (algebraMap L Ω x) ≤ 1) :
    A.valuation (algebraMap L Ω (τ x) - algebraMap L Ω x) < 1 := by
  obtain ⟨s, t, hs1, e⟩ := den A x hx
  have hs := inert_val hτ s
  have ht := inert_val hτ t
  have hτs : A.valuation (algebraMap L Ω (τ s)) = 1 := by
    have e2 : algebraMap L Ω (τ s) = algebraMap L Ω s + (algebraMap L Ω (τ s) - algebraMap L Ω s) := by ring
    rw [e2, Valuation.map_add_eq_of_lt_left, hs1]
    rw [hs1]; exact hs
  have he' : τ s * τ x = τ t := by rw [← map_mul, e]
  have key : algebraMap L Ω (τ s) * (algebraMap L Ω (τ x) - algebraMap L Ω x) =
      (algebraMap L Ω (τ t) - algebraMap L Ω t) + algebraMap L Ω x * (algebraMap L Ω s - algebraMap L Ω (τ s)) := by
    rw [← he', ← e]; simp only [map_mul]; ring
  have hv : A.valuation (algebraMap L Ω (τ s) * (algebraMap L Ω (τ x) - algebraMap L Ω x)) < 1 := by
    rw [key]
    refine Valuation.map_add_lt _ ht ?_
    rw [Valuation.map_mul, Valuation.map_sub_swap]
    calc A.valuation (algebraMap L Ω x) * A.valuation (algebraMap L Ω (τ s) - algebraMap L Ω s)
        ≤ 1 * A.valuation (algebraMap L Ω (τ s) - algebraMap L Ω s) := mul_le_mul_left hx _
      _ < 1 := by rw [one_mul]; exact hs
  rwa [Valuation.map_mul, hτs, one_mul] at hv

open ReciprocityTheory.DiscreteGroups.GlobalClassField in
/- English proof (translation)
Establish `hm0 : m ≠ 0` using `by rintro rfl; exact hm (by simp)`. Establish `hint : IsIntegral ℤ η` using `IsIntegral.of_pow (Nat.pos_of_ne_zero hm0) (by rw [hη]; exact isIntegral_one)`. Establish `h` using `inert_val hτ (⟨η, hint⟩ : 𝓞 L)`. Apply `(algebraMap L Ω).injective` to reduce the goal to its premises. Use `eq_of_pow_eq_one A hm ?_ ?_ h` and prove the remaining obligations.

Rewrite using `[← map_pow, ← map_pow, hη, map_one, map_one]`. Rewrite using `[← map_pow, hη, map_one]`.
-/
theorem inert_fix_root {E L : Type} [Field E] [NumberField E] [Field L] [NumberField L] [Algebra E L] [Algebra L Ω]
    {A : ValuationSubring Ω} {τ : L ≃ₐ[E] L} (hτ : τ ∈ inertiaGroup E L (primeOf (L := L) A)) (m : ℕ)
    (hm : ¬ A.valuation (m : Ω) < 1) {η : L} (hη : η ^ m = 1) : τ η = η := by
  have hm0 : m ≠ 0 := by rintro rfl; exact hm (by simp)
  have hint : IsIntegral ℤ η := IsIntegral.of_pow (Nat.pos_of_ne_zero hm0) (by rw [hη]; exact isIntegral_one)
  have h := inert_val hτ (⟨η, hint⟩ : 𝓞 L)
  apply (algebraMap L Ω).injective
  refine eq_of_pow_eq_one A hm ?_ ?_ h
  · rw [← map_pow, ← map_pow, hη, map_one, map_one]
  · rw [← map_pow, hη, map_one]

open ReciprocityTheory.DiscreteGroups.GlobalClassField in
/- English proof (translation)
Establish `hm0 : m ≠ 0` using `by rintro rfl; exact hm (by simp)`. Establish `hmpos : 0 < m` using `Nat.pos_of_ne_zero hm0`. Establish `hπint : IsIntegral ℤ π` using `IsIntegral.of_pow hmpos (by`. Rewrite using `[hπ]`. Conclude with `ϖ.isIntegral_coe.map (algebraMap E L).toIntAlgHom)`.

Set `πO : 𝓞 L` to `⟨π, hπint⟩`. Establish `hπQ : πO ∈ primeOf (L` using `L) A := hπv`. Establish `hπm : πO ^ m = algebraMap (𝓞 E) (𝓞 L) ϖ`. Apply `RingOfIntegers.ext` to reduce the goal to its premises. Use `show π ^ m = algebraMap (𝓞 L) L (algebraMap (𝓞 E) (𝓞 L) ϖ)`.

Rewrite using `[← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (𝓞 E) E L, hπ]`. Establish `hcard : m ≤ Nat.card (inertiaGroup E L (primeOf (L` using `L) A)) := by`. Rewrite using `[card_inertiaGroup P (primeOf (L := L) A)]`. Conclude with `ram_le P (primeOf (L := L) A) m ϖ hϖ2 πO hπQ hπm`. Set `S : Finset L` to `Polynomial.nthRootsFinset m (1 : L)`.

Establish `hS : ∀ η : L, η ∈ S ↔ η ^ m = 1` using `fun η => Polynomial.mem_nthRootsFinset hmpos 1`. Establish `hScard : Nat.card S ≤ m`. Rewrite using `[Nat.card_eq_fintype_card, Fintype.card_coe]`. Conclude with `(Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots m (1 : L))`. Establish `hquot : ∀ τ : L ≃ₐ[E] L, (τ π / π) ^ m = 1` using `fun τ => by`.

Rewrite using `[div_pow, ← map_pow, hπ, AlgEquiv.commutes, div_self]`. Rewrite using `[← hπ]`. Conclude with `pow_ne_zero _ hπ0`. Set `φ : inertiaGroup E L (primeOf (L` to `L) A) → S := fun τ => ⟨(τ : L ≃ₐ[E] L) π / π, (hS _).2 (hquot τ)⟩`. Establish `hinj : Function.Injective φ`.

Introduce `τ₁ τ₂ h`. Establish `h1 : (τ₁ : L ≃ₐ[E] L) π = (τ₂ : L ≃ₐ[E] L) π`. Use `congrArg Subtype.val h` as an intermediate fact. Simplify using `only [φ] at this`. Conclude with `(div_left_inj' hπ0).mp this`.

Establish `key` using `hgen ((τ₂ : L ≃ₐ[E] L)⁻¹ * τ₁) (by`. Rewrite using `[AlgEquiv.mul_apply, h1]`. Conclude with `(τ₂ : L ≃ₐ[E] L).symm_apply_apply π) (fun η hη => by`. Rewrite using `[AlgEquiv.mul_apply, inert_fix_root τ₁.2 m hm hη]`. Conclude with `inert_fix_root (inv_mem τ₂.2) m hm hη)`.

Apply `Subtype.ext` to reduce the goal to its premises. Rewrite `key` using `[inv_mul_eq_one]`. Conclude with `key.symm`. Establish `hbij` using `hinj.bijective_of_nat_card_le (hScard.trans hcard)`. Take `⟨τ, hτ⟩` from `hbij.2 ⟨ζ, (hS ζ).2 hζ⟩`.

Use `⟨τ, τ.2, ?_⟩` and prove the remaining obligations. Use `congrArg Subtype.val hτ` as an intermediate fact. Simplify using `only [φ] at this`. Rewrite using `[← this, div_mul_cancel₀ _ hπ0]`.
-/
theorem exists_tau {E L : Type} [Field E] [NumberField E] [Field L] [NumberField L] [Algebra E L] [IsGalois E L]
    [Algebra L Ω] (A : ValuationSubring Ω) (P : HeightOneSpectrum (𝓞 E))
    [(primeOf (L := L) A).LiesOver P.asIdeal]
    (m : ℕ) (hm : ¬ A.valuation (m : Ω) < 1) (ϖ : 𝓞 E) (hϖ2 : ϖ ∉ P.asIdeal ^ 2) (π : L)
    (hπ : π ^ m = algebraMap E L ϖ) (hπ0 : π ≠ 0) (hπv : A.valuation (algebraMap L Ω π) < 1)
    (hgen : ∀ τ : L ≃ₐ[E] L, τ π = π → (∀ η : L, η ^ m = 1 → τ η = η) → τ = 1)
    (ζ : L) (hζ : ζ ^ m = 1) :
    ∃ τ ∈ inertiaGroup E L (primeOf (L := L) A), τ π = ζ * π := by
  classical
  have hm0 : m ≠ 0 := by rintro rfl; exact hm (by simp)
  have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
  have hπint : IsIntegral ℤ π := IsIntegral.of_pow hmpos (by
    rw [hπ]; exact ϖ.isIntegral_coe.map (algebraMap E L).toIntAlgHom)
  let πO : 𝓞 L := ⟨π, hπint⟩
  have hπQ : πO ∈ primeOf (L := L) A := hπv
  have hπm : πO ^ m = algebraMap (𝓞 E) (𝓞 L) ϖ := by
    apply RingOfIntegers.ext
    show π ^ m = algebraMap (𝓞 L) L (algebraMap (𝓞 E) (𝓞 L) ϖ)
    rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (𝓞 E) E L, hπ]
  have hcard : m ≤ Nat.card (inertiaGroup E L (primeOf (L := L) A)) := by
    rw [card_inertiaGroup P (primeOf (L := L) A)]
    exact ram_le P (primeOf (L := L) A) m ϖ hϖ2 πO hπQ hπm
  let S : Finset L := Polynomial.nthRootsFinset m (1 : L)
  have hS : ∀ η : L, η ∈ S ↔ η ^ m = 1 := fun η => Polynomial.mem_nthRootsFinset hmpos 1
  have hScard : Nat.card S ≤ m := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    exact (Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots m (1 : L))
  have hquot : ∀ τ : L ≃ₐ[E] L, (τ π / π) ^ m = 1 := fun τ => by
    rw [div_pow, ← map_pow, hπ, AlgEquiv.commutes, div_self]
    rw [← hπ]; exact pow_ne_zero _ hπ0
  let φ : inertiaGroup E L (primeOf (L := L) A) → S := fun τ => ⟨(τ : L ≃ₐ[E] L) π / π, (hS _).2 (hquot τ)⟩
  have hinj : Function.Injective φ := by
    intro τ₁ τ₂ h
    have h1 : (τ₁ : L ≃ₐ[E] L) π = (τ₂ : L ≃ₐ[E] L) π := by
      have := congrArg Subtype.val h
      simp only [φ] at this
      exact (div_left_inj' hπ0).mp this
    have key := hgen ((τ₂ : L ≃ₐ[E] L)⁻¹ * τ₁) (by
        rw [AlgEquiv.mul_apply, h1]
        exact (τ₂ : L ≃ₐ[E] L).symm_apply_apply π) (fun η hη => by
        rw [AlgEquiv.mul_apply, inert_fix_root τ₁.2 m hm hη]
        exact inert_fix_root (inv_mem τ₂.2) m hm hη)
    apply Subtype.ext
    rw [inv_mul_eq_one] at key
    exact key.symm
  have hbij := hinj.bijective_of_nat_card_le (hScard.trans hcard)
  obtain ⟨τ, hτ⟩ := hbij.2 ⟨ζ, (hS ζ).2 hζ⟩
  refine ⟨τ, τ.2, ?_⟩
  have := congrArg Subtype.val hτ
  simp only [φ] at this
  rw [← this, div_mul_cancel₀ _ hπ0]

open Polynomial in
/- English proof (translation)
Introduce `E Ω _ _ _ _ _ A P hA m hm hmP ϖ hϖ hϖ2 π hπ ζ hζ`. Use `haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E`. Use `haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective`. Establish `hm0 : m ≠ 0` using `hm.ne'`. Establish `hmv : ¬ A.valuation (m : Ω) < 1`.

Use `(hA (m : 𝓞 E)).not.mpr hmP` as an intermediate fact. Simplify using `using this`. Establish `hϖ0 : (ϖ : E) ≠ 0`. Introduce `h`. Apply `hϖ2` to reduce the goal to its premises.

Rewrite using `[show ϖ = 0 from RingOfIntegers.ext (by simpa using h)]`. Conclude with `zero_mem _`. Set `f : E[X]` to `X ^ m - C (ϖ : E)`. Establish `hf0 : f ≠ 0` using `X_pow_sub_C_ne_zero hm _`. Set `M : IntermediateField E Ω` to `IntermediateField.adjoin E (f.rootSet Ω)`.

Use `haveI : IsSplittingField E M f := IntermediateField.adjoin_rootSet_isSplittingField (IsAlgClosed.splits _)`. Use `haveI : FiniteDimensional E M := IsSplittingField.finiteDimensional M f`. Use `haveI : IsGalois E M := IsGalois.of_separable_splitting_field (p := f) (separable_X_pow_sub_C _ (by exact_mod_cast hm0) hϖ0)`. Use `haveI : NumberField M := NumberField.of_module_finite E M`. Establish `hroot : ∀ r : Ω, r ^ m = algebraMap E Ω ϖ → r ∈ M` using `fun r hr => IntermediateField.subset_adjoin _ _ (by`.

Rewrite using `[mem_rootSet]`. Conclude with `⟨hf0, by simp [f, hr]⟩)`. Establish `hπ0 : π ≠ 0`. Introduce and unpack `rfl`. Rewrite `hπ` using `[zero_pow hm0, eq_comm, map_eq_zero_iff _ (algebraMap E Ω).injective]`.

Conclude with `hϖ0 hπ`. Set `πM : M` to `⟨π, hroot π hπ⟩`. Establish `hζM : ζ ∈ M`. Establish `h1 : ζ * π ∈ M` using `hroot _ (by rw [mul_pow, hζ, one_mul, hπ])`. Use `M.div_mem h1 (hroot π hπ)` as an intermediate fact.

Rewrite `this` using `[mul_div_cancel_right₀ _ hπ0]`. Then use the resulting hypothesis. Set `ζM : M` to `⟨ζ, hζM⟩`. Use `haveI : (primeOf (L := M) A).LiesOver P.asIdeal := by`. Prove the components needed by the constructor for the conclusion. Use extensionality with `x`.

Rewrite using `[Ideal.under_def, Ideal.mem_comap, mem_primeOf, ← hA x]`. Both sides reduce to the same expression. Establish `hπv : A.valuation π < 1`. Assume the negation of the conclusion as `h`. Establish `h1 : 1 ≤ A.valuation π ^ m` using `one_le_pow₀ (not_lt.mp h)`.

Rewrite `h1` using `[← Valuation.map_pow, hπ]`. Conclude with `not_lt.mpr h1 ((hA ϖ).mpr hϖ)`. Establish `hπM : πM ^ m = algebraMap E M ϖ` using `Subtype.ext (by simpa using hπ)`. Establish `hπM0 : πM ≠ 0` using `fun h => hπ0 (congrArg Subtype.val h)`. Establish `hgen : ∀ τ : M ≃ₐ[E] M, τ πM = πM → (∀ η : M, η ^ m = 1 → τ η = η) → τ = 1`.

Introduce `τ h1 h2`. Use extensionality with `⟨x, hx⟩`. Use `show (τ ⟨x, hx⟩ : Ω) = x`. Proceed by induction on `hx using IntermediateField.adjoin_induction with`. Consider the case `mem y hy`.

Rewrite `hy` using `[mem_rootSet]`. Establish `hy' : y ^ m = algebraMap E Ω ϖ`. Use `hy.2` as an intermediate fact. Simplify using `only [f, map_sub, map_pow, aeval_X, aeval_C] at this`. Conclude with `sub_eq_zero.mp this`.

Set `yM : M` to `⟨y, hroot y hy'⟩`. Establish `hη : (yM / πM) ^ m = 1`. Rewrite using `[div_pow, hπM, div_eq_one_iff_eq (by rw [← hπM]; exact pow_ne_zero _ hπM0)]`. Conclude with `Subtype.ext (by simpa using hy')`. Establish `e : yM = (yM / πM) * πM` using `by rw [div_mul_cancel₀ _ hπM0]`.

Express the relevant statement in the definitionally equal form `((τ yM : M) : Ω) = y`. Rewrite using `[e, map_mul, h2 _ hη, h1, ← e]`. Consider the case `algebraMap y`. Use `τ.commutes y` as an intermediate fact. Conclude with `congrArg Subtype.val this`.

Consider the case `add y z hy hz ihy ihz`. Express the relevant statement in the definitionally equal form `((τ ((⟨y, hy⟩ : M) + ⟨z, hz⟩) : M) : Ω) = y + z`. Rewrite using `[map_add, IntermediateField.coe_add, ihy, ihz]`. Consider the case `inv y hy ih`. Express the relevant statement in the definitionally equal form `((τ ((⟨y, hy⟩ : M)⁻¹) : M) : Ω) = y⁻¹`.

Rewrite using `[map_inv₀, IntermediateField.coe_inv, ih]`. Consider the case `mul y z hy hz ihy ihz`. Express the relevant statement in the definitionally equal form `((τ ((⟨y, hy⟩ : M) * ⟨z, hz⟩) : M) : Ω) = y * z`. Rewrite using `[map_mul, IntermediateField.coe_mul, ihy, ihz]`. Establish `hζM1 : ζM ^ m = 1` using `Subtype.ext (by simpa using hζ)`.

Take `⟨τ, hτ, hτπ⟩` from `exists_tau (L := M) A P m hmv ϖ hϖ2 πM hπM hπM0 hπv hgen ζM hζM1`. Take `⟨σ, hσ, hσx⟩` from `GlobalTheory.InertiaLift.exists_mem_Ine_lift A M τ (fun x hx => inert_val_of_le hτ x hx)`. Use `⟨σ, hσ, ?_⟩` and prove the remaining obligations. Use `hσx πM` as an intermediate fact. Rewrite `this` using `[hτπ]`.

Conclude with `this`.
-/
theorem main : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (P : HeightOneSpectrum (𝓞 E)), IsPlaceOver A P → ∀ (m : ℕ), 0 < m → ((m : ℕ) : 𝓞 E) ∉ P.asIdeal → ∀ (ϖ : 𝓞 E), ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 → ∀ π : Ω, π ^ m = algebraMap E Ω (ϖ : E) → ∀ ζ : Ω, ζ ^ m = 1 → ∃ σ ∈ Ine (F := E) A, σ π = ζ * π := by
  intro E Ω _ _ _ _ _ A P hA m hm hmP ϖ hϖ hϖ2 π hπ ζ hζ
  classical
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
  have hm0 : m ≠ 0 := hm.ne'
  have hmv : ¬ A.valuation (m : Ω) < 1 := by
    have := (hA (m : 𝓞 E)).not.mpr hmP
    simpa using this
  have hϖ0 : (ϖ : E) ≠ 0 := by
    intro h
    apply hϖ2
    rw [show ϖ = 0 from RingOfIntegers.ext (by simpa using h)]
    exact zero_mem _
  let f : E[X] := X ^ m - C (ϖ : E)
  have hf0 : f ≠ 0 := X_pow_sub_C_ne_zero hm _
  let M : IntermediateField E Ω := IntermediateField.adjoin E (f.rootSet Ω)
  haveI : IsSplittingField E M f := IntermediateField.adjoin_rootSet_isSplittingField (IsAlgClosed.splits _)
  haveI : FiniteDimensional E M := IsSplittingField.finiteDimensional M f
  haveI : IsGalois E M := IsGalois.of_separable_splitting_field (p := f)
    (separable_X_pow_sub_C _ (by exact_mod_cast hm0) hϖ0)
  haveI : NumberField M := NumberField.of_module_finite E M
  have hroot : ∀ r : Ω, r ^ m = algebraMap E Ω ϖ → r ∈ M := fun r hr =>
    IntermediateField.subset_adjoin _ _ (by
      rw [mem_rootSet]
      exact ⟨hf0, by simp [f, hr]⟩)
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [zero_pow hm0, eq_comm, map_eq_zero_iff _ (algebraMap E Ω).injective] at hπ
    exact hϖ0 hπ
  let πM : M := ⟨π, hroot π hπ⟩
  have hζM : ζ ∈ M := by
    have h1 : ζ * π ∈ M := hroot _ (by rw [mul_pow, hζ, one_mul, hπ])
    have := M.div_mem h1 (hroot π hπ)
    rwa [mul_div_cancel_right₀ _ hπ0] at this
  let ζM : M := ⟨ζ, hζM⟩
  haveI : (primeOf (L := M) A).LiesOver P.asIdeal := by
    constructor
    ext x
    rw [Ideal.under_def, Ideal.mem_comap, mem_primeOf, ← hA x]
    rfl
  have hπv : A.valuation π < 1 := by
    by_contra h
    have h1 : 1 ≤ A.valuation π ^ m := one_le_pow₀ (not_lt.mp h)
    rw [← Valuation.map_pow, hπ] at h1
    exact not_lt.mpr h1 ((hA ϖ).mpr hϖ)
  have hπM : πM ^ m = algebraMap E M ϖ := Subtype.ext (by simpa using hπ)
  have hπM0 : πM ≠ 0 := fun h => hπ0 (congrArg Subtype.val h)
  have hgen : ∀ τ : M ≃ₐ[E] M, τ πM = πM → (∀ η : M, η ^ m = 1 → τ η = η) → τ = 1 := by
    intro τ h1 h2
    ext ⟨x, hx⟩
    show (τ ⟨x, hx⟩ : Ω) = x
    induction hx using IntermediateField.adjoin_induction with
    | mem y hy =>
      rw [mem_rootSet] at hy
      have hy' : y ^ m = algebraMap E Ω ϖ := by
        have := hy.2
        simp only [f, map_sub, map_pow, aeval_X, aeval_C] at this
        exact sub_eq_zero.mp this
      let yM : M := ⟨y, hroot y hy'⟩
      have hη : (yM / πM) ^ m = 1 := by
        rw [div_pow, hπM, div_eq_one_iff_eq (by rw [← hπM]; exact pow_ne_zero _ hπM0)]
        exact Subtype.ext (by simpa using hy')
      have e : yM = (yM / πM) * πM := by rw [div_mul_cancel₀ _ hπM0]
      change ((τ yM : M) : Ω) = y
      rw [e, map_mul, h2 _ hη, h1, ← e]
    | algebraMap y =>
      have := τ.commutes y
      exact congrArg Subtype.val this
    | add y z hy hz ihy ihz =>
      change ((τ ((⟨y, hy⟩ : M) + ⟨z, hz⟩) : M) : Ω) = y + z
      rw [map_add, IntermediateField.coe_add, ihy, ihz]
    | inv y hy ih =>
      change ((τ ((⟨y, hy⟩ : M)⁻¹) : M) : Ω) = y⁻¹
      rw [map_inv₀, IntermediateField.coe_inv, ih]
    | mul y z hy hz ihy ihz =>
      change ((τ ((⟨y, hy⟩ : M) * ⟨z, hz⟩) : M) : Ω) = y * z
      rw [map_mul, IntermediateField.coe_mul, ihy, ihz]
  have hζM1 : ζM ^ m = 1 := Subtype.ext (by simpa using hζ)
  obtain ⟨τ, hτ, hτπ⟩ := exists_tau (L := M) A P m hmv ϖ hϖ2 πM hπM hπM0 hπv hgen ζM hζM1
  obtain ⟨σ, hσ, hσx⟩ := GlobalTheory.InertiaLift.exists_mem_Ine_lift A M τ (fun x hx => inert_val_of_le hτ x hx)
  refine ⟨σ, hσ, ?_⟩
  have := hσx πM
  rw [hτπ] at this
  exact this

end GlobalTheory.TameSurj
