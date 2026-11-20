import Mathlib

namespace GlobalTheory

def FieldCopy (k : Type) : Type := k

instance FieldCopy.instField (k : Type) [h : Field k] : Field (FieldCopy k) := h

instance FieldCopy.instIsAlgClosed (k : Type) [Field k] [h : IsAlgClosed k] :
    IsAlgClosed (FieldCopy k) := h

/- English proof (translation)
Introduce `k _ _ hroot R J α β hker`. Set `eα : MvPolynomial J R →ₐ[R] k` to `MvPolynomial.aeval α`. Set `eβ : MvPolynomial J R →ₐ[R] k` to `MvPolynomial.aeval β`. Set `S : Subalgebra R k` to `eα.range`. Establish `hle : ∀ p ∈ RingHom.ker eα.rangeRestrict, eβ p = 0`.

Introduce `p hp`. Rewrite `hp` using `[RingHom.mem_ker]`. Apply `hker` to reduce the goal to its premises. Use `congrArg Subtype.val hp` as an intermediate fact. Simplify using `using this`.

Set `ψ0 : S →ₐ[R] k` to `(Ideal.Quotient.liftₐ (RingHom.ker eα.rangeRestrict) eβ hle).comp (Ideal.quotientKerAlgEquivOfSurjective (AlgHom.rangeRestrict_surjective eα)).symm.toAlgHom`. Establish `hψ0 : ∀ p, ψ0 (eα.rangeRestrict p) = eβ p`. Introduce `p`. Establish `h1 : (Ideal.quotientKerAlgEquivOfSurjective (AlgHom.rangeRestrict_surjective eα)).symm (eα.rangeRestrict p) = Ideal.Quotient.mk _ p`. Rewrite using `[AlgEquiv.symm_apply_eq]`.

Both sides reduce to the same expression. Simplify using `only [ψ0, AlgHom.comp_apply]`. Use `erw [h1]`. Both sides reduce to the same expression. Set `ψ : S →+* FieldCopy k` to `ψ0.toRingHom`.

Establish `hψinj : Function.Injective ψ`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `s hs`. Assume the negation of the conclusion as `hne`. Establish `hne' : (s : k) ≠ 0` using `fun h => hne (Subtype.ext h)`.

Take `⟨n, hn, hsn⟩` from `hroot _ hne'`. Establish `hsn' : s ^ n = 1` using `Subtype.ext (by simpa using hsn)`. Establish `: ψ s ^ n = 1` using `by rw [← map_pow, hsn', map_one]`. Rewrite `this` using `[hs, zero_pow (by omega)]`. Conclude with `zero_ne_one this`.

Use `letI : Algebra S (FieldCopy k) := ψ.toAlgebra`. Use `haveI : Module.IsTorsionFree S (FieldCopy k) := by`. Use `Module.IsTorsionFree.of_smul_eq_zero fun r m h => ?_` and prove the remaining obligations. Rewrite `h` using `[Algebra.smul_def, mul_eq_zero]`. Break down `h with h | h` into its components or cases.

Use `left`. Conclude with `hψinj (h.trans (map_zero ψ).symm)`. Conclude with `Or.inr h`. Use `haveI : Algebra.IsIntegral S k := by`. Prove the components needed by the constructor for the conclusion.

Introduce `x`. Distinguish the cases in `hx : x = 0`. Rewrite using `[hx]`. Conclude with `isIntegral_zero`. Take `⟨n, hn, hxn⟩` from `hroot x hx`.

Use `⟨Polynomial.X ^ n - Polynomial.C 1, Polynomial.monic_X_pow_sub_C 1 (by omega), ?_⟩` and prove the remaining obligations. Simplify using `[hxn]`. Set `θ' : k →ₐ[S] FieldCopy k` to `IsAlgClosed.lift`. Set `θ : k →+* k` to `θ'.toRingHom`. Establish `hθS : ∀ s : S, θ (s : k) = ψ0 s`.

Introduce `s`. Use `θ'.commutes s` as an intermediate fact. Conclude with `this`. Establish `hθinj : Function.Injective θ` using `θ.injective`. Establish `hθsurj : Function.Surjective θ`.

Introduce `y`. Distinguish the cases in `hy : y = 0`. Conclude with `⟨0, by rw [hy, map_zero]⟩`. Take `⟨n, hn, hyn⟩` from `hroot y hy`. Set `T` to `Polynomial.nthRootsFinset n (1 : k)`.

Establish `hmem : ∀ x : k, x ∈ T ↔ x ^ n = 1` using `fun x => Polynomial.mem_nthRootsFinset (by omega) 1`. Set `f : T → T` to `fun t => ⟨θ t, (hmem _).2 (by rw [← map_pow, (hmem _).1 t.2, map_one])⟩`. Establish `hf : Function.Injective f`. Introduce `a b hab`. Conclude with `Subtype.ext (hθinj (congrArg Subtype.val hab))`.

Take `⟨t, ht⟩` from `Finite.injective_iff_surjective.1 hf ⟨y, (hmem y).2 hyn⟩`. Conclude with `⟨t, congrArg Subtype.val ht⟩`. Use `⟨RingEquiv.ofBijective θ ⟨hθinj, hθsurj⟩, ?_, ?_⟩` and prove the remaining obligations. Introduce `r hr`. Establish `hrS : (r : k) ∈ S` using `⟨MvPolynomial.C ⟨r, hr⟩, by simp [eα]; rfl⟩`.

Use `show θ r = r`. Establish `h2 : (⟨r, hrS⟩ : S) = eα.rangeRestrict (MvPolynomial.C ⟨r, hr⟩)` using `Subtype.ext (by simp [eα]; rfl)`. Rewrite using `[show r = ((⟨r, hrS⟩ : S) : k) from rfl, hθS, h2, hψ0]`. Simplify using `[eβ]`. Introduce `j show θ (α j) = β j`.

Establish `h2 : (⟨α j, ⟨MvPolynomial.X j, by simp [eα]⟩⟩ : S) = eα.rangeRestrict (MvPolynomial.X j)` using `Subtype.ext (by simp [eα])`. Rewrite using `[show α j = ((⟨α j, ⟨MvPolynomial.X j, by simp [eα]⟩⟩ : S) : k) from rfl, hθS, h2, hψ0]`. Simplify using `[eβ]`.
-/
theorem exists_ringEquiv_extending_of_ker_le :
    ∀ (k : Type) [Field k] [IsAlgClosed k], (∀ x : k, x ≠ 0 → ∃ n : ℕ, 1 ≤ n ∧ x ^ n = 1) →
      ∀ (R : Subring k) (J : Type) (α β : J → k),
        (∀ p : MvPolynomial J R, MvPolynomial.aeval α p = 0 → MvPolynomial.aeval β p = 0) →
        ∃ φ : k ≃+* k, (∀ r ∈ R, φ r = r) ∧ ∀ j, φ (α j) = β j := by
  intro k _ _ hroot R J α β hker
  let eα : MvPolynomial J R →ₐ[R] k := MvPolynomial.aeval α
  let eβ : MvPolynomial J R →ₐ[R] k := MvPolynomial.aeval β
  let S : Subalgebra R k := eα.range
  have hle : ∀ p ∈ RingHom.ker eα.rangeRestrict, eβ p = 0 := by
    intro p hp
    rw [RingHom.mem_ker] at hp
    apply hker
    have := congrArg Subtype.val hp
    simpa using this
  let ψ0 : S →ₐ[R] k := (Ideal.Quotient.liftₐ (RingHom.ker eα.rangeRestrict) eβ hle).comp
    (Ideal.quotientKerAlgEquivOfSurjective (AlgHom.rangeRestrict_surjective eα)).symm.toAlgHom
  have hψ0 : ∀ p, ψ0 (eα.rangeRestrict p) = eβ p := by
    intro p
    have h1 : (Ideal.quotientKerAlgEquivOfSurjective (AlgHom.rangeRestrict_surjective eα)).symm
        (eα.rangeRestrict p) = Ideal.Quotient.mk _ p := by
      rw [AlgEquiv.symm_apply_eq]
      rfl
    simp only [ψ0, AlgHom.comp_apply]
    erw [h1]
    rfl
  let ψ : S →+* FieldCopy k := ψ0.toRingHom
  have hψinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_zero]
    intro s hs
    by_contra hne
    have hne' : (s : k) ≠ 0 := fun h => hne (Subtype.ext h)
    obtain ⟨n, hn, hsn⟩ := hroot _ hne'
    have hsn' : s ^ n = 1 := Subtype.ext (by simpa using hsn)
    have : ψ s ^ n = 1 := by rw [← map_pow, hsn', map_one]
    rw [hs, zero_pow (by omega)] at this
    exact zero_ne_one this
  letI : Algebra S (FieldCopy k) := ψ.toAlgebra
  haveI : Module.IsTorsionFree S (FieldCopy k) := by
    refine Module.IsTorsionFree.of_smul_eq_zero fun r m h => ?_
    rw [Algebra.smul_def, mul_eq_zero] at h
    rcases h with h | h
    · left
      exact hψinj (h.trans (map_zero ψ).symm)
    · exact Or.inr h
  haveI : Algebra.IsIntegral S k := by
    constructor
    intro x
    by_cases hx : x = 0
    · rw [hx]; exact isIntegral_zero
    · obtain ⟨n, hn, hxn⟩ := hroot x hx
      refine ⟨Polynomial.X ^ n - Polynomial.C 1, Polynomial.monic_X_pow_sub_C 1 (by omega), ?_⟩
      simp [hxn]
  let θ' : k →ₐ[S] FieldCopy k := IsAlgClosed.lift
  let θ : k →+* k := θ'.toRingHom
  have hθS : ∀ s : S, θ (s : k) = ψ0 s := by
    intro s
    have := θ'.commutes s
    exact this
  have hθinj : Function.Injective θ := θ.injective
  have hθsurj : Function.Surjective θ := by
    intro y
    by_cases hy : y = 0
    · exact ⟨0, by rw [hy, map_zero]⟩
    obtain ⟨n, hn, hyn⟩ := hroot y hy
    let T := Polynomial.nthRootsFinset n (1 : k)
    have hmem : ∀ x : k, x ∈ T ↔ x ^ n = 1 := fun x => Polynomial.mem_nthRootsFinset (by omega) 1
    let f : T → T := fun t => ⟨θ t, (hmem _).2 (by rw [← map_pow, (hmem _).1 t.2, map_one])⟩
    have hf : Function.Injective f := by
      intro a b hab
      exact Subtype.ext (hθinj (congrArg Subtype.val hab))
    obtain ⟨t, ht⟩ := Finite.injective_iff_surjective.1 hf ⟨y, (hmem y).2 hyn⟩
    exact ⟨t, congrArg Subtype.val ht⟩
  refine ⟨RingEquiv.ofBijective θ ⟨hθinj, hθsurj⟩, ?_, ?_⟩
  · intro r hr
    have hrS : (r : k) ∈ S := ⟨MvPolynomial.C ⟨r, hr⟩, by simp [eα]; rfl⟩
    show θ r = r
    have h2 : (⟨r, hrS⟩ : S) = eα.rangeRestrict (MvPolynomial.C ⟨r, hr⟩) :=
      Subtype.ext (by simp [eα]; rfl)
    rw [show r = ((⟨r, hrS⟩ : S) : k) from rfl, hθS, h2, hψ0]
    simp [eβ]
  · intro j
    show θ (α j) = β j
    have h2 : (⟨α j, ⟨MvPolynomial.X j, by simp [eα]⟩⟩ : S) = eα.rangeRestrict (MvPolynomial.X j) :=
      Subtype.ext (by simp [eα])
    rw [show α j = ((⟨α j, ⟨MvPolynomial.X j, by simp [eα]⟩⟩ : S) : k) from rfl, hθS, h2, hψ0]
    simp [eβ]

end GlobalTheory
