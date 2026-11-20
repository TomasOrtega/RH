import Mathlib

open MvPolynomial

namespace GlobalTheory.CompanionTheory.Ar.ChartHom

/- English proof (translation)
Distinguish the cases in `hf : (aeval u F : Ω) = 0`. Establish `h0 : θ F = 0` using `hker F hf`. Establish `hR : Subsingleton R`. Establish `: IsUnit (0 : R)` using `h0 ▸ hF`. Conclude with `subsingleton_of_zero_eq_one (isUnit_zero_iff.mp this)`.

Use `⟨{ toFun := fun _ => 0, map_one' := Subsingleton.elim _ _, map_mul' := fun _ _ => Subsingleton.elim _ _, map_zero' := rfl, map_add' := fun _ _ => Subsingleton.elim _ _ }, fun _ _ _ => Subsingleton.elim _ _⟩` and prove the remaining obligations. Set `B` to `Localization.Away F`. Establish `hunit : ∀ y : Submonoid.powers F, IsUnit (aeval u (y : MvPolynomial σ ℚ) : Ω)`. Introduce and unpack `⟨_, n, rfl⟩`. Simplify using `using (IsUnit.mk0 _ hf).pow n`.

Set `Φ : B →ₐ[ℚ] Ω` to `IsLocalization.liftAlgHom (M := Submonoid.powers F) (f := aeval u) hunit`. Establish `hΦ : ∀ a : MvPolynomial σ ℚ, Φ (algebraMap _ B a) = aeval u a` using `fun a => by simp [Φ, IsLocalization.liftAlgHom_apply]`. Set `Θ : B →+* R` to `IsLocalization.Away.lift F hF`. Establish `hΘ : ∀ a : MvPolynomial σ ℚ, Θ (algebraMap _ B a) = θ a` using `fun a => IsLocalization.Away.lift_eq F hF a`. Establish `hnum : ∀ z : B, ∃ (n : ℕ) (a : MvPolynomial σ ℚ), z * algebraMap _ B (F ^ n) = algebraMap _ B a`.

Introduce `z`. Take `⟨n, a, h⟩` from `IsLocalization.Away.surj F z`. Conclude with `⟨n, a, by simpa using h⟩`. Establish `hmem : ∀ a : MvPolynomial σ ℚ, (aeval u a : Ω) ∈ S`. Introduce `a`.

Establish `: (aeval u a : Ω) ∈ Algebra.adjoin ℚ (Set.range u)`. Rewrite using `[Algebra.adjoin_range_eq_range_aeval]`. Conclude with `⟨a, rfl⟩`. Rewrite using `[hS]`. Conclude with `Algebra.adjoin_mono (Set.subset_insert _ _) this`.

Establish `hinv : (aeval u F : Ω)⁻¹ ∈ S`. Rewrite using `[hS]`. Conclude with `Algebra.subset_adjoin (Set.mem_insert _ _)`. Establish `hΦS : ∀ z : B, Φ z ∈ S`. Introduce `z`.

Take `⟨n, a, h⟩` from `hnum z`. Establish `h2` using `congrArg Φ h`. Rewrite `h2` using `[map_mul, hΦ, hΦ, map_pow]`. Establish `: Φ z = aeval u a * ((aeval u F : Ω)⁻¹) ^ n`. Rewrite using `[← h2, inv_pow, _root_.mul_assoc, mul_inv_cancel₀ (pow_ne_zero n hf), _root_.mul_one]`.

Rewrite using `[this]`. Conclude with `S.mul_mem (hmem a) (S.pow_mem hinv n)`. Set `Φ' : B →+* S` to `(Φ : B →+* Ω).codRestrict S.toSubsemiring hΦS`. Establish `hΦ' : ∀ z, ((Φ' z : S) : Ω) = Φ z` using `fun _ => rfl`. Establish `hsurj : Function.Surjective Φ'`.

Establish `hle : S ≤ Φ.range`. Rewrite using `[hS]`. Use `Algebra.adjoin_le ?_` and prove the remaining obligations. Introduce and unpack `_ (rfl | ⟨p, rfl⟩)`. Establish `hu : IsUnit (algebraMap _ B F)` using `IsLocalization.Away.algebraMap_isUnit F`.

Take `⟨v, hv⟩` from `hu`. Use `⟨(↑v⁻¹ : B), ?_⟩` and prove the remaining obligations. Establish `h1 : Φ (↑v⁻¹ : B) * aeval u F = 1`. Rewrite using `[← hΦ, ← hv, ← map_mul]`. Simplify using the standard rewrite rules.

Conclude with `eq_inv_of_mul_eq_one_left h1`. Conclude with `⟨algebraMap (MvPolynomial σ ℚ) B (X p), (hΦ (X p)).trans (aeval_X u p)⟩`. Introduce `s`. Take `⟨z, hz⟩` from `hle s.2`. Conclude with `⟨z, Subtype.ext hz⟩`.

Establish `hkerΘ : RingHom.ker Φ' ≤ RingHom.ker Θ`. Introduce `z hz`. Rewrite `hz`, the goal using `[RingHom.mem_ker]`. Establish `hz0 : Φ z = 0`. Use `congrArg (Subtype.val) hz` as an intermediate fact.

Simplify `this` using `[hΦ']`. Take `⟨n, a, h⟩` from `hnum z`. Establish `h2` using `congrArg Φ h`. Rewrite `h2` using `[map_mul, hz0, zero_mul, hΦ]`. Establish `ha : θ a = 0` using `hker a h2.symm`.

Establish `h3` using `congrArg Θ h`. Rewrite `h3` using `[map_mul, hΘ, hΘ, ha, map_pow]`. Conclude with `(hF.pow n).mul_left_eq_zero.mp h3`. Use `⟨RingHom.liftOfSurjective Φ' hsurj ⟨Θ, hkerΘ⟩, fun G s hs => ?_⟩` and prove the remaining obligations. Establish `hsG : s = Φ' (algebraMap _ B G)` using `Subtype.ext (by rw [hΦ', hΦ, hs])`.

Rewrite using `[hsG, RingHom.liftOfRightInverse_comp_apply]`. Conclude with `hΘ G`.
-/
theorem exists_hom_adjoin_inv {σ Ω R : Type*} [Field Ω] [CharZero Ω] [CommRing R]
    (u : σ → Ω) (θ : MvPolynomial σ ℚ →+* R)
    (hker : ∀ G : MvPolynomial σ ℚ, aeval u G = (0 : Ω) → θ G = 0)
    (F : MvPolynomial σ ℚ) (hF : IsUnit (θ F))
    (S : Subalgebra ℚ Ω) (hS : S = Algebra.adjoin ℚ (insert (aeval u F : Ω)⁻¹ (Set.range u))) :
    ∃ ψ : S →+* R, ∀ (G : MvPolynomial σ ℚ) (s : S), (s : Ω) = aeval u G → ψ s = θ G := by
  classical
  by_cases hf : (aeval u F : Ω) = 0
  · have h0 : θ F = 0 := hker F hf
    have hR : Subsingleton R := by
      have : IsUnit (0 : R) := h0 ▸ hF
      exact subsingleton_of_zero_eq_one (isUnit_zero_iff.mp this)
    refine ⟨{ toFun := fun _ => 0, map_one' := Subsingleton.elim _ _, map_mul' := fun _ _ => Subsingleton.elim _ _,
              map_zero' := rfl, map_add' := fun _ _ => Subsingleton.elim _ _ }, fun _ _ _ => Subsingleton.elim _ _⟩
  · let B := Localization.Away F
    have hunit : ∀ y : Submonoid.powers F, IsUnit (aeval u (y : MvPolynomial σ ℚ) : Ω) := by
      rintro ⟨_, n, rfl⟩
      simpa using (IsUnit.mk0 _ hf).pow n
    let Φ : B →ₐ[ℚ] Ω := IsLocalization.liftAlgHom (M := Submonoid.powers F) (f := aeval u) hunit
    have hΦ : ∀ a : MvPolynomial σ ℚ, Φ (algebraMap _ B a) = aeval u a := fun a =>
      by simp [Φ, IsLocalization.liftAlgHom_apply]
    let Θ : B →+* R := IsLocalization.Away.lift F hF
    have hΘ : ∀ a : MvPolynomial σ ℚ, Θ (algebraMap _ B a) = θ a := fun a =>
      IsLocalization.Away.lift_eq F hF a
    have hnum : ∀ z : B, ∃ (n : ℕ) (a : MvPolynomial σ ℚ), z * algebraMap _ B (F ^ n) = algebraMap _ B a := by
      intro z
      obtain ⟨n, a, h⟩ := IsLocalization.Away.surj F z
      exact ⟨n, a, by simpa using h⟩
    have hmem : ∀ a : MvPolynomial σ ℚ, (aeval u a : Ω) ∈ S := by
      intro a
      have : (aeval u a : Ω) ∈ Algebra.adjoin ℚ (Set.range u) := by
        rw [Algebra.adjoin_range_eq_range_aeval]; exact ⟨a, rfl⟩
      rw [hS]
      exact Algebra.adjoin_mono (Set.subset_insert _ _) this
    have hinv : (aeval u F : Ω)⁻¹ ∈ S := by
      rw [hS]; exact Algebra.subset_adjoin (Set.mem_insert _ _)
    have hΦS : ∀ z : B, Φ z ∈ S := by
      intro z
      obtain ⟨n, a, h⟩ := hnum z
      have h2 := congrArg Φ h
      rw [map_mul, hΦ, hΦ, map_pow] at h2
      have : Φ z = aeval u a * ((aeval u F : Ω)⁻¹) ^ n := by
        rw [← h2, inv_pow, _root_.mul_assoc, mul_inv_cancel₀ (pow_ne_zero n hf), _root_.mul_one]
      rw [this]
      exact S.mul_mem (hmem a) (S.pow_mem hinv n)
    let Φ' : B →+* S := (Φ : B →+* Ω).codRestrict S.toSubsemiring hΦS
    have hΦ' : ∀ z, ((Φ' z : S) : Ω) = Φ z := fun _ => rfl
    have hsurj : Function.Surjective Φ' := by
      have hle : S ≤ Φ.range := by
        rw [hS]
        refine Algebra.adjoin_le ?_
        rintro _ (rfl | ⟨p, rfl⟩)
        · have hu : IsUnit (algebraMap _ B F) := IsLocalization.Away.algebraMap_isUnit F
          obtain ⟨v, hv⟩ := hu
          refine ⟨(↑v⁻¹ : B), ?_⟩
          have h1 : Φ (↑v⁻¹ : B) * aeval u F = 1 := by
            rw [← hΦ, ← hv, ← map_mul]; simp
          exact eq_inv_of_mul_eq_one_left h1
        · exact ⟨algebraMap (MvPolynomial σ ℚ) B (X p), (hΦ (X p)).trans (aeval_X u p)⟩
      intro s
      obtain ⟨z, hz⟩ := hle s.2
      exact ⟨z, Subtype.ext hz⟩
    have hkerΘ : RingHom.ker Φ' ≤ RingHom.ker Θ := by
      intro z hz
      rw [RingHom.mem_ker] at hz ⊢
      have hz0 : Φ z = 0 := by
        have := congrArg (Subtype.val) hz
        simpa [hΦ'] using this
      obtain ⟨n, a, h⟩ := hnum z
      have h2 := congrArg Φ h
      rw [map_mul, hz0, zero_mul, hΦ] at h2
      have ha : θ a = 0 := hker a h2.symm
      have h3 := congrArg Θ h
      rw [map_mul, hΘ, hΘ, ha, map_pow] at h3
      exact (hF.pow n).mul_left_eq_zero.mp h3
    refine ⟨RingHom.liftOfSurjective Φ' hsurj ⟨Θ, hkerΘ⟩, fun G s hs => ?_⟩
    have hsG : s = Φ' (algebraMap _ B G) := Subtype.ext (by rw [hΦ', hΦ, hs])
    rw [hsG, RingHom.liftOfRightInverse_comp_apply]
    exact hΘ G

end GlobalTheory.CompanionTheory.Ar.ChartHom
