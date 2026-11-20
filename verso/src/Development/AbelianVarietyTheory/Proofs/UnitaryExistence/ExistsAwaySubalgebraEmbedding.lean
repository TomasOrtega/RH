import Mathlib

namespace GlobalTheory.AwaySubalgebraEmbedding

/- English proof (translation)
Set `f : S₁ →ₐ[K] Localization.Away x` to `(IsScalarTower.toAlgHom K S (Localization.Away x)).comp S₁.val`. Establish `hxu : IsUnit (algebraMap S (Localization.Away x) x)` using `IsLocalization.Away.algebraMap_isUnit x`. Establish `hf : ∀ y : Submonoid.powers (⟨x, hx⟩ : S₁), IsUnit (f y)`. Introduce and unpack `⟨y, n, rfl⟩`. Simplify using `only [map_pow]`.

Conclude with `hxu.pow n`. Set `κ : Localization.Away (⟨x, hx⟩ : S₁) →ₐ[K] Localization.Away x` to `IsLocalization.liftAlgHom (M := Submonoid.powers (⟨x, hx⟩ : S₁)) hf`. Establish `hκ : ∀ s : S₁, κ (algebraMap S₁ (Localization.Away (⟨x, hx⟩ : S₁)) s) = algebraMap S (Localization.Away x) (s : S)`. Introduce `s`. Conclude with `IsLocalization.lift_eq (M := Submonoid.powers (⟨x, hx⟩ : S₁)) (g := (f : S₁ →+* Localization.Away x)) hf s`.

Establish `hxu₁ : IsUnit (algebraMap S₁ (Localization.Away (⟨x, hx⟩ : S₁)) ⟨x, hx⟩)` using `IsLocalization.Away.algebraMap_isUnit _`. Use `⟨κ, hκ, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `a ha`. Take `⟨n, s, hs⟩` from `IsLocalization.Away.surj (⟨x, hx⟩ : S₁) a`.

Establish `h0 : algebraMap S (Localization.Away x) (s : S) = 0`. Rewrite using `[← hκ, ← hs, map_mul, ha, zero_mul]`. Take `⟨⟨_, k, rfl⟩, hk⟩` from `(IsLocalization.map_eq_zero_iff (Submonoid.powers x) (Localization.Away x) _).1 h0`. Establish `h1 : (⟨x, hx⟩ : S₁) ^ k * s = 0`. Apply `Subtype.ext` to reduce the goal to its premises.

Simplify using `using hk`. Establish `h2 : a * algebraMap S₁ (Localization.Away (⟨x, hx⟩ : S₁)) ⟨x, hx⟩ ^ (n + k) = 0`. Rewrite using `[pow_add, ← mul_assoc, hs, ← map_pow, ← map_mul, mul_comm, h1, map_zero]`. Conclude with `(hxu₁.pow (n + k)).mul_left_eq_zero.1 h2`. Introduce `z m s hs hz`.

Take `⟨u, hu⟩` from `hxu₁.pow m`. Use `⟨algebraMap S₁ (Localization.Away (⟨x, hx⟩ : S₁)) ⟨s, hs⟩ * ↑u⁻¹, ?_⟩` and prove the remaining obligations. Apply `(hxu.pow m).mul_right_cancel` to reduce the goal to its premises. Establish `h3 : κ ↑u = algebraMap S (Localization.Away x) x ^ m`. Rewrite using `[hu, map_pow, hκ]`.

Use `show κ _ * _ = _`. Rewrite using `[hz, ← h3, ← map_mul, mul_assoc, Units.inv_mul, mul_one, hκ]`.
-/
theorem exists_away_subalgebra_embedding (K : Type) [Field K] (S : Type) [CommRing S]
    [Algebra K S] (S₁ : Subalgebra K S) (x : S) (hx : x ∈ S₁) :
    ∃ (κ : Localization.Away (⟨x, hx⟩ : S₁) →ₐ[K] Localization.Away x),
      (∀ s : S₁, κ (algebraMap S₁ (Localization.Away (⟨x, hx⟩ : S₁)) s)
        = algebraMap S (Localization.Away x) (s : S)) ∧
      Function.Injective κ ∧
      ∀ (z : Localization.Away x) (m : ℕ), ∀ s ∈ S₁,
        z * algebraMap S (Localization.Away x) x ^ m = algebraMap S (Localization.Away x) s →
          z ∈ AlgHom.range κ := by
  let f : S₁ →ₐ[K] Localization.Away x :=
    (IsScalarTower.toAlgHom K S (Localization.Away x)).comp S₁.val
  have hxu : IsUnit (algebraMap S (Localization.Away x) x) :=
    IsLocalization.Away.algebraMap_isUnit x
  have hf : ∀ y : Submonoid.powers (⟨x, hx⟩ : S₁), IsUnit (f y) := by
    rintro ⟨y, n, rfl⟩
    simp only [map_pow]
    exact hxu.pow n
  let κ : Localization.Away (⟨x, hx⟩ : S₁) →ₐ[K] Localization.Away x :=
    IsLocalization.liftAlgHom (M := Submonoid.powers (⟨x, hx⟩ : S₁)) hf
  have hκ : ∀ s : S₁, κ (algebraMap S₁ (Localization.Away (⟨x, hx⟩ : S₁)) s)
      = algebraMap S (Localization.Away x) (s : S) := by
    intro s
    exact IsLocalization.lift_eq (M := Submonoid.powers (⟨x, hx⟩ : S₁))
      (g := (f : S₁ →+* Localization.Away x)) hf s
  have hxu₁ : IsUnit (algebraMap S₁ (Localization.Away (⟨x, hx⟩ : S₁)) ⟨x, hx⟩) :=
    IsLocalization.Away.algebraMap_isUnit _
  refine ⟨κ, hκ, ?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro a ha
    obtain ⟨n, s, hs⟩ := IsLocalization.Away.surj (⟨x, hx⟩ : S₁) a
    have h0 : algebraMap S (Localization.Away x) (s : S) = 0 := by
      rw [← hκ, ← hs, map_mul, ha, zero_mul]
    obtain ⟨⟨_, k, rfl⟩, hk⟩ :=
      (IsLocalization.map_eq_zero_iff (Submonoid.powers x) (Localization.Away x) _).1 h0
    have h1 : (⟨x, hx⟩ : S₁) ^ k * s = 0 := by
      apply Subtype.ext
      simpa using hk
    have h2 : a * algebraMap S₁ (Localization.Away (⟨x, hx⟩ : S₁)) ⟨x, hx⟩ ^ (n + k) = 0 := by
      rw [pow_add, ← mul_assoc, hs, ← map_pow, ← map_mul, mul_comm, h1, map_zero]
    exact (hxu₁.pow (n + k)).mul_left_eq_zero.1 h2
  · intro z m s hs hz
    obtain ⟨u, hu⟩ := hxu₁.pow m
    refine ⟨algebraMap S₁ (Localization.Away (⟨x, hx⟩ : S₁)) ⟨s, hs⟩ * ↑u⁻¹, ?_⟩
    apply (hxu.pow m).mul_right_cancel
    have h3 : κ ↑u = algebraMap S (Localization.Away x) x ^ m := by
      rw [hu, map_pow, hκ]
    show κ _ * _ = _
    rw [hz, ← h3, ← map_mul, mul_assoc, Units.inv_mul, mul_one, hκ]

end GlobalTheory.AwaySubalgebraEmbedding
