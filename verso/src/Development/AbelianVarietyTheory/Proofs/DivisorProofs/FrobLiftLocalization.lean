import Development.AbelianVarietyTheory.Definitions.Divisors.IsFlatLift
open GlobalTheory GlobalTheory.DI

namespace GlobalTheory.DI

/- English proof (translation)
Introduce `p _ B Kt _ _ _ S _ F hp2 hF`. Establish `hunit : ∀ s : S, IsUnit ((algebraMap B Kt).comp F s)`. Introduce `s`. Take `⟨w, hw⟩` from `hF (s : B)`. Establish `hu : IsUnit (algebraMap B Kt (s : B) ^ p)` using `(IsLocalization.map_units Kt s).pow p`.

Establish `hn : IsNilpotent ((p : Kt) * algebraMap B Kt w)`. Use `⟨2, ?_⟩` and prove the remaining obligations. Establish `: (p : Kt) ^ 2 = 0`. Use `congrArg (algebraMap B Kt) hp2` as an intermediate fact. Simplify using `using this`.

Rewrite using `[mul_pow, this, zero_mul]`. Use `hn.isUnit_add_right_of_commute hu (Commute.all _ _)` as an intermediate fact. Rewrite `this` using `[add_comm]`. Simplify `this` using `[RingHom.comp_apply, hw, map_add, map_mul, map_pow, map_natCast]`. Use `⟨IsLocalization.lift hunit, fun b => by simp [IsLocalization.lift_eq], ?_⟩` and prove the remaining obligations.

Introduce `z`. Take `⟨⟨b, s⟩, rfl⟩` from `IsLocalization.mk'_surjective S z`. Use `set z := IsLocalization.mk' Kt b s with hz`. Use `set F' : Kt →+* Kt := IsLocalization.lift hunit`. Establish `hF' : ∀ c, F' (algebraMap B Kt c) = algebraMap B Kt (F c)` using `fun c => by`.

Simplify using `[F', IsLocalization.lift_eq]`. Establish `hspec : z * algebraMap B Kt (s : B) = algebraMap B Kt b` using `IsLocalization.mk'_spec Kt b s`. Take `⟨v, hv⟩` from `hF b`. Take `⟨u, hu⟩` from `hF (s : B)`. Establish `key : F' z * (algebraMap B Kt (s : B) ^ p + p * algebraMap B Kt u) = algebraMap B Kt b ^ p + p * algebraMap B Kt v`.

Use `congrArg F' hspec` as an intermediate fact. Rewrite `this` using `[map_mul, hF', hF', hu, hv]`. Simplify `this` using `[map_add, map_mul, map_pow, map_natCast]`. Take `⟨t, ht⟩` from `(IsLocalization.map_units Kt s).pow p`. Use `⟨(algebraMap B Kt v - F' z * algebraMap B Kt u) * ↑t⁻¹, ?_⟩` and prove the remaining obligations.

Establish `hzs : z ^ p * algebraMap B Kt (s : B) ^ p = algebraMap B Kt b ^ p`. Rewrite using `[← mul_pow, hspec]`. Establish `h1 : (F' z - z ^ p) * (t : Kt) = p * (algebraMap B Kt v - F' z * algebraMap B Kt u)`. Rewrite using `[ht]`. Take the linear combination `key - hzs`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mul_assoc, Units.mul_inv, mul_one]`. Expand and normalize the polynomial expressions, which then agree. Use `_ = _ := by rw [h1]; ring`.
-/
theorem frobLift_localization :
    ∀ (p : ℕ) [Fact p.Prime] {B Kt : Type} [CommRing B] [CommRing Kt] [Algebra B Kt]
      (S : Submonoid B) [IsLocalization S Kt] (F : B →+* B), (p : B) ^ 2 = 0 →
      (∀ z, ∃ w, F z = z ^ p + p * w) →
      ∃ F' : Kt →+* Kt, (∀ b, F' (algebraMap B Kt b) = algebraMap B Kt (F b)) ∧
        ∀ z, ∃ w, F' z = z ^ p + p * w := by
  intro p _ B Kt _ _ _ S _ F hp2 hF
  have hunit : ∀ s : S, IsUnit ((algebraMap B Kt).comp F s) := by
    intro s
    obtain ⟨w, hw⟩ := hF (s : B)
    have hu : IsUnit (algebraMap B Kt (s : B) ^ p) :=
      (IsLocalization.map_units Kt s).pow p
    have hn : IsNilpotent ((p : Kt) * algebraMap B Kt w) := by
      refine ⟨2, ?_⟩
      have : (p : Kt) ^ 2 = 0 := by
        have := congrArg (algebraMap B Kt) hp2
        simpa using this
      rw [mul_pow, this, zero_mul]
    have := hn.isUnit_add_right_of_commute hu (Commute.all _ _)
    rw [add_comm] at this
    simpa [RingHom.comp_apply, hw, map_add, map_mul, map_pow, map_natCast] using this
  refine ⟨IsLocalization.lift hunit, fun b => by simp [IsLocalization.lift_eq], ?_⟩
  intro z
  obtain ⟨⟨b, s⟩, rfl⟩ := IsLocalization.mk'_surjective S z
  set z := IsLocalization.mk' Kt b s with hz
  set F' : Kt →+* Kt := IsLocalization.lift hunit
  have hF' : ∀ c, F' (algebraMap B Kt c) = algebraMap B Kt (F c) := fun c => by
    simp [F', IsLocalization.lift_eq]
  have hspec : z * algebraMap B Kt (s : B) = algebraMap B Kt b := IsLocalization.mk'_spec Kt b s
  obtain ⟨v, hv⟩ := hF b
  obtain ⟨u, hu⟩ := hF (s : B)
  have key : F' z * (algebraMap B Kt (s : B) ^ p + p * algebraMap B Kt u) =
      algebraMap B Kt b ^ p + p * algebraMap B Kt v := by
    have := congrArg F' hspec
    rw [map_mul, hF', hF', hu, hv] at this
    simpa [map_add, map_mul, map_pow, map_natCast] using this
  obtain ⟨t, ht⟩ := (IsLocalization.map_units Kt s).pow p
  refine ⟨(algebraMap B Kt v - F' z * algebraMap B Kt u) * ↑t⁻¹, ?_⟩
  have hzs : z ^ p * algebraMap B Kt (s : B) ^ p = algebraMap B Kt b ^ p := by
    rw [← mul_pow, hspec]
  have h1 : (F' z - z ^ p) * (t : Kt) = p * (algebraMap B Kt v - F' z * algebraMap B Kt u) := by
    rw [ht]; linear_combination key - hzs
  calc F' z = z ^ p + (F' z - z ^ p) * (t : Kt) * ↑t⁻¹ := by
        rw [mul_assoc, Units.mul_inv, mul_one]; ring
    _ = _ := by rw [h1]; ring

end GlobalTheory.DI
