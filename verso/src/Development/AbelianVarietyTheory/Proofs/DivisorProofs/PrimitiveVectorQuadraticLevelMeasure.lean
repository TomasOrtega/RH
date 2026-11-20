import Mathlib

namespace GlobalTheory

/- English proof (translation)
Introduce `B D _ _ _ P hP Q g hg hQP hsurj a`. Take `⟨⟨d, s⟩, rfl⟩` from `IsLocalization.mk'_surjective (Submonoid.powers g) a`. Take `⟨n, hn⟩` from `s.2`. Take `⟨bd, hbd⟩` from `hsurj d`. Take `⟨bg, hbg⟩` from `hsurj g`.

Establish `hbgP : bg ∉ P`. Introduce `h`. Rewrite `h` using `[← hQP, Ideal.mem_comap]`. Conclude with `hg (by simpa using Q.add_mem hbg h)`. Take `⟨c, i, hi, hci⟩` from `hP.exists_inv hbgP`.

Establish `hcg : algebraMap B D c * g - 1 ∈ Q`. Establish `hiQ : algebraMap B D i ∈ Q` using `by rw [← hQP] at hi; exact hi`. Establish `e : algebraMap B D c * g - 1 = algebraMap B D c * (g - algebraMap B D bg) - algebraMap B D i`. Use `congrArg (algebraMap B D) hci` as an intermediate fact. Simplify using `only [map_add, map_mul, map_one] at this`.

Take the linear combination `this`. Rewrite using `[e]`. Conclude with `Q.sub_mem (Q.mul_mem_left _ hbg) hiQ`. Use `⟨bd * c ^ n, ?_⟩` and prove the remaining obligations. Establish `key : d - algebraMap B D (bd * c ^ n) * (s : D) ∈ Q`.

Rewrite using `[← hn]`. Rewrite `hcg`, `hbd`, the goal using `[← Ideal.Quotient.eq_zero_iff_mem]`. Simplify using `only [map_sub, map_mul, map_pow, map_one, sub_eq_zero] at hcg hbd ⊢`. Rewrite using `[hbd, mul_assoc, ← mul_pow, hcg, one_pow, mul_one]`. Use `set L := Localization.Away g`.

Establish `hspec : algebraMap D L (s : D) * IsLocalization.mk' L (1 : D) s = 1`. Rewrite using `[IsLocalization.mk'_spec', map_one]`. Establish `e : IsLocalization.mk' L d s - algebraMap B L (bd * c ^ n) = algebraMap D L (d - algebraMap B D (bd * c ^ n) * (s : D)) * IsLocalization.mk' L (1 : D) s`. Rewrite using `[IsScalarTower.algebraMap_apply B D L, IsLocalization.mk'_eq_mul_mk'_one, map_sub, map_mul (algebraMap D L)]`. Take the linear combination `(algebraMap D L (algebraMap B D (bd * c ^ n))) * hspec`.

Rewrite using `[e]`. Conclude with `Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ key)`.
-/
theorem residue_surj_localizationAway : ∀ (B D : Type) [CommRing B] [CommRing D] [Algebra B D] (P : Ideal B), P.IsMaximal → ∀ (Q : Ideal D) (g : D), g ∉ Q → Q.comap (algebraMap B D) = P → (∀ d : D, ∃ b : B, d - algebraMap B D b ∈ Q) → ∀ a : Localization.Away g, ∃ b : B, a - algebraMap B (Localization.Away g) b ∈ Q.map (algebraMap D (Localization.Away g)) := by
  intro B D _ _ _ P hP Q g hg hQP hsurj a
  obtain ⟨⟨d, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers g) a
  obtain ⟨n, hn⟩ := s.2
  obtain ⟨bd, hbd⟩ := hsurj d
  obtain ⟨bg, hbg⟩ := hsurj g
  have hbgP : bg ∉ P := by
    intro h
    rw [← hQP, Ideal.mem_comap] at h
    exact hg (by simpa using Q.add_mem hbg h)
  obtain ⟨c, i, hi, hci⟩ := hP.exists_inv hbgP
  have hcg : algebraMap B D c * g - 1 ∈ Q := by
    have hiQ : algebraMap B D i ∈ Q := by rw [← hQP] at hi; exact hi
    have e : algebraMap B D c * g - 1 = algebraMap B D c * (g - algebraMap B D bg) - algebraMap B D i := by
      have := congrArg (algebraMap B D) hci
      simp only [map_add, map_mul, map_one] at this
      linear_combination this
    rw [e]
    exact Q.sub_mem (Q.mul_mem_left _ hbg) hiQ
  refine ⟨bd * c ^ n, ?_⟩
  have key : d - algebraMap B D (bd * c ^ n) * (s : D) ∈ Q := by
    rw [← hn]
    rw [← Ideal.Quotient.eq_zero_iff_mem] at hcg hbd ⊢
    simp only [map_sub, map_mul, map_pow, map_one, sub_eq_zero] at hcg hbd ⊢
    rw [hbd, mul_assoc, ← mul_pow, hcg, one_pow, mul_one]
  set L := Localization.Away g
  have hspec : algebraMap D L (s : D) * IsLocalization.mk' L (1 : D) s = 1 := by
    rw [IsLocalization.mk'_spec', map_one]
  have e : IsLocalization.mk' L d s - algebraMap B L (bd * c ^ n)
      = algebraMap D L (d - algebraMap B D (bd * c ^ n) * (s : D)) * IsLocalization.mk' L (1 : D) s := by
    rw [IsScalarTower.algebraMap_apply B D L, IsLocalization.mk'_eq_mul_mk'_one, map_sub, map_mul (algebraMap D L)]
    linear_combination (algebraMap D L (algebraMap B D (bd * c ^ n))) * hspec
  rw [e]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ key)

end GlobalTheory
