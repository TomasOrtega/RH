import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsolateMaximalAmongPrimesContainingEtaleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatLocalizationMembership
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleUniquePrimeLeMapMaximalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NilpotentApproximationSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DedekindPowerLocalization
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalizationResidueApproximation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalizationInverseModF

namespace GlobalTheory

/- English proof (translation)
Introduce `B D _ _ _ _ _ f hf P hP hfP Q hQ hQP hres`. Establish `hQmax : Q.IsMaximal`. Rewrite using `[Ideal.isMaximal_iff]`. Use `⟨fun h1 => ?_, fun J x hQJ hx hxJ => ?_⟩` and prove the remaining obligations. Establish `: (1 : B) ∈ Q.comap (algebraMap B D)` using `by simpa using h1`.

Rewrite `this` using `[hQP]`. Conclude with `hP.ne_top ((Ideal.eq_top_iff_one _).2 this)`. Take `⟨b, hb⟩` from `hres x`. Establish `hbP : b ∉ P`. Introduce `hbP`.

Apply `hx` to reduce the goal to its premises. Establish `: algebraMap B D b ∈ Q`. Rewrite using `[← Ideal.mem_comap, hQP]`. Conclude with `hbP`. Simplify using `using Q.add_mem hb this`.

Choose the witnesses or unpack the hypotheses as in `⟨c, hc⟩ : ∃ c : B, c * b - 1 ∈ P := by`. Take `⟨c, i, hi, hci⟩` from `hP.exists_inv hbP`. Use `⟨c, ?_⟩` and prove the remaining obligations. Establish `: c * b - 1 = -i` using `by rw [← hci]; ring`. Rewrite using `[this]`.

Conclude with `P.neg_mem hi`. Establish `h1 : algebraMap B D (c * b - 1) ∈ Q`. Rewrite using `[← Ideal.mem_comap, hQP]`. Conclude with `hc`. Establish `h2 : algebraMap B D c * x - 1 ∈ Q`.

Establish `: algebraMap B D c * x - 1 = algebraMap B D c * (x - algebraMap B D b) + algebraMap B D (c * b - 1)`. Simplify using `only [map_sub, map_mul, map_one]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Conclude with `Q.add_mem (Q.mul_mem_left _ hb) h1`.

Establish `h3 : algebraMap B D c * x ∈ J` using `J.mul_mem_left _ hxJ`. Establish `: (1 : D) = algebraMap B D c * x - (algebraMap B D c * x - 1)` using `by ring`. Rewrite using `[this]`. Conclude with `J.sub_mem h3 (hQJ h2)`. Take `⟨g, hgQ, hQ'⟩` from `GlobalTheory.T.isolate_maximal_among_primes_containing_etale B D f hf Q hQmax`.

Use `⟨g, ?_⟩` and prove the remaining obligations. Use `haveI : Algebra.Etale D (Localization.Away g) := Algebra.Etale.of_isLocalizationAway g`. Use `haveI : Algebra.Etale B (Localization.Away g) := Algebra.Etale.comp B D (Localization.Away g)`. Establish `hφ : ∀ b : B, algebraMap B (Localization.Away g) b = algebraMap D (Localization.Away g) (algebraMap B D b)` using `fun b => IsScalarTower.algebraMap_apply B D (Localization.Away g) b`. Establish `hunit` using `GlobalTheory.T.localization_inverse_mod_f B D f P Q g hQP hQ'`.

Establish `hker : ∀ b : B, (∃ s : B, s ∉ P ∧ s * b ∈ Ideal.span {f}) → algebraMap B (Localization.Away g) b ∈ Ideal.span {algebraMap B (Localization.Away g) f}`. Introduce and unpack `b ⟨s, hs, hsb⟩`. Take `⟨t, ht⟩` from `hunit s hs`. Establish `h1 : algebraMap B (Localization.Away g) (s * b) ∈ Ideal.span {algebraMap B (Localization.Away g) f}`. Rewrite `hsb`, the goal using `[Ideal.mem_span_singleton]`.

Take `⟨c, hc⟩` from `hsb`. Conclude with `⟨algebraMap B _ c, by rw [hc, map_mul]⟩`. Establish `: algebraMap B (Localization.Away g) b = algebraMap B _ (s * b) * t - (algebraMap B _ s * t - 1) * algebraMap B (Localization.Away g) b`. Rewrite using `[map_mul]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[this]`. Conclude with `Ideal.sub_mem _ (Ideal.mul_mem_right _ _ h1) (Ideal.mul_mem_right _ _ ht)`. Use `⟨?_, fun b => ⟨fun hb => ?_, hker b⟩⟩` and prove the remaining obligations. Take `⟨N, hN⟩` from `GlobalTheory.T.dedekind_power_localization B f hf P hP`. Establish `hPN : (P ^ N).map (algebraMap B (Localization.Away g)) ≤ Ideal.span {algebraMap B (Localization.Away g) f}`.

Rewrite using `[Ideal.map_le_iff_le_comap]`. Introduce `b hb`. Conclude with `hker b (hN b hb)`. Establish `hfib : ∀ Q' : Ideal (Localization.Away g), Q'.IsPrime → P.map (algebraMap B (Localization.Away g)) ≤ Q' → Q' = Q.map (algebraMap D (Localization.Away g))`. Introduce `Q' hQ'p hPQ'`.

Establish `hc : Q'.comap (algebraMap D (Localization.Away g)) = Q`. Apply `hQ' _ (Ideal.comap_isPrime _ _)` to reduce the goal to its premises. Rewrite using `[Ideal.mem_comap, ← hφ]`. Conclude with `hPQ' (Ideal.mem_map_of_mem _ hfP)`. Introduce `hg`.

Rewrite `hg` using `[Ideal.mem_comap]`. Conclude with `hQ'p.ne_top (Ideal.eq_top_of_isUnit_mem _ hg (IsLocalization.Away.algebraMap_isUnit g))`. Rewrite using `[← hc]`. Conclude with `(IsLocalization.map_comap (Submonoid.powers g) (Localization.Away g) Q').symm`. Establish `hle` using `GlobalTheory.T.etale_unique_prime_le_map_maximal B (Localization.Away g) P hP (Q.map (algebraMap D (Localization.Away g))) hfib`.

Establish `hres'` using `GlobalTheory.T.localization_residue_approximation B D P hP Q g hgQ hQP hres`. Use `GlobalTheory.T.nilpotent_approximation_surjective B (Localization.Away g) P _ N (fun a => ?_) hPN` and prove the remaining obligations. Take `⟨b, hb⟩` from `hres' a`. Conclude with `⟨b, Ideal.mem_sup_left (hle hb)⟩`. Establish `hgu : IsUnit (algebraMap D (Localization.AtPrime Q) g)` using `IsLocalization.map_units (Localization.AtPrime Q) (⟨g, hgQ⟩ : Q.primeCompl)`.

Set `ρ : Localization.Away g →+* Localization.AtPrime Q` to `IsLocalization.Away.lift g hgu`. Establish `hρ : ∀ d : D, ρ (algebraMap D (Localization.Away g) d) = algebraMap D (Localization.AtPrime Q) d` using `fun d => IsLocalization.Away.lift_eq g hgu d`. Establish `e : ∀ x : B, algebraMap B (Localization.AtPrime Q) x = ρ (algebraMap B (Localization.Away g) x)`. Introduce `x`. Rewrite using `[hφ, hρ, IsScalarTower.algebraMap_apply B D (Localization.AtPrime Q)]`.

Establish `hloc : algebraMap B (Localization.AtPrime Q) b ∈ Ideal.span {algebraMap B (Localization.AtPrime Q) f}`. Rewrite `hb`, the goal using `[Ideal.mem_span_singleton]`. Take `⟨c, hc⟩` from `hb`. Conclude with `⟨ρ c, by rw [e, e, hc, map_mul]⟩`. Take `⟨s, hs, hsb⟩` from `GlobalTheory.T.flat_localization_membership B D Q f b hloc`.

Rewrite `hs` using `[hQP]`. Conclude with `⟨s, hs, hsb⟩`.
-/
theorem etale_away_quotient_eq_localization :
    ∀ (B D : Type) [CommRing B] [IsDedekindDomain B] [CommRing D] [Algebra B D] [Algebra.Etale B D]
      (f : B), f ≠ 0 → ∀ (P : Ideal B), P.IsMaximal → f ∈ P → ∀ (Q : Ideal D), Q.IsPrime →
      Q.comap (algebraMap B D) = P → (∀ d : D, ∃ b : B, d - algebraMap B D b ∈ Q) →
      ∃ g : D, (∀ a : Localization.Away g, ∃ b : B,
          a - algebraMap B (Localization.Away g) b ∈
            Ideal.span {algebraMap B (Localization.Away g) f}) ∧
        ∀ b : B, algebraMap B (Localization.Away g) b ∈
            Ideal.span {algebraMap B (Localization.Away g) f} ↔
          ∃ s : B, s ∉ P ∧ s * b ∈ Ideal.span {f} := by
  intro B D _ _ _ _ _ f hf P hP hfP Q hQ hQP hres

  have hQmax : Q.IsMaximal := by
    rw [Ideal.isMaximal_iff]
    refine ⟨fun h1 => ?_, fun J x hQJ hx hxJ => ?_⟩
    · have : (1 : B) ∈ Q.comap (algebraMap B D) := by simpa using h1
      rw [hQP] at this
      exact hP.ne_top ((Ideal.eq_top_iff_one _).2 this)
    · obtain ⟨b, hb⟩ := hres x
      have hbP : b ∉ P := by
        intro hbP
        apply hx
        have : algebraMap B D b ∈ Q := by
          rw [← Ideal.mem_comap, hQP]; exact hbP
        simpa using Q.add_mem hb this
      obtain ⟨c, hc⟩ : ∃ c : B, c * b - 1 ∈ P := by
        obtain ⟨c, i, hi, hci⟩ := hP.exists_inv hbP
        refine ⟨c, ?_⟩
        have : c * b - 1 = -i := by rw [← hci]; ring
        rw [this]; exact P.neg_mem hi
      have h1 : algebraMap B D (c * b - 1) ∈ Q := by
        rw [← Ideal.mem_comap, hQP]; exact hc
      have h2 : algebraMap B D c * x - 1 ∈ Q := by
        have : algebraMap B D c * x - 1 =
            algebraMap B D c * (x - algebraMap B D b) + algebraMap B D (c * b - 1) := by
          simp only [map_sub, map_mul, map_one]; ring
        rw [this]
        exact Q.add_mem (Q.mul_mem_left _ hb) h1
      have h3 : algebraMap B D c * x ∈ J := J.mul_mem_left _ hxJ
      have : (1 : D) = algebraMap B D c * x - (algebraMap B D c * x - 1) := by ring
      rw [this]
      exact J.sub_mem h3 (hQJ h2)
  obtain ⟨g, hgQ, hQ'⟩ := GlobalTheory.T.isolate_maximal_among_primes_containing_etale B D f hf Q hQmax
  refine ⟨g, ?_⟩
  haveI : Algebra.Etale D (Localization.Away g) := Algebra.Etale.of_isLocalizationAway g
  haveI : Algebra.Etale B (Localization.Away g) := Algebra.Etale.comp B D (Localization.Away g)
  have hφ : ∀ b : B, algebraMap B (Localization.Away g) b =
      algebraMap D (Localization.Away g) (algebraMap B D b) := fun b =>
    IsScalarTower.algebraMap_apply B D (Localization.Away g) b

  have hunit := GlobalTheory.T.localization_inverse_mod_f B D f P Q g hQP hQ'

  have hker : ∀ b : B, (∃ s : B, s ∉ P ∧ s * b ∈ Ideal.span {f}) →
      algebraMap B (Localization.Away g) b ∈
        Ideal.span {algebraMap B (Localization.Away g) f} := by
    rintro b ⟨s, hs, hsb⟩
    obtain ⟨t, ht⟩ := hunit s hs
    have h1 : algebraMap B (Localization.Away g) (s * b) ∈
        Ideal.span {algebraMap B (Localization.Away g) f} := by
      rw [Ideal.mem_span_singleton] at hsb ⊢
      obtain ⟨c, hc⟩ := hsb
      exact ⟨algebraMap B _ c, by rw [hc, map_mul]⟩
    have : algebraMap B (Localization.Away g) b = algebraMap B _ (s * b) * t -
        (algebraMap B _ s * t - 1) * algebraMap B (Localization.Away g) b := by
      rw [map_mul]; ring
    rw [this]
    exact Ideal.sub_mem _ (Ideal.mul_mem_right _ _ h1) (Ideal.mul_mem_right _ _ ht)
  refine ⟨?_, fun b => ⟨fun hb => ?_, hker b⟩⟩
  ·
    obtain ⟨N, hN⟩ := GlobalTheory.T.dedekind_power_localization B f hf P hP
    have hPN : (P ^ N).map (algebraMap B (Localization.Away g)) ≤
        Ideal.span {algebraMap B (Localization.Away g) f} := by
      rw [Ideal.map_le_iff_le_comap]
      intro b hb
      exact hker b (hN b hb)
    have hfib : ∀ Q' : Ideal (Localization.Away g), Q'.IsPrime →
        P.map (algebraMap B (Localization.Away g)) ≤ Q' →
        Q' = Q.map (algebraMap D (Localization.Away g)) := by
      intro Q' hQ'p hPQ'
      have hc : Q'.comap (algebraMap D (Localization.Away g)) = Q := by
        apply hQ' _ (Ideal.comap_isPrime _ _)
        · rw [Ideal.mem_comap, ← hφ]
          exact hPQ' (Ideal.mem_map_of_mem _ hfP)
        · intro hg
          rw [Ideal.mem_comap] at hg
          exact hQ'p.ne_top (Ideal.eq_top_of_isUnit_mem _ hg
            (IsLocalization.Away.algebraMap_isUnit g))
      rw [← hc]
      exact (IsLocalization.map_comap (Submonoid.powers g) (Localization.Away g) Q').symm
    have hle := GlobalTheory.T.etale_unique_prime_le_map_maximal B (Localization.Away g) P hP
      (Q.map (algebraMap D (Localization.Away g))) hfib
    have hres' := GlobalTheory.T.localization_residue_approximation B D P hP Q g hgQ hQP hres
    refine GlobalTheory.T.nilpotent_approximation_surjective B (Localization.Away g) P _ N (fun a => ?_) hPN
    obtain ⟨b, hb⟩ := hres' a
    exact ⟨b, Ideal.mem_sup_left (hle hb)⟩
  ·
    have hgu : IsUnit (algebraMap D (Localization.AtPrime Q) g) :=
      IsLocalization.map_units (Localization.AtPrime Q) (⟨g, hgQ⟩ : Q.primeCompl)
    let ρ : Localization.Away g →+* Localization.AtPrime Q := IsLocalization.Away.lift g hgu
    have hρ : ∀ d : D, ρ (algebraMap D (Localization.Away g) d) =
        algebraMap D (Localization.AtPrime Q) d :=
      fun d => IsLocalization.Away.lift_eq g hgu d
    have e : ∀ x : B, algebraMap B (Localization.AtPrime Q) x =
        ρ (algebraMap B (Localization.Away g) x) := by
      intro x
      rw [hφ, hρ, IsScalarTower.algebraMap_apply B D (Localization.AtPrime Q)]
    have hloc : algebraMap B (Localization.AtPrime Q) b ∈
        Ideal.span {algebraMap B (Localization.AtPrime Q) f} := by
      rw [Ideal.mem_span_singleton] at hb ⊢
      obtain ⟨c, hc⟩ := hb
      exact ⟨ρ c, by rw [e, e, hc, map_mul]⟩
    obtain ⟨s, hs, hsb⟩ := GlobalTheory.T.flat_localization_membership B D Q f b hloc
    rw [hQP] at hs
    exact ⟨s, hs, hsb⟩

end GlobalTheory
