import Mathlib

open IsLocalRing

/- English proof (translation)
Introduce `Λ T _ _ _ _ _`. Set `I : Ideal T` to `(maximalIdeal Λ).map (algebraMap Λ T)`. Establish `h1 : Module.Finite Λ (T ⧸ I)` using `Module.Finite.of_surjective (Ideal.Quotient.mkₐ Λ I).toLinearMap Ideal.Quotient.mk_surjective`. Establish `h2 : Module.Finite (Λ ⧸ maximalIdeal Λ) (T ⧸ I)` using `Module.Finite.of_restrictScalars_finite Λ _ _`. Establish `h0 : IsArtinianRing (Λ ⧸ maximalIdeal Λ)`.

Use `letI := Ideal.Quotient.field (maximalIdeal Λ)`. Use `infer_instance`. Establish `h3 : IsArtinianRing (T ⧸ I)` using `IsArtinianRing.of_finite (Λ ⧸ maximalIdeal Λ) (T ⧸ I)`. Establish `hcomap : ∀ m : Ideal T, m.IsMaximal → m.comap (algebraMap Λ T) = maximalIdeal Λ`. Introduce `m hm`.

Use `haveI := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := Λ) m`. Conclude with `IsLocalRing.eq_maximalIdeal this`. Establish `hIm : ∀ m : Ideal T, m.IsMaximal → I ≤ m` using `fun m hm => Ideal.map_le_iff_le_comap.2 (hcomap m hm).ge`. Establish `hker : RingHom.ker (Ideal.Quotient.mk I) = I` using `Ideal.mk_ker`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations.

Set `f : MaximalSpectrum (T ⧸ I) → MaximalSpectrum T` to `fun p => ⟨p.asIdeal.comap (Ideal.Quotient.mk I), Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective⟩`. Apply `Finite.of_surjective f` to reduce the goal to its premises. Introduce `m`. Establish `hcm : (m.asIdeal.map (Ideal.Quotient.mk I)).comap (Ideal.Quotient.mk I) = m.asIdeal`. Rewrite using `[Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot, hker]`.

Conclude with `sup_eq_left.2 (hIm _ m.isMaximal)`. Break down `Ideal.map_eq_top_or_isMaximal_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective m.isMaximal with h | h` into its components or cases. It suffices to derive a contradiction. Apply `m.isMaximal.ne_top` to reduce the goal to its premises. Rewrite using `[← hcm, h, Ideal.comap_top]`.

Conclude with `⟨⟨_, h⟩, MaximalSpectrum.ext hcm⟩`. Introduce `m hm`. Use `⟨hcomap m hm, fun hk => ?_⟩` and prove the remaining obligations. Use `haveI : Finite (Λ ⧸ maximalIdeal Λ) := hk`. Use `haveI : Finite (T ⧸ I) := Module.finite_of_finite (Λ ⧸ maximalIdeal Λ)`.

Conclude with `Finite.of_surjective _ (Ideal.Quotient.factor_surjective (hIm m hm))`. Take `⟨n, hn⟩` from `IsArtinianRing.isNilpotent_jacobson_bot (R := T ⧸ I)`. Use `⟨n, ?_, ?_⟩` and prove the remaining obligations. Establish `hJ : (⊥ : Ideal T).jacobson.map (Ideal.Quotient.mk I) ≤ (⊥ : Ideal (T ⧸ I)).jacobson`. Rewrite using `[Ideal.map_le_iff_le_comap]`.

Introduce `x hx`. Rewrite using `[Ideal.mem_comap, Ideal.mem_jacobson_bot]`. Introduce `y`. Take `⟨y, rfl⟩` from `Ideal.Quotient.mk_surjective y`. Rewrite using `[← map_mul, ← map_one (Ideal.Quotient.mk I), ← map_add]`.

Conclude with `(Ideal.mem_jacobson_bot.1 hx y).map _`. Introduce `x hx`. Establish `hx' : Ideal.Quotient.mk I x ∈ ((⊥ : Ideal (T ⧸ I)).jacobson) ^ n`. Apply `Ideal.pow_right_mono hJ n` to reduce the goal to its premises. Rewrite using `[← Ideal.map_pow]`.

Conclude with `Ideal.mem_map_of_mem _ hx`. Rewrite `hx'` using `[hn]`. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `hx'`. Rewrite using `[Ideal.jacobson]`.

Use `le_sInf ?_` and prove the remaining obligations. Introduce and unpack `m ⟨-, hm⟩`. Conclude with `hIm m hm`.
-/
theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.finMax :
    ∀ (Λ T : Type) [CommRing Λ] [IsLocalRing Λ] [CommRing T] [Algebra Λ T] [Module.Finite Λ T], Finite (MaximalSpectrum T) ∧ (∀ m : Ideal T, m.IsMaximal → m.comap (algebraMap Λ T) = maximalIdeal Λ ∧ (Finite (ResidueField Λ) → Finite (T ⧸ m))) ∧ ∃ n : ℕ, (⊥ : Ideal T).jacobson ^ n ≤ (maximalIdeal Λ).map (algebraMap Λ T) ∧ (maximalIdeal Λ).map (algebraMap Λ T) ≤ (⊥ : Ideal T).jacobson := by
  intro Λ T _ _ _ _ _
  let I : Ideal T := (maximalIdeal Λ).map (algebraMap Λ T)
  have h1 : Module.Finite Λ (T ⧸ I) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ Λ I).toLinearMap Ideal.Quotient.mk_surjective
  have h2 : Module.Finite (Λ ⧸ maximalIdeal Λ) (T ⧸ I) :=
    Module.Finite.of_restrictScalars_finite Λ _ _
  have h0 : IsArtinianRing (Λ ⧸ maximalIdeal Λ) := by
    letI := Ideal.Quotient.field (maximalIdeal Λ)
    infer_instance
  have h3 : IsArtinianRing (T ⧸ I) := IsArtinianRing.of_finite (Λ ⧸ maximalIdeal Λ) (T ⧸ I)
  have hcomap : ∀ m : Ideal T, m.IsMaximal → m.comap (algebraMap Λ T) = maximalIdeal Λ := by
    intro m hm
    haveI := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := Λ) m
    exact IsLocalRing.eq_maximalIdeal this
  have hIm : ∀ m : Ideal T, m.IsMaximal → I ≤ m := fun m hm =>
    Ideal.map_le_iff_le_comap.2 (hcomap m hm).ge
  have hker : RingHom.ker (Ideal.Quotient.mk I) = I := Ideal.mk_ker
  refine ⟨?_, ?_, ?_⟩
  · let f : MaximalSpectrum (T ⧸ I) → MaximalSpectrum T := fun p =>
      ⟨p.asIdeal.comap (Ideal.Quotient.mk I),
        Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective⟩
    apply Finite.of_surjective f
    intro m
    have hcm : (m.asIdeal.map (Ideal.Quotient.mk I)).comap (Ideal.Quotient.mk I) = m.asIdeal := by
      rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
        hker]
      exact sup_eq_left.2 (hIm _ m.isMaximal)
    rcases Ideal.map_eq_top_or_isMaximal_of_surjective (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective m.isMaximal with h | h
    · exfalso
      apply m.isMaximal.ne_top
      rw [← hcm, h, Ideal.comap_top]
    · exact ⟨⟨_, h⟩, MaximalSpectrum.ext hcm⟩
  · intro m hm
    refine ⟨hcomap m hm, fun hk => ?_⟩
    haveI : Finite (Λ ⧸ maximalIdeal Λ) := hk
    haveI : Finite (T ⧸ I) := Module.finite_of_finite (Λ ⧸ maximalIdeal Λ)
    exact Finite.of_surjective _ (Ideal.Quotient.factor_surjective (hIm m hm))
  · obtain ⟨n, hn⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := T ⧸ I)
    refine ⟨n, ?_, ?_⟩
    · have hJ : (⊥ : Ideal T).jacobson.map (Ideal.Quotient.mk I) ≤ (⊥ : Ideal (T ⧸ I)).jacobson := by
        rw [Ideal.map_le_iff_le_comap]
        intro x hx
        rw [Ideal.mem_comap, Ideal.mem_jacobson_bot]
        intro y
        obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
        rw [← map_mul, ← map_one (Ideal.Quotient.mk I), ← map_add]
        exact (Ideal.mem_jacobson_bot.1 hx y).map _
      intro x hx
      have hx' : Ideal.Quotient.mk I x ∈ ((⊥ : Ideal (T ⧸ I)).jacobson) ^ n := by
        apply Ideal.pow_right_mono hJ n
        rw [← Ideal.map_pow]
        exact Ideal.mem_map_of_mem _ hx
      rw [hn] at hx'
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      exact hx'
    · rw [Ideal.jacobson]
      refine le_sInf ?_
      rintro m ⟨-, hm⟩
      exact hIm m hm
