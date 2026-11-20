import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.SiegelFixedPoints.IsThBIff
import Development.AbelianVarietyTheory.Definitions.Foundations.IsLamOfLSmulIff
open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.Glue GlobalTheory.KummerEisensteinGalois UpperTheory.Kd.L

/- English proof (translation)
Introduce `Ω _ _ ε l n hl`. Establish `hp : l.Prime` using `hl.out`. Establish `hmul : ∀ D E : ℕ, ¬ l ∣ D → ¬ l ∣ E → ¬ l ∣ D * E` using `fun D E hD hE h => ((Nat.Prime.dvd_mul hp).1 h).elim hD hE`. Use `⟨fun k => ⟨1, hp.not_dvd_one, ?_⟩, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Nat.cast_one, one_mul]`.

Conclude with `natCast_mem _ k`. Introduce and unpack `F G ⟨D, hD, hF⟩ ⟨E, hE, hG⟩`. Use `⟨D * E, hmul D E hD hE, ?_⟩` and prove the remaining obligations. Establish `h : ((D * E : ℕ) : Ω) * (F + G) = (E : Ω) * ((D : Ω) * F) + (D : Ω) * ((E : Ω) * G)` using `by push_cast; ring`. Rewrite using `[h]`.

Conclude with `add_mem (mul_mem (natCast_mem _ E) hF) (mul_mem (natCast_mem _ D) hG)`. Introduce and unpack `F G ⟨D, hD, hF⟩ ⟨E, hE, hG⟩`. Use `⟨D * E, hmul D E hD hE, ?_⟩` and prove the remaining obligations. Establish `h : ((D * E : ℕ) : Ω) * (F * G) = ((D : Ω) * F) * ((E : Ω) * G)` using `by push_cast; ring`. Rewrite using `[h]`.

Conclude with `mul_mem hF hG`. Introduce and unpack `s k hs F ⟨D, hD, hF⟩`. Use `⟨D, hD, ?_⟩` and prove the remaining obligations. Establish `key : ∀ y ∈ Subring.closure ({zt ε l n} : Set Ω), s y ∈ Subring.closure ({zt ε l n} : Set Ω)`. Introduce `y hy`.

Establish `hle : Subring.closure ({zt ε l n} : Set Ω) ≤ (Subring.closure ({zt ε l n} : Set Ω)).comap (s : Ω →+* Ω)`. Rewrite using `[Subring.closure_le, Set.singleton_subset_iff]`. Use `show s (zt ε l n) ∈ Subring.closure ({zt ε l n} : Set Ω)`. Rewrite using `[hs]`. Conclude with `pow_mem (Subring.subset_closure (Set.mem_singleton _)) k`.

Conclude with `hle hy`. Establish `h` using `key _ hF`. Rewrite `h` using `[map_mul, map_natCast]`. Then use the resulting hypothesis.
-/
theorem UpperTheory.inZl_closed_add_mul_and_cyclotomic_galois_stable :
    ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (l n : ℕ) [Fact l.Prime], (∀ k : ℕ, InZl ε l n (k : Ω)) ∧ (∀ F G : Ω, InZl ε l n F → InZl ε l n G → InZl ε l n (F + G)) ∧ (∀ F G : Ω, InZl ε l n F → InZl ε l n G → InZl ε l n (F * G)) ∧ ∀ (s : Ω ≃ₐ[ℚ] Ω) (k : ℕ), s (zt ε l n) = zt ε l n ^ k → ∀ F : Ω, InZl ε l n F → InZl ε l n (s F) := by
  intro Ω _ _ ε l n hl
  have hp : l.Prime := hl.out
  have hmul : ∀ D E : ℕ, ¬ l ∣ D → ¬ l ∣ E → ¬ l ∣ D * E := fun D E hD hE h =>
    ((Nat.Prime.dvd_mul hp).1 h).elim hD hE
  refine ⟨fun k => ⟨1, hp.not_dvd_one, ?_⟩, ?_, ?_, ?_⟩
  · rw [Nat.cast_one, one_mul]
    exact natCast_mem _ k
  · rintro F G ⟨D, hD, hF⟩ ⟨E, hE, hG⟩
    refine ⟨D * E, hmul D E hD hE, ?_⟩
    have h : ((D * E : ℕ) : Ω) * (F + G) = (E : Ω) * ((D : Ω) * F) + (D : Ω) * ((E : Ω) * G) := by
      push_cast; ring
    rw [h]
    exact add_mem (mul_mem (natCast_mem _ E) hF) (mul_mem (natCast_mem _ D) hG)
  · rintro F G ⟨D, hD, hF⟩ ⟨E, hE, hG⟩
    refine ⟨D * E, hmul D E hD hE, ?_⟩
    have h : ((D * E : ℕ) : Ω) * (F * G) = ((D : Ω) * F) * ((E : Ω) * G) := by
      push_cast; ring
    rw [h]
    exact mul_mem hF hG
  · rintro s k hs F ⟨D, hD, hF⟩
    refine ⟨D, hD, ?_⟩
    have key : ∀ y ∈ Subring.closure ({zt ε l n} : Set Ω), s y ∈ Subring.closure ({zt ε l n} : Set Ω) := by
      intro y hy
      have hle : Subring.closure ({zt ε l n} : Set Ω) ≤
          (Subring.closure ({zt ε l n} : Set Ω)).comap (s : Ω →+* Ω) := by
        rw [Subring.closure_le, Set.singleton_subset_iff]
        show s (zt ε l n) ∈ Subring.closure ({zt ε l n} : Set Ω)
        rw [hs]
        exact pow_mem (Subring.subset_closure (Set.mem_singleton _)) k
      exact hle hy
    have h := key _ hF
    rwa [map_mul, map_natCast] at h
