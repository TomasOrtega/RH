import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ScalesBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEquivReps
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittFrameLeviNormalizesRadicalPropertiesStatement

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.ResidueEisenstein

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ n J r X Y L a h D T hT`. Establish `hrat` using `(GlobalTheory.T.wittFrameLevi_normalizes_radical_properties F E σ n J r X Y D.cm D.herm D.witt).2.2.2.2.1`. Establish `h3 : ∀ γ ∈ (ratPts σ J ⊓ GlobalTheory.StdPar.frameStab σ J X ⊤), ∀ g, h (γ * g) = h g`. Introduce and unpack `γ ⟨hγ, B, -, hB⟩ g`. Take `⟨p, β, hp, k, hk, rfl⟩` from `D.iwa g`.

Establish `hs : ScalesBy σ J X (γ * p) (B * β)`. Unfold `ScalesBy at hp ⊢`. Rewrite using `[map_mul, Units.val_mul, Matrix.mul_assoc, hp, ← Matrix.mul_assoc, hB, Matrix.mul_assoc, Units.val_mul]`. Rewrite using `[← mul_assoc, D.ht _ _ hs k hk, D.ht _ _ hp k hk, map_mul, map_mul, hrat γ hγ B hB, one_mul]`. Establish `h4 : ∀ γ : ratPts σ J, ∃! t, t ∈ T ∧ ((γ * t⁻¹ : ratPts σ J) : GAd σ J) ∈ (ratPts σ J ⊓ GlobalTheory.StdPar.frameStab σ J X ⊤)`.

Introduce `γ`. Take `⟨t, ⟨ht, β, hβ⟩, hu⟩` from `hT γ`. Conclude with `⟨t, ⟨ht, (γ * t⁻¹).2, β, trivial, hβ⟩, fun s hs => hu s ⟨hs.1, let ⟨β, _, e⟩ := hs.2.2; ⟨β, e⟩⟩⟩`. Use `⟨fun γ hγ => ?_, ?_, h3, h4⟩` and prove the remaining obligations. Take `⟨π, hπ⟩` from `exists_equiv_reps _ _ T h4 ⟨γ, hγ⟩`.

Use `⟨π, fun i g => ?_⟩` and prove the remaining obligations. Rewrite using `[← h3 _ (hπ i) ((π i).1.1 * g)]`. Use `congr 1`. Simplify using `[mul_assoc]`. Take `⟨t, ⟨ht, hl⟩, -⟩` from `h4 1`.

Use `⟨⟨t, ht⟩, fun g => ?_⟩` and prove the remaining obligations. Rewrite using `[← h3 _ hl (t.1 * g)]`. Use `congr 1`. Simplify using the standard rewrite rules.
-/
theorem reps_perm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E) (L : Submodule (𝓞 E) (Fin n → E)) (a : GL (Fin n) (AF F ⊗[F] E)) (h : GAd σ J → ℝ), DataJ σ J X Y L a h → ∀ T, IsRepsJ σ J X T → (∀ γ ∈ ratPts σ J, ∃ π : T ≃ T, ∀ (i : T) g, h (i.1.1 * (γ * g)) = h ((π i).1.1 * g)) ∧ (∃ i : T, ∀ g, h (i.1.1 * g) = h g) ∧ (∀ γ ∈ (ratPts σ J ⊓ GlobalTheory.StdPar.frameStab σ J X ⊤), ∀ g, h (γ * g) = h g) ∧ ∀ γ : ratPts σ J, ∃! t, t ∈ T ∧ ((γ * t⁻¹ : ratPts σ J) : GAd σ J) ∈ (ratPts σ J ⊓ GlobalTheory.StdPar.frameStab σ J X ⊤) := by
  intro F E _ _ _ _ _ σ n J r X Y L a h D T hT
  have hrat := (GlobalTheory.T.wittFrameLevi_normalizes_radical_properties F E σ n J r X Y D.cm D.herm D.witt).2.2.2.2.1
  have h3 : ∀ γ ∈ (ratPts σ J ⊓ GlobalTheory.StdPar.frameStab σ J X ⊤), ∀ g, h (γ * g) = h g := by
    rintro γ ⟨hγ, B, -, hB⟩ g
    obtain ⟨p, β, hp, k, hk, rfl⟩ := D.iwa g
    have hs : ScalesBy σ J X (γ * p) (B * β) := by
      unfold ScalesBy at hp ⊢
      rw [map_mul, Units.val_mul, Matrix.mul_assoc, hp, ← Matrix.mul_assoc, hB, Matrix.mul_assoc, Units.val_mul]
    rw [← mul_assoc, D.ht _ _ hs k hk, D.ht _ _ hp k hk, map_mul, map_mul, hrat γ hγ B hB, one_mul]
  have h4 : ∀ γ : ratPts σ J, ∃! t, t ∈ T ∧ ((γ * t⁻¹ : ratPts σ J) : GAd σ J) ∈ (ratPts σ J ⊓ GlobalTheory.StdPar.frameStab σ J X ⊤) := by
    intro γ
    obtain ⟨t, ⟨ht, β, hβ⟩, hu⟩ := hT γ
    exact ⟨t, ⟨ht, (γ * t⁻¹).2, β, trivial, hβ⟩, fun s hs => hu s ⟨hs.1, let ⟨β, _, e⟩ := hs.2.2; ⟨β, e⟩⟩⟩
  refine ⟨fun γ hγ => ?_, ?_, h3, h4⟩
  · obtain ⟨π, hπ⟩ := exists_equiv_reps _ _ T h4 ⟨γ, hγ⟩
    refine ⟨π, fun i g => ?_⟩
    rw [← h3 _ (hπ i) ((π i).1.1 * g)]
    congr 1
    simp [mul_assoc]
  · obtain ⟨t, ⟨ht, hl⟩, -⟩ := h4 1
    refine ⟨⟨t, ht⟩, fun g => ?_⟩
    rw [← h3 _ hl (t.1 * g)]
    congr 1
    simp

end GlobalTheory.ResidueEisenstein
