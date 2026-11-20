import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankCyclotomicExtAndCyclotomicCharSurjective

namespace GlobalTheory.Cyc

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation TensorProduct

/- English proof (translation)
Establish `h1 : ‖(l : ℚ_[l])‖ < 1` using `Padic.norm_p_lt_one`. Establish `hne : ‖(1 : ℚ_[l])‖ ≠ ‖(l : ℚ_[l])‖` using `by rw [norm_one]; exact ne_of_gt h1`. Use `first`. Consider the case `rw [padicNormE.add_eq_max_of_ne hne, norm_one]`. Conclude with `max_eq_left h1.le`.

Consider the case `rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne, norm_one]`. Conclude with `max_eq_left h1.le`.
-/
private lemma norm_one_add_prime_padic (l : ℕ) [Fact l.Prime] : ‖(1 : ℚ_[l]) + l‖ = 1 := by
  have h1 : ‖(l : ℚ_[l])‖ < 1 := Padic.norm_p_lt_one
  have hne : ‖(1 : ℚ_[l])‖ ≠ ‖(l : ℚ_[l])‖ := by rw [norm_one]; exact ne_of_gt h1
  first
  | rw [padicNormE.add_eq_max_of_ne hne, norm_one]; exact max_eq_left h1.le
  | rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne, norm_one]; exact max_eq_left h1.le

/- English proof (translation)
Establish `hl : 2 ≤ l` using `(Fact.out : l.Prime).two_le`. Establish `key : (1 + l) ^ n ≠ 1` using `(Nat.one_lt_pow (by omega) (by omega)).ne'`. Introduce `h`. Apply `key` to reduce the goal to its premises. Conclude with `h` after adjusting the coercions.
-/
private lemma zmod_pow_ne_one_of_pow_mod_ne_one (l : ℕ) [Fact l.Prime] (n : ℕ) (hn : 0 < n) :
    ((1 : ℚ_[l]) + l) ^ n ≠ 1 := by
  have hl : 2 ≤ l := (Fact.out : l.Prime).two_le
  have key : (1 + l) ^ n ≠ 1 := (Nat.one_lt_pow (by omega) (by omega)).ne'
  intro h
  apply key
  exact_mod_cast h

/- English proof (translation)
Introduce `l _ χ hχ K e he`. Take `⟨σ, -, hσ⟩` from `exists_chi_eq K χ hχ _ (norm_one_add_prime_padic l)`. Establish `hK : FiniteDimensional ℚ_[l] ↥K.1` using `K.2`. Set `f : ℕ → (↥K.1 →ₐ[ℚ_[l]] Om l)` to `fun n => (AlgEquiv.toAlgHom (σ ^ n : Om l ≃ₐ[ℚ_[l]] Om l)).comp (IntermediateField.val K.1)`. Take `⟨i, j, hij, hfij⟩` from `Finite.exists_ne_map_eq_of_infinite f`.

Establish `key : ∀ a b : ℕ, a < b → f a = f b → ∃ g ∈ GK K, (χ g : ℚ_[l]) ^ e ≠ 1`. Introduce `a b hab hfab`. Use `⟨σ ^ (b - a), ?_, ?_⟩` and prove the remaining obligations. Unfold `GK`. Rewrite using `[IntermediateField.mem_fixingSubgroup_iff]`.

Introduce `x hx`. Establish `h1 : (σ ^ a) x = (σ ^ b) x` using `congrArg (fun φ : ↥K.1 →ₐ[ℚ_[l]] Om l => φ ⟨x, hx⟩) hfab`. Establish `hb : σ ^ b = σ ^ a * σ ^ (b - a)`. Rewrite using `[← pow_add]`. Use `congr 1`.

Use linear arithmetic over natural numbers and integers. Rewrite `h1` using `[hb, AlgEquiv.mul_apply]`. Conclude with `((σ ^ a).injective h1).symm`. Rewrite using `[map_pow, Units.val_pow_eq_pow_val, hσ, ← pow_mul]`. Conclude with `zmod_pow_ne_one_of_pow_mod_ne_one l _ (Nat.mul_pos (by omega) he)`.

Break down `lt_or_gt_of_ne hij with h | h` into its components or cases. Conclude with `key i j h hfij`. Conclude with `key j i h hfij.symm`.
-/
theorem exists_mem_GK_chi_pow_ne_one : ∀ (l : ℕ) [Fact l.Prime] (χ : GQ l →* ℚ_[l]ˣ), IsCyc χ →
    ∀ (K : FinExt l) (e : ℕ), 0 < e → ∃ g ∈ GK K, (χ g : ℚ_[l]) ^ e ≠ 1 := by
  intro l _ χ hχ K e he

  obtain ⟨σ, -, hσ⟩ := exists_chi_eq K χ hχ _ (norm_one_add_prime_padic l)
  have hK : FiniteDimensional ℚ_[l] ↥K.1 := K.2

  let f : ℕ → (↥K.1 →ₐ[ℚ_[l]] Om l) := fun n =>
    (AlgEquiv.toAlgHom (σ ^ n : Om l ≃ₐ[ℚ_[l]] Om l)).comp (IntermediateField.val K.1)
  obtain ⟨i, j, hij, hfij⟩ := Finite.exists_ne_map_eq_of_infinite f

  have key : ∀ a b : ℕ, a < b → f a = f b → ∃ g ∈ GK K, (χ g : ℚ_[l]) ^ e ≠ 1 := by
    intro a b hab hfab
    refine ⟨σ ^ (b - a), ?_, ?_⟩
    · unfold GK
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      have h1 : (σ ^ a) x = (σ ^ b) x :=
        congrArg (fun φ : ↥K.1 →ₐ[ℚ_[l]] Om l => φ ⟨x, hx⟩) hfab
      have hb : σ ^ b = σ ^ a * σ ^ (b - a) := by
        rw [← pow_add]
        congr 1
        omega
      rw [hb, AlgEquiv.mul_apply] at h1
      exact ((σ ^ a).injective h1).symm
    · rw [map_pow, Units.val_pow_eq_pow_val, hσ, ← pow_mul]
      exact zmod_pow_ne_one_of_pow_mod_ne_one l _ (Nat.mul_pos (by omega) he)
  rcases lt_or_gt_of_ne hij with h | h
  · exact key i j h hfij
  · exact key j i h hfij.symm

end GlobalTheory.Cyc
