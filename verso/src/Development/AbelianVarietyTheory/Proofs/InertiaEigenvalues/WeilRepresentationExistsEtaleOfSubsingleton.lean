import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitting
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section
namespace GlobalTheory.JR

/- English proof (translation)
Establish `h01 : (0 : A.L) = 1`. Rewrite using `[← map_zero (algebraMap A.K A.L), ← map_one (algebraMap A.K A.L), Subsingleton.elim (0 : A.K) 1]`. Use `haveI hL : Subsingleton A.L := subsingleton_of_zero_eq_one h01`. Establish `hpsi : ∀ (ψ : AddChar F ℂ), IsStdChar ψ → ∀ t : A.K, A.psiK ψ t = 1`. Introduce `ψ _ t`.

Unfold `Et.psiK`. Rewrite using `[Subsingleton.elim t 0, map_zero, AddChar.map_zero_eq_one]`. Introduce `ψ hψ x μ hμ`. Use `haveI := hμ.1`. Establish `hpos : 0 < μ Set.univ` using `(isOpen_univ.measure_pos μ Set.univ_nonempty)`.

Establish `hfin : μ Set.univ < ⊤` using `isCompact_univ.measure_lt_top`. Establish `hreal : μ.real Set.univ ≠ 0`. Rewrite using `[measureReal_def]`. Conclude with `(ENNReal.toReal_pos hpos.ne' hfin.ne).ne'`. Use `⟨(μ.real Set.univ : ℂ)⁻¹, fun _ φ => φ, ?_, ?_⟩` and prove the remaining obligations.

Conclude with `⟨fun _ _ hf => hf, fun _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ _ _ _ _ => rfl⟩`. Introduce `φ _`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `z y`. Simplify using `[hpsi ψ hψ]`.

Introduce `s y`. Establish `he : A.etaK (s : A.K) = 1`. Unfold `Et.etaK eta`. Rewrite using `[Subsingleton.elim (s : A.K) 1, map_one]`. Rewrite using `[if_pos ⟨1, by simp⟩]`.

Establish `ha : A.absK (s : A.K) = 1`. Unfold `Et.absK`. Rewrite using `[dif_pos s.isUnit]`. Rewrite using `[Subsingleton.elim (s.isUnit.unit) 1, map_one]`. Both sides reduce to the same expression.

Rewrite using `[he, ha, Subsingleton.elim ((s : A.K) • y) y]`. Simplify using the standard rewrite rules. Introduce `y`. Unfold `fourB`. Establish `: (fun x' => φ x' * A.kerL ψ x x' y) = fun _ => φ y`.

Use function extensionality and compare the values at `x'`. Unfold `Et.kerL`. Rewrite using `[hpsi ψ hψ, Subsingleton.elim x' y, mul_one]`. Rewrite using `[this, integral_const, Complex.real_smul]`. Use `show φ y = _`.

Establish `hc : ((μ.real Set.univ : ℝ) : ℂ) ≠ 0` using `by exact_mod_cast hreal`. Clear the denominators using the available nonvanishing facts.
-/
theorem weilAt_of_subsingleton (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (hK : Subsingleton A.K) : WeilAt A := by
  have h01 : (0 : A.L) = 1 := by
    rw [← map_zero (algebraMap A.K A.L), ← map_one (algebraMap A.K A.L), Subsingleton.elim (0 : A.K) 1]
  haveI hL : Subsingleton A.L := subsingleton_of_zero_eq_one h01
  have hpsi : ∀ (ψ : AddChar F ℂ), IsStdChar ψ → ∀ t : A.K, A.psiK ψ t = 1 := by
    intro ψ _ t
    unfold Et.psiK
    rw [Subsingleton.elim t 0, map_zero, AddChar.map_zero_eq_one]
  intro ψ hψ x μ hμ
  haveI := hμ.1
  have hpos : 0 < μ Set.univ := (isOpen_univ.measure_pos μ Set.univ_nonempty)
  have hfin : μ Set.univ < ⊤ := isCompact_univ.measure_lt_top
  have hreal : μ.real Set.univ ≠ 0 := by
    rw [measureReal_def]; exact (ENNReal.toReal_pos hpos.ne' hfin.ne).ne'
  refine ⟨(μ.real Set.univ : ℂ)⁻¹, fun _ φ => φ, ?_, ?_⟩
  · exact ⟨fun _ _ hf => hf, fun _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ _ _ _ _ => rfl⟩
  · intro φ _
    refine ⟨?_, ?_, ?_⟩
    · intro z y; simp [hpsi ψ hψ]
    · intro s y
      have he : A.etaK (s : A.K) = 1 := by
        unfold Et.etaK eta
        rw [Subsingleton.elim (s : A.K) 1, map_one]
        rw [if_pos ⟨1, by simp⟩]
      have ha : A.absK (s : A.K) = 1 := by
        unfold Et.absK
        rw [dif_pos s.isUnit]
        rw [Subsingleton.elim (s.isUnit.unit) 1, map_one]
        rfl
      rw [he, ha, Subsingleton.elim ((s : A.K) • y) y]
      simp
    · intro y
      unfold fourB
      have : (fun x' => φ x' * A.kerL ψ x x' y) = fun _ => φ y := by
        funext x'
        unfold Et.kerL
        rw [hpsi ψ hψ, Subsingleton.elim x' y, mul_one]
      rw [this, integral_const, Complex.real_smul]
      show φ y = _
      have hc : ((μ.real Set.univ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hreal
      field_simp

end GlobalTheory.JR
