import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSplitChartSplitChart
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GSEqZeroOfLt

namespace GlobalTheory.StepFacNe

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

open NumberField IsDedekindDomain in

/- English proof (translation)
Unfold `_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.chrW`. Establish `h1` using `_root_.GlobalTheory.LFun.continuous_locChar h (_root_.GlobalTheory.AdelicU.splitPrime τ)`. Establish `h2` using `Continuous.units_map (_root_.GlobalTheory.LFun.complMap (_root_.GlobalTheory.AdelicU.splitPrime_under τ)).toMonoidHom (_root_.GlobalTheory.LFun.SplitChart.continuous_complMap (_root_.GlobalTheory.AdelicU.splitPrime_under τ))`. Conclude with `h1.comp h2`.
-/
theorem _root_.GlobalTheory.StepFacNe.chrW_continuous {F E : Type} [Field F] [NumberField F]
    [Field E] [NumberField E] [Algebra F E]
    (χ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E) (h : Continuous χ) {v : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F}
    (τ : E →ₐ[F] _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) :
    Continuous (fun x : (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)ˣ => (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.chrW χ τ x : ℂ)) := by
  unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.chrW
  have h1 := _root_.GlobalTheory.LFun.continuous_locChar h (_root_.GlobalTheory.AdelicU.splitPrime τ)
  have h2 := Continuous.units_map
    (_root_.GlobalTheory.LFun.complMap (_root_.GlobalTheory.AdelicU.splitPrime_under τ)).toMonoidHom
    (_root_.GlobalTheory.LFun.SplitChart.continuous_complMap (_root_.GlobalTheory.AdelicU.splitPrime_under τ))
  exact h1.comp h2

open NumberField IsDedekindDomain in

/- English proof (translation)
Establish `hw` using `_root_.GlobalTheory.AdelicU.splitPrime_under τ`. Unfold `_root_.GlobalTheory.LFun.UnrAt at h`. Use `push_neg at h`. Take `⟨y, hy1, hy2⟩` from `h`. Unfold `_root_.Formalism.L2.Host.IsUnitAt at hy1`.

Take `⟨a, ha⟩` from `(_root_.GlobalTheory.LFun.SplitTie.complMap_bijective τ hw).2 (y : _)`. Establish `hv : Valued.v a = 1`. Rewrite using `[← _root_.GlobalTheory.LFun.SplitTie.valued_complMap τ hw, ha]`. Conclude with `hy1`. Establish `ha0 : a ≠ 0`.

Introduce and unpack `rfl`. Simplify using `at hv`. Use `⟨Units.mk0 a ha0, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[HeightOneSpectrum.mem_adicCompletionIntegers]`. Simplify using `[hv]`.

Rewrite using `[HeightOneSpectrum.mem_adicCompletionIntegers]`. Simplify using `[hv]`. Introduce `h1`. Apply `hy2` to reduce the goal to its premises. Establish `hy : Units.map (_root_.GlobalTheory.LFun.complMap hw).toMonoidHom (Units.mk0 a ha0) = y` using `Units.ext (by simpa using ha)`.

Unfold `_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.chrW at h1`. Rewrite `h1` using `[MonoidHom.comp_apply, hy]`. Conclude with `h1`.
-/
theorem _root_.GlobalTheory.StepFacNe.chrW_ram {F E : Type} [Field F]
    [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (χ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E) {v : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F} (τ : E →ₐ[F] _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)
    (h : ¬ _root_.GlobalTheory.LFun.UnrAt χ (_root_.GlobalTheory.AdelicU.splitPrime τ)) :
    ∃ x : (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)ˣ, (x : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) ∈ v.adicCompletionIntegers F ∧
      ((x⁻¹ : (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)ˣ) : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) ∈ v.adicCompletionIntegers F ∧
        _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.chrW χ τ x ≠ 1 := by
  have hw := _root_.GlobalTheory.AdelicU.splitPrime_under τ
  unfold _root_.GlobalTheory.LFun.UnrAt at h
  push_neg at h
  obtain ⟨y, hy1, hy2⟩ := h
  unfold _root_.Formalism.L2.Host.IsUnitAt at hy1
  obtain ⟨a, ha⟩ := (_root_.GlobalTheory.LFun.SplitTie.complMap_bijective τ hw).2 (y : _)
  have hv : Valued.v a = 1 := by
    rw [← _root_.GlobalTheory.LFun.SplitTie.valued_complMap τ hw, ha]
    exact hy1
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp at hv
  refine ⟨Units.mk0 a ha0, ?_, ?_, ?_⟩
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    simp [hv]
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    simp [hv]
  · intro h1
    apply hy2
    have hy : Units.map (_root_.GlobalTheory.LFun.complMap hw).toMonoidHom (Units.mk0 a ha0) = y :=
      Units.ext (by simpa using ha)
    unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.chrW at h1
    rw [MonoidHom.comp_apply, hy] at h1
    exact h1

/- English proof (translation)
Establish `hB : Bounded (above E S) (charFam χ) 1 0`. Introduce `w _`. Unfold `charFam`. Use `split_ifs`. Use `⟨by simp, fun b hb => ?_⟩` and prove the remaining obligations.

Rewrite `hb` using `[Multiset.mem_singleton]`. Substitute `hb` using the available equality. Simplify using `[norm_val]`. Simplify using the standard rewrite rules. Establish `hc` using `hB.converges (s := (k : ℂ)) (by`.

Simplify using `only [Complex.natCast_re, zero_add]`. Conclude with `(by omega : 1 < k))` after adjusting the coercions. Conclude with `hc.ne_zero`.
-/
theorem charL_ne_zero {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (χ : Chr F E) (S : Set (Pl F)) (k : ℕ) (hk : 2 ≤ k) : charL χ S (k : ℂ) ≠ 0 := by
  have hB : Bounded (above E S) (charFam χ) 1 0 := by
    intro w _
    unfold charFam
    split_ifs
    · refine ⟨by simp, fun b hb => ?_⟩
      rw [Multiset.mem_singleton] at hb
      subst hb
      simp [norm_val]
    · simp
  have hc := hB.converges (s := (k : ℂ)) (by
    simp only [Complex.natCast_re, zero_add]
    exact_mod_cast (by omega : 1 < k))
  exact hc.ne_zero

end GlobalTheory.StepFacNe
