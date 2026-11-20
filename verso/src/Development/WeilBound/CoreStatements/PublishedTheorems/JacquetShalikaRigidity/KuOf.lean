import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.ColumnConjugationMeasure

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

/- English proof (translation)
Introduce `hG hD E _ _ _ k ψ hψ φ u hφ h1`. Take `⟨-, -, -, hW⟩` from `hG E k ψ hψ`. Establish `hWc : Continuous (Wh ψ φ)` using `(hW φ hφ).1`. Take `⟨hpos, hmul, hcont, -⟩` from `hD E k`. Establish `hD1 : Dt (1 : GA E k) = 1`.

Establish `h` using `hmul 1 1`. Rewrite `h` using `[show (1 : GA E k) * 1 = 1 from mul_one 1]`. Conclude with `mul_left_cancel₀ (hpos 1).ne' (h.symm.trans (mul_one _).symm)`. Use `set F : GA E k → ℂ := fun c => conj (Wh ψ φ c) * (Dt c : ℂ) ^ ((u : ℂ) * Complex.I) with hF`. Establish `hDc : Continuous fun c : GA E k => (Dt c : ℂ)` using `Complex.continuous_ofReal.comp hcont`.

Establish `hFc : Continuous F` using `(Complex.continuous_conj.comp hWc).mul (hDc.cpow continuous_const fun c => Complex.ofReal_mem_slitPlane.2 (hpos c))`. Establish `hF1 : F 1 = 1` using `by simp [F, h1, hD1]`. Use `⟨{c | Dt c ∈ Set.Ioo (1 / 2 : ℝ) 2} ∩ {c | 0 < (F c).re}, ?_, ?_⟩` and prove the remaining obligations. Apply `IsOpen.mem_nhds` to reduce the goal to its premises. Conclude with `(isOpen_Ioo.preimage hcont).inter (isOpen_lt continuous_const (Complex.continuous_re.comp hFc))`.

Simplify using `only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_Ioo, hD1, hF1]`. Evaluate the numerical expressions. Introduce and unpack `c ⟨⟨ha, hb⟩, hc⟩`. Conclude with `⟨ha.le, hb.le, hc⟩`.
-/
theorem ku_of : jumpWindows.G5 → D0 → KU := by
  intro hG hD E _ _ _ k ψ hψ φ u hφ h1
  obtain ⟨-, -, -, hW⟩ := hG E k ψ hψ
  have hWc : Continuous (Wh ψ φ) := (hW φ hφ).1
  obtain ⟨hpos, hmul, hcont, -⟩ := hD E k
  have hD1 : Dt (1 : GA E k) = 1 := by
    have h := hmul 1 1
    rw [show (1 : GA E k) * 1 = 1 from mul_one 1] at h
    exact mul_left_cancel₀ (hpos 1).ne' (h.symm.trans (mul_one _).symm)
  set F : GA E k → ℂ := fun c => conj (Wh ψ φ c) * (Dt c : ℂ) ^ ((u : ℂ) * Complex.I) with hF
  have hDc : Continuous fun c : GA E k => (Dt c : ℂ) := Complex.continuous_ofReal.comp hcont
  have hFc : Continuous F := (Complex.continuous_conj.comp hWc).mul
    (hDc.cpow continuous_const fun c => Complex.ofReal_mem_slitPlane.2 (hpos c))
  have hF1 : F 1 = 1 := by simp [F, h1, hD1]
  refine ⟨{c | Dt c ∈ Set.Ioo (1 / 2 : ℝ) 2} ∩ {c | 0 < (F c).re}, ?_, ?_⟩
  · apply IsOpen.mem_nhds
    · exact (isOpen_Ioo.preimage hcont).inter (isOpen_lt continuous_const (Complex.continuous_re.comp hFc))
    · simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_Ioo, hD1, hF1]
      norm_num
  · rintro c ⟨⟨ha, hb⟩, hc⟩
    exact ⟨ha.le, hb.le, hc⟩

end PositivityTheory.AdelicQuotientData

end
