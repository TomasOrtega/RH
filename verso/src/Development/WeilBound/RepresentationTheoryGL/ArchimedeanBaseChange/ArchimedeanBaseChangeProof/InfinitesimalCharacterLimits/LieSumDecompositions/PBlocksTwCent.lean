import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.AllLeaves
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PExpTwA

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockTwistCharacters

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.
-/
theorem central_mulChi {a : ℕ} (e w : ℂ) (ψ : Sm E a)
    (hψ : ∀ (t : ℝ) m, ψ.1 (splitCentre E a t * m) = Complex.exp (e * t) * ψ.1 m) (t : ℝ) (m : GA E a) :
    (mulChi a (Model.absC E w) ψ).1 (splitCentre E a t * m) =
      Complex.exp ((e + w * a * (Module.finrank ℚ E : ℂ)) * t) * (mulChi a (Model.absC E w) ψ).1 m := by
  rw [mulChi_apply, mulChi_apply, map_mul, Units.val_mul, hψ, ExponentTwist.splitCentre_eq, ExponentTwist.chiDet_aT le_rfl,
    add_mul, Complex.exp_add]
  ring

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. A detailed English derivation is pending.
-/
theorem centIm_tw {a : ℕ} (V : Submodule ℂ (Sm E a)) (e w : ℂ) (he : (e + w * a * (Module.finrank ℚ E : ℂ)).re = 0)
    (hV : ∀ φ ∈ V, ∀ (t : ℝ) m, φ.1 (splitCentre E a t * m) = Complex.exp (e * t) * φ.1 m) :
    SpectralAccumulation.CentIm (tw V w) := by
  refine ⟨_, he, fun φ hφ t g => ?_⟩
  obtain ⟨ψ, hψ, rfl⟩ := Submodule.mem_map.1 hφ
  exact central_mulChi e w ψ (hV ψ hψ) t g

omit [IsCMField E] in
/- English proof (translation)
Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem finrank_ne_zero' : (Module.finrank ℚ E : ℝ) ≠ 0 := by
  have : 0 < Module.finrank ℚ E := Module.finrank_pos
  exact_mod_cast this.ne'

/- English proof (translation)
Establish an intermediate fact. Replace the relevant objects with their definitions. Move the embeddings inside the algebraic operations. Clear the denominators using the available nonvanishing facts. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem re_of_pE {r s : ℕ} {c : ℂ} (hc : pE E (r + s) r c = 0) :
    c.re = (r : ℝ) * s * (Module.finrank ℚ E : ℝ) / 2 := by
  have hd := finrank_ne_zero' (E := E)
  unfold pE at hc
  push_cast at hc
  field_simp at hc
  linarith

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact. Apply the first step, then apply the next step to every resulting obligation. Rewrite the conclusion using the stated equalities.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem centIm_left {r s : ℕ} (V : Submodule ℂ (Sm E r)) {c : ℂ} (hc : pE E (r + s) r c = 0)
    (hV : ∀ φ ∈ V, ∀ (t : ℝ) m, φ.1 (splitCentre E r t * m) = Complex.exp (c * t) * φ.1 m) :
    SpectralAccumulation.CentIm (tw V (-(s : ℂ) / 2)) := by
  refine centIm_tw V c _ ?_ hV
  have h := re_of_pE (E := E) hc
  have e1 : (c + -(s : ℂ) / 2 * r * (Module.finrank ℚ E : ℂ)).re = c.re - (s : ℝ) / 2 * r * (Module.finrank ℚ E : ℝ) := by
    simp [Complex.add_re, Complex.mul_re, Complex.neg_re] <;> ring_nf
  rw [e1, h]; ring

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact. Apply the first step, then apply the next step to every resulting obligation. Rewrite the conclusion using the stated equalities.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem centIm_right {r s : ℕ} (V : Submodule ℂ (Sm E s)) {c : ℂ} (hc : pE E (r + s) r c = 0)
    (hV : ∀ φ ∈ V, ∀ (t : ℝ) m, φ.1 (splitCentre E s t * m) = Complex.exp (-c * t) * φ.1 m) :
    SpectralAccumulation.CentIm (tw V ((r : ℂ) / 2)) := by
  refine centIm_tw V (-c) _ ?_ hV
  have h := re_of_pE (E := E) hc
  have e1 : (-c + (r : ℂ) / 2 * s * (Module.finrank ℚ E : ℂ)).re = -c.re + (r : ℝ) / 2 * s * (Module.finrank ℚ E : ℝ) := by
    simp [Complex.add_re, Complex.mul_re, Complex.neg_re] <;> ring_nf
  rw [e1, h]; ring

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockTwistCharacters

end
