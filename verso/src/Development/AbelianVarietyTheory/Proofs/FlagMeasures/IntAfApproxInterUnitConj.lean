import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsDual
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsReduction

open MeasureTheory Formalism.MainNotions.S GlobalTheory.RowLev NumberField IsDedekindDomain Matrix
open scoped InnerProductSpace ComplexOrder TensorProduct Pointwise Classical

namespace GlobalTheory.RowLev

open MeasureTheory NumberField IsDedekindDomain Matrix in
open scoped InnerProductSpace ComplexOrder TensorProduct Pointwise Classical in

/- English proof (translation)
Introduce `I g hg`. Establish `hg0 : g ≠ 0` using `by omega`. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `z hz`. Take `⟨b, t, hbt⟩` from `_root_.GlobalTheory.RowLev.Inhab.exists_approx (F := I.F) (E := I.E) hg0 ⟨z, hz⟩`.

Use `⟨b, t, t.2, ?_⟩` and prove the remaining obligations. Establish `h` using `congrArg Subtype.val hbt`. Simplify `h` using `[_root_.GlobalTheory.RowLev.Inhab.psi]`. Introduce `a`. Prove the components needed by the constructor for the conclusion.

Introduce `ha`. Establish `hint : IsIntegral ℤ a` using `_root_.Formalism.UG.P.csGlob_int a ha`. Conclude with `⟨⟨a, hint⟩, rfl⟩`. Introduce and unpack `⟨b, rfl⟩`. Conclude with `_root_.Formalism.UG.CS.incl_int b`.

Establish `hF : IsUnit (g : I.F)` using `isUnit_iff_ne_zero.mpr (by exact_mod_cast hg0)`. Simplify using `using hF.map (algebraMap I.F (I.E ⊗[I.F] _root_.Formalism.MainNotions.S.Af I.F))`. Introduce `z hz`. Conclude with `_root_.Formalism.UG.P.csDual_sig_mem _ hz`.
-/
theorem _root_.GlobalTheory.RowLev.intAf_approx_inter_unit_conj : ∀ (I : _root_.Formalism.MainNotions.S.AutInst) (g : ℕ), 1 ≤ g →
    (∀ z ∈ _root_.Formalism.MainNotions.S.IntAf I.F I.E, ∃ a : 𝓞 I.E, ∃ z' ∈ _root_.Formalism.MainNotions.S.IntAf I.F I.E,
      z = _root_.Formalism.UG.inclE (F := I.F) (_root_.Formalism.MainNotions.S.Af I.F) (a : I.E) + (g : (I.E ⊗[I.F] _root_.Formalism.MainNotions.S.Af I.F)) * z') ∧
    (∀ a : I.E, _root_.Formalism.UG.inclE (F := I.F) (_root_.Formalism.MainNotions.S.Af I.F) a ∈ _root_.Formalism.MainNotions.S.IntAf I.F I.E ↔
      a ∈ (algebraMap (𝓞 I.E) I.E).range) ∧
    IsUnit (g : (I.E ⊗[I.F] _root_.Formalism.MainNotions.S.Af I.F)) ∧
    ∀ z ∈ _root_.Formalism.MainNotions.S.IntAf I.F I.E, _root_.Formalism.UG.sigR I.cm.sig (_root_.Formalism.MainNotions.S.Af I.F) z ∈ _root_.Formalism.MainNotions.S.IntAf I.F I.E := by
  intro I g hg
  have hg0 : g ≠ 0 := by omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro z hz
    obtain ⟨b, t, hbt⟩ := _root_.GlobalTheory.RowLev.Inhab.exists_approx (F := I.F) (E := I.E) hg0 ⟨z, hz⟩
    refine ⟨b, t, t.2, ?_⟩
    have h := congrArg Subtype.val hbt
    simpa [_root_.GlobalTheory.RowLev.Inhab.psi] using h
  · intro a
    constructor
    · intro ha
      have hint : IsIntegral ℤ a := _root_.Formalism.UG.P.csGlob_int a ha
      exact ⟨⟨a, hint⟩, rfl⟩
    · rintro ⟨b, rfl⟩
      exact _root_.Formalism.UG.CS.incl_int b
  · have hF : IsUnit (g : I.F) := isUnit_iff_ne_zero.mpr (by exact_mod_cast hg0)
    simpa using hF.map (algebraMap I.F (I.E ⊗[I.F] _root_.Formalism.MainNotions.S.Af I.F))
  · intro z hz
    exact _root_.Formalism.UG.P.csDual_sig_mem _ hz

end GlobalTheory.RowLev
