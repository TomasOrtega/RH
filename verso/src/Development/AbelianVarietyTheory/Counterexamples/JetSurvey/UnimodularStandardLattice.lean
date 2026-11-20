import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.ThetaSpanAdjoint

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Survey.UnimodularStandardLattice

open NumberField Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

omit [IsCMField E] in
/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem mem_stdLat (v : Fin n → E) : v ∈ stdLat E n ↔ ∀ j, ∃ b : 𝓞 E, (b : E) = v j := by
  simp [stdLat, Submodule.mem_pi, Submodule.mem_one]

set_option autoImplicit false in
open NumberField in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} in
/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Fix the arbitrary inputs or assume the hypotheses. Supply the required witnesses or components. A detailed English derivation is pending.
-/
private lemma mem_range_algebraMap_iff_isIntegral_int (x : E) :
    x ∈ (algebraMap (𝓞 E) E).range ↔ IsIntegral ℤ x := by
  constructor
  · rintro ⟨y, rfl⟩
    exact RingOfIntegers.isIntegral_coe y
  · intro h
    exact ⟨⟨x, h⟩, rfl⟩

set_option autoImplicit false in
open NumberField in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} in
/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Simplify to obtain the desired conclusion from the available facts.
-/
private lemma complexConj_mem_integers_iff (x : E) :
    IsCMField.complexConj E x ∈ (algebraMap (𝓞 E) E).range ↔
      x ∈ (algebraMap (𝓞 E) E).range := by
  rw [mem_range_algebraMap_iff_isIntegral_int, mem_range_algebraMap_iff_isIntegral_int]
  refine ⟨fun h => ?_, fun h => h.map (IsCMField.complexConj E)⟩
  simpa using h.map (IsCMField.complexConj E).symm

set_option autoImplicit false in
open NumberField in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} in

/- English proof (translation)
Replace the relevant objects with their definitions. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem _root_.GlobalTheory.Survey.UnimodularStandardLattice.unimod_std :
    (⟨_root_.Formalism.L2.Pj.stdLat E n⟩ : _root_.Formalism.L2.Pj.GenLat E n).Unimod := by
  unfold _root_.Formalism.L2.Pj.GenLat.Unimod _root_.Formalism.L2.Pj.stdLat
  intro v
  simp only [Submodule.mem_pi, Set.mem_univ, true_implies, Submodule.mem_one,
    ← RingHom.mem_range]
  constructor
  · intro hv w hw
    exact Subring.sum_mem _ fun j _ =>
      Subring.mul_mem _ ((complexConj_mem_integers_iff (v j)).2 (hv j)) (hw j)
  · intro h i
    have hs := h (Pi.single i 1) fun j => by
      rw [Pi.single_apply]
      split_ifs
      · exact Subring.one_mem _
      · exact Subring.zero_mem _
    simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true] at hs
    exact (complexConj_mem_integers_iff (v i)).1 hs

omit [IsCMField E] in

/- English proof (translation)
Supply the required witnesses or components.
-/
theorem trivAt_std (bad : ℕ) : (⟨stdLat E n⟩ : GenLat E n).TrivAt bad :=
  ⟨1, by simp, Submodule.smul_le_right, Submodule.smul_le_right⟩

variable {H : Host E} {Dw : Datum H} {l : Level H}

end GlobalTheory.Survey.UnimodularStandardLattice
