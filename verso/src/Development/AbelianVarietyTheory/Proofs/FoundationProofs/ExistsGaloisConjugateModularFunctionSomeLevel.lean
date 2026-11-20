import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQPrin
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModJTau
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModularGroupRowVecAndConjRightActions
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitZetaAct
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CuspExpansionCoeffConjOfQExpansionConjStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsComplexRingEquivExtendingSubfieldAutStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LevelNFunctionGaloisConjQExpansionStatement
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

/- English proof (translation)
Introduce `Ω _ ε s f hf`. Take `⟨N, w, hN, hLv⟩` from `hf`. Use `haveI : NeZero N := ⟨hN.ne'⟩`. Take `⟨g, hg⟩` from `GlobalTheory.T.exists_complex_ringEquiv_extending_subfield_aut Ω ε s`. Establish `hgE : ∀ x ∈ ε.range, g x ∈ ε.range`.

Introduce and unpack `x ⟨y, rfl⟩`. Conclude with `⟨s y, (hg y).symm⟩`. Take `⟨d, hd⟩` from `GlobalTheory.WpFam.exists_unit_zetaAct N g`. Take `⟨f', hLv', hconj⟩` from `GlobalTheory.T.levelN_function_galois_conj_qExpansion g ε.range N d w f hgE hd hLv`. Use `⟨f', ⟨N, w, hN, hLv'⟩, ?_⟩` and prove the remaining obligations.

Introduce `h h' hh hh' r`. Establish `h1 : dg d * redGL N 1 = redGL N 1 * dg d`. Rewrite using `[GlobalTheory.WpFam.Act.redGL_one]`. Simplify using the standard rewrite rules. Establish `hc` using `hconj 1 1 h1`.

Simplify using `only [one_smul] at hc`. Establish `hq` using `hLv.2 1`. Simplify using `only [one_smul] at hq`. Conclude with `GlobalTheory.T.cuspExpansion_coeff_conj_of_qExpansion_conj Ω ε s.toRingHom g N w f f' h h' hg hN hq hc hh hh' r`.
-/
theorem exists_conj_of_inR : ∀ (Ω : Type) [Field Ω] (ε : Ω →+* ℂ) (s : Ω ≃+* Ω) (f : ℍ → ℂ), InR ε.range f → ∃ f' : ℍ → ℂ, InR ε.range f' ∧ ∀ h h' : HahnSeries ℚ Ω, IsExp ε f h → IsExp ε f' h' → ∀ r, h'.coeff r = s (h.coeff r) := by
  intro Ω _ ε s f hf
  obtain ⟨N, w, hN, hLv⟩ := hf
  haveI : NeZero N := ⟨hN.ne'⟩
  obtain ⟨g, hg⟩ := GlobalTheory.T.exists_complex_ringEquiv_extending_subfield_aut Ω ε s
  have hgE : ∀ x ∈ ε.range, g x ∈ ε.range := by
    rintro x ⟨y, rfl⟩
    exact ⟨s y, (hg y).symm⟩
  obtain ⟨d, hd⟩ := GlobalTheory.WpFam.exists_unit_zetaAct N g
  obtain ⟨f', hLv', hconj⟩ := GlobalTheory.T.levelN_function_galois_conj_qExpansion g ε.range N d w f hgE hd hLv
  refine ⟨f', ⟨N, w, hN, hLv'⟩, ?_⟩
  intro h h' hh hh' r
  have h1 : dg d * redGL N 1 = redGL N 1 * dg d := by
    rw [GlobalTheory.WpFam.Act.redGL_one]; simp
  have hc := hconj 1 1 h1
  simp only [one_smul] at hc
  have hq := hLv.2 1
  simp only [one_smul] at hq
  exact GlobalTheory.T.cuspExpansion_coeff_conj_of_qExpansion_conj Ω ε s.toRingHom g N w f f' h h' hg hN hq hc hh hh' r

end GlobalTheory.FN
