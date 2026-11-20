import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQPrin
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModJTau
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmpPropsStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SlTwoDiagConjCongruenceIffDiagOneUnitMatrixEqStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CuspExpansionCoeffConjOfQExpansionConjStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsComplexRingEquivExtendingSubfieldAutStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LevelNFunctionGaloisConjQExpansionStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FractionFieldExtClosureInjectiveStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisExponentRootOfUnityExpTwoPiIStatement
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

/- English proof (translation)
Introduce `Ω _ _ _ ε T a N w hN hLv s d hs γ γ' hC`. Use `haveI : NeZero N := ⟨hN.ne'⟩`. Take `⟨g, hg⟩` from `GlobalTheory.T.exists_complex_ringEquiv_extending_subfield_aut Ω ε s.toRingEquiv`. Establish `hg' : ∀ x, g (ε x) = ε (s x)` using `hg`. Take `⟨u, hu, hZ⟩` from `(GlobalTheory.T.galois_exponent_rootOfUnity_expTwoPiI Ω ε s N hN).2 d hs`.

Establish `hE : ∀ x ∈ ε.range, g x ∈ ε.range`. Introduce and unpack `_ ⟨y, rfl⟩`. Conclude with `⟨s y, (hg' y).symm⟩`. Take `⟨f', hf'L, hf'C⟩` from `GlobalTheory.T.levelN_function_galois_conj_qExpansion g ε.range N u w (a : ℍ → ℂ) hE (hZ g hg') hLv`. Set `a' : GlobalTheory.FN.ring ε.range` to `⟨f', mem_ring_of_inR ⟨N, w, hN, hf'L⟩⟩`.

Take `⟨hext, hcmp, hexpinj, -⟩` from `GlobalTheory.T.fractionField_ext_closure_injective Ω ε T`. Take `⟨-, -, hSL, -⟩` from `GlobalTheory.T.cmp_mul_ofSL_and_up_cmp_eq_up_mob`. Establish `key : ∀ γ γ' : SL(2, ℤ), dg u * redGL N γ' = redGL N γ * dg u → T.gal s (T.sl (ofSL γ) (T.io a)) = T.sl (ofSL γ') (T.io a')`. Introduce `γ γ' hM`. Take `⟨b, hb, hbio⟩` from `hcmp (ofSL γ) a`.

Take `⟨b', hb', hb'io⟩` from `hcmp (ofSL γ') a'`. Rewrite using `[hbio, hb'io]`. Apply `hexpinj` to reduce the goal to its premises. Use extensionality with `r`. Rewrite using `[T.gal_exp]`.

Establish `hb1 : (b : ℍ → ℂ) = fun τ => (a : ℍ → ℂ) (γ • τ)` using `by rw [hb, hSL]`. Establish `hb2 : (b' : ℍ → ℂ) = fun τ => f' (γ' • τ)` using `by rw [hb', hSL]`. Use `Eq.symm ?_` and prove the remaining obligations. Use `GlobalTheory.T.cuspExpansion_coeff_conj_of_qExpansion_conj Ω ε s.toRingEquiv.toRingHom g N w b b' _ _ hg' hN ?_ ?_ (T.exp_io b) (T.exp_io b') r` and prove the remaining obligations. Rewrite using `[hb1]`.

Conclude with `hLv.2 γ`. Rewrite using `[hb1, hb2]`. Conclude with `hf'C γ γ' hM`. Establish `h1 : T.gal s (T.io a) = T.io a'`. Establish `hM1 : dg u * redGL N 1 = redGL N 1 * dg u` using `by simp [redGL]`.

Use `key 1 1 hM1` as an intermediate fact. Take `⟨c, hc, hcio⟩` from `hcmp (ofSL 1) a`. Take `⟨c', hc', hc'io⟩` from `hcmp (ofSL 1) a'`. Establish `e1 : c = a` using `Subtype.ext (by rw [hc, hSL]; funext τ; simp)`. Establish `e2 : c' = a'` using `Subtype.ext (by rw [hc', hSL]; funext τ; simp [a'])`.

Rewrite `this` using `[hcio, hc'io, e1, e2]`. Conclude with `this`. Rewrite using `[h1]`. Conclude with `key γ γ' ((GlobalTheory.T.slTwoDiagConjCongruence_iff_diagOneUnit_matrix_eq N d u hu γ γ').mp hC)`.
-/
theorem gal_sl_io_of_cong :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Frac Ω ε) (a : GlobalTheory.FN.ring ε.range) (N w : ℕ), 0 < N → Lv ε.range N w a → ∀ (s : Ω ≃ₐ[ℚ] Ω) (d : ℤ), s (eOm ε (1 / N)) = eOm ε (1 / N) ^ d → ∀ γ γ' : SL(2, ℤ), Cong N d γ γ' → T.gal s (T.sl (ofSL γ) (T.io a)) = T.sl (ofSL γ') (T.gal s (T.io a)) := by
  intro Ω _ _ _ ε T a N w hN hLv s d hs γ γ' hC
  haveI : NeZero N := ⟨hN.ne'⟩
  obtain ⟨g, hg⟩ := GlobalTheory.T.exists_complex_ringEquiv_extending_subfield_aut Ω ε s.toRingEquiv
  have hg' : ∀ x, g (ε x) = ε (s x) := hg
  obtain ⟨u, hu, hZ⟩ := (GlobalTheory.T.galois_exponent_rootOfUnity_expTwoPiI Ω ε s N hN).2 d hs
  have hE : ∀ x ∈ ε.range, g x ∈ ε.range := by
    rintro _ ⟨y, rfl⟩
    exact ⟨s y, (hg' y).symm⟩
  obtain ⟨f', hf'L, hf'C⟩ := GlobalTheory.T.levelN_function_galois_conj_qExpansion g ε.range N u w (a : ℍ → ℂ) hE (hZ g hg') hLv
  let a' : GlobalTheory.FN.ring ε.range := ⟨f', mem_ring_of_inR ⟨N, w, hN, hf'L⟩⟩
  obtain ⟨hext, hcmp, hexpinj, -⟩ := GlobalTheory.T.fractionField_ext_closure_injective Ω ε T
  obtain ⟨-, -, hSL, -⟩ := GlobalTheory.T.cmp_mul_ofSL_and_up_cmp_eq_up_mob

  have key : ∀ γ γ' : SL(2, ℤ), dg u * redGL N γ' = redGL N γ * dg u →
      T.gal s (T.sl (ofSL γ) (T.io a)) = T.sl (ofSL γ') (T.io a') := by
    intro γ γ' hM
    obtain ⟨b, hb, hbio⟩ := hcmp (ofSL γ) a
    obtain ⟨b', hb', hb'io⟩ := hcmp (ofSL γ') a'
    rw [hbio, hb'io]
    apply hexpinj
    ext r
    rw [T.gal_exp]
    have hb1 : (b : ℍ → ℂ) = fun τ => (a : ℍ → ℂ) (γ • τ) := by rw [hb, hSL]
    have hb2 : (b' : ℍ → ℂ) = fun τ => f' (γ' • τ) := by rw [hb', hSL]
    refine Eq.symm ?_
    refine GlobalTheory.T.cuspExpansion_coeff_conj_of_qExpansion_conj Ω ε s.toRingEquiv.toRingHom g N w b b' _ _ hg' hN ?_ ?_ (T.exp_io b) (T.exp_io b') r
    · rw [hb1]; exact hLv.2 γ
    · rw [hb1, hb2]; exact hf'C γ γ' hM
  have h1 : T.gal s (T.io a) = T.io a' := by
    have hM1 : dg u * redGL N 1 = redGL N 1 * dg u := by simp [redGL]
    have := key 1 1 hM1
    obtain ⟨c, hc, hcio⟩ := hcmp (ofSL 1) a
    obtain ⟨c', hc', hc'io⟩ := hcmp (ofSL 1) a'
    have e1 : c = a := Subtype.ext (by rw [hc, hSL]; funext τ; simp)
    have e2 : c' = a' := Subtype.ext (by rw [hc', hSL]; funext τ; simp [a'])
    rw [hcio, hc'io, e1, e2] at this
    exact this
  rw [h1]
  exact key γ γ' ((GlobalTheory.T.slTwoDiagConjCongruence_iff_diagOneUnit_matrix_eq N d u hu γ γ').mp hC)

end GlobalTheory.FN
