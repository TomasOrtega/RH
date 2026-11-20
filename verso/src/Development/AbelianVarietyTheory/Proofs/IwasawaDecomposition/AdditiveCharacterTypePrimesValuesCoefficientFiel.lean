import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
import Formalism.LocalToGlobal.HermitianForms.TiedTwJSym
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TC.PsiRat

/- English proof (translation)
Rewrite using `[← map_natCast (IsLocalRing.residue (v.adicCompletionIntegers F)), IsLocalRing.residue_eq_zero_iff]`. Use `(Valuation.mem_maximalIdeal_iff (v := (Valued.v : Valuation (v.adicCompletion F) _)) (a := (p : v.adicCompletionIntegers F))).2 ?_` and prove the remaining obligations. Establish `h1 : ((p : v.adicCompletionIntegers F) : v.adicCompletion F) = algebraMap F (v.adicCompletion F) ((p : 𝓞 F) : F)`. Simplify using the standard rewrite rules. Rewrite using `[h1]`.

Establish `h2` using `HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v ((p : 𝓞 F) : F)`. Establish `h3` using `(HeightOneSpectrum.valuation_lt_one_iff_mem (K := F) v (p : 𝓞 F)).2 h`. Conclude with `h2.trans_lt h3`.
-/
theorem natCast_resField_eq_zero (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (p : ℕ) (h : (p : 𝓞 F) ∈ v.asIdeal) : (p : kv F v) = 0 := by
  rw [← map_natCast (IsLocalRing.residue (v.adicCompletionIntegers F)), IsLocalRing.residue_eq_zero_iff]
  refine (Valuation.mem_maximalIdeal_iff (v := (Valued.v : Valuation (v.adicCompletion F) _))
    (a := (p : v.adicCompletionIntegers F))).2 ?_
  have h1 : ((p : v.adicCompletionIntegers F) : v.adicCompletion F) =
      algebraMap F (v.adicCompletion F) ((p : 𝓞 F) : F) := by
    simp
  rw [h1]
  have h2 := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v ((p : 𝓞 F) : F)
  have h3 := (HeightOneSpectrum.valuation_lt_one_iff_mem (K := F) v (p : 𝓞 F)).2 h
  exact h2.trans_lt h3

/- English proof (translation)
Establish `hp` using `B.host.g_prime i`. Apply the tactic sequence `obtain ⟨ζ, -, hζ⟩ := B.roots_Ks (B.host.g i * (B.host.g i - 1)) (by fin_cases i <;> simp)`. Establish `hne : B.host.g i * (B.host.g i - 1) ≠ 0` using `mul_ne_zero hp.ne_zero (by have := hp.two_le; omega)`. Establish `hprim` using `Complex.isPrimitiveRoot_exp _ hne`. Establish `: NeZero (B.host.g i * (B.host.g i - 1))` using `⟨hne⟩`.

Take `⟨k, -, hk⟩` from `hprim.eq_pow_of_pow_eq_one (ξ := z) (by rw [pow_mul, hz, one_pow])`. Conclude with `⟨ζ ^ k, by rw [map_pow, hζ, hk]⟩`.
-/
theorem range_of_pow_g (B : Base) (i : Fin 2) (z : ℂ) (hz : z ^ B.host.g i = 1) : ∃ r : B.LL, B.embLL r = z := by
  have hp := B.host.g_prime i
  obtain ⟨ζ, -, hζ⟩ := B.roots_Ks (B.host.g i * (B.host.g i - 1)) (by fin_cases i <;> simp)
  have hne : B.host.g i * (B.host.g i - 1) ≠ 0 := mul_ne_zero hp.ne_zero (by have := hp.two_le; omega)
  have hprim := Complex.isPrimitiveRoot_exp _ hne
  have : NeZero (B.host.g i * (B.host.g i - 1)) := ⟨hne⟩
  obtain ⟨k, -, hk⟩ := hprim.eq_pow_of_pow_eq_one (ξ := z) (by rw [pow_mul, hz, one_pow])
  exact ⟨ζ ^ k, by rw [map_pow, hζ, hk]⟩

end GlobalTheory.Mem.Col2.TC.PsiRat

open GlobalTheory.Mem.Col2.TC.PsiRat in

/- English proof (translation)
Introduce `B X I _ _ l Z G _ j v h x`. Use `range_of_pow_g B j _ ?_` and prove the remaining obligations. Rewrite using `[← AddChar.map_nsmul_eq_pow, nsmul_eq_mul]`. Establish `h0` using `natCast_resField_eq_zero _ v _ h`. Use `erw [h0]`.

Rewrite using `[zero_mul, AddChar.map_zero_eq_one]`.
-/
theorem GlobalTheory.Mem.Col2.TC.additiveCharacter_typePrimes_values_coefficientField : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (G : GLoc (I.rec7 l Z).host.F (I.rec7 l Z).host.E (sigD (I.rec7 l Z)) (I.rec7 l Z).host.g), I.IdG l Z G → ∀ j v h x, ∃ r : B.LL, B.embLL r = G.psi0 j v h x := by
  intro B X I _ _ l Z G _ j v h x
  refine range_of_pow_g B j _ ?_
  rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul]
  have h0 := natCast_resField_eq_zero _ v _ h
  erw [h0]
  rw [zero_mul, AddChar.map_zero_eq_one]

end
