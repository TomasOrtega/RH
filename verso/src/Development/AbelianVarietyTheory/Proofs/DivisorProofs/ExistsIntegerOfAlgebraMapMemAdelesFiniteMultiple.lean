import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntFOneMul
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF GlobalTheory.HeckeExtend

namespace GlobalTheory.HeckeExtend

/- English proof (translation)
Introduce `F _ _ y m hm hy`. Take `⟨c, hc, e⟩` from `hy`. Establish `hmF : (m : F) ≠ 0` using `Nat.cast_ne_zero.2 hm.ne'`. Establish `key : ∀ v : HeightOneSpectrum (𝓞 F), v.valuation F (y / m) ≤ 1`. Introduce `v`.

Establish `h1 : (y : v.adicCompletion F) = ((m : F) : v.adicCompletion F) * c v`. Use `congrArg (fun a : FiniteAdeleRing (𝓞 F) F => a v) e` as an intermediate fact. Simplify using `only [nsmul_eq_mul] at this`. Establish `hL : (algebraMap F (AF F) y).2 v = (y : v.adicCompletion F)` using `rfl`. Establish `hm' : ((m : FiniteAdeleRing (𝓞 F) F)) = algebraMap F (FiniteAdeleRing (𝓞 F) F) (m : F)` using `(map_natCast _ m).symm`.

Establish `hR : ((m : FiniteAdeleRing (𝓞 F) F) * c) v = ((m : F) : v.adicCompletion F) * c v`. Rewrite using `[hm']`. Both sides reduce to the same expression. Rewrite using `[← hL, ← hR]`. Conclude with `this`.

Establish `h2 : v.valuation F y = v.valuation F (m : F) * Valued.v (c v)`. Rewrite using `[← HeightOneSpectrum.valuedAdicCompletion_eq_valuation', h1, map_mul, HeightOneSpectrum.valuedAdicCompletion_eq_valuation']`. Establish `hv0 : v.valuation F (m : F) ≠ 0` using `(Valuation.ne_zero_iff _).2 hmF`. Rewrite using `[map_div₀, h2, mul_div_cancel_left₀ _ hv0]`. Conclude with `(HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F v).1 (hc v)`.

Take `⟨r, hr⟩` from `HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 F) F (y / (m : F)) key`. Use `⟨r, ?_⟩` and prove the remaining obligations. Establish `: ((r : 𝓞 F) : F) = y / m` using `hr`. Rewrite using `[this, mul_div_cancel₀ _ hmF]`.
-/
theorem exists_int_of_mem_intF : ∀ (F : Type) [Field F] [NumberField F] (y : F) (m : ℕ), 0 < m →
    algebraMap F (AF F) y ∈ intF F m → ∃ r : 𝓞 F, y = m * r := by
  intro F _ _ y m hm hy
  obtain ⟨c, hc, e⟩ := hy
  have hmF : (m : F) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
  have key : ∀ v : HeightOneSpectrum (𝓞 F), v.valuation F (y / m) ≤ 1 := by
    intro v
    have h1 : (y : v.adicCompletion F) = ((m : F) : v.adicCompletion F) * c v := by
      have := congrArg (fun a : FiniteAdeleRing (𝓞 F) F => a v) e
      simp only [nsmul_eq_mul] at this
      have hL : (algebraMap F (AF F) y).2 v = (y : v.adicCompletion F) := rfl
      have hm' : ((m : FiniteAdeleRing (𝓞 F) F)) = algebraMap F (FiniteAdeleRing (𝓞 F) F) (m : F) :=
        (map_natCast _ m).symm
      have hR : ((m : FiniteAdeleRing (𝓞 F) F) * c) v = ((m : F) : v.adicCompletion F) * c v := by
        rw [hm']; rfl
      rw [← hL, ← hR]
      exact this
    have h2 : v.valuation F y = v.valuation F (m : F) * Valued.v (c v) := by
      rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation', h1, map_mul,
        HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    have hv0 : v.valuation F (m : F) ≠ 0 := (Valuation.ne_zero_iff _).2 hmF
    rw [map_div₀, h2, mul_div_cancel_left₀ _ hv0]
    exact (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F v).1 (hc v)
  obtain ⟨r, hr⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 F) F (y / (m : F)) key
  refine ⟨r, ?_⟩
  have : ((r : 𝓞 F) : F) = y / m := hr
  rw [this, mul_div_cancel₀ _ hmF]

end GlobalTheory.HeckeExtend
