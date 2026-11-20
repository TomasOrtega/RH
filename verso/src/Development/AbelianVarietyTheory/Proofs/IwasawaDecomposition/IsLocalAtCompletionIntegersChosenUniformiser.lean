import Mathlib
import Formalism.LocalToGlobal.Divisibility.QLocTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.HostPins
import Formalism.DoubleCosetMeasures.LatticeCoset

open MeasureTheory Matrix NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DoubleCosetMeasures Formalism.L2.Host Formalism.L2.DIV Formalism.L2.DIV.QLoc GlobalTheory.Mem.HD

namespace GlobalTheory.Mem.HD

/- English proof (translation)
Proceed by induction on `g using WithZero.expRecOn with`. Consider the case `zero => simp`. Consider the case `exp a => rw [← WithZero.exp_zero, WithZero.exp_lt_exp, WithZero.exp_le_exp]`. Use linear arithmetic over natural numbers and integers.
-/
private theorem lt_one_iff_le_exp_neg_one (g : WithZero (Multiplicative ℤ)) :
    g < 1 ↔ g ≤ WithZero.exp (-1 : ℤ) := by
  induction g using WithZero.expRecOn with
  | zero => simp
  | exp a => rw [← WithZero.exp_zero, WithZero.exp_lt_exp, WithZero.exp_le_exp]; omega

/- English proof (translation)
Establish `hv : Valued.v ((piP P : (P.adicCompletion L)ˣ) : P.adicCompletion L) = WithZero.exp (-1 : ℤ)` using `unif_spec P`. Establish `hne : ((piP P : (P.adicCompletion L)ˣ) : P.adicCompletion L) ≠ 0` using `Units.ne_zero _`. Establish `mem : ∀ x : P.adicCompletion L, x ∈ OP P ↔ Valued.v x ≤ 1` using `fun x => HeightOneSpectrum.mem_adicCompletionIntegers (R := 𝓞 L) (K := L) (v := P)`. Establish `hexp : (0 : WithZero (Multiplicative ℤ)) < WithZero.exp (-1 : ℤ)` using `zero_lt_iff.2 WithZero.exp_ne_zero`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Introduce `h`. Establish `h1` using `(mem _).1 h`. Rewrite `h1` using `[map_inv₀, hv, ← WithZero.exp_neg, ← WithZero.exp_zero, WithZero.exp_le_exp]`. Use linear arithmetic over natural numbers and integers. Introduce `x hx hnot`.

Establish `hx1 : Valued.v x ≤ 1` using `(mem x).1 hx`. Establish `hx_eq : Valued.v x = 1`. Assume the negation of the conclusion as `hne1`. Establish `hlt : Valued.v x < 1` using `lt_of_le_of_ne hx1 hne1`. Establish `hle` using `(lt_one_iff_le_exp_neg_one _).1 hlt`.

Use `hnot (((piP P : (P.adicCompletion L)ˣ) : P.adicCompletion L)⁻¹ * x) ?_ ?_` and prove the remaining obligations. Rewrite using `[mem, map_mul, map_inv₀, hv]`. Conclude with `inv_mul_le_one_of_le₀ hle hexp.le`. Rewrite using `[mul_inv_cancel_left₀ hne]`. Rewrite using `[mem, map_inv₀, hx_eq, inv_one]`.
-/
theorem isLocalAt_adicCompletionIntegers_uniformizer (L : Type) [Field L] [NumberField L] (P : HeightOneSpectrum (𝓞 L)) :
    IsLocalAt (OP P) ((piP P : (P.adicCompletion L)ˣ) : P.adicCompletion L) := by
  have hv : Valued.v ((piP P : (P.adicCompletion L)ˣ) : P.adicCompletion L)
      = WithZero.exp (-1 : ℤ) := unif_spec P
  have hne : ((piP P : (P.adicCompletion L)ˣ) : P.adicCompletion L) ≠ 0 := Units.ne_zero _
  have mem : ∀ x : P.adicCompletion L, x ∈ OP P ↔ Valued.v x ≤ 1 := fun x =>
    HeightOneSpectrum.mem_adicCompletionIntegers (R := 𝓞 L) (K := L) (v := P)
  have hexp : (0 : WithZero (Multiplicative ℤ)) < WithZero.exp (-1 : ℤ) :=
    zero_lt_iff.2 WithZero.exp_ne_zero
  refine ⟨?_, ?_⟩
  · intro h
    have h1 := (mem _).1 h
    rw [map_inv₀, hv, ← WithZero.exp_neg, ← WithZero.exp_zero, WithZero.exp_le_exp] at h1
    omega
  · intro x hx hnot
    have hx1 : Valued.v x ≤ 1 := (mem x).1 hx
    have hx_eq : Valued.v x = 1 := by
      by_contra hne1
      have hlt : Valued.v x < 1 := lt_of_le_of_ne hx1 hne1
      have hle := (lt_one_iff_le_exp_neg_one _).1 hlt
      refine hnot (((piP P : (P.adicCompletion L)ˣ) : P.adicCompletion L)⁻¹ * x) ?_ ?_
      · rw [mem, map_mul, map_inv₀, hv]
        exact inv_mul_le_one_of_le₀ hle hexp.le
      · rw [mul_inv_cancel_left₀ hne]
    rw [mem, map_inv₀, hx_eq, inv_one]

end GlobalTheory.Mem.HD
