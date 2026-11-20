import Mathlib
import ReciprocityTheory.DualLattices.Imports
import ReciprocityTheory.DualLattices.CyclicRecursion
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ValuationCoeEqNorm

open WittVector Ideal ReciprocityTheory.PGsh

namespace GlobalTheory.AinfChecks

open WittVector Ideal in

/- English proof (translation)
Take `⟨hunit, hcomp, ε, hv, hε⟩` from `_root_.GlobalTheory.PadicComplexHost.main p`. Establish `hker : _root_.ReciprocityTheory.PGsh.KerThetaStatement p 𝓞_ℂ_[p]` using `_root_.ReciprocityTheory.PGsh.kerTheta ℂ_[p] Valued.v hv`. Use `⟨hunit, hcomp, _root_.ReciprocityTheory.PGsh.exists_pflat ℂ_[p] Valued.v 𝓞_ℂ_[p] hv, ⟨ε, hε⟩, hker, _root_.ReciprocityTheory.PGsh.xiNu p ℂ_[p] Valued.v 𝓞_ℂ_[p] hker, ?_, _root_.ReciprocityTheory.PGsh.flatW' p 𝓞_ℂ_[p]⟩` and prove the remaining obligations. Use `_root_.ReciprocityTheory.PGsh.regular p 𝓞_ℂ_[p] fun x hx => ?_` and prove the remaining obligations. Establish `h : ((p : ℂ_[p]) * (x : ℂ_[p])) = 0`.

Simplify using `using congrArg (fun y : 𝓞_ℂ_[p] => (y : ℂ_[p])) hx`. Break down `mul_eq_zero.mp h with h | h` into its components or cases. Conclude with `absurd h (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)`. Conclude with `Subtype.ext h`.
-/
theorem _root_.GlobalTheory.AinfChecks.padicComplex (p : ℕ) [Fact p.Prime] :
    ∃ (_ : Fact ¬IsUnit ((p : ℕ) : 𝓞_ℂ_[p])) (_ : IsAdicComplete (span {((p : ℕ) : 𝓞_ℂ_[p])}) 𝓞_ℂ_[p]),
      (∃ pflat : PreTilt 𝓞_ℂ_[p] p, pflat.untilt = ((p : ℕ) : 𝓞_ℂ_[p])) ∧
      (∃ ε : PreTilt 𝓞_ℂ_[p] p,
        IsPrimitiveRoot (((frobeniusEquiv (PreTilt 𝓞_ℂ_[p] p) p).symm ε).untilt) p) ∧
      _root_.ReciprocityTheory.PGsh.KerThetaStatement p 𝓞_ℂ_[p] ∧ _root_.ReciprocityTheory.PGsh.XiNuStatement p ℂ_[p] Valued.v 𝓞_ℂ_[p] ∧
      _root_.ReciprocityTheory.PGsh.RegularStatement p 𝓞_ℂ_[p] ∧ _root_.ReciprocityTheory.PGsh.FlatW'Statement p 𝓞_ℂ_[p] := by
  obtain ⟨hunit, hcomp, ε, hv, hε⟩ := _root_.GlobalTheory.PadicComplexHost.main p
  have hker : _root_.ReciprocityTheory.PGsh.KerThetaStatement p 𝓞_ℂ_[p] := _root_.ReciprocityTheory.PGsh.kerTheta ℂ_[p] Valued.v hv
  refine ⟨hunit, hcomp, _root_.ReciprocityTheory.PGsh.exists_pflat ℂ_[p] Valued.v 𝓞_ℂ_[p] hv, ⟨ε, hε⟩, hker,
    _root_.ReciprocityTheory.PGsh.xiNu p ℂ_[p] Valued.v 𝓞_ℂ_[p] hker, ?_, _root_.ReciprocityTheory.PGsh.flatW' p 𝓞_ℂ_[p]⟩
  refine _root_.ReciprocityTheory.PGsh.regular p 𝓞_ℂ_[p] fun x hx => ?_
  have h : ((p : ℂ_[p]) * (x : ℂ_[p])) = 0 := by
    simpa using congrArg (fun y : 𝓞_ℂ_[p] => (y : ℂ_[p])) hx
  rcases mul_eq_zero.mp h with h | h
  · exact absurd h (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)
  · exact Subtype.ext h

section
variable (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (span {(p : O)}) O]

omit [IsAdicComplete (span {(p : O)}) O] in

/- English proof (translation)
Use `⟨((ZMod.castHom (ringChar.dvd ?_) _)).toAlgebra⟩` and prove the remaining obligations. Use `push_cast`. Rewrite using `[← map_natCast (Ideal.Quotient.mk _), ← map_pow, Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `subset_span (by simp)`.
-/
theorem nonempty_algebra (pflat : PreTilt O p) :
    Nonempty (Algebra (ZMod (p ^ 2)) (WittVector p (PreTilt O p) ⧸
      span {(p : WittVector p (PreTilt O p)) ^ 2, teichmuller p pflat})) := by
  refine ⟨((ZMod.castHom (ringChar.dvd ?_) _)).toAlgebra⟩
  push_cast
  rw [← map_natCast (Ideal.Quotient.mk _), ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  exact subset_span (by simp)
end

/- English proof (translation)
Establish `h0 : ((p : ℕ) : ZMod p) = 0` using `ZMod.natCast_self p`. Establish `hb : span {((p : ℕ) : ZMod p)} = ⊥` using `by rw [h0, span_singleton_eq_bot]`. Establish `i1 : Fact ¬IsUnit ((p : ℕ) : ZMod p)` using `⟨by rw [h0]; exact not_isUnit_zero⟩`. Establish `i2 : IsAdicComplete (span {((p : ℕ) : ZMod p)}) (ZMod p)` using `by rw [hb]; infer_instance`. Use `⟨i1, i2, fun h => ?_⟩` and prove the remaining obligations.

Establish `hz : (0 : PreTilt (ZMod p) p).untilt = ((p : ℕ) : ZMod p)`. Use `PreTilt.mk_untilt_eq_coeff_zero (0 : PreTilt (ZMod p) p)` as an intermediate fact. Rewrite `this` using `[map_zero (PreTilt.coeff 0), Ideal.Quotient.eq_zero_iff_mem, mem_span_singleton]`. Conclude with `(zero_dvd_iff.1 (h0 ▸ this)).trans h0.symm`. Take `⟨-, h2, h3⟩` from `h 0 hz`.

Apply `h3` to reduce the goal to its premises. Establish `h1` using `h2 1 (by rw [teichmuller_zero, zero_mul]; exact zero_mem _)`. Rewrite using `[eq_top_iff_one]`. Conclude with `span_mono (by simp) h1`.
-/
theorem not_regular_zmod (p : ℕ) [Fact p.Prime] :
    ∃ (_ : Fact ¬IsUnit ((p : ℕ) : ZMod p)) (_ : IsAdicComplete (span {((p : ℕ) : ZMod p)}) (ZMod p)),
      ¬ RegularStatement p (ZMod p) := by
  have h0 : ((p : ℕ) : ZMod p) = 0 := ZMod.natCast_self p
  have hb : span {((p : ℕ) : ZMod p)} = ⊥ := by rw [h0, span_singleton_eq_bot]
  have i1 : Fact ¬IsUnit ((p : ℕ) : ZMod p) := ⟨by rw [h0]; exact not_isUnit_zero⟩
  have i2 : IsAdicComplete (span {((p : ℕ) : ZMod p)}) (ZMod p) := by rw [hb]; infer_instance
  refine ⟨i1, i2, fun h => ?_⟩
  have hz : (0 : PreTilt (ZMod p) p).untilt = ((p : ℕ) : ZMod p) := by
    have := PreTilt.mk_untilt_eq_coeff_zero (0 : PreTilt (ZMod p) p)
    rw [map_zero (PreTilt.coeff 0), Ideal.Quotient.eq_zero_iff_mem, mem_span_singleton] at this
    exact (zero_dvd_iff.1 (h0 ▸ this)).trans h0.symm
  obtain ⟨-, h2, h3⟩ := h 0 hz
  apply h3
  have h1 := h2 1 (by rw [teichmuller_zero, zero_mul]; exact zero_mem _)
  rw [eq_top_iff_one]
  exact span_mono (by simp) h1

end GlobalTheory.AinfChecks
