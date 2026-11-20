import Formalism.WachLatticeTwists.RealDisplaySplitting.GaloisTheoremWithGenerator
import ReciprocityTheory.GaloisValuations.Global

noncomputable section

open Formalism.RepresentationBoundsCohomology.ringDataObjects (AbsIrr BlockDiagonalIrreducibleAt)
open Formalism.RepresentationBoundsCohomology.FIN (IsCycG)

namespace Formalism.AdicCompletionExports

section Mat

variable {k k' : Type*} [Field k] [Field k'] (σ : k ≃+* k')

end Mat

/- English proof (translation)
Introduce `g n ζ hζ`. Establish `: IsAlgClosed Ω` using `IsAlgClosure.isAlgClosed Ek`. Establish `: CharZero Ω` using `charZero_of_injective_algebraMap (algebraMap Ek Ω).injective`. Establish `: NeZero ((l : ℕ) : Ω)` using `⟨Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero⟩`. Establish `: NeZero (l ^ n)` using `⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩`.

Establish `hspec` using `cyclotomicCharacter.spec (L := Ω) l (MulSemiringAction.toRingAut (Ω ≃ₐ[Ek] Ω) Ω g) ζ hζ`. Use `set x : ℤ_[l] := ((ReciprocityTheory.Gal.cycZ (F := Ek) (Ω := Ω) l g : ℤ_[l]ˣ) : ℤ_[l]) with hx`. Use `⟨(PadicInt.toZModPow n x).val, hspec, ?_⟩` and prove the remaining obligations. Establish `h2 : x - (((PadicInt.toZModPow n x).val : ℕ) : ℤ_[l]) ∈ Ideal.span {(l : ℤ_[l]) ^ n}`. Rewrite using `[← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_natCast, ZMod.natCast_zmod_val, sub_self]`.

Rewrite `h2`, the goal using `[Ideal.mem_span_singleton]`. Take `⟨y, hy⟩` from `h2`. Use `⟨f y, ?_⟩` and prove the remaining obligations. Establish `h3` using `congrArg f hy`. Rewrite `h3` using `[map_sub, map_natCast, map_mul, map_pow, map_natCast]`.

Conclude with `h3`.
-/
theorem isCycG_cycZ (l : ℕ) [Fact l.Prime] (Ek Ω O : Type) [Field Ek] [NumberField Ek] [Field Ω] [Algebra Ek Ω]
    [IsAlgClosure Ek Ω] [CommRing O] (f : ℤ_[l] →+* O) :
    IsCycG l ((Units.map f.toMonoidHom).comp (ReciprocityTheory.Gal.cycZ (F := Ek) (Ω := Ω) l)) := by
  intro g n ζ hζ
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed Ek
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap Ek Ω).injective
  have : NeZero ((l : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero⟩
  have : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have hspec := cyclotomicCharacter.spec (L := Ω) l (MulSemiringAction.toRingAut (Ω ≃ₐ[Ek] Ω) Ω g) ζ hζ
  set x : ℤ_[l] := ((ReciprocityTheory.Gal.cycZ (F := Ek) (Ω := Ω) l g : ℤ_[l]ˣ) : ℤ_[l]) with hx
  refine ⟨(PadicInt.toZModPow n x).val, hspec, ?_⟩
  have h2 : x - (((PadicInt.toZModPow n x).val : ℕ) : ℤ_[l]) ∈ Ideal.span {(l : ℤ_[l]) ^ n} := by
    rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_natCast, ZMod.natCast_zmod_val, sub_self]
  rw [Ideal.mem_span_singleton] at h2 ⊢
  obtain ⟨y, hy⟩ := h2
  refine ⟨f y, ?_⟩
  have h3 := congrArg f hy
  rw [map_sub, map_natCast, map_mul, map_pow, map_natCast] at h3
  exact h3

end Formalism.AdicCompletionExports
