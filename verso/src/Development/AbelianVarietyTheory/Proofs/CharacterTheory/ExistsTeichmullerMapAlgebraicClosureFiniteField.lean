import Mathlib
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

namespace GlobalTheory.CuspGL.TeichEmb

open Polynomial IntermediateField in
/- English proof (translation)
Establish `hfin : FiniteDimensional F F⟮x⟯` using `IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x)`. Establish `: Finite F⟮x⟯` using `Module.finite_of_finite F`. Establish `hne : (⟨x, IntermediateField.mem_adjoin_simple_self F x⟩ : F⟮x⟯) ≠ 0`. Introduce `h`. Conclude with `hx (congrArg Subtype.val h)`.

Take `⟨n, hn, hpow⟩` from `isOfFinOrder_iff_pow_eq_one.mp (isOfFinOrder_of_finite (Units.mk0 _ hne))`. Use `⟨n, hn, ?_⟩` and prove the remaining obligations. Use `congrArg (fun u : (F⟮x⟯)ˣ => ((u : F⟮x⟯) : AlgebraicClosure F)) hpow` as an intermediate fact. Simplify using `using this`.
-/
private theorem exists_pow_eq_one_algebraicClosure_of_finite (F : Type) [Field F] [Finite F]
    (x : AlgebraicClosure F) (hx : x ≠ 0) : ∃ n : ℕ, 0 < n ∧ x ^ n = 1 := by
  have hfin : FiniteDimensional F F⟮x⟯ :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x)
  have : Finite F⟮x⟯ := Module.finite_of_finite F
  have hne : (⟨x, IntermediateField.mem_adjoin_simple_self F x⟩ : F⟮x⟯) ≠ 0 := by
    intro h; exact hx (congrArg Subtype.val h)
  obtain ⟨n, hn, hpow⟩ :=
    isOfFinOrder_iff_pow_eq_one.mp (isOfFinOrder_of_finite (Units.mk0 _ hne))
  refine ⟨n, hn, ?_⟩
  have := congrArg (fun u : (F⟮x⟯)ˣ => ((u : F⟮x⟯) : AlgebraicClosure F)) hpow
  simpa using this

open Polynomial IntermediateField in

/- English proof (translation)
Introduce `F _ _`. Use `set p := ringChar F`. Establish `: Fact p.Prime` using `⟨(CharP.char_is_prime_or_zero F p).resolve_right (CharP.char_ne_zero_of_finite F p)⟩`. Establish `: CharP (AlgebraicClosure F) p` using `charP_of_injective_algebraMap (algebraMap F (AlgebraicClosure F)).injective p`. Establish `: PerfectRing (AlgebraicClosure F) p` using `inferInstance`.

Set `W` to `WittVector p (AlgebraicClosure F)`. Establish `: IsDomain W` using `inferInstance`. Use `letI : Algebra (ZMod p) (AlgebraicClosure F) := ZMod.algebra _ p`. Establish `hW : CharZero W`. Set `f : ℤ_[p] →+* W` to `(WittVector.map (algebraMap (ZMod p) (AlgebraicClosure F))).comp (WittVector.equiv p).symm.toRingHom`.

Establish `hf : Function.Injective f` using `(WittVector.map_injective _ (algebraMap (ZMod p) (AlgebraicClosure F)).injective).comp (WittVector.equiv p).symm.injective`. Conclude with `(RingHom.charZero_iff hf).mp inferInstance`. Set `Ω` to `AlgebraicClosure (FractionRing W)`. Establish `: CharZero (FractionRing W)` using `charZero_of_injective_algebraMap (IsFractionRing.injective W (FractionRing W))`. Establish `: CharZero Ω` using `inferInstance`.

Set `g : W →+* Ω` to `(algebraMap (FractionRing W) Ω).comp (algebraMap W (FractionRing W))`. Establish `hg : Function.Injective g` using `(algebraMap (FractionRing W) Ω).injective.comp (IsFractionRing.injective W (FractionRing W))`. Set `ι : AlgebraicClosure F →* Ω` to `(g : W →* Ω).comp (WittVector.teichmuller p)`. Establish `hι : Function.Injective ι`. Introduce `x y h`.

Establish `h1 : WittVector.teichmuller p x = WittVector.teichmuller p y` using `hg h`. Simplify using `using congrArg (fun w : W => w.coeff 0) h1`. Establish `hmem : ∀ x, ι x ∈ algebraicClosure ℚ Ω`. Introduce `x`. Rewrite using `[mem_algebraicClosure_iff]`.

Distinguish the cases in `hx : x = 0`. Substitute `hx` using the available equality. Establish `: ι 0 = 0` using `by show g (WittVector.teichmuller p 0) = 0`. Rewrite using `[WittVector.teichmuller_zero, map_zero]`. Rewrite using `[this]`.

Conclude with `isAlgebraic_zero`. Take `⟨n, hn, hpow⟩` from `exists_pow_eq_one_algebraicClosure_of_finite F x hx`. Use `(IsIntegral.of_pow hn ?_).isAlgebraic` and prove the remaining obligations. Rewrite using `[← map_pow, hpow, map_one]`. Conclude with `isIntegral_one`.

Establish `: Algebra.IsAlgebraic ℚ (algebraicClosure ℚ Ω)` using `algebraicClosure.isAlgebraic ℚ Ω`. Set `φ : algebraicClosure ℚ Ω →ₐ[ℚ] ℂ` to `IsAlgClosed.lift`. Use `⟨{ toFun := fun x => φ ⟨ι x, hmem x⟩, map_one' := ?_, map_mul' := ?_ }, ?_⟩` and prove the remaining obligations. Conclude with `(congrArg φ (Subtype.ext (map_one ι) : (⟨ι 1, hmem 1⟩ : algebraicClosure ℚ Ω) = 1)).trans (map_one φ)`. Introduce `x y`.

Rewrite using `[← map_mul]`. Conclude with `congrArg φ (Subtype.ext (map_mul ι x y))`. Introduce `x y _ _ h`. Conclude with `hι (congrArg Subtype.val (φ.injective h))`.
-/
theorem _root_.GlobalTheory.CuspGL.TeichEmb.exists_teichmuller :
    ∀ (F : Type) [Field F] [Finite F], ∃ θ : AlgebraicClosure F →* ℂ,
      ∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y := by
  intro F _ _
  set p := ringChar F
  have : Fact p.Prime :=
    ⟨(CharP.char_is_prime_or_zero F p).resolve_right (CharP.char_ne_zero_of_finite F p)⟩
  have : CharP (AlgebraicClosure F) p :=
    charP_of_injective_algebraMap (algebraMap F (AlgebraicClosure F)).injective p
  have : PerfectRing (AlgebraicClosure F) p := inferInstance
  let W := WittVector p (AlgebraicClosure F)
  have : IsDomain W := inferInstance
  letI : Algebra (ZMod p) (AlgebraicClosure F) := ZMod.algebra _ p
  have hW : CharZero W := by
    let f : ℤ_[p] →+* W := (WittVector.map (algebraMap (ZMod p) (AlgebraicClosure F))).comp
      (WittVector.equiv p).symm.toRingHom
    have hf : Function.Injective f :=
      (WittVector.map_injective _ (algebraMap (ZMod p) (AlgebraicClosure F)).injective).comp
        (WittVector.equiv p).symm.injective
    exact (RingHom.charZero_iff hf).mp inferInstance
  let Ω := AlgebraicClosure (FractionRing W)
  have : CharZero (FractionRing W) :=
    charZero_of_injective_algebraMap (IsFractionRing.injective W (FractionRing W))
  have : CharZero Ω := inferInstance
  let g : W →+* Ω := (algebraMap (FractionRing W) Ω).comp (algebraMap W (FractionRing W))
  have hg : Function.Injective g :=
    (algebraMap (FractionRing W) Ω).injective.comp (IsFractionRing.injective W (FractionRing W))
  let ι : AlgebraicClosure F →* Ω := (g : W →* Ω).comp (WittVector.teichmuller p)
  have hι : Function.Injective ι := by
    intro x y h
    have h1 : WittVector.teichmuller p x = WittVector.teichmuller p y := hg h
    simpa using congrArg (fun w : W => w.coeff 0) h1
  have hmem : ∀ x, ι x ∈ algebraicClosure ℚ Ω := by
    intro x
    rw [mem_algebraicClosure_iff]
    by_cases hx : x = 0
    · subst hx
      have : ι 0 = 0 := by
        show g (WittVector.teichmuller p 0) = 0
        rw [WittVector.teichmuller_zero, map_zero]
      rw [this]; exact isAlgebraic_zero
    · obtain ⟨n, hn, hpow⟩ := exists_pow_eq_one_algebraicClosure_of_finite F x hx
      refine (IsIntegral.of_pow hn ?_).isAlgebraic
      rw [← map_pow, hpow, map_one]; exact isIntegral_one
  have : Algebra.IsAlgebraic ℚ (algebraicClosure ℚ Ω) := algebraicClosure.isAlgebraic ℚ Ω
  let φ : algebraicClosure ℚ Ω →ₐ[ℚ] ℂ := IsAlgClosed.lift
  refine ⟨{ toFun := fun x => φ ⟨ι x, hmem x⟩, map_one' := ?_, map_mul' := ?_ }, ?_⟩
  · exact (congrArg φ (Subtype.ext (map_one ι) : (⟨ι 1, hmem 1⟩ : algebraicClosure ℚ Ω) = 1)).trans
      (map_one φ)
  · intro x y
    rw [← map_mul]; exact congrArg φ (Subtype.ext (map_mul ι x y))
  · intro x y _ _ h
    exact hι (congrArg Subtype.val (φ.injective h))

end GlobalTheory.CuspGL.TeichEmb
