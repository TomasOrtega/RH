import Mathlib
import Formalism.LocalToGlobal.UnitaryNorms.CharExGen

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR

namespace PI.IdeleUnitsOpenW

variable (L : Type) [Field L] [NumberField L]

/- English proof (translation)
Establish `h : (v.adicCompletionIntegers L : Set (v.adicCompletion L)) = ((Valued.v : Valuation (v.adicCompletion L) _).integer : Set (v.adicCompletion L))`. Use extensionality with `x`. Simplify using `only [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers, Valuation.mem_integer_iff]`. Rewrite using `[h]`. Conclude with `Valued.isOpen_integer _`.
-/
theorem isOpen_adicCompletionIntegers (v : HeightOneSpectrum (𝓞 L)) :
    IsOpen (v.adicCompletionIntegers L : Set (v.adicCompletion L)) := by
  have h : (v.adicCompletionIntegers L : Set (v.adicCompletion L)) =
      ((Valued.v : Valuation (v.adicCompletion L) _).integer : Set (v.adicCompletion L)) := by
    ext x
    simp only [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers,
      Valuation.mem_integer_iff]
  rw [h]
  exact Valued.isOpen_integer _

/- English proof (translation)
The claim follows from `RestrictedProduct.isOpen_forall_mem (isOpen_adicCompletionIntegers L)`.
-/
theorem isOpen_integralFinite :
    IsOpen {f : FiniteAdeleRing (𝓞 L) L | ∀ v, f v ∈ v.adicCompletionIntegers L} :=
  RestrictedProduct.isOpen_forall_mem (isOpen_adicCompletionIntegers L)

def integralAdeles : Set (AdeleRing (𝓞 L) L) :=
  {x | ∀ v : HeightOneSpectrum (𝓞 L), Valued.v (x.2 v) ≤ 1}

/- English proof (translation)
Establish `h : integralAdeles L = Prod.snd ⁻¹' {f : FiniteAdeleRing (𝓞 L) L | ∀ v, f v ∈ v.adicCompletionIntegers L}`. Use extensionality with `x`. Conclude with `Iff.rfl`. Rewrite using `[h]`. Conclude with `(isOpen_integralFinite L).preimage continuous_snd`.
-/
theorem isOpen_integralAdeles : IsOpen (integralAdeles L) := by
  have h : integralAdeles L = Prod.snd ⁻¹'
      {f : FiniteAdeleRing (𝓞 L) L | ∀ v, f v ∈ v.adicCompletionIntegers L} := by
    ext x
    exact Iff.rfl
  rw [h]
  exact (isOpen_integralFinite L).preimage continuous_snd

/- English proof (translation)
Use extensionality with `u`. Prove the components needed by the constructor for the conclusion. Introduce `hu`. Establish `hu' : ∀ v, Valued.v ((u : AdeleRing (𝓞 L) L).2 v) = 1` using `hu`. Use `⟨fun v => (hu' v).le, fun v => ?_⟩` and prove the remaining obligations.

Establish `e` using `congrArg Valued.v (comp_mul_inv L u v)`. Rewrite `e` using `[map_mul, hu' v, one_mul, map_one]`. Conclude with `e.le`. Introduce and unpack `⟨h1, h2⟩ show ∀ v, Valued.v ((u : AdeleRing (𝓞 L) L).2 v) = 1`. Introduce `v`.

Establish `e` using `congrArg Valued.v (comp_mul_inv L u v)`. Rewrite `e` using `[map_mul, map_one]`. Establish `hle1 : Valued.v ((u : AdeleRing (𝓞 L) L).2 v) ≤ 1` using `h1 v`. Establish `hle2 : Valued.v (((u⁻¹ : Ideles L) : AdeleRing (𝓞 L) L).2 v) ≤ 1` using `h2 v`. Use `le_antisymm hle1 ?_` and prove the remaining obligations.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem unitIdeles_eq :
    (Formalism.L2.Host.CharEx.unitIdeles L : Set (Ideles L)) =
      (fun u : Ideles L => (u : AdeleRing (𝓞 L) L)) ⁻¹' integralAdeles L ∩
        (fun u : Ideles L => ((u⁻¹ : Ideles L) : AdeleRing (𝓞 L) L)) ⁻¹' integralAdeles L := by
  ext u
  constructor
  · intro hu
    have hu' : ∀ v, Valued.v ((u : AdeleRing (𝓞 L) L).2 v) = 1 := hu
    refine ⟨fun v => (hu' v).le, fun v => ?_⟩
    have e := congrArg Valued.v (comp_mul_inv L u v)
    rw [map_mul, hu' v, one_mul, map_one] at e
    exact e.le
  · rintro ⟨h1, h2⟩
    show ∀ v, Valued.v ((u : AdeleRing (𝓞 L) L).2 v) = 1
    intro v
    have e := congrArg Valued.v (comp_mul_inv L u v)
    rw [map_mul, map_one] at e
    have hle1 : Valued.v ((u : AdeleRing (𝓞 L) L).2 v) ≤ 1 := h1 v
    have hle2 : Valued.v (((u⁻¹ : Ideles L) : AdeleRing (𝓞 L) L).2 v) ≤ 1 := h2 v
    refine le_antisymm hle1 ?_
    calc (1 : WithZero (Multiplicative ℤ)) = _ := e.symm
      _ ≤ Valued.v ((u : AdeleRing (𝓞 L) L).2 v) * 1 := by gcongr
      _ = _ := mul_one _

/- English proof (translation)
Use `show IsOpen (Formalism.L2.Host.CharEx.unitIdeles L : Set (Ideles L))`. Rewrite using `[unitIdeles_eq]`. Conclude with `((isOpen_integralAdeles L).preimage Units.continuous_val).inter ((isOpen_integralAdeles L).preimage (Units.continuous_val.comp continuous_inv))`.
-/
theorem openUnits : Formalism.L2.Host.CharEx.OpenUnits L := by
  show IsOpen (Formalism.L2.Host.CharEx.unitIdeles L : Set (Ideles L))
  rw [unitIdeles_eq]
  exact ((isOpen_integralAdeles L).preimage Units.continuous_val).inter
    ((isOpen_integralAdeles L).preimage (Units.continuous_val.comp continuous_inv))

end PI.IdeleUnitsOpenW
