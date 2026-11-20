import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemCycAlgOfPow
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIndexStabilizer

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.RecOne GlobalTheory.AlmostEt
open scoped Matrix NNReal

namespace GlobalTheory.RecOne.CycDvd

/- English proof (translation)
Use `haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ`. Use `haveI : CharZero Ω := algebraRat.charZero Ω`. Use `haveI : NeZero (l : Ω) := ⟨by exact_mod_cast (Fact.out : l.Prime).ne_zero⟩`. Establish `h1` using `cyclotomicCharacter.spec (L := Ω) l (MulSemiringAction.toRingAut (G ℚ Ω) Ω s) t ht`. Establish `h2 : (cyclotomicCharacter Ω l (MulSemiringAction.toRingAut (G ℚ Ω) Ω s)).val.toZModPow n = ((cycMod ℚ Ω l n s : (ZMod (l ^ n))ˣ) : ZMod (l ^ n))`.

Simplify using `[cycMod, cycZ]`. Rewrite `h1` using `[h2]`. Conclude with `h1`.
-/
theorem apply_eq_pow (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (n : ℕ) (s : G ℚ Ω)
    {t : Ω} (ht : t ^ (l ^ n) = 1) : s t = t ^ ((cycMod ℚ Ω l n s : (ZMod (l ^ n))ˣ) : ZMod (l ^ n)).val := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := algebraRat.charZero Ω
  haveI : NeZero (l : Ω) := ⟨by exact_mod_cast (Fact.out : l.Prime).ne_zero⟩
  have h1 := cyclotomicCharacter.spec (L := Ω) l (MulSemiringAction.toRingAut (G ℚ Ω) Ω s) t ht
  have h2 : (cyclotomicCharacter Ω l (MulSemiringAction.toRingAut (G ℚ Ω) Ω s)).val.toZModPow n =
      ((cycMod ℚ Ω l n s : (ZMod (l ^ n))ˣ) : ZMod (l ^ n)) := by
    simp [cycMod, cycZ]
  rw [h2] at h1
  exact h1

/- English proof (translation)
Establish `hpos : 0 < l ^ n` using `pow_pos (Fact.out : l.Prime).pos n`. Use `haveI : NeZero (l ^ n) := ⟨hpos.ne'⟩`. Take `⟨i, hi, hcop, rfl⟩` from `(hz.isPrimitiveRoot_iff).1 hμ`. Take `⟨⟨s, hs⟩, hsu⟩` from `GlobalTheory.InertiaPowers.cycMod_Ine_surjective l Ω A hA n (ZMod.unitOfCoprime i hcop)`. Use `⟨s, hs, ?_⟩` and prove the remaining obligations.

Establish `hsu' : cycMod ℚ Ω l n s = ZMod.unitOfCoprime i hcop` using `hsu`. Rewrite using `[apply_eq_pow l Ω n s hz.pow_eq_one, hsu', ZMod.coe_unitOfCoprime, ZMod.val_natCast, Nat.mod_eq_of_lt hi]`.
-/
theorem exists_Ine_apply_eq (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]
    (A : ValuationSubring Ω) (hA : A.valuation (l : Ω) < 1) (n : ℕ) {z μ : Ω} (hz : IsPrimitiveRoot z (l ^ n))
    (hμ : IsPrimitiveRoot μ (l ^ n)) : ∃ s ∈ Ine (F := ℚ) A, s z = μ := by
  have hpos : 0 < l ^ n := pow_pos (Fact.out : l.Prime).pos n
  haveI : NeZero (l ^ n) := ⟨hpos.ne'⟩
  obtain ⟨i, hi, hcop, rfl⟩ := (hz.isPrimitiveRoot_iff).1 hμ
  obtain ⟨⟨s, hs⟩, hsu⟩ := GlobalTheory.InertiaPowers.cycMod_Ine_surjective l Ω A hA n (ZMod.unitOfCoprime i hcop)
  refine ⟨s, hs, ?_⟩
  have hsu' : cycMod ℚ Ω l n s = ZMod.unitOfCoprime i hcop := hsu
  rw [apply_eq_pow l Ω n s hz.pow_eq_one, hsu', ZMod.coe_unitOfCoprime, ZMod.val_natCast, Nat.mod_eq_of_lt hi]

/- English proof (translation)
Introduce `l _ Ω _ _ _ A hO n z hz R hR`. Establish `hA : A.valuation (l : Ω) < 1`. Take `⟨v, hv, hl⟩` from `hO`. Establish `h1` using `(hv ((l : ℕ) : 𝓞 ℚ)).2 hl`. Simplify using `using h1`.

Establish `hpos : 0 < l ^ n` using `pow_pos (Fact.out : l.Prime).pos n`. Set `f : fixA A →+* Ω` to `A.subtype.comp (fixA A).subtype`. Establish `hf : Function.Injective f` using `Subtype.val_injective.comp Subtype.val_injective`. Establish `h0 : Polynomial.eval₂ f (z : Ω) R = 0`. Use `Polynomial.hom_eval₂ R (algebraMap (fixA A) A) A.subtype z` as an intermediate fact.

Rewrite `this` using `[← Polynomial.aeval_def, hR, map_zero]`. Conclude with `this.symm`. Establish `hroot : ∀ μ ∈ primitiveRoots (l ^ n) Ω, (R.map f).eval μ = 0`. Introduce `μ hμ`. Take `⟨s, hs, rfl⟩` from `exists_Ine_apply_eq l Ω A hA n hz ((mem_primitiveRoots hpos).1 hμ)`.

Establish `e` using `Polynomial.hom_eval₂ R f (s : Ω →+* Ω) (z : Ω)`. Establish `e2 : (s : Ω →+* Ω).comp f = f` using `RingHom.ext fun a => a.2 s hs`. Rewrite `e` using `[h0, map_zero, e2]`. Rewrite using `[Polynomial.eval_map]`. Conclude with `e.symm`.

Rewrite using `[← Polynomial.map_dvd_map f hf (Polynomial.cyclotomic.monic _ _), Polynomial.map_cyclotomic, Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots hz]`. Use `Finset.prod_dvd_of_coprime ?_ ?_` and prove the remaining obligations. Introduce `a _ b _ hab`. Conclude with `Polynomial.isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.2 hab).isUnit`. Introduce `μ hμ`.

Conclude with `Polynomial.dvd_iff_isRoot.2 (hroot μ hμ)`.
-/
theorem cyclotomic_dvd : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω), OverL l A → ∀ (n : ℕ) (z : A), IsPrimitiveRoot (z : Ω) (l ^ n) → ∀ R : Polynomial (fixA A), Polynomial.aeval z R = 0 → Polynomial.cyclotomic (l ^ n) (fixA A) ∣ R := by
  intro l _ Ω _ _ _ A hO n z hz R hR
  classical
  have hA : A.valuation (l : Ω) < 1 := by
    obtain ⟨v, hv, hl⟩ := hO
    have h1 := (hv ((l : ℕ) : 𝓞 ℚ)).2 hl
    simpa using h1
  have hpos : 0 < l ^ n := pow_pos (Fact.out : l.Prime).pos n
  let f : fixA A →+* Ω := A.subtype.comp (fixA A).subtype
  have hf : Function.Injective f := Subtype.val_injective.comp Subtype.val_injective
  have h0 : Polynomial.eval₂ f (z : Ω) R = 0 := by
    have := Polynomial.hom_eval₂ R (algebraMap (fixA A) A) A.subtype z
    rw [← Polynomial.aeval_def, hR, map_zero] at this
    exact this.symm
  have hroot : ∀ μ ∈ primitiveRoots (l ^ n) Ω, (R.map f).eval μ = 0 := by
    intro μ hμ
    obtain ⟨s, hs, rfl⟩ := exists_Ine_apply_eq l Ω A hA n hz ((mem_primitiveRoots hpos).1 hμ)
    have e := Polynomial.hom_eval₂ R f (s : Ω →+* Ω) (z : Ω)
    have e2 : (s : Ω →+* Ω).comp f = f := RingHom.ext fun a => a.2 s hs
    rw [h0, map_zero, e2] at e
    rw [Polynomial.eval_map]
    exact e.symm
  rw [← Polynomial.map_dvd_map f hf (Polynomial.cyclotomic.monic _ _), Polynomial.map_cyclotomic,
    Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots hz]
  refine Finset.prod_dvd_of_coprime ?_ ?_
  · intro a _ b _ hab
    exact Polynomial.isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.2 hab).isUnit
  · intro μ hμ
    exact Polynomial.dvd_iff_isRoot.2 (hroot μ hμ)

end GlobalTheory.RecOne.CycDvd
