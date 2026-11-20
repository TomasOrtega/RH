import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

namespace GlobalTheory.SiegelTor.CycLift

/- English proof (translation)
Take `⟨l, hl⟩` from `CharP.exists (WittVector p K)`. Break down `CharP.char_is_prime_or_zero (WittVector p K) l with h | h` into its components or cases. It suffices to derive a contradiction. Establish `h1 : ((l : ℕ) : WittVector p K) = 0` using `CharP.cast_eq_zero _ l`. Establish `h2 : ((l : ℕ) : K) = 0`.

Use `congrArg (WittVector.constantCoeff : WittVector p K →+* K) h1` as an intermediate fact. Rewrite `this` using `[map_natCast, map_zero]`. Then use the resulting hypothesis. Establish `h4 : p = l` using `(Nat.prime_dvd_prime_iff_eq hp.out h).1 ((CharP.cast_eq_zero_iff K p l).1 h2)`. Substitute `h4` using the available equality. Conclude with `WittVector.p_nonzero p K h1`.

Substitute `h` using the available equality. Conclude with `CharP.charP_to_charZero _`.
-/
theorem charZero_witt (p : ℕ) [hp : Fact p.Prime] (K : Type) [Field K] [CharP K p] :
    CharZero (WittVector p K) := by
  obtain ⟨l, hl⟩ := CharP.exists (WittVector p K)
  rcases CharP.char_is_prime_or_zero (WittVector p K) l with h | h
  · exfalso
    have h1 : ((l : ℕ) : WittVector p K) = 0 := CharP.cast_eq_zero _ l
    have h2 : ((l : ℕ) : K) = 0 := by
      have := congrArg (WittVector.constantCoeff : WittVector p K →+* K) h1
      rwa [map_natCast, map_zero] at this
    have h4 : p = l := (Nat.prime_dvd_prime_iff_eq hp.out h).1 ((CharP.cast_eq_zero_iff K p l).1 h2)
    subst h4
    exact WittVector.p_nonzero p K h1
  · subst h
    exact CharP.charP_to_charZero _

/- English proof (translation)
The claim follows from `IsPrimitiveRoot.of_map_of_injective (f := (cycAway n).subtype) (Complex.isPrimitiveRoot_exp n hn) Subtype.val_injective`.
-/
theorem isPrimitiveRoot_zetaAway {n : ℕ} (hn : n ≠ 0) : IsPrimitiveRoot (zetaAway n) n :=
  IsPrimitiveRoot.of_map_of_injective (f := (cycAway n).subtype) (Complex.isPrimitiveRoot_exp n hn)
    Subtype.val_injective

/- English proof (translation)
Establish `hinv : ∀ hx : (n : ℂ)⁻¹ ∈ cycAway n, f ⟨(n : ℂ)⁻¹, hx⟩ = g ⟨(n : ℂ)⁻¹, hx⟩`. Introduce `hx`. Establish `hu : (⟨(n : ℂ)⁻¹, hx⟩ : cycAway n) * (n : cycAway n) = 1` using `Subtype.ext (by simp [inv_mul_cancel₀ (Nat.cast_ne_zero.2 hn : (n : ℂ) ≠ 0)])`. Establish `hf` using `congrArg f hu`. Establish `hg` using `congrArg g hu`.

Rewrite `hf`, `hg` using `[map_mul, map_natCast, map_one]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[_root_.mul_comm (n : R), hg, _root_.mul_one]`. Use `_ = g ⟨(n : ℂ)⁻¹, hx⟩ := by rw [← _root_.mul_assoc, hf, _root_.one_mul]`. Use extensionality with `⟨x, hx⟩`.

Proceed by induction on `hx using Subring.closure_induction with`. Consider the case `mem x hx`. Break down `hx with rfl | rfl` into its components or cases. Conclude with `h`. Conclude with `hinv _`.

Consider the case `zero => exact (map_zero f).trans (map_zero g).symm`. Consider the case `one => exact (map_one f).trans (map_one g).symm`. Consider the case `add x y hx hy ihx ihy`. Express the relevant statement in the definitionally equal form `f (⟨x, hx⟩ + ⟨y, hy⟩) = g (⟨x, hx⟩ + ⟨y, hy⟩)`. Rewrite using `[map_add, map_add, ihx, ihy]`.

Consider the case `neg x hx ih`. Express the relevant statement in the definitionally equal form `f (-⟨x, hx⟩) = g (-⟨x, hx⟩)`. Rewrite using `[map_neg, map_neg, ih]`. Consider the case `mul x y hx hy ihx ihy`. Express the relevant statement in the definitionally equal form `f (⟨x, hx⟩ * ⟨y, hy⟩) = g (⟨x, hx⟩ * ⟨y, hy⟩)`.

Rewrite using `[map_mul, map_mul, ihx, ihy]`.
-/
theorem hom_ext {n : ℕ} (hn : n ≠ 0) {R : Type} [CommRing R] (f g : cycAway n →+* R)
    (h : f (zetaAway n) = g (zetaAway n)) : f = g := by
  have hinv : ∀ hx : (n : ℂ)⁻¹ ∈ cycAway n, f ⟨(n : ℂ)⁻¹, hx⟩ = g ⟨(n : ℂ)⁻¹, hx⟩ := by
    intro hx
    have hu : (⟨(n : ℂ)⁻¹, hx⟩ : cycAway n) * (n : cycAway n) = 1 :=
      Subtype.ext (by simp [inv_mul_cancel₀ (Nat.cast_ne_zero.2 hn : (n : ℂ) ≠ 0)])
    have hf := congrArg f hu
    have hg := congrArg g hu
    rw [map_mul, map_natCast, map_one] at hf hg
    calc f ⟨(n : ℂ)⁻¹, hx⟩ = f ⟨(n : ℂ)⁻¹, hx⟩ * ((n : R) * g ⟨(n : ℂ)⁻¹, hx⟩) := by
          rw [_root_.mul_comm (n : R), hg, _root_.mul_one]
      _ = g ⟨(n : ℂ)⁻¹, hx⟩ := by rw [← _root_.mul_assoc, hf, _root_.one_mul]
  ext ⟨x, hx⟩
  induction hx using Subring.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact h
    · exact hinv _
  | zero => exact (map_zero f).trans (map_zero g).symm
  | one => exact (map_one f).trans (map_one g).symm
  | add x y hx hy ihx ihy =>
    change f (⟨x, hx⟩ + ⟨y, hy⟩) = g (⟨x, hx⟩ + ⟨y, hy⟩)
    rw [map_add, map_add, ihx, ihy]
  | neg x hx ih =>
    change f (-⟨x, hx⟩) = g (-⟨x, hx⟩)
    rw [map_neg, map_neg, ih]
  | mul x y hx hy ihx ihy =>
    change f (⟨x, hx⟩ * ⟨y, hy⟩) = g (⟨x, hx⟩ * ⟨y, hy⟩)
    rw [map_mul, map_mul, ihx, ihy]

end GlobalTheory.SiegelTor.CycLift

namespace GlobalTheory.SiegelTor.CycLift

/- English proof (translation)
Establish `hpos : 0 < n` using `Nat.pos_of_ne_zero hn`. Use `set z : ℂ := ((zetaAway n : cycAway n) : ℂ) with hzdef`. Establish `hz : IsPrimitiveRoot z n` using `(isPrimitiveRoot_zetaAway hn).map_of_injective (f := (cycAway n).subtype) Subtype.val_injective`. Establish `hint : IsIntegral ℚ z` using `(hz.isIntegral hpos).tower_top`. Set `pb` to `IntermediateField.adjoin.powerBasis hint`.

Establish `hgen : pb.gen = IntermediateField.AdjoinSimple.gen ℚ z` using `rfl`. Establish `hroot : Polynomial.aeval y (minpoly ℚ pb.gen) = 0`. Establish `hmp : minpoly ℚ pb.gen = minpoly ℚ z`. Conclude with `IntermediateField.minpoly_gen ℚ z`. Rewrite using `[hmp, ← Polynomial.cyclotomic_eq_minpoly_rat hz hpos, Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]`.

Conclude with `hy.isRoot_cyclotomic hpos`. Set `ψ` to `pb.lift y hroot`. Establish `hle : cycAway n ≤ (IntermediateField.adjoin ℚ {z}).toSubring`. Use `Subring.closure_le.2 ?_` and prove the remaining obligations. Introduce and unpack `x (rfl | rfl)`.

Conclude with `IntermediateField.mem_adjoin_simple_self ℚ z`. Use `show _ ∈ IntermediateField.adjoin ℚ {z}`. Conclude with `inv_mem (IntermediateField.natCast_mem _ n)`. Use `⟨(ψ : IntermediateField.adjoin ℚ {z} →+* F).comp (Subring.inclusion hle), ?_, ?_⟩` and prove the remaining obligations. Conclude with `((ψ : IntermediateField.adjoin ℚ {z} →+* F).injective).comp (Subring.inclusion_injective hle)`.

Express the relevant statement in the definitionally equal form `ψ pb.gen = y`. Conclude with `PowerBasis.lift_gen _ _ _`.
-/
theorem exists_hom {n : ℕ} (hn : n ≠ 0) {F : Type} [Field F] [CharZero F] {y : F} (hy : IsPrimitiveRoot y n) :
    ∃ f : cycAway n →+* F, Function.Injective f ∧ f (zetaAway n) = y := by
  have hpos : 0 < n := Nat.pos_of_ne_zero hn
  set z : ℂ := ((zetaAway n : cycAway n) : ℂ) with hzdef
  have hz : IsPrimitiveRoot z n := (isPrimitiveRoot_zetaAway hn).map_of_injective (f := (cycAway n).subtype) Subtype.val_injective
  have hint : IsIntegral ℚ z := (hz.isIntegral hpos).tower_top
  let pb := IntermediateField.adjoin.powerBasis hint
  have hgen : pb.gen = IntermediateField.AdjoinSimple.gen ℚ z := rfl
  have hroot : Polynomial.aeval y (minpoly ℚ pb.gen) = 0 := by
    have hmp : minpoly ℚ pb.gen = minpoly ℚ z := by
      exact IntermediateField.minpoly_gen ℚ z
    rw [hmp, ← Polynomial.cyclotomic_eq_minpoly_rat hz hpos, Polynomial.aeval_def,
      Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]
    exact hy.isRoot_cyclotomic hpos
  let ψ := pb.lift y hroot
  have hle : cycAway n ≤ (IntermediateField.adjoin ℚ {z}).toSubring := by
    refine Subring.closure_le.2 ?_
    rintro x (rfl | rfl)
    · exact IntermediateField.mem_adjoin_simple_self ℚ z
    · show _ ∈ IntermediateField.adjoin ℚ {z}
      exact inv_mem (IntermediateField.natCast_mem _ n)
  refine ⟨(ψ : IntermediateField.adjoin ℚ {z} →+* F).comp (Subring.inclusion hle), ?_, ?_⟩
  · exact ((ψ : IntermediateField.adjoin ℚ {z} →+* F).injective).comp (Subring.inclusion_injective hle)
  · change ψ pb.gen = y
    exact PowerBasis.lift_gen _ _ _

end GlobalTheory.SiegelTor.CycLift

namespace GlobalTheory.SiegelTor.CycLift

/- English proof (translation)
Introduce `n hn3 K _ _ β`. Establish `hn : n ≠ 0` using `by omega`. Establish `hβζ` using `isPrimitiveRoot_map hn β`. Establish `hnK : (n : K) ≠ 0` using `by simpa using ((isUnit_natCast hn).map β).ne_zero`. Take `⟨p, hp⟩` from `CharP.exists K`.

Break down `CharP.char_is_prime_or_zero K p with hpp | hp0` into its components or cases. Use `haveI : Fact p.Prime := ⟨hpp⟩ haveI := charZero_witt p K`. Establish `hinj` using `IsFractionRing.injective (WittVector p K) (FractionRing (WittVector p K))`. Use `haveI : CharZero (FractionRing (WittVector p K)) := charZero_of_injective_algebraMap hinj`. Establish `hc : ∀ a : K, (WittVector.constantCoeff : WittVector p K →+* K) (WittVector.teichmuller p a) = a` using `fun a => by rw [WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero]`.

Use `set t : WittVector p K := WittVector.teichmuller p (β (zetaAway n)) with ht_def`. Establish `ht : IsPrimitiveRoot t n`. Use `⟨?_, fun l hl => hβζ.dvd_of_pow_eq_one l ?_⟩` and prove the remaining obligations. Rewrite using `[ht_def, ← map_pow, hβζ.pow_eq_one, map_one]`. Use `congrArg (WittVector.constantCoeff : WittVector p K →+* K) hl` as an intermediate fact.

Rewrite `this` using `[map_pow, map_one, hc]`. Then use the resulting hypothesis. Take `⟨f, hf, hfζ⟩` from `exists_hom hn (ht.map_of_injective hinj)`. Establish `hnW : IsUnit (n : WittVector p K)` using `WittVector.isUnit_of_coeff_zero_ne_zero _ (by rw [← WittVector.constantCoeff_apply, map_natCast]; exact hnK)`. Establish `hmem : ∀ x, f x ∈ (algebraMap (WittVector p K) (FractionRing (WittVector p K))).range`. Introduce and unpack `⟨x, hx⟩`.

Proceed by induction on `hx using Subring.closure_induction with`. Consider the case `mem x hx`. Break down `hx with rfl | hx'` into its components or cases. Conclude with `⟨t, hfζ.symm⟩`. Substitute `hx'` using the available equality.

Use `⟨↑hnW.unit⁻¹, ?_⟩` and prove the remaining obligations. Apply `mul_right_cancel₀ (Nat.cast_ne_zero.2 hn : (n : FractionRing (WittVector p K)) ≠ 0)` to reduce the goal to its premises. Establish `e1 : algebraMap (WittVector p K) (FractionRing (WittVector p K)) ↑hnW.unit⁻¹ * n = 1`. Rewrite using `[← map_natCast (algebraMap (WittVector p K) (FractionRing (WittVector p K))) n, ← map_mul, hnW.val_inv_mul, map_one]`. Establish `hu : (⟨(n : ℂ)⁻¹, Subring.subset_closure (Or.inr rfl)⟩ : cycAway n) * (n : cycAway n) = 1` using `Subtype.ext (by simp [inv_mul_cancel₀ (Nat.cast_ne_zero.2 hn : (n : ℂ) ≠ 0)])`.

Establish `e2` using `congrArg f hu`. Rewrite `e2` using `[map_mul, map_natCast, map_one]`. Conclude with `e1.trans e2.symm`. Consider the case `zero => show f 0 ∈ _`. Rewrite using `[map_zero]`.

Conclude with `zero_mem _`. Consider the case `one => show f 1 ∈ _`. Rewrite using `[map_one]`. Conclude with `one_mem _`. Consider the case `add x y hx hy ihx ihy => show f (⟨x, hx⟩ + ⟨y, hy⟩) ∈ _`.

Rewrite using `[map_add]`. Conclude with `add_mem ihx ihy`. Consider the case `neg x hx ih => show f (-⟨x, hx⟩) ∈ _`. Rewrite using `[map_neg]`. Conclude with `neg_mem ih`.

Consider the case `mul x y hx hy ihx ihy => show f (⟨x, hx⟩ * ⟨y, hy⟩) ∈ _`. Rewrite using `[map_mul]`. Conclude with `mul_mem ihx ihy`. Set `e : WittVector p K ≃+* (algebraMap (WittVector p K) (FractionRing (WittVector p K))).range` to `RingEquiv.ofBijective (algebraMap (WittVector p K) (FractionRing (WittVector p K))).rangeRestrict ⟨fun a b h => hinj (congrArg Subtype.val h), RingHom.rangeRestrict_surjective _⟩`. Set `βV : cycAway n →+* WittVector p K` to `e.symm.toRingHom.comp (f.codRestrict _ hmem)`.

Establish `hβV : ∀ x, algebraMap (WittVector p K) (FractionRing (WittVector p K)) (βV x) = f x` using `fun x => congrArg Subtype.val (e.apply_symm_apply (f.codRestrict _ hmem x))`. Use `⟨WittVector p K, inferInstance, inferInstance, inferInstance, inferInstance, βV, WittVector.constantCoeff, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[(WittVector.irreducible p).maximalIdeal_eq]`. Conclude with `WittVector.isAdicCompleteIdealSpanP`. Conclude with `fun a b h => hf (by rw [← hβV, ← hβV, h])`.

Conclude with `fun a => ⟨WittVector.teichmuller p a, hc a⟩`. Use `hom_ext hn _ _ ?_` and prove the remaining obligations. Establish `h1 : βV (zetaAway n) = t` using `hinj (by rw [hβV, hfζ])`. Use `show WittVector.constantCoeff (βV (zetaAway n)) = β (zetaAway n)`. Rewrite using `[h1, hc]`.

Substitute `hp0 haveI : CharZero K := CharP.charP_to_charZero K` using the available equality. Take `⟨f, hf, hfζ⟩` from `exists_hom hn hβζ`. Establish `hβ : β = f` using `hom_ext hn _ _ hfζ.symm`. Use `⟨K, inferInstance, inferInstance, inferInstance, inferInstance, β, RingHom.id K, ?_, hβ ▸ hf, fun x => ⟨x, rfl⟩, RingHom.id_comp β⟩` and prove the remaining obligations. Rewrite using `[IsLocalRing.maximalIdeal_eq_bot]`.

Use `infer_instance`.
-/
theorem exists_complete_domain_lift : ∀ (n : ℕ), 3 ≤ n → ∀ (K : Type) [Field K] [IsAlgClosed K] (β : cycAway n →+* K),
    ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsLocalRing V) (_ : IsNoetherianRing V) (βV : cycAway n →+* V)
      (π : V →+* K), IsAdicComplete (IsLocalRing.maximalIdeal V) V ∧ Function.Injective βV ∧ Function.Surjective π ∧
        π.comp βV = β := by
  intro n hn3 K _ _ β
  have hn : n ≠ 0 := by omega
  have hβζ := isPrimitiveRoot_map hn β
  have hnK : (n : K) ≠ 0 := by simpa using ((isUnit_natCast hn).map β).ne_zero
  obtain ⟨p, hp⟩ := CharP.exists K
  rcases CharP.char_is_prime_or_zero K p with hpp | hp0
  · haveI : Fact p.Prime := ⟨hpp⟩
    haveI := charZero_witt p K
    have hinj := IsFractionRing.injective (WittVector p K) (FractionRing (WittVector p K))
    haveI : CharZero (FractionRing (WittVector p K)) := charZero_of_injective_algebraMap hinj
    have hc : ∀ a : K, (WittVector.constantCoeff : WittVector p K →+* K) (WittVector.teichmuller p a) = a :=
      fun a => by rw [WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero]
    set t : WittVector p K := WittVector.teichmuller p (β (zetaAway n)) with ht_def
    have ht : IsPrimitiveRoot t n := by
      refine ⟨?_, fun l hl => hβζ.dvd_of_pow_eq_one l ?_⟩
      · rw [ht_def, ← map_pow, hβζ.pow_eq_one, map_one]
      · have := congrArg (WittVector.constantCoeff : WittVector p K →+* K) hl
        rwa [map_pow, map_one, hc] at this
    obtain ⟨f, hf, hfζ⟩ := exists_hom hn (ht.map_of_injective hinj)
    have hnW : IsUnit (n : WittVector p K) :=
      WittVector.isUnit_of_coeff_zero_ne_zero _ (by rw [← WittVector.constantCoeff_apply, map_natCast]; exact hnK)
    have hmem : ∀ x, f x ∈ (algebraMap (WittVector p K) (FractionRing (WittVector p K))).range := by
      rintro ⟨x, hx⟩
      induction hx using Subring.closure_induction with
      | mem x hx =>
        rcases hx with rfl | hx'
        · exact ⟨t, hfζ.symm⟩
        · subst hx'
          refine ⟨↑hnW.unit⁻¹, ?_⟩
          apply mul_right_cancel₀ (Nat.cast_ne_zero.2 hn : (n : FractionRing (WittVector p K)) ≠ 0)
          have e1 : algebraMap (WittVector p K) (FractionRing (WittVector p K)) ↑hnW.unit⁻¹ * n = 1 := by
            rw [← map_natCast (algebraMap (WittVector p K) (FractionRing (WittVector p K))) n, ← map_mul,
              hnW.val_inv_mul, map_one]
          have hu : (⟨(n : ℂ)⁻¹, Subring.subset_closure (Or.inr rfl)⟩ : cycAway n) * (n : cycAway n) = 1 :=
            Subtype.ext (by simp [inv_mul_cancel₀ (Nat.cast_ne_zero.2 hn : (n : ℂ) ≠ 0)])
          have e2 := congrArg f hu
          rw [map_mul, map_natCast, map_one] at e2
          exact e1.trans e2.symm
      | zero => show f 0 ∈ _; rw [map_zero]; exact zero_mem _
      | one => show f 1 ∈ _; rw [map_one]; exact one_mem _
      | add x y hx hy ihx ihy =>
        show f (⟨x, hx⟩ + ⟨y, hy⟩) ∈ _; rw [map_add]; exact add_mem ihx ihy
      | neg x hx ih => show f (-⟨x, hx⟩) ∈ _; rw [map_neg]; exact neg_mem ih
      | mul x y hx hy ihx ihy =>
        show f (⟨x, hx⟩ * ⟨y, hy⟩) ∈ _; rw [map_mul]; exact mul_mem ihx ihy
    let e : WittVector p K ≃+* (algebraMap (WittVector p K) (FractionRing (WittVector p K))).range :=
      RingEquiv.ofBijective (algebraMap (WittVector p K) (FractionRing (WittVector p K))).rangeRestrict
        ⟨fun a b h => hinj (congrArg Subtype.val h), RingHom.rangeRestrict_surjective _⟩
    let βV : cycAway n →+* WittVector p K := e.symm.toRingHom.comp (f.codRestrict _ hmem)
    have hβV : ∀ x, algebraMap (WittVector p K) (FractionRing (WittVector p K)) (βV x) = f x := fun x =>
      congrArg Subtype.val (e.apply_symm_apply (f.codRestrict _ hmem x))
    refine ⟨WittVector p K, inferInstance, inferInstance, inferInstance, inferInstance, βV, WittVector.constantCoeff,
      ?_, ?_, ?_, ?_⟩
    · rw [(WittVector.irreducible p).maximalIdeal_eq]
      exact WittVector.isAdicCompleteIdealSpanP
    · exact fun a b h => hf (by rw [← hβV, ← hβV, h])
    · exact fun a => ⟨WittVector.teichmuller p a, hc a⟩
    · refine hom_ext hn _ _ ?_
      have h1 : βV (zetaAway n) = t := hinj (by rw [hβV, hfζ])
      show WittVector.constantCoeff (βV (zetaAway n)) = β (zetaAway n)
      rw [h1, hc]
  · subst hp0
    haveI : CharZero K := CharP.charP_to_charZero K
    obtain ⟨f, hf, hfζ⟩ := exists_hom hn hβζ
    have hβ : β = f := hom_ext hn _ _ hfζ.symm
    refine ⟨K, inferInstance, inferInstance, inferInstance, inferInstance, β, RingHom.id K, ?_, hβ ▸ hf,
      fun x => ⟨x, rfl⟩, RingHom.id_comp β⟩
    rw [IsLocalRing.maximalIdeal_eq_bot]
    infer_instance

end GlobalTheory.SiegelTor.CycLift
