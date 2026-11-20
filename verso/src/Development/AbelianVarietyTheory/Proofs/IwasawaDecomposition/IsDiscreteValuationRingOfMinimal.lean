import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FinrankEqZeroIff
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsDiscreteValuationRingAndFiniteResidueFieldValu

open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam
open Formalism.MainNotions.DIV.Cons (SCF intO)
open GlobalTheory.LocM GlobalTheory.LocM.Cht

namespace GlobalTheory.SpecialStalk

/- English proof (translation)
Take `⟨l, hl⟩` from `CharP.exists k`. Break down `CharP.char_is_prime_or_zero k l with h | rfl` into its components or cases. Distinguish the cases in `e : l = p`. Conclude with `e ▸ CharP.cast_eq_zero k l`. It suffices to derive a contradiction.

Establish `hc : IsCoprime (l : V) (p : V)` using `Nat.Coprime.cast ((Nat.coprime_primes h hp).2 e)`. Establish `hu : IsUnit (l : V)`. Assume the negation of the conclusion as `hn`. Take `⟨a, b, hab⟩` from `hc`. Conclude with `(maximalIdeal.isMaximal V).ne_top ((Ideal.eq_top_iff_one _).2 (hab ▸ add_mem (Ideal.mul_mem_left _ _ ((mem_maximalIdeal _).2 hn)) (Ideal.mul_mem_left _ _ hV)))`.

Use `(hu.map φ).ne_zero` as an intermediate fact. Rewrite `this` using `[map_natCast]`. Conclude with `this (CharP.cast_eq_zero k l)`. Conclude with `absurd (CharP.charP_to_charZero k) hk`.
-/
theorem natCast_eq_zero_of_not_charZero {V k : Type} [CommRing V] [IsLocalRing V] [Field k] (φ : V →+* k) {p : ℕ}
    (hp : p.Prime) (hV : (p : V) ∈ maximalIdeal V) (hk : ¬ CharZero k) : (p : k) = 0 := by
  obtain ⟨l, hl⟩ := CharP.exists k
  rcases CharP.char_is_prime_or_zero k l with h | rfl
  · by_cases e : l = p
    · exact e ▸ CharP.cast_eq_zero k l
    · exfalso
      have hc : IsCoprime (l : V) (p : V) := Nat.Coprime.cast ((Nat.coprime_primes h hp).2 e)
      have hu : IsUnit (l : V) := by
        by_contra hn
        obtain ⟨a, b, hab⟩ := hc
        exact (maximalIdeal.isMaximal V).ne_top ((Ideal.eq_top_iff_one _).2 (hab ▸ add_mem
          (Ideal.mul_mem_left _ _ ((mem_maximalIdeal _).2 hn)) (Ideal.mul_mem_left _ _ hV)))
      have := (hu.map φ).ne_zero
      rw [map_natCast] at this
      exact this (CharP.cast_eq_zero k l)
  · exact absurd (CharP.charP_to_charZero k) hk

/- English proof (translation)
Establish `hne : maximalIdeal R ≠ ⊥` using `fun e => ha (by simpa [e] using hm)`. Establish `hf : ¬ IsField R` using `fun hf => hne (isField_iff_maximalIdeal_eq.1 hf)`. Establish `hmin : maximalIdeal R ∈ (Ideal.span {a}).minimalPrimes` using `⟨⟨inferInstance, (Ideal.span_singleton_le_iff_mem _).2 hm⟩, fun P hP _ => (h P hP.1 ((Ideal.span_singleton_le_iff_mem _).1 hP.2)).ge⟩`. Establish `hle : (maximalIdeal R).height ≤ 1` using `Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _ hmin`. Establish `key` using `(IsDiscreteValuationRing.TFAE R hf).out 3 0`.

Use `key.1 ⟨inferInstance, maximalIdeal R, ⟨hne, inferInstance⟩, fun P hP => ?_⟩` and prove the remaining obligations. Use `hP.2` as an intermediate fact. Assume the negation of the conclusion as `hn`. Establish `h1` using `Ideal.height_strict_mono_of_isPrime (lt_of_le_of_ne (le_maximalIdeal hP.2.ne_top) hn)`. Conclude with `hP.1 (Ideal.height_eq_zero_iff_eq_bot.1 (Order.lt_one_iff.1 (h1.trans_le hle)))`.
-/
theorem isDiscreteValuationRing_of_minimal {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    [IsIntegrallyClosed R] {a : R} (ha : a ≠ 0) (hm : a ∈ maximalIdeal R)
    (h : ∀ P : Ideal R, P.IsPrime → a ∈ P → P = maximalIdeal R) : IsDiscreteValuationRing R := by
  have hne : maximalIdeal R ≠ ⊥ := fun e => ha (by simpa [e] using hm)
  have hf : ¬ IsField R := fun hf => hne (isField_iff_maximalIdeal_eq.1 hf)
  have hmin : maximalIdeal R ∈ (Ideal.span {a}).minimalPrimes :=
    ⟨⟨inferInstance, (Ideal.span_singleton_le_iff_mem _).2 hm⟩, fun P hP _ =>
      (h P hP.1 ((Ideal.span_singleton_le_iff_mem _).1 hP.2)).ge⟩
  have hle : (maximalIdeal R).height ≤ 1 := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _ hmin
  have key := (IsDiscreteValuationRing.TFAE R hf).out 3 0
  refine key.1 ⟨inferInstance, maximalIdeal R, ⟨hne, inferInstance⟩, fun P hP => ?_⟩
  have := hP.2
  by_contra hn
  have h1 := Ideal.height_strict_mono_of_isPrime (lt_of_le_of_ne (le_maximalIdeal hP.2.ne_top) hn)
  exact hP.1 (Ideal.height_eq_zero_iff_eq_bot.1 (Order.lt_one_iff.1 (h1.trans_le hle)))

/- English proof (translation)
Take `⟨o, ho, hne, hs⟩` from `NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent _ (irreducibleComponent_mem_irreducibleComponents x)`. Take `⟨y, hyo, hyU⟩` from `hd.inter_open_nonempty o ho hne`. Take `⟨ξ, hξ⟩` from `QuasiSober.sober (isIrreducible_irreducibleComponent (x := x)) isClosed_irreducibleComponent`. Establish `e` using `hx ξ (hξ.specializes mem_irreducibleComponent)`. Conclude with `(e ▸ hξ.specializes (hs hyo)).mem_open hU hyU`.
-/
theorem mem_of_dense {X : Type} [TopologicalSpace X] [NoetherianSpace X] [QuasiSober X] {x : X}
    (hx : ∀ y, y ⤳ x → y = x) {U : Set X} (hU : IsOpen U) (hd : Dense U) : x ∈ U := by
  obtain ⟨o, ho, hne, hs⟩ := NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent _
    (irreducibleComponent_mem_irreducibleComponents x)
  obtain ⟨y, hyo, hyU⟩ := hd.inter_open_nonempty o ho hne
  obtain ⟨ξ, hξ⟩ := QuasiSober.sober (isIrreducible_irreducibleComponent (x := x)) isClosed_irreducibleComponent
  have e := hx ξ (hξ.specializes mem_irreducibleComponent)
  exact (e ▸ hξ.specializes (hs hyo)).mem_open hU hyU

/- English proof (translation)
Take `⟨_, ⟨U, hU, rfl⟩, hx, -⟩` from `X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ`. Establish `h1 : Countable Γ(Sp V, ⊤)` using `(ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of V)).hom).1.countable`. Establish `h2 : (f.appLE ⊤ U le_top).hom.FiniteType` using `f.finiteType_appLE (isAffineOpen_top _) hU _`. Establish `h3 : Countable Γ(X, U)`. Take `⟨n, g, hg⟩` from `(@Algebra.FiniteType.iff_quotient_mvPolynomial'' _ _ _ _ (f.appLE ⊤ U le_top).hom.toAlgebra).1 h2`.

Establish `: Countable (MvPolynomial (Fin n) Γ(Sp V, ⊤))` using `AddMonoidAlgebra.coeff_injective.countable`. Conclude with `hg.countable`. Set `_` to `X.presheaf.algebra_section_stalk (U := U) ⟨x, hx⟩`. Use `hU.isLocalization_stalk ⟨x, hx⟩` as an intermediate fact. Conclude with `(IsLocalization.mk'_surjective (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl).countable`.
-/
theorem countable_stalk {V : Type} [CommRing V] [Countable V] {X : Scheme.{0}} (f : X ⟶ Sp V) [LocallyOfFiniteType f]
    (x : X) : Countable (X.presheaf.stalk x) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hx, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have h1 : Countable Γ(Sp V, ⊤) :=
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of V)).hom).1.countable
  have h2 : (f.appLE ⊤ U le_top).hom.FiniteType := f.finiteType_appLE (isAffineOpen_top _) hU _
  have h3 : Countable Γ(X, U) := by
    obtain ⟨n, g, hg⟩ := (@Algebra.FiniteType.iff_quotient_mvPolynomial'' _ _ _ _ (f.appLE ⊤ U le_top).hom.toAlgebra).1 h2
    have : Countable (MvPolynomial (Fin n) Γ(Sp V, ⊤)) := AddMonoidAlgebra.coeff_injective.countable
    exact hg.countable
  let _ := X.presheaf.algebra_section_stalk (U := U) ⟨x, hx⟩
  have := hU.isLocalization_stalk ⟨x, hx⟩
  exact (IsLocalization.mk'_surjective (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl).countable

noncomputable def toStalk {V : Type} [CommRing V] {X : Scheme.{0}} (f : X ⟶ Sp V) (x : X) : V →+* X.presheaf.stalk x :=
  (f.stalkMap x).hom.comp
    (((Sp V).presheaf.germ ⊤ (f x) trivial).hom.comp (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom)

/- English proof (translation)
Establish `fl : (toStalk f x).Flat`. Use `RingHom.Flat.comp (RingHom.Flat.comp (RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of V)).inv)) ?_) (Flat.stalkMap f x)` and prove the remaining obligations. Establish `hU` using `isAffineOpen_top (Sp V)`. Set `_` to `(Sp V).presheaf.algebra_section_stalk (U := ⊤) ⟨f x, trivial⟩`. Use `hU.isLocalization_stalk ⟨f x, trivial⟩` as an intermediate fact.

Conclude with `IsLocalization.flat ((Sp V).presheaf.stalk ((⟨f x, trivial⟩ : (⊤ : (Sp V).Opens)) : Sp V)) (hU.primeIdealOf ⟨f x, trivial⟩).asIdeal.primeCompl`. Set `_` to `(toStalk f x).toAlgebra`. Establish `: Module.Flat V (X.presheaf.stalk x)` using `fl`. Conclude with `charZero_of_injective_algebraMap (FaithfulSMul.algebraMap_injective V _)`.
-/
theorem charZero_stalk {V : Type} [CommRing V] [IsDomain V] [CharZero V] {X : Scheme.{0}} (f : X ⟶ Sp V) [Flat f]
    (x : X) : CharZero (X.presheaf.stalk x) := by
  have fl : (toStalk f x).Flat := by
    refine RingHom.Flat.comp (RingHom.Flat.comp (RingHom.Flat.of_bijective
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of V)).inv)) ?_) (Flat.stalkMap f x)
    have hU := isAffineOpen_top (Sp V)
    let _ := (Sp V).presheaf.algebra_section_stalk (U := ⊤) ⟨f x, trivial⟩
    have := hU.isLocalization_stalk ⟨f x, trivial⟩
    exact IsLocalization.flat ((Sp V).presheaf.stalk ((⟨f x, trivial⟩ : (⊤ : (Sp V).Opens)) : Sp V))
      (hU.primeIdealOf ⟨f x, trivial⟩).asIdeal.primeCompl
  let _ := (toStalk f x).toAlgebra
  have : Module.Flat V (X.presheaf.stalk x) := fl
  exact charZero_of_injective_algebraMap (FaithfulSMul.algebraMap_injective V _)

/- English proof (translation)
Introduce `hc`. Use `charZero_of_injective_ringHom (f := (Scheme.Spec.residueFieldIso (X.presheaf.stalk x) q).hom.hom.comp ((X.fromSpecStalk x).residueFieldMap q).hom) (RingHom.injective _)` as an intermediate fact. Use `q.isPrime` as an intermediate fact. Establish `h1` using `Ideal.algebraMap_residueField_eq_zero.2 h`. Rewrite `h1` using `[map_natCast]`.

Conclude with `hp (by exact_mod_cast h1)`.
-/
theorem not_charZero_fromSpecStalk {X : Scheme.{0}} (x : X) (q : Spec (X.presheaf.stalk x)) {p : ℕ} (hp : p ≠ 0)
    (h : (p : X.presheaf.stalk x) ∈ q.asIdeal) : ¬ CharZero (X.residueField (X.fromSpecStalk x q)) := by
  intro hc
  have := charZero_of_injective_ringHom (f := (Scheme.Spec.residueFieldIso (X.presheaf.stalk x) q).hom.hom.comp
    ((X.fromSpecStalk x).residueFieldMap q).hom) (RingHom.injective _)
  have := q.isPrime
  have h1 := Ideal.algebraMap_residueField_eq_zero.2 h
  rw [map_natCast] at h1
  exact hp (by exact_mod_cast h1)

/- English proof (translation)
Introduce `E _ _ _ H Dw Xo p W Y i₀ hp hW Z η`. Use `Z.i.c.fin` as an intermediate fact. Establish `: NumberField Z.i.c.F` using `{}`. Establish `hW' : (p : Z.i.c.F) ∈ (Z.i.c.V W).nonunits`. Rewrite `hW`, the goal using `[ValuationSubring.mem_nonunits_iff_or]`.

Break down `hW with h | h` into its components or cases. Conclude with `absurd (by exact_mod_cast h) hp.ne_zero`. Conclude with `Or.inr fun h' => h (by simpa [Coeff.V] using h')`. Use `(isDiscreteValuationRing_and_finite_residueField_of_numberField (Z.i.c.V W) hp.ne_zero hW').1` as an intermediate fact. Establish `hV : (p : Z.i.c.V W) ∈ maximalIdeal (Z.i.c.V W)`.

Rewrite using `[← ValuationSubring.coe_mem_nonunits_iff]`. Simplify using `using hW'`. Establish `: Countable Z.i.c.F` using `Countable.of_equiv _ (Module.finBasis ℚ Z.i.c.F).equivFun.toEquiv.symm`. Establish `: IsProper (PSpace.str (Z.i.c.V W) Z.n)` using `isProper_str _ _`. Establish `: IsProper Z.s` using `inferInstanceAs (IsProper (Z.I.subschemeι ≫ PSpace.str (Z.i.c.V W) Z.n))`.

Use `Z.flat` as an intermediate fact. Establish `: IsLocallyNoetherian Z.X` using `LocallyOfFiniteType.isLocallyNoetherian Z.s`. Establish `: CompactSpace Z.X` using `QuasiCompact.compactSpace_of_compactSpace Z.s`. Establish `: IsNoetherian Z.X` using `{}`. Establish `hdom` using `Z.normal.isDomain_stalk η.1`.

Use `Z.normal.isIntegrallyClosed_stalk η.1` as an intermediate fact. Establish `hcz` using `charZero_stalk Z.s η.1`. Establish `hm : (p : Z.X.presheaf.stalk η.1) ∈ maximalIdeal (Z.X.presheaf.stalk η.1)`. Rewrite using `[← residue_eq_zero_iff, map_natCast]`. Conclude with `natCast_eq_zero_of_not_charZero ((residue _).comp (toStalk Z.s η.1)) hp hV η.2.1`.

Establish `hsp : ∀ q : Spec (Z.X.presheaf.stalk η.1), Z.X.fromSpecStalk η.1 q ⤳ η.1` using `fun q => by`. Establish `: Z.X.fromSpecStalk η.1 q ∈ Set.range (Z.X.fromSpecStalk η.1)` using `⟨q, rfl⟩`. Rewrite `this` using `[Scheme.range_fromSpecStalk]`. Then use the resulting hypothesis. Use `⟨hdom, isDiscreteValuationRing_of_minimal (Nat.cast_ne_zero.2 hp.ne_zero) hm fun P hP h => ?_, hcz, countable_stalk Z.s η.1, hm, fun q hq => mem_of_dense (fun y hy => ?_) ?_ Z.dense⟩` and prove the remaining obligations. Establish `e` using `η.2.2 _ (not_charZero_fromSpecStalk η.1 (⟨P, hP⟩ : PrimeSpectrum _) hp.ne_zero h) (hsp _)`.

Conclude with `congrArg PrimeSpectrum.asIdeal ((Z.X.fromSpecStalk η.1).isEmbedding.injective (e.trans Scheme.fromSpecStalk_closedPoint.symm))`. Choose the witnesses or unpack the hypotheses as in `⟨q', rfl⟩ : y ∈ Set.range (Z.X.fromSpecStalk η.1) := by`. Rewrite using `[Scheme.range_fromSpecStalk]`. Conclude with `hy.trans (hsp q)`. Establish `h` using `(PrimeSpectrum.le_iff_specializes q' q).2 ((Z.X.fromSpecStalk η.1).isEmbedding.isInducing.specializes_iff.1 hy)`.

Conclude with `congrArg _ (le_antisymm (α := PrimeSpectrum _) h (show q.asIdeal ≤ q'.asIdeal from hq ▸ bot_le))`. Rewrite using `[← Z.cover]`. Conclude with `isOpen_iUnion fun a => (Z.U a).1.2`.
-/
theorem stalkSt : GlobalTheory.LocM.Cht.StalkSt := by
  intro E _ _ _ H Dw Xo p W Y i₀ hp hW Z η
  have := Z.i.c.fin
  have : NumberField Z.i.c.F := {}
  have hW' : (p : Z.i.c.F) ∈ (Z.i.c.V W).nonunits := by
    rw [ValuationSubring.mem_nonunits_iff_or] at hW ⊢
    rcases hW with h | h
    · exact absurd (by exact_mod_cast h) hp.ne_zero
    · exact Or.inr fun h' => h (by simpa [Coeff.V] using h')
  have := (isDiscreteValuationRing_and_finite_residueField_of_numberField (Z.i.c.V W) hp.ne_zero hW').1
  have hV : (p : Z.i.c.V W) ∈ maximalIdeal (Z.i.c.V W) := by
    rw [← ValuationSubring.coe_mem_nonunits_iff]
    simpa using hW'
  have : Countable Z.i.c.F := Countable.of_equiv _ (Module.finBasis ℚ Z.i.c.F).equivFun.toEquiv.symm
  have : IsProper (PSpace.str (Z.i.c.V W) Z.n) := isProper_str _ _
  have : IsProper Z.s := inferInstanceAs (IsProper (Z.I.subschemeι ≫ PSpace.str (Z.i.c.V W) Z.n))
  have := Z.flat
  have : IsLocallyNoetherian Z.X := LocallyOfFiniteType.isLocallyNoetherian Z.s
  have : CompactSpace Z.X := QuasiCompact.compactSpace_of_compactSpace Z.s
  have : IsNoetherian Z.X := {}
  have hdom := Z.normal.isDomain_stalk η.1
  have := Z.normal.isIntegrallyClosed_stalk η.1
  have hcz := charZero_stalk Z.s η.1
  have hm : (p : Z.X.presheaf.stalk η.1) ∈ maximalIdeal (Z.X.presheaf.stalk η.1) := by
    rw [← residue_eq_zero_iff, map_natCast]
    exact natCast_eq_zero_of_not_charZero ((residue _).comp (toStalk Z.s η.1)) hp hV η.2.1
  have hsp : ∀ q : Spec (Z.X.presheaf.stalk η.1), Z.X.fromSpecStalk η.1 q ⤳ η.1 := fun q => by
    have : Z.X.fromSpecStalk η.1 q ∈ Set.range (Z.X.fromSpecStalk η.1) := ⟨q, rfl⟩
    rwa [Scheme.range_fromSpecStalk] at this
  refine ⟨hdom, isDiscreteValuationRing_of_minimal (Nat.cast_ne_zero.2 hp.ne_zero) hm fun P hP h => ?_, hcz,
    countable_stalk Z.s η.1, hm, fun q hq => mem_of_dense (fun y hy => ?_) ?_ Z.dense⟩
  · have e := η.2.2 _ (not_charZero_fromSpecStalk η.1 (⟨P, hP⟩ : PrimeSpectrum _) hp.ne_zero h) (hsp _)
    exact congrArg PrimeSpectrum.asIdeal ((Z.X.fromSpecStalk η.1).isEmbedding.injective
      (e.trans Scheme.fromSpecStalk_closedPoint.symm))
  · obtain ⟨q', rfl⟩ : y ∈ Set.range (Z.X.fromSpecStalk η.1) := by
      rw [Scheme.range_fromSpecStalk]
      exact hy.trans (hsp q)
    have h := (PrimeSpectrum.le_iff_specializes q' q).2
      ((Z.X.fromSpecStalk η.1).isEmbedding.isInducing.specializes_iff.1 hy)
    exact congrArg _ (le_antisymm (α := PrimeSpectrum _) h (show q.asIdeal ≤ q'.asIdeal from hq ▸ bot_le))
  · rw [← Z.cover]
    exact isOpen_iUnion fun a => (Z.U a).1.2

end GlobalTheory.SpecialStalk
