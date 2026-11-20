import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SmoothOfRelativeDimensionDescendsEtaleCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapComapMaximalIdealEqOfFormallyUnramifiedStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FieldPair.UnramOrd

variable {k K : Type} [Field k] [Field K] {c : k →+* K}

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hx`. Conclude with `⟨fun h => hx.ne_zero (Subtype.ext h), E.ord_eq_zero hx⟩`. Introduce and unpack `⟨h0, h1⟩`. Establish `hm : (x : K)⁻¹ ∈ E.ring`.

Rewrite using `[← E.ord_nonneg_iff (inv_ne_zero h0), E.ord_inv, h1]`. Simplify using the standard rewrite rules. Conclude with `IsUnit.of_mul_eq_one ⟨_, hm⟩ (Subtype.ext (mul_inv_cancel₀ h0))`.
-/
theorem isUnit_iff (E : Place c) (x : E.ring) : IsUnit x ↔ (x : K) ≠ 0 ∧ E.ord x = 0 := by
  constructor
  · intro hx
    exact ⟨fun h => hx.ne_zero (Subtype.ext h), E.ord_eq_zero hx⟩
  · rintro ⟨h0, h1⟩
    have hm : (x : K)⁻¹ ∈ E.ring := by
      rw [← E.ord_nonneg_iff (inv_ne_zero h0), E.ord_inv, h1]; simp
    exact IsUnit.of_mul_eq_one ⟨_, hm⟩ (Subtype.ext (mul_inv_cancel₀ h0))

def incl (E : Place c) {T : Subring K} (h : E.Contains T) : T →+* E.ring :=
  T.subtype.codRestrict E.ring fun x => h x x.2

/- English proof (translation)
Use `letI := (incl E h.1).toAlgebra`. Use `⟨fun y => y.2, fun z => ?_, fun {x y} e => ⟨1, ?_⟩⟩` and prove the remaining obligations. Take `⟨a, ha, b, hb, hb0, hbo, e⟩` from `h.2 z z.2`. Establish `hu : IsUnit (incl E h.1 ⟨b, hb⟩)` using `(isUnit_iff E _).2 ⟨hb0, hbo⟩`. Conclude with `⟨⟨⟨a, ha⟩, ⟨⟨b, hb⟩, hu⟩⟩, Subtype.ext e⟩`.

Establish `e' : (x : K) = y` using `congrArg (fun z : E.ring => (z : K)) e`. Simplify using `only [OneMemClass.coe_one, one_mul]`. Conclude with `Subtype.ext e'`.
-/
theorem isLocalization (E : Place c) {T : Subring K} (h : E.IsPrimeOf T) :
    letI := (incl E h.1).toAlgebra
    IsLocalization ((IsUnit.submonoid E.ring).comap (incl E h.1)) E.ring := by
  letI := (incl E h.1).toAlgebra
  refine ⟨fun y => y.2, fun z => ?_, fun {x y} e => ⟨1, ?_⟩⟩
  · obtain ⟨a, ha, b, hb, hb0, hbo, e⟩ := h.2 z z.2
    have hu : IsUnit (incl E h.1 ⟨b, hb⟩) := (isUnit_iff E _).2 ⟨hb0, hbo⟩
    exact ⟨⟨⟨a, ha⟩, ⟨⟨b, hb⟩, hu⟩⟩, Subtype.ext e⟩
  · have e' : (x : K) = y := congrArg (fun z : E.ring => (z : K)) e
    simp only [OneMemClass.coe_one, one_mul]
    exact Subtype.ext e'

end GlobalTheory.FieldPair.UnramOrd

namespace GlobalTheory.FieldPair.UnramOrd

variable {k K : Type} [Field k] [Field K] {c : k →+* K}

/- English proof (translation)
Rewrite using `[Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_iff]`. Express the relevant statement in the definitionally equal form `¬((y : K) ≠ 0 ∧ E.ord y = 0) ↔ _`. The claim follows by propositional logic.
-/
theorem mem_comap_iff (E : Place c) {T : Subring K} (h : E.Contains T) (y : T) :
    y ∈ (IsLocalRing.maximalIdeal E.ring).comap (incl E h) ↔ (y : K) = 0 ∨ E.ord y ≠ 0 := by
  rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_iff]
  change ¬((y : K) ≠ 0 ∧ E.ord y = 0) ↔ _
  tauto

/- English proof (translation)
Take `⟨x, hxQ, hx0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hQ`. Establish `hx0' : (x : K) ≠ 0` using `fun e => hx0 (Subtype.ext e)`. Introduce `y hy`. Distinguish the cases in `hy0 : (y : K) = 0`. Rewrite using `[show y = 0 from Subtype.ext hy0]`.

Conclude with `Q.zero_mem`. Establish `hy1 : E.ord y ≠ 0` using `((mem_comap_iff E h.1 y).1 hy).resolve_left hy0`. Establish `hyn : 0 ≤ E.ord y` using `(E.ord_nonneg_iff hy0).2 (h.1 _ y.2)`. Establish `hxn : 0 ≤ E.ord x` using `(E.ord_nonneg_iff hx0').2 (h.1 _ x.2)`. Use `set n := (E.ord x).toNat with hn`.

Establish `hnx : (n : ℤ) = E.ord x` using `Int.toNat_of_nonneg hxn`. Establish `hf0 : (y : K) ^ n / x ≠ 0` using `div_ne_zero (pow_ne_zero _ hy0) hx0'`. Establish `hf : (y : K) ^ n / x ∈ E.ring`. Rewrite using `[← E.ord_nonneg_iff hf0, div_eq_mul_inv, E.ord_mul (pow_ne_zero _ hy0) (inv_ne_zero hx0'), E.ord_pow, E.ord_inv, ← hnx]`. Establish `hy2 : 1 ≤ E.ord y` using `by omega`.

Establish `hn0 : (0 : ℤ) ≤ n` using `by positivity`. Use the polynomial consequences of the given equalities and inequalities. Take `⟨a, ha, b, hb, hb0, hbo, e⟩` from `h.2 _ hf`. Establish `e' : y ^ n * ⟨b, hb⟩ = ⟨a, ha⟩ * x`. Apply `Subtype.ext` to reduce the goal to its premises.

Simplify using `only [Subring.coe_mul, SubmonoidClass.coe_pow]`. Rewrite using `[← e]`. Clear the denominators using the available nonvanishing facts. Establish `hbQ : (⟨b, hb⟩ : T) ∉ Q`. Introduce `hbq`.

Break down `(mem_comap_iff E h.1 _).1 (hle hbq) with h' | h'` into its components or cases. Conclude with `hb0 h'`. Conclude with `h' hbo`. Establish `hm : y ^ n * ⟨b, hb⟩ ∈ Q` using `e' ▸ Q.mul_mem_left _ hxQ`. Conclude with `hQp.mem_of_pow_mem n ((hQp.mem_or_mem hm).resolve_right hbQ)`.
-/
theorem le_of_isPrimeOf (E : Place c) {T : Subring K} (h : E.IsPrimeOf T) (Q : Ideal T) [hQp : Q.IsPrime]
    (hQ : Q ≠ ⊥) (hle : Q ≤ (IsLocalRing.maximalIdeal E.ring).comap (incl E h.1)) :
    (IsLocalRing.maximalIdeal E.ring).comap (incl E h.1) ≤ Q := by
  obtain ⟨x, hxQ, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hQ
  have hx0' : (x : K) ≠ 0 := fun e => hx0 (Subtype.ext e)
  intro y hy
  by_cases hy0 : (y : K) = 0
  · rw [show y = 0 from Subtype.ext hy0]; exact Q.zero_mem
  have hy1 : E.ord y ≠ 0 := ((mem_comap_iff E h.1 y).1 hy).resolve_left hy0
  have hyn : 0 ≤ E.ord y := (E.ord_nonneg_iff hy0).2 (h.1 _ y.2)
  have hxn : 0 ≤ E.ord x := (E.ord_nonneg_iff hx0').2 (h.1 _ x.2)
  set n := (E.ord x).toNat with hn
  have hnx : (n : ℤ) = E.ord x := Int.toNat_of_nonneg hxn
  have hf0 : (y : K) ^ n / x ≠ 0 := div_ne_zero (pow_ne_zero _ hy0) hx0'
  have hf : (y : K) ^ n / x ∈ E.ring := by
    rw [← E.ord_nonneg_iff hf0, div_eq_mul_inv, E.ord_mul (pow_ne_zero _ hy0) (inv_ne_zero hx0'),
      E.ord_pow, E.ord_inv, ← hnx]
    have hy2 : 1 ≤ E.ord y := by omega
    have hn0 : (0 : ℤ) ≤ n := by positivity
    nlinarith
  obtain ⟨a, ha, b, hb, hb0, hbo, e⟩ := h.2 _ hf
  have e' : y ^ n * ⟨b, hb⟩ = ⟨a, ha⟩ * x := by
    apply Subtype.ext
    simp only [Subring.coe_mul, SubmonoidClass.coe_pow]
    rw [← e]; field_simp
  have hbQ : (⟨b, hb⟩ : T) ∉ Q := by
    intro hbq
    rcases (mem_comap_iff E h.1 _).1 (hle hbq) with h' | h'
    · exact hb0 h'
    · exact h' hbo
  have hm : y ^ n * ⟨b, hb⟩ ∈ Q := e' ▸ Q.mul_mem_left _ hxQ
  exact hQp.mem_of_pow_mem n ((hQp.mem_or_mem hm).resolve_right hbQ)

end GlobalTheory.FieldPair.UnramOrd

namespace GlobalTheory.FieldPair.UnramOrd

/- English proof (translation)
Introduce `K L _ _ cK cL r R T ι ψ τ P P0 hE hP hP0 hz`. Establish `hinj : Function.Injective ι` using `fun a b e => by`. Use `congrArg ψ e` as an intermediate fact. Rewrite `this` using `[hE.retr, hE.retr]`. Then use the resulting hypothesis. Establish `hιK : ∀ g : R, (g : K) ≠ 0 → ((ι g : T) : L) ≠ 0` using `fun g hg e => hg (by`.

Establish `: ι g = ι 0` using `by rw [map_zero]; exact Subtype.ext e`. Rewrite using `[hinj this]`. Use the proof step `rfl)`. Establish `hz' : ∀ g : R, (g : K) ≠ 0 → (P0.ord (g : K) = 0 ↔ P.ord (ι g : L) = 0)` using `fun g hg => hz g fun e => hg (by rw [e]; rfl)`. Use `letI : Algebra ℂ R := (cK.codRestrict R hE.base.const_mem).toAlgebra`.

Use `haveI : Algebra.EssFiniteType ℂ R := hE.base.essFiniteType`. Use `haveI : IsNoetherianRing R := Algebra.EssFiniteType.isNoetherianRing ℂ R`. Set `A` to `MvPolynomial (Fin r) R`. Set `φ : A →+* T` to `MvPolynomial.eval₂Hom ι τ`. Establish `hφC : ∀ g : R, φ (MvPolynomial.C g) = ι g` using `fun g => MvPolynomial.eval₂Hom_C ι τ g`.

Use `letI : Algebra A T := φ.toAlgebra`. Use `haveI : Algebra.FormallyEtale A T := hE.etale`. Use `haveI : Algebra.EssFiniteType A T := by`. Establish `h1 : (φ.comp (MvPolynomial.C.comp (cK.codRestrict R hE.base.const_mem))).EssFiniteType`. Establish `e : φ.comp (MvPolynomial.C.comp (cK.codRestrict R hE.base.const_mem)) = cL.codRestrict T hE.top.const_mem`.

Use extensionality with `a`. Simplify using `only [RingHom.coe_comp, Function.comp_apply, hφC]`. Conclude with `hE.const a`. Rewrite using `[e]`. Conclude with `hE.top.essFiniteType`.

Conclude with `RingHom.EssFiniteType.of_comp _ h1`. Use `haveI : Module.Flat A T := GlobalTheory.SmoothDescent.flat_of_formallySmooth_of_essFiniteType A T`. Set `j : T →+* P.ring` to `incl P hP.1`. Use `letI : Algebra T P.ring := j.toAlgebra`. Use `letI : Algebra A P.ring := (j.comp φ).toAlgebra`.

Use `haveI : IsScalarTower A T P.ring := IsScalarTower.of_algebraMap_eq' rfl`. Use `haveI := isLocalization P hP`. Use `haveI : Algebra.FormallyUnramified T P.ring := Algebra.FormallyUnramified.of_isLocalization ((IsUnit.submonoid P.ring).comap j)`. Use `haveI : Algebra.FormallyUnramified A P.ring := Algebra.FormallyUnramified.comp A T P.ring`. Use `haveI : Algebra.EssFiniteType T P.ring := Algebra.EssFiniteType.of_isLocalization P.ring ((IsUnit.submonoid P.ring).comap j)`.

Use `haveI : Algebra.EssFiniteType A P.ring := Algebra.EssFiniteType.comp A T P.ring`. Establish `hmax` using `GlobalTheory.T.map_comap_maximalIdeal_eq_of_formallyUnramified' A P.ring`. Set `q : Ideal T` to `(IsLocalRing.maximalIdeal P.ring).comap j`. Set `p : Ideal R` to `(IsLocalRing.maximalIdeal P0.ring).comap (incl P0 hP0.1)`. Use `haveI : q.IsPrime := Ideal.comap_isPrime _ _`.

Use `haveI : p.IsPrime := Ideal.comap_isPrime _ _`. Establish `hpq : ∀ g : R, g ∈ p ↔ ι g ∈ q`. Introduce `g`. Rewrite using `[mem_comap_iff P0 hP0.1, mem_comap_iff P hP.1]`. Distinguish the cases in `hg : (g : K) = 0`.

Establish `: g = 0` using `Subtype.ext hg`. Substitute `this` using the available equality. Simplify using the standard rewrite rules. Simplify using `only [hg, hιK g hg, false_or]`. Conclude with `not_congr (hz' g hg)`.

Take `⟨t, ht⟩` from `IsDiscreteValuationRing.exists_irreducible P0.ring`. Take `⟨π, hπR, b, hbR, hb0, hbo, eπ⟩` from `hP0.2 t t.2`. Establish `ht0 : (t : K) ≠ 0` using `fun e => ht.ne_zero (Subtype.ext e)`. Establish `hπ0 : π ≠ 0` using `by rw [← eπ]; exact mul_ne_zero ht0 hb0`. Establish `hπo : P0.ord π = 1`.

Rewrite using `[← eπ, P0.ord_mul ht0 hb0, hbo, P0.ord_irreducible ht, add_zero]`. Set `π' : R` to `⟨π, hπR⟩`. Establish `hdiv : ∀ g : R, (g : K) ≠ 0 → ∀ k : ℕ, (k : ℤ) ≤ P0.ord g → ∃ a b : R, (b : K) ≠ 0 ∧ P0.ord b = 0 ∧ g * b = a * π' ^ k`. Introduce `g hg k hk`. Establish `hπk : (π : K) ^ k ≠ 0` using `pow_ne_zero _ hπ0`.

Establish `hf0 : (g : K) / π ^ k ≠ 0` using `div_ne_zero hg hπk`. Establish `hf : (g : K) / π ^ k ∈ P0.ring`. Rewrite using `[← P0.ord_nonneg_iff hf0, div_eq_mul_inv, P0.ord_mul hg (inv_ne_zero hπk), P0.ord_inv, P0.ord_pow, hπo]`. Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨a, ha, b, hb, hb0, hbo, e⟩` from `hP0.2 _ hf`.

Use `⟨⟨a, ha⟩, ⟨b, hb⟩, hb0, hbo, Subtype.ext ?_⟩` and prove the remaining obligations. Use `show (g : K) * b = a * π ^ k`. Rewrite using `[← e]`. Clear the denominators using the available nonvanishing facts. Establish `hπp : π' ∈ p` using `(mem_comap_iff P0 hP0.1 π').2 (Or.inr (by rw [show ((π' : R) : K) = π from rfl, hπo]; simp))`.

Establish `hq' : q.comap (algebraMap A T) = Ideal.map (MvPolynomial.C : R →+* A) p`. Establish `hle : Ideal.map (MvPolynomial.C : R →+* A) p ≤ q.comap (algebraMap A T)`. Rewrite using `[Ideal.map_le_iff_le_comap]`. Introduce `g hg`. Rewrite using `[Ideal.mem_comap, Ideal.mem_comap]`.

Express the relevant statement in the definitionally equal form `φ (MvPolynomial.C g) ∈ q`. Rewrite using `[hφC]`. Conclude with `(hpq g).1 hg`. Use `haveI : (q.comap (algebraMap A T)).IsPrime := Ideal.comap_isPrime _ _`. Use `haveI : q.LiesOver (q.comap (algebraMap A T)) := ⟨rfl⟩`.

Use `haveI : (Ideal.map (MvPolynomial.C : R →+* A) p).IsPrime := by`. Rewrite using `[← Ideal.mk_ker (I := p), ← MvPolynomial.ker_map]`. Conclude with `RingHom.ker_isPrime _`. Take `⟨Q, hQq, hQp, hQl⟩` from `Ideal.exists_ideal_le_liesOver_of_le (p := Ideal.map (MvPolynomial.C : R →+* A) p) (q := q.comap (algebraMap A T)) q hle`. Establish `hQ0 : Q ≠ ⊥`.

Introduce `hQ`. Establish `hm : MvPolynomial.C π' ∈ Q.comap (algebraMap A T)`. Rewrite using `[← Ideal.under_def, ← hQl.over]`. Conclude with `Ideal.mem_map_of_mem _ hπp`. Rewrite `hm` using `[hQ, Ideal.mem_comap, Ideal.mem_bot]`.

Express the relevant statement in the definitionally equal form `φ (MvPolynomial.C π') = 0 at hm`. Rewrite `hm` using `[hφC]`. Conclude with `hιK π' hπ0 (by rw [hm]; rfl)`. Establish `hQe` using `le_antisymm hQq (le_of_isPrimeOf P hP Q hQ0 hQq)`. Rewrite using `[← hQe, ← Ideal.under_def]`.

Conclude with `hQl.over.symm`. Establish `hspan : IsLocalRing.maximalIdeal P.ring ≤ Ideal.span {j (ι π')}`. Establish `e1 : (IsLocalRing.maximalIdeal P.ring).comap (algebraMap A P.ring) = q.comap (algebraMap A T)`. Rewrite using `[IsScalarTower.algebraMap_eq A T P.ring, ← Ideal.comap_comap]`. Both sides reduce to the same expression.

Rewrite using `[← hmax, e1, hq', Ideal.map_map, Ideal.map_le_iff_le_comap]`. Introduce `g hg`. Rewrite using `[Ideal.mem_comap]`. Express the relevant statement in the definitionally equal form `j (φ (MvPolynomial.C g)) ∈ _`. Rewrite using `[hφC]`.

Distinguish the cases in `hg0 : (g : K) = 0`. Rewrite using `[show g = 0 from Subtype.ext hg0, map_zero, map_zero]`. Conclude with `Ideal.zero_mem _`. Establish `hk : ((1 : ℕ) : ℤ) ≤ P0.ord g`. Establish `h1` using `((mem_comap_iff P0 hP0.1 g).1 hg).resolve_left hg0`.

Establish `h2` using `(P0.ord_nonneg_iff hg0).2 (hP0.1 _ g.2)`. Use `push_cast`. Use linear arithmetic over natural numbers and integers. Take `⟨a, b, hb0, hbo, e⟩` from `hdiv g hg0 1 hk`. Establish `hu : IsUnit (j (ι b))` using `(isUnit_iff P _).2 ⟨hιK b hb0, (hz' b hb0).1 hbo⟩`.

Establish `e' : j (ι g) * j (ι b) = j (ι a) * j (ι π')`. Rewrite using `[← map_mul, ← map_mul, ← map_mul, ← map_mul, e, pow_one]`. Rewrite using `[Ideal.mem_span_singleton']`. Use `⟨j (ι a) * ↑hu.unit⁻¹, ?_⟩` and prove the remaining obligations. Rewrite using `[mul_right_comm, ← e', mul_assoc, IsUnit.mul_val_inv, mul_one]`.

Establish `hπ1 : P.ord ((ι π' : T) : L) = 1`. Take `⟨s, hs⟩` from `IsDiscreteValuationRing.exists_irreducible P.ring`. Establish `hsm : s ∈ IsLocalRing.maximalIdeal P.ring` using `(IsLocalRing.mem_maximalIdeal _).2 hs.not_isUnit`. Take `⟨c, hc⟩` from `Ideal.mem_span_singleton'.1 (hspan hsm)`. Establish `hs0 : (s : L) ≠ 0` using `fun e => hs.ne_zero (Subtype.ext e)`.

Establish `hc' : (c : L) * ((ι π' : T) : L) = s` using `congrArg Subtype.val hc`. Establish `hc0 : (c : L) ≠ 0` using `fun e => hs0 (by rw [← hc', e, zero_mul])`. Establish `hπ0'` using `hιK π' hπ0`. Establish `h1` using `P.ord_irreducible hs`. Rewrite `h1` using `[← hc', P.ord_mul hc0 hπ0']`.

Establish `h2` using `(P.ord_nonneg_iff hc0).2 c.2`. Establish `h3 : P.ord ((ι π' : T) : L) ≠ 0` using `((mem_comap_iff P hP.1 (ι π')).1 ((hpq π').1 hπp)).resolve_left hπ0'`. Establish `h4` using `(P.ord_nonneg_iff hπ0').2 (hP.1 _ (ι π').2)`. Use linear arithmetic over natural numbers and integers. Introduce `g hg`.

Establish `hg0 : (g : K) ≠ 0` using `fun e => hg (Subtype.ext e)`. Establish `hgn` using `(P0.ord_nonneg_iff hg0).2 (hP0.1 _ g.2)`. Take `⟨a, b, hb0, hbo, e⟩` from `hdiv g hg0 (P0.ord g).toNat (by rw [Int.toNat_of_nonneg hgn])`. Establish `eK : (g : K) * b = a * π ^ (P0.ord g).toNat` using `congrArg Subtype.val e`. Establish `ha0 : (a : K) ≠ 0`.

Introduce `ha`. Rewrite `eK` using `[ha, zero_mul]`. Conclude with `mul_ne_zero hg0 hb0 eK`. Establish `hao : P0.ord a = 0`. Use `congrArg P0.ord eK` as an intermediate fact.

Rewrite `this` using `[P0.ord_mul hg0 hb0, P0.ord_mul ha0 (pow_ne_zero _ hπ0), P0.ord_pow, hπo, hbo, Int.toNat_of_nonneg hgn]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `eL : ((ι g : T) : L) * ((ι b : T) : L) = ((ι a : T) : L) * ((ι π' : T) : L) ^ (P0.ord g).toNat`. Use `congrArg (fun x : R => ((ι x : T) : L)) e` as an intermediate fact. Simplify using `using this`.

Use `congrArg P.ord eL` as an intermediate fact. Rewrite `this` using `[P.ord_mul (hιK g hg0) (hιK b hb0), P.ord_mul (hιK a ha0) (pow_ne_zero _ (hιK π' hπ0)), P.ord_pow, hπ1, (hz' b hb0).1 hbo, (hz' a ha0).1 hao, Int.toNat_of_nonneg hgn]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem ord_eq_of_etTower : ∀ {K L : Type} [Field K] [Field L] (cK : ℂ →+* K) (cL : ℂ →+* L) (r : ℕ)
    (R : Subring K) (T : Subring L)
    (ι : R →+* T) (ψ : T →+* R) (τ : Fin r → T) (P : Place cL) (P0 : Place cK),
  IsEtTower cK R cL T ι ψ τ → P.IsPrimeOf T → P0.IsPrimeOf R →
  (∀ g : R, g ≠ 0 → (P0.ord (g : K) = 0 ↔ P.ord (ι g : L) = 0)) →
  ∀ g : R, g ≠ 0 → P.ord (ι g : L) = P0.ord (g : K) := by
  intro K L _ _ cK cL r R T ι ψ τ P P0 hE hP hP0 hz
  have hinj : Function.Injective ι := fun a b e => by
    have := congrArg ψ e
    rwa [hE.retr, hE.retr] at this
  have hιK : ∀ g : R, (g : K) ≠ 0 → ((ι g : T) : L) ≠ 0 := fun g hg e => hg (by
    have : ι g = ι 0 := by rw [map_zero]; exact Subtype.ext e
    rw [hinj this]; rfl)
  have hz' : ∀ g : R, (g : K) ≠ 0 → (P0.ord (g : K) = 0 ↔ P.ord (ι g : L) = 0) :=
    fun g hg => hz g fun e => hg (by rw [e]; rfl)
  letI : Algebra ℂ R := (cK.codRestrict R hE.base.const_mem).toAlgebra
  haveI : Algebra.EssFiniteType ℂ R := hE.base.essFiniteType
  haveI : IsNoetherianRing R := Algebra.EssFiniteType.isNoetherianRing ℂ R
  let A := MvPolynomial (Fin r) R
  let φ : A →+* T := MvPolynomial.eval₂Hom ι τ
  have hφC : ∀ g : R, φ (MvPolynomial.C g) = ι g := fun g => MvPolynomial.eval₂Hom_C ι τ g
  letI : Algebra A T := φ.toAlgebra
  haveI : Algebra.FormallyEtale A T := hE.etale
  haveI : Algebra.EssFiniteType A T := by
    have h1 : (φ.comp (MvPolynomial.C.comp (cK.codRestrict R hE.base.const_mem))).EssFiniteType := by
      have e : φ.comp (MvPolynomial.C.comp (cK.codRestrict R hE.base.const_mem)) =
          cL.codRestrict T hE.top.const_mem := by
        ext a
        simp only [RingHom.coe_comp, Function.comp_apply, hφC]
        exact hE.const a
      rw [e]; exact hE.top.essFiniteType
    exact RingHom.EssFiniteType.of_comp _ h1
  haveI : Module.Flat A T := GlobalTheory.SmoothDescent.flat_of_formallySmooth_of_essFiniteType A T
  let j : T →+* P.ring := incl P hP.1
  letI : Algebra T P.ring := j.toAlgebra
  letI : Algebra A P.ring := (j.comp φ).toAlgebra
  haveI : IsScalarTower A T P.ring := IsScalarTower.of_algebraMap_eq' rfl
  haveI := isLocalization P hP
  haveI : Algebra.FormallyUnramified T P.ring :=
    Algebra.FormallyUnramified.of_isLocalization ((IsUnit.submonoid P.ring).comap j)
  haveI : Algebra.FormallyUnramified A P.ring := Algebra.FormallyUnramified.comp A T P.ring
  haveI : Algebra.EssFiniteType T P.ring :=
    Algebra.EssFiniteType.of_isLocalization P.ring ((IsUnit.submonoid P.ring).comap j)
  haveI : Algebra.EssFiniteType A P.ring := Algebra.EssFiniteType.comp A T P.ring
  have hmax := GlobalTheory.T.map_comap_maximalIdeal_eq_of_formallyUnramified' A P.ring
  let q : Ideal T := (IsLocalRing.maximalIdeal P.ring).comap j
  let p : Ideal R := (IsLocalRing.maximalIdeal P0.ring).comap (incl P0 hP0.1)
  haveI : q.IsPrime := Ideal.comap_isPrime _ _
  haveI : p.IsPrime := Ideal.comap_isPrime _ _
  have hpq : ∀ g : R, g ∈ p ↔ ι g ∈ q := by
    intro g
    rw [mem_comap_iff P0 hP0.1, mem_comap_iff P hP.1]
    by_cases hg : (g : K) = 0
    · have : g = 0 := Subtype.ext hg
      subst this; simp
    · simp only [hg, hιK g hg, false_or]
      exact not_congr (hz' g hg)

  obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible P0.ring
  obtain ⟨π, hπR, b, hbR, hb0, hbo, eπ⟩ := hP0.2 t t.2
  have ht0 : (t : K) ≠ 0 := fun e => ht.ne_zero (Subtype.ext e)
  have hπ0 : π ≠ 0 := by rw [← eπ]; exact mul_ne_zero ht0 hb0
  have hπo : P0.ord π = 1 := by
    rw [← eπ, P0.ord_mul ht0 hb0, hbo, P0.ord_irreducible ht, add_zero]
  let π' : R := ⟨π, hπR⟩
  have hdiv : ∀ g : R, (g : K) ≠ 0 → ∀ k : ℕ, (k : ℤ) ≤ P0.ord g →
      ∃ a b : R, (b : K) ≠ 0 ∧ P0.ord b = 0 ∧ g * b = a * π' ^ k := by
    intro g hg k hk
    have hπk : (π : K) ^ k ≠ 0 := pow_ne_zero _ hπ0
    have hf0 : (g : K) / π ^ k ≠ 0 := div_ne_zero hg hπk
    have hf : (g : K) / π ^ k ∈ P0.ring := by
      rw [← P0.ord_nonneg_iff hf0, div_eq_mul_inv, P0.ord_mul hg (inv_ne_zero hπk), P0.ord_inv,
        P0.ord_pow, hπo]
      linarith
    obtain ⟨a, ha, b, hb, hb0, hbo, e⟩ := hP0.2 _ hf
    refine ⟨⟨a, ha⟩, ⟨b, hb⟩, hb0, hbo, Subtype.ext ?_⟩
    show (g : K) * b = a * π ^ k
    rw [← e]
    field_simp
  have hπp : π' ∈ p := (mem_comap_iff P0 hP0.1 π').2 (Or.inr (by rw [show ((π' : R) : K) = π from rfl, hπo]; simp))

  have hq' : q.comap (algebraMap A T) = Ideal.map (MvPolynomial.C : R →+* A) p := by
    have hle : Ideal.map (MvPolynomial.C : R →+* A) p ≤ q.comap (algebraMap A T) := by
      rw [Ideal.map_le_iff_le_comap]
      intro g hg
      rw [Ideal.mem_comap, Ideal.mem_comap]
      change φ (MvPolynomial.C g) ∈ q
      rw [hφC]
      exact (hpq g).1 hg
    haveI : (q.comap (algebraMap A T)).IsPrime := Ideal.comap_isPrime _ _
    haveI : q.LiesOver (q.comap (algebraMap A T)) := ⟨rfl⟩
    haveI : (Ideal.map (MvPolynomial.C : R →+* A) p).IsPrime := by
      rw [← Ideal.mk_ker (I := p), ← MvPolynomial.ker_map]
      exact RingHom.ker_isPrime _
    obtain ⟨Q, hQq, hQp, hQl⟩ := Ideal.exists_ideal_le_liesOver_of_le
      (p := Ideal.map (MvPolynomial.C : R →+* A) p) (q := q.comap (algebraMap A T)) q hle
    have hQ0 : Q ≠ ⊥ := by
      intro hQ
      have hm : MvPolynomial.C π' ∈ Q.comap (algebraMap A T) := by
        rw [← Ideal.under_def, ← hQl.over]
        exact Ideal.mem_map_of_mem _ hπp
      rw [hQ, Ideal.mem_comap, Ideal.mem_bot] at hm
      change φ (MvPolynomial.C π') = 0 at hm
      rw [hφC] at hm
      exact hιK π' hπ0 (by rw [hm]; rfl)
    have hQe := le_antisymm hQq (le_of_isPrimeOf P hP Q hQ0 hQq)
    rw [← hQe, ← Ideal.under_def]
    exact hQl.over.symm

  have hspan : IsLocalRing.maximalIdeal P.ring ≤ Ideal.span {j (ι π')} := by
    have e1 : (IsLocalRing.maximalIdeal P.ring).comap (algebraMap A P.ring) =
        q.comap (algebraMap A T) := by
      rw [IsScalarTower.algebraMap_eq A T P.ring, ← Ideal.comap_comap]
      rfl
    rw [← hmax, e1, hq', Ideal.map_map, Ideal.map_le_iff_le_comap]
    intro g hg
    rw [Ideal.mem_comap]
    change j (φ (MvPolynomial.C g)) ∈ _
    rw [hφC]
    by_cases hg0 : (g : K) = 0
    · rw [show g = 0 from Subtype.ext hg0, map_zero, map_zero]
      exact Ideal.zero_mem _
    have hk : ((1 : ℕ) : ℤ) ≤ P0.ord g := by
      have h1 := ((mem_comap_iff P0 hP0.1 g).1 hg).resolve_left hg0
      have h2 := (P0.ord_nonneg_iff hg0).2 (hP0.1 _ g.2)
      push_cast
      omega
    obtain ⟨a, b, hb0, hbo, e⟩ := hdiv g hg0 1 hk
    have hu : IsUnit (j (ι b)) := (isUnit_iff P _).2 ⟨hιK b hb0, (hz' b hb0).1 hbo⟩
    have e' : j (ι g) * j (ι b) = j (ι a) * j (ι π') := by
      rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, e, pow_one]
    rw [Ideal.mem_span_singleton']
    refine ⟨j (ι a) * ↑hu.unit⁻¹, ?_⟩
    rw [mul_right_comm, ← e', mul_assoc, IsUnit.mul_val_inv, mul_one]
  have hπ1 : P.ord ((ι π' : T) : L) = 1 := by
    obtain ⟨s, hs⟩ := IsDiscreteValuationRing.exists_irreducible P.ring
    have hsm : s ∈ IsLocalRing.maximalIdeal P.ring :=
      (IsLocalRing.mem_maximalIdeal _).2 hs.not_isUnit
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (hspan hsm)
    have hs0 : (s : L) ≠ 0 := fun e => hs.ne_zero (Subtype.ext e)
    have hc' : (c : L) * ((ι π' : T) : L) = s := congrArg Subtype.val hc
    have hc0 : (c : L) ≠ 0 := fun e => hs0 (by rw [← hc', e, zero_mul])
    have hπ0' := hιK π' hπ0
    have h1 := P.ord_irreducible hs
    rw [← hc', P.ord_mul hc0 hπ0'] at h1
    have h2 := (P.ord_nonneg_iff hc0).2 c.2
    have h3 : P.ord ((ι π' : T) : L) ≠ 0 :=
      ((mem_comap_iff P hP.1 (ι π')).1 ((hpq π').1 hπp)).resolve_left hπ0'
    have h4 := (P.ord_nonneg_iff hπ0').2 (hP.1 _ (ι π').2)
    omega
  intro g hg
  have hg0 : (g : K) ≠ 0 := fun e => hg (Subtype.ext e)
  have hgn := (P0.ord_nonneg_iff hg0).2 (hP0.1 _ g.2)
  obtain ⟨a, b, hb0, hbo, e⟩ := hdiv g hg0 (P0.ord g).toNat (by rw [Int.toNat_of_nonneg hgn])
  have eK : (g : K) * b = a * π ^ (P0.ord g).toNat := congrArg Subtype.val e
  have ha0 : (a : K) ≠ 0 := by
    intro ha
    rw [ha, zero_mul] at eK
    exact mul_ne_zero hg0 hb0 eK
  have hao : P0.ord a = 0 := by
    have := congrArg P0.ord eK
    rw [P0.ord_mul hg0 hb0, P0.ord_mul ha0 (pow_ne_zero _ hπ0), P0.ord_pow, hπo, hbo,
      Int.toNat_of_nonneg hgn] at this
    linarith
  have eL : ((ι g : T) : L) * ((ι b : T) : L) = ((ι a : T) : L) * ((ι π' : T) : L) ^ (P0.ord g).toNat := by
    have := congrArg (fun x : R => ((ι x : T) : L)) e
    simpa using this
  have := congrArg P.ord eL
  rw [P.ord_mul (hιK g hg0) (hιK b hb0), P.ord_mul (hιK a ha0) (pow_ne_zero _ (hιK π' hπ0)),
    P.ord_pow, hπ1, (hz' b hb0).1 hbo, (hz' a ha0).1 hao, Int.toNat_of_nonneg hgn] at this
  linarith

end GlobalTheory.FieldPair.UnramOrd
