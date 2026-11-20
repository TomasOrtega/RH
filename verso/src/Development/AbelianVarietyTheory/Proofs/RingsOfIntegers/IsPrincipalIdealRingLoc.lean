import Mathlib
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.PlaceInt.LocBasis
open NumberField Module
open scoped nonZeroDivisors

/- English proof (translation)
Use `set M : Submodule A (Fin n → E) := Submodule.span A (L : Set (Fin n → E)) with hM`. Establish `: Submodule.IsLattice E M` using `{ fg := by`. Take `⟨s, hs⟩` from `hfg`. Use `⟨s, ?_⟩` and prove the remaining obligations. Rewrite using `[hM, ← hs, Submodule.span_span_of_tower]`.

Use `span_eq_top := by rw [hM, Submodule.span_span_of_tower, hsp] }`. Establish `hrk : Module.finrank A M = n`. Simplify using `using Submodule.IsLattice.finrank_of_pi E M`. Set `c : Basis (Fin n) A M` to `Module.finBasisOfFinrankEq A M hrk`. Establish `hc : ∀ i, ∃ t : S, (t : O) • (c i : Fin n → E) ∈ L` using `fun i => by`.

Take `⟨t, ht⟩` from `multiple_mem_span_of_mem_localization_span S A (L : Set (Fin n → E)) _ (c i).2`. Rewrite `ht` using `[Submodule.span_eq]`. Conclude with `⟨t, ht⟩`. Use `choose t ht using hc`. Set `u : Fin n → Aˣ` to `fun i => (IsLocalization.map_units A (t i)).unit`.

Set `c' : Basis (Fin n) A M` to `c.unitsSMul u`. Establish `hc' : ∀ i, (c' i : Fin n → E) = (t i : O) • (c i : Fin n → E)` using `fun i => by`. Simplify using `only [c', Basis.unitsSMul_apply, u, Units.smul_def, IsUnit.unit_spec, algebraMap_smul, Submodule.coe_smul_of_tower]`. Set `b : Fin n → Fin n → E` to `fun i => (c' i : Fin n → E)`. Establish `hli : LinearIndependent E b`.

Establish `h : b = c'.extendOfIsLattice E` using `funext fun i => by simp [b]`. Rewrite using `[h]`. Conclude with `(c'.extendOfIsLattice E).linearIndependent`. Establish `hspanA : Submodule.span A (Set.range b) = M`. Establish `: Set.range b = M.subtype '' Set.range c'`.

Rewrite using `[← Set.range_comp]`. Both sides reduce to the same expression. Rewrite using `[this, Submodule.span_image, c'.span_eq, Submodule.map_top, Submodule.range_subtype]`. Establish `hw : ∀ w ∈ L, ∃ r : S, (r : O) • w ∈ Submodule.span O (Set.range b)` using `fun w hw => by`. Take `⟨r, hr⟩` from `multiple_mem_span_of_mem_localization_span S A (Set.range b) w (hspanA ▸ Submodule.subset_span hw)`.

Conclude with `⟨r, hr⟩`. Take `⟨G, hG⟩` from `hfg`. Use `choose! r hr using hw`. Use `⟨∏ x ∈ G, r x, b, hli, fun i => by simpa only [b, hc'] using ht i, fun w hw => ?_⟩` and prove the remaining obligations. Rewrite `hw` using `[← hG]`.

Proceed by induction on `hw using Submodule.span_induction with`. Consider the case `mem y hy`. Establish `hy' : y ∈ G` using `hy`. Rewrite using `[← Finset.prod_erase_mul G r hy', Submonoid.coe_mul, mul_smul]`. Conclude with `Submodule.smul_mem _ _ (hr y (hG ▸ Submodule.subset_span hy))`.

Consider the case `zero => simp`. Consider the case `add y z _ _ hy hz => rw [smul_add]`. Conclude with `Submodule.add_mem _ hy hz`. Consider the case `smul a y _ hy => rw [smul_comm]`. Conclude with `Submodule.smul_mem _ _ hy`.
-/
theorem exists_basis_up_to {O A E : Type} [CommRing O] [CommRing A] [IsDomain A] [Field E] [Algebra O A] [Algebra A E]
    [Algebra O E] [IsScalarTower O A E] (S : Submonoid O) [IsLocalization S A] [IsFractionRing A E]
    [IsPrincipalIdealRing A] {n : ℕ} (L : Submodule O (Fin n → E)) (hfg : L.FG)
    (hsp : Submodule.span E (L : Set (Fin n → E)) = ⊤) :
    ∃ (s : S) (b : Fin n → Fin n → E), LinearIndependent E b ∧ (∀ i, b i ∈ L) ∧
      ∀ w ∈ L, (s : O) • w ∈ Submodule.span O (Set.range b) := by
  classical
  set M : Submodule A (Fin n → E) := Submodule.span A (L : Set (Fin n → E)) with hM
  have : Submodule.IsLattice E M :=
    { fg := by
        obtain ⟨s, hs⟩ := hfg
        refine ⟨s, ?_⟩
        rw [hM, ← hs, Submodule.span_span_of_tower]
      span_eq_top := by rw [hM, Submodule.span_span_of_tower, hsp] }
  have hrk : Module.finrank A M = n := by
    simpa using Submodule.IsLattice.finrank_of_pi E M
  let c : Basis (Fin n) A M := Module.finBasisOfFinrankEq A M hrk
  have hc : ∀ i, ∃ t : S, (t : O) • (c i : Fin n → E) ∈ L := fun i => by
    obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span S A (L : Set (Fin n → E)) _ (c i).2
    rw [Submodule.span_eq] at ht
    exact ⟨t, ht⟩
  choose t ht using hc
  let u : Fin n → Aˣ := fun i => (IsLocalization.map_units A (t i)).unit
  let c' : Basis (Fin n) A M := c.unitsSMul u
  have hc' : ∀ i, (c' i : Fin n → E) = (t i : O) • (c i : Fin n → E) := fun i => by
    simp only [c', Basis.unitsSMul_apply, u, Units.smul_def, IsUnit.unit_spec, algebraMap_smul,
      Submodule.coe_smul_of_tower]
  let b : Fin n → Fin n → E := fun i => (c' i : Fin n → E)
  have hli : LinearIndependent E b := by
    have h : b = c'.extendOfIsLattice E := funext fun i => by simp [b]
    rw [h]
    exact (c'.extendOfIsLattice E).linearIndependent
  have hspanA : Submodule.span A (Set.range b) = M := by
    have : Set.range b = M.subtype '' Set.range c' := by
      rw [← Set.range_comp]; rfl
    rw [this, Submodule.span_image, c'.span_eq, Submodule.map_top, Submodule.range_subtype]
  have hw : ∀ w ∈ L, ∃ r : S, (r : O) • w ∈ Submodule.span O (Set.range b) := fun w hw => by
    obtain ⟨r, hr⟩ := multiple_mem_span_of_mem_localization_span S A (Set.range b) w
      (hspanA ▸ Submodule.subset_span hw)
    exact ⟨r, hr⟩
  obtain ⟨G, hG⟩ := hfg
  choose! r hr using hw
  refine ⟨∏ x ∈ G, r x, b, hli, fun i => by simpa only [b, hc'] using ht i, fun w hw => ?_⟩
  rw [← hG] at hw
  induction hw using Submodule.span_induction with
  | mem y hy =>
    have hy' : y ∈ G := hy
    rw [← Finset.prod_erase_mul G r hy', Submonoid.coe_mul, mul_smul]
    exact Submodule.smul_mem _ _ (hr y (hG ▸ Submodule.subset_span hy))
  | zero => simp
  | add y z _ _ hy hz => rw [smul_add]; exact Submodule.add_mem _ hy hz
  | smul a y _ hy => rw [smul_comm]; exact Submodule.smul_mem _ _ hy

def primeTo (R : Type) [CommRing R] (m : ℕ) : Submonoid R where
  carrier := {x | ∃ k : ℕ, k ≠ 0 ∧ Nat.Coprime k m ∧ x = (k : R)}
  one_mem' := ⟨1, one_ne_zero, Nat.coprime_one_left m, by simp⟩
  mul_mem' := by
    rintro _ _ ⟨a, ha0, ha, rfl⟩ ⟨b, hb0, hb, rfl⟩
    exact ⟨a * b, mul_ne_zero ha0 hb0, Nat.Coprime.mul_left ha hb, by simp⟩

/- English proof (translation)
Proceed by induction on `a using induction_on_primes with`. Consider the case `zero => exact absurd rfl ha`. Consider the case `one => exact absurd ((Ideal.eq_top_iff_one Q).2 (by simpa using h)) hQ.ne_top`. Consider the case `prime_mul p a hp ih`. Rewrite `h` using `[Nat.cast_mul]`.

Break down `hQ.mem_or_mem h with h | h` into its components or cases. Conclude with `⟨p, hp, h⟩`. Conclude with `ih (by rintro rfl; simp at ha) h`.
-/
theorem exists_prime_mem {R : Type} [CommRing R] (Q : Ideal R) (hQ : Q.IsPrime) (a : ℕ) (ha : a ≠ 0)
    (h : (a : R) ∈ Q) : ∃ p : ℕ, p.Prime ∧ (p : R) ∈ Q := by
  induction a using induction_on_primes with
  | zero => exact absurd rfl ha
  | one => exact absurd ((Ideal.eq_top_iff_one Q).2 (by simpa using h)) hQ.ne_top
  | prime_mul p a hp ih =>
    rw [Nat.cast_mul] at h
    rcases hQ.mem_or_mem h with h | h
    · exact ⟨p, hp, h⟩
    · exact ih (by rintro rfl; simp at ha) h

/- English proof (translation)
Establish `: IsDedekindDomain A` using `IsLocalization.isDedekindDomain (𝓞 E) hS A`. Establish `hinj : Function.Injective (algebraMap (𝓞 E) A)` using `IsLocalization.injective A hS`. Establish `hm0 : (m : A) ≠ 0`. Rewrite using `[← map_natCast (algebraMap (𝓞 E) A), map_ne_zero_iff _ hinj]`. Conclude with `hm.ne'` after adjusting the coercions.

Establish `hI : (Ideal.span {(m : A)}) ≠ 0` using `by simpa using hm0`. Apply `IsPrincipalIdealRing.of_finite_primes` to reduce the goal to its premises. Apply `(((Ideal.finite_factors hI).image (fun v => v.asIdeal)).insert ⊥).subset` to reduce the goal to its premises. Introduce `P hP`. Establish `hP' : P.IsPrime` using `hP`.

Distinguish the cases in `hb : P = ⊥`. Conclude with `Or.inl hb`. Use `Or.inr ⟨⟨P, hP', hb⟩, ?_, rfl⟩` and prove the remaining obligations. Use `set Q := P.comap (algebraMap (𝓞 E) A) with hQ`. Establish `hQb : Q ≠ ⊥`.

Introduce `h`. Apply `hb` to reduce the goal to its premises. Rewrite using `[← IsLocalization.map_under (primeTo (𝓞 E) m) A P]`. Express the relevant statement in the definitionally equal form `Q.map _ = ⊥`. Rewrite using `[h, Ideal.map_bot]`.

Establish `h1 : ((Ideal.absNorm Q : ℕ) : A) ∈ P`. Use `Ideal.absNorm_mem Q` as an intermediate fact. Rewrite `this` using `[hQ, Ideal.mem_comap, map_natCast]`. Conclude with `this`. Take `⟨p, hp, hpP⟩` from `exists_prime_mem P hP' _ (by rwa [Ne, Ideal.absNorm_eq_zero_iff]) h1`.

Establish `hpm : p ∣ m`. Assume the negation of the conclusion as `hn`. Establish `hu` using `IsLocalization.map_units A (⟨(p : 𝓞 E), p, hp.ne_zero, (Nat.Prime.coprime_iff_not_dvd hp).2 hn, rfl⟩ : primeTo (𝓞 E) m)`. Simplify using `only [map_natCast] at hu`. Conclude with `hP'.ne_top (Ideal.eq_top_of_isUnit_mem _ hpP hu)`.

Take `⟨c, rfl⟩` from `hpm`. Simplify using `only [Set.mem_setOf_eq, Ideal.dvd_span_singleton, Nat.cast_mul]`. Conclude with `Ideal.mul_mem_right _ _ hpP`.
-/
theorem isPrincipalIdealRing_loc (E : Type) [Field E] [NumberField E] (m : ℕ) (hm : 0 < m)
    (hS : primeTo (𝓞 E) m ≤ (𝓞 E)⁰) (A : Type) [CommRing A] [IsDomain A] [Algebra (𝓞 E) A]
    [IsLocalization (primeTo (𝓞 E) m) A] : IsPrincipalIdealRing A := by
  have : IsDedekindDomain A := IsLocalization.isDedekindDomain (𝓞 E) hS A
  have hinj : Function.Injective (algebraMap (𝓞 E) A) := IsLocalization.injective A hS
  have hm0 : (m : A) ≠ 0 := by
    rw [← map_natCast (algebraMap (𝓞 E) A), map_ne_zero_iff _ hinj]
    exact_mod_cast hm.ne'
  have hI : (Ideal.span {(m : A)}) ≠ 0 := by simpa using hm0
  apply IsPrincipalIdealRing.of_finite_primes
  apply (((Ideal.finite_factors hI).image (fun v => v.asIdeal)).insert ⊥).subset
  intro P hP
  have hP' : P.IsPrime := hP
  by_cases hb : P = ⊥
  · exact Or.inl hb
  refine Or.inr ⟨⟨P, hP', hb⟩, ?_, rfl⟩
  set Q := P.comap (algebraMap (𝓞 E) A) with hQ
  have hQb : Q ≠ ⊥ := by
    intro h
    apply hb
    rw [← IsLocalization.map_under (primeTo (𝓞 E) m) A P]
    change Q.map _ = ⊥
    rw [h, Ideal.map_bot]
  have h1 : ((Ideal.absNorm Q : ℕ) : A) ∈ P := by
    have := Ideal.absNorm_mem Q
    rw [hQ, Ideal.mem_comap, map_natCast] at this
    exact this
  obtain ⟨p, hp, hpP⟩ := exists_prime_mem P hP' _ (by rwa [Ne, Ideal.absNorm_eq_zero_iff]) h1
  have hpm : p ∣ m := by
    by_contra hn
    have hu := IsLocalization.map_units A (⟨(p : 𝓞 E), p, hp.ne_zero, (Nat.Prime.coprime_iff_not_dvd hp).2 hn,
      rfl⟩ : primeTo (𝓞 E) m)
    simp only [map_natCast] at hu
    exact hP'.ne_top (Ideal.eq_top_of_isUnit_mem _ hpP hu)
  obtain ⟨c, rfl⟩ := hpm
  simp only [Set.mem_setOf_eq, Ideal.dvd_span_singleton, Nat.cast_mul]
  exact Ideal.mul_mem_right _ _ hpP

end GlobalTheory.PlaceInt.LocBasis

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
namespace GlobalTheory.PlaceInt.LocBasis

/- English proof (translation)
Introduce `E _ _ n L N hN hle hNL m hm`. Establish `hmem : ∀ v : Fin n → E, v ∈ stdLat E n ↔ ∃ u : Fin n → 𝓞 E, v = fun i => algebraMap (𝓞 E) E (u i)` using `fun v => by`. Simplify using `only [stdLat, Submodule.mem_pi, Set.mem_univ, forall_true_left, Submodule.mem_one]`. Prove the components needed by the constructor for the conclusion. Introduce `h choose u hu using h`.

Conclude with `⟨u, funext fun i => (hu i).symm⟩`. Introduce and unpack `⟨u, rfl⟩ i`. Conclude with `⟨u i, rfl⟩`. Establish `hS : primeTo (𝓞 E) m ≤ nonZeroDivisors (𝓞 E)`. Introduce and unpack `_ ⟨k, hk, -, rfl⟩`.

Conclude with `mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hk)`. Set `A` to `Localization.subalgebra E (primeTo (𝓞 E) m) hS`. Establish `: IsPrincipalIdealRing A` using `isPrincipalIdealRing_loc E m hm hS A`. Establish `hstd : (stdLat E n).FG` using `Submodule.fg_pi fun _ => by`. Rewrite using `[Submodule.one_eq_span]`.

Conclude with `Submodule.fg_span_singleton _`. Establish `hfg : L.FG` using `hstd.of_le hle`. Establish `hN0 : (N : E) ≠ 0` using `by exact_mod_cast hN.ne'`. Establish `hsp : Submodule.span E (L : Set (Fin n → E)) = ⊤`. Rewrite using `[eq_top_iff, ← (Pi.basisFun E (Fin n)).span_eq, Submodule.span_le]`.

Introduce and unpack `_ ⟨i, rfl⟩`. Apply the tactic sequence `have h1 : (Pi.basisFun E (Fin n) i) ∈ stdLat E n := (hmem _).2 ⟨Pi.single i 1, funext fun j => by by_cases h : j = i <;> simp [h, Pi.single_apply]⟩`. Establish `h2` using `hNL (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self (N : 𝓞 E)) h1)`. Establish `h3` using `Submodule.smul_mem (Submodule.span E (L : Set (Fin n → E))) (N : E)⁻¹ (Submodule.subset_span h2)`. Rewrite `h3` using `[← algebraMap_smul E (N : 𝓞 E), smul_smul, map_natCast, inv_mul_cancel₀ hN0, one_smul]`. Then use the resulting hypothesis.

Take `⟨⟨_, k, hk0, hk, rfl⟩, b, hli, hb, hw⟩` from `exists_basis_up_to (A := A) (primeTo (𝓞 E) m) L hfg hsp`. Use `choose u hu using fun j => (hmem (b j)).1 (hle (hb j))`. Set `g : Matrix (Fin n) (Fin n) (𝓞 E)` to `Matrix.of fun i j => u j i`. Establish `hg : ∀ a : Fin n → 𝓞 E, (g.map (algebraMap (𝓞 E) E)).mulVec (fun i => algebraMap (𝓞 E) E (a i)) = ∑ j, a j • b j` using `fun a => by`. Use function extensionality and compare the values at `i`.

Simplify using `only [Matrix.mulVec, dotProduct, g, Matrix.map_apply, Matrix.of_apply, Finset.sum_apply, Pi.smul_apply]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[hu j, Algebra.smul_def, mul_comm]`. Use `⟨k, g, hk, ?_, ?_, ?_⟩` and prove the remaining obligations. Establish `hcol : (g.map (algebraMap (𝓞 E) E)).col = b`.

Use function extensionality and compare the values at `j i`. Rewrite using `[hu j]`. Both sides reduce to the same expression. Establish `hunit : IsUnit (g.map (algebraMap (𝓞 E) E))` using `Matrix.linearIndependent_cols_iff_isUnit.1 (hcol ▸ hli)`. Introduce `h0`.

Use `((Matrix.isUnit_iff_isUnit_det _).1 hunit).ne_zero` as an intermediate fact. Apply `this` to reduce the goal to its premises. Rewrite using `[← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]`. Introduce `v hv`. Take `⟨a, rfl⟩` from `(hmem v).1 hv`.

Rewrite using `[hg]`. Conclude with `Submodule.sum_mem _ fun j _ => L.smul_mem _ (hb j)`. Introduce `w hwL`. Take `⟨a, ha⟩` from `(Submodule.mem_span_range_iff_exists_fun _).1 (hw w hwL)`. Use `⟨_, (hmem _).2 ⟨a, rfl⟩, ?_⟩` and prove the remaining obligations.

Rewrite using `[hg, ha]`. Express the relevant statement in the definitionally equal form `_ = (k : 𝓞 E) • w`. Rewrite using `[Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]`.
-/
theorem exists_matrix_primeTo : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)) (N : ℕ), 0 < N → L ≤ stdLat E n → Ideal.span {(N : 𝓞 E)} • stdLat E n ≤ L → ∀ m : ℕ, 0 < m → ∃ (k₁ : ℕ) (g : Matrix (Fin n) (Fin n) (𝓞 E)), Nat.Coprime k₁ m ∧ g.det ≠ 0 ∧ (∀ v ∈ stdLat E n, (g.map (algebraMap (𝓞 E) E)).mulVec v ∈ L) ∧ ∀ w ∈ L, ∃ v ∈ stdLat E n, (k₁ : E) • w = (g.map (algebraMap (𝓞 E) E)).mulVec v := by
  intro E _ _ n L N hN hle hNL m hm
  classical
  have hmem : ∀ v : Fin n → E, v ∈ stdLat E n ↔ ∃ u : Fin n → 𝓞 E, v = fun i => algebraMap (𝓞 E) E (u i) := fun v => by
    simp only [stdLat, Submodule.mem_pi, Set.mem_univ, forall_true_left, Submodule.mem_one]
    constructor
    · intro h
      choose u hu using h
      exact ⟨u, funext fun i => (hu i).symm⟩
    · rintro ⟨u, rfl⟩ i
      exact ⟨u i, rfl⟩
  have hS : primeTo (𝓞 E) m ≤ nonZeroDivisors (𝓞 E) := by
    rintro _ ⟨k, hk, -, rfl⟩
    exact mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hk)
  let A := Localization.subalgebra E (primeTo (𝓞 E) m) hS
  have : IsPrincipalIdealRing A := isPrincipalIdealRing_loc E m hm hS A
  have hstd : (stdLat E n).FG := Submodule.fg_pi fun _ => by
    rw [Submodule.one_eq_span]; exact Submodule.fg_span_singleton _
  have hfg : L.FG := hstd.of_le hle
  have hN0 : (N : E) ≠ 0 := by exact_mod_cast hN.ne'
  have hsp : Submodule.span E (L : Set (Fin n → E)) = ⊤ := by
    rw [eq_top_iff, ← (Pi.basisFun E (Fin n)).span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have h1 : (Pi.basisFun E (Fin n) i) ∈ stdLat E n :=
      (hmem _).2 ⟨Pi.single i 1, funext fun j => by by_cases h : j = i <;> simp [h, Pi.single_apply]⟩
    have h2 := hNL (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self (N : 𝓞 E)) h1)
    have h3 := Submodule.smul_mem (Submodule.span E (L : Set (Fin n → E))) (N : E)⁻¹ (Submodule.subset_span h2)
    rwa [← algebraMap_smul E (N : 𝓞 E), smul_smul, map_natCast, inv_mul_cancel₀ hN0, one_smul] at h3
  obtain ⟨⟨_, k, hk0, hk, rfl⟩, b, hli, hb, hw⟩ := exists_basis_up_to (A := A) (primeTo (𝓞 E) m) L hfg hsp
  choose u hu using fun j => (hmem (b j)).1 (hle (hb j))
  let g : Matrix (Fin n) (Fin n) (𝓞 E) := Matrix.of fun i j => u j i
  have hg : ∀ a : Fin n → 𝓞 E, (g.map (algebraMap (𝓞 E) E)).mulVec (fun i => algebraMap (𝓞 E) E (a i)) =
      ∑ j, a j • b j := fun a => by
    funext i
    simp only [Matrix.mulVec, dotProduct, g, Matrix.map_apply, Matrix.of_apply, Finset.sum_apply, Pi.smul_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hu j, Algebra.smul_def, mul_comm]
  refine ⟨k, g, hk, ?_, ?_, ?_⟩
  · have hcol : (g.map (algebraMap (𝓞 E) E)).col = b := by
      funext j i
      rw [hu j]; rfl
    have hunit : IsUnit (g.map (algebraMap (𝓞 E) E)) :=
      Matrix.linearIndependent_cols_iff_isUnit.1 (hcol ▸ hli)
    intro h0
    have := ((Matrix.isUnit_iff_isUnit_det _).1 hunit).ne_zero
    apply this
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]
  · intro v hv
    obtain ⟨a, rfl⟩ := (hmem v).1 hv
    rw [hg]
    exact Submodule.sum_mem _ fun j _ => L.smul_mem _ (hb j)
  · intro w hwL
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 (hw w hwL)
    refine ⟨_, (hmem _).2 ⟨a, rfl⟩, ?_⟩
    rw [hg, ha]
    change _ = (k : 𝓞 E) • w
    rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
end GlobalTheory.PlaceInt.LocBasis
