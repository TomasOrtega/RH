import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SiegelAtOfKnownTheorem
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsDedFracLocalizationAway
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.SiegLoc

namespace GlobalTheory.Member

/- English proof (translation)
Introduce `E _ _ _ H l c hgood`. Use `haveI := c.fin`. Use `haveI : NumberField c.F := {}`. Set `n : Option {p // p ∈ l.M.primeFactors} → ℕ` to `fun i => Option.elim i l.M (fun p => l.M / p.1 ^ l.M.factorization p.1)`. Establish `hM0 : l.M ≠ 0` using `by have := l.three_le; omega`.

Establish `hdvd : ∀ i, n i ∣ l.M`. Introduce and unpack `(_ | p)`. Conclude with `dvd_rfl`. Conclude with `Nat.ordCompl_dvd _ _`. Establish `hthree : ∀ i, 3 ≤ n i`.

Introduce and unpack `(_ | p)`. Conclude with `l.three_le`. Conclude with `hgood p.1 (Nat.prime_of_mem_primeFactors p.2)`. Set `a : Option {p // p ∈ l.M.primeFactors} → 𝓞 c.F` to `fun i => (n i : 𝓞 c.F)`. Establish `hne : ∀ i, algebraMap (𝓞 c.F) c.F (a i) ≠ 0`.

Introduce `i`. Simplify using `only [a, map_natCast]`. Conclude with `Nat.cast_ne_zero.mpr (by have := hthree i; omega)`. Establish `hD : IsDedFrac (algebraMap (𝓞 c.F) c.F)`. Use `⟨⟨inferInstance, inferInstance⟩, inferInstance, ?_⟩` and prove the remaining obligations.

Establish `e : (algebraMap (𝓞 c.F) c.F).toAlgebra = (inferInstance : Algebra (𝓞 c.F) c.F)` using `Algebra.algebra_ext _ _ (fun _ => rfl)`. Rewrite using `[e]`. Use `infer_instance`. Establish `hZ : Ideal.span (Set.range (fun i => (n i : ℤ))) = ⊤` using `by set J := Ideal.span (Set.range (fun i => (n i : ℤ)))`. Take `⟨g, hg⟩ : ∃ g : ℤ, J = Ideal.span {g}` from `⟨Submodule.IsPrincipal.generator J, (Submodule.IsPrincipal.span_singleton_generator J).symm⟩`.

Establish `hgd : ∀ i, g.natAbs ∣ n i`. Introduce `i`. Establish `hm : (n i : ℤ) ∈ J` using `Ideal.subset_span ⟨i, rfl⟩`. Rewrite `hm` using `[hg, Ideal.mem_span_singleton]`. Simplify using `using Int.natAbs_dvd_natAbs.mpr hm`.

Establish `h1 : g.natAbs = 1`. Assume the negation of the conclusion as `h`. Establish `hq` using `Nat.minFac_prime h`. Establish `hqM : g.natAbs.minFac ∣ l.M` using `(Nat.minFac_dvd _).trans (hgd none)`. Establish `hmem : g.natAbs.minFac ∈ l.M.primeFactors` using `Nat.mem_primeFactors.mpr ⟨hq, hqM, hM0⟩`.

Conclude with `Nat.not_dvd_ordCompl hq hM0 ((Nat.minFac_dvd _).trans (hgd (some ⟨_, hmem⟩)))`. Rewrite using `[hg, Ideal.span_singleton_eq_top]`. Conclude with `Int.isUnit_iff_natAbs_eq.mpr h1`. Establish `hspan : Ideal.span (Set.range a) = ⊤`. Use `congrArg (Ideal.map (Int.castRingHom (𝓞 c.F))) hZ` as an intermediate fact.

Rewrite `this` using `[Ideal.map_span, Ideal.map_top, ← Set.range_comp]`. Use `this using 3` and compare the differences between its conclusion and the goal. Use extensionality with `i`. Simplify using `[a]`. Establish `hloc : ∀ i, @IsLocalization.Away (𝓞 c.F) _ (a i) (Localization.Away (a i)) _ (algebraMap (𝓞 c.F) (Localization.Away (a i))).toAlgebra`.

Introduce `i`. Establish `e : (algebraMap (𝓞 c.F) (Localization.Away (a i))).toAlgebra = (inferInstance : Algebra (𝓞 c.F) (Localization.Away (a i)))` using `Algebra.algebra_ext _ _ (fun _ => rfl)`. Rewrite using `[e]`. Use `infer_instance`. Establish `hu : ∀ i, IsUnit (algebraMap (𝓞 c.F) c.F (a i))` using `fun i => (hne i).isUnit`.

Use `⟨Option {p // p ∈ l.M.primeFactors}, inferInstance, fun i => Localization.Away (a i), fun i => inferInstance, a, fun i => algebraMap _ _, fun i => IsLocalization.Away.lift (a i) (hu i), n, ⟨hD, fun i => ?_, hspan⟩, fun i => ⟨hthree i, l.odd.of_dvd_nat (hdvd i), hdvd i, rfl⟩⟩` and prove the remaining obligations. Establish `hc : (IsLocalization.Away.lift (S` using `Localization.Away (a i)) (a i) (hu i)).comp (algebraMap (𝓞 c.F) (Localization.Away (a i))) = algebraMap (𝓞 c.F) c.F := IsLocalization.Away.lift_comp _ _`. Conclude with `⟨isDedFrac_away _ _ _ (a i) (hne i) hD _ hc, hc, hloc i⟩`.
-/
theorem exists_cover_of_goodAt_all : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H) (c : Coeff l), (∀ p : ℕ, p.Prime → l.GoodAt p) → ∃ (I : Type) (_ : Finite I) (R : I → Type) (_ : ∀ i, CommRing (R i)) (a : I → 𝓞 c.F) (b : ∀ i, 𝓞 c.F →+* R i) (ω : ∀ i, R i →+* c.F) (n : I → ℕ), IsCover (algebraMap (𝓞 c.F) c.F) R a b ω ∧ ∀ i, 3 ≤ n i ∧ Odd (n i) ∧ n i ∣ l.M ∧ a i = (n i : 𝓞 c.F) := by
  intro E _ _ _ H l c hgood
  haveI := c.fin
  haveI : NumberField c.F := {}
  let n : Option {p // p ∈ l.M.primeFactors} → ℕ := fun i => Option.elim i l.M (fun p => l.M / p.1 ^ l.M.factorization p.1)
  have hM0 : l.M ≠ 0 := by have := l.three_le; omega
  have hdvd : ∀ i, n i ∣ l.M := by
    rintro (_ | p)
    · exact dvd_rfl
    · exact Nat.ordCompl_dvd _ _
  have hthree : ∀ i, 3 ≤ n i := by
    rintro (_ | p)
    · exact l.three_le
    · exact hgood p.1 (Nat.prime_of_mem_primeFactors p.2)
  let a : Option {p // p ∈ l.M.primeFactors} → 𝓞 c.F := fun i => (n i : 𝓞 c.F)
  have hne : ∀ i, algebraMap (𝓞 c.F) c.F (a i) ≠ 0 := by
    intro i
    simp only [a, map_natCast]
    exact Nat.cast_ne_zero.mpr (by have := hthree i; omega)
  have hD : IsDedFrac (algebraMap (𝓞 c.F) c.F) := by
    refine ⟨⟨inferInstance, inferInstance⟩, inferInstance, ?_⟩
    have e : (algebraMap (𝓞 c.F) c.F).toAlgebra = (inferInstance : Algebra (𝓞 c.F) c.F) :=
      Algebra.algebra_ext _ _ (fun _ => rfl)
    rw [e]; infer_instance

  have hZ : Ideal.span (Set.range (fun i => (n i : ℤ))) = ⊤ := by
    set J := Ideal.span (Set.range (fun i => (n i : ℤ)))
    obtain ⟨g, hg⟩ : ∃ g : ℤ, J = Ideal.span {g} :=
      ⟨Submodule.IsPrincipal.generator J, (Submodule.IsPrincipal.span_singleton_generator J).symm⟩
    have hgd : ∀ i, g.natAbs ∣ n i := by
      intro i
      have hm : (n i : ℤ) ∈ J := Ideal.subset_span ⟨i, rfl⟩
      rw [hg, Ideal.mem_span_singleton] at hm
      simpa using Int.natAbs_dvd_natAbs.mpr hm
    have h1 : g.natAbs = 1 := by
      by_contra h
      have hq := Nat.minFac_prime h
      have hqM : g.natAbs.minFac ∣ l.M := (Nat.minFac_dvd _).trans (hgd none)
      have hmem : g.natAbs.minFac ∈ l.M.primeFactors := Nat.mem_primeFactors.mpr ⟨hq, hqM, hM0⟩
      exact Nat.not_dvd_ordCompl hq hM0 ((Nat.minFac_dvd _).trans (hgd (some ⟨_, hmem⟩)))
    rw [hg, Ideal.span_singleton_eq_top]
    exact Int.isUnit_iff_natAbs_eq.mpr h1
  have hspan : Ideal.span (Set.range a) = ⊤ := by
    have := congrArg (Ideal.map (Int.castRingHom (𝓞 c.F))) hZ
    rw [Ideal.map_span, Ideal.map_top, ← Set.range_comp] at this
    convert this using 3
    ext i
    simp [a]
  have hloc : ∀ i, @IsLocalization.Away (𝓞 c.F) _ (a i) (Localization.Away (a i)) _
      (algebraMap (𝓞 c.F) (Localization.Away (a i))).toAlgebra := by
    intro i
    have e : (algebraMap (𝓞 c.F) (Localization.Away (a i))).toAlgebra =
        (inferInstance : Algebra (𝓞 c.F) (Localization.Away (a i))) := Algebra.algebra_ext _ _ (fun _ => rfl)
    rw [e]; infer_instance
  have hu : ∀ i, IsUnit (algebraMap (𝓞 c.F) c.F (a i)) := fun i => (hne i).isUnit
  refine ⟨Option {p // p ∈ l.M.primeFactors}, inferInstance, fun i => Localization.Away (a i), fun i => inferInstance, a,
    fun i => algebraMap _ _, fun i => IsLocalization.Away.lift (a i) (hu i), n, ⟨hD, fun i => ?_, hspan⟩, fun i =>
      ⟨hthree i, l.odd.of_dvd_nat (hdvd i), hdvd i, rfl⟩⟩
  have hc : (IsLocalization.Away.lift (S := Localization.Away (a i)) (a i) (hu i)).comp
      (algebraMap (𝓞 c.F) (Localization.Away (a i))) = algebraMap (𝓞 c.F) c.F :=
    IsLocalization.Away.lift_comp _ _
  exact ⟨isDedFrac_away _ _ _ (a i) (hne i) hD _ hc, hc, hloc i⟩

end GlobalTheory.Member
