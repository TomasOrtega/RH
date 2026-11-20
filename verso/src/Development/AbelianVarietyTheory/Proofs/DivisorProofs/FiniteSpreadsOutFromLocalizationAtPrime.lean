import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
open CategoryTheory Limits AlgebraicGeometry
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

/- English proof (translation)
Use `letI : Algebra B (Rm ⊗[R] B) := Algebra.TensorProduct.rightAlgebra`. Use `haveI : IsLocalization (Algebra.algebraMapSubmonoid B M) (Rm ⊗[R] B) := IsLocalization.tensorRight Rm M`. Take `⟨⟨m, hm⟩, h1⟩` from `IsIntegral.exists_multiple_integral_of_isLocalization M _ hb`. Establish `h2 : IsIntegral R (algebraMap B (Rm ⊗[R] B) (m • b))`. Establish `e : algebraMap B (Rm ⊗[R] B) (m • b) = m • ((1 : Rm) ⊗ₜ[R] b)`.

Rewrite using `[← TensorProduct.tmul_smul]`. Both sides reduce to the same expression. Rewrite using `[e]`. Conclude with `h1`. Take `⟨m', hm', h3⟩` from `IsLocalization.exists_isIntegral_smul_of_isIntegral_map (Sₘ := Rm ⊗[R] B) M h2`.

Conclude with `⟨m' * m, M.mul_mem hm' hm, by rwa [mul_smul]⟩`.
-/
theorem exists_smul_isIntegral_of_isIntegral_one_tmul {R : Type} [CommRing R] (M : Submonoid R)
    (Rm : Type) [CommRing Rm] [Algebra R Rm] [IsLocalization M Rm]
    {B : Type} [CommRing B] [Algebra R B] (b : B)
    (hb : IsIntegral Rm ((1 : Rm) ⊗ₜ[R] b)) : ∃ s ∈ M, IsIntegral R (s • b) := by
  letI : Algebra B (Rm ⊗[R] B) := Algebra.TensorProduct.rightAlgebra
  haveI : IsLocalization (Algebra.algebraMapSubmonoid B M) (Rm ⊗[R] B) :=
    IsLocalization.tensorRight Rm M
  obtain ⟨⟨m, hm⟩, h1⟩ := IsIntegral.exists_multiple_integral_of_isLocalization M _ hb
  have h2 : IsIntegral R (algebraMap B (Rm ⊗[R] B) (m • b)) := by
    have e : algebraMap B (Rm ⊗[R] B) (m • b) = m • ((1 : Rm) ⊗ₜ[R] b) := by
      rw [← TensorProduct.tmul_smul]; rfl
    rw [e]; exact h1
  obtain ⟨m', hm', h3⟩ := IsLocalization.exists_isIntegral_smul_of_isIntegral_map
    (Sₘ := Rm ⊗[R] B) M h2
  exact ⟨m' * m, M.mul_mem hm' hm, by rwa [mul_smul]⟩

/- English proof (translation)
Introduce `R _ q B _ _ hft hfin`. Take `⟨S, hS⟩` from `hft.out`. Establish `key : ∀ b : B, ∃ s ∈ q.asIdeal.primeCompl, IsIntegral R (s • b)` using `fun b => exists_smul_isIntegral_of_isIntegral_one_tmul q.asIdeal.primeCompl (Localization.AtPrime q.asIdeal) b (Algebra.IsIntegral.isIntegral _)`. Use `choose s hs hint using key`. Establish `hr : ∏ b ∈ S, s b ∈ q.asIdeal.primeCompl` using `Submonoid.prod_mem _ fun b _ => hs b`.

Use `⟨∏ b ∈ S, s b, hr, ?_⟩` and prove the remaining obligations. Use `set r := ∏ b ∈ S, s b with hrdef`. Set `A` to `Localization.Away r`. Establish `hint' : ∀ b ∈ S, IsIntegral A ((1 : A) ⊗ₜ[R] b)`. Introduce `b hb`.

Establish `hu : IsUnit (algebraMap R A (s b))` using `isUnit_of_dvd_unit (map_dvd _ (Finset.dvd_prod_of_mem s hb)) (IsLocalization.Away.algebraMap_isUnit r)`. Take `⟨u, hu⟩` from `hu`. Establish `h1 : IsIntegral R ((1 : A) ⊗ₜ[R] (s b • b))` using `(hint b).map (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := B))`. Establish `h2 : IsIntegral A ((1 : A) ⊗ₜ[R] (s b • b))` using `h1.tower_top`. Establish `e : (1 : A) ⊗ₜ[R] b = (↑u⁻¹ : A) • ((1 : A) ⊗ₜ[R] (s b • b))`.

Rewrite using `[TensorProduct.tmul_smul, ← algebraMap_smul A (s b), ← hu, smul_smul]`. Simplify using the standard rewrite rules. Rewrite using `[e]`. Conclude with `h2.smul _`. Establish `hall : ∀ b : B, IsIntegral A ((1 : A) ⊗ₜ[R] b)`.

Introduce `b`. Establish `hb : b ∈ Algebra.adjoin R (S : Set B)` using `by rw [hS]; trivial`. Proceed by induction on `hb using Algebra.adjoin_induction with`. Consider the case `mem x hx => exact hint' x hx`. Consider the case `algebraMap x`.

Conclude with `((isIntegral_algebraMap (R := R) (A := B) (x := x)).map (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := B))).tower_top`. Consider the case `add x y _ _ hx hy => rw [TensorProduct.tmul_add]`. Conclude with `hx.add hy`. Consider the case `mul x y _ _ hx hy`. Use `hx.mul hy` as an intermediate fact.

Rewrite `this` using `[Algebra.TensorProduct.tmul_mul_tmul, one_mul]`. Then use the resulting hypothesis. Use `haveI : Algebra.IsIntegral A (A ⊗[R] B) := ⟨fun x => by`. Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => exact isIntegral_zero`. Consider the case `tmul a b`.

Use `(hall b).smul a` as an intermediate fact. Rewrite `this` using `[TensorProduct.smul_tmul', smul_eq_mul, mul_one]`. Then use the resulting hypothesis. Consider the case `add x y hx hy => exact hx.add hy⟩`. Conclude with `Algebra.IsIntegral.finite`.
-/
theorem exists_notMem_finite_away_of_finite_atPrime :
    ∀ (R : Type) [CommRing R] (q : PrimeSpectrum R) (B : Type) [CommRing B] [Algebra R B] [Algebra.FiniteType R B], Module.Finite (Localization.AtPrime q.asIdeal) ((Localization.AtPrime q.asIdeal) ⊗[R] B) → ∃ r : R, r ∉ q.asIdeal ∧ Module.Finite (Localization.Away r) (Localization.Away r ⊗[R] B) := by
  intro R _ q B _ _ hft hfin
  classical
  obtain ⟨S, hS⟩ := hft.out
  have key : ∀ b : B, ∃ s ∈ q.asIdeal.primeCompl, IsIntegral R (s • b) := fun b =>
    exists_smul_isIntegral_of_isIntegral_one_tmul q.asIdeal.primeCompl
      (Localization.AtPrime q.asIdeal) b (Algebra.IsIntegral.isIntegral _)
  choose s hs hint using key
  have hr : ∏ b ∈ S, s b ∈ q.asIdeal.primeCompl := Submonoid.prod_mem _ fun b _ => hs b
  refine ⟨∏ b ∈ S, s b, hr, ?_⟩
  set r := ∏ b ∈ S, s b with hrdef
  let A := Localization.Away r
  have hint' : ∀ b ∈ S, IsIntegral A ((1 : A) ⊗ₜ[R] b) := by
    intro b hb
    have hu : IsUnit (algebraMap R A (s b)) :=
      isUnit_of_dvd_unit (map_dvd _ (Finset.dvd_prod_of_mem s hb))
        (IsLocalization.Away.algebraMap_isUnit r)
    obtain ⟨u, hu⟩ := hu
    have h1 : IsIntegral R ((1 : A) ⊗ₜ[R] (s b • b)) :=
      (hint b).map (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := B))
    have h2 : IsIntegral A ((1 : A) ⊗ₜ[R] (s b • b)) := h1.tower_top
    have e : (1 : A) ⊗ₜ[R] b = (↑u⁻¹ : A) • ((1 : A) ⊗ₜ[R] (s b • b)) := by
      rw [TensorProduct.tmul_smul, ← algebraMap_smul A (s b), ← hu, smul_smul]
      simp
    rw [e]
    exact h2.smul _
  have hall : ∀ b : B, IsIntegral A ((1 : A) ⊗ₜ[R] b) := by
    intro b
    have hb : b ∈ Algebra.adjoin R (S : Set B) := by rw [hS]; trivial
    induction hb using Algebra.adjoin_induction with
    | mem x hx => exact hint' x hx
    | algebraMap x =>
      exact ((isIntegral_algebraMap (R := R) (A := B) (x := x)).map
        (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := B))).tower_top
    | add x y _ _ hx hy => rw [TensorProduct.tmul_add]; exact hx.add hy
    | mul x y _ _ hx hy =>
      have := hx.mul hy
      rwa [Algebra.TensorProduct.tmul_mul_tmul, one_mul] at this
  haveI : Algebra.IsIntegral A (A ⊗[R] B) := ⟨fun x => by
    induction x using TensorProduct.induction_on with
    | zero => exact isIntegral_zero
    | tmul a b =>
      have := (hall b).smul a
      rwa [TensorProduct.smul_tmul', smul_eq_mul, mul_one] at this
    | add x y hx hy => exact hx.add hy⟩
  exact Algebra.IsIntegral.finite

end GlobalTheory
