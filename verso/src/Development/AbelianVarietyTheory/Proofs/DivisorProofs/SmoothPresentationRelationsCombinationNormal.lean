import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianUnobstructed
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SmoothRel

/- English proof (translation)
Rewrite `hx` using `[pow_two]`. Use `Submodule.mul_induction_on hx (fun y hy z hz => ?_) (fun y z hy hz => ?_)` and prove the remaining obligations. Rewrite using `[Derivation.leibniz, smul_eq_mul, smul_eq_mul]`. Conclude with `I.add_mem (I.mul_mem_right _ hy) (I.mul_mem_right _ hz)`. Rewrite using `[map_add]`.

Conclude with `I.add_mem hy hz`.
-/
theorem derivation_mem_of_mem_sq {R A : Type} [CommRing R] [CommRing A] [Algebra R A]
    (D : Derivation R A A) (I : Ideal A) {x : A} (hx : x ∈ I ^ 2) : D x ∈ I := by
  rw [pow_two] at hx
  refine Submodule.mul_induction_on hx (fun y hy z hz => ?_) (fun y z hy hz => ?_)
  · rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    exact I.add_mem (I.mul_mem_right _ hy) (I.mul_mem_right _ hz)
  · rw [map_add]; exact I.add_mem hy hz

/- English proof (translation)
Proceed by induction on `h using MvPolynomial.induction_on with`. Consider the case `C c => simp`. Consider the case `add p q hp hq`. Use `Ideal.add_mem _ hp hq` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal.

Simplify using `only [map_add, add_mul, Finset.sum_add_distrib]`. Expand and normalize the polynomial expressions, which then agree. Consider the case `mul_X p s hp`. Establish `hD : ∑ i, MvPolynomial.pderiv i p * u i ∈ I` using `Ideal.sum_mem _ fun i _ ↦ I.mul_mem_left _ (hu i)`. Establish `h2 : (∑ i, MvPolynomial.pderiv i p * u i) * u s ∈ I ^ 2`.

Rewrite using `[pow_two]`. Conclude with `Ideal.mul_mem_mul hD (hu s)`. Establish `h3` using `Ideal.add_mem _ h2 ((I ^ 2).mul_mem_left (MvPolynomial.X s + u s) hp)`. Establish `hs : ∑ i, MvPolynomial.pderiv i (p * MvPolynomial.X s) * u i = p * u s + MvPolynomial.X s * ∑ i, MvPolynomial.pderiv i p * u i`. Simplify using `only [Derivation.leibniz, MvPolynomial.pderiv_X, smul_eq_mul, add_mul, Finset.sum_add_distrib, Finset.mul_sum]`.

Use `congr 1`. Simplify using `[Pi.single_apply]`. Conclude with `Finset.sum_congr rfl fun i _ => by ring`. Use `h3 using 1` and compare the differences between its conclusion and the goal. Rewrite using `[map_mul, MvPolynomial.aeval_X, hs]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem taylor_rem_mem {R σ : Type} [CommRing R] [Fintype σ] (I : Ideal (MvPolynomial σ R))
    (u : σ → MvPolynomial σ R) (hu : ∀ i, u i ∈ I) (h : MvPolynomial σ R) :
    MvPolynomial.aeval (fun i ↦ MvPolynomial.X i + u i) h - h
      - ∑ i, MvPolynomial.pderiv i h * u i ∈ I ^ 2 := by
  classical
  induction h using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq =>
    have := Ideal.add_mem _ hp hq
    convert this using 1
    simp only [map_add, add_mul, Finset.sum_add_distrib]; ring
  | mul_X p s hp =>
    have hD : ∑ i, MvPolynomial.pderiv i p * u i ∈ I :=
      Ideal.sum_mem _ fun i _ ↦ I.mul_mem_left _ (hu i)
    have h2 : (∑ i, MvPolynomial.pderiv i p * u i) * u s ∈ I ^ 2 := by
      rw [pow_two]; exact Ideal.mul_mem_mul hD (hu s)
    have h3 := Ideal.add_mem _ h2 ((I ^ 2).mul_mem_left (MvPolynomial.X s + u s) hp)
    have hs : ∑ i, MvPolynomial.pderiv i (p * MvPolynomial.X s) * u i
        = p * u s + MvPolynomial.X s * ∑ i, MvPolynomial.pderiv i p * u i := by
      simp only [Derivation.leibniz, MvPolynomial.pderiv_X, smul_eq_mul, add_mul,
        Finset.sum_add_distrib, Finset.mul_sum]
      congr 1
      · simp [Pi.single_apply]
      · exact Finset.sum_congr rfl fun i _ => by ring
    convert h3 using 1
    rw [map_mul, MvPolynomial.aeval_X, hs]; ring

/- English proof (translation)
Introduce `R₀ _ n r g a b hrel`. Use `set J : Ideal (MvPolynomial (Fin n) R₀) := Ideal.span (Set.range g) with hJ`. Establish `hg : ∀ k, g k ∈ J` using `fun k => Ideal.subset_span ⟨k, rfl⟩`. Establish `hu : ∀ i, (∑ k, a i k * g k) ∈ J` using `fun i => Ideal.sum_mem _ fun k _ => J.mul_mem_left _ (hg k)`. Establish `h1 : ∀ j, g j + ∑ i, MvPolynomial.pderiv i (g j) * ∑ k, a i k * g k ∈ J ^ 2`.

Introduce `j`. Establish `hT` using `taylor_rem_mem J (fun i => ∑ k, a i k * g k) hu (g j)`. Establish `hA : MvPolynomial.aeval (fun i ↦ MvPolynomial.X i + ∑ k, a i k * g k) (g j) ∈ J ^ 2`. Rewrite using `[hrel j]`. Conclude with `Ideal.sum_mem _ fun k _ => Ideal.sum_mem _ fun l _ => (J ^ 2).mul_mem_left _ (by rw [pow_two]; exact Ideal.mul_mem_mul (hg k) (hg l))`.

Use `Ideal.sub_mem _ hA hT` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree. Use `⟨h1, fun j m => ?_⟩` and prove the remaining obligations. Establish `hF` using `derivation_mem_of_mem_sq (MvPolynomial.pderiv m) J (h1 j)`.

Establish `hg0 : ∀ k, Ideal.Quotient.mk J (g k) = 0` using `fun k => Ideal.Quotient.eq_zero_iff_mem.mpr (hg k)`. Rewrite `hF`, the goal using `[← Ideal.Quotient.eq_zero_iff_mem]`. Simplify `hF` using `[Derivation.leibniz, map_sum, map_add, map_mul, hg0, smul_eq_mul, mul_add, Finset.sum_add_distrib]`.
-/
theorem relations_combination :
    ∀ (R₀ : Type) [CommRing R₀] (n r : ℕ) (g : Fin r → MvPolynomial (Fin n) R₀) (a : Fin n → Fin r → MvPolynomial (Fin n) R₀) (b : Fin r → Fin r → Fin r → MvPolynomial (Fin n) R₀), (∀ j, MvPolynomial.aeval (fun i ↦ MvPolynomial.X i + ∑ k, a i k * g k) (g j) = ∑ k, ∑ l, b j k l * (g k * g l)) → (∀ j, g j + ∑ i, MvPolynomial.pderiv i (g j) * ∑ k, a i k * g k ∈ Ideal.span (Set.range g) ^ 2) ∧ ∀ j m, MvPolynomial.pderiv m (g j) + ∑ i, MvPolynomial.pderiv i (g j) * ∑ k, a i k * MvPolynomial.pderiv m (g k) ∈ Ideal.span (Set.range g) := by
  intro R₀ _ n r g a b hrel
  set J : Ideal (MvPolynomial (Fin n) R₀) := Ideal.span (Set.range g) with hJ
  have hg : ∀ k, g k ∈ J := fun k => Ideal.subset_span ⟨k, rfl⟩
  have hu : ∀ i, (∑ k, a i k * g k) ∈ J := fun i =>
    Ideal.sum_mem _ fun k _ => J.mul_mem_left _ (hg k)
  have h1 : ∀ j, g j + ∑ i, MvPolynomial.pderiv i (g j) * ∑ k, a i k * g k ∈ J ^ 2 := by
    intro j
    have hT := taylor_rem_mem J (fun i => ∑ k, a i k * g k) hu (g j)
    have hA : MvPolynomial.aeval (fun i ↦ MvPolynomial.X i + ∑ k, a i k * g k) (g j) ∈ J ^ 2 := by
      rw [hrel j]
      exact Ideal.sum_mem _ fun k _ => Ideal.sum_mem _ fun l _ =>
        (J ^ 2).mul_mem_left _ (by rw [pow_two]; exact Ideal.mul_mem_mul (hg k) (hg l))
    have := Ideal.sub_mem _ hA hT
    convert this using 1
    ring
  refine ⟨h1, fun j m => ?_⟩
  have hF := derivation_mem_of_mem_sq (MvPolynomial.pderiv m) J (h1 j)
  have hg0 : ∀ k, Ideal.Quotient.mk J (g k) = 0 := fun k =>
    Ideal.Quotient.eq_zero_iff_mem.mpr (hg k)
  rw [← Ideal.Quotient.eq_zero_iff_mem] at hF ⊢
  simpa [Derivation.leibniz, map_sum, map_add, map_mul, hg0, smul_eq_mul, mul_add,
    Finset.sum_add_distrib] using hF

end GlobalTheory.SmoothRel
