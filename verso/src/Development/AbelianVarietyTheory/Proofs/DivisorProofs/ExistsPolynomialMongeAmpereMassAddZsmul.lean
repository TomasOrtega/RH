import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ChernDegreeComplex
import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

namespace GlobalTheory.MongeAmperePoly

variable {X : Type} [TopologicalSpace X]

/- English proof (translation)
Use function extensionality and compare the values at `k`. Use `Fin.cases ?_ (fun k => ?_) k` and prove the remaining obligations. Simplify using the standard rewrite rules. Establish `h : Equiv.swap 0 i k.succ ≠ i`. Introduce `h`.

Establish `h2 : Equiv.swap 0 i k.succ = Equiv.swap 0 i 0` using `by rw [h, Equiv.swap_apply_left]`. Conclude with `Fin.succ_ne_zero k ((Equiv.swap 0 i).injective h2)`. Simplify using `[Function.update_of_ne h]`.
-/
theorem update_comp_swap {e : ℕ} (Φ : Fin (e + 1) → LocPot X) (i : Fin (e + 1)) (P : LocPot X) :
    Function.update Φ i P ∘ Equiv.swap 0 i =
      (Fin.cons P (fun k => Φ (Equiv.swap 0 i k.succ)) : Fin (e + 1) → LocPot X) := by
  funext k
  refine Fin.cases ?_ (fun k => ?_) k
  · simp
  · have h : Equiv.swap 0 i k.succ ≠ i := by
      intro h
      have h2 : Equiv.swap 0 i k.succ = Equiv.swap 0 i 0 := by rw [h, Equiv.swap_apply_left]
      exact Fin.succ_ne_zero k ((Equiv.swap 0 i).injective h2)
    simp [Function.update_of_ne h]

/- English proof (translation)
Consider the cases of `e with`. Consider the case `zero => exact i.elim0`. Consider the case `succ e`. Establish `key : ∀ R : LocPot X, mInt A (Function.update Φ i R) (fun _ => 1) = mInt A (Fin.cons R (fun k => Φ (Equiv.swap 0 i k.succ))) (fun _ => 1)`. Introduce `R`.

Rewrite using `[← update_comp_swap, mIntSymm]`. Establish `hT : ∀ k : Fin e, IsPotential A (Φ (Equiv.swap 0 i k.succ))` using `fun k => hΦ _`. Establish `hI : ∀ R : LocPot X, IsPotential A R → MIntegrable A (Fin.cons R (fun k => Φ (Equiv.swap 0 i k.succ))) (fun _ => 1)`. Introduce `R hR`. Use `mIntegrableCont A _ (fun k => ?_) _ continuous_const` and prove the remaining obligations.

Use `Fin.cases ?_ (fun k => ?_) k` and prove the remaining obligations. Simplify using `using hR`. Simplify using `using hT k`. Establish `hQm` using `isPotentialZsmul A m Q hQ`. Rewrite using `[key, key, key, mIntAdd A P _ _ hP hQm hT _ (hI _ hP) (hI _ hQm), mIntZsmul A m Q _ hQ hT]`.
-/
theorem mInt_update_add_zsmul [CompactSpace X] [T2Space X] {e : ℕ} (A : FinHolAtlas e X)
    (Φ : Fin e → LocPot X) (hΦ : ∀ i, IsPotential A (Φ i)) (i : Fin e) (P Q : LocPot X)
    (hP : IsPotential A P) (hQ : IsPotential A Q) (m : ℤ) :
    mInt A (Function.update Φ i (P + Q.zsmul m)) (fun _ => 1) =
      mInt A (Function.update Φ i P) (fun _ => 1) +
        m * mInt A (Function.update Φ i Q) (fun _ => 1) := by
  cases e with
  | zero => exact i.elim0
  | succ e =>
    have key : ∀ R : LocPot X, mInt A (Function.update Φ i R) (fun _ => 1) =
        mInt A (Fin.cons R (fun k => Φ (Equiv.swap 0 i k.succ))) (fun _ => 1) := by
      intro R
      rw [← update_comp_swap, mIntSymm]
    have hT : ∀ k : Fin e, IsPotential A (Φ (Equiv.swap 0 i k.succ)) := fun k => hΦ _
    have hI : ∀ R : LocPot X, IsPotential A R →
        MIntegrable A (Fin.cons R (fun k => Φ (Equiv.swap 0 i k.succ))) (fun _ => 1) := by
      intro R hR
      refine mIntegrableCont A _ (fun k => ?_) _ continuous_const
      refine Fin.cases ?_ (fun k => ?_) k
      · simpa using hR
      · simpa using hT k
    have hQm := isPotentialZsmul A m Q hQ
    rw [key, key, key, mIntAdd A P _ _ hP hQm hT _ (hI _ hP) (hI _ hQm),
      mIntZsmul A m Q _ hQ hT]

/- English proof (translation)
Proceed by induction on `S using Finset.induction_on with`. Consider the case `empty`. Introduce `Φ _`. Conclude with `⟨Polynomial.C (mInt A Φ (fun _ => 1)), fun m => by simp⟩`. Consider the case `insert a S ha ih`.

Introduce `Φ hΦ`. Establish `hΦ' : ∀ i, IsPotential A (Function.update Φ a (Ψ a) i)`. Introduce `i`. Distinguish the cases in `h : i = a`. Substitute `h` using the available equality.

Simplify using `using hΨ i`. Simplify `hΦ i` using `[Function.update_of_ne h]`. Take `⟨P₁, h₁⟩` from `ih Φ hΦ`. Take `⟨P₂, h₂⟩` from `ih _ hΦ'`. Use `⟨P₁ + Polynomial.X * P₂, fun m => ?_⟩` and prove the remaining obligations.

Use `set F : Fin e → LocPot X := fun i => if i ∈ S then Φ i + (Ψ i).zsmul m else Φ i with hF`. Establish `hFp : ∀ i, IsPotential A (F i)`. Introduce `i`. Distinguish the cases in `h : i ∈ S`. Simplify `isPotentialAdd A _ _ (hΦ i) (isPotentialZsmul A m _ (hΨ i))` using `[hF, h]`.

Simplify `hΦ i` using `[hF, h]`. Establish `e0 : (fun i => if i ∈ insert a S then Φ i + (Ψ i).zsmul m else Φ i) = Function.update F a (Φ a + (Ψ a).zsmul m)`. Use function extensionality and compare the values at `i`. Distinguish the cases in `h : i = a`. Substitute `h` using the available equality.

Simplify using the standard rewrite rules. Simplify using `[hF, Function.update_of_ne h, h]`. Establish `e1 : Function.update F a (Φ a) = F`. Use function extensionality and compare the values at `i`. Distinguish the cases in `h : i = a`.

Substitute `h` using the available equality. Simplify using `[hF, ha]`. Simplify using `[Function.update_of_ne h]`. Establish `e2 : Function.update F a (Ψ a) = fun i => if i ∈ S then Function.update Φ a (Ψ a) i + (Ψ i).zsmul m else Function.update Φ a (Ψ a) i`. Use function extensionality and compare the values at `i`.

Distinguish the cases in `h : i = a`. Substitute `h` using the available equality. Simplify using `[ha]`. Simplify using `[hF, Function.update_of_ne h]`. Rewrite using `[e0, mInt_update_add_zsmul A F hFp a _ _ (hΦ a) (hΨ a), e1, e2, h₂ m]`.

Use `h₁ m` as an intermediate fact. Simplify using `only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X]`. Rewrite using `[← this]`.
-/
theorem exists_poly_finset [CompactSpace X] [T2Space X] {e : ℕ} (A : FinHolAtlas e X)
    (Ψ : Fin e → LocPot X) (hΨ : ∀ i, IsPotential A (Ψ i)) (S : Finset (Fin e)) :
    ∀ Φ : Fin e → LocPot X, (∀ i, IsPotential A (Φ i)) → ∃ P : Polynomial ℝ, ∀ m : ℤ,
      mInt A (fun i => if i ∈ S then Φ i + (Ψ i).zsmul m else Φ i) (fun _ => 1) =
        P.eval (m : ℝ) := by
  induction S using Finset.induction_on with
  | empty =>
    intro Φ _
    exact ⟨Polynomial.C (mInt A Φ (fun _ => 1)), fun m => by simp⟩
  | insert a S ha ih =>
    intro Φ hΦ
    have hΦ' : ∀ i, IsPotential A (Function.update Φ a (Ψ a) i) := by
      intro i
      by_cases h : i = a
      · subst h; simpa using hΨ i
      · simpa [Function.update_of_ne h] using hΦ i
    obtain ⟨P₁, h₁⟩ := ih Φ hΦ
    obtain ⟨P₂, h₂⟩ := ih _ hΦ'
    refine ⟨P₁ + Polynomial.X * P₂, fun m => ?_⟩
    set F : Fin e → LocPot X := fun i => if i ∈ S then Φ i + (Ψ i).zsmul m else Φ i with hF
    have hFp : ∀ i, IsPotential A (F i) := by
      intro i
      by_cases h : i ∈ S
      · simpa [hF, h] using isPotentialAdd A _ _ (hΦ i) (isPotentialZsmul A m _ (hΨ i))
      · simpa [hF, h] using hΦ i
    have e0 : (fun i => if i ∈ insert a S then Φ i + (Ψ i).zsmul m else Φ i) =
        Function.update F a (Φ a + (Ψ a).zsmul m) := by
      funext i
      by_cases h : i = a
      · subst h; simp
      · simp [hF, Function.update_of_ne h, h]
    have e1 : Function.update F a (Φ a) = F := by
      funext i
      by_cases h : i = a
      · subst h; simp [hF, ha]
      · simp [Function.update_of_ne h]
    have e2 : Function.update F a (Ψ a) = fun i => if i ∈ S then
        Function.update Φ a (Ψ a) i + (Ψ i).zsmul m else Function.update Φ a (Ψ a) i := by
      funext i
      by_cases h : i = a
      · subst h; simp [ha]
      · simp [hF, Function.update_of_ne h]
    rw [e0, mInt_update_add_zsmul A F hFp a _ _ (hΦ a) (hΨ a), e1, e2, h₂ m]
    have := h₁ m
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X]
    rw [← this]

/- English proof (translation)
Introduce `e X _ _ _ A Φ Ψ hΦ hΨ`. Take `⟨P, hP⟩` from `exists_poly_finset A Ψ hΨ Finset.univ Φ hΦ`. Conclude with `⟨P, fun m => by simpa using hP m⟩`.
-/
theorem mInt_add_zsmul_poly : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X]
    [T2Space X] (A : FinHolAtlas e X) (Φ Ψ : Fin e → LocPot X), (∀ i, IsPotential A (Φ i)) →
    (∀ i, IsPotential A (Ψ i)) → ∃ P : Polynomial ℝ, ∀ m : ℤ,
      mInt A (fun i => Φ i + (Ψ i).zsmul m) (fun _ => 1) = P.eval (m : ℝ) := by
  intro e X _ _ _ A Φ Ψ hΦ hΨ
  obtain ⟨P, hP⟩ := exists_poly_finset A Ψ hΨ Finset.univ Φ hΦ
  exact ⟨P, fun m => by simpa using hP m⟩

end GlobalTheory.MongeAmperePoly
