import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExpandsPullOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdFam
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TWMain
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadraticAlgebraValuation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.GenCalc
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.SatLin

/- English proof (translation)
Take `⟨j, hj⟩` from `Function.ne_iff.1 hx`. Establish `: Nonempty Ix` using `⟨j⟩`. Set `f : Ix → ℕ∞` to `fun i => IsDiscreteValuationRing.addVal V (x i)`. Set `i₀` to `Function.argmin f`. Establish `h : ∀ i, x i₀ ∣ x i` using `fun i => IsDiscreteValuationRing.addVal_le_iff_dvd.1 (Function.argmin_le f i)`.

Use `choose u hu using h`. Use `⟨i₀, u, fun h0 => hj ?_, hu⟩` and prove the remaining obligations. Rewrite using `[hu j, h0, zero_mul]`. Both sides reduce to the same expression.
-/
theorem exists_pivot {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {Ix : Type}
    (x : Ix → V) (hx : x ≠ 0) :
    ∃ (i₀ : Ix) (u : Ix → V), x i₀ ≠ 0 ∧ ∀ i, x i = x i₀ * u i := by
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hx
  have : Nonempty Ix := ⟨j⟩
  let f : Ix → ℕ∞ := fun i => IsDiscreteValuationRing.addVal V (x i)
  let i₀ := Function.argmin f
  have h : ∀ i, x i₀ ∣ x i := fun i =>
    IsDiscreteValuationRing.addVal_le_iff_dvd.1 (Function.argmin_le f i)
  choose u hu using h
  refine ⟨i₀, u, fun h0 => hj ?_, hu⟩
  rw [hu j, h0, zero_mul]; rfl

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Introduce `w c _`. Conclude with `⟨0, Fin.elim0, Fin.elim0, Fin.elim0, fun l => l.elim0, fun l => l.elim0, fun i => by simp⟩`. Consider the case `succ n ih`.

Introduce `w c hc`. Distinguish the cases in `h0 : w 0 = 0`. Take `⟨m, c', a, u, h1, h2, h3⟩` from `ih (fun p => w p.succ) (fun p => c p.succ) (fun i => by`. Use `hc i` as an intermediate fact. Rewrite `this` using `[Fin.sum_univ_succ, h0]`.

Simplify using `using this)`. Use `⟨m, c', fun l => Fin.cons 0 (a l), u, h1, fun l i => ?_, fun i => ?_⟩` and prove the remaining obligations. Rewrite using `[Fin.sum_univ_succ, h2]`. Simplify using the standard rewrite rules. Rewrite using `[Fin.sum_univ_succ, h0, ← h3]`.

Simplify using the standard rewrite rules. Take `⟨i₀, u₀, hne, hu⟩` from `exists_pivot (w 0) h0`. Establish `hne' : φ (w 0 i₀) ≠ 0` using `fun h => hne (hφ (by rw [h, map_zero]))`. Establish `key : ∀ i, ∑ p : Fin n, c p.succ * κ (φ (w p.succ i - w p.succ i₀ * u₀ i)) = ∑ p, c p * κ (φ (w p i)) - (∑ p, c p * κ (φ (w p i₀))) * κ (φ (u₀ i))` using `fun i => by`. Rewrite using `[Fin.sum_univ_succ, Fin.sum_univ_succ, hu i, add_mul, Finset.sum_mul]`.

Simplify using `only [map_sub, map_mul, mul_sub, Finset.sum_sub_distrib, _root_.mul_assoc]`. Expand and normalize the polynomial expressions, which then agree. Take `⟨m, c', a, u, h1, h2, h3⟩` from `ih (fun p i => w p.succ i - w p.succ i₀ * u₀ i) (fun p => c p.succ) (fun i => by`. Rewrite using `[key i]`. Use `AddValuation.map_le_sub v (hc i) ?_` and prove the remaining obligations.

Rewrite using `[AddValuation.map_mul]`. Conclude with `add_nonneg (hc i₀) (hv _))`. Use `⟨m + 1, Fin.cons (∑ p, c p * κ (φ (w p i₀))) c', Fin.cons (Fin.cons (φ (w 0 i₀))⁻¹ 0) (fun l => Fin.cons (-(∑ p, a l p * φ (w p.succ i₀)) * (φ (w 0 i₀))⁻¹) (a l)), Fin.cons u₀ u, fun l => ?_, fun l i => ?_, fun i => ?_⟩` and prove the remaining obligations. Use `Fin.cases ?_ (fun l => ?_) l` and prove the remaining obligations. Simplify using `using hc i₀`.

Simplify using `using h1 l`. Use `Fin.cases ?_ (fun l => ?_) l` and prove the remaining obligations. Rewrite using `[Fin.sum_univ_succ, hu i]`. Simplify using `only [Fin.cons_zero, Fin.cons_succ, Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero, map_mul]`. Rewrite using `[inv_mul_cancel_left₀ hne']`.

Rewrite using `[Fin.sum_univ_succ, hu i]`. Simplify using `only [Fin.cons_zero, Fin.cons_succ, map_mul]`. Rewrite using `[h2, _root_.mul_assoc, inv_mul_cancel_left₀ hne', neg_mul, Finset.sum_mul]`. Simplify using `only [map_sub, map_mul, mul_sub, Finset.sum_sub_distrib, _root_.mul_assoc]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[Fin.sum_univ_succ (n := m)]`. Simplify using `only [Fin.cons_zero, Fin.cons_succ]`. Rewrite using `[← h3, key]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem aux {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    {K : Type} [Field K] {F : Type} [Field F] (φ : V →+* K) (hφ : Function.Injective φ) (κ : K →+* F)
    (v : AddValuation F (WithTop ℚ)) (hv : ∀ x : V, (0 : WithTop ℚ) ≤ v (κ (φ x))) {Ix : Type} (n : ℕ) :
    ∀ (w : Fin n → Ix → V) (c : Fin n → F),
      (∀ i, (0 : WithTop ℚ) ≤ v (∑ p, c p * κ (φ (w p i)))) →
      ∃ (m : ℕ) (c' : Fin m → F) (a : Fin m → Fin n → K) (u : Fin m → Ix → V),
        (∀ l, (0 : WithTop ℚ) ≤ v (c' l)) ∧ (∀ l i, φ (u l i) = ∑ p, a l p * φ (w p i)) ∧
        ∀ i, ∑ p, c p * κ (φ (w p i)) = ∑ l, c' l * κ (φ (u l i)) := by
  induction n with
  | zero =>
    intro w c _
    exact ⟨0, Fin.elim0, Fin.elim0, Fin.elim0, fun l => l.elim0, fun l => l.elim0, fun i => by simp⟩
  | succ n ih =>
    intro w c hc
    by_cases h0 : w 0 = 0
    · obtain ⟨m, c', a, u, h1, h2, h3⟩ := ih (fun p => w p.succ) (fun p => c p.succ) (fun i => by
        have := hc i
        rw [Fin.sum_univ_succ, h0] at this
        simpa using this)
      refine ⟨m, c', fun l => Fin.cons 0 (a l), u, h1, fun l i => ?_, fun i => ?_⟩
      · rw [Fin.sum_univ_succ, h2]; simp
      · rw [Fin.sum_univ_succ, h0, ← h3]; simp
    · obtain ⟨i₀, u₀, hne, hu⟩ := exists_pivot (w 0) h0
      have hne' : φ (w 0 i₀) ≠ 0 := fun h => hne (hφ (by rw [h, map_zero]))
      have key : ∀ i, ∑ p : Fin n, c p.succ * κ (φ (w p.succ i - w p.succ i₀ * u₀ i)) =
          ∑ p, c p * κ (φ (w p i)) - (∑ p, c p * κ (φ (w p i₀))) * κ (φ (u₀ i)) := fun i => by
        rw [Fin.sum_univ_succ, Fin.sum_univ_succ, hu i, add_mul, Finset.sum_mul]
        simp only [map_sub, map_mul, mul_sub, Finset.sum_sub_distrib, _root_.mul_assoc]
        ring
      obtain ⟨m, c', a, u, h1, h2, h3⟩ := ih (fun p i => w p.succ i - w p.succ i₀ * u₀ i)
        (fun p => c p.succ) (fun i => by
          rw [key i]
          refine AddValuation.map_le_sub v (hc i) ?_
          rw [AddValuation.map_mul]
          exact add_nonneg (hc i₀) (hv _))
      refine ⟨m + 1, Fin.cons (∑ p, c p * κ (φ (w p i₀))) c',
        Fin.cons (Fin.cons (φ (w 0 i₀))⁻¹ 0)
          (fun l => Fin.cons (-(∑ p, a l p * φ (w p.succ i₀)) * (φ (w 0 i₀))⁻¹) (a l)),
        Fin.cons u₀ u, fun l => ?_, fun l i => ?_, fun i => ?_⟩
      · refine Fin.cases ?_ (fun l => ?_) l
        · simpa using hc i₀
        · simpa using h1 l
      · refine Fin.cases ?_ (fun l => ?_) l
        · rw [Fin.sum_univ_succ, hu i]
          simp only [Fin.cons_zero, Fin.cons_succ, Pi.zero_apply, zero_mul, Finset.sum_const_zero,
            add_zero, map_mul]
          rw [inv_mul_cancel_left₀ hne']
        · rw [Fin.sum_univ_succ, hu i]
          simp only [Fin.cons_zero, Fin.cons_succ, map_mul]
          rw [h2, _root_.mul_assoc, inv_mul_cancel_left₀ hne', neg_mul, Finset.sum_mul]
          simp only [map_sub, map_mul, mul_sub, Finset.sum_sub_distrib, _root_.mul_assoc]
          ring
      · rw [Fin.sum_univ_succ (n := m)]
        simp only [Fin.cons_zero, Fin.cons_succ]
        rw [← h3, key]
        ring

/- English proof (translation)
Introduce `V _ _ _ ϖ hϖ F _ _ v hv Ix n w c hc`. Conclude with `aux (algebraMap V (FractionRing V)) (IsFractionRing.injective V _) (algebraMap (FractionRing V) F) v (GC.v_alg_nonneg hϖ hv) n w c hc`.
-/
theorem main : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ → ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v → ∀ (Ix : Type) (n : ℕ) (w : Fin n → Ix → V) (c : Fin n → F), (∀ i, (0 : WithTop ℚ) ≤ v (∑ p, c p * algebraMap (FractionRing V) F (algebraMap V (FractionRing V) (w p i)))) → ∃ (m : ℕ) (c' : Fin m → F) (a : Fin m → Fin n → (FractionRing V)) (u : Fin m → Ix → V), (∀ l, (0 : WithTop ℚ) ≤ v (c' l)) ∧ (∀ l i, algebraMap V (FractionRing V) (u l i) = ∑ p, a l p * algebraMap V (FractionRing V) (w p i)) ∧ ∀ i, ∑ p, c p * algebraMap (FractionRing V) F (algebraMap V (FractionRing V) (w p i)) = ∑ l, c' l * algebraMap (FractionRing V) F (algebraMap V (FractionRing V) (u l i)) := by
  intro V _ _ _ ϖ hϖ F _ _ v hv Ix n w c hc
  exact aux (algebraMap V (FractionRing V)) (IsFractionRing.injective V _)
    (algebraMap (FractionRing V) F) v (GC.v_alg_nonneg hϖ hv) n w c hc

end GlobalTheory.SatLin
