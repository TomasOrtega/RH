import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTaylorExpansionOrderOne
import Development.AbelianVarietyTheory.Definitions.Divisors.FstTszeSec
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPeriodHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TaylorAddSquareZeroNilpotent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TaylorPolynomialEvalAlgebraFormalProperties
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer GlobalTheory.PeriodFamily
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PeriodFamily

/- English proof (translation)
Introduce `I _ _ g R _ _ J N hJ r`. Proceed by induction on `r with`. Consider the case `zero`. Introduce `m _ _ τ _`. Use `⟨fun j => Fin.elim0 j, fun j => Fin.elim0 j, fun j => Fin.elim0 j, fun a => ?_⟩` and prove the remaining obligations.

Establish `h` using `(taylor_formal_properties N (fun i ↦ ∑ j : Fin 0, m j i)).2.2.2.2.2 (fun z ↦ τ z a)`. Simplify using `only [Finset.univ_eq_empty, Finset.sum_empty] at h ⊢`. Establish `: Set.range (fun _ : I => (0 : R)) ⊆ {0}`. Introduce and unpack `_ ⟨_, rfl⟩`. Both sides reduce to the same expression.

Establish `hb : Ideal.span (Set.range (fun _ : I => (0 : R))) = ⊥`. Rewrite using `[Ideal.span_eq_bot]`. Introduce and unpack `_ ⟨_, rfl⟩`. Both sides reduce to the same expression. Rewrite `h` using `[hb, Ideal.mem_bot]`.

Conclude with `h`. Consider the case `succ r ih`. Introduce `m hmJ hm τ hτ`. Take `⟨n', hn'J, hn', hn'eq⟩` from `ih (fun j => m (Fin.castSucc j)) (fun j i => hmJ _ i) (fun j i i' => hm _ i i') τ hτ`. Use `set t : I → R := fun i => ∑ j : Fin r, m (Fin.castSucc j) i with ht`.

Use `set l : I → R := fun i => m (Fin.last r) i with hl`. Set `v : Fin g → R` to `fun a => ∑ i, taylor N t (fun z ↦ fderiv ℂ (fun z ↦ τ z a) z (Pi.single i 1)) * l i`. Establish `htJ : ∀ i, t i ∈ J` using `fun i => J.sum_mem fun j _ => hmJ _ i`. Establish `hlJ : ∀ i, l i ∈ J` using `fun i => hmJ _ i`. Establish `hspan : Ideal.span (Set.range t ∪ Set.range l) ≤ J`.

Rewrite using `[Ideal.span_le]`. Introduce and unpack `_ (⟨i, rfl⟩ | ⟨i, rfl⟩)`. Conclude with `htJ i`. Conclude with `hlJ i`. Establish `hvJ : ∀ a, v a ∈ J` using `fun a => J.sum_mem fun i _ => J.mul_mem_left _ (hlJ i)`.

Establish `hv : ∀ a b, v a * v b = 0`. Introduce `a b`. Simplify using `only [v, Finset.sum_mul, Finset.mul_sum]`. Use `Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun i' _ => ?_` and prove the remaining obligations. Use `hm (Fin.last r) i' i` as an intermediate fact.

Combine the equalities or inequalities in the displayed calculation. Use `⟨Fin.snoc (α := fun _ => Fin g → R) n' v, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `j a`. Use `Fin.lastCases ?_ (fun j => ?_) j` and prove the remaining obligations. Simplify using `using hvJ a`.

Simplify using `using hn'J j a`. Introduce `j a b`. Use `Fin.lastCases ?_ (fun j => ?_) j` and prove the remaining obligations. Simplify using `using hv a b`. Simplify using `using hn' j a b`.

Introduce `a`. Establish `hfa : AnalyticAt ℂ (fun z ↦ τ z a) 0` using `((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin g => ℂ) a).analyticAt (τ 0)).comp hτ`. Establish `hsum : (fun i ↦ ∑ j : Fin (r + 1), m j i) = fun i => t i + l i`. Use function extensionality and compare the values at `i`. Simplify using `only [ht, hl, Fin.sum_univ_castSucc]`.

Establish `hstep` using `taylor_add_of_mul_eq_zero N t l (fun s hs => hJ s fun a => hspan (hs a)) (fun i j => hm (Fin.last r) i j) _ hfa`. Rewrite using `[hsum, hstep, Fin.sum_univ_castSucc]`. Simplify using `only [Fin.snoc_castSucc, Fin.snoc_last]`. Rewrite using `[← hn'eq a]`. Simplify using `only [v, t]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem taylor_sub_value_eq_sum_sqZero : ∀ {I : Type} [Fintype I] [DecidableEq I] {g : ℕ} {R : Type} [CommRing R] [Algebra ℂ R] (J : Ideal R) (N : ℕ), (∀ s : Fin (N + 1) → R, (∀ a, s a ∈ J) → ∏ a, s a = 0) → ∀ (r : ℕ) (m : Fin r → I → R), (∀ j i, m j i ∈ J) → (∀ j i i', m j i * m j i' = 0) → ∀ τ : (I → ℂ) → Fin g → ℂ, AnalyticAt ℂ τ 0 → ∃ n : Fin r → Fin g → R, (∀ j a, n j a ∈ J) ∧ (∀ j a b, n j a * n j b = 0) ∧ ∀ a, taylor N (fun i ↦ ∑ j, m j i) (fun z ↦ τ z a) - algebraMap ℂ R (τ 0 a) = ∑ j, n j a := by
  intro I _ _ g R _ _ J N hJ r
  induction r with
  | zero =>
    intro m _ _ τ _
    refine ⟨fun j => Fin.elim0 j, fun j => Fin.elim0 j, fun j => Fin.elim0 j, fun a => ?_⟩
    have h := (taylor_formal_properties N (fun i ↦ ∑ j : Fin 0, m j i)).2.2.2.2.2 (fun z ↦ τ z a)
    simp only [Finset.univ_eq_empty, Finset.sum_empty] at h ⊢
    have : Set.range (fun _ : I => (0 : R)) ⊆ {0} := by
      rintro _ ⟨_, rfl⟩; rfl
    have hb : Ideal.span (Set.range (fun _ : I => (0 : R))) = ⊥ := by
      rw [Ideal.span_eq_bot]; rintro _ ⟨_, rfl⟩; rfl
    rw [hb, Ideal.mem_bot] at h
    exact h
  | succ r ih =>
    intro m hmJ hm τ hτ
    obtain ⟨n', hn'J, hn', hn'eq⟩ := ih (fun j => m (Fin.castSucc j)) (fun j i => hmJ _ i)
      (fun j i i' => hm _ i i') τ hτ
    set t : I → R := fun i => ∑ j : Fin r, m (Fin.castSucc j) i with ht
    set l : I → R := fun i => m (Fin.last r) i with hl
    let v : Fin g → R := fun a => ∑ i, taylor N t (fun z ↦ fderiv ℂ (fun z ↦ τ z a) z (Pi.single i 1)) * l i
    have htJ : ∀ i, t i ∈ J := fun i => J.sum_mem fun j _ => hmJ _ i
    have hlJ : ∀ i, l i ∈ J := fun i => hmJ _ i
    have hspan : Ideal.span (Set.range t ∪ Set.range l) ≤ J := by
      rw [Ideal.span_le]
      rintro _ (⟨i, rfl⟩ | ⟨i, rfl⟩)
      · exact htJ i
      · exact hlJ i
    have hvJ : ∀ a, v a ∈ J := fun a => J.sum_mem fun i _ => J.mul_mem_left _ (hlJ i)
    have hv : ∀ a b, v a * v b = 0 := by
      intro a b
      simp only [v, Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun i' _ => ?_
      have := hm (Fin.last r) i' i
      calc _ = (taylor N t (fun z ↦ fderiv ℂ (fun z ↦ τ z b) z (Pi.single i 1)) *
              taylor N t (fun z ↦ fderiv ℂ (fun z ↦ τ z a) z (Pi.single i' 1))) * (l i' * l i) := by ring
        _ = 0 := by simp only [hl, this, mul_zero]
    refine ⟨Fin.snoc (α := fun _ => Fin g → R) n' v, ?_, ?_, ?_⟩
    · intro j a
      refine Fin.lastCases ?_ (fun j => ?_) j
      · simpa using hvJ a
      · simpa using hn'J j a
    · intro j a b
      refine Fin.lastCases ?_ (fun j => ?_) j
      · simpa using hv a b
      · simpa using hn' j a b
    · intro a
      have hfa : AnalyticAt ℂ (fun z ↦ τ z a) 0 :=
        ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin g => ℂ) a).analyticAt (τ 0)).comp hτ
      have hsum : (fun i ↦ ∑ j : Fin (r + 1), m j i) = fun i => t i + l i := by
        funext i; simp only [ht, hl, Fin.sum_univ_castSucc]
      have hstep := taylor_add_of_mul_eq_zero N t l
        (fun s hs => hJ s fun a => hspan (hs a)) (fun i j => hm (Fin.last r) i j) _ hfa
      rw [hsum, hstep, Fin.sum_univ_castSucc]
      simp only [Fin.snoc_castSucc, Fin.snoc_last]
      rw [← hn'eq a]
      simp only [v, t]
      ring

end GlobalTheory.PeriodFamily
