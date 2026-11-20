import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsUnitEv
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS

/- English proof (translation)
Set `s : (J → F) → Finset J` to `fun u => A.filter (fun i => u i ≠ 0)`. Establish `hex : ∃ n, ∃ u, M u ∧ L u ≠ 0 ∧ (s u).card = n` using `⟨_, v, hv, hLv, rfl⟩`. Take `⟨v', hMv', hLv', hcard⟩` from `Nat.find_spec hex`. Use `⟨v', hMv', hLv', ?_⟩` and prove the remaining obligations. Establish `hmin : ∀ u, M u → L u ≠ 0 → s u ⊆ s v' → s u ≠ s v' → False`.

Introduce `u hMu hLu hsub hne`. Establish `hlt : (s u).card < (s v').card` using `Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩)`. Rewrite `hlt` using `[hcard]`. Conclude with `Nat.find_min hex hlt ⟨u, hMu, hLu, rfl⟩`. Introduce `w hMw hsupp i₀ hi₀ hv'i₀ hwi₀ j hj`.

Assume the negation of the conclusion as `hwj`. Establish `hv'j : v' j ≠ 0` using `fun h => hwj (hsupp j hj h)`. Distinguish the cases in `hLw : L w = 0`. Establish `hMu : M (fun i => v' i - v' j / w j * w i)` using `hM v' w _ hMv' hMw`. Establish `hLu : L (fun i => v' i - v' j / w j * w i) ≠ 0`.

Rewrite using `[hL v' w, hLw, mul_zero, sub_zero]`. Conclude with `hLv'`. Apply `hmin _ hMu hLu` to reduce the goal to its premises. Introduce `i hi`. Simplify using `only [s, Finset.mem_filter] at hi ⊢`.

Use `⟨hi.1, fun h => hi.2 ?_⟩` and prove the remaining obligations. Rewrite using `[h, hsupp i hi.1 h, mul_zero, sub_zero]`. Introduce `heq`. Establish `hjs : j ∈ s v'` using `by simp [s, hj, hv'j]`. Rewrite `hjs` using `[← heq]`.

Simplify using `only [s, Finset.mem_filter] at hjs`. Conclude with `hjs.2 (by rw [div_mul_cancel₀ _ hwj, sub_self])`. Apply `hmin w hMw hLw` to reduce the goal to its premises. Introduce `i hi`. Simplify using `only [s, Finset.mem_filter] at hi ⊢`.

Conclude with `⟨hi.1, fun h => hi.2 (hsupp i hi.1 h)⟩`. Introduce `heq`. Establish `hi₀s : i₀ ∈ s v'` using `by simp [s, hi₀, hv'i₀]`. Rewrite `hi₀s` using `[← heq]`. Simplify using `[s, hwi₀] at hi₀s`.
-/
theorem exists_minimal_support {F J : Type} [Field F] (A : Finset J) (M : (J → F) → Prop)
    (L : (J → F) → F) (hM : ∀ v w (a : F), M v → M w → M (fun i => v i - a * w i))
    (hL : ∀ v w (a : F), L (fun i => v i - a * w i) = L v - a * L w)
    (v : J → F) (hv : M v) (hLv : L v ≠ 0) :
    ∃ v', M v' ∧ L v' ≠ 0 ∧ ∀ w, M w → (∀ i ∈ A, v' i = 0 → w i = 0) →
      ∀ i₀ ∈ A, v' i₀ ≠ 0 → w i₀ = 0 → ∀ i ∈ A, w i = 0 := by
  classical
  let s : (J → F) → Finset J := fun u => A.filter (fun i => u i ≠ 0)
  have hex : ∃ n, ∃ u, M u ∧ L u ≠ 0 ∧ (s u).card = n := ⟨_, v, hv, hLv, rfl⟩
  obtain ⟨v', hMv', hLv', hcard⟩ := Nat.find_spec hex
  refine ⟨v', hMv', hLv', ?_⟩
  have hmin : ∀ u, M u → L u ≠ 0 → s u ⊆ s v' → s u ≠ s v' → False := by
    intro u hMu hLu hsub hne
    have hlt : (s u).card < (s v').card :=
      Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩)
    rw [hcard] at hlt
    exact Nat.find_min hex hlt ⟨u, hMu, hLu, rfl⟩
  intro w hMw hsupp i₀ hi₀ hv'i₀ hwi₀ j hj
  by_contra hwj
  have hv'j : v' j ≠ 0 := fun h => hwj (hsupp j hj h)
  by_cases hLw : L w = 0
  · have hMu : M (fun i => v' i - v' j / w j * w i) := hM v' w _ hMv' hMw
    have hLu : L (fun i => v' i - v' j / w j * w i) ≠ 0 := by
      rw [hL v' w, hLw, mul_zero, sub_zero]
      exact hLv'
    apply hmin _ hMu hLu
    · intro i hi
      simp only [s, Finset.mem_filter] at hi ⊢
      refine ⟨hi.1, fun h => hi.2 ?_⟩
      rw [h, hsupp i hi.1 h, mul_zero, sub_zero]
    · intro heq
      have hjs : j ∈ s v' := by simp [s, hj, hv'j]
      rw [← heq] at hjs
      simp only [s, Finset.mem_filter] at hjs
      exact hjs.2 (by rw [div_mul_cancel₀ _ hwj, sub_self])
  · apply hmin w hMw hLw
    · intro i hi
      simp only [s, Finset.mem_filter] at hi ⊢
      exact ⟨hi.1, fun h => hi.2 (hsupp i hi.1 h)⟩
    · intro heq
      have hi₀s : i₀ ∈ s v' := by simp [s, hi₀, hv'i₀]
      rw [← heq] at hi₀s
      simp [s, hwi₀] at hi₀s

/- English proof (translation)
Introduce `F T X _ _ c σ φ S p q hmul hone hσc hσφ hrel hsum`. Establish `hcinv : ∀ t χ, c t χ * c t⁻¹ χ = 1`. Introduce `t χ`. Rewrite using `[← hmul, mul_inv_cancel, hone]`. Take `⟨v', hMv', hLv', hmin⟩` from `exists_minimal_support (S.disjSum S) (fun v : X ⊕ X → F => ∀ t, φ t * ∑ χ ∈ S, c t χ * v (Sum.inl χ) = ∑ χ ∈ S, c t χ * v (Sum.inr χ)) (fun v => ∑ χ ∈ S, v (Sum.inl χ)) (by`.

Introduce `v w a hv hw t`. Establish `e1 : ∀ g h : X → F, ∑ χ ∈ S, c t χ * (g χ - a * h χ) = ∑ χ ∈ S, c t χ * g χ - a * ∑ χ ∈ S, c t χ * h χ`. Introduce `g h`. Rewrite using `[Finset.mul_sum, ← Finset.sum_sub_distrib]`. Conclude with `Finset.sum_congr rfl fun χ _ => by ring`.

Rewrite using `[e1 (fun χ => v (Sum.inl χ)) (fun χ => w (Sum.inl χ)), e1 (fun χ => v (Sum.inr χ)) (fun χ => w (Sum.inr χ))]`. Take the linear combination `hv t - a * hw t)`. Use the proof step `(by`. Introduce `v w a`. Rewrite using `[Finset.sum_sub_distrib, Finset.mul_sum])`.

Use the proof step `(Sum.elim p q) (fun t => hrel t) hsum`. Take `⟨χ₀, hχ₀S, hr⟩` from `Finset.exists_ne_zero_of_sum_ne_zero hLv'`. Use `set r := v' (Sum.inl χ₀) with hrdef`. Establish `htw : ∀ t, ∀ t', φ t' * ∑ χ ∈ S, c t' χ * (c t⁻¹ χ * σ t (v' (Sum.inl χ))) = ∑ χ ∈ S, c t' χ * (c t⁻¹ χ * σ t (v' (Sum.inr χ)))`. Introduce `t t'`.

Establish `h` using `congrArg (σ t) (hMv' (t' * t⁻¹))`. Simplify using `only [map_mul, map_sum, hσc, hσφ, inv_mul_cancel_right, hmul] at h`. Establish `e : ∀ g : X → F, ∑ χ ∈ S, c t' χ * (c t⁻¹ χ * g χ) = ∑ χ ∈ S, c t' χ * c t⁻¹ χ * g χ` using `fun g => Finset.sum_congr rfl fun χ _ => (mul_assoc _ _ _).symm`. Rewrite using `[e (fun χ => σ t (v' (Sum.inl χ))), e (fun χ => σ t (v' (Sum.inr χ)))]`. Conclude with `h`.

Establish `hfin : ∀ t, ∀ i ∈ S.disjSum S, σ t (r⁻¹ * v' i) * c t χ₀ = c t (Sum.elim id id i) * (r⁻¹ * v' i)`. Introduce `t i hi`. Establish `hsr : σ t r ≠ 0` using `(map_ne_zero (σ t)).mpr hr`. Establish `hz` using `hmin (fun j => c t⁻¹ (Sum.elim id id j) * σ t (v' j) - c t⁻¹ χ₀ * σ t r / r * v' j) (fun t' => by`. Establish `e1 : ∀ g h : X → F, ∑ χ ∈ S, c t' χ * (g χ - c t⁻¹ χ₀ * σ t r / r * h χ) = ∑ χ ∈ S, c t' χ * g χ - c t⁻¹ χ₀ * σ t r / r * ∑ χ ∈ S, c t' χ * h χ`.

Introduce `g h`. Rewrite using `[Finset.mul_sum, ← Finset.sum_sub_distrib]`. Conclude with `Finset.sum_congr rfl fun χ _ => by ring`. Simplify using `only [Sum.elim_inl, Sum.elim_inr, id_eq]`. Rewrite using `[e1 (fun χ => c t⁻¹ χ * σ t (v' (Sum.inl χ))) (fun χ => v' (Sum.inl χ)), e1 (fun χ => c t⁻¹ χ * σ t (v' (Sum.inr χ))) (fun χ => v' (Sum.inr χ))]`.

Take the linear combination `htw t t' - c t⁻¹ χ₀ * σ t r / r * hMv' t')`. Use the proof step `(by`. Introduce `j _ hj`. Simplify using `[hj])`. Use the proof step `(Sum.inl χ₀) (Finset.inl_mem_disjSum.mpr hχ₀S) hr`.

Use the proof step `(by show c t⁻¹ χ₀ * σ t r - c t⁻¹ χ₀ * σ t r / r * r = 0`. Rewrite using `[div_mul_cancel₀ _ hr, sub_self])`. Use `i hi`. Establish `e' : r * (c t⁻¹ (Sum.elim id id i) * σ t (v' i)) = c t⁻¹ χ₀ * σ t r * v' i`. Establish `hz' : c t⁻¹ (Sum.elim id id i) * σ t (v' i) = c t⁻¹ χ₀ * σ t r / r * v' i` using `sub_eq_zero.mp hz`.

Rewrite using `[hz']`. Clear the denominators using the available nonvanishing facts. Establish `hc` using `hcinv t (Sum.elim id id i)`. Establish `hc0` using `hcinv t χ₀`. Establish `h1 : σ t r * (σ t r)⁻¹ = 1` using `mul_inv_cancel₀ hsr`.

Establish `h2 : r * r⁻¹ = 1` using `mul_inv_cancel₀ hr`. Rewrite using `[map_mul, map_inv₀]`. Take the linear combination `((σ t r)⁻¹ * r⁻¹ * c t (Sum.elim id id i) * c t χ₀) * e' - ((σ t r)⁻¹ * σ t (v' i) * c t χ₀ * c t (Sum.elim id id i) * c t⁻¹ (Sum.elim id id i)) * h2 - ((σ t r)⁻¹ * σ t (v' i) * c t χ₀) * hc + (r⁻¹ * c t (Sum.elim id id i) * v' i * c t χ₀ * c t⁻¹ χ₀) * h1 + (r⁻¹ * c t (Sum.elim i …`. Use `⟨χ₀, fun χ => r⁻¹ * v' (Sum.inl χ), fun χ => r⁻¹ * v' (Sum.inr χ), ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← Finset.mul_sum]`.

Conclude with `mul_ne_zero (inv_ne_zero hr) hLv'`. Establish `h1` using `hMv' 1`. Simplify using `only [hone, _root_.one_mul] at h1`. Rewrite using `[← Finset.mul_sum, ← Finset.mul_sum, ← h1]`. Expand and normalize the polynomial expressions, which then agree.

Introduce `t χ hχ`. Conclude with `⟨by simpa only [Sum.elim_inl, id_eq] using hfin t (Sum.inl χ) (Finset.inl_mem_disjSum.mpr hχ), by simpa only [Sum.elim_inr, id_eq] using hfin t (Sum.inr χ) (Finset.inr_mem_disjSum.mpr hχ)⟩`.
-/
theorem exists_weighted_relation :
    ∀ (F T X : Type) [Field F] [Group T] (c : T → X → F) (σ : T → F →+* F) (φ : T → F) (S : Finset X) (p q : X → F), (∀ t t' χ, c (t * t') χ = c t χ * c t' χ) → (∀ χ, c 1 χ = 1) → (∀ t t' χ, σ t (c t' χ) = c t' χ) → (∀ t t', σ t (φ t') = φ (t' * t)) → (∀ t, φ t * ∑ χ ∈ S, c t χ * p χ = ∑ χ ∈ S, c t χ * q χ) → ∑ χ ∈ S, p χ ≠ 0 → ∃ (χ₀ : X) (p' q' : X → F), ∑ χ ∈ S, p' χ ≠ 0 ∧ φ 1 * ∑ χ ∈ S, p' χ = ∑ χ ∈ S, q' χ ∧ ∀ t, ∀ χ ∈ S, σ t (p' χ) * c t χ₀ = c t χ * p' χ ∧ σ t (q' χ) * c t χ₀ = c t χ * q' χ := by
  intro F T X _ _ c σ φ S p q hmul hone hσc hσφ hrel hsum
  classical
  have hcinv : ∀ t χ, c t χ * c t⁻¹ χ = 1 := by
    intro t χ
    rw [← hmul, mul_inv_cancel, hone]
  obtain ⟨v', hMv', hLv', hmin⟩ := exists_minimal_support (S.disjSum S)
    (fun v : X ⊕ X → F => ∀ t, φ t * ∑ χ ∈ S, c t χ * v (Sum.inl χ) = ∑ χ ∈ S, c t χ * v (Sum.inr χ))
    (fun v => ∑ χ ∈ S, v (Sum.inl χ))
    (by
      intro v w a hv hw t
      have e1 : ∀ g h : X → F, ∑ χ ∈ S, c t χ * (g χ - a * h χ)
          = ∑ χ ∈ S, c t χ * g χ - a * ∑ χ ∈ S, c t χ * h χ := by
        intro g h
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun χ _ => by ring
      rw [e1 (fun χ => v (Sum.inl χ)) (fun χ => w (Sum.inl χ)),
        e1 (fun χ => v (Sum.inr χ)) (fun χ => w (Sum.inr χ))]
      linear_combination hv t - a * hw t)
    (by
      intro v w a
      rw [Finset.sum_sub_distrib, Finset.mul_sum])
    (Sum.elim p q) (fun t => hrel t) hsum
  obtain ⟨χ₀, hχ₀S, hr⟩ := Finset.exists_ne_zero_of_sum_ne_zero hLv'
  set r := v' (Sum.inl χ₀) with hrdef
  have htw : ∀ t, ∀ t', φ t' * ∑ χ ∈ S, c t' χ * (c t⁻¹ χ * σ t (v' (Sum.inl χ)))
      = ∑ χ ∈ S, c t' χ * (c t⁻¹ χ * σ t (v' (Sum.inr χ))) := by
    intro t t'
    have h := congrArg (σ t) (hMv' (t' * t⁻¹))
    simp only [map_mul, map_sum, hσc, hσφ, inv_mul_cancel_right, hmul] at h
    have e : ∀ g : X → F, ∑ χ ∈ S, c t' χ * (c t⁻¹ χ * g χ) = ∑ χ ∈ S, c t' χ * c t⁻¹ χ * g χ :=
      fun g => Finset.sum_congr rfl fun χ _ => (mul_assoc _ _ _).symm
    rw [e (fun χ => σ t (v' (Sum.inl χ))), e (fun χ => σ t (v' (Sum.inr χ)))]
    exact h
  have hfin : ∀ t, ∀ i ∈ S.disjSum S,
      σ t (r⁻¹ * v' i) * c t χ₀ = c t (Sum.elim id id i) * (r⁻¹ * v' i) := by
    intro t i hi
    have hsr : σ t r ≠ 0 := (map_ne_zero (σ t)).mpr hr
    have hz := hmin (fun j => c t⁻¹ (Sum.elim id id j) * σ t (v' j) - c t⁻¹ χ₀ * σ t r / r * v' j)
      (fun t' => by
        have e1 : ∀ g h : X → F, ∑ χ ∈ S, c t' χ * (g χ - c t⁻¹ χ₀ * σ t r / r * h χ)
            = ∑ χ ∈ S, c t' χ * g χ - c t⁻¹ χ₀ * σ t r / r * ∑ χ ∈ S, c t' χ * h χ := by
          intro g h
          rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl fun χ _ => by ring
        simp only [Sum.elim_inl, Sum.elim_inr, id_eq]
        rw [e1 (fun χ => c t⁻¹ χ * σ t (v' (Sum.inl χ))) (fun χ => v' (Sum.inl χ)),
          e1 (fun χ => c t⁻¹ χ * σ t (v' (Sum.inr χ))) (fun χ => v' (Sum.inr χ))]
        linear_combination htw t t' - c t⁻¹ χ₀ * σ t r / r * hMv' t')
      (by
        intro j _ hj
        simp [hj])
      (Sum.inl χ₀) (Finset.inl_mem_disjSum.mpr hχ₀S) hr
      (by
        show c t⁻¹ χ₀ * σ t r - c t⁻¹ χ₀ * σ t r / r * r = 0
        rw [div_mul_cancel₀ _ hr, sub_self])
      i hi
    have e' : r * (c t⁻¹ (Sum.elim id id i) * σ t (v' i)) = c t⁻¹ χ₀ * σ t r * v' i := by
      have hz' : c t⁻¹ (Sum.elim id id i) * σ t (v' i) = c t⁻¹ χ₀ * σ t r / r * v' i :=
        sub_eq_zero.mp hz
      rw [hz']
      field_simp
    have hc := hcinv t (Sum.elim id id i)
    have hc0 := hcinv t χ₀
    have h1 : σ t r * (σ t r)⁻¹ = 1 := mul_inv_cancel₀ hsr
    have h2 : r * r⁻¹ = 1 := mul_inv_cancel₀ hr
    rw [map_mul, map_inv₀]
    linear_combination ((σ t r)⁻¹ * r⁻¹ * c t (Sum.elim id id i) * c t χ₀) * e'
      - ((σ t r)⁻¹ * σ t (v' i) * c t χ₀ * c t (Sum.elim id id i) * c t⁻¹ (Sum.elim id id i)) * h2
      - ((σ t r)⁻¹ * σ t (v' i) * c t χ₀) * hc
      + (r⁻¹ * c t (Sum.elim id id i) * v' i * c t χ₀ * c t⁻¹ χ₀) * h1
      + (r⁻¹ * c t (Sum.elim id id i) * v' i) * hc0
  refine ⟨χ₀, fun χ => r⁻¹ * v' (Sum.inl χ), fun χ => r⁻¹ * v' (Sum.inr χ), ?_, ?_, ?_⟩
  · rw [← Finset.mul_sum]
    exact mul_ne_zero (inv_ne_zero hr) hLv'
  · have h1 := hMv' 1
    simp only [hone, _root_.one_mul] at h1
    rw [← Finset.mul_sum, ← Finset.mul_sum, ← h1]
    ring
  · intro t χ hχ
    exact ⟨by simpa only [Sum.elim_inl, id_eq] using hfin t (Sum.inl χ) (Finset.inl_mem_disjSum.mpr hχ),
      by simpa only [Sum.elim_inr, id_eq] using hfin t (Sum.inr χ) (Finset.inr_mem_disjSum.mpr hχ)⟩

end GlobalTheory.SS
