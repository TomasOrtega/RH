import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.GoodPathWeight

noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas

/- English proof (translation)
Establish `heq : (restrictSupport R s : Submodule R (MvPolynomial σ R)) = Submodule.span R ((fun m => (monomial m (1 : R) : MvPolynomial σ R)) '' s)`. Apply `le_antisymm` to reduce the goal to its premises. Introduce `P hP`. Rewrite `hP` using `[MvPolynomial.mem_restrictSupport_iff]`. Rewrite using `[P.as_sum]`.

Use `Submodule.sum_mem _ fun m hm => ?_` and prove the remaining obligations. Establish `: (monomial m (coeff m P) : MvPolynomial σ R) = coeff m P • monomial m (1 : R)`. Rewrite using `[smul_monomial, smul_eq_mul, mul_one]`. Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, hP (by exact_mod_cast hm), rfl⟩)`.

Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨m, hm, rfl⟩`. Rewrite using `[SetLike.mem_coe, MvPolynomial.mem_restrictSupport_iff]`. Introduce `m' hm'`. Use `MvPolynomial.support_monomial_subset (by exact_mod_cast hm')` as an intermediate fact.

Rewrite `this` using `[Finset.mem_singleton]`. Rewrite using `[this]`. Conclude with `hm`. Rewrite using `[heq]`. Conclude with `Submodule.fg_span (hs.image _)`.
-/
theorem finite_restrictSupport' (R : Type) [CommRing R] (σ : Type) (s : Set (σ →₀ ℕ)) (hs : s.Finite) :
    (restrictSupport R s : Submodule R (MvPolynomial σ R)).FG := by
  have heq : (restrictSupport R s : Submodule R (MvPolynomial σ R)) =
      Submodule.span R ((fun m => (monomial m (1 : R) : MvPolynomial σ R)) '' s) := by
    apply le_antisymm
    · intro P hP
      rw [MvPolynomial.mem_restrictSupport_iff] at hP
      rw [P.as_sum]
      refine Submodule.sum_mem _ fun m hm => ?_
      have : (monomial m (coeff m P) : MvPolynomial σ R) = coeff m P • monomial m (1 : R) := by
        rw [smul_monomial, smul_eq_mul, mul_one]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, hP (by exact_mod_cast hm), rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨m, hm, rfl⟩
      rw [SetLike.mem_coe, MvPolynomial.mem_restrictSupport_iff]
      intro m' hm'
      have := MvPolynomial.support_monomial_subset (by exact_mod_cast hm')
      rw [Finset.mem_singleton] at this
      rw [this]; exact hm
  rw [heq]
  exact Submodule.fg_span (hs.image _)

/- English proof (translation)
Set `B : ℤ × Fin (r + K) →₀ ℕ` to `Finsupp.onFinset (L ×ˢ Finset.univ) (fun v => b v.1) (by`. Introduce `v hv`. Assume the negation of the conclusion as `h`. Apply `hv` to reduce the goal to its premises. Apply `hb` to reduce the goal to its premises.

Introduce `hL`. Conclude with `h (Finset.mem_product.mpr ⟨hL, Finset.mem_univ _⟩))`. Use `(Set.finite_Iic B).subset ?_` and prove the remaining obligations. Introduce `m hm v`. Establish `h` using `hm v.1`.

Establish `: m (v.1, v.2) ≤ ∑ c : Fin (r + K), m (v.1, c)` using `Finset.single_le_sum (f := fun c => m (v.1, c)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ v.2)`. Rewrite `this` using `[h]`. Simplify `this` using `[B]`.
-/
theorem segDegSet_finite {r : ℕ} (K : ℕ) (b : ℤ → ℕ) (L : Finset ℤ) (hb : ∀ x, x ∉ L → b x = 0) :
    (Dat.segDegSet (r := r) K b).Finite := by
  classical
  let B : ℤ × Fin (r + K) →₀ ℕ := Finsupp.onFinset (L ×ˢ Finset.univ) (fun v => b v.1) (by
    intro v hv
    by_contra h
    apply hv
    apply hb
    intro hL
    exact h (Finset.mem_product.mpr ⟨hL, Finset.mem_univ _⟩))
  refine (Set.finite_Iic B).subset ?_
  intro m hm v
  have h := hm v.1
  have : m (v.1, v.2) ≤ ∑ c : Fin (r + K), m (v.1, c) :=
    Finset.single_le_sum (f := fun c => m (v.1, c)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ v.2)
  rw [h] at this
  simpa [B] using this

/- English proof (translation)
Introduce `p n' r K _ _ _ X O _ _ _ j b hb`. Establish `hfg` using `finite_restrictSupport' O (ℤ × Fin (r + K)) _ (segDegSet_finite (r := r) K b (X.F.letters j) hb)`. Establish `hN : IsNoetherian O (restrictSupport O (Dat.segDegSet (r` using `r) K b) : Submodule O (SegRing O r K)) := isNoetherian_of_fg_of_noetherian _ hfg`. Establish `hle : X.Mj p K O j b ≤ restrictSupport O (Dat.segDegSet (r` using `r) K b) := by`. Introduce `P hP`.

Conclude with `hP.1.2`. Establish `: IsNoetherian O (X.Mj p K O j b)` using `isNoetherian_of_le hle`. Use `infer_instance`.
-/
theorem restFin : RestFin := by
  intro p n' r K _ _ _ X O _ _ _ j b hb
  have hfg := finite_restrictSupport' O (ℤ × Fin (r + K)) _ (segDegSet_finite (r := r) K b (X.F.letters j) hb)
  have hN : IsNoetherian O (restrictSupport O (Dat.segDegSet (r := r) K b) : Submodule O (SegRing O r K)) :=
    isNoetherian_of_fg_of_noetherian _ hfg
  have hle : X.Mj p K O j b ≤ restrictSupport O (Dat.segDegSet (r := r) K b) := by
    intro P hP
    exact hP.1.2
  have : IsNoetherian O (X.Mj p K O j b) := isNoetherian_of_le hle
  infer_instance

end Formalism.MainNotions.SelectionLemmas.Pf
