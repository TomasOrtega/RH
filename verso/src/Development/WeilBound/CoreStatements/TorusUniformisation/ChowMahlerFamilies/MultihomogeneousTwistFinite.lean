import Mathlib
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsLatFlagPair
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagIndependence
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.FiniteNonvanishingSelection

open MvPolynomial

namespace PositivityTheory.Xgn.MultihomogeneousTwistFinite
open GroundTheory.Heights₂.Heights.NumbersDVR

/- English proof (translation)
Establish `h` using `IsWeightedHomogeneous.prod (w := blockWeight ι) Finset.univ (fun k => (X ⟨k, c k⟩ : MvPolynomial (Σ k, ι k) ℤ) ^ d k) (fun k => d k • blockWeight ι ⟨k, c k⟩) (fun k _ => (isWeightedHomogeneous_X ℤ (blockWeight ι) ⟨k, c k⟩).pow (d k))`. Establish `e : ∑ k, d k • blockWeight ι ⟨k, c k⟩ = d`. Use function extensionality and compare the values at `j`. Simplify using `[blockWeight, Finset.sum_apply, Pi.single_apply]`. Rewrite `h` using `[e]`.

Conclude with `h`.
-/
theorem homog_prod {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} (c : ∀ k, ι k)
    (d : K → ℕ) :
    IsMultiHomog (∏ k, (X ⟨k, c k⟩ : MvPolynomial (Σ k, ι k) ℤ) ^ d k) d := by
  have h := IsWeightedHomogeneous.prod (w := blockWeight ι) Finset.univ
    (fun k => (X ⟨k, c k⟩ : MvPolynomial (Σ k, ι k) ℤ) ^ d k)
    (fun k => d k • blockWeight ι ⟨k, c k⟩)
    (fun k _ => (isWeightedHomogeneous_X ℤ (blockWeight ι) ⟨k, c k⟩).pow (d k))
  have e : ∑ k, d k • blockWeight ι ⟨k, c k⟩ = d := by
    funext j
    simp [blockWeight, Finset.sum_apply, Pi.single_apply]
  rw [e] at h
  exact h

/- English proof (translation)
Rewrite using `[map_mul, map_mul]`. Use `mul_ne_zero hu ?_` and prove the remaining obligations. Simplify using `only [map_prod, map_pow, MvPolynomial.map_X, MvPolynomial.eval_X]`. Conclude with `Finset.prod_ne_zero_iff.2 (fun k _ => pow_ne_zero _ (hc k))`.
-/
theorem eval_mul_ne {K : Type} [Fintype K] {ι : K → Type} (c : ∀ k, ι k)
    (d : K → ℕ) (z : (Σ k, ι k) → ℂ) (hc : ∀ k, z ⟨k, c k⟩ ≠ 0) (u : MvPolynomial (Σ k, ι k) ℤ)
    (hu : eval z (MvPolynomial.map (Int.castRingHom ℂ) u) ≠ 0) :
    eval z (MvPolynomial.map (Int.castRingHom ℂ)
      (u * ∏ k, (X ⟨k, c k⟩ : MvPolynomial (Σ k, ι k) ℤ) ^ d k)) ≠ 0 := by
  rw [map_mul, map_mul]
  refine mul_ne_zero hu ?_
  simp only [map_prod, map_pow, MvPolynomial.map_X, MvPolynomial.eval_X]
  exact Finset.prod_ne_zero_iff.2 (fun k _ => pow_ne_zero _ (hc k))

end PositivityTheory.Xgn.MultihomogeneousTwistFinite

/- English proof (translation)
Introduce `K _ _ ι _ Q bf bg hQmul hQ hU hV`. Take `⟨TU, hTU, hselU⟩` from `PositivityTheory.Xgn.finite_nonvanishing_selection (Σ k, ι k) {u | ∃ a b v, Q a b u v}`. Take `⟨TV, hTV, hselV⟩` from `PositivityTheory.Xgn.finite_nonvanishing_selection (Σ k, ι k) {v | ∃ a b u, Q a b u v}`. Establish `wU : ∀ t : TU, ∃ a b v, Q a b t.1 v` using `fun t => hTU t.2`. Establish `wV : ∀ t : TV, ∃ a b u, Q a b u t.1` using `fun t => hTV t.2`.

Use `choose aU bU vU hqU using wU`. Use `choose aV bV uV hqV using wV`. Take `⟨A, hA⟩ : ∃ A : K → ℕ, A = bg + (∑ t, aU t + ∑ t, aV t)` from `⟨_, rfl⟩`. Establish `leU : ∀ t k, aU t k ≤ A k`. Introduce `t k`.

Rewrite using `[hA]`. Simplify using `only [Pi.add_apply, Finset.sum_apply]`. Use `Finset.single_le_sum (f := fun t => aU t k) (fun _ _ => Nat.zero_le _) (Finset.mem_univ t)` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `leV : ∀ t k, aV t k ≤ A k`.

Introduce `t k`. Rewrite using `[hA]`. Simplify using `only [Pi.add_apply, Finset.sum_apply]`. Use `Finset.single_le_sum (f := fun t => aV t k) (fun _ _ => Nat.zero_le _) (Finset.mem_univ t)` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Establish `hbgA : ∀ k, bg k ≤ A k`. Introduce `k`. Rewrite using `[hA]`. Simplify using `only [Pi.add_apply]`. Use linear arithmetic over natural numbers and integers.

Take `⟨B, hB⟩ : ∃ B : K → ℕ, B = A + bf - bg` from `⟨_, rfl⟩`. Establish `hAB : A + bf = B + bg`. Use function extensionality and compare the values at `k`. Rewrite using `[hB]`. Simplify using `only [Pi.add_apply, Pi.sub_apply]`.

Use `hbgA k` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `lift : ∀ (a b : K → ℕ) (u v : MvPolynomial (Σ k, ι k) ℤ) (c : ∀ k, ι k), Q a b u v → (∀ k, a k ≤ A k) → Q A B (u * ∏ k, (X ⟨k, c k⟩ : MvPolynomial (Σ k, ι k) ℤ) ^ (A - a) k) (v * ∏ k, (X ⟨k, c k⟩ : MvPolynomial (Σ k, ι k) ℤ) ^ (A - a) k)`. Introduce `a b u v c hq hle`. Establish `h` using `hQmul a b (A - a) u v _ hq (MultihomogeneousTwistFinite.homog_prod c (A - a))`.

Take `⟨_, _, hab⟩` from `hQ a b u v hq`. Establish `e1 : a + (A - a) = A`. Use function extensionality and compare the values at `k`. Simplify using `only [Pi.add_apply, Pi.sub_apply]`. Use `hle k` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Establish `e2 : b + (A - a) = B`. Use function extensionality and compare the values at `k`. Establish `h1` using `congrFun hab k`. Establish `h2` using `congrFun hAB k`.

Simplify using `only [Pi.add_apply, Pi.sub_apply] at h1 h2 ⊢`. Use `hle k` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Rewrite `h` using `[e1, e2]`. Conclude with `h`.

Set `e` to `Fintype.equivFin ((TU × (∀ k, ι k)) ⊕ (TV × (∀ k, ι k)))`. Set `uu : (TU × (∀ k, ι k)) ⊕ (TV × (∀ k, ι k)) → MvPolynomial (Σ k, ι k) ℤ` to `Sum.elim (fun p => p.1.1 * ∏ k, (X ⟨k, p.2 k⟩ : MvPolynomial (Σ k, ι k) ℤ) ^ (A - aU p.1) k) (fun p => uV p.1 * ∏ k, (X ⟨k, p.2 k⟩ : MvPolynomial (Σ k, ι k) ℤ) ^ (A - aV p.1) k)`. Set `vv : (TU × (∀ k, ι k)) ⊕ (TV × (∀ k, ι k)) → MvPolynomial (Σ k, ι k) ℤ` to `Sum.elim (fun p => vU p.1 * ∏ k, (X ⟨k, p.2 k⟩ : MvPolynomial (Σ k, ι k) ℤ) ^ (A - aU p.1) k) (fun p => p.1.1 * ∏ k, (X ⟨k, p.2 k⟩ : MvPolynomial (Σ k, ι k) ℤ) ^ (A - aV p.1) k)`. Use `⟨A, B, _, fun j => uu (e.symm j), fun j => vv (e.symm j), hAB, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `j show Q A B (uu (e.symm j)) (vv (e.symm j))`.

Generalize the expression as in `e.symm j = w`. Break down `w with ⟨t, c⟩ | ⟨t, c⟩` into its components or cases. Conclude with `lift _ _ _ _ c (hqU t) (leU t)`. Conclude with `lift _ _ _ _ c (hqV t) (leV t)`. Introduce `z hz`.

Take `⟨a, b, u, v, hq, hu⟩` from `hU z hz`. Use `choose c hc using hz`. Take `⟨t, ht, htne⟩` from `hselU z ⟨u, ⟨a, b, v, hq⟩, hu⟩`. Use `⟨e (Sum.inl (⟨t, ht⟩, c)), ?_⟩` and prove the remaining obligations. Simplify using `only [uu, Equiv.symm_apply_apply, Sum.elim_inl]`.

Conclude with `MultihomogeneousTwistFinite.eval_mul_ne c _ z hc _ htne`. Introduce `z hz`. Take `⟨a, b, u, v, hq, hv⟩` from `hV z hz`. Use `choose c hc using hz`. Take `⟨t, ht, htne⟩` from `hselV z ⟨v, ⟨a, b, u, hq⟩, hv⟩`.

Use `⟨e (Sum.inr (⟨t, ht⟩, c)), ?_⟩` and prove the remaining obligations. Simplify using `only [vv, Equiv.symm_apply_apply, Sum.elim_inr]`. Conclude with `MultihomogeneousTwistFinite.eval_mul_ne c _ z hc _ htne`.
-/
theorem PositivityTheory.Xgn.multihomogeneous_twist_finite : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Q : (K → ℕ) → (K → ℕ) → MvPolynomial (Σ k, ι k) ℤ → MvPolynomial (Σ k, ι k) ℤ → Prop) (bf bg : K → ℕ), (∀ (a b d : K → ℕ) (u v m : MvPolynomial (Σ k, ι k) ℤ), Q a b u v → GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog m d → Q (a + d) (b + d) (u * m) (v * m)) → (∀ (a b : K → ℕ) (u v : MvPolynomial (Σ k, ι k) ℤ), Q a b u v → GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog u a ∧ GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog v b ∧ a + bf = b + bg) → (∀ z : ((Σ k, ι k) → ℂ), (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → ∃ (a b : K → ℕ) (u v : MvPolynomial (Σ k, ι k) ℤ), Q a b u v ∧ eval z (MvPolynomial.map (Int.castRingHom ℂ) u) ≠ 0) → (∀ z : ((Σ k, ι k) → ℂ), (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → ∃ (a b : K → ℕ) (u v : MvPolynomial (Σ k, ι k) ℤ), Q a b u v ∧ eval z (MvPolynomial.map (Int.castRingHom ℂ) v) ≠ 0) → ∃ (A B : K → ℕ) (n : ℕ) (u v : Fin n → MvPolynomial (Σ k, ι k) ℤ), A + bf = B + bg ∧ (∀ j, Q A B (u j) (v j)) ∧ (∀ z : ((Σ k, ι k) → ℂ), (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → ∃ j, eval z (MvPolynomial.map (Int.castRingHom ℂ) (u j)) ≠ 0) ∧ (∀ z : ((Σ k, ι k) → ℂ), (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → ∃ j, eval z (MvPolynomial.map (Int.castRingHom ℂ) (v j)) ≠ 0) := by
  intro K _ _ ι _ Q bf bg hQmul hQ hU hV
  obtain ⟨TU, hTU, hselU⟩ :=
    PositivityTheory.Xgn.finite_nonvanishing_selection (Σ k, ι k) {u | ∃ a b v, Q a b u v}
  obtain ⟨TV, hTV, hselV⟩ :=
    PositivityTheory.Xgn.finite_nonvanishing_selection (Σ k, ι k) {v | ∃ a b u, Q a b u v}
  have wU : ∀ t : TU, ∃ a b v, Q a b t.1 v := fun t => hTU t.2
  have wV : ∀ t : TV, ∃ a b u, Q a b u t.1 := fun t => hTV t.2
  choose aU bU vU hqU using wU
  choose aV bV uV hqV using wV
  obtain ⟨A, hA⟩ : ∃ A : K → ℕ, A = bg + (∑ t, aU t + ∑ t, aV t) := ⟨_, rfl⟩
  have leU : ∀ t k, aU t k ≤ A k := by
    intro t k
    rw [hA]
    simp only [Pi.add_apply, Finset.sum_apply]
    have := Finset.single_le_sum (f := fun t => aU t k) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ t)
    omega
  have leV : ∀ t k, aV t k ≤ A k := by
    intro t k
    rw [hA]
    simp only [Pi.add_apply, Finset.sum_apply]
    have := Finset.single_le_sum (f := fun t => aV t k) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ t)
    omega
  have hbgA : ∀ k, bg k ≤ A k := by
    intro k
    rw [hA]
    simp only [Pi.add_apply]
    omega
  obtain ⟨B, hB⟩ : ∃ B : K → ℕ, B = A + bf - bg := ⟨_, rfl⟩
  have hAB : A + bf = B + bg := by
    funext k
    rw [hB]
    simp only [Pi.add_apply, Pi.sub_apply]
    have := hbgA k
    omega
  have lift : ∀ (a b : K → ℕ) (u v : MvPolynomial (Σ k, ι k) ℤ) (c : ∀ k, ι k), Q a b u v →
      (∀ k, a k ≤ A k) →
      Q A B (u * ∏ k, (X ⟨k, c k⟩ : MvPolynomial (Σ k, ι k) ℤ) ^ (A - a) k)
        (v * ∏ k, (X ⟨k, c k⟩ : MvPolynomial (Σ k, ι k) ℤ) ^ (A - a) k) := by
    intro a b u v c hq hle
    have h := hQmul a b (A - a) u v _ hq (MultihomogeneousTwistFinite.homog_prod c (A - a))
    obtain ⟨_, _, hab⟩ := hQ a b u v hq
    have e1 : a + (A - a) = A := by
      funext k
      simp only [Pi.add_apply, Pi.sub_apply]
      have := hle k
      omega
    have e2 : b + (A - a) = B := by
      funext k
      have h1 := congrFun hab k
      have h2 := congrFun hAB k
      simp only [Pi.add_apply, Pi.sub_apply] at h1 h2 ⊢
      have := hle k
      omega
    rw [e1, e2] at h
    exact h
  let e := Fintype.equivFin ((TU × (∀ k, ι k)) ⊕ (TV × (∀ k, ι k)))
  let uu : (TU × (∀ k, ι k)) ⊕ (TV × (∀ k, ι k)) → MvPolynomial (Σ k, ι k) ℤ :=
    Sum.elim (fun p => p.1.1 * ∏ k, (X ⟨k, p.2 k⟩ : MvPolynomial (Σ k, ι k) ℤ) ^ (A - aU p.1) k)
      (fun p => uV p.1 * ∏ k, (X ⟨k, p.2 k⟩ : MvPolynomial (Σ k, ι k) ℤ) ^ (A - aV p.1) k)
  let vv : (TU × (∀ k, ι k)) ⊕ (TV × (∀ k, ι k)) → MvPolynomial (Σ k, ι k) ℤ :=
    Sum.elim (fun p => vU p.1 * ∏ k, (X ⟨k, p.2 k⟩ : MvPolynomial (Σ k, ι k) ℤ) ^ (A - aU p.1) k)
      (fun p => p.1.1 * ∏ k, (X ⟨k, p.2 k⟩ : MvPolynomial (Σ k, ι k) ℤ) ^ (A - aV p.1) k)
  refine ⟨A, B, _, fun j => uu (e.symm j), fun j => vv (e.symm j), hAB, ?_, ?_, ?_⟩
  · intro j
    show Q A B (uu (e.symm j)) (vv (e.symm j))
    generalize e.symm j = w
    rcases w with ⟨t, c⟩ | ⟨t, c⟩
    · exact lift _ _ _ _ c (hqU t) (leU t)
    · exact lift _ _ _ _ c (hqV t) (leV t)
  · intro z hz
    obtain ⟨a, b, u, v, hq, hu⟩ := hU z hz
    choose c hc using hz
    obtain ⟨t, ht, htne⟩ := hselU z ⟨u, ⟨a, b, v, hq⟩, hu⟩
    refine ⟨e (Sum.inl (⟨t, ht⟩, c)), ?_⟩
    simp only [uu, Equiv.symm_apply_apply, Sum.elim_inl]
    exact MultihomogeneousTwistFinite.eval_mul_ne c _ z hc _ htne
  · intro z hz
    obtain ⟨a, b, u, v, hq, hv⟩ := hV z hz
    choose c hc using hz
    obtain ⟨t, ht, htne⟩ := hselV z ⟨v, ⟨a, b, u, hq⟩, hv⟩
    refine ⟨e (Sum.inr (⟨t, ht⟩, c)), ?_⟩
    simp only [vv, Equiv.symm_apply_apply, Sum.elim_inr]
    exact MultihomogeneousTwistFinite.eval_mul_ne c _ z hc _ htne
