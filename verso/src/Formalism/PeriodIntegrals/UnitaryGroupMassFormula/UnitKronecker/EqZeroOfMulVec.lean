import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitKronecker.PosDefFormNeZero

namespace PI.UnitKronW

open Matrix Polynomial ComplexOrder

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Rewrite using `[pow_succ, Matrix.conjTranspose_mul]`. Combine the equalities or inequalities in the displayed calculation.

Simplify using `only [Matrix.mul_assoc]`. Use `_ = H := by rw [ih, hG]`.
-/
theorem pres_pow {k : ℕ} {H G : Matrix (Fin k) (Fin k) ℂ} (hG : Gᴴ * H * G = H) (n : ℕ) :
    (G ^ n)ᴴ * H * G ^ n = H := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Matrix.conjTranspose_mul]
    calc Gᴴ * (G ^ n)ᴴ * H * (G ^ n * G) = Gᴴ * ((G ^ n)ᴴ * H * G ^ n) * G := by
          simp only [Matrix.mul_assoc]
      _ = H := by rw [ih, hG]

/- English proof (translation)
Conclude with `Matrix.toLin'.injective (LinearMap.ext fun x => by simp [Matrix.toLin'_apply, h])`.
-/
theorem eq_zero_of_mulVec {k : ℕ} (N : Matrix (Fin k) (Fin k) ℂ) (h : ∀ x, N *ᵥ x = 0) : N = 0 := by
  exact Matrix.toLin'.injective (LinearMap.ext fun x => by simp [Matrix.toLin'_apply, h])

/- English proof (translation)
Establish `pres : ∀ x y : Fin k → ℂ, star (W *ᵥ x) ⬝ᵥ (H *ᵥ (W *ᵥ y)) = star x ⬝ᵥ (H *ᵥ y)`. Introduce `x y`. Rewrite using `[Matrix.star_mulVec, Matrix.mulVec_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hW]`. Take `⟨u, hu⟩ : ∃ u, u = (W - 1) *ᵥ v` from `⟨_, rfl⟩`. Rewrite `hv`, the goal using `[← hu]`.

Establish `hWu : W *ᵥ u = u`. Rewrite `hv` using `[Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero]`. Conclude with `hv`. Establish `hu2 : u = W *ᵥ v - v` using `by rw [hu, Matrix.sub_mulVec, Matrix.one_mulVec]`. Establish `h1 : star u ⬝ᵥ (H *ᵥ (W *ᵥ v)) = star u ⬝ᵥ (H *ᵥ v)`.

Use `pres u v` as an intermediate fact. Rewrite `this` using `[hWu]`. Conclude with `this`. Establish `key : star u ⬝ᵥ (H *ᵥ u) = 0` using `by nth_rw 2 [hu2]`. Rewrite using `[Matrix.mulVec_sub]`.

Use `first`. Consider the case `rw [dotProduct_sub, h1, sub_self]`. Consider the case `rw [Matrix.dotProduct_sub, h1, sub_self]`. Assume the negation of the conclusion as `hne`. Establish `hpos : 0 < star u ⬝ᵥ (H *ᵥ u)` using `by first`.

Consider the case `exact hH.2 u hne`. Consider the case `exact hH.dotProduct_mulVec_pos hne`. Rewrite `hpos` using `[key]`. Conclude with `lt_irrefl _ hpos`.
-/
theorem unip_step {k : ℕ} {H W : Matrix (Fin k) (Fin k) ℂ} (hH : H.PosDef) (hW : Wᴴ * H * W = H)
    (v : Fin k → ℂ) (hv : (W - 1) *ᵥ ((W - 1) *ᵥ v) = 0) : (W - 1) *ᵥ v = 0 := by
  have pres : ∀ x y : Fin k → ℂ, star (W *ᵥ x) ⬝ᵥ (H *ᵥ (W *ᵥ y)) = star x ⬝ᵥ (H *ᵥ y) := by
    intro x y
    rw [Matrix.star_mulVec, Matrix.mulVec_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
      ← Matrix.mul_assoc, hW]
  obtain ⟨u, hu⟩ : ∃ u, u = (W - 1) *ᵥ v := ⟨_, rfl⟩
  rw [← hu] at hv ⊢
  have hWu : W *ᵥ u = u := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at hv
    exact hv
  have hu2 : u = W *ᵥ v - v := by rw [hu, Matrix.sub_mulVec, Matrix.one_mulVec]
  have h1 : star u ⬝ᵥ (H *ᵥ (W *ᵥ v)) = star u ⬝ᵥ (H *ᵥ v) := by
    have := pres u v
    rw [hWu] at this
    exact this
  have key : star u ⬝ᵥ (H *ᵥ u) = 0 := by
    nth_rw 2 [hu2]
    rw [Matrix.mulVec_sub]
    first
      | rw [dotProduct_sub, h1, sub_self]
      | rw [Matrix.dotProduct_sub, h1, sub_self]
  by_contra hne
  have hpos : 0 < star u ⬝ᵥ (H *ᵥ u) := by
    first
      | exact hH.2 u hne
      | exact hH.dotProduct_mulVec_pos hne
  rw [key] at hpos
  exact lt_irrefl _ hpos

/- English proof (translation)
Introduce `j`. Proceed by induction on `j with`. Consider the case `zero => intro h`. Simplify using `using h`. Consider the case `succ j ih`.

Introduce `h`. Apply `ih` to reduce the goal to its premises. Apply `eq_zero_of_mulVec` to reduce the goal to its premises. Introduce `x`. Establish `e : (W - 1) ^ (j + 1 + 1) *ᵥ x = (W - 1) *ᵥ ((W - 1) *ᵥ ((W - 1) ^ j *ᵥ x))`.

Rewrite using `[pow_succ', pow_succ', ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]`. Establish `h2 : (W - 1) *ᵥ ((W - 1) *ᵥ ((W - 1) ^ j *ᵥ x)) = 0`. Rewrite using `[← e, h, Matrix.zero_mulVec]`. Establish `h3` using `unip_step hH hW _ h2`. Rewrite using `[pow_succ', ← Matrix.mulVec_mulVec]`.

Conclude with `h3`.
-/
theorem unip_pow {k : ℕ} {H W : Matrix (Fin k) (Fin k) ℂ} (hH : H.PosDef) (hW : Wᴴ * H * W = H) :
    ∀ j : ℕ, (W - 1) ^ (j + 1) = 0 → W - 1 = 0 := by
  intro j
  induction j with
  | zero => intro h; simpa using h
  | succ j ih =>
    intro h
    apply ih
    apply eq_zero_of_mulVec
    intro x
    have e : (W - 1) ^ (j + 1 + 1) *ᵥ x = (W - 1) *ᵥ ((W - 1) *ᵥ ((W - 1) ^ j *ᵥ x)) := by
      rw [pow_succ', pow_succ', ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    have h2 : (W - 1) *ᵥ ((W - 1) *ᵥ ((W - 1) ^ j *ᵥ x)) = 0 := by
      rw [← e, h, Matrix.zero_mulVec]
    have h3 := unip_step hH hW _ h2
    rw [pow_succ', ← Matrix.mulVec_mulVec]
    exact h3

/- English proof (translation)
Establish `hmon : G.charpoly.Monic` using `Matrix.charpoly_monic G`. Establish `hcard : Multiset.card G.charpoly.roots = k`. Establish `h1 : Multiset.card G.charpoly.roots = G.charpoly.natDegree` using `by first`. Consider the case `exact (IsAlgClosed.card_roots_eq_natDegree (k := ℂ))`. Consider the case `exact IsAlgClosed.card_roots_eq_natDegree`.

Consider the case `exact (Polynomial.natDegree_eq_card_roots (IsAlgClosed.splits _)).symm`. Rewrite using `[h1, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]`. Establish `hprod : (G.charpoly.roots.map fun a => X - C a).prod = G.charpoly` using `Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hmon (by`. Rewrite using `[hcard, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin])`. Rewrite using `[← hprod]`.

Establish `hd : (G.charpoly.roots.map fun a => X - C a).prod ∣ (G.charpoly.roots.map fun _ => (X ^ n - 1 : ℂ[X])).prod`. Apply `Multiset.prod_dvd_prod_of_dvd` to reduce the goal to its premises. Introduce `μ hμ`. Rewrite using `[Polynomial.dvd_iff_isRoot]`. Simplify using `[hn μ hμ]`.

Rewrite `hd` using `[Multiset.map_const', Multiset.prod_replicate, hcard]`. Conclude with `hd`.
-/
theorem charpoly_dvd {k : ℕ} (G : Matrix (Fin k) (Fin k) ℂ) (n : ℕ)
    (hn : ∀ μ ∈ G.charpoly.roots, μ ^ n = 1) : G.charpoly ∣ (X ^ n - 1 : ℂ[X]) ^ k := by
  have hmon : G.charpoly.Monic := Matrix.charpoly_monic G
  have hcard : Multiset.card G.charpoly.roots = k := by
    have h1 : Multiset.card G.charpoly.roots = G.charpoly.natDegree := by
      first
        | exact (IsAlgClosed.card_roots_eq_natDegree (k := ℂ))
        | exact IsAlgClosed.card_roots_eq_natDegree
        | exact (Polynomial.natDegree_eq_card_roots (IsAlgClosed.splits _)).symm
    rw [h1, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  have hprod : (G.charpoly.roots.map fun a => X - C a).prod = G.charpoly :=
    Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hmon (by
      rw [hcard, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin])
  rw [← hprod]
  have hd : (G.charpoly.roots.map fun a => X - C a).prod ∣
      (G.charpoly.roots.map fun _ => (X ^ n - 1 : ℂ[X])).prod := by
    apply Multiset.prod_dvd_prod_of_dvd
    intro μ hμ
    rw [Polynomial.dvd_iff_isRoot]
    simp [hn μ hμ]
  rw [Multiset.map_const', Multiset.prod_replicate, hcard] at hd
  exact hd

/- English proof (translation)
Unfold `StepC`. Introduce `k H G hH hG n hn`. Establish `hW` using `pres_pow hG n`. Establish `hdvd` using `charpoly_dvd G n hn`. Establish `h0 : (G ^ n - 1) ^ k = 0`.

Take `⟨q, hq⟩` from `hdvd`. Establish `h` using `congrArg (Polynomial.aeval G) hq`. Rewrite `h` using `[map_mul, Matrix.aeval_self_charpoly, zero_mul]`. Simplify using `using h`. Break down `Nat.eq_zero_or_pos k with rfl | hk` into its components or cases.

Use extensionality with `i j`. Conclude with `Fin.elim0 i`. Establish `h1` using `unip_pow hH hW (k - 1) (by rw [Nat.sub_add_cancel hk]; exact h0)`. Conclude with `sub_eq_zero.mp h1`.
-/
theorem stepC : StepC := by
  unfold StepC
  intro k H G hH hG n hn
  have hW := pres_pow hG n
  have hdvd := charpoly_dvd G n hn
  have h0 : (G ^ n - 1) ^ k = 0 := by
    obtain ⟨q, hq⟩ := hdvd
    have h := congrArg (Polynomial.aeval G) hq
    rw [map_mul, Matrix.aeval_self_charpoly, zero_mul] at h
    simpa using h
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · ext i j
    exact Fin.elim0 i
  · have h1 := unip_pow hH hW (k - 1) (by rw [Nat.sub_add_cancel hk]; exact h0)
    exact sub_eq_zero.mp h1

end PI.UnitKronW
