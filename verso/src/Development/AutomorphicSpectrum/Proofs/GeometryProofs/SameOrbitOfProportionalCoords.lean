import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SmallPointsCoordRatioBoundStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.OrbitBlock

/- English proof (translation)
Simplify using `only [MvPolynomial.aeval_def]`. Rewrite using `[MvPolynomial.eval₂_eq', MvPolynomial.eval₂_eq', Finset.mul_sum]`. Use `Finset.sum_congr rfl fun d hd => ?_` and prove the remaining obligations. Establish `hdeg : ∑ i, d i = n`. Establish `h` using `hF (MvPolynomial.mem_support_iff.1 hd)`.

Rewrite using `[← h, Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]`. Simplify using the standard rewrite rules. Simplify using `only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hdeg]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem aeval_smul_of_homog {σ A : Type} [Fintype σ] [CommRing A] [Algebra ℤ A] {n : ℕ}
    {F : MvPolynomial σ ℤ} (hF : F.IsHomogeneous n) (t : A) (b : σ → A) :
    MvPolynomial.aeval (fun i => t * b i) F = t ^ n * MvPolynomial.aeval b F := by
  classical
  simp only [MvPolynomial.aeval_def]
  rw [MvPolynomial.eval₂_eq', MvPolynomial.eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdeg : ∑ i, d i = n := by
    have h := hF (MvPolynomial.mem_support_iff.1 hd)
    rw [← h, Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
    simp
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hdeg]
  ring

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {Ω : Type} [Field Ω]

/- English proof (translation)
Establish `h1 : mConeMap y (MvPolynomial.rename (Sigma.mk k₀) F) = MvPolynomial.aeval (fun i : J k₀ => (MvPolynomial.X k₀ : MvPolynomial K Ω) * MvPolynomial.C (y ⟨k₀, i⟩)) F`. Rewrite using `[mConeMap, MvPolynomial.aeval_rename]`. Use `congr 2`. Use function extensionality and compare the values at `i`. Simplify using `[mul_comm]`.

Rewrite using `[h1, aeval_smul_of_homog hF]`. Use `congr 1`. Conclude with `(MvPolynomial.comp_aeval_apply (fun i : J k₀ => y ⟨k₀, i⟩) (IsScalarTower.toAlgHom ℤ Ω (MvPolynomial K Ω)) F).symm`.
-/
theorem mConeMap_rename_block {n : ℕ} (y : (Σ k, J k) → Ω) (k₀ : K)
    {F : MvPolynomial (J k₀) ℤ} (hF : F.IsHomogeneous n) :
    mConeMap y (MvPolynomial.rename (Sigma.mk k₀) F) =
      MvPolynomial.X k₀ ^ n *
        MvPolynomial.C (MvPolynomial.aeval (fun i : J k₀ => y ⟨k₀, i⟩) F) := by
  have h1 : mConeMap y (MvPolynomial.rename (Sigma.mk k₀) F) =
      MvPolynomial.aeval (fun i : J k₀ => (MvPolynomial.X k₀ : MvPolynomial K Ω) *
        MvPolynomial.C (y ⟨k₀, i⟩)) F := by
    rw [mConeMap, MvPolynomial.aeval_rename]
    congr 2
    funext i
    simp [mul_comm]
  rw [h1, aeval_smul_of_homog hF]
  congr 1
  exact (MvPolynomial.comp_aeval_apply (fun i : J k₀ => y ⟨k₀, i⟩)
    (IsScalarTower.toAlgHom ℤ Ω (MvPolynomial K Ω)) F).symm

/- English proof (translation)
Use `set G : MRing J := MvPolynomial.rename (Sigma.mk k₀) Fj * MvPolynomial.X ⟨k, c⟩ - MvPolynomial.rename (Sigma.mk k₀) Fc * MvPolynomial.X ⟨k, j⟩ with hG`. Establish `hmem : G ∈ mCoordIdeal y`. Rewrite using `[mCoordIdeal, RingHom.mem_ker, hG, map_sub, map_mul, map_mul, mConeMap_rename_block y k₀ hj, mConeMap_rename_block y k₀ hc]`. Establish `hx : ∀ p : Σ k, J k, mConeMap y (MvPolynomial.X p) = MvPolynomial.C (y p) * MvPolynomial.X p.1` using `fun p => by`. Simplify using `[mConeMap]`.

Rewrite using `[hx, hx]`. Establish `h'` using `congrArg (MvPolynomial.C : Ω →+* MvPolynomial K Ω) h`. Simplify using `only [map_mul] at h'`. Take the linear combination `(MvPolynomial.X k₀ ^ n * MvPolynomial.X k) * h'`. Establish `hv` using `hw.2 G hmem`.

Establish `hv' : MvPolynomial.aeval w G = 0`. Rewrite using `[← hv, MvPolynomial.eval_map]`. Both sides reduce to the same expression. Rewrite `hv'` using `[hG, map_sub, map_mul, map_mul, MvPolynomial.aeval_rename, MvPolynomial.aeval_rename, MvPolynomial.aeval_X, MvPolynomial.aeval_X]`. Conclude with `sub_eq_zero.1 hv'`.
-/
theorem relation_at {n : ℕ} (y : (Σ k, J k) → Ω) (k₀ k : K) (c j : J k)
    {Fj Fc : MvPolynomial (J k₀) ℤ} (hj : Fj.IsHomogeneous n) (hc : Fc.IsHomogeneous n)
    (h : MvPolynomial.aeval (fun i : J k₀ => y ⟨k₀, i⟩) Fj * y ⟨k, c⟩ =
      MvPolynomial.aeval (fun i : J k₀ => y ⟨k₀, i⟩) Fc * y ⟨k, j⟩)
    {w : (Σ k, J k) → ℂ} (hw : w ∈ mcPts (mCoordIdeal y)) :
    MvPolynomial.aeval (fun i : J k₀ => w ⟨k₀, i⟩) Fj * w ⟨k, c⟩ =
      MvPolynomial.aeval (fun i : J k₀ => w ⟨k₀, i⟩) Fc * w ⟨k, j⟩ := by
  set G : MRing J := MvPolynomial.rename (Sigma.mk k₀) Fj * MvPolynomial.X ⟨k, c⟩ -
    MvPolynomial.rename (Sigma.mk k₀) Fc * MvPolynomial.X ⟨k, j⟩ with hG
  have hmem : G ∈ mCoordIdeal y := by
    rw [mCoordIdeal, RingHom.mem_ker, hG, map_sub, map_mul, map_mul,
      mConeMap_rename_block y k₀ hj, mConeMap_rename_block y k₀ hc]
    have hx : ∀ p : Σ k, J k, mConeMap y (MvPolynomial.X p) =
        MvPolynomial.C (y p) * MvPolynomial.X p.1 := fun p => by
      simp [mConeMap]
    rw [hx, hx]
    have h' := congrArg (MvPolynomial.C : Ω →+* MvPolynomial K Ω) h
    simp only [map_mul] at h'
    linear_combination (MvPolynomial.X k₀ ^ n * MvPolynomial.X k) * h'
  have hv := hw.2 G hmem
  have hv' : MvPolynomial.aeval w G = 0 := by
    rw [← hv, MvPolynomial.eval_map]
    rfl
  rw [hG, map_sub, map_mul, map_mul, MvPolynomial.aeval_rename, MvPolynomial.aeval_rename,
    MvPolynomial.aeval_X, MvPolynomial.aeval_X] at hv'
  exact sub_eq_zero.1 hv'

/- English proof (translation)
Introduce `X Ω _ _ ξ K _ J _ y k₀ hT hE w hw w' hw' u hu`. Establish `hpts : w ∈ Small.ptsOver ℂ (mCoordIdeal y)`. Use `⟨hw.1, fun f hf => ?_⟩` and prove the remaining obligations. Rewrite using `[← hw.2 f hf, MvPolynomial.eval_map]`. Both sides reduce to the same expression.

Take `⟨i, hi⟩` from `hw.1 k₀`. Establish `hu0 : u ≠ 0`. Introduce and unpack `rfl`. Conclude with `hi (by rw [hu i, zero_mul])`. Establish `key : ∀ k, ∃ s : ℂ, s ≠ 0 ∧ ∀ j, w ⟨k, j⟩ = s * w' ⟨k, j⟩`.

Introduce `k`. Take `⟨c, hc⟩` from `hw.1 k`. Take `⟨n, F, hF, hrel, hne⟩` from `GlobalTheory.T.small_points_coord_ratio_bound X Ω ξ K J y k₀ hT hE ℂ w hpts i k c hi hc`. Establish `hscale : ∀ t, MvPolynomial.aeval (fun i' : J k₀ => w ⟨k₀, i'⟩) (F t) = u ^ n * MvPolynomial.aeval (fun i' : J k₀ => w' ⟨k₀, i'⟩) (F t)`. Introduce `t`.

Rewrite using `[← aeval_smul_of_homog (hF t)]`. Use `congr 2`. Use function extensionality and compare the values at `i'`. Conclude with `hu i'`. Establish `hne' : MvPolynomial.aeval (fun i' : J k₀ => w' ⟨k₀, i'⟩) (F c) ≠ 0`.

Introduce `h0`. Conclude with `hne (by rw [hscale, h0, mul_zero])`. Establish `r` using `fun j => relation_at y k₀ k c j (hF j) (hF c) (hrel j) hw`. Establish `r'` using `fun j => relation_at y k₀ k c j (hF j) (hF c) (hrel j) hw'`. Establish `hc' : w' ⟨k, c⟩ ≠ 0`.

Introduce `h0`. Take `⟨j, hj⟩` from `hw'.1 k`. Use `r' j` as an intermediate fact. Rewrite `this` using `[h0, mul_zero]`. Conclude with `(mul_ne_zero hne' hj) this.symm`.

Use `⟨w ⟨k, c⟩ / w' ⟨k, c⟩, div_ne_zero hc hc', fun j => ?_⟩` and prove the remaining obligations. Establish `e1` using `r j`. Establish `e2` using `r' j`. Rewrite `e1` using `[hscale, hscale]`. Establish `hun : u ^ n ≠ 0` using `pow_ne_zero n hu0`.

Establish `e3 : MvPolynomial.aeval (fun i' : J k₀ => w' ⟨k₀, i'⟩) (F j) * w ⟨k, c⟩ = MvPolynomial.aeval (fun i' : J k₀ => w' ⟨k₀, i'⟩) (F c) * w ⟨k, j⟩` using `mul_left_cancel₀ hun (by linear_combination e1)`. Apply `mul_left_cancel₀ hne'` to reduce the goal to its premises. Establish `e4 : w ⟨k, c⟩ / w' ⟨k, c⟩ * w' ⟨k, c⟩ = w ⟨k, c⟩` using `div_mul_cancel₀ _ hc'`. Take the linear combination `(-1 : ℂ) * e3 + (w ⟨k, c⟩ / w' ⟨k, c⟩) * e2 - MvPolynomial.aeval (fun i' : J k₀ => w' ⟨k₀, i'⟩) (F j) * e4`. Use `choose s hs0 hs using key`.

Conclude with `⟨s, hs0, funext fun p => by`. Take `⟨k, j⟩` from `p`. Conclude with `hs k j⟩`.
-/
theorem sameOrbit_of_block : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (k₀ : K), CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → EmbedsGeneric ξ (fun i : J k₀ => y ⟨k₀, i⟩) → ∀ w ∈ mcPts (mCoordIdeal y), ∀ w' ∈ mcPts (mCoordIdeal y), ∀ u : ℂ, (∀ i : J k₀, w ⟨k₀, i⟩ = u * w' ⟨k₀, i⟩) → SameOrbit w w' := by
  intro X Ω _ _ ξ K _ J _ y k₀ hT hE w hw w' hw' u hu
  have hpts : w ∈ Small.ptsOver ℂ (mCoordIdeal y) := by
    refine ⟨hw.1, fun f hf => ?_⟩
    rw [← hw.2 f hf, MvPolynomial.eval_map]
    rfl
  obtain ⟨i, hi⟩ := hw.1 k₀
  have hu0 : u ≠ 0 := by
    rintro rfl
    exact hi (by rw [hu i, zero_mul])
  have key : ∀ k, ∃ s : ℂ, s ≠ 0 ∧ ∀ j, w ⟨k, j⟩ = s * w' ⟨k, j⟩ := by
    intro k
    obtain ⟨c, hc⟩ := hw.1 k
    obtain ⟨n, F, hF, hrel, hne⟩ :=
      GlobalTheory.T.small_points_coord_ratio_bound X Ω ξ K J y k₀ hT hE ℂ w hpts i k c hi hc
    have hscale : ∀ t, MvPolynomial.aeval (fun i' : J k₀ => w ⟨k₀, i'⟩) (F t) =
        u ^ n * MvPolynomial.aeval (fun i' : J k₀ => w' ⟨k₀, i'⟩) (F t) := by
      intro t
      rw [← aeval_smul_of_homog (hF t)]
      congr 2
      funext i'
      exact hu i'
    have hne' : MvPolynomial.aeval (fun i' : J k₀ => w' ⟨k₀, i'⟩) (F c) ≠ 0 := by
      intro h0
      exact hne (by rw [hscale, h0, mul_zero])
    have r := fun j => relation_at y k₀ k c j (hF j) (hF c) (hrel j) hw
    have r' := fun j => relation_at y k₀ k c j (hF j) (hF c) (hrel j) hw'
    have hc' : w' ⟨k, c⟩ ≠ 0 := by
      intro h0
      obtain ⟨j, hj⟩ := hw'.1 k
      have := r' j
      rw [h0, mul_zero] at this
      exact (mul_ne_zero hne' hj) this.symm
    refine ⟨w ⟨k, c⟩ / w' ⟨k, c⟩, div_ne_zero hc hc', fun j => ?_⟩
    have e1 := r j
    have e2 := r' j
    rw [hscale, hscale] at e1
    have hun : u ^ n ≠ 0 := pow_ne_zero n hu0
    have e3 : MvPolynomial.aeval (fun i' : J k₀ => w' ⟨k₀, i'⟩) (F j) * w ⟨k, c⟩ =
        MvPolynomial.aeval (fun i' : J k₀ => w' ⟨k₀, i'⟩) (F c) * w ⟨k, j⟩ :=
      mul_left_cancel₀ hun (by linear_combination e1)
    apply mul_left_cancel₀ hne'
    have e4 : w ⟨k, c⟩ / w' ⟨k, c⟩ * w' ⟨k, c⟩ = w ⟨k, c⟩ := div_mul_cancel₀ _ hc'
    linear_combination (-1 : ℂ) * e3 + (w ⟨k, c⟩ / w' ⟨k, c⟩) * e2 -
      MvPolynomial.aeval (fun i' : J k₀ => w' ⟨k₀, i'⟩) (F j) * e4
  choose s hs0 hs using key
  exact ⟨s, hs0, funext fun p => by
    obtain ⟨k, j⟩ := p
    exact hs k j⟩

end GlobalTheory.CompanionTheory.Ar.OrbitBlock
