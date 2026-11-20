import Mathlib
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.DetDvdEquivariantFramePolynomialStatement
import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.ExistsPrincipalLattice
import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
import Formalism.LocalToGlobal.ProjectiveLattices.L2DefiniteCuspForms
import Formalism.LocalToGlobal.ProjectiveLattices.NonnegIffOfLiesTotal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NonemptyUnitAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.NonvanishingNearMaximum
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

namespace GlobalTheory.LamT

noncomputable def blockDetPoly (K : Type) [CommRing K] {B : Type} (m : B → ℕ) (b : B) :
    MvPolynomial (FrVar m) K :=
  (Matrix.of fun i k : Fin (m b) => (MvPolynomial.X ⟨b, (k, i)⟩ : MvPolynomial (FrVar m) K)).det

/- English proof (translation)
Unfold `evalFr blockDetPoly`. Rewrite using `[RingHom.map_det, RingHom.map_det]`. Use `congr 1`. Use extensionality with `i k`. Simplify using the standard rewrite rules.
-/
theorem evalFr_map_blockDetPoly {K S : Type} [CommRing K] [CommRing S] (φ : K →+* S) {B : Type}
    [Fintype B] (m : B → ℕ) (b : B) (X : ∀ b, Matrix (Fin (m b)) (Fin (m b)) S) :
    evalFr (MvPolynomial.map φ (blockDetPoly K m b)) X = (X b).det := by
  unfold evalFr blockDetPoly
  rw [RingHom.map_det, RingHom.map_det]
  congr 1
  ext i k
  simp

/- English proof (translation)
Use `evalFr_map_blockDetPoly (RingHom.id K) m b X` as an intermediate fact. Rewrite `this` using `[MvPolynomial.map_id]`. Then use the resulting hypothesis.
-/
theorem evalFr_blockDetPoly {K : Type} [CommRing K] {B : Type}
    [Fintype B] (m : B → ℕ) (b : B) (X : ∀ b, Matrix (Fin (m b)) (Fin (m b)) K) :
    evalFr (blockDetPoly K m b) X = (X b).det := by
  have := evalFr_map_blockDetPoly (RingHom.id K) m b X
  rwa [MvPolynomial.map_id] at this

/- English proof (translation)
Proceed by induction on `s with`. Consider the case `zero`. Introduce `n hn P _`. Establish `h0 : ∀ b, n b = 0` using `fun b => (Finset.sum_eq_zero_iff.1 hn) b (Finset.mem_univ b)`. Conclude with `⟨P, by simp [h0]⟩`.

Consider the case `succ s ih`. Introduce `n hn P hP`. Take `⟨b₀, -, hb₀⟩ : ∃ b ∈ (Finset.univ : Finset B), n b ≠ 0` from `Finset.exists_ne_zero_of_sum_ne_zero (by omega)`. Take `⟨Q, hQ⟩` from `GlobalTheory.T.det_dvd_equivariant_framePolynomial K B m P (fun b i => a b i + n b) hP b₀ (fun i => by omega)`. Express the relevant statement in the definitionally equal form `P = blockDetPoly K m b₀ * Q at hQ`.

Use `set n' : B → ℕ := Function.update n b₀ (n b₀ - 1) with hn'`. Establish `hn'0 : n' b₀ + 1 = n b₀` using `by simp only [hn', Function.update_self]; omega`. Establish `hn'1 : ∀ b, b ≠ b₀ → n' b = n b` using `fun b hb => by`. Simplify using `only [hn', Function.update_of_ne hb]`. Establish `hsum : ∑ b, n' b = s`.

Rewrite `hn`, the goal using `[← Finset.add_sum_erase _ _ (Finset.mem_univ b₀)]`. Establish `: ∑ b ∈ Finset.univ.erase b₀, n' b = ∑ b ∈ Finset.univ.erase b₀, n b` using `Finset.sum_congr rfl fun b hb => hn'1 b (Finset.ne_of_mem_erase hb)`. Use linear arithmetic over natural numbers and integers. Establish `hev : ∀ X : ∀ b, Matrix (Fin (m b)) (Fin (m b)) K, evalFr P X = (X b₀).det * evalFr Q X` using `fun X => by`. Rewrite using `[← evalFr_blockDetPoly m b₀ X, hQ]`.

Simplify using `only [evalFr, map_mul]`. Take `⟨G, hG⟩` from `ih n' hsum Q (by`. Introduce `X b t hX ht htri`. Establish `h` using `hP X b t hX ht htri`. Rewrite `h` using `[hev, hev]`.

Distinguish the cases in `hb : b = b₀`. Substitute `hb` using the available equality. Rewrite `h` using `[Function.update_self, Matrix.det_mul]`. Establish `hd : t.det = ∏ i, t i i` using `Matrix.det_of_upperTriangular htri`. Establish `hp : (∏ i, t i i ^ (a b i + n b)) = t.det * ∏ i, t i i ^ (a b i + n' b)`.

Rewrite using `[hd, ← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← hn'0]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `h` using `[hp]`.

Apply `mul_left_cancel₀ (mul_ne_zero (hX b) ht)` to reduce the goal to its premises. Rewrite using `[h]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `h` using `[Function.update_of_ne (Ne.symm hb)]`. Rewrite using `[hn'1 b hb]`.

Apply `mul_left_cancel₀ (hX b₀)` to reduce the goal to its premises. Rewrite using `[h]`. Use the proof step `ring)`. Use `⟨G, ?_⟩` and prove the remaining obligations. Rewrite using `[hQ, hG, ← Finset.mul_prod_erase _ _ (Finset.mem_univ b₀), ← Finset.mul_prod_erase _ (fun b => blockDetPoly K m b ^ n b) (Finset.mem_univ b₀)]`.

Establish `: ∏ b ∈ Finset.univ.erase b₀, blockDetPoly K m b ^ n' b = ∏ b ∈ Finset.univ.erase b₀, blockDetPoly K m b ^ n b` using `Finset.prod_congr rfl fun b hb => by rw [hn'1 b (Finset.ne_of_mem_erase hb)]`. Rewrite using `[this, ← hn'0]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_eq_prod_blockDetPoly_pow_mul (K : Type) [Field K] [Infinite K] (B : Type) [Fintype B]
    [DecidableEq B] (m : B → ℕ) (a : ∀ b, Fin (m b) → ℕ) (s : ℕ) :
    ∀ (n : B → ℕ), ∑ b, n b = s → ∀ (P : MvPolynomial (FrVar m) K),
      (∀ (X : ∀ b, Matrix (Fin (m b)) (Fin (m b)) K) (b : B) (t : Matrix (Fin (m b)) (Fin (m b)) K),
        (∀ b', (X b').det ≠ 0) → t.det ≠ 0 → t.BlockTriangular id →
        evalFr P (Function.update X b (X b * t)) = (∏ i, t i i ^ (a b i + n b)) * evalFr P X) →
      ∃ G : MvPolynomial (FrVar m) K, P = (∏ b, blockDetPoly K m b ^ n b) * G := by
  induction s with
  | zero =>
    intro n hn P _
    have h0 : ∀ b, n b = 0 := fun b =>
      (Finset.sum_eq_zero_iff.1 hn) b (Finset.mem_univ b)
    exact ⟨P, by simp [h0]⟩
  | succ s ih =>
    intro n hn P hP
    obtain ⟨b₀, -, hb₀⟩ : ∃ b ∈ (Finset.univ : Finset B), n b ≠ 0 :=
      Finset.exists_ne_zero_of_sum_ne_zero (by omega)
    obtain ⟨Q, hQ⟩ := GlobalTheory.T.det_dvd_equivariant_framePolynomial K B m P (fun b i => a b i + n b) hP b₀ (fun i => by omega)
    change P = blockDetPoly K m b₀ * Q at hQ
    set n' : B → ℕ := Function.update n b₀ (n b₀ - 1) with hn'
    have hn'0 : n' b₀ + 1 = n b₀ := by simp only [hn', Function.update_self]; omega
    have hn'1 : ∀ b, b ≠ b₀ → n' b = n b := fun b hb => by
      simp only [hn', Function.update_of_ne hb]
    have hsum : ∑ b, n' b = s := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ b₀)] at hn ⊢
      have : ∑ b ∈ Finset.univ.erase b₀, n' b = ∑ b ∈ Finset.univ.erase b₀, n b :=
        Finset.sum_congr rfl fun b hb => hn'1 b (Finset.ne_of_mem_erase hb)
      omega
    have hev : ∀ X : ∀ b, Matrix (Fin (m b)) (Fin (m b)) K,
        evalFr P X = (X b₀).det * evalFr Q X := fun X => by
      rw [← evalFr_blockDetPoly m b₀ X, hQ]
      simp only [evalFr, map_mul]
    obtain ⟨G, hG⟩ := ih n' hsum Q (by
      intro X b t hX ht htri
      have h := hP X b t hX ht htri
      rw [hev, hev] at h
      by_cases hb : b = b₀
      · subst hb
        rw [Function.update_self, Matrix.det_mul] at h
        have hd : t.det = ∏ i, t i i := Matrix.det_of_upperTriangular htri
        have hp : (∏ i, t i i ^ (a b i + n b)) = t.det * ∏ i, t i i ^ (a b i + n' b) := by
          rw [hd, ← Finset.prod_mul_distrib]
          refine Finset.prod_congr rfl fun i _ => ?_
          rw [← hn'0]; ring
        rw [hp] at h
        apply mul_left_cancel₀ (mul_ne_zero (hX b) ht)
        rw [h]; ring
      · rw [Function.update_of_ne (Ne.symm hb)] at h
        rw [hn'1 b hb]
        apply mul_left_cancel₀ (hX b₀)
        rw [h]; ring)
    refine ⟨G, ?_⟩
    rw [hQ, hG, ← Finset.mul_prod_erase _ _ (Finset.mem_univ b₀),
      ← Finset.mul_prod_erase _ (fun b => blockDetPoly K m b ^ n b) (Finset.mem_univ b₀)]
    have : ∏ b ∈ Finset.univ.erase b₀, blockDetPoly K m b ^ n' b
        = ∏ b ∈ Finset.univ.erase b₀, blockDetPoly K m b ^ n b :=
      Finset.prod_congr rfl fun b hb => by rw [hn'1 b (Finset.ne_of_mem_erase hb)]
    rw [this, ← hn'0]; ring

/- English proof (translation)
Introduce `K _ _ B _ _ m P a N hP`. Take `⟨G, hG⟩` from `exists_eq_prod_blockDetPoly_pow_mul K B m a _ (fun _ => N) rfl P hP`. Use `⟨G, fun S _ φ X => ?_⟩` and prove the remaining obligations. Rewrite using `[hG, ← Finset.prod_pow]`. Simplify using `only [← evalFr_map_blockDetPoly φ m _ X]`.

Simplify using `only [evalFr, map_mul, map_prod, map_pow]`.
-/
theorem evalFr_eq_prod_det_pow_mul : ∀ (K : Type) [Field K] [Infinite K] (B : Type) [Fintype B] [DecidableEq B] (m : B → ℕ) (P : MvPolynomial (FrVar m) K) (a : ∀ b, Fin (m b) → ℕ) (N : ℕ), (∀ (X : ∀ b, Matrix (Fin (m b)) (Fin (m b)) K) (b : B) (t : Matrix (Fin (m b)) (Fin (m b)) K), (∀ b', (X b').det ≠ 0) → t.det ≠ 0 → t.BlockTriangular id → evalFr P (Function.update X b (X b * t)) = (∏ i, t i i ^ (a b i + N)) * evalFr P X) → ∃ G : MvPolynomial (FrVar m) K, ∀ (S : Type) [CommRing S] (φ : K →+* S) (X : ∀ b, Matrix (Fin (m b)) (Fin (m b)) S), evalFr (MvPolynomial.map φ P) X = (∏ b, (X b).det) ^ N * evalFr (MvPolynomial.map φ G) X := by
  intro K _ _ B _ _ m P a N hP
  obtain ⟨G, hG⟩ := exists_eq_prod_blockDetPoly_pow_mul K B m a _ (fun _ => N) rfl P hP
  refine ⟨G, fun S _ φ X => ?_⟩
  rw [hG, ← Finset.prod_pow]
  simp only [← evalFr_map_blockDetPoly φ m _ X]
  simp only [evalFr, map_mul, map_prod, map_pow]

end GlobalTheory.LamT
