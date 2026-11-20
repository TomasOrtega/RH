import Mathlib
import Formalism.HermitianLattices.GenusCovolBound
import Formalism.HermitianLattices.HermitianLatticesProofs.GenusScale
import Formalism.HermitianLattices.HermitianLatticesProofs.LocDual
import Formalism.HermitianLattices.HermitianLatticesProofs.DualLattice
import Formalism.HermitianLattices.HermitianLatticesProofs.IsomAct
import Formalism.FockGram.FockGramProofs.CovolGram

open Module NumberField

noncomputable section

namespace Formalism.HermitianLatticesTheory

section PartA

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

/- English proof (translation)
Conclude with `Iff.rfl`.
-/
theorem genusCovolBound_mem_zmap (N : ℕ) (ι : V →+ EuclideanSpace ℝ (Fin N))
    (M : Submodule (𝓞 K) V) (v : EuclideanSpace ℝ (Fin N)) :
    v ∈ zmap ι M ↔ ∃ x ∈ M, ι x = v := by
  exact Iff.rfl

/- English proof (translation)
Use `set Λ := zmap ι M with hΛdef`. Set `n` to `Module.Free.ChooseBasisIndex ℤ Λ`. Set `bZ : Module.Basis n ℤ Λ` to `Module.Free.chooseBasis ℤ Λ`. Set `b : Module.Basis n ℝ (EuclideanSpace ℝ (Fin N))` to `bZ.ofZLatticeBasis ℝ Λ`. Establish `hb : ∀ i, b i = (bZ i : EuclideanSpace ℝ (Fin N))` using `fun i => Module.Basis.ofZLatticeBasis_apply ℝ Λ bZ i`.

Establish `hspan : Submodule.span ℤ (Set.range b) = Λ` using `Module.Basis.ofZLatticeBasis_span ℝ Λ bZ`. Establish `hcard : Fintype.card n = N`. Rewrite using `[← Module.finrank_eq_card_basis b, finrank_euclideanSpace_fin]`. Establish `hpre : ∀ i, ∃ x ∈ M, ι x = b i`. Introduce `i`.

Establish `hi : b i ∈ Λ` using `by rw [hb]; exact (bZ i).2`. Conclude with `(genusCovolBound_mem_zmap N ι M (b i)).mp hi`. Use `choose x hxM hxb using hpre`. Set `Gq : Matrix n n ℚ` to `Matrix.of fun i j => Algebra.trace ℚ K (h (x i) (x j))`. Establish `e1 : ∀ i k, inner ℝ (b i) (b k) = ((Gq i k : ℚ) : ℝ)` using `fun i k => by`.

Rewrite using `[← hxb i, ← hxb k, hι]`. Both sides reduce to the same expression. Establish `hG : Matrix.gram ℝ b = (Rat.castHom ℝ).mapMatrix Gq`. Use extensionality with `i j`. Rewrite using `[Matrix.gram_apply, e1]`.

Both sides reduce to the same expression. Establish `hdetG : 0 < (Matrix.gram ℝ b).det` using `(Matrix.posDef_gram_of_linearIndependent b.linearIndependent).det_pos`. Establish `hdetq : ((Gq.det : ℚ) : ℝ) = (Matrix.gram ℝ b).det`. Rewrite using `[hG, ← RingHom.map_det]`. Both sides reduce to the same expression.

Establish `hdq0 : 0 < Gq.det`. Establish `: (0 : ℝ) < (Gq.det : ℝ)` using `by rw [hdetq]; exact hdetG`. Conclude with `this` after adjusting the coercions. Set `Hq` to `Gq⁻¹`. Establish `hGH : Gq * Hq = 1` using `Matrix.mul_nonsing_inv Gq (isUnit_iff_ne_zero.mpr hdq0.ne')`.

Set `w : n → EuclideanSpace ℝ (Fin N)` to `fun j => ∑ k, ((Hq k j : ℚ) : ℝ) • b k`. Set `y : n → V` to `fun j => ∑ k, ((Hq k j : ℚ) : K) • x k`. Establish `hy : ∀ j, ι (y j) = w j`. Introduce `j`. Simplify using `only [y, w, map_sum]`.

Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[map_ratCast_smul ι K ℝ, hxb]`. Establish `hbw : ∀ i j, inner ℝ (b i) (w j) = (((1 : Matrix n n ℚ) i j : ℚ) : ℝ)`. Introduce `i j`. Establish `hw : w j = ∑ k, ((Hq k j : ℚ) : ℝ) • b k` using `rfl`.

Rewrite using `[hw, inner_sum, ← hGH, Matrix.mul_apply]`. Use `push_cast`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[inner_smul_right, e1]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hint : ∀ v ∈ Λ, ∀ j, ∃ z : ℤ, inner ℝ v (w j) = z`. Introduce `v hv j`. Rewrite `hv` using `[← hspan]`. Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem v hv`.

Take `⟨i, rfl⟩` from `hv`. Rewrite using `[hbw, Matrix.one_apply]`. Use `split_ifs`. Conclude with `⟨1, by simp⟩`. Conclude with `⟨0, by simp⟩`.

Consider the case `zero => exact ⟨0, by simp⟩`. Consider the case `add u v _ _ hu hv`. Take `⟨a, ha⟩` from `hu`. Take `⟨c, hc⟩` from `hv`. Conclude with `⟨a + c, by rw [inner_add_left, ha, hc]; push_cast; ring⟩`.

Consider the case `smul a u _ hu`. Take `⟨c, hc⟩` from `hu`. Conclude with `⟨a * c, by rw [← Int.cast_smul_eq_zsmul ℝ, real_inner_smul_left, hc]; push_cast; ring⟩`. Establish `hyd : ∀ j, ∀ x' ∈ M, ∃ z : ℤ, Algebra.trace ℚ K (h x' (y j)) = z`. Introduce `j x' hx'`.

Take `⟨z, hz⟩` from `hint (ι x') ((genusCovolBound_mem_zmap N ι M _).mpr ⟨x', hx', rfl⟩) j`. Use `⟨z, ?_⟩` and prove the remaining obligations. Rewrite `hz` using `[← hy j, hι]`. Conclude with `hz` after adjusting the coercions. Establish `hww : ∀ i j, inner ℝ (w i) (w j) = ((Hq j i : ℚ) : ℝ)`.

Introduce `i j`. Establish `hw : w i = ∑ k, ((Hq k i : ℚ) : ℝ) • b k` using `rfl`. Rewrite using `[hw, sum_inner, Finset.sum_eq_single j]`. Rewrite using `[real_inner_smul_left, hbw, Matrix.one_apply_eq]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Introduce `k _ hk`. Rewrite using `[real_inner_smul_left, hbw, Matrix.one_apply_ne hk]`. Simplify using the standard rewrite rules. Introduce `hj`.

Conclude with `absurd (Finset.mem_univ j) hj`. Establish `hZ : ∀ i j, ∃ z : ℤ, (D : ℚ) * Hq j i = z`. Introduce `i j`. Take `⟨z, hz⟩` from `hD (y i) (y j) (hyd i) (hyd j)`. Use `⟨z, ?_⟩` and prove the remaining obligations.

Establish `e : ((Algebra.trace ℚ K (h (y i) (y j)) : ℚ) : ℝ) = ((Hq j i : ℚ) : ℝ)`. Rewrite using `[← hι, hy, hy, hww]`. Establish `e' : Algebra.trace ℚ K (h (y i) (y j)) = Hq j i` using `by exact_mod_cast e`. Rewrite using `[← e', hz]`. Use `choose Z hZ' using hZ`.

Establish `hZm : (Int.castRingHom ℚ).mapMatrix (Matrix.of Z) = (D : ℚ) • Hq.transpose`. Use extensionality with `i j`. Simplify using `[hZ']`. Establish `hdetZ : (((Matrix.of Z).det : ℤ) : ℚ) = (D : ℚ) ^ N * (Gq.det)⁻¹`. Use `RingHom.map_det (Int.castRingHom ℚ) (Matrix.of Z)` as an intermediate fact.

Rewrite `this` using `[hZm, Matrix.det_smul, Matrix.det_transpose, Matrix.det_nonsing_inv, hcard, Ring.inverse_eq_inv']`. Simplify using `using this`. Establish `hpos : (0 : ℚ) < (((Matrix.of Z).det : ℤ) : ℚ)` using `by rw [hdetZ]; positivity`. Establish `h1 : (1 : ℚ) ≤ (((Matrix.of Z).det : ℤ) : ℚ)`. Establish `h0 : 0 < (Matrix.of Z).det` using `by exact_mod_cast hpos`.

Establish `h1' : (1 : ℤ) ≤ (Matrix.of Z).det` using `by omega`. Conclude with `h1'` after adjusting the coercions. Establish `hq : Gq.det ≤ (D : ℚ) ^ N`. Rewrite `h1` using `[hdetZ]`. Use `mul_le_mul_of_nonneg_right h1 hdq0.le` as an intermediate fact.

Rewrite `this` using `[mul_assoc, inv_mul_cancel₀ hdq0.ne', mul_one, one_mul]`. Then use the resulting hypothesis. Establish `hle : (Matrix.gram ℝ b).det ≤ (D : ℝ) ^ N`. Rewrite using `[← hdetq]`. Conclude with `hq` after adjusting the coercions. Establish `hcg` using `Formalism.E.covolumeEqSqrtDetGram (EuclideanSpace ℝ (Fin N)) n b`.

Rewrite `hcg` using `[hspan]`. Rewrite using `[hcg]`. Conclude with `Real.sqrt_le_sqrt hle`.
-/
theorem genusCovolBound_covol_le (h : V →ₗ⋆[K] V →ₗ[K] K) (N : ℕ)
    (ι : V →+ EuclideanSpace ℝ (Fin N))
    (hι : ∀ x y : V, inner ℝ (ι x) (ι y) = ((Algebra.trace ℚ K (h x y) : ℚ) : ℝ))
    (M : Submodule (𝓞 K) V) [DiscreteTopology (zmap ι M)] [IsZLattice ℝ (zmap ι M)]
    (D : ℕ) (hD0 : 0 < D)
    (hD : ∀ y y' : V, (∀ x ∈ M, ∃ z : ℤ, Algebra.trace ℚ K (h x y) = z) →
       (∀ x ∈ M, ∃ z : ℤ, Algebra.trace ℚ K (h x y') = z) →
       ∃ z : ℤ, (D : ℚ) * Algebra.trace ℚ K (h y y') = z) :
    ZLattice.covolume (zmap ι M) ≤ Real.sqrt ((D : ℝ) ^ N) := by
  classical
  set Λ := zmap ι M with hΛdef

  let n := Module.Free.ChooseBasisIndex ℤ Λ
  let bZ : Module.Basis n ℤ Λ := Module.Free.chooseBasis ℤ Λ
  let b : Module.Basis n ℝ (EuclideanSpace ℝ (Fin N)) := bZ.ofZLatticeBasis ℝ Λ
  have hb : ∀ i, b i = (bZ i : EuclideanSpace ℝ (Fin N)) := fun i =>
    Module.Basis.ofZLatticeBasis_apply ℝ Λ bZ i
  have hspan : Submodule.span ℤ (Set.range b) = Λ := Module.Basis.ofZLatticeBasis_span ℝ Λ bZ
  have hcard : Fintype.card n = N := by
    rw [← Module.finrank_eq_card_basis b, finrank_euclideanSpace_fin]
  have hpre : ∀ i, ∃ x ∈ M, ι x = b i := by
    intro i
    have hi : b i ∈ Λ := by rw [hb]; exact (bZ i).2
    exact (genusCovolBound_mem_zmap N ι M (b i)).mp hi
  choose x hxM hxb using hpre
  let Gq : Matrix n n ℚ := Matrix.of fun i j => Algebra.trace ℚ K (h (x i) (x j))
  have e1 : ∀ i k, inner ℝ (b i) (b k) = ((Gq i k : ℚ) : ℝ) := fun i k => by
    rw [← hxb i, ← hxb k, hι]
    rfl
  have hG : Matrix.gram ℝ b = (Rat.castHom ℝ).mapMatrix Gq := by
    ext i j
    rw [Matrix.gram_apply, e1]
    rfl
  have hdetG : 0 < (Matrix.gram ℝ b).det :=
    (Matrix.posDef_gram_of_linearIndependent b.linearIndependent).det_pos
  have hdetq : ((Gq.det : ℚ) : ℝ) = (Matrix.gram ℝ b).det := by
    rw [hG, ← RingHom.map_det]
    rfl
  have hdq0 : 0 < Gq.det := by
    have : (0 : ℝ) < (Gq.det : ℝ) := by rw [hdetq]; exact hdetG
    exact_mod_cast this
  let Hq := Gq⁻¹
  have hGH : Gq * Hq = 1 := Matrix.mul_nonsing_inv Gq (isUnit_iff_ne_zero.mpr hdq0.ne')

  let w : n → EuclideanSpace ℝ (Fin N) := fun j => ∑ k, ((Hq k j : ℚ) : ℝ) • b k
  let y : n → V := fun j => ∑ k, ((Hq k j : ℚ) : K) • x k
  have hy : ∀ j, ι (y j) = w j := by
    intro j
    simp only [y, w, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_ratCast_smul ι K ℝ, hxb]
  have hbw : ∀ i j, inner ℝ (b i) (w j) = (((1 : Matrix n n ℚ) i j : ℚ) : ℝ) := by
    intro i j
    have hw : w j = ∑ k, ((Hq k j : ℚ) : ℝ) • b k := rfl
    rw [hw, inner_sum, ← hGH, Matrix.mul_apply]
    push_cast
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [inner_smul_right, e1]
    ring
  have hint : ∀ v ∈ Λ, ∀ j, ∃ z : ℤ, inner ℝ v (w j) = z := by
    intro v hv j
    rw [← hspan] at hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨i, rfl⟩ := hv
      rw [hbw, Matrix.one_apply]
      split_ifs
      · exact ⟨1, by simp⟩
      · exact ⟨0, by simp⟩
    | zero => exact ⟨0, by simp⟩
    | add u v _ _ hu hv =>
      obtain ⟨a, ha⟩ := hu
      obtain ⟨c, hc⟩ := hv
      exact ⟨a + c, by rw [inner_add_left, ha, hc]; push_cast; ring⟩
    | smul a u _ hu =>
      obtain ⟨c, hc⟩ := hu
      exact ⟨a * c, by rw [← Int.cast_smul_eq_zsmul ℝ, real_inner_smul_left, hc]; push_cast; ring⟩
  have hyd : ∀ j, ∀ x' ∈ M, ∃ z : ℤ, Algebra.trace ℚ K (h x' (y j)) = z := by
    intro j x' hx'
    obtain ⟨z, hz⟩ := hint (ι x') ((genusCovolBound_mem_zmap N ι M _).mpr ⟨x', hx', rfl⟩) j
    refine ⟨z, ?_⟩
    rw [← hy j, hι] at hz
    exact_mod_cast hz
  have hww : ∀ i j, inner ℝ (w i) (w j) = ((Hq j i : ℚ) : ℝ) := by
    intro i j
    have hw : w i = ∑ k, ((Hq k i : ℚ) : ℝ) • b k := rfl
    rw [hw, sum_inner, Finset.sum_eq_single j]
    · rw [real_inner_smul_left, hbw, Matrix.one_apply_eq]
      push_cast
      ring
    · intro k _ hk
      rw [real_inner_smul_left, hbw, Matrix.one_apply_ne hk]
      simp
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  have hZ : ∀ i j, ∃ z : ℤ, (D : ℚ) * Hq j i = z := by
    intro i j
    obtain ⟨z, hz⟩ := hD (y i) (y j) (hyd i) (hyd j)
    refine ⟨z, ?_⟩
    have e : ((Algebra.trace ℚ K (h (y i) (y j)) : ℚ) : ℝ) = ((Hq j i : ℚ) : ℝ) := by
      rw [← hι, hy, hy, hww]
    have e' : Algebra.trace ℚ K (h (y i) (y j)) = Hq j i := by exact_mod_cast e
    rw [← e', hz]
  choose Z hZ' using hZ
  have hZm : (Int.castRingHom ℚ).mapMatrix (Matrix.of Z) = (D : ℚ) • Hq.transpose := by
    ext i j
    simp [hZ']
  have hdetZ : (((Matrix.of Z).det : ℤ) : ℚ) = (D : ℚ) ^ N * (Gq.det)⁻¹ := by
    have := RingHom.map_det (Int.castRingHom ℚ) (Matrix.of Z)
    rw [hZm, Matrix.det_smul, Matrix.det_transpose, Matrix.det_nonsing_inv, hcard,
      Ring.inverse_eq_inv'] at this
    simpa using this
  have hpos : (0 : ℚ) < (((Matrix.of Z).det : ℤ) : ℚ) := by rw [hdetZ]; positivity
  have h1 : (1 : ℚ) ≤ (((Matrix.of Z).det : ℤ) : ℚ) := by
    have h0 : 0 < (Matrix.of Z).det := by exact_mod_cast hpos
    have h1' : (1 : ℤ) ≤ (Matrix.of Z).det := by omega
    exact_mod_cast h1'
  have hq : Gq.det ≤ (D : ℚ) ^ N := by
    rw [hdetZ] at h1
    have := mul_le_mul_of_nonneg_right h1 hdq0.le
    rwa [mul_assoc, inv_mul_cancel₀ hdq0.ne', mul_one, one_mul] at this
  have hle : (Matrix.gram ℝ b).det ≤ (D : ℝ) ^ N := by
    rw [← hdetq]
    exact_mod_cast hq
  have hcg := Formalism.E.covolumeEqSqrtDetGram (EuclideanSpace ℝ (Fin N)) n b
  rw [hspan] at hcg
  rw [hcg]
  exact Real.sqrt_le_sqrt hle

end PartA

section PartB

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

/- English proof (translation)
Use extensionality with `x`. Simplify using `only [dualAt, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.coe_restrictScalars, isomAct_mem_gmap]`. Prove the components needed by the constructor for the conclusion. Introduce `H z hz`. Use `H (g z) (by simpa using hz)` as an intermediate fact.

Rewrite using `[show h (g z) x = h z (g.symm x) by conv_lhs => rw [show x = g (g.symm x) by simp]` and apply the resulting hypothesis. Conclude with `hg z (g.symm x)] at this`. Introduce `H y hy`. Use `H (g.symm y) hy` as an intermediate fact. Rewrite using `[show h (g.symm y) (g.symm x) = h y x by conv_rhs => rw [show y = g (g.symm y) by simp, show x = g (g.symm x) by simp]` and apply the resulting hypothesis.

Conclude with `(hg (g.symm y) (g.symm x)).symm] at this`.
-/
theorem genusCovolBound_dualAt_gmap (h : V →ₗ⋆[K] V →ₗ[K] K) (g : V ≃ₗ[K] V) (hg : g ∈ isom h)
    (p : Ideal (𝓞 K)) (X : Submodule (𝓞 K) V) :
    dualAt h p (gmap g X) = gmap g (dualAt h p X) := by
  ext x
  simp only [dualAt, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.coe_restrictScalars,
    isomAct_mem_gmap]
  constructor
  · intro H z hz
    have := H (g z) (by simpa using hz)
    rwa [show h (g z) x = h z (g.symm x) by
      conv_lhs => rw [show x = g (g.symm x) by simp]
      exact hg z (g.symm x)] at this
  · intro H y hy
    have := H (g.symm y) hy
    rwa [show h (g.symm y) (g.symm x) = h y x by
      conv_rhs => rw [show y = g (g.symm y) by simp, show x = g (g.symm x) by simp]
      exact (hg (g.symm y) (g.symm x)).symm] at this

/- English proof (translation)
Take `⟨hMl, hMg⟩` from `hM`. Use `⟨(dualLattice (𝓞 K) K V h hs hnd hstar M hMl).1, ?_⟩` and prove the remaining obligations. Introduce `p hp`. Take `⟨g, hg, hgL⟩` from `hMg p hp`. Use `⟨g, hg, ?_⟩` and prove the remaining obligations.

Establish `hL1` using `(locDual (𝓞 K) K V h hs hstar L hL.fg).1 p hp.isPrime`. Establish `hM1` using `(locDual (𝓞 K) K V h hs hstar M hMl.fg).1 p hp.isPrime`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem genusCovolBound_dual_genus [FiniteDimensional K V] (h : V →ₗ⋆[K] V →ₗ[K] K)
    (hs : h.IsSymm) (hnd : h.Nondegenerate)
    (hstar : ∀ r : 𝓞 K, star (algebraMap (𝓞 K) K r) ∈ Set.range (algebraMap (𝓞 K) K))
    (L : Submodule (𝓞 K) V) (hL : Submodule.IsLattice K L) (M : Submodule (𝓞 K) V)
    (hM : M ∈ genus h L) : dual h M ∈ genus h (dual h L) := by
  obtain ⟨hMl, hMg⟩ := hM
  refine ⟨(dualLattice (𝓞 K) K V h hs hnd hstar M hMl).1, ?_⟩
  intro p hp
  obtain ⟨g, hg, hgL⟩ := hMg p hp
  refine ⟨g, hg, ?_⟩
  have hL1 := (locDual (𝓞 K) K V h hs hstar L hL.fg).1 p hp.isPrime
  have hM1 := (locDual (𝓞 K) K V h hs hstar M hMl.fg).1 p hp.isPrime
  calc gmap g (loc (K := K) p (dual h L))
      = gmap g (dualAt h p (loc (K := K) p L)) := by rw [hL1.1, hL1.2]
    _ = dualAt h p (gmap g (loc (K := K) p L)) :=
        (genusCovolBound_dualAt_gmap h g hg p _).symm
    _ = dualAt h p (loc (K := K) p M) := by rw [hgL]
    _ = loc (K := K) p (dual h M) := by rw [hM1.2, hM1.1]

/- English proof (translation)
Establish `htr : ∀ r : 𝓞 K, ∃ z : ℤ, Algebra.trace ℚ K (algebraMap (𝓞 K) K r) = z`. Introduce `r`. Establish `hi : IsIntegral ℤ (Algebra.trace ℚ K (algebraMap (𝓞 K) K r))` using `Algebra.isIntegral_trace (RingOfIntegers.isIntegral_coe r)`. Take `⟨z, hz⟩` from `IsIntegrallyClosed.isIntegral_iff.mp hi`. Conclude with `⟨z, by rw [← hz]; simp⟩`.

Establish `hint : ∀ i j, ∃ z : ℤ, Algebra.trace ℚ K (NumberField.integralBasis K i * NumberField.integralBasis K j) = z`. Introduce `i j`. Simplify `htr (RingOfIntegers.basis K i * RingOfIntegers.basis K j)` using `[NumberField.integralBasis_apply, map_mul]`. Use `choose T hT using hint`. Establish `hm : ∀ i, ∃ z : ℤ, Algebra.trace ℚ K (a * NumberField.integralBasis K i) = z`.

Introduce `i`. Simplify `ha (RingOfIntegers.basis K i)` using `[NumberField.integralBasis_apply]`. Use `choose m hm' using hm`. Set `Tq : Matrix _ _ ℚ` to `(Int.castRingHom ℚ).mapMatrix (Matrix.of T)`. Establish `hTq : Matrix.mulVec Tq ((NumberField.integralBasis K).repr a) = fun i => (m i : ℚ)`.

Use function extensionality and compare the values at `i`. Establish `hs : Algebra.trace ℚ K (a * NumberField.integralBasis K i) = ∑ j, (NumberField.integralBasis K).repr a j * Algebra.trace ℚ K (NumberField.integralBasis K i * NumberField.integralBasis K j)` using `by conv_lhs => rw [← (NumberField.integralBasis K).sum_repr a]`. Rewrite using `[Finset.sum_mul, map_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[smul_mul_assoc, LinearMap.map_smul, smul_eq_mul, mul_comm (NumberField.integralBasis K j)]`.

Rewrite using `[← hm' i, hs]`. Simplify using `only [Matrix.mulVec, dotProduct, Tq, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, eq_intCast]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[← hT i j, mul_comm]`. Establish `hdet : ((NumberField.discr K : ℤ) : ℚ) = Tq.det`.

Rewrite using `[NumberField.coe_discr, Algebra.discr_def]`. Use `congr 1`. Use extensionality with `i j`. Simplify using `only [Algebra.traceMatrix_apply, Algebra.traceForm_apply, Tq, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, eq_intCast, hT]`. Establish `hn : ∀ i, ((NumberField.discr K : ℤ) : ℚ) * (NumberField.integralBasis K).repr a i = (Matrix.mulVec (Matrix.of T).adjugate m i : ℤ)`.

Introduce `i`. Establish `h2 : Matrix.mulVec Tq.adjugate (Matrix.mulVec Tq ((NumberField.integralBasis K).repr a)) = Matrix.mulVec Tq.adjugate (fun i => (m i : ℚ))` using `by rw [hTq]`. Rewrite `h2` using `[Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]`. Establish `h3` using `congrFun h2 i`. Rewrite `h3` using `[Pi.smul_apply, smul_eq_mul, ← hdet]`.

Rewrite using `[h3, show Tq.adjugate = (Int.castRingHom ℚ).mapMatrix (Matrix.of T).adjugate from (RingHom.map_adjugate _ _).symm]`. Simplify using `only [Matrix.mulVec, dotProduct, RingHom.mapMatrix_apply, Matrix.map_apply]`. Use `push_cast`. Both sides reduce to the same expression. Rewrite using `[Submodule.mem_one]`.

Use `⟨∑ i, Matrix.mulVec (Matrix.of T).adjugate m i • RingOfIntegers.basis K i, ?_⟩` and prove the remaining obligations. Rewrite using `[map_sum]`. Use `conv_rhs => rw [← (NumberField.integralBasis K).sum_repr a, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_zsmul, zsmul_eq_mul, ← NumberField.integralBasis_apply, Rat.smul_def]`.

Use `congrArg (fun q : ℚ => (q : K)) (hn i)` as an intermediate fact. Move the coercions through the operations in `at this`. Rewrite using `[← this]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem genusCovolBound_discr (a : K)
    (ha : ∀ r : 𝓞 K, ∃ z : ℤ, Algebra.trace ℚ K (a * algebraMap (𝓞 K) K r) = z) :
    ((NumberField.discr K : ℤ) : K) * a ∈ (1 : Submodule (𝓞 K) K) := by
  classical
  have htr : ∀ r : 𝓞 K, ∃ z : ℤ, Algebra.trace ℚ K (algebraMap (𝓞 K) K r) = z := by
    intro r
    have hi : IsIntegral ℤ (Algebra.trace ℚ K (algebraMap (𝓞 K) K r)) :=
      Algebra.isIntegral_trace (RingOfIntegers.isIntegral_coe r)
    obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.mp hi
    exact ⟨z, by rw [← hz]; simp⟩
  have hint : ∀ i j, ∃ z : ℤ, Algebra.trace ℚ K
      (NumberField.integralBasis K i * NumberField.integralBasis K j) = z := by
    intro i j
    simpa [NumberField.integralBasis_apply, map_mul] using
      htr (RingOfIntegers.basis K i * RingOfIntegers.basis K j)
  choose T hT using hint
  have hm : ∀ i, ∃ z : ℤ, Algebra.trace ℚ K (a * NumberField.integralBasis K i) = z := by
    intro i
    simpa [NumberField.integralBasis_apply] using ha (RingOfIntegers.basis K i)
  choose m hm' using hm

  let Tq : Matrix _ _ ℚ := (Int.castRingHom ℚ).mapMatrix (Matrix.of T)
  have hTq : Matrix.mulVec Tq ((NumberField.integralBasis K).repr a) = fun i => (m i : ℚ) := by
    funext i
    have hs : Algebra.trace ℚ K (a * NumberField.integralBasis K i) =
        ∑ j, (NumberField.integralBasis K).repr a j *
          Algebra.trace ℚ K (NumberField.integralBasis K i * NumberField.integralBasis K j) := by
      conv_lhs => rw [← (NumberField.integralBasis K).sum_repr a]
      rw [Finset.sum_mul, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [smul_mul_assoc, LinearMap.map_smul, smul_eq_mul,
        mul_comm (NumberField.integralBasis K j)]
    rw [← hm' i, hs]
    simp only [Matrix.mulVec, dotProduct, Tq, RingHom.mapMatrix_apply, Matrix.map_apply,
      Matrix.of_apply, eq_intCast]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← hT i j, mul_comm]
  have hdet : ((NumberField.discr K : ℤ) : ℚ) = Tq.det := by
    rw [NumberField.coe_discr, Algebra.discr_def]
    congr 1
    ext i j
    simp only [Algebra.traceMatrix_apply, Algebra.traceForm_apply, Tq, RingHom.mapMatrix_apply,
      Matrix.map_apply, Matrix.of_apply, eq_intCast, hT]
  have hn : ∀ i, ((NumberField.discr K : ℤ) : ℚ) * (NumberField.integralBasis K).repr a i =
      (Matrix.mulVec (Matrix.of T).adjugate m i : ℤ) := by
    intro i
    have h2 : Matrix.mulVec Tq.adjugate (Matrix.mulVec Tq ((NumberField.integralBasis K).repr a)) =
        Matrix.mulVec Tq.adjugate (fun i => (m i : ℚ)) := by rw [hTq]
    rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec,
      Matrix.one_mulVec] at h2
    have h3 := congrFun h2 i
    rw [Pi.smul_apply, smul_eq_mul, ← hdet] at h3
    rw [h3, show Tq.adjugate = (Int.castRingHom ℚ).mapMatrix (Matrix.of T).adjugate from
      (RingHom.map_adjugate _ _).symm]
    simp only [Matrix.mulVec, dotProduct, RingHom.mapMatrix_apply, Matrix.map_apply]
    push_cast
    rfl
  rw [Submodule.mem_one]
  refine ⟨∑ i, Matrix.mulVec (Matrix.of T).adjugate m i • RingOfIntegers.basis K i, ?_⟩
  rw [map_sum]
  conv_rhs => rw [← (NumberField.integralBasis K).sum_repr a, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul, zsmul_eq_mul, ← NumberField.integralBasis_apply, Rat.smul_def]
  have := congrArg (fun q : ℚ => (q : K)) (hn i)
  push_cast at this
  rw [← this]
  ring

/- English proof (translation)
Establish `hi : IsIntegral ℤ (Algebra.trace ℚ K (algebraMap (𝓞 K) K r))` using `Algebra.isIntegral_trace (RingOfIntegers.isIntegral_coe r)`. Take `⟨z, hz⟩` from `IsIntegrallyClosed.isIntegral_iff.mp hi`. Conclude with `⟨z, by rw [← hz]; simp⟩`.
-/
theorem genusCovolBound_trace_int (r : 𝓞 K) :
    ∃ z : ℤ, Algebra.trace ℚ K (algebraMap (𝓞 K) K r) = z := by
  have hi : IsIntegral ℤ (Algebra.trace ℚ K (algebraMap (𝓞 K) K r)) :=
    Algebra.isIntegral_trace (RingOfIntegers.isIntegral_coe r)
  obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.mp hi
  exact ⟨z, by rw [← hz]; simp⟩

end PartB

/- English proof (translation)
Introduce `K V _ _ _ _ _ _ _ _ h hs hpos N ι hι L hL`. Establish `hnd : h.Nondegenerate`. Use `⟨fun x hx => ?_, fun y hy => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hne`. Use `hpos x hne` as an intermediate fact.

Rewrite `this` using `[hx x]`. Simplify using `at this`. Assume the negation of the conclusion as `hne`. Use `hpos y hne` as an intermediate fact. Rewrite `this` using `[hy y]`.

Simplify using `at this`. Establish `hstar : ∀ r : 𝓞 K, star (algebraMap (𝓞 K) K r) ∈ Set.range (algebraMap (𝓞 K) K)`. Introduce `r`. Establish `hi : IsIntegral ℤ (star (algebraMap (𝓞 K) K r))`. Use `(RingOfIntegers.isIntegral_coe r).map ((starRingEnd K).toIntAlgHom)` as an intermediate fact.

Rewrite `this` using `[RingHom.toIntAlgHom_apply, starRingEnd_apply]`. Then use the resulting hypothesis. Conclude with `(IsIntegralClosure.isIntegral_iff (A := 𝓞 K)).mp hi`. Establish `hdL` using `dualLattice (𝓞 K) K V h hs hnd hstar L hL`. Take `⟨d, hd0, hd⟩` from `genusScale K V h hs (dual h L) hdL.1`. Use `set δ : ℤ := NumberField.discr K with hδ`.

Establish `hδ0 : δ ≠ 0` using `NumberField.discr_ne_zero K`. Use `⟨Real.sqrt (((d * δ.natAbs ^ 2 : ℕ) : ℝ) ^ N), fun M hM _ _ => ?_⟩` and prove the remaining obligations. Use `genusCovolBound_covol_le h N ι hι M (d * δ.natAbs ^ 2) (Nat.mul_pos hd0 (pow_pos (Int.natAbs_pos.mpr hδ0) 2)) ?_` and prove the remaining obligations. Establish `key : ∀ y : V, (∀ x ∈ M, ∃ z : ℤ, Algebra.trace ℚ K (h x y) = z) → (δ : K) • y ∈ dual h M`. Introduce `y hy`.

Simplify using `only [dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.coe_restrictScalars]`. Introduce `x hx`. Rewrite using `[map_smul, smul_eq_mul]`. Apply `genusCovolBound_discr` to reduce the goal to its premises. Introduce `r`.

Take `⟨s, hs'⟩` from `hstar r`. Take `⟨z, hz⟩` from `hy (s • x) (M.smul_mem s hx)`. Use `⟨z, ?_⟩` and prove the remaining obligations. Rewrite using `[← hz, ← algebraMap_smul K s x, LinearMap.map_smulₛₗ, LinearMap.smul_apply, hs', starRingEnd_apply, star_star, smul_eq_mul, mul_comm]`. Introduce `y y' hy hy'`.

Establish `hmem` using `genusCovolBound_dual_genus h hs hnd hstar L hL M hM`. Establish `h1` using `hd (dual h M) hmem _ (key y hy) _ (key y' hy')`. Take `⟨w, hw⟩` from `Submodule.mem_one.mp h1`. Take `⟨z, hz⟩` from `genusCovolBound_trace_int w`. Use `⟨z, ?_⟩` and prove the remaining obligations.

Establish `e2 : h ((δ : K) • y) ((δ : K) • y') = (δ : K) * ((δ : K) * h y y')`. Rewrite using `[LinearMap.map_smulₛₗ₂, LinearMap.map_smul, starRingEnd_apply, star_intCast, smul_eq_mul, smul_eq_mul]`. Rewrite using `[← hz, hw, e2]`. Establish `e : (d : K) * ((δ : K) * ((δ : K) * h y y')) = algebraMap ℚ K (((d * δ.natAbs ^ 2 : ℕ) : ℚ)) * h y y'`. Establish `hna : ((δ.natAbs ^ 2 : ℕ) : ℚ) = (δ : ℚ) ^ 2`.

Use `push_cast`. Simplify using `[sq_abs]`. Rewrite using `[Nat.cast_mul, hna, map_mul, map_pow, map_natCast, map_intCast]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, ← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul]`.
-/
theorem genusCovolBound : GenusCovolBound := by
  intro K V _ _ _ _ _ _ _ _ h hs hpos N ι hι L hL
  have hnd : h.Nondegenerate := by
    refine ⟨fun x hx => ?_, fun y hy => ?_⟩
    · by_contra hne
      have := hpos x hne
      rw [hx x] at this
      simp at this
    · by_contra hne
      have := hpos y hne
      rw [hy y] at this
      simp at this
  have hstar : ∀ r : 𝓞 K, star (algebraMap (𝓞 K) K r) ∈ Set.range (algebraMap (𝓞 K) K) := by
    intro r
    have hi : IsIntegral ℤ (star (algebraMap (𝓞 K) K r)) := by
      have := (RingOfIntegers.isIntegral_coe r).map ((starRingEnd K).toIntAlgHom)
      rwa [RingHom.toIntAlgHom_apply, starRingEnd_apply] at this
    exact (IsIntegralClosure.isIntegral_iff (A := 𝓞 K)).mp hi
  have hdL := dualLattice (𝓞 K) K V h hs hnd hstar L hL
  obtain ⟨d, hd0, hd⟩ := genusScale K V h hs (dual h L) hdL.1
  set δ : ℤ := NumberField.discr K with hδ
  have hδ0 : δ ≠ 0 := NumberField.discr_ne_zero K
  refine ⟨Real.sqrt (((d * δ.natAbs ^ 2 : ℕ) : ℝ) ^ N), fun M hM _ _ => ?_⟩
  refine genusCovolBound_covol_le h N ι hι M (d * δ.natAbs ^ 2)
    (Nat.mul_pos hd0 (pow_pos (Int.natAbs_pos.mpr hδ0) 2)) ?_

  have key : ∀ y : V, (∀ x ∈ M, ∃ z : ℤ, Algebra.trace ℚ K (h x y) = z) →
      (δ : K) • y ∈ dual h M := by
    intro y hy
    simp only [dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
      LinearMap.coe_restrictScalars]
    intro x hx
    rw [map_smul, smul_eq_mul]
    apply genusCovolBound_discr
    intro r
    obtain ⟨s, hs'⟩ := hstar r
    obtain ⟨z, hz⟩ := hy (s • x) (M.smul_mem s hx)
    refine ⟨z, ?_⟩
    rw [← hz, ← algebraMap_smul K s x, LinearMap.map_smulₛₗ, LinearMap.smul_apply, hs',
      starRingEnd_apply, star_star, smul_eq_mul, mul_comm]
  intro y y' hy hy'
  have hmem := genusCovolBound_dual_genus h hs hnd hstar L hL M hM
  have h1 := hd (dual h M) hmem _ (key y hy) _ (key y' hy')
  obtain ⟨w, hw⟩ := Submodule.mem_one.mp h1
  obtain ⟨z, hz⟩ := genusCovolBound_trace_int w
  refine ⟨z, ?_⟩
  have e2 : h ((δ : K) • y) ((δ : K) • y') = (δ : K) * ((δ : K) * h y y') := by
    rw [LinearMap.map_smulₛₗ₂, LinearMap.map_smul, starRingEnd_apply, star_intCast, smul_eq_mul,
      smul_eq_mul]
  rw [← hz, hw, e2]
  have e : (d : K) * ((δ : K) * ((δ : K) * h y y')) =
      algebraMap ℚ K (((d * δ.natAbs ^ 2 : ℕ) : ℚ)) * h y y' := by
    have hna : ((δ.natAbs ^ 2 : ℕ) : ℚ) = (δ : ℚ) ^ 2 := by
      push_cast
      simp [sq_abs]
    rw [Nat.cast_mul, hna, map_mul, map_pow, map_natCast, map_intCast]
    ring
  rw [e, ← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul]

end Formalism.HermitianLatticesTheory
