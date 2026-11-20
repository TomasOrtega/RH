import ReciprocityTheory.DualLattices.FormMonomialUnitVector
import ReciprocityTheory.DualLattices.FrobEqOfLe

noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

open ReciprocityTheory.PGsh.Up.FrobeniusValuationMatrix ReciprocityTheory.PGsh.Up.UnitVectorPowers

/- English proof (translation)
Introduce `p _ g C _ _ _ v R _ _ _ O _ _ σ cp _ hS H U X D`. Establish `hv` using `hS.integers`. Establish `hp1` using `hS.p_lt`. Use `haveI := isLocal_of_integers hv`. Use `haveI : CharP (IsLocalRing.ResidueField R) p := by`.

Establish `h0` using `residue_p hv hp1`. Use `first`. Consider the case `exact (CharP.charP_iff_prime_eq_zero Fact.out).mpr h0`. Consider the case `exact CharP.of_prime_eq_zero Fact.out h0`. Consider the case `exact (charP_iff_prime_eq_zero Fact.out).mpr h0`.

Use `⟨fun j l hl => ?_, fun i e => ?_⟩` and prove the remaining obligations. Rewrite using `[linX_xp hv hp1 D j l, bR_off hv hp1 D j l hl, map_zero, zero_mul]`. Establish `hM : (Matrix.of fun j l : {j // D.κ j = i} => linX D (fun y => xL D j.1 y ^ p) (e l).1) = Matrix.of fun j l : {j // D.κ j = i} => algebraMap R C (bR hv D j.1 (e1 (e l).1)) * (algebraMap R C (D.ε j.1) ^ p / algebraMap R C (D.ε (e l).1))`. Use extensionality with `j l`. Simplify using `only [Matrix.of_apply]`.

Conclude with `linX_xp hv hp1 D j.1 (e l).1`. Establish `hs` using `Det2.v_det_scaled v (Matrix.of fun j l : {j // D.κ j = i} => algebraMap R C (bR hv D j.1 (e1 (e l).1))) (fun j => algebraMap R C (D.ε j.1) ^ p) (fun l => algebraMap R C (D.ε (e l).1))`. Simplify using `only [Matrix.of_apply] at hs`. Establish `hcB : (Matrix.of fun j l : {j // D.κ j = i} => algebraMap R C (bR hv D j.1 (e1 (e l).1))).det = algebraMap R C (Matrix.of fun j l : {j // D.κ j = i} => bR hv D j.1 (e1 (e l).1)).det`. Rewrite using `[RingHom.map_det]`.

Use `first`. Consider the case `rfl`. Consider the case `(congr 1; ext j l; simp [RingHom.mapMatrix_apply])`. Establish `hres : IsLocalRing.residue R (Matrix.of fun j l : {j // D.κ j = i} => bR hv D j.1 (e1 (e l).1)).det = (Matrix.of fun j l : {j // D.κ j = i} => Mk D j.1 (e l).1).det`. Rewrite using `[RingHom.map_det]`.

Use `congr 1`. Use extensionality with `j l`. Simplify using `only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply]`. Conclude with `res_bR hv hp1 D _ _`. Establish `hunit : IsUnit (Matrix.of fun j l : {j // D.κ j = i} => bR hv D j.1 (e1 (e l).1)).det`.

Assume the negation of the conclusion as `h`. Apply `block_det_ne hv hp1 D i e` to reduce the goal to its premises. Rewrite using `[← hres, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]`. Conclude with `h`. Establish `h1` using `hv.one_of_isUnit hunit`.

Establish `hy : ∏ j : {j // D.κ j = i}, v (algebraMap R C (D.ε j.1) ^ p) = X i ^ p`. Rewrite using `[← D.ε_prod i, ← Finset.prod_pow]`. Simplify using `only [map_pow]`. Conclude with `(Finset.prod_subtype _ (fun j => by simp) (fun j => v (algebraMap R C (D.ε j)) ^ p)).symm`. Establish `hz : ∏ k : {j // D.κ j = i}, v (algebraMap R C (D.ε (e k).1)) = X (U.φ i)` using `(Equiv.prod_comp e (fun l : {l // D.κ l = U.φ i} => v (algebraMap R C (D.ε l.1)))).trans ((Finset.prod_subtype _ (fun l => by simp) (fun l => v (algebraMap R C (D.ε l)))).symm.trans (D.ε_prod (U.φ i)))`.

Rewrite using `[hM, hs, hcB, h1, hy, hz, one_mul]`.
-/
theorem frobeniusBlock : FrobeniusBlockStatement := by
  intro p _ g C _ _ _ v R _ _ _ O _ _ σ cp _ hS H U X D
  have hv := hS.integers
  have hp1 := hS.p_lt
  haveI := isLocal_of_integers hv
  haveI : CharP (IsLocalRing.ResidueField R) p := by
    have h0 := residue_p hv hp1
    first
      | exact (CharP.charP_iff_prime_eq_zero Fact.out).mpr h0
      | exact CharP.of_prime_eq_zero Fact.out h0
      | exact (charP_iff_prime_eq_zero Fact.out).mpr h0
  refine ⟨fun j l hl => ?_, fun i e => ?_⟩
  · rw [linX_xp hv hp1 D j l, bR_off hv hp1 D j l hl, map_zero, zero_mul]
  ·
    have hM : (Matrix.of fun j l : {j // D.κ j = i} =>
        linX D (fun y => xL D j.1 y ^ p) (e l).1) =
        Matrix.of fun j l : {j // D.κ j = i} =>
          algebraMap R C (bR hv D j.1 (e1 (e l).1)) *
            (algebraMap R C (D.ε j.1) ^ p / algebraMap R C (D.ε (e l).1)) := by
      ext j l
      simp only [Matrix.of_apply]
      exact linX_xp hv hp1 D j.1 (e l).1
    have hs := Det2.v_det_scaled v
      (Matrix.of fun j l : {j // D.κ j = i} => algebraMap R C (bR hv D j.1 (e1 (e l).1)))
      (fun j => algebraMap R C (D.ε j.1) ^ p) (fun l => algebraMap R C (D.ε (e l).1))
    simp only [Matrix.of_apply] at hs

    have hcB : (Matrix.of fun j l : {j // D.κ j = i} =>
        algebraMap R C (bR hv D j.1 (e1 (e l).1))).det =
        algebraMap R C (Matrix.of fun j l : {j // D.κ j = i} => bR hv D j.1 (e1 (e l).1)).det := by
      rw [RingHom.map_det]
      first
        | rfl
        | (congr 1; ext j l; simp [RingHom.mapMatrix_apply])
    have hres : IsLocalRing.residue R
        (Matrix.of fun j l : {j // D.κ j = i} => bR hv D j.1 (e1 (e l).1)).det =
        (Matrix.of fun j l : {j // D.κ j = i} => Mk D j.1 (e l).1).det := by
      rw [RingHom.map_det]
      congr 1
      ext j l
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply]
      exact res_bR hv hp1 D _ _
    have hunit : IsUnit
        (Matrix.of fun j l : {j // D.κ j = i} => bR hv D j.1 (e1 (e l).1)).det := by
      by_contra h
      apply block_det_ne hv hp1 D i e
      rw [← hres, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      exact h
    have h1 := hv.one_of_isUnit hunit
    have hy : ∏ j : {j // D.κ j = i}, v (algebraMap R C (D.ε j.1) ^ p) = X i ^ p := by
      rw [← D.ε_prod i, ← Finset.prod_pow]
      simp only [map_pow]
      exact (Finset.prod_subtype _ (fun j => by simp)
        (fun j => v (algebraMap R C (D.ε j)) ^ p)).symm
    have hz : ∏ k : {j // D.κ j = i}, v (algebraMap R C (D.ε (e k).1)) = X (U.φ i) :=
      (Equiv.prod_comp e (fun l : {l // D.κ l = U.φ i} => v (algebraMap R C (D.ε l.1)))).trans
        ((Finset.prod_subtype _ (fun l => by simp)
          (fun l => v (algebraMap R C (D.ε l)))).symm.trans (D.ε_prod (U.φ i)))
    rw [hM, hs, hcB, h1, hy, hz, one_mul]

end ReciprocityTheory.PGsh.Up
