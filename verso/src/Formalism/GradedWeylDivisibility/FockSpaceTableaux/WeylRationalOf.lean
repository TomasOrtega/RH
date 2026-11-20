import Formalism.GradedWeylDivisibility.StatementB
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LClosedeqLemmas

open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

/- English proof (translation)
Proceed by induction on `f using MvPolynomial.induction_on`. Use `next c =>`. Simplify using `[rowGen]`. Use `next p q hp hq =>`. Rewrite using `[_root_.map_add, _root_.map_add, _root_.map_add, hp, hq, Polynomial.map_add]`.

Use `next p v hp =>`. Rewrite using `[_root_.map_mul, map_X, _root_.map_mul, _root_.map_mul, Polynomial.map_mul, hp]`. Use `congr 1`. Simplify using `only [rowGen, aeval_X]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
private theorem rowGen_map_intCast {r n : ℕ} (a b : Fin r) (f : MvPolynomial (Fin r × Fin n) ℤ) :
    rowGen ℚ a b (map (Int.castRingHom ℚ) f) =
      Polynomial.map (map (Int.castRingHom ℚ)) (rowGen ℤ a b f) := by
  induction f using MvPolynomial.induction_on
  next c =>
    simp [rowGen]
  next p q hp hq =>
    rw [_root_.map_add, _root_.map_add, _root_.map_add, hp, hq, Polynomial.map_add]
  next p v hp =>
    rw [_root_.map_mul, map_X, _root_.map_mul, _root_.map_mul, Polynomial.map_mul, hp]
    congr 1
    simp only [rowGen, aeval_X]
    split_ifs <;> simp

/- English proof (translation)
Unfold `rowDiv`. Rewrite using `[rowGen_map_intCast, Polynomial.coeff_map]`.
-/
private theorem rowDiv_map_intCast {r n : ℕ} (a b : Fin r) (k : ℕ) (f : MvPolynomial (Fin r × Fin n) ℤ) :
    rowDiv ℚ a b k (map (Int.castRingHom ℚ) f) = map (Int.castRingHom ℚ) (rowDiv ℤ a b k f) := by
  unfold rowDiv
  rw [rowGen_map_intCast, Polynomial.coeff_map]

/- English proof (translation)
Proceed by induction on `w with`. Consider the case `nil => rfl`. Consider the case `cons x w ih => show map (Int.castRingHom ℚ) (rowDiv ℤ x.1 x.2.1 x.2.2 (applyWord ℤ w f)) = rowDiv ℚ x.1 x.2.1 x.2.2 (applyWord ℚ w (map (Int.castRingHom ℚ) f))`. Rewrite using `[← rowDiv_map_intCast, ih]`.
-/
private theorem map_intCast_applyWord {r n : ℕ} (w : List (Fin r × Fin r × ℕ))
    (f : MvPolynomial (Fin r × Fin n) ℤ) :
    map (Int.castRingHom ℚ) (applyWord ℤ w f) = applyWord ℚ w (map (Int.castRingHom ℚ) f) := by
  induction w with
  | nil => rfl
  | cons x w ih =>
    show map (Int.castRingHom ℚ) (rowDiv ℤ x.1 x.2.1 x.2.2 (applyWord ℤ w f)) =
      rowDiv ℚ x.1 x.2.1 x.2.2 (applyWord ℚ w (map (Int.castRingHom ℚ) f))
    rw [← rowDiv_map_intCast, ih]

/- English proof (translation)
Unfold `hw`. Rewrite using `[_root_.map_prod]`. Use `Finset.prod_congr rfl (fun s _ => ?_)` and prove the remaining obligations. Rewrite using `[_root_.map_pow]`. Use `congr 1`.

Unfold `lpMinor`. Rewrite using `[RingHom.map_det]`. Use `congr 1`. Use extensionality with `p q`. Simplify using `[RingHom.mapMatrix_apply]`.
-/
private theorem map_intCast_hw {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) :
    map (Int.castRingHom ℚ) (hw ℤ hn ν) = hw ℚ hn ν := by
  unfold hw
  rw [_root_.map_prod]
  refine Finset.prod_congr rfl (fun s _ => ?_)
  rw [_root_.map_pow]
  congr 1
  unfold lpMinor
  rw [RingHom.map_det]
  congr 1
  ext p q
  simp [RingHom.mapMatrix_apply]

/- English proof (translation)
Unfold `weyl at hF`. Proceed by induction on `hF using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨w, rfl⟩` from `hx`. Use `⟨1, one_ne_zero, applyWord ℤ w (hw ℤ hn ν), Submodule.subset_span ⟨w, rfl⟩, ?_⟩` and prove the remaining obligations.

Rewrite using `[map_intCast_applyWord, map_intCast_hw]`. Simplify using the standard rewrite rules. Consider the case `zero => exact ⟨1, one_ne_zero, 0, Submodule.zero_mem _, by simp⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨c, hc, u, hu, hu'⟩` from `hx`.

Take `⟨d, hd, v, hv, hv'⟩` from `hy`. Use `⟨c * d, mul_ne_zero hc hd, d • u + c • v, Submodule.add_mem _ (Submodule.smul_mem _ _ hu) (Submodule.smul_mem _ _ hv), ?_⟩` and prove the remaining obligations. Rewrite using `[_root_.map_add, MvPolynomial.smul_eq_C_mul u d, MvPolynomial.smul_eq_C_mul v c, _root_.map_mul, _root_.map_mul, map_C, map_C, hu', hv']`. Simplify using `only [MvPolynomial.smul_eq_C_mul, eq_intCast, Int.cast_mul, MvPolynomial.C_mul]`. Expand and normalize the polynomial expressions, which then agree.

Consider the case `smul q x _ hx`. Take `⟨c, hc, u, hu, hu'⟩` from `hx`. Use `⟨(q.den : ℤ) * c, mul_ne_zero (by exact_mod_cast q.den_nz) hc, q.num • u, Submodule.smul_mem _ _ hu, ?_⟩` and prove the remaining obligations. Rewrite using `[MvPolynomial.smul_eq_C_mul u q.num, _root_.map_mul, map_C, hu']`. Establish `hq : q * (q.den : ℚ) = (q.num : ℚ)` using `Rat.mul_den_eq_num q`.

Simplify using `only [MvPolynomial.smul_eq_C_mul, eq_intCast, Int.cast_mul, Int.cast_natCast, MvPolynomial.C_mul, ← hq]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem lclosedeq_weyl_denom {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ)
    (F : MvPolynomial (Fin r × Fin n) ℚ) (hF : F ∈ weyl ℚ r n hn ν) :
    ∃ c : ℤ, c ≠ 0 ∧ ∃ u ∈ weyl ℤ r n hn ν, map (Int.castRingHom ℚ) u = (c : ℚ) • F := by
  unfold weyl at hF
  induction hF using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, rfl⟩ := hx
    refine ⟨1, one_ne_zero, applyWord ℤ w (hw ℤ hn ν), Submodule.subset_span ⟨w, rfl⟩, ?_⟩
    rw [map_intCast_applyWord, map_intCast_hw]
    simp
  | zero => exact ⟨1, one_ne_zero, 0, Submodule.zero_mem _, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨c, hc, u, hu, hu'⟩ := hx
    obtain ⟨d, hd, v, hv, hv'⟩ := hy
    refine ⟨c * d, mul_ne_zero hc hd, d • u + c • v,
      Submodule.add_mem _ (Submodule.smul_mem _ _ hu) (Submodule.smul_mem _ _ hv), ?_⟩
    rw [_root_.map_add, MvPolynomial.smul_eq_C_mul u d, MvPolynomial.smul_eq_C_mul v c,
      _root_.map_mul, _root_.map_mul, map_C, map_C, hu', hv']
    simp only [MvPolynomial.smul_eq_C_mul, eq_intCast, Int.cast_mul, MvPolynomial.C_mul]
    ring
  | smul q x _ hx =>
    obtain ⟨c, hc, u, hu, hu'⟩ := hx
    refine ⟨(q.den : ℤ) * c, mul_ne_zero (by exact_mod_cast q.den_nz) hc, q.num • u,
      Submodule.smul_mem _ _ hu, ?_⟩
    rw [MvPolynomial.smul_eq_C_mul u q.num, _root_.map_mul, map_C, hu']
    have hq : q * (q.den : ℚ) = (q.num : ℚ) := Rat.mul_den_eq_num q
    simp only [MvPolynomial.smul_eq_C_mul, eq_intCast, Int.cast_mul, Int.cast_natCast,
      MvPolynomial.C_mul, ← hq]
    ring

/- English proof (translation)
Proceed by induction on `f using MvPolynomial.induction_on`. Use `next c =>`. Simplify using `[colAddGen]`. Use `next p q hp hq =>`. Rewrite using `[_root_.map_add, _root_.map_add, _root_.map_add, hp, hq, _root_.map_add]`.

Use `next p v hp =>`. Rewrite using `[_root_.map_mul, map_X, _root_.map_mul, _root_.map_mul, _root_.map_mul, hp]`. Use `congr 1`. Simplify using `only [colAddGen, aeval_X]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
private theorem colAddGen_map_intCast {r n : ℕ} (l j : Fin n) (f : MvPolynomial (Fin r × Fin n) ℤ) :
    colAddGen ℚ (r := r) l j (map (Int.castRingHom ℚ) f) =
      map (Int.castRingHom ℚ) (colAddGen ℤ (r := r) l j f) := by
  induction f using MvPolynomial.induction_on
  next c =>
    simp [colAddGen]
  next p q hp hq =>
    rw [_root_.map_add, _root_.map_add, _root_.map_add, hp, hq, _root_.map_add]
  next p v hp =>
    rw [_root_.map_mul, map_X, _root_.map_mul, _root_.map_mul, _root_.map_mul, hp]
    congr 1
    simp only [colAddGen, aeval_X]
    split_ifs <;> simp

/- English proof (translation)
Simplify using `only [dualWeyl, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, AlgHom.toLinearMap_apply, sub_eq_zero, mem_weightedHomogeneousSubmodule] at hf ⊢`. Take `⟨h1, h2⟩` from `hf`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `d hd`. Apply `h1` to reduce the goal to its premises.

Introduce `h0`. Apply `hd` to reduce the goal to its premises. Rewrite using `[coeff_map, h0, _root_.map_zero]`. Introduce `l j hlj`. Rewrite using `[colAddGen_map_intCast, h2 l j hlj, map_rename]`.
-/
private theorem map_intCast_mem_dualWeyl {r n : ℕ} (ν : Fin n → ℕ) (f : MvPolynomial (Fin r × Fin n) ℤ)
    (hf : f ∈ dualWeyl ℤ r n ν) : map (Int.castRingHom ℚ) f ∈ dualWeyl ℚ r n ν := by
  simp only [dualWeyl, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker,
    LinearMap.sub_apply, AlgHom.toLinearMap_apply, sub_eq_zero,
    mem_weightedHomogeneousSubmodule] at hf ⊢
  obtain ⟨h1, h2⟩ := hf
  refine ⟨?_, ?_⟩
  · intro d hd
    apply h1
    intro h0
    apply hd
    rw [coeff_map, h0, _root_.map_zero]
  · intro l j hlj
    rw [colAddGen_map_intCast, h2 l j hlj, map_rename]

/- English proof (translation)
Unfold `WeylRationalOf WeylRational`. Introduce `h r n hn ν hν f hf`. Establish `hfQ : map (Int.castRingHom ℚ) f ∈ weyl ℚ r n hn ν`. Rewrite using `[h r n hn ν hν]`. Conclude with `map_intCast_mem_dualWeyl ν f hf`.

Take `⟨c, hc, u, hu, hmap⟩` from `lclosedeq_weyl_denom hn ν _ hfQ`. Use `⟨c, hc, ?_⟩` and prove the remaining obligations. Establish `huf : u = c • f`. Apply `MvPolynomial.map_injective _ (RingHom.injective_int (Int.castRingHom ℚ))` to reduce the goal to its premises. Rewrite using `[hmap, _root_.map_zsmul]`.

Conclude with `Int.cast_smul_eq_zsmul ℚ c _`. Rewrite using `[← huf]`. Conclude with `hu`.
-/
theorem weyl_module_rational : WeylRationalOf := by
  unfold WeylRationalOf WeylRational
  intro h r n hn ν hν f hf
  have hfQ : map (Int.castRingHom ℚ) f ∈ weyl ℚ r n hn ν := by
    rw [h r n hn ν hν]
    exact map_intCast_mem_dualWeyl ν f hf
  obtain ⟨c, hc, u, hu, hmap⟩ := lclosedeq_weyl_denom hn ν _ hfQ
  refine ⟨c, hc, ?_⟩
  have huf : u = c • f := by
    apply MvPolynomial.map_injective _ (RingHom.injective_int (Int.castRingHom ℚ))
    rw [hmap, _root_.map_zsmul]
    exact Int.cast_smul_eq_zsmul ℚ c _
  rw [← huf]
  exact hu

end Formalism.GradedWeylDivisibility
