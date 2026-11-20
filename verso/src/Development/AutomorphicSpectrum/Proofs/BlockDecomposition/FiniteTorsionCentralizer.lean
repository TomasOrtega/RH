import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.EulerFinOf
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsMulCommutativeCentRealUJ
open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.TorCent

/- English proof (translation)
Use `(NumberField.Embeddings.finite_of_norm_le M ℂ 1).subset ?_` and prove the remaining obligations. Introduce and unpack `ζ ⟨k, hk, h⟩`. Use `⟨IsIntegral.of_pow hk (by rw [h]; exact isIntegral_one), fun φ => ?_⟩` and prove the remaining obligations. Establish `h1 : (φ ζ) ^ k = 1` using `by rw [← map_pow, h, map_one]`. Conclude with `(Complex.norm_eq_one_of_pow_eq_one h1 hk.ne').le`.
-/
theorem finite_roots_of_unity (M : Type) [Field M] [NumberField M] :
    {ζ : M | ∃ k : ℕ, 0 < k ∧ ζ ^ k = 1}.Finite := by
  refine (NumberField.Embeddings.finite_of_norm_le M ℂ 1).subset ?_
  rintro ζ ⟨k, hk, h⟩
  refine ⟨IsIntegral.of_pow hk (by rw [h]; exact isIntegral_one), fun φ => ?_⟩
  have h1 : (φ ζ) ^ k = 1 := by rw [← map_pow, h, map_one]
  exact (Complex.norm_eq_one_of_pow_eq_one h1 hk.ne').le

/- English proof (translation)
Establish `hnd : A.charpoly.roots.Nodup` using `nodup_roots hs`. Establish `hcard` using `splits_iff_card_roots.1 hsp`. Establish `hdeg : A.charpoly.natDegree = n`. Rewrite using `[charpoly_natDegree_eq_dim, Fintype.card_fin]`. Use `set s := A.charpoly.roots.toFinset with hs_def`.

Establish `hsc : Fintype.card s = n`. Rewrite using `[Fintype.card_coe, Multiset.toFinset_card_of_nodup hnd, hcard, hdeg]`. Set `e` to `Fintype.equivFinOfCardEq hsc`. Use `⟨fun a => ((e.symm a : s) : M), Subtype.val_injective.comp e.symm.injective, ?_⟩` and prove the remaining obligations. Rewrite using `[Equiv.prod_comp e.symm (fun r : s => X - C (r : M)), Finset.prod_coe_sort s (fun r => X - C r), Finset.prod_eq_multiset_prod, hs_def, Multiset.toFinset_val, Multiset.dedup_eq_self.2 hnd, prod_multiset_X_sub_C_of_monic_of_roots_card_eq (charpoly_monic _) hcard]`.
-/
theorem exists_distinct_roots {M : Type} [Field M] {n : ℕ} (A : Matrix (Fin n) (Fin n) M)
    (hs : A.charpoly.Separable) (hsp : A.charpoly.Splits) :
    ∃ z : Fin n → M, Function.Injective z ∧ A.charpoly = ∏ a, (X - C (z a)) := by
  have hnd : A.charpoly.roots.Nodup := nodup_roots hs
  have hcard := splits_iff_card_roots.1 hsp
  have hdeg : A.charpoly.natDegree = n := by
    rw [charpoly_natDegree_eq_dim, Fintype.card_fin]
  set s := A.charpoly.roots.toFinset with hs_def
  have hsc : Fintype.card s = n := by
    rw [Fintype.card_coe, Multiset.toFinset_card_of_nodup hnd, hcard, hdeg]
  let e := Fintype.equivFinOfCardEq hsc
  refine ⟨fun a => ((e.symm a : s) : M), Subtype.val_injective.comp e.symm.injective, ?_⟩
  rw [Equiv.prod_comp e.symm (fun r : s => X - C (r : M)), Finset.prod_coe_sort s (fun r => X - C r),
    Finset.prod_eq_multiset_prod, hs_def, Multiset.toFinset_val, Multiset.dedup_eq_self.2 hnd,
    prod_multiset_X_sub_C_of_monic_of_roots_card_eq (charpoly_monic _) hcard]

/- English proof (translation)
Use extensionality with `i j`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Simplify using the standard rewrite rules. Establish `h1` using `congrFun (congrFun h i) j`.

Rewrite `h1` using `[mul_diagonal, diagonal_mul]`. Rewrite using `[diagonal_apply_ne _ hij]`. Establish `h2 : F i j * (z j - z i) = 0` using `by rw [mul_sub, h1]; ring`. Conclude with `(mul_eq_zero.1 h2).resolve_right (sub_ne_zero.2 fun e => hij (hz e.symm))`.
-/
theorem eq_diagonal_of_commute {M : Type} [Field M] {n : ℕ} {z : Fin n → M}
    (hz : Function.Injective z) {F : Matrix (Fin n) (Fin n) M}
    (h : F * diagonal z = diagonal z * F) : F = diagonal fun i => F i i := by
  ext i j
  by_cases hij : i = j
  · subst hij; simp
  · have h1 := congrFun (congrFun h i) j
    rw [mul_diagonal, diagonal_mul] at h1
    rw [diagonal_apply_ne _ hij]
    have h2 : F i j * (z j - z i) = 0 := by rw [mul_sub, h1]; ring
    exact (mul_eq_zero.1 h2).resolve_right (sub_ne_zero.2 fun e => hij (hz e.symm))

/- English proof (translation)
Introduce `E _ _ n N hsep`. Set `M` to `N.val.charpoly.SplittingField`. Use `haveI : NumberField M := NumberField.of_module_finite E M`. Set `f : E →+* M` to `algebraMap E M`. Set `A : Matrix (Fin n) (Fin n) M` to `N.val.map f`.

Establish `hA : A.charpoly = N.val.charpoly.map f` using `charpoly_map _ _`. Establish `hs : A.charpoly.Separable` using `by rw [hA]; exact hsep.map`. Establish `hsp : A.charpoly.Splits` using `by rw [hA]; exact SplittingField.splits _`. Take `⟨z, hz, hprod⟩` from `exists_distinct_roots A hs hsp`. Take `⟨x, hx⟩` from `GlobalTheory.Orb.IsRegSS.exists_conj (M := A) (N := diagonal z) hs (by rw [charpoly_diagonal, hprod])`.

Set `B : Matrix (Fin n) (Fin n) M` to `x.val`. Set `Bi : Matrix (Fin n) (Fin n) M` to `(x⁻¹).val`. Establish `hBB : B * Bi = 1` using `by simp [B, Bi]`. Establish `hBB' : Bi * B = 1` using `by simp [B, Bi]`. Establish `hx' : diagonal z * B = B * A` using `hx`.

Establish `hx2 : Bi * diagonal z = A * Bi`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.mul_assoc, Matrix.mul_assoc, hBB, Matrix.mul_one]`. Use `_ = A * Bi := by rw [hx', ← Matrix.mul_assoc, hBB', Matrix.one_mul]`. Set `F : GL (Fin n) E → Matrix (Fin n) (Fin n) M` to `fun g => B * g.val.map f * Bi`.

Establish `hFc : ∀ g : GL (Fin n) E, g * N = N * g → F g * diagonal z = diagonal z * F g`. Introduce `g hg`. Establish `h1 : g.val * N.val = N.val * g.val` using `congrArg Units.val hg`. Establish `h2 : g.val.map f * A = A * g.val.map f`. Simplify using `only [A]`.

Rewrite using `[← Matrix.map_mul, ← Matrix.map_mul, h1]`. Simplify using `only [F]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.mul_assoc, hx2, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc]`. Use `_ = diagonal z * (B * g.val.map f * Bi) := by`.

Rewrite using `[h2, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← hx', Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc]`. Establish `hFpow : ∀ (g : GL (Fin n) E) (k : ℕ), F g ^ k = F (g ^ k)`. Introduce `g k`. Proceed by induction on `k with`. Consider the case `zero => simp [F, hBB, Matrix.map_one, Matrix.mul_one]`.

Consider the case `succ k ih`. Rewrite using `[pow_succ, ih, pow_succ]`. Simplify using `only [F, Units.val_mul]`. Rewrite using `[Matrix.map_mul]`. Combine the equalities or inequalities in the displayed calculation.

Simplify using `only [Matrix.mul_assoc]`. Use `_ = _ := by rw [hBB', Matrix.mul_one]; simp only [Matrix.mul_assoc]`. Set `φ : GL (Fin n) E → Fin n → M` to `fun g i => F g i i`. Establish `hfin` using `Set.Finite.pi' fun _ : Fin n => finite_roots_of_unity M`. Use `Set.Finite.of_injOn (f := φ) ?_ ?_ hfin` and prove the remaining obligations.

Introduce and unpack `g ⟨hg, ho⟩ i`. Take `⟨k, hk, hgk⟩` from `isOfFinOrder_iff_pow_eq_one.1 ho`. Use `⟨k, hk, ?_⟩` and prove the remaining obligations. Establish `h1 : F g ^ k = 1`. Rewrite using `[hFpow, hgk]`.

Simplify using `[F, hBB, Matrix.map_one]`. Rewrite `h1` using `[eq_diagonal_of_commute hz (hFc g hg), diagonal_pow]`. Establish `h2` using `congrFun (congrFun h1 i) i`. Simplify `h2` using `[φ]`. Introduce and unpack `g ⟨hg, -⟩ g' ⟨hg', -⟩ e`.

Establish `h1 : F g = F g'`. Rewrite using `[eq_diagonal_of_commute hz (hFc g hg), eq_diagonal_of_commute hz (hFc g' hg')]`. Conclude with `congrArg diagonal e`. Establish `h2 : g.val.map f = g'.val.map f`. Establish `h3 : Bi * F g * B = Bi * F g' * B` using `by rw [h1]`.

Establish `h4 : ∀ Y : Matrix (Fin n) (Fin n) M, Bi * (B * Y * Bi) * B = Y` using `fun Y => by`. Combine the equalities or inequalities in the displayed calculation. Simplify `h3` using `only [F, h4]`. Use `Units.ext ?_` and prove the remaining obligations. Use extensionality with `i j`.

Conclude with `f.injective (congrFun (congrFun h2 i) j)`.
-/
theorem finite_torsion_centralizer : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (N : GL (Fin n) E), N.val.charpoly.Separable →
  {g : GL (Fin n) E | g * N = N * g ∧ IsOfFinOrder g}.Finite := by
  intro E _ _ n N hsep
  let M := N.val.charpoly.SplittingField
  haveI : NumberField M := NumberField.of_module_finite E M
  let f : E →+* M := algebraMap E M
  let A : Matrix (Fin n) (Fin n) M := N.val.map f
  have hA : A.charpoly = N.val.charpoly.map f := charpoly_map _ _
  have hs : A.charpoly.Separable := by rw [hA]; exact hsep.map
  have hsp : A.charpoly.Splits := by rw [hA]; exact SplittingField.splits _
  obtain ⟨z, hz, hprod⟩ := exists_distinct_roots A hs hsp
  obtain ⟨x, hx⟩ := GlobalTheory.Orb.IsRegSS.exists_conj (M := A) (N := diagonal z) hs
    (by rw [charpoly_diagonal, hprod])
  let B : Matrix (Fin n) (Fin n) M := x.val
  let Bi : Matrix (Fin n) (Fin n) M := (x⁻¹).val
  have hBB : B * Bi = 1 := by simp [B, Bi]
  have hBB' : Bi * B = 1 := by simp [B, Bi]
  have hx' : diagonal z * B = B * A := hx
  have hx2 : Bi * diagonal z = A * Bi := by
    calc Bi * diagonal z = Bi * (diagonal z * B) * Bi := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, hBB, Matrix.mul_one]
      _ = A * Bi := by rw [hx', ← Matrix.mul_assoc, hBB', Matrix.one_mul]
  let F : GL (Fin n) E → Matrix (Fin n) (Fin n) M := fun g => B * g.val.map f * Bi
  have hFc : ∀ g : GL (Fin n) E, g * N = N * g → F g * diagonal z = diagonal z * F g := by
    intro g hg
    have h1 : g.val * N.val = N.val * g.val := congrArg Units.val hg
    have h2 : g.val.map f * A = A * g.val.map f := by
      simp only [A]
      rw [← Matrix.map_mul, ← Matrix.map_mul, h1]
    simp only [F]
    calc B * g.val.map f * Bi * diagonal z = B * (g.val.map f * A) * Bi := by
          rw [Matrix.mul_assoc, hx2, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc]
      _ = diagonal z * (B * g.val.map f * Bi) := by
          rw [h2, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← hx', Matrix.mul_assoc, Matrix.mul_assoc,
            Matrix.mul_assoc, Matrix.mul_assoc]
  have hFpow : ∀ (g : GL (Fin n) E) (k : ℕ), F g ^ k = F (g ^ k) := by
    intro g k
    induction k with
    | zero => simp [F, hBB, Matrix.map_one, Matrix.mul_one]
    | succ k ih =>
      rw [pow_succ, ih, pow_succ]
      simp only [F, Units.val_mul]
      rw [Matrix.map_mul]
      calc B * (g ^ k).val.map f * Bi * (B * g.val.map f * Bi)
          = B * (g ^ k).val.map f * (Bi * B) * g.val.map f * Bi := by
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [hBB', Matrix.mul_one]; simp only [Matrix.mul_assoc]
  let φ : GL (Fin n) E → Fin n → M := fun g i => F g i i
  have hfin := Set.Finite.pi' fun _ : Fin n => finite_roots_of_unity M
  refine Set.Finite.of_injOn (f := φ) ?_ ?_ hfin
  · rintro g ⟨hg, ho⟩ i
    obtain ⟨k, hk, hgk⟩ := isOfFinOrder_iff_pow_eq_one.1 ho
    refine ⟨k, hk, ?_⟩
    have h1 : F g ^ k = 1 := by
      rw [hFpow, hgk]; simp [F, hBB, Matrix.map_one]
    rw [eq_diagonal_of_commute hz (hFc g hg), diagonal_pow] at h1
    have h2 := congrFun (congrFun h1 i) i
    simpa [φ] using h2
  · rintro g ⟨hg, -⟩ g' ⟨hg', -⟩ e
    have h1 : F g = F g' := by
      rw [eq_diagonal_of_commute hz (hFc g hg), eq_diagonal_of_commute hz (hFc g' hg')]
      exact congrArg diagonal e
    have h2 : g.val.map f = g'.val.map f := by
      have h3 : Bi * F g * B = Bi * F g' * B := by rw [h1]
      have h4 : ∀ Y : Matrix (Fin n) (Fin n) M, Bi * (B * Y * Bi) * B = Y := fun Y => by
        calc Bi * (B * Y * Bi) * B = (Bi * B) * Y * (Bi * B) := by simp only [Matrix.mul_assoc]
          _ = Y := by rw [hBB', Matrix.one_mul, Matrix.mul_one]
      simpa only [F, h4] using h3
    refine Units.ext ?_
    ext i j
    exact f.injective (congrFun (congrFun h2 i) j)

end GlobalTheory.CompanionTheory.TorCent
