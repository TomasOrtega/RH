import Mathlib
import GroundTheory.LocalFields.FiniteExtension
import GroundTheory.LocalFields.Eisenstein
import GroundTheory.LocalFields.SeparableClosure
import GroundTheory.LocalFields.UnramifiedExistence
import GroundTheory.LocalFields.MaximalUnramified
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open Polynomial IntermediateField ValuativeRel

namespace GroundTheory.LocalField

section Normed

variable {L : Type*} [NontriviallyNormedField L]

/- English proof (translation)
Assume the negation of the conclusion as `h`. Use `push Not at h`. Use `set e := g.natDegree`. Establish `hsum : aeval x g = x ^ e + ∑ i ∈ Finset.range e, algebraMap L C (g.coeff i) * x ^ i`. Rewrite using `[aeval_eq_sum_range, Finset.sum_range_succ, hg.coeff_natDegree, one_smul, add_comm]`.

Simplify using `only [Algebra.smul_def]`. Both sides reduce to the same expression. Establish `hx0 : x ≠ 0`. Introduce and unpack `rfl`. Rewrite `h` using `[norm_zero]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `h1 : ‖∑ i ∈ Finset.range e, algebraMap L C (g.coeff i) * x ^ i‖ < ‖x ^ e‖`. Break down `(Finset.range e).eq_empty_or_nonempty with he | he` into its components or cases. Rewrite using `[he, Finset.sum_empty, norm_zero, norm_pow]`. Conclude with `pow_pos (norm_pos_iff.2 hx0) _`.

Take `⟨i, hi, hle⟩` from `IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty he (fun i ↦ algebraMap L C (g.coeff i) * x ^ i)`. Use `hle.trans_lt ?_` and prove the remaining obligations. Rewrite using `[norm_mul, norm_algebraMap', norm_pow, norm_pow]`. Combine the equalities or inequalities in the displayed calculation. Conclude with `hc i`.

Use `_ < ‖x‖ ^ e := by`. Rewrite using `[one_mul]`. Conclude with `pow_lt_pow_right₀ h (Finset.mem_range.1 hi)`. Establish `h2 : x ^ e = -∑ i ∈ Finset.range e, algebraMap L C (g.coeff i) * x ^ i`. Rewrite `hx` using `[hsum]`.

Conclude with `eq_neg_of_add_eq_zero_left hx`. Rewrite `h1` using `[h2, norm_neg]`. Conclude with `lt_irrefl _ h1`.
-/
theorem norm_le_one_of_aeval_eq_zero {C : Type*} [NormedField C] [IsUltrametricDist C]
    [NormedAlgebra L C] {g : L[X]} (hg : g.Monic) (hc : ∀ i, ‖g.coeff i‖ ≤ 1) {x : C}
    (hx : aeval x g = 0) : ‖x‖ ≤ 1 := by
  by_contra h
  push Not at h
  set e := g.natDegree
  have hsum : aeval x g = x ^ e + ∑ i ∈ Finset.range e, algebraMap L C (g.coeff i) * x ^ i := by
    rw [aeval_eq_sum_range, Finset.sum_range_succ, hg.coeff_natDegree, one_smul, add_comm]
    simp only [Algebra.smul_def]
    rfl
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [norm_zero] at h
    linarith
  have h1 : ‖∑ i ∈ Finset.range e, algebraMap L C (g.coeff i) * x ^ i‖ < ‖x ^ e‖ := by
    rcases (Finset.range e).eq_empty_or_nonempty with he | he
    · rw [he, Finset.sum_empty, norm_zero, norm_pow]
      exact pow_pos (norm_pos_iff.2 hx0) _
    · obtain ⟨i, hi, hle⟩ := IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty he
        (fun i ↦ algebraMap L C (g.coeff i) * x ^ i)
      refine hle.trans_lt ?_
      rw [norm_mul, norm_algebraMap', norm_pow, norm_pow]
      calc ‖g.coeff i‖ * ‖x‖ ^ i ≤ 1 * ‖x‖ ^ i := by
            gcongr
            exact hc i
        _ < ‖x‖ ^ e := by
            rw [one_mul]
            exact pow_lt_pow_right₀ h (Finset.mem_range.1 hi)
  have h2 : x ^ e = -∑ i ∈ Finset.range e, algebraMap L C (g.coeff i) * x ^ i := by
    rw [hsum] at hx
    exact eq_neg_of_add_eq_zero_left hx
  rw [h2, norm_neg] at h1
  exact lt_irrefl _ h1

variable [CompleteSpace L] [IsUltrametricDist L]

/- English proof (translation)
Set `C` to `AlgebraicClosure L`. Set `: NontriviallyNormedField C` to `spectralNorm.nontriviallyNormedField L C`. Set `: NormedAlgebra L C` to `spectralNorm.normedAlgebra L C`. Establish `: IsUltrametricDist C` using `IsUltrametricDist.of_normedAlgebra L`. Use `set R : Finset C := (f.map (algebraMap L C)).roots.toFinset with hR`.

Use `set D : Finset ℝ := ((R ×ˢ R).filter (fun p ↦ p.1 ≠ p.2)).image (fun p ↦ ‖p.1 - p.2‖) with hD`. Use `set r : ℝ := if h : D.Nonempty then D.min' h else 1 with hr_def`. Establish `hDpos : ∀ d ∈ D, 0 < d`. Introduce `d hd`. Take `⟨⟨a, b⟩, hab, rfl⟩` from `Finset.mem_image.1 hd`.

Conclude with `norm_pos_iff.2 (sub_ne_zero.2 (Finset.mem_filter.1 hab).2)`. Establish `hr : 0 < r`. Rewrite using `[hr_def]`. Use `split_ifs with h`. Conclude with `hDpos _ (D.min'_mem h)`.

Conclude with `one_pos`. Establish `hrle : ∀ a ∈ R, ∀ b ∈ R, a ≠ b → r ≤ ‖a - b‖`. Introduce `a ha b hb hab`. Establish `hmem : ‖a - b‖ ∈ D` using `Finset.mem_image.2 ⟨(a, b), Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨ha, hb⟩, hab⟩, rfl⟩`. Rewrite using `[hr_def, dif_pos ⟨_, hmem⟩]`.

Conclude with `D.min'_le _ hmem`. Use `⟨r ^ f.natDegree, pow_pos hr _, ?_⟩` and prove the remaining obligations. Introduce `g hgm hdeg hgc hclose β hβ`. Establish `hβint : IsIntegral L β` using `⟨g, hgm, by rwa [← aeval_def]⟩`. Establish `: FiniteDimensional L L⟮β⟯` using `adjoin.finiteDimensional hβint`.

Set `ψ : L⟮β⟯ →ₐ[L] C` to `IsAlgClosed.lift`. Use `set β' : C := ψ (AdjoinSimple.gen L β) with hβ'_def`. Establish `hgen : aeval (AdjoinSimple.gen L β) g = 0`. Apply `(algebraMap L⟮β⟯ Ω').injective` to reduce the goal to its premises. Rewrite using `[← aeval_algebraMap_apply, IntermediateField.algebraMap_apply, AdjoinSimple.coe_gen, hβ, map_zero]`.

Establish `hβ' : aeval β' g = 0`. Rewrite using `[hβ'_def, aeval_algHom_apply, hgen, map_zero]`. Establish `hnorm : ‖β'‖ ≤ 1` using `norm_le_one_of_aeval_eq_zero hgm hgc hβ'`. Establish `hsmall : ‖aeval β' f‖ < r ^ f.natDegree`. Establish `hfg : aeval β' f = aeval β' (f - g)` using `by rw [map_sub, hβ', sub_zero]`.

Establish `hdeg' : (f - g).natDegree < f.natDegree + 1` using `Nat.lt_succ_of_le ((natDegree_sub_le f g).trans (by rw [hdeg, max_self]))`. Rewrite using `[hfg, aeval_eq_sum_range' hdeg']`. Take `⟨i, -, hle⟩` from `IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty ⟨0, Finset.mem_range.2 (Nat.succ_pos _)⟩ (fun i ↦ (f - g).coeff i • β' ^ i)`. Use `hle.trans_lt ?_` and prove the remaining obligations. Rewrite using `[Algebra.smul_def, norm_mul, norm_algebraMap', norm_pow, coeff_sub, norm_sub_rev]`.

Combine the equalities or inequalities in the displayed calculation. Conclude with `pow_le_one₀ (norm_nonneg _) hnorm`. Use `_ < r ^ f.natDegree := by rw [mul_one]; exact hclose i`. Establish `hsplit : (f.map (algebraMap L C)).Splits` using `IsAlgClosed.splits _`. Establish `hnodup : (f.map (algebraMap L C)).roots.Nodup` using `nodup_roots (hsep.map)`.

Establish `hcard : R.card = f.natDegree`. Rewrite using `[hR, Multiset.toFinset_card_of_nodup hnodup, ← hsplit.natDegree_eq_card_roots, natDegree_map]`. Establish `heval : aeval β' f = ∏ a ∈ R, (β' - a)`. Rewrite using `[aeval_def, eval₂_eq_eval_map, hsplit.eval_eq_prod_roots_of_monic (hm.map _), hR, Finset.prod_eq_multiset_prod, Multiset.toFinset_val, hnodup.dedup]`. Choose the witnesses or unpack the hypotheses as in `⟨a, haR, ha⟩ : ∃ a ∈ R, ‖β' - a‖ < r := by`.

Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Establish `: r ^ f.natDegree ≤ ‖aeval β' f‖`. Rewrite using `[heval, norm_prod, ← hcard, ← Finset.prod_const]`. Conclude with `Finset.prod_le_prod (fun _ _ ↦ hr.le) hcon`.

Conclude with `absurd hsmall (not_lt.2 this)`. Establish `hfC : f.map (algebraMap L C) ≠ 0` using `(hm.map _).ne_zero`. Establish `haroot : aeval a f = 0`. Use `(mem_roots hfC).1 (Multiset.mem_toFinset.1 haR)` as an intermediate fact. Rewrite `this` using `[IsRoot, eval_map_algebraMap]`. Then use the resulting hypothesis.

Establish `hmin : minpoly L a = f` using `(minpoly.eq_of_irreducible_of_monic hirr haroot hm).symm`. Establish `hkr : a ∈ L⟮β'⟯`. Use `IsKrasner.krasner (by rw [hmin]; exact hsep) (by rw [hmin]; exact IsAlgClosed.splits _) (Algebra.IsIntegral.isIntegral β') (fun x' hx' hne ↦ ?_)` and prove the remaining obligations. Establish `hx'root : aeval x' f = 0`. Rewrite using `[← hmin, isConjRoot_def.1 hx']`.

Conclude with `minpoly.aeval L x'`. Establish `hx'R : x' ∈ R`. Rewrite using `[hR, Multiset.mem_toFinset, mem_roots hfC, IsRoot, eval_map_algebraMap]`. Conclude with `hx'root`. Rewrite using `[norm_sub_rev]`.

Conclude with `ha.trans_le (hrle a haR x' hx'R hne)`. Establish `hrange : L⟮β'⟯ ≤ ψ.fieldRange` using `adjoin_simple_le_iff.2 (AlgHom.mem_fieldRange.2 ⟨_, rfl⟩)`. Take `⟨y, hy⟩` from `AlgHom.mem_fieldRange.1 (hrange hkr)`. Establish `hy0 : aeval y f = 0`. Establish `h' : ψ (aeval y f) = 0` using `by rw [← aeval_algHom_apply, hy, haroot]`.

Simplify using `using h'`. Establish `hα : aeval (y : Ω') f = 0`. Use `aeval_algebraMap_apply Ω' y f` as an intermediate fact. Rewrite `this` using `[hy0, map_zero]`. Conclude with `this`.

Use `⟨(y : Ω'), hα, ?_⟩` and prove the remaining obligations. Establish `hαint : IsIntegral L (y : Ω')` using `⟨f, hm, by rwa [← aeval_def]⟩`. Use `eq_of_le_of_finrank_le (adjoin_simple_le_iff.2 y.2) ?_` and prove the remaining obligations. Rewrite using `[adjoin.finrank hβint, adjoin.finrank hαint, ← minpoly.eq_of_irreducible_of_monic hirr hα hm, ← hdeg]`. Conclude with `natDegree_le_natDegree (minpoly.degree_le_of_ne_zero L β hgm.ne_zero hβ)`.
-/
theorem exists_adjoin_eq_of_norm_coeff_sub_lt (f : L[X]) (hm : f.Monic) (hirr : Irreducible f)
    (hsep : f.Separable) (Ω' : Type*) [Field Ω'] [Algebra L Ω'] :
    ∃ ε : ℝ, 0 < ε ∧ ∀ g : L[X], g.Monic → g.natDegree = f.natDegree → (∀ i, ‖g.coeff i‖ ≤ 1) →
      (∀ i, ‖g.coeff i - f.coeff i‖ < ε) → ∀ β : Ω', aeval β g = 0 →
        ∃ α : Ω', aeval α f = 0 ∧ L⟮α⟯ = L⟮β⟯ := by
  classical
  let C := AlgebraicClosure L
  let : NontriviallyNormedField C := spectralNorm.nontriviallyNormedField L C
  let : NormedAlgebra L C := spectralNorm.normedAlgebra L C
  have : IsUltrametricDist C := IsUltrametricDist.of_normedAlgebra L
  set R : Finset C := (f.map (algebraMap L C)).roots.toFinset with hR
  set D : Finset ℝ := ((R ×ˢ R).filter (fun p ↦ p.1 ≠ p.2)).image (fun p ↦ ‖p.1 - p.2‖) with hD
  set r : ℝ := if h : D.Nonempty then D.min' h else 1 with hr_def
  have hDpos : ∀ d ∈ D, 0 < d := by
    intro d hd
    obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.1 hd
    exact norm_pos_iff.2 (sub_ne_zero.2 (Finset.mem_filter.1 hab).2)
  have hr : 0 < r := by
    rw [hr_def]
    split_ifs with h
    · exact hDpos _ (D.min'_mem h)
    · exact one_pos
  have hrle : ∀ a ∈ R, ∀ b ∈ R, a ≠ b → r ≤ ‖a - b‖ := by
    intro a ha b hb hab
    have hmem : ‖a - b‖ ∈ D :=
      Finset.mem_image.2 ⟨(a, b), Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨ha, hb⟩, hab⟩, rfl⟩
    rw [hr_def, dif_pos ⟨_, hmem⟩]
    exact D.min'_le _ hmem
  refine ⟨r ^ f.natDegree, pow_pos hr _, ?_⟩
  intro g hgm hdeg hgc hclose β hβ
  have hβint : IsIntegral L β := ⟨g, hgm, by rwa [← aeval_def]⟩
  have : FiniteDimensional L L⟮β⟯ := adjoin.finiteDimensional hβint
  let ψ : L⟮β⟯ →ₐ[L] C := IsAlgClosed.lift
  set β' : C := ψ (AdjoinSimple.gen L β) with hβ'_def
  have hgen : aeval (AdjoinSimple.gen L β) g = 0 := by
    apply (algebraMap L⟮β⟯ Ω').injective
    rw [← aeval_algebraMap_apply, IntermediateField.algebraMap_apply, AdjoinSimple.coe_gen, hβ,
      map_zero]
  have hβ' : aeval β' g = 0 := by
    rw [hβ'_def, aeval_algHom_apply, hgen, map_zero]
  have hnorm : ‖β'‖ ≤ 1 := norm_le_one_of_aeval_eq_zero hgm hgc hβ'

  have hsmall : ‖aeval β' f‖ < r ^ f.natDegree := by
    have hfg : aeval β' f = aeval β' (f - g) := by rw [map_sub, hβ', sub_zero]
    have hdeg' : (f - g).natDegree < f.natDegree + 1 :=
      Nat.lt_succ_of_le ((natDegree_sub_le f g).trans (by rw [hdeg, max_self]))
    rw [hfg, aeval_eq_sum_range' hdeg']
    obtain ⟨i, -, hle⟩ := IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty
      ⟨0, Finset.mem_range.2 (Nat.succ_pos _)⟩ (fun i ↦ (f - g).coeff i • β' ^ i)
    refine hle.trans_lt ?_
    rw [Algebra.smul_def, norm_mul, norm_algebraMap', norm_pow, coeff_sub, norm_sub_rev]
    calc ‖g.coeff i - f.coeff i‖ * ‖β'‖ ^ i ≤ ‖g.coeff i - f.coeff i‖ * 1 := by
          gcongr
          exact pow_le_one₀ (norm_nonneg _) hnorm
      _ < r ^ f.natDegree := by rw [mul_one]; exact hclose i

  have hsplit : (f.map (algebraMap L C)).Splits := IsAlgClosed.splits _
  have hnodup : (f.map (algebraMap L C)).roots.Nodup := nodup_roots (hsep.map)
  have hcard : R.card = f.natDegree := by
    rw [hR, Multiset.toFinset_card_of_nodup hnodup, ← hsplit.natDegree_eq_card_roots,
      natDegree_map]
  have heval : aeval β' f = ∏ a ∈ R, (β' - a) := by
    rw [aeval_def, eval₂_eq_eval_map, hsplit.eval_eq_prod_roots_of_monic (hm.map _), hR,
      Finset.prod_eq_multiset_prod, Multiset.toFinset_val, hnodup.dedup]
  obtain ⟨a, haR, ha⟩ : ∃ a ∈ R, ‖β' - a‖ < r := by
    by_contra hcon
    push Not at hcon
    have : r ^ f.natDegree ≤ ‖aeval β' f‖ := by
      rw [heval, norm_prod, ← hcard, ← Finset.prod_const]
      exact Finset.prod_le_prod (fun _ _ ↦ hr.le) hcon
    exact absurd hsmall (not_lt.2 this)
  have hfC : f.map (algebraMap L C) ≠ 0 := (hm.map _).ne_zero
  have haroot : aeval a f = 0 := by
    have := (mem_roots hfC).1 (Multiset.mem_toFinset.1 haR)
    rwa [IsRoot, eval_map_algebraMap] at this
  have hmin : minpoly L a = f := (minpoly.eq_of_irreducible_of_monic hirr haroot hm).symm

  have hkr : a ∈ L⟮β'⟯ := by
    refine IsKrasner.krasner (by rw [hmin]; exact hsep) (by rw [hmin]; exact IsAlgClosed.splits _)
      (Algebra.IsIntegral.isIntegral β') (fun x' hx' hne ↦ ?_)
    have hx'root : aeval x' f = 0 := by
      rw [← hmin, isConjRoot_def.1 hx']
      exact minpoly.aeval L x'
    have hx'R : x' ∈ R := by
      rw [hR, Multiset.mem_toFinset, mem_roots hfC, IsRoot, eval_map_algebraMap]
      exact hx'root
    rw [norm_sub_rev]
    exact ha.trans_le (hrle a haR x' hx'R hne)

  have hrange : L⟮β'⟯ ≤ ψ.fieldRange := adjoin_simple_le_iff.2 (AlgHom.mem_fieldRange.2 ⟨_, rfl⟩)
  obtain ⟨y, hy⟩ := AlgHom.mem_fieldRange.1 (hrange hkr)
  have hy0 : aeval y f = 0 := by
    have h' : ψ (aeval y f) = 0 := by rw [← aeval_algHom_apply, hy, haroot]
    simpa using h'
  have hα : aeval (y : Ω') f = 0 := by
    have := aeval_algebraMap_apply Ω' y f
    rw [hy0, map_zero] at this
    exact this
  refine ⟨(y : Ω'), hα, ?_⟩
  have hαint : IsIntegral L (y : Ω') := ⟨f, hm, by rwa [← aeval_def]⟩
  refine eq_of_le_of_finrank_le (adjoin_simple_le_iff.2 y.2) ?_
  rw [adjoin.finrank hβint, adjoin.finrank hαint,
    ← minpoly.eq_of_irreducible_of_monic hirr hα hm, ← hdeg]
  exact natDegree_le_natDegree (minpoly.degree_le_of_ne_zero L β hgm.ne_zero hβ)

end Normed

section MonicOfCoeffs

variable {R : Type*} [CommRing R]

def monicOfCoeffs {n : ℕ} (c : Fin n → R) : R[X] := X ^ n + ∑ i : Fin n, C (c i) * X ^ (i : ℕ)

/- English proof (translation)
Rewrite using `[finsetSum_coeff]`. Simplify using `only [coeff_C_mul_X_pow]`. Use `split_ifs with h`. Rewrite using `[Finset.sum_eq_single ⟨k, h⟩ (fun j _ hj ↦ if_neg fun hk ↦ hj (Fin.ext hk.symm)) (fun h' ↦ absurd (Finset.mem_univ _) h'), if_pos rfl]`. Conclude with `Finset.sum_eq_zero fun j _ ↦ if_neg fun (hk : k = (j : ℕ)) ↦ h (hk ▸ j.2)`.
-/
theorem coeff_sum_fin_C_mul_X_pow {n : ℕ} (c : Fin n → R) (k : ℕ) :
    (∑ i : Fin n, C (c i) * X ^ (i : ℕ)).coeff k = if h : k < n then c ⟨k, h⟩ else 0 := by
  classical
  rw [finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨k, h⟩ (fun j _ hj ↦ if_neg fun hk ↦ hj (Fin.ext hk.symm))
      (fun h' ↦ absurd (Finset.mem_univ _) h'), if_pos rfl]
  · exact Finset.sum_eq_zero fun j _ ↦ if_neg fun (hk : k = (j : ℕ)) ↦ h (hk ▸ j.2)

/- English proof (translation)
The claim follows from `monic_X_pow_add (degree_sum_fin_lt c)`.
-/
theorem monic_monicOfCoeffs {n : ℕ} (c : Fin n → R) : (monicOfCoeffs c).Monic :=
  monic_X_pow_add (degree_sum_fin_lt c)

/- English proof (translation)
Rewrite using `[monicOfCoeffs, natDegree_add_eq_left_of_degree_lt (by rw [degree_X_pow]; exact degree_sum_fin_lt c), natDegree_X_pow]`.
-/
theorem natDegree_monicOfCoeffs [Nontrivial R] {n : ℕ} (c : Fin n → R) :
    (monicOfCoeffs c).natDegree = n := by
  rw [monicOfCoeffs, natDegree_add_eq_left_of_degree_lt (by rw [degree_X_pow]; exact degree_sum_fin_lt c),
    natDegree_X_pow]

/- English proof (translation)
Use `conv_lhs => rw [hg.as_sum, hn]`. Rewrite using `[monicOfCoeffs, Fin.sum_univ_eq_sum_range (fun i ↦ C (g.coeff i) * X ^ i) n]`.
-/
theorem eq_monicOfCoeffs {g : R[X]} (hg : g.Monic) {n : ℕ} (hn : g.natDegree = n) :
    g = monicOfCoeffs (fun i : Fin n ↦ g.coeff i) := by
  conv_lhs => rw [hg.as_sum, hn]
  rw [monicOfCoeffs, Fin.sum_univ_eq_sum_range (fun i ↦ C (g.coeff i) * X ^ i) n]

/- English proof (translation)
Rewrite using `[monicOfCoeffs, monicOfCoeffs, add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]`. Simplify using `only [C_sub, sub_mul]`.
-/
theorem monicOfCoeffs_sub_monicOfCoeffs {n : ℕ} (c d : Fin n → R) :
    monicOfCoeffs c - monicOfCoeffs d = ∑ i : Fin n, C (c i - d i) * X ^ (i : ℕ) := by
  rw [monicOfCoeffs, monicOfCoeffs, add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
  simp only [C_sub, sub_mul]

end MonicOfCoeffs

section Eisenstein

variable {L : Type*} [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]

end Eisenstein

section Main

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

section Valued

variable {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω]

end Valued

variable (Ω : Type*) [Field Ω] [Algebra K Ω]

end Main

end GroundTheory.LocalField
