import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LinkExactAff
import Development.AutomorphicArithmetic.AutomorphicVarieties.TensorHomCubes.StabDirectedSystem
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.ExistsTransvectionPreservingLowAndAff
open GlobalTheory.SeqCx Matrix UpperTheory.V.KL

namespace GlobalTheory

/- English proof (translation)
Introduce `R _ s hs n hn v hv`. Take `⟨F, hF⟩` from `hv`. Set `f` to `F ⟨0, by simp⟩`. Establish `hfv : f v = 1`. Use `hF ⟨0, by simp⟩ ⟨0, by simp⟩` as an intermediate fact.

Simplify `this` using `[f]`. Set `a : Fin n → R` to `fun i => f (Finsupp.single (i : ℕ) 1)`. Set `h : (ℕ →₀ R) →ₗ[R] R` to `f - ∑ i : Fin n, a i • Finsupp.lapply (i : ℕ)`. Establish `hh : ∀ x, h x = f x - ∑ i : Fin n, a i * x i`. Introduce `x`.

Simplify using `[h]`. Set `r : Fin (n + 1) → R` to `Fin.snoc (fun i : Fin n => v i) (h v)`. Establish `hr : Unimodular R r`. Rewrite using `[Unimodular, Ideal.eq_top_iff_one]`. Establish `e : (1:R) = ∑ i : Fin n, a i * r i.castSucc + 1 * r (Fin.last n)`.

Simplify using `only [r, Fin.snoc_castSucc, Fin.snoc_last, hh, hfv, one_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Use `Ideal.add_mem _ (Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨_, rfl⟩)) (Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨_, rfl⟩))` and prove the remaining obligations. Take `⟨t', ht'⟩` from `hs n hn r hr`.

Simplify using `only [r, Fin.snoc_castSucc, Fin.snoc_last] at ht'`. Set `t : ℕ →₀ R` to `∑ j : Fin n, Finsupp.single (j : ℕ) (t' j)`. Establish `htapp : ∀ k, t k = if hk : k < n then t' ⟨k, hk⟩ else 0`. Introduce `k`. Simplify using `only [t, Finsupp.finset_sum_apply, Finsupp.single_apply]`.

Use `split_ifs with hk`. Rewrite using `[Finset.sum_eq_single ⟨k, hk⟩]`. Simplify using the standard rewrite rules. Introduce `b _ hb`. Rewrite using `[if_neg]`.

Introduce `e`. Apply `hb` to reduce the goal to its premises. Use `ext`. Conclude with `e`. Simplify using the standard rewrite rules.

Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `b _`. Rewrite using `[if_neg]`. Introduce `e`. Apply `hk` to reduce the goal to its premises.

Rewrite using `[← e]`. Conclude with `b.2`. Establish `htlow : t ∈ low R n` using `fun k hk => by rw [htapp, dif_neg (by omega)]`. Establish `htlow' : t ∈ low R (n + 1)` using `fun k hk => htlow k (by omega)`. Establish `hht : h t = 0`.

Rewrite using `[hh]`. Establish `h1 : f t = ∑ j : Fin n, t' j * a j`. Simplify using `only [t, map_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[← Finsupp.smul_single_one, map_smul, smul_eq_mul]`.

Establish `h2 : ∑ i : Fin n, a i * t i = ∑ j : Fin n, t' j * a j`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[htapp, dif_pos j.2, mul_comm]`. Rewrite using `[h1, h2, sub_self]`. Take `⟨ψ1, hψ1, hψ1l, hψ1a⟩` from `GlobalTheory.T.exists_transvection_preserving_low_and_aff R (n + 1) h t htlow' hht`.

Establish `hv' : ∀ i : Fin n, ψ1 v i = v i + t' i * h v`. Introduce `i`. Rewrite using `[hψ1, Finsupp.add_apply, Finsupp.smul_apply, htapp, dif_pos i.2, smul_eq_mul, mul_comm]`. Establish `hv'n : ψ1 v n = v n`. Rewrite using `[hψ1, Finsupp.add_apply, Finsupp.smul_apply, htapp, dif_neg (lt_irrefl n), smul_zero, add_zero]`.

Establish `hmem : (1 - v n) ∈ Ideal.span (Set.range fun i : Fin n => v i + t' i * h v)`. Rewrite using `[ht']`. Discharge the goal by the elementary cases of `trivial`. Take `⟨c, hc⟩` from `(Ideal.mem_span_range_iff_exists_fun).1 hmem`. Set `h2 : (ℕ →₀ R) →ₗ[R] R` to `∑ i : Fin n, c i • Finsupp.lapply (i : ℕ)`.

Establish `hh2 : ∀ x, h2 x = ∑ i : Fin n, c i * x i`. Introduce `x`. Simplify using `[h2]`. Establish `ht2low : Finsupp.single n (1 : R) ∈ low R (n + 1)` using `fun k hk => by`. Rewrite using `[Finsupp.single_apply, if_neg (by omega)]`.

Establish `hht2 : h2 (Finsupp.single n 1) = 0`. Rewrite using `[hh2]`. Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations. Use `i.2` as an intermediate fact. Rewrite using `[Finsupp.single_apply, if_neg (by omega), mul_zero]`.

Take `⟨ψ2, hψ2, hψ2l, hψ2a⟩` from `GlobalTheory.T.exists_transvection_preserving_low_and_aff R (n + 1) h2 _ ht2low hht2`. Use `⟨ψ1.trans ψ2, fun x => ?_, fun j x => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[LinearEquiv.trans_apply, hψ2l, hψ1l]`. Rewrite using `[LinearEquiv.trans_apply, hψ2a, hψ1a]`. Rewrite using `[LinearEquiv.trans_apply, hψ2, Finsupp.add_apply, Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul, mul_one, hh2, hv'n]`.

Establish `: ∑ i : Fin n, c i * ψ1 v i = 1 - v n`. Rewrite using `[← hc]; exact Finset.sum_congr rfl fun i _ => by rw [hv' i]`. Rewrite using `[this]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem unimodular_to_coord_one : ∀ (R : Type) [CommRing R] (s : ℕ), StableRangeLe R s → ∀ (n : ℕ), s ≤ n →
    ∀ v : ℕ →₀ R, [v] ∈ uniM R (ℕ →₀ R) → ∃ ψ : (ℕ →₀ R) ≃ₗ[R] (ℕ →₀ R),
      (∀ x, ψ x ∈ low R (n + 1) ↔ x ∈ low R (n + 1)) ∧ (∀ j x, ψ x ∈ aff R (n + 1) j ↔ x ∈ aff R (n + 1) j) ∧
      ψ v n = 1 := by
  intro R _ s hs n hn v hv
  obtain ⟨F, hF⟩ := hv
  let f := F ⟨0, by simp⟩
  have hfv : f v = 1 := by
    have := hF ⟨0, by simp⟩ ⟨0, by simp⟩
    simpa [f] using this
  let a : Fin n → R := fun i => f (Finsupp.single (i : ℕ) 1)
  let h : (ℕ →₀ R) →ₗ[R] R := f - ∑ i : Fin n, a i • Finsupp.lapply (i : ℕ)
  have hh : ∀ x, h x = f x - ∑ i : Fin n, a i * x i := by
    intro x; simp [h]
  let r : Fin (n + 1) → R := Fin.snoc (fun i : Fin n => v i) (h v)
  have hr : Unimodular R r := by
    rw [Unimodular, Ideal.eq_top_iff_one]
    have e : (1:R) = ∑ i : Fin n, a i * r i.castSucc + 1 * r (Fin.last n) := by
      simp only [r, Fin.snoc_castSucc, Fin.snoc_last, hh, hfv, one_mul]
      ring
    rw [e]
    refine Ideal.add_mem _ (Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨_, rfl⟩))
      (Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨_, rfl⟩))
  obtain ⟨t', ht'⟩ := hs n hn r hr
  simp only [r, Fin.snoc_castSucc, Fin.snoc_last] at ht'
  let t : ℕ →₀ R := ∑ j : Fin n, Finsupp.single (j : ℕ) (t' j)
  have htapp : ∀ k, t k = if hk : k < n then t' ⟨k, hk⟩ else 0 := by
    intro k
    simp only [t, Finsupp.finset_sum_apply, Finsupp.single_apply]
    split_ifs with hk
    · rw [Finset.sum_eq_single ⟨k, hk⟩]
      · simp
      · intro b _ hb; rw [if_neg]; intro e; apply hb; ext; exact e
      · simp
    · apply Finset.sum_eq_zero; intro b _; rw [if_neg]; intro e; apply hk; rw [← e]; exact b.2
  have htlow : t ∈ low R n := fun k hk => by rw [htapp, dif_neg (by omega)]
  have htlow' : t ∈ low R (n + 1) := fun k hk => htlow k (by omega)
  have hht : h t = 0 := by
    rw [hh]
    have h1 : f t = ∑ j : Fin n, t' j * a j := by
      simp only [t, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← Finsupp.smul_single_one, map_smul, smul_eq_mul]
    have h2 : ∑ i : Fin n, a i * t i = ∑ j : Fin n, t' j * a j := by
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [htapp, dif_pos j.2, mul_comm]
    rw [h1, h2, sub_self]
  obtain ⟨ψ1, hψ1, hψ1l, hψ1a⟩ := GlobalTheory.T.exists_transvection_preserving_low_and_aff R (n + 1) h t htlow' hht
  have hv' : ∀ i : Fin n, ψ1 v i = v i + t' i * h v := by
    intro i
    rw [hψ1, Finsupp.add_apply, Finsupp.smul_apply, htapp, dif_pos i.2, smul_eq_mul, mul_comm]
  have hv'n : ψ1 v n = v n := by
    rw [hψ1, Finsupp.add_apply, Finsupp.smul_apply, htapp, dif_neg (lt_irrefl n), smul_zero, add_zero]
  have hmem : (1 - v n) ∈ Ideal.span (Set.range fun i : Fin n => v i + t' i * h v) := by
    rw [ht']; trivial
  obtain ⟨c, hc⟩ := (Ideal.mem_span_range_iff_exists_fun).1 hmem
  let h2 : (ℕ →₀ R) →ₗ[R] R := ∑ i : Fin n, c i • Finsupp.lapply (i : ℕ)
  have hh2 : ∀ x, h2 x = ∑ i : Fin n, c i * x i := by
    intro x; simp [h2]
  have ht2low : Finsupp.single n (1 : R) ∈ low R (n + 1) := fun k hk => by
    rw [Finsupp.single_apply, if_neg (by omega)]
  have hht2 : h2 (Finsupp.single n 1) = 0 := by
    rw [hh2]
    refine Finset.sum_eq_zero fun i _ => ?_
    have := i.2
    rw [Finsupp.single_apply, if_neg (by omega), mul_zero]
  obtain ⟨ψ2, hψ2, hψ2l, hψ2a⟩ := GlobalTheory.T.exists_transvection_preserving_low_and_aff R (n + 1) h2 _ ht2low hht2
  refine ⟨ψ1.trans ψ2, fun x => ?_, fun j x => ?_, ?_⟩
  · rw [LinearEquiv.trans_apply, hψ2l, hψ1l]
  · rw [LinearEquiv.trans_apply, hψ2a, hψ1a]
  · rw [LinearEquiv.trans_apply, hψ2, Finsupp.add_apply, Finsupp.smul_apply, Finsupp.single_eq_same,
      smul_eq_mul, mul_one, hh2, hv'n]
    have : ∑ i : Fin n, c i * ψ1 v i = 1 - v n := by
      rw [← hc]; exact Finset.sum_congr rfl fun i _ => by rw [hv' i]
    rw [this]; ring

end GlobalTheory

section
open GlobalTheory.SeqCx Matrix UpperTheory.V.KL
/- English proof (translation)
Use `first`. Consider the case `exact @GlobalTheory.unimodular_to_coord_one`.
-/
theorem _root_.GlobalTheory.T.exists_automorphism_preserving_translates_coord_one : ∀ (R : Type) [CommRing R] (s : ℕ), StableRangeLe R s → ∀ (n : ℕ), s ≤ n → ∀ v : ℕ →₀ R, [v] ∈ uniM R (ℕ →₀ R) → ∃ ψ : (ℕ →₀ R) ≃ₗ[R] (ℕ →₀ R), (∀ x, ψ x ∈ low R (n + 1) ↔ x ∈ low R (n + 1)) ∧ (∀ j x, ψ x ∈ aff R (n + 1) j ↔ x ∈ aff R (n + 1) j) ∧ ψ v n = 1 := by
  first
  | exact @GlobalTheory.unimodular_to_coord_one
end
