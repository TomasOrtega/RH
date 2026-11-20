import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurEqJtDet
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CauchyIdentitySchurFormalDegreeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MkSumProdHsymmMulProdOneSubStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EulerInversePowerSeriesEvalOneStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSumRegroupAntitonePartitionsByDegreeStatement

noncomputable section

namespace GlobalTheory.JSW

open Finset

/- English proof (translation)
Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Expand and normalize the polynomial expressions, which then agree. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem cauchy_local {m n : ℕ} (hmn : m ≤ n) (α : Fin n → ℂ) (β : Fin m → ℂ) (T : ℂ)
    (hs : Summable fun l : {l : Fin m → ℕ // Antitone l} =>
      ‖schurAt (padTo hmn l.1) α * schurAt l.1 β‖ * ‖T‖ ^ (∑ i, l.1 i)) :
    (∀ i j, 1 - α i * β j * T ≠ 0) ∧
    HasSum (fun l : {l : Fin m → ℕ // Antitone l} =>
      schurAt (padTo hmn l.1) α * schurAt l.1 β * T ^ (∑ i, l.1 i))
      (∏ i, ∏ j, (1 - α i * β j * T)⁻¹) := by
  set G : (Fin m → ℕ) → ℂ := fun l => schurAt (padTo hmn l) α * schurAt l β * T ^ (∑ i, l i) with hGdef
  have hG : Summable fun l : {l : Fin m → ℕ // Antitone l} => ‖G l.1‖ := by
    refine hs.congr fun l => ?_
    simp [G, norm_mul, norm_pow]
  obtain ⟨hsum, htrans⟩ := GlobalTheory.T.hasSum_regroup_antitonePartitions_by_degree G hG
  have hc : (fun d => ∑ l ∈ antiParts m d, G l) = fun d => T ^ d * ∑ k ∈ Finset.Nat.antidiagonalTuple m d,
      ∏ j, MvPolynomial.eval₂ (Int.castRingHom ℂ) α (MvPolynomial.hsymm (Fin n) ℤ (k j)) * β j ^ (k j) := by
    funext d
    rw [← GlobalTheory.T.cauchy_identity_schur_formal_degree hmn α β d, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l hl => ?_
    simp only [G]; rw [(mem_antiParts.1 hl).1]; ring
  have h5 := GlobalTheory.T.mk_sum_hsymm_mul_prod_one_sub_eq_one α β T
  rw [← hc] at h5
  obtain ⟨hne, hhas⟩ := GlobalTheory.T.eulerInverse_powerSeries_eval_one _ hsum (fun p : Fin n × Fin m => α p.1 * β p.2 * T) h5
  refine ⟨fun i j => ?_, ?_⟩
  · rw [Fintype.prod_prod_type] at hne
    exact Finset.prod_ne_zero_iff.1 (Finset.prod_ne_zero_iff.1 hne i (mem_univ _)) j (mem_univ _)
  · have := htrans _ hhas
    rw [← Finset.prod_inv_distrib, Fintype.prod_prod_type] at this
    exact this

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately.
-/
theorem multiset_prod_map_product_eq_prod_prod {X Y : Type} (A : Multiset X) (B : Multiset Y) (f : X × Y → ℂ) :
    ((A ×ˢ B).map f).prod = (A.map fun a => (B.map fun b => f (a, b)).prod).prod := by
  induction A using Multiset.induction_on with
  | empty => simp
  | cons a A ih => simp [Multiset.cons_product, ih]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Both sides reduce to the same expression.
-/
theorem locL_univ (q : ℕ) {m n : ℕ} (α : Fin n → ℂˣ) (β : Fin m → ℂˣ) (s : ℂ) :
    locL q (Finset.univ.val.map α) (Finset.univ.val.map β) s =
      ∏ i, ∏ j, (1 - (α i : ℂ) * β j * (q : ℂ) ^ (-s))⁻¹ := by
  rw [locL, multiset_prod_map_product_eq_prod_prod, Multiset.map_map]
  simp only [Multiset.map_map, Function.comp_def]
  rfl

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem cauchy_locL {m n : ℕ} (hmn : m ≤ n) (α : Fin n → ℂˣ) (β : Fin m → ℂˣ) (q : ℕ) (s : ℂ)
    (hs : Summable fun l : {l : Fin m → ℕ // Antitone l} =>
      ‖schurAt (padTo hmn l.1) (fun i => (α i : ℂ)) * schurAt l.1 (fun j => (β j : ℂ))‖ *
        ‖(q : ℂ) ^ (-s)‖ ^ (∑ i, l.1 i)) :
    HasSum (fun l : {l : Fin m → ℕ // Antitone l} => schurAt (padTo hmn l.1) (fun i => (α i : ℂ)) *
      schurAt l.1 (fun j => (β j : ℂ)) * ((q : ℂ) ^ (-s)) ^ (∑ i, l.1 i))
      (locL q (Finset.univ.val.map α) (Finset.univ.val.map β) s) := by
  rw [locL_univ]; exact (cauchy_local hmn _ _ _ hs).2

end GlobalTheory.JSW
