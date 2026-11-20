import Formalism.LocalToGlobal.CharacterGerms.RowTiePKeyEigB

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

namespace RowTiePKeyEig

open RowTiePE0 RowTiePKey RowTiePProj GmExArith

variable {C : Type} [Field C] {V : VF C} {O : Type} [CommRing O] {n d : ℕ} (K : KeyData C V O n d)

/- English proof (translation)
The claim follows from `hT C V hc n d hd (Acl K) (fun _ ha _ hb => add_mem K ha hb) (fun _ ha => neg_mem K ha) (fun _ ha _ hb => mul_mem K ha hb) (fun _ ha _ hb => comm_mem K ha hb) (fun _ ha => int_mem K ha) (fun _ _ hs h => closed_mem K hs h) (fun _ ha => star_mem K ha) B hB`.
-/
theorem teich_acl (hT : TeichSt)
    (hc : ∀ s : ℕ → C, (∀ n : ℕ, V.Ge n (s (n + 1) - s n)) → ∃ x, ∀ n : ℕ, V.Ge n (x - s n)) (hd : d ≠ 0)
    {B : Matrix (Fin n) (Fin n) C} (hB : B ∈ Acl K) :
    ∃ τ ∈ Acl K, τ ^ V.l ^ d = τ ∧ ((V.l : C)⁻¹) • (B - τ) ∈ Acl K :=
  hT C V hc n d hd (Acl K) (fun _ ha _ hb => add_mem K ha hb) (fun _ ha => neg_mem K ha)
    (fun _ ha _ hb => mul_mem K ha hb) (fun _ ha _ hb => comm_mem K ha hb) (fun _ ha => int_mem K ha)
    (fun _ _ hs h => closed_mem K hs h) (fun _ ha => star_mem K ha) B hB

/- English proof (translation)
Distinguish the cases in `hw0 : w = 0`. Conclude with `⟨0, by rw [hw0, Matrix.mulVec_zero, smul_zero]⟩`. Establish `ht : ∀ b : {b // b ∈ Acl K}, ∃ τ : Matrix (Fin n) (Fin n) C, τ ∈ Acl K ∧ τ ^ V.l ^ d = τ ∧ ((V.l : C)⁻¹) • (b.1 - τ) ∈ Acl K`. Introduce `b`. Take `⟨τ, h1, h2, h3⟩` from `teich_acl K hT hc hd b.2`.

Conclude with `⟨τ, h1, h2, h3⟩`. Use `choose tf htf using ht`. Set `nx : {b // b ∈ Acl K} → {b // b ∈ Acl K}` to `fun b => ⟨((V.l : C)⁻¹) • (b.1 - tf b), (htf b).2.2⟩`. Set `bs : ℕ → {b // b ∈ Acl K}` to `fun k => nx^[k] ⟨B, hB⟩`. Establish `hl0 : (V.l : C) ≠ 0` using `V.l_ne_zero`.

Establish `hrel : ∀ k, (bs k).1 = tf (bs k) + (V.l : C) • (bs (k + 1)).1`. Introduce `k`. Use `show (bs k).1 = tf (bs k) + (V.l : C) • (nx^[k + 1] ⟨B, hB⟩).1`. Rewrite using `[Function.iterate_succ_apply']`. Use `show (bs k).1 = tf (bs k) + (V.l : C) • (((V.l : C)⁻¹) • ((bs k).1 - tf (bs k)))`.

Rewrite using `[smul_smul, mul_inv_cancel₀ hl0, one_smul]`. Normalize the expressions using the abelian group laws. Establish `hcs : ∀ k, ∃ c : C, Matrix.mulVec (tf (bs k)) w = c • w` using `fun k => hw _ (htf _).1 (htf _).2.1`. Use `choose cs hcs using hcs`. Establish `hcsi : ∀ k, V.Ge 0 (cs k)` using `fun k => eig_int (tf (bs k)) (int_mem K (htf _).1) w hw0 (cs k) (hcs k)`.

Set `σs : ℕ → C` to `fun K' => ∑ k ∈ Finset.range K', (V.l : C) ^ k * cs k`. Establish `hid : ∀ K', Matrix.mulVec B w = σs K' • w + ((V.l : C) ^ K') • Matrix.mulVec (bs K').1 w`. Introduce `K'`. Proceed by induction on `K' with`. Consider the case `zero => simp [σs, bs]`.

Consider the case `succ K' ih`. Rewrite using `[ih, hrel K', Matrix.add_mulVec, Matrix.smul_mulVec, hcs K', smul_add, smul_smul, smul_smul, ← add_assoc, ← add_smul, ← pow_succ]`. Simplify using `only [σs, Finset.sum_range_succ]`. Establish `hcau : ∀ N : ℕ, ∃ n0 : ℕ, ∀ m ≥ n0, V.Ge N (σs (m + 1) - σs m)`. Introduce `N`.

Use `⟨N, fun m hm => ?_⟩` and prove the remaining obligations. Simplify using `only [σs, Finset.sum_range_succ, add_sub_cancel_left]`. Use `(RowTiePKeyEig.ge_lpow (V := V) m).mul (hcsi m)` as an intermediate fact. Use `this.mono ?_` and prove the remaining obligations. Establish `: (N : ℝ) ≤ m` using `by exact_mod_cast hm`.

Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨σ, hσ⟩` from `exists_tends hc hcau`. Use `⟨σ, funext fun i => ?_⟩` and prove the remaining obligations. Rewrite using `[← sub_eq_zero]`. Use `RowTiePE0.eq_zero_of_ge_all (V := V) fun r => ?_` and prove the remaining obligations.

Use `choose Kj hKj using fun j => exists_ge (V := V) (w j)`. Use `set W0 : ℝ := -∑ j, |Kj j| with hW0`. Establish `hW : ∀ j, V.Ge W0 (w j)` using `fun j => (hKj j).mono (by`. Establish `h1 : |Kj j| ≤ ∑ j', |Kj j'|` using `Finset.single_le_sum (f := fun j' => |Kj j'|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)`. Establish `h2` using `neg_abs_le (Kj j)`.

Use the proof step `linarith)`. Take `⟨n0, h0⟩` from `hσ (r - W0)`. Take `⟨N, hN⟩` from `exists_nat_ge (r - W0)`. Use `set K' := max n0 N`. Establish `e` using `congrFun (hid K') i`.

Simplify using `only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at e`. Rewrite using `[e, Pi.smul_apply, smul_eq_mul]`. Establish `e2 : σs K' * w i + (V.l : C) ^ K' * Matrix.mulVec (bs K').1 w i - σ * w i = -((σ - σs K') * w i) + (V.l : C) ^ K' * Matrix.mulVec (bs K').1 w i` using `by ring`. Rewrite using `[e2]`. Use `VF.Ge.add ?_ ?_` and prove the remaining obligations.

Use `((h0 K' (le_max_left _ _)).mul (hW i)).neg` as an intermediate fact. Simplify using `using this`. Establish `hv : V.Ge W0 (Matrix.mulVec (bs K').1 w i)`. Simplify using `only [Matrix.mulVec, dotProduct]`. Conclude with `VF.Ge.sum fun j _ => (int_mem K (bs K').2 i j).mul_int (hW j)`.

Use `(RowTiePKeyEig.ge_lpow (V := V) K').mul hv` as an intermediate fact. Use `this.mono ?_` and prove the remaining obligations. Establish `: (N : ℝ) ≤ K'` using `by exact_mod_cast le_max_right n0 N`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem scal (hT : TeichSt)
    (hc : ∀ s : ℕ → C, (∀ n : ℕ, V.Ge n (s (n + 1) - s n)) → ∃ x, ∀ n : ℕ, V.Ge n (x - s n)) (hd : d ≠ 0)
    {B : Matrix (Fin n) (Fin n) C} (hB : B ∈ Acl K) (w : Fin n → C)
    (hw : ∀ τ ∈ Acl K, τ ^ V.l ^ d = τ → ∃ c : C, Matrix.mulVec τ w = c • w) :
    ∃ σ : C, Matrix.mulVec B w = σ • w := by
  by_cases hw0 : w = 0
  · exact ⟨0, by rw [hw0, Matrix.mulVec_zero, smul_zero]⟩
  have ht : ∀ b : {b // b ∈ Acl K}, ∃ τ : Matrix (Fin n) (Fin n) C,
      τ ∈ Acl K ∧ τ ^ V.l ^ d = τ ∧ ((V.l : C)⁻¹) • (b.1 - τ) ∈ Acl K := by
    intro b
    obtain ⟨τ, h1, h2, h3⟩ := teich_acl K hT hc hd b.2
    exact ⟨τ, h1, h2, h3⟩
  choose tf htf using ht
  let nx : {b // b ∈ Acl K} → {b // b ∈ Acl K} := fun b => ⟨((V.l : C)⁻¹) • (b.1 - tf b), (htf b).2.2⟩
  let bs : ℕ → {b // b ∈ Acl K} := fun k => nx^[k] ⟨B, hB⟩
  have hl0 : (V.l : C) ≠ 0 := V.l_ne_zero
  have hrel : ∀ k, (bs k).1 = tf (bs k) + (V.l : C) • (bs (k + 1)).1 := by
    intro k
    show (bs k).1 = tf (bs k) + (V.l : C) • (nx^[k + 1] ⟨B, hB⟩).1
    rw [Function.iterate_succ_apply']
    show (bs k).1 = tf (bs k) + (V.l : C) • (((V.l : C)⁻¹) • ((bs k).1 - tf (bs k)))
    rw [smul_smul, mul_inv_cancel₀ hl0, one_smul]
    abel
  have hcs : ∀ k, ∃ c : C, Matrix.mulVec (tf (bs k)) w = c • w := fun k => hw _ (htf _).1 (htf _).2.1
  choose cs hcs using hcs
  have hcsi : ∀ k, V.Ge 0 (cs k) := fun k =>
    eig_int (tf (bs k)) (int_mem K (htf _).1) w hw0 (cs k) (hcs k)
  let σs : ℕ → C := fun K' => ∑ k ∈ Finset.range K', (V.l : C) ^ k * cs k
  have hid : ∀ K', Matrix.mulVec B w = σs K' • w + ((V.l : C) ^ K') • Matrix.mulVec (bs K').1 w := by
    intro K'
    induction K' with
    | zero => simp [σs, bs]
    | succ K' ih =>
      rw [ih, hrel K', Matrix.add_mulVec, Matrix.smul_mulVec, hcs K', smul_add, smul_smul, smul_smul,
        ← add_assoc, ← add_smul, ← pow_succ]
      simp only [σs, Finset.sum_range_succ]
  have hcau : ∀ N : ℕ, ∃ n0 : ℕ, ∀ m ≥ n0, V.Ge N (σs (m + 1) - σs m) := by
    intro N
    refine ⟨N, fun m hm => ?_⟩
    simp only [σs, Finset.sum_range_succ, add_sub_cancel_left]
    have := (RowTiePKeyEig.ge_lpow (V := V) m).mul (hcsi m)
    refine this.mono ?_
    have : (N : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  obtain ⟨σ, hσ⟩ := exists_tends hc hcau
  refine ⟨σ, funext fun i => ?_⟩
  rw [← sub_eq_zero]
  refine RowTiePE0.eq_zero_of_ge_all (V := V) fun r => ?_

  choose Kj hKj using fun j => exists_ge (V := V) (w j)
  set W0 : ℝ := -∑ j, |Kj j| with hW0
  have hW : ∀ j, V.Ge W0 (w j) := fun j => (hKj j).mono (by
    have h1 : |Kj j| ≤ ∑ j', |Kj j'| := Finset.single_le_sum (f := fun j' => |Kj j'|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ j)
    have h2 := neg_abs_le (Kj j)
    linarith)
  obtain ⟨n0, h0⟩ := hσ (r - W0)
  obtain ⟨N, hN⟩ := exists_nat_ge (r - W0)
  set K' := max n0 N
  have e := congrFun (hid K') i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at e
  rw [e, Pi.smul_apply, smul_eq_mul]
  have e2 : σs K' * w i + (V.l : C) ^ K' * Matrix.mulVec (bs K').1 w i - σ * w i =
      -((σ - σs K') * w i) + (V.l : C) ^ K' * Matrix.mulVec (bs K').1 w i := by ring
  rw [e2]
  refine VF.Ge.add ?_ ?_
  · have := ((h0 K' (le_max_left _ _)).mul (hW i)).neg
    simpa using this
  · have hv : V.Ge W0 (Matrix.mulVec (bs K').1 w i) := by
      simp only [Matrix.mulVec, dotProduct]
      exact VF.Ge.sum fun j _ => (int_mem K (bs K').2 i j).mul_int (hW j)
    have := (RowTiePKeyEig.ge_lpow (V := V) K').mul hv
    refine this.mono ?_
    have : (N : ℝ) ≤ K' := by exact_mod_cast le_max_right n0 N
    linarith

end RowTiePKeyEig

end Formalism.L2.FormalSeriesBounds
