import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsHsymmShift
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PNumericalSegre
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.RingKrullDimQuotComapRename
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Assembly
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

namespace HsymmShiftProof

open NumericalSegreProof

variable {F : Type u} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
  [∀ k, Fintype (ι k)]

omit [Fintype K] [DecidableEq K] in

/- English proof (translation)
Unfold `rootList`. Simplify using `[List.length_flatMap, Fin.sum_univ_def]`.
-/
theorem length_rootList {n : ℕ} (x : Fin n → K → ℤ) (α : Fin n → ℕ) :
    (rootList x α).length = ∑ i, α i := by
  unfold rootList
  simp [List.length_flatMap, Fin.sum_univ_def]

/- English proof (translation)
Establish `key : ∀ e, Function.update (c :: l).get (0 : Fin (l.length + 1)) e = (e :: l).get`. Introduce `e`. Use function extensionality and compare the values at `j`. Use `Fin.cases ?_ (fun j => ?_) j` and prove the remaining obligations. Simplify using the standard rewrite rules.

Rewrite using `[Function.update_of_ne (Fin.succ_ne_zero j)]`. Both sides reduce to the same expression. Establish `h` using `FieldNumbers.IntNumAdd.full.{u} F K ι W hW.multiHomog hW.relevant (l.length + 1) hd ((c :: l).get) 0 c c'`. Rewrite `h` using `[key, key, key]`. Conclude with `h`.
-/
theorem cons_add (W : Ideal (MRing ι F)) (hW : IsMultiProjPrime W) (l : List (K → ℤ))
    (hd : FieldNumbers.relDim W = ((l.length + 1 : ℕ) : WithBot (WithTop ℤ))) (c c' : K → ℤ) :
    intNumL F W ((c + c') :: l) = intNumL F W (c :: l) + intNumL F W (c' :: l) := by
  have key : ∀ e, Function.update (c :: l).get (0 : Fin (l.length + 1)) e = (e :: l).get := by
    intro e
    funext j
    refine Fin.cases ?_ (fun j => ?_) j
    · simp
    · rw [Function.update_of_ne (Fin.succ_ne_zero j)]
      rfl
  have h := FieldNumbers.IntNumAdd.full.{u} F K ι W hW.multiHomog hW.relevant (l.length + 1) hd
    ((c :: l).get) 0 c c'
  rw [key, key, key] at h
  exact h

/- English proof (translation)
The claim follows from `| 0, L, _ => by simp | n + 1, L, hd => by have hd' : ∀ c : K → ℤ, FieldNumbers.relDim W = ((n + (c :: L).length : ℕ) : WithBot (WithTop ℤ)) := by intro c rw [hd, List.length_cons, Nat.add_right_comm, Nat.add_assoc] rw [List.replicate_succ, List.cons_append, cons_add W hW _ (by rw …`.
-/
theorem replicate_add (W : Ideal (MRing ι F)) (hW : IsMultiProjPrime W)
    (z s : K → ℤ) : ∀ (n : ℕ) (L : List (K → ℤ)),
    FieldNumbers.relDim W = ((n + L.length : ℕ) : WithBot (WithTop ℤ)) →
    intNumL F W (List.replicate n (z + s) ++ L) =
      ∑ k ∈ Finset.range (n + 1), (n.choose k : ℤ) *
        intNumL F W (List.replicate (n - k) z ++ List.replicate k s ++ L)
  | 0, L, _ => by simp
  | n + 1, L, hd => by
    have hd' : ∀ c : K → ℤ,
        FieldNumbers.relDim W = ((n + (c :: L).length : ℕ) : WithBot (WithTop ℤ)) := by
      intro c
      rw [hd, List.length_cons, Nat.add_right_comm, Nat.add_assoc]
    rw [List.replicate_succ, List.cons_append,
      cons_add W hW _ (by rw [hd, List.length_append, List.length_replicate]; congr 1; omega) z s,
      intNumL_perm F W (List.perm_middle (l₁ := List.replicate n (z + s))).symm,
      intNumL_perm F W (List.perm_middle (l₁ := List.replicate n (z + s)) (a := s)).symm,
      replicate_add W hW z s n (z :: L) (hd' z), replicate_add W hW z s n (s :: L) (hd' s),
      ProjectiveBundleNumbers.sum_choose_succ n (fun k => intNumL F W (List.replicate (n + 1 - k) z ++ List.replicate k s ++ L))]
    congr 1
    · refine Finset.sum_congr rfl fun k hk => ?_
      have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      congr 1
      refine intNumL_perm F W ?_
      rw [show n + 1 - k = (n - k) + 1 by omega, List.replicate_succ']
      simp only [List.append_assoc, List.singleton_append]
      exact List.Perm.append_left _ List.perm_middle
    · refine Finset.sum_congr rfl fun k hk => ?_
      rw [show n + 1 - (k + 1) = n - k by omega, List.replicate_succ']
      simp only [List.append_assoc, List.singleton_append]

def H (W : Ideal (MRing ι F)) {n : ℕ} (x : Fin n → K → ℤ) (c : ℕ) (L : List (K → ℤ)) : ℤ :=
  ∑ α ∈ Finset.Nat.antidiagonalTuple n c, intNumL F W (rootList x α ++ L)

omit [Fintype K] [∀ k, Fintype (ι k)] in
/- English proof (translation)
Simplify using `[H, Finset.Nat.antidiagonalTuple_zero_right, rootList_zero]`.
-/
theorem H_zero (W : Ideal (MRing ι F)) {n : ℕ} (x : Fin n → K → ℤ) (L : List (K → ℤ)) :
    H W x 0 L = intNumL F W L := by
  simp [H, Finset.Nat.antidiagonalTuple_zero_right, rootList_zero]

omit [Fintype K] [∀ k, Fintype (ι k)] in
/- English proof (translation)
Unfold `H`. Rewrite using `[Finset.Nat.antidiagonalTuple_one, Finset.sum_singleton, rootList_succ]`. Simplify using `[rootList]`.
-/
theorem H_one (W : Ideal (MRing ι F)) (x : Fin 1 → K → ℤ) (c : ℕ) (L : List (K → ℤ)) :
    H W x c L = intNumL F W (List.replicate c (x 0) ++ L) := by
  unfold H
  rw [Finset.Nat.antidiagonalTuple_one, Finset.sum_singleton, rootList_succ]
  simp [rootList]

omit [Fintype K] [∀ k, Fintype (ι k)] in
/- English proof (translation)
The claim follows from `Finset.sum_congr rfl fun _ _ => intNumL_perm F W (h.append_left _)`.
-/
theorem H_perm (W : Ideal (MRing ι F)) {n : ℕ} (x : Fin n → K → ℤ) (c : ℕ)
    {L L' : List (K → ℤ)} (h : L.Perm L') : H W x c L = H W x c L' :=
  Finset.sum_congr rfl fun _ _ => intNumL_perm F W (h.append_left _)

/- English proof (translation)
Unfold `H`. Rewrite using `[← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun α hα => ?_` and prove the remaining obligations. Establish `hlen : (rootList x α).length = c`. Rewrite using `[length_rootList]`.

Conclude with `Finset.Nat.mem_antidiagonalTuple.mp hα`. Rewrite using `[intNumL_perm F W (List.perm_middle (l₁ := rootList x α) (a := a + b)), intNumL_perm F W (List.perm_middle (l₁ := rootList x α) (a := a)), intNumL_perm F W (List.perm_middle (l₁ := rootList x α) (a := b))]`. Conclude with `cons_add W hW _ (by rw [hd, List.length_append, hlen, show c + 1 + L.length = c + L.length + 1 by omega]) a b`.
-/
theorem H_add (W : Ideal (MRing ι F)) (hW : IsMultiProjPrime W) {n : ℕ} (x : Fin n → K → ℤ)
    (c : ℕ) (L : List (K → ℤ))
    (hd : FieldNumbers.relDim W = ((c + 1 + L.length : ℕ) : WithBot (WithTop ℤ))) (a b : K → ℤ) :
    H W x c ((a + b) :: L) = H W x c (a :: L) + H W x c (b :: L) := by
  unfold H
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun α hα => ?_
  have hlen : (rootList x α).length = c := by
    rw [length_rootList]
    exact Finset.Nat.mem_antidiagonalTuple.mp hα
  rw [intNumL_perm F W (List.perm_middle (l₁ := rootList x α) (a := a + b)),
    intNumL_perm F W (List.perm_middle (l₁ := rootList x α) (a := a)),
    intNumL_perm F W (List.perm_middle (l₁ := rootList x α) (a := b))]
  exact cons_add W hW _
    (by rw [hd, List.length_append, hlen, show c + 1 + L.length = c + L.length + 1 by omega]) a b

omit [Fintype K] [∀ k, Fintype (ι k)] in

/- English proof (translation)
Unfold `H`. Rewrite using `[sum_antidiagonalTuple_succ]`. Use `congr 1`. Use `Finset.sum_congr rfl fun α _ => ?_` and prove the remaining obligations. Rewrite using `[rootList_snoc_zero]`.

Use `Finset.sum_congr rfl fun β _ => ?_` and prove the remaining obligations. Rewrite using `[rootList_update_last, List.append_assoc, List.singleton_append]`.
-/
theorem H_succ (W : Ideal (MRing ι F)) {i : ℕ} (x : Fin (i + 1) → K → ℤ) (c : ℕ)
    (L : List (K → ℤ)) :
    H W x (c + 1) L = H W (fun j => x (Fin.castSucc j)) (c + 1) L + H W x c (x (Fin.last i) :: L) := by
  unfold H
  rw [sum_antidiagonalTuple_succ]
  congr 1
  · refine Finset.sum_congr rfl fun α _ => ?_
    rw [rootList_snoc_zero]
  · refine Finset.sum_congr rfl fun β _ => ?_
    rw [rootList_update_last, List.append_assoc, List.singleton_append]

/- English proof (translation)
Rewrite using `[Finset.sum_range_succ', Finset.sum_range_succ' (fun k => (M.choose k : ℤ) * f k)]`. Simplify using `only [Nat.choose_succ_succ', Nat.cast_add, add_mul, Finset.sum_add_distrib, Nat.choose_zero_right]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sum_choose_pascal (M r : ℕ) (f : ℕ → ℤ) :
    ∑ k ∈ Finset.range (r + 1 + 1), ((M + 1).choose k : ℤ) * f k =
      ∑ k ∈ Finset.range (r + 1 + 1), (M.choose k : ℤ) * f k +
        ∑ k ∈ Finset.range (r + 1), (M.choose k : ℤ) * f (k + 1) := by
  rw [Finset.sum_range_succ', Finset.sum_range_succ' (fun k => (M.choose k : ℤ) * f k)]
  simp only [Nat.choose_succ_succ', Nat.cast_add, add_mul, Finset.sum_add_distrib,
    Nat.choose_zero_right]
  ring

/- English proof (translation)
The claim follows from `| 0, x, r, Y, hd => by rw [H_one, replicate_add W hW (x 0) s r Y hd] refine Finset.sum_congr rfl fun k _ => ?_ rw [H_one, List.append_assoc, show 0 + r = r from Nat.zero_add r] | N + 1, x, r, Y, hd => by induction r generalizing Y with | zero => simp [H_zero] | succ r ih => have …`.
-/
theorem main (W : Ideal (MRing ι F)) (hW : IsMultiProjPrime W) (s : K → ℤ) :
    ∀ (N : ℕ) (x : Fin (N + 1) → K → ℤ) (r : ℕ) (Y : List (K → ℤ)),
    FieldNumbers.relDim W = ((r + Y.length : ℕ) : WithBot (WithTop ℤ)) →
    H W (fun i => x i + s) r Y =
      ∑ k ∈ Finset.range (r + 1), ((N + r).choose k : ℤ) * H W x (r - k) (List.replicate k s ++ Y)
  | 0, x, r, Y, hd => by
    rw [H_one, replicate_add W hW (x 0) s r Y hd]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [H_one, List.append_assoc, show 0 + r = r from Nat.zero_add r]
  | N + 1, x, r, Y, hd => by
    induction r generalizing Y with
    | zero => simp [H_zero]
    | succ r ih =>
      have e1 := main W hW s N (fun j => x (Fin.castSucc j)) (r + 1) Y hd
      have e2 := ih (x (Fin.last (N + 1)) :: Y)
        (by rw [hd, List.length_cons, show r + 1 + Y.length = r + (Y.length + 1) by omega])
      have e3 := ih (s :: Y)
        (by rw [hd, List.length_cons, show r + 1 + Y.length = r + (Y.length + 1) by omega])
      have hadd := H_add W hW (fun i => x i + s) r Y hd (x (Fin.last (N + 1))) s
      have hAB : ∑ k ∈ Finset.range (r + 1 + 1), ((N + 1 + r).choose k : ℤ) *
            H W x (r + 1 - k) (List.replicate k s ++ Y) =
          ∑ k ∈ Finset.range (r + 1 + 1), ((N + (r + 1)).choose k : ℤ) *
              H W (fun j => x (Fin.castSucc j)) (r + 1 - k) (List.replicate k s ++ Y) +
            ∑ k ∈ Finset.range (r + 1), ((N + 1 + r).choose k : ℤ) *
              H W x (r - k) (List.replicate k s ++ x (Fin.last (N + 1)) :: Y) := by
        rw [show N + (r + 1) = N + 1 + r by omega, Finset.sum_range_succ,
          Finset.sum_range_succ (fun k => ((N + 1 + r).choose k : ℤ) *
            H W (fun j => x (Fin.castSucc j)) (r + 1 - k) (List.replicate k s ++ Y)),
          Nat.sub_self, H_zero, H_zero,
          add_right_comm _ _ (∑ k ∈ Finset.range (r + 1), ((N + 1 + r).choose k : ℤ) *
            H W x (r - k) (List.replicate k s ++ x (Fin.last (N + 1)) :: Y)),
          ← Finset.sum_add_distrib]
        congr 1
        refine Finset.sum_congr rfl fun k hk => ?_
        have hk' : k ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
        rw [show r + 1 - k = (r - k) + 1 by omega, H_succ W x (r - k) (List.replicate k s ++ Y),
          ← mul_add, H_perm W x (r - k) (List.perm_middle (l₁ := List.replicate k s)).symm]
      have hC : ∑ k ∈ Finset.range (r + 1), ((N + 1 + r).choose k : ℤ) *
            H W x (r + 1 - (k + 1)) (List.replicate (k + 1) s ++ Y) =
          ∑ k ∈ Finset.range (r + 1), ((N + 1 + r).choose k : ℤ) *
            H W x (r - k) (List.replicate k s ++ s :: Y) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Nat.add_sub_add_right, List.replicate_succ', List.append_assoc, List.singleton_append]
      rw [H_succ W (fun i => x i + s) r Y]
      beta_reduce at e1 ⊢
      rw [e1, hadd, e2, e3, show N + 1 + (r + 1) = N + 1 + r + 1 by omega,
        sum_choose_pascal (N + 1 + r) r (fun k => H W x (r + 1 - k) (List.replicate k s ++ Y)), hAB, hC]
      ring

end HsymmShiftProof

/- English proof (translation)
Introduce `F _ K _ _ ι _ W hW d hd N hN x s r Y hrY`. Take `⟨M, rfl⟩ : ∃ M, N = M + 1` from `⟨N - 1, by omega⟩`. Establish `h` using `HsymmShiftProof.main W hW s M x r Y (by rw [hd, ← hrY])`. Simplify using `only [HsymmShiftProof.H] at h`. Rewrite using `[h, Nat.add_sub_cancel]`.

Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Simplify using `only [List.append_assoc]`.
-/
theorem HsymmShift.proof : HsymmShift.Statement.{u} := by
  intro F _ K _ _ ι _ W hW d hd N hN x s r Y hrY
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  have h := HsymmShiftProof.main W hW s M x r Y (by rw [hd, ← hrY])
  simp only [HsymmShiftProof.H] at h
  rw [h, Nat.add_sub_cancel]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [List.append_assoc]

end

end GroundTheory.Heights₂.Heights.NumbersDVR
