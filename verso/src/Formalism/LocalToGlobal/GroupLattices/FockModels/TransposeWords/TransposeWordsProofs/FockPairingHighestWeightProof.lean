import Formalism.LocalToGlobal.GroupLattices.FockModels.TransposeWords.FockPairingHighestWeight
import Formalism.GradedWeylDivisibility.FinalD
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LEhwLemmas

open MvPolynomial

noncomputable section

namespace Formalism.L2.G.Model.TS

open Formalism.GradedWeylDivisibility

/- English proof (translation)
Rewrite `hf` using `[standardMonomialSpanDomain B r n ν]`. Establish `key : ∀ m ∈ f.support, ∀ k : ℕ, (∑ a : Fin r with a.val < k, rowDeg m a) ≤ ∑ t : Fin n with t.val < k, ν t`. Proceed by induction on `hf using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨K, sz, hsz, I, hshape, rfl⟩` from `hx`.

Introduce `m hm k`. Establish `h` using `(bidetDominance B r n K sz hsz I m hm).1 k`. Rewrite `h` using `[hshape]`. Conclude with `h`. Consider the case `zero`.

Introduce `m hm`. Simplify using `at hm`. Consider the case `add x y _ _ hx hy`. Introduce `m hm`. Break down `Finset.mem_union.mp (support_add hm) with h | h` into its components or cases.

Conclude with `hx m h`. Conclude with `hy m h`. Consider the case `smul c x _ hx`. Introduce `m hm`. Conclude with `hx m (support_smul hm)`.

Introduce `m hm k`. Rewrite using `[rowNu_partial_sum ν hnr k]`. Conclude with `key m hm k`.
-/
theorem hw_dom {B : Type} [CommRing B] [IsDomain B] {r n : ℕ} (ν : Fin n → ℕ) (hnr : n ≤ r)
    (f : MvPolynomial (Fin r × Fin n) B) (hf : f ∈ dualWeyl B r n ν) :
    ∀ m ∈ f.support, ∀ k : ℕ,
      (∑ a : Fin r with a.val < k, rowDeg m a) ≤ ∑ a : Fin r with a.val < k, rowNu (r := r) ν a := by
  classical
  rw [standardMonomialSpanDomain B r n ν] at hf
  have key : ∀ m ∈ f.support, ∀ k : ℕ,
      (∑ a : Fin r with a.val < k, rowDeg m a) ≤ ∑ t : Fin n with t.val < k, ν t := by
    induction hf using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨K, sz, hsz, I, hshape, rfl⟩ := hx
      intro m hm k
      have h := (bidetDominance B r n K sz hsz I m hm).1 k
      rw [hshape] at h
      exact h
    | zero =>
      intro m hm
      simp at hm
    | add x y _ _ hx hy =>
      intro m hm
      rcases Finset.mem_union.mp (support_add hm) with h | h
      · exact hx m h
      · exact hy m h
    | smul c x _ hx =>
      intro m hm
      exact hx m (support_smul hm)
  intro m hm k
  rw [rowNu_partial_sum ν hnr k]
  exact key m hm k

/- English proof (translation)
Establish `hGp : IsWeightedHomogeneous (lehwP a) G ((∑ a' : Fin r with a'.val < a.val + 1, rowNu (r` using `r) ν a' : ℕ) : ℤ) := by`. Introduce `m hm`. Rewrite using `[lehw_weight_P]`. Establish `hm'` using `hGh hm`. Use `congr 1`.

Use `Finset.sum_congr rfl fun a' _ => ?_` and prove the remaining obligations. Rewrite using `[← lehw_weight_rowW, hm']`. Establish `hsh` using `lehw_rowDiv_shift B (lehwP a) 1 a b (highestWeightCount_self_eq_succ_of_lt hab) _ k G hGp`. Establish `hmem` using `rowDivStable B r n ν a b k G hG`. Assume the negation of the conclusion as `hne`.

Take `⟨m, hm⟩` from `ne_zero_iff.mp hne`. Establish `h1` using `hsh hm`. Rewrite `h1` using `[lehw_weight_P]`. Establish `h2` using `hw_dom ν hn _ hmem m (mem_support_iff.mpr hm) (a.val + 1)`. Establish `h3 : ((∑ a' : Fin r with a'.val < a.val + 1, rowDeg m a' : ℕ) : ℤ) ≤ ((∑ a' : Fin r with a'.val < a.val + 1, rowNu (r` using `r) ν a' : ℕ) : ℤ) := by exact_mod_cast h2`.

Establish `hk' : (1 : ℤ) ≤ k` using `by exact_mod_cast hk`. Rewrite `h3` using `[h1]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem hw_kill {B : Type} [CommRing B] [IsDomain B] {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ)
    (G : MvPolynomial (Fin r × Fin n) B) (hG : G ∈ dualWeyl B r n ν)
    (hGh : IsWeightedHomogeneous (rowW r n) G (rowNu (r := r) ν))
    (a b : Fin r) (hab : a < b) (k : ℕ) (hk : 1 ≤ k) : rowDiv B a b k G = 0 := by
  classical
  have hGp : IsWeightedHomogeneous (lehwP a) G
      ((∑ a' : Fin r with a'.val < a.val + 1, rowNu (r := r) ν a' : ℕ) : ℤ) := by
    intro m hm
    rw [lehw_weight_P]
    have hm' := hGh hm
    congr 1
    refine Finset.sum_congr rfl fun a' _ => ?_
    rw [← lehw_weight_rowW, hm']
  have hsh := lehw_rowDiv_shift B (lehwP a) 1 a b (highestWeightCount_self_eq_succ_of_lt hab) _ k G hGp
  have hmem := rowDivStable B r n ν a b k G hG
  by_contra hne
  obtain ⟨m, hm⟩ := ne_zero_iff.mp hne
  have h1 := hsh hm
  rw [lehw_weight_P] at h1
  have h2 := hw_dom ν hn _ hmem m (mem_support_iff.mpr hm) (a.val + 1)
  have h3 : ((∑ a' : Fin r with a'.val < a.val + 1, rowDeg m a' : ℕ) : ℤ) ≤
      ((∑ a' : Fin r with a'.val < a.val + 1, rowNu (r := r) ν a' : ℕ) : ℤ) := by exact_mod_cast h2
  have hk' : (1 : ℤ) ≤ k := by exact_mod_cast hk
  rw [h1] at h3
  linarith

/- English proof (translation)
Unfold `hw`. Rewrite using `[map_prod]`. Use `Finset.prod_eq_one fun s _ => ?_` and prove the remaining obligations. Rewrite using `[map_pow]`. Establish `h` using `eval_idPoint_lpMinor R (r := r) (n := n) (s.val + 1) (by omega) (by omega)`.

Express the relevant statement in the definitionally equal form `eval (idPoint R r n) _ ^ _ = 1`. Rewrite using `[h, one_pow]`.
-/
theorem eval_idFrame_hw (R : Type) [CommRing R] {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) :
    eval (idFrame R r n) (hw R hn ν) = 1 := by
  unfold hw
  rw [map_prod]
  refine Finset.prod_eq_one fun s _ => ?_
  rw [map_pow]
  have h := eval_idPoint_lpMinor R (r := r) (n := n) (s.val + 1) (by omega) (by omega)
  change eval (idPoint R r n) _ ^ _ = 1
  rw [h, one_pow]

/- English proof (translation)
Introduce `K _ _ r n hn ν hν F hF`. Establish `: Infinite K` using `Infinite.of_injective (Nat.cast : ℕ → K) Nat.cast_injective`. Use `set G := weightedHomogeneousComponent (rowW r n) (rowNu (r := r) ν) F with hGdef`. Establish `hG : G ∈ dualWeyl K r n ν` using `dualWeylRowGraded K r n ν _ F hF`. Establish `hGh : IsWeightedHomogeneous (rowW r n) G (rowNu (r` using `r) ν) := weightedHomogeneousComponent_isWeightedHomogeneous _ _`.

Take `⟨c, hc⟩` from `hwLine K r n hn ν hν G hG (fun a b hab k hk => hw_kill hn ν G hG hGh a b hab k hk)`. Establish `hHW` using `hwRowWeight K r n hn ν hν`. Establish `h1 : fockR (hw K hn ν) F = fockR (hw K hn ν) G`. Unfold `fockR`. Use `Finset.sum_congr rfl fun m hm => ?_` and prove the remaining obligations.

Rewrite using `[hGdef, coeff_weightedHomogeneousComponent, if_pos (hHW (mem_support_iff.mp hm))]`. Establish `h2 : fockR (hw K hn ν) G = c * fockR (hw K hn ν) (hw K hn ν)`. Rewrite using `[hc]`. Unfold `fockR`. Rewrite using `[Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Rewrite using `[coeff_smul, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `hcolF : IsWeightedHomogeneous (colW r n) F ν` using `(mem_weightedHomogeneousSubmodule _ _ _ _).mp (Submodule.mem_inf.mp hF).1`. Establish `hcolH : IsWeightedHomogeneous (colW r n) (hw K hn ν) ν` using `(mem_weightedHomogeneousSubmodule _ _ _ _).mp (Submodule.mem_inf.mp (hwMem K r n hn ν hν)).1`.

Establish `hD : ∀ (a : Fin r) (j : Fin n), a.val ≠ j.val → idFrame K r n (a, j) = 0`. Introduce `a j h`. Simplify using `[idFrame, h]`. Establish `eF` using `lhwline_diag hn ν F hcolF (idFrame K r n) hD`. Establish `eH` using `lhwline_diag hn ν (hw K hn ν) hcolH (idFrame K r n) hD`.

Establish `hev1` using `eval_idFrame_hw K hn ν`. Establish `hDmem : lhwline_mnu hn ν ∈ (hw K hn ν).support`. Rewrite using `[mem_support_iff]`. Introduce `h0`. Rewrite `eH` using `[h0, zero_mul, hev1]`.

Conclude with `one_ne_zero eH`. Establish `hcoef : coeff (lhwline_mnu hn ν) F = c * coeff (lhwline_mnu hn ν) (hw K hn ν)`. Establish `e : coeff (lhwline_mnu hn ν) F = coeff (lhwline_mnu hn ν) G`. Rewrite using `[hGdef, coeff_weightedHomogeneousComponent, if_pos (hHW (mem_support_iff.mp hDmem))]`. Rewrite using `[e, hc, coeff_smul, smul_eq_mul]`.

Establish `hevF : eval (idFrame K r n) F = c`. Rewrite using `[eF, hcoef, mul_assoc, ← eH, hev1, mul_one]`. Rewrite using `[h1, h2, hevF]`.
-/
theorem fock_pairing_highest_weight_proof : FockPairingHighestWeight := by
  intro K _ _ r n hn ν hν F hF
  classical
  have : Infinite K := Infinite.of_injective (Nat.cast : ℕ → K) Nat.cast_injective
  set G := weightedHomogeneousComponent (rowW r n) (rowNu (r := r) ν) F with hGdef
  have hG : G ∈ dualWeyl K r n ν := dualWeylRowGraded K r n ν _ F hF
  have hGh : IsWeightedHomogeneous (rowW r n) G (rowNu (r := r) ν) :=
    weightedHomogeneousComponent_isWeightedHomogeneous _ _
  obtain ⟨c, hc⟩ := hwLine K r n hn ν hν G hG
    (fun a b hab k hk => hw_kill hn ν G hG hGh a b hab k hk)
  have hHW := hwRowWeight K r n hn ν hν
  have h1 : fockR (hw K hn ν) F = fockR (hw K hn ν) G := by
    unfold fockR
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [hGdef, coeff_weightedHomogeneousComponent, if_pos (hHW (mem_support_iff.mp hm))]
  have h2 : fockR (hw K hn ν) G = c * fockR (hw K hn ν) (hw K hn ν) := by
    rw [hc]
    unfold fockR
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [coeff_smul, smul_eq_mul]
    ring
  have hcolF : IsWeightedHomogeneous (colW r n) F ν :=
    (mem_weightedHomogeneousSubmodule _ _ _ _).mp (Submodule.mem_inf.mp hF).1
  have hcolH : IsWeightedHomogeneous (colW r n) (hw K hn ν) ν :=
    (mem_weightedHomogeneousSubmodule _ _ _ _).mp (Submodule.mem_inf.mp (hwMem K r n hn ν hν)).1
  have hD : ∀ (a : Fin r) (j : Fin n), a.val ≠ j.val → idFrame K r n (a, j) = 0 := by
    intro a j h
    simp [idFrame, h]
  have eF := lhwline_diag hn ν F hcolF (idFrame K r n) hD
  have eH := lhwline_diag hn ν (hw K hn ν) hcolH (idFrame K r n) hD
  have hev1 := eval_idFrame_hw K hn ν
  have hDmem : lhwline_mnu hn ν ∈ (hw K hn ν).support := by
    rw [mem_support_iff]
    intro h0
    rw [h0, zero_mul, hev1] at eH
    exact one_ne_zero eH
  have hcoef : coeff (lhwline_mnu hn ν) F = c * coeff (lhwline_mnu hn ν) (hw K hn ν) := by
    have e : coeff (lhwline_mnu hn ν) F = coeff (lhwline_mnu hn ν) G := by
      rw [hGdef, coeff_weightedHomogeneousComponent, if_pos (hHW (mem_support_iff.mp hDmem))]
    rw [e, hc, coeff_smul, smul_eq_mul]
  have hevF : eval (idFrame K r n) F = c := by
    rw [eF, hcoef, mul_assoc, ← eH, hev1, mul_one]
  rw [h1, h2, hevF]

end Formalism.L2.G.Model.TS
