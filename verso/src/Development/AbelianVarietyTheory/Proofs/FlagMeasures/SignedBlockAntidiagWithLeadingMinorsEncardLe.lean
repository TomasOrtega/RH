import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AdaptSelf
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt GlobalTheory.DegAsm
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.SignedBlockCount
open Formalism.MainNotions.S.Loc

variable {K : Type} [Field K]

noncomputable def minor (bs : List (Kˣ × ℕ+)) (l : ℕ) : K :=
  (Matrix.of fun a b : Fin l => ptEntryL bs a b).det

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem minor_zero (bs : List (Kˣ × ℕ+)) : minor bs 0 = 1 := by simp [minor]

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Simplify using the standard rewrite rules. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem minor_lt (t : Kˣ) (s : ℕ+) (bs : List (Kˣ × ℕ+)) (l : ℕ) (h0 : 0 < l) (hl : l < s) :
    minor ((t, s) :: bs) l = 0 := by
  refine Matrix.det_eq_zero_of_row_eq_zero ⟨0, h0⟩ fun b => ?_
  have hb := b.2
  simp only [Matrix.of_apply, ptEntryL]
  split_ifs <;> first | rfl | omega

/- English proof (translation)
Establish an intermediate fact. By extensionality, compare the relevant components. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules.

Apply the first step, then apply the next step to every resulting obligation. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules.
-/
theorem minor_add (t : Kˣ) (s : ℕ+) (bs : List (Kˣ × ℕ+)) (l : ℕ) :
    minor ((t, s) :: bs) (s + l) =
      (((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin s)) : ℤˣ) : ℤ) *
        (t : K) ^ (s : ℕ)) * minor bs l := by
  have key : (Matrix.of fun a b : Fin (s + l) => ptEntryL ((t, s) :: bs) a b).submatrix
      finSumFinEquiv finSumFinEquiv =
      Matrix.fromBlocks ((Matrix.diagonal (fun _ : Fin s => (t : K))).submatrix id
          (Fin.revPerm : Equiv.Perm (Fin s))) 0 0
        (Matrix.of fun a b : Fin l => ptEntryL bs a b) := by
    ext (a | a) (b | b)
    · have ha := a.2
      have hb := b.2
      simp only [Matrix.submatrix_apply, Matrix.of_apply, ptEntryL, finSumFinEquiv_apply_left,
        Fin.val_castAdd, Matrix.fromBlocks_apply₁₁, id, Matrix.diagonal_apply, Fin.revPerm_apply,
        Fin.ext_iff, Fin.val_rev]
      split_ifs <;> first | rfl | omega
    · simp [ptEntryL]
    · simp [ptEntryL]
    · simp [ptEntryL]
  rw [minor, ← Matrix.det_submatrix_equiv_self finSumFinEquiv, key, Matrix.det_fromBlocks_zero₂₁,
    Matrix.det_permute', Matrix.det_diagonal]
  simp [minor]

/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem sign_ne (u : ℤˣ) : ((u : ℤ) : K) ≠ 0 := by
  rcases Int.units_eq_one_or u with e | e <;> simp [e]

/- English proof (translation)
Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.
-/
theorem minor_self (t : Kˣ) (s : ℕ+) (bs : List (Kˣ × ℕ+)) :
    minor ((t, s) :: bs) s =
      ((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin s)) : ℤˣ) : ℤ) * (t : K) ^ (s : ℕ) := by
  have := minor_add t s bs 0
  rwa [minor_zero, mul_one, Nat.add_zero] at this

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem minor_self_ne (t : Kˣ) (s : ℕ+) (bs : List (Kˣ × ℕ+)) : minor ((t, s) :: bs) s ≠ 0 := by
  rw [minor_self]
  exact mul_ne_zero (sign_ne _) (pow_ne_zero _ t.ne_zero)

/- English proof (translation)
Proceed by induction. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Consider separately whether the proposition holds or fails. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Extract witnesses or component facts from the available result. Introduce a local definition for the expression. Establish an intermediate fact. Introduce a local definition for the expression.

Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. Chain the equalities or inequalities of the calculation. Assume the hypotheses and unpack their components.

Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers. Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact.

Reduce the claim to the hypotheses of an applicable result. Separate the alternatives or extract the components of the hypothesis. Substitute using the available equality. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations.

Assume the hypotheses and unpack their components. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem count_lists (n : ℕ) : ∀ η : ℕ → K, ∃ T : Finset (List (Kˣ × ℕ+)), T.card ≤ 2 ^ n ∧
    ∀ bs : List (Kˣ × ℕ+), (bs.map (fun b => (b.2 : ℕ))).sum = n →
      (∀ l ≤ n, minor bs l = η l) → bs ∈ T := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro η
  by_cases hex : ∃ (t : Kˣ) (s : ℕ+) (bs : List (Kˣ × ℕ+)),
      (s : ℕ) + (bs.map (fun b => (b.2 : ℕ))).sum = n ∧ ∀ l ≤ n, minor ((t, s) :: bs) l = η l
  · obtain ⟨t₀, s, bs₀, hs, h₀⟩ := hex
    have hsp := s.pos
    obtain ⟨T, hT, hT'⟩ := ih (n - s) (by omega) (fun l => η (s + l) / η s)
    let c : K := ((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin s)) : ℤˣ) : ℤ)
    have hc : c ≠ 0 := sign_ne _
    let R := (Polynomial.nthRoots s (η s / c)).toFinset
    have hR : R.card ≤ s := (Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots _ _)
    refine ⟨Finset.image₂ (fun x bs => ((if h : x = 0 then 1 else Units.mk0 x h), s) :: bs) R T,
      ?_, ?_⟩
    · refine (Finset.card_image₂_le _ _ _).trans ?_
      calc R.card * T.card ≤ 2 ^ (s : ℕ) * 2 ^ (n - s) :=
            Nat.mul_le_mul (hR.trans (Nat.lt_two_pow_self).le) hT
        _ = 2 ^ n := by rw [← pow_add]; congr 1; omega
    · rintro (_ | ⟨⟨t, s'⟩, bs⟩) hsum h
      · simp only [List.map_nil, List.sum_nil] at hsum
        omega
      simp only [List.map_cons, List.sum_cons] at hsum
      have hsp' := s'.pos
      have e : s' = s := by
        apply PNat.eq
        rcases lt_trichotomy (s' : ℕ) s with h1 | h1 | h1
        · exact absurd ((h s' (by omega)).trans ((h₀ s' (by omega)).symm.trans
            (minor_lt _ _ _ _ hsp' h1))) (minor_self_ne _ _ _)
        · exact h1
        · exact absurd ((h₀ s (by omega)).trans ((h s (by omega)).symm.trans
            (minor_lt _ _ _ _ hsp h1))) (minor_self_ne _ _ _)
      subst e
      have h1 := h s' (by omega)
      refine Finset.mem_image₂.2 ⟨t, ?_, bs, hT' bs (by omega) fun l hl => ?_, ?_⟩
      · simp only [R, Multiset.mem_toFinset, Polynomial.mem_nthRoots hsp]
        rw [← h1, minor_self, eq_div_iff hc, mul_comm]
      · rw [← h _ (by omega), ← h1, minor_add, ← minor_self t s' bs,
          mul_div_cancel_left₀ _ (minor_self_ne _ _ _)]
      · simp [t.ne_zero]
  · refine ⟨{[]}, by simpa using Nat.one_le_two_pow, ?_⟩
    rintro (_ | ⟨⟨t, s⟩, bs⟩) hsum h
    · simp
    · exact absurd ⟨t, s, bs, by simpa using hsum, h⟩ hex

end GlobalTheory.SignedBlockCount

namespace GlobalTheory

open Formalism.MainNotions.S.Loc SignedBlockCount in

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Introduce a local definition for the expression. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.

By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem signed_block_count : ∀ (K : Type) [Field K] (j : ℕ) (δ : ℕ → K), (({P : Matrix (Fin j) (Fin j) K | (∃ (w : Formalism.MainNotions.S.Loc.Pt K j) (sgn : Fin j → ℤˣ), ∀ a b, P a b = w.mat a b * ((sgn b : ℤ) : K)) ∧ ∀ (l : ℕ) (hl : l ≤ j), (P.submatrix (Fin.castLE hl) (Fin.castLE hl)).det = δ l}).encard : ℕ∞) ≤ 8 ^ j := by
  intro K _ j δ
  choose T hT hT' using count_lists (K := K) j
  let η : (Fin j → ℤˣ) → ℕ → K := fun sgn l =>
    if hl : l ≤ j then δ l / ∏ b : Fin l, ((sgn (Fin.castLE hl b) : ℤ) : K) else 0
  let U : Finset (Matrix (Fin j) (Fin j) K) := Finset.univ.biUnion fun sgn : Fin j → ℤˣ =>
    (T (η sgn)).image fun bs => Matrix.of fun a b => ptEntryL bs a b * ((sgn b : ℤ) : K)
  have hU : U.card ≤ 8 ^ j := by
    refine (Finset.card_biUnion_le_card_mul _ _ (2 ^ j)
      fun sgn _ => Finset.card_image_le.trans (hT _)).trans ?_
    simp only [Finset.card_univ, Fintype.card_pi, Fintype.card_units_int, Finset.prod_const,
      Fintype.card_fin]
    rw [← mul_pow]
    exact Nat.pow_le_pow_left (by norm_num) _
  refine (Set.encard_le_encard (t := (U : Set _)) ?_).trans ?_
  · rintro P ⟨⟨w, sgn, hP⟩, hδ⟩
    refine Finset.mem_coe.2 (Finset.mem_biUnion.2 ⟨sgn, Finset.mem_univ _,
      Finset.mem_image.2 ⟨w.blocks, hT' _ _ w.size fun l hl => ?_, ?_⟩⟩)
    · simp only [η, dif_pos hl]
      rw [eq_div_iff (Finset.prod_ne_zero_iff.2 fun b _ => sign_ne _), ← hδ l hl, mul_comm, minor,
        ← Matrix.det_mul_row]
      congr 1
      ext a b
      simp [hP, Pt.mat, mul_comm]
    · ext a b
      simp [hP, Pt.mat]
  · rw [Set.encard_coe_eq_coe_finsetCard]
    exact_mod_cast hU

end GlobalTheory
