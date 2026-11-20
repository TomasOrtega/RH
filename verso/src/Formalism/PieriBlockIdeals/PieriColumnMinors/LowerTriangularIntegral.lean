import Formalism.GradedWeylDivisibility.FinalD
import Formalism.GradedWeylDivisibility.StatementE

open MvPolynomial

namespace Formalism.CohomologicalDescent.LR

open Formalism.GradedWeylDivisibility

open scoped MonomialOrder

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem lre_intQ_apply (r n : ℕ) (P : MvPolynomial (Fin r × Fin n) ℤ) :
    intQ r n P = map (Int.castRingHom ℚ) P := rfl

/- English proof (translation)
Take `⟨k, hk⟩` from `p`. Proceed by induction on `k with`. Consider the case `zero => exact Nat.zero_le _`. Consider the case `succ k ih`. Establish `h1` using `ih (by omega)`.

Establish `h2 : I ⟨k, by omega⟩ < I ⟨k + 1, hk⟩` using `hI (by simp [Fin.lt_def])`. Establish `h3 : (I ⟨k, by omega⟩).val < (I ⟨k + 1, hk⟩).val` using `h2`. Use `show k + 1 ≤ (I ⟨k + 1, hk⟩).val`. Establish `h1' : k ≤ (I ⟨k, by omega⟩).val` using `h1`. Use linear arithmetic over natural numbers and integers.
-/
theorem lre_le_apply {s r : ℕ} (I : Fin s → Fin r) (hI : StrictMono I) (p : Fin s) : p.val ≤ (I p).val := by
  obtain ⟨k, hk⟩ := p
  induction k with
  | zero => exact Nat.zero_le _
  | succ k ih =>
    have h1 := ih (by omega)
    have h2 : I ⟨k, by omega⟩ < I ⟨k + 1, hk⟩ := hI (by simp [Fin.lt_def])
    have h3 : (I ⟨k, by omega⟩).val < (I ⟨k + 1, hk⟩).val := h2
    show k + 1 ≤ (I ⟨k + 1, hk⟩).val
    have h1' : k ≤ (I ⟨k, by omega⟩).val := h1
    omega

/- English proof (translation)
Introduce `a s has`. Unfold `bidetExp`. Rewrite using `[Finsupp.finsetSum_apply]`. Use `Finset.sum_eq_zero fun k _ => ?_` and prove the remaining obligations. Rewrite using `[Finsupp.finsetSum_apply]`.

Use `Finset.sum_eq_zero fun p _ => ?_` and prove the remaining obligations. Rewrite using `[Finsupp.single_apply, if_neg]`. Introduce `h`. Establish `h1 : I k p = a` using `congrArg Prod.fst h`. Establish `h2 : Fin.castLE (hsz k) p = s` using `congrArg Prod.snd h`.

Establish `h3` using `lre_le_apply (I k) (hI k) p`. Establish `h4 : p.val = s.val` using `by rw [← h2]; rfl`. Rewrite `h3` using `[h1]`. Use linear arithmetic over natural numbers and integers.
-/
theorem lre_lowerTri {r n K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n) (I : ∀ k, Fin (sz k) → Fin r)
    (hI : ∀ k, StrictMono (I k)) : LowerTri (bidetExp sz hsz I) := by
  intro a s has
  unfold bidetExp
  rw [Finsupp.finsetSum_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [Finsupp.finsetSum_apply]
  refine Finset.sum_eq_zero fun p _ => ?_
  rw [Finsupp.single_apply, if_neg]
  intro h
  have h1 : I k p = a := congrArg Prod.fst h
  have h2 : Fin.castLE (hsz k) p = s := congrArg Prod.snd h
  have h3 := lre_le_apply (I k) (hI k) p
  have h4 : p.val = s.val := by rw [← h2]; rfl
  rw [h1] at h3
  omega

/- English proof (translation)
Introduce `r n ν`. It suffices to establish `key : ∀ d : (colLex r n).syn, ∀ Q ∈ dualWeyl ℚ r n ν, (∀ e : Fin r × Fin n →₀ ℕ, LowerTri e → ∃ z : ℤ, coeff e Q = z) → (colLex r n).toSyn ((colLex r n).degree Q) = d → ∃ Q' : MvPolynomial (Fin r × Fin n) ℤ, Q = intQ r n Q' by`. Introduce `Q hQ hint`. Conclude with `key _ Q hQ hint rfl`. Introduce `d`.

Proceed by induction on `d using WellFoundedLT.induction with`. Consider the case `_ d ih`. Introduce `f hf hz hd`. Distinguish the cases in `hf0 : f = 0`. Conclude with `⟨0, by rw [hf0, map_zero]⟩`.

Use `set m := (colLex r n).degree f with hm`. Establish `hint : Interlaced m` using `leadInterlaced ℚ r n ν f hf hf0`. Establish `hcol : ∀ t : Fin n, ∑ a : Fin r, m (a, t) = ν t` using `colSums ℚ r n ν f hf m (((colLex r n).degree_mem_support_iff f).mpr hf0)`. Take `⟨K, sz, hsz, I, hshape, hmono, hexp⟩` from `sSYTExists r n ν m hcol hint`. Take `⟨hbdeg, hblc⟩` from `column_lex_bideterminant ℚ r n K sz hsz I hmono`.

Establish `hbmap : bideterminant ℚ sz hsz I = intQ r n (bideterminant ℤ sz hsz I)`. Rewrite using `[lre_intQ_apply, ldlat_map_bidet]`. Establish `hbmem : bideterminant ℚ sz hsz I ∈ dualWeyl ℚ r n ν`. Use `bidetMem ℚ r n K sz hsz I` as an intermediate fact. Rewrite `this` using `[hshape]`.

Conclude with `this`. Establish `hmL : LowerTri m`. Rewrite using `[← hexp]`. Conclude with `lre_lowerTri sz hsz I hmono`. Take `⟨c, hc⟩` from `hz m hmL`.

Establish `hlc : (colLex r n).leadingCoeff f = (c : ℚ)` using `hc`. Establish `hf'mem : f - (colLex r n).leadingCoeff f • bideterminant ℚ sz hsz I ∈ dualWeyl ℚ r n ν` using `Submodule.sub_mem _ hf (Submodule.smul_mem _ _ hbmem)`. Establish `hf'z : ∀ e : Fin r × Fin n →₀ ℕ, LowerTri e → ∃ z : ℤ, coeff e (f - (colLex r n).leadingCoeff f • bideterminant ℚ sz hsz I) = z`. Introduce `e he`. Take `⟨z, hz'⟩` from `hz e he`.

Use `⟨z - c * coeff e (bideterminant ℤ sz hsz I), ?_⟩` and prove the remaining obligations. Rewrite using `[coeff_sub, coeff_smul, hz', hlc, hbmap, lre_intQ_apply, coeff_map]`. Simplify using the standard rewrite rules. Establish `hfin : ∃ Q'' : MvPolynomial (Fin r × Fin n) ℤ, f - (colLex r n).leadingCoeff f • bideterminant ℚ sz hsz I = intQ r n Q''`. Distinguish the cases in `h0 : f - (colLex r n).leadingCoeff f • bideterminant ℚ sz hsz I = 0`.

Conclude with `⟨0, by rw [h0, map_zero]⟩`. Establish `hlt` using `lcassem_sub_lt (colLex r n) (f := f) (g := bideterminant ℚ sz hsz I) (hbdeg.trans hexp) hblc h0`. Conclude with `ih _ (hd ▸ hlt) _ hf'mem hf'z rfl`. Take `⟨Q'', hQ''⟩` from `hfin`. Use `⟨Q'' + c • bideterminant ℤ sz hsz I, ?_⟩` and prove the remaining obligations.

Rewrite using `[map_add, map_smul, ← hQ'', ← hbmap, hlc, Int.cast_smul_eq_zsmul]`. Normalize the expressions using the abelian group laws.
-/
theorem lower_triangular_integral : LowerTriIntegral := by
  intro r n ν
  suffices key : ∀ d : (colLex r n).syn, ∀ Q ∈ dualWeyl ℚ r n ν,
      (∀ e : Fin r × Fin n →₀ ℕ, LowerTri e → ∃ z : ℤ, coeff e Q = z) →
      (colLex r n).toSyn ((colLex r n).degree Q) = d →
      ∃ Q' : MvPolynomial (Fin r × Fin n) ℤ, Q = intQ r n Q' by
    intro Q hQ hint
    exact key _ Q hQ hint rfl
  intro d
  induction d using WellFoundedLT.induction with
  | _ d ih =>
    intro f hf hz hd
    by_cases hf0 : f = 0
    · exact ⟨0, by rw [hf0, map_zero]⟩
    set m := (colLex r n).degree f with hm
    have hint : Interlaced m := leadInterlaced ℚ r n ν f hf hf0
    have hcol : ∀ t : Fin n, ∑ a : Fin r, m (a, t) = ν t :=
      colSums ℚ r n ν f hf m (((colLex r n).degree_mem_support_iff f).mpr hf0)
    obtain ⟨K, sz, hsz, I, hshape, hmono, hexp⟩ := sSYTExists r n ν m hcol hint
    obtain ⟨hbdeg, hblc⟩ := column_lex_bideterminant ℚ r n K sz hsz I hmono
    have hbmap : bideterminant ℚ sz hsz I = intQ r n (bideterminant ℤ sz hsz I) := by
      rw [lre_intQ_apply, ldlat_map_bidet]
    have hbmem : bideterminant ℚ sz hsz I ∈ dualWeyl ℚ r n ν := by
      have := bidetMem ℚ r n K sz hsz I
      rw [hshape] at this
      exact this
    have hmL : LowerTri m := by
      rw [← hexp]
      exact lre_lowerTri sz hsz I hmono
    obtain ⟨c, hc⟩ := hz m hmL
    have hlc : (colLex r n).leadingCoeff f = (c : ℚ) := hc
    have hf'mem : f - (colLex r n).leadingCoeff f • bideterminant ℚ sz hsz I ∈ dualWeyl ℚ r n ν :=
      Submodule.sub_mem _ hf (Submodule.smul_mem _ _ hbmem)
    have hf'z : ∀ e : Fin r × Fin n →₀ ℕ, LowerTri e →
        ∃ z : ℤ, coeff e (f - (colLex r n).leadingCoeff f • bideterminant ℚ sz hsz I) = z := by
      intro e he
      obtain ⟨z, hz'⟩ := hz e he
      refine ⟨z - c * coeff e (bideterminant ℤ sz hsz I), ?_⟩
      rw [coeff_sub, coeff_smul, hz', hlc, hbmap, lre_intQ_apply, coeff_map]
      simp
    have hfin : ∃ Q'' : MvPolynomial (Fin r × Fin n) ℤ,
        f - (colLex r n).leadingCoeff f • bideterminant ℚ sz hsz I = intQ r n Q'' := by
      by_cases h0 : f - (colLex r n).leadingCoeff f • bideterminant ℚ sz hsz I = 0
      · exact ⟨0, by rw [h0, map_zero]⟩
      · have hlt := lcassem_sub_lt (colLex r n) (f := f) (g := bideterminant ℚ sz hsz I) (hbdeg.trans hexp) hblc h0
        exact ih _ (hd ▸ hlt) _ hf'mem hf'z rfl
    obtain ⟨Q'', hQ''⟩ := hfin
    refine ⟨Q'' + c • bideterminant ℤ sz hsz I, ?_⟩
    rw [map_add, map_smul, ← hQ'', ← hbmap, hlc, Int.cast_smul_eq_zsmul]
    abel

end Formalism.CohomologicalDescent.LR
