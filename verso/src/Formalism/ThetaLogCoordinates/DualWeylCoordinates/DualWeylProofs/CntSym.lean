import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.ExtendedColumns

noncomputable section

open Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

open Formalism.InvariantFactorPaths.GelfandTsetlinBases (dGT)

/- English proof (translation)
Consider the cases of `n with`. Consider the case `zero => intro a`. Conclude with `a.elim0`. Consider the case `succ m`. Rewrite using `[Fin.antitone_iff_succ_le]`.

Introduce `i`. Conclude with `h i.castSucc (by simp)`.
-/
lemma qk_antitone_of_step {n : ℕ} {f : Fin n → ℤ} (h : ∀ a : Fin n, ∀ h : a.1 + 1 < n, f ⟨a.1 + 1, h⟩ ≤ f a) :
    Antitone f := by
  cases n with
  | zero => intro a; exact a.elim0
  | succ m =>
    rw [Fin.antitone_iff_succ_le]
    intro i
    exact h i.castSucc (by simp)

/- English proof (translation)
Assemble the required witnesses or components as `⟨qk_antitone_of_step fun a ha => (h.1 _).trans (h.2.1 a ha), qk_antitone_of_step fun a ha => (h.2.1 a ha).trans (h.1 a)⟩`.
-/
lemma qk_hstrip_dom {n : ℕ} {nu mu : Fin n → ℤ} {b : ℕ} (h : HStrip nu mu b) : Dominant nu ∧ Dominant mu :=
  ⟨qk_antitone_of_step fun a ha => (h.1 _).trans (h.2.1 a ha),
   qk_antitone_of_step fun a ha => (h.2.1 a ha).trans (h.1 a)⟩

/- English proof (translation)
Unfold `HStrip Formalism.InvariantFactorPaths.GelfandTsetlinBases.HStrip`. Use `and_congr Iff.rfl (and_congr ?_ ?_)` and prove the remaining obligations. Prove the components needed by the constructor for the conclusion. Introduce `h m m' hm`. Use `h m (by have := m'.2; omega)` as an intermediate fact.

Establish `e : (⟨m.1 + 1, by have` using `m'.2; omega⟩ : Fin n) = m' := Fin.ext hm`. Rewrite `this` using `[e]`. Then use the resulting hypothesis. Introduce `h a ha`. Conclude with `h a ⟨a.1 + 1, ha⟩ rfl`. Rewrite using `[sum_sub_distrib]`.
-/
lemma qk_hstrip_iff {n : ℕ} (nu mu : Fin n → ℤ) (b : ℕ) : HStrip nu mu b ↔ Formalism.InvariantFactorPaths.GelfandTsetlinBases.HStrip mu nu b := by
  unfold HStrip Formalism.InvariantFactorPaths.GelfandTsetlinBases.HStrip
  refine and_congr Iff.rfl (and_congr ?_ ?_)
  · constructor
    · intro h m m' hm
      have := h m (by have := m'.2; omega)
      have e : (⟨m.1 + 1, by have := m'.2; omega⟩ : Fin n) = m' := Fin.ext hm
      rwa [e] at this
    · intro h a ha
      exact h a ⟨a.1 + 1, ha⟩ rfl
  · rw [sum_sub_distrib]

/- English proof (translation)
Unfold `strUp Formalism.InvariantFactorPaths.GelfandTsetlinBases.stripsUp`. Use extensionality with `nu`. Simplify using `only [mem_filter, qk_hstrip_iff]`.
-/
lemma qk_strUp_eq {n : ℕ} (mu : Fin n → ℤ) (b : ℕ) : strUp mu b = Formalism.InvariantFactorPaths.GelfandTsetlinBases.stripsUp mu b := by
  unfold strUp Formalism.InvariantFactorPaths.GelfandTsetlinBases.stripsUp
  ext nu
  simp only [mem_filter, qk_hstrip_iff]

/- English proof (translation)
Unfold `strDown Formalism.InvariantFactorPaths.GelfandTsetlinBases.stripsDown`. Use extensionality with `nu`. Simplify using `only [mem_filter, qk_hstrip_iff]`.
-/
lemma qk_strDown_eq {n : ℕ} (mu : Fin n → ℤ) (b : ℕ) : strDown mu b = Formalism.InvariantFactorPaths.GelfandTsetlinBases.stripsDown mu b := by
  unfold strDown Formalism.InvariantFactorPaths.GelfandTsetlinBases.stripsDown
  ext nu
  simp only [mem_filter, qk_hstrip_iff]

/- English proof (translation)
Unfold `strUp at h`. Simplify using `only [mem_filter] at h`. Conclude with `h.2`.
-/
lemma qk_mem_strUp {n : ℕ} {mu nu : Fin n → ℤ} {b : ℕ} (h : nu ∈ strUp mu b) : HStrip mu nu b := by
  unfold strUp at h
  simp only [mem_filter] at h
  exact h.2

/- English proof (translation)
Unfold `strDown at h`. Simplify using `only [mem_filter] at h`. Conclude with `h.2`.
-/
lemma qk_mem_strDown {n : ℕ} {mu nu : Fin n → ℤ} {b : ℕ} (h : nu ∈ strDown mu b) : HStrip nu mu b := by
  unfold strDown at h
  simp only [mem_filter] at h
  exact h.2

def qk_symEquiv (n b : ℕ) : SymIdx n b ≃ {P : Fin n → ℕ // ∑ i, P i = b} where
  toFun α := ⟨fun a => (α.1 a : ℕ), α.2⟩
  invFun P := ⟨fun a => ⟨P.1 a, by
    have := single_le_sum (f := P.1) (fun i _ => Nat.zero_le _) (mem_univ a)
    have h2 := P.2
    omega⟩, P.2⟩
  left_inv α := rfl
  right_inv P := rfl

/- English proof (translation)
Rewrite using `[Fintype.card_congr ((qk_symEquiv n b).trans (Sym.equivNatSumOfFintype (Fin n) b).symm), Sym.card_sym_eq_choose, Fintype.card_fin]`.
-/
lemma qk_card_symIdx (n b : ℕ) : Fintype.card (SymIdx n b) = (n + b - 1).choose b := by
  rw [Fintype.card_congr ((qk_symEquiv n b).trans (Sym.equivNatSumOfFintype (Fin n) b).symm),
    Sym.card_sym_eq_choose, Fintype.card_fin]

/- English proof (translation)
Introduce `n _ mu b hmu`. Rewrite using `[qk_card_symIdx, qk_dMu_eq_dGT n mu hmu, ← (Formalism.InvariantFactorPaths.GelfandTsetlinBases.Top.gtPieri n mu b hmu).1, ← qk_strUp_eq]`. Use `sum_congr rfl fun nu hnu => ?_` and prove the remaining obligations. Rewrite using `[qk_dMu_eq_dGT n nu (qk_hstrip_dom (qk_mem_strUp hnu)).2]`.
-/
theorem symmetric_power_count_holds : CntSym := by
  intro n _ mu b hmu
  rw [qk_card_symIdx, qk_dMu_eq_dGT n mu hmu, ← (Formalism.InvariantFactorPaths.GelfandTsetlinBases.Top.gtPieri n mu b hmu).1, ← qk_strUp_eq]
  refine sum_congr rfl fun nu hnu => ?_
  rw [qk_dMu_eq_dGT n nu (qk_hstrip_dom (qk_mem_strUp hnu)).2]

/- English proof (translation)
Introduce `n _ mu b hmu`. Rewrite using `[qk_card_symIdx, qk_dMu_eq_dGT n mu hmu, ← (Formalism.InvariantFactorPaths.GelfandTsetlinBases.Top.gtPieri n mu b hmu).2, ← qk_strDown_eq]`. Use `sum_congr rfl fun nu hnu => ?_` and prove the remaining obligations. Rewrite using `[qk_dMu_eq_dGT n nu (qk_hstrip_dom (qk_mem_strDown hnu)).1]`.
-/
theorem dual_symmetric_power_count_holds : CntSymD := by
  intro n _ mu b hmu
  rw [qk_card_symIdx, qk_dMu_eq_dGT n mu hmu, ← (Formalism.InvariantFactorPaths.GelfandTsetlinBases.Top.gtPieri n mu b hmu).2, ← qk_strDown_eq]
  refine sum_congr rfl fun nu hnu => ?_
  rw [qk_dMu_eq_dGT n nu (qk_hstrip_dom (qk_mem_strDown hnu)).1]

end Formalism.InvariantFactorPaths.ColumnFamilies
