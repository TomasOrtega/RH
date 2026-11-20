import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DualGramSubstitution.BeMulByZero

noncomputable section

open Classical

namespace PI.UnitaryGroupMassFormula.PhDualGram

open PI.FglGram MvPowerSeries

/- English proof (translation)
Introduce `p _ l ex ph S hD hG κ ι _ _ b b' hb hb' hI`. Take `⟨hex0, hinv, hph0⟩` from `hD`. Take `⟨hl0, hinvl⟩` from `PI.FglPhSplit.Wk.compositionalInverseSymm ℂ_[p] l ex hex0 hinv`. Set `eι : ι ≃ Fin (Fintype.card ι)` to `Fintype.equivFin ι`. Set `E : ι ⊕ ι ≃ Fin (Fintype.card ι + Fintype.card ι)` to `(Equiv.sumCongr eι eι).trans finSumFinEquiv`.

Establish `hE : ∀ e e', E (Sum.inl e) < E (Sum.inr e')`. Introduce `e e'`. Simplify using `only [E, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, Fin.lt_def, Fin.val_castAdd, Fin.val_natAdd]`. Use `(eι e).isLt` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Establish `hS : ∀ j i, Sum.elim b b' (E.symm j) i ∈ S`. Introduce `j i`. Break down `E.symm j with e | e` into its components or cases. Use `exacts [hb e i, hb' e i]`. Establish `h` using `simeq_ren (p := p) E.symm (hG κ _ (fun j => Sum.elim b b' (E.symm j)) hS)`.

Rewrite `h` using `[ren_PhOn hex0 hl0 E (Sum.elim b b'), gramRhs_dual hex0 hph0 hl0 hinvl b b' hI E hE, map_sum]`. Use `(congrArg (Simeq _) ?_).mp h` and prove the remaining obligations. Unfold `beSum`. Use `Finset.sum_congr rfl fun e _ => ?_` and prove the remaining obligations. Rewrite using `[ren_be hex0 hl0 _ (constantCoeff_X _) (constantCoeff_X _)]`.

Simplify using `only [Xv, ren_X, Equiv.symm_apply_apply]`.
-/
theorem phDualGram_main : PhDualGram := by
  intro p _ l ex ph S hD hG κ ι _ _ b b' hb hb' hI
  obtain ⟨hex0, hinv, hph0⟩ := hD
  obtain ⟨hl0, hinvl⟩ := PI.FglPhSplit.Wk.compositionalInverseSymm ℂ_[p] l ex hex0 hinv
  let eι : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let E : ι ⊕ ι ≃ Fin (Fintype.card ι + Fintype.card ι) :=
    (Equiv.sumCongr eι eι).trans finSumFinEquiv
  have hE : ∀ e e', E (Sum.inl e) < E (Sum.inr e') := by
    intro e e'
    simp only [E, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr,
      finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, Fin.lt_def, Fin.val_castAdd,
      Fin.val_natAdd]
    have := (eι e).isLt
    omega
  have hS : ∀ j i, Sum.elim b b' (E.symm j) i ∈ S := by
    intro j i
    rcases E.symm j with e | e
    exacts [hb e i, hb' e i]
  have h := simeq_ren (p := p) E.symm (hG κ _ (fun j => Sum.elim b b' (E.symm j)) hS)
  rw [ren_PhOn hex0 hl0 E (Sum.elim b b'), gramRhs_dual hex0 hph0 hl0 hinvl b b' hI E hE,
    map_sum] at h
  refine (congrArg (Simeq _) ?_).mp h
  unfold beSum
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [ren_be hex0 hl0 _ (constantCoeff_X _) (constantCoeff_X _)]
  simp only [Xv, ren_X, Equiv.symm_apply_apply]

end PI.UnitaryGroupMassFormula.PhDualGram

end
