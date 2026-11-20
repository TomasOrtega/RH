import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.InductiveHeisenbergInputs

noncomputable section

namespace ReciprocityTheory.ChartRestriction.DS.Xi

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

/- English proof (translation)
Introduce `k r hk`. Proceed by induction on `r with`. Consider the case `zero => exact hb k hk`. Consider the case `succ r' ih => exact hs k (r' + 1) r' (by omega) hk ih`.
-/
theorem aAll_of (hb : AStepBase) (hs : AStepSucc) : ∀ k r : ℕ, 1 ≤ k → AAt k r := by
  intro k r hk
  induction r with
  | zero => exact hb k hk
  | succ r' ih => exact hs k (r' + 1) r' (by omega) hk ih

/- English proof (translation)
Introduce `k r hk`. Proceed by induction on `r with`. Consider the case `zero => intro δ hδ _`. Conclude with `hb k hk δ hδ`. Consider the case `succ r' ih`.

Introduce `δ hδ hδ'`. Conclude with `hs k (r' + 1) r' (by omega) hk δ hδ hδ' (ih (δ / 4) (by positivity) (by linarith))`.
-/
theorem bAll_of (hb : BStepBase) (hs : BStepSucc) :
    ∀ k r : ℕ, 1 ≤ k → ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 2 → BAt k r δ := by
  intro k r hk
  induction r with
  | zero => intro δ hδ _; exact hb k hk δ hδ
  | succ r' ih =>
    intro δ hδ hδ'
    exact hs k (r' + 1) r' (by omega) hk δ hδ hδ' (ih (δ / 4) (by positivity) (by linarith))

/- English proof (translation)
Introduce `k r Wp Wq _ _ _ _ _ _ D A hA'`. Take `⟨eS, heS, hBs⟩` from `hB k r D.k_pos`. Establish `he0 : 0 < min eS (1 / 10 : ℝ)` using `lt_min heS (by norm_num)`. Establish `adm : SAdm k r (fun l => s0 k r l - min eS (1 / 10))` using `fun l => by`. Simplify using `only [sub_sub_cancel]`.

Conclude with `⟨he0, min_le_right _ _⟩`. Establish `adm' : ∀ l, 0 < s0 k r l - (s0 k r l - min eS (1 / 10)) ∧ s0 k r l - (s0 k r l - min eS (1 / 10)) ≤ eS` using `fun l => by simp only [sub_sub_cancel]; exact ⟨he0, min_le_left _ _⟩`. Conclude with `⟨xiN k r _, hC k r Wp Wq D A _ adm hA' (hA k r D.k_pos _ adm D.μG D.haarG A hA'), hX k r Wp Wq D _ adm (hBs _ adm' D.z D.z_mem D.T_pos D.μN D.haarN) (hBs _ adm' D.z' D.z'_mem D.T'_pos D.μN D.haarN)⟩`.
-/
theorem xiExists_of (hA : ∀ k r : ℕ, 1 ≤ k → AAt k r) (hB : ∀ k r : ℕ, 1 ≤ k → BAt k r (1 / 2))
    (hC : CoefStep) (hX : XiIntStep) : XiExists := by
  intro k r Wp Wq _ _ _ _ _ _ D A hA'
  obtain ⟨eS, heS, hBs⟩ := hB k r D.k_pos
  have he0 : 0 < min eS (1 / 10 : ℝ) := lt_min heS (by norm_num)
  have adm : SAdm k r (fun l => s0 k r l - min eS (1 / 10)) := fun l => by
    simp only [sub_sub_cancel]; exact ⟨he0, min_le_right _ _⟩
  have adm' : ∀ l, 0 < s0 k r l - (s0 k r l - min eS (1 / 10)) ∧ s0 k r l - (s0 k r l - min eS (1 / 10)) ≤ eS :=
    fun l => by simp only [sub_sub_cancel]; exact ⟨he0, min_le_left _ _⟩
  exact ⟨xiN k r _, hC k r Wp Wq D A _ adm hA' (hA k r D.k_pos _ adm D.μG D.haarG A hA'),
    hX k r Wp Wq D _ adm (hBs _ adm' D.z D.z_mem D.T_pos D.μN D.haarN)
      (hBs _ adm' D.z' D.z'_mem D.T'_pos D.μN D.haarN)⟩

/- English proof (translation)
The claim follows from `xiExists_of (aAll_of hAb hAs) (fun k r hk => bAll_of hBb hBs k r hk (1 / 2) (by norm_num) le_rfl) hC hX`.
-/
theorem xiExists_of_induction_steps (hAb : AStepBase) (hAs : AStepSucc) (hBb : BStepBase) (hBs : BStepSucc)
    (hC : CoefStep) (hX : XiIntStep) : XiExists :=
  xiExists_of (aAll_of hAb hAs) (fun k r hk => bAll_of hBb hBs k r hk (1 / 2) (by norm_num) le_rfl) hC hX

end ReciprocityTheory.ChartRestriction.DS.Xi
