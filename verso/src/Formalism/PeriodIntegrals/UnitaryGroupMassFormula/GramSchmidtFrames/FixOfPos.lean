import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GramSchmidtFrames.AdjugateLastEntrySum

open MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C6
open Matrix

noncomputable section

namespace PI.UnitaryGroupMassFormula.GsFr
open PI.UnitaryGroupMassFormula.DLm.Gram

def StabCore : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), 1 ≤ k → 1 ≤ r → C2.StdZ k r z → C2.StdZ k r z' →
    ∀ D0 : GfBaseD k r z z', ∀ y ∈ gfSig D0, ∀ α ∈ UWset k r z, ∀ β ∈ UWset k r z',
      α *ᵥ D0.nu = D0.nu → β⁻¹ *ᵥ D0.nu' = D0.nu' →
      α * y * β ∈ gfSig D0 → Rel z z' y (α * y * β)

section eqv

variable {k r : ℕ}

/- English proof (translation)
Take `⟨μ, _, _, rfl⟩` from `(Formalism.FourierDecayAlt.P.TwoByOneBlock.UWset_iff hz α).1 hα`. Break down `h with h | h` into its components or cases. Conclude with `Formalism.FourierDecayAlt.P.TwoByOneBlock.emb_out_row μ i j h`. Conclude with `Formalism.FourierDecayAlt.P.TwoByOneBlock.emb_out_col μ i j h`.
-/
lemma uw_entry {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) {α : B.Mat k r} (hα : α ∈ UWset k r z)
    (i j : Fin (2 * r + k + 1)) (h : ¬ (r ≤ i.val ∧ i.val ≤ r + k) ∨ ¬ (r ≤ j.val ∧ j.val ≤ r + k)) :
    α i j = if i = j then 1 else 0 := by
  obtain ⟨μ, _, _, rfl⟩ := (Formalism.FourierDecayAlt.P.TwoByOneBlock.UWset_iff hz α).1 hα
  rcases h with h | h
  · exact Formalism.FourierDecayAlt.P.TwoByOneBlock.emb_out_row μ i j h
  · exact Formalism.FourierDecayAlt.P.TwoByOneBlock.emb_out_col μ i j h

/- English proof (translation)
Use function extensionality and compare the values at `i`. Unfold `PI.UnitaryGroupMassFormula.GsFr.wbPart`. Simplify using `only [mulVec, dotProduct]`. Use `split_ifs with hi`. Use `Finset.sum_congr rfl fun j _ => ?_ split_ifs with hj` and prove the remaining obligations.

Both sides reduce to the same expression. Apply the tactic sequence `rw [uw_entry hz hα i j (Or.inr hj), if_neg (fun (e : i = j) => hj (e ▸ hi)), zero_mul, mul_zero]`. Use `symm`. Use `Finset.sum_eq_zero fun j _ => ?_` and prove the remaining obligations. Apply the tactic sequence `rw [uw_entry hz hα i j (Or.inl hi)]`.

Use `split_ifs with h1 h2`. Substitute `h1` using the available equality. Conclude with `absurd h2 hi`. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules.
-/
lemma wb_UW {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) {α : B.Mat k r} (hα : α ∈ UWset k r z)
    (v : Fin (2 * r + k + 1) → ℂ) :
    PI.UnitaryGroupMassFormula.GsFr.wbPart k r (α *ᵥ v) = α *ᵥ PI.UnitaryGroupMassFormula.GsFr.wbPart k r v := by
  funext i
  unfold PI.UnitaryGroupMassFormula.GsFr.wbPart
  simp only [mulVec, dotProduct]
  split_ifs with hi
  · refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs with hj
    · rfl
    · rw [uw_entry hz hα i j (Or.inr hj), if_neg (fun (e : i = j) => hj (e ▸ hi)), zero_mul, mul_zero]
  · symm
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [uw_entry hz hα i j (Or.inl hi)]
    split_ifs with h1 h2
    · subst h1; exact absurd h2 hi
    · simp
    · simp
    · simp

/- English proof (translation)
Establish `hUz` using `Formalism.FourierDecayAlt.P.TwoByOneBlock.herm_UH hα.1 (PI.UnitaryGroupMassFormula.GsFr.wbPart k r v) z`. Rewrite `hUz` using `[hα.2.2]`. Unfold `prW`. Rewrite using `[wb_UW hz.1 hα, hUz, mulVec_add, mulVec_smul, hα.2.2]`.
-/
lemma prW_UW {z : Fin (2 * r + k + 1) → ℂ} (hz : C2.StdZ k r z) {α : B.Mat k r} (hα : α ∈ UWset k r z)
    (v : Fin (2 * r + k + 1) → ℂ) : prW k r z (α *ᵥ v) = α *ᵥ prW k r z v := by
  have hUz := Formalism.FourierDecayAlt.P.TwoByOneBlock.herm_UH hα.1 (PI.UnitaryGroupMassFormula.GsFr.wbPart k r v) z
  rw [hα.2.2] at hUz
  unfold prW
  rw [wb_UW hz.1 hα, hUz, mulVec_add, mulVec_smul, hα.2.2]

/- English proof (translation)
Unfold `fvec`. Use `split_ifs with h`. Conclude with `(hα.2.1 ⟨b.val, h⟩).1`. Conclude with `hα.2.2`.
-/
lemma uw_fvec {z : Fin (2 * r + k + 1) → ℂ} {α : B.Mat k r} (hα : α ∈ UWset k r z) (b : Fin (r + 1)) :
    α *ᵥ fvec k r z b = fvec k r z b := by
  unfold fvec
  split_ifs with h
  · exact (hα.2.1 ⟨b.val, h⟩).1
  · exact hα.2.2

/- English proof (translation)
Use function extensionality and compare the values at `a b`. Simplify using `only [Zhat]`. Rewrite using `[← mulVec_mulVec, uw_fvec hβ, ← mulVec_mulVec]`. Use `conv_lhs => rw [← uw_fvec hα a]`. Rewrite using `[Formalism.FourierDecayAlt.P.TwoByOneBlock.herm_UH hα.1]`.
-/
lemma zhat_UW {z z' : Fin (2 * r + k + 1) → ℂ} {α β : B.Mat k r} (hα : α ∈ UWset k r z) (hβ : β ∈ UWset k r z')
    (y : B.Mat k r) : Zhat k r z z' (α * y * β) = Zhat k r z z' y := by
  funext a b
  simp only [Zhat]
  rw [← mulVec_mulVec, uw_fvec hβ, ← mulVec_mulVec]
  conv_lhs => rw [← uw_fvec hα a]
  rw [Formalism.FourierDecayAlt.P.TwoByOneBlock.herm_UH hα.1]

/- English proof (translation)
Unfold `xcof`. Rewrite using `[zhat_UW hα hβ, mv_sum]`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Rewrite using `[mulVec_smul, ← mulVec_mulVec, uw_fvec hβ, ← mulVec_mulVec]`.
-/
lemma xcof_UW {z z' : Fin (2 * r + k + 1) → ℂ} {α β : B.Mat k r} (hα : α ∈ UWset k r z) (hβ : β ∈ UWset k r z')
    (y : B.Mat k r) : xcof k r z z' (α * y * β) = α *ᵥ xcof k r z z' y := by
  unfold xcof
  rw [zhat_UW hα hβ, mv_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [mulVec_smul, ← mulVec_mulVec, uw_fvec hβ, ← mulVec_mulVec]

/- English proof (translation)
Unfold `xcofL`. Rewrite using `[zhat_UW hα hβ]`.
-/
lemma xcofL_UW {z z' : Fin (2 * r + k + 1) → ℂ} {α β : B.Mat k r} (hα : α ∈ UWset k r z) (hβ : β ∈ UWset k r z')
    (y : B.Mat k r) : xcofL k r z z' (α * y * β) = xcofL k r z z' y := by
  unfold xcofL; rw [zhat_UW hα hβ]

/- English proof (translation)
Unfold `xcofL`. Rewrite using `[mv_sum]`. Conclude with `Finset.sum_congr rfl fun a _ => by rw [mulVec_smul, uw_fvec hα]`.
-/
lemma xcofL_fix {z z' : Fin (2 * r + k + 1) → ℂ} {α : B.Mat k r} (hα : α ∈ UWset k r z) (y : B.Mat k r) :
    α *ᵥ xcofL k r z z' y = xcofL k r z z' y := by
  unfold xcofL
  rw [mv_sum]
  exact Finset.sum_congr rfl fun a _ => by rw [mulVec_smul, uw_fvec hα]

/- English proof (translation)
Unfold `omW`. Rewrite using `[xcof_UW hα hβ, prW_UW hz hα]`.
-/
theorem omW_UW {z z' : Fin (2 * r + k + 1) → ℂ} (hz : C2.StdZ k r z) {α β : B.Mat k r} (hα : α ∈ UWset k r z)
    (hβ : β ∈ UWset k r z') (y : B.Mat k r) : omW k r z z' (α * y * β) = α *ᵥ omW k r z z' y := by
  unfold omW; rw [xcof_UW hα hβ, prW_UW hz hα]

/- English proof (translation)
Establish `Wz` using `Formalism.FourierDecayAlt.P.weyl_subgroup_closed k r z`. Establish `Wz'` using `Formalism.FourierDecayAlt.P.weyl_subgroup_closed k r z'`. Unfold `omW'`. Rewrite using `[xcofL_UW hα hβ, Matrix.mul_inv_rev, Matrix.mul_inv_rev, ← mulVec_mulVec, ← mulVec_mulVec, xcofL_fix (Wz.inv_mem α hα), prW_UW hz' (Wz'.inv_mem β hβ)]`.
-/
theorem omW'_UW {z z' : Fin (2 * r + k + 1) → ℂ} (hz : C2.StdZ k r z) (hz' : C2.StdZ k r z') {α β : B.Mat k r}
    (hα : α ∈ UWset k r z) (hβ : β ∈ UWset k r z') (y : B.Mat k r) :
    omW' k r z z' (α * y * β) = β⁻¹ *ᵥ omW' k r z z' y := by
  have Wz := Formalism.FourierDecayAlt.P.weyl_subgroup_closed k r z
  have Wz' := Formalism.FourierDecayAlt.P.weyl_subgroup_closed k r z'
  unfold omW'
  rw [xcofL_UW hα hβ, Matrix.mul_inv_rev, Matrix.mul_inv_rev, ← mulVec_mulVec, ← mulVec_mulVec,
    xcofL_fix (Wz.inv_mem α hα), prW_UW hz' (Wz'.inv_mem β hβ)]

/- English proof (translation)
Establish `hsc : ∀ (t : ℝ) (u : Fin (2 * r + k + 1) → ℂ), herm (Hpk k r) ((t : ℂ) • u) ((t : ℂ) • u) = ((t ^ 2 : ℝ) : ℂ) * herm (Hpk k r) u u`. Introduce `t u`. Simplify using `only [herm, Matrix.mulVec_smul, star_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, Complex.star_def, Complex.conj_ofReal]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Establish `h3` using `congrArg (fun u => herm (Hpk k r) u u) e`. Rewrite `h3` using `[hsc, hsc, hv, hw, mul_one, mul_one]`. Establish `h4 : t₁ ^ 2 = t₂ ^ 2` using `by exact_mod_cast h3`. Establish `h5 : t₁ = t₂` using `(pow_left_inj₀ h1.le h2.le two_ne_zero).mp h4`. Substitute `h5` using the available equality.

Conclude with `smul_right_injective _ (by exact_mod_cast h1.ne') e`.
-/
lemma fix_of_pos {v w : Fin (2 * r + k + 1) → ℂ} (hw : herm (Hpk k r) w w = 1) (hv : herm (Hpk k r) v v = 1)
    {t₁ t₂ : ℝ} (h1 : 0 < t₁) (h2 : 0 < t₂) (e : (t₁ : ℂ) • v = (t₂ : ℂ) • w) : v = w := by
  have hsc : ∀ (t : ℝ) (u : Fin (2 * r + k + 1) → ℂ),
      herm (Hpk k r) ((t : ℂ) • u) ((t : ℂ) • u) = ((t ^ 2 : ℝ) : ℂ) * herm (Hpk k r) u u := by
    intro t u
    simp only [herm, Matrix.mulVec_smul, star_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul,
      Complex.star_def, Complex.conj_ofReal]
    push_cast
    ring
  have h3 := congrArg (fun u => herm (Hpk k r) u u) e
  rw [hsc, hsc, hv, hw, mul_one, mul_one] at h3
  have h4 : t₁ ^ 2 = t₂ ^ 2 := by exact_mod_cast h3
  have h5 : t₁ = t₂ := (pow_left_inj₀ h1.le h2.le two_ne_zero).mp h4
  subst h5
  exact smul_right_injective _ (by exact_mod_cast h1.ne') e

end eqv

/- English proof (translation)
Introduce `k r z z' hk hr hz hz' D0 y hy α hα β hβ hay`. Establish `Wz'` using `Formalism.FourierDecayAlt.P.weyl_subgroup_closed k r z'`. Establish `hH` using `Formalism.QuantumDeterminants.hpkFacts k r`. Establish `hy2` using `hy`. Establish `hay2` using `hay`.

Take `⟨_, _, ⟨t, ht, hom⟩, ⟨t', ht', hom'⟩, _⟩` from `hy2`. Take `⟨_, _, ⟨s, hs, hos⟩, ⟨s', hs', hos'⟩, _⟩` from `hay2`. Use `hC k r z z' hk hr hz hz' D0 y hy α hα β hβ ?_ ?_ hay` and prove the remaining obligations. Rewrite `hos` using `[omW_UW hz hα hβ, hom, mulVec_smul]`. Establish `hαu : herm (Hpk k r) (α *ᵥ D0.nu) (α *ᵥ D0.nu) = 1`.

Rewrite using `[Formalism.FourierDecayAlt.P.TwoByOneBlock.herm_UH hα.1]`. Conclude with `D0.nu_unit`. Conclude with `fix_of_pos D0.nu_unit hαu ht hs hos`. Rewrite `hos'` using `[omW'_UW hz hz' hα hβ, hom', mulVec_smul]`. Establish `hβu : herm (Hpk k r) (β⁻¹ *ᵥ D0.nu') (β⁻¹ *ᵥ D0.nu') = 1`.

Rewrite using `[Formalism.FourierDecayAlt.P.TwoByOneBlock.herm_UH (Wz'.inv_mem β hβ).1]`. Conclude with `D0.nu'_unit`. Conclude with `fix_of_pos D0.nu'_unit hβu ht' hs' hos'`.
-/
theorem gfStab_of (hC : StabCore) : GfStab := by
  intro k r z z' hk hr hz hz' D0 y hy α hα β hβ hay
  have Wz' := Formalism.FourierDecayAlt.P.weyl_subgroup_closed k r z'
  have hH := Formalism.QuantumDeterminants.hpkFacts k r
  have hy2 := hy
  have hay2 := hay
  obtain ⟨_, _, ⟨t, ht, hom⟩, ⟨t', ht', hom'⟩, _⟩ := hy2
  obtain ⟨_, _, ⟨s, hs, hos⟩, ⟨s', hs', hos'⟩, _⟩ := hay2
  refine hC k r z z' hk hr hz hz' D0 y hy α hα β hβ ?_ ?_ hay
  · rw [omW_UW hz hα hβ, hom, mulVec_smul] at hos
    have hαu : herm (Hpk k r) (α *ᵥ D0.nu) (α *ᵥ D0.nu) = 1 := by
      rw [Formalism.FourierDecayAlt.P.TwoByOneBlock.herm_UH hα.1]; exact D0.nu_unit
    exact fix_of_pos D0.nu_unit hαu ht hs hos
  · rw [omW'_UW hz hz' hα hβ, hom', mulVec_smul] at hos'
    have hβu : herm (Hpk k r) (β⁻¹ *ᵥ D0.nu') (β⁻¹ *ᵥ D0.nu') = 1 := by
      rw [Formalism.FourierDecayAlt.P.TwoByOneBlock.herm_UH (Wz'.inv_mem β hβ).1]; exact D0.nu'_unit
    exact fix_of_pos D0.nu'_unit hβu ht' hs' hos'

end PI.UnitaryGroupMassFormula.GsFr
