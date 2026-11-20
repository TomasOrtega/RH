import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MonodromyZeroOfWeilDeligneRepClassIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPowEqPowOfWeilDegreeEqSmoothStatement

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module GlobalTheory.WeilDeligne

namespace GlobalTheory.WeilDeligne

/- English proof (translation)
Introduce `v hv`. Rewrite `hv`, the goal using `[End.mem_eigenspace_iff]`. Proceed by induction on `m with`. Consider the case `zero => simp`. Consider the case `succ m ih => rw [pow_succ', End.mul_apply, ih, map_smul, hv, smul_smul, pow_succ]`.
-/
theorem eigenspace_le_eigenspace_pow {V : Type*} [AddCommGroup V] [Module ℂ V] (f : End ℂ V)
    (α : ℂ) (m : ℕ) : f.eigenspace α ≤ (f ^ m).eigenspace (α ^ m) := by
  intro v hv
  rw [End.mem_eigenspace_iff] at hv ⊢
  induction m with
  | zero => simp
  | succ m ih => rw [pow_succ', End.mul_apply, ih, map_smul, hv, smul_smul, pow_succ]

/- English proof (translation)
Rewrite using `[absSpace, eq_bot_iff]`. Conclude with `iSup₂_le fun α hα => absurd (hα ▸ norm_nonneg α) (not_le.mpr hr)`.
-/
theorem absSpace_of_neg {V : Type*} [AddCommGroup V] [Module ℂ V] (f : End ℂ V) {r : ℝ}
    (hr : r < 0) : absSpace f r = ⊥ := by
  rw [absSpace, eq_bot_iff]
  exact iSup₂_le fun α hα => absurd (hα ▸ norm_nonneg α) (not_le.mpr hr)

/- English proof (translation)
Establish `hP : absSpace f r ≤ absSpace (f ^ m) (r ^ m)` using `iSup₂_le fun α hα => (eigenspace_le_eigenspace_pow f α m).trans (le_iSup₂_of_le (f := fun (β : ℂ) (_ : ‖β‖ = r ^ m) => (f ^ m).eigenspace β) (α ^ m) (by rw [norm_pow, hα]) le_rfl)`. Use `set Q : Submodule ℂ V := ⨆ β ∈ {β : ℂ | ‖β‖ ≠ r ^ m}, (f ^ m).eigenspace β with hQ`. Establish `hd : Disjoint (absSpace (f ^ m) (r ^ m)) Q` using `(End.eigenspaces_iSupIndep (f ^ m)).disjoint_biSup_biSup (s := {β : ℂ | ‖β‖ = r ^ m}) (t := {β : ℂ | ‖β‖ ≠ r ^ m}) (Set.disjoint_left.mpr fun _ h1 h2 => h2 h1)`. Establish `ht : absSpace f r ⊔ Q = ⊤`. Rewrite using `[eq_top_iff, ← hf.iSup_eigenspace_eq_top]`.

Use `iSup_le fun α => ?_` and prove the remaining obligations. Distinguish the cases in `hα : ‖α‖ = r`. Conclude with `le_sup_of_le_left (le_iSup₂_of_le (f := fun (β : ℂ) (_ : ‖β‖ = r) => f.eigenspace β) α hα le_rfl)`. Use `le_sup_of_le_right ((eigenspace_le_eigenspace_pow f α m).trans ?_)` and prove the remaining obligations. Use `le_iSup₂_of_le (f := fun β (_ : β ∈ {β : ℂ | ‖β‖ ≠ r ^ m}) => (f ^ m).eigenspace β) (α ^ m) ?_ le_rfl` and prove the remaining obligations.

Introduce `h`. Rewrite `h` using `[norm_pow]`. Conclude with `hα ((pow_left_inj₀ (norm_nonneg α) hr hm.ne').mp h)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[ht, top_inf_eq]`.

Use `_ = absSpace f r := by rw [sup_inf_assoc_of_le _ hP, hd.symm.eq_bot, sup_bot_eq]`.
-/
theorem absSpace_pow {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {f : End ℂ V} (hf : f.IsSemisimple) {m : ℕ} (hm : 0 < m) {r : ℝ} (hr : 0 ≤ r) :
    absSpace (f ^ m) (r ^ m) = absSpace f r := by
  have hP : absSpace f r ≤ absSpace (f ^ m) (r ^ m) :=
    iSup₂_le fun α hα => (eigenspace_le_eigenspace_pow f α m).trans
      (le_iSup₂_of_le (f := fun (β : ℂ) (_ : ‖β‖ = r ^ m) => (f ^ m).eigenspace β) (α ^ m)
        (by rw [norm_pow, hα]) le_rfl)
  set Q : Submodule ℂ V := ⨆ β ∈ {β : ℂ | ‖β‖ ≠ r ^ m}, (f ^ m).eigenspace β with hQ
  have hd : Disjoint (absSpace (f ^ m) (r ^ m)) Q :=
    (End.eigenspaces_iSupIndep (f ^ m)).disjoint_biSup_biSup
      (s := {β : ℂ | ‖β‖ = r ^ m}) (t := {β : ℂ | ‖β‖ ≠ r ^ m})
      (Set.disjoint_left.mpr fun _ h1 h2 => h2 h1)
  have ht : absSpace f r ⊔ Q = ⊤ := by
    rw [eq_top_iff, ← hf.iSup_eigenspace_eq_top]
    refine iSup_le fun α => ?_
    by_cases hα : ‖α‖ = r
    · exact le_sup_of_le_left
        (le_iSup₂_of_le (f := fun (β : ℂ) (_ : ‖β‖ = r) => f.eigenspace β) α hα le_rfl)
    · refine le_sup_of_le_right ((eigenspace_le_eigenspace_pow f α m).trans ?_)
      refine le_iSup₂_of_le (f := fun β (_ : β ∈ {β : ℂ | ‖β‖ ≠ r ^ m}) => (f ^ m).eigenspace β)
        (α ^ m) ?_ le_rfl
      intro h
      rw [norm_pow] at h
      exact hα ((pow_left_inj₀ (norm_nonneg α) hr hm.ne').mp h)
  calc absSpace (f ^ m) (r ^ m) = (absSpace f r ⊔ Q) ⊓ absSpace (f ^ m) (r ^ m) := by
        rw [ht, top_inf_eq]
    _ = absSpace f r := by rw [sup_inf_assoc_of_le _ hP, hd.symm.eq_bot, sup_bot_eq]

/- English proof (translation)
Introduce `E Ω _ _ _ _ _ A w h V _ _ _ a φ ψ hd r`. Break down `lt_or_ge r 0 with hr | hr` into its components or cases. Rewrite using `[absSpace_of_neg _ hr, absSpace_of_neg _ hr]`. Take `⟨m, hm, he⟩` from `GlobalTheory.T.exists_pow_eq_pow_of_weilDegree_eq_smooth E Ω A w h V a.ρ a.smooth φ ψ hd`. Rewrite using `[← absSpace_pow (a.semisimple φ) hm hr, ← absSpace_pow (a.semisimple ψ) hm hr, he]`.
-/
theorem absSpace_eq_of_deg_eq : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E))
    (h : IsPlaceOver A w) (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (a : WDRep h V) (φ ψ : Weil h), deg φ = deg ψ →
    ∀ r : ℝ, absSpace (a.ρ φ) r = absSpace (a.ρ ψ) r := by
  intro E Ω _ _ _ _ _ A w h V _ _ _ a φ ψ hd r
  rcases lt_or_ge r 0 with hr | hr
  · rw [absSpace_of_neg _ hr, absSpace_of_neg _ hr]
  · obtain ⟨m, hm, he⟩ := GlobalTheory.T.exists_pow_eq_pow_of_weilDegree_eq_smooth E Ω A w h V a.ρ a.smooth φ ψ hd
    rw [← absSpace_pow (a.semisimple φ) hm hr, ← absSpace_pow (a.semisimple ψ) hm hr, he]

end GlobalTheory.WeilDeligne
