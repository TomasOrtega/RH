import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.SchurOrthogonalityWhittaker
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.ToMKMulInv

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap.Base.SchurOrthogonalityLemmas

open ReciprocityTheory.ChartRestriction.DS Formalism.QuantumDeterminants

variable {k r : ℕ}

/- English proof (translation)
Establish `hJ : κᴴ * Jm ε * κ = Jm ε` using `HW.torep_inUJ ε hκ`. Unfold `inUJ`. Rewrite using `[Matrix.conjTranspose_mul]`. Establish `e : gᴴ * κᴴ * Jm ε * (κ * g) = gᴴ * (κᴴ * Jm ε * κ) * g` using `by simp only [Matrix.mul_assoc]`. Rewrite using `[e, hJ]`.
-/
theorem inUJ_kmul {ε : Fin (2 * r + k + 1) → Bool} {κ g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hκ : κ ∈ Kset ε) : inUJ ε (κ * g) ↔ inUJ ε g := by
  have hJ : κᴴ * Jm ε * κ = Jm ε := HW.torep_inUJ ε hκ
  unfold inUJ
  rw [Matrix.conjTranspose_mul]
  have e : gᴴ * κᴴ * Jm ε * (κ * g) = gᴴ * (κᴴ * Jm ε * κ) * g := by simp only [Matrix.mul_assoc]
  rw [e, hJ]

/- English proof (translation)
Unfold `S7.PsiM`. Rewrite using `[dif_neg]`. Introduce and unpack `⟨k', X, hX, rfl⟩`. Conclude with `hg (S7.inUJ_kexp k' hX)`.
-/
theorem psiM_zero {ε : Fin (2 * r + k + 1) → Bool} {Λ : Fin (2 * r + k + 1) → ℝ} (T : S7.KType ε Λ)
    (μ : Fin (2 * r + k + 1) → ℤ) {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hg : ¬ inUJ ε g) :
    S7.PsiM T μ g = 0 := by
  unfold S7.PsiM
  rw [dif_neg]
  rintro ⟨k', X, hX, rfl⟩
  exact hg (S7.inUJ_kexp k' hX)

/- English proof (translation)
Distinguish the cases in `hg : inUJ ε g`. Establish `h` using `S7.psiM_equiv T μ (HW.torepK ε hκ) 1 hg`. Rewrite `h` using `[HW.toMK_torepK]`. Establish `h1 : S7.toMK (1 : S7.KG ε) = 1` using `rfl`. Rewrite `h` using `[h1, Matrix.mul_one]`.

Rewrite using `[h, HW.torepSig_of_mem T hκ]`. Establish `: T.op 1 = 1` using `by simp [S7.KType.op]`. Rewrite using `[this, mul_one]`. Rewrite using `[psiM_zero T μ hg, psiM_zero T μ (fun h => hg ((inUJ_kmul hκ).1 h)), mul_zero]`.
-/
theorem psiM_K {ε : Fin (2 * r + k + 1) → Bool} {Λ : Fin (2 * r + k + 1) → ℝ} (T : S7.KType ε Λ)
    (μ : Fin (2 * r + k + 1) → ℤ) {κ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hκ : κ ∈ Kset ε)
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    S7.PsiM T μ (κ * g) = HW.torepSig T κ * S7.PsiM T μ g := by
  by_cases hg : inUJ ε g
  · have h := S7.psiM_equiv T μ (HW.torepK ε hκ) 1 hg
    rw [HW.toMK_torepK] at h
    have h1 : S7.toMK (1 : S7.KG ε) = 1 := rfl
    rw [h1, Matrix.mul_one] at h
    rw [h, HW.torepSig_of_mem T hκ]
    have : T.op 1 = 1 := by simp [S7.KType.op]
    rw [this, mul_one]
  · rw [psiM_zero T μ hg, psiM_zero T μ (fun h => hg ((inUJ_kmul hκ).1 h)), mul_zero]

/- English proof (translation)
Unfold `Formalism.MainNotions.S.psiGen`. Establish `h : ∀ a : Fin r, Continuous (fun g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ => Formalism.MainNotions.S.ellA k r z g a)`. Introduce `a`. Unfold `Formalism.MainNotions.S.ellA`. Use `split_ifs`.

Conclude with `(continuous_apply _).comp (continuous_apply _)`. Simplify using `only [Matrix.mulVec, dotProduct]`. Conclude with `continuous_finsetSum _ fun j _ => (continuous_id.matrix_elem _ j).mul continuous_const`. Use `Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp (Complex.continuous_re.comp (continuous_finsetSum _ fun a _ => continuous_const.mul (h a)))))` and prove the remaining obligations.
-/
theorem psiGen_cont (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) : Continuous (Formalism.MainNotions.S.psiGen k r z c) := by
  unfold Formalism.MainNotions.S.psiGen
  have h : ∀ a : Fin r, Continuous (fun g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ =>
      Formalism.MainNotions.S.ellA k r z g a) := by
    intro a
    unfold Formalism.MainNotions.S.ellA
    split_ifs
    · exact (continuous_apply _).comp (continuous_apply _)
    · simp only [Matrix.mulVec, dotProduct]
      exact continuous_finsetSum _ fun j _ =>
        (continuous_id.matrix_elem _ j).mul continuous_const
  refine Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp
    (Complex.continuous_re.comp (continuous_finsetSum _ fun a _ => continuous_const.mul (h a)))))

/- English proof (translation)
Unfold `Formalism.MainNotions.S.psiGen`. Rewrite using `[mul_comm]`. Conclude with `Complex.norm_exp_ofReal_mul_I _`.
-/
theorem norm_psiGen (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    ‖Formalism.MainNotions.S.psiGen k r z c g‖ = 1 := by
  unfold Formalism.MainNotions.S.psiGen
  rw [mul_comm]
  exact Complex.norm_exp_ofReal_mul_I _

/- English proof (translation)
Use `set s : Set (Mt k r) := {M | inUJ ε (Matrix.of M)}`. Establish `hc : Continuous (fun x : Mt k r => (Matrix.of x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ))` using `continuous_id`. Establish `hs : IsClosed s` using `isClosed_eq ((hc.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul hc) continuous_const`. Establish `hΦ : ContinuousOn (fun M : Mt k r => ⟪w, S7.PsiM T μ (Matrix.of M) v⟫_ℂ) s`. Establish `h1 : ContinuousOn (fun M : Mt k r => S7.PsiM T μ (Matrix.of M)) s` using `hcont.comp hc.continuousOn (fun M hM => hM)`.

Conclude with `continuousOn_const.inner (h1.clm_apply continuousOn_const)`. Establish `he : (fun M : Mt k r => ⟪w, S7.PsiM T μ (Matrix.of M) v⟫_ℂ) = s.piecewise (fun M : Mt k r => ⟪w, S7.PsiM T μ (Matrix.of M) v⟫_ℂ) (fun _ => 0)`. Use function extensionality and compare the values at `M`. Distinguish the cases in `hM : M ∈ s`. Rewrite using `[Set.piecewise_eq_of_mem _ _ _ hM]`.

Rewrite using `[Set.piecewise_eq_of_notMem _ _ _ hM, psiM_zero T μ hM]`. Simplify using the standard rewrite rules. Rewrite using `[he]`. Conclude with `hΦ.measurable_piecewise continuousOn_const hs.measurableSet`.
-/
theorem coef_meas {ε : Fin (2 * r + k + 1) → Bool} {Λ : Fin (2 * r + k + 1) → ℝ} (T : S7.KType ε Λ)
    (μ : Fin (2 * r + k + 1) → ℤ) (hcont : ContinuousOn (S7.PsiM T μ) (UJset ε)) (v w : T.V) :
    Measurable (fun M : Mt k r => ⟪w, S7.PsiM T μ (Matrix.of M) v⟫_ℂ) := by
  classical
  set s : Set (Mt k r) := {M | inUJ ε (Matrix.of M)}
  have hc : Continuous (fun x : Mt k r => (Matrix.of x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)) :=
    continuous_id
  have hs : IsClosed s :=
    isClosed_eq ((hc.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul hc) continuous_const
  have hΦ : ContinuousOn (fun M : Mt k r => ⟪w, S7.PsiM T μ (Matrix.of M) v⟫_ℂ) s := by
    have h1 : ContinuousOn (fun M : Mt k r => S7.PsiM T μ (Matrix.of M)) s :=
      hcont.comp hc.continuousOn (fun M hM => hM)
    exact continuousOn_const.inner (h1.clm_apply continuousOn_const)
  have he : (fun M : Mt k r => ⟪w, S7.PsiM T μ (Matrix.of M) v⟫_ℂ) =
      s.piecewise (fun M : Mt k r => ⟪w, S7.PsiM T μ (Matrix.of M) v⟫_ℂ) (fun _ => 0) := by
    funext M
    by_cases hM : M ∈ s
    · rw [Set.piecewise_eq_of_mem _ _ _ hM]
    · rw [Set.piecewise_eq_of_notMem _ _ _ hM, psiM_zero T μ hM]; simp
  rw [he]
  exact hΦ.measurable_piecewise continuousOn_const hs.measurableSet

end ReciprocityTheory.ChartRestriction.DS.Lap.Base.SchurOrthogonalityLemmas
