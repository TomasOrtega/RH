import Mathlib
import Formalism.PeriodIntegrals.UpqRep
import Formalism.PeriodIntegrals.IsLowUnitH
import Formalism.PeriodIntegrals.ZuckTensor
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ZuckermanTensor.DualDefs
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ZuckermanTensor.DualChoice

open Matrix Finset
open scoped InnerProductSpace
noncomputable section
namespace PI.ZuckTensorWork
open PI.UpqRep PI.ZuckTensor

section Mat
variable {n : ℕ}

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[revM, Fin.revPerm_apply]`.
-/
theorem revM_eq_submatrix (g : Matrix (Fin n) (Fin n) ℂ) :
    revM g = g.submatrix (Fin.revPerm : Fin n ≃ Fin n) (Fin.revPerm : Fin n ≃ Fin n) := by
  ext i j; simp [revM, Fin.revPerm_apply]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[revM]`.
-/
theorem revM_revM (g : Matrix (Fin n) (Fin n) ℂ) : revM (revM g) = g := by
  ext i j; simp [revM]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `congrArg revM h` as an intermediate fact. Rewrite `this` using `[revM_revM, revM_revM]`. Then use the resulting hypothesis. Introduce `h`.

Rewrite using `[h]`.
-/
theorem revM_inj {a b : Matrix (Fin n) (Fin n) ℂ} : revM a = revM b ↔ a = b := by
  constructor
  · intro h
    have := congrArg revM h
    rwa [revM_revM, revM_revM] at this
  · intro h; rw [h]

/- English proof (translation)
Rewrite using `[revM_eq_submatrix, revM_eq_submatrix, revM_eq_submatrix, Matrix.submatrix_mul_equiv]`.
-/
theorem revM_mul (a b : Matrix (Fin n) (Fin n) ℂ) : revM (a * b) = revM a * revM b := by
  rw [revM_eq_submatrix, revM_eq_submatrix, revM_eq_submatrix, Matrix.submatrix_mul_equiv]

/- English proof (translation)
Rewrite using `[revM_eq_submatrix, Matrix.submatrix_one_equiv]`.
-/
theorem revM_one : revM (1 : Matrix (Fin n) (Fin n) ℂ) = 1 := by
  rw [revM_eq_submatrix, Matrix.submatrix_one_equiv]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Rewrite using `[← revM_revM a, h, revM_one]`. Introduce `h`. Rewrite using `[h, revM_one]`.
-/
theorem revM_eq_one_iff {a : Matrix (Fin n) (Fin n) ℂ} : revM a = 1 ↔ a = 1 := by
  constructor
  · intro h; rw [← revM_revM a, h, revM_one]
  · intro h; rw [h, revM_one]

/- English proof (translation)
Unfold `revM`. Rewrite using `[Matrix.conjTranspose_submatrix]`.
-/
theorem revM_conjTranspose (g : Matrix (Fin n) (Fin n) ℂ) : (revM g)ᴴ = revM gᴴ := by
  unfold revM; rw [Matrix.conjTranspose_submatrix]

/- English proof (translation)
Rewrite using `[revM_eq_submatrix, Matrix.submatrix_diagonal_equiv]`. Use `congr 1`.
-/
theorem revM_diagonal (d : Fin n → ℂ) : revM (diagonal d) = diagonal (d ∘ Fin.rev) := by
  rw [revM_eq_submatrix, Matrix.submatrix_diagonal_equiv]
  congr 1

/- English proof (translation)
Unfold `Jm`. Rewrite using `[revM_diagonal]`. Both sides reduce to the same expression.
-/
theorem revM_Jm (ε : Fin n → Bool) : revM (Jm ε) = Jm (revE ε) := by
  unfold Jm; rw [revM_diagonal]; rfl

/- English proof (translation)
Rewrite using `[revM_Jm, revE_revE]`.
-/
theorem Jm_eq_revM (ε : Fin n → Bool) : Jm ε = revM (Jm (revE ε)) := by
  rw [revM_Jm, revE_revE]

/- English proof (translation)
The claim follows from `continuous_id.matrix_submatrix _ _`.
-/
theorem continuous_revM : Continuous (revM : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ) :=
  continuous_id.matrix_submatrix _ _

/- English proof (translation)
Use `show inUJ ε (revM g) ↔ inUJ (revE ε) g`. Unfold `inUJ`. Rewrite using `[Jm_eq_revM ε, revM_conjTranspose, ← revM_mul, ← revM_mul, revM_inj]`.
-/
theorem revM_mem_UJset_iff {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} :
    revM g ∈ UJset ε ↔ g ∈ UJset (revE ε) := by
  show inUJ ε (revM g) ↔ inUJ (revE ε) g
  unfold inUJ
  rw [Jm_eq_revM ε, revM_conjTranspose, ← revM_mul, ← revM_mul, revM_inj]

/- English proof (translation)
The claim follows from `revM_mem_UJset_iff.mpr h`.
-/
theorem revM_mem_UJset {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (h : g ∈ UJset (revE ε)) :
    revM g ∈ UJset ε := revM_mem_UJset_iff.mpr h

/- English proof (translation)
The claim follows from `revM_mem_UJset_iff.mpr (by rwa [revE_revE])`.
-/
theorem revM_mem_UJset' {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (h : g ∈ UJset ε) :
    revM g ∈ UJset (revE ε) := revM_mem_UJset_iff.mpr (by rwa [revE_revE])

/- English proof (translation)
Use `show (revM g ∈ unitaryGroup (Fin n) ℂ ∧ revM g * Jm ε = Jm ε * revM g) ↔ (g ∈ unitaryGroup (Fin n) ℂ ∧ g * Jm (revE ε) = Jm (revE ε) * g)`. Rewrite using `[Matrix.mem_unitaryGroup_iff, Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.star_eq_conjTranspose, revM_conjTranspose, ← revM_mul, revM_eq_one_iff, Jm_eq_revM ε, ← revM_mul, ← revM_mul, revM_inj]`.
-/
theorem revM_mem_Kset_iff {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} :
    revM g ∈ Kset ε ↔ g ∈ Kset (revE ε) := by
  show (revM g ∈ unitaryGroup (Fin n) ℂ ∧ revM g * Jm ε = Jm ε * revM g) ↔
    (g ∈ unitaryGroup (Fin n) ℂ ∧ g * Jm (revE ε) = Jm (revE ε) * g)
  rw [Matrix.mem_unitaryGroup_iff, Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
    Matrix.star_eq_conjTranspose, revM_conjTranspose, ← revM_mul, revM_eq_one_iff, Jm_eq_revM ε,
    ← revM_mul, ← revM_mul, revM_inj]

/- English proof (translation)
The claim follows from `revM_mem_Kset_iff.mpr h`.
-/
theorem revM_mem_Kset {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (h : g ∈ Kset (revE ε)) :
    revM g ∈ Kset ε := revM_mem_Kset_iff.mpr h

/- English proof (translation)
The claim follows from `revM_mem_Kset_iff.mpr (by rwa [revE_revE])`.
-/
theorem revM_mem_Kset' {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (h : g ∈ Kset ε) :
    revM g ∈ Kset (revE ε) := revM_mem_Kset_iff.mpr (by rwa [revE_revE])

end Mat

section Conj
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/- English proof (translation)
Use `show c • x = (starRingEnd ℂ) ((starRingEnd ℂ) c) • x`. Rewrite using `[Complex.conj_conj]`.
-/
theorem Cj.mk_smul (c : ℂ) (x : H) : Cj.mk (c • x) = (starRingEnd ℂ) c • Cj.mk x := by
  show c • x = (starRingEnd ℂ) ((starRingEnd ℂ) c) • x
  rw [Complex.conj_conj]

/- English proof (translation)
The claim follows from `continuous_id`.
-/
theorem Cj.continuous_mk : Continuous (Cj.mk : H → Cj H) := continuous_id

/- English proof (translation)
The claim follows from `ContinuousLinearMap.ext fun _ => rfl`.
-/
theorem cjOp_one : cjOp (1 : H →L[ℂ] H) = 1 := ContinuousLinearMap.ext fun _ => rfl

/- English proof (translation)
The claim follows from `ContinuousLinearMap.ext fun _ => rfl`.
-/
theorem cjOp_comp (S T : H →L[ℂ] H) : cjOp (S.comp T) = (cjOp S).comp (cjOp T) :=
  ContinuousLinearMap.ext fun _ => rfl

variable {n : ℕ}

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem sigC_mk (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (g : Matrix (Fin n) (Fin n) ℂ) (x : H) :
    sigC σ g (Cj.mk x) = Cj.mk (σ (revM g) x) := rfl

/- English proof (translation)
Rewrite using `[sigC_mk, revM_revM]`.
-/
theorem sigC_revM_mk (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (g : Matrix (Fin n) (Fin n) ℂ) (x : H) :
    sigC σ (revM g) (Cj.mk x) = Cj.mk (σ g x) := by
  rw [sigC_mk, revM_revM]

/- English proof (translation)
Use extensionality with `x`. Conclude with `Iff.rfl`.
-/
theorem cjSub_cjSubInv (S : Submodule ℂ (Cj H)) : cjSub (cjSubInv S) = S := by
  ext x; exact Iff.rfl

/- English proof (translation)
Use extensionality with `x`. Conclude with `Iff.rfl`.
-/
theorem cjSubInv_cjSub (S : Submodule ℂ H) : cjSubInv (cjSub S) = S := by
  ext x; exact Iff.rfl

/- English proof (translation)
Use extensionality with `x`. Use `show Cj.un x ∈ (⊥ : Submodule ℂ H) ↔ x ∈ (⊥ : Submodule ℂ (Cj H))`. Rewrite using `[Submodule.mem_bot, Submodule.mem_bot]`. Conclude with `Iff.rfl`.
-/
theorem cjSub_bot : cjSub (⊥ : Submodule ℂ H) = ⊥ := by
  ext x
  show Cj.un x ∈ (⊥ : Submodule ℂ H) ↔ x ∈ (⊥ : Submodule ℂ (Cj H))
  rw [Submodule.mem_bot, Submodule.mem_bot]; exact Iff.rfl

/- English proof (translation)
Rewrite using `[← cjSub_bot, cjSubInv_cjSub]`.
-/
theorem cjSubInv_bot : cjSubInv (⊥ : Submodule ℂ (Cj H)) = ⊥ := by
  rw [← cjSub_bot, cjSubInv_cjSub]

/- English proof (translation)
Use extensionality with `x`. Use `show Cj.un x ∈ (⊤ : Submodule ℂ H) ↔ x ∈ (⊤ : Submodule ℂ (Cj H))`. Conclude with `iff_of_true Submodule.mem_top Submodule.mem_top`.
-/
theorem cjSub_top : cjSub (⊤ : Submodule ℂ H) = ⊤ := by
  ext x
  show Cj.un x ∈ (⊤ : Submodule ℂ H) ↔ x ∈ (⊤ : Submodule ℂ (Cj H))
  exact iff_of_true Submodule.mem_top Submodule.mem_top

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun h _ hx => h hx, fun h _ hx => h hx⟩`.
-/
theorem cjSub_le_iff {S T : Submodule ℂ H} : cjSub S ≤ cjSub T ↔ S ≤ T :=
  ⟨fun h _ hx => h hx, fun h _ hx => h hx⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun h _ hx => h hx, fun h _ hx => h hx⟩`.
-/
theorem cjSubInv_le_iff {S T : Submodule ℂ (Cj H)} : cjSubInv S ≤ cjSubInv T ↔ S ≤ T :=
  ⟨fun h _ hx => h hx, fun h _ hx => h hx⟩

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Introduce `x hx`. Establish `key : ∀ y ∈ Submodule.span ℂ s, Cj.mk y ∈ Submodule.span ℂ (Cj.mk '' s)`. Introduce `y hy`. Proceed by induction on `hy using Submodule.span_induction with`.

Consider the case `mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩`. Consider the case `zero => exact Submodule.zero_mem _`. Consider the case `add _ _ _ _ ha hb => exact Submodule.add_mem _ ha hb`. Consider the case `smul c a _ ha => rw [Cj.mk_smul]`. Conclude with `Submodule.smul_mem _ _ ha`.

Conclude with `key (Cj.un x) hx`. Rewrite using `[Submodule.span_le]`. Introduce `z hz`. Take `⟨y, hy, rfl⟩` from `hz`. Use `show y ∈ Submodule.span ℂ s`.

Conclude with `Submodule.subset_span hy`.
-/
theorem cjSub_span (s : Set H) : cjSub (Submodule.span ℂ s) = Submodule.span ℂ (Cj.mk '' s) := by
  apply le_antisymm
  · intro x hx
    have key : ∀ y ∈ Submodule.span ℂ s, Cj.mk y ∈ Submodule.span ℂ (Cj.mk '' s) := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
      | zero => exact Submodule.zero_mem _
      | add _ _ _ _ ha hb => exact Submodule.add_mem _ ha hb
      | smul c a _ ha => rw [Cj.mk_smul]; exact Submodule.smul_mem _ _ ha
    exact key (Cj.un x) hx
  · rw [Submodule.span_le]
    intro z hz
    obtain ⟨y, hy, rfl⟩ := hz
    show y ∈ Submodule.span ℂ s
    exact Submodule.subset_span hy

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Introduce `x hx`. Establish `key : ∀ y ∈ Submodule.span ℂ s, Cj.un y ∈ Submodule.span ℂ (Cj.un '' s)`. Introduce `y hy`. Proceed by induction on `hy using Submodule.span_induction with`.

Consider the case `mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩`. Consider the case `zero => exact Submodule.zero_mem _`. Consider the case `add _ _ _ _ ha hb => exact Submodule.add_mem _ ha hb`. Consider the case `smul c a _ ha => rw [Cj.un_smul]`. Conclude with `Submodule.smul_mem _ _ ha`.

Conclude with `key (Cj.mk x) hx`. Rewrite using `[Submodule.span_le]`. Introduce `z hz`. Take `⟨y, hy, rfl⟩` from `hz`. Use `show y ∈ Submodule.span ℂ s`.

Conclude with `Submodule.subset_span hy`.
-/
theorem cjSubInv_span (s : Set (Cj H)) :
    cjSubInv (Submodule.span ℂ s) = Submodule.span ℂ (Cj.un '' s) := by
  apply le_antisymm
  · intro x hx
    have key : ∀ y ∈ Submodule.span ℂ s, Cj.un y ∈ Submodule.span ℂ (Cj.un '' s) := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
      | zero => exact Submodule.zero_mem _
      | add _ _ _ _ ha hb => exact Submodule.add_mem _ ha hb
      | smul c a _ ha => rw [Cj.un_smul]; exact Submodule.smul_mem _ _ ha
    exact key (Cj.mk x) hx
  · rw [Submodule.span_le]
    intro z hz
    obtain ⟨y, hy, rfl⟩ := hz
    show y ∈ Submodule.span ℂ s
    exact Submodule.subset_span hy

/- English proof (translation)
Take `⟨T, hT⟩` from `(Submodule.fg_iff_finiteDimensional S).mpr inferInstance`. Apply `(Submodule.fg_iff_finiteDimensional _).mp` to reduce the goal to its premises. Use `⟨T.image Cj.mk, ?_⟩` and prove the remaining obligations. Rewrite using `[Finset.coe_image, ← cjSub_span, hT]`.
-/
theorem cjSub_finiteDimensional (S : Submodule ℂ H) [FiniteDimensional ℂ S] :
    FiniteDimensional ℂ (cjSub S) := by
  classical
  obtain ⟨T, hT⟩ := (Submodule.fg_iff_finiteDimensional S).mpr inferInstance
  apply (Submodule.fg_iff_finiteDimensional _).mp
  refine ⟨T.image Cj.mk, ?_⟩
  rw [Finset.coe_image, ← cjSub_span, hT]

/- English proof (translation)
Take `⟨T, hT⟩` from `(Submodule.fg_iff_finiteDimensional S).mpr inferInstance`. Apply `(Submodule.fg_iff_finiteDimensional _).mp` to reduce the goal to its premises. Use `⟨T.image Cj.un, ?_⟩` and prove the remaining obligations. Rewrite using `[Finset.coe_image, ← cjSubInv_span, hT]`.
-/
theorem cjSubInv_finiteDimensional (S : Submodule ℂ (Cj H)) [FiniteDimensional ℂ S] :
    FiniteDimensional ℂ (cjSubInv S) := by
  classical
  obtain ⟨T, hT⟩ := (Submodule.fg_iff_finiteDimensional S).mpr inferInstance
  apply (Submodule.fg_iff_finiteDimensional _).mp
  refine ⟨T.image Cj.un, ?_⟩
  rw [Finset.coe_image, ← cjSubInv_span, hT]

end Conj

section Wt
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {n : ℕ} {ε : Fin n → Bool}

/- English proof (translation)
Rewrite using `[← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]`. Use `push_cast`. Put the polynomial expressions in normal form.
-/
private theorem conjRep_conj_expI (r : ℝ) :
    (starRingEnd ℂ) (Complex.exp ((r : ℂ) * Complex.I)) = Complex.exp (((-r : ℝ) : ℂ) * Complex.I) := by
  rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast; ring_nf

/- English proof (translation)
Rewrite using `[← Finset.sum_neg_distrib, ← Equiv.sum_comp (Fin.revPerm : Fin n ≃ Fin n) (fun a => -(μ a * θ (Fin.rev a)))]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Simplify using `[revP, Fin.revPerm_apply]`.
-/
private theorem conjRep_sum_revP (μ θ : Fin n → ℝ) :
    ∑ a, revP μ a * θ a = -(∑ a, μ a * θ (Fin.rev a)) := by
  rw [← Finset.sum_neg_distrib,
    ← Equiv.sum_comp (Fin.revPerm : Fin n ≃ Fin n) (fun a => -(μ a * θ (Fin.rev a)))]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp [revP, Fin.revPerm_apply]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h θ hθ`. Establish `hD : revM (diagonal fun a => Complex.exp ((θ a : ℂ) * Complex.I)) = diagonal fun a => Complex.exp (((θ ∘ Fin.rev) a : ℂ) * Complex.I)`. Rewrite using `[revM_diagonal]`. Both sides reduce to the same expression.

Establish `hK` using `revM_mem_Kset hθ`. Rewrite `hK` using `[hD]`. Establish `h1` using `h (θ ∘ Fin.rev) hK`. Rewrite using `[sigC_mk, hD, h1, Cj.mk_smul, conjRep_conj_expI, conjRep_sum_revP]`. Both sides reduce to the same expression.

Introduce `h θ hθ`. Establish `hD : revM (diagonal fun a => Complex.exp (((θ ∘ Fin.rev) a : ℂ) * Complex.I)) = diagonal fun a => Complex.exp ((θ a : ℂ) * Complex.I)`. Rewrite using `[revM_diagonal]`. Use `congr 1`. Use function extensionality and compare the values at `a`.

Simplify using `[Fin.rev_rev]`. Establish `hK : (diagonal fun a => Complex.exp (((θ ∘ Fin.rev) a : ℂ) * Complex.I)) ∈ Kset (revE ε)`. Rewrite using `[← revM_mem_Kset_iff, hD]`. Conclude with `hθ`. Establish `h1` using `h (θ ∘ Fin.rev) hK`.

Rewrite `h1` using `[sigC_mk, hD]`. Establish `h2` using `congrArg Cj.un h1`. Rewrite `h2` using `[Cj.un_smul, Cj.un_mk, Cj.un_mk]`. Rewrite using `[h2, conjRep_conj_expI, conjRep_sum_revP]`. Establish `e : -(-(∑ a, μ a * (θ ∘ Fin.rev) (Fin.rev a))) = ∑ a, μ a * θ a` using `by simp [Fin.rev_rev]`.

Rewrite using `[e]`.
-/
theorem isWtOn_sigC_iff (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (μ : Fin n → ℝ) (v : H) :
    IsWtOn (Kset ε) σ μ v ↔ IsWtOn (Kset (revE ε)) (sigC σ) (revP μ) (Cj.mk v) := by
  constructor
  · intro h θ hθ
    have hD : revM (diagonal fun a => Complex.exp ((θ a : ℂ) * Complex.I)) =
        diagonal fun a => Complex.exp (((θ ∘ Fin.rev) a : ℂ) * Complex.I) := by
      rw [revM_diagonal]; rfl
    have hK := revM_mem_Kset hθ
    rw [hD] at hK
    have h1 := h (θ ∘ Fin.rev) hK
    rw [sigC_mk, hD, h1, Cj.mk_smul, conjRep_conj_expI, conjRep_sum_revP]
    rfl
  · intro h θ hθ
    have hD : revM (diagonal fun a => Complex.exp (((θ ∘ Fin.rev) a : ℂ) * Complex.I)) =
        diagonal fun a => Complex.exp ((θ a : ℂ) * Complex.I) := by
      rw [revM_diagonal]; congr 1; funext a; simp [Fin.rev_rev]
    have hK : (diagonal fun a => Complex.exp (((θ ∘ Fin.rev) a : ℂ) * Complex.I)) ∈ Kset (revE ε) := by
      rw [← revM_mem_Kset_iff, hD]; exact hθ
    have h1 := h (θ ∘ Fin.rev) hK
    rw [sigC_mk, hD] at h1
    have h2 := congrArg Cj.un h1
    rw [Cj.un_smul, Cj.un_mk, Cj.un_mk] at h2
    rw [h2, conjRep_conj_expI, conjRep_sum_revP]
    have e : -(-(∑ a, μ a * (θ ∘ Fin.rev) (Fin.rev a))) = ∑ a, μ a * θ a := by simp [Fin.rev_rev]
    rw [e]

/- English proof (translation)
Rewrite using `[isWtOn_sigC_iff (ε := ε) σ (revP μ) (Cj.un x), dualWeight_dualWeight]`. Conclude with `Iff.rfl`.
-/
theorem isWtOn_sigC_iff' (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (μ : Fin n → ℝ) (x : Cj H) :
    IsWtOn (Kset (revE ε)) (sigC σ) μ x ↔ IsWtOn (Kset ε) σ (revP μ) (Cj.un x) := by
  rw [isWtOn_sigC_iff (ε := ε) σ (revP μ) (Cj.un x), dualWeight_dualWeight]
  exact Iff.rfl

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h g hg x hx`. Conclude with `h (revM g) (revM_mem_Kset hg) (Cj.un x) hx`. Introduce `h g hg x hx`. Use `h (revM g) (revM_mem_Kset' hg) (Cj.mk x) hx` as an intermediate fact.

Rewrite `this` using `[sigC_revM_mk]`. Conclude with `this`.
-/
theorem kStable_cjSubInv_iff (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (S : Submodule ℂ (Cj H)) :
    IsKStableOn ε σ (cjSubInv S) ↔ IsKStableOn (revE ε) (sigC σ) S := by
  constructor
  · intro h g hg x hx
    exact h (revM g) (revM_mem_Kset hg) (Cj.un x) hx
  · intro h g hg x hx
    have := h (revM g) (revM_mem_Kset' hg) (Cj.mk x) hx
    rw [sigC_revM_mk] at this
    exact this

/- English proof (translation)
Rewrite using `[← kStable_cjSubInv_iff, cjSubInv_cjSub]`.
-/
theorem kStable_cjSub_iff (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (S : Submodule ℂ H) :
    IsKStableOn ε σ S ↔ IsKStableOn (revE ε) (sigC σ) (cjSub S) := by
  rw [← kStable_cjSubInv_iff, cjSubInv_cjSub]

end Wt

/- English proof (translation)
Introduce `n ε H _ _ σ ⟨⟨h1, hmul⟩, hiso, hcont⟩`. Use `⟨⟨?_, ?_⟩, ?_, ?_⟩` and prove the remaining obligations. Use `show cjOp (σ (revM 1)) = 1`. Rewrite using `[revM_one, h1, cjOp_one]`. Introduce `a ha b hb show cjOp (σ (revM (a * b))) = (cjOp (σ (revM a))).comp (cjOp (σ (revM b)))`.

Rewrite using `[revM_mul, hmul _ (revM_mem_UJset ha) _ (revM_mem_UJset hb), cjOp_comp]`. Introduce `g hg v`. Conclude with `hiso _ (revM_mem_UJset hg) (Cj.un v)`. Introduce `v`. Establish `hc : ContinuousOn (fun g => σ (revM g) (Cj.un v)) (UJset (revE ε))` using `(hcont (Cj.un v)).comp continuous_revM.continuousOn (fun g hg => revM_mem_UJset hg)`.

Conclude with `Cj.continuous_mk.comp_continuousOn hc`.
-/
theorem unitary_representation_holds : URepConj := by
  intro n ε H _ _ σ ⟨⟨h1, hmul⟩, hiso, hcont⟩
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · show cjOp (σ (revM 1)) = 1
    rw [revM_one, h1, cjOp_one]
  · intro a ha b hb
    show cjOp (σ (revM (a * b))) = (cjOp (σ (revM a))).comp (cjOp (σ (revM b)))
    rw [revM_mul, hmul _ (revM_mem_UJset ha) _ (revM_mem_UJset hb), cjOp_comp]
  · intro g hg v
    exact hiso _ (revM_mem_UJset hg) (Cj.un v)
  · intro v
    have hc : ContinuousOn (fun g => σ (revM g) (Cj.un v)) (UJset (revE ε)) :=
      (hcont (Cj.un v)).comp continuous_revM.continuousOn (fun g hg => revM_mem_UJset hg)
    exact Cj.continuous_mk.comp_continuousOn hc

/- English proof (translation)
Introduce `n ε H _ _ σ hirr S hS hstab`. Establish `hS' : IsClosed (cjSubInv S : Set H)` using `hS`. Establish `hstab' : ∀ g ∈ UJset ε, ∀ v ∈ cjSubInv S, σ g v ∈ cjSubInv S`. Introduce `g hg v hv`. Use `hstab (revM g) (revM_mem_UJset' hg) (Cj.mk v) hv` as an intermediate fact.

Rewrite `this` using `[sigC_revM_mk]`. Conclude with `this`. Break down `hirr _ hS' hstab' with h0 | h0` into its components or cases. Use `left`. Rewrite using `[← cjSub_cjSubInv S, h0, cjSub_bot]`.

Use `right`. Rewrite using `[← cjSub_cjSubInv S, h0, cjSub_top]`.
-/
theorem irreducible_conjecture_holds : IrredConj := by
  intro n ε H _ _ σ hirr S hS hstab
  have hS' : IsClosed (cjSubInv S : Set H) := hS
  have hstab' : ∀ g ∈ UJset ε, ∀ v ∈ cjSubInv S, σ g v ∈ cjSubInv S := by
    intro g hg v hv
    have := hstab (revM g) (revM_mem_UJset' hg) (Cj.mk v) hv
    rw [sigC_revM_mk] at this
    exact this
  rcases hirr _ hS' hstab' with h0 | h0
  · left; rw [← cjSub_cjSubInv S, h0, cjSub_bot]
  · right; rw [← cjSub_cjSubInv S, h0, cjSub_top]

/- English proof (translation)
Introduce `n ε H _ _ σ Λ S ⟨hfd, hst, hirr, ⟨v, hvS, hv0, hvw⟩, hdom⟩`. Use `⟨(haveI := hfd; cjSub_finiteDimensional S), (kStable_cjSub_iff σ S).mp hst, ?_, ⟨Cj.mk v, hvS, hv0, (isWtOn_sigC_iff σ Λ v).mp hvw⟩, ?_⟩` and prove the remaining obligations. Introduce `S' hle hst'`. Establish `hle' : cjSubInv S' ≤ S`. Rewrite using `[← cjSubInv_cjSub S]`.

Conclude with `cjSubInv_le_iff.mpr hle`. Break down `hirr _ hle' ((kStable_cjSubInv_iff σ S').mpr hst') with h0 | h0` into its components or cases. Use `left`. Rewrite using `[← cjSub_cjSubInv S', h0, cjSub_bot]`. Use `right`.

Rewrite using `[← cjSub_cjSubInv S', h0]`. Introduce `μ x hx hx0 hxw`. Establish `h1` using `hdom (revP μ) (Cj.un x) hx hx0 ((isWtOn_sigC_iff' σ μ x).mp hxw)`. Establish `h2` using `h n ε (revP μ) Λ h1`. Rewrite `h2` using `[dualWeight_dualWeight]`. Then use the resulting hypothesis.
-/
theorem kTypeConj_of (h : CDomRev) : KTypeConj := by
  intro n ε H _ _ σ Λ S ⟨hfd, hst, hirr, ⟨v, hvS, hv0, hvw⟩, hdom⟩
  refine ⟨(haveI := hfd; cjSub_finiteDimensional S), (kStable_cjSub_iff σ S).mp hst, ?_,
    ⟨Cj.mk v, hvS, hv0, (isWtOn_sigC_iff σ Λ v).mp hvw⟩, ?_⟩
  · intro S' hle hst'
    have hle' : cjSubInv S' ≤ S := by
      rw [← cjSubInv_cjSub S]; exact cjSubInv_le_iff.mpr hle
    rcases hirr _ hle' ((kStable_cjSubInv_iff σ S').mpr hst') with h0 | h0
    · left; rw [← cjSub_cjSubInv S', h0, cjSub_bot]
    · right; rw [← cjSub_cjSubInv S', h0]
  · intro μ x hx hx0 hxw
    have h1 := hdom (revP μ) (Cj.un x) hx hx0 ((isWtOn_sigC_iff' σ μ x).mp hxw)
    have h2 := h n ε (revP μ) Λ h1
    rwa [dualWeight_dualWeight] at h2

/- English proof (translation)
Introduce `n ε H _ _ σ Λ S ⟨hfd, hst, hirr, ⟨x, hxS, hx0, hxw⟩, hdom⟩`. Use `⟨(haveI := hfd; cjSubInv_finiteDimensional S), (kStable_cjSubInv_iff σ S).mpr hst, ?_, ⟨Cj.un x, hxS, hx0, (isWtOn_sigC_iff' σ Λ x).mp hxw⟩, ?_⟩` and prove the remaining obligations. Introduce `S' hle hst'`. Establish `hle' : cjSub S' ≤ S`. Rewrite using `[← cjSub_cjSubInv S]`.

Conclude with `cjSub_le_iff.mpr hle`. Break down `hirr _ hle' ((kStable_cjSub_iff σ S').mp hst') with h0 | h0` into its components or cases. Use `left`. Rewrite using `[← cjSubInv_cjSub S', h0, cjSubInv_bot]`. Use `right`.

Rewrite using `[← cjSubInv_cjSub S', h0]`. Introduce `μ v hv hv0 hvw`. Establish `h1` using `hdom (revP μ) (Cj.mk v) hv hv0 ((isWtOn_sigC_iff σ μ v).mp hvw)`. Establish `h2` using `h n (revE ε) (revP μ) Λ h1`. Rewrite `h2` using `[dualWeight_dualWeight, revE_revE]`. Then use the resulting hypothesis.
-/
theorem kTypeConjInv_of (h : CDomRev) : KTypeConjInv := by
  intro n ε H _ _ σ Λ S ⟨hfd, hst, hirr, ⟨x, hxS, hx0, hxw⟩, hdom⟩
  refine ⟨(haveI := hfd; cjSubInv_finiteDimensional S), (kStable_cjSubInv_iff σ S).mpr hst, ?_,
    ⟨Cj.un x, hxS, hx0, (isWtOn_sigC_iff' σ Λ x).mp hxw⟩, ?_⟩
  · intro S' hle hst'
    have hle' : cjSub S' ≤ S := by
      rw [← cjSub_cjSubInv S]; exact cjSub_le_iff.mpr hle
    rcases hirr _ hle' ((kStable_cjSub_iff σ S').mp hst') with h0 | h0
    · left; rw [← cjSubInv_cjSub S', h0, cjSubInv_bot]
    · right; rw [← cjSubInv_cjSub S', h0]
  · intro μ v hv hv0 hvw
    have h1 := hdom (revP μ) (Cj.mk v) hv hv0 ((isWtOn_sigC_iff σ μ v).mp hvw)
    have h2 := h n (revE ε) (revP μ) Λ h1
    rwa [dualWeight_dualWeight, revE_revE] at h2

end PI.ZuckTensorWork
end
