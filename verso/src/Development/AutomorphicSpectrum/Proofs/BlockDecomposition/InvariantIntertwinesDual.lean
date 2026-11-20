import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.HighestVectorsRegularLine
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WtRInjective

noncomputable section

open Matrix Finset
open scoped InnerProductSpace

open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount GlobalTheory.CompanionTheory.RealCountG

namespace GlobalTheory.CompanionTheory.RealCountG.Intertw

variable {n : ℕ}

/- English proof (translation)
Rewrite using `[Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, ← Matrix.exp_conjTranspose]`. Establish `h : ((s : ℂ) • X)ᴴ = -((s : ℂ) • X)`. Rewrite using `[conjTranspose_smul, hX]`. Simplify using the standard rewrite rules. Establish `hc : Commute ((s : ℂ) • X) (-((s : ℂ) • X))` using `(Commute.refl _).neg_right`.

Rewrite using `[h, ← Matrix.exp_add_of_commute _ _ hc]`. Simplify using the standard rewrite rules.
-/
theorem exp_mem (X : Matrix (Fin n) (Fin n) ℂ) (hX : Xᴴ = -X) (s : ℝ) :
    NormedSpace.exp ((s : ℂ) • X) ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, ← Matrix.exp_conjTranspose]
  have h : ((s : ℂ) • X)ᴴ = -((s : ℂ) • X) := by
    rw [conjTranspose_smul, hX]
    simp
  have hc : Commute ((s : ℂ) • X) (-((s : ℂ) • X)) := (Commute.refl _).neg_right
  rw [h, ← Matrix.exp_add_of_commute _ _ hc]
  simp

/- English proof (translation)
Rewrite using `[Finset.sum_eq_single a, Finset.sum_eq_single b]`. Simplify using the standard rewrite rules. Introduce `y _ hy`. Rewrite using `[Matrix.single_apply, if_neg (fun hh => hy hh.2.symm), zero_smul]`. Simplify using the standard rewrite rules.

Introduce `x _ hx`. Use `Finset.sum_eq_zero fun y _ => ?_` and prove the remaining obligations. Rewrite using `[Matrix.single_apply, if_neg (fun hh => hx hh.1.symm), zero_smul]`. Simplify using the standard rewrite rules.
-/
theorem sum_single {V : Type} [AddCommGroup V] [Module ℂ V] (F : Fin n → Fin n → V) (a b : Fin n) (c : ℂ) :
    ∑ x, ∑ y, (Matrix.single a b c : Matrix (Fin n) (Fin n) ℂ) x y • F x y = c • F a b := by
  rw [Finset.sum_eq_single a, Finset.sum_eq_single b]
  · simp
  · intro y _ hy
    rw [Matrix.single_apply, if_neg (fun hh => hy hh.2.symm), zero_smul]
  · simp
  · intro x _ hx
    refine Finset.sum_eq_zero fun y _ => ?_
    rw [Matrix.single_apply, if_neg (fun hh => hx hh.1.symm), zero_smul]
  · simp

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [conjTranspose_apply, Matrix.single_apply]`. Distinguish the cases in `h : a = j ∧ b = i`. Rewrite using `[if_pos h, if_pos ⟨h.2, h.1⟩]`. Rewrite using `[if_neg h, if_neg (fun hh => h ⟨hh.2, hh.1⟩)]`.

Simplify using the standard rewrite rules.
-/
theorem single_conjT (a b : Fin n) (c : ℂ) :
    (Matrix.single a b c : Matrix (Fin n) (Fin n) ℂ)ᴴ = Matrix.single b a (star c) := by
  ext i j
  simp only [conjTranspose_apply, Matrix.single_apply]
  by_cases h : a = j ∧ b = i
  · rw [if_pos h, if_pos ⟨h.2, h.1⟩]
  · rw [if_neg h, if_neg (fun hh => h ⟨hh.2, hh.1⟩)]
    simp

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [Matrix.neg_apply, Matrix.single_apply]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem single_neg' (a b : Fin n) (c : ℂ) :
    (Matrix.single a b (-c) : Matrix (Fin n) (Fin n) ℂ) = -Matrix.single a b c := by
  ext i j
  simp only [Matrix.neg_apply, Matrix.single_apply]
  split_ifs <;> simp

/- English proof (translation)
Establish `h1 : (Matrix.single a b (1 : ℂ) - Matrix.single b a 1)ᴴ = -(Matrix.single a b (1 : ℂ) - Matrix.single b a 1)`. Rewrite using `[conjTranspose_sub, single_conjT, single_conjT, star_one, neg_sub]`. Establish `h2 : (Matrix.single a b Complex.I + Matrix.single b a Complex.I)ᴴ = -(Matrix.single a b Complex.I + Matrix.single b a Complex.I)`. Rewrite using `[conjTranspose_add, single_conjT, single_conjT, Complex.star_def, Complex.conj_I, single_neg', single_neg', neg_add, add_comm]`. Establish `m1` using `h _ h1`.

Establish `m2` using `h _ h2`. Simplify using `only [Matrix.sub_apply, Matrix.add_apply, sub_smul, add_smul, Finset.sum_sub_distrib, Finset.sum_add_distrib, sum_single, one_smul] at m1 m2`. Establish `m3 : F a b + F b a = 0`. Use `congrArg (fun v => (-Complex.I) • v) m2` as an intermediate fact. Simplify `this` using `[smul_add, smul_smul]`.

Establish `m4 : (2 : ℂ) • F a b = 0`. Rewrite using `[two_smul]`. Combine the equalities or inequalities in the displayed calculation. Conclude with `(smul_eq_zero.1 m4).resolve_left two_ne_zero`.
-/
theorem family_eq_zero {V : Type} [AddCommGroup V] [Module ℂ V] (F : Fin n → Fin n → V)
    (h : ∀ X : Matrix (Fin n) (Fin n) ℂ, Xᴴ = -X → ∑ a, ∑ b, X a b • F a b = 0) (a b : Fin n) : F a b = 0 := by
  have h1 : (Matrix.single a b (1 : ℂ) - Matrix.single b a 1)ᴴ = -(Matrix.single a b (1 : ℂ) - Matrix.single b a 1) := by
    rw [conjTranspose_sub, single_conjT, single_conjT, star_one, neg_sub]
  have h2 : (Matrix.single a b Complex.I + Matrix.single b a Complex.I)ᴴ =
      -(Matrix.single a b Complex.I + Matrix.single b a Complex.I) := by
    rw [conjTranspose_add, single_conjT, single_conjT, Complex.star_def, Complex.conj_I, single_neg', single_neg', neg_add,
      add_comm]
  have m1 := h _ h1
  have m2 := h _ h2
  simp only [Matrix.sub_apply, Matrix.add_apply, sub_smul, add_smul, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, sum_single, one_smul] at m1 m2
  have m3 : F a b + F b a = 0 := by
    have := congrArg (fun v => (-Complex.I) • v) m2
    simpa [smul_add, smul_smul] using this
  have m4 : (2 : ℂ) • F a b = 0 := by
    rw [two_smul]
    calc F a b + F a b = (F a b - F b a) + (F a b + F b a) := by abel
      _ = 0 := by rw [m1, m3, add_zero]
  exact (smul_eq_zero.1 m4).resolve_left two_ne_zero

/- English proof (translation)
Introduce `n V _ _ σ Kf hK E G hG t ht a b ξ`. Use `sub_eq_zero.1 (family_eq_zero (fun a b => t (G a b ξ) - Kf a b (t ξ)) (fun X hX => ?_) a b)` and prove the remaining obligations. Set `γ : ℝ → Matrix.unitaryGroup (Fin n) ℂ` to `fun s => ⟨NormedSpace.exp ((s : ℂ) • X), exp_mem X hX s⟩`. Establish `h1` using `hG.2 X γ hX (fun _ => rfl) ξ`. Take `⟨S, _, hS, _, _, hd⟩` from `hK.2 (t ξ)`.

Establish `h2` using `hd X γ (fun _ => rfl) (t ξ) hS`. Set `tL : (E.V →L[ℂ] ℂ) →L[ℂ] V` to `LinearMap.toContinuousLinearMap t`. Establish `h3 : HasDerivAt (fun s : ℝ => tL (ξ ∘L E.ρ (γ s)⁻¹)) (tL (∑ a, ∑ b, X a b • G a b ξ)) 0` using `(tL.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 h1`. Establish `h4 : (fun s : ℝ => tL (ξ ∘L E.ρ (γ s)⁻¹)) = fun s : ℝ => σ (γ s) (t ξ)`. Use function extensionality and compare the values at `s`.

Conclude with `ht (γ s) ξ`. Rewrite `h3` using `[h4]`. Establish `h5` using `h3.unique h2`. Establish `h6 : tL (∑ a, ∑ b, X a b • G a b ξ) = ∑ a, ∑ b, X a b • t (G a b ξ)`. Simplify using `only [map_sum, map_smul]`.

Both sides reduce to the same expression. Rewrite `h5` using `[h6]`. Simplify using `only [smul_sub, Finset.sum_sub_distrib, h5, sub_self]`.
-/
theorem intertwines : ∀ {n : ℕ} (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (σ : Matrix.unitaryGroup (Fin n) ℂ →* (V →ₗ[ℂ] V)) (Kf : Fin n → Fin n → Module.End ℂ V), IsDerivK σ Kf →
    ∀ (E : KMod n) (G : Fin n → Fin n → Module.End ℂ (E.V →L[ℂ] ℂ)), IsDualFam E G →
    ∀ t ∈ invA σ E, ∀ a b ξ, t (G a b ξ) = Kf a b (t ξ) := by
  intro n V _ _ σ Kf hK E G hG t ht a b ξ
  refine sub_eq_zero.1 (family_eq_zero (fun a b => t (G a b ξ) - Kf a b (t ξ)) (fun X hX => ?_) a b)
  let γ : ℝ → Matrix.unitaryGroup (Fin n) ℂ := fun s => ⟨NormedSpace.exp ((s : ℂ) • X), exp_mem X hX s⟩
  have h1 := hG.2 X γ hX (fun _ => rfl) ξ
  obtain ⟨S, _, hS, _, _, hd⟩ := hK.2 (t ξ)
  have h2 := hd X γ (fun _ => rfl) (t ξ) hS
  let tL : (E.V →L[ℂ] ℂ) →L[ℂ] V := LinearMap.toContinuousLinearMap t
  have h3 : HasDerivAt (fun s : ℝ => tL (ξ ∘L E.ρ (γ s)⁻¹)) (tL (∑ a, ∑ b, X a b • G a b ξ)) 0 :=
    (tL.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 h1
  have h4 : (fun s : ℝ => tL (ξ ∘L E.ρ (γ s)⁻¹)) = fun s : ℝ => σ (γ s) (t ξ) := by
    funext s
    exact ht (γ s) ξ
  rw [h4] at h3
  have h5 := h3.unique h2
  have h6 : tL (∑ a, ∑ b, X a b • G a b ξ) = ∑ a, ∑ b, X a b • t (G a b ξ) := by
    simp only [map_sum, map_smul]
    rfl
  rw [h6] at h5
  simp only [smul_sub, Finset.sum_sub_distrib, h5, sub_self]

end GlobalTheory.CompanionTheory.RealCountG.Intertw
