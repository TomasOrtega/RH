import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.SecDerF

noncomputable section

open MeasureTheory Matrix Set Filter Topology

namespace PositivityTheory.Rg.Sw.AbsSt.SD

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt PositivityTheory.Rg.Sw.AbsSt.DF

variable {n : ℕ}

/- English proof (translation)
Unfold `Matrix.IsHermitian`. Rewrite using `[Matrix.conjTranspose_smul, hH.eq]`. Simplify using the standard rewrite rules.
-/
theorem herm_smul {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.IsHermitian) (σ : ℝ) : ((σ : ℂ) • H).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_smul, hH.eq]
  simp

/- English proof (translation)
Unfold `InG nU JJ`. Rewrite using `[Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]`. Simplify using `[hb.eq]`.
-/
theorem inG_nU {b : Matrix (Fin n) (Fin n) ℂ} (hb : b.IsHermitian) : InG (nU b) := by
  unfold InG nU JJ
  rw [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp [hb.eq]

def nGU (H : Matrix (Fin n) (Fin n) ℂ) (σ : ℝ) : GL (Fin n ⊕ Fin n) ℂ where
  val := nU ((σ : ℂ) • H)
  inv := nU (-((σ : ℂ) • H))
  val_inv := by rw [nU_mul_nU, add_neg_cancel, nU_zero]
  inv_val := by rw [nU_mul_nU, neg_add_cancel, nU_zero]

def nG {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.IsHermitian) (σ : ℝ) : GR n := ⟨nGU H σ, inG_nU (herm_smul hH σ)⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem mR_nG {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.IsHermitian) (σ : ℝ) : mR (nG hH σ) = nU ((σ : ℂ) • H) := rfl

/- English proof (translation)
Use `Continuous.subtype_mk ?_ _` and prove the remaining obligations. Rewrite using `[Units.continuous_iff]`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `show Continuous fun σ : ℝ => fromBlocks (1 : Matrix (Fin n) (Fin n) ℂ) ((σ : ℂ) • H) 0 1`. Conclude with `Continuous.matrix_fromBlocks continuous_const ((Complex.continuous_ofReal).smul continuous_const) continuous_const continuous_const`.

Use `show Continuous fun σ : ℝ => fromBlocks (1 : Matrix (Fin n) (Fin n) ℂ) (-((σ : ℂ) • H)) 0 1`. Conclude with `Continuous.matrix_fromBlocks continuous_const ((Complex.continuous_ofReal).smul continuous_const).neg continuous_const continuous_const`.
-/
theorem cont_nG {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.IsHermitian) : Continuous (nG hH) := by
  refine Continuous.subtype_mk ?_ _
  rw [Units.continuous_iff]
  refine ⟨?_, ?_⟩
  · show Continuous fun σ : ℝ => fromBlocks (1 : Matrix (Fin n) (Fin n) ℂ) ((σ : ℂ) • H) 0 1
    exact Continuous.matrix_fromBlocks continuous_const ((Complex.continuous_ofReal).smul continuous_const)
      continuous_const continuous_const
  · show Continuous fun σ : ℝ => fromBlocks (1 : Matrix (Fin n) (Fin n) ℂ) (-((σ : ℂ) • H)) 0 1
    exact Continuous.matrix_fromBlocks continuous_const ((Complex.continuous_ofReal).smul continuous_const).neg
      continuous_const continuous_const

/- English proof (translation)
Apply `DF.ext_mR` to reduce the goal to its premises. Rewrite using `[mR_nG, DF.mR_one]`. Simplify using `[DF.nU_zero]`.
-/
theorem nG_zero {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.IsHermitian) : nG hH 0 = 1 := by
  apply DF.ext_mR
  rw [mR_nG, DF.mR_one]
  simp [DF.nU_zero]

def eH (H : Matrix (Fin n) (Fin n) ℂ) (σ : ℝ) : Matrix (Fin n) (Fin n) ℂ := NormedSpace.exp ((σ : ℂ) • H)

/- English proof (translation)
Simplify using `[eH, neg_smul]`.
-/
theorem eH_neg (H : Matrix (Fin n) (Fin n) ℂ) (σ : ℝ) : eH H (-σ) = NormedSpace.exp (-((σ : ℂ) • H)) := by
  simp [eH, neg_smul]

/- English proof (translation)
Rewrite using `[eH_neg]`. Unfold `eH`. Rewrite using `[← Matrix.exp_add_of_commute _ _ (Commute.refl ((σ : ℂ) • H)).neg_right, add_neg_cancel]`. Simplify using the standard rewrite rules.
-/
theorem eH_mul_neg (H : Matrix (Fin n) (Fin n) ℂ) (σ : ℝ) : eH H σ * eH H (-σ) = 1 := by
  rw [eH_neg]
  unfold eH
  rw [← Matrix.exp_add_of_commute _ _ (Commute.refl ((σ : ℂ) • H)).neg_right, add_neg_cancel]
  simp

/- English proof (translation)
Rewrite using `[eH_neg]`. Unfold `eH`. Rewrite using `[← Matrix.exp_add_of_commute _ _ (Commute.refl ((σ : ℂ) • H)).neg_left, neg_add_cancel]`. Simplify using the standard rewrite rules.
-/
theorem eH_neg_mul (H : Matrix (Fin n) (Fin n) ℂ) (σ : ℝ) : eH H (-σ) * eH H σ = 1 := by
  rw [eH_neg]
  unfold eH
  rw [← Matrix.exp_add_of_commute _ _ (Commute.refl ((σ : ℂ) • H)).neg_left, neg_add_cancel]
  simp

/- English proof (translation)
Rewrite using `[eH, ← Matrix.exp_conjTranspose, (herm_smul hH σ).eq]`.
-/
theorem eH_herm {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.IsHermitian) (σ : ℝ) : (eH H σ)ᴴ = eH H σ := by
  rw [eH, ← Matrix.exp_conjTranspose, (herm_smul hH σ).eq]

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra in
/- English proof (translation)
The claim follows from `NormedSpace.exp_continuous.comp ((Complex.continuous_ofReal).smul continuous_const)`.
-/
theorem cont_eH (H : Matrix (Fin n) (Fin n) ℂ) : Continuous (eH H) :=
  NormedSpace.exp_continuous.comp ((Complex.continuous_ofReal).smul continuous_const)

def mGU (H : Matrix (Fin n) (Fin n) ℂ) (σ : ℝ) : GL (Fin n ⊕ Fin n) ℂ where
  val := fromBlocks (eH H σ) 0 0 (eH H (-σ))
  inv := fromBlocks (eH H (-σ)) 0 0 (eH H σ)
  val_inv := by rw [fromBlocks_multiply]; simp [eH_mul_neg, eH_neg_mul, fromBlocks_one]
  inv_val := by rw [fromBlocks_multiply]; simp [eH_mul_neg, eH_neg_mul, fromBlocks_one]

/- English proof (translation)
Unfold `InG JJ`. Rewrite using `[Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]`. Simplify using `[eH_herm hH, eH_mul_neg, eH_neg_mul]`.
-/
theorem inG_mGU {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.IsHermitian) (σ : ℝ) :
    InG (fromBlocks (eH H σ) 0 0 (eH H (-σ))) := by
  unfold InG JJ
  rw [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp [eH_herm hH, eH_mul_neg, eH_neg_mul]

def mG {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.IsHermitian) (σ : ℝ) : GR n := ⟨mGU H σ, inG_mGU hH σ⟩

/- English proof (translation)
Rewrite using `[← eH_neg]`. Both sides reduce to the same expression.
-/
theorem mR_mG {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.IsHermitian) (σ : ℝ) :
    mR (mG hH σ) = fromBlocks (NormedSpace.exp ((σ : ℂ) • H)) 0 0 (NormedSpace.exp (-((σ : ℂ) • H))) := by
  rw [← eH_neg]
  rfl

/- English proof (translation)
Apply `Continuous.subtype_mk` to reduce the goal to its premises. Rewrite using `[Units.continuous_iff]`. Establish `h1` using `cont_eH H`. Establish `h2 : Continuous fun σ : ℝ => eH H (-σ)` using `h1.comp continuous_neg`. Prove the components needed by the constructor for the conclusion.

Conclude with `Continuous.matrix_fromBlocks h1 continuous_const continuous_const h2`. Conclude with `Continuous.matrix_fromBlocks h2 continuous_const continuous_const h1`.
-/
theorem cont_mG {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.IsHermitian) : Continuous (mG hH) := by
  apply Continuous.subtype_mk
  rw [Units.continuous_iff]
  have h1 := cont_eH H
  have h2 : Continuous fun σ : ℝ => eH H (-σ) := h1.comp continuous_neg
  constructor
  · exact Continuous.matrix_fromBlocks h1 continuous_const continuous_const h2
  · exact Continuous.matrix_fromBlocks h2 continuous_const continuous_const h1

/- English proof (translation)
Apply `DF.ext_mR` to reduce the goal to its premises. Rewrite using `[mR_mG, DF.mR_one]`. Simplify using `[Matrix.fromBlocks_one]`.
-/
theorem mG_zero {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.IsHermitian) : mG hH 0 = 1 := by
  apply DF.ext_mR
  rw [mR_mG, DF.mR_one]
  simp [Matrix.fromBlocks_one]

/- English proof (translation)
Introduce `δ hδ`. Establish `hcontD : Continuous fun p : GR n × ℝ => D (p.1 * f p.2)` using `hD.comp (continuous_fst.mul (hf.comp continuous_snd))`. Establish `ftc : ∀ s : ℝ, ∀ g : GR n, S (g * f s) - S g = ∫ σ in (0:ℝ)..s, D (g * f σ)`. Introduce `s`. Establish `hcl : IsClosed {g : GR n | S (g * f s) - S g = ∫ σ in (0:ℝ)..s, D (g * f σ)}`.

Apply `isClosed_eq` to reduce the goal to its premises. Conclude with `(hS.comp (continuous_id.mul continuous_const)).sub hS`. Conclude with `intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (f := fun g σ => D (g * f σ)) hcontD 0 s`. Establish `hsub : {y : GR n | (mR y).toBlocks₂₁.det ≠ 0} ⊆ {g : GR n | S (g * f s) - S g = ∫ σ in (0:ℝ)..s, D (g * f σ)}`. Introduce `g hg`.

Establish `h` using `intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := s) (f := fun σ => S (g * f σ)) (f' := fun σ => D (g * f σ)) (fun x _ => hd g hg x) ((hD.comp (continuous_const.mul hf)).intervalIntegrable 0 s)`. Simplify using `only [hf0, mul_one] at h`. Conclude with `h.symm`. Introduce `g`. Establish `h` using `hcl.closure_subset_iff.mpr hsub`.

Rewrite `h` using `[DF.dense_cell.closure_eq]`. Conclude with `h (Set.mem_univ g)`. Establish `htube : ∀ᶠ σ in 𝓝 (0:ℝ), ∀ k ∈ (Set.univ : Set (KR n)), ‖D ((k : GR n) * y * f σ) - D ((k : GR n) * y)‖ < δ`. Apply `isCompact_univ.eventually_forall_of_forall_eventually` to reduce the goal to its premises. Introduce `k _`.

Establish `hc : Continuous fun p : ℝ × KR n => ‖D ((p.2 : GR n) * y * f p.1) - D ((p.2 : GR n) * y)‖` using `((hD.comp (((continuous_subtype_val.comp continuous_snd).mul continuous_const).mul (hf.comp continuous_fst))).sub (hD.comp ((continuous_subtype_val.comp continuous_snd).mul continuous_const))).norm`. Establish `h0 : ‖D ((k : GR n) * y * f 0) - D ((k : GR n) * y)‖ < δ` using `by simp [hf0, hδ]`. Conclude with `Filter.eventually_of_mem ((hc.isOpen_preimage _ isOpen_Iio).mem_nhds h0) (fun z hz => hz)`. Take `⟨η, hη, hball⟩` from `Metric.eventually_nhds_iff.mp htube`. Use `⟨η, hη, fun s hs hsη k => ?_⟩` and prove the remaining obligations.

Use `set g := (k : GR n) * y with hg`. Rewrite using `[ftc s g]`. Establish `hint : IntervalIntegrable (fun σ => D (g * f σ)) MeasureTheory.volume 0 s` using `(hD.comp (continuous_const.mul hf)).intervalIntegrable 0 s`. Establish `hs' : (s : ℂ) ≠ 0` using `by exact_mod_cast hs`. Establish `key : (∫ σ in (0:ℝ)..s, D (g * f σ)) / s - D g = (∫ σ in (0:ℝ)..s, (D (g * f σ) - D g)) / s`.

Rewrite using `[intervalIntegral.integral_sub hint intervalIntegrable_const, intervalIntegral.integral_const, sub_zero, Complex.real_smul, sub_div, mul_div_cancel_left₀ _ hs']`. Establish `hb : ‖∫ σ in (0:ℝ)..s, (D (g * f σ) - D g)‖ ≤ δ * |s - 0|`. Apply `intervalIntegral.norm_integral_le_of_norm_le_const` to reduce the goal to its premises. Introduce `x hx`. Establish `hx' : |x| ≤ |s|`.

Break down `Set.mem_uIoc.mp hx with ⟨h1, h2⟩ | ⟨h1, h2⟩` into its components or cases. Conclude with `abs_le_abs h2 (by linarith)`. Rewrite using `[abs_of_nonpos h2, abs_of_neg (by linarith)]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hx2 : dist x 0 < η`.

Rewrite using `[dist_zero_right, Real.norm_eq_abs]`. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `(hball hx2 k (Set.mem_univ _)).le`. Establish `hs0 : (0:ℝ) < ‖(s:ℂ)‖`. Rewrite using `[Complex.norm_real, Real.norm_eq_abs]`.

Conclude with `abs_pos.mpr hs`. Rewrite using `[key, norm_div, div_le_iff₀ hs0]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem unif_family (S D : GR n → ℂ) (hS : Continuous S) (hD : Continuous D) (f : ℝ → GR n) (hf : Continuous f)
    (hf0 : f 0 = 1)
    (hd : ∀ g : GR n, (mR g).toBlocks₂₁.det ≠ 0 → ∀ s : ℝ, HasDerivAt (fun σ : ℝ => S (g * f σ)) (D (g * f s)) s)
    (y : GR n) : ∀ δ : ℝ, 0 < δ → ∃ η : ℝ, 0 < η ∧ ∀ s : ℝ, s ≠ 0 → |s| < η → ∀ k : KR n,
      ‖(S ((k : GR n) * y * f s) - S ((k : GR n) * y)) / s - D ((k : GR n) * y)‖ ≤ δ := by
  intro δ hδ
  have hcontD : Continuous fun p : GR n × ℝ => D (p.1 * f p.2) :=
    hD.comp (continuous_fst.mul (hf.comp continuous_snd))
  have ftc : ∀ s : ℝ, ∀ g : GR n, S (g * f s) - S g = ∫ σ in (0:ℝ)..s, D (g * f σ) := by
    intro s
    have hcl : IsClosed {g : GR n | S (g * f s) - S g = ∫ σ in (0:ℝ)..s, D (g * f σ)} := by
      apply isClosed_eq
      · exact (hS.comp (continuous_id.mul continuous_const)).sub hS
      · exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
          (f := fun g σ => D (g * f σ)) hcontD 0 s
    have hsub : {y : GR n | (mR y).toBlocks₂₁.det ≠ 0} ⊆
        {g : GR n | S (g * f s) - S g = ∫ σ in (0:ℝ)..s, D (g * f σ)} := by
      intro g hg
      have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := s)
        (f := fun σ => S (g * f σ)) (f' := fun σ => D (g * f σ)) (fun x _ => hd g hg x)
        ((hD.comp (continuous_const.mul hf)).intervalIntegrable 0 s)
      simp only [hf0, mul_one] at h
      exact h.symm
    intro g
    have h := hcl.closure_subset_iff.mpr hsub
    rw [DF.dense_cell.closure_eq] at h
    exact h (Set.mem_univ g)
  have htube : ∀ᶠ σ in 𝓝 (0:ℝ), ∀ k ∈ (Set.univ : Set (KR n)),
      ‖D ((k : GR n) * y * f σ) - D ((k : GR n) * y)‖ < δ := by
    apply isCompact_univ.eventually_forall_of_forall_eventually
    intro k _
    have hc : Continuous fun p : ℝ × KR n => ‖D ((p.2 : GR n) * y * f p.1) - D ((p.2 : GR n) * y)‖ :=
      ((hD.comp (((continuous_subtype_val.comp continuous_snd).mul continuous_const).mul
        (hf.comp continuous_fst))).sub
        (hD.comp ((continuous_subtype_val.comp continuous_snd).mul continuous_const))).norm
    have h0 : ‖D ((k : GR n) * y * f 0) - D ((k : GR n) * y)‖ < δ := by simp [hf0, hδ]
    exact Filter.eventually_of_mem ((hc.isOpen_preimage _ isOpen_Iio).mem_nhds h0) (fun z hz => hz)
  obtain ⟨η, hη, hball⟩ := Metric.eventually_nhds_iff.mp htube
  refine ⟨η, hη, fun s hs hsη k => ?_⟩
  set g := (k : GR n) * y with hg
  rw [ftc s g]
  have hint : IntervalIntegrable (fun σ => D (g * f σ)) MeasureTheory.volume 0 s :=
    (hD.comp (continuous_const.mul hf)).intervalIntegrable 0 s
  have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hs
  have key : (∫ σ in (0:ℝ)..s, D (g * f σ)) / s - D g = (∫ σ in (0:ℝ)..s, (D (g * f σ) - D g)) / s := by
    rw [intervalIntegral.integral_sub hint intervalIntegrable_const, intervalIntegral.integral_const,
      sub_zero, Complex.real_smul, sub_div, mul_div_cancel_left₀ _ hs']
  have hb : ‖∫ σ in (0:ℝ)..s, (D (g * f σ) - D g)‖ ≤ δ * |s - 0| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro x hx
    have hx' : |x| ≤ |s| := by
      rcases Set.mem_uIoc.mp hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact abs_le_abs h2 (by linarith)
      · rw [abs_of_nonpos h2, abs_of_neg (by linarith)]
        linarith
    have hx2 : dist x 0 < η := by
      rw [dist_zero_right, Real.norm_eq_abs]
      linarith
    exact (hball hx2 k (Set.mem_univ _)).le
  have hs0 : (0:ℝ) < ‖(s:ℂ)‖ := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact abs_pos.mpr hs
  rw [key, norm_div, div_le_iff₀ hs0]
  calc _ ≤ δ * |s - 0| := hb
    _ = δ * ‖(s:ℂ)‖ := by rw [sub_zero, Complex.norm_real, Real.norm_eq_abs]

end PositivityTheory.Rg.Sw.AbsSt.SD

namespace PositivityTheory.Rg.Sw.AbsSt

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt.SD

/- English proof (translation)
Introduce `m n ε c t p q e sL ρ hL R _ y H hH`. Use `⟨⟨nG hH, unif_family (sL R) (sL (DN ε t H R)) (hL.cont R) (hL.cont _) (nG hH) (cont_nG hH) (nG_zero hH) (fun g hg s => hN m n ε c t p q e sL ρ hL R H hH (nG hH) (mR_nG hH) g hg s) y⟩, ⟨mG hH, unif_family (sL R) (sL (DM ε c H R)) (hL.cont R) (hL.cont _) (mG hH) (cont_mG hH) (mG_ze …` and prove the remaining obligations.
-/
theorem secDer_of (hN : NDer) (hM : MDer) : SecDer := by
  intro m n ε c t p q e sL ρ hL R _ y H hH
  refine ⟨⟨nG hH, unif_family (sL R) (sL (DN ε t H R)) (hL.cont R) (hL.cont _) (nG hH) (cont_nG hH) (nG_zero hH)
    (fun g hg s => hN m n ε c t p q e sL ρ hL R H hH (nG hH) (mR_nG hH) g hg s) y⟩,
    ⟨mG hH, unif_family (sL R) (sL (DM ε c H R)) (hL.cont R) (hL.cont _) (mG hH) (cont_mG hH) (mG_zero hH)
    (fun g hg s => hM m n ε c t p q e sL ρ hL R H hH (mG hH) (mR_mG hH) g hg s) y⟩⟩

end PositivityTheory.Rg.Sw.AbsSt
