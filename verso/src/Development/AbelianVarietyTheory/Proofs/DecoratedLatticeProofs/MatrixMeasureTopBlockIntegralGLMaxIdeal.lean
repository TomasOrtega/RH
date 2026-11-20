import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlockVolumeProd
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatrixEntrywiseProductMeasureUniformizerPowerBox
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChainStepIdentities
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ValTwoBlockParahoricInfTorusConjBlockwise

open MeasureTheory Matrix Formalism.IndefR.Datum
open scoped NNReal ENNReal

noncomputable section

namespace GlobalTheory.RectBlockVolume

section Gen
variable {k : Type} [MeasurableSpace k] (ν : Measure k) [SigmaFinite ν]

def rectEquiv (A D B C : Type) [Fintype A] [Fintype D] [Fintype B] [Fintype C] :
    Matrix (A ⊕ D) (B ⊕ C) k ≃ᵐ ((Matrix A B k × Matrix A C k) × (Matrix D B k × Matrix D C k)) :=
  (MeasurableEquiv.sumPiEquivProdPi (fun _ : A ⊕ D => (B ⊕ C) → k)).trans
    (MeasurableEquiv.prodCongr (GlobalTheory.BlockVolume.colSplit A B C) (GlobalTheory.BlockVolume.colSplit D B C))

/- English proof (translation)
Establish `h1` using `measurePreserving_sumPiEquivProdPi (fun _ : A ⊕ D => Measure.pi fun _ : B ⊕ C => ν)`. Establish `h2` using `(GlobalTheory.BlockVolume.colSplit_mp ν A B C).prod (GlobalTheory.BlockVolume.colSplit_mp ν D B C)`. Conclude with `h2.comp h1`.
-/
theorem rectEquiv_mp (A D B C : Type) [Fintype A] [Fintype D] [Fintype B] [Fintype C] :
    MeasurePreserving (rectEquiv (k := k) A D B C) (GlobalTheory.SplitWeil.volM ν (A ⊕ D) (B ⊕ C))
      (((GlobalTheory.SplitWeil.volM ν A B).prod (GlobalTheory.SplitWeil.volM ν A C)).prod
        ((GlobalTheory.SplitWeil.volM ν D B).prod (GlobalTheory.SplitWeil.volM ν D C))) := by
  have h1 := measurePreserving_sumPiEquivProdPi (fun _ : A ⊕ D => Measure.pi fun _ : B ⊕ C => ν)
  have h2 := (GlobalTheory.BlockVolume.colSplit_mp ν A B C).prod (GlobalTheory.BlockVolume.colSplit_mp ν D B C)
  exact h2.comp h1

/- English proof (translation)
Use `haveI hσ : ∀ (m n : Type) [Fintype m] [Fintype n], SigmaFinite (GlobalTheory.SplitWeil.volM ν m n) := fun m n _ _ => by`. Conclude with `(inferInstance : SigmaFinite (Measure.pi fun _ : m => Measure.pi fun _ : n => ν : Measure (m → n → k)))`. Use `haveI := hσ A B`. Use `haveI := hσ A C`. Use `haveI := hσ D B`.

Use `haveI := hσ D C`. Establish `hset : {x : Matrix (A ⊕ D) (B ⊕ C) k | x.toBlocks₁₁ ∈ S₁₁ ∧ x.toBlocks₁₂ ∈ S₁₂ ∧ x.toBlocks₂₁ ∈ S₂₁ ∧ x.toBlocks₂₂ ∈ S₂₂} = rectEquiv (k` using `k) A D B C ⁻¹' ((S₁₁ ×ˢ S₁₂) ×ˢ (S₂₁ ×ˢ S₂₂)) := by`. Use extensionality with `x`. Conclude with `⟨fun ⟨h1, h2, h3, h4⟩ => ⟨⟨h1, h2⟩, h3, h4⟩, fun ⟨⟨h1, h2⟩, h3, h4⟩ => ⟨h1, h2, h3, h4⟩⟩`. Rewrite using `[hset]`.

Use `((rectEquiv_mp ν A D B C).measure_preimage_equiv ((S₁₁ ×ˢ S₁₂) ×ˢ (S₂₁ ×ˢ S₂₂))).trans ?_` and prove the remaining obligations. Rewrite using `[Measure.prod_prod, Measure.prod_prod, Measure.prod_prod]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem volM_rect_blocks (A D B C : Type) [Fintype A] [Fintype D] [Fintype B] [Fintype C]
    (S₁₁ : Set (Matrix A B k)) (S₁₂ : Set (Matrix A C k)) (S₂₁ : Set (Matrix D B k)) (S₂₂ : Set (Matrix D C k)) :
    GlobalTheory.SplitWeil.volM ν (A ⊕ D) (B ⊕ C)
                 {x | x.toBlocks₁₁ ∈ S₁₁ ∧ x.toBlocks₁₂ ∈ S₁₂ ∧ x.toBlocks₂₁ ∈ S₂₁ ∧ x.toBlocks₂₂ ∈ S₂₂} =
      GlobalTheory.SplitWeil.volM ν A B S₁₁ * GlobalTheory.SplitWeil.volM ν A C S₁₂ * GlobalTheory.SplitWeil.volM ν D B S₂₁ *
        GlobalTheory.SplitWeil.volM ν D C S₂₂ := by
  haveI hσ : ∀ (m n : Type) [Fintype m] [Fintype n], SigmaFinite (GlobalTheory.SplitWeil.volM ν m n) := fun m n _ _ => by
    exact (inferInstance : SigmaFinite (Measure.pi fun _ : m => Measure.pi fun _ : n => ν :
      Measure (m → n → k)))
  haveI := hσ A B; haveI := hσ A C; haveI := hσ D B; haveI := hσ D C
  have hset : {x : Matrix (A ⊕ D) (B ⊕ C) k | x.toBlocks₁₁ ∈ S₁₁ ∧ x.toBlocks₁₂ ∈ S₁₂ ∧
      x.toBlocks₂₁ ∈ S₂₁ ∧ x.toBlocks₂₂ ∈ S₂₂} =
      rectEquiv (k := k) A D B C ⁻¹' ((S₁₁ ×ˢ S₁₂) ×ˢ (S₂₁ ×ˢ S₂₂)) := by
    ext x
    exact ⟨fun ⟨h1, h2, h3, h4⟩ => ⟨⟨h1, h2⟩, h3, h4⟩, fun ⟨⟨h1, h2⟩, h3, h4⟩ => ⟨h1, h2, h3, h4⟩⟩
  rw [hset]
  refine ((rectEquiv_mp ν A D B C).measure_preimage_equiv ((S₁₁ ×ˢ S₁₂) ×ˢ (S₂₁ ×ˢ S₂₂))).trans ?_
  rw [Measure.prod_prod, Measure.prod_prod, Measure.prod_prod]
  ring

def reidx (r a' b' : ℕ) : Matrix (Fin r ⊕ Fin b') (Fin r ⊕ Fin a') k ≃ᵐ Matrix (Fin (r + b')) (Fin (r + a')) k :=
  (MeasurableEquiv.piCongrRight fun _ => MeasurableEquiv.piCongrLeft (fun _ => k) finSumFinEquiv).trans
    (MeasurableEquiv.piCongrLeft (fun _ => Fin (r + a') → k) finSumFinEquiv)

/- English proof (translation)
Use `show Equiv.piCongrLeft (fun _ => Fin (r + a') → k) finSumFinEquiv (fun i => Equiv.piCongrLeft (fun _ => k) finSumFinEquiv (y i)) (finSumFinEquiv i) (finSumFinEquiv j) = y i j`. Rewrite using `[Equiv.piCongrLeft_apply_apply, Equiv.piCongrLeft_apply_apply]`.
-/
theorem reidx_apply (r a' b' : ℕ) (y : Matrix (Fin r ⊕ Fin b') (Fin r ⊕ Fin a') k) (i : Fin r ⊕ Fin b')
    (j : Fin r ⊕ Fin a') : reidx r a' b' y (finSumFinEquiv i) (finSumFinEquiv j) = y i j := by
  show Equiv.piCongrLeft (fun _ => Fin (r + a') → k) finSumFinEquiv
    (fun i => Equiv.piCongrLeft (fun _ => k) finSumFinEquiv (y i)) (finSumFinEquiv i) (finSumFinEquiv j) = y i j
  rw [Equiv.piCongrLeft_apply_apply, Equiv.piCongrLeft_apply_apply]

/- English proof (translation)
Establish `h1` using `measurePreserving_pi (fun _ : Fin r ⊕ Fin b' => Measure.pi fun _ : Fin r ⊕ Fin a' => ν) (fun _ => Measure.pi fun _ : Fin (r + a') => ν) (fun _ => measurePreserving_piCongrLeft (fun _ : Fin (r + a') => ν) finSumFinEquiv)`. Establish `h2` using `measurePreserving_piCongrLeft (fun _ : Fin (r + b') => Measure.pi fun _ : Fin (r + a') => ν) finSumFinEquiv`. Conclude with `h2.comp h1`.
-/
theorem reidx_mp (r a' b' : ℕ) :
    MeasurePreserving (reidx (k := k) r a' b') (GlobalTheory.SplitWeil.volM ν (Fin r ⊕ Fin b') (Fin r ⊕ Fin a'))
      (GlobalTheory.SplitWeil.volM ν (Fin (r + b')) (Fin (r + a'))) := by
  have h1 := measurePreserving_pi (fun _ : Fin r ⊕ Fin b' => Measure.pi fun _ : Fin r ⊕ Fin a' => ν)
    (fun _ => Measure.pi fun _ : Fin (r + a') => ν)
    (fun _ => measurePreserving_piCongrLeft (fun _ : Fin (r + a') => ν) finSumFinEquiv)
  have h2 := measurePreserving_piCongrLeft (fun _ : Fin (r + b') => Measure.pi fun _ : Fin (r + a') => ν)
    finSumFinEquiv
  exact h2.comp h1

end Gen

section Loc
open ValuativeRel

/- English proof (translation)
Use `haveI : SigmaFinite ((c : ℝ≥0∞) • μ) := by`. Establish `e : (c : ℝ≥0∞) • μ = c • μ`. Use extensionality with `s _`. Simplify using `[Measure.smul_apply]`. Rewrite using `[e]`.

Use `infer_instance`. Use `Measure.pi_eq fun s hs => ?_` and prove the remaining obligations. Simplify using `[Measure.smul_apply, Measure.pi_pi, Finset.prod_mul_distrib, smul_eq_mul]`.
-/
theorem pi_smul_const (ι : Type) [Fintype ι] {X : Type} [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ]
    (c : ℝ≥0) :
    Measure.pi (fun _ : ι => (c : ℝ≥0∞) • μ) = ((c : ℝ≥0∞) ^ Fintype.card ι) • Measure.pi (fun _ : ι => μ) := by
  haveI : SigmaFinite ((c : ℝ≥0∞) • μ) := by
    have e : (c : ℝ≥0∞) • μ = c • μ := by
      ext s _
      simp [Measure.smul_apply]
    rw [e]
    infer_instance
  refine Measure.pi_eq fun s hs => ?_
  simp [Measure.smul_apply, Measure.pi_pi, Finset.prod_mul_distrib, smul_eq_mul]

variable {k : Type} [MeasurableSpace k]

/- English proof (translation)
Unfold `GlobalTheory.SplitWeil.volM`. Rewrite using `[pi_smul_const n ν c]`. Establish `e : ((c : ℝ≥0∞) ^ Fintype.card n) = ((c ^ Fintype.card n : ℝ≥0) : ℝ≥0∞)` using `by push_cast; rfl`. Rewrite using `[e, pi_smul_const m _ (c ^ Fintype.card n)]`. Use `push_cast`.

Rewrite using `[← pow_mul]`. Both sides reduce to the same expression.
-/
theorem volM_smul (ν : Measure k) [SigmaFinite ν] (c : ℝ≥0) (m n : Type) [Fintype m] [Fintype n] :
    GlobalTheory.SplitWeil.volM ((c : ℝ≥0∞) • ν) m n =
      ((c : ℝ≥0∞) ^ (Fintype.card n * Fintype.card m)) • GlobalTheory.SplitWeil.volM ν m n := by
  unfold GlobalTheory.SplitWeil.volM
  rw [pi_smul_const n ν c]
  have e : ((c : ℝ≥0∞) ^ Fintype.card n) = ((c ^ Fintype.card n : ℝ≥0) : ℝ≥0∞) := by push_cast; rfl
  rw [e, pi_smul_const m _ (c ^ Fintype.card n)]
  push_cast
  rw [← pow_mul]
  rfl

variable [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [BorelSpace k]

/- English proof (translation)
Use `haveI := GlobalTheory.SplitWeil.secondCountable k`. Use `haveI : SigmaFinite ν := inferInstance`. Establish `h0 : ν (𝒪[k] : Set k) ≠ 0` using `(GlobalTheory.SplitWeil.isOpen_int k).measure_ne_zero ν ⟨0, zero_mem _⟩`. Establish `htop : ν (𝒪[k] : Set k) ≠ ∞` using `(GlobalTheory.SplitWeil.isCompact_int k).measure_lt_top.ne`. Use `set c : ℝ≥0 := (ν (𝒪[k] : Set k)).toNNReal with hcdef`.

Establish `hcc : (c : ℝ≥0∞) = ν (𝒪[k] : Set k)` using `ENNReal.coe_toNNReal htop`. Establish `hc0 : (c : ℝ≥0∞) ≠ 0` using `by rw [hcc]; exact h0`. Use `set ν₁ : Measure k := (c : ℝ≥0∞)⁻¹ • ν with hν₁def`. Use `haveI hH : ν₁.IsAddHaarMeasure := Measure.IsAddHaarMeasure.smul ν (ENNReal.inv_ne_zero.2 ENNReal.coe_ne_top) (ENNReal.inv_ne_top.2 hc0)`. Establish `hν₁ : GlobalTheory.SplitWeil.IsUnitVol ν₁` using `⟨hH, by`.

Rewrite using `[hν₁def, Measure.smul_apply, smul_eq_mul, ← hcc, ENNReal.inv_mul_cancel hc0 ENNReal.coe_ne_top]⟩`. Establish `hνeq : ν = (c : ℝ≥0∞) • ν₁`. Rewrite using `[hν₁def, smul_smul, ENNReal.mul_inv_cancel hc0 ENNReal.coe_ne_top, one_smul]`. Use `haveI : SigmaFinite ν₁ := inferInstance`. Establish `hV : GlobalTheory.SplitWeil.volM ν (Fin r) (Fin r) = ((c : ℝ≥0∞) ^ (r * r)) • GlobalTheory.SplitWeil.volM ν₁ (Fin r) (Fin r)` using `by conv_lhs => rw [hνeq]`.

Rewrite using `[volM_smul, Fintype.card_fin]`. Establish `h1` using `GlobalTheory.ChainStepIdentities.volAdd_eq k ν₁ hν₁ r`. Unfold `GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection.volAdd at h1`. Rewrite using `[hV, Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul, ← Measure.real, h1, ENNReal.toReal_pow, ← hcc, ENNReal.coe_toReal]`. Use `congr 1`.

Establish `hIcc : Finset.Icc 1 r = Finset.Ioc 0 r` using `by ext; simp; omega`. Rewrite using `[hIcc]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `[GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection.zetaAt]`.
-/
theorem volKO_real (ν : Measure k) [ν.IsAddHaarMeasure] (r : ℕ) :
    (GlobalTheory.SplitWeil.volM ν (Fin r) (Fin r) (Units.val '' (GlobalTheory.SplitWeil.KO k (Fin r) : Set (GL (Fin r) k)))).toReal =
      (ν (𝒪[k] : Set k)).toReal ^ (r * r) *
        ∏ n ∈ Finset.Ioc 0 r, (1 - ((GlobalTheory.SplitWeil.resCard k : ℝ) ^ n)⁻¹) := by
  haveI := GlobalTheory.SplitWeil.secondCountable k
  haveI : SigmaFinite ν := inferInstance
  have h0 : ν (𝒪[k] : Set k) ≠ 0 := (GlobalTheory.SplitWeil.isOpen_int k).measure_ne_zero ν ⟨0, zero_mem _⟩
  have htop : ν (𝒪[k] : Set k) ≠ ∞ := (GlobalTheory.SplitWeil.isCompact_int k).measure_lt_top.ne
  set c : ℝ≥0 := (ν (𝒪[k] : Set k)).toNNReal with hcdef
  have hcc : (c : ℝ≥0∞) = ν (𝒪[k] : Set k) := ENNReal.coe_toNNReal htop
  have hc0 : (c : ℝ≥0∞) ≠ 0 := by rw [hcc]; exact h0
  set ν₁ : Measure k := (c : ℝ≥0∞)⁻¹ • ν with hν₁def
  haveI hH : ν₁.IsAddHaarMeasure :=
    Measure.IsAddHaarMeasure.smul ν (ENNReal.inv_ne_zero.2 ENNReal.coe_ne_top) (ENNReal.inv_ne_top.2 hc0)
  have hν₁ : GlobalTheory.SplitWeil.IsUnitVol ν₁ := ⟨hH, by
    rw [hν₁def, Measure.smul_apply, smul_eq_mul, ← hcc, ENNReal.inv_mul_cancel hc0 ENNReal.coe_ne_top]⟩
  have hνeq : ν = (c : ℝ≥0∞) • ν₁ := by
    rw [hν₁def, smul_smul, ENNReal.mul_inv_cancel hc0 ENNReal.coe_ne_top, one_smul]
  haveI : SigmaFinite ν₁ := inferInstance
  have hV : GlobalTheory.SplitWeil.volM ν (Fin r) (Fin r) = ((c : ℝ≥0∞) ^ (r * r)) • GlobalTheory.SplitWeil.volM ν₁ (Fin r) (Fin r) := by
    conv_lhs => rw [hνeq]
    rw [volM_smul, Fintype.card_fin]
  have h1 := GlobalTheory.ChainStepIdentities.volAdd_eq k ν₁ hν₁ r
  unfold GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection.volAdd at h1
  rw [hV, Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul, ← Measure.real, h1, ENNReal.toReal_pow, ← hcc,
    ENNReal.coe_toReal]
  congr 1
  have hIcc : Finset.Icc 1 r = Finset.Ioc 0 r := by ext; simp; omega
  rw [hIcc]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp [GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection.zetaAt]

end Loc
end GlobalTheory.RectBlockVolume

open ValuativeRel in

/- English proof (translation)
Introduce `k _ _ _ _ _ _ ν hν a b r hra hrb`. Use `haveI := hν`. Use `haveI := GlobalTheory.SplitWeil.secondCountable k`. Use `haveI : SigmaFinite ν := inferInstance`. Take `⟨a', rfl⟩` from `Nat.exists_eq_add_of_le hra`.

Take `⟨b', rfl⟩` from `Nat.exists_eq_add_of_le hrb`. Choose the witnesses or unpack the hypotheses as in `⟨ϖ, hϖ⟩ : ∃ ϖ : kˣ, valuation k (ϖ : k) = uniformizer k := by`. Take `⟨x, hx⟩` from `valuation_surjective (uniformizer k)`. Use `⟨Units.mk0 x fun h => ?_, hx⟩` and prove the remaining obligations. Substitute `h` using the available equality.

Rewrite `hx` using `[map_zero]`. Conclude with `(show uniformizer k ≠ 0 by simp) hx.symm`. Establish `hset : GlobalTheory.RectBlockVolume.reidx r a' b' ⁻¹' {x : Matrix (Fin (r + b')) (Fin (r + a')) k | topL r x ∈ Units.val '' (GlobalTheory.SplitWeil.KO k (Fin r) : Set (GL (Fin r) k)) ∧ (∀ i j, valuation k (x i j) ≤ 1) ∧ ∀ i j, r ≤ i.val → j.val < r → valuation k (x i j) < 1} = {y …`. Use extensionality with `y`. Simplify using `only [Set.mem_preimage, Set.mem_setOf_eq]`.

Establish `htop : topL r (GlobalTheory.RectBlockVolume.reidx r a' b' y) = y.toBlocks₁₁`. Use extensionality with `i j`. Simplify using `only [topL]`. Rewrite using `[dif_pos ⟨by omega, by omega⟩]`. Establish `e1 : (⟨i.val, by omega⟩ : Fin (r + b')) = finSumFinEquiv (Sum.inl i)` using `Fin.ext (by simp)`.

Establish `e2 : (⟨j.val, by omega⟩ : Fin (r + a')) = finSumFinEquiv (Sum.inl j)` using `Fin.ext (by simp)`. Rewrite using `[e1, e2, GlobalTheory.RectBlockVolume.reidx_apply]`. Both sides reduce to the same expression. Rewrite using `[htop]`. Establish `hall : ∀ P : Fin (r + b') → Fin (r + a') → Prop, (∀ i j, P i j) ↔ ∀ i j, P (finSumFinEquiv i) (finSumFinEquiv j)` using `fun P => ⟨fun h i j => h _ _, fun h i j => by simpa using h (finSumFinEquiv.symm i) (finSumFinEquiv.symm j)⟩`.

Rewrite using `[hall (fun i j => valuation k (GlobalTheory.RectBlockVolume.reidx r a' b' y i j) ≤ 1), hall (fun i j => r ≤ i.val → j.val < r → valuation k (GlobalTheory.RectBlockVolume.reidx r a' b' y i j) < 1)]`. Establish `n1 : ∀ i : Fin r, ¬ r ≤ i.val` using `fun i => not_le.mpr i.2`. Establish `n2 : ∀ j : Fin a', ¬ (r + j.val < r)` using `fun j => by omega`. Simplify using `only [GlobalTheory.RectBlockVolume.reidx_apply, Sum.forall, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, Fin.coe_castAdd, Fin.coe_natAdd, toBlocks₁₁, toBlocks₁₂, toBlocks₂₁, toBlocks₂₂, of_apply, zpow_zero, zpow_one, map_one, n1, n2, false_implies, implies_true, and_tru …`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨hK, ⟨hI1, hI2⟩, -, hL⟩`. Conclude with `⟨hK, fun i j => (hI1 i).2 j, hL, fun i j => (hI2 i).2 j⟩`. Introduce and unpack `⟨hK, h12, hL, h22⟩`. Establish `hK'` using `(GlobalTheory.ParahoricConjBlocks.mem_KO_val_iff _).1 hK`. Conclude with `⟨hK, ⟨fun i => ⟨fun j => hK'.1 i j, fun j => h12 i j⟩, fun i => ⟨fun j => (hL i j).le, fun j => h22 i j⟩⟩, trivial, hL⟩`.

Establish `hpre : GlobalTheory.SplitWeil.volM ν (Fin (r + b')) (Fin (r + a')) {x : Matrix (Fin (r + b')) (Fin (r + a')) k | topL r x ∈ Units.val '' (GlobalTheory.SplitWeil.KO k (Fin r) : Set (GL (Fin r) k)) ∧ (∀ i j, valuation k (x i j) ≤ 1) ∧ ∀ i j, r ≤ i.val → j.val < r → valuation k (x i …`. Rewrite using `[← hset]`. Conclude with `((GlobalTheory.RectBlockVolume.reidx_mp ν r a' b').measure_preimage_equiv _).symm`. Establish `htot : GlobalTheory.SplitWeil.volM ν (Fin (r + b')) (Fin (r + a')) {x : Matrix (Fin (r + b')) (Fin (r + a')) k | ∀ i j, valuation k (x i j) ≤ 1} = GlobalTheory.SplitWeil.volM ν (Fin (r + b')) (Fin (r + a')) {y | ∀ i j, valuation k (y i j) ≤ valuation k ((ϖ : k) ^ ((fun _ _ => (0 …`. Simplify using `only [zpow_zero, map_one]`.

Rewrite using `[hpre, htot, GlobalTheory.RectBlockVolume.volM_rect_blocks, GlobalTheory.BoxVolume.volM_box k ν ϖ hϖ, GlobalTheory.BoxVolume.volM_box k ν ϖ hϖ, GlobalTheory.BoxVolume.volM_box k ν ϖ hϖ, GlobalTheory.BoxVolume.volM_box k ν ϖ hϖ]`. Use `clear hset hpre htot`. Establish `hq0 : (0 : ℝ) ≤ (GlobalTheory.SplitWeil.resCard k : ℝ)` using `Nat.cast_nonneg _`. Simplify using `only [Fintype.card_fin, Finset.sum_const_zero, neg_zero, zpow_zero, ENNReal.ofReal_one, mul_one, Finset.sum_const, Finset.card_univ, smul_eq_mul, nsmul_eq_mul, Nat.add_sub_cancel_left]`. Simplify using `only [ENNReal.toReal_mul, ENNReal.toReal_pow]`.

Rewrite using `[ENNReal.toReal_ofReal (zpow_nonneg hq0 _), GlobalTheory.RectBlockVolume.volKO_real]`. Establish `hz : ∀ m n : ℕ, (GlobalTheory.SplitWeil.resCard k : ℝ) ^ (-((m : ℤ) * (n : ℤ))) = ((GlobalTheory.SplitWeil.resCard k : ℝ) ^ (n * m))⁻¹`. Introduce `m n`. Rewrite using `[_root_.zpow_neg, show ((m : ℤ) * (n : ℤ)) = ((n * m : ℕ) : ℤ) by push_cast; ring, _root_.zpow_natCast]`. Rewrite using `[hz]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem GlobalTheory.RectBlockVolume.vol_topBlock_KO : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), ν.IsAddHaarMeasure → ∀ (a b r : ℕ), r ≤ a → r ≤ b → (GlobalTheory.SplitWeil.volM ν (Fin b) (Fin a) {x | topL r x ∈ Units.val '' (GlobalTheory.SplitWeil.KO k (Fin r) : Set (GL (Fin r) k)) ∧ (∀ i j, ValuativeRel.valuation k (x i j) ≤ 1) ∧ ∀ i j, r ≤ i.val → j.val < r → ValuativeRel.valuation k (x i j) < 1}).toReal = (GlobalTheory.SplitWeil.volM ν (Fin b) (Fin a) {x | ∀ i j, ValuativeRel.valuation k (x i j) ≤ 1}).toReal * ((∏ n ∈ Finset.Ioc 0 r, (1 - ((GlobalTheory.SplitWeil.resCard k : ℝ) ^ n)⁻¹)) * ((GlobalTheory.SplitWeil.resCard k : ℝ) ^ (r * (b - r)))⁻¹) := by
  intro k _ _ _ _ _ _ ν hν a b r hra hrb
  haveI := hν
  haveI := GlobalTheory.SplitWeil.secondCountable k
  haveI : SigmaFinite ν := inferInstance
  obtain ⟨a', rfl⟩ := Nat.exists_eq_add_of_le hra
  obtain ⟨b', rfl⟩ := Nat.exists_eq_add_of_le hrb
  obtain ⟨ϖ, hϖ⟩ : ∃ ϖ : kˣ, valuation k (ϖ : k) = uniformizer k := by
    obtain ⟨x, hx⟩ := valuation_surjective (uniformizer k)
    refine ⟨Units.mk0 x fun h => ?_, hx⟩
    subst h
    rw [map_zero] at hx
    exact (show uniformizer k ≠ 0 by simp) hx.symm
  have hset : GlobalTheory.RectBlockVolume.reidx r a' b' ⁻¹' {x : Matrix (Fin (r + b')) (Fin (r + a')) k | topL r x ∈ Units.val '' (GlobalTheory.SplitWeil.KO k (Fin r) : Set (GL (Fin r) k)) ∧ (∀ i j, valuation k (x i j) ≤ 1) ∧ ∀ i j, r ≤ i.val → j.val < r → valuation k (x i j) < 1} =
      {y | y.toBlocks₁₁ ∈ Units.val '' (GlobalTheory.SplitWeil.KO k (Fin r) : Set (GL (Fin r) k)) ∧
        y.toBlocks₁₂ ∈ {z : Matrix (Fin r) (Fin a') k | ∀ i j, valuation k (z i j) ≤ valuation k ((ϖ : k) ^ ((fun _ _ => (0 : ℤ)) i j))} ∧
        y.toBlocks₂₁ ∈ {z : Matrix (Fin b') (Fin r) k | ∀ i j, valuation k (z i j) ≤ valuation k ((ϖ : k) ^ ((fun _ _ => (1 : ℤ)) i j))} ∧
        y.toBlocks₂₂ ∈ {z : Matrix (Fin b') (Fin a') k | ∀ i j, valuation k (z i j) ≤ valuation k ((ϖ : k) ^ ((fun _ _ => (0 : ℤ)) i j))}} := by
    ext y
    simp only [Set.mem_preimage, Set.mem_setOf_eq]
    have htop : topL r (GlobalTheory.RectBlockVolume.reidx r a' b' y) = y.toBlocks₁₁ := by
      ext i j
      simp only [topL]
      rw [dif_pos ⟨by omega, by omega⟩]
      have e1 : (⟨i.val, by omega⟩ : Fin (r + b')) = finSumFinEquiv (Sum.inl i) := Fin.ext (by simp)
      have e2 : (⟨j.val, by omega⟩ : Fin (r + a')) = finSumFinEquiv (Sum.inl j) := Fin.ext (by simp)
      rw [e1, e2, GlobalTheory.RectBlockVolume.reidx_apply]
      rfl
    rw [htop]
    have hall : ∀ P : Fin (r + b') → Fin (r + a') → Prop,
        (∀ i j, P i j) ↔ ∀ i j, P (finSumFinEquiv i) (finSumFinEquiv j) := fun P =>
      ⟨fun h i j => h _ _, fun h i j => by simpa using h (finSumFinEquiv.symm i) (finSumFinEquiv.symm j)⟩
    rw [hall (fun i j => valuation k (GlobalTheory.RectBlockVolume.reidx r a' b' y i j) ≤ 1),
      hall (fun i j => r ≤ i.val → j.val < r → valuation k (GlobalTheory.RectBlockVolume.reidx r a' b' y i j) < 1)]
    have n1 : ∀ i : Fin r, ¬ r ≤ i.val := fun i => not_le.mpr i.2
    have n2 : ∀ j : Fin a', ¬ (r + j.val < r) := fun j => by omega
    simp only [GlobalTheory.RectBlockVolume.reidx_apply, Sum.forall, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right,
      Fin.coe_castAdd, Fin.coe_natAdd, toBlocks₁₁, toBlocks₁₂, toBlocks₂₁, toBlocks₂₂, of_apply, zpow_zero,
      zpow_one, map_one, n1, n2, false_implies, implies_true, and_true, Nat.le_add_right, Fin.is_lt, true_implies,
      ← GlobalTheory.ParahoricConjBlocks.val_lt_one_iff hϖ]
    constructor
    · rintro ⟨hK, ⟨hI1, hI2⟩, -, hL⟩
      exact ⟨hK, fun i j => (hI1 i).2 j, hL, fun i j => (hI2 i).2 j⟩
    · rintro ⟨hK, h12, hL, h22⟩
      have hK' := (GlobalTheory.ParahoricConjBlocks.mem_KO_val_iff _).1 hK
      exact ⟨hK, ⟨fun i => ⟨fun j => hK'.1 i j, fun j => h12 i j⟩,
        fun i => ⟨fun j => (hL i j).le, fun j => h22 i j⟩⟩, trivial, hL⟩
  have hpre : GlobalTheory.SplitWeil.volM ν (Fin (r + b')) (Fin (r + a')) {x : Matrix (Fin (r + b')) (Fin (r + a')) k | topL r x ∈ Units.val '' (GlobalTheory.SplitWeil.KO k (Fin r) : Set (GL (Fin r) k)) ∧ (∀ i j, valuation k (x i j) ≤ 1) ∧ ∀ i j, r ≤ i.val → j.val < r → valuation k (x i j) < 1} =
      GlobalTheory.SplitWeil.volM ν (Fin r ⊕ Fin b') (Fin r ⊕ Fin a') {y | y.toBlocks₁₁ ∈ Units.val '' (GlobalTheory.SplitWeil.KO k (Fin r) : Set (GL (Fin r) k)) ∧
        y.toBlocks₁₂ ∈ {z : Matrix (Fin r) (Fin a') k | ∀ i j, valuation k (z i j) ≤ valuation k ((ϖ : k) ^ ((fun _ _ => (0 : ℤ)) i j))} ∧
        y.toBlocks₂₁ ∈ {z : Matrix (Fin b') (Fin r) k | ∀ i j, valuation k (z i j) ≤ valuation k ((ϖ : k) ^ ((fun _ _ => (1 : ℤ)) i j))} ∧
        y.toBlocks₂₂ ∈ {z : Matrix (Fin b') (Fin a') k | ∀ i j, valuation k (z i j) ≤ valuation k ((ϖ : k) ^ ((fun _ _ => (0 : ℤ)) i j))}} := by
    rw [← hset]
    exact ((GlobalTheory.RectBlockVolume.reidx_mp ν r a' b').measure_preimage_equiv _).symm
  have htot : GlobalTheory.SplitWeil.volM ν (Fin (r + b')) (Fin (r + a')) {x : Matrix (Fin (r + b')) (Fin (r + a')) k | ∀ i j, valuation k (x i j) ≤ 1} =
      GlobalTheory.SplitWeil.volM ν (Fin (r + b')) (Fin (r + a')) {y | ∀ i j, valuation k (y i j) ≤ valuation k ((ϖ : k) ^ ((fun _ _ => (0 : ℤ)) i j))} := by
    simp only [zpow_zero, map_one]
  rw [hpre, htot, GlobalTheory.RectBlockVolume.volM_rect_blocks, GlobalTheory.BoxVolume.volM_box k ν ϖ hϖ, GlobalTheory.BoxVolume.volM_box k ν ϖ hϖ,
    GlobalTheory.BoxVolume.volM_box k ν ϖ hϖ, GlobalTheory.BoxVolume.volM_box k ν ϖ hϖ]
  clear hset hpre htot
  have hq0 : (0 : ℝ) ≤ (GlobalTheory.SplitWeil.resCard k : ℝ) := Nat.cast_nonneg _
  simp only [Fintype.card_fin, Finset.sum_const_zero, neg_zero, zpow_zero, ENNReal.ofReal_one, mul_one,
    Finset.sum_const, Finset.card_univ, smul_eq_mul, nsmul_eq_mul, Nat.add_sub_cancel_left]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow]
  rw [ENNReal.toReal_ofReal (zpow_nonneg hq0 _), GlobalTheory.RectBlockVolume.volKO_real]
  have hz : ∀ m n : ℕ, (GlobalTheory.SplitWeil.resCard k : ℝ) ^ (-((m : ℤ) * (n : ℤ))) = ((GlobalTheory.SplitWeil.resCard k : ℝ) ^ (n * m))⁻¹ := by
    intro m n
    rw [_root_.zpow_neg, show ((m : ℤ) * (n : ℤ)) = ((n * m : ℕ) : ℤ) by push_cast; ring, _root_.zpow_natCast]
  rw [hz]
  ring
