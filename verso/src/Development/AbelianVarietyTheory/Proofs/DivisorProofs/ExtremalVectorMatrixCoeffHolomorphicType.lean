import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSmoothVector
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmFnAndKilledFnOfHolFn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicTypeOfSmoothBorelKilledStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscreteSeriesModelUnitaryIrreducibleOrthonormalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseFrameBorelActsExtremalVectorByWeightStatement

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolDict.CoefExt

open GlobalTheory.HolDict.HolTo

section General

variable {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] {Hm : ι → Mt n} {H : ι → Type}
  [∀ τ, NormedAddCommGroup (H τ)] [∀ τ, InnerProductSpace ℂ (H τ)] {σ : ∀ τ, Mt n → (H τ →L[ℂ] H τ)} {v : ∀ τ, H τ}

omit [Fintype ι] in
/- English proof (translation)
Rewrite using `[Pi.list_prod_apply, List.map_ofFn]`. Use `congr 2`. Use function extensionality and compare the values at `i`. Distinguish the cases in `h : ρ = τs i`. Substitute `h` using the available equality.

Simplify using the standard rewrite rules. Simplify using `[h]`.
-/
theorem prod_single_apply (k : ℕ) (τs : Fin k → ι) (Xs : Fin k → Mt n) (t : Fin k → ℝ) (ρ : ι) :
    (List.ofFn fun i => (Pi.mulSingle (τs i) (NormedSpace.exp (t i • Xs i)) : ι → Mt n)).prod ρ =
      (List.ofFn fun i => NormedSpace.exp (t i • (if ρ = τs i then Xs i else 0))).prod := by
  rw [Pi.list_prod_apply, List.map_ofFn]
  congr 2
  funext i
  by_cases h : ρ = τs i
  · subst h
    simp
  · simp [h]

/- English proof (translation)
Introduce `k τs Xs hX u hu`. Establish `hmem : ∀ t : Fin k → ℝ, (List.ofFn fun i => (Pi.mulSingle (τs i) (NormedSpace.exp (t i • Xs i)) : ι → Mt n)).prod ∈ UG Hm` using `fun t => prod_mem_UG _ fun v hv => by`. Take `⟨i, rfl⟩` from `List.mem_ofFn.1 hv`. Conclude with `single_mem_UG Hm _ (hX i) _`. Use `contDiff_prod fun ρ _ => ?_` and prove the remaining obligations.

Simplify using `only [Pi.mul_apply, (hσ ρ).2 _ (hu ρ) _ (hmem _ ρ), ContinuousLinearMap.comp_apply]`. Simplify using `only [prod_single_apply]`. Establish `h1` using `hv ρ k (fun i => if ρ = τs i then Xs i else 0) fun i => by split_ifs with h`. Substitute `h` using the available equality. Conclude with `hX i`.

Use `show _ = _`. Simplify using the standard rewrite rules. Conclude with `(((innerSL ℂ (v ρ)).comp (σ ρ (u ρ))).restrictScalars ℝ).contDiff.comp h1`.
-/
theorem smFn_coef (hσ : ∀ τ, Formalism.QuantumDeterminants.IsCRepOn (Formalism.QuantumDeterminants.UH (Hm τ)) (σ τ))
    (hv : ∀ τ, SmoothVec (lieH (Hm τ)) (σ τ) (v τ)) :
    SmFn Hm fun u => ∏ τ, ⟪v τ, σ τ (u τ) (v τ)⟫_ℂ := by
  intro k τs Xs hX u hu
  have hmem : ∀ t : Fin k → ℝ, (List.ofFn fun i =>
      (Pi.mulSingle (τs i) (NormedSpace.exp (t i • Xs i)) : ι → Mt n)).prod ∈ UG Hm := fun t =>
    prod_mem_UG _ fun v hv => by
      obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hv
      exact single_mem_UG Hm _ (hX i) _
  refine contDiff_prod fun ρ _ => ?_
  simp only [Pi.mul_apply, (hσ ρ).2 _ (hu ρ) _ (hmem _ ρ), ContinuousLinearMap.comp_apply]
  simp only [prod_single_apply]
  have h1 := hv ρ k (fun i => if ρ = τs i then Xs i else 0) fun i => by
    split_ifs with h
    · subst h
      exact hX i
    · show _ = _
      simp
  exact (((innerSL ℂ (v ρ)).comp (σ ρ (u ρ))).restrictScalars ℝ).contDiff.comp h1

/- English proof (translation)
Establish `h1` using `hx 1 (fun _ => X) fun _ => hX`. Establish `h2 : ContDiff ℝ ∞ (fun r : ℝ => (fun _ => r : Fin 1 → ℝ))` using `by fun_prop`. Establish `h3` using `(h1.comp h2).differentiable (by simp)`. Establish `h4 : Differentiable ℝ fun t : ℝ => π (NormedSpace.exp (t • X)) x`. Establish `e : (fun t : ℝ => π (NormedSpace.exp (t • X)) x) = ((fun t : Fin 1 → ℝ => π ((List.ofFn fun i => NormedSpace.exp (t i • X)).prod) x) ∘ fun r _ => r)`.

Use function extensionality and compare the values at `r`. Simplify using the standard rewrite rules. Rewrite using `[e]`. Conclude with `h3`. Conclude with `(h4 0).hasDerivAt`.
-/
theorem hasDerivAt_of_smooth {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] {L : Set (Mt n)}
    {π : Mt n → (K →L[ℂ] K)} {x : K} (hx : SmoothVec L π x) {X : Mt n} (hX : X ∈ L) :
    HasDerivAt (fun t : ℝ => π (NormedSpace.exp (t • X)) x) (dRep π X x) 0 := by
  have h1 := hx 1 (fun _ => X) fun _ => hX
  have h2 : ContDiff ℝ ∞ (fun r : ℝ => (fun _ => r : Fin 1 → ℝ)) := by fun_prop
  have h3 := (h1.comp h2).differentiable (by simp)
  have h4 : Differentiable ℝ fun t : ℝ => π (NormedSpace.exp (t • X)) x := by
    have e : (fun t : ℝ => π (NormedSpace.exp (t • X)) x) = ((fun t : Fin 1 → ℝ =>
        π ((List.ofFn fun i => NormedSpace.exp (t i • X)).prod) x) ∘ fun r _ => r) := by
      funext r
      simp
    rw [e]
    exact h3
  exact (h4 0).hasDerivAt

/- English proof (translation)
Unfold `der`. Establish `e : (fun t : ℝ => ∏ ρ, ⟪v ρ, σ ρ ((u * (Pi.mulSingle τ (NormedSpace.exp (t • X)) : ι → Mt n)) ρ) (v ρ)⟫_ℂ) = fun t : ℝ => ⟪v τ, σ τ (u τ) (σ τ (NormedSpace.exp (t • X)) (v τ))⟫_ℂ * ∏ ρ ∈ Finset.univ.erase τ, ⟪v ρ, σ ρ (u ρ) (v ρ)⟫_ℂ`. Use function extensionality and compare the values at `t`. Rewrite using `[← Finset.mul_prod_erase _ _ (Finset.mem_univ τ), Pi.mul_apply, (hσ τ).2 _ (hu τ) _ (single_mem_UG Hm τ hX t τ), Pi.mulSingle_eq_same]`. Use `congr 1`.

Use `Finset.prod_congr rfl fun ρ hρ => ?_` and prove the remaining obligations. Rewrite using `[Pi.mul_apply, Pi.mulSingle_eq_of_ne (Finset.ne_of_mem_erase hρ), mul_one]`. Rewrite using `[e]`. Establish `h1` using `(((innerSL ℂ (v τ)).comp (σ τ (u τ))).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hasDerivAt_of_smooth (hv τ) hX)`. Conclude with `(h1.mul_const _).deriv`.
-/
theorem der_coef (hσ : ∀ τ, Formalism.QuantumDeterminants.IsCRepOn (Formalism.QuantumDeterminants.UH (Hm τ)) (σ τ))
    (hv : ∀ τ, SmoothVec (lieH (Hm τ)) (σ τ) (v τ)) (τ : ι) {X : Mt n} (hX : X ∈ lieH (Hm τ)) {u : ι → Mt n}
    (hu : u ∈ UG Hm) :
    der τ X (fun u => ∏ τ, ⟪v τ, σ τ (u τ) (v τ)⟫_ℂ) u =
      ⟪v τ, σ τ (u τ) (dRep (σ τ) X (v τ))⟫_ℂ * ∏ ρ ∈ Finset.univ.erase τ, ⟪v ρ, σ ρ (u ρ) (v ρ)⟫_ℂ := by
  unfold der
  have e : (fun t : ℝ => ∏ ρ, ⟪v ρ, σ ρ ((u * (Pi.mulSingle τ (NormedSpace.exp (t • X)) : ι → Mt n)) ρ) (v ρ)⟫_ℂ) =
      fun t : ℝ => ⟪v τ, σ τ (u τ) (σ τ (NormedSpace.exp (t • X)) (v τ))⟫_ℂ *
        ∏ ρ ∈ Finset.univ.erase τ, ⟪v ρ, σ ρ (u ρ) (v ρ)⟫_ℂ := by
    funext t
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ τ), Pi.mul_apply,
      (hσ τ).2 _ (hu τ) _ (single_mem_UG Hm τ hX t τ), Pi.mulSingle_eq_same]
    congr 1
    refine Finset.prod_congr rfl fun ρ hρ => ?_
    rw [Pi.mul_apply, Pi.mulSingle_eq_of_ne (Finset.ne_of_mem_erase hρ), mul_one]
  rw [e]
  have h1 := (((innerSL ℂ (v τ)).comp (σ τ (u τ))).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ)
    (hasDerivAt_of_smooth (hv τ) hX)
  exact (h1.mul_const _).deriv

/- English proof (translation)
Take `⟨h1, h2⟩` from `conj_facts (herm_of_orth (h τ)) (dets_ne (h τ)).1 Z`. Establish `hA : (1 / 2 : ℂ) • (Z + conjH (Hm τ) Z) ∈ lieH (Hm τ)` using `by show _ = _`. Rewrite using `[conjTranspose_smul, conjTranspose_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add, h1, h2]`. Establish `: star (1 / 2 : ℂ) = 1 / 2` using `by simp`. Rewrite using `[this, ← smul_add]`.

Use `abel_nf`. Simplify using the standard rewrite rules. Establish `hB : (1 / (2 * Complex.I) : ℂ) • (Z - conjH (Hm τ) Z) ∈ lieH (Hm τ)` using `by show _ = _`. Rewrite using `[conjTranspose_smul, conjTranspose_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub, h1, h2]`. Establish `: star (1 / (2 * Complex.I) : ℂ) = -(1 / (2 * Complex.I))` using `by simp`.

Rewrite using `[this, neg_smul, ← smul_neg, ← smul_add]`. Use `abel_nf`. Simplify using the standard rewrite rules. Unfold `derC dRepC`. Rewrite using `[der_coef hσ hv τ hA hu, der_coef hσ hv τ hB hu, map_add, map_smul, inner_add_right, inner_smul_right]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem derC_coef {q : ι → ℕ} {x₀ : ι → Mt n} (h : ∀ τ, OrthFr (Hm τ) (q τ) (x₀ τ))
    (hσ : ∀ τ, Formalism.QuantumDeterminants.IsCRepOn (Formalism.QuantumDeterminants.UH (Hm τ)) (σ τ))
    (hv : ∀ τ, SmoothVec (lieH (Hm τ)) (σ τ) (v τ)) (τ : ι) (Z : Mt n) {u : ι → Mt n} (hu : u ∈ UG Hm) :
    derC Hm τ Z (fun u => ∏ τ, ⟪v τ, σ τ (u τ) (v τ)⟫_ℂ) u =
      ⟪v τ, σ τ (u τ) (dRepC (Hm τ) (σ τ) Z (v τ))⟫_ℂ * ∏ ρ ∈ Finset.univ.erase τ, ⟪v ρ, σ ρ (u ρ) (v ρ)⟫_ℂ := by
  obtain ⟨h1, h2⟩ := conj_facts (herm_of_orth (h τ)) (dets_ne (h τ)).1 Z
  have hA : (1 / 2 : ℂ) • (Z + conjH (Hm τ) Z) ∈ lieH (Hm τ) := by
    show _ = _
    rw [conjTranspose_smul, conjTranspose_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add, h1, h2]
    have : star (1 / 2 : ℂ) = 1 / 2 := by simp
    rw [this, ← smul_add]
    abel_nf
    simp
  have hB : (1 / (2 * Complex.I) : ℂ) • (Z - conjH (Hm τ) Z) ∈ lieH (Hm τ) := by
    show _ = _
    rw [conjTranspose_smul, conjTranspose_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub, h1, h2]
    have : star (1 / (2 * Complex.I) : ℂ) = -(1 / (2 * Complex.I)) := by simp
    rw [this, neg_smul, ← smul_neg, ← smul_add]
    abel_nf
    simp
  unfold derC dRepC
  rw [der_coef hσ hv τ hA hu, der_coef hσ hv τ hB hu, map_add, map_smul, inner_add_right, inner_smul_right]
  ring

/- English proof (translation)
Introduce `τ a c hac u hu`. Rewrite using `[derC_coef h hσ hv τ _ hu, hk τ a c hac]`. Use `split_ifs`. Rewrite using `[map_smul, inner_smul_right, mul_assoc] beta_reduce`. Rewrite using `[← Finset.mul_prod_erase _ _ (Finset.mem_univ τ)]`.

Simplify using the standard rewrite rules.
-/
theorem killedFn_coef {q : ι → ℕ} {x₀ : ι → Mt n} {w : ι → Fin n → ℤ} (h : ∀ τ, OrthFr (Hm τ) (q τ) (x₀ τ))
    (hσ : ∀ τ, Formalism.QuantumDeterminants.IsCRepOn (Formalism.QuantumDeterminants.UH (Hm τ)) (σ τ))
    (hv : ∀ τ, SmoothVec (lieH (Hm τ)) (σ τ) (v τ))
    (hk : ∀ τ (a c : Fin n), a ≤ c → dRepC (Hm τ) (σ τ) (x₀ τ * Matrix.single a c 1 * (x₀ τ)⁻¹) (v τ) =
      if a = c then (w τ a : ℂ) • v τ else 0) :
    KilledFn Hm x₀ w fun u => ∏ τ, ⟪v τ, σ τ (u τ) (v τ)⟫_ℂ := by
  intro τ a c hac u hu
  rw [derC_coef h hσ hv τ _ hu, hk τ a c hac]
  split_ifs
  · rw [map_smul, inner_smul_right, mul_assoc]
    beta_reduce
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ τ)]
  · simp

end General

/- English proof (translation)
Use `Finite.injective_iff_bijective.1 fun a b hab => ?_` and prove the remaining obligations. Establish `h` using `congrArg Fin.val hab`. Use `a.2` as an intermediate fact. Use `b.2` as an intermediate fact. Unfold `arr at h`.

Apply `Fin.ext` to reduce the goal to its premises. Apply the tactic sequence `split_ifs at h <;> simp only at h <;> omega`.
-/
theorem arr_bijective {n q : ℕ} (hq : q ≤ n) : Function.Bijective (arr (n := n) q) := by
  refine Finite.injective_iff_bijective.1 fun a b hab => ?_
  have h := congrArg Fin.val hab
  have := a.2
  have := b.2
  unfold arr at h
  apply Fin.ext
  split_ifs at h <;> simp only at h <;> omega

/- English proof (translation)
Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.mem_unitaryGroup_iff, star_eq_conjTranspose, diagonal_conjTranspose, diagonal_mul_diagonal, ← diagonal_one]`. Use `congr 1`. Use function extensionality and compare the values at `a`. Simplify using `only [Pi.star_apply, Complex.star_def]`.

Rewrite using `[← Complex.exp_conj, ← Complex.exp_add]`. Simplify using the standard rewrite rules. Unfold `Formalism.REAL.Jm`. Rewrite using `[diagonal_mul_diagonal, diagonal_mul_diagonal]`. Use `congr 1`.

Use function extensionality and compare the values at `a`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem diagonal_mem_Kset {n : ℕ} (ε : Fin n → Bool) (s : Fin n → ℝ) :
    diagonal (fun a => Complex.exp ((s a : ℂ) * Complex.I)) ∈ Formalism.REAL.Kset ε := by
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff, star_eq_conjTranspose, diagonal_conjTranspose, diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext a
    simp only [Pi.star_apply, Complex.star_def]
    rw [← Complex.exp_conj, ← Complex.exp_add]
    simp
  · unfold Formalism.REAL.Jm
    rw [diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 1
    funext a
    ring

/- English proof (translation)
Use `set e := Equiv.ofBijective _ (arr_bijective (nNeg_le (M.ε τ))) with he`. Establish `hfr : IsUnit (M.fr τ).det` using `(Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)`. Establish `h1` using `torus_x0Mat M τ fun a => Complex.exp ((s τ (e.symm a) : ℂ) * Complex.I)`. Establish `h2 : ∀ c, e.symm (arr (nNeg (M.ε τ)) c) = c` using `fun c => e.symm_apply_apply c`. Simplify using `only [h2] at h1`.

Establish `h3 : M.fr τ * torEl (x0Mat M) s τ * (M.fr τ)⁻¹ = diagonal fun a => Complex.exp ((s τ (e.symm a) : ℂ) * Complex.I)`. Unfold `torEl`. Rewrite using `[← h1, Matrix.mul_nonsing_inv_cancel_right _ _ hx.isUnit, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hfr, Matrix.mul_nonsing_inv_cancel_right _ _ hfr]`. Unfold `DSModel.rep`. Rewrite using `[h3, (hv τ).2.2 (fun a => s τ (e.symm a)) (diagonal_mem_Kset _ _)]`.

Use `congr 1`. Rewrite using `[← e.sum_comp]`. Simplify using `only [← Complex.exp_int_mul, ← Complex.exp_sum, Equiv.symm_apply_apply]`. Use `congr 1`. Use `push_cast`.

Rewrite using `[Finset.sum_mul]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Establish `h4 : extWt M τ (e c) = (w τ c : ℝ)` using `(hw τ c).symm`. Rewrite using `[h4]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem torus_ext {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) {w : D.what₂.Tau → Fin V.rank → ℤ}
    {v : M.Vec} (hw : WtIs M w) (hv : IsExtVec M v) (s : D.what₂.Tau → Fin V.rank → ℝ) (τ : D.what₂.Tau)
    (hx : (x0Mat M τ).det ≠ 0) :
    M.rep τ (torEl (x0Mat M) s τ) (v τ : M.H τ) =
      (∏ a, Complex.exp ((s τ a : ℂ) * Complex.I) ^ w τ a) • (v τ : M.H τ) := by
  set e := Equiv.ofBijective _ (arr_bijective (nNeg_le (M.ε τ))) with he
  have hfr : IsUnit (M.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  have h1 := torus_x0Mat M τ fun a => Complex.exp ((s τ (e.symm a) : ℂ) * Complex.I)
  have h2 : ∀ c, e.symm (arr (nNeg (M.ε τ)) c) = c := fun c => e.symm_apply_apply c
  simp only [h2] at h1
  have h3 : M.fr τ * torEl (x0Mat M) s τ * (M.fr τ)⁻¹ =
      diagonal fun a => Complex.exp ((s τ (e.symm a) : ℂ) * Complex.I) := by
    unfold torEl
    rw [← h1, Matrix.mul_nonsing_inv_cancel_right _ _ hx.isUnit, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv_cancel_left _ _ hfr, Matrix.mul_nonsing_inv_cancel_right _ _ hfr]
  unfold DSModel.rep
  rw [h3, (hv τ).2.2 (fun a => s τ (e.symm a)) (diagonal_mem_Kset _ _)]
  congr 1
  rw [← e.sum_comp]
  simp only [← Complex.exp_int_mul, ← Complex.exp_sum, Equiv.symm_apply_apply]
  congr 1
  push_cast
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun c _ => ?_
  have h4 : extWt M τ (e c) = (w τ c : ℝ) := (hw τ c).symm
  rw [h4]
  push_cast
  ring

end GlobalTheory.HolDict.CoefExt

namespace GlobalTheory.HolDict

open CoefExt in

/- English proof (translation)
Introduce `D θ V S M w v hθ hM hw hv`. Establish `ho : ∀ τ, OrthFr (gramAt D V τ) (nNeg (M.ε τ)) (x0Mat M τ)` using `fun τ => ((GlobalTheory.T.discreteSeriesModel_unitary_irreducible_orthonormal D V S M τ).2.2.2 hM).1`. Establish `hσ : ∀ τ, Formalism.QuantumDeterminants.IsCRepOn (Formalism.QuantumDeterminants.UH (gramAt D V τ)) (M.rep τ)` using `fun τ => (GlobalTheory.T.discreteSeriesModel_unitary_irreducible_orthonormal D V S M τ).2.1.1`. Establish `hk` using `GlobalTheory.T.baseFrameBorel_acts_extremalVector_by_weight D θ V S M w v hθ hM hw hv`. Use `⟨GlobalTheory.T.holomorphicType_of_smooth_borelKilled _ _ _ _ _ _ ho _ (smFn_coef hσ fun τ => (hk τ).1) (killedFn_coef ho hσ (fun τ => (hk τ).1) fun τ => (hk τ).2), fun s τ => ?_⟩` and prove the remaining obligations.

Conclude with `torus_ext M hw hv s τ (HolTo.dets_ne (ho τ)).2`.
-/
theorem holFn_coef_extVec : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (w : D.what₂.Tau → Fin V.rank → ℤ) (v : M.Vec), IsInfFam θ → HolShape M → WtIs M w → IsExtVec M v → HolFn (gramAt D V) (fun τ => nNeg (M.ε τ)) (x0Mat M) w (fun u => ∏ τ, ⟪(v τ : M.H τ), M.rep τ (u τ) (v τ : M.H τ)⟫_ℂ) ∧ ∀ s τ, M.rep τ (torEl (x0Mat M) s τ) (v τ : M.H τ) = (∏ a, Complex.exp ((s τ a : ℂ) * Complex.I) ^ w τ a) • (v τ : M.H τ) := by
  intro D θ V S M w v hθ hM hw hv
  classical
  have ho : ∀ τ, OrthFr (gramAt D V τ) (nNeg (M.ε τ)) (x0Mat M τ) := fun τ => ((GlobalTheory.T.discreteSeriesModel_unitary_irreducible_orthonormal D V S M τ).2.2.2 hM).1
  have hσ : ∀ τ, Formalism.QuantumDeterminants.IsCRepOn (Formalism.QuantumDeterminants.UH (gramAt D V τ)) (M.rep τ) := fun τ => (GlobalTheory.T.discreteSeriesModel_unitary_irreducible_orthonormal D V S M τ).2.1.1
  have hk := GlobalTheory.T.baseFrameBorel_acts_extremalVector_by_weight D θ V S M w v hθ hM hw hv
  refine ⟨GlobalTheory.T.holomorphicType_of_smooth_borelKilled _ _ _ _ _ _ ho _ (smFn_coef hσ fun τ => (hk τ).1)
    (killedFn_coef ho hσ (fun τ => (hk τ).1) fun τ => (hk τ).2), fun s τ => ?_⟩
  exact torus_ext M hw hv s τ (HolTo.dets_ne (ho τ)).2

end GlobalTheory.HolDict
