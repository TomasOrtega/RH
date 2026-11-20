import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.RealPlaceAnalysis.StatementE
import Formalism.RealPlaceAnalysis.StatementKT
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DerivedActionDiscreteSeriesProperties
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DiscreteSeriesUnitarySmoothBasic

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.CompactStable

open PI.UpqRep

/- English proof (translation)
Establish `hcl : IsClosed (S : Set H)` using `S.closed_of_finiteDimensional`. Establish `hsl` using `hasDerivAt_iff_tendsto_slope_zero.mp hf`. Use `hcl.mem_of_tendsto hsl (Filter.Eventually.of_forall fun t => ?_)` and prove the remaining obligations. Conclude with `S.smul_of_tower_mem t⁻¹ (S.sub_mem (hS _) (hS _))`.
-/
theorem deriv_mem {H : Type} [NormedAddCommGroup H] [NormedSpace ℂ H] (S : Submodule ℂ H) [FiniteDimensional ℂ S]
    {f : ℝ → H} {f' : H} (hf : HasDerivAt f f' 0) (hS : ∀ t, f t ∈ S) : f' ∈ S := by
  have hcl : IsClosed (S : Set H) := S.closed_of_finiteDimensional
  have hsl := hasDerivAt_iff_tendsto_slope_zero.mp hf
  refine hcl.mem_of_tendsto hsl (Filter.Eventually.of_forall fun t => ?_)
  exact S.smul_of_tower_mem t⁻¹ (S.sub_mem (hS _) (hS _))

variable {k r : ℕ}

/- English proof (translation)
Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.conjTranspose_smul, hX, Complex.star_def, Complex.conj_ofReal, smul_neg]`. Rewrite using `[Matrix.mul_smul, hc, Matrix.smul_mul]`.
-/
private lemma real_smul_skew_and_commute {n : ℕ} (M X : Matrix (Fin n) (Fin n) ℂ) (hX : Xᴴ = -X) (hc : M * X = X * M)
    (t : ℝ) : ((t : ℂ) • X)ᴴ = -((t : ℂ) • X) ∧ M * ((t : ℂ) • X) = ((t : ℂ) • X) * M := by
  refine ⟨?_, ?_⟩
  · rw [Matrix.conjTranspose_smul, hX, Complex.star_def, Complex.conj_ofReal, smul_neg]
  · rw [Matrix.mul_smul, hc, Matrix.smul_mul]

/- English proof (translation)
Establish `hu : (NormedSpace.exp Y)ᴴ * NormedSpace.exp Y = 1`. Rewrite using `[← Matrix.exp_conjTranspose, hY, ← Matrix.exp_add_of_commute _ _ (Commute.refl Y).neg_left, neg_add_cancel, NormedSpace.exp_zero]`. Establish `hcm : Commute M (NormedSpace.exp Y)` using `Commute.exp_right hc`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `show (NormedSpace.exp Y)ᴴ * M * NormedSpace.exp Y = M`.

Rewrite using `[Matrix.mul_assoc, hcm.eq, ← Matrix.mul_assoc, hu, Matrix.one_mul]`. Rewrite using `[SetLike.mem_coe, Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]`. Conclude with `hu`.
-/
private lemma exp_real_smul_mem_UJset_of_inG {n : ℕ} (M Y : Matrix (Fin n) (Fin n) ℂ) (hY : Yᴴ = -Y) (hc : M * Y = Y * M) :
    NormedSpace.exp Y ∈ UH M ∩ (Matrix.unitaryGroup (Fin n) ℂ : Set _) := by
  have hu : (NormedSpace.exp Y)ᴴ * NormedSpace.exp Y = 1 := by
    rw [← Matrix.exp_conjTranspose, hY, ← Matrix.exp_add_of_commute _ _ (Commute.refl Y).neg_left,
      neg_add_cancel, NormedSpace.exp_zero]
  have hcm : Commute M (NormedSpace.exp Y) := Commute.exp_right hc
  refine ⟨?_, ?_⟩
  · show (NormedSpace.exp Y)ᴴ * M * NormedSpace.exp Y = M
    rw [Matrix.mul_assoc, hcm.eq, ← Matrix.mul_assoc, hu, Matrix.one_mul]
  · rw [SetLike.mem_coe, Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
    exact hu

/- English proof (translation)
Establish `hmem : ∀ t : ℝ, R.σ (NormedSpace.exp ((t : ℂ) • X)) v ∈ S` using `fun t => hS _ (exp_real_smul_mem_UJset_of_inG _ _ (real_smul_skew_and_commute _ _ hX hc t).1 (real_smul_skew_and_commute _ _ hX hc t).2) v hv`. Use `show deriv (fun t : ℝ => R.σ (NormedSpace.exp ((t : ℂ) • X)) v) 0 ∈ S`. Distinguish the cases in `hd : DifferentiableAt ℝ (fun t : ℝ => R.σ (NormedSpace.exp ((t : ℂ) • X)) v) 0`. Conclude with `deriv_mem S hd.hasDerivAt hmem`. Rewrite using `[deriv_zero_of_not_differentiableAt hd]`.

Conclude with `S.zero_mem`.
-/
theorem dsig_mem (R : Rep k r) (S : Submodule ℂ R.H) [FiniteDimensional ℂ S]
    (hS : ∀ g ∈ UH (Hpk k r) ∩ (Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ : Set _), ∀ x ∈ S, R.σ g x ∈ S)
    {X : Mx k r} (hX : Xᴴ = -X) (hc : Hpk k r * X = X * Hpk k r) {v : R.H} (hv : v ∈ S) (hsm : v ∈ R.sm) :
    dsig (k := k) (r := r) R.σ X v ∈ S := by
  have hmem : ∀ t : ℝ, R.σ (NormedSpace.exp ((t : ℂ) • X)) v ∈ S := fun t =>
    hS _ (exp_real_smul_mem_UJset_of_inG _ _ (real_smul_skew_and_commute _ _ hX hc t).1 (real_smul_skew_and_commute _ _ hX hc t).2) v hv
  show deriv (fun t : ℝ => R.σ (NormedSpace.exp ((t : ℂ) • X)) v) 0 ∈ S
  by_cases hd : DifferentiableAt ℝ (fun t : ℝ => R.σ (NormedSpace.exp ((t : ℂ) • X)) v) 0
  · exact deriv_mem S hd.hasDerivAt hmem
  · rw [deriv_zero_of_not_differentiableAt hd]
    exact S.zero_mem

/- English proof (translation)
Establish `hs : Yᴴ * M = M * Yᴴ`. Establish `h0` using `congrArg Matrix.conjTranspose hc`. Rewrite `h0` using `[Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, h1]`. Then use the resulting hypothesis. Use `⟨?_, hs.symm⟩` and prove the remaining obligations. Rewrite using `[← hs, Matrix.mul_assoc, h2, Matrix.mul_one]`.
-/
private lemma herm_eq_sum_star_mul_mulVec {n : ℕ} (M Y : Matrix (Fin n) (Fin n) ℂ) (h1 : Mᴴ = M) (h2 : M * M = 1)
    (hc : M * Y = Y * M) : M * Yᴴ * M = Yᴴ ∧ M * Yᴴ = Yᴴ * M := by
  have hs : Yᴴ * M = M * Yᴴ := by
    have h0 := congrArg Matrix.conjTranspose hc
    rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, h1] at h0
  refine ⟨?_, hs.symm⟩
  rw [← hs, Matrix.mul_assoc, h2, Matrix.mul_one]

/- English proof (translation)
Establish `hH : Formalism.QuantumDeterminants.Hpk k r = Hpk k r` using `rfl`. Take `⟨hθ, hcs⟩` from `herm_eq_sum_star_mul_mulVec _ Y h1 h2 hc`. Establish `e1 : ((1 / 2 : ℂ) • (Y + -Yᴴ))ᴴ = -((1 / 2 : ℂ) • (Y + -Yᴴ))`. Rewrite using `[Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_neg, Matrix.conjTranspose_conjTranspose, ← smul_neg]`. Use `congr 1`.

Simplify using the standard rewrite rules. Normalize the expressions using the abelian group laws. Establish `hI : star (1 / (2 * Complex.I)) = -(1 / (2 * Complex.I))`. Rewrite using `[Complex.star_def, map_div₀, map_one, map_mul, Complex.conj_I, map_ofNat, mul_neg, div_neg]`. Establish `e2 : ((1 / (2 * Complex.I)) • (Y - -Yᴴ))ᴴ = -((1 / (2 * Complex.I)) • (Y - -Yᴴ))`.

Rewrite using `[Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_neg, Matrix.conjTranspose_conjTranspose, hI, neg_smul]`. Use `congr 2`. Normalize the expressions using the abelian group laws. Establish `c1 : Hpk k r * ((1 / 2 : ℂ) • (Y + -Yᴴ)) = ((1 / 2 : ℂ) • (Y + -Yᴴ)) * Hpk k r`. Rewrite using `[Matrix.mul_smul, Matrix.smul_mul, mul_add, add_mul, mul_neg, neg_mul, hc, hcs]`.

Establish `c2 : Hpk k r * ((1 / (2 * Complex.I)) • (Y - -Yᴴ)) = ((1 / (2 * Complex.I)) • (Y - -Yᴴ)) * Hpk k r`. Rewrite using `[Matrix.mul_smul, Matrix.smul_mul, mul_sub, sub_mul, mul_neg, neg_mul, hc, hcs]`. Unfold `BranchingSupport.Rep.dC`. Rewrite using `[hH, hθ]`. Conclude with `S.add_mem (dsig_mem R S hS e1 c1 hv hsm) (S.smul_mem _ (dsig_mem R S hS e2 c2 hv hsm))`.
-/
theorem dC_mem (R : Rep k r) (S : Submodule ℂ R.H) [FiniteDimensional ℂ S]
    (hS : ∀ g ∈ UH (Hpk k r) ∩ (Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ : Set _), ∀ x ∈ S, R.σ g x ∈ S)
    (h1 : (Hpk k r)ᴴ = Hpk k r) (h2 : Hpk k r * Hpk k r = 1)
    {Y : Mx k r} (hc : Hpk k r * Y = Y * Hpk k r) {v : R.H} (hv : v ∈ S) (hsm : v ∈ R.sm) :
    R.dC Y v ∈ S := by
  have hH : Formalism.QuantumDeterminants.Hpk k r = Hpk k r := rfl
  obtain ⟨hθ, hcs⟩ := herm_eq_sum_star_mul_mulVec _ Y h1 h2 hc
  have e1 : ((1 / 2 : ℂ) • (Y + -Yᴴ))ᴴ = -((1 / 2 : ℂ) • (Y + -Yᴴ)) := by
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_neg,
      Matrix.conjTranspose_conjTranspose, ← smul_neg]
    congr 1
    · simp
    · abel
  have hI : star (1 / (2 * Complex.I)) = -(1 / (2 * Complex.I)) := by
    rw [Complex.star_def, map_div₀, map_one, map_mul, Complex.conj_I, map_ofNat, mul_neg, div_neg]
  have e2 : ((1 / (2 * Complex.I)) • (Y - -Yᴴ))ᴴ = -((1 / (2 * Complex.I)) • (Y - -Yᴴ)) := by
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_neg,
      Matrix.conjTranspose_conjTranspose, hI, neg_smul]
    congr 2
    abel
  have c1 : Hpk k r * ((1 / 2 : ℂ) • (Y + -Yᴴ)) = ((1 / 2 : ℂ) • (Y + -Yᴴ)) * Hpk k r := by
    rw [Matrix.mul_smul, Matrix.smul_mul, mul_add, add_mul, mul_neg, neg_mul, hc, hcs]
  have c2 : Hpk k r * ((1 / (2 * Complex.I)) • (Y - -Yᴴ)) =
      ((1 / (2 * Complex.I)) • (Y - -Yᴴ)) * Hpk k r := by
    rw [Matrix.mul_smul, Matrix.smul_mul, mul_sub, sub_mul, mul_neg, neg_mul, hc, hcs]
  unfold BranchingSupport.Rep.dC
  rw [hH, hθ]
  exact S.add_mem (dsig_mem R S hS e1 c1 hv hsm) (S.smul_mem _ (dsig_mem R S hS e2 c2 hv hsm))

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [Jm, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.single_apply]`. Apply the tactic sequence `split_ifs <;> simp_all`.
-/
theorem Jm_single {n : ℕ} (ε : Fin n → Bool) {a b : Fin n} (h : ε a = ε b) :
    Jm ε * Matrix.single a b (1 : ℂ) = Matrix.single a b 1 * Jm ε := by
  ext i j
  simp only [Jm, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.single_apply]
  split_ifs <;> simp_all

/- English proof (translation)
Take `⟨hgM, hgU⟩` from `hg`. Establish `hgM' : gᴴ * M * g = M` using `hgM`. Establish `q1 : Qᴴ * Q = 1`. Establish `h0` using `Matrix.mem_unitaryGroup_iff'.mp hQ`. Rewrite `h0` using `[Matrix.star_eq_conjTranspose]`. Then use the resulting hypothesis.

Establish `q2 : Q * Qᴴ = 1`. Establish `h0` using `Matrix.mem_unitaryGroup_iff.mp hQ`. Rewrite `h0` using `[Matrix.star_eq_conjTranspose]`. Then use the resulting hypothesis. Establish `g2 : g * gᴴ = 1`. Establish `h0` using `Matrix.mem_unitaryGroup_iff.mp hgU`.

Rewrite `h0` using `[Matrix.star_eq_conjTranspose]`. Then use the resulting hypothesis. Establish `hJ : Jmat = Q * M * Qᴴ`. Rewrite using `[← hcay]`. Combine the equalities or inequalities in the displayed calculation. Establish `hgc : M * g = g * M`.

Combine the equalities or inequalities in the displayed calculation. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Establish `hs : Qᴴ ∈ Matrix.unitaryGroup (Fin n) ℂ`. Rewrite using `[Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]`. Conclude with `q1`.

Conclude with `Submonoid.mul_mem _ (Submonoid.mul_mem _ hQ hgU) hs`. Rewrite using `[hJ]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[q1, Matrix.mul_one, hgc]`. Simplify using `only [Matrix.mul_assoc]`.

Use `_ = Q * M * (Qᴴ * Q) * g * Qᴴ := by`. Rewrite using `[q1, Matrix.mul_one]`. Simplify using `only [Matrix.mul_assoc]`. Use `_ = Q * M * Qᴴ * (Q * g * Qᴴ) := by simp only [Matrix.mul_assoc]`. Combine the equalities or inequalities in the displayed calculation.
-/
private lemma unitary_conj_mem_and_commute_Jmat {n : ℕ} (Jmat M Q g : Matrix (Fin n) (Fin n) ℂ)
    (hQ : Q ∈ Matrix.unitaryGroup (Fin n) ℂ) (hcay : Qᴴ * Jmat * Q = M)
    (hg : g ∈ UH M ∩ (Matrix.unitaryGroup (Fin n) ℂ : Set _)) :
    Q * g * Qᴴ ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ Q * g * Qᴴ * Jmat = Jmat * (Q * g * Qᴴ) ∧
      Qᴴ * (Q * g * Qᴴ) * Q = g := by
  obtain ⟨hgM, hgU⟩ := hg
  have hgM' : gᴴ * M * g = M := hgM
  have q1 : Qᴴ * Q = 1 := by
    have h0 := Matrix.mem_unitaryGroup_iff'.mp hQ
    rwa [Matrix.star_eq_conjTranspose] at h0
  have q2 : Q * Qᴴ = 1 := by
    have h0 := Matrix.mem_unitaryGroup_iff.mp hQ
    rwa [Matrix.star_eq_conjTranspose] at h0
  have g2 : g * gᴴ = 1 := by
    have h0 := Matrix.mem_unitaryGroup_iff.mp hgU
    rwa [Matrix.star_eq_conjTranspose] at h0
  have hJ : Jmat = Q * M * Qᴴ := by
    rw [← hcay]
    calc Jmat = (Q * Qᴴ) * Jmat * (Q * Qᴴ) := by rw [q2, Matrix.one_mul, Matrix.mul_one]
      _ = Q * (Qᴴ * Jmat * Q) * Qᴴ := by simp only [Matrix.mul_assoc]
  have hgc : M * g = g * M := by
    calc M * g = (g * gᴴ) * M * g := by rw [g2, Matrix.one_mul]
      _ = g * (gᴴ * M * g) := by simp only [Matrix.mul_assoc]
      _ = g * M := by rw [hgM']
  refine ⟨?_, ?_, ?_⟩
  · have hs : Qᴴ ∈ Matrix.unitaryGroup (Fin n) ℂ := by
      rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
        Matrix.conjTranspose_conjTranspose]
      exact q1
    exact Submonoid.mul_mem _ (Submonoid.mul_mem _ hQ hgU) hs
  · rw [hJ]
    calc Q * g * Qᴴ * (Q * M * Qᴴ) = Q * g * (Qᴴ * Q) * M * Qᴴ := by simp only [Matrix.mul_assoc]
      _ = Q * (M * g) * Qᴴ := by
          rw [q1, Matrix.mul_one, hgc]
          simp only [Matrix.mul_assoc]
      _ = Q * M * (Qᴴ * Q) * g * Qᴴ := by
          rw [q1, Matrix.mul_one]
          simp only [Matrix.mul_assoc]
      _ = Q * M * Qᴴ * (Q * g * Qᴴ) := by simp only [Matrix.mul_assoc]
  · calc Qᴴ * (Q * g * Qᴴ) * Q = (Qᴴ * Q) * g * (Qᴴ * Q) := by simp only [Matrix.mul_assoc]
      _ = g := by rw [q1, Matrix.one_mul, Matrix.mul_one]

/- English proof (translation)
Introduce `hK k r ε mu R hR Q hQ S hfin hKS`. Take `⟨⟨-, hcay⟩, hQU⟩` from `hQ`. Take `⟨-, -, -, -, hTKsm, -, hKTK, -, -⟩` from `GlobalTheory.rep_basic_of_isDS hK k r ε mu R hR`. Establish `q1 : Qᴴ * Q = 1`. Establish `h0` using `Matrix.mem_unitaryGroup_iff'.mp hQU`.

Rewrite `h0` using `[Matrix.star_eq_conjTranspose]`. Then use the resulting hypothesis. Establish `q2 : Q * Qᴴ = 1`. Establish `h0` using `Matrix.mem_unitaryGroup_iff.mp hQU`. Rewrite `h0` using `[Matrix.star_eq_conjTranspose]`. Then use the resulting hypothesis. Establish `hinv : Q⁻¹ = Qᴴ` using `Matrix.inv_eq_left_inv q1`.

Establish `hS' : ∀ g ∈ UH (Hpk k r) ∩ (Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ : Set _), ∀ x ∈ S, R.σ g x ∈ S`. Introduce `g hg x hx`. Take `⟨hu, hc, he⟩` from `unitary_conj_mem_and_commute_Jmat _ _ Q g hQU hcay hg`. Establish `hk : Q * g * Qᴴ ∈ Kset ε`. Simplify using `only [Kset, Set.mem_ofPred_eq]`.

Conclude with `⟨hu, hc⟩`. Establish `h0` using `hKS (Q * g * Qᴴ) hk x hx`. Simplify using `only [hinv, he] at h0`. Conclude with `h0`. Establish `hsm : ∀ v ∈ S, R.KFin v ∧ v ∈ R.sm`.

Introduce `v hv`. Establish `hkf : R.KFin v`. Simplify using `only [BranchingSupport.Rep.KFin, PI.UpqRep.IsKFinHpk]`. Conclude with `⟨S, hfin, hv, hS'⟩`. Conclude with `⟨hkf, hTKsm v (hKTK v hkf)⟩`.

Use `⟨hsm, fun a b hab v hv => ?_⟩` and prove the remaining obligations. Establish `h1 : (Hpk k r)ᴴ = Hpk k r`. Rewrite using `[← hcay, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Jm_conjTranspose]`. Simplify using `only [Matrix.mul_assoc]`. Establish `h2 : Hpk k r * Hpk k r = 1`.

Rewrite using `[← hcay]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`. Use `_ = 1 := by`. Rewrite using `[q2, Matrix.mul_one, Matrix.mul_assoc (Qᴴ) (Jm ε), Jm_mul_self, Matrix.mul_one, q1]`.

Establish `hc : Hpk k r * (Q⁻¹ * Matrix.single a b 1 * Q) = (Q⁻¹ * Matrix.single a b 1 * Q) * Hpk k r`. Rewrite using `[hinv, ← hcay]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[q2, Matrix.mul_one]`. Simplify using `only [Matrix.mul_assoc]`.

Use `_ = Qᴴ * (Matrix.single a b 1 * Jm ε) * Q := by rw [Jm_single ε hab]`. Use `_ = Qᴴ * Matrix.single a b 1 * (Q * Qᴴ) * Jm ε * Q := by`. Rewrite using `[q2, Matrix.mul_one]`. Simplify using `only [Matrix.mul_assoc]`. Use `_ = Qᴴ * Matrix.single a b 1 * Q * (Qᴴ * Jm ε * Q) := by simp only [Matrix.mul_assoc]`.

Conclude with `dC_mem R S hS' h1 h2 hc hv (hsm v hv).2`.
-/
theorem kStable_smooth_and_stable : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDS ε mu → ∀ (Q : Mx k r), PI.UpqRep.IsCayleyU k r ε Q → ∀ S : Submodule ℂ R.H, FiniteDimensional ℂ S → PI.UpqRep.IsKStableOn ε (fun g => R.σ (Q⁻¹ * g * Q)) S → (∀ v ∈ S, R.KFin v ∧ v ∈ R.sm) ∧ ∀ a b, ε a = ε b → ∀ v ∈ S, R.dC (Q⁻¹ * Matrix.single a b 1 * Q) v ∈ S := by
  intro hK k r ε mu R hR Q hQ S hfin hKS
  obtain ⟨⟨-, hcay⟩, hQU⟩ := hQ
  obtain ⟨-, -, -, -, hTKsm, -, hKTK, -, -⟩ := GlobalTheory.rep_basic_of_isDS hK k r ε mu R hR
  have q1 : Qᴴ * Q = 1 := by
    have h0 := Matrix.mem_unitaryGroup_iff'.mp hQU
    rwa [Matrix.star_eq_conjTranspose] at h0
  have q2 : Q * Qᴴ = 1 := by
    have h0 := Matrix.mem_unitaryGroup_iff.mp hQU
    rwa [Matrix.star_eq_conjTranspose] at h0
  have hinv : Q⁻¹ = Qᴴ := Matrix.inv_eq_left_inv q1
  have hS' : ∀ g ∈ UH (Hpk k r) ∩ (Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ : Set _), ∀ x ∈ S,
      R.σ g x ∈ S := by
    intro g hg x hx
    obtain ⟨hu, hc, he⟩ := unitary_conj_mem_and_commute_Jmat _ _ Q g hQU hcay hg
    have hk : Q * g * Qᴴ ∈ Kset ε := by
      simp only [Kset, Set.mem_ofPred_eq]
      exact ⟨hu, hc⟩
    have h0 := hKS (Q * g * Qᴴ) hk x hx
    simp only [hinv, he] at h0
    exact h0
  have hsm : ∀ v ∈ S, R.KFin v ∧ v ∈ R.sm := by
    intro v hv
    have hkf : R.KFin v := by
      simp only [BranchingSupport.Rep.KFin, PI.UpqRep.IsKFinHpk]
      exact ⟨S, hfin, hv, hS'⟩
    exact ⟨hkf, hTKsm v (hKTK v hkf)⟩
  refine ⟨hsm, fun a b hab v hv => ?_⟩
  have h1 : (Hpk k r)ᴴ = Hpk k r := by
    rw [← hcay, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, Jm_conjTranspose]
    simp only [Matrix.mul_assoc]
  have h2 : Hpk k r * Hpk k r = 1 := by
    rw [← hcay]
    calc Qᴴ * Jm ε * Q * (Qᴴ * Jm ε * Q) = Qᴴ * Jm ε * (Q * Qᴴ) * Jm ε * Q := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by
          rw [q2, Matrix.mul_one, Matrix.mul_assoc (Qᴴ) (Jm ε), Jm_mul_self, Matrix.mul_one, q1]
  have hc : Hpk k r * (Q⁻¹ * Matrix.single a b 1 * Q) = (Q⁻¹ * Matrix.single a b 1 * Q) * Hpk k r := by
    rw [hinv, ← hcay]
    calc Qᴴ * Jm ε * Q * (Qᴴ * Matrix.single a b 1 * Q)
        = Qᴴ * Jm ε * (Q * Qᴴ) * Matrix.single a b 1 * Q := by simp only [Matrix.mul_assoc]
      _ = Qᴴ * (Jm ε * Matrix.single a b 1) * Q := by
          rw [q2, Matrix.mul_one]
          simp only [Matrix.mul_assoc]
      _ = Qᴴ * (Matrix.single a b 1 * Jm ε) * Q := by rw [Jm_single ε hab]
      _ = Qᴴ * Matrix.single a b 1 * (Q * Qᴴ) * Jm ε * Q := by
          rw [q2, Matrix.mul_one]
          simp only [Matrix.mul_assoc]
      _ = Qᴴ * Matrix.single a b 1 * Q * (Qᴴ * Jm ε * Q) := by simp only [Matrix.mul_assoc]
  exact dC_mem R S hS' h1 h2 hc hv (hsm v hv).2

end GlobalTheory.CompactStable
