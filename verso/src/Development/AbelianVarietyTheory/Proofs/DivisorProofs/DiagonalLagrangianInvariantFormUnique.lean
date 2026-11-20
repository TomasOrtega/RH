import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReindexDblIncM
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LagrInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicStoneVonNeumannLagrangianUniqueness
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagLagrangian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LagrIntRhoInv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormAdelicThetaSumSchroedingerRationalPairInvari
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HTensDiagEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixMemSpanIncM
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralNeZeroOfCocompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaReNonneg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdmittedEqDiagonalLagrangianThetaIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

namespace GlobalTheory.LagrUniq

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B hB nS nT JT JB ξ κ _ co hco ν 𝓕 hν h𝓕`. Establish `hstd : IsStd B.ψ` using `hB.std`. Use `haveI : IsModuleTopology (AF F) (WOF F E nS nT) := inferInstanceAs (IsModuleTopology (AF F) (Fin nT → Fin nS → AF F ⊗[F] E))`. Use `set C : Matrix (Fin (nT + nT)) (Fin nT) (AF F ⊗[F] E) := (diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id with hC`. Use `set C₀ : Matrix (Fin (nT + nT)) (Fin nT) E := (diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) E).submatrix finSumFinEquiv.symm id with hC₀`.

Establish `hCC : C = incM F C₀`. Use extensionality with `i j`. Take `⟨i, rfl⟩` from `finSumFinEquiv.surjective i`. Apply the tactic sequence `rcases i with i | i <;> by_cases h : i = j <;>`. Simplify using `only [hC, hC₀, incM, diagCols, Matrix.submatrix_apply, Matrix.map_apply, Equiv.symm_apply_apply, id, Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr, Matrix.one_apply, h, if_true, if_false, map_one, map_zero]`.

Set `mC : WOF F E nS nT →ₗ[AF F] Matrix (Fin (nT + nT)) (Fin nS) (AF F ⊗[F] E)` to `{ toFun := fun u => C * u map_add' := fun u v => Matrix.mul_add _ _ _ map_smul' := fun t u => Matrix.mul_smul _ _ _ }`. Set `Lm : WOF F E nS nT →ₗ[AF F] (κ → AF F) × (κ → AF F)` to `co.e.toLinearMap ∘ₗ mC`. Establish `hLm : ∀ u, Lm u = co.e (C * u)` using `fun u => rfl`. Set `S` to `LinearMap.range Lm`. Establish `hiso : ∀ s ∈ S, ∀ s' ∈ S, s.1 ⬝ᵥ s'.2 = s'.1 ⬝ᵥ s.2`.

Introduce and unpack `_ ⟨u, rfl⟩ _ ⟨u', rfl⟩`. Establish `h` using `co.form (C * u) (C * u')`. Rewrite `h` using `[GlobalTheory.WeilDiagIso.symp_diag_eq_zero F E σ nS nT JT JB ξ u u']`. Rewrite using `[hLm, hLm]`. Conclude with `(sub_eq_zero.mp h.symm)`.

Establish `hrat : ∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F, Lm (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))`. Introduce `x`. Establish `e : C * incM F x = incM F (C₀ * x)`. Rewrite using `[hCC]`. Simplify using `only [incM]`.

Conclude with `(Matrix.map_mul (f := (inclR (F := F) (AF F) : E →+* AF F ⊗[F] E))).symm`. Take `⟨y, z, h⟩` from `hco (C₀ * x)`. Conclude with `⟨y, z, by rw [hLm, e, h]⟩`. Establish `hspan : S ≤ Submodule.span (AF F) {s | s ∈ S ∧ ∃ y z : κ → F, s = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))}`. Introduce and unpack `_ ⟨u, rfl⟩`.

Establish `hu` using `Submodule.mem_map_of_mem (f := Lm) (GlobalTheory.matrix_mem_span_incM F E nT nS u)`. Rewrite `hu` using `[Submodule.map_span]`. Use `Submodule.span_mono ?_ hu` and prove the remaining obligations. Introduce and unpack `_ ⟨_, ⟨x, rfl⟩, rfl⟩`. Take `⟨y, z, h⟩` from `hrat x`.

Conclude with `⟨⟨incM F x, rfl⟩, y, z, h⟩`. Take `⟨Φ, hΦ, hcont, hre, hre0⟩` from `GlobalTheory.ThetaPosIso.exists_theta_re_nonneg F B.ψ hstd κ S hiso hspan`. Use `⟨Φ, hΦ, ?_⟩` and prove the remaining obligations. Establish `hI : ∀ u : WOF F E nS nT, GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ Φ (C * u) = thetaSum F (schr B.ψ (Lm u) Φ)` using `fun u => rfl`. Use `show ∫ u in 𝓕, GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ Φ (C * u) ∂ν ≠ 0`.

Repeatedly rewrite using `[hI]`. Use `GlobalTheory.PeriodicPositiveIntegral.integral_ne_zero F E nS nT (fun u => thetaSum F (schr B.ψ (Lm u) Φ)) ?_ ?_ ?_ ?_ ν 𝓕 hν h𝓕` and prove the remaining obligations. Conclude with `hcont.comp (IsModuleTopology.continuous_of_linearMap Lm)`. Introduce and unpack `_ ⟨γ₀, rfl⟩ u`. Take `⟨y, z, h⟩` from `hrat γ₀`.

Establish `e1 : Lm (((incAF F E).toAddMonoidHom.mapMatrix (m` using `Fin nT) (n := Fin nS)) γ₀ + u) = Lm (incM F γ₀) + Lm u := by`. Rewrite using `[map_add]`. Both sides reduce to the same expression. Establish `hr : Lm (incM F γ₀) ∈ S` using `⟨incM F γ₀, rfl⟩`. Establish `hw : Lm u ∈ S` using `⟨u, rfl⟩`.

Establish `hi` using `hiso _ hw _ hr`. Rewrite `hi` using `[h]`. Use `show thetaSum F (schr B.ψ (Lm (_ + u)) Φ) = _`. Rewrite using `[e1, h, GlobalTheory.ThetaRatInv.thetaSum_schr_rat_add B.ψ hstd.2.1 Φ y z (Lm u), hi, sub_self, mul_zero, AddChar.map_zero_eq_one, one_mul]`. Introduce `u`.

Conclude with `hre _ ⟨u, rfl⟩`. Use `show 0 < (thetaSum F (schr B.ψ (Lm 0) Φ)).re`. Rewrite using `[map_zero]`. Conclude with `hre0`.
-/
theorem exists_lagrInt_ne_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JT : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E)
      (κ : Type) [Fintype κ]
      (co : Darboux (symp (cA σ) ξ (incM F (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)ᵀ) (incM F JB)) κ),
      (∀ x : Matrix (Fin (nT + nT)) (Fin nS) E, ∃ y z : κ → F,
        co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
      ∀ (ν : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), ν.IsAddHaarMeasure →
        IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν →
      ∃ φ ∈ schA F κ, GlobalTheory.LagrTheta.lagrInt ν 𝓕 ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) (GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ φ) ≠ 0 := by
  intro F E _ _ _ _ _ σ B hB nS nT JT JB ξ κ _ co hco ν 𝓕 hν h𝓕
  have hstd : IsStd B.ψ := hB.std
  haveI : IsModuleTopology (AF F) (WOF F E nS nT) :=
    inferInstanceAs (IsModuleTopology (AF F) (Fin nT → Fin nS → AF F ⊗[F] E))
  set C : Matrix (Fin (nT + nT)) (Fin nT) (AF F ⊗[F] E) :=
    (diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id with hC
  set C₀ : Matrix (Fin (nT + nT)) (Fin nT) E :=
    (diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) E).submatrix finSumFinEquiv.symm id with hC₀
  have hCC : C = incM F C₀ := by
    ext i j
    obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
    rcases i with i | i <;> by_cases h : i = j <;>
      simp only [hC, hC₀, incM, diagCols, Matrix.submatrix_apply, Matrix.map_apply, Equiv.symm_apply_apply, id,
        Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr, Matrix.one_apply, h, if_true, if_false, map_one, map_zero]
  let mC : WOF F E nS nT →ₗ[AF F] Matrix (Fin (nT + nT)) (Fin nS) (AF F ⊗[F] E) :=
    { toFun := fun u => C * u
      map_add' := fun u v => Matrix.mul_add _ _ _
      map_smul' := fun t u => Matrix.mul_smul _ _ _ }
  let Lm : WOF F E nS nT →ₗ[AF F] (κ → AF F) × (κ → AF F) := co.e.toLinearMap ∘ₗ mC
  have hLm : ∀ u, Lm u = co.e (C * u) := fun u => rfl
  let S := LinearMap.range Lm
  have hiso : ∀ s ∈ S, ∀ s' ∈ S, s.1 ⬝ᵥ s'.2 = s'.1 ⬝ᵥ s.2 := by
    rintro _ ⟨u, rfl⟩ _ ⟨u', rfl⟩
    have h := co.form (C * u) (C * u')
    rw [GlobalTheory.WeilDiagIso.symp_diag_eq_zero F E σ nS nT JT JB ξ u u'] at h
    rw [hLm, hLm]
    exact (sub_eq_zero.mp h.symm)
  have hrat : ∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
      Lm (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i)) := by
    intro x
    have e : C * incM F x = incM F (C₀ * x) := by
      rw [hCC]
      simp only [incM]
      exact (Matrix.map_mul (f := (inclR (F := F) (AF F) : E →+* AF F ⊗[F] E))).symm
    obtain ⟨y, z, h⟩ := hco (C₀ * x)
    exact ⟨y, z, by rw [hLm, e, h]⟩
  have hspan : S ≤ Submodule.span (AF F) {s | s ∈ S ∧ ∃ y z : κ → F,
      s = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))} := by
    rintro _ ⟨u, rfl⟩
    have hu := Submodule.mem_map_of_mem (f := Lm) (GlobalTheory.matrix_mem_span_incM F E nT nS u)
    rw [Submodule.map_span] at hu
    refine Submodule.span_mono ?_ hu
    rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    obtain ⟨y, z, h⟩ := hrat x
    exact ⟨⟨incM F x, rfl⟩, y, z, h⟩
  obtain ⟨Φ, hΦ, hcont, hre, hre0⟩ := GlobalTheory.ThetaPosIso.exists_theta_re_nonneg F B.ψ hstd κ S hiso hspan
  refine ⟨Φ, hΦ, ?_⟩
  have hI : ∀ u : WOF F E nS nT, GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ Φ (C * u) = thetaSum F (schr B.ψ (Lm u) Φ) :=
    fun u => rfl
  show ∫ u in 𝓕, GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ Φ (C * u) ∂ν ≠ 0
  simp_rw [hI]
  refine GlobalTheory.PeriodicPositiveIntegral.integral_ne_zero F E nS nT (fun u => thetaSum F (schr B.ψ (Lm u) Φ)) ?_ ?_ ?_ ?_ ν 𝓕 hν h𝓕
  · exact hcont.comp (IsModuleTopology.continuous_of_linearMap Lm)
  · rintro _ ⟨γ₀, rfl⟩ u
    obtain ⟨y, z, h⟩ := hrat γ₀
    have e1 : Lm (((incAF F E).toAddMonoidHom.mapMatrix (m := Fin nT) (n := Fin nS)) γ₀ + u) = Lm (incM F γ₀) + Lm u := by
      rw [map_add]; rfl
    have hr : Lm (incM F γ₀) ∈ S := ⟨incM F γ₀, rfl⟩
    have hw : Lm u ∈ S := ⟨u, rfl⟩
    have hi := hiso _ hw _ hr
    rw [h] at hi
    show thetaSum F (schr B.ψ (Lm (_ + u)) Φ) = _
    rw [e1, h, GlobalTheory.ThetaRatInv.thetaSum_schr_rat_add B.ψ hstd.2.1 Φ y z (Lm u), hi, sub_self, mul_zero,
      AddChar.map_zero_eq_one, one_mul]
  · intro u; exact hre _ ⟨u, rfl⟩
  · show 0 < (thetaSum F (schr B.ψ (Lm 0) Φ)).re
    rw [map_zero]; exact hre0

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ₀ hσξ₀ JB ξ hξ κ _ co hco ν 𝓕 hν h𝓕 l hl hinv`. Establish `hstd : IsStd B.ψ` using `hB.std`. Take `⟨L, hiso, hdim, hL⟩` from `GlobalTheory.WeilSchrodinger.DiagLagr.exists_diag_lagrangian F E σ nS nT JT JB ξ κ co hco`. Take `⟨l₂, hl₂, he⟩` from `GlobalTheory.LagrThetaAdm.exists_admitted_eq_diagonalLagrangian_thetaIntegral_alt F E σ B hB nS nT JT JB ξ κ co hco ν 𝓕 hν h𝓕`. Take `⟨φ₀, hφ₀, hne⟩` from `exists_lagrInt_ne_zero F E σ B hB nS nT JT JB ξ κ co hco ν 𝓕 hν h𝓕`.

Establish `hrho : ∀ (u : Matrix (Fin nT) (Fin nS) (AF F ⊗[F] E)) (φ : (κ → AF F) → ℂ), (GlobalTheory.WeilSchrodinger.transD (cA σ) co).rho B.ψ (uᵀ * ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id)ᵀ) φ = co.rho B.ψ (((diagCols (Fin nT) …`. Introduce `u φ`. Rewrite using `[GlobalTheory.WeilSchrodinger.transD_rho, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_transpose]`. Establish `hmem : ∀ w, ∀ φ ∈ schA F κ, co.rho B.ψ w φ ∈ schA F κ` using `fun w φ hφ => GlobalTheory.HeisSchA.schr_mem_schA B.ψ hstd _ φ hφ`. Establish `key : ∀ l' : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ, (∀ (u : Matrix (Fin nT) (Fin nS) (AF F ⊗[F] E)), ∀ φ ∈ schA F κ, l' (co.rho B.ψ (((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) * u) φ) = l' φ) → ∀ (t : AF F), ∀ w ∈ L, ∀ φ ∈ schA F κ …`.

Introduce `l' h t w hw φ hφ`. Take `⟨u, hu⟩` from `hL t w hw`. Rewrite using `[← hu]`. Conclude with `h u φ hφ`. Take `⟨c, hc⟩` from `GlobalTheory.AdelicSvN.main F B.ψ hstd κ L hiso hdim l hl l₂ hl₂ (key l (fun u φ hφ => by rw [← hrho]; exact hinv _ φ hφ)) (key l₂ (fun u φ hφ => by`.

Rewrite using `[he _ (hmem _ φ hφ), he φ hφ]`. Conclude with `GlobalTheory.LagrThetaInv.lagrInt_rho_inv F E σ B hB nS nT JT JB ξ κ co hco ν 𝓕 hν h𝓕 u φ hφ))`. Use the proof step `⟨φ₀, hφ₀, by rw [he φ₀ hφ₀]; exact hne⟩`. Conclude with `⟨c, fun Φ hΦ => by rw [hc Φ hΦ, he Φ hΦ]⟩`.
-/
theorem lagr_invariant_unique : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
      ∀ (κ : Type) [Fintype κ]
        (co : Darboux (symp (cA σ) ξ (incM F (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)ᵀ) (incM F JB)) κ),
        (∀ x : Matrix (Fin (nT + nT)) (Fin nS) E, ∃ y z : κ → F,
          co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
      ∀ (ν : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), ν.IsAddHaarMeasure →
        IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν →
      ∀ l ∈ (adeleClass F).adm κ,
        (∀ z : Matrix (Fin nS) (Fin nT) (AF F ⊗[F] E), ∀ φ ∈ schA F κ,
          l ((GlobalTheory.WeilSchrodinger.transD (cA σ) co).rho B.ψ (z * ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id)ᵀ) φ) = l φ) →
        ∃ c : ℂ, ∀ Φ ∈ schA F κ, l Φ = c * GlobalTheory.LagrTheta.lagrInt ν 𝓕 ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) (GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ Φ) := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ₀ hσξ₀ JB ξ hξ κ _ co hco ν 𝓕 hν h𝓕 l hl hinv
  have hstd : IsStd B.ψ := hB.std
  obtain ⟨L, hiso, hdim, hL⟩ := GlobalTheory.WeilSchrodinger.DiagLagr.exists_diag_lagrangian F E σ nS nT JT JB ξ κ co hco
  obtain ⟨l₂, hl₂, he⟩ := GlobalTheory.LagrThetaAdm.exists_admitted_eq_diagonalLagrangian_thetaIntegral_alt F E σ B hB nS nT JT JB ξ κ co hco ν 𝓕 hν h𝓕
  obtain ⟨φ₀, hφ₀, hne⟩ := exists_lagrInt_ne_zero F E σ B hB nS nT JT JB ξ κ co hco ν 𝓕 hν h𝓕
  have hrho : ∀ (u : Matrix (Fin nT) (Fin nS) (AF F ⊗[F] E)) (φ : (κ → AF F) → ℂ),
      (GlobalTheory.WeilSchrodinger.transD (cA σ) co).rho B.ψ (uᵀ * ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id)ᵀ) φ = co.rho B.ψ (((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) * u) φ := by
    intro u φ
    rw [GlobalTheory.WeilSchrodinger.transD_rho, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_transpose]
  have hmem : ∀ w, ∀ φ ∈ schA F κ, co.rho B.ψ w φ ∈ schA F κ := fun w φ hφ =>
    GlobalTheory.HeisSchA.schr_mem_schA B.ψ hstd _ φ hφ
  have key : ∀ l' : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ,
      (∀ (u : Matrix (Fin nT) (Fin nS) (AF F ⊗[F] E)), ∀ φ ∈ schA F κ, l' (co.rho B.ψ (((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) * u) φ) = l' φ) →
      ∀ (t : AF F), ∀ w ∈ L, ∀ φ ∈ schA F κ,
        l' (schr B.ψ (t • ((fun i => algebraMap F (AF F) (w.1 i)), (fun i => algebraMap F (AF F) (w.2 i)))) φ) = l' φ := by
    intro l' h t w hw φ hφ
    obtain ⟨u, hu⟩ := hL t w hw
    rw [← hu]
    exact h u φ hφ
  obtain ⟨c, hc⟩ := GlobalTheory.AdelicSvN.main F B.ψ hstd κ L hiso hdim l hl l₂ hl₂
    (key l (fun u φ hφ => by rw [← hrho]; exact hinv _ φ hφ))
    (key l₂ (fun u φ hφ => by
      rw [he _ (hmem _ φ hφ), he φ hφ]
      exact GlobalTheory.LagrThetaInv.lagrInt_rho_inv F E σ B hB nS nT JT JB ξ κ co hco ν 𝓕 hν h𝓕 u φ hφ))
    ⟨φ₀, hφ₀, by rw [he φ₀ hφ₀]; exact hne⟩
  exact ⟨c, fun Φ hΦ => by rw [hc Φ hΦ, he Φ hΦ]⟩

end GlobalTheory.LagrUniq
