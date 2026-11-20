import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorPureTensorComponentAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSeriesFactorizableRestrictionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKernelArchimedeanUnipotentSupportStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSeriesFactorizableRestrictionFiniteStatement
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

noncomputable section
open Matrix
namespace GlobalTheory.VacScalar

/- English proof (translation)
Simplify using `only [hTens, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]`. Use `conv_lhs => rw [Finset.sum_comm]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Use `conv_lhs => rw [Finset.sum_comm]`. Use `conv_lhs => arg 2`.

Use extensionality with `k`. Rewrite using `[Finset.sum_comm]`. Use `conv_lhs => rw [Finset.sum_comm]`. Use `Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hTens_eq_trace {R E : Type} [CommRing R] [CommRing E] [Algebra R E] (c : E →ₐ[R] E) {α β : Type} [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] (JA : Matrix α α E) (JB : Matrix β β E) (x y : Matrix α β E) :
    hTens c JA JB x y = Matrix.trace (xᵀ * JA * y.map c * JBᵀ) := by
  simp only [hTens, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Finset.sum_mul]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  conv_lhs => rw [Finset.sum_comm]
  conv_lhs => arg 2; ext k; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
  ring

/- English proof (translation)
Rewrite using `[hTens_eq_trace, hTens_eq_trace]`. Establish `e1 : (A * y * Bmᵀ).map c = A.map c * y.map c * (Bm.map c)ᵀ`. Rewrite using `[show (A * y * Bmᵀ).map c = (A * y).map c * (Bmᵀ).map c from Matrix.map_mul (f := c.toRingHom), show (A * y).map c = A.map c * y.map c from Matrix.map_mul (f := c.toRingHom), Matrix.transpose_map]`. Establish `e2 : (Bm.map c)ᵀ * JBᵀ * Bm = JBᵀ` using `by conv_rhs => rw [← hB]`. Rewrite using `[Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]`.

Rewrite using `[e1, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`. Use `_ = Matrix.trace (xᵀ * JA * y.map c * ((Bm.map c)ᵀ * JBᵀ) * Bm) := by rw [hA, Matrix.trace_mul_comm]`. Use `_ = Matrix.trace (xᵀ * JA * y.map c * JBᵀ) := by rw [Matrix.mul_assoc _ _ Bm, e2]`.
-/
theorem hTens_act {R E : Type} [CommRing R] [CommRing E] [Algebra R E] (c : E →ₐ[R] E) {α β : Type} [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] (JA : Matrix α α E) (JB : Matrix β β E) (A : Matrix α α E)
    (Bm : Matrix β β E) (hA : Aᵀ * JA * A.map c = JA) (hB : Bmᵀ * JB * Bm.map c = JB) (x y : Matrix α β E) :
    hTens c JA JB (A * x * Bmᵀ) (A * y * Bmᵀ) = hTens c JA JB x y := by
  rw [hTens_eq_trace, hTens_eq_trace]
  have e1 : (A * y * Bmᵀ).map c = A.map c * y.map c * (Bm.map c)ᵀ := by
    rw [show (A * y * Bmᵀ).map c = (A * y).map c * (Bmᵀ).map c from Matrix.map_mul (f := c.toRingHom),
      show (A * y).map c = A.map c * y.map c from Matrix.map_mul (f := c.toRingHom), Matrix.transpose_map]
  have e2 : (Bm.map c)ᵀ * JBᵀ * Bm = JBᵀ := by
    conv_rhs => rw [← hB]
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  rw [e1, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose]
  calc _ = Matrix.trace (Bm * (xᵀ * (Aᵀ * JA * A.map c) * y.map c * ((Bm.map c)ᵀ * JBᵀ))) := by
        simp only [Matrix.mul_assoc]
    _ = Matrix.trace (xᵀ * JA * y.map c * ((Bm.map c)ᵀ * JBᵀ) * Bm) := by rw [hA, Matrix.trace_mul_comm]
    _ = Matrix.trace (xᵀ * JA * y.map c * JBᵀ) := by rw [Matrix.mul_assoc _ _ Bm, e2]

/- English proof (translation)
Simplify using `only [symp, actAB]`. Rewrite using `[hTens_act c JA JB _ _ k.1.2 k.2.2]`.
-/
theorem symp_act {R E : Type} [CommRing R] [CommRing E] [Algebra R E] (c : E →ₐ[R] E) {α β : Type} [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] (ξ : E) (JA : Matrix α α E) (JB : Matrix β β E)
    (k : UG c JA × UG c JB) (x : Matrix α β E) :
    symp c ξ JA JB (actAB c k x) (actAB c k x) = symp c ξ JA JB x x := by
  simp only [symp, actAB]
  rw [hTens_act c JA JB _ _ k.1.2 k.2.2]

open Classical in

/- English proof (translation)
Use function extensionality and compare the values at `x`. Establish `h1` using `GlobalTheory.PureFactor.finprod_update φ w (c • φ w) hstd x`. Establish `h2` using `GlobalTheory.PureFactor.finprod_update φ w (φ w) hstd x`. Rewrite `h2` using `[Function.update_eq_self]`. Simplify using `only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, Pi.smul_apply, smul_eq_mul]`.

Rewrite using `[h1, h2]`. Simplify using `only [Pi.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem pure_update_smul {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (f : SInf F κ)
    (φ : ∀ w : Pl F, (κ → Fv F w) → ℂ)
    (hstd : ∀ᶠ v in Filter.cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) (w : Pl F)
    (c : ℂ) : pure f (Function.update φ w (c • φ w)) = c • pure f φ := by
  funext x
  have h1 := GlobalTheory.PureFactor.finprod_update φ w (c • φ w) hstd x
  have h2 := GlobalTheory.PureFactor.finprod_update φ w (φ w) hstd x
  rw [Function.update_eq_self] at h2
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, Pi.smul_apply, smul_eq_mul]
  rw [h1, h2]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/- English proof (translation)
Use `filter_upwards [hG.hM'.std, S.finite_toSet.compl_mem_cofinite] with v hv hvS`. Rewrite using `[hvac v hvS, hv]`.
-/
theorem std_of_vac {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {B : Base F E} {a a' : ℕ} {G : Geo σ a a'} (hG : G.IsGood B) (S : Finset (Pl F))
    (φ : ∀ w : Pl F, (Fin a' × Fin (a + a') → Fv F w) → ℂ) (hvac : ∀ w, w ∉ S → φ w = G.M'.vac w) :
    ∀ᶠ v in Filter.cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 := by
  filter_upwards [hG.hM'.std, S.finite_toSet.compl_mem_cofinite] with v hv hvS
  rw [hvac v hvS, hv]

/- English proof (translation)
Take `⟨-, -, θ, -, hθ⟩` from `hT.geo.hM'.vac w`. Use `⟨θ, fun γ hγ => ?_⟩` and prove the remaining obligations. Establish `hstd` using `std_of_vac hT.geo S φ hvac`. Establish `hΦ` using `GlobalTheory.TensUniq.pure_mem_schA f φ hSB hstd`. Establish `e` using `GlobalTheory.ThK.LocalOps.acts_pure w (G.M'.co.rho B.ψ γ) f φ _ hΦ (fun x => GlobalTheory.PureFactor.mulSupport_finite φ hstd x) (by rw [hvac w hw]; exact hθ γ hγ)`.

Rewrite using `[e, ← hvac w hw, pure_update_smul f φ hstd]`.
-/
theorem pure_eigen {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {B : Base F E} {a a' : ℕ} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}
    (hT : IsTriple B G X om om') (S : Finset (Pl F)) (f : SInf F (Fin a' × Fin (a + a')))
    (φ : ∀ w : Pl F, (Fin a' × Fin (a + a') → Fv F w) → ℂ) (hSB : ∀ w, φ w ∈ SB (Fin a' × Fin (a + a') → Fv F w))
    (hvac : ∀ w, w ∉ S → φ w = G.M'.vac w) (w : Pl F) (hw : w ∉ S) :
    ∃ θ : 𝓞 E, ∀ γ ∈ latAtV G.V' G.W w, G.M'.co.rho B.ψ γ (pure f φ) =
      B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V'.J) (incM F G.W.J) γ γ) •
        pure f φ := by
  obtain ⟨-, -, θ, -, hθ⟩ := hT.geo.hM'.vac w
  refine ⟨θ, fun γ hγ => ?_⟩
  have hstd := std_of_vac hT.geo S φ hvac
  have hΦ := GlobalTheory.TensUniq.pure_mem_schA f φ hSB hstd
  have e := GlobalTheory.ThK.LocalOps.acts_pure w (G.M'.co.rho B.ψ γ) f φ _ hΦ
    (fun x => GlobalTheory.PureFactor.mulSupport_finite φ hstd x) (by rw [hvac w hw]; exact hθ γ hγ)
  rw [e, ← hvac w hw, pure_update_smul f φ hstd]

/- English proof (translation)
Introduce `hP F E _ _ _ _ _ σ B a a' G X om om' hT S g h hgI hhI hgS hhS hlat f φ hSB hvac`. Establish `hstd` using `std_of_vac hT.geo S φ hvac`. Establish `hΦ : pure f φ ∈ schA F (Fin a' × Fin (a + a'))` using `GlobalTheory.TensUniq.pure_mem_schA f φ hSB hstd`. Establish `hW` using `IsUWeilPair.isUSplitting hT.weil'`. Establish `hi : ∀ w, w ∉ S → ∀ γ ∈ latAtV G.V' G.W w, ∀ c : ℂ, G.M'.co.rho B.ψ γ (pure f φ) = c • pure f φ → G.M'.co.rho B.ψ γ (om' (g, h) (pure f φ)) = c • om' (g, h) (pure f φ)`.

Introduce `w hw γ hγ c hc`. Take `⟨θ, hθ⟩` from `pure_eigen hT S f φ hSB hvac w hw`. Use `set γ' := actAB (cA σ) ((g, h)⁻¹) γ with hγ'def`. Establish `e1 : mat g * mat g⁻¹ = 1` using `by show (g * g⁻¹).1.1 = 1`. Rewrite using `[mul_inv_cancel]`.

Both sides reduce to the same expression. Establish `e2 : mat h * mat h⁻¹ = 1` using `by show (h * h⁻¹).1.1 = 1`. Rewrite using `[mul_inv_cancel]`. Both sides reduce to the same expression. Establish `hact : actAB (cA σ) (g, h) γ' = γ`.

Express the relevant statement in the definitionally equal form `mat g * (mat g⁻¹ * γ * (mat h⁻¹)ᵀ) * (mat h)ᵀ = γ`. Rewrite using `[← Matrix.mul_assoc, ← Matrix.mul_assoc, e1, Matrix.one_mul, Matrix.mul_assoc, ← Matrix.transpose_mul, e2, Matrix.transpose_one, Matrix.mul_one]`. Establish `hγ' : γ' ∈ latAtV G.V' G.W w` using `(hlat w hw γ').1 (by change actAB (cA σ) (g, h) γ' ∈ _; rw [hact]; exact hγ)`. Establish `e3` using `hW.impl (g, h) γ' (pure f φ) hΦ`. Rewrite `e3` using `[hact]`.

Establish `hsym : symp (cA σ) (inclR (F` using `F) (AF F) (θ : E)) (incM F G.V'.J) (incM F G.W.J) γ' γ' = symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V'.J) (incM F G.W.J) γ γ := by`. Rewrite using `[← symp_act (cA σ) _ _ _ (g, h) γ', hact]`. Rewrite using `[← e3, hθ γ' hγ', map_smul, hsym]`. Distinguish the cases in `hΦ0 : pure f φ = 0`. Rewrite using `[hΦ0, map_zero, smul_zero, smul_zero]`.

Rewrite `hc` using `[hθ γ hγ]`. Rewrite using `[smul_left_injective ℂ hΦ0 hc]`. Establish `hTΦ : om' (g, h) (pure f φ) ∈ schA F (Fin a' × Fin (a + a'))` using `hW.pres (g, h) _ hΦ`. Take `⟨m, f', φ', hSB', hvac', heq⟩` from `GlobalTheory.T.theta_series_factorizable_restriction hP F E σ B a a' G X om om' hT S f φ hSB hvac _ hTΦ hi`. Establish `hco` using `GlobalTheory.T.theta_kernel_archimedean_unipotent_support F E σ B a a' G X om om' hT S g h hgI hhI hgS hhS (pure f φ) hΦ`.

Take `⟨c, hc⟩` from `GlobalTheory.T.theta_series_factorizable_restriction_finite hP F E σ B a a' G X om om' hT S f φ hSB hvac m f' φ' hSB' hvac' (fun u hu μ hμ => by rw [← heq]; exact hco u hu μ hμ)`. Conclude with `⟨c, heq.trans hc⟩`.
-/
theorem scalar_of_trivial : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (S : Finset (Pl F)) (g : UA σ G.V'.J) (h : UA σ G.W.J),
    (∀ u : AF F, At (evI F) u → u • (mat g - 1) = 0) → (∀ u : AF F, At (evI F) u → u • (mat h - 1) = 0) →
    (∀ w ∈ S, ∀ u : AF F, At (evFin F w) u → u • (mat g - 1) = 0) →
    (∀ w ∈ S, ∀ u : AF F, At (evFin F w) u → u • (mat h - 1) = 0) →
    (∀ w, w ∉ S → ∀ γ, (mat g * γ * Matrix.transpose (mat h) ∈ latAtV G.V' G.W w ↔ γ ∈ latAtV G.V' G.W w)) →
    ∀ (f : SInf F (Fin a' × Fin (a + a'))) (φ : ∀ w : Pl F, (Fin a' × Fin (a + a') → Fv F w) → ℂ),
    (∀ w, φ w ∈ SB (Fin a' × Fin (a + a') → Fv F w)) → (∀ w, w ∉ S → φ w = G.M'.vac w) →
    ∃ c : ℂ, om' (g, h) (pure f φ) = c • pure f φ := by
  intro hP F E _ _ _ _ _ σ B a a' G X om om' hT S g h hgI hhI hgS hhS hlat f φ hSB hvac
  have hstd := std_of_vac hT.geo S φ hvac
  have hΦ : pure f φ ∈ schA F (Fin a' × Fin (a + a')) := GlobalTheory.TensUniq.pure_mem_schA f φ hSB hstd
  have hW := IsUWeilPair.isUSplitting hT.weil'
  have hi : ∀ w, w ∉ S → ∀ γ ∈ latAtV G.V' G.W w, ∀ c : ℂ, G.M'.co.rho B.ψ γ (pure f φ) = c • pure f φ →
      G.M'.co.rho B.ψ γ (om' (g, h) (pure f φ)) = c • om' (g, h) (pure f φ) := by
    intro w hw γ hγ c hc
    obtain ⟨θ, hθ⟩ := pure_eigen hT S f φ hSB hvac w hw
    set γ' := actAB (cA σ) ((g, h)⁻¹) γ with hγ'def
    have e1 : mat g * mat g⁻¹ = 1 := by
      show (g * g⁻¹).1.1 = 1
      rw [mul_inv_cancel]; rfl
    have e2 : mat h * mat h⁻¹ = 1 := by
      show (h * h⁻¹).1.1 = 1
      rw [mul_inv_cancel]; rfl
    have hact : actAB (cA σ) (g, h) γ' = γ := by
      change mat g * (mat g⁻¹ * γ * (mat h⁻¹)ᵀ) * (mat h)ᵀ = γ
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, e1, Matrix.one_mul, Matrix.mul_assoc, ← Matrix.transpose_mul, e2,
        Matrix.transpose_one, Matrix.mul_one]
    have hγ' : γ' ∈ latAtV G.V' G.W w := (hlat w hw γ').1 (by change actAB (cA σ) (g, h) γ' ∈ _; rw [hact]; exact hγ)
    have e3 := hW.impl (g, h) γ' (pure f φ) hΦ
    rw [hact] at e3
    have hsym : symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V'.J) (incM F G.W.J) γ' γ' =
        symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V'.J) (incM F G.W.J) γ γ := by
      rw [← symp_act (cA σ) _ _ _ (g, h) γ', hact]
    rw [← e3, hθ γ' hγ', map_smul, hsym]
    by_cases hΦ0 : pure f φ = 0
    · rw [hΦ0, map_zero, smul_zero, smul_zero]
    · rw [hθ γ hγ] at hc
      rw [smul_left_injective ℂ hΦ0 hc]
  have hTΦ : om' (g, h) (pure f φ) ∈ schA F (Fin a' × Fin (a + a')) := hW.pres (g, h) _ hΦ
  obtain ⟨m, f', φ', hSB', hvac', heq⟩ := GlobalTheory.T.theta_series_factorizable_restriction hP F E σ B a a' G X om om' hT S f φ hSB hvac _ hTΦ hi
  have hco := GlobalTheory.T.theta_kernel_archimedean_unipotent_support F E σ B a a' G X om om' hT S g h hgI hhI hgS hhS (pure f φ) hΦ
  obtain ⟨c, hc⟩ := GlobalTheory.T.theta_series_factorizable_restriction_finite hP F E σ B a a' G X om om' hT S f φ hSB hvac m f' φ' hSB' hvac'
    (fun u hu μ hμ => by rw [← heq]; exact hco u hu μ hμ)
  exact ⟨c, heq.trans hc⟩

end GlobalTheory.VacScalar
