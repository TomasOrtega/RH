import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPairOfIsTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqSmulOfCommuteHeisenbergLinearModelSchwartzBruhStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHeisenbergActsByLocalSchrodingerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplementaryAdelicSchwartzRestFunction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitPlaceAdelicMatrixGivenComponentsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicTraceSupportedAtSplitPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianTensorSkewHermitianSplitSymplecticPairStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerPreservesSchwartzBruhat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharacterNontrivialAtPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceSymplecticSelfZeroSplitSupported
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomSuppSplit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianSelfDualLatticeSpaceFormHermitianNondeg
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped GlobalTheory.VacAny GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.UnitWShape

/- English proof (translation)
Use function extensionality and compare the values at `y`. Establish `hz : At (evFin F v) (fun i => GlobalTheory.LatVac.liftV v (y i))`. Introduce `u hu`. Use function extensionality and compare the values at `i`. Conclude with `GlobalTheory.LatVac.at_liftV v _ u hu`.

Establish `e` using `congrFun h (fun i => GlobalTheory.LatVac.liftV v (y i))`. Establish `hR : R (fun i => GlobalTheory.LatVac.liftV v (y i)) = R 0` using `by simpa using hinv 0 _ hz`. Simplify using `only [tens, GlobalTheory.LatVac.evFin_liftV, hR] at e`. Conclude with `mul_right_cancel₀ hR0 e`.
-/
theorem eq_of_tens_eq {F : Type} [Field F] [NumberField F] {κ : Type} (v : Pl F) (R : (κ → AF F) → ℂ)
    (hR0 : R 0 ≠ 0) (hinv : ∀ x z, At (evFin F v) z → R (x + z) = R x) (φ₁ φ₂ : (κ → Fv F v) → ℂ)
    (h : tens (evFin F v) φ₁ R = tens (evFin F v) φ₂ R) : φ₁ = φ₂ := by
  funext y
  have hz : At (evFin F v) (fun i => GlobalTheory.LatVac.liftV v (y i)) := by
    intro u hu
    funext i
    exact GlobalTheory.LatVac.at_liftV v _ u hu
  have e := congrFun h (fun i => GlobalTheory.LatVac.liftV v (y i))
  have hR : R (fun i => GlobalTheory.LatVac.liftV v (y i)) = R 0 := by simpa using hinv 0 _ hz
  simp only [tens, GlobalTheory.LatVac.evFin_liftV, hR] at e
  exact mul_right_cancel₀ hR0 e

/- English proof (translation)
Use function extensionality and compare the values at `z`. Simplify using `only [tens, Pi.add_apply, Pi.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem tens_add_smul {F : Type} [Field F] [NumberField F] {κ : Type} (v : Pl F) (R : (κ → AF F) → ℂ)
    (x y : (κ → Fv F v) → ℂ) (c : ℂ) :
    tens (evFin F v) (c • x + y) R = c • tens (evFin F v) x R + tens (evFin F v) y R := by
  funext z
  simp only [tens, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/- English proof (translation)
Introduce `hP F E _ _ _ _ _ σ B a a' G X om om' hTr v h hh`. Establish `hAE` using `GlobalTheory.T.theta_action_exists hP`. Establish `hPair` using `(GlobalTheory.ThK.Check.isPair_of_isTriple hTr).1`. Establish `h1 : (1 : UA σ G.V.J) ∈ UAt σ G.V (evFin F v)`. Introduce `u _`.

Simplify using `[mat]`. Establish `hex` using `(hAE F E σ B a (a + a') G.V G.W G.M X.β (X.β / X.α) om _ _ _ _ hPair v).1 1 h1 h hh`. Establish `hex' : ∀ φ, ∃ φ₁, φ ∈ SB (Fin a × Fin (a + a') → Fv F v) → φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v) ∧ Acts (evFin F v) (om (1, h)) φ φ₁`. Introduce `φ`. Distinguish the cases in `hφ : φ ∈ SB (Fin a × Fin (a + a') → Fv F v)`.

Take `⟨φ₁, hφ₁, -⟩` from `hex φ hφ`. Conclude with `⟨φ₁, fun _ => hφ₁⟩`. Conclude with `⟨0, fun h' => absurd h' hφ⟩`. Use `choose S hS using hex'`. Take `⟨R, hR0, hR⟩` from `GlobalTheory.RestWitness.exists_rest (Fin a × Fin (a + a')) v`.

Establish `hinv` using `(hR 0 (Submodule.zero_mem _)).1`. Establish `huniq : ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁, Acts (evFin F v) (om (1, h)) φ φ₁ → φ₁ = S φ` using `fun φ hφ φ₁ hA => eq_of_tens_eq v R hR0 hinv φ₁ (S φ) ((hA R (hR φ hφ)).symm.trans ((hS φ hφ).2 R (hR φ hφ)))`. Establish `hW` using `GlobalTheory.WeilM.IsUWeilPair.isUSplitting hTr.weil`. Use `⟨S, fun φ hφ => (hS φ hφ).1, huniq, ?_, ?_⟩` and prove the remaining obligations. Introduce `x hx y hy c`.

Establish `hz : c • x + y ∈ SB (Fin a × Fin (a + a') → Fv F v)` using `add_mem (Submodule.smul_mem _ c hx) hy`. Apply `eq_of_tens_eq v R hR0 hinv` to reduce the goal to its premises. Rewrite using `[← (hS _ hz).2 R (hR _ hz), tens_add_smul, map_add, map_smul, (hS x hx).2 R (hR x hx), (hS y hy).2 R (hR y hy), ← tens_add_smul]`. Introduce `γ hγ φ hφ`. Establish `hact : actAB (cA σ) ((1 : UA σ G.V.J), h) γ = γ * (mat h)ᵀ`.

Simplify using `[actAB, mat]`. Establish `hγ' : At (evFin F v) (actAB (cA σ) ((1 : UA σ G.V.J), h) γ)`. Rewrite using `[hact]`. Introduce `u hu`. Rewrite using `[← Matrix.smul_mul, hγ u hu, Matrix.zero_mul]`.

Establish `hψ₁` using `GlobalTheory.SchrSB.schr_mem_SB B.ψ hTr.base.std.1 v (GlobalTheory.LatVac.locCo G.M.co v γ) φ hφ`. Apply `eq_of_tens_eq v R hR0 hinv` to reduce the goal to its premises. Establish `e1` using `GlobalTheory.T.adelicHeisenberg_acts_by_local_schrodinger G.M.co B.ψ v γ hγ φ R (hR φ hφ)`. Establish `e2` using `hW.impl (1, h) γ _ (hR φ hφ).2`. Rewrite using `[← (hS _ hψ₁).2 R (hR _ hψ₁), ← e1, e2, (hS φ hφ).2 R (hR φ hφ)]`.

Conclude with `GlobalTheory.T.adelicHeisenberg_acts_by_local_schrodinger G.M.co B.ψ v _ hγ' (S φ) R (hR _ (hS φ hφ).1)`.
-/
theorem exists_localOp : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W)
    (om' : Rep σ G.V' G.W), IsTriple B G X om om' → ∀ (v : Pl F), ∀ h ∈ UAt σ G.W (evFin F v),
    ∃ S : ((Fin a × Fin (a + a') → Fv F v) → ℂ) → (Fin a × Fin (a + a') → Fv F v) → ℂ,
      (∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), S φ ∈ SB (Fin a × Fin (a + a') → Fv F v)) ∧
      (∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁, Acts (evFin F v) (om (1, h)) φ φ₁ → φ₁ = S φ) ∧
      (∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ' ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ c : ℂ,
        S (c • φ + φ') = c • S φ + S φ') ∧
      (∀ γ : Matrix (Fin a) (Fin (a + a')) (AE F E), At (evFin F v) γ →
        ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v),
          S (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M.co v γ) φ) =
            schr (GlobalTheory.LatVac.psiAt B.ψ v)
              (GlobalTheory.LatVac.locCo G.M.co v (actAB (cA σ) ((1 : UA σ G.V.J), h) γ)) (S φ)) := by
  intro hP F E _ _ _ _ _ σ B a a' G X om om' hTr v h hh
  have hAE := GlobalTheory.T.theta_action_exists hP
  have hPair := (GlobalTheory.ThK.Check.isPair_of_isTriple hTr).1
  have h1 : (1 : UA σ G.V.J) ∈ UAt σ G.V (evFin F v) := by
    intro u _
    simp [mat]
  have hex := (hAE F E σ B a (a + a') G.V G.W G.M X.β (X.β / X.α) om _ _ _ _ hPair v).1 1 h1 h hh
  have hex' : ∀ φ, ∃ φ₁, φ ∈ SB (Fin a × Fin (a + a') → Fv F v) →
      φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v) ∧ Acts (evFin F v) (om (1, h)) φ φ₁ := by
    intro φ
    by_cases hφ : φ ∈ SB (Fin a × Fin (a + a') → Fv F v)
    · obtain ⟨φ₁, hφ₁, -⟩ := hex φ hφ
      exact ⟨φ₁, fun _ => hφ₁⟩
    · exact ⟨0, fun h' => absurd h' hφ⟩
  choose S hS using hex'
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.RestWitness.exists_rest (Fin a × Fin (a + a')) v
  have hinv := (hR 0 (Submodule.zero_mem _)).1
  have huniq : ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁, Acts (evFin F v) (om (1, h)) φ φ₁ → φ₁ = S φ :=
    fun φ hφ φ₁ hA => eq_of_tens_eq v R hR0 hinv φ₁ (S φ)
      ((hA R (hR φ hφ)).symm.trans ((hS φ hφ).2 R (hR φ hφ)))
  have hW := GlobalTheory.WeilM.IsUWeilPair.isUSplitting hTr.weil
  refine ⟨S, fun φ hφ => (hS φ hφ).1, huniq, ?_, ?_⟩
  · intro x hx y hy c
    have hz : c • x + y ∈ SB (Fin a × Fin (a + a') → Fv F v) := add_mem (Submodule.smul_mem _ c hx) hy
    apply eq_of_tens_eq v R hR0 hinv
    rw [← (hS _ hz).2 R (hR _ hz), tens_add_smul, map_add, map_smul, (hS x hx).2 R (hR x hx),
      (hS y hy).2 R (hR y hy), ← tens_add_smul]
  · intro γ hγ φ hφ
    have hact : actAB (cA σ) ((1 : UA σ G.V.J), h) γ = γ * (mat h)ᵀ := by
      simp [actAB, mat]
    have hγ' : At (evFin F v) (actAB (cA σ) ((1 : UA σ G.V.J), h) γ) := by
      rw [hact]
      intro u hu
      rw [← Matrix.smul_mul, hγ u hu, Matrix.zero_mul]
    have hψ₁ := GlobalTheory.SchrSB.schr_mem_SB B.ψ hTr.base.std.1 v (GlobalTheory.LatVac.locCo G.M.co v γ) φ hφ
    apply eq_of_tens_eq v R hR0 hinv
    have e1 := GlobalTheory.T.adelicHeisenberg_acts_by_local_schrodinger G.M.co B.ψ v γ hγ φ R (hR φ hφ)
    have e2 := hW.impl (1, h) γ _ (hR φ hφ).2
    rw [← (hS _ hψ₁).2 R (hR _ hψ₁), ← e1, e2, (hS φ hφ).2 R (hR φ hφ)]
    exact GlobalTheory.T.adelicHeisenberg_acts_by_local_schrodinger G.M.co B.ψ v _ hγ' (S φ) R (hR _ (hS φ hφ).1)

/- English proof (translation)
Use `conv_lhs => rw [Y.matrix_eq_sum_single]`. Simplify using `only [map_sum]`. Use `Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[show Matrix.single k j (Y k j) = Y k j • Matrix.single k j (1 : K) by`. Rewrite using `[Matrix.smul_single, smul_eq_mul, mul_one], map_smul, smul_eq_mul]`.
-/
theorem linForm_eq {K : Type} [Field K] {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (l : Matrix m n K →ₗ[K] K) (Y : Matrix m n K) :
    l Y = ∑ k, ∑ j, Y k j * l (Matrix.single k j 1) := by
  conv_lhs => rw [Y.matrix_eq_sum_single]
  simp only [map_sum]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
  rw [show Matrix.single k j (Y k j) = Y k j • Matrix.single k j (1 : K) by
    rw [Matrix.smul_single, smul_eq_mul, mul_one], map_smul, smul_eq_mul]

/- English proof (translation)
Simplify using `[Matrix.trace, Matrix.mul_apply]`.
-/
theorem sum_mul_eq_trace {K : Type} [CommRing K] {m n : Type} [Fintype m] [Fintype n] (M P : Matrix m n K) :
    ∑ k, ∑ j, M k j * P k j = (M * Pᵀ).trace := by
  simp [Matrix.trace, Matrix.mul_apply]

/- English proof (translation)
Rewrite using `[sum_mul_eq_trace, sum_mul_eq_trace, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_transpose, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.trace_mul_comm]`. Simplify using `only [Matrix.mul_assoc]`.
-/
theorem pair_mul {K : Type} [CommRing K] {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m m K) (Y P : Matrix m n K) (B : Matrix n n K) :
    ∑ k, ∑ j, (A * Y * B) k j * P k j = ∑ k, ∑ j, Y k j * (Aᵀ * P * Bᵀ) k j := by
  rw [sum_mul_eq_trace, sum_mul_eq_trace, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.transpose_transpose, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

/- English proof (translation)
Rewrite using `[sum_mul_eq_trace, sum_mul_eq_trace, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]`.
-/
theorem pair_mul_transpose {K : Type} [CommRing K] {m n : Type} [Fintype m] [Fintype n] (M P : Matrix m n K)
    (N : Matrix n n K) :
    ∑ k, ∑ j, M k j * (P * Nᵀ) k j = ∑ k, ∑ j, (M * N) k j * P k j := by
  rw [sum_mul_eq_trace, sum_mul_eq_trace, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]

/- English proof (translation)
Introduce `r hr`. Establish `h : ∀ i j, r • x i j = 0` using `fun i j => by`. Use `congrFun (congrFun (hx r hr) i) j` as an intermediate fact. Simplify using `using this`. Rewrite using `[← mul_smul_comm]`.

Unfold `hTens`. Simplify using `only [Finset.smul_sum, ← smul_mul_assoc, h, zero_mul, Finset.sum_const_zero, mul_zero]`.
-/
theorem at_hTens {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {v : Pl F} {m n : ℕ} (JA : Matrix (Fin m) (Fin m) E) (JB : Matrix (Fin n) (Fin n) E)
    (x u : Matrix (Fin m) (Fin n) (AE F E)) (hx : At (evFin F v) x) :
    At (evFin F v) ((-1 : AE F E) * hTens (cA σ) (incM F JA) (incM F JB) x u) := by
  intro r hr
  have h : ∀ i j, r • x i j = 0 := fun i j => by
    have := congrFun (congrFun (hx r hr) i) j
    simpa using this
  rw [← mul_smul_comm]
  unfold hTens
  simp only [Finset.smul_sum, ← smul_mul_assoc, h, zero_mul, Finset.sum_const_zero, mul_zero]

/- English proof (translation)
Take `⟨τ⟩ : Nonempty (E →+* ℂ)` from `inferInstance`. Apply `τ.injective` to reduce the goal to its premises. Rewrite using `[h.2.2.2, h.2.2.2, star_star]`.
-/
theorem sigma_invol {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2, h.2.2.2, star_star]

/- English proof (translation)
Establish `hcm : IsCMExt F E σ` using `hTr.base.cm`. Establish `hstd` using `hTr.base.std`. Use `⟨GlobalTheory.SchrSB.continuous_psiAt _ hstd.1 _, GlobalTheory.PsiNontriv.psiAt_ne_one _ hstd _, ?_⟩` and prove the remaining obligations. Take `⟨w⟩ : Nonempty (InfinitePlace F)` from `inferInstance`. Establish `hdV : G.V.J.det ≠ 0`.

Introduce `h0`. Apply `GlobalTheory.WeilSchrodingerHerm.det_ne_zero_of_hasSig (hTr.geo.hV.sig w)` to reduce the goal to its premises. Establish `e : (G.V.J.map (B.emb w).1).det = (B.emb w).1 G.V.J.det` using `(RingHom.map_det _ _).symm`. Rewrite using `[e, h0, map_zero]`. Establish `hdW : G.W.J.det ≠ 0`.

Introduce `h0`. Apply `GlobalTheory.WeilSchrodingerHerm.det_ne_zero_of_hasSig (hTr.geo.hW.sig w)` to reduce the goal to its premises. Establish `e : (G.W.J.map (B.emb w).1).det = (B.emb w).1 G.W.J.det` using `(RingHom.map_det _ _).symm`. Rewrite using `[Matrix.det_smul, e, h0, map_zero, mul_zero]`. Establish `hss : (t.comp σ).comp σ = t`.

Use extensionality with `x`. Simplify using `only [AlgHom.comp_apply, sigma_invol hcm x]`. Use `set A := G.V.J.map (t.comp σ) with hAdef`. Use `set Bm := (G.W.J.map (t.comp σ))ᵀ with hBdef`. Establish `hA : IsUnit Aᵀ.det`.

Establish `e : A.det = ((t.comp σ : E →ₐ[F] Fv F v) : E →+* Fv F v) G.V.J.det` using `(RingHom.map_det _ _).symm`. Rewrite using `[Matrix.det_transpose, e]`. Conclude with `isUnit_iff_ne_zero.2 fun h0 => hdV (((t.comp σ : E →ₐ[F] Fv F v) : E →+* Fv F v).injective (by rw [map_zero]; exact h0))`. Establish `hB : IsUnit Bmᵀ.det`. Establish `e : (G.W.J.map (t.comp σ)).det = ((t.comp σ : E →ₐ[F] Fv F v) : E →+* Fv F v) G.W.J.det` using `(RingHom.map_det _ _).symm`.

Rewrite using `[hBdef, Matrix.transpose_transpose, e]`. Conclude with `isUnit_iff_ne_zero.2 fun h0 => hdW (((t.comp σ : E →ₐ[F] Fv F v) : E →+* Fv F v).injective (by rw [map_zero]; exact h0))`. Use `choose U hUat hU0 hU1 using fun (P₀ P₁ : Matrix (Fin a) (Fin (a + a')) (Fv F v)) => GlobalTheory.T.exists_splitPlace_adelicMatrix_given_components hcm v t P₀ P₁`. Establish `hsymp : ∀ x u : Matrix (Fin a) (Fin (a + a')) (AE F E), At (evFin F v) x → x.map (piW (t.comp σ)) = 0 → u.map (piW t) = 0 → B.ψ (symp (R` using `AF F) (cA σ) (-1) (incM F G.V.J) (incM F G.W.J) x u) = GlobalTheory.LatVac.psiAt B.ψ v (∑ k, ∑ j, (A * x.map (piW t) * Bm) k j * u.map (piW (t.comp σ)) k j) := by`. Introduce `x u hx hx0 hu1`.

Unfold `symp`. Rewrite using `[GlobalTheory.T.adelicTrace_supportedAtSplitPlace hcm v (t.comp σ) _ (at_hTens _ _ x u hx)]`. Rewrite using `[map_mul, map_mul, map_neg, map_neg, map_one, map_one, neg_one_mul, neg_one_mul, ← neg_add, GlobalTheory.T.hermitianTensor_skewHermitian_split_symplectic_pair hcm (t.comp σ) G.V.J G.W.J hTr.geo.hV.herm hTr.geo.hW.skew x u hx0 (by rw [hss]; exact hu1), hss]`. Use `show GlobalTheory.LatVac.psiAt B.ψ v _ = _`. Use `congr 1`.

Simplify using `only [hAdef, hBdef, Matrix.neg_apply, neg_mul, Finset.sum_neg_distrib, neg_neg]`. Set `Lm : (Matrix (Fin a) (Fin (a + a')) (Fv F v) →ₗ[Fv F v] Fv F v) → Matrix (Fin a) (Fin (a + a')) (Fv F v)` to `fun l => Matrix.of fun k j => l (Matrix.single k j 1)`. Set `Pm : (Matrix (Fin a) (Fin (a + a')) (Fv F v) →ₗ[Fv F v] Fv F v) → Matrix (Fin a) (Fin (a + a')) (Fv F v)` to `fun l => (Aᵀ)⁻¹ * Lm l * (Bmᵀ)⁻¹`. Establish `hpair : ∀ l Y, ∑ k, ∑ j, (A * Y * Bm) k j * Pm l k j = l Y`. Introduce `l Y`.

Rewrite using `[pair_mul, linForm_eq l Y]`. Establish `e : Aᵀ * Pm l * Bmᵀ = Lm l`. Simplify using `only [Pm]`. Rewrite using `[Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_right _ _ hB, Matrix.mul_nonsing_inv_cancel_left _ _ hA]`. Rewrite using `[e]`.

Both sides reduce to the same expression. Establish `hunit : ((mat h).map (piW t))ᵀ * Bm * (mat h).map (piW (t.comp σ)) = Bm`. Establish `hu : (mat h)ᵀ * incM F G.W.J * (mat h).map (cA σ) = incM F G.W.J` using `h.2`. Establish `e` using `congrArg (fun M => M.map (piW (t.comp σ))) hu`. Simplify using `only [Matrix.map_mul] at e`.

Establish `hJ : (incM F G.W.J).map (piW (t.comp σ)) = G.W.J.map (t.comp σ)`. Use extensionality with `i j`. Simplify using `[incM, GlobalTheory.SplitGLLift.piW_inclR]`. Establish `hc : ((mat h).map (cA σ)).map (piW (t.comp σ)) = (mat h).map (piW t)`. Use extensionality with `i j`.

Simplify using `only [Matrix.map_apply]`. Rewrite using `[GlobalTheory.VacIso.piW_cA, hss]`. Rewrite `e` using `[hJ, hc, Matrix.transpose_map]`. Establish `e2` using `congrArg Matrix.transpose e`. Simplify using `only [Matrix.transpose_mul, Matrix.transpose_transpose] at e2`.

Rewrite using `[hBdef]`. Simplify `e2` using `only [Matrix.mul_assoc]`. Use `⟨fun C => GlobalTheory.LatVac.locCo G.M.co v (U C 0), fun l => GlobalTheory.LatVac.locCo G.M.co v (U 0 (Pm l)), ?_⟩` and prove the remaining obligations. Introduce `ι hι`. Establish `hL` using `hι`.

Unfold `GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model.IsLinW at hL`. Simplify using `only [inv_one, Units.val_one, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one] at hL`. Establish `htr` using `hL.trans`. Establish `hmu` using `hL.mult`. Establish `hbr` using `fun (γ : Matrix (Fin a) (Fin (a + a')) (AE F E)) hγ (φ : (Fin a × Fin (a + a') → Fv F v) → ℂ) => GlobalTheory.T.adelicHeisenberg_acts_by_local_schrodinger G.M.co B.ψ v γ hγ φ`.

Establish `hsb` using `fun (w : (Fin a × Fin (a + a') → Fv F v) × (Fin a × Fin (a + a') → Fv F v)) (φ : (Fin a × Fin (a + a') → Fv F v) → ℂ) (hφ : φ ∈ SB _) => GlobalTheory.SchrSB.schr_mem_SB B.ψ hstd.1 v w φ hφ`. Establish `hact : ∀ u : Matrix (Fin a) (Fin (a + a')) (AE F E), actAB (cA σ) ((1 : UA σ G.V.J), h) u = u * (mat h)ᵀ`. Introduce `u`. Simplify using `[actAB, mat]`. Establish `hat : ∀ u : Matrix (Fin a) (Fin (a + a')) (AE F E), At (evFin F v) u → At (evFin F v) (u * (mat h)ᵀ)`.

Introduce `u hu r hr`. Rewrite using `[← Matrix.smul_mul, hu r hr, Matrix.zero_mul]`. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `C φ hφ`. Use function extensionality and compare the values at `Y`.

Rewrite using `[htr (U C 0) (hUat C 0) (hU1 C 0) φ hφ _ (hsb _ φ hφ) (hbr _ (hUat C 0) φ) Y, hU0]`. Introduce `l φ hφ`. Use function extensionality and compare the values at `Y`. Establish `hm` using `hmu (U 0 (Pm l)) (hUat _ _) (hU0 0 (Pm l)) φ hφ _ (hsb _ φ hφ) (hbr _ (hUat _ _) φ) (U Y 0) (hUat Y 0) (hU1 Y 0)`. Rewrite `hm` using `[hU0]`.

Rewrite using `[hm, hsymp _ _ (hUat Y 0) (hU1 Y 0) (hU0 0 (Pm l)), hU0, hU1, hpair]`. Introduce `C φ hφ`. Use function extensionality and compare the values at `Y`. Rewrite using `[hcomm _ (hUat C 0) φ hφ, hact]`. Establish `hat'` using `hat _ (hUat C 0)`.

Establish `hs' : (U C 0 * (mat h)ᵀ).map (piW (t.comp σ)) = 0`. Rewrite using `[Matrix.map_mul, hU1, Matrix.zero_mul]`. Rewrite using `[htr _ hat' hs' (S φ) (hSB φ hφ) _ (hsb _ _ (hSB φ hφ)) (hbr _ hat' _) Y, Matrix.map_mul, hU0, Matrix.transpose_map]`. Introduce `l φ hφ`. Use function extensionality and compare the values at `Y`.

Rewrite using `[hcomm _ (hUat 0 (Pm l)) φ hφ, hact]`. Establish `hat'` using `hat _ (hUat 0 (Pm l))`. Establish `ht' : (U 0 (Pm l) * (mat h)ᵀ).map (piW t) = 0`. Rewrite using `[Matrix.map_mul, hU0, Matrix.zero_mul]`. Establish `hm` using `hmu _ hat' ht' (S φ) (hSB φ hφ) _ (hsb _ _ (hSB φ hφ)) (hbr _ hat' _) (U Y 0) (hUat Y 0) (hU1 Y 0)`.

Rewrite `hm` using `[hU0]`. Rewrite using `[hm, hsymp _ _ (hUat Y 0) (hU1 Y 0) ht', hU0, Matrix.map_mul, hU1, Matrix.transpose_map, ← hpair l (Y * (((mat h).map (piW t))⁻¹)ᵀ), pair_mul_transpose]`. Establish `hdet : IsUnit ((mat h).map (piW t)).det`. Establish `h1 : IsUnit (mat h).det` using `(Units.isUnit h.1).map Matrix.detMonoidHom`. Establish `h2` using `h1.map (piW t)`.

Rewrite `h2` using `[RingHom.map_det]`. Conclude with `h2`. Establish `hBh : Bm * (mat h).map (piW (t.comp σ)) = (((mat h).map (piW t))⁻¹)ᵀ * Bm`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Matrix.transpose_mul, Matrix.mul_nonsing_inv _ hdet, Matrix.transpose_one, Matrix.one_mul]`.

Use `_ = (((mat h).map (piW t))⁻¹)ᵀ * (((mat h).map (piW t))ᵀ * Bm * (mat h).map (piW (t.comp σ))) := by`. Simplify using `only [Matrix.mul_assoc]`. Use `_ = (((mat h).map (piW t))⁻¹)ᵀ * Bm := by rw [hunit]`. Establish `key : A * Y * Bm * (mat h).map (piW (t.comp σ)) = A * (Y * (((mat h).map (piW t))⁻¹)ᵀ) * Bm`. Rewrite using `[Matrix.mul_assoc (A * Y) Bm, hBh]`.

Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[key]`.
-/
theorem heisW {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ}
    (B : Base F E) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W)
    (hTr : IsTriple B G X om om') (v : Pl F) (t : E →ₐ[F] Fv F v) (h : UA σ G.W.J)
    (S : ((Fin a × Fin (a + a') → Fv F v) → ℂ) → (Fin a × Fin (a + a') → Fv F v) → ℂ)
    (hSB : ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), S φ ∈ SB (Fin a × Fin (a + a') → Fv F v))
    (hcomm : ∀ γ : Matrix (Fin a) (Fin (a + a')) (AE F E), At (evFin F v) γ →
        ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v),
          S (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M.co v γ) φ) =
            schr (GlobalTheory.LatVac.psiAt B.ψ v)
              (GlobalTheory.LatVac.locCo G.M.co v (actAB (cA σ) ((1 : UA σ G.V.J), h) γ)) (S φ)) :
    Continuous (GlobalTheory.LatVac.psiAt B.ψ v) ∧ GlobalTheory.LatVac.psiAt B.ψ v ≠ 1 ∧
    ∃ (wT : Matrix (Fin a) (Fin (a + a')) (Fv F v) → (Fin a × Fin (a + a') → Fv F v) × (Fin a × Fin (a + a') → Fv F v))
      (wM : (Matrix (Fin a) (Fin (a + a')) (Fv F v) →ₗ[Fv F v] Fv F v) →
        (Fin a × Fin (a + a') → Fv F v) × (Fin a × Fin (a + a') → Fv F v)),
    ∀ ι, G.M.IsLinW B.ψ t 1 1 ι →
      (∀ C, ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v),
        ι (schr (GlobalTheory.LatVac.psiAt B.ψ v) (wT C) φ) = fun Y => ι φ (Y + C)) ∧
      (∀ l, ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v),
        ι (schr (GlobalTheory.LatVac.psiAt B.ψ v) (wM l) φ) = fun Y => GlobalTheory.LatVac.psiAt B.ψ v (l Y) * ι φ Y) ∧
      (∀ C, ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v),
        ι (S (schr (GlobalTheory.LatVac.psiAt B.ψ v) (wT C) φ)) = fun Y => ι (S φ) (Y + C * ((mat h).map (piW t))ᵀ)) ∧
      (∀ l, ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v),
        ι (S (schr (GlobalTheory.LatVac.psiAt B.ψ v) (wM l) φ)) =
          fun Y => GlobalTheory.LatVac.psiAt B.ψ v (l (Y * (((mat h).map (piW t))⁻¹)ᵀ)) * ι (S φ) Y) := by
  have hcm : IsCMExt F E σ := hTr.base.cm
  have hstd := hTr.base.std
  refine ⟨GlobalTheory.SchrSB.continuous_psiAt _ hstd.1 _, GlobalTheory.PsiNontriv.psiAt_ne_one _ hstd _, ?_⟩
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have hdV : G.V.J.det ≠ 0 := by
    intro h0
    apply GlobalTheory.WeilSchrodingerHerm.det_ne_zero_of_hasSig (hTr.geo.hV.sig w)
    have e : (G.V.J.map (B.emb w).1).det = (B.emb w).1 G.V.J.det := (RingHom.map_det _ _).symm
    rw [e, h0, map_zero]
  have hdW : G.W.J.det ≠ 0 := by
    intro h0
    apply GlobalTheory.WeilSchrodingerHerm.det_ne_zero_of_hasSig (hTr.geo.hW.sig w)
    have e : (G.W.J.map (B.emb w).1).det = (B.emb w).1 G.W.J.det := (RingHom.map_det _ _).symm
    rw [Matrix.det_smul, e, h0, map_zero, mul_zero]
  have hss : (t.comp σ).comp σ = t := by
    ext x
    simp only [AlgHom.comp_apply, sigma_invol hcm x]
  set A := G.V.J.map (t.comp σ) with hAdef
  set Bm := (G.W.J.map (t.comp σ))ᵀ with hBdef
  have hA : IsUnit Aᵀ.det := by
    have e : A.det = ((t.comp σ : E →ₐ[F] Fv F v) : E →+* Fv F v) G.V.J.det := (RingHom.map_det _ _).symm
    rw [Matrix.det_transpose, e]
    exact isUnit_iff_ne_zero.2 fun h0 =>
      hdV (((t.comp σ : E →ₐ[F] Fv F v) : E →+* Fv F v).injective (by rw [map_zero]; exact h0))
  have hB : IsUnit Bmᵀ.det := by
    have e : (G.W.J.map (t.comp σ)).det = ((t.comp σ : E →ₐ[F] Fv F v) : E →+* Fv F v) G.W.J.det :=
      (RingHom.map_det _ _).symm
    rw [hBdef, Matrix.transpose_transpose, e]
    exact isUnit_iff_ne_zero.2 fun h0 =>
      hdW (((t.comp σ : E →ₐ[F] Fv F v) : E →+* Fv F v).injective (by rw [map_zero]; exact h0))
  choose U hUat hU0 hU1 using fun (P₀ P₁ : Matrix (Fin a) (Fin (a + a')) (Fv F v)) =>
    GlobalTheory.T.exists_splitPlace_adelicMatrix_given_components hcm v t P₀ P₁
  have hsymp : ∀ x u : Matrix (Fin a) (Fin (a + a')) (AE F E), At (evFin F v) x → x.map (piW (t.comp σ)) = 0 →
      u.map (piW t) = 0 →
      B.ψ (symp (R := AF F) (cA σ) (-1) (incM F G.V.J) (incM F G.W.J) x u) =
        GlobalTheory.LatVac.psiAt B.ψ v (∑ k, ∑ j, (A * x.map (piW t) * Bm) k j * u.map (piW (t.comp σ)) k j) := by
    intro x u hx hx0 hu1
    unfold symp
    rw [GlobalTheory.T.adelicTrace_supportedAtSplitPlace hcm v (t.comp σ) _ (at_hTens _ _ x u hx)]
    rw [map_mul, map_mul, map_neg, map_neg, map_one, map_one, neg_one_mul, neg_one_mul, ← neg_add,
      GlobalTheory.T.hermitianTensor_skewHermitian_split_symplectic_pair hcm (t.comp σ) G.V.J G.W.J hTr.geo.hV.herm hTr.geo.hW.skew x u hx0 (by rw [hss]; exact hu1), hss]
    show GlobalTheory.LatVac.psiAt B.ψ v _ = _
    congr 1
    simp only [hAdef, hBdef, Matrix.neg_apply, neg_mul, Finset.sum_neg_distrib, neg_neg]
  let Lm : (Matrix (Fin a) (Fin (a + a')) (Fv F v) →ₗ[Fv F v] Fv F v) → Matrix (Fin a) (Fin (a + a')) (Fv F v) :=
    fun l => Matrix.of fun k j => l (Matrix.single k j 1)
  let Pm : (Matrix (Fin a) (Fin (a + a')) (Fv F v) →ₗ[Fv F v] Fv F v) → Matrix (Fin a) (Fin (a + a')) (Fv F v) :=
    fun l => (Aᵀ)⁻¹ * Lm l * (Bmᵀ)⁻¹
  have hpair : ∀ l Y, ∑ k, ∑ j, (A * Y * Bm) k j * Pm l k j = l Y := by
    intro l Y
    rw [pair_mul, linForm_eq l Y]
    have e : Aᵀ * Pm l * Bmᵀ = Lm l := by
      simp only [Pm]
      rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_right _ _ hB, Matrix.mul_nonsing_inv_cancel_left _ _ hA]
    rw [e]
    rfl

  have hunit : ((mat h).map (piW t))ᵀ * Bm * (mat h).map (piW (t.comp σ)) = Bm := by
    have hu : (mat h)ᵀ * incM F G.W.J * (mat h).map (cA σ) = incM F G.W.J := h.2
    have e := congrArg (fun M => M.map (piW (t.comp σ))) hu
    simp only [Matrix.map_mul] at e
    have hJ : (incM F G.W.J).map (piW (t.comp σ)) = G.W.J.map (t.comp σ) := by
      ext i j
      simp [incM, GlobalTheory.SplitGLLift.piW_inclR]
    have hc : ((mat h).map (cA σ)).map (piW (t.comp σ)) = (mat h).map (piW t) := by
      ext i j
      simp only [Matrix.map_apply]
      rw [GlobalTheory.VacIso.piW_cA, hss]
    rw [hJ, hc, Matrix.transpose_map] at e
    have e2 := congrArg Matrix.transpose e
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose] at e2
    rw [hBdef]
    simpa only [Matrix.mul_assoc] using e2
  refine ⟨fun C => GlobalTheory.LatVac.locCo G.M.co v (U C 0), fun l => GlobalTheory.LatVac.locCo G.M.co v (U 0 (Pm l)), ?_⟩
  intro ι hι
  have hL := hι
  unfold GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model.IsLinW at hL
  simp only [inv_one, Units.val_one, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one] at hL
  have htr := hL.trans
  have hmu := hL.mult
  have hbr := fun (γ : Matrix (Fin a) (Fin (a + a')) (AE F E)) hγ (φ : (Fin a × Fin (a + a') → Fv F v) → ℂ) =>
    GlobalTheory.T.adelicHeisenberg_acts_by_local_schrodinger G.M.co B.ψ v γ hγ φ
  have hsb := fun (w : (Fin a × Fin (a + a') → Fv F v) × (Fin a × Fin (a + a') → Fv F v))
    (φ : (Fin a × Fin (a + a') → Fv F v) → ℂ) (hφ : φ ∈ SB _) => GlobalTheory.SchrSB.schr_mem_SB B.ψ hstd.1 v w φ hφ
  have hact : ∀ u : Matrix (Fin a) (Fin (a + a')) (AE F E),
      actAB (cA σ) ((1 : UA σ G.V.J), h) u = u * (mat h)ᵀ := by
    intro u
    simp [actAB, mat]
  have hat : ∀ u : Matrix (Fin a) (Fin (a + a')) (AE F E), At (evFin F v) u → At (evFin F v) (u * (mat h)ᵀ) := by
    intro u hu r hr
    rw [← Matrix.smul_mul, hu r hr, Matrix.zero_mul]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro C φ hφ
    funext Y
    rw [htr (U C 0) (hUat C 0) (hU1 C 0) φ hφ _ (hsb _ φ hφ) (hbr _ (hUat C 0) φ) Y, hU0]
  · intro l φ hφ
    funext Y
    have hm := hmu (U 0 (Pm l)) (hUat _ _) (hU0 0 (Pm l)) φ hφ _ (hsb _ φ hφ) (hbr _ (hUat _ _) φ)
      (U Y 0) (hUat Y 0) (hU1 Y 0)
    rw [hU0] at hm
    rw [hm, hsymp _ _ (hUat Y 0) (hU1 Y 0) (hU0 0 (Pm l)), hU0, hU1, hpair]
  · intro C φ hφ
    funext Y
    rw [hcomm _ (hUat C 0) φ hφ, hact]
    have hat' := hat _ (hUat C 0)
    have hs' : (U C 0 * (mat h)ᵀ).map (piW (t.comp σ)) = 0 := by
      rw [Matrix.map_mul, hU1, Matrix.zero_mul]
    rw [htr _ hat' hs' (S φ) (hSB φ hφ) _ (hsb _ _ (hSB φ hφ)) (hbr _ hat' _) Y, Matrix.map_mul, hU0,
      Matrix.transpose_map]
  · intro l φ hφ
    funext Y
    rw [hcomm _ (hUat 0 (Pm l)) φ hφ, hact]
    have hat' := hat _ (hUat 0 (Pm l))
    have ht' : (U 0 (Pm l) * (mat h)ᵀ).map (piW t) = 0 := by
      rw [Matrix.map_mul, hU0, Matrix.zero_mul]
    have hm := hmu _ hat' ht' (S φ) (hSB φ hφ) _ (hsb _ _ (hSB φ hφ)) (hbr _ hat' _) (U Y 0) (hUat Y 0) (hU1 Y 0)
    rw [hU0] at hm
    rw [hm, hsymp _ _ (hUat Y 0) (hU1 Y 0) ht', hU0, Matrix.map_mul, hU1, Matrix.transpose_map,
      ← hpair l (Y * (((mat h).map (piW t))⁻¹)ᵀ), pair_mul_transpose]
    have hdet : IsUnit ((mat h).map (piW t)).det := by
      have h1 : IsUnit (mat h).det := (Units.isUnit h.1).map Matrix.detMonoidHom
      have h2 := h1.map (piW t)
      rw [RingHom.map_det] at h2
      exact h2
    have hBh : Bm * (mat h).map (piW (t.comp σ)) = (((mat h).map (piW t))⁻¹)ᵀ * Bm := by
      calc Bm * (mat h).map (piW (t.comp σ))
          = ((((mat h).map (piW t))⁻¹)ᵀ * ((mat h).map (piW t))ᵀ) * Bm * (mat h).map (piW (t.comp σ)) := by
            rw [← Matrix.transpose_mul, Matrix.mul_nonsing_inv _ hdet, Matrix.transpose_one, Matrix.one_mul]
        _ = (((mat h).map (piW t))⁻¹)ᵀ * (((mat h).map (piW t))ᵀ * Bm * (mat h).map (piW (t.comp σ))) := by
            simp only [Matrix.mul_assoc]
        _ = (((mat h).map (piW t))⁻¹)ᵀ * Bm := by rw [hunit]
    have key : A * Y * Bm * (mat h).map (piW (t.comp σ)) = A * (Y * (((mat h).map (piW t))⁻¹)ᵀ) * Bm := by
      rw [Matrix.mul_assoc (A * Y) Bm, hBh]
      simp only [Matrix.mul_assoc]
    rw [key]

/- English proof (translation)
Introduce `hP F E _ _ _ _ _ σ B a a' G X om om' hTr v _ t ι hι h hh`. Take `⟨S, hSB, huniq, hlin, hcomm⟩` from `exists_localOp hP F E σ B a a' G X om om' hTr v h hh`. Take `⟨hψc, hψ1, wT, wM, hA⟩` from `heisW B G X om om' hTr v t h S hSB hcomm`. Take `⟨hT0, hM0, hST, hSM⟩` from `hA ι hι`. Establish `hbij` using `GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model.IsLin.bij hι`.

Use `set ht := (mat h).map (piW t) with hht`. Establish `hdet : IsUnit ht.det`. Establish `h1 : IsUnit (mat h).det` using `(Units.isUnit h.1).map Matrix.detMonoidHom`. Establish `h2` using `h1.map (piW t)`. Rewrite `h2` using `[RingHom.map_det]`.

Conclude with `h2`. Establish `hsb` using `fun (w : (Fin a × Fin (a + a') → Fv F v) × (Fin a × Fin (a + a') → Fv F v)) (φ : (Fin a × Fin (a + a') → Fv F v) → ℂ) (hφ : φ ∈ SB _) => GlobalTheory.SchrSB.schr_mem_SB B.ψ hTr.base.std.1 v w φ hφ`. Establish `hL2 : ∀ x ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ y ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ c : ℂ, (fun Y : Matrix (Fin a) (Fin (a + a')) (Fv F v) => ι (S (c • x + y)) (Y * htᵀ)) = c • (fun Y : Matrix (Fin a) (Fin (a + a')) (Fv F v) => ι (S x) (Y * htᵀ)) + fun Y : Matrix (Fin a) …`. Introduce `x hx y hy c`. Use function extensionality and compare the values at `Y`.

Simplify using `only [hlin x hx y hy c, map_add, map_smul, Pi.add_apply, Pi.smul_apply]`. Establish `hT2 : ∀ C, ∀ x ∈ SB (Fin a × Fin (a + a') → Fv F v), schr (GlobalTheory.LatVac.psiAt B.ψ v) (wT C) x ∈ SB (Fin a × Fin (a + a') → Fv F v) ∧ ι (schr (GlobalTheory.LatVac.psiAt B.ψ v) (wT C) x) = (fun Y => ι x (Y + C)) ∧ (fun Y : Matrix (Fin a) (Fin (a + a')) (Fv F v) => ι (S (schr …`. Introduce `C x hx`. Use `⟨hsb _ x hx, hT0 C x hx, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `Y`.

Simplify using `only [hST C x hx, Matrix.add_mul]`. Establish `hM2 : ∀ l, ∀ x ∈ SB (Fin a × Fin (a + a') → Fv F v), schr (GlobalTheory.LatVac.psiAt B.ψ v) (wM l) x ∈ SB (Fin a × Fin (a + a') → Fv F v) ∧ ι (schr (GlobalTheory.LatVac.psiAt B.ψ v) (wM l) x) = (fun Y => GlobalTheory.LatVac.psiAt B.ψ v (l Y) * ι x Y) ∧ (fun Y : Matrix (Fin a) (Fi …`. Introduce `l x hx`. Use `⟨hsb _ x hx, hM0 l x hx, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `Y`.

Simplify using `only [hSM l x hx, Matrix.mul_assoc, ← Matrix.transpose_mul, Matrix.nonsing_inv_mul _ hdet, Matrix.transpose_one, Matrix.mul_one]`. Take `⟨c, hc⟩` from `GlobalTheory.T.eq_smul_of_commute_heisenberg_linearModel_schwartzBruhat (SB (Fin a × Fin (a + a') → Fv F v)) (GlobalTheory.LatVac.psiAt B.ψ v) hψc hψ1 ι (fun x Y => ι (S x) (Y * htᵀ)) hbij hL2 (fun C => schr (GlobalTheory.LatVac.psiAt B.ψ v) (wT C)) (fun l => schr (GlobalTheory.L …`. Use `⟨c, fun φ hφ φ₁ _ hAct Y => ?_⟩` and prove the remaining obligations. Rewrite using `[huniq φ hφ φ₁ hAct]`. Establish `e` using `congrFun (hc φ hφ) (Y * (ht⁻¹)ᵀ)`.

Simplify using `only [Pi.smul_apply, smul_eq_mul] at e`. Rewrite `e` using `[Matrix.mul_assoc, ← Matrix.transpose_mul, Matrix.mul_nonsing_inv _ hdet, Matrix.transpose_one, Matrix.mul_one]`. Then use the resulting hypothesis.
-/
theorem shape : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ v, X.Good v →
    ∀ (t : E →ₐ[F] Fv F v) (ι : ((Fin a × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin a) (Fin (a + a')) (Fv F v) → ℂ)), G.M.IsLinW B.ψ t 1 1 ι → (∀ h ∈ UAt σ G.W (evFin F v), ∃ c : ℂ, ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v),
      Acts (evFin F v) (om (1, h)) φ φ₁ → ∀ Y, ι φ₁ Y = c * ι φ (Y * (((mat h).map (piW t))⁻¹)ᵀ)) := by
  intro hP F E _ _ _ _ _ σ B a a' G X om om' hTr v _ t ι hι h hh
  obtain ⟨S, hSB, huniq, hlin, hcomm⟩ := exists_localOp hP F E σ B a a' G X om om' hTr v h hh
  obtain ⟨hψc, hψ1, wT, wM, hA⟩ := heisW B G X om om' hTr v t h S hSB hcomm
  obtain ⟨hT0, hM0, hST, hSM⟩ := hA ι hι
  have hbij := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model.IsLin.bij hι
  set ht := (mat h).map (piW t) with hht
  have hdet : IsUnit ht.det := by
    have h1 : IsUnit (mat h).det := (Units.isUnit h.1).map Matrix.detMonoidHom
    have h2 := h1.map (piW t)
    rw [RingHom.map_det] at h2
    exact h2
  have hsb := fun (w : (Fin a × Fin (a + a') → Fv F v) × (Fin a × Fin (a + a') → Fv F v))
    (φ : (Fin a × Fin (a + a') → Fv F v) → ℂ) (hφ : φ ∈ SB _) => GlobalTheory.SchrSB.schr_mem_SB B.ψ hTr.base.std.1 v w φ hφ
  have hL2 : ∀ x ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ y ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ c : ℂ,
      (fun Y : Matrix (Fin a) (Fin (a + a')) (Fv F v) => ι (S (c • x + y)) (Y * htᵀ)) = c • (fun Y : Matrix (Fin a) (Fin (a + a')) (Fv F v) => ι (S x) (Y * htᵀ)) + fun Y : Matrix (Fin a) (Fin (a + a')) (Fv F v) => ι (S y) (Y * htᵀ) := by
    intro x hx y hy c
    funext Y
    simp only [hlin x hx y hy c, map_add, map_smul, Pi.add_apply, Pi.smul_apply]
  have hT2 : ∀ C, ∀ x ∈ SB (Fin a × Fin (a + a') → Fv F v),
      schr (GlobalTheory.LatVac.psiAt B.ψ v) (wT C) x ∈ SB (Fin a × Fin (a + a') → Fv F v) ∧
      ι (schr (GlobalTheory.LatVac.psiAt B.ψ v) (wT C) x) = (fun Y => ι x (Y + C)) ∧
      (fun Y : Matrix (Fin a) (Fin (a + a')) (Fv F v) => ι (S (schr (GlobalTheory.LatVac.psiAt B.ψ v) (wT C) x)) (Y * htᵀ)) = fun Y : Matrix (Fin a) (Fin (a + a')) (Fv F v) => ι (S x) ((Y + C) * htᵀ) := by
    intro C x hx
    refine ⟨hsb _ x hx, hT0 C x hx, ?_⟩
    funext Y
    simp only [hST C x hx, Matrix.add_mul]
  have hM2 : ∀ l, ∀ x ∈ SB (Fin a × Fin (a + a') → Fv F v),
      schr (GlobalTheory.LatVac.psiAt B.ψ v) (wM l) x ∈ SB (Fin a × Fin (a + a') → Fv F v) ∧
      ι (schr (GlobalTheory.LatVac.psiAt B.ψ v) (wM l) x) = (fun Y => GlobalTheory.LatVac.psiAt B.ψ v (l Y) * ι x Y) ∧
      (fun Y : Matrix (Fin a) (Fin (a + a')) (Fv F v) => ι (S (schr (GlobalTheory.LatVac.psiAt B.ψ v) (wM l) x)) (Y * htᵀ)) =
        fun Y : Matrix (Fin a) (Fin (a + a')) (Fv F v) => GlobalTheory.LatVac.psiAt B.ψ v (l Y) * ι (S x) (Y * htᵀ) := by
    intro l x hx
    refine ⟨hsb _ x hx, hM0 l x hx, ?_⟩
    funext Y
    simp only [hSM l x hx, Matrix.mul_assoc, ← Matrix.transpose_mul, Matrix.nonsing_inv_mul _ hdet, Matrix.transpose_one,
      Matrix.mul_one]
  obtain ⟨c, hc⟩ := GlobalTheory.T.eq_smul_of_commute_heisenberg_linearModel_schwartzBruhat (SB (Fin a × Fin (a + a') → Fv F v)) (GlobalTheory.LatVac.psiAt B.ψ v) hψc hψ1 ι
    (fun x Y => ι (S x) (Y * htᵀ)) hbij hL2
    (fun C => schr (GlobalTheory.LatVac.psiAt B.ψ v) (wT C)) (fun l => schr (GlobalTheory.LatVac.psiAt B.ψ v) (wM l)) hT2 hM2
  refine ⟨c, fun φ hφ φ₁ _ hAct Y => ?_⟩
  rw [huniq φ hφ φ₁ hAct]
  have e := congrFun (hc φ hφ) (Y * (ht⁻¹)ᵀ)
  simp only [Pi.smul_apply, smul_eq_mul] at e
  rwa [Matrix.mul_assoc, ← Matrix.transpose_mul, Matrix.mul_nonsing_inv _ hdet, Matrix.transpose_one,
    Matrix.mul_one] at e

end GlobalTheory.UnitWShape
