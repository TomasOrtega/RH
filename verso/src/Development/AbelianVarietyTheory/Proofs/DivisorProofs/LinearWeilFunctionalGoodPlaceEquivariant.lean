import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPairOfIsTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqSmulOfCommuteHeisenbergLinearModelSchwartzBruhStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitPlaceAdelicMatrixGivenComponentsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianTensorSkewHermitianSplitSymplecticPairStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicTraceSupportedAtSplitPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHeisenbergActsByLocalSchrodinger
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplementaryAdelicSchwartzOfNonzeroLocalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartzStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerPreservesSchwartzBruhat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharacterNontrivialAtPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianSelfDualLatticeSpaceFormHermitianNondeg
import Development.AbelianVarietyTheory.Definitions.Foundations.NonemptyAlgHomOfNotIsField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.ShapeUV

/- English proof (translation)
Unfold `hTens`. Simplify using `only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => by ring`.
-/
theorem hTens_eq_sum {R E : Type} [CommRing R] [CommRing E] [Algebra R E] (c : E →ₐ[R] E) {α β : Type}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] (JA : Matrix α α E) (JB : Matrix β β E)
    (x y : Matrix α β E) :
    hTens c JA JB x y = ∑ j, ∑ l, (xᵀ * JA * y.map c) j l * JB j l := by
  unfold hTens
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  calc ∑ i, ∑ k, ∑ l, x i j * JA i k * JB j l * c (y k l)
      = ∑ i, ∑ l, ∑ k, x i j * JA i k * JB j l * c (y k l) := Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ l, ∑ i, ∑ k, x i j * JA i k * JB j l * c (y k l) := Finset.sum_comm
    _ = ∑ l, ∑ k, ∑ i, x i j * JA i k * c (y k l) * JB j l := Finset.sum_congr rfl fun l _ => by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => by ring

/- English proof (translation)
Unfold `symp`. Rewrite using `[hTens_eq_sum, hTens_eq_sum]`. Establish `e : (g * x)ᵀ * JA * (g * y).map c = xᵀ * JA * y.map c`. Establish `hm : (g * y).map c = g.map c * y.map c` using `Matrix.map_mul (f := c.toRingHom)`. Rewrite using `[hm, Matrix.transpose_mul]`.

Use `conv_rhs => rw [← hg]`. Simplify using `only [Matrix.mul_assoc]`. Simplify using `only [e]`.
-/
theorem symp_mul_mul {R E : Type} [CommRing R] [CommRing E] [Algebra R E] (c : E →ₐ[R] E) {α β : Type}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] (ξ : E) (JA : Matrix α α E) (JB : Matrix β β E)
    (g : Matrix α α E) (hg : gᵀ * JA * g.map c = JA) (x y : Matrix α β E) :
    symp c ξ JA JB (g * x) (g * y) = symp c ξ JA JB x y := by
  unfold symp
  rw [hTens_eq_sum, hTens_eq_sum]
  have e : (g * x)ᵀ * JA * (g * y).map c = xᵀ * JA * y.map c := by
    have hm : (g * y).map c = g.map c * y.map c := Matrix.map_mul (f := c.toRingHom)
    rw [hm, Matrix.transpose_mul]
    conv_rhs => rw [← hg]
    simp only [Matrix.mul_assoc]
  simp only [e]

/- English proof (translation)
Simplify using `[Matrix.trace, Matrix.mul_apply]`.
-/
theorem sum_mul_eq_trace {K : Type} [CommRing K] {m n : Type} [Fintype m] [Fintype n]
    (M N : Matrix m n K) : ∑ k, ∑ l, M k l * N k l = (M * Nᵀ).trace := by
  simp [Matrix.trace, Matrix.mul_apply]

/- English proof (translation)
Rewrite using `[sum_mul_eq_trace, sum_mul_eq_trace]`. Simplify using `only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]`. Rewrite using `[Matrix.trace_mul_comm]`. Simplify using `only [Matrix.mul_assoc]`.
-/
theorem sum_conj_mul {K : Type} [CommRing K] {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (P : Matrix m m K) (Q : Matrix n n K) (Y L : Matrix m n K) :
    ∑ k, ∑ l, (P * Y * Qᵀ) k l * L k l = ∑ k, ∑ l, Y k l * (Pᵀ * L * Q) k l := by
  rw [sum_mul_eq_trace, sum_mul_eq_trace]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  rw [Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

/- English proof (translation)
Use `conv_lhs => rw [Y.matrix_eq_sum_single]`. Simplify using `only [map_sum]`. Use `Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[show Matrix.single k j (Y k j) = Y k j • Matrix.single k j (1 : K) by`. Rewrite using `[Matrix.smul_single, smul_eq_mul, mul_one], map_smul, smul_eq_mul]`.
-/
theorem linForm_sum {K : Type} [Field K] {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (l : Matrix m n K →ₗ[K] K) (Y : Matrix m n K) :
    l Y = ∑ k, ∑ j, Y k j * l (Matrix.single k j 1) := by
  conv_lhs => rw [Y.matrix_eq_sum_single]
  simp only [map_sum]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
  rw [show Matrix.single k j (Y k j) = Y k j • Matrix.single k j (1 : K) by
    rw [Matrix.smul_single, smul_eq_mul, mul_one], map_smul, smul_eq_mul]

/- English proof (translation)
Introduce `r hr`. Establish `h : ∀ i j, r • x i j = 0` using `fun i j => by`. Use `congrFun (congrFun (hx r hr) i) j` as an intermediate fact. Simplify using `using this`. Rewrite using `[← mul_smul_comm]`.

Unfold `hTens`. Simplify using `only [Finset.smul_sum, ← smul_mul_assoc, h, zero_mul, Finset.sum_const_zero, mul_zero]`.
-/
theorem at_neg_hTens {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
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

end GlobalTheory.ShapeUV

namespace GlobalTheory.ShapeUV

/- English proof (translation)
Introduce `hP F E _ _ _ _ _ σ B a a' G X om om' hTr v hv t ι hι g hg`. Establish `hcm : IsCMExt F E σ` using `hTr.base.cm`. Establish `hstd` using `hTr.base.std`. Establish `hψc : Continuous (GlobalTheory.LatVac.psiAt B.ψ v)` using `GlobalTheory.SchrSB.continuous_psiAt _ hstd.1 v`. Establish `hψ1 : GlobalTheory.LatVac.psiAt B.ψ v ≠ 1` using `GlobalTheory.PsiNontriv.psiAt_ne_one _ hstd v`.

Establish `hSplit` using `GlobalTheory.WeilM.IsUWeilPair.isUSplitting hTr.weil`. Establish `hAE` using `(GlobalTheory.T.theta_action_exists hP) F E σ B a (a + a') G.V G.W G.M X.β (X.β / X.α) om _ _ _ _ (GlobalTheory.ThK.Check.isPair_of_isTriple hTr).1 v`. Establish `h1W : (1 : UA σ G.W.J) ∈ UAt σ G.W (evFin F v)`. Introduce `u _`. Simplify using `[mat]`.

Establish `hex : ∀ φ : (Fin a × Fin (a + a') → Fv F v) → ℂ, ∃ φ₁ : (Fin a × Fin (a + a') → Fv F v) → ℂ, φ ∈ SB (Fin a × Fin (a + a') → Fv F v) → φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v) ∧ Acts (evFin F v) (om (g, 1)) φ φ₁`. Introduce `φ`. Distinguish the cases in `hφ : φ ∈ SB (Fin a × Fin (a + a') → Fv F v)`. Take `⟨φ₁, h, -⟩` from `hAE.1 g hg 1 h1W φ hφ`. Conclude with `⟨φ₁, fun _ => h⟩`.

Conclude with `⟨0, fun h => absurd h hφ⟩`. Use `choose A hA using hex`. Establish `huniq : ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v), Acts (evFin F v) (om (g, 1)) φ φ₁ → φ₁ = A φ` using `fun φ hφ φ₁ hφ₁ h => (hAE.1 g hg 1 h1W φ hφ).unique ⟨hφ₁, h⟩ (hA φ hφ)`. Establish `hASB : ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), A φ ∈ SB (Fin a × Fin (a + a') → Fv F v)` using `fun φ hφ => (hA φ hφ).1`. Establish `restA : ∀ φ r, φ ∈ SB (Fin a × Fin (a + a') → Fv F v) → Rest (evFin F v) φ r → Rest (evFin F v) (A φ) r` using `fun φ r hφ hr => ⟨hr.1, by rw [← (hA φ hφ).2 r hr]; exact hSplit.pres _ _ hr.2⟩`.

Establish `hvac` using `hTr.geo.hM.vac v`. Establish `hlin : ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ' ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ c : ℂ, A (c • φ + φ') = c • A φ + A φ'`. Introduce `φ hφ φ' hφ' c`. Use `GlobalTheory.T.eq_of_componentTensorAdelicFunction_eq v (G.M.vac v) _ _ hvac.1 fun r hr => ?_` and prove the remaining obligations. Establish `hsum : c • φ + φ' ∈ SB (Fin a × Fin (a + a') → Fv F v)` using `Submodule.add_mem _ (Submodule.smul_mem _ c hφ) hφ'`.

Establish `r0` using `GlobalTheory.T.complementaryAdelicSchwartz_of_nonzero_local v _ _ r hvac.2.1 hsum hr`. Establish `r1` using `GlobalTheory.T.complementaryAdelicSchwartz_of_nonzero_local v _ _ r hvac.2.1 hφ hr`. Establish `r2` using `GlobalTheory.T.complementaryAdelicSchwartz_of_nonzero_local v _ _ r hvac.2.1 hφ' hr`. Establish `et : ∀ (ψ₁ ψ₂ : (Fin a × Fin (a + a') → Fv F v) → ℂ), tens (evFin F v) (c • ψ₁ + ψ₂) r = c • tens (evFin F v) ψ₁ r + tens (evFin F v) ψ₂ r` using `fun ψ₁ ψ₂ => by`. Use function extensionality and compare the values at `x`.

Simplify using `only [tens, Pi.add_apply, Pi.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[← (hA _ hsum).2 r r0, et, map_add, map_smul, (hA φ hφ).2 r r1, (hA φ' hφ').2 r r2, et]`. Establish `hact : ∀ γ : Matrix (Fin a) (Fin (a + a')) (AE F E), actAB (cA σ) (g, (1 : UA σ G.W.J)) γ = mat g * γ`. Introduce `γ`.

Simplify using `[actAB, mat]`. Establish `atMul : ∀ (M : Matrix (Fin a) (Fin a) (AE F E)) (γ : Matrix (Fin a) (Fin (a + a')) (AE F E)), At (evFin F v) γ → At (evFin F v) (M * γ)`. Introduce `M γ hγ u hu`. Rewrite using `[← Matrix.mul_smul, hγ u hu, Matrix.mul_zero]`. Establish `hcov : ∀ γ : Matrix (Fin a) (Fin (a + a')) (AE F E), At (evFin F v) γ → ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), A (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M.co v γ) φ) = schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M.co v (mat …`.

Introduce `γ hγ φ hφ`. Establish `hw` using `GlobalTheory.SchrSB.schr_mem_SB B.ψ hstd.1 v (GlobalTheory.LatVac.locCo G.M.co v γ) φ hφ`. Use `GlobalTheory.T.eq_of_componentTensorAdelicFunction_eq v φ _ _ hφ fun r hr => ?_` and prove the remaining obligations. Establish `hb1` using `GlobalTheory.VacBridge.rho_acts_locCo G.M.co B.ψ v γ hγ φ r hr`. Establish `hRw : Rest (evFin F v) (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M.co v γ) φ) r` using `⟨hr.1, by rw [← hb1]; exact GlobalTheory.T.weil_representation_preserves_schwartz G.M B.ψ hstd γ _ hr.2⟩`.

Rewrite using `[← (hA _ hw).2 r hRw, ← hb1, hSplit.impl _ _ _ hr.2, (hA φ hφ).2 r hr, hact, GlobalTheory.VacBridge.rho_acts_locCo G.M.co B.ψ v _ (atMul _ γ hγ) (A φ) r (restA φ r hφ hr)]`. Establish `hL` using `hι`. Unfold `GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model.IsLinW at hL`. Simplify using `only [inv_one, Units.val_one, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one] at hL`. Establish `hsb : ∀ (w : (Fin a × Fin (a + a') → Fv F v) × (Fin a × Fin (a + a') → Fv F v)) (φ : (Fin a × Fin (a + a') → Fv F v) → ℂ), φ ∈ SB (Fin a × Fin (a + a') → Fv F v) → schr (GlobalTheory.LatVac.psiAt B.ψ v) w φ ∈ SB (Fin a × Fin (a + a') → Fv F v)` using `fun w φ hφ => GlobalTheory.SchrSB.schr_mem_SB B.ψ hstd.1 v w φ hφ`.

Establish `hT : ∀ γ : Matrix (Fin a) (Fin (a + a')) (AE F E), At (evFin F v) γ → γ.map (piW (t.comp σ)) = 0 → ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ Y, ι (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M.co v γ) φ) Y = ι φ (Y + γ.map (piW t))` using `fun γ hγ h0 φ hφ Y => hL.trans γ hγ h0 φ hφ _ (hsb _ φ hφ) (GlobalTheory.VacBridge.rho_acts_locCo G.M.co B.ψ v γ hγ φ) Y`. Establish `hM : ∀ γ : Matrix (Fin a) (Fin (a + a')) (AE F E), At (evFin F v) γ → γ.map (piW t) = 0 → ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ x : Matrix (Fin a) (Fin (a + a')) (AE F E), At (evFin F v) x → x.map (piW (t.comp σ)) = 0 → ι (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheor …` using `fun γ hγ h0 φ hφ x hx hx0 => hL.mult γ hγ h0 φ hφ _ (hsb _ φ hφ) (GlobalTheory.VacBridge.rho_acts_locCo G.M.co B.ψ v γ hγ φ) x hx hx0`. Use `choose U hUat hU0 hU1 using fun (P₀ P₁ : Matrix (Fin a) (Fin (a + a')) (Fv F v)) => GlobalTheory.T.exists_splitPlace_adelicMatrix_given_components hcm v t P₀ P₁`. Use `set A' := G.V.J.map (t.comp σ) with hA'def`. Use `set B' := G.W.J.map (t.comp σ) with hB'def`.

Establish `hsymp : ∀ x u : Matrix (Fin a) (Fin (a + a')) (AE F E), At (evFin F v) x → x.map (piW (t.comp σ)) = 0 → u.map (piW t) = 0 → B.ψ (symp (R` using `AF F) (cA σ) (-1) (incM F G.V.J) (incM F G.W.J) x u) = GlobalTheory.LatVac.psiAt B.ψ v (-(∑ k, ∑ l, (-(A' * x.map (piW t) * B'ᵀ)) k l * u.map (piW (t.comp σ)) k l)) := by`. Introduce `x u hx hx0 hu1`. Establish `hu1' : u.map (piW ((t.comp σ).comp σ)) = 0` using `by rw [comp_conj_conj hcm]; exact hu1`. Establish `e` using `GlobalTheory.T.hermitianTensor_skewHermitian_split_symplectic_pair hcm (t.comp σ) G.V.J G.W.J hTr.geo.hV.herm hTr.geo.hW.skew x u hx0 hu1'`. Rewrite `e` using `[comp_conj_conj hcm]`.

Unfold `symp`. Rewrite using `[GlobalTheory.T.adelicTrace_supportedAtSplitPlace hcm v (t.comp σ) _ (at_neg_hTens _ _ x u hx), comp_conj_conj hcm]`. Rewrite using `[map_mul, map_mul, map_neg, map_neg, map_one, map_one, neg_one_mul, neg_one_mul, ← neg_add, e]`. Both sides reduce to the same expression. Take `⟨w⟩ : Nonempty (InfinitePlace F)` from `inferInstance`.

Establish `hdV : G.V.J.det ≠ 0`. Introduce `h0`. Apply `GlobalTheory.WeilSchrodingerHerm.det_ne_zero_of_hasSig (hTr.geo.hV.sig w)` to reduce the goal to its premises. Establish `e : (G.V.J.map (B.emb w).1).det = (B.emb w).1 G.V.J.det` using `(RingHom.map_det _ _).symm`. Rewrite using `[e, h0, map_zero]`.

Establish `hdW : G.W.J.det ≠ 0`. Introduce `h0`. Apply `GlobalTheory.WeilSchrodingerHerm.det_ne_zero_of_hasSig (hTr.geo.hW.sig w)` to reduce the goal to its premises. Establish `e : (G.W.J.map (B.emb w).1).det = (B.emb w).1 G.W.J.det` using `(RingHom.map_det _ _).symm`. Rewrite using `[Matrix.det_smul, e, h0, map_zero, mul_zero]`.

Establish `hA' : IsUnit A'ᵀ.det`. Establish `e : A'.det = ((t.comp σ : E →ₐ[F] Fv F v) : E →+* Fv F v) G.V.J.det` using `(RingHom.map_det _ _).symm`. Rewrite using `[Matrix.det_transpose, e]`. Conclude with `isUnit_iff_ne_zero.2 fun h => hdV (((t.comp σ : E →ₐ[F] Fv F v) : E →+* Fv F v).injective (by rw [map_zero]; exact h))`. Establish `hB' : IsUnit B'.det`.

Establish `e : B'.det = ((t.comp σ : E →ₐ[F] Fv F v) : E →+* Fv F v) G.W.J.det` using `(RingHom.map_det _ _).symm`. Rewrite using `[e]`. Conclude with `isUnit_iff_ne_zero.2 fun h => hdW (((t.comp σ : E →ₐ[F] Fv F v) : E →+* Fv F v).injective (by rw [map_zero]; exact h))`. Set `Lm : (Matrix (Fin a) (Fin (a + a')) (Fv F v) →ₗ[Fv F v] Fv F v) → Matrix (Fin a) (Fin (a + a')) (Fv F v)` to `fun l => Matrix.of fun k j => l (Matrix.single k j 1)`. Establish `hchar : ∀ (l : Matrix (Fin a) (Fin (a + a')) (Fv F v) →ₗ[Fv F v] Fv F v) (Y : Matrix (Fin a) (Fin (a + a')) (Fv F v)), -(∑ k, ∑ j, (-(A' * Y * B'ᵀ)) k j * ((A'ᵀ)⁻¹ * Lm l * B'⁻¹) k j) = l Y`.

Introduce `l Y`. Simplify using `only [Matrix.neg_apply, neg_mul, Finset.sum_neg_distrib, neg_neg]`. Rewrite using `[sum_conj_mul, linForm_sum l Y]`. Establish `e : A'ᵀ * ((A'ᵀ)⁻¹ * Lm l * B'⁻¹) * B' = Lm l`. Simplify using `only [Matrix.mul_assoc]`.

Rewrite using `[Matrix.nonsing_inv_mul _ hB', Matrix.mul_one, Matrix.mul_nonsing_inv_cancel_left _ _ hA']`. Rewrite using `[e]`. Both sides reduce to the same expression. Use `set gt := (mat g).map (piW t) with hgt`. Use `set gti := (mat g⁻¹).map (piW t) with hgti`.

Establish `hmatinv : mat g⁻¹ * mat g = 1` using `by simp [mat]`. Establish `hmatinv' : mat g * mat g⁻¹ = 1` using `by simp [mat]`. Establish `hgg : gti * gt = 1`. Rewrite using `[hgti, hgt, ← Matrix.map_mul, hmatinv, Matrix.map_one _ (map_zero _) (map_one _)]`. Establish `hgg' : gt * gti = 1`.

Rewrite using `[hgti, hgt, ← Matrix.map_mul, hmatinv', Matrix.map_one _ (map_zero _) (map_one _)]`. Establish `hinv : gt⁻¹ = gti` using `Matrix.inv_eq_left_inv hgg`. Establish `hU : (mat g)ᵀ * incM F G.V.J * (mat g).map (cA σ) = incM F G.V.J` using `g.2`. Establish `h2lin : ∀ x ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ y ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ c : ℂ, (fun (Y : Matrix (Fin a) (Fin (a + a')) (Fv F v)) => ι (A (c • x + y)) (gt * Y)) = c • (fun (Y : Matrix (Fin a) (Fin (a + a')) (Fv F v)) => ι (A x) (gt * Y)) + (fun (Y : Matrix (F …`. Introduce `x hx y hy c`.

Use function extensionality and compare the values at `Y`. Simplify using `only [hlin x hx y hy c, map_add, map_smul, Pi.add_apply, Pi.smul_apply]`. Establish `h2tr : ∀ C : Matrix (Fin a) (Fin (a + a')) (Fv F v), ∀ x ∈ SB (Fin a × Fin (a + a') → Fv F v), schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M.co v (U C 0)) x ∈ SB (Fin a × Fin (a + a') → Fv F v) ∧ ι (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatV …`. Introduce `C x hx`. Use `⟨hsb _ x hx, ?_, ?_⟩` and prove the remaining obligations.

Use function extensionality and compare the values at `Y`. Rewrite using `[hT _ (hUat C 0) (hU1 C 0) x hx Y, hU0]`. Use function extensionality and compare the values at `Y`. Establish `h0 : (mat g * U C 0).map (piW (t.comp σ)) = 0`. Rewrite using `[Matrix.map_mul, hU1, Matrix.mul_zero]`.

Rewrite using `[hcov _ (hUat C 0) x hx, hT _ (atMul _ _ (hUat C 0)) h0 (A x) (hASB x hx), Matrix.map_mul, hU0, Matrix.mul_add]`. Establish `h2mu : ∀ (l : Matrix (Fin a) (Fin (a + a')) (Fv F v) →ₗ[Fv F v] Fv F v), ∀ x ∈ SB (Fin a × Fin (a + a') → Fv F v), schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M.co v (U 0 ((A'ᵀ)⁻¹ * Lm l * B'⁻¹))) x ∈ SB (Fin a × Fin (a + a') → Fv F v) ∧ ι (schr (GlobalThe …`. Introduce `l x hx`. Use `set P := (A'ᵀ)⁻¹ * Lm l * B'⁻¹ with hP`. Use `⟨hsb _ x hx, ?_, ?_⟩` and prove the remaining obligations.

Use function extensionality and compare the values at `Y`. Establish `hm` using `hM (U 0 P) (hUat 0 P) (hU0 0 P) x hx (U Y 0) (hUat Y 0) (hU1 Y 0)`. Rewrite `hm` using `[hU0]`. Rewrite using `[hm, hsymp _ _ (hUat Y 0) (hU1 Y 0) (hU0 0 P), hU0, hU1, hchar]`. Use function extensionality and compare the values at `Y`.

Establish `h0 : (mat g * U 0 P).map (piW t) = 0`. Rewrite using `[Matrix.map_mul, hU0, Matrix.mul_zero]`. Establish `hm` using `hM _ (atMul _ _ (hUat 0 P)) h0 (A x) (hASB x hx) (U (gt * Y) 0) (hUat (gt * Y) 0) (hU1 (gt * Y) 0)`. Rewrite `hm` using `[hU0]`. Establish `hx' : symp (cA σ) (-1) (incM F G.V.J) (incM F G.W.J) (U (gt * Y) 0) (mat g * U 0 P) = symp (cA σ) (-1) (incM F G.V.J) (incM F G.W.J) (mat g⁻¹ * U (gt * Y) 0) (U 0 P)` using `by conv_lhs => rw [show U (gt * Y) 0 = mat g * (mat g⁻¹ * U (gt * Y) 0) by`.

Rewrite using `[← Matrix.mul_assoc, hmatinv', Matrix.one_mul]]`. Conclude with `symp_mul_mul _ _ _ _ _ hU _ _`. Establish `h1 : (mat g⁻¹ * U (gt * Y) 0).map (piW (t.comp σ)) = 0`. Rewrite using `[Matrix.map_mul, hU1, Matrix.mul_zero]`. Establish `h2 : (mat g⁻¹ * U (gt * Y) 0).map (piW t) = Y`.

Rewrite using `[Matrix.map_mul, hU0, ← hgti, ← Matrix.mul_assoc, hgg, Matrix.one_mul]`. Rewrite using `[hcov _ (hUat 0 P) x hx, hm, hx', hsymp _ _ (atMul _ _ (hUat (gt * Y) 0)) h1 (hU0 0 P), h2, hU1, hchar]`. Take `⟨c, hc⟩` from `GlobalTheory.T.eq_smul_of_commute_heisenberg_linearModel_schwartzBruhat (SB (Fin a × Fin (a + a') → Fv F v)) (GlobalTheory.LatVac.psiAt B.ψ v) hψc hψ1 ι (fun φ (Y : Matrix (Fin a) (Fin (a + a')) (Fv F v)) => ι (A φ) (gt * Y)) hL.bij h2lin _ _ h2tr h2mu`. Use `⟨c, fun φ hφ φ₁ hφ₁ hact1 Y => ?_⟩` and prove the remaining obligations. Rewrite using `[huniq φ hφ φ₁ hφ₁ hact1, hinv]`.

Establish `e` using `congrFun (hc φ hφ) (gti * Y)`. Simplify using `only [Pi.smul_apply, smul_eq_mul] at e`. Rewrite `e` using `[← Matrix.mul_assoc, hgg', Matrix.one_mul]`. Conclude with `e`.
-/
theorem shapeV : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ v, X.Good v →
    ∀ (t : E →ₐ[F] Fv F v) (ι : ((Fin a × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin a) (Fin (a + a')) (Fv F v) → ℂ)), G.M.IsLinW B.ψ t 1 1 ι → (∀ g ∈ UAt σ G.V (evFin F v), ∃ c : ℂ, ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v),
      Acts (evFin F v) (om (g, 1)) φ φ₁ → ∀ Y, ι φ₁ Y = c * ι φ (((mat g).map (piW t))⁻¹ * Y)) := by
  intro hP F E _ _ _ _ _ σ B a a' G X om om' hTr v hv t ι hι g hg
  have hcm : IsCMExt F E σ := hTr.base.cm
  have hstd := hTr.base.std
  have hψc : Continuous (GlobalTheory.LatVac.psiAt B.ψ v) := GlobalTheory.SchrSB.continuous_psiAt _ hstd.1 v
  have hψ1 : GlobalTheory.LatVac.psiAt B.ψ v ≠ 1 := GlobalTheory.PsiNontriv.psiAt_ne_one _ hstd v
  have hSplit := GlobalTheory.WeilM.IsUWeilPair.isUSplitting hTr.weil
  have hAE := (GlobalTheory.T.theta_action_exists hP) F E σ B a (a + a') G.V G.W G.M X.β (X.β / X.α) om _ _ _ _
    (GlobalTheory.ThK.Check.isPair_of_isTriple hTr).1 v
  have h1W : (1 : UA σ G.W.J) ∈ UAt σ G.W (evFin F v) := by
    intro u _
    simp [mat]

  have hex : ∀ φ : (Fin a × Fin (a + a') → Fv F v) → ℂ, ∃ φ₁ : (Fin a × Fin (a + a') → Fv F v) → ℂ,
      φ ∈ SB (Fin a × Fin (a + a') → Fv F v) → φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v) ∧
        Acts (evFin F v) (om (g, 1)) φ φ₁ := by
    intro φ
    by_cases hφ : φ ∈ SB (Fin a × Fin (a + a') → Fv F v)
    · obtain ⟨φ₁, h, -⟩ := hAE.1 g hg 1 h1W φ hφ
      exact ⟨φ₁, fun _ => h⟩
    · exact ⟨0, fun h => absurd h hφ⟩
  choose A hA using hex
  have huniq : ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v),
      Acts (evFin F v) (om (g, 1)) φ φ₁ → φ₁ = A φ := fun φ hφ φ₁ hφ₁ h =>
    (hAE.1 g hg 1 h1W φ hφ).unique ⟨hφ₁, h⟩ (hA φ hφ)
  have hASB : ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), A φ ∈ SB (Fin a × Fin (a + a') → Fv F v) :=
    fun φ hφ => (hA φ hφ).1
  have restA : ∀ φ r, φ ∈ SB (Fin a × Fin (a + a') → Fv F v) → Rest (evFin F v) φ r → Rest (evFin F v) (A φ) r :=
    fun φ r hφ hr => ⟨hr.1, by rw [← (hA φ hφ).2 r hr]; exact hSplit.pres _ _ hr.2⟩

  have hvac := hTr.geo.hM.vac v
  have hlin : ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ' ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ c : ℂ,
      A (c • φ + φ') = c • A φ + A φ' := by
    intro φ hφ φ' hφ' c
    refine GlobalTheory.T.eq_of_componentTensorAdelicFunction_eq v (G.M.vac v) _ _ hvac.1 fun r hr => ?_
    have hsum : c • φ + φ' ∈ SB (Fin a × Fin (a + a') → Fv F v) :=
      Submodule.add_mem _ (Submodule.smul_mem _ c hφ) hφ'
    have r0 := GlobalTheory.T.complementaryAdelicSchwartz_of_nonzero_local v _ _ r hvac.2.1 hsum hr
    have r1 := GlobalTheory.T.complementaryAdelicSchwartz_of_nonzero_local v _ _ r hvac.2.1 hφ hr
    have r2 := GlobalTheory.T.complementaryAdelicSchwartz_of_nonzero_local v _ _ r hvac.2.1 hφ' hr
    have et : ∀ (ψ₁ ψ₂ : (Fin a × Fin (a + a') → Fv F v) → ℂ), tens (evFin F v) (c • ψ₁ + ψ₂) r =
        c • tens (evFin F v) ψ₁ r + tens (evFin F v) ψ₂ r := fun ψ₁ ψ₂ => by
      funext x; simp only [tens, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
    rw [← (hA _ hsum).2 r r0, et, map_add, map_smul, (hA φ hφ).2 r r1, (hA φ' hφ').2 r r2, et]

  have hact : ∀ γ : Matrix (Fin a) (Fin (a + a')) (AE F E),
      actAB (cA σ) (g, (1 : UA σ G.W.J)) γ = mat g * γ := by
    intro γ
    simp [actAB, mat]
  have atMul : ∀ (M : Matrix (Fin a) (Fin a) (AE F E)) (γ : Matrix (Fin a) (Fin (a + a')) (AE F E)),
      At (evFin F v) γ → At (evFin F v) (M * γ) := by
    intro M γ hγ u hu
    rw [← Matrix.mul_smul, hγ u hu, Matrix.mul_zero]
  have hcov : ∀ γ : Matrix (Fin a) (Fin (a + a')) (AE F E), At (evFin F v) γ →
      ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v),
        A (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M.co v γ) φ) =
          schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M.co v (mat g * γ)) (A φ) := by
    intro γ hγ φ hφ
    have hw := GlobalTheory.SchrSB.schr_mem_SB B.ψ hstd.1 v (GlobalTheory.LatVac.locCo G.M.co v γ) φ hφ
    refine GlobalTheory.T.eq_of_componentTensorAdelicFunction_eq v φ _ _ hφ fun r hr => ?_
    have hb1 := GlobalTheory.VacBridge.rho_acts_locCo G.M.co B.ψ v γ hγ φ r hr
    have hRw : Rest (evFin F v) (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M.co v γ) φ) r :=
      ⟨hr.1, by rw [← hb1]; exact GlobalTheory.T.weil_representation_preserves_schwartz G.M B.ψ hstd γ _ hr.2⟩
    rw [← (hA _ hw).2 r hRw, ← hb1, hSplit.impl _ _ _ hr.2, (hA φ hφ).2 r hr, hact,
      GlobalTheory.VacBridge.rho_acts_locCo G.M.co B.ψ v _ (atMul _ γ hγ) (A φ) r (restA φ r hφ hr)]

  have hL := hι
  unfold GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model.IsLinW at hL
  simp only [inv_one, Units.val_one, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one] at hL
  have hsb : ∀ (w : (Fin a × Fin (a + a') → Fv F v) × (Fin a × Fin (a + a') → Fv F v)) (φ : (Fin a × Fin (a + a') → Fv F v) → ℂ),
      φ ∈ SB (Fin a × Fin (a + a') → Fv F v) → schr (GlobalTheory.LatVac.psiAt B.ψ v) w φ ∈ SB (Fin a × Fin (a + a') → Fv F v) :=
    fun w φ hφ => GlobalTheory.SchrSB.schr_mem_SB B.ψ hstd.1 v w φ hφ
  have hT : ∀ γ : Matrix (Fin a) (Fin (a + a')) (AE F E), At (evFin F v) γ → γ.map (piW (t.comp σ)) = 0 →
      ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ Y,
        ι (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M.co v γ) φ) Y = ι φ (Y + γ.map (piW t)) :=
    fun γ hγ h0 φ hφ Y => hL.trans γ hγ h0 φ hφ _ (hsb _ φ hφ) (GlobalTheory.VacBridge.rho_acts_locCo G.M.co B.ψ v γ hγ φ) Y
  have hM : ∀ γ : Matrix (Fin a) (Fin (a + a')) (AE F E), At (evFin F v) γ → γ.map (piW t) = 0 →
      ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ x : Matrix (Fin a) (Fin (a + a')) (AE F E), At (evFin F v) x →
        x.map (piW (t.comp σ)) = 0 →
        ι (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M.co v γ) φ) (x.map (piW t)) =
          B.ψ (symp (cA σ) (-1) (incM F G.V.J) (incM F G.W.J) x γ) * ι φ (x.map (piW t)) :=
    fun γ hγ h0 φ hφ x hx hx0 =>
      hL.mult γ hγ h0 φ hφ _ (hsb _ φ hφ) (GlobalTheory.VacBridge.rho_acts_locCo G.M.co B.ψ v γ hγ φ) x hx hx0

  choose U hUat hU0 hU1 using fun (P₀ P₁ : Matrix (Fin a) (Fin (a + a')) (Fv F v)) => GlobalTheory.T.exists_splitPlace_adelicMatrix_given_components hcm v t P₀ P₁

  set A' := G.V.J.map (t.comp σ) with hA'def
  set B' := G.W.J.map (t.comp σ) with hB'def
  have hsymp : ∀ x u : Matrix (Fin a) (Fin (a + a')) (AE F E), At (evFin F v) x → x.map (piW (t.comp σ)) = 0 →
      u.map (piW t) = 0 →
      B.ψ (symp (R := AF F) (cA σ) (-1) (incM F G.V.J) (incM F G.W.J) x u) =
        GlobalTheory.LatVac.psiAt B.ψ v (-(∑ k, ∑ l, (-(A' * x.map (piW t) * B'ᵀ)) k l * u.map (piW (t.comp σ)) k l)) := by
    intro x u hx hx0 hu1
    have hu1' : u.map (piW ((t.comp σ).comp σ)) = 0 := by rw [comp_conj_conj hcm]; exact hu1
    have e := GlobalTheory.T.hermitianTensor_skewHermitian_split_symplectic_pair hcm (t.comp σ) G.V.J G.W.J hTr.geo.hV.herm hTr.geo.hW.skew x u hx0 hu1'
    rw [comp_conj_conj hcm] at e
    unfold symp
    rw [GlobalTheory.T.adelicTrace_supportedAtSplitPlace hcm v (t.comp σ) _ (at_neg_hTens _ _ x u hx), comp_conj_conj hcm]
    rw [map_mul, map_mul, map_neg, map_neg, map_one, map_one, neg_one_mul, neg_one_mul, ← neg_add, e]
    rfl

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
  have hA' : IsUnit A'ᵀ.det := by
    have e : A'.det = ((t.comp σ : E →ₐ[F] Fv F v) : E →+* Fv F v) G.V.J.det := (RingHom.map_det _ _).symm
    rw [Matrix.det_transpose, e]
    exact isUnit_iff_ne_zero.2 fun h =>
      hdV (((t.comp σ : E →ₐ[F] Fv F v) : E →+* Fv F v).injective (by rw [map_zero]; exact h))
  have hB' : IsUnit B'.det := by
    have e : B'.det = ((t.comp σ : E →ₐ[F] Fv F v) : E →+* Fv F v) G.W.J.det := (RingHom.map_det _ _).symm
    rw [e]
    exact isUnit_iff_ne_zero.2 fun h =>
      hdW (((t.comp σ : E →ₐ[F] Fv F v) : E →+* Fv F v).injective (by rw [map_zero]; exact h))
  let Lm : (Matrix (Fin a) (Fin (a + a')) (Fv F v) →ₗ[Fv F v] Fv F v) → Matrix (Fin a) (Fin (a + a')) (Fv F v) :=
    fun l => Matrix.of fun k j => l (Matrix.single k j 1)
  have hchar : ∀ (l : Matrix (Fin a) (Fin (a + a')) (Fv F v) →ₗ[Fv F v] Fv F v) (Y : Matrix (Fin a) (Fin (a + a')) (Fv F v)),
      -(∑ k, ∑ j, (-(A' * Y * B'ᵀ)) k j * ((A'ᵀ)⁻¹ * Lm l * B'⁻¹) k j) = l Y := by
    intro l Y
    simp only [Matrix.neg_apply, neg_mul, Finset.sum_neg_distrib, neg_neg]
    rw [sum_conj_mul, linForm_sum l Y]
    have e : A'ᵀ * ((A'ᵀ)⁻¹ * Lm l * B'⁻¹) * B' = Lm l := by
      simp only [Matrix.mul_assoc]
      rw [Matrix.nonsing_inv_mul _ hB', Matrix.mul_one, Matrix.mul_nonsing_inv_cancel_left _ _ hA']
    rw [e]
    rfl

  set gt := (mat g).map (piW t) with hgt
  set gti := (mat g⁻¹).map (piW t) with hgti
  have hmatinv : mat g⁻¹ * mat g = 1 := by simp [mat]
  have hmatinv' : mat g * mat g⁻¹ = 1 := by simp [mat]
  have hgg : gti * gt = 1 := by
    rw [hgti, hgt, ← Matrix.map_mul, hmatinv, Matrix.map_one _ (map_zero _) (map_one _)]
  have hgg' : gt * gti = 1 := by
    rw [hgti, hgt, ← Matrix.map_mul, hmatinv', Matrix.map_one _ (map_zero _) (map_one _)]
  have hinv : gt⁻¹ = gti := Matrix.inv_eq_left_inv hgg
  have hU : (mat g)ᵀ * incM F G.V.J * (mat g).map (cA σ) = incM F G.V.J := g.2

  have h2lin : ∀ x ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ y ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ c : ℂ,
      (fun (Y : Matrix (Fin a) (Fin (a + a')) (Fv F v)) => ι (A (c • x + y)) (gt * Y)) = c • (fun (Y : Matrix (Fin a) (Fin (a + a')) (Fv F v)) => ι (A x) (gt * Y)) + (fun (Y : Matrix (Fin a) (Fin (a + a')) (Fv F v)) => ι (A y) (gt * Y)) := by
    intro x hx y hy c
    funext Y
    simp only [hlin x hx y hy c, map_add, map_smul, Pi.add_apply, Pi.smul_apply]
  have h2tr : ∀ C : Matrix (Fin a) (Fin (a + a')) (Fv F v), ∀ x ∈ SB (Fin a × Fin (a + a') → Fv F v),
      schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M.co v (U C 0)) x ∈ SB (Fin a × Fin (a + a') → Fv F v) ∧
      ι (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M.co v (U C 0)) x) = (fun Y => ι x (Y + C)) ∧
      (fun (Y : Matrix (Fin a) (Fin (a + a')) (Fv F v)) => ι (A (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M.co v (U C 0)) x)) (gt * Y)) =
        fun Y => ι (A x) (gt * (Y + C)) := by
    intro C x hx
    refine ⟨hsb _ x hx, ?_, ?_⟩
    · funext Y
      rw [hT _ (hUat C 0) (hU1 C 0) x hx Y, hU0]
    · funext Y
      have h0 : (mat g * U C 0).map (piW (t.comp σ)) = 0 := by
        rw [Matrix.map_mul, hU1, Matrix.mul_zero]
      rw [hcov _ (hUat C 0) x hx, hT _ (atMul _ _ (hUat C 0)) h0 (A x) (hASB x hx), Matrix.map_mul, hU0,
        Matrix.mul_add]
  have h2mu : ∀ (l : Matrix (Fin a) (Fin (a + a')) (Fv F v) →ₗ[Fv F v] Fv F v), ∀ x ∈ SB (Fin a × Fin (a + a') → Fv F v),
      schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M.co v (U 0 ((A'ᵀ)⁻¹ * Lm l * B'⁻¹))) x ∈
        SB (Fin a × Fin (a + a') → Fv F v) ∧
      ι (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M.co v (U 0 ((A'ᵀ)⁻¹ * Lm l * B'⁻¹))) x) =
        (fun Y => GlobalTheory.LatVac.psiAt B.ψ v (l Y) * ι x Y) ∧
      (fun (Y : Matrix (Fin a) (Fin (a + a')) (Fv F v)) => ι (A (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M.co v (U 0 ((A'ᵀ)⁻¹ * Lm l * B'⁻¹))) x))
          (gt * Y)) = fun Y => GlobalTheory.LatVac.psiAt B.ψ v (l Y) * ι (A x) (gt * Y) := by
    intro l x hx
    set P := (A'ᵀ)⁻¹ * Lm l * B'⁻¹ with hP
    refine ⟨hsb _ x hx, ?_, ?_⟩
    · funext Y
      have hm := hM (U 0 P) (hUat 0 P) (hU0 0 P) x hx (U Y 0) (hUat Y 0) (hU1 Y 0)
      rw [hU0] at hm
      rw [hm, hsymp _ _ (hUat Y 0) (hU1 Y 0) (hU0 0 P), hU0, hU1, hchar]
    · funext Y
      have h0 : (mat g * U 0 P).map (piW t) = 0 := by
        rw [Matrix.map_mul, hU0, Matrix.mul_zero]
      have hm := hM _ (atMul _ _ (hUat 0 P)) h0 (A x) (hASB x hx) (U (gt * Y) 0) (hUat (gt * Y) 0) (hU1 (gt * Y) 0)
      rw [hU0] at hm
      have hx' : symp (cA σ) (-1) (incM F G.V.J) (incM F G.W.J) (U (gt * Y) 0) (mat g * U 0 P) =
          symp (cA σ) (-1) (incM F G.V.J) (incM F G.W.J) (mat g⁻¹ * U (gt * Y) 0) (U 0 P) := by
        conv_lhs => rw [show U (gt * Y) 0 = mat g * (mat g⁻¹ * U (gt * Y) 0) by
          rw [← Matrix.mul_assoc, hmatinv', Matrix.one_mul]]
        exact symp_mul_mul _ _ _ _ _ hU _ _
      have h1 : (mat g⁻¹ * U (gt * Y) 0).map (piW (t.comp σ)) = 0 := by
        rw [Matrix.map_mul, hU1, Matrix.mul_zero]
      have h2 : (mat g⁻¹ * U (gt * Y) 0).map (piW t) = Y := by
        rw [Matrix.map_mul, hU0, ← hgti, ← Matrix.mul_assoc, hgg, Matrix.one_mul]
      rw [hcov _ (hUat 0 P) x hx, hm, hx', hsymp _ _ (atMul _ _ (hUat (gt * Y) 0)) h1 (hU0 0 P), h2, hU1, hchar]
  obtain ⟨c, hc⟩ := GlobalTheory.T.eq_smul_of_commute_heisenberg_linearModel_schwartzBruhat (SB (Fin a × Fin (a + a') → Fv F v)) (GlobalTheory.LatVac.psiAt B.ψ v) hψc hψ1 ι
    (fun φ (Y : Matrix (Fin a) (Fin (a + a')) (Fv F v)) => ι (A φ) (gt * Y)) hL.bij h2lin _ _ h2tr h2mu
  refine ⟨c, fun φ hφ φ₁ hφ₁ hact1 Y => ?_⟩
  rw [huniq φ hφ φ₁ hφ₁ hact1, hinv]
  have e := congrFun (hc φ hφ) (gti * Y)
  simp only [Pi.smul_apply, smul_eq_mul] at e
  rw [← Matrix.mul_assoc, hgg', Matrix.one_mul] at e
  exact e

end GlobalTheory.ShapeUV
