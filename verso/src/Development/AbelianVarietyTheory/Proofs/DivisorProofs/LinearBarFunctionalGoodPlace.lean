import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRk
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitDetOfCartan
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
import Development.AbelianVarietyTheory.Definitions.Divisors.PairsOfSquareTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartzStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHeisenbergActsByLocalSchrodingerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplementaryAdelicSchwartzRestFunctionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerPreservesSchwartzBruhat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharacterNontrivialAtPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqSmulOfCommuteHeisenbergLinearModelSchwartzBruhStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitPlaceAdelicMatrixGivenComponentsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicTraceSupportedAtSplitPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianTensorSkewHermitianSplitSymplecticPairStatement
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.WeilTransferW

/- English proof (translation)
Introduce `hP F E _ _ _ _ _ σ B a a' G X om om' hT v h hh`. Establish `hone : (1 : UA σ G.V'.J) ∈ UAt σ G.V' (evFin F v)` using `fun u _ => by simp [mat]`. Take `⟨hex, -, -⟩` from `GlobalTheory.T.theta_action_exists hP F E σ B a' (a + a') G.V' G.W G.M' X.α (X.α / X.β) om' G.q (a' - G.q) (a + a' - (G.p + G.q)) (G.p + G.q) (GlobalTheory.ThK.Inhab.pairV' hT) v`. Use `choose! S hS using fun φ (hφ : φ ∈ SB (Fin a' × Fin (a + a') → Fv F v)) => (hex 1 hone h hh φ hφ).exists`. Take `⟨R, hR0, hR⟩` from `GlobalTheory.T.exists_complementary_adelicSchwartz_restFunction (Fin a' × Fin (a + a')) v`.

Establish `eqR : ∀ φ₁ φ₂ : (Fin a' × Fin (a + a') → Fv F v) → ℂ, tens (evFin F v) φ₁ R = tens (evFin F v) φ₂ R → φ₁ = φ₂`. Introduce `φ₁ φ₂ e0`. Establish `hRc` using `(hR 0 (Submodule.zero_mem _)).1`. Use function extensionality and compare the values at `y`. Establish `hp : At (evFin F v) (fun i => GlobalTheory.LatVac.liftV v (y i))` using `fun u hu => funext fun i => GlobalTheory.LatVac.at_liftV v _ u hu`.

Establish `e` using `congrFun e0 (fun i => GlobalTheory.LatVac.liftV v (y i))`. Establish `e2 : R (fun i => GlobalTheory.LatVac.liftV v (y i)) = R 0` using `by simpa using hRc 0 _ hp`. Simplify using `only [tens, GlobalTheory.LatVac.evFin_liftV, e2] at e`. Conclude with `mul_right_cancel₀ hR0 e`. Establish `hSR : ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), om' (1, h) (tens (evFin F v) φ R) = tens (evFin F v) (S φ) R` using `fun φ hφ => (hS φ hφ).2 R (hR φ hφ)`.

Establish `tensLin : ∀ (c : ℂ) (φ φ' : (Fin a' × Fin (a + a') → Fv F v) → ℂ), tens (evFin F v) (c • φ + φ') R = c • tens (evFin F v) φ R + tens (evFin F v) φ' R`. Introduce `c φ φ'`. Use function extensionality and compare the values at `x`. Simplify using `only [tens, Pi.add_apply, Pi.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hSplit` using `GlobalTheory.WeilM.IsUWeilPair.isUSplitting hT.weil'`. Establish `atAct : ∀ (γ : Matrix (Fin a') (Fin (a + a')) (AE F E)), At (evFin F v) γ → At (evFin F v) (GlobalTheory.WeilM.actAB (cA σ) ((1 : UA σ G.V'.J), h) γ)`. Introduce `γ hγ u hu`. Simplify using `only [GlobalTheory.WeilM.actAB]`. Rewrite using `[← Matrix.smul_mul, ← Matrix.mul_smul, hγ u hu, Matrix.mul_zero, Matrix.zero_mul]`.

Establish `restS : ∀ φ r, φ ∈ SB (Fin a' × Fin (a + a') → Fv F v) → Rest (evFin F v) φ r → Rest (evFin F v) (S φ) r` using `fun φ r hφ hr => ⟨hr.1, by rw [← (hS φ hφ).2 r hr]; exact hSplit.pres _ _ hr.2⟩`. Use `⟨S, hS, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `φ hφ φ' hφ' c`. Establish `hm : c • φ + φ' ∈ SB (Fin a' × Fin (a + a') → Fv F v)` using `Submodule.add_mem _ (Submodule.smul_mem _ c hφ) hφ'`. Apply `eqR` to reduce the goal to its premises.

Rewrite using `[← hSR _ hm, tensLin, map_add, map_smul, hSR φ hφ, hSR φ' hφ', tensLin]`. Introduce `γ hγ φ hφ`. Establish `hw` using `GlobalTheory.SchrSB.schr_mem_SB B.ψ hT.base.std.1 v (GlobalTheory.LatVac.locCo G.M'.co v γ) φ hφ`. Use `GlobalTheory.T.eq_of_componentTensorAdelicFunction_eq v φ _ _ hφ fun r hr => ?_` and prove the remaining obligations. Establish `hb1` using `GlobalTheory.T.adelicHeisenberg_acts_by_local_schrodinger G.M'.co B.ψ v γ hγ φ r hr`.

Establish `hRw : Rest (evFin F v) (GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M'.co v γ) φ) r` using `⟨hr.1, by rw [← hb1]; exact GlobalTheory.T.weil_representation_preserves_schwartz G.M' B.ψ hT.base.std γ _ hr.2⟩`. Rewrite using `[← (hS _ hw).2 r hRw, ← hb1, hSplit.impl _ _ _ hr.2, (hS φ hφ).2 r hr, GlobalTheory.T.adelicHeisenberg_acts_by_local_schrodinger G.M'.co B.ψ v _ (atAct γ hγ) (S φ) r (restS φ r hφ hr)]`. Introduce `φ hφ h0`. Apply `eqR φ 0` to reduce the goal to its premises. Establish `e1 : om' (1, h⁻¹) (om' (1, h) (tens (evFin F v) φ R)) = tens (evFin F v) φ R`.

Rewrite using `[← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, one_mul, inv_mul_cancel]`. Rewrite using `[show ((1 : UA σ G.V'.J), (1 : UA σ G.W.J)) = 1 from rfl, map_one, Module.End.one_apply]`. Establish `t0 : tens (evFin F v) (0 : (Fin a' × Fin (a + a') → Fv F v) → ℂ) R = 0`. Use function extensionality and compare the values at `x`. Simplify using `[tens]`.

Rewrite `e1` using `[hSR φ hφ, h0, t0, map_zero]`. Rewrite using `[← e1, t0]`.
-/
theorem local_weil_operator_second_space : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (h : UA σ G.W.J), h ∈ UAt σ G.W (evFin F v) →
    ∃ S : ((Fin a' × Fin (a + a') → Fv F v) → ℂ) → (Fin a' × Fin (a + a') → Fv F v) → ℂ,
      (∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), S φ ∈ SB (Fin a' × Fin (a + a') → Fv F v) ∧
        Acts (evFin F v) (om' (1, h)) φ (S φ)) ∧
      (∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), ∀ φ' ∈ SB (Fin a' × Fin (a + a') → Fv F v), ∀ c : ℂ,
        S (c • φ + φ') = c • S φ + S φ') ∧
      (∀ γ : Matrix (Fin a') (Fin (a + a')) (AE F E), At (evFin F v) γ → ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v),
        S (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M'.co v γ) φ) =
          schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M'.co v (actAB (cA σ) ((1 : UA σ G.V'.J), h) γ)) (S φ)) ∧
      (∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), S φ = 0 → φ = 0) := by
  intro hP F E _ _ _ _ _ σ B a a' G X om om' hT v h hh
  have hone : (1 : UA σ G.V'.J) ∈ UAt σ G.V' (evFin F v) := fun u _ => by simp [mat]
  obtain ⟨hex, -, -⟩ := GlobalTheory.T.theta_action_exists hP F E σ B a' (a + a') G.V' G.W G.M' X.α (X.α / X.β) om' G.q (a' - G.q)
    (a + a' - (G.p + G.q)) (G.p + G.q) (GlobalTheory.ThK.Inhab.pairV' hT) v
  choose! S hS using fun φ (hφ : φ ∈ SB (Fin a' × Fin (a + a') → Fv F v)) => (hex 1 hone h hh φ hφ).exists
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.T.exists_complementary_adelicSchwartz_restFunction (Fin a' × Fin (a + a')) v
  have eqR : ∀ φ₁ φ₂ : (Fin a' × Fin (a + a') → Fv F v) → ℂ, tens (evFin F v) φ₁ R = tens (evFin F v) φ₂ R → φ₁ = φ₂ := by
    intro φ₁ φ₂ e0
    have hRc := (hR 0 (Submodule.zero_mem _)).1
    funext y
    have hp : At (evFin F v) (fun i => GlobalTheory.LatVac.liftV v (y i)) := fun u hu => funext fun i => GlobalTheory.LatVac.at_liftV v _ u hu
    have e := congrFun e0 (fun i => GlobalTheory.LatVac.liftV v (y i))
    have e2 : R (fun i => GlobalTheory.LatVac.liftV v (y i)) = R 0 := by simpa using hRc 0 _ hp
    simp only [tens, GlobalTheory.LatVac.evFin_liftV, e2] at e
    exact mul_right_cancel₀ hR0 e
  have hSR : ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), om' (1, h) (tens (evFin F v) φ R) = tens (evFin F v) (S φ) R :=
    fun φ hφ => (hS φ hφ).2 R (hR φ hφ)
  have tensLin : ∀ (c : ℂ) (φ φ' : (Fin a' × Fin (a + a') → Fv F v) → ℂ),
      tens (evFin F v) (c • φ + φ') R = c • tens (evFin F v) φ R + tens (evFin F v) φ' R := by
    intro c φ φ'; funext x; simp only [tens, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  have hSplit := GlobalTheory.WeilM.IsUWeilPair.isUSplitting hT.weil'
  have atAct : ∀ (γ : Matrix (Fin a') (Fin (a + a')) (AE F E)), At (evFin F v) γ →
      At (evFin F v) (GlobalTheory.WeilM.actAB (cA σ) ((1 : UA σ G.V'.J), h) γ) := by
    intro γ hγ u hu
    simp only [GlobalTheory.WeilM.actAB]
    rw [← Matrix.smul_mul, ← Matrix.mul_smul, hγ u hu, Matrix.mul_zero, Matrix.zero_mul]
  have restS : ∀ φ r, φ ∈ SB (Fin a' × Fin (a + a') → Fv F v) → Rest (evFin F v) φ r → Rest (evFin F v) (S φ) r :=
    fun φ r hφ hr => ⟨hr.1, by rw [← (hS φ hφ).2 r hr]; exact hSplit.pres _ _ hr.2⟩
  refine ⟨S, hS, ?_, ?_, ?_⟩
  · intro φ hφ φ' hφ' c
    have hm : c • φ + φ' ∈ SB (Fin a' × Fin (a + a') → Fv F v) := Submodule.add_mem _ (Submodule.smul_mem _ c hφ) hφ'
    apply eqR
    rw [← hSR _ hm, tensLin, map_add, map_smul, hSR φ hφ, hSR φ' hφ', tensLin]
  · intro γ hγ φ hφ
    have hw := GlobalTheory.SchrSB.schr_mem_SB B.ψ hT.base.std.1 v (GlobalTheory.LatVac.locCo G.M'.co v γ) φ hφ
    refine GlobalTheory.T.eq_of_componentTensorAdelicFunction_eq v φ _ _ hφ fun r hr => ?_
    have hb1 := GlobalTheory.T.adelicHeisenberg_acts_by_local_schrodinger G.M'.co B.ψ v γ hγ φ r hr
    have hRw : Rest (evFin F v) (GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M'.co v γ) φ) r :=
      ⟨hr.1, by rw [← hb1]; exact GlobalTheory.T.weil_representation_preserves_schwartz G.M' B.ψ hT.base.std γ _ hr.2⟩
    rw [← (hS _ hw).2 r hRw, ← hb1, hSplit.impl _ _ _ hr.2, (hS φ hφ).2 r hr,
      GlobalTheory.T.adelicHeisenberg_acts_by_local_schrodinger G.M'.co B.ψ v _ (atAct γ hγ) (S φ) r (restS φ r hφ hr)]
  · intro φ hφ h0
    apply eqR φ 0
    have e1 : om' (1, h⁻¹) (om' (1, h) (tens (evFin F v) φ R)) = tens (evFin F v) φ R := by
      rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, one_mul, inv_mul_cancel]
      rw [show ((1 : UA σ G.V'.J), (1 : UA σ G.W.J)) = 1 from rfl, map_one, Module.End.one_apply]
    have t0 : tens (evFin F v) (0 : (Fin a' × Fin (a + a') → Fv F v) → ℂ) R = 0 := by
      funext x; simp [tens]
    rw [hSR φ hφ, h0, t0, map_zero] at e1
    rw [← e1, t0]

/- English proof (translation)
Introduce `r hr`. Establish `h : ∀ i j, r • x i j = 0` using `fun i j => by`. Use `congrFun (congrFun (hx r hr) i) j` as an intermediate fact. Simplify using `using this`. Rewrite using `[← mul_smul_comm]`.

Unfold `hTens`. Simplify using `only [Finset.smul_sum, ← smul_mul_assoc, h, zero_mul, Finset.sum_const_zero, mul_zero]`.
-/
theorem atHTens {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
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
Use `conv_lhs => rw [Y.matrix_eq_sum_single]`. Simplify using `only [map_sum]`. Use `Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[show Matrix.single k j (Y k j) = Y k j • Matrix.single k j (1 : K) by`. Rewrite using `[Matrix.smul_single, smul_eq_mul, mul_one], map_smul, smul_eq_mul]`.
-/
theorem sumLinForm {K : Type} [Field K] {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (l : Matrix m n K →ₗ[K] K) (Y : Matrix m n K) :
    l Y = ∑ k, ∑ j, Y k j * l (Matrix.single k j 1) := by
  conv_lhs => rw [Y.matrix_eq_sum_single]
  simp only [map_sum]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
  rw [show Matrix.single k j (Y k j) = Y k j • Matrix.single k j (1 : K) by
    rw [Matrix.smul_single, smul_eq_mul, mul_one], map_smul, smul_eq_mul]

/- English proof (translation)
Simplify using `only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring` and prove the remaining obligations.
-/
theorem sumMulRight {K : Type} [CommRing K] {m n : Type} [Fintype m] [Fintype n]
    (g : Matrix n n K) (Y L : Matrix m n K) :
    ∑ k, ∑ j, (Y * g) k j * L k j = ∑ k, ∑ j, Y k j * (L * gᵀ) k j := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B a a' G X om om' hT v t h g hh ht hts S hSB hlin hcov ι hι`. Establish `hcm : IsCMExt F E σ` using `hT.base.cm`. Establish `hstd` using `hT.base.std`. Take `⟨w⟩ : Nonempty (InfinitePlace F)` from `inferInstance`. Use `set A := G.V'.J.map t with hAdef`.

Use `set Bm := G.W.J.map t with hBdef`. Establish `hA : IsUnit A.det` using `GlobalTheory.SplitUnitLift.isUnit_det_of_cartan G.V'.J t (B.emb w).1 1 one_ne_zero (G.V'.θ w) (by rw [one_smul]; exact hT.geo.hV'.cartan w)`. Establish `hBm : IsUnit Bm.det` using `GlobalTheory.SplitUnitLift.isUnit_det_of_cartan G.W.J t (B.emb w).1 Complex.I Complex.I_ne_zero (G.W.θ w) (hT.geo.hW.cartan w)`. Establish `hB : IsUnit Bmᵀ.det` using `by rw [Matrix.det_transpose]; exact hBm`. Use `choose U hUat hU0 hU1 using fun (P₀ P₁ : Matrix (Fin a') (Fin (a + a')) (Fv F v)) => GlobalTheory.T.exists_splitPlace_adelicMatrix_given_components hcm v t P₀ P₁`.

Set `Pm : Matrix (Fin a') (Fin (a + a')) (Fv F v) → Matrix (Fin a') (Fin (a + a')) (Fv F v)` to `fun C => -(A⁻¹ * C * (Bmᵀ)⁻¹)`. Set `Lm : (Matrix (Fin a') (Fin (a + a')) (Fv F v) →ₗ[Fv F v] Fv F v) → Matrix (Fin a') (Fin (a + a')) (Fv F v)` to `fun l => Matrix.of fun k j => l (Matrix.single k j 1)`. Establish `hcoP : ∀ C, -(A * (U 0 (Pm C)).map (piW (t.comp σ)) * Bmᵀ) = C`. Introduce `C`. Rewrite using `[hU1]`.

Simplify using `only [Pm, Matrix.mul_neg, Matrix.neg_mul, neg_neg, Matrix.mul_assoc]`. Rewrite using `[Matrix.nonsing_inv_mul _ hB, Matrix.mul_one, Matrix.mul_nonsing_inv_cancel_left _ _ hA]`. Establish `hsymp : ∀ x u : Matrix (Fin a') (Fin (a + a')) (AE F E), At (evFin F v) x → x.map (piW t) = 0 → u.map (piW (t.comp σ)) = 0 → B.ψ (symp (R` using `AF F) (cA σ) (-1) (incM F G.V'.J) (incM F G.W.J) x u) = GlobalTheory.LatVac.psiAt B.ψ v (-(∑ k, ∑ j, (-(A * x.map (piW (t.comp σ)) * Bmᵀ)) k j * u.map (piW t) k j)) := by`. Introduce `x u hx hx0 hu1`. Unfold `symp`.

Rewrite using `[GlobalTheory.T.adelicTrace_supportedAtSplitPlace hcm v t _ (atHTens _ _ x u hx)]`. Rewrite using `[map_mul, map_mul, map_neg, map_neg, map_one, map_one, neg_one_mul, neg_one_mul, ← neg_add, GlobalTheory.T.hermitianTensor_skewHermitian_split_symplectic_pair hcm t G.V'.J G.W.J hT.geo.hV'.herm hT.geo.hW.skew x u hx0 hu1]`. Both sides reduce to the same expression. Establish `hL` using `hι`. Unfold `Model.IsLinBar at hL`.

Simplify using `only [Units.val_one, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one] at hL`. Establish `htr` using `hL.trans`. Establish `hmu` using `hL.mult`. Establish `hact : ∀ u : Matrix (Fin a') (Fin (a + a')) (AE F E), actAB (cA σ) ((1 : UA σ G.V'.J), h) u = u * (mat h)ᵀ`. Introduce `u`.

Simplify using `[actAB, mat]`. Establish `hat : ∀ u : Matrix (Fin a') (Fin (a + a')) (AE F E), At (evFin F v) u → At (evFin F v) (u * (mat h)ᵀ)`. Introduce `u hu r hr`. Rewrite using `[← Matrix.smul_mul, hu r hr, Matrix.zero_mul]`. Establish `hmap : ∀ (u : Matrix (Fin a') (Fin (a + a')) (AE F E)) (s : E →ₐ[F] Fv F v), (u * (mat h)ᵀ).map (piW s) = u.map (piW s) * ((mat h).map (piW s))ᵀ`.

Introduce `u s`. Rewrite using `[Matrix.map_mul, Matrix.transpose_map]`. Establish `hbr` using `fun (γ : Matrix (Fin a') (Fin (a + a')) (AE F E)) hγ (φ : (Fin a' × Fin (a + a') → Fv F v) → ℂ) => GlobalTheory.T.adelicHeisenberg_acts_by_local_schrodinger G.M'.co B.ψ v γ hγ φ`. Establish `hsb` using `fun (w : (Fin a' × Fin (a + a') → Fv F v) × (Fin a' × Fin (a + a') → Fv F v)) (φ : (Fin a' × Fin (a + a') → Fv F v) → ℂ) (hφ : φ ∈ SB _) => GlobalTheory.SchrSB.schr_mem_SB B.ψ hstd.1 v w φ hφ`. Establish `c1 : ∀ C, ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), ι (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M'.co v (U 0 (Pm C))) φ) = fun Y => ι φ (Y + C)`.

Introduce `C φ hφ`. Use function extensionality and compare the values at `Y`. Rewrite using `[htr (U 0 (Pm C)) (hUat 0 (Pm C)) (hU0 0 (Pm C)) φ hφ _ (hsb _ φ hφ) (hbr _ (hUat 0 (Pm C)) φ) Y, hcoP]`. Establish `c2 : ∀ l, ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), ι (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M'.co v (U (-Lm l) 0)) φ) = fun Y => GlobalTheory.LatVac.psiAt B.ψ v (l Y) * ι φ Y`. Introduce `l φ hφ`.

Use function extensionality and compare the values at `Y`. Establish `hm` using `hmu (U (-Lm l) 0) (hUat (-Lm l) 0) (hU1 (-Lm l) 0) φ hφ _ (hsb _ φ hφ) (hbr _ (hUat (-Lm l) 0) φ) (U 0 (Pm Y)) (hUat 0 (Pm Y)) (hU0 0 (Pm Y))`. Rewrite `hm` using `[hcoP]`. Rewrite using `[hm, hsymp _ _ (hUat 0 (Pm Y)) (hU0 0 (Pm Y)) (hU1 (-Lm l) 0), hcoP, hU0, sumLinForm l Y]`. Use `congr 2`.

Simplify using `[Lm, Finset.sum_neg_distrib]`. Establish `c3 : ∀ C, ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), ι (S (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M'.co v (U 0 (Pm C))) φ)) = fun Y => ι (S φ) (Y + C * ((g⁻¹ : GL (Fin (a + a')) (Fv F v)).val))`. Introduce `C φ hφ`. Use function extensionality and compare the values at `Y`. Rewrite using `[hcov _ (hUat 0 (Pm C)) φ hφ, hact]`.

Establish `hat'` using `hat _ (hUat 0 (Pm C))`. Rewrite using `[htr _ hat' (by rw [hmap, hU0, Matrix.zero_mul]) _ (hSB φ hφ) _ (hsb _ _ (hSB φ hφ)) (hbr _ hat' _) Y]`. Use `congrArg (fun Z => ι (S φ) (Y + Z)) ?_` and prove the remaining obligations. Rewrite using `[hmap, hts, hU1]`. Use `show -(A * (-(A⁻¹ * C * (Bmᵀ)⁻¹) * (Bm⁻¹ * ((g⁻¹ : GL (Fin (a + a')) (Fv F v)).val)ᵀ * Bm)ᵀ) * Bmᵀ) = _`.

Rewrite using `[Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_nonsing_inv]`. Simplify using `only [Matrix.mul_neg, Matrix.neg_mul, neg_neg, Matrix.mul_assoc]`. Rewrite using `[Matrix.nonsing_inv_mul _ hB, Matrix.mul_one, Matrix.nonsing_inv_mul_cancel_left _ _ hB, Matrix.mul_nonsing_inv_cancel_left _ _ hA]`. Establish `c4 : ∀ l, ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), ι (S (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M'.co v (U (-Lm l) 0)) φ)) = fun Y => GlobalTheory.LatVac.psiAt B.ψ v (l (Y * g.val)) * ι (S φ) Y`. Introduce `l φ hφ`.

Use function extensionality and compare the values at `Y`. Rewrite using `[hcov _ (hUat (-Lm l) 0) φ hφ, hact]`. Establish `hat'` using `hat _ (hUat (-Lm l) 0)`. Establish `h1 : (U (-Lm l) 0 * (mat h)ᵀ).map (piW (t.comp σ)) = 0` using `by rw [hmap, hU1, Matrix.zero_mul]`. Establish `hm` using `hmu _ hat' h1 _ (hSB φ hφ) _ (hsb _ _ (hSB φ hφ)) (hbr _ hat' _) (U 0 (Pm Y)) (hUat 0 (Pm Y)) (hU0 0 (Pm Y))`.

Rewrite `hm` using `[hcoP]`. Rewrite using `[hm, hsymp _ _ (hUat 0 (Pm Y)) (hU0 0 (Pm Y)) h1, hcoP, hmap, ht, hU0, sumLinForm l]`. Use `congr 2`. Rewrite using `[show (∑ k, ∑ j, (Y * g.val) k j * l (Matrix.single k j 1)) = ∑ k, ∑ j, (Y * g.val) k j * Lm l k j from rfl, sumMulRight]`. Simplify using `[Matrix.neg_mul, Finset.sum_neg_distrib]`.

Take `⟨c, hc⟩` from `GlobalTheory.T.eq_smul_of_commute_heisenberg_linearModel_schwartzBruhat (SB (Fin a' × Fin (a + a') → Fv F v)) (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.SchrSB.continuous_psiAt B.ψ hstd.1 v) (GlobalTheory.PsiNontriv.psiAt_ne_one B.ψ hstd v) ι (fun φ Y => ι (S φ) (Y * ((g⁻¹ : …`. Use function extensionality and compare the values at `Y`. Simplify using `only [hlin x hx y hy c, map_add, map_smul, Pi.add_apply, Pi.smul_apply])`. Use the proof step `(fun C => schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M'.co v (U 0 (Pm C))))`. Use the proof step `(fun l => schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M'.co v (U (-Lm l) 0)))`.

Use the proof step `(fun C x hx => ⟨hsb _ x hx, c1 C x hx, by`. Use function extensionality and compare the values at `Y`. Use `show ι (S _) (Y * ((g⁻¹ : GL (Fin (a + a')) (Fv F v)).val)) = ι (S x) ((Y + C) * ((g⁻¹ : GL (Fin (a + a')) (Fv F v)).val))`. Rewrite using `[c3 C x hx, Matrix.add_mul]⟩)`. Use the proof step `(fun l x hx => ⟨hsb _ x hx, c2 l x hx, by`.

Use function extensionality and compare the values at `Y`. Use `show ι (S _) (Y * ((g⁻¹ : GL (Fin (a + a')) (Fv F v)).val)) = GlobalTheory.LatVac.psiAt B.ψ v (l Y) * ι (S x) (Y * ((g⁻¹ : GL (Fin (a + a')) (Fv F v)).val))`. Rewrite using `[c4 l x hx]`. Use `beta_reduce`. Rewrite using `[Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]⟩)`.

Use `⟨c, fun φ hφ => funext fun Y => ?_⟩` and prove the remaining obligations. Establish `e` using `congrFun (hc φ hφ) (Y * g.val)`. Simplify using `only [Pi.smul_apply] at e`. Rewrite `e` using `[Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]`. Rewrite using `[Pi.smul_apply]`.

Conclude with `e`.
-/
theorem linBar_right_mul : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (t : E →ₐ[F] Fv F v) (h : UA σ G.W.J) (g : GL (Fin (a + a')) (Fv F v)), h ∈ UAt σ G.W (evFin F v) →
    (mat h).map (piW t) = g.val →
    (mat h).map (piW (t.comp σ)) = (G.W.J.map t)⁻¹ * ((g⁻¹ : GL (Fin (a + a')) (Fv F v)).val)ᵀ * G.W.J.map t →
    ∀ S : ((Fin a' × Fin (a + a') → Fv F v) → ℂ) → (Fin a' × Fin (a + a') → Fv F v) → ℂ,
      (∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), S φ ∈ SB (Fin a' × Fin (a + a') → Fv F v)) →
      (∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), ∀ φ' ∈ SB (Fin a' × Fin (a + a') → Fv F v), ∀ c : ℂ,
        S (c • φ + φ') = c • S φ + S φ') →
      (∀ γ : Matrix (Fin a') (Fin (a + a')) (AE F E), At (evFin F v) γ → ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v),
        S (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M'.co v γ) φ) =
          schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M'.co v (actAB (cA σ) ((1 : UA σ G.V'.J), h) γ)) (S φ)) →
      ∀ ι : ((Fin a' × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin a') (Fin (a + a')) (Fv F v) → ℂ),
        G.M'.IsLinBar B.ψ t 1 1 ι →
        ∃ c : ℂ, ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), ι (S φ) = c • fun Y => ι φ (Y * g.val) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v t h g hh ht hts S hSB hlin hcov ι hι
  have hcm : IsCMExt F E σ := hT.base.cm
  have hstd := hT.base.std
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  set A := G.V'.J.map t with hAdef
  set Bm := G.W.J.map t with hBdef
  have hA : IsUnit A.det := GlobalTheory.SplitUnitLift.isUnit_det_of_cartan G.V'.J t (B.emb w).1 1 one_ne_zero (G.V'.θ w)
    (by rw [one_smul]; exact hT.geo.hV'.cartan w)
  have hBm : IsUnit Bm.det := GlobalTheory.SplitUnitLift.isUnit_det_of_cartan G.W.J t (B.emb w).1 Complex.I Complex.I_ne_zero
    (G.W.θ w) (hT.geo.hW.cartan w)
  have hB : IsUnit Bmᵀ.det := by rw [Matrix.det_transpose]; exact hBm
  choose U hUat hU0 hU1 using fun (P₀ P₁ : Matrix (Fin a') (Fin (a + a')) (Fv F v)) =>
    GlobalTheory.T.exists_splitPlace_adelicMatrix_given_components hcm v t P₀ P₁
  let Pm : Matrix (Fin a') (Fin (a + a')) (Fv F v) → Matrix (Fin a') (Fin (a + a')) (Fv F v) :=
    fun C => -(A⁻¹ * C * (Bmᵀ)⁻¹)
  let Lm : (Matrix (Fin a') (Fin (a + a')) (Fv F v) →ₗ[Fv F v] Fv F v) →
      Matrix (Fin a') (Fin (a + a')) (Fv F v) := fun l => Matrix.of fun k j => l (Matrix.single k j 1)
  have hcoP : ∀ C, -(A * (U 0 (Pm C)).map (piW (t.comp σ)) * Bmᵀ) = C := by
    intro C
    rw [hU1]
    simp only [Pm, Matrix.mul_neg, Matrix.neg_mul, neg_neg, Matrix.mul_assoc]
    rw [Matrix.nonsing_inv_mul _ hB, Matrix.mul_one, Matrix.mul_nonsing_inv_cancel_left _ _ hA]
  have hsymp : ∀ x u : Matrix (Fin a') (Fin (a + a')) (AE F E), At (evFin F v) x → x.map (piW t) = 0 →
      u.map (piW (t.comp σ)) = 0 →
      B.ψ (symp (R := AF F) (cA σ) (-1) (incM F G.V'.J) (incM F G.W.J) x u) =
        GlobalTheory.LatVac.psiAt B.ψ v
          (-(∑ k, ∑ j, (-(A * x.map (piW (t.comp σ)) * Bmᵀ)) k j * u.map (piW t) k j)) := by
    intro x u hx hx0 hu1
    unfold symp
    rw [GlobalTheory.T.adelicTrace_supportedAtSplitPlace hcm v t _ (atHTens _ _ x u hx)]
    rw [map_mul, map_mul, map_neg, map_neg, map_one, map_one, neg_one_mul, neg_one_mul, ← neg_add,
      GlobalTheory.T.hermitianTensor_skewHermitian_split_symplectic_pair hcm t G.V'.J G.W.J hT.geo.hV'.herm hT.geo.hW.skew x u hx0 hu1]
    rfl

  have hL := hι
  unfold Model.IsLinBar at hL
  simp only [Units.val_one, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one] at hL
  have htr := hL.trans
  have hmu := hL.mult
  have hact : ∀ u : Matrix (Fin a') (Fin (a + a')) (AE F E), actAB (cA σ) ((1 : UA σ G.V'.J), h) u = u * (mat h)ᵀ := by
    intro u; simp [actAB, mat]
  have hat : ∀ u : Matrix (Fin a') (Fin (a + a')) (AE F E), At (evFin F v) u → At (evFin F v) (u * (mat h)ᵀ) := by
    intro u hu r hr
    rw [← Matrix.smul_mul, hu r hr, Matrix.zero_mul]
  have hmap : ∀ (u : Matrix (Fin a') (Fin (a + a')) (AE F E)) (s : E →ₐ[F] Fv F v),
      (u * (mat h)ᵀ).map (piW s) = u.map (piW s) * ((mat h).map (piW s))ᵀ := by
    intro u s; rw [Matrix.map_mul, Matrix.transpose_map]
  have hbr := fun (γ : Matrix (Fin a') (Fin (a + a')) (AE F E)) hγ (φ : (Fin a' × Fin (a + a') → Fv F v) → ℂ) =>
    GlobalTheory.T.adelicHeisenberg_acts_by_local_schrodinger G.M'.co B.ψ v γ hγ φ
  have hsb := fun (w : (Fin a' × Fin (a + a') → Fv F v) × (Fin a' × Fin (a + a') → Fv F v))
    (φ : (Fin a' × Fin (a + a') → Fv F v) → ℂ) (hφ : φ ∈ SB _) => GlobalTheory.SchrSB.schr_mem_SB B.ψ hstd.1 v w φ hφ
  have c1 : ∀ C, ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v),
      ι (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M'.co v (U 0 (Pm C))) φ) = fun Y => ι φ (Y + C) := by
    intro C φ hφ
    funext Y
    rw [htr (U 0 (Pm C)) (hUat 0 (Pm C)) (hU0 0 (Pm C)) φ hφ _ (hsb _ φ hφ) (hbr _ (hUat 0 (Pm C)) φ) Y, hcoP]
  have c2 : ∀ l, ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v),
      ι (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M'.co v (U (-Lm l) 0)) φ) =
        fun Y => GlobalTheory.LatVac.psiAt B.ψ v (l Y) * ι φ Y := by
    intro l φ hφ
    funext Y
    have hm := hmu (U (-Lm l) 0) (hUat (-Lm l) 0) (hU1 (-Lm l) 0) φ hφ _ (hsb _ φ hφ) (hbr _ (hUat (-Lm l) 0) φ)
      (U 0 (Pm Y)) (hUat 0 (Pm Y)) (hU0 0 (Pm Y))
    rw [hcoP] at hm
    rw [hm, hsymp _ _ (hUat 0 (Pm Y)) (hU0 0 (Pm Y)) (hU1 (-Lm l) 0), hcoP, hU0, sumLinForm l Y]
    congr 2
    simp [Lm, Finset.sum_neg_distrib]
  have c3 : ∀ C, ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v),
      ι (S (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M'.co v (U 0 (Pm C))) φ)) =
        fun Y => ι (S φ) (Y + C * ((g⁻¹ : GL (Fin (a + a')) (Fv F v)).val)) := by
    intro C φ hφ
    funext Y
    rw [hcov _ (hUat 0 (Pm C)) φ hφ, hact]
    have hat' := hat _ (hUat 0 (Pm C))
    rw [htr _ hat' (by rw [hmap, hU0, Matrix.zero_mul]) _ (hSB φ hφ) _ (hsb _ _ (hSB φ hφ)) (hbr _ hat' _) Y]
    refine congrArg (fun Z => ι (S φ) (Y + Z)) ?_
    rw [hmap, hts, hU1]
    show -(A * (-(A⁻¹ * C * (Bmᵀ)⁻¹) * (Bm⁻¹ * ((g⁻¹ : GL (Fin (a + a')) (Fv F v)).val)ᵀ * Bm)ᵀ) * Bmᵀ) = _
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_nonsing_inv]
    simp only [Matrix.mul_neg, Matrix.neg_mul, neg_neg, Matrix.mul_assoc]
    rw [Matrix.nonsing_inv_mul _ hB, Matrix.mul_one, Matrix.nonsing_inv_mul_cancel_left _ _ hB,
      Matrix.mul_nonsing_inv_cancel_left _ _ hA]
  have c4 : ∀ l, ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v),
      ι (S (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M'.co v (U (-Lm l) 0)) φ)) =
        fun Y => GlobalTheory.LatVac.psiAt B.ψ v (l (Y * g.val)) * ι (S φ) Y := by
    intro l φ hφ
    funext Y
    rw [hcov _ (hUat (-Lm l) 0) φ hφ, hact]
    have hat' := hat _ (hUat (-Lm l) 0)
    have h1 : (U (-Lm l) 0 * (mat h)ᵀ).map (piW (t.comp σ)) = 0 := by rw [hmap, hU1, Matrix.zero_mul]
    have hm := hmu _ hat' h1 _ (hSB φ hφ) _ (hsb _ _ (hSB φ hφ)) (hbr _ hat' _) (U 0 (Pm Y)) (hUat 0 (Pm Y)) (hU0 0 (Pm Y))
    rw [hcoP] at hm
    rw [hm, hsymp _ _ (hUat 0 (Pm Y)) (hU0 0 (Pm Y)) h1, hcoP, hmap, ht, hU0, sumLinForm l]
    congr 2
    rw [show (∑ k, ∑ j, (Y * g.val) k j * l (Matrix.single k j 1)) =
      ∑ k, ∑ j, (Y * g.val) k j * Lm l k j from rfl, sumMulRight]
    simp [Matrix.neg_mul, Finset.sum_neg_distrib]
  obtain ⟨c, hc⟩ := GlobalTheory.T.eq_smul_of_commute_heisenberg_linearModel_schwartzBruhat (SB (Fin a' × Fin (a + a') → Fv F v)) (GlobalTheory.LatVac.psiAt B.ψ v)
    (GlobalTheory.SchrSB.continuous_psiAt B.ψ hstd.1 v) (GlobalTheory.PsiNontriv.psiAt_ne_one B.ψ hstd v) ι
    (fun φ Y => ι (S φ) (Y * ((g⁻¹ : GL (Fin (a + a')) (Fv F v)).val))) hι.bij
    (fun x hx y hy c => by
      funext Y
      simp only [hlin x hx y hy c, map_add, map_smul, Pi.add_apply, Pi.smul_apply])
    (fun C => schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M'.co v (U 0 (Pm C))))
    (fun l => schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M'.co v (U (-Lm l) 0)))
    (fun C x hx => ⟨hsb _ x hx, c1 C x hx, by
      funext Y
      show ι (S _) (Y * ((g⁻¹ : GL (Fin (a + a')) (Fv F v)).val)) = ι (S x) ((Y + C) * ((g⁻¹ : GL (Fin (a + a')) (Fv F v)).val))
      rw [c3 C x hx, Matrix.add_mul]⟩)
    (fun l x hx => ⟨hsb _ x hx, c2 l x hx, by
      funext Y
      show ι (S _) (Y * ((g⁻¹ : GL (Fin (a + a')) (Fv F v)).val)) =
        GlobalTheory.LatVac.psiAt B.ψ v (l Y) * ι (S x) (Y * ((g⁻¹ : GL (Fin (a + a')) (Fv F v)).val))
      rw [c4 l x hx]
      beta_reduce
      rw [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]⟩)
  refine ⟨c, fun φ hφ => funext fun Y => ?_⟩
  have e := congrFun (hc φ hφ) (Y * g.val)
  simp only [Pi.smul_apply] at e
  rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one] at e
  rw [Pi.smul_apply]
  exact e

/- English proof (translation)
Introduce `hP F E _ _ _ _ _ σ B a a' G X om om' hT v hv t ι hι h₀`. Establish `hcm : IsCMExt F E σ` using `hT.base.cm`. Take `⟨w⟩ : Nonempty (InfinitePlace F)` from `inferInstance`. Establish `skew : ∀ i j, σ (G.W.J j i) = algebraMap F E (-1) * G.W.J i j` using `fun i j => by`. Rewrite using `[map_neg, map_one, neg_one_mul]`.

Conclude with `hT.geo.hW.skew i j`. Establish `hdetW : IsUnit (G.W.J.map t).det` using `GlobalTheory.SplitUnitLift.isUnit_det_of_cartan G.W.J t (B.emb w).1 Complex.I Complex.I_ne_zero (G.W.θ w) (hT.geo.hW.cartan w)`. Use `set h := GlobalTheory.SplitUnitLift.liftU hcm t G.W.J (-1) skew hdetW h₀ with hhdef`. Establish `hmem : h ∈ UAt σ G.W (evFin F v)` using `GlobalTheory.SplitUnitLift.liftU_mem_UAt hcm t G.W (-1) skew hdetW h₀`. Take `⟨S, hS, hlin, hcov, hinj⟩` from `local_weil_operator_second_space hP F E σ B a a' G X om om' hT v h hmem`.

Take `⟨c, hc⟩` from `linBar_right_mul F E σ B a a' G X om om' hT v t h h₀ hmem (GlobalTheory.SplitUnitLift.liftU_piW hcm t G.W.J (-1) skew hdetW h₀) (GlobalTheory.SplitUnitLift.liftU_piW_comp hcm t G.W.J (-1) skew hdetW h₀) S (fun φ hφ => (hS φ hφ).1) hlin hcov ι hι`. Use `⟨h, hmem, c, ?_, fun φ hφ => ⟨S φ, (hS φ hφ).1, (hS φ hφ).2, hc φ hφ⟩⟩` and prove the remaining obligations. Introduce `hc0`. Establish `hvac` using `hT.geo.hM'.vac v`. Establish `h0 : ι (S (G.M'.vac v)) = 0` using `by rw [hc _ hvac.1, hc0, zero_smul]`.

Establish `hS0 : S (G.M'.vac v) = 0` using `hι.bij.injOn (hS _ hvac.1).1 (Submodule.zero_mem _) (by rw [h0, map_zero])`. Conclude with `hvac.2.1 (hinj _ hvac.1 hS0)`.
-/
theorem unitaryW_acts_right : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → ∀ v, X.Good v → ∀ (t : E →ₐ[F] Fv F v) (ι : ((Fin a' × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin a') (Fin (a + a')) (Fv F v) → ℂ)), G.M'.IsLinBar B.ψ t 1 1 ι → ∀ h₀ : GL (Fin (a + a')) (Fv F v), ∃ h ∈ UAt σ G.W (evFin F v), ∃ c : ℂ, c ≠ 0 ∧ ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), ∃ φ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F v), Acts (evFin F v) (om' (1, h)) φ φ₁ ∧ ι φ₁ = c • fun Y => ι φ (Y * h₀.1) := by
  intro hP F E _ _ _ _ _ σ B a a' G X om om' hT v hv t ι hι h₀
  have hcm : IsCMExt F E σ := hT.base.cm
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have skew : ∀ i j, σ (G.W.J j i) = algebraMap F E (-1) * G.W.J i j := fun i j => by
    rw [map_neg, map_one, neg_one_mul]; exact hT.geo.hW.skew i j
  have hdetW : IsUnit (G.W.J.map t).det :=
    GlobalTheory.SplitUnitLift.isUnit_det_of_cartan G.W.J t (B.emb w).1 Complex.I Complex.I_ne_zero (G.W.θ w) (hT.geo.hW.cartan w)
  set h := GlobalTheory.SplitUnitLift.liftU hcm t G.W.J (-1) skew hdetW h₀ with hhdef
  have hmem : h ∈ UAt σ G.W (evFin F v) := GlobalTheory.SplitUnitLift.liftU_mem_UAt hcm t G.W (-1) skew hdetW h₀
  obtain ⟨S, hS, hlin, hcov, hinj⟩ := local_weil_operator_second_space hP F E σ B a a' G X om om' hT v h hmem
  obtain ⟨c, hc⟩ := linBar_right_mul F E σ B a a' G X om om' hT v t h h₀ hmem
    (GlobalTheory.SplitUnitLift.liftU_piW hcm t G.W.J (-1) skew hdetW h₀)
    (GlobalTheory.SplitUnitLift.liftU_piW_comp hcm t G.W.J (-1) skew hdetW h₀) S (fun φ hφ => (hS φ hφ).1) hlin hcov ι hι
  refine ⟨h, hmem, c, ?_, fun φ hφ => ⟨S φ, (hS φ hφ).1, (hS φ hφ).2, hc φ hφ⟩⟩
  intro hc0
  have hvac := hT.geo.hM'.vac v
  have h0 : ι (S (G.M'.vac v)) = 0 := by rw [hc _ hvac.1, hc0, zero_smul]
  have hS0 : S (G.M'.vac v) = 0 :=
    hι.bij.injOn (hS _ hvac.1).1 (Submodule.zero_mem _) (by rw [h0, map_zero])
  exact hvac.2.1 (hinj _ hvac.1 hS0)

end GlobalTheory.WeilTransferW
