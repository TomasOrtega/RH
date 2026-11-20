import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTriple
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftPRouteSmall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHeisenbergActsByLocalSchrodingerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharacterNontrivialAtPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerPreservesSchwartzBruhat
import Development.AbelianVarietyTheory.Definitions.Foundations.NonemptyAlgHomOfNotIsField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianSelfDualLatticeSpaceFormHermitianNondeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitPlaceAdelicMatrixGivenComponentsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicTraceSupportedAtSplitPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianTensorSkewHermitianSplitSymplecticPairStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel

open scoped GlobalTheory.VacAny
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.LinBarOps

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (AE At piW cA incM)

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
Simplify using `only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul, Finset.mul_sum]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem sum_transpose_mul {K : Type} [CommRing K] {m n : Type} [Fintype m] [Fintype n]
    (g : Matrix m m K) (Y L : Matrix m n K) :
    ∑ k, ∑ j, (gᵀ * Y) k j * L k j = ∑ k, ∑ j, Y k j * (g * L) k j := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul, Finset.mul_sum]
  calc _ = ∑ x, ∑ i, ∑ j, g i x * Y i j * L x j := Finset.sum_congr rfl fun x _ => Finset.sum_comm
    _ = ∑ i, ∑ x, ∑ j, g i x * Y i j * L x j := Finset.sum_comm
    _ = ∑ i, ∑ j, ∑ x, g i x * Y i j * L x j := Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun x _ => by ring

end GlobalTheory.LinBarOps

namespace GlobalTheory.LinBarOps

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (AE At piW cA incM)

/- English proof (translation)
Introduce `r hr`. Establish `h : ∀ i j, r • x i j = 0` using `fun i j => by`. Use `congrFun (congrFun (hx r hr) i) j` as an intermediate fact. Simplify using `using this`. Rewrite using `[← mul_smul_comm]`.

Unfold `hTens`. Simplify using `only [Finset.smul_sum, ← smul_mul_assoc, h, zero_mul, Finset.sum_const_zero, mul_zero]`.
-/
theorem at_hTens {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F} {m n : ℕ} (JA : Matrix (Fin m) (Fin m) E) (JB : Matrix (Fin n) (Fin n) E)
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
Introduce `F E _ _ _ _ _ σ a a' Bs Γ X om om' hT K hK S hSB h4`. Establish `hcm : IsCMExt F E σ` using `hT.base.cm`. Establish `hstd` using `hT.base.std`. Use `⟨GlobalTheory.SchrSB.continuous_psiAt _ hstd.1 _, GlobalTheory.PsiNontriv.psiAt_ne_one _ hstd _, ?_⟩` and prove the remaining obligations. Take `⟨w⟩ : Nonempty (InfinitePlace F)` from `inferInstance`.

Establish `hdV : Γ.V'.J.det ≠ 0`. Introduce `h0`. Apply `GlobalTheory.WeilSchrodingerHerm.det_ne_zero_of_hasSig (hT.geo.hV'.sig w)` to reduce the goal to its premises. Establish `e : (Γ.V'.J.map (Bs.emb w).1).det = (Bs.emb w).1 Γ.V'.J.det` using `(RingHom.map_det _ _).symm`. Rewrite using `[e, h0, map_zero]`.

Establish `hdW : Γ.W.J.det ≠ 0`. Introduce `h0`. Apply `GlobalTheory.WeilSchrodingerHerm.det_ne_zero_of_hasSig (hT.geo.hW.sig w)` to reduce the goal to its premises. Establish `e : (Γ.W.J.map (Bs.emb w).1).det = (Bs.emb w).1 Γ.W.J.det` using `(RingHom.map_det _ _).symm`. Rewrite using `[Matrix.det_smul, e, h0, map_zero, mul_zero]`.

Use `set A := Γ.V'.J.map Bs.τ₁ with hAdef`. Use `set B := Γ.W.J.map Bs.τ₁ with hBdef`. Establish `hA : IsUnit A.det`. Establish `e : A.det = (Bs.τ₁ : E →+* Fv F Bs.v₁) Γ.V'.J.det` using `(RingHom.map_det _ _).symm`. Rewrite using `[e]`.

Conclude with `isUnit_iff_ne_zero.2 fun h => hdV ((Bs.τ₁ : E →+* Fv F Bs.v₁).injective (by rw [map_zero]; exact h))`. Establish `hB : IsUnit Bᵀ.det`. Establish `e : B.det = (Bs.τ₁ : E →+* Fv F Bs.v₁) Γ.W.J.det` using `(RingHom.map_det _ _).symm`. Rewrite using `[Matrix.det_transpose, e]`. Conclude with `isUnit_iff_ne_zero.2 fun h => hdW ((Bs.τ₁ : E →+* Fv F Bs.v₁).injective (by rw [map_zero]; exact h))`.

Establish `hBm : IsUnit B.det` using `by rw [← Matrix.det_transpose]; exact hB`. Use `choose U hUat hU0 hU1 using fun (P₀ P₁ : Matrix (Fin a') (Fin (a + a')) (Fv F Bs.v₁)) => GlobalTheory.T.exists_splitPlace_adelicMatrix_given_components hcm Bs.v₁ Bs.τ₁ P₀ P₁`. Set `Pm : Matrix (Fin a') (Fin (a + a')) (Fv F Bs.v₁) → Matrix (Fin a') (Fin (a + a')) (Fv F Bs.v₁)` to `fun C => -(A⁻¹ * C * (Bᵀ)⁻¹)`. Set `Lm : (Matrix (Fin a') (Fin (a + a')) (Fv F Bs.v₁) →ₗ[Fv F Bs.v₁] Fv F Bs.v₁) → Matrix (Fin a') (Fin (a + a')) (Fv F Bs.v₁)` to `fun l => Matrix.of fun k j => l (Matrix.single k j 1)`. Establish `hcoP : ∀ C, -(A * (U 0 (Pm C)).map (piW (Bs.τ₁.comp σ)) * Bᵀ) = C`.

Introduce `C`. Rewrite using `[hU1]`. Simplify using `only [Pm, Matrix.mul_neg, Matrix.neg_mul, neg_neg, Matrix.mul_assoc]`. Rewrite using `[Matrix.nonsing_inv_mul _ hB, Matrix.mul_one, Matrix.mul_nonsing_inv_cancel_left _ _ hA]`. Establish `hsymp : ∀ x u : Matrix (Fin a') (Fin (a + a')) (AE F E), At (evFin F Bs.v₁) x → x.map (piW Bs.τ₁) = 0 → u.map (piW (Bs.τ₁.comp σ)) = 0 → Bs.ψ (symp (R` using `AF F) (cA σ) (-1) (incM F Γ.V'.J) (incM F Γ.W.J) x u) = GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁ (-(∑ k, ∑ j, (-(A * x.map (piW (Bs.τ₁.comp σ)) * Bᵀ)) k j * u.map (piW Bs.τ₁) k j)) := by`.

Introduce `x u hx hx0 hu1`. Unfold `symp`. Rewrite using `[GlobalTheory.T.adelicTrace_supportedAtSplitPlace hcm Bs.v₁ Bs.τ₁ _ (at_hTens _ _ x u hx)]`. Rewrite using `[map_mul, map_mul, map_neg, map_neg, map_one, map_one, neg_one_mul, neg_one_mul, ← neg_add, GlobalTheory.T.hermitianTensor_skewHermitian_split_symplectic_pair hcm Bs.τ₁ Γ.V'.J Γ.W.J hT.geo.hV'.herm hT.geo.hW.skew x u hx0 hu1]`. Both sides reduce to the same expression.

Use `⟨fun C => GlobalTheory.LatVac.locCo Γ.M'.co Bs.v₁ (U 0 (Pm C)), fun l => GlobalTheory.LatVac.locCo Γ.M'.co Bs.v₁ (U (-Lm l) 0), ?_⟩` and prove the remaining obligations. Introduce `ι hι`. Establish `hL` using `hι`. Unfold `GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model.IsLinBar at hL`. Simplify using `only [Units.val_one, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one] at hL`.

Establish `htr` using `hL.trans`. Establish `hmu` using `hL.mult`. Establish `hK' : ∀ g (u : Matrix (Fin a') (Fin (a + a')) (AE F E)), actAB (cA σ) (K g, (1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ Γ.W.J)) u = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (K g) * u`. Introduce `g u`. Simplify using `[actAB, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat]`.

Establish `hKat : ∀ g (u : Matrix (Fin a') (Fin (a + a')) (AE F E)), At (evFin F Bs.v₁) u → At (evFin F Bs.v₁) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (K g) * u)`. Introduce `g u hu r hr`. Rewrite using `[← Matrix.mul_smul, hu r hr, Matrix.mul_zero]`. Establish `hKmap : ∀ g (u : Matrix (Fin a') (Fin (a + a')) (AE F E)) (t : E →ₐ[F] Fv F Bs.v₁), (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (K g) * u).map (piW t) = (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (K g)).map (piW t) * u.map (piW t)` using `fun g u t => Matrix.map_mul`. Establish `hbr` using `fun (γ : Matrix (Fin a') (Fin (a + a')) (AE F E)) hγ (φ : (Fin a' × Fin (a + a') → Fv F Bs.v₁) → ℂ) => GlobalTheory.T.adelicHeisenberg_acts_by_local_schrodinger Γ.M'.co Bs.ψ Bs.v₁ γ hγ φ`.

Establish `hsb` using `fun (w : (Fin a' × Fin (a + a') → Fv F Bs.v₁) × (Fin a' × Fin (a + a') → Fv F Bs.v₁)) (φ : (Fin a' × Fin (a + a') → Fv F Bs.v₁) → ℂ) (hφ : φ ∈ GlobalTheory.WeilM.SB _) => GlobalTheory.SchrSB.schr_mem_SB Bs.ψ hstd.1 Bs.v₁ w φ hφ`. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `C φ hφ`. Use function extensionality and compare the values at `Y`. Rewrite using `[htr (U 0 (Pm C)) (hUat 0 (Pm C)) (hU0 0 (Pm C)) φ hφ _ (hsb _ φ hφ) (hbr _ (hUat 0 (Pm C)) φ) Y, hcoP]`.

Introduce `l φ hφ`. Use function extensionality and compare the values at `Y`. Establish `hm` using `hmu (U (-Lm l) 0) (hUat (-Lm l) 0) (hU1 (-Lm l) 0) φ hφ _ (hsb _ φ hφ) (hbr _ (hUat (-Lm l) 0) φ) (U 0 (Pm Y)) (hUat 0 (Pm Y)) (hU0 0 (Pm Y))`. Rewrite `hm` using `[hcoP]`. Rewrite using `[hm, hsymp _ _ (hUat 0 (Pm Y)) (hU0 0 (Pm Y)) (hU1 (-Lm l) 0), hcoP, hU0, linForm_eq l Y]`.

Use `congr 2`. Simplify using `[Lm, Finset.sum_neg_distrib]`. Introduce `g C φ hφ`. Use function extensionality and compare the values at `Y`. Rewrite using `[h4 g _ (hUat 0 (Pm C)) φ hφ, hK']`.

Establish `hat` using `hKat g _ (hUat 0 (Pm C))`. Rewrite using `[htr _ hat (by rw [hKmap, hU0, Matrix.mul_zero]) _ (hSB g φ hφ) _ (hsb _ _ (hSB g φ hφ)) (hbr _ hat _) Y]`. Use `congr 2`. Rewrite using `[hKmap, (hK g).2.2, hU1]`. Simplify using `only [Pm, Matrix.mul_neg, Matrix.neg_mul, neg_neg, Matrix.mul_assoc]`.

Rewrite using `[Matrix.nonsing_inv_mul _ hB, Matrix.mul_one, Matrix.mul_nonsing_inv_cancel_left _ _ hA, Matrix.mul_nonsing_inv_cancel_left _ _ hA]`. Introduce `g l φ hφ`. Use function extensionality and compare the values at `Y`. Rewrite using `[h4 g _ (hUat (-Lm l) 0) φ hφ, hK']`. Establish `hat` using `hKat g _ (hUat (-Lm l) 0)`.

Establish `h1 : (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (K g) * U (-Lm l) 0).map (piW (Bs.τ₁.comp σ)) = 0`. Rewrite using `[hKmap, hU1, Matrix.mul_zero]`. Establish `hm` using `hmu _ hat h1 _ (hSB g φ hφ) _ (hsb _ _ (hSB g φ hφ)) (hbr _ hat _) (U 0 (Pm Y)) (hUat 0 (Pm Y)) (hU0 0 (Pm Y))`. Rewrite `hm` using `[hcoP]`. Rewrite using `[hm, hsymp _ _ (hUat 0 (Pm Y)) (hU0 0 (Pm Y)) h1, hcoP, hKmap, (hK g).2.1, hU0, linForm_eq l]`.

Use `congr 2`. Rewrite using `[show (∑ k, ∑ j, ((g : Matrix (Fin a') (Fin a') (Fv F Bs.v₁))ᵀ * Y) k j * l (Matrix.single k j 1)) = ∑ k, ∑ j, ((g : Matrix (Fin a') (Fin a') (Fv F Bs.v₁))ᵀ * Y) k j * Lm l k j from rfl, sum_transpose_mul]`. Simplify using `[Matrix.mul_neg, Finset.sum_neg_distrib]`.
-/
theorem heis_ops : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ}
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V' Γ.W), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om' →
    ∀ (K : GL (Fin a') (Fv F Bs.v₁) →* GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ Γ.V'.J),
    (∀ g, K g ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ Γ.V' (evFin F Bs.v₁) ∧
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (K g)).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW Bs.τ₁) = g.val ∧
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (K g)).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW (Bs.τ₁.comp σ)) =
        (Γ.V'.J.map Bs.τ₁)⁻¹ * ((g⁻¹ : GL _ _).val)ᵀ * Γ.V'.J.map Bs.τ₁) →
    ∀ (S : GL (Fin a') (Fv F Bs.v₁) → ((Fin a' × Fin (a + a') → Fv F Bs.v₁) → ℂ) → (Fin a' × Fin (a + a') → Fv F Bs.v₁) → ℂ),
    (∀ g, ∀ φ ∈ GlobalTheory.WeilM.SB _, S g φ ∈ GlobalTheory.WeilM.SB _) →
    (∀ g (γ : Matrix (Fin a') (Fin (a + a')) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E)), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F Bs.v₁) γ →
      ∀ φ ∈ GlobalTheory.WeilM.SB _,
        S g (GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) (GlobalTheory.LatVac.locCo Γ.M'.co Bs.v₁ γ) φ) =
          GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁)
            (GlobalTheory.LatVac.locCo Γ.M'.co Bs.v₁ (GlobalTheory.WeilM.actAB (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (K g, (1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ Γ.W.J)) γ)) (S g φ)) →
    Continuous (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) ∧ GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁ ≠ 1 ∧
    ∃ (wT : Matrix (Fin a') (Fin (a + a')) (Fv F Bs.v₁) → (Fin a' × Fin (a + a') → Fv F Bs.v₁) × (Fin a' × Fin (a + a') → Fv F Bs.v₁))
      (wM : (Matrix (Fin a') (Fin (a + a')) (Fv F Bs.v₁) →ₗ[Fv F Bs.v₁] Fv F Bs.v₁) → (Fin a' × Fin (a + a') → Fv F Bs.v₁) × (Fin a' × Fin (a + a') → Fv F Bs.v₁)),
    ∀ ι, Γ.M'.IsLinBar Bs.ψ Bs.τ₁ 1 1 ι →
      (∀ C, ∀ φ ∈ GlobalTheory.WeilM.SB _, ι (GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) (wT C) φ) = fun Y => ι φ (Y + C)) ∧
      (∀ l, ∀ φ ∈ GlobalTheory.WeilM.SB _, ι (GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) (wM l) φ) = fun Y => GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁ (l Y) * ι φ Y) ∧
      (∀ g C, ∀ φ ∈ GlobalTheory.WeilM.SB _, ι (S g (GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) (wT C) φ)) =
        fun Y => ι (S g φ) (Y + ((g⁻¹ : GL (Fin a') (Fv F Bs.v₁)).val)ᵀ * C)) ∧
      (∀ g l, ∀ φ ∈ GlobalTheory.WeilM.SB _, ι (S g (GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) (wM l) φ)) =
        fun Y => GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁ (l (g.valᵀ * Y)) * ι (S g φ) Y) := by
  intro F E _ _ _ _ _ σ a a' Bs Γ X om om' hT K hK S hSB h4
  have hcm : IsCMExt F E σ := hT.base.cm
  have hstd := hT.base.std
  refine ⟨GlobalTheory.SchrSB.continuous_psiAt _ hstd.1 _, GlobalTheory.PsiNontriv.psiAt_ne_one _ hstd _, ?_⟩
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have hdV : Γ.V'.J.det ≠ 0 := by
    intro h0
    apply GlobalTheory.WeilSchrodingerHerm.det_ne_zero_of_hasSig (hT.geo.hV'.sig w)
    have e : (Γ.V'.J.map (Bs.emb w).1).det = (Bs.emb w).1 Γ.V'.J.det := (RingHom.map_det _ _).symm
    rw [e, h0, map_zero]
  have hdW : Γ.W.J.det ≠ 0 := by
    intro h0
    apply GlobalTheory.WeilSchrodingerHerm.det_ne_zero_of_hasSig (hT.geo.hW.sig w)
    have e : (Γ.W.J.map (Bs.emb w).1).det = (Bs.emb w).1 Γ.W.J.det := (RingHom.map_det _ _).symm
    rw [Matrix.det_smul, e, h0, map_zero, mul_zero]
  set A := Γ.V'.J.map Bs.τ₁ with hAdef
  set B := Γ.W.J.map Bs.τ₁ with hBdef
  have hA : IsUnit A.det := by
    have e : A.det = (Bs.τ₁ : E →+* Fv F Bs.v₁) Γ.V'.J.det := (RingHom.map_det _ _).symm
    rw [e]
    exact isUnit_iff_ne_zero.2 fun h => hdV ((Bs.τ₁ : E →+* Fv F Bs.v₁).injective (by rw [map_zero]; exact h))
  have hB : IsUnit Bᵀ.det := by
    have e : B.det = (Bs.τ₁ : E →+* Fv F Bs.v₁) Γ.W.J.det := (RingHom.map_det _ _).symm
    rw [Matrix.det_transpose, e]
    exact isUnit_iff_ne_zero.2 fun h => hdW ((Bs.τ₁ : E →+* Fv F Bs.v₁).injective (by rw [map_zero]; exact h))
  have hBm : IsUnit B.det := by rw [← Matrix.det_transpose]; exact hB
  choose U hUat hU0 hU1 using fun (P₀ P₁ : Matrix (Fin a') (Fin (a + a')) (Fv F Bs.v₁)) =>
    GlobalTheory.T.exists_splitPlace_adelicMatrix_given_components hcm Bs.v₁ Bs.τ₁ P₀ P₁
  let Pm : Matrix (Fin a') (Fin (a + a')) (Fv F Bs.v₁) → Matrix (Fin a') (Fin (a + a')) (Fv F Bs.v₁) :=
    fun C => -(A⁻¹ * C * (Bᵀ)⁻¹)
  let Lm : (Matrix (Fin a') (Fin (a + a')) (Fv F Bs.v₁) →ₗ[Fv F Bs.v₁] Fv F Bs.v₁) →
      Matrix (Fin a') (Fin (a + a')) (Fv F Bs.v₁) := fun l => Matrix.of fun k j => l (Matrix.single k j 1)
  have hcoP : ∀ C, -(A * (U 0 (Pm C)).map (piW (Bs.τ₁.comp σ)) * Bᵀ) = C := by
    intro C
    rw [hU1]
    simp only [Pm, Matrix.mul_neg, Matrix.neg_mul, neg_neg, Matrix.mul_assoc]
    rw [Matrix.nonsing_inv_mul _ hB, Matrix.mul_one, Matrix.mul_nonsing_inv_cancel_left _ _ hA]
  have hsymp : ∀ x u : Matrix (Fin a') (Fin (a + a')) (AE F E), At (evFin F Bs.v₁) x → x.map (piW Bs.τ₁) = 0 →
      u.map (piW (Bs.τ₁.comp σ)) = 0 →
      Bs.ψ (symp (R := AF F) (cA σ) (-1) (incM F Γ.V'.J) (incM F Γ.W.J) x u) =
        GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁
          (-(∑ k, ∑ j, (-(A * x.map (piW (Bs.τ₁.comp σ)) * Bᵀ)) k j * u.map (piW Bs.τ₁) k j)) := by
    intro x u hx hx0 hu1
    unfold symp
    rw [GlobalTheory.T.adelicTrace_supportedAtSplitPlace hcm Bs.v₁ Bs.τ₁ _ (at_hTens _ _ x u hx)]
    rw [map_mul, map_mul, map_neg, map_neg, map_one, map_one, neg_one_mul, neg_one_mul, ← neg_add,
      GlobalTheory.T.hermitianTensor_skewHermitian_split_symplectic_pair hcm Bs.τ₁ Γ.V'.J Γ.W.J hT.geo.hV'.herm hT.geo.hW.skew x u hx0 hu1]
    rfl
  refine ⟨fun C => GlobalTheory.LatVac.locCo Γ.M'.co Bs.v₁ (U 0 (Pm C)),
    fun l => GlobalTheory.LatVac.locCo Γ.M'.co Bs.v₁ (U (-Lm l) 0), ?_⟩
  intro ι hι
  have hL := hι
  unfold GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model.IsLinBar at hL
  simp only [Units.val_one, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one] at hL
  have htr := hL.trans
  have hmu := hL.mult
  have hK' : ∀ g (u : Matrix (Fin a') (Fin (a + a')) (AE F E)),
      actAB (cA σ) (K g, (1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ Γ.W.J)) u = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (K g) * u := by
    intro g u
    simp [actAB, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat]
  have hKat : ∀ g (u : Matrix (Fin a') (Fin (a + a')) (AE F E)), At (evFin F Bs.v₁) u →
      At (evFin F Bs.v₁) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (K g) * u) := by
    intro g u hu r hr
    rw [← Matrix.mul_smul, hu r hr, Matrix.mul_zero]
  have hKmap : ∀ g (u : Matrix (Fin a') (Fin (a + a')) (AE F E)) (t : E →ₐ[F] Fv F Bs.v₁),
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (K g) * u).map (piW t) = (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (K g)).map (piW t) * u.map (piW t) :=
    fun g u t => Matrix.map_mul
  have hbr := fun (γ : Matrix (Fin a') (Fin (a + a')) (AE F E)) hγ (φ : (Fin a' × Fin (a + a') → Fv F Bs.v₁) → ℂ) => GlobalTheory.T.adelicHeisenberg_acts_by_local_schrodinger Γ.M'.co Bs.ψ Bs.v₁ γ hγ φ
  have hsb := fun (w : (Fin a' × Fin (a + a') → Fv F Bs.v₁) × (Fin a' × Fin (a + a') → Fv F Bs.v₁)) (φ : (Fin a' × Fin (a + a') → Fv F Bs.v₁) → ℂ) (hφ : φ ∈ GlobalTheory.WeilM.SB _) => GlobalTheory.SchrSB.schr_mem_SB Bs.ψ hstd.1 Bs.v₁ w φ hφ
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro C φ hφ
    funext Y
    rw [htr (U 0 (Pm C)) (hUat 0 (Pm C)) (hU0 0 (Pm C)) φ hφ _ (hsb _ φ hφ) (hbr _ (hUat 0 (Pm C)) φ) Y, hcoP]
  · intro l φ hφ
    funext Y
    have hm := hmu (U (-Lm l) 0) (hUat (-Lm l) 0) (hU1 (-Lm l) 0) φ hφ _ (hsb _ φ hφ) (hbr _ (hUat (-Lm l) 0) φ)
      (U 0 (Pm Y)) (hUat 0 (Pm Y)) (hU0 0 (Pm Y))
    rw [hcoP] at hm
    rw [hm, hsymp _ _ (hUat 0 (Pm Y)) (hU0 0 (Pm Y)) (hU1 (-Lm l) 0), hcoP, hU0, linForm_eq l Y]
    congr 2
    simp [Lm, Finset.sum_neg_distrib]
  · intro g C φ hφ
    funext Y
    rw [h4 g _ (hUat 0 (Pm C)) φ hφ, hK']
    have hat := hKat g _ (hUat 0 (Pm C))
    rw [htr _ hat (by rw [hKmap, hU0, Matrix.mul_zero]) _ (hSB g φ hφ) _ (hsb _ _ (hSB g φ hφ)) (hbr _ hat _) Y]
    congr 2
    rw [hKmap, (hK g).2.2, hU1]
    simp only [Pm, Matrix.mul_neg, Matrix.neg_mul, neg_neg, Matrix.mul_assoc]
    rw [Matrix.nonsing_inv_mul _ hB, Matrix.mul_one, Matrix.mul_nonsing_inv_cancel_left _ _ hA,
      Matrix.mul_nonsing_inv_cancel_left _ _ hA]
  · intro g l φ hφ
    funext Y
    rw [h4 g _ (hUat (-Lm l) 0) φ hφ, hK']
    have hat := hKat g _ (hUat (-Lm l) 0)
    have h1 : (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (K g) * U (-Lm l) 0).map (piW (Bs.τ₁.comp σ)) = 0 := by
      rw [hKmap, hU1, Matrix.mul_zero]
    have hm := hmu _ hat h1 _ (hSB g φ hφ) _ (hsb _ _ (hSB g φ hφ)) (hbr _ hat _) (U 0 (Pm Y)) (hUat 0 (Pm Y)) (hU0 0 (Pm Y))
    rw [hcoP] at hm
    rw [hm, hsymp _ _ (hUat 0 (Pm Y)) (hU0 0 (Pm Y)) h1, hcoP, hKmap, (hK g).2.1, hU0, linForm_eq l]
    congr 2
    rw [show (∑ k, ∑ j, ((g : Matrix (Fin a') (Fin a') (Fv F Bs.v₁))ᵀ * Y) k j * l (Matrix.single k j 1)) =
      ∑ k, ∑ j, ((g : Matrix (Fin a') (Fin a') (Fv F Bs.v₁))ᵀ * Y) k j * Lm l k j from rfl, sum_transpose_mul]
    simp [Matrix.mul_neg, Finset.sum_neg_distrib]

end GlobalTheory.LinBarOps
