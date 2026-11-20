import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RootOfUnityThetaTwist
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaFunctionFockVectorDownwardArrow
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HandBFSmul
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ConTwist

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

/- English proof (translation)
Rewrite using `[mul_assoc, mul_comm b' b⁻¹, mul_inv_cancel_left]`.
-/
theorem commGroup_mul_eq_mul_mul_div {C : Type} [CommGroup C] (a b b' : C) : a * b' = a * b * (b' * b⁻¹) := by
  rw [mul_assoc, mul_comm b' b⁻¹, mul_inv_cancel_left]

/- English proof (translation)
Rewrite using `[commGroup_mul_eq_mul_mul_div a b b', mul_right_comm]`.
-/
theorem commGroup_mul_mul_eq_mul_mul_div {C : Type} [CommGroup C] (a b b' e : C) : a * b' * e = a * b * e * (b' * b⁻¹) := by
  rw [commGroup_mul_eq_mul_mul_div a b b', mul_right_comm]

/- English proof (translation)
Simplify using `only [GridData.chrS, GridData.chr, LevCh.mu, Lift.tup, Lift.attChr]`. Use `split_ifs`. Conclude with `commGroup_mul_mul_eq_mul_mul_div _ _ _ _`. Conclude with `commGroup_mul_eq_mul_mul_div _ _ _`.
-/
theorem chrS_mu (t t' : T) (i j : ℕ) :
    G.chrS (.mu t' i j) = G.chrS (.mu t i j) * (L.xi t' * (L.xi t)⁻¹) := by
  simp only [GridData.chrS, GridData.chr, LevCh.mu, Lift.tup, Lift.attChr]
  split_ifs
  · exact commGroup_mul_mul_eq_mul_mul_div _ _ _ _
  · exact commGroup_mul_eq_mul_mul_div _ _ _

/- English proof (translation)
Simplify using `only [GridData.chrT, GridData.chr, LevCh.mu, Lift.tup, Lift.attChr]`. Use `split_ifs`. Conclude with `commGroup_mul_mul_eq_mul_mul_div _ _ _ _`. Conclude with `commGroup_mul_eq_mul_mul_div _ _ _`.
-/
theorem chrT_mu (t t' : T) (i j : ℕ) :
    G.chrT (.mu t' i j) = G.chrT (.mu t i j) * (L.xi t' * (L.xi t)⁻¹) := by
  simp only [GridData.chrT, GridData.chr, LevCh.mu, Lift.tup, Lift.attChr]
  split_ifs
  · exact commGroup_mul_mul_eq_mul_mul_div _ _ _ _
  · exact commGroup_mul_eq_mul_mul_div _ _ _

end GlobalTheory.ConTwist

namespace GlobalTheory.ConTwist

open GlobalTheory.RowChain GlobalTheory.Unf

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

/- English proof (translation)
Simplify using `only [IsDetRoot, map_one, Units.val_one, Matrix.det_one, one_mul] at hy ⊢`. Conclude with `hy`.
-/
theorem isDetRoot_one {V V' : HSp D} {y : (AE D)ˣ} (hy : IsDetRoot V 1 y) : IsDetRoot V' 1 y := by
  simp only [IsDetRoot, map_one, Units.val_one, Matrix.det_one, one_mul] at hy ⊢
  exact hy

/- English proof (translation)
Use function extensionality and compare the values at `u v`. Simplify using `only [contr, Pi.smul_apply, smul_eq_mul]`. Rewrite using `[← integral_const_mul]`. Use `congr 1`. Use function extensionality and compare the values at `w`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem contr_smul_right {ρ σ : ℕ} {B : BesLev D ρ} {B' : BesLev D σ} (l : Link B B'.L B'.ζ) (S : HSp D)
    (vL : VolM D B'.L.rank S.rank) (c : ℂ) (f₁ : WO B.V₀ S → ℂ) (f₂ : WO S B'.V₀ → ℂ) :
    contr l S vL f₁ (c • f₂) = c • contr l S vL f₁ f₂ := by
  funext u v
  simp only [contr, Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul]
  congr 1
  funext w
  ring

/- English proof (translation)
Use function extensionality and compare the values at `u v`. Simplify using `only [contr, Pi.smul_apply, smul_eq_mul]`. Rewrite using `[← integral_const_mul]`. Use `congr 1`. Use function extensionality and compare the values at `w`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem contr_smul_left {ρ σ : ℕ} {B : BesLev D ρ} {B' : BesLev D σ} (l : Link B B'.L B'.ζ) (S : HSp D)
    (vL : VolM D B'.L.rank S.rank) (c : ℂ) (f₁ : WO B.V₀ S → ℂ) (f₂ : WO S B'.V₀ → ℂ) :
    contr l S vL (c • f₁) f₂ = c • contr l S vL f₁ f₂ := by
  funext u v
  simp only [contr, Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul]
  congr 1
  funext w
  ring

/- English proof (translation)
Use function extensionality and compare the values at `u v`. Simplify using `only [GlobalTheory.FinPl.lastBi, OrthDec.boxT, Pi.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem lastBi_smul {V₀ A L S X T L'' : HSp D} (o : OrthDec V₀ A L) (o'' : OrthDec X T L'')
    (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E) (c : ℂ) (Ξ : WO V₀ S → ℂ) (Φ₂ : WO S T → ℂ) :
    GlobalTheory.FinPl.lastBi o o'' τ (c • Ξ) Φ₂ = c • GlobalTheory.FinPl.lastBi o o'' τ Ξ Φ₂ := by
  funext u v
  simp only [GlobalTheory.FinPl.lastBi, OrthDec.boxT, Pi.smul_apply, smul_eq_mul]
  ring

/- English proof (translation)
Establish `h0` using `W.om_is (.mu t D.R.m k) ⟨le_rfl, hk⟩`. Establish `h1` using `W.om_is (.mu t' D.R.m k) ⟨le_rfl, hk⟩`. Rewrite `h1` using `[chrS_mu t t', chrT_mu t t']`. Conclude with `GlobalTheory.TupRoot.twist_eq h0 h1 hy hy' hf`.
-/
theorem om_mu_twist (W : G.Weil) (t t' : T) (k : ℕ) (hk : k + 1 ≤ D.R.m) {a : GA D (G.V (.grid D.R.m k))}
    {b : GA D (G.V (.grid D.R.m (k + 1)))} {y y' : (AE D)ˣ} (hy : IsDetRoot _ a y) (hy' : IsDetRoot _ b y')
    {f : WO (G.V (.grid D.R.m k)) (G.V (.grid D.R.m (k + 1))) → ℂ} (hf : IsThetaFunO W.ψ _ _ f) :
    W.om (.mu t' D.R.m k) (a, b) f =
      ((((L.xi t' * (L.xi t)⁻¹) y)⁻¹ * (L.xi t' * (L.xi t)⁻¹) y' : Circle) : ℂ) • W.om (.mu t D.R.m k) (a, b) f := by
  have h0 := W.om_is (.mu t D.R.m k) ⟨le_rfl, hk⟩
  have h1 := W.om_is (.mu t' D.R.m k) ⟨le_rfl, hk⟩
  rw [chrS_mu t t', chrT_mu t t'] at h1
  exact GlobalTheory.TupRoot.twist_eq h0 h1 hy hy' hf

/- English proof (translation)
The claim follows from `GlobalTheory.Chain.InnerSteps.theta_pureTensorO W.ψ_std W.θ_is _ _ _ _ (ρ.vT_is t D.R.m k le_rfl hk).2.theta _`.
-/
theorem fock_theta (W : G.Weil) (ρ : RealMatch W) (t : T) (P : PolDown G) (k : ℕ) (hk : k < D.R.m) :
    IsThetaFunO W.ψ (G.V (.grid D.R.m k)) (G.V (.grid D.R.m (k + 1)))
      (fockD W t (fun j => ρ.vT D.R.m j) P ⟨k, hk⟩) :=
  GlobalTheory.Chain.InnerSteps.theta_pureTensorO W.ψ_std W.θ_is _ _ _ _ (ρ.vT_is t D.R.m k le_rfl hk).2.theta _

end GlobalTheory.ConTwist

namespace GlobalTheory.ConTwist

open GlobalTheory.RowChain GlobalTheory.Unf

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

/- English proof (translation)
Rewrite using `[GlobalTheory.HandHom.flatBF_smul, GlobalTheory.HandHom.flatFB_smul, contr_smul_left, contr_smul_right, smul_smul, mul_comm]`.
-/
theorem contr_flat_twist {ψ : AddChar (AF D.host.F) ℂ} {σ : ℕ} {B : BesLev D (σ + 1)} {J : JacLev D (σ + 1)}
    {B' : BesLev D σ} (s₁ : StepBF ψ B J) (s₂ : StepFB ψ J B') (l : Link B B'.L B'.ζ)
    (vL : VolM D B'.L.rank J.W₀.rank) (X : WO B.V J.W → ℂ) (Y : WO J.W B'.V → ℂ) (c₁ c₂ : ℂ) :
    contr l J.W₀ vL (flatBF s₁ (c₁ • X)) (flatFB s₂ (c₂ • Y)) =
      (c₁ * c₂) • contr l J.W₀ vL (flatBF s₁ X) (flatFB s₂ Y) := by
  rw [GlobalTheory.HandHom.flatBF_smul, GlobalTheory.HandHom.flatFB_smul, contr_smul_left, contr_smul_right, smul_smul, mul_comm]

/- English proof (translation)
Establish `k1` using `congrArg (flatBF (lastAt G W t' hM' j hj vN).s) he`. Establish `k2` using `GlobalTheory.HandHom.flatBF_smul (lastAt G W t' hM' j hj vN).s c (W.om (.mu t D.R.m j) (g, 1) Φ₁)`. Establish `k` using `k1.trans k2`. Unfold `lastDat`. Use `erw [k]`.

Use `erw [lastBi_smul]`. Both sides reduce to the same expression.
-/
theorem lastDat_twist (W : G.Weil) {t t' : T} {M M' : Vol G} (hM : M.Is t) (hM' : M'.Is t') (j : ℕ)
    (hj : j + 2 * 0 + 2 = D.R.m) (vN : VolN (besDecAt G j 0 hj)) (g : GA D (G.V (.grid D.R.m j)))
    (Φ₁ : WO (G.V (.grid D.R.m j)) (G.V (.grid D.R.m (j + 1))) → ℂ)
    (Φ₂ : WO (G.V (.grid D.R.m (j + 1))) (G.V (.grid D.R.m D.R.m)) → ℂ) (c : ℂ)
    (he : W.om (.mu t' D.R.m j) (g, 1) Φ₁ = c • W.om (.mu t D.R.m j) (g, 1) Φ₁) :
    lastDat W hM' j hj vN g Φ₁ Φ₂ = c • lastDat W hM j hj vN g Φ₁ Φ₂ := by
  have k1 := congrArg (flatBF (lastAt G W t' hM' j hj vN).s) he
  have k2 := GlobalTheory.HandHom.flatBF_smul (lastAt G W t' hM' j hj vN).s c (W.om (.mu t D.R.m j) (g, 1) Φ₁)
  have k := k1.trans k2
  unfold lastDat
  erw [k]
  erw [lastBi_smul]
  rfl

/- English proof (translation)
Distinguish the cases in `h0 : j + 2 * 0 + 2 = D.R.m`. Simplify using `only [conAt, h0, ↓reduceDIte]`. Establish `hr : IsDetRoot (G.V (.grid D.R.m (j + 1))) 1 (x D.R.m)` using `isDetRoot_one (hm ▸ hx D.R.m)`. Conclude with `lastDat_twist W hM hM' j h0 _ _ _ _ _ (om_mu_twist W t t' j (by omega) (hx j) hr (fock_theta W ρ t' P j (by omega)))`. Distinguish the cases in `h1 : j + 2 * ((D.R.m - 4 - j) / 2 + 1) + 2 = D.R.m`.

Simplify using `only [conAt, h0, h1, ↓reduceDIte]`. Establish `e1` using `om_mu_twist W t t' j (by omega) (hx j) (hx (j + 1)) (fock_theta W ρ t' P j (by omega))`. Establish `e2 : W.om (.mu t' D.R.m (j + 1)) (h (j + 1), h (j + 1 + 1)) (fockD W t' (fun j => ρ.vT D.R.m j) P ⟨j + 1, by omega⟩) = ((((L.xi t' * (L.xi t)⁻¹) (x (j + 1)))⁻¹ * (L.xi t' * (L.xi t)⁻¹) (x (j + 2)) : Circle) : ℂ) • W.om (.mu t D.R.m (j + 1)) (h (j + 1), h (j + 1 + 1)) (fockD W t' …` using `om_mu_twist W t t' (j + 1) (by omega) (hx (j + 1)) (hx (j + 2)) (fock_theta W ρ t' P (j + 1) (by omega))`. Use `erw [e1, e2]`. Use `(contr_flat_twist (J := jacAt G hM' (j + 1) ((D.R.m - 4 - j) / 2 + 1) (by omega)) _ _ _ _ _ _ _ _).trans ?_` and prove the remaining obligations.

Rewrite using `[← Circle.coe_mul]`. Establish `hc : ((L.xi t' * (L.xi t)⁻¹) (x j))⁻¹ * (L.xi t' * (L.xi t)⁻¹) (x (j + 1)) * (((L.xi t' * (L.xi t)⁻¹) (x (j + 1)))⁻¹ * (L.xi t' * (L.xi t)⁻¹) (x (j + 2))) = ((L.xi t' * (L.xi t)⁻¹) (x j))⁻¹ * (L.xi t' * (L.xi t)⁻¹) (x (j + 2))` using `by group`. Rewrite using `[hc]`. Both sides reduce to the same expression. Simplify using `only [conAt, h0, h1, ↓reduceDIte, smul_zero]`.
-/
theorem conAt_twist (W : G.Weil) (ρ : RealMatch W) (t t' : T) (M M' : Vol G) (hM : M.Is t) (hM' : M'.Is t')
    (P : PolDown G) (h : Pts G) (x : ℕ → (AE D)ˣ) (hx : ∀ k, IsDetRoot _ (h k) (x k)) (hm : h D.R.m = 1) (j : ℕ)
    (hjm : j < D.R.m) :
    conAt W hM' (fockD W t' (fun j => ρ.vT D.R.m j) P) h j =
      ((((L.xi t' * (L.xi t)⁻¹) (x j))⁻¹ * (L.xi t' * (L.xi t)⁻¹) (x (j + 2)) : Circle) : ℂ) •
        conAt W hM (fockD W t (fun j => ρ.vT D.R.m j) P) h j := by
  by_cases h0 : j + 2 * 0 + 2 = D.R.m
  · simp only [conAt, h0, ↓reduceDIte]
    have hr : IsDetRoot (G.V (.grid D.R.m (j + 1))) 1 (x D.R.m) := isDetRoot_one (hm ▸ hx D.R.m)
    exact lastDat_twist W hM hM' j h0 _ _ _ _ _
      (om_mu_twist W t t' j (by omega) (hx j) hr (fock_theta W ρ t' P j (by omega)))
  by_cases h1 : j + 2 * ((D.R.m - 4 - j) / 2 + 1) + 2 = D.R.m
  · simp only [conAt, h0, h1, ↓reduceDIte]
    have e1 := om_mu_twist W t t' j (by omega) (hx j) (hx (j + 1)) (fock_theta W ρ t' P j (by omega))
    have e2 : W.om (.mu t' D.R.m (j + 1)) (h (j + 1), h (j + 1 + 1)) (fockD W t' (fun j => ρ.vT D.R.m j) P ⟨j + 1, by omega⟩) =
        ((((L.xi t' * (L.xi t)⁻¹) (x (j + 1)))⁻¹ * (L.xi t' * (L.xi t)⁻¹) (x (j + 2)) : Circle) : ℂ) •
          W.om (.mu t D.R.m (j + 1)) (h (j + 1), h (j + 1 + 1)) (fockD W t' (fun j => ρ.vT D.R.m j) P ⟨j + 1, by omega⟩) :=
      om_mu_twist W t t' (j + 1) (by omega) (hx (j + 1)) (hx (j + 2)) (fock_theta W ρ t' P (j + 1) (by omega))
    erw [e1, e2]
    refine (contr_flat_twist (J := jacAt G hM' (j + 1) ((D.R.m - 4 - j) / 2 + 1) (by omega)) _ _ _ _ _ _ _ _).trans ?_
    rw [← Circle.coe_mul]
    have hc : ((L.xi t' * (L.xi t)⁻¹) (x j))⁻¹ * (L.xi t' * (L.xi t)⁻¹) (x (j + 1)) *
        (((L.xi t' * (L.xi t)⁻¹) (x (j + 1)))⁻¹ * (L.xi t' * (L.xi t)⁻¹) (x (j + 2))) =
        ((L.xi t' * (L.xi t)⁻¹) (x j))⁻¹ * (L.xi t' * (L.xi t)⁻¹) (x (j + 2)) := by
      group
    rw [hc]
    rfl
  · simp only [conAt, h0, h1, ↓reduceDIte, smul_zero]

end GlobalTheory.ConTwist

namespace GlobalTheory.ConTwist

/- English proof (translation)
Use `⟨0, fun _ _ _ => ⟨0, ?_⟩⟩` and prove the remaining obligations. Introduce `D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F _ ch _ _ t t' M M' hM hM' P h x hx hm j _ hjm`. Conclude with `conAt_twist ch.W ch.rm t t' M M' hM hM' P h x hx hm j hjm`.
-/
theorem conAt_twist_big : Big fun {D} _ _ _ _ {T} _ _ _ _ _ {R} ch => ∀ (t t' : T) (M M' : Vol ch.G) (hM : M.Is t) (hM' : M'.Is t') (P : PolDown ch.G) (h : Pts ch.G) (x : ℕ → (AE D)ˣ), (∀ k, IsDetRoot _ (h k) (x k)) → h D.R.m = 1 → ∀ j, Even j → j < D.R.m → conAt ch.W hM' (fockD ch.W t' (fun j => ch.rm.vT D.R.m j) P) h j = ((((R.toLevCh.xi t' * (R.toLevCh.xi t)⁻¹) (x j))⁻¹ * (R.toLevCh.xi t' * (R.toLevCh.xi t)⁻¹) (x (j + 2)) : Circle) : ℂ) • conAt ch.W hM (fockD ch.W t (fun j => ch.rm.vT D.R.m j) P) h j := by
  refine ⟨0, fun _ _ _ => ⟨0, ?_⟩⟩
  intro D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F _ ch _ _ t t' M M' hM hM' P h x hx hm j _ hjm
  exact conAt_twist ch.W ch.rm t t' M M' hM hM' P h x hx hm j hjm

end GlobalTheory.ConTwist
