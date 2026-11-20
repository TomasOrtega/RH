import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierTCoefCap
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.IsBuiltPlaceOfCompactTest
import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.Admissible
import Formalism.SharpRestriction.CuspSpanNormBounds.NonemptyParameterModels.AmpTensorDSdNonemptyOfSubsingleton
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.FamilyFormalDegreeLowerBound
import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeLitG

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped Matrix

namespace Formalism.L2.SG.Pf.CarrierXAll

open Formalism.L2.SG.Pf.Carrier Formalism.L2.SG.Pf.BaseOf Formalism.L2.SG.Pf.Built Formalism.L2.SG.LocWSOf Formalism.L2.SG.Pf.CarrierT

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/- English proof (translation)
Substitute `h` using the available equality. Conclude with `hf`.
-/
theorem isHCParam_cast {m n : ℕ} (h : m = n) (f : Fin n → ℝ) (hf : Formalism.QuantumDeterminants.IsHCParam f) :
    Formalism.QuantumDeterminants.IsHCParam (fun i : Fin m => f (Fin.cast h i)) := by
  subst h
  exact hf

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

/- English proof (translation)
Establish `hf` using `Formalism.MainNotions.S.Inh.amp_isHCParam_lamSH D.R (D.hc (X.pl w))`. Establish `e : X.B.lam w = fun i => lamSH D.R (D.hc (X.pl w)) (Fin.cast (X.n_eq.trans (dimS_eq D.R).symm) i)`. Use function extensionality and compare the values at `i`. Rewrite using `[X.lam_eq]`. Both sides reduce to the same expression.

Rewrite using `[e]`. Conclude with `isHCParam_cast _ _ hf`.
-/
theorem isHCParam_lamX (w : InfinitePlace X.B.I.F) : Formalism.QuantumDeterminants.IsHCParam (X.B.lam w) := by
  have hf := Formalism.MainNotions.S.Inh.amp_isHCParam_lamSH D.R (D.hc (X.pl w))
  have e : X.B.lam w = fun i => lamSH D.R (D.hc (X.pl w)) (Fin.cast (X.n_eq.trans (dimS_eq D.R).symm) i) := by
    funext i
    rw [X.lam_eq]
    rfl
  rw [e]
  exact isHCParam_cast _ _ hf

/- English proof (translation)
Use `⟨Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * large₂.sc.L, ?_, ?_⟩` and prove the remaining obligations. Establish `hg` using `Formalism.MainNotions.BridgeLemma.szh_gap hS0 (X.pl w) set c : Fin X.B.I.n → Fin (2 * D.R.rS + D.R.k + 1) := Fin.cast (X.n_eq.trans (dimS_eq D.R).symm) with hc`. Establish `ea : ∀ a, X.B.I.ε w a = epsSH D.R (c a)` using `fun a => by rw [X.eps_eq]; rfl`. Establish `la : ∀ a, X.B.lam w a = lamSH D.R (D.hc (X.pl w)) (c a)` using `fun a => by rw [X.lam_eq]; rfl`. Introduce `a b hab`.

Rewrite using `[la a, la b]`. Conclude with `hg (c a) (c b) (by rwa [ea a, ea b] at hab)`. Establish `hn : (D.R.r : ℝ) = (X.B.I.n : ℝ)` using `by rw [X.n_eq]`. Establish `hrS : 2 * D.R.rS + 2 = D.R.m` using `Ranks.rS_two D.R`. Establish `hr : D.R.r = 2 * D.R.rS + D.R.k + 1` using `by unfold Ranks.r; omega`.

Establish `hn900 : (900 : ℝ) ≤ (X.B.I.n : ℝ)`. Rewrite using `[← hn, hr]`. Use `push_cast`. Establish `: (1801 : ℝ) ≤ (D.R.k : ℝ)` using `by exact_mod_cast hk`. Establish `: (0 : ℝ) ≤ (D.R.rS : ℝ)` using `Nat.cast_nonneg _`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hthr` using `Formalism.MainNotions.GapDS.thrX_le (X.B.I.ε w) hn900`. Rewrite `hthr` using `[← hn]`. Establish `hkL` using `Formalism.MainNotions.BridgeLemma.szh_k_le hS0 (by linarith) (X.pl w)`. Establish `hk5 : (5 : ℝ) ≤ (D.R.k : ℝ)` using `by exact_mod_cast Formalism.MainNotions.BridgeLemma.five_le_k D`.

Establish `hL : (1 / 2 : ℝ) ≤ large₂.sc.L`. Assume the negation of the conclusion as `hcn`. Use `push Not at hcn`. Establish `h1 : Real.exp (2 * large₂.sc.L) < Real.exp 1` using `Real.exp_lt_exp.mpr (by linarith)`. Establish `h2 : Real.exp 1 < 3` using `by have := Real.exp_one_lt_d9; linarith`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hf : (2 : ℝ) ≤ (D.R.f : ℝ)`. Establish `: 2 ≤ D.R.f`. Unfold `Ranks.f Ranks.n; have := And.intro (Nat.one_le_two_pow (n := D.R.e)) (show 0 < D.R.ord by positivity); omega`. Conclude with `this` after adjusting the coercions.

Establish `hf5 : (32 : ℝ) ≤ (D.R.f : ℝ) ^ 5`. Establish `: (2 : ℝ) ^ 5 ≤ (D.R.f : ℝ) ^ 5` using `pow_le_pow_left₀ (by norm_num) hf 5`. Evaluate the numerical expressions using `at this`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hn1 : (1 : ℝ) ≤ (D.R.r : ℝ)`.

Rewrite using `[hr]`. Use `push_cast`. Establish `: (0 : ℝ) ≤ (D.R.rS : ℝ)` using `Nat.cast_nonneg _`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hn19 : 0 ≤ (D.R.r : ℝ) ^ 19` using `by positivity`.

Establish `h3 : (D.R.r : ℝ) ^ 3 ≤ (D.R.r : ℝ) ^ 19` using `pow_le_pow_right₀ hn1 (by norm_num)`. Establish `e1 : Cl * (D.R.r : ℝ) ^ 19 * 32 ≤ Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5` using `mul_le_mul_of_nonneg_left hf5 (by positivity)`. Establish `e2 : Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * (1 / 2) ≤ Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * large₂.sc.L` using `mul_le_mul_of_nonneg_left hL (by positivity)`. Establish `e3 : 1000 * (D.R.r : ℝ) ^ 19 ≤ Cl * (D.R.r : ℝ) ^ 19` using `mul_le_mul_of_nonneg_right hCl hn19`. Establish `hr0 : (0 : ℝ) < (D.R.r : ℝ) ^ 19` using `by positivity`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem gap_X {large₂ : SizeData₂ D} {C' Cl Cg cb Cu cT CT : ℝ} (hS0 : StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT) (hCl : 1000 ≤ Cl)
    (hk : 1801 ≤ D.R.k) (w : InfinitePlace X.B.I.F) :
    ∃ h : ℝ, Formalism.QuantumDeterminants.GapAtLeast (X.B.I.ε w) (X.B.lam w) h ∧ Formalism.MainNotions.GapDS.thrX (X.B.I.ε w) < h := by
  refine ⟨Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * large₂.sc.L, ?_, ?_⟩
  · have hg := Formalism.MainNotions.BridgeLemma.szh_gap hS0 (X.pl w)
    set c : Fin X.B.I.n → Fin (2 * D.R.rS + D.R.k + 1) := Fin.cast (X.n_eq.trans (dimS_eq D.R).symm) with hc
    have ea : ∀ a, X.B.I.ε w a = epsSH D.R (c a) := fun a => by rw [X.eps_eq]; rfl
    have la : ∀ a, X.B.lam w a = lamSH D.R (D.hc (X.pl w)) (c a) := fun a => by rw [X.lam_eq]; rfl
    intro a b hab
    rw [la a, la b]
    exact hg (c a) (c b) (by rwa [ea a, ea b] at hab)
  · have hn : (D.R.r : ℝ) = (X.B.I.n : ℝ) := by rw [X.n_eq]
    have hrS : 2 * D.R.rS + 2 = D.R.m := Ranks.rS_two D.R
    have hr : D.R.r = 2 * D.R.rS + D.R.k + 1 := by unfold Ranks.r; omega
    have hn900 : (900 : ℝ) ≤ (X.B.I.n : ℝ) := by
      rw [← hn, hr]; push_cast
      have : (1801 : ℝ) ≤ (D.R.k : ℝ) := by exact_mod_cast hk
      have : (0 : ℝ) ≤ (D.R.rS : ℝ) := Nat.cast_nonneg _
      linarith
    have hthr := Formalism.MainNotions.GapDS.thrX_le (X.B.I.ε w) hn900
    rw [← hn] at hthr
    have hkL := Formalism.MainNotions.BridgeLemma.szh_k_le hS0 (by linarith) (X.pl w)
    have hk5 : (5 : ℝ) ≤ (D.R.k : ℝ) := by exact_mod_cast Formalism.MainNotions.BridgeLemma.five_le_k D
    have hL : (1 / 2 : ℝ) ≤ large₂.sc.L := by
      by_contra hcn
      push Not at hcn
      have h1 : Real.exp (2 * large₂.sc.L) < Real.exp 1 := Real.exp_lt_exp.mpr (by linarith)
      have h2 : Real.exp 1 < 3 := by have := Real.exp_one_lt_d9; linarith
      linarith
    have hf : (2 : ℝ) ≤ (D.R.f : ℝ) := by
      have : 2 ≤ D.R.f := by
        unfold Ranks.f Ranks.n; have := And.intro (Nat.one_le_two_pow (n := D.R.e)) (show 0 < D.R.ord by positivity); omega
      exact_mod_cast this
    have hf5 : (32 : ℝ) ≤ (D.R.f : ℝ) ^ 5 := by
      have : (2 : ℝ) ^ 5 ≤ (D.R.f : ℝ) ^ 5 := pow_le_pow_left₀ (by norm_num) hf 5
      norm_num at this; linarith
    have hn1 : (1 : ℝ) ≤ (D.R.r : ℝ) := by
      rw [hr]; push_cast; have : (0 : ℝ) ≤ (D.R.rS : ℝ) := Nat.cast_nonneg _; linarith
    have hn19 : 0 ≤ (D.R.r : ℝ) ^ 19 := by positivity
    have h3 : (D.R.r : ℝ) ^ 3 ≤ (D.R.r : ℝ) ^ 19 := pow_le_pow_right₀ hn1 (by norm_num)
    have e1 : Cl * (D.R.r : ℝ) ^ 19 * 32 ≤ Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 :=
      mul_le_mul_of_nonneg_left hf5 (by positivity)
    have e2 : Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * (1 / 2) ≤ Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * large₂.sc.L :=
      mul_le_mul_of_nonneg_left hL (by positivity)
    have e3 : 1000 * (D.R.r : ℝ) ^ 19 ≤ Cl * (D.R.r : ℝ) ^ 19 := mul_le_mul_of_nonneg_right hCl hn19
    have hr0 : (0 : ℝ) < (D.R.r : ℝ) ^ 19 := by positivity
    linarith

/- English proof (translation)
Establish `h2' : Qiᴴ * Qᴴ = 1` using `by rw [← Matrix.conjTranspose_mul, h2, Matrix.conjTranspose_one]`. Establish `hU : ∀ g : Matrix (Fin n) (Fin n) ℂ, Formalism.QuantumDeterminants.inUH J g → Formalism.QuantumDeterminants.inUH K (Qi * g * Q)`. Introduce `g hg`. Establish `hg' : gᴴ * J * g = J` using `hg`. Use `show (Qi * g * Q)ᴴ * K * (Qi * g * Q) = K`.

Rewrite using `[← h3]`. Simplify using `only [Matrix.conjTranspose_mul, Matrix.mul_assoc]`. Rewrite using `[← Matrix.mul_assoc Qiᴴ Qᴴ, h2', Matrix.one_mul, ← Matrix.mul_assoc Q Qi, h2, Matrix.one_mul]`. Rewrite using `[← Matrix.mul_assoc gᴴ J, ← Matrix.mul_assoc (gᴴ * J) g, hg']`. Establish `hback : ∀ g : Matrix (Fin n) (Fin n) ℂ, Q * (Qi * g * Q) * Qi = g`.

Introduce `g`. Rewrite using `[← Matrix.mul_assoc, ← Matrix.mul_assoc, h2, Matrix.one_mul, Matrix.mul_assoc, h2, Matrix.mul_one]`. Set `Lφ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] Matrix (Fin m) (Fin m) ℂ` to `{ toFun := fun g => Qi * g * Q map_add' := fun x y => by simp only [Matrix.mul_add, Matrix.add_mul] map_smul' := fun c x => by simp only [RingHom.id_apply, Matrix.mul_smul, Matrix.smul_mul] }`. Establish `hφ : ContDiff ℝ ⊤ (fun g : Matrix (Fin n) (Fin n) ℂ => Qi * g * Q)` using `(LinearMap.toContinuousLinearMap Lφ).contDiff`. Introduce `g₀ hg₀`.

Take `⟨U, F, hUo, h0, hF, hE⟩` from `hs (Qi * g₀ * Q) (hU g₀ hg₀)`. Use `⟨(fun g => Qi * g * Q) ⁻¹' U, fun g => F (Qi * g * Q), hUo.preimage hφ.continuous, h0, hF.comp (hφ.of_le le_top).contDiffOn (fun g hg => hg), ?_⟩` and prove the remaining obligations. Introduce `g hgU hgJ`. Use `hE _ hgU (hU g hgJ)` as an intermediate fact. Simplify using `only [hback] at this`.

Conclude with `this`.
-/
theorem smooth_tr {n m : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (J : Matrix (Fin n) (Fin n) ℂ) (K : Matrix (Fin m) (Fin m) ℂ)
    (Q : Matrix (Fin n) (Fin m) ℂ) (Qi : Matrix (Fin m) (Fin n) ℂ) (h1 : Qi * Q = 1) (h2 : Q * Qi = 1)
    (h3 : Qᴴ * J * Q = K) (b : H) (hs : Formalism.QuantumDeterminants.SmoothOnH K (fun x => σ (Q * x * Qi) b)) :
    Formalism.QuantumDeterminants.SmoothOnH J (fun g => σ g b) := by
  have h2' : Qiᴴ * Qᴴ = 1 := by rw [← Matrix.conjTranspose_mul, h2, Matrix.conjTranspose_one]
  have hU : ∀ g : Matrix (Fin n) (Fin n) ℂ, Formalism.QuantumDeterminants.inUH J g → Formalism.QuantumDeterminants.inUH K (Qi * g * Q) := by
    intro g hg
    have hg' : gᴴ * J * g = J := hg
    show (Qi * g * Q)ᴴ * K * (Qi * g * Q) = K
    rw [← h3]
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Qiᴴ Qᴴ, h2', Matrix.one_mul, ← Matrix.mul_assoc Q Qi, h2, Matrix.one_mul]
    rw [← Matrix.mul_assoc gᴴ J, ← Matrix.mul_assoc (gᴴ * J) g, hg']
  have hback : ∀ g : Matrix (Fin n) (Fin n) ℂ, Q * (Qi * g * Q) * Qi = g := by
    intro g
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h2, Matrix.one_mul, Matrix.mul_assoc, h2, Matrix.mul_one]
  let Lφ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] Matrix (Fin m) (Fin m) ℂ :=
    { toFun := fun g => Qi * g * Q
      map_add' := fun x y => by simp only [Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun c x => by simp only [RingHom.id_apply, Matrix.mul_smul, Matrix.smul_mul] }
  have hφ : ContDiff ℝ ⊤ (fun g : Matrix (Fin n) (Fin n) ℂ => Qi * g * Q) :=
    (LinearMap.toContinuousLinearMap Lφ).contDiff
  intro g₀ hg₀
  obtain ⟨U, F, hUo, h0, hF, hE⟩ := hs (Qi * g₀ * Q) (hU g₀ hg₀)
  refine ⟨(fun g => Qi * g * Q) ⁻¹' U, fun g => F (Qi * g * Q), hUo.preimage hφ.continuous, h0,
    hF.comp (hφ.of_le le_top).contDiffOn (fun g hg => hg), ?_⟩
  intro g hgU hgJ
  have := hE _ hgU (hU g hgJ)
  simp only [hback] at this
  exact this

variable {θ : ℝ} (C : Choice X θ)

variable [Fact Formalism.L2.SG.Pf.CarrierT.CoefCapAll] in

/- English proof (translation)
Establish `hb : ∀ j, b j ∈ PI.PhMeasCore.smoothVecs (Formalism.REAL.Jm (X.B.I.ε (tauE X e j))) (X.B.σ (tauE X e j))`. Introduce `j`. Establish `hsmv : Formalism.MainNotions.S.IsSmoothVec (k` using `D.R.k) (r := D.R.rS) (sigB X (C.Q (e (plE D j))) (C.Qi (e (plE D j))) (e (plE D j))) (b j) := Formalism.L2.SG.LitS.kFinSmooth_pi Formalism.L2.SG.Pf.k_finite_smooth D.R.k D.R.rS (epsSH D.R) (lamD D (e (plE D j))) _ (sigB X (C.Q (e (plE D j))) (C.Qi (e (plE D j))) (e (plE D j))) (F …`. Take `⟨h1, h2, h3, -⟩` from `C.isT (e (plE D j))`. Conclude with `smooth_tr (X.B.σ (vOf X (e (plE D j)))) _ _ (C.Q (e (plE D j))) (C.Qi (e (plE D j))) h1 h2 h3 (b j) hsmv`.

Conclude with `coefCap_carrierInT X C u u' e he hv CA de de' l grid grid1 a b ξ ξ' cc c (nuE X C u' e i0') (m0E X C u u' e) Θ TP A₀ hb (isHCParam_lamX X) (gap_X X hS0 hCl hk)`.
-/
theorem coefCap_ITc {large₂ : SizeData₂ D} {C' Cl Cg cb Cu cT CT : ℝ} (hS0 : StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT) (hCl : 1000 ≤ Cl)
    (hk : 1801 ≤ D.R.k) (u u' : D.what₂.Word) (e : InfinitePlace D.host.E ≃ D.what₂.Tau) (he : PlaceTie X e)
    (hv : D.host.v = Formalism.FourierDecayAlt.S6.rd D.host.E / 2) (CA : ℝ) (de de' : ℕ → ℝ) (l : ℕ)
    (grid : Fin (nfE D) → ℕ → Finset ℝ) (grid1 : Fin (nfE D) → Finset ℝ)
    (a b : ∀ j : Fin (nfE D), X.B.H (tauE X e j)) (ξ : ∀ j : Fin (nfE D), X.Vloc u (tauE X e j))
    (ξ' : ∀ j : Fin (nfE D), X.Vloc u' (tauE X e j)) (cc : Fin (nfE D) → ℂ)
    (c : Formalism.FourierDecayAlt.LE.Cut) (i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k)
    (Θ : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.Top.TopLift D.R.k D.R.rS (X.Vloc u (tauE X e j)) (X.Vloc u' (tauE X e j)))
    (TP : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.Top.TypeProj (parE e u u' de de' j) (towersOf X C u u' e j).base.π
      (towersOf X C u u' e j).base.z (m0E X C u u' e j *ᵥ nuE X C u' e i0' j)) (A₀ : ℝ)
    (hkb : ∀ j, PI.UpqRep.IsKFinHpk (k := D.R.k) (r := D.R.rS)
      (sigB X (C.Q (e (plE D j))) (C.Qi (e (plE D j))) (e (plE D j))) (b j)) :
    CoefCap (ITc X C u u' e he hv CA de de' l grid grid1 (fcT X C e u u' a b ξ ξ' cc) c i0' Θ TP A₀) := by
  have hb : ∀ j, b j ∈ PI.PhMeasCore.smoothVecs (Formalism.REAL.Jm (X.B.I.ε (tauE X e j))) (X.B.σ (tauE X e j)) := by
    intro j
    have hsmv : Formalism.MainNotions.S.IsSmoothVec (k := D.R.k) (r := D.R.rS)
        (sigB X (C.Q (e (plE D j))) (C.Qi (e (plE D j))) (e (plE D j))) (b j) :=
      Formalism.L2.SG.LitS.kFinSmooth_pi Formalism.L2.SG.Pf.k_finite_smooth D.R.k D.R.rS (epsSH D.R) (lamD D (e (plE D j))) _
        (sigB X (C.Q (e (plE D j))) (C.Qi (e (plE D j))) (e (plE D j))) (Formalism.MainNotions.S.Inh.amp_isHCParam_lamD D _)
        (Formalism.L2.SG.Pf.dsTr C (e (plE D j))) (b j) (hkb j)
    obtain ⟨h1, h2, h3, -⟩ := C.isT (e (plE D j))
    exact smooth_tr (X.B.σ (vOf X (e (plE D j)))) _ _ (C.Q (e (plE D j))) (C.Qi (e (plE D j))) h1 h2 h3 (b j) hsmv
  exact coefCap_carrierInT X C u u' e he hv CA de de' l grid grid1 a b ξ ξ' cc c (nuE X C u' e i0') (m0E X C u u' e) Θ TP A₀
    hb (isHCParam_lamX X) (gap_X X hS0 hCl hk)

end Formalism.L2.SG.Pf.CarrierXAll
