import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConstMemBddAut
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaInnerProductHermitian
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchwartzBruhatHalfSpanModulatedTranslates
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompletedHomLatticeMultipleMemOpenLevel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompletedHomLatticeFinitelyGenerated
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticFormUnitaryPairAction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisThetaLaws
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsInvariantForm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOrEqOfPlaceIdem
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor

noncomputable section

namespace GlobalTheory.ThetaOrth

variable {D : D7}

/- English proof (translation)
Rewrite using `[AddChar.map_neg_eq_inv, Complex.inv_eq_conj (hψ.1.2.1 x)]`.
-/
theorem conj_psi {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (x : AF D.host.F) :
    (starRingEnd ℂ) (ψ x) = ψ (-x) := by
  rw [AddChar.map_neg_eq_inv, Complex.inv_eq_conj (hψ.1.2.1 x)]

/- English proof (translation)
Establish `h` using `GlobalTheory.SplitScalar.symplO_smul S T (N : AE D) x y`. Rewrite `h` using `[map_natCast]`. Simplify `h` using `only [Nat.cast_smul_eq_nsmul]`.
-/
theorem symplO_nsmul (S T : HSp D) (N : ℕ) (x y : WO S T) :
    symplO S T (N • x) y = symplO S T x (N • y) := by
  have h := GlobalTheory.SplitScalar.symplO_smul S T (N : AE D) x y
  rw [map_natCast] at h
  simpa only [Nat.cast_smul_eq_nsmul] using h

/- English proof (translation)
Simplify using `only [symplO, hO, Matrix.neg_apply, map_neg, mul_neg, neg_mul, Finset.sum_neg_distrib]`.
-/
theorem symplO_neg_right (S T : HSp D) (x y : WO S T) :
    symplO S T x (-y) = -symplO S T x y := by
  simp only [symplO, hO, Matrix.neg_apply, map_neg, mul_neg, neg_mul, Finset.sum_neg_distrib]

/- English proof (translation)
Introduce `i j`. Establish `e : (N • y) i j = N • y i j` using `rfl`. Rewrite using `[e, nsmul_eq_mul, mul_left_comm, hy i j]`.
-/
theorem isHalf_nsmul {m n : ℕ} {b : AE D} {y : Mx D m n} (hy : IsHalf b y) (N : ℕ) : IsHalf b (N • y) := by
  intro i j
  have e : (N • y) i j = N • y i j := rfl
  rw [e, nsmul_eq_mul, mul_left_comm, hy i j]

/- English proof (translation)
Introduce `i j`. Establish `e : (-y) i j = -y i j` using `rfl`. Rewrite using `[e, mul_neg, hy i j]`.
-/
theorem isHalf_neg {m n : ℕ} {b : AE D} {y : Mx D m n} (hy : IsHalf b y) : IsHalf b (-y) := by
  intro i j
  have e : (-y) i j = -y i j := rfl
  rw [e, mul_neg, hy i j]

/- English proof (translation)
Introduce `i j`. Establish `e : (x + y) i j = x i j + y i j` using `rfl`. Rewrite using `[e, mul_add, hx i j, hy i j]`.
-/
theorem isHalf_add {m n : ℕ} {b : AE D} {x y : Mx D m n} (hx : IsHalf b x) (hy : IsHalf b y) : IsHalf b (x + y) := by
  intro i j
  have e : (x + y) i j = x i j + y i j := rfl
  rw [e, mul_add, hx i j, hy i j]

/- English proof (translation)
Rewrite using `[smul_add, h, smul_neg, mul_smul, smul_neg, add_neg_cancel_right]`.
-/
theorem nsmul_add_neg {A : Type} [AddCommGroup A] (N k : ℕ) (t u v : A) (h : N • t = u + (N * k) • v) :
    N • (t + k • (-v)) = u := by
  rw [smul_add, h, smul_neg, mul_smul, smul_neg, add_neg_cancel_right]

/- English proof (translation)
Rewrite using `[smul_add, mul_smul]`.
-/
theorem nsmul_add_mul {A : Type} [AddCommGroup A] (N k : ℕ) (t v : A) :
    N • (t + k • v) = N • t + (N * k) • v := by
  rw [smul_add, mul_smul]

/- English proof (translation)
Establish `hu : IsUnit (N : AE D)`. Establish `h1 : IsUnit (N : D.host.E)` using `(Nat.cast_ne_zero.2 hN.ne').isUnit`. Simplify `h1.map (incA D)` using `only [map_natCast]`. Use `Matrix.ext fun i j => ?_` and prove the remaining obligations. Establish `e : N • x i j = N • y i j` using `congrFun (congrFun h i) j`.

Rewrite `e` using `[nsmul_eq_mul, nsmul_eq_mul]`. Conclude with `hu.mul_left_cancel e`.
-/
theorem nsmul_inj {m n : ℕ} {N : ℕ} (hN : 0 < N) {x y : Mx D m n} (h : N • x = N • y) : x = y := by
  have hu : IsUnit (N : AE D) := by
    have h1 : IsUnit (N : D.host.E) := (Nat.cast_ne_zero.2 hN.ne').isUnit
    simpa only [map_natCast] using h1.map (incA D)
  refine Matrix.ext fun i j => ?_
  have e : N • x i j = N • y i j := congrFun (congrFun h i) j
  rw [nsmul_eq_mul, nsmul_eq_mul] at e
  exact hu.mul_left_cancel e

def charSpan (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (b : AE D) : Submodule ℂ (WO S T → ℂ) :=
  Submodule.span ℂ {p | ∃ y : WO S T, IsHalf b y ∧ p = fun t => ψ (symplO S T t y)}

open Classical in

/- English proof (translation)
Proceed by induction on `hΨ using Submodule.span_induction with`. Consider the case `mem Ψ h`. Take `⟨x, y, hx, hy, rfl⟩` from `h`. Distinguish the cases in `hxΛ : x ∈ Λ`. Use `⟨fun t => ψ (symplO S T t (N • y)), Submodule.subset_span ⟨N • y, isHalf_nsmul hy N, rfl⟩, fun t ht htΛ => ?_⟩` and prove the remaining obligations.

Establish `h1 : halfInd a Λ (N • t + x) = 1` using `if_pos ⟨Λ.add_mem htΛ hxΛ, isHalf_add (isHalf_nsmul ht N) hx⟩`. Use `show ψ (symplO S T (N • t) y) * halfInd a Λ (N • t + x) = _`. Rewrite using `[h1, mul_one, symplO_nsmul]`. Use `⟨0, Submodule.zero_mem _, fun t ht htΛ => ?_⟩` and prove the remaining obligations. Establish `h1 : halfInd a Λ (N • t + x) = 0` using `if_neg fun h => hxΛ (by`.

Use `Λ.sub_mem h.1 htΛ` as an intermediate fact. Rewrite using `[add_sub_cancel_left] at this)` and apply the resulting hypothesis. Use `show ψ (symplO S T (N • t) y) * halfInd a Λ (N • t + x) = 0`. Rewrite using `[h1, mul_zero]`. Consider the case `zero => exact ⟨0, Submodule.zero_mem _, fun _ _ _ => rfl⟩`.

Consider the case `add Ψ₁ Ψ₂ _ _ h₁ h₂`. Take `⟨q₁, m₁, e₁⟩` from `h₁`. Take `⟨q₂, m₂, e₂⟩` from `h₂`. Conclude with `⟨q₁ + q₂, Submodule.add_mem _ m₁ m₂, fun t ht hΛ => by`. Rewrite using `[Pi.add_apply, Pi.add_apply, e₁ t ht hΛ, e₂ t ht hΛ]⟩`.

Consider the case `smul c Ψ _ h`. Take `⟨q, m, e⟩` from `h`. Conclude with `⟨c • q, Submodule.smul_mem _ c m, fun t ht hΛ => by`. Rewrite using `[Pi.smul_apply, Pi.smul_apply, e t ht hΛ]⟩`.
-/
theorem exists_char_of_wave {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {a : AE D} {Λ : AddSubgroup (WO S T)} (N : ℕ)
    {Ψ : WO S T → ℂ}
    (hΨ : Ψ ∈ Submodule.span ℂ {Ψ : WO S T → ℂ | ∃ x y : WO S T, IsHalf a x ∧ IsHalf (cA D a) y ∧
      Ψ = fun t => ψ (symplO S T t y) * halfInd a Λ (t + x)}) :
    ∃ q ∈ charSpan ψ S T (cA D a), ∀ t : WO S T, IsHalf a t → N • t ∈ Λ → Ψ (N • t) = q t := by
  induction hΨ using Submodule.span_induction with
  | mem Ψ h =>
    obtain ⟨x, y, hx, hy, rfl⟩ := h
    by_cases hxΛ : x ∈ Λ
    · refine ⟨fun t => ψ (symplO S T t (N • y)), Submodule.subset_span ⟨N • y, isHalf_nsmul hy N, rfl⟩, fun t ht htΛ => ?_⟩
      have h1 : halfInd a Λ (N • t + x) = 1 :=
        if_pos ⟨Λ.add_mem htΛ hxΛ, isHalf_add (isHalf_nsmul ht N) hx⟩
      show ψ (symplO S T (N • t) y) * halfInd a Λ (N • t + x) = _
      rw [h1, mul_one, symplO_nsmul]
    · refine ⟨0, Submodule.zero_mem _, fun t ht htΛ => ?_⟩
      have h1 : halfInd a Λ (N • t + x) = 0 := if_neg fun h => hxΛ (by
        have := Λ.sub_mem h.1 htΛ
        rwa [add_sub_cancel_left] at this)
      show ψ (symplO S T (N • t) y) * halfInd a Λ (N • t + x) = 0
      rw [h1, mul_zero]
  | zero => exact ⟨0, Submodule.zero_mem _, fun _ _ _ => rfl⟩
  | add Ψ₁ Ψ₂ _ _ h₁ h₂ =>
    obtain ⟨q₁, m₁, e₁⟩ := h₁
    obtain ⟨q₂, m₂, e₂⟩ := h₂
    exact ⟨q₁ + q₂, Submodule.add_mem _ m₁ m₂, fun t ht hΛ => by
      rw [Pi.add_apply, Pi.add_apply, e₁ t ht hΛ, e₂ t ht hΛ]⟩
  | smul c Ψ _ h =>
    obtain ⟨q, m, e⟩ := h
    exact ⟨c • q, Submodule.smul_mem _ c m, fun t ht hΛ => by
      rw [Pi.smul_apply, Pi.smul_apply, e t ht hΛ]⟩

/- English proof (translation)
Establish `hψ` using `hw.std`. Establish `hF` using `hw.om_pres (1, g) f hf`. Establish `laws` using `fun {u v : WO S T → ℂ} (hu : IsThetaFunO ψ S T u) (hv : IsThetaFunO ψ S T v) => GlobalTheory.ThetaPairingLaws.ipO_laws D ψ S T μ 𝓕 hψ hμ u v hu hv`. Establish `hzero : IsThetaFunO ψ S T (0 : WO S T → ℂ)`. Use `GlobalTheory.WeilVacMove.isTheta_smul (0 : ℂ) hf` as an intermediate fact.

Rewrite `this` using `[zero_smul]`. Then use the resulting hypothesis. Proceed by induction on `hp using Submodule.span_induction with`. Consider the case `mem p h`. Take `⟨y, hy, rfl⟩` from `h`. Establish `hθ` using `(GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ S T).1`.

Use `set w : WO S T := actO S T 1⁻¹ g⁻¹ (-y) with hwdef`. Establish `hact : actO S T 1 g w = -y` using `GlobalTheory.AdelicLatMove.actO_actO_inv S T 1 g (-y)`. Establish `hwh : IsHalf (cA D a) w` using `GlobalTheory.SplitHecke.isHalf_actO _ _ (isHalf_neg hy)`. Establish `e1 : (Tm fun t => ψ (symplO S T t y) * Φ t) = heisO ψ S T y f`. Rewrite using `[hfT]`.

Conclude with `hTm.modul Φ hΦ y hy`. Establish `e2 : (fun t => (starRingEnd ℂ) (ψ (symplO S T (actO S T 1 g t) y)) * Φ t) = fun t => ψ (symplO S T t w) * Φ t`. Use function extensionality and compare the values at `t`. Rewrite using `[conj_psi hψ, ← GlobalTheory.SymplOInv.symplO_actO D S T 1 g t w, hact, symplO_neg_right]`. Establish `e3 : (Tm fun t => ψ (symplO S T t w) * Φ t) = heisO ψ S T w f`.

Rewrite using `[hfT]`. Conclude with `hTm.modul Φ hΦ w hwh`. Use `show IsThetaFunO ψ S T (Tm fun t => ψ (symplO S T t y) * Φ t) ∧ IsThetaFunO ψ S T (Tm fun t => (starRingEnd ℂ) (ψ (symplO S T (actO S T 1 g t) y)) * Φ t) ∧ ipO μ 𝓕 (om (1, g) f) (Tm fun t => ψ (symplO S T t y) * Φ t) = ipO μ 𝓕 (om (1, g) (Tm fun t => (starRingEnd ℂ) (ψ (symplO S …`. Rewrite using `[e2, e1, e3]`. Use `⟨hθ y f hf, hθ w f hf, ?_⟩` and prove the remaining obligations.

Rewrite using `[hw.om_heis 1 g w f hf, hact]`. Use `((laws hF hf).2.2.2.2.2.2.1 (-y)).2` as an intermediate fact. Rewrite `this` using `[neg_neg]`. Conclude with `this.symm`. Consider the case `zero`.

Establish `e1 : (Tm fun t => (0 : WO S T → ℂ) t * Φ t) = 0`. Establish `: (fun t => (0 : WO S T → ℂ) t * Φ t) = 0` using `by funext t; simp`. Rewrite using `[this, map_zero]`. Establish `e2 : (Tm fun t => (starRingEnd ℂ) ((0 : WO S T → ℂ) (actO S T 1 g t)) * Φ t) = 0`. Establish `: (fun t => (starRingEnd ℂ) ((0 : WO S T → ℂ) (actO S T 1 g t)) * Φ t) = 0` using `by funext t; simp`.

Rewrite using `[this, map_zero]`. Rewrite using `[e1, e2, map_zero]`. Use `⟨hzero, hzero, ?_⟩` and prove the remaining obligations. Simplify using `[ipO]`. Consider the case `add p₁ p₂ _ _ h₁ h₂`.

Take `⟨a₁, b₁, c₁⟩` from `h₁`. Take `⟨a₂, b₂, c₂⟩` from `h₂`. Establish `e1 : (Tm fun t => (p₁ + p₂) t * Φ t) = (Tm fun t => p₁ t * Φ t) + Tm fun t => p₂ t * Φ t`. Rewrite using `[← map_add]`. Use `congr 1`.

Use function extensionality and compare the values at `t`. Simplify using `[add_mul]`. Establish `e2 : (Tm fun t => (starRingEnd ℂ) ((p₁ + p₂) (actO S T 1 g t)) * Φ t) = (Tm fun t => (starRingEnd ℂ) (p₁ (actO S T 1 g t)) * Φ t) + Tm fun t => (starRingEnd ℂ) (p₂ (actO S T 1 g t)) * Φ t`. Rewrite using `[← map_add]`. Use `congr 1`.

Use function extensionality and compare the values at `t`. Simplify using `[add_mul]`. Rewrite using `[e1, e2, map_add]`. Use `⟨GlobalTheory.WeilVacMove.isTheta_add a₁ a₂, GlobalTheory.WeilVacMove.isTheta_add b₁ b₂, ?_⟩` and prove the remaining obligations. Rewrite using `[((laws a₁ hF).2.2.2.1 _ a₂).2, ((laws (hw.om_pres _ _ b₁) hf).2.2.2.1 _ (hw.om_pres _ _ b₂)).1, c₁, c₂]`.

Consider the case `smul c p _ h`. Take `⟨a₁, b₁, c₁⟩` from `h`. Establish `e1 : (Tm fun t => (c • p) t * Φ t) = c • Tm fun t => p t * Φ t`. Rewrite using `[← map_smul]`. Use `congr 1`.

Use function extensionality and compare the values at `t`. Simplify using `[mul_assoc]`. Establish `e2 : (Tm fun t => (starRingEnd ℂ) ((c • p) (actO S T 1 g t)) * Φ t) = (starRingEnd ℂ) c • Tm fun t => (starRingEnd ℂ) (p (actO S T 1 g t)) * Φ t`. Rewrite using `[← map_smul]`. Use `congr 1`.

Use function extensionality and compare the values at `t`. Simplify using `[mul_assoc]`. Rewrite using `[e1, e2, map_smul]`. Use `⟨GlobalTheory.WeilVacMove.isTheta_smul _ a₁, GlobalTheory.WeilVacMove.isTheta_smul _ b₁, ?_⟩` and prove the remaining obligations. Rewrite using `[((laws hF a₁).2.2.1 c).2, ((laws (hw.om_pres _ _ b₁) hf).2.2.1 _).1, c₁]`.
-/
theorem pairing_charSpan {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hw : IsWeilDatumO ψ S T χS χT om)
    {a : AE D} {Λ : AddSubgroup (WO S T)} {f₀ Φ f : WO S T → ℂ} {Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)}
    (hTm : IsPlaceModel ψ (symplO S T) (heisO ψ S T) a Λ 1 f₀ Tm) (hΦ : IsSBHalf a Λ Φ) (hfT : f = Tm Φ)
    (hf : IsThetaFunO ψ S T f) {μ : Measure (WO S T)} {𝓕 : Set (WO S T)} (hμ : IsCovolOne (ratL T S) μ 𝓕)
    (g : GA D T) {p : WO S T → ℂ} (hp : p ∈ charSpan ψ S T (cA D a)) :
    IsThetaFunO ψ S T (Tm fun t => p t * Φ t) ∧
      IsThetaFunO ψ S T (Tm fun t => (starRingEnd ℂ) (p (actO S T 1 g t)) * Φ t) ∧
      ipO μ 𝓕 (om (1, g) f) (Tm fun t => p t * Φ t) =
        ipO μ 𝓕 (om (1, g) (Tm fun t => (starRingEnd ℂ) (p (actO S T 1 g t)) * Φ t)) f := by
  have hψ := hw.std
  have hF := hw.om_pres (1, g) f hf
  have laws := fun {u v : WO S T → ℂ} (hu : IsThetaFunO ψ S T u) (hv : IsThetaFunO ψ S T v) =>
    GlobalTheory.ThetaPairingLaws.ipO_laws D ψ S T μ 𝓕 hψ hμ u v hu hv
  have hzero : IsThetaFunO ψ S T (0 : WO S T → ℂ) := by
    have := GlobalTheory.WeilVacMove.isTheta_smul (0 : ℂ) hf
    rwa [zero_smul] at this
  induction hp using Submodule.span_induction with
  | mem p h =>
    obtain ⟨y, hy, rfl⟩ := h
    have hθ := (GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ S T).1
    set w : WO S T := actO S T 1⁻¹ g⁻¹ (-y) with hwdef
    have hact : actO S T 1 g w = -y := GlobalTheory.AdelicLatMove.actO_actO_inv S T 1 g (-y)
    have hwh : IsHalf (cA D a) w := GlobalTheory.SplitHecke.isHalf_actO _ _ (isHalf_neg hy)
    have e1 : (Tm fun t => ψ (symplO S T t y) * Φ t) = heisO ψ S T y f := by
      rw [hfT]; exact hTm.modul Φ hΦ y hy
    have e2 : (fun t => (starRingEnd ℂ) (ψ (symplO S T (actO S T 1 g t) y)) * Φ t) =
        fun t => ψ (symplO S T t w) * Φ t := by
      funext t
      rw [conj_psi hψ, ← GlobalTheory.SymplOInv.symplO_actO D S T 1 g t w, hact, symplO_neg_right]
    have e3 : (Tm fun t => ψ (symplO S T t w) * Φ t) = heisO ψ S T w f := by
      rw [hfT]; exact hTm.modul Φ hΦ w hwh
    show IsThetaFunO ψ S T (Tm fun t => ψ (symplO S T t y) * Φ t) ∧
      IsThetaFunO ψ S T (Tm fun t => (starRingEnd ℂ) (ψ (symplO S T (actO S T 1 g t) y)) * Φ t) ∧
      ipO μ 𝓕 (om (1, g) f) (Tm fun t => ψ (symplO S T t y) * Φ t) =
        ipO μ 𝓕 (om (1, g) (Tm fun t => (starRingEnd ℂ) (ψ (symplO S T (actO S T 1 g t) y)) * Φ t)) f
    rw [e2, e1, e3]
    refine ⟨hθ y f hf, hθ w f hf, ?_⟩
    rw [hw.om_heis 1 g w f hf, hact]
    have := ((laws hF hf).2.2.2.2.2.2.1 (-y)).2
    rw [neg_neg] at this
    exact this.symm
  | zero =>
    have e1 : (Tm fun t => (0 : WO S T → ℂ) t * Φ t) = 0 := by
      have : (fun t => (0 : WO S T → ℂ) t * Φ t) = 0 := by funext t; simp
      rw [this, map_zero]
    have e2 : (Tm fun t => (starRingEnd ℂ) ((0 : WO S T → ℂ) (actO S T 1 g t)) * Φ t) = 0 := by
      have : (fun t => (starRingEnd ℂ) ((0 : WO S T → ℂ) (actO S T 1 g t)) * Φ t) = 0 := by funext t; simp
      rw [this, map_zero]
    rw [e1, e2, map_zero]
    refine ⟨hzero, hzero, ?_⟩
    simp [ipO]
  | add p₁ p₂ _ _ h₁ h₂ =>
    obtain ⟨a₁, b₁, c₁⟩ := h₁
    obtain ⟨a₂, b₂, c₂⟩ := h₂
    have e1 : (Tm fun t => (p₁ + p₂) t * Φ t) = (Tm fun t => p₁ t * Φ t) + Tm fun t => p₂ t * Φ t := by
      rw [← map_add]; congr 1; funext t; simp [add_mul]
    have e2 : (Tm fun t => (starRingEnd ℂ) ((p₁ + p₂) (actO S T 1 g t)) * Φ t) =
        (Tm fun t => (starRingEnd ℂ) (p₁ (actO S T 1 g t)) * Φ t) +
          Tm fun t => (starRingEnd ℂ) (p₂ (actO S T 1 g t)) * Φ t := by
      rw [← map_add]; congr 1; funext t; simp [add_mul]
    rw [e1, e2, map_add]
    refine ⟨GlobalTheory.WeilVacMove.isTheta_add a₁ a₂, GlobalTheory.WeilVacMove.isTheta_add b₁ b₂, ?_⟩
    rw [((laws a₁ hF).2.2.2.1 _ a₂).2, ((laws (hw.om_pres _ _ b₁) hf).2.2.2.1 _ (hw.om_pres _ _ b₂)).1, c₁, c₂]
  | smul c p _ h =>
    obtain ⟨a₁, b₁, c₁⟩ := h
    have e1 : (Tm fun t => (c • p) t * Φ t) = c • Tm fun t => p t * Φ t := by
      rw [← map_smul]; congr 1; funext t; simp [mul_assoc]
    have e2 : (Tm fun t => (starRingEnd ℂ) ((c • p) (actO S T 1 g t)) * Φ t) =
        (starRingEnd ℂ) c • Tm fun t => (starRingEnd ℂ) (p (actO S T 1 g t)) * Φ t := by
      rw [← map_smul]; congr 1; funext t; simp [mul_assoc]
    rw [e1, e2, map_smul]
    refine ⟨GlobalTheory.WeilVacMove.isTheta_smul _ a₁, GlobalTheory.WeilVacMove.isTheta_smul _ b₁, ?_⟩
    rw [((laws hF a₁).2.2.1 c).2, ((laws (hw.om_pres _ _ b₁) hf).2.2.1 _).1, c₁]

/- English proof (translation)
Introduce `D ψ S T χS χT om hw ΛS ΛT hS hT Z e he f₀ Φ f hΦ hth hf μ 𝓕 hμ g hg hsupp`. Take `⟨⟨Tm, hTm⟩, hall⟩` from `hth`. Establish `hfT` using `hall Tm hTm`. Establish `ho` using `(GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum he).conj`. Establish `hψ` using `hw.std`.

Establish `hac : cA D e * cA D (cA D e) = 0` using `by rw [cA_cA, mul_comm, he.2]`. Take `⟨k, hk, hinv, hsup⟩` from `hΦ.2`. Take `⟨M, hM, hMact⟩` from `(GlobalTheory.LatLevel.level_of_generators D S T ΛS ΛT hS hT (GlobalTheory.LatFinGen.latO_finitely_generated D S T ΛS ΛT hS hT)).2 1 g`. Use `set Λ := latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True with hΛ`. Use `set N : ℕ := M * k with hN`.

Establish `hNpos : 0 < N` using `Nat.mul_pos hM hk`. Set `Ψ : WO S T → ℂ` to `fun u => if ∃ t, Φ t ≠ 0 ∧ N • t = u then 1 else 0`. Establish `hNt : ∀ t, Φ t ≠ 0 → N • t ∈ Λ` using `fun t ht => by`. Rewrite using `[hN, mul_smul]`. Conclude with `Λ.nsmul_mem (hsup t ht) M`.

Establish `hΨ : IsSBHalf (cA D e) Λ Ψ`. Use `⟨fun u hu => ?_, N * k, Nat.mul_pos hNpos hk, fun v hv hvh u => ?_, fun u hu => ?_⟩` and prove the remaining obligations. Establish `: ∃ t, Φ t ≠ 0 ∧ N • t = u`. Assume the negation of the conclusion as `h`. Conclude with `hu (if_neg h)`.

Take `⟨t, ht, rfl⟩` from `this`. Conclude with `isHalf_nsmul (hΦ.1 t ht) N`. Establish `key : (∃ t, Φ t ≠ 0 ∧ N • t = u + (N * k) • v) ↔ ∃ t, Φ t ≠ 0 ∧ N • t = u`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨t, ht, h⟩`.

Use `⟨t + k • (-v), by rwa [hinv (-v) (Λ.neg_mem hv) (isHalf_neg hvh) t], ?_⟩` and prove the remaining obligations. Conclude with `nsmul_add_neg N k t u v h`. Introduce and unpack `⟨t, ht, rfl⟩`. Use `⟨t + k • v, by rwa [hinv v hv hvh t], ?_⟩` and prove the remaining obligations. Conclude with `nsmul_add_mul N k t v`.

Use `show (if _ then _ else _) = (if _ then _ else _)`. Simplify using `only [key]`. Establish `: ∃ t, Φ t ≠ 0 ∧ N • t = u`. Assume the negation of the conclusion as `h`. Conclude with `hu (if_neg h)`.

Take `⟨t, ht, rfl⟩` from `this`. Conclude with `Λ.nsmul_mem (hNt t ht) _`. Establish `hspan` using `(GlobalTheory.PlaceTensor.halfWaves_span D ψ S T ΛS ΛT hψ hS hT (cA D e) ho.idem hac ho.infPart_eq).2 Ψ hΨ`. Take `⟨q, hq, hqΨ⟩` from `exists_char_of_wave N hspan`. Take `⟨-, -, hip⟩` from `pairing_charSpan hw hTm hΦ hfT hf hμ g hq`.

Establish `hq1 : ∀ t, Φ t ≠ 0 → q t = 1` using `fun t ht => by`. Rewrite using `[← hqΨ t (hΦ.1 t ht) (hNt t ht)]`. Conclude with `if_pos ⟨t, ht, rfl⟩`. Establish `hq0 : ∀ t, Φ t ≠ 0 → q (actO S T 1 g t) = 0` using `fun t ht => by`. Establish `h1 : N • actO S T 1 g t ∈ Λ`.

Use `hMact (k • t) (hsup t ht)` as an intermediate fact. Establish `e : actO S T 1 g (k • t) = k • actO S T 1 g t` using `map_nsmul (GlobalTheory.LatLevel.actHom S T 1 g) k t`. Rewrite `this` using `[e, ← mul_smul]`. Then use the resulting hypothesis. Rewrite using `[← hqΨ _ (GlobalTheory.SplitHecke.isHalf_actO _ _ (hΦ.1 t ht)) h1]`. Use `if_neg ?_` and prove the remaining obligations.

Introduce and unpack `⟨t', ht', h⟩`. Establish `: t' = actO S T 1 g t` using `nsmul_inj hNpos h`. Conclude with `ht' (this ▸ hsupp t ht)`. Establish `e1 : (fun t => q t * Φ t) = Φ`. Use function extensionality and compare the values at `t`.

Distinguish the cases in `h : Φ t = 0`. Rewrite using `[h, mul_zero]`. Rewrite using `[hq1 t h, one_mul]`. Establish `e2 : (fun t => (starRingEnd ℂ) (q (actO S T 1 g t)) * Φ t) = 0`. Use function extensionality and compare the values at `t`.

Distinguish the cases in `h : Φ t = 0`. Simplify using `[h]`. Simplify using `[hq0 t h]`. Rewrite `hip` using `[e1, e2, map_zero, map_zero, ← hfT]`. Use `show ipO μ 𝓕 (om (1, g) f) f = 0`.

Rewrite using `[hip]`. Simplify using `[ipO]`.
-/
theorem orth : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ (Z : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e Z → ∀ (f₀ Φ f : WO S T → ℂ), IsSBHalf (cA D e) (latO S T ΛS ΛT fun _ => True) Φ → IsThetaAt ψ (symplO S T) (heisO ψ S T) (cA D e) (latO S T ΛS ΛT fun _ => True) 1 f₀ Φ f → IsThetaFunO ψ S T f → ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ g ∈ GfC T, (∀ x, Φ x ≠ 0 → Φ (actO S T 1 g x) = 0) → l2 μ 𝓕 (om (1, g) f) f = 0 := by
  classical
  intro D ψ S T χS χT om hw ΛS ΛT hS hT Z e he f₀ Φ f hΦ hth hf μ 𝓕 hμ g hg hsupp
  obtain ⟨⟨Tm, hTm⟩, hall⟩ := hth
  have hfT := hall Tm hTm
  have ho := (GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum he).conj
  have hψ := hw.std
  have hac : cA D e * cA D (cA D e) = 0 := by rw [cA_cA, mul_comm, he.2]
  obtain ⟨k, hk, hinv, hsup⟩ := hΦ.2
  obtain ⟨M, hM, hMact⟩ := (GlobalTheory.LatLevel.level_of_generators D S T ΛS ΛT hS hT
    (GlobalTheory.LatFinGen.latO_finitely_generated D S T ΛS ΛT hS hT)).2 1 g
  set Λ := latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True with hΛ
  set N : ℕ := M * k with hN
  have hNpos : 0 < N := Nat.mul_pos hM hk

  let Ψ : WO S T → ℂ := fun u => if ∃ t, Φ t ≠ 0 ∧ N • t = u then 1 else 0
  have hNt : ∀ t, Φ t ≠ 0 → N • t ∈ Λ := fun t ht => by
    rw [hN, mul_smul]; exact Λ.nsmul_mem (hsup t ht) M
  have hΨ : IsSBHalf (cA D e) Λ Ψ := by
    refine ⟨fun u hu => ?_, N * k, Nat.mul_pos hNpos hk, fun v hv hvh u => ?_, fun u hu => ?_⟩
    · have : ∃ t, Φ t ≠ 0 ∧ N • t = u := by
        by_contra h; exact hu (if_neg h)
      obtain ⟨t, ht, rfl⟩ := this
      exact isHalf_nsmul (hΦ.1 t ht) N
    · have key : (∃ t, Φ t ≠ 0 ∧ N • t = u + (N * k) • v) ↔ ∃ t, Φ t ≠ 0 ∧ N • t = u := by
        constructor
        · rintro ⟨t, ht, h⟩
          refine ⟨t + k • (-v), by rwa [hinv (-v) (Λ.neg_mem hv) (isHalf_neg hvh) t], ?_⟩
          exact nsmul_add_neg N k t u v h
        · rintro ⟨t, ht, rfl⟩
          refine ⟨t + k • v, by rwa [hinv v hv hvh t], ?_⟩
          exact nsmul_add_mul N k t v
      show (if _ then _ else _) = (if _ then _ else _)
      simp only [key]
    · have : ∃ t, Φ t ≠ 0 ∧ N • t = u := by
        by_contra h; exact hu (if_neg h)
      obtain ⟨t, ht, rfl⟩ := this
      exact Λ.nsmul_mem (hNt t ht) _
  have hspan := (GlobalTheory.PlaceTensor.halfWaves_span D ψ S T ΛS ΛT hψ hS hT (cA D e) ho.idem hac ho.infPart_eq).2 Ψ hΨ
  obtain ⟨q, hq, hqΨ⟩ := exists_char_of_wave N hspan
  obtain ⟨-, -, hip⟩ := pairing_charSpan hw hTm hΦ hfT hf hμ g hq
  have hq1 : ∀ t, Φ t ≠ 0 → q t = 1 := fun t ht => by
    rw [← hqΨ t (hΦ.1 t ht) (hNt t ht)]
    exact if_pos ⟨t, ht, rfl⟩
  have hq0 : ∀ t, Φ t ≠ 0 → q (actO S T 1 g t) = 0 := fun t ht => by
    have h1 : N • actO S T 1 g t ∈ Λ := by
      have := hMact (k • t) (hsup t ht)
      have e : actO S T 1 g (k • t) = k • actO S T 1 g t := map_nsmul (GlobalTheory.LatLevel.actHom S T 1 g) k t
      rwa [e, ← mul_smul] at this
    rw [← hqΨ _ (GlobalTheory.SplitHecke.isHalf_actO _ _ (hΦ.1 t ht)) h1]
    refine if_neg ?_
    rintro ⟨t', ht', h⟩
    have : t' = actO S T 1 g t := nsmul_inj hNpos h
    exact ht' (this ▸ hsupp t ht)
  have e1 : (fun t => q t * Φ t) = Φ := by
    funext t
    by_cases h : Φ t = 0
    · rw [h, mul_zero]
    · rw [hq1 t h, one_mul]
  have e2 : (fun t => (starRingEnd ℂ) (q (actO S T 1 g t)) * Φ t) = 0 := by
    funext t
    by_cases h : Φ t = 0
    · simp [h]
    · simp [hq0 t h]
  rw [e1, e2, map_zero, map_zero, ← hfT] at hip
  show ipO μ 𝓕 (om (1, g) f) f = 0
  rw [hip]
  simp [ipO]

end GlobalTheory.ThetaOrth
