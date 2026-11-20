import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LocalLanglandsExists

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.Whittaker GlobalTheory.LocLanglands

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocLanglands.LocalLanglandsExistence₂

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

/- English proof (translation)
Assemble the required witnesses or components as `⟨_, isPlaceOver_placeOf _ w⟩`.
-/
theorem exists_place (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) :
    ∃ A : ValuationSubring (AlgebraicClosure E), IsPlaceOver A w :=
  ⟨_, isPlaceOver_placeOf _ w⟩

/- English proof (translation)
Introduce `E Ω _ _ _ _ _ A w h` and use `let ⟨rc, hrc, _⟩ := H.1 E Ω A w h; ⟨rc, hrc.toLit⟩`.
-/
theorem localLanglandsExists_of_localLanglandsGL (H : GlobalTheory.Published.LocalLanglandsGL) : GlobalTheory.Published.LocalLanglandsExists :=
  fun E Ω _ _ _ _ _ A w h => let ⟨rc, hrc, _⟩ := H.1 E Ω A w h; ⟨rc, hrc.toLit⟩

/- English proof (translation)
Take `⟨n, a, rfl⟩` from `x.exists_rep`. Take `rfl : n = 0` from `by simpa using hx`. Conclude with `WD.sound ⟨.refl _ _, fun _ _ => Subsingleton.elim _ _, fun _ => Subsingleton.elim _ _⟩`.
-/
theorem eq_lpZero {x : WD h} (hx : x.lpDim = 0) : x = WD.lpZero h := by
  obtain ⟨n, a, rfl⟩ := x.exists_rep
  obtain rfl : n = 0 := by simpa using hx
  exact WD.sound ⟨.refl _ _, fun _ _ => Subsingleton.elim _ _, fun _ => Subsingleton.elim _ _⟩

/- English proof (translation)
Introduce and unpack `⟨n, a, ha, hi⟩`. Establish `h0` using `congrArg WD.lpDim ha`. Take `rfl : n = 0` from `by simpa [WD.lpZero] using h0`. Establish `: Nontrivial (Subrepresentation a.ρ)` using `hi.toNontrivial`. Take `⟨S, T, hST⟩` from `exists_pair_ne (Subrepresentation a.ρ)`.

Conclude with `hST (Subrepresentation.toSubmodule_injective (Subsingleton.elim _ _))`.
-/
theorem not_isIrrWD_lpZero : ¬ IsIrrWD (WD.lpZero h) := by
  rintro ⟨n, a, ha, hi⟩
  have h0 := congrArg WD.lpDim ha
  obtain rfl : n = 0 := by simpa [WD.lpZero] using h0
  have : Nontrivial (Subrepresentation a.ρ) := hi.toNontrivial
  obtain ⟨S, T, hST⟩ := exists_pair_ne (Subrepresentation a.ρ)
  exact hST (Subrepresentation.toSubmodule_injective (Subsingleton.elim _ _))

/- English proof (translation)
Establish `h1 : (x.lpChar y).lpDim = 0`. Take `⟨n, a, rfl⟩` from `x.exists_rep`. Take `⟨m, b, rfl⟩` from `y.exists_rep`. Take `rfl : m = 0` from `by simpa using hy`. Simplify using the standard rewrite rules.

Establish `h2 : ((x.lpChar y).lpSum (x.lpChar y)).lpDim = 0`. Take `⟨n, a, ha⟩` from `(x.lpChar y).exists_rep`. Rewrite `h1`, the goal using `[← ha]`. Take `rfl : n = 0` from `by simpa using h1`. Simplify using the standard rewrite rules.

Establish `h3` using `hε.add E w h ψ hψ hψ' (x.lpChar y) (x.lpChar y)`. Rewrite `h3` using `[(eq_lpZero h2).trans (eq_lpZero h1).symm]`. Conclude with `(mul_eq_left.1 h3.symm)`.
-/
theorem eps_tensor_zero {ε : EpsFamily A} (hε : IsDeligneEps ε) (ψ : AddChar (w.adicCompletion E) Circle)
    (hψ : Continuous ψ) (hψ' : ψ ≠ 1) (x y : WD h) (hy : y.lpDim = 0) : ε E w h ψ (x.lpChar y) = 1 := by
  have h1 : (x.lpChar y).lpDim = 0 := by
    obtain ⟨n, a, rfl⟩ := x.exists_rep
    obtain ⟨m, b, rfl⟩ := y.exists_rep
    obtain rfl : m = 0 := by simpa using hy
    simp
  have h2 : ((x.lpChar y).lpSum (x.lpChar y)).lpDim = 0 := by
    obtain ⟨n, a, ha⟩ := (x.lpChar y).exists_rep
    rw [← ha] at h1 ⊢
    obtain rfl : n = 0 := by simpa using h1
    simp
  have h3 := hε.add E w h ψ hψ hψ' (x.lpChar y) (x.lpChar y)
  rw [(eq_lpZero h2).trans (eq_lpZero h1).symm] at h3
  exact (mul_eq_left.1 h3.symm)

/- English proof (translation)
Take `⟨n, a, ha⟩` from `(rc ρ).exists_rep`. Use `show ((((rc ρ).lpTw ((((1 : ℕ) : ℝ) - 1) / 2)).lpChar (WD.lpSp h 1)).lpSum (WD.lpZero h)) = rc ρ`. Rewrite using `[← ha, WD.lpTw_mk, WD.lpSp, WD.lpChar_mk, WD.lpZero, WD.lpSum_mk]`. Use `WD.sound ⟨(LinearEquiv.prodUnique).trans ((TensorProduct.congr (.refl ℂ _) (LinearEquiv.funUnique (Fin 1) ℂ ℂ)).trans (TensorProduct.rid ℂ _)), fun σ v => ?_, fun v => ?_⟩` and prove the remaining obligations. Take `⟨v, u⟩` from `v show (TensorProduct.rid ℂ _) (TensorProduct.congr (.refl ℂ _) (LinearEquiv.funUnique (Fin 1) ℂ ℂ) (TensorProduct.map _ _ v)) = a.ρ σ ((TensorProduct.rid ℂ _) (TensorProduct.congr (.refl ℂ _) (LinearEquiv.funUnique (Fin 1) ℂ ℂ) v))`.

Proceed by induction on `v using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul x y => simp [WDRep.spEig, coe_qPow]`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`. Take `⟨v, u⟩` from `v show (TensorProduct.rid ℂ _) (TensorProduct.congr (.refl ℂ _) (LinearEquiv.funUnique (Fin 1) ℂ ℂ) (((a.tw ((((1 : ℕ) : ℝ) - 1) / 2)).tensor (WDRep.sp h 1)).N v)) = a.N ((TensorProduct.rid ℂ _) (TensorProduct.congr (.refl ℂ _) (LinearEquiv.funUnique (Fin 1) ℂ ℂ) v))`.

Proceed by induction on `v using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul x y => simp [shiftEnd_apply]`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`.
-/
theorem segSum_single (rc : IrrGL (w.adicCompletion E) → WD h) (ρ : IrrGL (w.adicCompletion E)) (hρ : ρ.IsCusp) :
    segSum rc [Segment.single ρ hρ] = rc ρ := by
  obtain ⟨n, a, ha⟩ := (rc ρ).exists_rep
  show ((((rc ρ).lpTw ((((1 : ℕ) : ℝ) - 1) / 2)).lpChar (WD.lpSp h 1)).lpSum (WD.lpZero h)) = rc ρ
  rw [← ha, WD.lpTw_mk, WD.lpSp, WD.lpChar_mk, WD.lpZero, WD.lpSum_mk]
  refine WD.sound ⟨(LinearEquiv.prodUnique).trans ((TensorProduct.congr (.refl ℂ _)
    (LinearEquiv.funUnique (Fin 1) ℂ ℂ)).trans (TensorProduct.rid ℂ _)), fun σ v => ?_, fun v => ?_⟩
  · obtain ⟨v, u⟩ := v
    show (TensorProduct.rid ℂ _) (TensorProduct.congr (.refl ℂ _) (LinearEquiv.funUnique (Fin 1) ℂ ℂ)
      (TensorProduct.map _ _ v)) = a.ρ σ ((TensorProduct.rid ℂ _)
        (TensorProduct.congr (.refl ℂ _) (LinearEquiv.funUnique (Fin 1) ℂ ℂ) v))
    induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp [WDRep.spEig, coe_qPow]
    | add x y hx hy => simp only [map_add, hx, hy]
  · obtain ⟨v, u⟩ := v
    show (TensorProduct.rid ℂ _) (TensorProduct.congr (.refl ℂ _) (LinearEquiv.funUnique (Fin 1) ℂ ℂ)
      (((a.tw ((((1 : ℕ) : ℝ) - 1) / 2)).tensor (WDRep.sp h 1)).N v)) = a.N ((TensorProduct.rid ℂ _)
        (TensorProduct.congr (.refl ℂ _) (LinearEquiv.funUnique (Fin 1) ℂ ℂ) v))
    induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp [shiftEnd_apply]
    | add x y hx hy => simp only [map_add, hx, hy]

/- English proof (translation)
Take `⟨a, ha, ε, -, H⟩` from `H`. Rewrite using `[H.one]`. Establish `: WD.lpOfChar h ((SmGL.unrChar (w.adicCompletion E) c).comp a) (ha.smooth hc) = WD.mk (WDRep.diag h fun _ : Fin 1 => c⁻¹)`. Simplify using `only [WD.lpOfChar, WDRep.diag, ha.unrChar_comp]`. Rewrite using `[this, WD.frobEig_diag]`.

Both sides reduce to the same expression.
-/
theorem frobEig_unr {rc : IrrGL (w.adicCompletion E) → WD h} (H : IsRecLit h rc) (c : ℂˣ)
    (hc : IsSmoothChar (SmGL.unrChar (w.adicCompletion E) c)) :
    (rc (.ofChar _ hc)).frobEig = {((c⁻¹ : ℂˣ) : ℂ)} := by
  obtain ⟨a, ha, ε, -, H⟩ := H
  rw [H.one]
  have : WD.lpOfChar h ((SmGL.unrChar (w.adicCompletion E) c).comp a) (ha.smooth hc) =
      WD.mk (WDRep.diag h fun _ : Fin 1 => c⁻¹) := by
    simp only [WD.lpOfChar, WDRep.diag, ha.unrChar_comp]
  rw [this, WD.frobEig_diag]
  rfl

/- English proof (translation)
Introduce and unpack `⟨a, ha, ε, -, H⟩`. Take `⟨_, h0⟩` from `H.bij.2 (WD.lpSp h 0)`. Take `⟨_, h1⟩` from `H.bij.2 (WD.lpSp h 1)`. Use `congrArg WD.lpDim (h0.symm.trans h1)` as an intermediate fact. Simplify using `at this`.
-/
theorem not_const (y : WD h) : ¬ IsRecLit h fun _ => y := by
  rintro ⟨a, ha, ε, -, H⟩
  obtain ⟨_, h0⟩ := H.bij.2 (WD.lpSp h 0)
  obtain ⟨_, h1⟩ := H.bij.2 (WD.lpSp h 1)
  have := congrArg WD.lpDim (h0.symm.trans h1)
  simp at this

end GlobalTheory.LocLanglands.LocalLanglandsExistence₂

end
