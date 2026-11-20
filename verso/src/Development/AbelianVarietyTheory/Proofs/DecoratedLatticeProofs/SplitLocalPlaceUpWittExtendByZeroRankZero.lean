import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CombAtSingleZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastDat
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntIndFromCols
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TypeChainPrincipalEntryNeZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumTransportSourceRationalIsometryStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.T2SpaceMatrixOfIsNonarchimedeanLocalField
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

noncomputable section
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocMod.RankZeroSrc

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Establish `h : x * p.pr a = p.π (p.ι x * (incA D a : AE D))` using `by rw [map_mul, p.π_ι]; rfl`. Rewrite using `[h, p.ι_π, ← mul_assoc, Witness.e_ι]`.
-/
theorem ι_mul_incA (p : Place D k) (x : k) (a : D.host.E) : p.ι x * (incA D a : AE D) = p.ι (x * p.pr a) := by
  have h : x * p.pr a = p.π (p.ι x * (incA D a : AE D)) := by rw [map_mul, p.π_ι]; rfl
  rw [h, p.ι_π, ← mul_assoc, Witness.e_ι]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [rat, Matrix.mul_apply, Matrix.map_apply, map_sum, ι_mul_incA]`.
-/
theorem map_ι_mul_rat (p : Place D k) {l m : ℕ} {Y : Type} [Fintype Y] (N : Matrix Y (Fin l) k)
    (M : Matrix (Fin l) (Fin m) D.host.E) :
    (N.map p.ι) * (rat M : Matrix (Fin l) (Fin m) (AE D)) = (N * M.map p.pr).map p.ι := by
  ext i j
  simp only [rat, Matrix.mul_apply, Matrix.map_apply, map_sum, ι_mul_incA]

/- English proof (translation)
Use `conv_rhs => rw [← Matrix.fromCols_toCols x]`. Use `congr 1`. Use extensionality with `i j`. Conclude with `j.elim0`.
-/
theorem fromCols_toCols₁ {Z n : Type} (x : Matrix Z (n ⊕ Fin 0) k) : fromCols x.toCols₁ 0 = x := by
  conv_rhs => rw [← Matrix.fromCols_toCols x]
  congr 1
  ext i j
  exact j.elim0

/- English proof (translation)
Establish `hq : J.d.q0 * J.d.i₀ = 1` using `rat_injective (by rw [rat_mul, rat_one]; exact J.d.p0_j0)`. Establish `hq' : J.d.q0.map p.pr * J.d.i₀.map p.pr = 1`. Rewrite using `[← show (J.d.q0 * J.d.i₀).map p.pr = J.d.q0.map p.pr * J.d.i₀.map p.pr from Matrix.map_mul (f := Witness.prH p), hq]`. Conclude with `Matrix.map_one _ (map_zero (Witness.prH p)) (map_one (Witness.prH p))`. Establish `hβ : F.β.toCols₁ = J.d.i₀.map p.pr * F₀.β` using `by ext r a; exact hF.2.1 r a`.

Establish `h1 : F.β * F.γ = 1` using `F.βγ`. Establish `h0 : F.β.toCols₂ * F.γ.toRows₂ = 0` using `by ext i j; simp [Matrix.mul_apply]`. Rewrite `h1` using `[← Matrix.fromCols_toCols F.β, ← Matrix.fromRows_toRows F.γ, Matrix.fromCols_mul_fromRows, h0, add_zero, hβ]`. Establish `hγ : F.γ.toRows₁ = F₀.γ * J.d.q0.map p.pr`. Establish `e : F₀.γ * J.d.q0.map p.pr * (J.d.i₀.map p.pr * F₀.β * F.γ.toRows₁) = F.γ.toRows₁`.

Rewrite using `[show F₀.γ * J.d.q0.map p.pr * (J.d.i₀.map p.pr * F₀.β * F.γ.toRows₁) = F₀.γ * (J.d.q0.map p.pr * J.d.i₀.map p.pr) * F₀.β * F.γ.toRows₁ by simp only [Matrix.mul_assoc], hq', Matrix.mul_one, F₀.γβ, Matrix.one_mul]`. Rewrite using `[← e, h1, Matrix.mul_one]`. Rewrite using `[HypDec.matrixExtendByZero_apply]`. Unfold `Place.up`. Rewrite using `[HypDec.p0, map_ι_mul_rat]`.

Use `congr 1`. Use `conv_rhs => rw [← Matrix.fromRows_toRows F.γ, Matrix.mul_assoc, Matrix.fromCols_mul_fromRows, Matrix.zero_mul, add_zero, hγ]`. Simplify using `only [Matrix.mul_assoc]`.
-/
theorem splitLocalPlace_up_wittExtendByZero_rankZero (p : Place D k) {n Z : Type} [Fintype n] [DecidableEq n] [Fintype Z] [DecidableEq Z] (J : JacLev D 0)
    (s hh : k) (F₀ : Frame k J.W₀.rank n) (F : Frame k J.W.rank (n ⊕ Fin 0)) (hF : p.IsJacFrame J s hh F₀ F) (T : HSp D)
    (FT : Frame k T.rank Z) (x : Matrix Z n k) :
    J.d.ext0 T (p.up F₀ FT x) = p.up F FT (fromCols x 0) := by
  have hq : J.d.q0 * J.d.i₀ = 1 := rat_injective (by rw [rat_mul, rat_one]; exact J.d.p0_j0)
  have hq' : J.d.q0.map p.pr * J.d.i₀.map p.pr = 1 := by
    rw [← show (J.d.q0 * J.d.i₀).map p.pr = J.d.q0.map p.pr * J.d.i₀.map p.pr from Matrix.map_mul (f := Witness.prH p), hq]
    exact Matrix.map_one _ (map_zero (Witness.prH p)) (map_one (Witness.prH p))
  have hβ : F.β.toCols₁ = J.d.i₀.map p.pr * F₀.β := by ext r a; exact hF.2.1 r a
  have h1 : F.β * F.γ = 1 := F.βγ
  have h0 : F.β.toCols₂ * F.γ.toRows₂ = 0 := by ext i j; simp [Matrix.mul_apply]
  rw [← Matrix.fromCols_toCols F.β, ← Matrix.fromRows_toRows F.γ, Matrix.fromCols_mul_fromRows, h0, add_zero, hβ] at h1
  have hγ : F.γ.toRows₁ = F₀.γ * J.d.q0.map p.pr := by
    have e : F₀.γ * J.d.q0.map p.pr * (J.d.i₀.map p.pr * F₀.β * F.γ.toRows₁) = F.γ.toRows₁ := by
      rw [show F₀.γ * J.d.q0.map p.pr * (J.d.i₀.map p.pr * F₀.β * F.γ.toRows₁) =
          F₀.γ * (J.d.q0.map p.pr * J.d.i₀.map p.pr) * F₀.β * F.γ.toRows₁ by simp only [Matrix.mul_assoc],
        hq', Matrix.mul_one, F₀.γβ, Matrix.one_mul]
    rw [← e, h1, Matrix.mul_one]
  rw [HypDec.matrixExtendByZero_apply]
  unfold Place.up
  rw [HypDec.p0, map_ι_mul_rat]
  congr 1
  conv_rhs => rw [← Matrix.fromRows_toRows F.γ, Matrix.mul_assoc, Matrix.fromCols_mul_fromRows, Matrix.zero_mul, add_zero, hγ]
  simp only [Matrix.mul_assoc]

/- English proof (translation)
Establish `h` using `d.hO_ext T 0 0 0 0 w w'`. Simplify using `only [map_zero, zero_add, add_zero, pairS, Matrix.mul_zero, trace_zero] at h`. Unfold `symplO`. Rewrite using `[h]`.
-/
theorem wittExtensionByZero_symplectic_form_eq {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (T : HSp D) (w w' : WO S₀ T) :
    symplO S T (d.ext0 T w) (d.ext0 T w') = symplO S₀ T w w' := by
  have h := d.hO_ext T 0 0 0 0 w w'
  simp only [map_zero, zero_add, add_zero, pairS, Matrix.mul_zero, trace_zero] at h
  unfold symplO
  rw [h]

/- English proof (translation)
Introduce `i j` and use `by rw [HypDec.matrixExtendByZero_apply, Matrix.mul_apply, Finset.mul_sum] exact Finset.sum_congr rfl fun l _ => by rw [← mul_assoc, hy i l]`.
-/
theorem wittExtensionByZero_preserves_isHalf {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (T : HSp D) {e : AE D} {y : WO S₀ T} (hy : IsHalf e y) :
    IsHalf e (d.ext0 T y) := fun i j => by
  rw [HypDec.matrixExtendByZero_apply, Matrix.mul_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => by rw [← mul_assoc, hy i l]

end GlobalTheory.LocMod.RankZeroSrc

namespace GlobalTheory.LocMod.RankZeroSrc

/- English proof (translation)
Introduce `D k _ _ _ _ p ψ hψ J s hh n Z _ _ _ _ F₀ F hF T FT Tm hM`. Apply the tactic sequence `have hT := GlobalTheory.T.weil_datum_transport_source_rational_isometry D ψ J.W J.W₀ T J.d hψ`. Use `haveI := GlobalTheory.FinPl.Comm.t2Space_matrix_of_isNonarchimedeanLocalField (k := k) (n := Z) (n' := n ⊕ Fin 0)`. Establish `hc1 : Continuous fun x : Matrix Z (n ⊕ Fin 0) k => x.toCols₁` using `continuous_pi fun i => continuous_pi fun j => by show Continuous fun a : Matrix Z (n ⊕ Fin 0) k => a i (Sum.inl j)`. Conclude with `(continuous_apply (Sum.inl j)).comp (continuous_apply i)`.

Establish `hc2 : Continuous fun x : Matrix Z n k => (fromCols x 0 : Matrix Z (n ⊕ Fin 0) k)` using `continuous_pi fun i => continuous_pi fun j => by`. Break down `j with j | j` into its components or cases. Use `show Continuous fun a : Matrix Z n k => a i j`. Conclude with `(continuous_apply j).comp (continuous_apply i)`. Conclude with `j.elim0`.

Set `R : SB (Matrix Z n k) → SB (Matrix Z (n ⊕ Fin 0) k)` to `fun Ψ => ⟨fun x => Ψ.1 x.toCols₁, GlobalTheory.FinPl.Comm.comp_mem_SB Ψ.2 hc1 hc2 fromCols_toCols₁⟩`. Establish `hR : ∀ Ψ x, (R Ψ).1 x = Ψ.1 x.toCols₁` using `fun _ _ => rfl`. Set `T₂ : SB (Matrix Z n k) →ₗ[ℂ] (WO J.W₀ T → ℂ)` to `{ toFun := fun Ψ w => Tm (R Ψ) (J.d.ext0 T w) map_add' := fun Ψ Ψ' => by`. Use function extensionality and compare the values at `w`. Rewrite using `[show R (Ψ + Ψ') = R Ψ + R Ψ' from Subtype.ext rfl, map_add]`.

Both sides reduce to the same expression. Use the proof step `map_smul' := fun c Ψ => by`. Use function extensionality and compare the values at `w`. Rewrite using `[show R (c • Ψ) = c • R Ψ from Subtype.ext rfl, map_smul]`. Use `rfl }`.

Establish `hT₂ : ∀ Ψ w, T₂ Ψ w = Tm (R Ψ) (J.d.ext0 T w)` using `fun _ _ => rfl`. Establish `hup : ∀ x, p.up F FT x = J.d.ext0 T (p.up F₀ FT x.toCols₁)` using `fun x => by`. Rewrite using `[splitLocalPlace_up_wittExtendByZero_rankZero p J s hh F₀ F hF T FT, fromCols_toCols₁]`. Use `⟨T₂, ⟨fun Ψ => ?_, fun x Ψ Ψ' h => ?_, fun y hy Ψ Ψ' h => ?_⟩, fun Ψ Φ h w => ?_⟩` and prove the remaining obligations. Conclude with `(hT.2.2.1 (Tm (R Ψ))).2 (hM.theta _)`.

Establish `e1 : Tm (R Ψ') = heisO ψ J.W T (p.up F FT (fromCols x 0)) (Tm (R Ψ))` using `hM.trans _ _ _ fun t => by`. Rewrite using `[hR, hR, h]`. Use `congr 1`. Use function extensionality and compare the values at `w`. Rewrite using `[hT₂, e1, ← splitLocalPlace_up_wittExtendByZero_rankZero p J s hh F₀ F hF T FT]`.

Simplify using `only [heisO, hT₂]`. Rewrite using `[J.d.wittDecomp_sympl_extAnisotropic_extAnisotropic, map_add]`. Establish `e1 : Tm (R Ψ') = heisO ψ J.W T (J.d.ext0 T y) (Tm (R Ψ))` using `hM.modul _ (wittExtensionByZero_preserves_isHalf J.d T hy) _ _ fun t => by`. Rewrite using `[hR, hR, h, hup, wittExtensionByZero_symplectic_form_eq]`. Use function extensionality and compare the values at `w`.

Rewrite using `[hT₂, e1]`. Simplify using `only [heisO, hT₂]`. Rewrite using `[J.d.wittDecomp_sympl_extAnisotropic_extAnisotropic, map_add]`. Rewrite using `[hT₂, show R Ψ = Φ from Subtype.ext (funext fun x => by rw [hR, h, fromCols_toCols₁])]`.
-/
theorem localModel_rankZeroWitt_source_isModel : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : GlobalTheory.LocMod.Place D k) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (J : JacLev D 0) (s hh : k) (n Z : Type) [Fintype n] [DecidableEq n] [Fintype Z] [DecidableEq Z] (F₀ : GlobalTheory.LocMod.Frame k J.W₀.rank n) (F : GlobalTheory.LocMod.Frame k J.W.rank (n ⊕ Fin 0)), p.IsJacFrame J s hh F₀ F → ∀ (T : HSp D) (FT : GlobalTheory.LocMod.Frame k T.rank Z) (Tm : SB (Matrix Z (n ⊕ Fin 0) k) →ₗ[ℂ] (WO J.W T → ℂ)), p.IsModel ψ F FT Tm → ∃ T₂ : SB (Matrix Z n k) →ₗ[ℂ] (WO J.W₀ T → ℂ), p.IsModel ψ F₀ FT T₂ ∧ ∀ (Ψ : SB (Matrix Z n k)) (Φ : SB (Matrix Z (n ⊕ Fin 0) k)), (∀ x, Ψ.1 x = Φ.1 (fromCols x 0)) → ∀ w, T₂ Ψ w = Tm Φ (J.d.ext0 T w) := by
  intro D k _ _ _ _ p ψ hψ J s hh n Z _ _ _ _ F₀ F hF T FT Tm hM
  have hT := GlobalTheory.T.weil_datum_transport_source_rational_isometry D ψ J.W J.W₀ T J.d hψ
  haveI := GlobalTheory.FinPl.Comm.t2Space_matrix_of_isNonarchimedeanLocalField (k := k) (n := Z) (n' := n ⊕ Fin 0)
  have hc1 : Continuous fun x : Matrix Z (n ⊕ Fin 0) k => x.toCols₁ :=
    continuous_pi fun i => continuous_pi fun j => by
      show Continuous fun a : Matrix Z (n ⊕ Fin 0) k => a i (Sum.inl j)
      exact (continuous_apply (Sum.inl j)).comp (continuous_apply i)
  have hc2 : Continuous fun x : Matrix Z n k => (fromCols x 0 : Matrix Z (n ⊕ Fin 0) k) :=
    continuous_pi fun i => continuous_pi fun j => by
      rcases j with j | j
      · show Continuous fun a : Matrix Z n k => a i j
        exact (continuous_apply j).comp (continuous_apply i)
      · exact j.elim0
  let R : SB (Matrix Z n k) → SB (Matrix Z (n ⊕ Fin 0) k) := fun Ψ =>
    ⟨fun x => Ψ.1 x.toCols₁, GlobalTheory.FinPl.Comm.comp_mem_SB Ψ.2 hc1 hc2 fromCols_toCols₁⟩
  have hR : ∀ Ψ x, (R Ψ).1 x = Ψ.1 x.toCols₁ := fun _ _ => rfl
  let T₂ : SB (Matrix Z n k) →ₗ[ℂ] (WO J.W₀ T → ℂ) :=
    { toFun := fun Ψ w => Tm (R Ψ) (J.d.ext0 T w)
      map_add' := fun Ψ Ψ' => by
        funext w
        rw [show R (Ψ + Ψ') = R Ψ + R Ψ' from Subtype.ext rfl, map_add]
        rfl
      map_smul' := fun c Ψ => by
        funext w
        rw [show R (c • Ψ) = c • R Ψ from Subtype.ext rfl, map_smul]
        rfl }
  have hT₂ : ∀ Ψ w, T₂ Ψ w = Tm (R Ψ) (J.d.ext0 T w) := fun _ _ => rfl
  have hup : ∀ x, p.up F FT x = J.d.ext0 T (p.up F₀ FT x.toCols₁) := fun x => by
    rw [splitLocalPlace_up_wittExtendByZero_rankZero p J s hh F₀ F hF T FT, fromCols_toCols₁]
  refine ⟨T₂, ⟨fun Ψ => ?_, fun x Ψ Ψ' h => ?_, fun y hy Ψ Ψ' h => ?_⟩, fun Ψ Φ h w => ?_⟩
  · exact (hT.2.2.1 (Tm (R Ψ))).2 (hM.theta _)
  · have e1 : Tm (R Ψ') = heisO ψ J.W T (p.up F FT (fromCols x 0)) (Tm (R Ψ)) := hM.trans _ _ _ fun t => by
      rw [hR, hR, h]
      congr 1
    funext w
    rw [hT₂, e1, ← splitLocalPlace_up_wittExtendByZero_rankZero p J s hh F₀ F hF T FT]
    simp only [heisO, hT₂]
    rw [J.d.wittDecomp_sympl_extAnisotropic_extAnisotropic, map_add]
  · have e1 : Tm (R Ψ') = heisO ψ J.W T (J.d.ext0 T y) (Tm (R Ψ)) := hM.modul _ (wittExtensionByZero_preserves_isHalf J.d T hy) _ _ fun t => by
      rw [hR, hR, h, hup, wittExtensionByZero_symplectic_form_eq]
    funext w
    rw [hT₂, e1]
    simp only [heisO, hT₂]
    rw [J.d.wittDecomp_sympl_extAnisotropic_extAnisotropic, map_add]
  · rw [hT₂, show R Ψ = Φ from Subtype.ext (funext fun x => by rw [hR, h, fromCols_toCols₁])]

end GlobalTheory.LocMod.RankZeroSrc
end
