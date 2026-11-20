import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWeilDatumOOneOfRankZero

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RawLift.Model

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {V W : HSp D} {χV χW : (AE D)ˣ →* Circle}
  {om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)}

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem cA_inc (e : D.host.E) : cA D (incA D e) = incA D (star e) := by
  rfl

/- English proof (translation)
Simplify using `only [hO, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply, Finset.mul_sum, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hO_eq_trace (x y : WO V W) :
    hO V W x y = Matrix.trace ((V.gram⁻¹).map (incA D) * ((y.map (cA D))ᵀ * W.gram.map (incA D) * x)) := by
  simp only [hO, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply,
    Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  ring

/- English proof (translation)
Establish `h : (C.map (incA D)).map (cA D) = (Cᴴ.map (incA D))ᵀ`. Use extensionality with `i j`. Simplify using `[Matrix.map_apply, cA_inc]`. Rewrite using `[hO_eq_trace]`. Unfold `ratMul`.

Rewrite using `[Matrix.map_mul, h, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.map_mul, Matrix.map_mul]`. Simplify using `only [Matrix.mul_assoc]`.
-/
theorem hO_ratMul (C : Matrix (Fin W.rank) (Fin W.rank) D.host.E) (u v : WO V W) :
    hO V W (ratMul C u) (ratMul C v) =
      Matrix.trace ((V.gram⁻¹).map (incA D) * ((v.map (cA D))ᵀ * (Cᴴ * W.gram * C).map (incA D) * u)) := by
  have h : (C.map (incA D)).map (cA D) = (Cᴴ.map (incA D))ᵀ := by
    ext i j; simp [Matrix.map_apply, cA_inc]
  rw [hO_eq_trace]
  unfold ratMul
  rw [Matrix.map_mul, h, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.map_mul, Matrix.map_mul]
  simp only [Matrix.mul_assoc]

/- English proof (translation)
Rewrite using `[Matrix.mul_assoc, Matrix.mul_assoc]`. Use function extensionality and compare the values at `j k`. Establish `m : ∀ j, ((fun a => C.1 a j), (fun a => C.2 a j)) ∈ Y.1` using `fun j => h ▸ Submodule.subset_span ⟨j, rfl⟩`. Use `Y.2.2 _ (m j) _ (m k)` as an intermediate fact. Simplify using `only [dotProduct, Matrix.mulVec, Pi.star_apply] at this`.

Simplify `this` using `only [Matrix.mul_apply, Matrix.conjTranspose_apply]`.
-/
theorem gram_eq {Y : Lag W} {C} (h : IsLagFrame W Y C) : C.1ᴴ * W.gram * C.1 = C.2ᴴ * W.gram * C.2 := by
  rw [Matrix.mul_assoc, Matrix.mul_assoc]
  funext j k
  have m : ∀ j, ((fun a => C.1 a j), (fun a => C.2 a j)) ∈ Y.1 := fun j => h ▸ Submodule.subset_span ⟨j, rfl⟩
  have := Y.2.2 _ (m j) _ (m k)
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply] at this
  simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply] using this

/- English proof (translation)
Unfold `ratMul ratW`. Rewrite using `[Matrix.mul_add, Matrix.map_mul]`.
-/
theorem ratMul_add (C : Matrix (Fin W.rank) (Fin W.rank) D.host.E) (γ) (u : WO V W) :
    ratMul C (ratW W V γ + u) = ratW W V (C * γ) + ratMul C u := by
  unfold ratMul ratW
  rw [Matrix.mul_add, Matrix.map_mul]

/- English proof (translation)
Establish `e : ∀ B : Matrix (Fin W.rank) (Fin W.rank) D.host.E, ratW W V (B * γ) = ratMul B (ratW W V γ)` using `fun B => by`. Unfold `ratMul ratW`. Rewrite using `[Matrix.map_mul]`. Establish `s : symplOH V W (ratW W V (C.1 * γ)) (ratMul C.1 u) = symplOH V W (ratW W V (C.2 * γ)) (ratMul C.2 u)`. Rewrite using `[e, e]`.

Unfold `symplOH symplO`. Rewrite using `[hO_ratMul, hO_ratMul, gram_eq h]`. Rewrite using `[ratMul_add, ratMul_add, h₁.quasi, h₂.quasi, s, star_mul']`. Use `set z := ψ (-(symplOH V W (ratW W V (C.2 * γ)) (ratMul C.2 u))) with hz`. Establish `: z * star z = 1`.

Use `Complex.mul_conj' z` as an intermediate fact. Rewrite `this` using `[hz, hψ]`. Simplify using `using this`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem integrand_periodic (hψ : ∀ x, ‖ψ x‖ = 1) {Y : Lag W} {C} (h : IsLagFrame W Y C) {f₁ f₂ : WO V W → ℂ}
    (h₁ : IsThetaFunO ψ V W f₁) (h₂ : IsThetaFunO ψ V W f₂) (γ) (u : WO V W) :
    f₁ (ratMul C.1 (ratW W V γ + u)) * star (f₂ (ratMul C.2 (ratW W V γ + u))) =
      f₁ (ratMul C.1 u) * star (f₂ (ratMul C.2 u)) := by
  have e : ∀ B : Matrix (Fin W.rank) (Fin W.rank) D.host.E, ratW W V (B * γ) = ratMul B (ratW W V γ) := fun B => by
    unfold ratMul ratW; rw [Matrix.map_mul]
  have s : symplOH V W (ratW W V (C.1 * γ)) (ratMul C.1 u) = symplOH V W (ratW W V (C.2 * γ)) (ratMul C.2 u) := by
    rw [e, e]; unfold symplOH symplO; rw [hO_ratMul, hO_ratMul, gram_eq h]
  rw [ratMul_add, ratMul_add, h₁.quasi, h₂.quasi, s, star_mul']
  set z := ψ (-(symplOH V W (ratW W V (C.2 * γ)) (ratMul C.2 u))) with hz
  have : z * star z = 1 := by
    have := Complex.mul_conj' z
    rw [hz, hψ] at this
    simpa using this
  calc _ = (z * star z) * (f₁ (ratMul C.1 u) * star (f₂ (ratMul C.2 u))) := by ring
    _ = _ := by rw [this, one_mul]

/- English proof (translation)
Use `haveI : IsEmpty (Fin W.rank) := by rw [h]; infer_instance`. Use `haveI : Subsingleton (WO V W) := ⟨fun a b => by funext i; exact isEmptyElim i⟩`. Use `haveI : Subsingleton (Lag W) := ⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩`. Use `haveI : Unique (Lag W) := uniqueOfSubsingleton default`. Establish `hμ : μ 𝓕 = 1` using `hs.covol.2.2`.

Establish `hc : ∀ g : WO V W → ℂ, g = fun _ => g 0` using `fun g => funext fun w => by rw [Subsingleton.elim w 0]`. Establish `z : ∀ x y : WO V W, symplOH V W x y = 0` using `fun x y => by simp [symplOH, symplO, hO]`. Establish `one : IsThetaFunO ψ V W (fun _ => 1)` using `⟨fun γ w => by simp [z], ⟨⊤, isOpen_univ, fun u _ _ => by funext w; simp [heisO, z]⟩, continuous_const, fun _ _ _ _ _ => contDiff_const⟩`. Establish `key : ∀ p, ∀ f : WO V W → ℂ, om p f 0 = f 0 * om p (fun _ => 1) 0` using `fun p f => by`. Establish `: f = f 0 • (fun _ => (1 : ℂ))` using `by funext w; simp [Subsingleton.elim w 0]`.

Use `conv_lhs => rw [this, map_smul]`. Simplify using the standard rewrite rules. Establish `nm : ∀ p, om p (fun _ => 1) 0 * star (om p (fun _ => 1) 0) = 1` using `fun p => by`. Establish `u` using `hs.weil.om_unit μ 𝓕 hs.covol.1 hs.covol.2.1 p _ one`. Rewrite `u` using `[hc (om p fun _ => 1)]`.

Simplify using `only [setLIntegral_const, hμ, mul_one, enorm_one, one_pow] at u`. Establish `u2 : ‖om p (fun _ => 1) 0‖ ^ 2 = 1`. Use `congrArg ENNReal.toReal u` as an intermediate fact. Rewrite `this` using `[ENNReal.toReal_pow, toReal_enorm, ENNReal.toReal_one]`. Then use the resulting hypothesis. Use `Complex.mul_conj' (om p (fun _ => 1) 0)` as an intermediate fact.

Rewrite `this` using `[← Complex.ofReal_pow, u2]`. Simplify using `using this`. Establish `I : ∀ g, thetaKO om g 1 f₁ * star (thetaKO om g 1 f₂) = f₁ 0 * star (f₂ 0)` using `fun g => by`. Unfold `thetaKO`. Rewrite using `[key _ f₁, key _ f₂, star_mul']`.

Combine the equalities or inequalities in the displayed calculation. Establish `L : ∀ C, lagTerm μ 𝓕 C f₁ f₂ = f₁ 0 * star (f₂ 0)` using `fun C => by`. Establish `: μ.real 𝓕 = 1` using `by rw [Measure.real, hμ, ENNReal.toReal_one]`. Unfold `lagTerm`. Simplify using `only [Subsingleton.elim (ratMul _ _ : WO V W) 0]`.

Rewrite using `[setIntegral_const, this, one_smul]`. Simplify using `only [I, L, setIntegral_const]`. Use `hasSum_unique (fun _ : Lag W => ((νV 𝓗).toReal : ℂ) * (f₁ 0 * star (f₂ 0))) using 1` and compare the differences between its conclusion and the goal. Simplify using `[Measure.real]`.
-/
theorem swPair_rank_zero {νV 𝓗 νW 𝓖 μ 𝓕 fr} (hs : SWSetup ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr) (h : W.rank = 0)
    (f₁ f₂ : WO V W → ℂ) :
    HasSum (fun Y : Lag W => ((νV 𝓗).toReal : ℂ) * lagTerm μ 𝓕 (fr Y) f₁ f₂)
      (∫ h in 𝓗, thetaKO om h 1 f₁ * star (thetaKO om h 1 f₂) ∂νV) := by
  haveI : IsEmpty (Fin W.rank) := by rw [h]; infer_instance
  haveI : Subsingleton (WO V W) := ⟨fun a b => by funext i; exact isEmptyElim i⟩
  haveI : Subsingleton (Lag W) := ⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩
  haveI : Unique (Lag W) := uniqueOfSubsingleton default
  have hμ : μ 𝓕 = 1 := hs.covol.2.2
  have hc : ∀ g : WO V W → ℂ, g = fun _ => g 0 := fun g => funext fun w => by rw [Subsingleton.elim w 0]
  have z : ∀ x y : WO V W, symplOH V W x y = 0 := fun x y => by simp [symplOH, symplO, hO]
  have one : IsThetaFunO ψ V W (fun _ => 1) :=
    ⟨fun γ w => by simp [z], ⟨⊤, isOpen_univ, fun u _ _ => by funext w; simp [heisO, z]⟩, continuous_const,
      fun _ _ _ _ _ => contDiff_const⟩
  have key : ∀ p, ∀ f : WO V W → ℂ, om p f 0 = f 0 * om p (fun _ => 1) 0 := fun p f => by
    have : f = f 0 • (fun _ => (1 : ℂ)) := by funext w; simp [Subsingleton.elim w 0]
    conv_lhs => rw [this, map_smul]
    simp
  have nm : ∀ p, om p (fun _ => 1) 0 * star (om p (fun _ => 1) 0) = 1 := fun p => by
    have u := hs.weil.om_unit μ 𝓕 hs.covol.1 hs.covol.2.1 p _ one
    rw [hc (om p fun _ => 1)] at u
    simp only [setLIntegral_const, hμ, mul_one, enorm_one, one_pow] at u
    have u2 : ‖om p (fun _ => 1) 0‖ ^ 2 = 1 := by
      have := congrArg ENNReal.toReal u
      rwa [ENNReal.toReal_pow, toReal_enorm, ENNReal.toReal_one] at this
    have := Complex.mul_conj' (om p (fun _ => 1) 0)
    rw [← Complex.ofReal_pow, u2] at this
    simpa using this
  have I : ∀ g, thetaKO om g 1 f₁ * star (thetaKO om g 1 f₂) = f₁ 0 * star (f₂ 0) := fun g => by
    unfold thetaKO
    rw [key _ f₁, key _ f₂, star_mul']
    calc _ = (om (g, 1) (fun _ => 1) 0 * star (om (g, 1) (fun _ => 1) 0)) * (f₁ 0 * star (f₂ 0)) := by ring
      _ = _ := by rw [nm, one_mul]
  have L : ∀ C, lagTerm μ 𝓕 C f₁ f₂ = f₁ 0 * star (f₂ 0) := fun C => by
    have : μ.real 𝓕 = 1 := by rw [Measure.real, hμ, ENNReal.toReal_one]
    unfold lagTerm
    simp only [Subsingleton.elim (ratMul _ _ : WO V W) 0]
    rw [setIntegral_const, this, one_smul]
  simp only [I, L, setIntegral_const]
  convert hasSum_unique (fun _ : Lag W => ((νV 𝓗).toReal : ℂ) * (f₁ 0 * star (f₂ 0))) using 1
  simp [Measure.real]

end GlobalTheory.RawLift.Model

end
