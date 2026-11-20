import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformVanishing
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.LimitOfFinite

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE

namespace GlobalTheory.CompanionTheory.GE

attribute [local instance] algebraOfOver

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.LimitOfFinite.exists_limit_of_finite I hI f hf`.
-/
theorem exists_limit_of_finite {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    [Module.Finite A M] (I : Ideal A) (hI : IsPrecomplete I A) (f : ℕ → M)
    (hf : ∀ m, f m - f (m + 1) ∈ (I ^ m • ⊤ : Submodule A M)) :
    ∃ L, ∀ m, f m - L ∈ (I ^ m • ⊤ : Submodule A M) :=
  _root_.UpperTheory.Reformulated.B.LimitOfFinite.exists_limit_of_finite I hI f hf

/- English proof (translation)
Use `haveI : GlobalTheory.QCoh.IsFiniteQC P := ⟨hP.1, hP.2⟩`. Use `haveI : GlobalTheory.QCoh.IsFiniteQC (GlobalTheory.twistZ P H n) := GlobalTheory.Twist.isFiniteQC_twist (F := P) (GlobalTheory.Twist.isLB_lbZPow hH.isLB n)`. Establish `h0 : Module.Finite A (GlobalTheory.coh (GlobalTheory.twistZ P H n) 0)` using `GlobalTheory.IsAmpleLB.finite_coh (R := A) (f := X ↘ Spec (.of A)) (fun _ => rfl) _ hH 0`. Conclude with `Module.Finite.equiv ((GlobalTheory.cohOn.zeroEquiv A (GlobalTheory.twistZ P H n) ⊤).trans (GlobalTheory.sectionsOn.equivOfSMul A (GlobalTheory.twistZ P H n) ⊤ fun a x => by`. Rewrite using `[hs, GlobalTheory.restrictGlobal_top]))`.
-/
theorem finite_twisted_sections {A : Type} [CommRing A] [IsNoetherianRing A] {X : Scheme.{0}}
    [X.Over (Spec (.of A))] [IsProper (X ↘ Spec (.of A))] (H : ReciprocityTheory.ChartRestriction.G.Semi.LB X)
    (hH : GlobalTheory.IsAmpleLB H) {P : X.Modules} (hP : IsCoherent P) (n : ℤ)
    [Module A Γ(GlobalTheory.twistZ P H n, ⊤)]
    (hs : ∀ (a : A) (x : Γ(GlobalTheory.twistZ P H n, ⊤)), a • x = algebraMap A Γ(X, ⊤) a • x) :
    Module.Finite A Γ(GlobalTheory.twistZ P H n, ⊤) := by
  haveI : GlobalTheory.QCoh.IsFiniteQC P := ⟨hP.1, hP.2⟩
  haveI : GlobalTheory.QCoh.IsFiniteQC (GlobalTheory.twistZ P H n) :=
    GlobalTheory.Twist.isFiniteQC_twist (F := P) (GlobalTheory.Twist.isLB_lbZPow hH.isLB n)
  have h0 : Module.Finite A (GlobalTheory.coh (GlobalTheory.twistZ P H n) 0) :=
    GlobalTheory.IsAmpleLB.finite_coh (R := A) (f := X ↘ Spec (.of A)) (fun _ => rfl) _ hH 0
  exact Module.Finite.equiv ((GlobalTheory.cohOn.zeroEquiv A (GlobalTheory.twistZ P H n) ⊤).trans
    (GlobalTheory.sectionsOn.equivOfSMul A (GlobalTheory.twistZ P H n) ⊤ fun a x => by
      rw [hs, GlobalTheory.restrictGlobal_top]))

/- English proof (translation)
Introduce `A _ _ I hI X _ _ H hH P hP n f hf`. Use `letI : Module A Γ(GlobalTheory.twistZ P H n, ⊤) := Module.compHom _ (algebraMap A Γ(X, ⊤))`. Use `haveI : IsScalarTower A Γ(X, ⊤) Γ(GlobalTheory.twistZ P H n, ⊤) := ⟨fun a r x => by`. Express the relevant statement in the definitionally equal form `(a • r) • x = algebraMap A Γ(X, ⊤) a • (r • x)`. Rewrite using `[Algebra.smul_def, mul_smul]⟩`.

Use `haveI := finite_twisted_sections (A := A) H hH hP n (fun _ _ => rfl)`. Establish `hmem : ∀ (m : ℕ) (y : Γ(GlobalTheory.twistZ P H n, ⊤)), y ∈ twPow I H n P m ↔ y ∈ (I ^ m • ⊤ : Submodule A Γ(GlobalTheory.twistZ P H n, ⊤))`. Introduce `m y`. Establish `hfun : toFunctions (X` using `X) (A := A) ⊤ = algebraMap A Γ(X, ⊤) := by`. Use extensionality with `a`.

Simplify using `[toFunctions, restrictTop]`. Establish `h` using `Ideal.smul_restrictScalars (R := A) (S := Γ(X, ⊤)) (M := Γ(GlobalTheory.twistZ P H n, ⊤)) (I ^ m) ⊤`. Rewrite `h` using `[Submodule.restrictScalars_top]`. Rewrite using `[← h]`. Simplify using `only [twPow, hfun]`.

Both sides reduce to the same expression. Take `⟨L, hL⟩` from `exists_limit_of_finite I hI.toIsPrecomplete f fun m => (hmem m _).1 (hf m)`. Conclude with `⟨L, fun m => (hmem m _).2 (hL m)⟩`.
-/
theorem exists_limit_twPow : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A), IsAdicComplete I A → ∀ {X : Scheme.{0}} [X.Over (Spec (.of A))] [IsProper (X ↘ Spec (.of A))] (H : ReciprocityTheory.ChartRestriction.G.Semi.LB X), GlobalTheory.IsAmpleLB H → ∀ {P : X.Modules}, IsCoherent P → ∀ (n : ℤ) (f : ℕ → Γ(GlobalTheory.twistZ P H n, ⊤)), (∀ m, f m - f (m + 1) ∈ twPow I H n P m) → ∃ L : Γ(GlobalTheory.twistZ P H n, ⊤), ∀ m, f m - L ∈ twPow I H n P m := by
  intro A _ _ I hI X _ _ H hH P hP n f hf
  letI : Module A Γ(GlobalTheory.twistZ P H n, ⊤) := Module.compHom _ (algebraMap A Γ(X, ⊤))
  haveI : IsScalarTower A Γ(X, ⊤) Γ(GlobalTheory.twistZ P H n, ⊤) :=
    ⟨fun a r x => by
      change (a • r) • x = algebraMap A Γ(X, ⊤) a • (r • x)
      rw [Algebra.smul_def, mul_smul]⟩
  haveI := finite_twisted_sections (A := A) H hH hP n (fun _ _ => rfl)
  have hmem : ∀ (m : ℕ) (y : Γ(GlobalTheory.twistZ P H n, ⊤)),
      y ∈ twPow I H n P m ↔ y ∈ (I ^ m • ⊤ : Submodule A Γ(GlobalTheory.twistZ P H n, ⊤)) := by
    intro m y
    have hfun : toFunctions (X := X) (A := A) ⊤ = algebraMap A Γ(X, ⊤) := by
      ext a
      simp [toFunctions, restrictTop]
    have h := Ideal.smul_restrictScalars (R := A) (S := Γ(X, ⊤))
      (M := Γ(GlobalTheory.twistZ P H n, ⊤)) (I ^ m) ⊤
    rw [Submodule.restrictScalars_top] at h
    rw [← h]
    simp only [twPow, hfun]
    rfl
  obtain ⟨L, hL⟩ := exists_limit_of_finite I hI.toIsPrecomplete f fun m => (hmem m _).1 (hf m)
  exact ⟨L, fun m => (hmem m _).2 (hL m)⟩

end GlobalTheory.CompanionTheory.GE
