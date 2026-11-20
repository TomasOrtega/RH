import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistSmulHomApp

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE GlobalTheory.CompanionTheory.GE.Step

namespace GlobalTheory.CompanionTheory.GE.Step

/- English proof (translation)
Express the relevant statement in the definitionally equal form `(X.presheaf.map (homOfLE le_top : (⊤ : X.Opens) ⟶ ⊤).op).hom r = r`. Rewrite using `[show (homOfLE le_top : (⊤ : X.Opens) ⟶ ⊤) = 𝟙 _ from rfl, op_id, X.presheaf.map_id]`. Both sides reduce to the same expression.
-/
lemma restrictTop_top_self {X : Scheme.{0}} (r : Γ(X, ⊤)) : restrictTop (⊤ : X.Opens) r = r := by
  change (X.presheaf.map (homOfLE le_top : (⊤ : X.Opens) ⟶ ⊤).op).hom r = r
  rw [show (homOfLE le_top : (⊤ : X.Opens) ⟶ ⊤) = 𝟙 _ from rfl, op_id, X.presheaf.map_id]
  rfl

/- English proof (translation)
Rewrite using `[GlobalTheory.Twist.map_comp]`. Both sides reduce to the same expression.
-/
lemma twist_map_comp_app {X : Scheme.{0}} (L : ReciprocityTheory.ChartRestriction.G.Semi.LB X) {F G K : X.Modules}
    (φ : F ⟶ G) (ψ : G ⟶ K) (V : X.Opens) (s : Γ(GlobalTheory.twist F L, V)) :
    (GlobalTheory.Twist.map L (φ ≫ ψ)).app V s = (GlobalTheory.Twist.map L ψ).app V ((GlobalTheory.Twist.map L φ).app V s) := by
  rw [GlobalTheory.Twist.map_comp]
  rfl

/- English proof (translation)
Establish `hm' : m ∈ (Ideal.map (toFunctions (X` using `X) (A := A) ⊤) (I ^ e) • ⊤ : Submodule Γ(X, ⊤) Γ(GlobalTheory.twistZ P H n, ⊤)) := hm`. Express the relevant statement in the definitionally equal form `_ ∈ (Ideal.map (toFunctions (X := X) (A := A) ⊤) (I ^ (e + 1)) • ⊤ : Submodule Γ(X, ⊤) Γ(GlobalTheory.twistZ P H n, ⊤))`. Establish `hmem : toFunctions (X` using `X) (A := A) ⊤ a ∈ Ideal.map (toFunctions (X := X) (A := A) ⊤) I := Ideal.mem_map_of_mem _ ha`. Rewrite using `[pow_succ', Ideal.map_mul, mul_smul]`. Conclude with `Submodule.smul_mem_smul hmem hm'`.
-/
lemma smul_mem_twPow {A : Type} [CommRing A] (I : Ideal A) {X : Scheme.{0}} [X.Over (Spec (.of A))]
    (H : ReciprocityTheory.ChartRestriction.G.Semi.LB X) (n : ℤ) (P : X.Modules) (e : ℕ) {a : A} (ha : a ∈ I)
    {m : Γ(GlobalTheory.twistZ P H n, ⊤)} (hm : m ∈ twPow I H n P e) :
    toFunctions (X := X) (A := A) ⊤ a • m ∈ twPow I H n P (e + 1) := by
  have hm' : m ∈ (Ideal.map (toFunctions (X := X) (A := A) ⊤) (I ^ e) •
      ⊤ : Submodule Γ(X, ⊤) Γ(GlobalTheory.twistZ P H n, ⊤)) := hm
  change _ ∈ (Ideal.map (toFunctions (X := X) (A := A) ⊤) (I ^ (e + 1)) •
      ⊤ : Submodule Γ(X, ⊤) Γ(GlobalTheory.twistZ P H n, ⊤))
  have hmem : toFunctions (X := X) (A := A) ⊤ a ∈ Ideal.map (toFunctions (X := X) (A := A) ⊤) I :=
    Ideal.mem_map_of_mem _ ha
  rw [pow_succ', Ideal.map_mul, mul_smul]
  exact Submodule.smul_mem_smul hmem hm'

/- English proof (translation)
Introduce `A _ _ I X _ H P S hS k g hg hr n e hspan hL y`. Establish `hy : y ∈ Submodule.span Γ(X, ⊤) (⋃ i, Set.range ((GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) (grT (anti hS) (hr i) e)).app ⊤))`. Rewrite using `[hspan]`. Discharge the goal by the elementary cases of `trivial`. Establish `hsub : ∀ m : ℕ, ∀ a b : Γ(GlobalTheory.twistZ P H n, ⊤), a ∈ twPow I H n P m → b ∈ twPow I H n P m → a + b ∈ twPow I H n P m` using `fun m a b ha hb => Submodule.add_mem (Ideal.map (toFunctions (X := X) (A := A) ⊤) (I ^ m) • ⊤ : Submodule Γ(X, ⊤) Γ(GlobalTheory.twistZ P H n, ⊤)) ha hb`.

Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨i, y', rfl⟩` from `Set.mem_iUnion.1 hy`. Take `⟨c', rfl, hc'⟩` from `hL y'`. Use `⟨(GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) (mulLvl (hr i) e)).app ⊤ c', ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[← twist_map_comp_app, ← twist_map_comp_app, grπ_grT]`. Rewrite using `[← twist_map_comp_app, mulLvl_arrow, twist_map_comp_app, twist_smulHom_app, restrictTop_top_self]`. Conclude with `smul_mem_twPow I H n P e (hg i) hc'`. Consider the case `zero`. Use `⟨0, map_zero _, ?_⟩` and prove the remaining obligations.

Rewrite using `[map_zero]`. Conclude with `Submodule.zero_mem (Ideal.map (toFunctions (X := X) (A := A) ⊤) (I ^ (e + 1)) • ⊤ : Submodule Γ(X, ⊤) Γ(GlobalTheory.twistZ P H n, ⊤))`. Consider the case `add x y _ _ hx hy`. Take `⟨c₁, rfl, h₁⟩` from `hx`. Take `⟨c₂, rfl, h₂⟩` from `hy`.

Use `⟨c₁ + c₂, map_add _ _ _, ?_⟩` and prove the remaining obligations. Rewrite using `[map_add]`. Conclude with `hsub _ _ _ h₁ h₂`. Consider the case `smul a x _ hx`. Take `⟨c, rfl, h⟩` from `hx`.

Use `⟨a • c, Scheme.Modules.Hom.app_smul _ _ _, ?_⟩` and prove the remaining obligations. Rewrite using `[Scheme.Modules.Hom.app_smul]`. Conclude with `Submodule.smul_mem (Ideal.map (toFunctions (X := X) (A := A) ⊤) (I ^ (e + 1)) • ⊤ : Submodule Γ(X, ⊤) Γ(GlobalTheory.twistZ P H n, ⊤)) a h`.
-/
theorem lifts_succ : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{0}} [X.Over (Spec (.of A))] (H : ReciprocityTheory.ChartRestriction.G.Semi.LB X) {P : X.Modules} (S : ℕ → Subobject P) (hS : ClosedSys I P S) {k : ℕ} (g : Fin k → A), (∀ i, g i ∈ I) → ∀ (hr : ∀ i, MapsDown S (toFunctions (X := X) (A := A) ⊤ (g i))) (n : ℤ) (e : ℕ), Submodule.span Γ(X, ⊤) (⋃ i, Set.range ((GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) (grT (anti hS) (hr i) e)).app ⊤)) = ⊤ → Lifts I H hS n e → Lifts I H hS n (e + 1) := by
  intro A _ _ I X _ H P S hS k g hg hr n e hspan hL y
  have hy : y ∈ Submodule.span Γ(X, ⊤) (⋃ i, Set.range
      ((GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) (grT (anti hS) (hr i) e)).app ⊤)) := by
    rw [hspan]; trivial
  have hsub : ∀ m : ℕ, ∀ a b : Γ(GlobalTheory.twistZ P H n, ⊤), a ∈ twPow I H n P m → b ∈ twPow I H n P m →
      a + b ∈ twPow I H n P m := fun m a b ha hb =>
    Submodule.add_mem (Ideal.map (toFunctions (X := X) (A := A) ⊤) (I ^ m) •
      ⊤ : Submodule Γ(X, ⊤) Γ(GlobalTheory.twistZ P H n, ⊤)) ha hb
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨i, y', rfl⟩ := Set.mem_iUnion.1 hy
    obtain ⟨c', rfl, hc'⟩ := hL y'
    refine ⟨(GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) (mulLvl (hr i) e)).app ⊤ c', ?_, ?_⟩
    · rw [← twist_map_comp_app, ← twist_map_comp_app, grπ_grT]
    · rw [← twist_map_comp_app, mulLvl_arrow, twist_map_comp_app, twist_smulHom_app,
        restrictTop_top_self]
      exact smul_mem_twPow I H n P e (hg i) hc'
  | zero =>
    refine ⟨0, map_zero _, ?_⟩
    rw [map_zero]
    exact Submodule.zero_mem (Ideal.map (toFunctions (X := X) (A := A) ⊤) (I ^ (e + 1)) •
      ⊤ : Submodule Γ(X, ⊤) Γ(GlobalTheory.twistZ P H n, ⊤))
  | add x y _ _ hx hy =>
    obtain ⟨c₁, rfl, h₁⟩ := hx
    obtain ⟨c₂, rfl, h₂⟩ := hy
    refine ⟨c₁ + c₂, map_add _ _ _, ?_⟩
    rw [map_add]
    exact hsub _ _ _ h₁ h₂
  | smul a x _ hx =>
    obtain ⟨c, rfl, h⟩ := hx
    refine ⟨a • c, Scheme.Modules.Hom.app_smul _ _ _, ?_⟩
    rw [Scheme.Modules.Hom.app_smul]
    exact Submodule.smul_mem (Ideal.map (toFunctions (X := X) (A := A) ⊤) (I ^ (e + 1)) •
      ⊤ : Submodule Γ(X, ⊤) Γ(GlobalTheory.twistZ P H n, ⊤)) a h

end GlobalTheory.CompanionTheory.GE.Step
