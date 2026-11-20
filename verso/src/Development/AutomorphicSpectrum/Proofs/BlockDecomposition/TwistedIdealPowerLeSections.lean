import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformVanishing
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.FormalIdealMul
import GroundTheory.ArithmeticGeometry.SchemeCohomology.CechNaturality.Linear
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.GE

attribute [local instance] algebraOfOver

/- English proof (translation)
Express the relevant statement in the definitionally equal form `(X.presheaf.map (homOfLE le_top : (⊤ : X.Opens) ⟶ ⊤).op).hom _ = _`. Rewrite using `[show (homOfLE le_top : (⊤ : X.Opens) ⟶ ⊤) = 𝟙 _ from rfl, op_id, X.presheaf.map_id]`. Both sides reduce to the same expression.
-/
lemma toFunctions_top_eq {A : Type} [CommRing A] [IsNoetherianRing A] {X : Scheme.{0}}
    [X.Over (Spec (.of A))] (a : A) :
    toFunctions (X := X) (A := A) ⊤ a = algebraMap A Γ(X, ⊤) a := by
  change (X.presheaf.map (homOfLE le_top : (⊤ : X.Opens) ⟶ ⊤).op).hom _ = _
  rw [show (homOfLE le_top : (⊤ : X.Opens) ⟶ ⊤) = 𝟙 _ from rfl, op_id, X.presheaf.map_id]
  rfl

/- English proof (translation)
Apply `GlobalTheory.Twist.sec_ext` to reduce the goal to its premises. Introduce `i`. Rewrite using `[GlobalTheory.Twist.coord_map_app, GroundTheory.Arith.SchemeCoh.smulHom_app_apply, GlobalTheory.Twist.coord_smul]`.
-/
lemma twist_map_smulHom_app {X : Scheme.{0}} (L : ReciprocityTheory.ChartRestriction.G.Semi.LB X) (P : X.Modules)
    (r : Γ(X, ⊤)) (c : Γ(GlobalTheory.twist P L, ⊤)) :
    (GlobalTheory.Twist.map L (GroundTheory.Arith.SchemeCoh.smulHom P r)).app ⊤ c = r • c := by
  apply GlobalTheory.Twist.sec_ext
  intro i
  rw [GlobalTheory.Twist.coord_map_app, GroundTheory.Arith.SchemeCoh.smulHom_app_apply, GlobalTheory.Twist.coord_smul]

/- English proof (translation)
Set `g : P ⟶ (powSub I P m : X.Modules)` to `idealPowOfMem I P a ha ≫ (Subobject.underlyingIso (idealPowι I P m)).inv`. Establish `hg : g ≫ (powSub I P m).arrow = GroundTheory.Arith.SchemeCoh.smulHom P (algebraMap A Γ(X, ⊤) a)`. Simplify using `only [g, powSub, Category.assoc]`. Rewrite using `[← Subobject.underlyingIso_hom_comp_eq_mk, Iso.inv_hom_id_assoc, idealPowOfMem_ι]`. Use `⟨(GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) g).app ⊤ c, ?_⟩` and prove the remaining obligations.

Rewrite using `[← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, ← GlobalTheory.Twist.map_comp, hg, twist_map_smulHom_app, toFunctions_top_eq]`.
-/
lemma smul_mem_twSecs {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{0}}
    [X.Over (Spec (.of A))] (H : ReciprocityTheory.ChartRestriction.G.Semi.LB X) (n : ℤ) (P : X.Modules) (m : ℕ)
    {a : A} (ha : a ∈ I ^ m) (c : Γ(GlobalTheory.twistZ P H n, ⊤)) :
    toFunctions (X := X) (A := A) ⊤ a • c ∈ twSecs H n (powSub I P m) := by
  let g : P ⟶ (powSub I P m : X.Modules) :=
    idealPowOfMem I P a ha ≫ (Subobject.underlyingIso (idealPowι I P m)).inv
  have hg : g ≫ (powSub I P m).arrow = GroundTheory.Arith.SchemeCoh.smulHom P (algebraMap A Γ(X, ⊤) a) := by
    simp only [g, powSub, Category.assoc]
    rw [← Subobject.underlyingIso_hom_comp_eq_mk, Iso.inv_hom_id_assoc, idealPowOfMem_ι]
  refine ⟨(GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) g).app ⊤ c, ?_⟩
  rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, ← GlobalTheory.Twist.map_comp, hg,
    twist_map_smulHom_app, toFunctions_top_eq]

def twSecsSub {X : Scheme.{0}} (H : ReciprocityTheory.ChartRestriction.G.Semi.LB X) (n : ℤ) {P : X.Modules}
    (S : Subobject P) : Submodule Γ(X, ⊤) Γ(GlobalTheory.twistZ P H n, ⊤) where
  carrier := twSecs H n S
  add_mem' := by
    rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨x + y, map_add _ _ _⟩
  zero_mem' := ⟨0, map_zero _⟩
  smul_mem' := by
    rintro r _ ⟨x, rfl⟩
    exact ⟨r • x, Scheme.Modules.Hom.app_smul _ _ _⟩

/- English proof (translation)
Introduce `A _ _ I X _ H _ P _ n m`. Establish `key : (Ideal.map (toFunctions (X` using `X) (A := A) ⊤) (I ^ m) • ⊤ : Submodule Γ(X, ⊤) Γ(GlobalTheory.twistZ P H n, ⊤)) ≤ twSecsSub H n (powSub I P m) := by`. Rewrite using `[Submodule.smul_le]`. Introduce `r hr c _`. Proceed by induction on `hr using Submodule.span_induction with`.

Consider the case `mem x hx`. Take `⟨a, ha, rfl⟩` from `hx`. Conclude with `smul_mem_twSecs I H n P m ha c`. Consider the case `zero => rw [zero_smul]`. Conclude with `Submodule.zero_mem _`.

Consider the case `add x y _ _ hx hy => rw [add_smul]`. Conclude with `Submodule.add_mem _ hx hy`. Consider the case `smul x y _ hy => rw [smul_eq_mul, mul_smul]`. Conclude with `Submodule.smul_mem _ _ hy`. Conclude with `key`.
-/
theorem twPow_subset_twSecs : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {X : Scheme.{0}} [X.Over (Spec (.of A))] (H : ReciprocityTheory.ChartRestriction.G.Semi.LB X), GlobalTheory.IsAmpleLB H →
    ∀ {P : X.Modules}, IsCoherent P → ∀ (n : ℤ) (m : ℕ),
      twPow I H n P m ⊆ twSecs H n (powSub I P m) := by
  intro A _ _ I X _ H _ P _ n m
  have key : (Ideal.map (toFunctions (X := X) (A := A) ⊤) (I ^ m) • ⊤ :
      Submodule Γ(X, ⊤) Γ(GlobalTheory.twistZ P H n, ⊤)) ≤ twSecsSub H n (powSub I P m) := by
    rw [Submodule.smul_le]
    intro r hr c _
    induction hr using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, ha, rfl⟩ := hx
      exact smul_mem_twSecs I H n P m ha c
    | zero => rw [zero_smul]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [add_smul]; exact Submodule.add_mem _ hx hy
    | smul x y _ hy => rw [smul_eq_mul, mul_smul]; exact Submodule.smul_mem _ _ hy
  exact key

end GlobalTheory.CompanionTheory.GE
