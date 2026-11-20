import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsFiniteProjectiveComplexQuasiIso
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC

variable {R : Type} [CommRing R]

def biprodPresheaf (P₁ P₂ : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)) : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R) where
  obj U := ModuleCat.of _ (P₁.obj U × P₂.obj U)
  map f := ModuleCat.ofHom ((P₁.map f).hom.prodMap (P₂.map f).hom)
  map_id U := by ext x <;> simp
  map_comp f g := by ext x <;> simp

/- English proof (translation)
Use `conv_lhs => rw [show y = (((𝟙 (M ⊞ N)) : M ⊞ N ⟶ M ⊞ N).hom.app (op U)).hom y from rfl, ← biprod.total]`. Both sides reduce to the same expression.
-/
theorem secBiprod_total (M N : Shv R) (U : Scheme.{0}) (y : Sec (M ⊞ N) U) :
    y = Sec.map (biprod.inl : M ⟶ M ⊞ N) (Sec.map biprod.fst y) + Sec.map (biprod.inr : N ⟶ M ⊞ N) (Sec.map biprod.snd y) := by
  conv_lhs => rw [show y = (((𝟙 (M ⊞ N)) : M ⊞ N ⟶ M ⊞ N).hom.app (op U)).hom y from rfl, ← biprod.total]
  rfl

/- English proof (translation)
Express the relevant statement in the definitionally equal form `((biprod.inl ≫ biprod.fst : M ⟶ M).hom.app (op U)).hom a = a`. Rewrite using `[biprod.inl_fst]`. Both sides reduce to the same expression.
-/
theorem secBiprod_inl_fst (M N : Shv R) {U : Scheme.{0}} (a : Sec M U) :
    Sec.map (biprod.fst : M ⊞ N ⟶ M) (Sec.map (biprod.inl : M ⟶ M ⊞ N) a) = a := by
  change ((biprod.inl ≫ biprod.fst : M ⟶ M).hom.app (op U)).hom a = a
  rw [biprod.inl_fst]; rfl

/- English proof (translation)
Express the relevant statement in the definitionally equal form `((biprod.inr ≫ biprod.fst : N ⟶ M).hom.app (op U)).hom b = 0`. Rewrite using `[biprod.inr_fst]`. Both sides reduce to the same expression.
-/
theorem secBiprod_inr_fst (M N : Shv R) {U : Scheme.{0}} (b : Sec N U) :
    Sec.map (biprod.fst : M ⊞ N ⟶ M) (Sec.map (biprod.inr : N ⟶ M ⊞ N) b) = 0 := by
  change ((biprod.inr ≫ biprod.fst : N ⟶ M).hom.app (op U)).hom b = 0
  rw [biprod.inr_fst]; rfl

/- English proof (translation)
Express the relevant statement in the definitionally equal form `((biprod.inl ≫ biprod.snd : M ⟶ N).hom.app (op U)).hom a = 0`. Rewrite using `[biprod.inl_snd]`. Both sides reduce to the same expression.
-/
theorem secBiprod_inl_snd (M N : Shv R) {U : Scheme.{0}} (a : Sec M U) :
    Sec.map (biprod.snd : M ⊞ N ⟶ N) (Sec.map (biprod.inl : M ⟶ M ⊞ N) a) = 0 := by
  change ((biprod.inl ≫ biprod.snd : M ⟶ N).hom.app (op U)).hom a = 0
  rw [biprod.inl_snd]; rfl

/- English proof (translation)
Express the relevant statement in the definitionally equal form `((biprod.inr ≫ biprod.snd : N ⟶ N).hom.app (op U)).hom b = b`. Rewrite using `[biprod.inr_snd]`. Both sides reduce to the same expression.
-/
theorem secBiprod_inr_snd (M N : Shv R) {U : Scheme.{0}} (b : Sec N U) :
    Sec.map (biprod.snd : M ⊞ N ⟶ N) (Sec.map (biprod.inr : N ⟶ M ⊞ N) b) = b := by
  change ((biprod.inr ≫ biprod.snd : N ⟶ N).hom.app (op U)).hom b = b
  rw [biprod.inr_snd]; rfl

noncomputable section

def biprodPresheafMap {M N : Shv R} {P₁ P₂ : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)} (φ₁ : P₁ ⟶ M.obj) (φ₂ : P₂ ⟶ N.obj) :
    biprodPresheaf P₁ P₂ ⟶ (M ⊞ N).obj where
  app U := ModuleCat.ofHom (LinearMap.coprod (((biprod.inl : M ⟶ M ⊞ N).hom.app U).hom ∘ₗ (φ₁.app U).hom)
    (((biprod.inr : N ⟶ M ⊞ N).hom.app U).hom ∘ₗ (φ₂.app U).hom))
  naturality U V f := by
    ext ⟨a, b⟩
    have h1 := congrArg (fun g => ModuleCat.Hom.hom g a) (φ₁.naturality f)
    have h2 := congrArg (fun g => ModuleCat.Hom.hom g b) (φ₂.naturality f)
    have h3 := congrArg (fun g => ModuleCat.Hom.hom g ((φ₁.app U).hom a)) ((biprod.inl : M ⟶ M ⊞ N).hom.naturality f)
    have h4 := congrArg (fun g => ModuleCat.Hom.hom g ((φ₂.app U).hom b)) ((biprod.inr : N ⟶ M ⊞ N).hom.naturality f)
    simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply] at h1 h2 h3 h4
    change (((biprod.inl : M ⟶ M ⊞ N).hom).app V).hom ((φ₁.app V).hom ((P₁.map f).hom a)) +
        (((biprod.inr : N ⟶ M ⊞ N).hom).app V).hom ((φ₂.app V).hom ((P₂.map f).hom b)) =
      ((M ⊞ N).obj.map f).hom ((((biprod.inl : M ⟶ M ⊞ N).hom).app U).hom ((φ₁.app U).hom a) +
        (((biprod.inr : N ⟶ M ⊞ N).hom).app U).hom ((φ₂.app U).hom b))
    rw [map_add, h1, h2, h3, h4]

/- English proof (translation)
Establish `h` using `congrArg (fun h => ModuleCat.Hom.hom h a) (φ.hom.naturality g.op)`. Simplify using `only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply] at h`. Conclude with `h.symm`.
-/
theorem secRes_secMap {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (a : Sec F U) :
    Sec.res g (Sec.map φ a) = Sec.map φ (Sec.res g a) := by
  have h := congrArg (fun h => ModuleCat.Hom.hom h a) (φ.hom.naturality g.op)
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply] at h
  exact h.symm

/- English proof (translation)
Introduce `R _ M N ⟨P₁, φ₁, s₁, i₁, f₁⟩ ⟨P₂, φ₂, s₂, i₂, f₂⟩`. Use `⟨biprodPresheaf P₁ P₂, biprodPresheafMap φ₁ φ₂, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `U y`. Take `⟨S, hS, hS'⟩` from `s₁ U (Sec.map biprod.fst y)`. Take `⟨T, hT, hT'⟩` from `s₂ U (Sec.map biprod.snd y)`.

Use `⟨S ⊓ T, Scheme.etaleTopology.intersection_covering hS hT, fun V g hg => ?_⟩` and prove the remaining obligations. Take `⟨x₁, hx₁⟩` from `hS' V g hg.1`. Take `⟨x₂, hx₂⟩` from `hT' V g hg.2`. Use `⟨(x₁, x₂), ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Sec.map (biprod.inl : M ⟶ M ⊞ N) ((φ₁.app (op V)).hom x₁) + Sec.map (biprod.inr : N ⟶ M ⊞ N) ((φ₂.app (op V)).hom x₂) = Sec.res g y`.

Rewrite using `[hx₁, hx₂, ← secRes_secMap, ← secRes_secMap, ← map_add]`. Conclude with `congrArg (Sec.res g) (secBiprod_total M N U y).symm`. Introduce and unpack `U ⟨a, b⟩ hx`. Express the relevant statement in the definitionally equal form `Sec.map (biprod.inl : M ⟶ M ⊞ N) ((φ₁.app (op U)).hom a) + Sec.map (biprod.inr : N ⟶ M ⊞ N) ((φ₂.app (op U)).hom b) = 0 at hx`. Establish `ha : (φ₁.app (op U)).hom a = 0`.

Establish `e : ∀ x y : Sec (M ⊞ N) U, Sec.map (biprod.fst : M ⊞ N ⟶ M) (x + y) = Sec.map biprod.fst x + Sec.map biprod.fst y` using `fun x y => map_add _ x y`. Establish `z : Sec.map (biprod.fst : M ⊞ N ⟶ M) (0 : Sec (M ⊞ N) U) = 0` using `map_zero _`. Establish `h` using `congrArg (Sec.map (biprod.fst : M ⊞ N ⟶ M)) hx`. Rewrite `h` using `[e, secBiprod_inl_fst, secBiprod_inr_fst, add_zero, z]`. Then use the resulting hypothesis. Establish `hb : (φ₂.app (op U)).hom b = 0`.

Establish `e : ∀ x y : Sec (M ⊞ N) U, Sec.map (biprod.snd : M ⊞ N ⟶ N) (x + y) = Sec.map biprod.snd x + Sec.map biprod.snd y` using `fun x y => map_add _ x y`. Establish `z : Sec.map (biprod.snd : M ⊞ N ⟶ N) (0 : Sec (M ⊞ N) U) = 0` using `map_zero _`. Establish `h` using `congrArg (Sec.map (biprod.snd : M ⊞ N ⟶ N)) hx`. Rewrite `h` using `[e, secBiprod_inl_snd, secBiprod_inr_snd, zero_add, z]`. Then use the resulting hypothesis. Take `⟨S, hS, hS'⟩` from `i₁ U a ha`.

Take `⟨T, hT, hT'⟩` from `i₂ U b hb`. Use `⟨S ⊓ T, Scheme.etaleTopology.intersection_covering hS hT, fun V g hg => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `((P₁.map g.op).hom a, (P₂.map g.op).hom b) = 0`. Rewrite using `[hS' V g hg.1, hT' V g hg.2]`. Both sides reduce to the same expression.

Introduce `U hU haveI := f₁ U hU haveI := f₂ U hU`. Conclude with `GlobalTheory.flat_prod (R := ULift.{1} R) (A := P₁.obj (op U)) (B := P₂.obj (op U))`.
-/
theorem flatS_biprod : ∀ (R : Type) [CommRing R] (M N : Shv R), FlatS M → FlatS N → FlatS (M ⊞ N) := by
  intro R _ M N ⟨P₁, φ₁, s₁, i₁, f₁⟩ ⟨P₂, φ₂, s₂, i₂, f₂⟩
  refine ⟨biprodPresheaf P₁ P₂, biprodPresheafMap φ₁ φ₂, ?_, ?_, ?_⟩
  · intro U y
    obtain ⟨S, hS, hS'⟩ := s₁ U (Sec.map biprod.fst y)
    obtain ⟨T, hT, hT'⟩ := s₂ U (Sec.map biprod.snd y)
    refine ⟨S ⊓ T, Scheme.etaleTopology.intersection_covering hS hT, fun V g hg => ?_⟩
    obtain ⟨x₁, hx₁⟩ := hS' V g hg.1
    obtain ⟨x₂, hx₂⟩ := hT' V g hg.2
    refine ⟨(x₁, x₂), ?_⟩
    change Sec.map (biprod.inl : M ⟶ M ⊞ N) ((φ₁.app (op V)).hom x₁) +
      Sec.map (biprod.inr : N ⟶ M ⊞ N) ((φ₂.app (op V)).hom x₂) = Sec.res g y
    rw [hx₁, hx₂, ← secRes_secMap, ← secRes_secMap, ← map_add]
    exact congrArg (Sec.res g) (secBiprod_total M N U y).symm
  · rintro U ⟨a, b⟩ hx
    change Sec.map (biprod.inl : M ⟶ M ⊞ N) ((φ₁.app (op U)).hom a) +
      Sec.map (biprod.inr : N ⟶ M ⊞ N) ((φ₂.app (op U)).hom b) = 0 at hx
    have ha : (φ₁.app (op U)).hom a = 0 := by
      have e : ∀ x y : Sec (M ⊞ N) U, Sec.map (biprod.fst : M ⊞ N ⟶ M) (x + y) =
          Sec.map biprod.fst x + Sec.map biprod.fst y := fun x y => map_add _ x y
      have z : Sec.map (biprod.fst : M ⊞ N ⟶ M) (0 : Sec (M ⊞ N) U) = 0 := map_zero _
      have h := congrArg (Sec.map (biprod.fst : M ⊞ N ⟶ M)) hx
      rwa [e, secBiprod_inl_fst, secBiprod_inr_fst, add_zero, z] at h
    have hb : (φ₂.app (op U)).hom b = 0 := by
      have e : ∀ x y : Sec (M ⊞ N) U, Sec.map (biprod.snd : M ⊞ N ⟶ N) (x + y) =
          Sec.map biprod.snd x + Sec.map biprod.snd y := fun x y => map_add _ x y
      have z : Sec.map (biprod.snd : M ⊞ N ⟶ N) (0 : Sec (M ⊞ N) U) = 0 := map_zero _
      have h := congrArg (Sec.map (biprod.snd : M ⊞ N ⟶ N)) hx
      rwa [e, secBiprod_inl_snd, secBiprod_inr_snd, zero_add, z] at h
    obtain ⟨S, hS, hS'⟩ := i₁ U a ha
    obtain ⟨T, hT, hT'⟩ := i₂ U b hb
    refine ⟨S ⊓ T, Scheme.etaleTopology.intersection_covering hS hT, fun V g hg => ?_⟩
    change ((P₁.map g.op).hom a, (P₂.map g.op).hom b) = 0
    rw [hS' V g hg.1, hT' V g hg.2]
    rfl
  · intro U hU
    haveI := f₁ U hU
    haveI := f₂ U hU
    exact GlobalTheory.flat_prod (R := ULift.{1} R) (A := P₁.obj (op U)) (B := P₂.obj (op U))

end

end GlobalTheory.EtC
