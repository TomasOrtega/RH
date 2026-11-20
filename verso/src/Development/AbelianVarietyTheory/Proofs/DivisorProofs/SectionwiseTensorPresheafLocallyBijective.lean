import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalPropertyCalculusRulesStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

open scoped TensorProduct

namespace GlobalTheory.EtC.TensLocBij

/- English proof (translation)
The claim follows from `GlobalTheory.T.etaleLocal_property_calculus_rules.1 U P h`.
-/
theorem locAll {U : Scheme.{0}} {P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : ∀ V g, P V g) :
    Loc U P := GlobalTheory.T.etaleLocal_property_calculus_rules.1 U P h

/- English proof (translation)
The claim follows from `GlobalTheory.T.etaleLocal_property_calculus_rules.2.1 U P Q h hPQ`.
-/
theorem locMono {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : Loc U P)
    (hPQ : ∀ V g, P V g → Q V g) : Loc U Q := GlobalTheory.T.etaleLocal_property_calculus_rules.2.1 U P Q h hPQ

/- English proof (translation)
The claim follows from `GlobalTheory.T.etaleLocal_property_calculus_rules.2.2.1 U P Q hP hQ`.
-/
theorem locAnd {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (hP : Loc U P)
    (hQ : Loc U Q) : Loc U fun V g => P V g ∧ Q V g := GlobalTheory.T.etaleLocal_property_calculus_rules.2.2.1 U P Q hP hQ

/- English proof (translation)
The claim follows from `GlobalTheory.T.etaleLocal_property_calculus_rules.2.2.2.2.1 U P h`.
-/
theorem locTrans {U : Scheme.{0}} {P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop}
    (h : Loc U fun V g => Loc V fun W k => P W (k ≫ g)) : Loc U P :=
  GlobalTheory.T.etaleLocal_property_calculus_rules.2.2.2.2.1 U P h

/- English proof (translation)
The claim follows from `GlobalTheory.T.etaleLocal_property_calculus_rules.2.2.2.2.2.1 U ι P h`.
-/
theorem locFin {U : Scheme.{0}} {ι : Type} [Finite ι] (P : ι → ∀ V : Scheme.{0}, (V ⟶ U) → Prop)
    (h : ∀ i, Loc U (P i)) : Loc U fun V g => ∀ i, P i V g :=
  GlobalTheory.T.etaleLocal_property_calculus_rules.2.2.2.2.2.1 U ι P h

section Alg

variable {S : Type*} [CommRing S] {A B D : Type*} [AddCommGroup A] [Module S A]
  [AddCommGroup B] [Module S B] [AddCommGroup D] [Module S D]

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => exact ⟨⊥, Submodule.fg_bot, 0, by simp⟩`. Consider the case `tmul a b => exact ⟨S ∙ b, Submodule.fg_span_singleton b, a ⊗ₜ[S] ⟨b, Submodule.mem_span_singleton_self _⟩, rfl⟩`. Consider the case `add x₁ x₂ ih₁ ih₂`. Take `⟨J₁, fg₁, y₁, rfl⟩` from `ih₁`.

Take `⟨J₂, fg₂, y₂, rfl⟩` from `ih₂`. Use `⟨J₁ ⊔ J₂, fg₁.sup fg₂, LinearMap.lTensor A (Submodule.inclusion le_sup_left) y₁ + LinearMap.lTensor A (Submodule.inclusion le_sup_right) y₂, ?_⟩` and prove the remaining obligations. Rewrite using `[map_add, ← LinearMap.lTensor_comp_apply, ← LinearMap.lTensor_comp_apply]`. Both sides reduce to the same expression.
-/
theorem exists_fg_lTensor (x : A ⊗[S] B) :
    ∃ (J : Submodule S B) (_ : J.FG) (y : A ⊗[S] J), x = LinearMap.lTensor A J.subtype y := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨⊥, Submodule.fg_bot, 0, by simp⟩
  | tmul a b => exact ⟨S ∙ b, Submodule.fg_span_singleton b,
      a ⊗ₜ[S] ⟨b, Submodule.mem_span_singleton_self _⟩, rfl⟩
  | add x₁ x₂ ih₁ ih₂ =>
    obtain ⟨J₁, fg₁, y₁, rfl⟩ := ih₁
    obtain ⟨J₂, fg₂, y₂, rfl⟩ := ih₂
    refine ⟨J₁ ⊔ J₂, fg₁.sup fg₂, LinearMap.lTensor A (Submodule.inclusion le_sup_left) y₁ +
      LinearMap.lTensor A (Submodule.inclusion le_sup_right) y₂, ?_⟩
    rw [map_add, ← LinearMap.lTensor_comp_apply, ← LinearMap.lTensor_comp_apply]
    rfl

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a b => simp`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`.
-/
theorem rTensor_comm_eq {Y : Type*} [AddCommGroup Y] [Module S Y] (g : B →ₗ[S] Y) (x : A ⊗[S] B) :
    LinearMap.rTensor A g (TensorProduct.comm S A B x) =
      TensorProduct.comm S A Y (LinearMap.lTensor A g x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp
  | add x y hx hy => simp only [map_add, hx, hy]

/- English proof (translation)
Establish `h' : LinearMap.rTensor A J.subtype (TensorProduct.comm S A J t) = 0`. Rewrite using `[rTensor_comm_eq, h, map_zero]`. Take `⟨K, hJK, hK, h0⟩` from `TensorProduct.eq_zero_of_fg_of_subtype_eq_zero hJ h'`. Use `⟨K, hJK, hK, ?_⟩` and prove the remaining obligations. Rewrite `h0` using `[rTensor_comm_eq]`.

Conclude with `(LinearEquiv.map_eq_zero_iff _).mp h0`.
-/
theorem fg_lTensor_eq_zero {J : Submodule S D} (hJ : J.FG) {t : A ⊗[S] J}
    (h : LinearMap.lTensor A J.subtype t = 0) :
    ∃ (K : Submodule S D) (hJK : J ≤ K), K.FG ∧
      LinearMap.lTensor A (Submodule.inclusion hJK) t = 0 := by
  have h' : LinearMap.rTensor A J.subtype (TensorProduct.comm S A J t) = 0 := by
    rw [rTensor_comm_eq, h, map_zero]
  obtain ⟨K, hJK, hK, h0⟩ := TensorProduct.eq_zero_of_fg_of_subtype_eq_zero hJ h'
  refine ⟨K, hJK, hK, ?_⟩
  rw [rTensor_comm_eq] at h0
  exact (LinearEquiv.map_eq_zero_iff _).mp h0

end Alg

end GlobalTheory.EtC.TensLocBij

namespace GlobalTheory.EtC.TensLocBij

variable {R : Type} [CommRing R] (C P Q : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)) (φ : P ⟶ Q)

/- English proof (translation)
Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => exact locAll fun V g => ⟨0, by simp⟩`. Consider the case `tmul c q`. Conclude with `locMono (hs U q) fun V g ⟨x, hx⟩ => ⟨(C.map g.op).hom c ⊗ₜ x, by simp [hx]⟩`. Consider the case `add a b ha hb`.

Conclude with `locMono (locAnd ha hb) fun V g ⟨⟨x, hx⟩, ⟨x', hx'⟩⟩ => ⟨x + x', by simp [map_add, hx, hx']⟩`.
-/
theorem surj
    (hs : ∀ (U : Scheme.{0}) (y : Q.obj (op U)), Loc U fun V g => ∃ x, (φ.app (op V)).hom x = (Q.map g.op).hom y)
    (U : Scheme.{0}) (y : TensorProduct (ULift.{1} R) (C.obj (op U)) (Q.obj (op U))) :
    Loc U fun V g => ∃ x, LinearMap.lTensor _ (φ.app (op V)).hom x =
      TensorProduct.map (C.map g.op).hom (Q.map g.op).hom y := by
  induction y using TensorProduct.induction_on with
  | zero => exact locAll fun V g => ⟨0, by simp⟩
  | tmul c q =>
    exact locMono (hs U q) fun V g ⟨x, hx⟩ => ⟨(C.map g.op).hom c ⊗ₜ x, by simp [hx]⟩
  | add a b ha hb =>
    exact locMono (locAnd ha hb) fun V g ⟨⟨x, hx⟩, ⟨x', hx'⟩⟩ => ⟨x + x', by simp [map_add, hx, hx']⟩

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => exact locAll fun _ _ => by simp`. Consider the case `tmul c k => exact locMono (hi V k.1 (hK k.1 k.2)) fun W h hk => by simp [hk]`. Consider the case `add a b ha hb => exact locMono (locAnd ha hb) fun W h ⟨h1, h2⟩ => by simp [map_add, h1, h2]`.
-/
theorem kerPart
    (hi : ∀ (U : Scheme.{0}) (x : P.obj (op U)), (φ.app (op U)).hom x = 0 → Loc U fun _ g => (P.map g.op).hom x = 0)
    (V : Scheme.{0}) (K : Submodule (ULift.{1} R) (P.obj (op V)))
    (hK : ∀ k ∈ K, (φ.app (op V)).hom k = 0) (z : C.obj (op V) ⊗[ULift.{1} R] K) :
    Loc V fun _ h => TensorProduct.map (C.map h.op).hom (P.map h.op).hom
      (LinearMap.lTensor _ K.subtype z) = 0 := by
  induction z using TensorProduct.induction_on with
  | zero => exact locAll fun _ _ => by simp
  | tmul c k => exact locMono (hi V k.1 (hK k.1 k.2)) fun W h hk => by simp [hk]
  | add a b ha hb => exact locMono (locAnd ha hb) fun W h ⟨h1, h2⟩ => by simp [map_add, h1, h2]

/- English proof (translation)
Rewrite using `[op_comp, Functor.map_comp, Functor.map_comp, ModuleCat.hom_comp, ModuleCat.hom_comp, TensorProduct.map_comp]`.
-/
theorem map_restr_comp {U V W : Scheme.{0}} (g : V ⟶ U) (k : W ⟶ V) :
    TensorProduct.map (C.map (k ≫ g).op).hom (P.map (k ≫ g).op).hom =
      TensorProduct.map (C.map k.op).hom (P.map k.op).hom ∘ₗ
        TensorProduct.map (C.map g.op).hom (P.map g.op).hom := by
  rw [op_comp, Functor.map_comp, Functor.map_comp, ModuleCat.hom_comp, ModuleCat.hom_comp,
    TensorProduct.map_comp]

/- English proof (translation)
Use `congrArg (fun h => ModuleCat.Hom.hom h p) (φ.naturality g.op)` as an intermediate fact. Simplify using `using this`.
-/
theorem nat_apply {U V : Scheme.{0}} (g : V ⟶ U) (p : P.obj (op U)) :
    (φ.app (op V)).hom ((P.map g.op).hom p) = (Q.map g.op).hom ((φ.app (op U)).hom p) := by
  have := congrArg (fun h => ModuleCat.Hom.hom h p) (φ.naturality g.op)
  simpa using this

end GlobalTheory.EtC.TensLocBij

namespace GlobalTheory.EtC.TensLocBij

variable {R : Type} [CommRing R] (C P Q : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)) (φ : P ⟶ Q)

/- English proof (translation)
Take `⟨B₀, hB₀, x₀, rfl⟩` from `exists_fg_lTensor x`. Establish `hcomp : (B₀.map (φ.app (op U)).hom).subtype ∘ₗ (φ.app (op U)).hom.submoduleMap B₀ = (φ.app (op U)).hom ∘ₗ B₀.subtype` using `rfl`. Establish `ht : LinearMap.lTensor _ (B₀.map (φ.app (op U)).hom).subtype (LinearMap.lTensor _ ((φ.app (op U)).hom.submoduleMap B₀) x₀) = 0`. Rewrite using `[← LinearMap.lTensor_comp_apply, hcomp, LinearMap.lTensor_comp_apply]`. Conclude with `hx`.

Take `⟨K, hJK, ⟨s, hs'⟩, hK0⟩` from `fg_lTensor_eq_zero (hB₀.map _) ht`. Establish `hloc` using `locFin (ι := Fin s.card) (fun i V g => ∃ p, (φ.app (op V)).hom p = (Q.map g.op).hom (s.equivFin.symm i).1) (fun i => hs U (s.equivFin.symm i).1)`. Apply `locTrans` to reduce the goal to its premises. Use `locMono hloc fun V g hV => ?_` and prove the remaining obligations. Establish `hle : K ≤ (LinearMap.range (φ.app (op V)).hom).comap (Q.map g.op).hom`.

Rewrite using `[← hs', Submodule.span_le]`. Introduce `q hq`. Take `⟨p, hp⟩` from `hV (s.equivFin ⟨q, hq⟩)`. Rewrite `hp` using `[Equiv.symm_apply_apply]`. Conclude with `⟨p, hp⟩`.

Set `ρ` to `((Q.map g.op).hom ∘ₗ K.subtype).codRestrict (LinearMap.range (φ.app (op V)).hom) (fun k => hle k.2)`. Establish `key : LinearMap.lTensor _ (φ.app (op V)).hom.rangeRestrict ∘ₗ TensorProduct.map (C.map g.op).hom (P.map g.op).hom ∘ₗ LinearMap.lTensor _ B₀.subtype = TensorProduct.map (C.map g.op).hom ρ ∘ₗ LinearMap.lTensor _ (Submodule.inclusion hJK) ∘ₗ LinearMap.lTensor _ ((φ.app (op U)).hom.s …`. Apply `TensorProduct.ext'` to reduce the goal to its premises. Introduce `a b`. Simplify using `only [LinearMap.comp_apply, LinearMap.lTensor_tmul, TensorProduct.map_tmul]`.

Use `congr 1`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `[ρ, nat_apply]`. Establish `hy : LinearMap.lTensor _ (φ.app (op V)).hom.rangeRestrict (TensorProduct.map (C.map g.op).hom (P.map g.op).hom (LinearMap.lTensor _ B₀.subtype x₀)) = 0`. Use `congrArg (fun L => L x₀) key` as an intermediate fact.

Simplify using `only [LinearMap.comp_apply] at this`. Rewrite using `[this, hK0, map_zero]`. Establish `hex` using `lTensor_exact (C.obj (op V)) (LinearMap.exact_subtype_ker_map (φ.app (op V)).hom.rangeRestrict) (LinearMap.surjective_rangeRestrict _)`. Take `⟨z, hz⟩` from `(hex _).mp hy`. Establish `hK : ∀ k ∈ LinearMap.ker (φ.app (op V)).hom.rangeRestrict, (φ.app (op V)).hom k = 0`.

Introduce `k hk`. Use `congrArg Subtype.val (LinearMap.mem_ker.mp hk)` as an intermediate fact. Simplify using `using this`. Use `locMono (kerPart C P Q φ hi V _ hK z) fun W k hk => ?_` and prove the remaining obligations. Rewrite using `[map_restr_comp, LinearMap.comp_apply, ← hz]`.

Conclude with `hk`.
-/
theorem inj
    (hs : ∀ (U : Scheme.{0}) (y : Q.obj (op U)), Loc U fun V g => ∃ x, (φ.app (op V)).hom x = (Q.map g.op).hom y)
    (hi : ∀ (U : Scheme.{0}) (x : P.obj (op U)), (φ.app (op U)).hom x = 0 → Loc U fun _ g => (P.map g.op).hom x = 0)
    (U : Scheme.{0}) (x : TensorProduct (ULift.{1} R) (C.obj (op U)) (P.obj (op U)))
    (hx : LinearMap.lTensor _ (φ.app (op U)).hom x = 0) :
    Loc U fun _ g => TensorProduct.map (C.map g.op).hom (P.map g.op).hom x = 0 := by
  obtain ⟨B₀, hB₀, x₀, rfl⟩ := exists_fg_lTensor x
  have hcomp : (B₀.map (φ.app (op U)).hom).subtype ∘ₗ (φ.app (op U)).hom.submoduleMap B₀ =
      (φ.app (op U)).hom ∘ₗ B₀.subtype := rfl
  have ht : LinearMap.lTensor _ (B₀.map (φ.app (op U)).hom).subtype
      (LinearMap.lTensor _ ((φ.app (op U)).hom.submoduleMap B₀) x₀) = 0 := by
    rw [← LinearMap.lTensor_comp_apply, hcomp, LinearMap.lTensor_comp_apply]
    exact hx
  obtain ⟨K, hJK, ⟨s, hs'⟩, hK0⟩ := fg_lTensor_eq_zero (hB₀.map _) ht
  have hloc := locFin (ι := Fin s.card)
    (fun i V g => ∃ p, (φ.app (op V)).hom p = (Q.map g.op).hom (s.equivFin.symm i).1)
    (fun i => hs U (s.equivFin.symm i).1)
  apply locTrans
  refine locMono hloc fun V g hV => ?_
  have hle : K ≤ (LinearMap.range (φ.app (op V)).hom).comap (Q.map g.op).hom := by
    rw [← hs', Submodule.span_le]
    intro q hq
    obtain ⟨p, hp⟩ := hV (s.equivFin ⟨q, hq⟩)
    rw [Equiv.symm_apply_apply] at hp
    exact ⟨p, hp⟩
  let ρ := ((Q.map g.op).hom ∘ₗ K.subtype).codRestrict (LinearMap.range (φ.app (op V)).hom)
    (fun k => hle k.2)
  have key : LinearMap.lTensor _ (φ.app (op V)).hom.rangeRestrict ∘ₗ
      TensorProduct.map (C.map g.op).hom (P.map g.op).hom ∘ₗ LinearMap.lTensor _ B₀.subtype =
      TensorProduct.map (C.map g.op).hom ρ ∘ₗ LinearMap.lTensor _ (Submodule.inclusion hJK) ∘ₗ
        LinearMap.lTensor _ ((φ.app (op U)).hom.submoduleMap B₀) := by
    apply TensorProduct.ext'
    intro a b
    simp only [LinearMap.comp_apply, LinearMap.lTensor_tmul, TensorProduct.map_tmul]
    congr 1
    apply Subtype.ext
    simp [ρ, nat_apply]
  have hy : LinearMap.lTensor _ (φ.app (op V)).hom.rangeRestrict
      (TensorProduct.map (C.map g.op).hom (P.map g.op).hom (LinearMap.lTensor _ B₀.subtype x₀)) = 0 := by
    have := congrArg (fun L => L x₀) key
    simp only [LinearMap.comp_apply] at this
    rw [this, hK0, map_zero]
  have hex := lTensor_exact (C.obj (op V))
    (LinearMap.exact_subtype_ker_map (φ.app (op V)).hom.rangeRestrict)
    (LinearMap.surjective_rangeRestrict _)
  obtain ⟨z, hz⟩ := (hex _).mp hy
  have hK : ∀ k ∈ LinearMap.ker (φ.app (op V)).hom.rangeRestrict, (φ.app (op V)).hom k = 0 := by
    intro k hk
    have := congrArg Subtype.val (LinearMap.mem_ker.mp hk)
    simpa using this
  refine locMono (kerPart C P Q φ hi V _ hK z) fun W k hk => ?_
  rw [map_restr_comp, LinearMap.comp_apply, ← hz]
  exact hk

/- English proof (translation)
Introduce `_ _ C P Q φ hs hi U` and use `⟨surj C P Q φ hs U, inj C P Q φ hs hi U⟩`.
-/
theorem main : ∀ (R : Type) [CommRing R] (C P Q : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)) (φ : P ⟶ Q), (∀ (U : Scheme.{0}) (y : Q.obj (op U)), Loc U fun V g => ∃ x, (φ.app (op V)).hom x = (Q.map g.op).hom y) → (∀ (U : Scheme.{0}) (x : P.obj (op U)), (φ.app (op U)).hom x = 0 → Loc U fun _ g => (P.map g.op).hom x = 0) → ∀ U : Scheme.{0}, (∀ y : TensorProduct (ULift.{1} R) (C.obj (op U)) (Q.obj (op U)), Loc U fun V g => ∃ x, LinearMap.lTensor _ (φ.app (op V)).hom x = TensorProduct.map (C.map g.op).hom (Q.map g.op).hom y) ∧ ∀ x : TensorProduct (ULift.{1} R) (C.obj (op U)) (P.obj (op U)), LinearMap.lTensor _ (φ.app (op U)).hom x = 0 → Loc U fun _ g => TensorProduct.map (C.map g.op).hom (P.map g.op).hom x = 0 :=
  fun _ _ C P Q φ hs hi U => ⟨surj C P Q φ hs U, inj C P Q φ hs hi U⟩

end GlobalTheory.EtC.TensLocBij

/- English proof (translation)
The claim follows from `GlobalTheory.EtC.TensLocBij.main`.
-/
theorem GlobalTheory.EtC.tensor_loc_bij : ∀ (R : Type) [CommRing R] (C P Q : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)) (φ : P ⟶ Q), (∀ (U : Scheme.{0}) (y : Q.obj (op U)), Loc U fun V g => ∃ x, (φ.app (op V)).hom x = (Q.map g.op).hom y) → (∀ (U : Scheme.{0}) (x : P.obj (op U)), (φ.app (op U)).hom x = 0 → Loc U fun _ g => (P.map g.op).hom x = 0) → ∀ U : Scheme.{0}, (∀ y : TensorProduct (ULift.{1} R) (C.obj (op U)) (Q.obj (op U)), Loc U fun V g => ∃ x, LinearMap.lTensor _ (φ.app (op V)).hom x = TensorProduct.map (C.map g.op).hom (Q.map g.op).hom y) ∧ ∀ x : TensorProduct (ULift.{1} R) (C.obj (op U)) (P.obj (op U)), LinearMap.lTensor _ (φ.app (op U)).hom x = 0 → Loc U fun _ g => TensorProduct.map (C.map g.op).hom (P.map g.op).hom x = 0 :=
  GlobalTheory.EtC.TensLocBij.main
