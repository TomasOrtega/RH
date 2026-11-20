import Mathlib
import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane
import Development.WeilBound.CoreStatements.HodgeTatePoints.GeCanon
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BtOrderValueEval
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SemiabelianAdicTorsionOneStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsUniqueTangentDualNumber

noncomputable section

namespace PositivityTheory.HtPt.Ge.TwDer
open GlobalTheory.CompanionTheory PositivityTheory.HtPt.Ge.Tan

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.BT.Tan GlobalTheory.CompanionTheory.Ar.LieEx GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G.Semi

section Rel
variable {R : Type} [CommRing R] [IsDomain R] {T : Type} [CommGroup T] (Γ : QFGroup R T)
  {S : Scheme.{0}} {G : Over S} [GrpObj G] {x : Spec (CommRingCat.of R) ⟶ S} {N : ℕ} {i : Γ.G.left ⟶ G.left}
  {j : Γ.G.left ⟶ Spec (CommRingCat.of (Γ.btOrder ⊤))} (U : Γ.G.left.Opens)
  {V : Type} [AddCommGroup V] [Module R V] [Module Rᵐᵒᵖ V] [IsCentralScalar R V]

/- English proof (translation)
Set `a` to `Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R V).toRingHom)`. Establish `ha : a ≫ Spec.map (CommRingCat.ofHom (algebraMap R (TrivSqZeroExt R V))) = 𝟙 _`. Rewrite using `[← Spec.map_comp, ← Spec.map_id]`. Use `congr 1`. Use `ht.inj (Over.mk (𝟙 _)) (Over.homMk (a ≫ y) (by` as an intermediate fact.

Express the relevant statement in the definitionally equal form `(a ≫ y) ≫ Γ.G.hom = 𝟙 _`. Rewrite using `[Category.assoc, y1, ha])) 1 (by`. Rewrite using `[one_left_eq]`. Simplify using `only [Over.homMk_left, Over.mk_hom, Category.id_comp, Category.assoc]`. Rewrite using `[unit_i' Γ ht, y3]`.

Use `congrArg Over.Hom.left h1` as an intermediate fact. Rewrite `this` using `[one_left_eq, Over.comp_left]`. Conclude with `this)`. Establish `h` using `congrArg Over.Hom.left this`. Rewrite `h` using `[one_left_eq]`.

Simplify `h` using `[a]`.
-/
theorem fst_comp_eq_unit (ht : Γ.IsTorsionAlong G x N i) {y : Spec (CommRingCat.of (TrivSqZeroExt R V)) ⟶ Γ.G.left}
    (y1 : y ≫ Γ.G.hom = Spec.map (CommRingCat.ofHom (algebraMap R (TrivSqZeroExt R V))))
    {v : ob x V ⟶ G} (y3 : y ≫ i = v.left) (h1 : zsec x ≫ v = 1) :
    Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R V).toRingHom) ≫ y = η[Γ.G].left := by
  let a := Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R V).toRingHom)
  have ha : a ≫ Spec.map (CommRingCat.ofHom (algebraMap R (TrivSqZeroExt R V))) = 𝟙 _ := by
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1
  have := ht.inj (Over.mk (𝟙 _)) (Over.homMk (a ≫ y) (by
      change (a ≫ y) ≫ Γ.G.hom = 𝟙 _
      rw [Category.assoc, y1, ha])) 1 (by
    rw [one_left_eq]
    simp only [Over.homMk_left, Over.mk_hom, Category.id_comp, Category.assoc]
    rw [unit_i' Γ ht, y3]
    have := congrArg Over.Hom.left h1
    rw [one_left_eq, Over.comp_left] at this
    exact this)
  have h := congrArg Over.Hom.left this
  rw [one_left_eq] at h
  simpa [a] using h

/- English proof (translation)
Take `⟨z', rfl⟩` from `zsec_surj (R := R) (V := V) z`. Establish `e2 : y (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R V).toRingHom) z') = η[Γ.G].left z'` using `congrArg (fun k : Spec (CommRingCat.of R) ⟶ _ => k z') e`. Rewrite using `[e2]`. Conclude with `hU z'`.
-/
theorem mem_of_fst_comp {y : Spec (CommRingCat.of (TrivSqZeroExt R V)) ⟶ Γ.G.left}
    (e : Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R V).toRingHom) ≫ y = η[Γ.G].left)
    (hU : ∀ z, η[Γ.G].left z ∈ U) (z) : y z ∈ U := by
  obtain ⟨z', rfl⟩ := zsec_surj (R := R) (V := V) z
  have e2 : y (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R V).toRingHom) z') = η[Γ.G].left z' :=
    congrArg (fun k : Spec (CommRingCat.of R) ⟶ _ => k z') e
  rw [e2]
  exact hU z'

/- English proof (translation)
Use `set f₀ := Spec.map (CommRingCat.ofHom (derRing (ev1 Γ) ψ).toRingHom) with hf₀`. Establish `hr : Set.range f₀ ⊆ Set.range (U.ι ≫ j)`. Introduce and unpack `_ ⟨z, rfl⟩`. Take `⟨z', rfl⟩` from `zsec_surj (R := R) (V := V) z`. Establish `e` using `spec_fst_comp Γ ψ`.

Rewrite `e` using `[← unit_j Γ hj]`. Establish `e2 : f₀ (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R V).toRingHom) z') = j (η[Γ.G].left z')`. Conclude with `congrArg (fun k : Spec (CommRingCat.of R) ⟶ _ => k z') e`. Use `⟨⟨_, hU z'⟩, ?_⟩` and prove the remaining obligations. Conclude with `e2.symm`.

Set `y'` to `IsOpenImmersion.lift (U.ι ≫ j) f₀ hr`. Establish `y'j : y' ≫ U.ι ≫ j = f₀` using `IsOpenImmersion.lift_fac (U.ι ≫ j) f₀ hr`. Set `y` to `y' ≫ U.ι`. Establish `yj : y ≫ j = f₀` using `by simpa [y] using y'j`. Establish `y1 : y ≫ Γ.G.hom = Spec.map (CommRingCat.ofHom (algebraMap R (TrivSqZeroExt R V)))`.

Rewrite using `[← hj.isOver, ← Category.assoc, yj]`. Conclude with `spec_alg_comp Γ ψ`. Set `v : ob x V ⟶ G` to `Over.homMk (y ≫ i) (by`. Express the relevant statement in the definitionally equal form `(y ≫ i) ≫ G.hom = _ ≫ x`. Rewrite using `[Category.assoc, ht.isOver, ← Category.assoc, y1])`.

Use `⟨v, ?_, ?_, y, y1, yj, rfl⟩` and prove the remaining obligations. Establish `rη : Set.range η[Γ.G].left ⊆ Set.range U.ι`. Introduce and unpack `_ ⟨z, rfl⟩`. Rewrite using `[Scheme.Opens.range_ι]`. Conclude with `hU z`.

Establish `hl` using `IsOpenImmersion.lift_fac U.ι η[Γ.G].left rη`. Establish `e0 : Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R V).toRingHom) ≫ y' = IsOpenImmersion.lift U.ι η[Γ.G].left rη`. Rewrite using `[← cancel_mono (U.ι ≫ j), Category.assoc, y'j, ← Category.assoc (IsOpenImmersion.lift U.ι η[Γ.G].left rη), hl, unit_j Γ hj]`. Conclude with `spec_fst_comp Γ ψ`. Establish `e1 : (zsec x : Over.mk x ⟶ ob x V).left ≫ y = η[Γ.G].left`.

Express the relevant statement in the definitionally equal form `Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R V).toRingHom) ≫ y' ≫ U.ι = _`. Rewrite using `[← Category.assoc, e0, hl]`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Rewrite using `[one_left_eq, Over.comp_left]`. Express the relevant statement in the definitionally equal form `(zsec x : Over.mk x ⟶ ob x V).left ≫ y ≫ i = x ≫ _`.

Rewrite using `[← Category.assoc, e1, unit_i' Γ ht]`. Conclude with `(ht.kernel (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R (TrivSqZeroExt R V))))) v).2 ⟨Over.homMk y y1, rfl⟩`.
-/
theorem rel_exists_open (ht : Γ.IsTorsionAlong G x N i) (hj : Γ.IsEmb (Γ.btOrder ⊤) j)
    (hU : ∀ z, η[Γ.G].left z ∈ U) [IsOpenImmersion (U.ι ≫ j)]
    (ψ : omega (Γ.btOrder ⊤) →ₗ[R] V) :
    ∃ v : ob x V ⟶ G, zsec x ≫ v = 1 ∧ v ^ N = 1 ∧ TanRel Γ i j ψ v := by
  set f₀ := Spec.map (CommRingCat.ofHom (derRing (ev1 Γ) ψ).toRingHom) with hf₀
  have hr : Set.range f₀ ⊆ Set.range (U.ι ≫ j) := by
    rintro _ ⟨z, rfl⟩
    obtain ⟨z', rfl⟩ := zsec_surj (R := R) (V := V) z
    have e := spec_fst_comp Γ ψ
    rw [← unit_j Γ hj] at e
    have e2 : f₀ (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R V).toRingHom) z') = j (η[Γ.G].left z') := by
      exact congrArg (fun k : Spec (CommRingCat.of R) ⟶ _ => k z') e
    refine ⟨⟨_, hU z'⟩, ?_⟩
    exact e2.symm
  let y' := IsOpenImmersion.lift (U.ι ≫ j) f₀ hr
  have y'j : y' ≫ U.ι ≫ j = f₀ := IsOpenImmersion.lift_fac (U.ι ≫ j) f₀ hr
  let y := y' ≫ U.ι
  have yj : y ≫ j = f₀ := by simpa [y] using y'j
  have y1 : y ≫ Γ.G.hom = Spec.map (CommRingCat.ofHom (algebraMap R (TrivSqZeroExt R V))) := by
    rw [← hj.isOver, ← Category.assoc, yj]
    exact spec_alg_comp Γ ψ
  let v : ob x V ⟶ G := Over.homMk (y ≫ i) (by
    change (y ≫ i) ≫ G.hom = _ ≫ x
    rw [Category.assoc, ht.isOver, ← Category.assoc, y1])
  refine ⟨v, ?_, ?_, y, y1, yj, rfl⟩
  · have rη : Set.range η[Γ.G].left ⊆ Set.range U.ι := by
      rintro _ ⟨z, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact hU z
    have hl := IsOpenImmersion.lift_fac U.ι η[Γ.G].left rη
    have e0 : Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R V).toRingHom) ≫ y' =
        IsOpenImmersion.lift U.ι η[Γ.G].left rη := by
      rw [← cancel_mono (U.ι ≫ j), Category.assoc, y'j, ← Category.assoc (IsOpenImmersion.lift U.ι η[Γ.G].left rη), hl,
        unit_j Γ hj]
      exact spec_fst_comp Γ ψ
    have e1 : (zsec x : Over.mk x ⟶ ob x V).left ≫ y = η[Γ.G].left := by
      change Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R V).toRingHom) ≫ y' ≫ U.ι = _
      rw [← Category.assoc, e0, hl]
    apply Over.OverMorphism.ext
    rw [one_left_eq, Over.comp_left]
    change (zsec x : Over.mk x ⟶ ob x V).left ≫ y ≫ i = x ≫ _
    rw [← Category.assoc, e1, unit_i' Γ ht]
  · exact (ht.kernel (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R (TrivSqZeroExt R V))))) v).2
      ⟨Over.homMk y y1, rfl⟩

/- English proof (translation)
Take `⟨y, a, b, c⟩` from `h`. Take `⟨y', a', b', c'⟩` from `h'`. Establish `m` using `mem_of_fst_comp Γ U (fst_comp_eq_unit Γ ht a c h1) hU`. Establish `m'` using `mem_of_fst_comp Γ U (fst_comp_eq_unit Γ ht a' c' h1') hU`. Establish `r : Set.range y ⊆ Set.range U.ι`.

Introduce and unpack `_ ⟨z, rfl⟩`. Rewrite using `[Scheme.Opens.range_ι]`. Conclude with `m z`. Establish `r' : Set.range y' ⊆ Set.range U.ι`. Introduce and unpack `_ ⟨z, rfl⟩`.

Rewrite using `[Scheme.Opens.range_ι]`. Conclude with `m' z`. Establish `hl` using `IsOpenImmersion.lift_fac U.ι y r`. Establish `hl'` using `IsOpenImmersion.lift_fac U.ι y' r'`. Establish `e : IsOpenImmersion.lift U.ι y r = IsOpenImmersion.lift U.ι y' r'`.

Rewrite using `[← cancel_mono (U.ι ≫ j), ← Category.assoc, ← Category.assoc, hl, hl', b, b']`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Rewrite using `[← c, ← c', ← hl, ← hl', e]`.
-/
theorem rel_eq_open (ht : Γ.IsTorsionAlong G x N i) (hU : ∀ z, η[Γ.G].left z ∈ U) [IsOpenImmersion (U.ι ≫ j)]
    {ψ : omega (Γ.btOrder ⊤) →ₗ[R] V} {v v' : ob x V ⟶ G}
    (h : TanRel Γ i j ψ v) (h' : TanRel Γ i j ψ v') (h1 : zsec x ≫ v = 1) (h1' : zsec x ≫ v' = 1) : v = v' := by
  obtain ⟨y, a, b, c⟩ := h
  obtain ⟨y', a', b', c'⟩ := h'
  have m := mem_of_fst_comp Γ U (fst_comp_eq_unit Γ ht a c h1) hU
  have m' := mem_of_fst_comp Γ U (fst_comp_eq_unit Γ ht a' c' h1') hU
  have r : Set.range y ⊆ Set.range U.ι := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact m z
  have r' : Set.range y' ⊆ Set.range U.ι := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact m' z
  have hl := IsOpenImmersion.lift_fac U.ι y r
  have hl' := IsOpenImmersion.lift_fac U.ι y' r'
  have e : IsOpenImmersion.lift U.ι y r = IsOpenImmersion.lift U.ι y' r' := by
    rw [← cancel_mono (U.ι ≫ j), ← Category.assoc, ← Category.assoc, hl, hl', b, b']
  apply Over.OverMorphism.ext
  rw [← c, ← c', ← hl, ← hl', e]

end Rel

section Core
variable {R : Type} [CommRing R] [IsDomain R] {T : Type} [CommGroup T] (Γ : QFGroup R T)
  {S : Scheme.{0}} {G : Over S} [GrpObj G] {x : Spec (CommRingCat.of R) ⟶ S} {N : ℕ} {i : Γ.G.left ⟶ G.left}
  {j : Γ.G.left ⟶ Spec (CommRingCat.of (Γ.btOrder ⊤))} (U : Γ.G.left.Opens)
  {P : Type} [AddCommGroup P] [Module R P] [Module Rᵐᵒᵖ P] [IsCentralScalar R P]

/- English proof (translation)
Use `letI : Module Rᵐᵒᵖ (omega (Γ.btOrder ⊤)) := opMod R _`. Use `haveI : IsCentralScalar R (omega (Γ.btOrder ⊤)) := opCentral R _`. Take `⟨v₀, hv₀, hvN, hrel⟩` from `rel_exists_open Γ U ht hj hU (LinearMap.id : omega (Γ.btOrder ⊤) →ₗ[R] omega (Γ.btOrder ⊤))`. Take `⟨θ, hθ, -⟩` from `huniv _ v₀ hv₀`. Establish `nat : ∀ (V : Type) [AddCommGroup V] [Module R V] [Module Rᵐᵒᵖ V] [IsCentralScalar R V] (ψ : omega (Γ.btOrder ⊤) →ₗ[R] V), TanRel Γ i j ψ (hom x (ψ ∘ₗ θ) ≫ u)`.

Introduce `V _ _ _ _ ψ`. Use `rel_map Γ hrel ψ` as an intermediate fact. Rewrite `this` using `[LinearMap.comp_id, ← hθ, ← Category.assoc, LieEx.hom_comp]`. Then use the resulting hypothesis. Establish `zero : ∀ (V : Type) [AddCommGroup V] [Module R V] [Module Rᵐᵒᵖ V] [IsCentralScalar R V] (ψ : omega (Γ.btOrder ⊤) →ₗ[R] V), ψ ∘ₗ θ = 0 → ψ = 0`. Introduce `V _ _ _ _ ψ h`.

Establish `h1` using `nat V ψ`. Establish `h2` using `nat V 0`. Rewrite `h1` using `[h]`. Rewrite `h2` using `[LinearMap.zero_comp]`. Conclude with `rel_unique Γ ht h1 h2`.

Establish `hN : N • θ = 0`. Establish `h1 : hom x (N • θ) ≫ u = 1` using `by rw [hom_nsmul u hu, hθ, hvN]`. Establish `h2 : hom x (0 : P →ₗ[R] omega (Γ.btOrder ⊤)) ≫ u = 1` using `hom_zero_comp u hu`. Establish `hz : zsec x ≫ (1 : ob x (omega (Γ.btOrder ⊤)) ⟶ G) = 1` using `MonObj.comp_one _`. Conclude with `(huniv _ 1 hz).unique h1 h2`.

Use `⟨θ, ?_, hN, ?_⟩` and prove the remaining obligations. Use `letI : Module Rᵐᵒᵖ (omega (Γ.btOrder ⊤) ⧸ LinearMap.range θ) := opMod R _ haveI : IsCentralScalar R (omega (Γ.btOrder ⊤) ⧸ LinearMap.range θ) := opCentral R _`. Use `zero _ (LinearMap.range θ).mkQ (by` as an intermediate fact. Use extensionality with `w`. Use the proof step `simp)`.

Rewrite using `[← LinearMap.range_eq_top, ← Submodule.ker_mkQ (LinearMap.range θ), this, LinearMap.ker_zero]`. Introduce `V _ _ _ _ φ hφ`. Establish `h1 : zsec x ≫ hom x φ ≫ u = 1` using `by rw [← Category.assoc, zsec_hom, hu]`. Establish `h2 : (hom x φ ≫ u) ^ N = 1` using `by rw [← hom_nsmul u hu, hφ, hom_zero_comp u hu]`. Take `⟨ψ, hψ⟩` from `rel_of_torsion Γ ht hj _ h1 h2`.

Establish `h3` using `rel_eq_open Γ U ht hU hψ (nat V ψ) h1 (by rw [← Category.assoc, zsec_hom, hu])`. Use `⟨ψ, (huniv V _ h1).unique h3.symm rfl, hψ⟩` and prove the remaining obligations.
-/
theorem exists_theta_open (ht : Γ.IsTorsionAlong G x N i) (hj : Γ.IsEmb (Γ.btOrder ⊤) j)
    (hU : ∀ z, η[Γ.G].left z ∈ U) [IsOpenImmersion (U.ι ≫ j)]
    (u : ob x P ⟶ G) (hu : zsec x ≫ u = 1)
    (huniv : ∀ (V : Type) [AddCommGroup V] [Module R V] [Module Rᵐᵒᵖ V] [IsCentralScalar R V] (v : ob x V ⟶ G),
      zsec x ≫ v = 1 → ∃! φ : P →ₗ[R] V, hom x φ ≫ u = v) :
    ∃ θ : P →ₗ[R] omega (Γ.btOrder ⊤), Function.Surjective θ ∧ N • θ = 0 ∧
      ∀ (V : Type) [AddCommGroup V] [Module R V] [Module Rᵐᵒᵖ V] [IsCentralScalar R V] (φ : P →ₗ[R] V), N • φ = 0 →
        ∃ ψ : omega (Γ.btOrder ⊤) →ₗ[R] V, ψ ∘ₗ θ = φ ∧ TanRel Γ i j ψ (hom x φ ≫ u) := by
  letI : Module Rᵐᵒᵖ (omega (Γ.btOrder ⊤)) := opMod R _
  haveI : IsCentralScalar R (omega (Γ.btOrder ⊤)) := opCentral R _
  obtain ⟨v₀, hv₀, hvN, hrel⟩ := rel_exists_open Γ U ht hj hU (LinearMap.id : omega (Γ.btOrder ⊤) →ₗ[R] omega (Γ.btOrder ⊤))
  obtain ⟨θ, hθ, -⟩ := huniv _ v₀ hv₀
  have nat : ∀ (V : Type) [AddCommGroup V] [Module R V] [Module Rᵐᵒᵖ V] [IsCentralScalar R V]
      (ψ : omega (Γ.btOrder ⊤) →ₗ[R] V), TanRel Γ i j ψ (hom x (ψ ∘ₗ θ) ≫ u) := by
    intro V _ _ _ _ ψ
    have := rel_map Γ hrel ψ
    rwa [LinearMap.comp_id, ← hθ, ← Category.assoc, LieEx.hom_comp] at this
  have zero : ∀ (V : Type) [AddCommGroup V] [Module R V] [Module Rᵐᵒᵖ V] [IsCentralScalar R V]
      (ψ : omega (Γ.btOrder ⊤) →ₗ[R] V), ψ ∘ₗ θ = 0 → ψ = 0 := by
    intro V _ _ _ _ ψ h
    have h1 := nat V ψ
    have h2 := nat V 0
    rw [h] at h1
    rw [LinearMap.zero_comp] at h2
    exact rel_unique Γ ht h1 h2
  have hN : N • θ = 0 := by
    have h1 : hom x (N • θ) ≫ u = 1 := by rw [hom_nsmul u hu, hθ, hvN]
    have h2 : hom x (0 : P →ₗ[R] omega (Γ.btOrder ⊤)) ≫ u = 1 := hom_zero_comp u hu
    have hz : zsec x ≫ (1 : ob x (omega (Γ.btOrder ⊤)) ⟶ G) = 1 := MonObj.comp_one _
    exact (huniv _ 1 hz).unique h1 h2
  refine ⟨θ, ?_, hN, ?_⟩
  · letI : Module Rᵐᵒᵖ (omega (Γ.btOrder ⊤) ⧸ LinearMap.range θ) := opMod R _
    haveI : IsCentralScalar R (omega (Γ.btOrder ⊤) ⧸ LinearMap.range θ) := opCentral R _
    have := zero _ (LinearMap.range θ).mkQ (by
      ext w
      simp)
    rw [← LinearMap.range_eq_top, ← Submodule.ker_mkQ (LinearMap.range θ), this, LinearMap.ker_zero]
  · intro V _ _ _ _ φ hφ
    have h1 : zsec x ≫ hom x φ ≫ u = 1 := by rw [← Category.assoc, zsec_hom, hu]
    have h2 : (hom x φ ≫ u) ^ N = 1 := by rw [← hom_nsmul u hu, hφ, hom_zero_comp u hu]
    obtain ⟨ψ, hψ⟩ := rel_of_torsion Γ ht hj _ h1 h2
    have h3 := rel_eq_open Γ U ht hU hψ (nat V ψ) h1 (by rw [← Category.assoc, zsec_hom, hu])
    refine ⟨ψ, (huniv V _ h1).unique h3.symm rfl, hψ⟩

end Core

/- English proof (translation)
Take `⟨u, hu, hupin, huniv⟩` from `GlobalTheory.T.dual_lattice_point_universal S G R x L M`. Take `⟨θ, hsurj, hNθ, hlift⟩` from `exists_theta_open Γ U ht hj hU u hu huniv`. Establish `hθN : ∀ w', θ (N • w') = 0` using `fun w' => by`. Use `LinearMap.congr_fun hNθ w'` as an intermediate fact. Simplify using `using this`.

Establish `hker : ∀ w, θ w = 0 ↔ ∃ u', w = N • u'`. Introduce `w`. Prove the components needed by the constructor for the conclusion. Introduce `hw`. Set `W : Submodule R (Module.Dual R L)` to `LinearMap.range ((N : R) • (LinearMap.id : Module.Dual R L →ₗ[R] Module.Dual R L))`.

Establish `h0 : N • W.mkQ = 0`. Use extensionality with `w'`. Simplify using `only [LinearMap.smul_apply, LinearMap.zero_apply, LinearMap.comp_apply]`. Conclude with `(map_nsmul W.mkQ N w').symm.trans ((Submodule.Quotient.mk_eq_zero W).2 ⟨w', by simp [Nat.cast_smul_eq_nsmul]⟩)`. Take `⟨ψ, hψ, -⟩` from `hlift _ W.mkQ h0`.

Establish `h1 : W.mkQ w = 0`. Rewrite using `[← hψ, LinearMap.comp_apply, hw, map_zero]`. Rewrite `h1` using `[Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]`. Take `⟨u', rfl⟩` from `h1`. Conclude with `⟨u', by simp [Nat.cast_smul_eq_nsmul]⟩`.

Introduce and unpack `⟨u', rfl⟩`. Conclude with `hθN u'`. Establish `hkey : ∀ e : L, ∃ ψ : omega (Γ.btOrder ⊤) →ₗ[R] (R ⧸ Ideal.span {(N : R)}), (∀ w, ψ (θ w) = Ideal.Quotient.mk (Ideal.span {(N : R)}) (w e)) ∧ ∃ v : Spec (CommRingCat.of (DualNumber (R ⧸ Ideal.span {(N : R)}))) ⟶ Γ.G.left, v ≫ Γ.G.hom = Spec.map (CommRingCat.ofHom ((algebraMap (R …`. Introduce `e`. Set `mkL : R →ₗ[R] (R ⧸ Ideal.span {(N : R)})` to `(Ideal.Quotient.mkₐ R (Ideal.span {(N : R)})).toLinearMap`.

Set `φ : Module.Dual R L →ₗ[R] (R ⧸ Ideal.span {(N : R)})` to `mkL ∘ₗ Module.Dual.eval R L e`. Establish `h0 : N • φ = 0`. Use extensionality with `w'`. Simplify using `only [φ, mkL, LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.zero_apply]`. Rewrite using `[← map_nsmul, ← Nat.cast_smul_eq_nsmul R, AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem, smul_eq_mul]`.

Conclude with `Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)`. Take `⟨ψ, hψ, y, y1, y2, y3⟩` from `hlift _ φ h0`. Use `⟨ψ, fun w => by simpa [φ, mkL] using LinearMap.congr_fun hψ w, Spec.map (CommRingCat.ofHom (kap _).toRingHom) ≫ y, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Category.assoc, y1, ← Spec.map_comp]`. Use `congr 1`.

Use extensionality with `r : 2`. Conclude with `kap_algebraMap _ r`. Establish `e1 : hom x φ ≫ u = hom x mkL ≫ M.pt e`. Rewrite using `[← hupin e, ← Category.assoc, LieEx.hom_comp]`. Rewrite using `[Category.assoc, y3, e1]`.

Express the relevant statement in the definitionally equal form `_ ≫ Spec.map _ ≫ (M.pt e).left = _`. Establish `e2 : CommRingCat.ofHom (TrivSqZeroExt.map mkL).toRingHom ≫ CommRingCat.ofHom (kap (Ideal.span {(N : R)})).toRingHom = CommRingCat.ofHom (dualMap (Ideal.Quotient.mk (Ideal.span {(N : R)})))`. Apply `CommRingCat.hom_ext` to reduce the goal to its premises. Apply `RingHom.ext` to reduce the goal to its premises. Introduce `a`.

Conclude with `kap_map _ a`. Rewrite using `[← Category.assoc, ← Spec.map_comp, e2]`. Rewrite using `[Category.assoc, y2, ← Spec.map_comp]`. Both sides reduce to the same expression. Establish `huniq : ∀ (e : L) (v v' : Spec (CommRingCat.of (DualNumber (R ⧸ Ideal.span {(N : R)}))) ⟶ Γ.G.left), v ≫ Γ.G.hom = Spec.map (CommRingCat.ofHom ((algebraMap (R ⧸ Ideal.span {(N : R)}) (DualNumber (R ⧸ Ideal.span {(N : R)}))).comp (Ideal.Quotient.mk _))) → v' ≫ Γ.G.hom = Spec.map ( …`.

Introduce `e v v' h1 h1' h2 h2'`. Use `ht.inj (Over.mk (Spec.map (CommRingCat.ofHom ((algebraMap (R ⧸ Ideal.span {(N : R)}) (DualNumber (R ⧸ Ideal.span {(N : R)}))).comp (Ideal.Quotient.mk _))))) (Over.homMk v h1) (Over.homMk v' h1') (by simpa using h2.trans h2'.symm)` as an intermediate fact. Conclude with `congrArg CommaMorphism.left this`. Use `⟨θ, hsurj, hker, ?_⟩` and prove the remaining obligations. Introduce `f w s hs`.

Establish `hval : ∀ (ψ : omega (Γ.btOrder ⊤) →ₗ[R] (R ⧸ Ideal.span {(N : R)})) (v : Spec (CommRingCat.of (DualNumber (R ⧸ Ideal.span {(N : R)}))) ⟶ Γ.G.left), v ≫ j = Spec.map (CommRingCat.ofHom ((kap (Ideal.span {(N : R)})).toRingHom.comp (derRing (ev1 Γ) ψ).toRingHom)) → valAt v ⊤ le_top …`. Introduce `ψ v hv`. Rewrite using `[val_of_emb Γ hj f.1 s hs v _ hv]`. Express the relevant statement in the definitionally equal form `kap _ (derRing (ev1 Γ) ψ f.1) = _`. Rewrite using `[derRing_of_mem (ev1 Γ) ψ f, kap_inr]`.

Both sides reduce to the same expression. Prove the components needed by the constructor for the conclusion. Introduce `hw e v h1 h2`. Take `⟨ψ, hψ, v', h1', h2', h3'⟩` from `hkey e`. Rewrite using `[huniq e v v' h1 h1' h2 h2', hval ψ v' h3', ← hw, hψ]`.

Introduce `H`. Take `⟨w₀, hw₀⟩` from `hsurj ((augIdeal (Γ.btOrder ⊤)).toCotangent f)`. Establish `hd : ∀ e, Ideal.Quotient.mk (Ideal.span {(N : R)}) ((w - w₀) e) = 0`. Introduce `e`. Take `⟨ψ, hψ, v', h1', h2', h3'⟩` from `hkey e`.

Establish `a1` using `H e v' h1' h2'`. Rewrite `a1` using `[hval ψ v' h3', ← hw₀, hψ]`. Establish `a2` using `TrivSqZeroExt.inr_injective a1`. Rewrite using `[LinearMap.sub_apply, map_sub, a2, sub_self]`. Take `⟨u', hu'⟩` from `dual_eq_smul N (w - w₀) hd`.

Establish `: θ (w - w₀) = 0` using `(hker _).2 ⟨u', hu'⟩`. Rewrite `this` using `[map_sub, sub_eq_zero]`. Rewrite using `[this, hw₀]`.
-/
theorem omega_open {R : Type} [CommRing R] [IsDomain R] {T : Type} [CommGroup T] [Finite T] (Γ : QFGroup R T)
    {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] [Smooth G.hom] {x : Spec (CommRingCat.of R) ⟶ S} {N : ℕ}
    {i : Γ.G.left ⟶ G.left} (ht : Γ.IsTorsionAlong G x N i) {L : Type} [AddCommGroup L] [Module R L]
    [Module.Projective R L] (M : LieModel G x L) {j : Γ.G.left ⟶ Spec (CommRingCat.of (Γ.btOrder ⊤))}
    (hj : Γ.IsEmb (Γ.btOrder ⊤) j) (U : Γ.G.left.Opens) (hU : ∀ z, η[Γ.G].left z ∈ U) [IsOpenImmersion (U.ι ≫ j)] :
    ∃ θ : Module.Dual R L →ₗ[R] omega (Γ.btOrder ⊤), Function.Surjective θ ∧ (∀ w, θ w = 0 ↔ ∃ u, w = N • u) ∧ ∀ (f : augIdeal (Γ.btOrder ⊤)) (w : Module.Dual R L) (s : Γ(Γ.G.left, ⊤)), Γ.HasValues s (f.1.1 : T → R) → (θ w = (augIdeal (Γ.btOrder ⊤)).toCotangent f ↔ ∀ (e : L) (v : Spec (CommRingCat.of (DualNumber (R ⧸ Ideal.span {(N : R)}))) ⟶ Γ.G.left), v ≫ Γ.G.hom = Spec.map (CommRingCat.ofHom ((algebraMap (R ⧸ Ideal.span {(N : R)}) (DualNumber (R ⧸ Ideal.span {(N : R)}))).comp (Ideal.Quotient.mk _))) → v ≫ i = Spec.map (CommRingCat.ofHom (dualMap (Ideal.Quotient.mk (Ideal.span {(N : R)})))) ≫ (M.pt e).left → valAt v ⊤ le_top s = TrivSqZeroExt.inr (Ideal.Quotient.mk (Ideal.span {(N : R)}) (w e))) := by
  obtain ⟨u, hu, hupin, huniv⟩ := GlobalTheory.T.dual_lattice_point_universal S G R x L M
  obtain ⟨θ, hsurj, hNθ, hlift⟩ := exists_theta_open Γ U ht hj hU u hu huniv
  have hθN : ∀ w', θ (N • w') = 0 := fun w' => by
    have := LinearMap.congr_fun hNθ w'
    simpa using this
  have hker : ∀ w, θ w = 0 ↔ ∃ u', w = N • u' := by
    intro w
    constructor
    · intro hw
      let W : Submodule R (Module.Dual R L) := LinearMap.range ((N : R) • (LinearMap.id : Module.Dual R L →ₗ[R] Module.Dual R L))
      have h0 : N • W.mkQ = 0 := by
        ext w'
        simp only [LinearMap.smul_apply, LinearMap.zero_apply, LinearMap.comp_apply]
        exact (map_nsmul W.mkQ N w').symm.trans ((Submodule.Quotient.mk_eq_zero W).2 ⟨w', by simp [Nat.cast_smul_eq_nsmul]⟩)
      obtain ⟨ψ, hψ, -⟩ := hlift _ W.mkQ h0
      have h1 : W.mkQ w = 0 := by
        rw [← hψ, LinearMap.comp_apply, hw, map_zero]
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h1
      obtain ⟨u', rfl⟩ := h1
      exact ⟨u', by simp [Nat.cast_smul_eq_nsmul]⟩
    · rintro ⟨u', rfl⟩
      exact hθN u'
  have hkey : ∀ e : L, ∃ ψ : omega (Γ.btOrder ⊤) →ₗ[R] (R ⧸ Ideal.span {(N : R)}),
      (∀ w, ψ (θ w) = Ideal.Quotient.mk (Ideal.span {(N : R)}) (w e)) ∧
      ∃ v : Spec (CommRingCat.of (DualNumber (R ⧸ Ideal.span {(N : R)}))) ⟶ Γ.G.left,
        v ≫ Γ.G.hom = Spec.map (CommRingCat.ofHom ((algebraMap (R ⧸ Ideal.span {(N : R)})
          (DualNumber (R ⧸ Ideal.span {(N : R)}))).comp (Ideal.Quotient.mk _))) ∧
        v ≫ i = Spec.map (CommRingCat.ofHom (dualMap (Ideal.Quotient.mk (Ideal.span {(N : R)})))) ≫ (M.pt e).left ∧
        v ≫ j = Spec.map (CommRingCat.ofHom
          ((kap (Ideal.span {(N : R)})).toRingHom.comp (derRing (ev1 Γ) ψ).toRingHom)) := by
    intro e
    let mkL : R →ₗ[R] (R ⧸ Ideal.span {(N : R)}) := (Ideal.Quotient.mkₐ R (Ideal.span {(N : R)})).toLinearMap
    let φ : Module.Dual R L →ₗ[R] (R ⧸ Ideal.span {(N : R)}) := mkL ∘ₗ Module.Dual.eval R L e
    have h0 : N • φ = 0 := by
      ext w'
      simp only [φ, mkL, LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.zero_apply]
      rw [← map_nsmul, ← Nat.cast_smul_eq_nsmul R, AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk,
        Ideal.Quotient.eq_zero_iff_mem, smul_eq_mul]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
    obtain ⟨ψ, hψ, y, y1, y2, y3⟩ := hlift _ φ h0
    refine ⟨ψ, fun w => by simpa [φ, mkL] using LinearMap.congr_fun hψ w, Spec.map (CommRingCat.ofHom (kap _).toRingHom) ≫ y, ?_, ?_, ?_⟩
    · rw [Category.assoc, y1, ← Spec.map_comp]
      congr 1
      ext r : 2
      exact kap_algebraMap _ r
    · have e1 : hom x φ ≫ u = hom x mkL ≫ M.pt e := by
        rw [← hupin e, ← Category.assoc, LieEx.hom_comp]
      rw [Category.assoc, y3, e1]
      change _ ≫ Spec.map _ ≫ (M.pt e).left = _
      have e2 : CommRingCat.ofHom (TrivSqZeroExt.map mkL).toRingHom ≫ CommRingCat.ofHom (kap (Ideal.span {(N : R)})).toRingHom =
          CommRingCat.ofHom (dualMap (Ideal.Quotient.mk (Ideal.span {(N : R)}))) := by
        apply CommRingCat.hom_ext
        apply RingHom.ext
        intro a
        exact kap_map _ a
      rw [← Category.assoc, ← Spec.map_comp, e2]
    · rw [Category.assoc, y2, ← Spec.map_comp]
      rfl
  have huniq : ∀ (e : L) (v v' : Spec (CommRingCat.of (DualNumber (R ⧸ Ideal.span {(N : R)}))) ⟶ Γ.G.left),
      v ≫ Γ.G.hom = Spec.map (CommRingCat.ofHom ((algebraMap (R ⧸ Ideal.span {(N : R)})
          (DualNumber (R ⧸ Ideal.span {(N : R)}))).comp (Ideal.Quotient.mk _))) →
      v' ≫ Γ.G.hom = Spec.map (CommRingCat.ofHom ((algebraMap (R ⧸ Ideal.span {(N : R)})
          (DualNumber (R ⧸ Ideal.span {(N : R)}))).comp (Ideal.Quotient.mk _))) →
      v ≫ i = Spec.map (CommRingCat.ofHom (dualMap (Ideal.Quotient.mk (Ideal.span {(N : R)})))) ≫ (M.pt e).left →
      v' ≫ i = Spec.map (CommRingCat.ofHom (dualMap (Ideal.Quotient.mk (Ideal.span {(N : R)})))) ≫ (M.pt e).left →
      v = v' := by
    intro e v v' h1 h1' h2 h2'
    have := ht.inj (Over.mk (Spec.map (CommRingCat.ofHom ((algebraMap (R ⧸ Ideal.span {(N : R)})
          (DualNumber (R ⧸ Ideal.span {(N : R)}))).comp (Ideal.Quotient.mk _)))))
      (Over.homMk v h1) (Over.homMk v' h1') (by simpa using h2.trans h2'.symm)
    exact congrArg CommaMorphism.left this
  refine ⟨θ, hsurj, hker, ?_⟩
  intro f w s hs
  have hval : ∀ (ψ : omega (Γ.btOrder ⊤) →ₗ[R] (R ⧸ Ideal.span {(N : R)}))
      (v : Spec (CommRingCat.of (DualNumber (R ⧸ Ideal.span {(N : R)}))) ⟶ Γ.G.left),
      v ≫ j = Spec.map (CommRingCat.ofHom
          ((kap (Ideal.span {(N : R)})).toRingHom.comp (derRing (ev1 Γ) ψ).toRingHom)) →
      valAt v ⊤ le_top s = TrivSqZeroExt.inr (ψ ((augIdeal (Γ.btOrder ⊤)).toCotangent f)) := by
    intro ψ v hv
    rw [val_of_emb Γ hj f.1 s hs v _ hv]
    change kap _ (derRing (ev1 Γ) ψ f.1) = _
    rw [derRing_of_mem (ev1 Γ) ψ f, kap_inr]
    rfl
  constructor
  · intro hw e v h1 h2
    obtain ⟨ψ, hψ, v', h1', h2', h3'⟩ := hkey e
    rw [huniq e v v' h1 h1' h2 h2', hval ψ v' h3', ← hw, hψ]
  · intro H
    obtain ⟨w₀, hw₀⟩ := hsurj ((augIdeal (Γ.btOrder ⊤)).toCotangent f)
    have hd : ∀ e, Ideal.Quotient.mk (Ideal.span {(N : R)}) ((w - w₀) e) = 0 := by
      intro e
      obtain ⟨ψ, hψ, v', h1', h2', h3'⟩ := hkey e
      have a1 := H e v' h1' h2'
      rw [hval ψ v' h3', ← hw₀, hψ] at a1
      have a2 := TrivSqZeroExt.inr_injective a1
      rw [LinearMap.sub_apply, map_sub, a2, sub_self]
    obtain ⟨u', hu'⟩ := dual_eq_smul N (w - w₀) hd
    have : θ (w - w₀) = 0 := (hker _).2 ⟨u', hu'⟩
    rw [map_sub, sub_eq_zero] at this
    rw [this, hw₀]

end PositivityTheory.HtPt.Ge.TwDer

namespace PositivityTheory.HtPt.Ge.TwDer
open GlobalTheory.CompanionTheory PositivityTheory.HtPt.Ge.Tan

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.BT.Tan GlobalTheory.CompanionTheory.Ar.LieEx GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G.Semi

section Der
variable {R : Type} [CommRing R] [IsDomain R] {T : Type} [CommGroup T] (Γ : QFGroup R T)
  {S : Scheme.{0}} {G : Over S} [GrpObj G] {x : Spec (CommRingCat.of R) ⟶ S} (N : ℕ) (i : Γ.G.left ⟶ G.left)
  {L : Type} [AddCommGroup L] [Module R L] (M : LieModel G x L)

abbrev Q (R : Type) [CommRing R] (N : ℕ) : Type := R ⧸ Ideal.span {(N : R)}

def IsTanPt (e : L) (v : Spec (CommRingCat.of (DualNumber (Q R N))) ⟶ Γ.G.left) : Prop :=
  v ≫ Γ.G.hom = Spec.map (CommRingCat.ofHom ((algebraMap (R ⧸ Ideal.span {(N : R)})
        (DualNumber (R ⧸ Ideal.span {(N : R)}))).comp (Ideal.Quotient.mk _))) ∧
    v ≫ i = Spec.map (CommRingCat.ofHom (dualMap (Ideal.Quotient.mk (Ideal.span {(N : R)})))) ≫ (M.pt e).left

def Der (f : T → R) (w : Module.Dual R L) : Prop :=
  ∃ s : Γ(Γ.G.left, ⊤), Γ.HasValues s f ∧ ∀ e : L,
    ∃ v : Spec (CommRingCat.of (DualNumber (R ⧸ Ideal.span {(N : R)}))) ⟶ Γ.G.left,
      v ≫ Γ.G.hom = Spec.map (CommRingCat.ofHom ((algebraMap (R ⧸ Ideal.span {(N : R)})
        (DualNumber (R ⧸ Ideal.span {(N : R)}))).comp (Ideal.Quotient.mk _))) ∧
      v ≫ i = Spec.map (CommRingCat.ofHom (dualMap (Ideal.Quotient.mk (Ideal.span {(N : R)})))) ≫
        (M.pt e).left ∧
      valAt v ⊤ le_top s = TrivSqZeroExt.inl (Ideal.Quotient.mk _ (f 1)) +
        TrivSqZeroExt.inr (Ideal.Quotient.mk (Ideal.span {(N : R)}) (w e))

/- English proof (translation)
Simplify using `[valAt]`.
-/
theorem valAt_add' {B : Type} [CommRing B] {X : Scheme.{0}} (y : Spec (CommRingCat.of B) ⟶ X) (a b : Γ(X, ⊤)) :
    valAt y ⊤ le_top (a + b) = valAt y ⊤ le_top a + valAt y ⊤ le_top b := by
  simp [valAt]

/- English proof (translation)
Simplify using `[valAt]`.
-/
theorem valAt_mul' {B : Type} [CommRing B] {X : Scheme.{0}} (y : Spec (CommRingCat.of B) ⟶ X) (a b : Γ(X, ⊤)) :
    valAt y ⊤ le_top (a * b) = valAt y ⊤ le_top a * valAt y ⊤ le_top b := by
  simp [valAt]

def cst (r : R) : Γ(Γ.G.left, ⊤) :=
  Γ.G.hom.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)

/- English proof (translation)
The claim follows from `ValEmb.valAt_pull Γ.G.hom y φ h r`.
-/
theorem valAt_cst {B : Type} [CommRing B] (y : Spec (CommRingCat.of B) ⟶ Γ.G.left) (φ : R →+* B)
    (h : y ≫ Γ.G.hom = Spec.map (CommRingCat.ofHom φ)) (r : R) : valAt y ⊤ le_top (cst Γ r) = φ r :=
  ValEmb.valAt_pull Γ.G.hom y φ h r

/- English proof (translation)
Introduce `t` and use `valAt_cst Γ (Γ.pt t).left (algebraMap R (FractionRing R)) (Over.w (Γ.pt t)) r`.
-/
theorem hasValues_cst (r : R) : Γ.HasValues (cst Γ r) (fun _ => r) := fun t =>
  valAt_cst Γ (Γ.pt t).left (algebraMap R (FractionRing R)) (Over.w (Γ.pt t)) r

/- English proof (translation)
Use `⟨cst Γ r, hasValues_cst Γ r, fun e => ?_⟩` and prove the remaining obligations. Take `⟨v, h1, h2⟩` from `h e`. Use `⟨v, h1, h2, ?_⟩` and prove the remaining obligations. Rewrite using `[valAt_cst Γ v _ h1]`. Simplify using `[TrivSqZeroExt.algebraMap_eq_inl]`.
-/
theorem der_const (r : R) (h : ∀ e : L, ∃ v, IsTanPt Γ N i M e v) : Der Γ N i M (fun _ => r) 0 := by
  refine ⟨cst Γ r, hasValues_cst Γ r, fun e => ?_⟩
  obtain ⟨v, h1, h2⟩ := h e
  refine ⟨v, h1, h2, ?_⟩
  rw [valAt_cst Γ v _ h1]
  simp [TrivSqZeroExt.algebraMap_eq_inl]

variable {Γ N i M}

/- English proof (translation)
Take `⟨s, hs, hv⟩` from `hf`. Take `⟨s', hs', hv'⟩` from `hg`. Prove the components needed by the constructor for the conclusion. Use `⟨s + s', fun t => ?_, fun e => ?_⟩` and prove the remaining obligations. Rewrite using `[valAt_add', hs t, hs' t]`.

Simplify using the standard rewrite rules. Take `⟨v, a, b, c⟩` from `hv e`. Take `⟨v', a', b', c'⟩` from `hv' e`. Take `rfl` from `hu e v v' ⟨a, b⟩ ⟨a', b'⟩`. Use `⟨v, a, b, ?_⟩` and prove the remaining obligations.

Rewrite using `[valAt_add', c, c']`. Apply the tactic sequence `refine TrivSqZeroExt.ext ?_ ?_ <;> simp`. Use `⟨s * s', fun t => ?_, fun e => ?_⟩` and prove the remaining obligations. Rewrite using `[valAt_mul', hs t, hs' t]`. Simplify using the standard rewrite rules.

Take `⟨v, a, b, c⟩` from `hv e`. Take `⟨v', a', b', c'⟩` from `hv' e`. Take `rfl` from `hu e v v' ⟨a, b⟩ ⟨a', b'⟩`. Use `⟨v, a, b, ?_⟩` and prove the remaining obligations. Rewrite using `[valAt_mul', c, c']`.

Use `TrivSqZeroExt.ext ?_ ?_` and prove the remaining obligations. Simplify using the standard rewrite rules. Simplify using `[TrivSqZeroExt.snd_mul, mul_comm, add_comm]`.
-/
theorem der_add_mul (hu : ∀ (e : L) (v v'), IsTanPt Γ N i M e v → IsTanPt Γ N i M e v' → v = v')
    {f g : T → R} {w w' : Module.Dual R L} (hf : Der Γ N i M f w) (hg : Der Γ N i M g w') :
    Der Γ N i M (f + g) (w + w') ∧ Der Γ N i M (f * g) (f 1 • w' + g 1 • w) := by
  obtain ⟨s, hs, hv⟩ := hf
  obtain ⟨s', hs', hv'⟩ := hg
  constructor
  · refine ⟨s + s', fun t => ?_, fun e => ?_⟩
    · rw [valAt_add', hs t, hs' t]; simp
    · obtain ⟨v, a, b, c⟩ := hv e
      obtain ⟨v', a', b', c'⟩ := hv' e
      obtain rfl := hu e v v' ⟨a, b⟩ ⟨a', b'⟩
      refine ⟨v, a, b, ?_⟩
      rw [valAt_add', c, c']
      refine TrivSqZeroExt.ext ?_ ?_ <;> simp
  · refine ⟨s * s', fun t => ?_, fun e => ?_⟩
    · rw [valAt_mul', hs t, hs' t]; simp
    · obtain ⟨v, a, b, c⟩ := hv e
      obtain ⟨v', a', b', c'⟩ := hv' e
      obtain rfl := hu e v v' ⟨a, b⟩ ⟨a', b'⟩
      refine ⟨v, a, b, ?_⟩
      rw [valAt_mul', c, c']
      refine TrivSqZeroExt.ext ?_ ?_
      · simp
      · simp [TrivSqZeroExt.snd_mul, mul_comm, add_comm]

/- English proof (translation)
Take `⟨s, hs, hv⟩` from `hf`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨s', hs', hv'⟩`. Establish `hss : s' = s`. Use `sub_eq_zero.mp (GlobalTheory.T.section_eq_zero_of_values R T Γ ⊤ (s' - s) ?_)` and prove the remaining obligations.

Introduce `t h`. Rewrite using `[ValEmb.valAt_sub]`. Conclude with `sub_eq_zero.mpr ((hs' t).trans (hs t).symm)`. Substitute `hss` using the available equality. Establish `hd : ∀ e, Ideal.Quotient.mk (Ideal.span {(N : R)}) ((w' - w) e) = 0`.

Introduce `e`. Take `⟨v, a, b, c⟩` from `hv e`. Take `⟨v', a', b', c'⟩` from `hv' e`. Take `rfl` from `hu e v v' ⟨a, b⟩ ⟨a', b'⟩`. Establish `h3` using `c'.symm.trans c`.

Establish `h4 : Ideal.Quotient.mk (Ideal.span {(N : R)}) (w' e) = Ideal.Quotient.mk (Ideal.span {(N : R)}) (w e)`. Simplify using `using congrArg TrivSqZeroExt.snd h3`. Rewrite using `[LinearMap.sub_apply, map_sub, h4, sub_self]`. Take `⟨u, hu'⟩` from `dual_eq_smul N (w' - w) hd`. Conclude with `⟨u, by rw [← hu']; abel⟩`.

Introduce and unpack `⟨u, rfl⟩`. Use `⟨s, hs, fun e => ?_⟩` and prove the remaining obligations. Take `⟨v, a, b, c⟩` from `hv e`. Use `⟨v, a, b, ?_⟩` and prove the remaining obligations. Rewrite using `[c]`.

Establish `h0 : Ideal.Quotient.mk (Ideal.span {(N : R)}) ((w + N • u) e) = Ideal.Quotient.mk (Ideal.span {(N : R)}) (w e)`. Use `Ideal.Quotient.eq.mpr ?_` and prove the remaining obligations. Rewrite using `[Ideal.mem_span_singleton]`. Conclude with `⟨u e, by simp⟩`. Rewrite using `[h0]`.
-/
theorem der_unique [Finite T] [Module.Projective R L]
    (hu : ∀ (e : L) (v v'), IsTanPt Γ N i M e v → IsTanPt Γ N i M e v' → v = v')
    {f : T → R} {w w' : Module.Dual R L} (hf : Der Γ N i M f w) :
    Der Γ N i M f w' ↔ ∃ u : Module.Dual R L, w' = w + N • u := by
  obtain ⟨s, hs, hv⟩ := hf
  constructor
  · rintro ⟨s', hs', hv'⟩
    have hss : s' = s := by
      refine sub_eq_zero.mp (GlobalTheory.T.section_eq_zero_of_values R T Γ ⊤ (s' - s) ?_)
      intro t h
      rw [ValEmb.valAt_sub]
      exact sub_eq_zero.mpr ((hs' t).trans (hs t).symm)
    subst hss
    have hd : ∀ e, Ideal.Quotient.mk (Ideal.span {(N : R)}) ((w' - w) e) = 0 := by
      intro e
      obtain ⟨v, a, b, c⟩ := hv e
      obtain ⟨v', a', b', c'⟩ := hv' e
      obtain rfl := hu e v v' ⟨a, b⟩ ⟨a', b'⟩
      have h3 := c'.symm.trans c
      have h4 : Ideal.Quotient.mk (Ideal.span {(N : R)}) (w' e) =
          Ideal.Quotient.mk (Ideal.span {(N : R)}) (w e) := by
        simpa using congrArg TrivSqZeroExt.snd h3
      rw [LinearMap.sub_apply, map_sub, h4, sub_self]
    obtain ⟨u, hu'⟩ := dual_eq_smul N (w' - w) hd
    exact ⟨u, by rw [← hu']; abel⟩
  · rintro ⟨u, rfl⟩
    refine ⟨s, hs, fun e => ?_⟩
    obtain ⟨v, a, b, c⟩ := hv e
    refine ⟨v, a, b, ?_⟩
    rw [c]
    have h0 : Ideal.Quotient.mk (Ideal.span {(N : R)}) ((w + N • u) e) =
        Ideal.Quotient.mk (Ideal.span {(N : R)}) (w e) := by
      refine Ideal.Quotient.eq.mpr ?_
      rw [Ideal.mem_span_singleton]
      exact ⟨u e, by simp⟩
    rw [h0]

end Der

end PositivityTheory.HtPt.Ge.TwDer

namespace PositivityTheory.HtPt.Ge.TwDer
open GlobalTheory.CompanionTheory PositivityTheory.HtPt.Ge.Tan

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open GlobalTheory GlobalTheory.PDivGroup GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.BT.Tan GlobalTheory.CompanionTheory.Ar.LieEx GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G.Semi

/- English proof (translation)
Establish `hex : ∀ e : L, ∃ v, IsTanPt Γ N i M e v` using `fun e => (TanLift.tangent_mod_torsion R T Γ S G x N i ht L M e).exists`. Establish `hu : ∀ (e : L) (v v'), IsTanPt Γ N i M e v → IsTanPt Γ N i M e v' → v = v'` using `fun e _ _ h h' => (TanLift.tangent_mod_torsion R T Γ S G x N i ht L M e).unique h h'`. Take `⟨θ, hsurj, -, hpin⟩` from `omega_open Γ ht M hj U hU`. Establish `hsec : ∀ f : Γ.btOrder ⊤, ∃ s, Γ.HasValues s (f : T → R)` using `fun f => ⟨j.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of (Γ.btOrder ⊤))).inv.hom f), fun t => ValEmb.valAt_pull j (Γ.pt t).left _ (hj.pt t) f⟩`. Establish `hpinD : ∀ (g : augIdeal (Γ.btOrder ⊤)) (w : Module.Dual R L), θ w = (augIdeal (Γ.btOrder ⊤)).toCotangent g → Der Γ N i M g.1.1 w`.

Introduce `g w h`. Take `⟨s, hs⟩` from `hsec g.1`. Use `⟨s, hs, fun e => ?_⟩` and prove the remaining obligations. Take `⟨v, a, b⟩` from `hex e`. Use `⟨v, a, b, ?_⟩` and prove the remaining obligations.

Establish `h0 : (g.1.1 : T → R) 1 = 0` using `g.2`. Rewrite using `[(hpin g w s hs).1 h e v a b, h0]`. Simplify using the standard rewrite rules. Use `⟨fun f hf => ?_, fun f w w' h => der_unique hu h, fun w => ?_, fun f g w w' h h' => der_add_mul hu h h', fun r => der_const Γ N i M r hex, fun f h => ?_⟩` and prove the remaining obligations. Set `a : Γ.btOrder ⊤` to `⟨f, hf⟩`.

Set `g : augIdeal (Γ.btOrder ⊤)` to `⟨a - algebraMap R _ (f 1), by`. Rewrite using `[OrderApi.mem_augIdeal]`. Simplify using `[a]⟩`. Take `⟨w, hw⟩` from `hsurj ((augIdeal (Γ.btOrder ⊤)).toCotangent g)`. Establish `h1` using `(der_add_mul hu (hpinD g w hw) (der_const Γ N i M (f 1) hex)).1`.

Use `⟨w + 0, ?_⟩` and prove the remaining obligations. Use `h1 using 1` and compare the differences between its conclusion and the goal. Use extensionality with `t`. Simplify using `[g, a]`. Take `⟨g, hg⟩` from `Ideal.toCotangent_surjective _ (θ w)`.

Conclude with `⟨g.1.1, g.1.2, hpinD g w hg.symm⟩`. Take `⟨s, hs, hv⟩` from `h`. Establish `h0 : (f.1.1 : T → R) 1 = 0` using `f.2`. Establish `h1` using `(hpin f 0 s hs).2 (fun e v a b => by`. Take `⟨v', a', b', c'⟩` from `hv e`.

Take `rfl` from `hu e v v' ⟨a, b⟩ ⟨a', b'⟩`. Rewrite using `[c', h0]`. Use the proof step `simp)`. Rewrite `h1` using `[map_zero]`. Conclude with `(Ideal.toCotangent_eq_zero _ _).1 h1.symm`.
-/
theorem der_all {R : Type} [CommRing R] [IsDomain R] {T : Type} [CommGroup T] [Finite T] (Γ : QFGroup R T)
    {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] [Smooth G.hom] {x : Spec (CommRingCat.of R) ⟶ S} {N : ℕ}
    {i : Γ.G.left ⟶ G.left} (ht : Γ.IsTorsionAlong G x N i) {L : Type} [AddCommGroup L] [Module R L]
    [Module.Projective R L] (M : LieModel G x L) {j : Γ.G.left ⟶ Spec (CommRingCat.of (Γ.btOrder ⊤))}
    (hj : Γ.IsEmb (Γ.btOrder ⊤) j) (U : Γ.G.left.Opens) (hU : ∀ z, η[Γ.G].left z ∈ U) [IsOpenImmersion (U.ι ≫ j)] :
    (∀ f ∈ Γ.btOrder ⊤, ∃ w, Der Γ N i M f w) ∧
    (∀ f w w', Der Γ N i M f w → (Der Γ N i M f w' ↔ ∃ u : Module.Dual R L, w' = w + N • u)) ∧
    (∀ w, ∃ f ∈ Γ.btOrder ⊤, Der Γ N i M f w) ∧
    (∀ f g w w', Der Γ N i M f w → Der Γ N i M g w' →
      Der Γ N i M (f + g) (w + w') ∧ Der Γ N i M (f * g) (f 1 • w' + g 1 • w)) ∧
    (∀ r : R, Der Γ N i M (fun _ => r) 0) ∧
    ∀ f : augIdeal (Γ.btOrder ⊤), Der Γ N i M f.1.1 0 → (f : Γ.btOrder ⊤) ∈ augIdeal (Γ.btOrder ⊤) ^ 2 := by
  have hex : ∀ e : L, ∃ v, IsTanPt Γ N i M e v := fun e =>
    (TanLift.tangent_mod_torsion R T Γ S G x N i ht L M e).exists
  have hu : ∀ (e : L) (v v'), IsTanPt Γ N i M e v → IsTanPt Γ N i M e v' → v = v' := fun e _ _ h h' =>
    (TanLift.tangent_mod_torsion R T Γ S G x N i ht L M e).unique h h'
  obtain ⟨θ, hsurj, -, hpin⟩ := omega_open Γ ht M hj U hU
  have hsec : ∀ f : Γ.btOrder ⊤, ∃ s, Γ.HasValues s (f : T → R) := fun f =>
    ⟨j.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of (Γ.btOrder ⊤))).inv.hom f), fun t =>
      ValEmb.valAt_pull j (Γ.pt t).left _ (hj.pt t) f⟩
  have hpinD : ∀ (g : augIdeal (Γ.btOrder ⊤)) (w : Module.Dual R L),
      θ w = (augIdeal (Γ.btOrder ⊤)).toCotangent g → Der Γ N i M g.1.1 w := by
    intro g w h
    obtain ⟨s, hs⟩ := hsec g.1
    refine ⟨s, hs, fun e => ?_⟩
    obtain ⟨v, a, b⟩ := hex e
    refine ⟨v, a, b, ?_⟩
    have h0 : (g.1.1 : T → R) 1 = 0 := g.2
    rw [(hpin g w s hs).1 h e v a b, h0]
    simp
  refine ⟨fun f hf => ?_, fun f w w' h => der_unique hu h, fun w => ?_, fun f g w w' h h' => der_add_mul hu h h',
    fun r => der_const Γ N i M r hex, fun f h => ?_⟩
  · let a : Γ.btOrder ⊤ := ⟨f, hf⟩
    let g : augIdeal (Γ.btOrder ⊤) := ⟨a - algebraMap R _ (f 1), by
      rw [OrderApi.mem_augIdeal]
      simp [a]⟩
    obtain ⟨w, hw⟩ := hsurj ((augIdeal (Γ.btOrder ⊤)).toCotangent g)
    have h1 := (der_add_mul hu (hpinD g w hw) (der_const Γ N i M (f 1) hex)).1
    refine ⟨w + 0, ?_⟩
    convert h1 using 1
    ext t
    simp [g, a]
  · obtain ⟨g, hg⟩ := Ideal.toCotangent_surjective _ (θ w)
    exact ⟨g.1.1, g.1.2, hpinD g w hg.symm⟩
  · obtain ⟨s, hs, hv⟩ := h
    have h0 : (f.1.1 : T → R) 1 = 0 := f.2
    have h1 := (hpin f 0 s hs).2 (fun e v a b => by
      obtain ⟨v', a', b', c'⟩ := hv e
      obtain rfl := hu e v v' ⟨a, b⟩ ⟨a', b'⟩
      rw [c', h0]
      simp)
    rw [map_zero] at h1
    exact (Ideal.toCotangent_eq_zero _ _).1 h1.symm

/- English proof (translation)
Establish `: Finite (La ⧸ LinearMap.range ((p ^ n) • (LinearMap.id : La →ₗ[ℤ] La)))`. Use `Module.finite_of_fg_torsion _ fun t => ?_` and prove the remaining obligations. Take `⟨b, rfl⟩` from `Submodule.Quotient.mk_surjective _ t`. Use `⟨⟨((p ^ n : ℕ) : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast (pow_pos hp.pos n).ne')⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[Submonoid.mk_smul, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]`.

Conclude with `⟨b, by rw [LinearMap.smul_apply, LinearMap.id_apply, natCast_zsmul]⟩`. Use `infer_instance`.
-/
theorem finite_levGrp' {La : Type} [AddCommGroup La] [Module.Finite ℤ La] {p : ℕ} (hp : p.Prime) (n : ℕ) :
    Finite (LevGrp La p n) := by
  have : Finite (La ⧸ LinearMap.range ((p ^ n) • (LinearMap.id : La →ₗ[ℤ] La))) := by
    refine Module.finite_of_fg_torsion _ fun t => ?_
    obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ t
    refine ⟨⟨((p ^ n : ℕ) : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast (pow_pos hp.pos n).ne')⟩, ?_⟩
    rw [Submonoid.mk_smul, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact ⟨b, by rw [LinearMap.smul_apply, LinearMap.id_apply, natCast_zsmul]⟩
  infer_instance

/- English proof (translation)
Use `haveI : PreValuationRing O := by`. Use `⟨fun a b => ?_⟩` and prove the remaining obligations. Break down `le_total (v (algebraMap O C a)) (v (algebraMap O C b)) with h | h` into its components or cases. Take `⟨c, hc⟩` from `hv.dvd_of_le h`. Conclude with `⟨c, Or.inr hc.symm⟩`.

Take `⟨c, hc⟩` from `hv.dvd_of_le h`. Conclude with `⟨c, Or.inl hc.symm⟩`. Conclude with `{}`.
-/
theorem valuationRing_of_integers {C : Type} [Field C] (v : Valuation C NNReal) {O : Type} [CommRing O] [IsDomain O]
    [Algebra O C] (hv : v.Integers O) : ValuationRing O := by
  haveI : PreValuationRing O := by
    refine ⟨fun a b => ?_⟩
    rcases le_total (v (algebraMap O C a)) (v (algebraMap O C b)) with h | h
    · obtain ⟨c, hc⟩ := hv.dvd_of_le h
      exact ⟨c, Or.inr hc.symm⟩
    · obtain ⟨c, hc⟩ := hv.dvd_of_le h
      exact ⟨c, Or.inl hc.symm⟩
  exact {}

/- English proof (translation)
Introduce `p _ C _ _ _ v O _ _ _ hv hp hO S _ G _ _ hG y La _ _ _ X L _ _ M n`. Use `haveI : ValuationRing O := valuationRing_of_integers v hv`. Use `haveI : IsLocalRing O := inferInstance`. Use `haveI : IsIntegrallyClosed O := inferInstance`. Use `haveI : Smooth G.hom := hG.smooth`.

Use `haveI : Finite (LevGrp La p n) := finite_levGrp' (Fact.out) n`. Use `haveI : Module.Projective O L := (GlobalTheory.T.lie_model_finite_base_change S G O y L M).2.1`. Take `⟨U, H, hfin, -⟩` from `GlobalTheory.T.semiabelian_adic_torsion_one p C v O hv hp hO S G hG y La X`. Take `⟨j, hj, -⟩` from `GlobalTheory.T.existsUnique_btOrder_embedding O _ (X.Γ n)`. Use `haveI := (EmbSub.openImmersion_translatesCover O _ (X.Γ n) (U n) (hfin n) j hj).1`.

Conclude with `der_all (X.Γ n) (X.tors n) M hj (U n) (hfin n).one`.
-/
theorem der_main : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [IsDomain O] [Algebra O C] (hv : v.Integers O) (hp : v (p : C) < 1) (hO : IsAdicComplete (Ideal.span {(p : O)}) O) (S : Scheme.{0}) [IsLocallyNoetherian S] (G : Over S) [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G) (y : Spec (CommRingCat.of O) ⟶ S) (La : Type) [AddCommGroup La] [Module.Free ℤ La] [Module.Finite ℤ La] (X : TorsTower p G y La) (L : Type) [AddCommGroup L] [Module O L] (M : LieModel G y L) (n : ℕ), (∀ f ∈ (X.Γ n).btOrder ⊤, ∃ w, X.IsDer M n f w) ∧ (∀ f w w', X.IsDer M n f w → (X.IsDer M n f w' ↔ ∃ u : Module.Dual O L, w' = w + (p ^ n) • u)) ∧ (∀ w, ∃ f ∈ (X.Γ n).btOrder ⊤, X.IsDer M n f w) ∧ (∀ f g w w', X.IsDer M n f w → X.IsDer M n g w' → X.IsDer M n (f + g) (w + w') ∧ X.IsDer M n (f * g) (f 1 • w' + g 1 • w)) ∧ (∀ r : O, X.IsDer M n (fun _ => r) 0) ∧ ∀ f : augIdeal ((X.Γ n).btOrder ⊤), X.IsDer M n f.1.1 0 → (f : (X.Γ n).btOrder ⊤) ∈ augIdeal ((X.Γ n).btOrder ⊤) ^ 2 := by
  intro p _ C _ _ _ v O _ _ _ hv hp hO S _ G _ _ hG y La _ _ _ X L _ _ M n
  haveI : ValuationRing O := valuationRing_of_integers v hv
  haveI : IsLocalRing O := inferInstance
  haveI : IsIntegrallyClosed O := inferInstance
  haveI : Smooth G.hom := hG.smooth
  haveI : Finite (LevGrp La p n) := finite_levGrp' (Fact.out) n
  haveI : Module.Projective O L := (GlobalTheory.T.lie_model_finite_base_change S G O y L M).2.1
  obtain ⟨U, H, hfin, -⟩ := GlobalTheory.T.semiabelian_adic_torsion_one p C v O hv hp hO S G hG y La X
  obtain ⟨j, hj, -⟩ := GlobalTheory.T.existsUnique_btOrder_embedding O _ (X.Γ n)
  haveI := (EmbSub.openImmersion_translatesCover O _ (X.Γ n) (U n) (hfin n) j hj).1
  exact der_all (X.Γ n) (X.tors n) M hj (U n) (hfin n).one

end PositivityTheory.HtPt.Ge.TwDer
