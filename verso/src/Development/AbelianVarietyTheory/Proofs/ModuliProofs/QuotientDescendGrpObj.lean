import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsActionOfIsPullback

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

namespace GlobalTheory

namespace QuotientDescent

variable {X X' : Scheme.{0}} {π : X ⟶ X'} {G : Over X} {G' : Over X'} {φ : G.left ⟶ G'.left}

noncomputable def up (H : IsPullback φ G.hom G'.hom π) {T : Over X'} (z : T ⟶ G') :
    (Over.pullback π).obj T ⟶ G :=
  Over.homMk (H.lift (pullback.fst T.hom π ≫ z.left) (pullback.snd T.hom π)
    (by rw [Category.assoc, Over.w, pullback.condition])) (H.lift_snd ..)

/- English proof (translation)
The claim follows from `H.lift_fst ..`.
-/
theorem up_left (H : IsPullback φ G.hom G'.hom π) {T : Over X'} (z : T ⟶ G') :
    (up H z).left ≫ φ = pullback.fst T.hom π ≫ z.left := H.lift_fst ..

/- English proof (translation)
The claim follows from `Over.OverMorphism.ext (H.hom_ext h ((Over.w x).trans (Over.w y).symm))`.
-/
theorem hom_ext (H : IsPullback φ G.hom G'.hom π) {T : Over X} {x y : T ⟶ G}
    (h : x.left ≫ φ = y.left ≫ φ) : x = y :=
  Over.OverMorphism.ext (H.hom_ext h ((Over.w x).trans (Over.w y).symm))

/- English proof (translation)
Use `hom_ext H ?_` and prove the remaining obligations. Establish `A : ((Over.pullback π).map u).left ≫ pullback.fst T.hom π = pullback.fst T'.hom π ≫ u.left` using `pullback.lift_fst _ _ _`. Rewrite using `[up_left, Over.comp_left, Over.comp_left, Category.assoc, up_left, ← Category.assoc, ← Category.assoc, A]`.
-/
theorem up_comp (H : IsPullback φ G.hom G'.hom π) {T T' : Over X'} (u : T' ⟶ T) (z : T ⟶ G') :
    up H (u ≫ z) = (Over.pullback π).map u ≫ up H z := by
  refine hom_ext H ?_
  have A : ((Over.pullback π).map u).left ≫ pullback.fst T.hom π = pullback.fst T'.hom π ≫ u.left :=
    pullback.lift_fst _ _ _
  rw [up_left, Over.comp_left, Over.comp_left, Category.assoc, up_left, ← Category.assoc,
    ← Category.assoc, A]

variable {Γ : Type} [Group Γ] [Finite Γ] {ρ : Γ →* Aut X} {τ : Γ →* Aut G.left}

/- English proof (translation)
The claim follows from `fun x y e ↦ by have Hp := (IsPullback.of_hasPullback T.hom π).flip obtain ⟨σ, hσ⟩ := exists_action_of_isPullback ρ hq.comp_eq Hp have hq' := hq.of_isPullback Hp (fun g ↦ (hσ g).2) (fun g ↦ (hσ g).1) refine Over.OverMorphism.ext (hq'.hom_ext ?_) rw [← up_left H, ← up_left H, e]`.
-/
theorem up_injective (hq : IsAffineQuotient ρ π) (H : IsPullback φ G.hom G'.hom π) {T : Over X'}
    (hT : Flat T.hom) : Function.Injective (up H : (T ⟶ G') → _) := fun x y e ↦ by
  have Hp := (IsPullback.of_hasPullback T.hom π).flip
  obtain ⟨σ, hσ⟩ := exists_action_of_isPullback ρ hq.comp_eq Hp
  have hq' := hq.of_isPullback Hp (fun g ↦ (hσ g).2) (fun g ↦ (hσ g).1)
  refine Over.OverMorphism.ext (hq'.hom_ext ?_)
  rw [← up_left H, ← up_left H, e]

def Equivariant (ρ : Γ →* Aut X) (τ : Γ →* Aut G.left) {T : Over X'}
    (w : (Over.pullback π).obj T ⟶ G) : Prop :=
  ∀ g (s : pullback T.hom π ⟶ pullback T.hom π), s ≫ pullback.fst T.hom π = pullback.fst T.hom π →
    s ≫ pullback.snd T.hom π = pullback.snd T.hom π ≫ (ρ g).hom →
    s ≫ w.left = w.left ≫ (τ g).hom

/- English proof (translation)
Establish `Hp` using `(IsPullback.of_hasPullback T.hom π).flip`. Take `⟨σ, hσ⟩` from `exists_action_of_isPullback ρ hq.comp_eq Hp`. Establish `hq'` using `hq.of_isPullback Hp (fun g ↦ (hσ g).2) (fun g ↦ (hσ g).1)`. Take `⟨z, hz⟩` from `hq'.exists_comp_eq (w.left ≫ φ) fun g ↦ by`. Rewrite using `[← Category.assoc, hw g _ (hσ g).1 (hσ g).2, Category.assoc, hτ]`.

Use `⟨Over.homMk z (hq'.hom_ext ?_), hom_ext H ((up_left H _).trans hz)⟩` and prove the remaining obligations. Rewrite using `[reassoc_of% hz, H.w, pullback.condition]`. Conclude with `(Category.assoc _ _ _).symm.trans (congrArg (· ≫ π) (Over.w w))`.
-/
theorem Equivariant.exists_up (hq : IsAffineQuotient ρ π) (H : IsPullback φ G.hom G'.hom π)
    (hτ : ∀ g, (τ g).hom ≫ φ = φ) {T : Over X'} (hT : Flat T.hom)
    {w : (Over.pullback π).obj T ⟶ G} (hw : Equivariant ρ τ w) : ∃ z : T ⟶ G', up H z = w := by
  have Hp := (IsPullback.of_hasPullback T.hom π).flip
  obtain ⟨σ, hσ⟩ := exists_action_of_isPullback ρ hq.comp_eq Hp
  have hq' := hq.of_isPullback Hp (fun g ↦ (hσ g).2) (fun g ↦ (hσ g).1)
  obtain ⟨z, hz⟩ := hq'.exists_comp_eq (w.left ≫ φ) fun g ↦ by
    rw [← Category.assoc, hw g _ (hσ g).1 (hσ g).2, Category.assoc, hτ]
  refine ⟨Over.homMk z (hq'.hom_ext ?_), hom_ext H ((up_left H _).trans hz)⟩
  rw [reassoc_of% hz, H.w, pullback.condition]
  exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ π) (Over.w w))

omit [Finite Γ] in
/- English proof (translation)
The claim follows from `fun g s h₁ h₂ ↦ by have e : (up H z).left ≫ G.hom = pullback.snd T.hom π := Over.w _ refine H.hom_ext ?_ ?_ · rw [Category.assoc, Category.assoc, hτ, up_left, reassoc_of% h₁] · rw [Category.assoc, Category.assoc, hτ', e, h₂, reassoc_of% e]`.
-/
theorem equivariant_up (H : IsPullback φ G.hom G'.hom π) (hτ : ∀ g, (τ g).hom ≫ φ = φ)
    (hτ' : ∀ g, (τ g).hom ≫ G.hom = G.hom ≫ (ρ g).hom) {T : Over X'} (z : T ⟶ G') :
    Equivariant ρ τ (up H z) := fun g s h₁ h₂ ↦ by
  have e : (up H z).left ≫ G.hom = pullback.snd T.hom π := Over.w _
  refine H.hom_ext ?_ ?_
  · rw [Category.assoc, Category.assoc, hτ, up_left, reassoc_of% h₁]
  · rw [Category.assoc, Category.assoc, hτ', e, h₂, reassoc_of% e]

noncomputable def equivariantSubgroup [GrpObj G] (hτ : ∀ g, IsGrpPullback G G (ρ g).hom (τ g).hom)
    (T : Over X') : Subgroup ((Over.pullback π).obj T ⟶ G) :=
  ⨅ (g : Γ) (s : pullback T.hom π ⟶ pullback T.hom π)
    (_ : s ≫ pullback.fst T.hom π = pullback.fst T.hom π)
    (h : s ≫ pullback.snd T.hom π = pullback.snd T.hom π ≫ (ρ g).hom),
    (preHom (Over.homMk s h)).eqLocus (pushHom (hτ g) ((Over.pullback π).obj T))

omit [Finite Γ] in
/- English proof (translation)
Simplify using `only [equivariantSubgroup, Subgroup.mem_iInf]`. Conclude with `⟨fun h g s h₁ h₂ ↦ congrArg (fun z ↦ z.left) (h g s h₁ h₂), fun h g s h₁ h₂ ↦ Over.OverMorphism.ext (h g s h₁ h₂)⟩`.
-/
theorem mem_equivariantSubgroup [GrpObj G] (hτ : ∀ g, IsGrpPullback G G (ρ g).hom (τ g).hom)
    {T : Over X'} {w : (Over.pullback π).obj T ⟶ G} :
    w ∈ equivariantSubgroup hτ T ↔ Equivariant ρ τ w := by
  simp only [equivariantSubgroup, Subgroup.mem_iInf]
  exact ⟨fun h g s h₁ h₂ ↦ congrArg (fun z ↦ z.left) (h g s h₁ h₂),
    fun h g s h₁ h₂ ↦ Over.OverMorphism.ext (h g s h₁ h₂)⟩

end QuotientDescent

open QuotientDescent

/- English proof (translation)
Introduce `Γ _ _ O _ X X' ρ π G _ _ G' φ τ a ⟨h₁, h₂, h₃⟩ H hG' hτ`. Establish `hq : IsAffineQuotient ρ π` using `⟨h₂, h₁, fun V ↦ (h₃ V).1, fun V s hs ↦ (h₃ V).2 s fun g _ ↦ (hs g).2⟩`. Establish `hp (g)` using `(hτ g).2.1`. Establish `f₀ : Flat (𝟙_ (Over X')).hom` using `inferInstanceAs (Flat (𝟙 X'))`. Establish `f₂ {A B : Over X'} (hA : Flat A.hom) (hB : Flat B.hom) : Flat (A ⊗ B).hom` using `inferInstanceAs (Flat (pullback.fst A.hom B.hom ≫ A.hom))`.

Establish `inj {T : Over X'} (hT : Flat T.hom) {x y : T ⟶ G'} (e : up H x = up H y) : x = y` using `up_injective hq H hT e`. Establish `ex {T : Over X'} (hT : Flat T.hom) {w : (Over.pullback π).obj T ⟶ G} (hw : w ∈ equivariantSubgroup hp T) : ∃ z : T ⟶ G', up H z = w` using `((mem_equivariantSubgroup hp).mp hw).exists_up hq H (fun g ↦ (hτ g).1) hT`. Establish `mem {T : Over X'} (z : T ⟶ G') : up H z ∈ equivariantSubgroup hp T` using `(mem_equivariantSubgroup hp).mpr (equivariant_up H (fun g ↦ (hτ g).1) (fun g ↦ (hp g).1.w) z)`. Take `⟨m, hm⟩` from `ex (f₂ hG' hG') (mul_mem (mem (fst G' G')) (mem (snd G' G')))`. Take `⟨e, he⟩` from `ex f₀ (one_mem _)`.

Take `⟨i, hi⟩` from `ex hG' (inv_mem (mem (𝟙 G')))`. Establish `hb (c : O) : ∃ z : G' ⟶ G', up H z = up H (𝟙 G') ≫ a.act c` using `ex hG' ((mem_equivariantSubgroup hp).mpr fun g s k₁ k₂ ↦ by`. Rewrite using `[Over.comp_left, Category.assoc, (hτ g).2.2, reassoc_of% ((mem_equivariantSubgroup hp).mp (mem (𝟙 G')) g s k₁ k₂)])`. Use `choose b hb using hb`. Establish `hm' {T : Over X'} (u : T ⟶ G' ⊗ G') : up H (u ≫ m) = up H (u ≫ fst _ _) * up H (u ≫ snd _ _)`.

Rewrite using `[up_comp, hm, MonObj.comp_mul, ← up_comp, ← up_comp]`. Establish `he' {T : Over X'} (u : T ⟶ 𝟙_ _) : up H (u ≫ e) = 1`. Rewrite using `[up_comp, he, MonObj.comp_one]`. Establish `hb' {T : Over X'} (u : T ⟶ G') (c : O) : up H (u ≫ b c) = up H u ≫ a.act c`. Rewrite using `[up_comp, hb, ← Category.assoc, ← up_comp, Category.comp_id]`.

Use `letI : GrpObj G' := { one := e mul := m one_mul := inj (f₂ f₀ hG') (by`. Rewrite using `[hm', whiskerRight_fst, he', _root_.one_mul, whiskerRight_snd, leftUnitor_hom])`. Use `mul_one := inj (f₂ hG' f₀) (by`. Rewrite using `[hm', whiskerLeft_snd, he', _root_.mul_one, whiskerLeft_fst, rightUnitor_hom])`. Use `mul_assoc := inj (f₂ (f₂ hG' hG') hG') (by`.

Rewrite using `[← Category.assoc, hm' (m ▷ G'), hm' (_ ≫ G' ◁ m), whiskerRight_fst, whiskerRight_snd, Category.assoc, Category.assoc, whiskerLeft_fst, whiskerLeft_snd, hm' (fst _ _), ← Category.assoc _ _ m, hm', Category.assoc, Category.assoc, associator_hom_fst, associator_hom_snd_fst, associa …`. Use `inv := i`. Use `left_inv := inj hG' (by rw [hm', he', lift_fst, lift_snd, hi, inv_mul_cancel])`. Use `right_inv := inj hG' (by rw [hm', he', lift_fst, lift_snd, hi, mul_inv_cancel]) }`. Establish `hmul {T : Over X'} (x y : T ⟶ G') : up H (x * y) = up H x * up H y`.

Rewrite using `[Hom.mul_def]`. Conclude with `(hm' _).trans (by rw [lift_fst, lift_snd])`. Establish `: IsCommMonObj G'` using `⟨inj (f₂ hG' hG') (by`. Use `(hm' _).trans (Eq.trans ?_ hm.symm)` and prove the remaining obligations. Rewrite using `[braiding_hom_fst, braiding_hom_snd, mul_comm])⟩`.

Set `a' : OAct O G'` to `{ act := b hom c := by`. Use `a.hom c` as an intermediate fact. Use `⟨inj f₀ ?_, inj (f₂ hG' hG') ?_⟩` and prove the remaining obligations. Rewrite using `[hb']`. Express the relevant statement in the definitionally equal form `up H e ≫ _ = up H e`.

Rewrite using `[he, MonObj.one_comp]`. Rewrite using `[hb']`. Express the relevant statement in the definitionally equal form `up H m ≫ _ = up H (_ ≫ m)`. Rewrite using `[hm', hm, tensorHom_fst, tensorHom_snd, hb', hb', MonObj.mul_comp]`. Use `one := inj hG' (by rw [hb, a.one, Category.comp_id])`.

Use `mul c d := inj hG' (by rw [hb', hb, hb, a.mul, Category.assoc])`. Use `add c d := inj hG' (by rw [hmul, hb, hb, hb, a.add, MonObj.comp_mul]) }`. Establish `sec {T : Over X} : ∃ s : T ⟶ (Over.pullback π).obj (Over.mk (T.hom ≫ π)), s.left ≫ pullback.fst _ π = 𝟙 T.left` using `⟨Over.homMk (pullback.lift (𝟙 T.left) T.hom (Category.id_comp _)) (pullback.lift_snd ..), pullback.lift_fst ..⟩`. Use `⟨inferInstance, this, a', ⟨H, fun T x y x₀ y₀ hx hy ↦ ?_⟩, fun c ↦ ?_⟩` and prove the remaining obligations. Take `⟨s, hs⟩` from `sec (T := T)`.

Establish `k (z : Over.mk (T.hom ≫ π) ⟶ G') : (s ≫ up H z).left ≫ φ = z.left`. Rewrite using `[Over.comp_left, Category.assoc, up_left, reassoc_of% hs]`. Rewrite using `[← k, hmul, MonObj.comp_mul, QuotientDescent.hom_ext H ((k x₀).trans hx), QuotientDescent.hom_ext H ((k y₀).trans hy)]`. Take `⟨s, hs⟩` from `sec (T := G)`. Establish `k (z : Over.mk (G.hom ≫ π) ⟶ G') : (s ≫ up H z).left ≫ φ = z.left`.

Rewrite using `[Over.comp_left, Category.assoc, up_left, reassoc_of% hs]`. Set `u : Over.mk (G.hom ≫ π) ⟶ G'` to `Over.homMk φ H.w`. Establish `hu : s ≫ up H u = 𝟙 G` using `QuotientDescent.hom_ext H ((k u).trans (Category.id_comp _).symm)`. Use `k (u ≫ b c)` as an intermediate fact. Rewrite `this` using `[hb', reassoc_of% hu]`. Then use the resulting hypothesis.
-/
theorem quotient_descend_grpObj :
    ∀ (Γ : Type) [Group Γ] [Finite Γ] (O : Type) [CommRing O] (X X' : Scheme.{0}) (ρ : Γ →* Aut X) (π : X ⟶ X') (G : Over X) [GrpObj G] [IsCommMonObj G] (G' : Over X') (φ : G.left ⟶ G'.left) (τ : Γ →* Aut G.left) (a : OAct O G), (IsAffineHom π ∧ (∀ g, (ρ g).hom ≫ π = π) ∧ ∀ V : X'.Opens, Function.Injective (π.app V).hom ∧ ∀ f : Γ(X, π ⁻¹ᵁ V), (∀ g (h : π ⁻¹ᵁ V ≤ (ρ g).hom ⁻¹ᵁ (π ⁻¹ᵁ V)), ((ρ g).hom.appLE _ _ h).hom f = f) → f ∈ Set.range (π.app V).hom) → IsPullback φ G.hom G'.hom π → Flat G'.hom → (∀ g, (τ g).hom ≫ φ = φ ∧ IsGrpPullback G G (ρ g).hom (τ g).hom ∧ ∀ c, (a.act c).left ≫ (τ g).hom = (τ g).hom ≫ (a.act c).left) → ∃ (_ : GrpObj G') (_ : IsCommMonObj G') (a' : OAct O G'), IsGrpPullback G G' π φ ∧ ∀ c, (a.act c).left ≫ φ = φ ≫ (a'.act c).left := by
  intro Γ _ _ O _ X X' ρ π G _ _ G' φ τ a ⟨h₁, h₂, h₃⟩ H hG' hτ
  have hq : IsAffineQuotient ρ π :=
    ⟨h₂, h₁, fun V ↦ (h₃ V).1, fun V s hs ↦ (h₃ V).2 s fun g _ ↦ (hs g).2⟩
  have hp (g) := (hτ g).2.1
  have f₀ : Flat (𝟙_ (Over X')).hom := inferInstanceAs (Flat (𝟙 X'))
  have f₂ {A B : Over X'} (hA : Flat A.hom) (hB : Flat B.hom) : Flat (A ⊗ B).hom :=
    inferInstanceAs (Flat (pullback.fst A.hom B.hom ≫ A.hom))
  have inj {T : Over X'} (hT : Flat T.hom) {x y : T ⟶ G'} (e : up H x = up H y) : x = y :=
    up_injective hq H hT e
  have ex {T : Over X'} (hT : Flat T.hom) {w : (Over.pullback π).obj T ⟶ G}
      (hw : w ∈ equivariantSubgroup hp T) : ∃ z : T ⟶ G', up H z = w :=
    ((mem_equivariantSubgroup hp).mp hw).exists_up hq H (fun g ↦ (hτ g).1) hT
  have mem {T : Over X'} (z : T ⟶ G') : up H z ∈ equivariantSubgroup hp T :=
    (mem_equivariantSubgroup hp).mpr (equivariant_up H (fun g ↦ (hτ g).1) (fun g ↦ (hp g).1.w) z)
  obtain ⟨m, hm⟩ := ex (f₂ hG' hG') (mul_mem (mem (fst G' G')) (mem (snd G' G')))
  obtain ⟨e, he⟩ := ex f₀ (one_mem _)
  obtain ⟨i, hi⟩ := ex hG' (inv_mem (mem (𝟙 G')))
  have hb (c : O) : ∃ z : G' ⟶ G', up H z = up H (𝟙 G') ≫ a.act c :=
    ex hG' ((mem_equivariantSubgroup hp).mpr fun g s k₁ k₂ ↦ by
      rw [Over.comp_left, Category.assoc, (hτ g).2.2,
        reassoc_of% ((mem_equivariantSubgroup hp).mp (mem (𝟙 G')) g s k₁ k₂)])
  choose b hb using hb
  have hm' {T : Over X'} (u : T ⟶ G' ⊗ G') :
      up H (u ≫ m) = up H (u ≫ fst _ _) * up H (u ≫ snd _ _) := by
    rw [up_comp, hm, MonObj.comp_mul, ← up_comp, ← up_comp]
  have he' {T : Over X'} (u : T ⟶ 𝟙_ _) : up H (u ≫ e) = 1 := by
    rw [up_comp, he, MonObj.comp_one]
  have hb' {T : Over X'} (u : T ⟶ G') (c : O) : up H (u ≫ b c) = up H u ≫ a.act c := by
    rw [up_comp, hb, ← Category.assoc, ← up_comp, Category.comp_id]
  letI : GrpObj G' :=
    { one := e
      mul := m
      one_mul := inj (f₂ f₀ hG') (by
        rw [hm', whiskerRight_fst, he', _root_.one_mul, whiskerRight_snd, leftUnitor_hom])
      mul_one := inj (f₂ hG' f₀) (by
        rw [hm', whiskerLeft_snd, he', _root_.mul_one, whiskerLeft_fst, rightUnitor_hom])
      mul_assoc := inj (f₂ (f₂ hG' hG') hG') (by
        rw [← Category.assoc, hm' (m ▷ G'), hm' (_ ≫ G' ◁ m), whiskerRight_fst, whiskerRight_snd,
          Category.assoc, Category.assoc, whiskerLeft_fst, whiskerLeft_snd, hm' (fst _ _),
          ← Category.assoc _ _ m, hm', Category.assoc, Category.assoc, associator_hom_fst,
          associator_hom_snd_fst, associator_hom_snd_snd, _root_.mul_assoc])
      inv := i
      left_inv := inj hG' (by rw [hm', he', lift_fst, lift_snd, hi, inv_mul_cancel])
      right_inv := inj hG' (by rw [hm', he', lift_fst, lift_snd, hi, mul_inv_cancel]) }
  have hmul {T : Over X'} (x y : T ⟶ G') : up H (x * y) = up H x * up H y := by
    rw [Hom.mul_def]
    exact (hm' _).trans (by rw [lift_fst, lift_snd])
  have : IsCommMonObj G' := ⟨inj (f₂ hG' hG') (by
    refine (hm' _).trans (Eq.trans ?_ hm.symm)
    rw [braiding_hom_fst, braiding_hom_snd, mul_comm])⟩
  let a' : OAct O G' :=
    { act := b
      hom c := by
        have := a.hom c
        refine ⟨inj f₀ ?_, inj (f₂ hG' hG') ?_⟩
        · rw [hb']
          change up H e ≫ _ = up H e
          rw [he, MonObj.one_comp]
        · rw [hb']
          change up H m ≫ _ = up H (_ ≫ m)
          rw [hm', hm, tensorHom_fst, tensorHom_snd, hb', hb', MonObj.mul_comp]
      one := inj hG' (by rw [hb, a.one, Category.comp_id])
      mul c d := inj hG' (by rw [hb', hb, hb, a.mul, Category.assoc])
      add c d := inj hG' (by rw [hmul, hb, hb, hb, a.add, MonObj.comp_mul]) }
  have sec {T : Over X} : ∃ s : T ⟶ (Over.pullback π).obj (Over.mk (T.hom ≫ π)),
      s.left ≫ pullback.fst _ π = 𝟙 T.left :=
    ⟨Over.homMk (pullback.lift (𝟙 T.left) T.hom (Category.id_comp _)) (pullback.lift_snd ..),
      pullback.lift_fst ..⟩
  refine ⟨inferInstance, this, a', ⟨H, fun T x y x₀ y₀ hx hy ↦ ?_⟩, fun c ↦ ?_⟩
  · obtain ⟨s, hs⟩ := sec (T := T)
    have k (z : Over.mk (T.hom ≫ π) ⟶ G') : (s ≫ up H z).left ≫ φ = z.left := by
      rw [Over.comp_left, Category.assoc, up_left, reassoc_of% hs]
    rw [← k, hmul, MonObj.comp_mul, QuotientDescent.hom_ext H ((k x₀).trans hx),
      QuotientDescent.hom_ext H ((k y₀).trans hy)]
  · obtain ⟨s, hs⟩ := sec (T := G)
    have k (z : Over.mk (G.hom ≫ π) ⟶ G') : (s ≫ up H z).left ≫ φ = z.left := by
      rw [Over.comp_left, Category.assoc, up_left, reassoc_of% hs]
    let u : Over.mk (G.hom ≫ π) ⟶ G' := Over.homMk φ H.w
    have hu : s ≫ up H u = 𝟙 G := QuotientDescent.hom_ext H ((k u).trans (Category.id_comp _).symm)
    have := k (u ≫ b c)
    rwa [hb', reassoc_of% hu] at this

end GlobalTheory
