import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsDomainAndIsIntegrallyClosedLocalizationOfIsInv

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.LawDesc

section

variable {R : Type} [CommRing R] [IsLocalRing R] {S : Scheme.{0}} {π : S ⟶ Sp R} {G : Over S} (N : Near π G)

/- English proof (translation)
Take `⟨x₀, h₁, h₂, rfl⟩` from `h`. Take `⟨x₁, h₃, h₄, rfl⟩` from `h'`. Rewrite using `[pullback.hom_ext (h₁.trans h₃.symm) (h₂.trans h₄.symm)]`.
-/
theorem pt_unique {T : Scheme.{0}} {s : T ⟶ S} {a : T ⟶ N.U.left} {x x' : T ⟶ G.left}
    (h : N.Pt s a x) (h' : N.Pt s a x') : x = x' := by
  obtain ⟨x₀, h₁, h₂, rfl⟩ := h
  obtain ⟨x₁, h₃, h₄, rfl⟩ := h'
  rw [pullback.hom_ext (h₁.trans h₃.symm) (h₂.trans h₄.symm)]

/- English proof (translation)
Take `⟨x₀, rfl, -, h₂⟩` from `h`. Take `⟨x₁, rfl, -, h₄⟩` from `h'`. Use `N.isOpen` as an intermediate fact. Rewrite using `[(cancel_mono N.u).1 (h₂.trans h₄.symm)]`.
-/
theorem pt_unique_left {T : Scheme.{0}} {s s' : T ⟶ S} {a a' : T ⟶ N.U.left} {x : T ⟶ G.left}
    (h : N.Pt s a x) (h' : N.Pt s' a' x) : a = a' := by
  obtain ⟨x₀, rfl, -, h₂⟩ := h
  obtain ⟨x₁, rfl, -, h₄⟩ := h'
  have := N.isOpen
  rw [(cancel_mono N.u).1 (h₂.trans h₄.symm)]

/- English proof (translation)
Take `⟨x₀, rfl, rfl, rfl⟩` from `h`. Conclude with `⟨k ≫ x₀, Category.assoc _ _ _, Category.assoc _ _ _, Category.assoc _ _ _⟩`.
-/
theorem pt_comp {T T' : Scheme.{0}} (k : T' ⟶ T) {s : T ⟶ S} {a : T ⟶ N.U.left} {x : T ⟶ G.left}
    (h : N.Pt s a x) : N.Pt (k ≫ s) (k ≫ a) (k ≫ x) := by
  obtain ⟨x₀, rfl, rfl, rfl⟩ := h
  exact ⟨k ≫ x₀, Category.assoc _ _ _, Category.assoc _ _ _, Category.assoc _ _ _⟩

/- English proof (translation)
Take `⟨x₀, rfl, rfl, -⟩` from `h`. Rewrite using `[Category.assoc, Category.assoc, pullback.condition]`.
-/
theorem pt_over {T : Scheme.{0}} {s : T ⟶ S} {a : T ⟶ N.U.left} {x : T ⟶ G.left}
    (h : N.Pt s a x) : s ≫ π = a ≫ N.U.hom := by
  obtain ⟨x₀, rfl, rfl, -⟩ := h
  rw [Category.assoc, Category.assoc, pullback.condition]

/- English proof (translation)
Assemble the required witnesses or components as `⟨Over.homMk (pullback.lift a s h.symm ≫ N.u) (by change (pullback.lift a s h.symm ≫ N.u) ≫ G.hom = s rw [Category.assoc, N.u_over, pullback.lift_snd]), pullback.lift a s h.symm, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _, rfl⟩`.
-/
theorem pt_exists {T : Scheme.{0}} {s : T ⟶ S} {a : T ⟶ N.U.left} (h : s ≫ π = a ≫ N.U.hom) :
    ∃ x : Over.mk s ⟶ G, N.Pt s a x.left :=
  ⟨Over.homMk (pullback.lift a s h.symm ≫ N.u) (by
      change (pullback.lift a s h.symm ≫ N.u) ≫ G.hom = s
      rw [Category.assoc, N.u_over, pullback.lift_snd]),
    pullback.lift a s h.symm, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _, rfl⟩

variable [GrpObj G]

def Prod {T : Scheme.{0}} (s : T ⟶ S) (v : T ⟶ (N.U ⊗ N.U).left) (z : T ⟶ G.left) : Prop :=
  ∃ x y : Over.mk s ⟶ G, N.Pt s (v ≫ (fst N.U N.U).left) x.left ∧ N.Pt s (v ≫ (snd N.U N.U).left) y.left ∧
    (x * y).left = z

/- English proof (translation)
Take `⟨x, hx⟩` from `pt_exists N (s := s) (a := v ≫ (fst N.U N.U).left) (by rw [h, Category.assoc]; exact congrArg (v ≫ ·) (Over.w (fst N.U N.U)).symm)`. Take `⟨y, hy⟩` from `pt_exists N (s := s) (a := v ≫ (snd N.U N.U).left) (by rw [h, Category.assoc]; exact congrArg (v ≫ ·) (Over.w (snd N.U N.U)).symm)`. Conclude with `⟨_, x, y, hx, hy, rfl⟩`.
-/
theorem prod_exists {T : Scheme.{0}} {s : T ⟶ S} {v : T ⟶ (N.U ⊗ N.U).left} (h : s ≫ π = v ≫ (N.U ⊗ N.U).hom) :
    ∃ z, Prod N s v z := by
  obtain ⟨x, hx⟩ := pt_exists N (s := s) (a := v ≫ (fst N.U N.U).left)
    (by rw [h, Category.assoc]; exact congrArg (v ≫ ·) (Over.w (fst N.U N.U)).symm)
  obtain ⟨y, hy⟩ := pt_exists N (s := s) (a := v ≫ (snd N.U N.U).left)
    (by rw [h, Category.assoc]; exact congrArg (v ≫ ·) (Over.w (snd N.U N.U)).symm)
  exact ⟨_, x, y, hx, hy, rfl⟩

/- English proof (translation)
Take `⟨x, y, hx, hy, rfl⟩` from `h`. Take `⟨x', y', hx', hy', rfl⟩` from `h'`. Take `rfl : x = x'` from `Over.OverMorphism.ext (pt_unique N hx hx')`. Take `rfl : y = y'` from `Over.OverMorphism.ext (pt_unique N hy hy')`. Both sides reduce to the same expression.
-/
theorem prod_unique {T : Scheme.{0}} {s : T ⟶ S} {v : T ⟶ (N.U ⊗ N.U).left} {z z' : T ⟶ G.left}
    (h : Prod N s v z) (h' : Prod N s v z') : z = z' := by
  obtain ⟨x, y, hx, hy, rfl⟩ := h
  obtain ⟨x', y', hx', hy', rfl⟩ := h'
  obtain rfl : x = x' := Over.OverMorphism.ext (pt_unique N hx hx')
  obtain rfl : y = y' := Over.OverMorphism.ext (pt_unique N hy hy')
  rfl

/- English proof (translation)
Take `⟨x, y, -, -, rfl⟩` from `h`. Conclude with `Over.w (x * y)`.
-/
theorem prod_over {T : Scheme.{0}} {s : T ⟶ S} {v : T ⟶ (N.U ⊗ N.U).left} {z : T ⟶ G.left}
    (h : Prod N s v z) : z ≫ G.hom = s := by
  obtain ⟨x, y, -, -, rfl⟩ := h
  exact Over.w (x * y)

/- English proof (translation)
Take `⟨x, y, hx, hy, rfl⟩` from `h`. Set `k' : Over.mk (k ≫ s) ⟶ Over.mk s` to `Over.homMk k rfl`. Use `⟨k' ≫ x, k' ≫ y, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Category.assoc]`. Conclude with `pt_comp N k hx`.

Rewrite using `[Category.assoc]`. Conclude with `pt_comp N k hy`. Rewrite using `[← comp_mul]`. Both sides reduce to the same expression.
-/
theorem prod_comp {T T' : Scheme.{0}} (k : T' ⟶ T) {s : T ⟶ S} {v : T ⟶ (N.U ⊗ N.U).left} {z : T ⟶ G.left}
    (h : Prod N s v z) : Prod N (k ≫ s) (k ≫ v) (k ≫ z) := by
  obtain ⟨x, y, hx, hy, rfl⟩ := h
  let k' : Over.mk (k ≫ s) ⟶ Over.mk s := Over.homMk k rfl
  refine ⟨k' ≫ x, k' ≫ y, ?_, ?_, ?_⟩
  · rw [Category.assoc]; exact pt_comp N k hx
  · rw [Category.assoc]; exact pt_comp N k hy
  · rw [← comp_mul]; rfl

/- English proof (translation)
Take `⟨x, y, hx, hy, rfl⟩` from `h`. Establish `hx'` using `hN _ _ _ _ hx`. Establish `hy'` using `hN _ _ _ _ hy`. Take `⟨x₀, hx₀⟩` from `pt_exists N (pt_over N hx')`. Take `⟨y₀, hy₀⟩` from `pt_exists N (pt_over N hy')`.

Conclude with `⟨x₀, y₀, hx₀, hy₀, hφ.2 (Over.mk s) x y x₀ y₀ (pt_unique N hx₀ hx') (pt_unique N hy₀ hy')⟩`.
-/
theorem prod_act {c : S ⟶ S} {φ : G.left ⟶ G.left} (hφ : IsGrpPullback G G c φ)
    (hN : ∀ (T : Scheme.{0}) (s : T ⟶ S) (u : T ⟶ N.U.left) (x : T ⟶ G.left),
      N.Pt s u x → N.Pt (s ≫ c) u (x ≫ φ))
    {T : Scheme.{0}} {s : T ⟶ S} {v : T ⟶ (N.U ⊗ N.U).left} {z : T ⟶ G.left}
    (h : Prod N s v z) : Prod N (s ≫ c) v (z ≫ φ) := by
  obtain ⟨x, y, hx, hy, rfl⟩ := h
  have hx' := hN _ _ _ _ hx
  have hy' := hN _ _ _ _ hy
  obtain ⟨x₀, hx₀⟩ := pt_exists N (pt_over N hx')
  obtain ⟨y₀, hy₀⟩ := pt_exists N (pt_over N hy')
  exact ⟨x₀, y₀, hx₀, hy₀, hφ.2 (Over.mk s) x y x₀ y₀ (pt_unique N hx₀ hx') (pt_unique N hy₀ hy')⟩

/- English proof (translation)
Use `N.smooth` as an intermediate fact. Use `N.isOpen` as an intermediate fact. Establish `hy : Flat (N.U ⊗ N.U).hom`. Express the relevant statement in the definitionally equal form `Flat (pullback.fst N.U.hom N.U.hom ≫ N.U.hom)`. Use `infer_instance`.

Establish `quot : ∀ {Y : Scheme.{0}} (y : Y ⟶ Sp R) [Flat y], IsAffineQuotient (pullbackAction α π hq.comp_eq y) (pullback.snd π y)` using `fun y _ => hq.of_isPullback (IsPullback.of_hasPullback π y) (pullbackAction_fst α π hq.comp_eq y) (pullbackAction_snd α π hq.comp_eq y)`. Establish `equiv : ∀ {Y : Scheme.{0}} (y : Y ⟶ Sp R) (j : Y ⟶ (N.U ⊗ N.U).left) (z : pullback π y ⟶ G.left), Prod N (pullback.fst π y) (pullback.snd π y ≫ j) z → ∀ g, (pullbackAction α π hq.comp_eq y g).hom ≫ z = z ≫ φ g` using `fun y j z hz g => by`. Establish `h₁` using `prod_comp N (pullbackAction α π hq.comp_eq y g).hom hz`. Rewrite `h₁` using `[pullbackAction_fst, pullbackAction_snd_assoc]`. Conclude with `prod_unique N h₁ (prod_act N (hφ g) (hN g) hz)`.

Take `⟨z₀, hz₁⟩` from `prod_exists N (pullback.condition (f := π) (g := (N.U ⊗ N.U).hom))`. Establish `hrange : ∀ g, pullback.map N.U.hom π N.U.hom π (𝟙 _) (α g).hom (𝟙 _) (by simp) (by simp [hq.comp_eq]) ≫ N.u = N.u ≫ φ g` using `fun g => by`. Use `pt_unique N (s := pullback.snd N.U.hom π ≫ (α g).hom) (a := pullback.fst N.U.hom π) ⟨_, ?_, pullback.lift_snd _ _ _, rfl⟩ (hN g _ _ _ _ ⟨𝟙 _, Category.id_comp _, Category.id_comp _, Category.id_comp _⟩)` and prove the remaining obligations. Conclude with `(pullback.lift_fst _ _ _).trans (Category.comp_id _)`. Take `⟨V, hV⟩` from `(quot (N.U ⊗ N.U).hom).exists_preimage_eq (U := z₀ ⁻¹ᵁ N.u.opensRange) fun g w hw => by`.

Take `⟨w', hw'⟩` from `hw`. Express the relevant statement in the definitionally equal form `((pullbackAction α π hq.comp_eq (N.U ⊗ N.U).hom g).hom ≫ z₀) w ∈ Set.range N.u`. Rewrite using `[equiv _ (𝟙 _) z₀ (by rw [Category.comp_id]; exact hz₁) g, Scheme.Hom.comp_apply, ← hw', ← Scheme.Hom.comp_apply, ← hrange g, Scheme.Hom.comp_apply]`. Conclude with `⟨_, rfl⟩`. Set `y : V.toScheme ⟶ Sp R` to `V.ι ≫ (N.U ⊗ N.U).hom`.

Set `k : pullback π y ⟶ pullback π (N.U ⊗ N.U).hom` to `pullback.lift (pullback.fst π y) (pullback.snd π y ≫ V.ι) (by rw [pullback.condition, Category.assoc])`. Establish `hk : k ≫ pullback.snd _ _ = pullback.snd π y ≫ V.ι` using `pullback.lift_snd _ _ _`. Establish `hz : Prod N (pullback.fst π y) (pullback.snd π y ≫ V.ι) (k ≫ z₀)`. Use `prod_comp N k hz₁` as an intermediate fact. Rewrite `this` using `[hk, pullback.lift_fst]`. Then use the resulting hypothesis.

Establish `hsub : Set.range (k ≫ z₀) ⊆ Set.range N.u`. Introduce and unpack `_ ⟨w, rfl⟩`. Establish `: k w ∈ pullback.snd π (N.U ⊗ N.U).hom ⁻¹ᵁ V`. Express the relevant statement in the definitionally equal form `(k ≫ pullback.snd π (N.U ⊗ N.U).hom) w ∈ V`. Rewrite using `[hk, Scheme.Hom.comp_apply]`.

Conclude with `(pullback.snd π y w).2`. Rewrite `this` using `[hV]`. Conclude with `this`. Set `l` to `IsOpenImmersion.lift N.u (k ≫ z₀) hsub`. Establish `hl : l ≫ N.u = k ≫ z₀` using `IsOpenImmersion.lift_fac _ _ _`.

Establish `hf : N.Pt (pullback.fst π y) (l ≫ pullback.fst _ _) (k ≫ z₀)` using `⟨l, rfl, by rw [← N.u_over, ← Category.assoc, hl, prod_over N hz], hl⟩`. Take `⟨m, hm⟩` from `(quot y).exists_comp_eq (l ≫ pullback.fst _ _) fun g => by`. Establish `h₁` using `pt_comp N (pullbackAction α π hq.comp_eq y g).hom hf`. Rewrite `h₁` using `[equiv y V.ι _ hz g]`. Conclude with `pt_unique_left N h₁ (hN g _ _ _ _ hf)`.

Use `⟨V, m, fun z hz₀ => ?_, (quot y).hom_ext ?_, fun T v s a b ha hb => ?_⟩` and prove the remaining obligations. Take `⟨w, rfl⟩` from `(quot (N.U ⊗ N.U).hom).surjective.surj z`. Express the relevant statement in the definitionally equal form `w ∈ pullback.snd π (N.U ⊗ N.U).hom ⁻¹ᵁ V`. Rewrite using `[hV]`. Use `N.all (z₀ w) ?_` and prove the remaining obligations.

Rewrite using `[← hz₀, ← Scheme.Hom.comp_apply z₀, prod_over N hz₁, ← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]`. Rewrite using `[← Category.assoc, hm, ← pt_over N hf, pullback.condition]`. Establish `hs : s ≫ π = v ≫ y`. Rewrite using `[pt_over N ha, Category.assoc, Category.assoc]`. Conclude with `congrArg (fun t => v ≫ V.ι ≫ t) (Over.w (fst N.U N.U))`.

Establish `h₁` using `pt_comp N (pullback.lift s v hs) hf`. Establish `h₂` using `prod_comp N (pullback.lift s v hs) hz`. Rewrite `h₂` using `[pullback.lift_fst, pullback.lift_snd_assoc]`. Establish `h₃ : Prod N s (v ≫ V.ι) (a * b).left` using `⟨a, b, by rw [Category.assoc]; exact ha, by rw [Category.assoc]; exact hb, rfl⟩`. Rewrite `h₁` using `[← hm, pullback.lift_fst, pullback.lift_snd_assoc, prod_unique N h₂ h₃]`.

Conclude with `h₁`.
-/
theorem law_of_isAffineQuotient {Γ : Type} [Group Γ] [Finite Γ] {α : Γ →* Aut S} (hq : IsAffineQuotient α π)
    (φ : Γ → (G.left ⟶ G.left)) (hφ : ∀ g, IsGrpPullback G G (α g).hom (φ g))
    (hN : ∀ g (T : Scheme.{0}) (s : T ⟶ S) (u : T ⟶ N.U.left) (x : T ⟶ G.left),
      N.Pt s u x → N.Pt (s ≫ (α g).hom) u (x ≫ φ g)) : N.Law := by
  have := N.smooth
  have := N.isOpen
  have hy : Flat (N.U ⊗ N.U).hom := by
    change Flat (pullback.fst N.U.hom N.U.hom ≫ N.U.hom)
    infer_instance
  have quot : ∀ {Y : Scheme.{0}} (y : Y ⟶ Sp R) [Flat y],
      IsAffineQuotient (pullbackAction α π hq.comp_eq y) (pullback.snd π y) := fun y _ =>
    hq.of_isPullback (IsPullback.of_hasPullback π y) (pullbackAction_fst α π hq.comp_eq y)
      (pullbackAction_snd α π hq.comp_eq y)
  have equiv : ∀ {Y : Scheme.{0}} (y : Y ⟶ Sp R) (j : Y ⟶ (N.U ⊗ N.U).left) (z : pullback π y ⟶ G.left),
      Prod N (pullback.fst π y) (pullback.snd π y ≫ j) z →
      ∀ g, (pullbackAction α π hq.comp_eq y g).hom ≫ z = z ≫ φ g := fun y j z hz g => by
    have h₁ := prod_comp N (pullbackAction α π hq.comp_eq y g).hom hz
    rw [pullbackAction_fst, pullbackAction_snd_assoc] at h₁
    exact prod_unique N h₁ (prod_act N (hφ g) (hN g) hz)
  obtain ⟨z₀, hz₁⟩ := prod_exists N (pullback.condition (f := π) (g := (N.U ⊗ N.U).hom))
  have hrange : ∀ g, pullback.map N.U.hom π N.U.hom π (𝟙 _) (α g).hom (𝟙 _) (by simp) (by simp [hq.comp_eq]) ≫ N.u
      = N.u ≫ φ g := fun g => by
    refine pt_unique N (s := pullback.snd N.U.hom π ≫ (α g).hom) (a := pullback.fst N.U.hom π)
      ⟨_, ?_, pullback.lift_snd _ _ _, rfl⟩
      (hN g _ _ _ _ ⟨𝟙 _, Category.id_comp _, Category.id_comp _, Category.id_comp _⟩)
    exact (pullback.lift_fst _ _ _).trans (Category.comp_id _)
  obtain ⟨V, hV⟩ := (quot (N.U ⊗ N.U).hom).exists_preimage_eq (U := z₀ ⁻¹ᵁ N.u.opensRange) fun g w hw => by
    obtain ⟨w', hw'⟩ := hw
    change ((pullbackAction α π hq.comp_eq (N.U ⊗ N.U).hom g).hom ≫ z₀) w ∈ Set.range N.u
    rw [equiv _ (𝟙 _) z₀ (by rw [Category.comp_id]; exact hz₁) g, Scheme.Hom.comp_apply, ← hw',
      ← Scheme.Hom.comp_apply, ← hrange g, Scheme.Hom.comp_apply]
    exact ⟨_, rfl⟩
  let y : V.toScheme ⟶ Sp R := V.ι ≫ (N.U ⊗ N.U).hom
  let k : pullback π y ⟶ pullback π (N.U ⊗ N.U).hom :=
    pullback.lift (pullback.fst π y) (pullback.snd π y ≫ V.ι) (by rw [pullback.condition, Category.assoc])
  have hk : k ≫ pullback.snd _ _ = pullback.snd π y ≫ V.ι := pullback.lift_snd _ _ _
  have hz : Prod N (pullback.fst π y) (pullback.snd π y ≫ V.ι) (k ≫ z₀) := by
    have := prod_comp N k hz₁
    rwa [hk, pullback.lift_fst] at this
  have hsub : Set.range (k ≫ z₀) ⊆ Set.range N.u := by
    rintro _ ⟨w, rfl⟩
    have : k w ∈ pullback.snd π (N.U ⊗ N.U).hom ⁻¹ᵁ V := by
      change (k ≫ pullback.snd π (N.U ⊗ N.U).hom) w ∈ V
      rw [hk, Scheme.Hom.comp_apply]
      exact (pullback.snd π y w).2
    rw [hV] at this
    exact this
  let l := IsOpenImmersion.lift N.u (k ≫ z₀) hsub
  have hl : l ≫ N.u = k ≫ z₀ := IsOpenImmersion.lift_fac _ _ _
  have hf : N.Pt (pullback.fst π y) (l ≫ pullback.fst _ _) (k ≫ z₀) :=
    ⟨l, rfl, by rw [← N.u_over, ← Category.assoc, hl, prod_over N hz], hl⟩
  obtain ⟨m, hm⟩ := (quot y).exists_comp_eq (l ≫ pullback.fst _ _) fun g => by
    have h₁ := pt_comp N (pullbackAction α π hq.comp_eq y g).hom hf
    rw [equiv y V.ι _ hz g] at h₁
    exact pt_unique_left N h₁ (hN g _ _ _ _ hf)
  refine ⟨V, m, fun z hz₀ => ?_, (quot y).hom_ext ?_, fun T v s a b ha hb => ?_⟩
  · obtain ⟨w, rfl⟩ := (quot (N.U ⊗ N.U).hom).surjective.surj z
    change w ∈ pullback.snd π (N.U ⊗ N.U).hom ⁻¹ᵁ V
    rw [hV]
    refine N.all (z₀ w) ?_
    rw [← hz₀, ← Scheme.Hom.comp_apply z₀, prod_over N hz₁, ← Scheme.Hom.comp_apply, pullback.condition,
      Scheme.Hom.comp_apply]
  · rw [← Category.assoc, hm, ← pt_over N hf, pullback.condition]
  · have hs : s ≫ π = v ≫ y := by
      rw [pt_over N ha, Category.assoc, Category.assoc]
      exact congrArg (fun t => v ≫ V.ι ≫ t) (Over.w (fst N.U N.U))
    have h₁ := pt_comp N (pullback.lift s v hs) hf
    have h₂ := prod_comp N (pullback.lift s v hs) hz
    rw [pullback.lift_fst, pullback.lift_snd_assoc] at h₂
    have h₃ : Prod N s (v ≫ V.ι) (a * b).left :=
      ⟨a, b, by rw [Category.assoc]; exact ha, by rw [Category.assoc]; exact hb, rfl⟩
    rw [← hm, pullback.lift_fst, pullback.lift_snd_assoc, prod_unique N h₂ h₃] at h₁
    exact h₁

end

end GlobalTheory.Mum.LawDesc

namespace GlobalTheory.Mum

/- English proof (translation)
Introduce `R _ _ _ _ R' _ _ _ ρ hρ hG D D' hD A' G' _ _ _ U' a N hN`. Use `hG.1` as an intermediate fact. Set `_ : Algebra R R'` to `ρ.toAlgebra`. Set `_ : MulSemiringAction (R' ≃+* R') R'` to `RingAut.applyMulSemiringAction`. Set `_ : MulSemiringAction (Gal ρ) R'` to `Subgroup.mulSemiringAction _`.

Establish `: SMulCommClass (Gal ρ) R R'` using `⟨fun σ r x => by`. Express the relevant statement in the definitionally equal form `σ.1 (ρ r * x) = ρ r * σ.1 x`. Rewrite using `[map_mul, σ.2 r]⟩`. Establish `: FaithfulSMul R R'` using `(faithfulSMul_iff_algebraMap_injective _ _).2 hρ.2.1`. Establish `: Algebra.IsInvariant R R' (Gal ρ)` using `⟨fun x hx => hG.2 x fun σ hσ => hx ⟨σ, hσ⟩⟩`.

Establish `hq : IsAffineQuotient (specAction (Gal ρ) R') (spMap ρ)` using `isAffineQuotient_spec R R'`. Establish `e : ∀ σ : Gal ρ, (specAction (Gal ρ) R' σ).hom = spMap (Gal.hom σ⁻¹)` using `fun σ => by`. Rewrite using `[specAction_hom]`. Both sides reduce to the same expression. Use `LawDesc.law_of_isAffineQuotient N hq (fun σ => a.act σ⁻¹) (fun σ => ?_) fun σ => ?_` and prove the remaining obligations.

Rewrite using `[e]`. Conclude with `a.cart σ⁻¹`. Rewrite using `[e]`. Conclude with `hN σ⁻¹`.
-/
theorem law_of_galAct_invariant : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → IsGal ρ → ∀ (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R') D' A' G') (a : GalAct ρ hD U'), ∀ N : Near (spMap ρ) G', (∀ σ (T : Scheme.{0}) (s : T ⟶ Sp R') (u : T ⟶ N.U.left) (x : T ⟶ G'.left), N.Pt s u x → N.Pt (s ≫ spMap (Gal.hom σ)) u (x ≫ a.act σ)) → N.Law := by
  intro R _ _ _ _ R' _ _ _ ρ hρ hG D D' hD A' G' _ _ _ U' a N hN
  have := hG.1
  let _ : Algebra R R' := ρ.toAlgebra
  let _ : MulSemiringAction (R' ≃+* R') R' := RingAut.applyMulSemiringAction
  let _ : MulSemiringAction (Gal ρ) R' := Subgroup.mulSemiringAction _
  have : SMulCommClass (Gal ρ) R R' := ⟨fun σ r x => by
    change σ.1 (ρ r * x) = ρ r * σ.1 x
    rw [map_mul, σ.2 r]⟩
  have : FaithfulSMul R R' := (faithfulSMul_iff_algebraMap_injective _ _).2 hρ.2.1
  have : Algebra.IsInvariant R R' (Gal ρ) := ⟨fun x hx => hG.2 x fun σ hσ => hx ⟨σ, hσ⟩⟩
  have hq : IsAffineQuotient (specAction (Gal ρ) R') (spMap ρ) := isAffineQuotient_spec R R'
  have e : ∀ σ : Gal ρ, (specAction (Gal ρ) R' σ).hom = spMap (Gal.hom σ⁻¹) := fun σ => by
    rw [specAction_hom]; rfl
  refine LawDesc.law_of_isAffineQuotient N hq (fun σ => a.act σ⁻¹) (fun σ => ?_) fun σ => ?_
  · rw [e]; exact a.cart σ⁻¹
  · rw [e]; exact hN σ⁻¹

end GlobalTheory.Mum
