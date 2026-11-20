import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFlagFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TorsionFlatLocallyQuasiFiniteStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSectionOfIsIntegralHom
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsUniversalTorsionPairPolAV

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.LineNorm MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SplitFinitePart

structure IsTorsionOver {X S Z : Scheme.{0}} (G : Over X) [GrpObj G] (x : S ⟶ X) (q : ℕ) (π : Z ⟶ S)
    (κ : Over.mk (π ≫ x) ⟶ G) : Prop where
  pow : κ ^ q = 1
  lift : ∀ (T : Over X) (w : T ⟶ G) (c : T.left ⟶ S), c ≫ x = T.hom → w ^ q = 1 →
    ∃ z : T.left ⟶ Z, z ≫ π = c ∧ z ≫ κ.left = w.left
  ext : ∀ (T : Scheme.{0}) (z z' : T ⟶ Z), z ≫ π = z' ≫ π → z ≫ κ.left = z' ≫ κ.left → z = z'

/- English proof (translation)
Rewrite using `[← MonObj.comp_pow, (LamF.torsion_universal G q).1, MonObj.comp_one] lift T w c hc hw := by`. Take `⟨w', rfl⟩` from `(LamF.torsion_universal G q).2 T w hw`. Use `⟨pullback.lift w'.left c ((Over.w w').trans hc.symm), pullback.lift_snd _ _ _, ?_⟩` and prove the remaining obligations. Conclude with `pullback.lift_fst_assoc _ _ _ _`. Use extensionality with `T z z' h h' := by`.

Establish `: Mono (torsion.ι G q)` using `inferInstanceAs (Mono (pullback.fst _ _))`. Establish `: Mono (torsion.ι G q).left` using `inferInstanceAs (Mono ((Over.forget X).map (torsion.ι G q)))`. Use `pullback.hom_ext ?_ h` and prove the remaining obligations. Rewrite using `[← cancel_mono (torsion.ι G q).left]`. Simplify using `using h'`.
-/
theorem isTorsionOver {X S : Scheme.{0}} (G : Over X) [GrpObj G] (x : S ⟶ X) (q : ℕ) :
    IsTorsionOver G x q (pullback.snd (torsion G q).hom x)
      (Over.homMk (pullback.fst (torsion G q).hom x) pullback.condition ≫ torsion.ι G q) where
  pow := by rw [← MonObj.comp_pow, (LamF.torsion_universal G q).1, MonObj.comp_one]
  lift T w c hc hw := by
    obtain ⟨w', rfl⟩ := (LamF.torsion_universal G q).2 T w hw
    refine ⟨pullback.lift w'.left c ((Over.w w').trans hc.symm), pullback.lift_snd _ _ _, ?_⟩
    exact pullback.lift_fst_assoc _ _ _ _
  ext T z z' h h' := by
    have : Mono (torsion.ι G q) := inferInstanceAs (Mono (pullback.fst _ _))
    have : Mono (torsion.ι G q).left := inferInstanceAs (Mono ((Over.forget X).map (torsion.ι G q)))
    refine pullback.hom_ext ?_ h
    rw [← cancel_mono (torsion.ι G q).left]
    simpa using h'

variable {X S Z : Scheme.{0}} {G : Over X} [GrpObj G] {x : S ⟶ X} {q : ℕ} {π : Z ⟶ S} {κ : Over.mk (π ≫ x) ⟶ G}

/- English proof (translation)
Establish `h1 : z ≫ π ≫ x = T.hom`. Rewrite using `[← Over.w w, ← hz, Category.assoc, Over.w κ]`. Both sides reduce to the same expression. Establish `h2 : w = (Over.homMk z h1 : T ⟶ Over.mk (π ≫ x)) ≫ κ` using `Over.OverMorphism.ext hz.symm`. Rewrite using `[h2, ← MonObj.comp_pow, h.pow, MonObj.comp_one]`.
-/
theorem IsTorsionOver.pow_eq_one (h : IsTorsionOver G x q π κ) {T : Over X} (w : T ⟶ G) (z : T.left ⟶ Z)
    (hz : z ≫ κ.left = w.left) : w ^ q = 1 := by
  have h1 : z ≫ π ≫ x = T.hom := by
    rw [← Over.w w, ← hz, Category.assoc, Over.w κ]; rfl
  have h2 : w = (Over.homMk z h1 : T ⟶ Over.mk (π ≫ x)) ≫ κ := Over.OverMorphism.ext hz.symm
  rw [h2, ← MonObj.comp_pow, h.pow, MonObj.comp_one]

/- English proof (translation)
Take `⟨e, he, he'⟩` from `h.lift (Over.mk x) 1 (𝟙 S) (Category.id_comp _) (one_pow _)`. Use `⟨e ⁻¹ᵁ H, hH _ (by rw [← Scheme.Hom.comp_apply, he]; rfl), fun T z hz s hs => ?_⟩` and prove the remaining obligations. Establish `h1 : (z ≫ π) ≫ x = T.hom`. Rewrite using `[← Over.w (1 : T ⟶ G), ← hz, Category.assoc, Category.assoc, Over.w κ]`. Both sides reduce to the same expression.

Establish `h2 : z = (z ≫ π) ≫ e`. Use `h.ext _ _ _ (by rw [Category.assoc (z ≫ π), he]; exact (Category.comp_id _).symm) ?_` and prove the remaining obligations. Rewrite using `[Category.assoc (z ≫ π), he', hz, ← MonObj.comp_one (Over.homMk (z ≫ π) h1 : T ⟶ Over.mk x)]`. Both sides reduce to the same expression. Rewrite using `[h2]`.

Conclude with `hs`.
-/
theorem IsTorsionOver.exists_open_one (h : IsTorsionOver G x q π κ) (p : S) (H : Z.Opens)
    (hH : ∀ z : Z, π z = p → z ∈ H) : ∃ W : S.Opens, p ∈ W ∧ ∀ (T : Over X) (z : T.left ⟶ Z),
      z ≫ κ.left = (1 : T ⟶ G).left → ∀ s, π (z s) ∈ W → z s ∈ H := by
  obtain ⟨e, he, he'⟩ := h.lift (Over.mk x) 1 (𝟙 S) (Category.id_comp _) (one_pow _)
  refine ⟨e ⁻¹ᵁ H, hH _ (by rw [← Scheme.Hom.comp_apply, he]; rfl), fun T z hz s hs => ?_⟩
  have h1 : (z ≫ π) ≫ x = T.hom := by
    rw [← Over.w (1 : T ⟶ G), ← hz, Category.assoc, Category.assoc, Over.w κ]; rfl
  have h2 : z = (z ≫ π) ≫ e := by
    refine h.ext _ _ _ (by rw [Category.assoc (z ≫ π), he]; exact (Category.comp_id _).symm) ?_
    rw [Category.assoc (z ≫ π), he', hz, ← MonObj.comp_one (Over.homMk (z ≫ π) h1 : T ⟶ Over.mk x)]
    rfl
  rw [h2]
  exact hs

/- English proof (translation)
Set `c : pullback ρ ρ ⟶ S` to `(pullback.fst ρ ρ ≫ ρ) ≫ W.ι`. Set `P : Over X` to `Over.mk (c ≫ x)`. Set `a : P ⟶ G` to `(Over.homMk (pullback.fst ρ ρ ≫ H.ι) (by`. Simplify using `only [P, c, Over.mk_hom, Category.assoc, reassoc_of% hρ]) : P ⟶ Over.mk (π ≫ x)) ≫ κ`. Set `b : P ⟶ G` to `(Over.homMk (pullback.snd ρ ρ ≫ H.ι) (by`.

Simplify using `only [P, c, Over.mk_hom, Category.assoc, pullback.condition_assoc, reassoc_of% hρ]) : P ⟶ Over.mk (π ≫ x)) ≫ κ`. Establish `hab : (a * b) ^ q = 1`. Rewrite using `[mul_pow, h.pow_eq_one a (pullback.fst ρ ρ ≫ H.ι) rfl, h.pow_eq_one b (pullback.snd ρ ρ ≫ H.ι) rfl, _root_.mul_one]`. Take `⟨m, hm, hm'⟩` from `h.lift P (a * b) c rfl hab`. Establish `hc : ∀ y : ↥(pullback ρ ρ), ((pullback.fst ρ ρ ≫ ρ) y).1 = π (m y)` using `fun y => (congrArg (fun φ : pullback ρ ρ ⟶ S => φ y) hm).symm`.

Take `⟨W', hW', hm''⟩` from `exists_open_fibres_subset W (pullback.fst ρ ρ ≫ ρ) (m ⁻¹ᵁ H) p hp fun y hy => hH _ ((hc y).symm.trans hy)`. Use `⟨W', hW', fun T w w' z z' z'' hz hz' hz'' e' e'' hzH hzH' s hs => ?_⟩` and prove the remaining obligations. Establish `r : Set.range z ⊆ Set.range H.ι`. Rewrite using `[Scheme.Opens.range_ι]`. Introduce and unpack `_ ⟨s, rfl⟩`.

Conclude with `hzH s`. Establish `r' : Set.range z' ⊆ Set.range H.ι`. Rewrite using `[Scheme.Opens.range_ι]`. Introduce and unpack `_ ⟨s, rfl⟩`. Conclude with `hzH' s`.

Establish `f` using `IsOpenImmersion.lift_fac H.ι z r`. Establish `f'` using `IsOpenImmersion.lift_fac H.ι z' r'`. Set `l : T.left ⟶ pullback ρ ρ` to `pullback.lift (IsOpenImmersion.lift H.ι z r) (IsOpenImmersion.lift H.ι z' r') (by`. Rewrite using `[← cancel_mono W.ι, Category.assoc, Category.assoc, hρ, reassoc_of% f, reassoc_of% f', e'])`. Establish `l1 : l ≫ pullback.fst ρ ρ ≫ H.ι = z` using `by rw [pullback.lift_fst_assoc, f]`.

Establish `l2 : l ≫ pullback.snd ρ ρ ≫ H.ι = z'` using `by rw [pullback.lift_snd_assoc, f']`. Establish `lc : l ≫ c = z ≫ π`. Rewrite using `[← l1]`. Simplify using `only [c, Category.assoc, hρ]`. Establish `lx : l ≫ c ≫ x = T.hom`.

Rewrite using `[reassoc_of% lc, ← Over.w w, ← hz, Category.assoc, Over.w κ]`. Both sides reduce to the same expression. Set `L : T ⟶ P` to `Over.homMk l lx`. Establish `La : L ≫ a = w` using `Over.OverMorphism.ext (by`. Rewrite using `[← hz, ← l1]`.

Simplify using `[L, a])`. Establish `Lb : L ≫ b = w'` using `Over.OverMorphism.ext (by`. Rewrite using `[← hz', ← l2]`. Simplify using `[L, b])`. Establish `key : z'' = l ≫ m`.

Use `h.ext _ _ _ (by rw [e'', ← lc, ← hm]; exact (Category.assoc _ _ _).symm) ?_` and prove the remaining obligations. Rewrite using `[hz'', ← La, ← Lb, ← MonObj.comp_mul, Category.assoc]`. Conclude with `congrArg (l ≫ ·) hm'.symm`. Rewrite using `[key]`. Use `hm'' (l s) ?_` and prove the remaining obligations.

Rewrite using `[hc]`. Express the relevant statement in the definitionally equal form `((l ≫ m) ≫ π) s ∈ W'`. Rewrite using `[← key, e'']`. Conclude with `hs`.
-/
theorem IsTorsionOver.exists_open_mul [IsCommMonObj G] (h : IsTorsionOver G x q π κ) (p : S) (W : S.Opens)
    (H : Z.Opens) (ρ : H.toScheme ⟶ W.toScheme) (hp : p ∈ W) (hρ : ρ ≫ W.ι = H.ι ≫ π) [IsFinite ρ]
    (hH : ∀ z : Z, π z = p → z ∈ H) : ∃ W' : S.Opens, p ∈ W' ∧ ∀ (T : Over X) (w w' : T ⟶ G)
      (z z' z'' : T.left ⟶ Z), z ≫ κ.left = w.left → z' ≫ κ.left = w'.left → z'' ≫ κ.left = (w * w').left →
      z' ≫ π = z ≫ π → z'' ≫ π = z ≫ π → (∀ s, z s ∈ H) → (∀ s, z' s ∈ H) → ∀ s, π (z s) ∈ W' → z'' s ∈ H := by
  let c : pullback ρ ρ ⟶ S := (pullback.fst ρ ρ ≫ ρ) ≫ W.ι
  let P : Over X := Over.mk (c ≫ x)
  let a : P ⟶ G := (Over.homMk (pullback.fst ρ ρ ≫ H.ι) (by
    simp only [P, c, Over.mk_hom, Category.assoc, reassoc_of% hρ]) : P ⟶ Over.mk (π ≫ x)) ≫ κ
  let b : P ⟶ G := (Over.homMk (pullback.snd ρ ρ ≫ H.ι) (by
    simp only [P, c, Over.mk_hom, Category.assoc, pullback.condition_assoc, reassoc_of% hρ]) :
      P ⟶ Over.mk (π ≫ x)) ≫ κ
  have hab : (a * b) ^ q = 1 := by
    rw [mul_pow, h.pow_eq_one a (pullback.fst ρ ρ ≫ H.ι) rfl, h.pow_eq_one b (pullback.snd ρ ρ ≫ H.ι) rfl, _root_.mul_one]
  obtain ⟨m, hm, hm'⟩ := h.lift P (a * b) c rfl hab
  have hc : ∀ y : ↥(pullback ρ ρ), ((pullback.fst ρ ρ ≫ ρ) y).1 = π (m y) := fun y =>
    (congrArg (fun φ : pullback ρ ρ ⟶ S => φ y) hm).symm
  obtain ⟨W', hW', hm''⟩ := exists_open_fibres_subset W (pullback.fst ρ ρ ≫ ρ) (m ⁻¹ᵁ H) p hp
    fun y hy => hH _ ((hc y).symm.trans hy)
  refine ⟨W', hW', fun T w w' z z' z'' hz hz' hz'' e' e'' hzH hzH' s hs => ?_⟩
  have r : Set.range z ⊆ Set.range H.ι := by
    rw [Scheme.Opens.range_ι]; rintro _ ⟨s, rfl⟩; exact hzH s
  have r' : Set.range z' ⊆ Set.range H.ι := by
    rw [Scheme.Opens.range_ι]; rintro _ ⟨s, rfl⟩; exact hzH' s
  have f := IsOpenImmersion.lift_fac H.ι z r
  have f' := IsOpenImmersion.lift_fac H.ι z' r'
  let l : T.left ⟶ pullback ρ ρ := pullback.lift (IsOpenImmersion.lift H.ι z r) (IsOpenImmersion.lift H.ι z' r') (by
    rw [← cancel_mono W.ι, Category.assoc, Category.assoc, hρ, reassoc_of% f, reassoc_of% f', e'])
  have l1 : l ≫ pullback.fst ρ ρ ≫ H.ι = z := by rw [pullback.lift_fst_assoc, f]
  have l2 : l ≫ pullback.snd ρ ρ ≫ H.ι = z' := by rw [pullback.lift_snd_assoc, f']
  have lc : l ≫ c = z ≫ π := by
    rw [← l1]; simp only [c, Category.assoc, hρ]
  have lx : l ≫ c ≫ x = T.hom := by
    rw [reassoc_of% lc, ← Over.w w, ← hz, Category.assoc, Over.w κ]; rfl
  let L : T ⟶ P := Over.homMk l lx
  have La : L ≫ a = w := Over.OverMorphism.ext (by
    rw [← hz, ← l1]; simp [L, a])
  have Lb : L ≫ b = w' := Over.OverMorphism.ext (by
    rw [← hz', ← l2]; simp [L, b])
  have key : z'' = l ≫ m := by
    refine h.ext _ _ _ (by rw [e'', ← lc, ← hm]; exact (Category.assoc _ _ _).symm) ?_
    rw [hz'', ← La, ← Lb, ← MonObj.comp_mul, Category.assoc]
    exact congrArg (l ≫ ·) hm'.symm
  rw [key]
  refine hm'' (l s) ?_
  rw [hc]
  change ((l ≫ m) ≫ π) s ∈ W'
  rw [← key, e'']
  exact hs

/- English proof (translation)
Take `⟨Ω, _, y, o, hy⟩ : ∃ (Ω : Type) (_ : Field Ω) (y : Sp Ω ⟶ Z) (o : Sp Ω), y o = z` from `⟨Z.residueField z, inferInstance, Z.fromSpecResidueField z, IsLocalRing.closedPoint _, Scheme.fromSpecResidueField_apply z _⟩`. Take `⟨φ, hφ⟩` from `Spec.map_surjective (y ≫ π)`. Establish `hinj : Function.Injective φ.hom`. Rewrite using `[RingHom.injective_iff_ker_eq_bot, eq_bot_iff]`. Introduce `a ha`.

Establish `h1 : Spec.map φ o = genericPoint (Sp R)` using `by rw [hφ, Scheme.Hom.comp_apply, hy, hz]`. Rewrite `h1` using `[genericPoint_eq_bot_of_affine]`. Establish `h2 : a ∈ (Spec.map φ o).asIdeal`. Express the relevant statement in the definitionally equal form `φ.hom a ∈ o.asIdeal`. Rewrite using `[RingHom.mem_ker.mp ha]`.

Conclude with `zero_mem _`. Rewrite `h2` using `[h1]`. Conclude with `h2`. Set `io : FractionRing R →+* Ω` to `IsFractionRing.lift hinj`. Establish `hio : spMap (io.comp (algebraMap R (FractionRing R))) = y ≫ π`.

Rewrite using `[← hφ, show io.comp (algebraMap R (FractionRing R)) = φ.hom from RingHom.ext fun a => IsFractionRing.lift_algebraMap hinj a]`. Both sides reduce to the same expression. Establish `hio' : spMap io ≫ spMap (algebraMap R (FractionRing R)) = y ≫ π`. Rewrite using `[← hio, ← Spec.map_comp]`. Both sides reduce to the same expression.

Set `w : Over.mk (spMap (io.comp (algebraMap R (FractionRing R))) ≫ x) ⟶ t.G` to `(Over.homMk y (by rw [hio]; simp) : _ ⟶ Over.mk (π ≫ x)) ≫ κ`. Establish `hw : w ^ q = 1` using `h.pow_eq_one w y rfl`. Take `⟨w₀, hw₀⟩` from `hs Ω io w hw`. Use `epi_spMap io` as an intermediate fact. Establish `h0 : w₀ ≫ t.G.hom = spMap (algebraMap R (FractionRing R)) ≫ x`.

Rewrite using `[← cancel_epi (spMap io), reassoc_of% hw₀, reassoc_of% hio', Over.w w, ← Category.assoc, ← hio]`. Both sides reduce to the same expression. Set `w₁ : Over.mk (spMap (algebraMap R (FractionRing R)) ≫ x) ⟶ t.G` to `Over.homMk w₀ h0`. Set `i : Over.mk (spMap (io.comp (algebraMap R (FractionRing R))) ≫ x) ⟶ Over.mk (spMap (algebraMap R (FractionRing R)) ≫ x)` to `Over.homMk (spMap io) (by`. Rewrite using `[hio]`.

Simplify using `[reassoc_of% hio'])`. Establish `hi : i ≫ w₁ = w` using `Over.OverMorphism.ext hw₀`. Establish `hw₁ : w₁ ^ q = 1`. Establish `: i ≫ w₁ ^ q = i ≫ 1` using `by rw [MonObj.comp_pow, hi, hw, MonObj.comp_one]`. Conclude with `Over.OverMorphism.ext ((cancel_epi (spMap io)).mp (congrArg Over.Hom.left this))`.

Take `⟨g₀, hg₀, hg₀'⟩` from `h.lift _ w₁ (spMap (algebraMap R (FractionRing R))) rfl hw₁`. Establish `e : spMap io ≫ g₀ = y` using `h.ext _ _ _ ((Category.assoc _ _ _).trans ((congrArg (spMap io ≫ ·) hg₀).trans hio')) ((Category.assoc _ _ _).trans ((congrArg (spMap io ≫ ·) hg₀').trans hw₀))`. Conclude with `⟨g₀, hg₀, spMap io o, (congrArg (fun g : Sp Ω ⟶ Z => g o) e).trans hy⟩`.
-/
theorem IsTorsionOver.exists_rational {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (t : SAB H X) {R : Type} [CommRing R] [IsDomain R] {x : Sp R ⟶ X}
    {π : Z ⟶ Sp R} {κ : Over.mk (π ≫ x) ⟶ t.G} (h : IsTorsionOver t.G x q π κ) (hs : SplitTors t x q) (z : Z)
    (hz : π z = genericPoint (Sp R)) :
    ∃ g₀ : Sp (FractionRing R) ⟶ Z, g₀ ≫ π = spMap (algebraMap R (FractionRing R)) ∧ z ∈ Set.range g₀ := by
  obtain ⟨Ω, _, y, o, hy⟩ : ∃ (Ω : Type) (_ : Field Ω) (y : Sp Ω ⟶ Z) (o : Sp Ω), y o = z :=
    ⟨Z.residueField z, inferInstance, Z.fromSpecResidueField z, IsLocalRing.closedPoint _,
      Scheme.fromSpecResidueField_apply z _⟩
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (y ≫ π)
  have hinj : Function.Injective φ.hom := by
    rw [RingHom.injective_iff_ker_eq_bot, eq_bot_iff]
    intro a ha
    have h1 : Spec.map φ o = genericPoint (Sp R) := by rw [hφ, Scheme.Hom.comp_apply, hy, hz]
    rw [genericPoint_eq_bot_of_affine] at h1
    have h2 : a ∈ (Spec.map φ o).asIdeal := by
      change φ.hom a ∈ o.asIdeal
      rw [RingHom.mem_ker.mp ha]; exact zero_mem _
    rw [h1] at h2
    exact h2
  let io : FractionRing R →+* Ω := IsFractionRing.lift hinj
  have hio : spMap (io.comp (algebraMap R (FractionRing R))) = y ≫ π := by
    rw [← hφ, show io.comp (algebraMap R (FractionRing R)) = φ.hom from
      RingHom.ext fun a => IsFractionRing.lift_algebraMap hinj a]
    rfl
  have hio' : spMap io ≫ spMap (algebraMap R (FractionRing R)) = y ≫ π := by
    rw [← hio, ← Spec.map_comp]; rfl
  let w : Over.mk (spMap (io.comp (algebraMap R (FractionRing R))) ≫ x) ⟶ t.G :=
    (Over.homMk y (by rw [hio]; simp) : _ ⟶ Over.mk (π ≫ x)) ≫ κ
  have hw : w ^ q = 1 := h.pow_eq_one w y rfl
  obtain ⟨w₀, hw₀⟩ := hs Ω io w hw
  have := epi_spMap io
  have h0 : w₀ ≫ t.G.hom = spMap (algebraMap R (FractionRing R)) ≫ x := by
    rw [← cancel_epi (spMap io), reassoc_of% hw₀, reassoc_of% hio', Over.w w, ← Category.assoc, ← hio]; rfl
  let w₁ : Over.mk (spMap (algebraMap R (FractionRing R)) ≫ x) ⟶ t.G := Over.homMk w₀ h0
  let i : Over.mk (spMap (io.comp (algebraMap R (FractionRing R))) ≫ x) ⟶
      Over.mk (spMap (algebraMap R (FractionRing R)) ≫ x) := Over.homMk (spMap io) (by
    rw [hio]; simp [reassoc_of% hio'])
  have hi : i ≫ w₁ = w := Over.OverMorphism.ext hw₀
  have hw₁ : w₁ ^ q = 1 := by
    have : i ≫ w₁ ^ q = i ≫ 1 := by rw [MonObj.comp_pow, hi, hw, MonObj.comp_one]
    exact Over.OverMorphism.ext ((cancel_epi (spMap io)).mp (congrArg Over.Hom.left this))
  obtain ⟨g₀, hg₀, hg₀'⟩ := h.lift _ w₁ (spMap (algebraMap R (FractionRing R))) rfl hw₁
  have e : spMap io ≫ g₀ = y := h.ext _ _ _ ((Category.assoc _ _ _).trans ((congrArg (spMap io ≫ ·) hg₀).trans hio'))
    ((Category.assoc _ _ _).trans ((congrArg (spMap io ≫ ·) hg₀').trans hw₀))
  exact ⟨g₀, hg₀, spMap io o, (congrArg (fun g : Sp Ω ⟶ Z => g o) e).trans hy⟩

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨β, rfl, hβ⟩ s`. Establish `e : spMap β ≫ j = z` using `h.ext _ _ _ (by`. Rewrite using `[Category.assoc, hj, hz, ← Spec.map_comp_assoc]`. Use the proof step `rfl) ((Category.assoc _ _ _).trans hβ)`.

Conclude with `(hr.subset ⟨spMap β s, congrArg (fun g : Sp T ⟶ Z => g s) e⟩).1`. Introduce `hs`. Establish `r : Set.range z ⊆ Set.range j`. Introduce and unpack `_ ⟨s, rfl⟩`. Conclude with `hr.superset ⟨hs s, spMap φ s, (congrArg (fun g : Sp T ⟶ S => g s) hz).symm⟩`.

Take `⟨β, hβ⟩` from `Spec.map_surjective (IsOpenImmersion.lift j z r)`. Establish `e : Spec.map β ≫ j = z` using `by rw [hβ, IsOpenImmersion.lift_fac]`. Use `⟨β.hom, ?_, (Category.assoc _ _ _).symm.trans (congrArg (· ≫ κ.left) e)⟩` and prove the remaining obligations. Establish `e' : Spec.map β ≫ spMap (algebraMap A B) = spMap φ`. Rewrite using `[← cancel_mono a, Category.assoc, ← hj, reassoc_of% e, hz]`.

Rewrite `e'` using `[← Spec.map_comp]`. Conclude with `congrArg CommRingCat.Hom.hom (Spec.map_injective e')`.
-/
theorem IsTorsionOver.thru_iff {E : Type} [Field E] [NumberField E] [IsCMField E]
    {Ho : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (t : SAB Ho X) {κ : Over.mk (π ≫ x) ⟶ t.G} (h : IsTorsionOver t.G x q π κ)
    {A B : Type} [CommRing A] [CommRing B] [Algebra A B] (a : Sp A ⟶ S) [Mono a] (j : Sp B ⟶ Z) [IsOpenImmersion j]
    (hj : j ≫ π = spMap (algebraMap A B) ≫ a) (H : Z.Opens) (hr : Set.range j = (H : Set Z) ∩ π ⁻¹' Set.range a)
    {T : Type} [CommRing T] (φ : A →+* T) (z : Sp T ⟶ Z) (hz : z ≫ π = spMap φ ≫ a) :
    Thru t (j ≫ κ.left) φ (z ≫ κ.left) ↔ ∀ s, z s ∈ H := by
  constructor
  · rintro ⟨β, rfl, hβ⟩ s
    have e : spMap β ≫ j = z := h.ext _ _ _ (by
      rw [Category.assoc, hj, hz, ← Spec.map_comp_assoc]; rfl) ((Category.assoc _ _ _).trans hβ)
    exact (hr.subset ⟨spMap β s, congrArg (fun g : Sp T ⟶ Z => g s) e⟩).1
  · intro hs
    have r : Set.range z ⊆ Set.range j := by
      rintro _ ⟨s, rfl⟩
      exact hr.superset ⟨hs s, spMap φ s, (congrArg (fun g : Sp T ⟶ S => g s) hz).symm⟩
    obtain ⟨β, hβ⟩ := Spec.map_surjective (IsOpenImmersion.lift j z r)
    have e : Spec.map β ≫ j = z := by rw [hβ, IsOpenImmersion.lift_fac]
    refine ⟨β.hom, ?_, (Category.assoc _ _ _).symm.trans (congrArg (· ≫ κ.left) e)⟩
    have e' : Spec.map β ≫ spMap (algebraMap A B) = spMap φ := by
      rw [← cancel_mono a, Category.assoc, ← hj, reassoc_of% e, hz]
    rw [← Spec.map_comp] at e'
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective e')

/- English proof (translation)
Establish `hin : ∀ {T : Type} [CommRing T] (φ : A →+* T) (z : Sp T ⟶ Z), z ≫ π = spMap φ ≫ a → ∀ s, π (z s) = a (spMap φ s)` using `fun φ z hz s => congrArg (fun g : _ ⟶ S => g s) hz`. Establish `hsect : ∀ (k : Type) [Field k] (β : B →+* k), ∃ σ : B →ₐ[A] A, β = (β.comp (algebraMap A B)).comp σ.toRingHom` using `fun k _ β => by`. Set `o : Sp k` to `IsLocalRing.closedPoint k`. Take `⟨hz, y, hy⟩` from `hr.subset ⟨spMap β o, rfl⟩`. Take `⟨s, hs, hsH, w, hw⟩` from `hsec _ hz`.

Establish `r : Set.range a ⊆ Set.range W.ι`. Rewrite using `[Scheme.Opens.range_ι]`. Introduce and unpack `_ ⟨y, rfl⟩`. Conclude with `hW y`. Establish `f` using `IsOpenImmersion.lift_fac W.ι a r`.

Establish `hz' : (IsOpenImmersion.lift W.ι a r ≫ s) ≫ π = spMap (RingHom.id A) ≫ a`. Rewrite using `[Category.assoc, hs, f]`. Conclude with `(Category.id_comp a).symm.trans (congrArg (· ≫ a) (Spec.map_id _).symm)`. Take `⟨σ, hσ, hσ'⟩` from `(h.thru_iff t a j hj H hr _ _ hz').mpr fun y => hsH _`. Establish `e : spMap σ ≫ j = IsOpenImmersion.lift W.ι a r ≫ s` using `h.ext _ _ _ (by`.

Rewrite using `[Category.assoc, hj, hz', ← hσ, ← Spec.map_comp_assoc]`. Use the proof step `rfl) ((Category.assoc _ _ _).trans hσ')`. Use `⟨{ σ with commutes' := fun c => congrArg (fun g : A →+* A => g c) hσ }, eq_comp_section β _ o ⟨y, ?_⟩⟩` and prove the remaining obligations. Apply `j.isOpenEmbedding.injective` to reduce the goal to its premises. Use `(congrArg (fun g : Sp A ⟶ Z => g y) e).trans ?_` and prove the remaining obligations.

Rewrite using `[← hw, Scheme.Hom.comp_apply]`. Use `congr 1`. Apply `W.ι.isOpenEmbedding.injective` to reduce the goal to its premises. Rewrite using `[← Scheme.Hom.comp_apply, f, hy, ← hw, ← Scheme.Hom.comp_apply, hs]`. Use `⟨‹_›, ‹_›, h.pow_eq_one u j hu.symm, fun T _ β β' e e' => ?_, fun T _ φ w hw hm => ?_, fun T _ φ => ?_, fun T _ φ w w' hw hw' => ?_, hsect, fun b hb => ?_⟩` and prove the remaining obligations.

Establish `e₁ : spMap β ≫ j = spMap β' ≫ j` using `h.ext _ _ _ (by`. Rewrite using `[Category.assoc, Category.assoc, hj, ← Spec.map_comp_assoc, ← Spec.map_comp_assoc]`. Conclude with `congrArg (fun g => spMap g ≫ a) e) (by`. Rewrite using `[Category.assoc, Category.assoc, ← hu]`. Conclude with `e')`.

Conclude with `congrArg CommRingCat.Hom.hom (Spec.map_injective ((cancel_mono j).mp e₁))`. Take `⟨z, hz, hz'⟩` from `h.lift _ w (spMap φ ≫ a) (Category.assoc _ _ _) hw`. Rewrite using `[hu, ← hz']`. Use `(h.thru_iff t a j hj H hr φ z hz).mpr (mem_of_forall_maximal (z ⁻¹ᵁ H) fun 𝔪 h𝔪 => ?_)` and prove the remaining obligations. Establish `h1` using `hm 𝔪 h𝔪`.

Rewrite `h1` using `[hu, ← hz']`. Conclude with `(h.thru_iff t a j hj H hr ((Ideal.Quotient.mk 𝔪).comp φ) (spMap (Ideal.Quotient.mk 𝔪) ≫ z) (by`. Rewrite using `[Category.assoc]`. Use `(congrArg (spMap (Ideal.Quotient.mk 𝔪) ≫ ·) hz).trans ?_` and prove the remaining obligations. Rewrite using `[← Spec.map_comp_assoc]`.

Use the proof step `rfl)).mp h1`. Take `⟨z, hz, hz'⟩` from `h.lift (Over.mk (spMap φ ≫ a ≫ x)) 1 (spMap φ ≫ a) (Category.assoc _ _ _) (one_pow _)`. Rewrite using `[hu, ← hz']`. Conclude with `(h.thru_iff t a j hj H hr φ z hz).mpr fun s => hone _ z hz' s ((hin φ z hz s).symm ▸ hW₁ _)`. Establish `hq : ∀ v : Over.mk (spMap φ ≫ a ≫ x) ⟶ t.G, Thru t u.left φ v.left → v ^ q = 1`.

Introduce and unpack `v ⟨β, -, hβ⟩`. Conclude with `h.pow_eq_one v (spMap β ≫ j) (by rw [← hβ, hu]; exact Category.assoc _ _ _)`. Take `⟨z, hz, hz₁⟩` from `h.lift _ w (spMap φ ≫ a) (Category.assoc _ _ _) (hq w hw)`. Take `⟨z', hz', hz₂⟩` from `h.lift _ w' (spMap φ ≫ a) (Category.assoc _ _ _) (hq w' hw')`. Take `⟨z'', hz'', hz₃⟩` from `h.lift _ (w * w') (spMap φ ≫ a) (Category.assoc _ _ _) (by rw [mul_pow, hq w hw, hq w' hw', _root_.mul_one])`.

Rewrite `hw` using `[hu, ← hz₁]`. Rewrite `hw'` using `[hu, ← hz₂]`. Rewrite using `[hu, ← hz₃]`. Conclude with `(h.thru_iff t a j hj H hr φ z'' hz'').mpr fun s => hmul _ w w' z z' z'' hz₁ hz₂ hz₃ (hz'.trans hz.symm) (hz''.trans hz.symm) ((h.thru_iff t a j hj H hr φ z hz).mp hw) ((h.thru_iff t a j hj H hr φ z' hz').mp hw') s ((hin φ z hz s).symm ▸ hW₂ _)`. Establish `: _root_.IsReduced B` using `(affine_isReduced_iff (CommRingCat.of B)).mp (isReduced_of_isOpenImmersion j)`.

Use `IsNilpotent.eq_zero (nilpotent_iff_mem_prime.mpr fun J hJ => ?_)` and prove the remaining obligations. Take `⟨σ, hσ⟩` from `hsect J.ResidueField (algebraMap B J.ResidueField)`. Rewrite using `[← Ideal.algebraMap_residueField_eq_zero, hσ]`. Simplify using `[hb σ]`.
-/
theorem IsTorsionOver.isFinPart {E : Type} [Field E] [NumberField E] [IsCMField E]
    {Ho : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (t : SAB Ho X) {κ : Over.mk (π ≫ x) ⟶ t.G} (h : IsTorsionOver t.G x q π κ)
    [AlgebraicGeometry.IsReduced Z] {A B : Type} [CommRing A] [CommRing B] [Algebra A B] [Module.Finite A B]
    [Module.Free A B] (a : Sp A ⟶ S) [Mono a] (j : Sp B ⟶ Z) [IsOpenImmersion j]
    (hj : j ≫ π = spMap (algebraMap A B) ≫ a) (H : Z.Opens) (hr : Set.range j = (H : Set Z) ∩ π ⁻¹' Set.range a)
    (W W₁ W₂ : S.Opens) (hW : ∀ y, a y ∈ W) (hW₁ : ∀ y, a y ∈ W₁) (hW₂ : ∀ y, a y ∈ W₂)
    (hsec : ∀ z ∈ H, ∃ s : W.toScheme ⟶ Z, s ≫ π = W.ι ∧ (∀ w, s w ∈ H) ∧ z ∈ Set.range s)
    (hone : ∀ (T : Over X) (z : T.left ⟶ Z), z ≫ κ.left = (1 : T ⟶ t.G).left → ∀ s, π (z s) ∈ W₁ → z s ∈ H)
    (hmul : ∀ (T : Over X) (w w' : T ⟶ t.G)
      (z z' z'' : T.left ⟶ Z), z ≫ κ.left = w.left → z' ≫ κ.left = w'.left → z'' ≫ κ.left = (w * w').left →
      z' ≫ π = z ≫ π → z'' ≫ π = z ≫ π → (∀ s, z s ∈ H) → (∀ s, z' s ∈ H) → ∀ s, π (z s) ∈ W₂ → z'' s ∈ H)
    (u : Over.mk (spMap (algebraMap A B) ≫ a ≫ x) ⟶ t.G) (hu : u.left = j ≫ κ.left) :
    IsFinPart t (a ≫ x) q u := by
  have hin : ∀ {T : Type} [CommRing T] (φ : A →+* T) (z : Sp T ⟶ Z), z ≫ π = spMap φ ≫ a → ∀ s,
      π (z s) = a (spMap φ s) := fun φ z hz s => congrArg (fun g : _ ⟶ S => g s) hz
  have hsect : ∀ (k : Type) [Field k] (β : B →+* k),
      ∃ σ : B →ₐ[A] A, β = (β.comp (algebraMap A B)).comp σ.toRingHom := fun k _ β => by
    let o : Sp k := IsLocalRing.closedPoint k
    obtain ⟨hz, y, hy⟩ := hr.subset ⟨spMap β o, rfl⟩
    obtain ⟨s, hs, hsH, w, hw⟩ := hsec _ hz
    have r : Set.range a ⊆ Set.range W.ι := by
      rw [Scheme.Opens.range_ι]; rintro _ ⟨y, rfl⟩; exact hW y
    have f := IsOpenImmersion.lift_fac W.ι a r
    have hz' : (IsOpenImmersion.lift W.ι a r ≫ s) ≫ π = spMap (RingHom.id A) ≫ a := by
      rw [Category.assoc, hs, f]
      exact (Category.id_comp a).symm.trans (congrArg (· ≫ a) (Spec.map_id _).symm)
    obtain ⟨σ, hσ, hσ'⟩ := (h.thru_iff t a j hj H hr _ _ hz').mpr fun y => hsH _
    have e : spMap σ ≫ j = IsOpenImmersion.lift W.ι a r ≫ s := h.ext _ _ _ (by
      rw [Category.assoc, hj, hz', ← hσ, ← Spec.map_comp_assoc]; rfl) ((Category.assoc _ _ _).trans hσ')
    refine ⟨{ σ with commutes' := fun c => congrArg (fun g : A →+* A => g c) hσ }, eq_comp_section β _ o ⟨y, ?_⟩⟩
    apply j.isOpenEmbedding.injective
    refine (congrArg (fun g : Sp A ⟶ Z => g y) e).trans ?_
    rw [← hw, Scheme.Hom.comp_apply]
    congr 1
    apply W.ι.isOpenEmbedding.injective
    rw [← Scheme.Hom.comp_apply, f, hy, ← hw, ← Scheme.Hom.comp_apply, hs]
  refine ⟨‹_›, ‹_›, h.pow_eq_one u j hu.symm, fun T _ β β' e e' => ?_, fun T _ φ w hw hm => ?_, fun T _ φ => ?_,
    fun T _ φ w w' hw hw' => ?_, hsect, fun b hb => ?_⟩
  · have e₁ : spMap β ≫ j = spMap β' ≫ j := h.ext _ _ _ (by
      rw [Category.assoc, Category.assoc, hj, ← Spec.map_comp_assoc, ← Spec.map_comp_assoc]
      exact congrArg (fun g => spMap g ≫ a) e) (by
        rw [Category.assoc, Category.assoc, ← hu]; exact e')
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective ((cancel_mono j).mp e₁))
  · obtain ⟨z, hz, hz'⟩ := h.lift _ w (spMap φ ≫ a) (Category.assoc _ _ _) hw
    rw [hu, ← hz']
    refine (h.thru_iff t a j hj H hr φ z hz).mpr (mem_of_forall_maximal (z ⁻¹ᵁ H) fun 𝔪 h𝔪 => ?_)
    have h1 := hm 𝔪 h𝔪
    rw [hu, ← hz'] at h1
    exact (h.thru_iff t a j hj H hr ((Ideal.Quotient.mk 𝔪).comp φ) (spMap (Ideal.Quotient.mk 𝔪) ≫ z) (by
      rw [Category.assoc]
      refine (congrArg (spMap (Ideal.Quotient.mk 𝔪) ≫ ·) hz).trans ?_
      rw [← Spec.map_comp_assoc]; rfl)).mp h1
  · obtain ⟨z, hz, hz'⟩ := h.lift (Over.mk (spMap φ ≫ a ≫ x)) 1 (spMap φ ≫ a) (Category.assoc _ _ _) (one_pow _)
    rw [hu, ← hz']
    exact (h.thru_iff t a j hj H hr φ z hz).mpr fun s => hone _ z hz' s ((hin φ z hz s).symm ▸ hW₁ _)
  · have hq : ∀ v : Over.mk (spMap φ ≫ a ≫ x) ⟶ t.G, Thru t u.left φ v.left → v ^ q = 1 := by
      rintro v ⟨β, -, hβ⟩
      exact h.pow_eq_one v (spMap β ≫ j) (by rw [← hβ, hu]; exact Category.assoc _ _ _)
    obtain ⟨z, hz, hz₁⟩ := h.lift _ w (spMap φ ≫ a) (Category.assoc _ _ _) (hq w hw)
    obtain ⟨z', hz', hz₂⟩ := h.lift _ w' (spMap φ ≫ a) (Category.assoc _ _ _) (hq w' hw')
    obtain ⟨z'', hz'', hz₃⟩ := h.lift _ (w * w') (spMap φ ≫ a) (Category.assoc _ _ _)
      (by rw [mul_pow, hq w hw, hq w' hw', _root_.mul_one])
    rw [hu, ← hz₁] at hw
    rw [hu, ← hz₂] at hw'
    rw [hu, ← hz₃]
    exact (h.thru_iff t a j hj H hr φ z'' hz'').mpr fun s => hmul _ w w' z z' z'' hz₁ hz₂ hz₃ (hz'.trans hz.symm)
      (hz''.trans hz.symm) ((h.thru_iff t a j hj H hr φ z hz).mp hw) ((h.thru_iff t a j hj H hr φ z' hz').mp hw') s
      ((hin φ z hz s).symm ▸ hW₂ _)
  · have : _root_.IsReduced B := (affine_isReduced_iff (CommRingCat.of B)).mp (isReduced_of_isOpenImmersion j)
    refine IsNilpotent.eq_zero (nilpotent_iff_mem_prime.mpr fun J hJ => ?_)
    obtain ⟨σ, hσ⟩ := hsect J.ResidueField (algebraMap B J.ResidueField)
    rw [← Ideal.algebraMap_residueField_eq_zero, hσ]
    simp [hb σ]

/- English proof (translation)
Introduce `E _ _ _ Ho X _ t R _ _ _ _ x q hq hs 𝔭 h𝔭`. Use `t.semi.smooth` as an intermediate fact. Use `t.semi.separated` as an intermediate fact. Use `t.semi.quasiCompact` as an intermediate fact. Take `⟨_, _⟩` from `GlobalTheory.T.torsion_flat_locallyQuasiFinite X t.G t.semi q hq`.

Establish `hcl : IsClosedImmersion η[t.G].left`. Establish `: IsClosedImmersion (η[t.G].left ≫ t.G.hom)`. Rewrite using `[Over.w]`. Conclude with `inferInstanceAs (IsClosedImmersion (𝟙 X))`. Conclude with `IsClosedImmersion.of_comp _ t.G.hom`.

Establish `: IsClosedImmersion (torsion.ι t.G q).left` using `MorphismProperty.of_isPullback (P := @IsClosedImmersion) (GrpTangent.isPullback_torsion t.G q).flip hcl`. Establish `: IsSeparated (torsion t.G q).hom` using `by rw [← Over.w (torsion.ι t.G q)]; infer_instance`. Establish `: QuasiCompact (torsion t.G q).hom` using `by rw [← Over.w (torsion.ι t.G q)]; infer_instance`. Establish `: LocallyOfFiniteType (torsion t.G q).hom` using `by rw [← Over.w (torsion.ι t.G q)]; infer_instance`. Establish `: LocallyOfFinitePresentation (torsion t.G q).hom` using `inferInstance`.

Establish `hred : IsReduced (pullback (torsion t.G q).hom x)`. Establish `hu : IsUnit (q : Γ(Sp (FractionRing R), ⊤))`. Establish `h0 : (q : FractionRing R) ≠ 0`. Rewrite using `[← map_natCast (algebraMap R (FractionRing R))]`. Conclude with `fun h => Nat.cast_ne_zero.mpr hq ((map_eq_zero_iff _ (IsFractionRing.injective R _)).mp h)`.

Simplify using `using h0.isUnit.map (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom`. Establish `: Etale (pullback.snd (torsion t.G q).hom (spMap (algebraMap R (FractionRing R)) ≫ x))` using `LamF.etale_pullback_torsion _ t.G hu`. Use `GlobalTheory.isReduced_of_smooth_of_isReduced (pullback.snd (torsion t.G q).hom (spMap (algebraMap R (FractionRing R)) ≫ x))` as an intermediate fact. Use `isReduced_of_isOpenImmersion (pullbackLeftPullbackSndIso (torsion t.G q).hom x (spMap (algebraMap R (FractionRing R)))).hom` as an intermediate fact. Conclude with `isReduced_of_generic (K := FractionRing R) (pullback.snd (torsion t.G q).hom x)`.

Establish `h` using `isTorsionOver t.G x q`. Set `p : PrimeSpectrum R` to `⟨𝔭, h𝔭⟩`. Take `⟨W, H, ρ, hpW, hρ, _, hH, hsec⟩` from `exists_finite_open (K := FractionRing R) (pullback.snd (torsion t.G q).hom x) (h.exists_rational t hs) p`. Take `⟨W₁, hW₁, hone⟩` from `h.exists_open_one p H hH`. Take `⟨W₂, hW₂, hmul⟩` from `h.exists_open_mul p W H ρ hpW hρ hH`.

Take `⟨f, B, _, _, j, hf, hfin, hfree, _, hj, hsub, hr⟩` from `exists_free_chart (pullback.snd (torsion t.G q).hom x) p W (W₁ ⊓ W₂) H ρ hpW ⟨hW₁, hW₂⟩ hρ`. Establish `: IsOpenImmersion (spMap (algebraMap R (Localization.Away f)))` using `IsOpenImmersion.of_isLocalization f`. Set `u₀ : Over.mk (spMap (algebraMap (Localization.Away f) B) ≫ spMap (algebraMap R (Localization.Away f)) ≫ x) ⟶ Over.mk (pullback.snd (torsion t.G q).hom x ≫ x)` to `Over.homMk j (by simp [reassoc_of% hj])`. Use `⟨f, B, inferInstance, inferInstance, u₀ ≫ _, hf, h.isFinPart t _ j hj H hr W W₁ W₂ (fun y => (hsub ⟨y, rfl⟩).1) (fun y => (hsub ⟨y, rfl⟩).2.1) (fun y => (hsub ⟨y, rfl⟩).2.2) hsec hone hmul _ rfl, fun k _ φ hφ w hw => ?_⟩` and prove the remaining obligations. Take `⟨z, hz, hz'⟩` from `h.lift _ w (spMap φ ≫ spMap (algebraMap R (Localization.Away f))) (Category.assoc _ _ _) hw`.

Rewrite using `[← hz']`. Use `(h.thru_iff t _ j hj H hr φ z hz).mpr fun s => hH _ ?_` and prove the remaining obligations. Use `(congrArg (fun g : Sp k ⟶ Sp R => g s) hz).trans (PrimeSpectrum.ext ?_)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Ideal.comap (algebraMap R (Localization.Away f)) (Ideal.comap φ s.asIdeal) = 𝔭`. Rewrite using `[Ideal.eq_bot_of_prime s.asIdeal (h := s.isPrime), Ideal.comap_comap, ← hφ]`.

Both sides reduce to the same expression.
-/
theorem exists_finite_part : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) [IsLocallyNoetherian X] (t : SAB H X) (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [CharZero R] (x : Sp R ⟶ X) (q : ℕ), q ≠ 0 → SplitTors t x q → ∀ 𝔭 : Ideal R, 𝔭.IsPrime → ∃ (f : R) (B : Type) (_ : CommRing B) (_ : Algebra (Localization.Away f) B) (u : Over.mk (spMap (algebraMap (Localization.Away f) B) ≫ spMap (algebraMap R (Localization.Away f)) ≫ x) ⟶ t.G), f ∉ 𝔭 ∧ IsFinPart t (spMap (algebraMap R (Localization.Away f)) ≫ x) q u ∧ ∀ (k : Type) [Field k] (φ : Localization.Away f →+* k), RingHom.ker (φ.comp (algebraMap R (Localization.Away f))) = 𝔭 → ∀ w : Over.mk (spMap φ ≫ spMap (algebraMap R (Localization.Away f)) ≫ x) ⟶ t.G, w ^ q = 1 → Thru t u.left φ w.left := by
  intro E _ _ _ Ho X _ t R _ _ _ _ x q hq hs 𝔭 h𝔭
  have := t.semi.smooth
  have := t.semi.separated
  have := t.semi.quasiCompact
  obtain ⟨_, _⟩ := GlobalTheory.T.torsion_flat_locallyQuasiFinite X t.G t.semi q hq
  have hcl : IsClosedImmersion η[t.G].left := by
    have : IsClosedImmersion (η[t.G].left ≫ t.G.hom) := by
      rw [Over.w]; exact inferInstanceAs (IsClosedImmersion (𝟙 X))
    exact IsClosedImmersion.of_comp _ t.G.hom
  have : IsClosedImmersion (torsion.ι t.G q).left :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion) (GrpTangent.isPullback_torsion t.G q).flip hcl
  have : IsSeparated (torsion t.G q).hom := by rw [← Over.w (torsion.ι t.G q)]; infer_instance
  have : QuasiCompact (torsion t.G q).hom := by rw [← Over.w (torsion.ι t.G q)]; infer_instance
  have : LocallyOfFiniteType (torsion t.G q).hom := by rw [← Over.w (torsion.ι t.G q)]; infer_instance
  have : LocallyOfFinitePresentation (torsion t.G q).hom := inferInstance
  have hred : IsReduced (pullback (torsion t.G q).hom x) := by
    have hu : IsUnit (q : Γ(Sp (FractionRing R), ⊤)) := by
      have h0 : (q : FractionRing R) ≠ 0 := by
        rw [← map_natCast (algebraMap R (FractionRing R))]
        exact fun h => Nat.cast_ne_zero.mpr hq ((map_eq_zero_iff _ (IsFractionRing.injective R _)).mp h)
      simpa using h0.isUnit.map (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom
    have : Etale (pullback.snd (torsion t.G q).hom (spMap (algebraMap R (FractionRing R)) ≫ x)) :=
      LamF.etale_pullback_torsion _ t.G hu
    have := GlobalTheory.isReduced_of_smooth_of_isReduced
      (pullback.snd (torsion t.G q).hom (spMap (algebraMap R (FractionRing R)) ≫ x))
    have := isReduced_of_isOpenImmersion
      (pullbackLeftPullbackSndIso (torsion t.G q).hom x (spMap (algebraMap R (FractionRing R)))).hom
    exact isReduced_of_generic (K := FractionRing R) (pullback.snd (torsion t.G q).hom x)
  have h := isTorsionOver t.G x q
  let p : PrimeSpectrum R := ⟨𝔭, h𝔭⟩
  obtain ⟨W, H, ρ, hpW, hρ, _, hH, hsec⟩ := exists_finite_open (K := FractionRing R)
    (pullback.snd (torsion t.G q).hom x) (h.exists_rational t hs) p
  obtain ⟨W₁, hW₁, hone⟩ := h.exists_open_one p H hH
  obtain ⟨W₂, hW₂, hmul⟩ := h.exists_open_mul p W H ρ hpW hρ hH
  obtain ⟨f, B, _, _, j, hf, hfin, hfree, _, hj, hsub, hr⟩ :=
    exists_free_chart (pullback.snd (torsion t.G q).hom x) p W (W₁ ⊓ W₂) H ρ hpW ⟨hW₁, hW₂⟩ hρ
  have : IsOpenImmersion (spMap (algebraMap R (Localization.Away f))) := IsOpenImmersion.of_isLocalization f
  let u₀ : Over.mk (spMap (algebraMap (Localization.Away f) B) ≫ spMap (algebraMap R (Localization.Away f)) ≫ x) ⟶
      Over.mk (pullback.snd (torsion t.G q).hom x ≫ x) := Over.homMk j (by simp [reassoc_of% hj])
  refine ⟨f, B, inferInstance, inferInstance, u₀ ≫ _, hf, h.isFinPart t _ j hj H hr W W₁ W₂
    (fun y => (hsub ⟨y, rfl⟩).1) (fun y => (hsub ⟨y, rfl⟩).2.1) (fun y => (hsub ⟨y, rfl⟩).2.2) hsec hone hmul _ rfl,
    fun k _ φ hφ w hw => ?_⟩
  obtain ⟨z, hz, hz'⟩ := h.lift _ w (spMap φ ≫ spMap (algebraMap R (Localization.Away f))) (Category.assoc _ _ _) hw
  rw [← hz']
  refine (h.thru_iff t _ j hj H hr φ z hz).mpr fun s => hH _ ?_
  refine (congrArg (fun g : Sp k ⟶ Sp R => g s) hz).trans (PrimeSpectrum.ext ?_)
  change Ideal.comap (algebraMap R (Localization.Away f)) (Ideal.comap φ s.asIdeal) = 𝔭
  rw [Ideal.eq_bot_of_prime s.asIdeal (h := s.isPrime), Ideal.comap_comap, ← hφ]
  rfl

end GlobalTheory.SplitFinitePart
