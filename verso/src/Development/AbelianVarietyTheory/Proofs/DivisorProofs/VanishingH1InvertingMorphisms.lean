import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CommAlgFunctorCoboundaryZeroMemCocyclesOne

set_option autoImplicit false

noncomputable section

open CategoryTheory Filter

namespace GlobalTheory.CatCoh.Desc

universe v u w

variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C] (F : C ⥤ CommAlgCat.{0} R)

section Defs

variable {T : C} (P : ∀ S, (T ⟶ S) → Prop)

def IsSec (s : ∀ S, (T ⟶ S) → F.obj S) : Prop :=
  ∀ S S' (u : T ⟶ S) (ψ : S ⟶ S'), P S u → s S' (u ≫ ψ) = mp F ψ (s S u)

def Sep : Prop := ∀ x : F.obj T, (∀ S u, P S u → mp F u x = 0) → x = 0

def Glue : Prop := ∀ s, IsSec F P s → ∃ x : F.obj T, ∀ S u, P S u → mp F u x = s S u

def Van1 : Prop := ∀ a : ∀ S S', (T ⟶ S) → (S ⟶ S') → F.obj S',
  (∀ S S' S'' u ψ χ, P S u → a S S'' u (ψ ≫ χ) = mp F χ (a S S' u ψ) + a S' S'' (u ≫ ψ) χ) →
  ∃ b : ∀ S, (T ⟶ S) → F.obj S, ∀ S S' u ψ, P S u → b S' (u ≫ ψ) - mp F ψ (b S u) = a S S' u ψ

def Van2 : Prop := ∀ z : ∀ S S' S'', (T ⟶ S) → (S ⟶ S') → (S' ⟶ S'') → F.obj S'',
  (∀ S S' S'' S''' u ψ χ ω, P S u → mp F ω (z S S' S'' u ψ χ) + z S S'' S''' u (ψ ≫ χ) ω =
    z S S' S''' u ψ (χ ≫ ω) + z S' S'' S''' (u ≫ ψ) χ ω) →
  ∃ a : ∀ S S', (T ⟶ S) → (S ⟶ S') → F.obj S', ∀ S S' S'' u ψ χ, P S u →
    mp F χ (a S S' u ψ) - a S S'' u (ψ ≫ χ) + a S' S'' (u ≫ ψ) χ = z S S' S'' u ψ χ

end Defs

/- English proof (translation)
Establish `h1 : ∀ T (e : E T), ∃ g : ∀ S, (T ⟶ S) → F.obj S, Q T e → ∀ S S' u ψ, P S (act e u) → g S' (u ≫ ψ) - mp F ψ (g S u) = f S S' (act e u) ψ - z T S S' e u ψ`. Introduce `T e`. Distinguish the cases in `hq : Q T e`. Take `⟨g, hg⟩` from `van T e hq (fun S S' u ψ ↦ f S S' (act e u) ψ - z T S S' e u ψ) fun S S' S'' u ψ χ hp ↦ by`. Establish `k1` using `hz _ _ _ _ e u ψ χ hq`.

Establish `k2` using `hf _ _ _ _ ψ χ hp`. Simplify using `only [map_sub, hact]`. Take the linear combination `k1 - k2`. Conclude with `⟨g, fun _ ↦ hg⟩`. Conclude with `⟨0, fun h ↦ absurd h hq⟩`.

Use `choose g hg using h1`. Establish `h2 : ∀ T T' (e : E T) (φ : T ⟶ T'), ∃ x : F.obj T', Q T e → ∀ S (u : T' ⟶ S), P S (act (act e φ) u) → mp F u x = z T T' S e φ u + g T e S (φ ≫ u) - g T' (act e φ) S u`. Introduce `T T' e φ`. Distinguish the cases in `hq : Q T e`. Take `⟨x, hx⟩` from `glue T' _ (hQ _ _ e φ hq) (fun S u ↦ z T T' S e φ u + g T e S (φ ≫ u) - g T' (act e φ) S u) fun S S' u ψ hp ↦ by`.

Establish `k1` using `hz _ _ _ _ e φ u ψ hq`. Establish `k2` using `hg T e hq S S' (φ ≫ u) ψ (by rwa [hact])`. Establish `k3` using `hg T' _ (hQ _ _ e φ hq) S S' u ψ hp`. Simplify using `only [map_sub, map_add, hact, Category.assoc] at k2 ⊢`. Take the linear combination `k2 - k1 - k3`.

Conclude with `⟨x, fun _ ↦ hx⟩`. Conclude with `⟨0, fun h ↦ absurd h hq⟩`. Use `choose h hh using h2`. Use `⟨h, fun T T' T'' e φ ψ hq ↦ sub_eq_zero.1 (sep T'' _ (hQ _ _ _ ψ (hQ _ _ e φ hq)) _ fun S u hp ↦ ?_)⟩` and prove the remaining obligations. Establish `k1` using `hz _ _ _ _ e φ ψ u hq`.

Establish `k2` using `hh T T' e φ hq S (ψ ≫ u) (by rwa [hact])`. Establish `k3` using `hh T T'' e (φ ≫ ψ) hq S u (by rwa [hact])`. Establish `k4` using `hh T' T'' _ ψ (hQ _ _ e φ hq) S u hp`. Simplify using `only [map_sub, map_add, hact, Category.assoc, mp_comp] at k2 k3 ⊢`. Take the linear combination `k2 - k3 + k4 - k1`.
-/
theorem coboundary_of_restrict {E : C → Type w} (act : ∀ {S S'}, E S → (S ⟶ S') → E S')
    (hact : ∀ {S S' S''} (e : E S) (ψ : S ⟶ S') (χ : S' ⟶ S''), act e (ψ ≫ χ) = act (act e ψ) χ)
    (Q P : ∀ S, E S → Prop) (hQ : ∀ S S' e (ψ : S ⟶ S'), Q S e → Q S' (act e ψ))
    (sep : ∀ S e, Q S e → Sep F fun S' (ψ : S ⟶ S') ↦ P S' (act e ψ))
    (glue : ∀ S e, Q S e → Glue F fun S' (ψ : S ⟶ S') ↦ P S' (act e ψ))
    (van : ∀ S e, Q S e → Van1 F fun S' (ψ : S ⟶ S') ↦ P S' (act e ψ))
    (z : ∀ S S' S'', E S → (S ⟶ S') → (S' ⟶ S'') → F.obj S'')
    (hz : ∀ S S' S'' S''' e ψ χ ω, Q S e → mp F ω (z S S' S'' e ψ χ) + z S S'' S''' e (ψ ≫ χ) ω =
      z S S' S''' e ψ (χ ≫ ω) + z S' S'' S''' (act e ψ) χ ω)
    (f : ∀ S S', E S → (S ⟶ S') → F.obj S')
    (hf : ∀ S S' S'' e ψ χ, P S e →
      mp F χ (f S S' e ψ) - f S S'' e (ψ ≫ χ) + f S' S'' (act e ψ) χ = z S S' S'' e ψ χ) :
    ∃ h : ∀ S S', E S → (S ⟶ S') → F.obj S', ∀ S S' S'' e ψ χ, Q S e →
      mp F χ (h S S' e ψ) - h S S'' e (ψ ≫ χ) + h S' S'' (act e ψ) χ = z S S' S'' e ψ χ := by
  have h1 : ∀ T (e : E T), ∃ g : ∀ S, (T ⟶ S) → F.obj S, Q T e → ∀ S S' u ψ, P S (act e u) →
      g S' (u ≫ ψ) - mp F ψ (g S u) = f S S' (act e u) ψ - z T S S' e u ψ := by
    intro T e
    by_cases hq : Q T e
    · obtain ⟨g, hg⟩ := van T e hq (fun S S' u ψ ↦ f S S' (act e u) ψ - z T S S' e u ψ)
        fun S S' S'' u ψ χ hp ↦ by
          have k1 := hz _ _ _ _ e u ψ χ hq
          have k2 := hf _ _ _ _ ψ χ hp
          simp only [map_sub, hact]
          linear_combination k1 - k2
      exact ⟨g, fun _ ↦ hg⟩
    · exact ⟨0, fun h ↦ absurd h hq⟩
  choose g hg using h1
  have h2 : ∀ T T' (e : E T) (φ : T ⟶ T'), ∃ x : F.obj T', Q T e → ∀ S (u : T' ⟶ S),
      P S (act (act e φ) u) →
      mp F u x = z T T' S e φ u + g T e S (φ ≫ u) - g T' (act e φ) S u := by
    intro T T' e φ
    by_cases hq : Q T e
    · obtain ⟨x, hx⟩ := glue T' _ (hQ _ _ e φ hq)
        (fun S u ↦ z T T' S e φ u + g T e S (φ ≫ u) - g T' (act e φ) S u) fun S S' u ψ hp ↦ by
          have k1 := hz _ _ _ _ e φ u ψ hq
          have k2 := hg T e hq S S' (φ ≫ u) ψ (by rwa [hact])
          have k3 := hg T' _ (hQ _ _ e φ hq) S S' u ψ hp
          simp only [map_sub, map_add, hact, Category.assoc] at k2 ⊢
          linear_combination k2 - k1 - k3
      exact ⟨x, fun _ ↦ hx⟩
    · exact ⟨0, fun h ↦ absurd h hq⟩
  choose h hh using h2
  refine ⟨h, fun T T' T'' e φ ψ hq ↦ sub_eq_zero.1 (sep T'' _ (hQ _ _ _ ψ (hQ _ _ e φ hq)) _
    fun S u hp ↦ ?_)⟩
  have k1 := hz _ _ _ _ e φ ψ u hq
  have k2 := hh T T' e φ hq S (ψ ≫ u) (by rwa [hact])
  have k3 := hh T T'' e (φ ≫ ψ) hq S u (by rwa [hact])
  have k4 := hh T' T'' _ ψ (hQ _ _ e φ hq) S u hp
  simp only [map_sub, map_add, hact, Category.assoc, mp_comp] at k2 k3 ⊢
  linear_combination k2 - k3 + k4 - k1

open Classical in

/- English proof (translation)
Rewrite using `[injective_iff_map_eq_zero]`. Introduce `c hc`. Take `⟨z, rfl⟩` from `H2.mk_surjective F c`. Rewrite `hc` using `[CoefMap.pullCohomologyTwo_class, H2.mk_eq_zero]`. Take `⟨f, hf⟩` from `hc`.

Take `⟨h, hh⟩` from `coboundary_of_restrict F (E := fun _ ↦ PUnit.{1}) (fun e _ ↦ e) (fun _ _ _ ↦ rfl) (fun _ _ ↦ True) (fun S _ ↦ P S) (fun _ _ _ _ _ ↦ trivial) (fun S _ _ ↦ sep S) (fun S _ _ ↦ glue S) (fun S _ _ ↦ van S) (fun S S' S'' _ ψ χ ↦ z.1 S S' S'' ψ χ) (fun _ _ _ _ _ ψ χ ω _ ↦ z.2 ψ χ ω) (f …`. Simplify using `only [dif_pos hp, dif_pos (hP _ _ ψ hp)]`. Conclude with `congrFun (congrFun (congrFun (congrFun (congrFun hf ⟨S, hp⟩) ⟨S', hP _ _ ψ hp⟩) ⟨S'', hP _ _ χ (hP _ _ ψ hp)⟩) (ObjectProperty.homMk ψ)) (ObjectProperty.homMk χ)`. Use `H2.mk_eq_zero.2 ⟨fun S S' ψ ↦ h S S' PUnit.unit ψ, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `S S' S'' ψ χ`.

Conclude with `hh S S' S'' PUnit.unit ψ χ trivial`.
-/
theorem pull_restrict_small_injective (P : ObjectProperty C) (hP : ∀ S S', (S ⟶ S') → P S → P S')
    (sep : ∀ T, Sep F fun S (_ : T ⟶ S) ↦ P S) (glue : ∀ T, Glue F fun S (_ : T ⟶ S) ↦ P S)
    (van : ∀ T, Van1 F fun S (_ : T ⟶ S) ↦ P S) :
    Function.Injective (CoefMap.restrict F P.ι).pull2 := by
  rw [injective_iff_map_eq_zero]
  intro c hc
  obtain ⟨z, rfl⟩ := H2.mk_surjective F c
  rw [CoefMap.pullCohomologyTwo_class, H2.mk_eq_zero] at hc
  obtain ⟨f, hf⟩ := hc
  obtain ⟨h, hh⟩ := coboundary_of_restrict F (E := fun _ ↦ PUnit.{1}) (fun e _ ↦ e) (fun _ _ _ ↦ rfl)
    (fun _ _ ↦ True) (fun S _ ↦ P S) (fun _ _ _ _ _ ↦ trivial) (fun S _ _ ↦ sep S)
    (fun S _ _ ↦ glue S) (fun S _ _ ↦ van S) (fun S S' S'' _ ψ χ ↦ z.1 S S' S'' ψ χ)
    (fun _ _ _ _ _ ψ χ ω _ ↦ z.2 ψ χ ω)
    (fun S S' _ ψ ↦ if h : P S then f ⟨S, h⟩ ⟨S', hP _ _ ψ h⟩ (ObjectProperty.homMk ψ) else 0)
    fun S S' S'' _ ψ χ hp ↦ by
      simp only [dif_pos hp, dif_pos (hP _ _ ψ hp)]
      exact congrFun (congrFun (congrFun (congrFun (congrFun hf ⟨S, hp⟩) ⟨S', hP _ _ ψ hp⟩)
        ⟨S'', hP _ _ χ (hP _ _ ψ hp)⟩) (ObjectProperty.homMk ψ)) (ObjectProperty.homMk χ)
  refine H2.mk_eq_zero.2 ⟨fun S S' ψ ↦ h S S' PUnit.unit ψ, ?_⟩
  funext S S' S'' ψ χ
  exact hh S S' S'' PUnit.unit ψ χ trivial

open Classical in

/- English proof (translation)
Introduce `c`. Take `⟨y, rfl⟩` from `H2.mk_surjective _ c`. Choose the witnesses or unpack the hypotheses as in `⟨z, hz, hy⟩ : ∃ z : C2 F, (∀ S S' S'' S''' ψ χ ω, P S → mp F ω (z S S' S'' ψ χ) + z S S'' S''' (ψ ≫ χ) ω = z S S' S''' ψ (χ ≫ ω) + z S' S'' S''' χ ω) ∧ ∀ S S' S'' ψ χ, y.1 S S' S'' ψ χ = z S.obj S'.obj S''.obj ψ.hom χ.hom := by`. Use `⟨fun S S' S'' ψ χ ↦ if h : P S then y.1 ⟨S, h⟩ ⟨S', hP _ _ ψ h⟩ ⟨S'', hP _ _ χ (hP _ _ ψ h)⟩ (ObjectProperty.homMk ψ) (ObjectProperty.homMk χ) else 0, fun S S' S'' S''' ψ χ ω hp ↦ ?_, fun S S' S'' ψ χ ↦ ?_⟩` and prove the remaining obligations. Simplify using `only [dif_pos hp, dif_pos (hP _ _ ψ hp)]`.

Conclude with `y.2 (T := ⟨S, hp⟩) (T' := ⟨S', hP _ _ ψ hp⟩) (T'' := ⟨S'', hP _ _ χ (hP _ _ ψ hp)⟩) (T''' := ⟨S''', hP _ _ ω (hP _ _ χ (hP _ _ ψ hp))⟩) (ObjectProperty.homMk ψ) (ObjectProperty.homMk χ) (ObjectProperty.homMk ω)`. Simplify using `only [dif_pos S.property]`. Both sides reduce to the same expression. Establish `h1 : ∀ T, ∃ a : ∀ S S', (T ⟶ S) → (S ⟶ S') → F.obj S', (∀ S S' S'' u ψ χ, P S → mp F χ (a S S' u ψ) - a S S'' u (ψ ≫ χ) + a S' S'' (u ≫ ψ) χ = z S S' S'' ψ χ) ∧ (P T → a = z T)`. Introduce `T`.

Distinguish the cases in `hp : P T`. Conclude with `⟨z T, fun S S' S'' u ψ χ _ ↦ by linear_combination hz _ _ _ _ u ψ χ hp, fun _ ↦ rfl⟩`. Take `⟨a, ha⟩` from `van2 T (fun S S' S'' _ ψ χ ↦ z S S' S'' ψ χ) fun _ _ _ _ _ ψ χ ω h ↦ hz _ _ _ _ ψ χ ω h`. Conclude with `⟨a, ha, fun h ↦ absurd h hp⟩`. Use `choose a ha ha' using h1`.

Establish `h2 : ∀ T T' (φ : T ⟶ T'), ∃ b : ∀ S, (T' ⟶ S) → F.obj S, (∀ S S' u ψ, P S → b S' (u ≫ ψ) - mp F ψ (b S u) = a T S S' (φ ≫ u) ψ - a T' S S' u ψ) ∧ (P T → ∀ S u, b S u = z T T' S φ u)`. Introduce `T T' φ`. Distinguish the cases in `hp : P T`. Use `⟨fun S u ↦ z T T' S φ u, fun S S' u ψ _ ↦ ?_, fun _ _ _ ↦ rfl⟩` and prove the remaining obligations. Rewrite using `[ha' T hp, ha' T' (hP _ _ φ hp)]`.

Take the linear combination `-hz _ _ _ _ φ u ψ hp`. Take `⟨b, hb⟩` from `van T' (fun S S' u ψ ↦ a T S S' (φ ≫ u) ψ - a T' S S' u ψ) fun S S' S'' u ψ χ h ↦ by`. Establish `k1` using `ha T _ _ _ (φ ≫ u) ψ χ h`. Establish `k2` using `ha T' _ _ _ u ψ χ h`. Simplify using `only [map_sub, Category.assoc] at k1 ⊢`.

Take the linear combination `k2 - k1`. Conclude with `⟨b, hb, fun h ↦ absurd h hp⟩`. Use `choose b hb hb' using h2`. Establish `h3 : ∀ T T' T'' (φ : T ⟶ T') (ψ : T' ⟶ T''), ∃ x : F.obj T'', ∀ S (u : T'' ⟶ S), P S → mp F u x = b T T' φ S (ψ ≫ u) + b T' T'' ψ S u - b T T'' (φ ≫ ψ) S u`. Introduce `T T' T'' φ ψ`.

Use `glue T'' _ fun S S' u χ hp ↦ ?_` and prove the remaining obligations. Establish `k1` using `hb T T' φ _ _ (ψ ≫ u) χ hp`. Establish `k2` using `hb T' T'' ψ _ _ u χ hp`. Establish `k3` using `hb T T'' (φ ≫ ψ) _ _ u χ hp`. Simplify using `only [map_sub, map_add, Category.assoc] at k1 k3 ⊢`.

Take the linear combination `k1 + k2 - k3`. Use `choose c hc using h3`. Use `⟨H2.mk F ⟨c, fun T T' T'' T''' φ ψ χ ↦ sub_eq_zero.1 (sep T''' _ fun S u hp ↦ ?_)⟩, ?_⟩` and prove the remaining obligations. Establish `k1` using `hc _ _ _ φ ψ S (χ ≫ u) hp`. Establish `k2` using `hc _ _ _ (φ ≫ ψ) χ S u hp`.

Establish `k3` using `hc _ _ _ φ (ψ ≫ χ) S u hp`. Establish `k4` using `hc _ _ _ ψ χ S u hp`. Simplify using `only [map_sub, map_add, Category.assoc, mp_comp] at k1 k2 k3 ⊢`. Take the linear combination `k1 + k2 - k3 - k4`. Rewrite using `[CoefMap.pullCohomologyTwo_class]`.

Use `congr 1`. Use `Subtype.ext ?_` and prove the remaining obligations. Use function extensionality and compare the values at `S S' S'' ψ χ`. Establish `k1` using `hc _ _ _ ψ.hom χ.hom _ (𝟙 _) S''.property`. Establish `k2` using `hz _ _ _ _ ψ.hom χ.hom (𝟙 _) S.property`.

Rewrite `k1` using `[hb' _ _ _ S.property, hb' _ _ _ S.property, hb' _ _ _ S'.property, mp_id]`. Rewrite `k2` using `[mp_id]`. Rewrite using `[hy]`. Express the relevant statement in the definitionally equal form `c _ _ _ ψ.hom χ.hom = _`. Take the linear combination `k1 - k2`.
-/
theorem descent_H2_surjective (P : ObjectProperty C) (hP : ∀ S S', (S ⟶ S') → P S → P S')
    (sep : ∀ T, Sep F fun S (_ : T ⟶ S) ↦ P S) (glue : ∀ T, Glue F fun S (_ : T ⟶ S) ↦ P S)
    (van : ∀ T, Van1 F fun S (_ : T ⟶ S) ↦ P S) (van2 : ∀ T, Van2 F fun S (_ : T ⟶ S) ↦ P S) :
    Function.Surjective (CoefMap.restrict F P.ι).pull2 := by
  intro c
  obtain ⟨y, rfl⟩ := H2.mk_surjective _ c
  obtain ⟨z, hz, hy⟩ : ∃ z : C2 F, (∀ S S' S'' S''' ψ χ ω, P S →
      mp F ω (z S S' S'' ψ χ) + z S S'' S''' (ψ ≫ χ) ω = z S S' S''' ψ (χ ≫ ω) + z S' S'' S''' χ ω) ∧
      ∀ S S' S'' ψ χ, y.1 S S' S'' ψ χ = z S.obj S'.obj S''.obj ψ.hom χ.hom := by
    refine ⟨fun S S' S'' ψ χ ↦ if h : P S then y.1 ⟨S, h⟩ ⟨S', hP _ _ ψ h⟩ ⟨S'', hP _ _ χ (hP _ _ ψ h)⟩
      (ObjectProperty.homMk ψ) (ObjectProperty.homMk χ) else 0, fun S S' S'' S''' ψ χ ω hp ↦ ?_,
      fun S S' S'' ψ χ ↦ ?_⟩
    · simp only [dif_pos hp, dif_pos (hP _ _ ψ hp)]
      exact y.2 (T := ⟨S, hp⟩) (T' := ⟨S', hP _ _ ψ hp⟩) (T'' := ⟨S'', hP _ _ χ (hP _ _ ψ hp)⟩)
        (T''' := ⟨S''', hP _ _ ω (hP _ _ χ (hP _ _ ψ hp))⟩) (ObjectProperty.homMk ψ)
        (ObjectProperty.homMk χ) (ObjectProperty.homMk ω)
    · simp only [dif_pos S.property]
      rfl
  have h1 : ∀ T, ∃ a : ∀ S S', (T ⟶ S) → (S ⟶ S') → F.obj S', (∀ S S' S'' u ψ χ, P S →
      mp F χ (a S S' u ψ) - a S S'' u (ψ ≫ χ) + a S' S'' (u ≫ ψ) χ = z S S' S'' ψ χ) ∧
      (P T → a = z T) := by
    intro T
    by_cases hp : P T
    · exact ⟨z T, fun S S' S'' u ψ χ _ ↦ by linear_combination hz _ _ _ _ u ψ χ hp, fun _ ↦ rfl⟩
    · obtain ⟨a, ha⟩ := van2 T (fun S S' S'' _ ψ χ ↦ z S S' S'' ψ χ)
        fun _ _ _ _ _ ψ χ ω h ↦ hz _ _ _ _ ψ χ ω h
      exact ⟨a, ha, fun h ↦ absurd h hp⟩
  choose a ha ha' using h1
  have h2 : ∀ T T' (φ : T ⟶ T'), ∃ b : ∀ S, (T' ⟶ S) → F.obj S, (∀ S S' u ψ, P S →
      b S' (u ≫ ψ) - mp F ψ (b S u) = a T S S' (φ ≫ u) ψ - a T' S S' u ψ) ∧
      (P T → ∀ S u, b S u = z T T' S φ u) := by
    intro T T' φ
    by_cases hp : P T
    · refine ⟨fun S u ↦ z T T' S φ u, fun S S' u ψ _ ↦ ?_, fun _ _ _ ↦ rfl⟩
      rw [ha' T hp, ha' T' (hP _ _ φ hp)]
      linear_combination -hz _ _ _ _ φ u ψ hp
    · obtain ⟨b, hb⟩ := van T' (fun S S' u ψ ↦ a T S S' (φ ≫ u) ψ - a T' S S' u ψ)
        fun S S' S'' u ψ χ h ↦ by
          have k1 := ha T _ _ _ (φ ≫ u) ψ χ h
          have k2 := ha T' _ _ _ u ψ χ h
          simp only [map_sub, Category.assoc] at k1 ⊢
          linear_combination k2 - k1
      exact ⟨b, hb, fun h ↦ absurd h hp⟩
  choose b hb hb' using h2
  have h3 : ∀ T T' T'' (φ : T ⟶ T') (ψ : T' ⟶ T''), ∃ x : F.obj T'', ∀ S (u : T'' ⟶ S), P S →
      mp F u x = b T T' φ S (ψ ≫ u) + b T' T'' ψ S u - b T T'' (φ ≫ ψ) S u := by
    intro T T' T'' φ ψ
    refine glue T'' _ fun S S' u χ hp ↦ ?_
    have k1 := hb T T' φ _ _ (ψ ≫ u) χ hp
    have k2 := hb T' T'' ψ _ _ u χ hp
    have k3 := hb T T'' (φ ≫ ψ) _ _ u χ hp
    simp only [map_sub, map_add, Category.assoc] at k1 k3 ⊢
    linear_combination k1 + k2 - k3
  choose c hc using h3
  refine ⟨H2.mk F ⟨c, fun T T' T'' T''' φ ψ χ ↦ sub_eq_zero.1 (sep T''' _ fun S u hp ↦ ?_)⟩, ?_⟩
  · have k1 := hc _ _ _ φ ψ S (χ ≫ u) hp
    have k2 := hc _ _ _ (φ ≫ ψ) χ S u hp
    have k3 := hc _ _ _ φ (ψ ≫ χ) S u hp
    have k4 := hc _ _ _ ψ χ S u hp
    simp only [map_sub, map_add, Category.assoc, mp_comp] at k1 k2 k3 ⊢
    linear_combination k1 + k2 - k3 - k4
  · rw [CoefMap.pullCohomologyTwo_class]
    congr 1
    refine Subtype.ext ?_
    funext S S' S'' ψ χ
    have k1 := hc _ _ _ ψ.hom χ.hom _ (𝟙 _) S''.property
    have k2 := hz _ _ _ _ ψ.hom χ.hom (𝟙 _) S.property
    rw [hb' _ _ _ S.property, hb' _ _ _ S.property, hb' _ _ _ S'.property, mp_id] at k1
    rw [mp_id] at k2
    rw [hy]
    change c _ _ _ ψ.hom χ.hom = _
    linear_combination k1 - k2

section Refine

variable {F} {T : C} {P Q : ∀ S, (T ⟶ S) → Prop} (hPQ : ∀ S u, P S u → Q S u)
  (hQ : ∀ S S' u (ψ : S ⟶ S'), Q S u → Q S' (u ≫ ψ))
  (sep : ∀ S u, Q S u → Sep F fun S' (ψ : S ⟶ S') ↦ P S' (u ≫ ψ))
  (glue : ∀ S u, Q S u → Glue F fun S' (ψ : S ⟶ S') ↦ P S' (u ≫ ψ))
  (van : ∀ S u, Q S u → Van1 F fun S' (ψ : S ⟶ S') ↦ P S' (u ≫ ψ))

include hPQ in

/- English proof (translation)
The claim follows from `fun x hx ↦ h x fun S u hp ↦ hx S u (hPQ S u hp)`.
-/
theorem Sep.mono (h : Sep F P) : Sep F Q := fun x hx ↦ h x fun S u hp ↦ hx S u (hPQ S u hp)

include hPQ sep in

/- English proof (translation)
Introduce `s hs`. Take `⟨x, hx⟩` from `h s fun S S' u ψ hp ↦ hs S S' u ψ (hPQ S u hp)`. Use `⟨x, fun S u hq ↦ sub_eq_zero.1 (sep S u hq _ fun S' ψ hp ↦ ?_)⟩` and prove the remaining obligations. Rewrite using `[map_sub, ← mp_comp, hx _ _ hp, hs _ _ _ _ hq, sub_self]`.
-/
theorem Glue.mono (h : Glue F P) : Glue F Q := by
  intro s hs
  obtain ⟨x, hx⟩ := h s fun S S' u ψ hp ↦ hs S S' u ψ (hPQ S u hp)
  refine ⟨x, fun S u hq ↦ sub_eq_zero.1 (sep S u hq _ fun S' ψ hp ↦ ?_)⟩
  rw [map_sub, ← mp_comp, hx _ _ hp, hs _ _ _ _ hq, sub_self]

include hPQ hQ sep glue in

/- English proof (translation)
Introduce `a ha`. Take `⟨b, hb⟩` from `h a fun S S' S'' u ψ χ hp ↦ ha S S' S'' u ψ χ (hPQ S u hp)`. Establish `h1 : ∀ S (u : T ⟶ S), ∃ x : F.obj S, Q S u → ∀ S' (ψ : S ⟶ S'), P S' (u ≫ ψ) → mp F ψ x = b S' (u ≫ ψ) - a S S' u ψ`. Introduce `S u`. Distinguish the cases in `hq : Q S u`.

Take `⟨x, hx⟩` from `glue S u hq (fun S' ψ ↦ b S' (u ≫ ψ) - a S S' u ψ) fun S' S'' ψ χ hp ↦ by`. Establish `k1` using `ha _ _ _ u ψ χ hq`. Establish `k2` using `hb _ _ (u ≫ ψ) χ hp`. Simplify using `only [map_sub, Category.assoc] at k2 ⊢`. Take the linear combination `k2 - k1`.

Conclude with `⟨x, fun _ ↦ hx⟩`. Conclude with `⟨0, fun h ↦ absurd h hq⟩`. Use `choose x hx using h1`. Use `⟨x, fun S S' u ψ hq ↦ sub_eq_zero.1 (sep S' _ (hQ _ _ u ψ hq) _ fun S'' χ hp ↦ ?_)⟩` and prove the remaining obligations. Establish `k1` using `ha _ _ _ u ψ χ hq`.

Establish `k2` using `hx _ _ (hQ _ _ u ψ hq) _ χ hp`. Establish `k3` using `hx _ _ hq _ (ψ ≫ χ) (by rwa [← Category.assoc])`. Simplify using `only [map_sub, Category.assoc, mp_comp] at k2 k3 ⊢`. Take the linear combination `k2 - k3 + k1`.
-/
theorem Van1.mono (h : Van1 F P) : Van1 F Q := by
  intro a ha
  obtain ⟨b, hb⟩ := h a fun S S' S'' u ψ χ hp ↦ ha S S' S'' u ψ χ (hPQ S u hp)
  have h1 : ∀ S (u : T ⟶ S), ∃ x : F.obj S, Q S u → ∀ S' (ψ : S ⟶ S'), P S' (u ≫ ψ) →
      mp F ψ x = b S' (u ≫ ψ) - a S S' u ψ := by
    intro S u
    by_cases hq : Q S u
    · obtain ⟨x, hx⟩ := glue S u hq (fun S' ψ ↦ b S' (u ≫ ψ) - a S S' u ψ) fun S' S'' ψ χ hp ↦ by
        have k1 := ha _ _ _ u ψ χ hq
        have k2 := hb _ _ (u ≫ ψ) χ hp
        simp only [map_sub, Category.assoc] at k2 ⊢
        linear_combination k2 - k1
      exact ⟨x, fun _ ↦ hx⟩
    · exact ⟨0, fun h ↦ absurd h hq⟩
  choose x hx using h1
  refine ⟨x, fun S S' u ψ hq ↦ sub_eq_zero.1 (sep S' _ (hQ _ _ u ψ hq) _ fun S'' χ hp ↦ ?_)⟩
  have k1 := ha _ _ _ u ψ χ hq
  have k2 := hx _ _ (hQ _ _ u ψ hq) _ χ hp
  have k3 := hx _ _ hq _ (ψ ≫ χ) (by rwa [← Category.assoc])
  simp only [map_sub, Category.assoc, mp_comp] at k2 k3 ⊢
  linear_combination k2 - k3 + k1

include hPQ hQ sep glue van in

/- English proof (translation)
Introduce `z hz`. Take `⟨f, hf⟩` from `h z fun S S' S'' S''' u ψ χ ω hp ↦ hz S S' S'' S''' u ψ χ ω (hPQ S u hp)`. Conclude with `coboundary_of_restrict F (E := fun S ↦ T ⟶ S) (fun u ψ ↦ u ≫ ψ) (fun _ _ _ ↦ (Category.assoc _ _ _).symm) Q P hQ sep glue van z hz f hf`.
-/
theorem Van2.mono (h : Van2 F P) : Van2 F Q := by
  intro z hz
  obtain ⟨f, hf⟩ := h z fun S S' S'' S''' u ψ χ ω hp ↦ hz S S' S'' S''' u ψ χ ω (hPQ S u hp)
  exact coboundary_of_restrict F (E := fun S ↦ T ⟶ S) (fun u ψ ↦ u ≫ ψ)
    (fun _ _ _ ↦ (Category.assoc _ _ _).symm) Q P hQ sep glue van z hz f hf

end Refine

def HasLoc : Prop := ∀ (T : C) (b : F.obj T), ∃ (T' : C) (l : T ⟶ T'), IsUnit (mp F l b) ∧
  (∀ y : F.obj T', ∃ (n : ℕ) (x : F.obj T), y * mp F l b ^ n = mp F l x) ∧
  (∀ x : F.obj T, mp F l x = 0 → ∃ n : ℕ, b ^ n * x = 0) ∧
  ∀ (S : C) (u : T ⟶ S), IsUnit (mp F u b) → ∃! v : T' ⟶ S, l ≫ v = u

section Basic

variable {F} (H : HasLoc F) {T : C} {P : ∀ S, (T ⟶ S) → Prop} {b : F.obj T}
  (hP : ∀ S u, P S u ↔ IsUnit (mp F u b))

include H hP in

/- English proof (translation)
Take `⟨T', l, h1, -, -, h4⟩` from `H T b`. Use `choose p hp hp' using h4`. Use `⟨T', l, fun S u h ↦ p S u ((hP _ _).1 h), (hP _ _).2 h1, fun S u h ↦ hp _ _ _, fun S S' u ψ h ↦ ⟨(hP _ _).2 ?_, (hp' _ _ _ _ ?_).symm⟩⟩` and prove the remaining obligations. Rewrite using `[mp_comp]`. Conclude with `((hP _ _).1 h).map _`.

Use `beta_reduce`. Rewrite using `[← Category.assoc, hp]`.
-/
theorem exists_initial : ∃ (T' : C) (l : T ⟶ T') (p : ∀ S (u : T ⟶ S), P S u → (T' ⟶ S)), P T' l ∧
    (∀ S u h, l ≫ p S u h = u) ∧
    ∀ S S' u (ψ : S ⟶ S') h, ∃ h', p S' (u ≫ ψ) h' = p S u h ≫ ψ := by
  obtain ⟨T', l, h1, -, -, h4⟩ := H T b
  choose p hp hp' using h4
  refine ⟨T', l, fun S u h ↦ p S u ((hP _ _).1 h), (hP _ _).2 h1, fun S u h ↦ hp _ _ _,
    fun S S' u ψ h ↦ ⟨(hP _ _).2 ?_, (hp' _ _ _ _ ?_).symm⟩⟩
  · rw [mp_comp]; exact ((hP _ _).1 h).map _
  · beta_reduce
    rw [← Category.assoc, hp]

open Classical in
include H hP in

/- English proof (translation)
Take `⟨T', l, p, hl, h1, h2⟩` from `exists_initial H hP`. Introduce `a ha`. Use `⟨fun S u ↦ if h : P S u then a T' S l (p S u h) else 0, fun S S' u ψ h ↦ ?_⟩` and prove the remaining obligations. Take `⟨h', e⟩` from `h2 S S' u ψ h`. Simplify using `only [dif_pos h, dif_pos h', e]`.

Rewrite using `[ha _ _ _ _ _ _ hl, h1, add_sub_cancel_left]`.
-/
theorem vanishing_H1_inverting_morphisms : Van1 F P := by
  obtain ⟨T', l, p, hl, h1, h2⟩ := exists_initial H hP
  intro a ha
  refine ⟨fun S u ↦ if h : P S u then a T' S l (p S u h) else 0, fun S S' u ψ h ↦ ?_⟩
  obtain ⟨h', e⟩ := h2 S S' u ψ h
  simp only [dif_pos h, dif_pos h', e]
  rw [ha _ _ _ _ _ _ hl, h1, add_sub_cancel_left]

open Classical in
include H hP in

/- English proof (translation)
Take `⟨T', l, p, hl, h1, h2⟩` from `exists_initial H hP`. Introduce `z hz`. Use `⟨fun S S' u ψ ↦ if h : P S u then z T' S S' l (p S u h) ψ else 0, fun S S' S'' u ψ χ h ↦ ?_⟩` and prove the remaining obligations. Take `⟨h', e⟩` from `h2 S S' u ψ h`. Simplify using `only [dif_pos h, dif_pos h', e]`.

Use `hz _ _ _ _ l (p S u h) ψ χ hl` as an intermediate fact. Rewrite `this` using `[h1]`. Take the linear combination `this`.
-/
theorem vanishing_H2_inverting_morphisms : Van2 F P := by
  obtain ⟨T', l, p, hl, h1, h2⟩ := exists_initial H hP
  intro z hz
  refine ⟨fun S S' u ψ ↦ if h : P S u then z T' S S' l (p S u h) ψ else 0,
    fun S S' S'' u ψ χ h ↦ ?_⟩
  obtain ⟨h', e⟩ := h2 S S' u ψ h
  simp only [dif_pos h, dif_pos h', e]
  have := hz _ _ _ _ l (p S u h) ψ χ hl
  rw [h1] at this
  linear_combination this

include H hP in

/- English proof (translation)
Take `⟨T', l, h1, h2, -, h4⟩` from `H T b`. Take `⟨n, x, e⟩` from `h2 (s T' l)`. Use `⟨n, x, fun S u h ↦ ?_⟩` and prove the remaining obligations. Take `⟨v, rfl, -⟩` from `h4 S u ((hP _ _).1 h)`. Rewrite using `[hs _ _ _ _ ((hP _ _).2 h1), mp_comp, mp_comp, ← e, map_mul, map_pow]`.
-/
theorem IsSec.frac {s : ∀ S, (T ⟶ S) → F.obj S} (hs : IsSec F P s) :
    ∃ (n : ℕ) (x : F.obj T), ∀ S u, P S u → s S u * mp F u b ^ n = mp F u x := by
  obtain ⟨T', l, h1, h2, -, h4⟩ := H T b
  obtain ⟨n, x, e⟩ := h2 (s T' l)
  refine ⟨n, x, fun S u h ↦ ?_⟩
  obtain ⟨v, rfl, -⟩ := h4 S u ((hP _ _).1 h)
  rw [hs _ _ _ _ ((hP _ _).2 h1), mp_comp, mp_comp, ← e, map_mul, map_pow]

include H hP in

/- English proof (translation)
Take `⟨n, x, e⟩` from `hs.frac H (b := b * c) fun S u ↦ by rw [hP, map_mul, IsUnit.mul_iff]`. Use `eventually_atTop.2 ⟨n, fun N hN ↦ ?_⟩` and prove the remaining obligations. Take `⟨m, rfl⟩` from `Nat.exists_eq_add_of_le hN`. Use `⟨fun S u ↦ mp F u x * Ring.inverse (mp F u b) ^ n * mp F u c ^ m, fun S S' u ψ h ↦ ?_, fun S u h h' ↦ ?_⟩` and prove the remaining obligations. Take `⟨y, hy⟩` from `(hP _ _).1 h`.

Establish `: Ring.inverse (mp F ψ y) = mp F ψ (Ring.inverse y)`. Rewrite using `[Ring.inverse_unit]`. Conclude with `Ring.inverse_unit (Units.map (mp F ψ : F.obj S →* F.obj S') y)`. Simplify using `only [mp_comp, map_mul, map_pow, ← hy, this]`. Establish `k` using `Ring.mul_inverse_cancel _ ((hP _ _).1 h)`.

Establish `k' : mp F u b ^ n * Ring.inverse (mp F u b) ^ n = 1` using `by rw [← mul_pow, k, one_pow]`. Use `beta_reduce`. Rewrite using `[← e S u ⟨h, h'⟩, map_mul]`. Take the linear combination `(s S u * mp F u c ^ (n + m)) * k'`.
-/
theorem IsSec.extend (c : F.obj T) {s : ∀ S, (T ⟶ S) → F.obj S}
    (hs : IsSec F (fun S u ↦ P S u ∧ IsUnit (mp F u c)) s) :
    ∀ᶠ N : ℕ in atTop, ∃ s', IsSec F P s' ∧
      ∀ S u, P S u → IsUnit (mp F u c) → s' S u = mp F u c ^ N * s S u := by
  obtain ⟨n, x, e⟩ := hs.frac H (b := b * c) fun S u ↦ by rw [hP, map_mul, IsUnit.mul_iff]
  refine eventually_atTop.2 ⟨n, fun N hN ↦ ?_⟩
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hN
  refine ⟨fun S u ↦ mp F u x * Ring.inverse (mp F u b) ^ n * mp F u c ^ m, fun S S' u ψ h ↦ ?_,
    fun S u h h' ↦ ?_⟩
  · obtain ⟨y, hy⟩ := (hP _ _).1 h
    have : Ring.inverse (mp F ψ y) = mp F ψ (Ring.inverse y) := by
      rw [Ring.inverse_unit]
      exact Ring.inverse_unit (Units.map (mp F ψ : F.obj S →* F.obj S') y)
    simp only [mp_comp, map_mul, map_pow, ← hy, this]
  · have k := Ring.mul_inverse_cancel _ ((hP _ _).1 h)
    have k' : mp F u b ^ n * Ring.inverse (mp F u b) ^ n = 1 := by rw [← mul_pow, k, one_pow]
    beta_reduce
    rw [← e S u ⟨h, h'⟩, map_mul]
    linear_combination (s S u * mp F u c ^ (n + m)) * k'

include H hP in

/- English proof (translation)
Take `⟨n, x, e⟩` from `hs.frac H hP`. Take `⟨T', l, h1, -, h3, -⟩` from `H T (b * c)`. Rewrite `h1` using `[map_mul, IsUnit.mul_iff]`. Take `⟨m, hm⟩` from `h3 x (by rw [← e _ _ ((hP _ _).2 h1.1), h0 _ _ ((hP _ _).2 h1.1) h1.2, zero_mul])`. Use `eventually_atTop.2 ⟨m, fun N hN S u h ↦ ?_⟩` and prove the remaining obligations.

Take `⟨k, rfl⟩` from `Nat.exists_eq_add_of_le hN`. Use `congrArg (mp F u) hm` as an intermediate fact. Rewrite `this` using `[map_mul, map_pow, map_mul, map_zero, ← e S u h]`. Use `((((hP _ _).1 h).pow (m + n)).mul_right_eq_zero).1 ?_` and prove the remaining obligations. Take the linear combination `mp F u c ^ k * this`.
-/
theorem IsSec.kill (c : F.obj T) {s : ∀ S, (T ⟶ S) → F.obj S} (hs : IsSec F P s)
    (h0 : ∀ S u, P S u → IsUnit (mp F u c) → s S u = 0) :
    ∀ᶠ M : ℕ in atTop, ∀ S u, P S u → mp F u c ^ M * s S u = 0 := by
  obtain ⟨n, x, e⟩ := hs.frac H hP
  obtain ⟨T', l, h1, -, h3, -⟩ := H T (b * c)
  rw [map_mul, IsUnit.mul_iff] at h1
  obtain ⟨m, hm⟩ := h3 x (by rw [← e _ _ ((hP _ _).2 h1.1), h0 _ _ ((hP _ _).2 h1.1) h1.2, zero_mul])
  refine eventually_atTop.2 ⟨m, fun N hN S u h ↦ ?_⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hN
  have := congrArg (mp F u) hm
  rw [map_mul, map_pow, map_mul, map_zero, ← e S u h] at this
  refine ((((hP _ _).1 h).pow (m + n)).mul_right_eq_zero).1 ?_
  linear_combination mp F u c ^ k * this

end Basic

section Cech

variable {F} (H : HasLoc F) {T : C} {ι : Type} [Fintype ι] {b : ι → F.obj T}
  (hb : Ideal.span (Set.range b) = ⊤)

include hb in

/- English proof (translation)
Use `Ideal.span_pow_eq_top _ hb N` as an intermediate fact. Rewrite `this` using `[← Set.range_comp, Ideal.eq_top_iff_one, Ideal.mem_span_range_iff_exists_fun]`. Take `⟨r, hr⟩` from `this`. Use `⟨r, fun S u ↦ ?_⟩` and prove the remaining obligations. Simplify using `using congrArg (mp F u) hr`.
-/
theorem exists_partition (N : ℕ) : ∃ r : ι → F.obj T, ∀ S (u : T ⟶ S),
    ∑ l, mp F u (r l) * mp F u (b l) ^ N = 1 := by
  have := Ideal.span_pow_eq_top _ hb N
  rw [← Set.range_comp, Ideal.eq_top_iff_one, Ideal.mem_span_range_iff_exists_fun] at this
  obtain ⟨r, hr⟩ := this
  refine ⟨r, fun S u ↦ ?_⟩
  simpa using congrArg (mp F u) hr

include H hb in

/- English proof (translation)
Introduce `x hx`. Take `⟨M, hM⟩` from `(eventually_all.2 fun l ↦ IsSec.kill H (P := fun _ _ ↦ True) (b := 1) (by simp) (b l) (s := fun S u ↦ mp F u x) (fun _ _ _ _ _ ↦ mp_comp F _ _ _) fun S u _ h ↦ hx S u ⟨l, h⟩).exists`. Take `⟨r, hr⟩` from `exists_partition hb M`. Rewrite using `[← mp_id F T x, ← one_mul (mp F _ x), ← hr T (𝟙 T), Finset.sum_mul]`. Conclude with `Finset.sum_eq_zero fun l _ ↦ by rw [mul_assoc, hM l T _ trivial, mul_zero]`.
-/
theorem sep_std : Sep F fun S (u : T ⟶ S) ↦ ∃ i, IsUnit (mp F u (b i)) := by
  intro x hx
  obtain ⟨M, hM⟩ := (eventually_all.2 fun l ↦ IsSec.kill H (P := fun _ _ ↦ True) (b := 1)
    (by simp) (b l) (s := fun S u ↦ mp F u x) (fun _ _ _ _ _ ↦ mp_comp F _ _ _)
    fun S u _ h ↦ hx S u ⟨l, h⟩).exists
  obtain ⟨r, hr⟩ := exists_partition hb M
  rw [← mp_id F T x, ← one_mul (mp F _ x), ← hr T (𝟙 T), Finset.sum_mul]
  exact Finset.sum_eq_zero fun l _ ↦ by rw [mul_assoc, hM l T _ trivial, mul_zero]

include H hb in

/- English proof (translation)
Introduce `s hs`. Take `⟨N, hN⟩` from `(eventually_all.2 fun l ↦ IsSec.extend H (P := fun _ _ ↦ True) (b := 1) (by simp) (b l) (s := s) fun S S' u ψ h ↦ hs S S' u ψ ⟨l, h.2⟩).exists`. Use `choose h hh hh' using hN`. Take `⟨M, hM⟩` from `(eventually_all.2 fun l ↦ eventually_all.2 fun i ↦ IsSec.kill H (P := fun S u ↦ IsUnit (mp F u (b i))) (b := b i) (fun _ _ ↦ Iff.rfl) (b l) (s := fun S u ↦ mp F u (b l) ^ N * s S u - h l S u) (fun S S' u ψ hu ↦ by`. Simplify using `only [hs S S' u ψ ⟨i, hu⟩, hh l S S' u ψ trivial, mp_comp, map_sub, map_mul, map_pow])`.

Use `fun S u _ hl ↦ by rw [hh' l S u trivial hl, sub_self]).exists`. Take `⟨r, hr⟩` from `exists_partition hb (M + N)`. Use `⟨∑ l, r l * b l ^ M * h l T (𝟙 T), fun S u ⟨i, hi⟩ ↦ ?_⟩` and prove the remaining obligations. Rewrite using `[← one_mul (s S u), ← hr S u, Finset.sum_mul, map_sum]`. Use `Finset.sum_congr rfl fun l _ ↦ ?_` and prove the remaining obligations.

Rewrite using `[map_mul, map_mul, map_pow, ← hh l _ _ _ u trivial, Category.id_comp]`. Take the linear combination `-mp F u (r l) * hM l i S u hi`.
-/
theorem glue_std : Glue F fun S (u : T ⟶ S) ↦ ∃ i, IsUnit (mp F u (b i)) := by
  intro s hs
  obtain ⟨N, hN⟩ := (eventually_all.2 fun l ↦ IsSec.extend H (P := fun _ _ ↦ True) (b := 1)
    (by simp) (b l) (s := s) fun S S' u ψ h ↦ hs S S' u ψ ⟨l, h.2⟩).exists
  choose h hh hh' using hN
  obtain ⟨M, hM⟩ := (eventually_all.2 fun l ↦ eventually_all.2 fun i ↦
    IsSec.kill H (P := fun S u ↦ IsUnit (mp F u (b i))) (b := b i) (fun _ _ ↦ Iff.rfl) (b l)
      (s := fun S u ↦ mp F u (b l) ^ N * s S u - h l S u)
      (fun S S' u ψ hu ↦ by
        simp only [hs S S' u ψ ⟨i, hu⟩, hh l S S' u ψ trivial, mp_comp, map_sub, map_mul, map_pow])
      fun S u _ hl ↦ by rw [hh' l S u trivial hl, sub_self]).exists
  obtain ⟨r, hr⟩ := exists_partition hb (M + N)
  refine ⟨∑ l, r l * b l ^ M * h l T (𝟙 T), fun S u ⟨i, hi⟩ ↦ ?_⟩
  rw [← one_mul (s S u), ← hr S u, Finset.sum_mul, map_sum]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  rw [map_mul, map_mul, map_pow, ← hh l _ _ _ u trivial, Category.id_comp]
  linear_combination -mp F u (r l) * hM l i S u hi

include H hb in

/- English proof (translation)
Take `⟨N, hN⟩` from `(eventually_all.2 fun l ↦ eventually_all.2 fun i ↦ IsSec.extend H (P := fun S u ↦ IsUnit (mp F u (b i))) (b := b i) (fun _ _ ↦ Iff.rfl) (b l) (s := c l i) fun S S' u ψ h ↦ hs l i S S' u ψ ⟨h.2, h.1⟩).exists`. Use `choose h hh hh' using hN`. Take `⟨M, hM⟩` from `(eventually_all.2 fun l ↦ eventually_all.2 fun i ↦ eventually_all.2 fun j ↦ IsSec.kill H (P := fun S u ↦ IsUnit (mp F u (b i)) ∧ IsUnit (mp F u (b j))) (b := b i * b j) (fun _ _ ↦ by rw [map_mul, IsUnit.mul_iff]) (b l) (s := fun S u ↦ mp F u (b l) ^ N * c i j S u - (h l j S u - h …`. Simplify using `only [hs i j S S' u ψ hu, hh l i S S' u ψ hu.1, hh l j S S' u ψ hu.2, mp_comp, map_sub, map_mul, map_pow])`. Use `fun S u hu hl ↦ by`.

Rewrite using `[hh' l i S u hu.1 hl, hh' l j S u hu.2 hl]`. Take the linear combination `mp F u (b l) ^ N * hc l i j S u hl hu.1 hu.2).exists`. Take `⟨r, hr⟩` from `exists_partition hb (M + N)`. Use `⟨fun i S u ↦ ∑ l, mp F u (r l * b l ^ M) * h l i S u, fun i S S' u ψ hu ↦ ?_, fun i j S u hi hj ↦ ?_⟩` and prove the remaining obligations. Simplify using `only [map_sum, map_mul, mp_comp, fun l ↦ hh l i S S' u ψ hu]`.

Rewrite using `[← one_mul (c i j S u), ← hr S u, Finset.sum_mul, ← Finset.sum_sub_distrib]`. Use `Finset.sum_congr rfl fun l _ ↦ ?_` and prove the remaining obligations. Rewrite using `[map_mul, map_pow]`. Take the linear combination `mp F u (r l) * hM l i j S u ⟨hi, hj⟩`.
-/
theorem cech1 (c : ι → ι → ∀ S, (T ⟶ S) → F.obj S)
    (hs : ∀ i j, IsSec F (fun S u ↦ IsUnit (mp F u (b i)) ∧ IsUnit (mp F u (b j))) (c i j))
    (hc : ∀ i j k S u, IsUnit (mp F u (b i)) → IsUnit (mp F u (b j)) → IsUnit (mp F u (b k)) →
      c j k S u - c i k S u + c i j S u = 0) :
    ∃ e : ι → ∀ S, (T ⟶ S) → F.obj S, (∀ i, IsSec F (fun S u ↦ IsUnit (mp F u (b i))) (e i)) ∧
      ∀ i j S u, IsUnit (mp F u (b i)) → IsUnit (mp F u (b j)) → c i j S u = e j S u - e i S u := by
  obtain ⟨N, hN⟩ := (eventually_all.2 fun l ↦ eventually_all.2 fun i ↦
    IsSec.extend H (P := fun S u ↦ IsUnit (mp F u (b i))) (b := b i) (fun _ _ ↦ Iff.rfl) (b l)
      (s := c l i) fun S S' u ψ h ↦ hs l i S S' u ψ ⟨h.2, h.1⟩).exists
  choose h hh hh' using hN
  obtain ⟨M, hM⟩ := (eventually_all.2 fun l ↦ eventually_all.2 fun i ↦ eventually_all.2 fun j ↦
    IsSec.kill H (P := fun S u ↦ IsUnit (mp F u (b i)) ∧ IsUnit (mp F u (b j))) (b := b i * b j)
      (fun _ _ ↦ by rw [map_mul, IsUnit.mul_iff]) (b l)
      (s := fun S u ↦ mp F u (b l) ^ N * c i j S u - (h l j S u - h l i S u))
      (fun S S' u ψ hu ↦ by
        simp only [hs i j S S' u ψ hu, hh l i S S' u ψ hu.1, hh l j S S' u ψ hu.2, mp_comp, map_sub,
          map_mul, map_pow])
      fun S u hu hl ↦ by
        rw [hh' l i S u hu.1 hl, hh' l j S u hu.2 hl]
        linear_combination mp F u (b l) ^ N * hc l i j S u hl hu.1 hu.2).exists
  obtain ⟨r, hr⟩ := exists_partition hb (M + N)
  refine ⟨fun i S u ↦ ∑ l, mp F u (r l * b l ^ M) * h l i S u, fun i S S' u ψ hu ↦ ?_,
    fun i j S u hi hj ↦ ?_⟩
  · simp only [map_sum, map_mul, mp_comp, fun l ↦ hh l i S S' u ψ hu]
  · rw [← one_mul (c i j S u), ← hr S u, Finset.sum_mul, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun l _ ↦ ?_
    rw [map_mul, map_pow]
    linear_combination mp F u (r l) * hM l i j S u ⟨hi, hj⟩

include H hb in

/- English proof (translation)
Take `⟨N, hN⟩` from `(eventually_all.2 fun l ↦ eventually_all.2 fun i ↦ eventually_all.2 fun j ↦ IsSec.extend H (P := fun S u ↦ IsUnit (mp F u (b i)) ∧ IsUnit (mp F u (b j))) (b := b i * b j) (fun _ _ ↦ by rw [map_mul, IsUnit.mul_iff]) (b l) (s := c l i j) fun S S' u ψ h ↦ hs l i j S S' u ψ ⟨⟨h.2, h. …`. Use `choose h hh hh' using hN`. Take `⟨M, hM⟩` from `(eventually_all.2 fun l ↦ eventually_all.2 fun i ↦ eventually_all.2 fun j ↦ eventually_all.2 fun k ↦ IsSec.kill H (P := fun S u ↦ (IsUnit (mp F u (b i)) ∧ IsUnit (mp F u (b j))) ∧ IsUnit (mp F u (b k))) (b := b i * b j * b k) (fun _ _ ↦ by rw [map_mul, map_mul, IsUnit.mul_iff, Is …`. Simplify using `only [hs i j k S S' u ψ hu, hh l i j S S' u ψ hu.1, hh l j k S S' u ψ ⟨hu.1.2, hu.2⟩, hh l i k S S' u ψ ⟨hu.1.1, hu.2⟩, mp_comp, map_sub, map_add, map_mul, map_pow])`. Use `fun S u hu hl ↦ by`.

Rewrite using `[hh' l i j S u hu.1 hl, hh' l j k S u ⟨hu.1.2, hu.2⟩ hl, hh' l i k S u ⟨hu.1.1, hu.2⟩ hl]`. Take the linear combination `mp F u (b l) ^ N * hc l i j k S u hl hu.1.1 hu.1.2 hu.2).exists`. Take `⟨r, hr⟩` from `exists_partition hb (M + N)`. Use `⟨fun i j S u ↦ ∑ l, mp F u (r l * b l ^ M) * h l i j S u, fun i j S S' u ψ hu ↦ ?_, fun i j k S u hi hj hk ↦ ?_⟩` and prove the remaining obligations. Simplify using `only [map_sum, map_mul, mp_comp, fun l ↦ hh l i j S S' u ψ hu]`.

Rewrite using `[← one_mul (c i j k S u), ← hr S u, Finset.sum_mul, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun l _ ↦ ?_` and prove the remaining obligations. Rewrite using `[map_mul, map_pow]`. Take the linear combination `mp F u (r l) * hM l i j k S u ⟨⟨hi, hj⟩, hk⟩`.
-/
theorem cech2 (c : ι → ι → ι → ∀ S, (T ⟶ S) → F.obj S)
    (hs : ∀ i j k, IsSec F (fun S u ↦ (IsUnit (mp F u (b i)) ∧ IsUnit (mp F u (b j))) ∧
      IsUnit (mp F u (b k))) (c i j k))
    (hc : ∀ l i j k S u, IsUnit (mp F u (b l)) → IsUnit (mp F u (b i)) → IsUnit (mp F u (b j)) →
      IsUnit (mp F u (b k)) → c i j k S u - c l j k S u + c l i k S u - c l i j S u = 0) :
    ∃ e : ι → ι → ∀ S, (T ⟶ S) → F.obj S,
      (∀ i j, IsSec F (fun S u ↦ IsUnit (mp F u (b i)) ∧ IsUnit (mp F u (b j))) (e i j)) ∧
      ∀ i j k S u, IsUnit (mp F u (b i)) → IsUnit (mp F u (b j)) → IsUnit (mp F u (b k)) →
        c i j k S u = e j k S u - e i k S u + e i j S u := by
  obtain ⟨N, hN⟩ := (eventually_all.2 fun l ↦ eventually_all.2 fun i ↦ eventually_all.2 fun j ↦
    IsSec.extend H (P := fun S u ↦ IsUnit (mp F u (b i)) ∧ IsUnit (mp F u (b j))) (b := b i * b j)
      (fun _ _ ↦ by rw [map_mul, IsUnit.mul_iff]) (b l)
      (s := c l i j) fun S S' u ψ h ↦ hs l i j S S' u ψ ⟨⟨h.2, h.1.1⟩, h.1.2⟩).exists
  choose h hh hh' using hN
  obtain ⟨M, hM⟩ := (eventually_all.2 fun l ↦ eventually_all.2 fun i ↦ eventually_all.2 fun j ↦
    eventually_all.2 fun k ↦
    IsSec.kill H (P := fun S u ↦ (IsUnit (mp F u (b i)) ∧ IsUnit (mp F u (b j))) ∧
        IsUnit (mp F u (b k))) (b := b i * b j * b k)
      (fun _ _ ↦ by rw [map_mul, map_mul, IsUnit.mul_iff, IsUnit.mul_iff]) (b l)
      (s := fun S u ↦ mp F u (b l) ^ N * c i j k S u - (h l j k S u - h l i k S u + h l i j S u))
      (fun S S' u ψ hu ↦ by
        simp only [hs i j k S S' u ψ hu, hh l i j S S' u ψ hu.1, hh l j k S S' u ψ ⟨hu.1.2, hu.2⟩,
          hh l i k S S' u ψ ⟨hu.1.1, hu.2⟩, mp_comp, map_sub, map_add, map_mul, map_pow])
      fun S u hu hl ↦ by
        rw [hh' l i j S u hu.1 hl, hh' l j k S u ⟨hu.1.2, hu.2⟩ hl, hh' l i k S u ⟨hu.1.1, hu.2⟩ hl]
        linear_combination mp F u (b l) ^ N * hc l i j k S u hl hu.1.1 hu.1.2 hu.2).exists
  obtain ⟨r, hr⟩ := exists_partition hb (M + N)
  refine ⟨fun i j S u ↦ ∑ l, mp F u (r l * b l ^ M) * h l i j S u, fun i j S S' u ψ hu ↦ ?_,
    fun i j k S u hi hj hk ↦ ?_⟩
  · simp only [map_sum, map_mul, mp_comp, fun l ↦ hh l i j S S' u ψ hu]
  · rw [← one_mul (c i j k S u), ← hr S u, Finset.sum_mul, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun l _ ↦ ?_
    rw [map_mul, map_pow]
    linear_combination mp F u (r l) * hM l i j k S u ⟨⟨hi, hj⟩, hk⟩

omit [Fintype ι] in

/- English proof (translation)
Rewrite using `[mp_comp]`. Conclude with `h.map _`.
-/
theorem isUnit_comp {S S' : C} {u : T ⟶ S} (ψ : S ⟶ S') {x : F.obj T} (h : IsUnit (mp F u x)) :
    IsUnit (mp F (u ≫ ψ) x) := by
  rw [mp_comp]; exact h.map _

open Classical in
include H hb in

/- English proof (translation)
Introduce `a ha`. Use `choose β hβ using fun i ↦ vanishing_H1_inverting_morphisms H (P := fun S u ↦ IsUnit (mp F u (b i))) (fun _ _ ↦ Iff.rfl) a fun S S' S'' u ψ χ h ↦ ha S S' S'' u ψ χ ⟨i, h⟩`. Take `⟨e, he, he'⟩` from `cech1 H hb (fun i j S u ↦ β j S u - β i S u) (fun i j S S' u ψ h ↦ by`. Rewrite using `[map_sub]`. Take the linear combination `hβ j S S' u ψ h.2 - hβ i S S' u ψ h.1)`.

Use the proof step `(fun _ _ _ _ _ _ _ _ ↦ by ring)`. Choose the witnesses or unpack the hypotheses as in `⟨γ, hγ⟩ : ∃ γ : ∀ S, (T ⟶ S) → F.obj S, ∀ i S u, IsUnit (mp F u (b i)) → γ S u = β i S u - e i S u := by`. Use `⟨fun S u ↦ if h : ∃ i, IsUnit (mp F u (b i)) then β h.choose S u - e h.choose S u else 0, fun i S u hi ↦ ?_⟩` and prove the remaining obligations. Establish `h : ∃ i, IsUnit (mp F u (b i))` using `⟨i, hi⟩`. Simplify using `only [dif_pos h]`.

Take the linear combination `he' i _ S u hi h.choose_spec`. Use `⟨γ, fun S S' u ψ ⟨i, hi⟩ ↦ ?_⟩` and prove the remaining obligations. Rewrite using `[hγ i _ _ hi, hγ i _ _ (isUnit_comp ψ hi), he i _ _ _ _ hi, map_sub]`. Take the linear combination `hβ i S S' u ψ hi`.
-/
theorem vanishing_H1_standard_cover : Van1 F fun S (u : T ⟶ S) ↦ ∃ i, IsUnit (mp F u (b i)) := by
  intro a ha
  choose β hβ using fun i ↦ vanishing_H1_inverting_morphisms H (P := fun S u ↦ IsUnit (mp F u (b i))) (fun _ _ ↦ Iff.rfl) a
    fun S S' S'' u ψ χ h ↦ ha S S' S'' u ψ χ ⟨i, h⟩
  obtain ⟨e, he, he'⟩ := cech1 H hb (fun i j S u ↦ β j S u - β i S u)
    (fun i j S S' u ψ h ↦ by
      rw [map_sub]
      linear_combination hβ j S S' u ψ h.2 - hβ i S S' u ψ h.1)
    (fun _ _ _ _ _ _ _ _ ↦ by ring)
  obtain ⟨γ, hγ⟩ : ∃ γ : ∀ S, (T ⟶ S) → F.obj S, ∀ i S u, IsUnit (mp F u (b i)) →
      γ S u = β i S u - e i S u := by
    refine ⟨fun S u ↦ if h : ∃ i, IsUnit (mp F u (b i)) then β h.choose S u - e h.choose S u else 0,
      fun i S u hi ↦ ?_⟩
    have h : ∃ i, IsUnit (mp F u (b i)) := ⟨i, hi⟩
    simp only [dif_pos h]
    linear_combination he' i _ S u hi h.choose_spec
  refine ⟨γ, fun S S' u ψ ⟨i, hi⟩ ↦ ?_⟩
  rw [hγ i _ _ hi, hγ i _ _ (isUnit_comp ψ hi), he i _ _ _ _ hi, map_sub]
  linear_combination hβ i S S' u ψ hi

open Classical in
include H hb in

/- English proof (translation)
Introduce `z hz`. Use `choose a ha using fun i ↦ vanishing_H2_inverting_morphisms H (P := fun S u ↦ IsUnit (mp F u (b i))) (fun _ _ ↦ Iff.rfl) z fun S S' S'' S''' u ψ χ ω h ↦ hz S S' S'' S''' u ψ χ ω ⟨i, h⟩`. Use `choose β hβ using fun i j ↦ vanishing_H1_inverting_morphisms H (P := fun S u ↦ IsUnit (mp F u (b i)) ∧ IsUnit (mp F u (b j))) (b := b i * b j) (fun _ _ ↦ by rw [map_mul, IsUnit.mul_iff]) (fun S S' u ψ ↦ a j S S' u ψ - a i S S' u ψ) fun S S' S'' u ψ χ h ↦ by`. Rewrite using `[map_sub]`. Take the linear combination `ha i S S' S'' u ψ χ h.1 - ha j S S' S'' u ψ χ h.2`.

Take `⟨e, he, he'⟩` from `cech2 H hb (fun i j k S u ↦ β j k S u - β i k S u + β i j S u) (fun i j k S S' u ψ h ↦ by`. Rewrite using `[map_add, map_sub]`. Take the linear combination `hβ j k S S' u ψ ⟨h.1.2, h.2⟩ - hβ i k S S' u ψ ⟨h.1.1, h.2⟩ + hβ i j S S' u ψ h.1)`. Use the proof step `(fun _ _ _ _ _ _ _ _ _ _ ↦ by ring)`. Choose the witnesses or unpack the hypotheses as in `⟨γ, hγ⟩ : ∃ γ : ι → ∀ S, (T ⟶ S) → F.obj S, ∀ i j S u, IsUnit (mp F u (b i)) → IsUnit (mp F u (b j)) → γ j S u - γ i S u = β i j S u - e i j S u := by`.

Use `⟨fun i S u ↦ if h : ∃ i, IsUnit (mp F u (b i)) then β h.choose i S u - e h.choose i S u else 0, fun i j S u hi hj ↦ ?_⟩` and prove the remaining obligations. Establish `h : ∃ i, IsUnit (mp F u (b i))` using `⟨i, hi⟩`. Simplify using `only [dif_pos h]`. Take the linear combination `-he' _ i j S u h.choose_spec hi hj`. Choose the witnesses or unpack the hypotheses as in `⟨α, hα⟩ : ∃ α : ∀ S S', (T ⟶ S) → (S ⟶ S') → F.obj S', ∀ i S S' u ψ, IsUnit (mp F u (b i)) → α S S' u ψ = a i S S' u ψ - (γ i S' (u ≫ ψ) - mp F ψ (γ i S u)) := by`.

Use `⟨fun S S' u ψ ↦ if h : ∃ i, IsUnit (mp F u (b i)) then a h.choose S S' u ψ - (γ h.choose S' (u ≫ ψ) - mp F ψ (γ h.choose S u)) else 0, fun i S S' u ψ hi ↦ ?_⟩` and prove the remaining obligations. Establish `h : ∃ i, IsUnit (mp F u (b i))` using `⟨i, hi⟩`. Simplify using `only [dif_pos h]`. Establish `k1` using `congrArg (mp F ψ) (hγ i _ S u hi h.choose_spec)`. Establish `k2` using `hγ i _ S' (u ≫ ψ) (isUnit_comp ψ hi) (isUnit_comp ψ h.choose_spec)`.

Establish `k3` using `he i _ S S' u ψ ⟨hi, h.choose_spec⟩`. Establish `k4` using `hβ i _ S S' u ψ ⟨hi, h.choose_spec⟩`. Simplify using `only [map_sub] at k1`. Take the linear combination `k1 - k2 + k3 - k4`. Use `⟨α, fun S S' S'' u ψ χ ⟨i, hi⟩ ↦ ?_⟩` and prove the remaining obligations.

Rewrite using `[hα i _ _ _ _ hi, hα i _ _ _ _ hi, hα i _ _ _ _ (isUnit_comp ψ hi)]`. Simplify using `only [map_sub, mp_comp, Category.assoc]`. Take the linear combination `ha i S S' S'' u ψ χ hi`.
-/
theorem vanishing_H2_standard_cover : Van2 F fun S (u : T ⟶ S) ↦ ∃ i, IsUnit (mp F u (b i)) := by
  intro z hz
  choose a ha using fun i ↦ vanishing_H2_inverting_morphisms H (P := fun S u ↦ IsUnit (mp F u (b i))) (fun _ _ ↦ Iff.rfl) z
    fun S S' S'' S''' u ψ χ ω h ↦ hz S S' S'' S''' u ψ χ ω ⟨i, h⟩
  choose β hβ using fun i j ↦ vanishing_H1_inverting_morphisms H
    (P := fun S u ↦ IsUnit (mp F u (b i)) ∧ IsUnit (mp F u (b j))) (b := b i * b j)
    (fun _ _ ↦ by rw [map_mul, IsUnit.mul_iff]) (fun S S' u ψ ↦ a j S S' u ψ - a i S S' u ψ)
    fun S S' S'' u ψ χ h ↦ by
      rw [map_sub]
      linear_combination ha i S S' S'' u ψ χ h.1 - ha j S S' S'' u ψ χ h.2
  obtain ⟨e, he, he'⟩ := cech2 H hb (fun i j k S u ↦ β j k S u - β i k S u + β i j S u)
    (fun i j k S S' u ψ h ↦ by
      rw [map_add, map_sub]
      linear_combination hβ j k S S' u ψ ⟨h.1.2, h.2⟩ - hβ i k S S' u ψ ⟨h.1.1, h.2⟩ +
        hβ i j S S' u ψ h.1)
    (fun _ _ _ _ _ _ _ _ _ _ ↦ by ring)
  obtain ⟨γ, hγ⟩ : ∃ γ : ι → ∀ S, (T ⟶ S) → F.obj S, ∀ i j S u, IsUnit (mp F u (b i)) →
      IsUnit (mp F u (b j)) → γ j S u - γ i S u = β i j S u - e i j S u := by
    refine ⟨fun i S u ↦ if h : ∃ i, IsUnit (mp F u (b i)) then
      β h.choose i S u - e h.choose i S u else 0, fun i j S u hi hj ↦ ?_⟩
    have h : ∃ i, IsUnit (mp F u (b i)) := ⟨i, hi⟩
    simp only [dif_pos h]
    linear_combination -he' _ i j S u h.choose_spec hi hj
  obtain ⟨α, hα⟩ : ∃ α : ∀ S S', (T ⟶ S) → (S ⟶ S') → F.obj S', ∀ i S S' u ψ, IsUnit (mp F u (b i)) →
      α S S' u ψ = a i S S' u ψ - (γ i S' (u ≫ ψ) - mp F ψ (γ i S u)) := by
    refine ⟨fun S S' u ψ ↦ if h : ∃ i, IsUnit (mp F u (b i)) then
      a h.choose S S' u ψ - (γ h.choose S' (u ≫ ψ) - mp F ψ (γ h.choose S u)) else 0,
      fun i S S' u ψ hi ↦ ?_⟩
    have h : ∃ i, IsUnit (mp F u (b i)) := ⟨i, hi⟩
    simp only [dif_pos h]
    have k1 := congrArg (mp F ψ) (hγ i _ S u hi h.choose_spec)
    have k2 := hγ i _ S' (u ≫ ψ) (isUnit_comp ψ hi) (isUnit_comp ψ h.choose_spec)
    have k3 := he i _ S S' u ψ ⟨hi, h.choose_spec⟩
    have k4 := hβ i _ S S' u ψ ⟨hi, h.choose_spec⟩
    simp only [map_sub] at k1
    linear_combination k1 - k2 + k3 - k4
  refine ⟨α, fun S S' S'' u ψ χ ⟨i, hi⟩ ↦ ?_⟩
  rw [hα i _ _ _ _ hi, hα i _ _ _ _ hi, hα i _ _ _ _ (isUnit_comp ψ hi)]
  simp only [map_sub, mp_comp, Category.assoc]
  linear_combination ha i S S' S'' u ψ χ hi

end Cech

/- English proof (translation)
Take `⟨n, b, hb, h⟩` from `cov T`. Establish `hPQ : ∀ S (u : T ⟶ S), (∃ i, IsUnit (mp F u (b i))) → P S` using `fun S u ⟨i, hi⟩ ↦ h i S u hi`. Establish `hQ : ∀ S S' (_ : T ⟶ S) (ψ : S ⟶ S'), P S → P S'` using `fun S S' _ ψ ↦ hP S S' ψ`. Establish `hb' : ∀ S (u : T ⟶ S), Ideal.span (Set.range fun i ↦ mp F u (b i)) = ⊤` using `fun S u ↦ by`. Use `congrArg (Ideal.map (mp F u)) hb` as an intermediate fact.

Rewrite `this` using `[Ideal.map_span, Ideal.map_top, ← Set.range_comp]`. Then use the resulting hypothesis. Establish `sep : ∀ S (u : T ⟶ S), P S → Sep F fun S' (ψ : S ⟶ S') ↦ ∃ i, IsUnit (mp F (u ≫ ψ) (b i))` using `fun S u _ ↦ by`. Simplify `sep_std H (hb' S u)` using `only [mp_comp]`. Establish `glue : ∀ S (u : T ⟶ S), P S → Glue F fun S' (ψ : S ⟶ S') ↦ ∃ i, IsUnit (mp F (u ≫ ψ) (b i))` using `fun S u _ ↦ by`. Simplify `glue_std H (hb' S u)` using `only [mp_comp]`.

Establish `van : ∀ S (u : T ⟶ S), P S → Van1 F fun S' (ψ : S ⟶ S') ↦ ∃ i, IsUnit (mp F (u ≫ ψ) (b i))` using `fun S u _ ↦ by`. Simplify `vanishing_H1_standard_cover H (hb' S u)` using `only [mp_comp]`. Conclude with `⟨(sep_std H hb).mono hPQ, (glue_std H hb).mono hPQ sep, (vanishing_H1_standard_cover H hb).mono hPQ hQ sep glue, (vanishing_H2_standard_cover H hb).mono hPQ hQ sep glue van⟩`.
-/
theorem acyclic_of_cover (H : HasLoc F) (P : ObjectProperty C) (hP : ∀ S S', (S ⟶ S') → P S → P S')
    (cov : ∀ T : C, ∃ (n : ℕ) (b : Fin n → F.obj T), Ideal.span (Set.range b) = ⊤ ∧
      ∀ (i : Fin n) (S : C) (u : T ⟶ S), IsUnit (mp F u (b i)) → P S) (T : C) :
    (Sep F fun S (_ : T ⟶ S) ↦ P S) ∧ (Glue F fun S (_ : T ⟶ S) ↦ P S) ∧
      (Van1 F fun S (_ : T ⟶ S) ↦ P S) ∧ Van2 F fun S (_ : T ⟶ S) ↦ P S := by
  obtain ⟨n, b, hb, h⟩ := cov T
  have hPQ : ∀ S (u : T ⟶ S), (∃ i, IsUnit (mp F u (b i))) → P S := fun S u ⟨i, hi⟩ ↦ h i S u hi
  have hQ : ∀ S S' (_ : T ⟶ S) (ψ : S ⟶ S'), P S → P S' := fun S S' _ ψ ↦ hP S S' ψ
  have hb' : ∀ S (u : T ⟶ S), Ideal.span (Set.range fun i ↦ mp F u (b i)) = ⊤ := fun S u ↦ by
    have := congrArg (Ideal.map (mp F u)) hb
    rwa [Ideal.map_span, Ideal.map_top, ← Set.range_comp] at this
  have sep : ∀ S (u : T ⟶ S), P S →
      Sep F fun S' (ψ : S ⟶ S') ↦ ∃ i, IsUnit (mp F (u ≫ ψ) (b i)) := fun S u _ ↦ by
    simpa only [mp_comp] using sep_std H (hb' S u)
  have glue : ∀ S (u : T ⟶ S), P S →
      Glue F fun S' (ψ : S ⟶ S') ↦ ∃ i, IsUnit (mp F (u ≫ ψ) (b i)) := fun S u _ ↦ by
    simpa only [mp_comp] using glue_std H (hb' S u)
  have van : ∀ S (u : T ⟶ S), P S →
      Van1 F fun S' (ψ : S ⟶ S') ↦ ∃ i, IsUnit (mp F (u ≫ ψ) (b i)) := fun S u _ ↦ by
    simpa only [mp_comp] using vanishing_H1_standard_cover H (hb' S u)
  exact ⟨(sep_std H hb).mono hPQ, (glue_std H hb).mono hPQ sep,
    (vanishing_H1_standard_cover H hb).mono hPQ hQ sep glue, (vanishing_H2_standard_cover H hb).mono hPQ hQ sep glue van⟩

/- English proof (translation)
The claim follows from `have h := acyclic_of_cover F H P hP cov ⟨pull_restrict_small_injective F P hP (fun T ↦ (h T).1) (fun T ↦ (h T).2.1) fun T ↦ (h T).2.2.1, descent_H2_surjective F P hP (fun T ↦ (h T).1) (fun T ↦ (h T).2.1) (fun T ↦ (h T).2.2.1) fun T ↦ (h T).2.2.2⟩`.
-/
theorem pull2_bijective (H : HasLoc F) (P : ObjectProperty C) (hP : ∀ S S', (S ⟶ S') → P S → P S')
    (cov : ∀ T : C, ∃ (n : ℕ) (b : Fin n → F.obj T), Ideal.span (Set.range b) = ⊤ ∧
      ∀ (i : Fin n) (S : C) (u : T ⟶ S), IsUnit (mp F u (b i)) → P S) :
    Function.Bijective (CoefMap.restrict F P.ι).pull2 :=
  have h := acyclic_of_cover F H P hP cov
  ⟨pull_restrict_small_injective F P hP (fun T ↦ (h T).1) (fun T ↦ (h T).2.1) fun T ↦ (h T).2.2.1,
    descent_H2_surjective F P hP (fun T ↦ (h T).1) (fun T ↦ (h T).2.1) (fun T ↦ (h T).2.2.1)
      fun T ↦ (h T).2.2.2⟩

end GlobalTheory.CatCoh.Desc
