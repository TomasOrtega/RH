import Development.EtaleCohomology.KummerTheory.ContCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.KummerTheory.GluePf

def pc (U V : Scheme.{0}) : Bool → Scheme.{0} := fun b => Bool.rec V U b

def pm {U V X : Scheme.{0}} (f : U ⟶ X) (g : V ⟶ X) : ∀ b : Bool, pc U V b ⟶ X :=
  fun b => Bool.rec (motive := fun b => pc U V b ⟶ X) g f b

/- English proof (translation)
Take `⟨hf, hg, -, hcov⟩` from `h`. Apply `Precoverage.generate_mem_toGrothendieck` to reduce the goal to its premises. Use `(Scheme.ofArrows_mem_precoverage_iff (P := (@Etale : MorphismProperty Scheme.{0}))).2 ⟨fun x => ?_, fun i => ?_⟩` and prove the remaining obligations. Break down `hcov x with hx | hx` into its components or cases. Conclude with `⟨true, hx⟩`.

Conclude with `⟨false, hx⟩`. Consider the cases of `i`. Conclude with `(inferInstance : Etale g)`. Conclude with `(inferInstance : Etale f)`.
-/
theorem mem_cover {W U V X : Scheme.{0}} (a : W ⟶ U) (b : W ⟶ V) (f : U ⟶ X) (g : V ⟶ X)
    (h : LateralTheory.KummerTheory.ContCut.IsMV a b f g) :
    Sieve.generate (Presieve.ofArrows (pc U V) (pm f g)) ∈ Scheme.etaleTopology X := by
  obtain ⟨hf, hg, -, hcov⟩ := h
  apply Precoverage.generate_mem_toGrothendieck
  refine (Scheme.ofArrows_mem_precoverage_iff (P := (@Etale : MorphismProperty Scheme.{0}))).2 ⟨fun x => ?_, fun i => ?_⟩
  · rcases hcov x with hx | hx
    · exact ⟨true, hx⟩
    · exact ⟨false, hx⟩
  · cases i
    · exact (inferInstance : Etale g)
    · exact (inferInstance : Etale f)

/- English proof (translation)
Establish `hG : Presheaf.IsSheaf (Scheme.etaleTopology) (G.obj ⋙ forget (ModuleCat.{1} (ULift.{1} R)))` using `(Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget (ModuleCat.{1} (ULift.{1} R)))).1 G.cond`. Rewrite using `[Presieve.isSheafFor_iff_generate]`. Conclude with `hG.isSheafFor _ (mem_cover a b f g h)`.
-/
theorem sheafFor {R : Type} [CommRing R] (G : Shv R) {W U V X : Scheme.{0}} (a : W ⟶ U) (b : W ⟶ V)
    (f : U ⟶ X) (g : V ⟶ X) (h : LateralTheory.KummerTheory.ContCut.IsMV a b f g) :
    Presieve.IsSheafFor (G.obj ⋙ forget (ModuleCat.{1} (ULift.{1} R)))
      (Presieve.ofArrows (pc U V) (pm f g)) := by
  have hG : Presheaf.IsSheaf (Scheme.etaleTopology) (G.obj ⋙ forget (ModuleCat.{1} (ULift.{1} R))) :=
    (Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget (ModuleCat.{1} (ULift.{1} R)))).1 G.cond
  rw [Presieve.isSheafFor_iff_generate]
  exact hG.isSheafFor _ (mem_cover a b f g h)

/- English proof (translation)
Take `⟨l, hl1, hl2⟩` from `hpb.exists_lift gi gj e`. Substitute `hl1 hl2` using the available equality. Rewrite using `[op_comp, op_comp, Functor.map_comp, Functor.map_comp, ModuleCat.hom_comp, ModuleCat.hom_comp, LinearMap.comp_apply, LinearMap.comp_apply]`. Conclude with `congrArg (G.obj.map l.op).hom hst`.
-/
theorem compat {R : Type} [CommRing R] (G : Shv R) {W U V X : Scheme.{0}} {a : W ⟶ U} {b : W ⟶ V}
    {f : U ⟶ X} {g : V ⟶ X} (hpb : IsPullback a b f g) {s : Sec G U} {t : Sec G V}
    (hst : Sec.res a s = Sec.res b t) {Z : Scheme.{0}} (gi : Z ⟶ U) (gj : Z ⟶ V) (e : gi ≫ f = gj ≫ g) :
    (G.obj.map gi.op).hom s = (G.obj.map gj.op).hom t := by
  obtain ⟨l, hl1, hl2⟩ := hpb.exists_lift gi gj e
  subst hl1 hl2
  rw [op_comp, op_comp, Functor.map_comp, Functor.map_comp, ModuleCat.hom_comp, ModuleCat.hom_comp,
    LinearMap.comp_apply, LinearMap.comp_apply]
  exact congrArg (G.obj.map l.op).hom hst

/- English proof (translation)
Introduce `R _ G W U V X a b f g h`. Establish `hS` using `sheafFor G a b f g h`. Rewrite `hS` using `[Presieve.isSheafFor_arrows_iff]`. Take `⟨hf, hg, hpb, -⟩` from `h`. Use `⟨fun z hz1 hz2 => ?_, fun s t hst => ?_⟩` and prove the remaining obligations.

Establish `hc : Presieve.Arrows.Compatible (G.obj ⋙ forget (ModuleCat.{1} (ULift.{1} R))) (pm f g) (fun _ => (0 : Sec G _))`. Introduce `i j Z gi gj _`. Express the relevant statement in the definitionally equal form `(G.obj.map gi.op).hom 0 = (G.obj.map gj.op).hom 0`. Simplify using the standard rewrite rules. Take `⟨t, -, ht⟩` from `hS _ hc`.

Apply the tactic sequence `have e1 := ht z (fun i => by cases i <;> assumption)`. Establish `e2` using `ht 0 (fun i => by`. Express the relevant statement in the definitionally equal form `(G.obj.map _).hom 0 = 0`. Use the proof step `simp)`. Rewrite using `[e1, e2]`.

Set `x : ∀ i, Sec G (pc U V i)` to `fun i => Bool.rec (motive := fun i => Sec G (pc U V i)) t s i`. Establish `hc : Presieve.Arrows.Compatible (G.obj ⋙ forget (ModuleCat.{1} (ULift.{1} R))) (pm f g) x`. Introduce `i j Z gi gj e`. Express the relevant statement in the definitionally equal form `(G.obj.map gi.op).hom (x i) = (G.obj.map gj.op).hom (x j)`. Apply the tactic sequence `cases i <;> cases j`.

Establish `: gi = gj` using `(cancel_mono g).1 e`. Substitute `this` using the available equality. Both sides reduce to the same expression. Conclude with `(compat G hpb hst gj gi e.symm).symm`. Conclude with `compat G hpb hst gi gj e`.

Establish `: gi = gj` using `(cancel_mono f).1 e`. Substitute `this` using the available equality. Both sides reduce to the same expression. Take `⟨z, hz, -⟩` from `hS x hc`. Conclude with `⟨z, hz true, hz false⟩`.
-/
theorem Glue_of : LateralTheory.KummerTheory.ContCut.Glue := by
  intro R _ G W U V X a b f g h
  have hS := sheafFor G a b f g h
  rw [Presieve.isSheafFor_arrows_iff] at hS
  obtain ⟨hf, hg, hpb, -⟩ := h
  refine ⟨fun z hz1 hz2 => ?_, fun s t hst => ?_⟩
  · have hc : Presieve.Arrows.Compatible (G.obj ⋙ forget (ModuleCat.{1} (ULift.{1} R))) (pm f g)
        (fun _ => (0 : Sec G _)) := by
      intro i j Z gi gj _
      change (G.obj.map gi.op).hom 0 = (G.obj.map gj.op).hom 0
      simp
    obtain ⟨t, -, ht⟩ := hS _ hc
    have e1 := ht z (fun i => by cases i <;> assumption)
    have e2 := ht 0 (fun i => by
      change (G.obj.map _).hom 0 = 0
      simp)
    rw [e1, e2]
  · let x : ∀ i, Sec G (pc U V i) := fun i => Bool.rec (motive := fun i => Sec G (pc U V i)) t s i
    have hc : Presieve.Arrows.Compatible (G.obj ⋙ forget (ModuleCat.{1} (ULift.{1} R))) (pm f g) x := by
      intro i j Z gi gj e
      change (G.obj.map gi.op).hom (x i) = (G.obj.map gj.op).hom (x j)
      cases i <;> cases j
      · have : gi = gj := (cancel_mono g).1 e
        subst this; rfl
      · exact (compat G hpb hst gj gi e.symm).symm
      · exact compat G hpb hst gi gj e
      · have : gi = gj := (cancel_mono f).1 e
        subst this; rfl
    obtain ⟨z, hz, -⟩ := hS x hc
    exact ⟨z, hz true, hz false⟩

end LateralTheory.KummerTheory.GluePf
