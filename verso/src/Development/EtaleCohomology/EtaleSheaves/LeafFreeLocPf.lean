import Development.EtaleCohomology.EtaleSheaves.LeafSqPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.t_E6Cut LateralTheory.E.LeafSqPf

namespace LateralTheory.E.LeafFreeLocPf

/- English proof (translation)
Assemble the required witnesses or components as `⟨⊤, GrothendieckTopology.top_mem _ _, fun V k _ => h V k⟩`.
-/
lemma etLoc_top {T : Scheme.{0}} {P : ∀ V : Scheme.{0}, (V ⟶ T) → Prop} (h : ∀ V k, P V k) : EtLoc T P :=
  ⟨⊤, GrothendieckTopology.top_mem _ _, fun V k _ => h V k⟩

/- English proof (translation)
Take `⟨S, hS, hS'⟩` from `hP`. Take `⟨S', hT, hT'⟩` from `hQ`. Conclude with `⟨S ⊓ S', GrothendieckTopology.intersection_covering _ hS hT, fun V k hk => ⟨hS' V k hk.1, hT' V k hk.2⟩⟩`.
-/
lemma etLoc_and {T : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ T) → Prop} (hP : EtLoc T P) (hQ : EtLoc T Q) :
    EtLoc T (fun V k => P V k ∧ Q V k) := by
  obtain ⟨S, hS, hS'⟩ := hP
  obtain ⟨S', hT, hT'⟩ := hQ
  exact ⟨S ⊓ S', GrothendieckTopology.intersection_covering _ hS hT, fun V k hk => ⟨hS' V k hk.1, hT' V k hk.2⟩⟩

/- English proof (translation)
Take `⟨S, hS, hS'⟩` from `hP`. Conclude with `⟨S, hS, fun V k hk => h V k (hS' V k hk)⟩`.
-/
lemma etLoc_mono {T : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ T) → Prop} (hP : EtLoc T P)
    (h : ∀ V k, P V k → Q V k) : EtLoc T Q := by
  obtain ⟨S, hS, hS'⟩ := hP
  exact ⟨S, hS, fun V k hk => h V k (hS' V k hk)⟩

/- English proof (translation)
Set `v : Z → (X →₀ S) ⧸ D` to `fun z => if hz : (∃ a, g a = z) ∧ ¬ ∃ u, f u = z then D.mkQ (Finsupp.single hz.1.choose 1) else 0`. Set `θ` to `Finsupp.linearCombination S v`. Establish `hv : ∀ a, v (g a) = D.mkQ (Finsupp.single a 1)`. Introduce `a`. Simplify using `only [v]`.

Use `split_ifs with hz`. Establish `hc` using `hz.1.choose_spec`. Rewrite using `[eq_comm, ← sub_eq_zero, ← LinearMap.map_sub, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]`. Conclude with `h2 _ _ hc.symm`. Establish `: ∃ u, f u = g a`.

Assume the negation of the conclusion as `hn`. Conclude with `hz ⟨⟨a, rfl⟩, hn⟩`. Rewrite using `[eq_comm, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]`. Conclude with `h1 a this`. Establish `hx : ∀ x' : X →₀ S, θ (Finsupp.mapDomain g x') = D.mkQ x'`.

Introduce `x`. Proceed by induction on `x using Finsupp.induction_linear with`. Consider the case `zero => simp`. Consider the case `add p q hp hq => rw [Finsupp.mapDomain_add, map_add, hp, hq, map_add]`. Consider the case `single a r`.

Rewrite using `[Finsupp.mapDomain_single]`. Simplify using `only [θ, Finsupp.linearCombination_single, hv]`. Rewrite using `[← LinearMap.map_smul, Finsupp.smul_single_one]`. Establish `hy : ∀ y' : Y →₀ S, θ (Finsupp.mapDomain f y') = 0`. Introduce `y`.

Proceed by induction on `y using Finsupp.induction_linear with`. Consider the case `zero => simp`. Consider the case `add p q hp hq => rw [Finsupp.mapDomain_add, map_add, hp, hq, add_zero]`. Consider the case `single u r`. Rewrite using `[Finsupp.mapDomain_single]`.

Simplify using `only [θ, Finsupp.linearCombination_single, v]`. Rewrite using `[dif_neg (fun hz => hz.2 ⟨u, rfl⟩), smul_zero]`. Establish `: D.mkQ x = 0` using `by rw [← hx, h, hy]`. Simplify `this` using `[Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]`.
-/
lemma alg {S X Y Z : Type*} [CommRing S] (g : X → Z) (f : Y → Z) (D : Submodule S (X →₀ S))
    (h1 : ∀ a, (∃ u, f u = g a) → Finsupp.single a 1 ∈ D)
    (h2 : ∀ a b, g a = g b → Finsupp.single a 1 - Finsupp.single b 1 ∈ D)
    (x : X →₀ S) (y : Y →₀ S) (h : Finsupp.mapDomain g x = Finsupp.mapDomain f y) : x ∈ D := by
  classical
  let v : Z → (X →₀ S) ⧸ D := fun z =>
    if hz : (∃ a, g a = z) ∧ ¬ ∃ u, f u = z then D.mkQ (Finsupp.single hz.1.choose 1) else 0
  let θ := Finsupp.linearCombination S v
  have hv : ∀ a, v (g a) = D.mkQ (Finsupp.single a 1) := by
    intro a
    simp only [v]
    split_ifs with hz
    · have hc := hz.1.choose_spec
      rw [eq_comm, ← sub_eq_zero, ← LinearMap.map_sub, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact h2 _ _ hc.symm
    · have : ∃ u, f u = g a := by
        by_contra hn
        exact hz ⟨⟨a, rfl⟩, hn⟩
      rw [eq_comm, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact h1 a this
  have hx : ∀ x' : X →₀ S, θ (Finsupp.mapDomain g x') = D.mkQ x' := by
    intro x
    induction x using Finsupp.induction_linear with
    | zero => simp
    | add p q hp hq => rw [Finsupp.mapDomain_add, map_add, hp, hq, map_add]
    | single a r =>
      rw [Finsupp.mapDomain_single]
      simp only [θ, Finsupp.linearCombination_single, hv]
      rw [← LinearMap.map_smul, Finsupp.smul_single_one]
  have hy : ∀ y' : Y →₀ S, θ (Finsupp.mapDomain f y') = 0 := by
    intro y
    induction y using Finsupp.induction_linear with
    | zero => simp
    | add p q hp hq => rw [Finsupp.mapDomain_add, map_add, hp, hq, add_zero]
    | single u r =>
      rw [Finsupp.mapDomain_single]
      simp only [θ, Finsupp.linearCombination_single, v]
      rw [dif_neg (fun hz => hz.2 ⟨u, rfl⟩), smul_zero]
  have : D.mkQ x = 0 := by rw [← hx, h, hy]
  simpa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] using this

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma mapApp (R : Type) [CommRing R] {X Y : PSh} (φ : X ⟶ Y) (V : Scheme.{0}) (z : ((freeP R).obj X).obj (op V)) :
    (((freeP R).map φ).app (op V)).hom z =
      Finsupp.mapDomain (fun x : ULift (X.obj (op V)) => ULift.up (φ.app (op V) x.down)) z := rfl

/- English proof (translation)
The claim follows from `congrArg (fun m => m.hom z) (((freeP R).map φ).naturality k.op)`.
-/
lemma natP (R : Type) [CommRing R] {X Y : PSh} (φ : X ⟶ Y) {V T : Scheme.{0}} (k : V ⟶ T)
    (z : ((freeP R).obj X).obj (op T)) :
    (((freeP R).map φ).app (op V)).hom ((((freeP R).obj X).map k.op).hom z) =
      (((freeP R).obj Y).map k.op).hom ((((freeP R).map φ).app (op T)).hom z) :=
  congrArg (fun m => m.hom z) (((freeP R).map φ).naturality k.op)

/- English proof (translation)
Introduce `R _ P U E' E fst snd f _ g hpb h1 h2`. Establish `hinj : ∀ V : Scheme.{0}, Function.Injective (f.app (op V))` using `fun V => (mono_iff_injective _).1 ((NatTrans.mono_iff_mono_app f).1 inferInstance (op V))`. Establish `hex : ∀ (V : Scheme.{0}) (u : U.obj (op V)) (a : E'.obj (op V)), f.app (op V) u = g.app (op V) a → ∃ p, fst.app (op V) p = u ∧ snd.app (op V) p = a` using `fun V u a h => Types.exists_of_isPullback (hpb.map ((evaluation _ _).obj (op V))) u a h`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `show ∀ (T : Scheme.{0}) (z : ULift (E.obj (op T)) →₀ ULift R), EtLoc T fun V k => ∃ (x : ULift (E'.obj (op V)) →₀ ULift R) (y : ULift (U.obj (op V)) →₀ ULift R), Finsupp.mapDomain (fun x : ULift (E'.obj (op V)) => ULift.up (g.app (op V) x.down)) x + Finsupp.mapDomain (fun x : ULi …`.

Introduce `T z`. Proceed by induction on `z using Finsupp.induction_linear with`. Consider the case `zero => exact etLoc_top fun V k => ⟨0, 0, by simp⟩`. Consider the case `add p q hp hq`. Conclude with `etLoc_mono (etLoc_and hp hq) fun V k ⟨⟨x1, y1, e1⟩, ⟨x2, y2, e2⟩⟩ => ⟨x1 + x2, y1 + y2, by`.

Rewrite using `[Finsupp.mapDomain_add, Finsupp.mapDomain_add, Finsupp.mapDomain_add, ← e1, ← e2]`. Use the proof step `abel⟩`. Consider the case `single a r`. Use `etLoc_mono (h1 T a.down) fun V k hk => ?_` and prove the remaining obligations. Break down `hk with ⟨u, hu⟩ | ⟨b, hb⟩` into its components or cases.

Use `⟨0, Finsupp.single (ULift.up u) r, ?_⟩` and prove the remaining obligations. Rewrite using `[Finsupp.mapDomain_zero, zero_add, Finsupp.mapDomain_single, Finsupp.mapDomain_single, hu]`. Use `⟨Finsupp.single (ULift.up b) r, 0, ?_⟩` and prove the remaining obligations. Rewrite using `[Finsupp.mapDomain_zero, add_zero, Finsupp.mapDomain_single, Finsupp.mapDomain_single, hb]`. Introduce `T x y hxy`.

Set `D : Submodule (ULift R) (ULift (E'.obj (op T)) →₀ ULift R)` to `{ carrier := {x | EtLoc T fun V k => ∃ w : ULift (P.obj (op V)) →₀ ULift R, Finsupp.mapDomain (fun x : ULift (P.obj (op V)) => ULift.up (snd.app (op V) x.down)) w = Finsupp.mapDomain (fun x : ULift (E'.obj (op T)) => ULift.up (E'.map k.op x.down)) x} zero_mem' := etLoc_top fun V …`. Establish `hxD : x ∈ D`. Use `alg (fun a : ULift (E'.obj (op T)) => ULift.up (g.app (op T) a.down)) (fun u : ULift (U.obj (op T)) => ULift.up (f.app (op T) u.down)) D ?_ ?_ x (-y) ?_` and prove the remaining obligations. Introduce and unpack `a ⟨u, hu⟩`. Take `⟨p, -, hp2⟩` from `hex T u.down a.down (congrArg ULift.down hu)`.

Use `etLoc_top fun V k => ⟨Finsupp.single (ULift.up (P.map k.op p)) 1, ?_⟩` and prove the remaining obligations. Rewrite using `[Finsupp.mapDomain_single, Finsupp.mapDomain_single, ← hp2, NatTrans.naturality_apply]`. Introduce `a b hab`. Establish `hab' : g.app (op T) a.down = g.app (op T) b.down` using `congrArg ULift.down hab`. Use `show EtLoc T fun V k => ∃ w : ULift (P.obj (op V)) →₀ ULift R, Finsupp.mapDomain (fun x : ULift (P.obj (op V)) => ULift.up (snd.app (op V) x.down)) w = Finsupp.mapDomain (fun x : ULift (E'.obj (op T)) => ULift.up (E'.map k.op x.down)) (Finsupp.single a 1 - Finsupp.single b 1)`.

Use `etLoc_mono (h2 T a.down b.down hab') fun V k hk => ?_` and prove the remaining obligations. Break down `hk with he | ⟨u, hu⟩` into its components or cases. Use `⟨0, ?_⟩` and prove the remaining obligations. Rewrite using `[Finsupp.mapDomain_zero, Finsupp.mapDomain_sub, Finsupp.mapDomain_single, Finsupp.mapDomain_single]`. Simplify using `only [he, sub_self]`.

Establish `ga : f.app (op V) u = g.app (op V) (E'.map k.op a.down)`. Rewrite using `[hu, NatTrans.naturality_apply]`. Establish `gb : f.app (op V) u = g.app (op V) (E'.map k.op b.down)`. Rewrite using `[hu, hab', NatTrans.naturality_apply]`. Take `⟨pa, -, hpa⟩` from `hex V u _ ga`.

Take `⟨pb, -, hpb'⟩` from `hex V u _ gb`. Use `⟨Finsupp.single (ULift.up pa) 1 - Finsupp.single (ULift.up pb) 1, ?_⟩` and prove the remaining obligations. Rewrite using `[Finsupp.mapDomain_sub, Finsupp.mapDomain_sub]`. Simplify using `only [Finsupp.mapDomain_single, hpa, hpb']`. Express the relevant statement in the definitionally equal form `(((freeP R).map g).app (op T)).hom x = (((freeP R).map f).app (op T)).hom (-y)`.

Rewrite using `[map_neg]`. Conclude with `eq_neg_of_add_eq_zero_left hxy`. Use `etLoc_mono hxD fun V k hV => ?_` and prove the remaining obligations. Take `⟨w0, hw0⟩` from `hV`. Take `⟨w, hw'⟩ : ∃ w : ((freeP R).obj P).obj (op V), (((freeP R).map snd).app (op V)).hom w = (((freeP R).obj E').map k.op).hom x` from `⟨w0, hw0⟩`.

Use `⟨w, hw', ?_⟩` and prove the remaining obligations. Establish `hfi : Function.Injective (fun v : ULift (U.obj (op V)) => ULift.up (f.app (op V) v.down))` using `fun a b h => ULift.ext _ _ (hinj V (congrArg ULift.down h))`. Establish `fInj : Function.Injective (((freeP R).map f).app (op V)).hom`. Introduce `a b h`. Rewrite `h` using `[mapApp, mapApp]`.

Conclude with `Finsupp.mapDomain_injective hfi h`. Establish `commP : ∀ w : ((freeP R).obj P).obj (op V), (((freeP R).map f).app (op V)).hom ((((freeP R).map fst).app (op V)).hom w) = (((freeP R).map g).app (op V)).hom ((((freeP R).map snd).app (op V)).hom w)`. Introduce `w`. Use `congrArg (fun φ => ((freeP R).map φ).app (op V)) hpb.w` as an intermediate fact. Simplify using `only [Functor.map_comp, NatTrans.comp_app] at this`.

Conclude with `congrArg (fun m => m.hom w) this`. Establish `hg : (((freeP R).map g).app (op T)).hom x = -(((freeP R).map f).app (op T)).hom y` using `eq_neg_of_add_eq_zero_left hxy`. Apply `fInj` to reduce the goal to its premises. Rewrite using `[commP, hw', natP, hg, map_neg, map_neg, natP]`.
-/
theorem LeafFreeLoc_of (_hRel : LeafRel) : LeafFreeLoc := by
  intro R _ P U E' E fst snd f _ g hpb h1 h2
  have hinj : ∀ V : Scheme.{0}, Function.Injective (f.app (op V)) := fun V =>
    (mono_iff_injective _).1 ((NatTrans.mono_iff_mono_app f).1 inferInstance (op V))
  have hex : ∀ (V : Scheme.{0}) (u : U.obj (op V)) (a : E'.obj (op V)), f.app (op V) u = g.app (op V) a →
      ∃ p, fst.app (op V) p = u ∧ snd.app (op V) p = a :=
    fun V u a h => Types.exists_of_isPullback (hpb.map ((evaluation _ _).obj (op V))) u a h
  refine ⟨?_, ?_⟩
  · show ∀ (T : Scheme.{0}) (z : ULift (E.obj (op T)) →₀ ULift R), EtLoc T fun V k =>
      ∃ (x : ULift (E'.obj (op V)) →₀ ULift R) (y : ULift (U.obj (op V)) →₀ ULift R),
        Finsupp.mapDomain (fun x : ULift (E'.obj (op V)) => ULift.up (g.app (op V) x.down)) x +
          Finsupp.mapDomain (fun x : ULift (U.obj (op V)) => ULift.up (f.app (op V) x.down)) y =
        Finsupp.mapDomain (fun x : ULift (E.obj (op T)) => ULift.up (E.map k.op x.down)) z
    intro T z
    induction z using Finsupp.induction_linear with
    | zero => exact etLoc_top fun V k => ⟨0, 0, by simp⟩
    | add p q hp hq =>
      exact etLoc_mono (etLoc_and hp hq) fun V k ⟨⟨x1, y1, e1⟩, ⟨x2, y2, e2⟩⟩ =>
        ⟨x1 + x2, y1 + y2, by
          rw [Finsupp.mapDomain_add, Finsupp.mapDomain_add, Finsupp.mapDomain_add, ← e1, ← e2]; abel⟩
    | single a r =>
      refine etLoc_mono (h1 T a.down) fun V k hk => ?_
      rcases hk with ⟨u, hu⟩ | ⟨b, hb⟩
      · refine ⟨0, Finsupp.single (ULift.up u) r, ?_⟩
        rw [Finsupp.mapDomain_zero, zero_add, Finsupp.mapDomain_single, Finsupp.mapDomain_single, hu]
      · refine ⟨Finsupp.single (ULift.up b) r, 0, ?_⟩
        rw [Finsupp.mapDomain_zero, add_zero, Finsupp.mapDomain_single, Finsupp.mapDomain_single, hb]
  · intro T x y hxy
    let D : Submodule (ULift R) (ULift (E'.obj (op T)) →₀ ULift R) :=
      { carrier := {x | EtLoc T fun V k => ∃ w : ULift (P.obj (op V)) →₀ ULift R,
          Finsupp.mapDomain (fun x : ULift (P.obj (op V)) => ULift.up (snd.app (op V) x.down)) w =
            Finsupp.mapDomain (fun x : ULift (E'.obj (op T)) => ULift.up (E'.map k.op x.down)) x}
        zero_mem' := etLoc_top fun V k => ⟨0, by rw [Finsupp.mapDomain_zero, Finsupp.mapDomain_zero]⟩
        add_mem' := fun {a b} ha hb => etLoc_mono (etLoc_and ha hb) fun V k ⟨⟨w1, e1⟩, ⟨w2, e2⟩⟩ =>
          ⟨w1 + w2, by rw [Finsupp.mapDomain_add, Finsupp.mapDomain_add, e1, e2]⟩
        smul_mem' := fun c a ha => etLoc_mono ha fun V k ⟨w, e⟩ =>
          ⟨c • w, by rw [Finsupp.mapDomain_smul, Finsupp.mapDomain_smul, e]⟩ }
    have hxD : x ∈ D := by
      refine alg (fun a : ULift (E'.obj (op T)) => ULift.up (g.app (op T) a.down))
        (fun u : ULift (U.obj (op T)) => ULift.up (f.app (op T) u.down)) D ?_ ?_ x (-y) ?_
      · rintro a ⟨u, hu⟩
        obtain ⟨p, -, hp2⟩ := hex T u.down a.down (congrArg ULift.down hu)
        refine etLoc_top fun V k => ⟨Finsupp.single (ULift.up (P.map k.op p)) 1, ?_⟩
        rw [Finsupp.mapDomain_single, Finsupp.mapDomain_single, ← hp2, NatTrans.naturality_apply]
      · intro a b hab
        have hab' : g.app (op T) a.down = g.app (op T) b.down := congrArg ULift.down hab
        show EtLoc T fun V k => ∃ w : ULift (P.obj (op V)) →₀ ULift R,
          Finsupp.mapDomain (fun x : ULift (P.obj (op V)) => ULift.up (snd.app (op V) x.down)) w =
            Finsupp.mapDomain (fun x : ULift (E'.obj (op T)) => ULift.up (E'.map k.op x.down))
              (Finsupp.single a 1 - Finsupp.single b 1)
        refine etLoc_mono (h2 T a.down b.down hab') fun V k hk => ?_
        rcases hk with he | ⟨u, hu⟩
        · refine ⟨0, ?_⟩
          rw [Finsupp.mapDomain_zero, Finsupp.mapDomain_sub, Finsupp.mapDomain_single, Finsupp.mapDomain_single]
          simp only [he, sub_self]
        · have ga : f.app (op V) u = g.app (op V) (E'.map k.op a.down) := by
            rw [hu, NatTrans.naturality_apply]
          have gb : f.app (op V) u = g.app (op V) (E'.map k.op b.down) := by
            rw [hu, hab', NatTrans.naturality_apply]
          obtain ⟨pa, -, hpa⟩ := hex V u _ ga
          obtain ⟨pb, -, hpb'⟩ := hex V u _ gb
          refine ⟨Finsupp.single (ULift.up pa) 1 - Finsupp.single (ULift.up pb) 1, ?_⟩
          rw [Finsupp.mapDomain_sub, Finsupp.mapDomain_sub]
          simp only [Finsupp.mapDomain_single, hpa, hpb']
      · change (((freeP R).map g).app (op T)).hom x = (((freeP R).map f).app (op T)).hom (-y)
        rw [map_neg]
        exact eq_neg_of_add_eq_zero_left hxy
    refine etLoc_mono hxD fun V k hV => ?_
    obtain ⟨w0, hw0⟩ := hV
    obtain ⟨w, hw'⟩ : ∃ w : ((freeP R).obj P).obj (op V),
        (((freeP R).map snd).app (op V)).hom w = (((freeP R).obj E').map k.op).hom x :=
      ⟨w0, hw0⟩
    refine ⟨w, hw', ?_⟩
    have hfi : Function.Injective (fun v : ULift (U.obj (op V)) => ULift.up (f.app (op V) v.down)) :=
      fun a b h => ULift.ext _ _ (hinj V (congrArg ULift.down h))
    have fInj : Function.Injective (((freeP R).map f).app (op V)).hom := by
      intro a b h
      rw [mapApp, mapApp] at h
      exact Finsupp.mapDomain_injective hfi h
    have commP : ∀ w : ((freeP R).obj P).obj (op V),
        (((freeP R).map f).app (op V)).hom ((((freeP R).map fst).app (op V)).hom w) =
          (((freeP R).map g).app (op V)).hom ((((freeP R).map snd).app (op V)).hom w) := by
      intro w
      have := congrArg (fun φ => ((freeP R).map φ).app (op V)) hpb.w
      simp only [Functor.map_comp, NatTrans.comp_app] at this
      exact congrArg (fun m => m.hom w) this
    have hg : (((freeP R).map g).app (op T)).hom x = -(((freeP R).map f).app (op T)).hom y :=
      eq_neg_of_add_eq_zero_left hxy
    apply fInj
    rw [commP, hw', natP, hg, map_neg, map_neg, natP]

end LateralTheory.E.LeafFreeLocPf
