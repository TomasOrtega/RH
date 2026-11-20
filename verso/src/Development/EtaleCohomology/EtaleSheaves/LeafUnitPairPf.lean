import Development.EtaleCohomology.EtaleSheaves.LeafRingUnitPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafUnitPairPf
open LateralTheory.E.CupProductRingLaws LateralTheory.E.LeafRingUnitPf

/- English proof (translation)
Establish `h1 : Sec.res g (twGen i ζ) = twGen i (ζ.map g.appTop.hom)`. Establish `h` using `congrArg (fun f => f.hom (Submodule.Quotient.mk (Finsupp.single ζ 1) : (twF q i).obj Γ(U, ⊤))) ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q i)).naturality g.op)`. Simplify using `only [ModuleCat.hom_comp] at h`. Use `h.symm.trans (congrArg (fun x => ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q i)).app (op V)).hom x) ?_)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Submodule.Quotient.mk (Finsupp.mapDomain (Prim.map g.appTop.hom) (Finsupp.single ζ (1 : ULift.{1} (ZMod q)))) = _`.

Rewrite using `[Finsupp.mapDomain_single]`. Both sides reduce to the same expression. Unfold `resGen`. Rewrite using `[← h1]`. Conclude with `congrArg (fun f => f.hom (twGen i ζ)) (((resι _ (tw q i)).hom.naturality g.op)).symm`.
-/
theorem resGen_res' {q : ℕ} (i : ℤ) {V U : Scheme.{0}} (g : V ⟶ U) (ζ : Prim q Γ(U, ⊤)) :
    Sec.res g (resGen i ζ) = resGen i (ζ.map g.appTop.hom) := by
  have h1 : Sec.res g (twGen i ζ) = twGen i (ζ.map g.appTop.hom) := by
    have h := congrArg (fun f => f.hom (Submodule.Quotient.mk (Finsupp.single ζ 1) :
        (twF q i).obj Γ(U, ⊤)))
      ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q i)).naturality g.op)
    simp only [ModuleCat.hom_comp] at h
    refine h.symm.trans (congrArg (fun x => ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q i)).app (op V)).hom x) ?_)
    change Submodule.Quotient.mk (Finsupp.mapDomain (Prim.map g.appTop.hom) (Finsupp.single ζ (1 : ULift.{1} (ZMod q)))) = _
    rw [Finsupp.mapDomain_single]
    rfl
  unfold resGen
  rw [← h1]
  exact congrArg (fun f => f.hom (twGen i ζ)) (((resι _ (tw q i)).hom.naturality g.op)).symm

def UnitPairLoc : Prop := ∀ (q : ℕ) [NeZero q] (i : ℤ), ∃ ν : Pair (res _ (tw q 0)) (res _ (tw q i)) (res _ (tw q i)),
  ∀ (U : Scheme.{0}) (t : ℤ) (a : Sec ((res _ (tw q 0)).X 0) U) (b : Sec ((res _ (tw q i)).X t) U),
    Loc U (fun V g => ∃ ζ : Prim q Γ(V, ⊤), Sec.res g a = resGen 0 ζ) → ν.mul U 0 t t (zero_add t) a b = b

/- English proof (translation)
Take `⟨S, hS, hP⟩` from `h`. Establish `hsh` using `(F.property (ModuleCat.of (ULift.{1} R) (ULift.{1} R)) S hS).isSeparatedFor`. Set `fx : ModuleCat.of (ULift.{1} R) (ULift.{1} R) ⟶ F.obj.obj (op U)` to `ModuleCat.ofHom (LinearMap.toSpanSingleton _ _ x)`. Set `fy : ModuleCat.of (ULift.{1} R) (ULift.{1} R) ⟶ F.obj.obj (op U)` to `ModuleCat.ofHom (LinearMap.toSpanSingleton _ _ y)`. Establish `hxy : fx = fy`.

Use `hsh.ext (fun V g hg => ?_)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `fx ≫ F.obj.map g.op = fy ≫ F.obj.map g.op`. Use `ModuleCat.hom_ext (LinearMap.ext_ring ?_)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(F.obj.map g.op).hom (fx.hom 1) = (F.obj.map g.op).hom (fy.hom 1)`. Simplify `hP V g hg` using `[fx, fy]`.

Use `congrArg (fun f => f.hom 1) hxy` as an intermediate fact. Simplify `this` using `[fx, fy]`.
-/
theorem sec_eq_of_loc {R : Type} [CommRing R] (F : Shv R) {U : Scheme.{0}} (x y : Sec F U)
    (h : Loc U fun V g => Sec.res g x = Sec.res g y) : x = y := by
  obtain ⟨S, hS, hP⟩ := h
  have hsh := (F.property (ModuleCat.of (ULift.{1} R) (ULift.{1} R)) S hS).isSeparatedFor
  let fx : ModuleCat.of (ULift.{1} R) (ULift.{1} R) ⟶ F.obj.obj (op U) :=
    ModuleCat.ofHom (LinearMap.toSpanSingleton _ _ x)
  let fy : ModuleCat.of (ULift.{1} R) (ULift.{1} R) ⟶ F.obj.obj (op U) :=
    ModuleCat.ofHom (LinearMap.toSpanSingleton _ _ y)
  have hxy : fx = fy := by
    refine hsh.ext (fun V g hg => ?_)
    change fx ≫ F.obj.map g.op = fy ≫ F.obj.map g.op
    refine ModuleCat.hom_ext (LinearMap.ext_ring ?_)
    change (F.obj.map g.op).hom (fx.hom 1) = (F.obj.map g.op).hom (fy.hom 1)
    simpa [fx, fy] using hP V g hg
  have := congrArg (fun f => f.hom 1) hxy
  simpa [fx, fy] using this

def LeafUnitPairG : Prop := ∀ (q : ℕ) [NeZero q] (i : ℤ), ∃ ν : Pair (res _ (tw q 0)) (res _ (tw q i)) (res _ (tw q i)),
  ∀ (U : Scheme.{0}) (t : ℤ) (ζ : Prim q Γ(U, ⊤)) (b : Sec ((res _ (tw q i)).X t) U),
    ν.mul U 0 t t (zero_add t) (resGen 0 ζ) b = b

/- English proof (translation)
Introduce `q _ i`. Take `⟨ν, hν⟩` from `h q i`. Use `⟨ν, fun U t a b ha => sec_eq_of_loc _ _ _ ?_⟩` and prove the remaining obligations. Take `⟨S, hS, hP⟩` from `ha`. Use `⟨S, hS, fun V g hg => ?_⟩` and prove the remaining obligations.

Take `⟨ζ, hζ⟩` from `hP V g hg`. Rewrite using `[ν.nat g 0 t t (zero_add t) a b, hζ, hν]`.
-/
theorem unitPairLoc_of (h : LeafUnitPairG) : UnitPairLoc := by
  intro q _ i
  obtain ⟨ν, hν⟩ := h q i
  refine ⟨ν, fun U t a b ha => sec_eq_of_loc _ _ _ ?_⟩
  obtain ⟨S, hS, hP⟩ := ha
  refine ⟨S, hS, fun V g hg => ?_⟩
  obtain ⟨ζ, hζ⟩ := hP V g hg
  rw [ν.nat g 0 t t (zero_add t) a b, hζ, hν]

/- English proof (translation)
Introduce `q _ i`. Take `⟨ν, hν⟩` from `h q i`. Establish `key : ∀ k (_ : i = k), ∃ μ : Pair (res _ (tw q 0)) (res _ (tw q i)) (res _ (tw q k)), ∀ U s t w (hw : s + t = w) a b, HEq (μ.mul U s t w hw a b) (ν.mul U s t w hw a b)`. Introduce and unpack `k rfl`. Conclude with `⟨ν, fun _ _ _ _ _ _ _ => HEq.rfl⟩`.

Take `⟨μ, hμ⟩` from `key (0 + i) (zero_add i).symm`. Establish `gen : ∀ U t w w' (h1 : 0 + t = w) (h2 : 0 + t = w') (_ : w = w') a b, HEq (ν.mul U 0 t w h1 a b) (ν.mul U 0 t w' h2 a b)`. Introduce `U t w w' h1 h2 e a b`. Substitute `e` using the available equality. Both sides reduce to the same expression.

Establish `hgen : ∀ k (_ : k = i) (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)), HEq (resGen k ζ) (resGen i ζ)`. Introduce and unpack `k rfl U ζ`. Both sides reduce to the same expression. Use `⟨μ, ?_, ?_⟩` and prove the remaining obligations. Introduce `U ζ`.

Establish `hloc : Loc U (fun V g => ∃ ζ' : Prim q Γ(V, ⊤), Sec.res g (resGen 0 ζ) = resGen 0 ζ')` using `⟨⊤, GrothendieckTopology.top_mem _ _, fun _ g _ => ⟨_, resGen_res' 0 g ζ⟩⟩`. Conclude with `eq_of_heq ((hμ U 0 0 0 _ _ _).trans ((heq_of_eq (hν U 0 _ _ hloc)).trans (hgen _ (zero_add i) U ζ).symm))`. Introduce `U t w hw a b ha`. Conclude with `(hμ U 0 t w hw a b).trans ((gen U t w t hw (zero_add t) (by omega) a b).trans (heq_of_eq (hν U t a b ha)))`.
-/
theorem leafUnitPair_of_loc (h : UnitPairLoc) : LeafUnitPair := by
  intro q _ i
  obtain ⟨ν, hν⟩ := h q i
  have key : ∀ k (_ : i = k), ∃ μ : Pair (res _ (tw q 0)) (res _ (tw q i)) (res _ (tw q k)),
      ∀ U s t w (hw : s + t = w) a b, HEq (μ.mul U s t w hw a b) (ν.mul U s t w hw a b) := by
    rintro k rfl
    exact ⟨ν, fun _ _ _ _ _ _ _ => HEq.rfl⟩
  obtain ⟨μ, hμ⟩ := key (0 + i) (zero_add i).symm
  have gen : ∀ U t w w' (h1 : 0 + t = w) (h2 : 0 + t = w') (_ : w = w') a b,
      HEq (ν.mul U 0 t w h1 a b) (ν.mul U 0 t w' h2 a b) := by
    intro U t w w' h1 h2 e a b
    subst e
    rfl
  have hgen : ∀ k (_ : k = i) (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)), HEq (resGen k ζ) (resGen i ζ) := by
    rintro k rfl U ζ
    rfl
  refine ⟨μ, ?_, ?_⟩
  · intro U ζ
    have hloc : Loc U (fun V g => ∃ ζ' : Prim q Γ(V, ⊤), Sec.res g (resGen 0 ζ) = resGen 0 ζ') :=
      ⟨⊤, GrothendieckTopology.top_mem _ _, fun _ g _ => ⟨_, resGen_res' 0 g ζ⟩⟩
    exact eq_of_heq ((hμ U 0 0 0 _ _ _).trans ((heq_of_eq (hν U 0 _ _ hloc)).trans (hgen _ (zero_add i) U ζ).symm))
  · intro U t w hw a b ha
    exact (hμ U 0 t w hw a b).trans ((gen U t w t hw (zero_add t) (by omega) a b).trans (heq_of_eq (hν U t a b ha)))

/- English proof (translation)
The claim follows from `leafUnitPair_of_loc (unitPairLoc_of h)`.
-/
theorem LeafUnitPair_of (h : LeafUnitPairG) : LeafUnitPair := leafUnitPair_of_loc (unitPairLoc_of h)

end LateralTheory.E.LeafUnitPairPf
