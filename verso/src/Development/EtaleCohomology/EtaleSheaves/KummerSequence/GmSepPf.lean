import Development.EtaleCohomology.EtaleSheaves.KummerSequence.LeafKumMuInjPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.H2CurveOrder.GmSepPf

def ev (V : Scheme.{0}) (a : Γ(V, ⊤)) : CommRingCat.of (Polynomial ℤ) ⟶ Γ(V, ⊤) :=
  CommRingCat.ofHom (Polynomial.eval₂RingHom (Int.castRingHom _) a)

def lineMap (V : Scheme.{0}) (a : Γ(V, ⊤)) : V ⟶ Spec (CommRingCat.of (Polynomial ℤ)) :=
  ΓSpec.adjunction.homEquiv V (op (CommRingCat.of (Polynomial ℤ))) (ev V a).op

/- English proof (translation)
Establish `h1` using `(ΓSpec.adjunction.homEquiv _ _).injective h`. Establish `h2` using `congrArg (fun f => f.hom Polynomial.X) (Quiver.Hom.op_inj h1)`. Simplify `h2` using `[ev]`.
-/
theorem lineMap_inj (V : Scheme.{0}) (a b : Γ(V, ⊤)) (h : lineMap V a = lineMap V b) : a = b := by
  have h1 := (ΓSpec.adjunction.homEquiv _ _).injective h
  have h2 := congrArg (fun f => f.hom Polynomial.X) (Quiver.Hom.op_inj h1)
  simpa [ev] using h2

/- English proof (translation)
Apply `CommRingCat.hom_ext` to reduce the goal to its premises. Apply `Polynomial.ringHom_ext` to reduce the goal to its premises. Introduce `n`. Simplify using `[ev]`. Simplify using `[ev]`.
-/
theorem ev_comp {W V : Scheme.{0}} (g : W ⟶ V) (a : Γ(V, ⊤)) : ev V a ≫ g.appTop = ev W (g.appTop a) := by
  apply CommRingCat.hom_ext
  apply Polynomial.ringHom_ext
  · intro n; simp [ev]
  · simp [ev]

/- English proof (translation)
Unfold `lineMap`. Use `(ΓSpec.adjunction.homEquiv_naturality_left g (ev V a).op).symm.trans ?_` and prove the remaining obligations. Use `congr 1`. Apply `Quiver.Hom.unop_inj` to reduce the goal to its premises. Conclude with `ev_comp g a`.
-/
theorem lineMap_nat {W V : Scheme.{0}} (g : W ⟶ V) (a : Γ(V, ⊤)) :
    g ≫ lineMap V a = lineMap W (g.appTop a) := by
  unfold lineMap
  refine (ΓSpec.adjunction.homEquiv_naturality_left g (ev V a).op).symm.trans ?_
  congr 1
  apply Quiver.Hom.unop_inj
  exact ev_comp g a

/- English proof (translation)
Establish `: Scheme.etaleTopology.{0}.Subcanonical` using `GrothendieckTopology.Subcanonical.of_le Scheme.etaleTopology_le_proetaleTopology`. Establish `hsh` using `GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable (J := Scheme.etaleTopology.{0}) (yoneda.obj (Spec (CommRingCat.of (Polynomial ℤ))))`. Apply `lineMap_inj` to reduce the goal to its premises. Use `(hsh S hS).isSeparatedFor.ext (fun W g hg => ?_)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `g ≫ lineMap V a = g ≫ lineMap V b`.

Rewrite using `[lineMap_nat, lineMap_nat, h W g hg]`.
-/
theorem gamma_sep (V : Scheme.{0}) (S : Sieve V) (hS : S ∈ Scheme.etaleTopology V) (a b : Γ(V, ⊤))
    (h : ∀ (W : Scheme.{0}) (g : W ⟶ V), S.arrows g → g.appTop a = g.appTop b) : a = b := by
  have : Scheme.etaleTopology.{0}.Subcanonical :=
    GrothendieckTopology.Subcanonical.of_le Scheme.etaleTopology_le_proetaleTopology
  have hsh := GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable (J := Scheme.etaleTopology.{0})
    (yoneda.obj (Spec (CommRingCat.of (Polynomial ℤ))))
  apply lineMap_inj
  refine (hsh S hS).isSeparatedFor.ext (fun W g hg => ?_)
  change g ≫ lineMap V a = g ≫ lineMap V b
  rw [lineMap_nat, lineMap_nat, h W g hg]

/- English proof (translation)
Introduce `V u h`. Establish `h0 : ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ unitsF)).app (op V)).hom (ULift.up (Additive.ofMul u)) = ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ unitsF)).app (op V)).hom 0`. Rewrite using `[map_zero]`. Conclude with `h`. Establish `hm` using `Presheaf.equalizerSieve_mem Scheme.etaleTopology (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ unitsF)) (X := op V) (ULift.up (Additive.ofMul u) : (Scheme.Γ ⋙ unitsF).obj (op V)) 0 h0`.

Apply `Units.ext` to reduce the goal to its premises. Use `gamma_sep V _ hm u.1 (1 : Γ(V, ⊤)) (fun W g hg => ?_)` and prove the remaining obligations. Establish `h1` using `congrArg (fun z : (Scheme.Γ ⋙ unitsF).obj (op W) => ((Additive.toMul z.down : (Γ(W, ⊤))ˣ) : Γ(W, ⊤))) hg`. Conclude with `h1`.
-/
theorem gmSep : LateralTheory.E.H2CurveOrder.LeafKumMuInjPf.GmSep := by
  intro V u h
  have h0 : ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ unitsF)).app (op V)).hom (ULift.up (Additive.ofMul u))
      = ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ unitsF)).app (op V)).hom 0 := by
    rw [map_zero]; exact h
  have hm := Presheaf.equalizerSieve_mem Scheme.etaleTopology
    (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ unitsF)) (X := op V)
    (ULift.up (Additive.ofMul u) : (Scheme.Γ ⋙ unitsF).obj (op V)) 0 h0
  apply Units.ext
  refine gamma_sep V _ hm u.1 (1 : Γ(V, ⊤)) (fun W g hg => ?_)
  have h1 := congrArg (fun z : (Scheme.Γ ⋙ unitsF).obj (op W) => ((Additive.toMul z.down : (Γ(W, ⊤))ˣ) : Γ(W, ⊤))) hg
  exact h1

/- English proof (translation)
The claim follows from `gmSep`.
-/
theorem GmSep_of : LateralTheory.E.H2CurveOrder.LeafKumMuInjPf.GmSep := gmSep

end LateralTheory.E.H2CurveOrder.GmSepPf
