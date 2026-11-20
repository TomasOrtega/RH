import Development.EtaleCohomology.EtaleSheaves.LeafTw0LocSplitOf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafTw0LocSplitPfM

/- English proof (translation)
The claim follows from `inferInstance`.
-/
theorem iso_inv_mono' {C : Type*} [Category C] {X Y : C} (e : X ≅ Y) : Mono e.inv := inferInstance

/- English proof (translation)
Unfold `resι`. Rewrite using `[InjectiveResolution.ι'_f_zero]`. Establish `h0 : Mono ((injectiveResolution F).ι.f 0)` using `inferInstance`. Conclude with `@mono_comp _ _ _ _ _ _ inferInstance _ (@mono_comp _ _ _ _ _ _ inferInstance _ (@mono_comp _ _ _ _ _ _ h0 _ (iso_inv_mono' _)))`.
-/
theorem resι_mono {R : Type} [CommRing R] (F : Shv R) : Mono (resι R F) := by
  unfold resι
  rw [InjectiveResolution.ι'_f_zero]
  have h0 : Mono ((injectiveResolution F).ι.f 0) := inferInstance
  exact @mono_comp _ _ _ _ _ _ inferInstance _ (@mono_comp _ _ _ _ _ _ inferInstance _ (@mono_comp _ _ _ _ _ _ h0 _ (iso_inv_mono' _)))

/- English proof (translation)
Establish `h1 : Mono ((sheafToPresheaf _ _).map φ)` using `inferInstance`. Establish `h2 : Mono (((sheafToPresheaf _ _).map φ).app (op U))` using `inferInstance`. Conclude with `(ModuleCat.mono_iff_injective _).1 h2`.
-/
theorem sec_inj {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) [Mono φ] (U : Scheme.{0}) :
    Function.Injective (fun x : Sec F U => Sec.map φ x) := by
  have h1 : Mono ((sheafToPresheaf _ _).map φ) := inferInstance
  have h2 : Mono (((sheafToPresheaf _ _).map φ).app (op U)) := inferInstance
  exact (ModuleCat.mono_iff_injective _).1 h2

def LeafTw0TwFree : Prop := ∀ (q : ℕ) [NeZero q] (V : Scheme.{0}) (ζ : Prim q Γ(V, ⊤)),
  twGen 0 ζ = 0 ∨ ∀ c : ULift.{1} (ZMod q), c • twGen 0 ζ = 0 → c = 0

/- English proof (translation)
Introduce `q _ V ζ`. Break down `h q V ζ with h0 | h1` into its components or cases. Conclude with `Or.inl h0`. Use `right`. Introduce `c hc`.

Apply `h1 c` to reduce the goal to its premises. Establish `: Mono (resι (ZMod q) (tw q 0))` using `resι_mono _`. Apply `sec_inj (resι (ZMod q) (tw q 0)) V` to reduce the goal to its premises. Use `show Sec.map (resι (ZMod q) (tw q 0)) (c • twGen 0 ζ) = Sec.map (resι (ZMod q) (tw q 0)) 0`. Rewrite using `[show Sec.map (resι (ZMod q) (tw q 0)) (c • twGen 0 ζ) = c • resGen 0 ζ from map_smul ((resι (ZMod q) (tw q 0)).hom.app (op V)).hom c _, hc]`.

Simplify using `[Sec.map]`.
-/
theorem LeafTw0GenFree_of (h : LeafTw0TwFree) : LateralTheory.E.LeafTw0LocSplitPf.LeafTw0GenFree := by
  intro q _ V ζ
  rcases h q V ζ with h0 | h1
  · exact Or.inl h0
  · right
    intro c hc
    apply h1 c
    have : Mono (resι (ZMod q) (tw q 0)) := resι_mono _
    apply sec_inj (resι (ZMod q) (tw q 0)) V
    show Sec.map (resι (ZMod q) (tw q 0)) (c • twGen 0 ζ) = Sec.map (resι (ZMod q) (tw q 0)) 0
    rw [show Sec.map (resι (ZMod q) (tw q 0)) (c • twGen 0 ζ) = c • resGen 0 ζ from
      map_smul ((resι (ZMod q) (tw q 0)).hom.app (op V)).hom c _, hc]
    simp [Sec.map]

/- English proof (translation)
The claim follows from `LateralTheory.E.LeafTw0LocSplitPf.LeafTw0LocSplit_of h1 (LeafTw0GenFree_of h2)`.
-/
theorem LeafTw0LocSplit_of (h1 : LateralTheory.E.LeafTw0LocSplitPf.LeafTw0LocGen) (h2 : LeafTw0TwFree) :
    LateralTheory.E.LeafTensMonoPf.LeafTw0LocSplit :=
  LateralTheory.E.LeafTw0LocSplitPf.LeafTw0LocSplit_of h1 (LeafTw0GenFree_of h2)

end LateralTheory.E.LeafTw0LocSplitPfM
