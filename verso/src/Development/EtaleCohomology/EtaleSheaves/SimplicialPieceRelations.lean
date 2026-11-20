import Development.EtaleCohomology.EtaleSheaves.FiltPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.TruncationPieces LateralTheory.E.FiltPf

namespace LateralTheory.E.SimplicialPieceRelations

abbrev Qt (R : Type) [CommRing R] := HomotopyCategory.quotient (Shv R) (ComplexShape.up ℤ)
abbrev HC (R : Type) [CommRing R] := HomotopyCategory (Shv R) (ComplexShape.up ℤ)

def Disc0 : Prop := ∀ (R : Type) [CommRing R] {X Y : PSh} (f : X ⟶ Y),
  ∃ (a : (Qt R).obj ((chains R).obj (disc.obj X)) ≅ (Qt R).obj ((HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) 0).obj ((free R).obj X)))
    (b : (Qt R).obj ((chains R).obj (disc.obj Y)) ≅ (Qt R).obj ((HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) 0).obj ((free R).obj Y))),
    (Qt R).map ((chains R).map (disc.map f)) ≫ b.hom = a.hom ≫ (Qt R).map ((HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) 0).map ((free R).map f))

variable {R : Type} [CommRing R]

/- English proof (translation)
Establish `hg' : g' = a.inv ≫ g ≫ b.hom` using `by rw [h]; simp`. Introduce and unpack `⟨hs, hi⟩`. Use `⟨fun y => ?_, fun x1 x2 hx => ?_⟩` and prove the remaining obligations. Take `⟨x, hx⟩` from `hs (a.hom ≫ y)`. Use `⟨b.inv ≫ x, ?_⟩` and prove the remaining obligations.

Simplify using `only at hx ⊢`. Rewrite using `[hg']`. Simplify using `[hx]`. Simplify using `only at hx`. Rewrite `hx` using `[hg']`.

Establish `: g ≫ (b.hom ≫ x1) = g ≫ (b.hom ≫ x2)`. Use `congrArg (fun z => a.hom ≫ z) hx` as an intermediate fact. Simplify using `using this`. Use `hi this` as an intermediate fact. Simplify using `using congrArg (fun z => b.inv ≫ z) this`.
-/
theorem relY_conj_imp (F : Shv R) (n : ℤ) {A B A' B' : HC R} (g : A ⟶ B) (g' : A' ⟶ B') (a : A ≅ A') (b : B ≅ B')
    (h : g ≫ b.hom = a.hom ≫ g') : Tri.RelY (Yres R F) n g → Tri.RelY (Yres R F) n g' := by
  have hg' : g' = a.inv ≫ g ≫ b.hom := by rw [h]; simp
  rintro ⟨hs, hi⟩
  refine ⟨fun y => ?_, fun x1 x2 hx => ?_⟩
  · obtain ⟨x, hx⟩ := hs (a.hom ≫ y)
    refine ⟨b.inv ≫ x, ?_⟩
    simp only at hx ⊢
    rw [hg']; simp [hx]
  · simp only at hx
    rw [hg'] at hx
    have : g ≫ (b.hom ≫ x1) = g ≫ (b.hom ≫ x2) := by
      have := congrArg (fun z => a.hom ≫ z) hx
      simpa using this
    have := hi this
    simpa using congrArg (fun z => b.inv ≫ z) this

/- English proof (translation)
Assemble the required witnesses or components as `⟨relY_conj_imp F n g g' a b h, relY_conj_imp F n g' g a.symm b.symm (by rw [Iso.symm_hom, Iso.symm_hom, Iso.eq_inv_comp, ← Category.assoc, ← h]; simp)⟩`.
-/
theorem relY_conj (F : Shv R) (n : ℤ) {A B A' B' : HC R} (g : A ⟶ B) (g' : A' ⟶ B') (a : A ≅ A') (b : B ≅ B')
    (h : g ≫ b.hom = a.hom ≫ g') : Tri.RelY (Yres R F) n g ↔ Tri.RelY (Yres R F) n g' :=
  ⟨relY_conj_imp F n g g' a b h, relY_conj_imp F n g' g a.symm b.symm (by
    rw [Iso.symm_hom, Iso.symm_hom, Iso.eq_inv_comp, ← Category.assoc, ← h]; simp)⟩

def yIso (F : Shv R) (p m c : ℤ) (hc : m + p = c) : Yres R F c ≅ (Yres R F m)⟦p⟧ :=
  (Qt R).mapIso ((shiftFunctorAdd' (Cx R) m p c hc).app (res R F)) ≪≫ ((Qt R).commShiftIso p).app _

/- English proof (translation)
Introduce and unpack `⟨hs, hi⟩`. Use `⟨fun y => ?_, fun x1 x2 hx => ?_⟩` and prove the remaining obligations. Set `e` to `yIso F p (k - 1) (k + p - 1) (by omega)`. Take `⟨z, hz⟩` from `(shiftFunctor (HC R) p).map_surjective (y ≫ e.hom)`. Take `⟨w, hw⟩` from `hs z`.

Use `⟨(shiftFunctor (HC R) p).map w ≫ e.inv, ?_⟩` and prove the remaining obligations. Simplify using `only at hw ⊢`. Rewrite using `[← Category.assoc, ← Functor.map_comp, hw, hz]`. Simplify using the standard rewrite rules. Set `e` to `yIso F p k (k + p) rfl`.

Take `⟨w1, hw1⟩` from `(shiftFunctor (HC R) p).map_surjective (x1 ≫ e.hom)`. Take `⟨w2, hw2⟩` from `(shiftFunctor (HC R) p).map_surjective (x2 ≫ e.hom)`. Simplify using `only at hx`. Establish `h1 : (shiftFunctor (HC R) p).map (g ≫ w1) = (shiftFunctor (HC R) p).map (g ≫ w2)`. Rewrite using `[Functor.map_comp, Functor.map_comp, hw1, hw2, ← Category.assoc, ← Category.assoc, hx]`.

Establish `h2` using `hi ((shiftFunctor (HC R) p).map_injective h1)`. Establish `: x1 ≫ e.hom = x2 ≫ e.hom` using `by rw [← hw1, ← hw2, h2]`. Simplify using `using congrArg (fun z => z ≫ e.inv) this`.
-/
theorem relY_shift (F : Shv R) (k p : ℤ) {A B : HC R} (g : A ⟶ B) :
    Tri.RelY (Yres R F) k g → Tri.RelY (Yres R F) (k + p) (g⟦p⟧') := by
  rintro ⟨hs, hi⟩
  refine ⟨fun y => ?_, fun x1 x2 hx => ?_⟩
  · let e := yIso F p (k - 1) (k + p - 1) (by omega)
    obtain ⟨z, hz⟩ := (shiftFunctor (HC R) p).map_surjective (y ≫ e.hom)
    obtain ⟨w, hw⟩ := hs z
    refine ⟨(shiftFunctor (HC R) p).map w ≫ e.inv, ?_⟩
    simp only at hw ⊢
    rw [← Category.assoc, ← Functor.map_comp, hw, hz]; simp
  · let e := yIso F p k (k + p) rfl
    obtain ⟨w1, hw1⟩ := (shiftFunctor (HC R) p).map_surjective (x1 ≫ e.hom)
    obtain ⟨w2, hw2⟩ := (shiftFunctor (HC R) p).map_surjective (x2 ≫ e.hom)
    simp only at hx
    have h1 : (shiftFunctor (HC R) p).map (g ≫ w1) = (shiftFunctor (HC R) p).map (g ≫ w2) := by
      rw [Functor.map_comp, Functor.map_comp, hw1, hw2, ← Category.assoc, ← Category.assoc, hx]
    have h2 := hi ((shiftFunctor (HC R) p).map_injective h1)
    have : x1 ≫ e.hom = x2 ≫ e.hom := by rw [← hw1, ← hw2, h2]
    simpa using congrArg (fun z => z ≫ e.inv) this

/- English proof (translation)
Simplify using `only [chains, chainsXIso, Functor.comp_map]`. Use `erw [HomologicalComplex.extendMap_f _ ComplexShape.embeddingDownNat (i := p) rfl]`. Both sides reduce to the same expression.
-/
theorem chains_f (U E : Spc) (u : U ⟶ E) (p : ℕ) :
    ((chains R).map u).f (-(p : ℤ)) =
      (chainsXIso R U p).hom ≫ (free R).map (u.app (Opposite.op (SimplexCategory.mk p))) ≫ (chainsXIso R E p).inv := by
  dsimp only [chains, chainsXIso, Functor.comp_map]
  erw [HomologicalComplex.extendMap_f _ ComplexShape.embeddingDownNat (i := p) rfl]
  rfl

/- English proof (translation)
Introduce `R _ F U E u p k h`. Set `f` to `u.app (Opposite.op (SimplexCategory.mk p))`. Set `s0` to `(HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) 0).map ((free R).map f)`. Establish `h1 : Tri.RelY (Yres R F) k ((Qt R).map ((chains R).map (disc.map f)))` using `(relK_iff R _ F k).1 h`. Take `⟨a, b, hab⟩` from `hD R f`.

Establish `h2 : Tri.RelY (Yres R F) k ((Qt R).map s0)` using `(relY_conj F k _ _ a b hab).1 h1`. Establish `h3` using `relY_shift F k (p : ℤ) _ h2`. Establish `h4 : Tri.RelY (Yres R F) (k + p) ((Qt R).map (s0⟦(p : ℤ)⟧'))` using `(relY_conj F _ _ _ (((Qt R).commShiftIso (p : ℤ)).app _) (((Qt R).commShiftIso (p : ℤ)).app _) (((Qt R).commShiftIso (p : ℤ)).hom.naturality s0)).2 h3`. Set `Eo` to `(CochainComplex.singleFunctors (Shv R)).shiftIso (p : ℤ) (-(p : ℤ)) 0 (by omega)`. Establish `h5 : Tri.RelY (Yres R F) (k + p) ((Qt R).map ((CochainComplex.singleFunctor (Shv R) (-(p : ℤ))).map ((free R).map f)))` using `(relY_conj F _ _ _ ((Qt R).mapIso (Eo.symm.app _)) ((Qt R).mapIso (Eo.symm.app _)) (by`.

Simplify using `only [Functor.mapIso_hom, Iso.app_hom, Iso.symm_hom, ← Functor.map_comp]`. Use `congr 1`. Conclude with `Eo.inv.naturality _)).2 h4`. Use `(relK_iff R _ F (k + p)).2 ?_` and prove the remaining obligations. Use `(relY_conj F _ _ _ ((Qt R).mapIso ((HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) (-(p : ℤ))).mapIso (chainsXIso R U p))) ((Qt R).mapIso ((HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) (-(p : ℤ))).mapIso (chainsXIso R E p))) ?_).2 h5` and prove the remaining obligations.

Simplify using `only [piece, Functor.mapIso_hom, ← Functor.map_comp, chains_f]`. Simplify using `[f]`. Both sides reduce to the same expression.
-/
theorem piece_of (hD : Disc0) : Piece := by
  intro R _ F U E u p k h
  let f := u.app (Opposite.op (SimplexCategory.mk p))
  let s0 := (HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) 0).map ((free R).map f)
  have h1 : Tri.RelY (Yres R F) k ((Qt R).map ((chains R).map (disc.map f))) := (relK_iff R _ F k).1 h
  obtain ⟨a, b, hab⟩ := hD R f
  have h2 : Tri.RelY (Yres R F) k ((Qt R).map s0) := (relY_conj F k _ _ a b hab).1 h1
  have h3 := relY_shift F k (p : ℤ) _ h2
  have h4 : Tri.RelY (Yres R F) (k + p) ((Qt R).map (s0⟦(p : ℤ)⟧')) :=
    (relY_conj F _ _ _ (((Qt R).commShiftIso (p : ℤ)).app _) (((Qt R).commShiftIso (p : ℤ)).app _)
      (((Qt R).commShiftIso (p : ℤ)).hom.naturality s0)).2 h3
  let Eo := (CochainComplex.singleFunctors (Shv R)).shiftIso (p : ℤ) (-(p : ℤ)) 0 (by omega)
  have h5 : Tri.RelY (Yres R F) (k + p) ((Qt R).map ((CochainComplex.singleFunctor (Shv R) (-(p : ℤ))).map ((free R).map f))) :=
    (relY_conj F _ _ _ ((Qt R).mapIso (Eo.symm.app _)) ((Qt R).mapIso (Eo.symm.app _)) (by
      simp only [Functor.mapIso_hom, Iso.app_hom, Iso.symm_hom, ← Functor.map_comp]
      congr 1
      exact Eo.inv.naturality _)).2 h4
  refine (relK_iff R _ F (k + p)).2 ?_
  refine (relY_conj F _ _ _ ((Qt R).mapIso ((HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) (-(p : ℤ))).mapIso (chainsXIso R U p)))
    ((Qt R).mapIso ((HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) (-(p : ℤ))).mapIso (chainsXIso R E p))) ?_).2 h5
  simp only [piece, Functor.mapIso_hom, ← Functor.map_comp, chains_f]
  simp [f]
  rfl

end LateralTheory.E.SimplicialPieceRelations
