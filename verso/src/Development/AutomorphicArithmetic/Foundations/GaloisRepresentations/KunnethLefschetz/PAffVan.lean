import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.BasisOne

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace UpperTheory.Gal.KunnethLefschetz
open scoped TensorProduct DirectSum

/- English proof (translation)
Establish `hid : spMap (e : A →+* B) ≫ spMap (e.symm : B →+* A) = 𝟙 (sp B)`. Simplify using `only [spMap, ← Functor.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp]`. Establish `: (e : A →+* B).comp (e.symm : B →+* A) = RingHom.id B`. Use extensionality with `x`. Simplify using the standard rewrite rules.

Rewrite using `[this]`. Simplify using the standard rewrite rules. Use `⟨fun x y => ?_⟩` and prove the remaining obligations. Establish `hx : x = pull (ZMod q) (spMap (e : A →+* B)) (tw q i) n (pull (ZMod q) (spMap (e.symm : B →+* A)) (tw q i) n x)`. Rewrite using `[← pull_comp, hid, pull_id]`.

Establish `hy : y = pull (ZMod q) (spMap (e : A →+* B)) (tw q i) n (pull (ZMod q) (spMap (e.symm : B →+* A)) (tw q i) n y)`. Rewrite using `[← pull_comp, hid, pull_id]`. Rewrite using `[hx, hy, Subsingleton.elim (pull (ZMod q) (spMap (e.symm : B →+* A)) (tw q i) n x) (pull (ZMod q) (spMap (e.symm : B →+* A)) (tw q i) n y)]`.
-/
private theorem sub_of_equiv {A B : Type} [CommRing A] [CommRing B] (e : A ≃+* B) (q : ℕ) (n i : ℤ)
    (h : Subsingleton (Ht q (sp A) n i)) : Subsingleton (Ht q (sp B) n i) := by
  have hid : spMap (e : A →+* B) ≫ spMap (e.symm : B →+* A) = 𝟙 (sp B) := by
    simp only [spMap, ← Functor.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have : (e : A →+* B).comp (e.symm : B →+* A) = RingHom.id B := by
      ext x
      simp
    rw [this]
    simp
  refine ⟨fun x y => ?_⟩
  have hx : x = pull (ZMod q) (spMap (e : A →+* B)) (tw q i) n
      (pull (ZMod q) (spMap (e.symm : B →+* A)) (tw q i) n x) := by
    rw [← pull_comp, hid, pull_id]
  have hy : y = pull (ZMod q) (spMap (e : A →+* B)) (tw q i) n
      (pull (ZMod q) (spMap (e.symm : B →+* A)) (tw q i) n y) := by
    rw [← pull_comp, hid, pull_id]
  rw [hx, hy, Subsingleton.elim (pull (ZMod q) (spMap (e.symm : B →+* A)) (tw q i) n x)
    (pull (ZMod q) (spMap (e.symm : B →+* A)) (tw q i) n y)]

/- English proof (translation)
Introduce `hIn hPt k _ _ q _ hq d n i hn`. Use `show Subsingleton (Ht q (sp (MvPolynomial (Fin d) k)) n i)`. Proceed by induction on `d with`. Consider the case `zero`. Establish `h0 : Subsingleton (Ht q (sp k) n i)` using `hPt hIn k q n i hn`.

Conclude with `sub_of_equiv (MvPolynomial.isEmptyRingEquiv k (Fin 0)).symm q n i h0`. Consider the case `succ d ih`. Establish `hq' : IsUnit ((q : ℕ) : MvPolynomial (Fin d) k)`. Use `hq.map (MvPolynomial.C : k →+* MvPolynomial (Fin d) k)` as an intermediate fact. Rewrite `this` using `[map_natCast]`. Then use the resulting hypothesis.

Establish `hpoly : Subsingleton (Ht q (sp (Polynomial (MvPolynomial (Fin d) k))) n i)`. Establish `hb` using `hIn.c4 q (MvPolynomial (Fin d) k) hq' i n`. Use `⟨fun x y => ?_⟩` and prove the remaining obligations. Take `⟨a, rfl⟩` from `hb.2 x`. Take `⟨b, rfl⟩` from `hb.2 y`.

Rewrite using `[Subsingleton.elim a b]`. Conclude with `sub_of_equiv (MvPolynomial.finSuccEquiv k d).toRingEquiv.symm q n i hpoly`.
-/
theorem UpperTheory.Gal.KunnethLefschetz.affVan_holds :
    UpperTheory.Gal.KunnethLefschetz.AffVan := by
  intro hIn hPt k _ _ q _ hq d n i hn
  show Subsingleton (Ht q (sp (MvPolynomial (Fin d) k)) n i)
  induction d with
  | zero =>
    have h0 : Subsingleton (Ht q (sp k) n i) := hPt hIn k q n i hn
    exact sub_of_equiv (MvPolynomial.isEmptyRingEquiv k (Fin 0)).symm q n i h0
  | succ d ih =>
    have hq' : IsUnit ((q : ℕ) : MvPolynomial (Fin d) k) := by
      have := hq.map (MvPolynomial.C : k →+* MvPolynomial (Fin d) k)
      rwa [map_natCast] at this
    have hpoly : Subsingleton (Ht q (sp (Polynomial (MvPolynomial (Fin d) k))) n i) := by
      have hb := hIn.c4 q (MvPolynomial (Fin d) k) hq' i n
      refine ⟨fun x y => ?_⟩
      obtain ⟨a, rfl⟩ := hb.2 x
      obtain ⟨b, rfl⟩ := hb.2 y
      rw [Subsingleton.elim a b]
    exact sub_of_equiv (MvPolynomial.finSuccEquiv k d).toRingEquiv.symm q n i hpoly
