import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC.PrimColim

variable {J : Type} [SmallCategory J] [IsFiltered J] {D : J ⥤ CommRingCat.{0}} {c : Cocone D}

/- English proof (translation)
Rewrite using `[← c.w f]`. Both sides reduce to the same expression.
-/
theorem nat_apply {j k : J} (f : j ⟶ k) (a : D.obj j) :
    (c.ι.app k).hom ((D.map f).hom a) = (c.ι.app j).hom a := by
  rw [← c.w f]; rfl

/- English proof (translation)
Take `⟨j, y, h⟩` from `Concrete.isColimit_exists_rep D hc x`. Conclude with `⟨j, y, h⟩`.
-/
theorem exists_rep (hc : IsColimit c) (x : c.pt) : ∃ (j : J) (y : D.obj j), (c.ι.app j).hom y = x := by
  obtain ⟨j, y, h⟩ := Concrete.isColimit_exists_rep D hc x
  exact ⟨j, y, h⟩

/- English proof (translation)
Take `⟨k, f, g, hfg⟩` from `Concrete.isColimit_exists_of_rep_eq D hc a b h`. Use `⟨IsFiltered.coeq f g, f ≫ IsFiltered.coeqHom f g, ?_⟩` and prove the remaining obligations. Establish `hfg' : (D.map f).hom a = (D.map g).hom b` using `hfg`. Establish `e` using `IsFiltered.coeq_condition f g`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem exists_eq (hc : IsColimit c) {j : J} (a b : D.obj j) (h : (c.ι.app j).hom a = (c.ι.app j).hom b) :
    ∃ (k : J) (f : j ⟶ k), (D.map f).hom a = (D.map f).hom b := by
  obtain ⟨k, f, g, hfg⟩ := Concrete.isColimit_exists_of_rep_eq D hc a b h
  refine ⟨IsFiltered.coeq f g, f ≫ IsFiltered.coeqHom f g, ?_⟩
  have hfg' : (D.map f).hom a = (D.map g).hom b := hfg
  have e := IsFiltered.coeq_condition f g
  calc (D.map (f ≫ IsFiltered.coeqHom f g)).hom a
      = (D.map (IsFiltered.coeqHom f g)).hom ((D.map f).hom a) := by rw [D.map_comp]; rfl
    _ = (D.map (IsFiltered.coeqHom f g)).hom ((D.map g).hom b) := by rw [hfg']
    _ = (D.map (g ≫ IsFiltered.coeqHom f g)).hom b := by rw [D.map_comp]; rfl
    _ = (D.map (f ≫ IsFiltered.coeqHom f g)).hom b := by rw [e]

/- English proof (translation)
The claim follows from `Polynomial.aeval_algHom_apply φ.toIntAlgHom a p`.
-/
theorem aeval_ringHom {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (a : A) (p : Polynomial ℤ) :
    Polynomial.aeval (φ a) p = φ (Polynomial.aeval a p) :=
  Polynomial.aeval_algHom_apply φ.toIntAlgHom a p

end GlobalTheory.EtC.PrimColim

open GlobalTheory.EtC.PrimColim in
/- English proof (translation)
Introduce `q J _ _ D c hc`. Use `⟨fun ζ => ?_, fun j ξ ξ' h => ?_⟩` and prove the remaining obligations. Take `⟨u, hu⟩` from `ζ.2.1.exists_right_inv`. Take `⟨j1, x, hx⟩` from `exists_rep hc ζ.1`. Take `⟨j2, y, hy⟩` from `exists_rep hc u`.

Use `set k := IsFiltered.max j1 j2`. Use `set x' := (D.map (IsFiltered.leftToMax j1 j2)).hom x`. Use `set y' := (D.map (IsFiltered.rightToMax j1 j2)).hom y`. Establish `hx' : (c.ι.app k).hom x' = ζ.1` using `by rw [nat_apply, hx]`. Establish `hy' : (c.ι.app k).hom y' = u` using `by rw [nat_apply, hy]`.

Establish `e1 : (c.ι.app k).hom ((q : D.obj k) * y') = (c.ι.app k).hom 1`. Rewrite using `[map_mul, map_natCast, hy', map_one, hu]`. Take `⟨k1, f1, hf1⟩` from `exists_eq hc _ _ e1`. Use `set x1 := (D.map f1).hom x'`. Establish `hx1 : (c.ι.app k1).hom x1 = ζ.1` using `by rw [nat_apply, hx']`.

Establish `e2 : (c.ι.app k1).hom (Polynomial.aeval x1 (Polynomial.cyclotomic q ℤ)) = (c.ι.app k1).hom 0`. Rewrite using `[map_zero, ← aeval_ringHom, hx1]`. Conclude with `ζ.2.2`. Take `⟨k2, f2, hf2⟩` from `exists_eq hc _ _ e2`. Establish `hu1 : (q : D.obj k1) * (D.map f1).hom y' = 1`.

Simplify `hf1` using `only [map_mul, map_natCast, map_one]`. Establish `hu2 : (q : D.obj k2) * (D.map f2).hom ((D.map f1).hom y') = 1`. Use `congrArg (D.map f2).hom hu1` as an intermediate fact. Simplify `this` using `only [map_mul, map_natCast, map_one]`. Establish `hr : Polynomial.aeval ((D.map f2).hom x1) (Polynomial.cyclotomic q ℤ) = 0`.

Rewrite using `[aeval_ringHom, hf2, map_zero]`. Use `⟨k2, ⟨(D.map f2).hom x1, IsUnit.of_mul_eq_one _ hu2, hr⟩, ?_⟩` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `(c.ι.app k2).hom ((D.map f2).hom x1) = ζ.1`. Rewrite using `[nat_apply, hx1]`.

Establish `h1 : (c.ι.app j).hom ξ.1 = (c.ι.app j).hom ξ'.1` using `congrArg Subtype.val h`. Take `⟨k, f, hf⟩` from `exists_eq hc _ _ h1`. Conclude with `⟨k, f, Subtype.ext hf⟩`.
-/
theorem GlobalTheory.EtC.prim_filtered_colimit : ∀ (q : ℕ) (J : Type) [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D), IsColimit c → (∀ ζ : Prim q c.pt, ∃ (j : J) (ξ : Prim q (D.obj j)), Prim.map (c.ι.app j).hom ξ = ζ) ∧ ∀ (j : J) (ξ ξ' : Prim q (D.obj j)), Prim.map (c.ι.app j).hom ξ = Prim.map (c.ι.app j).hom ξ' → ∃ (k : J) (f : j ⟶ k), Prim.map (D.map f).hom ξ = Prim.map (D.map f).hom ξ' := by
  intro q J _ _ D c hc
  refine ⟨fun ζ => ?_, fun j ξ ξ' h => ?_⟩
  · obtain ⟨u, hu⟩ := ζ.2.1.exists_right_inv
    obtain ⟨j1, x, hx⟩ := exists_rep hc ζ.1
    obtain ⟨j2, y, hy⟩ := exists_rep hc u
    set k := IsFiltered.max j1 j2
    set x' := (D.map (IsFiltered.leftToMax j1 j2)).hom x
    set y' := (D.map (IsFiltered.rightToMax j1 j2)).hom y
    have hx' : (c.ι.app k).hom x' = ζ.1 := by rw [nat_apply, hx]
    have hy' : (c.ι.app k).hom y' = u := by rw [nat_apply, hy]
    have e1 : (c.ι.app k).hom ((q : D.obj k) * y') = (c.ι.app k).hom 1 := by
      rw [map_mul, map_natCast, hy', map_one, hu]
    obtain ⟨k1, f1, hf1⟩ := exists_eq hc _ _ e1
    set x1 := (D.map f1).hom x'
    have hx1 : (c.ι.app k1).hom x1 = ζ.1 := by rw [nat_apply, hx']
    have e2 : (c.ι.app k1).hom (Polynomial.aeval x1 (Polynomial.cyclotomic q ℤ)) = (c.ι.app k1).hom 0 := by
      rw [map_zero, ← aeval_ringHom, hx1]; exact ζ.2.2
    obtain ⟨k2, f2, hf2⟩ := exists_eq hc _ _ e2
    have hu1 : (q : D.obj k1) * (D.map f1).hom y' = 1 := by
      simpa only [map_mul, map_natCast, map_one] using hf1
    have hu2 : (q : D.obj k2) * (D.map f2).hom ((D.map f1).hom y') = 1 := by
      have := congrArg (D.map f2).hom hu1
      simpa only [map_mul, map_natCast, map_one] using this
    have hr : Polynomial.aeval ((D.map f2).hom x1) (Polynomial.cyclotomic q ℤ) = 0 := by
      rw [aeval_ringHom, hf2, map_zero]
    refine ⟨k2, ⟨(D.map f2).hom x1, IsUnit.of_mul_eq_one _ hu2, hr⟩, ?_⟩
    apply Subtype.ext
    change (c.ι.app k2).hom ((D.map f2).hom x1) = ζ.1
    rw [nat_apply, hx1]
  · have h1 : (c.ι.app j).hom ξ.1 = (c.ι.app j).hom ξ'.1 := congrArg Subtype.val h
    obtain ⟨k, f, hf⟩ := exists_eq hc _ _ h1
    exact ⟨k, f, Subtype.ext hf⟩
