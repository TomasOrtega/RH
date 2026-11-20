import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentVarUnit

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory.EtC

def laurentMap {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) : LaurentPolynomial A →+* LaurentPolynomial B :=
  AddMonoidAlgebra.mapRingHom ℤ f

namespace GmPhiNat

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem laurentMap_C {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) :
    (laurentMap f).comp (LaurentPolynomial.C : A →+* LaurentPolynomial A) = (LaurentPolynomial.C : B →+* LaurentPolynomial B).comp f := by
  refine RingHom.ext fun a => ?_
  change AddMonoidAlgebra.mapRingHom ℤ f (LaurentPolynomial.C a) = LaurentPolynomial.C (f a)
  rw [← LaurentPolynomial.single_eq_C, AddMonoidAlgebra.mapRingHom_single]; rfl

/- English proof (translation)
Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities.
-/
theorem laurentMap_T {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (n : ℤ) :
    laurentMap f (LaurentPolynomial.T n) = LaurentPolynomial.T n := by
  change AddMonoidAlgebra.mapRingHom ℤ f (AddMonoidAlgebra.single n (1 : A)) = AddMonoidAlgebra.single n (1 : B)
  rw [AddMonoidAlgebra.mapRingHom_single, map_one]

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem laurentMap_comp {A B D : Type} [CommRing A] [CommRing B] [CommRing D] (f : A →+* B) (g : B →+* D) :
    laurentMap (g.comp f) = (laurentMap g).comp (laurentMap f) :=
  AddMonoidAlgebra.mapRingHom_comp _ _

/- English proof (translation)
Simplify using the standard rewrite rules. Both sides reduce to the same expression.
-/
theorem spMap_comp {A B D : Type} [CommRing A] [CommRing B] [CommRing D] (f : A →+* B) (g : B →+* D) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp only [spMap, ← Functor.map_comp, ← Spec.map_comp]
  rfl

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem pull_spMap_comp (q : ℕ) {A B D : Type} [CommRing A] [CommRing B] [CommRing D] (f : A →+* B) (g : B →+* D) (n i : ℤ)
    (x : Ht q (sp A) n i) : pull _ (spMap (g.comp f)) _ n x = pull _ (spMap g) _ n (pull _ (spMap f) _ n x) := by
  rw [spMap_comp, pull_comp]

/- English proof (translation)
Substitute using the available equality. Substitute using the available equality. Both sides reduce to the same expression.
-/
theorem pull_cast (q : ℕ) {E E' : Spc} (f : E ⟶ E') {n i n' i' : ℤ} (hn : n = n') (hi : i = i') (x : Ht q E' n i) :
    pull _ f (tw q i') n' (Ht.cast hn hi x) = Ht.cast hn hi (pull _ f (tw q i) n x) := by
  subst hn; subst hi; rfl

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities.
-/
theorem laurentVar_map {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) :
    Units.map (Spec.map (CommRingCat.ofHom (laurentMap f))).appTop.hom.toMonoidHom (laurentVar A) = laurentVar B := by
  apply Units.ext
  have h := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (laurentMap f))
  have h2 := congrArg (fun φ => φ.hom (LaurentPolynomial.T 1)) h
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h2
  simp only [laurentVar, laurentVarUnit, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe]
  rw [← h2, laurentMap_T]

/- English proof (translation)
Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.
-/
theorem isUnit_gamma (q : ℕ) (A : Type) [CommRing A] (hq : IsUnit (q : A)) :
    IsUnit (q : Γ(Spec (CommRingCat.of (LaurentPolynomial A)), ⊤)) := by
  have h := (hq.map (LaurentPolynomial.C : A →+* LaurentPolynomial A)).map
    (Scheme.ΓSpecIso (CommRingCat.of (LaurentPolynomial A))).inv.hom
  simpa using h

end GmPhiNat

open GmPhiNat in

/- English proof (translation)
Extract witnesses or component facts from the available result. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Rewrite the conclusion using the stated equalities.
-/
theorem gmPhi_nat (h6 : DivisorNaturality) (q : ℕ) [NeZero q] {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (hq : IsUnit (q : A))
    (i : ℤ) (a : Ht q (sp A) 0 (i - 1)) :
    pull _ (spMap (laurentMap f)) _ 1 (gmPhi q A i a) = gmPhi q B i (pull _ (spMap f) _ 0 a) := by
  obtain ⟨hcup, -, -, hkum⟩ := h6 q
  simp only [gmPhi, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  rw [pull_cast, hcup, ← pull_spMap_comp, ← pull_spMap_comp, laurentMap_C]
  congr 2
  rw [spMap, hkum _ _ (isUnit_gamma q A hq), laurentVar_map]

end GlobalTheory.EtC

end
