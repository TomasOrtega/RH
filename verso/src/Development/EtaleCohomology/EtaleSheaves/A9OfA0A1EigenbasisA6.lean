import Development.EtaleCohomology.EtaleSheaves.LeafVanBPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LeafClosedSH0Pf
open LateralTheory.E.E4 LateralTheory.E.LeafVanBPf

def LeafSHSieve : Prop := ∀ (X : Scheme.{0}) [IsAffine X], SH Γ(X, ⊤) →
  ∀ S ∈ Scheme.etaleTopology X, S (𝟙 X)

def LeafSHQuot : Prop := ∀ (A : Type) [CommRing A], SH A → ∀ {W' : Scheme.{0}} (ι' : W' ⟶ Sp A) [IsClosedImmersion ι'],
  IsEmpty W' ∨ SH Γ(W', ⊤)

def LeafEmptySec : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) (X : Scheme.{0}), IsEmpty X → Subsingleton (Sec F X)

def LeafPrimLift : Prop := ∀ (q : ℕ) (B C : Type) [CommRing B] [CommRing C] [HenselianLocalRing B] [Nontrivial C]
  (f : B →+* C), Function.Surjective f → Function.Surjective (Prim.map (q := q) f)

/- English proof (translation)
The claim follows from `hy.2.2.2.2.2.2.2.1`.
-/
theorem a9_of_a0_a1_eigenbasis_a6 (hy : Hyps) : A9 := hy.2.2.2.2.2.2.2.1

/- English proof (translation)
Introduce `y`. Take `⟨x, rfl⟩` from `Submodule.Quotient.mk_surjective _ y`. Take `⟨x', rfl⟩` from `Finsupp.mapDomain_surjective (hP q B C f.hom hf) x`. Conclude with `⟨Submodule.Quotient.mk x', rfl⟩`.
-/
theorem twF_surj (hP : LeafPrimLift) (q : ℕ) (i : ℤ) {B C : CommRingCat.{0}} [HenselianLocalRing B] [Nontrivial C]
    (f : B ⟶ C) (hf : Function.Surjective f) : Function.Surjective ((twF q i).map f) := by
  intro y
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  obtain ⟨x', rfl⟩ := Finsupp.mapDomain_surjective (hP q B C f.hom hf) x
  exact ⟨Submodule.Quotient.mk x', rfl⟩

/- English proof (translation)
Break down `hQ A hA ι' with hW | hW` into its components or cases. Use `hE (ZMod q) (tw q i) W' hW` as an intermediate fact. Conclude with `fun y => ⟨0, Subsingleton.elim _ _⟩`. Take `⟨hAff, hsurj⟩` from `IsClosedImmersion.isAffine_surjective_of_isAffine ι'`. Establish `hW0` using `hW`.

Take `⟨_, _⟩` from `hW`. Take `⟨_, _⟩` from `hA`. Introduce `s`. Set `P : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} (ZMod q))` to `Scheme.Γ ⋙ twF q i`. Establish `hmem` using `Presheaf.imageSieve_mem Scheme.etaleTopology (toSheafify Scheme.etaleTopology P) s`.

Take `⟨t, ht⟩` from `hS W' hW0 _ hmem`. Set `g : CommRingCat.of A ⟶ Γ(W', ⊤)` to `(Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ ι'.appTop`. Establish `hg : Function.Surjective g` using `hsurj.comp (Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv.symm.surjective`. Take `⟨t', rfl⟩` from `twF_surj hP q i g hg t`. Use `⟨(toSheafify Scheme.etaleTopology P).app (op (Sp A)) ((twF q i).map (Scheme.ΓSpecIso (CommRingCat.of A)).inv t'), ?_⟩` and prove the remaining obligations.

Establish `e1` using `NatTrans.naturality_apply (toSheafify Scheme.etaleTopology P) ι'.op ((twF q i).map (Scheme.ΓSpecIso (CommRingCat.of A)).inv t')`. Establish `e2 : P.map ι'.op ((twF q i).map (Scheme.ΓSpecIso (CommRingCat.of A)).inv t') = (twF q i).map g t'`. Simplify using `only [P, g, Functor.comp_map, Functor.map_comp, ConcreteCategory.comp_apply]`. Both sides reduce to the same expression. Rewrite `e1` using `[e2, ht]`.

Simplify using `only [op_id] at e1`. Use `Eq.trans ?_ (e1.symm.trans ?_)` and prove the remaining obligations. Both sides reduce to the same expression. Simplify using the standard rewrite rules. Both sides reduce to the same expression.
-/
theorem secSurj (hS : LeafSHSieve) (hQ : LeafSHQuot) (hE : LeafEmptySec) (hP : LeafPrimLift) (q : ℕ) (i : ℤ)
    (A : Type) [CommRing A] (hA : SH A) {W' : Scheme.{0}} (ι' : W' ⟶ Sp A) [IsClosedImmersion ι'] :
    Function.Surjective (Sec.res ι' : Sec (tw q i) (Sp A) → Sec (tw q i) W') := by
  rcases hQ A hA ι' with hW | hW
  · have := hE (ZMod q) (tw q i) W' hW
    exact fun y => ⟨0, Subsingleton.elim _ _⟩
  obtain ⟨hAff, hsurj⟩ := IsClosedImmersion.isAffine_surjective_of_isAffine ι'
  have hW0 := hW
  obtain ⟨_, _⟩ := hW
  obtain ⟨_, _⟩ := hA
  intro s
  let P : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} (ZMod q)) := Scheme.Γ ⋙ twF q i
  have hmem := Presheaf.imageSieve_mem Scheme.etaleTopology (toSheafify Scheme.etaleTopology P) s
  obtain ⟨t, ht⟩ := hS W' hW0 _ hmem
  let g : CommRingCat.of A ⟶ Γ(W', ⊤) := (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ ι'.appTop
  have hg : Function.Surjective g := hsurj.comp (Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv.symm.surjective
  obtain ⟨t', rfl⟩ := twF_surj hP q i g hg t
  refine ⟨(toSheafify Scheme.etaleTopology P).app (op (Sp A)) ((twF q i).map (Scheme.ΓSpecIso (CommRingCat.of A)).inv t'), ?_⟩
  have e1 := NatTrans.naturality_apply (toSheafify Scheme.etaleTopology P) ι'.op
    ((twF q i).map (Scheme.ΓSpecIso (CommRingCat.of A)).inv t')
  have e2 : P.map ι'.op ((twF q i).map (Scheme.ΓSpecIso (CommRingCat.of A)).inv t') = (twF q i).map g t' := by
    simp only [P, g, Functor.comp_map, Functor.map_comp, ConcreteCategory.comp_apply]
    rfl
  rw [e2, ht] at e1
  simp only [op_id] at e1
  refine Eq.trans ?_ (e1.symm.trans ?_)
  · rfl
  · simp
    rfl

/- English proof (translation)
Introduce `hy q _ i A _ _ hA hq W' ι' _`. Take `⟨-, e, he, -⟩` from `a9_of_a0_a1_eigenbasis_a6 hy (ZMod q) (tw q i)`. Introduce `y`. Take `⟨s, rfl⟩` from `(e W').surjective y`. Take `⟨t, rfl⟩` from `secSurj hS hQ hE hP q i A hA ι' s`.

Conclude with `⟨e _ t, he _ t⟩`.
-/
theorem LeafClosedSH0_of (hS : LeafSHSieve) (hQ : LeafSHQuot) (hE : LeafEmptySec) (hP : LeafPrimLift) :
    LeafClosedSH0 := by
  intro hy q _ i A _ _ hA hq W' ι' _
  obtain ⟨-, e, he, -⟩ := a9_of_a0_a1_eigenbasis_a6 hy (ZMod q) (tw q i)
  intro y
  obtain ⟨s, rfl⟩ := (e W').surjective y
  obtain ⟨t, rfl⟩ := secSurj hS hQ hE hP q i A hA ι' s
  exact ⟨e _ t, he _ t⟩

end LateralTheory.E.LeafClosedSH0Pf
