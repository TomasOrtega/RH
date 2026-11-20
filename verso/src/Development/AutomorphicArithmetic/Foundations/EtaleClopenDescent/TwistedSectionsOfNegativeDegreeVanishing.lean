import Mathlib
import Development.EtaleCohomology.EtaleSheaves.EtaleStandingHypothesesImplyRestrictionAxiom
import Development.AutomorphicArithmetic.CommutativeAlgebra.PrimitiveRootEqPowLocally
import Development.AutomorphicArithmetic.CommutativeAlgebra.TwistGeneratorSmulEqZeroImp
import Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsEtaleNbhdPrimitiveRootOfIsUnitNatCast

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace UpperTheory.Cb.LocalTwistForms

set_option backward.isDefEq.respectTransparency false in
/- English proof (translation)
Take `⟨𝒰, hle⟩` from `Scheme.mem_grothendieckTopology_iff.1 hS`. Take `⟨i, y, rfl⟩` from `𝒰.exists_eq x`. Conclude with `⟨𝒰.X i, 𝒰.f i, inferInstance, y, hle _ _ ⟨i⟩, rfl⟩`.
-/
private theorem covPt {X : Scheme.{0}} (S : Sieve X) (hS : S ∈ Scheme.etaleTopology X) (x : X) :
    ∃ (V : Scheme.{0}) (f : V ⟶ X) (_ : Etale f) (y : V), S f ∧ f y = x := by
  obtain ⟨𝒰, hle⟩ := Scheme.mem_grothendieckTopology_iff.1 hS
  obtain ⟨i, y, rfl⟩ := 𝒰.exists_eq x
  exact ⟨𝒰.X i, 𝒰.f i, inferInstance, y, hle _ _ ⟨i⟩, rfl⟩

/- English proof (translation)
Simplify using `[Sec.res, op_comp, Functor.map_comp]`.
-/
private theorem res_res {R : Type} [CommRing R] {F : Shv R} {V' V U : Scheme.{0}} (g : V' ⟶ V) (h : V ⟶ U) (x : Sec F U) :
    Sec.res g (Sec.res h x) = Sec.res (g ≫ h) x := by
  simp [Sec.res, op_comp, Functor.map_comp]

/- English proof (translation)
The claim follows from `map_smul _ _ _`.
-/
private theorem res_smul {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (c : ULift.{1} R) (x : Sec F U) :
    Sec.res g (c • x) = c • Sec.res g x := map_smul _ _ _

/- English proof (translation)
The claim follows from `(NatTrans.naturality_apply (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q i)) g.op x).symm`.
-/
private theorem sec_res (q : ℕ) (i : ℤ) {V U : Scheme.{0}} (g : V ⟶ U) (x : (twF q i).obj Γ(U, ⊤)) :
    (Sec.res g (ofRings.sec (twF q i) U x) : Sec (tw q i) V) = ofRings.sec (twF q i) V ((twF q i).map g.appTop x) :=
  (NatTrans.naturality_apply (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q i)) g.op x).symm

/- English proof (translation)
Express the relevant statement in the definitionally equal form `Submodule.Quotient.mk (Finsupp.mapDomain _ _) = _`. Rewrite using `[Finsupp.mapDomain_single]`.
-/
private theorem map_single (q : ℕ) (i : ℤ) {A B : CommRingCat.{0}} (φ : A ⟶ B) (ζ : Prim q A) (b : ULift.{1} (ZMod q)) :
    (twF q i).map φ (Submodule.Quotient.mk (Finsupp.single ζ b) : (twF q i).obj A) =
      (Submodule.Quotient.mk (Finsupp.single (Prim.map φ.hom ζ) b) : (twF q i).obj B) := by
  change Submodule.Quotient.mk (Finsupp.mapDomain _ _) = _
  rw [Finsupp.mapDomain_single]

/- English proof (translation)
Conclude with `(sec_res q i g _).trans (congrArg _ (map_single q i g.appTop ζ 1))`.
-/
private theorem twGen_res (q : ℕ) (i : ℤ) {V U : Scheme.{0}} (g : V ⟶ U) (ζ : Prim q Γ(U, ⊤)) :
    Sec.res g (twGen i ζ) = twGen i (Prim.map g.appTop.hom ζ) := by
  exact (sec_res q i g _).trans (congrArg _ (map_single q i g.appTop ζ 1))

/- English proof (translation)
Establish `e : X.presheaf.map (homOfLE h₂).op = X.presheaf.map (homOfLE h₁).op ≫ X.presheaf.map (homOfLE h₃).op`. Rewrite using `[← Functor.map_comp]`. Both sides reduce to the same expression. Rewrite using `[e, CommRingCat.comp_apply]`. Conclude with `hu.map _`.
-/
private theorem unit_res {X : Scheme.{0}} {A B C : X.Opens} (h₁ : B ≤ A) (h₂ : C ≤ A) (h₃ : C ≤ B) (f : Γ(X, A))
    (hu : IsUnit (X.presheaf.map (homOfLE h₁).op f)) : IsUnit (X.presheaf.map (homOfLE h₂).op f) := by
  have e : X.presheaf.map (homOfLE h₂).op = X.presheaf.map (homOfLE h₁).op ≫ X.presheaf.map (homOfLE h₃).op := by
    rw [← Functor.map_comp]; rfl
  rw [e, CommRingCat.comp_apply]
  exact hu.map _

/- English proof (translation)
Set `e : (twF q i).obj Γ(X, ⊤)` to `c • (Submodule.Quotient.mk (Finsupp.single ζ 1) : (twF q i).obj Γ(X, ⊤))`. Establish `h0 : ofRings.sec (twF q i) X e = ofRings.sec (twF q i) X 0`. Use `Eq.trans ?_ (h.trans (map_zero _).symm)` and prove the remaining obligations. Conclude with `map_smul _ _ _`. Establish `hmem` using `Presheaf.equalizerSieve_mem Scheme.etaleTopology (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q i)) (X := op X) e 0 h0`.

Take `⟨V, f, -, y, hf, -⟩` from `covPt _ hmem (Classical.arbitrary X)`. Establish `hf' : (twF q i).map f.appTop e = 0` using `Eq.trans hf (map_zero ((twF q i).map f.appTop).hom)`. Establish `e1 : (twF q i).map f.appTop e = c • (twF q i).map f.appTop (Submodule.Quotient.mk (Finsupp.single ζ 1) : (twF q i).obj Γ(X, ⊤))` using `map_smul ((twF q i).map f.appTop).hom c _`. Establish `: Nontrivial Γ(V, ⊤)` using `(V.presheaf.germ ⊤ y trivial).hom.domain_nontrivial`. Rewrite `hf'` using `[e1, map_single]`.

Conclude with `UpperTheory.twist_generator_smul_eq_zero_imp q i Γ(V, ⊤) _ c hf'`.
-/
private theorem sheafDetect (q : ℕ) [NeZero q] (i : ℤ) (X : Scheme.{0}) [Nonempty X] (ζ : Prim q Γ(X, ⊤))
    (c : ULift.{1} (ZMod q)) (h : c • twGen i ζ = 0) : c = 0 := by
  let e : (twF q i).obj Γ(X, ⊤) := c • (Submodule.Quotient.mk (Finsupp.single ζ 1) : (twF q i).obj Γ(X, ⊤))
  have h0 : ofRings.sec (twF q i) X e = ofRings.sec (twF q i) X 0 := by
    refine Eq.trans ?_ (h.trans (map_zero _).symm)
    exact map_smul _ _ _
  have hmem := Presheaf.equalizerSieve_mem Scheme.etaleTopology
    (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q i)) (X := op X) e 0 h0
  obtain ⟨V, f, -, y, hf, -⟩ := covPt _ hmem (Classical.arbitrary X)
  have hf' : (twF q i).map f.appTop e = 0 := Eq.trans hf (map_zero ((twF q i).map f.appTop).hom)
  have e1 : (twF q i).map f.appTop e =
      c • (twF q i).map f.appTop (Submodule.Quotient.mk (Finsupp.single ζ 1) : (twF q i).obj Γ(X, ⊤)) :=
    map_smul ((twF q i).map f.appTop).hom c _
  have : Nontrivial Γ(V, ⊤) := (V.presheaf.germ ⊤ y trivial).hom.domain_nontrivial
  rw [e1, map_single] at hf'
  exact UpperTheory.twist_generator_smul_eq_zero_imp q i Γ(V, ⊤) _ c hf'

/- English proof (translation)
Take `⟨x, rfl⟩` from `Submodule.Quotient.mk_surjective _ t`. Proceed by induction on `x using Finsupp.induction_linear with`. Consider the case `zero`. Use `⟨1, fun h => Ideal.IsPrime.ne_top ‹_› ((Ideal.eq_top_iff_one _).2 h), fun B φ _ => ⟨0, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[zero_smul]`.

Conclude with `map_zero ((twF q i).map φ).hom`. Consider the case `add x y hx hy`. Take `⟨f, hf, H⟩` from `hx`. Take `⟨g, hg, H'⟩` from `hy`. Use `⟨f * g, fun h => (Ideal.IsPrime.mem_or_mem ‹_› h).elim hf hg, fun B φ hu => ?_⟩` and prove the remaining obligations.

Rewrite `hu` using `[map_mul]`. Take `⟨c, hc⟩` from `H B φ (isUnit_of_mul_isUnit_left hu)`. Take `⟨d, hd⟩` from `H' B φ (isUnit_of_mul_isUnit_right hu)`. Use `⟨c + d, ?_⟩` and prove the remaining obligations. Rewrite using `[add_smul, ← hc, ← hd]`.

Conclude with `map_add ((twF q i).map φ).hom (Submodule.Quotient.mk x : (twF q i).obj A) (Submodule.Quotient.mk y : (twF q i).obj A)`. Consider the case `single ξ b`. Take `⟨f, a, hf, H⟩` from `UpperTheory.primitive_root_eq_pow_locally q A ξ ζ p`. Use `⟨f, hf, fun B φ hu => ⟨b * ULift.up ((a ^ i : (ZMod q)ˣ) : ZMod q), ?_⟩⟩` and prove the remaining obligations. Rewrite using `[map_single]`.

Establish `hmem : Finsupp.single (Prim.map φ.hom ξ) 1 - Finsupp.single (Prim.map φ.hom ζ) (ULift.up ((a ^ i : (ZMod q)ˣ) : ZMod q)) ∈ twRel q i B` using `Submodule.subset_span ⟨Prim.map φ.hom ζ, Prim.map φ.hom ξ, a, H B φ.hom hu, rfl⟩`. Establish `e1 : (Submodule.Quotient.mk (Finsupp.single (Prim.map φ.hom ξ) 1) : (twF q i).obj B) = Submodule.Quotient.mk (Finsupp.single (Prim.map φ.hom ζ) (ULift.up ((a ^ i : (ZMod q)ˣ) : ZMod q)))` using `(Submodule.Quotient.eq _).2 hmem`. Establish `e2 : ∀ (η : Prim q B) (r : ULift.{1} (ZMod q)), (Submodule.Quotient.mk (Finsupp.single η r) : (twF q i).obj B) = r • (Submodule.Quotient.mk (Finsupp.single η 1) : (twF q i).obj B)`. Introduce `η r`. Use `Eq.trans ?_ (Submodule.Quotient.mk_smul _ _ _)` and prove the remaining obligations.

Rewrite using `[Finsupp.smul_single, smul_eq_mul, mul_one]`. Rewrite using `[e2 _ b, e1, e2 _ (ULift.up _), smul_smul]`.
-/
private theorem twLocal (q : ℕ) [NeZero q] (i : ℤ) (A : CommRingCat.{0}) (ζ : Prim q A) (t : (twF q i).obj A)
    (p : Ideal A) [p.IsPrime] :
    ∃ f : A, f ∉ p ∧ ∀ (B : CommRingCat.{0}) (φ : A ⟶ B), IsUnit (φ f) → ∃ c : ULift.{1} (ZMod q),
      (twF q i).map φ t = c • (Submodule.Quotient.mk (Finsupp.single (Prim.map φ.hom ζ) 1) : (twF q i).obj B) := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ t
  induction x using Finsupp.induction_linear with
  | zero =>
    refine ⟨1, fun h => Ideal.IsPrime.ne_top ‹_› ((Ideal.eq_top_iff_one _).2 h), fun B φ _ => ⟨0, ?_⟩⟩
    rw [zero_smul]
    exact map_zero ((twF q i).map φ).hom
  | add x y hx hy =>
    obtain ⟨f, hf, H⟩ := hx
    obtain ⟨g, hg, H'⟩ := hy
    refine ⟨f * g, fun h => (Ideal.IsPrime.mem_or_mem ‹_› h).elim hf hg, fun B φ hu => ?_⟩
    rw [map_mul] at hu
    obtain ⟨c, hc⟩ := H B φ (isUnit_of_mul_isUnit_left hu)
    obtain ⟨d, hd⟩ := H' B φ (isUnit_of_mul_isUnit_right hu)
    refine ⟨c + d, ?_⟩
    rw [add_smul, ← hc, ← hd]
    exact map_add ((twF q i).map φ).hom (Submodule.Quotient.mk x : (twF q i).obj A) (Submodule.Quotient.mk y : (twF q i).obj A)
  | single ξ b =>
    obtain ⟨f, a, hf, H⟩ := UpperTheory.primitive_root_eq_pow_locally q A ξ ζ p
    refine ⟨f, hf, fun B φ hu => ⟨b * ULift.up ((a ^ i : (ZMod q)ˣ) : ZMod q), ?_⟩⟩
    rw [map_single]
    have hmem : Finsupp.single (Prim.map φ.hom ξ) 1 - Finsupp.single (Prim.map φ.hom ζ) (ULift.up ((a ^ i : (ZMod q)ˣ) : ZMod q))
        ∈ twRel q i B :=
      Submodule.subset_span ⟨Prim.map φ.hom ζ, Prim.map φ.hom ξ, a, H B φ.hom hu, rfl⟩
    have e1 : (Submodule.Quotient.mk (Finsupp.single (Prim.map φ.hom ξ) 1) : (twF q i).obj B) =
        Submodule.Quotient.mk (Finsupp.single (Prim.map φ.hom ζ) (ULift.up ((a ^ i : (ZMod q)ˣ) : ZMod q))) :=
      (Submodule.Quotient.eq _).2 hmem
    have e2 : ∀ (η : Prim q B) (r : ULift.{1} (ZMod q)), (Submodule.Quotient.mk (Finsupp.single η r) : (twF q i).obj B) =
        r • (Submodule.Quotient.mk (Finsupp.single η 1) : (twF q i).obj B) := by
      intro η r
      refine Eq.trans ?_ (Submodule.Quotient.mk_smul _ _ _)
      rw [Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [e2 _ b, e1, e2 _ (ULift.up _), smul_smul]

/- English proof (translation)
Take `⟨V₁, f₁, h₁, y₁, ζ₁, rfl⟩` from `UpperTheory.exists_etale_nbhd_primitiveRoot_of_isUnit_natCast q X hX x`. Establish `hmem` using `Presheaf.imageSieve_mem Scheme.etaleTopology (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q i)) (U := op V₁) (Sec.res f₁ s)`. Take `⟨V₂, f₂, h₂, y₂, ⟨t, ht⟩, rfl⟩` from `covPt _ hmem y₁`. Set `ρ : Γ(V₂, ⊤) ⟶ V₂.residueField y₂` to `V₂.presheaf.germ ⊤ y₂ trivial ≫ V₂.residue y₂`. Establish `hp : (RingHom.ker ρ.hom).IsPrime` using `RingHom.ker_isPrime _`.

Take `⟨f, hfp, H⟩` from `twLocal q i Γ(V₂, ⊤) (Prim.map f₂.appTop.hom ζ₁) t (RingHom.ker ρ.hom)`. Establish `hy : y₂ ∈ V₂.basicOpen f`. Rewrite using `[Scheme.mem_basicOpen_top]`. Establish `h1 : (V₂.residue y₂).hom ((V₂.presheaf.germ ⊤ y₂ trivial).hom f) ≠ 0` using `fun h => hfp (RingHom.mem_ker.2 h)`. Conclude with `(IsLocalRing.residue_ne_zero_iff_isUnit _).1 h1`.

Establish `hu : IsUnit ((V₂.basicOpen f).ι.appTop f)`. Establish `h0` using `V₂.toRingedSpace.isUnit_res_basicOpen f`. Rewrite using `[Scheme.Opens.ι_appTop]`. Conclude with `unit_res _ _ (le_of_eq (by simp; rfl)) f h0`. Take `⟨c, hc⟩` from `H _ (V₂.basicOpen f).ι.appTop hu`.

Use `⟨V₂.basicOpen f, (V₂.basicOpen f).ι ≫ f₂ ≫ f₁, inferInstance, ⟨y₂, hy⟩, Prim.map (V₂.basicOpen f).ι.appTop.hom (Prim.map f₂.appTop.hom ζ₁), c, by simp; rfl, ?_⟩` and prove the remaining obligations. Rewrite using `[← res_res, ← res_res]`. Establish `ht' : Sec.res f₂ (Sec.res f₁ s) = ofRings.sec (twF q i) V₂ t` using `ht.symm`. Use `(congrArg (Sec.res (V₂.basicOpen f).ι) ht').trans ((sec_res q i _ t).trans ((congrArg (ofRings.sec (twF q i) _) hc).trans ?_))` and prove the remaining obligations. Conclude with `map_smul _ _ _`.
-/
private theorem formP (q : ℕ) [NeZero q] (i : ℤ) (X : Scheme.{0}) (hX : IsUnit ((q : ℕ) : Γ(X, ⊤)))
    (s : Sec (tw q i) X) (x : X) :
    ∃ (V : Scheme.{0}) (f : V ⟶ X) (_ : Etale f) (y : V) (ζ : Prim q Γ(V, ⊤)) (c : ULift.{1} (ZMod q)),
      f y = x ∧ Sec.res f s = c • twGen i ζ := by
  obtain ⟨V₁, f₁, h₁, y₁, ζ₁, rfl⟩ := UpperTheory.exists_etale_nbhd_primitiveRoot_of_isUnit_natCast q X hX x
  have hmem := Presheaf.imageSieve_mem Scheme.etaleTopology
    (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q i)) (U := op V₁) (Sec.res f₁ s)
  obtain ⟨V₂, f₂, h₂, y₂, ⟨t, ht⟩, rfl⟩ := covPt _ hmem y₁
  let ρ : Γ(V₂, ⊤) ⟶ V₂.residueField y₂ := V₂.presheaf.germ ⊤ y₂ trivial ≫ V₂.residue y₂
  have hp : (RingHom.ker ρ.hom).IsPrime := RingHom.ker_isPrime _
  obtain ⟨f, hfp, H⟩ := twLocal q i Γ(V₂, ⊤) (Prim.map f₂.appTop.hom ζ₁) t (RingHom.ker ρ.hom)
  have hy : y₂ ∈ V₂.basicOpen f := by
    rw [Scheme.mem_basicOpen_top]
    have h1 : (V₂.residue y₂).hom ((V₂.presheaf.germ ⊤ y₂ trivial).hom f) ≠ 0 := fun h => hfp (RingHom.mem_ker.2 h)
    exact (IsLocalRing.residue_ne_zero_iff_isUnit _).1 h1
  have hu : IsUnit ((V₂.basicOpen f).ι.appTop f) := by
    have h0 := V₂.toRingedSpace.isUnit_res_basicOpen f
    rw [Scheme.Opens.ι_appTop]
    exact unit_res _ _ (le_of_eq (by simp; rfl)) f h0
  obtain ⟨c, hc⟩ := H _ (V₂.basicOpen f).ι.appTop hu
  refine ⟨V₂.basicOpen f, (V₂.basicOpen f).ι ≫ f₂ ≫ f₁, inferInstance, ⟨y₂, hy⟩,
    Prim.map (V₂.basicOpen f).ι.appTop.hom (Prim.map f₂.appTop.hom ζ₁), c, by simp; rfl, ?_⟩
  rw [← res_res, ← res_res]
  have ht' : Sec.res f₂ (Sec.res f₁ s) = ofRings.sec (twF q i) V₂ t := ht.symm
  refine (congrArg (Sec.res (V₂.basicOpen f).ι) ht').trans ((sec_res q i _ t).trans
    ((congrArg (ofRings.sec (twF q i) _) hc).trans ?_))
  exact map_smul _ _ _

end UpperTheory.Cb.LocalTwistForms

open LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafInj0WPf LateralTheory.E.LeafDegCut UpperTheory.Cb.LocalTwistForms in
/- English proof (translation)
Introduce `_ q _ k _ hq i B W s₀ ι _ U s hs x hx`. Establish `hX : IsUnit ((q : ℕ) : Γ(U.left, ⊤))`. Establish `h` using `hq.map ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ (U.hom ≫ s₀).appTop).hom`. Simplify using `using h`. Take `⟨V, f, hf, y, ζ, c, hy, hsV⟩` from `formP q i U.left hX s x`.

Set `U' : B.Etale` to `MorphismProperty.Over.mk ⊤ (f ≫ U.hom) (inferInstanceAs (Etale (f ≫ U.hom)))`. Set `a : U' ⟶ U` to `MorphismProperty.Over.homMk f rfl`. Use `⟨U', a, y, hy, ?_⟩` and prove the remaining obligations. Take `⟨w, hw⟩` from `hx`. Establish `hne : Nonempty ↥(pullback U'.hom ι)`.

Establish `e : U'.hom y = ι w`. Rewrite using `[hw, ← hy]`. Both sides reduce to the same expression. Take `⟨z, -, -⟩` from `Scheme.Pullback.exists_preimage_pullback y w e`. Conclude with `⟨z⟩`.

Establish `hc : c = 0`. Establish `e : prB ι U' ≫ f = resBW ι a ≫ prB ι U` using `(pullback.lift_fst _ _ _).symm`. Establish `h1 : Sec.res (prB ι U') (Sec.res f s) = 0`. Establish `h0` using `congrArg (Sec.res (resBW ι a)) hs`. Rewrite `h0` using `[res_res, ← e]`.

Conclude with `(res_res _ _ _).trans (h0.trans (map_zero _))`. Establish `key : ∀ pr : pullback U'.hom ι ⟶ V, Sec.res pr (Sec.res f s) = 0 → c = 0` using `fun pr h => by`. Rewrite `h` using `[hsV, res_smul, twGen_res]`. Conclude with `sheafDetect q i _ _ c h`. Conclude with `key (prB ι U') h1`.

Express the relevant statement in the definitionally equal form `Sec.res f s = 0`. Rewrite using `[hsV, hc, zero_smul]`.
-/
theorem UpperTheory.Cb.twistedSections_of_negativeDegreeVanishing :
    LateralTheory.E.LeafDegCut.LeafNeg → LateralTheory.E.LeafInj0WPf.LeafSecTw := by
  intro _ q _ k _ hq i B W s₀ ι _ U s hs x hx
  have hX : IsUnit ((q : ℕ) : Γ(U.left, ⊤)) := by
    have h := hq.map ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ (U.hom ≫ s₀).appTop).hom
    simpa using h
  obtain ⟨V, f, hf, y, ζ, c, hy, hsV⟩ := formP q i U.left hX s x
  let U' : B.Etale := MorphismProperty.Over.mk ⊤ (f ≫ U.hom) (inferInstanceAs (Etale (f ≫ U.hom)))
  let a : U' ⟶ U := MorphismProperty.Over.homMk f rfl
  refine ⟨U', a, y, hy, ?_⟩
  obtain ⟨w, hw⟩ := hx
  have hne : Nonempty ↥(pullback U'.hom ι) := by
    have e : U'.hom y = ι w := by
      rw [hw, ← hy]
      rfl
    obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback y w e
    exact ⟨z⟩
  have hc : c = 0 := by
    have e : prB ι U' ≫ f = resBW ι a ≫ prB ι U := (pullback.lift_fst _ _ _).symm
    have h1 : Sec.res (prB ι U') (Sec.res f s) = 0 := by
      have h0 := congrArg (Sec.res (resBW ι a)) hs
      rw [res_res, ← e] at h0
      exact (res_res _ _ _).trans (h0.trans (map_zero _))
    have key : ∀ pr : pullback U'.hom ι ⟶ V, Sec.res pr (Sec.res f s) = 0 → c = 0 := fun pr h => by
      rw [hsV, res_smul, twGen_res] at h
      exact sheafDetect q i _ _ c h
    exact key (prB ι U') h1
  change Sec.res f s = 0
  rw [hsV, hc, zero_smul]
