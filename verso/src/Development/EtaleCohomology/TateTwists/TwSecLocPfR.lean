import Development.EtaleCohomology.TateTwists.TwLocPfR

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite TensorProduct GlobalTheory.EtC GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec

namespace LateralTheory.EtaleFoundations.TwSecLocPf

/- English proof (translation)
Take `⟨S, hS, hP⟩` from `h`. Conclude with `⟨S, hS, fun V g hg => hPQ V g (hP V g hg)⟩`.
-/
theorem loc_mono {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : Loc U P)
    (hPQ : ∀ V g, P V g → Q V g) : Loc U Q := by
  obtain ⟨S, hS, hP⟩ := h
  exact ⟨S, hS, fun V g hg => hPQ V g (hP V g hg)⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨⊤, Scheme.etaleTopology.top_mem U, fun _ _ _ => trivial⟩`.
-/
theorem loc_true (U : Scheme.{0}) : Loc U fun _ _ => True :=
  ⟨⊤, Scheme.etaleTopology.top_mem U, fun _ _ _ => trivial⟩

/- English proof (translation)
Take `⟨S, hS, hS'⟩` from `hP`. Take `⟨T, hT, hT'⟩` from `hQ`. Conclude with `⟨S ⊓ T, Scheme.etaleTopology.intersection_covering hS hT, fun V g hg => ⟨hS' V g hg.1, hT' V g hg.2⟩⟩`.
-/
theorem loc_and {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (hP : Loc U P) (hQ : Loc U Q) :
    Loc U fun V g => P V g ∧ Q V g := by
  obtain ⟨S, hS, hS'⟩ := hP
  obtain ⟨T, hT, hT'⟩ := hQ
  exact ⟨S ⊓ T, Scheme.etaleTopology.intersection_covering hS hT, fun V g hg => ⟨hS' V g hg.1, hT' V g hg.2⟩⟩

/- English proof (translation)
Take `⟨S, hS, hS'⟩` from `hP`. Use `choose T hT hT' using fun V (g : V ⟶ U) (hg : S.arrows g) => hQ V g (hS' V g hg)`. Use `⟨Sieve.bind S.arrows T, Scheme.etaleTopology.bind_covering hS hT, ?_⟩` and prove the remaining obligations. Introduce and unpack `W _ ⟨V, h, g, hg, hh, rfl⟩`. Conclude with `hT' V g hg W h hh`.
-/
theorem loc_bind {U : Scheme.{0}} {P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} {Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop}
    (hP : Loc U P) (hQ : ∀ V (g : V ⟶ U), P V g → Loc V fun W h => Q W (h ≫ g)) : Loc U Q := by
  obtain ⟨S, hS, hS'⟩ := hP
  choose T hT hT' using fun V (g : V ⟶ U) (hg : S.arrows g) => hQ V g (hS' V g hg)
  refine ⟨Sieve.bind S.arrows T, Scheme.etaleTopology.bind_covering hS hT, ?_⟩
  rintro W _ ⟨V, h, g, hg, hh, rfl⟩
  exact hT' V g hg W h hh

/- English proof (translation)
Establish `h` using `Presheaf.imageSieve_mem Scheme.etaleTopology (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ M)) y`. Use `⟨_, h, fun V g hg => ?_⟩` and prove the remaining obligations. Take `⟨x, hx⟩` from `hg`. Conclude with `⟨x, hx.symm⟩`.
-/
theorem loc_surj {R : Type} [CommRing R] (M : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} R)) (U : Scheme.{0})
    (y : Sec (ofRings R M) U) :
    Loc U fun V g => ∃ x : M.obj Γ(V, ⊤), Sec.res g y = ofRings.sec M V x := by
  have h := Presheaf.imageSieve_mem Scheme.etaleTopology (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ M)) y
  refine ⟨_, h, fun V g hg => ?_⟩
  obtain ⟨x, hx⟩ := hg
  exact ⟨x, hx.symm⟩

end LateralTheory.EtaleFoundations.TwSecLocPf

namespace LateralTheory.EtaleFoundations.TwSecLocPf

def ZarPow : Prop := ∀ (q : ℕ) [NeZero q] (V : Scheme.{0}) (ζ ξ : Prim q Γ(V, ⊤)),
  Loc V fun W h => ∃ a : (ZMod q)ˣ, (ξ.map h.appTop.hom).1 = (ζ.map h.appTop.hom).1 ^ (a : ZMod q).val

/- English proof (translation)
Establish `: r = ((r.down.val : ℕ) : ULift.{1} (ZMod q))`. Consider the cases of `r with`. Consider the case `up a`. Express the relevant statement in the definitionally equal form `ULift.up a = ULift.up ((a.val : ℕ) : ZMod q)`. Rewrite using `[ZMod.natCast_zmod_val]`.

Use `conv_lhs => rw [this]`. Conclude with `Nat.cast_smul_eq_nsmul _ _ _`.
-/
theorem ulift_smul_eq_nsmul {q : ℕ} [NeZero q] {M : Type*} [AddCommGroup M] [Module (ULift.{1} (ZMod q)) M]
    (r : ULift.{1} (ZMod q)) (m : M) : r • m = r.down.val • m := by
  have : r = ((r.down.val : ℕ) : ULift.{1} (ZMod q)) := by
    cases r with
    | up a =>
      change ULift.up a = ULift.up ((a.val : ℕ) : ZMod q)
      rw [ZMod.natCast_zmod_val]
  conv_lhs => rw [this]
  exact Nat.cast_smul_eq_nsmul _ _ _

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem twF_map_mk (q : ℕ) (i : ℤ) {A B : CommRingCat.{0}} (f : A ⟶ B) (x : Prim q A →₀ ULift.{1} (ZMod q)) :
    ((twF q i).map f).hom (Submodule.Quotient.mk x) =
      (Submodule.Quotient.mk (Finsupp.mapDomain (Prim.map f.hom) x) : (twF q i).obj B) := rfl

/- English proof (translation)
Establish `hrel : (Submodule.Quotient.mk (Finsupp.single ξ 1) : (twF q i).obj A) = Submodule.Quotient.mk (Finsupp.single ζ (ULift.up ((a ^ i : (ZMod q)ˣ) : ZMod q)))` using `(Submodule.Quotient.eq _).2 (Submodule.subset_span ⟨ζ, ξ, a, h, rfl⟩)`. Establish `e1 : Finsupp.single ξ b = b • Finsupp.single ξ (1 : ULift.{1} (ZMod q))`. Rewrite using `[Finsupp.smul_single, smul_eq_mul, mul_one]`. Establish `e2 : Finsupp.single ζ (ULift.up ((a ^ i : (ZMod q)ˣ) : ZMod q)) = (ULift.up ((a ^ i : (ZMod q)ˣ) : ZMod q)) • Finsupp.single ζ (1 : ULift.{1} (ZMod q))`. Rewrite using `[Finsupp.smul_single, smul_eq_mul, mul_one]`.

Rewrite using `[e1, Submodule.Quotient.mk_smul, hrel, e2, Submodule.Quotient.mk_smul, smul_smul]`. Conclude with `ulift_smul_eq_nsmul _ _`.
-/
theorem twF_single_pow (q : ℕ) [NeZero q] (i : ℤ) (A : CommRingCat.{0}) (ζ ξ : Prim q A) (a : (ZMod q)ˣ)
    (h : ξ.1 = ζ.1 ^ (a : ZMod q).val) (b : ULift.{1} (ZMod q)) :
    (Submodule.Quotient.mk (Finsupp.single ξ b) : (twF q i).obj A) =
      (b.down * ((a ^ i : (ZMod q)ˣ) : ZMod q)).val • (Submodule.Quotient.mk (Finsupp.single ζ 1) : (twF q i).obj A) := by
  have hrel : (Submodule.Quotient.mk (Finsupp.single ξ 1) : (twF q i).obj A) =
      Submodule.Quotient.mk (Finsupp.single ζ (ULift.up ((a ^ i : (ZMod q)ˣ) : ZMod q))) :=
    (Submodule.Quotient.eq _).2 (Submodule.subset_span ⟨ζ, ξ, a, h, rfl⟩)
  have e1 : Finsupp.single ξ b = b • Finsupp.single ξ (1 : ULift.{1} (ZMod q)) := by
    rw [Finsupp.smul_single, smul_eq_mul, mul_one]
  have e2 : Finsupp.single ζ (ULift.up ((a ^ i : (ZMod q)ˣ) : ZMod q)) =
      (ULift.up ((a ^ i : (ZMod q)ˣ) : ZMod q)) • Finsupp.single ζ (1 : ULift.{1} (ZMod q)) := by
    rw [Finsupp.smul_single, smul_eq_mul, mul_one]
  rw [e1, Submodule.Quotient.mk_smul, hrel, e2, Submodule.Quotient.mk_smul, smul_smul]
  exact ulift_smul_eq_nsmul _ _

/- English proof (translation)
Take `⟨f, rfl⟩` from `Submodule.Quotient.mk_surjective _ x`. Proceed by induction on `f using Finsupp.induction with`. Consider the case `zero`. Use `loc_mono (loc_true V) fun W h _ => ⟨0, ?_⟩` and prove the remaining obligations. Rewrite using `[zero_smul, Submodule.Quotient.mk_zero]`.

Conclude with `map_zero ((twF q i).map h.appTop).hom`. Consider the case `single_add ξ b g _ _ ih`. Use `loc_mono (loc_and (hZ q V ζ ξ) ih) fun W h ⟨⟨a, ha⟩, ⟨c, hc⟩⟩ => ⟨(b.down * ((a ^ i : (ZMod q)ˣ) : ZMod q)).val + c, ?_⟩` and prove the remaining obligations. Rewrite using `[Submodule.Quotient.mk_add]`. Use `(map_add ((twF q i).map h.appTop).hom _ _).trans ?_` and prove the remaining obligations.

Rewrite using `[hc, twF_map_mk, Finsupp.mapDomain_single, twF_single_pow q i _ _ _ a ha b, add_smul]`. Both sides reduce to the same expression.
-/
theorem twF_loc (hZ : ZarPow) (q : ℕ) [NeZero q] (i : ℤ) (V : Scheme.{0}) (ζ : Prim q Γ(V, ⊤))
    (x : (twF q i).obj Γ(V, ⊤)) :
    Loc V fun W h => ∃ c : ℕ, ((twF q i).map h.appTop).hom x =
      c • (Submodule.Quotient.mk (Finsupp.single (ζ.map h.appTop.hom) 1) : (twF q i).obj Γ(W, ⊤)) := by
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  induction f using Finsupp.induction with
  | zero =>
    refine loc_mono (loc_true V) fun W h _ => ⟨0, ?_⟩
    rw [zero_smul, Submodule.Quotient.mk_zero]
    exact map_zero ((twF q i).map h.appTop).hom
  | single_add ξ b g _ _ ih =>
    refine loc_mono (loc_and (hZ q V ζ ξ) ih) fun W h ⟨⟨a, ha⟩, ⟨c, hc⟩⟩ =>
      ⟨(b.down * ((a ^ i : (ZMod q)ˣ) : ZMod q)).val + c, ?_⟩
    rw [Submodule.Quotient.mk_add]
    refine (map_add ((twF q i).map h.appTop).hom _ _).trans ?_
    rw [hc, twF_map_mk, Finsupp.mapDomain_single,
      twF_single_pow q i _ _ _ a ha b, add_smul]
    rfl

/- English proof (translation)
Introduce `q _ i U ζ y`. Use `loc_bind (loc_surj (twF q i) U y) fun V g ⟨x, hx⟩ => ?_` and prove the remaining obligations. Use `loc_mono (twF_loc hZ q i V (ζ.map g.appTop.hom) x) fun W h ⟨c, hc⟩ => ⟨c, ?_⟩` and prove the remaining obligations. Establish `e : Sec.res (h ≫ g) y = Sec.res h (Sec.res g y)`. Simplify using `only [Sec.res, op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]`.

Establish `hp : (ζ.map g.appTop.hom).map h.appTop.hom = ζ.map (h ≫ g).appTop.hom`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `[Prim.map]`. Both sides reduce to the same expression. Rewrite using `[e]`.

Use `(congrArg (fun z => ((tw q i).obj.map h.op).hom z) hx).trans ?_` and prove the remaining obligations. Use `(LateralTheory.EtaleFoundations.TwLocPf.ofRings_sec_res (twF q i) h x).trans ?_` and prove the remaining obligations. Rewrite using `[hc, ← hp]`. Unfold `twGen ofRings.sec`. Conclude with `map_nsmul _ _ _`.
-/
theorem TwSecLoc_of (hZ : ZarPow) : LateralTheory.EtaleFoundations.TwLocPf.TwSecLoc := by
  intro q _ i U ζ y
  refine loc_bind (loc_surj (twF q i) U y) fun V g ⟨x, hx⟩ => ?_
  refine loc_mono (twF_loc hZ q i V (ζ.map g.appTop.hom) x) fun W h ⟨c, hc⟩ => ⟨c, ?_⟩
  have e : Sec.res (h ≫ g) y = Sec.res h (Sec.res g y) := by
    simp only [Sec.res, op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]
  have hp : (ζ.map g.appTop.hom).map h.appTop.hom = ζ.map (h ≫ g).appTop.hom := by
    apply Subtype.ext
    simp [Prim.map]
    rfl
  rw [e]
  refine (congrArg (fun z => ((tw q i).obj.map h.op).hom z) hx).trans ?_
  refine (LateralTheory.EtaleFoundations.TwLocPf.ofRings_sec_res (twF q i) h x).trans ?_
  rw [hc, ← hp]
  unfold twGen ofRings.sec
  exact map_nsmul _ _ _

end LateralTheory.EtaleFoundations.TwSecLocPf
