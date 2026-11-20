import Development.EtaleCohomology.EtaleSheaves.UnitExistence

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LeafUnitSecPf

def LeafTwGenIndep : Prop := ∀ (q : ℕ) [NeZero q] (U : Scheme.{0}) (ζ ξ : Prim q Γ(U, ⊤)), twGen 0 ζ = twGen 0 ξ

/- English proof (translation)
Unfold `twGen ofRings.sec`. Establish `h` using `congrArg (fun t => t.hom (Submodule.Quotient.mk (Finsupp.single ζ (1 : ULift.{1} (ZMod q))))) ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q i)).naturality g.op)`. Simplify using `only [ModuleCat.hom_comp] at h`. Use `h.symm.trans (congrArg (fun y => ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q i)).app (op V)).hom y) ?_)` and prove the remaining obligations. Conclude with `congrArg (Submodule.Quotient.mk (p := twRel q i Γ(V, ⊤))) (Finsupp.mapDomain_single (f := Prim.map (Scheme.Γ.map g.op).hom))`.
-/
theorem twGen_res {q : ℕ} (i : ℤ) {V U : Scheme.{0}} (g : V ⟶ U) (ζ : Prim q Γ(U, ⊤)) :
    Sec.res g (twGen i ζ) = twGen i (ζ.map (Scheme.Γ.map g.op).hom) := by
  unfold twGen ofRings.sec
  have h := congrArg (fun t => t.hom (Submodule.Quotient.mk (Finsupp.single ζ (1 : ULift.{1} (ZMod q)))))
    ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q i)).naturality g.op)
  simp only [ModuleCat.hom_comp] at h
  refine h.symm.trans (congrArg (fun y => ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q i)).app (op V)).hom y) ?_)
  exact congrArg (Submodule.Quotient.mk (p := twRel q i Γ(V, ⊤))) (Finsupp.mapDomain_single (f := Prim.map (Scheme.Γ.map g.op).hom))

/- English proof (translation)
Simplify using `only [Sec.res, op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]`.
-/
theorem res_comp {R : Type} [CommRing R] {F : Shv R} {W V U : Scheme.{0}} (h : W ⟶ V) (k : V ⟶ U) (x : Sec F U) :
    Sec.res h (Sec.res k x) = Sec.res (h ≫ k) x := by
  simp only [Sec.res, op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]

/- English proof (translation)
Use `show (F.obj.map (𝟙 U).op).hom x = x`. Rewrite using `[op_id, F.obj.map_id]`. Both sides reduce to the same expression.
-/
theorem res_id {R : Type} [CommRing R] {F : Shv R} {U : Scheme.{0}} (x : Sec F U) : Sec.res (𝟙 U) x = x := by
  show (F.obj.map (𝟙 U).op).hom x = x
  rw [op_id, F.obj.map_id]
  rfl

/- English proof (translation)
Establish `hF` using `(Presheaf.isSheaf_iff_isSheaf_forget Scheme.etaleTopology (tw q 0).obj (forget (ModuleCat.{1} (ULift.{1} (ZMod q))))).1 (tw q 0).property`. Rewrite `hF` using `[isSheaf_iff_isSheaf_of_type]`. Conclude with `hF S hS`.
-/
theorem tw_isSheafFor (q : ℕ) (U : Scheme.{0}) (S : Sieve U) (hS : S ∈ Scheme.etaleTopology U) :
    Presieve.IsSheafFor ((tw q 0).obj ⋙ forget (ModuleCat.{1} (ULift.{1} (ZMod q)))) S.arrows := by
  have hF := (Presheaf.isSheaf_iff_isSheaf_forget Scheme.etaleTopology (tw q 0).obj
    (forget (ModuleCat.{1} (ULift.{1} (ZMod q))))).1 (tw q 0).property
  rw [isSheaf_iff_isSheaf_of_type] at hF
  exact hF S hS

section Glue

def cov (hP : LateralTheory.E.LeafOneSpecPf.LeafPrimCover) (q : ℕ) [NeZero q] (U : Scheme.{0}) (hU : IsUnit (q : Γ(U, ⊤))) : Sieve U := Classical.choose (hP q U hU)

/- English proof (translation)
The claim follows from `(Classical.choose_spec (hP q U hU)).1`.
-/
theorem cov_mem (hP : LateralTheory.E.LeafOneSpecPf.LeafPrimCover) (q : ℕ) [NeZero q] (U : Scheme.{0}) (hU : IsUnit (q : Γ(U, ⊤))) : cov hP q U hU ∈ Scheme.etaleTopology U :=
  (Classical.choose_spec (hP q U hU)).1

/- English proof (translation)
The claim follows from `(Classical.choose_spec (hP q U hU)).2 V g hg`.
-/
theorem cov_prim (hP : LateralTheory.E.LeafOneSpecPf.LeafPrimCover) (q : ℕ) [NeZero q] (U : Scheme.{0}) (hU : IsUnit (q : Γ(U, ⊤))) (V : Scheme.{0}) (g : V ⟶ U) (hg : (cov hP q U hU).arrows g) :
    Nonempty (Prim q Γ(V, ⊤)) :=
  (Classical.choose_spec (hP q U hU)).2 V g hg

def fam (hP : LateralTheory.E.LeafOneSpecPf.LeafPrimCover) (q : ℕ) [NeZero q] (U : Scheme.{0}) (hU : IsUnit (q : Γ(U, ⊤))) :
    Presieve.FamilyOfElements ((tw q 0).obj ⋙ forget (ModuleCat.{1} (ULift.{1} (ZMod q)))) (cov hP q U hU).arrows :=
  fun V g hg => twGen 0 (Classical.choice (cov_prim hP q U hU V g hg))

/- English proof (translation)
Rewrite using `[Presieve.compatible_iff_sieveCompatible]`. Introduce `Y Z f g hf`. Express the relevant statement in the definitionally equal form `_ = Sec.res g (twGen 0 _)`. Rewrite using `[twGen_res]`. Conclude with `hI q Z _ _`.
-/
theorem fam_compat (hP : LateralTheory.E.LeafOneSpecPf.LeafPrimCover) (hI : LeafTwGenIndep) (q : ℕ) [NeZero q] (U : Scheme.{0}) (hU : IsUnit (q : Γ(U, ⊤))) : (fam hP q U hU).Compatible := by
  rw [Presieve.compatible_iff_sieveCompatible]
  intro Y Z f g hf
  change _ = Sec.res g (twGen 0 _)
  rw [twGen_res]
  exact hI q Z _ _

def one (hP : LateralTheory.E.LeafOneSpecPf.LeafPrimCover) (hI : LeafTwGenIndep) (q : ℕ) [NeZero q] (U : Scheme.{0}) (hU : IsUnit (q : Γ(U, ⊤))) : Sec (tw q 0) U :=
  (tw_isSheafFor q U _ (cov_mem hP q U hU)).amalgamate (fam hP q U hU) (fam_compat hP hI q U hU)

/- English proof (translation)
Use `LateralTheory.E.LeafOneSpecPf.sec_sep (ZMod q) (tw q 0) W ((cov hP q U hU).pullback k) (Scheme.etaleTopology.pullback_stable k (cov_mem hP q U hU)) _ _ fun V h hh => ?_` and prove the remaining obligations. Rewrite using `[res_comp, twGen_res]`. Establish `hv` using `(tw_isSheafFor q U _ (cov_mem hP q U hU)).valid_glue (fam_compat hP hI q U hU) (h ≫ k) hh`. Use `hv.trans ?_` and prove the remaining obligations. Conclude with `hI q V _ _`.
-/
theorem one_char (hP : LateralTheory.E.LeafOneSpecPf.LeafPrimCover) (hI : LeafTwGenIndep) (q : ℕ) [NeZero q] (U : Scheme.{0}) (hU : IsUnit (q : Γ(U, ⊤))) (W : Scheme.{0}) (k : W ⟶ U) (ζ : Prim q Γ(W, ⊤)) :
    Sec.res k (one hP hI q U hU) = twGen 0 ζ := by
  refine LateralTheory.E.LeafOneSpecPf.sec_sep (ZMod q) (tw q 0) W ((cov hP q U hU).pullback k)
    (Scheme.etaleTopology.pullback_stable k (cov_mem hP q U hU)) _ _ fun V h hh => ?_
  rw [res_comp, twGen_res]
  have hv := (tw_isSheafFor q U _ (cov_mem hP q U hU)).valid_glue (fam_compat hP hI q U hU) (h ≫ k) hh
  refine hv.trans ?_
  exact hI q V _ _

end Glue

/- English proof (translation)
Introduce `q _`. Use `⟨one hP hI q, fun V U g hU hV => ?_, fun U hU ζ => ?_⟩` and prove the remaining obligations. Use `LateralTheory.E.LeafOneSpecPf.sec_sep (ZMod q) (tw q 0) V (cov hP q V hV) (cov_mem hP q V hV) _ _ fun W h hh => ?_` and prove the remaining obligations. Take `⟨ζ⟩` from `cov_prim hP q V hV W h hh`. Rewrite using `[res_comp, one_char hP hI q U hU W _ ζ, one_char hP hI q V hV W h ζ]`.

Rewrite using `[← one_char hP hI q U hU U (𝟙 U) ζ, res_id]`.
-/
theorem LeafUnitSec_of (hP : LateralTheory.E.LeafOneSpecPf.LeafPrimCover) (hI : LeafTwGenIndep) :
    LateralTheory.E.LeafOneExistsPf.LeafUnitSec := by
  intro q _
  refine ⟨one hP hI q, fun V U g hU hV => ?_, fun U hU ζ => ?_⟩
  · refine LateralTheory.E.LeafOneSpecPf.sec_sep (ZMod q) (tw q 0) V (cov hP q V hV) (cov_mem hP q V hV) _ _ fun W h hh => ?_
    obtain ⟨ζ⟩ := cov_prim hP q V hV W h hh
    rw [res_comp, one_char hP hI q U hU W _ ζ, one_char hP hI q V hV W h ζ]
  · rw [← one_char hP hI q U hU U (𝟙 U) ζ, res_id]

end LateralTheory.E.LeafUnitSecPf
