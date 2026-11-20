import Development.EtaleCohomology.EtaleSheaves.CupProductRingLaws
import Development.EtaleCohomology.TateTwists.EtaleCochainEvaluationNaturalInRestriction

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafOneSpecPf

open LateralTheory.E.CupProductRingLaws

/- English proof (translation)
Unfold `res`. Unfold `InjectiveResolution.cochainComplex`. Apply `HomologicalComplex.isZero_extend_X` to reduce the goal to its premises. Introduce and unpack `i rfl`. Express the relevant statement in the definitionally equal form `((i : ℤ)) < 0 at hn`.

Use linear arithmetic over natural numbers and integers.
-/
theorem res_neg_zero (R : Type) [CommRing R] (F : Shv R) (n : ℤ) (hn : n < 0) : IsZero ((res R F).X n) := by
  unfold res
  unfold InjectiveResolution.cochainComplex
  apply HomologicalComplex.isZero_extend_X
  rintro i rfl
  change ((i : ℤ)) < 0 at hn
  omega
/- English proof (translation)
Unfold `chains`. Simplify using `only [Functor.comp_obj, ComplexShape.Embedding.extendFunctor_obj]`. Apply `HomologicalComplex.isZero_extend_X` to reduce the goal to its premises. Introduce and unpack `i rfl`. Express the relevant statement in the definitionally equal form `0 < -((i : ℤ)) at hn`.

Use linear arithmetic over natural numbers and integers.
-/
theorem chains_pos_zero (R : Type) [CommRing R] (E : Spc) (n : ℤ) (hn : 0 < n) : IsZero (((chains R).obj E).X n) := by
  unfold chains
  simp only [Functor.comp_obj, ComplexShape.Embedding.extendFunctor_obj]
  apply HomologicalComplex.isZero_extend_X
  rintro i rfl
  change 0 < -((i : ℤ)) at hn
  omega
/- English proof (translation)
Apply `Sheaf.hom_ext` to reduce the goal to its premises. Apply `sheafify_hom_ext _ _ _ G.property` to reduce the goal to its premises. Use extensionality with `U : 2`. Apply `ModuleCat.free_hom_ext` to reduce the goal to its premises. Introduce `x`.

Conclude with `h U.unop x.down`.
-/
theorem free_hom_ext (R : Type) [CommRing R] (P : PSh) (G : Shv R) (f g : (free R).obj P ⟶ G)
    (h : ∀ (U : Scheme.{0}) (x : P.obj (op U)), (f.hom.app (op U)).hom (freeGen R P U x) = (g.hom.app (op U)).hom (freeGen R P U x)) :
    f = g := by
  apply Sheaf.hom_ext
  apply sheafify_hom_ext _ _ _ G.property
  ext U : 2
  apply ModuleCat.free_hom_ext
  intro x
  exact h U.unop x.down
/- English proof (translation)
Apply `Cochain.ext` to reduce the goal to its premises. Introduce `p q hpq`. Break down `lt_trichotomy p 0 with hp | rfl | hp` into its components or cases. Conclude with `(res_neg_zero R F q (by omega)).eq_of_tgt _ _`. Establish `key : (chainsXIso R E 0).inv ≫ α.v (-((0 : ℕ) : ℤ)) 0 (by simp) = (chainsXIso R E 0).inv ≫ β.v (-((0 : ℕ) : ℤ)) 0 (by simp)` using `free_hom_ext R _ _ _ _ (fun U x => h U x)`.

Take `rfl : q = 0` from `by omega`. Simplify using `using key`. Conclude with `(chains_pos_zero R E p hp).eq_of_src _ _`.
-/
theorem cochain0_ext (R : Type) [CommRing R] (F : Shv R) (E : Spc)
    (α β : Cochain ((chains R).obj E) (res R F) 0)
    (h : ∀ (U : Scheme.{0}) (x : Sx E 0 U), ev α 0 0 (by simp) U x = ev β 0 0 (by simp) U x) : α = β := by
  apply Cochain.ext
  intro p q hpq
  rcases lt_trichotomy p 0 with hp | rfl | hp
  · exact (res_neg_zero R F q (by omega)).eq_of_tgt _ _
  · have key : (chainsXIso R E 0).inv ≫ α.v (-((0 : ℕ) : ℤ)) 0 (by simp) =
        (chainsXIso R E 0).inv ≫ β.v (-((0 : ℕ) : ℤ)) 0 (by simp) :=
      free_hom_ext R _ _ _ _ (fun U x => h U x)
    obtain rfl : q = 0 := by omega
    simpa using key
  · exact (chains_pos_zero R E p hp).eq_of_src _ _

def LeafCochain0Ext : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) (E : Spc)
  (α β : Cochain ((chains R).obj E) (res R F) 0),
  (∀ (U : Scheme.{0}) (x : Sx E 0 U), ev α 0 0 (by simp) U x = ev β 0 0 (by simp) U x) → α = β

/- English proof (translation)
Introduce `R _ F E α β h` and use `cochain0_ext R F E α β h`.
-/
theorem leafCochain0Ext_pf : LeafCochain0Ext := fun R _ F E α β h => cochain0_ext R F E α β h

def LeafOneExists : Prop := ∀ (q : ℕ) [NeZero q] (E : Spc), Inv q E → ∃ α, IsOneCocycle q E α

def LeafPrimCover : Prop := ∀ (q : ℕ) [NeZero q] (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) →
  ∃ S : Sieve U, S ∈ Scheme.etaleTopology U ∧ ∀ (V : Scheme.{0}) (g : V ⟶ U), S.arrows g → Nonempty (Prim q Γ(V, ⊤))

def LeafSecPrimLocal : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) (q : ℕ) [NeZero q] (U : Scheme.{0}) (a b : Sec F U),
  IsUnit (q : Γ(U, ⊤)) → (∀ (V : Scheme.{0}) (g : V ⟶ U), Nonempty (Prim q Γ(V, ⊤)) → Sec.res g a = Sec.res g b) → a = b

/- English proof (translation)
Establish `hF` using `(Presheaf.isSheaf_iff_isSheaf_forget Scheme.etaleTopology F.obj (forget (ModuleCat.{1} (ULift.{1} R)))).1 F.property`. Rewrite `hF` using `[isSheaf_iff_isSheaf_of_type]`. Conclude with `(hF S hS).isSeparatedFor.ext (fun V g hg => h V g hg)`.
-/
theorem sec_sep (R : Type) [CommRing R] (F : Shv R) (U : Scheme.{0}) (S : Sieve U) (hS : S ∈ Scheme.etaleTopology U)
    (a b : Sec F U) (h : ∀ (V : Scheme.{0}) (g : V ⟶ U), S.arrows g → Sec.res g a = Sec.res g b) : a = b := by
  have hF := (Presheaf.isSheaf_iff_isSheaf_forget Scheme.etaleTopology F.obj (forget (ModuleCat.{1} (ULift.{1} R)))).1 F.property
  rw [isSheaf_iff_isSheaf_of_type] at hF
  exact (hF S hS).isSeparatedFor.ext (fun V g hg => h V g hg)

/- English proof (translation)
Introduce `R _ F q _ U a b hq h`. Take `⟨S, hS, hSP⟩` from `hP q U hq`. Conclude with `sec_sep R F U S hS a b fun V g hg => h V g (hSP V g hg)`.
-/
theorem leafSecPrimLocal_of (hP : LeafPrimCover) : LeafSecPrimLocal := by
  intro R _ F q _ U a b hq h
  obtain ⟨S, hS, hSP⟩ := hP q U hq
  exact sec_sep R F U S hS a b fun V g hg => h V g (hSP V g hg)

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Apply `hB (ZMod q) (tw q 0) E α.1 β.1` to reduce the goal to its premises. Introduce `U x`. Use `hC (ZMod q) _ q U _ _ (hE U ⟨x⟩) ?_` and prove the remaining obligations. Introduce and unpack `V g ⟨ζ⟩`.

Rewrite using `[← LateralTheory.EtaleFoundations.ev_nat_pf α.1 0 0 (by simp) g x, ← LateralTheory.EtaleFoundations.ev_nat_pf β.1 0 0 (by simp) g x]`. Conclude with `(hα V _ ζ).trans (hβ V _ ζ).symm`.
-/
theorem one_cocycle_eq (hB : LeafCochain0Ext) (hC : LeafSecPrimLocal) (q : ℕ) [NeZero q] (E : Spc) (hE : Inv q E)
    (α β : Cocycle ((chains (ZMod q)).obj E) (res _ (tw q 0)) 0) (hα : IsOneCocycle q E α) (hβ : IsOneCocycle q E β) :
    α = β := by
  apply Subtype.ext
  apply hB (ZMod q) (tw q 0) E α.1 β.1
  intro U x
  refine hC (ZMod q) _ q U _ _ (hE U ⟨x⟩) ?_
  rintro V g ⟨ζ⟩
  rw [← LateralTheory.EtaleFoundations.ev_nat_pf α.1 0 0 (by simp) g x, ← LateralTheory.EtaleFoundations.ev_nat_pf β.1 0 0 (by simp) g x]
  exact (hα V _ ζ).trans (hβ V _ ζ).symm

/- English proof (translation)
Establish `hB` using `leafCochain0Ext_pf`. Establish `hC` using `leafSecPrimLocal_of hP`. Introduce `q _ E hE`. Use `⟨hA q E hE, fun α hα => ?_⟩` and prove the remaining obligations. Take `⟨α₀, h₀⟩` from `hA q E hE`.

Take `⟨α₁, h₁, hα₁⟩` from `pick_spec (P := fun c : Ht q E 0 0 => ∃ α : Cocycle ((chains (ZMod q)).obj E) (res _ (tw q 0)) 0, CohomologyClass.mk α = c ∧ ∀ (U : Scheme.{0}) (x : Sx E 0 U) (ζ : Prim q Γ(U, ⊤)), ev α.1 0 0 (by simp) U x = resGen 0 ζ) ⟨CohomologyClass.mk α₀, α₀, rfl, h₀⟩`. Express the relevant statement in the definitionally equal form `pick _ = _`. Rewrite using `[← h₁, one_cocycle_eq hB hC q E hE α₁ α hα₁ hα]`.
-/
theorem LeafOneSpec_of (hA : LeafOneExists) (hP : LeafPrimCover) : LeafOneSpec := by
  have hB := leafCochain0Ext_pf
  have hC := leafSecPrimLocal_of hP
  intro q _ E hE
  refine ⟨hA q E hE, fun α hα => ?_⟩
  obtain ⟨α₀, h₀⟩ := hA q E hE
  obtain ⟨α₁, h₁, hα₁⟩ := pick_spec (P := fun c : Ht q E 0 0 => ∃ α : Cocycle ((chains (ZMod q)).obj E) (res _ (tw q 0)) 0,
    CohomologyClass.mk α = c ∧ ∀ (U : Scheme.{0}) (x : Sx E 0 U) (ζ : Prim q Γ(U, ⊤)),
      ev α.1 0 0 (by simp) U x = resGen 0 ζ) ⟨CohomologyClass.mk α₀, α₀, rfl, h₀⟩
  change pick _ = _
  rw [← h₁, one_cocycle_eq hB hC q E hE α₁ α hα₁ hα]

end LateralTheory.E.LeafOneSpecPf
