import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.EtaleCohomology.TateTwists.EtaleSimplicialCochainExistsFromNaturalSections

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

def EtaleSimplicialCochainEvaluationAdditive : Prop := ∀ (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n : ℤ}, ∀ (α β : Cochain ((chains R).obj E) I n) p s h U x, ev (α + β) p s h U x = ev α p s h U x + ev β p s h U x ∧ ev (α - β) p s h U x = ev α p s h U x - ev β p s h U x ∧ ev (0 : Cochain ((chains R).obj E) I n) p s h U x = 0 ∧ ∀ c : ℤ, ev (c • α) p s h U x = c • ev α p s h U x

def EtaleSimplicialCochainEvaluationRestrictionNaturality : Prop := ∀ (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n : ℤ}, ∀ (α : Cochain ((chains R).obj E) I n) p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U), Sec.res g (ev α p s h U x) = ev α p s h V (x.res g)

def EtaleSimplicialCochainExtOfEvaluation : Prop := ∀ (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n : ℤ}, ∀ α β : Cochain ((chains R).obj E) I n, (∀ p s h U x, ev α p s h U x = ev β p s h U x) → α = β

def EtaleSimplicialCochainEvaluationPrecompSpaceMap : Prop := ∀ (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n : ℤ}, ∀ {E' : Spc} (f : E' ⟶ E) (α : Cochain ((chains R).obj E) I n) p s h U (x : Sx E' p U), ev ((Cochain.ofHom ((chains R).map f)).comp α (zero_add n)) p s h U x = ev α p s h U (x.map f)

def EtaleSimplicialCochainEvaluationPostcompComplexMap : Prop := ∀ (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n : ℤ}, ∀ {J : Cx R} (m : I ⟶ J) (α : Cochain ((chains R).obj E) I n) p s h U x, ev (α.comp (Cochain.ofHom m) (add_zero n)) p s h U x = Sec.map (m.f s) (ev α p s h U x)

end LateralTheory.EtaleFoundations

namespace LateralTheory.EtaleFoundations.BasicPf
variable {R : Type} [CommRing R]

/- English proof (translation)
A detailed English derivation is pending.
-/
lemma app_add {A B : Shv R} (φ ψ : A ⟶ B) (U : Scheme.{0}) (y : Sec A U) :
    ((φ + ψ).hom.app (op U)).hom y = (φ.hom.app (op U)).hom y + (ψ.hom.app (op U)).hom y := by
  first | rfl | simp | (change (((sheafToPresheaf _ _).map (φ + ψ)).app (op U)).hom y = _; rw [Functor.map_add]; rfl)

noncomputable def evH {E : Spc} {I : Cx R} {n : ℤ} (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
    Cochain ((chains R).obj E) I n →+ Sec (I.X s) U :=
  AddMonoidHom.mk' (fun α => ev α p s h U x) (by
    intro α β
    show ((((chainsXIso R E p).inv ≫ (α + β).v _ _ h).hom.app (op U))).hom _ = _
    rw [Cochain.add_v, Preadditive.comp_add, app_add]
    rfl)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Supply the required witnesses or components.
-/
theorem lin : EtaleSimplicialCochainEvaluationAdditive := by
  intro R _ E I n α β p s h U x
  exact ⟨map_add (evH p s h U x) α β, map_sub (evH p s h U x) α β, map_zero (evH p s h U x),
    fun c => map_zsmul (evH p s h U x) c α⟩

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem cx : EtaleSimplicialCochainEvaluationPostcompComplexMap := by
  intro R _ E I n J m α p s h U x
  show ((((chainsXIso R E p).inv ≫ (α.comp (Cochain.ofHom m) (add_zero n)).v _ _ h).hom.app (op U))).hom _ = _
  rw [Cochain.comp_zero_cochain_v, Cochain.ofHom_v]
  rfl

/- English proof (translation)
Replace the relevant objects with their definitions. Reduce the equality to equality of the corresponding arguments. A detailed English derivation is pending.
-/
lemma freeGen_res (P : PSh) {V U : Scheme.{0}} (g : V ⟶ U) (x : P.obj (op U)) :
    Sec.res g (freeGen R P U x) = freeGen R P V (P.map g.op x) := by
  unfold freeGen Sec.res
  erw [← ConcreteCategory.comp_apply, ← NatTrans.naturality, ConcreteCategory.comp_apply]
  congr 1
  exact ModuleCat.free_map_apply _ _

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem nat : EtaleSimplicialCochainEvaluationRestrictionNaturality := by
  intro R _ E I n α p s h V U g x
  show Sec.res g ((((chainsXIso R E p).inv ≫ α.v _ _ h).hom.app (op U)).hom (freeGen R _ U x)) =
    ((((chainsXIso R E p).inv ≫ α.v _ _ h).hom.app (op V)).hom (freeGen R _ V (x.res g)))
  rw [show x.res g = (E.obj (op (SimplexCategory.mk p))).map g.op x from rfl, ← freeGen_res]
  simp only [Sec.res]
  exact (congrArg (fun f => ModuleCat.Hom.hom f (freeGen R _ U x))
    (((chainsXIso R E p).inv ≫ α.v _ _ h).hom.naturality g.op)).symm

/- English proof (translation)
Replace the relevant objects with their definitions. Reduce the equality to equality of the corresponding arguments. A detailed English derivation is pending.
-/
lemma freeGen_map {P Q : PSh} (η : P ⟶ Q) (U : Scheme.{0}) (x : P.obj (op U)) :
    (((free R).map η).hom.app (op U)).hom (freeGen R P U x) = freeGen R Q U (η.app (op U) x) := by
  unfold freeGen
  erw [← ConcreteCategory.comp_apply, ← NatTrans.comp_app, ← toSheafify_naturality, NatTrans.comp_app, ConcreteCategory.comp_apply]
  congr 1
  exact ModuleCat.free_map_apply _ _

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify using the standard rewrite rules. Both sides reduce to the same expression. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem spc : LateralTheory.EtaleFoundations.EtaleSimplicialCochainEvaluationPrecompSpaceMap := by
  intro R _ E I n E' f α p s h U x
  have key : (chainsXIso R E' p).inv ≫ ((chains R).map f).f (-(p:ℤ)) =
      (free R).map (f.app (op (SimplexCategory.mk p))) ≫ (chainsXIso R E p).inv := by
    simp only [chains, chainsXIso, Functor.comp_map]
    erw [HomologicalComplex.extendMap_f _ _ (i := p) rfl, Iso.inv_hom_id_assoc]
    rfl
  show ((((chainsXIso R E' p).inv ≫ ((Cochain.ofHom ((chains R).map f)).comp α (zero_add n)).v _ _ h).hom.app (op U))).hom _ = ((((chainsXIso R E p).inv ≫ α.v _ _ h).hom.app (op U))).hom (freeGen R _ U (x.map f))
  rw [Cochain.zero_cochain_comp_v, Cochain.ofHom_v, ← Category.assoc, key, Category.assoc]
  show (((chainsXIso R E p).inv ≫ α.v _ _ h).hom.app (op U)).hom ((((free R).map (f.app (op (SimplexCategory.mk p)))).hom.app (op U)).hom (freeGen R _ U x)) = _
  rw [freeGen_map]
  rfl

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Separate the alternatives or extract the components of the hypothesis. Extract witnesses or component facts from the available result.

Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Reduce the claim to the hypotheses of an applicable result. Reduce the claim to the hypotheses of an applicable result. Apply function extensionality and compare values at an arbitrary argument.

Reduce the claim to the hypotheses of an applicable result. Assume the hypotheses and unpack their components. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Express the relevant assertion in an equivalent form by its definition.

Use linear arithmetic over natural numbers and integers. A detailed English derivation is pending.
-/
theorem ext : LateralTheory.EtaleFoundations.EtaleSimplicialCochainExtOfEvaluation := by
  intro R _ E I n α β hev
  apply Cochain.ext
  intro a b hab
  rcases le_or_gt a 0 with ha | ha
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, a = -(k:ℤ) := ⟨a.natAbs, by omega⟩
    rw [← cancel_epi (chainsXIso R E k).inv]
    apply (sheafToPresheaf _ _).map_injective
    apply sheafify_hom_ext _ _ _ (I.X b).cond
    apply NatTrans.ext
    funext U
    apply ModuleCat.free_hom_ext
    rintro ⟨y⟩
    exact hev k b hab U.unop y
  · apply (HomologicalComplex.isZero_extend_X _ _ a _).eq_of_src
    intro i hi
    change -(i:ℤ) = a at hi
    omega

end LateralTheory.EtaleFoundations.BasicPf

open LateralTheory.EtaleFoundations in
/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Supply the required witnesses or components.
-/
theorem LateralTheory.EtaleFoundations.etaleSimplicialCochain_evaluation_properties_of_components : EtaleSimplicialCochainEvaluationProperties := by
  intro R _ E I n
  exact ⟨BasicPf.lin R, BasicPf.nat R, BasicPf.ext R, BasicPf.spc R, BasicPf.cx R⟩
