import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.EtaleCohomology.TateTwists.EtaleCochainExistsOfNaturalEvaluation

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.EvMkPf

variable (R : Type) [CommRing R]

noncomputable def psiOf (P : PSh) (F : Shv R) (a : ∀ U : Scheme.{0}, P.obj (op U) → Sec F U)
    (ha : ∀ (V U : Scheme.{0}) (g : V ⟶ U) x, Sec.res g (a U x) = a V (P.map g.op x)) :
    (freeP R).obj P ⟶ F.obj where
  app U := ModuleCat.freeDesc (↾fun x : ULift.{1} (P.obj U) => a U.unop x.down)
  naturality := by
    intro U V g
    refine ModuleCat.free_hom_ext (fun x => ?_)
    have := ha V.unop U.unop g.unop x.down
    simp [freeP] at this ⊢
    erw [ModuleCat.free_map_apply, ModuleCat.freeDesc_apply]
    exact this.symm

/- English proof (translation)
Set `ψ` to `psiOf R P F a ha`. Set `φ : (presheafToSheaf Scheme.etaleTopology.{0} _).obj ((freeP R).obj P) ⟶ F` to `((sheafificationAdjunction _ _).homEquiv _ _).symm ψ`. Establish `key : toSheafify _ ((freeP R).obj P) ≫ φ.hom = ψ`. Use `((sheafificationAdjunction _ _).homEquiv _ _).apply_symm_apply ψ` as an intermediate fact. Rewrite `this` using `[Adjunction.homEquiv_unit]`.

Conclude with `this`. Use `⟨φ, fun U x => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `((toSheafify _ ((freeP R).obj P)).app (op U) ≫ φ.hom.app (op U)).hom (ModuleCat.freeMk (ULift.up x)) = _`. Rewrite using `[← NatTrans.comp_app, key]`. Use `erw [ModuleCat.freeDesc_apply]`.

Both sides reduce to the same expression.
-/
theorem free_hom_exists (P : PSh) (F : Shv R) (a : ∀ U : Scheme.{0}, P.obj (op U) → Sec F U)
    (ha : ∀ (V U : Scheme.{0}) (g : V ⟶ U) x, Sec.res g (a U x) = a V (P.map g.op x)) :
    ∃ φ : (free R).obj P ⟶ F, ∀ U x, Sec.map φ (freeGen R P U x) = a U x := by
  let ψ := psiOf R P F a ha
  let φ : (presheafToSheaf Scheme.etaleTopology.{0} _).obj ((freeP R).obj P) ⟶ F :=
    ((sheafificationAdjunction _ _).homEquiv _ _).symm ψ
  have key : toSheafify _ ((freeP R).obj P) ≫ φ.hom = ψ := by
    have := ((sheafificationAdjunction _ _).homEquiv _ _).apply_symm_apply ψ
    rw [Adjunction.homEquiv_unit] at this
    exact this
  refine ⟨φ, fun U x => ?_⟩
  change ((toSheafify _ ((freeP R).obj P)).app (op U) ≫ φ.hom.app (op U)).hom (ModuleCat.freeMk (ULift.up x)) = _
  rw [← NatTrans.comp_app, key]
  erw [ModuleCat.freeDesc_apply]
  rfl

end LateralTheory.EtaleFoundations.EvMkPf

open LateralTheory.EtaleFoundations.EvMkPf in
/- English proof (translation)
Introduce `R _ E I n a ha`. Establish `hex : ∀ (p : ℕ) (s : ℤ) (h : -(p:ℤ) + n = s), ∃ φ : (free R).obj (E.obj (op (SimplexCategory.mk p))) ⟶ I.X s, ∀ U x, Sec.map φ (freeGen R _ U x) = a p s h U x` using `fun p s h => free_hom_exists R _ _ (a p s h) (fun V U g x => ha p s h V U g x)`. Use `choose φ hφ using hex`. Set `f : ∀ (p : ℕ) (s : ℤ) (_ : -(p:ℤ) + n = s), (((chains R).obj E).X (-(p:ℤ)) ⟶ I.X s)` to `fun p s h => (chainsXIso R E p).hom ≫ φ p s h`. Set `α : Cochain ((chains R).obj E) I n` to `Cochain.mk (fun i j hij => if hi : 0 ≤ -i then (((chains R).obj E).XIsoOfEq (show i = -(((-i).toNat : ℕ) : ℤ) by omega)).hom ≫ f (-i).toNat j (by omega) else 0)`.

Use `⟨α, fun p s h U x => ?_⟩` and prove the remaining obligations. Establish `gen : ∀ (q : ℕ) (hq : q = p) (e : -(p:ℤ) = -(q:ℤ)) (h' : -(q:ℤ) + n = s), (((chains R).obj E).XIsoOfEq e).hom ≫ f q s h' = f p s h`. Introduce and unpack `q rfl e h'`. Simplify using the standard rewrite rules. Establish `hv : α.v (-(p:ℤ)) s h = f p s h`.

Simplify using `only [α, Cochain.mk_v]`. Rewrite using `[dif_pos (by omega)]`. Conclude with `gen _ (by omega) _ _`. Simplify using `only [GlobalTheory.EtC.ev]`. Rewrite using `[hv]`.

Simplify using `only [f]`. Rewrite using `[Iso.inv_hom_id_assoc]`. Conclude with `hφ p s h U x`.
-/
theorem LateralTheory.EtaleFoundations.etale_chain_cochain_exists_of_eval_data : LateralTheory.EtaleFoundations.EtaleCochainExistsOfNaturalEvaluation := by
  intro R _ E I n a ha
  have hex : ∀ (p : ℕ) (s : ℤ) (h : -(p:ℤ) + n = s), ∃ φ : (free R).obj (E.obj (op (SimplexCategory.mk p))) ⟶ I.X s,
      ∀ U x, Sec.map φ (freeGen R _ U x) = a p s h U x :=
    fun p s h => free_hom_exists R _ _ (a p s h) (fun V U g x => ha p s h V U g x)
  choose φ hφ using hex
  let f : ∀ (p : ℕ) (s : ℤ) (_ : -(p:ℤ) + n = s), (((chains R).obj E).X (-(p:ℤ)) ⟶ I.X s) :=
    fun p s h => (chainsXIso R E p).hom ≫ φ p s h
  let α : Cochain ((chains R).obj E) I n := Cochain.mk (fun i j hij =>
    if hi : 0 ≤ -i then
      (((chains R).obj E).XIsoOfEq (show i = -(((-i).toNat : ℕ) : ℤ) by omega)).hom ≫ f (-i).toNat j (by omega)
    else 0)
  refine ⟨α, fun p s h U x => ?_⟩
  have gen : ∀ (q : ℕ) (hq : q = p) (e : -(p:ℤ) = -(q:ℤ)) (h' : -(q:ℤ) + n = s),
      (((chains R).obj E).XIsoOfEq e).hom ≫ f q s h' = f p s h := by
    rintro q rfl e h'
    simp
  have hv : α.v (-(p:ℤ)) s h = f p s h := by
    simp only [α, Cochain.mk_v]
    rw [dif_pos (by omega)]
    exact gen _ (by omega) _ _
  simp only [GlobalTheory.EtC.ev]
  rw [hv]
  simp only [f]
  rw [Iso.inv_hom_id_assoc]
  exact hφ p s h U x
