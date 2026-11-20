import Development.EtaleCohomology.KummerTheory.FinalTheorems

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.KummerTheory.LHCut

/- English proof (translation)
Express the relevant assertion in an equivalent form by its definition. Apply the first step, then apply the next step to every resulting obligation. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem sym_tot {X S : Scheme.{0}} (p : X ⟶ S) {V U : Over S} (g : V ⟶ U) :
    rst p g ≫ (pullbackSymmetry p U.hom).hom = (pullbackSymmetry p V.hom).hom ≫ (tot p).map g := by
  change rst p g ≫ (pullbackSymmetry p U.hom).hom = (pullbackSymmetry p V.hom).hom ≫
    pullback.lift (pullback.fst V.hom p ≫ g.left) (pullback.snd V.hom p)
      (by rw [Category.assoc, Over.w g]; exact pullback.condition)
  apply pullback.hom_ext <;> simp only [rst, Category.assoc, pullbackSymmetry_hom_comp_fst, pullbackSymmetry_hom_comp_snd]
  · erw [pullback.lift_fst, pullbackSymmetry_hom_comp_fst_assoc]; simp only [pullback.map]; erw [pullback.lift_snd]
  · erw [pullback.lift_snd, pullbackSymmetry_hom_comp_snd]; simp only [pullback.map, Category.comp_id]; erw [pullback.lift_fst]

def prodSec {Λ : Type} [CommRing Λ] {S : Scheme.{0}} {ι : Type 1} (G : ι → SlShv Λ S) (U : Over S) :
    (∏ᶜ G).obj.obj (op U) →ₗ[ULift.{1} Λ] (∀ i, (G i).obj.obj (op U)) :=
  LinearMap.pi fun i => ((Pi.π G i).hom.app (op U)).hom

/- English proof (translation)
Introduce a local definition for the expression. Introduce a local definition for the expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Apply function extensionality and compare values at an arbitrary argument.

Establish an intermediate fact. Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem prodSec_bij {Λ : Type} [CommRing Λ] {S : Scheme.{0}} {ι : Type 1} (G : ι → SlShv Λ S) (U : Over S) :
    Function.Bijective (prodSec G U) := by
  let F : SlShv Λ S ⥤ ModuleCat.{1} (ULift.{1} Λ) := sheafToPresheaf (Scheme.etaleTopology.over S) (ModuleCat.{1} (ULift.{1} Λ)) ⋙
    (evaluation (Over S)ᵒᵖ (ModuleCat.{1} (ULift.{1} Λ))).obj (op U)
  let e := PreservesProduct.iso F G ≪≫ ModuleCat.piIsoPi.{1, 1, 0} (fun i => F.obj (G i))
  have : ∀ x, prodSec G U x = e.hom x := by
    intro x; funext i
    have h := congrArg (fun φ => φ.hom x) (congrArg (fun ψ => (PreservesProduct.iso F G).hom ≫ ψ)
      (ModuleCat.piIsoPi_hom_ker_subtype.{1, 1, 0} (fun i => F.obj (G i)) i))
    simp only [← Category.assoc, PreservesProduct.iso_hom, piComparison_comp_π] at h
    exact h.symm
  have hb : Function.Bijective e.hom := e.toLinearEquiv.bijective
  have h2 : (prodSec G U : _ → _) = fun x => e.hom x := funext this
  rw [h2]; exact hb

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Establish an intermediate fact. Extract witnesses or component facts from the available result. Introduce a local definition for the expression.

Treat this case separately. Treat this case separately. Establish an intermediate fact. Assume the hypotheses and unpack their components. Separate the alternatives or extract the components of the hypothesis.

Reduce the conclusion to the remaining proof obligations. Introduce a local definition for the expression. Introduce a local definition for the expression. Treat this case separately. Treat this case separately.

Fix the arbitrary inputs or assume the hypotheses. Apply function extensionality and compare values at an arbitrary argument. Separate the alternatives or extract the components of the hypothesis. Both sides reduce to the same expression. Fix the arbitrary inputs or assume the hypotheses.

By extensionality, compare the relevant components. Both sides reduce to the same expression. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Reduce the conclusion to the remaining proof obligations. Apply function extensionality and compare values at an arbitrary argument. Express the relevant assertion in an equivalent form by its definition.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Reduce the equality to equality of the corresponding arguments. Reduce the claim to the hypotheses of an applicable result.

Simplify using the standard rewrite rules. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem coneObj_of (h : InjSlice) : ConeObj := by
  intro Λ _ J K hJ hK X S p r M j
  let σ := Σ a : Fin (M + 1), Fin (r a)
  have hs : ∀ a : Fin (M + 1), ∃ hh : Presheaf.IsSheaf (Scheme.etaleTopology.over S)
      ((Over.forget S).op ⋙ (J.X (j + 1 - ((a : ℕ) : ℤ))).obj),
      Injective (⟨_, hh⟩ : SlShv Λ S) := fun a => (h Λ (J.X _) p).2
  obtain ⟨hk, ik⟩ := (h Λ (K.X j) p).1
  let G : ULift.{1} (Option σ) → SlShv Λ S := fun o => match o.down with
    | none => ⟨_, hk⟩
    | some ⟨a, _⟩ => ⟨_, (hs a).choose⟩
  have hG : ∀ o, Injective (G o) := by
    rintro ⟨o⟩; rcases o with _ | ⟨a, s⟩
    · exact ik
    · exact (hs a).choose_spec
  refine ⟨∏ᶜ G, inferInstance, ?_⟩
  let sy : ∀ U : Over S, (K.X j).obj.obj (op ((tot p).obj U)) ≃ₗ[ULift.{1} Λ] Sec (K.X j) (pullback p U.hom) :=
    fun U => ((K.X j).obj.mapIso (pullbackSymmetry p U.hom).op).toLinearEquiv
  let f2 : ∀ U : Over S, (∀ o, (G o).obj.obj (op U)) ≃ₗ[ULift.{1} Λ] Cone J K p r M j U := fun U =>
    { toFun := fun x => (fun a s => x ⟨some ⟨a, s⟩⟩, sy U (x ⟨none⟩))
      invFun := fun y o => match o with
        | ⟨none⟩ => (sy U).symm y.2
        | ⟨some ⟨a, s⟩⟩ => y.1 a s
      map_add' := fun x y => Prod.ext rfl ((sy U).map_add _ _)
      map_smul' := fun c x => Prod.ext rfl ((sy U).map_smul _ _)
      left_inv := by
        intro x; funext o; rcases o with ⟨_ | ⟨a, s⟩⟩
        · exact (sy U).symm_apply_apply _
        · rfl
      right_inv := by
        intro y; ext a s
        · rfl
        · exact (sy U).apply_symm_apply _ }
  refine ⟨fun U => (LinearEquiv.ofBijective (prodSec G U) (prodSec_bij G U)).trans (f2 U), ?_⟩
  intro V U g x
  have nat : ∀ o, ((Pi.π G o).hom.app (op V)).hom (((∏ᶜ G).obj.map g.op).hom x) =
      ((G o).obj.map g.op).hom (((Pi.π G o).hom.app (op U)).hom x) := fun o => by
    have := congrArg (fun φ => φ.hom x) ((Pi.π G o).hom.naturality g.op)
    simpa using this
  refine Prod.ext ?_ ?_
  · funext a s; exact nat ⟨some ⟨a, s⟩⟩
  · change (sy V) (((Pi.π G ⟨none⟩).hom.app (op V)).hom _) = Sec.res (rst p g) ((sy U) _)
    rw [nat ⟨none⟩]
    have key : (K.X j).obj.map ((tot p).op.map g.op) ≫ (K.X j).obj.map (pullbackSymmetry p V.hom).op.hom =
        (K.X j).obj.map ((pullbackSymmetry p U.hom).op.hom ≫ (rst p g).op) := by
      refine ((K.X j).obj.map_comp _ _).symm.trans ?_; congr 1; apply Quiver.Hom.unop_inj
      simp only [unop_comp, Iso.op_hom, Quiver.Hom.unop_op, Functor.op_map]
      exact (sym_tot p g).symm
    change ((K.X j).obj.map ((tot p).op.map g.op) ≫ (K.X j).obj.map (pullbackSymmetry p V.hom).op.hom).hom
      (((Pi.π G ⟨none⟩).hom.app (op U)).hom x) = _
    rw [key, (K.X j).obj.map_comp]; rfl

end LateralTheory.KummerTheory.LHCut
