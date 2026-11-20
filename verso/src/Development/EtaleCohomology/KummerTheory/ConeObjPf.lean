import Development.EtaleCohomology.KummerTheory.FinalTheorems

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.KummerTheory.LHCut

/- English proof (translation)
Apply the tactic sequence `change rst p g ≫ (pullbackSymmetry p U.hom).hom = (pullbackSymmetry p V.hom).hom ≫ pullback.lift (pullback.fst V.hom p ≫ g.left) (pullback.snd V.hom p) (by rw [Category.assoc, Over.w g]; exact pullback.condition)`. Apply the tactic sequence `apply pullback.hom_ext <;> simp only [rst, Category.assoc, pullbackSymmetry_hom_comp_fst, pullbackSymmetry_hom_comp_snd]`. Use `erw [pullback.lift_fst, pullbackSymmetry_hom_comp_fst_assoc]`. Simplify using `only [pullback.map]`. Use `erw [pullback.lift_snd]`.

Use `erw [pullback.lift_snd, pullbackSymmetry_hom_comp_snd]`. Simplify using `only [pullback.map, Category.comp_id]`. Use `erw [pullback.lift_fst]`.
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
Set `F : SlShv Λ S ⥤ ModuleCat.{1} (ULift.{1} Λ)` to `sheafToPresheaf (Scheme.etaleTopology.over S) (ModuleCat.{1} (ULift.{1} Λ)) ⋙ (evaluation (Over S)ᵒᵖ (ModuleCat.{1} (ULift.{1} Λ))).obj (op U)`. Set `e` to `PreservesProduct.iso F G ≪≫ ModuleCat.piIsoPi.{1, 1, 0} (fun i => F.obj (G i))`. Establish `: ∀ x, prodSec G U x = e.hom x`. Introduce `x`. Use function extensionality and compare the values at `i`.

Establish `h` using `congrArg (fun φ => φ.hom x) (congrArg (fun ψ => (PreservesProduct.iso F G).hom ≫ ψ) (ModuleCat.piIsoPi_hom_ker_subtype.{1, 1, 0} (fun i => F.obj (G i)) i))`. Simplify using `only [← Category.assoc, PreservesProduct.iso_hom, piComparison_comp_π] at h`. Conclude with `h.symm`. Establish `hb : Function.Bijective e.hom` using `e.toLinearEquiv.bijective`. Establish `h2 : (prodSec G U : _ → _) = fun x => e.hom x` using `funext this`.

Rewrite using `[h2]`. Conclude with `hb`.
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
Introduce `Λ _ J K hJ hK X S p r M j`. Set `σ` to `Σ a : Fin (M + 1), Fin (r a)`. Establish `hs : ∀ a : Fin (M + 1), ∃ hh : Presheaf.IsSheaf (Scheme.etaleTopology.over S) ((Over.forget S).op ⋙ (J.X (j + 1 - ((a : ℕ) : ℤ))).obj), Injective (⟨_, hh⟩ : SlShv Λ S)` using `fun a => (h Λ (J.X _) p).2`. Take `⟨hk, ik⟩` from `(h Λ (K.X j) p).1`. Set `G : ULift.{1} (Option σ) → SlShv Λ S` to `fun o => match o.down with`.

Consider the case `none => ⟨_, hk⟩`. Consider the case `some ⟨a, _⟩ => ⟨_, (hs a).choose⟩`. Establish `hG : ∀ o, Injective (G o)`. Introduce and unpack `⟨o⟩`. Break down `o with _ | ⟨a, s⟩` into its components or cases.

Conclude with `ik`. Conclude with `(hs a).choose_spec`. Use `⟨∏ᶜ G, inferInstance, ?_⟩` and prove the remaining obligations. Apply the tactic sequence `let sy : ∀ U : Over S, (K.X j).obj.obj (op ((tot p).obj U)) ≃ₗ[ULift.{1} Λ] Sec (K.X j) (pullback p U.hom) := fun U => ((K.X j).obj.mapIso (pullbackSymmetry p U.hom).op).toLinearEquiv`. Set `f2 : ∀ U : Over S, (∀ o, (G o).obj.obj (op U)) ≃ₗ[ULift.{1} Λ] Cone J K p r M j U` to `fun U => { toFun := fun x => (fun a s => x ⟨some ⟨a, s⟩⟩, sy U (x ⟨none⟩)) invFun := fun y o => match o with`.

Consider the case `⟨none⟩ => (sy U).symm y.2`. Consider the case `⟨some ⟨a, s⟩⟩ => y.1 a s`. Use the proof step `map_add' := fun x y => Prod.ext rfl ((sy U).map_add _ _)`. Use the proof step `map_smul' := fun c x => Prod.ext rfl ((sy U).map_smul _ _)`. Use `left_inv := by`.

Introduce `x`. Use function extensionality and compare the values at `o`. Break down `o with ⟨_ | ⟨a, s⟩⟩` into its components or cases. Conclude with `(sy U).symm_apply_apply _`. Both sides reduce to the same expression.

Use `right_inv := by`. Introduce `y`. Use extensionality with `a s`. Both sides reduce to the same expression. Conclude with `(sy U).apply_symm_apply _ }`.

Use `⟨fun U => (LinearEquiv.ofBijective (prodSec G U) (prodSec_bij G U)).trans (f2 U), ?_⟩` and prove the remaining obligations. Introduce `V U g x`. Establish `nat : ∀ o, ((Pi.π G o).hom.app (op V)).hom (((∏ᶜ G).obj.map g.op).hom x) = ((G o).obj.map g.op).hom (((Pi.π G o).hom.app (op U)).hom x)` using `fun o => by`. Use `congrArg (fun φ => φ.hom x) ((Pi.π G o).hom.naturality g.op)` as an intermediate fact. Simplify using `using this`.

Use `Prod.ext ?_ ?_` and prove the remaining obligations. Use function extensionality and compare the values at `a s`. Conclude with `nat ⟨some ⟨a, s⟩⟩`. Express the relevant statement in the definitionally equal form `(sy V) (((Pi.π G ⟨none⟩).hom.app (op V)).hom _) = Sec.res (rst p g) ((sy U) _)`. Rewrite using `[nat ⟨none⟩]`.

Apply the tactic sequence `have key : (K.X j).obj.map ((tot p).op.map g.op) ≫ (K.X j).obj.map (pullbackSymmetry p V.hom).op.hom = (K.X j).obj.map ((pullbackSymmetry p U.hom).op.hom ≫ (rst p g).op) := by`. Use `((K.X j).obj.map_comp _ _).symm.trans ?_` and prove the remaining obligations. Use `congr 1`. Apply `Quiver.Hom.unop_inj` to reduce the goal to its premises. Simplify using `only [unop_comp, Iso.op_hom, Quiver.Hom.unop_op, Functor.op_map]`.

Conclude with `(sym_tot p g).symm`. Apply the tactic sequence `change ((K.X j).obj.map ((tot p).op.map g.op) ≫ (K.X j).obj.map (pullbackSymmetry p V.hom).op.hom).hom (((Pi.π G ⟨none⟩).hom.app (op U)).hom x) = _`. Rewrite using `[key, (K.X j).obj.map_comp]`. Both sides reduce to the same expression.
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
