import Development.EtaleCohomology.EtaleSheaves.MayerVietorisSequence

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.OpenCov_ptaPf

variable (R : Type) [CommRing R]

abbrev gen (P : PSh) {W : Scheme.{0}ᵒᵖ} (x : P.obj W) : ((freeP R).obj P).obj W :=
  ModuleCat.freeMk (X := uliftFunctor.{1}.obj (P.obj W)) (ULift.up x)

abbrev adj {P : PSh} {G : Shv R} (a : (free R).obj P ⟶ G) : (freeP R).obj P ⟶ G.obj :=
  toSheafify Scheme.etaleTopology ((freeP R).obj P) ≫ a.hom

/- English proof (translation)
Use `ext1`. Conclude with `sheafify_hom_ext _ _ _ G.property h`.
-/
theorem adj_inj {P : PSh} {G : Shv R} (a b : (free R).obj P ⟶ G) (h : adj R a = adj R b) : a = b := by
  ext1
  exact sheafify_hom_ext _ _ _ G.property h

/- English proof (translation)
Use `show toSheafify _ _ ≫ (sheafifyMap _ ((freeP R).map φ) ≫ a.hom) = _`. Use `show _ = (freeP R).map φ ≫ toSheafify _ _ ≫ a.hom`. Use `erw [toSheafify_naturality_assoc]`.
-/
theorem adj_comp {P Q : PSh} {G : Shv R} (φ : P ⟶ Q) (a : (free R).obj Q ⟶ G) :
    adj R ((free R).map φ ≫ a) = (freeP R).map φ ≫ adj R a := by
  show toSheafify _ _ ≫ (sheafifyMap _ ((freeP R).map φ) ≫ a.hom) = _
  show _ = (freeP R).map φ ≫ toSheafify _ _ ≫ a.hom
  erw [toSheafify_naturality_assoc]

/- English proof (translation)
Simplify using `[freeP, gen]`. Use `erw [ModuleCat.free_map_apply]`. Both sides reduce to the same expression.
-/
theorem freePresheaf_obj_map_freeMk (P : PSh) {W W' : Scheme.{0}ᵒᵖ} (h : W ⟶ W') (x : P.obj W) :
    ((freeP R).obj P).map h (gen R P x) = gen R P (P.map h x) := by
  dsimp [freeP, gen]
  erw [ModuleCat.free_map_apply]
  rfl

/- English proof (translation)
Simplify using `[freeP, gen]`. Use `erw [ModuleCat.free_map_apply]`. Both sides reduce to the same expression.
-/
theorem freePresheaf_map_freeMk {P Q : PSh} (φ : P ⟶ Q) (W : Scheme.{0}ᵒᵖ) (x : P.obj W) :
    ((freeP R).map φ).app W (gen R P x) = gen R Q (φ.app W x) := by
  dsimp [freeP, gen]
  erw [ModuleCat.free_map_apply]
  rfl

/- English proof (translation)
Rewrite using `[← ConcreteCategory.comp_apply, ← (adj R a).naturality, ConcreteCategory.comp_apply, freePresheaf_obj_map_freeMk]`. Simplify using the standard rewrite rules.
-/
theorem adj_val {X Y : Scheme.{0}} {G : Shv R} (a : (free R).obj (yoneda.obj X) ⟶ G) (x : Y ⟶ X) :
    (adj R a).app (op Y) (gen R (yoneda.obj X) (W := op Y) x) =
      G.obj.map x.op ((adj R a).app (op X) (gen R (yoneda.obj X) (W := op X) (𝟙 X))) := by
  rw [← ConcreteCategory.comp_apply, ← (adj R a).naturality, ConcreteCategory.comp_apply, freePresheaf_obj_map_freeMk]
  simp

/- English proof (translation)
Set `Z : Bool → Scheme.{0}` to `fun i => Bool.rec V U i`. Set `φ : ∀ i, Z i ⟶ X` to `fun i => Bool.rec (motive := fun i => Z i ⟶ X) g f i`. Establish `hS : Sieve.ofArrows Z φ ∈ Scheme.etaleTopology X`. Apply `Precoverage.generate_mem_toGrothendieck` to reduce the goal to its premises. Use `(Scheme.ofArrows_mem_precoverage_iff _).2 ⟨fun x => ?_, fun i => ?_⟩` and prove the remaining obligations.

Establish `hx : x ∈ Set.range f ∪ Set.range g` using `hcov ▸ Set.mem_univ x`. Break down `hx with hx | hx` into its components or cases. Conclude with `⟨true, hx⟩`. Conclude with `⟨false, hx⟩`. Apply the tactic sequence `cases i <;> infer_instance`.

Establish `hf'` using `congrArg (adj R) hf`. Establish `hg'` using `congrArg (adj R) hg`. Rewrite `hf'`, `hg'` using `[adj_comp, adj_comp]`. Establish `key : (adj R a).app (op X) (gen R (yoneda.obj X) (W` using `op X) (𝟙 X)) = (adj R b).app (op X) (gen R (yoneda.obj X) (W := op X) (𝟙 X)) := by`. Use `Presheaf.IsSheaf.isSeparated G.property _ _ hS _ _ ?_` and prove the remaining obligations.

Introduce `Y' h hh`. Take `⟨W, k, _, ⟨i⟩, rfl⟩` from `hh`. Rewrite using `[← adj_val, ← adj_val]`. Consider the cases of `i`. Use `congrArg (fun t => t.app (op _) (gen R (yoneda.obj V) (W := op _) k)) hg'` as an intermediate fact.

Simplify `this` using `[freePresheaf_map_freeMk]`. Use `congrArg (fun t => t.app (op _) (gen R (yoneda.obj U) (W := op _) k)) hf'` as an intermediate fact. Simplify `this` using `[freePresheaf_map_freeMk]`. Apply `adj_inj` to reduce the goal to its premises. Use extensionality with `Y : 2`.

Proceed by induction on `Y with | op Y => ?_`. Apply `ModuleCat.free_hom_ext` to reduce the goal to its premises. Introduce and unpack `⟨x⟩`. Conclude with `(adj_val R a x).trans ((congrArg _ key).trans (adj_val R b x).symm)`.
-/
theorem ext_of_cover {U V X : Scheme.{0}} (f : U ⟶ X) (g : V ⟶ X) [IsOpenImmersion f] [IsOpenImmersion g]
    (hcov : Set.range f ∪ Set.range g = Set.univ) {G : Shv R} (a b : (free R).obj (yoneda.obj X) ⟶ G)
    (hf : (free R).map (yoneda.map f) ≫ a = (free R).map (yoneda.map f) ≫ b)
    (hg : (free R).map (yoneda.map g) ≫ a = (free R).map (yoneda.map g) ≫ b) : a = b := by
  let Z : Bool → Scheme.{0} := fun i => Bool.rec V U i
  let φ : ∀ i, Z i ⟶ X := fun i => Bool.rec (motive := fun i => Z i ⟶ X) g f i
  have hS : Sieve.ofArrows Z φ ∈ Scheme.etaleTopology X := by
    apply Precoverage.generate_mem_toGrothendieck
    refine (Scheme.ofArrows_mem_precoverage_iff _).2 ⟨fun x => ?_, fun i => ?_⟩
    · have hx : x ∈ Set.range f ∪ Set.range g := hcov ▸ Set.mem_univ x
      rcases hx with hx | hx
      · exact ⟨true, hx⟩
      · exact ⟨false, hx⟩
    · cases i <;> infer_instance
  have hf' := congrArg (adj R) hf
  have hg' := congrArg (adj R) hg
  rw [adj_comp, adj_comp] at hf' hg'
  have key : (adj R a).app (op X) (gen R (yoneda.obj X) (W := op X) (𝟙 X)) =
      (adj R b).app (op X) (gen R (yoneda.obj X) (W := op X) (𝟙 X)) := by
    refine Presheaf.IsSheaf.isSeparated G.property _ _ hS _ _ ?_
    intro Y' h hh
    obtain ⟨W, k, _, ⟨i⟩, rfl⟩ := hh
    rw [← adj_val, ← adj_val]
    cases i
    · have := congrArg (fun t => t.app (op _) (gen R (yoneda.obj V) (W := op _) k)) hg'
      simpa [freePresheaf_map_freeMk] using this
    · have := congrArg (fun t => t.app (op _) (gen R (yoneda.obj U) (W := op _) k)) hf'
      simpa [freePresheaf_map_freeMk] using this
  apply adj_inj
  ext Y : 2
  induction Y with | op Y => ?_
  apply ModuleCat.free_hom_ext
  rintro ⟨x⟩
  exact (adj_val R a x).trans ((congrArg _ key).trans (adj_val R b x).symm)

/- English proof (translation)
Introduce `R _ U V X f g _ _ hcov`. Establish `: PreservesLimitsOfShape WalkingCospan sch` using `by unfold sch; infer_instance`. Establish `: sch.PreservesMonomorphisms` using `preservesMonomorphisms_of_preservesLimitsOfShape _`. Use `⟨inferInstance, inferInstance, fun n => ⟨fun {G} a b h => ?_⟩⟩` and prove the remaining obligations. Apply `ext_of_cover R f g hcov a b` to reduce the goal to its premises.

Establish `h1 : (free R).map ((sch.map f).app n) ≫ a = (free R).map ((sch.map f).app n) ≫ b`. Simplify using `using congrArg (biprod.inl ≫ ·) h`. Conclude with `h1`. Establish `h1 : (free R).map ((sch.map g).app n) ≫ a = (free R).map ((sch.map g).app n) ≫ b`. Simplify using `using congrArg (biprod.inr ≫ ·) h`.

Conclude with `h1`.
-/
theorem openCov : LateralTheory.E.MayerVietorisSequence.OpenCov := by
  intro R _ U V X f g _ _ hcov
  have : PreservesLimitsOfShape WalkingCospan sch := by unfold sch; infer_instance
  have : sch.PreservesMonomorphisms := preservesMonomorphisms_of_preservesLimitsOfShape _
  refine ⟨inferInstance, inferInstance, fun n => ⟨fun {G} a b h => ?_⟩⟩
  apply ext_of_cover R f g hcov a b
  · have h1 : (free R).map ((sch.map f).app n) ≫ a = (free R).map ((sch.map f).app n) ≫ b := by
      simpa using congrArg (biprod.inl ≫ ·) h
    exact h1
  · have h1 : (free R).map ((sch.map g).app n) ≫ a = (free R).map ((sch.map g).app n) ≫ b := by
      simpa using congrArg (biprod.inr ≫ ·) h
    exact h1

end LateralTheory.E.OpenCov_ptaPf
