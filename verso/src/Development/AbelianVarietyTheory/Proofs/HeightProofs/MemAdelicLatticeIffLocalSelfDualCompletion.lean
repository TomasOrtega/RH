import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.AdelicUnitaryGroups
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ImportsBis
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions
open scoped TensorProduct

namespace GlobalTheory.LatticeLocalGlobal

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

omit [NumberField F] [NumberField E] in

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]`. Consider the case `tmul a e => simp [Algebra.TensorProduct.basis_repr_tmul]`.
-/
theorem repr_map {R R' ι : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R']
    (φ : R →ₐ[F] R') (b : Module.Basis ι F E) (z : R ⊗[F] E) (k : ι) :
    (Algebra.TensorProduct.basis R' b).repr (Algebra.TensorProduct.map φ (AlgHom.id F E) z) k =
      φ ((Algebra.TensorProduct.basis R b).repr z k) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]
  | tmul a e => simp [Algebra.TensorProduct.basis_repr_tmul]

omit [NumberField E] in

/- English proof (translation)
Set `b` to `Module.Basis.ofVectorSpace F E`. Apply `(Algebra.TensorProduct.basis (Af F) b).repr.injective` to reduce the goal to its premises. Use `Finsupp.ext fun k => FiniteAdeleRing.ext _ fun v => ?_` and prove the remaining obligations. Establish `h1` using `repr_map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) b z k`. Establish `h2` using `repr_map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) b z' k`.

Rewrite `h1` using `[h v, h2]`. Conclude with `h1.symm`.
-/
theorem ext_components (z z' : Af F ⊗[F] E)
    (h : ∀ v : HeightOneSpectrum (𝓞 F),
      Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) (AlgHom.id F E) z =
        Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) (AlgHom.id F E) z') : z = z' := by
  let b := Module.Basis.ofVectorSpace F E
  apply (Algebra.TensorProduct.basis (Af F) b).repr.injective
  refine Finsupp.ext fun k => FiniteAdeleRing.ext _ fun v => ?_
  have h1 := repr_map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) b z k
  have h2 := repr_map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) b z' k
  rw [h v, h2] at h1
  exact h1.symm

variable [StarRing E]

/- English proof (translation)
Use `V.standardTuple_isLattice` as an intermediate fact. Establish `: Module.Finite (𝓞 E) V.L0` using `Module.Finite.iff_fg.2 V.standardTuple_isLattice.fg`. Establish `: Module.Finite ℤ V.L0` using `Module.Finite.trans (𝓞 E) V.L0`. Take `⟨k, s, hs⟩` from `Module.Finite.exists_fin (R := ℤ) (M := V.L0)`. Use `⟨k, fun j => s j, fun j => (s j).2, fun w hw => ?_⟩` and prove the remaining obligations.

Establish `: (⟨w, hw⟩ : V.L0) ∈ Submodule.span ℤ (Set.range s)` using `hs ▸ Submodule.mem_top`. Take `⟨n, hn⟩` from `(Submodule.mem_span_range_iff_exists_fun ℤ).1 this`. Use `⟨n, ?_⟩` and prove the remaining obligations. Use `congrArg Subtype.val hn` as an intermediate fact. Simplify using `using this.symm`.
-/
theorem exists_generators (V : HSpace E) :
    ∃ (k : ℕ) (x : Fin k → V.V), (∀ j, x j ∈ V.L0) ∧
      ∀ w ∈ V.L0, ∃ n : Fin k → ℤ, w = ∑ j, n j • x j := by
  have := V.standardTuple_isLattice
  have : Module.Finite (𝓞 E) V.L0 := Module.Finite.iff_fg.2 V.standardTuple_isLattice.fg
  have : Module.Finite ℤ V.L0 := Module.Finite.trans (𝓞 E) V.L0
  obtain ⟨k, s, hs⟩ := Module.Finite.exists_fin (R := ℤ) (M := V.L0)
  refine ⟨k, fun j => s j, fun j => (s j).2, fun w hw => ?_⟩
  have : (⟨w, hw⟩ : V.L0) ∈ Submodule.span ℤ (Set.range s) := hs ▸ Submodule.mem_top
  obtain ⟨n, hn⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 this
  refine ⟨n, ?_⟩
  have := congrArg Subtype.val hn
  simpa using this.symm

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.MiscellaneousLemmas.main`. Consider the case `exact _root_.GlobalTheory.MiscellaneousLemmas.main`. Consider the case `(apply _root_.GlobalTheory.MiscellaneousLemmas.main <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.MiscellaneousLemmas.main <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.MiscellaneousLemmas.main <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.MiscellaneousLemmas.main ..)`.
-/
theorem exists_coeff (V : HSpace E) {k : ℕ} (x : Fin k → V.V)
    (hx : ∀ w ∈ V.L0, ∃ n : Fin k → ℤ, w = ∑ j, n j • x j) (v : HeightOneSpectrum (𝓞 F))
    (y : Fin V.rank → Fv F v ⊗[F] E) (hy : y ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.latLoc (F := F) V v) :
    ∃ a : Fin k → Fv F v, (∀ j, a j ∈ v.adicCompletionIntegers F) ∧
      ∀ i, y i = ∑ j, a j ⊗ₜ[F] V.frame.repr (x j) i := by
  first
  | exact @_root_.GlobalTheory.MiscellaneousLemmas.main
  | exact _root_.GlobalTheory.MiscellaneousLemmas.main
  | (apply _root_.GlobalTheory.MiscellaneousLemmas.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.MiscellaneousLemmas.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.MiscellaneousLemmas.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.MiscellaneousLemmas.main ..)

/- English proof (translation)
Introduce `F E _ _ _ _ _ _ V y`. Prove the components needed by the constructor for the conclusion. Introduce `hy v`. Proceed by induction on `hy using AddSubgroup.closure_induction with`. Consider the case `mem y hy`.

Take `⟨a, ha, x, hx, rfl⟩` from `hy`. Use `AddSubgroup.subset_closure ⟨_, ha v, _, hx, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`. Rewrite using `[V.frame.repr_sum_self]`. Both sides reduce to the same expression.

Consider the case `zero`. Simplify using `only [Pi.zero_apply, map_zero]`. Conclude with `zero_mem _`. Consider the case `add y z _ _ hy hz`. Simplify using `only [Pi.add_apply, map_add]`.

Conclude with `add_mem hy hz`. Consider the case `neg y _ hy`. Simplify using `only [Pi.neg_apply, map_neg]`. Conclude with `neg_mem hy`. Introduce `h`.

Take `⟨k, x, hxL, hx⟩` from `exists_generators V`. Use `choose a ha ea using fun v => exists_coeff V x hx v _ (h v)`. Set `A : Fin k → Af F` to `fun j => ⟨fun v => a v j, Filter.Eventually.of_forall fun v => ha v j⟩`. Establish `hA : ∀ j v, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (A j) = a v j` using `fun _ _ => rfl`. Establish `e : y = ∑ j, fun i => A j ⊗ₜ[F] V.frame.repr (x j) i`.

Use function extensionality and compare the values at `i`. Apply `ext_components` to reduce the goal to its premises. Introduce `v`. Rewrite using `[ea v i, Finset.sum_apply, map_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[Algebra.TensorProduct.map_tmul, hA]`. Both sides reduce to the same expression. Rewrite using `[e]`. Use `sum_mem fun j _ => AddSubgroup.subset_closure ⟨A j, fun v => ha v j, fun i => V.frame.repr (x j) i, ?_, rfl⟩` and prove the remaining obligations. Use `show ∑ i, V.frame.repr (x j) i • V.frame i ∈ V.L0`.

Rewrite using `[V.frame.sum_repr]`. Conclude with `hxL j`.
-/
theorem mem_latHat_iff :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
      (V : HSpace E) (y : Fin V.rank → Af F ⊗[F] E),
      y ∈ Formalism.MainNotions.StandardLattice.latHat F E {x : Fin V.rank → E | ∑ i, x i • V.frame i ∈ V.L0} ↔
        ∀ v : HeightOneSpectrum (𝓞 F),
          (fun i => Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) (AlgHom.id F E) (y i)) ∈
            GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.latLoc (F := F) V v := by
  intro F E _ _ _ _ _ _ V y
  constructor
  · intro hy v
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, ha, x, hx, rfl⟩ := hy
      refine AddSubgroup.subset_closure ⟨_, ha v, _, hx, ?_⟩
      funext i
      rw [V.frame.repr_sum_self]
      rfl
    | zero =>
      simp only [Pi.zero_apply, map_zero]
      exact zero_mem _
    | add y z _ _ hy hz =>
      simp only [Pi.add_apply, map_add]
      exact add_mem hy hz
    | neg y _ hy =>
      simp only [Pi.neg_apply, map_neg]
      exact neg_mem hy
  · intro h
    obtain ⟨k, x, hxL, hx⟩ := exists_generators V
    choose a ha ea using fun v => exists_coeff V x hx v _ (h v)
    let A : Fin k → Af F := fun j =>
      ⟨fun v => a v j, Filter.Eventually.of_forall fun v => ha v j⟩
    have hA : ∀ j v, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (A j) = a v j := fun _ _ => rfl
    have e : y = ∑ j, fun i => A j ⊗ₜ[F] V.frame.repr (x j) i := by
      funext i
      apply ext_components
      intro v
      rw [ea v i, Finset.sum_apply, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Algebra.TensorProduct.map_tmul, hA]
      rfl
    rw [e]
    refine sum_mem fun j _ => AddSubgroup.subset_closure
      ⟨A j, fun v => ha v j, fun i => V.frame.repr (x j) i, ?_, rfl⟩
    show ∑ i, V.frame.repr (x j) i • V.frame i ∈ V.L0
    rw [V.frame.sum_repr]
    exact hxL j

end GlobalTheory.LatticeLocalGlobal
