import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterDeRham
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.DeRhamJacobian.IsdRJ
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharLocalComponentExistsUniqueUnitary
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.HeckeSmooth

/- English proof (translation)
Introduce `E _ _ χ w`. Establish `hker : IsOpen ((χ.loc w).ker : Set (w.adicCompletion E)ˣ)` using `GlobalTheory.HeckeComp.smooth_loc χ w`. Set `V : Subgroup (w.adicCompletion E)ˣ` to `{ carrier := {x | Valued.v (x : w.adicCompletion E) = 1} mul_mem' := fun {a b} ha hb => by`. Simplify using `only [Set.mem_ofPred_eq, Units.val_mul, map_mul] at ha hb ⊢`. Rewrite using `[ha, hb, one_mul]`.

Use the proof step `one_mem' := by simp`. Use the proof step `inv_mem' := fun {a} ha => by`. Simplify using `only [Set.mem_ofPred_eq, Units.val_inv_eq_inv_val, map_inv₀] at ha ⊢`. Rewrite using `[ha, inv_one] }`. Establish `hV : IsOpen (V : Set (w.adicCompletion E)ˣ)`.

Rewrite using `[isOpen_iff_mem_nhds]`. Introduce `x hx`. Establish `hx1 : Valued.v (x : w.adicCompletion E) = 1` using `hx`. Establish `hx0 : Valued.v (x : w.adicCompletion E) ≠ 0` using `by rw [hx1]; exact one_ne_zero`. Establish `h2 : (fun y : (w.adicCompletion E)ˣ => (y : w.adicCompletion E)) ⁻¹' {y | Valued.v y = Valued.v (x : w.adicCompletion E)} ∈ nhds x` using `Units.continuous_val.continuousAt (Valued.locally_const hx0)`.

Use `Filter.mem_of_superset h2 ?_` and prove the remaining obligations. Introduce `y hy`. Establish `hy' : Valued.v (y : w.adicCompletion E) = Valued.v (x : w.adicCompletion E)` using `hy`. Use `show Valued.v (y : w.adicCompletion E) = 1`. Rewrite using `[hy', hx1]`.

Use `⟨(χ.loc w).ker ⊓ V, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Subgroup.coe_inf]`. Conclude with `hker.inter hV`. Introduce `x hx`. Conclude with `(Subgroup.mem_inf.mp hx).2`.

Introduce `x hx`. Conclude with `MonoidHom.mem_ker.mp (Subgroup.mem_inf.mp hx).1`.
-/
theorem exists_open_unit_subgroup_ker : ∀ {E : Type} [Field E] [NumberField E] (χ : HChar E)
    (w : HeightOneSpectrum (𝓞 E)),
    ∃ U : Subgroup (w.adicCompletion E)ˣ, IsOpen (U : Set (w.adicCompletion E)ˣ) ∧
      (∀ x ∈ U, IsUnitAt w x) ∧ ∀ x ∈ U, χ.1 (localIdele E w x) = 1 := by
  intro E _ _ χ w
  have hker : IsOpen ((χ.loc w).ker : Set (w.adicCompletion E)ˣ) := GlobalTheory.HeckeComp.smooth_loc χ w
  let V : Subgroup (w.adicCompletion E)ˣ :=
    { carrier := {x | Valued.v (x : w.adicCompletion E) = 1}
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_ofPred_eq, Units.val_mul, map_mul] at ha hb ⊢
        rw [ha, hb, one_mul]
      one_mem' := by simp
      inv_mem' := fun {a} ha => by
        simp only [Set.mem_ofPred_eq, Units.val_inv_eq_inv_val, map_inv₀] at ha ⊢
        rw [ha, inv_one] }
  have hV : IsOpen (V : Set (w.adicCompletion E)ˣ) := by
    rw [isOpen_iff_mem_nhds]
    intro x hx
    have hx1 : Valued.v (x : w.adicCompletion E) = 1 := hx
    have hx0 : Valued.v (x : w.adicCompletion E) ≠ 0 := by rw [hx1]; exact one_ne_zero
    have h2 : (fun y : (w.adicCompletion E)ˣ => (y : w.adicCompletion E)) ⁻¹'
        {y | Valued.v y = Valued.v (x : w.adicCompletion E)} ∈ nhds x :=
      Units.continuous_val.continuousAt (Valued.locally_const hx0)
    refine Filter.mem_of_superset h2 ?_
    intro y hy
    have hy' : Valued.v (y : w.adicCompletion E) = Valued.v (x : w.adicCompletion E) := hy
    show Valued.v (y : w.adicCompletion E) = 1
    rw [hy', hx1]
  refine ⟨(χ.loc w).ker ⊓ V, ?_, ?_, ?_⟩
  · rw [Subgroup.coe_inf]
    exact hker.inter hV
  · intro x hx
    exact (Subgroup.mem_inf.mp hx).2
  · intro x hx
    exact MonoidHom.mem_ker.mp (Subgroup.mem_inf.mp hx).1

end GlobalTheory.CompanionTheory.HeckeSmooth
