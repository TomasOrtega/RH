import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PowMulMemAdd
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

noncomputable section

namespace GlobalTheory.Ord2.DualCont

/- English proof (translation)
The claim follows from `(Continuous.units_map _ (show Continuous (fun x : ℤ_[l] => algebraMap ℚ_[l] (Qbar l) (x : ℚ_[l])) from (continuous_algebraMap ℚ_[l] (Qbar l)).comp continuous_subtype_val)).comp (continuous_cycZ ℚ Ω l)`.
-/
theorem cyc_cont' {Ω : Type} [Field Ω] [Algebra ℚ Ω] (l : ℕ) [Fact l.Prime] : Continuous (cycBar ℚ Ω l) :=
  (Continuous.units_map _ (show Continuous (fun x : ℤ_[l] => algebraMap ℚ_[l] (Qbar l) (x : ℚ_[l])) from
    (continuous_algebraMap ℚ_[l] (Qbar l)).comp continuous_subtype_val)).comp (continuous_cycZ ℚ Ω l)

/- English proof (translation)
Use `Units.continuous_iff.2 ⟨h, ?_⟩` and prove the remaining obligations. Simplify using `only [← map_inv]`. Conclude with `h.comp continuous_inv`.
-/
theorem units_cont {Γ R : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Monoid R]
    [TopologicalSpace R] (f : Γ →* Rˣ) (h : Continuous fun s => (f s : R)) : Continuous f := by
  refine Units.continuous_iff.2 ⟨h, ?_⟩
  simp only [← map_inv]
  exact h.comp continuous_inv

/- English proof (translation)
Introduce `l _ Ω _ _ _ e S A W hN`. Establish `hW : Continuous fun s => ((W s : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l))` using `Units.continuous_val.comp hN.cont`. Establish `hd : Continuous (dt W)`. Apply `units_cont` to reduce the goal to its premises. Use `show Continuous fun s => (Matrix.GeneralLinearGroup.det (W s) : Qbar l)`.

Simplify using `only [Matrix.GeneralLinearGroup.val_det_apply]`. Conclude with `hW.matrix_det`. Establish `hc` using `cyc_cont' (Ω := Ω) l`. Establish `hχ : Continuous (cycBar ℚ Ω l * (dt W)⁻¹)` using `by show Continuous fun s => cycBar ℚ Ω l s * ((dt W) s)⁻¹`. Conclude with `hc.mul hd.inv`.

Apply `units_cont` to reduce the goal to its premises. Use `show Continuous fun s => ((tw W (cycBar ℚ Ω l * (dt W)⁻¹) s : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l))`. Simplify using `only [tw_val]`. Conclude with `(Units.continuous_val.comp hχ).smul hW`.
-/
theorem continuous_galoisRepRankTwoTateDual : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → Continuous (dual1 W) := by
  intro l _ Ω _ _ _ e S A W hN
  have hW : Continuous fun s => ((W s : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l)) :=
    Units.continuous_val.comp hN.cont
  have hd : Continuous (dt W) := by
    apply units_cont
    show Continuous fun s => (Matrix.GeneralLinearGroup.det (W s) : Qbar l)
    simp only [Matrix.GeneralLinearGroup.val_det_apply]
    exact hW.matrix_det
  have hc := cyc_cont' (Ω := Ω) l
  have hχ : Continuous (cycBar ℚ Ω l * (dt W)⁻¹) := by
    show Continuous fun s => cycBar ℚ Ω l s * ((dt W) s)⁻¹
    exact hc.mul hd.inv
  apply units_cont
  show Continuous fun s => ((tw W (cycBar ℚ Ω l * (dt W)⁻¹) s : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l))
  simp only [tw_val]
  exact (Units.continuous_val.comp hχ).smul hW

end GlobalTheory.Ord2.DualCont
