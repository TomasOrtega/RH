import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.MeasProps
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.IsPureTIff
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FourierCompactness.SigmaSigmaOfGood

set_option linter.unusedSectionVars false

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.MeasD

open PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.KWhit PositivityTheory.SiegelWeilFormula.kfour

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def colE (m n : ℕ) : (Fin n → Fin m → AF F ⊗[F] E) ≃ₜ+ Mx F E m n where
  toFun := toMx
  invFun := fun X j a => X a j
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  map_add' := fun _ _ => rfl
  continuous_toFun := continuous_pi fun a => continuous_pi fun j => (continuous_apply a).comp (continuous_apply j)
  continuous_invFun := continuous_pi fun j => continuous_pi fun a => (continuous_apply j).comp (continuous_apply a)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem colE_apply {m n : ℕ} (Y : Fin n → Fin m → AF F ⊗[F] E) : colE m n Y = toMx Y := rfl

def colM (m n : ℕ) : (Fin n → Fin m → AF F ⊗[F] E) ≃ᵐ Mx F E m n := (colE (F := F) (E := E) m n).toHomeomorph.toMeasurableEquiv

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem colM_apply {m n : ℕ} (Y : Fin n → Fin m → AF F ⊗[F] E) : colM m n Y = toMx Y := rfl

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Apply function extensionality and compare values at an arbitrary argument.

Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.

A detailed English derivation is pending.
-/
theorem toMx_mem {m n : ℕ} (Y : Fin n → Fin m → AF F ⊗[F] E) :
    toMx Y ∈ ratMx F E m n ↔ Y ∈ MeasP.ratTupA F E n m := by
  rw [mem_ratMx]
  constructor
  · rintro ⟨X, hX⟩
    refine ⟨fun j a => X a j, ?_⟩
    funext j a
    exact congrFun (congrFun hX a) j
  · rintro ⟨Z, hZ⟩
    refine ⟨Matrix.of fun a j => Z j a, ?_⟩
    funext a j
    rw [← hZ]
    rfl

def ratEq (m n : ℕ) : ratMx F E m n ≃ MeasP.ratTupA F E n m where
  toFun X := ⟨(colE m n).symm X.1, (toMx_mem _).1 X.2⟩
  invFun Y := ⟨toMx Y.1, (toMx_mem _).2 Y.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/- English proof (translation)
Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses.

Both sides reduce to the same expression. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem meas_toMx (d : SD σ) (μ : Measure (Fin d.n → Fin d.m → AF F ⊗[F] E)) (𝓕 : Set (Fin d.n → Fin d.m → AF F ⊗[F] E))
    (hμ : μ.IsAddHaarMeasure) (hF : IsAddFundamentalDomain (MeasP.ratTupA F E d.n d.m) 𝓕 μ) (h1 : μ 𝓕 = 1) :
    MeasurableEmbedding (toMx (F := F) (E := E) (m := d.m) (n := d.n)) ∧ (μ.map toMx).IsAddHaarMeasure ∧
      IsAddFundamentalDomain d.ratM (toMx '' 𝓕) (μ.map toMx) ∧ μ.map toMx (toMx '' 𝓕) = 1 := by
  have hemb : MeasurableEmbedding (toMx (F := F) (E := E) (m := d.m) (n := d.n)) := (colM d.m d.n).measurableEmbedding
  refine ⟨hemb, ?_, ?_, ?_⟩
  · exact (colE (F := F) (E := E) d.m d.n).toAddEquiv.isAddHaarMeasure_map μ (colE d.m d.n).continuous
      (colE d.m d.n).symm.continuous
  · rw [ratM_eq]
    refine hF.image_of_equiv (colM d.m d.n).toEquiv ?_ (ratEq d.m d.n) ?_
    · exact ((colM d.m d.n).measurePreserving_symm μ).quasiMeasurePreserving
    · intro g x
      rfl
  · rw [hemb.map_apply, Set.preimage_image_eq _ hemb.injective, h1]

end PositivityTheory.SiegelWeilFormula.MeasD

end
