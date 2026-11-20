import Mathlib
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.HilbertSchmidtDecay.HaarExists

open MeasureTheory Matrix

namespace GlobalTheory.CompanionTheory.ParabolicHaar

open CompanionTheory.RgExh.Dec ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

/- English proof (translation)
Unfold `Keeps`. Prove the components needed by the constructor for the conclusion. Introduce `h v hv`. Establish `hm : Matrix.toLin' (g : Matrix (Fin n) (Fin n) ℂ) v ∈ Submodule.map (Matrix.toLin' (g : Matrix (Fin n) (Fin n) ℂ)) S` using `Submodule.mem_map_of_mem hv`. Rewrite `hm` using `[h]`.

Simplify `hm` using `[Matrix.toLin'_apply]`. Introduce `h`. Establish `hle : Submodule.map (Matrix.toLin' (g : Matrix (Fin n) (Fin n) ℂ)) S ≤ S`. Introduce and unpack `_ ⟨v, hv, rfl⟩`. Rewrite using `[Matrix.toLin'_apply]`.

Conclude with `h v hv`. Set `e : (Fin n → ℂ) ≃ₗ[ℂ] (Fin n → ℂ)` to `LinearEquiv.ofLinear (Matrix.toLin' (g : Matrix (Fin n) (Fin n) ℂ)) (Matrix.toLin' ((g⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)) (by rw [← Matrix.toLin'_mul, Units.mul_inv, Matrix.toLin'_one]) (by rw [← Matrix.toLin'_mul, Units.inv_mul, Matrix.toLin'_one])`. Establish `hfr : Module.finrank ℂ (Submodule.map (Matrix.toLin' (g : Matrix (Fin n) (Fin n) ℂ)) S) = Module.finrank ℂ S` using `LinearEquiv.finrank_map_eq e S`. Conclude with `Submodule.eq_of_le_of_finrank_eq hle hfr`.
-/
theorem keeps_iff_forall_mem (g : (Matrix (Fin n) (Fin n) ℂ)ˣ) (S : Submodule ℂ (Fin n → ℂ)) :
    Keeps (g : Matrix (Fin n) (Fin n) ℂ) S ↔
      ∀ v ∈ S, (g : Matrix (Fin n) (Fin n) ℂ) *ᵥ v ∈ S := by
  unfold Keeps
  constructor
  · intro h v hv
    have hm : Matrix.toLin' (g : Matrix (Fin n) (Fin n) ℂ) v ∈
        Submodule.map (Matrix.toLin' (g : Matrix (Fin n) (Fin n) ℂ)) S := Submodule.mem_map_of_mem hv
    rw [h] at hm
    simpa [Matrix.toLin'_apply] using hm
  · intro h
    have hle : Submodule.map (Matrix.toLin' (g : Matrix (Fin n) (Fin n) ℂ)) S ≤ S := by
      rintro _ ⟨v, hv, rfl⟩
      rw [Matrix.toLin'_apply]
      exact h v hv
    let e : (Fin n → ℂ) ≃ₗ[ℂ] (Fin n → ℂ) :=
      LinearEquiv.ofLinear (Matrix.toLin' (g : Matrix (Fin n) (Fin n) ℂ))
        (Matrix.toLin' ((g⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ))
        (by rw [← Matrix.toLin'_mul, Units.mul_inv, Matrix.toLin'_one])
        (by rw [← Matrix.toLin'_mul, Units.inv_mul, Matrix.toLin'_one])
    have hfr : Module.finrank ℂ (Submodule.map (Matrix.toLin' (g : Matrix (Fin n) (Fin n) ℂ)) S) =
        Module.finrank ℂ S := LinearEquiv.finrank_map_eq e S
    exact Submodule.eq_of_le_of_finrank_eq hle hfr

/- English proof (translation)
Establish `hset : {g : S7.UJ ε | Keeps (S7.toM g) S} = ⋂ v ∈ S, {g : S7.UJ ε | S7.toM g *ᵥ v ∈ S}`. Use extensionality with `g`. Simplify using `only [Set.mem_setOf_eq, Set.mem_iInter]`. Conclude with `keeps_iff_forall_mem (g : (Matrix (Fin n) (Fin n) ℂ)ˣ) S`. Rewrite using `[hset]`.

Use `isClosed_biInter fun v _ => ?_` and prove the remaining obligations. Establish `hS : IsClosed (S : Set (Fin n → ℂ))` using `S.closed_of_finiteDimensional`. Establish `hc : Continuous fun g : S7.UJ ε => S7.toM g *ᵥ v` using `Continuous.matrix_mulVec (Units.continuous_val.comp continuous_subtype_val) continuous_const`. Conclude with `IsClosed.preimage hc hS`.
-/
theorem isClosed_keeps (ε : Fin n → Bool) (S : Submodule ℂ (Fin n → ℂ)) :
    IsClosed {g : S7.UJ ε | Keeps (S7.toM g) S} := by
  have hset : {g : S7.UJ ε | Keeps (S7.toM g) S} =
      ⋂ v ∈ S, {g : S7.UJ ε | S7.toM g *ᵥ v ∈ S} := by
    ext g
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    exact keeps_iff_forall_mem (g : (Matrix (Fin n) (Fin n) ℂ)ˣ) S
  rw [hset]
  refine isClosed_biInter fun v _ => ?_
  have hS : IsClosed (S : Set (Fin n → ℂ)) := S.closed_of_finiteDimensional
  have hc : Continuous fun g : S7.UJ ε => S7.toM g *ᵥ v :=
    Continuous.matrix_mulVec (Units.continuous_val.comp continuous_subtype_val) continuous_const
  exact IsClosed.preimage hc hS

/- English proof (translation)
Conclude with `(isClosed_keeps ε (Vm A)).inter (isClosed_keeps ε (Wm A))`.
-/
theorem isClosed_pSub (ε : Fin n → Bool) (A : Matrix (Fin n) (Fin n) ℂ) :
    IsClosed (PSub ε A : Set (S7.UJ ε)) := by
  exact (isClosed_keeps ε (Vm A)).inter (isClosed_keeps ε (Wm A))

instance (ε : Fin n → Bool) (A : Matrix (Fin n) (Fin n) ℂ) : LocallyCompactSpace (PSub ε A) :=
  (isClosed_pSub ε A).isClosedEmbedding_subtypeVal.locallyCompactSpace

/- English proof (translation)
Use `infer_instance`.
-/
theorem haar_pSub_isHaar (ε : Fin n → Bool) (A : Matrix (Fin n) (Fin n) ℂ) :
    (Measure.haar : Measure (PSub ε A)).IsHaarMeasure := by
  infer_instance

/- English proof (translation)
Introduce `n ε A _`. Conclude with `⟨Measure.haar, haar_pSub_isHaar ε A⟩`.
-/
theorem haarExists : CompanionTheory.RgExh.Dec.L.HaarExists := by
  intro n ε A _
  exact ⟨Measure.haar, haar_pSub_isHaar ε A⟩

end GlobalTheory.CompanionTheory.ParabolicHaar
