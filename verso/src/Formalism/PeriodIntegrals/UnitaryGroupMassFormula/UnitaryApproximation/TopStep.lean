import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryApproximation.MemIntOEOfIsIntegral
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryApproximation.Development

noncomputable section

open Matrix TensorProduct NumberField IsDedekindDomain

namespace PI.UnitaryApproxFinWork

/- English proof (translation)
Unfold `TopStep CayleyFin EigAvoid PI.UnitaryApproxFin.UnitaryApproxFin`. Introduce `hC hE F E iF iNF iE iNE iA n iFt iDe σ J hσ hθ hJ hdet T g hg D hD`. Take `⟨μ, hμ, hinv⟩` from `hE F E n σ hσ hθ T (fun v => ((g v : GL n _) : Matrix n n _))`. Establish `hμ' : μ * σ μ = 1` using `by rw [mul_comm]; exact hμ`. Establish `hab : ∀ v : HeightOneSpectrum (𝓞 F), PI.UnitaryApproxDefs.inclE (F` using `F) (v.adicCompletion F) μ * PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F) (σ μ) = 1 := fun v => by`.

Rewrite using `[← map_mul, hμ', map_one]`. Establish `hρ : ∀ v : HeightOneSpectrum (𝓞 F), PI.UnitaryApproxDefs.sigR σ (v.adicCompletion F) (PI.UnitaryApproxDefs.inclE (F` using `F) (v.adicCompletion F) μ) * PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F) μ = 1 := fun v => by`. Rewrite using `[sigR_inclE, ← map_mul, hμ, map_one]`. Take `⟨c, hc0, hc⟩` from `exists_int_mul (F := F) (σ μ)`. Take `⟨γ', hγ', hcong⟩` from `hC F E n σ J hσ hJ hdet T (fun v => scU (n := n) (PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F) μ) (PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F) (σ μ)) (hab v) * g v) (fun v hv => Subgroup.mul_mem _ (scU_mem_UJ (n := n) (PI.UnitaryApproxDefs.sigR σ (v.adicC …`.

Simplify using `only [Units.val_mul, scU_val, Matrix.smul_mul, Matrix.one_mul]`. Conclude with `hinv v hv)`. Use the proof step `(D * c) (mul_ne_zero hD hc0)`. Use `⟨scU (n := n) (σ μ) μ hμ * γ', Subgroup.mul_mem _ (scU_mem_UJ (n := n) (σ : E →+* E) J (σ μ) μ hμ ?_) hγ', ?_⟩` and prove the remaining obligations. Use `show σ (σ μ) * σ μ = 1`.

Rewrite using `[hσ, hμ']`. Introduce `v hv i j`. Take `⟨s, hs, hseq⟩` from `hcong v hv i j`. Use `⟨PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F) (algebraMap F E (c : F) * σ μ) * s, Subring.mul_mem _ (inclE_mem_Sv v hc) hs, ?_⟩` and prove the remaining obligations. Establish `hdv : dv E v (D * c) = PI.UnitaryApproxDefs.inclE (F` using `F) (v.adicCompletion F) (algebraMap F E (D : F)) * PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F) (algebraMap F E (c : F)) := dv_mul v D c`.

Establish `hba : PI.UnitaryApproxDefs.inclE (F` using `F) (v.adicCompletion F) (σ μ) * PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F) μ = 1 := by`. Rewrite using `[← map_mul, hμ, map_one]`. Simplify using `only [Units.val_mul, scU_val, Matrix.smul_mul, Matrix.one_mul, Matrix.smul_apply, smul_eq_mul] at hseq ⊢`. Rewrite `hseq` using `[hdv]`. Simplify using `only [map_mul]`.

Take the linear combination `PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F) (σ μ) * hseq - ((g v : GL n (E ⊗[F] v.adicCompletion F)) : Matrix n n (E ⊗[F] v.adicCompletion F)) i j * hba`.
-/
theorem topStep : TopStep := by
  unfold TopStep CayleyFin EigAvoid PI.UnitaryApproxFin.UnitaryApproxFin
  intro hC hE F E iF iNF iE iNE iA n iFt iDe σ J hσ hθ hJ hdet T g hg D hD
  obtain ⟨μ, hμ, hinv⟩ := hE F E n σ hσ hθ T (fun v => ((g v : GL n _) : Matrix n n _))
  have hμ' : μ * σ μ = 1 := by rw [mul_comm]; exact hμ
  have hab : ∀ v : HeightOneSpectrum (𝓞 F),
      PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F) μ *
        PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F) (σ μ) = 1 := fun v => by
    rw [← map_mul, hμ', map_one]
  have hρ : ∀ v : HeightOneSpectrum (𝓞 F),
      PI.UnitaryApproxDefs.sigR σ (v.adicCompletion F)
          (PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F) μ) *
        PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F) μ = 1 := fun v => by
    rw [sigR_inclE, ← map_mul, hμ, map_one]
  obtain ⟨c, hc0, hc⟩ := exists_int_mul (F := F) (σ μ)
  obtain ⟨γ', hγ', hcong⟩ := hC F E n σ J hσ hJ hdet T
    (fun v => scU (n := n) (PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F) μ)
      (PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F) (σ μ)) (hab v) * g v)
    (fun v hv => Subgroup.mul_mem _
      (scU_mem_UJ (n := n) (PI.UnitaryApproxDefs.sigR σ (v.adicCompletion F))
        (J.map (PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F))) _ _ _ (hρ v)) (hg v hv))
    (fun v hv => by
      simp only [Units.val_mul, scU_val, Matrix.smul_mul, Matrix.one_mul]
      exact hinv v hv)
    (D * c) (mul_ne_zero hD hc0)
  refine ⟨scU (n := n) (σ μ) μ hμ * γ',
    Subgroup.mul_mem _ (scU_mem_UJ (n := n) (σ : E →+* E) J (σ μ) μ hμ ?_) hγ', ?_⟩
  · show σ (σ μ) * σ μ = 1
    rw [hσ, hμ']
  · intro v hv i j
    obtain ⟨s, hs, hseq⟩ := hcong v hv i j
    refine ⟨PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F) (algebraMap F E (c : F) * σ μ) * s,
      Subring.mul_mem _ (inclE_mem_Sv v hc) hs, ?_⟩
    have hdv : dv E v (D * c) =
        PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F) (algebraMap F E (D : F)) *
          PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F) (algebraMap F E (c : F)) :=
      dv_mul v D c
    have hba : PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F) (σ μ) *
        PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F) μ = 1 := by
      rw [← map_mul, hμ, map_one]
    simp only [Units.val_mul, scU_val, Matrix.smul_mul, Matrix.one_mul, Matrix.smul_apply,
      smul_eq_mul] at hseq ⊢
    rw [hdv] at hseq
    simp only [map_mul]
    linear_combination PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F) (σ μ) * hseq -
      ((g v : GL n (E ⊗[F] v.adicCompletion F)) : Matrix n n (E ⊗[F] v.adicCompletion F)) i j * hba

end PI.UnitaryApproxFinWork

end
