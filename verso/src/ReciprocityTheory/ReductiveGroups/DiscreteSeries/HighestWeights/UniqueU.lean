import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.FromHC
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.Unique

noncomputable section

open Matrix

namespace ReciprocityTheory.ChartRestriction.DS.HW

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

/- English proof (translation)
Unfold `Jm`. Simplify using the standard rewrite rules.
-/
lemma uqU_Jm_allTrue (k : ℕ) : Jm (fun _ : Fin k => true) = 1 := by
  unfold Jm
  simp

/- English proof (translation)
Establish `h : gᴴ * Jm (fun _ : Fin k => true) * g = Jm (fun _ : Fin k => true)` using `hg`. Rewrite `h` using `[uqU_Jm_allTrue, Matrix.mul_one]`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.mem_unitaryGroup_iff']`. Rewrite using `[Matrix.star_eq_conjTranspose]`.

Conclude with `h`. Rewrite using `[uqU_Jm_allTrue, Matrix.mul_one, Matrix.one_mul]`.
-/
lemma uqU_mem_Kset {k : ℕ} {g : Matrix (Fin k) (Fin k) ℂ} (hg : g ∈ Formalism.MainNotions.S.UJset (Formalism.MainNotions.S.allPos k)) :
    g ∈ Kset (fun _ : Fin k => true) := by
  have h : gᴴ * Jm (fun _ : Fin k => true) * g = Jm (fun _ : Fin k => true) := hg
  rw [uqU_Jm_allTrue, Matrix.mul_one] at h
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff']
    rw [Matrix.star_eq_conjTranspose]
    exact h
  · rw [uqU_Jm_allTrue, Matrix.mul_one, Matrix.one_mul]

/- English proof (translation)
Take `⟨T, U₁, h₁⟩` from `kType_of_hcTypeU π hπ`. Take `⟨T', U₂, h₂⟩` from `kType_of_hcTypeU π' hπ'`. Take `⟨φ, hφ, -, -⟩` from `kType_unique T T'`. Use `⟨U₁.trans (φ.trans U₂.symm), ?_⟩` and prove the remaining obligations. Introduce `g hg v`.

Establish `hK` using `uqU_mem_Kset hg`. Establish `hU : g ∈ Matrix.unitaryGroup (Fin k) ℂ` using `hK.1`. Establish `hUJ : inUJ (fun _ : Fin k => true) g` using `hg`. Set `k0 : KG (fun _ : Fin k => true)` to `⟨⟨⟨g, star g, Unitary.mul_star_self_of_mem hU, Unitary.star_mul_self_of_mem hU⟩, hUJ⟩, hK⟩`. Establish `hk0 : toMK k0 = g` using `rfl`.

Apply `U₂.injective` to reduce the goal to its premises. Simplify using `only [LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.apply_symm_apply]`. Rewrite using `[← hk0, h₂, h₁, hφ, LinearIsometryEquiv.apply_symm_apply]`.
-/
theorem hcTypeU_unique {k : ℕ} {u : Fin k → ℝ} {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
    (π : Matrix (Fin k) (Fin k) ℂ → (H →L[ℂ] H)) (π' : Matrix (Fin k) (Fin k) ℂ → (H' →L[ℂ] H'))
    (hπ : Formalism.MainNotions.S.IsHCTypeU k u π) (hπ' : Formalism.MainNotions.S.IsHCTypeU k u π') :
    ∃ U : H ≃ₗᵢ[ℂ] H', ∀ g ∈ Formalism.MainNotions.S.UJset (Formalism.MainNotions.S.allPos k), ∀ v : H, π' g (U v) = U (π g v) := by
  obtain ⟨T, U₁, h₁⟩ := kType_of_hcTypeU π hπ
  obtain ⟨T', U₂, h₂⟩ := kType_of_hcTypeU π' hπ'
  obtain ⟨φ, hφ, -, -⟩ := kType_unique T T'
  refine ⟨U₁.trans (φ.trans U₂.symm), ?_⟩
  intro g hg v
  have hK := uqU_mem_Kset hg
  have hU : g ∈ Matrix.unitaryGroup (Fin k) ℂ := hK.1
  have hUJ : inUJ (fun _ : Fin k => true) g := hg
  let k0 : KG (fun _ : Fin k => true) :=
    ⟨⟨⟨g, star g, Unitary.mul_star_self_of_mem hU, Unitary.star_mul_self_of_mem hU⟩, hUJ⟩, hK⟩
  have hk0 : toMK k0 = g := rfl
  apply U₂.injective
  simp only [LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.apply_symm_apply]
  rw [← hk0, h₂, h₁, hφ, LinearIsometryEquiv.apply_symm_apply]

end ReciprocityTheory.ChartRestriction.DS.HW
