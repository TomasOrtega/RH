import Mathlib
import Formalism.PeriodIntegrals.UnitKron

namespace PI.UnitKronW

open Matrix Polynomial ComplexOrder

def StepA : Prop := ∀ (k : ℕ) (H G : Matrix (Fin k) (Fin k) ℂ), H.PosDef → Gᴴ * H * G = H →
  ∀ μ : ℂ, G.charpoly.IsRoot μ → ‖μ‖ = 1

def StepB : Prop := ∀ (E : Type) [Field E] [NumberField E] (p : E[X]), p.Monic → (∀ i, IsIntegral ℤ (p.coeff i)) →
  (∀ (φ : E →+* ℂ) (μ : ℂ), (p.map φ).IsRoot μ → ‖μ‖ = 1) →
  ∀ (φ₀ : E →+* ℂ) (μ : ℂ), (p.map φ₀).IsRoot μ → ∃ m : ℕ, 0 < m ∧ μ ^ m = 1

def StepC : Prop := ∀ (k : ℕ) (H G : Matrix (Fin k) (Fin k) ℂ), H.PosDef → Gᴴ * H * G = H →
  ∀ n : ℕ, (∀ μ ∈ G.charpoly.roots, μ ^ n = 1) → G ^ n = 1

/- English proof (translation)
Establish `h` using `congrArg (fun M => M.map φ) hγ`. Simplify using `only [Matrix.map_mul] at h`. Use `h using 3` and compare the differences between its conclusion and the goal. Use extensionality with `i j`. Simplify using `[Matrix.conjTranspose_apply, hc, Complex.star_def]`.
-/
theorem map_relation {E : Type} [Field E] (c : E →+* E) (φ : E →+* ℂ)
    (hc : ∀ x : E, φ (c x) = (starRingEnd ℂ) (φ x)) {k : ℕ} (J γ : Matrix (Fin k) (Fin k) E)
    (hγ : (γ.map c)ᵀ * J * γ = J) : (γ.map φ)ᴴ * J.map φ * γ.map φ = J.map φ := by
  have h := congrArg (fun M => M.map φ) hγ
  simp only [Matrix.map_mul] at h
  convert h using 3
  ext i j
  simp [Matrix.conjTranspose_apply, hc, Complex.star_def]

/- English proof (translation)
Introduce `E _ _ c hc k J γ hJ hγ hint`. Take `⟨φ₀⟩ : Nonempty (E →+* ℂ)` from `inferInstance`. Establish `hrel : ∀ φ : E →+* ℂ, (γ.map φ)ᴴ * J.map φ * γ.map φ = J.map φ` using `fun φ => map_relation c φ (hc φ) J γ hγ`. Establish `hnorm : ∀ (φ : E →+* ℂ) (μ : ℂ), (γ.charpoly.map φ).IsRoot μ → ‖μ‖ = 1`. Introduce `φ μ hμ`.

Rewrite `hμ` using `[← Matrix.charpoly_map]`. Break down `hJ φ with hpos | hneg` into its components or cases. Conclude with `hA k (J.map φ) (γ.map φ) hpos (hrel φ) μ hμ`. Use `hA k (-(J.map φ)) (γ.map φ) hneg ?_ μ hμ` and prove the remaining obligations. Rewrite using `[Matrix.mul_neg, Matrix.neg_mul, hrel φ]`.

Establish `hroot : ∀ μ : ℂ, (γ.charpoly.map φ₀).IsRoot μ → ∃ m : ℕ, 0 < m ∧ μ ^ m = 1` using `hB E γ.charpoly (Matrix.charpoly_monic γ) hint hnorm φ₀`. Set `m : ℂ → ℕ` to `fun μ => if h : (γ.charpoly.map φ₀).IsRoot μ then (hroot μ h).choose else 1`. Establish `hm : ∀ μ, 0 < m μ`. Introduce `μ`. Simplify using `only [m]`.

Use `split_ifs with h`. Conclude with `(hroot μ h).choose_spec.1`. Conclude with `one_pos`. Set `S` to `(γ.map φ₀).charpoly.roots.toFinset`. Choose the witnesses or unpack the hypotheses as in `⟨H, hH, hHrel⟩ : ∃ H : Matrix (Fin k) (Fin k) ℂ, H.PosDef ∧ (γ.map φ₀)ᴴ * H * γ.map φ₀ = H := by`.

Break down `hJ φ₀ with hpos | hneg` into its components or cases. Conclude with `⟨_, hpos, hrel φ₀⟩`. Use `⟨_, hneg, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.mul_neg, Matrix.neg_mul, hrel φ₀]`. Establish `hpow : (γ.map φ₀) ^ (∏ μ ∈ S, m μ) = 1`.

Apply `hC k H (γ.map φ₀) hH hHrel` to reduce the goal to its premises. Introduce `μ hμ`. Establish `hr : (γ.charpoly.map φ₀).IsRoot μ`. Rewrite using `[← Matrix.charpoly_map]`. Conclude with `Polynomial.isRoot_of_mem_roots hμ`.

Take `⟨t, ht⟩ : m μ ∣ ∏ ν ∈ S, m ν` from `Finset.dvd_prod_of_mem m (Multiset.mem_toFinset.mpr hμ)`. Establish `hmμ : μ ^ m μ = 1`. Simplify using `only [m, dif_pos hr]`. Conclude with `(hroot μ hr).choose_spec.2`. Rewrite using `[ht, pow_mul, hmμ, one_pow]`.

Use `⟨∏ μ ∈ S, m μ, Finset.prod_pos fun μ _ => hm μ, ?_⟩` and prove the remaining obligations. Apply `Matrix.map_injective φ₀.injective` to reduce the goal to its premises. Use `show (γ ^ (∏ μ ∈ S, m μ)).map φ₀ = (1 : Matrix (Fin k) (Fin k) E).map φ₀`. Rewrite using `[Matrix.map_pow, hpow, Matrix.map_one _ (map_zero φ₀) (map_one φ₀)]`.
-/
theorem unitKron_of (hA : StepA) (hB : StepB) (hC : StepC) : PI.UnitKron := by
  intro E _ _ c hc k J γ hJ hγ hint
  obtain ⟨φ₀⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hrel : ∀ φ : E →+* ℂ, (γ.map φ)ᴴ * J.map φ * γ.map φ = J.map φ :=
    fun φ => map_relation c φ (hc φ) J γ hγ
  have hnorm : ∀ (φ : E →+* ℂ) (μ : ℂ), (γ.charpoly.map φ).IsRoot μ → ‖μ‖ = 1 := by
    intro φ μ hμ
    rw [← Matrix.charpoly_map] at hμ
    rcases hJ φ with hpos | hneg
    · exact hA k (J.map φ) (γ.map φ) hpos (hrel φ) μ hμ
    · refine hA k (-(J.map φ)) (γ.map φ) hneg ?_ μ hμ
      rw [Matrix.mul_neg, Matrix.neg_mul, hrel φ]
  have hroot : ∀ μ : ℂ, (γ.charpoly.map φ₀).IsRoot μ → ∃ m : ℕ, 0 < m ∧ μ ^ m = 1 :=
    hB E γ.charpoly (Matrix.charpoly_monic γ) hint hnorm φ₀
  classical
  let m : ℂ → ℕ := fun μ => if h : (γ.charpoly.map φ₀).IsRoot μ then (hroot μ h).choose else 1
  have hm : ∀ μ, 0 < m μ := by
    intro μ
    simp only [m]
    split_ifs with h
    · exact (hroot μ h).choose_spec.1
    · exact one_pos
  let S := (γ.map φ₀).charpoly.roots.toFinset
  obtain ⟨H, hH, hHrel⟩ : ∃ H : Matrix (Fin k) (Fin k) ℂ, H.PosDef ∧ (γ.map φ₀)ᴴ * H * γ.map φ₀ = H := by
    rcases hJ φ₀ with hpos | hneg
    · exact ⟨_, hpos, hrel φ₀⟩
    · refine ⟨_, hneg, ?_⟩
      rw [Matrix.mul_neg, Matrix.neg_mul, hrel φ₀]
  have hpow : (γ.map φ₀) ^ (∏ μ ∈ S, m μ) = 1 := by
    apply hC k H (γ.map φ₀) hH hHrel
    intro μ hμ
    have hr : (γ.charpoly.map φ₀).IsRoot μ := by
      rw [← Matrix.charpoly_map]
      exact Polynomial.isRoot_of_mem_roots hμ
    obtain ⟨t, ht⟩ : m μ ∣ ∏ ν ∈ S, m ν := Finset.dvd_prod_of_mem m (Multiset.mem_toFinset.mpr hμ)
    have hmμ : μ ^ m μ = 1 := by
      simp only [m, dif_pos hr]
      exact (hroot μ hr).choose_spec.2
    rw [ht, pow_mul, hmμ, one_pow]
  refine ⟨∏ μ ∈ S, m μ, Finset.prod_pos fun μ _ => hm μ, ?_⟩
  apply Matrix.map_injective φ₀.injective
  show (γ ^ (∏ μ ∈ S, m μ)).map φ₀ = (1 : Matrix (Fin k) (Fin k) E).map φ₀
  rw [Matrix.map_pow, hpow, Matrix.map_one _ (map_zero φ₀) (map_one φ₀)]

end PI.UnitKronW
