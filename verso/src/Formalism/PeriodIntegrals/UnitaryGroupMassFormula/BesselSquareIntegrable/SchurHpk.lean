import Mathlib
import Formalism.PeriodIntegrals.BesselL2FixAtZero
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BesselSquareIntegrable.SchurHpkAlt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FormalDegreeSquareIntegrable.Closed

noncomputable section

namespace PI.UnitaryGroupMassFormula.BesselL2FixAtZero

open MeasureTheory Matrix Topology
open scoped InnerProductSpace ENNReal
open PI.UpqRep PI.BesselL2FixAtZero

section Transport

variable {n : ℕ} (ε : Fin n → Bool) (P : Matrix (Fin n) (Fin n) ℂ)

def conjPrime₂ (g : UJ ε) : Fin n → Fin n → ℂ := Matrix.of.symm (P⁻¹ * toM g * P)

/- English proof (translation)
Establish `hdet : IsUnit P.det` using `(Matrix.isUnit_iff_isUnit_det P).mp hP`. Establish `h1 : P⁻¹ * P = 1` using `Matrix.nonsing_inv_mul P hdet`. Establish `h2 : P * P⁻¹ = 1` using `Matrix.mul_nonsing_inv P hdet`. Set `e : Matrix (Fin n) (Fin n) ℂ ≃ₜ (Fin n → Fin n → ℂ)` to `{ toFun := fun m => Matrix.of.symm (P⁻¹ * m * P) invFun := fun x => P * Matrix.of x * P⁻¹ left_inv := fun m => by show P * (P⁻¹ * m * P) * P⁻¹ = m`. Combine the equalities or inequalities in the displayed calculation.

Use `right_inv := fun x => by show P⁻¹ * (P * Matrix.of x * P⁻¹) * P = Matrix.of x`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`. Use `_ = Matrix.of x := by rw [h1, Matrix.one_mul, Matrix.mul_one]`. Use `continuous_toFun := by show Continuous fun m : Matrix (Fin n) (Fin n) ℂ => P⁻¹ * m * P`.

Conclude with `(continuous_const.matrix_mul continuous_id).matrix_mul continuous_const`. Use `continuous_invFun := by show Continuous fun x : Fin n → Fin n → ℂ => P * Matrix.of x * P⁻¹`. Conclude with `(continuous_const.matrix_mul continuous_id).matrix_mul continuous_const }`. Conclude with `e.isClosedEmbedding.comp (isClosedEmbeddingMatrix n ε).1`.
-/
lemma conjP_isClosedEmbedding (hP : IsUnit P) : IsClosedEmbedding (conjPrime₂ ε P) := by
  have hdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP
  have h1 : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hdet
  have h2 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hdet
  let e : Matrix (Fin n) (Fin n) ℂ ≃ₜ (Fin n → Fin n → ℂ) :=
    { toFun := fun m => Matrix.of.symm (P⁻¹ * m * P)
      invFun := fun x => P * Matrix.of x * P⁻¹
      left_inv := fun m => by
        show P * (P⁻¹ * m * P) * P⁻¹ = m
        calc P * (P⁻¹ * m * P) * P⁻¹ = (P * P⁻¹) * m * (P * P⁻¹) := by simp only [Matrix.mul_assoc]
          _ = m := by rw [h2, Matrix.one_mul, Matrix.mul_one]
      right_inv := fun x => by
        show P⁻¹ * (P * Matrix.of x * P⁻¹) * P = Matrix.of x
        calc P⁻¹ * (P * Matrix.of x * P⁻¹) * P = (P⁻¹ * P) * Matrix.of x * (P⁻¹ * P) := by
              simp only [Matrix.mul_assoc]
          _ = Matrix.of x := by rw [h1, Matrix.one_mul, Matrix.mul_one]
      continuous_toFun := by
        show Continuous fun m : Matrix (Fin n) (Fin n) ℂ => P⁻¹ * m * P
        exact (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
      continuous_invFun := by
        show Continuous fun x : Fin n → Fin n → ℂ => P * Matrix.of x * P⁻¹
        exact (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const }
  exact e.isClosedEmbedding.comp (isClosedEmbeddingMatrix n ε).1

/- English proof (translation)
The claim follows from `(conjP_isClosedEmbedding ε P hP).measurableEmbedding`.
-/
lemma conjP_measurableEmbedding (hP : IsUnit P) : MeasurableEmbedding (conjPrime₂ ε P) :=
  (conjP_isClosedEmbedding ε P hP).measurableEmbedding

/- English proof (translation)
Establish `hdet : IsUnit P.det` using `(Matrix.isUnit_iff_isUnit_det P).mp hP`. Establish `h1 : P⁻¹ * P = 1` using `Matrix.nonsing_inv_mul P hdet`. Establish `h2 : P * P⁻¹ = 1` using `Matrix.mul_nonsing_inv P hdet`. Establish `hE` using `conjP_measurableEmbedding ε P hP`. Use `set ψ := conjPrime₂ ε P with hψdef`.

Establish `hrange : {x : Fin n → Fin n → ℂ | Matrix.of x ∈ PI.UpqRep.UH (Pᴴ * Jm ε * P)} ⊆ Set.range ψ`. Introduce `x hx`. Establish `hx' : (Matrix.of x)ᴴ * (Pᴴ * Jm ε * P) * Matrix.of x = Pᴴ * Jm ε * P` using `hx`. Establish `hin : inUJ ε (P * Matrix.of x * P⁻¹)` using `by show (P * Matrix.of x * P⁻¹)ᴴ * Jm ε * (P * Matrix.of x * P⁻¹) = Jm ε`. Combine the equalities or inequalities in the displayed calculation.

Simplify using `only [Matrix.conjTranspose_mul, Matrix.mul_assoc]`. Use `_ = (P⁻¹)ᴴ * (Pᴴ * Jm ε * P) * P⁻¹ := by rw [hx']`. Use `_ = (P * P⁻¹)ᴴ * Jm ε * (P * P⁻¹) := by`. Simplify using `only [Matrix.conjTranspose_mul, Matrix.mul_assoc]`. Use `_ = Jm ε := by rw [h2]; simp`.

Establish `hr` using `(isClosedEmbeddingMatrix n ε).2`. Establish `hmem : P * Matrix.of x * P⁻¹ ∈ Set.range (fun g : UJ ε => ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ))`. Rewrite using `[hr]`. Conclude with `hin`. Take `⟨g, hg⟩` from `hmem`.

Use `⟨g, ?_⟩` and prove the remaining obligations. Use `show Matrix.of.symm (P⁻¹ * toM g * P) = x`. Establish `hg' : toM g = P * Matrix.of x * P⁻¹` using `hg`. Rewrite using `[hg']`. Combine the equalities or inequalities in the displayed calculation.

Establish `hinto : ∀ g : UJ ε, P⁻¹ * toM g * P ∈ PI.UpqRep.UH (Pᴴ * Jm ε * P)`. Introduce `g`. Establish `hg : (toM g)ᴴ * Jm ε * toM g = Jm ε` using `g.2`. Use `show (P⁻¹ * toM g * P)ᴴ * (Pᴴ * Jm ε * P) * (P⁻¹ * toM g * P) = Pᴴ * Jm ε * P`. Establish `hPP : (P⁻¹)ᴴ * Pᴴ = 1` using `by rw [← Matrix.conjTranspose_mul, h2, Matrix.conjTranspose_one]`.

Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.conjTranspose_mul, Matrix.mul_assoc]`. Use `_ = Pᴴ * ((toM g)ᴴ * Jm ε * toM g) * P := by`. Rewrite using `[hPP, h2]`. Simplify using `only [Matrix.mul_one, Matrix.mul_assoc]`.

Use `_ = Pᴴ * Jm ε * P := by rw [hg]`. Use `set ν := μ.comap ψ with hνdef`. Establish `hmapν : ν.map ψ = μ`. Rewrite using `[hνdef, hE.map_comap]`. Apply `Measure.restrict_eq_self_of_ae_mem` to reduce the goal to its premises.

Rewrite using `[ae_iff]`. Use `measure_mono_null ?_ hconc` and prove the remaining obligations. Introduce `x hx`. Assume the negation of the conclusion as `hc`. Establish `hc' : Matrix.of x ∈ PI.UpqRep.UH (Pᴴ * Jm ε * P)`.

Assume the negation of the conclusion as `h'`. Conclude with `hc h'`. Conclude with `hx (hrange hc')`. Establish `hσν : SigmaFinite ν` using `SigmaFinite.of_map ν hE.measurable.aemeasurable (by rw [hmapν]; infer_instance)`. Establish `hinj : ∀ a b : Measure (UJ ε), a.map ψ = b.map ψ → a = b`.

Introduce `a b hab`. Rewrite using `[← hE.comap_map a, ← hE.comap_map b, hab]`. Establish `hleft : ν.IsMulLeftInvariant`. Use `⟨fun g => ?_⟩` and prove the remaining obligations. Apply `hinj` to reduce the goal to its premises.

Establish `hcomp : ψ ∘ (fun h : UJ ε => g * h) = (fun x => Matrix.of.symm ((P⁻¹ * toM g * P) * Matrix.of x)) ∘ ψ`. Use function extensionality and compare the values at `h`. Use `show Matrix.of.symm (P⁻¹ * toM (g * h) * P) = Matrix.of.symm ((P⁻¹ * toM g * P) * (P⁻¹ * toM h * P))`. Use `congr 1`. Use `show P⁻¹ * (toM g * toM h) * P = (P⁻¹ * toM g * P) * (P⁻¹ * toM h * P)`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[h2, Matrix.mul_one]`. Simplify using `only [Matrix.mul_assoc]`. Use `_ = (P⁻¹ * toM g * P) * (P⁻¹ * toM h * P) := by simp only [Matrix.mul_assoc]`. Establish `hmul : Measurable (fun h : UJ ε => g * h)` using `measurable_const_mul g`.

Establish `hlm : Measurable (fun x : Fin n → Fin n → ℂ => Matrix.of.symm ((P⁻¹ * toM g * P) * Matrix.of x))`. Apply `Continuous.measurable` to reduce the goal to its premises. Use `show Continuous fun x : Fin n → Fin n → ℂ => (P⁻¹ * toM g * P) * Matrix.of x`. Conclude with `continuous_const.matrix_mul continuous_id`. Rewrite using `[Measure.map_map hE.measurable hmul, hcomp, ← Measure.map_map hlm hE.measurable, hmapν]`.

Conclude with `hinv _ (hinto g)`. Take `⟨K, hK, hKn⟩` from `exists_compact_mem_nhds (1 : UJ ε)`. Establish `hK0 : muG ε K ≠ 0` using `(Measure.measure_pos_of_mem_nhds (muG ε) hKn).ne'`. Establish `hKt : muG ε K ≠ ∞` using `hK.measure_lt_top.ne`. Establish `heq` using `measure_eq_div_smul ν (muG ε) hK0 hKt`.

Use `set c := ν K / muG ε K with hc`. Establish `hcne0 : c ≠ 0`. Introduce `h`. Apply `h0` to reduce the goal to its premises. Rewrite using `[← hmapν, heq, h, zero_smul, Measure.map_zero]`.

Establish `hcnetop : c ≠ ∞`. Introduce `h`. Establish `hnull : ∀ i, muG ε (spanningSets ν i) = 0`. Introduce `i`. Establish `hlt` using `measure_spanningSets_lt_top ν i`.

Establish `hS : ν (spanningSets ν i) = (c • muG ε) (spanningSets ν i)` using `congrArg (fun m : Measure (UJ ε) => m (spanningSets ν i)) heq`. Rewrite `hlt` using `[hS, Measure.smul_apply, smul_eq_mul, h]`. Assume the negation of the conclusion as `hne`. Rewrite `hlt` using `[ENNReal.top_mul hne]`. Conclude with `lt_irrefl _ hlt`.

Establish `: muG ε Set.univ = 0`. Rewrite using `[← iUnion_spanningSets ν]`. Conclude with `measure_iUnion_null hnull`. Establish `hne : muG ε ≠ 0` using `NeZero.ne _`. Conclude with `hne (Measure.measure_univ_eq_zero.mp this)`.

Conclude with `⟨c, hcne0, hcnetop, by rw [← hmapν, ← heq]⟩`.
-/
theorem haar_transport (hP : IsUnit P) (μ : Measure (Fin n → Fin n → ℂ)) [SigmaFinite μ] (h0 : μ ≠ 0)
    (hconc : μ {x | Matrix.of x ∉ PI.UpqRep.UH (Pᴴ * Jm ε * P)} = 0)
    (hinv : ∀ s ∈ PI.UpqRep.UH (Pᴴ * Jm ε * P), μ.map (fun x => Matrix.of.symm (s * Matrix.of x)) = μ) :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ∞ ∧ μ = (c • muG ε).map (conjPrime₂ ε P) := by
  have hdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP
  have h1 : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hdet
  have h2 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hdet
  have hE := conjP_measurableEmbedding ε P hP
  set ψ := conjPrime₂ ε P with hψdef

  have hrange : {x : Fin n → Fin n → ℂ | Matrix.of x ∈ PI.UpqRep.UH (Pᴴ * Jm ε * P)} ⊆ Set.range ψ := by
    intro x hx
    have hx' : (Matrix.of x)ᴴ * (Pᴴ * Jm ε * P) * Matrix.of x = Pᴴ * Jm ε * P := hx
    have hin : inUJ ε (P * Matrix.of x * P⁻¹) := by
      show (P * Matrix.of x * P⁻¹)ᴴ * Jm ε * (P * Matrix.of x * P⁻¹) = Jm ε
      calc (P * Matrix.of x * P⁻¹)ᴴ * Jm ε * (P * Matrix.of x * P⁻¹)
          = (P⁻¹)ᴴ * ((Matrix.of x)ᴴ * (Pᴴ * Jm ε * P) * Matrix.of x) * P⁻¹ := by
            simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
        _ = (P⁻¹)ᴴ * (Pᴴ * Jm ε * P) * P⁻¹ := by rw [hx']
        _ = (P * P⁻¹)ᴴ * Jm ε * (P * P⁻¹) := by
            simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
        _ = Jm ε := by rw [h2]; simp
    have hr := (isClosedEmbeddingMatrix n ε).2
    have hmem : P * Matrix.of x * P⁻¹ ∈
        Set.range (fun g : UJ ε => ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)) := by
      rw [hr]; exact hin
    obtain ⟨g, hg⟩ := hmem
    refine ⟨g, ?_⟩
    show Matrix.of.symm (P⁻¹ * toM g * P) = x
    have hg' : toM g = P * Matrix.of x * P⁻¹ := hg
    rw [hg']
    calc Matrix.of.symm (P⁻¹ * (P * Matrix.of x * P⁻¹) * P)
        = Matrix.of.symm ((P⁻¹ * P) * Matrix.of x * (P⁻¹ * P)) := by simp only [Matrix.mul_assoc]
      _ = x := by rw [h1, Matrix.one_mul, Matrix.mul_one]; rfl

  have hinto : ∀ g : UJ ε, P⁻¹ * toM g * P ∈ PI.UpqRep.UH (Pᴴ * Jm ε * P) := by
    intro g
    have hg : (toM g)ᴴ * Jm ε * toM g = Jm ε := g.2
    show (P⁻¹ * toM g * P)ᴴ * (Pᴴ * Jm ε * P) * (P⁻¹ * toM g * P) = Pᴴ * Jm ε * P
    have hPP : (P⁻¹)ᴴ * Pᴴ = 1 := by rw [← Matrix.conjTranspose_mul, h2, Matrix.conjTranspose_one]
    calc (P⁻¹ * toM g * P)ᴴ * (Pᴴ * Jm ε * P) * (P⁻¹ * toM g * P)
        = Pᴴ * (toM g)ᴴ * ((P⁻¹)ᴴ * Pᴴ) * Jm ε * (P * P⁻¹) * toM g * P := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Pᴴ * ((toM g)ᴴ * Jm ε * toM g) * P := by
          rw [hPP, h2]; simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = Pᴴ * Jm ε * P := by rw [hg]

  set ν := μ.comap ψ with hνdef
  have hmapν : ν.map ψ = μ := by
    rw [hνdef, hE.map_comap]
    apply Measure.restrict_eq_self_of_ae_mem
    rw [ae_iff]
    refine measure_mono_null ?_ hconc
    intro x hx
    by_contra hc
    have hc' : Matrix.of x ∈ PI.UpqRep.UH (Pᴴ * Jm ε * P) := by
      by_contra h'
      exact hc h'
    exact hx (hrange hc')
  have hσν : SigmaFinite ν := SigmaFinite.of_map ν hE.measurable.aemeasurable (by rw [hmapν]; infer_instance)
  have hinj : ∀ a b : Measure (UJ ε), a.map ψ = b.map ψ → a = b := by
    intro a b hab
    rw [← hE.comap_map a, ← hE.comap_map b, hab]
  have hleft : ν.IsMulLeftInvariant := by
    refine ⟨fun g => ?_⟩
    apply hinj
    have hcomp : ψ ∘ (fun h : UJ ε => g * h) =
        (fun x => Matrix.of.symm ((P⁻¹ * toM g * P) * Matrix.of x)) ∘ ψ := by
      funext h
      show Matrix.of.symm (P⁻¹ * toM (g * h) * P) =
        Matrix.of.symm ((P⁻¹ * toM g * P) * (P⁻¹ * toM h * P))
      congr 1
      show P⁻¹ * (toM g * toM h) * P = (P⁻¹ * toM g * P) * (P⁻¹ * toM h * P)
      calc P⁻¹ * (toM g * toM h) * P = P⁻¹ * toM g * (P * P⁻¹) * toM h * P := by
            rw [h2, Matrix.mul_one]; simp only [Matrix.mul_assoc]
        _ = (P⁻¹ * toM g * P) * (P⁻¹ * toM h * P) := by simp only [Matrix.mul_assoc]
    have hmul : Measurable (fun h : UJ ε => g * h) := measurable_const_mul g
    have hlm : Measurable (fun x : Fin n → Fin n → ℂ => Matrix.of.symm ((P⁻¹ * toM g * P) * Matrix.of x)) := by
      apply Continuous.measurable
      show Continuous fun x : Fin n → Fin n → ℂ => (P⁻¹ * toM g * P) * Matrix.of x
      exact continuous_const.matrix_mul continuous_id
    rw [Measure.map_map hE.measurable hmul, hcomp, ← Measure.map_map hlm hE.measurable, hmapν]
    exact hinv _ (hinto g)

  obtain ⟨K, hK, hKn⟩ := exists_compact_mem_nhds (1 : UJ ε)
  have hK0 : muG ε K ≠ 0 := (Measure.measure_pos_of_mem_nhds (muG ε) hKn).ne'
  have hKt : muG ε K ≠ ∞ := hK.measure_lt_top.ne
  have heq := measure_eq_div_smul ν (muG ε) hK0 hKt
  set c := ν K / muG ε K with hc
  have hcne0 : c ≠ 0 := by
    intro h
    apply h0
    rw [← hmapν, heq, h, zero_smul, Measure.map_zero]
  have hcnetop : c ≠ ∞ := by
    intro h
    have hnull : ∀ i, muG ε (spanningSets ν i) = 0 := by
      intro i
      have hlt := measure_spanningSets_lt_top ν i
      have hS : ν (spanningSets ν i) = (c • muG ε) (spanningSets ν i) :=
        congrArg (fun m : Measure (UJ ε) => m (spanningSets ν i)) heq
      rw [hS, Measure.smul_apply, smul_eq_mul, h] at hlt
      by_contra hne
      rw [ENNReal.top_mul hne] at hlt
      exact lt_irrefl _ hlt
    have : muG ε Set.univ = 0 := by
      rw [← iUnion_spanningSets ν]
      exact measure_iUnion_null hnull
    have hne : muG ε ≠ 0 := NeZero.ne _
    exact hne (Measure.measure_univ_eq_zero.mp this)
  exact ⟨c, hcne0, hcnetop, by rw [← hmapν, ← heq]⟩

end Transport

end PI.UnitaryGroupMassFormula.BesselL2FixAtZero
