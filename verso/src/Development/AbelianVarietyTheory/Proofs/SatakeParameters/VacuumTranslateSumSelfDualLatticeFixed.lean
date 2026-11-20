import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SelfDualOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeModelVacuumTranslateClassesIndependent
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MulSelfEqOneIffOfLinearOrderedCommGroupWithZero
open Matrix

namespace GlobalTheory.Hk3.HoweG

/- English proof (translation)
Introduce `L _ _ _ _ ϖ σ q δ n n' JS JT ψ M _ _ ρ ω hP s hvac a hSD Z hZform hZdist hZcov u hu`. Take `⟨hU, hodd, hSint, hTint, -, -, hδ, hpsi, -, -, hρ, -, -, -⟩` from `hP`. Establish `hσσ` using `hU.1`. Establish `hσv` using `hU.2.1`. Establish `h2 : Valued.v (2 : L) = 1` using `GlobalTheory.Hk3.Inh.v_two hU hodd`.

Use `set A : Matrix (Fin n) (Fin n) L := ((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) with hA`. Use `set P : Matrix (Fin n) (Fin n) L := ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) with hPdef`. Establish `hloc : ∀ w w' : Matrix (Fin n') (Fin n) L, (∀ i j, w i j ∈ Formalism.UG.intL L) → (∀ i j, w' i j ∈ Formalism.UG.intL L) → locH σ δ JS JT (w * A) (w' * A) ∈ Formalism.UG.intL L`. Introduce `w w' hw hw'`. Establish `hw'σ : ∀ i j, (w'.map σ)ᵀ i j ∈ Formalism.UG.intL L`.

Introduce `i j`. Use `show Valued.v (σ (w' j i)) ≤ 1`. Rewrite using `[hσv]`. Conclude with `hw' j i`. Apply the tactic sequence `have hJT : ∀ i j, (JT : Matrix (Fin n') (Fin n') L) i j ∈ Formalism.UG.intL L := fun i j => glint_entry hTint i j`.

Establish `hB : ∀ i j, (A * P * (A.map σ)ᵀ) i j ∈ Formalism.UG.intL L` using `hSD.2`. Establish `hC : ∀ i j, ((w'.map σ)ᵀ * (JT : Matrix (Fin n') (Fin n') L) * w) i j ∈ Formalism.UG.intL L` using `matMul_int (matMul_int hw'σ hJT) hw`. Establish `e : locH σ δ JS JT (w * A) (w' * A) = δ * Matrix.trace ((A * P * (A.map σ)ᵀ) * ((w'.map σ)ᵀ * (JT : Matrix (Fin n') (Fin n') L) * w))`. Unfold `locH`. Use `congr 1`.

Rewrite using `[Matrix.map_mul, Matrix.transpose_mul]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`. Use `_ = Matrix.trace (A * (P * (A.map σ)ᵀ * (w'.map σ)ᵀ * (JT : Matrix (Fin n') (Fin n') L) * w)) := Matrix.trace_mul_comm _ _`. Use `_ = _ := by simp only [Matrix.mul_assoc]`.

Rewrite using `[e]`. Use `(Formalism.UG.intL L).mul_mem (le_of_eq hδ.1) ?_` and prove the remaining obligations. Unfold `Matrix.trace`. Conclude with `(Formalism.UG.intL L).sum_mem fun i _ => matMul_int hB hC i i`. Establish `hpair : ∀ w w' : Matrix (Fin n') (Fin n) L, (∀ i j, w i j ∈ Formalism.UG.intL L) → (∀ i j, w' i j ∈ Formalism.UG.intL L) → ψ ((locH σ δ JS JT (w * A) (w' * A) + σ (locH σ δ JS JT (w * A) (w' * A))) / 2) = 1`.

Introduce `w w' hw hw'`. Establish `hcI` using `hloc w w' hw hw'`. Establish `hσc : σ (locH σ δ JS JT (w * A) (w' * A)) ∈ Formalism.UG.intL L` using `by show Valued.v (σ _) ≤ 1`. Rewrite using `[hσv]`. Conclude with `hcI`.

Apply `hpsi` to reduce the goal to its premises. Rewrite using `[GlobalTheory.Hk3.mem_intL_iff, map_div₀, h2, div_one]`. Conclude with `(Formalism.UG.intL L).add_mem hcI hσc`. Rewrite using `[map_div₀, map_add, hσσ, map_ofNat]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hcomb : ∀ w w' : Matrix (Fin n') (Fin n) L, (∀ i j, w i j ∈ Formalism.UG.intL L) → (∀ i j, w' i j ∈ Formalism.UG.intL L) → ∀ t : M, ρ (w * A) (ρ (w' * A) t) = ρ (w * A + w' * A) t`. Introduce `w w' hw hw' t`. Use `congrArg (fun f => f t) (hρ (w * A) (w' * A))` as an intermediate fact. Simplify using `only [Module.End.mul_apply, LinearMap.smul_apply] at this`. Rewrite using `[this, hpair w w' hw hw', one_smul]`.

Establish `key : ∀ z ∈ Z, ∃ z' ∈ Z, ρ (u * A) (ρ z s) = ρ z' s ∧ (u * A + z) - z' ∈ GlobalTheory.Hk3.HoweDuality.intMat L n' n`. Introduce `z hz`. Take `⟨v, hv, rfl⟩` from `hZform z hz`. Establish `huv : ∀ i j, (u + v) i j ∈ Formalism.UG.intL L` using `fun i j => (Formalism.UG.intL L).add_mem (hu i j) (hv i j)`. Take `⟨z', hz', hdiff⟩` from `hZcov (u + v) huv`.

Take `⟨v', hv', rfl⟩` from `hZform z' hz'`. Use `⟨v' * A, hz', ?_, by rwa [← Matrix.add_mul]⟩` and prove the remaining obligations. Establish `hw : ∀ i j, (u + v - v') i j ∈ Formalism.UG.intL L` using `fun i j => (Formalism.UG.intL L).sub_mem (huv i j) (hv' i j)`. Establish `hl : ρ ((u + v - v') * A) s = s`. Apply `hvac` to reduce the goal to its premises.

Rewrite using `[Matrix.sub_mul]`. Conclude with `hdiff`. Rewrite using `[hcomb u v hu hv]`. Combine the equalities or inequalities in the displayed calculation. Use `congr 1`.

Rewrite using `[Matrix.sub_mul, Matrix.add_mul]`. Normalize the expressions using the abelian group laws. Use `_ = ρ (v' * A) (ρ ((u + v - v') * A) s) := (hcomb v' _ hv' hw s).symm`. Use `_ = ρ (v' * A) s := by rw [hl]`. Use `choose! f hfZ hf hfd using key`.

Rewrite using `[map_sum, Finset.sum_congr rfl hf]`. Establish `hinj : ∀ x ∈ Z, ∀ y ∈ Z, f x = f y → x = y`. Introduce `z1 h1 z2 h2 he`. Apply `hZdist z1 h1 z2 h2` to reduce the goal to its premises. Use `sub_mem (hfd z1 h1) (hfd z2 h2)` as an intermediate fact.

Rewrite `this` using `[he]`. Use `this using 1` and compare the differences between its conclusion and the goal. Normalize the expressions using the abelian group laws. Establish `himg : Z.image f = Z` using `Finset.eq_of_subset_of_card_le (fun x hx => by obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx; exact hfZ z hz) (by rw [Finset.card_image_of_injOn (fun x hx y hy h => hinj x hx y hy h)])`. Rewrite using `[← Finset.sum_image (f := fun z => ρ z s) hinj, himg]`.
-/
theorem vacuum_sum_selfDual_fixed : ∀ (L : Type) [Field L] [CharZero L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L)
    (n n' : ℕ) (JS : GL (Fin n) L) (JT : GL (Fin n') L) (ψ : AddChar L ℂ) (M : Type) [AddCommGroup M] [Module ℂ M]
    (ρ : Matrix (Fin n') (Fin n) L → Module.End ℂ M)
    (ω : Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L) × Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L) →* Module.End ℂ M),
    GlobalTheory.Hk3.LocPair ϖ σ q δ JS JT ψ ρ ω → ∀ s : M, GlobalTheory.Hk3.LocVac ρ s →
    ∀ a : GL (Fin n) L, GlobalTheory.Hk3.HoweG.SelfDual σ JS a → ∀ Z : Finset (Matrix (Fin n') (Fin n) L),
    (∀ z ∈ Z, ∃ u : Matrix (Fin n') (Fin n) L, (∀ i j, u i j ∈ Formalism.UG.intL L) ∧
      z = u * ((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) →
    (∀ z ∈ Z, ∀ z' ∈ Z, z - z' ∈ GlobalTheory.Hk3.HoweDuality.intMat L n' n → z = z') →
    (∀ u : Matrix (Fin n') (Fin n) L, (∀ i j, u i j ∈ Formalism.UG.intL L) →
      ∃ z ∈ Z, u * ((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) - z ∈ GlobalTheory.Hk3.HoweDuality.intMat L n' n) →
    ∀ u : Matrix (Fin n') (Fin n) L, (∀ i j, u i j ∈ Formalism.UG.intL L) →
      ρ (u * ((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) (∑ z ∈ Z, ρ z s) = ∑ z ∈ Z, ρ z s := by
  intro L _ _ _ _ ϖ σ q δ n n' JS JT ψ M _ _ ρ ω hP s hvac a hSD Z hZform hZdist hZcov u hu
  classical
  obtain ⟨hU, hodd, hSint, hTint, -, -, hδ, hpsi, -, -, hρ, -, -, -⟩ := hP
  have hσσ := hU.1
  have hσv := hU.2.1
  have h2 : Valued.v (2 : L) = 1 := GlobalTheory.Hk3.Inh.v_two hU hodd
  set A : Matrix (Fin n) (Fin n) L := ((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) with hA
  set P : Matrix (Fin n) (Fin n) L := ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) with hPdef

  have hloc : ∀ w w' : Matrix (Fin n') (Fin n) L, (∀ i j, w i j ∈ Formalism.UG.intL L) → (∀ i j, w' i j ∈ Formalism.UG.intL L) →
      locH σ δ JS JT (w * A) (w' * A) ∈ Formalism.UG.intL L := by
    intro w w' hw hw'
    have hw'σ : ∀ i j, (w'.map σ)ᵀ i j ∈ Formalism.UG.intL L := by
      intro i j
      show Valued.v (σ (w' j i)) ≤ 1
      rw [hσv]; exact hw' j i
    have hJT : ∀ i j, (JT : Matrix (Fin n') (Fin n') L) i j ∈ Formalism.UG.intL L := fun i j => glint_entry hTint i j
    have hB : ∀ i j, (A * P * (A.map σ)ᵀ) i j ∈ Formalism.UG.intL L := hSD.2
    have hC : ∀ i j, ((w'.map σ)ᵀ * (JT : Matrix (Fin n') (Fin n') L) * w) i j ∈ Formalism.UG.intL L :=
      matMul_int (matMul_int hw'σ hJT) hw
    have e : locH σ δ JS JT (w * A) (w' * A) =
        δ * Matrix.trace ((A * P * (A.map σ)ᵀ) * ((w'.map σ)ᵀ * (JT : Matrix (Fin n') (Fin n') L) * w)) := by
      unfold locH
      congr 1
      rw [Matrix.map_mul, Matrix.transpose_mul]
      calc Matrix.trace (P * ((A.map σ)ᵀ * (w'.map σ)ᵀ) * (JT : Matrix (Fin n') (Fin n') L) * (w * A))
          = Matrix.trace ((P * (A.map σ)ᵀ * (w'.map σ)ᵀ * (JT : Matrix (Fin n') (Fin n') L) * w) * A) := by
            simp only [Matrix.mul_assoc]
        _ = Matrix.trace (A * (P * (A.map σ)ᵀ * (w'.map σ)ᵀ * (JT : Matrix (Fin n') (Fin n') L) * w)) :=
            Matrix.trace_mul_comm _ _
        _ = _ := by simp only [Matrix.mul_assoc]
    rw [e]
    refine (Formalism.UG.intL L).mul_mem (le_of_eq hδ.1) ?_
    unfold Matrix.trace
    exact (Formalism.UG.intL L).sum_mem fun i _ => matMul_int hB hC i i

  have hpair : ∀ w w' : Matrix (Fin n') (Fin n) L, (∀ i j, w i j ∈ Formalism.UG.intL L) → (∀ i j, w' i j ∈ Formalism.UG.intL L) →
      ψ ((locH σ δ JS JT (w * A) (w' * A) + σ (locH σ δ JS JT (w * A) (w' * A))) / 2) = 1 := by
    intro w w' hw hw'
    have hcI := hloc w w' hw hw'
    have hσc : σ (locH σ δ JS JT (w * A) (w' * A)) ∈ Formalism.UG.intL L := by
      show Valued.v (σ _) ≤ 1
      rw [hσv]; exact hcI
    apply hpsi
    · rw [GlobalTheory.Hk3.mem_intL_iff, map_div₀, h2, div_one]
      exact (Formalism.UG.intL L).add_mem hcI hσc
    · rw [map_div₀, map_add, hσσ, map_ofNat]; ring
  have hcomb : ∀ w w' : Matrix (Fin n') (Fin n) L, (∀ i j, w i j ∈ Formalism.UG.intL L) → (∀ i j, w' i j ∈ Formalism.UG.intL L) →
      ∀ t : M, ρ (w * A) (ρ (w' * A) t) = ρ (w * A + w' * A) t := by
    intro w w' hw hw' t
    have := congrArg (fun f => f t) (hρ (w * A) (w' * A))
    simp only [Module.End.mul_apply, LinearMap.smul_apply] at this
    rw [this, hpair w w' hw hw', one_smul]
  have key : ∀ z ∈ Z, ∃ z' ∈ Z, ρ (u * A) (ρ z s) = ρ z' s ∧ (u * A + z) - z' ∈ GlobalTheory.Hk3.HoweDuality.intMat L n' n := by
    intro z hz
    obtain ⟨v, hv, rfl⟩ := hZform z hz
    have huv : ∀ i j, (u + v) i j ∈ Formalism.UG.intL L := fun i j => (Formalism.UG.intL L).add_mem (hu i j) (hv i j)
    obtain ⟨z', hz', hdiff⟩ := hZcov (u + v) huv
    obtain ⟨v', hv', rfl⟩ := hZform z' hz'
    refine ⟨v' * A, hz', ?_, by rwa [← Matrix.add_mul]⟩
    have hw : ∀ i j, (u + v - v') i j ∈ Formalism.UG.intL L := fun i j => (Formalism.UG.intL L).sub_mem (huv i j) (hv' i j)
    have hl : ρ ((u + v - v') * A) s = s := by
      apply hvac
      rw [Matrix.sub_mul]
      exact hdiff
    rw [hcomb u v hu hv]
    calc ρ (u * A + v * A) s = ρ (v' * A + (u + v - v') * A) s := by
          congr 1; rw [Matrix.sub_mul, Matrix.add_mul]; abel
      _ = ρ (v' * A) (ρ ((u + v - v') * A) s) := (hcomb v' _ hv' hw s).symm
      _ = ρ (v' * A) s := by rw [hl]
  choose! f hfZ hf hfd using key
  rw [map_sum, Finset.sum_congr rfl hf]
  have hinj : ∀ x ∈ Z, ∀ y ∈ Z, f x = f y → x = y := by
    intro z1 h1 z2 h2 he
    apply hZdist z1 h1 z2 h2
    have := sub_mem (hfd z1 h1) (hfd z2 h2)
    rw [he] at this
    convert this using 1; abel
  have himg : Z.image f = Z := Finset.eq_of_subset_of_card_le
    (fun x hx => by obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx; exact hfZ z hz)
    (by rw [Finset.card_image_of_injOn (fun x hx y hy h => hinj x hx y hy h)])
  rw [← Finset.sum_image (f := fun z => ρ z s) hinj, himg]

end GlobalTheory.Hk3.HoweG
