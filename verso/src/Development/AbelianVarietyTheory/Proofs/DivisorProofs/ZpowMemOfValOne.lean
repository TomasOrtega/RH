import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisOfPolarized

noncomputable section

namespace GlobalTheory.DoubleCosetDivisors

open Matrix

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

/- English proof (translation)
Apply `hO` to reduce the goal to its premises. Rewrite using `[map_zpow₀, hu, _root_.one_zpow]`.
-/
theorem zpow_mem_of_val_one {O : Subring L}
    (hO : ∀ x : L, (Valued.v : L → WithZero (Multiplicative ℤ)) x ≤ 1 → x ∈ O)
    {u : L} (hu : (Valued.v : L → WithZero (Multiplicative ℤ)) u = 1) (k : ℤ) : u ^ k ∈ O := by
  apply hO
  rw [map_zpow₀, hu, _root_.one_zpow]

/- English proof (translation)
Establish `hu0 : u ≠ 0`. Introduce `h`. Rewrite `hu` using `[h, map_zero]`. Conclude with `zero_ne_one hu`. Set `Uo : GL (Fin n) O` to `{ val := Matrix.diagonal (fun i => ⟨u ^ e i, zpow_mem_of_val_one hO hu (e i)⟩) inv := Matrix.diagonal (fun i => ⟨u ^ (-e i), zpow_mem_of_val_one hO hu (-e i)⟩) val_inv := by`.

Rewrite using `[Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `[mul_inv_cancel₀ (zpow_ne_zero _ hu0)]`.

Use `inv_val := by`. Rewrite using `[Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Apply `Subtype.ext` to reduce the goal to its premises.

Simplify using `[inv_mul_cancel₀ (zpow_ne_zero _ hu0)] }`. Use `⟨Formalism.UG.bc (n := Fin n) O.subtype Uo, ⟨Uo, rfl⟩, ?_⟩` and prove the remaining obligations. Use extensionality with `i j`. Simplify using `[Formalism.UG.bc, Uo, Matrix.diagonal_apply]`.
-/
theorem diag_mem {n : ℕ} {O : Subring L}
    (hO : ∀ x : L, (Valued.v : L → WithZero (Multiplicative ℤ)) x ≤ 1 → x ∈ O)
    {u : L} (hu : (Valued.v : L → WithZero (Multiplicative ℤ)) u = 1) (e : Fin n → ℤ) :
    ∃ U ∈ Formalism.UG.GLint (Fin n) O, (U : Matrix (Fin n) (Fin n) L) = Matrix.diagonal (fun i => u ^ e i) := by
  have hu0 : u ≠ 0 := by
    intro h; rw [h, map_zero] at hu; exact zero_ne_one hu
  let Uo : GL (Fin n) O :=
    { val := Matrix.diagonal (fun i => ⟨u ^ e i, zpow_mem_of_val_one hO hu (e i)⟩)
      inv := Matrix.diagonal (fun i => ⟨u ^ (-e i), zpow_mem_of_val_one hO hu (-e i)⟩)
      val_inv := by
        rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
        congr 1; funext i; apply Subtype.ext
        simp [mul_inv_cancel₀ (zpow_ne_zero _ hu0)]
      inv_val := by
        rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
        congr 1; funext i; apply Subtype.ext
        simp [inv_mul_cancel₀ (zpow_ne_zero _ hu0)] }
  refine ⟨Formalism.UG.bc (n := Fin n) O.subtype Uo, ⟨Uo, rfl⟩, ?_⟩
  ext i j
  simp [Formalism.UG.bc, Uo, Matrix.diagonal_apply]

/- English proof (translation)
Take `⟨ϖ, hϖ, a1, ha1, b1, hb1, hg⟩` from `hg`. Take `⟨ϖ', hϖ', a2, ha2, b2, hb2, hs⟩` from `hs`. Establish `hne : ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) ≠ 0` using `WithZero.coe_ne_zero`. Establish `h0' : ϖ' ≠ 0`. Introduce `h`.

Rewrite `hϖ'` using `[h, map_zero]`. Conclude with `hne hϖ'.symm`. Establish `hu : (Valued.v : L → WithZero (Multiplicative ℤ)) (ϖ / ϖ') = 1`. Rewrite using `[map_div₀, hϖ, hϖ', div_self hne]`. Take `⟨U, hU, hUe⟩` from `diag_mem hO hu (fun i : Fin n => d.getD i 0)`.

Establish `hD : Matrix.diagonal (fun i : Fin n => ϖ ^ d.getD i 0) = (U : Matrix (Fin n) (Fin n) L) * Matrix.diagonal (fun i : Fin n => ϖ' ^ d.getD i 0)`. Rewrite using `[hUe, Matrix.diagonal_mul_diagonal]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Rewrite using `[← mul_zpow, div_mul_cancel₀ _ h0']`.

Use `⟨⟨a1 * U * a2⁻¹, Subgroup.mul_mem _ (Subgroup.mul_mem _ ha1 hU) (Subgroup.inv_mem _ ha2)⟩, ⟨b2⁻¹ * b1, Subgroup.mul_mem _ (Subgroup.inv_mem _ hb2) hb1⟩, ?_⟩` and prove the remaining obligations. Apply `Units.ext` to reduce the goal to its premises. Establish `e1 : ((a2⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * (a2 : Matrix (Fin n) (Fin n) L) = 1` using `Units.inv_mul a2`. Establish `e2 : (b2 : Matrix (Fin n) (Fin n) L) * ((b2⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = 1` using `Units.mul_inv b2`. Simplify using `only [Units.val_mul]`.

Rewrite using `[hg, hs, hD]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[e1, e2]`. Simplify using `only [Matrix.mul_one, Matrix.mul_assoc]`. Use `_ = _ := by simp only [Matrix.mul_assoc]`.
-/
theorem sameDiv_doubleCoset {n : ℕ} {O : Subring L}
    (hO : ∀ x : L, (Valued.v : L → WithZero (Multiplicative ℤ)) x ≤ 1 → x ∈ O) {d : List ℤ} {g s : GL (Fin n) L}
    (hg : GlobalTheory.SphPar.HasDiv O d g) (hs : GlobalTheory.SphPar.HasDiv O d s) :
    ∃ (a : ↥(Formalism.UG.GLint (Fin n) O)) (b : ↥(Formalism.UG.GLint (Fin n) O)),
      g = (↑a : GL (Fin n) L) * s * (↑b : GL (Fin n) L) := by
  obtain ⟨ϖ, hϖ, a1, ha1, b1, hb1, hg⟩ := hg
  obtain ⟨ϖ', hϖ', a2, ha2, b2, hb2, hs⟩ := hs
  have hne : ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) ≠ 0 :=
    WithZero.coe_ne_zero
  have h0' : ϖ' ≠ 0 := by
    intro h; rw [h, map_zero] at hϖ'; exact hne hϖ'.symm
  have hu : (Valued.v : L → WithZero (Multiplicative ℤ)) (ϖ / ϖ') = 1 := by
    rw [map_div₀, hϖ, hϖ', div_self hne]
  obtain ⟨U, hU, hUe⟩ := diag_mem hO hu (fun i : Fin n => d.getD i 0)
  have hD : Matrix.diagonal (fun i : Fin n => ϖ ^ d.getD i 0) =
      (U : Matrix (Fin n) (Fin n) L) * Matrix.diagonal (fun i : Fin n => ϖ' ^ d.getD i 0) := by
    rw [hUe, Matrix.diagonal_mul_diagonal]
    congr 1; funext i
    rw [← mul_zpow, div_mul_cancel₀ _ h0']
  refine ⟨⟨a1 * U * a2⁻¹, Subgroup.mul_mem _ (Subgroup.mul_mem _ ha1 hU) (Subgroup.inv_mem _ ha2)⟩,
    ⟨b2⁻¹ * b1, Subgroup.mul_mem _ (Subgroup.inv_mem _ hb2) hb1⟩, ?_⟩
  apply Units.ext
  have e1 : ((a2⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * (a2 : Matrix (Fin n) (Fin n) L) = 1 := Units.inv_mul a2
  have e2 : (b2 : Matrix (Fin n) (Fin n) L) * ((b2⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = 1 := Units.mul_inv b2
  simp only [Units.val_mul]
  rw [hg, hs, hD]
  calc (a1 : Matrix (Fin n) (Fin n) L) * ((U : Matrix (Fin n) (Fin n) L) * Matrix.diagonal (fun i : Fin n => ϖ' ^ d.getD i 0)) * (b1 : Matrix (Fin n) (Fin n) L)
      = (a1 : Matrix (Fin n) (Fin n) L) * (U : Matrix (Fin n) (Fin n) L) * (((a2⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * (a2 : Matrix (Fin n) (Fin n) L))
          * Matrix.diagonal (fun i : Fin n => ϖ' ^ d.getD i 0) * ((b2 : Matrix (Fin n) (Fin n) L) * ((b2⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) * (b1 : Matrix (Fin n) (Fin n) L) := by
        rw [e1, e2]; simp only [Matrix.mul_one, Matrix.mul_assoc]
    _ = _ := by simp only [Matrix.mul_assoc]

/- English proof (translation)
Introduce `hO _ _ _ hg hs` and use `sameDiv_doubleCoset hO hg hs`.
-/
theorem main : ∀ {L : Type} [inst : Field L] [inst_1 : Valued L (WithZero (Multiplicative ℤ))] {n : ℕ} {O : Subring L}, (∀ (x : L), (Valued.v : L → WithZero (Multiplicative ℤ)) x ≤ (1 : WithZero (Multiplicative ℤ)) → x ∈ O) → ∀ {d : List ℤ} {g s : GL (Fin n) L}, GlobalTheory.SphPar.HasDiv O d g → GlobalTheory.SphPar.HasDiv O d s → ∃ (a : ↥(Formalism.UG.GLint (Fin n) O)) (b : ↥(Formalism.UG.GLint (Fin n) O)), g = (↑a : GL (Fin n) L) * s * (↑b : GL (Fin n) L) :=
  fun hO _ _ _ hg hs => sameDiv_doubleCoset hO hg hs

end GlobalTheory.DoubleCosetDivisors
