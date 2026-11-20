import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen

noncomputable section

open Formalism.UG Matrix GlobalTheory.SatakeWeyl GlobalTheory.InertZeta

namespace GlobalTheory.CompanionTheory.InertDual

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {N : ℕ}

/- English proof (translation)
Rewrite using `[Fin.ext_iff, Fin.val_rev]`. Use `i.isLt` as an intermediate fact. Use `j.isLt` as an intermediate fact. Apply the tactic sequence `constructor <;> intro h <;> omega`.
-/
theorem antiJ_iff (i j : Fin N) : i.val + j.val + 1 = N ↔ j = i.rev := by
  rw [Fin.ext_iff, Fin.val_rev]
  have := i.isLt
  have := j.isLt
  constructor <;> intro h <;> omega

/- English proof (translation)
Simplify using `[Matrix.mulVec, dotProduct, antiJ, antiJ_iff]`.
-/
theorem antiJ_mulVec (b : Fin N → L) (k : Fin N) : (antiJ L N *ᵥ b) k = b k.rev := by
  simp [Matrix.mulVec, dotProduct, antiJ, antiJ_iff]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [Matrix.mul_apply, antiJ, antiJ_iff, boole_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true, Fin.rev_rev, Matrix.one_apply]`. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality. Simplify using the standard rewrite rules.

Simplify using `[h, Ne.symm h]`.
-/
theorem antiJ_mul_self : antiJ L N * antiJ L N = 1 := by
  ext i j
  simp only [Matrix.mul_apply, antiJ, antiJ_iff, boole_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    Fin.rev_rev, Matrix.one_apply]
  by_cases h : i = j
  · subst h
    simp
  · simp [h, Ne.symm h]

/- English proof (translation)
Introduce `i j`. Simplify using `only [antiJ]`. Use `split_ifs`. Conclude with `one_mem _`. Conclude with `zero_mem _`.
-/
theorem isInt_antiJ : IsInt (antiJ L N) := by
  intro i j
  simp only [antiJ]
  split_ifs
  · exact one_mem _
  · exact zero_mem _

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[cT]`.
-/
theorem cT_add (σ : L →+* L) (A B : Matrix (Fin N) (Fin N) L) : cT σ (A + B) = cT σ A + cT σ B := by
  ext i j
  simp [cT]

/- English proof (translation)
Introduce `i j`. Establish `h : M j i ∈ intL L` using `hM j i`. Establish `hmem : ∀ x : L, x ∈ intL L ↔ Valued.v x ≤ 1` using `fun x => Valuation.mem_integer_iff _ _`. Simplify using `only [cT, Matrix.transpose_apply, Matrix.map_apply]`. Rewrite `h`, the goal using `[hmem]`.

Rewrite using `[hσ]`. Conclude with `h`.
-/
theorem isInt_cT {σ : L →+* L} (hσ : ∀ x, Valued.v (σ x) = Valued.v x) {M : Matrix (Fin N) (Fin N) L} (hM : IsInt M) :
    IsInt (cT σ M) := by
  intro i j
  have h : M j i ∈ intL L := hM j i
  have hmem : ∀ x : L, x ∈ intL L ↔ Valued.v x ≤ 1 := fun x => Valuation.mem_integer_iff _ _
  simp only [cT, Matrix.transpose_apply, Matrix.map_apply]
  rw [hmem] at h ⊢
  rw [hσ]
  exact h

/- English proof (translation)
Simplify using `only [Matrix.mulVec, dotProduct]`. Conclude with `sum_mem (fun j _ => mul_mem (hM i j) (hw j))`.
-/
theorem int_mulVec {M : Matrix (Fin N) (Fin N) L} (hM : IsInt M) {w : Fin N → L} (hw : ∀ i, w i ∈ intL L) (i : Fin N) :
    (M *ᵥ w) i ∈ intL L := by
  simp only [Matrix.mulVec, dotProduct]
  exact sum_mem (fun j _ => mul_mem (hM i j) (hw j))

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `key : ∀ P : Matrix (Fin N) (Fin N) L, IsInt (P * E) → ∀ i, (P *ᵥ B) i ∈ intL L`. Introduce `P hP i`. Establish `hPB : P *ᵥ B = (P * E) *ᵥ (D *ᵥ B)`.

Rewrite using `[Matrix.mulVec_mulVec, Matrix.mul_assoc, hED, Matrix.mul_one]`. Rewrite using `[hPB]`. Conclude with `int_mulVec hP h i`. Conclude with `⟨key Q hQ, key R hR⟩`. Introduce and unpack `⟨hq, hr⟩ i`.

Establish `hDB : D *ᵥ B = Dg *ᵥ (R *ᵥ B) + D *ᵥ (Q *ᵥ B)`. Rewrite using `[Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.add_mulVec, ← e]`. Rewrite using `[hDB, Pi.add_apply]`. Conclude with `add_mem (int_mulVec hDg hr i) (int_mulVec hD hq i)`.
-/
theorem iff_of_inverse {D E Q R Dg : Matrix (Fin N) (Fin N) L} (hED : E * D = 1) (hQ : IsInt (Q * E))
    (hR : IsInt (R * E)) (hDg : IsInt Dg) (hD : IsInt D) (e : D = Dg * R + D * Q) (B : Fin N → L) :
    (∀ i, (D *ᵥ B) i ∈ intL L) ↔ (∀ i, (Q *ᵥ B) i ∈ intL L) ∧ ∀ i, (R *ᵥ B) i ∈ intL L := by
  constructor
  · intro h
    have key : ∀ P : Matrix (Fin N) (Fin N) L, IsInt (P * E) → ∀ i, (P *ᵥ B) i ∈ intL L := by
      intro P hP i
      have hPB : P *ᵥ B = (P * E) *ᵥ (D *ᵥ B) := by
        rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, hED, Matrix.mul_one]
      rw [hPB]
      exact int_mulVec hP h i
    exact ⟨key Q hQ, key R hR⟩
  · rintro ⟨hq, hr⟩ i
    have hDB : D *ᵥ B = Dg *ᵥ (R *ᵥ B) + D *ᵥ (Q *ᵥ B) := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.add_mulVec, ← e]
    rw [hDB, Pi.add_apply]
    exact add_mem (int_mulVec hDg hr i) (int_mulVec hD hq i)

/- English proof (translation)
Unfold `GlobalTheory.InertZeta.Dual`. Introduce `L _ _ ϖ σ q N hU g U V C hF r b t hr`. Take `⟨hσσ, hσv, -, -, -, -, -⟩` from `hU`. Take `⟨hUi, hVi, hCi, hAi, hUVC⟩` from `hF`. Establish `hg : cT σ (mat g) * antiJ L N * mat g = antiJ L N` using `g.2`.

Establish `hJJ : antiJ L N * antiJ L N = 1` using `antiJ_mul_self`. Establish `hJi : IsInt (antiJ L N)` using `isInt_antiJ`. Establish `hmem : ∀ x : L, x ∈ intL L ↔ Valued.v x ≤ 1` using `fun x => Valuation.mem_integer_iff _ _`. Establish `hsub : ∀ {X Y : Matrix (Fin N) (Fin N) L}, IsInt X → IsInt Y → IsInt (X - Y)` using `fun hX hY i j => sub_mem (hX i j) (hY i j)`. Establish `hcTmul : ∀ X Y : Matrix (Fin N) (Fin N) L, cT σ (X * Y) = cT σ Y * cT σ X`.

Introduce `X Y`. Simplify using `[cT, Matrix.map_mul, Matrix.transpose_mul]`. Establish `hcTone : cT σ (1 : Matrix (Fin N) (Fin N) L) = 1`. Use extensionality with `i j`. Distinguish the cases in `h : i = j`.

Substitute `h` using the available equality. Simplify using `[cT]`. Simplify using `[cT, Matrix.one_apply, h, Ne.symm h]`. Establish `hGJ : mat g * antiJ L N * cT σ (mat g) = antiJ L N`. Establish `h1 : (antiJ L N * cT σ (mat g) * antiJ L N) * mat g = 1`.

Rewrite using `[show antiJ L N * cT σ (mat g) * antiJ L N * mat g = antiJ L N * (cT σ (mat g) * antiJ L N * mat g) by simp only [Matrix.mul_assoc], hg, hJJ]`. Establish `h2` using `mul_eq_one_comm.mp h1`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc, hJJ, Matrix.mul_one]`. Use `_ = antiJ L N := by rw [h2, Matrix.one_mul]`.

Establish `hCUV : C * (U + V * mat g) = 1` using `mul_eq_one_comm.mp hUVC`. Establish `hCUV' : C * U + C * V * mat g = 1`. Rewrite using `[Matrix.mul_assoc C V, ← Matrix.mul_add]`. Conclude with `hCUV`. Establish `hED : (antiJ L N * cT σ (U + V * mat g)) * (cT σ C * antiJ L N) = 1`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hcTmul]`. Simplify using `only [Matrix.mul_assoc]`. Use `_ = 1 := by rw [hCUV, hcTone, Matrix.mul_one, hJJ]`. Establish `hD : IsInt (cT σ C * antiJ L N)` using `(isInt_cT hσv hCi).mul hJi`.

Establish `hDg : IsInt (cT σ (mat g * C) * antiJ L N)` using `(isInt_cT hσv hAi).mul hJi`. Establish `he : cT σ C * antiJ L N = cT σ (mat g * C) * antiJ L N * (mat g * C * U) + cT σ C * antiJ L N * (C * V * mat g)`. Establish `h1 : cT σ C * cT σ (mat g) * antiJ L N * (mat g * C * U) = cT σ C * antiJ L N * (C * U)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hcTmul, h1, ← Matrix.mul_add, hCUV', Matrix.mul_one]`.

Establish `hcTU : IsInt (cT σ U)` using `isInt_cT hσv hUi`. Establish `hcTV : IsInt (cT σ V)` using `isInt_cT hσv hVi`. Establish `hQE : IsInt (C * V * mat g * (antiJ L N * cT σ (U + V * mat g)))`. Establish `hCVG : C * V * mat g = 1 - C * U` using `eq_sub_of_add_eq' hCUV'`. Establish `h2 : C * V * mat g * (antiJ L N * (cT σ (mat g) * cT σ V)) = C * V * (antiJ L N * cT σ V)`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[cT_add, hcTmul, Matrix.mul_add (antiJ L N), Matrix.mul_add, h2, hCVG, Matrix.sub_mul, Matrix.one_mul]`. Conclude with `(hsub (hJi.mul hcTU) ((hCi.mul hUi).mul (hJi.mul hcTU))).add ((hCi.mul hVi).mul (hJi.mul hcTV))`. Establish `hRE : IsInt (mat g * C * U * (antiJ L N * cT σ (U + V * mat g)))`. Establish `hCU : C * U = 1 - C * V * mat g` using `eq_sub_of_add_eq hCUV'`.

Establish `hA : mat g * (antiJ L N * cT σ (mat g)) * cT σ V = antiJ L N * cT σ V`. Rewrite using `[← Matrix.mul_assoc (mat g) (antiJ L N), hGJ]`. Establish `hB : mat g * (C * V * mat g) * (antiJ L N * cT σ (mat g)) * cT σ V = mat g * C * V * (antiJ L N * cT σ V)`. Combine the equalities or inequalities in the displayed calculation. Establish `h3 : mat g * C * U * (antiJ L N * (cT σ (mat g) * cT σ V)) = antiJ L N * cT σ V - mat g * C * V * (antiJ L N * cT σ V)`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, Matrix.sub_mul, hA, hB]`. Rewrite using `[cT_add, hcTmul, Matrix.mul_add (antiJ L N), Matrix.mul_add, h3]`. Conclude with `((hAi.mul hUi).mul (hJi.mul hcTU)).add (hsub (hJi.mul hcTV) ((hAi.mul hVi).mul (hJi.mul hcTV)))`. Establish `hJb : antiJ L N *ᵥ b = fun k => b k.rev` using `funext (antiJ_mulVec b)`.

Establish `hσvec : ∀ j, σ (vecMul r C j) = -((cT σ C * antiJ L N) *ᵥ b) j`. Introduce `j`. Rewrite using `[← Matrix.mulVec_mulVec, hJb]`. Simplify using `only [Matrix.vecMul, Matrix.mulVec, dotProduct, cT, Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul, hr, map_neg, hσσ, neg_mul, Finset.sum_neg_distrib, neg_inj]`. Conclude with `Finset.sum_congr rfl (fun i _ => mul_comm _ _)`.

Establish `hL : ∀ j, (t * vecMul r C j ∈ intL L ↔ t * ((cT σ C * antiJ L N) *ᵥ b) j ∈ intL L)`. Introduce `j`. Rewrite using `[hmem, hmem, Valuation.map_mul, Valuation.map_mul, ← hσv (vecMul r C j), hσvec j, Valuation.map_neg]`. Establish `key` using `iff_of_inverse (D := cT σ C * antiJ L N) (E := antiJ L N * cT σ (U + V * mat g)) (Q := C * V * mat g) (R := mat g * C * U) (Dg := cT σ (mat g * C) * antiJ L N) hED hQE hRE hDg hD he (t • b)`. Simplify using `only [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul] at key`.

Rewrite using `[forall_congr' hL]`. Conclude with `key`.
-/
theorem dual : Dual := by
  unfold GlobalTheory.InertZeta.Dual
  intro L _ _ ϖ σ q N hU g U V C hF r b t hr
  obtain ⟨hσσ, hσv, -, -, -, -, -⟩ := hU
  obtain ⟨hUi, hVi, hCi, hAi, hUVC⟩ := hF
  have hg : cT σ (mat g) * antiJ L N * mat g = antiJ L N := g.2
  have hJJ : antiJ L N * antiJ L N = 1 := antiJ_mul_self
  have hJi : IsInt (antiJ L N) := isInt_antiJ
  have hmem : ∀ x : L, x ∈ intL L ↔ Valued.v x ≤ 1 := fun x => Valuation.mem_integer_iff _ _
  have hsub : ∀ {X Y : Matrix (Fin N) (Fin N) L}, IsInt X → IsInt Y → IsInt (X - Y) :=
    fun hX hY i j => sub_mem (hX i j) (hY i j)
  have hcTmul : ∀ X Y : Matrix (Fin N) (Fin N) L, cT σ (X * Y) = cT σ Y * cT σ X := by
    intro X Y
    simp [cT, Matrix.map_mul, Matrix.transpose_mul]
  have hcTone : cT σ (1 : Matrix (Fin N) (Fin N) L) = 1 := by
    ext i j
    by_cases h : i = j
    · subst h
      simp [cT]
    · simp [cT, Matrix.one_apply, h, Ne.symm h]
  have hGJ : mat g * antiJ L N * cT σ (mat g) = antiJ L N := by
    have h1 : (antiJ L N * cT σ (mat g) * antiJ L N) * mat g = 1 := by
      rw [show antiJ L N * cT σ (mat g) * antiJ L N * mat g
          = antiJ L N * (cT σ (mat g) * antiJ L N * mat g) by simp only [Matrix.mul_assoc], hg, hJJ]
    have h2 := mul_eq_one_comm.mp h1
    calc mat g * antiJ L N * cT σ (mat g)
        = mat g * (antiJ L N * cT σ (mat g) * antiJ L N) * antiJ L N := by
          simp only [Matrix.mul_assoc, hJJ, Matrix.mul_one]
      _ = antiJ L N := by rw [h2, Matrix.one_mul]
  have hCUV : C * (U + V * mat g) = 1 := mul_eq_one_comm.mp hUVC
  have hCUV' : C * U + C * V * mat g = 1 := by
    rw [Matrix.mul_assoc C V, ← Matrix.mul_add]
    exact hCUV
  have hED : (antiJ L N * cT σ (U + V * mat g)) * (cT σ C * antiJ L N) = 1 := by
    calc (antiJ L N * cT σ (U + V * mat g)) * (cT σ C * antiJ L N)
        = antiJ L N * cT σ (C * (U + V * mat g)) * antiJ L N := by
          rw [hcTmul]
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hCUV, hcTone, Matrix.mul_one, hJJ]
  have hD : IsInt (cT σ C * antiJ L N) := (isInt_cT hσv hCi).mul hJi
  have hDg : IsInt (cT σ (mat g * C) * antiJ L N) := (isInt_cT hσv hAi).mul hJi
  have he : cT σ C * antiJ L N
      = cT σ (mat g * C) * antiJ L N * (mat g * C * U) + cT σ C * antiJ L N * (C * V * mat g) := by
    have h1 : cT σ C * cT σ (mat g) * antiJ L N * (mat g * C * U) = cT σ C * antiJ L N * (C * U) := by
      calc cT σ C * cT σ (mat g) * antiJ L N * (mat g * C * U)
          = cT σ C * (cT σ (mat g) * antiJ L N * mat g) * (C * U) := by simp only [Matrix.mul_assoc]
        _ = cT σ C * antiJ L N * (C * U) := by rw [hg]
    rw [hcTmul, h1, ← Matrix.mul_add, hCUV', Matrix.mul_one]
  have hcTU : IsInt (cT σ U) := isInt_cT hσv hUi
  have hcTV : IsInt (cT σ V) := isInt_cT hσv hVi
  have hQE : IsInt (C * V * mat g * (antiJ L N * cT σ (U + V * mat g))) := by
    have hCVG : C * V * mat g = 1 - C * U := eq_sub_of_add_eq' hCUV'
    have h2 : C * V * mat g * (antiJ L N * (cT σ (mat g) * cT σ V)) = C * V * (antiJ L N * cT σ V) := by
      calc C * V * mat g * (antiJ L N * (cT σ (mat g) * cT σ V))
          = C * V * (mat g * antiJ L N * cT σ (mat g)) * cT σ V := by simp only [Matrix.mul_assoc]
        _ = C * V * (antiJ L N * cT σ V) := by rw [hGJ]; simp only [Matrix.mul_assoc]
    rw [cT_add, hcTmul, Matrix.mul_add (antiJ L N), Matrix.mul_add, h2, hCVG, Matrix.sub_mul, Matrix.one_mul]
    exact (hsub (hJi.mul hcTU) ((hCi.mul hUi).mul (hJi.mul hcTU))).add ((hCi.mul hVi).mul (hJi.mul hcTV))
  have hRE : IsInt (mat g * C * U * (antiJ L N * cT σ (U + V * mat g))) := by
    have hCU : C * U = 1 - C * V * mat g := eq_sub_of_add_eq hCUV'
    have hA : mat g * (antiJ L N * cT σ (mat g)) * cT σ V = antiJ L N * cT σ V := by
      rw [← Matrix.mul_assoc (mat g) (antiJ L N), hGJ]
    have hB : mat g * (C * V * mat g) * (antiJ L N * cT σ (mat g)) * cT σ V
        = mat g * C * V * (antiJ L N * cT σ V) := by
      calc mat g * (C * V * mat g) * (antiJ L N * cT σ (mat g)) * cT σ V
          = mat g * C * V * (mat g * antiJ L N * cT σ (mat g)) * cT σ V := by simp only [Matrix.mul_assoc]
        _ = mat g * C * V * (antiJ L N * cT σ V) := by rw [hGJ]; simp only [Matrix.mul_assoc]
    have h3 : mat g * C * U * (antiJ L N * (cT σ (mat g) * cT σ V))
        = antiJ L N * cT σ V - mat g * C * V * (antiJ L N * cT σ V) := by
      calc mat g * C * U * (antiJ L N * (cT σ (mat g) * cT σ V))
          = mat g * (C * U) * (antiJ L N * cT σ (mat g)) * cT σ V := by simp only [Matrix.mul_assoc]
        _ = mat g * (1 - C * V * mat g) * (antiJ L N * cT σ (mat g)) * cT σ V := by rw [hCU]
        _ = antiJ L N * cT σ V - mat g * C * V * (antiJ L N * cT σ V) := by
          rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, Matrix.sub_mul, hA, hB]
    rw [cT_add, hcTmul, Matrix.mul_add (antiJ L N), Matrix.mul_add, h3]
    exact ((hAi.mul hUi).mul (hJi.mul hcTU)).add (hsub (hJi.mul hcTV) ((hAi.mul hVi).mul (hJi.mul hcTV)))
  have hJb : antiJ L N *ᵥ b = fun k => b k.rev := funext (antiJ_mulVec b)
  have hσvec : ∀ j, σ (vecMul r C j) = -((cT σ C * antiJ L N) *ᵥ b) j := by
    intro j
    rw [← Matrix.mulVec_mulVec, hJb]
    simp only [Matrix.vecMul, Matrix.mulVec, dotProduct, cT, Matrix.transpose_apply, Matrix.map_apply,
      map_sum, map_mul, hr, map_neg, hσσ, neg_mul, Finset.sum_neg_distrib, neg_inj]
    exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
  have hL : ∀ j, (t * vecMul r C j ∈ intL L ↔ t * ((cT σ C * antiJ L N) *ᵥ b) j ∈ intL L) := by
    intro j
    rw [hmem, hmem, Valuation.map_mul, Valuation.map_mul, ← hσv (vecMul r C j), hσvec j, Valuation.map_neg]
  have key := iff_of_inverse (D := cT σ C * antiJ L N) (E := antiJ L N * cT σ (U + V * mat g))
    (Q := C * V * mat g) (R := mat g * C * U) (Dg := cT σ (mat g * C) * antiJ L N)
    hED hQE hRE hDg hD he (t • b)
  simp only [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul] at key
  rw [forall_congr' hL]
  exact key

end GlobalTheory.CompanionTheory.InertDual

end
