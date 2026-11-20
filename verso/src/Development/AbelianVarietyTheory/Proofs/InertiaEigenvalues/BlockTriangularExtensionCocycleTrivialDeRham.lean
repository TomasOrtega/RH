import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamPeriodRingFieldTPowFiltrationUnitsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InvariantRightInverseOfRightInverseStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KroneckerTransposeMulVec
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `l _ P AI T a b _ _ _ _ K ρ ρ₁ ρ₂ c hρ hQ hR m`. Take `⟨Q, hQm⟩` from `hQ m`. Take `⟨R, hRm⟩` from `hR m`. Set `f : ↥(MaximalUnramifiedExtension l) →+* P.R.BdR` to `(kd P).comp (fr l m)`. Set `σ : ↥(GK K) → P.R.BdR →+* P.R.BdR` to `fun g => ((P.actQdR (g : GQ l) : P.R.BdR ≃ₐ[ℚ_[l]] P.R.BdR) : P.R.BdR →+* P.R.BdR)`.

Set `A : ↥(GK K) → Matrix a a P.R.BdR` to `fun g => (ρ₁ g : Matrix a a ↥(MaximalUnramifiedExtension l)).map f`. Set `C : ↥(GK K) → Matrix a b P.R.BdR` to `fun g => (c g).map f`. Set `D : ↥(GK K) → Matrix b b P.R.BdR` to `fun g => (ρ₂ g : Matrix b b ↥(MaximalUnramifiedExtension l)).map f`. Set `Di : ↥(GK K) → Matrix b b P.R.BdR` to `fun g => (((ρ₂ g)⁻¹ : GL b ↥(MaximalUnramifiedExtension l)) : Matrix b b ↥(MaximalUnramifiedExtension l)).map f`. Establish `hDDi : ∀ g, D g * Di g = 1` using `fun g => by`.

Simplify using `only [D, Di]`. Rewrite using `[← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.map_one _ (map_zero f) (map_one f)]`. Establish `hDiD : ∀ g, Di g * D g = 1` using `fun g => by`. Simplify using `only [D, Di]`. Rewrite using `[← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.map_one _ (map_zero f) (map_one f)]`.

Establish `hM : ∀ g, matD P ρ m g = Matrix.fromBlocks (A g) (C g) 0 (D g)` using `fun g => by show (ρ g : Matrix (a ⊕ b) (a ⊕ b) ↥(MaximalUnramifiedExtension l)).map f = _`. Rewrite using `[hρ g, Matrix.fromBlocks_map, Matrix.map_zero _ (map_zero f)]`. Set `Qa : Matrix a (a ⊕ b) P.R.BdR` to `(Q : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR).submatrix Sum.inl id`. Set `Qb : Matrix b (a ⊕ b) P.R.BdR` to `(Q : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR).submatrix Sum.inr id`. Establish `hb : ∀ g, D g * Qb.map (σ g) = Qb` using `fun g => by`.

Use extensionality with `i j`. Establish `h` using `congrFun (congrFun (hQm g) (Sum.inr i)) j`. Rewrite `h` using `[hM g]`. Simplify `h` using `[Matrix.mul_apply, Fintype.sum_sum_type, Qb, σ]`. Establish `ha : ∀ g, A g * Qa.map (σ g) + C g * Qb.map (σ g) = Qa` using `fun g => by`.

Use extensionality with `i j`. Establish `h` using `congrFun (congrFun (hQm g) (Sum.inl i)) j`. Rewrite `h` using `[hM g]`. Simplify `h` using `[Matrix.mul_apply, Fintype.sum_sum_type, Qa, Qb, σ]`. Establish `hRg : ∀ g, D g * (R : Matrix b b P.R.BdR).map (σ g) = R` using `fun g => hRm g`.

Set `S : Matrix b b P.R.BdR` to `((R⁻¹ : GL b P.R.BdR) : Matrix b b P.R.BdR)`. Establish `hSR : S * R = 1` using `by simp only [S]; rw [← Units.val_mul, inv_mul_cancel, Units.val_one]`. Establish `hRS : (R : Matrix b b P.R.BdR) * S = 1` using `by simp only [S]; rw [← Units.val_mul, mul_inv_cancel, Units.val_one]`. Establish `hgSR : ∀ g, S.map (σ g) * (R : Matrix b b P.R.BdR).map (σ g) = 1` using `fun g => by`. Rewrite using `[← Matrix.map_mul, hSR, Matrix.map_one _ (map_zero _) (map_one _)]`.

Establish `hgRS : ∀ g, (R : Matrix b b P.R.BdR).map (σ g) * S.map (σ g) = 1` using `fun g => by`. Rewrite using `[← Matrix.map_mul, hRS, Matrix.map_one _ (map_zero _) (map_one _)]`. Establish `hgS : ∀ g, S.map (σ g) = S * D g` using `fun g => by`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hRg g, hSR, Matrix.one_mul]`.

Use `_ = S * D g * ((R : Matrix b b P.R.BdR).map (σ g) * S.map (σ g)) := by`. Simplify using `only [Matrix.mul_assoc]`. Use `_ = S * D g := by rw [hgRS g, Matrix.mul_one]`. Establish `hgR : ∀ g, (R : Matrix b b P.R.BdR).map (σ g) = Di g * R` using `fun g => by`. Use `symm`.

Use `conv_lhs => rw [← hRg g]`. Rewrite using `[← Matrix.mul_assoc, hDiD g, Matrix.one_mul]`. Take `⟨κ, hκdef⟩ : ∃ κ : Matrix b (a ⊕ b) P.R.BdR, κ = S * Qb` from `⟨_, rfl⟩`. Establish `hκ : ∀ g, κ.map (σ g) = κ` using `fun g => by`. Rewrite using `[hκdef, Matrix.map_mul, hgS g, Matrix.mul_assoc, hb g]`.

Set `Y : Matrix (a ⊕ b) b P.R.BdR` to `(((Q⁻¹ : GL (a ⊕ b) P.R.BdR) : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR).submatrix id Sum.inr) * (R : Matrix b b P.R.BdR)`. Establish `hQQ : (Q : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR) * ((Q⁻¹ : GL (a ⊕ b) P.R.BdR) : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR) = 1`. Rewrite using `[← Units.val_mul, mul_inv_cancel, Units.val_one]`. Establish `hQb : Qb * (((Q⁻¹ : GL (a ⊕ b) P.R.BdR) : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR).submatrix id Sum.inr) = 1`. Use extensionality with `i j`.

Establish `h` using `congrFun (congrFun hQQ (Sum.inr i)) (Sum.inr j)`. Simplify `h` using `[Matrix.mul_apply, Matrix.one_apply, Qb]`. Establish `hY : κ * Y = 1`. Simplify using `only [Y]`. Rewrite using `[hκdef, Matrix.mul_assoc, ← Matrix.mul_assoc Qb, hQb, Matrix.one_mul, hSR]`.

Take `⟨Λ, hκΛ, hΛ⟩` from `GlobalTheory.T.exists_invariant_right_inverse P.R.BdR (GlobalTheory.T.deRhamPeriodRing_field_tPow_filtration_units l P AI T).1 (↥(GK K)) σ (a ⊕ b) b κ Y hY hκ`. Establish `hQbR : Qb = (R : Matrix b b P.R.BdR) * κ`. Rewrite using `[hκdef, ← Matrix.mul_assoc, hRS, Matrix.one_mul]`. Establish `hgQb : ∀ g, Qb.map (σ g) = (R : Matrix b b P.R.BdR).map (σ g) * κ` using `fun g => by conv_lhs => rw [hQbR]`. Rewrite using `[Matrix.map_mul, hκ g]`.

Set `Z : Matrix a b P.R.BdR` to `Qa * Λ`. Establish `hAZ : ∀ g, A g * Z.map (σ g) = Z - C g * (R : Matrix b b P.R.BdR).map (σ g)` using `fun g => by`. Establish `e : A g * Qa.map (σ g) = Qa - C g * ((R : Matrix b b P.R.BdR).map (σ g) * κ)`. Rewrite using `[← hgQb g]`. Conclude with `eq_sub_of_add_eq (ha g)`.

Simplify using `only [Z]`. Rewrite using `[Matrix.map_mul, hΛ g, ← Matrix.mul_assoc, e, Matrix.sub_mul, Matrix.mul_assoc (C g), Matrix.mul_assoc ((R : Matrix b b P.R.BdR).map (σ g)), hκΛ, Matrix.mul_one]`. Use `⟨vecM (-(Z * S)), fun g => ?_⟩` and prove the remaining obligations. Establish `hL : (fun i => kd P (fr l m (extCoc ρ₂ c g i))) = vecM (C g * Di g)` using `by show vecM ((c g * (((ρ₂ g)⁻¹ : GL b ↥(MaximalUnramifiedExtension l)) : Matrix b b ↥(MaximalUnramifiedExtension l))).map f) = _`. Rewrite using `[Matrix.map_mul]`.

Establish `hR' : (matD P (homRep ρ₁ ρ₂) m g).mulVec (fun i => P.actQdR (g : GQ l) (vecM (-(Z * S)) i)) = vecM (A g * (-(Z * S)).map (σ g) * Di g)` using `by show (((homUnit (ρ₁ g) (ρ₂ g) : GL (a × b) ↥(MaximalUnramifiedExtension l)) : Matrix (a × b) (a × b) ↥(MaximalUnramifiedExtension l)).map f).mulVec (vecM ((-(Z * S)).map (σ g))) = _`. Rewrite using `[homUnit_mulVec]`. Rewrite using `[hL, hR']`. Establish `hsub : ∀ X Y : Matrix a b P.R.BdR, vecM X - vecM Y = vecM (X - Y)` using `fun _ _ => rfl`. Rewrite using `[hsub]`.

Use `congr 1`. Establish `hneg : (-(Z * S)).map (σ g) = -(Z.map (σ g) * S.map (σ g))`. Rewrite using `[Matrix.map_neg _ (map_neg (σ g)), Matrix.map_mul]`. Rewrite using `[hneg, hgS g, Matrix.mul_neg, Matrix.neg_mul, ← Matrix.mul_assoc (A g), hAZ g, hgR g]`. Simplify using `only [Matrix.sub_mul, Matrix.mul_assoc, hDDi g, hRS, Matrix.mul_one]`.

Normalize the expressions using the abelian group laws.
-/
theorem GlobalTheory.PMon.extCoc_dies_in_BdR : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (_ : LocTied l P AI) (a b : Type) [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (K : FinExt l) (ρ : ↥(GK K) →* GL (a ⊕ b) ↥(MaximalUnramifiedExtension l)) (ρ₁ : ↥(GK K) →* GL a ↥(MaximalUnramifiedExtension l)) (ρ₂ : ↥(GK K) →* GL b ↥(MaximalUnramifiedExtension l)) (c : ↥(GK K) → Matrix a b ↥(MaximalUnramifiedExtension l)), (∀ g, (ρ g : Matrix (a ⊕ b) (a ⊕ b) ↥(MaximalUnramifiedExtension l)) = Matrix.fromBlocks (ρ₁ g : Matrix a a ↥(MaximalUnramifiedExtension l)) (c g) 0 (ρ₂ g : Matrix b b ↥(MaximalUnramifiedExtension l))) → AdmDR P ρ → AdmDR P ρ₂ → ∀ m : ℕ, ∃ v : a × b → P.R.BdR, ∀ g : ↥(GK K), (fun i => kd P (fr l m (extCoc ρ₂ c g i))) = (matD P (homRep ρ₁ ρ₂) m g).mulVec (fun i => P.actQdR (g : GQ l) (v i)) - v := by
  intro l _ P AI T a b _ _ _ _ K ρ ρ₁ ρ₂ c hρ hQ hR m
  obtain ⟨Q, hQm⟩ := hQ m
  obtain ⟨R, hRm⟩ := hR m
  let f : ↥(MaximalUnramifiedExtension l) →+* P.R.BdR := (kd P).comp (fr l m)
  let σ : ↥(GK K) → P.R.BdR →+* P.R.BdR := fun g => ((P.actQdR (g : GQ l) : P.R.BdR ≃ₐ[ℚ_[l]] P.R.BdR) : P.R.BdR →+* P.R.BdR)

  let A : ↥(GK K) → Matrix a a P.R.BdR := fun g => (ρ₁ g : Matrix a a ↥(MaximalUnramifiedExtension l)).map f
  let C : ↥(GK K) → Matrix a b P.R.BdR := fun g => (c g).map f
  let D : ↥(GK K) → Matrix b b P.R.BdR := fun g => (ρ₂ g : Matrix b b ↥(MaximalUnramifiedExtension l)).map f
  let Di : ↥(GK K) → Matrix b b P.R.BdR := fun g => (((ρ₂ g)⁻¹ : GL b ↥(MaximalUnramifiedExtension l)) : Matrix b b ↥(MaximalUnramifiedExtension l)).map f
  have hDDi : ∀ g, D g * Di g = 1 := fun g => by
    simp only [D, Di]
    rw [← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.map_one _ (map_zero f) (map_one f)]
  have hDiD : ∀ g, Di g * D g = 1 := fun g => by
    simp only [D, Di]
    rw [← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.map_one _ (map_zero f) (map_one f)]
  have hM : ∀ g, matD P ρ m g = Matrix.fromBlocks (A g) (C g) 0 (D g) := fun g => by
    show (ρ g : Matrix (a ⊕ b) (a ⊕ b) ↥(MaximalUnramifiedExtension l)).map f = _
    rw [hρ g, Matrix.fromBlocks_map, Matrix.map_zero _ (map_zero f)]
  let Qa : Matrix a (a ⊕ b) P.R.BdR := (Q : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR).submatrix Sum.inl id
  let Qb : Matrix b (a ⊕ b) P.R.BdR := (Q : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR).submatrix Sum.inr id
  have hb : ∀ g, D g * Qb.map (σ g) = Qb := fun g => by
    ext i j
    have h := congrFun (congrFun (hQm g) (Sum.inr i)) j
    rw [hM g] at h
    simpa [Matrix.mul_apply, Fintype.sum_sum_type, Qb, σ] using h
  have ha : ∀ g, A g * Qa.map (σ g) + C g * Qb.map (σ g) = Qa := fun g => by
    ext i j
    have h := congrFun (congrFun (hQm g) (Sum.inl i)) j
    rw [hM g] at h
    simpa [Matrix.mul_apply, Fintype.sum_sum_type, Qa, Qb, σ] using h
  have hRg : ∀ g, D g * (R : Matrix b b P.R.BdR).map (σ g) = R := fun g => hRm g
  let S : Matrix b b P.R.BdR := ((R⁻¹ : GL b P.R.BdR) : Matrix b b P.R.BdR)
  have hSR : S * R = 1 := by simp only [S]; rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hRS : (R : Matrix b b P.R.BdR) * S = 1 := by simp only [S]; rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hgSR : ∀ g, S.map (σ g) * (R : Matrix b b P.R.BdR).map (σ g) = 1 := fun g => by
    rw [← Matrix.map_mul, hSR, Matrix.map_one _ (map_zero _) (map_one _)]
  have hgRS : ∀ g, (R : Matrix b b P.R.BdR).map (σ g) * S.map (σ g) = 1 := fun g => by
    rw [← Matrix.map_mul, hRS, Matrix.map_one _ (map_zero _) (map_one _)]
  have hgS : ∀ g, S.map (σ g) = S * D g := fun g => by
    calc S.map (σ g) = (S * (D g * (R : Matrix b b P.R.BdR).map (σ g))) * S.map (σ g) := by
          rw [hRg g, hSR, Matrix.one_mul]
      _ = S * D g * ((R : Matrix b b P.R.BdR).map (σ g) * S.map (σ g)) := by
          simp only [Matrix.mul_assoc]
      _ = S * D g := by rw [hgRS g, Matrix.mul_one]
  have hgR : ∀ g, (R : Matrix b b P.R.BdR).map (σ g) = Di g * R := fun g => by
    symm
    conv_lhs => rw [← hRg g]
    rw [← Matrix.mul_assoc, hDiD g, Matrix.one_mul]
  obtain ⟨κ, hκdef⟩ : ∃ κ : Matrix b (a ⊕ b) P.R.BdR, κ = S * Qb := ⟨_, rfl⟩
  have hκ : ∀ g, κ.map (σ g) = κ := fun g => by
    rw [hκdef, Matrix.map_mul, hgS g, Matrix.mul_assoc, hb g]
  let Y : Matrix (a ⊕ b) b P.R.BdR :=
    (((Q⁻¹ : GL (a ⊕ b) P.R.BdR) : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR).submatrix id Sum.inr) * (R : Matrix b b P.R.BdR)
  have hQQ : (Q : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR) * ((Q⁻¹ : GL (a ⊕ b) P.R.BdR) : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hQb : Qb * (((Q⁻¹ : GL (a ⊕ b) P.R.BdR) : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR).submatrix id Sum.inr) = 1 := by
    ext i j
    have h := congrFun (congrFun hQQ (Sum.inr i)) (Sum.inr j)
    simpa [Matrix.mul_apply, Matrix.one_apply, Qb] using h
  have hY : κ * Y = 1 := by
    simp only [Y]
    rw [hκdef, Matrix.mul_assoc, ← Matrix.mul_assoc Qb, hQb, Matrix.one_mul, hSR]
  obtain ⟨Λ, hκΛ, hΛ⟩ := GlobalTheory.T.exists_invariant_right_inverse P.R.BdR (GlobalTheory.T.deRhamPeriodRing_field_tPow_filtration_units l P AI T).1 (↥(GK K)) σ (a ⊕ b) b κ Y hY hκ
  have hQbR : Qb = (R : Matrix b b P.R.BdR) * κ := by
    rw [hκdef, ← Matrix.mul_assoc, hRS, Matrix.one_mul]
  have hgQb : ∀ g, Qb.map (σ g) = (R : Matrix b b P.R.BdR).map (σ g) * κ := fun g => by
    conv_lhs => rw [hQbR]
    rw [Matrix.map_mul, hκ g]
  let Z : Matrix a b P.R.BdR := Qa * Λ
  have hAZ : ∀ g, A g * Z.map (σ g) = Z - C g * (R : Matrix b b P.R.BdR).map (σ g) := fun g => by
    have e : A g * Qa.map (σ g) = Qa - C g * ((R : Matrix b b P.R.BdR).map (σ g) * κ) := by
      rw [← hgQb g]
      exact eq_sub_of_add_eq (ha g)
    simp only [Z]
    rw [Matrix.map_mul, hΛ g, ← Matrix.mul_assoc, e, Matrix.sub_mul, Matrix.mul_assoc (C g),
      Matrix.mul_assoc ((R : Matrix b b P.R.BdR).map (σ g)), hκΛ, Matrix.mul_one]
  refine ⟨vecM (-(Z * S)), fun g => ?_⟩
  have hL : (fun i => kd P (fr l m (extCoc ρ₂ c g i))) = vecM (C g * Di g) := by
    show vecM ((c g * (((ρ₂ g)⁻¹ : GL b ↥(MaximalUnramifiedExtension l)) : Matrix b b ↥(MaximalUnramifiedExtension l))).map f) = _
    rw [Matrix.map_mul]
  have hR' : (matD P (homRep ρ₁ ρ₂) m g).mulVec (fun i => P.actQdR (g : GQ l) (vecM (-(Z * S)) i)) =
      vecM (A g * (-(Z * S)).map (σ g) * Di g) := by
    show (((homUnit (ρ₁ g) (ρ₂ g) : GL (a × b) ↥(MaximalUnramifiedExtension l)) : Matrix (a × b) (a × b) ↥(MaximalUnramifiedExtension l)).map f).mulVec
      (vecM ((-(Z * S)).map (σ g))) = _
    rw [homUnit_mulVec]
  rw [hL, hR']
  have hsub : ∀ X Y : Matrix a b P.R.BdR, vecM X - vecM Y = vecM (X - Y) := fun _ _ => rfl
  rw [hsub]
  congr 1
  have hneg : (-(Z * S)).map (σ g) = -(Z.map (σ g) * S.map (σ g)) := by
    rw [Matrix.map_neg _ (map_neg (σ g)), Matrix.map_mul]
  rw [hneg, hgS g, Matrix.mul_neg, Matrix.neg_mul, ← Matrix.mul_assoc (A g), hAZ g, hgR g]
  simp only [Matrix.sub_mul, Matrix.mul_assoc, hDDi g, hRS, Matrix.mul_one]
  abel
