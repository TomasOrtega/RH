import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBdRPlusFrameOfPeriodMatrixStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamPeriodRingFieldTPowFiltrationUnitsStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon.FrameEquiv

variable {l : ℕ} [Fact l.Prime]

/- English proof (translation)
Take `⟨K, hK⟩ : ∃ K : FinExt l, x ∈ K.1` from `⟨⟨IntermediateField.adjoin ℚ_[l] {x}, IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral _)⟩, IntermediateField.mem_adjoin_simple_self _ _⟩`. Establish `h2` using `((P.PD K).Fil 0).smul_mem (⟨x, hK⟩ : ↥K.1) (P.PD K).one_mem`. Rewrite `h2` using `[Algebra.smul_def, mul_one]`. Use `show algebraMap (Om l) P.R.BdR x ∈ ((P.PD (botExt l)).Fil 0 : Set P.R.BdR)`. Rewrite using `[P.PD_Fil (botExt l) K 0]`.

Conclude with `h2`.
-/
theorem algebraMap_algebraicClosure_mem_deRhamFil_zero (P : LocPrime l) (x : Om l) : algebraMap (Om l) P.R.BdR x ∈ Fil P 0 := by
  obtain ⟨K, hK⟩ : ∃ K : FinExt l, x ∈ K.1 := ⟨⟨IntermediateField.adjoin ℚ_[l] {x},
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral _)⟩,
    IntermediateField.mem_adjoin_simple_self _ _⟩
  have h2 := ((P.PD K).Fil 0).smul_mem (⟨x, hK⟩ : ↥K.1) (P.PD K).one_mem
  rw [Algebra.smul_def, mul_one] at h2
  show algebraMap (Om l) P.R.BdR x ∈ ((P.PD (botExt l)).Fil 0 : Set P.R.BdR)
  rw [P.PD_Fil (botExt l) K 0]
  exact h2

/- English proof (translation)
Use `show (frobUr l ^ 0) c = c`. Rewrite using `[pow_zero]`. Both sides reduce to the same expression.
-/
theorem fr_zero (c : ↥(MaximalUnramifiedExtension l)) : fr l 0 c = c := by
  show (frobUr l ^ 0) c = c
  rw [pow_zero]
  rfl

/- English proof (translation)
Use `show (frobUr l ^ (a + b)) c = (frobUr l ^ a) ((frobUr l ^ b) c)`. Rewrite using `[pow_add]`. Both sides reduce to the same expression.
-/
theorem fr_add (a b : ℕ) (c : ↥(MaximalUnramifiedExtension l)) : fr l (a + b) c = fr l a (fr l b c) := by
  show (frobUr l ^ (a + b)) c = (frobUr l ^ a) ((frobUr l ^ b) c)
  rw [pow_add]
  rfl

/- English proof (translation)
Proceed by induction on `q with`. Consider the case `zero => simpa using fr_zero c`. Consider the case `succ q ih => rw [Nat.mul_succ, fr_add, hc, ih]`.
-/
theorem fr_mul_self {r : ℕ} {c : ↥(MaximalUnramifiedExtension l)} (hc : fr l r c = c) (q : ℕ) : fr l (r * q) c = c := by
  induction q with
  | zero => simpa using fr_zero c
  | succ q ih => rw [Nat.mul_succ, fr_add, hc, ih]

/- English proof (translation)
Use `conv_lhs => rw [← Nat.mod_add_div m r]`. Rewrite using `[fr_add, fr_mul_self hc]`.
-/
theorem fr_mod {r : ℕ} {c : ↥(MaximalUnramifiedExtension l)} (hc : fr l r c = c) (m : ℕ) : fr l m c = fr l (m % r) c := by
  conv_lhs => rw [← Nat.mod_add_div m r]
  rw [fr_add, fr_mul_self hc]

variable (P : LocPrime l) {K : FinExt l} {n : Type} [Fintype n] [DecidableEq n]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [matD, Matrix.map_apply]`. Rewrite using `[fr_mod (h.rat g i j) m]`.
-/
theorem matD_mod {r : ℕ} {ρ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)} (h : IsRat r ρ) (m : ℕ) (g : ↥(GK K)) :
    matD P ρ m g = matD P ρ (m % r) g := by
  ext i j
  simp only [matD, Matrix.map_apply]
  rw [fr_mod (h.rat g i j) m]

/- English proof (translation)
Simplify using `only [matD, Matrix.map_apply, kd, RingHom.comp_apply]`. Conclude with `algebraMap_algebraicClosure_mem_deRhamFil_zero P _`.
-/
theorem matD_mem (ρ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)) (m : ℕ) (g : ↥(GK K)) (i j : n) :
    matD P ρ m g i j ∈ Fil P 0 := by
  simp only [matD, Matrix.map_apply, kd, RingHom.comp_apply]
  exact algebraMap_algebraicClosure_mem_deRhamFil_zero P _

end GlobalTheory.PMon.FrameEquiv

namespace GlobalTheory.PMon.FrameEquiv

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l)

/- English proof (translation)
Take `⟨-, -, -, -, -, -, -, hact, hadd, h0, -⟩` from `GlobalTheory.T.deRhamPeriodRing_field_tPow_filtration_units l P _ T`. Conclude with `⟨hact, hadd, h0⟩`.
-/
theorem tz_facts {AI : LocAinf l P} (T : LocTied l P AI) :
    (∀ (a : ℤ) (g : GQ l), P.actQdR g (tz P a) = algebraMap ℚ_[l] P.R.BdR ((P.χQ g ^ a : ℚ_[l]ˣ) : ℚ_[l]) * tz P a) ∧
    (∀ a b : ℤ, tz P (a + b) = tz P a * tz P b) ∧ tz P 0 = 1 := by
  obtain ⟨-, -, -, -, -, -, -, hact, hadd, h0, -⟩ := GlobalTheory.T.deRhamPeriodRing_field_tPow_filtration_units l P _ T
  exact ⟨hact, hadd, h0⟩

variable {n : Type} [Fintype n] [DecidableEq n]

def tDiag (h : ∀ a : ℤ, tz P a * tz P (-a) = 1) (a : n → ℤ) : GL n P.R.BdR where
  val := Matrix.diagonal fun j => tz P (a j)
  inv := Matrix.diagonal fun j => tz P (-a j)
  val_inv := by rw [Matrix.diagonal_mul_diagonal]; simp [h]
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal]
    have : ∀ j, tz P (-a j) * tz P (a j) = 1 := fun j => by simpa using h (-a j)
    simp [this]

/- English proof (translation)
Introduce `l _ P AI T n _ _ K r ρ hρ`. Prove the components needed by the constructor for the conclusion. Introduce `hD`. Establish `H : ∀ m : Fin r, ∃ (U : GL n P.R.BdR) (w : n → ℤ), UnitM P U ∧ ∀ g : ↥(GK K), matD P ρ m g * (U : Matrix n n P.R.BdR).map (P.actQdR (g : GQ l)) = (U : Matrix n n P.R.BdR) * Matrix.diagonal fun j => algebraMap ℚ_[l] P.R.BdR ((P.χQ (g : GQ l) ^ w j : ℚ_[l]ˣ) : ℚ_[l])` using `fun m => by`. Take `⟨Q, hQ⟩` from `hD m`.

Conclude with `GlobalTheory.T.exists_bdRPlus_frame_of_period_matrix l P AI T n K (matD P ρ m) Q (matD_mem P ρ m) hQ`. Use `choose U w hU using H`. Conclude with `⟨w, fun m => ⟨U m, (hU m).1, (hU m).2⟩⟩`. Introduce and unpack `⟨w, hw⟩ m`. Take `⟨hact, hadd, h0⟩` from `tz_facts P T`.

Establish `hinv : ∀ a : ℤ, tz P a * tz P (-a) = 1` using `fun a => by rw [← hadd, add_neg_cancel, h0]`. Set `k : Fin r` to `⟨m % r, Nat.mod_lt _ hρ.pos⟩`. Take `⟨U, -, hU⟩` from `hw k`. Use `⟨U * tDiag P hinv (fun j => -w k j), fun g => ?_⟩` and prove the remaining obligations. Establish `hmap : ∀ (X Y : Matrix n n P.R.BdR), (X * Y).map (P.actQdR (g : GQ l)) = X.map (P.actQdR (g : GQ l)) * Y.map (P.actQdR (g : GQ l))` using `fun X Y => Matrix.map_mul (f := ((P.actQdR (g : GQ l) : P.R.BdR ≃ₐ[ℚ_[l]] P.R.BdR) : P.R.BdR →+* P.R.BdR))`.

Establish `hm : matD P ρ m g = matD P ρ (k : ℕ) g` using `matD_mod P hρ m g`. Rewrite using `[Units.val_mul, hmap, ← mul_assoc, hm, hU g, mul_assoc]`. Use `congr 1`. Use `show Matrix.diagonal _ * (Matrix.diagonal fun j => tz P (-w k j)).map (P.actQdR (g : GQ l)) = Matrix.diagonal fun j => tz P (-w k j)`. Rewrite using `[Matrix.diagonal_map (map_zero _), Matrix.diagonal_mul_diagonal]`.

Use `congr 1`. Use function extensionality and compare the values at `j`. Rewrite using `[hact, ← mul_assoc, ← map_mul, ← Units.val_mul, ← zpow_add, add_neg_cancel, zpow_zero, Units.val_one, map_one, one_mul]`.
-/
theorem frameEx : FrameEx := by
  intro l _ P AI T n _ _ K r ρ hρ
  constructor
  · intro hD
    have H : ∀ m : Fin r, ∃ (U : GL n P.R.BdR) (w : n → ℤ), UnitM P U ∧ ∀ g : ↥(GK K),
        matD P ρ m g * (U : Matrix n n P.R.BdR).map (P.actQdR (g : GQ l)) =
          (U : Matrix n n P.R.BdR) * Matrix.diagonal fun j =>
            algebraMap ℚ_[l] P.R.BdR ((P.χQ (g : GQ l) ^ w j : ℚ_[l]ˣ) : ℚ_[l]) := fun m => by
      obtain ⟨Q, hQ⟩ := hD m
      exact GlobalTheory.T.exists_bdRPlus_frame_of_period_matrix l P AI T n K (matD P ρ m) Q (matD_mem P ρ m) hQ
    choose U w hU using H
    exact ⟨w, fun m => ⟨U m, (hU m).1, (hU m).2⟩⟩
  · rintro ⟨w, hw⟩ m
    obtain ⟨hact, hadd, h0⟩ := tz_facts P T
    have hinv : ∀ a : ℤ, tz P a * tz P (-a) = 1 := fun a => by rw [← hadd, add_neg_cancel, h0]
    let k : Fin r := ⟨m % r, Nat.mod_lt _ hρ.pos⟩
    obtain ⟨U, -, hU⟩ := hw k
    refine ⟨U * tDiag P hinv (fun j => -w k j), fun g => ?_⟩
    have hmap : ∀ (X Y : Matrix n n P.R.BdR), (X * Y).map (P.actQdR (g : GQ l)) =
        X.map (P.actQdR (g : GQ l)) * Y.map (P.actQdR (g : GQ l)) := fun X Y =>
      Matrix.map_mul (f := ((P.actQdR (g : GQ l) : P.R.BdR ≃ₐ[ℚ_[l]] P.R.BdR) : P.R.BdR →+* P.R.BdR))
    have hm : matD P ρ m g = matD P ρ (k : ℕ) g := matD_mod P hρ m g
    rw [Units.val_mul, hmap, ← mul_assoc, hm, hU g, mul_assoc]
    congr 1
    show Matrix.diagonal _ * (Matrix.diagonal fun j => tz P (-w k j)).map (P.actQdR (g : GQ l)) =
      Matrix.diagonal fun j => tz P (-w k j)
    rw [Matrix.diagonal_map (map_zero _), Matrix.diagonal_mul_diagonal]
    congr 1
    funext j
    rw [hact, ← mul_assoc, ← map_mul, ← Units.val_mul, ← zpow_add, add_neg_cancel, zpow_zero,
      Units.val_one, map_one, one_mul]

end GlobalTheory.PMon.FrameEquiv
