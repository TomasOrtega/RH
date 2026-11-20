import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.LocalDefs
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResAlgSplitTwo
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FixedNondeg
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedQuotientCardStatement
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens GlobalTheory.CompanionTheory.SiegLoc Filter Topology

namespace GlobalTheory.CompanionTheory.SiegLoc.NuDiag

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact.

By extensionality, compare the relevant components. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Supply the required witnesses or components. Assume the hypotheses and unpack their components.

Supply the required witnesses or components. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.
-/
private theorem card_range_vecMul_mul_mul_eq_of_mul_eq_one {Q : Type} [CommRing Q] {n : ℕ}
    (H P P' G G' : Matrix (Fin n) (Fin n) Q) (hP : P' * P = 1) (hG : G * G' = 1) :
    Nat.card (Set.range fun z : Fin n → Q => Matrix.vecMul z (P * H * G)) =
      Nat.card (Set.range fun x : Fin n → Q => Matrix.vecMul x H) := by
  have hinj : Function.Injective fun y : Fin n → Q => Matrix.vecMul y G := by
    intro y₁ y₂ hy
    have h := congrArg (fun v => Matrix.vecMul v G') hy
    simpa only [Matrix.vecMul_vecMul, hG, Matrix.vecMul_one] using h
  have hrange : (Set.range fun z : Fin n → Q => Matrix.vecMul z (P * H * G)) =
      (fun y => Matrix.vecMul y G) '' Set.range fun x : Fin n → Q => Matrix.vecMul x H := by
    ext v
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨Matrix.vecMul (Matrix.vecMul z P) H, ⟨Matrix.vecMul z P, rfl⟩,
        by simp only [Matrix.vecMul_vecMul]⟩
    · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨Matrix.vecMul x P', by
        simp only [Matrix.vecMul_vecMul, ← Matrix.mul_assoc, hP, Matrix.one_mul]⟩
  rw [hrange, Nat.card_image_of_injective hinj]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem cT_mul' {R : Type} [CommRing R] (σ : R →+* R) {n : ℕ} (a b : Matrix (Fin n) (Fin n) R) :
    cT σ (a * b) = cT σ b * cT σ a := by
  simp only [PositivityTheory.PfSWUS.Loc.cT, Matrix.map_mul, Matrix.transpose_mul]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem cT_one' {R : Type} [CommRing R] (σ : R →+* R) {n : ℕ} :
    cT σ (1 : Matrix (Fin n) (Fin n) R) = 1 := by
  simp only [PositivityTheory.PfSWUS.Loc.cT, Matrix.map_one _ (map_zero σ) (map_one σ), Matrix.transpose_one]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem red_mul' {R : Type} [CommRing R] (ϖ : R) (k : ℕ) {n : ℕ} (a b : Matrix (Fin n) (Fin n) R) :
    red ϖ k (a * b) = red ϖ k a * red ϖ k b := by
  simp only [PositivityTheory.PfSWUS.Loc.red, Matrix.map_mul]

/- English proof (translation)
Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem red_one' {R : Type} [CommRing R] (ϖ : R) (k : ℕ) {n : ℕ} :
    red ϖ k (1 : Matrix (Fin n) (Fin n) R) = 1 := by
  simp only [PositivityTheory.PfSWUS.Loc.red]
  exact Matrix.map_one _ (map_zero _) (map_one _)

/- English proof (translation)
Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components.

Supply the required witnesses or components. Fix the arbitrary inputs or assume the hypotheses. Supply the required witnesses or components. Rewrite the conclusion using the stated equalities.
-/
theorem card_range_vecMul_diagonal {A : Type} [CommRing A] {n : ℕ} (e : Fin n → A) :
    Nat.card (Set.range fun z : Fin n → A => Matrix.vecMul z (Matrix.diagonal e)) =
      ∏ i : Fin n, Nat.card (Set.range fun w : A => w * e i) := by
  have hset : (Set.range fun z : Fin n → A => Matrix.vecMul z (Matrix.diagonal e)) =
      Set.pi Set.univ (fun i => Set.range fun w : A => w * e i) := by
    ext v
    simp only [Set.mem_range, Set.mem_univ_pi]
    constructor
    · rintro ⟨z, rfl⟩ i
      exact ⟨z i, by rw [Matrix.vecMul_diagonal]⟩
    · intro hv
      choose z hz using hv
      exact ⟨z, funext fun i => by rw [Matrix.vecMul_diagonal, hz i]⟩
  rw [hset, Nat.card_congr (Equiv.Set.univPi _), Nat.card_pi]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem nuAt_eq_prod : ∀ (R : Type) [CommRing R] (σ : R →+* R) (ϖ : R), σ ϖ = ϖ → (∀ a, σ (σ a) = a) → ∀ (k : ℕ) [Fintype (R ⧸ lev ϖ k)] (n : ℕ) (h g g' : Matrix (Fin n) (Fin n) R) (d : Fin n → R), g * g' = 1 → g' * g = 1 → cT σ g * h * g = Matrix.diagonal d → nuAt ϖ (red ϖ k h) = ∏ i : Fin n, Nat.card (Set.range fun w : R ⧸ lev ϖ k => w * Ideal.Quotient.mk (lev ϖ k) (d i)) := by
  intro R _ σ ϖ _ _ k _ n h g g' d hgg' hg'g hdiag
  have hP : PositivityTheory.PfSWUS.Loc.red ϖ k (PositivityTheory.PfSWUS.Loc.cT σ g') *
      PositivityTheory.PfSWUS.Loc.red ϖ k (PositivityTheory.PfSWUS.Loc.cT σ g) = 1 := by
    rw [← GlobalTheory.CompanionTheory.SiegLoc.NuDiag.red_mul', ← GlobalTheory.CompanionTheory.SiegLoc.NuDiag.cT_mul', hgg',
      GlobalTheory.CompanionTheory.SiegLoc.NuDiag.cT_one', GlobalTheory.CompanionTheory.SiegLoc.NuDiag.red_one']
  have hG : PositivityTheory.PfSWUS.Loc.red ϖ k g * PositivityTheory.PfSWUS.Loc.red ϖ k g' = 1 := by
    rw [← GlobalTheory.CompanionTheory.SiegLoc.NuDiag.red_mul', hgg', GlobalTheory.CompanionTheory.SiegLoc.NuDiag.red_one']
  have hD : PositivityTheory.PfSWUS.Loc.red ϖ k (PositivityTheory.PfSWUS.Loc.cT σ g) * PositivityTheory.PfSWUS.Loc.red ϖ k h *
      PositivityTheory.PfSWUS.Loc.red ϖ k g =
        Matrix.diagonal fun i => Ideal.Quotient.mk (PositivityTheory.PfSWUS.Loc.lev ϖ k) (d i) := by
    rw [← GlobalTheory.CompanionTheory.SiegLoc.NuDiag.red_mul', ← GlobalTheory.CompanionTheory.SiegLoc.NuDiag.red_mul', hdiag]
    simp only [PositivityTheory.PfSWUS.Loc.red]
    exact Matrix.diagonal_map (map_zero _)
  unfold PositivityTheory.PfSWUS.Loc.nuAt
  refine Eq.trans ?_ (GlobalTheory.CompanionTheory.SiegLoc.NuDiag.card_range_vecMul_diagonal
    (fun i => Ideal.Quotient.mk (PositivityTheory.PfSWUS.Loc.lev ϖ k) (d i)))
  rw [← hD]
  exact (card_range_vecMul_mul_mul_eq_of_mul_eq_one _ _ _ _ _ hP hG).symm

end GlobalTheory.CompanionTheory.SiegLoc.NuDiag
