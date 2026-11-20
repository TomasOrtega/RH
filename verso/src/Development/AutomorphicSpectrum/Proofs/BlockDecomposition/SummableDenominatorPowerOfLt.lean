import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaPartD
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundUnitary
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermInf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermOf
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FiniteAdeleTopologyStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsLatIntVec
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DeltaEqLatticeIndexStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DeltaBlockQuotientInjectionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorsionSumZetaBoundDeltaStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DeltaBlockSeriesZetaBoundStatement

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped Matrix

/- English proof (translation)
The claim follows from `tsum_nonneg fun _ => Real.rpow_nonneg (Nat.cast_nonneg _) _`.
-/
theorem zetaR_nonneg (K : Type) [Field K] [NumberField K] (r : ℝ) : 0 ≤ zetaR K r :=
  tsum_nonneg fun _ => Real.rpow_nonneg (Nat.cast_nonneg _) _

/- English proof (translation)
Take `⟨C, hC, hD⟩` from `GlobalTheory.T.delta_block_series_zeta_bound F E σ hσ`. Take `⟨ι, hinj, hι⟩` from `GlobalTheory.T.delta_block_quotient_injection F E σ hσ m`. Establish `hm : (0 : ℝ) ≤ m` using `Nat.cast_nonneg m`. Establish `hs1 : 1 < s` using `by linarith`. Use `set G : (hermE σ m ⧸ hermO σ m) × ((Fin m → E) ⧸ intVec E m) × FQ F → ℝ := fun p => (delta (blk σ (Quotient.out p.1).1 (Quotient.out p.2.1) (algebraMap F E ((Quotient.out p.2.2 : Fin 1 → F) 0))) : ℝ) ^ (-s) with hG`.

Establish `hG0 : 0 ≤ G` using `fun p => Real.rpow_nonneg (Nat.cast_nonneg _) _`. Use `set r : ℝ := 2 * s - 1 - m with hr`. Establish `hr1 : 1 < r` using `by rw [hr]; linarith`. Establish `hexp : 1 - 2 * s = -((m : ℝ) + r)` using `by rw [hr]; ring`. Establish `hin : ∀ (x : hermE σ m ⧸ hermO σ m) (U : (Fin m → E) ⧸ intVec E m), Summable (fun D : FQ F => G (x, U, D)) ∧ ∑' D : FQ F, G (x, U, D) ≤ C * zetaR F (2 * s - 1) * (delta (Quotient.out x).1 : ℝ) ^ (-s) * (Ideal.absNorm (tor (Quotient.out x).1 (Quotient.out U)) : ℝ) ^ (-((m : ℝ) + r …`.

Introduce `x U`. Use `hD m (Quotient.out x).1 (Quotient.out x).2 (Quotient.out U) s hs1` as an intermediate fact. Rewrite `this` using `[hexp]`. Conclude with `this`. Use `set A : ℝ := C * zetaR F (2 * s - 1) with hA`.

Establish `hA0 : 0 ≤ A` using `mul_nonneg hC.le (zetaR_nonneg _ _)`. Establish `hmid : ∀ x : hermE σ m ⧸ hermO σ m, Summable (fun q : ((Fin m → E) ⧸ intVec E m) × FQ F => G (x, q)) ∧ ∑' q : ((Fin m → E) ⧸ intVec E m) × FQ F, G (x, q) ≤ A * zetaR E r * (delta (Quotient.out x).1 : ℝ) ^ (-(s - 1))`. Introduce `x`. Take `⟨hU, hUle⟩` from `GlobalTheory.T.torsion_sum_zeta_bound_delta E m (Quotient.out x).1 r hr1`. Establish `hδ : (0 : ℝ) < delta (Quotient.out x).1` using `Nat.cast_pos.mpr (Nat.pos_of_ne_zero (GlobalTheory.T.delta_eq_lattice_index E m _).1)`.

Use `set B : ℝ := A * (delta (Quotient.out x).1 : ℝ) ^ (-s) with hB`. Establish `hB0 : 0 ≤ B` using `mul_nonneg hA0 (Real.rpow_nonneg hδ.le _)`. Establish `hsum : Summable (fun U : (Fin m → E) ⧸ intVec E m => ∑' D : FQ F, G (x, U, D))` using `Summable.of_nonneg_of_le (fun U => tsum_nonneg fun D => hG0 _) (fun U => (hin x U).2) (hU.mul_left B)`. Establish `hS : Summable (fun q : ((Fin m → E) ⧸ intVec E m) × FQ F => G (x, q))` using `(summable_prod_of_nonneg (fun q => hG0 (x, q))).mpr ⟨fun U => (hin x U).1, hsum⟩`. Use `⟨hS, ?_⟩` and prove the remaining obligations.

Rewrite using `[hS.tsum_prod' (fun U => (hin x U).1)]`. Combine the equalities or inequalities in the displayed calculation. Establish `: (delta (Quotient.out x).1 : ℝ) ^ (-(s - 1)) = (delta (Quotient.out x).1 : ℝ) ^ (-s) * delta (Quotient.out x).1`. Rewrite using `[show -(s - 1) = -s + 1 by ring, Real.rpow_add hδ, Real.rpow_one]`. Rewrite using `[this, hB]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hGs : Summable G`. Use `(summable_prod_of_nonneg hG0).mpr ⟨fun x => (hmid x).1, ?_⟩` and prove the remaining obligations. Conclude with `Summable.of_nonneg_of_le (fun x => tsum_nonneg fun q => hG0 _) (fun x => (hmid x).2) (ih.mul_left _)`. Use `(hGs.comp_injective hinj).congr fun x => ?_` and prove the remaining obligations.

Simplify using `only [Function.comp, hG, hι x]`.
-/
theorem step {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) (m : ℕ) (s : ℝ) (hs : (m : ℝ) + 1 < s)
    (ih : Summable (fun x : hermE σ m ⧸ hermO σ m => (delta (Quotient.out x).1 : ℝ) ^ (-(s - 1)))) :
    Summable (fun x : hermE σ (m + 1) ⧸ hermO σ (m + 1) =>
      (delta (Quotient.out x).1 : ℝ) ^ (-s)) := by
  obtain ⟨C, hC, hD⟩ := GlobalTheory.T.delta_block_series_zeta_bound F E σ hσ
  obtain ⟨ι, hinj, hι⟩ := GlobalTheory.T.delta_block_quotient_injection F E σ hσ m
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hs1 : 1 < s := by linarith
  set G : (hermE σ m ⧸ hermO σ m) × ((Fin m → E) ⧸ intVec E m) × FQ F → ℝ := fun p =>
    (delta (blk σ (Quotient.out p.1).1 (Quotient.out p.2.1)
      (algebraMap F E ((Quotient.out p.2.2 : Fin 1 → F) 0))) : ℝ) ^ (-s) with hG
  have hG0 : 0 ≤ G := fun p => Real.rpow_nonneg (Nat.cast_nonneg _) _
  set r : ℝ := 2 * s - 1 - m with hr
  have hr1 : 1 < r := by rw [hr]; linarith
  have hexp : 1 - 2 * s = -((m : ℝ) + r) := by rw [hr]; ring

  have hin : ∀ (x : hermE σ m ⧸ hermO σ m) (U : (Fin m → E) ⧸ intVec E m),
      Summable (fun D : FQ F => G (x, U, D)) ∧
      ∑' D : FQ F, G (x, U, D) ≤ C * zetaR F (2 * s - 1) * (delta (Quotient.out x).1 : ℝ) ^ (-s) *
        (Ideal.absNorm (tor (Quotient.out x).1 (Quotient.out U)) : ℝ) ^ (-((m : ℝ) + r)) := by
    intro x U
    have := hD m (Quotient.out x).1 (Quotient.out x).2 (Quotient.out U) s hs1
    rw [hexp] at this
    exact this
  set A : ℝ := C * zetaR F (2 * s - 1) with hA
  have hA0 : 0 ≤ A := mul_nonneg hC.le (zetaR_nonneg _ _)
  have hmid : ∀ x : hermE σ m ⧸ hermO σ m,
      Summable (fun q : ((Fin m → E) ⧸ intVec E m) × FQ F => G (x, q)) ∧
      ∑' q : ((Fin m → E) ⧸ intVec E m) × FQ F, G (x, q) ≤
        A * zetaR E r * (delta (Quotient.out x).1 : ℝ) ^ (-(s - 1)) := by
    intro x
    obtain ⟨hU, hUle⟩ := GlobalTheory.T.torsion_sum_zeta_bound_delta E m (Quotient.out x).1 r hr1
    have hδ : (0 : ℝ) < delta (Quotient.out x).1 :=
      Nat.cast_pos.mpr (Nat.pos_of_ne_zero (GlobalTheory.T.delta_eq_lattice_index E m _).1)
    set B : ℝ := A * (delta (Quotient.out x).1 : ℝ) ^ (-s) with hB
    have hB0 : 0 ≤ B := mul_nonneg hA0 (Real.rpow_nonneg hδ.le _)
    have hsum : Summable (fun U : (Fin m → E) ⧸ intVec E m => ∑' D : FQ F, G (x, U, D)) :=
      Summable.of_nonneg_of_le (fun U => tsum_nonneg fun D => hG0 _) (fun U => (hin x U).2)
        (hU.mul_left B)
    have hS : Summable (fun q : ((Fin m → E) ⧸ intVec E m) × FQ F => G (x, q)) :=
      (summable_prod_of_nonneg (fun q => hG0 (x, q))).mpr ⟨fun U => (hin x U).1, hsum⟩
    refine ⟨hS, ?_⟩
    rw [hS.tsum_prod' (fun U => (hin x U).1)]
    calc ∑' U : (Fin m → E) ⧸ intVec E m, ∑' D : FQ F, G (x, U, D)
        ≤ ∑' U : (Fin m → E) ⧸ intVec E m, B *
            (Ideal.absNorm (tor (Quotient.out x).1 (Quotient.out U)) : ℝ) ^ (-((m : ℝ) + r)) :=
          hsum.tsum_le_tsum (fun U => (hin x U).2) (hU.mul_left B)
      _ = B * ∑' U : (Fin m → E) ⧸ intVec E m,
            (Ideal.absNorm (tor (Quotient.out x).1 (Quotient.out U)) : ℝ) ^ (-((m : ℝ) + r)) :=
          tsum_mul_left
      _ ≤ B * (delta (Quotient.out x).1 * zetaR E r) := mul_le_mul_of_nonneg_left hUle hB0
      _ = A * zetaR E r * (delta (Quotient.out x).1 : ℝ) ^ (-(s - 1)) := by
          have : (delta (Quotient.out x).1 : ℝ) ^ (-(s - 1)) =
              (delta (Quotient.out x).1 : ℝ) ^ (-s) * delta (Quotient.out x).1 := by
            rw [show -(s - 1) = -s + 1 by ring, Real.rpow_add hδ, Real.rpow_one]
          rw [this, hB]
          ring
  have hGs : Summable G := by
    refine (summable_prod_of_nonneg hG0).mpr ⟨fun x => (hmid x).1, ?_⟩
    exact Summable.of_nonneg_of_le (fun x => tsum_nonneg fun q => hG0 _) (fun x => (hmid x).2)
      (ih.mul_left _)
  refine (hGs.comp_injective hinj).congr fun x => ?_
  simp only [Function.comp, hG, hι x]

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hσ n`. Proceed by induction on `n with`. Consider the case `zero`. Introduce `s _`. Use `haveI : Subsingleton (hermE σ 0) := ⟨fun a b => Subtype.ext (Matrix.ext fun i => i.elim0)⟩`.

Use `haveI : Subsingleton (hermE σ 0 ⧸ hermO σ 0) := QuotientAddGroup.mk_surjective.subsingleton`. Conclude with `summable_of_finite_support (Set.toFinite _)`. Consider the case `succ n ih`. Introduce `s hs`. Move the coercions through the operations in `at hs`.

Conclude with `step σ hσ n s hs (ih (s - 1) (by linarith))`.
-/
theorem summable_delta_rpow : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (n : ℕ) (s : ℝ), (n : ℝ) < s →
    Summable (fun x : hermE σ n ⧸ hermO σ n => (delta (Quotient.out x).1 : ℝ) ^ (-s)) := by
  intro F E _ _ _ _ _ σ hσ n
  induction n with
  | zero =>
    intro s _
    haveI : Subsingleton (hermE σ 0) := ⟨fun a b => Subtype.ext (Matrix.ext fun i => i.elim0)⟩
    haveI : Subsingleton (hermE σ 0 ⧸ hermO σ 0) := QuotientAddGroup.mk_surjective.subsingleton
    exact summable_of_finite_support (Set.toFinite _)
  | succ n ih =>
    intro s hs
    push_cast at hs
    exact step σ hσ n s hs (ih (s - 1) (by linarith))

end GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
