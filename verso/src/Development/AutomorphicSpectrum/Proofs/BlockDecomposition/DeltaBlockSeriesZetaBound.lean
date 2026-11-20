import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsLatIntVec
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TsumCompBoundedFibresLeStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DeltaEqLatticeIndexStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LamIsLatticeStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeQuotientTorsionNonzeroStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorsionCardLeAbsNormPowStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemLatticeOfDualPairingStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DenominatorIndexBoundStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DenominatorNormQuadraticExtensionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdealPrincipalElementNormBoundStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RelativeNormCmAbsNormStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CmConjugationPropertiesStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorsionOrthogonalityIntegralSolutionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DeltaBlockMatrixMultiplicativeStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DeltaBlockQuotientInjectionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorsionNormZetaBoundStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DeltaBlockLowerBoundTorsionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorsionSumZetaBoundDeltaStatement
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SiegelND.Integ.Hua GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open scoped Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.SumD

/- English proof (translation)
Establish `hne : Ideal.span {ρ} ≠ ⊥`. Simplify `hρ` using `[Ideal.span_singleton_eq_bot]`. Take `⟨hfin, hcard⟩` from `GlobalTheory.T.torsion_card_le_absNorm_pow F 1 (intVec F 1) (isLat_intVec 1) (Ideal.span {ρ}) hne`. Rewrite `hcard` using `[pow_one]`. Distinguish the cases in `hb : ∃ D₀ : FQ F, a + ρ • D₀ = b`.

Take `⟨D₀, hD₀⟩` from `hb`. Set `φ : {D : FQ F // a + ρ • D = b} → {x : FQ F // ∀ r ∈ Ideal.span {ρ}, r • x = 0}` to `fun D => ⟨D.1 - D₀, by`. Introduce `r hr`. Take `⟨q, rfl⟩` from `Ideal.mem_span_singleton'.1 hr`. Establish `h1 : ρ • (D.1 - D₀) = 0`.

Establish `h2 : a + ρ • D.1 = a + ρ • D₀` using `D.2.trans hD₀.symm`. Rewrite using `[smul_sub, sub_eq_zero]`. Conclude with `add_left_cancel h2`. Rewrite using `[mul_smul, h1, smul_zero]⟩`. Establish `hφ : Function.Injective φ`.

Introduce `x y hxy`. Establish `h3 : x.1 - D₀ = y.1 - D₀` using `congrArg Subtype.val hxy`. Conclude with `Subtype.ext (sub_left_inj.1 h3)`. Establish `hF : Finite {D : FQ F // a + ρ • D = b}` using `Finite.of_injective φ hφ`. Conclude with `⟨hF, (Nat.card_le_card_of_injective φ hφ).trans hcard⟩`.

Establish `hE : IsEmpty {D : FQ F // a + ρ • D = b}` using `⟨fun D => hb ⟨D.1, D.2⟩⟩`. Conclude with `⟨inferInstance, by simp⟩`.
-/
theorem fibres (F : Type) [Field F] [NumberField F] (ρ : 𝓞 F) (hρ : ρ ≠ 0) (a : FQ F) (b : FQ F) :
    Finite {D : FQ F // a + ρ • D = b} ∧
      Nat.card {D : FQ F // a + ρ • D = b} ≤ Ideal.absNorm (Ideal.span {ρ}) := by
  have hne : Ideal.span {ρ} ≠ ⊥ := by
    simpa [Ideal.span_singleton_eq_bot] using hρ
  obtain ⟨hfin, hcard⟩ := GlobalTheory.T.torsion_card_le_absNorm_pow F 1 (intVec F 1) (isLat_intVec 1) (Ideal.span {ρ}) hne
  rw [pow_one] at hcard
  by_cases hb : ∃ D₀ : FQ F, a + ρ • D₀ = b
  · obtain ⟨D₀, hD₀⟩ := hb
    let φ : {D : FQ F // a + ρ • D = b} → {x : FQ F // ∀ r ∈ Ideal.span {ρ}, r • x = 0} :=
      fun D => ⟨D.1 - D₀, by
        intro r hr
        obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton'.1 hr
        have h1 : ρ • (D.1 - D₀) = 0 := by
          have h2 : a + ρ • D.1 = a + ρ • D₀ := D.2.trans hD₀.symm
          rw [smul_sub, sub_eq_zero]
          exact add_left_cancel h2
        rw [mul_smul, h1, smul_zero]⟩
    have hφ : Function.Injective φ := by
      intro x y hxy
      have h3 : x.1 - D₀ = y.1 - D₀ := congrArg Subtype.val hxy
      exact Subtype.ext (sub_left_inj.1 h3)
    have hF : Finite {D : FQ F // a + ρ • D = b} := Finite.of_injective φ hφ
    exact ⟨hF, (Nat.card_le_card_of_injective φ hφ).trans hcard⟩
  · have hE : IsEmpty {D : FQ F // a + ρ • D = b} := ⟨fun D => hb ⟨D.1, D.2⟩⟩
    exact ⟨inferInstance, by simp⟩

/- English proof (translation)
Unfold `den`. Use `congr 1`. Establish `hD : D = Submodule.Quotient.mk (Quotient.out D : Fin 1 → F)` using `(Quotient.out_eq D).symm`. Use `conv_rhs => rw [hD]`. Rewrite using `[← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_add]`.

Use `congr 1`. Use function extensionality and compare the values at `i`. Establish `hi : i = 0` using `Subsingleton.elim i 0`. Substitute `hi` using the available equality. Simplify using `[Algebra.smul_def]`.
-/
theorem den_eq (F : Type) [Field F] [NumberField F] (ρ : 𝓞 F) (f : F) (D : FQ F) :
    den F (f + ((ρ : 𝓞 F) : F) * (Quotient.out D : Fin 1 → F) 0) =
      Ideal.torsionOf (𝓞 F) (FQ F)
        ((Submodule.Quotient.mk (fun _ => f) : FQ F) + ρ • D) := by
  unfold den
  congr 1
  have hD : D = Submodule.Quotient.mk (Quotient.out D : Fin 1 → F) :=
    (Quotient.out_eq D).symm
  conv_rhs => rw [hD]
  rw [← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_add]
  congr 1
  funext i
  have hi : i = 0 := Subsingleton.elim i 0
  subst hi
  simp [Algebra.smul_def]

/- English proof (translation)
Establish `hδ' : (0 : ℝ) < δ` using `by exact_mod_cast Nat.pos_of_ne_zero hδ`. Establish `hN' : (0 : ℝ) < N` using `by exact_mod_cast Nat.pos_of_ne_zero hN`. Establish `hn' : (0 : ℝ) < n` using `by exact_mod_cast Nat.pos_of_ne_zero hn`. Establish `hle : (δ : ℝ) * (N : ℝ) ^ 2 * (n : ℝ) ^ 2 ≤ A` using `by exact_mod_cast h`. Establish `hpos : (0 : ℝ) < (δ : ℝ) * (N : ℝ) ^ 2 * (n : ℝ) ^ 2` using `by positivity`.

Establish `hsq : ∀ x : ℝ, 0 < x → (x ^ 2) ^ (-s) = x ^ (-(2 * s))`. Introduce `x hx`. Rewrite using `[← Real.rpow_natCast x 2, ← Real.rpow_mul hx.le]`. Use `congr 1`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow (by positivity) (by positivity), hsq _ hN', hsq _ hn']`.
-/
theorem term_le (A δ N n : ℕ) (s : ℝ) (hs : 0 < s) (hδ : δ ≠ 0) (hN : N ≠ 0) (hn : n ≠ 0)
    (h : δ * N ^ 2 * n ^ 2 ≤ A) :
    (A : ℝ) ^ (-s) ≤ (δ : ℝ) ^ (-s) * (N : ℝ) ^ (-(2 * s)) * (n : ℝ) ^ (-(2 * s)) := by
  have hδ' : (0 : ℝ) < δ := by exact_mod_cast Nat.pos_of_ne_zero hδ
  have hN' : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hle : (δ : ℝ) * (N : ℝ) ^ 2 * (n : ℝ) ^ 2 ≤ A := by exact_mod_cast h
  have hpos : (0 : ℝ) < (δ : ℝ) * (N : ℝ) ^ 2 * (n : ℝ) ^ 2 := by positivity
  have hsq : ∀ x : ℝ, 0 < x → (x ^ 2) ^ (-s) = x ^ (-(2 * s)) := by
    intro x hx
    rw [← Real.rpow_natCast x 2, ← Real.rpow_mul hx.le]
    congr 1
    push_cast
    ring
  calc (A : ℝ) ^ (-s) ≤ ((δ : ℝ) * (N : ℝ) ^ 2 * (n : ℝ) ^ 2) ^ (-s) :=
        Real.rpow_le_rpow_of_nonpos hpos hle (by linarith)
    _ = (δ : ℝ) ^ (-s) * (N : ℝ) ^ (-(2 * s)) * (n : ℝ) ^ (-(2 * s)) := by
        rw [Real.mul_rpow (by positivity) (by positivity),
          Real.mul_rpow (by positivity) (by positivity), hsq _ hN', hsq _ hn']

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hσ`. Take `⟨C, hC, hmink⟩` from `GlobalTheory.T.ideal_principal_element_norm_bound E`. Use `⟨C, hC, ?_⟩` and prove the remaining obligations. Introduce `m c hc u s hs`. Establish `hT : tor c u ≠ ⊥` using `GlobalTheory.T.lattice_quotient_torsion_nonzero E m (lam c) (GlobalTheory.T.lam_is_lattice E m c) (Submodule.Quotient.mk u)`.

Take `⟨t, htT, ht0, htC⟩` from `hmink (tor c u) hT`. Take `⟨f, hf⟩` from `GlobalTheory.T.delta_block_lower_bound_torsion F E σ hσ m c hc u t htT ht0`. Establish `hkt : Ideal.absNorm (Ideal.span {RingOfIntegers.norm F t}) = Ideal.absNorm (Ideal.span {t})` using `(GlobalTheory.T.relative_norm_cm_absNorm F E σ hσ t).2`. Establish `hNt : Ideal.absNorm (Ideal.span {t}) ≠ 0`. Rewrite using `[Ne, Ideal.absNorm_eq_zero_iff]`.

Simplify `ht0` using `[Ideal.span_singleton_eq_bot]`. Establish `hρ : RingOfIntegers.norm F t ≠ 0`. Introduce `h0`. Rewrite `hkt` using `[h0]`. Apply `hNt` to reduce the goal to its premises.

Rewrite using `[← hkt]`. Simplify using the standard rewrite rules. Generalize the expression as in `hρdef : RingOfIntegers.norm F t = ρ at hf hkt hρ`. Establish `hδ : delta c ≠ 0` using `(GlobalTheory.T.delta_eq_lattice_index E m c).1`. Establish `hN : Ideal.absNorm (tor c u) ≠ 0`.

Rewrite using `[Ne, Ideal.absNorm_eq_zero_iff]`. Conclude with `hT`. Establish `hδ' : (0 : ℝ) < delta c` using `by exact_mod_cast Nat.pos_of_ne_zero hδ`. Establish `hN' : (0 : ℝ) < Ideal.absNorm (tor c u)` using `by exact_mod_cast Nat.pos_of_ne_zero hN`. Establish `hs0 : 0 < s` using `by linarith`.

Take `⟨hsum, hzeta⟩` from `GlobalTheory.T.torsion_norm_zeta_bound F 1 (intVec F 1) (isLat_intVec 1) (2 * s - 1) (by linarith)`. Establish `hexp : (((1 : ℕ) : ℝ) + (2 * s - 1)) = 2 * s`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite `hsum`, `hzeta` using `[hexp]`.

Set `g : FQ F → ℝ` to `fun x => (Ideal.absNorm (Ideal.torsionOf (𝓞 F) (FQ F) x) : ℝ) ^ (-(2 * s))`. Establish `hg0 : ∀ x, 0 ≤ g x` using `fun x => Real.rpow_nonneg (Nat.cast_nonneg _) _`. Set `a : FQ F` to `Submodule.Quotient.mk (fun _ => f)`. Set `π : FQ F → FQ F` to `fun D => a + ρ • D`. Take `⟨hsum2, hle2⟩` from `GlobalTheory.T.tsum_comp_bounded_fibres_le (FQ F) (FQ F) π (Ideal.absNorm (Ideal.span {ρ})) (fun b => fibres F ρ hρ a b) g hg0 hsum`.

Set `P : ℝ` to `(delta c : ℝ) ^ (-s) * (Ideal.absNorm (tor c u) : ℝ) ^ (-(2 * s))`. Establish `hP : 0 ≤ P` using `by positivity`. Establish `hterm : ∀ D : FQ F, (delta (blk σ c u (algebraMap F E ((Quotient.out D : Fin 1 → F) 0))) : ℝ) ^ (-s) ≤ P * g (π D)`. Introduce `D`. Establish `h1` using `hf ((Quotient.out D : Fin 1 → F) 0)`.

Rewrite `h1` using `[den_eq F ρ f D]`. Establish `hn : Ideal.absNorm (Ideal.torsionOf (𝓞 F) (FQ F) (π D)) ≠ 0`. Rewrite using `[Ne, Ideal.absNorm_eq_zero_iff]`. Conclude with `GlobalTheory.T.lattice_quotient_torsion_nonzero F 1 (intVec F 1) (isLat_intVec 1) (π D)`. Conclude with `term_le _ _ _ _ s hs0 hδ hN hn h1`.

Establish `hnn : ∀ D : FQ F, 0 ≤ (delta (blk σ c u (algebraMap F E ((Quotient.out D : Fin 1 → F) 0))) : ℝ) ^ (-s)` using `fun D => Real.rpow_nonneg (Nat.cast_nonneg _) _`. Establish `hsumP : Summable (fun D : FQ F => P * g (π D))` using `hsum2.mul_left P`. Use `⟨Summable.of_nonneg_of_le hnn hterm hsumP, ?_⟩` and prove the remaining obligations. Establish `hS : 0 ≤ ∑' x, g x` using `tsum_nonneg hg0`. Establish `hZ : 0 ≤ zetaR F (2 * s - 1)` using `hS.trans hzeta`.

Establish `hkC : (Ideal.absNorm (Ideal.span {ρ}) : ℝ) ≤ C * Ideal.absNorm (tor c u)`. Rewrite using `[hkt]`. Conclude with `htC`. Establish `hpow : (Ideal.absNorm (tor c u) : ℝ) ^ (-(2 * s)) * (Ideal.absNorm (tor c u) : ℝ) = (Ideal.absNorm (tor c u) : ℝ) ^ (1 - 2 * s)`. Rewrite using `[show (1 - 2 * s) = -(2 * s) + 1 by ring, Real.rpow_add hN', Real.rpow_one]`.

Combine the equalities or inequalities in the displayed calculation. Use `mul_le_mul_of_nonneg_left ?_ hP` and prove the remaining obligations. Conclude with `mul_le_mul hkC hzeta hS (by positivity)`. Use `_ = C * zetaR F (2 * s - 1) * (delta c : ℝ) ^ (-s) * (Ideal.absNorm (tor c u) : ℝ) ^ (1 - 2 * s) := by`. Rewrite using `[← hpow]`.

Simplify using `only [P]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sum_delta_le : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (c : Matrix (Fin m) (Fin m) E), (∀ a b, σ (c b a) = c a b) → ∀ (u : Fin m → E) (s : ℝ), 1 < s → Summable (fun D : FQ F => (delta (blk σ c u (algebraMap F E ((Quotient.out D : Fin 1 → F) 0))) : ℝ) ^ (-s)) ∧ ∑' D : FQ F, (delta (blk σ c u (algebraMap F E ((Quotient.out D : Fin 1 → F) 0))) : ℝ) ^ (-s) ≤ C * zetaR F (2 * s - 1) * (delta c : ℝ) ^ (-s) * (Ideal.absNorm (tor c u) : ℝ) ^ (1 - 2 * s) := by
  intro F E _ _ _ _ _ σ hσ
  obtain ⟨C, hC, hmink⟩ := GlobalTheory.T.ideal_principal_element_norm_bound E
  refine ⟨C, hC, ?_⟩
  intro m c hc u s hs
  have hT : tor c u ≠ ⊥ :=
    GlobalTheory.T.lattice_quotient_torsion_nonzero E m (lam c) (GlobalTheory.T.lam_is_lattice E m c) (Submodule.Quotient.mk u)
  obtain ⟨t, htT, ht0, htC⟩ := hmink (tor c u) hT
  obtain ⟨f, hf⟩ := GlobalTheory.T.delta_block_lower_bound_torsion F E σ hσ m c hc u t htT ht0
  have hkt : Ideal.absNorm (Ideal.span {RingOfIntegers.norm F t}) =
      Ideal.absNorm (Ideal.span {t}) := (GlobalTheory.T.relative_norm_cm_absNorm F E σ hσ t).2
  have hNt : Ideal.absNorm (Ideal.span {t}) ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    simpa [Ideal.span_singleton_eq_bot] using ht0
  have hρ : RingOfIntegers.norm F t ≠ 0 := by
    intro h0
    rw [h0] at hkt
    apply hNt
    rw [← hkt]
    simp
  generalize hρdef : RingOfIntegers.norm F t = ρ at hf hkt hρ
  have hδ : delta c ≠ 0 := (GlobalTheory.T.delta_eq_lattice_index E m c).1
  have hN : Ideal.absNorm (tor c u) ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact hT
  have hδ' : (0 : ℝ) < delta c := by exact_mod_cast Nat.pos_of_ne_zero hδ
  have hN' : (0 : ℝ) < Ideal.absNorm (tor c u) := by exact_mod_cast Nat.pos_of_ne_zero hN
  have hs0 : 0 < s := by linarith
  obtain ⟨hsum, hzeta⟩ := GlobalTheory.T.torsion_norm_zeta_bound F 1 (intVec F 1) (isLat_intVec 1) (2 * s - 1) (by linarith)
  have hexp : (((1 : ℕ) : ℝ) + (2 * s - 1)) = 2 * s := by
    push_cast
    ring
  rw [hexp] at hsum hzeta
  let g : FQ F → ℝ := fun x => (Ideal.absNorm (Ideal.torsionOf (𝓞 F) (FQ F) x) : ℝ) ^ (-(2 * s))
  have hg0 : ∀ x, 0 ≤ g x := fun x => Real.rpow_nonneg (Nat.cast_nonneg _) _
  let a : FQ F := Submodule.Quotient.mk (fun _ => f)
  let π : FQ F → FQ F := fun D => a + ρ • D
  obtain ⟨hsum2, hle2⟩ := GlobalTheory.T.tsum_comp_bounded_fibres_le (FQ F) (FQ F) π (Ideal.absNorm (Ideal.span {ρ}))
    (fun b => fibres F ρ hρ a b) g hg0 hsum
  let P : ℝ := (delta c : ℝ) ^ (-s) * (Ideal.absNorm (tor c u) : ℝ) ^ (-(2 * s))
  have hP : 0 ≤ P := by positivity
  have hterm : ∀ D : FQ F,
      (delta (blk σ c u (algebraMap F E ((Quotient.out D : Fin 1 → F) 0))) : ℝ) ^ (-s) ≤
        P * g (π D) := by
    intro D
    have h1 := hf ((Quotient.out D : Fin 1 → F) 0)
    rw [den_eq F ρ f D] at h1
    have hn : Ideal.absNorm (Ideal.torsionOf (𝓞 F) (FQ F) (π D)) ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff]
      exact GlobalTheory.T.lattice_quotient_torsion_nonzero F 1 (intVec F 1) (isLat_intVec 1) (π D)
    exact term_le _ _ _ _ s hs0 hδ hN hn h1
  have hnn : ∀ D : FQ F,
      0 ≤ (delta (blk σ c u (algebraMap F E ((Quotient.out D : Fin 1 → F) 0))) : ℝ) ^ (-s) :=
    fun D => Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hsumP : Summable (fun D : FQ F => P * g (π D)) := hsum2.mul_left P
  refine ⟨Summable.of_nonneg_of_le hnn hterm hsumP, ?_⟩
  have hS : 0 ≤ ∑' x, g x := tsum_nonneg hg0
  have hZ : 0 ≤ zetaR F (2 * s - 1) := hS.trans hzeta
  have hkC : (Ideal.absNorm (Ideal.span {ρ}) : ℝ) ≤ C * Ideal.absNorm (tor c u) := by
    rw [hkt]
    exact htC
  have hpow : (Ideal.absNorm (tor c u) : ℝ) ^ (-(2 * s)) * (Ideal.absNorm (tor c u) : ℝ) =
      (Ideal.absNorm (tor c u) : ℝ) ^ (1 - 2 * s) := by
    rw [show (1 - 2 * s) = -(2 * s) + 1 by ring, Real.rpow_add hN', Real.rpow_one]
  calc ∑' D : FQ F, (delta (blk σ c u (algebraMap F E ((Quotient.out D : Fin 1 → F) 0))) : ℝ) ^ (-s)
      ≤ ∑' D : FQ F, P * g (π D) :=
        (Summable.of_nonneg_of_le hnn hterm hsumP).tsum_le_tsum hterm hsumP
    _ = P * ∑' D : FQ F, g (π D) := tsum_mul_left
    _ ≤ P * ((Ideal.absNorm (Ideal.span {ρ}) : ℝ) * ∑' x, g x) :=
        mul_le_mul_of_nonneg_left hle2 hP
    _ ≤ P * ((C * Ideal.absNorm (tor c u)) * zetaR F (2 * s - 1)) := by
        refine mul_le_mul_of_nonneg_left ?_ hP
        exact mul_le_mul hkC hzeta hS (by positivity)
    _ = C * zetaR F (2 * s - 1) * (delta c : ℝ) ^ (-s) *
          (Ideal.absNorm (tor c u) : ℝ) ^ (1 - 2 * s) := by
        rw [← hpow]
        simp only [P]
        ring

end GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.SumD
