import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStdCharNegOneOfStandardTraceAdelicAddChar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyConstantFinprodSchwartzBruhatFiniteAdel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasCompactSupportFinprodSchwartzBruhatFiniteAdel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicRapidDecayOfMemAdelicSchwartzSpace

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

noncomputable section

namespace GlobalTheory.ThetaLinePure

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

variable {F : Type} [Field F] [NumberField F]

section Helpers
open scoped Classical

/- English proof (translation)
Establish `h1 : ‖z‖ ≤ ‖z + a‖ + ‖a‖`. Combine the equalities or inequalities in the displayed calculation. Use polynomial arithmetic with `[norm_nonneg a, norm_nonneg (z + a), mul_nonneg (norm_nonneg a) (norm_nonneg (z + a))]`.
-/
theorem norm_le_mul {V : Type} [NormedAddCommGroup V] (z a : V) : ‖z‖ ≤ (1 + ‖a‖) * (1 + ‖z + a‖) := by
  have h1 : ‖z‖ ≤ ‖z + a‖ + ‖a‖ := by
    calc ‖z‖ = ‖(z + a) - a‖ := by rw [add_sub_cancel_right]
      _ ≤ ‖z + a‖ + ‖a‖ := norm_sub_le _ _
  nlinarith [norm_nonneg a, norm_nonneg (z + a), mul_nonneg (norm_nonneg a) (norm_nonneg (z + a))]

/- English proof (translation)
Take `⟨B, hB⟩` from `hR.1.continuous.bounded_above_of_compact_support hR.2`. Take `⟨N, hN, hK⟩` from `exists_nat_mul_integral_of_isCompact F hR.2.isCompact`. Use `haveI := discreteTopology_denomLattice F κ hN`. Use `set L := denomLattice F κ N`. Use `⟨Module.finrank ℤ L + 1, fun a => ?_⟩` and prove the remaining obligations.

Use `set m := Module.finrank ℤ L + 1`. Establish `hw` using `ZLattice.summable_norm_pow_inv L m (Nat.lt_succ_self _)`. Set `S : Set (κ → F)` to `{ξ | (fun i => mixedEmbedding F (ξ i)) ∈ L}`. Establish `hsupp : ∀ ξ : κ → F, ξ ∉ Set.range (Subtype.val : S → κ → F) → ‖R (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i))‖ / (1 + ‖(fun i => mixedEmbedding F (ξ i)) + a‖) ^ m = 0`. Introduce `ξ hξ`.

Assume the negation of the conclusion as `h0`. Apply `hξ` to reduce the goal to its premises. Establish `h0' : R (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i)) ≠ 0`. Introduce `h`. Apply `h0` to reduce the goal to its premises.

Rewrite using `[h, norm_zero, zero_div]`. Use `⟨⟨ξ, fun i => ?_⟩, rfl⟩` and prove the remaining obligations. Take `⟨y, hy⟩` from `(IntegralFinAdele.integral_finiteAdele_properties F).2.2.2.1 ((N : F) * ξ i) fun v => by`. Rewrite using `[map_mul, map_natCast]`. Conclude with `hK _ (subset_tsupport _ h0') i v`.

Use `⟨y, ?_⟩` and prove the remaining obligations. Establish `h2` using `congrArg (mixedEmbedding F) hy`. Rewrite `h2` using `[← nsmul_eq_mul, map_nsmul, ← Nat.cast_smul_eq_nsmul ℝ]`. Conclude with `h2.symm`. Use `((Subtype.val_injective (p := fun ξ => ξ ∈ S)).summable_iff hsupp).1 ?_` and prove the remaining obligations.

Set `j : S → L` to `fun ξ => ⟨_, ξ.2⟩`. Establish `hj : Function.Injective j` using `fun x y h => Subtype.ext (funext fun i => mixedEmbedding_injective F (congrFun (congrArg Subtype.val h) i))`. Establish `hs : Summable fun ξ : S => max B 0 * (1 + ‖a‖) ^ m * ‖j ξ‖⁻¹ ^ m` using `(hw.comp_injective hj).mul_left _`. Use `Summable.of_norm_bounded_eventually hs ?_` and prove the remaining obligations. Establish `h0S : (fun i => mixedEmbedding F ((0 : κ → F) i)) ∈ L`.

Simplify using `only [Pi.zero_apply, map_zero]`. Conclude with `L.zero_mem`. Use `filter_upwards [Filter.eventually_cofinite_ne (⟨0, h0S⟩ : S)] with ξ hne`. Establish `hz : j ξ ≠ 0` using `fun h => hne (hj (h.trans (Subtype.ext (funext fun i => (map_zero (mixedEmbedding F)).symm))))`. Establish `hzn : ‖j ξ‖ = ‖((j ξ : L) : κ → mixedEmbedding.mixedSpace F)‖` using `by simp`.

Establish `key : ∀ z : κ → mixedEmbedding.mixedSpace F, 0 < ‖z‖ → ∀ y : κ → FiniteAdeleRing (𝓞 F) F, ‖‖R y‖ / (1 + ‖z + a‖) ^ m‖ ≤ max B 0 * (1 + ‖a‖) ^ m * ‖z‖⁻¹ ^ m`. Introduce `z hz0 y`. Establish `hY : 0 < ‖z‖ ^ m` using `pow_pos hz0 m`. Establish `hX : 0 < (1 + ‖z + a‖) ^ m` using `pow_pos (by linarith [norm_nonneg (z + a)]) m`. Establish `hYX : ‖z‖ ^ m ≤ (1 + ‖a‖) ^ m * (1 + ‖z + a‖) ^ m`.

Rewrite using `[← mul_pow]`. Conclude with `pow_le_pow_left₀ (norm_nonneg _) (norm_le_mul z a) m`. Establish `hinv : ((1 + ‖z + a‖) ^ m)⁻¹ ≤ (1 + ‖a‖) ^ m * (‖z‖ ^ m)⁻¹`. Rewrite using `[← div_eq_mul_inv, le_div_iff₀ hY, ← div_eq_inv_mul, div_le_iff₀ hX]`. Conclude with `hYX`.

Rewrite using `[Real.norm_of_nonneg (div_nonneg (norm_nonneg _) hX.le), inv_pow, div_eq_mul_inv, mul_assoc]`. Conclude with `mul_le_mul (le_max_of_le_left (hB _)) hinv (inv_nonneg.2 hX.le) (le_max_right _ _)`. Establish `h` using `key _ (hzn ▸ norm_pos_iff.2 hz) (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ.1 i))`. Rewrite `h` using `[← hzn]`. Conclude with `h`.
-/
theorem exists_summable_decay {κ : Type} [Fintype κ] {R : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ}
    (hR : R ∈ SB (κ → FiniteAdeleRing (𝓞 F) F)) : ∃ m : ℕ, ∀ a : κ → mixedEmbedding.mixedSpace F,
      Summable fun ξ : κ → F =>
        ‖R (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i))‖ / (1 + ‖(fun i => mixedEmbedding F (ξ i)) + a‖) ^ m := by
  obtain ⟨B, hB⟩ := hR.1.continuous.bounded_above_of_compact_support hR.2
  obtain ⟨N, hN, hK⟩ := exists_nat_mul_integral_of_isCompact F hR.2.isCompact
  haveI := discreteTopology_denomLattice F κ hN
  set L := denomLattice F κ N
  refine ⟨Module.finrank ℤ L + 1, fun a => ?_⟩
  set m := Module.finrank ℤ L + 1
  have hw := ZLattice.summable_norm_pow_inv L m (Nat.lt_succ_self _)
  let S : Set (κ → F) := {ξ | (fun i => mixedEmbedding F (ξ i)) ∈ L}
  have hsupp : ∀ ξ : κ → F, ξ ∉ Set.range (Subtype.val : S → κ → F) →
      ‖R (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i))‖ / (1 + ‖(fun i => mixedEmbedding F (ξ i)) + a‖) ^ m = 0 := by
    intro ξ hξ
    by_contra h0
    apply hξ
    have h0' : R (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i)) ≠ 0 := by
      intro h; apply h0; rw [h, norm_zero, zero_div]
    refine ⟨⟨ξ, fun i => ?_⟩, rfl⟩
    obtain ⟨y, hy⟩ := (IntegralFinAdele.integral_finiteAdele_properties F).2.2.2.1 ((N : F) * ξ i) fun v => by
      rw [map_mul, map_natCast]
      exact hK _ (subset_tsupport _ h0') i v
    refine ⟨y, ?_⟩
    have h2 := congrArg (mixedEmbedding F) hy
    rw [← nsmul_eq_mul, map_nsmul, ← Nat.cast_smul_eq_nsmul ℝ] at h2
    exact h2.symm
  refine ((Subtype.val_injective (p := fun ξ => ξ ∈ S)).summable_iff hsupp).1 ?_
  let j : S → L := fun ξ => ⟨_, ξ.2⟩
  have hj : Function.Injective j := fun x y h => Subtype.ext (funext fun i =>
    mixedEmbedding_injective F (congrFun (congrArg Subtype.val h) i))
  have hs : Summable fun ξ : S => max B 0 * (1 + ‖a‖) ^ m * ‖j ξ‖⁻¹ ^ m :=
    (hw.comp_injective hj).mul_left _
  refine Summable.of_norm_bounded_eventually hs ?_
  have h0S : (fun i => mixedEmbedding F ((0 : κ → F) i)) ∈ L := by
    simp only [Pi.zero_apply, map_zero]; exact L.zero_mem
  filter_upwards [Filter.eventually_cofinite_ne (⟨0, h0S⟩ : S)] with ξ hne
  have hz : j ξ ≠ 0 := fun h => hne (hj (h.trans (Subtype.ext (funext fun i => (map_zero (mixedEmbedding F)).symm))))
  have hzn : ‖j ξ‖ = ‖((j ξ : L) : κ → mixedEmbedding.mixedSpace F)‖ := by simp
  have key : ∀ z : κ → mixedEmbedding.mixedSpace F, 0 < ‖z‖ → ∀ y : κ → FiniteAdeleRing (𝓞 F) F,
      ‖‖R y‖ / (1 + ‖z + a‖) ^ m‖ ≤ max B 0 * (1 + ‖a‖) ^ m * ‖z‖⁻¹ ^ m := by
    intro z hz0 y
    have hY : 0 < ‖z‖ ^ m := pow_pos hz0 m
    have hX : 0 < (1 + ‖z + a‖) ^ m := pow_pos (by linarith [norm_nonneg (z + a)]) m
    have hYX : ‖z‖ ^ m ≤ (1 + ‖a‖) ^ m * (1 + ‖z + a‖) ^ m := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (norm_nonneg _) (norm_le_mul z a) m
    have hinv : ((1 + ‖z + a‖) ^ m)⁻¹ ≤ (1 + ‖a‖) ^ m * (‖z‖ ^ m)⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ hY, ← div_eq_inv_mul, div_le_iff₀ hX]; exact hYX
    rw [Real.norm_of_nonneg (div_nonneg (norm_nonneg _) hX.le), inv_pow, div_eq_mul_inv, mul_assoc]
    exact mul_le_mul (le_max_of_le_left (hB _)) hinv (inv_nonneg.2 hX.le) (le_max_right _ _)
  have h := key _ (hzn ▸ norm_pos_iff.2 hz) (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ.1 i))
  rw [← hzn] at h
  exact h

/- English proof (translation)
Use `set q := p + t • X`. Establish `htX : ‖t • X‖ ≤ ‖X‖`. Rewrite using `[norm_smul, Real.norm_eq_abs]`. Conclude with `mul_le_of_le_one_left (norm_nonneg _) ht`. Establish `hpq : ‖p‖ ≤ ‖q‖ + ‖X‖`.

Combine the equalities or inequalities in the displayed calculation. Establish `hq : 1 + ‖p‖ ≤ (1 + ‖X‖) * (1 + ‖q‖)`. Use polynomial arithmetic with `[norm_nonneg X, norm_nonneg q, mul_nonneg (norm_nonneg X) (norm_nonneg q)]`. Establish `hP : 0 < (1 + ‖p‖) ^ m` using `pow_pos (by linarith [norm_nonneg p]) m`. Establish `H : ‖h q‖ * (1 + ‖p‖) ^ m ≤ C * (1 + ‖X‖) ^ m`.

Combine the equalities or inequalities in the displayed calculation. Use `mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)` and prove the remaining obligations. Rewrite using `[← mul_pow]; exact pow_le_pow_left₀ (by linarith [norm_nonneg p]) hq m`. Use `_ = (1 + ‖X‖) ^ m * ((1 + ‖q‖) ^ m * ‖h q‖) := by ring`. Use `_ ≤ (1 + ‖X‖) ^ m * C := mul_le_mul_of_nonneg_left (hC q) (pow_nonneg (by linarith [norm_nonneg X]) m)`.

Use `_ = C * (1 + ‖X‖) ^ m := by ring`. Rewrite using `[← mul_div_assoc, le_div_iff₀ hP]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem bound_aux {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (h : V → ℂ) (C : ℝ) (m : ℕ)
    (hC : ∀ p, (1 + ‖p‖) ^ m * ‖h p‖ ≤ C) (p X : V) (t : ℝ) (ht : |t| ≤ 1) (b : ℝ) (hb : 0 ≤ b) :
    ‖h (p + t • X)‖ * b ≤ C * (1 + ‖X‖) ^ m * (b / (1 + ‖p‖) ^ m) := by
  set q := p + t • X
  have htX : ‖t • X‖ ≤ ‖X‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (norm_nonneg _) ht
  have hpq : ‖p‖ ≤ ‖q‖ + ‖X‖ := by
    calc ‖p‖ = ‖q - t • X‖ := by simp [q]
      _ ≤ ‖q‖ + ‖t • X‖ := norm_sub_le _ _
      _ ≤ ‖q‖ + ‖X‖ := by linarith
  have hq : 1 + ‖p‖ ≤ (1 + ‖X‖) * (1 + ‖q‖) := by
    nlinarith [norm_nonneg X, norm_nonneg q, mul_nonneg (norm_nonneg X) (norm_nonneg q)]
  have hP : 0 < (1 + ‖p‖) ^ m := pow_pos (by linarith [norm_nonneg p]) m
  have H : ‖h q‖ * (1 + ‖p‖) ^ m ≤ C * (1 + ‖X‖) ^ m := by
    calc ‖h q‖ * (1 + ‖p‖) ^ m ≤ ‖h q‖ * ((1 + ‖X‖) ^ m * (1 + ‖q‖) ^ m) := by
          refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
          rw [← mul_pow]; exact pow_le_pow_left₀ (by linarith [norm_nonneg p]) hq m
      _ = (1 + ‖X‖) ^ m * ((1 + ‖q‖) ^ m * ‖h q‖) := by ring
      _ ≤ (1 + ‖X‖) ^ m * C :=
          mul_le_mul_of_nonneg_left (hC q) (pow_nonneg (by linarith [norm_nonneg X]) m)
      _ = C * (1 + ‖X‖) ^ m := by ring
  rw [← mul_div_assoc, le_div_iff₀ hP]
  calc ‖h q‖ * b * (1 + ‖p‖) ^ m = (‖h q‖ * (1 + ‖p‖) ^ m) * b := by ring
    _ ≤ (C * (1 + ‖X‖) ^ m) * b := mul_le_mul_of_nonneg_right H hb

end Helpers

/- English proof (translation)
Unfold `realAd`. Rewrite using `[map_add, map_add, map_add]`. Both sides reduce to the same expression.
-/
theorem realAd_add (t s : ℝ) : realAd F (t + s) = realAd F t + realAd F s := by
  unfold realAd; rw [map_add, map_add, map_add]; rfl

/- English proof (translation)
Unfold `realAd`. Rewrite using `[map_zero, map_zero, map_zero]`. Both sides reduce to the same expression.
-/
theorem realAd_zero : realAd F 0 = 0 := by
  unfold realAd; rw [map_zero, map_zero, map_zero]; rfl

/- English proof (translation)
Simplify using `[evI, realAd]`.
-/
theorem evI_realAd (t : ℝ) : evI F (realAd F t) = algebraMap ℝ _ t := by
  simp [evI, realAd]

/- English proof (translation)
Introduce `b hb`. Establish `hb1 : b.1 = 0` using `(map_eq_zero_iff _ (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective).1 hb`. Establish `: b * realAd F t = 0`. Express the relevant statement in the definitionally equal form `((b.1 * _, b.2 * (0 : FiniteAdeleRing (𝓞 F) F)) : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F) = ((0 : InfiniteAdeleRing F), (0 : FiniteAdeleRing (𝓞 F) F))`. Rewrite using `[hb1, zero_mul, mul_zero]`.

Rewrite using `[smul_smul, this, zero_smul]`.
-/
theorem at_realAd_smul {V : Type} [AddCommGroup V] [Module (AF F) V] (t : ℝ) (x : V) :
    At (evI F) (realAd F t • x) := by
  intro b hb
  have hb1 : b.1 = 0 := (map_eq_zero_iff _ (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective).1 hb
  have : b * realAd F t = 0 := by
    change ((b.1 * _, b.2 * (0 : FiniteAdeleRing (𝓞 F) F)) : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F) =
      ((0 : InfiniteAdeleRing F), (0 : FiniteAdeleRing (𝓞 F) F))
    rw [hb1, zero_mul, mul_zero]
  rw [smul_smul, this, zero_smul]

/- English proof (translation)
Establish `hb : evI F (pairA F 0 1) = 0` using `by show InfiniteAdeleRing.ringEquiv_mixedSpace F (0 : InfiniteAdeleRing F) = 0`. Conclude with `map_zero _`. Establish `h` using `congrArg (evFin F v) (congrFun (hz _ hb) i)`. Express the relevant statement in the definitionally equal form `evFin F v (pairA F 0 1 * z i) = evFin F v 0 at h`. Rewrite `h` using `[map_mul, map_zero]`.

Establish `h1 : evFin F v (pairA F 0 1) = 1` using `by show Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v 1 = 1`. Conclude with `map_one _`. Rewrite `h` using `[h1, one_mul]`. Then use the resulting hypothesis.
-/
theorem evFin_eq_zero {κ : Type} {z : κ → AF F} (hz : At (evI F) z) (v : HeightOneSpectrum (𝓞 F)) (i : κ) :
    evFin F v (z i) = 0 := by
  have hb : evI F (pairA F 0 1) = 0 := by
    show InfiniteAdeleRing.ringEquiv_mixedSpace F (0 : InfiniteAdeleRing F) = 0
    exact map_zero _
  have h := congrArg (evFin F v) (congrFun (hz _ hb) i)
  change evFin F v (pairA F 0 1 * z i) = evFin F v 0 at h
  rw [map_mul, map_zero] at h
  have h1 : evFin F v (pairA F 0 1) = 1 := by
    show Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v 1 = 1
    exact map_one _
  rwa [h1, one_mul] at h

section Line

variable {E : Type} [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
  {Y : Spc F E n} {Wd : Spc F E d} (M : Model σ Y Wd) (ψ : AddChar (AF F) ℂ)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem rho_apply (w : Matrix (Fin n) (Fin d) (AE F E)) (Ψ : (Fin n × Fin d → AF F) → ℂ) (z : Fin n × Fin d → AF F) :
    M.co.rho ψ w Ψ z =
      ψ (z ⬝ᵥ (M.co.e w).2 + ⅟(2 : AF F) * ((M.co.e w).1 ⬝ᵥ (M.co.e w).2)) * Ψ (z + (M.co.e w).1) := rfl

/- English proof (translation)
Use function extensionality and compare the values at `z`. Simplify using `only [Model.heisLine, rho_apply, realAd_add, add_smul, map_add, map_smul, Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add]`. Rewrite using `[← mul_assoc, ← AddChar.map_add_eq_mul, add_assoc z]`. Use `congr 2`. Simplify using `only [dotProduct_add, add_dotProduct, dotProduct_smul, smul_dotProduct, smul_eq_mul]`.

Take the linear combination `(realAd F t * realAd F s * ((M.co.e u).1 ⬝ᵥ (M.co.e u).2)) * invOf_mul_self (2 : AF F)`.
-/
theorem heisLine_add (u : Matrix (Fin n) (Fin d) (AE F E)) (t s : ℝ) (Ψ : (Fin n × Fin d → AF F) → ℂ) :
    M.heisLine ψ u (t + s) Ψ = M.heisLine ψ u t (M.heisLine ψ u s Ψ) := by
  funext z
  simp only [Model.heisLine, rho_apply, realAd_add, add_smul, map_add, map_smul, Prod.smul_fst, Prod.smul_snd,
    Prod.fst_add, Prod.snd_add]
  rw [← mul_assoc, ← AddChar.map_add_eq_mul, add_assoc z]
  congr 2
  simp only [dotProduct_add, add_dotProduct, dotProduct_smul, smul_dotProduct, smul_eq_mul]
  linear_combination (realAd F t * realAd F s * ((M.co.e u).1 ⬝ᵥ (M.co.e u).2)) * invOf_mul_self (2 : AF F)

/- English proof (translation)
Use function extensionality and compare the values at `z`. Simplify using `[Model.heisLine, rho_apply, realAd_zero]`.
-/
theorem heisLine_zero (u : Matrix (Fin n) (Fin d) (AE F E)) (Ψ : (Fin n × Fin d → AF F) → ℂ) :
    M.heisLine ψ u 0 Ψ = Ψ := by
  funext z
  simp [Model.heisLine, rho_apply, realAd_zero]

/- English proof (translation)
Use `set w := M.co.e (realAd F t • u)`. Use `set c := ψ (x ⬝ᵥ w.2 + ⅟(2 : AF F) * (w.1 ⬝ᵥ w.2))`. Establish `h1 : HasDerivAt (fun τ => M.heisLine ψ u (τ - t) Φ (x + w.1)) (Φ₁ (x + w.1)) t` using `HasDerivAt.comp_sub_const t t (by simpa using hD (x + w.1))`. Establish `hf : (fun τ => M.heisLine ψ u τ Φ x) = fun τ => c * M.heisLine ψ u (τ - t) Φ (x + w.1)`. Use function extensionality and compare the values at `τ`.

Use `conv_lhs => rw [show τ = t + (τ - t) by ring, heisLine_add]`. Both sides reduce to the same expression. Rewrite using `[hf]`. Conclude with `h1.const_mul c`.
-/
theorem hasDerivAt_heisLine (u : Matrix (Fin n) (Fin d) (AE F E)) {Φ Φ₁ : (Fin n × Fin d → AF F) → ℂ}
    (hD : ∀ x, HasDerivAt (fun t => M.heisLine ψ u t Φ x) (Φ₁ x) 0) (t : ℝ) (x : Fin n × Fin d → AF F) :
    HasDerivAt (fun τ => M.heisLine ψ u τ Φ x) (M.heisLine ψ u t Φ₁ x) t := by
  set w := M.co.e (realAd F t • u)
  set c := ψ (x ⬝ᵥ w.2 + ⅟(2 : AF F) * (w.1 ⬝ᵥ w.2))
  have h1 : HasDerivAt (fun τ => M.heisLine ψ u (τ - t) Φ (x + w.1)) (Φ₁ (x + w.1)) t :=
    HasDerivAt.comp_sub_const t t (by simpa using hD (x + w.1))
  have hf : (fun τ => M.heisLine ψ u τ Φ x) = fun τ => c * M.heisLine ψ u (τ - t) Φ (x + w.1) := by
    funext τ
    conv_lhs => rw [show τ = t + (τ - t) by ring, heisLine_add]
    rfl
  rw [hf]
  exact h1.const_mul c

end Line

/- English proof (translation)
Use `congr 1`. Use function extensionality and compare the values at `v`. Use `congr 1`. Use function extensionality and compare the values at `i`. Rewrite using `[Pi.add_apply, map_add, evFin_eq_zero hz, add_zero]`.
-/
theorem finprod_add {κ : Type} (φ : ∀ v : HeightOneSpectrum (𝓞 F), (κ → v.adicCompletion F) → ℂ) (x z : κ → AF F)
    (hz : At (evI F) z) :
    (∏ᶠ v, φ v fun i => evFin F v ((x + z) i)) = ∏ᶠ v, φ v fun i => evFin F v (x i) := by
  congr 1; funext v; congr 1; funext i; rw [Pi.add_apply, map_add, evFin_eq_zero hz, add_zero]

/- English proof (translation)
The claim follows from `map_add (InfiniteAdeleRing.ringEquiv_mixedSpace F) a.1 b.1`.
-/
theorem evI_add (a b : AF F) : evI F (a + b) = evI F a + evI F b := map_add (InfiniteAdeleRing.ringEquiv_mixedSpace F) a.1 b.1

/- English proof (translation)
The claim follows from `map_mul (InfiniteAdeleRing.ringEquiv_mixedSpace F) a.1 b.1`.
-/
theorem evI_mul (a b : AF F) : evI F (a * b) = evI F a * evI F b := map_mul (InfiniteAdeleRing.ringEquiv_mixedSpace F) a.1 b.1

/- English proof (translation)
Rewrite using `[InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp]`. Both sides reduce to the same expression.
-/
theorem evI_algebraMap (x : F) : evI F (algebraMap F (AF F) x) = mixedEmbedding F x := by
  rw [InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp]; rfl

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ n d Y Wd M ψ hψ hM u _hu g g₁ φ hSB hφ hAD u'`. Establish `hstd : ∀ᶠ v in Filter.cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1` using `(hφ.and hM.std).mono fun v h => h.1.trans h.2`. Set `r : (Fin n × Fin d → AF F) → ℂ` to `fun x => ∏ᶠ v, φ v fun i => evFin F v (x i)`. Establish `hr : ∀ x z, At (evI F) z → r (x + z) = r x` using `fun x z hz => finprod_add φ x z hz`. Establish `hrest : Rest (evI F) g r` using `⟨hr, GlobalTheory.TensUniq.pure_mem_schA g φ hSB hstd⟩`.

Establish `hD : ∀ x, HasDerivAt (fun t => M.heisLine ψ u t (pure g φ) x) (pure g₁ φ x) 0` using `hAD r hrest`. Use `set c := (M.co.e u').1`. Use `set X : Fin n × Fin d → mixedEmbedding.mixedSpace F := fun i => evI F ((M.co.e u).1 i)`. Establish `hnorm : ∀ (h : SInf F (Fin n × Fin d)) (t : ℝ) (z : Fin n × Fin d → AF F), ‖M.co.rho ψ u' (M.heisLine ψ u t (pure h φ)) z‖ = ‖h ((fun i => evI F (z i + c i)) + t • X)‖ * ‖r (z + c)‖`. Introduce `h t z`.

Rewrite using `[rho_apply, Model.heisLine, rho_apply, norm_mul, norm_mul, GlobalTheory.StdCharFromIsStd.norm_psi hψ, GlobalTheory.StdCharFromIsStd.norm_psi hψ, one_mul, one_mul, map_smul, Prod.smul_fst]`. Establish `hz : r (z + c + realAd F t • (M.co.e u).1) = r (z + c)` using `hr _ _ (at_realAd_smul t _)`. Use `show ‖h (fun i => evI F ((z + c + realAd F t • (M.co.e u).1) i)) * r (z + c + realAd F t • (M.co.e u).1)‖ = _`. Rewrite using `[hz, norm_mul]`. Use `congr 3`.

Use function extensionality and compare the values at `i`. Simplify using `only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]`. Rewrite using `[evI_add, evI_mul, evI_realAd, ← Algebra.smul_def]`. Set `R' : (Fin n × Fin d → FiniteAdeleRing (𝓞 F) F) → ℂ` to `fun y => ∏ᶠ v, φ v fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i + (c i).2)`. Establish `hR' : R' ∈ SB (Fin n × Fin d → FiniteAdeleRing (𝓞 F) F)` using `⟨(GlobalTheory.WeilM.isLocallyConstant_finprod_evalV φ hSB hstd).comp_continuous (Homeomorph.addRight (fun i => (c i).2)).continuous, (GlobalTheory.AdelicCoordSupport.hasCompactSupport_finprod φ hSB hstd).comp_homeomorph (Homeomorph.addRight (fun i => (c i).2))⟩`.

Take `⟨m, hm⟩` from `exists_summable_decay hR'`. Establish `hsum` using `hm (fun i => evI F (c i))`. Establish `key : ∀ (h : SInf F (Fin n × Fin d)) (C : ℝ), (∀ p, (1 + ‖p‖) ^ m * ‖h p‖ ≤ C) → ∀ t : ℝ, |t| ≤ 1 → ∀ ξ : Fin n × Fin d → F, ‖M.co.rho ψ u' (M.heisLine ψ u t (pure h φ)) (fun i => algebraMap F (AF F) (ξ i))‖ ≤ C * (1 + ‖X‖) ^ m * (‖R' (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) …`. Introduce `h C hC t ht ξ`. Rewrite using `[hnorm]`.

Establish `hp : (fun i => evI F (algebraMap F (AF F) (ξ i) + c i)) = (fun i => mixedEmbedding F (ξ i)) + fun i => evI F (c i)`. Use function extensionality and compare the values at `fun i => by rw [evI_add, evI_algebraMap]; rfl`. Rewrite using `[hp]`. Conclude with `bound_aux h C m hC _ X t ht _ (norm_nonneg _)`. Take `⟨C₁, hC₁⟩` from `GlobalTheory.SchwartzDecay.schwartz_bound g₁ m`.

Take `⟨C₀, hC₀⟩` from `GlobalTheory.SchwartzDecay.schwartz_bound g m`. Establish `hderiv : ∀ (ξ : Fin n × Fin d → F), ∀ y ∈ Set.Ioo (-1 : ℝ) 1, HasDerivAt (fun t => M.co.rho ψ u' (M.heisLine ψ u t (pure g φ)) (fun i => algebraMap F (AF F) (ξ i))) (M.co.rho ψ u' (M.heisLine ψ u y (pure g₁ φ)) (fun i => algebraMap F (AF F) (ξ i))) y`. Introduce `ξ y _`. Simplify using `only [rho_apply]`. Conclude with `(hasDerivAt_heisLine M ψ u hD y _).const_mul _`.

Establish `hbd : ∀ (ξ : Fin n × Fin d → F), ∀ y ∈ Set.Ioo (-1 : ℝ) 1, ‖M.co.rho ψ u' (M.heisLine ψ u y (pure g₁ φ)) (fun i => algebraMap F (AF F) (ξ i))‖ ≤ C₁ * (1 + ‖X‖) ^ m * (‖R' (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i))‖ / (1 + ‖(fun i => mixedEmbedding F (ξ i)) + fun i => …` using `fun ξ y hy => key g₁ C₁ hC₁ y (abs_le.2 ⟨hy.1.le, hy.2.le⟩) ξ`. Establish `hs0 : Summable fun ξ : Fin n × Fin d → F => M.co.rho ψ u' (M.heisLine ψ u 0 (pure g φ)) (fun i => algebraMap F (AF F) (ξ i))` using `Summable.of_norm_bounded (hsum.mul_left (C₀ * (1 + ‖X‖) ^ m)) fun ξ => key g C₀ hC₀ 0 (by simp) ξ`. Establish `h0 : (0 : ℝ) ∈ Set.Ioo (-1 : ℝ) 1` using `by norm_num`. Use `hasDerivAt_tsum_of_isPreconnected (hsum.mul_left (C₁ * (1 + ‖X‖) ^ m)) isOpen_Ioo isPreconnected_Ioo hderiv hbd h0 hs0 h0` as an intermediate fact. Rewrite `this` using `[heisLine_zero]`.

Conclude with `this`.
-/
theorem hasDerivAt_thetaSum_heisLine : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Wd) (ψ : AddChar (AF F) ℂ),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → M.IsGood ψ → ∀ (u : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E)), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) u →
    ∀ (g g₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)) (φ : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), (Fin n × Fin d → v.adicCompletion F) → ℂ),
      (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) → (∀ᶠ v in Filter.cofinite, φ v = M.vac v) →
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (M.heisLine ψ u) g g₁ →
      ∀ u' : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E),
        HasDerivAt (fun t : ℝ => GlobalTheory.WeilM.thetaSum F (M.co.rho ψ u' (M.heisLine ψ u t (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ))))
          (GlobalTheory.WeilM.thetaSum F (M.co.rho ψ u' (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g₁ φ))) 0 := by
  intro F E _ _ _ _ _ σ n d Y Wd M ψ hψ hM u _hu g g₁ φ hSB hφ hAD u'
  classical
  have hstd : ∀ᶠ v in Filter.cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 :=
    (hφ.and hM.std).mono fun v h => h.1.trans h.2
  let r : (Fin n × Fin d → AF F) → ℂ := fun x => ∏ᶠ v, φ v fun i => evFin F v (x i)
  have hr : ∀ x z, At (evI F) z → r (x + z) = r x := fun x z hz => finprod_add φ x z hz
  have hrest : Rest (evI F) g r := ⟨hr, GlobalTheory.TensUniq.pure_mem_schA g φ hSB hstd⟩
  have hD : ∀ x, HasDerivAt (fun t => M.heisLine ψ u t (pure g φ) x) (pure g₁ φ x) 0 := hAD r hrest
  set c := (M.co.e u').1
  set X : Fin n × Fin d → mixedEmbedding.mixedSpace F := fun i => evI F ((M.co.e u).1 i)
  have hnorm : ∀ (h : SInf F (Fin n × Fin d)) (t : ℝ) (z : Fin n × Fin d → AF F),
      ‖M.co.rho ψ u' (M.heisLine ψ u t (pure h φ)) z‖ = ‖h ((fun i => evI F (z i + c i)) + t • X)‖ * ‖r (z + c)‖ := by
    intro h t z
    rw [rho_apply, Model.heisLine, rho_apply, norm_mul, norm_mul, GlobalTheory.StdCharFromIsStd.norm_psi hψ,
      GlobalTheory.StdCharFromIsStd.norm_psi hψ, one_mul, one_mul, map_smul, Prod.smul_fst]
    have hz : r (z + c + realAd F t • (M.co.e u).1) = r (z + c) := hr _ _ (at_realAd_smul t _)
    show ‖h (fun i => evI F ((z + c + realAd F t • (M.co.e u).1) i)) * r (z + c + realAd F t • (M.co.e u).1)‖ = _
    rw [hz, norm_mul]
    congr 3
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [evI_add, evI_mul, evI_realAd, ← Algebra.smul_def]

  let R' : (Fin n × Fin d → FiniteAdeleRing (𝓞 F) F) → ℂ := fun y =>
    ∏ᶠ v, φ v fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i + (c i).2)
  have hR' : R' ∈ SB (Fin n × Fin d → FiniteAdeleRing (𝓞 F) F) :=
    ⟨(GlobalTheory.WeilM.isLocallyConstant_finprod_evalV φ hSB hstd).comp_continuous
        (Homeomorph.addRight (fun i => (c i).2)).continuous,
      (GlobalTheory.AdelicCoordSupport.hasCompactSupport_finprod φ hSB hstd).comp_homeomorph
        (Homeomorph.addRight (fun i => (c i).2))⟩
  obtain ⟨m, hm⟩ := exists_summable_decay hR'
  have hsum := hm (fun i => evI F (c i))
  have key : ∀ (h : SInf F (Fin n × Fin d)) (C : ℝ), (∀ p, (1 + ‖p‖) ^ m * ‖h p‖ ≤ C) → ∀ t : ℝ, |t| ≤ 1 →
      ∀ ξ : Fin n × Fin d → F,
        ‖M.co.rho ψ u' (M.heisLine ψ u t (pure h φ)) (fun i => algebraMap F (AF F) (ξ i))‖ ≤
          C * (1 + ‖X‖) ^ m * (‖R' (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i))‖ /
            (1 + ‖(fun i => mixedEmbedding F (ξ i)) + fun i => evI F (c i)‖) ^ m) := by
    intro h C hC t ht ξ
    rw [hnorm]
    have hp : (fun i => evI F (algebraMap F (AF F) (ξ i) + c i)) =
        (fun i => mixedEmbedding F (ξ i)) + fun i => evI F (c i) :=
      funext fun i => by rw [evI_add, evI_algebraMap]; rfl
    rw [hp]
    exact bound_aux h C m hC _ X t ht _ (norm_nonneg _)
  obtain ⟨C₁, hC₁⟩ := GlobalTheory.SchwartzDecay.schwartz_bound g₁ m
  obtain ⟨C₀, hC₀⟩ := GlobalTheory.SchwartzDecay.schwartz_bound g m
  have hderiv : ∀ (ξ : Fin n × Fin d → F), ∀ y ∈ Set.Ioo (-1 : ℝ) 1,
      HasDerivAt (fun t => M.co.rho ψ u' (M.heisLine ψ u t (pure g φ)) (fun i => algebraMap F (AF F) (ξ i)))
        (M.co.rho ψ u' (M.heisLine ψ u y (pure g₁ φ)) (fun i => algebraMap F (AF F) (ξ i))) y := by
    intro ξ y _
    simp only [rho_apply]
    exact (hasDerivAt_heisLine M ψ u hD y _).const_mul _
  have hbd : ∀ (ξ : Fin n × Fin d → F), ∀ y ∈ Set.Ioo (-1 : ℝ) 1,
      ‖M.co.rho ψ u' (M.heisLine ψ u y (pure g₁ φ)) (fun i => algebraMap F (AF F) (ξ i))‖ ≤
        C₁ * (1 + ‖X‖) ^ m * (‖R' (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i))‖ /
            (1 + ‖(fun i => mixedEmbedding F (ξ i)) + fun i => evI F (c i)‖) ^ m) :=
    fun ξ y hy => key g₁ C₁ hC₁ y (abs_le.2 ⟨hy.1.le, hy.2.le⟩) ξ
  have hs0 : Summable fun ξ : Fin n × Fin d → F =>
      M.co.rho ψ u' (M.heisLine ψ u 0 (pure g φ)) (fun i => algebraMap F (AF F) (ξ i)) :=
    Summable.of_norm_bounded (hsum.mul_left (C₀ * (1 + ‖X‖) ^ m)) fun ξ => key g C₀ hC₀ 0 (by simp) ξ
  have h0 : (0 : ℝ) ∈ Set.Ioo (-1 : ℝ) 1 := by norm_num
  have := hasDerivAt_tsum_of_isPreconnected (hsum.mul_left (C₁ * (1 + ‖X‖) ^ m)) isOpen_Ioo isPreconnected_Ioo
    hderiv hbd h0 hs0 h0
  rw [heisLine_zero] at this
  exact this

end GlobalTheory.ThetaLinePure
