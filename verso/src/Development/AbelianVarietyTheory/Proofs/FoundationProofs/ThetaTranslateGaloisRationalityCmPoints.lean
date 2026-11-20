import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DifferentiableComb
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutesStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisConjTorsionTranslatesOddThetaProductStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GalStarComplexMultiplicationPointsStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaSpaceSelfDualPairAtMostLineStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIntegerMapEqHalfOneAddSqrt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TaylorCoeffConjugateSeries
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsComplexEndomorphismEqOnCountableStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ImaginaryQuadraticFieldStructureStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TaylorConjugateTangentSpacePadZeroColumnsStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SignedTranslationAddSelfDualLatticeStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsNonzeroThetaOfFiniteLevelAverageStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TranslateLevelFourStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsNsmulPaddedLatticeMemBasisProductStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AdaptedTorsionLiftDeeperLevelStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AdaptedPointChangeOfRationalBasisStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTranslationCombPeriodicTwiceLevelStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaOddPrimePhaseConjInvariantStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.GalTheta
open scoped BigOperators

namespace GlobalTheory.GalTheta

/- English proof (translation)
Take `⟨a, ha⟩` from `GlobalTheory.NormSum.exists_integer_map_eq_w0 D`. Establish `hlam : ∀ w ∈ lamOf D cc δ, w0 D * w ∈ lamOf D cc δ`. Introduce `w hw`. Unfold `lamOf at hw ⊢`. Proceed by induction on `hw using AddSubgroup.closure_induction with`.

Consider the case `mem z hz`. Take `⟨c, hc, rfl⟩` from `hz`. Use `AddSubgroup.subset_closure ⟨a * c, cc.mul_mem_left a hc, ?_⟩` and prove the remaining obligations. Rewrite using `[← ha]`. Simplify using `only [map_mul, MulMemClass.coe_mul, RingOfIntegers.coe_eq_algebraMap]`.

Expand and normalize the polynomial expressions, which then agree. Consider the case `zero => simp`. Consider the case `add y z _ _ hy hz => rw [mul_add]`. Conclude with `AddSubgroup.add_mem _ hy hz`. Consider the case `neg y _ hy => rw [mul_neg]`.

Conclude with `AddSubgroup.neg_mem _ hy`. Introduce `x hx`. Unfold `La at hx ⊢`. Proceed by induction on `hx using AddSubgroup.closure_induction with`. Consider the case `mem z hz`.

Take `⟨w, hw, A, hA, rfl⟩` from `hz`. Conclude with `AddSubgroup.subset_closure ⟨w0 D * w, hlam w hw, A, hA, by rw [smul_smul]⟩`. Consider the case `zero => simp`. Consider the case `add y z _ _ hy hz => rw [smul_add]`. Conclude with `AddSubgroup.add_mem _ hy hz`.

Consider the case `neg y _ hy => rw [smul_neg]`. Conclude with `AddSubgroup.neg_mem _ hy`.
-/
theorem weilElement_smul_mem_thetaLattice (D : D7) (hG : admG1 D) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {N N' : ℕ}
    (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) :
    ∀ x ∈ La D (tor0 D cc δ) L L', w0 D • x ∈ La D (tor0 D cc δ) L L' := by
  obtain ⟨a, ha⟩ := GlobalTheory.NormSum.exists_integer_map_eq_w0 D
  have hlam : ∀ w ∈ lamOf D cc δ, w0 D * w ∈ lamOf D cc δ := by
    intro w hw
    unfold lamOf at hw ⊢
    induction hw using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨c, hc, rfl⟩ := hz
      refine AddSubgroup.subset_closure ⟨a * c, cc.mul_mem_left a hc, ?_⟩
      rw [← ha]
      simp only [map_mul, MulMemClass.coe_mul, RingOfIntegers.coe_eq_algebraMap]
      ring
    | zero => simp
    | add y z _ _ hy hz => rw [mul_add]; exact AddSubgroup.add_mem _ hy hz
    | neg y _ hy => rw [mul_neg]; exact AddSubgroup.neg_mem _ hy
  intro x hx
  unfold La at hx ⊢
  induction hx using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨w, hw, A, hA, rfl⟩ := hz
    exact AddSubgroup.subset_closure ⟨w0 D * w, hlam w hw, A, hA, by rw [smul_smul]⟩
  | zero => simp
  | add y z _ _ hy hz => rw [smul_add]; exact AddSubgroup.add_mem _ hy hz
  | neg y _ hy => rw [smul_neg]; exact AddSubgroup.neg_mem _ hy

/- English proof (translation)
Establish `hG : admG1 D` using `(GlobalTheory.T.inducedType_thetaGenusOne_permutes D).1`. Take `⟨hline, -, hint, hdual, hfg, -, hq⟩` from `GlobalTheory.T.theta_space_selfDual_pair_at_most_line D hG cc δ hc N N' (La D (tor0 D cc δ) L L') (Or.inr ⟨L, L', hL, hL', rfl⟩)`. Take `⟨hS, t, ht2, ht0, ht4⟩` from `GlobalTheory.T.U_pullB_ne_zero_and_invariant_four_smul D hG cc δ hc (N + m) N' r b hb`. Take `⟨R, hR, hRA⟩` from `GlobalTheory.T.exists_nsmul_padded_lattice_mem_basis_product D hG cc δ hc N N' m r L L' b hb hfg`. Use `set S := pullB D (tor0 D cc δ) b (sgStar (lamOf D cc δ)) with hSdef`.

Establish `hF0 : (fun z : VC D N N' => U D (tor0 D cc δ) t S (pad D m z)) ≠ 0`. Introduce `h`. Use `congrFun h 0` as an intermediate fact. Rewrite `this` using `[pad_zero]`. Conclude with `ht0 this`.

Take `⟨P, hPt, hP, hP0⟩` from `GlobalTheory.T.exists_nonzero_theta_of_finite_level_average D (tor0 D cc δ) N N' _ hfg hint hdual hq (GlobalTheory.T.signedTranslation_add_selfDual_lattice D _ N N' _ hint hq (weilElement_smul_mem_thetaLattice D hG cc δ L L')) (fun z : VC D N N' => U D (tor0 D cc δ) t S (pad D m …`. Introduce `x hx`. Rewrite using `[U_pad, pad_nsmul, mul_smul, ht4 _ (hRA x hx)])`. Take `⟨a, ha⟩` from `hline e₀ he P hP hP0`. Establish `h1 : IsTr D (tor0 D cc δ) (La D (tor0 D cc δ) L L') P e₀`.

Use `IsTr.single D (tor0 D cc δ) (A := La D (tor0 D cc δ) L L') P a 0 1 one_pos (by simp)` as an intermediate fact. Rewrite `this` using `[U_zero]`. Rewrite using `[ha]`. Conclude with `this`. Take `⟨G₁, hG₁, hGG⟩` from `IsTr.pad D _ hR hRA ((hPt.trans D _ h1).trans D _ hGe)`.

Use `⟨G₁, IsTr.trans D _ ?_ hG₁, hGG⟩` and prove the remaining obligations. Use `IsTr.single D (tor0 D cc δ) (A := LaB D (tor0 D cc δ) b) S 1 t 2 two_pos ht2` as an intermediate fact. Simplify using `using this`.
-/
theorem exists_restriction (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (hc : Crv D cc δ) {N N' m r : ℕ}
    (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
    (hL : SD D L) (hL' : SD D L') (b : Fin r → Matrix (Fin N') (Fin (N + m)) D.host.E) (hb : OnB D b)
    (e₀ G : VC D N N' → ℂ) (he : e₀ ∈ Th D (tor0 D cc δ) L L')
    (hGe : IsTr D (tor0 D cc δ) (La D (tor0 D cc δ) L L') e₀ G) :
    ∃ G₁, IsTr D (tor0 D cc δ) (LaB D (tor0 D cc δ) b) (pullB D (tor0 D cc δ) b (sgStar (lamOf D cc δ))) G₁ ∧
      G = fun z => G₁ (pad D m z) := by
  have hG : admG1 D := (GlobalTheory.T.inducedType_thetaGenusOne_permutes D).1
  obtain ⟨hline, -, hint, hdual, hfg, -, hq⟩ :=
    GlobalTheory.T.theta_space_selfDual_pair_at_most_line D hG cc δ hc N N' (La D (tor0 D cc δ) L L') (Or.inr ⟨L, L', hL, hL', rfl⟩)
  obtain ⟨hS, t, ht2, ht0, ht4⟩ := GlobalTheory.T.U_pullB_ne_zero_and_invariant_four_smul D hG cc δ hc (N + m) N' r b hb
  obtain ⟨R, hR, hRA⟩ := GlobalTheory.T.exists_nsmul_padded_lattice_mem_basis_product D hG cc δ hc N N' m r L L' b hb hfg
  set S := pullB D (tor0 D cc δ) b (sgStar (lamOf D cc δ)) with hSdef
  have hF0 : (fun z : VC D N N' => U D (tor0 D cc δ) t S (pad D m z)) ≠ 0 := by
    intro h
    have := congrFun h 0
    rw [pad_zero] at this
    exact ht0 this
  obtain ⟨P, hPt, hP, hP0⟩ := GlobalTheory.T.exists_nonzero_theta_of_finite_level_average D (tor0 D cc δ) N N' _ hfg hint hdual hq
    (GlobalTheory.T.signedTranslation_add_selfDual_lattice D _ N N' _ hint hq (weilElement_smul_mem_thetaLattice D hG cc δ L L'))
    (fun z : VC D N N' => U D (tor0 D cc δ) t S (pad D m z))
    ((differentiable_U D _ t hS).comp (differentiable_pad D m)) hF0 (4 * R) (by omega) (by
      intro x hx
      rw [U_pad, pad_nsmul, mul_smul, ht4 _ (hRA x hx)])
  obtain ⟨a, ha⟩ := hline e₀ he P hP hP0
  have h1 : IsTr D (tor0 D cc δ) (La D (tor0 D cc δ) L L') P e₀ := by
    have := IsTr.single D (tor0 D cc δ) (A := La D (tor0 D cc δ) L L') P a 0 1 one_pos (by simp)
    rw [U_zero] at this
    rw [ha]; exact this
  obtain ⟨G₁, hG₁, hGG⟩ := IsTr.pad D _ hR hRA ((hPt.trans D _ h1).trans D _ hGe)
  refine ⟨G₁, IsTr.trans D _ ?_ hG₁, hGG⟩
  have := IsTr.single D (tor0 D cc δ) (A := LaB D (tor0 D cc δ) b) S 1 t 2 two_pos ht2
  simpa using this

/- English proof (translation)
Establish `hG : admG1 D` using `(GlobalTheory.T.inducedType_thetaGenusOne_permutes D).1`. Establish `hSt : galStar D` using `GlobalTheory.T.galStar_complexMultiplication_points D`. Establish `hD : DataIn D (tor0 D cc δ) ⊤` using `⟨fun _ _ => trivial, trivial, trivial⟩`. Take `⟨-, -, hint, -, hfg, -, hq⟩` from `GlobalTheory.T.theta_space_selfDual_pair_at_most_line D hG cc δ hc N N' (La D (tor0 D cc δ) L L') (Or.inr ⟨L, L', hL, hL', rfl⟩)`. Take `⟨m, r, B, hB⟩` from `GlobalTheory.T.exists_orthonormal_frame_var D N N'`.

Take `⟨G₁, ⟨k₁, c₁, t₁, m₁, hm₁, ht₁, rfl⟩, hGG⟩` from `exists_restriction D cc δ hc L L' hL hL' B hB e₀ _ he ⟨k, c, t, m₀, hm, ht, rfl⟩`. Take `⟨R, hR, hRA⟩` from `GlobalTheory.T.exists_nsmul_padded_lattice_mem_basis_product D hG cc δ hc N N' m r L L' B hB hfg`. Take `⟨s, b, a, a', hb, ha, hxa, hxa', haa⟩` from `hA`. Take `⟨R', hR', hchg⟩` from `GlobalTheory.T.adapted_point_change_of_rational_basis D hG hSt cc δ hc ⊤ σ hK hD (N + m) N' r s B (fun j => padM D m (b j)) hB`. Establish `hl` using `fun j => GlobalTheory.T.adapted_torsion_lift_deeper_level D hSt cc δ hc σ hK (a j) (a' j) (2 * m₀) (R * m₁ * R') (by omega) (by positivity) (ha j) (haa j)`.

Use `choose ω hω hωa using hl`. Use `set l : VC D N N' := ∑ j, ω j • embV D (tor0 D cc δ) (b j) with hldef`. Establish `hlA : l ∈ La D (tor0 D cc δ) L L'` using `AddSubgroup.sum_mem _ fun j _ => AddSubgroup.subset_closure ⟨ω j, hω j, b j, hb j, rfl⟩`. Take `⟨hp1, hp2⟩` from `GlobalTheory.T.thetaTranslation_comb_periodic_twice_level D (tor0 D cc δ) N N' _ hint hq k c t e₀ x m₀ he hx ht l hlA`. Establish `hy : m₀ • (x + (2 * m₀) • l) ∈ La D (tor0 D cc δ) L L'`.

Rewrite using `[smul_add]`. Conclude with `AddSubgroup.add_mem _ hx (AddSubgroup.nsmul_mem _ (AddSubgroup.nsmul_mem _ hlA _) _)`. Establish `e1 : pad D m (x + (2 * m₀) • l) = ∑ j, (a j + ((2 * m₀ : ℕ) : ℂ) * ω j) • embV D (tor0 D cc δ) (padM D m (b j))`. Establish `: x + (2 * m₀) • l = ∑ j, (a j + ((2 * m₀ : ℕ) : ℂ) * ω j) • embV D (tor0 D cc δ) (b j)`. Rewrite using `[hxa, hldef, ← Nat.cast_smul_eq_nsmul ℂ, Finset.smul_sum, ← Finset.sum_add_distrib]`.

Simplify using `only [add_smul, smul_smul]`. Rewrite using `[this, pad_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[pad_smul, pad_embV D _ (fun τ => map_zero (embT D τ))]`. Establish `e2 : pad D m x' = ∑ j, a' j • embV D (torConj D (tor0 D cc δ) ⊤ σ) (padM D m (b j))`.

Rewrite using `[hxa', pad_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[pad_smul, pad_embV]`. Introduce `τ`. Use `show σ (TaylorLogMetric.liftM ⊤ (embT D τ 0)) = 0`.

Rewrite using `[map_zero]`. Establish `: TaylorLogMetric.liftM ⊤ (0 : ℂ) = 0` using `by simp [TaylorLogMetric.liftM]; rfl`. Rewrite using `[this, map_zero]`. Establish `hAd : AdpB D (tor0 D cc δ) ⊤ σ B (2 * (m₀ * R * m₁)) (pad D m (x + (2 * m₀) • l)) (pad D m x')`. Rewrite using `[e1, e2]`.

Use `hchg _ _ _ (by positivity) (fun j => ?_) (fun j => ?_)` and prove the remaining obligations. Take `⟨n, hn, hna⟩` from `ha j`. Use `⟨n, hn, ?_⟩` and prove the remaining obligations. Rewrite using `[mul_add, ← mul_assoc, ← Nat.cast_mul, ← nsmul_eq_mul (n * (2 * m₀))]`. Conclude with `AddSubgroup.add_mem _ hna (AddSubgroup.nsmul_mem _ (hω j) _)`.

Establish `: 2 * (m₀ * R * m₁) * R' = 2 * m₀ * (R * m₁ * R')` using `by ring`. Rewrite using `[this]`. Conclude with `hωa j`. Take `⟨hg1, hg2⟩` from `GlobalTheory.T.galois_conj_torsionTranslates_oddThetaProduct D cc δ hc ⊤ σ hK hD (N + m) N' r B hB k₁ c₁ t₁ (pad D m (x + (2 * m₀) • l)) (pad D m x') (m₀ * R * m₁) (by positivity) (by`. Establish `: (m₀ * R * m₁) • pad D m (x + (2 * m₀) • l) = m₁ • R • pad D m (m₀ • (x + (2 * m₀) • l))`.

Rewrite using `[pad_nsmul, smul_smul, smul_smul]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Conclude with `AddSubgroup.nsmul_mem _ (hRA _ hy) _)`.

Use the proof step `(fun i => by rw [mul_smul]; exact AddSubgroup.nsmul_mem _ (ht₁ i) _) hAd (fun _ => trivial) (fun _ => trivial)`. Establish `hd` using `differentiable_comb D (tor0 D cc δ) c₁ t₁ (GlobalTheory.T.U_pullB_ne_zero_and_invariant_four_smul D hG cc δ hc (N + m) N' r B hB).1`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← hp1, hGG, U_pad, GlobalTheory.T.taylorConjugate_tangentSpacePadZeroColumns D N N' m ⊤ σ _ (differentiable_U D _ _ hd), hg1, GlobalTheory.T.taylorConjugate_tangentSpacePadZeroColumns D N N' m ⊤ σ _ hd, U_pad]`. Use `(hg2 trivial).1` as an intermediate fact.

Rewrite `this` using `[wdPh_pad, wdPh_pad, hp2]`. Then use the resulting hypothesis.
-/
theorem gal_top (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (hc : Crv D cc δ)
    (σ : (⊤ : IntermediateField ℚ ℂ) →ₐ[ℚ] ℂ) (hK : FixK D ⊤ σ) {N N' : ℕ}
    (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
    (hL : SD D L) (hL' : SD D L') {k : ℕ} (c : Fin k → ℂ) (t : Fin k → VC D N N') (e₀ : VC D N N' → ℂ)
    (x x' : VC D N N') (m₀ : ℕ) (he : e₀ ∈ Th D (tor0 D cc δ) L L') (hm : 0 < m₀)
    (hx : m₀ • x ∈ La D (tor0 D cc δ) L L') (ht : ∀ i, m₀ • t i ∈ La D (tor0 D cc δ) L L')
    (hA : AdpV D (tor0 D cc δ) ⊤ σ L L' (2 * m₀) x x') :
    fnConj D ⊤ σ (U D (tor0 D cc δ) x (comb D (tor0 D cc δ) c t e₀)) =
        U D (torConj D (tor0 D cc δ) ⊤ σ) x' (fnConj D ⊤ σ (comb D (tor0 D cc δ) c t e₀)) ∧
      cj ⊤ σ (wdPh D (tor0 D cc δ) x) = wdPh D (torConj D (tor0 D cc δ) ⊤ σ) x' := by
  have hG : admG1 D := (GlobalTheory.T.inducedType_thetaGenusOne_permutes D).1
  have hSt : galStar D := GlobalTheory.T.galStar_complexMultiplication_points D
  have hD : DataIn D (tor0 D cc δ) ⊤ := ⟨fun _ _ => trivial, trivial, trivial⟩
  obtain ⟨-, -, hint, -, hfg, -, hq⟩ :=
    GlobalTheory.T.theta_space_selfDual_pair_at_most_line D hG cc δ hc N N' (La D (tor0 D cc δ) L L') (Or.inr ⟨L, L', hL, hL', rfl⟩)
  obtain ⟨m, r, B, hB⟩ := GlobalTheory.T.exists_orthonormal_frame_var D N N'
  obtain ⟨G₁, ⟨k₁, c₁, t₁, m₁, hm₁, ht₁, rfl⟩, hGG⟩ :=
    exists_restriction D cc δ hc L L' hL hL' B hB e₀ _ he ⟨k, c, t, m₀, hm, ht, rfl⟩
  obtain ⟨R, hR, hRA⟩ := GlobalTheory.T.exists_nsmul_padded_lattice_mem_basis_product D hG cc δ hc N N' m r L L' B hB hfg
  obtain ⟨s, b, a, a', hb, ha, hxa, hxa', haa⟩ := hA
  obtain ⟨R', hR', hchg⟩ := GlobalTheory.T.adapted_point_change_of_rational_basis D hG hSt cc δ hc ⊤ σ hK hD (N + m) N' r s B (fun j => padM D m (b j)) hB
  have hl := fun j => GlobalTheory.T.adapted_torsion_lift_deeper_level D hSt cc δ hc σ hK (a j) (a' j) (2 * m₀) (R * m₁ * R') (by omega) (by positivity)
    (ha j) (haa j)
  choose ω hω hωa using hl
  set l : VC D N N' := ∑ j, ω j • embV D (tor0 D cc δ) (b j) with hldef
  have hlA : l ∈ La D (tor0 D cc δ) L L' :=
    AddSubgroup.sum_mem _ fun j _ => AddSubgroup.subset_closure ⟨ω j, hω j, b j, hb j, rfl⟩
  obtain ⟨hp1, hp2⟩ := GlobalTheory.T.thetaTranslation_comb_periodic_twice_level D (tor0 D cc δ) N N' _ hint hq k c t e₀ x m₀ he hx ht l hlA
  have hy : m₀ • (x + (2 * m₀) • l) ∈ La D (tor0 D cc δ) L L' := by
    rw [smul_add]
    exact AddSubgroup.add_mem _ hx (AddSubgroup.nsmul_mem _ (AddSubgroup.nsmul_mem _ hlA _) _)
  have e1 : pad D m (x + (2 * m₀) • l) =
      ∑ j, (a j + ((2 * m₀ : ℕ) : ℂ) * ω j) • embV D (tor0 D cc δ) (padM D m (b j)) := by
    have : x + (2 * m₀) • l = ∑ j, (a j + ((2 * m₀ : ℕ) : ℂ) * ω j) • embV D (tor0 D cc δ) (b j) := by
      rw [hxa, hldef, ← Nat.cast_smul_eq_nsmul ℂ, Finset.smul_sum, ← Finset.sum_add_distrib]
      simp only [add_smul, smul_smul]
    rw [this, pad_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [pad_smul, pad_embV D _ (fun τ => map_zero (embT D τ))]
  have e2 : pad D m x' = ∑ j, a' j • embV D (torConj D (tor0 D cc δ) ⊤ σ) (padM D m (b j)) := by
    rw [hxa', pad_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [pad_smul, pad_embV]
    intro τ
    show σ (TaylorLogMetric.liftM ⊤ (embT D τ 0)) = 0
    rw [map_zero]
    have : TaylorLogMetric.liftM ⊤ (0 : ℂ) = 0 := by simp [TaylorLogMetric.liftM]; rfl
    rw [this, map_zero]
  have hAd : AdpB D (tor0 D cc δ) ⊤ σ B (2 * (m₀ * R * m₁)) (pad D m (x + (2 * m₀) • l)) (pad D m x') := by
    rw [e1, e2]
    refine hchg _ _ _ (by positivity) (fun j => ?_) (fun j => ?_)
    · obtain ⟨n, hn, hna⟩ := ha j
      refine ⟨n, hn, ?_⟩
      rw [mul_add, ← mul_assoc, ← Nat.cast_mul, ← nsmul_eq_mul (n * (2 * m₀))]
      exact AddSubgroup.add_mem _ hna (AddSubgroup.nsmul_mem _ (hω j) _)
    · have : 2 * (m₀ * R * m₁) * R' = 2 * m₀ * (R * m₁ * R') := by ring
      rw [this]; exact hωa j
  obtain ⟨hg1, hg2⟩ := GlobalTheory.T.galois_conj_torsionTranslates_oddThetaProduct D cc δ hc ⊤ σ hK hD (N + m) N' r B hB k₁ c₁ t₁
    (pad D m (x + (2 * m₀) • l)) (pad D m x') (m₀ * R * m₁) (by positivity) (by
      have : (m₀ * R * m₁) • pad D m (x + (2 * m₀) • l) = m₁ • R • pad D m (m₀ • (x + (2 * m₀) • l)) := by
        rw [pad_nsmul, smul_smul, smul_smul]; congr 1; ring
      rw [this]
      exact AddSubgroup.nsmul_mem _ (hRA _ hy) _)
    (fun i => by rw [mul_smul]; exact AddSubgroup.nsmul_mem _ (ht₁ i) _) hAd (fun _ => trivial) (fun _ => trivial)
  have hd := differentiable_comb D (tor0 D cc δ) c₁ t₁ (GlobalTheory.T.U_pullB_ne_zero_and_invariant_four_smul D hG cc δ hc (N + m) N' r B hB).1
  refine ⟨?_, ?_⟩
  · rw [← hp1, hGG, U_pad, GlobalTheory.T.taylorConjugate_tangentSpacePadZeroColumns D N N' m ⊤ σ _ (differentiable_U D _ _ hd), hg1, GlobalTheory.T.taylorConjugate_tangentSpacePadZeroColumns D N N' m ⊤ σ _ hd, U_pad]
  · have := (hg2 trivial).1
    rwa [wdPh_pad, wdPh_pad, hp2] at this

/- English proof (translation)
Simplify using `only [cj, TaylorLogMetric.liftM, dif_pos ha, dif_pos hb, dif_pos (M.mul_mem ha hb), ← map_mul]`. Both sides reduce to the same expression.
-/
theorem cj_mul (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) {a b : ℂ} (ha : a ∈ M) (hb : b ∈ M) :
    cj M ρ (a * b) = cj M ρ a * cj M ρ b := by
  simp only [cj, TaylorLogMetric.liftM, dif_pos ha, dif_pos hb, dif_pos (M.mul_mem ha hb), ← map_mul]
  rfl

/- English proof (translation)
Establish `h1 : (-1 : ℂ) ∈ M` using `M.neg_mem M.one_mem`. Break down `Int.even_or_odd m with h | h` into its components or cases. Rewrite using `[h.neg_one_zpow]`. Use `⟨M.one_mem, ?_⟩` and prove the remaining obligations. Simplify using `only [cj, TaylorLogMetric.liftM, dif_pos M.one_mem]`.

Conclude with `map_one ρ`. Rewrite using `[h.neg_one_zpow]`. Use `⟨h1, ?_⟩` and prove the remaining obligations. Simplify using `only [cj, TaylorLogMetric.liftM, dif_pos h1]`. Establish `: (⟨-1, h1⟩ : M) = -1` using `rfl`.

Rewrite using `[this, map_neg, map_one]`.
-/
theorem cj_neg_one_zpow (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) (m : ℤ) :
    (-1 : ℂ) ^ m ∈ M ∧ cj M ρ ((-1 : ℂ) ^ m) = (-1 : ℂ) ^ m := by
  have h1 : (-1 : ℂ) ∈ M := M.neg_mem M.one_mem
  rcases Int.even_or_odd m with h | h
  · rw [h.neg_one_zpow]
    refine ⟨M.one_mem, ?_⟩
    simp only [cj, TaylorLogMetric.liftM, dif_pos M.one_mem]
    exact map_one ρ
  · rw [h.neg_one_zpow]
    refine ⟨h1, ?_⟩
    simp only [cj, TaylorLogMetric.liftM, dif_pos h1]
    have : (⟨-1, h1⟩ : M) = -1 := rfl
    rw [this, map_neg, map_one]

/- English proof (translation)
Establish `ht : ∀ α, TaylorLogMetric.taylor D (fun z => a * F z) α = a * TaylorLogMetric.taylor D F α`. Introduce `α`. Establish `han : AnalyticAt ℂ F 0` using `SCV.analyticAt_iff_eventually_differentiableAt.2 (Filter.Eventually.of_forall hF)`. Establish `: (fun z => a * F z) = a • F` using `rfl`. Unfold `TaylorLogMetric.taylor`.

Rewrite using `[this, iteratedFDeriv_const_smul_apply han.contDiffAt]`. Simplify using `only [ContinuousMultilinearMap.smul_apply, smul_eq_mul, mul_div_assoc]`. Use function extensionality and compare the values at `z`. Unfold `fnConj`. Rewrite using `[← tsum_mul_left]`.

Use `tsum_congr fun α => ?_` and prove the remaining obligations. Rewrite using `[ht, ← mul_assoc]`. Conclude with `congrArg (· * mono D α z) (cj_mul M ρ ha (hM α))`.
-/
theorem fnConj_mul (D : D7) {N N' : ℕ} (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) (a : ℂ) (ha : a ∈ M)
    (F : VC D N N' → ℂ) (hF : Differentiable ℂ F) (hM : CoefIn D F M) :
    fnConj D M ρ (fun z => a * F z) = fun z => cj M ρ a * fnConj D M ρ F z := by
  have ht : ∀ α, TaylorLogMetric.taylor D (fun z => a * F z) α = a * TaylorLogMetric.taylor D F α := by
    intro α
    have han : AnalyticAt ℂ F 0 := SCV.analyticAt_iff_eventually_differentiableAt.2 (Filter.Eventually.of_forall hF)
    have : (fun z => a * F z) = a • F := rfl
    unfold TaylorLogMetric.taylor
    rw [this, iteratedFDeriv_const_smul_apply han.contDiffAt]
    simp only [ContinuousMultilinearMap.smul_apply, smul_eq_mul, mul_div_assoc]
  funext z
  unfold fnConj
  rw [← tsum_mul_left]
  refine tsum_congr fun α => ?_
  rw [ht, ← mul_assoc]
  exact congrArg (· * mono D α z) (cj_mul M ρ ha (hM α))

/- English proof (translation)
Introduce `D cc δ hc M ρ hK hD N N' L L' hL hL' k c t e₀ x x' m₀ he hm hx ht hA hG hU`. Take `⟨s, b, a, a', hb, ha, hxa, hxa', haa⟩` from `hA`. Take `⟨σ, hσ⟩` from `GlobalTheory.T.exists_complexEndomorphism_eq_on_countable M ρ ((⋃ τ, Set.range (embT D τ)) ∪ Set.range D.host.φ₀ ∪ {g2 (lamOf D cc δ), g3 (lamOf D cc δ), wdPh D (tor0 D cc δ) x} ∪ Set.range (fun j => wpF (lamOf D cc δ) (a j / ((2 * m₀ : ℕ) : ℂ))) ∪ Set.range (fun j => wpD (lamOf …`. Simplify using `only [Set.countable_union]`. Use `⟨⟨⟨⟨⟨⟨Set.countable_iUnion fun _ => Set.countable_range _, Set.countable_range _⟩, ?_⟩, Set.countable_range _⟩, Set.countable_range _⟩, Set.countable_range _⟩, Set.countable_range _⟩` and prove the remaining obligations.

Conclude with `(Set.toFinite _).countable)`. Establish `hlam : lamConj ⊤ σ (lamOf D cc δ) = lamConj M ρ (lamOf D cc δ)`. Establish `h2` using `hσ (g2 (lamOf D cc δ)) (by simp) hD.2.1`. Establish `h3` using `hσ (g3 (lamOf D cc δ)) (by simp) hD.2.2`. Unfold `cj at h2 h3`.

Unfold `lamConj`. Rewrite using `[h2, h3]`. Establish `htor : torConj D (tor0 D cc δ) ⊤ σ = torConj D (tor0 D cc δ) M ρ`. Establish `h : (fun τ y => σ (TaylorLogMetric.liftM ⊤ ((tor0 D cc δ).emb τ y))) = fun τ y => ρ (TaylorLogMetric.liftM M ((tor0 D cc δ).emb τ y))`. Use function extensionality and compare the values at `τ y`.

Conclude with `hσ (embT D τ y) (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Set.mem_iUnion.2 ⟨τ, y, rfl⟩))))))) (hD.1 τ y)`. Unfold `torConj`. Rewrite using `[h]`. Conclude with `congrArg _ hlam`. Establish `hK' : FixK D ⊤ σ` using `fun y => ⟨trivial, (hσ _ (by simp) (hK y).1).trans (hK y).2⟩`.

Establish `hfn : ∀ F : VC D N N' → ℂ, (∀ α, cj ⊤ σ (TaylorLogMetric.taylor D F α) = cj M ρ (TaylorLogMetric.taylor D F α)) → fnConj D ⊤ σ F = fnConj D M ρ F`. Introduce `F hF`. Use function extensionality and compare the values at `z`. Conclude with `tsum_congr fun α => congrArg (· * mono D α z) (hF α)`. Establish `hA' : AdpV D (tor0 D cc δ) ⊤ σ L L' (2 * m₀) x x'`.

Use `⟨s, b, a, a', hb, ha, hxa, by rw [htor]; exact hxa', fun j => ?_⟩` and prove the remaining obligations. Establish `h` using `haa j`. Unfold `Adp1 StarPt at h ⊢`. Express the relevant statement in the definitionally equal form `_ ∧ _ ∈ lamConj ⊤ σ (lamOf D cc δ) ∨ _ ∧ _ ∉ lamConj ⊤ σ (lamOf D cc δ) ∧ _ ∧ _ ∧ wpF (lamConj ⊤ σ (lamOf D cc δ)) _ = _ ∧ wpD (lamConj ⊤ σ (lamOf D cc δ)) _ = _`. Rewrite using `[hlam]`.

Break down `h with h | ⟨h1, h2, h3, h4, h5, h6⟩` into its components or cases. Conclude with `Or.inl h`. Use `Or.inr ⟨h1, h2, trivial, trivial, h5.trans (hσ _ ?_ h3).symm, h6.trans (hσ _ ?_ h4).symm⟩` and prove the remaining obligations. Conclude with `Or.inl (Or.inl (Or.inl (Or.inr ⟨j, rfl⟩)))`. Conclude with `Or.inl (Or.inl (Or.inr ⟨j, rfl⟩))`.

Take `⟨h1, h2⟩` from `gal_top D cc δ hc σ hK' L L' hL hL' c t e₀ x x' m₀ he hm hx ht hA'`. Rewrite `h1` using `[hfn _ (fun α => hσ _ (Or.inr ⟨α, rfl⟩) (hU α)), hfn _ (fun α => hσ _ (Or.inl (Or.inr ⟨α, rfl⟩)) (hG α)), htor]`. Rewrite `h2` using `[htor]`. Establish `hd` using `differentiable_U D (tor0 D cc δ) x (differentiable_comb D (tor0 D cc δ) c t he.1)`. Use `⟨h1, fun hw => ?_, fun p hp hp2 ⟨j, hj⟩ => ?_⟩` and prove the remaining obligations.

Establish `h3` using `(hσ _ (by simp) hw).symm.trans h2`. Use `⟨h3, ?_⟩` and prove the remaining obligations. Unfold `Wd`. Rewrite using `[fnConj_mul D M ρ _ hw _ hd hU, h1, h3]`. Take `⟨-, -, -, -, -, -, hq⟩` from `GlobalTheory.T.theta_space_selfDual_pair_at_most_line D (GlobalTheory.T.inducedType_thetaGenusOne_permutes D).1 cc δ hc N N' (La D (tor0 D cc δ) L L') (Or.inr ⟨L, L', hL, hL', rfl⟩)`.

Take `⟨m, hmq⟩` from `hq _ hj`. Establish `hpq : (p : ℝ) ^ (2 * j) * qH D (tor0 D cc δ) x = (m : ℝ)`. Rewrite using `[← hmq]`. Unfold `qH`. Rewrite using `[Hf_nsmul_left, Hf_nsmul_right, ← Complex.ofReal_natCast, Complex.re_ofReal_mul, Complex.re_ofReal_mul]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Take `⟨h4, h5⟩` from `GlobalTheory.T.thetaOddPrimePhase_conj_invariant D _ _ N N' x x' σ p (2 * j) m hp hp2 hpq h2`. Unfold `Wop`. Rewrite using `[h4, h5, fnConj_mul D M ρ _ (cj_neg_one_zpow M ρ m).1 _ hd hU, h1, (cj_neg_one_zpow M ρ m).2]`.
-/
theorem gal_all : ∀ D : D7, gal D := by
  intro D cc δ hc M ρ hK hD N N' L L' hL hL' k c t e₀ x x' m₀ he hm hx ht hA hG hU
  obtain ⟨s, b, a, a', hb, ha, hxa, hxa', haa⟩ := hA
  obtain ⟨σ, hσ⟩ := GlobalTheory.T.exists_complexEndomorphism_eq_on_countable M ρ
    ((⋃ τ, Set.range (embT D τ)) ∪ Set.range D.host.φ₀ ∪
      {g2 (lamOf D cc δ), g3 (lamOf D cc δ), wdPh D (tor0 D cc δ) x} ∪
      Set.range (fun j => wpF (lamOf D cc δ) (a j / ((2 * m₀ : ℕ) : ℂ))) ∪
      Set.range (fun j => wpD (lamOf D cc δ) (a j / ((2 * m₀ : ℕ) : ℂ))) ∪
      Set.range (TaylorLogMetric.taylor D (comb D (tor0 D cc δ) c t e₀)) ∪
      Set.range (TaylorLogMetric.taylor D (U D (tor0 D cc δ) x (comb D (tor0 D cc δ) c t e₀)))) (by
      haveI : Countable D.host.E := Countable.of_equiv _ (Module.finBasis ℚ D.host.E).equivFun.toEquiv.symm
      simp only [Set.countable_union]
      refine ⟨⟨⟨⟨⟨⟨Set.countable_iUnion fun _ => Set.countable_range _, Set.countable_range _⟩, ?_⟩,
        Set.countable_range _⟩, Set.countable_range _⟩, Set.countable_range _⟩, Set.countable_range _⟩
      exact (Set.toFinite _).countable)
  have hlam : lamConj ⊤ σ (lamOf D cc δ) = lamConj M ρ (lamOf D cc δ) := by
    have h2 := hσ (g2 (lamOf D cc δ)) (by simp) hD.2.1
    have h3 := hσ (g3 (lamOf D cc δ)) (by simp) hD.2.2
    unfold cj at h2 h3
    unfold lamConj
    rw [h2, h3]
  have htor : torConj D (tor0 D cc δ) ⊤ σ = torConj D (tor0 D cc δ) M ρ := by
    have h : (fun τ y => σ (TaylorLogMetric.liftM ⊤ ((tor0 D cc δ).emb τ y))) =
        fun τ y => ρ (TaylorLogMetric.liftM M ((tor0 D cc δ).emb τ y)) := by
      funext τ y
      exact hσ (embT D τ y) (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Set.mem_iUnion.2 ⟨τ, y, rfl⟩)))))))
        (hD.1 τ y)
    unfold torConj
    rw [h]
    exact congrArg _ hlam
  have hK' : FixK D ⊤ σ := fun y => ⟨trivial, (hσ _ (by simp) (hK y).1).trans (hK y).2⟩
  have hfn : ∀ F : VC D N N' → ℂ, (∀ α, cj ⊤ σ (TaylorLogMetric.taylor D F α) = cj M ρ (TaylorLogMetric.taylor D F α)) →
      fnConj D ⊤ σ F = fnConj D M ρ F := by
    intro F hF
    funext z
    exact tsum_congr fun α => congrArg (· * mono D α z) (hF α)
  have hA' : AdpV D (tor0 D cc δ) ⊤ σ L L' (2 * m₀) x x' := by
    refine ⟨s, b, a, a', hb, ha, hxa, by rw [htor]; exact hxa', fun j => ?_⟩
    have h := haa j
    unfold Adp1 StarPt at h ⊢
    change _ ∧ _ ∈ lamConj ⊤ σ (lamOf D cc δ) ∨ _ ∧ _ ∉ lamConj ⊤ σ (lamOf D cc δ) ∧ _ ∧ _ ∧
      wpF (lamConj ⊤ σ (lamOf D cc δ)) _ = _ ∧ wpD (lamConj ⊤ σ (lamOf D cc δ)) _ = _
    rw [hlam]
    rcases h with h | ⟨h1, h2, h3, h4, h5, h6⟩
    · exact Or.inl h
    · refine Or.inr ⟨h1, h2, trivial, trivial, h5.trans (hσ _ ?_ h3).symm, h6.trans (hσ _ ?_ h4).symm⟩
      · exact Or.inl (Or.inl (Or.inl (Or.inr ⟨j, rfl⟩)))
      · exact Or.inl (Or.inl (Or.inr ⟨j, rfl⟩))
  obtain ⟨h1, h2⟩ := gal_top D cc δ hc σ hK' L L' hL hL' c t e₀ x x' m₀ he hm hx ht hA'
  rw [hfn _ (fun α => hσ _ (Or.inr ⟨α, rfl⟩) (hU α)), hfn _ (fun α => hσ _ (Or.inl (Or.inr ⟨α, rfl⟩)) (hG α)),
    htor] at h1
  rw [htor] at h2
  have hd := differentiable_U D (tor0 D cc δ) x (differentiable_comb D (tor0 D cc δ) c t he.1)
  refine ⟨h1, fun hw => ?_, fun p hp hp2 ⟨j, hj⟩ => ?_⟩
  · have h3 := (hσ _ (by simp) hw).symm.trans h2
    refine ⟨h3, ?_⟩
    unfold Wd
    rw [fnConj_mul D M ρ _ hw _ hd hU, h1, h3]
  · obtain ⟨-, -, -, -, -, -, hq⟩ := GlobalTheory.T.theta_space_selfDual_pair_at_most_line D (GlobalTheory.T.inducedType_thetaGenusOne_permutes D).1 cc δ hc N N' (La D (tor0 D cc δ) L L')
      (Or.inr ⟨L, L', hL, hL', rfl⟩)
    obtain ⟨m, hmq⟩ := hq _ hj
    have hpq : (p : ℝ) ^ (2 * j) * qH D (tor0 D cc δ) x = (m : ℝ) := by
      rw [← hmq]
      unfold qH
      rw [Hf_nsmul_left, Hf_nsmul_right, ← Complex.ofReal_natCast, Complex.re_ofReal_mul, Complex.re_ofReal_mul]
      push_cast
      ring
    obtain ⟨h4, h5⟩ := GlobalTheory.T.thetaOddPrimePhase_conj_invariant D _ _ N N' x x' σ p (2 * j) m hp hp2 hpq h2
    unfold Wop
    rw [h4, h5, fnConj_mul D M ρ _ (cj_neg_one_zpow M ρ m).1 _ hd hU, h1, (cj_neg_one_zpow M ρ m).2]

end GlobalTheory.GalTheta
