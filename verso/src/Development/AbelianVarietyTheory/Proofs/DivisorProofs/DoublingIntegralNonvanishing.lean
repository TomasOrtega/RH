import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearWittModelLocal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearWittModelUnitaryAction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearBarModelUnitaryAction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearWeilFunctionalUnramifiedVector
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitUnitaryLiftTendstoOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearWeilFunctionalSphericalValue
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorPureTensorComponentAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzMemL2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalizingWeightEqualOffPlaceMasses
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStdCharNegOneOfStandardTraceAdelicAddChar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealScalarArchimedeanAdeleSmulMatrixRealPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinsetLatStabMemNhds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplementaryAdelicSchwartzOfNonzeroLocal
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterTrivialMatrixLatticeOpenCompactBasis

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling GlobalTheory.ThK.Bot
open Formalism.L2.Host (aboveF)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.ThK.BotRam

section Val

variable {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ] (w : Valuation K Γ) {n d : ℕ}

def frame (K : Type) [Field K] {n d : ℕ} (h : n ≤ d) : Matrix (Fin n) (Fin d) K :=
  Matrix.of fun i j => if j = Fin.castLE h i then 1 else 0

/- English proof (translation)
Simplify using `[frame, Matrix.mul_apply, eq_comm]`.
-/
theorem mul_frame (h : n ≤ d) (M : Matrix (Fin n) (Fin n) K) (i j : Fin n) :
    (M * frame K h) i (Fin.castLE h j) = M i j := by
  simp [frame, Matrix.mul_apply, eq_comm]

/- English proof (translation)
Unfold `frame`. Rewrite using `[Matrix.of_apply]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem val_frame (h : n ≤ d) (i : Fin n) (j : Fin d) : w (frame K h i j) ≤ 1 := by
  unfold frame
  rw [Matrix.of_apply]
  split_ifs <;> simp

/- English proof (translation)
Rewrite using `[Matrix.mul_apply]`. Use `w.map_sum_le fun k _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul]`. Conclude with `mul_le_mul' (hM _ _) (hN _ _)`.
-/
theorem val_mul_le {a b : Γ} {m p q : ℕ} {M : Matrix (Fin m) (Fin p) K} {N : Matrix (Fin p) (Fin q) K}
    (hM : ∀ i j, w (M i j) ≤ a) (hN : ∀ i j, w (N i j) ≤ b) (i : Fin m) (j : Fin q) : w ((M * N) i j) ≤ a * b := by
  rw [Matrix.mul_apply]
  refine w.map_sum_le fun k _ => ?_
  rw [map_mul]
  exact mul_le_mul' (hM _ _) (hN _ _)

/- English proof (translation)
Rewrite using `[Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem val_one_le (i j : Fin n) : w ((1 : Matrix (Fin n) (Fin n) K) i j) ≤ 1 := by
  rw [Matrix.one_apply]
  split_ifs <;> simp

/- English proof (translation)
Establish `hint : ∀ x, w x ≤ 1 → ψ x = 1` using `fun x hx => by simpa using (hψ x).2 hx 1 (by simp)`. Establish `hwt : 0 < w t` using `zero_lt_iff.2 ((w.ne_zero_iff).2 ht0)`. Take `⟨a, ha1, hah, i, j, hij⟩ : ∃ a : K, 1 ≤ w a ∧ (∀ i j, w (h i j) ≤ w a) ∧ ∃ i j, w t * w a < w ((h - 1) i j)` from `by push_neg at hh`. Take `⟨i₀, j₀, h₀⟩` from `hh`. Take `⟨p, -, hp⟩` from `Finset.exists_max_image (Finset.univ : Finset (Fin n × Fin n)) (fun p => w (h p.1 p.2)) ⟨(i₀, j₀), Finset.mem_univ _⟩`.

Distinguish the cases in `h1 : w (h p.1 p.2) ≤ 1`. Use `⟨1, by simp, fun i j => ?_, i₀, j₀, by simpa using h₀⟩` and prove the remaining obligations. Rewrite using `[map_one]`. Conclude with `(hp (i, j) (Finset.mem_univ _)).trans h1`. Use `push_neg at h1`.

Use `⟨h p.1 p.2, h1.le, fun i j => hp (i, j) (Finset.mem_univ _), p.1, p.2, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.sub_apply, w.map_sub_eq_of_lt_left ((val_one_le w _ _).trans_lt h1)]`. Combine the equalities or inequalities in the displayed calculation. Establish `hwa : 0 < w a` using `zero_lt_one.trans_le ha1`. Establish `hta : 0 < w (t * a)` using `by rw [map_mul]; exact mul_pos hwt hwa`.

Establish `hx : ¬ w ((h - 1) i j / (t * a)) ≤ 1`. Rewrite using `[map_div₀, div_le_one₀ hta, map_mul]`. Conclude with `not_le.2 hij`. Rewrite `hx` using `[← hψ]`. Use `push_neg at hx`.

Take `⟨y, hy, hy1⟩` from `hx`. Use `⟨(y / (t * a)) • Matrix.entryLinearMap K K i (Fin.castLE hnd j), fun Z hZ => ?_, ?_⟩` and prove the remaining obligations. Establish `key : ∀ z : K, w z ≤ w a * w t → ψ (y / (t * a) * z) = 1` using `fun z hz => hint _ (by`. Rewrite using `[map_mul, map_div₀, div_mul_eq_mul_div, div_le_one₀ hta, map_mul, mul_comm (w t)]`. Combine the equalities or inequalities in the displayed calculation.

Use `⟨key _ ((hZ _ _).trans ?_), key _ (val_mul_le w hah hZ _ _)⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Express the relevant statement in the definitionally equal form `ψ (y / (t * a) * ((h - 1) * frame K hnd : Matrix (Fin n) (Fin d) K) i (Fin.castLE hnd j)) ≠ 1`. Rewrite using `[mul_frame]`. Use `hy1 using 2` and compare the differences between its conclusion and the goal.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_sep (ψ : AddChar K ℂ) (hψ : ∀ x, (∀ y, w y ≤ 1 → ψ (x * y) = 1) ↔ w x ≤ 1) (hnd : n ≤ d) {t : K}
    (ht0 : t ≠ 0) (ht1 : w t < 1) (h : Matrix (Fin n) (Fin n) K) (hh : ¬ ∀ i j, w ((h - 1) i j) ≤ w t) :
    ∃ l : Matrix (Fin n) (Fin d) K →ₗ[K] K, (∀ Z, (∀ i j, w (Z i j) ≤ w t) → ψ (l Z) = 1 ∧ ψ (l (h * Z)) = 1) ∧
      ψ (l ((h - 1) * frame K hnd)) ≠ 1 := by
  have hint : ∀ x, w x ≤ 1 → ψ x = 1 := fun x hx => by simpa using (hψ x).2 hx 1 (by simp)
  have hwt : 0 < w t := zero_lt_iff.2 ((w.ne_zero_iff).2 ht0)
  obtain ⟨a, ha1, hah, i, j, hij⟩ : ∃ a : K, 1 ≤ w a ∧ (∀ i j, w (h i j) ≤ w a) ∧ ∃ i j, w t * w a < w ((h - 1) i j) := by
    push_neg at hh
    obtain ⟨i₀, j₀, h₀⟩ := hh
    obtain ⟨p, -, hp⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin n × Fin n)) (fun p => w (h p.1 p.2))
      ⟨(i₀, j₀), Finset.mem_univ _⟩
    by_cases h1 : w (h p.1 p.2) ≤ 1
    · refine ⟨1, by simp, fun i j => ?_, i₀, j₀, by simpa using h₀⟩
      rw [map_one]
      exact (hp (i, j) (Finset.mem_univ _)).trans h1
    · push_neg at h1
      refine ⟨h p.1 p.2, h1.le, fun i j => hp (i, j) (Finset.mem_univ _), p.1, p.2, ?_⟩
      rw [Matrix.sub_apply, w.map_sub_eq_of_lt_left ((val_one_le w _ _).trans_lt h1)]
      calc w t * w (h p.1 p.2) < 1 * w (h p.1 p.2) := mul_lt_mul_of_pos_right ht1 (zero_lt_one.trans h1)
        _ = _ := one_mul _
  have hwa : 0 < w a := zero_lt_one.trans_le ha1
  have hta : 0 < w (t * a) := by rw [map_mul]; exact mul_pos hwt hwa
  have hx : ¬ w ((h - 1) i j / (t * a)) ≤ 1 := by
    rw [map_div₀, div_le_one₀ hta, map_mul]
    exact not_le.2 hij
  rw [← hψ] at hx
  push_neg at hx
  obtain ⟨y, hy, hy1⟩ := hx
  refine ⟨(y / (t * a)) • Matrix.entryLinearMap K K i (Fin.castLE hnd j), fun Z hZ => ?_, ?_⟩
  · have key : ∀ z : K, w z ≤ w a * w t → ψ (y / (t * a) * z) = 1 := fun z hz => hint _ (by
      rw [map_mul, map_div₀, div_mul_eq_mul_div, div_le_one₀ hta, map_mul, mul_comm (w t)]
      calc w y * w z ≤ 1 * (w a * w t) := mul_le_mul' hy hz
        _ = _ := one_mul _)
    refine ⟨key _ ((hZ _ _).trans ?_), key _ (val_mul_le w hah hZ _ _)⟩
    calc w t = 1 * w t := (one_mul _).symm
      _ ≤ _ := mul_le_mul' ha1 le_rfl
  · change ψ (y / (t * a) * ((h - 1) * frame K hnd : Matrix (Fin n) (Fin d) K) i (Fin.castLE hnd j)) ≠ 1
    rw [mul_frame]
    convert hy1 using 2
    ring

/- English proof (translation)
Introduce `i j`. Establish `e : h * Y - frame K hnd = (h - 1) * (Y - frame K hnd) + (h - 1) * frame K hnd + (Y - frame K hnd)`. Simplify using `only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul]`. Normalize the expressions using the abelian group laws. Rewrite using `[e, Matrix.add_apply, Matrix.add_apply]`.

Use `w.map_add_le (w.map_add_le ?_ ?_) (hY i j)` and prove the remaining obligations. Conclude with `(val_mul_le w hh (fun i j => (hY i j).trans ht1.le) i j).trans_eq (mul_one _)`. Conclude with `(val_mul_le w hh (val_frame w hnd) i j).trans_eq (mul_one _)`.
-/
theorem mul_mem_coset (hnd : n ≤ d) {t : K} (ht1 : w t < 1) {h : Matrix (Fin n) (Fin n) K}
    (hh : ∀ i j, w ((h - 1) i j) ≤ w t) {Y : Matrix (Fin n) (Fin d) K} (hY : ∀ i j, w ((Y - frame K hnd) i j) ≤ w t) :
    ∀ i j, w ((h * Y - frame K hnd) i j) ≤ w t := by
  intro i j
  have e : h * Y - frame K hnd = (h - 1) * (Y - frame K hnd) + (h - 1) * frame K hnd + (Y - frame K hnd) := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul]
    abel
  rw [e, Matrix.add_apply, Matrix.add_apply]
  refine w.map_add_le (w.map_add_le ?_ ?_) (hY i j)
  · exact (val_mul_le w hh (fun i j => (hY i j).trans ht1.le) i j).trans_eq (mul_one _)
  · exact (val_mul_le w hh (val_frame w hnd) i j).trans_eq (mul_one _)

/- English proof (translation)
Introduce `i j`. Establish `e : H - 1 = -(H * (h - 1))`. Rewrite using `[Matrix.mul_sub, hH, Matrix.mul_one, neg_sub]`. Rewrite using `[e, Matrix.neg_apply, w.map_neg]`. Conclude with `(val_mul_le w hi hh i j).trans_eq (one_mul _)`.
-/
theorem inv_cong {t : K} {h H : Matrix (Fin n) (Fin n) K} (hH : H * h = 1)
    (hh : ∀ i j, w ((h - 1) i j) ≤ w t) (hi : ∀ i j, w (H i j) ≤ 1) : ∀ i j, w ((H - 1) i j) ≤ w t := by
  intro i j
  have e : H - 1 = -(H * (h - 1)) := by
    rw [Matrix.mul_sub, hH, Matrix.mul_one, neg_sub]
  rw [e, Matrix.neg_apply, w.map_neg]
  exact (val_mul_le w hi hh i j).trans_eq (one_mul _)

end Val

section Box

variable {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)}

def box (m p : ℕ) (t : v.adicCompletion F) : Set (Matrix (Fin m) (Fin p) (v.adicCompletion F)) :=
  {Z | ∀ i j, Valued.v (Z i j) ≤ Valued.v t}

/- English proof (translation)
Establish `hwt : 0 < Valued.v t` using `zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 ht)`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce `hx`. Use `⟨x / t, ?_, mul_div_cancel₀ x ht⟩` and prove the remaining obligations.

Rewrite using `[SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers, map_div₀, div_le_one₀ hwt]`. Conclude with `hx`. Introduce and unpack `⟨y, hy, rfl⟩`. Rewrite `hy` using `[SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers]`. Express the relevant statement in the definitionally equal form `Valued.v (t * y) ≤ _`.

Rewrite using `[map_mul]`. Conclude with `(mul_le_mul' le_rfl hy).trans_eq (mul_one _)`.
-/
theorem ball_eq {t : v.adicCompletion F} (ht : t ≠ 0) : {x : v.adicCompletion F | Valued.v x ≤ Valued.v t} =
    (Homeomorph.mulLeft₀ t ht) '' (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
  have hwt : 0 < Valued.v t := zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 ht)
  ext x
  constructor
  · intro hx
    refine ⟨x / t, ?_, mul_div_cancel₀ x ht⟩
    rw [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers, map_div₀, div_le_one₀ hwt]
    exact hx
  · rintro ⟨y, hy, rfl⟩
    rw [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers] at hy
    change Valued.v (t * y) ≤ _
    rw [map_mul]
    exact (mul_le_mul' le_rfl hy).trans_eq (mul_one _)

/- English proof (translation)
Establish `h : IsOpen {x : v.adicCompletion F | Valued.v x ≤ Valued.v t}`. Rewrite using `[ball_eq ht]`. Conclude with `(Homeomorph.isOpenMap _) _ (Valued.isOpen_valuationSubring _)`. Establish `e : box m p t = ⋂ i, ⋂ j, (fun Z : Matrix (Fin m) (Fin p) (v.adicCompletion F) => Z i j) ⁻¹' {x : v.adicCompletion F | Valued.v x ≤ Valued.v t}`. Use extensionality with `Z`.

Simplify using `[box]`. Rewrite using `[e]`. Conclude with `isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => h.preimage (continuous_id.matrix_elem i j)`.
-/
theorem isOpen_box (m p : ℕ) {t : v.adicCompletion F} (ht : t ≠ 0) : IsOpen (box m p t) := by
  have h : IsOpen {x : v.adicCompletion F | Valued.v x ≤ Valued.v t} := by
    rw [ball_eq ht]
    exact (Homeomorph.isOpenMap _) _ (Valued.isOpen_valuationSubring _)
  have e : box m p t = ⋂ i, ⋂ j, (fun Z : Matrix (Fin m) (Fin p) (v.adicCompletion F) => Z i j) ⁻¹'
      {x : v.adicCompletion F | Valued.v x ≤ Valued.v t} := by
    ext Z; simp [box]
  rw [e]
  exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => h.preimage (continuous_id.matrix_elem i j)

/- English proof (translation)
Establish `h : IsCompact {x : v.adicCompletion F | Valued.v x ≤ Valued.v t}`. Rewrite using `[ball_eq ht]`. Conclude with `(isCompact_iff_compactSpace.2 hO).image (Homeomorph.continuous _)`. Establish `e : box m p t = Set.univ.pi fun _ : Fin m => Set.univ.pi fun _ : Fin p => {x : v.adicCompletion F | Valued.v x ≤ Valued.v t}`. Use extensionality with `Z`.

Conclude with `⟨fun h i _ j _ => h i j, fun h i j => h i trivial j trivial⟩`. Rewrite using `[e]`. Conclude with `isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => h`.
-/
theorem isCompact_box (hO : CompactSpace (v.adicCompletionIntegers F)) (m p : ℕ) {t : v.adicCompletion F} (ht : t ≠ 0) :
    IsCompact (box m p t) := by
  have h : IsCompact {x : v.adicCompletion F | Valued.v x ≤ Valued.v t} := by
    rw [ball_eq ht]
    exact (isCompact_iff_compactSpace.2 hO).image (Homeomorph.continuous _)
  have e : box m p t = Set.univ.pi fun _ : Fin m => Set.univ.pi fun _ : Fin p =>
      {x : v.adicCompletion F | Valued.v x ≤ Valued.v t} := by
    ext Z; exact ⟨fun h i _ j _ => h i j, fun h i j => h i trivial j trivial⟩
  rw [e]
  exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => h

/- English proof (translation)
Establish `h1 : ∀ᶠ t in 𝓝 (0 : v.adicCompletion F), ∀ Z ∈ box m p (1 : v.adicCompletion F), t • Z ∈ V`. Use `(isCompact_box hO m p one_ne_zero).eventually_forall_of_forall_eventually fun Z _ => ?_` and prove the remaining obligations. Establish `hc : Continuous fun x : v.adicCompletion F × Matrix (Fin m) (Fin p) (v.adicCompletion F) => x.1 • x.2` using `continuous_smul`. Conclude with `hc.continuousAt.preimage_mem_nhds (by simpa using hV)`. Establish `h2 : ∀ᶠ t in 𝓝 (0 : v.adicCompletion F), Valued.v t < 1`.

Take `⟨π, hπ⟩` from `v.valuation_exists_uniformizer F`. Establish `hπ' : Valued.v (π : v.adicCompletion F) = WithZero.exp (-1 : ℤ)`. Rewrite using `[HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hπ]`. Establish `h0 : (π : v.adicCompletion F) ≠ 0` using `fun h => by`. Rewrite `hπ'` using `[h, map_zero]`.

Conclude with `WithZero.exp_ne_zero hπ'.symm`. Establish `ho : IsOpen {x : v.adicCompletion F | Valued.v x ≤ Valued.v (π : v.adicCompletion F)}`. Rewrite using `[ball_eq h0]`. Conclude with `(Homeomorph.isOpenMap _) _ (Valued.isOpen_valuationSubring _)`. Use `filter_upwards [ho.mem_nhds (show (0 : v.adicCompletion F) ∈ _ by simp)] with x hx`.

Use `lt_of_le_of_lt hx ?_` and prove the remaining obligations. Rewrite using `[hπ', ← WithZero.exp_zero, WithZero.exp_lt_exp]`. Evaluate the numerical expressions. Use `haveI : (𝓝[≠] (0 : v.adicCompletion F)).NeBot := GlobalTheory.LinSchurLatt.nhdsNE_neBot' (k := Fv F v)`. Take `⟨t, ⟨ht1, ht2⟩, ht0⟩` from `(((h1.and h2).filter_mono (nhdsWithin_le_nhds (s := {0}ᶜ))).and self_mem_nhdsWithin).exists`.

Establish `ht0' : t ≠ 0` using `ht0`. Establish `hwt : 0 < Valued.v t` using `zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 ht0')`. Use `⟨t, ht0', ht2, fun Z hZ => ?_⟩` and prove the remaining obligations. Use `ht1 (t⁻¹ • Z) fun i j => by` as an intermediate fact. Rewrite using `[Matrix.smul_apply, smul_eq_mul, map_one, inv_mul_eq_div, map_div₀, div_le_one₀ hwt]`.

Conclude with `hZ i j`. Rewrite `this` using `[smul_inv_smul₀ ht0']`. Then use the resulting hypothesis.
-/
theorem exists_box_subset (hO : CompactSpace (v.adicCompletionIntegers F)) {m p : ℕ}
    {V : Set (Matrix (Fin m) (Fin p) (v.adicCompletion F))} (hV : V ∈ 𝓝 0) :
    ∃ t : v.adicCompletion F, t ≠ 0 ∧ Valued.v t < 1 ∧ box m p t ⊆ V := by
  have h1 : ∀ᶠ t in 𝓝 (0 : v.adicCompletion F), ∀ Z ∈ box m p (1 : v.adicCompletion F), t • Z ∈ V := by
    refine (isCompact_box hO m p one_ne_zero).eventually_forall_of_forall_eventually fun Z _ => ?_
    have hc : Continuous fun x : v.adicCompletion F × Matrix (Fin m) (Fin p) (v.adicCompletion F) => x.1 • x.2 :=
      continuous_smul
    exact hc.continuousAt.preimage_mem_nhds (by simpa using hV)
  have h2 : ∀ᶠ t in 𝓝 (0 : v.adicCompletion F), Valued.v t < 1 := by
    obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F
    have hπ' : Valued.v (π : v.adicCompletion F) = WithZero.exp (-1 : ℤ) := by
      rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hπ]
    have h0 : (π : v.adicCompletion F) ≠ 0 := fun h => by
      rw [h, map_zero] at hπ'
      exact WithZero.exp_ne_zero hπ'.symm
    have ho : IsOpen {x : v.adicCompletion F | Valued.v x ≤ Valued.v (π : v.adicCompletion F)} := by
      rw [ball_eq h0]
      exact (Homeomorph.isOpenMap _) _ (Valued.isOpen_valuationSubring _)
    filter_upwards [ho.mem_nhds (show (0 : v.adicCompletion F) ∈ _ by simp)] with x hx
    refine lt_of_le_of_lt hx ?_
    rw [hπ', ← WithZero.exp_zero, WithZero.exp_lt_exp]
    norm_num
  haveI : (𝓝[≠] (0 : v.adicCompletion F)).NeBot := GlobalTheory.LinSchurLatt.nhdsNE_neBot' (k := Fv F v)
  obtain ⟨t, ⟨ht1, ht2⟩, ht0⟩ := (((h1.and h2).filter_mono (nhdsWithin_le_nhds (s := {0}ᶜ))).and self_mem_nhdsWithin).exists
  have ht0' : t ≠ 0 := ht0
  have hwt : 0 < Valued.v t := zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 ht0')
  refine ⟨t, ht0', ht2, fun Z hZ => ?_⟩
  have := ht1 (t⁻¹ • Z) fun i j => by
    rw [Matrix.smul_apply, smul_eq_mul, map_one, inv_mul_eq_div, map_div₀, div_le_one₀ hwt]
    exact hZ i j
  rwa [smul_inv_smul₀ ht0'] at this

end Box

section Global

open scoped GlobalTheory.VacAny

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}

/- English proof (translation)
Establish `hev : Continuous (evFin F v)` using `(RestrictedProduct.continuous_eval v).comp continuous_snd`. Conclude with `(continuous_splitProj t).comp (GlobalTheory.AutFunCompare.continuous_tensNU (E := E) (evFin F v).toLinearMap (map_mul (evFin F v)) hev)`.
-/
theorem continuous_piW {v : Pl F} (t : E →ₐ[F] Fv F v) : Continuous (piW t) := by
  have hev : Continuous (evFin F v) := (RestrictedProduct.continuous_eval v).comp continuous_snd
  exact (continuous_splitProj t).comp
    (GlobalTheory.AutFunCompare.continuous_tensNU (E := E) (evFin F v).toLinearMap (map_mul (evFin F v)) hev)

/- English proof (translation)
Establish `h : Continuous (Matrix.GeneralLinearGroup.map (n` using `Fin n) (piW t)) := Continuous.units_map _ (continuous_id.matrix_map (continuous_piW t))`. Conclude with `(continuous_const.mul (h.comp continuous_subtype_val)).mul continuous_const`.
-/
theorem continuous_locMat {v : Pl F} (t : E →ₐ[F] Fv F v) {J : Matrix (Fin n) (Fin n) E} (c : GL (Fin n) (Fv F v)) :
    Continuous (GlobalTheory.KSplit.locMat (σ := σ) (J := J) t c) := by
  have h : Continuous (Matrix.GeneralLinearGroup.map (n := Fin n) (piW t)) :=
    Continuous.units_map _ (continuous_id.matrix_map (continuous_piW t))
  exact (continuous_const.mul (h.comp continuous_subtype_val)).mul continuous_const

/- English proof (translation)
Use `haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E`. Use `haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩`. Set `bF` to `Module.finBasis F E`. Set `B` to `Algebra.TensorProduct.basis (AF F) bF`. Set `c : Matrix (Fin n) (Fin n) (AE F E) → Fin n × Fin n × Fin (Module.finrank F E) → AF F` to `fun M j => B.repr (M j.1 j.2.1) j.2.2`.

Set `Nm : Fin n × Fin n × Fin (Module.finrank F E) → (Fin n → E) →ₗ[E] (Fin n → E)` to `fun j => (LinearMap.single E (fun _ : Fin n => E) j.1) ∘ₗ (bF j.2.2 • LinearMap.proj j.2.1)`. Set `iV : (Fin n → E) → (Fin n → AE F E)` to `fun y i => inclR (F := F) (AF F) (y i)`. Establish `key : ∀ M y, (M *ᵥ iV y) = ∑ j, c M j • iV (Nm j y)`. Introduce `M y`. Use function extensionality and compare the values at `r`.

Simplify using `only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply]`. Rewrite using `[Fintype.sum_prod_type]`. Use `symm`. Rewrite using `[Finset.sum_eq_single r]`. Rewrite using `[Fintype.sum_prod_type]`.

Use `symm`. Use `Finset.sum_congr rfl fun q _ => ?_` and prove the remaining obligations. Use `conv_lhs => rw [← B.sum_repr (M r q)]`. Rewrite using `[Finset.sum_mul]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Simplify using `[Nm, iV, B, c, Algebra.TensorProduct.basis_apply, inclR]`. Introduce `p _ hp`. Simplify using `[Nm, iV, Ne.symm hp]`. Simplify using the standard rewrite rules. Use `choose D hD0 hDL using fun j => GlobalTheory.AdelicLatticeIntegral.exists_nsmul_map_mem X.L hL (Nm j)`.

Set `c' : Matrix (Fin n) (Fin n) (AE F E) → Fin n × Fin n × Fin (Module.finrank F E) → AF F` to `fun M j => c M j * algebraMap F (AF F) ((D j : F)⁻¹)`. Establish `hcont : ∀ j, Continuous fun M => c' M j` using `fun j => ((IsModuleTopology.continuous_of_linearMap (B.coord j.2.2)).comp (continuous_id.matrix_elem j.1 j.2.1)).mul continuous_const`. Establish `hU : (⋂ j, (fun M => c' M j) ⁻¹' {a : AF F | ∀ w : Pl F, evFin F w a ∈ w.adicCompletionIntegers F}) ∈ 𝓝 (0 : Matrix (Fin n) (Fin n) (AE F E))`. Use `Filter.iInter_mem.2 fun j => (GlobalTheory.LatStabNbhd.isOpen_integral.preimage (hcont j)).mem_nhds fun w => ?_` and prove the remaining obligations. Simplify using `[c', c]`.

Use `Filter.mem_of_superset hU fun M hM z hz => ?_` and prove the remaining obligations. Establish `hc' : ∀ j w, evFin F w (c' M j) ∈ w.adicCompletionIntegers F` using `fun j w => Set.mem_iInter.1 hM j w`. Proceed by induction on `hz using AddSubgroup.closure_induction with`. Consider the case `mem z hz`. Take `⟨a, ha, hai, y, hy, rfl⟩` from `hz`.

Establish `hterm : ∀ j, a • (c M j • iV (Nm j y)) = (a * c' M j) • iV (D j • Nm j y)`. Introduce `j`. Establish `h1 : iV (D j • Nm j y) = D j • iV (Nm j y)`. Use function extensionality and compare the values at `i`. Simplify using `[iV]`.

Rewrite using `[h1, ← Nat.cast_smul_eq_nsmul (AF F), smul_smul, smul_smul]`. Use `congr 1`. Establish `h2 : (D j : F) ≠ 0` using `Nat.cast_ne_zero.mpr (hD0 j)`. Simplify using `only [c', mul_assoc]`. Rewrite using `[← map_natCast (algebraMap F (AF F)), ← map_mul, inv_mul_cancel₀ h2, map_one, mul_one]`.

Express the relevant statement in the definitionally equal form `M *ᵥ (a • iV y) ∈ _`. Rewrite using `[Matrix.mulVec_smul, key, Finset.smul_sum]`. Use `AddSubgroup.sum_mem _ fun j _ => ?_` and prove the remaining obligations. Rewrite using `[hterm j]`. Use `AddSubgroup.subset_closure ⟨a * c' M j, ?_, fun w => ?_, D j • Nm j y, hDL j y hy, rfl⟩` and prove the remaining obligations.

Establish `e : evI F (a * c' M j) = evI F a * evI F (c' M j)` using `map_mul (InfiniteAdeleRing.ringEquiv_mixedSpace F) _ _`. Rewrite using `[e, ha, zero_mul]`. Rewrite using `[map_mul]`. Conclude with `mul_mem (hai w) (hc' j w)`. Consider the case `zero => rw [Matrix.mulVec_zero]`.

Conclude with `zero_mem _`. Consider the case `add _ _ _ _ h1 h2 => rw [Matrix.mulVec_add]`. Conclude with `add_mem h1 h2`. Consider the case `neg _ _ h1 => rw [Matrix.mulVec_neg]`. Conclude with `neg_mem h1`.
-/
theorem mulVec_mem_latHat_mem_nhds (X : Spc F E n) (hL : X.L.IsLattice E) :
    {M : Matrix (Fin n) (Fin n) (AE F E) | ∀ z ∈ latHat X, M *ᵥ z ∈ latHat X} ∈
      𝓝 (0 : Matrix (Fin n) (Fin n) (AE F E)) := by
  classical
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  let bF := Module.finBasis F E
  let B := Algebra.TensorProduct.basis (AF F) bF
  let c : Matrix (Fin n) (Fin n) (AE F E) → Fin n × Fin n × Fin (Module.finrank F E) → AF F :=
    fun M j => B.repr (M j.1 j.2.1) j.2.2
  let Nm : Fin n × Fin n × Fin (Module.finrank F E) → (Fin n → E) →ₗ[E] (Fin n → E) := fun j =>
    (LinearMap.single E (fun _ : Fin n => E) j.1) ∘ₗ (bF j.2.2 • LinearMap.proj j.2.1)
  let iV : (Fin n → E) → (Fin n → AE F E) := fun y i => inclR (F := F) (AF F) (y i)
  have key : ∀ M y, (M *ᵥ iV y) = ∑ j, c M j • iV (Nm j y) := by
    intro M y
    funext r
    simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply]
    rw [Fintype.sum_prod_type]
    symm
    rw [Finset.sum_eq_single r]
    · rw [Fintype.sum_prod_type]
      symm
      refine Finset.sum_congr rfl fun q _ => ?_
      conv_lhs => rw [← B.sum_repr (M r q)]
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [Nm, iV, B, c, Algebra.TensorProduct.basis_apply, inclR]
    · intro p _ hp
      simp [Nm, iV, Ne.symm hp]
    · simp
  choose D hD0 hDL using fun j => GlobalTheory.AdelicLatticeIntegral.exists_nsmul_map_mem X.L hL (Nm j)
  let c' : Matrix (Fin n) (Fin n) (AE F E) → Fin n × Fin n × Fin (Module.finrank F E) → AF F :=
    fun M j => c M j * algebraMap F (AF F) ((D j : F)⁻¹)
  have hcont : ∀ j, Continuous fun M => c' M j := fun j =>
    ((IsModuleTopology.continuous_of_linearMap (B.coord j.2.2)).comp
      (continuous_id.matrix_elem j.1 j.2.1)).mul continuous_const
  have hU : (⋂ j, (fun M => c' M j) ⁻¹' {a : AF F | ∀ w : Pl F, evFin F w a ∈ w.adicCompletionIntegers F}) ∈
      𝓝 (0 : Matrix (Fin n) (Fin n) (AE F E)) := by
    refine Filter.iInter_mem.2 fun j => (GlobalTheory.LatStabNbhd.isOpen_integral.preimage (hcont j)).mem_nhds fun w => ?_
    simp [c', c]
  refine Filter.mem_of_superset hU fun M hM z hz => ?_
  have hc' : ∀ j w, evFin F w (c' M j) ∈ w.adicCompletionIntegers F := fun j w => Set.mem_iInter.1 hM j w
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, hai, y, hy, rfl⟩ := hz
    have hterm : ∀ j, a • (c M j • iV (Nm j y)) = (a * c' M j) • iV (D j • Nm j y) := by
      intro j
      have h1 : iV (D j • Nm j y) = D j • iV (Nm j y) := by
        funext i; simp [iV]
      rw [h1, ← Nat.cast_smul_eq_nsmul (AF F), smul_smul, smul_smul]
      congr 1
      have h2 : (D j : F) ≠ 0 := Nat.cast_ne_zero.mpr (hD0 j)
      simp only [c', mul_assoc]
      rw [← map_natCast (algebraMap F (AF F)), ← map_mul, inv_mul_cancel₀ h2, map_one, mul_one]
    change M *ᵥ (a • iV y) ∈ _
    rw [Matrix.mulVec_smul, key, Finset.smul_sum]
    refine AddSubgroup.sum_mem _ fun j _ => ?_
    rw [hterm j]
    refine AddSubgroup.subset_closure ⟨a * c' M j, ?_, fun w => ?_, D j • Nm j y, hDL j y hy, rfl⟩
    · have e : evI F (a * c' M j) = evI F a * evI F (c' M j) := map_mul (InfiniteAdeleRing.ringEquiv_mixedSpace F) _ _
      rw [e, ha, zero_mul]
    · rw [map_mul]; exact mul_mem (hai w) (hc' j w)
  | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
  | add _ _ _ _ h1 h2 => rw [Matrix.mulVec_add]; exact add_mem h1 h2
  | neg _ _ h1 => rw [Matrix.mulVec_neg]; exact neg_mem h1

/- English proof (translation)
Use `haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E`. Use `haveI : IsTopologicalRing (AE F E) := GlobalTheory.Doubling.isTopologicalRing_tens`. Establish `hL₂ : X₂.L.IsLattice E`. Rewrite using `[hD.lat]`. Conclude with `isLattice_sumLat _ _`.

Establish `hU` using `mulVec_mem_latHat_mem_nhds X₂ hL₂`. Establish `hb : Continuous fun M : Matrix (Fin n) (Fin n) (AE F E) => blkMat finSumFinEquiv M (1 : Matrix (Fin n) (Fin n) (AE F E)) - 1` using `((continuous_id.matrix_fromBlocks continuous_const continuous_const continuous_const).matrix_submatrix _ _).sub continuous_const`. Establish `hm : Continuous fun g : UA σ X.J => blkMat finSumFinEquiv (mat g) (1 : Matrix (Fin n) (Fin n) (AE F E)) - 1` using `hb.comp (Units.continuous_val.comp continuous_subtype_val)`. Establish `hm' : Continuous fun g : UA σ X.J => blkMat finSumFinEquiv (mat g⁻¹) (1 : Matrix (Fin n) (Fin n) (AE F E)) - 1` using `hb.comp (Units.continuous_coe_inv.comp continuous_subtype_val)`. Establish `h1` using `hm.continuousAt (x := 1) |>.preimage_mem_nhds (by rw [GlobalTheory.StabHaar.mat_one, blkMat_one, sub_self]; exact hU)`.

Establish `h2` using `hm'.continuousAt (x := 1) |>.preimage_mem_nhds (by rw [inv_one, GlobalTheory.StabHaar.mat_one, blkMat_one, sub_self]; exact hU)`. Use `filter_upwards [h1, h2] with g hg1 hg2 hg`. Establish `e : ∀ (M : Matrix (Fin (n + n)) (Fin (n + n)) (AE F E)) z, M *ᵥ z = (M - 1) *ᵥ z + z` using `fun M z => by`. Rewrite using `[Matrix.sub_mulVec, Matrix.one_mulVec, sub_add_cancel]`. Use `(hD.stab _).2 ⟨fun w => ?_, fun z hz => ⟨?_, ?_⟩⟩` and prove the remaining obligations.

Establish `h0 : (mat g).map (piInf (B.emb w)) = 1`. Establish `h3` using `hg (realAd F 1) (map_zero (evalV F v))`. Use extensionality with `a b`. Establish `h4` using `GlobalTheory.RealScalar.piInf_realAd_smul (B.emb w) 1 ((mat g - 1) a b)`. Establish `h5 : realAd F 1 • (mat g - 1) a b = 0` using `congrFun (congrFun h3 a) b`.

Rewrite `h4` using `[h5, map_zero, Matrix.sub_apply, map_sub, Complex.ofReal_one, one_mul, eq_comm, sub_eq_zero]`. Rewrite using `[Matrix.map_apply, h4, Matrix.one_apply, Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> simp`. Establish `h6 : (mat (i (g, 1))).map (piInf (B.emb w)) = 1`. Rewrite using `[hD.emb, GlobalTheory.StabHaar.mat_one, ← blkMat_one (A := ℂ) finSumFinEquiv, blkMat, blkMat, ← Matrix.submatrix_map, Matrix.fromBlocks_map, h0, Matrix.map_zero _ (map_zero _), Matrix.map_one _ (map_zero _) (map_one _)]`.

Rewrite using `[h6]`. Conclude with `Commute.one_left _`. Rewrite using `[hD.emb, GlobalTheory.StabHaar.mat_one, e]`. Conclude with `add_mem (hg1 z hz) hz`. Rewrite using `[← map_inv, Prod.inv_mk, inv_one, hD.emb, GlobalTheory.StabHaar.mat_one, e]`.

Conclude with `add_mem (hg2 z hz) hz`.
-/
theorem eventually_mem_stab {B : Base F E} {X : Spc F E n} (hL : X.L.IsLattice E) {X₂ : Spc F E (n + n)}
    {i : UA σ X.J × UA σ X.J →* UA σ X₂.J} {K₂ : Subgroup (UA σ X₂.J)} (hD : IsDbl B X X₂ i K₂) (v : Pl F) :
    ∀ᶠ g in 𝓝 (1 : UA σ X.J), g ∈ UAt σ X (evFin F v) → i (g, 1) ∈ K₂ := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsTopologicalRing (AE F E) := GlobalTheory.Doubling.isTopologicalRing_tens
  have hL₂ : X₂.L.IsLattice E := by
    rw [hD.lat]
    exact isLattice_sumLat _ _
  have hU := mulVec_mem_latHat_mem_nhds X₂ hL₂
  have hb : Continuous fun M : Matrix (Fin n) (Fin n) (AE F E) =>
      blkMat finSumFinEquiv M (1 : Matrix (Fin n) (Fin n) (AE F E)) - 1 :=
    ((continuous_id.matrix_fromBlocks continuous_const continuous_const continuous_const).matrix_submatrix _ _).sub
      continuous_const
  have hm : Continuous fun g : UA σ X.J => blkMat finSumFinEquiv (mat g) (1 : Matrix (Fin n) (Fin n) (AE F E)) - 1 :=
    hb.comp (Units.continuous_val.comp continuous_subtype_val)
  have hm' : Continuous fun g : UA σ X.J => blkMat finSumFinEquiv (mat g⁻¹) (1 : Matrix (Fin n) (Fin n) (AE F E)) - 1 :=
    hb.comp (Units.continuous_coe_inv.comp continuous_subtype_val)
  have h1 := hm.continuousAt (x := 1) |>.preimage_mem_nhds
    (by rw [GlobalTheory.StabHaar.mat_one, blkMat_one, sub_self]; exact hU)
  have h2 := hm'.continuousAt (x := 1) |>.preimage_mem_nhds
    (by rw [inv_one, GlobalTheory.StabHaar.mat_one, blkMat_one, sub_self]; exact hU)
  filter_upwards [h1, h2] with g hg1 hg2 hg
  have e : ∀ (M : Matrix (Fin (n + n)) (Fin (n + n)) (AE F E)) z, M *ᵥ z = (M - 1) *ᵥ z + z := fun M z => by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_add_cancel]
  refine (hD.stab _).2 ⟨fun w => ?_, fun z hz => ⟨?_, ?_⟩⟩
  · have h0 : (mat g).map (piInf (B.emb w)) = 1 := by
      have h3 := hg (realAd F 1) (map_zero (evalV F v))
      ext a b
      have h4 := GlobalTheory.RealScalar.piInf_realAd_smul (B.emb w) 1 ((mat g - 1) a b)
      have h5 : realAd F 1 • (mat g - 1) a b = 0 := congrFun (congrFun h3 a) b
      rw [h5, map_zero, Matrix.sub_apply, map_sub, Complex.ofReal_one, one_mul, eq_comm, sub_eq_zero] at h4
      rw [Matrix.map_apply, h4, Matrix.one_apply, Matrix.one_apply]
      split_ifs <;> simp
    have h6 : (mat (i (g, 1))).map (piInf (B.emb w)) = 1 := by
      rw [hD.emb, GlobalTheory.StabHaar.mat_one, ← blkMat_one (A := ℂ) finSumFinEquiv, blkMat, blkMat, ← Matrix.submatrix_map,
        Matrix.fromBlocks_map, h0, Matrix.map_zero _ (map_zero _), Matrix.map_one _ (map_zero _) (map_one _)]
    rw [h6]
    exact Commute.one_left _
  · rw [hD.emb, GlobalTheory.StabHaar.mat_one, e]
    exact add_mem (hg1 z hz) hz
  · rw [← map_inv, Prod.inv_mk, inv_one, hD.emb, GlobalTheory.StabHaar.mat_one, e]
    exact add_mem (hg2 z hz) hz

/- English proof (translation)
Establish `hcm : IsCMExt F E σ` using `hB.cm`. Establish `hstd` using `hB.std`. Establish `hss : (t.comp σ).comp σ = t` using `GlobalTheory.OppLagr.comp_comp hcm t`. Use `set A := X.J.map (t.comp σ) with hAdef`. Use `set Bm := (W.J.map (t.comp σ))ᵀ with hBdef`.

Establish `hA : IsUnit Aᵀ.det`. Rewrite using `[Matrix.det_transpose]`. Conclude with `isUnit_iff_ne_zero.2 (GlobalTheory.OppLagr.det_map_ne_zero (GlobalTheory.OppLagr.det_ne_zero_herm hX) _)`. Establish `hB' : IsUnit Bmᵀ.det`. Rewrite using `[hBdef, Matrix.transpose_transpose]`.

Conclude with `isUnit_iff_ne_zero.2 (GlobalTheory.OppLagr.det_map_ne_zero (GlobalTheory.OppLagr.det_ne_zero_skew hW) _)`. Use `choose U hUat hU0 hU1 using fun (P₀ P₁ : Matrix (Fin n) (Fin d) (Fv F v)) => GlobalTheory.T.exists_splitPlace_adelicMatrix_given_components hcm v t P₀ P₁`. Establish `hsymp : ∀ x u : Matrix (Fin n) (Fin d) (AE F E), At (evFin F v) x → x.map (piW (t.comp σ)) = 0 → u.map (piW t) = 0 → B.ψ (symp (R` using `AF F) (cA σ) (-1) (incM F X.J) (incM F W.J) x u) = GlobalTheory.LatVac.psiAt B.ψ v (∑ k, ∑ j, (A * x.map (piW t) * Bm) k j * u.map (piW (t.comp σ)) k j) := by`. Introduce `x u hx hx0 hu1`. Unfold `symp`.

Rewrite using `[GlobalTheory.T.adelicTrace_supportedAtSplitPlace hcm v (t.comp σ) _ (GlobalTheory.UnitWShape.at_hTens _ _ x u hx)]`. Rewrite using `[map_mul, map_mul, map_neg, map_neg, map_one, map_one, neg_one_mul, neg_one_mul, ← neg_add, GlobalTheory.T.hermitianTensor_skewHermitian_split_symplectic_pair hcm (t.comp σ) X.J W.J hX.herm hW.skew x u hx0 (by rw [hss]; exact hu1), hss]`. Use `show GlobalTheory.LatVac.psiAt B.ψ v _ = _`. Use `congr 1`. Simplify using `only [hAdef, hBdef, Matrix.neg_apply, neg_mul, Finset.sum_neg_distrib, neg_neg]`.

Set `Lm : Matrix (Fin n) (Fin d) (Fv F v)` to `Matrix.of fun k j => l (Matrix.single k j 1)`. Set `Pm : Matrix (Fin n) (Fin d) (Fv F v)` to `(Aᵀ)⁻¹ * Lm * (Bmᵀ)⁻¹`. Establish `hpair : ∀ Y, ∑ k, ∑ j, (A * Y * Bm) k j * Pm k j = l Y`. Introduce `Y`. Rewrite using `[GlobalTheory.UnitWShape.pair_mul, GlobalTheory.UnitWShape.linForm_eq l Y]`.

Establish `e : Aᵀ * Pm * Bmᵀ = Lm`. Simplify using `only [Pm]`. Rewrite using `[Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_right _ _ hB', Matrix.mul_nonsing_inv_cancel_left _ _ hA]`. Rewrite using `[e]`. Both sides reduce to the same expression.

Establish `hL` using `hι`. Unfold `GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model.IsLinW at hL`. Simplify using `only [inv_one, Units.val_one, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one] at hL`. Use `⟨U 0 Pm, fun φ hφ => ?_⟩` and prove the remaining obligations. Establish `hact` using `GlobalTheory.T.adelicHeisenberg_acts_by_local_schrodinger M.co B.ψ v _ (hUat 0 Pm) φ`.

Establish `hsb` using `GlobalTheory.SchrSB.schr_mem_SB B.ψ hstd.1 v (GlobalTheory.LatVac.locCo M.co v (U 0 Pm)) φ hφ`. Use `⟨_, hsb, hact, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `Y`. Establish `hm` using `hL.mult (U 0 Pm) (hUat _ _) (hU0 0 Pm) φ hφ _ hsb hact (U Y 0) (hUat Y 0) (hU1 Y 0)`. Rewrite `hm` using `[hU0]`.

Rewrite using `[hm, hsymp _ _ (hUat Y 0) (hU1 Y 0) (hU0 0 Pm), hU0, hU1, hpair]`.
-/
theorem exists_mult {B : Base F E} (hB : B.IsGood σ) {X : Spc F E n} {W : Spc F E d} {r s r' s' : ℕ} (hX : X.IsHerm σ B r s)
    (hW : W.IsSkew σ B r' s') (M : Model σ X W) (v : Pl F) (t : E →ₐ[F] Fv F v)
    (ι : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d) (Fv F v) → ℂ)) (hι : M.IsLinW B.ψ t 1 1 ι)
    (l : Matrix (Fin n) (Fin d) (Fv F v) →ₗ[Fv F v] Fv F v) :
    ∃ u : Matrix (Fin n) (Fin d) (AE F E), ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ∃ φ₁ ∈ SB (Fin n × Fin d → Fv F v),
      Acts (evFin F v) (M.co.rho B.ψ u) φ φ₁ ∧ ι φ₁ = fun Y => GlobalTheory.LatVac.psiAt B.ψ v (l Y) * ι φ Y := by
  have hcm : IsCMExt F E σ := hB.cm
  have hstd := hB.std
  have hss : (t.comp σ).comp σ = t := GlobalTheory.OppLagr.comp_comp hcm t
  set A := X.J.map (t.comp σ) with hAdef
  set Bm := (W.J.map (t.comp σ))ᵀ with hBdef
  have hA : IsUnit Aᵀ.det := by
    rw [Matrix.det_transpose]
    exact isUnit_iff_ne_zero.2 (GlobalTheory.OppLagr.det_map_ne_zero (GlobalTheory.OppLagr.det_ne_zero_herm hX) _)
  have hB' : IsUnit Bmᵀ.det := by
    rw [hBdef, Matrix.transpose_transpose]
    exact isUnit_iff_ne_zero.2 (GlobalTheory.OppLagr.det_map_ne_zero (GlobalTheory.OppLagr.det_ne_zero_skew hW) _)
  choose U hUat hU0 hU1 using fun (P₀ P₁ : Matrix (Fin n) (Fin d) (Fv F v)) => GlobalTheory.T.exists_splitPlace_adelicMatrix_given_components hcm v t P₀ P₁
  have hsymp : ∀ x u : Matrix (Fin n) (Fin d) (AE F E), At (evFin F v) x → x.map (piW (t.comp σ)) = 0 →
      u.map (piW t) = 0 →
      B.ψ (symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J) x u) =
        GlobalTheory.LatVac.psiAt B.ψ v (∑ k, ∑ j, (A * x.map (piW t) * Bm) k j * u.map (piW (t.comp σ)) k j) := by
    intro x u hx hx0 hu1
    unfold symp
    rw [GlobalTheory.T.adelicTrace_supportedAtSplitPlace hcm v (t.comp σ) _ (GlobalTheory.UnitWShape.at_hTens _ _ x u hx)]
    rw [map_mul, map_mul, map_neg, map_neg, map_one, map_one, neg_one_mul, neg_one_mul, ← neg_add,
      GlobalTheory.T.hermitianTensor_skewHermitian_split_symplectic_pair hcm (t.comp σ) X.J W.J hX.herm hW.skew x u hx0 (by rw [hss]; exact hu1), hss]
    show GlobalTheory.LatVac.psiAt B.ψ v _ = _
    congr 1
    simp only [hAdef, hBdef, Matrix.neg_apply, neg_mul, Finset.sum_neg_distrib, neg_neg]
  let Lm : Matrix (Fin n) (Fin d) (Fv F v) := Matrix.of fun k j => l (Matrix.single k j 1)
  let Pm : Matrix (Fin n) (Fin d) (Fv F v) := (Aᵀ)⁻¹ * Lm * (Bmᵀ)⁻¹
  have hpair : ∀ Y, ∑ k, ∑ j, (A * Y * Bm) k j * Pm k j = l Y := by
    intro Y
    rw [GlobalTheory.UnitWShape.pair_mul, GlobalTheory.UnitWShape.linForm_eq l Y]
    have e : Aᵀ * Pm * Bmᵀ = Lm := by
      simp only [Pm]
      rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_right _ _ hB', Matrix.mul_nonsing_inv_cancel_left _ _ hA]
    rw [e]
    rfl
  have hL := hι
  unfold GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model.IsLinW at hL
  simp only [inv_one, Units.val_one, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one] at hL
  refine ⟨U 0 Pm, fun φ hφ => ?_⟩
  have hact := GlobalTheory.T.adelicHeisenberg_acts_by_local_schrodinger M.co B.ψ v _ (hUat 0 Pm) φ
  have hsb := GlobalTheory.SchrSB.schr_mem_SB B.ψ hstd.1 v (GlobalTheory.LatVac.locCo M.co v (U 0 Pm)) φ hφ
  refine ⟨_, hsb, hact, ?_⟩
  funext Y
  have hm := hL.mult (U 0 Pm) (hUat _ _) (hU0 0 Pm) φ hφ _ hsb hact (U Y 0) (hUat Y 0) (hU1 Y 0)
  rw [hU0] at hm
  rw [hm, hsymp _ _ (hUat Y 0) (hU1 Y 0) (hU0 0 Pm), hU0, hU1, hpair]

/- English proof (translation)
Establish `h1 : ∀ s, ψ s * (starRingEnd ℂ) (ψ s) = 1` using `fun s => by`. Rewrite using `[Complex.mul_conj, Complex.normSq_eq_norm_sq, hψ s]`. Simplify using the standard rewrite rules. Establish `h2 : (fun y => schr ψ w Φ y * (starRingEnd ℂ) (schr ψ w Φ' y)) = fun y => Φ (y + w.1) * (starRingEnd ℂ) (Φ' (y + w.1))`. Use function extensionality and compare the values at `y`.

Simplify using `only [schr, map_mul]`. Use `h1 (y ⬝ᵥ w.2 + ⅟(2 : AF F) * (w.1 ⬝ᵥ w.2))` as an intermediate fact. Take the linear combination `(Φ (y + w.1) * (starRingEnd ℂ) (Φ' (y + w.1))) * this`. Establish `h3 : ∫ y, schr ψ w Φ y * (starRingEnd ℂ) (schr ψ w Φ' y) ∂m = ∫ x, Φ x * starRingEnd ℂ (Φ' x) ∂m`. Rewrite using `[h2]`.

Conclude with `integral_add_right_eq_self (fun y => Φ y * (starRingEnd ℂ) (Φ' y)) w.1`. Establish `h4 : ∫ y, schr ψ w Φ y * (starRingEnd ℂ) (schr ψ w Φ' y) ∂m = a * starRingEnd ℂ b * ∫ x, Φ x * starRingEnd ℂ (Φ' x) ∂m`. Rewrite using `[ha, hb, ← integral_const_mul]`. Use `congr 1`. Use function extensionality and compare the values at `y`.

Simplify using `only [Pi.smul_apply, smul_eq_mul, map_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `h5 : (a * starRingEnd ℂ b - 1) * ∫ x, Φ x * starRingEnd ℂ (Φ' x) ∂m = 0` using `by linear_combination h3 - h4`. Conclude with `(mul_eq_zero.1 h5).resolve_left (sub_ne_zero.2 hab)`.
-/
theorem integral_eq_zero_of_eigen {κ : Type} [Fintype κ] [MeasurableSpace (κ → AF F)] [BorelSpace (κ → AF F)]
    (m : Measure (κ → AF F)) [m.IsAddHaarMeasure] {ψ : AddChar (AF F) ℂ} (hψ : ∀ x, ‖ψ x‖ = 1)
    (w : (κ → AF F) × (κ → AF F)) {Φ Φ' : (κ → AF F) → ℂ} {a b : ℂ} (ha : schr ψ w Φ = a • Φ) (hb : schr ψ w Φ' = b • Φ')
    (hab : a * starRingEnd ℂ b ≠ 1) : ∫ x, Φ x * starRingEnd ℂ (Φ' x) ∂m = 0 := by
  have h1 : ∀ s, ψ s * (starRingEnd ℂ) (ψ s) = 1 := fun s => by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hψ s]; simp
  have h2 : (fun y => schr ψ w Φ y * (starRingEnd ℂ) (schr ψ w Φ' y)) =
      fun y => Φ (y + w.1) * (starRingEnd ℂ) (Φ' (y + w.1)) := by
    funext y
    simp only [schr, map_mul]
    have := h1 (y ⬝ᵥ w.2 + ⅟(2 : AF F) * (w.1 ⬝ᵥ w.2))
    linear_combination (Φ (y + w.1) * (starRingEnd ℂ) (Φ' (y + w.1))) * this
  have h3 : ∫ y, schr ψ w Φ y * (starRingEnd ℂ) (schr ψ w Φ' y) ∂m = ∫ x, Φ x * starRingEnd ℂ (Φ' x) ∂m := by
    rw [h2]
    exact integral_add_right_eq_self (fun y => Φ y * (starRingEnd ℂ) (Φ' y)) w.1
  have h4 : ∫ y, schr ψ w Φ y * (starRingEnd ℂ) (schr ψ w Φ' y) ∂m =
      a * starRingEnd ℂ b * ∫ x, Φ x * starRingEnd ℂ (Φ' x) ∂m := by
    rw [ha, hb, ← integral_const_mul]
    congr 1
    funext y
    simp only [Pi.smul_apply, smul_eq_mul, map_mul]
    ring
  have h5 : (a * starRingEnd ℂ b - 1) * ∫ x, Φ x * starRingEnd ℂ (Φ' x) ∂m = 0 := by linear_combination h3 - h4
  exact (mul_eq_zero.1 h5).resolve_left (sub_ne_zero.2 hab)

/- English proof (translation)
Establish `h2 : MemLp Φ 2 m`. Take `⟨rfl⟩` from `hB`. Conclude with `GlobalTheory.WeilM.schA_memLp_two F κ m hm Φ hΦ`. Establish `hc : Continuous Φ` using `(GlobalTheory.OffVLocalWeights.continuous_and_compact_finite_support Φ hΦ).1`. Establish `hi : Integrable (fun x => ‖Φ x‖ ^ 2) m` using `h2.integrable_norm_pow two_ne_zero`.

Establish `e : (fun y => Φ y * (starRingEnd ℂ) (Φ y)) = fun y => (((‖Φ y‖ ^ 2 : ℝ)) : ℂ)`. Use function extensionality and compare the values at `y`. Rewrite using `[Complex.mul_conj, Complex.normSq_eq_norm_sq]`. Rewrite using `[e, integral_complex_ofReal, Ne, Complex.ofReal_eq_zero, integral_eq_zero_iff_of_nonneg (fun y => by positivity) hi]`. Introduce `h`.

Establish `h'` using `(Continuous.ae_eq_iff_eq m (hc.norm.pow 2) continuous_zero).1 h`. Apply `h0` to reduce the goal to its premises. Use function extensionality and compare the values at `y`. Simplify using `using congrFun h' y`.
-/
theorem integral_ne_zero {κ : Type} [Fintype κ] [hM : MeasurableSpace (κ → AF F)] [hB : BorelSpace (κ → AF F)]
    (m : Measure (κ → AF F)) [hm : m.IsAddHaarMeasure] {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) (h0 : Φ ≠ 0) :
    ∫ x, Φ x * starRingEnd ℂ (Φ x) ∂m ≠ 0 := by
  have h2 : MemLp Φ 2 m := by
    obtain ⟨rfl⟩ := hB
    exact GlobalTheory.WeilM.schA_memLp_two F κ m hm Φ hΦ
  have hc : Continuous Φ := (GlobalTheory.OffVLocalWeights.continuous_and_compact_finite_support Φ hΦ).1
  have hi : Integrable (fun x => ‖Φ x‖ ^ 2) m := h2.integrable_norm_pow two_ne_zero
  have e : (fun y => Φ y * (starRingEnd ℂ) (Φ y)) = fun y => (((‖Φ y‖ ^ 2 : ℝ)) : ℂ) := by
    funext y
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [e, integral_complex_ofReal, Ne, Complex.ofReal_eq_zero,
    integral_eq_zero_iff_of_nonneg (fun y => by positivity) hi]
  intro h
  have h' := (Continuous.ae_eq_iff_eq m (hc.norm.pow 2) continuous_zero).1 h
  apply h0
  funext y
  simpa using congrFun h' y

end Global

/- English proof (translation)
Establish `hO` using `GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F v`. Establish `hc : IsCompact {Y | Y - Y₀ ∈ box m p t}` using `(Homeomorph.subRight Y₀).isCompact_preimage.2 (isCompact_box hO m p ht)`. Establish `ho : IsOpen {Y | Y - Y₀ ∈ box m p t}` using `(isOpen_box m p ht).preimage (continuous_id.sub continuous_const)`. Conclude with `⟨(LocallyConstant.charFn ℂ ⟨hc.isClosed, ho⟩).isLocallyConstant, HasCompactSupport.intro hc fun x hx => Set.indicator_of_notMem hx _⟩`.
-/
theorem indicator_mem_SB {F : Type} [Field F] [NumberField F] {v : Pl F} {m p : ℕ} (Y₀ : Matrix (Fin m) (Fin p) (Fv F v))
    {t : Fv F v} (ht : t ≠ 0) : Set.indicator {Y | Y - Y₀ ∈ box m p t} (1 : Matrix (Fin m) (Fin p) (Fv F v) → ℂ) ∈
      SB (Matrix (Fin m) (Fin p) (Fv F v)) := by
  have hO := GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F v
  have hc : IsCompact {Y | Y - Y₀ ∈ box m p t} :=
    (Homeomorph.subRight Y₀).isCompact_preimage.2 (isCompact_box hO m p ht)
  have ho : IsOpen {Y | Y - Y₀ ∈ box m p t} := (isOpen_box m p ht).preimage (continuous_id.sub continuous_const)
  exact ⟨(LocallyConstant.charFn ℂ ⟨hc.isClosed, ho⟩).isLocallyConstant,
    HasCompactSupport.intro hc fun x hx => Set.indicator_of_notMem hx _⟩

set_option maxHeartbeats 1600000 in

/- English proof (translation)
Introduce `hK F E _ _ _ _ _ σ B n d X W M χX χW om r s' r₁ s₁ hP _ _ _ hnd _ X₂ i K₂ hD _ _ m hm v hv`. Establish `hPr` using `hK.base`. Establish `hcm : IsCMExt F E σ` using `hP.base.cm`. Take `⟨τ⟩ : Nonempty (E →ₐ[F] Fv F v)` from `⟨B.τ ⟨v, hv⟩⟩`. Take `⟨ι, hι⟩` from `GlobalTheory.LinWSplit.exists_isLinW_at hPr F E σ B n d X W M χX χW om r s' r₁ s₁ hP v τ 1 1`.

Establish `hbij` using `Model.IsLin.bij hι`. Establish `hA` using `GlobalTheory.ThK.LocalOps.actsEx hPr F E σ B n d X W M χX χW om r s' r₁ s₁ hP v`. Establish `hO` using `GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F v`. Establish `h1W : (1 : UA σ W.J) ∈ UAt σ W (evFin F v)` using `(UAtSub σ W (evFin F v)).one_mem`. Use `set L : UA σ X.J →* GL (Fin n) (Fv F v) := GlobalTheory.KSplit.locMat τ 1 with hLdef`.

Choose the witnesses or unpack the hypotheses as in `⟨c, hc⟩ : ∃ c : UA σ X.J → ℂ, ∀ g ∈ UAt σ X (evFin F v), ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ∀ φ₁ ∈ SB (Fin n × Fin d → Fv F v), Acts (evFin F v) (om (g, 1)) φ φ₁ → ∀ Y, ι φ₁ Y = c g * ι φ ((L g)⁻¹.val * Y) := by`. Use `⟨fun g => GlobalTheory.SplitFlip.omA (chrW χW τ)⁻¹ (chrW χX τ) (L g) (1 : GL (Fin d) (Fv F v)) (fun _ => 1) 0, fun g hg φ hφ φ₁ hφ₁ hact Y => ?_⟩` and prove the remaining obligations. Rewrite using `[GlobalTheory.KSplit.om_linW_split hPr F E σ B n d X W M χX χW om r s' r₁ s₁ hP v τ 1 1 ι hι g hg 1 h1W φ hφ φ₁ hφ₁ hact, map_one]`. Establish `e : (GlobalTheory.SplitFlip.invT (1 : GL (Fin d) (Fv F v))).val = 1` using `by simp`. Simplify using `only [GlobalTheory.SplitFlip.omA, e, Matrix.mul_one, mul_one, hLdef]`.

Establish `hc1 : ∀ᶠ g in 𝓝 (1 : UA σ X.J), g ∈ UAt σ X (evFin F v) → c g = 1`. Take `⟨φ₀, hφ₀, e₀⟩` from `hbij.surjOn (indicator_mem_SB (0 : Matrix (Fin n) (Fin d) (Fv F v)) one_ne_zero)`. Take `⟨U, hU, hUa⟩` from `hA.2.2 φ₀ hφ₀`. Establish `ht : Tendsto (fun g : UA σ X.J => (g, (1 : UA σ W.J))) (𝓝 1) (𝓝 (1 : UA σ X.J × UA σ W.J))` using `(continuous_id.prodMk (continuous_const (y := (1 : UA σ W.J)))).tendsto (1 : UA σ X.J)`. Use `filter_upwards [ht hU] with g hg hgv`.

Establish `h0 : ι φ₀ 0 = 1`. Rewrite using `[e₀]`. Conclude with `Set.indicator_of_mem (show (0 : Matrix (Fin n) (Fin d) (Fv F v)) ∈ {Y | Y - 0 ∈ box n d (1 : Fv F v)} from fun i j => by simp) _`. Use `hc g hgv φ₀ hφ₀ φ₀ hφ₀ (hUa (g, 1) hg hgv h1W) 0` as an intermediate fact. Rewrite `this` using `[Matrix.mul_zero, h0, mul_one]`.

Conclude with `this.symm`. Establish `hK2` using `eventually_mem_stab hP.herm.lat hD v`. Establish `hermV : ∀ k l, σ (X.J l k) = algebraMap F E 1 * X.J k l` using `fun k l => by`. Rewrite using `[hP.herm.herm k l, map_one, one_mul]`. Establish `hJ : IsUnit (X.J.map τ).det` using `isUnit_iff_ne_zero.2 (GlobalTheory.OppLagr.det_map_ne_zero (GlobalTheory.OppLagr.det_ne_zero_herm hP.herm) τ)`.

Use `set Λ := GlobalTheory.SplitUnitLift.liftU hcm τ X.J 1 hermV hJ with hΛ`. Establish `hΛL : ∀ g ∈ UAt σ X (evFin F v), Λ (L g) = g` using `fun g hg => by`. Establish `e : L g = Matrix.GeneralLinearGroup.map (piW τ) g.1` using `by show (1 : GL (Fin n) (Fv F v))⁻¹ * _ * 1 = _`. Rewrite using `[inv_one, one_mul, mul_one]`. Rewrite using `[e]`.

Conclude with `(GlobalTheory.SchurCharV.eq_liftU_of_UAt hcm τ X hermV hJ g hg).symm`. Use `haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) (Fv F v)) := inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → Fv F v))`. Take `⟨C, hC, hC1⟩` from `exists_compact_mem_nhds (1 : GL (Fin n) (Fv F v))`. Establish `hint : ∀ᶠ h in 𝓝 (1 : GL (Fin n) (Fv F v)), (h⁻¹).val ∈ box n n (1 : Fv F v)`. Use `Units.continuous_coe_inv.continuousAt.preimage_mem_nhds ((isOpen_box n n one_ne_zero).mem_nhds fun i j => ?_)` and prove the remaining obligations.

Rewrite using `[inv_one, Units.val_one, map_one]`. Conclude with `val_one_le _ i j`. Establish `hN` using `((GlobalTheory.SplitUnitLiftCont.tendsto_liftU hcm τ X.J 1 hermV hJ).eventually (hc1.and hK2)).and (hint.and hC1)`. Rewrite `hN` using `[GlobalTheory.SplitFlip.isEmbedding_val_GL.nhds_eq_comap, Filter.eventually_comap]`. Establish `htd : Tendsto (fun Z : Matrix (Fin n) (Fin n) (Fv F v) => Z + 1) (𝓝 0) (𝓝 1)` using `(continuous_id.add continuous_const).tendsto' _ _ (zero_add _)`.

Establish `hN0` using `htd.eventually hN`. Take `⟨t, ht0, ht1, htN⟩` from `exists_box_subset hO hN0`. Establish `hS : ∀ g ∈ UAt σ X (evFin F v), (L g).val - 1 ∈ box n n t → c g = 1 ∧ i (g, 1) ∈ K₂ ∧ ((L g)⁻¹).val ∈ box n n (1 : Fv F v) ∧ L g ∈ C` using `fun g hg h => by`. Establish `h2` using `htN h (L g) (by simp)`. Rewrite `h2` using `[hΛL g hg]`.

Conclude with `⟨h2.1.1 hg, h2.1.2 hg, h2.2⟩`. Use `clear htd hN hN0 htN hint hK2 hc1`. Take `⟨φv, hφv, hιv⟩` from `hbij.surjOn (indicator_mem_SB (frame (Fv F v) hnd.le) ht0)`. Establish `hφv0 : φv ≠ 0` using `fun h => by`. Establish `h0` using `congrFun hιv (frame (Fv F v) hnd.le)`.

Rewrite `h0` using `[h, map_zero, Set.indicator_of_mem (show frame (Fv F v) hnd.le ∈ {Y | Y - frame (Fv F v) hnd.le ∈ box n d t} from fun i j => by simp)]`. Conclude with `zero_ne_one h0`. Use `⟨φv, hφv, hφv0, fun f _ φ hSB hev hne hφ μ hμ => ?_⟩` and prove the remaining obligations. Establish `hstd : ∀ᶠ w in Filter.cofinite, φ w = Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1` using `(hev.and hP.good.std).mono fun w hw => hw.1.trans hw.2`. Take `⟨ρ, hρ, hρt⟩` from `GlobalTheory.PureFactor.exists_rest_factor v f φ hstd`.

Establish `hpure : tens (evFin F v) φv ρ = pure f φ`. Rewrite using `[← hφ, hρt, Function.update_eq_self]`. Establish `hsch` using `GlobalTheory.TensUniq.pure_mem_schA f φ hSB hstd`. Establish `hRest : Rest (evFin F v) φv ρ` using `⟨hρ, by rw [hpure]; exact hsch⟩`. Establish `hnorm` using `integral_ne_zero m hsch hne`.

Establish `hcoef1 : Bot.coef m om (pure f φ) 1 = ∫ x, pure f φ x * starRingEnd ℂ (pure f φ x) ∂m`. Unfold `Bot.coef`. Rewrite using `[show ((1 : UA σ X.J), (1 : UA σ W.J)) = 1 from rfl, map_one, Module.End.one_apply]`. Establish `hψn` using `GlobalTheory.StdCharFromIsStd.norm_psi hP.base.std`. Establish `hin : ∀ g ∈ UAt σ X (evFin F v), (L g).val - 1 ∈ box n n t → Bot.coef m om (pure f φ) g = Bot.coef m om (pure f φ) 1` using `fun g hg h => by`.

Take `⟨h1, -, h3, -⟩` from `hS g hg h`. Take `⟨φ₁, ⟨hφ₁, hact⟩, -⟩` from `hA.1 g hg 1 h1W φv hφv`. Establish `hinv : ((L g)⁻¹).val - 1 ∈ box n n t` using `inv_cong Valued.v (Units.inv_mul (L g)) h fun i j => (h3 i j).trans_eq (map_one _)`. Establish `e : φ₁ = φv` using `hbij.injOn hφ₁ hφv (funext fun Y => by`. Rewrite using `[hc g hg φv hφv φ₁ hφ₁ hact, h1, one_mul, hιv]`.

Establish `hiff : ((L g)⁻¹).val * Y ∈ {Y | Y - frame (Fv F v) hnd.le ∈ box n d t} ↔ Y ∈ {Y | Y - frame (Fv F v) hnd.le ∈ box n d t}`. Use `⟨fun hY => ?_, fun hY => mul_mem_coset Valued.v hnd.le ht1 hinv hY⟩` and prove the remaining obligations. Use `mul_mem_coset Valued.v hnd.le ht1 h hY` as an intermediate fact. Rewrite `this` using `[← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]`. Then use the resulting hypothesis. Distinguish the cases in `hY : Y ∈ {Y | Y - frame (Fv F v) hnd.le ∈ box n d t}`.

Rewrite using `[Set.indicator_of_mem hY, Set.indicator_of_mem (hiff.2 hY)]`. Both sides reduce to the same expression. Rewrite using `[Set.indicator_of_notMem hY, Set.indicator_of_notMem (mt hiff.1 hY)])`. Rewrite using `[hcoef1]`. Unfold `Bot.coef`.

Rewrite using `[← hpure, hact ρ hRest, e]`. Establish `hout : ∀ g ∈ UAt σ X (evFin F v), (L g).val - 1 ∉ box n n t → Bot.coef m om (pure f φ) g = 0` using `fun g hg h => by`. Take `⟨l, hl, hl1⟩` from `exists_sep Valued.v (GlobalTheory.LatVac.psiAt B.ψ v) (fun x => by`. Simplify `hP.base.psiP v hv x) hnd.le ht0 ht1 (L g).val h` using `only [HeightOneSpectrum.mem_adicCompletionIntegers, GlobalTheory.LatVac.psiAt_apply]`. Take `⟨u, hu⟩` from `exists_mult hP.base hP.herm hP.skew M v τ ι hι l`.

Establish `eig : ∀ φ' ∈ SB (Fin n × Fin d → Fv F v), ∀ a : ℂ, (∀ Y, ι φ' Y ≠ 0 → GlobalTheory.LatVac.psiAt B.ψ v (l Y) = a) → schr B.ψ (M.co.e u) (tens (evFin F v) φ' ρ) = a • tens (evFin F v) φ' ρ` using `fun φ' hφ' a ha => by`. Take `⟨φ₂, hφ₂, hact, e⟩` from `hu φ' hφ'`. Establish `e2 : φ₂ = a • φ'` using `hbij.injOn hφ₂ (Submodule.smul_mem _ _ hφ') (funext fun Y => by`. Rewrite using `[e, map_smul, Pi.smul_apply, smul_eq_mul]`. Distinguish the cases in `hY : ι φ' Y = 0`.

Simplify using `[hY]`. Simplify using `only [ha Y hY])`. Establish `e3` using `hact ρ (GlobalTheory.RestCofactor.rest_of_rest v φv φ' ρ hφv0 hφ' hRest)`. Use `e3.trans ?_` and prove the remaining obligations. Rewrite using `[e2]`.

Use function extensionality and compare the values at `x`. Simplify using `[tens, mul_assoc]`. Take `⟨φ₁, ⟨hφ₁, hact⟩, -⟩` from `hA.1 g hg 1 h1W φv hφv`. Establish `hsupp : ∀ Y, ι φv Y ≠ 0 → Y - frame (Fv F v) hnd.le ∈ box n d t` using `fun Y hY => by`. Rewrite `hY` using `[hιv]`.

Establish `h2` using `Set.mem_of_indicator_ne_zero hY`. Conclude with `h2`. Establish `e1` using `eig φ₁ hφ₁ (GlobalTheory.LatVac.psiAt B.ψ v (l ((L g).val * frame (Fv F v) hnd.le))) fun Y hY => by`. Rewrite `hY` using `[hc g hg φv hφv φ₁ hφ₁ hact]`. Establish `h2` using `(hl _ (hsupp _ (right_ne_zero_of_mul hY))).2`.

Rewrite `h2` using `[Matrix.mul_sub, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]`. Rewrite using `[← sub_add_cancel Y ((L g).val * frame (Fv F v) hnd.le), map_add, AddChar.map_add_eq_mul, h2, one_mul]`. Establish `e2` using `eig φv hφv (GlobalTheory.LatVac.psiAt B.ψ v (l (frame (Fv F v) hnd.le))) fun Y hY => by`. Establish `h2` using `(hl _ (hsupp _ hY)).1`. Rewrite using `[← sub_add_cancel Y (frame (Fv F v) hnd.le), map_add, AddChar.map_add_eq_mul, h2, one_mul]`.

Unfold `Bot.coef`. Rewrite using `[← hpure, hact ρ hRest]`. Use `integral_eq_zero_of_eigen m hψn _ e1 e2 ?_` and prove the remaining obligations. Establish `e3 : (L g).val * frame (Fv F v) hnd.le = ((L g).val - 1) * frame (Fv F v) hnd.le + frame (Fv F v) hnd.le`. Rewrite using `[Matrix.sub_mul, Matrix.one_mul, sub_add_cancel]`.

Establish `e4 : ‖GlobalTheory.LatVac.psiAt B.ψ v (l (frame (Fv F v) hnd.le))‖ = 1` using `hψn _`. Rewrite using `[e3, map_add, AddChar.map_add_eq_mul, mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq, e4]`. Simplify using `using hl1`. Use `haveI : BorelSpace (UA σ X.J) := ⟨rfl⟩`. Use `haveI : BorelSpace (UAtSub σ X (evFin F v)) := Subtype.borelSpace _`.

Set `S : Set (UAtSub σ X (evFin F v))` to `{g | (L g.1).val - 1 ∈ box n n t}`. Establish `hSo : IsOpen S` using `(isOpen_box n n ht0).preimage ((Units.continuous_val.comp ((continuous_locMat τ 1).comp continuous_subtype_val)).sub continuous_const)`. Establish `hS1 : (1 : UAtSub σ X (evFin F v)) ∈ S` using `fun i j => by simp`. Establish `hpos : μ S ≠ 0` using `hSo.measure_ne_zero μ ⟨1, hS1⟩`. Establish `hfin : μ S ≠ ⊤`.

Set `Λ' : GL (Fin n) (Fv F v) → UAtSub σ X (evFin F v)` to `fun h => ⟨Λ h, GlobalTheory.SplitUnitLift.liftU_mem_UAt hcm τ X 1 hermV hJ h⟩`. Establish `hcont : Continuous Λ'` using `(GlobalTheory.SplitUnitLiftCont.continuous_liftU hcm τ X.J 1 hermV hJ).subtype_mk _`. Use `((measure_mono fun g hg => ?_).trans_lt (hC.image hcont).measure_lt_top).ne` and prove the remaining obligations. Conclude with `⟨L g.1, (hS g.1 g.2 hg).2.2.2, Subtype.ext (hΛL g.1 g.2)⟩`. Use `⟨(μ.real S : ℝ), Complex.ofReal_ne_zero.2 (ENNReal.toReal_ne_zero.2 ⟨hpos, hfin⟩), fun s => ?_⟩` and prove the remaining obligations.

Unfold `zetaOn`. Rewrite using `[← integral_indicator_one hSo.measurableSet, ← integral_complex_ofReal]`. Use `congr 1`. Use function extensionality and compare the values at `g`. Distinguish the cases in `hg : g ∈ S`.

Establish `h1` using `hD.iwa.hgtOf_mul 1 (hS g.1 g.2 hg).2.1`. Rewrite `h1` using `[OneMemClass.coe_one, one_mul, map_one, map_one]`. Rewrite using `[Set.indicator_of_mem hg, hin g.1 g.2 hg, h1, div_self (by rw [hcoef1]; exact hnorm)]`. Simplify using the standard rewrite rules. Rewrite using `[Set.indicator_of_notMem hg, hout g.1 g.2 hg]`.

Simplify using the standard rewrite rules.
-/
theorem exists_zetaOn_const : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s' r₁ s₁ : ℕ),
    IsPair B M χX χW om r s' r₁ s₁ → min r s' = 0 → min r₁ s₁ = 0 → 1 ≤ n → n < d → Even d →
    ∀ (X₂ : Spc F E (n + n)) (i : UA σ X.J × UA σ X.J →* UA σ X₂.J) (K₂ : Subgroup (UA σ X₂.J)), IsDbl B X X₂ i K₂ →
    ∀ [MeasurableSpace (Fin n × Fin d → AF F)] [BorelSpace (Fin n × Fin d → AF F)] (m : Measure (Fin n × Fin d → AF F)), m.IsAddHaarMeasure →
    ∀ v ∈ B.P, ∃ φv ∈ SB (Fin n × Fin d → Fv F v), φv ≠ 0 ∧ ∀ f ∈ M.Pol B.ψ B.emb, ∀ φ : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = M.vac v) → pure f φ ≠ 0 → φ v = φv →
      ∀ μ : Measure (UAtSub σ X (evFin F v)), μ.IsHaarMeasure → ∃ z : ℂ, z ≠ 0 ∧ ∀ s : ℂ, zetaOn m om (pure f φ) i K₂ _ μ s = z := by
  intro hK F E _ _ _ _ _ σ B n d X W M χX χW om r s' r₁ s₁ hP _ _ _ hnd _ X₂ i K₂ hD _ _ m hm v hv
  classical
  have hPr := hK.base
  have hcm : IsCMExt F E σ := hP.base.cm
  obtain ⟨τ⟩ : Nonempty (E →ₐ[F] Fv F v) := ⟨B.τ ⟨v, hv⟩⟩
  obtain ⟨ι, hι⟩ := GlobalTheory.LinWSplit.exists_isLinW_at hPr F E σ B n d X W M χX χW om r s' r₁ s₁ hP v τ 1 1
  have hbij := Model.IsLin.bij hι
  have hA := GlobalTheory.ThK.LocalOps.actsEx hPr F E σ B n d X W M χX χW om r s' r₁ s₁ hP v
  have hO := GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F v
  have h1W : (1 : UA σ W.J) ∈ UAt σ W (evFin F v) := (UAtSub σ W (evFin F v)).one_mem
  set L : UA σ X.J →* GL (Fin n) (Fv F v) := GlobalTheory.KSplit.locMat τ 1 with hLdef
  obtain ⟨c, hc⟩ : ∃ c : UA σ X.J → ℂ, ∀ g ∈ UAt σ X (evFin F v), ∀ φ ∈ SB (Fin n × Fin d → Fv F v),
      ∀ φ₁ ∈ SB (Fin n × Fin d → Fv F v), Acts (evFin F v) (om (g, 1)) φ φ₁ →
        ∀ Y, ι φ₁ Y = c g * ι φ ((L g)⁻¹.val * Y) := by
    refine ⟨fun g => GlobalTheory.SplitFlip.omA (chrW χW τ)⁻¹ (chrW χX τ) (L g) (1 : GL (Fin d) (Fv F v)) (fun _ => 1) 0,
      fun g hg φ hφ φ₁ hφ₁ hact Y => ?_⟩
    rw [GlobalTheory.KSplit.om_linW_split hPr F E σ B n d X W M χX χW om r s' r₁ s₁ hP v τ 1 1 ι hι g hg 1 h1W φ hφ φ₁ hφ₁ hact,
      map_one]
    have e : (GlobalTheory.SplitFlip.invT (1 : GL (Fin d) (Fv F v))).val = 1 := by simp
    simp only [GlobalTheory.SplitFlip.omA, e, Matrix.mul_one, mul_one, hLdef]

  have hc1 : ∀ᶠ g in 𝓝 (1 : UA σ X.J), g ∈ UAt σ X (evFin F v) → c g = 1 := by
    obtain ⟨φ₀, hφ₀, e₀⟩ := hbij.surjOn (indicator_mem_SB (0 : Matrix (Fin n) (Fin d) (Fv F v)) one_ne_zero)
    obtain ⟨U, hU, hUa⟩ := hA.2.2 φ₀ hφ₀
    have ht : Tendsto (fun g : UA σ X.J => (g, (1 : UA σ W.J))) (𝓝 1) (𝓝 (1 : UA σ X.J × UA σ W.J)) :=
      (continuous_id.prodMk (continuous_const (y := (1 : UA σ W.J)))).tendsto (1 : UA σ X.J)
    filter_upwards [ht hU] with g hg hgv
    have h0 : ι φ₀ 0 = 1 := by
      rw [e₀]
      exact Set.indicator_of_mem (show (0 : Matrix (Fin n) (Fin d) (Fv F v)) ∈ {Y | Y - 0 ∈ box n d (1 : Fv F v)} from
        fun i j => by simp) _
    have := hc g hgv φ₀ hφ₀ φ₀ hφ₀ (hUa (g, 1) hg hgv h1W) 0
    rw [Matrix.mul_zero, h0, mul_one] at this
    exact this.symm
  have hK2 := eventually_mem_stab hP.herm.lat hD v
  have hermV : ∀ k l, σ (X.J l k) = algebraMap F E 1 * X.J k l := fun k l => by
    rw [hP.herm.herm k l, map_one, one_mul]
  have hJ : IsUnit (X.J.map τ).det :=
    isUnit_iff_ne_zero.2 (GlobalTheory.OppLagr.det_map_ne_zero (GlobalTheory.OppLagr.det_ne_zero_herm hP.herm) τ)
  set Λ := GlobalTheory.SplitUnitLift.liftU hcm τ X.J 1 hermV hJ with hΛ
  have hΛL : ∀ g ∈ UAt σ X (evFin F v), Λ (L g) = g := fun g hg => by
    have e : L g = Matrix.GeneralLinearGroup.map (piW τ) g.1 := by
      show (1 : GL (Fin n) (Fv F v))⁻¹ * _ * 1 = _
      rw [inv_one, one_mul, mul_one]
    rw [e]
    exact (GlobalTheory.SchurCharV.eq_liftU_of_UAt hcm τ X hermV hJ g hg).symm
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) (Fv F v)) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → Fv F v))
  obtain ⟨C, hC, hC1⟩ := exists_compact_mem_nhds (1 : GL (Fin n) (Fv F v))
  have hint : ∀ᶠ h in 𝓝 (1 : GL (Fin n) (Fv F v)), (h⁻¹).val ∈ box n n (1 : Fv F v) := by
    refine Units.continuous_coe_inv.continuousAt.preimage_mem_nhds ((isOpen_box n n one_ne_zero).mem_nhds fun i j => ?_)
    rw [inv_one, Units.val_one, map_one]
    exact val_one_le _ i j
  have hN := ((GlobalTheory.SplitUnitLiftCont.tendsto_liftU hcm τ X.J 1 hermV hJ).eventually (hc1.and hK2)).and (hint.and hC1)
  rw [GlobalTheory.SplitFlip.isEmbedding_val_GL.nhds_eq_comap, Filter.eventually_comap] at hN
  have htd : Tendsto (fun Z : Matrix (Fin n) (Fin n) (Fv F v) => Z + 1) (𝓝 0) (𝓝 1) :=
    (continuous_id.add continuous_const).tendsto' _ _ (zero_add _)
  have hN0 := htd.eventually hN
  obtain ⟨t, ht0, ht1, htN⟩ := exists_box_subset hO hN0
  have hS : ∀ g ∈ UAt σ X (evFin F v), (L g).val - 1 ∈ box n n t →
      c g = 1 ∧ i (g, 1) ∈ K₂ ∧ ((L g)⁻¹).val ∈ box n n (1 : Fv F v) ∧ L g ∈ C := fun g hg h => by
    have h2 := htN h (L g) (by simp)
    rw [hΛL g hg] at h2
    exact ⟨h2.1.1 hg, h2.1.2 hg, h2.2⟩
  clear htd hN hN0 htN hint hK2 hc1
  obtain ⟨φv, hφv, hιv⟩ := hbij.surjOn (indicator_mem_SB (frame (Fv F v) hnd.le) ht0)
  have hφv0 : φv ≠ 0 := fun h => by
    have h0 := congrFun hιv (frame (Fv F v) hnd.le)
    rw [h, map_zero, Set.indicator_of_mem (show frame (Fv F v) hnd.le ∈ {Y | Y - frame (Fv F v) hnd.le ∈ box n d t} from
      fun i j => by simp)] at h0
    exact zero_ne_one h0
  refine ⟨φv, hφv, hφv0, fun f _ φ hSB hev hne hφ μ hμ => ?_⟩
  have hstd : ∀ᶠ w in Filter.cofinite, φ w = Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1 :=
    (hev.and hP.good.std).mono fun w hw => hw.1.trans hw.2
  obtain ⟨ρ, hρ, hρt⟩ := GlobalTheory.PureFactor.exists_rest_factor v f φ hstd
  have hpure : tens (evFin F v) φv ρ = pure f φ := by
    rw [← hφ, hρt, Function.update_eq_self]
  have hsch := GlobalTheory.TensUniq.pure_mem_schA f φ hSB hstd
  have hRest : Rest (evFin F v) φv ρ := ⟨hρ, by rw [hpure]; exact hsch⟩
  have hnorm := integral_ne_zero m hsch hne
  have hcoef1 : Bot.coef m om (pure f φ) 1 = ∫ x, pure f φ x * starRingEnd ℂ (pure f φ x) ∂m := by
    unfold Bot.coef
    rw [show ((1 : UA σ X.J), (1 : UA σ W.J)) = 1 from rfl, map_one, Module.End.one_apply]
  have hψn := GlobalTheory.StdCharFromIsStd.norm_psi hP.base.std

  have hin : ∀ g ∈ UAt σ X (evFin F v), (L g).val - 1 ∈ box n n t →
      Bot.coef m om (pure f φ) g = Bot.coef m om (pure f φ) 1 := fun g hg h => by
    obtain ⟨h1, -, h3, -⟩ := hS g hg h
    obtain ⟨φ₁, ⟨hφ₁, hact⟩, -⟩ := hA.1 g hg 1 h1W φv hφv
    have hinv : ((L g)⁻¹).val - 1 ∈ box n n t :=
      inv_cong Valued.v (Units.inv_mul (L g)) h fun i j => (h3 i j).trans_eq (map_one _)
    have e : φ₁ = φv := hbij.injOn hφ₁ hφv (funext fun Y => by
      rw [hc g hg φv hφv φ₁ hφ₁ hact, h1, one_mul, hιv]
      have hiff : ((L g)⁻¹).val * Y ∈ {Y | Y - frame (Fv F v) hnd.le ∈ box n d t} ↔
          Y ∈ {Y | Y - frame (Fv F v) hnd.le ∈ box n d t} := by
        refine ⟨fun hY => ?_, fun hY => mul_mem_coset Valued.v hnd.le ht1 hinv hY⟩
        have := mul_mem_coset Valued.v hnd.le ht1 h hY
        rwa [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul] at this
      by_cases hY : Y ∈ {Y | Y - frame (Fv F v) hnd.le ∈ box n d t}
      · rw [Set.indicator_of_mem hY, Set.indicator_of_mem (hiff.2 hY)]; rfl
      · rw [Set.indicator_of_notMem hY, Set.indicator_of_notMem (mt hiff.1 hY)])
    rw [hcoef1]
    unfold Bot.coef
    rw [← hpure, hact ρ hRest, e]

  have hout : ∀ g ∈ UAt σ X (evFin F v), (L g).val - 1 ∉ box n n t → Bot.coef m om (pure f φ) g = 0 := fun g hg h => by
    obtain ⟨l, hl, hl1⟩ := exists_sep Valued.v (GlobalTheory.LatVac.psiAt B.ψ v) (fun x => by
      simpa only [HeightOneSpectrum.mem_adicCompletionIntegers, GlobalTheory.LatVac.psiAt_apply] using hP.base.psiP v hv x) hnd.le ht0 ht1 (L g).val h
    obtain ⟨u, hu⟩ := exists_mult hP.base hP.herm hP.skew M v τ ι hι l
    have eig : ∀ φ' ∈ SB (Fin n × Fin d → Fv F v), ∀ a : ℂ, (∀ Y, ι φ' Y ≠ 0 → GlobalTheory.LatVac.psiAt B.ψ v (l Y) = a) →
        schr B.ψ (M.co.e u) (tens (evFin F v) φ' ρ) = a • tens (evFin F v) φ' ρ := fun φ' hφ' a ha => by
      obtain ⟨φ₂, hφ₂, hact, e⟩ := hu φ' hφ'
      have e2 : φ₂ = a • φ' := hbij.injOn hφ₂ (Submodule.smul_mem _ _ hφ') (funext fun Y => by
        rw [e, map_smul, Pi.smul_apply, smul_eq_mul]
        by_cases hY : ι φ' Y = 0
        · simp [hY]
        · simp only [ha Y hY])
      have e3 := hact ρ (GlobalTheory.RestCofactor.rest_of_rest v φv φ' ρ hφv0 hφ' hRest)
      refine e3.trans ?_
      rw [e2]
      funext x
      simp [tens, mul_assoc]
    obtain ⟨φ₁, ⟨hφ₁, hact⟩, -⟩ := hA.1 g hg 1 h1W φv hφv
    have hsupp : ∀ Y, ι φv Y ≠ 0 → Y - frame (Fv F v) hnd.le ∈ box n d t := fun Y hY => by
      rw [hιv] at hY
      have h2 := Set.mem_of_indicator_ne_zero hY
      exact h2
    have e1 := eig φ₁ hφ₁ (GlobalTheory.LatVac.psiAt B.ψ v (l ((L g).val * frame (Fv F v) hnd.le))) fun Y hY => by
      rw [hc g hg φv hφv φ₁ hφ₁ hact] at hY
      have h2 := (hl _ (hsupp _ (right_ne_zero_of_mul hY))).2
      rw [Matrix.mul_sub, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul] at h2
      rw [← sub_add_cancel Y ((L g).val * frame (Fv F v) hnd.le), map_add, AddChar.map_add_eq_mul, h2, one_mul]
    have e2 := eig φv hφv (GlobalTheory.LatVac.psiAt B.ψ v (l (frame (Fv F v) hnd.le))) fun Y hY => by
      have h2 := (hl _ (hsupp _ hY)).1
      rw [← sub_add_cancel Y (frame (Fv F v) hnd.le), map_add, AddChar.map_add_eq_mul, h2, one_mul]
    unfold Bot.coef
    rw [← hpure, hact ρ hRest]
    refine integral_eq_zero_of_eigen m hψn _ e1 e2 ?_
    have e3 : (L g).val * frame (Fv F v) hnd.le = ((L g).val - 1) * frame (Fv F v) hnd.le + frame (Fv F v) hnd.le := by
      rw [Matrix.sub_mul, Matrix.one_mul, sub_add_cancel]
    have e4 : ‖GlobalTheory.LatVac.psiAt B.ψ v (l (frame (Fv F v) hnd.le))‖ = 1 := hψn _
    rw [e3, map_add, AddChar.map_add_eq_mul, mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq, e4]
    simpa using hl1
  haveI : BorelSpace (UA σ X.J) := ⟨rfl⟩
  haveI : BorelSpace (UAtSub σ X (evFin F v)) := Subtype.borelSpace _
  let S : Set (UAtSub σ X (evFin F v)) := {g | (L g.1).val - 1 ∈ box n n t}
  have hSo : IsOpen S := (isOpen_box n n ht0).preimage
    ((Units.continuous_val.comp ((continuous_locMat τ 1).comp continuous_subtype_val)).sub continuous_const)
  have hS1 : (1 : UAtSub σ X (evFin F v)) ∈ S := fun i j => by simp
  have hpos : μ S ≠ 0 := hSo.measure_ne_zero μ ⟨1, hS1⟩
  have hfin : μ S ≠ ⊤ := by
    let Λ' : GL (Fin n) (Fv F v) → UAtSub σ X (evFin F v) := fun h =>
      ⟨Λ h, GlobalTheory.SplitUnitLift.liftU_mem_UAt hcm τ X 1 hermV hJ h⟩
    have hcont : Continuous Λ' := (GlobalTheory.SplitUnitLiftCont.continuous_liftU hcm τ X.J 1 hermV hJ).subtype_mk _
    refine ((measure_mono fun g hg => ?_).trans_lt (hC.image hcont).measure_lt_top).ne
    exact ⟨L g.1, (hS g.1 g.2 hg).2.2.2, Subtype.ext (hΛL g.1 g.2)⟩
  refine ⟨(μ.real S : ℝ), Complex.ofReal_ne_zero.2 (ENNReal.toReal_ne_zero.2 ⟨hpos, hfin⟩), fun s => ?_⟩
  unfold zetaOn
  rw [← integral_indicator_one hSo.measurableSet, ← integral_complex_ofReal]
  congr 1
  funext g
  by_cases hg : g ∈ S
  · have h1 := hD.iwa.hgtOf_mul 1 (hS g.1 g.2 hg).2.1
    rw [OneMemClass.coe_one, one_mul, map_one, map_one] at h1
    rw [Set.indicator_of_mem hg, hin g.1 g.2 hg, h1, div_self (by rw [hcoef1]; exact hnorm)]
    simp
  · rw [Set.indicator_of_notMem hg, hout g.1 g.2 hg]
    simp

end GlobalTheory.ThK.BotRam

end
