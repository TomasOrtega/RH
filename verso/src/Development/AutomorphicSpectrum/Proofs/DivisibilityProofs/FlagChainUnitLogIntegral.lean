import Mathlib
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.IsChainFirst
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PGrassFibreDegree
import GroundTheory.HeightsAndTheta.Heights.Intersections.PConsequences
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PHFlProdLinear
set_option maxSynthPendingDepth 1

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Top.FlDeg.Base

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4
open GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

section Proj

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

def blockEquiv (k₀ : K) (hk : ∀ a : K, a = k₀) : Unit ≃ K :=
  Equiv.ofBijective (fun _ => k₀) ⟨fun _ _ _ => rfl, fun a => ⟨(), (hk a).symm⟩⟩

def coordEquiv (k₀ : K) (hk : ∀ a : K, a = k₀) {n : ℕ} (σ : ι k₀ ≃ Fin (n + 1)) :
    (Σ _ : Unit, Fin (n + 1)) ≃ (Σ k, ι k) :=
  Equiv.ofBijective (fun p => ⟨k₀, σ.symm p.2⟩) (by
    constructor
    · rintro ⟨⟨⟩, a⟩ ⟨⟨⟩, b⟩ h
      have h2 : σ.symm a = σ.symm b := by simpa using h
      rw [σ.symm.injective h2]
    · rintro ⟨k, i⟩
      obtain rfl := hk k
      exact ⟨⟨(), σ i⟩, by simp⟩)

variable (ι) in
/- English proof (translation)
Rewrite using `[← Nat.card_congr (coordEquiv k₀ hk σ)]`. Simplify using the standard rewrite rules.
-/
theorem card_coords (k₀ : K) (hk : ∀ a : K, a = k₀) {n : ℕ} (σ : ι k₀ ≃ Fin (n + 1)) :
    Nat.card (Σ k, ι k) = n + 1 := by
  rw [← Nat.card_congr (coordEquiv k₀ hk σ)]
  simp

/- English proof (translation)
The claim follows from `Fintype.card_eq_one_iff.2 ⟨k₀, hk⟩`.
-/
theorem card_blocks (k₀ : K) (hk : ∀ a : K, a = k₀) : Fintype.card K = 1 :=
  Fintype.card_eq_one_iff.2 ⟨k₀, hk⟩

variable (p : ℕ) [Fact p.Prime]

/- English proof (translation)
The claim follows from `(Bridge.GeoNum.ker_red p).symm`.
-/
theorem span_eq_ker : (Ideal.span {C (p : ℤ)} : Ideal (MRing ι)) = RingHom.ker (Bridge.GeoNum.red (ι := ι) p) :=
  (Bridge.GeoNum.ker_red p).symm

/- English proof (translation)
Rewrite using `[span_eq_ker]`. Conclude with `RingHom.ker_isPrime _`.
-/
theorem isPrime_span : (Ideal.span {C (p : ℤ)} : Ideal (MRing ι)).IsPrime := by
  rw [span_eq_ker]
  exact RingHom.ker_isPrime _

/- English proof (translation)
Introduce `k`. Take `rfl` from `hk k`. Use `⟨σ.symm 0, ?_⟩` and prove the remaining obligations. Rewrite using `[span_eq_ker, RingHom.mem_ker, Bridge.GeoNum.red, map_X]`. Conclude with `X_ne_zero _`.
-/
theorem isRelevant_span (k₀ : K) (hk : ∀ a : K, a = k₀) {n : ℕ} (σ : ι k₀ ≃ Fin (n + 1)) :
    IsRelevant (Ideal.span {C (p : ℤ)} : Ideal (MRing ι)) := by
  intro k
  obtain rfl := hk k
  refine ⟨σ.symm 0, ?_⟩
  rw [span_eq_ker, RingHom.mem_ker, Bridge.GeoNum.red, map_X]
  exact X_ne_zero _

/- English proof (translation)
Use `isPrime_span (ι := ι) p` as an intermediate fact. Use extensionality with `W`. Simplify using `only [divSupp, bot_sup_eq, Ideal.minimalPrimes_eq_subsingleton_self, Set.mem_ofPred_eq, Set.mem_singleton_iff]`. Prove the components needed by the constructor for the conclusion. Conclude with `fun h => h.1`.

Introduce and unpack `rfl`. Conclude with `⟨rfl, isRelevant_span p k₀ hk σ⟩`.
-/
theorem divSupp_bot (k₀ : K) (hk : ∀ a : K, a = k₀) {n : ℕ} (σ : ι k₀ ≃ Fin (n + 1)) :
    divSupp (⊥ : Ideal (MRing ι)) (C (p : ℤ)) = {Ideal.span {C (p : ℤ)}} := by
  have := isPrime_span (ι := ι) p
  ext W
  simp only [divSupp, bot_sup_eq, Ideal.minimalPrimes_eq_subsingleton_self, Set.mem_ofPred_eq,
    Set.mem_singleton_iff]
  constructor
  · exact fun h => h.1
  · rintro rfl
    exact ⟨rfl, isRelevant_span p k₀ hk σ⟩

/- English proof (translation)
Rewrite using `[span_eq_ker, ringKrullDim_eq_of_ringEquiv (RingHom.quotientKerEquivOfSurjective (Bridge.GeoNum.red_surjective p)), MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field, zero_add, card_coords ι k₀ hk σ, card_blocks k₀ hk]`.
-/
theorem ringKrullDim_span (k₀ : K) (hk : ∀ a : K, a = k₀) {n : ℕ} (σ : ι k₀ ≃ Fin (n + 1)) :
    ringKrullDim (MRing ι ⧸ (Ideal.span {C (p : ℤ)} : Ideal (MRing ι))) =
      ((n + Fintype.card K : ℕ) : WithBot ℕ∞) := by
  rw [span_eq_ker, ringKrullDim_eq_of_ringEquiv
      (RingHom.quotientKerEquivOfSurjective (Bridge.GeoNum.red_surjective p)),
    MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field, zero_add,
    card_coords ι k₀ hk σ, card_blocks k₀ hk]

/- English proof (translation)
Establish `h` using `FieldNumbers.Relabel.intNum_map_rename (F := ZMod p) (blockEquiv k₀ hk) (coordEquiv k₀ hk σ) (fun _ => rfl) (⊥ : Ideal (NumbersDVR.MRing (FieldNumbers.ProjIdx n) (ZMod p))) (fun _ : Fin n => a)`. Rewrite `h` using `[Ideal.map_bot]`. Rewrite using `[h]`. Establish `hb : (fun _ : Fin n => a ∘ blockEquiv k₀ hk) = fun _ : Fin n => (1 : Unit → ℤ)`. Use function extensionality and compare the values at `_ u`.

Conclude with `ha`. Rewrite using `[hb]`. Conclude with `FieldNumbers.intNum_projectiveSpace (ZMod p) n`.
-/
theorem intNum_bot (k₀ : K) (hk : ∀ a : K, a = k₀) {n : ℕ} (σ : ι k₀ ≃ Fin (n + 1)) (a : K → ℤ) (ha : a k₀ = 1) :
    NumbersDVR.intNum (ZMod p) (⊥ : Ideal (NumbersDVR.MRing ι (ZMod p))) (fun _ : Fin n => a) = 1 := by
  have h := FieldNumbers.Relabel.intNum_map_rename (F := ZMod p) (blockEquiv k₀ hk)
    (coordEquiv k₀ hk σ) (fun _ => rfl)
    (⊥ : Ideal (NumbersDVR.MRing (FieldNumbers.ProjIdx n) (ZMod p))) (fun _ : Fin n => a)
  rw [Ideal.map_bot] at h
  rw [h]
  have hb : (fun _ : Fin n => a ∘ blockEquiv k₀ hk) = fun _ : Fin n => (1 : Unit → ℤ) := by
    funext _ u
    exact ha
  rw [hb]
  exact FieldNumbers.intNum_projectiveSpace (ZMod p) n

/- English proof (translation)
Establish `hV : IsMultiProjPrime (Ideal.span {C (p : ℤ)} : Ideal (MRing ι))` using `⟨isPrime_span p, ⟨{C (p : ℤ)}, fun f hf => ⟨0, by`. Rewrite using `[Set.mem_singleton_iff.mp hf]`. Conclude with `Inter.Conservation.isMultiHomog_C _⟩, rfl⟩, isRelevant_span p k₀ hk σ⟩`. Rewrite using `[← Bridge.intNum_map_eq_geoNum p n _ hV (Ideal.mem_span_singleton_self _) (ringKrullDim_span p k₀ hk σ)]`. Establish `hb : (Ideal.span {C (p : ℤ)} : Ideal (MRing ι)).map (MvPolynomial.map (Int.castRingHom (ZMod p))) = ⊥` using `(Ideal.map_eq_bot_iff_le_ker _).mpr (span_eq_ker p).le`.

Rewrite using `[hb]`. Conclude with `intNum_bot p k₀ hk σ a ha`.
-/
theorem geoNum_span (k₀ : K) (hk : ∀ a : K, a = k₀) {n : ℕ} (σ : ι k₀ ≃ Fin (n + 1)) (a : K → ℤ) (ha : a k₀ = 1) :
    geoNum n (Ideal.span {C (p : ℤ)} : Ideal (MRing ι)) (fun _ : Fin n => a) = 1 := by
  have hV : IsMultiProjPrime (Ideal.span {C (p : ℤ)} : Ideal (MRing ι)) :=
    ⟨isPrime_span p, ⟨{C (p : ℤ)}, fun f hf => ⟨0, by
      rw [Set.mem_singleton_iff.mp hf]
      exact Inter.Conservation.isMultiHomog_C _⟩, rfl⟩, isRelevant_span p k₀ hk σ⟩
  rw [← Bridge.intNum_map_eq_geoNum p n _ hV (Ideal.mem_span_singleton_self _) (ringKrullDim_span p k₀ hk σ)]
  have hb : (Ideal.span {C (p : ℤ)} : Ideal (MRing ι)).map
      (MvPolynomial.map (Int.castRingHom (ZMod p))) = ⊥ :=
    (Ideal.map_eq_bot_iff_le_ker _).mpr (span_eq_ker p).le
  rw [hb]
  exact intNum_bot p k₀ hk σ a ha

omit p in
/- English proof (translation)
Use `⟨⟨k₀⟩, ⟨Ideal.isPrime_bot, ⟨∅, by simp, by simp⟩, fun k => ?_⟩, ?_, ?_⟩` and prove the remaining obligations. Take `rfl` from `hk k`. Use `⟨σ.symm 0, ?_⟩` and prove the remaining obligations. Rewrite using `[Ideal.mem_bot]`. Conclude with `X_ne_zero _`.

Conclude with `Ideal.comap_bot_of_injective _ (C_injective _ _)`. Rewrite using `[ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot _), MvPolynomial.ringKrullDim_of_isNoetherianRing, IsPrincipalIdealRing.ringKrullDim_eq_one ℤ Int.not_isField, card_coords ι k₀ hk σ, card_blocks k₀ hk]`. Use `push_cast`. Conclude with `add_comm _ _`.
-/
theorem arithVar_bot (k₀ : K) (hk : ∀ a : K, a = k₀) {n : ℕ} (σ : ι k₀ ≃ Fin (n + 1)) :
    IsArithVar (⊥ : Ideal (MRing ι)) (n + 1) := by
  refine ⟨⟨k₀⟩, ⟨Ideal.isPrime_bot, ⟨∅, by simp, by simp⟩, fun k => ?_⟩, ?_, ?_⟩
  · obtain rfl := hk k
    refine ⟨σ.symm 0, ?_⟩
    rw [Ideal.mem_bot]
    exact X_ne_zero _
  · exact Ideal.comap_bot_of_injective _ (C_injective _ _)
  · rw [ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot _),
      MvPolynomial.ringKrullDim_of_isNoetherianRing, IsPrincipalIdealRing.ringKrullDim_eq_one ℤ Int.not_isField,
      card_coords ι k₀ hk σ, card_blocks k₀ hk]
    push_cast
    exact add_comm _ _

omit p in

/- English proof (translation)
Establish `hP` using `arithVar_bot k₀ hk σ`. Establish `: Fact (Nat.Prime 2)` using `⟨Nat.prime_two⟩`. Take `⟨h1, h2⟩` from `(Inter.Conservation.proof : ConservationStatement) K ι (II K ι) (hII _ _) ⊥ n (fun _ => L) 2 hP (fun _ => hL) Nat.prime_two`. Establish `hW : (Ideal.span {C ((2 : ℕ) : ℤ)} : Ideal (MRing ι)) ∈ divSupp (⊥ : Ideal (MRing ι)) (C ((2 : ℕ) : ℤ))`. Rewrite using `[divSupp_bot 2 k₀ hk σ]`.

Both sides reduce to the same expression. Use `isPrime_span (ι := ι) 2` as an intermediate fact. Establish `hv : vertR (⊥ : Ideal (MRing ι)) (fun _ : Fin n => L) (C ((2 : ℕ) : ℤ)) = Real.log ((2 : ℕ) : ℝ)`. Establish `hg : geoNum n (Ideal.span {C ((2 : ℕ) : ℤ)} : Ideal (MRing ι)) (fun j => ((fun _ : Fin n => L) j).a) = 1` using `geoNum_span 2 k₀ hk σ L.a ha`. Unfold `vertR`.

Rewrite using `[divSupp_bot 2 k₀ hk σ, finsum_mem_singleton, if_neg (Inter.Conservation.not_horizontal Nat.prime_two hW), Inter.Conservation.charOf_eq Nat.prime_two hW, bot_sup_eq, ReciprocityTheory.ChartRestriction.G.AI.I1.inh_multAt_self, hg]`. Simplify using the standard rewrite rules. Rewrite `h2` using `[h1, hv]`. Establish `hlog : Real.log ((2 : ℕ) : ℝ) ≠ 0` using `(Real.log_pos (by norm_num)).ne'`. Establish `h3 : Real.log ((2 : ℕ) : ℝ) * 1 = Real.log ((2 : ℕ) : ℝ) * ptsIntegral (⊥ : Ideal (MRing ι)) (pot fun _ : Fin n => L) (fun _ => 1)`.

Rewrite using `[mul_one]`. Conclude with `h2`. Conclude with `(mul_left_cancel₀ hlog h3).symm`.
-/
theorem ptsIntegral_bot (II : IntersectionSystem) (hII : IsIntersectionSystem II) (k₀ : K) (hk : ∀ a : K, a = k₀)
    {n : ℕ} (σ : ι k₀ ≃ Fin (n + 1)) (L : HermLine ι) (hL : IsSmoothHerm L) (ha : L.a k₀ = 1) :
    ptsIntegral (⊥ : Ideal (MRing ι)) (pot fun _ : Fin n => L) (fun _ => 1) = 1 := by
  have hP := arithVar_bot k₀ hk σ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨h1, h2⟩ := (Inter.Conservation.proof : ConservationStatement) K ι (II K ι) (hII _ _) ⊥ n
    (fun _ => L) 2 hP (fun _ => hL) Nat.prime_two
  have hW : (Ideal.span {C ((2 : ℕ) : ℤ)} : Ideal (MRing ι)) ∈ divSupp (⊥ : Ideal (MRing ι)) (C ((2 : ℕ) : ℤ)) := by
    rw [divSupp_bot 2 k₀ hk σ]
    rfl
  have := isPrime_span (ι := ι) 2
  have hv : vertR (⊥ : Ideal (MRing ι)) (fun _ : Fin n => L) (C ((2 : ℕ) : ℤ)) = Real.log ((2 : ℕ) : ℝ) := by
    have hg : geoNum n (Ideal.span {C ((2 : ℕ) : ℤ)} : Ideal (MRing ι)) (fun j => ((fun _ : Fin n => L) j).a) = 1 :=
      geoNum_span 2 k₀ hk σ L.a ha
    unfold vertR
    rw [divSupp_bot 2 k₀ hk σ, finsum_mem_singleton, if_neg (Inter.Conservation.not_horizontal Nat.prime_two hW),
      Inter.Conservation.charOf_eq Nat.prime_two hW, bot_sup_eq, ReciprocityTheory.ChartRestriction.G.AI.I1.inh_multAt_self, hg]
    simp
  rw [h1, hv] at h2
  have hlog : Real.log ((2 : ℕ) : ℝ) ≠ 0 := (Real.log_pos (by norm_num)).ne'
  have h3 : Real.log ((2 : ℕ) : ℝ) * 1 =
      Real.log ((2 : ℕ) : ℝ) * ptsIntegral (⊥ : Ideal (MRing ι)) (pot fun _ : Fin n => L) (fun _ => 1) := by
    rw [mul_one]
    exact h2
  exact (mul_left_cancel₀ hlog h3).symm

end Proj

section First

variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ} {K : Type} [Fintype K] [DecidableEq K]

/- English proof (translation)
Use `set j : K → FlBlock Ψ N := fun _ => (τ, ⟨0, h⟩) with hj`. Establish `hN : 0 < N` using `by omega`. Set `emb : (Σ k, PIdx j k) → Ψ × Fin N × Fin N` to `fun p => (τ, ⟨0, hN⟩, p.2.1 ⟨0, Nat.succ_pos _⟩)`. Establish `hemb : Function.Injective emb`. Introduce and unpack `⟨a, A⟩ ⟨b, B⟩ hab`.

Take `rfl : a = b` from `(hk a).trans (hk b).symm`. Establish `h3 : A.1 ⟨0, Nat.succ_pos _⟩ = B.1 ⟨0, Nat.succ_pos _⟩` using `(Prod.ext_iff.1 (Prod.ext_iff.1 hab).2).2`. Establish `hAB : A = B`. Use `Subtype.ext (funext fun x => ?_)` and prove the remaining obligations. Establish `hx : x = ⟨0, Nat.succ_pos _⟩` using `Fin.ext (by have := x.2; simp [j] at this ⊢)`.

Rewrite using `[hx]`. Conclude with `h3`. Rewrite using `[hAB]`. Establish `hy : ∀ p, yPart j p = algebraMap (MvPolynomial (Ψ × Fin N × Fin N) ℚ) (ΩFl Ψ N) (X (emb p))`. Introduce `p`.

Unfold `yPart yFl`. Use `congr 1`. Express the relevant statement in the definitionally equal form `Matrix.det (n := Fin 1) _ = _`. Rewrite using `[Matrix.det_fin_one]`. Both sides reduce to the same expression.

Establish `hval : ∀ x : MRing (PIdx j), aeval (yPart j) x = algebraMap (MvPolynomial (Ψ × Fin N × Fin N) ℚ) (ΩFl Ψ N) (rename emb (map (Int.castRingHom ℚ) x))`. Introduce `x`. Proceed by induction on `x using MvPolynomial.induction_on with`. Consider the case `C a => simp`. Consider the case `add f g hf hg => simp only [map_add, hf, hg]`.

Consider the case `mul_X f p hf => simp only [map_mul, hf, aeval_X, map_X, rename_X, hy]`. Establish `hcomp : ∀ x : MRing (PIdx j), aeval (fun _ : K => (1 : ΩFl Ψ N)) (mConeMap (yPart j) x) = aeval (yPart j) x`. Introduce `x`. Proceed by induction on `x using MvPolynomial.induction_on with`. Consider the case `C a => simp [mConeMap]`.

Consider the case `add f g hf hg => simp only [map_add, hf, hg]`. Consider the case `mul_X f p hf => simp only [map_mul, hf]`. Simplify using `[mConeMap]`. Unfold `PPart mCoordIdeal`. Rewrite using `[← RingHom.injective_iff_ker_eq_bot]`.

Introduce `x y hxy`. Establish `h1` using `congrArg (aeval (fun _ : K => (1 : ΩFl Ψ N))) hxy`. Rewrite `h1` using `[hcomp, hcomp, hval, hval]`. Establish `h2` using `IsFractionRing.injective (MvPolynomial (Ψ × Fin N × Fin N) ℚ) (ΩFl Ψ N) h1`. Conclude with `map_injective _ (RingHom.injective_int _) (rename_injective _ hemb h2)`.
-/
theorem pPart_eq_bot (τ : Ψ) (h : 0 < N - 1) (k₀ : K) (hk : ∀ a : K, a = k₀) :
    PPart (fun _ : K => ((τ, ⟨0, h⟩) : FlBlock Ψ N)) = ⊥ := by
  set j : K → FlBlock Ψ N := fun _ => (τ, ⟨0, h⟩) with hj
  have hN : 0 < N := by omega
  let emb : (Σ k, PIdx j k) → Ψ × Fin N × Fin N := fun p => (τ, ⟨0, hN⟩, p.2.1 ⟨0, Nat.succ_pos _⟩)
  have hemb : Function.Injective emb := by
    rintro ⟨a, A⟩ ⟨b, B⟩ hab
    obtain rfl : a = b := (hk a).trans (hk b).symm
    have h3 : A.1 ⟨0, Nat.succ_pos _⟩ = B.1 ⟨0, Nat.succ_pos _⟩ := (Prod.ext_iff.1 (Prod.ext_iff.1 hab).2).2
    have hAB : A = B := by
      refine Subtype.ext (funext fun x => ?_)
      have hx : x = ⟨0, Nat.succ_pos _⟩ := Fin.ext (by have := x.2; simp [j] at this ⊢)
      rw [hx]
      exact h3
    rw [hAB]
  have hy : ∀ p, yPart j p = algebraMap (MvPolynomial (Ψ × Fin N × Fin N) ℚ) (ΩFl Ψ N) (X (emb p)) := by
    intro p
    unfold yPart yFl
    congr 1
    change Matrix.det (n := Fin 1) _ = _
    rw [Matrix.det_fin_one]
    rfl
  have hval : ∀ x : MRing (PIdx j), aeval (yPart j) x = algebraMap (MvPolynomial (Ψ × Fin N × Fin N) ℚ) (ΩFl Ψ N)
      (rename emb (map (Int.castRingHom ℚ) x)) := by
    intro x
    induction x using MvPolynomial.induction_on with
    | C a => simp
    | add f g hf hg => simp only [map_add, hf, hg]
    | mul_X f p hf => simp only [map_mul, hf, aeval_X, map_X, rename_X, hy]
  have hcomp : ∀ x : MRing (PIdx j), aeval (fun _ : K => (1 : ΩFl Ψ N)) (mConeMap (yPart j) x) = aeval (yPart j) x := by
    intro x
    induction x using MvPolynomial.induction_on with
    | C a => simp [mConeMap]
    | add f g hf hg => simp only [map_add, hf, hg]
    | mul_X f p hf => simp only [map_mul, hf]; simp [mConeMap]
  unfold PPart mCoordIdeal
  rw [← RingHom.injective_iff_ker_eq_bot]
  intro x y hxy
  have h1 := congrArg (aeval (fun _ : K => (1 : ΩFl Ψ N))) hxy
  rw [hcomp, hcomp, hval, hval] at h1
  have h2 := IsFractionRing.injective (MvPolynomial (Ψ × Fin N × Fin N) ℚ) (ΩFl Ψ N) h1
  exact map_injective _ (RingHom.injective_int _) (rename_injective _ hemb h2)

def incrOne (N : ℕ) : PlueckerData.Incr 1 N ≃ Fin N where
  toFun A := A.1 0
  invFun i := ⟨fun _ => i, Subsingleton.strictMono _⟩
  left_inv A := Subtype.ext (funext fun x => by rw [Subsingleton.elim x 0])
  right_inv _ := rfl

end First

/- English proof (translation)
Introduce `Ψ _ _ N K _ _ II hII k₀ hk j hj`. Choose the witnesses or unpack the hypotheses as in `⟨τ, h, rfl⟩ : ∃ (τ : Ψ) (h : 0 < N - 1), j = fun _ => ((τ, ⟨0, h⟩) : FlBlock Ψ N) := by`. Establish `h : 0 < N - 1` using `Nat.lt_of_le_of_lt (Nat.zero_le _) (j k₀).2.2`. Use `⟨(j k₀).1, h, ?_⟩` and prove the remaining obligations. Take `⟨k, hk'⟩` from `hj.down k₀ ((j k₀).1, ⟨0, h⟩) rfl (Nat.zero_le _)`.

Use function extensionality and compare the values at `a`. Rewrite `hk'` using `[hk k]`. Rewrite using `[hk a]`. Conclude with `hk'`. Establish `hN : N - 1 + 1 = N` using `by omega`.

Rewrite using `[pPart_eq_bot τ h k₀ hk]`. Use `ptsIntegral_bot II hII.1 k₀ hk (n := N - 1) ((incrOne N).trans (finCongr hN.symm)) _ (FlagHeightMultilinear.isSmoothHerm_fsHerm _) ?_` and prove the remaining obligations. Simplify using `[unitLine, fsHerm]`.
-/
theorem ptsIntegral_first : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (K : Type) [Fintype K] [DecidableEq K]
    (II : IntersectionSystem), IsFullIntersectionSystem II → ∀ k₀ : K, (∀ a : K, a = k₀) →
    ∀ j : K → FlBlock Ψ N, IsChain j →
      ptsIntegral (PPart j) (pot fun _ : Fin (N - 1) => unitLine j k₀) (fun _ => 1) = 1 := by
  intro Ψ _ _ N K _ _ II hII k₀ hk j hj
  obtain ⟨τ, h, rfl⟩ : ∃ (τ : Ψ) (h : 0 < N - 1), j = fun _ => ((τ, ⟨0, h⟩) : FlBlock Ψ N) := by
    have h : 0 < N - 1 := Nat.lt_of_le_of_lt (Nat.zero_le _) (j k₀).2.2
    refine ⟨(j k₀).1, h, ?_⟩
    obtain ⟨k, hk'⟩ := hj.down k₀ ((j k₀).1, ⟨0, h⟩) rfl (Nat.zero_le _)
    funext a
    rw [hk k] at hk'
    rw [hk a]
    exact hk'
  have hN : N - 1 + 1 = N := by omega
  rw [pPart_eq_bot τ h k₀ hk]
  refine ptsIntegral_bot II hII.1 k₀ hk (n := N - 1)
    ((incrOne N).trans (finCongr hN.symm)) _ (FlagHeightMultilinear.isSmoothHerm_fsHerm _) ?_
  simp [unitLine, fsHerm]

end GlobalTheory.CompanionTheory.Ar.Top.FlDeg.Base
