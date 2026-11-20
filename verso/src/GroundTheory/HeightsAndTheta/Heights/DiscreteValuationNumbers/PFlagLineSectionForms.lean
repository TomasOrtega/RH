import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagLineSection
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

set_option linter.unusedSectionVars false

namespace FlagLineSectionProof

variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type} {Ω : Type*} [Field Ω]
  {F : Type*} [Field F] [Algebra F Ω] {N M : ℕ} {E : Type*} [AddCommGroup E] [Module Ω E]
  {Φ : Type*} [Field Φ] [Algebra Ω Φ]

abbrev projMap (F : Type*) [Field F] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (w : Module.Basis (Fin N) Ω E)
    (φ : Fin M → Module.Dual Ω E) (t : Fin N → Φ) :
    MRing (bundleIdx ι M) F →+* MvPolynomial (Option K) Φ :=
  eval₂Hom (C.comp ((algebraMap Ω Φ).comp (algebraMap F Ω))) (fun p => C (projCoord y w φ t p) * X p.1)

/- English proof (translation)
The claim follows from `RingHom.mem_ker`.
-/
theorem mem_projIdeal_iff {y : (Σ k, ι k) → Ω} {w : Module.Basis (Fin N) Ω E}
    {φ : Fin M → Module.Dual Ω E} {t : Fin N → Φ} {h : MRing (bundleIdx ι M) F} :
    h ∈ projIdeal F y w φ t ↔ projMap F y w φ t h = 0 :=
  RingHom.mem_ker

def tMon (α : K → ℕ) : MvPolynomial (Option K) Φ := ∏ k, X (some k) ^ α k

/- English proof (translation)
Simplify using `only [tMon, Pi.add_apply, pow_add, Finset.prod_mul_distrib]`.
-/
theorem tMon_add (α β : K → ℕ) : (tMon (α + β) : MvPolynomial (Option K) Φ) = tMon α * tMon β := by
  simp only [tMon, Pi.add_apply, pow_add, Finset.prod_mul_distrib]

def liftN (α : K → ℕ) : Option K → ℕ := fun o => Option.elim o 0 α

/- English proof (translation)
Apply the tactic sequence `funext o; cases o <;> simp [liftN]`.
-/
theorem liftN_add (α β : K → ℕ) : liftN (α + β) = liftN α + liftN β := by
  funext o; cases o <;> simp [liftN]

def chartMon (F : Type*) [Field F] (M : ℕ) (c : ∀ k, ι k) (α : K → ℕ) : MRing (bundleIdx ι M) F :=
  ∏ k, (X ⟨some k, c k⟩ : MRing (bundleIdx ι M) F) ^ α k

/- English proof (translation)
Simplify using `[projMap, projCoord]`.
-/
theorem projMap_X_some (y : (Σ k, ι k) → Ω) (w : Module.Basis (Fin N) Ω E)
    (φ : Fin M → Module.Dual Ω E) (t : Fin N → Φ) (k : K) (i : ι k) :
    projMap F y w φ t (X ⟨some k, i⟩) = C (algebraMap Ω Φ (y ⟨k, i⟩)) * X (some k) := by
  simp [projMap, projCoord]

/- English proof (translation)
Simplify using `[projMap, projCoord]`.
-/
theorem projMap_X_none (y : (Σ k, ι k) → Ω) (w : Module.Basis (Fin N) Ω E)
    (φ : Fin M → Module.Dual Ω E) (t : Fin N → Φ) (l : Fin M) :
    projMap F y w φ t (X ⟨none, l⟩) =
      C (∑ i, t i * algebraMap Ω Φ (φ l (w i))) * X none := by
  simp [projMap, projCoord]

/- English proof (translation)
Rewrite using `[Finset.sum_eq_single ⟨0, h0⟩]`. Simplify using `[truncCoord]`. Introduce `j _ hj`. Establish `: ¬ (j : ℕ) < 1`. Introduce `h`.

Apply `hj` to reduce the goal to its premises. Use `ext`. Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers. Simplify using `[truncCoord, this]`.

Simplify using the standard rewrite rules.
-/
theorem sum_truncCoord_one (t : Fin N → Φ) (h0 : 0 < N) (z : Fin N → Φ) :
    ∑ i, truncCoord t 1 i * z i = t ⟨0, h0⟩ * z ⟨0, h0⟩ := by
  rw [Finset.sum_eq_single ⟨0, h0⟩]
  · simp [truncCoord]
  · intro j _ hj
    have : ¬ (j : ℕ) < 1 := by
      intro h; apply hj; ext; simp; omega
    simp [truncCoord, this]
  · simp

/- English proof (translation)
Simplify using `[projMap]`.
-/
theorem projMap_C (y : (Σ k, ι k) → Ω) (w : Module.Basis (Fin N) Ω E)
    (φ : Fin M → Module.Dual Ω E) (t : Fin N → Φ) (r : F) :
    projMap F y w φ t (C r) = C (algebraMap Ω Φ (algebraMap F Ω r)) := by
  simp [projMap]

/- English proof (translation)
Simplify using `only [chartMon, map_prod, map_pow, projMap_X_some, mul_pow, Finset.prod_mul_distrib, tMon]`.
-/
theorem projMap_chartMon (y : (Σ k, ι k) → Ω) (w : Module.Basis (Fin N) Ω E)
    (φ : Fin M → Module.Dual Ω E) (t : Fin N → Φ) (c : ∀ k, ι k) (α : K → ℕ) :
    projMap F y w φ t (chartMon F M c α) =
      C (algebraMap Ω Φ (∏ k, y ⟨k, c k⟩ ^ α k)) * tMon α := by
  simp only [chartMon, map_prod, map_pow, projMap_X_some, mul_pow, Finset.prod_mul_distrib, tMon]

/- English proof (translation)
Unfold `IsMultiHomog chartMon`. Establish `h` using `IsWeightedHomogeneous.prod (w := blockWeight (bundleIdx ι M)) Finset.univ (fun k => (X ⟨some k, c k⟩ : MRing (bundleIdx ι M) F) ^ α k) (fun k => α k • blockWeight (bundleIdx ι M) ⟨some k, c k⟩) (fun k _ => (isWeightedHomogeneous_X F _ _).pow (α k))`. Use `h using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `o`. Consider the cases of `o with`.

Consider the case `none => simp [liftN, blockWeight, Finset.sum_apply]`. Consider the case `some k => simp [liftN, blockWeight, Finset.sum_apply, Pi.single_apply]`.
-/
theorem isMultiHomog_chartMon (c : ∀ k, ι k) (α : K → ℕ) :
    IsMultiHomog (chartMon F M c α) (liftN α) := by
  unfold IsMultiHomog chartMon
  have h := IsWeightedHomogeneous.prod (w := blockWeight (bundleIdx ι M)) Finset.univ
    (fun k => (X ⟨some k, c k⟩ : MRing (bundleIdx ι M) F) ^ α k)
    (fun k => α k • blockWeight (bundleIdx ι M) ⟨some k, c k⟩)
    (fun k _ => (isWeightedHomogeneous_X F _ _).pow (α k))
  convert h using 1
  funext o
  cases o with
  | none => simp [liftN, blockWeight, Finset.sum_apply]
  | some k => simp [liftN, blockWeight, Finset.sum_apply, Pi.single_apply]

/- English proof (translation)
Unfold `IsMultiHomog`. Conclude with `isWeightedHomogeneous_X F _ _`.
-/
theorem isMultiHomog_X_none (l : Fin M) :
    IsMultiHomog (X ⟨none, l⟩ : MRing (bundleIdx ι M) F) (Pi.single none 1) := by
  unfold IsMultiHomog
  exact isWeightedHomogeneous_X F _ _

variable (F M) in

def IsChartForm (y : (Σ k, ι k) → Ω) (w : Module.Basis (Fin N) Ω E)
    (φ : Fin M → Module.Dual Ω E) (t : Fin N → Φ) (c : ∀ k, ι k) (a : Ω) (n : ℕ)
    (A : MRing (bundleIdx ι M) F) : Prop :=
  IsMultiHomog A (liftN fun _ => n) ∧
    projMap F y w φ t A = C (algebraMap Ω Φ (a * segreVec y c ^ n)) * tMon (fun _ => n)

/- English proof (translation)
Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `h.1.mul (isMultiHomog_chartMon (F := F) (M := M) c (fun _ => m))` as an intermediate fact. Rewrite `this` using `[← liftN_add]`. Then use the resulting hypothesis. Rewrite using `[map_mul, h.2, projMap_chartMon]`. Establish `e : (fun _ : K => n + m) = (fun _ => n) + (fun _ => m)` using `rfl`.

Rewrite using `[e, tMon_add]`. Simplify using `only [segreVec, pow_add, Finset.prod_pow, map_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem IsChartForm.pad {y : (Σ k, ι k) → Ω} {w : Module.Basis (Fin N) Ω E}
    {φ : Fin M → Module.Dual Ω E} {t : Fin N → Φ} {c : ∀ k, ι k} {a : Ω} {n : ℕ}
    {A : MRing (bundleIdx ι M) F} (h : IsChartForm F M y w φ t c a n A) (m : ℕ) :
    IsChartForm F M y w φ t c a (n + m) (A * chartMon F M c (fun _ => m)) := by
  refine ⟨?_, ?_⟩
  · have := h.1.mul (isMultiHomog_chartMon (F := F) (M := M) c (fun _ => m))
    rwa [← liftN_add] at this
  · rw [map_mul, h.2, projMap_chartMon]
    have e : (fun _ : K => n + m) = (fun _ => n) + (fun _ => m) := rfl
    rw [e, tMon_add]
    simp only [segreVec, pow_add, Finset.prod_pow, map_mul]
    ring

/- English proof (translation)
Proceed by induction on `ha using Algebra.adjoin_induction with`. Consider the case `mem x hx`. Take `⟨j, rfl⟩` from `hx`. Use `⟨1, chartMon F M j (fun _ => 1), ?_, ?_⟩` and prove the remaining obligations. Conclude with `isMultiHomog_chartMon j _`.

Rewrite using `[projMap_chartMon, div_mul_eq_mul_div, pow_one, mul_div_assoc, div_self hc, mul_one]`. Simplify using `[segreVec]`. Consider the case `algebraMap r`. Use `⟨0, C r, ?_, ?_⟩` and prove the remaining obligations. Apply the tactic sequence `have e : liftN (fun _ : K => 0) = 0 := by funext o; cases o <;> rfl`.

Unfold `IsMultiHomog`. Rewrite using `[e]`. Conclude with `isWeightedHomogeneous_C _ _`. Rewrite using `[projMap_C]`. Simplify using `[tMon]`.

Consider the case `add x z _ _ hx hz`. Take `⟨n₁, A₁, h₁⟩` from `hx`. Take `⟨n₂, A₂, h₂⟩` from `hz`. Establish `h₁'` using `h₁.pad n₂`. Establish `h₂'` using `h₂.pad n₁`.

Rewrite `h₂'` using `[Nat.add_comm n₂ n₁]`. Use `⟨n₁ + n₂, _, h₁'.1.add h₂'.1, ?_⟩` and prove the remaining obligations. Rewrite using `[map_add, h₁'.2, h₂'.2, add_mul, map_add, C_add, add_mul]`. Consider the case `mul x z _ _ hx hz`. Take `⟨n₁, A₁, h₁⟩` from `hx`.

Take `⟨n₂, A₂, h₂⟩` from `hz`. Use `⟨n₁ + n₂, A₁ * A₂, ?_, ?_⟩` and prove the remaining obligations. Use `h₁.1.mul h₂.1` as an intermediate fact. Rewrite `this` using `[← liftN_add]`. Then use the resulting hypothesis. Rewrite using `[map_mul, h₁.2, h₂.2]`.

Establish `e : (fun _ : K => n₁ + n₂) = (fun _ => n₁) + (fun _ => n₂)` using `rfl`. Rewrite using `[e, tMon_add, pow_add]`. Simplify using `only [map_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_chartForm (y : (Σ k, ι k) → Ω) (w : Module.Basis (Fin N) Ω E)
    (φ : Fin M → Module.Dual Ω E) (t : Fin N → Φ) (c : ∀ k, ι k) (hc : segreVec y c ≠ 0)
    {a : Ω} (ha : a ∈ chartRing F (segreVec y) c) :
    ∃ (n : ℕ) (A : MRing (bundleIdx ι M) F), IsChartForm F M y w φ t c a n A := by
  induction ha using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    refine ⟨1, chartMon F M j (fun _ => 1), ?_, ?_⟩
    · exact isMultiHomog_chartMon j _
    · rw [projMap_chartMon, div_mul_eq_mul_div, pow_one, mul_div_assoc, div_self hc, mul_one]
      simp [segreVec]
  | algebraMap r =>
    refine ⟨0, C r, ?_, ?_⟩
    · have e : liftN (fun _ : K => 0) = 0 := by funext o; cases o <;> rfl
      unfold IsMultiHomog
      rw [e]
      exact isWeightedHomogeneous_C _ _
    · rw [projMap_C]
      simp [tMon]
  | add x z _ _ hx hz =>
    obtain ⟨n₁, A₁, h₁⟩ := hx
    obtain ⟨n₂, A₂, h₂⟩ := hz
    have h₁' := h₁.pad n₂
    have h₂' := h₂.pad n₁
    rw [Nat.add_comm n₂ n₁] at h₂'
    refine ⟨n₁ + n₂, _, h₁'.1.add h₂'.1, ?_⟩
    rw [map_add, h₁'.2, h₂'.2, add_mul, map_add, C_add, add_mul]
  | mul x z _ _ hx hz =>
    obtain ⟨n₁, A₁, h₁⟩ := hx
    obtain ⟨n₂, A₂, h₂⟩ := hz
    refine ⟨n₁ + n₂, A₁ * A₂, ?_, ?_⟩
    · have := h₁.1.mul h₂.1
      rwa [← liftN_add] at this
    · rw [map_mul, h₁.2, h₂.2]
      have e : (fun _ : K => n₁ + n₂) = (fun _ => n₁) + (fun _ => n₂) := rfl
      rw [e, tMon_add, pow_add]
      simp only [map_mul]
      ring

/- English proof (translation)
Use `choose n A hA using fun j => exists_chartForm (M := M) y w φ t c hc (ha j)`. Use `⟨∑ j, n j, fun m hm j => ?_⟩` and prove the remaining obligations. Establish `hle : n j ≤ m` using `(Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)).trans hm`. Use `(hA j).pad (m - n j)` as an intermediate fact. Rewrite `this` using `[Nat.add_sub_cancel' hle]`.

Conclude with `⟨_, this⟩`.
-/
theorem exists_chartForm_family (y : (Σ k, ι k) → Ω) (w : Module.Basis (Fin N) Ω E)
    (φ : Fin M → Module.Dual Ω E) (t : Fin N → Φ) (c : ∀ k, ι k) (hc : segreVec y c ≠ 0)
    {J : Type*} [Fintype J] (a : J → Ω) (ha : ∀ j, a j ∈ chartRing F (segreVec y) c) :
    ∃ n : ℕ, ∀ m, n ≤ m → ∀ j, ∃ A : MRing (bundleIdx ι M) F, IsChartForm F M y w φ t c (a j) m A := by
  choose n A hA using fun j => exists_chartForm (M := M) y w φ t c hc (ha j)
  refine ⟨∑ j, n j, fun m hm j => ?_⟩
  have hle : n j ≤ m := (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)).trans hm
  have := (hA j).pad (m - n j)
  rw [Nat.add_sub_cancel' hle] at this
  exact ⟨_, this⟩

def chartZ (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (e : K → ℤ) : Ω := ∏ k, y ⟨k, c k⟩ ^ e k

/- English proof (translation)
Simplify using `only [chartZ, Pi.add_apply, zpow_add₀ (hc _), Finset.prod_mul_distrib]`.
-/
theorem chartZ_add {y : (Σ k, ι k) → Ω} {c : ∀ k, ι k} (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (e e' : K → ℤ) :
    chartZ y c (e + e') = chartZ y c e * chartZ y c e' := by
  simp only [chartZ, Pi.add_apply, zpow_add₀ (hc _), Finset.prod_mul_distrib]

/- English proof (translation)
Simplify using `[chartZ]`.
-/
theorem chartZ_natCast (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (α : K → ℕ) :
    chartZ y c (fun k => (α k : ℤ)) = ∏ k, y ⟨k, c k⟩ ^ α k := by
  simp [chartZ]

/- English proof (translation)
Simplify using `[chartZ, segreVec, Finset.prod_pow]`.
-/
theorem segreVec_pow (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (n : ℕ) :
    segreVec y c ^ n = chartZ y c (fun _ => (n : ℤ)) := by
  simp [chartZ, segreVec, Finset.prod_pow]

/- English proof (translation)
The claim follows from `Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (hc k)`.
-/
theorem chartZ_ne_zero {y : (Σ k, ι k) → Ω} {c : ∀ k, ι k} (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (e : K → ℤ) :
    chartZ y c e ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (hc k)

/- English proof (translation)
Introduce `k` and use `(Finset.prod_ne_zero_iff.mp hc) k (Finset.mem_univ k)`.
-/
theorem live_of_segreVec_ne_zero {y : (Σ k, ι k) → Ω} {c : ∀ k, ι k} (hc : segreVec y c ≠ 0) :
    ∀ k, y ⟨k, c k⟩ ≠ 0 :=
  fun k => (Finset.prod_ne_zero_iff.mp hc) k (Finset.mem_univ k)

/- English proof (translation)
The claim follows from `Finset.prod_ne_zero_iff.mpr fun k _ => hc k`.
-/
theorem segreVec_ne_zero_of_live {y : (Σ k, ι k) → Ω} {c : ∀ k, ι k} (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) :
    segreVec y c ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun k _ => hc k

/- English proof (translation)
The claim follows from `Finset.prod_ne_zero_iff.mpr fun _ _ => pow_ne_zero _ (X_ne_zero _)`.
-/
theorem tMon_ne_zero (α : K → ℕ) : (tMon α : MvPolynomial (Option K) Φ) ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun _ _ => pow_ne_zero _ (X_ne_zero _)

end FlagLineSectionProof

end

end GroundTheory.Heights₂.Heights.NumbersDVR
