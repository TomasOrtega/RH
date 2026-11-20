import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ExistsPhiBridge
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.RingDataOfCaseAOfP9
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ArcLengthFourCostBound

noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.N.Ln17

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

variable [FiniteDimensional Qp LL]

/- English proof (translation)
Establish `hp : PD.p.Prime` using `by first`. Consider the case `exact PD.hp.out`. Consider the case `exact PD.hp`. Consider the case `exact PD.p_prime`. Consider the case `exact PD.prime`.

Consider the case `exact PD.hprime`. Consider the case `exact Fact.out`. Take `⟨⟨w1, hw1⟩, ⟨w2, hw2⟩, -, -⟩` from `hR`. Establish `hπ0 : IsUnit (algebraMap (LetA O n) W.EE W.π₀)`. Rewrite using `[hw1, map_mul, map_pow]`.

Conclude with `(w1.isUnit.map _).mul (W.EE_π.pow _)`. Establish `hq0 : IsUnit (algebraMap (LetA O n) W.EE (qA W))`. Establish `h` using `congrArg (algebraMap (LetA O n) W.EE) hw2`. Rewrite `h` using `[map_mul, map_mul, map_pow]`. Establish `hφ : IsUnit (algebraMap (LetA O n) W.EE (W.φA W.π₀))`.

Rewrite using `[show algebraMap (LetA O n) W.EE (W.φA W.π₀) = W.φE (algebraMap (LetA O n) W.EE W.π₀) from (W.φE_ext W.π₀).symm]`. Conclude with `hπ0.map W.φE`. Rewrite `hφ` using `[h]`. Establish `h3` using `isUnit_of_mul_isUnit_right hφ`. Conclude with `(isUnit_pow_iff (by have := hp.two_le; omega)).1 h3`.

Proceed by induction on `t with`. Consider the case `zero => simpa [ps] using hq0`. Consider the case `succ t ih`. Establish `e : algebraMap (LetA O n) W.EE (ps W (t + 1)) = W.φE (algebraMap (LetA O n) W.EE (ps W t))`. Rewrite using `[ps, ps, pow_succ', AlgHom.mul_apply]`.

Conclude with `(W.φE_ext _).symm`. Rewrite using `[e]`. Conclude with `ih.map W.φE`.
-/
theorem ArcLengthFourSecond.isUnit_ps (W : LocWach PD LL O v n) (hR : GS.RD W) (t : ℕ) :
    IsUnit (algebraMap (LetA O n) W.EE (ps W t)) := by
  have hp : PD.p.Prime := by
    first
      | exact PD.hp.out
      | exact PD.hp
      | exact PD.p_prime
      | exact PD.prime
      | exact PD.hprime
      | exact Fact.out
  obtain ⟨⟨w1, hw1⟩, ⟨w2, hw2⟩, -, -⟩ := hR
  have hπ0 : IsUnit (algebraMap (LetA O n) W.EE W.π₀) := by
    rw [hw1, map_mul, map_pow]
    exact (w1.isUnit.map _).mul (W.EE_π.pow _)
  have hq0 : IsUnit (algebraMap (LetA O n) W.EE (qA W)) := by
    have h := congrArg (algebraMap (LetA O n) W.EE) hw2
    rw [map_mul, map_mul, map_pow] at h
    have hφ : IsUnit (algebraMap (LetA O n) W.EE (W.φA W.π₀)) := by
      rw [show algebraMap (LetA O n) W.EE (W.φA W.π₀) = W.φE (algebraMap (LetA O n) W.EE W.π₀) from
        (W.φE_ext W.π₀).symm]
      exact hπ0.map W.φE
    rw [h] at hφ
    have h3 := isUnit_of_mul_isUnit_right hφ
    exact (isUnit_pow_iff (by have := hp.two_le; omega)).1 h3
  induction t with
  | zero => simpa [ps] using hq0
  | succ t ih =>
    have e : algebraMap (LetA O n) W.EE (ps W (t + 1)) = W.φE (algebraMap (LetA O n) W.EE (ps W t)) := by
      rw [ps, ps, pow_succ', AlgHom.mul_apply]
      exact (W.φE_ext _).symm
    rw [e]
    exact ih.map W.φE

/- English proof (translation)
Use `show (fun _ => Br.ι (F + G) : LetA O n) = (fun _ => Br.ι F : LetA O n) + (fun _ => Br.ι G : LetA O n)`. Rewrite using `[map_add]`. Both sides reduce to the same expression.
-/
theorem ArcLengthFourSecond.cst_add [IsDomain O] [IsDiscreteValuationRing O] {W : LocWach PD LL O v n} (Br : PhiBridge W)
    (F G : PowerSeries O) : Br.cst (F + G) = Br.cst F + Br.cst G := by
  show (fun _ => Br.ι (F + G) : LetA O n) = (fun _ => Br.ι F : LetA O n) + (fun _ => Br.ι G : LetA O n)
  rw [map_add]
  rfl

/- English proof (translation)
Use `haveI : Fact PD.p.Prime := ⟨PD.hp⟩`. Take `⟨Br⟩` from `exists_phiBridge W hcase hP9 T hT hO hinj`. Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible O`. Establish `hR` using `GS.ringData_of_caseA_of_p9 W hcase hP9`. Use `set y : ℝ := (wa : ℝ) - (Bn : ℝ) / PD.p - (η : ℝ) / (PD.p : ℝ) ^ 2 with hy`.

Use `set si : ℕ := ⌊y⌋₊ with hsi`. Establish `hk : eO (O` using `O) PD.p * si ≤ ⌈(eO (O := O) PD.p : ℝ) * ((wa : ℝ) - Bn / PD.p - η / (PD.p : ℝ) ^ 2)⌉₊ := by`. Rewrite using `[← hy]`. Distinguish the cases in `h0 : 0 ≤ y`. Establish `h1 : (si : ℝ) ≤ y` using `Nat.floor_le h0`.

Establish `h2 : ((eO (O` using `O) PD.p * si : ℕ) : ℝ) ≤ (eO (O := O) PD.p : ℝ) * y := by push_cast; exact mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)`. Conclude with `h2.trans (Nat.le_ceil _)` after adjusting the coercions. Establish `: si = 0` using `Nat.floor_eq_zero.mpr (by linarith)`. Rewrite using `[this, mul_zero]`. Conclude with `Nat.zero_le _`.

Establish `hmem` using `Br.P.c3b hϖ wa Bn η (Or.inl hBn) (eO (O := O) PD.p * si) hk`. Establish `hspan` using `span_C_l_pow hϖ Br.P.hl0 si`. Take `⟨r, hr⟩ : ∃ r : PowerSeries O, r * (PowerSeries.C ((PD.p : ℕ) : O)) ^ si = (PowerSeries.C ϖ) ^ (eO (O` from `O) PD.p * si) := by`. Establish `: (PowerSeries.C ϖ : PowerSeries O) ^ (eO (O` using `O) PD.p * si) ∈ Ideal.span {(PowerSeries.C ((PD.p : ℕ) : O) : PowerSeries O) ^ si} := by`. Rewrite using `[hspan]`.

Conclude with `Ideal.subset_span rfl`. Conclude with `Ideal.mem_span_singleton'.mp this`. Take `⟨α', β, hαβ⟩` from `Ideal.mem_span_pair.mp hmem`. Establish `hD : ps W 2 ^ wa = lA W ^ si * Br.cst (α' * r) + ps W 1 ^ Bn * ps W 0 ^ η * Br.cst β`. Establish `e0 : ps W 0 = qA W` using `by simp [ps]`.

Establish `e2 : Br.cst (Br.P.p 2 ^ wa) = Br.cst ((α' * r) * PowerSeries.C ((PD.p : ℕ) : O) ^ si + β * (Br.P.p 1 ^ Bn * PowerSeries.X ^ η))`. Rewrite using `[← hαβ, ← hr]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [ArcLengthFourSecond.cst_add, Br.cst_mul, Br.cst_pow] at e2`.

Rewrite `e2` using `[← Br.ps_eq, ← Br.ps_eq, ← Br.qA_eq, ← Br.lA_eq, ← e0]`. Rewrite using `[e2, Br.cst_mul]`. Expand and normalize the polynomial expressions, which then agree. Use `set e₄ := s - si with he₄`. Use `set t := e₄ + si - s with ht`.

Establish `hexp : lA W ^ s * lA W ^ t = lA W ^ e₄ * lA W ^ si`. Rewrite using `[← pow_add, ← pow_add]`. Use `congr 1`. Use linear arithmetic over natural numbers and integers. Establish `hUn : IsUnit (algebraMap (LetA O n) W.EE (ps W 2 ^ wa))`.

Rewrite using `[map_pow]`. Conclude with `(ArcLengthFourSecond.isUnit_ps W hR 2).pow _`. Use `set u : LetA O n := lA W ^ t * (algebraMap O (LetA O n) x₀ * Br.cst (α' * r)) with hu`. Establish `hu_mem : u ∈ W.AΔ` using `W.AΔ.mul_mem (W.AΔ.pow_mem ArcLengthFourSecond.lA_mem t) (W.AΔ.mul_mem (W.AΔ.algebraMap_mem x₀) (Br.cst_mem _))`. Use `set fa : W.EE := ((hUn.unit⁻¹ : W.EEˣ) : W.EE) * algebraMap (LetA O n) W.EE (letE c * 1 * u) with hfa`.

Establish `hfaD : algebraMap (LetA O n) W.EE (ps W 2 ^ wa) * fa = algebraMap (LetA O n) W.EE (letE c * 1 * u)`. Rewrite using `[hfa, ← mul_assoc, IsUnit.mul_val_inv hUn, one_mul]`. Use `set u₂ : LetA O n := -(lA W ^ e₄ * (algebraMap O (LetA O n) x₀ * Br.cst β)) with hu₂`. Establish `hu₂_mem : u₂ ∈ W.AΔ` using `W.AΔ.neg_mem (W.AΔ.mul_mem (W.AΔ.pow_mem ArcLengthFourSecond.lA_mem e₄) (W.AΔ.mul_mem (W.AΔ.algebraMap_mem x₀) (Br.cst_mem _)))`. Use `⟨fa, si, ⟨u, hu_mem, hfaD⟩, ⟨u₂, hu₂_mem, ?_⟩, ?_⟩` and prove the remaining obligations.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hfaD, ArcLengthFourSecond.lE_eq, ArcLengthFourSecond.lE_eq, IsScalarTower.algebraMap_apply O (LetA O n) W.EE x₀]`. Use `_ = algebraMap (LetA O n) W.EE (lA W ^ s * (letE c * 1 * u) - lA W ^ e₄ * (letE c * algebraMap O (LetA O n) x₀) * ps W 2 ^ wa) := by`. Simplify using `only [map_mul, map_sub]`. Use `_ = algebraMap (LetA O n) W.EE (letE c * (ps W 1 ^ Bn * ps W 0 ^ η) * u₂) := by`.

Use `congr 1`. Rewrite using `[hD, hu, hu₂]`. Take the linear combination `((letE c : LetA O n) * algebraMap O (LetA O n) x₀ * Br.cst (α' * r)) * hexp`. Use `Nat.lt_floor_add_one y` as an intermediate fact. Rewrite `this` using `[← hsi]`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem exists_fraction_in_frame [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    (W : LocWach PD LL O v n) (hcase : Formalism.MainNotions.LiftingTheory.CaseA W) (hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W)
    (hO : ∀ x : O, 0 ≤ v (algebraMap O LL x)) (hinj : Function.Injective (algebraMap O LL))
    (T : LocLat G Qp LL O) (hT : IsCrys PD T.ρ) (c : ZMod n) (wa Bn η s : ℕ) (hBn : 1 ≤ Bn) (x₀ : O) :
    ∃ (fa : W.EE) (si : ℕ), InFr W c 1 (ps W 2 ^ wa) fa ∧
      InFr W c (ps W 1 ^ Bn * ps W 0 ^ η) (ps W 2 ^ wa)
        (lE W s * fa - lE W (s - si) * (algebraMap (LetA O n) W.EE (letE c) * algebraMap O W.EE x₀)) ∧
      (wa : ℝ) - (Bn : ℝ) / PD.p - (η : ℝ) / (PD.p : ℝ) ^ 2 - 1 ≤ si := by
  haveI : Fact PD.p.Prime := ⟨PD.hp⟩
  obtain ⟨Br⟩ := exists_phiBridge W hcase hP9 T hT hO hinj
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hR := GS.ringData_of_caseA_of_p9 W hcase hP9
  set y : ℝ := (wa : ℝ) - (Bn : ℝ) / PD.p - (η : ℝ) / (PD.p : ℝ) ^ 2 with hy
  set si : ℕ := ⌊y⌋₊ with hsi
  have hk : eO (O := O) PD.p * si ≤
      ⌈(eO (O := O) PD.p : ℝ) * ((wa : ℝ) - Bn / PD.p - η / (PD.p : ℝ) ^ 2)⌉₊ := by
    rw [← hy]
    by_cases h0 : 0 ≤ y
    · have h1 : (si : ℝ) ≤ y := Nat.floor_le h0
      have h2 : ((eO (O := O) PD.p * si : ℕ) : ℝ) ≤ (eO (O := O) PD.p : ℝ) * y := by
        push_cast; exact mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)
      exact_mod_cast h2.trans (Nat.le_ceil _)
    · have : si = 0 := Nat.floor_eq_zero.mpr (by linarith)
      rw [this, mul_zero]; exact Nat.zero_le _
  have hmem := Br.P.c3b hϖ wa Bn η (Or.inl hBn) (eO (O := O) PD.p * si) hk
  have hspan := span_C_l_pow hϖ Br.P.hl0 si
  obtain ⟨r, hr⟩ : ∃ r : PowerSeries O,
      r * (PowerSeries.C ((PD.p : ℕ) : O)) ^ si = (PowerSeries.C ϖ) ^ (eO (O := O) PD.p * si) := by
    have : (PowerSeries.C ϖ : PowerSeries O) ^ (eO (O := O) PD.p * si) ∈
        Ideal.span {(PowerSeries.C ((PD.p : ℕ) : O) : PowerSeries O) ^ si} := by
      rw [hspan]; exact Ideal.subset_span rfl
    exact Ideal.mem_span_singleton'.mp this
  obtain ⟨α', β, hαβ⟩ := Ideal.mem_span_pair.mp hmem
  have hD : ps W 2 ^ wa = lA W ^ si * Br.cst (α' * r) + ps W 1 ^ Bn * ps W 0 ^ η * Br.cst β := by
    have e0 : ps W 0 = qA W := by simp [ps]
    have e2 : Br.cst (Br.P.p 2 ^ wa) =
        Br.cst ((α' * r) * PowerSeries.C ((PD.p : ℕ) : O) ^ si + β * (Br.P.p 1 ^ Bn * PowerSeries.X ^ η)) := by
      rw [← hαβ, ← hr]; congr 1; ring
    simp only [ArcLengthFourSecond.cst_add, Br.cst_mul, Br.cst_pow] at e2
    rw [← Br.ps_eq, ← Br.ps_eq, ← Br.qA_eq, ← Br.lA_eq, ← e0] at e2
    rw [e2, Br.cst_mul]; ring
  set e₄ := s - si with he₄
  set t := e₄ + si - s with ht
  have hexp : lA W ^ s * lA W ^ t = lA W ^ e₄ * lA W ^ si := by
    rw [← pow_add, ← pow_add]; congr 1; omega
  have hUn : IsUnit (algebraMap (LetA O n) W.EE (ps W 2 ^ wa)) := by
    rw [map_pow]; exact (ArcLengthFourSecond.isUnit_ps W hR 2).pow _
  set u : LetA O n := lA W ^ t * (algebraMap O (LetA O n) x₀ * Br.cst (α' * r)) with hu
  have hu_mem : u ∈ W.AΔ :=
    W.AΔ.mul_mem (W.AΔ.pow_mem ArcLengthFourSecond.lA_mem t) (W.AΔ.mul_mem (W.AΔ.algebraMap_mem x₀) (Br.cst_mem _))
  set fa : W.EE := ((hUn.unit⁻¹ : W.EEˣ) : W.EE) * algebraMap (LetA O n) W.EE (letE c * 1 * u) with hfa
  have hfaD : algebraMap (LetA O n) W.EE (ps W 2 ^ wa) * fa = algebraMap (LetA O n) W.EE (letE c * 1 * u) := by
    rw [hfa, ← mul_assoc, IsUnit.mul_val_inv hUn, one_mul]
  set u₂ : LetA O n := -(lA W ^ e₄ * (algebraMap O (LetA O n) x₀ * Br.cst β)) with hu₂
  have hu₂_mem : u₂ ∈ W.AΔ :=
    W.AΔ.neg_mem (W.AΔ.mul_mem (W.AΔ.pow_mem ArcLengthFourSecond.lA_mem e₄) (W.AΔ.mul_mem (W.AΔ.algebraMap_mem x₀) (Br.cst_mem _)))
  refine ⟨fa, si, ⟨u, hu_mem, hfaD⟩, ⟨u₂, hu₂_mem, ?_⟩, ?_⟩
  · calc algebraMap (LetA O n) W.EE (ps W 2 ^ wa) *
          (lE W s * fa - lE W e₄ * (algebraMap (LetA O n) W.EE (letE c) * algebraMap O W.EE x₀))
        = lE W s * (algebraMap (LetA O n) W.EE (ps W 2 ^ wa) * fa) -
            lE W e₄ * (algebraMap (LetA O n) W.EE (letE c) * algebraMap O W.EE x₀) *
              algebraMap (LetA O n) W.EE (ps W 2 ^ wa) := by ring
      _ = algebraMap (LetA O n) W.EE (lA W ^ s) * algebraMap (LetA O n) W.EE (letE c * 1 * u) -
            algebraMap (LetA O n) W.EE (lA W ^ e₄) * (algebraMap (LetA O n) W.EE (letE c) *
              algebraMap (LetA O n) W.EE (algebraMap O (LetA O n) x₀)) *
              algebraMap (LetA O n) W.EE (ps W 2 ^ wa) := by
          rw [hfaD, ArcLengthFourSecond.lE_eq, ArcLengthFourSecond.lE_eq, IsScalarTower.algebraMap_apply O (LetA O n) W.EE x₀]
      _ = algebraMap (LetA O n) W.EE (lA W ^ s * (letE c * 1 * u) -
            lA W ^ e₄ * (letE c * algebraMap O (LetA O n) x₀) * ps W 2 ^ wa) := by
          simp only [map_mul, map_sub]
      _ = algebraMap (LetA O n) W.EE (letE c * (ps W 1 ^ Bn * ps W 0 ^ η) * u₂) := by
          congr 1
          rw [hD, hu, hu₂]
          linear_combination ((letE c : LetA O n) * algebraMap O (LetA O n) x₀ * Br.cst (α' * r)) * hexp
  · have := Nat.lt_floor_add_one y
    rw [← hsi] at this
    linarith

end Formalism.MainNotions.N.FrobeniusPowerSeries
