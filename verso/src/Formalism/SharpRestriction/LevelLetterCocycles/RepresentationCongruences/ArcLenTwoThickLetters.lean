import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.HmaxLe
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.DenBound
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ExistsPhiBridge
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ImportsAlt

noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries.ArcLengthTwo

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.N.Ln17 PowerSeries

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

/- English proof (translation)
Use `set s := {d : ℕ | 1 ≤ d ∧ ¬ Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size (c - (d : ZMod n) + 1)} with hs`. Establish `hlen' : sInf s = 2` using `hlen`. Establish `hne : s.Nonempty`. Assume the negation of the conclusion as `h`. Rewrite `h` using `[Set.not_nonempty_iff_eq_empty]`.

Rewrite `hlen'` using `[h, Nat.sInf_empty]`. Evaluate the numerical expressions using `at hlen'`. Establish `h2 : 2 ∈ s` using `hlen' ▸ Nat.sInf_mem hne`. Establish `h1 : 1 ∉ s` using `fun h => by`. Use `Nat.sInf_le h` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Prove the components needed by the constructor for the conclusion. Assume the negation of the conclusion as `hT`. Apply `h1` to reduce the goal to its premises. Use `⟨le_rfl, ?_⟩` and prove the remaining obligations.

Simplify using `using hT`. Establish `h22` using `h2.2`. Use `h22 using 2` and compare the differences between its conclusion and the goal. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem arc_len_two_thick_letters [NeZero n] {b w S η : ℕ} {up : ZMod n → Bool} {size : ZMod n → ℕ} (c : ZMod n)
    (hlen : (arcOf b w S η up size).len c = 2) :
    Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size c ∧ ¬ Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size (c - 1) := by
  set s := {d : ℕ | 1 ≤ d ∧ ¬ Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size (c - (d : ZMod n) + 1)} with hs
  have hlen' : sInf s = 2 := hlen
  have hne : s.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    rw [h, Nat.sInf_empty] at hlen'
    norm_num at hlen'
  have h2 : 2 ∈ s := hlen' ▸ Nat.sInf_mem hne
  have h1 : 1 ∉ s := fun h => by
    have := Nat.sInf_le h
    omega
  constructor
  · by_contra hT
    apply h1
    refine ⟨le_rfl, ?_⟩
    simpa using hT
  · have h22 := h2.2
    convert h22 using 2
    push_cast
    ring

/- English proof (translation)
Take `⟨w₁, z, h1, h2, h3, h4, h5⟩` from `h`. Use `⟨w₁, z, h1, h2, h3, h4, ?_⟩` and prove the remaining obligations. Establish `he : lE W (e + k) * f = lE W e * (lE W k * f)`. Simplify using `only [lE, pow_add, mul_assoc]`. Establish `hfun : (fun kk => if kk = k₀ then lE W (e + k) * f else 0) = (fun kk => if kk = k₀ then lE W e * (lE W k * f) else 0)` using `funext fun kk => by rw [he]`.

Rewrite using `[hfun]`. Conclude with `h5`.
-/
theorem lifts_scale (W : LocWach PD LL O v n) (A : ArcP n) {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L)
    (c : ZMod n) {d : ℕ} (bb : Fin d → W.DD T₂) (sol : Fin d → ℕ → Fin d → LL) (k₀ : Fin d) {f : W.EE}
    {e k : ℕ} (h : LiftsAt W A F c bb sol k₀ (lE W k * f) e) : LiftsAt W A F c bb sol k₀ f (e + k) := by
  obtain ⟨w₁, z, h1, h2, h3, h4, h5⟩ := h
  refine ⟨w₁, z, h1, h2, h3, h4, ?_⟩
  have he : lE W (e + k) * f = lE W e * (lE W k * f) := by
    simp only [lE, pow_add, mul_assoc]
  have hfun : (fun kk => if kk = k₀ then lE W (e + k) * f else 0) =
      (fun kk => if kk = k₀ then lE W e * (lE W k * f) else 0) := funext fun kk => by rw [he]
  rw [hfun]
  exact h5

/- English proof (translation)
Simplify using `only [lE, lA, map_pow, map_natCast]`.
-/
theorem lE_alg (W : LocWach PD LL O v n) (k : ℕ) :
    lE W k = algebraMap (LetA O n) W.EE (lA W ^ k) := by
  simp only [lE, lA, map_pow, map_natCast]

/- English proof (translation)
The claim follows from `IsScalarTower.algebraMap_apply O (LetA O n) W.EE x`.
-/
theorem algO (W : LocWach PD LL O v n) (x : O) :
    algebraMap O W.EE x = algebraMap (LetA O n) W.EE (algebraMap O (LetA O n) x) := IsScalarTower.algebraMap_apply O (LetA O n) W.EE x

/- English proof (translation)
Use `haveI := Fact.mk PD.hp`. Use `set P := Br.P`. Establish `hp0 : P.p 0 = X` using `rfl`. Establish `hps : ∀ s k, ps W s ^ k = Br.cst (P.p s ^ k)`. Introduce `s k`.

Rewrite using `[Br.cst_pow, Br.ps_eq]`. Establish `h1 : (1 : LetA O n) = Br.cst 1` using `Br.cst_one.symm`. Rewrite `hf` using `[hps, h1]`. Rewrite `hx` using `[hps, hps, hp0]`. Take `⟨U₁, U₂, hU⟩` from `Br.inFr_const c hf hx`.

Take `⟨hd1, hd2⟩` from `den_bound P y Bq κ hy hBq x U₁ U₂ hU`. Use `set D := ⌈max 0 ((y : ℝ) - Bq / PD.p + 2 + Real.logb PD.p y)⌉₊ with hD`. Use `set de : ℕ := if PD.p * y < Bq then 0 else min D κ with hde`. Establish `hxd : ((PD.p : ℕ) : O) ^ (κ - de) ∣ x`. Rewrite using `[hde]`.

Use `split_ifs with hlt`. Simplify using `using hd2 hlt`. Establish `: κ - min D κ = κ - D` using `by omega`. Rewrite using `[this]`. Conclude with `hd1`.

Apply the tactic sequence `have hdeκ : de ≤ κ := by rw [hde]; split_ifs <;> omega`. Take `⟨x', hx'⟩` from `hxd`. Use `⟨de, x', ?_, ?_, ?_⟩` and prove the remaining obligations. Apply the tactic sequence `rw [hde]; split_ifs <;> omega`. Introduce `hlt`.

Rewrite using `[hde, if_pos hlt]`. Take `⟨u₁, hu₁, hfu⟩` from `hf`. Take `⟨F₁, hF₁⟩` from `Br.range u₁ hu₁ c`. Use `set G : PowerSeries O := C ((PD.p : ℕ) : O) ^ de * F₁ - P.p 1 ^ y * C x' with hG`. Establish `hletu : (letE c : LetA O n) * u₁ = letE c * Br.cst F₁`.

Use function extensionality and compare the values at `i`. Distinguish the cases in `hi : i = c`. Substitute `hi` using the available equality. Simplify using `[letE, hF₁, Formalism.MainNotions.N.FrobeniusPowerSeries.PhiBridge.cst]`. Simplify using `[letE, Pi.single_apply, hi]`.

Establish `e1 : (letE c : LetA O n) * Br.cst G = lA W ^ de * (letE c * Br.cst 1 * u₁) - Br.cst (P.p 1 ^ y) * (letE c * algebraMap O (LetA O n) x')`. Rewrite using `[Br.cst_one, mul_one, hletu, hG, Br.lA_eq, ← Br.cst_pow, ← Br.cst_C]`. Use function extensionality and compare the values at `i`. Simplify using `only [Formalism.MainNotions.N.FrobeniusPowerSeries.PhiBridge.cst, Pi.mul_apply, Pi.sub_apply, map_sub, map_mul, map_pow]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hkey : algebraMap (LetA O n) W.EE (Br.cst (P.p 1 ^ y)) * (lE W de * f - algebraMap (LetA O n) W.EE (letE c) * algebraMap O W.EE x') = algebraMap (LetA O n) W.EE (letE c * Br.cst G)`. Rewrite using `[algO, e1]`. Simplify using `only [map_sub, map_mul] at hfu ⊢`. Rewrite using `[← lE_alg]`. Take the linear combination `(lE W de) * hfu`.

Use `⟨⟨Br.cst G, Br.cst_mem G, ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[hps 1 y, hkey, mul_one]`. Establish `hscale : lE W κ * f - algebraMap (LetA O n) W.EE (letE c) * algebraMap O W.EE x = lE W (κ - de) * (lE W de * f - algebraMap (LetA O n) W.EE (letE c) * algebraMap O W.EE x')`. Establish `hj' : lE W κ = lE W (κ - de) * lE W de`. Unfold `lE`.

Rewrite using `[← pow_add, Nat.sub_add_cancel hdeκ]`. Rewrite using `[hx', map_mul, map_pow, map_natCast, hj']`. Unfold `lE`. Expand and normalize the polynomial expressions, which then agree. Take `⟨u₂, hu₂, hxu⟩` from `hx`.

Establish `hxu2 : algebraMap (LetA O n) W.EE (lA W ^ (κ - de) * (letE c * Br.cst G)) = algebraMap (LetA O n) W.EE (letE c * Br.cst (X ^ Bq) * u₂)`. Rewrite using `[map_mul, ← hkey, ← lE_alg, ← hxu, hscale]`. Expand and normalize the polynomial expressions, which then agree. Establish `hxc` using `congrFun (W.EE_inj hxu2) c`. Take `⟨F₂, hF₂⟩` from `Br.range u₂ hu₂ c`.

Establish `hιeq : Br.ι (C ((PD.p : ℕ) : O) ^ (κ - de) * G) = Br.ι (X ^ Bq * F₂)`. Establish `e2 : (lA W ^ (κ - de) * (letE c * Br.cst G) : LetA O n) c = Br.ι (C ((PD.p : ℕ) : O) ^ (κ - de) * G)`. Rewrite using `[Br.lA_eq, ← Br.cst_pow]`. Simplify using `[letE, Formalism.MainNotions.N.FrobeniusPowerSeries.PhiBridge.cst, map_mul]`. Establish `e3 : (letE c * Br.cst (X ^ Bq) * u₂ : LetA O n) c = Br.ι (X ^ Bq * F₂)`.

Simplify using `[letE, Formalism.MainNotions.N.FrobeniusPowerSeries.PhiBridge.cst, hF₂, map_mul]`. Rewrite using `[← e2, ← e3, hxc]`. Establish `hGB` using `Br.inj hιeq`. Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible O`. Take `⟨u, hu⟩` from `l_eq_unit_mul_pow hϖ P.hl0`.

Establish `hmem : C ϖ ^ (eO (O` using `O) PD.p * (κ - de)) * (C ((↑u : O) ^ (κ - de)) * G) ∈ Ideal.span {(X : O⟦X⟧) ^ Bq} := by`. Establish `: C ϖ ^ (eO (O` using `O) PD.p * (κ - de)) * (C ((↑u : O) ^ (κ - de)) * G) = X ^ Bq * F₂ := by`. Rewrite using `[← hGB, hu]`. Simplify using `only [map_mul, map_pow, mul_pow, ← pow_mul]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[this]`. Conclude with `Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)`. Establish `hmem2` using `Cont.mem_of_pow_mul_mem hϖ (ContPA.dist_X_pow (O := O) Bq).1 _ _ hmem`. Take `⟨U', hU'⟩` from `Ideal.mem_span_singleton'.mp hmem2`. Establish `hone : (C ((↑(u⁻¹) : O) ^ (κ - de)) : O⟦X⟧) * C ((↑u : O) ^ (κ - de)) = 1`.

Rewrite using `[← map_mul, ← mul_pow, Units.inv_mul, one_pow, map_one]`. Establish `hG2 : G = X ^ Bq * (C ((↑(u⁻¹) : O) ^ (κ - de)) * U')`. Take the linear combination `(-G) * hone + (-(C ((↑(u⁻¹) : O) ^ (κ - de)) : O⟦X⟧)) * hU'`. Use `⟨Br.cst (C ((↑(u⁻¹) : O) ^ (κ - de)) * U'), Br.cst_mem _, ?_⟩` and prove the remaining obligations. Rewrite using `[hps 1 y, hps 0 Bq, hp0, hkey, hG2, Br.cst_mul, mul_assoc]`.
-/
theorem den_step [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    (W : LocWach PD LL O v n) (Br : Formalism.MainNotions.N.FrobeniusPowerSeries.PhiBridge W) (c : ZMod n) (y Bq κ : ℕ)
    (hy : 1 ≤ y) (hBq : 1 ≤ Bq) (f : W.EE) (x : O)
    (hf : InFr W c 1 (ps W 1 ^ y) f)
    (hx : InFr W c (ps W 0 ^ Bq) (ps W 1 ^ y)
      (lE W κ * f - algebraMap (LetA O n) W.EE (letE c) * algebraMap O W.EE x)) :
    ∃ (de : ℕ) (x' : O), de ≤ ⌈max 0 ((y : ℝ) - Bq / PD.p + 2 + Real.logb PD.p y)⌉₊ ∧
      (PD.p * y < Bq → de = 0) ∧
      InFr W c 1 (ps W 1 ^ y) (lE W de * f - algebraMap (LetA O n) W.EE (letE c) * algebraMap O W.EE x') ∧
      InFr W c (ps W 0 ^ Bq) (ps W 1 ^ y)
        (lE W de * f - algebraMap (LetA O n) W.EE (letE c) * algebraMap O W.EE x') := by
  haveI := Fact.mk PD.hp
  set P := Br.P
  have hp0 : P.p 0 = X := rfl
  have hps : ∀ s k, ps W s ^ k = Br.cst (P.p s ^ k) := by
    intro s k; rw [Br.cst_pow, Br.ps_eq]
  have h1 : (1 : LetA O n) = Br.cst 1 := Br.cst_one.symm
  rw [hps, h1] at hf
  rw [hps, hps, hp0] at hx
  obtain ⟨U₁, U₂, hU⟩ := Br.inFr_const c hf hx
  obtain ⟨hd1, hd2⟩ := den_bound P y Bq κ hy hBq x U₁ U₂ hU
  set D := ⌈max 0 ((y : ℝ) - Bq / PD.p + 2 + Real.logb PD.p y)⌉₊ with hD
  set de : ℕ := if PD.p * y < Bq then 0 else min D κ with hde
  have hxd : ((PD.p : ℕ) : O) ^ (κ - de) ∣ x := by
    rw [hde]; split_ifs with hlt
    · simpa using hd2 hlt
    · have : κ - min D κ = κ - D := by omega
      rw [this]; exact hd1
  have hdeκ : de ≤ κ := by rw [hde]; split_ifs <;> omega
  obtain ⟨x', hx'⟩ := hxd
  refine ⟨de, x', ?_, ?_, ?_⟩
  · rw [hde]; split_ifs <;> omega
  · intro hlt; rw [hde, if_pos hlt]
  obtain ⟨u₁, hu₁, hfu⟩ := hf
  obtain ⟨F₁, hF₁⟩ := Br.range u₁ hu₁ c
  set G : PowerSeries O := C ((PD.p : ℕ) : O) ^ de * F₁ - P.p 1 ^ y * C x' with hG
  have hletu : (letE c : LetA O n) * u₁ = letE c * Br.cst F₁ := by
    funext i
    by_cases hi : i = c
    · subst hi; simp [letE, hF₁, Formalism.MainNotions.N.FrobeniusPowerSeries.PhiBridge.cst]
    · simp [letE, Pi.single_apply, hi]
  have e1 : (letE c : LetA O n) * Br.cst G =
      lA W ^ de * (letE c * Br.cst 1 * u₁) - Br.cst (P.p 1 ^ y) * (letE c * algebraMap O (LetA O n) x') := by
    rw [Br.cst_one, mul_one, hletu, hG, Br.lA_eq, ← Br.cst_pow, ← Br.cst_C]
    funext i
    simp only [Formalism.MainNotions.N.FrobeniusPowerSeries.PhiBridge.cst, Pi.mul_apply, Pi.sub_apply, map_sub, map_mul, map_pow]
    ring
  have hkey : algebraMap (LetA O n) W.EE (Br.cst (P.p 1 ^ y)) *
      (lE W de * f - algebraMap (LetA O n) W.EE (letE c) * algebraMap O W.EE x') =
      algebraMap (LetA O n) W.EE (letE c * Br.cst G) := by
    rw [algO, e1]
    simp only [map_sub, map_mul] at hfu ⊢
    rw [← lE_alg]
    linear_combination (lE W de) * hfu
  refine ⟨⟨Br.cst G, Br.cst_mem G, ?_⟩, ?_⟩
  · rw [hps 1 y, hkey, mul_one]
  have hscale : lE W κ * f - algebraMap (LetA O n) W.EE (letE c) * algebraMap O W.EE x =
      lE W (κ - de) * (lE W de * f - algebraMap (LetA O n) W.EE (letE c) * algebraMap O W.EE x') := by
    have hj' : lE W κ = lE W (κ - de) * lE W de := by
      unfold lE; rw [← pow_add, Nat.sub_add_cancel hdeκ]
    rw [hx', map_mul, map_pow, map_natCast, hj']
    unfold lE
    ring
  obtain ⟨u₂, hu₂, hxu⟩ := hx
  have hxu2 : algebraMap (LetA O n) W.EE (lA W ^ (κ - de) * (letE c * Br.cst G)) =
      algebraMap (LetA O n) W.EE (letE c * Br.cst (X ^ Bq) * u₂) := by
    rw [map_mul, ← hkey, ← lE_alg, ← hxu, hscale]
    ring
  have hxc := congrFun (W.EE_inj hxu2) c
  obtain ⟨F₂, hF₂⟩ := Br.range u₂ hu₂ c
  have hιeq : Br.ι (C ((PD.p : ℕ) : O) ^ (κ - de) * G) = Br.ι (X ^ Bq * F₂) := by
    have e2 : (lA W ^ (κ - de) * (letE c * Br.cst G) : LetA O n) c = Br.ι (C ((PD.p : ℕ) : O) ^ (κ - de) * G) := by
      rw [Br.lA_eq, ← Br.cst_pow]
      simp [letE, Formalism.MainNotions.N.FrobeniusPowerSeries.PhiBridge.cst, map_mul]
    have e3 : (letE c * Br.cst (X ^ Bq) * u₂ : LetA O n) c = Br.ι (X ^ Bq * F₂) := by
      simp [letE, Formalism.MainNotions.N.FrobeniusPowerSeries.PhiBridge.cst, hF₂, map_mul]
    rw [← e2, ← e3, hxc]
  have hGB := Br.inj hιeq
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨u, hu⟩ := l_eq_unit_mul_pow hϖ P.hl0
  have hmem : C ϖ ^ (eO (O := O) PD.p * (κ - de)) * (C ((↑u : O) ^ (κ - de)) * G) ∈
      Ideal.span {(X : O⟦X⟧) ^ Bq} := by
    have : C ϖ ^ (eO (O := O) PD.p * (κ - de)) * (C ((↑u : O) ^ (κ - de)) * G) = X ^ Bq * F₂ := by
      rw [← hGB, hu]
      simp only [map_mul, map_pow, mul_pow, ← pow_mul]
      ring
    rw [this]; exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  have hmem2 := Cont.mem_of_pow_mul_mem hϖ (ContPA.dist_X_pow (O := O) Bq).1 _ _ hmem
  obtain ⟨U', hU'⟩ := Ideal.mem_span_singleton'.mp hmem2
  have hone : (C ((↑(u⁻¹) : O) ^ (κ - de)) : O⟦X⟧) * C ((↑u : O) ^ (κ - de)) = 1 := by
    rw [← map_mul, ← mul_pow, Units.inv_mul, one_pow, map_one]
  have hG2 : G = X ^ Bq * (C ((↑(u⁻¹) : O) ^ (κ - de)) * U') := by
    linear_combination (-G) * hone + (-(C ((↑(u⁻¹) : O) ^ (κ - de)) : O⟦X⟧)) * hU'
  refine ⟨Br.cst (C ((↑(u⁻¹) : O) ^ (κ - de)) * U'), Br.cst_mem _, ?_⟩
  rw [hps 1 y, hps 0 Bq, hp0, hkey, hG2, Br.cst_mul, mul_assoc]

end Formalism.MainNotions.N.FrobeniusPowerSeries.ArcLengthTwo
