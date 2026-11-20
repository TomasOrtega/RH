import Formalism.SharpRestriction.LevelLetterCocycles.FilCrisTriv
import Formalism.SharpRestriction.LevelLetterCocycles.MembershipCriterionOfLevelZero
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.FrobeniusUniformizerPowDvd

noncomputable section

open Classical

namespace Formalism.MainNotions.UnusedSlot80.SplitP

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.WachCoordinates.Br Formalism.MainNotions.ArcLiftingSetup

/- English proof (translation)
Establish `e1 : ∑ j, (∑ k, a k * o k j) • (l ^ κ • Z j) = ∑ k, a k • (l ^ κ • ∑ j, o k j • Z j)`. Simplify using `only [Finset.sum_smul, Finset.smul_sum]`. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by module`. Use `set Yv : Fin d → M := fun k => ∑ j, o k j • Z j with hYv`.

Establish `e2 : ∑ k, a k • (l ^ K • (l ^ κY • X k - l ^ κ • Yv k)) = l ^ K • l ^ κY • ∑ k, a k • X k - l ^ K • ∑ k, a k • (l ^ κ • Yv k)`. Rewrite using `[Finset.smul_sum, Finset.smul_sum, Finset.smul_sum, ← Finset.sum_sub_distrib]`. Conclude with `Finset.sum_congr rfl fun k _ => by module`. Rewrite using `[e1, e2]`. Use `module`.
-/
theorem lin_map {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] {d dY : ℕ} (l Λ : R) (κ κY κ' K : ℕ)
    (u : M) (X : Fin d → M) (Z : Fin dY → M) (a : Fin d → R) (o : Fin d → Fin dY → R) :
    l ^ (κ' + K) • (l ^ (κ + κY) • Λ • u - ∑ j, (∑ k, a k * o k j) • (l ^ κ • Z j)) =
      l ^ K • l ^ κY • (l ^ κ' • (l ^ κ • Λ • u - ∑ k, a k • X k)) +
        l ^ κ' • ∑ k, a k • (l ^ K • (l ^ κY • X k - l ^ κ • ∑ j, o k j • Z j)) := by
  have e1 : ∑ j, (∑ k, a k * o k j) • (l ^ κ • Z j) = ∑ k, a k • (l ^ κ • ∑ j, o k j • Z j) := by
    simp only [Finset.sum_smul, Finset.smul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by module
  set Yv : Fin d → M := fun k => ∑ j, o k j • Z j with hYv
  have e2 : ∑ k, a k • (l ^ K • (l ^ κY • X k - l ^ κ • Yv k)) =
      l ^ K • l ^ κY • ∑ k, a k • X k - l ^ K • ∑ k, a k • (l ^ κ • Yv k) := by
    rw [Finset.smul_sum, Finset.smul_sum, Finset.smul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => by module
  rw [e1, e2]
  module

/- English proof (translation)
Use `module`.
-/
theorem linear_identity_head_difference {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (l π : R) (κ κY : ℕ)
    (S E U SY : M) :
    l ^ κY • (l ^ κ • (S + π • E) + π • U) - l ^ κ • (l ^ κY • S + π • SY) =
      π • (l ^ (κY + κ) • E + l ^ κY • U - l ^ κ • SY) := by
  module

/- English proof (translation)
Use `module`.
-/
theorem linear_identity_tail_difference {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (l π : R) (κ κY M' : ℕ)
    (U X S Z : M) :
    (l ^ κY • (U + π ^ M' • X) - l ^ κ • (S + π ^ M' • Z)) - (l ^ κY • U - l ^ κ • S) =
      π ^ M' • (l ^ κY • X - l ^ κ • Z) := by
  module

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

/- English proof (translation)
Take `⟨y, hy, rfl⟩` from `h`. Establish `hy0 : ∀ m, y 0 m = if m = k then ((PD.p : ℕ) : O) ^ κ else 0`. Introduce `m`. Apply `hinj` to reduce the goal to its premises. Rewrite using `[hy 0 hM m, hsol0 k]`.

Distinguish the cases in `hm : m = k`. Substitute `hm` using the available equality. Simplify using the standard rewrite rules. Simplify using `[hm, Pi.single_apply]`. Take `⟨M', rfl⟩ : ∃ M', M = M' + 1` from `⟨M - 1, by omega⟩`.

Use `⟨∑ r ∈ Finset.range M', W.π₀ ^ r • Formalism.MainNotions.LiftingTheory.vecB W T b (y (r + 1)), Formalism.MainNotions.UnusedSlot80.Relay2.InNΔi_sum W T c _ _ fun r _ => Formalism.MainNotions.UnusedSlot80.Relay2.InNΔi_smul W T c (W.AΔ.pow_mem hπ r) (Formalism.MainNotions.UnusedSlot …` and prove the remaining obligations. Rewrite using `[Finset.sum_range_succ', pow_zero, one_smul, add_comm, Finset.smul_sum]`. Use `congr 1`. Rewrite using `[LevC.lA_smul_eq]`. Unfold `Formalism.MainNotions.LiftingTheory.vecB`.

Simplify using `only [hy0, ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]`. Use `Finset.sum_congr rfl fun r _ => ?_` and prove the remaining obligations. Rewrite using `[smul_smul, ← pow_succ']`.
-/
theorem horTr_split (hinj : Function.Injective (algebraMap O LL)) (T : LocLat G Qp LL O) (c : ZMod n)
    {d : ℕ} (b : Fin d → W.DD T) (hb : ∀ m, Formalism.MainNotions.LiftingTheory.InNΔi W T c (b m)) (hπ : W.π₀ ∈ W.AΔ)
    (sol : Fin d → ℕ → Fin d → LL) (hsol0 : ∀ k, sol k 0 = Pi.single k 1) (M κ : ℕ) (hM : 1 ≤ M) (k : Fin d)
    {H : W.DD T} (h : IsHorTr W T b sol M κ k H) :
    ∃ S, Formalism.MainNotions.LiftingTheory.InNΔi W T c S ∧ H = lA W ^ κ • b k + W.π₀ • S := by
  obtain ⟨y, hy, rfl⟩ := h
  have hy0 : ∀ m, y 0 m = if m = k then ((PD.p : ℕ) : O) ^ κ else 0 := by
    intro m
    apply hinj
    rw [hy 0 hM m, hsol0 k]
    by_cases hm : m = k
    · subst hm; simp
    · simp [hm, Pi.single_apply]
  obtain ⟨M', rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
  refine ⟨∑ r ∈ Finset.range M', W.π₀ ^ r • Formalism.MainNotions.LiftingTheory.vecB W T b (y (r + 1)),
    Formalism.MainNotions.UnusedSlot80.Relay2.InNΔi_sum W T c _ _ fun r _ =>
      Formalism.MainNotions.UnusedSlot80.Relay2.InNΔi_smul W T c (W.AΔ.pow_mem hπ r)
        (Formalism.MainNotions.UnusedSlot80.Relay2.InNΔi_sum W T c _ _ fun m _ => Formalism.MainNotions.UnusedSlot80.Relay2.InNΔi_osmul W T c _ (hb m)), ?_⟩
  rw [Finset.sum_range_succ', pow_zero, one_smul, add_comm, Finset.smul_sum]
  congr 1
  · rw [LevC.lA_smul_eq]
    unfold Formalism.MainNotions.LiftingTheory.vecB
    simp only [hy0, ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  · refine Finset.sum_congr rfl fun r _ => ?_
    rw [smul_smul, ← pow_succ']

/- English proof (translation)
Take `⟨y, hy, rfl⟩` from `h`. Take `⟨x, hx, hxe⟩` from `(hb.2 k).1 M κ y hy`. Use `⟨x, hx, ?_⟩` and prove the remaining obligations. Rewrite using `[← hxe, smul_zero, sub_zero]`.
-/
theorem horTr_γ (T : LocLat G Qp LL O) (c : ZMod n) {d : ℕ} (b : Fin d → W.DD T)
    (sol : Fin d → ℕ → Fin d → LL) (hb : IsHor W T c b sol) (M κ : ℕ) (k : Fin d) {H : W.DD T}
    (h : IsHorTr W T b sol M κ k H) :
    ∃ x, Formalism.MainNotions.LiftingTheory.InNΔi W T c x ∧ W.γ T H - H = W.π₀ ^ M • x := by
  obtain ⟨y, hy, rfl⟩ := h
  obtain ⟨x, hx, hxe⟩ := (hb.2 k).1 M κ y hy
  refine ⟨x, hx, ?_⟩
  rw [← hxe, smul_zero, sub_zero]

variable [IsDomain O]

/- English proof (translation)
Rewrite using `[LevC.lA_smul_eq, map_smul, ← LevC.lA_smul_eq]`.
-/
theorem γ_lA (T : LocLat G Qp LL O) (t : ℕ) (z : W.DD T) : W.γ T (lA W ^ t • z) = lA W ^ t • W.γ T z := by
  rw [LevC.lA_smul_eq, map_smul, ← LevC.lA_smul_eq]

variable [NeZero n]

/- English proof (translation)
Establish `hx` using `Formalism.MainNotions.UnusedSlot80.Relay2.InNΔi_map W ι h2 hY c' (hb.1 k)`. Take `⟨m, ⟨hm, hmx⟩, -⟩` from `hbY.2 _ hx`. Use `⟨m, hm, hmx, ?_⟩` and prove the remaining obligations. Use `set o : Fin dY → O := fun j => PowerSeries.constantCoeff (m j c') with ho`. Establish `hdv : ∀ j, ∃ g ∈ W.AΔ, m j - letE c' * algebraMap O (LetA O n) (o j) = W.π₀ * g`.

Introduce `j`. Use `Formalism.MainNotions.N.Pv.LocalLengthBound.frobenius_uniformizer_pow_dvd (c := c') hR (W.AΔ.sub_mem (hm j).1 (W.AΔ.mul_mem (Formalism.MainNotions.UnusedSlot80.SatPW.letE_mem_AΔ W c') (W.AΔ.algebraMap_mem _))) ?_ ?_` and prove the remaining obligations. Rewrite using `[mul_sub, (hm j).2, ← mul_assoc, Formalism.MainNotions.N.Pv.LocalLengthBound.letE_sq]`. Use `Formalism.MainNotions.UnusedSlot80.ArcF.ev_apply c' (m j - letE c' * algebraMap O (LetA O n) (o j))` as an intermediate fact. Rewrite using `[← this, map_sub, map_mul, Formalism.MainNotions.UnusedSlot80.ArcF.ev_letE, Formalism.MainNotions.UnusedSlot80.ArcF.ev_alg, one_mul, Formalism.MainNotions.UnusedSlot80.ArcF.ev_apply, sub_self]`.

Use `choose g hg hge using hdv`. Establish `hbl : ∀ j, (letE c' : LetA O n) • bY j = bY j` using `fun j => Formalism.MainNotions.UnusedSlot80.Relay2.InNΔi_letter W Y c' (hbY.1 j)`. Use `⟨∑ j, g j • bY j, Formalism.MainNotions.UnusedSlot80.Relay2.InNΔi_sum W Y c' _ _ fun j _ => Formalism.MainNotions.UnusedSlot80.Relay2.InNΔi_smul W Y c' (hg j) (hbY.1 j), ?_⟩` and prove the remaining obligations. Rewrite using `[hmx, Finset.smul_sum, ← Finset.sum_sub_distrib]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Establish `e1 : o j • bY j = (letE c' * algebraMap O (LetA O n) (o j)) • bY j`. Rewrite using `[mul_comm, mul_smul, hbl j, algebraMap_smul]`. Rewrite using `[e1, ← sub_smul, hge j, mul_smul]`.
-/
theorem frame_const (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) {T₂ Y : LocLat G Qp LL O} (ι : LatHom T₂.L Y.L)
    (h2 : IsCrys PD T₂.ρ) (hY : IsCrys PD Y.ρ) (c' : ZMod n) {d dY : ℕ} (b : Fin d → W.DD T₂)
    (hb : Formalism.MainNotions.LiftingTheory.IsFrameΔ W T₂ c' b) (bY : Fin dY → W.DD Y) (hbY : Formalism.MainNotions.LiftingTheory.IsFrameΔ W Y c' bY)
    (k : Fin d) :
    ∃ (m : Fin dY → LetA O n), (∀ j, m j ∈ W.AΔ ∧ letE c' * m j = m j) ∧
      W.map ι (b k) = ∑ j, m j • bY j ∧
      ∃ E, Formalism.MainNotions.LiftingTheory.InNΔi W Y c' E ∧
        W.map ι (b k) - ∑ j, PowerSeries.constantCoeff (m j c') • bY j = W.π₀ • E := by
  have hx := Formalism.MainNotions.UnusedSlot80.Relay2.InNΔi_map W ι h2 hY c' (hb.1 k)
  obtain ⟨m, ⟨hm, hmx⟩, -⟩ := hbY.2 _ hx
  refine ⟨m, hm, hmx, ?_⟩
  set o : Fin dY → O := fun j => PowerSeries.constantCoeff (m j c') with ho
  have hdv : ∀ j, ∃ g ∈ W.AΔ, m j - letE c' * algebraMap O (LetA O n) (o j) = W.π₀ * g := by
    intro j
    refine Formalism.MainNotions.N.Pv.LocalLengthBound.frobenius_uniformizer_pow_dvd (c := c') hR (W.AΔ.sub_mem (hm j).1
      (W.AΔ.mul_mem (Formalism.MainNotions.UnusedSlot80.SatPW.letE_mem_AΔ W c') (W.AΔ.algebraMap_mem _))) ?_ ?_
    · rw [mul_sub, (hm j).2, ← mul_assoc, Formalism.MainNotions.N.Pv.LocalLengthBound.letE_sq]
    · have := Formalism.MainNotions.UnusedSlot80.ArcF.ev_apply c' (m j - letE c' * algebraMap O (LetA O n) (o j))
      rw [← this, map_sub, map_mul, Formalism.MainNotions.UnusedSlot80.ArcF.ev_letE, Formalism.MainNotions.UnusedSlot80.ArcF.ev_alg, one_mul,
        Formalism.MainNotions.UnusedSlot80.ArcF.ev_apply, sub_self]
  choose g hg hge using hdv
  have hbl : ∀ j, (letE c' : LetA O n) • bY j = bY j := fun j =>
    Formalism.MainNotions.UnusedSlot80.Relay2.InNΔi_letter W Y c' (hbY.1 j)
  refine ⟨∑ j, g j • bY j, Formalism.MainNotions.UnusedSlot80.Relay2.InNΔi_sum W Y c' _ _ fun j _ =>
    Formalism.MainNotions.UnusedSlot80.Relay2.InNΔi_smul W Y c' (hg j) (hbY.1 j), ?_⟩
  rw [hmx, Finset.smul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  have e1 : o j • bY j = (letE c' * algebraMap O (LetA O n) (o j)) • bY j := by
    rw [mul_comm, mul_smul, hbl j, algebraMap_smul]
  rw [e1, ← sub_smul, hge j, mul_smul]

/- English proof (translation)
Establish `hM : 1 ≤ A.M PD.p` using `by unfold ArcP.M; exact Nat.le_add_left 1 _`. Establish `hπ` using `C.hR.1`. Take `⟨S, hS, hSe⟩` from `horTr_split W C.hinj T₂ c' b (fun m => hb.1.1 m) hπ sol (fun k => (hb.2 k).2) _ κ hM k (hHh k)`. Establish `hSY : ∀ j, ∃ S, Formalism.MainNotions.LiftingTheory.InNΔi W Y c' S ∧ HhY j = lA W ^ κY • bY j + W.π₀ • S` using `fun j => horTr_split W C.hinj Y c' bY (fun m => hbY.1.1 m) hπ solY (fun k => (hbY.2 k).2) _ κY hM j (hHhY j)`. Use `choose SY hSY hSYe using hSY`.

Take `⟨E, hE, hEe⟩` from `ho k`. Take `⟨x, hx, hxe⟩` from `horTr_γ W T₂ c' b sol hb _ κ k (hHh k)`. Establish `hxY : ∀ j, ∃ x, Formalism.MainNotions.LiftingTheory.InNΔi W Y c' x ∧ W.γ Y (HhY j) - HhY j = W.π₀ ^ (A.M PD.p) • x` using `fun j => horTr_γ W Y c' bY solY hbY _ κY j (hHhY j)`. Use `choose xY hxY hxYe using hxY`. Use `set D : W.DD Y := lA W ^ κY • W.map ι (Hh k) - lA W ^ κ • ∑ j, o k j • HhY j with hD`.

Establish `hmapS` using `Formalism.MainNotions.UnusedSlot80.Relay2.InNΔi_map W ι h2 hY c' hS`. Establish `hmapx` using `Formalism.MainNotions.UnusedSlot80.Relay2.InNΔi_map W ι h2 hY c' hx`. Establish `hD1 : ∃ E', Formalism.MainNotions.LiftingTheory.InNΔi W Y c' E' ∧ D = W.π₀ • E'`. Use `⟨lA W ^ (κY + κ) • E + lA W ^ κY • W.map ι S - lA W ^ κ • ∑ j, o k j • SY j, Formalism.MainNotions.UnusedSlot80.Relay2.InNΔi_sub W Y c' (Formalism.MainNotions.UnusedSlot80.Relay2.InNΔi_add W Y c' (Formalism.MainNotions.UnusedSlot80.Relay2.InNΔi_lsmul W Y c' _ hE) (Formalism.MainN …` and prove the remaining obligations. Establish `hmk : W.map ι (b k) = ∑ j, o k j • bY j + W.π₀ • E` using `by rw [← hEe]; abel`.

Establish `s1 : ∑ j, o k j • (lA W ^ κY • bY j) = lA W ^ κY • ∑ j, o k j • bY j`. Rewrite using `[Finset.smul_sum]`. Conclude with `Finset.sum_congr rfl fun j _ => smul_comm _ _ _`. Establish `s2 : ∑ j, o k j • (W.π₀ • SY j) = W.π₀ • ∑ j, o k j • SY j`. Rewrite using `[Finset.smul_sum]`.

Conclude with `Finset.sum_congr rfl fun j _ => smul_comm _ _ _`. Establish `s12 : ∑ j, o k j • HhY j = lA W ^ κY • ∑ j, o k j • bY j + W.π₀ • ∑ j, o k j • SY j`. Simplify using `only [hSYe, smul_add, Finset.sum_add_distrib]`. Rewrite using `[s1, s2]`. Rewrite using `[hD, hSe, map_add, Formalism.MainNotions.UnusedSlot80.Relay2.mapA_smul, Formalism.MainNotions.UnusedSlot80.Relay2.mapA_smul, hmk, s12]`.

Conclude with `linear_identity_head_difference _ _ _ _ _ _ _ _`. Establish `hγT` using `sub_eq_iff_eq_add'.1 hxe`. Establish `hγι : W.γ Y (W.map ι (Hh k)) = W.map ι (Hh k) + W.π₀ ^ (A.M PD.p) • W.map ι x`. Rewrite using `[show W.γ Y (W.map ι (Hh k)) = W.map ι (W.γ T₂ (Hh k)) from (W.map_γ ι W.gam (Hh k)).symm, hγT, map_add, Formalism.MainNotions.UnusedSlot80.Relay2.mapA_smul]`. Establish `hγY : ∀ j, W.γ Y (HhY j) = HhY j + W.π₀ ^ (A.M PD.p) • xY j` using `fun j => sub_eq_iff_eq_add'.1 (hxYe j)`.

Establish `hD2 : ∃ z, Formalism.MainNotions.LiftingTheory.InNΔi W Y c' z ∧ W.γ Y D - D = W.π₀ ^ (A.M PD.p) • z`. Use `⟨lA W ^ κY • W.map ι x - lA W ^ κ • ∑ j, o k j • xY j, Formalism.MainNotions.UnusedSlot80.Relay2.InNΔi_sub W Y c' (Formalism.MainNotions.UnusedSlot80.Relay2.InNΔi_lsmul W Y c' _ hmapx) (Formalism.MainNotions.UnusedSlot80.Relay2.InNΔi_lsmul W Y c' _ (Formalism.MainNotions.UnusedSl …` and prove the remaining obligations. Establish `s3 : ∑ j, o k j • (W.π₀ ^ (A.M PD.p) • xY j) = W.π₀ ^ (A.M PD.p) • ∑ j, o k j • xY j`. Rewrite using `[Finset.smul_sum]`. Conclude with `Finset.sum_congr rfl fun j _ => smul_comm _ _ _`.

Establish `s4 : W.γ Y (∑ j, o k j • HhY j) = ∑ j, o k j • HhY j + W.π₀ ^ (A.M PD.p) • ∑ j, o k j • xY j`. Simplify using `only [map_sum, map_smul, hγY, smul_add, Finset.sum_add_distrib]`. Rewrite using `[s3]`. Rewrite using `[hD, map_sub, γ_lA, γ_lA, hγι, s4]`. Conclude with `linear_identity_tail_difference _ _ _ _ _ _ _ _ _`.

Take `⟨K, x', hx', hK⟩` from `Formalism.MainNotions.UnusedSlot80.Relay2.formal_unique W Y c' C.hinj C.hO2 hπ C.hR.2.2.1 (C.hH C.hCA Y hY c').1 (C.hH C.hCA Y hY c').2.1 (A.M PD.p) D hD1 hD2`. Take `⟨ν, hν, hνe⟩` from `LevC.yM_gen W C.hTr C.hCA hπ C.h5p A hA a e`. Use `⟨K, ν • ((W.φD Y) ^ e) x', Formalism.MainNotions.UnusedSlot80.Relay2.Pp_gen W Y c' e hν hx', ?_⟩` and prove the remaining obligations. Rewrite using `[← Formalism.MainNotions.UnusedSlot80.Relay2.φpow_lsmul, hK, Formalism.MainNotions.UnusedSlot80.Relay2.φpow_smul, map_pow, hνe, mul_smul]`.
-/
theorem hor_diff (C : LevC.Ctx W) {T₂ Y : LocLat G Qp LL O} (ι : LatHom T₂.L Y.L)
    (h2 : IsCrys PD T₂.ρ) (hY : IsCrys PD Y.ρ) (A : ArcP n) (hA : A.OK) (a : ZMod n) (c' : ZMod n) (e : ℕ)
    {d dY : ℕ} (b : Fin d → W.DD T₂) (sol : Fin d → ℕ → Fin d → LL) (hb : IsHor W T₂ c' b sol)
    (bY : Fin dY → W.DD Y) (solY : Fin dY → ℕ → Fin dY → LL) (hbY : IsHor W Y c' bY solY)
    (κ κY : ℕ) (Hh : Fin d → W.DD T₂) (HhY : Fin dY → W.DD Y)
    (hHh : ∀ k, IsHorTr W T₂ b sol (A.M PD.p) κ k (Hh k)) (hHhY : ∀ j, IsHorTr W Y bY solY (A.M PD.p) κY j (HhY j))
    (o : Fin d → Fin dY → O)
    (ho : ∀ k, ∃ E, Formalism.MainNotions.LiftingTheory.InNΔi W Y c' E ∧ W.map ι (b k) - ∑ j, o k j • bY j = W.π₀ • E) (k : Fin d) :
    ∃ K : ℕ, InFP W Y c' e (W.π₀ * abelian₂ W A a e ^ 2)
      (lA W ^ K • ((W.φD Y) ^ e) (lA W ^ κY • W.map ι (Hh k) - lA W ^ κ • ∑ j, o k j • HhY j)) := by
  have hM : 1 ≤ A.M PD.p := by unfold ArcP.M; exact Nat.le_add_left 1 _
  have hπ := C.hR.1
  obtain ⟨S, hS, hSe⟩ := horTr_split W C.hinj T₂ c' b (fun m => hb.1.1 m) hπ sol (fun k => (hb.2 k).2) _ κ hM k (hHh k)
  have hSY : ∀ j, ∃ S, Formalism.MainNotions.LiftingTheory.InNΔi W Y c' S ∧ HhY j = lA W ^ κY • bY j + W.π₀ • S := fun j =>
    horTr_split W C.hinj Y c' bY (fun m => hbY.1.1 m) hπ solY (fun k => (hbY.2 k).2) _ κY hM j (hHhY j)
  choose SY hSY hSYe using hSY
  obtain ⟨E, hE, hEe⟩ := ho k
  obtain ⟨x, hx, hxe⟩ := horTr_γ W T₂ c' b sol hb _ κ k (hHh k)
  have hxY : ∀ j, ∃ x, Formalism.MainNotions.LiftingTheory.InNΔi W Y c' x ∧ W.γ Y (HhY j) - HhY j = W.π₀ ^ (A.M PD.p) • x := fun j =>
    horTr_γ W Y c' bY solY hbY _ κY j (hHhY j)
  choose xY hxY hxYe using hxY
  set D : W.DD Y := lA W ^ κY • W.map ι (Hh k) - lA W ^ κ • ∑ j, o k j • HhY j with hD
  have hmapS := Formalism.MainNotions.UnusedSlot80.Relay2.InNΔi_map W ι h2 hY c' hS
  have hmapx := Formalism.MainNotions.UnusedSlot80.Relay2.InNΔi_map W ι h2 hY c' hx

  have hD1 : ∃ E', Formalism.MainNotions.LiftingTheory.InNΔi W Y c' E' ∧ D = W.π₀ • E' := by
    refine ⟨lA W ^ (κY + κ) • E + lA W ^ κY • W.map ι S - lA W ^ κ • ∑ j, o k j • SY j,
      Formalism.MainNotions.UnusedSlot80.Relay2.InNΔi_sub W Y c'
        (Formalism.MainNotions.UnusedSlot80.Relay2.InNΔi_add W Y c' (Formalism.MainNotions.UnusedSlot80.Relay2.InNΔi_lsmul W Y c' _ hE)
          (Formalism.MainNotions.UnusedSlot80.Relay2.InNΔi_lsmul W Y c' _ hmapS))
        (Formalism.MainNotions.UnusedSlot80.Relay2.InNΔi_lsmul W Y c' _ (Formalism.MainNotions.UnusedSlot80.Relay2.InNΔi_sum W Y c' _ _ fun j _ =>
          Formalism.MainNotions.UnusedSlot80.Relay2.InNΔi_osmul W Y c' _ (hSY j))), ?_⟩
    have hmk : W.map ι (b k) = ∑ j, o k j • bY j + W.π₀ • E := by rw [← hEe]; abel
    have s1 : ∑ j, o k j • (lA W ^ κY • bY j) = lA W ^ κY • ∑ j, o k j • bY j := by
      rw [Finset.smul_sum]; exact Finset.sum_congr rfl fun j _ => smul_comm _ _ _
    have s2 : ∑ j, o k j • (W.π₀ • SY j) = W.π₀ • ∑ j, o k j • SY j := by
      rw [Finset.smul_sum]; exact Finset.sum_congr rfl fun j _ => smul_comm _ _ _
    have s12 : ∑ j, o k j • HhY j = lA W ^ κY • ∑ j, o k j • bY j + W.π₀ • ∑ j, o k j • SY j := by
      simp only [hSYe, smul_add, Finset.sum_add_distrib]
      rw [s1, s2]
    rw [hD, hSe, map_add, Formalism.MainNotions.UnusedSlot80.Relay2.mapA_smul, Formalism.MainNotions.UnusedSlot80.Relay2.mapA_smul, hmk, s12]
    exact linear_identity_head_difference _ _ _ _ _ _ _ _
  have hγT := sub_eq_iff_eq_add'.1 hxe
  have hγι : W.γ Y (W.map ι (Hh k)) = W.map ι (Hh k) + W.π₀ ^ (A.M PD.p) • W.map ι x := by
    rw [show W.γ Y (W.map ι (Hh k)) = W.map ι (W.γ T₂ (Hh k)) from (W.map_γ ι W.gam (Hh k)).symm, hγT,
      map_add, Formalism.MainNotions.UnusedSlot80.Relay2.mapA_smul]
  have hγY : ∀ j, W.γ Y (HhY j) = HhY j + W.π₀ ^ (A.M PD.p) • xY j := fun j => sub_eq_iff_eq_add'.1 (hxYe j)
  have hD2 : ∃ z, Formalism.MainNotions.LiftingTheory.InNΔi W Y c' z ∧ W.γ Y D - D = W.π₀ ^ (A.M PD.p) • z := by
    refine ⟨lA W ^ κY • W.map ι x - lA W ^ κ • ∑ j, o k j • xY j,
      Formalism.MainNotions.UnusedSlot80.Relay2.InNΔi_sub W Y c' (Formalism.MainNotions.UnusedSlot80.Relay2.InNΔi_lsmul W Y c' _ hmapx)
        (Formalism.MainNotions.UnusedSlot80.Relay2.InNΔi_lsmul W Y c' _ (Formalism.MainNotions.UnusedSlot80.Relay2.InNΔi_sum W Y c' _ _ fun j _ =>
          Formalism.MainNotions.UnusedSlot80.Relay2.InNΔi_osmul W Y c' _ (hxY j))), ?_⟩
    have s3 : ∑ j, o k j • (W.π₀ ^ (A.M PD.p) • xY j) = W.π₀ ^ (A.M PD.p) • ∑ j, o k j • xY j := by
      rw [Finset.smul_sum]; exact Finset.sum_congr rfl fun j _ => smul_comm _ _ _
    have s4 : W.γ Y (∑ j, o k j • HhY j) = ∑ j, o k j • HhY j + W.π₀ ^ (A.M PD.p) • ∑ j, o k j • xY j := by
      simp only [map_sum, map_smul, hγY, smul_add, Finset.sum_add_distrib]
      rw [s3]
    rw [hD, map_sub, γ_lA, γ_lA, hγι, s4]
    exact linear_identity_tail_difference _ _ _ _ _ _ _ _ _
  obtain ⟨K, x', hx', hK⟩ := Formalism.MainNotions.UnusedSlot80.Relay2.formal_unique W Y c' C.hinj C.hO2 hπ C.hR.2.2.1
    (C.hH C.hCA Y hY c').1 (C.hH C.hCA Y hY c').2.1 (A.M PD.p) D hD1 hD2
  obtain ⟨ν, hν, hνe⟩ := LevC.yM_gen W C.hTr C.hCA hπ C.h5p A hA a e
  refine ⟨K, ν • ((W.φD Y) ^ e) x', Formalism.MainNotions.UnusedSlot80.Relay2.Pp_gen W Y c' e hν hx', ?_⟩
  rw [← Formalism.MainNotions.UnusedSlot80.Relay2.φpow_lsmul, hK, Formalism.MainNotions.UnusedSlot80.Relay2.φpow_smul, map_pow, hνe, mul_smul]

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using Formalism.MainNotions.UnusedSlot80.Relay2.inMultiple_zero W T c e f`. Consider the case `insert j s hj ih`. Rewrite using `[Finset.sum_insert hj]`. Conclude with `Formalism.MainNotions.UnusedSlot80.Relay2.inMultiple_add W T c e f (h j (Finset.mem_insert_self j s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))`.
-/
theorem inFP_sum (T : LocLat G Qp LL O) (c : ZMod n) (e : ℕ) (f : LetA O n) {ι₀ : Type} (s : Finset ι₀)
    (z : ι₀ → W.DD T) (h : ∀ i ∈ s, InFP W T c e f (z i)) : InFP W T c e f (∑ i ∈ s, z i) := by
  induction s using Finset.induction_on with
  | empty => simpa using Formalism.MainNotions.UnusedSlot80.Relay2.inMultiple_zero W T c e f
  | insert j s hj ih =>
    rw [Finset.sum_insert hj]
    exact Formalism.MainNotions.UnusedSlot80.Relay2.inMultiple_add W T c e f (h j (Finset.mem_insert_self j s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/- English proof (translation)
Take `⟨κ, κ', Hh, aa, hHh, haa, hP⟩` from `hF`. Take `⟨κY, HhY, hHhY⟩` from `LevC.horTr_exists W C.hO2 C.hH C.hCA Y hY c' bY solY hbY (A.M PD.p)`. Use `choose K hK using fun k => hor_diff W C ι h2 hY A hA a c' e b sol hb bY solY hbY κ κY Hh HhY hHh hHhY o ho k`. Use `set Kt : ℕ := ∑ k, K k with hKt`. Use `set Λ : LetA O n := abelian₂ W A a e with hΛ`.

Use `⟨κ + κY, κ' + Kt, fun j => lA W ^ κ • HhY j, fun j => ∑ k, aa k * algebraMap O (LetA O n) (o k j), fun j => by rw [add_comm κ κY]; exact LevC.horTr_scale W Y bY solY _ κY κ j (hHhY j), fun j => ⟨W.AΔ.sum_mem fun k _ => W.AΔ.mul_mem (haa k).1 (W.AΔ.algebraMap_mem _), ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[Finset.mul_sum, map_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[← mul_assoc, (haa k).2, map_mul, ← IsScalarTower.algebraMap_apply O (LetA O n) W.EE]`. Simplify using `only [Formalism.MainNotions.UnusedSlot80.Relay2.φpow_lsmul]`.

Rewrite using `[lin_map (lA W) Λ κ κY κ' Kt (W.map ι x) (fun k => ((W.φD Y) ^ e) (W.map ι (Hh k))) (fun j => ((W.φD Y) ^ e) (HhY j)) aa (fun k j => algebraMap O (LetA O n) (o k j))]`. Use `Formalism.MainNotions.UnusedSlot80.Relay2.inMultiple_add W Y c' e _ ?_ ?_` and prove the remaining obligations. Use `Formalism.MainNotions.UnusedSlot80.Relay2.inMultiple_smul W Y c' e _ (LevC.lA_mem W _) (Formalism.MainNotions.UnusedSlot80.Relay2.inMultiple_smul W Y c' e _ (LevC.lA_mem W _) ?_)` and prove the remaining obligations. Use `Formalism.MainNotions.UnusedSlot80.Relay2.inMultiple_map W ι h2 hY c' e _ hP` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal.

Simplify using `only [Formalism.MainNotions.UnusedSlot80.Relay2.mapA_smul, map_sub, map_sum, Formalism.MainNotions.UnusedSlot80.Relay2.map_φpow]`. Use `Formalism.MainNotions.UnusedSlot80.Relay2.inMultiple_smul W Y c' e _ (LevC.lA_mem W _) (inFP_sum W Y c' e _ _ _ fun k _ => Formalism.MainNotions.UnusedSlot80.Relay2.inMultiple_smul W Y c' e _ (haa k).1 ?_)` and prove the remaining obligations. Establish `hle : K k ≤ Kt` using `Finset.single_le_sum (fun i _ => Nat.zero_le (K i)) (Finset.mem_univ k)`. Use `Formalism.MainNotions.UnusedSlot80.Relay2.inMultiple_smul W Y c' e _ (LevC.lA_mem W (Kt - K k)) (hK k)` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal.

Rewrite using `[smul_smul, ← pow_add, Nat.sub_add_cancel hle]`. Use `congr 1`. Simplify using `only [map_sub, Formalism.MainNotions.UnusedSlot80.Relay2.φpow_lsmul, map_sum, map_smul, algebraMap_smul]`.
-/
theorem repVV_map (C : LevC.Ctx W) {T₂ Y : LocLat G Qp LL O} (ι : LatHom T₂.L Y.L)
    (h2 : IsCrys PD T₂.ρ) (hY : IsCrys PD Y.ρ) (A : ArcP n) (hA : A.OK) (a : ZMod n) (c' : ZMod n) (e : ℕ)
    {d dY : ℕ} (b : Fin d → W.DD T₂) (sol : Fin d → ℕ → Fin d → LL) (hb : IsHor W T₂ c' b sol)
    (bY : Fin dY → W.DD Y) (solY : Fin dY → ℕ → Fin dY → LL) (hbY : IsHor W Y c' bY solY)
    (o : Fin d → Fin dY → O)
    (ho : ∀ k, ∃ E, Formalism.MainNotions.LiftingTheory.InNΔi W Y c' E ∧ W.map ι (b k) - ∑ j, o k j • bY j = W.π₀ • E)
    {x : W.DD T₂} {F : Fin d → W.EE} (hF : RepVV W T₂ c' e (A.M PD.p) (abelian₂ W A a e) b sol x F) :
    RepVV W Y c' e (A.M PD.p) (abelian₂ W A a e) bY solY (W.map ι x)
      (fun j => ∑ k, F k * algebraMap O W.EE (o k j)) := by
  obtain ⟨κ, κ', Hh, aa, hHh, haa, hP⟩ := hF
  obtain ⟨κY, HhY, hHhY⟩ := LevC.horTr_exists W C.hO2 C.hH C.hCA Y hY c' bY solY hbY (A.M PD.p)
  choose K hK using fun k => hor_diff W C ι h2 hY A hA a c' e b sol hb bY solY hbY κ κY Hh HhY hHh hHhY o ho k
  set Kt : ℕ := ∑ k, K k with hKt
  set Λ : LetA O n := abelian₂ W A a e with hΛ
  refine ⟨κ + κY, κ' + Kt, fun j => lA W ^ κ • HhY j,
    fun j => ∑ k, aa k * algebraMap O (LetA O n) (o k j),
    fun j => by rw [add_comm κ κY]; exact LevC.horTr_scale W Y bY solY _ κY κ j (hHhY j),
    fun j => ⟨W.AΔ.sum_mem fun k _ => W.AΔ.mul_mem (haa k).1 (W.AΔ.algebraMap_mem _), ?_⟩, ?_⟩
  · rw [Finset.mul_sum, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← mul_assoc, (haa k).2, map_mul, ← IsScalarTower.algebraMap_apply O (LetA O n) W.EE]
  · simp only [Formalism.MainNotions.UnusedSlot80.Relay2.φpow_lsmul]
    rw [lin_map (lA W) Λ κ κY κ' Kt (W.map ι x) (fun k => ((W.φD Y) ^ e) (W.map ι (Hh k)))
      (fun j => ((W.φD Y) ^ e) (HhY j)) aa (fun k j => algebraMap O (LetA O n) (o k j))]
    refine Formalism.MainNotions.UnusedSlot80.Relay2.inMultiple_add W Y c' e _ ?_ ?_
    · refine Formalism.MainNotions.UnusedSlot80.Relay2.inMultiple_smul W Y c' e _ (LevC.lA_mem W _)
        (Formalism.MainNotions.UnusedSlot80.Relay2.inMultiple_smul W Y c' e _ (LevC.lA_mem W _) ?_)
      have := Formalism.MainNotions.UnusedSlot80.Relay2.inMultiple_map W ι h2 hY c' e _ hP
      convert this using 1
      simp only [Formalism.MainNotions.UnusedSlot80.Relay2.mapA_smul, map_sub, map_sum, Formalism.MainNotions.UnusedSlot80.Relay2.map_φpow]
    · refine Formalism.MainNotions.UnusedSlot80.Relay2.inMultiple_smul W Y c' e _ (LevC.lA_mem W _)
        (inFP_sum W Y c' e _ _ _ fun k _ => Formalism.MainNotions.UnusedSlot80.Relay2.inMultiple_smul W Y c' e _ (haa k).1 ?_)
      have hle : K k ≤ Kt := Finset.single_le_sum (fun i _ => Nat.zero_le (K i)) (Finset.mem_univ k)
      have := Formalism.MainNotions.UnusedSlot80.Relay2.inMultiple_smul W Y c' e _ (LevC.lA_mem W (Kt - K k)) (hK k)
      convert this using 1
      rw [smul_smul, ← pow_add, Nat.sub_add_cancel hle]
      congr 1
      simp only [map_sub, Formalism.MainNotions.UnusedSlot80.Relay2.φpow_lsmul, map_sum, map_smul, algebraMap_smul]

/- English proof (translation)
Rewrite using `[Formalism.MainNotions.UnusedSlot80.ArcF.dv_single, crisMap_φVB_pow PD]`. Establish `hbN` using `(hb.1 k).1.1`. Establish `hmN` using `W.map_N ι h2 hY _ hbN`. Establish `e1 : Formalism.MainNotions.TruncatedSeriesCountingBounds.crisMap B ι.f (cmpD W T₂ (b k)) = cmpD W Y (W.map ι (b k))`. Rewrite using `[Formalism.MainNotions.UnusedSlot80.ArcF.cmpD_of_mem W T₂ hbN, Formalism.MainNotions.UnusedSlot80.ArcF.cmpD_of_mem W Y hmN]`.

Conclude with `(W.cmp_map ι h2 hY ⟨b k, hbN⟩ hmN).symm`. Establish `hsum : ∑ j, m j • bY j ∈ W.N Y` using `hmx ▸ hmN`. Establish `e2 : cmpD W Y (W.map ι (b k)) = W.cmp Y ⟨∑ j, m j • bY j, hsum⟩`. Rewrite using `[Formalism.MainNotions.UnusedSlot80.ArcF.cmpD_of_mem W Y hmN]`. Use `congr 1`.

Conclude with `Subtype.ext hmx`. Rewrite using `[e1, e2, Formalism.MainNotions.UnusedSlot80.ArcF.cmp_sum_letter W Y c' bY (fun j => (hbY.1 j).1.1) (fun j => Formalism.MainNotions.UnusedSlot80.Relay2.InNΔi_letter W Y c' (hbY.1 j)) m hsum, map_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, Formalism.MainNotions.UnusedSlot80.ArcF.dv_single, Formalism.MainNotions.UnusedSlot80.ArcF.cmpD_of_mem W Y (hbY.1 j).1.1]`.
-/
theorem dv_map {T₂ Y : LocLat G Qp LL O} (ι : LatHom T₂.L Y.L) (h2 : IsCrys PD T₂.ρ) (hY : IsCrys PD Y.ρ)
    (c' : ZMod n) (e : ℕ) {d dY : ℕ} (b : Fin d → W.DD T₂) (hb : Formalism.MainNotions.LiftingTheory.IsFrameΔ W T₂ c' b)
    (bY : Fin dY → W.DD Y) (hbY : Formalism.MainNotions.LiftingTheory.IsFrameΔ W Y c' bY) (k : Fin d) (m : Fin dY → LetA O n)
    (hmx : W.map ι (b k) = ∑ j, m j • bY j) :
    Formalism.MainNotions.TruncatedSeriesCountingBounds.crisMap B ι.f (dv W T₂ e b (Pi.single k 1)) =
      ∑ j, algebraMap O LL (PowerSeries.constantCoeff (m j c')) • dv W Y e bY (Pi.single j 1) := by
  rw [Formalism.MainNotions.UnusedSlot80.ArcF.dv_single, crisMap_φVB_pow PD]
  have hbN := (hb.1 k).1.1
  have hmN := W.map_N ι h2 hY _ hbN
  have e1 : Formalism.MainNotions.TruncatedSeriesCountingBounds.crisMap B ι.f (cmpD W T₂ (b k)) = cmpD W Y (W.map ι (b k)) := by
    rw [Formalism.MainNotions.UnusedSlot80.ArcF.cmpD_of_mem W T₂ hbN, Formalism.MainNotions.UnusedSlot80.ArcF.cmpD_of_mem W Y hmN]
    exact (W.cmp_map ι h2 hY ⟨b k, hbN⟩ hmN).symm
  have hsum : ∑ j, m j • bY j ∈ W.N Y := hmx ▸ hmN
  have e2 : cmpD W Y (W.map ι (b k)) = W.cmp Y ⟨∑ j, m j • bY j, hsum⟩ := by
    rw [Formalism.MainNotions.UnusedSlot80.ArcF.cmpD_of_mem W Y hmN]
    congr 1
    exact Subtype.ext hmx
  rw [e1, e2, Formalism.MainNotions.UnusedSlot80.ArcF.cmp_sum_letter W Y c' bY (fun j => (hbY.1 j).1.1)
    (fun j => Formalism.MainNotions.UnusedSlot80.Relay2.InNΔi_letter W Y c' (hbY.1 j)) m hsum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, Formalism.MainNotions.UnusedSlot80.ArcF.dv_single, Formalism.MainNotions.UnusedSlot80.ArcF.cmpD_of_mem W Y (hbY.1 j).1.1]

end Formalism.MainNotions.UnusedSlot80.SplitP
