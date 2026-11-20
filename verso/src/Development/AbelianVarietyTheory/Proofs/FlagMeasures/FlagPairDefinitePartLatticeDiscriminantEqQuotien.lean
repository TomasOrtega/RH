import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IdxSupRight
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairNormalFormGeometrySummaryStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairInnerLatticesUnimodularPrimitiveStatement

open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.DegCnt.PrimPerp

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

omit [StarRing K] [FiniteDimensional K V] in

/- English proof (translation)
Set `φ : 𝓞 K →ₗ[𝓞 K] (↥D ⧸ M.comap D.subtype)` to `(M.comap D.subtype).mkQ ∘ₗ LinearMap.toSpanSingleton (𝓞 K) D ⟨w, hw⟩`. Establish `hs : Function.Surjective φ`. Introduce `q`. Take `⟨y, rfl⟩` from `(M.comap D.subtype).mkQ_surjective q`. Take `⟨a, ha⟩` from `h2 y y.2`.

Conclude with `⟨a, ((Submodule.Quotient.eq (M.comap D.subtype)).2 (show y - a • (⟨w, hw⟩ : D) ∈ M.comap D.subtype from ha)).symm⟩`. Establish `hk : LinearMap.ker φ = J`. Use extensionality with `a`. Rewrite using `[LinearMap.mem_ker, ← h1]`. Conclude with `Submodule.Quotient.mk_eq_zero _`.

Conclude with `⟨(φ.quotKerEquivOfSurjective hs).symm.trans (Submodule.quotEquivOfEq _ _ hk)⟩`.
-/
theorem equiv_of_gen {D M : Submodule (𝓞 K) V} {w : V} (hw : w ∈ D) (J : Ideal (𝓞 K))
    (h1 : ∀ a : 𝓞 K, a • w ∈ M ↔ a ∈ J) (h2 : ∀ y ∈ D, ∃ a : 𝓞 K, y - a • w ∈ M) :
    Nonempty ((↥D ⧸ M.comap D.subtype) ≃ₗ[𝓞 K] (𝓞 K ⧸ J)) := by
  let φ : 𝓞 K →ₗ[𝓞 K] (↥D ⧸ M.comap D.subtype) :=
    (M.comap D.subtype).mkQ ∘ₗ LinearMap.toSpanSingleton (𝓞 K) D ⟨w, hw⟩
  have hs : Function.Surjective φ := by
    intro q
    obtain ⟨y, rfl⟩ := (M.comap D.subtype).mkQ_surjective q
    obtain ⟨a, ha⟩ := h2 y y.2
    exact ⟨a, ((Submodule.Quotient.eq (M.comap D.subtype)).2 (show y - a • (⟨w, hw⟩ : D) ∈ M.comap D.subtype from ha)).symm⟩
  have hk : LinearMap.ker φ = J := by
    ext a
    rw [LinearMap.mem_ker, ← h1]
    exact Submodule.Quotient.mk_eq_zero _
  exact ⟨(φ.quotKerEquivOfSurjective hs).symm.trans (Submodule.quotEquivOfEq _ _ hk)⟩

/- English proof (translation)
Take `⟨a, b⟩` from `DelScale.le_of_latMod hM.1`. Establish `hT0 : (T : K) ≠ 0` using `by exact_mod_cast (by omega : T ≠ 0)`. Establish `hzM : z ∈ M` using `by simpa using (hp 1).2 (Submodule.mem_one.2 ⟨1, map_one _⟩)`. Establish `hzS : z ∈ S` using `b hzM`. Establish `o1 : ∀ i ∈ I, ∀ y ∈ S, H.B i y = 0` using `fun i hi => (hrad i (hIS hi)).2 hi`.

Establish `o2 : ∀ i ∈ I, ∀ y ∈ S, H.B y i = 0` using `fun i hi y hy => by rw [← H.herm, o1 i hi y hy, star_zero]`. Establish `hint : ∀ x ∈ M, ∀ y ∈ M, H.B x y ∈ (1 : Submodule (𝓞 K) K)` using `fun x hx => ((mem_dual_iff H M x).1 (hM.2.symm ▸ hx)).2`. Use `set U : Submodule K V := Submodule.span K {z} ⊔ I with hU`. Establish `hmU : ∀ u, u ∈ U ↔ ∃ t : K, ∃ i ∈ I, u = t • z + i` using `fun u => by`. Rewrite using `[hU, Submodule.mem_sup]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, hx, i, hi, rfl⟩`. Take `⟨t, rfl⟩` from `Submodule.mem_span_singleton.1 hx`. Conclude with `⟨t, i, hi, rfl⟩`. Introduce and unpack `⟨t, i, hi, rfl⟩`.

Conclude with `⟨_, Submodule.mem_span_singleton.2 ⟨t, rfl⟩, i, hi, rfl⟩`. Establish `hUS : U ≤ S` using `sup_le ((Submodule.span_singleton_le_iff_mem _ _).2 hzS) hIS`. Establish `hWU : S ⊓ perp H U = W`. Use extensionality with `y`. Rewrite using `[hW, Submodule.mem_inf, mem_perp_iff]`.

Use `and_congr_right fun hy => ⟨fun h => h z ((hmU z).2 ⟨1, 0, I.zero_mem, by simp⟩), fun h x hx => ?_⟩` and prove the remaining obligations. Take `⟨t, i, hi, rfl⟩` from `(hmU x).1 hx`. Simplify using `[h, o2 i hi y hy]`. Establish `hWS : W ≤ S` using `fun y hy => ((hW y).1 hy).1`. Establish `hIW : I ≤ W` using `fun i hi => (hW i).2 ⟨hIS hi, o1 i hi z hzS⟩`.

Take `⟨k1, k2⟩` from `Compl.key H hIS hrad hM (le_sup_right : I ≤ U) hUS`. Take `⟨k3, -⟩` from `Compl.key H hIS hrad hM hIW hWS`. Rewrite `k1`, `k2` using `[hWU]`. Rewrite `k3` using `[k2]`. Rewrite `k1`, `k3` using `[← hU]`.

Establish `hzU : (T : K)⁻¹ • z ∈ U` using `(hmU _).2 ⟨_, 0, I.zero_mem, (add_zero _).symm⟩`. Establish `hd : (T : K)⁻¹ • z ∈ dual H (M ⊓ rs (𝓞 K) U)`. Rewrite using `[mem_dual_iff, Compl.span_inf (hM.1.2 ▸ hUS)]`. Use `⟨hzU, fun x hx => ?_⟩` and prove the remaining obligations. Take `⟨t, i, hi, rfl⟩` from `(hmU x).1 hx.2`.

Establish `ht : t • z ∈ M` using `by simpa using M.sub_mem hx.1 (a hi)`. Establish `e : H.B ((T : K)⁻¹ • z) (t • z + i) = - star t`. Simplify using `[hz, o2 i hi z hzS]`. Clear the denominators using the available nonvanishing facts. Apply the tactic sequence `try rfl`.

Rewrite using `[e]`. Conclude with `Submodule.neg_mem _ (UnimodQuot.star_mem_one ((hp t).1 ht))`. Rewrite `hd` using `[k1]`. Take `⟨m, hm, w, hw, e⟩` from `Submodule.mem_sup.1 hd.2`. Establish `hw' : w ∈ W` using `hw`.

Establish `hwD : w ∈ dual H (M ⊓ rs (𝓞 K) W)`. Rewrite using `[k3]`. Conclude with `⟨hw, Submodule.mem_sup.2 ⟨-m, M.neg_mem hm, _, hzU, by rw [← e]; abel⟩⟩`. Establish `h1 : ∀ c : 𝓞 K, c • w ∈ M ⊓ rs (𝓞 K) W ↔ c ∈ Ideal.span {(T : 𝓞 K)}`. Introduce `c`.

Establish `e1 : c • w = (algebraMap (𝓞 K) K c * (T : K)⁻¹) • z - c • m`. Rewrite using `[mul_smul, algebraMap_smul, ← e, smul_add]`. Normalize the expressions using the abelian group laws. Rewrite using `[Submodule.mem_inf, and_iff_left (Submodule.smul_mem _ c hw), e1, M.sub_mem_iff_left (M.smul_mem c hm), hp, Submodule.mem_one, Ideal.mem_span_singleton']`. Use `exists_congr fun d => ?_` and prove the remaining obligations.

Rewrite using `[eq_mul_inv_iff_mul_eq₀ hT0, ← map_natCast (algebraMap (𝓞 K) K), ← map_mul]`. Conclude with `(IsFractionRing.injective (𝓞 K) K).eq_iff`. Establish `h2 : ∀ y ∈ dual H (M ⊓ rs (𝓞 K) W), ∃ c : 𝓞 K, y - c • w ∈ M ⊓ rs (𝓞 K) W`. Introduce `y hy`. Rewrite `hy` using `[k3]`.

Take `⟨m', hm', u, hu, e'⟩` from `Submodule.mem_sup.1 hy.2`. Take `⟨t, i, hi, rfl⟩` from `(hmU u).1 hu`. Establish `h0` using `((hW y).1 hy.1).2`. Take `⟨c, hc⟩` from `Submodule.mem_one.1 (hint m' hm' z hzM)`. Rewrite `h0` using `[← e']`.

Simplify using `only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, hz, o1 i hi z hzS, smul_eq_mul, ← hc] at h0`. Establish `ht : t = algebraMap (𝓞 K) K c * (T : K)⁻¹`. Clear the denominators using the available nonvanishing facts. Take the linear combination `-h0`. Use `⟨c, ?_, Submodule.sub_mem _ hy.1 (Submodule.smul_mem _ c hw)⟩` and prove the remaining obligations.

Establish `: y - c • w = m' + c • m + i`. Rewrite using `[← e', ht, mul_smul, algebraMap_smul, ← e, smul_add]`. Normalize the expressions using the abelian group laws. Rewrite using `[this]`. Conclude with `M.add_mem (M.add_mem hm' (M.smul_mem c hm)) (a hi)`.

Establish `hle : M ⊓ rs (𝓞 K) W ≤ dual H (M ⊓ rs (𝓞 K) W)`. Rewrite using `[k3]`. Conclude with `le_inf inf_le_right (inf_le_left.trans le_sup_left)`. Take `⟨E⟩` from `equiv_of_gen hwD _ h1 h2`. Use `⟨?_, ⟨{w}, by simp, ?_⟩, ⟨?_, Compl.span_inf (hM.1.2 ▸ hWS)⟩, ⟨E⟩⟩` and prove the remaining obligations.

Establish `i1 : idx (M ⊓ rs (𝓞 K) W) (dual H (M ⊓ rs (𝓞 K) W)) = 1` using `AddSubgroup.relIndex_eq_one.2 hle`. Establish `i2 : idx (dual H (M ⊓ rs (𝓞 K) W)) (M ⊓ rs (𝓞 K) W) = T ^ (2 * Formalism.HermitianLatticesTheory.fDeg K)`. Establish `: idx (dual H (M ⊓ rs (𝓞 K) W)) (M ⊓ rs (𝓞 K) W) = Nat.card (𝓞 K ⧸ Ideal.span {(T : 𝓞 K)})` using `Nat.card_congr E.toEquiv`. Rewrite using `[this, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, Ideal.absNorm_span_natCast, RingOfIntegers.rank, IsTotallyComplex.finrank, Formalism.HermitianLatticesTheory.fDeg, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, IsTotallyComplex.nrRealPlaces_eq_zero, zero_add]`. Rewrite using `[del, gidx, i1, i2, mul_comm, pow_mul]`.

Simplify using the standard rewrite rules. Apply `le_antisymm` to reduce the goal to its premises. Introduce `y hy`. Take `⟨c, hc⟩` from `h2 y hy`. Conclude with `Submodule.mem_sup.2 ⟨_, hc, c • w, Submodule.smul_mem _ c (Submodule.subset_span (by simp)), by abel⟩`.

Conclude with `sup_le hle (Submodule.span_le.2 (by simpa using hwD))`. Take `⟨N, hN, rfl⟩` from `hM.1.1`. Use `⟨N ⊓ rs (𝓞 K) W, hN.of_le inf_le_left, ?_⟩` and prove the remaining obligations. Rewrite using `[sup_comm N, sup_inf_assoc_of_le N (show rs (𝓞 K) I ≤ rs (𝓞 K) W from hIW), sup_comm]`.
-/
theorem perp_prim (H : HermSpace K V) [IsTotallyComplex K] {M : Submodule (𝓞 K) V} {S I W : Submodule K V}
    (hIS : I ≤ S) (hrad : ∀ x ∈ S, (∀ y ∈ S, H.B x y = 0) ↔ x ∈ I) (hM : IsUnimodMod H M S I)
    {z : V} {T : ℕ} (hT : 1 ≤ T) (hz : H.B z z = -(T : K))
    (hp : ∀ t : K, t • z ∈ M ↔ t ∈ (1 : Submodule (𝓞 K) K))
    (hW : ∀ y, y ∈ W ↔ y ∈ S ∧ H.B y z = 0) :
    del H (M ⊓ rs (𝓞 K) W) = (T : ℝ) ^ Formalism.HermitianLatticesTheory.fDeg K ∧
      GenBy (dual H (M ⊓ rs (𝓞 K) W)) (M ⊓ rs (𝓞 K) W) 1 ∧ IsLatMod (M ⊓ rs (𝓞 K) W) W I ∧
      Nonempty ((↥(dual H (M ⊓ rs (𝓞 K) W)) ⧸ (M ⊓ rs (𝓞 K) W).comap (dual H (M ⊓ rs (𝓞 K) W)).subtype) ≃ₗ[𝓞 K]
        (𝓞 K ⧸ Ideal.span {(T : 𝓞 K)})) := by
  obtain ⟨a, b⟩ := DelScale.le_of_latMod hM.1
  have hT0 : (T : K) ≠ 0 := by exact_mod_cast (by omega : T ≠ 0)
  have hzM : z ∈ M := by simpa using (hp 1).2 (Submodule.mem_one.2 ⟨1, map_one _⟩)
  have hzS : z ∈ S := b hzM
  have o1 : ∀ i ∈ I, ∀ y ∈ S, H.B i y = 0 := fun i hi => (hrad i (hIS hi)).2 hi
  have o2 : ∀ i ∈ I, ∀ y ∈ S, H.B y i = 0 := fun i hi y hy => by rw [← H.herm, o1 i hi y hy, star_zero]
  have hint : ∀ x ∈ M, ∀ y ∈ M, H.B x y ∈ (1 : Submodule (𝓞 K) K) := fun x hx =>
    ((mem_dual_iff H M x).1 (hM.2.symm ▸ hx)).2
  set U : Submodule K V := Submodule.span K {z} ⊔ I with hU
  have hmU : ∀ u, u ∈ U ↔ ∃ t : K, ∃ i ∈ I, u = t • z + i := fun u => by
    rw [hU, Submodule.mem_sup]
    constructor
    · rintro ⟨x, hx, i, hi, rfl⟩
      obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hx
      exact ⟨t, i, hi, rfl⟩
    · rintro ⟨t, i, hi, rfl⟩
      exact ⟨_, Submodule.mem_span_singleton.2 ⟨t, rfl⟩, i, hi, rfl⟩
  have hUS : U ≤ S := sup_le ((Submodule.span_singleton_le_iff_mem _ _).2 hzS) hIS
  have hWU : S ⊓ perp H U = W := by
    ext y
    rw [hW, Submodule.mem_inf, mem_perp_iff]
    refine and_congr_right fun hy => ⟨fun h => h z ((hmU z).2 ⟨1, 0, I.zero_mem, by simp⟩), fun h x hx => ?_⟩
    obtain ⟨t, i, hi, rfl⟩ := (hmU x).1 hx
    simp [h, o2 i hi y hy]
  have hWS : W ≤ S := fun y hy => ((hW y).1 hy).1
  have hIW : I ≤ W := fun i hi => (hW i).2 ⟨hIS hi, o1 i hi z hzS⟩
  obtain ⟨k1, k2⟩ := Compl.key H hIS hrad hM (le_sup_right : I ≤ U) hUS
  obtain ⟨k3, -⟩ := Compl.key H hIS hrad hM hIW hWS
  rw [hWU] at k1 k2
  rw [k2] at k3
  rw [← hU] at k1 k3
  have hzU : (T : K)⁻¹ • z ∈ U := (hmU _).2 ⟨_, 0, I.zero_mem, (add_zero _).symm⟩
  have hd : (T : K)⁻¹ • z ∈ dual H (M ⊓ rs (𝓞 K) U) := by
    rw [mem_dual_iff, Compl.span_inf (hM.1.2 ▸ hUS)]
    refine ⟨hzU, fun x hx => ?_⟩
    obtain ⟨t, i, hi, rfl⟩ := (hmU x).1 hx.2
    have ht : t • z ∈ M := by simpa using M.sub_mem hx.1 (a hi)
    have e : H.B ((T : K)⁻¹ • z) (t • z + i) = - star t := by
      simp [hz, o2 i hi z hzS]
      field_simp
      try rfl
    rw [e]
    exact Submodule.neg_mem _ (UnimodQuot.star_mem_one ((hp t).1 ht))
  rw [k1] at hd
  obtain ⟨m, hm, w, hw, e⟩ := Submodule.mem_sup.1 hd.2
  have hw' : w ∈ W := hw
  have hwD : w ∈ dual H (M ⊓ rs (𝓞 K) W) := by
    rw [k3]
    exact ⟨hw, Submodule.mem_sup.2 ⟨-m, M.neg_mem hm, _, hzU, by rw [← e]; abel⟩⟩
  have h1 : ∀ c : 𝓞 K, c • w ∈ M ⊓ rs (𝓞 K) W ↔ c ∈ Ideal.span {(T : 𝓞 K)} := by
    intro c
    have e1 : c • w = (algebraMap (𝓞 K) K c * (T : K)⁻¹) • z - c • m := by
      rw [mul_smul, algebraMap_smul, ← e, smul_add]; abel
    rw [Submodule.mem_inf, and_iff_left (Submodule.smul_mem _ c hw), e1,
      M.sub_mem_iff_left (M.smul_mem c hm), hp, Submodule.mem_one, Ideal.mem_span_singleton']
    refine exists_congr fun d => ?_
    rw [eq_mul_inv_iff_mul_eq₀ hT0, ← map_natCast (algebraMap (𝓞 K) K), ← map_mul]
    exact (IsFractionRing.injective (𝓞 K) K).eq_iff
  have h2 : ∀ y ∈ dual H (M ⊓ rs (𝓞 K) W), ∃ c : 𝓞 K, y - c • w ∈ M ⊓ rs (𝓞 K) W := by
    intro y hy
    rw [k3] at hy
    obtain ⟨m', hm', u, hu, e'⟩ := Submodule.mem_sup.1 hy.2
    obtain ⟨t, i, hi, rfl⟩ := (hmU u).1 hu
    have h0 := ((hW y).1 hy.1).2
    obtain ⟨c, hc⟩ := Submodule.mem_one.1 (hint m' hm' z hzM)
    rw [← e'] at h0
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, hz, o1 i hi z hzS, smul_eq_mul, ← hc] at h0
    have ht : t = algebraMap (𝓞 K) K c * (T : K)⁻¹ := by
      field_simp
      linear_combination -h0
    refine ⟨c, ?_, Submodule.sub_mem _ hy.1 (Submodule.smul_mem _ c hw)⟩
    have : y - c • w = m' + c • m + i := by
      rw [← e', ht, mul_smul, algebraMap_smul, ← e, smul_add]; abel
    rw [this]
    exact M.add_mem (M.add_mem hm' (M.smul_mem c hm)) (a hi)
  have hle : M ⊓ rs (𝓞 K) W ≤ dual H (M ⊓ rs (𝓞 K) W) := by
    rw [k3]
    exact le_inf inf_le_right (inf_le_left.trans le_sup_left)
  obtain ⟨E⟩ := equiv_of_gen hwD _ h1 h2
  refine ⟨?_, ⟨{w}, by simp, ?_⟩, ⟨?_, Compl.span_inf (hM.1.2 ▸ hWS)⟩, ⟨E⟩⟩
  · have i1 : idx (M ⊓ rs (𝓞 K) W) (dual H (M ⊓ rs (𝓞 K) W)) = 1 := AddSubgroup.relIndex_eq_one.2 hle
    have i2 : idx (dual H (M ⊓ rs (𝓞 K) W)) (M ⊓ rs (𝓞 K) W) = T ^ (2 * Formalism.HermitianLatticesTheory.fDeg K) := by
      have : idx (dual H (M ⊓ rs (𝓞 K) W)) (M ⊓ rs (𝓞 K) W) = Nat.card (𝓞 K ⧸ Ideal.span {(T : 𝓞 K)}) :=
        Nat.card_congr E.toEquiv
      rw [this, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, Ideal.absNorm_span_natCast, RingOfIntegers.rank,
        IsTotallyComplex.finrank, Formalism.HermitianLatticesTheory.fDeg, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
        IsTotallyComplex.nrRealPlaces_eq_zero, zero_add]
    rw [del, gidx, i1, i2, mul_comm, pow_mul]
    simp
  · apply le_antisymm
    · intro y hy
      obtain ⟨c, hc⟩ := h2 y hy
      exact Submodule.mem_sup.2 ⟨_, hc, c • w, Submodule.smul_mem _ c (Submodule.subset_span (by simp)), by abel⟩
    · exact sup_le hle (Submodule.span_le.2 (by simpa using hwD))
  · obtain ⟨N, hN, rfl⟩ := hM.1.1
    refine ⟨N ⊓ rs (𝓞 K) W, hN.of_le inf_le_left, ?_⟩
    rw [sup_comm N, sup_inf_assoc_of_le N (show rs (𝓞 K) I ≤ rs (𝓞 K) W from hIW), sup_comm]

/- English proof (translation)
Introduce `K V _ _ _ _ _ _ _ _ H hK r N g Λ hg hΛ`. Use `haveI := hK.1`. Take `⟨hNF, -, -, -, -, -, -, hww, -, hT, -⟩` from `GlobalTheory.T.hermFramePairNormalForm_geometry_summary K V H hK r N`. Take `⟨hL, hL', hp, hp', -⟩` from `GlobalTheory.T.hermFramePair_innerLattices_unimodular_primitive K V H hK r N g Λ hg hΛ`. Establish `hV` using `hNF.2.2.2.1`.

Establish `hc : N.c ≠ 0` using `hNF.1.1`. Establish `hzz : N.F'.z = N.c • N.F.z` using `N.same (Fin.last r) N.j_le`. Establish `hzS : N.F.z ∈ uPerp N.F N.F'`. Use `(hp 1).2 (Submodule.mem_one.2 ⟨1, map_one _⟩)` as an intermediate fact. Rewrite `this` using `[one_smul]`.

Conclude with `this.1`. Establish `hXV : N.F.X ⊔ N.F'.X ≤ V0 N.F N.F'` using `le_sup_left`. Establish `hW : ∀ y, y ∈ wSp N.F N.F' ↔ y ∈ uPerp N.F N.F' ∧ H.B y N.F.z = 0`. Introduce `y`. Rewrite using `[wSp, uPerp, mem_perp_iff, mem_perp_iff]`.

Use `⟨fun h => ⟨fun x hx => h x (hXV hx), h _ (Submodule.mem_sup_right (Submodule.subset_span (by simp)))⟩, fun h x hx => ?_⟩` and prove the remaining obligations. Take `⟨u, hu, v, hv, rfl⟩` from `Submodule.mem_sup.1 hx`. Take `⟨s, t, rfl⟩` from `Submodule.mem_span_pair.1 hv`. Simplify using `[hzz, h.1 u hu, h.2]`. Establish `hW' : ∀ y, y ∈ wSp N.F N.F' ↔ y ∈ uPerp N.F N.F' ∧ H.B y N.F'.z = 0`.

Introduce `y`. Rewrite using `[hW, hzz]`. Simplify using `[hc]`. Establish `hIX : II N.F N.F' ≤ N.F.X ⊔ N.F'.X` using `inf_le_left.trans le_sup_left`. Establish `hIS : II N.F N.F' ≤ uPerp N.F N.F'` using `fun i hi => (mem_perp_iff H _ i).2 fun x hx => (hV i (hXV (hIX hi))).2 hi x (hXV hx)`.

Establish `hrad : ∀ x ∈ uPerp N.F N.F', (∀ y ∈ uPerp N.F N.F', H.B x y = 0) ↔ x ∈ II N.F N.F'`. Introduce `x hx`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `h1 : x ∈ N.F.X ⊔ N.F'.X` using `UnimodQuot.mem_of_perp_perp H _ fun y hy => by`.

Rewrite using `[← H.herm, h y hy, star_zero]`. Conclude with `(hV x (hXV h1)).1 ((mem_perp_iff H _ x).1 ((hW x).2 ⟨hx, h _ hzS⟩))`. Introduce `h y hy`. Rewrite using `[← H.herm, (mem_perp_iff H _ y).1 hy x (hIX h), star_zero]`. Take `⟨a1, a2, a3, a4⟩` from `perp_prim H hIS hrad hL hT (N.hT ▸ N.F.zz) hp hW`.

Take `⟨b1, -, b3, -⟩` from `perp_prim H hIS hrad hL' hT (N.hT' ▸ N.F'.zz) hp' hW'`. Establish `e : flagPairDefinitePartLattice N.F' N.F Λ = latL N.F' N.F Λ ⊓ rs (𝓞 K) (wSp N.F N.F')` using `by rw [flagPairDefinitePartLattice, hww]`. Rewrite using `[e]`. Conclude with `⟨a1, b1, a2, a3, b3, a4⟩`.
-/
theorem main : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ (g : ℕ) (Λ : Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ → del H (flagPairDefinitePartLattice N.F N.F' Λ) = N.NT ∧ del H (flagPairDefinitePartLattice N.F' N.F Λ) = N.NT ∧ GenBy (dual H (flagPairDefinitePartLattice N.F N.F' Λ)) (flagPairDefinitePartLattice N.F N.F' Λ) 1 ∧ IsLatMod (flagPairDefinitePartLattice N.F N.F' Λ) (wSp N.F N.F') (II N.F N.F') ∧ IsLatMod (flagPairDefinitePartLattice N.F' N.F Λ) (wSp N.F N.F') (II N.F N.F') ∧ Nonempty ((↥(dual H (flagPairDefinitePartLattice N.F N.F' Λ)) ⧸ (flagPairDefinitePartLattice N.F N.F' Λ).comap (dual H (flagPairDefinitePartLattice N.F N.F' Λ)).subtype) ≃ₗ[𝓞 K] (𝓞 K ⧸ Ideal.span {(N.T : 𝓞 K)})) := by
  intro K V _ _ _ _ _ _ _ _ H hK r N g Λ hg hΛ
  haveI := hK.1
  obtain ⟨hNF, -, -, -, -, -, -, hww, -, hT, -⟩ := GlobalTheory.T.hermFramePairNormalForm_geometry_summary K V H hK r N
  obtain ⟨hL, hL', hp, hp', -⟩ := GlobalTheory.T.hermFramePair_innerLattices_unimodular_primitive K V H hK r N g Λ hg hΛ
  have hV := hNF.2.2.2.1
  have hc : N.c ≠ 0 := hNF.1.1
  have hzz : N.F'.z = N.c • N.F.z := N.same (Fin.last r) N.j_le
  have hzS : N.F.z ∈ uPerp N.F N.F' := by
    have := (hp 1).2 (Submodule.mem_one.2 ⟨1, map_one _⟩)
    rw [one_smul] at this
    exact this.1
  have hXV : N.F.X ⊔ N.F'.X ≤ V0 N.F N.F' := le_sup_left
  have hW : ∀ y, y ∈ wSp N.F N.F' ↔ y ∈ uPerp N.F N.F' ∧ H.B y N.F.z = 0 := by
    intro y
    rw [wSp, uPerp, mem_perp_iff, mem_perp_iff]
    refine ⟨fun h => ⟨fun x hx => h x (hXV hx), h _ (Submodule.mem_sup_right (Submodule.subset_span (by simp)))⟩,
      fun h x hx => ?_⟩
    obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.1 hx
    obtain ⟨s, t, rfl⟩ := Submodule.mem_span_pair.1 hv
    simp [hzz, h.1 u hu, h.2]
  have hW' : ∀ y, y ∈ wSp N.F N.F' ↔ y ∈ uPerp N.F N.F' ∧ H.B y N.F'.z = 0 := by
    intro y
    rw [hW, hzz]
    simp [hc]
  have hIX : II N.F N.F' ≤ N.F.X ⊔ N.F'.X := inf_le_left.trans le_sup_left
  have hIS : II N.F N.F' ≤ uPerp N.F N.F' := fun i hi =>
    (mem_perp_iff H _ i).2 fun x hx => (hV i (hXV (hIX hi))).2 hi x (hXV hx)
  have hrad : ∀ x ∈ uPerp N.F N.F', (∀ y ∈ uPerp N.F N.F', H.B x y = 0) ↔ x ∈ II N.F N.F' := by
    intro x hx
    constructor
    · intro h
      have h1 : x ∈ N.F.X ⊔ N.F'.X := UnimodQuot.mem_of_perp_perp H _ fun y hy => by
        rw [← H.herm, h y hy, star_zero]
      exact (hV x (hXV h1)).1 ((mem_perp_iff H _ x).1 ((hW x).2 ⟨hx, h _ hzS⟩))
    · intro h y hy
      rw [← H.herm, (mem_perp_iff H _ y).1 hy x (hIX h), star_zero]
  obtain ⟨a1, a2, a3, a4⟩ := perp_prim H hIS hrad hL hT (N.hT ▸ N.F.zz) hp hW
  obtain ⟨b1, -, b3, -⟩ := perp_prim H hIS hrad hL' hT (N.hT' ▸ N.F'.zz) hp' hW'
  have e : flagPairDefinitePartLattice N.F' N.F Λ = latL N.F' N.F Λ ⊓ rs (𝓞 K) (wSp N.F N.F') := by rw [flagPairDefinitePartLattice, hww]
  rw [e]
  exact ⟨a1, b1, a2, a3, b3, a4⟩

end GlobalTheory.DegCnt.PrimPerp
