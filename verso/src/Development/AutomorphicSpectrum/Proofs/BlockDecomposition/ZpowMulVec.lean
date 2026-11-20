import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousMulVec
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsClopenCoset
open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd GlobalTheory.SplitWeil GlobalTheory.JHMult GlobalTheory.CompanionTheory.BZShell GlobalTheory.CompanionTheory.MirPair GlobalTheory.CompanionTheory.BZCore
open scoped Topology

noncomputable section

namespace GlobalTheory.CompanionTheory.BZCore

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {d : ℕ}

/- English proof (translation)
Set `φ : kˣ →* GL (Fin d) k` to `Units.map (Matrix.scalar (Fin d) : k →+* Matrix (Fin d) (Fin d) k).toMonoidHom`. Establish `hφ : ∀ u : kˣ, ((φ u : GL (Fin d) k) : Matrix (Fin d) (Fin d) k) = (u : k) • (1 : Matrix (Fin d) (Fin d) k)`. Introduce `u`. Use extensionality with `i j`. Simplify using `[φ, Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.one_apply]`.

Establish `h1 : z = φ (Units.mk0 ϖ hϖ0)` using `Units.ext (by rw [hφ, hz]; rfl)`. Rewrite using `[h1, ← map_zpow, hφ, Matrix.smul_mulVec, one_mulVec]`. Simplify using the standard rewrite rules.
-/
theorem zpow_mulVec (z : GL (Fin d) k) (ϖ : k) (hz : (z : Matrix (Fin d) (Fin d) k) = ϖ • (1 : Matrix (Fin d) (Fin d) k))
    (hϖ0 : ϖ ≠ 0) (r : ℤ) (y : Fin d → k) :
    ((z ^ r : GL (Fin d) k) : Matrix (Fin d) (Fin d) k).mulVec y = ϖ ^ r • y := by
  let φ : kˣ →* GL (Fin d) k := Units.map (Matrix.scalar (Fin d) : k →+* Matrix (Fin d) (Fin d) k).toMonoidHom
  have hφ : ∀ u : kˣ, ((φ u : GL (Fin d) k) : Matrix (Fin d) (Fin d) k) = (u : k) • (1 : Matrix (Fin d) (Fin d) k) := by
    intro u
    ext i j
    simp [φ, Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.one_apply]
  have h1 : z = φ (Units.mk0 ϖ hϖ0) := Units.ext (by rw [hφ, hz]; rfl)
  rw [h1, ← map_zpow, hφ, Matrix.smul_mulVec, one_mulVec]
  simp

/- English proof (translation)
Establish `hv : ValuativeRel.valuation k ϖ ≠ 0` using `by simpa using hϖ0`. Rewrite using `[latZ, COSub.mem_act, ← _root_.zpow_neg, zpow_mulVec z ϖ hz hϖ0]`. Use `show (∀ i, ValuativeRel.valuation k ((ϖ ^ (-r) • y) i) ≤ 1) ↔ _`. Use `forall_congr' fun i => ?_` and prove the remaining obligations. Rewrite using `[Pi.smul_apply, smul_eq_mul, map_mul, map_zpow₀, _root_.zpow_neg, inv_mul_le_iff₀ (zero_lt_iff.2 (zpow_ne_zero _ hv)), mul_one]`.
-/
theorem mem_latZ (z : GL (Fin d) k) (ϖ : k) (hz : (z : Matrix (Fin d) (Fin d) k) = ϖ • (1 : Matrix (Fin d) (Fin d) k))
    (hϖ0 : ϖ ≠ 0) (r : ℤ) (y : Fin d → k) :
    y ∈ (latZ z r).sub ↔ ∀ i, ValuativeRel.valuation k (y i) ≤ ValuativeRel.valuation k ϖ ^ r := by
  have hv : ValuativeRel.valuation k ϖ ≠ 0 := by simpa using hϖ0
  rw [latZ, COSub.mem_act, ← _root_.zpow_neg, zpow_mulVec z ϖ hz hϖ0]
  show (∀ i, ValuativeRel.valuation k ((ϖ ^ (-r) • y) i) ≤ 1) ↔ _
  refine forall_congr' fun i => ?_
  rw [Pi.smul_apply, smul_eq_mul, map_mul, map_zpow₀, _root_.zpow_neg, inv_mul_le_iff₀ (zero_lt_iff.2 (zpow_ne_zero _ hv)), mul_one]

/- English proof (translation)
Introduce `y hy`. Establish `hv : 0 < ValuativeRel.valuation k ϖ` using `zero_lt_iff.2 (by simpa using hϖ0)`. Rewrite `hy`, the goal using `[mem_latZ z ϖ hz hϖ0]`. Conclude with `fun i => (hy i).trans (zpow_le_zpow_right_of_le_one₀ hv hϖ.le h)`.
-/
theorem latZ_anti (z : GL (Fin d) k) (ϖ : k) (hz : (z : Matrix (Fin d) (Fin d) k) = ϖ • (1 : Matrix (Fin d) (Fin d) k))
    (hϖ : ValuativeRel.valuation k ϖ < 1) (hϖ0 : ϖ ≠ 0) (r s : ℤ) (h : r ≤ s) : (latZ z s).sub ≤ (latZ z r).sub := by
  intro y hy
  have hv : 0 < ValuativeRel.valuation k ϖ := zero_lt_iff.2 (by simpa using hϖ0)
  rw [mem_latZ z ϖ hz hϖ0] at hy ⊢
  exact fun i => (hy i).trans (zpow_le_zpow_right_of_le_one₀ hv hϖ.le h)

/- English proof (translation)
Establish `hall : ∀ᶠ t : k in 𝓝 0, ∀ w ∈ ((lat0 : COSub k d).sub : Set (Fin d → k)), t • w ∈ (L.sub : Set (Fin d → k))`. Use `(lat0 : COSub k d).isCompact.eventually_forall_of_forall_eventually fun w _ => ?_` and prove the remaining obligations. Establish `hc : Continuous fun p : k × (Fin d → k) => p.1 • p.2` using `continuous_fst.smul continuous_snd`. Establish `h0 : (L.sub : Set (Fin d → k)) ∈ 𝓝 (((0 : k), w).1 • ((0 : k), w).2)`. Simplify using `using L.isOpen.mem_nhds (show (0 : Fin d → k) ∈ (L.sub : Set (Fin d → k)) from L.sub.zero_mem)`.

Conclude with `hc.continuousAt.eventually h0`. Establish `ht : Filter.Tendsto (fun n : ℕ => ϖ ^ n) Filter.atTop (𝓝 0)`. Rewrite using `[(IsValuativeTopology.hasBasis_nhds_zero' k).tendsto_right_iff]`. Introduce `γ hγ`. Establish `: MulArchimedean (ValuativeRel.ValueGroupWithZero k)` using `ValuativeRel.isRankLeOne_iff_mulArchimedean.mp inferInstance`.

Take `⟨n, hn⟩` from `exists_pow_lt₀ hϖ (Units.mk0 γ hγ)`. Use `filter_upwards [Filter.eventually_ge_atTop n] with m hm`. Rewrite using `[map_pow]`. Conclude with `lt_of_le_of_lt (pow_le_pow_right_of_le_one' hϖ.le hm) hn`. Take `⟨r, hr⟩` from `(ht.eventually hall).exists`.

Use `⟨r, fun y hy => ?_⟩` and prove the remaining obligations. Establish `h1 : ϖ ^ r • ((((z ^ (r : ℤ) : GL (Fin d) k)⁻¹ : GL (Fin d) k) : Matrix (Fin d) (Fin d) k).mulVec y) ∈ (L.sub : Set (Fin d → k))` using `hr _ hy`. Establish `h2 : ϖ ^ r • ((((z ^ (r : ℤ) : GL (Fin d) k)⁻¹ : GL (Fin d) k) : Matrix (Fin d) (Fin d) k).mulVec y) = y`. Use `zpow_mulVec z ϖ hz hϖ0 (r : ℤ) ((((z ^ (r : ℤ) : GL (Fin d) k)⁻¹ : GL (Fin d) k) : Matrix (Fin d) (Fin d) k).mulVec y)` as an intermediate fact. Rewrite `this` using `[mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec, zpow_natCast]`.

Conclude with `this.symm`. Rewrite `h1` using `[h2]`. Conclude with `h1`.
-/
theorem latZ_basis (z : GL (Fin d) k) (ϖ : k) (hz : (z : Matrix (Fin d) (Fin d) k) = ϖ • (1 : Matrix (Fin d) (Fin d) k))
    (hϖ : ValuativeRel.valuation k ϖ < 1) (hϖ0 : ϖ ≠ 0) (L : COSub k d) : ∃ r : ℕ, (latZ z (r : ℤ)).sub ≤ L.sub := by
  have hall : ∀ᶠ t : k in 𝓝 0, ∀ w ∈ ((lat0 : COSub k d).sub : Set (Fin d → k)), t • w ∈ (L.sub : Set (Fin d → k)) := by
    refine (lat0 : COSub k d).isCompact.eventually_forall_of_forall_eventually fun w _ => ?_
    have hc : Continuous fun p : k × (Fin d → k) => p.1 • p.2 := continuous_fst.smul continuous_snd
    have h0 : (L.sub : Set (Fin d → k)) ∈ 𝓝 (((0 : k), w).1 • ((0 : k), w).2) := by
      simpa using L.isOpen.mem_nhds (show (0 : Fin d → k) ∈ (L.sub : Set (Fin d → k)) from L.sub.zero_mem)
    exact hc.continuousAt.eventually h0
  have ht : Filter.Tendsto (fun n : ℕ => ϖ ^ n) Filter.atTop (𝓝 0) := by
    rw [(IsValuativeTopology.hasBasis_nhds_zero' k).tendsto_right_iff]
    intro γ hγ
    have : MulArchimedean (ValuativeRel.ValueGroupWithZero k) :=
      ValuativeRel.isRankLeOne_iff_mulArchimedean.mp inferInstance
    obtain ⟨n, hn⟩ := exists_pow_lt₀ hϖ (Units.mk0 γ hγ)
    filter_upwards [Filter.eventually_ge_atTop n] with m hm
    rw [map_pow]
    exact lt_of_le_of_lt (pow_le_pow_right_of_le_one' hϖ.le hm) hn
  obtain ⟨r, hr⟩ := (ht.eventually hall).exists
  refine ⟨r, fun y hy => ?_⟩
  have h1 : ϖ ^ r • ((((z ^ (r : ℤ) : GL (Fin d) k)⁻¹ : GL (Fin d) k) : Matrix (Fin d) (Fin d) k).mulVec y) ∈ (L.sub : Set (Fin d → k)) := hr _ hy
  have h2 : ϖ ^ r • ((((z ^ (r : ℤ) : GL (Fin d) k)⁻¹ : GL (Fin d) k) : Matrix (Fin d) (Fin d) k).mulVec y) = y := by
    have := zpow_mulVec z ϖ hz hϖ0 (r : ℤ) ((((z ^ (r : ℤ) : GL (Fin d) k)⁻¹ : GL (Fin d) k) : Matrix (Fin d) (Fin d) k).mulVec y)
    rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec, zpow_natCast] at this
    exact this.symm
  rw [h2] at h1
  exact h1

/- English proof (translation)
Take `⟨t, ht⟩` from `L.isCompact.elim_finite_subcover (fun c : L.sub => {y | y - (c : Fin d → k) ∈ L'.sub}) (fun c => (isClopen_coset L' c).isOpen) (fun y hy => Set.mem_iUnion.2 ⟨⟨y, hy⟩, by simp⟩)`. Set `mk : (Fin d → k) → (Fin d → k) ⧸ L'.sub` to `QuotientAddGroup.mk`. Establish `hout : ∀ c : Fin d → k, (-(Quotient.out (mk c)) + c) ∈ L'.sub` using `fun c => QuotientAddGroup.eq.1 (QuotientAddGroup.out_eq' (mk c))`. Set `S : Finset (Fin d → k)` to `(t.image fun c : L.sub => mk c.1).image Quotient.out`. Use `⟨S, ?_, ?_⟩` and prove the remaining obligations.

Introduce `s hs`. Take `⟨q, hq, rfl⟩` from `Finset.mem_image.1 hs`. Take `⟨c, -, rfl⟩` from `Finset.mem_image.1 hq`. Establish `h1` using `L.sub.sub_mem c.2 (h (hout c.1))`. Simplify `h1` using `[sub_eq_add_neg]`.

Introduce `y hy`. Take `⟨c, hct, hc⟩` from `Set.mem_iUnion₂.1 (ht hy)`. Establish `hc' : y - c.1 ∈ L'.sub` using `hc`. Establish `key : ∀ s ∈ S, y - s ∈ L'.sub → s = Quotient.out (mk y)`. Introduce `s hs hys`.

Take `⟨q, -, rfl⟩` from `Finset.mem_image.1 hs`. Establish `e1 : mk (Quotient.out q) = q` using `QuotientAddGroup.out_eq' q`. Establish `e2 : mk (Quotient.out q) = mk y` using `QuotientAddGroup.eq.2 (by simpa [sub_eq_add_neg, add_comm] using hys)`. Rewrite using `[← e2, e1]`. Establish `hmem : Quotient.out (mk c.1) ∈ S` using `Finset.mem_image_of_mem _ (Finset.mem_image_of_mem (fun c : L.sub => mk c.1) hct)`.

Establish `hs : y - Quotient.out (mk c.1) ∈ L'.sub`. Use `L'.sub.add_mem hc' (hout c.1)` as an intermediate fact. Establish `e : y - c.1 + (-(Quotient.out (mk c.1)) + c.1) = y - Quotient.out (mk c.1)` using `by abel`. Rewrite `this` using `[e]`. Then use the resulting hypothesis. Conclude with `⟨_, ⟨hmem, hs⟩, fun s' hs' => (key s' hs'.1 hs'.2).trans (key _ hmem hs).symm⟩`.
-/
theorem exists_reps (L' L : COSub k d) (h : L'.sub ≤ L.sub) : ∃ S : Finset (Fin d → k), IsReps L' L S := by
  classical
  obtain ⟨t, ht⟩ := L.isCompact.elim_finite_subcover (fun c : L.sub => {y | y - (c : Fin d → k) ∈ L'.sub})
    (fun c => (isClopen_coset L' c).isOpen) (fun y hy => Set.mem_iUnion.2 ⟨⟨y, hy⟩, by simp⟩)
  let mk : (Fin d → k) → (Fin d → k) ⧸ L'.sub := QuotientAddGroup.mk
  have hout : ∀ c : Fin d → k, (-(Quotient.out (mk c)) + c) ∈ L'.sub := fun c =>
    QuotientAddGroup.eq.1 (QuotientAddGroup.out_eq' (mk c))
  let S : Finset (Fin d → k) := (t.image fun c : L.sub => mk c.1).image Quotient.out
  refine ⟨S, ?_, ?_⟩
  · intro s hs
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hs
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hq
    have h1 := L.sub.sub_mem c.2 (h (hout c.1))
    simpa [sub_eq_add_neg] using h1
  · intro y hy
    obtain ⟨c, hct, hc⟩ := Set.mem_iUnion₂.1 (ht hy)
    have hc' : y - c.1 ∈ L'.sub := hc
    have key : ∀ s ∈ S, y - s ∈ L'.sub → s = Quotient.out (mk y) := by
      intro s hs hys
      obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hs
      have e1 : mk (Quotient.out q) = q := QuotientAddGroup.out_eq' q
      have e2 : mk (Quotient.out q) = mk y :=
        QuotientAddGroup.eq.2 (by simpa [sub_eq_add_neg, add_comm] using hys)
      rw [← e2, e1]
    have hmem : Quotient.out (mk c.1) ∈ S :=
      Finset.mem_image_of_mem _ (Finset.mem_image_of_mem (fun c : L.sub => mk c.1) hct)
    have hs : y - Quotient.out (mk c.1) ∈ L'.sub := by
      have := L'.sub.add_mem hc' (hout c.1)
      have e : y - c.1 + (-(Quotient.out (mk c.1)) + c.1) = y - Quotient.out (mk c.1) := by abel
      rwa [e] at this
    exact ⟨_, ⟨hmem, hs⟩, fun s' hs' => (key s' hs'.1 hs'.2).trans (key _ hmem hs).symm⟩

end GlobalTheory.CompanionTheory.BZCore

end
