import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeviEmbMulSingle

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.InertSupp GlobalTheory.IndefiniteRowSideFullHecke.TameConstituentPlaces ValuativeRel Matrix MeasureTheory
open GlobalTheory.IwahoriInj (Deep)
open Filter Topology

namespace GlobalTheory.SBUniform

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Establish `hγ : (uniformizer k ^ a : ValueGroupWithZero k) ≠ 0` using `zpow_ne_zero _ uniformizer_ne_zero`. Unfold `Deep`. Rewrite using `[isOpen_iff_mem_nhds]`. Introduce `x hx`. Rewrite using `[IsValuativeTopology.mem_nhds_iff']`.

Use `⟨Units.mk0 _ hγ, fun z hz => ?_⟩` and prove the remaining obligations. Simplify using `only [Set.mem_ofPred_eq, Units.val_mk0] at hz hx ⊢`. Establish `h` using `(valuation k).map_add (z - x) x`. Rewrite `h` using `[sub_add_cancel]`. Conclude with `h.trans (max_le hz.le hx)`.
-/
theorem isOpen_deep (a : ℤ) : IsOpen {x : k | Deep a x} := by
  have hγ : (uniformizer k ^ a : ValueGroupWithZero k) ≠ 0 := zpow_ne_zero _ uniformizer_ne_zero
  unfold Deep
  rw [isOpen_iff_mem_nhds]
  intro x hx
  rw [IsValuativeTopology.mem_nhds_iff']
  refine ⟨Units.mk0 _ hγ, fun z hz => ?_⟩
  simp only [Set.mem_ofPred_eq, Units.val_mk0] at hz hx ⊢

  have h := (valuation k).map_add (z - x) x
  rw [sub_add_cancel] at h
  exact h.trans (max_le hz.le hx)

/- English proof (translation)
Take `⟨γ, hγ⟩` from `(IsValuativeTopology.mem_nhds_zero_iff s).1 hs`. Take `⟨M₀, hM₀⟩` from `exists_pow_lt₀ (uniformizer_lt_one (R := k)) γ`. Use `filter_upwards [eventually_ge_atTop M₀] with M hM x hx`. Apply `hγ` to reduce the goal to its premises. Unfold `Deep at hx`.

Use `show valuation k x < γ`. Establish `hle : uniformizer k ^ (M : ℤ) ≤ uniformizer k ^ (M₀ : ℤ)` using `zpow_le_zpow_right_of_le_one₀ uniformizer_pos uniformizer_lt_one.le (by exact_mod_cast hM)`. Establish `hM₀' : uniformizer k ^ (M₀ : ℤ) < γ` using `by rwa [zpow_natCast]`. Conclude with `hx.trans_lt (hle.trans_lt hM₀')`.
-/
theorem eventually_deep_subset {s : Set k} (hs : s ∈ 𝓝 (0 : k)) :
    ∀ᶠ M : ℕ in atTop, ∀ x : k, Deep (M : ℤ) x → x ∈ s := by
  obtain ⟨γ, hγ⟩ := (IsValuativeTopology.mem_nhds_zero_iff s).1 hs

  obtain ⟨M₀, hM₀⟩ := exists_pow_lt₀ (uniformizer_lt_one (R := k)) γ
  filter_upwards [eventually_ge_atTop M₀] with M hM x hx
  apply hγ
  unfold Deep at hx
  show valuation k x < γ
  have hle : uniformizer k ^ (M : ℤ) ≤ uniformizer k ^ (M₀ : ℤ) :=
    zpow_le_zpow_right_of_le_one₀ uniformizer_pos uniformizer_lt_one.le (by exact_mod_cast hM)
  have hM₀' : uniformizer k ^ (M₀ : ℤ) < γ := by rwa [zpow_natCast]
  exact hx.trans_lt (hle.trans_lt hM₀')

/- English proof (translation)
Establish `hs' : s ∈ 𝓝 (0 : n → n → k)` using `hs`. Rewrite `hs'` using `[nhds_pi]`. Take `⟨I, -, t, ht, hts⟩` from `Filter.mem_pi.1 hs'`. Establish `ht' : ∀ i, ∃ J : Set n, J.Finite ∧ ∃ u : n → Set k, (∀ j, u j ∈ 𝓝 (0 : k)) ∧ J.pi u ⊆ t i`. Introduce `i`.

Establish `hi : t i ∈ 𝓝 (0 : n → k)` using `ht i`. Rewrite `hi` using `[nhds_pi]`. Conclude with `Filter.mem_pi.1 hi`. Use `choose J _ u hu hJu using ht'`. Establish `hev : ∀ᶠ M : ℕ in atTop, ∀ i j, ∀ x : k, Deep (M : ℤ) x → x ∈ u i j`.

Rewrite using `[Filter.eventually_all]`. Introduce `i`. Rewrite using `[Filter.eventually_all]`. Introduce `j`. Conclude with `eventually_deep_subset (hu i j)`.

Take `⟨M, hM⟩` from `hev.exists`. Conclude with `⟨M, fun y hy => hts (Set.mem_pi.2 fun i _ => hJu i (Set.mem_pi.2 fun j _ => hM i j _ (hy i j)))⟩`.
-/
theorem exists_deep_subset {n : Type} [Fintype n] {s : Set (Matrix n n k)} (hs : s ∈ 𝓝 (0 : Matrix n n k)) :
    ∃ M : ℕ, ∀ y : Matrix n n k, (∀ i j, Deep (M : ℤ) (y i j)) → y ∈ s := by
  have hs' : s ∈ 𝓝 (0 : n → n → k) := hs
  rw [nhds_pi] at hs'
  obtain ⟨I, -, t, ht, hts⟩ := Filter.mem_pi.1 hs'

  have ht' : ∀ i, ∃ J : Set n, J.Finite ∧ ∃ u : n → Set k, (∀ j, u j ∈ 𝓝 (0 : k)) ∧ J.pi u ⊆ t i := by
    intro i
    have hi : t i ∈ 𝓝 (0 : n → k) := ht i
    rw [nhds_pi] at hi
    exact Filter.mem_pi.1 hi
  choose J _ u hu hJu using ht'
  have hev : ∀ᶠ M : ℕ in atTop, ∀ i j, ∀ x : k, Deep (M : ℤ) x → x ∈ u i j := by
    rw [Filter.eventually_all]
    intro i
    rw [Filter.eventually_all]
    intro j
    exact eventually_deep_subset (hu i j)
  obtain ⟨M, hM⟩ := hev.exists
  exact ⟨M, fun y hy => hts (Set.mem_pi.2 fun i _ => hJu i (Set.mem_pi.2 fun j _ => hM i j _ (hy i j)))⟩

/- English proof (translation)
Unfold `Deep at h ⊢`. Rewrite using `[Valuation.map_neg]` and apply the resulting hypothesis.
-/
private theorem deep_neg {a : ℤ} {x : k} (h : Deep a x) : Deep a (-x) := by
  unfold Deep at h ⊢
  rwa [Valuation.map_neg]

/- English proof (translation)
Unfold `Deep at hx hy ⊢`. Conclude with `((valuation k).map_add x y).trans (max_le hx hy)`.
-/
private theorem deep_add {a : ℤ} {x y : k} (hx : Deep a x) (hy : Deep a y) : Deep a (x + y) := by
  unfold Deep at hx hy ⊢
  exact ((valuation k).map_add x y).trans (max_le hx hy)

/- English proof (translation)
Unfold `Deep`. Simplify using the standard rewrite rules.
-/
private theorem deep_zero' (a : ℤ) : Deep a (0 : k) := by
  unfold Deep
  simp

/- English proof (translation)
Unfold `Deep at h ⊢`. Conclude with `h.trans (zpow_le_zpow_right_of_le_one₀ uniformizer_pos uniformizer_lt_one.le hab)`.
-/
private theorem deep_of_le' {a b : ℤ} (hab : a ≤ b) {x : k} (h : Deep b x) : Deep a x := by
  unfold Deep at h ⊢
  exact h.trans (zpow_le_zpow_right_of_le_one₀ uniformizer_pos uniformizer_lt_one.le hab)

/- English proof (translation)
Unfold `Deep`. Distinguish the cases in `hx : valuation k x = 0`. Conclude with `⟨0, by simp [hx]⟩`. Take `⟨N, hN⟩` from `exists_pow_lt₀ (uniformizer_lt_one (R := k)) (Units.mk0 _ (inv_ne_zero hx))`. Use `⟨N, ?_⟩` and prove the remaining obligations.

Rewrite `hN` using `[Units.val_mk0]`. Establish `hpos : (0 : ValueGroupWithZero k) < uniformizer k ^ N` using `pow_pos uniformizer_pos N`. Establish `hx0 : (0 : ValueGroupWithZero k) < valuation k x` using `zero_lt_iff.2 hx`. Rewrite using `[_root_.zpow_neg, zpow_natCast]`. Conclude with `((lt_inv_comm₀ hpos hx0).1 hN).le`.
-/
private theorem exists_deep_neg_natCast (x : k) : ∃ N : ℕ, Deep (-(N : ℤ)) x := by
  unfold Deep
  by_cases hx : valuation k x = 0
  · exact ⟨0, by simp [hx]⟩

  obtain ⟨N, hN⟩ := exists_pow_lt₀ (uniformizer_lt_one (R := k)) (Units.mk0 _ (inv_ne_zero hx))
  refine ⟨N, ?_⟩
  rw [Units.val_mk0] at hN
  have hpos : (0 : ValueGroupWithZero k) < uniformizer k ^ N := pow_pos uniformizer_pos N
  have hx0 : (0 : ValueGroupWithZero k) < valuation k x := zero_lt_iff.2 hx
  rw [_root_.zpow_neg, zpow_natCast]
  exact ((lt_inv_comm₀ hpos hx0).1 hN).le

/- English proof (translation)
Simplify using `only [Set.ofPred_forall]`. Conclude with `isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => (isOpen_deep (k := k) a).preimage (continuous_id.matrix_elem i j)`.
-/
private theorem isOpen_setOf_forall_deep {n : Type} [Fintype n] (a : ℤ) :
    IsOpen {y : Matrix n n k | ∀ i j, Deep a (y i j)} := by
  simp only [Set.ofPred_forall]
  exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
    (isOpen_deep (k := k) a).preimage (continuous_id.matrix_elem i j)

/- English proof (translation)
Introduce `k _ _ _ _ n _ _ Φ hΦ`. Establish `hΦ' : IsLocallyConstant Φ ∧ HasCompactSupport Φ` using `hΦ`. Take `⟨hlc, hcs⟩` from `hΦ'`. Establish `hC : IsCompact (tsupport Φ)` using `hcs`. Establish `hzero : ∀ z, z ∉ tsupport Φ → Φ z = 0` using `fun z hz => by`.

Assume the negation of the conclusion as `h`. Conclude with `hz (subset_tsupport Φ h)`. Set `U : ℕ → Set (Matrix n n k)` to `fun N => {x | ∀ i j, Deep (-(N : ℤ)) (x i j)}`. Establish `hUm : Monotone U` using `fun N N' h x hx i j => deep_of_le' (neg_le_neg (by exact_mod_cast h)) (hx i j)`. Establish `hUcov : tsupport Φ ⊆ ⋃ N, U N`.

Introduce `x _`. Establish `hev : ∀ᶠ N : ℕ in atTop, ∀ i j, Deep (-(N : ℤ)) (x i j)`. Rewrite using `[Filter.eventually_all]`. Introduce `i`. Rewrite using `[Filter.eventually_all]`.

Introduce `j`. Take `⟨N₀, hN₀⟩` from `exists_deep_neg_natCast (x i j)`. Use `filter_upwards [eventually_ge_atTop N₀] with N hN`. Conclude with `deep_of_le' (neg_le_neg (by exact_mod_cast hN)) hN₀`. Take `⟨N, hN⟩` from `hev.exists`.

Conclude with `Set.mem_iUnion.2 ⟨N, hN⟩`. Take `⟨N, hN⟩` from `hC.elim_directed_cover U (fun N => isOpen_setOf_forall_deep _) hUcov hUm.directed_le`. Set `W : ℕ → Set (Matrix n n k)` to `fun M => {x | ∀ y : Matrix n n k, (∀ i j, Deep (M : ℤ) (y i j)) → Φ (x + y) = Φ x}`. Establish `hWm : Monotone W` using `fun M M' h x hx y hy => hx y fun i j => deep_of_le' (by exact_mod_cast h) (hy i j)`. Establish `hWo : ∀ M, IsOpen (W M)`.

Introduce `M`. Rewrite using `[isOpen_iff_mem_nhds]`. Introduce `x hx`. Establish `hD : {y : Matrix n n k | ∀ i j, Deep (M : ℤ) (y i j)} ∈ 𝓝 (0 : Matrix n n k)` using `(isOpen_setOf_forall_deep _).mem_nhds fun i j => deep_zero' _`. Establish `hD' : (fun z : Matrix n n k => z - x) ⁻¹' {y | ∀ i j, Deep (M : ℤ) (y i j)} ∈ 𝓝 x`.

Apply `(continuous_id.sub continuous_const).continuousAt.preimage_mem_nhds` to reduce the goal to its premises. Simplify using `using hD`. Use `Filter.mem_of_superset hD' fun z hz y hy => ?_` and prove the remaining obligations. Establish `hz' : ∀ i j, Deep (M : ℤ) ((z - x) i j)` using `hz`. Establish `h1 : Φ (x + ((z - x) + y)) = Φ x` using `hx _ fun i j => by simpa using deep_add (hz' i j) (hy i j)`.

Establish `h2 : Φ (x + (z - x)) = Φ x` using `hx _ hz'`. Rewrite `h2` using `[add_sub_cancel]`. Establish `he : x + ((z - x) + y) = z + y` using `by abel`. Rewrite `h1` using `[he]`. Rewrite using `[h1, h2]`.

Establish `hWcov : tsupport Φ ⊆ ⋃ M, W M`. Introduce `x _`. Establish `hs : {y : Matrix n n k | Φ (x + y) = Φ x} ∈ 𝓝 (0 : Matrix n n k)`. Apply `IsOpen.mem_nhds` to reduce the goal to its premises. Conclude with `(hlc.isOpen_fiber (Φ x)).preimage (continuous_const.add continuous_id)`.

Simplify using the standard rewrite rules. Take `⟨M, hM⟩` from `exists_deep_subset hs`. Conclude with `Set.mem_iUnion.2 ⟨M, fun y hy => hM y hy⟩`. Take `⟨M, hM⟩` from `hC.elim_directed_cover W hWo hWcov hWm.directed_le`. Use `⟨N, M, fun x hx i j => hN (subset_tsupport Φ hx) i j, fun x y hy => ?_⟩` and prove the remaining obligations.

Distinguish the cases in `hx : x ∈ tsupport Φ`. Conclude with `hM hx y hy`. Distinguish the cases in `hxy : x + y ∈ tsupport Φ`. Establish `h` using `hM hxy (-y) fun i j => by simpa using deep_neg (hy i j)`. Rewrite `h` using `[add_neg_cancel_right]`.

Conclude with `h.symm`. Rewrite using `[hzero _ hx, hzero _ hxy]`.
-/
theorem exists_bound_period : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n], ∀ Φ ∈ SB (Matrix n n k),
    ∃ N M : ℕ, (∀ x, Φ x ≠ 0 → ∀ i j, Deep (-(N : ℤ)) (x i j)) ∧
      ∀ x y : Matrix n n k, (∀ i j, Deep (M : ℤ) (y i j)) → Φ (x + y) = Φ x := by
  intro k _ _ _ _ n _ _ Φ hΦ
  have hΦ' : IsLocallyConstant Φ ∧ HasCompactSupport Φ := hΦ
  obtain ⟨hlc, hcs⟩ := hΦ'
  have hC : IsCompact (tsupport Φ) := hcs
  have hzero : ∀ z, z ∉ tsupport Φ → Φ z = 0 := fun z hz => by
    by_contra h
    exact hz (subset_tsupport Φ h)

  let U : ℕ → Set (Matrix n n k) := fun N => {x | ∀ i j, Deep (-(N : ℤ)) (x i j)}
  have hUm : Monotone U := fun N N' h x hx i j =>
    deep_of_le' (neg_le_neg (by exact_mod_cast h)) (hx i j)
  have hUcov : tsupport Φ ⊆ ⋃ N, U N := by
    intro x _
    have hev : ∀ᶠ N : ℕ in atTop, ∀ i j, Deep (-(N : ℤ)) (x i j) := by
      rw [Filter.eventually_all]
      intro i
      rw [Filter.eventually_all]
      intro j
      obtain ⟨N₀, hN₀⟩ := exists_deep_neg_natCast (x i j)
      filter_upwards [eventually_ge_atTop N₀] with N hN
      exact deep_of_le' (neg_le_neg (by exact_mod_cast hN)) hN₀
    obtain ⟨N, hN⟩ := hev.exists
    exact Set.mem_iUnion.2 ⟨N, hN⟩
  obtain ⟨N, hN⟩ := hC.elim_directed_cover U (fun N => isOpen_setOf_forall_deep _) hUcov hUm.directed_le

  let W : ℕ → Set (Matrix n n k) :=
    fun M => {x | ∀ y : Matrix n n k, (∀ i j, Deep (M : ℤ) (y i j)) → Φ (x + y) = Φ x}
  have hWm : Monotone W := fun M M' h x hx y hy =>
    hx y fun i j => deep_of_le' (by exact_mod_cast h) (hy i j)
  have hWo : ∀ M, IsOpen (W M) := by
    intro M
    rw [isOpen_iff_mem_nhds]
    intro x hx
    have hD : {y : Matrix n n k | ∀ i j, Deep (M : ℤ) (y i j)} ∈ 𝓝 (0 : Matrix n n k) :=
      (isOpen_setOf_forall_deep _).mem_nhds fun i j => deep_zero' _
    have hD' : (fun z : Matrix n n k => z - x) ⁻¹' {y | ∀ i j, Deep (M : ℤ) (y i j)} ∈ 𝓝 x := by
      apply (continuous_id.sub continuous_const).continuousAt.preimage_mem_nhds
      simpa using hD
    refine Filter.mem_of_superset hD' fun z hz y hy => ?_
    have hz' : ∀ i j, Deep (M : ℤ) ((z - x) i j) := hz
    have h1 : Φ (x + ((z - x) + y)) = Φ x :=
      hx _ fun i j => by simpa using deep_add (hz' i j) (hy i j)
    have h2 : Φ (x + (z - x)) = Φ x := hx _ hz'
    rw [add_sub_cancel] at h2
    have he : x + ((z - x) + y) = z + y := by abel
    rw [he] at h1
    rw [h1, h2]
  have hWcov : tsupport Φ ⊆ ⋃ M, W M := by
    intro x _
    have hs : {y : Matrix n n k | Φ (x + y) = Φ x} ∈ 𝓝 (0 : Matrix n n k) := by
      apply IsOpen.mem_nhds
      · exact (hlc.isOpen_fiber (Φ x)).preimage (continuous_const.add continuous_id)
      · simp
    obtain ⟨M, hM⟩ := exists_deep_subset hs
    exact Set.mem_iUnion.2 ⟨M, fun y hy => hM y hy⟩
  obtain ⟨M, hM⟩ := hC.elim_directed_cover W hWo hWcov hWm.directed_le
  refine ⟨N, M, fun x hx i j => hN (subset_tsupport Φ hx) i j, fun x y hy => ?_⟩
  by_cases hx : x ∈ tsupport Φ
  · exact hM hx y hy
  by_cases hxy : x + y ∈ tsupport Φ
  · have h := hM hxy (-y) fun i j => by simpa using deep_neg (hy i j)
    rw [add_neg_cancel_right] at h
    exact h.symm
  · rw [hzero _ hx, hzero _ hxy]

end GlobalTheory.SBUniform
