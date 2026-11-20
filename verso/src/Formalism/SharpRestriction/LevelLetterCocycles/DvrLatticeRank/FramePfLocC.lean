import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.FramePfPt
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ModelFPfA
import Formalism.SharpRestriction.LevelLetterCocycles.MapCompZero

noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules TensorProduct

section Ser

variable {LL V : Type} [Field LL] [AddCommGroup V] [Module LL V]

/- English proof (translation)
Simplify using `only [serC]`. Rewrite using `[if_neg (by omega)]`.
-/
theorem framepf_serC_neg (f : PowerSeries LL) (d : V) (i : ℤ) (hi : i < 0) : serC f d i = 0 := by
  simp only [serC]
  rw [if_neg (by omega)]

/- English proof (translation)
Break down `lt_or_ge i 0 with hi | hi` into its components or cases. Rewrite using `[framepf_serC_neg _ _ _ hi]`. Simplify using `only [serMul]`. Establish `h0 : ∀ j : ℕ, PowerSeries.coeff j g • serC f d (i - j) = 0` using `fun j => by`. Rewrite using `[framepf_serC_neg _ _ _ (by omega), smul_zero]`.

Simplify using `[h0]`. Take `⟨n, rfl⟩` from `Int.eq_ofNat_of_zero_le hi`. Simplify using `only [serMul]`. Rewrite using `[finsum_eq_sum_of_support_subset _ (s := Finset.range (n + 1)) (by`. Introduce `j hj`.

Rewrite `hj` using `[Function.mem_support]`. Rewrite using `[Finset.coe_range, Set.mem_Iio]`. Assume the negation of the conclusion as `hjn`. Conclude with `hj (by rw [framepf_serC_neg _ _ _ (by omega), smul_zero]))]`. Establish `h1 : ∀ j ∈ Finset.range (n + 1), PowerSeries.coeff j g • serC f d ((n : ℤ) - j) = (PowerSeries.coeff j g * PowerSeries.coeff (n - j) f) • d`.

Introduce `j hj`. Rewrite `hj` using `[Finset.mem_range]`. Simplify using `only [serC]`. Rewrite using `[if_pos (by omega), show ((n : ℤ) - j).toNat = n - j by omega, smul_smul]`. Rewrite using `[Finset.sum_congr rfl h1, ← Finset.sum_smul]`.

Simplify using `only [serC]`. Rewrite using `[if_pos hi, PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]`. Simplify using the standard rewrite rules.
-/
theorem framepf_serMul_serC (g f : PowerSeries LL) (d : V) (i : ℤ) :
    serMul g (serC f d) i = serC (g * f) d i := by
  rcases lt_or_ge i 0 with hi | hi
  · rw [framepf_serC_neg _ _ _ hi]
    simp only [serMul]
    have h0 : ∀ j : ℕ, PowerSeries.coeff j g • serC f d (i - j) = 0 := fun j => by
      rw [framepf_serC_neg _ _ _ (by omega), smul_zero]
    simp [h0]
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hi
    simp only [serMul]
    rw [finsum_eq_sum_of_support_subset _ (s := Finset.range (n + 1)) (by
      intro j hj
      rw [Function.mem_support] at hj
      rw [Finset.coe_range, Set.mem_Iio]
      by_contra hjn
      exact hj (by rw [framepf_serC_neg _ _ _ (by omega), smul_zero]))]
    have h1 : ∀ j ∈ Finset.range (n + 1), PowerSeries.coeff j g • serC f d ((n : ℤ) - j) =
        (PowerSeries.coeff j g * PowerSeries.coeff (n - j) f) • d := by
      intro j hj
      rw [Finset.mem_range] at hj
      simp only [serC]
      rw [if_pos (by omega), show ((n : ℤ) - j).toNat = n - j by omega, smul_smul]
    rw [Finset.sum_congr rfl h1, ← Finset.sum_smul]
    simp only [serC]
    rw [if_pos hi, PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    simp

/- English proof (translation)
Simplify using `only [serMul]`. Use `finsum_congr (fun j => ?_)` and prove the remaining obligations. Distinguish the cases in `hj : j < m`. Rewrite using `[hg j hj, zero_smul, zero_smul]`. Rewrite using `[h (i - j) (by omega)]`.
-/
theorem framepf_serMul_congr (g : PowerSeries LL) (m : ℕ) (hg : ∀ j < m, PowerSeries.coeff j g = 0)
    (f f' : ℤ → V) (R : ℤ) (h : ∀ i < R, f i = f' i) (i : ℤ) (hi : i < R + m) :
    serMul g f i = serMul g f' i := by
  simp only [serMul]
  refine finsum_congr (fun j => ?_)
  by_cases hj : j < m
  · rw [hg j hj, zero_smul, zero_smul]
  · rw [h (i - j) (by omega)]

/- English proof (translation)
Simplify using `[serMul]`.
-/
theorem framepf_serMul_zero (g : PowerSeries LL) (i : ℤ) : serMul g (fun _ => (0 : V)) i = 0 := by
  simp [serMul]

/- English proof (translation)
Simplify using `only [serMul, Finset.smul_sum]`. Rewrite using `[finsum_sum_comm]`. Use `Finset.sum_congr rfl (fun t _ => ?_)` and prove the remaining obligations. Rewrite using `[← framepf_serMul_serC]`. Both sides reduce to the same expression.

Introduce `t _`. Use `(Set.finite_Iio (i.toNat + 1)).subset ?_` and prove the remaining obligations. Introduce `j hj`. Rewrite `hj` using `[Function.mem_support]`. Rewrite using `[Set.mem_Iio]`.

Assume the negation of the conclusion as `hjn`. Conclude with `hj (by rw [framepf_serC_neg _ _ _ (by omega), smul_zero])`.
-/
theorem framepf_serMul_sum {ι : Type} [Fintype ι] (g : PowerSeries LL) (f : ι → PowerSeries LL)
    (d : ι → V) (i : ℤ) :
    serMul g (fun k => ∑ j, serC (f j) (d j) k) i = ∑ j, serC (g * f j) (d j) i := by
  simp only [serMul, Finset.smul_sum]
  rw [finsum_sum_comm]
  · refine Finset.sum_congr rfl (fun t _ => ?_)
    rw [← framepf_serMul_serC]
    rfl
  · intro t _
    refine (Set.finite_Iio (i.toNat + 1)).subset ?_
    intro j hj
    rw [Function.mem_support] at hj
    rw [Set.mem_Iio]
    by_contra hjn
    exact hj (by rw [framepf_serC_neg _ _ _ (by omega), smul_zero])

/- English proof (translation)
Establish `key : ∀ t : ℕ, ∀ k : ℤ, k < R → k < m₀ + t → f k = f' k`. Introduce `t`. Proceed by induction on `t with`. Consider the case `zero`. Introduce `k _ hk`.

Rewrite using `[hf k (by omega), hf' k (by omega)]`. Consider the case `succ t ih`. Introduce `k hkR hk`. Break down `lt_or_ge k (m₀ + t) with hk' | hk'` into its components or cases. Conclude with `ih k hkR hk'`.

Break down `lt_or_ge k m₀ with hk0 | hk0` into its components or cases. Rewrite using `[hf k hk0, hf' k hk0]`. Establish `hs` using `h (k + m) (by omega)`. Simplify using `only [serMul] at hs`. Establish `hsupp : ∀ F : ℤ → V, (∀ x < m₀, F x = 0) → (Function.support fun j : ℕ => PowerSeries.coeff j g • F (k + m - j)) ⊆ ↑(Finset.range ((k + m - m₀).toNat + 1))`.

Introduce `F hF j hj`. Rewrite `hj` using `[Function.mem_support]`. Rewrite using `[Finset.coe_range, Set.mem_Iio]`. Assume the negation of the conclusion as `hjn`. Conclude with `hj (by rw [hF _ (by omega), smul_zero])`.

Rewrite `hs` using `[finsum_eq_sum_of_support_subset _ (hsupp f hf), finsum_eq_sum_of_support_subset _ (hsupp f' hf')]`. Establish `hmem : m ∈ Finset.range ((k + m - m₀).toNat + 1)`. Rewrite using `[Finset.mem_range]`. Use linear arithmetic over natural numbers and integers. Rewrite `hs` using `[← Finset.add_sum_erase _ _ hmem, ← Finset.add_sum_erase _ _ hmem]`.

Establish `hrest : ∑ j ∈ (Finset.range ((k + m - m₀).toNat + 1)).erase m, PowerSeries.coeff j g • f (k + m - j) = ∑ j ∈ (Finset.range ((k + m - m₀).toNat + 1)).erase m, PowerSeries.coeff j g • f' (k + m - j)`. Use `Finset.sum_congr rfl (fun j hj => ?_)` and prove the remaining obligations. Rewrite `hj` using `[Finset.mem_erase]`. Break down `lt_or_gt_of_ne hj.1 with hjm | hjm` into its components or cases. Rewrite using `[hg j hjm, zero_smul, zero_smul]`.

Rewrite using `[ih (k + m - j) (by omega) (by omega)]`. Rewrite `hs` using `[hrest, add_left_inj]`. Simplify using `only [add_sub_cancel_right] at hs`. Conclude with `smul_right_injective V hgm hs`. Conclude with `key ((i - m₀).toNat + 1) i hi (by omega)`.
-/
theorem framepf_serMul_cancel (g : PowerSeries LL) (m : ℕ) (hg : ∀ j < m, PowerSeries.coeff j g = 0)
    (hgm : PowerSeries.coeff m g ≠ 0) (f f' : ℤ → V) (m₀ : ℤ) (hf : ∀ k < m₀, f k = 0)
    (hf' : ∀ k < m₀, f' k = 0) (R : ℤ) (h : ∀ i < R + m, serMul g f i = serMul g f' i) (i : ℤ)
    (hi : i < R) : f i = f' i := by
  have key : ∀ t : ℕ, ∀ k : ℤ, k < R → k < m₀ + t → f k = f' k := by
    intro t
    induction t with
    | zero =>
      intro k _ hk
      rw [hf k (by omega), hf' k (by omega)]
    | succ t ih =>
      intro k hkR hk
      rcases lt_or_ge k (m₀ + t) with hk' | hk'
      · exact ih k hkR hk'
      rcases lt_or_ge k m₀ with hk0 | hk0
      · rw [hf k hk0, hf' k hk0]
      have hs := h (k + m) (by omega)
      simp only [serMul] at hs
      have hsupp : ∀ F : ℤ → V, (∀ x < m₀, F x = 0) →
          (Function.support fun j : ℕ => PowerSeries.coeff j g • F (k + m - j)) ⊆
            ↑(Finset.range ((k + m - m₀).toNat + 1)) := by
        intro F hF j hj
        rw [Function.mem_support] at hj
        rw [Finset.coe_range, Set.mem_Iio]
        by_contra hjn
        exact hj (by rw [hF _ (by omega), smul_zero])
      rw [finsum_eq_sum_of_support_subset _ (hsupp f hf),
        finsum_eq_sum_of_support_subset _ (hsupp f' hf')] at hs
      have hmem : m ∈ Finset.range ((k + m - m₀).toNat + 1) := by
        rw [Finset.mem_range]
        omega
      rw [← Finset.add_sum_erase _ _ hmem, ← Finset.add_sum_erase _ _ hmem] at hs
      have hrest : ∑ j ∈ (Finset.range ((k + m - m₀).toNat + 1)).erase m,
            PowerSeries.coeff j g • f (k + m - j) =
          ∑ j ∈ (Finset.range ((k + m - m₀).toNat + 1)).erase m,
            PowerSeries.coeff j g • f' (k + m - j) := by
        refine Finset.sum_congr rfl (fun j hj => ?_)
        rw [Finset.mem_erase] at hj
        rcases lt_or_gt_of_ne hj.1 with hjm | hjm
        · rw [hg j hjm, zero_smul, zero_smul]
        · rw [ih (k + m - j) (by omega) (by omega)]
      rw [hrest, add_left_inj] at hs
      simp only [add_sub_cancel_right] at hs
      exact smul_right_injective V hgm hs
  exact key ((i - m₀).toNat + 1) i hi (by omega)

end Ser

section Local

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {W : LocWach PD LL O v n}
    {Zl Ai : Type} [CommRing Zl] [CommRing Ai] [Algebra Zl O] [Algebra Zl Ai]
    {RW : Type} [CommRing RW] [Algebra O RW]
    {inclR : (O ⊗[Zl] Ai) →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : O ⊗[Zl] Ai}
    {E : EtTie W (O ⊗[Zl] Ai) RW inclR φR gR πA} {ιdR : Ai →+* BdR} {p1 : Ai} {tS zS : BdR}
    (Ct : CmpTie W E ιdR p1 tS zS) (T : LocLat G Qp LL O)

include Ct in
/- English proof (translation)
Establish `h1` using `Ct.levN_eq T i 1 x r`. Rewrite `h1` using `[hneg x r hr]`. Establish `hinj : Function.Injective (ιV PD (LL` using `LL) (V := T.V)) := by`. Establish `h2` using `Module.Flat.lTensor_preserves_injective_linearMap (M := T.V) (PD.ι.toLinearMap.restrictScalars Qp) PD.ι_inj`. Use `h2 using 1` and compare the differences between its conclusion and the goal.

Use function extensionality and compare the values at `y`. Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a b => simp [ιV, AlgebraTensorModule.map_tmul, LinearMap.lTensor_tmul]`. Consider the case `add a b ha hb => simp only [map_add, ha, hb]`.

Conclude with `hinj (by rw [← h1, map_zero])`.
-/
theorem framepf_levB_neg (i : ZMod n)
    (hneg : ∀ (x : ↥(W.N T)) (k : ℤ), k < 0 → W.levN T i 1 x k = 0) (x : ↥(W.N T)) (r : ℤ)
    (hr : r < 0) : Ct.levB T i 1 x r = 0 := by
  have h1 := Ct.levN_eq T i 1 x r
  rw [hneg x r hr] at h1
  have hinj : Function.Injective (ιV PD (LL := LL) (V := T.V)) := by
    have h2 := Module.Flat.lTensor_preserves_injective_linearMap (M := T.V)
      (PD.ι.toLinearMap.restrictScalars Qp) PD.ι_inj
    convert h2 using 1
    funext y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [ιV, AlgebraTensorModule.map_tmul, LinearMap.lTensor_tmul]
    | add a b ha hb => simp only [map_add, ha, hb]
  exact hinj (by rw [← h1, map_zero])

/- English proof (translation)
Take `⟨d, rfl⟩` from `Nat.exists_eq_add_of_le hm`. Rewrite using `[pow_add, mul_comm, mul_smul]`. Conclude with `Submodule.smul_mem _ _ h`.
-/
theorem framepf_Qpow_mem {p : W.DD T} {m₀ m : ℕ} (h : W.Q ^ m₀ • p ∈ W.N T) (hm : m₀ ≤ m) :
    W.Q ^ m • p ∈ W.N T := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hm
  rw [pow_add, mul_comm, mul_smul]
  exact Submodule.smul_mem _ _ h

include Ct in

/- English proof (translation)
Proceed by induction on `hp using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨z, hz, rfl⟩` from `hx`. Take `⟨k, hk⟩` from `W.N_φ T z hz`. Use `⟨k, fun m hm => ⟨framepf_Qpow_mem T hk hm, fun i hi => ?_⟩⟩` and prove the remaining obligations.

Establish `hQ : ∀ j < m, PowerSeries.coeff j (W.lev c ζ (W.Q ^ m)) = 0` using `fun j hj => by`. Rewrite using `[map_pow]`. Conclude with `framepf_coeff_pow_lt _ hQ0 _ _ hj`. Rewrite using `[Ct.levN_eq, framepf_levB_phi Ct T hc c ζ ⟨1, by simpa using hζ⟩ hζ.pow_eq_one ⟨z, hz⟩ m 0 (framepf_Qpow_mem T hk hm) hQ (framepf_levB_neg Ct T (c - 1) hneg _) (fun r h1 h2 => by omega) i (by omega)]`. Unfold `serC`.

Use `split_ifs with h0`. Rewrite using `[hQ _ (by omega), zero_smul, map_zero]`. Rewrite using `[map_zero]`. Consider the case `zero`. Use `⟨0, fun m _ => ⟨by simp, fun i _ => ?_⟩⟩` and prove the remaining obligations.

Establish `: (⟨W.Q ^ m • (0 : W.DD T), by simp⟩ : ↥(W.N T)) = 0` using `Subtype.ext (by simp)`. Rewrite using `[this, map_zero, Pi.zero_apply]`. Consider the case `add x y _ _ hx hy`. Take `⟨m₁, h₁⟩` from `hx`. Take `⟨m₂, h₂⟩` from `hy`.

Use `⟨max m₁ m₂, fun m hm => ?_⟩` and prove the remaining obligations. Take `⟨a₁, b₁⟩` from `h₁ m (le_of_max_le_left hm)`. Take `⟨a₂, b₂⟩` from `h₂ m (le_of_max_le_right hm)`. Establish `hN : W.Q ^ m • (x + y) ∈ W.N T` using `by rw [smul_add]; exact (W.N T).add_mem a₁ a₂`. Use `⟨hN, fun i hi => ?_⟩` and prove the remaining obligations.

Establish `: (⟨_, hN⟩ : ↥(W.N T)) = ⟨_, a₁⟩ + ⟨_, a₂⟩` using `Subtype.ext (smul_add _ _ _)`. Rewrite using `[this, map_add, Pi.add_apply, b₁ i hi, b₂ i hi, add_zero]`. Consider the case `smul s x _ hx`. Take `⟨m₁, h₁⟩` from `hx`. Use `⟨m₁, fun m hm => ?_⟩` and prove the remaining obligations.

Take `⟨a₁, b₁⟩` from `h₁ m hm`. Establish `hN : W.Q ^ m • (s • x) ∈ W.N T` using `by rw [smul_comm]; exact (W.N T).smul_mem _ a₁`. Use `⟨hN, fun i hi => ?_⟩` and prove the remaining obligations. Establish `: (⟨_, hN⟩ : ↥(W.N T)) = s • ⟨_, a₁⟩` using `Subtype.ext (smul_comm _ _ _)`. Rewrite using `[this, ModelFPf.levN_eq_serMul, framepf_serMul_congr _ 0 (fun j hj => by omega) _ (fun _ => 0) m b₁ i (by omega), framepf_serMul_zero]`.
-/
theorem framepf_span_vanish (hc : IsCrys PD T.ρ) (c : ZMod n) (ζ : LL) (hζ : IsPrimitiveRoot ζ PD.p)
    (hQ0 : PowerSeries.constantCoeff (W.lev c ζ W.Q) = 0)
    (hneg : ∀ (x : ↥(W.N T)) (k : ℤ), k < 0 → W.levN T (c - 1) 1 x k = 0) {p : W.DD T}
    (hp : p ∈ Submodule.span (LetA O n) (W.φD T '' (W.N T : Set (W.DD T)))) :
    ∃ m₀ : ℕ, ∀ m ≥ m₀, ∃ h : W.Q ^ m • p ∈ W.N T, ∀ i : ℤ, i < m → W.levN T c ζ ⟨_, h⟩ i = 0 := by
  induction hp using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨z, hz, rfl⟩ := hx
    obtain ⟨k, hk⟩ := W.N_φ T z hz
    refine ⟨k, fun m hm => ⟨framepf_Qpow_mem T hk hm, fun i hi => ?_⟩⟩
    have hQ : ∀ j < m, PowerSeries.coeff j (W.lev c ζ (W.Q ^ m)) = 0 := fun j hj => by
      rw [map_pow]; exact framepf_coeff_pow_lt _ hQ0 _ _ hj
    rw [Ct.levN_eq, framepf_levB_phi Ct T hc c ζ ⟨1, by simpa using hζ⟩ hζ.pow_eq_one ⟨z, hz⟩ m 0
      (framepf_Qpow_mem T hk hm) hQ (framepf_levB_neg Ct T (c - 1) hneg _) (fun r h1 h2 => by omega) i
      (by omega)]
    unfold serC
    split_ifs with h0
    · rw [hQ _ (by omega), zero_smul, map_zero]
    · rw [map_zero]
  | zero =>
    refine ⟨0, fun m _ => ⟨by simp, fun i _ => ?_⟩⟩
    have : (⟨W.Q ^ m • (0 : W.DD T), by simp⟩ : ↥(W.N T)) = 0 := Subtype.ext (by simp)
    rw [this, map_zero, Pi.zero_apply]
  | add x y _ _ hx hy =>
    obtain ⟨m₁, h₁⟩ := hx
    obtain ⟨m₂, h₂⟩ := hy
    refine ⟨max m₁ m₂, fun m hm => ?_⟩
    obtain ⟨a₁, b₁⟩ := h₁ m (le_of_max_le_left hm)
    obtain ⟨a₂, b₂⟩ := h₂ m (le_of_max_le_right hm)
    have hN : W.Q ^ m • (x + y) ∈ W.N T := by rw [smul_add]; exact (W.N T).add_mem a₁ a₂
    refine ⟨hN, fun i hi => ?_⟩
    have : (⟨_, hN⟩ : ↥(W.N T)) = ⟨_, a₁⟩ + ⟨_, a₂⟩ := Subtype.ext (smul_add _ _ _)
    rw [this, map_add, Pi.add_apply, b₁ i hi, b₂ i hi, add_zero]
  | smul s x _ hx =>
    obtain ⟨m₁, h₁⟩ := hx
    refine ⟨m₁, fun m hm => ?_⟩
    obtain ⟨a₁, b₁⟩ := h₁ m hm
    have hN : W.Q ^ m • (s • x) ∈ W.N T := by rw [smul_comm]; exact (W.N T).smul_mem _ a₁
    refine ⟨hN, fun i hi => ?_⟩
    have : (⟨_, hN⟩ : ↥(W.N T)) = s • ⟨_, a₁⟩ := Subtype.ext (smul_comm _ _ _)
    rw [this, ModelFPf.levN_eq_serMul, framepf_serMul_congr _ 0 (fun j hj => by omega) _ (fun _ => 0) m
      b₁ i (by omega), framepf_serMul_zero]

include Ct in

/- English proof (translation)
Take `⟨m₀, hm₀⟩` from `framepf_span_vanish Ct T hc c ζ hζ hQ0 hneg hp`. Use `choose e he using fun j => W.N_φ T (h j : W.DD T) (h j).2`. Use `set d : ℕ := m₀ + ∑ j, e j with hd`. Take `⟨hpN, hp0⟩` from `hm₀ (d + k) (by omega)`. Establish `hj : ∀ j, W.Q ^ (d + k) • W.φD T (h j : W.DD T) ∈ W.N T` using `fun j => framepf_Qpow_mem T (he j) (by`.

Use `Finset.single_le_sum (f := e) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)` as an intermediate fact. Use the proof step `omega)`. Establish `heq : W.Q ^ d • (⟨_, hk⟩ : ↥(W.N T)) = ∑ j, ((letE c : LetA O n) * a j) • (⟨_, hj j⟩ : ↥(W.N T)) + g • ⟨_, hpN⟩`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `only [Submodule.coe_smul, Submodule.coe_add, Submodule.coe_sum]`.

Rewrite using `[smul_smul, ← pow_add, hu, smul_add, Finset.smul_sum, smul_comm _ g]`. Use `congr 1`. Conclude with `Finset.sum_congr rfl fun j _ => smul_comm _ _ _`. Take `⟨m₁, hm₁⟩` from `W.levN_supp T c ζ ⟨_, hk⟩`. Use `framepf_serMul_cancel (W.lev c ζ (W.Q ^ d)) d (fun j hj => by rw [map_pow]; exact framepf_coeff_pow_lt _ hQ0 _ _ hj) (by rw [map_pow, framepf_coeff_pow_self _ hQ0]; exact pow_ne_zero _ hQ1) (W.levN T c ζ ⟨_, hk⟩) (fun i => ∑ j, serC (W.lev c ζ (W.Q ^ k) * W.lev c ζ (a j)) (valAt …` and prove the remaining obligations.

Rewrite using `[← ModelFPf.levN_eq_serMul, heq, map_add, map_sum, Pi.add_apply, Finset.sum_apply, framepf_serMul_sum, ModelFPf.levN_eq_serMul W T c ζ g, framepf_serMul_congr _ R hg _ (fun _ => 0) ((d + k : ℕ) : ℤ) hp0 r (by push_cast; omega), framepf_serMul_zero, add_zero]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[ModelFPf.levN_eq_serMul, framepf_serMul_congr _ 0 (fun j hj => by omega) _ (serC (W.lev c ζ (W.Q ^ (d + k))) (valAt W T c ζ (h j : W.DD T))) (((d + k : ℕ) : ℤ) + R) (fun s hs => framepf_levN_phi Ct T hc c ζ ⟨1, by simpa using hζ⟩ hζ.pow_eq_one hQ0 hQ1 (h j) (d + k) R (hj j) (fra …`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem framepf_loc_core (hc : IsCrys PD T.ρ) (c : ZMod n) (ζ : LL) (hζ : IsPrimitiveRoot ζ PD.p)
    (hQ0 : PowerSeries.constantCoeff (W.lev c ζ W.Q) = 0)
    (hQ1 : PowerSeries.coeff 1 (W.lev c ζ W.Q) ≠ 0)
    (hneg : ∀ (x : ↥(W.N T)) (k : ℤ), k < 0 → W.levN T (c - 1) 1 x k = 0) (R : ℕ) {m : ℕ}
    (a : Fin m → LetA O n) (h : Fin m → ↥(W.N T))
    (hmid : ∀ j (r : ℤ), 1 ≤ r → r < R → Ct.levB T (c - 1) 1 (h j) r = 0)
    (g : LetA O n) (hg : ∀ j < R, PowerSeries.coeff j (W.lev c ζ g) = 0) (p : W.DD T)
    (hp : p ∈ Submodule.span (LetA O n) (W.φD T '' (W.N T : Set (W.DD T)))) (u : W.DD T)
    (hu : u = ∑ j, ((letE c : LetA O n) * a j) • W.φD T (h j : W.DD T) + g • p)
    (k : ℕ) (hk : W.Q ^ k • u ∈ W.N T) (i : ℤ) (hi : i < k + R) :
    W.levN T c ζ ⟨_, hk⟩ i =
      ∑ j, serC (W.lev c ζ (W.Q ^ k) * W.lev c ζ (a j)) (valAt W T c ζ (h j : W.DD T)) i := by
  obtain ⟨m₀, hm₀⟩ := framepf_span_vanish Ct T hc c ζ hζ hQ0 hneg hp
  choose e he using fun j => W.N_φ T (h j : W.DD T) (h j).2
  set d : ℕ := m₀ + ∑ j, e j with hd
  obtain ⟨hpN, hp0⟩ := hm₀ (d + k) (by omega)
  have hj : ∀ j, W.Q ^ (d + k) • W.φD T (h j : W.DD T) ∈ W.N T := fun j =>
    framepf_Qpow_mem T (he j) (by
      have := Finset.single_le_sum (f := e) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
      omega)
  have heq : W.Q ^ d • (⟨_, hk⟩ : ↥(W.N T)) =
      ∑ j, ((letE c : LetA O n) * a j) • (⟨_, hj j⟩ : ↥(W.N T)) + g • ⟨_, hpN⟩ := by
    apply Subtype.ext
    simp only [Submodule.coe_smul, Submodule.coe_add, Submodule.coe_sum]
    rw [smul_smul, ← pow_add, hu, smul_add, Finset.smul_sum, smul_comm _ g]
    congr 1
    exact Finset.sum_congr rfl fun j _ => smul_comm _ _ _
  obtain ⟨m₁, hm₁⟩ := W.levN_supp T c ζ ⟨_, hk⟩
  refine framepf_serMul_cancel (W.lev c ζ (W.Q ^ d)) d
    (fun j hj => by rw [map_pow]; exact framepf_coeff_pow_lt _ hQ0 _ _ hj)
    (by rw [map_pow, framepf_coeff_pow_self _ hQ0]; exact pow_ne_zero _ hQ1)
    (W.levN T c ζ ⟨_, hk⟩)
    (fun i => ∑ j, serC (W.lev c ζ (W.Q ^ k) * W.lev c ζ (a j)) (valAt W T c ζ (h j : W.DD T)) i)
    (min m₁ 0) (fun r hr => hm₁ r (by omega))
    (fun r hr => Finset.sum_eq_zero fun j _ => framepf_serC_neg _ _ _ (by omega)) (k + R)
    (fun r hr => ?_) i hi
  rw [← ModelFPf.levN_eq_serMul, heq, map_add, map_sum, Pi.add_apply, Finset.sum_apply,
    framepf_serMul_sum, ModelFPf.levN_eq_serMul W T c ζ g,
    framepf_serMul_congr _ R hg _ (fun _ => 0) ((d + k : ℕ) : ℤ) hp0 r (by push_cast; omega),
    framepf_serMul_zero, add_zero]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [ModelFPf.levN_eq_serMul, framepf_serMul_congr _ 0 (fun j hj => by omega) _
    (serC (W.lev c ζ (W.Q ^ (d + k))) (valAt W T c ζ (h j : W.DD T))) (((d + k : ℕ) : ℤ) + R)
    (fun s hs => framepf_levN_phi Ct T hc c ζ ⟨1, by simpa using hζ⟩ hζ.pow_eq_one hQ0 hQ1 (h j)
      (d + k) R (hj j) (framepf_levB_neg Ct T (c - 1) hneg _) (hmid j) s hs) r (by push_cast; omega),
    framepf_serMul_serC, map_mul, ModelFPf.lev_letE, pow_add, map_mul]
  congr 1
  ring

include Ct in

/- English proof (translation)
Establish `hv : ∀ x : ↥(W.N T), valAt W T c ζ (x : W.DD T) = ιV PD (LL` using `LL) (V := T.V) (φVB PD (LL := LL) (V := T.V) (Ct.levB T (c - 1) 1 x 0)) := fun x => framepf_valAt Ct T hc c ζ ⟨1, by simpa using hζ⟩ hζ.pow_eq_one hQ0 hQ1 x (framepf_levB_neg Ct T (c - 1) hneg _) (W.N_φ T x x.2)`. Establish `e' : h = N • z + π' • w`. Apply `Subtype.ext` to reduce the goal to its premises. Establish `: ((N • z + π' • w : ↥(W.N T)) : W.DD T) = N • (z : W.DD T) + π' • (w : W.DD T)` using `rfl`. Rewrite using `[this, ← e]`.

Normalize the expressions using the abelian group laws. Establish `h0 : Ct.levB T (c - 1) 1 (π' • w) 0 = 0`. Apply `framepf_ιV_inj (PD := PD) T` to reduce the goal to its premises. Rewrite using `[← Ct.levN_eq, map_zero, ModelFPf.levN_eq_serMul, framepf_serMul_congr _ 1 (fun j hj => by`. Take `rfl : j = 0` from `by omega`.

Rewrite using `[PowerSeries.coeff_zero_eq_constantCoeff_apply, hπ]) _ (fun _ => 0) 0 (hneg w) 0 (by omega),`. Use the proof step `framepf_serMul_zero]`. Rewrite using `[hv, hv, e', map_add, Pi.add_apply, h0, add_zero, map_nsmul, Pi.smul_apply, map_nsmul, map_nsmul]`.
-/
theorem framepf_valAt_mod (hc : IsCrys PD T.ρ) (c : ZMod n) (ζ : LL) (hζ : IsPrimitiveRoot ζ PD.p)
    (hQ0 : PowerSeries.constantCoeff (W.lev c ζ W.Q) = 0)
    (hQ1 : PowerSeries.coeff 1 (W.lev c ζ W.Q) ≠ 0)
    (hneg : ∀ (x : ↥(W.N T)) (k : ℤ), k < 0 → W.levN T (c - 1) 1 x k = 0) (π' : LetA O n)
    (hπ : PowerSeries.constantCoeff (W.lev (c - 1) 1 π') = 0) (N : ℕ) (h z w : ↥(W.N T))
    (e : (h : W.DD T) - N • (z : W.DD T) = π' • (w : W.DD T)) :
    valAt W T c ζ (h : W.DD T) = N • valAt W T c ζ (z : W.DD T) := by
  have hv : ∀ x : ↥(W.N T), valAt W T c ζ (x : W.DD T) =
      ιV PD (LL := LL) (V := T.V) (φVB PD (LL := LL) (V := T.V) (Ct.levB T (c - 1) 1 x 0)) := fun x =>
    framepf_valAt Ct T hc c ζ ⟨1, by simpa using hζ⟩ hζ.pow_eq_one hQ0 hQ1 x
      (framepf_levB_neg Ct T (c - 1) hneg _) (W.N_φ T x x.2)
  have e' : h = N • z + π' • w := by
    apply Subtype.ext
    have : ((N • z + π' • w : ↥(W.N T)) : W.DD T) = N • (z : W.DD T) + π' • (w : W.DD T) := rfl
    rw [this, ← e]
    abel
  have h0 : Ct.levB T (c - 1) 1 (π' • w) 0 = 0 := by
    apply framepf_ιV_inj (PD := PD) T
    rw [← Ct.levN_eq, map_zero, ModelFPf.levN_eq_serMul,
      framepf_serMul_congr _ 1 (fun j hj => by
        obtain rfl : j = 0 := by omega
        rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, hπ]) _ (fun _ => 0) 0 (hneg w) 0 (by omega),
      framepf_serMul_zero]
  rw [hv, hv, e', map_add, Pi.add_apply, h0, add_zero, map_nsmul, Pi.smul_apply, map_nsmul, map_nsmul]

/- English proof (translation)
Take `⟨E, hE1, -, hE⟩` from `W.lev_π i 1 ⟨0, by rw [pow_zero]; exact IsPrimitiveRoot.one⟩`. Simplify `congrArg PowerSeries.constantCoeff hE` using `[hE1]`.
-/
theorem framepf_lev_π_one (i : ZMod n) : PowerSeries.constantCoeff (W.lev i 1 letπ) = 0 := by
  obtain ⟨E, hE1, -, hE⟩ := W.lev_π i 1 ⟨0, by rw [pow_zero]; exact IsPrimitiveRoot.one⟩
  simpa [hE1] using congrArg PowerSeries.constantCoeff hE

include Ct in

/- English proof (translation)
Take `⟨hQ0, hQ1⟩` from `framepf_Q_at W hs c ζ hζ`. Take `⟨hz, hrep⟩` from `hrep`. Take `⟨p, hp, hpe⟩` from `hxy`. Establish `hpe' : (π' ^ M * Eπ ^ (3 * h')) • p = Ψ x - y` using `hpe`. Establish `hπ1 : PowerSeries.constantCoeff (W.lev (c - 1) 1 π') = 0`.

Rewrite using `[hπ, map_mul, map_pow, map_mul, map_pow, framepf_lev_π_one, zero_pow (by omega), mul_zero]`. Establish `hE0 : PowerSeries.constantCoeff (W.lev c ζ Eπ) = 0`. Establish `h0` using `hQ0`. Rewrite `h0` using `[framepf_Q_eq_q W hs, hq, map_mul, map_mul]`. Conclude with `(mul_eq_zero.1 h0).resolve_left ((hw'.map (W.lev c ζ)).map PowerSeries.constantCoeff).ne_zero`.

Establish `hsm : ∀ (b : LetA O n) (t : LA W T π' c), Ψ (smulLA W T π' c b t) = b • Ψ t`. Introduce `b t`. Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul e ℓ`.

Establish `: smulLA W T π' c b (e ⊗ₜ ℓ) = (algebraMap (LetA O n) W.EE b * e) ⊗ₜ ℓ` using `rfl`. Rewrite using `[this, hΨ, hΨ, mul_smul, algebraMap_smul]`. Consider the case `add x y hx hy => rw [map_add, map_add, hx, hy, map_add, smul_add]`. Establish `hΛ : Eπ ^ h' • Ψ x = ∑ j, ((letE c : LetA O n) * a j) • W.φD T (hh (mkL W T π' c (z j) (hz j)))`. Rewrite using `[← hsm, hrep, map_sum]`.

Conclude with `Finset.sum_congr rfl fun j _ => by rw [hΨ, algebraMap_smul]`. Establish `hmid : ∀ ℓ (r : ℤ), 1 ≤ r → r < (4 * h' : ℕ) → Ct.levB T (c - 1) 1 ⟨hh ℓ, hN ℓ⟩ r = 0`. Introduce `ℓ r h1 h2`. Take `⟨⟨t, ht, hte⟩, -⟩` from `(mem_PiNS W T π' M _).1 (hγ ℓ)`. Use `framepf_levB_zero Ct T hc (c - 1) hv hχ (π' ^ M) (4 * h') (fun j hj => ?_) ⟨hh ℓ, hN ℓ⟩ ⟨t, ht⟩ hte.symm (hneg _) r h1 h2` and prove the remaining obligations.

Take `⟨f, hf⟩` from `PowerSeries.X_dvd_iff.2 (framepf_lev_π_one (W := W) (c - 1))`. Establish `: W.lev (c - 1) 1 (π' ^ M) = PowerSeries.X ^ (s' * M) * (W.lev (c - 1) 1 w ^ M * f ^ (s' * M))`. Rewrite using `[hπ, map_pow, map_mul, map_pow, hf]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this, PowerSeries.coeff_X_pow_mul', if_neg (by omega)]`.

Establish `key` using `framepf_loc_core Ct T hc c ζ hζ hQ0 hQ1 hneg (4 * h') (fun j => (a j : LetA O n)) (fun j => ⟨_, hN (mkL W T π' c (z j) (hz j))⟩) (fun j => hmid _) (-(π' ^ M * Eπ ^ (4 * h'))) (fun j hj => by`. Take `⟨f, hf⟩` from `PowerSeries.X_dvd_iff.2 hE0`. Establish `: W.lev c ζ (-(π' ^ M * Eπ ^ (4 * h'))) = PowerSeries.X ^ (4 * h') * (-(W.lev c ζ π' ^ M * f ^ (4 * h')))`. Rewrite using `[map_neg, map_mul, map_pow, map_pow, hf]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[this, PowerSeries.coeff_X_pow_mul', if_neg (by omega)]) p`. Use the proof step `(Submodule.span_mono (Set.image_mono fun _ hx => Formalism.MainNotions.LiftingTheory.wmap_Nl_le W T (c - 1) hx) hp.1.1)`. Use the proof step `(Eπ ^ h' • y) (by`. Rewrite using `[← hΛ, show y = Ψ x - (π' ^ M * Eπ ^ (3 * h')) • p by rw [hpe']; abel, smul_sub, smul_smul, neg_smul, sub_eq_add_neg]`. Use `congr 3`.

Use the proof step `ring) k hk i (by push_cast; omega)`. Rewrite using `[key]`. Unfold `expS`. Rewrite using `[framepf_serMul_sum, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Take `⟨⟨t, ht, hte⟩, -⟩` from `(mem_PiNS W T π' 1 _).1 (hmod (z j) (hz j))`. Establish `hval` using `framepf_valAt_mod Ct T hc c ζ hζ hQ0 hQ1 hneg π' hπ1 (PD.p ^ σ) ⟨_, hN (mkL W T π' c (z j) (hz j))⟩ ⟨z j, ((mem_NcS W T (c - 1) _).1 (hz j)).1⟩ ⟨t, ht⟩ (by`. Rewrite `hte` using `[pow_one]`. Rewrite using `[hte, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul])`. Simplify using `only at hval ⊢`.

Rewrite using `[hval]`. Unfold `serC`. Use `split_ifs`. Rewrite using `[smul_comm]`. Rewrite using `[smul_zero]`.
-/
theorem framepf_locC (hc : IsCrys PD T.ρ) (hs : W.s = 1) (c : ZMod n) (ζ : LL)
    (hζ : IsPrimitiveRoot ζ PD.p)
    (hneg : ∀ (x : ↥(W.N T)) (k : ℤ), k < 0 → W.levN T (c - 1) 1 x k = 0)
    (hv : (0 : WithTop ℚ) ≤ v (algebraMap O LL (W.χΓ W.gam : O) - 1))
    (hχ : ∀ r : ℤ, 1 ≤ r → (algebraMap O LL (W.χΓ W.gam : O)) ^ r ≠ 1)
    (π' Eπ w w' : LetA O n) (s' h' M σ : ℕ) (hs' : 1 ≤ s') (hπ : π' = w * letπ ^ s')
    (hw' : IsUnit w') (hq : W.q = w' * Eπ) (hM : 4 * h' ≤ s' * M)
    (hh : LcQ W T π' c →ₗ[O] W.DD T) (hN : ∀ ℓ, hh ℓ ∈ W.N T)
    (hγ : ∀ ℓ, W.γD T W.gam (hh ℓ) - hh ℓ ∈ PiNS W T π' M)
    (hmod : ∀ z hz, hh (mkL W T π' c z hz) - ((PD.p : ℕ) : O) ^ σ • z ∈ PiNS W T π' 1)
    (Ψ : W.EE ⊗[O] LcQ W T π' c →ₗ[W.EE] W.DD T) (hΨ : ∀ e ℓ, Ψ (e ⊗ₜ ℓ) = e • W.φD T (hh ℓ))
    (x : LA W T π' c) (y : W.DD T) (hxy : Ψ x - y ∈ JP W T π' Eπ h' M c)
    (m : ℕ) (a : Fin m → ↥W.AΔ) (z : Fin m → W.DD T) (hrep : IsRepL W T π' Eπ h' c x a z)
    (k : ℕ) (hk : W.Q ^ k • (Eπ ^ h' • y) ∈ W.N T) (i : ℤ) (hi : i < k + 4 * h') :
    W.levN T c ζ ⟨_, hk⟩ i =
      (PD.p ^ σ) • serMul (W.lev c ζ (W.Q ^ k)) (expS W T c ζ (fun j => (a j : LetA O n)) z) i := by
  obtain ⟨hQ0, hQ1⟩ := framepf_Q_at W hs c ζ hζ
  obtain ⟨hz, hrep⟩ := hrep
  obtain ⟨p, hp, hpe⟩ := hxy
  have hpe' : (π' ^ M * Eπ ^ (3 * h')) • p = Ψ x - y := hpe
  have hπ1 : PowerSeries.constantCoeff (W.lev (c - 1) 1 π') = 0 := by
    rw [hπ, map_mul, map_pow, map_mul, map_pow, framepf_lev_π_one, zero_pow (by omega), mul_zero]
  have hE0 : PowerSeries.constantCoeff (W.lev c ζ Eπ) = 0 := by
    have h0 := hQ0
    rw [framepf_Q_eq_q W hs, hq, map_mul, map_mul] at h0
    exact (mul_eq_zero.1 h0).resolve_left ((hw'.map (W.lev c ζ)).map PowerSeries.constantCoeff).ne_zero
  have hsm : ∀ (b : LetA O n) (t : LA W T π' c), Ψ (smulLA W T π' c b t) = b • Ψ t := by
    intro b t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul e ℓ =>
      have : smulLA W T π' c b (e ⊗ₜ ℓ) = (algebraMap (LetA O n) W.EE b * e) ⊗ₜ ℓ := rfl
      rw [this, hΨ, hΨ, mul_smul, algebraMap_smul]
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, smul_add]
  have hΛ : Eπ ^ h' • Ψ x =
      ∑ j, ((letE c : LetA O n) * a j) • W.φD T (hh (mkL W T π' c (z j) (hz j))) := by
    rw [← hsm, hrep, map_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [hΨ, algebraMap_smul]
  have hmid : ∀ ℓ (r : ℤ), 1 ≤ r → r < (4 * h' : ℕ) → Ct.levB T (c - 1) 1 ⟨hh ℓ, hN ℓ⟩ r = 0 := by
    intro ℓ r h1 h2
    obtain ⟨⟨t, ht, hte⟩, -⟩ := (mem_PiNS W T π' M _).1 (hγ ℓ)
    refine framepf_levB_zero Ct T hc (c - 1) hv hχ (π' ^ M) (4 * h') (fun j hj => ?_) ⟨hh ℓ, hN ℓ⟩
      ⟨t, ht⟩ hte.symm (hneg _) r h1 h2
    obtain ⟨f, hf⟩ := PowerSeries.X_dvd_iff.2 (framepf_lev_π_one (W := W) (c - 1))
    have : W.lev (c - 1) 1 (π' ^ M) =
        PowerSeries.X ^ (s' * M) * (W.lev (c - 1) 1 w ^ M * f ^ (s' * M)) := by
      rw [hπ, map_pow, map_mul, map_pow, hf]
      ring
    rw [this, PowerSeries.coeff_X_pow_mul', if_neg (by omega)]
  have key := framepf_loc_core Ct T hc c ζ hζ hQ0 hQ1 hneg (4 * h') (fun j => (a j : LetA O n))
    (fun j => ⟨_, hN (mkL W T π' c (z j) (hz j))⟩) (fun j => hmid _)
    (-(π' ^ M * Eπ ^ (4 * h'))) (fun j hj => by
      obtain ⟨f, hf⟩ := PowerSeries.X_dvd_iff.2 hE0
      have : W.lev c ζ (-(π' ^ M * Eπ ^ (4 * h'))) =
          PowerSeries.X ^ (4 * h') * (-(W.lev c ζ π' ^ M * f ^ (4 * h'))) := by
        rw [map_neg, map_mul, map_pow, map_pow, hf]
        ring
      rw [this, PowerSeries.coeff_X_pow_mul', if_neg (by omega)]) p
    (Submodule.span_mono (Set.image_mono fun _ hx => Formalism.MainNotions.LiftingTheory.wmap_Nl_le W T (c - 1) hx) hp.1.1)
    (Eπ ^ h' • y) (by
      rw [← hΛ, show y = Ψ x - (π' ^ M * Eπ ^ (3 * h')) • p by rw [hpe']; abel, smul_sub, smul_smul,
        neg_smul, sub_eq_add_neg]
      congr 3
      ring) k hk i (by push_cast; omega)
  rw [key]
  unfold expS
  rw [framepf_serMul_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  obtain ⟨⟨t, ht, hte⟩, -⟩ := (mem_PiNS W T π' 1 _).1 (hmod (z j) (hz j))
  have hval := framepf_valAt_mod Ct T hc c ζ hζ hQ0 hQ1 hneg π' hπ1 (PD.p ^ σ)
    ⟨_, hN (mkL W T π' c (z j) (hz j))⟩ ⟨z j, ((mem_NcS W T (c - 1) _).1 (hz j)).1⟩ ⟨t, ht⟩ (by
      rw [pow_one] at hte
      rw [hte, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul])
  dsimp only at hval ⊢
  rw [hval]
  unfold serC
  split_ifs
  · rw [smul_comm]
  · rw [smul_zero]

end Local

end Formalism.MainNotions.N.Ln34

end
