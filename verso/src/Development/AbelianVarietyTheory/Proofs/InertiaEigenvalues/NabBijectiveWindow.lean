import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.PowerSeriesOneAddConstMulXMulInv

noncomputable section
namespace GlobalTheory.PhiGam.Window
open GlobalTheory.PhiGam
open scoped LaurentSeries PowerSeries

/- English proof (translation)
Establish `hinj : ∀ p ∈ P, T p - x • p ∈ Q → p ∈ Q`. Introduce `p hp hq`. Unfold `gmult at h`. Use `set P' := P ⊓ ⨆ m : ℕ, Q.comap ((T - algebraMap k (Module.End k U) x) ^ m) with hP'`. Establish `hker : LinearMap.ker (Q.mkQ ∘ₗ P'.subtype) = Q.submoduleOf P'`.

Rewrite using `[LinearMap.ker_comp, Submodule.ker_mkQ]`. Both sides reduce to the same expression. Establish `hle : LinearMap.range (Q.mkQ ∘ₗ P'.subtype) ≤ P.map Q.mkQ`. Rewrite using `[LinearMap.range_comp, Submodule.range_subtype]`. Conclude with `Submodule.map_mono inf_le_left`.

Use `haveI : FiniteDimensional k (LinearMap.range (Q.mkQ ∘ₗ P'.subtype)) := Submodule.finiteDimensional_of_le hle`. Use `haveI : FiniteDimensional k (↥P' ⧸ Q.submoduleOf P') := by`. Rewrite using `[← hker]`. Conclude with `LinearEquiv.finiteDimensional (LinearMap.quotKerEquivRange _).symm`. Establish `hsub : Subsingleton (↥P' ⧸ Q.submoduleOf P')` using `Module.finrank_zero_iff.mp h`.

Establish `hmem : p ∈ P'`. Use `⟨hp, ?_⟩` and prove the remaining obligations. Use `Submodule.mem_iSup_of_mem 1 ?_` and prove the remaining obligations. Simplify `hq` using `[Module.algebraMap_end_apply]`. Establish `: (Submodule.Quotient.mk (⟨p, hmem⟩ : P') : ↥P' ⧸ Q.submoduleOf P') = 0` using `Subsingleton.elim _ _`.

Conclude with `(Submodule.Quotient.mk_eq_zero (Q.submoduleOf P')).mp this`. Use `⟨hinj, ?_⟩` and prove the remaining obligations. Set `S : U →ₗ[k] U` to `T - x • LinearMap.id`. Establish `hS : ∀ p, S p = T p - x • p` using `fun p => rfl`. Establish `hSQ : Q ≤ Q.comap S` using `fun p hp => by`.

Rewrite using `[Submodule.mem_comap, hS]`. Conclude with `Q.sub_mem (hQ p hp) (Q.smul_mem _ hp)`. Set `Sq` to `Q.mapQ Q S hSQ`. Establish `hSq : ∀ z ∈ P.map Q.mkQ, Sq z ∈ P.map Q.mkQ`. Introduce and unpack `_ ⟨p, hp, rfl⟩`.

Conclude with `⟨S p, P.sub_mem (hP p hp) (P.smul_mem _ hp), rfl⟩`. Establish `hi : Function.Injective (Sq.restrict hSq)`. Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce and unpack `⟨_, p, hp, rfl⟩ hz`. Establish `h1 : Q.mkQ (S p) = 0` using `congrArg Subtype.val hz`.

Establish `h2 : p ∈ Q` using `hinj p hp ((Submodule.Quotient.mk_eq_zero _).mp h1)`. Conclude with `Subtype.ext ((Submodule.Quotient.mk_eq_zero _).mpr h2)`. Establish `hs` using `LinearMap.injective_iff_surjective.mp hi`. Introduce `y hy`. Take `⟨⟨_, p, hp, rfl⟩, hz⟩` from `hs ⟨Q.mkQ y, y, hy, rfl⟩`.

Establish `h1 : Q.mkQ (S p) = Q.mkQ y` using `congrArg Subtype.val hz`. Conclude with `⟨p, hp, (Submodule.Quotient.eq _).mp h1.symm⟩`.
-/
theorem bij_of_gmult_zero {k U : Type} [Field k] [AddCommGroup U] [Module k U] (T : Module.End k U)
    (P Q : Submodule k U) (hP : ∀ p ∈ P, T p ∈ P) (hQ : ∀ p ∈ Q, T p ∈ Q)
    [hfin : FiniteDimensional k (P.map Q.mkQ)] (x : k) (h : gmult T P Q x = 0) :
    (∀ p ∈ P, T p - x • p ∈ Q → p ∈ Q) ∧ ∀ y ∈ P, ∃ p ∈ P, y - (T p - x • p) ∈ Q := by
  have hinj : ∀ p ∈ P, T p - x • p ∈ Q → p ∈ Q := by
    intro p hp hq
    unfold gmult at h
    set P' := P ⊓ ⨆ m : ℕ, Q.comap ((T - algebraMap k (Module.End k U) x) ^ m) with hP'
    have hker : LinearMap.ker (Q.mkQ ∘ₗ P'.subtype) = Q.submoduleOf P' := by
      rw [LinearMap.ker_comp, Submodule.ker_mkQ]; rfl
    have hle : LinearMap.range (Q.mkQ ∘ₗ P'.subtype) ≤ P.map Q.mkQ := by
      rw [LinearMap.range_comp, Submodule.range_subtype]
      exact Submodule.map_mono inf_le_left
    haveI : FiniteDimensional k (LinearMap.range (Q.mkQ ∘ₗ P'.subtype)) :=
      Submodule.finiteDimensional_of_le hle
    haveI : FiniteDimensional k (↥P' ⧸ Q.submoduleOf P') := by
      rw [← hker]
      exact LinearEquiv.finiteDimensional (LinearMap.quotKerEquivRange _).symm
    have hsub : Subsingleton (↥P' ⧸ Q.submoduleOf P') := Module.finrank_zero_iff.mp h
    have hmem : p ∈ P' := by
      refine ⟨hp, ?_⟩
      refine Submodule.mem_iSup_of_mem 1 ?_
      simpa [Module.algebraMap_end_apply] using hq
    have : (Submodule.Quotient.mk (⟨p, hmem⟩ : P') : ↥P' ⧸ Q.submoduleOf P') = 0 := Subsingleton.elim _ _
    exact (Submodule.Quotient.mk_eq_zero (Q.submoduleOf P')).mp this
  refine ⟨hinj, ?_⟩
  let S : U →ₗ[k] U := T - x • LinearMap.id
  have hS : ∀ p, S p = T p - x • p := fun p => rfl
  have hSQ : Q ≤ Q.comap S := fun p hp => by
    rw [Submodule.mem_comap, hS]; exact Q.sub_mem (hQ p hp) (Q.smul_mem _ hp)
  let Sq := Q.mapQ Q S hSQ
  have hSq : ∀ z ∈ P.map Q.mkQ, Sq z ∈ P.map Q.mkQ := by
    rintro _ ⟨p, hp, rfl⟩
    exact ⟨S p, P.sub_mem (hP p hp) (P.smul_mem _ hp), rfl⟩
  have hi : Function.Injective (Sq.restrict hSq) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨_, p, hp, rfl⟩ hz
    have h1 : Q.mkQ (S p) = 0 := congrArg Subtype.val hz
    have h2 : p ∈ Q := hinj p hp ((Submodule.Quotient.mk_eq_zero _).mp h1)
    exact Subtype.ext ((Submodule.Quotient.mk_eq_zero _).mpr h2)
  have hs := LinearMap.injective_iff_surjective.mp hi
  intro y hy
  obtain ⟨⟨_, p, hp, rfl⟩, hz⟩ := hs ⟨Q.mkQ y, y, hy, rfl⟩
  have h1 : Q.mkQ (S p) = Q.mkQ y := congrArg Subtype.val hz
  exact ⟨p, hp, (Submodule.Quotient.eq _).mp h1.symm⟩

variable {k : Type} [Field k]

/- English proof (translation)
Simplify using `[vv]`.
-/
theorem vv_coe : vv k = ((PowerSeries.X : k⟦X⟧) : k⸨X⸩) := by
  simp [vv]

/- English proof (translation)
Simplify using `[vv]`.
-/
theorem vv_ne_zero : vv k ≠ 0 := by
  simp [vv]

/- English proof (translation)
Take `⟨κ, hκ, hγ⟩` from `R.γ_v`. Choose the witnesses or unpack the hypotheses as in `⟨c0, hc0⟩ : (PowerSeries.X : k⟦X⟧) ∣ κ - 1 := by`. Rewrite using `[PowerSeries.X_dvd_iff]`. Simplify using `[hκ]`. Establish `hκ' : κ = 1 + PowerSeries.X * c0` using `by rw [← hc0]; ring`.

Establish `hu : IsUnit (1 - κ * PowerSeries.X : k⟦X⟧)`. Rewrite using `[PowerSeries.isUnit_iff_constantCoeff]`. Simplify using the standard rewrite rules. Take `⟨w', hw'⟩` from `hu.exists_right_inv`. Set `ι : k⟦X⟧ →+* k⸨X⸩` to `HahnSeries.ofPowerSeries ℤ k`.

Establish `hι : ∀ c : k⟦X⟧, (c : k⸨X⸩) = ι c` using `fun _ => rfl`. Establish `hv : vv k = ι PowerSeries.X` using `vv_coe`. Use `set w : k⸨X⸩ := 1 - (κ : k⸨X⸩) * vv k with hw`. Establish `hw1 : w = 1 - vv k - ι c0 * vv k ^ 2`. Rewrite using `[hw, hι, hκ', hv]`.

Simplify using `only [map_add, map_mul, map_one]`. Expand and normalize the polynomial expressions, which then agree. Establish `hww : w * ι w' = 1`. Use `congrArg ι hw'` as an intermediate fact. Simplify using `only [map_mul, map_sub, map_one] at this`.

Rewrite using `[hw, hv, hι]`. Conclude with `this`. Establish `hw0 : w ≠ 0` using `left_ne_zero_of_mul_eq_one hww`. Establish `hinv : w⁻¹ = ι w'` using `(eq_inv_of_mul_eq_one_right hww).symm`. Establish `key : ∃ c : k⟦X⟧, w ^ b = 1 - (b : k⸨X⸩) * vv k + ι c * vv k ^ 2`.

Proceed by induction on `b using Int.induction_on with`. Consider the case `zero => exact ⟨0, by simp⟩`. Consider the case `succ n ih`. Take `⟨c, hc⟩` from `ih`. Use `⟨(n : k⟦X⟧) - c0 + (n : k⟦X⟧) * c0 * PowerSeries.X + c * (1 - PowerSeries.X - c0 * PowerSeries.X ^ 2), ?_⟩` and prove the remaining obligations.

Rewrite using `[zpow_add_one₀ hw0, hc, hw1]`. Simplify using `only [map_add, map_sub, map_mul, map_one, map_pow, map_natCast, ← hv]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Consider the case `pred n ih`.

Take `⟨c, hc⟩` from `ih`. Use `⟨w' * (c + ((n : k⟦X⟧) + 1) + c0 + ((n : k⟦X⟧) + 1) * c0 * PowerSeries.X), ?_⟩` and prove the remaining obligations. Rewrite using `[zpow_sub_one₀ hw0, hc, hinv]`. Simplify using `only [map_add, map_sub, map_mul, map_one, map_pow, map_natCast, ← hv]`. Use `push_cast`.

Rewrite `hww` using `[hw1]`. Take the linear combination `(1 + ((n : k⸨X⸩) + 1) * vv k) * hww`. Take `⟨c, hc⟩` from `key`. Conclude with `⟨c, by rw [map_zpow₀, hγ, mul_zpow, hc]⟩`.
-/
theorem gam_zpow {l : ℕ} (R : RingPG k l) (b : ℤ) :
    ∃ c : k⟦X⟧, R.γ (vv k ^ b) = vv k ^ b * (1 - (b : k⸨X⸩) * vv k + (c : k⸨X⸩) * vv k ^ 2) := by
  obtain ⟨κ, hκ, hγ⟩ := R.γ_v
  obtain ⟨c0, hc0⟩ : (PowerSeries.X : k⟦X⟧) ∣ κ - 1 := by
    rw [PowerSeries.X_dvd_iff]; simp [hκ]
  have hκ' : κ = 1 + PowerSeries.X * c0 := by rw [← hc0]; ring
  have hu : IsUnit (1 - κ * PowerSeries.X : k⟦X⟧) := by
    rw [PowerSeries.isUnit_iff_constantCoeff]; simp
  obtain ⟨w', hw'⟩ := hu.exists_right_inv
  let ι : k⟦X⟧ →+* k⸨X⸩ := HahnSeries.ofPowerSeries ℤ k
  have hι : ∀ c : k⟦X⟧, (c : k⸨X⸩) = ι c := fun _ => rfl
  have hv : vv k = ι PowerSeries.X := vv_coe
  set w : k⸨X⸩ := 1 - (κ : k⸨X⸩) * vv k with hw
  have hw1 : w = 1 - vv k - ι c0 * vv k ^ 2 := by
    rw [hw, hι, hκ', hv]; simp only [map_add, map_mul, map_one]; ring
  have hww : w * ι w' = 1 := by
    have := congrArg ι hw'
    simp only [map_mul, map_sub, map_one] at this
    rw [hw, hv, hι]; exact this
  have hw0 : w ≠ 0 := left_ne_zero_of_mul_eq_one hww
  have hinv : w⁻¹ = ι w' := (eq_inv_of_mul_eq_one_right hww).symm
  have key : ∃ c : k⟦X⟧, w ^ b = 1 - (b : k⸨X⸩) * vv k + ι c * vv k ^ 2 := by
    induction b using Int.induction_on with
    | zero => exact ⟨0, by simp⟩
    | succ n ih =>
      obtain ⟨c, hc⟩ := ih
      refine ⟨(n : k⟦X⟧) - c0 + (n : k⟦X⟧) * c0 * PowerSeries.X + c * (1 - PowerSeries.X - c0 * PowerSeries.X ^ 2), ?_⟩
      rw [zpow_add_one₀ hw0, hc, hw1]
      simp only [map_add, map_sub, map_mul, map_one, map_pow, map_natCast, ← hv]
      push_cast
      ring
    | pred n ih =>
      obtain ⟨c, hc⟩ := ih
      refine ⟨w' * (c + ((n : k⟦X⟧) + 1) + c0 + ((n : k⟦X⟧) + 1) * c0 * PowerSeries.X), ?_⟩
      rw [zpow_sub_one₀ hw0, hc, hinv]
      simp only [map_add, map_sub, map_mul, map_one, map_pow, map_natCast, ← hv]
      push_cast
      rw [hw1] at hww
      linear_combination (1 + ((n : k⸨X⸩) + 1) * vv k) * hww
  obtain ⟨c, hc⟩ := key
  exact ⟨c, by rw [map_zpow₀, hγ, mul_zpow, hc]⟩

variable {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V]
  [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V]

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_sh_iff {a : ℤ} {N : Submodule k⟦X⟧ V} {x : V} :
    x ∈ sh a N ↔ ∃ n ∈ N, vv k ^ a • n = x := Iff.rfl

/- English proof (translation)
The claim follows from `algebraMap_smul k⸨X⸩ c x`.
-/
theorem coe_smul_eq (c : k⟦X⟧) (x : V) : (c : k⸨X⸩) • x = c • x :=
  algebraMap_smul k⸨X⸩ c x

/- English proof (translation)
Rewrite using `[vv_coe, coe_smul_eq]`. Conclude with `N.smul_mem _ hn`.
-/
theorem v_smul_mem {N : Submodule k⟦X⟧ V} {n : V} (hn : n ∈ N) : vv k • n ∈ N := by
  rw [vv_coe, coe_smul_eq]; exact N.smul_mem _ hn

/- English proof (translation)
Introduce and unpack `_ ⟨n, hn, rfl⟩`. Use `mem_sh_iff.mpr ⟨vv k • n, v_smul_mem hn, ?_⟩` and prove the remaining obligations. Use `show _ = vv k ^ (a + 1) • n`. Rewrite using `[smul_smul, zpow_add_one₀ vv_ne_zero]`.
-/
theorem sh_succ_le (a : ℤ) (N : Submodule k⟦X⟧ V) : sh (a + 1) N ≤ sh a N := by
  rintro _ ⟨n, hn, rfl⟩
  refine mem_sh_iff.mpr ⟨vv k • n, v_smul_mem hn, ?_⟩
  show _ = vv k ^ (a + 1) • n
  rw [smul_smul, zpow_add_one₀ vv_ne_zero]

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => simp`. Consider the case `succ m ih`. Use `le_trans ?_ ih` and prove the remaining obligations. Rewrite using `[Nat.cast_succ, ← add_assoc]`.

Conclude with `sh_succ_le _ _`.
-/
theorem sh_add_le (a : ℤ) (m : ℕ) (N : Submodule k⟦X⟧ V) : sh (a + m) N ≤ sh a N := by
  induction m with
  | zero => simp
  | succ m ih =>
    refine le_trans ?_ ih
    rw [Nat.cast_succ, ← add_assoc]; exact sh_succ_le _ _

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem nab_eq (g : V →ₗ[k] V) (x : V) : nab g x = (vv k)⁻¹ • (g x - x) := rfl

/- English proof (translation)
Take `⟨n', hn', h⟩` from `mem_sh_iff.mp (hC n hn)`. Rewrite using `[nab_eq, ← h, smul_smul, zpow_one, inv_mul_cancel₀ vv_ne_zero, one_smul]`. Conclude with `hn'`.
-/
theorem nab_mem {g : V →ₗ[k] V} {N : Submodule k⟦X⟧ V} (hC : CondC g N) {n : V} (hn : n ∈ N) :
    nab g n ∈ N := by
  obtain ⟨n', hn', h⟩ := mem_sh_iff.mp (hC n hn)
  rw [nab_eq, ← h, smul_smul, zpow_one, inv_mul_cancel₀ vv_ne_zero, one_smul]; exact hn'

/- English proof (translation)
Apply the tactic sequence `match_scalars <;> field_simp <;> ring`.
-/
theorem shift_identity {K W : Type} [Field K] [AddCommGroup W] [Module K W] {v : K} (hv : v ≠ 0)
    (u b c : K) (n t : W) :
    v⁻¹ • ((u * (1 - b * v + c * v ^ 2)) • (n + v • t) - u • n) =
      u • (t - b • n + v • (c • (n + v • t) - b • t)) := by
  match_scalars <;> field_simp <;> ring

/- English proof (translation)
Take `⟨c, hc⟩` from `gam_zpow R b`. Establish `hv : vv k ≠ 0` using `vv_ne_zero`. Establish `hgn : g n = n + vv k • nab g n`. Rewrite using `[nab_eq, smul_smul, mul_inv_cancel₀ hv, one_smul]`. Normalize the expressions using the abelian group laws.

Establish `hm` using `nab_mem hC hn`. Use `⟨c • (n + vv k • nab g n) - b • nab g n, N.sub_mem (N.smul_mem _ (N.add_mem hn (v_smul_mem hm))) (zsmul_mem hm _), ?_⟩` and prove the remaining obligations. Rewrite using `[nab_eq g (vv k ^ b • n), hg, hc, hgn, Int.cast_smul_eq_zsmul, ← coe_smul_eq, ← Int.cast_smul_eq_zsmul k⸨X⸩ b n, ← Int.cast_smul_eq_zsmul k⸨X⸩ b (nab g n)]`. Conclude with `shift_identity hv _ _ _ _ _`.
-/
theorem nab_shift {l : ℕ} (R : RingPG k l) {g : V →ₗ[k] V} (hg : Semi R.γ g) {N : Submodule k⟦X⟧ V}
    (hC : CondC g N) (b : ℤ) {n : V} (hn : n ∈ N) :
    ∃ n' ∈ N, nab g (vv k ^ b • n) = vv k ^ b • (nab g n - (b : k) • n + vv k • n') := by
  obtain ⟨c, hc⟩ := gam_zpow R b
  have hv : vv k ≠ 0 := vv_ne_zero
  have hgn : g n = n + vv k • nab g n := by
    rw [nab_eq, smul_smul, mul_inv_cancel₀ hv, one_smul]; abel
  have hm := nab_mem hC hn
  refine ⟨c • (n + vv k • nab g n) - b • nab g n,
    N.sub_mem (N.smul_mem _ (N.add_mem hn (v_smul_mem hm))) (zsmul_mem hm _), ?_⟩
  rw [nab_eq g (vv k ^ b • n), hg, hc, hgn, Int.cast_smul_eq_zsmul, ← coe_smul_eq,
    ← Int.cast_smul_eq_zsmul k⸨X⸩ b n, ← Int.cast_smul_eq_zsmul k⸨X⸩ b (nab g n)]
  exact shift_identity hv _ _ _ _ _

/- English proof (translation)
Take `⟨n, hn, rfl⟩` from `mem_sh_iff.mp hx`. Take `⟨n', hn', h⟩` from `nab_shift R hg hC b hn`. Use `mem_sh_iff.mpr ⟨_, ?_, h.symm⟩` and prove the remaining obligations. Conclude with `N.add_mem (N.sub_mem (nab_mem hC hn) ((N.restrictScalars k).smul_mem _ hn)) (v_smul_mem hn')`.
-/
theorem nab_mem_sh {l : ℕ} (R : RingPG k l) {g : V →ₗ[k] V} (hg : Semi R.γ g) {N : Submodule k⟦X⟧ V}
    (hC : CondC g N) (b : ℤ) {x : V} (hx : x ∈ sh b N) : nab g x ∈ sh b N := by
  obtain ⟨n, hn, rfl⟩ := mem_sh_iff.mp hx
  obtain ⟨n', hn', h⟩ := nab_shift R hg hC b hn
  refine mem_sh_iff.mpr ⟨_, ?_, h.symm⟩
  exact N.add_mem (N.sub_mem (nab_mem hC hn) ((N.restrictScalars k).smul_mem _ hn)) (v_smul_mem hn')

/- English proof (translation)
Take `⟨s, hs⟩` from `hN`. Use `set Q := (sh 1 N).restrictScalars k with hQ`. Establish `hle : (N.restrictScalars k).map Q.mkQ ≤ Submodule.span k (Q.mkQ '' (s : Set V))`. Introduce and unpack `_ ⟨n, hn, rfl⟩`. Establish `hn' : n ∈ Submodule.span k⟦X⟧ (s : Set V)` using `by rw [hs]; exact hn`.

Use `clear hn`. Proceed by induction on `hn' using Submodule.span_induction with`. Consider the case `mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩`. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => rw [map_add]`.

Conclude with `Submodule.add_mem _ hx hy`. Consider the case `smul c x hx ih`. Establish `hxN : x ∈ N` using `by rw [← hs]; exact hx`. Choose the witnesses or unpack the hypotheses as in `⟨c', hc'⟩ : (PowerSeries.X : k⟦X⟧) ∣ c - algebraMap k k⟦X⟧ (PowerSeries.constantCoeff c) := by`. Rewrite using `[PowerSeries.X_dvd_iff]`.

Simplify using the standard rewrite rules. Establish `: Q.mkQ (c • x) = PowerSeries.constantCoeff c • Q.mkQ x`. Rewrite using `[← map_smul]`. Use `(Submodule.Quotient.eq _).mpr ?_` and prove the remaining obligations. Use `mem_sh_iff.mpr ⟨c' • x, N.smul_mem _ hxN, ?_⟩` and prove the remaining obligations.

Rewrite using `[zpow_one, vv_coe, coe_smul_eq, smul_smul, ← hc', sub_smul, algebraMap_smul]`. Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ _ ih`. Use `haveI : FiniteDimensional k (Submodule.span k (Q.mkQ '' (s : Set V))) := FiniteDimensional.span_of_finite k (s.finite_toSet.image _)`. Conclude with `Submodule.finiteDimensional_of_le hle`.
-/
theorem finite_quot {N : Submodule k⟦X⟧ V} (hN : N.FG) :
    FiniteDimensional k ((N.restrictScalars k).map ((sh 1 N).restrictScalars k).mkQ) := by
  obtain ⟨s, hs⟩ := hN
  set Q := (sh 1 N).restrictScalars k with hQ
  have hle : (N.restrictScalars k).map Q.mkQ ≤ Submodule.span k (Q.mkQ '' (s : Set V)) := by
    rintro _ ⟨n, hn, rfl⟩
    have hn' : n ∈ Submodule.span k⟦X⟧ (s : Set V) := by rw [hs]; exact hn
    clear hn
    induction hn' using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    | smul c x hx ih =>
      have hxN : x ∈ N := by rw [← hs]; exact hx
      obtain ⟨c', hc'⟩ : (PowerSeries.X : k⟦X⟧) ∣ c - algebraMap k k⟦X⟧ (PowerSeries.constantCoeff c) := by
        rw [PowerSeries.X_dvd_iff]; simp
      have : Q.mkQ (c • x) = PowerSeries.constantCoeff c • Q.mkQ x := by
        rw [← map_smul]
        refine (Submodule.Quotient.eq _).mpr ?_
        refine mem_sh_iff.mpr ⟨c' • x, N.smul_mem _ hxN, ?_⟩
        rw [zpow_one, vv_coe, coe_smul_eq, smul_smul, ← hc', sub_smul, algebraMap_smul]
      rw [this]; exact Submodule.smul_mem _ _ ih
  haveI : FiniteDimensional k (Submodule.span k (Q.mkQ '' (s : Set V))) :=
    FiniteDimensional.span_of_finite k (s.finite_toSet.image _)
  exact Submodule.finiteDimensional_of_le hle

/- English proof (translation)
Use `haveI := finite_quot hN`. Take `⟨h1, h2⟩` from `bij_of_gmult_zero (nab g) (N.restrictScalars k) ((sh 1 N).restrictScalars k) (fun p hp => nab_mem hC hp) (fun p hp => nab_mem_sh R hg hC 1 hp) (b : k) h`. Establish `hv : vv k ≠ 0` using `vv_ne_zero`. Prove the components needed by the constructor for the conclusion. Introduce `x hx hx'`.

Take `⟨n, hn, rfl⟩` from `mem_sh_iff.mp hx`. Take `⟨n', hn', e⟩` from `nab_shift R hg hC b hn`. Take `⟨t, ht, e'⟩` from `mem_sh_iff.mp hx'`. Rewrite `e'` using `[e, zpow_add_one₀ hv, mul_smul]`. Establish `e2` using `smul_right_injective V (zpow_ne_zero b hv) e'`.

Establish `: n ∈ sh 1 N` using `h1 n hn (mem_sh_iff.mpr ⟨t - n', N.sub_mem ht hn', by`. Rewrite using `[zpow_one, smul_sub, e2]`. Use the proof step `abel⟩)`. Take `⟨r, hr, rfl⟩` from `mem_sh_iff.mp this`. Conclude with `mem_sh_iff.mpr ⟨r, hr, by rw [zpow_add₀ hv, mul_smul]⟩`.

Introduce `y hy`. Take `⟨n, hn, rfl⟩` from `mem_sh_iff.mp hy`. Take `⟨p, hp, hq⟩` from `h2 n hn`. Take `⟨r, hr, e'⟩` from `mem_sh_iff.mp hq`. Take `⟨n', hn', e⟩` from `nab_shift R hg hC b hp`.

Use `⟨vv k ^ b • p, mem_sh_iff.mpr ⟨p, hp, rfl⟩, mem_sh_iff.mpr ⟨r - n', N.sub_mem hr hn', ?_⟩⟩` and prove the remaining obligations. Rewrite `e'` using `[zpow_one]`. Rewrite using `[e, zpow_add_one₀ hv, mul_smul, ← smul_sub, smul_sub (vv k), e']`. Use `congr 1`. Normalize the expressions using the abelian group laws.
-/
theorem graded {l : ℕ} (R : RingPG k l) {g : V →ₗ[k] V} (hg : Semi R.γ g) {N : Submodule k⟦X⟧ V}
    (hN : N.FG) (hC : CondC g N) (b : ℤ) (h : sen g N (b : k) = 0) :
    (∀ x ∈ sh b N, nab g x ∈ sh (b + 1) N → x ∈ sh (b + 1) N) ∧
      ∀ y ∈ sh b N, ∃ x ∈ sh b N, y - nab g x ∈ sh (b + 1) N := by
  haveI := finite_quot hN
  obtain ⟨h1, h2⟩ := bij_of_gmult_zero (nab g) (N.restrictScalars k) ((sh 1 N).restrictScalars k)
    (fun p hp => nab_mem hC hp) (fun p hp => nab_mem_sh R hg hC 1 hp) (b : k) h
  have hv : vv k ≠ 0 := vv_ne_zero
  constructor
  · intro x hx hx'
    obtain ⟨n, hn, rfl⟩ := mem_sh_iff.mp hx
    obtain ⟨n', hn', e⟩ := nab_shift R hg hC b hn
    obtain ⟨t, ht, e'⟩ := mem_sh_iff.mp hx'
    rw [e, zpow_add_one₀ hv, mul_smul] at e'
    have e2 := smul_right_injective V (zpow_ne_zero b hv) e'
    have : n ∈ sh 1 N := h1 n hn (mem_sh_iff.mpr ⟨t - n', N.sub_mem ht hn', by
      rw [zpow_one, smul_sub, e2]; abel⟩)
    obtain ⟨r, hr, rfl⟩ := mem_sh_iff.mp this
    exact mem_sh_iff.mpr ⟨r, hr, by rw [zpow_add₀ hv, mul_smul]⟩
  · intro y hy
    obtain ⟨n, hn, rfl⟩ := mem_sh_iff.mp hy
    obtain ⟨p, hp, hq⟩ := h2 n hn
    obtain ⟨r, hr, e'⟩ := mem_sh_iff.mp hq
    obtain ⟨n', hn', e⟩ := nab_shift R hg hC b hp
    refine ⟨vv k ^ b • p, mem_sh_iff.mpr ⟨p, hp, rfl⟩, mem_sh_iff.mpr ⟨r - n', N.sub_mem hr hn', ?_⟩⟩
    rw [zpow_one] at e'
    rw [e, zpow_add_one₀ hv, mul_smul, ← smul_sub, smul_sub (vv k), e']
    congr 1; abel

/- English proof (translation)
Introduce `k _ l _ _ R V _ _ _ _ _ _ _ _ g hg N hN hC a m`. Proceed by induction on `m with`. Consider the case `zero`. Introduce `_`. Use `⟨fun x hx _ => by simpa using hx, fun y hy => ⟨0, Submodule.zero_mem _, by simpa using hy⟩⟩` and prove the remaining obligations.

Consider the case `succ m ih`. Introduce `h`. Take `⟨i1, i2⟩` from `ih (fun j hj => h j (Nat.lt_succ_of_lt hj))`. Take `⟨g1, g2⟩` from `graded R hg hN.1 hC (a + m) (h m (Nat.lt_succ_self m))`. Rewrite using `[Nat.cast_succ, ← add_assoc]`.

Use `⟨fun x hx hx' => g1 x (i1 x hx (sh_succ_le _ _ hx')) hx', fun y hy => ?_⟩` and prove the remaining obligations. Take `⟨x, hx, hx'⟩` from `i2 y hy`. Take `⟨z, hz, hz'⟩` from `g2 _ hx'`. Use `⟨x + z, Submodule.add_mem _ hx (sh_add_le a m N hz), ?_⟩` and prove the remaining obligations. Rewrite using `[map_add, ← sub_sub]`.

Conclude with `hz'`.
-/
theorem nab_bijective_window : ∀ {k : Type} [Field k] {l : ℕ} [Fact l.Prime] [CharP k l] (R : RingPG k l) {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V] [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V] [FiniteDimensional k⸨X⸩ V] (g : V →ₗ[k] V), Semi R.γ g → ∀ N : Submodule k⟦X⟧ V, IsLat N → CondC g N → ∀ (a : ℤ) (m : ℕ), (∀ j : ℕ, j < m → sen g N ((a + j : ℤ) : k) = 0) → (∀ x ∈ sh a N, nab g x ∈ sh (a + m) N → x ∈ sh (a + m) N) ∧ ∀ y ∈ sh a N, ∃ x ∈ sh a N, y - nab g x ∈ sh (a + m) N := by
  intro k _ l _ _ R V _ _ _ _ _ _ _ _ g hg N hN hC a m
  induction m with
  | zero =>
    intro _
    refine ⟨fun x hx _ => by simpa using hx, fun y hy => ⟨0, Submodule.zero_mem _, by simpa using hy⟩⟩
  | succ m ih =>
    intro h
    obtain ⟨i1, i2⟩ := ih (fun j hj => h j (Nat.lt_succ_of_lt hj))
    obtain ⟨g1, g2⟩ := graded R hg hN.1 hC (a + m) (h m (Nat.lt_succ_self m))
    rw [Nat.cast_succ, ← add_assoc]
    refine ⟨fun x hx hx' => g1 x (i1 x hx (sh_succ_le _ _ hx')) hx', fun y hy => ?_⟩
    obtain ⟨x, hx, hx'⟩ := i2 y hy
    obtain ⟨z, hz, hz'⟩ := g2 _ hx'
    refine ⟨x + z, Submodule.add_mem _ hx (sh_add_le a m N hz), ?_⟩
    rw [map_add, ← sub_sub]; exact hz'

end GlobalTheory.PhiGam.Window
