import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.SplitAtOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.DivMemLocRingOfVFEq
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.CongrPIffInI
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsFracOfFixed

open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.TemperedBoundGL3

open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.U0 Formalism.HermitianLattices.Ext.L3.WA Formalism.HermitianLattices.Ext.L3.WCA Formalism.HermitianLattices.Ext.L3.Cell

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "κ" => algebraMap (𝓞 K) K

/- English proof (translation)
Establish `hbot : ∃ N, a ∉ 𝔭 ^ N`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Establish `hinf : a ∈ ⨅ i, 𝔭 ^ i` using `Submodule.mem_iInf _ |>.mpr hcon`. Rewrite `hinf` using `[Ideal.iInf_pow_eq_bot_of_isDomain 𝔭 h𝔭.ne_top, Ideal.mem_bot]`.

Conclude with `ha hinf`. Take `⟨N, hN⟩` from `hbot`. Establish `hbdd : BddAbove {e : ℕ | a ∈ 𝔭 ^ e}` using `⟨N, fun e he => by`. Assume the negation of the conclusion as `hlt`. Use `push_neg at hlt`.

Conclude with `hN (Ideal.pow_le_pow_right hlt.le he)⟩`. Establish `hmem : a ∈ 𝔭 ^ vF 𝔭 a` using `Nat.sSup_mem ⟨0, by simp⟩ hbdd`. Use `⟨hmem, fun h => ?_⟩` and prove the remaining obligations. Establish `hle : vF 𝔭 a + 1 ≤ vF 𝔭 a` using `le_csSup hbdd h`. Use linear arithmetic over natural numbers and integers.
-/
private theorem vF_spec_of_ne_zero {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {a : 𝓞 F} (ha : a ≠ 0) :
    a ∈ 𝔭 ^ vF 𝔭 a ∧ a ∉ 𝔭 ^ (vF 𝔭 a + 1) := by
  have hbot : ∃ N, a ∉ 𝔭 ^ N := by
    by_contra hcon
    push_neg at hcon
    have hinf : a ∈ ⨅ i, 𝔭 ^ i := Submodule.mem_iInf _ |>.mpr hcon
    rw [Ideal.iInf_pow_eq_bot_of_isDomain 𝔭 h𝔭.ne_top, Ideal.mem_bot] at hinf
    exact ha hinf
  obtain ⟨N, hN⟩ := hbot
  have hbdd : BddAbove {e : ℕ | a ∈ 𝔭 ^ e} := ⟨N, fun e he => by
    by_contra hlt
    push_neg at hlt
    exact hN (Ideal.pow_le_pow_right hlt.le he)⟩
  have hmem : a ∈ 𝔭 ^ vF 𝔭 a := Nat.sSup_mem ⟨0, by simp⟩ hbdd
  refine ⟨hmem, fun h => ?_⟩
  have hle : vF 𝔭 a + 1 ≤ vF 𝔭 a := le_csSup hbdd h
  omega

/- English proof (translation)
Rewrite using `[← IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 K) K, IsScalarTower.algebraMap_apply (𝓞 F) F K]`. Use `(map_ne_zero (algebraMap F K)).mpr ?_` and prove the remaining obligations. Conclude with `(map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).mpr ha`.
-/
private theorem jK_iota_ne_zero {a : 𝓞 F} (ha : a ≠ 0) : κ (ι a) ≠ 0 := by
  rw [← IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 K) K, IsScalarTower.algebraMap_apply (𝓞 F) F K]
  refine (map_ne_zero (algebraMap F K)).mpr ?_
  exact (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).mpr ha

/- English proof (translation)
Take `⟨hmem, hnot⟩` from `vF_spec_of_ne_zero h𝔭 ha`. Take `⟨J, hJ⟩ : 𝔭 ^ vF 𝔭 a ∣ Ideal.span {a}` from `Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hmem)`. Establish `hJp : ¬ J ≤ 𝔭` using `fun hle => hnot (by`. Establish `hs : Ideal.span {a} ≤ 𝔭 ^ (vF 𝔭 a + 1)`. Rewrite using `[hJ, pow_succ]`.

Conclude with `Ideal.mul_mono_right hle`. Conclude with `(Ideal.span_singleton_le_iff_mem _).mp hs)`. Take `⟨t, htJ, htp⟩` from `SetLike.not_le_iff_exists.mp hJp`. Establish `hat : a' * t ∈ Ideal.span {a}`. Rewrite using `[hJ]`.

Conclude with `Ideal.mul_mem_mul ha' htJ`. Take `⟨c, hc⟩` from `Ideal.mem_span_singleton'.mp hat`. Conclude with `⟨t, htp, c, by rw [mul_comm, hc]⟩`.
-/
theorem exists_mul_eq_of_mem_pow {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {a a' : 𝓞 F}
    (ha : a ≠ 0) (ha' : a' ∈ 𝔭 ^ vF 𝔭 a) :
    ∃ t : 𝓞 F, t ∉ 𝔭 ∧ ∃ c : 𝓞 F, t * a' = c * a := by
  obtain ⟨hmem, hnot⟩ := vF_spec_of_ne_zero h𝔭 ha
  obtain ⟨J, hJ⟩ : 𝔭 ^ vF 𝔭 a ∣ Ideal.span {a} :=
    Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hmem)
  have hJp : ¬ J ≤ 𝔭 := fun hle => hnot (by
    have hs : Ideal.span {a} ≤ 𝔭 ^ (vF 𝔭 a + 1) := by
      rw [hJ, pow_succ]
      exact Ideal.mul_mono_right hle
    exact (Ideal.span_singleton_le_iff_mem _).mp hs)
  obtain ⟨t, htJ, htp⟩ := SetLike.not_le_iff_exists.mp hJp
  have hat : a' * t ∈ Ideal.span {a} := by
    rw [hJ]
    exact Ideal.mul_mem_mul ha' htJ
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hat
  exact ⟨t, htp, c, by rw [mul_comm, hc]⟩

variable (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
include hK hF

/- English proof (translation)
Establish `hPm : (P.comap ι).IsMaximal` using `Ideal.isMaximal_comap_of_isIntegral_of_isMaximal P`. Take `⟨t, ht, c, hc⟩` from `exists_mul_eq_of_mem_pow hPm ha ha'`. Establish `hκa : κ (ι a) ≠ 0` using `jK_iota_ne_zero ha`. Establish `e : κ (ι t) * (κ (ι a') / κ (ι a)) = κ (ι c)`. Rewrite using `[← mul_div_assoc, ← map_mul, ← map_mul, hc, map_mul, map_mul, mul_div_cancel_right₀ _ hκa]`.

Use `show κ (ι a') / κ (ι a) ∈ Formalism.HermitianLatticesTheory.locR (K := K) P`. Rewrite using `[Formalism.HermitianLatticesTheory.locDual_mem_locR]`. Establish `hfix : star (κ (ι t)) = κ (ι t)` using `(hF _).mpr ⟨(t : F), by`. Rewrite using `[← IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 K) K, IsScalarTower.algebraMap_apply (𝓞 F) F K]⟩`. Establish `hmem : ι t ∈ Formalism.HermitianLatticesTheory.hcompl (K` using `K) P := by`.

Use `Submonoid.subset_closure (And.intro ht fun t' ht' => ?_)` and prove the remaining obligations. Rewrite `ht'` using `[hfix]`. Establish `ht'' : t' = ι t` using `IsFractionRing.injective (𝓞 K) K ht'`. Rewrite using `[ht'']`. Conclude with `ht`.

Use `⟨ι t, hmem, ?_⟩` and prove the remaining obligations. Rewrite using `[e]`. Conclude with `Submodule.mem_one.mpr ⟨_, rfl⟩`.
-/
theorem div_mem_locRing_of_mem_pow {P : Ideal (𝓞 K)} (hP : P.IsMaximal) {a a' : 𝓞 F}
    (ha : a ≠ 0) (ha' : a' ∈ (P.comap ι) ^ vF (P.comap ι) a) :
    κ (ι a') / κ (ι a) ∈ locRing P := by
  have hPm : (P.comap ι).IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal P
  obtain ⟨t, ht, c, hc⟩ := exists_mul_eq_of_mem_pow hPm ha ha'
  have hκa : κ (ι a) ≠ 0 := jK_iota_ne_zero ha
  have e : κ (ι t) * (κ (ι a') / κ (ι a)) = κ (ι c) := by
    rw [← mul_div_assoc, ← map_mul, ← map_mul, hc, map_mul, map_mul, mul_div_cancel_right₀ _ hκa]
  show κ (ι a') / κ (ι a) ∈ Formalism.HermitianLatticesTheory.locR (K := K) P
  rw [Formalism.HermitianLatticesTheory.locDual_mem_locR]
  have hfix : star (κ (ι t)) = κ (ι t) := (hF _).mpr ⟨(t : F), by
    rw [← IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 K) K, IsScalarTower.algebraMap_apply (𝓞 F) F K]⟩
  have hmem : ι t ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) P := by
    refine Submonoid.subset_closure (And.intro ht fun t' ht' => ?_)
    rw [hfix] at ht'
    have ht'' : t' = ι t := IsFractionRing.injective (𝓞 K) K ht'
    rw [ht'']
    exact ht
  refine ⟨ι t, hmem, ?_⟩
  rw [e]
  exact Submodule.mem_one.mpr ⟨_, rfl⟩

omit hK in

/- English proof (translation)
Establish `hz0 : ∀ z : 𝓞 K, κ z ∈ locRing P`. Introduce `z`. Use `show κ z ∈ Formalism.HermitianLatticesTheory.locR (K := K) P`. Rewrite using `[Formalism.HermitianLatticesTheory.locDual_mem_locR]`. Conclude with `⟨1, one_mem _, by rw [map_one, one_mul]; exact Submodule.mem_one.mpr ⟨z, rfl⟩⟩`.

Proceed by induction on `j with`. Consider the case `zero`. Introduce `z _`. Rewrite using `[pow_zero, inv_one, mul_one]`. Conclude with `hz0 z`.

Consider the case `succ j ih`. Introduce `z hz`. Rewrite `hz` using `[pow_succ]`. Use `Submodule.mul_induction_on hz (fun x hx y hy => ?_) (fun u w hu hw => ?_)` and prove the remaining obligations. Establish `hxy` using `(locRing P).mul_mem (ih x hx) (h1 y hy)`.

Rewrite using `[map_mul, pow_succ, mul_inv]`. Use `hxy using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[map_add, add_mul]`. Conclude with `(locRing P).add_mem hu hw`.
-/
theorem mul_inv_pow_mem {P : Ideal (𝓞 K)} {π : K}
    (h1 : ∀ z ∈ extP K (P.comap ι), Dv (locRing P) π (κ z)) (j : ℕ) :
    ∀ z ∈ extP K (P.comap ι) ^ j, κ z * (π ^ j)⁻¹ ∈ locRing P := by
  have hz0 : ∀ z : 𝓞 K, κ z ∈ locRing P := by
    intro z
    show κ z ∈ Formalism.HermitianLatticesTheory.locR (K := K) P
    rw [Formalism.HermitianLatticesTheory.locDual_mem_locR]
    exact ⟨1, one_mem _, by rw [map_one, one_mul]; exact Submodule.mem_one.mpr ⟨z, rfl⟩⟩
  induction j with
  | zero =>
    intro z _
    rw [pow_zero, inv_one, mul_one]
    exact hz0 z
  | succ j ih =>
    intro z hz
    rw [pow_succ] at hz
    refine Submodule.mul_induction_on hz (fun x hx y hy => ?_) (fun u w hu hw => ?_)
    · have hxy := (locRing P).mul_mem (ih x hx) (h1 y hy)
      rw [map_mul, pow_succ, mul_inv]
      convert hxy using 1
      ring
    · rw [map_add, add_mul]
      exact (locRing P).add_mem hu hw

/- English proof (translation)
Take `⟨π, hπ, h1, h2⟩` from `exists_isUnif hF hP`. Establish `hPm : (P.comap ι).IsMaximal` using `Ideal.isMaximal_comap_of_isIntegral_of_isMaximal P`. Establish `hcoe : ∀ c : 𝓞 F, algebraMap F K (c : F) = κ (ι c)` using `fun c => by`. Rewrite using `[← IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 K) K, IsScalarTower.algebraMap_apply (𝓞 F) F K]`. Establish `hstar : ∀ c : 𝓞 F, star (κ (ι c)) = κ (ι c)` using `fun c => (hF _).mpr ⟨(c : F), hcoe c⟩`.

Establish `hπ0 : π ≠ 0` using `hπ.3`. Establish `hex : ∃ p0 ∈ P.comap ι, IsUnitIn (locRing P) (κ (ι p0) * π⁻¹)`. Assume the negation of the conclusion as `hne`. Use `push_neg at hne`. Establish `hle : extP K (P.comap ι) ≤ extP K (P.comap ι) ^ 2` using `by show Ideal.map ι (P.comap ι) ≤ _`.

Use `Ideal.map_le_iff_le_comap.mpr fun p0 hp0 => ?_` and prove the remaining obligations. Use `show ι p0 ∈ extP K (P.comap ι) ^ 2`. Establish `hmemR : κ (ι p0) * π⁻¹ ∈ locRing P` using `h1 _ (Ideal.mem_map_of_mem _ hp0)`. Establish `hfix : star (κ (ι p0) * π⁻¹) = κ (ι p0) * π⁻¹`. Rewrite using `[star_mul', star_inv₀, hπ.2, hstar]`.

Conclude with `h2 _ ((hπ.4 _ hmemR hfix).resolve_left (hne p0 hp0))`. Establish `hI0 : extP K (P.comap ι) ≠ ⊥`. Introduce `h0`. Establish `hp0 : P.comap ι ≠ ⊥` using `Ring.ne_bot_of_isMaximal_of_not_isField hPm (NumberField.RingOfIntegers.not_isField F)`. Apply `hp0` to reduce the goal to its premises.

Rewrite using `[eq_bot_iff]`. Introduce `c hc`. Establish `hc' : ι c ∈ extP K (P.comap ι)` using `Ideal.mem_map_of_mem _ hc`. Rewrite `hc'` using `[h0, Ideal.mem_bot]`. Establish `hk : algebraMap F K (c : F) = 0` using `by rw [hcoe, hc', map_zero]`.

Rewrite using `[Ideal.mem_bot]`. Conclude with `(map_eq_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).mp ((map_eq_zero (algebraMap F K)).mp hk)`. Establish `hIT : extP K (P.comap ι) ≠ ⊤`. Introduce `htop`. Establish `hle' : extP K (P.comap ι) ≤ P` using `Ideal.map_comap_le`.

Rewrite `hle'` using `[htop]`. Conclude with `hP.ne_top (top_le_iff.mp hle')`. Establish `hsq : extP K (P.comap ι) * extP K (P.comap ι) = extP K (P.comap ι) * ⊤`. Rewrite using `[Ideal.mul_top]`. Use `le_antisymm Ideal.mul_le_right ?_` and prove the remaining obligations.

Rewrite using `[← sq]`. Conclude with `hle`. Conclude with `hIT (mul_left_cancel₀ hI0 hsq)`. Take `⟨p0, hp0, hu⟩` from `hex`. Establish `hu' : κ (ι p0) * π⁻¹ ≠ 0 ∧ κ (ι p0) * π⁻¹ ∈ locRing P ∧ (κ (ι p0) * π⁻¹)⁻¹ ∈ locRing P` using `hu`.

Establish `hy : κ (ι p0) ≠ 0` using `fun h0 => hu'.1 (by rw [h0, zero_mul])`. Use `⟨π, hπ, fun a ha => ?_⟩` and prove the remaining obligations. Take `⟨hav, -⟩` from `vF_spec_of_ne_zero hPm ha`. Establish `hκa : κ (ι a) ≠ 0` using `jK_iota_ne_zero ha`. Rewrite using `[hcoe a]`.

Establish `hιa : ι a ∈ extP K (P.comap ι) ^ vF (P.comap ι) a` using `by show ι a ∈ (Ideal.map ι (P.comap ι)) ^ _`. Rewrite using `[← Ideal.map_pow]`. Conclude with `Ideal.mem_map_of_mem _ hav`. Establish `hxR : κ (ι a) * (π ^ vF (P.comap ι) a)⁻¹ ∈ locRing P` using `mul_inv_pow_mem hF h1 _ (ι a) hιa`. Establish `hb : p0 ^ vF (P.comap ι) a ∈ P.comap ι ^ vF (P.comap ι) a` using `Ideal.pow_mem_pow hp0 _`.

Establish `hdiv` using `div_mem_locRing_of_mem_pow hK hF hP ha hb`. Establish `hinvR : ((κ (ι p0) * π⁻¹)⁻¹) ^ vF (P.comap ι) a ∈ locRing P` using `(locRing P).pow_mem hu'.2.2 _`. Establish `e : (κ (ι a) * (π ^ vF (P.comap ι) a)⁻¹)⁻¹ = ((κ (ι p0) * π⁻¹)⁻¹) ^ vF (P.comap ι) a * (κ (ι (p0 ^ vF (P.comap ι) a)) / κ (ι a))`. Rewrite using `[map_pow, map_pow, mul_inv, inv_inv, mul_inv, inv_inv, mul_pow, inv_pow, div_eq_mul_inv, mul_comm ((κ (ι p0) ^ vF (P.comap ι) a)⁻¹) (π ^ vF (P.comap ι) a), mul_assoc, ← mul_assoc ((κ (ι p0) ^ vF (P.comap ι) a)⁻¹), inv_mul_cancel₀ (pow_ne_zero _ hy), one_mul, mul_comm]`. Use `(⟨mul_ne_zero hκa (inv_ne_zero (pow_ne_zero _ hπ0)), hxR, ?_⟩ : _ ∧ _ ∧ _)` and prove the remaining obligations.

Rewrite using `[e]`. Conclude with `(locRing P).mul_mem hinvR hdiv`.
-/
theorem unifVal_at {P : Ideal (𝓞 K)} (hP : P.IsMaximal) :
    ∃ π : K, IsUnif (locRing P) π ∧ ∀ a : 𝓞 F, a ≠ 0 →
      IsUnitIn (locRing P) (algebraMap F K (a : F) * (π ^ vF (P.comap ι) a)⁻¹) := by
  obtain ⟨π, hπ, h1, h2⟩ := exists_isUnif hF hP
  have hPm : (P.comap ι).IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal P
  have hcoe : ∀ c : 𝓞 F, algebraMap F K (c : F) = κ (ι c) := fun c => by
    rw [← IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 K) K, IsScalarTower.algebraMap_apply (𝓞 F) F K]
  have hstar : ∀ c : 𝓞 F, star (κ (ι c)) = κ (ι c) := fun c => (hF _).mpr ⟨(c : F), hcoe c⟩
  have hπ0 : π ≠ 0 := hπ.3
  have hex : ∃ p0 ∈ P.comap ι, IsUnitIn (locRing P) (κ (ι p0) * π⁻¹) := by
    by_contra hne
    push_neg at hne
    have hle : extP K (P.comap ι) ≤ extP K (P.comap ι) ^ 2 := by
      show Ideal.map ι (P.comap ι) ≤ _
      refine Ideal.map_le_iff_le_comap.mpr fun p0 hp0 => ?_
      show ι p0 ∈ extP K (P.comap ι) ^ 2
      have hmemR : κ (ι p0) * π⁻¹ ∈ locRing P := h1 _ (Ideal.mem_map_of_mem _ hp0)
      have hfix : star (κ (ι p0) * π⁻¹) = κ (ι p0) * π⁻¹ := by
        rw [star_mul', star_inv₀, hπ.2, hstar]
      exact h2 _ ((hπ.4 _ hmemR hfix).resolve_left (hne p0 hp0))
    have hI0 : extP K (P.comap ι) ≠ ⊥ := by
      intro h0
      have hp0 : P.comap ι ≠ ⊥ :=
        Ring.ne_bot_of_isMaximal_of_not_isField hPm (NumberField.RingOfIntegers.not_isField F)
      apply hp0
      rw [eq_bot_iff]
      intro c hc
      have hc' : ι c ∈ extP K (P.comap ι) := Ideal.mem_map_of_mem _ hc
      rw [h0, Ideal.mem_bot] at hc'
      have hk : algebraMap F K (c : F) = 0 := by rw [hcoe, hc', map_zero]
      rw [Ideal.mem_bot]
      exact (map_eq_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).mp
        ((map_eq_zero (algebraMap F K)).mp hk)
    have hIT : extP K (P.comap ι) ≠ ⊤ := by
      intro htop
      have hle' : extP K (P.comap ι) ≤ P := Ideal.map_comap_le
      rw [htop] at hle'
      exact hP.ne_top (top_le_iff.mp hle')
    have hsq : extP K (P.comap ι) * extP K (P.comap ι) = extP K (P.comap ι) * ⊤ := by
      rw [Ideal.mul_top]
      refine le_antisymm Ideal.mul_le_right ?_
      rw [← sq]
      exact hle
    exact hIT (mul_left_cancel₀ hI0 hsq)
  obtain ⟨p0, hp0, hu⟩ := hex
  have hu' : κ (ι p0) * π⁻¹ ≠ 0 ∧ κ (ι p0) * π⁻¹ ∈ locRing P ∧
      (κ (ι p0) * π⁻¹)⁻¹ ∈ locRing P := hu
  have hy : κ (ι p0) ≠ 0 := fun h0 => hu'.1 (by rw [h0, zero_mul])
  refine ⟨π, hπ, fun a ha => ?_⟩
  obtain ⟨hav, -⟩ := vF_spec_of_ne_zero hPm ha
  have hκa : κ (ι a) ≠ 0 := jK_iota_ne_zero ha
  rw [hcoe a]
  have hιa : ι a ∈ extP K (P.comap ι) ^ vF (P.comap ι) a := by
    show ι a ∈ (Ideal.map ι (P.comap ι)) ^ _
    rw [← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ hav
  have hxR : κ (ι a) * (π ^ vF (P.comap ι) a)⁻¹ ∈ locRing P :=
    mul_inv_pow_mem hF h1 _ (ι a) hιa
  have hb : p0 ^ vF (P.comap ι) a ∈ P.comap ι ^ vF (P.comap ι) a := Ideal.pow_mem_pow hp0 _
  have hdiv := div_mem_locRing_of_mem_pow hK hF hP ha hb
  have hinvR : ((κ (ι p0) * π⁻¹)⁻¹) ^ vF (P.comap ι) a ∈ locRing P :=
    (locRing P).pow_mem hu'.2.2 _
  have e : (κ (ι a) * (π ^ vF (P.comap ι) a)⁻¹)⁻¹ =
      ((κ (ι p0) * π⁻¹)⁻¹) ^ vF (P.comap ι) a * (κ (ι (p0 ^ vF (P.comap ι) a)) / κ (ι a)) := by
    rw [map_pow, map_pow, mul_inv, inv_inv, mul_inv, inv_inv, mul_pow, inv_pow, div_eq_mul_inv,
      mul_comm ((κ (ι p0) ^ vF (P.comap ι) a)⁻¹) (π ^ vF (P.comap ι) a), mul_assoc,
      ← mul_assoc ((κ (ι p0) ^ vF (P.comap ι) a)⁻¹), inv_mul_cancel₀ (pow_ne_zero _ hy), one_mul,
      mul_comm]
  refine (⟨mul_ne_zero hκa (inv_ne_zero (pow_ne_zero _ hπ0)), hxR, ?_⟩ : _ ∧ _ ∧ _)
  rw [e]
  exact (locRing P).mul_mem hinvR hdiv

end Formalism.L2.SG.Pf.TemperedBoundGL3

namespace Formalism.L2.SG.Pf.TemperedBoundGL3

/- English proof (translation)
Introduce `K F _ _ _ _ _ _ hK hF P hP`. Conclude with `unifVal_at hK hF hP`.
-/
theorem uniformizer_valuation_holds : G3.UnifVal := by
  intro K F _ _ _ _ _ _ hK hF P hP
  exact unifVal_at hK hF hP

end Formalism.L2.SG.Pf.TemperedBoundGL3
