import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.DiscOnto
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.DiagMulMulDiagApply

open NumberField Module Matrix

open scoped Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds

noncomputable section

namespace Formalism.L2.SG.Pf.discriminantGroupCounts

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.G5

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

local notation "ι" => algebraMap (𝓞 F) (𝓞 K)

/- English proof (translation)
Rewrite using `[← map_mul, Ideal.Quotient.eq_zero_iff_mem]`. Establish `hkP : extP K 𝔭 ^ k = extP K 𝔭 ^ (k - e) * extP K 𝔭 ^ e`. Rewrite using `[← pow_add, Nat.sub_add_cancel hek]`. Establish `haP : algebraMap (𝓞 F) (𝓞 K) a ∈ extP K 𝔭 ^ e`. Establish `h1 : algebraMap (𝓞 F) (𝓞 K) a ∈ (𝔭 ^ e).map (algebraMap (𝓞 F) (𝓞 K))` using `Ideal.mem_map_of_mem _ ha`.

Rewrite `h1` using `[Ideal.map_pow]`. Conclude with `h1`. Prove the components needed by the constructor for the conclusion. Introduce `hw`. Take `⟨J, hJ⟩ : 𝔭 ^ e ∣ Ideal.span {a}` from `Ideal.dvd_span_singleton.mpr ha`.

Establish `hJP : J ⊔ 𝔭 = ⊤`. Assume the negation of the conclusion as `hne`. Establish `hle : J ≤ 𝔭` using `le_sup_left.trans (le_of_eq (h𝔭.eq_of_le hne le_sup_right).symm)`. Apply `ha'` to reduce the goal to its premises. Establish `h1 : a ∈ 𝔭 ^ e * J`.

Rewrite using `[← hJ]`. Conclude with `Ideal.mem_span_singleton_self a`. Rewrite using `[pow_succ]`. Conclude with `Ideal.mul_mono_right hle h1`. Establish `hspan : Ideal.span {algebraMap (𝓞 F) (𝓞 K) a} = extP K 𝔭 ^ e * J.map (algebraMap (𝓞 F) (𝓞 K))`.

Establish `h1` using `congrArg (Ideal.map (algebraMap (𝓞 F) (𝓞 K))) hJ`. Rewrite `h1` using `[Ideal.map_span, Set.image_singleton, Ideal.map_mul, Ideal.map_pow]`. Conclude with `h1`. Establish `hcop : IsCoprime (extP K 𝔭 ^ (k - e)) (J.map (algebraMap (𝓞 F) (𝓞 K)))`. Apply `IsCoprime.pow_left` to reduce the goal to its premises.

Rewrite using `[Ideal.isCoprime_iff_sup_eq]`. Establish `h1` using `congrArg (Ideal.map (algebraMap (𝓞 F) (𝓞 K))) hJP`. Rewrite `h1` using `[Ideal.map_sup, Ideal.map_top]`. Rewrite using `[sup_comm]`. Conclude with `h1`.

Establish `hιinj : ∀ x : 𝓞 F, algebraMap (𝓞 F) (𝓞 K) x = 0 → x = 0`. Introduce `x hx`. Establish `h1 : algebraMap F K (algebraMap (𝓞 F) F x) = 0`. Rewrite using `[← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 K) K, hx, map_zero]`. Rewrite `h1` using `[map_eq_zero_iff _ (algebraMap F K).injective]`.

Conclude with `IsFractionRing.injective (𝓞 F) F (by rw [h1, map_zero])`. Establish `ha0 : a ≠ 0` using `fun h => ha' (h ▸ Ideal.zero_mem _)`. Establish `hPe : extP K 𝔭 ^ e ≠ 0`. Rewrite using `[Ne, Ideal.zero_eq_bot]`. Introduce `h0`.

Rewrite `hspan` using `[h0, Ideal.bot_mul, Ideal.span_singleton_eq_bot]`. Conclude with `ha0 (hιinj a hspan)`. Establish `hdiv : extP K 𝔭 ^ (k - e) * extP K 𝔭 ^ e ∣ (Ideal.span {w} * J.map (algebraMap (𝓞 F) (𝓞 K))) * extP K 𝔭 ^ e`. Rewrite using `[← hkP]`. Establish `h2 : extP K 𝔭 ^ k ∣ Ideal.span {w * algebraMap (𝓞 F) (𝓞 K) a}` using `Ideal.dvd_span_singleton.mpr hw`.

Rewrite `h2` using `[← Ideal.span_singleton_mul_span_singleton, hspan, mul_comm (extP K 𝔭 ^ e), ← mul_assoc]`. Conclude with `h2`. Rewrite `hdiv` using `[mul_dvd_mul_iff_right hPe]`. Conclude with `Ideal.dvd_span_singleton.mp (hcop.dvd_of_dvd_mul_right hdiv)`. Introduce `hw`.

Rewrite using `[hkP]`. Conclude with `Ideal.mul_mem_mul hw haP`.
-/
theorem mul_mk_eq_zero_iff {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {a : 𝓞 F} {e k : ℕ}
    (ha : a ∈ 𝔭 ^ e) (ha' : a ∉ 𝔭 ^ (e + 1)) (hek : e ≤ k) (w : 𝓞 K) :
    Ideal.Quotient.mk (extP K 𝔭 ^ k) w * Ideal.Quotient.mk (extP K 𝔭 ^ k) (ι a) = 0 ↔
      w ∈ extP K 𝔭 ^ (k - e) := by
  rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem]
  have hkP : extP K 𝔭 ^ k = extP K 𝔭 ^ (k - e) * extP K 𝔭 ^ e := by
    rw [← pow_add, Nat.sub_add_cancel hek]
  have haP : algebraMap (𝓞 F) (𝓞 K) a ∈ extP K 𝔭 ^ e := by
    have h1 : algebraMap (𝓞 F) (𝓞 K) a ∈ (𝔭 ^ e).map (algebraMap (𝓞 F) (𝓞 K)) :=
      Ideal.mem_map_of_mem _ ha
    rw [Ideal.map_pow] at h1
    exact h1
  constructor
  · intro hw
    obtain ⟨J, hJ⟩ : 𝔭 ^ e ∣ Ideal.span {a} := Ideal.dvd_span_singleton.mpr ha
    have hJP : J ⊔ 𝔭 = ⊤ := by
      by_contra hne
      have hle : J ≤ 𝔭 := le_sup_left.trans (le_of_eq (h𝔭.eq_of_le hne le_sup_right).symm)
      apply ha'
      have h1 : a ∈ 𝔭 ^ e * J := by
        rw [← hJ]
        exact Ideal.mem_span_singleton_self a
      rw [pow_succ]
      exact Ideal.mul_mono_right hle h1
    have hspan : Ideal.span {algebraMap (𝓞 F) (𝓞 K) a} =
        extP K 𝔭 ^ e * J.map (algebraMap (𝓞 F) (𝓞 K)) := by
      have h1 := congrArg (Ideal.map (algebraMap (𝓞 F) (𝓞 K))) hJ
      rw [Ideal.map_span, Set.image_singleton, Ideal.map_mul, Ideal.map_pow] at h1
      exact h1
    have hcop : IsCoprime (extP K 𝔭 ^ (k - e)) (J.map (algebraMap (𝓞 F) (𝓞 K))) := by
      apply IsCoprime.pow_left
      rw [Ideal.isCoprime_iff_sup_eq]
      have h1 := congrArg (Ideal.map (algebraMap (𝓞 F) (𝓞 K))) hJP
      rw [Ideal.map_sup, Ideal.map_top] at h1
      rw [sup_comm]
      exact h1
    have hιinj : ∀ x : 𝓞 F, algebraMap (𝓞 F) (𝓞 K) x = 0 → x = 0 := by
      intro x hx
      have h1 : algebraMap F K (algebraMap (𝓞 F) F x) = 0 := by
        rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 K) K, hx,
          map_zero]
      rw [map_eq_zero_iff _ (algebraMap F K).injective] at h1
      exact IsFractionRing.injective (𝓞 F) F (by rw [h1, map_zero])
    have ha0 : a ≠ 0 := fun h => ha' (h ▸ Ideal.zero_mem _)
    have hPe : extP K 𝔭 ^ e ≠ 0 := by
      rw [Ne, Ideal.zero_eq_bot]
      intro h0
      rw [h0, Ideal.bot_mul, Ideal.span_singleton_eq_bot] at hspan
      exact ha0 (hιinj a hspan)
    have hdiv : extP K 𝔭 ^ (k - e) * extP K 𝔭 ^ e ∣
        (Ideal.span {w} * J.map (algebraMap (𝓞 F) (𝓞 K))) * extP K 𝔭 ^ e := by
      rw [← hkP]
      have h2 : extP K 𝔭 ^ k ∣ Ideal.span {w * algebraMap (𝓞 F) (𝓞 K) a} :=
        Ideal.dvd_span_singleton.mpr hw
      rw [← Ideal.span_singleton_mul_span_singleton, hspan, mul_comm (extP K 𝔭 ^ e),
        ← mul_assoc] at h2
      exact h2
    rw [mul_dvd_mul_iff_right hPe] at hdiv
    exact Ideal.dvd_span_singleton.mp (hcop.dvd_of_dvd_mul_right hdiv)
  · intro hw
    rw [hkP]
    exact Ideal.mul_mem_mul hw haP

/- English proof (translation)
Establish `hle : extP K 𝔭 ^ k ≤ extP K 𝔭 ^ (k - e)` using `Ideal.pow_le_pow_right (Nat.sub_le k e)`. Set `π : 𝓞 K ⧸ extP K 𝔭 ^ k →+* 𝓞 K ⧸ extP K 𝔭 ^ (k - e)` to `Ideal.Quotient.lift (extP K 𝔭 ^ k) (Ideal.Quotient.mk (extP K 𝔭 ^ (k - e))) (fun w hw => Ideal.Quotient.eq_zero_iff_mem.mpr (hle hw))`. Establish `hπ : Function.Surjective π`. Introduce `y`. Take `⟨w, rfl⟩` from `Ideal.Quotient.mk_surjective y`.

Conclude with `⟨Ideal.Quotient.mk _ w, Ideal.Quotient.lift_mk _ _ _⟩`. Establish `hS : Nat.card {z : 𝓞 K ⧸ extP K 𝔭 ^ k // z * Ideal.Quotient.mk (extP K 𝔭 ^ k) (ι a) = 0} = Nat.card π.toAddMonoidHom.ker`. Use `Nat.card_congr (Equiv.subtypeEquivRight fun z => ?_)` and prove the remaining obligations. Take `⟨w, rfl⟩` from `Ideal.Quotient.mk_surjective z`. Rewrite using `[mul_mk_eq_zero_iff h𝔭 ha ha' hek, AddMonoidHom.mem_ker]`.

Conclude with `Ideal.Quotient.eq_zero_iff_mem.symm`. Establish `hcard` using `AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup π.toAddMonoidHom.ker`. Rewrite `hcard` using `[Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective π.toAddMonoidHom hπ).toEquiv, Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds.absNorm_extP_pow hK hF h𝔭, Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds.absNorm_extP_pow hK hF h𝔭, ← hS]`. Establish `hN : Ideal.absNorm 𝔭 ≠ 0`. Rewrite using `[Ne, Ideal.absNorm_eq_zero_iff]`.

Conclude with `Ring.ne_bot_of_isMaximal_of_not_isField h𝔭 (NumberField.RingOfIntegers.not_isField F)`. Establish `h2 : Ideal.absNorm 𝔭 ^ (2 * k) = Ideal.absNorm 𝔭 ^ (2 * (k - e)) * Ideal.absNorm 𝔭 ^ (2 * e)`. Rewrite using `[← pow_add]`. Use `congr 1`. Use linear arithmetic over natural numbers and integers.

Rewrite `hcard` using `[h2]`. Conclude with `(Nat.eq_of_mul_eq_mul_left (pow_pos (Nat.pos_of_ne_zero hN) _) hcard).symm`.
-/
theorem card_ann (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    {a : 𝓞 F} {e k : ℕ} (ha : a ∈ 𝔭 ^ e) (ha' : a ∉ 𝔭 ^ (e + 1)) (hek : e ≤ k) :
    Nat.card {z : 𝓞 K ⧸ extP K 𝔭 ^ k // z * Ideal.Quotient.mk (extP K 𝔭 ^ k) (ι a) = 0} =
      Ideal.absNorm 𝔭 ^ (2 * e) := by
  have hle : extP K 𝔭 ^ k ≤ extP K 𝔭 ^ (k - e) := Ideal.pow_le_pow_right (Nat.sub_le k e)
  let π : 𝓞 K ⧸ extP K 𝔭 ^ k →+* 𝓞 K ⧸ extP K 𝔭 ^ (k - e) :=
    Ideal.Quotient.lift (extP K 𝔭 ^ k) (Ideal.Quotient.mk (extP K 𝔭 ^ (k - e)))
      (fun w hw => Ideal.Quotient.eq_zero_iff_mem.mpr (hle hw))
  have hπ : Function.Surjective π := by
    intro y
    obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨Ideal.Quotient.mk _ w, Ideal.Quotient.lift_mk _ _ _⟩
  have hS : Nat.card {z : 𝓞 K ⧸ extP K 𝔭 ^ k // z * Ideal.Quotient.mk (extP K 𝔭 ^ k) (ι a) = 0} =
      Nat.card π.toAddMonoidHom.ker := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun z => ?_)
    obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective z
    rw [mul_mk_eq_zero_iff h𝔭 ha ha' hek, AddMonoidHom.mem_ker]
    exact Ideal.Quotient.eq_zero_iff_mem.symm
  have hcard := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup π.toAddMonoidHom.ker
  rw [Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective π.toAddMonoidHom hπ).toEquiv,
    Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds.absNorm_extP_pow hK hF h𝔭,
    Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds.absNorm_extP_pow hK hF h𝔭, ← hS] at hcard
  have hN : Ideal.absNorm 𝔭 ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact Ring.ne_bot_of_isMaximal_of_not_isField h𝔭 (NumberField.RingOfIntegers.not_isField F)
  have h2 : Ideal.absNorm 𝔭 ^ (2 * k) =
      Ideal.absNorm 𝔭 ^ (2 * (k - e)) * Ideal.absNorm 𝔭 ^ (2 * e) := by
    rw [← pow_add]
    congr 1
    omega
  rw [h2] at hcard
  exact (Nat.eq_of_mul_eq_mul_left (pow_pos (Nat.pos_of_ne_zero hN) _) hcard).symm

variable [Fact (IsFixF K F)]

/- English proof (translation)
Establish `hF : IsFixF K F` using `Fact.out`. Establish `hfin : Finite (𝓞 K ⧸ extP K 𝔭 ^ k)` using `idealPowerSpanBounds.finite_quot h𝔭 k`. Set `e : Fin m → ℕ` to `fun i => vF 𝔭 (a i)`. Establish `hmem : ∀ i, a i ∈ 𝔭 ^ e i` using `fun i => localValuationFiltration.mem_pow_vF h𝔭 (ha0 i)`. Establish `hnot : ∀ i, a i ∉ 𝔭 ^ (e i + 1)` using `fun i => localValuationFiltration.notMem_pow_vF h𝔭 (ha0 i)`.

Establish `hle : ∀ i, e i ≤ vJof 𝔭 a` using `fun i => Finset.single_le_sum (f := fun j => vF 𝔭 (a j)) (fun j _ => Nat.zero_le _) (Finset.mem_univ i)`. Establish `hsum : ∀ i j, e i + e j + 1 ≤ k` using `fun i j => by`. Use `hle i` as an intermediate fact. Use `hle j` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Set `d : Fin m → 𝓞 K ⧸ extP K 𝔭 ^ k` to `fun i => Ideal.Quotient.mk (extP K 𝔭 ^ k) (ι (a i))`. Establish `hd : ∀ i, star (d i) = d i` using `fun i => by show star (Ideal.Quotient.mk (extP K 𝔭 ^ k) (ι (a i))) = _`. Rewrite using `[idealPowerSpanBounds.star_mk]`. Conclude with `congrArg _ (idealPowerSpanBounds.conjO_map hF (a i))`. Establish `hprod : ∀ i j (z : 𝓞 K ⧸ extP K 𝔭 ^ k), d i * z * d j = z * Ideal.Quotient.mk (extP K 𝔭 ^ k) (ι (a i * a j))` using `fun i j z => by show Ideal.Quotient.mk _ (ι (a i)) * z * Ideal.Quotient.mk _ (ι (a j)) = _`.

Rewrite using `[map_mul, map_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `hpm : ∀ i j, a i * a j ∈ 𝔭 ^ (e i + e j)` using `fun i j => by`. Rewrite using `[pow_add]`. Conclude with `Ideal.mul_mem_mul (hmem i) (hmem j)`.

Establish `hpn : ∀ i j, a i * a j ∉ 𝔭 ^ (e i + e j + 1)` using `fun i j => idealPowerSpanBounds.mul_notMem h𝔭.isPrime (idealPowerSpanBounds.ne_bot h𝔭) (hnot i) (hnot j)`. Take `⟨θ, u, hu⟩` from `reductionMapsOfForms.exists_unit_quot (K := K) hK h𝔭 k`. Establish `hsq : ∀ i j, Nat.card {z // d i * z * d j = 0} = Nat.card {z // z * d i = 0} * Nat.card {z // z * d j = 0}` using `fun i j => by`. Rewrite using `[Nat.card_congr (Equiv.subtypeEquivRight fun z => by rw [hprod i j z]), card_ann hK hF h𝔭 (hpm i j) (hpn i j) (by have := hsum i j; omega), card_ann hK hF h𝔭 (hmem i) (hnot i) (by have := hsum i i; omega), card_ann hK hF h𝔭 (hmem j) (hnot j) (by have := hsum j j; omega), ← pow_ad …`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree. Establish `hent : ∀ T ∈ tSet d, ∀ i j, T i j ∈ (extP K 𝔭).map (Ideal.Quotient.mk (extP K 𝔭 ^ k))`. Introduce `T hT i j`. Take `⟨w, hw⟩` from `Ideal.Quotient.mk_surjective (T i j)`. Establish `h0 : d i * T i j * d j = 0`.

Rewrite using `[← diag_mul_mul_diag_apply, hT.2, Matrix.zero_apply]`. Rewrite `h0` using `[hprod, ← hw, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]`. Establish `h1 : ι (a i * a j) * w ∈ extP K 𝔭 ^ ((e i + e j) + 1)`. Rewrite using `[mul_comm]`. Conclude with `Ideal.pow_le_pow_right (hsum i j) h0`.

Establish `h2` using `idealPowerSpanBounds.mem_of_mul_mem h𝔭 (hpn i j) h1`. Rewrite `h2` using `[pow_one]`. Rewrite using `[← hw]`. Conclude with `Ideal.mem_map_of_mem _ h2`. Conclude with `card_kerX_eq hd hu hsq N fun T hT => hN T hT.1 (hent T hT)`.
-/
theorem kerCount_main (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {m : ℕ}
    {a : Fin m → 𝓞 F} (ha0 : ∀ i, a i ≠ 0) {k : ℕ} (hk : 2 * vJof 𝔭 a + 1 ≤ k) (N : ℕ)
    (hN : ∀ T : Matrix (Fin m) (Fin m) (𝓞 K ⧸ extP K 𝔭 ^ k), Tᴴ = T →
      (∀ i j, T i j ∈ (extP K 𝔭).map (Ideal.Quotient.mk (extP K 𝔭 ^ k))) →
      Nat.card {Y : Matrix (Fin m) (Fin m) (𝓞 K ⧸ extP K 𝔭 ^ k) // phiQ K 𝔭 k a Y = T} = N) :
    Nat.card (kerSet K 𝔭 k a) = N := by
  have hF : IsFixF K F := Fact.out
  have hfin : Finite (𝓞 K ⧸ extP K 𝔭 ^ k) := idealPowerSpanBounds.finite_quot h𝔭 k
  let e : Fin m → ℕ := fun i => vF 𝔭 (a i)
  have hmem : ∀ i, a i ∈ 𝔭 ^ e i := fun i => localValuationFiltration.mem_pow_vF h𝔭 (ha0 i)
  have hnot : ∀ i, a i ∉ 𝔭 ^ (e i + 1) := fun i => localValuationFiltration.notMem_pow_vF h𝔭 (ha0 i)
  have hle : ∀ i, e i ≤ vJof 𝔭 a := fun i =>
    Finset.single_le_sum (f := fun j => vF 𝔭 (a j)) (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
  have hsum : ∀ i j, e i + e j + 1 ≤ k := fun i j => by
    have := hle i; have := hle j; omega
  let d : Fin m → 𝓞 K ⧸ extP K 𝔭 ^ k := fun i => Ideal.Quotient.mk (extP K 𝔭 ^ k) (ι (a i))
  have hd : ∀ i, star (d i) = d i := fun i => by
    show star (Ideal.Quotient.mk (extP K 𝔭 ^ k) (ι (a i))) = _
    rw [idealPowerSpanBounds.star_mk]
    exact congrArg _ (idealPowerSpanBounds.conjO_map hF (a i))
  have hprod : ∀ i j (z : 𝓞 K ⧸ extP K 𝔭 ^ k),
      d i * z * d j = z * Ideal.Quotient.mk (extP K 𝔭 ^ k) (ι (a i * a j)) := fun i j z => by
    show Ideal.Quotient.mk _ (ι (a i)) * z * Ideal.Quotient.mk _ (ι (a j)) = _
    rw [map_mul, map_mul]
    ring
  have hpm : ∀ i j, a i * a j ∈ 𝔭 ^ (e i + e j) := fun i j => by
    rw [pow_add]; exact Ideal.mul_mem_mul (hmem i) (hmem j)
  have hpn : ∀ i j, a i * a j ∉ 𝔭 ^ (e i + e j + 1) := fun i j =>
    idealPowerSpanBounds.mul_notMem h𝔭.isPrime (idealPowerSpanBounds.ne_bot h𝔭) (hnot i) (hnot j)
  obtain ⟨θ, u, hu⟩ := reductionMapsOfForms.exists_unit_quot (K := K) hK h𝔭 k
  have hsq : ∀ i j, Nat.card {z // d i * z * d j = 0} =
      Nat.card {z // z * d i = 0} * Nat.card {z // z * d j = 0} := fun i j => by
    rw [Nat.card_congr (Equiv.subtypeEquivRight fun z => by rw [hprod i j z]),
      card_ann hK hF h𝔭 (hpm i j) (hpn i j) (by have := hsum i j; omega),
      card_ann hK hF h𝔭 (hmem i) (hnot i) (by have := hsum i i; omega),
      card_ann hK hF h𝔭 (hmem j) (hnot j) (by have := hsum j j; omega), ← pow_add]
    congr 1
    ring
  have hent : ∀ T ∈ tSet d, ∀ i j, T i j ∈ (extP K 𝔭).map (Ideal.Quotient.mk (extP K 𝔭 ^ k)) := by
    intro T hT i j
    obtain ⟨w, hw⟩ := Ideal.Quotient.mk_surjective (T i j)
    have h0 : d i * T i j * d j = 0 := by
      rw [← diag_mul_mul_diag_apply, hT.2, Matrix.zero_apply]
    rw [hprod, ← hw, ← map_mul, Ideal.Quotient.eq_zero_iff_mem] at h0
    have h1 : ι (a i * a j) * w ∈ extP K 𝔭 ^ ((e i + e j) + 1) := by
      rw [mul_comm]; exact Ideal.pow_le_pow_right (hsum i j) h0
    have h2 := idealPowerSpanBounds.mem_of_mul_mem h𝔭 (hpn i j) h1
    rw [pow_one] at h2
    rw [← hw]
    exact Ideal.mem_map_of_mem _ h2
  exact card_kerX_eq hd hu hsq N fun T hT => hN T hT.1 (hent T hT)

end Formalism.L2.SG.Pf.discriminantGroupCounts

namespace Formalism.L2.SG.Pf.Cnt

/- English proof (translation)
Introduce `K F _ _ _ _ _ _ _ hK 𝔭 h𝔭 m a ha0 k hk N hN`. Conclude with `Formalism.L2.SG.Pf.discriminantGroupCounts.kerCount_main hK h𝔭 ha0 hk N hN`.
-/
theorem kernel_counting_holds : Formalism.L2.SG.Pf.G5.KerCount := by
  intro K F _ _ _ _ _ _ _ hK 𝔭 h𝔭 m a ha0 k hk N hN
  exact Formalism.L2.SG.Pf.discriminantGroupCounts.kerCount_main hK h𝔭 ha0 hk N hN

end Formalism.L2.SG.Pf.Cnt
