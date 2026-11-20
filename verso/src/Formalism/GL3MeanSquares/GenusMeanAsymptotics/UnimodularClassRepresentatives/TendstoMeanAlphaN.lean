import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.NkCountLocF
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.StarAlgebraMap

open NumberField Module Filter Topology

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

namespace MeanC

/- English proof (translation)
The claim follows from `Ring.ne_bot_of_isMaximal_of_not_isField h𝔭 (NumberField.RingOfIntegers.not_isField F)`.
-/
theorem ne_bot_of_isMaximal {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) : 𝔭 ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField h𝔭 (NumberField.RingOfIntegers.not_isField F)

/- English proof (translation)
The claim follows from `Ideal.finiteQuotientOfFreeOfNeBot _ (pow_ne_zero k (ne_bot_of_isMaximal h𝔭))`.
-/
theorem finite_quot_pow {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (k : ℕ) : Finite (𝓞 F ⧸ 𝔭 ^ k) := Ideal.finiteQuotientOfFreeOfNeBot _ (pow_ne_zero k (ne_bot_of_isMaximal h𝔭))

/- English proof (translation)
Establish `h0 : Ideal.absNorm 𝔭 ≠ 0` using `fun h => ne_bot_of_isMaximal h𝔭 (Ideal.absNorm_eq_zero_iff.mp h)`. Establish `h1 : Ideal.absNorm 𝔭 ≠ 1` using `fun h => h𝔭.ne_top (Ideal.absNorm_eq_one_iff.mp h)`. Use linear arithmetic over natural numbers and integers.
-/
theorem one_lt_absNorm {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) : 1 < Ideal.absNorm 𝔭 := by
  have h0 : Ideal.absNorm 𝔭 ≠ 0 := fun h => ne_bot_of_isMaximal h𝔭 (Ideal.absNorm_eq_zero_iff.mp h)
  have h1 : Ideal.absNorm 𝔭 ≠ 1 := fun h => h𝔭.ne_top (Ideal.absNorm_eq_one_iff.mp h)
  omega

/- English proof (translation)
Rewrite using `[← map_pow, Ideal.absNorm_apply, Submodule.cardQuot_apply]`.
-/
theorem card_quot_pow (𝔭 : Ideal (𝓞 F)) (k : ℕ) : Nat.card (𝓞 F ⧸ 𝔭 ^ k) = Ideal.absNorm 𝔭 ^ k := by
  rw [← map_pow, Ideal.absNorm_apply, Submodule.cardQuot_apply]

/- English proof (translation)
Establish `hb : BddAbove {e : ℕ | n ∈ 𝔭 ^ e}` using `⟨j, fun e he => by`. Assume the negation of the conclusion as `hlt`. Use `push_neg at hlt`. Conclude with `h (Ideal.pow_le_pow_right hlt.le he)⟩`. Establish `hne : ({e : ℕ | n ∈ 𝔭 ^ e}).Nonempty` using `⟨0, by simp⟩`.

Establish `hm : n ∈ 𝔭 ^ sSup {e : ℕ | n ∈ 𝔭 ^ e}` using `Nat.sSup_mem hne hb`. Unfold `vF`. Assume the negation of the conclusion as `hle`. Use `push_neg at hle`. Conclude with `h (Ideal.pow_le_pow_right hle hm)`.
-/
theorem vF_lt_of_notMem {𝔭 : Ideal (𝓞 F)} {n : 𝓞 F} {j : ℕ} (h : n ∉ 𝔭 ^ j) : vF 𝔭 n < j := by
  have hb : BddAbove {e : ℕ | n ∈ 𝔭 ^ e} := ⟨j, fun e he => by
    by_contra hlt
    push_neg at hlt
    exact h (Ideal.pow_le_pow_right hlt.le he)⟩
  have hne : ({e : ℕ | n ∈ 𝔭 ^ e}).Nonempty := ⟨0, by simp⟩
  have hm : n ∈ 𝔭 ^ sSup {e : ℕ | n ∈ 𝔭 ^ e} := Nat.sSup_mem hne hb
  unfold vF
  by_contra hle
  push_neg at hle
  exact h (Ideal.pow_le_pow_right hle hm)

/- English proof (translation)
Establish `hle : 𝔭 ^ k ≤ 𝔭 ^ j` using `Ideal.pow_le_pow_right hjk`. Set `f : (𝓞 F ⧸ 𝔭 ^ k) →+* (𝓞 F ⧸ 𝔭 ^ j)` to `Ideal.Quotient.factor hle`. Establish `hf : Function.Surjective f` using `Ideal.Quotient.factor_surjective hle`. Establish `hset : ∀ n' : 𝓞 F ⧸ 𝔭 ^ k, Quotient.out n' ∈ 𝔭 ^ j ↔ n' ∈ f.toAddMonoidHom.ker`. Introduce `n'`.

Rewrite using `[AddMonoidHom.mem_ker]`. Use `conv_rhs => rw [← Ideal.Quotient.mk_out n']`. Simplify using `only [RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe, f, Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem]`. Establish `e1 : Nat.card {n' : 𝓞 F ⧸ 𝔭 ^ k // Quotient.out n' ∈ 𝔭 ^ j} = Nat.card f.toAddMonoidHom.ker` using `Nat.card_congr (Equiv.subtypeEquivRight hset)`. Establish `h2 : (f.toAddMonoidHom.ker).index = Nat.card (𝓞 F ⧸ 𝔭 ^ j)` using `Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective _ hf).toEquiv`.

Establish `h1` using `AddSubgroup.card_mul_index (f.toAddMonoidHom.ker)`. Rewrite `h1` using `[h2, card_quot_pow, card_quot_pow]`. Rewrite using `[e1, h1]`.
-/
theorem card_out_mem (𝔭 : Ideal (𝓞 F)) {j k : ℕ} (hjk : j ≤ k) :
    Nat.card {n' : 𝓞 F ⧸ 𝔭 ^ k // Quotient.out n' ∈ 𝔭 ^ j} * Ideal.absNorm 𝔭 ^ j =
      Ideal.absNorm 𝔭 ^ k := by
  have hle : 𝔭 ^ k ≤ 𝔭 ^ j := Ideal.pow_le_pow_right hjk
  let f : (𝓞 F ⧸ 𝔭 ^ k) →+* (𝓞 F ⧸ 𝔭 ^ j) := Ideal.Quotient.factor hle
  have hf : Function.Surjective f := Ideal.Quotient.factor_surjective hle
  have hset : ∀ n' : 𝓞 F ⧸ 𝔭 ^ k,
      Quotient.out n' ∈ 𝔭 ^ j ↔ n' ∈ f.toAddMonoidHom.ker := by
    intro n'
    rw [AddMonoidHom.mem_ker]
    conv_rhs => rw [← Ideal.Quotient.mk_out n']
    simp only [RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe, f,
      Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem]
  have e1 : Nat.card {n' : 𝓞 F ⧸ 𝔭 ^ k // Quotient.out n' ∈ 𝔭 ^ j} =
      Nat.card f.toAddMonoidHom.ker := Nat.card_congr (Equiv.subtypeEquivRight hset)
  have h2 : (f.toAddMonoidHom.ker).index = Nat.card (𝓞 F ⧸ 𝔭 ^ j) :=
    Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective _ hf).toEquiv
  have h1 := AddSubgroup.card_mul_index (f.toAddMonoidHom.ker)
  rw [h2, card_quot_pow, card_quot_pow] at h1
  rw [e1, h1]

end MeanC

/- English proof (translation)
Use `haveI := MeanC.finite_quot_pow h𝔭 k`. Establish `hN` using `MeanC.one_lt_absNorm h𝔭`. Use `haveI : Finite (↥L ⧸ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥L)) := Nat.finite_of_card_ne_zero (by`. Rewrite using `[MeanB.card_quot_extP hK hF hL h𝔭 k]; exact pow_ne_zero _ (by omega))`. Set `nv : ↥L → 𝓞 F` to `fun y => (MeanB.exists_val hF hs hLi y).choose`.

Establish `hnv : ∀ y : ↥L, h (y : V) (y : V) = algebraMap F K (nv y : F)` using `fun y => (MeanB.exists_val hF hs hLi y).choose_spec`. Set `rep : (↥L ⧸ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥L)) → ↥L` to `fun x => (Submodule.Quotient.mk_surjective _ x).choose`. Establish `hrep : ∀ x, Submodule.Quotient.mk (rep x) = x` using `fun x => (Submodule.Quotient.mk_surjective _ x).choose_spec`. Set `φ : (↥L ⧸ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥L)) → 𝓞 F ⧸ 𝔭 ^ k` to `fun x => Ideal.Quotient.mk _ (nv (rep x))`. Establish `hfib : ∀ n' : 𝓞 F ⧸ 𝔭 ^ k, nkCount h L 𝔭 k (Quotient.out n') = Nat.card {x // φ x = n'}`.

Introduce `n'`. Unfold `nkCount`. Use `Nat.card_congr (Equiv.subtypeEquivRight fun x => ?_)` and prove the remaining obligations. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, hc⟩`.

Rewrite `hc` using `[hnv y, MeanB.congrP_algebraMap_iff_sub_mem h𝔭]`. Establish `hyx : rep x - y ∈ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥L)` using `(Submodule.Quotient.eq _).mp ((hrep x).trans hy.symm)`. Establish `h2` using `MeanB.val_congr hF hs hLi 𝔭 k hyx (hnv _) (hnv y)`. Use `show Ideal.Quotient.mk _ (nv (rep x)) = n'`. Use `conv_rhs => rw [← Ideal.Quotient.mk_out n']`.

Rewrite using `[Ideal.Quotient.eq]`. Use `Ideal.add_mem _ h2 hc` as an intermediate fact. Simplify using `using this`. Introduce `hx`. Use `⟨rep x, hrep x, ?_⟩` and prove the remaining obligations.

Rewrite using `[hnv, MeanB.congrP_algebraMap_iff_sub_mem h𝔭]`. Rewrite using `[← Ideal.Quotient.eq, Ideal.Quotient.mk_out]`. Conclude with `hx`. Use `letI := Fintype.ofFinite (𝓞 F ⧸ 𝔭 ^ k)`. Rewrite using `[finsum_eq_sum_of_fintype]`.

Repeatedly rewrite using `[hfib]`. Rewrite using `[← Nat.card_sigma, Nat.card_congr (Equiv.sigmaFiberEquiv φ), MeanB.card_quot_extP hK hF hL h𝔭 k]`.
-/
theorem sum_nkCount (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (k : ℕ) :
    ∑ᶠ n' : 𝓞 F ⧸ 𝔭 ^ k, nkCount h L 𝔭 k (Quotient.out n') =
      Ideal.absNorm 𝔭 ^ (2 * finrank K V * k) := by
  classical
  haveI := MeanC.finite_quot_pow h𝔭 k
  have hN := MeanC.one_lt_absNorm h𝔭
  haveI : Finite (↥L ⧸ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥L)) :=
    Nat.finite_of_card_ne_zero (by
      rw [MeanB.card_quot_extP hK hF hL h𝔭 k]; exact pow_ne_zero _ (by omega))
  let nv : ↥L → 𝓞 F := fun y => (MeanB.exists_val hF hs hLi y).choose
  have hnv : ∀ y : ↥L, h (y : V) (y : V) = algebraMap F K (nv y : F) :=
    fun y => (MeanB.exists_val hF hs hLi y).choose_spec
  let rep : (↥L ⧸ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥L)) → ↥L :=
    fun x => (Submodule.Quotient.mk_surjective _ x).choose
  have hrep : ∀ x, Submodule.Quotient.mk (rep x) = x :=
    fun x => (Submodule.Quotient.mk_surjective _ x).choose_spec
  let φ : (↥L ⧸ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥L)) → 𝓞 F ⧸ 𝔭 ^ k :=
    fun x => Ideal.Quotient.mk _ (nv (rep x))
  have hfib : ∀ n' : 𝓞 F ⧸ 𝔭 ^ k,
      nkCount h L 𝔭 k (Quotient.out n') = Nat.card {x // φ x = n'} := by
    intro n'
    unfold nkCount
    refine Nat.card_congr (Equiv.subtypeEquivRight fun x => ?_)
    constructor
    · rintro ⟨y, hy, hc⟩
      rw [hnv y, MeanB.congrP_algebraMap_iff_sub_mem h𝔭] at hc
      have hyx : rep x - y ∈ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥L) :=
        (Submodule.Quotient.eq _).mp ((hrep x).trans hy.symm)
      have h2 := MeanB.val_congr hF hs hLi 𝔭 k hyx (hnv _) (hnv y)
      show Ideal.Quotient.mk _ (nv (rep x)) = n'
      conv_rhs => rw [← Ideal.Quotient.mk_out n']
      rw [Ideal.Quotient.eq]
      have := Ideal.add_mem _ h2 hc
      simpa using this
    · intro hx
      refine ⟨rep x, hrep x, ?_⟩
      rw [hnv, MeanB.congrP_algebraMap_iff_sub_mem h𝔭]
      rw [← Ideal.Quotient.eq, Ideal.Quotient.mk_out]
      exact hx
  letI := Fintype.ofFinite (𝓞 F ⧸ 𝔭 ^ k)
  rw [finsum_eq_sum_of_fintype]
  simp_rw [hfib]
  rw [← Nat.card_sigma, Nat.card_congr (Equiv.sigmaFiberEquiv φ),
    MeanB.card_quot_extP hK hF hL h𝔭 k]

/- English proof (translation)
Conclude with `firstFamilyOperatorEnd.alphaN_eq hK hF hs hd hL hLi h𝔭 (localValuationFiltration.notMem_pow_vF h𝔭 hn) (by omega)`.
-/
theorem alphaN_eq_of_le (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    {n : 𝓞 F} (hn : n ≠ 0) {k : ℕ} (hk : 2 * vd h L 𝔭 + 2 * vF 𝔭 n + 2 ≤ k) :
    alphaN h L 𝔭 n =
      (nkCount h L 𝔭 k n : ℝ) / (Ideal.absNorm 𝔭 : ℝ) ^ (k * (2 * finrank K V - 1)) := by
  exact firstFamilyOperatorEnd.alphaN_eq hK hF hs hd hL hLi h𝔭 (localValuationFiltration.notMem_pow_vF h𝔭 hn) (by omega)

/- English proof (translation)
Take `⟨C0, hC0⟩` from `nkCount_le hK hF hs hd hL hLi hm h𝔭`. Establish `hN1` using `MeanC.one_lt_absNorm h𝔭`. Establish `hNpos : (0:ℝ) < (Ideal.absNorm 𝔭 : ℝ)` using `by exact_mod_cast (by omega : 0 < Ideal.absNorm 𝔭)`. Establish `hCnn : (0:ℝ) ≤ max C0 0` using `le_max_right _ _`. Establish `hratio : ∀ (k : ℕ) (n : 𝓞 F), (nkCount h L 𝔭 k n : ℝ) / (Ideal.absNorm 𝔭 : ℝ) ^ (k * (2 * finrank K V - 1)) ≤ max C0 0` using `fun k n => by`.

Rewrite using `[div_le_iff₀ (pow_pos hNpos _)]`. Conclude with `(hC0 k n).trans (by gcongr; exact le_max_left _ _)`. Establish `hratio0 : ∀ (k : ℕ) (n : 𝓞 F), 0 ≤ (nkCount h L 𝔭 k n : ℝ) / (Ideal.absNorm 𝔭 : ℝ) ^ (k * (2 * finrank K V - 1))` using `fun k n => by positivity`. Establish `hα : ∀ n : 𝓞 F, n ≠ 0 → |alphaN h L 𝔭 n| ≤ max C0 0`. Introduce `n hn`.

Rewrite using `[alphaN_eq_of_le hK hF hs hd hL hLi h𝔭 hn (k := 2 * vd h L 𝔭 + 2 * vF 𝔭 n + 2) le_rfl, abs_of_nonneg (hratio0 _ _)]`. Conclude with `hratio _ _`. Set `j : ℕ → ℕ` to `fun k => (k - 2 * vd h L 𝔭) / 2`. Establish `hjk : ∀ k, j k ≤ k` using `fun k => by show (k - 2 * vd h L 𝔭) / 2 ≤ k`. Use linear arithmetic over natural numbers and integers.

Establish `hgood : ∀ (k : ℕ) (n : 𝓞 F), n ∉ 𝔭 ^ j k → n ≠ 0 ∧ 2 * vd h L 𝔭 + 2 * vF 𝔭 n + 2 ≤ k`. Introduce `k n hn`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `rfl`. Conclude with `hn (Ideal.zero_mem _)`.

Establish `: vF 𝔭 n < (k - 2 * vd h L 𝔭) / 2` using `MeanC.vF_lt_of_notMem hn`. Use linear arithmetic over natural numbers and integers. Establish `key : ∀ k : ℕ, |(Ideal.absNorm 𝔭 : ℝ) ^ (-(k : ℤ)) * ∑ᶠ n' : 𝓞 F ⧸ 𝔭 ^ k, alphaN h L 𝔭 (Quotient.out n') - 1| ≤ (2 * max C0 0 + |alphaN h L 𝔭 0|) * ((Ideal.absNorm 𝔭 : ℝ)⁻¹) ^ (j k)`. Introduce `k`. Use `haveI := MeanC.finite_quot_pow h𝔭 k`.

Use `letI := Fintype.ofFinite (𝓞 F ⧸ 𝔭 ^ k)`. Establish `hsumr : ∑ n' : 𝓞 F ⧸ 𝔭 ^ k, (nkCount h L 𝔭 k (Quotient.out n') : ℝ) / (Ideal.absNorm 𝔭 : ℝ) ^ (k * (2 * finrank K V - 1)) = (Ideal.absNorm 𝔭 : ℝ) ^ k`. Establish `hS` using `sum_nkCount hK hF hs hd hL hLi h𝔭 k`. Rewrite `hS` using `[finsum_eq_sum_of_fintype]`. Rewrite using `[← Finset.sum_div, ← Nat.cast_sum, hS]`.

Use `push_cast`. Rewrite using `[div_eq_iff (pow_ne_zero _ hNpos.ne'), ← pow_add]`. Use `congr 1`. Establish `h2f : 2 * finrank K V - 1 + 1 = 2 * finrank K V` using `by omega`. Use `nth_rewrite 1 [← h2f]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[finsum_eq_sum_of_fintype]`. Establish `hdiff : (Ideal.absNorm 𝔭 : ℝ) ^ (-(k : ℤ)) * ∑ n' : 𝓞 F ⧸ 𝔭 ^ k, alphaN h L 𝔭 (Quotient.out n') - 1 = (Ideal.absNorm 𝔭 : ℝ) ^ (-(k : ℤ)) * ∑ n' : 𝓞 F ⧸ 𝔭 ^ k, (alphaN h L 𝔭 (Quotient.out n') - (nkCount h L 𝔭 k (Quotient.out n') : ℝ) / (Ideal.absNorm 𝔭 : ℝ) ^ (k * (2 * finrank K V …`. Rewrite using `[Finset.sum_sub_distrib, hsumr, mul_sub, zpow_neg, zpow_natCast, inv_mul_cancel₀ (pow_ne_zero _ hNpos.ne')]`. Rewrite using `[hdiff]`.

Establish `hterm : ∀ n' : 𝓞 F ⧸ 𝔭 ^ k, |alphaN h L 𝔭 (Quotient.out n') - (nkCount h L 𝔭 k (Quotient.out n') : ℝ) / (Ideal.absNorm 𝔭 : ℝ) ^ (k * (2 * finrank K V - 1))| ≤ if Quotient.out n' ∈ 𝔭 ^ j k then 2 * max C0 0 + |alphaN h L 𝔭 0| else 0`. Introduce `n'`. Use `split_ifs with hin`. Establish `h1 : |alphaN h L 𝔭 (Quotient.out n')| ≤ max C0 0 + |alphaN h L 𝔭 0|`. Distinguish the cases in `h0 : Quotient.out n' = 0`.

Rewrite using `[h0]`. Combine the linear equalities and inequalities to obtain the conclusion. Combine the linear relations using `[hα _ h0, abs_nonneg (alphaN h L 𝔭 0)]`. Establish `h2` using `hratio k (Quotient.out n')`. Establish `h3` using `hratio0 k (Quotient.out n')`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[abs_of_nonneg h3]`. Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨hn0, hk⟩` from `hgood k _ hin`. Rewrite using `[alphaN_eq_of_le hK hF hs hd hL hLi h𝔭 hn0 hk, sub_self, abs_zero]`.

Establish `hcount : ((Finset.univ.filter fun n' : 𝓞 F ⧸ 𝔭 ^ k => Quotient.out n' ∈ 𝔭 ^ j k).card : ℝ) * (Ideal.absNorm 𝔭 : ℝ) ^ (j k) = (Ideal.absNorm 𝔭 : ℝ) ^ k`. Establish `h1` using `MeanC.card_out_mem 𝔭 (hjk k)`. Rewrite `h1` using `[Nat.card_eq_fintype_card, Fintype.card_subtype]`. Conclude with `h1` after adjusting the coercions. Rewrite using `[abs_mul, abs_of_pos (zpow_pos hNpos _)]`.

Combine the equalities or inequalities in the displayed calculation. Conclude with `(Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun n' _ => hterm n')`. Use `_ = (Ideal.absNorm 𝔭 : ℝ) ^ (-(k : ℤ)) * (((Finset.univ.filter fun n' : 𝓞 F ⧸ 𝔭 ^ k => Quotient.out n' ∈ 𝔭 ^ j k).card : ℝ) * (2 * max C0 0 + |alphaN h L 𝔭 0|)) := by`. Rewrite using `[Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]`. Use `_ = _ := by`.

Rewrite using `[zpow_neg, zpow_natCast, ← hcount, inv_pow]`. Establish `hc0 : ((Finset.univ.filter fun n' : 𝓞 F ⧸ 𝔭 ^ k => Quotient.out n' ∈ 𝔭 ^ j k).card : ℝ) ≠ 0`. Introduce `h0`. Rewrite `hcount` using `[h0, zero_mul]`. Conclude with `(pow_pos hNpos k).ne' hcount.symm`.

Clear the denominators using the available nonvanishing facts. Establish `hj : Tendsto j atTop atTop`. Use `Filter.tendsto_atTop_atTop.mpr fun b => ⟨2 * b + 2 * vd h L 𝔭, fun k hk => ?_⟩` and prove the remaining obligations. Use `show b ≤ (k - 2 * vd h L 𝔭) / 2`. Use linear arithmetic over natural numbers and integers.

Establish `hlim : Tendsto (fun k => (2 * max C0 0 + |alphaN h L 𝔭 0|) * ((Ideal.absNorm 𝔭 : ℝ)⁻¹) ^ (j k)) atTop (𝓝 0)`. Establish `h1 : Tendsto (fun n : ℕ => ((Ideal.absNorm 𝔭 : ℝ)⁻¹) ^ n) atTop (𝓝 0)` using `tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (inv_lt_one_of_one_lt₀ (by exact_mod_cast hN1))`. Simplify using `using (h1.comp hj).const_mul (2 * max C0 0 + |alphaN h L 𝔭 0|)`. Rewrite using `[tendsto_iff_norm_sub_tendsto_zero]`. Conclude with `squeeze_zero (fun k => norm_nonneg _) (fun k => by rw [Real.norm_eq_abs]; exact key k) hlim`.
-/
theorem tendsto_mean_alphaN (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) (hm : 2 ≤ finrank K V) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) :
    Tendsto (fun k : ℕ => (Ideal.absNorm 𝔭 : ℝ) ^ (-(k : ℤ)) *
      ∑ᶠ n' : 𝓞 F ⧸ 𝔭 ^ k, alphaN h L 𝔭 (Quotient.out n')) atTop (𝓝 1) := by
  classical
  obtain ⟨C0, hC0⟩ := nkCount_le hK hF hs hd hL hLi hm h𝔭
  have hN1 := MeanC.one_lt_absNorm h𝔭
  have hNpos : (0:ℝ) < (Ideal.absNorm 𝔭 : ℝ) := by exact_mod_cast (by omega : 0 < Ideal.absNorm 𝔭)
  have hCnn : (0:ℝ) ≤ max C0 0 := le_max_right _ _
  have hratio : ∀ (k : ℕ) (n : 𝓞 F), (nkCount h L 𝔭 k n : ℝ) /
      (Ideal.absNorm 𝔭 : ℝ) ^ (k * (2 * finrank K V - 1)) ≤ max C0 0 := fun k n => by
    rw [div_le_iff₀ (pow_pos hNpos _)]
    exact (hC0 k n).trans (by gcongr; exact le_max_left _ _)
  have hratio0 : ∀ (k : ℕ) (n : 𝓞 F), 0 ≤ (nkCount h L 𝔭 k n : ℝ) /
      (Ideal.absNorm 𝔭 : ℝ) ^ (k * (2 * finrank K V - 1)) := fun k n => by positivity
  have hα : ∀ n : 𝓞 F, n ≠ 0 → |alphaN h L 𝔭 n| ≤ max C0 0 := by
    intro n hn
    rw [alphaN_eq_of_le hK hF hs hd hL hLi h𝔭 hn (k := 2 * vd h L 𝔭 + 2 * vF 𝔭 n + 2) le_rfl,
      abs_of_nonneg (hratio0 _ _)]
    exact hratio _ _
  let j : ℕ → ℕ := fun k => (k - 2 * vd h L 𝔭) / 2
  have hjk : ∀ k, j k ≤ k := fun k => by
    show (k - 2 * vd h L 𝔭) / 2 ≤ k
    omega
  have hgood : ∀ (k : ℕ) (n : 𝓞 F), n ∉ 𝔭 ^ j k →
      n ≠ 0 ∧ 2 * vd h L 𝔭 + 2 * vF 𝔭 n + 2 ≤ k := by
    intro k n hn
    refine ⟨?_, ?_⟩
    · rintro rfl
      exact hn (Ideal.zero_mem _)
    · have : vF 𝔭 n < (k - 2 * vd h L 𝔭) / 2 := MeanC.vF_lt_of_notMem hn
      omega
  have key : ∀ k : ℕ, |(Ideal.absNorm 𝔭 : ℝ) ^ (-(k : ℤ)) *
      ∑ᶠ n' : 𝓞 F ⧸ 𝔭 ^ k, alphaN h L 𝔭 (Quotient.out n') - 1| ≤
        (2 * max C0 0 + |alphaN h L 𝔭 0|) * ((Ideal.absNorm 𝔭 : ℝ)⁻¹) ^ (j k) := by
    intro k
    haveI := MeanC.finite_quot_pow h𝔭 k
    letI := Fintype.ofFinite (𝓞 F ⧸ 𝔭 ^ k)
    have hsumr : ∑ n' : 𝓞 F ⧸ 𝔭 ^ k, (nkCount h L 𝔭 k (Quotient.out n') : ℝ) /
        (Ideal.absNorm 𝔭 : ℝ) ^ (k * (2 * finrank K V - 1)) = (Ideal.absNorm 𝔭 : ℝ) ^ k := by
      have hS := sum_nkCount hK hF hs hd hL hLi h𝔭 k
      rw [finsum_eq_sum_of_fintype] at hS
      rw [← Finset.sum_div, ← Nat.cast_sum, hS]
      push_cast
      rw [div_eq_iff (pow_ne_zero _ hNpos.ne'), ← pow_add]
      congr 1
      have h2f : 2 * finrank K V - 1 + 1 = 2 * finrank K V := by omega
      nth_rewrite 1 [← h2f]
      ring
    rw [finsum_eq_sum_of_fintype]
    have hdiff : (Ideal.absNorm 𝔭 : ℝ) ^ (-(k : ℤ)) *
        ∑ n' : 𝓞 F ⧸ 𝔭 ^ k, alphaN h L 𝔭 (Quotient.out n') - 1 =
        (Ideal.absNorm 𝔭 : ℝ) ^ (-(k : ℤ)) * ∑ n' : 𝓞 F ⧸ 𝔭 ^ k,
          (alphaN h L 𝔭 (Quotient.out n') - (nkCount h L 𝔭 k (Quotient.out n') : ℝ) /
            (Ideal.absNorm 𝔭 : ℝ) ^ (k * (2 * finrank K V - 1))) := by
      rw [Finset.sum_sub_distrib, hsumr, mul_sub, zpow_neg, zpow_natCast,
        inv_mul_cancel₀ (pow_ne_zero _ hNpos.ne')]
    rw [hdiff]
    have hterm : ∀ n' : 𝓞 F ⧸ 𝔭 ^ k, |alphaN h L 𝔭 (Quotient.out n') -
        (nkCount h L 𝔭 k (Quotient.out n') : ℝ) /
          (Ideal.absNorm 𝔭 : ℝ) ^ (k * (2 * finrank K V - 1))| ≤
        if Quotient.out n' ∈ 𝔭 ^ j k then 2 * max C0 0 + |alphaN h L 𝔭 0| else 0 := by
      intro n'
      split_ifs with hin
      · have h1 : |alphaN h L 𝔭 (Quotient.out n')| ≤ max C0 0 + |alphaN h L 𝔭 0| := by
          by_cases h0 : Quotient.out n' = 0
          · rw [h0]
            linarith
          · linarith [hα _ h0, abs_nonneg (alphaN h L 𝔭 0)]
        have h2 := hratio k (Quotient.out n')
        have h3 := hratio0 k (Quotient.out n')
        calc _ ≤ |alphaN h L 𝔭 (Quotient.out n')| + |(nkCount h L 𝔭 k (Quotient.out n') : ℝ) /
              (Ideal.absNorm 𝔭 : ℝ) ^ (k * (2 * finrank K V - 1))| := abs_sub _ _
          _ ≤ _ := by
            rw [abs_of_nonneg h3]
            linarith
      · obtain ⟨hn0, hk⟩ := hgood k _ hin
        rw [alphaN_eq_of_le hK hF hs hd hL hLi h𝔭 hn0 hk, sub_self, abs_zero]
    have hcount : ((Finset.univ.filter fun n' : 𝓞 F ⧸ 𝔭 ^ k =>
        Quotient.out n' ∈ 𝔭 ^ j k).card : ℝ) * (Ideal.absNorm 𝔭 : ℝ) ^ (j k) =
          (Ideal.absNorm 𝔭 : ℝ) ^ k := by
      have h1 := MeanC.card_out_mem 𝔭 (hjk k)
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at h1
      exact_mod_cast h1
    rw [abs_mul, abs_of_pos (zpow_pos hNpos _)]
    calc _ ≤ (Ideal.absNorm 𝔭 : ℝ) ^ (-(k : ℤ)) * ∑ n' : 𝓞 F ⧸ 𝔭 ^ k,
          (if Quotient.out n' ∈ 𝔭 ^ j k then 2 * max C0 0 + |alphaN h L 𝔭 0| else 0) := by
          gcongr
          exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun n' _ => hterm n')
      _ = (Ideal.absNorm 𝔭 : ℝ) ^ (-(k : ℤ)) * (((Finset.univ.filter fun n' : 𝓞 F ⧸ 𝔭 ^ k =>
          Quotient.out n' ∈ 𝔭 ^ j k).card : ℝ) * (2 * max C0 0 + |alphaN h L 𝔭 0|)) := by
          rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
      _ = _ := by
          rw [zpow_neg, zpow_natCast, ← hcount, inv_pow]
          have hc0 : ((Finset.univ.filter fun n' : 𝓞 F ⧸ 𝔭 ^ k =>
              Quotient.out n' ∈ 𝔭 ^ j k).card : ℝ) ≠ 0 := by
            intro h0
            rw [h0, zero_mul] at hcount
            exact (pow_pos hNpos k).ne' hcount.symm
          field_simp
  have hj : Tendsto j atTop atTop := by
    refine Filter.tendsto_atTop_atTop.mpr fun b => ⟨2 * b + 2 * vd h L 𝔭, fun k hk => ?_⟩
    show b ≤ (k - 2 * vd h L 𝔭) / 2
    omega
  have hlim : Tendsto (fun k => (2 * max C0 0 + |alphaN h L 𝔭 0|) *
      ((Ideal.absNorm 𝔭 : ℝ)⁻¹) ^ (j k)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => ((Ideal.absNorm 𝔭 : ℝ)⁻¹) ^ n) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity)
        (inv_lt_one_of_one_lt₀ (by exact_mod_cast hN1))
    simpa using (h1.comp hj).const_mul (2 * max C0 0 + |alphaN h L 𝔭 0|)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact squeeze_zero (fun k => norm_nonneg _) (fun k => by rw [Real.norm_eq_abs]; exact key k) hlim

end Formalism.HermitianLattices.Ext.L3
