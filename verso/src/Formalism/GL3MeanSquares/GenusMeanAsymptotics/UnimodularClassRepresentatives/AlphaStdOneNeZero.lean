import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.NkCountLocF
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.NormOneMkIff

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

namespace U3

open ExtendedPrimeIdeals EndomorphismScalars NormOneGroup

/- English proof (translation)
Rewrite using `[← absNorm_eq_card, map_pow, ThirdPropositionSlot.absNorm_extP hK hF, ← pow_mul]`.
-/
theorem absNorm_extP_pow (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (𝔭 : Ideal (𝓞 F))
    (k : ℕ) : Nat.card (𝓞 K ⧸ extP K 𝔭 ^ k) = Ideal.absNorm 𝔭 ^ (2 * k) := by
  rw [← absNorm_eq_card, map_pow, ThirdPropositionSlot.absNorm_extP hK hF, ← pow_mul]

/- English proof (translation)
The claim follows from `Nat.pos_of_ne_zero (mt Ideal.absNorm_eq_zero_iff.1 (ne_bot_of_isMaximal h𝔭))`.
-/
theorem absNorm_pos {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) : 0 < Ideal.absNorm 𝔭 :=
  Nat.pos_of_ne_zero (mt Ideal.absNorm_eq_zero_iff.1 (ne_bot_of_isMaximal h𝔭))

/- English proof (translation)
Take `⟨e, he⟩` from `exists_isGen hL h1 h𝔭`. Take `⟨n, hn⟩` from `MeanB.exists_val hF hs hLi ⟨e, he.1⟩`. Take `⟨hv, hv'⟩` from `vd_spec hF hd h1 h𝔭 he hn`. Generalize the expression as in `vd h L 𝔭 = v at hv hv' hvk ⊢`. Establish `hq` using `absNorm_pos h𝔭`.

Establish `hfin : Finite (𝓞 K ⧸ extP K 𝔭 ^ k)` using `Nat.finite_of_card_ne_zero (by`. Rewrite using `[absNorm_extP_pow hK hF]`. Use the proof step `positivity)`. Set `π : (𝓞 K ⧸ extP K 𝔭 ^ k) →+* (𝓞 K ⧸ extP K 𝔭 ^ (k - v))` to `Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.sub_le k v))`. Establish `hπ : Function.Surjective π` using `Ideal.Quotient.factor_surjective _`.

Establish `s1 : akCount h L 𝔭 k = Nat.card {a : 𝓞 K ⧸ extP K 𝔭 ^ k // NormOne (extP K 𝔭 ^ (k - v)) (π a)}`. Unfold `akCount`. Use `(Nat.card_congr (Equiv.subtypeEquiv (Equiv.ofBijective _ (endHom_bijective h𝔭 he k)) fun a => ?_)).symm` and prove the remaining obligations. Take `⟨b, rfl⟩` from `Ideal.Quotient.mk_surjective a`. Rewrite using `[Equiv.ofBijective_apply, endHom_mk, cond_iff hF hs hLi h𝔭 he hn hv hv' hvk b]`.

Conclude with `normOne_mk_iff hF 𝔭 (k - v) b`. Establish `s2 : Nat.card {a : 𝓞 K ⧸ extP K 𝔭 ^ k // NormOne (extP K 𝔭 ^ (k - v)) (π a)} = _` using `HermitianSublattices.card_preimage π.toAddMonoidHom hπ (NormOne (extP K 𝔭 ^ (k - v)))`. Establish `s3 : Nat.card {a : 𝓞 K ⧸ extP K 𝔭 ^ k // True} = _` using `HermitianSublattices.card_preimage π.toAddMonoidHom hπ (fun _ => True)`. Rewrite `s3` using `[Nat.card_congr (Equiv.subtypeUnivEquiv fun _ => trivial), Nat.card_congr (Equiv.subtypeUnivEquiv fun _ => trivial), absNorm_extP_pow hK hF, absNorm_extP_pow hK hF]`. Establish `s4 : Nat.card π.toAddMonoidHom.ker = Ideal.absNorm 𝔭 ^ (2 * v)`.

Apply `Nat.eq_of_mul_eq_mul_right (pow_pos hq (2 * (k - v)))` to reduce the goal to its premises. Rewrite using `[← s3, ← pow_add]`. Use `congr 1`. Use linear arithmetic over natural numbers and integers. Rewrite using `[s1, s2, s4, card_normOne]`.
-/
theorem akCount_eq (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) (h1 : finrank K V = 1)
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {k : ℕ} (hvk : vd h L 𝔭 ≤ k) :
    akCount h L 𝔭 k = Ideal.absNorm 𝔭 ^ (2 * vd h L 𝔭) *
      normRepCount K (extP K 𝔭 ^ (k - vd h L 𝔭)) 1 1 := by
  obtain ⟨e, he⟩ := exists_isGen hL h1 h𝔭
  obtain ⟨n, hn⟩ := MeanB.exists_val hF hs hLi ⟨e, he.1⟩
  obtain ⟨hv, hv'⟩ := vd_spec hF hd h1 h𝔭 he hn
  generalize vd h L 𝔭 = v at hv hv' hvk ⊢
  have hq := absNorm_pos h𝔭
  have hfin : Finite (𝓞 K ⧸ extP K 𝔭 ^ k) := Nat.finite_of_card_ne_zero (by
    rw [absNorm_extP_pow hK hF]
    positivity)
  let π : (𝓞 K ⧸ extP K 𝔭 ^ k) →+* (𝓞 K ⧸ extP K 𝔭 ^ (k - v)) :=
    Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.sub_le k v))
  have hπ : Function.Surjective π := Ideal.Quotient.factor_surjective _
  have s1 : akCount h L 𝔭 k =
      Nat.card {a : 𝓞 K ⧸ extP K 𝔭 ^ k // NormOne (extP K 𝔭 ^ (k - v)) (π a)} := by
    unfold akCount
    refine (Nat.card_congr (Equiv.subtypeEquiv
      (Equiv.ofBijective _ (endHom_bijective h𝔭 he k)) fun a => ?_)).symm
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective a
    rw [Equiv.ofBijective_apply, endHom_mk, cond_iff hF hs hLi h𝔭 he hn hv hv' hvk b]
    exact normOne_mk_iff hF 𝔭 (k - v) b
  have s2 : Nat.card {a : 𝓞 K ⧸ extP K 𝔭 ^ k // NormOne (extP K 𝔭 ^ (k - v)) (π a)} = _ :=
    HermitianSublattices.card_preimage π.toAddMonoidHom hπ (NormOne (extP K 𝔭 ^ (k - v)))
  have s3 : Nat.card {a : 𝓞 K ⧸ extP K 𝔭 ^ k // True} = _ :=
    HermitianSublattices.card_preimage π.toAddMonoidHom hπ (fun _ => True)
  rw [Nat.card_congr (Equiv.subtypeUnivEquiv fun _ => trivial),
    Nat.card_congr (Equiv.subtypeUnivEquiv fun _ => trivial), absNorm_extP_pow hK hF,
    absNorm_extP_pow hK hF] at s3
  have s4 : Nat.card π.toAddMonoidHom.ker = Ideal.absNorm 𝔭 ^ (2 * v) := by
    apply Nat.eq_of_mul_eq_mul_right (pow_pos hq (2 * (k - v)))
    rw [← s3, ← pow_add]
    congr 1
    omega
  rw [s1, s2, s4, card_normOne]

/- English proof (translation)
Establish `h2 : (2 : ℝ) ≤ (Ideal.absNorm 𝔭 : ℝ)`. Establish `h0` using `absNorm_pos h𝔭`. Establish `h1 : Ideal.absNorm 𝔭 ≠ 1` using `mt Ideal.absNorm_eq_one_iff.1 h𝔭.ne_top`. Conclude with `(show 2 ≤ Ideal.absNorm 𝔭 by omega)` after adjusting the coercions. Establish `h3 : (Ideal.absNorm 𝔭 : ℝ)⁻¹ ≤ 2⁻¹` using `inv_anti₀ (by norm_num) h2`.

Establish `h4 : 0 < (Ideal.absNorm 𝔭 : ℝ)⁻¹` using `inv_pos.2 (by linarith)`. Rewrite using `[ThirdPropositionSlot.alphaStd_one]`. Unfold `etaF`. Use `split_ifs`. Use the polynomial consequences of the given equalities and inequalities.

Use the polynomial consequences of the given equalities and inequalities.
-/
theorem alphaStd_one_ne_zero {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) : alphaStd K 𝔭 1 ≠ 0 := by
  have h2 : (2 : ℝ) ≤ (Ideal.absNorm 𝔭 : ℝ) := by
    have h0 := absNorm_pos h𝔭
    have h1 : Ideal.absNorm 𝔭 ≠ 1 := mt Ideal.absNorm_eq_one_iff.1 h𝔭.ne_top
    exact_mod_cast (show 2 ≤ Ideal.absNorm 𝔭 by omega)
  have h3 : (Ideal.absNorm 𝔭 : ℝ)⁻¹ ≤ 2⁻¹ := inv_anti₀ (by norm_num) h2
  have h4 : 0 < (Ideal.absNorm 𝔭 : ℝ)⁻¹ := inv_pos.2 (by linarith)
  rw [ThirdPropositionSlot.alphaStd_one]
  unfold etaF
  split_ifs
  · nlinarith
  · nlinarith

/- English proof (translation)
Establish `hq : (Ideal.absNorm 𝔭 : ℝ) ≠ 0` using `by exact_mod_cast (absNorm_pos h𝔭).ne'`. Unfold `alphaL`. Apply `Filter.Tendsto.limUnder_eq` to reduce the goal to its premises. Apply `tendsto_const_nhds.congr'` to reduce the goal to its premises. Use `filter_upwards [Filter.eventually_ge_atTop (vd h L 𝔭 + 1)] with k hk`.

Rewrite using `[akCount_eq hK hF hs hd hL hLi h1 h𝔭 (by omega), h1]`. Use `push_cast`. Rewrite using `[ThirdPropositionSlot.normRepCount_extP hK hF h𝔭 (by omega), eq_div_iff (pow_ne_zero _ hq)]`. Establish `e1 : (Ideal.absNorm 𝔭 : ℝ) ^ (2 * vd h L 𝔭) * (Ideal.absNorm 𝔭 : ℝ) ^ (k - vd h L 𝔭) = (Ideal.absNorm 𝔭 : ℝ) ^ vd h L 𝔭 * (Ideal.absNorm 𝔭 : ℝ) ^ (k * 1 ^ 2)`. Rewrite using `[← pow_add, ← pow_add]`.

Use `congr 1`. Rewrite using `[one_pow, mul_one]`. Use linear arithmetic over natural numbers and integers. Take the linear combination `(-alphaStd K 𝔭 1) * e1`.
-/
theorem alphaL_eq (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) (h1 : finrank K V = 1)
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) :
    alphaL h L 𝔭 = (Ideal.absNorm 𝔭 : ℝ) ^ vd h L 𝔭 * alphaStd K 𝔭 1 := by
  have hq : (Ideal.absNorm 𝔭 : ℝ) ≠ 0 := by exact_mod_cast (absNorm_pos h𝔭).ne'
  unfold alphaL
  apply Filter.Tendsto.limUnder_eq
  apply tendsto_const_nhds.congr'
  filter_upwards [Filter.eventually_ge_atTop (vd h L 𝔭 + 1)] with k hk
  rw [akCount_eq hK hF hs hd hL hLi h1 h𝔭 (by omega), h1]
  push_cast
  rw [ThirdPropositionSlot.normRepCount_extP hK hF h𝔭 (by omega), eq_div_iff (pow_ne_zero _ hq)]
  have e1 : (Ideal.absNorm 𝔭 : ℝ) ^ (2 * vd h L 𝔭) * (Ideal.absNorm 𝔭 : ℝ) ^ (k - vd h L 𝔭) =
      (Ideal.absNorm 𝔭 : ℝ) ^ vd h L 𝔭 * (Ideal.absNorm 𝔭 : ℝ) ^ (k * 1 ^ 2) := by
    rw [← pow_add, ← pow_add]
    congr 1
    rw [one_pow, mul_one]
    omega
  linear_combination (-alphaStd K 𝔭 1) * e1

end U3

/- English proof (translation)
Establish `hq : (Ideal.absNorm 𝔭 : ℝ) ≠ 0` using `by exact_mod_cast (U3.absNorm_pos h𝔭).ne'`. Unfold `lamP`. Rewrite using `[U3.alphaL_eq hK hF hs hd hL hLi h1 h𝔭, h1, one_mul, mul_comm]`. Conclude with `div_self (mul_ne_zero (pow_ne_zero _ hq) (U3.alphaStd_one_ne_zero h𝔭))`.
-/
theorem localFactor_rank_one (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) (h1 : finrank K V = 1) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) :
    lamP h L 𝔭 = 1 := by
  have hq : (Ideal.absNorm 𝔭 : ℝ) ≠ 0 := by exact_mod_cast (U3.absNorm_pos h𝔭).ne'
  unfold lamP
  rw [U3.alphaL_eq hK hF hs hd hL hLi h1 h𝔭, h1, one_mul, mul_comm]
  exact div_self (mul_ne_zero (pow_ne_zero _ hq) (U3.alphaStd_one_ne_zero h𝔭))

end Formalism.HermitianLattices.Ext.L3
