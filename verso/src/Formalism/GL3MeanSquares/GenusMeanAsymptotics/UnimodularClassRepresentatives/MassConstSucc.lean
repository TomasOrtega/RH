import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.RepMassEqProdPsi
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.TendstoBallCount
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.TendstoSingSSum
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.MassRatioEqLvalue
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.LamGEqOneOfOrtho
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.IsClassRepsMap
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.FactorIdentity

open NumberField Module Filter Topology

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

namespace Step

/- English proof (translation)
Establish `hD'` using `hD.ne'`. Establish `hP'` using `hP.ne'`. Establish `ha'` using `ha.ne'`. Establish `hmm'` using `hmm.ne'`. Establish `hvv'` using `hvv.ne'`.

Establish `hsq'` using `hsq.ne'`. Establish `hX : (P / (mm * a)) ^ f / (vv * D) ≠ 0` using `by positivity`. Rewrite `h` using `[zero_add]`. Rewrite using `[eq_div_of_mul_eq hX h, div_pow, mul_pow, div_pow]`. Clear the denominators using the available nonvanishing facts.
-/
theorem final_algebra (μ c lam D P a mm vv sq lV : ℝ) (f : ℕ) (hD : 0 < D) (hP : 0 < P)
    (ha : 0 < a) (hmm : 0 < mm) (hvv : 0 < vv) (hsq : 0 < sq)
    (h : μ * ((P / (mm * a)) ^ f / (vv * D)) = 0 + c * lam * D⁻¹ * ((mm ^ f)⁻¹ / sq * lV)) :
    μ = c * ((a / P) ^ f * vv / sq * lV) * lam := by
  have hD' := hD.ne'
  have hP' := hP.ne'
  have ha' := ha.ne'
  have hmm' := hmm.ne'
  have hvv' := hvv.ne'
  have hsq' := hsq.ne'
  have hX : (P / (mm * a)) ^ f / (vv * D) ≠ 0 := by positivity
  rw [zero_add] at h
  rw [eq_div_of_mul_eq hX h, div_pow, mul_pow, div_pow]
  field_simp

variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

/- English proof (translation)
Establish `hd' : ∀ x, h x x = 0 → x = 0`. Introduce `x hx`. Assume the negation of the conclusion as `hne`. Take `⟨φ⟩ : Nonempty (K →+* ℂ)` from `inferInstance`. Use `hd x hne φ` as an intermediate fact.

Simplify using `[hx] at this`. Establish `hne` using `LocF.discrIdeal_ne_bot hd' hL hLi`. Unfold `normD`. Apply `Real.sqrt_pos.mpr` to reduce the goal to its premises. Establish `: Ideal.absNorm (discrIdeal h L) ≠ 0` using `Ideal.absNorm_eq_zero_iff.not.mpr hne`.

Conclude with `Nat.pos_of_ne_zero this` after adjusting the coercions.
-/
theorem normD_pos {h : V →ₗ⋆[K] V →ₗ[K] K} (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) : 0 < normD h L := by
  have hd' : ∀ x, h x x = 0 → x = 0 := by
    intro x hx
    by_contra hne
    obtain ⟨φ⟩ : Nonempty (K →+* ℂ) := inferInstance
    have := hd x hne φ
    simp [hx] at this
  have hne := LocF.discrIdeal_ne_bot hd' hL hLi
  unfold normD
  apply Real.sqrt_pos.mpr
  have : Ideal.absNorm (discrIdeal h L) ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr hne
  exact_mod_cast Nat.pos_of_ne_zero this

/- English proof (translation)
Rewrite using `[RankOne.mass_eq_sum h L s hsr, Finset.sum_mul]`. Repeatedly rewrite using `[Finset.sum_div]`. Use `tendsto_finsetSum _ fun M hM => ?_` and prove the remaining obligations. Establish `hg` using `hsr.1 M hM`. Take `⟨hMi, -, hMD⟩` from `integral_of_mem_genus hK hF hs hd hL hLi hg`.

Establish `ht` using `(tendsto_ballCount hK hF hs hd hg.1 hMi).const_mul ((Nat.card (Formalism.ThetaLiftIndependence.autL h M) : ℝ)⁻¹)`. Rewrite `ht` using `[hMD]`. Use `ht.congr fun j => ?_` and prove the remaining obligations. Rewrite using `[div_eq_mul_inv (ballCount h M ((j : ℝ) ^ 2) : ℝ), div_eq_mul_inv, div_eq_mul_inv]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem tendsto_left (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L)
    {s : Finset (Submodule (𝓞 K) V)} (hsr : Formalism.ThetaLiftIndependence.IsClassReps h L s) :
    Tendsto (fun j : ℕ => (∑ M ∈ s, (ballCount h M ((j : ℝ) ^ 2) : ℝ) /
        (Nat.card (Formalism.ThetaLiftIndependence.autL h M) : ℝ)) / (j : ℝ) ^ (2 * Formalism.HermitianLatticesTheory.fDeg K * finrank K V))
      atTop (𝓝 (Formalism.HermitianLatticesTheory.mass h L *
        ((Real.pi ^ finrank K V / ((finrank K V).factorial : ℝ)) ^ Formalism.HermitianLatticesTheory.fDeg K /
          (Formalism.HermitianLatticesTheory.vInv K ^ (Formalism.HermitianLatticesTheory.fDeg K * finrank K V) * normD h L)))) := by
  rw [RankOne.mass_eq_sum h L s hsr, Finset.sum_mul]
  simp_rw [Finset.sum_div]
  refine tendsto_finsetSum _ fun M hM => ?_
  have hg := hsr.1 M hM
  obtain ⟨hMi, -, hMD⟩ := integral_of_mem_genus hK hF hs hd hL hLi hg
  have ht := (tendsto_ballCount hK hF hs hd hg.1 hMi).const_mul
    ((Nat.card (Formalism.ThetaLiftIndependence.autL h M) : ℝ)⁻¹)
  rw [hMD] at ht
  refine ht.congr fun j => ?_
  rw [div_eq_mul_inv (ballCount h M ((j : ℝ) ^ 2) : ℝ), div_eq_mul_inv, div_eq_mul_inv]
  ring

/- English proof (translation)
Establish `hf : 0 < Formalism.HermitianLatticesTheory.fDeg K` using `Fintype.card_pos`. Establish `hexp : 2 * Formalism.HermitianLatticesTheory.fDeg K * finrank K V ≠ 0` using `by positivity`. Establish `h1 : Tendsto (fun j : ℕ => Formalism.HermitianLatticesTheory.mass h L / (j : ℝ) ^ (2 * Formalism.HermitianLatticesTheory.fDeg K * finrank K V)) atTop (𝓝 0)` using `tendsto_const_nhds.div_atTop ((tendsto_pow_atTop hexp).comp tendsto_natCast_atTop_atTop)`. Establish `h2` using `(tendsto_singS_sum hK hF hs hd hL hLi hm).const_mul (c * lamG F h L * (normD h L)⁻¹)`. Use `(h1.add h2).congr fun j => ?_` and prove the remaining obligations.

Rewrite using `[add_div]`. Use `congr 1`. Rewrite using `[finsum_mem_congr rfl fun n hn => repMass_eq hH hLI hK hF hs hd hL hLi hm hc hn, finsum_mem_eq_finite_toFinset_sum _ (A5.boxSet_finite hK hF ((j : ℝ) ^ 2)), finsum_mem_eq_finite_toFinset_sum _ (A5.boxSet_finite hK hF ((j : ℝ) ^ 2)), ← Finset.mul_sum, zpow_neg, zpow_natCast, ← pow …`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem tendsto_right (hH : HermRepUnram) (hLI : LIStat) (hK : Formalism.HermitianLatticesTheory.IsCMUnram K)
    (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h)
    {L : Submodule (𝓞 K) V} (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L)
    (hm : 2 ≤ finrank K V) {c : ℝ} (hc : MassConst K F (finrank K V - 1) c) :
    Tendsto (fun j : ℕ => (Formalism.HermitianLatticesTheory.mass h L + ∑ᶠ n ∈ boxSet K F ((j : ℝ) ^ 2),
        repMass h L (algebraMap F K (n : F))) / (j : ℝ) ^ (2 * Formalism.HermitianLatticesTheory.fDeg K * finrank K V))
      atTop (𝓝 (0 + c * lamG F h L * (normD h L)⁻¹ *
        ((finrank K V : ℝ) ^ (-(Formalism.HermitianLatticesTheory.fDeg K : ℤ)) /
          Real.sqrt ((2 * Formalism.HermitianLatticesTheory.vInv K) ^ Formalism.HermitianLatticesTheory.fDeg K) * lValEtaF K F (finrank K V)))) := by
  have hf : 0 < Formalism.HermitianLatticesTheory.fDeg K := Fintype.card_pos
  have hexp : 2 * Formalism.HermitianLatticesTheory.fDeg K * finrank K V ≠ 0 := by positivity
  have h1 : Tendsto (fun j : ℕ => Formalism.HermitianLatticesTheory.mass h L /
      (j : ℝ) ^ (2 * Formalism.HermitianLatticesTheory.fDeg K * finrank K V)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop ((tendsto_pow_atTop hexp).comp tendsto_natCast_atTop_atTop)
  have h2 := (tendsto_singS_sum hK hF hs hd hL hLi hm).const_mul
    (c * lamG F h L * (normD h L)⁻¹)
  refine (h1.add h2).congr fun j => ?_
  rw [add_div]
  congr 1
  rw [finsum_mem_congr rfl fun n hn => repMass_eq hH hLI hK hF hs hd hL hLi hm hc hn,
    finsum_mem_eq_finite_toFinset_sum _ (A5.boxSet_finite hK hF ((j : ℝ) ^ 2)),
    finsum_mem_eq_finite_toFinset_sum _ (A5.boxSet_finite hK hF ((j : ℝ) ^ 2)),
    ← Finset.mul_sum, zpow_neg, zpow_natCast, ← pow_mul, ← mul_assoc 2, div_eq_mul_inv]
  ring

end Step

/- English proof (translation)
Unfold `MassConst`. Introduce `V _ _ _ _ _ h L hs hd hfin hL hLi`. Substitute `hfin` using the available equality. Take `⟨s, hsr⟩` from `StabilizerLattices.exists_classReps hs hd hL`. Establish `hlim` using `Step.tendsto_left hK hF hs hd hL hLi hsr`.

Establish `hlim2` using `Step.tendsto_right hH hLI hK hF hs hd hL hLi hm hc`. Establish `hfun : (fun j : ℕ => (∑ M ∈ s, (ballCount h M ((j : ℝ) ^ 2) : ℝ) / (Nat.card (Formalism.ThetaLiftIndependence.autL h M) : ℝ)) / (j : ℝ) ^ (2 * Formalism.HermitianLatticesTheory.fDeg K * finrank K V)) = fun j : ℕ => (Formalism.HermitianLatticesTheory.mass h L + ∑ᶠ n ∈ boxSet K F ( …`. Use function extensionality and compare the values at `j`. Rewrite using `[sum_ballCount_eq hK hF hs hd hL hLi hsr (by positivity)]`. Rewrite `hlim` using `[hfun]`.

Establish `hAB` using `tendsto_nhds_unique hlim hlim2`. Establish `hn0 : 0 < finrank K V` using `by omega`. Establish `hfact : ((finrank K V).factorial : ℝ) = (finrank K V : ℝ) * ((finrank K V - 1).factorial : ℝ)`. Rewrite using `[← Nat.mul_factorial_pred hn0.ne']`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Rewrite `hAB` using `[hfact, zpow_neg, zpow_natCast]`. Establish `hv` using `vInv_pos K`. Establish `key` using `Step.final_algebra (Formalism.HermitianLatticesTheory.mass h L) c (lamG F h L) (normD h L) (Real.pi ^ finrank K V) ((finrank K V - 1).factorial : ℝ) (finrank K V : ℝ) (Formalism.HermitianLatticesTheory.vInv K ^ (Formalism.HermitianLatticesTheory.fDeg K * finrank K V)) (Real.sqrt …`. Rewrite using `[massRatio_eq_lvalue hK hF (finrank K V) hm]`.

Conclude with `key`.
-/
theorem massConst_succ (hH : HermRepUnram) (hLI : LIStat) (hK : Formalism.HermitianLatticesTheory.IsCMUnram K)
    (hF : IsFixF K F) {m : ℕ} (hm : 2 ≤ m) {c : ℝ} (hc0 : 0 < c) (hc : MassConst K F (m - 1) c) :
    MassConst K F m (c * Formalism.HermitianLatticesTheory.massRatioRightSide K m) := by
  unfold MassConst
  intro V _ _ _ _ _ h L hs hd hfin hL hLi
  subst hfin
  obtain ⟨s, hsr⟩ := StabilizerLattices.exists_classReps hs hd hL
  have hlim := Step.tendsto_left hK hF hs hd hL hLi hsr
  have hlim2 := Step.tendsto_right hH hLI hK hF hs hd hL hLi hm hc
  have hfun : (fun j : ℕ => (∑ M ∈ s, (ballCount h M ((j : ℝ) ^ 2) : ℝ) /
        (Nat.card (Formalism.ThetaLiftIndependence.autL h M) : ℝ)) / (j : ℝ) ^ (2 * Formalism.HermitianLatticesTheory.fDeg K * finrank K V)) =
      fun j : ℕ => (Formalism.HermitianLatticesTheory.mass h L + ∑ᶠ n ∈ boxSet K F ((j : ℝ) ^ 2),
        repMass h L (algebraMap F K (n : F))) / (j : ℝ) ^ (2 * Formalism.HermitianLatticesTheory.fDeg K * finrank K V) := by
    funext j
    rw [sum_ballCount_eq hK hF hs hd hL hLi hsr (by positivity)]
  rw [hfun] at hlim
  have hAB := tendsto_nhds_unique hlim hlim2
  have hn0 : 0 < finrank K V := by omega
  have hfact : ((finrank K V).factorial : ℝ) =
      (finrank K V : ℝ) * ((finrank K V - 1).factorial : ℝ) := by
    rw [← Nat.mul_factorial_pred hn0.ne']
    push_cast
    ring
  rw [hfact, zpow_neg, zpow_natCast] at hAB
  have hv := vInv_pos K
  have key := Step.final_algebra (Formalism.HermitianLatticesTheory.mass h L) c (lamG F h L) (normD h L)
    (Real.pi ^ finrank K V) ((finrank K V - 1).factorial : ℝ) (finrank K V : ℝ)
    (Formalism.HermitianLatticesTheory.vInv K ^ (Formalism.HermitianLatticesTheory.fDeg K * finrank K V))
    (Real.sqrt ((2 * Formalism.HermitianLatticesTheory.vInv K) ^ Formalism.HermitianLatticesTheory.fDeg K)) (lValEtaF K F (finrank K V))
    (Formalism.HermitianLatticesTheory.fDeg K) (Step.normD_pos hd hL hLi) (by positivity) (by positivity)
    (by exact_mod_cast hn0) (by positivity) (by positivity) hAB
  rw [massRatio_eq_lvalue hK hF (finrank K V) hm]
  exact key

end Formalism.HermitianLattices.Ext.L3
