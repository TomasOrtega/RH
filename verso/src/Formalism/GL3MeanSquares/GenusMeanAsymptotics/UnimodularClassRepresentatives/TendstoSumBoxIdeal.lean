import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.NkCountLocF
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.TendstoMeanAlphaN
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.BoxInterEqEmpty
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.TendstoSumOfMean

open NumberField Module Filter Topology

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

/- English proof (translation)
Take `⟨C, hC⟩` from `nkCount_le hK hF hs hd hL hLi hm h𝔭`. Establish `hq : (0 : ℝ) < (Ideal.absNorm 𝔭 : ℝ)` using `zero_lt_one.trans (BoxSum.one_lt_absNorm h𝔭)`. Use `⟨max C |alphaN h L 𝔭 0|, fun n => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hn : n = 0`. Rewrite using `[hn]`.

Conclude with `le_max_right _ _`. Use `le_trans ?_ (le_max_left _ _)` and prove the remaining obligations. Use `set u : ℕ → ℝ := fun k => (nkCount h L 𝔭 k n : ℝ) / (Ideal.absNorm 𝔭 : ℝ) ^ (k * (2 * finrank K V - 1)) with hu`. Use `set k₀ := 2 * vd h L 𝔭 + 2 * vF 𝔭 n + 2 with hk₀`. Establish `hstep : ∀ k, k₀ ≤ k → u k = u k₀`.

Introduce `k hk`. Proceed by induction on `k, hk using Nat.le_induction with`. Consider the case `base => rfl`. Consider the case `succ k hk ih`. Rewrite using `[← ih]`.

Simplify using `only [hu]`. Rewrite using `[nkCount_succ hK hF hs hd hL hLi h𝔭 hn hk, add_mul, one_mul, pow_add]`. Use `push_cast`. Clear the denominators using the available nonvanishing facts. Establish `hlim : Tendsto u atTop (𝓝 (u k₀))` using `tendsto_atTop_of_eventually_const (i₀ := k₀) fun k hk => hstep k hk`.

Establish `hα : alphaN h L 𝔭 n = u k₀` using `hlim.limUnder_eq`. Rewrite using `[hα, abs_of_nonneg (by simp only [hu]; positivity)]`. Simplify using `only [hu]`. Rewrite using `[div_le_iff₀ (by positivity)]`. Conclude with `hC _ _`.
-/
theorem exists_abs_alphaN_le (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) (hm : 2 ≤ finrank K V)
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) : ∃ C : ℝ, ∀ n : 𝓞 F, |alphaN h L 𝔭 n| ≤ C := by
  obtain ⟨C, hC⟩ := nkCount_le hK hF hs hd hL hLi hm h𝔭
  have hq : (0 : ℝ) < (Ideal.absNorm 𝔭 : ℝ) := zero_lt_one.trans (BoxSum.one_lt_absNorm h𝔭)
  refine ⟨max C |alphaN h L 𝔭 0|, fun n => ?_⟩
  by_cases hn : n = 0
  · rw [hn]; exact le_max_right _ _
  refine le_trans ?_ (le_max_left _ _)
  set u : ℕ → ℝ := fun k => (nkCount h L 𝔭 k n : ℝ) /
    (Ideal.absNorm 𝔭 : ℝ) ^ (k * (2 * finrank K V - 1)) with hu
  set k₀ := 2 * vd h L 𝔭 + 2 * vF 𝔭 n + 2 with hk₀
  have hstep : ∀ k, k₀ ≤ k → u k = u k₀ := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => rfl
    | succ k hk ih =>
      rw [← ih]
      simp only [hu]
      rw [nkCount_succ hK hF hs hd hL hLi h𝔭 hn hk, add_mul, one_mul, pow_add]
      push_cast
      field_simp
  have hlim : Tendsto u atTop (𝓝 (u k₀)) :=
    tendsto_atTop_of_eventually_const (i₀ := k₀) fun k hk => hstep k hk
  have hα : alphaN h L 𝔭 n = u k₀ := hlim.limUnder_eq
  rw [hα, abs_of_nonneg (by simp only [hu]; positivity)]
  simp only [hu]
  rw [div_le_iff₀ (by positivity)]
  exact hC _ _

/- English proof (translation)
Use `choose C hC using fun 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} => exists_abs_alphaN_le hK hF hs hd hL hLi hm 𝔭.2`. Establish `key` using `BoxSum.tendsto_sum_of_mean hK hF (m := finrank K V) (by omega) S (fun 𝔭 n => alphaN h L 𝔭.1 n) C (fun 𝔭 => 2 * vd h L 𝔭.1 + 2) (fun 𝔭 _ n => hC 𝔭 n) (fun 𝔭 _ n n' k hn hk hc => alphaN_congr hK hF hs hd hL hLi 𝔭.2 hn (by omega) hc) (fun 𝔭 _ => tendsto_mean_alphaN hK hF hs hd hL hL …`. Use `(key.mul_const (∏ 𝔭 ∈ S, (1 - etaF K F 𝔭.1 ^ finrank K V * (Ideal.absNorm 𝔭.1 : ℝ) ^ (-(finrank K V : ℤ)))⁻¹)).congr fun j => ?_` and prove the remaining obligations. Rewrite using `[mul_assoc, finsum_mem_mul]`. Use `congr 1`.

Use `finsum_mem_congr rfl fun n _ => ?_` and prove the remaining obligations. Simplify using `only [div_eq_mul_inv]`. Rewrite using `[Finset.prod_mul_distrib, mul_assoc]`.
-/
theorem tendsto_sum_box_ideal (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) (hm : 2 ≤ finrank K V) (S : Finset {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal})
    (hS : ∀ 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, vd h L 𝔭.1 ≠ 0 → 𝔭 ∈ S) {b : Ideal (𝓞 F)} (hb : b ≠ ⊥)
    (hbS : ∀ 𝔭 ∈ S, b ⊔ 𝔭.1 = ⊤) :
    Tendsto (fun j : ℕ => ((j : ℝ) ^ 2) ^ (-((Formalism.HermitianLatticesTheory.fDeg K * finrank K V : ℕ) : ℤ)) *
        ∑ᶠ n ∈ {n : 𝓞 F | n ∈ boxSet K F ((j : ℝ) ^ 2) ∧ n ∈ b},
          (Ideal.absNorm (Ideal.span {n}) : ℝ) ^ (finrank K V - 1) *
            ∏ 𝔭 ∈ S, alphaN h L 𝔭.1 n / (1 - etaF K F 𝔭.1 ^ finrank K V *
              (Ideal.absNorm 𝔭.1 : ℝ) ^ (-(finrank K V : ℤ))))
      atTop (𝓝 ((finrank K V : ℝ) ^ (-(Formalism.HermitianLatticesTheory.fDeg K : ℤ)) /
        Real.sqrt ((2 * Formalism.HermitianLatticesTheory.vInv K) ^ Formalism.HermitianLatticesTheory.fDeg K) / (Ideal.absNorm b : ℝ) *
          ∏ 𝔭 ∈ S, (1 - etaF K F 𝔭.1 ^ finrank K V *
            (Ideal.absNorm 𝔭.1 : ℝ) ^ (-(finrank K V : ℤ)))⁻¹)) := by
  choose C hC using fun 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} =>
    exists_abs_alphaN_le hK hF hs hd hL hLi hm 𝔭.2
  have key := BoxSum.tendsto_sum_of_mean hK hF (m := finrank K V) (by omega) S
    (fun 𝔭 n => alphaN h L 𝔭.1 n) C (fun 𝔭 => 2 * vd h L 𝔭.1 + 2) (fun 𝔭 _ n => hC 𝔭 n)
    (fun 𝔭 _ n n' k hn hk hc => alphaN_congr hK hF hs hd hL hLi 𝔭.2 hn (by omega) hc)
    (fun 𝔭 _ => tendsto_mean_alphaN hK hF hs hd hL hLi hm 𝔭.2) hb hbS
  refine (key.mul_const (∏ 𝔭 ∈ S, (1 - etaF K F 𝔭.1 ^ finrank K V *
            (Ideal.absNorm 𝔭.1 : ℝ) ^ (-(finrank K V : ℤ)))⁻¹)).congr fun j => ?_
  rw [mul_assoc, finsum_mem_mul]
  congr 1
  refine finsum_mem_congr rfl fun n _ => ?_
  simp only [div_eq_mul_inv]
  rw [Finset.prod_mul_distrib, mul_assoc]

end Formalism.HermitianLattices.Ext.L3
