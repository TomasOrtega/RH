import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.NuGmapLocF

open NumberField Module Filter

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

namespace LIOrb

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
variable {V' : Type} [AddCommGroup V'] [Module K V'] [FiniteDimensional K V'] [Module (𝓞 K) V']
  [IsScalarTower (𝓞 K) K V']
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}

/- English proof (translation)
Unfold `lamP nu`. Rewrite using `[inv_div, mul_div_assoc]`.
-/
theorem eigenvalue_eq₂ (T : Submodule (𝓞 K) V') (𝔭 : Ideal (𝓞 F)) :
    lamP h' T 𝔭 = alphaStd K 𝔭 (finrank K V') * (nu h' T 𝔭)⁻¹ := by
  unfold lamP nu
  rw [inv_div, mul_div_assoc]

/- English proof (translation)
Establish `hq : (0 : ℝ) < (Ideal.absNorm 𝔭 : ℝ)`. Conclude with `reductionMapsOfForms.absNorm_pos h𝔭` after adjusting the coercions. Establish `hα` using `alphaL_pos hK hF hs hd hL hLi h𝔭`. Unfold `repRatio`. Rewrite using `[alphaN_eq_of_le hK hF hs hd hL hLi h𝔭 hn hk, e]`.

Unfold `nu`. Establish `e2 : (Ideal.absNorm 𝔭 : ℝ) ^ (finrank K V * vd h L 𝔭) = (Ideal.absNorm 𝔭 : ℝ) ^ ((finrank K V - 1) * vd h L 𝔭) * (Ideal.absNorm 𝔭 : ℝ) ^ vd h L 𝔭`. Rewrite using `[← pow_add, ← S.finrank_add_one, Nat.add_sub_cancel, Nat.succ_mul]`. Rewrite using `[e2]`. Establish `h1` using `pow_pos hq ((finrank K V - 1) * vd h L 𝔭)`.

Establish `h2` using `pow_pos hq (vd h L 𝔭)`. Establish `h3` using `pow_pos hq (k * (2 * finrank K V - 1))`. Clear the denominators using the available nonvanishing facts.
-/
theorem repRatio_eq (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (hs : h.IsSymm) (hd : IsTotPosDef h)
    (S : VecSplit h h') {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {n : 𝓞 F} (hn : n ≠ 0) {k : ℕ}
    (hk : 2 * vd h L 𝔭 + 2 * vF 𝔭 n + 2 ≤ k) {κ σ : ℝ}
    (e : (nkCount h L 𝔭 k n : ℝ) = κ * ((Ideal.absNorm 𝔭 : ℝ) ^ vd h L 𝔭 * nu h L 𝔭) * σ) :
    repRatio h L 𝔭 n = κ / (Ideal.absNorm 𝔭 : ℝ) ^ (k * (2 * finrank K V - 1)) * σ := by
  have hq : (0 : ℝ) < (Ideal.absNorm 𝔭 : ℝ) := by
    exact_mod_cast reductionMapsOfForms.absNorm_pos h𝔭
  have hα := alphaL_pos hK hF hs hd hL hLi h𝔭
  unfold repRatio
  rw [alphaN_eq_of_le hK hF hs hd hL hLi h𝔭 hn hk, e]
  unfold nu
  have e2 : (Ideal.absNorm 𝔭 : ℝ) ^ (finrank K V * vd h L 𝔭) =
      (Ideal.absNorm 𝔭 : ℝ) ^ ((finrank K V - 1) * vd h L 𝔭) * (Ideal.absNorm 𝔭 : ℝ) ^ vd h L 𝔭 := by
    rw [← pow_add, ← S.finrank_add_one, Nat.add_sub_cancel, Nat.succ_mul]
  rw [e2]
  have h1 := pow_pos hq ((finrank K V - 1) * vd h L 𝔭)
  have h2 := pow_pos hq (vd h L 𝔭)
  have h3 := pow_pos hq (k * (2 * finrank K V - 1))
  field_simp

/- English proof (translation)
Take `⟨s, hsr⟩` from `exists_locReps hK hF hs hd S hL hLi h𝔭`. Take `⟨R, hR⟩` from `exists_mReps hK hF hs hd S hL hLi h𝔭 hn hx hsr`. Establish `hR0 : R = ∅`. Rewrite using `[Finset.eq_empty_iff_forall_notMem]`. Introduce `M hM`.

Take `⟨⟨⟨g, hg, rfl⟩, hxM⟩, -⟩` from `hR.1 M hM`. Rewrite `hxM` using `[LocalizedFibreSets.gmap_locF]`. Conclude with `hE ⟨_, LocalizedFibreSets.isLattice_gmap g hL, UnimodularLocalization.isIntegralLat_gmap hg hLi, hxM⟩`. Take `⟨J, hJ⟩` from `(nkCount_eq_sum hK hF hs hd S hL hLi h𝔭 hn hx hR).exists`. Take `⟨k, hk1, hk2⟩` from `(hJ.and (eventually_ge_atTop (2 * vd h L 𝔭 + 2 * vF 𝔭 n + 2))).exists`.

Rewrite `hk1` using `[hR0, Finset.sum_empty]`. Rewrite using `[repRatio_eq hK hF hs hd S hL hLi h𝔭 hn hk2 (κ := 0) (σ := 0) (by rw [hk1]; simp)]`. Simplify using the standard rewrite rules.
-/
theorem repRatio_eq_zero (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (hs : h.IsSymm) (hd : IsTotPosDef h)
    (S : VecSplit h h') {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {n : 𝓞 F} (hn : n ≠ 0) (hx : h S.x₀ S.x₀ = algebraMap F K (n : F))
    (hE : ¬ ∃ M₂ : Submodule (𝓞 K) V, Submodule.IsLattice K M₂ ∧ Formalism.HermitianLatticesTheory.IsIntegralLat h M₂ ∧
      S.x₀ ∈ locF 𝔭 M₂) : repRatio h L 𝔭 n = 0 := by
  obtain ⟨s, hsr⟩ := exists_locReps hK hF hs hd S hL hLi h𝔭
  obtain ⟨R, hR⟩ := exists_mReps hK hF hs hd S hL hLi h𝔭 hn hx hsr
  have hR0 : R = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro M hM
    obtain ⟨⟨⟨g, hg, rfl⟩, hxM⟩, -⟩ := hR.1 M hM
    rw [LocalizedFibreSets.gmap_locF] at hxM
    exact hE ⟨_, LocalizedFibreSets.isLattice_gmap g hL, UnimodularLocalization.isIntegralLat_gmap hg hLi, hxM⟩
  obtain ⟨J, hJ⟩ := (nkCount_eq_sum hK hF hs hd S hL hLi h𝔭 hn hx hR).exists
  obtain ⟨k, hk1, hk2⟩ := (hJ.and (eventually_ge_atTop (2 * vd h L 𝔭 + 2 * vF 𝔭 n + 2))).exists
  rw [hR0, Finset.sum_empty] at hk1
  rw [repRatio_eq hK hF hs hd S hL hLi h𝔭 hn hk2 (κ := 0) (σ := 0) (by rw [hk1]; simp)]
  simp

end LIOrb

open LIOrb in
/- English proof (translation)
Introduce `K F _ _ _ _ _ _ hK hF V V' _ _ _ _ _ _ _ _ _ _ h h' S L L₀ 𝔭 n hs hd h𝔭 hn hx hL hLi hL₀ hL₀i`. Distinguish the cases in `hE : ∃ M₂ : Submodule (𝓞 K) V, Submodule.IsLattice K M₂ ∧ Formalism.HermitianLatticesTheory.IsIntegralLat h M₂ ∧ S.x₀ ∈ locF 𝔭 M₂`. Take `⟨M₂, hM₂, hM₂i, hx₂⟩` from `hE`. Take `⟨s, hsr⟩` from `exists_locReps hK hF hs hd S hL hLi h𝔭`. Take `⟨s₀, hsr₀⟩` from `exists_locReps hK hF hs hd S hL₀ hL₀i h𝔭`.

Take `⟨J, hJ, hJ₀⟩` from `((main_term hK hF hs hd S hL hLi hM₂ hM₂i h𝔭 hn hx hx₂ hsr).and (main_term hK hF hs hd S hL₀ hL₀i hM₂ hM₂i h𝔭 hn hx hx₂ hsr₀)).exists`. Take `⟨k, ⟨hk, hk₀⟩, hk1, hk2⟩` from `((hJ.and hJ₀).and ((eventually_ge_atTop (2 * vd h L 𝔭 + 2 * vF 𝔭 n + 2)).and (eventually_ge_atTop (2 * vd h L₀ 𝔭 + 2 * vF 𝔭 n + 2)))).exists`. Rewrite using `[psiP_eq_sum hK hF hs hd S hL hLi h𝔭 hsr, psiP_eq_sum hK hF hs hd S hL₀ hL₀i h𝔭 hsr₀, repRatio_eq hK hF hs hd S hL hLi h𝔭 hn hk1 hk, repRatio_eq hK hF hs hd S hL₀ hL₀i h𝔭 hn hk2 hk₀]`. Simplify using `only [eigenvalue_eq₂, mul_left_comm _ (alphaStd K 𝔭 (finrank K V')), ← Finset.mul_sum]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[repRatio_eq_zero hK hF hs hd S hL hLi h𝔭 hn hx hE, repRatio_eq_zero hK hF hs hd S hL₀ hL₀i h𝔭 hn hx hE, mul_zero, mul_zero]`.
-/
theorem liRatio : LIRatio := by
  intro K F _ _ _ _ _ _ hK hF V V' _ _ _ _ _ _ _ _ _ _ h h' S L L₀ 𝔭 n hs hd h𝔭 hn hx hL hLi hL₀ hL₀i
  by_cases hE : ∃ M₂ : Submodule (𝓞 K) V, Submodule.IsLattice K M₂ ∧
      Formalism.HermitianLatticesTheory.IsIntegralLat h M₂ ∧ S.x₀ ∈ locF 𝔭 M₂
  · obtain ⟨M₂, hM₂, hM₂i, hx₂⟩ := hE
    obtain ⟨s, hsr⟩ := exists_locReps hK hF hs hd S hL hLi h𝔭
    obtain ⟨s₀, hsr₀⟩ := exists_locReps hK hF hs hd S hL₀ hL₀i h𝔭
    obtain ⟨J, hJ, hJ₀⟩ := ((main_term hK hF hs hd S hL hLi hM₂ hM₂i h𝔭 hn hx hx₂ hsr).and
      (main_term hK hF hs hd S hL₀ hL₀i hM₂ hM₂i h𝔭 hn hx hx₂ hsr₀)).exists
    obtain ⟨k, ⟨hk, hk₀⟩, hk1, hk2⟩ := ((hJ.and hJ₀).and
      ((eventually_ge_atTop (2 * vd h L 𝔭 + 2 * vF 𝔭 n + 2)).and
        (eventually_ge_atTop (2 * vd h L₀ 𝔭 + 2 * vF 𝔭 n + 2)))).exists
    rw [psiP_eq_sum hK hF hs hd S hL hLi h𝔭 hsr, psiP_eq_sum hK hF hs hd S hL₀ hL₀i h𝔭 hsr₀,
      repRatio_eq hK hF hs hd S hL hLi h𝔭 hn hk1 hk, repRatio_eq hK hF hs hd S hL₀ hL₀i h𝔭 hn hk2 hk₀]
    simp only [eigenvalue_eq₂, mul_left_comm _ (alphaStd K 𝔭 (finrank K V')), ← Finset.mul_sum]
    ring
  · rw [repRatio_eq_zero hK hF hs hd S hL hLi h𝔭 hn hx hE,
      repRatio_eq_zero hK hF hs hd S hL₀ hL₀i h𝔭 hn hx hE, mul_zero, mul_zero]

end Formalism.HermitianLattices.Ext.L3
