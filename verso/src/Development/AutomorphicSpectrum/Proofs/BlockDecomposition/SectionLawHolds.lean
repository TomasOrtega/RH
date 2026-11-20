import Mathlib
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.StripEntire
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Iwa

noncomputable section

open PositivityTheory.RgEis

namespace GlobalTheory.CompanionTheory.RgEisSec

variable {G : Type} [Group G] [TopologicalSpace G]
  {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.DYhc7.main hK hP hI`.
-/
theorem isQuotientMap_mul [IsTopologicalGroup G] {K P : Subgroup G} (hK : IsCompact (K : Set G))
    (hP : IsClosed (P : Set G)) (hI : Iwa P K) :
    Topology.IsQuotientMap (fun x : P × K => (x.1 : G) * (x.2 : G)) :=
  _root_.UpperTheory.Reformulated.B.DYhc7.main hK hP hI

/- English proof (translation)
Establish `h : ∃ k' : K, (p * (k : G)) * (k' : G)⁻¹ ∈ P` using `⟨k, by simpa using hp⟩`. Rewrite using `[sec, dif_pos h]`. Take `⟨k0, hk0⟩ : ∃ k0 : K, k0 = h.choose` from `⟨_, rfl⟩`. Establish `h0 : p * (k : G) * (k0 : G)⁻¹ ∈ P` using `hk0 ▸ h.choose_spec`. Rewrite using `[← hk0]`.

Establish `hr : ((k0 * k⁻¹ : K) : G) ∈ P`. Establish `: ((k0 * k⁻¹ : K) : G) = (p * (k : G) * (k0 : G)⁻¹)⁻¹ * p` using `by simp [mul_assoc]`. Rewrite using `[this]`. Conclude with `P.mul_mem (P.inv_mem h0) hp`. Establish `hrw : c ((k0 * k⁻¹ : K) : G) • ρ (k0 * k⁻¹) w = w` using `hw _ hr`.

Establish `hcp : c p = c (p * (k : G) * (k0 : G)⁻¹) * c ((k0 * k⁻¹ : K) : G)`. Rewrite using `[← hch.mul _ h0 _ hr]`. Use `congr 1`. Simplify using `[mul_assoc]`. Establish `hρ : ρ k⁻¹ = ρ k0⁻¹ * ρ (k0 * k⁻¹)`.

Rewrite using `[← map_mul]`. Use `congr 1`. Simplify using the standard rewrite rules. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hrw]`.

Both sides reduce to the same expression. Use `_ = c p • ρ k⁻¹ w := by`. Rewrite using `[hcp, hρ, map_smul, mul_smul]`. Both sides reduce to the same expression.
-/
theorem sec_mul {Γ K P : Subgroup G} {c : G → ℂ} {ρ : K →* (W →L[ℂ] W)} (hch : IsCh Γ P c)
    {w : W} (hw : w ∈ secSp K P c ρ) {p : G} (hp : p ∈ P) (k : K) :
    sec K P c ρ (p * k) w = c p • ρ k⁻¹ w := by
  have h : ∃ k' : K, (p * (k : G)) * (k' : G)⁻¹ ∈ P := ⟨k, by simpa using hp⟩
  rw [sec, dif_pos h]
  obtain ⟨k0, hk0⟩ : ∃ k0 : K, k0 = h.choose := ⟨_, rfl⟩
  have h0 : p * (k : G) * (k0 : G)⁻¹ ∈ P := hk0 ▸ h.choose_spec
  rw [← hk0]
  have hr : ((k0 * k⁻¹ : K) : G) ∈ P := by
    have : ((k0 * k⁻¹ : K) : G) = (p * (k : G) * (k0 : G)⁻¹)⁻¹ * p := by simp [mul_assoc]
    rw [this]
    exact P.mul_mem (P.inv_mem h0) hp
  have hrw : c ((k0 * k⁻¹ : K) : G) • ρ (k0 * k⁻¹) w = w := hw _ hr
  have hcp : c p = c (p * (k : G) * (k0 : G)⁻¹) * c ((k0 * k⁻¹ : K) : G) := by
    rw [← hch.mul _ h0 _ hr]
    congr 1
    simp [mul_assoc]
  have hρ : ρ k⁻¹ = ρ k0⁻¹ * ρ (k0 * k⁻¹) := by
    rw [← map_mul]
    congr 1
    simp
  calc (c (p * (k : G) * (k0 : G)⁻¹) • ρ k0⁻¹) w
      = c (p * (k : G) * (k0 : G)⁻¹) • ρ k0⁻¹ (c ((k0 * k⁻¹ : K) : G) • ρ (k0 * k⁻¹) w) := by
        rw [hrw]; rfl
    _ = c p • ρ k⁻¹ w := by
        rw [hcp, hρ, map_smul, mul_smul]; rfl

/- English proof (translation)
Use `(isQuotientMap_mul hK hpar.closed hpar.iwa).continuous_iff.mpr ?_` and prove the remaining obligations. Establish `hc : Continuous fun p : P => c p` using `continuousOn_iff_continuous_restrict.mp hpar.ch.cont`. Establish `he : ((fun g => sec K P c ρ g w) ∘ fun x : P × K => (x.1 : G) * (x.2 : G)) = fun x : P × K => c x.1 • ρ x.2⁻¹ w`. Use function extensionality and compare the values at `x`. Conclude with `sec_mul hpar.ch hw x.1.2 x.2`.

Rewrite using `[he]`. Establish `h2 : Continuous fun k : K => ρ k⁻¹ w` using `(hρ.comp continuous_inv).clm_apply continuous_const`. Conclude with `(hc.comp continuous_fst).smul (h2.comp continuous_snd)`.
-/
theorem sec_continuous [IsTopologicalGroup G] {Γ K P : Subgroup G} {c : G → ℂ}
    {ρ : K →* (W →L[ℂ] W)} (hK : IsCompact (K : Set G)) (hρ : Continuous ρ) (hpar : IsPar Γ K P c)
    {w : W} (hw : w ∈ secSp K P c ρ) : Continuous fun g => sec K P c ρ g w := by
  refine (isQuotientMap_mul hK hpar.closed hpar.iwa).continuous_iff.mpr ?_
  have hc : Continuous fun p : P => c p := continuousOn_iff_continuous_restrict.mp hpar.ch.cont
  have he : ((fun g => sec K P c ρ g w) ∘ fun x : P × K => (x.1 : G) * (x.2 : G))
      = fun x : P × K => c x.1 • ρ x.2⁻¹ w := by
    funext x
    exact sec_mul hpar.ch hw x.1.2 x.2
  rw [he]
  have h2 : Continuous fun k : K => ρ k⁻¹ w :=
    (hρ.comp continuous_inv).clm_apply continuous_const
  exact (hc.comp continuous_fst).smul (h2.comp continuous_snd)

/- English proof (translation)
Use `haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK`. Take `⟨M, hM⟩` from `(isCompact_range hρ).isBounded.exists_norm_le`. Use `⟨M, fun g w => ?_⟩` and prove the remaining obligations. Take `⟨p, hp, k, hk, rfl⟩` from `hpar.iwa g`. Establish `h : ∃ k' : K, (p * k) * (k' : G)⁻¹ ∈ P` using `⟨⟨k, hk⟩, by simpa using hp⟩`.

Rewrite using `[sec, dif_pos h, ContinuousLinearMap.smul_apply, norm_smul, hpar.ch.norm _ h.choose_spec, one_mul]`. Conclude with `((ρ _).le_opNorm w).trans (mul_le_mul_of_nonneg_right (hM _ ⟨_, rfl⟩) (norm_nonneg _))`.
-/
theorem sec_bound {Γ K P : Subgroup G} {c : G → ℂ} {ρ : K →* (W →L[ℂ] W)}
    (hK : IsCompact (K : Set G)) (hρ : Continuous ρ) (hpar : IsPar Γ K P c) :
    ∃ M : ℝ, ∀ g (w : W), ‖sec K P c ρ g w‖ ≤ M * ‖w‖ := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  obtain ⟨M, hM⟩ := (isCompact_range hρ).isBounded.exists_norm_le
  refine ⟨M, fun g w => ?_⟩
  obtain ⟨p, hp, k, hk, rfl⟩ := hpar.iwa g
  have h : ∃ k' : K, (p * k) * (k' : G)⁻¹ ∈ P := ⟨⟨k, hk⟩, by simpa using hp⟩
  rw [sec, dif_pos h, ContinuousLinearMap.smul_apply, norm_smul, hpar.ch.norm _ h.choose_spec,
    one_mul]
  exact ((ρ _).le_opNorm w).trans (mul_le_mul_of_nonneg_right (hM _ ⟨_, rfl⟩) (norm_nonneg _))

/- English proof (translation)
Introduce `G _ _ _ _ _ W _ _ _ K ρ hK hρ Γ P c hpar`. Conclude with `⟨fun w hw p hp k => sec_mul hpar.ch hw hp k, fun w hw => sec_continuous hK hρ hpar hw, sec_bound hK hρ hpar⟩`.
-/
theorem secLaw : SecLaw := by
  intro G _ _ _ _ _ W _ _ _ K ρ hK hρ Γ P c hpar
  exact ⟨fun w hw p hp k => sec_mul hpar.ch hw hp k,
    fun w hw => sec_continuous hK hρ hpar hw, sec_bound hK hρ hpar⟩

end GlobalTheory.CompanionTheory.RgEisSec
