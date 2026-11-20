import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients
import Formalism.RealPlaceAnalysis.FinalF
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.KTypesAboveOfDsClass
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ComplexOrder

noncomputable section

namespace GlobalTheory.ClassificationConsequences

open GlobalTheory.LowestKTypeDetermines

variable {n : ℕ} {ε : Fin n → Bool} {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {τ : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')}

/- English proof (translation)
Establish `ha' : aᴴ * Jm ε * a = Jm ε` using `ha`. Establish `hb' : bᴴ * Jm ε * b = Jm ε` using `hb`. Use `show (a * b)ᴴ * Jm ε * (a * b) = Jm ε`. Rewrite using `[Matrix.conjTranspose_mul]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem mul_mem_UJset {a b : Matrix (Fin n) (Fin n) ℂ} (ha : a ∈ UJset ε) (hb : b ∈ UJset ε) :
    a * b ∈ UJset ε := by
  have ha' : aᴴ * Jm ε * a = Jm ε := ha
  have hb' : bᴴ * Jm ε * b = Jm ε := hb
  show (a * b)ᴴ * Jm ε * (a * b) = Jm ε
  rw [Matrix.conjTranspose_mul]
  calc bᴴ * aᴴ * Jm ε * (a * b) = bᴴ * (aᴴ * Jm ε * a) * b := by simp only [Matrix.mul_assoc]
    _ = Jm ε := by rw [ha', hb']

/- English proof (translation)
Take `⟨T, hT⟩` from `he`. Take `⟨hc, hn, ⟨⟨h1, hmul⟩, hiso, hcont⟩, hirr, hsq⟩` from `h`. Establish `hσ : ∀ g ∈ UJset ε, ∀ v, σ g v = T.symm (τ g (T v))`. Introduce `g hg v`. Rewrite using `[← hT g hg v, LinearIsometryEquiv.symm_apply_apply]`.

Establish `one_mem : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ UJset ε` using `by show (1 : Matrix (Fin n) (Fin n) ℂ)ᴴ * Jm ε * 1 = Jm ε`. Simplify using the standard rewrite rules. Use `⟨?_, ?_, ⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_, ?_⟩` and prove the remaining obligations. Use `haveI := hc`. Conclude with `T.toIsometryEquiv.completeSpace`.

Use `haveI := hn`. Conclude with `T.toLinearEquiv.toEquiv.nontrivial`. Use extensionality with `v`. Rewrite using `[hσ 1 one_mem v, h1]`. Simplify using the standard rewrite rules.

Introduce `a ha b hb`. Use extensionality with `v`. Rewrite using `[hσ _ (mul_mem_UJset ha hb), hmul a ha b hb, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, hσ a ha, hσ b hb, LinearIsometryEquiv.apply_symm_apply]`. Introduce `g hg v`. Rewrite using `[hσ g hg v, LinearIsometryEquiv.norm_map, hiso g hg, LinearIsometryEquiv.norm_map]`.

Introduce `v`. Establish `hc' : ContinuousOn (fun g => T.symm (τ g (T v))) (UJset ε)` using `T.symm.continuous.comp_continuousOn (hcont (T v))`. Conclude with `hc'.congr (fun g hg => hσ g hg v)`. Introduce `S hS hst`. Set `S' : Submodule ℂ H'` to `S.comap (T.symm.toLinearEquiv : H' →ₗ[ℂ] H)`.

Establish `mem' : ∀ w, w ∈ S' ↔ T.symm w ∈ S` using `fun w => Iff.rfl`. Establish `hcl : IsClosed (S' : Set H')` using `hS.preimage T.symm.continuous`. Establish `hst' : ∀ g ∈ UJset ε, ∀ w ∈ S', τ g w ∈ S'`. Introduce `g hg w hw`. Rewrite `hw`, the goal using `[mem']`.

Rewrite using `[symm_inter T hT g hg w]`. Conclude with `hst g hg _ hw`. Break down `hirr S' hcl hst' with h0 | h0` into its components or cases. Use `left`. Rewrite using `[Submodule.eq_bot_iff]`.

Introduce `v hv`. Establish `hTv : T v ∈ S'`. Rewrite using `[mem', LinearIsometryEquiv.symm_apply_apply]`. Conclude with `hv`. Rewrite `hTv` using `[h0, Submodule.mem_bot]`.

Conclude with `(LinearIsometryEquiv.map_eq_zero_iff T).mp hTv`. Use `right`. Rewrite using `[Submodule.eq_top_iff']`. Introduce `v`. Establish `hTv : T v ∈ S'`.

Rewrite using `[h0]`. Conclude with `Submodule.mem_top`. Rewrite `hTv` using `[mem', LinearIsometryEquiv.symm_apply_apply]`. Conclude with `hTv`. Introduce `v w`.

Establish `heq : coefOn (ε` using `ε) σ v w = coefOn (ε := ε) τ (T v) (T w) := by`. Use function extensionality and compare the values at `g`. Establish `hg : umat g ∈ UJset ε` using `g.2`. Simplify using `only [coefOn]`. Rewrite using `[← hT _ hg v, LinearIsometryEquiv.inner_map_map]`.

Rewrite using `[heq]`. Conclude with `hsq (T v) (T w)`.
-/
theorem isSqIntIrr_of_uEquiv (he : UEquiv ε σ τ) (h : IsSqIntIrr ε τ) : IsSqIntIrr ε σ := by
  obtain ⟨T, hT⟩ := he
  obtain ⟨hc, hn, ⟨⟨h1, hmul⟩, hiso, hcont⟩, hirr, hsq⟩ := h

  have hσ : ∀ g ∈ UJset ε, ∀ v, σ g v = T.symm (τ g (T v)) := by
    intro g hg v
    rw [← hT g hg v, LinearIsometryEquiv.symm_apply_apply]
  have one_mem : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ UJset ε := by
    show (1 : Matrix (Fin n) (Fin n) ℂ)ᴴ * Jm ε * 1 = Jm ε
    simp
  refine ⟨?_, ?_, ⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_, ?_⟩
  · haveI := hc
    exact T.toIsometryEquiv.completeSpace
  · haveI := hn
    exact T.toLinearEquiv.toEquiv.nontrivial
  · ext v
    rw [hσ 1 one_mem v, h1]
    simp
  · intro a ha b hb
    ext v
    rw [hσ _ (mul_mem_UJset ha hb), hmul a ha b hb, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.comp_apply, hσ a ha, hσ b hb, LinearIsometryEquiv.apply_symm_apply]
  · intro g hg v
    rw [hσ g hg v, LinearIsometryEquiv.norm_map, hiso g hg, LinearIsometryEquiv.norm_map]
  · intro v
    have hc' : ContinuousOn (fun g => T.symm (τ g (T v))) (UJset ε) :=
      T.symm.continuous.comp_continuousOn (hcont (T v))
    exact hc'.congr (fun g hg => hσ g hg v)
  ·
    intro S hS hst
    let S' : Submodule ℂ H' := S.comap (T.symm.toLinearEquiv : H' →ₗ[ℂ] H)
    have mem' : ∀ w, w ∈ S' ↔ T.symm w ∈ S := fun w => Iff.rfl
    have hcl : IsClosed (S' : Set H') := hS.preimage T.symm.continuous
    have hst' : ∀ g ∈ UJset ε, ∀ w ∈ S', τ g w ∈ S' := by
      intro g hg w hw
      rw [mem'] at hw ⊢
      rw [symm_inter T hT g hg w]
      exact hst g hg _ hw
    rcases hirr S' hcl hst' with h0 | h0
    · left
      rw [Submodule.eq_bot_iff]
      intro v hv
      have hTv : T v ∈ S' := by
        rw [mem', LinearIsometryEquiv.symm_apply_apply]
        exact hv
      rw [h0, Submodule.mem_bot] at hTv
      exact (LinearIsometryEquiv.map_eq_zero_iff T).mp hTv
    · right
      rw [Submodule.eq_top_iff']
      intro v
      have hTv : T v ∈ S' := by
        rw [h0]
        exact Submodule.mem_top
      rw [mem', LinearIsometryEquiv.symm_apply_apply] at hTv
      exact hTv
  ·
    intro v w
    have heq : coefOn (ε := ε) σ v w = coefOn (ε := ε) τ (T v) (T w) := by
      funext g
      have hg : umat g ∈ UJset ε := g.2
      simp only [coefOn]
      rw [← hT _ hg v, LinearIsometryEquiv.inner_map_map]
    rw [heq]
    exact hsq (T v) (T w)

/- English proof (translation)
Take `⟨c1, c2, c3, c4, c5⟩` from `isSqIntIrr_of_uEquiv he ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1⟩`. Take `⟨T, hT⟩` from `he`. Use `⟨c1, c2, c3, c4, c5, ?_, ?_⟩` and prove the remaining obligations. Conclude with `exists_ktype_of_uEquiv (uEquiv_symm ⟨T, hT⟩) h.2.2.2.2.2.1`. Introduce `μ S hS`.

Conclude with `h.2.2.2.2.2.2 μ _ (ktype_transfer T hT hS)`.
-/
theorem isDS_of_uEquiv {lam : Fin n → ℝ} (he : UEquiv ε σ τ) (h : IsDS ε lam τ) : IsDS ε lam σ := by
  obtain ⟨c1, c2, c3, c4, c5⟩ :=
    isSqIntIrr_of_uEquiv he ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1⟩
  obtain ⟨T, hT⟩ := he
  refine ⟨c1, c2, c3, c4, c5, ?_, ?_⟩
  · exact exists_ktype_of_uEquiv (uEquiv_symm ⟨T, hT⟩) h.2.2.2.2.2.1
  · intro μ S hS
    exact h.2.2.2.2.2.2 μ _ (ktype_transfer T hT hS)

/- English proof (translation)
Take `⟨S, hfin, hvS, hst⟩` from `hv`. Use `⟨S.map (T.toLinearEquiv : H →ₗ[ℂ] H'), ?_, Submodule.mem_map_of_mem hvS, ?_⟩` and prove the remaining obligations. Use `haveI := hfin infer_instance`. Introduce `g hg w hw`. Take `⟨u, hu, hwu⟩` from `Submodule.mem_map.mp hw`.

Establish `hw' : w = T u` using `hwu.symm`. Substitute `hw'` using the available equality. Rewrite using `[← h g (Kset_sub hg) u]`. Conclude with `Submodule.mem_map_of_mem (hst g hg u hu)`.
-/
theorem isKFin_transfer (T : H ≃ₗᵢ[ℂ] H') (h : ∀ g ∈ UJset ε, ∀ v, T (σ g v) = τ g (T v)) {v : H}
    (hv : IsKFin ε σ v) : IsKFin ε τ (T v) := by
  obtain ⟨S, hfin, hvS, hst⟩ := hv
  refine ⟨S.map (T.toLinearEquiv : H →ₗ[ℂ] H'), ?_, Submodule.mem_map_of_mem hvS, ?_⟩
  · haveI := hfin
    infer_instance
  · intro g hg w hw
    obtain ⟨u, hu, hwu⟩ := Submodule.mem_map.mp hw
    have hw' : w = T u := hwu.symm
    subst hw'
    rw [← h g (Kset_sub hg) u]
    exact Submodule.mem_map_of_mem (hst g hg u hu)

/- English proof (translation)
Take `⟨hsm, heig⟩` from `hf`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `g₀ hg₀`. Take `⟨U, F, hU, hgU, hF, hfF⟩` from `hsm g₀ hg₀`. Conclude with `⟨U, F, hU, hgU, hF, fun g hgU' hg => (h g hg).trans (hfF g hgU' hg)⟩`.

Introduce `m g hg`. Establish `hgel : gelf ε m f g = gelf ε m f' g`. Simplify using `only [gelf]`. Conclude with `Finset.sum_congr rfl (fun a _ => Eword_congr ε h _ g hg)`. Rewrite using `[hgel, heig m g hg, h g hg]`.
-/
theorem isZEigen_congr {χ : Fin n → ℂ} {f f' : Matrix (Fin n) (Fin n) ℂ → ℂ}
    (h : ∀ g, inUJ ε g → f g = f' g) (hf : IsZEigen ε χ f') : IsZEigen ε χ f := by
  obtain ⟨hsm, heig⟩ := hf
  refine ⟨?_, ?_⟩
  · intro g₀ hg₀
    obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hsm g₀ hg₀
    exact ⟨U, F, hU, hgU, hF, fun g hgU' hg => (h g hg).trans (hfF g hgU' hg)⟩
  · intro m g hg

    have hgel : gelf ε m f g = gelf ε m f' g := by
      simp only [gelf]
      exact Finset.sum_congr rfl (fun a _ => Eword_congr ε h _ g hg)
    rw [hgel, heig m g hg, h g hg]

/- English proof (translation)
Take `⟨T, hT⟩` from `he`. Introduce `v w hv hw`. Establish `hz` using `h (T v) (T w) (isKFin_transfer T hT hv) (isKFin_transfer T hT hw)`. Use `isZEigen_congr (fun g hg => ?_) hz` and prove the remaining obligations. Use `show ⟪w, σ g v⟫_ℂ = ⟪T w, τ g (T v)⟫_ℂ`.

Rewrite using `[← hT g hg v, LinearIsometryEquiv.inner_map_map]`.
-/
theorem hasInfChar_of_uEquiv {χ : Fin n → ℂ} (he : UEquiv ε σ τ) (h : HasInfChar ε χ τ) :
    HasInfChar ε χ σ := by
  obtain ⟨T, hT⟩ := he
  intro v w hv hw
  have hz := h (T v) (T w) (isKFin_transfer T hT hv) (isKFin_transfer T hT hw)
  refine isZEigen_congr (fun g hg => ?_) hz
  show ⟪w, σ g v⟫_ℂ = ⟪T w, τ g (T v)⟫_ℂ
  rw [← hT g hg v, LinearIsometryEquiv.inner_map_map]

/- English proof (translation)
Introduce `n ε H _ _ σ hσ`. Take `⟨G, i1, i2, π, hπ, hcl⟩` from `h n`. Take `⟨s, mu, hmu, hs, he⟩` from `hcl ε H σ hσ`. Conclude with `⟨s, mu, hmu, hs, isDS_of_uEquiv he (isDS_of_isHCDS hmu (hπ (ε ∘ s) mu hmu))⟩`.
-/
theorem dsExhaust_of_dsClass (h : DSClass) : DSExhaust := by
  intro n ε H _ _ σ hσ
  obtain ⟨G, i1, i2, π, hπ, hcl⟩ := h n
  obtain ⟨s, mu, hmu, hs, he⟩ := hcl ε H σ hσ
  exact ⟨s, mu, hmu, hs, isDS_of_uEquiv he (isDS_of_isHCDS hmu (hπ (ε ∘ s) mu hmu))⟩

/- English proof (translation)
Introduce `n ε lam H _ _ σ hl hσ`. Take `⟨G, i1, i2, π, hπ, huniq⟩` from `exists_model h ε hl`. Conclude with `hasInfChar_of_uEquiv (huniq H σ hσ) hπ.2.1`.
-/
theorem dsInfChar_of_dsClass (h : DSClass) : DSInfChar := by
  intro n ε lam H _ _ σ hl hσ
  obtain ⟨G, i1, i2, π, hπ, huniq⟩ := exists_model h ε hl
  exact hasInfChar_of_uEquiv (huniq H σ hσ) hπ.2.1

/- English proof (translation)
Introduce `n ε lam hl H _ _ _ σ hσ`. Take `⟨S0, hS0⟩` from `hσ.2.2.2.2.2.1`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Establish `hset : {S : Submodule ℂ H | IsKTypeOf ε σ (lowK ε lam) S} = {S0}`. Use extensionality with `S`.

Simplify using `only [Set.mem_setOf_eq, Set.mem_singleton_iff]`. Prove the components needed by the constructor for the conclusion. Introduce `hS`. Conclude with `lowKMultOne_of_dsClass h n ε lam H σ hl hσ S S0 hS hS0`. Introduce and unpack `rfl`.

Conclude with `hS0`. Establish `hsub : lowKSub ε lam σ = S0` using `by show sSup {S : Submodule ℂ H | IsKTypeOf ε σ (lowK ε lam) S} = S0`. Rewrite using `[hset, sSup_singleton]`. Rewrite using `[hsub]`. Conclude with `hS0`.

Introduce `μ S hS hne`. Take `⟨c, hc, hμ⟩` from `kTypesAbove_of_dsClass h n ε lam H σ hl hσ μ S hS`. Establish `hQ0 : (∑ a, ∑ b, (c a b : ℝ) • root a b) ≠ 0`. Introduce `h0`. Apply `hne` to reduce the goal to its premises.

Rewrite using `[hμ, h0, add_zero]`. Establish `hx : Antitone (lam + Formalism.QuantumDeterminants.rhoStd n)` using `(strictAnti_add_rho hl.1).antitone`. Establish `hcone` using `nsq_add_cone hx hc`. Establish `hpos : 0 < nsq (∑ a, ∑ b, (c a b : ℝ) • root a b)`. Break down `(nsq_nonneg (∑ a, ∑ b, (c a b : ℝ) • root a b)).lt_or_eq with hp | hp` into its components or cases.

Conclude with `hp`. Conclude with `absurd (eq_zero_of_nsq hp.symm.le) hQ0`. Establish `e1 : vNormSq ε (lowK ε lam) = nsq (lam + Formalism.QuantumDeterminants.rhoStd n)` using `by show nsq (lowK ε lam + (2 : ℝ) • rhoC ε) = _`. Rewrite using `[lowK_add]`. Establish `e2 : vNormSq ε μ = nsq (lam + Formalism.QuantumDeterminants.rhoStd n + ∑ a, ∑ b, (c a b : ℝ) • root a b)` using `by show nsq (μ + (2 : ℝ) • rhoC ε) = _`.

Rewrite using `[hμ, add_right_comm (lowK ε lam) _ ((2 : ℝ) • rhoC ε), lowK_add]`. Rewrite using `[e1, e2]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem strictLow_of_dsClass (h : DSClass) : StrictLow := by
  intro n ε lam hl H _ _ _ σ hσ
  obtain ⟨S0, hS0⟩ := hσ.2.2.2.2.2.1
  refine ⟨?_, ?_⟩
  ·
    have hset : {S : Submodule ℂ H | IsKTypeOf ε σ (lowK ε lam) S} = {S0} := by
      ext S
      simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
      constructor
      · intro hS
        exact lowKMultOne_of_dsClass h n ε lam H σ hl hσ S S0 hS hS0
      · rintro rfl
        exact hS0
    have hsub : lowKSub ε lam σ = S0 := by
      show sSup {S : Submodule ℂ H | IsKTypeOf ε σ (lowK ε lam) S} = S0
      rw [hset, sSup_singleton]
    rw [hsub]
    exact hS0
  ·
    intro μ S hS hne
    obtain ⟨c, hc, hμ⟩ := kTypesAbove_of_dsClass h n ε lam H σ hl hσ μ S hS
    have hQ0 : (∑ a, ∑ b, (c a b : ℝ) • root a b) ≠ 0 := by
      intro h0
      apply hne
      rw [hμ, h0, add_zero]
    have hx : Antitone (lam + Formalism.QuantumDeterminants.rhoStd n) := (strictAnti_add_rho hl.1).antitone
    have hcone := nsq_add_cone hx hc
    have hpos : 0 < nsq (∑ a, ∑ b, (c a b : ℝ) • root a b) := by
      rcases (nsq_nonneg (∑ a, ∑ b, (c a b : ℝ) • root a b)).lt_or_eq with hp | hp
      · exact hp
      · exact absurd (eq_zero_of_nsq hp.symm.le) hQ0
    have e1 : vNormSq ε (lowK ε lam) = nsq (lam + Formalism.QuantumDeterminants.rhoStd n) := by
      show nsq (lowK ε lam + (2 : ℝ) • rhoC ε) = _
      rw [lowK_add]
    have e2 : vNormSq ε μ = nsq (lam + Formalism.QuantumDeterminants.rhoStd n + ∑ a, ∑ b, (c a b : ℝ) • root a b) := by
      show nsq (μ + (2 : ℝ) • rhoC ε) = _
      rw [hμ, add_right_comm (lowK ε lam) _ ((2 : ℝ) • rhoC ε), lowK_add]
    rw [e1, e2]
    linarith

/- English proof (translation)
Introduce `h`. Conclude with `⟨dsExists_of_dsClass h, dsExhaust_of_dsClass h, dsUnique_of_dsClass h, dsInfChar_of_dsClass h, lowKMultOne_of_dsClass h, kTypesAbove_of_dsClass h, strictLow_of_dsClass h⟩`.
-/
theorem consequences_of_dsClass :
    DSClass → DSExists ∧ DSExhaust ∧ DSUnique ∧ DSInfChar ∧ LowKMultOne ∧ KTypesAbove ∧ StrictLow := by
  intro h
  exact ⟨dsExists_of_dsClass h, dsExhaust_of_dsClass h, dsUnique_of_dsClass h, dsInfChar_of_dsClass h,
    lowKMultOne_of_dsClass h, kTypesAbove_of_dsClass h, strictLow_of_dsClass h⟩

end GlobalTheory.ClassificationConsequences
