import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReindexDblIncM
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LagrInt
import GroundTheory.GlobalFields.Adele.Discrete
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FiniteAdeleVectorAnnihilatorsCompactOpenBasis
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegrableOfRapidDecay
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalProjectionSectionIsotropicSpanStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonnegAdelicSchwartzBumpTestStatement
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

noncomputable section

namespace GlobalTheory.ThetaPosIso

/- English proof (translation)
Establish `hd` using `GroundTheory.Global.discreteTopology_principalSubgroup F`. Establish `ho : IsOpen ({0} : Set (AdeleRing.principalSubgroup (𝓞 F) F))` using `isOpen_discrete _`. Take `⟨t, ht, hpre⟩` from `isOpen_induced_iff.mp ho`. Use `⟨Set.pi Set.univ fun _ => t, set_pi_mem_nhds Set.finite_univ fun _ _ => ht.mem_nhds ?_, ?_⟩` and prove the remaining obligations. Establish `h0 : ((0 : AdeleRing.principalSubgroup (𝓞 F) F) : AF F) ∈ t`.

Establish `: (0 : AdeleRing.principalSubgroup (𝓞 F) F) ∈ Subtype.val ⁻¹' t` using `by rw [hpre]; rfl`. Conclude with `this`. Simplify using `using h0`. Introduce `ξ hξ`. Use function extensionality and compare the values at `i`.

Establish `hm : algebraMap F (AF F) (ξ i) ∈ AdeleRing.principalSubgroup (𝓞 F) F` using `⟨ξ i, rfl⟩`. Establish `: (⟨_, hm⟩ : AdeleRing.principalSubgroup (𝓞 F) F) ∈ Subtype.val ⁻¹' t` using `hξ i (Set.mem_univ _)`. Rewrite `this` using `[hpre]`. Establish `h2 : algebraMap F (AF F) (ξ i) = 0` using `congrArg Subtype.val this`. Conclude with `(NumberField.AdeleRing.algebraMap_injective (𝓞 F) F) (h2.trans (map_zero _).symm)`.
-/
theorem disc (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] :
    ∃ D ∈ nhds (0 : κ → AF F), ∀ ξ : κ → F, (fun i => algebraMap F (AF F) (ξ i)) ∈ D → ξ = 0 := by
  have hd := GroundTheory.Global.discreteTopology_principalSubgroup F
  have ho : IsOpen ({0} : Set (AdeleRing.principalSubgroup (𝓞 F) F)) := isOpen_discrete _
  obtain ⟨t, ht, hpre⟩ := isOpen_induced_iff.mp ho
  refine ⟨Set.pi Set.univ fun _ => t, set_pi_mem_nhds Set.finite_univ fun _ _ => ht.mem_nhds ?_, ?_⟩
  · have h0 : ((0 : AdeleRing.principalSubgroup (𝓞 F) F) : AF F) ∈ t := by
      have : (0 : AdeleRing.principalSubgroup (𝓞 F) F) ∈ Subtype.val ⁻¹' t := by rw [hpre]; rfl
      exact this
    simpa using h0
  · intro ξ hξ
    funext i
    have hm : algebraMap F (AF F) (ξ i) ∈ AdeleRing.principalSubgroup (𝓞 F) F := ⟨ξ i, rfl⟩
    have : (⟨_, hm⟩ : AdeleRing.principalSubgroup (𝓞 F) F) ∈ Subtype.val ⁻¹' t := hξ i (Set.mem_univ _)
    rw [hpre] at this
    have h2 : algebraMap F (AF F) (ξ i) = 0 := congrArg Subtype.val this
    exact (NumberField.AdeleRing.algebraMap_injective (𝓞 F) F) (h2.trans (map_zero _).symm)

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `F _ _ ψ hψ κ _ S hiso hspan`. Take `⟨P, Q, hP, hQ, hker⟩` from `GlobalTheory.T.exists_rational_projection_section_isotropicSpan F κ S hspan`. Take `⟨D, hD, hDξ⟩` from `disc F κ`. Use `set PA := P.map (algebraMap F (AF F)) with hPA`. Use `set QA := Q.map (algebraMap F (AF F)) with hQA`.

Take `⟨g, hgdef⟩ : ∃ g : (κ → AF F) → ℂ, g = fun x => ψ (⅟(2 : AF F) * (x ⬝ᵥ (QA *ᵥ x)))` from `⟨_, rfl⟩`. Establish `hg : Continuous g`. Rewrite using `[hgdef]`. Conclude with `hψ.1.comp (continuous_const.mul (continuous_id.dotProduct (continuous_const.matrix_mulVec continuous_id)))`. Establish `hg0 : 0 < (g 0).re` using `by simp [hgdef]`.

Take `⟨V₀, hV₀, hq⟩` from `exists_nhds_zero_quarter hD`. Choose the witnesses or unpack the hypotheses as in `⟨V, hV, hVm⟩ : ∃ V ∈ nhds (0 : κ → AF F), ∀ x ∈ V, x ∈ V₀ ∧ -x ∈ V₀ ∧ PA *ᵥ x ∈ D ∧ 0 < (g x).re := by`. Use `⟨((V₀ ∩ -V₀) ∩ (fun x => PA *ᵥ x) ⁻¹' D) ∩ {x | 0 < (g x).re}, ?_, fun x hx => ⟨hx.1.1.1, Set.mem_neg.mp hx.1.1.2, hx.1.2, hx.2⟩⟩` and prove the remaining obligations. Use `Filter.inter_mem (Filter.inter_mem (Filter.inter_mem hV₀ (neg_mem_nhds_zero _ hV₀)) ?_) ?_` and prove the remaining obligations. Conclude with `(continuous_const.matrix_mulVec continuous_id).tendsto' (0 : κ → AF F) 0 (by simp) hD`.

Conclude with `((Complex.continuous_re.comp hg).tendsto 0).eventually (lt_mem_nhds hg0)`. Take `⟨Φ, hΦS, hΦc, hΦV, hΦr, hΦ0⟩` from `GlobalTheory.T.exists_nonneg_adelicSchwartz_bump_test F κ V hV`. Establish `hsub : ∀ ξ ξ' : κ → F, (fun i => algebraMap F (AF F) ((ξ - ξ') i)) = (fun i => algebraMap F (AF F) (ξ i)) - (fun i => algebraMap F (AF F) (ξ' i))`. Introduce `ξ ξ'`. Use function extensionality and compare the values at `i`.

Simplify using `[map_sub]`. Establish `KEY : ∀ ξ : κ → F, ∀ v₁ ∈ V, ∀ v₂ ∈ V, ∀ v₃ ∈ V, ∀ v₄ ∈ V, (fun i => algebraMap F (AF F) (ξ i)) = v₁ - v₂ - (v₃ - v₄) → ξ = 0`. Introduce `ξ v₁ h₁ v₂ h₂ v₃ h₃ v₄ h₄ he`. Apply `hDξ` to reduce the goal to its premises. Rewrite using `[he, show v₁ - v₂ - (v₃ - v₄) = v₁ + -v₂ + -v₃ + v₄ by abel]`.

Conclude with `hq (hVm _ h₁).1 (hVm _ h₂).2.1 (hVm _ h₃).2.1 (hVm _ h₄).1`. Establish `hV0 : (0 : κ → AF F) ∈ V` using `mem_of_mem_nhds hV`. Establish `LOC : ∀ a₀ : κ → AF F, ∃ ξ₀ : κ → F, ∀ᶠ a in nhds a₀, ∀ ξ : κ → F, ξ ≠ ξ₀ → Φ ((fun i => algebraMap F (AF F) (ξ i)) + a) = 0`. Introduce `a₀`. Establish `hnear : ∀ᶠ a in nhds a₀, a - a₀ ∈ V` using `(continuous_id.sub continuous_const).tendsto' a₀ 0 (sub_self a₀) hV`.

Distinguish the cases in `h : ∃ ξ₀ : κ → F, ∃ v₁ ∈ V, ∃ v₂ ∈ V, (fun i => algebraMap F (AF F) (ξ₀ i)) + a₀ = v₁ - v₂`. Take `⟨ξ₀, v₁, h₁, v₂, h₂, he⟩` from `h`. Use `⟨ξ₀, ?_⟩` and prove the remaining obligations. Use `filter_upwards [hnear] with a ha ξ hne`. Assume the negation of the conclusion as `hz`.

Apply `hne` to reduce the goal to its premises. Rewrite using `[← sub_eq_zero]`. Use `KEY _ _ (hΦV _ hz) _ ha _ h₁ _ h₂ ?_` and prove the remaining obligations. Rewrite using `[hsub, ← he]`. Normalize the expressions using the abelian group laws.

Use `⟨0, ?_⟩ filter_upwards [hnear] with a ha ξ _` and prove the remaining obligations. Assume the negation of the conclusion as `hz`. Conclude with `h ⟨ξ, _, hΦV _ hz, _, ha, by abel⟩`. Establish `THETA : ∀ w : (κ → AF F) × (κ → AF F), ∃ ξ₀ : κ → F, ∀ᶠ w' in nhds w, thetaSum F (schr ψ w' Φ) = ψ ((fun i => algebraMap F (AF F) (ξ₀ i)) ⬝ᵥ w'.2 + ⅟(2 : AF F) * (w'.1 ⬝ᵥ w'.2)) * Φ ((fun i => algebraMap F (AF F) (ξ₀ i)) + w'.1)`. Introduce `w`.

Take `⟨ξ₀, h⟩` from `LOC w.1`. Use `⟨ξ₀, ?_⟩` and prove the remaining obligations. Use `filter_upwards [(continuous_fst.tendsto w).eventually h] with w' hw'`. Conclude with `tsum_eq_single ξ₀ fun ξ hne => mul_eq_zero_of_right _ (hw' ξ hne)`. Establish `htwo : ⅟(2 : AF F) = algebraMap F (AF F) (2⁻¹ : F)`.

Use `invOf_eq_right_inv ?_` and prove the remaining obligations. Rewrite using `[← map_ofNat (algebraMap F (AF F)) 2, ← map_mul, mul_inv_cancel₀ two_ne_zero, map_one]`. Use `⟨Φ, hΦS, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `continuous_iff_continuousAt.2 fun w => ?_` and prove the remaining obligations. Take `⟨ξ₀, h⟩` from `THETA w`.

Use `ContinuousAt.congr ?_ (h.mono fun _ h => h.symm)` and prove the remaining obligations. Use `Continuous.continuousAt ?_` and prove the remaining obligations. Conclude with `(hψ.1.comp ((continuous_const.dotProduct continuous_snd).add (continuous_const.mul (continuous_fst.dotProduct continuous_snd)))).mul (hΦc.comp (continuous_const.add continuous_fst))`. Introduce `s hs`. Take `⟨ξ₀, h⟩` from `THETA s`.

Rewrite using `[h.self_of_nhds]`. Use `set e : κ → AF F := fun i => algebraMap F (AF F) (ξ₀ i) with he`. Distinguish the cases in `hz : Φ (e + s.1) = 0`. Simplify using `[hz]`. Establish `hx : e + s.1 ∈ V` using `hΦV _ hz`.

Establish `hP0 : P *ᵥ ξ₀ = 0`. Apply `hDξ` to reduce the goal to its premises. Establish `h1` using `(hVm _ hx).2.2.1`. Simplify using `only [Set.mem_preimage, Matrix.mulVec_add, hP s hs, add_zero] at h1`. Use `h1 using 1` and compare the differences between its conclusion and the goal.

Use function extensionality and compare the values at `i`. Conclude with `RingHom.map_mulVec _ _ _ _`. Use `set f : κ → AF F := fun i => algebraMap F (AF F) ((Q *ᵥ ξ₀) i) with hf`. Establish `hef : (e, f) ∈ S` using `hker ξ₀ hP0`. Establish `hac : (s.1, QA *ᵥ s.1) ∈ S` using `hQ s hs`.

Establish `hQe : QA *ᵥ e = f`. Use function extensionality and compare the values at `i`. Conclude with `(RingHom.map_mulVec _ _ _ _).symm`. Establish `h1` using `hiso s hs _ hac`. Establish `h2` using `hiso _ hef s hs`.

Establish `h3` using `hiso _ hef _ hac`. Simplify using `only at h1 h2 h3`. Establish `hrat : e ⬝ᵥ f = algebraMap F (AF F) (ξ₀ ⬝ᵥ (Q *ᵥ ξ₀))` using `(RingHom.map_dotProduct _ _ _).symm`. Establish `hinv : ⅟(2 : AF F) * 2 = 1` using `invOf_mul_self _`. Establish `phase : e ⬝ᵥ s.2 + ⅟(2 : AF F) * (s.1 ⬝ᵥ s.2) = ⅟(2 : AF F) * ((e + s.1) ⬝ᵥ (QA *ᵥ (e + s.1))) + algebraMap F (AF F) (-(2⁻¹ * (ξ₀ ⬝ᵥ (Q *ᵥ ξ₀))))`.

Rewrite using `[Matrix.mulVec_add, hQe, add_dotProduct, dotProduct_add, dotProduct_add, map_neg, map_mul, ← htwo, ← hrat]`. Take the linear combination `h2 - ⅟(2 : AF F) * h3 - ⅟(2 : AF F) * h1 - (s.1 ⬝ᵥ f) * hinv`. Rewrite using `[phase, AddChar.map_add_eq_mul, hψ.2.1, mul_one, Complex.mul_re, (hΦr _).1, mul_zero, sub_zero]`. Establish `hpos` using `(hVm _ hx).2.2.2`. Rewrite `hpos` using `[hgdef]`.

Conclude with `mul_nonneg (le_of_lt hpos) (hΦr _).2`. Establish `hz : ∀ ξ : κ → F, ξ ≠ 0 → Φ ((fun i => algebraMap F (AF F) (ξ i)) + (0 : (κ → AF F) × (κ → AF F)).1) = 0`. Introduce `ξ hne`. Assume the negation of the conclusion as `hz`. Conclude with `hne (KEY ξ _ (hΦV _ hz) 0 hV0 0 hV0 0 hV0 (by simp))`.

Establish `e0 : (fun i => algebraMap F (AF F) ((0 : κ → F) i)) = 0` using `by funext i; simp`. Establish `hsum : thetaSum F (schr ψ 0 Φ) = schr ψ 0 Φ (fun i => algebraMap F (AF F) ((0 : κ → F) i))` using `tsum_eq_single 0 fun ξ hne => mul_eq_zero_of_right _ (hz ξ hne)`. Rewrite using `[hsum, e0]`. Simplify using `only [schr, Prod.fst_zero, Prod.snd_zero, dotProduct_zero, mul_zero, add_zero, AddChar.map_zero_eq_one, one_mul, hΦ0, Complex.one_re]`. Evaluate the numerical expressions.
-/
theorem exists_theta_re_nonneg : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ]
    (S : Submodule (AF F) ((κ → AF F) × (κ → AF F))),
    (∀ s ∈ S, ∀ s' ∈ S, s.1 ⬝ᵥ s'.2 = s'.1 ⬝ᵥ s.2) →
    S ≤ Submodule.span (AF F) {s | s ∈ S ∧ ∃ y z : κ → F,
      s = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))} →
    ∃ Φ ∈ schA F κ, Continuous (fun w => thetaSum F (schr ψ w Φ)) ∧
      (∀ s ∈ S, 0 ≤ (thetaSum F (schr ψ s Φ)).re) ∧ 0 < (thetaSum F (schr ψ 0 Φ)).re := by
  intro F _ _ ψ hψ κ _ S hiso hspan
  classical
  obtain ⟨P, Q, hP, hQ, hker⟩ := GlobalTheory.T.exists_rational_projection_section_isotropicSpan F κ S hspan
  obtain ⟨D, hD, hDξ⟩ := disc F κ
  set PA := P.map (algebraMap F (AF F)) with hPA
  set QA := Q.map (algebraMap F (AF F)) with hQA
  obtain ⟨g, hgdef⟩ : ∃ g : (κ → AF F) → ℂ, g = fun x => ψ (⅟(2 : AF F) * (x ⬝ᵥ (QA *ᵥ x))) := ⟨_, rfl⟩
  have hg : Continuous g := by
    rw [hgdef]
    exact hψ.1.comp (continuous_const.mul (continuous_id.dotProduct (continuous_const.matrix_mulVec continuous_id)))
  have hg0 : 0 < (g 0).re := by simp [hgdef]
  obtain ⟨V₀, hV₀, hq⟩ := exists_nhds_zero_quarter hD
  obtain ⟨V, hV, hVm⟩ : ∃ V ∈ nhds (0 : κ → AF F), ∀ x ∈ V, x ∈ V₀ ∧ -x ∈ V₀ ∧ PA *ᵥ x ∈ D ∧ 0 < (g x).re := by
    refine ⟨((V₀ ∩ -V₀) ∩ (fun x => PA *ᵥ x) ⁻¹' D) ∩ {x | 0 < (g x).re}, ?_, fun x hx => ⟨hx.1.1.1, Set.mem_neg.mp hx.1.1.2, hx.1.2, hx.2⟩⟩
    refine Filter.inter_mem (Filter.inter_mem (Filter.inter_mem hV₀ (neg_mem_nhds_zero _ hV₀)) ?_) ?_
    · exact (continuous_const.matrix_mulVec continuous_id).tendsto' (0 : κ → AF F) 0 (by simp) hD
    · exact ((Complex.continuous_re.comp hg).tendsto 0).eventually (lt_mem_nhds hg0)
  obtain ⟨Φ, hΦS, hΦc, hΦV, hΦr, hΦ0⟩ := GlobalTheory.T.exists_nonneg_adelicSchwartz_bump_test F κ V hV
  have hsub : ∀ ξ ξ' : κ → F, (fun i => algebraMap F (AF F) ((ξ - ξ') i)) =
      (fun i => algebraMap F (AF F) (ξ i)) - (fun i => algebraMap F (AF F) (ξ' i)) := by
    intro ξ ξ'; funext i; simp [map_sub]
  have KEY : ∀ ξ : κ → F, ∀ v₁ ∈ V, ∀ v₂ ∈ V, ∀ v₃ ∈ V, ∀ v₄ ∈ V,
      (fun i => algebraMap F (AF F) (ξ i)) = v₁ - v₂ - (v₃ - v₄) → ξ = 0 := by
    intro ξ v₁ h₁ v₂ h₂ v₃ h₃ v₄ h₄ he
    apply hDξ
    rw [he, show v₁ - v₂ - (v₃ - v₄) = v₁ + -v₂ + -v₃ + v₄ by abel]
    exact hq (hVm _ h₁).1 (hVm _ h₂).2.1 (hVm _ h₃).2.1 (hVm _ h₄).1
  have hV0 : (0 : κ → AF F) ∈ V := mem_of_mem_nhds hV
  have LOC : ∀ a₀ : κ → AF F, ∃ ξ₀ : κ → F, ∀ᶠ a in nhds a₀, ∀ ξ : κ → F, ξ ≠ ξ₀ →
      Φ ((fun i => algebraMap F (AF F) (ξ i)) + a) = 0 := by
    intro a₀
    have hnear : ∀ᶠ a in nhds a₀, a - a₀ ∈ V :=
      (continuous_id.sub continuous_const).tendsto' a₀ 0 (sub_self a₀) hV
    by_cases h : ∃ ξ₀ : κ → F, ∃ v₁ ∈ V, ∃ v₂ ∈ V, (fun i => algebraMap F (AF F) (ξ₀ i)) + a₀ = v₁ - v₂
    · obtain ⟨ξ₀, v₁, h₁, v₂, h₂, he⟩ := h
      refine ⟨ξ₀, ?_⟩
      filter_upwards [hnear] with a ha ξ hne
      by_contra hz
      apply hne
      rw [← sub_eq_zero]
      refine KEY _ _ (hΦV _ hz) _ ha _ h₁ _ h₂ ?_
      rw [hsub, ← he]; abel
    · refine ⟨0, ?_⟩
      filter_upwards [hnear] with a ha ξ _
      by_contra hz
      exact h ⟨ξ, _, hΦV _ hz, _, ha, by abel⟩
  have THETA : ∀ w : (κ → AF F) × (κ → AF F), ∃ ξ₀ : κ → F, ∀ᶠ w' in nhds w,
      thetaSum F (schr ψ w' Φ) = ψ ((fun i => algebraMap F (AF F) (ξ₀ i)) ⬝ᵥ w'.2 + ⅟(2 : AF F) * (w'.1 ⬝ᵥ w'.2)) *
        Φ ((fun i => algebraMap F (AF F) (ξ₀ i)) + w'.1) := by
    intro w
    obtain ⟨ξ₀, h⟩ := LOC w.1
    refine ⟨ξ₀, ?_⟩
    filter_upwards [(continuous_fst.tendsto w).eventually h] with w' hw'
    exact tsum_eq_single ξ₀ fun ξ hne => mul_eq_zero_of_right _ (hw' ξ hne)
  have htwo : ⅟(2 : AF F) = algebraMap F (AF F) (2⁻¹ : F) := by
    refine invOf_eq_right_inv ?_
    rw [← map_ofNat (algebraMap F (AF F)) 2, ← map_mul, mul_inv_cancel₀ two_ne_zero, map_one]
  refine ⟨Φ, hΦS, ?_, ?_, ?_⟩
  · refine continuous_iff_continuousAt.2 fun w => ?_
    obtain ⟨ξ₀, h⟩ := THETA w
    refine ContinuousAt.congr ?_ (h.mono fun _ h => h.symm)
    refine Continuous.continuousAt ?_
    exact (hψ.1.comp ((continuous_const.dotProduct continuous_snd).add
      (continuous_const.mul (continuous_fst.dotProduct continuous_snd)))).mul
      (hΦc.comp (continuous_const.add continuous_fst))
  · intro s hs
    obtain ⟨ξ₀, h⟩ := THETA s
    rw [h.self_of_nhds]
    set e : κ → AF F := fun i => algebraMap F (AF F) (ξ₀ i) with he
    by_cases hz : Φ (e + s.1) = 0
    · simp [hz]
    have hx : e + s.1 ∈ V := hΦV _ hz
    have hP0 : P *ᵥ ξ₀ = 0 := by
      apply hDξ
      have h1 := (hVm _ hx).2.2.1
      simp only [Set.mem_preimage, Matrix.mulVec_add, hP s hs, add_zero] at h1
      convert h1 using 1
      funext i
      exact RingHom.map_mulVec _ _ _ _
    set f : κ → AF F := fun i => algebraMap F (AF F) ((Q *ᵥ ξ₀) i) with hf
    have hef : (e, f) ∈ S := hker ξ₀ hP0
    have hac : (s.1, QA *ᵥ s.1) ∈ S := hQ s hs
    have hQe : QA *ᵥ e = f := by
      funext i
      exact (RingHom.map_mulVec _ _ _ _).symm
    have h1 := hiso s hs _ hac
    have h2 := hiso _ hef s hs
    have h3 := hiso _ hef _ hac
    simp only at h1 h2 h3
    have hrat : e ⬝ᵥ f = algebraMap F (AF F) (ξ₀ ⬝ᵥ (Q *ᵥ ξ₀)) := (RingHom.map_dotProduct _ _ _).symm
    have hinv : ⅟(2 : AF F) * 2 = 1 := invOf_mul_self _
    have phase : e ⬝ᵥ s.2 + ⅟(2 : AF F) * (s.1 ⬝ᵥ s.2) =
        ⅟(2 : AF F) * ((e + s.1) ⬝ᵥ (QA *ᵥ (e + s.1))) + algebraMap F (AF F) (-(2⁻¹ * (ξ₀ ⬝ᵥ (Q *ᵥ ξ₀)))) := by
      rw [Matrix.mulVec_add, hQe, add_dotProduct, dotProduct_add, dotProduct_add, map_neg, map_mul, ← htwo, ← hrat]
      linear_combination h2 - ⅟(2 : AF F) * h3 - ⅟(2 : AF F) * h1 - (s.1 ⬝ᵥ f) * hinv
    rw [phase, AddChar.map_add_eq_mul, hψ.2.1, mul_one, Complex.mul_re, (hΦr _).1, mul_zero, sub_zero]
    have hpos := (hVm _ hx).2.2.2
    rw [hgdef] at hpos
    exact mul_nonneg (le_of_lt hpos) (hΦr _).2
  · have hz : ∀ ξ : κ → F, ξ ≠ 0 → Φ ((fun i => algebraMap F (AF F) (ξ i)) + (0 : (κ → AF F) × (κ → AF F)).1) = 0 := by
      intro ξ hne
      by_contra hz
      exact hne (KEY ξ _ (hΦV _ hz) 0 hV0 0 hV0 0 hV0 (by simp))
    have e0 : (fun i => algebraMap F (AF F) ((0 : κ → F) i)) = 0 := by funext i; simp
    have hsum : thetaSum F (schr ψ 0 Φ) = schr ψ 0 Φ (fun i => algebraMap F (AF F) ((0 : κ → F) i)) :=
      tsum_eq_single 0 fun ξ hne => mul_eq_zero_of_right _ (hz ξ hne)
    rw [hsum, e0]
    simp only [schr, Prod.fst_zero, Prod.snd_zero, dotProduct_zero, mul_zero, add_zero, AddChar.map_zero_eq_one,
      one_mul, hΦ0, Complex.one_re]
    norm_num

end GlobalTheory.ThetaPosIso
