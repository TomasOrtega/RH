import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentFundamentalDomainExists
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.UnipMassAdapted

open GlobalTheory.UnipMass GlobalTheory.UnipMassHerm

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B n n₁ X Y X₁ H r s i₀ i₁ hB hV _ hH μN hμ`. Establish `hσ : ∀ a, σ (σ a) = a` using `cm_conj_conj hB.cm`. Establish `hHxx : form σ X.J H.x H.x = 0` using `hH.xx`. Establish `hHyy : form σ X.J H.y H.y = 0` using `hH.yy`. Establish `hHxy : form σ X.J H.x H.y = 1` using `hH.xy`.

Establish `hHorth : ∀ u, form σ X.J (H.ι *ᵥ u) H.x = 0 ∧ form σ X.J (H.ι *ᵥ u) H.y = 0` using `hH.orth`. Establish `hHsplit : ∀ z ∈ X.L, ∃ (s t : E) (u : Fin n₁ → E), s • H.x ∈ X.L ∧ t • H.y ∈ X.L ∧ u ∈ X₁.L ∧ z = s • H.x + H.ι *ᵥ u + t • H.y` using `hH.split`. Establish `hspan : ∀ v : Fin n → E, ∃ (s t : E) (u : Fin n₁ → E), v = s • H.x + H.ι *ᵥ u + t • H.y`. Introduce `v`. Establish `hv : v ∈ Submodule.span E (X.L : Set (Fin n → E))`.

Rewrite using `[hV.lat.span_eq_top]`. Discharge the goal by the elementary cases of `trivial`. Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem z hz`. Take `⟨s, t, u, -, -, -, hz⟩` from `hHsplit z hz`.

Conclude with `⟨s, t, u, hz⟩`. Consider the case `zero => exact ⟨0, 0, 0, by simp⟩`. Consider the case `add y z _ _ hy hz`. Take `⟨s, t, u, rfl⟩` from `hy`. Take `⟨s', t', u', rfl⟩` from `hz`.

Conclude with `⟨s + s', t + t', u + u', by rw [Matrix.mulVec_add]; module⟩`. Consider the case `smul a y _ hy`. Take `⟨s, t, u, rfl⟩` from `hy`. Conclude with `⟨a * s, a * t, a • u, by rw [Matrix.mulVec_smul]; module⟩`. Establish `hx0 : H.x ≠ 0` using `fun h0 => by`.

Establish `h1` using `hHxy`. Rewrite `h1` using `[h0]`. Simplify using `[form] at h1`. Take `⟨δ, hδ0, hδ⟩` from `exists_anti hB.cm`. Set `W' : Spc F E n` to `⟨δ • X.J, X.L, X.θ, X.bas⟩`.

Set `H'' : Plane E n n₁` to `⟨H.x, (-δ⁻¹) • H.y, H.ι, H.𝔟⟩`. Establish `hform : ∀ v w, form σ W'.J v w = δ * form σ X.J v w` using `form_smul_mat σ X.J δ`. Establish `hσt : σ (-δ⁻¹) = δ⁻¹` using `by rw [map_neg, map_inv₀, hδ, inv_neg, neg_neg]`. Establish `hxx : form σ W'.J H''.x H''.x = 0` using `by rw [hform]; show δ * form σ X.J H.x H.x = 0; rw [hHxx, mul_zero]`. Establish `hyy : form σ W'.J H''.y H''.y = 0`.

Rewrite using `[hform]`. Use `show δ * form σ X.J ((-δ⁻¹) • H.y) ((-δ⁻¹) • H.y) = 0`. Rewrite using `[form_smul_left, form_smul_right, hHyy]`. Expand and normalize the polynomial expressions, which then agree. Establish `hxy : form σ W'.J H''.x H''.y = 1`.

Rewrite using `[hform]`. Use `show δ * form σ X.J H.x ((-δ⁻¹) • H.y) = 1`. Rewrite using `[form_smul_right, hHxy, hσt, mul_one, mul_inv_cancel₀ hδ0]`. Establish `horth : ∀ u, form σ W'.J (H''.ι *ᵥ u) H''.x = 0 ∧ form σ W'.J (H''.ι *ᵥ u) H''.y = 0`. Introduce `u`.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hform]`. Use `show δ * form σ X.J (H.ι *ᵥ u) H.x = 0`. Rewrite using `[(hHorth u).1, mul_zero]`. Rewrite using `[hform]`.

Use `show δ * form σ X.J (H.ι *ᵥ u) ((-δ⁻¹) • H.y) = 0`. Rewrite using `[form_smul_right, (hHorth u).2]`. Expand and normalize the polynomial expressions, which then agree. Establish `hspan'' : ∀ v : Fin n → E, ∃ (s t : E) (u : Fin n₁ → E), v = s • H''.x + H''.ι *ᵥ u + t • H''.y`. Introduce `v`.

Take `⟨s, t, u, hv⟩` from `hspan v`. Use `⟨s, t * -δ, u, ?_⟩` and prove the remaining obligations. Use `show v = s • H.x + H.ι *ᵥ u + (t * -δ) • (-δ⁻¹) • H.y`. Rewrite using `[smul_smul, show t * -δ * -δ⁻¹ = t by field_simp, hv]`. Establish `horthA : ∀ z, hA σ W'.J (incM F H''.ι *ᵥ z) (incV F H''.x) = 0`.

Introduce `z`. Rewrite using `[hA_incM_incV]`. Use `Finset.sum_eq_zero fun j _ => ?_` and prove the remaining obligations. Establish `h1` using `(horth (Pi.single j 1)).1`. Rewrite `h1` using `[Matrix.mulVec_single_one]`.

Rewrite using `[show (fun i => H''.ι i j) = H''.ι.col j from rfl, h1, map_zero, mul_zero]`. Establish `hyp : Hyp σ W' H''`. Use `⟨hσ, fun i j => ?_, by rw [hA_incV, hxx, map_zero], horthA⟩` and prove the remaining obligations. Use `show σ (δ * X.J j i) = -(δ * X.J i j)`. Rewrite using `[map_mul, hδ, hV.herm]`.

Expand and normalize the polynomial expressions, which then agree. Take `⟨K', hK', hcov'⟩` from `cocompact hyp hxx hyy hxy horth hspan''`. Establish `hUG` using `UG_smul (F := F) σ X.J hδ0`. Set `φ : UA σ W'.J →* UA σ X.J` to `Subgroup.inclusion hUG.le`. Set `φ' : UA σ X.J →* UA σ W'.J` to `Subgroup.inclusion hUG.ge`.

Establish `hmap : (unip σ W' H'').map φ ≤ unip σ X H`. Rewrite using `[unip, MonoidHom.map_closure]`. Use `Subgroup.closure_mono ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨u, hu, rfl⟩`. Conclude with `hu`.

Establish `hmap' : (unip σ X H).map φ' ≤ unip σ W' H''`. Rewrite using `[unip, MonoidHom.map_closure]`. Use `Subgroup.closure_mono ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨u, hu, rfl⟩`. Conclude with `hu`.

Set `Ψ : unip σ W' H'' → unip σ X H` to `fun g => ⟨φ g.1, hmap ⟨g.1, g.2, rfl⟩⟩`. Establish `hΨ : Continuous Ψ` using `Continuous.subtype_mk (Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _) _`. Establish `hcov : ∀ g : unip σ X H, ∃ γ : (ratU σ X.J).subgroupOf (unip σ X H), γ • g ∈ Ψ '' K'`. Introduce `g`. Take `⟨γ', hγ'⟩` from `hcov' ⟨φ' g.1, hmap' ⟨g.1, g.2, rfl⟩⟩`.

Use `⟨⟨Ψ γ'.1, ?_⟩, ⟨_, hγ', ?_⟩⟩` and prove the remaining obligations. Conclude with `Subgroup.mem_subgroupOf.2 (Subgroup.mem_subgroupOf.2 (Subgroup.mem_subgroupOf.1 (Subgroup.mem_subgroupOf.1 γ'.2)))`. Conclude with `unip_ext rfl`. Take `⟨hTG, hLC, hSC, hT2⟩` from `topUA σ X.J`. Use `haveI := hTG`.

Use `haveI := hLC`. Use `haveI := hSC`. Use `haveI := hT2`. Use `haveI : BorelSpace (UA σ X.J) := ⟨rfl⟩`. Establish `hcl` using `GlobalTheory.T.unipotent_radical_closed_nonzero F E σ _ _ X H hx0`.

Use `haveI : LocallyCompactSpace (unip σ X H) := hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace`. Use `haveI : SecondCountableTopology (unip σ X H) := hcl.isClosedEmbedding_subtypeVal.isEmbedding.secondCountableTopology`. Use `haveI := countable_ratU' σ X.J (unip σ X H)`. Use `haveI := GlobalTheory.T.discrete_rational_points_subgroup F E σ _ X.J (unip σ X H)`. Use `haveI := hμ`.

Conclude with `exists_fundDom_pos_finite _ (Ψ '' K') (hK'.image hΨ) hcov μN`.
-/
theorem exists_fundDom_unip_adapted : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n n₁ : ℕ) (X Y : Spc F E n) (X₁ : Spc F E n₁) (H : Plane E n n₁) (r s i₀ i₁ : ℕ), B.IsGood σ → X.IsHerm σ B r s → (reS X Y).IsHerm σ B r s → H.IsAdapted σ B (reS X Y) X₁ i₀ i₁ → ∀ μN : Measure (unip σ X H), μN.IsHaarMeasure → ∃ 𝓕 : Set (unip σ X H), IsFundamentalDomain ((ratU σ X.J).subgroupOf (unip σ X H)) 𝓕 μN ∧ μN 𝓕 ≠ 0 ∧ μN 𝓕 ≠ ⊤ := by
  intro F E _ _ _ _ _ σ B n n₁ X Y X₁ H r s i₀ i₁ hB hV _ hH μN hμ
  have hσ : ∀ a, σ (σ a) = a := cm_conj_conj hB.cm
  have hHxx : form σ X.J H.x H.x = 0 := hH.xx
  have hHyy : form σ X.J H.y H.y = 0 := hH.yy
  have hHxy : form σ X.J H.x H.y = 1 := hH.xy
  have hHorth : ∀ u, form σ X.J (H.ι *ᵥ u) H.x = 0 ∧ form σ X.J (H.ι *ᵥ u) H.y = 0 := hH.orth
  have hHsplit : ∀ z ∈ X.L, ∃ (s t : E) (u : Fin n₁ → E), s • H.x ∈ X.L ∧ t • H.y ∈ X.L ∧ u ∈ X₁.L ∧
      z = s • H.x + H.ι *ᵥ u + t • H.y := hH.split
  have hspan : ∀ v : Fin n → E, ∃ (s t : E) (u : Fin n₁ → E), v = s • H.x + H.ι *ᵥ u + t • H.y := by
    intro v
    have hv : v ∈ Submodule.span E (X.L : Set (Fin n → E)) := by
      rw [hV.lat.span_eq_top]; trivial
    induction hv using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨s, t, u, -, -, -, hz⟩ := hHsplit z hz
      exact ⟨s, t, u, hz⟩
    | zero => exact ⟨0, 0, 0, by simp⟩
    | add y z _ _ hy hz =>
      obtain ⟨s, t, u, rfl⟩ := hy
      obtain ⟨s', t', u', rfl⟩ := hz
      exact ⟨s + s', t + t', u + u', by rw [Matrix.mulVec_add]; module⟩
    | smul a y _ hy =>
      obtain ⟨s, t, u, rfl⟩ := hy
      exact ⟨a * s, a * t, a • u, by rw [Matrix.mulVec_smul]; module⟩
  have hx0 : H.x ≠ 0 := fun h0 => by
    have h1 := hHxy
    rw [h0] at h1
    simp [form] at h1
  obtain ⟨δ, hδ0, hδ⟩ := exists_anti hB.cm
  let W' : Spc F E n := ⟨δ • X.J, X.L, X.θ, X.bas⟩
  let H'' : Plane E n n₁ := ⟨H.x, (-δ⁻¹) • H.y, H.ι, H.𝔟⟩
  have hform : ∀ v w, form σ W'.J v w = δ * form σ X.J v w := form_smul_mat σ X.J δ
  have hσt : σ (-δ⁻¹) = δ⁻¹ := by rw [map_neg, map_inv₀, hδ, inv_neg, neg_neg]
  have hxx : form σ W'.J H''.x H''.x = 0 := by rw [hform]; show δ * form σ X.J H.x H.x = 0; rw [hHxx, mul_zero]
  have hyy : form σ W'.J H''.y H''.y = 0 := by
    rw [hform]; show δ * form σ X.J ((-δ⁻¹) • H.y) ((-δ⁻¹) • H.y) = 0
    rw [form_smul_left, form_smul_right, hHyy]; ring
  have hxy : form σ W'.J H''.x H''.y = 1 := by
    rw [hform]; show δ * form σ X.J H.x ((-δ⁻¹) • H.y) = 1
    rw [form_smul_right, hHxy, hσt, mul_one, mul_inv_cancel₀ hδ0]
  have horth : ∀ u, form σ W'.J (H''.ι *ᵥ u) H''.x = 0 ∧ form σ W'.J (H''.ι *ᵥ u) H''.y = 0 := by
    intro u
    refine ⟨?_, ?_⟩
    · rw [hform]; show δ * form σ X.J (H.ι *ᵥ u) H.x = 0; rw [(hHorth u).1, mul_zero]
    · rw [hform]; show δ * form σ X.J (H.ι *ᵥ u) ((-δ⁻¹) • H.y) = 0; rw [form_smul_right, (hHorth u).2]; ring
  have hspan'' : ∀ v : Fin n → E, ∃ (s t : E) (u : Fin n₁ → E), v = s • H''.x + H''.ι *ᵥ u + t • H''.y := by
    intro v
    obtain ⟨s, t, u, hv⟩ := hspan v
    refine ⟨s, t * -δ, u, ?_⟩
    show v = s • H.x + H.ι *ᵥ u + (t * -δ) • (-δ⁻¹) • H.y
    rw [smul_smul, show t * -δ * -δ⁻¹ = t by field_simp, hv]
  have horthA : ∀ z, hA σ W'.J (incM F H''.ι *ᵥ z) (incV F H''.x) = 0 := by
    intro z
    rw [hA_incM_incV]
    refine Finset.sum_eq_zero fun j _ => ?_
    have h1 := (horth (Pi.single j 1)).1
    rw [Matrix.mulVec_single_one] at h1
    rw [show (fun i => H''.ι i j) = H''.ι.col j from rfl, h1, map_zero, mul_zero]
  have hyp : Hyp σ W' H'' := by
    refine ⟨hσ, fun i j => ?_, by rw [hA_incV, hxx, map_zero], horthA⟩
    show σ (δ * X.J j i) = -(δ * X.J i j)
    rw [map_mul, hδ, hV.herm]; ring
  obtain ⟨K', hK', hcov'⟩ := cocompact hyp hxx hyy hxy horth hspan''
  have hUG := UG_smul (F := F) σ X.J hδ0
  let φ : UA σ W'.J →* UA σ X.J := Subgroup.inclusion hUG.le
  let φ' : UA σ X.J →* UA σ W'.J := Subgroup.inclusion hUG.ge
  have hmap : (unip σ W' H'').map φ ≤ unip σ X H := by
    rw [unip, MonoidHom.map_closure]
    refine Subgroup.closure_mono ?_
    rintro _ ⟨u, hu, rfl⟩
    exact hu
  have hmap' : (unip σ X H).map φ' ≤ unip σ W' H'' := by
    rw [unip, MonoidHom.map_closure]
    refine Subgroup.closure_mono ?_
    rintro _ ⟨u, hu, rfl⟩
    exact hu
  let Ψ : unip σ W' H'' → unip σ X H := fun g => ⟨φ g.1, hmap ⟨g.1, g.2, rfl⟩⟩
  have hΨ : Continuous Ψ :=
    Continuous.subtype_mk (Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _) _
  have hcov : ∀ g : unip σ X H, ∃ γ : (ratU σ X.J).subgroupOf (unip σ X H), γ • g ∈ Ψ '' K' := by
    intro g
    obtain ⟨γ', hγ'⟩ := hcov' ⟨φ' g.1, hmap' ⟨g.1, g.2, rfl⟩⟩
    refine ⟨⟨Ψ γ'.1, ?_⟩, ⟨_, hγ', ?_⟩⟩
    · exact Subgroup.mem_subgroupOf.2 (Subgroup.mem_subgroupOf.2
        (Subgroup.mem_subgroupOf.1 (Subgroup.mem_subgroupOf.1 γ'.2)))
    · exact unip_ext rfl
  obtain ⟨hTG, hLC, hSC, hT2⟩ := topUA σ X.J
  haveI := hTG
  haveI := hLC
  haveI := hSC
  haveI := hT2
  haveI : BorelSpace (UA σ X.J) := ⟨rfl⟩
  have hcl := GlobalTheory.T.unipotent_radical_closed_nonzero F E σ _ _ X H hx0
  haveI : LocallyCompactSpace (unip σ X H) := hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology (unip σ X H) :=
    hcl.isClosedEmbedding_subtypeVal.isEmbedding.secondCountableTopology
  haveI := countable_ratU' σ X.J (unip σ X H)
  haveI := GlobalTheory.T.discrete_rational_points_subgroup F E σ _ X.J (unip σ X H)
  haveI := hμ
  exact exists_fundDom_pos_finite _ (Ψ '' K') (hK'.image hΨ) hcov μN

end GlobalTheory.UnipMassAdapted
