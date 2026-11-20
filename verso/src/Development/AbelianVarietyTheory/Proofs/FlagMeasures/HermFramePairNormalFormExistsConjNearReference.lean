import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairNormalFormGeometrySummaryStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CommonUnipotentStabiliserPreservesTermsAndDatumStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormalFormFlagLatticesNearUnderStabiliserStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormalFormIdealDivisibilityStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairSplitTermNearReferenceBySkewStatement

noncomputable section
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.DegCnt.NormalPos

section
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {H : HermSpace K V} {r : ℕ}

/- English proof (translation)
Rewrite using `[Submodule.mem_smul_pointwise_iff_exists]`. Both sides reduce to the same expression.
-/
theorem mem_smul_iff (s : V ≃ₗ[K] V) (Λ : Submodule (𝓞 K) V) (y : V) :
    y ∈ s • Λ ↔ ∃ x ∈ Λ, s x = y := by
  rw [Submodule.mem_smul_pointwise_iff_exists]
  rfl

/- English proof (translation)
Use extensionality with `y`. Simplify using `only [Submodule.mem_inf, Submodule.restrictScalars_mem, mem_smul_iff]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨x, hx, hxy⟩, hy⟩`. Establish `: x = y` using `s.injective (hxy.trans (h y hy).symm)`.

Conclude with `⟨this ▸ hx, hy⟩`. Introduce and unpack `⟨hx, hy⟩`. Conclude with `⟨⟨y, hx, h y hy⟩, hy⟩`.
-/
theorem smul_inf_eq (s : V ≃ₗ[K] V) (Λ : Submodule (𝓞 K) V) (S : Submodule K V)
    (h : ∀ y ∈ S, s y = y) : (s • Λ) ⊓ rs (𝓞 K) S = Λ ⊓ rs (𝓞 K) S := by
  ext y
  simp only [Submodule.mem_inf, Submodule.restrictScalars_mem, mem_smul_iff]
  constructor
  · rintro ⟨⟨x, hx, hxy⟩, hy⟩
    have : x = y := s.injective (hxy.trans (h y hy).symm)
    exact ⟨this ▸ hx, hy⟩
  · rintro ⟨hx, hy⟩
    exact ⟨⟨y, hx, h y hy⟩, hy⟩

/- English proof (translation)
Introduce and unpack `_ ⟨t, -, rfl⟩`. Conclude with `S.smul_mem t hv`.
-/
theorem line_le (A : Submodule (𝓞 K) K) (v : V) (S : Submodule K V) (hv : v ∈ S) :
    line A v ≤ rs (𝓞 K) S := by
  rintro _ ⟨t, -, rfl⟩
  exact S.smul_mem t hv

omit [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
/- English proof (translation)
Establish `hc : N.c ≠ 0`. Introduce `h`. Use `N.c_norm` as an intermediate fact. Rewrite `this` using `[h, zero_mul]`. Conclude with `zero_ne_one this`.

Use `⟨Submodule.subset_span ⟨a, a.2, rfl⟩, ?_⟩` and prove the remaining obligations. Establish `h1 : N.F'.e a.castSucc ∈ N.F'.X` using `Submodule.subset_span ⟨a, a.2, rfl⟩`. Establish `h2` using `N.F'.X.smul_mem N.c⁻¹ h1`. Rewrite `h2` using `[N.same a.castSucc ha, smul_smul, inv_mul_cancel₀ hc, one_smul]`. Then use the resulting hypothesis.
-/
theorem e_mem_II (N : NF H r) (a : Fin r) (ha : N.j ≤ a.val) : N.F.e a.castSucc ∈ II N.F N.F' := by
  have hc : N.c ≠ 0 := by
    intro h
    have := N.c_norm
    rw [h, zero_mul] at this
    exact zero_ne_one this
  refine ⟨Submodule.subset_span ⟨a, a.2, rfl⟩, ?_⟩
  have h1 : N.F'.e a.castSucc ∈ N.F'.X := Submodule.subset_span ⟨a, a.2, rfl⟩
  have h2 := N.F'.X.smul_mem N.c⁻¹ h1
  rwa [N.same a.castSucc ha, smul_smul, inv_mul_cancel₀ hc, one_smul] at h2

omit [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
/- English proof (translation)
The claim follows from `inf_le_left.trans (le_sup_left.trans le_sup_left)`.
-/
theorem isotropicMeet_le_jointSpan (N : NF H r) : II N.F N.F' ≤ V0 N.F N.F' :=
  inf_le_left.trans (le_sup_left.trans le_sup_left)

omit [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
/- English proof (translation)
Set `φ : V →ₗ[K] V` to `∑ a ∈ Finset.univ.filter (fun a : Fin r => N.j ≤ a.val), (H.B.flip (N.F.e a.castSucc)).smulRight (N.ist a)`. Establish `h1 : N.Ist ≤ LinearMap.eqLocus φ LinearMap.id`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨b, hb, rfl⟩`. Establish `hb' : N.j ≤ b.val` using `hb`.

Use `show φ (N.ist b) = N.ist b`. Simplify using `only [φ, LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.flip_apply]`. Rewrite using `[Finset.sum_eq_single b]`. Rewrite using `[← H.herm, N.ist_e b b hb']`. Simplify using the standard rewrite rules.

Introduce `a _ hab`. Rewrite using `[← H.herm, N.ist_e a b hb']`. Simplify using `[hab]`. Introduce `h; exact absurd (by simpa using hb') h`. Establish `h2 : φ d = d` using `h1 hd`.

Rewrite using `[← h2]`. Simplify using `only [φ, LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.flip_apply]`. Use `Finset.sum_eq_zero fun a ha => ?_` and prove the remaining obligations. Establish `ha' : N.j ≤ a.val` using `by simpa using ha`. Establish `he` using `e_mem_II N a ha'`.

Rewrite using `[← H.herm, (hrad _ (isotropicMeet_le_jointSpan N he)).2 he d hd']`. Simplify using the standard rewrite rules.
-/
theorem eq_zero_of_mem (N : NF H r)
    (hrad : ∀ v ∈ V0 N.F N.F', (∀ w ∈ V0 N.F N.F', H.B v w = 0) ↔ v ∈ II N.F N.F')
    (d : V) (hd : d ∈ N.Ist) (hd' : d ∈ V0 N.F N.F') : d = 0 := by
  let φ : V →ₗ[K] V := ∑ a ∈ Finset.univ.filter (fun a : Fin r => N.j ≤ a.val),
    (H.B.flip (N.F.e a.castSucc)).smulRight (N.ist a)
  have h1 : N.Ist ≤ LinearMap.eqLocus φ LinearMap.id := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨b, hb, rfl⟩
    have hb' : N.j ≤ b.val := hb
    show φ (N.ist b) = N.ist b
    simp only [φ, LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.flip_apply]
    rw [Finset.sum_eq_single b]
    · rw [← H.herm, N.ist_e b b hb']; simp
    · intro a _ hab
      rw [← H.herm, N.ist_e a b hb']; simp [hab]
    · intro h; exact absurd (by simpa using hb') h
  have h2 : φ d = d := h1 hd
  rw [← h2]
  simp only [φ, LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.flip_apply]
  refine Finset.sum_eq_zero fun a ha => ?_
  have ha' : N.j ≤ a.val := by simpa using ha
  have he := e_mem_II N a ha'
  rw [← H.herm, (hrad _ (isotropicMeet_le_jointSpan N he)).2 he d hd']
  simp

omit [NumberField K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
/- English proof (translation)
The claim follows from `Submodule.span_mono (Set.image_mono fun b _ => b.2)`.
-/
theorem Xa_le_X (F : FlagD H r) (j : ℕ) : F.Xa j ≤ F.X :=
  Submodule.span_mono (Set.image_mono fun b _ => b.2)

/- English proof (translation)
Use `set Q := (N.P0 ⊓ rs (𝓞 K) (N.F.Xa N.j)) ⊔ (N.P0 ⊓ rs (𝓞 K) (N.F'.Xa N.j)) ⊔ (N.P0 ⊓ rs (𝓞 K) (II N.F N.F')) ⊔ line 1 N.F.z with hQ`. Establish `hQV : Q ≤ rs (𝓞 K) (V0 N.F N.F')`. Use `sup_le (sup_le (sup_le ?_ ?_) ?_) ?_` and prove the remaining obligations. Conclude with `inf_le_right.trans fun x hx => ((Xa_le_X N.F N.j).trans (le_sup_left.trans le_sup_left) : N.F.Xa N.j ≤ V0 N.F N.F') hx`. Conclude with `inf_le_right.trans fun x hx => ((Xa_le_X N.F' N.j).trans (le_sup_right.trans le_sup_left) : N.F'.Xa N.j ≤ V0 N.F N.F') hx`.

Conclude with `inf_le_right.trans fun x hx => isotropicMeet_le_jointSpan N hx`. Conclude with `line_le _ _ _ (Submodule.mem_sup_right (Submodule.subset_span (by simp)))`. Establish `hP : N.P0 ≤ Q ⊔ rs (𝓞 K) N.Ist`. Use `sup_le (le_sup_of_le_left (sup_le (sup_le ?_ ?_) le_sup_right)) (le_sup_of_le_right ?_)` and prove the remaining obligations. Use `iSup_le fun a => ?_` and prove the remaining obligations.

Establish `h0 : line (N.aa a) (N.F.e a.castSucc) ≤ N.P0` using `le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left (le_iSup (fun a : Fin r => line (N.aa a) (N.F.e a.castSucc)) a)))`. Distinguish the cases in `ha : a.val < N.j`. Conclude with `le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left (le_inf h0 (line_le _ _ _ (Submodule.subset_span ⟨a, ha, rfl⟩)))))`. Conclude with `le_sup_of_le_left (le_sup_of_le_right (le_inf h0 (line_le _ _ _ (e_mem_II N a (not_lt.1 ha)))))`. Use `iSup₂_le fun a ha => ?_` and prove the remaining obligations.

Establish `h0 : line (N.aa a) (N.F'.e a.castSucc) ≤ N.P0` using `le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_right (le_iSup₂ (f := fun (a : Fin r) (_ : a.val < N.j) => line (N.aa a) (N.F'.e a.castSucc)) a ha)))`. Conclude with `le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_right (le_inf h0 (line_le _ _ _ (Submodule.subset_span ⟨a, ha, rfl⟩)))))`. Conclude with `iSup₂_le fun a ha => line_le _ _ _ (Submodule.subset_span ⟨a, ha, rfl⟩)`. Introduce and unpack `p ⟨hp, hpV⟩`. Take `⟨u, hu, d, hd, rfl⟩` from `Submodule.mem_sup.1 (hP hp)`.

Establish `hdV : d ∈ V0 N.F N.F'`. Use `(V0 N.F N.F').sub_mem hpV (hQV hu)` as an intermediate fact. Rewrite `this` using `[add_sub_cancel_left]`. Then use the resulting hypothesis. Rewrite using `[eq_zero_of_mem N hrad d hd hdV, add_zero]`. Conclude with `hu`.
-/
theorem P0_inf_V0_le_sup_of_radical (N : NF H r)
    (hrad : ∀ v ∈ V0 N.F N.F', (∀ w ∈ V0 N.F N.F', H.B v w = 0) ↔ v ∈ II N.F N.F') :
    N.P0 ⊓ rs (𝓞 K) (V0 N.F N.F') ≤ (N.P0 ⊓ rs (𝓞 K) (N.F.Xa N.j)) ⊔ (N.P0 ⊓ rs (𝓞 K) (N.F'.Xa N.j)) ⊔
      (N.P0 ⊓ rs (𝓞 K) (II N.F N.F')) ⊔ line 1 N.F.z := by
  set Q := (N.P0 ⊓ rs (𝓞 K) (N.F.Xa N.j)) ⊔ (N.P0 ⊓ rs (𝓞 K) (N.F'.Xa N.j)) ⊔
      (N.P0 ⊓ rs (𝓞 K) (II N.F N.F')) ⊔ line 1 N.F.z with hQ
  have hQV : Q ≤ rs (𝓞 K) (V0 N.F N.F') := by
    refine sup_le (sup_le (sup_le ?_ ?_) ?_) ?_
    · exact inf_le_right.trans fun x hx =>
        ((Xa_le_X N.F N.j).trans (le_sup_left.trans le_sup_left) : N.F.Xa N.j ≤ V0 N.F N.F') hx
    · exact inf_le_right.trans fun x hx =>
        ((Xa_le_X N.F' N.j).trans (le_sup_right.trans le_sup_left) : N.F'.Xa N.j ≤ V0 N.F N.F') hx
    · exact inf_le_right.trans fun x hx => isotropicMeet_le_jointSpan N hx
    · exact line_le _ _ _ (Submodule.mem_sup_right (Submodule.subset_span (by simp)))
  have hP : N.P0 ≤ Q ⊔ rs (𝓞 K) N.Ist := by
    refine sup_le (le_sup_of_le_left (sup_le (sup_le ?_ ?_) le_sup_right)) (le_sup_of_le_right ?_)
    · refine iSup_le fun a => ?_
      have h0 : line (N.aa a) (N.F.e a.castSucc) ≤ N.P0 :=
        le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left
          (le_iSup (fun a : Fin r => line (N.aa a) (N.F.e a.castSucc)) a)))
      by_cases ha : a.val < N.j
      · exact le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left
          (le_inf h0 (line_le _ _ _ (Submodule.subset_span ⟨a, ha, rfl⟩)))))
      · exact le_sup_of_le_left (le_sup_of_le_right
          (le_inf h0 (line_le _ _ _ (e_mem_II N a (not_lt.1 ha)))))
    · refine iSup₂_le fun a ha => ?_
      have h0 : line (N.aa a) (N.F'.e a.castSucc) ≤ N.P0 :=
        le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_right
          (le_iSup₂ (f := fun (a : Fin r) (_ : a.val < N.j) => line (N.aa a) (N.F'.e a.castSucc)) a ha)))
      exact le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_right
          (le_inf h0 (line_le _ _ _ (Submodule.subset_span ⟨a, ha, rfl⟩)))))
    · exact iSup₂_le fun a ha => line_le _ _ _ (Submodule.subset_span ⟨a, ha, rfl⟩)
  rintro p ⟨hp, hpV⟩
  obtain ⟨u, hu, d, hd, rfl⟩ := Submodule.mem_sup.1 (hP hp)
  have hdV : d ∈ V0 N.F N.F' := by
    have := (V0 N.F N.F').sub_mem hpV (hQV hu)
    rwa [add_sub_cancel_left] at this
  rw [eq_zero_of_mem N hrad d hd hdV, add_zero]
  exact hu

/- English proof (translation)
Introduce `y hy` and use `(mem_fixingSubgroup_iff _).1 hs.2 y hy`.
-/
theorem fix_of_mem_Rs (N : NF H r) {s : V ≃ₗ[K] V} (hs : s ∈ N.Rs) : ∀ y ∈ N.Wt, s y = y :=
  fun y hy => (mem_fixingSubgroup_iff _).1 hs.2 y hy

/- English proof (translation)
Unfold `NF.Split at h ⊢`. Rewrite using `[hT, smul_inf_eq s Λ _ (fix_of_mem_Rs N hs), h]`.
-/
theorem split_smul (N : NF H r) {s : V ≃ₗ[K] V} (hs : s ∈ N.Rs) {Λ : Submodule (𝓞 K) V}
    (hT : latTh N.F N.F' (s • Λ) = latTh N.F N.F' Λ) (h : N.Split Λ) : N.Split (s • Λ) := by
  unfold NF.Split at h ⊢
  rw [hT, smul_inf_eq s Λ _ (fix_of_mem_Rs N hs), h]

/- English proof (translation)
Assemble the required witnesses or components as `⟨(Submodule.smul_mono_left h).trans hn.1, (Submodule.smul_mono_left h).trans hn.2⟩`.
-/
theorem near_mono (N : NF H r) {𝔞 𝔟 : Ideal (𝓞 K)} (h : 𝔞 ≤ 𝔟) {Λ : Submodule (𝓞 K) V}
    (hn : N.Near 𝔟 Λ) : N.Near 𝔞 Λ :=
  ⟨(Submodule.smul_mono_left h).trans hn.1, (Submodule.smul_mono_left h).trans hn.2⟩

end

/- English proof (translation)
Introduce `K V _ _ _ _ _ _ _ _ H hK r N g Λ hg hΛ 𝔠 h0 hst hT hD hS`. Establish `hrad` using `(GlobalTheory.T.hermFramePairNormalForm_geometry_summary K V H hK r N).1.2.2.2.1`. Take `⟨s₁, hs₁, -, h₁⟩` from `GlobalTheory.T.normalForm_flag_lattices_near_under_stabiliser K V H hK r N g Λ hg hΛ 𝔠 h0 hst hT hD`. Take `⟨a₁, a₂, a₃, a₄⟩` from `h₁ _ rfl`. Take `⟨t₁, -, th₁, -⟩` from `GlobalTheory.T.commonUnipotent_stabiliser_preserves_terms_and_datum K V H hK r N g Λ hg hΛ s₁ hs₁.1`.

Establish `hS₁` using `split_smul N hs₁ th₁ hS`. Take `⟨s₂, hs₂, hfix, h₂⟩` from `GlobalTheory.T.normal_form_ideal_divisibility K V H hK r N g _ hg t₁ 𝔠 h0 hst hT hD`. Take `⟨b₁, b₂, b₃⟩` from `h₂ _ rfl`. Take `⟨t₂, -, th₂, -⟩` from `GlobalTheory.T.commonUnipotent_stabiliser_preserves_terms_and_datum K V H hK r N g _ hg t₁ s₂ hs₂.1`. Establish `hS₂` using `split_smul N hs₂ th₂ hS₁`.

Establish `e₁` using `smul_inf_eq s₂ (s₁ • Λ) (N.F.Xa N.j) fun y hy => hfix y (Submodule.mem_sup_left hy)`. Establish `e₂` using `smul_inf_eq s₂ (s₁ • Λ) (N.F'.Xa N.j) fun y hy => hfix y (Submodule.mem_sup_right hy)`. Establish `key : 𝔠 ^ (2 * r + 2) • (N.P0 ⊓ rs (𝓞 K) (V0 N.F N.F')) ≤ s₂ • s₁ • Λ`. Use `(smul_mono_right _ (P0_inf_V0_le_sup_of_radical N hrad)).trans ?_` and prove the remaining obligations. Rewrite using `[Submodule.smul_sup, Submodule.smul_sup, Submodule.smul_sup]`.

Use `sup_le (sup_le (sup_le ?_ ?_) ?_) ?_` and prove the remaining obligations. Use `le_trans ?_ (e₁.ge.trans inf_le_left)` and prove the remaining obligations. Conclude with `le_inf a₁ (Submodule.smul_le_right.trans inf_le_right)`. Use `le_trans ?_ (e₂.ge.trans inf_le_left)` and prove the remaining obligations. Conclude with `le_inf a₂ (Submodule.smul_le_right.trans inf_le_right)`.

Conclude with `(Submodule.smul_mono_left (Ideal.pow_le_pow_right (by omega))).trans b₁`. Conclude with `(Submodule.smul_mono_left (Ideal.pow_le_self (by omega))).trans b₃`. Take `⟨s₃, hs₃, hn⟩` from `GlobalTheory.T.hermFramePair_split_term_near_reference_by_skew K V H hK r N g _ hg t₂ 𝔠 h0 hst hT hD hS₂ (2 * r + 2) (by omega) key (by rw [e₁]; exact a₃) (by rw [e₂]; exact a₄) b₂`. Establish `hs₃' : s₃ ∈ N.Rs` using `⟨hs₃.1.1, hs₃.2⟩`. Take `⟨-, -, th₃, -⟩` from `GlobalTheory.T.commonUnipotent_stabiliser_preserves_terms_and_datum K V H hK r N g _ hg t₂ s₃ hs₃'.1`.

Use `⟨s₃ * (s₂ * s₁), N.Rs.mul_mem hs₃' (N.Rs.mul_mem hs₂ hs₁), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[mul_smul, mul_smul]`. Conclude with `split_smul N hs₃' th₃ hS₂`. Rewrite using `[mul_smul, mul_smul]`. Conclude with `near_mono N (Ideal.pow_le_pow_right (by omega)) hn`.
-/
theorem exists_near : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ (g : ℕ) (Λ : Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ → ∀ 𝔠 : Ideal (𝓞 K), 𝔠 ≠ ⊥ → (∀ x ∈ 𝔠, ∃ y ∈ 𝔠, (y : K) = star (x : K)) → (∀ x ∈ 𝔠, (N.T : 𝓞 K) ∣ x) → (∀ (l : ℕ) (hl : l ≤ r + 1), l ≤ N.j → Dl N.F N.F' l hl ≠ 0 → ∀ x ∈ 𝔠, ∀ y ∈ ipow N.𝔡 (2 * ∑ a ∈ Finset.range l, ((r : ℤ) - a)), (x : K) * y / Dl N.F N.F' l hl ∈ (1 : Submodule (𝓞 K) K) ∧ (x : K) * y / star (Dl N.F N.F' l hl) ∈ (1 : Submodule (𝓞 K) K)) → N.Split Λ → ∃ s ∈ N.Rs, N.Split (s • Λ) ∧ N.Near (𝔠 ^ (12 * r + 50)) (s • Λ) := by
  intro K V _ _ _ _ _ _ _ _ H hK r N g Λ hg hΛ 𝔠 h0 hst hT hD hS
  have hrad := (GlobalTheory.T.hermFramePairNormalForm_geometry_summary K V H hK r N).1.2.2.2.1
  obtain ⟨s₁, hs₁, -, h₁⟩ := GlobalTheory.T.normalForm_flag_lattices_near_under_stabiliser K V H hK r N g Λ hg hΛ 𝔠 h0 hst hT hD
  obtain ⟨a₁, a₂, a₃, a₄⟩ := h₁ _ rfl
  obtain ⟨t₁, -, th₁, -⟩ := GlobalTheory.T.commonUnipotent_stabiliser_preserves_terms_and_datum K V H hK r N g Λ hg hΛ s₁ hs₁.1
  have hS₁ := split_smul N hs₁ th₁ hS
  obtain ⟨s₂, hs₂, hfix, h₂⟩ := GlobalTheory.T.normal_form_ideal_divisibility K V H hK r N g _ hg t₁ 𝔠 h0 hst hT hD
  obtain ⟨b₁, b₂, b₃⟩ := h₂ _ rfl
  obtain ⟨t₂, -, th₂, -⟩ := GlobalTheory.T.commonUnipotent_stabiliser_preserves_terms_and_datum K V H hK r N g _ hg t₁ s₂ hs₂.1
  have hS₂ := split_smul N hs₂ th₂ hS₁
  have e₁ := smul_inf_eq s₂ (s₁ • Λ) (N.F.Xa N.j) fun y hy => hfix y (Submodule.mem_sup_left hy)
  have e₂ := smul_inf_eq s₂ (s₁ • Λ) (N.F'.Xa N.j) fun y hy => hfix y (Submodule.mem_sup_right hy)
  have key : 𝔠 ^ (2 * r + 2) • (N.P0 ⊓ rs (𝓞 K) (V0 N.F N.F')) ≤ s₂ • s₁ • Λ := by
    refine (smul_mono_right _ (P0_inf_V0_le_sup_of_radical N hrad)).trans ?_
    rw [Submodule.smul_sup, Submodule.smul_sup, Submodule.smul_sup]
    refine sup_le (sup_le (sup_le ?_ ?_) ?_) ?_
    · refine le_trans ?_ (e₁.ge.trans inf_le_left)
      exact le_inf a₁ (Submodule.smul_le_right.trans inf_le_right)
    · refine le_trans ?_ (e₂.ge.trans inf_le_left)
      exact le_inf a₂ (Submodule.smul_le_right.trans inf_le_right)
    · exact (Submodule.smul_mono_left (Ideal.pow_le_pow_right (by omega))).trans b₁
    · exact (Submodule.smul_mono_left (Ideal.pow_le_self (by omega))).trans b₃
  obtain ⟨s₃, hs₃, hn⟩ := GlobalTheory.T.hermFramePair_split_term_near_reference_by_skew K V H hK r N g _ hg t₂ 𝔠 h0 hst hT hD hS₂ (2 * r + 2) (by omega)
    key (by rw [e₁]; exact a₃) (by rw [e₂]; exact a₄) b₂
  have hs₃' : s₃ ∈ N.Rs := ⟨hs₃.1.1, hs₃.2⟩
  obtain ⟨-, -, th₃, -⟩ := GlobalTheory.T.commonUnipotent_stabiliser_preserves_terms_and_datum K V H hK r N g _ hg t₂ s₃ hs₃'.1
  refine ⟨s₃ * (s₂ * s₁), N.Rs.mul_mem hs₃' (N.Rs.mul_mem hs₂ hs₁), ?_, ?_⟩
  · rw [mul_smul, mul_smul]
    exact split_smul N hs₃' th₃ hS₂
  · rw [mul_smul, mul_smul]
    exact near_mono N (Ideal.pow_le_pow_right (by omega)) hn

end GlobalTheory.DegCnt.NormalPos
