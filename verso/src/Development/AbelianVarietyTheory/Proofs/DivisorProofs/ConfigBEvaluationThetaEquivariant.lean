import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeIntZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocallyConstantMaxCompactActionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBSchwartzBruhatLatticeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBEigenTripleRelationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrablePowerNormCompactStatement
open MeasureTheory Filter NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ConeSoB
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.ConeSoB

/- English proof (translation)
Take `⟨t, ht⟩` from `hC.elim_finite_subcover (fun c : G => (fun x => x - c) ⁻¹' (Λ : Set G)) (fun c => hΛ.preimage (continuous_sub_right c)) (fun x _ => Set.mem_iUnion.2 ⟨x, by simp [Λ.zero_mem]⟩)`. Set `rep : G → β` to `fun c => if h : ∃ a, p a - c ∈ Λ then f h.choose else 0`. Use `(((t.finite_toSet.image rep).insert 0)).subset ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨a, rfl⟩`. Distinguish the cases in `hp : p a ∈ C`.

Take `⟨c, hc, hac⟩` from `Set.mem_iUnion₂.1 (ht hp)`. Establish `hex : ∃ a', p a' - c ∈ Λ` using `⟨a, hac⟩`. Use `Set.mem_insert_of_mem _ ⟨c, hc, ?_⟩` and prove the remaining obligations. Simplify using `only [rep, dif_pos hex]`. Use `hinv a _ ?_` and prove the remaining obligations.

Use `Λ.sub_mem hex.choose_spec hac` as an intermediate fact. Simplify using `using this`. Conclude with `Set.mem_insert_iff.2 (Or.inl (h0 a hp))`.
-/
theorem finite_range_of_lattice {α β G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [Zero β]
    (f : α → β) (p : α → G) (Λ : AddSubgroup G) (hΛ : IsOpen (Λ : Set G)) (C : Set G) (hC : IsCompact C)
    (hinv : ∀ a a', p a' - p a ∈ Λ → f a' = f a) (h0 : ∀ a, p a ∉ C → f a = 0) : (Set.range f).Finite := by
  classical
  obtain ⟨t, ht⟩ := hC.elim_finite_subcover (fun c : G => (fun x => x - c) ⁻¹' (Λ : Set G))
    (fun c => hΛ.preimage (continuous_sub_right c)) (fun x _ => Set.mem_iUnion.2 ⟨x, by simp [Λ.zero_mem]⟩)
  let rep : G → β := fun c => if h : ∃ a, p a - c ∈ Λ then f h.choose else 0
  refine (((t.finite_toSet.image rep).insert 0)).subset ?_
  rintro _ ⟨a, rfl⟩
  by_cases hp : p a ∈ C
  · obtain ⟨c, hc, hac⟩ := Set.mem_iUnion₂.1 (ht hp)
    have hex : ∃ a', p a' - c ∈ Λ := ⟨a, hac⟩
    refine Set.mem_insert_of_mem _ ⟨c, hc, ?_⟩
    simp only [rep, dif_pos hex]
    refine hinv a _ ?_
    have := Λ.sub_mem hex.choose_spec hac
    simpa using this
  · exact Set.mem_insert_iff.2 (Or.inl (h0 a hp))

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B a b G G₁ H H' hC e' hE X om om' om₁ om₁' hT hT₁ ei ev hei hvac hfac K hK μK₁ μ₁ hμK hμ φ hφ`. Use `haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E`. Take `⟨_, _, _, _, _⟩` from `idelesAt_facts E (evFin F B.v₁)`. Use `haveI : BorelSpace (UA σ G.V'.J) := ⟨rfl⟩`. Use `haveI : IsFiniteMeasure μK₁ := ⟨by rw [hμK.2]; exact ENNReal.one_lt_top⟩`.

Take `⟨hlcK, hfinK⟩` from `GlobalTheory.T.locally_constant_max_compact_action B G X om om' hT K hK φ hφ`. Set `Fl : ((Fin (b + 2) × Fin (a + (b + 2)) → Fv F B.v₁) → ℂ) → (AE F E)ˣ → (Fin b × Fin (a + b) → Fv F B.v₁) → ℂ` to `fun ψ₀ l => ev B.v₁ (locOp B.v₁ (G.M'.co.rho B.ψ (partFin B.v₁ (shiftB σ H H' l))) ψ₀)`. Establish `hcomp : Continuous fun l : idelesAt E (evFin F B.v₁) => compFin F E B.v₁ l.1.1` using `Units.continuous_val.comp ((GlobalTheory.Doubling.continuous_unitFin B.v₁).comp continuous_subtype_val)`. Establish `hFl : ∀ ψ₀ ∈ SB (Fin (b + 2) × Fin (a + (b + 2)) → Fv F B.v₁), (Set.range (Fl ψ₀)).Finite ∧ (∃ C : Set (Fv F B.v₁ ⊗[F] E), IsCompact C ∧ ∀ l : (AE F E)ˣ, compFin F E B.v₁ l.1 ∉ C → Fl ψ₀ l = 0) ∧ IsLocallyConstant (fun l : idelesAt E (evFin F B.v₁) => Fl ψ₀ l.1)`. Introduce `ψ₀ hψ₀`.

Take `⟨Λ, hΛ, hinv⟩` from `GlobalTheory.T.config_b_schwartz_bruhat_lattice B G G₁ H H' hC X om om' hT ψ₀ hψ₀`. Take `⟨C, hCc, h0⟩` from `GlobalTheory.T.config_b_eigen_triple_relation B G G₁ H H' hC e' hE X om om' om₁ om₁' hT hT₁ ei ev hei hvac hfac ψ₀ hψ₀`. Establish `hinv' : ∀ l l' : (AE F E)ˣ, compFin F E B.v₁ l'.1 - compFin F E B.v₁ l.1 ∈ Λ → Fl ψ₀ l' = Fl ψ₀ l` using `fun l l' h => by simp only [Fl]; rw [hinv l l' h]`. Use `⟨finite_range_of_lattice (Fl ψ₀) (fun l => compFin F E B.v₁ l.1) Λ hΛ C hCc hinv' h0, ⟨C, hCc, h0⟩, ?_⟩` and prove the remaining obligations. Use `(IsLocallyConstant.iff_eventually_eq _).2 fun x => ?_` and prove the remaining obligations.

Establish `ho : IsOpen {l : idelesAt E (evFin F B.v₁) | compFin F E B.v₁ l.1.1 - compFin F E B.v₁ x.1.1 ∈ Λ}` using `hΛ.preimage (hcomp.sub continuous_const)`. Use `filter_upwards [ho.mem_nhds (by simp [Λ.zero_mem])] with l hl`. Conclude with `hinv' x.1 l.1 hl`. Establish `hSB : ∀ ψ₀ ∈ Set.range (fun k : KAt K (evFin F B.v₁) => locOp B.v₁ (om' (k.1, 1)) φ), ψ₀ ∈ SB (Fin (b + 2) × Fin (a + (b + 2)) → Fv F B.v₁)`. Introduce and unpack `_ ⟨k, rfl⟩`.

Conclude with `locOp_mem _ _ _`. Use `set S := ⋃ ψ₀ ∈ Set.range (fun k : KAt K (evFin F B.v₁) => locOp B.v₁ (om' (k.1, 1)) φ), Set.range (Fl ψ₀) with hS`. Establish `hSfin : S.Finite` using `hfinK.biUnion fun ψ₀ h => (hFl ψ₀ (hSB ψ₀ h)).1`. Establish `hν : Continuous fun x : (AE F E)ˣ => (X.ν x : ℂ)`. Establish `h1 : Continuous X.ν` using `hT.chars.heckeα.1.div' hT.chars.heckeβ.1`.

Conclude with `continuous_subtype_val.comp h1`. Establish `hz : 1 ≤ (a - (b + 2)) / 2 + 1` using `Nat.le_add_left 1 _`. Establish `hint : ∀ y, ∀ ψ₀ ∈ SB (Fin (b + 2) × Fin (a + (b + 2)) → Fv F B.v₁), Integrable (fun l : idelesAt E (evFin F B.v₁) => Fl ψ₀ l.1 y * (X.ν l.1 : ℂ) * ((GlobalTheory.Doubling.absE F E l.1 : ℝ) : ℂ) ^ ((a - (b + 2)) / 2 + 1)) μ₁`. Introduce `y ψ₀ hψ₀`. Take `⟨hfin, ⟨C, hCc, h0⟩, hlc⟩` from `hFl ψ₀ hψ₀`.

Choose the witnesses or unpack the hypotheses as in `⟨M, hM⟩ : ∃ M, ∀ l, ‖Fl ψ₀ l y‖ ≤ M := by`. Take `⟨M, hM⟩` from `(hfin.image (fun g => ‖g y‖)).bddAbove`. Conclude with `⟨M, fun l => hM ⟨_, ⟨l, rfl⟩, rfl⟩⟩`. Establish `hL` using `(GlobalTheory.T.integrable_power_norm_compact B.v₁ μ₁ hμ C hCc _ hz).const_mul M`. Use `hL.mono' ?_ (Eventually.of_forall fun l => ?_)` and prove the remaining obligations.

Use `Continuous.aestronglyMeasurable ?_` and prove the remaining obligations. Use `(((hlc.comp fun g => g y).continuous.mul (hν.comp continuous_subtype_val)).mul ?_)` and prove the remaining obligations. Conclude with `((Complex.continuous_ofReal.comp (NNReal.continuous_coe.comp (GlobalTheory.Doubling.continuous_absE.comp continuous_subtype_val))).pow _)`. Distinguish the cases in `hl : compFin F E B.v₁ l.1.1 ∈ C`. Rewrite using `[Set.indicator_of_mem hl, norm_mul, norm_mul, Circle.norm_coe, mul_one, norm_pow, Complex.norm_real, Real.norm_of_nonneg (NNReal.coe_nonneg _)]`.

Conclude with `mul_le_mul_of_nonneg_right (hM l.1) (pow_nonneg (NNReal.coe_nonneg _) _)`. Rewrite using `[h0 _ hl, Set.indicator_of_notMem hl]`. Simplify using the standard rewrite rules. Use `⟨Submodule.span ℂ S, FiniteDimensional.span_of_finite ℂ hSfin, ?_, fun k l => ?_, fun y => ⟨fun k => ?_, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[Submodule.span_le]`.

Introduce `f hf`. Take `⟨ψ₀, hψ₀, ⟨l, rfl⟩⟩` from `Set.mem_iUnion₂.1 hf`. Establish `h : Fl ψ₀ l ∈ (SB _).map (ev B.v₁)` using `Submodule.mem_map_of_mem (locOp_mem _ _ _)`. Rewrite `h` using `[(hvac B.v₁).2]`. Conclude with `h`.

Establish `e : (fun y => coneFinInt B G.M' om' B.v₁ (ev B.v₁) (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) φ k.1 l.1 y) = ((X.ν l.1 : ℂ) * ((GlobalTheory.Doubling.absE F E l.1 : ℝ) : ℂ) ^ ((a - (b + 2)) / 2 + 1)) • Fl (locOp B.v₁ (om' (k.1, 1)) φ) l.1`. Use function extensionality and compare the values at `y`. Simplify using `only [coneFinInt, Pi.smul_apply, smul_eq_mul, Fl]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`.

Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_iUnion₂.2 ⟨_, ⟨k, rfl⟩, ⟨l.1, rfl⟩⟩))`. Conclude with `hint y _ (locOp_mem _ _ _)`. Set `h : ((Fin (b + 2) × Fin (a + (b + 2)) → Fv F B.v₁) → ℂ) → ℂ` to `fun ψ₀ => ∫ l : idelesAt E (evFin F B.v₁), Fl ψ₀ l.1 y * (X.ν l.1 : ℂ) * ((GlobalTheory.Doubling.absE F E l.1 : ℝ) : ℂ) ^ ((a - (b + 2)) / 2 + 1) ∂μ₁`. Establish `hlc` using `hlcK.comp h`. Take `⟨M, hM⟩` from `((hfinK.image h).image norm).bddAbove`.

Use `(integrable_const M).mono' hlc.continuous.aestronglyMeasurable (Eventually.of_forall fun k => ?_)` and prove the remaining obligations. Conclude with `hM ⟨_, ⟨_, ⟨k, rfl⟩, rfl⟩, rfl⟩`.
-/
theorem integrands_findim : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} (B : Base F E) {a b : ℕ}
    (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ (e' : Fn F (b + 2) (a + (b + 2)) →ₗ[ℂ] Fn F b (a + b)), IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e' →
    ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W),
    IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ (ei : SInf F (Fin (b + 2) × Fin (a + (b + 2))) →L[ℂ] SInf F (Fin b × Fin (a + b)))
      (ev : ∀ v : Pl F, ((Fin (b + 2) × Fin (a + (b + 2)) → Fv F v) → ℂ) →ₗ[ℂ] (Fin b × Fin (a + b) → Fv F v) → ℂ),
    ei ≠ 0 → (∀ v, ev v (G.M'.vac v) = G₁.M'.vac v ∧ (SB _).map (ev v) = SB _) →
    (∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = G.M'.vac v) → e' (pure f φ) = pure (ei f) fun v => ev v (φ v)) →
    ∀ (K : Subgroup (UA σ G.V'.J)), IsStab B K →
    ∀ (μK₁ : Measure (KAt K (evFin F B.v₁))) (μ₁ : Measure (idelesAt E (evFin F B.v₁))),
    IsNormK K (evFin F B.v₁) μK₁ → IsNormE E B.v₁ μ₁ →
    ∀ φ ∈ SB (Fin (b + 2) × Fin (a + (b + 2)) → Fv F B.v₁),
    ∃ V : Submodule ℂ ((Fin b × Fin (a + b) → Fv F B.v₁) → ℂ), FiniteDimensional ℂ V ∧ V ≤ SB _ ∧
      (∀ (k : KAt K (evFin F B.v₁)) (l : idelesAt E (evFin F B.v₁)),
        (fun y => coneFinInt B G.M' om' B.v₁ (ev B.v₁) (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) φ k.1 l.1 y) ∈ V) ∧
      ∀ y, (∀ k : KAt K (evFin F B.v₁), Integrable (fun l : idelesAt E (evFin F B.v₁) =>
          coneFinInt B G.M' om' B.v₁ (ev B.v₁) (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) φ k.1 l.1 y) μ₁) ∧
        Integrable (fun k : KAt K (evFin F B.v₁) => ∫ l : idelesAt E (evFin F B.v₁),
          coneFinInt B G.M' om' B.v₁ (ev B.v₁) (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) φ k.1 l.1 y ∂μ₁) μK₁ := by
  intro F E _ _ _ _ _ σ B a b G G₁ H H' hC e' hE X om om' om₁ om₁' hT hT₁ ei ev hei hvac hfac K hK μK₁ μ₁ hμK hμ φ hφ
  classical
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  obtain ⟨_, _, _, _, _⟩ := idelesAt_facts E (evFin F B.v₁)
  haveI : BorelSpace (UA σ G.V'.J) := ⟨rfl⟩
  haveI : IsFiniteMeasure μK₁ := ⟨by rw [hμK.2]; exact ENNReal.one_lt_top⟩
  obtain ⟨hlcK, hfinK⟩ := GlobalTheory.T.locally_constant_max_compact_action B G X om om' hT K hK φ hφ
  let Fl : ((Fin (b + 2) × Fin (a + (b + 2)) → Fv F B.v₁) → ℂ) → (AE F E)ˣ → (Fin b × Fin (a + b) → Fv F B.v₁) → ℂ :=
    fun ψ₀ l => ev B.v₁ (locOp B.v₁ (G.M'.co.rho B.ψ (partFin B.v₁ (shiftB σ H H' l))) ψ₀)
  have hcomp : Continuous fun l : idelesAt E (evFin F B.v₁) => compFin F E B.v₁ l.1.1 :=
    Units.continuous_val.comp ((GlobalTheory.Doubling.continuous_unitFin B.v₁).comp continuous_subtype_val)
  have hFl : ∀ ψ₀ ∈ SB (Fin (b + 2) × Fin (a + (b + 2)) → Fv F B.v₁), (Set.range (Fl ψ₀)).Finite ∧
      (∃ C : Set (Fv F B.v₁ ⊗[F] E), IsCompact C ∧ ∀ l : (AE F E)ˣ, compFin F E B.v₁ l.1 ∉ C → Fl ψ₀ l = 0) ∧
      IsLocallyConstant (fun l : idelesAt E (evFin F B.v₁) => Fl ψ₀ l.1) := by
    intro ψ₀ hψ₀
    obtain ⟨Λ, hΛ, hinv⟩ := GlobalTheory.T.config_b_schwartz_bruhat_lattice B G G₁ H H' hC X om om' hT ψ₀ hψ₀
    obtain ⟨C, hCc, h0⟩ := GlobalTheory.T.config_b_eigen_triple_relation B G G₁ H H' hC e' hE X om om' om₁ om₁' hT hT₁ ei ev hei hvac hfac ψ₀ hψ₀
    have hinv' : ∀ l l' : (AE F E)ˣ, compFin F E B.v₁ l'.1 - compFin F E B.v₁ l.1 ∈ Λ → Fl ψ₀ l' = Fl ψ₀ l :=
      fun l l' h => by simp only [Fl]; rw [hinv l l' h]
    refine ⟨finite_range_of_lattice (Fl ψ₀) (fun l => compFin F E B.v₁ l.1) Λ hΛ C hCc hinv' h0, ⟨C, hCc, h0⟩, ?_⟩
    refine (IsLocallyConstant.iff_eventually_eq _).2 fun x => ?_
    have ho : IsOpen {l : idelesAt E (evFin F B.v₁) | compFin F E B.v₁ l.1.1 - compFin F E B.v₁ x.1.1 ∈ Λ} :=
      hΛ.preimage (hcomp.sub continuous_const)
    filter_upwards [ho.mem_nhds (by simp [Λ.zero_mem])] with l hl
    exact hinv' x.1 l.1 hl
  have hSB : ∀ ψ₀ ∈ Set.range (fun k : KAt K (evFin F B.v₁) => locOp B.v₁ (om' (k.1, 1)) φ),
      ψ₀ ∈ SB (Fin (b + 2) × Fin (a + (b + 2)) → Fv F B.v₁) := by
    rintro _ ⟨k, rfl⟩
    exact locOp_mem _ _ _
  set S := ⋃ ψ₀ ∈ Set.range (fun k : KAt K (evFin F B.v₁) => locOp B.v₁ (om' (k.1, 1)) φ), Set.range (Fl ψ₀) with hS
  have hSfin : S.Finite := hfinK.biUnion fun ψ₀ h => (hFl ψ₀ (hSB ψ₀ h)).1
  have hν : Continuous fun x : (AE F E)ˣ => (X.ν x : ℂ) := by
    have h1 : Continuous X.ν := hT.chars.heckeα.1.div' hT.chars.heckeβ.1
    exact continuous_subtype_val.comp h1
  have hz : 1 ≤ (a - (b + 2)) / 2 + 1 := Nat.le_add_left 1 _
  have hint : ∀ y, ∀ ψ₀ ∈ SB (Fin (b + 2) × Fin (a + (b + 2)) → Fv F B.v₁),
      Integrable (fun l : idelesAt E (evFin F B.v₁) => Fl ψ₀ l.1 y * (X.ν l.1 : ℂ) *
        ((GlobalTheory.Doubling.absE F E l.1 : ℝ) : ℂ) ^ ((a - (b + 2)) / 2 + 1)) μ₁ := by
    intro y ψ₀ hψ₀
    obtain ⟨hfin, ⟨C, hCc, h0⟩, hlc⟩ := hFl ψ₀ hψ₀
    obtain ⟨M, hM⟩ : ∃ M, ∀ l, ‖Fl ψ₀ l y‖ ≤ M := by
      obtain ⟨M, hM⟩ := (hfin.image (fun g => ‖g y‖)).bddAbove
      exact ⟨M, fun l => hM ⟨_, ⟨l, rfl⟩, rfl⟩⟩
    have hL := (GlobalTheory.T.integrable_power_norm_compact B.v₁ μ₁ hμ C hCc _ hz).const_mul M
    refine hL.mono' ?_ (Eventually.of_forall fun l => ?_)
    · refine Continuous.aestronglyMeasurable ?_
      refine (((hlc.comp fun g => g y).continuous.mul (hν.comp continuous_subtype_val)).mul ?_)
      exact ((Complex.continuous_ofReal.comp (NNReal.continuous_coe.comp
        (GlobalTheory.Doubling.continuous_absE.comp continuous_subtype_val))).pow _)
    · by_cases hl : compFin F E B.v₁ l.1.1 ∈ C
      · rw [Set.indicator_of_mem hl, norm_mul, norm_mul, Circle.norm_coe, mul_one, norm_pow, Complex.norm_real,
          Real.norm_of_nonneg (NNReal.coe_nonneg _)]
        exact mul_le_mul_of_nonneg_right (hM l.1) (pow_nonneg (NNReal.coe_nonneg _) _)
      · rw [h0 _ hl, Set.indicator_of_notMem hl]
        simp
  refine ⟨Submodule.span ℂ S, FiniteDimensional.span_of_finite ℂ hSfin, ?_, fun k l => ?_, fun y => ⟨fun k => ?_, ?_⟩⟩
  · rw [Submodule.span_le]
    intro f hf
    obtain ⟨ψ₀, hψ₀, ⟨l, rfl⟩⟩ := Set.mem_iUnion₂.1 hf
    have h : Fl ψ₀ l ∈ (SB _).map (ev B.v₁) := Submodule.mem_map_of_mem (locOp_mem _ _ _)
    rw [(hvac B.v₁).2] at h
    exact h
  · have e : (fun y => coneFinInt B G.M' om' B.v₁ (ev B.v₁) (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) φ k.1 l.1 y) =
        ((X.ν l.1 : ℂ) * ((GlobalTheory.Doubling.absE F E l.1 : ℝ) : ℂ) ^ ((a - (b + 2)) / 2 + 1)) •
          Fl (locOp B.v₁ (om' (k.1, 1)) φ) l.1 := by
      funext y
      simp only [coneFinInt, Pi.smul_apply, smul_eq_mul, Fl]
      ring
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_iUnion₂.2 ⟨_, ⟨k, rfl⟩, ⟨l.1, rfl⟩⟩))
  · exact hint y _ (locOp_mem _ _ _)
  · let h : ((Fin (b + 2) × Fin (a + (b + 2)) → Fv F B.v₁) → ℂ) → ℂ := fun ψ₀ =>
      ∫ l : idelesAt E (evFin F B.v₁), Fl ψ₀ l.1 y * (X.ν l.1 : ℂ) *
        ((GlobalTheory.Doubling.absE F E l.1 : ℝ) : ℂ) ^ ((a - (b + 2)) / 2 + 1) ∂μ₁
    have hlc := hlcK.comp h
    obtain ⟨M, hM⟩ := ((hfinK.image h).image norm).bddAbove
    refine (integrable_const M).mono' hlc.continuous.aestronglyMeasurable (Eventually.of_forall fun k => ?_)
    exact hM ⟨_, ⟨_, ⟨k, rfl⟩, rfl⟩, rfl⟩

end GlobalTheory.ConeSoB
