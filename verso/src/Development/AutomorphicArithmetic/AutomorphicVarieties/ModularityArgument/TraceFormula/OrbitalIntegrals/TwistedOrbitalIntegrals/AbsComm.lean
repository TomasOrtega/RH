import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.QuotFubini

open MeasureTheory Topology PositivityTheory.Rg.Tf.Loc UpperTheory.V.Z.Tf.Orb

/- English proof (translation)
Introduce `hF hR hP G _ _ _ _ _ _ _ _ μG hμG r1 r2 θ hθ l hl hθl δ hD μ hμ hi a b a1 a2 b1 b2`. Establish `hcl : IsClosed (twCent θ δ : Set G)` using `isClosed_eq ((continuous_inv.mul continuous_const).mul hθ) continuous_const`. Use `haveI : LocallyCompactSpace (twCent θ δ) := hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace`. Use `haveI : SecondCountableTopology (twCent θ δ) := TopologicalSpace.Subtype.secondCountableTopology _`. Use `haveI : SigmaCompactSpace (twCent θ δ) := inferInstance`.

Use `haveI : SigmaFinite μ := inferInstance`. Establish `hmp` using `hP G μG hμG θ hθ l hl hθl`. Establish `hθθ : ∀ x, (θ ^ (l - 1)) (θ x) = x` using `fun x => by`. Rewrite using `[← pow_succ_apply, Nat.sub_add_cancel (Nat.pos_of_ne_zero hl), hθl]`. Both sides reduce to the same expression.

Establish `hθθ' : ∀ x, θ ((θ ^ (l - 1)) x) = x` using `fun x => by`. Rewrite using `[← pow_succ_apply', Nat.sub_add_cancel (Nat.pos_of_ne_zero hl), hθl]`. Both sides reduce to the same expression. Establish `hpc : ∀ m : ℕ, Continuous (θ ^ m : Monoid.End G)` using `fun m => by`. Proceed by induction on `m with`.

Consider the case `zero => exact continuous_id`. Consider the case `succ m ih => exact (ih.comp hθ).congr fun x => (pow_succ_apply θ m x).symm`. Set `e : G ≃ₜ G` to `⟨⟨θ, (θ ^ (l - 1) : Monoid.End G), hθθ, hθθ'⟩, hθ, hpc _⟩`. Establish `hinv : ∀ h ∈ twCent θ δ, ∀ g, twConj θ (h * g) δ = twConj θ g δ` using `fun h hh g => twConj_mul_left θ δ hh g`. Establish `hct : Continuous fun g => twConj θ g δ` using `(continuous_inv.mul continuous_const).mul hθ`.

Take `⟨D1, d1, e1⟩` from `hD _ (a2.isCompact.mul b2.isCompact)`. Take `⟨D2, d2, e2⟩` from `hD _ (b2.isCompact.mul (a2.isCompact.image hθ))`. Establish `k1` using `hF G μG hμG _ hcl μ hμ hi (fun y g => a y * b (y⁻¹ * twConj θ g δ)) ((a1.comp continuous_fst).mul (b1.comp (continuous_fst.inv.mul (hct.comp continuous_snd)))) (fun y h hh g => by simp only [hinv h hh]) ⟨_, D1, a2.isCompact, d1, fun y g hne => ⟨subset_tsupport _ (left_ne_zero_of_ …`. Establish `k2` using `hF G μG hμG _ hcl μ hμ hi (fun y g => a y * b (twConj θ g δ * (θ y)⁻¹)) ((a1.comp continuous_fst).mul (b1.comp ((hct.comp continuous_snd).mul (hθ.comp continuous_fst).inv))) (fun y h hh g => by simp only [hinv h hh]) ⟨_, D2, a2.isCompact, d2, fun y g hne => ⟨subset_tsupport _ (le …`. Establish `k3 : ∀ x, conv μG b (fun x => a ((θ ^ (l - 1)) x)) x = ∫ y, a y * b (x * (θ y)⁻¹) ∂μG` using `fun x => by`.

Establish `s1` using `hmp.integral_comp e.measurableEmbedding fun w => a ((θ ^ (l - 1)) w) * b (x * w⁻¹)`. Simplify using `only [hθθ] at s1`. Rewrite using `[s1, ← integral_inv_eq_self, ← integral_mul_left_eq_self _ x⁻¹, conv]`. Use `integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)` and prove the remaining obligations. Simplify using `[mul_comm]`.

Rewrite using `[twOrbIntegralC, twOrbIntegralC]`. Simplify using `only [k3]`. Rewrite using `[k2]`. Use `k1.trans (integral_congr_ae (Filter.Eventually.of_forall fun y => ?_))` and prove the remaining obligations. Establish `k4` using `hR G μG hμG r1 _ μ inferInstance hi (fun g => a y * b (y⁻¹ * twConj θ g δ)) (continuous_const.mul (b1.comp (continuous_const.mul hct))).measurable (fun h hh g => by simp only [hinv h hh]) y⁻¹`.

Use `k4.symm.trans ?_` and prove the remaining obligations. Use `congr 1`. Use function extensionality and compare the values at `g`. Simplify using `[twConj, mul_assoc]`.
-/
theorem UpperTheory.V.Z.Tf.Orb.absComm :
    UpperTheory.V.Z.Tf.Orb.QuotFubini → UpperTheory.V.Z.Tf.Orb.QuotRight → UpperTheory.V.Z.Tf.Orb.FinPres → UpperTheory.V.Z.Tf.Orb.AbsComm := by
  intro hF hR hP G _ _ _ _ _ _ _ _ μG hμG r1 r2 θ hθ l hl hθl δ hD μ hμ hi a b a1 a2 b1 b2
  have hcl : IsClosed (twCent θ δ : Set G) :=
    isClosed_eq ((continuous_inv.mul continuous_const).mul hθ) continuous_const
  haveI : LocallyCompactSpace (twCent θ δ) := hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology (twCent θ δ) := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : SigmaCompactSpace (twCent θ δ) := inferInstance
  haveI : SigmaFinite μ := inferInstance
  have hmp := hP G μG hμG θ hθ l hl hθl
  have hθθ : ∀ x, (θ ^ (l - 1)) (θ x) = x := fun x => by
    rw [← pow_succ_apply, Nat.sub_add_cancel (Nat.pos_of_ne_zero hl), hθl]; rfl
  have hθθ' : ∀ x, θ ((θ ^ (l - 1)) x) = x := fun x => by
    rw [← pow_succ_apply', Nat.sub_add_cancel (Nat.pos_of_ne_zero hl), hθl]; rfl
  have hpc : ∀ m : ℕ, Continuous (θ ^ m : Monoid.End G) := fun m => by
    induction m with
    | zero => exact continuous_id
    | succ m ih => exact (ih.comp hθ).congr fun x => (pow_succ_apply θ m x).symm
  let e : G ≃ₜ G := ⟨⟨θ, (θ ^ (l - 1) : Monoid.End G), hθθ, hθθ'⟩, hθ, hpc _⟩
  have hinv : ∀ h ∈ twCent θ δ, ∀ g, twConj θ (h * g) δ = twConj θ g δ := fun h hh g => twConj_mul_left θ δ hh g
  have hct : Continuous fun g => twConj θ g δ := (continuous_inv.mul continuous_const).mul hθ
  obtain ⟨D1, d1, e1⟩ := hD _ (a2.isCompact.mul b2.isCompact)
  obtain ⟨D2, d2, e2⟩ := hD _ (b2.isCompact.mul (a2.isCompact.image hθ))
  have k1 := hF G μG hμG _ hcl μ hμ hi (fun y g => a y * b (y⁻¹ * twConj θ g δ))
    ((a1.comp continuous_fst).mul (b1.comp (continuous_fst.inv.mul (hct.comp continuous_snd))))
    (fun y h hh g => by simp only [hinv h hh]) ⟨_, D1, a2.isCompact, d1, fun y g hne =>
      ⟨subset_tsupport _ (left_ne_zero_of_mul hne), e1 g ⟨y, subset_tsupport _ (left_ne_zero_of_mul hne), _,
        subset_tsupport _ (right_ne_zero_of_mul hne), by simp⟩⟩⟩
  have k2 := hF G μG hμG _ hcl μ hμ hi (fun y g => a y * b (twConj θ g δ * (θ y)⁻¹))
    ((a1.comp continuous_fst).mul (b1.comp ((hct.comp continuous_snd).mul (hθ.comp continuous_fst).inv)))
    (fun y h hh g => by simp only [hinv h hh]) ⟨_, D2, a2.isCompact, d2, fun y g hne =>
      ⟨subset_tsupport _ (left_ne_zero_of_mul hne), e2 g ⟨_, subset_tsupport _ (right_ne_zero_of_mul hne), θ y,
        ⟨y, subset_tsupport _ (left_ne_zero_of_mul hne), rfl⟩, by simp⟩⟩⟩
  have k3 : ∀ x, conv μG b (fun x => a ((θ ^ (l - 1)) x)) x = ∫ y, a y * b (x * (θ y)⁻¹) ∂μG := fun x => by
    have s1 := hmp.integral_comp e.measurableEmbedding fun w => a ((θ ^ (l - 1)) w) * b (x * w⁻¹)
    simp only [hθθ] at s1
    rw [s1, ← integral_inv_eq_self, ← integral_mul_left_eq_self _ x⁻¹, conv]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp [mul_comm]
  rw [twOrbIntegralC, twOrbIntegralC]
  simp only [k3]
  rw [k2]
  refine k1.trans (integral_congr_ae (Filter.Eventually.of_forall fun y => ?_))
  have k4 := hR G μG hμG r1 _ μ inferInstance hi (fun g => a y * b (y⁻¹ * twConj θ g δ))
    (continuous_const.mul (b1.comp (continuous_const.mul hct))).measurable (fun h hh g => by simp only [hinv h hh]) y⁻¹
  refine k4.symm.trans ?_
  congr 1
  funext g
  simp [twConj, mul_assoc]
