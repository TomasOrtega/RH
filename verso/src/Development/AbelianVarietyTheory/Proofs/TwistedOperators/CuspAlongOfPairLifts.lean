import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasInfExpOfOrder
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowestKTypesJointShapeBlockUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowestKTypesJointShapeBlockInUnitarySStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealThetaRuleExchangePairMembersStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SignedUnitaryGroupCompatStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesModelConjugateTransferStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorFrameChangeSameCartanStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermitianAdjointLawsStandardCharacterStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsNegatedSpaceDiscreteSeriesModelTransportStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsConjWeilDatumExchangedPairStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorsConjAdjointPullbackBijectionStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealThetaIntertwinerAdjointIsRealThetaIntertwineStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LowerTowerLiftsVanishOnFockStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LowerTowerLiftsVanishOfVanishOnFockStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftsCuspidalOfLowerTowerLiftsVanishStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairThetaLiftFactorsThroughIntertwinerStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContragredientThetaParamsAddBlockArrowStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContragredientThetaParamsRemoveBlockArrowStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContragredientThetaParamsColumnArrowsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContragredientThetaParamsLastRowArrowsStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open MeasureTheory Matrix GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Grid
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PairLift

/- English proof (translation)
Establish `far : ∀ {t : ℕ} {al be ga de : List ℚ}, GlobalTheory.SignedHC.FarFrom aT (((t : ℚ) + 3) / 2) (signed (al ++ be) (ga ++ de) aT) → ¬ ∃ a, lamA al be ga de a = ((t : ℚ) + 1) / 2`. Introduce and unpack `t al be ga de hF ⟨a, ha⟩`. Establish `hm : (((t : ℚ) + 1) / 2, a.isLeft) ∈ GlobalTheory.SignedHC.ofIx (lamA al be ga de)` using `Finset.mem_image.2 ⟨a, Finset.mem_univ _, by rw [ha]⟩`. Rewrite `hm` using `[lamA, GlobalTheory.SignedHC.mem_ofIx_ofBlocks (by simp) (by simp)]`. Establish `: ∃ s, (((t : ℚ) + 1) / 2 + aT, s) ∈ signed (al ++ be) (ga ++ de) aT`.

Break down `hm with ⟨h1, -⟩ | ⟨h1, -⟩` into its components or cases. Conclude with `⟨true, Finset.mem_union_left _ (List.mem_toFinset.2 (List.mem_map.2 ⟨_, h1, rfl⟩))⟩`. Conclude with `⟨false, Finset.mem_union_right _ (List.mem_toFinset.2 (List.mem_map.2 ⟨_, h1, rfl⟩))⟩`. Use `hF _ (GlobalTheory.SignedHC.mem_entries.2 this)` as an intermediate fact. Rewrite `this` using `[add_sub_cancel_right, abs_of_nonneg (by positivity)]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hb : ∀ t, (block t).length = t` using `fun t => by simp [block]`. Take `⟨t, P, P', e, e', ⟨⟨al, be, ga, de, rfl, ⟨hd, rfl⟩ | ⟨hd, rfl⟩⟩, hF⟩ | ⟨al, be, ga, de, rfl, ⟨hd, rfl⟩ | ⟨hd, rfl⟩⟩⟩` from `h`. Use `all_goals`. Establish `ht` using `hd.1.1`.

Establish `hn` using `hd.1.2.1`. Take `⟨-, p1, p2, -⟩` from `GlobalTheory.T.lowest_kTypes_jointShape_block_unitary t al be ga de hd.1`. Take `⟨-, p3, -⟩` from `GlobalTheory.T.lowestKTypes_jointShape_block_in_unitaryS t al be ga de hd.1`. Conclude with `⟨_, _, _, _, _, _, _, _, by simp, by simp, by simp [hb]; omega, by simp, ⟨by omega, by omega, p1, p2, (h3.1 t al be ga de hd).2.1, (h3.1 t al be ga de hd).2.2, h5.1 t al be ga de hd (Or.inl (far hF))⟩, e, e'⟩`. Conclude with `⟨_, _, _, _, _, _, _, _, by simp, by simp, by simp, by simp [hb]; omega, ⟨by omega, by omega, p1, p3, (h3.2 t al be ga de hd).2.1, (h3.2 t al be ga de hd).2.2, h5.2 t al be ga de hd (Or.inl (far hF))⟩, e, e'⟩`.

Establish `sw` using `GlobalTheory.T.realThetaRule_exchange_pair_members X _ _ _ _ (lamA al be ga de) (lamA' t al be ga de)`. Conclude with `⟨_, _, _, _, _, _, _, _, by simp [hb]; omega, by simp, by simp, by simp, ⟨by omega, by omega, p2, p1, sw.1 (h3.1 t al be ga de hd).1, sw.2.1 (h3.1 t al be ga de hd).2.2, sw.2.2 (h4.1 t al be ga de hd)⟩, e, e'⟩`. Establish `sw` using `GlobalTheory.T.realThetaRule_exchange_pair_members X _ _ _ _ (lamA al be ga de) (lamM' t al be ga de)`. Conclude with `⟨_, _, _, _, _, _, _, _, by simp, by simp [hb]; omega, by simp, by simp, ⟨by omega, by omega, p3, p1, sw.1 (h3.2 t al be ga de hd).1, sw.2.1 (h3.2 t al be ga de hd).2.2, sw.2.2 (h4.2 t al be ga de hd)⟩, e, e'⟩`.
-/
theorem rulePar_of_pairPar {X : ProvA} (h3 : Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisUpDownLine X) (h4 : Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisFourth X) (h5 : Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisFifth X)
    {S S' : SPar} {aS aT : ℚ} (h : PairPar S S' aS aT) : RulePar X S S' aS aT := by
  have far : ∀ {t : ℕ} {al be ga de : List ℚ}, GlobalTheory.SignedHC.FarFrom aT (((t : ℚ) + 3) / 2) (signed (al ++ be) (ga ++ de) aT) →
      ¬ ∃ a, lamA al be ga de a = ((t : ℚ) + 1) / 2 := by
    rintro t al be ga de hF ⟨a, ha⟩
    have hm : (((t : ℚ) + 1) / 2, a.isLeft) ∈ GlobalTheory.SignedHC.ofIx (lamA al be ga de) :=
      Finset.mem_image.2 ⟨a, Finset.mem_univ _, by rw [ha]⟩
    rw [lamA, GlobalTheory.SignedHC.mem_ofIx_ofBlocks (by simp) (by simp)] at hm
    have : ∃ s, (((t : ℚ) + 1) / 2 + aT, s) ∈ signed (al ++ be) (ga ++ de) aT := by
      rcases hm with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact ⟨true, Finset.mem_union_left _ (List.mem_toFinset.2 (List.mem_map.2 ⟨_, h1, rfl⟩))⟩
      · exact ⟨false, Finset.mem_union_right _ (List.mem_toFinset.2 (List.mem_map.2 ⟨_, h1, rfl⟩))⟩
    have := hF _ (GlobalTheory.SignedHC.mem_entries.2 this)
    rw [add_sub_cancel_right, abs_of_nonneg (by positivity)] at this
    linarith
  have hb : ∀ t, (block t).length = t := fun t => by simp [block]
  obtain ⟨t, P, P', e, e', ⟨⟨al, be, ga, de, rfl, ⟨hd, rfl⟩ | ⟨hd, rfl⟩⟩, hF⟩ | ⟨al, be, ga, de, rfl, ⟨hd, rfl⟩ | ⟨hd, rfl⟩⟩⟩ := h
  all_goals
    have ht := hd.1.1
    have hn := hd.1.2.1
    obtain ⟨-, p1, p2, -⟩ := GlobalTheory.T.lowest_kTypes_jointShape_block_unitary t al be ga de hd.1
    obtain ⟨-, p3, -⟩ := GlobalTheory.T.lowestKTypes_jointShape_block_in_unitaryS t al be ga de hd.1
  · exact ⟨_, _, _, _, _, _, _, _, by simp, by simp, by simp [hb]; omega, by simp,
      ⟨by omega, by omega, p1, p2, (h3.1 t al be ga de hd).2.1, (h3.1 t al be ga de hd).2.2,
        h5.1 t al be ga de hd (Or.inl (far hF))⟩, e, e'⟩
  · exact ⟨_, _, _, _, _, _, _, _, by simp, by simp, by simp, by simp [hb]; omega,
      ⟨by omega, by omega, p1, p3, (h3.2 t al be ga de hd).2.1, (h3.2 t al be ga de hd).2.2,
        h5.2 t al be ga de hd (Or.inl (far hF))⟩, e, e'⟩
  · have sw := GlobalTheory.T.realThetaRule_exchange_pair_members X _ _ _ _ (lamA al be ga de) (lamA' t al be ga de)
    exact ⟨_, _, _, _, _, _, _, _, by simp [hb]; omega, by simp, by simp, by simp,
      ⟨by omega, by omega, p2, p1, sw.1 (h3.1 t al be ga de hd).1, sw.2.1 (h3.1 t al be ga de hd).2.2,
        sw.2.2 (h4.1 t al be ga de hd)⟩, e, e'⟩
  · have sw := GlobalTheory.T.realThetaRule_exchange_pair_members X _ _ _ _ (lamA al be ga de) (lamM' t al be ga de)
    exact ⟨_, _, _, _, _, _, _, _, by simp, by simp [hb]; omega, by simp, by simp,
      ⟨by omega, by omega, p3, p1, sw.1 (h3.2 t al be ga de hd).1, sw.2.1 (h3.2 t al be ga de hd).2.2,
        sw.2.2 (h4.2 t al be ga de hd)⟩, e, e'⟩

def IdOrConj (σ : ℂ →+* ℂ) : Prop := σ = RingHom.id ℂ ∨ σ = starRingEnd ℂ

/- English proof (translation)
Apply the tactic sequence `rcases h with rfl | rfl <;> simp`.
-/
theorem IdOrConj.invol {σ : ℂ →+* ℂ} (h : IdOrConj σ) (z : ℂ) : σ (σ z) = z := by
  rcases h with rfl | rfl <;> simp

/- English proof (translation)
Apply the tactic sequence `rcases h with rfl | rfl <;> simp`.
-/
theorem IdOrConj.norm {σ : ℂ →+* ℂ} (h : IdOrConj σ) (z : ℂ) : ‖σ z‖ = ‖z‖ := by
  rcases h with rfl | rfl <;> simp

/- English proof (translation)
Break down `h with rfl | rfl` into its components or cases. Conclude with `hf`. Simplify using `using hf.star`.
-/
theorem IdOrConj.deriv {σ : ℂ →+* ℂ} (h : IdOrConj σ) {f : ℝ → ℂ} {a : ℂ} (hf : HasDerivAt (fun t => σ (f t)) (σ a) 0) :
    HasDerivAt f a 0 := by
  rcases h with rfl | rfl
  · exact hf
  · simpa using hf.star

/- English proof (translation)
Break down `h with rfl | rfl` into its components or cases. Conclude with `⟨id, rfl⟩`. Conclude with `⟨fun hf => Complex.conjCLE.integrable_comp_iff.1 hf, integral_conj⟩`.
-/
theorem IdOrConj.integral {σ : ℂ →+* ℂ} (h : IdOrConj σ) {G : Type} [MeasurableSpace G] (μ : Measure G) (f : G → ℂ) :
    (Integrable (fun g => σ (f g)) μ → Integrable f μ) ∧ ∫ g, σ (f g) ∂μ = σ (∫ g, f g ∂μ) := by
  rcases h with rfl | rfl
  · exact ⟨id, rfl⟩
  · exact ⟨fun hf => Complex.conjCLE.integrable_comp_iff.1 hf, integral_conj⟩

variable {D : D7} {θ : InfFam D}

section Transport

variable {A B : HSp D} {SA SB SA₁ SB₁ : D.what₂.Tau → SPar} {MA : DSModel A SA} {MB : DSModel B SB} {εA εB : Bool}
  {MA₁ : DSModel (sgn εA A) SA₁} {MB₁ : DSModel (sgn εB B) SB₁} {σ : ℂ →+* ℂ} {κA : SmT MA₁ ≃+ SmT MA}
  {κB : SmT MB₁ ≃+ SmT MB}

/- English proof (translation)
Introduce `F hF`. Take `⟨ν₁, a, b, c⟩` from `(GlobalTheory.T.signedUnitaryGroup_compat D θ hθ εA A).meas ν 𝓕 hν h𝓕`. Take `⟨F₁, hF₁, e₁⟩` from `hA.mult F hF`. Take `⟨F₂, hF₂, e₂⟩` from `H ν₁ _ a b F₁ hF₁`. Take `⟨F', hF', e'⟩` from `hB.mult' F₂ hF₂`.

Use `⟨F', hF', fun p v h => ?_⟩` and prove the remaining obligations. Take `⟨v, rfl⟩` from `κA.surjective v`. Take `⟨h, rfl⟩` from `(ofSgn εB B).surjective h`. Take `⟨i1, i2⟩` from `e₂ (j p) v h`. Simplify using `only [hK, e₁, ← map_mul] at i1 i2`.

Take `⟨c1, c2⟩` from `c fun g => σ (K p (ofSgn εB B h) g * F (κA v) g)`. Take `⟨d1, d2⟩` from `hσ.integral (ν.restrict 𝓕) fun g => K p (ofSgn εB B h) g * F (κA v) g`. Use `⟨d1 (c1.1 i1), σ.injective ?_⟩` and prove the remaining obligations. Rewrite using `[← d2, ← c2, i2, e', hI]`.
-/
theorem LiftsM.transport (hθ : IsInfFam θ) (hσ : IdOrConj σ) (hA : ModelTr σ εA θ MA₁ MA κA) (hB : ModelTr σ εB θ MB₁ MB κB)
    {P P₁ : Type} (j : P → P₁) {K : P → GA D B → GA D A → ℂ} {K₁ : P₁ → GA D (sgn εB B) → GA D (sgn εA A) → ℂ}
    {It : P → SmT MA → SmT MB} {It₁ : P₁ → SmT MA₁ → SmT MB₁}
    (hK : ∀ p h g, K₁ (j p) h g = σ (K p (ofSgn εB B h) (ofSgn εA A g))) (hI : ∀ p v, κB (It₁ (j p) v) = It p (κA v))
    {ν : Measure (GA D A)} {𝓕 : Set (GA D A)} (hν : ν.IsHaarMeasure) (h𝓕 : IsFundamentalDomain (GQ A) 𝓕 ν)
    (H : ∀ ν₁ 𝓕₁, ν₁.IsHaarMeasure → IsFundamentalDomain (GQ (sgn εA A)) 𝓕₁ ν₁ → LiftsM θ MA₁ MB₁ ν₁ 𝓕₁ K₁ It₁) :
    LiftsM θ MA MB ν 𝓕 K It := by
  intro F hF
  obtain ⟨ν₁, a, b, c⟩ := (GlobalTheory.T.signedUnitaryGroup_compat D θ hθ εA A).meas ν 𝓕 hν h𝓕
  obtain ⟨F₁, hF₁, e₁⟩ := hA.mult F hF
  obtain ⟨F₂, hF₂, e₂⟩ := H ν₁ _ a b F₁ hF₁
  obtain ⟨F', hF', e'⟩ := hB.mult' F₂ hF₂
  refine ⟨F', hF', fun p v h => ?_⟩
  obtain ⟨v, rfl⟩ := κA.surjective v
  obtain ⟨h, rfl⟩ := (ofSgn εB B).surjective h
  obtain ⟨i1, i2⟩ := e₂ (j p) v h
  simp only [hK, e₁, ← map_mul] at i1 i2
  obtain ⟨c1, c2⟩ := c fun g => σ (K p (ofSgn εB B h) g * F (κA v) g)
  obtain ⟨d1, d2⟩ := hσ.integral (ν.restrict 𝓕) fun g => K p (ofSgn εB B h) g * F (κA v) g
  refine ⟨d1 (c1.1 i1), σ.injective ?_⟩
  rw [← d2, ← c2, i2, e', hI]

/- English proof (translation)
Establish `lA` using `GlobalTheory.T.signedUnitaryGroup_compat D θ hθ εA A`. Establish `lB` using `GlobalTheory.T.signedUnitaryGroup_compat D θ hθ εB B`. Establish `inj : ∀ {f f' : Z → ℂ}, ((fun y => ρ (f (α y))) = fun y => ρ (f' (α y))) → f = f'` using `fun {f f'} h => by`. Use function extensionality and compare the values at `z`. Take `⟨y, rfl⟩` from `hα z`.

Conclude with `ρ.injective (congrFun h y)`. Use `⟨fun h0 => ?_, fun φ w => ?_, fun τ g hg φ φ' h v => ?_, fun τ Y hY φ φ' h v => ?_, fun τ g hg φ φ' v v' h h' => ?_, fun τ Y hY φ φ' v v' h h' => ?_⟩` and prove the remaining obligations. Take `⟨φ, hφ⟩` from `H.ne`. Use `hφ (LinearMap.ext fun v => ?_)` and prove the remaining obligations. Take `⟨v, rfl⟩` from `κA.surjective v`.

Rewrite using `[← hI, h0]`. Simplify using the standard rewrite rules. Take `⟨φ, rfl⟩` from `hj φ`. Take `⟨w', hw⟩` from `hB.ell w`. Take `⟨c, hc⟩` from `H.bdd φ w'`.

Use `⟨c, fun v => ?_⟩` and prove the remaining obligations. Take `⟨v', e1, e2⟩` from `hA.vec v`. Rewrite using `[hw, hσ.norm, hI, e1]`. Simplify `hc v'` using `only [e2]`. Take `⟨φ, rfl⟩` from `hj φ`.

Take `⟨φ', rfl⟩` from `hj φ'`. Rewrite `hg` using `[lB.grp]`. Rewrite `h` using `[hpt, hpt, hω, lB.atTau, map_one]`. Rewrite using `[hB.act τ g hg, hI, hI]`. Conclude with `H.eqK τ g hg φ φ' (inj h) _`.

Take `⟨φ, rfl⟩` from `hj φ`. Take `⟨φ', rfl⟩` from `hj φ'`. Rewrite `hY` using `[lB.lie]`. Rewrite using `[hB.der τ Y hY, hI, hI]`. Use `H.eqg τ Y hY φ φ' (fun z => ?_) _` and prove the remaining obligations.

Take `⟨y, rfl⟩` from `hα z`. Use `h y` as an intermediate fact. Simplify using `only [hpt, hω, oneP, lB.atTau, map_one] at this`. Conclude with `hρ.deriv this`. Take `⟨φ, rfl⟩` from `hj φ`.

Take `⟨φ', rfl⟩` from `hj φ'`. Rewrite `hg` using `[lA.grp]`. Rewrite `h` using `[hpt, hpt, hω, lA.atTau, map_one]`. Apply `κB.injective` to reduce the goal to its premises. Rewrite using `[hI, hI]`.

Conclude with `H.invK τ g hg φ φ' _ _ (inj h) ((hA.act τ g hg _ _).1 h')`. Take `⟨φ, rfl⟩` from `hj φ`. Take `⟨φ', rfl⟩` from `hj φ'`. Rewrite `hY` using `[lA.lie]`. Apply `κB.injective` to reduce the goal to its premises.

Rewrite using `[map_add, map_zero, hI, hI]`. Use `H.invg τ Y hY φ φ' _ _ (fun z => ?_) ((hA.der τ Y hY _ _).1 h')` and prove the remaining obligations. Take `⟨y, rfl⟩` from `hα z`. Use `h y` as an intermediate fact. Simplify using `only [hpt, hω, oneP, lA.atTau, map_one] at this`.

Conclude with `hρ.deriv this`.
-/
theorem IsIntwF.transport (hθ : IsInfFam θ) (hσ : IdOrConj σ) (hA : ModelTr σ εA θ MA₁ MA κA)
    (hB : ModelTr σ εB θ MB₁ MB κB) {Z P : Type} {ω : GA D B × GA D A →* Module.End ℂ (Z → ℂ)} {pt : P → Z → ℂ}
    {It : P → SmT MA →ₗ[ℂ] SmT MB} (H : IsIntwF θ MB MA ω pt It) {ρ : ℂ →+* ℂ} (hρ : IdOrConj ρ)
    {α : WO (sgn εB B) (sgn εA A) → Z} (hα : Function.Surjective α) {ω₁ : WRep (sgn εB B) (sgn εA A)}
    (hω : ∀ h g f, ω₁ (h, g) (fun y => ρ (f (α y))) = fun y => ρ (ω (ofSgn εB B h, ofSgn εA A g) f (α y)))
    {j : P → PolF D (sgn εA A).rank (sgn εB B).rank} (hj : Function.Surjective j)
    {pt₁ : PolF D (sgn εA A).rank (sgn εB B).rank → WO (sgn εB B) (sgn εA A) → ℂ}
    (hpt : ∀ p, pt₁ (j p) = fun y => ρ (pt p (α y)))
    {It₁ : PolF D (sgn εA A).rank (sgn εB B).rank →ₗ[ℂ] SmT MA₁ →ₗ[ℂ] SmT MB₁}
    (hI : ∀ p v, κB (It₁ (j p) v) = It p (κA v)) : IsItW θ MB₁ MA₁ ω₁ pt₁ It₁ := by
  have lA := GlobalTheory.T.signedUnitaryGroup_compat D θ hθ εA A
  have lB := GlobalTheory.T.signedUnitaryGroup_compat D θ hθ εB B
  have inj : ∀ {f f' : Z → ℂ}, ((fun y => ρ (f (α y))) = fun y => ρ (f' (α y))) → f = f' := fun {f f'} h => by
    funext z
    obtain ⟨y, rfl⟩ := hα z
    exact ρ.injective (congrFun h y)
  refine ⟨fun h0 => ?_, fun φ w => ?_, fun τ g hg φ φ' h v => ?_, fun τ Y hY φ φ' h v => ?_,
    fun τ g hg φ φ' v v' h h' => ?_, fun τ Y hY φ φ' v v' h h' => ?_⟩
  · obtain ⟨φ, hφ⟩ := H.ne
    refine hφ (LinearMap.ext fun v => ?_)
    obtain ⟨v, rfl⟩ := κA.surjective v
    rw [← hI, h0]
    simp
  · obtain ⟨φ, rfl⟩ := hj φ
    obtain ⟨w', hw⟩ := hB.ell w
    obtain ⟨c, hc⟩ := H.bdd φ w'
    refine ⟨c, fun v => ?_⟩
    obtain ⟨v', e1, e2⟩ := hA.vec v
    rw [hw, hσ.norm, hI, e1]
    simpa only [e2] using hc v'
  · obtain ⟨φ, rfl⟩ := hj φ
    obtain ⟨φ', rfl⟩ := hj φ'
    rw [lB.grp] at hg
    rw [hpt, hpt, hω, lB.atTau, map_one] at h
    rw [hB.act τ g hg, hI, hI]
    exact H.eqK τ g hg φ φ' (inj h) _
  · obtain ⟨φ, rfl⟩ := hj φ
    obtain ⟨φ', rfl⟩ := hj φ'
    rw [lB.lie] at hY
    rw [hB.der τ Y hY, hI, hI]
    refine H.eqg τ Y hY φ φ' (fun z => ?_) _
    obtain ⟨y, rfl⟩ := hα z
    have := h y
    simp only [hpt, hω, oneP, lB.atTau, map_one] at this
    exact hρ.deriv this
  · obtain ⟨φ, rfl⟩ := hj φ
    obtain ⟨φ', rfl⟩ := hj φ'
    rw [lA.grp] at hg
    rw [hpt, hpt, hω, lA.atTau, map_one] at h
    apply κB.injective
    rw [hI, hI]
    exact H.invK τ g hg φ φ' _ _ (inj h) ((hA.act τ g hg _ _).1 h')
  · obtain ⟨φ, rfl⟩ := hj φ
    obtain ⟨φ', rfl⟩ := hj φ'
    rw [lA.lie] at hY
    apply κB.injective
    rw [map_add, map_zero, hI, hI]
    refine H.invg τ Y hY φ φ' _ _ (fun z => ?_) ((hA.der τ Y hY _ _).1 h')
    obtain ⟨y, rfl⟩ := hα z
    have := h y
    simp only [hpt, hω, oneP, lA.atTau, map_one] at this
    exact hρ.deriv this

/- English proof (translation)
Establish `hs : ∀ (c : ℂ) x, κB.symm (σ c • x) = c • κB.symm x` using `fun c x => κB.injective (by rw [hB.smul, κB.apply_symm_apply, κB.apply_symm_apply])`. Conclude with `⟨LinearMap.mk₂ ℂ (fun p v => κB.symm (It p (κA v))) (fun p q v => by simp [h1]) (fun c p v => by simp only [h2, LinearMap.smul_apply, hs]) (fun p v w => by simp) (fun c p v => by simp only [hA.smul, map_smul, hs]), fun p v => κB.apply_symm_apply _⟩`.
-/
theorem exists_bilin (hσ : IdOrConj σ) (hA : ModelTr σ εA θ MA₁ MA κA) (hB : ModelTr σ εB θ MB₁ MB κB)
    {P₁ : Type} [AddCommGroup P₁] [Module ℂ P₁] (It : P₁ → SmT MA →ₗ[ℂ] SmT MB) (h1 : ∀ p q, It (p + q) = It p + It q)
    (h2 : ∀ (c : ℂ) p, It (c • p) = σ c • It p) :
    ∃ It₁ : P₁ →ₗ[ℂ] SmT MA₁ →ₗ[ℂ] SmT MB₁, ∀ p v, κB (It₁ p v) = It p (κA v) := by
  have hs : ∀ (c : ℂ) x, κB.symm (σ c • x) = c • κB.symm x := fun c x =>
    κB.injective (by rw [hB.smul, κB.apply_symm_apply, κB.apply_symm_apply])
  exact ⟨LinearMap.mk₂ ℂ (fun p v => κB.symm (It p (κA v))) (fun p q v => by simp [h1])
    (fun c p v => by simp only [h2, LinearMap.smul_apply, hs]) (fun p v w => by simp)
    (fun c p v => by simp only [hA.smul, map_smul, hs]), fun p v => κB.apply_symm_apply _⟩

end Transport

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun _ _ => rfl, fun _ => rfl, fun _ _ _ _ _ => Iff.rfl, fun _ _ _ _ _ => Iff.rfl, fun w => ⟨w, fun _ => rfl⟩, fun v => ⟨v, rfl, fun _ => rfl⟩, fun F h => ⟨F, h, fun _ _ => rfl⟩, fun F h => ⟨F, h, fun _ _ => rfl⟩⟩`.
-/
theorem ModelTr.refl {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) :
    ModelTr (RingHom.id ℂ) false θ (V := V) (S₁ := S) M M (AddEquiv.refl _) :=
  ⟨fun _ _ => rfl, fun _ => rfl, fun _ _ _ _ _ => Iff.rfl, fun _ _ _ _ _ => Iff.rfl, fun w => ⟨w, fun _ => rfl⟩,
    fun v => ⟨v, rfl, fun _ => rfl⟩, fun F h => ⟨F, h, fun _ _ => rfl⟩, fun F h => ⟨F, h, fun _ _ => rfl⟩⟩

/- English proof (translation)
Take `⟨N, κ, h⟩` from `GlobalTheory.T.exists_negatedSpace_discreteSeriesModelTransport D θ hθ V S M`. Take `⟨M₁, κ', h'⟩` from `GlobalTheory.T.discrete_series_model_conjugate_transfer D θ hθ (sgn true V) _ N`. Establish `l` using `GlobalTheory.T.signedUnitaryGroup_compat D θ hθ true V`. Use `⟨M₁, κ'.trans κ, fun c x => ?_, fun τ => (h'.cart τ).trans (h.cart τ), fun τ g hg x y => ?_, fun τ Y hY x y => ?_, fun w => ?_, fun v => ?_, fun F hF => ?_, fun F hF => ?_⟩` and prove the remaining obligations. Conclude with `(congrArg κ (h'.smul c x)).trans (h.smul _ _)`.

Conclude with `(h'.act τ g (by rwa [l.grp]) x y).trans (h.act τ g hg _ _)`. Conclude with `(h'.der τ Y (by rwa [l.lie]) x y).trans (h.der τ Y hY _ _)`. Take `⟨w', e'⟩` from `h'.ell w`. Take `⟨w'', e⟩` from `h.ell w'`. Conclude with `⟨w'', fun x => (e' x).trans (congrArg _ (e _))⟩`.

Take `⟨v', e1, e2⟩` from `h'.vec v`. Take `⟨v'', e3, e4⟩` from `h.vec v'`. Conclude with `⟨v'', (congrArg κ e1).trans e3, fun τ => (e4 τ).trans (e2 τ)⟩`. Take `⟨F', a, b⟩` from `h.mult F hF`. Take `⟨F'', c, d⟩` from `h'.mult F' a`.

Conclude with `⟨F'', c, fun x g => (d x g).trans (congrArg _ (b _ _))⟩`. Take `⟨F', a, b⟩` from `h'.mult' F hF`. Take `⟨F'', c, d⟩` from `h.mult' F' a`. Conclude with `⟨F'', c, fun x g => (b x g).trans (congrArg _ (d _ _))⟩`.
-/
theorem exists_conj_neg (hθ : IsInfFam θ) {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) :
    ∃ (M₁ : DSModel (sgn true V) fun τ => dualPar (GlobalTheory.SignedHC.flip (S τ))) (κ : SmT M₁ ≃+ SmT M),
      ModelTr (starRingEnd ℂ) true θ M₁ M κ := by
  obtain ⟨N, κ, h⟩ := GlobalTheory.T.exists_negatedSpace_discreteSeriesModelTransport D θ hθ V S M
  obtain ⟨M₁, κ', h'⟩ := GlobalTheory.T.discrete_series_model_conjugate_transfer D θ hθ (sgn true V) _ N
  have l := GlobalTheory.T.signedUnitaryGroup_compat D θ hθ true V
  refine ⟨M₁, κ'.trans κ, fun c x => ?_, fun τ => (h'.cart τ).trans (h.cart τ), fun τ g hg x y => ?_, fun τ Y hY x y => ?_,
    fun w => ?_, fun v => ?_, fun F hF => ?_, fun F hF => ?_⟩
  · exact (congrArg κ (h'.smul c x)).trans (h.smul _ _)
  · exact (h'.act τ g (by rwa [l.grp]) x y).trans (h.act τ g hg _ _)
  · exact (h'.der τ Y (by rwa [l.lie]) x y).trans (h.der τ Y hY _ _)
  · obtain ⟨w', e'⟩ := h'.ell w
    obtain ⟨w'', e⟩ := h.ell w'
    exact ⟨w'', fun x => (e' x).trans (congrArg _ (e _))⟩
  · obtain ⟨v', e1, e2⟩ := h'.vec v
    obtain ⟨v'', e3, e4⟩ := h.vec v'
    exact ⟨v'', (congrArg κ e1).trans e3, fun τ => (e4 τ).trans (e2 τ)⟩
  · obtain ⟨F', a, b⟩ := h.mult F hF
    obtain ⟨F'', c, d⟩ := h'.mult F' a
    exact ⟨F'', c, fun x g => (d x g).trans (congrArg _ (b _ _))⟩
  · obtain ⟨F', a, b⟩ := h'.mult' F hF
    obtain ⟨F'', c, d⟩ := h.mult' F' a
    exact ⟨F'', c, fun x g => (b x g).trans (congrArg _ (d _ _))⟩

/- English proof (translation)
Take `⟨It₁, hI⟩` from `exists_bilin hσ hA hB (fun p => It (j.symm p)) h1 h2`. Establish `hI' : ∀ p v, κB (It₁ (j p) v) = It p (κA v)` using `fun p v => by rw [hI, j.symm_apply_apply]`. Establish `hv : IsVacVec ψ θ MB₁ MA₁ fun y => ρ (f₀ (α y))` using `⟨(hpt f₀ hf₀).1.1, fun h => h0 (funext fun z => by`. Take `⟨y, rfl⟩` from `hα z`. Conclude with `ρ.injective ((congrFun h y).trans (map_zero ρ).symm)), (hpt f₀ hf₀).1.2⟩`.

Use `LiftsM.transport hθ hσ hA hB j (fun p h g => ?_) hI' hν h𝓕 fun ν₁ 𝓕₁ a b => hP _ _ aS aT hR _ _ MB₁ MA₁ θ ψ hθ ω₁ hW _ It₁ hv (H.transport hθ hσ hA hB hρ hα hω j.surjective (hpt f₀ hf₀).2 hI') ν₁ 𝓕₁ a b _ (hpt f hf).1` and prove the remaining obligations. Rewrite using `[(hpt f hf).2, thetaKO, hω]`. Conclude with `hK _ _ _`.
-/
theorem lifts_of_tr {X : ProvA} (hP : PairLifts D X) (hθ : IsInfFam θ) {A B : HSp D} {SA SB SA₁ SB₁ : D.what₂.Tau → SPar}
    {MA : DSModel A SA} {MB : DSModel B SB} {εA εB : Bool} {MA₁ : DSModel (sgn εA A) SA₁} {MB₁ : DSModel (sgn εB B) SB₁}
    {σ : ℂ →+* ℂ} {κA : SmT MA₁ ≃+ SmT MA} {κB : SmT MB₁ ≃+ SmT MB} (hσ : IdOrConj σ) (hA : ModelTr σ εA θ MA₁ MA κA)
    (hB : ModelTr σ εB θ MB₁ MB κB) {aS aT : D.what₂.Tau → ℚ} (hR : ∀ τ, RulePar X (SB₁ τ) (SA₁ τ) (aS τ) (aT τ))
    {ψ : AddChar (AF D.host.F) ℂ} {ω₁ : WRep (sgn εB B) (sgn εA A)} (hW : IsWeilExp ψ _ _ aS aT ω₁)
    {Z P : Type} {ω : GA D B × GA D A →* Module.End ℂ (Z → ℂ)} {pt : (Z → ℂ) → P → Z → ℂ} {vac : (Z → ℂ) → Prop}
    {ρ : ℂ →+* ℂ} (hρ : IdOrConj ρ) {α : WO (sgn εB B) (sgn εA A) → Z} (hα : Function.Surjective α)
    (hω : ∀ h g f, ω₁ (h, g) (fun y => ρ (f (α y))) = fun y => ρ (ω (ofSgn εB B h, ofSgn εA A g) f (α y)))
    (j : P ≃ PolF D (sgn εA A).rank (sgn εB B).rank)
    (hpt : ∀ f, vac f → IsVacF ψ θ (Fr.ofModel MB₁) (Fr.ofModel MA₁) (fun y => ρ (f (α y))) ∧
      ∀ p, ptOf ψ θ MB₁ MA₁ (fun y => ρ (f (α y))) (j p) = fun y => ρ (pt f p (α y)))
    {f₀ : Z → ℂ} (hf₀ : vac f₀) (h0 : f₀ ≠ 0) {It : P → SmT MA →ₗ[ℂ] SmT MB} (H : IsIntwF θ MB MA ω (pt f₀) It)
    (h1 : ∀ p q, It (j.symm (p + q)) = It (j.symm p) + It (j.symm q))
    (h2 : ∀ (c : ℂ) p, It (j.symm (c • p)) = σ c • It (j.symm p)) {f : Z → ℂ} (hf : vac f)
    {K : P → GA D B → GA D A → ℂ} (hK : ∀ p h g, ρ (ω (h, g) (pt f p) (α 0)) = σ (K p h g))
    {ν : Measure (GA D A)} {𝓕 : Set (GA D A)} (hν : ν.IsHaarMeasure) (h𝓕 : IsFundamentalDomain (GQ A) 𝓕 ν) :
    LiftsM θ MA MB ν 𝓕 K fun p v => It p v := by
  obtain ⟨It₁, hI⟩ := exists_bilin hσ hA hB (fun p => It (j.symm p)) h1 h2
  have hI' : ∀ p v, κB (It₁ (j p) v) = It p (κA v) := fun p v => by rw [hI, j.symm_apply_apply]
  have hv : IsVacVec ψ θ MB₁ MA₁ fun y => ρ (f₀ (α y)) := ⟨(hpt f₀ hf₀).1.1, fun h => h0 (funext fun z => by
    obtain ⟨y, rfl⟩ := hα z
    exact ρ.injective ((congrFun h y).trans (map_zero ρ).symm)), (hpt f₀ hf₀).1.2⟩
  refine LiftsM.transport hθ hσ hA hB j (fun p h g => ?_) hI' hν h𝓕 fun ν₁ 𝓕₁ a b =>
    hP _ _ aS aT hR _ _ MB₁ MA₁ θ ψ hθ ω₁ hW _ It₁ hv
      (H.transport hθ hσ hA hB hρ hα hω j.surjective (hpt f₀ hf₀).2 hI') ν₁ 𝓕₁ a b _ (hpt f hf).1
  rw [(hpt f hf).2, thetaKO, hω]
  exact hK _ _ _

variable {ψ : AddChar (AF D.host.F) ℂ} {ε : Bool} {S T : Node D}

/- English proof (translation)
Establish `: (frSgn ε (Fr.ofModel S.M)).cart = cartS ε S` using `funext fun τ => cart_frSgn ε _ τ`. Unfold `ptF fock`. Rewrite using `[this]`. Both sides reduce to the same expression.
-/
theorem fock_eq (f : WO S.V T.V → ℂ) (p : GlobalTheory.Grid.Pol S T) :
    ptF ψ θ (frSgn ε (Fr.ofModel S.M)) (Fr.ofModel T.M) f p = fock ψ θ ε S T f p := by
  have : (frSgn ε (Fr.ofModel S.M)).cart = cartS ε S := funext fun τ => cart_frSgn ε _ τ
  unfold ptF fock
  rw [this]
  rfl

/- English proof (translation)
Assemble the required witnesses or components as `⟨h.1, fun τ => by rw [hA, hB]; exact h.2 τ⟩`.
-/
theorem isVacF_congr {V W : HSp D} {A A' : Fr V} {B B' : Fr W} (hA : ∀ τ, A'.cart τ = A.cart τ)
    (hB : ∀ τ, B'.cart τ = B.cart τ) {f : WO V W → ℂ} (h : IsVacF ψ θ A B f) : IsVacF ψ θ A' B' f :=
  ⟨h.1, fun τ => by rw [hA, hB]; exact h.2 τ⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨h.1, fun τ => by rw [cart_frSgn]; exact h.2 τ⟩`.
-/
theorem isVacF_of_finVec {f : WO S.V T.V → ℂ} (h : IsFinVec ψ θ ε S T f) :
    IsVacF ψ θ (frSgn ε (Fr.ofModel S.M)) (Fr.ofModel T.M) f :=
  ⟨h.1, fun τ => by rw [cart_frSgn]; exact h.2 τ⟩

/- English proof (translation)
Introduce and unpack `rfl`. Take `⟨⟨p, hp⟩, h⟩` from `h.2.norm`. Use `h p hp` as an intermediate fact. Simplify using `[nrm2] at this`.
-/
theorem vac_ne {f : WO S.V T.V → ℂ} (h : IsVac ψ θ ε S T f) : f ≠ 0 := by
  rintro rfl
  obtain ⟨⟨p, hp⟩, h⟩ := h.2.norm
  have := h p hp
  simp [nrm2] at this

/- English proof (translation)
Establish `cS : ∀ τ, (Fr.ofModel MS).cart τ = (frSgn ε (Fr.ofModel S.M)).cart τ` using `fun τ => (hS.cart τ).trans (cart_frSgn ε (Fr.ofModel S.M) τ).symm`. Establish `cT : ∀ τ, (Fr.ofModel MT).cart τ = (Fr.ofModel T.M).cart τ` using `hT.cart`. Take `⟨j, hj⟩` from `GlobalTheory.T.fockVector_frameChange_same_cartan D ψ θ hW.std hθ (sgn ε S.V) T.V _ _ _ _ cS cT`. Conclude with `lifts_of_tr hP hθ hσ hT hS hR (ω₁ := ω.toSgn ε) ⟨χS, χT, hW, he⟩ (pt := fun f p => fock ψ θ ε S T f p) (vac := IsFinVec ψ θ ε S T) (Or.inl rfl) (α := fun y => y) Function.surjective_id (fun _ _ _ => rfl) j.toEquiv (fun f hf => ⟨isVacF_congr cS cT (isVacF_of_finVec hf), fun p => ( …`.
-/
theorem lifts_toSource {X : ProvA} (hP : PairLifts D X) (hθ : IsInfFam θ) {σ : ℂ →+* ℂ} (hσ : IdOrConj σ)
    {S₁ T₁ : D.what₂.Tau → SPar} {MS : DSModel (sgn ε S.V) S₁} {MT : DSModel (sgn false T.V) T₁}
    {κS : SmT MS ≃+ SmT S.M} {κT : SmT MT ≃+ SmT T.M} (hS : ModelTr σ ε θ MS S.M κS) (hT : ModelTr σ false θ MT T.M κT)
    {aS aT : D.what₂.Tau → ℚ} (hR : ∀ τ, RulePar X (S₁ τ) (T₁ τ) (aS τ) (aT τ)) {χS χT : (AE D)ˣ →* Circle}
    {ω : WRep S.V T.V} (hW : IsWeil ψ ε S.V T.V χS χT ω) (he : ∀ τ, HasInfExp D χS τ (aS τ) ∧ HasInfExp D χT τ (aT τ))
    {f₀ : WO S.V T.V → ℂ} (hf₀ : IsVac ψ θ ε S T f₀) {It : GlobalTheory.Grid.Pol S T → SmT T.M →ₗ[ℂ] SmT S.M}
    (H : IsIntwF θ S.M T.M ω (fock ψ θ ε S T f₀) It) (h1 : ∀ p q, It (p + q) = It p + It q)
    (h2 : ∀ (c : ℂ) p, It (c • p) = σ c • It p) {f : WO S.V T.V → ℂ} (hf : IsFinVec ψ θ ε S T f) {m : T.MeasDat}
    (hm : m.ν.IsHaarMeasure ∧ IsFundamentalDomain (GQ T.V) m.fd m.ν) :
    LiftsM θ T.M S.M m.ν m.fd (fun p h g => σ (thetaKO ω h g (fock ψ θ ε S T f p))) fun p v => It p v := by
  have cS : ∀ τ, (Fr.ofModel MS).cart τ = (frSgn ε (Fr.ofModel S.M)).cart τ := fun τ =>
    (hS.cart τ).trans (cart_frSgn ε (Fr.ofModel S.M) τ).symm
  have cT : ∀ τ, (Fr.ofModel MT).cart τ = (Fr.ofModel T.M).cart τ := hT.cart
  obtain ⟨j, hj⟩ := GlobalTheory.T.fockVector_frameChange_same_cartan D ψ θ hW.std hθ (sgn ε S.V) T.V _ _ _ _ cS cT
  exact lifts_of_tr hP hθ hσ hT hS hR (ω₁ := ω.toSgn ε) ⟨χS, χT, hW, he⟩ (pt := fun f p => fock ψ θ ε S T f p)
    (vac := IsFinVec ψ θ ε S T) (Or.inl rfl) (α := fun y => y) Function.surjective_id (fun _ _ _ => rfl) j.toEquiv
    (fun f hf => ⟨isVacF_congr cS cT (isVacF_of_finVec hf), fun p => (hj f hf.1 p).trans (fock_eq f p)⟩)
    (IsVac.isFinVec ψ θ ε S T hf₀) (vac_ne hf₀) H (fun p q => by simp [h1]) (fun c p => by simp [h2]) hf
    (fun p h g => (hσ.invol _).symm) hm.1 hm.2

/- English proof (translation)
Establish `cS : ∀ τ, (Fr.ofModel MS).cart τ = (frSgn ε (Fr.ofModel S.M)).cart τ` using `fun τ => (hS.cart τ).trans (cart_frSgn ε (Fr.ofModel S.M) τ).symm`. Establish `cT : ∀ τ, (Fr.ofModel MT).cart τ = (Fr.ofModel T.M).cart τ` using `hT.cart`. Establish `hs` using `ha.weil.std`. Establish `L` using `GlobalTheory.T.hermitianAdjoint_laws_standardCharacter D ψ hs (sgn ε S.V) T.V`. Take `⟨ω', hW', hω'⟩` from `GlobalTheory.T.exists_conj_weilDatum_exchangedPair D ψ _ _ _ _ _ ha.weil`.

Take `⟨j₀, hj₀, hj₀'⟩` from `GlobalTheory.T.fockVectors_conjAdjointPullback_bijection D ψ θ hs hθ (sgn ε S.V) T.V (frSgn ε (Fr.ofModel S.M)) (Fr.ofModel T.M)`. Take `⟨j, hj⟩` from `GlobalTheory.T.fockVector_frameChange_same_cartan D ψ θ hs hθ T.V (sgn ε S.V) _ _ _ _ cT cS`. Establish `z : adjO (sgn ε S.V) T.V 0 = 0`. Use `L.add 0 0` as an intermediate fact. Rewrite `this` using `[add_zero]`.

Conclude with `left_eq_add.1 this`. Establish `hs₀ : ∀ (c : ℂ) x, j₀.symm (c • x) = starRingEnd ℂ c • j₀.symm x` using `fun c x => j₀.injective (by rw [hj₀, j₀.apply_symm_apply, j₀.apply_symm_apply, Complex.conj_conj])`. Establish `H` using `ha.intw`. Use `lifts_of_tr hP hθ (Or.inr rfl) hS hT hR (ω₁ := ω') ⟨χT, χS, hW', fun τ => (he τ).symm⟩ (ω := a.ω.swap) (pt := fun f p => fock ψ θ ε S T f p) (vac := IsFinVec ψ θ ε S T) (Or.inr rfl) (α := adjO (sgn ε S.V) T.V) (fun x => ⟨_, L.invol x⟩) (fun h g f => hω' g h f) (j₀.toEquiv.trans j …` and prove the remaining obligations. Conclude with `(hj _ (hj₀' f (isVacF_of_finVec hf)).1.1 _).trans (((hj₀' f (isVacF_of_finVec hf)).2 p).trans (congrArg _ (fock_eq f p)))`.
-/
theorem lifts_toTarget {X : ProvA} (hP : PairLifts D X) (hθ : IsInfFam θ)
    {S₁ T₁ : D.what₂.Tau → SPar} {MS : DSModel (sgn ε S.V) S₁} {MT : DSModel (sgn false T.V) T₁}
    {κS : SmT MS ≃+ SmT S.M} {κT : SmT MT ≃+ SmT T.M} (hS : ModelTr (starRingEnd ℂ) ε θ MS S.M κS)
    (hT : ModelTr (starRingEnd ℂ) false θ MT T.M κT)
    {aS aT : D.what₂.Tau → ℚ} (hR : ∀ τ, RulePar X (T₁ τ) (S₁ τ) (aT τ) (aS τ)) {χS χT : (AE D)ˣ →* Circle}
    {a : ArrT S T} (ha : a.Is ψ θ ε χS χT) (he : ∀ τ, HasInfExp D χS τ (aS τ) ∧ HasInfExp D χT τ (aT τ))
    {f : WO S.V T.V → ℂ} (hf : IsFinVec ψ θ ε S T f) {m : S.MeasDat}
    (hm : m.ν.IsHaarMeasure ∧ IsFundamentalDomain (GQ S.V) m.fd m.ν) :
    LiftsM θ S.M T.M m.ν m.fd (fun p h g => thetaKO a.ω g h (fock ψ θ ε S T f p)) fun p v => a.It p v := by
  have cS : ∀ τ, (Fr.ofModel MS).cart τ = (frSgn ε (Fr.ofModel S.M)).cart τ := fun τ =>
    (hS.cart τ).trans (cart_frSgn ε (Fr.ofModel S.M) τ).symm
  have cT : ∀ τ, (Fr.ofModel MT).cart τ = (Fr.ofModel T.M).cart τ := hT.cart
  have hs := ha.weil.std
  have L := GlobalTheory.T.hermitianAdjoint_laws_standardCharacter D ψ hs (sgn ε S.V) T.V
  obtain ⟨ω', hW', hω'⟩ := GlobalTheory.T.exists_conj_weilDatum_exchangedPair D ψ _ _ _ _ _ ha.weil
  obtain ⟨j₀, hj₀, hj₀'⟩ := GlobalTheory.T.fockVectors_conjAdjointPullback_bijection D ψ θ hs hθ (sgn ε S.V) T.V (frSgn ε (Fr.ofModel S.M)) (Fr.ofModel T.M)
  obtain ⟨j, hj⟩ := GlobalTheory.T.fockVector_frameChange_same_cartan D ψ θ hs hθ T.V (sgn ε S.V) _ _ _ _ cT cS
  have z : adjO (sgn ε S.V) T.V 0 = 0 := by
    have := L.add 0 0
    rw [add_zero] at this
    exact left_eq_add.1 this
  have hs₀ : ∀ (c : ℂ) x, j₀.symm (c • x) = starRingEnd ℂ c • j₀.symm x := fun c x =>
    j₀.injective (by rw [hj₀, j₀.apply_symm_apply, j₀.apply_symm_apply, Complex.conj_conj])
  have H := ha.intw
  refine lifts_of_tr hP hθ (Or.inr rfl) hS hT hR (ω₁ := ω') ⟨χT, χS, hW', fun τ => (he τ).symm⟩ (ω := a.ω.swap)
    (pt := fun f p => fock ψ θ ε S T f p) (vac := IsFinVec ψ θ ε S T) (Or.inr rfl) (α := adjO (sgn ε S.V) T.V)
    (fun x => ⟨_, L.invol x⟩) (fun h g f => hω' g h f) (j₀.toEquiv.trans j.toEquiv)
    (fun f hf => ⟨isVacF_congr cT cS (hj₀' f (isVacF_of_finVec hf)).1, fun p => ?_⟩)
    (IsVac.isFinVec ψ θ ε S T ha.vac) (vac_ne ha.vac) (It := fun p => a.It p)
    ⟨by_contra fun h => H.ne (LinearMap.ext fun p => by_contra fun h' => h ⟨p, h'⟩), H.bdd, H.eqK, H.eqg, H.invK, H.invg⟩
    (fun p q => by simp) (fun c p => by simp [hs₀]) hf (fun p h g => by rw [z]; rfl) hm.1 hm.2
  exact (hj _ (hj₀' f (isVacF_of_finVec hf)).1.1 _).trans (((hj₀' f (isVacF_of_finVec hf)).2 p).trans
    (congrArg _ (fock_eq f p)))

/- English proof (translation)
Unfold `Lift.attChr att`. Use `split_ifs`. Rewrite using `[sub_eq_add_neg]`. Conclude with `StepVac.hasInfExp_mul h (StepVac.hasInfExp_inv hη)`. Conclude with `h`.
-/
theorem hasInfExp_att {χ η : (AE D)ˣ →* Circle} {τ : D.what₂.Tau} {c : ℚ} (h : HasInfExp D χ τ c)
    (hη : HasInfExp D η τ (1 / 2)) (n : ℕ) : HasInfExp D (Lift.attChr χ η n) τ (att c n) := by
  unfold Lift.attChr att
  split_ifs
  · rw [sub_eq_add_neg]
    exact StepVac.hasInfExp_mul h (StepVac.hasInfExp_inv hη)
  · exact h

/- English proof (translation)
Distinguish the cases in `hd : df`. Conclude with `⟨(h.1 hd).1.1, (h.1 hd).2⟩`. Conclude with `⟨(h.2 hd).1.1, (h.2 hd).2⟩`.
-/
theorem haar_of_is {N : Node D} {m : N.MeasDat} {df : Prop} {K : Subgroup (GL (Fin N.V.rank) (Lev.EAf D))}
    (h : m.Is df K) : m.ν.IsHaarMeasure ∧ IsFundamentalDomain (GQ N.V) m.fd m.ν := by
  by_cases hd : df
  · exact ⟨(h.1 hd).1.1, (h.1 hd).2⟩
  · exact ⟨(h.2 hd).1.1, (h.2 hd).2⟩

/- English proof (translation)
Substitute `h` using the available equality. Conclude with `hm`.
-/
theorem haar_cast {N N' : Node D} (h : N = N') {m : N.MeasDat}
    (hm : m.ν.IsHaarMeasure ∧ IsFundamentalDomain (GQ N.V) m.fd m.ν) :
    (m.cast h).ν.IsHaarMeasure ∧ IsFundamentalDomain (GQ N'.V) (m.cast h).fd (m.cast h).ν := by
  subst h; exact hm

section Grid

open GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts Formalism.L2.DIV Formalism.L2.Indef

variable {G₀ : Type} [Group G₀] [Fintype G₀] {Pl0 T : Type} {A : FamIn D.what₂.LL G₀ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {G : GridPre R}

/- English proof (translation)
Consider the cases of `i with`. Consider the case `succ i => exact (hG.spaces.vert i j hi hj).par`. Consider the case `zero`. Rewrite using `[parV_zero D hj]`. Use `show (row0 R j).S = _`.

Break down `hj.lt_or_eq with h | rfl` into its components or cases. Rewrite using `[← nodeY_eq_chainVertexAtRowZero_of_lt R h] show parB (Ptw D) (min j D.R.m) = _`. Rewrite using `[min_eq_left hj]`. Rewrite using `[← nodeX_eq_chainVertexAtRowZero_top R]`.
-/
theorem par_vert (hG : G.Is) {i j : ℕ} (hi : i ≤ D.R.m) (hj : j ≤ D.R.m) : (G.V i j).S = parV D i j := by
  cases i with
  | succ i => exact (hG.spaces.vert i j hi hj).par
  | zero =>
    rw [parV_zero D hj]
    show (row0 R j).S = _
    rcases hj.lt_or_eq with h | rfl
    · rw [← nodeY_eq_chainVertexAtRowZero_of_lt R h]
      show parB (Ptw D) (min j D.R.m) = _
      rw [min_eq_left hj]
    · rw [← nodeX_eq_chainVertexAtRowZero_top R]

/- English proof (translation)
Consider the cases of `j with`. Consider the case `succ j => exact (hG.spaces.X j hj).par`. Consider the case `zero => exact (hG.spaces.P _ le_rfl).par.trans (parP_m D)`.
-/
theorem par_Xp (hG : G.Is) {j : ℕ} (hj : j ≤ D.R.m) : (G.Xp j).S = parXp D j := by
  cases j with
  | succ j => exact (hG.spaces.X j hj).par
  | zero => exact (hG.spaces.P _ le_rfl).par.trans (parP_m D)

/- English proof (translation)
Consider the cases of `j with`. Consider the case `zero => rw [G.meas_zero]`. Conclude with `haar_of_is (hG.meas.col i hi)`. Consider the case `succ j`. Consider the cases of `i with`.

Consider the case `succ i => exact haar_of_is (hG.meas.vert i j hi hj)`. Consider the case `zero => show (meas0 R t j).ν.IsHaarMeasure ∧ IsFundamentalDomain (GQ (row0 R (j + 1)).V) (meas0 R t j).fd (meas0 R t j).ν`. Unfold `meas0`. Use `split_ifs with h`. Use `haar_cast _ ?_` and prove the remaining obligations.

Distinguish the cases in `h' : j + 1 + 1 < D.R.m`. Conclude with `⟨(hR.measY t _ h').1.1, (hR.measY t _ h').2⟩`. Establish `e : j + 1 = D.R.m - 1` using `by omega`. Use `hR.measY' t` as an intermediate fact. Rewrite `this` using `[← e]`.

Conclude with `⟨this.1.1, this.2⟩`. Conclude with `haar_cast _ ⟨(hR.measX t).1.1, (hR.measX t).2⟩`.
-/
theorem haar_vert (hR : RowBase R) (hG : G.Is) (t : T) {i j : ℕ} (hi : i ≤ D.R.m) (hj : j ≤ D.R.m) :
    (G.meas t i j).ν.IsHaarMeasure ∧ IsFundamentalDomain (GQ (G.V i j).V) (G.meas t i j).fd (G.meas t i j).ν := by
  cases j with
  | zero => rw [G.meas_zero]; exact haar_of_is (hG.meas.col i hi)
  | succ j =>
    cases i with
    | succ i => exact haar_of_is (hG.meas.vert i j hi hj)
    | zero =>
      show (meas0 R t j).ν.IsHaarMeasure ∧ IsFundamentalDomain (GQ (row0 R (j + 1)).V) (meas0 R t j).fd (meas0 R t j).ν
      unfold meas0
      split_ifs with h
      · refine haar_cast _ ?_
        by_cases h' : j + 1 + 1 < D.R.m
        · exact ⟨(hR.measY t _ h').1.1, (hR.measY t _ h').2⟩
        · have e : j + 1 = D.R.m - 1 := by omega
          have := hR.measY' t
          rw [← e] at this
          exact ⟨this.1.1, this.2⟩
      · exact haar_cast _ ⟨(hR.measX t).1.1, (hR.measX t).2⟩

/- English proof (translation)
Consider the cases of `j with`. Consider the case `zero => exact haar_of_is (hG.meas.P _ le_rfl)`. Consider the case `succ j => exact haar_of_is (hG.meas.X j hj)`.
-/
theorem haar_Xp (hG : G.Is) {j : ℕ} (hj : j ≤ D.R.m) :
    (G.measX j).ν.IsHaarMeasure ∧ IsFundamentalDomain (GQ (G.Xp j).V) (G.measX j).fd (G.measX j).ν := by
  cases j with
  | zero => exact haar_of_is (hG.meas.P _ le_rfl)
  | succ j => exact haar_of_is (hG.meas.X j hj)

/- English proof (translation)
The claim follows from `GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ _ hR.lev.eta (StepVac.hasInfQ_tau (a := fun _ => 1 / 2) ⟨_, fun _ => by norm_num, R.toLevCh.C.isEta.inf⟩) τ`.
-/
theorem exp_eta (hR : RowBase R) (τ : D.what₂.Tau) : HasInfExp D R.eta τ (1 / 2) :=
  GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ _ hR.lev.eta
    (StepVac.hasInfQ_tau (a := fun _ => 1 / 2) ⟨_, fun _ => by norm_num, R.toLevCh.C.isEta.inf⟩) τ

/- English proof (translation)
Take `⟨n, hn, ho⟩` from `hR.lev.xi_fin t`. Use `StepVac.hasInfExp_mul (GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ _ (hR.lev.mu0 ⟨j, hj⟩) (StepVac.hasInfQ_tau (R.toLevCh.C.isMu0 ⟨j, hj⟩).inf) τ) (StepVac.hasInfExp_of_order hR.inf (hR.lev.xi t) hn ho τ)` as an intermediate fact. Rewrite `this` using `[add_zero, Formalism.L2.Host.eExp, Equiv.symm_apply_apply]`. Then use the resulting hypothesis.
-/
theorem exp_mu (hR : RowBase R) (t : T) {j : ℕ} (hj : j < D.R.m) (τ : D.what₂.Tau) :
    HasInfExp D (R.toLevCh.mu t (j + 1)) τ (-(D.hc τ).e ⟨j, hj⟩) := by
  obtain ⟨n, hn, ho⟩ := hR.lev.xi_fin t
  have := StepVac.hasInfExp_mul (GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ _ (hR.lev.mu0 ⟨j, hj⟩)
    (StepVac.hasInfQ_tau (R.toLevCh.C.isMu0 ⟨j, hj⟩).inf) τ) (StepVac.hasInfExp_of_order hR.inf (hR.lev.xi t) hn ho τ)
  rwa [add_zero, Formalism.L2.Host.eExp, Equiv.symm_apply_apply] at this

/- English proof (translation)
The claim follows from `GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ _ (hG.chars.tie _ (by omega) (by omega)) (hG.chars.aux _ (by omega) (by omega)).inf τ`.
-/
theorem exp_chi (hG : G.Is) {i : ℕ} (hi : i < D.R.m) (τ : D.what₂.Tau) :
    HasInfExp D (G.chi (D.R.m - i)) τ (cen D τ (D.R.m - i)) :=
  GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ _ (hG.chars.tie _ (by omega) (by omega))
    (hG.chars.aux _ (by omega) (by omega)).inf τ

/- English proof (translation)
Assemble the required witnesses or components as `⟨by_contra fun h => H.ne (LinearMap.ext fun p => by_contra fun h' => h ⟨p, h'⟩), H.bdd, H.eqK, H.eqg, H.invK, H.invg⟩`.
-/
theorem isIntwF_of_isItW {V W : HSp D} {S S' : D.what₂.Tau → SPar} {M : DSModel V S} {M' : DSModel W S'} {ω : WRep V W}
    {pt : PolF D W.rank V.rank → WO V W → ℂ} {It : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M}
    (H : IsItW θ M M' ω pt It) : IsIntwF θ M M' ω pt fun p => It p :=
  ⟨by_contra fun h => H.ne (LinearMap.ext fun p => by_contra fun h' => h ⟨p, h'⟩), H.bdd, H.eqK, H.eqg, H.invK, H.invg⟩

/- English proof (translation)
Establish `hθ` using `hR.inf`. Establish `rp` using `fun {S S' aS aT} => rulePar_of_pairPar (S := S) (S' := S') (aS := aS) (aT := aT) h3 h4 h5`. Use `⟨fun t i j hi hj f hf => ?_, fun t i j hi hj f hf => ?_, fun i hi f hf => ?_, fun i hi f hf => ?_, fun t j hj f hf => ?_⟩` and prove the remaining obligations. Take `⟨M₁, κ, h⟩` from `GlobalTheory.T.exists_negatedSpace_discreteSeriesModelTransport D _ hθ _ _ (G.V (i + 1) j).M`. Establish `a` using `hG.arrows.X i j hi hj`.

Conclude with `lifts_toSource hP hθ (Or.inl rfl) h (ModelTr.refl _) (fun τ => rp (by rw [par_vert hG hi hj, par_vert hG hi.le hj]; exact GlobalTheory.T.contragredientThetaParams_addBlockArrow D hS i j τ hi hj)) a.weil (fun τ => ⟨hasInfExp_att (exp_chi hG hi τ) (exp_eta hR τ) _, hasInfExp_att (e …`. Establish `a` using `hG.arrows.th t i j hi hj`. Conclude with `lifts_toSource hP hθ (Or.inl rfl) (ModelTr.refl _) (ModelTr.refl _) (fun τ => rp (by rw [par_vert hG hi hj.le, par_vert hG hi hj]; exact GlobalTheory.T.contragredientThetaParams_removeBlockArrow D hS i j τ hi hj)) a.weil (fun τ => ⟨hasInfExp_att (exp_mu hR t hj τ) (exp_eta hR τ) …`. Take `⟨M₁, κ, h⟩` from `exists_conj_neg hθ (G.P (i + 1)).M`. Take `⟨M₂, κ', h'⟩` from `GlobalTheory.T.discrete_series_model_conjugate_transfer D _ hθ _ _ (G.P i).M`.

Establish `a` using `hG.arrows.dn i hi`. Conclude with `lifts_toSource hP hθ (Or.inr rfl) h h' (fun τ => rp (by rw [(hG.spaces.P _ hi).par, (hG.spaces.P _ hi.le).par]; exact (GlobalTheory.T.contragredientThetaParams_columnArrows D hS i τ hi).1)) a.weil (fun τ => ⟨exp_chi hG hi τ, exp_chi hG hi τ⟩) a.vac (GlobalTheory.T.realThetaIntert …`. Take `⟨M₁, κ, h⟩` from `exists_conj_neg hθ (G.P (i + 1)).M`. Take `⟨M₂, κ', h'⟩` from `GlobalTheory.T.discrete_series_model_conjugate_transfer D _ hθ _ _ (G.P i).M`. Conclude with `lifts_toTarget hP hθ h h' (fun τ => rp (by rw [(hG.spaces.P _ hi).par, (hG.spaces.P _ hi.le).par]; exact (GlobalTheory.T.contragredientThetaParams_columnArrows D hS i τ hi).2)) (hG.arrows.dn i hi) (fun τ => ⟨exp_chi hG hi τ, exp_chi hG hi τ⟩) hf (haar_of_is (hG.meas.P _ hi))`.

Take `⟨M₁, κ, h⟩` from `GlobalTheory.T.discrete_series_model_conjugate_transfer D _ hθ _ _ (G.Xp j).M`. Take `⟨M₂, κ', h'⟩` from `GlobalTheory.T.discrete_series_model_conjugate_transfer D _ hθ _ _ (G.Xp (j + 1)).M`. Conclude with `lifts_toTarget hP hθ h h' (fun τ => rp (by rw [par_Xp hG hj, par_Xp hG hj.le]; exact GlobalTheory.T.contragredientThetaParams_lastRowArrows D hS j τ hj)) (hG.arrows.col t j hj) (fun τ => ⟨exp_mu hR t hj τ, exp_mu hR t hj τ⟩) hf (haar_Xp hG hj.le)`.
-/
theorem cuspAlong_of_pairLifts {X : ProvA} (h3 : Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisUpDownLine X) (h4 : Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisFourth X)
    (h5 : Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisFifth X) (hP : PairLifts D X) (hS : Sizes D) (hR : RowBase R) (hG : G.Is) : CuspAlong G := by
  have hθ := hR.inf
  have rp := fun {S S' aS aT} => rulePar_of_pairPar (S := S) (S' := S') (aS := aS) (aT := aT) h3 h4 h5
  refine ⟨fun t i j hi hj f hf => ?_, fun t i j hi hj f hf => ?_, fun i hi f hf => ?_, fun i hi f hf => ?_,
    fun t j hj f hf => ?_⟩
  · obtain ⟨M₁, κ, h⟩ := GlobalTheory.T.exists_negatedSpace_discreteSeriesModelTransport D _ hθ _ _ (G.V (i + 1) j).M
    have a := hG.arrows.X i j hi hj
    exact lifts_toSource hP hθ (Or.inl rfl) h (ModelTr.refl _)
      (fun τ => rp (by rw [par_vert hG hi hj, par_vert hG hi.le hj]; exact GlobalTheory.T.contragredientThetaParams_addBlockArrow D hS i j τ hi hj)) a.weil
      (fun τ => ⟨hasInfExp_att (exp_chi hG hi τ) (exp_eta hR τ) _, hasInfExp_att (exp_chi hG hi τ) (exp_eta hR τ) _⟩)
      a.vac (isIntwF_of_isItW a.intw) (map_add _) (map_smul _) hf (haar_vert hR hG t hi.le hj)
  · have a := hG.arrows.th t i j hi hj
    exact lifts_toSource hP hθ (Or.inl rfl) (ModelTr.refl _) (ModelTr.refl _)
      (fun τ => rp (by rw [par_vert hG hi hj.le, par_vert hG hi hj]; exact GlobalTheory.T.contragredientThetaParams_removeBlockArrow D hS i j τ hi hj)) a.weil
      (fun τ => ⟨hasInfExp_att (exp_mu hR t hj τ) (exp_eta hR τ) _, hasInfExp_att (exp_mu hR t hj τ) (exp_eta hR τ) _⟩)
      a.vac (isIntwF_of_isItW a.intw) (map_add _) (map_smul _) hf (haar_vert hR hG t hi hj)
  · obtain ⟨M₁, κ, h⟩ := exists_conj_neg hθ (G.P (i + 1)).M
    obtain ⟨M₂, κ', h'⟩ := GlobalTheory.T.discrete_series_model_conjugate_transfer D _ hθ _ _ (G.P i).M
    have a := hG.arrows.dn i hi
    exact lifts_toSource hP hθ (Or.inr rfl) h h'
      (fun τ => rp (by rw [(hG.spaces.P _ hi).par, (hG.spaces.P _ hi.le).par]; exact (GlobalTheory.T.contragredientThetaParams_columnArrows D hS i τ hi).1)) a.weil
      (fun τ => ⟨exp_chi hG hi τ, exp_chi hG hi τ⟩) a.vac
      (GlobalTheory.T.realThetaIntertwiner_adjoint_isRealThetaIntertwiner D _ _ _ _ _ _ _ _ _ _ _ _ _ (fun p => G.ItU i p) (fun _ _ => rfl) a.intw (hG.arrows.up i hi))
      (map_add _) (map_smulₛₗ _) hf (haar_of_is (hG.meas.P i hi.le))
  · obtain ⟨M₁, κ, h⟩ := exists_conj_neg hθ (G.P (i + 1)).M
    obtain ⟨M₂, κ', h'⟩ := GlobalTheory.T.discrete_series_model_conjugate_transfer D _ hθ _ _ (G.P i).M
    exact lifts_toTarget hP hθ h h'
      (fun τ => rp (by rw [(hG.spaces.P _ hi).par, (hG.spaces.P _ hi.le).par]; exact (GlobalTheory.T.contragredientThetaParams_columnArrows D hS i τ hi).2))
      (hG.arrows.dn i hi) (fun τ => ⟨exp_chi hG hi τ, exp_chi hG hi τ⟩) hf (haar_of_is (hG.meas.P _ hi))
  · obtain ⟨M₁, κ, h⟩ := GlobalTheory.T.discrete_series_model_conjugate_transfer D _ hθ _ _ (G.Xp j).M
    obtain ⟨M₂, κ', h'⟩ := GlobalTheory.T.discrete_series_model_conjugate_transfer D _ hθ _ _ (G.Xp (j + 1)).M
    exact lifts_toTarget hP hθ h h'
      (fun τ => rp (by rw [par_Xp hG hj, par_Xp hG hj.le]; exact GlobalTheory.T.contragredientThetaParams_lastRowArrows D hS j τ hj))
      (hG.arrows.col t j hj) (fun τ => ⟨exp_mu hR t hj τ, exp_mu hR t hj τ⟩) hf (haar_Xp hG hj.le)

end Grid

/- English proof (translation)
Introduce `D hS G₀ _ _ Pl0 T A Ks _ _ _ R G hR hG`. Establish `I : Inputs D X` using `⟨hX, hH, hC, hB D, hV D, hL D, hK D, hD D, hP D, hT D, hE D⟩`. Conclude with `cuspAlong_of_pairLifts h3 h4 h5 (GlobalTheory.T.pairThetaLift_factors_through_intertwiner D X I (GlobalTheory.T.thetaLifts_cuspidal_of_lower_tower_lifts_vanish D X I (GlobalTheory.T.lowerTowerLiftsVanish_of_vanish_on_fock D X I (GlobalTheory.T.lowerTowerLifts_vanish_on_fock D X I …`.
-/
theorem liftsCuspidal (X : ProvA) (hX : GlobalTheory.Chain.RealIt.ChosenSeries X) (h3 : Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisUpDownLine X)
    (h4 : Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisFourth X) (h5 : Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisFifth X) (hH : GlobalTheory.Published.HarishChandraModules)
    (hC : GlobalTheory.Published.CuspRapidDecay) (hB : ∀ D, GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.ModelsAreCoverSeries D)
    (hV : ∀ D, GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.VacChar D) (hL : ∀ D, LieFockAll D) (hK : ∀ D, CompactFockAll D) (hD : ∀ D, FockDense D)
    (hP : ∀ D, GlobalTheory.IndefiniteRowSideFullHecke.RapidDecayLift.LiftProps D) (hT : ∀ D, GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.TowerConstTerm D)
    (hE : ∀ D, GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.GKExtension D) : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal := by
  intro D hS G₀ _ _ Pl0 T A Ks _ _ _ R G hR hG
  have I : Inputs D X := ⟨hX, hH, hC, hB D, hV D, hL D, hK D, hD D, hP D, hT D, hE D⟩
  exact cuspAlong_of_pairLifts h3 h4 h5
    (GlobalTheory.T.pairThetaLift_factors_through_intertwiner D X I (GlobalTheory.T.thetaLifts_cuspidal_of_lower_tower_lifts_vanish D X I (GlobalTheory.T.lowerTowerLiftsVanish_of_vanish_on_fock D X I (GlobalTheory.T.lowerTowerLifts_vanish_on_fock D X I)))) hS hR hG

end GlobalTheory.PairLift

end
