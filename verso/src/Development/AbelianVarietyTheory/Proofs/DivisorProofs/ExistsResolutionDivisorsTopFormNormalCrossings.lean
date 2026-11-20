import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CentreAtOfIsAt
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PointSeparationPair
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOrdSubOneLeOrdWedgeDifferentialsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEffectiveCartierDivisorPullbackOfDominant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NadelVanishingCanonicalAddBoundary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeakResolutionOfPrincipalisation
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.ExistsSncChartStatement
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.ExistsPrimeDivisorsSncBoundaryStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDominantOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionFieldMapBijectiveOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalTopFormPullbackBijectiveBirational
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackCompositionCompatible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalDivisorOfForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormOrdEqMultOfIsCartierDivisorOfRationalForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimeDivisorEtalePullbackOrders
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
open GlobalTheory.Discrepancy GlobalTheory.EtaleKlt

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.ResPairSupp

/- English proof (translation)
Take `⟨E, hE, -, hform⟩` from `GlobalTheory.EtaleDiv.exists_isAt_ord_formOrd Y W q s n V hV v hv F hF`. Rewrite using `[hform ω hω, DivOver.formOrd_eq_mult_of_isDivOfForm ℂ W q n ω hω K hK E (s v) hE]`. Establish `h1 : K.IsEqn (s v) 1` using `not_not.1 hvK`. Rewrite using `[h1.mult_eq, Units.val_one]`. Conclude with `(unitAt_one _).ord_eq_zero`.
-/
theorem formOrd_ratPull_eq_zero {W Y : Scheme.{0}} [IsIntegral W] [IsIntegral Y]
    [IsLocallyNoetherian W] [IsLocallyNoetherian Y] (q : W ⟶ Sp ℂ) (n : ℕ)
    [SmoothOfRelativeDimension n q] (s : Y ⟶ W) [IsDominant s] [SmoothOfRelativeDimension n (s ≫ q)]
    (V : Y.Opens) (hV : Etale (V.ι ≫ s)) (ω : RatForms q n) (hω : ω ≠ 0) (K : CartierDiv W)
    (hK : IsDivOfForm K ω) (v : Y) (hv : v ∈ V) (hvK : s v ∉ K.supp) (F : DivOver (s ≫ q))
    (hF : F.IsAt v) : F.formOrd (ratPull q s n ω) = 0 := by
  obtain ⟨E, hE, -, hform⟩ := GlobalTheory.EtaleDiv.exists_isAt_ord_formOrd Y W q s n V hV v hv F hF
  rw [hform ω hω, DivOver.formOrd_eq_mult_of_isDivOfForm ℂ W q n ω hω K hK E (s v) hE]
  have h1 : K.IsEqn (s v) 1 := not_not.1 hvK
  rw [h1.mult_eq, Units.val_one]
  exact (unitAt_one _).ord_eq_zero

/- English proof (translation)
Rewrite `hg` using `[Scheme.Hom.comp_apply]`. Establish `h1` using `isEqn_pullCart s₁ hg`. Take `⟨U, hU, hUe⟩` from `h1.exists_nhds`. Establish `h2` using `hUe (s₂ v) ((hvy.map s₂.continuous).mem_open U.isOpen hU)`. Establish `h3 : UnitAt (s₂ v) ((fnPull s₁ g : W.functionField) / (1 : W.functionFieldˣ))` using `(not_not.1 hv).iff_unitAt.1 h2`.

Rewrite `h3` using `[Units.val_one, div_one]`. Establish `h4` using `GlobalTheory.Cartier.PullDominant.unitAt_map s₂ h3`. Establish `e : (fnPull (s₂ ≫ s₁) g : Y.functionField) = functionFieldMap s₂ (fnPull s₁ g)` using `RingHom.congr_fun (functionFieldMap_comp_dominant s₁ s₂) g`. Rewrite using `[e]`. Conclude with `h4.ord_eq_zero`.
-/
theorem ord_fnPull_eq_zero {X W Y : Scheme.{0}} [IsIntegral X] [IsIntegral W] [IsIntegral Y]
    [IsLocallyNoetherian Y] (s₁ : W ⟶ X) [IsDominant s₁] (s₂ : Y ⟶ W) [IsDominant s₂]
    [IsDominant (s₂ ≫ s₁)] (G : CartierDiv X) (y v : Y) (g : X.functionFieldˣ) (hvy : v ⤳ y)
    (hv : s₂ v ∉ (pullCart s₁ G).supp) (hg : G.IsEqn ((s₂ ≫ s₁) y) g) :
    Scheme.ord (fnPull (s₂ ≫ s₁) g : Y.functionField) v = 0 := by
  rw [Scheme.Hom.comp_apply] at hg
  have h1 := isEqn_pullCart s₁ hg
  obtain ⟨U, hU, hUe⟩ := h1.exists_nhds
  have h2 := hUe (s₂ v) ((hvy.map s₂.continuous).mem_open U.isOpen hU)
  have h3 : UnitAt (s₂ v) ((fnPull s₁ g : W.functionField) / (1 : W.functionFieldˣ)) :=
    (not_not.1 hv).iff_unitAt.1 h2
  rw [Units.val_one, div_one] at h3
  have h4 := GlobalTheory.Cartier.PullDominant.unitAt_map s₂ h3
  have e : (fnPull (s₂ ≫ s₁) g : Y.functionField) = functionFieldMap s₂ (fnPull s₁ g) :=
    RingHom.congr_fun (functionFieldMap_comp_dominant s₁ s₂) g
  rw [e]
  exact h4.ord_eq_zero

end GlobalTheory.ResPairSupp

namespace GlobalTheory.ResPairSupp

/- English proof (translation)
Introduce `hP X _ _ p n hp hdim η G D₀ hη`. Take `⟨W, s₁, U, hW, hsm₁, hpr₁, hU, hiso₁⟩` from `GlobalTheory.WeakRes.weak_resolution hP ℂ X p n hp hdim`. Use `haveI := hW`. Use `haveI : IsDominant s₁ := isDominant_of_isIso_restrict X W s₁ U hU hiso₁`. Establish `hbij₁` using `functionFieldMap_bijective_of_isIso_restrict X W s₁ U hU hiso₁`.

Use `haveI := hsm₁`. Use `haveI := SmoothOfRelativeDimension.smooth n (s₁ ≫ p)`. Use `haveI : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian (s₁ ≫ p)`. Establish `hη₁ : ratPull p s₁ n η ≠ 0` using `fun h => hη ((ratPull_bijective_of_birational ℂ X W p s₁ hbij₁ n).1 (h.trans (map_zero _).symm))`. Take `⟨K₁, hK₁⟩` from `(exists_isDivOfForm_and_toPic ℂ W (s₁ ≫ p) n _ hη₁).1`.

Set `Z : Closeds W` to `(pullCart s₁ G).supp ⊔ (pullCart s₁ D₀).supp ⊔ K₁.supp`. Establish `hZ : ∀ w, w ∉ Z → w ∉ (pullCart s₁ G).supp ∧ w ∉ (pullCart s₁ D₀).supp ∧ w ∉ K₁.supp` using `fun w hw => ⟨fun h => hw (Or.inl (Or.inl h)), fun h => hw (Or.inl (Or.inr h)), fun h => hw (Or.inr h)⟩`. Establish `hgZ : genericPoint W ∉ Z`. Introduce and unpack `((h | h) | h)`. Conclude with `(pullCart s₁ G).genericPoint_notMem_supp h`.

Conclude with `(pullCart s₁ D₀).genericPoint_notMem_supp h`. Conclude with `K₁.genericPoint_notMem_supp h`. Set `I` to `Scheme.IdealSheafData.vanishingIdeal Z`. Establish `hIs : (I.support : Set W) = Z` using `Scheme.IdealSheafData.coe_support_vanishingIdeal Z`. Establish `hI : I ≠ ⊥`.

Introduce `h0`. Establish `: genericPoint W ∈ (I.support : Set W)` using `by rw [h0]; simp`. Rewrite `this` using `[hIs]`. Conclude with `hgZ this`. Take `⟨Y, s₂, hY, hsm, hpr, -, hiso₂, -, hsnc⟩` from `hP ℂ n W (s₁ ≫ p) hW hsm₁ hpr₁ I hI`.

Use `haveI := hY`. Use `haveI := hsm`. Use `haveI := SmoothOfRelativeDimension.smooth n (s₂ ≫ s₁ ≫ p)`. Use `haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (s₂ ≫ s₁ ≫ p)`. Establish `hne : ((I.support.compl : W.Opens) : Set W).Nonempty` using `⟨genericPoint W, by`.

Express the relevant statement in the definitionally equal form `genericPoint W ∉ (I.support : Set W)`. Rewrite using `[hIs]`. Conclude with `hgZ⟩`. Use `haveI : IsDominant s₂ := isDominant_of_isIso_restrict W Y s₂ _ hne hiso₂`. Establish `hbij₂` using `functionFieldMap_bijective_of_isIso_restrict W Y s₂ _ hne hiso₂`.

Set `B : Closeds Y` to `(I.comap s₂).support`. Establish `hB : ∀ y, y ∈ B ↔ s₂ y ∈ Z`. Introduce `y`. Express the relevant statement in the definitionally equal form `y ∈ (B : Set Y) ↔ s₂ y ∈ (Z : Set W)`. Rewrite using `[← hIs]`.

Simplify using `only [B, Scheme.IdealSheafData.support_comap]`. Both sides reduce to the same expression. Establish `hsm' : SmoothOfRelativeDimension n ((s₂ ≫ s₁) ≫ p)` using `by rw [Category.assoc]; exact hsm`. Establish `hpr' : IsProjOver ((s₂ ≫ s₁) ≫ p)` using `by rw [Category.assoc]; exact hpr`. Use `haveI := hsm'`.

Establish `hbij : Function.Bijective (functionFieldMap (s₂ ≫ s₁))`. Rewrite using `[functionFieldMap_comp_dominant s₁ s₂]`. Conclude with `hbij₂.comp hbij₁`. Set `V : Y.Opens` to `s₂ ⁻¹ᵁ I.support.compl`. Establish `hV : Etale (V.ι ≫ s₂)`.

Rewrite using `[← morphismRestrict_ι]`. Use `infer_instance`. Establish `hVB : ∀ v, v ∉ B → v ∈ V`. Introduce `v hv`. Express the relevant statement in the definitionally equal form `s₂ v ∉ (I.support : Set W)`.

Rewrite using `[hIs]`. Conclude with `fun h => hv ((hB v).2 h)`. Use `⟨Y, hY, inferInstance, s₂ ≫ s₁, inferInstance, B, hsm', ?_, hbij, ?_, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Establish `: IsProper ((s₂ ≫ s₁) ≫ p)`. Take `⟨N, i, hi, hi'⟩` from `hpr'`.

Use `isProper_str ℂ N` as an intermediate fact. Rewrite using `[← hi']`. Use `infer_instance`. Establish `: IsProper p`. Take `⟨N, i, hi, rfl⟩` from `hp`.

Use `isProper_str ℂ N` as an intermediate fact. Use `infer_instance`. Conclude with `IsProper.of_comp (s₂ ≫ s₁) p`. Take `⟨r, w, D, σ, -, -, hw, -⟩` from `GlobalTheory.T.exists_prime_divisors_snc_boundary ℂ Y ((s₂ ≫ s₁) ≫ p) n hpr' B hsnc`. Use `(Set.finite_range w).subset ?_` and prove the remaining obligations.

Introduce and unpack `v ⟨hvB, hv1⟩`. Take `⟨i, rfl⟩` from `hw v hv1 hvB`. Conclude with `⟨i, rfl⟩`. Introduce `h`. Conclude with `hη ((ratPull_bijective_of_birational ℂ X Y p (s₂ ≫ s₁) hbij n).1 (h.trans (map_zero _).symm))`.

Introduce `y`. Conclude with `GlobalTheory.T.exists_snc_chart ℂ Y ((s₂ ≫ s₁) ≫ p) n B hsnc y`. Introduce `y v g hvy _ hvB hg`. Conclude with `ord_fnPull_eq_zero s₁ s₂ G y v g hvy (fun h => hvB ((hB v).2 (Or.inl (Or.inl h)))) hg`. Introduce `y v g hvy _ hvB hg`.

Conclude with `ord_fnPull_eq_zero s₁ s₂ D₀ y v g hvy (fun h => hvB ((hB v).2 (Or.inl (Or.inr h)))) hg`. Introduce `v F _ hvB hF`. Establish `hvK : s₂ v ∉ K₁.supp` using `fun h => hvB ((hB v).2 (Or.inr h))`. Establish `key : ∀ (q : Y ⟶ Sp ℂ) (e : s₂ ≫ s₁ ≫ p = q) (F : DivOver q) (_ : F.IsAt v) (h : (functionFieldMap (s₂ ≫ s₁)).comp (Cartier.constFn p) = Cartier.constFn q), F.formOrd (TopForm.formMap n (functionFieldMap (s₂ ≫ s₁)) h η) = 0`. Introduce `q e`.

Substitute `e` using the available equality. Introduce `F hF h`. Establish `e2 : ratPull (s₁ ≫ p) s₂ n (ratPull p s₁ n η) = TopForm.formMap n (functionFieldMap (s₂ ≫ s₁)) h η` using `formMap_formMap _ _ _ (functionFieldMap_comp_dominant s₁ s₂).symm _ _ _ η`. Rewrite using `[← e2]`. Conclude with `formOrd_ratPull_eq_zero (s₁ ≫ p) n s₂ V hV _ hη₁ K₁ hK₁ v (hVB v hvB) hvK F hF`.

Conclude with `key _ (Category.assoc s₂ s₁ p).symm F hF _`.
-/
theorem exists_resolution_supp : GlobalTheory.Published.Principalisation → ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X]
    (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (η : RatForms p n)
    (G D₀ : CartierDiv X), η ≠ 0 →
    ∃ (Y : Scheme.{0}) (_ : IsIntegral Y) (_ : IsLocallyNoetherian Y) (s : Y ⟶ X) (_ : IsDominant s)
      (B : Closeds Y),
      SmoothOfRelativeDimension n (s ≫ p) ∧ IsProper s ∧ Function.Bijective (functionFieldMap s) ∧
      {v : Y | v ∈ B ∧ Order.coheight v = 1}.Finite ∧ ratPull p s n η ≠ 0 ∧
      (∀ y : Y, ∃ (U : Y.Opens) (hy : y ∈ U) (z : Fin n → Γ(Y, U)) (J : Finset (Fin n)) (w : Fin n → Y)
        (u : Fin n → Y.functionFieldˣ), IsSncChart (s ≫ p) n B y U hy z J w u) ∧
      (∀ (y v : Y) (g : X.functionFieldˣ), v ⤳ y → Order.coheight v = 1 → v ∉ B → G.IsEqn (s y) g →
        Scheme.ord (fnPull s g : Y.functionField) v = 0) ∧
      (∀ (y v : Y) (g : X.functionFieldˣ), v ⤳ y → Order.coheight v = 1 → v ∉ B → D₀.IsEqn (s y) g →
        Scheme.ord (fnPull s g : Y.functionField) v = 0) ∧
      (∀ (v : Y) (F : DivOver (s ≫ p)), Order.coheight v = 1 → v ∉ B → F.IsAt v →
        F.formOrd (ratPull p s n η) = 0) := by
  intro hP X _ _ p n hp hdim η G D₀ hη
  obtain ⟨W, s₁, U, hW, hsm₁, hpr₁, hU, hiso₁⟩ := GlobalTheory.WeakRes.weak_resolution hP ℂ X p n hp hdim
  haveI := hW
  haveI : IsDominant s₁ := isDominant_of_isIso_restrict X W s₁ U hU hiso₁
  have hbij₁ := functionFieldMap_bijective_of_isIso_restrict X W s₁ U hU hiso₁
  haveI := hsm₁
  haveI := SmoothOfRelativeDimension.smooth n (s₁ ≫ p)
  haveI : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian (s₁ ≫ p)
  have hη₁ : ratPull p s₁ n η ≠ 0 := fun h =>
    hη ((ratPull_bijective_of_birational ℂ X W p s₁ hbij₁ n).1 (h.trans (map_zero _).symm))
  obtain ⟨K₁, hK₁⟩ := (exists_isDivOfForm_and_toPic ℂ W (s₁ ≫ p) n _ hη₁).1
  let Z : Closeds W := (pullCart s₁ G).supp ⊔ (pullCart s₁ D₀).supp ⊔ K₁.supp
  have hZ : ∀ w, w ∉ Z → w ∉ (pullCart s₁ G).supp ∧ w ∉ (pullCart s₁ D₀).supp ∧ w ∉ K₁.supp :=
    fun w hw => ⟨fun h => hw (Or.inl (Or.inl h)), fun h => hw (Or.inl (Or.inr h)),
      fun h => hw (Or.inr h)⟩
  have hgZ : genericPoint W ∉ Z := by
    rintro ((h | h) | h)
    · exact (pullCart s₁ G).genericPoint_notMem_supp h
    · exact (pullCart s₁ D₀).genericPoint_notMem_supp h
    · exact K₁.genericPoint_notMem_supp h
  let I := Scheme.IdealSheafData.vanishingIdeal Z
  have hIs : (I.support : Set W) = Z := Scheme.IdealSheafData.coe_support_vanishingIdeal Z
  have hI : I ≠ ⊥ := by
    intro h0
    have : genericPoint W ∈ (I.support : Set W) := by rw [h0]; simp
    rw [hIs] at this
    exact hgZ this
  obtain ⟨Y, s₂, hY, hsm, hpr, -, hiso₂, -, hsnc⟩ := hP ℂ n W (s₁ ≫ p) hW hsm₁ hpr₁ I hI
  haveI := hY
  haveI := hsm
  haveI := SmoothOfRelativeDimension.smooth n (s₂ ≫ s₁ ≫ p)
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (s₂ ≫ s₁ ≫ p)
  have hne : ((I.support.compl : W.Opens) : Set W).Nonempty := ⟨genericPoint W, by
    change genericPoint W ∉ (I.support : Set W)
    rw [hIs]; exact hgZ⟩
  haveI : IsDominant s₂ := isDominant_of_isIso_restrict W Y s₂ _ hne hiso₂
  have hbij₂ := functionFieldMap_bijective_of_isIso_restrict W Y s₂ _ hne hiso₂
  let B : Closeds Y := (I.comap s₂).support
  have hB : ∀ y, y ∈ B ↔ s₂ y ∈ Z := by
    intro y
    change y ∈ (B : Set Y) ↔ s₂ y ∈ (Z : Set W)
    rw [← hIs]
    simp only [B, Scheme.IdealSheafData.support_comap]
    rfl

  have hsm' : SmoothOfRelativeDimension n ((s₂ ≫ s₁) ≫ p) := by rw [Category.assoc]; exact hsm
  have hpr' : IsProjOver ((s₂ ≫ s₁) ≫ p) := by rw [Category.assoc]; exact hpr
  haveI := hsm'
  have hbij : Function.Bijective (functionFieldMap (s₂ ≫ s₁)) := by
    rw [functionFieldMap_comp_dominant s₁ s₂]
    exact hbij₂.comp hbij₁
  let V : Y.Opens := s₂ ⁻¹ᵁ I.support.compl
  have hV : Etale (V.ι ≫ s₂) := by
    rw [← morphismRestrict_ι]
    infer_instance
  have hVB : ∀ v, v ∉ B → v ∈ V := by
    intro v hv
    change s₂ v ∉ (I.support : Set W)
    rw [hIs]
    exact fun h => hv ((hB v).2 h)
  refine ⟨Y, hY, inferInstance, s₂ ≫ s₁, inferInstance, B, hsm', ?_, hbij, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    have : IsProper ((s₂ ≫ s₁) ≫ p) := by
      obtain ⟨N, i, hi, hi'⟩ := hpr'
      have := isProper_str ℂ N
      rw [← hi']; infer_instance
    have : IsProper p := by
      obtain ⟨N, i, hi, rfl⟩ := hp
      have := isProper_str ℂ N
      infer_instance
    exact IsProper.of_comp (s₂ ≫ s₁) p
  · obtain ⟨r, w, D, σ, -, -, hw, -⟩ := GlobalTheory.T.exists_prime_divisors_snc_boundary ℂ Y ((s₂ ≫ s₁) ≫ p) n hpr' B hsnc
    refine (Set.finite_range w).subset ?_
    rintro v ⟨hvB, hv1⟩
    obtain ⟨i, rfl⟩ := hw v hv1 hvB
    exact ⟨i, rfl⟩
  · intro h
    exact hη ((ratPull_bijective_of_birational ℂ X Y p (s₂ ≫ s₁) hbij n).1
      (h.trans (map_zero _).symm))
  · intro y
    exact GlobalTheory.T.exists_snc_chart ℂ Y ((s₂ ≫ s₁) ≫ p) n B hsnc y
  · intro y v g hvy _ hvB hg
    exact ord_fnPull_eq_zero s₁ s₂ G y v g hvy (fun h => hvB ((hB v).2 (Or.inl (Or.inl h)))) hg
  · intro y v g hvy _ hvB hg
    exact ord_fnPull_eq_zero s₁ s₂ D₀ y v g hvy (fun h => hvB ((hB v).2 (Or.inl (Or.inr h)))) hg
  · intro v F _ hvB hF
    have hvK : s₂ v ∉ K₁.supp := fun h => hvB ((hB v).2 (Or.inr h))
    have key : ∀ (q : Y ⟶ Sp ℂ) (e : s₂ ≫ s₁ ≫ p = q) (F : DivOver q) (_ : F.IsAt v)
        (h : (functionFieldMap (s₂ ≫ s₁)).comp (Cartier.constFn p) = Cartier.constFn q),
        F.formOrd (TopForm.formMap n (functionFieldMap (s₂ ≫ s₁)) h η) = 0 := by
      intro q e
      subst e
      intro F hF h
      have e2 : ratPull (s₁ ≫ p) s₂ n (ratPull p s₁ n η) =
          TopForm.formMap n (functionFieldMap (s₂ ≫ s₁)) h η :=
        formMap_formMap _ _ _ (functionFieldMap_comp_dominant s₁ s₂).symm _ _ _ η
      rw [← e2]
      exact formOrd_ratPull_eq_zero (s₁ ≫ p) n s₂ V hV _ hη₁ K₁ hK₁ v (hVB v hvB) hvK F hF
    exact key _ (Category.assoc s₂ s₁ p).symm F hF _

end GlobalTheory.ResPairSupp
