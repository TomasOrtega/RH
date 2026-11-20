import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScaleInvOfFamMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenSetOfChartsMemStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartMapIntoAffineConstStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreLineOverSurjectionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineLineMorphismConstantOfConstOnNonzeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PuncturedLineOpenCofiniteStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveLineChartFamiliesAgreeOnOverlapStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LineConst
open Polynomial

/- English proof (translation)
Introduce `k _ _ B _ hB f₀ f₁ h0 h1 h01 a b`. Use `hB.proper` as an intermediate fact. Use `haveI hsub : Subsingleton (Sp k) := inferInstanceAs (Subsingleton (PrimeSpectrum k))`. Set `pt : Sp k` to `IsLocalRing.closedPoint k`. Set `e : B.left` to `(η[B] : 𝟙_ (Over (Sp k)) ⟶ B).left pt`.

Take `⟨_, ⟨W, hW, rfl⟩, heW, -⟩` from `B.left.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ e) isOpen_univ`. Set `L` to `Localization.Away (X : Polynomial k)`. Set `t : L` to `algebraMap (Polynomial k) L X`. Set `ti : L` to `IsLocalization.Away.invSelf (X : Polynomial k)`. Establish `hti : t * ti = 1` using `IsLocalization.Away.mul_invSelf (X : Polynomial k)`.

Set `g₀` to `famMap B f₀ h0 L t`. Set `g₁` to `famMap B f₁ h1 L ti`. Establish `hc` using `GlobalTheory.T.projectiveLine_chart_families_agree_on_overlap B f₀ f₁ h0 h1 h01 L t ti hti`. Set `V : Set (Sp L)` to `{τ | ∀ x : Sp (Polynomial L), spMap (algebraMap L (Polynomial L)) x = τ → g₀ x ∈ W ∧ g₁ x ∈ W}`. Establish `hV : IsOpen V` using `GlobalTheory.T.isOpen_setOf_fibre_charts_mem L _ g₀ g₁ hc W`.

Establish `hfib : ∀ (χ : L →ₐ[k] k) (x' : Sp (Polynomial k)), spMap (algebraMap L (Polynomial L)) (spMap (Polynomial.mapRingHom (χ : L →+* k)) x') = spMap χ.toRingHom pt`. Introduce `χ x'`. Rewrite using `[← Scheme.Hom.comp_apply, ← Spec.map_comp, ← CommRingCat.ofHom_comp]`. Establish `: (Polynomial.mapRingHom (χ : L →+* k)).comp (algebraMap L (Polynomial L)) = (algebraMap k (Polynomial k)).comp (χ : L →+* k)`. Use extensionality with `z`.

Simplify using `[Polynomial.algebraMap_apply]`. Rewrite using `[this, CommRingCat.ofHom_comp, Spec.map_comp, Scheme.Hom.comp_apply]`. Use `congr 1`. Conclude with `hsub.elim _ _`. Establish `hW₀ : ∀ χ : L →ₐ[k] k, spMap χ.toRingHom pt ∈ V → (∀ x', famMap B f₀ h0 k (χ t) x' ∈ W) ∧ (∀ x', famMap B f₁ h1 k (χ ti) x' ∈ W)`.

Introduce `χ hχ`. Prove the components needed by the constructor for the conclusion. Introduce `x'`. Rewrite using `[← famMap_base B f₀ h0 χ t, Scheme.Hom.comp_apply]`. Conclude with `(hχ _ (hfib χ x')).1`.

Introduce `x'`. Rewrite using `[← famMap_base B f₁ h1 χ ti, Scheme.Hom.comp_apply]`. Conclude with `(hχ _ (hfib χ x')).2`. Establish `hinW : ∀ R : Type, ∀ _ : CommRing R, ∀ _ : Algebra k R, ∀ (f : Sp (Polynomial k) ⟶ B.left) (hf : f ≫ B.hom = spMap (algebraMap k (Polynomial k))) (x : Sp (Polynomial R)), famMap B f hf R 1 x ∈ W`. Introduce `R _ _ f hf x`.

Rewrite using `[famMap_one, Scheme.Hom.comp_apply]`. Establish `hx : (spMap (algebraMap k (Polynomial R))) x = pt` using `hsub.elim _ _`. Rewrite using `[hx]`. Conclude with `heW`. Set `χ₁ : L →ₐ[k] k` to `IsLocalization.liftAlgHom (M := Submonoid.powers (X : Polynomial k)) (f := Polynomial.aeval (1 : k)) (by`.

Introduce and unpack `⟨_, n, rfl⟩`. Use the proof step `simp)`. Establish `hχ₁t : χ₁ t = 1` using `by simp [χ₁, t]`. Establish `hχ₁ti : χ₁ ti = 1`. Use `congrArg χ₁ hti` as an intermediate fact.

Rewrite `this` using `[map_mul, hχ₁t, _root_.one_mul, map_one]`. Conclude with `this`. Establish `h1V : spMap χ₁.toRingHom pt ∈ V`. Introduce `x hx`. Take `⟨x', rfl⟩` from `GlobalTheory.T.mem_range_spMap_mapRingHom_of_fibre_closedPoint L k χ₁.toRingHom (fun z => ⟨algebraMap k L z, by simp⟩) x hx`.

Prove the components needed by the constructor for the conclusion. Use `famMap_base B f₀ h0 χ₁ t` as an intermediate fact. Rewrite `this` using `[hχ₁t]`. Rewrite using `[← Scheme.Hom.comp_apply]`. Use `erw [this]`.

Conclude with `hinW k _ _ f₀ h0 x'`. Use `famMap_base B f₁ h1 χ₁ ti` as an intermediate fact. Rewrite `this` using `[hχ₁ti]`. Rewrite using `[← Scheme.Hom.comp_apply]`. Use `erw [this]`.

Conclude with `hinW k _ _ f₁ h1 x'`. Establish `hF` using `GlobalTheory.T.finite_compl_punctured_line_open k V hV χ₁ h1V`. Use `set F := {c : k | c ≠ 0 ∧ ∀ χ : L →ₐ[k] k, χ (algebraMap (Polynomial k) _ X) = c → spMap χ.toRingHom pt ∉ V}`. Establish `hscale : ∀ c : k, c ≠ 0 → c ∉ F → ∀ a : k, spMap (Polynomial.evalRingHom (c * a)) ≫ f₀ = spMap (Polynomial.evalRingHom a) ≫ f₀`. Introduce `c hc0 hcF`.

Simplify using `only [F, Set.mem_setOf_eq, not_and, not_forall, not_not] at hcF`. Take `⟨χ, hχt, hχV⟩` from `hcF hc0`. Take `⟨hA, hB'⟩` from `hW₀ χ hχV`. Establish `hu : χ t * χ ti = 1` using `by rw [← map_mul, hti, map_one]`. Establish `hcmp` using `GlobalTheory.T.projectiveLine_chart_families_agree_on_overlap B f₀ f₁ h0 h1 h01 k (χ t) (χ ti) hu`.

Establish `key` using `GlobalTheory.T.eq_spMap_comp_eval_zero_of_chart_comp_eq k B.left W hW _ _ hA hB' hcmp`. Use `scale_inv_of_famMap B f₀ h0 (χ t) key` as an intermediate fact. Simplify `this` using `[t, hχt]`. Establish `hunit : ∀ c : k, c ≠ 0 → spMap (Polynomial.evalRingHom c) ≫ f₀ = spMap (Polynomial.evalRingHom 1) ≫ f₀`. Introduce `c hc`.

Establish `hfin : ((F ∪ {0}) ∪ (fun d => c / d) '' F).Finite` using `(hF.union (Set.finite_singleton 0)).union (hF.image _)`. Take `⟨d, hd⟩` from `hfin.infinite_compl.nonempty`. Simplify using `only [Set.mem_compl_iff, Set.mem_union, Set.mem_singleton_iff, Set.mem_image, not_or, not_exists, not_and] at hd`. Take `⟨⟨hdF, hd0⟩, hd'⟩` from `hd`. Establish `hcd0 : c / d ≠ 0` using `div_ne_zero hc hd0`.

Establish `hcdF : c / d ∉ F` using `fun h => hd' (c / d) h (by field_simp)`. Establish `e1` using `hscale d hd0 hdF (c / d * 1)`. Establish `e2` using `hscale (c / d) hcd0 hcdF 1`. Rewrite `e1`, `e2` using `[_root_.mul_one]`. Rewrite `e1` using `[show d * (c / d) = c by field_simp]`.

Rewrite using `[e1, e2]`. Conclude with `GlobalTheory.T.affineLine_morphism_constant_of_const_on_nonzero k B.left B.hom f₀ h0 hunit a b`.
-/
theorem projLine_map_const : ∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B], IsAbelianScheme B → ∀ (f₀ f₁ : Sp (Polynomial k) ⟶ B.left), f₀ ≫ B.hom = spMap (algebraMap k (Polynomial k)) → f₁ ≫ B.hom = spMap (algebraMap k (Polynomial k)) → spMap (algebraMap (Polynomial k) (Localization.Away (Polynomial.X : Polynomial k))) ≫ f₀ = spMap (Polynomial.aeval (IsLocalization.Away.invSelf (Polynomial.X : Polynomial k) : Localization.Away (Polynomial.X : Polynomial k))).toRingHom ≫ f₁ → ∀ a b : Polynomial k →ₐ[k] k, spMap a.toRingHom ≫ f₀ = spMap b.toRingHom ≫ f₀ := by
  intro k _ _ B _ hB f₀ f₁ h0 h1 h01 a b
  have := hB.proper
  haveI hsub : Subsingleton (Sp k) := inferInstanceAs (Subsingleton (PrimeSpectrum k))
  let pt : Sp k := IsLocalRing.closedPoint k
  let e : B.left := (η[B] : 𝟙_ (Over (Sp k)) ⟶ B).left pt
  obtain ⟨_, ⟨W, hW, rfl⟩, heW, -⟩ :=
    B.left.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ e) isOpen_univ
  let L := Localization.Away (X : Polynomial k)
  let t : L := algebraMap (Polynomial k) L X
  let ti : L := IsLocalization.Away.invSelf (X : Polynomial k)
  have hti : t * ti = 1 := IsLocalization.Away.mul_invSelf (X : Polynomial k)
  let g₀ := famMap B f₀ h0 L t
  let g₁ := famMap B f₁ h1 L ti
  have hc := GlobalTheory.T.projectiveLine_chart_families_agree_on_overlap B f₀ f₁ h0 h1 h01 L t ti hti
  let V : Set (Sp L) := {τ | ∀ x : Sp (Polynomial L), spMap (algebraMap L (Polynomial L)) x = τ → g₀ x ∈ W ∧ g₁ x ∈ W}
  have hV : IsOpen V := GlobalTheory.T.isOpen_setOf_fibre_charts_mem L _ g₀ g₁ hc W

  have hfib : ∀ (χ : L →ₐ[k] k) (x' : Sp (Polynomial k)),
      spMap (algebraMap L (Polynomial L)) (spMap (Polynomial.mapRingHom (χ : L →+* k)) x') = spMap χ.toRingHom pt := by
    intro χ x'
    rw [← Scheme.Hom.comp_apply, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have : (Polynomial.mapRingHom (χ : L →+* k)).comp (algebraMap L (Polynomial L)) =
        (algebraMap k (Polynomial k)).comp (χ : L →+* k) := by
      ext z; simp [Polynomial.algebraMap_apply]
    rw [this, CommRingCat.ofHom_comp, Spec.map_comp, Scheme.Hom.comp_apply]
    congr 1
    exact hsub.elim _ _
  have hW₀ : ∀ χ : L →ₐ[k] k, spMap χ.toRingHom pt ∈ V →
      (∀ x', famMap B f₀ h0 k (χ t) x' ∈ W) ∧ (∀ x', famMap B f₁ h1 k (χ ti) x' ∈ W) := by
    intro χ hχ
    constructor
    · intro x'
      rw [← famMap_base B f₀ h0 χ t, Scheme.Hom.comp_apply]
      exact (hχ _ (hfib χ x')).1
    · intro x'
      rw [← famMap_base B f₁ h1 χ ti, Scheme.Hom.comp_apply]
      exact (hχ _ (hfib χ x')).2
  have hinW : ∀ R : Type, ∀ _ : CommRing R, ∀ _ : Algebra k R, ∀ (f : Sp (Polynomial k) ⟶ B.left)
      (hf : f ≫ B.hom = spMap (algebraMap k (Polynomial k))) (x : Sp (Polynomial R)), famMap B f hf R 1 x ∈ W := by
    intro R _ _ f hf x
    rw [famMap_one, Scheme.Hom.comp_apply]
    have hx : (spMap (algebraMap k (Polynomial R))) x = pt := hsub.elim _ _
    rw [hx]
    exact heW

  let χ₁ : L →ₐ[k] k := IsLocalization.liftAlgHom (M := Submonoid.powers (X : Polynomial k))
    (f := Polynomial.aeval (1 : k)) (by
      rintro ⟨_, n, rfl⟩
      simp)
  have hχ₁t : χ₁ t = 1 := by simp [χ₁, t]
  have hχ₁ti : χ₁ ti = 1 := by
    have := congrArg χ₁ hti
    rw [map_mul, hχ₁t, _root_.one_mul, map_one] at this
    exact this
  have h1V : spMap χ₁.toRingHom pt ∈ V := by
    intro x hx
    obtain ⟨x', rfl⟩ := GlobalTheory.T.mem_range_spMap_mapRingHom_of_fibre_closedPoint L k χ₁.toRingHom
      (fun z => ⟨algebraMap k L z, by simp⟩) x hx
    constructor
    · have := famMap_base B f₀ h0 χ₁ t
      rw [hχ₁t] at this
      rw [← Scheme.Hom.comp_apply]
      erw [this]
      exact hinW k _ _ f₀ h0 x'
    · have := famMap_base B f₁ h1 χ₁ ti
      rw [hχ₁ti] at this
      rw [← Scheme.Hom.comp_apply]
      erw [this]
      exact hinW k _ _ f₁ h1 x'
  have hF := GlobalTheory.T.finite_compl_punctured_line_open k V hV χ₁ h1V
  set F := {c : k | c ≠ 0 ∧ ∀ χ : L →ₐ[k] k, χ (algebraMap (Polynomial k) _ X) = c → spMap χ.toRingHom pt ∉ V}

  have hscale : ∀ c : k, c ≠ 0 → c ∉ F → ∀ a : k,
      spMap (Polynomial.evalRingHom (c * a)) ≫ f₀ = spMap (Polynomial.evalRingHom a) ≫ f₀ := by
    intro c hc0 hcF
    simp only [F, Set.mem_setOf_eq, not_and, not_forall, not_not] at hcF
    obtain ⟨χ, hχt, hχV⟩ := hcF hc0
    obtain ⟨hA, hB'⟩ := hW₀ χ hχV
    have hu : χ t * χ ti = 1 := by rw [← map_mul, hti, map_one]
    have hcmp := GlobalTheory.T.projectiveLine_chart_families_agree_on_overlap B f₀ f₁ h0 h1 h01 k (χ t) (χ ti) hu
    have key := GlobalTheory.T.eq_spMap_comp_eval_zero_of_chart_comp_eq k B.left W hW _ _ hA hB' hcmp
    have := scale_inv_of_famMap B f₀ h0 (χ t) key
    simpa [t, hχt] using this
  have hunit : ∀ c : k, c ≠ 0 → spMap (Polynomial.evalRingHom c) ≫ f₀ = spMap (Polynomial.evalRingHom 1) ≫ f₀ := by
    intro c hc
    have hfin : ((F ∪ {0}) ∪ (fun d => c / d) '' F).Finite :=
      (hF.union (Set.finite_singleton 0)).union (hF.image _)
    obtain ⟨d, hd⟩ := hfin.infinite_compl.nonempty
    simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_singleton_iff, Set.mem_image, not_or, not_exists,
      not_and] at hd
    obtain ⟨⟨hdF, hd0⟩, hd'⟩ := hd
    have hcd0 : c / d ≠ 0 := div_ne_zero hc hd0
    have hcdF : c / d ∉ F := fun h => hd' (c / d) h (by field_simp)
    have e1 := hscale d hd0 hdF (c / d * 1)
    have e2 := hscale (c / d) hcd0 hcdF 1
    rw [_root_.mul_one] at e1 e2
    rw [show d * (c / d) = c by field_simp] at e1
    rw [e1, e2]
  exact GlobalTheory.T.affineLine_morphism_constant_of_const_on_nonzero k B.left B.hom f₀ h0 hunit a b

end GlobalTheory.LineConst
