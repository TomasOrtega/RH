import Development.WeilBound.CoreStatements.VolumeEquality.BaseUnifEx2
import Development.WeilBound.CoreStatements.VolumeEquality.OnePieceB
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericPointGenericFibreStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericOfSmoothSurjectiveStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.StalkSurjectiveOpenImmersionStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsResolutionGenericFibreStatement

noncomputable section

namespace SheetDecomposition

open AlgebraicGeometry CategoryTheory Limits NumberField Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

namespace One

/- English proof (translation)
Use `show Spec.map (CommRingCat.ofHom (g.comp f)) = _`. Rewrite using `[CommRingCat.ofHom_comp, Spec.map_comp]`.
-/
theorem spMap_comp' {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (f : R →+* S) (g : S →+* T) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  show Spec.map (CommRingCat.ofHom (g.comp f)) = _
  rw [CommRingCat.ofHom_comp, Spec.map_comp]

/- English proof (translation)
The claim follows from `congrArg CommRingCat.Hom.hom (Spec.map_injective h)`.
-/
theorem spMap_inj {R S : Type} [CommRing R] [CommRing S] {f g : R →+* S} (h : spMap f = spMap g) : f = g :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective h)

/- English proof (translation)
Substitute `e e' e₂` using the available equality. Rewrite using `[← Category.assoc (Spec.map _), ← Spec.map_comp, IsIso.hom_inv_id_assoc, Spec.map_comp, Category.assoc]`.
-/
theorem spec_map_factorisation {X : Scheme.{0}} {A A' B B' : CommRingCat.{0}} (u : A ⟶ B) [IsIso u] (r : A ⟶ A') (v : A' ⟶ B')
    (a : Spec A ⟶ X) (a' : Spec A' ⟶ X) (x : Spec B ⟶ X) (x' : Spec B' ⟶ X) (e : Spec.map u ≫ a = x)
    (e' : Spec.map v ≫ a' = x') (e₂ : Spec.map r ≫ a = a') : Spec.map (inv u ≫ r ≫ v) ≫ x = x' := by
  subst e e' e₂
  rw [← Category.assoc (Spec.map _), ← Spec.map_comp, IsIso.hom_inv_id_assoc, Spec.map_comp, Category.assoc]

/- English proof (translation)
Use `haveI : IsIso (Scheme.stalkClosedPointTo ξ₀) := (ConcreteCategory.isIso_iff_bijective _).2 h₀.bij`. Use `⟨(inv (Scheme.stalkClosedPointTo ξ₀) ≫ X.presheaf.stalkSpecializes h ≫ Scheme.stalkClosedPointTo ξ₁).hom, ?_⟩` and prove the remaining obligations. Conclude with `spec_map_factorisation (Scheme.stalkClosedPointTo ξ₀) (X.presheaf.stalkSpecializes h) (Scheme.stalkClosedPointTo ξ₁) _ _ ξ₀ ξ₁ (Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ₀) (Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ₁) (Scheme.SpecMap_stalkSpecializes_fromSpecStalk (X := …`.
-/
theorem exists_factor {X : Scheme.{0}} {Ω₀ Ω₁ : Type} [Field Ω₀] [Field Ω₁] {ξ₀ : Sp Ω₀ ⟶ X} (ξ₁ : Sp Ω₁ ⟶ X)
    (h₀ : IsCptGen ξ₀) (h : genPt ξ₁ ⤳ genPt ξ₀) : ∃ i : Ω₀ →+* Ω₁, spMap i ≫ ξ₀ = ξ₁ := by
  haveI : IsIso (Scheme.stalkClosedPointTo ξ₀) := (ConcreteCategory.isIso_iff_bijective _).2 h₀.bij
  refine ⟨(inv (Scheme.stalkClosedPointTo ξ₀) ≫ X.presheaf.stalkSpecializes h ≫ Scheme.stalkClosedPointTo ξ₁).hom, ?_⟩
  exact spec_map_factorisation (Scheme.stalkClosedPointTo ξ₀) (X.presheaf.stalkSpecializes h) (Scheme.stalkClosedPointTo ξ₁) _ _ ξ₀ ξ₁
    (Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ₀) (Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ₁)
    (Scheme.SpecMap_stalkSpecializes_fromSpecStalk (X := X) h)

/- English proof (translation)
The claim follows from `IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 F)) h`.
-/
theorem ext_int {F Ω : Type} [Field F] [NumberField F] [Field Ω] {f g : F →+* Ω}
    (h : f.comp (algebraMap (𝓞 F) F) = g.comp (algebraMap (𝓞 F) F)) : f = g :=
  IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 F)) h

/- English proof (translation)
Introduce `a ha`. Use `haveI : Algebra.IsAlgebraic ℤ F := (IsFractionRing.comap_isAlgebraic_iff (A := ℤ) (K := ℚ)).2 inferInstance`. Establish `h1 : IsAlgebraic ℤ a` using `ha.restrictScalars ℤ`. Take `⟨x, hx⟩` from `halg (i a) (h1.algHom i.toIntAlgHom)`. Use `⟨x, 1, one_ne_zero, ?_⟩` and prove the remaining obligations.

Rewrite using `[map_one, mul_one]`. Use `(g.comp i).injective ?_` and prove the remaining obligations. Rewrite `hx` using `[← h]`. Conclude with `hx.symm`.
-/
theorem constClosed_of {F Ω₀ Ω₁ Ω₂ : Type} [Field F] [NumberField F] [Field Ω₀] [Field Ω₁] [Field Ω₂] [Algebra F Ω₀]
    (i : Ω₀ →+* Ω₁) (g : Ω₁ →+* Ω₂) (cst : F →+* Ω₂) (h : (g.comp i).comp (algebraMap F Ω₀) = cst)
    (halg : ∀ a : Ω₁, IsAlgebraic ℤ a → g a ∈ cst.range) : ConstClosed F Ω₀ := by
  intro a ha
  haveI : Algebra.IsAlgebraic ℤ F := (IsFractionRing.comap_isAlgebraic_iff (A := ℤ) (K := ℚ)).2 inferInstance
  have h1 : IsAlgebraic ℤ a := ha.restrictScalars ℤ
  obtain ⟨x, hx⟩ := halg (i a) (h1.algHom i.toIntAlgHom)
  refine ⟨x, 1, one_ne_zero, ?_⟩
  rw [map_one, mul_one]
  refine (g.comp i).injective ?_
  rw [← h] at hx
  exact hx.symm

/- English proof (translation)
Use `⟨IsFractionRing.injective _ _, inferInstance, fun x => ?_⟩` and prove the remaining obligations. Take `⟨a, b, hb, rfl⟩` from `IsFractionRing.div_surjective (A := 𝓞 F) x`. Establish `: algebraMap (𝓞 F) F b ≠ 0` using `IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb`. Conclude with `⟨a, b, this, div_mul_cancel₀ _ this⟩`.
-/
theorem int_frac (F : Type) [Field F] [NumberField F] : Function.Injective (algebraMap (𝓞 F) F) ∧ IsNoetherianRing (𝓞 F) ∧
    ∀ x : F, ∃ a b : 𝓞 F, algebraMap (𝓞 F) F b ≠ 0 ∧ x * algebraMap (𝓞 F) F b = algebraMap (𝓞 F) F a := by
  refine ⟨IsFractionRing.injective _ _, inferInstance, fun x => ?_⟩
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 F) x
  have : algebraMap (𝓞 F) F b ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  exact ⟨a, b, this, div_mul_cancel₀ _ this⟩

end One

open SheetDecomposition.One

/- English proof (translation)
Introduce `hgiven E _ _ _ H D l Xo c Y sm j j' n B Ω₀ _ ξ₀ Ω₁ Ω₂ _ _ ξ₁ g cst U hloc hξ₀ hpt hover halg hU hUc κ`. Take `⟨-, -, -, -, hRes, -⟩` from `hgiven`. Use `haveI : FiniteDimensional ℚ c.F := c.fin`. Use `haveI : NumberField c.F := {}`. Take `⟨i, hi⟩` from `exists_factor ξ₁ hξ₀ (hpt ▸ specializes_rfl)`.

Use `haveI : CharZero Ω₂ := (RingHom.charZero_iff cst.injective).1 inferInstance`. Use `haveI : CharZero Ω₀ := (g.comp i).charZero`. Take `⟨b, ξF, hF1, hF2, hFg⟩` from `GlobalTheory.T.generic_point_generic_fibre c.F Y.X Y.s Ω₀ ξ₀ hξ₀`. Use `letI : Algebra c.F Ω₀ := b.toAlgebra`. Establish `hb : (g.comp i).comp b = cst`.

Use `ext_int (spMap_inj ?_)` and prove the remaining obligations. Rewrite using `[← hover, ← hi, ← hF1, spMap_comp', spMap_comp', spMap_comp', ← hF2]`. Simplify using `only [Category.assoc, pullback.condition]`. Establish `hcl : ConstClosed c.F Ω₀` using `constClosed_of i g cst hb halg`. Establish `hβ` using `int_frac c.F`.

Take `⟨hnoeth, X', f, d, W', jW, hiso, hjW, -, -, hsm, -⟩` from `GlobalTheory.T.exists_resolution_generic_fibre hRes E H D l Xo c _ _ Y hβ`. Use `haveI := Y.jQ_open`. Use `haveI hpre : IsPreimmersion (pullback.fst Y.s (spMap (algebraMap (𝓞 c.F) c.F))) := by`. Establish `h : IsPreimmersion (spMap (algebraMap (𝓞 c.F) c.F))` using `IsPreimmersion.of_isLocalization (R := 𝓞 c.F) (S := c.F) (nonZeroDivisors (𝓞 c.F))`. Use `infer_instance`.

Establish `hsurj` using `GlobalTheory.T.stalk_surjective_open_immersion _ _ _ _ _ f W' jW Y.jQ hpre inferInstance hiso hjW`. Use `haveI hopen : IsOpenImmersion (W'.ι ≫ f) := by rw [← hjW]; infer_instance`. Establish `hrange : Set.range (W'.ι ≫ f) = Set.range Y.jQ`. Rewrite using `[← hjW, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Set.range_eq_univ.2 (show Function.Surjective jW from jW.homeomorph.surjective), Set.image_univ]`. Establish `hlift : ∀ (R : Type) [Field R] (z : Sp R ⟶ pullback Y.s (spMap (algebraMap (𝓞 c.F) c.F))), centre z ∈ Set.range Y.jQ → ∃ z' : Sp R ⟶ W'.toScheme, z' ≫ W'.ι ≫ f = z`.

Introduce `R _ z hz`. Use `⟨IsOpenImmersion.lift (W'.ι ≫ f) z ?_, IsOpenImmersion.lift_fac _ _ _⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨q, rfl⟩`. Establish `: q = IsLocalRing.closedPoint R` using `Subsingleton.elim (α := PrimeSpectrum R) _ _`. Rewrite using `[hrange, this]`.

Conclude with `hz`. Take `⟨π, hπ⟩ : ∃ π, π = f ≫ pullback.fst Y.s (spMap (algebraMap (𝓞 c.F) c.F))` from `⟨_, rfl⟩`. Take `⟨s', hs'⟩ : ∃ s', s' = f ≫ pullback.snd Y.s (spMap (algebraMap (𝓞 c.F) c.F))` from `⟨_, rfl⟩`. Use `haveI hemb : IsPreimmersion (W'.ι ≫ π) := by`. Rewrite using `[hπ, ← Category.assoc]`.

Use `infer_instance`. Rewrite `hsurj` using `[← hπ]`. Rewrite `hsm` using `[← hs']`. Establish `hsm' : Smooth s'` using `SmoothOfRelativeDimension.smooth d s'`. Establish `hπs : π ≫ Y.s = s' ≫ spMap (algebraMap (𝓞 c.F) c.F)`.

Rewrite using `[hπ, hs', Category.assoc, Category.assoc, pullback.condition]`. Take `⟨ξW, hξW⟩` from `hlift Ω₀ ξF (genPt_mem_dense Y.jQ.opensRange hFg (by simpa using Y.jQ_dense))`. Establish `h2 : (ξW ≫ W'.ι) ≫ π = ξ₀`. Rewrite using `[hπ, ← hF1, ← hξW]`. Simplify using `only [Category.assoc]`.

Establish `h3 : (ξW ≫ W'.ι) ≫ s' = spMap (algebraMap c.F Ω₀)`. Use `Eq.trans ?_ hF2` and prove the remaining obligations. Rewrite using `[hs', ← hξW]`. Simplify using `only [Category.assoc]`. Establish `hgW : genPt (ξW ≫ W'.ι) ∈ W'` using `(genPt ξW).2`.

Establish `hξg : IsCptGen (ξW ≫ W'.ι)` using `GlobalTheory.T.generic_of_smooth_surjective c.F _ _ _ _ _ π s' hsm' h2 hξ₀ (hsurj _ hgW)`. Establish `hab : ∀ x : Sp ℂ ⟶ X', ⊤ ≤ x ⁻¹ᵁ W' → centre (x ≫ π) ∈ abLocus Y.t.G`. Introduce `x hx`. Establish `h1 : f (centre x) ∈ Set.range Y.jQ`. Rewrite using `[← hrange]`.

Conclude with `⟨⟨centre x, GagaRat.centre_mem hx⟩, rfl⟩`. Rewrite `h1` using `[← Y.ab_gen]`. Rewrite using `[hπ]`. Conclude with `h1`. Establish `hexF : ∀ x : Sp ℂ ⟶ X', ∃ r : ℂ, r ≠ 0 ∧ ∀ k, ∀ t ∈ Cusp.ballDom (B.F k).q, x ≫ π = B.pt k t → r = (((k : ℕ) + 1 : ℕ) : ℂ)`.

Introduce `x`. Distinguish the cases in `h : ∃ k, ∃ t ∈ Cusp.ballDom (B.F k).q, x ≫ π = B.pt k t`. Take `⟨k, t, ht, e⟩` from `h`. Use `⟨(((k : ℕ) + 1 : ℕ) : ℂ), Nat.cast_ne_zero.2 (Nat.succ_ne_zero _), fun k' t' ht' e' => ?_⟩` and prove the remaining obligations. Rewrite using `[B.disj k k' t ht t' ht' (e.symm.trans e')]`.

Conclude with `⟨1, one_ne_zero, fun k t ht e => absurd ⟨k, t, ht, e⟩ h⟩`. Use `choose F _ hF using hexF`. Establish `hconst` using `const_of_hol κ s' (ξW ≫ W'.ι) W' F d hsm h3 hξg hcl (by`. Introduce `m T y hT hc hy hW b₁ hb₁ b₂ hb₂`. Take `⟨k₁, t₁, ht₁, e₁⟩` from `B.onto _ (hab _ (hW b₁ hb₁))`.

Take `⟨k₂, t₂, ht₂, e₂⟩` from `B.onto _ (hab _ (hW b₂ hb₂))`. Rewrite using `[hF _ k₁ t₁ ht₁ e₁.symm, hF _ k₂ t₂ ht₂ e₂.symm, hloc m T (fun b => y b ≫ π) hT hc (GagaRat.isHolTo_comp π hy) (fun b hb => hab _ (hW b hb)) b₁ hb₁ b₂ hb₂ k₁ k₂ t₁ ht₁ t₂ ht₂ e₁.symm e₂.symm])`. Establish `hup : ∀ k, B.κ k = κ → ∀ t ∈ Cusp.ballDom (B.F k).q, ⊤ ≤ B.pt k t ⁻¹ᵁ U → ∃ x : Sp ℂ ⟶ X', x ≫ π = B.pt k t ∧ x ≫ s' = spMap κ ∧ ⊤ ≤ x ⁻¹ᵁ W' ∧ genPt (ξW ≫ W'.ι) ⤳ centre x`. Introduce `k hk t ht hu`. Set `z : Sp ℂ ⟶ pullback Y.s (spMap (algebraMap (𝓞 c.F) c.F))` to `pullback.lift (B.pt k t) (spMap κ) (by rw [B.comp_s_eq_spMap_of_isOver k t ht, hk, spMap_comp'])`.

Establish `z1 : z ≫ pullback.fst _ _ = B.pt k t` using `pullback.lift_fst _ _ _`. Establish `z2 : z ≫ pullback.snd _ _ = spMap κ` using `pullback.lift_snd _ _ _`. Take `⟨z', hz'⟩` from `hlift ℂ z (by`. Rewrite using `[← Y.ab_gen]`. Use `B.interior k t ht` as an intermediate fact.

Rewrite `this` using `[← z1]`. Conclude with `this)`. Establish `a1 : (z' ≫ W'.ι) ≫ π = B.pt k t`. Rewrite using `[hπ, ← z1, ← hz']`. Simplify using `only [Category.assoc]`.

Use `⟨z' ≫ W'.ι, a1, ?_, GagaRat.top_le_of_centre_mem (centre z').2, ?_⟩` and prove the remaining obligations. Rewrite using `[hs', ← z2, ← hz']`. Simplify using `only [Category.assoc]`. Establish `a2` using `hUc _ hu`. Rewrite `a2` using `[← a1, ← h2, Category.assoc, Category.assoc]`.

Establish `a3 : genPt ξW ⤳ centre z'` using `(W'.ι ≫ π).isEmbedding.isInducing.specializes_iff.1 a2`. Conclude with `a3.map W'.ι.continuous`. Establish `hgU : genPt (ξW ≫ W'.ι) ∈ W' ⊓ π ⁻¹ᵁ U`. Use `⟨hgW, ?_⟩` and prove the remaining obligations. Rewrite `hU` using `[← h2]`.

Conclude with `hU`. Take `⟨x, hx, hxU⟩` from `exists_point κ s' _ hgU`. Take `⟨k, t, ht, e⟩` from `B.onto _ (hab x fun q hq => (hxU hq).1)`. Establish `hk : B.κ k = κ`. Use `ext_int (spMap_inj ?_)` and prove the remaining obligations.

Rewrite using `[← B.comp_s_eq_spMap_of_isOver k t ht, e, Category.assoc, hπs, ← Category.assoc, hx, spMap_comp']`. Establish `hu : ⊤ ≤ B.pt k t ⁻¹ᵁ U`. Rewrite using `[e]`. Conclude with `fun q hq => (hxU hq).2`. Use `⟨k, ⟨hk, t, ht, hu⟩, ?_⟩` and prove the remaining obligations.

Introduce and unpack `k' ⟨hk', t', ht', hu'⟩`. Take `⟨x₁, a₁, b₁, c₁, d₁⟩` from `hup k hk t ht hu`. Take `⟨x₂, a₂, b₂, c₂, d₂⟩` from `hup k' hk' t' ht' hu'`. Use `hconst x₂ x₁ b₂ b₁ c₂ c₁ d₂ d₁` as an intermediate fact. Rewrite `this` using `[hF _ k t ht a₁, hF _ k' t' ht' a₂]`.

Conclude with `Fin.ext (Nat.succ_injective (Nat.cast_injective this))`.
-/
theorem onePiece : OnePiece := by
  intro hgiven E _ _ _ H D l Xo c Y sm j j' n B Ω₀ _ ξ₀ Ω₁ Ω₂ _ _ ξ₁ g cst U hloc hξ₀ hpt hover halg hU hUc κ
  classical
  obtain ⟨-, -, -, -, hRes, -⟩ := hgiven
  haveI : FiniteDimensional ℚ c.F := c.fin
  haveI : NumberField c.F := {}
  obtain ⟨i, hi⟩ := exists_factor ξ₁ hξ₀ (hpt ▸ specializes_rfl)
  haveI : CharZero Ω₂ := (RingHom.charZero_iff cst.injective).1 inferInstance
  haveI : CharZero Ω₀ := (g.comp i).charZero
  obtain ⟨b, ξF, hF1, hF2, hFg⟩ := GlobalTheory.T.generic_point_generic_fibre c.F Y.X Y.s Ω₀ ξ₀ hξ₀
  letI : Algebra c.F Ω₀ := b.toAlgebra
  have hb : (g.comp i).comp b = cst := by
    refine ext_int (spMap_inj ?_)
    rw [← hover, ← hi, ← hF1, spMap_comp', spMap_comp', spMap_comp', ← hF2]
    simp only [Category.assoc, pullback.condition]
  have hcl : ConstClosed c.F Ω₀ := constClosed_of i g cst hb halg
  have hβ := int_frac c.F
  obtain ⟨hnoeth, X', f, d, W', jW, hiso, hjW, -, -, hsm, -⟩ := GlobalTheory.T.exists_resolution_generic_fibre hRes E H D l Xo c _ _ Y hβ
  haveI := Y.jQ_open
  haveI hpre : IsPreimmersion (pullback.fst Y.s (spMap (algebraMap (𝓞 c.F) c.F))) := by
    have h : IsPreimmersion (spMap (algebraMap (𝓞 c.F) c.F)) :=
      IsPreimmersion.of_isLocalization (R := 𝓞 c.F) (S := c.F) (nonZeroDivisors (𝓞 c.F))
    infer_instance
  have hsurj := GlobalTheory.T.stalk_surjective_open_immersion _ _ _ _ _ f W' jW Y.jQ hpre inferInstance hiso hjW
  haveI hopen : IsOpenImmersion (W'.ι ≫ f) := by rw [← hjW]; infer_instance
  have hrange : Set.range (W'.ι ≫ f) = Set.range Y.jQ := by
    rw [← hjW, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      Set.range_eq_univ.2 (show Function.Surjective jW from jW.homeomorph.surjective), Set.image_univ]
  have hlift : ∀ (R : Type) [Field R] (z : Sp R ⟶ pullback Y.s (spMap (algebraMap (𝓞 c.F) c.F))),
      centre z ∈ Set.range Y.jQ → ∃ z' : Sp R ⟶ W'.toScheme, z' ≫ W'.ι ≫ f = z := by
    intro R _ z hz
    refine ⟨IsOpenImmersion.lift (W'.ι ≫ f) z ?_, IsOpenImmersion.lift_fac _ _ _⟩
    rintro _ ⟨q, rfl⟩
    have : q = IsLocalRing.closedPoint R := Subsingleton.elim (α := PrimeSpectrum R) _ _
    rw [hrange, this]
    exact hz
  obtain ⟨π, hπ⟩ : ∃ π, π = f ≫ pullback.fst Y.s (spMap (algebraMap (𝓞 c.F) c.F)) := ⟨_, rfl⟩
  obtain ⟨s', hs'⟩ : ∃ s', s' = f ≫ pullback.snd Y.s (spMap (algebraMap (𝓞 c.F) c.F)) := ⟨_, rfl⟩
  haveI hemb : IsPreimmersion (W'.ι ≫ π) := by
    rw [hπ, ← Category.assoc]
    infer_instance
  rw [← hπ] at hsurj
  rw [← hs'] at hsm
  have hsm' : Smooth s' := SmoothOfRelativeDimension.smooth d s'
  have hπs : π ≫ Y.s = s' ≫ spMap (algebraMap (𝓞 c.F) c.F) := by
    rw [hπ, hs', Category.assoc, Category.assoc, pullback.condition]
  obtain ⟨ξW, hξW⟩ := hlift Ω₀ ξF
    (genPt_mem_dense Y.jQ.opensRange hFg (by simpa using Y.jQ_dense))
  have h2 : (ξW ≫ W'.ι) ≫ π = ξ₀ := by
    rw [hπ, ← hF1, ← hξW]
    simp only [Category.assoc]
  have h3 : (ξW ≫ W'.ι) ≫ s' = spMap (algebraMap c.F Ω₀) := by
    refine Eq.trans ?_ hF2
    rw [hs', ← hξW]
    simp only [Category.assoc]
  have hgW : genPt (ξW ≫ W'.ι) ∈ W' := (genPt ξW).2
  have hξg : IsCptGen (ξW ≫ W'.ι) := GlobalTheory.T.generic_of_smooth_surjective c.F _ _ _ _ _ π s' hsm' h2 hξ₀ (hsurj _ hgW)
  have hab : ∀ x : Sp ℂ ⟶ X', ⊤ ≤ x ⁻¹ᵁ W' → centre (x ≫ π) ∈ abLocus Y.t.G := by
    intro x hx
    have h1 : f (centre x) ∈ Set.range Y.jQ := by
      rw [← hrange]
      exact ⟨⟨centre x, GagaRat.centre_mem hx⟩, rfl⟩
    rw [← Y.ab_gen] at h1
    rw [hπ]
    exact h1
  have hexF : ∀ x : Sp ℂ ⟶ X', ∃ r : ℂ, r ≠ 0 ∧ ∀ k, ∀ t ∈ Cusp.ballDom (B.F k).q, x ≫ π = B.pt k t →
      r = (((k : ℕ) + 1 : ℕ) : ℂ) := by
    intro x
    by_cases h : ∃ k, ∃ t ∈ Cusp.ballDom (B.F k).q, x ≫ π = B.pt k t
    · obtain ⟨k, t, ht, e⟩ := h
      refine ⟨(((k : ℕ) + 1 : ℕ) : ℂ), Nat.cast_ne_zero.2 (Nat.succ_ne_zero _), fun k' t' ht' e' => ?_⟩
      rw [B.disj k k' t ht t' ht' (e.symm.trans e')]
    · exact ⟨1, one_ne_zero, fun k t ht e => absurd ⟨k, t, ht, e⟩ h⟩
  choose F _ hF using hexF
  have hconst := const_of_hol κ s' (ξW ≫ W'.ι) W' F d hsm h3 hξg hcl (by
    intro m T y hT hc hy hW b₁ hb₁ b₂ hb₂
    obtain ⟨k₁, t₁, ht₁, e₁⟩ := B.onto _ (hab _ (hW b₁ hb₁))
    obtain ⟨k₂, t₂, ht₂, e₂⟩ := B.onto _ (hab _ (hW b₂ hb₂))
    rw [hF _ k₁ t₁ ht₁ e₁.symm, hF _ k₂ t₂ ht₂ e₂.symm,
      hloc m T (fun b => y b ≫ π) hT hc (GagaRat.isHolTo_comp π hy) (fun b hb => hab _ (hW b hb)) b₁ hb₁ b₂ hb₂ k₁ k₂
        t₁ ht₁ t₂ ht₂ e₁.symm e₂.symm])
  have hup : ∀ k, B.κ k = κ → ∀ t ∈ Cusp.ballDom (B.F k).q, ⊤ ≤ B.pt k t ⁻¹ᵁ U → ∃ x : Sp ℂ ⟶ X',
      x ≫ π = B.pt k t ∧ x ≫ s' = spMap κ ∧ ⊤ ≤ x ⁻¹ᵁ W' ∧ genPt (ξW ≫ W'.ι) ⤳ centre x := by
    intro k hk t ht hu
    let z : Sp ℂ ⟶ pullback Y.s (spMap (algebraMap (𝓞 c.F) c.F)) :=
      pullback.lift (B.pt k t) (spMap κ) (by rw [B.comp_s_eq_spMap_of_isOver k t ht, hk, spMap_comp'])
    have z1 : z ≫ pullback.fst _ _ = B.pt k t := pullback.lift_fst _ _ _
    have z2 : z ≫ pullback.snd _ _ = spMap κ := pullback.lift_snd _ _ _
    obtain ⟨z', hz'⟩ := hlift ℂ z (by
      rw [← Y.ab_gen]
      have := B.interior k t ht
      rw [← z1] at this
      exact this)
    have a1 : (z' ≫ W'.ι) ≫ π = B.pt k t := by
      rw [hπ, ← z1, ← hz']
      simp only [Category.assoc]
    refine ⟨z' ≫ W'.ι, a1, ?_, GagaRat.top_le_of_centre_mem (centre z').2, ?_⟩
    · rw [hs', ← z2, ← hz']
      simp only [Category.assoc]
    · have a2 := hUc _ hu
      rw [← a1, ← h2, Category.assoc, Category.assoc] at a2
      have a3 : genPt ξW ⤳ centre z' := (W'.ι ≫ π).isEmbedding.isInducing.specializes_iff.1 a2
      exact a3.map W'.ι.continuous
  have hgU : genPt (ξW ≫ W'.ι) ∈ W' ⊓ π ⁻¹ᵁ U := by
    refine ⟨hgW, ?_⟩
    rw [← h2] at hU
    exact hU
  obtain ⟨x, hx, hxU⟩ := exists_point κ s' _ hgU
  obtain ⟨k, t, ht, e⟩ := B.onto _ (hab x fun q hq => (hxU hq).1)
  have hk : B.κ k = κ := by
    refine ext_int (spMap_inj ?_)
    rw [← B.comp_s_eq_spMap_of_isOver k t ht, e, Category.assoc, hπs, ← Category.assoc, hx, spMap_comp']
  have hu : ⊤ ≤ B.pt k t ⁻¹ᵁ U := by
    rw [e]
    exact fun q hq => (hxU hq).2
  refine ⟨k, ⟨hk, t, ht, hu⟩, ?_⟩
  rintro k' ⟨hk', t', ht', hu'⟩
  obtain ⟨x₁, a₁, b₁, c₁, d₁⟩ := hup k hk t ht hu
  obtain ⟨x₂, a₂, b₂, c₂, d₂⟩ := hup k' hk' t' ht' hu'
  have := hconst x₂ x₁ b₂ b₁ c₂ c₁ d₂ d₁
  rw [hF _ k t ht a₁, hF _ k' t' ht' a₂] at this
  exact Fin.ext (Nat.succ_injective (Nat.cast_injective this))

end SheetDecomposition
