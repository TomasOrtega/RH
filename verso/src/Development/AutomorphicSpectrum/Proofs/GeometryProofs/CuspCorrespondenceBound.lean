import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.IsPshLocallyIntegrableStatement
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
import Development.AutomorphicSpectrum.Statements.GeometryStatements.NineGeoU
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.StalkClosedPointToGermTop
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsUnitIffUnitAt
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FinrankFiniteFlatTorsionSubschemeEqCardPoints
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

namespace GlobalTheory.CompanionTheory.Ar.Cusp.LabPt

/- English proof (translation)
Use `⟨h, (X.presheaf.germ ⊤ (centre z) trivial).hom (s.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom o)), Flat.ConstReg.genMap_germ_const ξ s hs ⟨centre z, h⟩ o, ?_⟩` and prove the remaining obligations. Establish `h1 : X.presheaf.germ ⊤ (centre z) trivial ≫ Scheme.stalkClosedPointTo z = z.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom`. Use `(Scheme.germ_stalkClosedPointTo z ⊤ trivial).trans ?_` and prove the remaining obligations. Simplify using `only [Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom, Scheme.Hom.appTop]`. Use `congr 1`.

Establish `h1'` using `congrArg (fun q => q.hom (s.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom o))) h1`. Use `h1'.trans ?_` and prove the remaining obligations. Establish `h2 : z.appTop.hom (s.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom o)) = (Spec.map (CommRingCat.ofHom ρ)).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom o)`. Rewrite using `[← hz]`. Simplify using `only [Scheme.Hom.comp_appTop]`.

Both sides reduce to the same expression. Establish `h3` using `congrArg (fun q => q.hom o) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom ρ))`. Establish `h3' : (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (ρ o) = (Spec.map (CommRingCat.ofHom ρ)).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom o)` using `h3`. Use `show (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom (z.appTop.hom (s.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom o))) = ρ o`. Rewrite using `[h2, ← h3']`.

Simplify using the standard rewrite rules.
-/
theorem valAt_of_const {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    {O : Type} [CommRing O] [Algebra O Ω] (s : X ⟶ Spec (CommRingCat.of O))
    (hs : ξ ≫ s = Spec.map (CommRingCat.ofHom (algebraMap O Ω))) {R : Type} [CommRing R] [IsLocalRing R]
    (z : Spec (CommRingCat.of R) ⟶ X) (ρ : O →+* R) (hz : z ≫ s = Spec.map (CommRingCat.ofHom ρ))
    (h : genPt ξ ⤳ centre z) (o : O) : ValAt ξ z (algebraMap O Ω o) (ρ o) := by
  refine ⟨h, (X.presheaf.germ ⊤ (centre z) trivial).hom
    (s.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom o)),
    Flat.ConstReg.genMap_germ_const ξ s hs ⟨centre z, h⟩ o, ?_⟩
  have h1 : X.presheaf.germ ⊤ (centre z) trivial ≫ Scheme.stalkClosedPointTo z =
      z.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom := by
    refine (Scheme.germ_stalkClosedPointTo z ⊤ trivial).trans ?_
    simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom, Scheme.Hom.appTop]
    congr 1
  have h1' := congrArg (fun q => q.hom (s.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom o))) h1
  refine h1'.trans ?_
  have h2 : z.appTop.hom (s.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom o)) =
      (Spec.map (CommRingCat.ofHom ρ)).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom o) := by
    rw [← hz]; simp only [Scheme.Hom.comp_appTop]; rfl
  have h3 := congrArg (fun q => q.hom o) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom ρ))
  have h3' : (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (ρ o) =
      (Spec.map (CommRingCat.ofHom ρ)).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom o) := h3
  show (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom (z.appTop.hom (s.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom o))) = ρ o
  rw [h2, ← h3']
  simp

/- English proof (translation)
Take `⟨φ, hφ, -⟩` from `ValHom.exists_valAt_hom X Ω ξ R z h hξ`. Take `⟨_, e₁⟩` from `(hφ a r).1 h₁`. Take `⟨_, e₂⟩` from `(hφ a r').1 h₂`. Conclude with `e₁.symm.trans e₂`.
-/
theorem valAt_unique {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (hξ : IsCptGen ξ)
    {R : Type} [CommRing R] [IsLocalRing R] (z : Spec (CommRingCat.of R) ⟶ X)
    (h : genPt ξ ⤳ centre z) {a : Ω} {r r' : R} (h₁ : ValAt ξ z a r) (h₂ : ValAt ξ z a r') : r = r' := by
  obtain ⟨φ, hφ, -⟩ := ValHom.exists_valAt_hom X Ω ξ R z h hξ
  obtain ⟨_, e₁⟩ := (hφ a r).1 h₁
  obtain ⟨_, e₂⟩ := (hφ a r').1 h₂
  exact e₁.symm.trans e₂

/- English proof (translation)
Establish `hk : RingHom.ker t = ⊥`. Apply `Ideal.eq_bot_of_comap_eq_bot (R := ℤ)` to reduce the goal to its premises. Use extensionality with `n`. Simplify using `[Ideal.mem_comap, RingHom.mem_ker]`. Conclude with `(RingHom.injective_iff_ker_eq_bot t).2 hk`.
-/
theorem injective_of_charZero {A : Type} [CommRing A] [IsDomain A] [Algebra.IsIntegral ℤ A] {L : Type} [Field L]
    [CharZero L] (t : A →+* L) : Function.Injective t := by
  have hk : RingHom.ker t = ⊥ := by
    apply Ideal.eq_bot_of_comap_eq_bot (R := ℤ)
    ext n
    simp [Ideal.mem_comap, RingHom.mem_ker]
  exact (RingHom.injective_iff_ker_eq_bot t).2 hk

/- English proof (translation)
Set `f : (𝓞 E →+* L) → (E →ₐ[ℚ] AlgebraicClosure L)` to `fun t => ((algebraMap L (AlgebraicClosure L)).comp (IsFractionRing.lift (K := E) (injective_of_charZero t))).toRatAlgHom`. Establish `hf : Function.Injective f`. Introduce `t t' h`. Use `RingHom.ext fun a => (algebraMap L (AlgebraicClosure L)).injective ?_` and prove the remaining obligations. Use `DFunLike.congr_fun h (algebraMap (𝓞 E) E a)` as an intermediate fact.

Simplify `this` using `[f]`. Establish `hc : Nat.card (E →ₐ[ℚ] AlgebraicClosure L) = Module.finrank ℚ E`. Rewrite using `[Nat.card_eq_fintype_card, AlgHom.card]`. Use `haveI : Finite (𝓞 E →+* L) := Finite.of_injective f hf`. Conclude with `⟨inferInstance, (Nat.card_le_card_of_injective f hf).trans hc.le⟩`.
-/
theorem card_hom_le (E : Type) [Field E] [NumberField E] (L : Type) [Field L] [CharZero L] :
    Finite (𝓞 E →+* L) ∧ Nat.card (𝓞 E →+* L) ≤ Module.finrank ℚ E := by
  let f : (𝓞 E →+* L) → (E →ₐ[ℚ] AlgebraicClosure L) := fun t =>
    ((algebraMap L (AlgebraicClosure L)).comp
      (IsFractionRing.lift (K := E) (injective_of_charZero t))).toRatAlgHom
  have hf : Function.Injective f := by
    intro t t' h
    refine RingHom.ext fun a => (algebraMap L (AlgebraicClosure L)).injective ?_
    have := DFunLike.congr_fun h (algebraMap (𝓞 E) E a)
    simpa [f] using this
  have hc : Nat.card (E →ₐ[ℚ] AlgebraicClosure L) = Module.finrank ℚ E := by
    rw [Nat.card_eq_fintype_card, AlgHom.card]
  haveI : Finite (𝓞 E →+* L) := Finite.of_injective f hf
  exact ⟨inferInstance, (Nat.card_le_card_of_injective f hf).trans hc.le⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

/- English proof (translation)
Take `⟨hfin, hle⟩` from `card_hom_le E L`. Use `hf.bijective_of_nat_card_le (hle.trans ?_)` and prove the remaining obligations. Rewrite using `[Nat.card_eq_of_bijective _ (LabelCount.labelCx_bijective H), Nat.card_eq_fintype_card, NumberField.Embeddings.card]`.
-/
theorem bijective_of_injective (H : Host E) {L : Type} [Field L] [CharZero L]
    (f : CMType H ⊕ CMType H → (𝓞 E →+* L)) (hf : Function.Injective f) : Function.Bijective f := by
  obtain ⟨hfin, hle⟩ := card_hom_le E L
  refine hf.bijective_of_nat_card_le (hle.trans ?_)
  rw [Nat.card_eq_of_bijective _ (LabelCount.labelCx_bijective H), Nat.card_eq_fintype_card,
    NumberField.Embeddings.card]

/- English proof (translation)
Establish `cc : ∀ s : 𝓞 E →+* ℂ, (starRingEnd ℂ).comp ((starRingEnd ℂ).comp s) = s` using `fun s => RingHom.ext fun a => by simp`. Establish `hf : Function.Injective f` using `fun a b h => Sum.inl_injective (hb.1 (a₁ := .inl a) (a₂ := .inl b) h)`. Establish `hg : Function.Injective g` using `fun a b h => Sum.inr_injective (hb.1 (a₁ := .inr a) (a₂ := .inr b) h)`. Establish `hd : ∀ a b, f a ≠ g b` using `fun a b h => by`. Use `hb.1 (a₁ := .inl a) (a₂ := .inr b) h` as an intermediate fact.

Simplify using `at this`. Use `⟨⟨hf, fun s => ⟨?_, fun hn => ?_⟩⟩, ⟨hg, fun s => ⟨?_, fun hn => ?_⟩⟩⟩` and prove the remaining obligations. Introduce and unpack `⟨τ, rfl⟩ ⟨τ', h⟩`. Conclude with `hd τ' τ (h.trans (hc τ).symm)`. Take `⟨x, hx⟩` from `hb.2 s`.

Break down `x with τ | τ` into its components or cases. Conclude with `⟨τ, hx⟩`. Establish `hx' : g τ = s` using `hx`. Conclude with `absurd ⟨τ, by rw [← hx', hc, cc]⟩ hn`. Introduce and unpack `⟨τ, rfl⟩ ⟨τ', h⟩`.

Use `hd τ τ' (Eq.symm (h.trans ?_))` and prove the remaining obligations. Rewrite using `[hc, cc]`. Take `⟨x, hx⟩` from `hb.2 s`. Break down `x with τ | τ` into its components or cases. Establish `hx' : f τ = s` using `hx`.

Conclude with `absurd ⟨τ, by rw [← hx', hc]⟩ hn`. Conclude with `⟨τ, hx⟩`.
-/
theorem isCMFam_of_bijective {A : Type} [Fintype A] (f g : A → (𝓞 E →+* ℂ))
    (hb : Function.Bijective (Sum.elim f g)) (hc : ∀ τ, g τ = (starRingEnd ℂ).comp (f τ)) :
    IsCMFam f ∧ IsCMFam g := by
  have cc : ∀ s : 𝓞 E →+* ℂ, (starRingEnd ℂ).comp ((starRingEnd ℂ).comp s) = s :=
    fun s => RingHom.ext fun a => by simp
  have hf : Function.Injective f := fun a b h =>
    Sum.inl_injective (hb.1 (a₁ := .inl a) (a₂ := .inl b) h)
  have hg : Function.Injective g := fun a b h =>
    Sum.inr_injective (hb.1 (a₁ := .inr a) (a₂ := .inr b) h)
  have hd : ∀ a b, f a ≠ g b := fun a b h => by
    have := hb.1 (a₁ := .inl a) (a₂ := .inr b) h
    simp at this
  refine ⟨⟨hf, fun s => ⟨?_, fun hn => ?_⟩⟩, ⟨hg, fun s => ⟨?_, fun hn => ?_⟩⟩⟩
  · rintro ⟨τ, rfl⟩ ⟨τ', h⟩
    exact hd τ' τ (h.trans (hc τ).symm)
  · obtain ⟨x, hx⟩ := hb.2 s
    rcases x with τ | τ
    · exact ⟨τ, hx⟩
    · have hx' : g τ = s := hx
      exact absurd ⟨τ, by rw [← hx', hc, cc]⟩ hn
  · rintro ⟨τ, rfl⟩ ⟨τ', h⟩
    refine hd τ τ' (Eq.symm (h.trans ?_))
    rw [hc, cc]
  · obtain ⟨x, hx⟩ := hb.2 s
    rcases x with τ | τ
    · have hx' : f τ = s := hx
      exact absurd ⟨τ, by rw [← hx', hc]⟩ hn
    · exact ⟨τ, hx⟩

/- English proof (translation)
Introduce `E _ _ _ H D l Xo c Y S Ω _ K _ J _ y 𝔐 L _ _ z`. Use `haveI : FiniteDimensional ℚ c.F := c.fin`. Use `haveI : NumberField c.F := { }`. Take `⟨ρ, hρ⟩ : ∃ ρ : 𝓞 c.F →+* L, spMap ρ = z ≫ 𝔐.f ≫ Y.s` from `⟨(Spec.preimage (z ≫ 𝔐.f ≫ Y.s)).hom, by simp [spMap]⟩`. Set `κ : c.F →+* L` to `IsFractionRing.lift (injective_of_charZero ρ)`.

Establish `hκ : ∀ o, κ (algebraMap (𝓞 c.F) c.F o) = ρ o` using `fun o => IsFractionRing.lift_algebraMap _ o`. Use `letI : Algebra (𝓞 c.F) Ω := (𝔐.cst.comp (algebraMap (𝓞 c.F) c.F)).toAlgebra`. Establish `hsp : genPt 𝔐.ξ ⤳ centre z` using `𝔐.all _`. Establish `hval : ∀ (s : CMType H ⊕ CMType H) (a : 𝓞 E), ValAt 𝔐.ξ z (𝔐.emb s a) (κ (labelEmb c s a))`. Introduce `s a`.

Establish `hint : IsIntegral ℤ (labelEmb c s a)` using `(NumberField.RingOfIntegers.isIntegral a).map (labelEmb c s).toIntAlgHom`. Establish `hm : algebraMap (𝓞 c.F) c.F (IsIntegralClosure.mk' (𝓞 c.F) _ hint) = labelEmb c s a` using `IsIntegralClosure.algebraMap_mk' _ _ hint`. Establish `h` using `valAt_of_const 𝔐.ξ (𝔐.f ≫ Y.s) 𝔐.cst_over z ρ hρ.symm hsp (IsIntegralClosure.mk' (𝓞 c.F) _ hint)`. Establish `he : algebraMap (𝓞 c.F) Ω (IsIntegralClosure.mk' (𝓞 c.F) _ hint) = 𝔐.emb s a` using `by show 𝔐.cst (algebraMap (𝓞 c.F) c.F (IsIntegralClosure.mk' (𝓞 c.F) _ hint)) = 𝔐.cst (labelEmb c s a)`. Rewrite using `[hm]`.

Rewrite `h` using `[he, ← hκ, hm]`. Conclude with `h`. Set `σ : CMType H ⊕ CMType H → (𝓞 E →+* L)` to `fun s => κ.comp (labelEmb c s)`. Establish `hinj : ∀ {L' : Type} [Field L'] (κ' : c.F →+* L'), Function.Injective fun s : CMType H ⊕ CMType H => κ'.comp (labelEmb c s)` using `fun κ' s t h => LabelCount.labelEmb_injective c (RingHom.ext fun a => κ'.injective (RingHom.congr_fun h a))`. Establish `hconj : ∀ (e : L →+* ℂ) (τ : CMType H), e.comp (σ (.inr τ)) = (starRingEnd ℂ).comp (e.comp (σ (.inl τ)))`.

Introduce `e τ`. Use `RingHom.ext fun a => ?_` and prove the remaining obligations. Set `ψ : E →+* ℂ` to `(e.comp κ).comp (τ.1.codRestrict c.F (c.conj τ.1))`. Use `show ψ ((H.bar a : 𝓞 E) : E) = starRingEnd ℂ (ψ (a : E))`. Rewrite using `[H.bar_eq, IsCMField.complexEmbedding_complexConj]`.

Use `⟨σ, hval, fun σ' h' => ?_, bijective_of_injective H σ (hinj κ), fun s => injective_of_charZero _, ?_, fun e => ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `s`. Use `RingHom.ext fun a => ?_` and prove the remaining obligations. Conclude with `valAt_unique 𝔐.ξ 𝔐.tie.gen z hsp (h' s a) (hval s a)`. Establish `h` using `(LabelCount.labels_injective_card E H l c c.F (RingHom.id _)).2`.

Rewrite `h` using `[Fintype.card_sum]`. Use linear arithmetic over natural numbers and integers. Establish `hb : Function.Bijective (fun s => e.comp (σ s))` using `bijective_of_injective H _ (hinj (e.comp κ))`. Establish `hb' : Function.Bijective (Sum.elim (fun τ => e.comp (σ (.inl τ))) fun τ => e.comp (σ (.inr τ)))`. Use `hb using 1` and compare the differences between its conclusion and the goal.

Use function extensionality and compare the values at `s`. Apply the tactic sequence `rcases s with τ | τ <;> rfl`. Take `⟨h1, h2⟩` from `isCMFam_of_bijective _ _ hb' (hconj e)`. Conclude with `⟨h1, h2, hconj e⟩`.
-/
theorem exists_labVal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (L : Type) [Field L] [CharZero L] (z : Sp L ⟶ 𝔐.X), ∃ σ : CMType H ⊕ CMType H → (𝓞 E →+* L), 𝔐.LabVal z id σ ∧ (∀ σ', 𝔐.LabVal z id σ' → σ' = σ) ∧ Function.Bijective σ ∧ (∀ s, Function.Injective (σ s)) ∧ 2 * Fintype.card (CMType H) = Module.finrank ℚ E ∧ ∀ e : L →+* ℂ, IsCMFam (fun τ => e.comp (σ (.inl τ))) ∧ IsCMFam (fun τ => e.comp (σ (.inr τ))) ∧ ∀ τ, e.comp (σ (.inr τ)) = (starRingEnd ℂ).comp (e.comp (σ (.inl τ))) := by
  intro E _ _ _ H D l Xo c Y S Ω _ K _ J _ y 𝔐 L _ _ z
  haveI : FiniteDimensional ℚ c.F := c.fin
  haveI : NumberField c.F := { }
  obtain ⟨ρ, hρ⟩ : ∃ ρ : 𝓞 c.F →+* L, spMap ρ = z ≫ 𝔐.f ≫ Y.s :=
    ⟨(Spec.preimage (z ≫ 𝔐.f ≫ Y.s)).hom, by simp [spMap]⟩
  let κ : c.F →+* L := IsFractionRing.lift (injective_of_charZero ρ)
  have hκ : ∀ o, κ (algebraMap (𝓞 c.F) c.F o) = ρ o := fun o => IsFractionRing.lift_algebraMap _ o
  letI : Algebra (𝓞 c.F) Ω := (𝔐.cst.comp (algebraMap (𝓞 c.F) c.F)).toAlgebra
  have hsp : genPt 𝔐.ξ ⤳ centre z := 𝔐.all _
  have hval : ∀ (s : CMType H ⊕ CMType H) (a : 𝓞 E), ValAt 𝔐.ξ z (𝔐.emb s a) (κ (labelEmb c s a)) := by
    intro s a
    have hint : IsIntegral ℤ (labelEmb c s a) :=
      (NumberField.RingOfIntegers.isIntegral a).map (labelEmb c s).toIntAlgHom
    have hm : algebraMap (𝓞 c.F) c.F (IsIntegralClosure.mk' (𝓞 c.F) _ hint) = labelEmb c s a :=
      IsIntegralClosure.algebraMap_mk' _ _ hint
    have h := valAt_of_const 𝔐.ξ (𝔐.f ≫ Y.s) 𝔐.cst_over z ρ hρ.symm hsp (IsIntegralClosure.mk' (𝓞 c.F) _ hint)
    have he : algebraMap (𝓞 c.F) Ω (IsIntegralClosure.mk' (𝓞 c.F) _ hint) = 𝔐.emb s a := by
      show 𝔐.cst (algebraMap (𝓞 c.F) c.F (IsIntegralClosure.mk' (𝓞 c.F) _ hint)) = 𝔐.cst (labelEmb c s a)
      rw [hm]
    rw [he, ← hκ, hm] at h
    exact h
  let σ : CMType H ⊕ CMType H → (𝓞 E →+* L) := fun s => κ.comp (labelEmb c s)
  have hinj : ∀ {L' : Type} [Field L'] (κ' : c.F →+* L'),
      Function.Injective fun s : CMType H ⊕ CMType H => κ'.comp (labelEmb c s) := fun κ' s t h =>
    LabelCount.labelEmb_injective c (RingHom.ext fun a => κ'.injective (RingHom.congr_fun h a))
  have hconj : ∀ (e : L →+* ℂ) (τ : CMType H),
      e.comp (σ (.inr τ)) = (starRingEnd ℂ).comp (e.comp (σ (.inl τ))) := by
    intro e τ
    refine RingHom.ext fun a => ?_
    let ψ : E →+* ℂ := (e.comp κ).comp (τ.1.codRestrict c.F (c.conj τ.1))
    show ψ ((H.bar a : 𝓞 E) : E) = starRingEnd ℂ (ψ (a : E))
    rw [H.bar_eq, IsCMField.complexEmbedding_complexConj]
  refine ⟨σ, hval, fun σ' h' => ?_, bijective_of_injective H σ (hinj κ), fun s => injective_of_charZero _, ?_,
    fun e => ?_⟩
  · funext s
    refine RingHom.ext fun a => ?_
    exact valAt_unique 𝔐.ξ 𝔐.tie.gen z hsp (h' s a) (hval s a)
  · have h := (LabelCount.labels_injective_card E H l c c.F (RingHom.id _)).2
    rw [Fintype.card_sum] at h
    omega
  · have hb : Function.Bijective (fun s => e.comp (σ s)) :=
      bijective_of_injective H _ (hinj (e.comp κ))
    have hb' : Function.Bijective (Sum.elim (fun τ => e.comp (σ (.inl τ))) fun τ => e.comp (σ (.inr τ))) := by
      convert hb using 1
      funext s
      rcases s with τ | τ <;> rfl
    obtain ⟨h1, h2⟩ := isCMFam_of_bijective _ _ hb' (hconj e)
    exact ⟨h1, h2, hconj e⟩

end GlobalTheory.CompanionTheory.Ar.Cusp.LabPt
