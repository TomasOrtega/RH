import Development.WeilBound.CoreStatements.FlagImmersions.FibSandwich
import Development.WeilBound.CoreStatements.VolumeEquality.OnePieceB
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RingOfIntegersHomInjective
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.InducedModelMorphismCompStructureMap
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericOfSmoothSurjectiveStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FamilyUniformisationLocalPeriodStatement
import Development.AbelianVarietyTheory.Statements.HyperbolicHypotheses.HypothesesInhabitedHyperbolic
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.RegularFunctionConstOfFiniteValuesAnyLevel

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl

namespace RootFieldNumerics.RF

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l}
  {c : Coeff l}

/- English proof (translation)
Use `⟨fun h => h ⟨_, rfl⟩, ?_⟩` and prove the remaining obligations. Introduce and unpack `h _ ⟨p, rfl⟩`. Take `rfl : p = IsLocalRing.closedPoint ℂ` from `Subsingleton.elim (α := PrimeSpectrum ℂ) _ _`. Conclude with `h`.
-/
theorem range_sub_iff {X : Scheme.{0}} (y : Sp ℂ ⟶ X) (U : Set X) : Set.range y ⊆ U ↔ centre y ∈ U := by
  refine ⟨fun h => h ⟨_, rfl⟩, ?_⟩
  rintro h _ ⟨p, rfl⟩
  obtain rfl : p = IsLocalRing.closedPoint ℂ := Subsingleton.elim (α := PrimeSpectrum ℂ) _ _
  exact h

/- English proof (translation)
Establish `hty' : IsTypeFn H (F.Di i).p (F.Di i).q ty`. Rewrite using `[(F.sig i).1, (F.sig i).2]`. Conclude with `hty`. Take `⟨B, Q, hBo, hBc, hQ, huniq⟩` from `GlobalTheory.exists_period_domain_param E H (F.Di i) g ty hty'`. Establish `hcond : spMap σ = spMap j ≫ spMap (IntermediateField.inclusion c.le).toRingHom`.

Rewrite using `[← F.over_σ i P hP, ← hx1, ← hx2, Category.assoc, Category.assoc, pullback.condition]`. Set `y : (Fin (F.Di i).dim → ℂ) → (Sp ℂ ⟶ Xo.XF c)` to `fun b => if hb : b ∈ B then pullback.lift (F.u i (Q b)) (spMap j) ((F.over_σ i _ (hQ.1 b hb)).trans hcond) else x`. Establish `hy1 : ∀ b ∈ B, y b ≫ pullback.fst _ _ = F.u i (Q b)` using `fun b hb => by`. Simplify using `only [y, dif_pos hb, pullback.lift_fst]`. Establish `hy2 : ∀ b ∈ B, y b ≫ pullback.snd _ _ = spMap j` using `fun b hb => by`.

Simplify using `only [y, dif_pos hb, pullback.lift_snd]`. Establish `hhol : IsHolTo B y` using `GlobalTheory.HolFibre.isHolTo_of_isPullback (IsPullback.of_hasPullback _ _) (GlobalTheory.LocLift.isHolTo_congr (F.hol i _ B Q hBo hQ).1 hy1) (GlobalTheory.LocLift.isHolTo_congr (GlobalTheory.HolFibre.isHolTo_const hBo (spMap j)) hy2)`. Establish `hfind : ∀ R, IsPeriod (F.Di i) ty R → ∀ z : Sp ℂ ⟶ Xo.XF c, z ≫ pullback.fst _ _ = F.u i R → z ≫ pullback.snd _ _ = spMap j → ∃ b ∈ B, y b = z`. Introduce `R hR z hz1 hz2`. Take `⟨b, ⟨hb, h, hh⟩, -⟩` from `huniq R hR`.

Use `⟨b, hb, pullback.hom_ext ?_ ?_⟩` and prove the remaining obligations. Rewrite using `[hy1 b hb, hz1]`. Conclude with `(F.fibre i _ _ (hQ.1 b hb) hR).2 ⟨LinearEquiv.refl _ _, h, fun _ _ => rfl, fun a _ => ⟨0, by simp⟩, fun a => ⟨0, by simp⟩, hh⟩`. Rewrite using `[hy2 b hb, hz2]`. Take `⟨b, hb, e⟩` from `hfind P hP x hx1 hx2`.

Take `⟨b', hb', e'⟩` from `hfind P' hP' x' hx1' hx2'`. Assume the negation of the conclusion as `hn`. Set `W : (Xo.XF c).Opens` to `⟨U, hU.isOpen⟩`. Set `W' : (Xo.XF c).Opens` to `⟨Uᶜ, hU.compl.isOpen⟩`. Take `⟨t, -, ht, ht'⟩` from `hBc.isPreconnected _ _ (hhol W 0).1 (hhol W' 0).1 (fun t ht => by`.

Distinguish the cases in `h : centre (y t) ∈ U`. Conclude with `Or.inl ⟨ht, GagaRat.top_le_of_centre_mem (show centre (y t) ∈ W from h)⟩`. Conclude with `Or.inr ⟨ht, GagaRat.top_le_of_centre_mem (show centre (y t) ∈ W' from h)⟩)`. Use the proof step `⟨b, hb, hb, GagaRat.top_le_of_centre_mem (show centre (y b) ∈ W from e ▸ hx)⟩`. Use the proof step `⟨b', hb', hb', GagaRat.top_le_of_centre_mem (show centre (y b') ∈ W' from e' ▸ hn)⟩`.

Conclude with `(GagaRat.centre_mem ht'.2 : centre (y t) ∈ W') (GagaRat.centre_mem ht.2 : centre (y t) ∈ W)`.
-/
theorem mem_of_period {σ : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)} (F : FamilyUnif Xo σ ty)
    (hty : IsTypeFn H D.p D.q ty) (j : c.F →+* ℂ) {U : Set (Xo.XF c)} (hU : IsClopen U) (i : Fin F.n)
    {P P' : (F.Di i).La →+ (Fin g → ℂ)} (hP : IsPeriod (F.Di i) ty P) (hP' : IsPeriod (F.Di i) ty P')
    {x x' : Sp ℂ ⟶ Xo.XF c} (hx1 : x ≫ pullback.fst _ _ = F.u i P) (hx2 : x ≫ pullback.snd _ _ = spMap j)
    (hx1' : x' ≫ pullback.fst _ _ = F.u i P') (hx2' : x' ≫ pullback.snd _ _ = spMap j) (hx : centre x ∈ U) :
    centre x' ∈ U := by
  classical
  have hty' : IsTypeFn H (F.Di i).p (F.Di i).q ty := by
    rw [(F.sig i).1, (F.sig i).2]
    exact hty
  obtain ⟨B, Q, hBo, hBc, hQ, huniq⟩ := GlobalTheory.exists_period_domain_param E H (F.Di i) g ty hty'
  have hcond : spMap σ = spMap j ≫ spMap (IntermediateField.inclusion c.le).toRingHom := by
    rw [← F.over_σ i P hP, ← hx1, ← hx2, Category.assoc, Category.assoc, pullback.condition]
  let y : (Fin (F.Di i).dim → ℂ) → (Sp ℂ ⟶ Xo.XF c) := fun b =>
    if hb : b ∈ B then pullback.lift (F.u i (Q b)) (spMap j) ((F.over_σ i _ (hQ.1 b hb)).trans hcond) else x
  have hy1 : ∀ b ∈ B, y b ≫ pullback.fst _ _ = F.u i (Q b) := fun b hb => by
    simp only [y, dif_pos hb, pullback.lift_fst]
  have hy2 : ∀ b ∈ B, y b ≫ pullback.snd _ _ = spMap j := fun b hb => by
    simp only [y, dif_pos hb, pullback.lift_snd]
  have hhol : IsHolTo B y :=
    GlobalTheory.HolFibre.isHolTo_of_isPullback (IsPullback.of_hasPullback _ _)
      (GlobalTheory.LocLift.isHolTo_congr (F.hol i _ B Q hBo hQ).1 hy1)
      (GlobalTheory.LocLift.isHolTo_congr (GlobalTheory.HolFibre.isHolTo_const hBo (spMap j)) hy2)
  have hfind : ∀ R, IsPeriod (F.Di i) ty R → ∀ z : Sp ℂ ⟶ Xo.XF c, z ≫ pullback.fst _ _ = F.u i R →
      z ≫ pullback.snd _ _ = spMap j → ∃ b ∈ B, y b = z := by
    intro R hR z hz1 hz2
    obtain ⟨b, ⟨hb, h, hh⟩, -⟩ := huniq R hR
    refine ⟨b, hb, pullback.hom_ext ?_ ?_⟩
    · rw [hy1 b hb, hz1]
      exact (F.fibre i _ _ (hQ.1 b hb) hR).2 ⟨LinearEquiv.refl _ _, h, fun _ _ => rfl,
        fun a _ => ⟨0, by simp⟩, fun a => ⟨0, by simp⟩, hh⟩
    · rw [hy2 b hb, hz2]
  obtain ⟨b, hb, e⟩ := hfind P hP x hx1 hx2
  obtain ⟨b', hb', e'⟩ := hfind P' hP' x' hx1' hx2'
  by_contra hn
  let W : (Xo.XF c).Opens := ⟨U, hU.isOpen⟩
  let W' : (Xo.XF c).Opens := ⟨Uᶜ, hU.compl.isOpen⟩
  obtain ⟨t, -, ht, ht'⟩ := hBc.isPreconnected _ _ (hhol W 0).1 (hhol W' 0).1
    (fun t ht => by
      by_cases h : centre (y t) ∈ U
      · exact Or.inl ⟨ht, GagaRat.top_le_of_centre_mem (show centre (y t) ∈ W from h)⟩
      · exact Or.inr ⟨ht, GagaRat.top_le_of_centre_mem (show centre (y t) ∈ W' from h)⟩)
    ⟨b, hb, hb, GagaRat.top_le_of_centre_mem (show centre (y b) ∈ W from e ▸ hx)⟩
    ⟨b', hb', hb', GagaRat.top_le_of_centre_mem (show centre (y b') ∈ W' from e' ▸ hn)⟩
  exact (GagaRat.centre_mem ht'.2 : centre (y t) ∈ W') (GagaRat.centre_mem ht.2 : centre (y t) ∈ W)

/- English proof (translation)
Establish `hemb : ∀ p : Sp ℂ ⟶ Xo.XF c, ∃ κ : c.F →+* ℂ, p ≫ pullback.snd _ _ = spMap κ` using `fun p => ⟨(Spec.preimage (p ≫ pullback.snd _ _)).hom, by`. Unfold `spMap`. Rewrite using `[CommRingCat.ofHom_hom, Spec.map_preimage]⟩`. Use `choose κ hκy using fun b => hemb (y b)`. Establish `hd : ∀ r : 𝓞 c.F, DifferentiableOn ℂ (fun b => κ b (r : c.F)) T` using `fun r => by`.

Establish `h3` using `(GagaRat.isHolTo_comp (pullback.snd _ _) hy ⊤ ((Scheme.ΓSpecIso (CommRingCat.of c.F)).inv (r : c.F))).2`. Establish `hset : T ⊆ {b ∈ T | ⊤ ≤ (y b ≫ pullback.snd _ _) ⁻¹ᵁ ⊤}` using `fun b hb => ⟨hb, le_top⟩`. Use `(h3.mono hset).congr fun b _ => ?_` and prove the remaining obligations. Use `show κ b (r : c.F) = valAt' (y b ≫ pullback.snd _ _) ⊤ _`. Rewrite using `[hκy b]`.

Conclude with `(PullbackSections.valAt'_spMap (κ b) (r : c.F)).symm`. Rewrite using `[hκy, hκy, GlobalTheory.CompanionTheory.Ar.Cusp.FamEx.embedding_const_preconnected hTc κ hd hb hb']`.
-/
theorem over_const [NumberField c.F] {m : ℕ} {T : Set (Fin m → ℂ)} {y : (Fin m → ℂ) → (Sp ℂ ⟶ Xo.XF c)}
    (hTc : IsPreconnected T) (hy : IsHolTo T y) {b b' : Fin m → ℂ} (hb : b ∈ T) (hb' : b' ∈ T) :
    y b ≫ pullback.snd _ _ = y b' ≫ pullback.snd _ _ := by
  have hemb : ∀ p : Sp ℂ ⟶ Xo.XF c, ∃ κ : c.F →+* ℂ, p ≫ pullback.snd _ _ = spMap κ := fun p =>
    ⟨(Spec.preimage (p ≫ pullback.snd _ _)).hom, by
      unfold spMap
      rw [CommRingCat.ofHom_hom, Spec.map_preimage]⟩
  choose κ hκy using fun b => hemb (y b)
  have hd : ∀ r : 𝓞 c.F, DifferentiableOn ℂ (fun b => κ b (r : c.F)) T := fun r => by
    have h3 := (GagaRat.isHolTo_comp (pullback.snd _ _) hy ⊤ ((Scheme.ΓSpecIso (CommRingCat.of c.F)).inv (r : c.F))).2
    have hset : T ⊆ {b ∈ T | ⊤ ≤ (y b ≫ pullback.snd _ _) ⁻¹ᵁ ⊤} := fun b hb => ⟨hb, le_top⟩
    refine (h3.mono hset).congr fun b _ => ?_
    show κ b (r : c.F) = valAt' (y b ≫ pullback.snd _ _) ⊤ _
    rw [hκy b]
    exact (PullbackSections.valAt'_spMap (κ b) (r : c.F)).symm
  rw [hκy, hκy, GlobalTheory.CompanionTheory.Ar.Cusp.FamEx.embedding_const_preconnected hTc κ hd hb hb']

/- English proof (translation)
Introduce `hG E _ _ _ H D l Xo c _ Y U Z hp hq hU _ hgeom`. Establish `hN : N1c` using `hG.1.2.2.1`. Take `⟨g, ty, hty⟩` from `GlobalTheory.AllClasses.exists_isTypeFn H D.p D.q`. Take `⟨FU⟩` from `hN E H D l Xo (algebraMap (KA l) ℂ) g ty (by omega) rfl hty`. Set `s : Xo.XF c ⟶ Sp c.F` to `pullback.snd _ _`.

Establish `hsm : SmoothOfRelativeDimension D.dim s` using `(smoothOfRelativeDimension_isStableUnderBaseChange D.dim).of_isPullback (IsPullback.of_hasPullback _ _) Xo.smooth`. Establish `hsm' : Smooth s` using `SmoothOfRelativeDimension.smooth D.dim s`. Use `haveI := Y.jQ_open`. Use `haveI : IsPreimmersion (spMap (algebraMap (𝓞 c.F) c.F)) := IsPreimmersion.of_isLocalization (nonZeroDivisors (𝓞 c.F)) (S := c.F)`. Use `haveI : IsPreimmersion Y.j := by show IsPreimmersion (Y.jQ ≫ pullback.fst _ _) infer_instance`.

Establish `hξ : IsCptGen Z.ξ₀` using `GlobalTheory.T.generic_of_smooth_surjective c.F _ _ _ _ _ Y.j s hsm' rfl Z.gen (Y.j.stalkMap_surjective _)`. Use `letI : Algebra c.F Z.Ω := Z.inc.toAlgebra`. Establish `hcl : ConstClosed c.F Z.Ω`. Introduce and unpack `a ⟨f, hf, hfa⟩`. Take `⟨x, hx⟩` from `hgeom a ⟨f, hf, hfa⟩`.

Conclude with `⟨x, 1, one_ne_zero, by rw [map_one, mul_one]; exact hx.symm⟩`. Establish `hover : ∀ x : Sp ℂ ⟶ Xo.XF c, x ≫ s = spMap (algebraMap c.F ℂ) → under x ≫ Xo.s = spMap (algebraMap (KA l) ℂ)`. Introduce `x hx`. Rewrite using `[Category.assoc, pullback.condition, ← Category.assoc]`. Use `erw [hx]`.

Conclude with `GagaRat.spMap_comp _ _`. Establish `hexF : ∀ x : Sp ℂ ⟶ Xo.XF c, ∃ r : ℂ, (x ≫ s ≠ spMap (algebraMap c.F ℂ) → r = 0) ∧ (x ≫ s = spMap (algebraMap c.F ℂ) → ∀ k P, IsPeriod (FU.Di k) ty P → FU.u k P = under x → r = ((k : ℕ) : ℂ))`. Introduce `x`. Distinguish the cases in `hx : x ≫ s = spMap (algebraMap c.F ℂ)`. Take `⟨k, P, hP, e⟩` from `FU.onto _ (hover x hx)`.

Conclude with `⟨((k : ℕ) : ℂ), fun h => absurd hx h, fun _ k' P' hP' e' => by rw [FU.disj k k' P P' hP hP' (e.trans e'.symm)]⟩`. Conclude with `⟨0, fun _ => rfl, fun h => absurd h hx⟩`. Use `choose F hF0 hF using hexF`. Establish `hconst` using `SheetDecomposition.One.const_of_hol (algebraMap c.F ℂ) s Z.ξ₀ ⊤ F D.dim hsm Z.over_inc hξ hcl (by`. Introduce `m T y hT hc hy _ b₁ hb₁ b₂ hb₂`.

Establish `hall : ∀ b ∈ T, y b ≫ s = y b₁ ≫ s` using `fun b hb => over_const hc hy hb hb₁`. Distinguish the cases in `h : y b₁ ≫ s = spMap (algebraMap c.F ℂ)`. Take `⟨i, hi⟩` from `GlobalTheory.T.family_uniformisation_local_period E H D l Xo _ g ty FU m T (fun b => under (y b)) hT hc ⟨b₁, hb₁⟩ (fun b hb => hover _ ((hall b hb).trans h)) (GagaRat.isHolTo_comp _ hy)`. Establish `key : ∀ b ∈ T, F (y b) = ((i : ℕ) : ℂ)` using `fun b hb => by`. Take `⟨B', P, -, m1, -, hP, e⟩` from `hi b hb`.

Conclude with `hF _ ((hall b hb).trans h) i (P b) (hP.1 b m1) (e b m1)`. Rewrite using `[key b₁ hb₁, key b₂ hb₂]`. Rewrite using `[hF0 _ h, hF0 _ (by rw [hall b₂ hb₂]; exact h)])`. Take `⟨x, hx, hxU⟩` from `SheetDecomposition.One.exists_point (algebraMap c.F ℂ) s ⟨U, hU.isOpen⟩ (q := genPt Z.ξ₀) Z.genPt_mem`. Establish `hxU' : centre x ∈ U` using `GagaRat.centre_mem hxU`.

Take `⟨i, P₀, hP₀, e₀⟩` from `FU.onto _ (hover x hx)`. Use `⟨g, ty, FU, i, hty, fun y hy => ?_⟩` and prove the remaining obligations. Rewrite using `[range_sub_iff]`. Prove the components needed by the constructor for the conclusion. Introduce `hyU`.

Take `⟨k, P, hP, e⟩` from `FU.onto _ (hover y hy)`. Use `hconst y x hy hx le_top le_top ((Z.closure _).1 hyU) ((Z.closure _).1 hxU')` as an intermediate fact. Rewrite `this` using `[hF _ hy k P hP e, hF _ hx i P₀ hP₀ e₀]`. Take `rfl : k = i` from `Fin.ext (Nat.cast_injective this)`. Conclude with `⟨P, hP, e.symm⟩`.

Introduce and unpack `⟨P, hP, e⟩`. Conclude with `mem_of_period FU hty _ hU i hP₀ hP e₀.symm hx e hy hxU'`.
-/
theorem periodOf : PeriodOf := by
  intro hG E _ _ _ H D l Xo c _ Y U Z hp hq hU _ hgeom
  classical
  have hN : N1c := hG.1.2.2.1
  obtain ⟨g, ty, hty⟩ := GlobalTheory.AllClasses.exists_isTypeFn H D.p D.q
  obtain ⟨FU⟩ := hN E H D l Xo (algebraMap (KA l) ℂ) g ty (by omega) rfl hty
  let s : Xo.XF c ⟶ Sp c.F := pullback.snd _ _
  have hsm : SmoothOfRelativeDimension D.dim s :=
    (smoothOfRelativeDimension_isStableUnderBaseChange D.dim).of_isPullback (IsPullback.of_hasPullback _ _) Xo.smooth
  have hsm' : Smooth s := SmoothOfRelativeDimension.smooth D.dim s
  haveI := Y.jQ_open
  haveI : IsPreimmersion (spMap (algebraMap (𝓞 c.F) c.F)) :=
    IsPreimmersion.of_isLocalization (nonZeroDivisors (𝓞 c.F)) (S := c.F)
  haveI : IsPreimmersion Y.j := by
    show IsPreimmersion (Y.jQ ≫ pullback.fst _ _)
    infer_instance
  have hξ : IsCptGen Z.ξ₀ := GlobalTheory.T.generic_of_smooth_surjective c.F _ _ _ _ _ Y.j s hsm' rfl Z.gen (Y.j.stalkMap_surjective _)
  letI : Algebra c.F Z.Ω := Z.inc.toAlgebra
  have hcl : ConstClosed c.F Z.Ω := by
    rintro a ⟨f, hf, hfa⟩
    obtain ⟨x, hx⟩ := hgeom a ⟨f, hf, hfa⟩
    exact ⟨x, 1, one_ne_zero, by rw [map_one, mul_one]; exact hx.symm⟩
  have hover : ∀ x : Sp ℂ ⟶ Xo.XF c, x ≫ s = spMap (algebraMap c.F ℂ) →
      under x ≫ Xo.s = spMap (algebraMap (KA l) ℂ) := by
    intro x hx
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    erw [hx]
    exact GagaRat.spMap_comp _ _
  have hexF : ∀ x : Sp ℂ ⟶ Xo.XF c, ∃ r : ℂ, (x ≫ s ≠ spMap (algebraMap c.F ℂ) → r = 0) ∧
      (x ≫ s = spMap (algebraMap c.F ℂ) → ∀ k P, IsPeriod (FU.Di k) ty P → FU.u k P = under x → r = ((k : ℕ) : ℂ)) := by
    intro x
    by_cases hx : x ≫ s = spMap (algebraMap c.F ℂ)
    · obtain ⟨k, P, hP, e⟩ := FU.onto _ (hover x hx)
      exact ⟨((k : ℕ) : ℂ), fun h => absurd hx h, fun _ k' P' hP' e' => by rw [FU.disj k k' P P' hP hP' (e.trans e'.symm)]⟩
    · exact ⟨0, fun _ => rfl, fun h => absurd h hx⟩
  choose F hF0 hF using hexF
  have hconst := SheetDecomposition.One.const_of_hol (algebraMap c.F ℂ) s Z.ξ₀ ⊤ F D.dim hsm Z.over_inc hξ hcl (by
    intro m T y hT hc hy _ b₁ hb₁ b₂ hb₂
    have hall : ∀ b ∈ T, y b ≫ s = y b₁ ≫ s := fun b hb => over_const hc hy hb hb₁
    by_cases h : y b₁ ≫ s = spMap (algebraMap c.F ℂ)
    · obtain ⟨i, hi⟩ := GlobalTheory.T.family_uniformisation_local_period E H D l Xo _ g ty FU m T (fun b => under (y b)) hT hc ⟨b₁, hb₁⟩
        (fun b hb => hover _ ((hall b hb).trans h)) (GagaRat.isHolTo_comp _ hy)
      have key : ∀ b ∈ T, F (y b) = ((i : ℕ) : ℂ) := fun b hb => by
        obtain ⟨B', P, -, m1, -, hP, e⟩ := hi b hb
        exact hF _ ((hall b hb).trans h) i (P b) (hP.1 b m1) (e b m1)
      rw [key b₁ hb₁, key b₂ hb₂]
    · rw [hF0 _ h, hF0 _ (by rw [hall b₂ hb₂]; exact h)])
  obtain ⟨x, hx, hxU⟩ := SheetDecomposition.One.exists_point (algebraMap c.F ℂ) s ⟨U, hU.isOpen⟩ (q := genPt Z.ξ₀) Z.genPt_mem
  have hxU' : centre x ∈ U := GagaRat.centre_mem hxU
  obtain ⟨i, P₀, hP₀, e₀⟩ := FU.onto _ (hover x hx)
  refine ⟨g, ty, FU, i, hty, fun y hy => ?_⟩
  rw [range_sub_iff]
  constructor
  · intro hyU
    obtain ⟨k, P, hP, e⟩ := FU.onto _ (hover y hy)
    have := hconst y x hy hx le_top le_top ((Z.closure _).1 hyU) ((Z.closure _).1 hxU')
    rw [hF _ hy k P hP e, hF _ hx i P₀ hP₀ e₀] at this
    obtain rfl : k = i := Fin.ext (Nat.cast_injective this)
    exact ⟨P, hP, e.symm⟩
  · rintro ⟨P, hP, e⟩
    exact mem_of_period FU hty _ hU i hP₀ hP e₀.symm hx e hy hxU'

end RootFieldNumerics.RF
