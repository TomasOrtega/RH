import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.ChartRange
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.SigmaLocal
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.ChartLift
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.PieceFacts

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz.G.PX

/- English proof (translation)
Assume the negation of the conclusion as `hn`. Use `push_neg at hn`. Set `φ : Γ(V, ⊤) →+* V.presheaf.stalk x` to `(V.presheaf.germ ⊤ x trivial).hom`. Establish `hle : Ideal.span (Set.range v) ≤ (IsLocalRing.maximalIdeal (V.presheaf.stalk x)).comap φ`. Rewrite using `[Ideal.span_le]`.

Introduce and unpack `_ ⟨k, rfl⟩`. Use `hn k` as an intermediate fact. Rewrite `this` using `[Scheme.mem_basicOpen_top]`. Conclude with `(IsLocalRing.mem_maximalIdeal _).2 this`. Rewrite `hle` using `[h]`.

Establish `h1 : (1 : Γ(V, ⊤)) ∈ (IsLocalRing.maximalIdeal (V.presheaf.stalk x)).comap φ` using `hle trivial`. Establish `h2 : φ 1 ∈ IsLocalRing.maximalIdeal (V.presheaf.stalk x)` using `h1`. Rewrite `h2` using `[map_one]`. Conclude with `(IsLocalRing.mem_maximalIdeal _).1 h2 isUnit_one`.
-/
private theorem exists_basicOpen_of_span {V : Scheme.{0}} {d : ℕ} (v : Fin d → Γ(V, ⊤))
    (h : Ideal.span (Set.range v) = ⊤) (x : V) : ∃ k, x ∈ V.basicOpen (v k) := by
  by_contra hn
  push_neg at hn
  let φ : Γ(V, ⊤) →+* V.presheaf.stalk x := (V.presheaf.germ ⊤ x trivial).hom
  have hle : Ideal.span (Set.range v) ≤ (IsLocalRing.maximalIdeal (V.presheaf.stalk x)).comap φ := by
    rw [Ideal.span_le]
    rintro _ ⟨k, rfl⟩
    have := hn k
    rw [Scheme.mem_basicOpen_top] at this
    exact (IsLocalRing.mem_maximalIdeal _).2 this
  rw [h] at hle
  have h1 : (1 : Γ(V, ⊤)) ∈ (IsLocalRing.maximalIdeal (V.presheaf.stalk x)).comap φ := hle trivial
  have h2 : φ 1 ∈ IsLocalRing.maximalIdeal (V.presheaf.stalk x) := h1
  rw [map_one] at h2
  exact (IsLocalRing.mem_maximalIdeal _).1 h2 isUnit_one

/- English proof (translation)
Establish `h0 : IsUnit ((V.presheaf.map (homOfLE (V.basicOpen_le s)).op).hom s)` using `RingedSpace.isUnit_res_basicOpen _ _`. Establish `hle : ⊤ ≤ U.ι ⁻¹ᵁ V.basicOpen s`. Introduce `z _`. Conclude with `hU z.2`. Establish `h1 : U.ι.appTop = V.presheaf.map (homOfLE (V.basicOpen_le s)).op ≫ U.ι.appLE (V.basicOpen s) ⊤ hle`.

Rewrite using `[Scheme.Hom.map_appLE]`. Conclude with `Scheme.Hom.app_eq_appLE U.ι`. Rewrite using `[h1]`. Conclude with `h0.map (U.ι.appLE (V.basicOpen s) ⊤ hle).hom`.
-/
private theorem isUnit_restrict {V : Scheme.{0}} (s : Γ(V, ⊤)) (U : V.Opens) (hU : U ≤ V.basicOpen s) :
    IsUnit (U.ι.appTop.hom s) := by
  have h0 : IsUnit ((V.presheaf.map (homOfLE (V.basicOpen_le s)).op).hom s) :=
    RingedSpace.isUnit_res_basicOpen _ _
  have hle : ⊤ ≤ U.ι ⁻¹ᵁ V.basicOpen s := by
    intro z _
    exact hU z.2
  have h1 : U.ι.appTop = V.presheaf.map (homOfLE (V.basicOpen_le s)).op ≫ U.ι.appLE (V.basicOpen s) ⊤ hle := by
    rw [Scheme.Hom.map_appLE]
    exact Scheme.Hom.app_eq_appLE U.ι
  rw [h1]
  exact h0.map (U.ι.appLE (V.basicOpen s) ⊤ hle).hom

/- English proof (translation)
Substitute `e` using the available equality. Both sides reduce to the same expression.
-/
private theorem uV_congr {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)}
    {i : W ⟶ Z} {π : Y ⟶ Z} {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d) (α : B.ι) (k : Fin d)
    {V : Scheme.{0}} {f g : V ⟶ Y} (e : f = g) (h : ⊤ ≤ f ⁻¹ᵁ (B.c α).C k) (h' : ⊤ ≤ g ⁻¹ᵁ (B.c α).C k) :
    uV B α k f h = uV B α k g h' := by
  subst e; rfl

/- English proof (translation)
Introduce `K _ W Z Y q i π D d B T j r hsq v hv V a₀ v₀ x`. Take `⟨U₀, α, a₁, hx₀, ha₁⟩` from `sigmaLocal (fun α : B.ι => (oW B α : Scheme.{0})) a₀ x`. Take `⟨k, hk⟩` from `exists_basicOpen_of_span v₀.1 v₀.2 x`. Set `U : V.Opens` to `U₀ ⊓ V.basicOpen (v₀.1 k)`. Take `⟨e, he⟩` from `isUnit_restrict (v₀.1 k) U inf_le_right`.

Set `a₂ : (U : Scheme.{0}) ⟶ (oW B α : Scheme.{0})` to `V.homOfLE (inf_le_left : U ≤ U₀) ≫ a₁`. Set `p : (U : Scheme.{0}) ⟶ W` to `a₂ ≫ (oW B α).ι`. Establish `hp : ⊤ ≤ (p ≫ i) ⁻¹ᵁ B.V α`. Introduce `z _`. Establish `hz : (a₂ z).1 ∈ oW B α` using `(a₂ z).2`.

Conclude with `hz`. Set `w : Fin d → Γ((U : Scheme.{0}), ⊤)` to `fun m => (↑e⁻¹ : Γ((U : Scheme.{0}), ⊤)) * U.ι.appTop.hom (v₀.1 m)`. Establish `hwk : w k = 1`. Express the relevant statement in the definitionally equal form `(↑e⁻¹ : Γ((U : Scheme.{0}), ⊤)) * U.ι.appTop.hom (v₀.1 k) = 1`. Rewrite using `[← he]`.

Conclude with `e.inv_mul`. Take `⟨y, hy, hyr, huv⟩` from `chartLift B j r hsq α k p hp w hwk`. Establish `hrange : Set.range y ⊆ Set.range (oT B j (α, k)).ι`. Introduce and unpack `_ ⟨z, rfl⟩`. Rewrite using `[Scheme.Opens.range_ι]`.

Establish `hz : (y ≫ j) z ∈ (B.c α).C k` using `hy (Set.mem_univ z)`. Rewrite `hz` using `[Scheme.Hom.comp_apply]`. Conclude with `hz`. Set `y₁ : (U : Scheme.{0}) ⟶ (oT B j (α, k) : Scheme.{0})` to `IsOpenImmersion.lift (oT B j (α, k)).ι y hrange`. Establish `hy₁ : y₁ ≫ (oT B j (α, k)).ι = y` using `IsOpenImmersion.lift_fac _ _ _`.

Take `⟨h', hv', -, hrho⟩` from `pieceFacts B j r hsq.w v hv (α, k) y₁`. Establish `hpath : (y₁ ≫ tI B j (α, k)) ≫ eP B j ≫ j = y ≫ j`. Establish `: tI B j (α, k) ≫ eP B j = (oT B j (α, k)).ι`. Simplify using `[tI, eP]`. Rewrite using `[← hy₁, Category.assoc, reassoc_of% this, Category.assoc]`.

Establish `hmap : y₁ ≫ rhoC B j r hsq.w (α, k) = a₂`. Rewrite using `[← cancel_mono (oW B α).ι]`. Establish `: rhoC B j r hsq.w (α, k) ≫ (oW B α).ι = (oT B j (α, k)).ι ≫ r` using `IsOpenImmersion.lift_fac _ _ _`. Rewrite using `[Category.assoc, this, reassoc_of% hy₁, hyr]`. Use `⟨U, y₁ ≫ tI B j (α, k), e⁻¹, ⟨hx₀, hk⟩, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[hrho, hmap]`. Establish `hι : U.ι ≫ a₀ = V.homOfLE (inf_le_left : U ≤ U₀) ≫ U₀.ι ≫ a₀`. Rewrite using `[← Category.assoc, Scheme.homOfLE_ι]`. Rewrite using `[hι, ha₁]`. Simplify using `only [a₂, Category.assoc]`.

Both sides reduce to the same expression. Rewrite using `[hv', uV_congr B α k hpath h' hy, huv]`. Both sides reduce to the same expression.
-/
theorem UpperTheory.Gal.KunnethLefschetz.G.PX.ontoField :
    ∀ {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z} {π : Y ⟶ Z} {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d) {T : Scheme.{0}} (j : T ⟶ Y) (r : T ⟶ W) (hsq : IsPullback j r π i) (v : Fin d → Γ(TP B j, ⊤)), IsV B j v → ∀ {V : Scheme.{0}} (a₀ : V ⟶ WP B) (v₀ : Um d Γ(V, ⊤)) (x : V), ∃ (U : V.Opens) (a : (U : Scheme.{0}) ⟶ TP B j) (u : (Γ((U : Scheme.{0}), ⊤))ˣ), x ∈ U ∧ a ≫ rhoP B j r hsq.w = U.ι ≫ a₀ ∧ a.appTop.hom ∘ v = (u : Γ((U : Scheme.{0}), ⊤)) • (U.ι.appTop.hom ∘ v₀.1) := by
  intro K _ W Z Y q i π D d B T j r hsq v hv V a₀ v₀ x
  obtain ⟨U₀, α, a₁, hx₀, ha₁⟩ := sigmaLocal (fun α : B.ι => (oW B α : Scheme.{0})) a₀ x
  obtain ⟨k, hk⟩ := exists_basicOpen_of_span v₀.1 v₀.2 x
  let U : V.Opens := U₀ ⊓ V.basicOpen (v₀.1 k)
  obtain ⟨e, he⟩ := isUnit_restrict (v₀.1 k) U inf_le_right
  let a₂ : (U : Scheme.{0}) ⟶ (oW B α : Scheme.{0}) := V.homOfLE (inf_le_left : U ≤ U₀) ≫ a₁
  let p : (U : Scheme.{0}) ⟶ W := a₂ ≫ (oW B α).ι
  have hp : ⊤ ≤ (p ≫ i) ⁻¹ᵁ B.V α := by
    intro z _
    have hz : (a₂ z).1 ∈ oW B α := (a₂ z).2
    exact hz
  let w : Fin d → Γ((U : Scheme.{0}), ⊤) := fun m => (↑e⁻¹ : Γ((U : Scheme.{0}), ⊤)) * U.ι.appTop.hom (v₀.1 m)
  have hwk : w k = 1 := by
    change (↑e⁻¹ : Γ((U : Scheme.{0}), ⊤)) * U.ι.appTop.hom (v₀.1 k) = 1
    rw [← he]; exact e.inv_mul
  obtain ⟨y, hy, hyr, huv⟩ := chartLift B j r hsq α k p hp w hwk
  have hrange : Set.range y ⊆ Set.range (oT B j (α, k)).ι := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    have hz : (y ≫ j) z ∈ (B.c α).C k := hy (Set.mem_univ z)
    rw [Scheme.Hom.comp_apply] at hz
    exact hz
  let y₁ : (U : Scheme.{0}) ⟶ (oT B j (α, k) : Scheme.{0}) := IsOpenImmersion.lift (oT B j (α, k)).ι y hrange
  have hy₁ : y₁ ≫ (oT B j (α, k)).ι = y := IsOpenImmersion.lift_fac _ _ _
  obtain ⟨h', hv', -, hrho⟩ := pieceFacts B j r hsq.w v hv (α, k) y₁
  have hpath : (y₁ ≫ tI B j (α, k)) ≫ eP B j ≫ j = y ≫ j := by
    have : tI B j (α, k) ≫ eP B j = (oT B j (α, k)).ι := by
      simp [tI, eP]
    rw [← hy₁, Category.assoc, reassoc_of% this, Category.assoc]
  have hmap : y₁ ≫ rhoC B j r hsq.w (α, k) = a₂ := by
    rw [← cancel_mono (oW B α).ι]
    have : rhoC B j r hsq.w (α, k) ≫ (oW B α).ι = (oT B j (α, k)).ι ≫ r := IsOpenImmersion.lift_fac _ _ _
    rw [Category.assoc, this, reassoc_of% hy₁, hyr]
  refine ⟨U, y₁ ≫ tI B j (α, k), e⁻¹, ⟨hx₀, hk⟩, ?_, ?_⟩
  · rw [hrho, hmap]
    have hι : U.ι ≫ a₀ = V.homOfLE (inf_le_left : U ≤ U₀) ≫ U₀.ι ≫ a₀ := by
      rw [← Category.assoc, Scheme.homOfLE_ι]
    rw [hι, ha₁]
    simp only [a₂, Category.assoc]
    rfl
  · rw [hv', uV_congr B α k hpath h' hy, huv]
    rfl
