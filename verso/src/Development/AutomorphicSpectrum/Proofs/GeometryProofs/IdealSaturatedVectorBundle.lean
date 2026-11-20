import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IntegralClosureHeightEqOneOfLiesOver
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GenWeil
import Development.WeilBound.CoreStatements.HodgeTatePoints.NearMemSpan

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
/- English proof (translation)
Take `⟨g, rfl⟩` from `hw`. Take `⟨W, hq, s, rfl⟩` from `X.presheaf.exists_germ_eq g`. Use `⟨W, hq, fun q' hq' => ⟨X.presheaf.germ W q'.1 hq' s, ?_⟩⟩` and prove the remaining obligations. Establish `key : ∀ (y : X) (hy : y ∈ W) (h : genPt ξ ⤳ y), X.presheaf.germ W y hy ≫ X.presheaf.stalkSpecializes h ≫ Scheme.stalkClosedPointTo ξ = X.presheaf.germ W (genPt ξ) (h.mem_open W.isOpen hy) ≫ Scheme.stalkClosedPointTo ξ`. Introduce `y hy h`.

Conclude with `TopCat.Presheaf.germ_stalkSpecializes_assoc X.presheaf hy h _`. Simplify using `only [genMap]`. Rewrite using `[← CommRingCat.comp_apply, ← CommRingCat.comp_apply]`. Use `erw [key q'.1 hq' q'.2, key q.1 hq q.2]`.
-/
private theorem exists_open_forall_mem_regAt' {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Sp Ω ⟶ X) (q : Cpt ξ) (w : Ω)
    (hw : w ∈ regAt ξ q) : ∃ W : X.Opens, q.1 ∈ W ∧ ∀ q' : Cpt ξ, q'.1 ∈ W → w ∈ regAt ξ q' := by
  obtain ⟨g, rfl⟩ := hw
  obtain ⟨W, hq, s, rfl⟩ := X.presheaf.exists_germ_eq g
  refine ⟨W, hq, fun q' hq' => ⟨X.presheaf.germ W q'.1 hq' s, ?_⟩⟩
  have key : ∀ (y : X) (hy : y ∈ W) (h : genPt ξ ⤳ y),
      X.presheaf.germ W y hy ≫ X.presheaf.stalkSpecializes h ≫ Scheme.stalkClosedPointTo ξ =
        X.presheaf.germ W (genPt ξ) (h.mem_open W.isOpen hy) ≫ Scheme.stalkClosedPointTo ξ := by
    intro y hy h
    exact TopCat.Presheaf.germ_stalkSpecializes_assoc X.presheaf hy h _
  simp only [genMap]
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply]
  erw [key q'.1 hq' q'.2, key q.1 hq q.2]

/- English proof (translation)
Take `⟨x, hx𝔡, hx0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot h𝔡`. Take `⟨𝔞, h𝔞⟩ : 𝔡 ∣ Ideal.span {x}` from `Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hx𝔡)`. Establish `hσx : σ x ≠ 0` using `fun h => hx0 (hinj (by rw [h, map_zero]))`. Establish `hgood : ∀ n ∈ 𝔞, ∀ d' ∈ 𝔡, ∃ o : O, σ d' * (σ n / σ x) = σ o`. Introduce `n hn d' hd'`.

Establish `hmem : d' * n ∈ Ideal.span {x}` using `h𝔞 ▸ Ideal.mul_mem_mul hd' hn`. Take `⟨o, ho⟩` from `Ideal.mem_span_singleton'.mp hmem`. Use `⟨o, ?_⟩` and prove the remaining obligations. Rewrite using `[← mul_div_assoc, ← map_mul, ← ho, map_mul, mul_div_cancel_right₀ _ hσx]`. Assume the negation of the conclusion as `hne`.

Use `push_neg at hne`. Set `C : O → Prop` to `fun y => ∃ h : σ y / σ x ∈ R, (⟨_, h⟩ : R) ∈ IsLocalRing.maximalIdeal R`. Establish `hx : x ∈ 𝔡 * 𝔞` using `h𝔞 ▸ Ideal.mem_span_singleton_self x`. Establish `hC : C x`. Use `Submodule.mul_induction_on hx ?_ ?_` and prove the remaining obligations.

Introduce `m hm n hn`. Take `⟨o, ho⟩` from `hgood n hn m hm`. Establish `hR : σ (m * n) / σ x ∈ R`. Rewrite using `[map_mul, mul_div_assoc, ho]`. Conclude with `hσ o`.

Use `⟨hR, ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hnot`. Establish `hu : IsUnit (⟨_, hR⟩ : R)`. Assume the negation of the conclusion as `h'`. Conclude with `hnot ((IsLocalRing.mem_maximalIdeal _).mpr h')`.

Take `⟨w, hw⟩` from `hu.exists_right_inv`. Use `hne m hm (σ n / σ x) (hgood n hn) w w.2 ?_` and prove the remaining obligations. Use `congrArg Subtype.val hw` as an intermediate fact. Simplify `this` using `[map_mul, mul_div_assoc]`. Introduce and unpack `a b ⟨ha, ha'⟩ ⟨hb, hb'⟩`.

Establish `hab : σ (a + b) / σ x ∈ R` using `by rw [map_add, add_div]; exact add_mem ha hb`. Use `⟨hab, ?_⟩` and prove the remaining obligations. Establish `: (⟨_, hab⟩ : R) = ⟨_, ha⟩ + ⟨_, hb⟩` using `by ext; simp [map_add, add_div]`. Rewrite using `[this]`. Conclude with `add_mem ha' hb'`.

Take `⟨h1, h2⟩` from `hC`. Establish `: (⟨_, h1⟩ : R) = 1` using `by ext; simp [div_self hσx]`. Rewrite `h2` using `[this]`. Conclude with `(IsLocalRing.maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).mpr h2)`.
-/
private theorem exists_mul_eq_one_of_dedekind_ideal_ne_bot {Ω : Type} [Field Ω] (O : Type) [CommRing O] [IsDedekindDomain O] (σ : O →+* Ω)
    (𝔡 : Ideal O) (R : Subring Ω) [IsLocalRing R] (hσ : ∀ a, σ a ∈ R) (hinj : Function.Injective σ)
    (h𝔡 : 𝔡 ≠ ⊥) : ∃ d ∈ 𝔡, ∃ u : Ω, (∀ d' ∈ 𝔡, ∃ o : O, σ d' * u = σ o) ∧ ∃ v ∈ R, σ d * u * v = 1 := by
  obtain ⟨x, hx𝔡, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h𝔡
  obtain ⟨𝔞, h𝔞⟩ : 𝔡 ∣ Ideal.span {x} :=
    Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hx𝔡)
  have hσx : σ x ≠ 0 := fun h => hx0 (hinj (by rw [h, map_zero]))
  have hgood : ∀ n ∈ 𝔞, ∀ d' ∈ 𝔡, ∃ o : O, σ d' * (σ n / σ x) = σ o := by
    intro n hn d' hd'
    have hmem : d' * n ∈ Ideal.span {x} := h𝔞 ▸ Ideal.mul_mem_mul hd' hn
    obtain ⟨o, ho⟩ := Ideal.mem_span_singleton'.mp hmem
    refine ⟨o, ?_⟩
    rw [← mul_div_assoc, ← map_mul, ← ho, map_mul, mul_div_cancel_right₀ _ hσx]
  by_contra hne
  push_neg at hne
  let C : O → Prop := fun y => ∃ h : σ y / σ x ∈ R, (⟨_, h⟩ : R) ∈ IsLocalRing.maximalIdeal R
  have hx : x ∈ 𝔡 * 𝔞 := h𝔞 ▸ Ideal.mem_span_singleton_self x
  have hC : C x := by
    refine Submodule.mul_induction_on hx ?_ ?_
    · intro m hm n hn
      obtain ⟨o, ho⟩ := hgood n hn m hm
      have hR : σ (m * n) / σ x ∈ R := by
        rw [map_mul, mul_div_assoc, ho]; exact hσ o
      refine ⟨hR, ?_⟩
      by_contra hnot
      have hu : IsUnit (⟨_, hR⟩ : R) := by
        by_contra h'
        exact hnot ((IsLocalRing.mem_maximalIdeal _).mpr h')
      obtain ⟨w, hw⟩ := hu.exists_right_inv
      refine hne m hm (σ n / σ x) (hgood n hn) w w.2 ?_
      have := congrArg Subtype.val hw
      simpa [map_mul, mul_div_assoc] using this
    · rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
      have hab : σ (a + b) / σ x ∈ R := by rw [map_add, add_div]; exact add_mem ha hb
      refine ⟨hab, ?_⟩
      have : (⟨_, hab⟩ : R) = ⟨_, ha⟩ + ⟨_, hb⟩ := by
        ext; simp [map_add, add_div]
      rw [this]; exact add_mem ha' hb'
  obtain ⟨h1, h2⟩ := hC
  have : (⟨_, h1⟩ : R) = 1 := by ext; simp [div_self hσx]
  rw [this] at h2
  exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).mpr h2)

set_option maxHeartbeats 1000000 in
/- English proof (translation)
Introduce `X Ω _ ξ Li _ _ O _ _ σ 𝔡 L T r V hinj h𝔡 hσ hL p hp`. Take `⟨U₀, hpU₀, b, hbV, hb⟩` from `hL p hp`. Use `haveI : IsLocalRing (regAt ξ p) := IsLocalRing.of_surjective' (genMap ξ p).rangeRestrict (genMap ξ p).rangeRestrict_surjective`. Take `⟨d, hd, u, hu, v, hv, hdu⟩` from `exists_mul_eq_one_of_dedekind_ideal_ne_bot O σ 𝔡 (regAt ξ p) (hσ p hp) hinj h𝔡`. Take `⟨W₂, hpW₂, hW₂⟩` from `exists_open_forall_mem_regAt' ξ p v hv`.

Establish `hu0 : u ≠ 0` using `by rintro rfl; simp at hdu`. Use `⟨U₀ ⊓ W₂, ⟨hpU₀, hpW₂⟩, fun i => u • b i, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← hbV]`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Submodule.span_le]`.

Introduce and unpack `_ ⟨i, rfl⟩`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Establish `: b i = u⁻¹ • (u • b i)` using `by rw [smul_smul, inv_mul_cancel₀ hu0, one_smul]`.

Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`. Introduce `q hq hqU`. Take `⟨hli, hLq⟩` from `hb q hq hqU.1`. Establish `hvq : v ∈ regAt ξ q` using `hW₂ q hqU.2`.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `hli.units_smul (fun _ => Units.mk0 u hu0)` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `i`. Simplify using `[Units.smul_def]`.

Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Submodule.span_le]`. Introduce and unpack `e ⟨heV, he⟩`. Establish `h1 : σ d • e ∈ L q` using `he d hd`. Rewrite `h1` using `[hLq]`.

Establish `h2 : (⟨v, hvq⟩ : regAt ξ q) • (σ d • e) ∈ Submodule.span (regAt ξ q) (Set.range b)` using `Submodule.smul_mem _ _ h1`. Take `⟨c, hc⟩` from `(Submodule.mem_span_range_iff_exists_fun _).mp h2`. Establish `he' : e = u • ((⟨v, hvq⟩ : regAt ξ q) • (σ d • e))`. Rewrite using `[Subring.smul_def, smul_smul, smul_smul]`. Rewrite using `[show u * v * σ d = 1 by rw [← hdu]; ring, one_smul]`.

Rewrite using `[SetLike.mem_coe, he', ← hc, Finset.smul_sum]`. Use `Submodule.sum_mem _ (fun i _ => ?_)` and prove the remaining obligations. Rewrite using `[Subring.smul_def, smul_comm]`. Conclude with `Submodule.smul_mem _ (c i) (Submodule.subset_span ⟨i, rfl⟩)`. Rewrite using `[Submodule.span_le]`.

Introduce and unpack `_ ⟨i, rfl⟩`. Apply `Submodule.subset_span` to reduce the goal to its premises. Use `⟨?_, fun d' hd' => ?_⟩` and prove the remaining obligations. Rewrite using `[← hbV]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`.

Take `⟨o, ho⟩` from `hu d' hd'`. Establish `hbi : b i ∈ L q` using `by rw [hLq]; exact Submodule.subset_span ⟨i, rfl⟩`. Rewrite using `[smul_smul, ho]`. Conclude with `Submodule.smul_mem (L q) (⟨σ o, hσ q hq o⟩ : regAt ξ q) hbi`.
-/
theorem _root_.GlobalTheory.CompanionTheory.Relay.ideal_saturated_vector_bundle : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (Li : Type) [AddCommGroup Li] [Module Ω Li] (O : Type) [CommRing O] [IsDedekindDomain O] (σ : O →+* Ω) (𝔡 : Ideal O) (L : Lat ξ Li) (T : Set (Cpt ξ)) (r : ℕ) (V : Submodule Ω Li), Function.Injective σ → 𝔡 ≠ ⊥ → (∀ q ∈ T, ∀ a, σ a ∈ regAt ξ q) → L.IsVBOn T r V → Lat.IsVBOn (fun q => Submodule.span (regAt ξ q) {e | e ∈ V ∧ ∀ d ∈ 𝔡, σ d • e ∈ L q} : Lat ξ Li) T r V := by
  intro X Ω _ ξ Li _ _ O _ _ σ 𝔡 L T r V hinj h𝔡 hσ hL p hp
  obtain ⟨U₀, hpU₀, b, hbV, hb⟩ := hL p hp
  haveI : IsLocalRing (regAt ξ p) :=
    IsLocalRing.of_surjective' (genMap ξ p).rangeRestrict (genMap ξ p).rangeRestrict_surjective
  obtain ⟨d, hd, u, hu, v, hv, hdu⟩ := exists_mul_eq_one_of_dedekind_ideal_ne_bot O σ 𝔡 (regAt ξ p) (hσ p hp) hinj h𝔡
  obtain ⟨W₂, hpW₂, hW₂⟩ := exists_open_forall_mem_regAt' ξ p v hv
  have hu0 : u ≠ 0 := by rintro rfl; simp at hdu
  refine ⟨U₀ ⊓ W₂, ⟨hpU₀, hpW₂⟩, fun i => u • b i, ?_, ?_⟩
  · rw [← hbV]
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      have : b i = u⁻¹ • (u • b i) := by rw [smul_smul, inv_mul_cancel₀ hu0, one_smul]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · intro q hq hqU
    obtain ⟨hli, hLq⟩ := hb q hq hqU.1
    have hvq : v ∈ regAt ξ q := hW₂ q hqU.2
    refine ⟨?_, ?_⟩
    · have := hli.units_smul (fun _ => Units.mk0 u hu0)
      convert this using 1
      funext i
      simp [Units.smul_def]
    · apply le_antisymm
      · rw [Submodule.span_le]
        rintro e ⟨heV, he⟩
        have h1 : σ d • e ∈ L q := he d hd
        rw [hLq] at h1
        have h2 : (⟨v, hvq⟩ : regAt ξ q) • (σ d • e) ∈ Submodule.span (regAt ξ q) (Set.range b) :=
          Submodule.smul_mem _ _ h1
        obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp h2
        have he' : e = u • ((⟨v, hvq⟩ : regAt ξ q) • (σ d • e)) := by
          rw [Subring.smul_def, smul_smul, smul_smul]
          rw [show u * v * σ d = 1 by rw [← hdu]; ring, one_smul]
        rw [SetLike.mem_coe, he', ← hc, Finset.smul_sum]
        refine Submodule.sum_mem _ (fun i _ => ?_)
        rw [Subring.smul_def, smul_comm]
        exact Submodule.smul_mem _ (c i) (Submodule.subset_span ⟨i, rfl⟩)
      · rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        apply Submodule.subset_span
        refine ⟨?_, fun d' hd' => ?_⟩
        · rw [← hbV]
          exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
        · obtain ⟨o, ho⟩ := hu d' hd'
          have hbi : b i ∈ L q := by rw [hLq]; exact Submodule.subset_span ⟨i, rfl⟩
          rw [smul_smul, ho]
          exact Submodule.smul_mem (L q) (⟨σ o, hσ q hq o⟩ : regAt ξ q) hbi
