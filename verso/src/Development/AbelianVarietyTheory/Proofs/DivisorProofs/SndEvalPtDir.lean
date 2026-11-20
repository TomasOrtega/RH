import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimeSpectrumDualNumberEq
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.TangentOrigin
open GlobalTheory.FlagMod
open GlobalTheory.FlagTan (dimFlag)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompHS

/- English proof (translation)
Establish `h : ∀ z : PrimeSpectrum (TrivSqZeroExt L M), ∀ a, a ∈ z.asIdeal ↔ a.fst = 0` using `fun z a => by`. Prove the components needed by the constructor for the conclusion. Introduce `ha`. Assume the negation of the conclusion as `h0`. Conclude with `z.2.ne_top (z.asIdeal.eq_top_of_isUnit_mem ha (TrivSqZeroExt.isUnit_iff_isUnit_fst.2 (Ne.isUnit h0)))`.

Introduce `ha`. Use `z.2.mem_of_pow_mem 2 ?_` and prove the remaining obligations. Apply the tactic sequence `rw [show a ^ 2 = 0 by ext <;> simp [pow_two, ha]]`. Conclude with `z.asIdeal.zero_mem`. Use extensionality with `a`.

Rewrite using `[h, h]`.
-/
theorem primeSpectrum_trivSqZeroExt_eq {L M : Type} [Field L] [AddCommGroup M] [Module L M] [Module Lᵐᵒᵖ M]
    [IsCentralScalar L M] (x y : PrimeSpectrum (TrivSqZeroExt L M)) : x = y := by
  have h : ∀ z : PrimeSpectrum (TrivSqZeroExt L M), ∀ a, a ∈ z.asIdeal ↔ a.fst = 0 := fun z a => by
    constructor
    · intro ha
      by_contra h0
      exact z.2.ne_top (z.asIdeal.eq_top_of_isUnit_mem ha (TrivSqZeroExt.isUnit_iff_isUnit_fst.2 (Ne.isUnit h0)))
    · intro ha
      refine z.2.mem_of_pow_mem 2 ?_
      rw [show a ^ 2 = 0 by ext <;> simp [pow_two, ha]]
      exact z.asIdeal.zero_mem
  ext a
  rw [h, h]

/- English proof (translation)
Introduce `s _`. Establish `hp : (spMap φ) (IsLocalRing.closedPoint L) = s` using `hR _ _`. Establish `h₁ : (spMap φ ≫ x) (IsLocalRing.closedPoint L) ∈ V` using `h (Set.mem_univ _)`. Conclude with `hp ▸ h₁`.
-/
theorem le_preimage_of_reduction {R L : Type} [CommRing R] [Field L] (hR : ∀ a b : PrimeSpectrum R, a = b)
    (φ : R →+* L) {T : Scheme.{0}} (x : Sp R ⟶ T) (V : T.Opens) (h : ⊤ ≤ (spMap φ ≫ x) ⁻¹ᵁ V) : ⊤ ≤ x ⁻¹ᵁ V := by
  intro s _
  have hp : (spMap φ) (IsLocalRing.closedPoint L) = s := hR _ _
  have h₁ : (spMap φ ≫ x) (IsLocalRing.closedPoint L) ∈ V := h (Set.mem_univ _)
  exact hp ▸ h₁

/- English proof (translation)
Introduce `s _`. Establish `hp : (spMap φ) s₀ = s` using `hR _ _`. Establish `h₁ : (spMap φ ≫ x) s₀ ∈ V` using `h (Set.mem_univ _)`. Conclude with `hp ▸ h₁`.
-/
theorem le_preimage_of_comp {R S : Type} [CommRing R] [CommRing S] (hR : ∀ a b : PrimeSpectrum R, a = b)
    (φ : R →+* S) (s₀ : Sp S) {T : Scheme.{0}} (x : Sp R ⟶ T) (V : T.Opens) (h : ⊤ ≤ (spMap φ ≫ x) ⁻¹ᵁ V) :
    ⊤ ≤ x ⁻¹ᵁ V := by
  intro s _
  have hp : (spMap φ) s₀ = s := hR _ _
  have h₁ : (spMap φ ≫ x) s₀ ∈ V := h (Set.mem_univ _)
  exact hp ▸ h₁

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {X : GlobalTheory.FlagMod.FlagCover Y} {Z : Comp Xo c}

/- English proof (translation)
Establish `hred : spMap (TrivSqZeroExt.fstHom c.F K (ι → K)).toRingHom ≫ X.ptY W = X.ptY Q` using `X.ptY_frMap hW`. Establish `hpt : ∀ a b : PrimeSpectrum (TrivSqZeroExt K (ι → K)), a = b` using `primeSpectrum_trivSqZeroExt_eq`. Establish `hU : ⊤ ≤ (z ≫ M.σ) ⁻¹ᵁ U₀ X Z` using `fun s _ => by`. Use `ho (Set.mem_univ s)` as an intermediate fact. Rewrite `this` using `[M.off_eq]`.

Conclude with `this`. Establish `hb : ⊤ ≤ X.ptY W ⁻¹ᵁ (inc₀ X Z).opensRange` using `le_preimage_of_reduction hpt (TrivSqZeroExt.fstHom c.F K (ι → K)).toRingHom _ _ (by`. Rewrite using `[hred, ← hz]`. Introduce and unpack `s -`. Conclude with `⟨(z ≫ M.σ) s, rfl⟩)`.

Establish `hr : Set.range (X.ptY W) ⊆ Set.range (inc₀ X Z)`. Introduce and unpack `_ ⟨s, rfl⟩`. Conclude with `hb (Set.mem_univ s)`. Take `⟨w₁, hw₁⟩ : ∃ w₁, w₁ ≫ inc₀ X Z = X.ptY W` from `⟨_, IsOpenImmersion.lift_fac _ _ hr⟩`. Establish `ered : spMap (TrivSqZeroExt.fstHom c.F K (ι → K)).toRingHom ≫ w₁ = z ≫ M.σ`.

Rewrite using `[← cancel_mono (inc₀ X Z), Category.assoc, hw₁, hred, ← hz, Category.assoc]`. Establish `hwU : ⊤ ≤ w₁ ⁻¹ᵁ U₀ X Z` using `le_preimage_of_reduction hpt _ _ _ (by rw [ered]; exact hU)`. Take `⟨ZW, hZW, -⟩` from `M.existsUnique_lift w₁ hwU`. Use `⟨ZW, by rw [toFlag, ← Category.assoc, hZW, hw₁], fun m x hx => ?_⟩` and prove the remaining obligations. Establish `hxU : ⊤ ≤ (spMap (GlobalTheory.FlagTan.dir c m).toRingHom ≫ w₁) ⁻¹ᵁ U₀ X Z` using `fun s _ => hwU (Set.mem_univ _)`.

Use `(M.existsUnique_lift _ hxU).unique ?_ (by rw [Category.assoc, hZW])` and prove the remaining obligations. Rewrite using `[← cancel_mono (inc₀ X Z), Category.assoc, Category.assoc, hw₁, ← hx]`.
-/
theorem exists_thickLift (M : Modif (str₀ X Z) (U₀ X Z) (dimFlag Dw)) {K : Type} [Field K] [Algebra c.F K]
    {ι : Type} [Fintype ι] (z : Sp K ⟶ M.X) (ho : ⊤ ≤ z ⁻¹ᵁ M.off) {Q : FrPt Xo c K} (hz : z ≫ toFlag M = X.ptY Q)
    {W : FrPt Xo c (TrivSqZeroExt K (ι → K))} (hW : FrMap (TrivSqZeroExt.fstHom c.F K (ι → K)) W Q) :
    ∃ ZW : Sp (TrivSqZeroExt K (ι → K)) ⟶ M.X, ZW ≫ toFlag M = X.ptY W ∧
      ∀ (m : ι → K) (x : Sp (DualNumber K) ⟶ M.X),
        x ≫ toFlag M = spMap (GlobalTheory.FlagTan.dir c m).toRingHom ≫ X.ptY W →
          x = spMap (GlobalTheory.FlagTan.dir c m).toRingHom ≫ ZW := by
  have hred : spMap (TrivSqZeroExt.fstHom c.F K (ι → K)).toRingHom ≫ X.ptY W = X.ptY Q := X.ptY_frMap hW
  have hpt : ∀ a b : PrimeSpectrum (TrivSqZeroExt K (ι → K)), a = b := primeSpectrum_trivSqZeroExt_eq
  have hU : ⊤ ≤ (z ≫ M.σ) ⁻¹ᵁ U₀ X Z := fun s _ => by
    have := ho (Set.mem_univ s)
    rw [M.off_eq] at this
    exact this
  have hb : ⊤ ≤ X.ptY W ⁻¹ᵁ (inc₀ X Z).opensRange :=
    le_preimage_of_reduction hpt (TrivSqZeroExt.fstHom c.F K (ι → K)).toRingHom _ _ (by
      rw [hred, ← hz]
      rintro s -
      exact ⟨(z ≫ M.σ) s, rfl⟩)
  have hr : Set.range (X.ptY W) ⊆ Set.range (inc₀ X Z) := by
    rintro _ ⟨s, rfl⟩
    exact hb (Set.mem_univ s)
  obtain ⟨w₁, hw₁⟩ : ∃ w₁, w₁ ≫ inc₀ X Z = X.ptY W := ⟨_, IsOpenImmersion.lift_fac _ _ hr⟩
  have ered : spMap (TrivSqZeroExt.fstHom c.F K (ι → K)).toRingHom ≫ w₁ = z ≫ M.σ := by
    rw [← cancel_mono (inc₀ X Z), Category.assoc, hw₁, hred, ← hz, Category.assoc]
  have hwU : ⊤ ≤ w₁ ⁻¹ᵁ U₀ X Z := le_preimage_of_reduction hpt _ _ _ (by rw [ered]; exact hU)
  obtain ⟨ZW, hZW, -⟩ := M.existsUnique_lift w₁ hwU
  refine ⟨ZW, by rw [toFlag, ← Category.assoc, hZW, hw₁], fun m x hx => ?_⟩
  have hxU : ⊤ ≤ (spMap (GlobalTheory.FlagTan.dir c m).toRingHom ≫ w₁) ⁻¹ᵁ U₀ X Z := fun s _ => hwU (Set.mem_univ _)
  refine (M.existsUnique_lift _ hxU).unique ?_ (by rw [Category.assoc, hZW])
  rw [← cancel_mono (inc₀ X Z), Category.assoc, Category.assoc, hw₁, ← hx]

/- English proof (translation)
Substitute `e` using the available equality. Rewrite using `[evalPt_spMap_comp (GlobalTheory.FlagTan.dir c m).toRingHom ZW O hO hx g]`. Conclude with `GlobalTheory.FlagTan.snd_dir m _`.
-/
theorem snd_evalPt_dir {K : Type} [Field K] [Algebra c.F K] {ι : Type} [Fintype ι] {T : Scheme.{0}}
    (ZW : Sp (TrivSqZeroExt K (ι → K)) ⟶ T) (O : T.Opens) (hO : ⊤ ≤ ZW ⁻¹ᵁ O) (m : ι → K)
    (x : Sp (DualNumber K) ⟶ T) (hx : ⊤ ≤ x ⁻¹ᵁ O) (e : x = spMap (GlobalTheory.FlagTan.dir c m).toRingHom ≫ ZW) (g : Γ(T, O)) :
    (evalPt x O hx g).snd = ∑ k, (evalPt ZW O hO g).snd k * m k := by
  subst e
  rw [evalPt_spMap_comp (GlobalTheory.FlagTan.dir c m).toRingHom ZW O hO hx g]
  exact GlobalTheory.FlagTan.snd_dir m _

end GlobalTheory.CompHS
