import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.RatTors
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ModuliModelUltrametricPoints
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFieldOfValues
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsMulEquivOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCompleteDvrFiniteSubalgebra

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Trait

namespace GlobalTheory.Ex.TorsionField

open GlobalTheory.Ex.UnifModel

/- English proof (translation)
Establish `hC : (n : C) ≠ 0` using `Nat.cast_ne_zero.2 (by omega)`. Establish `hF : (n : F) ≠ 0` using `fun e => hC (by rw [← map_natCast i, e, map_zero])`. Establish `c₁` using `(hM _ P n hn).2.2.2.2 C (spMap c) hC`. Establish `c₂` using `(hM _ P n hn).2.2.2.2 F (spMap a) hF`. Use `Nat.finite_of_card_ne_zero (c₁ ▸ pow_ne_zero _ (by omega) : _ ≠ 0)` as an intermediate fact.

Set `u : Over.mk (spMap c) ⟶ Over.mk (spMap a)` to `Over.homMk (spMap i) (spMap_comp h)`. Set `Φ : {y : Over.mk (spMap a) ⟶ P.A // y ^ n = 1} → {y : Over.mk (spMap c) ⟶ P.A // y ^ n = 1}` to `fun y => ⟨u ≫ y.1, by rw [← MonObj.comp_pow, y.2, MonObj.comp_one]⟩`. Use `epi_spMap i` as an intermediate fact. Establish `hΦ : Function.Injective Φ` using `fun y y' e => Subtype.ext (Over.OverMorphism.ext ((cancel_epi (spMap i)).1 congr(($e).1.left)))`. Take `⟨y, hy⟩` from `(hΦ.bijective_of_nat_card_le (c₁.trans c₂.symm).le).2 ⟨x, hx⟩`.

Conclude with `⟨y.1, y.2, congr(($hy).1.left)⟩`.
-/
theorem exists_descend_algClosed (hM : MulNSt) {K F C : Type} [Field K] [Field F] [IsAlgClosed F] [Field C]
    [IsAlgClosed C] [CharZero C] (P : PolAV (Sp K)) (a : K →+* F) (i : F →+* C) (c : K →+* C)
    (h : ∀ x, i (a x) = c x) {n : ℕ} (hn : 1 ≤ n) (x : Over.mk (spMap c) ⟶ P.A) (hx : x ^ n = 1) :
    ∃ y : Over.mk (spMap a) ⟶ P.A, y ^ n = 1 ∧ spMap i ≫ y.left = x.left := by
  have hC : (n : C) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hF : (n : F) ≠ 0 := fun e => hC (by rw [← map_natCast i, e, map_zero])
  have c₁ := (hM _ P n hn).2.2.2.2 C (spMap c) hC
  have c₂ := (hM _ P n hn).2.2.2.2 F (spMap a) hF
  have := Nat.finite_of_card_ne_zero (c₁ ▸ pow_ne_zero _ (by omega) : _ ≠ 0)
  let u : Over.mk (spMap c) ⟶ Over.mk (spMap a) := Over.homMk (spMap i) (spMap_comp h)
  let Φ : {y : Over.mk (spMap a) ⟶ P.A // y ^ n = 1} → {y : Over.mk (spMap c) ⟶ P.A // y ^ n = 1} :=
    fun y => ⟨u ≫ y.1, by rw [← MonObj.comp_pow, y.2, MonObj.comp_one]⟩
  have := epi_spMap i
  have hΦ : Function.Injective Φ := fun y y' e =>
    Subtype.ext (Over.OverMorphism.ext ((cancel_epi (spMap i)).1 congr(($e).1.left)))
  obtain ⟨y, hy⟩ := (hΦ.bijective_of_nat_card_le (c₁.trans c₂.symm).le).2 ⟨x, hx⟩
  exact ⟨y.1, y.2, congr(($hy).1.left)⟩

/- English proof (translation)
Establish `c₂` using `(hM _ P n hn).2.2.2.2 F (spMap (algebraMap K F)) (Nat.cast_ne_zero.2 (by omega))`. Use `Nat.finite_of_card_ne_zero (c₂ ▸ pow_ne_zero _ (by omega) : _ ≠ 0)` as an intermediate fact. Use `Fintype.ofFinite {y : Over.mk (spMap (algebraMap K F)) ⟶ P.A // y ^ n = 1}` as an intermediate fact. Establish `hpr` using `P.isAb.proper`. Establish `key : ∀ x : {y : Over.mk (spMap (algebraMap K F)) ⟶ P.A // y ^ n = 1}, ∃ s : Finset F, ∀ (k : Type) [Field k] (β : k →+* F), (∀ c, algebraMap K F c ∈ β.fieldRange) → (∀ c ∈ s, c ∈ β.fieldRange) → ∃ y : Sp k ⟶ P.A.left, spMap β ≫ y = x.1.left`.

Introduce `x`. Take `⟨E, -, h2, h3⟩` from `GlobalTheory.SS.exists_fieldOfValues P.A.left F x.1.left`. Take `⟨L, hL, rfl⟩` from `h3 K P.A.hom inferInstance (Over.w x.1) inferInstance`. Take `⟨s, hs⟩` from `(Submodule.fg_top L.toSubalgebra.toSubmodule).1 hL.fg_top`. Use `⟨s, fun k _ β h₁ h₂ => (h2 k β).1 fun c hc => ?_⟩` and prove the remaining obligations.

Establish `hc' : c ∈ Submodule.span K (s : Set F)` using `hs ▸ hc`. Use `clear hc`. Proceed by induction on `hc' using Submodule.span_induction with`. Consider the case `mem c hc => exact h₂ c hc`. Consider the case `zero => exact zero_mem _`.

Consider the case `add _ _ _ _ ha hb => exact add_mem ha hb`. Consider the case `smul r c _ hc => rw [Algebra.smul_def]`. Conclude with `mul_mem (h₁ r) hc`. Use `choose s hs using key`. Conclude with `⟨Finset.univ.biUnion s, fun k _ β h₁ h₂ x hx => hs ⟨x, hx⟩ k β h₁ fun c hc => h₂ c (Finset.mem_biUnion.2 ⟨_, Finset.mem_univ _, hc⟩)⟩`.
-/
theorem exists_finset (hM : MulNSt) {K F : Type} [Field K] [Field F] [IsAlgClosed F] [CharZero F] [Algebra K F]
    [Algebra.IsAlgebraic K F] (P : PolAV (Sp K)) {n : ℕ} (hn : 1 ≤ n) :
    ∃ s : Finset F, ∀ (k : Type) [Field k] (β : k →+* F), (∀ c, algebraMap K F c ∈ β.fieldRange) →
      (∀ c ∈ s, c ∈ β.fieldRange) → ∀ x : Over.mk (spMap (algebraMap K F)) ⟶ P.A, x ^ n = 1 →
        ∃ y : Sp k ⟶ P.A.left, spMap β ≫ y = x.left := by
  classical
  have c₂ := (hM _ P n hn).2.2.2.2 F (spMap (algebraMap K F)) (Nat.cast_ne_zero.2 (by omega))
  have := Nat.finite_of_card_ne_zero (c₂ ▸ pow_ne_zero _ (by omega) : _ ≠ 0)
  have := Fintype.ofFinite {y : Over.mk (spMap (algebraMap K F)) ⟶ P.A // y ^ n = 1}
  have hpr := P.isAb.proper
  have key : ∀ x : {y : Over.mk (spMap (algebraMap K F)) ⟶ P.A // y ^ n = 1}, ∃ s : Finset F,
      ∀ (k : Type) [Field k] (β : k →+* F), (∀ c, algebraMap K F c ∈ β.fieldRange) →
        (∀ c ∈ s, c ∈ β.fieldRange) → ∃ y : Sp k ⟶ P.A.left, spMap β ≫ y = x.1.left := by
    intro x
    obtain ⟨E, -, h2, h3⟩ := GlobalTheory.SS.exists_fieldOfValues P.A.left F x.1.left
    obtain ⟨L, hL, rfl⟩ := h3 K P.A.hom inferInstance (Over.w x.1) inferInstance
    obtain ⟨s, hs⟩ := (Submodule.fg_top L.toSubalgebra.toSubmodule).1 hL.fg_top
    refine ⟨s, fun k _ β h₁ h₂ => (h2 k β).1 fun c hc => ?_⟩
    have hc' : c ∈ Submodule.span K (s : Set F) := hs ▸ hc
    clear hc
    induction hc' using Submodule.span_induction with
    | mem c hc => exact h₂ c hc
    | zero => exact zero_mem _
    | add _ _ _ _ ha hb => exact add_mem ha hb
    | smul r c _ hc => rw [Algebra.smul_def]; exact mul_mem (h₁ r) hc
  choose s hs using key
  exact ⟨Finset.univ.biUnion s, fun k _ β h₁ h₂ x hx => hs ⟨x, hx⟩ k β h₁ fun c hc =>
    h₂ c (Finset.mem_biUnion.2 ⟨_, Finset.mem_univ _, hc⟩)⟩

/- English proof (translation)
Establish `: CharZero F` using `i.charZero`. Take `⟨P, φ, hφ₀, -, hm, -⟩` from `hL.polBaseChange S (Sp K) t B₁`. Establish `hφ : IsGrpPullback P.A B₁.A t φ` using `⟨hφ₀, fun T x y x₀ y₀ hx hy => by`. Rewrite using `[(Over.OverMorphism.ext hx : x₀ = toBase hφ₀.w x), (Over.OverMorphism.ext hy : y₀ = toBase hφ₀.w y), ← hm]`. Use the proof step `rfl⟩`.

Take `⟨s, hs⟩` from `exists_finset (F := F) hL.mulN P hn`. Use `⟨s, fun R _ _ _ β hβ h₁ h₂ r hr B ψ hψ x hx => ?_⟩` and prove the remaining obligations. Establish `e₁ : spMap i ≫ spMap β = jFK (R` using `R) C := spMap_comp hβ`. Establish `e₂ : spMap i ≫ spMap (algebraMap K F) = spMap (i.comp (algebraMap K F))` using `spMap_comp fun _ => rfl`. Take `⟨e, he⟩` from `exists_mulEquiv_of_isGrpPullback hψ (jFK (R := R) C ≫ jK R) _ rfl`.

Take `⟨e', he'⟩` from `exists_mulEquiv_of_isGrpPullback hφ (spMap (i.comp (algebraMap K F))) ((jFK (R := R) C ≫ jK R) ≫ r) (by rw [← e₁, ← e₂, Category.assoc, Category.assoc, hr, Category.assoc])`. Take `⟨y, hy, hy'⟩` from `exists_descend_algClosed hL.mulN P (algebraMap K F) i _ (fun _ => rfl) hn (e'.symm (e x)) (by rw [← map_pow, ← map_pow, hx, map_one, map_one])`. Take `⟨z, hz⟩` from `hs _ β h₁ h₂ y hy`. Use `epi_spMap β` as an intermediate fact. Establish `w : (z ≫ φ) ≫ B₁.A.hom = jK R ≫ r`.

Rewrite using `[← cancel_epi (spMap β), hr, Category.assoc, hφ₀.w, reassoc_of% hz]`. Conclude with `(Category.assoc _ _ _).symm.trans (congrArg (· ≫ t) (Over.w y))`. Use `⟨Over.homMk (hψ.1.lift _ _ w) (hψ.1.lift_snd _ _ _), hψ.1.hom_ext ?_ ?_⟩` and prove the remaining obligations. Use `(he x).symm.trans ?_` and prove the remaining obligations. Rewrite using `[← e'.apply_symm_apply (e x), he', ← hy', ← hz, ← e₁]`.

Simplify using `only [Category.assoc]`. Conclude with `congrArg (fun q => spMap i ≫ spMap β ≫ q) (hψ.1.lift_fst _ _ w).symm`. Use `(Over.w x).trans ?_` and prove the remaining obligations. Conclude with `(congrArg (fun q => jFK (R := R) C ≫ q) (hψ.1.lift_snd _ _ w).symm).trans (Category.assoc _ _ _).symm`.
-/
theorem exists_finset_ratTors (hL : Laws) {K F C : Type} [Field K] [Field F] [IsAlgClosed F] [Algebra K F]
    [Algebra.IsAlgebraic K F] [Field C] [IsAlgClosed C] [CharZero C] (i : F →+* C) {S : Scheme.{0}} (t : Sp K ⟶ S)
    (B₁ : PolAV S) {n : ℕ} (hn : 1 ≤ n) :
    ∃ s : Finset F, ∀ (R : Type) [CommRing R] [IsDomain R] [Algebra (FractionRing R) C] (β : FractionRing R →+* F),
      (∀ c, i (β c) = algebraMap _ C c) → (∀ c, algebraMap K F c ∈ β.fieldRange) → (∀ c ∈ s, c ∈ β.fieldRange) →
      ∀ r : Sp R ⟶ S, spMap β ≫ jK R ≫ r = spMap (algebraMap K F) ≫ t →
      ∀ (B : PolAV (Sp R)) (ψ : B.A.left ⟶ B₁.A.left), IsGrpPullback B.A B₁.A r ψ → RatTors B C n := by
  have : CharZero F := i.charZero
  obtain ⟨P, φ, hφ₀, -, hm, -⟩ := hL.polBaseChange S (Sp K) t B₁
  have hφ : IsGrpPullback P.A B₁.A t φ := ⟨hφ₀, fun T x y x₀ y₀ hx hy => by
    rw [(Over.OverMorphism.ext hx : x₀ = toBase hφ₀.w x), (Over.OverMorphism.ext hy : y₀ = toBase hφ₀.w y), ← hm]
    rfl⟩
  obtain ⟨s, hs⟩ := exists_finset (F := F) hL.mulN P hn
  refine ⟨s, fun R _ _ _ β hβ h₁ h₂ r hr B ψ hψ x hx => ?_⟩
  have e₁ : spMap i ≫ spMap β = jFK (R := R) C := spMap_comp hβ
  have e₂ : spMap i ≫ spMap (algebraMap K F) = spMap (i.comp (algebraMap K F)) := spMap_comp fun _ => rfl
  obtain ⟨e, he⟩ := exists_mulEquiv_of_isGrpPullback hψ (jFK (R := R) C ≫ jK R) _ rfl
  obtain ⟨e', he'⟩ := exists_mulEquiv_of_isGrpPullback hφ (spMap (i.comp (algebraMap K F)))
    ((jFK (R := R) C ≫ jK R) ≫ r) (by rw [← e₁, ← e₂, Category.assoc, Category.assoc, hr, Category.assoc])
  obtain ⟨y, hy, hy'⟩ := exists_descend_algClosed hL.mulN P (algebraMap K F) i _ (fun _ => rfl) hn
    (e'.symm (e x)) (by rw [← map_pow, ← map_pow, hx, map_one, map_one])
  obtain ⟨z, hz⟩ := hs _ β h₁ h₂ y hy
  have := epi_spMap β
  have w : (z ≫ φ) ≫ B₁.A.hom = jK R ≫ r := by
    rw [← cancel_epi (spMap β), hr, Category.assoc, hφ₀.w, reassoc_of% hz]
    exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ t) (Over.w y))
  refine ⟨Over.homMk (hψ.1.lift _ _ w) (hψ.1.lift_snd _ _ _), hψ.1.hom_ext ?_ ?_⟩
  · refine (he x).symm.trans ?_
    rw [← e'.apply_symm_apply (e x), he', ← hy', ← hz, ← e₁]
    simp only [Category.assoc]
    exact congrArg (fun q => spMap i ≫ spMap β ≫ q) (hψ.1.lift_fst _ _ w).symm
  · refine (Over.w x).trans ?_
    exact (congrArg (fun q => jFK (R := R) C ≫ q) (hψ.1.lift_snd _ _ w).symm).trans (Category.assoc _ _ _).symm

/- English proof (translation)
Introduce `hL W _ _ _ ⟨d, hc, h0⟩ C _ _ _ _ hext n hn S₁ S₂ s₁ s₂ B₁ B₂`. Set `F` to `algebraicClosure (FractionRing W) C`. Establish `: IsAlgClosed F` using `(algebraicClosure.isAlgClosure (FractionRing W) C).isAlgClosed`. Set `: Algebra W F` to `((algebraMap (FractionRing W) F).comp (algebraMap W _)).toAlgebra`. Establish `: IsScalarTower W (FractionRing W) F` using `IsScalarTower.of_algebraMap_eq fun _ => rfl`.

Establish `iW : Function.Injective (algebraMap W F)` using `(algebraMap (FractionRing W) F).injective.comp (IsFractionRing.injective W _)`. Establish `: FaithfulSMul W F` using `(faithfulSMul_iff_algebraMap_injective W F).2 iW`. Establish `: Algebra.IsAlgebraic W F` using `(IsFractionRing.comap_isAlgebraic_iff (A := W) (K := FractionRing W) (C := F)).2 inferInstance`. Establish `: CharZero (FractionRing W)` using `IsFractionRing.charZero_of_isFractionRing W`. Establish `: CharZero C` using `charZero_of_injective_algebraMap (algebraMap (FractionRing W) C).injective`.

Take `⟨t₁, ht₁⟩` from `exists_finset_ratTors hL (algebraMap F C) (jK W ≫ s₁) B₁ hn`. Take `⟨t₂, ht₂⟩` from `exists_finset_ratTors hL (algebraMap F C) (jK W ≫ s₂) B₂ hn`. Take `⟨V, dV, cV, -, fV, -, lV, hV, -⟩` from `exists_complete_dvr_finite_subalgebra W F (t₁ ∪ t₂)`. Establish `i₁ : Function.Injective (algebraMap V F)` using `Subtype.val_injective`. Set `β : FractionRing V →+* F` to `IsFractionRing.lift i₁`.

Establish `hβ : ∀ x, β (algebraMap V _ x) = algebraMap V F x` using `IsFractionRing.lift_algebraMap i₁`. Set `: Algebra (FractionRing V) C` to `((algebraMap F C).comp β).toAlgebra`. Establish `hA : Along (algebraMap W V) C` using `fun x => congrArg (algebraMap F C) (hβ _)`. Establish `h₁ : ∀ c, algebraMap (FractionRing W) F c ∈ β.fieldRange` using `fun c => by`. Take `⟨a, b, -, rfl⟩` from `IsFractionRing.div_surjective (A := W) c`.

Rewrite using `[map_div₀]`. Conclude with `div_mem ⟨_, hβ (algebraMap W V a)⟩ ⟨_, hβ (algebraMap W V b)⟩`. Establish `h₂ : ∀ c ∈ t₁ ∪ t₂, c ∈ β.fieldRange` using `fun x hx => by`. Take `⟨u, hu, v, hv, h0, e⟩` from `hV x hx`. Use `⟨algebraMap V _ ⟨u, hu⟩ / algebraMap V _ ⟨v, hv⟩, ?_⟩` and prove the remaining obligations.

Rewrite using `[map_div₀, hβ, hβ]`. Conclude with `(div_eq_iff h0).2 e.symm`. Establish `e : spMap β ≫ jK V ≫ spMap (algebraMap W V) = spMap (algebraMap (FractionRing W) F) ≫ jK W`. Rewrite using `[← Category.assoc, spMap_comp hβ, spMap_comp (d := algebraMap W F) fun _ => rfl]`. Conclude with `(spMap_comp fun _ => rfl).symm`.

Establish `: CharZero V` using `(algebraMap V F).charZero`. Use `⟨V, inferInstance, inferInstance, inferInstance, inferInstance, algebraMap W V, ⟨dV, cV, inferInstance⟩, fun a b h => iW (congrArg Subtype.val h), RingHom.finite_algebraMap.2 fV, lV, hA, cExt_of_integral hext hA, ht₁ V β (fun _ => rfl) h₁ (fun c hc => h₂ c (Finset.mem_union_left …` and prove the remaining obligations. Rewrite using `[reassoc_of% e]`. Rewrite using `[reassoc_of% e]`.
-/
theorem exists_cDvr_ratTors : Laws → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ (C : Type) [NormedField C] [IsUltrametricDist C] [IsAlgClosed C] [Algebra (FractionRing W) C], CExt W (IsLocalRing.maximalIdeal W) C → ∀ n : ℕ, 1 ≤ n → ∀ (S₁ S₂ : Scheme.{0}) (s₁ : Sp W ⟶ S₁) (s₂ : Sp W ⟶ S₂) (B₁ : PolAV S₁) (B₂ : PolAV S₂), ∃ (W' : Type) (_ : CommRing W') (_ : IsDomain W') (_ : IsLocalRing W') (_ : Algebra (FractionRing W') C) (io : W →+* W'), GlobalTheory.LN.CDvr W' ∧ Function.Injective io ∧ io.Finite ∧ IsLocalHom io ∧ Along io C ∧ CExt W' (IsLocalRing.maximalIdeal W') C ∧ (∀ (B : PolAV (Sp W')) (ψ : B.A.left ⟶ B₁.A.left), IsGrpPullback B.A B₁.A (spMap io ≫ s₁) ψ → RatTors B C n) ∧ ∀ (B : PolAV (Sp W')) (ψ : B.A.left ⟶ B₂.A.left), IsGrpPullback B.A B₂.A (spMap io ≫ s₂) ψ → RatTors B C n := by
  intro hL W _ _ _ ⟨d, hc, h0⟩ C _ _ _ _ hext n hn S₁ S₂ s₁ s₂ B₁ B₂
  classical
  let F := algebraicClosure (FractionRing W) C
  have : IsAlgClosed F := (algebraicClosure.isAlgClosure (FractionRing W) C).isAlgClosed
  let : Algebra W F := ((algebraMap (FractionRing W) F).comp (algebraMap W _)).toAlgebra
  have : IsScalarTower W (FractionRing W) F := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have iW : Function.Injective (algebraMap W F) :=
    (algebraMap (FractionRing W) F).injective.comp (IsFractionRing.injective W _)
  have : FaithfulSMul W F := (faithfulSMul_iff_algebraMap_injective W F).2 iW
  have : Algebra.IsAlgebraic W F :=
    (IsFractionRing.comap_isAlgebraic_iff (A := W) (K := FractionRing W) (C := F)).2 inferInstance
  have : CharZero (FractionRing W) := IsFractionRing.charZero_of_isFractionRing W
  have : CharZero C := charZero_of_injective_algebraMap (algebraMap (FractionRing W) C).injective
  obtain ⟨t₁, ht₁⟩ := exists_finset_ratTors hL (algebraMap F C) (jK W ≫ s₁) B₁ hn
  obtain ⟨t₂, ht₂⟩ := exists_finset_ratTors hL (algebraMap F C) (jK W ≫ s₂) B₂ hn
  obtain ⟨V, dV, cV, -, fV, -, lV, hV, -⟩ := exists_complete_dvr_finite_subalgebra W F (t₁ ∪ t₂)
  have i₁ : Function.Injective (algebraMap V F) := Subtype.val_injective
  let β : FractionRing V →+* F := IsFractionRing.lift i₁
  have hβ : ∀ x, β (algebraMap V _ x) = algebraMap V F x := IsFractionRing.lift_algebraMap i₁
  let : Algebra (FractionRing V) C := ((algebraMap F C).comp β).toAlgebra
  have hA : Along (algebraMap W V) C := fun x => congrArg (algebraMap F C) (hβ _)
  have h₁ : ∀ c, algebraMap (FractionRing W) F c ∈ β.fieldRange := fun c => by
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := W) c
    rw [map_div₀]
    exact div_mem ⟨_, hβ (algebraMap W V a)⟩ ⟨_, hβ (algebraMap W V b)⟩
  have h₂ : ∀ c ∈ t₁ ∪ t₂, c ∈ β.fieldRange := fun x hx => by
    obtain ⟨u, hu, v, hv, h0, e⟩ := hV x hx
    refine ⟨algebraMap V _ ⟨u, hu⟩ / algebraMap V _ ⟨v, hv⟩, ?_⟩
    rw [map_div₀, hβ, hβ]
    exact (div_eq_iff h0).2 e.symm
  have e : spMap β ≫ jK V ≫ spMap (algebraMap W V) = spMap (algebraMap (FractionRing W) F) ≫ jK W := by
    rw [← Category.assoc, spMap_comp hβ, spMap_comp (d := algebraMap W F) fun _ => rfl]
    exact (spMap_comp fun _ => rfl).symm
  have : CharZero V := (algebraMap V F).charZero
  refine ⟨V, inferInstance, inferInstance, inferInstance, inferInstance, algebraMap W V, ⟨dV, cV, inferInstance⟩,
    fun a b h => iW (congrArg Subtype.val h), RingHom.finite_algebraMap.2 fV, lV, hA, cExt_of_integral hext hA,
    ht₁ V β (fun _ => rfl) h₁ (fun c hc => h₂ c (Finset.mem_union_left _ hc)) _ ?_,
    ht₂ V β (fun _ => rfl) h₁ (fun c hc => h₂ c (Finset.mem_union_right _ hc)) _ ?_⟩
  · rw [reassoc_of% e]
  · rw [reassoc_of% e]

end GlobalTheory.Ex.TorsionField
