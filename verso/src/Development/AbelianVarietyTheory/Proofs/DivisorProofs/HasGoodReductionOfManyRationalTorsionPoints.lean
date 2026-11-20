import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsNeutralGroupModel
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.EqOneOfPowOfClosedPoint
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SemiAbelianReductionAlongIsogenyStrictHenselian
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLiftOfSchemeTheoreticallyDominant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianSchemeOfSmConnOfIsProperStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardAbelianVarietyTorsionSepClosedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProperOfInfinitelyManyLargeTorsionCountsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyIsProjectiveOverRingByChartsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProperSmoothConnGroupSchemeDvrOfProperFibresStatement

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.GoodRedTorsion

def secHom {S T : Scheme.{0}} (f : T ⟶ S) (G : Over S) [GrpObj G] :
    (𝟙_ (Over S) ⟶ G) →* (𝟙_ (Over T) ⟶ (Over.pullback f).obj G) :=
  (GlobalTheory.RedPts.precomp _ (Functor.LaxMonoidal.ε (Over.pullback f))).comp (Over.pullback f).homMonoidHom

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem secHom_apply {S T : Scheme.{0}} (f : T ⟶ S) (G : Over S) [GrpObj G] (s : 𝟙_ (Over S) ⟶ G) :
    secHom f G s = GlobalTheory.IsogRed.sec f s := rfl

/- English proof (translation)
Use `Finset.card_le_mul_card_image TF B fun y hy => ?_` and prove the remaining obligations. Take `⟨a0, ha0, rfl⟩` from `Finset.mem_image.1 hy`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.card_le_card_of_injOn (fun a => a * a0⁻¹) ?_ ?_` and prove the remaining obligations. Introduce `a ha`.

Establish `ha' : a ∈ TF.filter fun x => F x = F a0` using `by simpa using ha`. Take `⟨haT, haF⟩` from `Finset.mem_filter.1 ha'`. Establish `h1 : (a * a0⁻¹) ^ m = 1` using `by rw [mul_pow, inv_pow, hT a haT, hT a0 ha0]; simp`. Establish `h2 : (a * a0⁻¹) ^ c = 1` using `by rw [mul_pow, inv_pow, hF a haT a0 ha0 haF, mul_inv_cancel]`. Simplify using `using pow_gcd_eq_one.2 ⟨h1, h2⟩`.

Introduce `a _ b _ h`. Simplify using `using h`. Use `_ = {x : M | x ^ Nat.gcd m c = 1}.ncard := (Set.ncard_eq_toFinset_card _ hfin).symm`. Use `_ ≤ B := hB`.
-/
theorem card_le_of_fibres {M N : Type} [CommGroup M] [DecidableEq N] (TF : Finset M) (m c B : ℕ)
    (hT : ∀ a ∈ TF, a ^ m = 1) (F : M → N)
    (hF : ∀ a ∈ TF, ∀ b ∈ TF, F a = F b → a ^ c = b ^ c)
    (hfin : {x : M | x ^ Nat.gcd m c = 1}.Finite) (hB : {x : M | x ^ Nat.gcd m c = 1}.ncard ≤ B) :
    TF.card ≤ B * (TF.image F).card := by
  classical
  refine Finset.card_le_mul_card_image TF B fun y hy => ?_
  obtain ⟨a0, ha0, rfl⟩ := Finset.mem_image.1 hy
  calc (TF.filter fun x => F x = F a0).card ≤ hfin.toFinset.card := by
        refine Finset.card_le_card_of_injOn (fun a => a * a0⁻¹) ?_ ?_
        · intro a ha
          have ha' : a ∈ TF.filter fun x => F x = F a0 := by simpa using ha
          obtain ⟨haT, haF⟩ := Finset.mem_filter.1 ha'
          have h1 : (a * a0⁻¹) ^ m = 1 := by rw [mul_pow, inv_pow, hT a haT, hT a0 ha0]; simp
          have h2 : (a * a0⁻¹) ^ c = 1 := by rw [mul_pow, inv_pow, hF a haT a0 ha0 haF, mul_inv_cancel]
          simpa using pow_gcd_eq_one.2 ⟨h1, h2⟩
        · intro a _ b _ h
          simpa using h
    _ = {x : M | x ^ Nat.gcd m c = 1}.ncard := (Set.ncard_eq_toFinset_card _ hfin).symm
    _ ≤ B := hB

/- English proof (translation)
Establish `hc` using `GlobalTheory.T.card_abelianVariety_torsion_sepClosed K (AlgebraicClosure K) A hA g hg d hd`. Set `u : ptOver K (AlgebraicClosure K) ⟶ 𝟙_ (Over (Sp K))` to `toUnit _`. Establish `hu : u.left = spMap (algebraMap K (AlgebraicClosure K))` using `by simpa using Over.w u`. Establish `hdom : IsDominant (spMap (algebraMap K (AlgebraicClosure K)))` using `⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2 (by`. Express the relevant statement in the definitionally equal form `RingHom.ker (algebraMap K (AlgebraicClosure K)) ≤ _`.

Rewrite using `[(RingHom.injective_iff_ker_eq_bot _).1 (algebraMap K (AlgebraicClosure K)).injective]`. Conclude with `bot_le)⟩`. Establish `: IsProper A.hom` using `hA.proper`. Establish `hinj : Function.Injective (fun x : 𝟙_ (Over (Sp K)) ⟶ A => u ≫ x)`. Introduce `x y h`.

Establish `h' : spMap (algebraMap K (AlgebraicClosure K)) ≫ x.left = spMap (algebraMap K (AlgebraicClosure K)) ≫ y.left`. Rewrite using `[← hu]`. Conclude with `congrArg Over.Hom.left h`. Conclude with `Over.OverMorphism.ext (ext_of_isDominant_of_isSeparated (X := Sp K) A.hom ((Over.w x).trans (Over.w y).symm) (spMap (algebraMap K (AlgebraicClosure K))) h')`. Establish `hd0 : d ≠ 0` using `by rintro rfl; exact hd Nat.cast_zero`.

Establish `hfinB : Finite {x : ptOver K (AlgebraicClosure K) ⟶ A // x ^ d = 1}` using `Nat.finite_of_card_ne_zero (by rw [hc]; exact pow_ne_zero _ hd0)`. Set `φ : {x : 𝟙_ (Over (Sp K)) ⟶ A | x ^ d = 1} → {x : ptOver K (AlgebraicClosure K) ⟶ A // x ^ d = 1}` to `fun x => ⟨u ≫ x.1, by rw [← MonObj.comp_pow, x.2, MonObj.comp_one]⟩`. Establish `hφ : Function.Injective φ` using `fun x y h => Subtype.ext (hinj (congrArg Subtype.val h))`. Establish `: Finite {x : 𝟙_ (Over (Sp K)) ⟶ A | x ^ d = 1}` using `Finite.of_injective φ hφ`. Use `⟨Set.toFinite _, ?_⟩` and prove the remaining obligations.

Rewrite using `[← Nat.card_coe_set_eq, ← hc]`. Conclude with `Nat.card_le_card_of_injective φ hφ`.
-/
theorem torsion_finite_ncard_le (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A]
    (hA : IsAbelianScheme A) (g : ℕ) (hg : SmoothOfRelativeDimension g A.hom) (d : ℕ) (hd : (d : K) ≠ 0) :
    {x : 𝟙_ (Over (Sp K)) ⟶ A | x ^ d = 1}.Finite ∧
      {x : 𝟙_ (Over (Sp K)) ⟶ A | x ^ d = 1}.ncard ≤ d ^ (2 * g) := by
  have hc := GlobalTheory.T.card_abelianVariety_torsion_sepClosed K (AlgebraicClosure K) A hA g hg d hd
  let u : ptOver K (AlgebraicClosure K) ⟶ 𝟙_ (Over (Sp K)) := toUnit _
  have hu : u.left = spMap (algebraMap K (AlgebraicClosure K)) := by simpa using Over.w u
  have hdom : IsDominant (spMap (algebraMap K (AlgebraicClosure K))) :=
    ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2 (by
      change RingHom.ker (algebraMap K (AlgebraicClosure K)) ≤ _
      rw [(RingHom.injective_iff_ker_eq_bot _).1 (algebraMap K (AlgebraicClosure K)).injective]; exact bot_le)⟩
  have : IsProper A.hom := hA.proper
  have hinj : Function.Injective (fun x : 𝟙_ (Over (Sp K)) ⟶ A => u ≫ x) := by
    intro x y h
    have h' : spMap (algebraMap K (AlgebraicClosure K)) ≫ x.left = spMap (algebraMap K (AlgebraicClosure K)) ≫ y.left := by
      rw [← hu]; exact congrArg Over.Hom.left h
    exact Over.OverMorphism.ext (ext_of_isDominant_of_isSeparated (X := Sp K) A.hom
      ((Over.w x).trans (Over.w y).symm) (spMap (algebraMap K (AlgebraicClosure K))) h')
  have hd0 : d ≠ 0 := by rintro rfl; exact hd Nat.cast_zero
  have hfinB : Finite {x : ptOver K (AlgebraicClosure K) ⟶ A // x ^ d = 1} :=
    Nat.finite_of_card_ne_zero (by rw [hc]; exact pow_ne_zero _ hd0)
  let φ : {x : 𝟙_ (Over (Sp K)) ⟶ A | x ^ d = 1} → {x : ptOver K (AlgebraicClosure K) ⟶ A // x ^ d = 1} :=
    fun x => ⟨u ≫ x.1, by rw [← MonObj.comp_pow, x.2, MonObj.comp_one]⟩
  have hφ : Function.Injective φ := fun x y h => Subtype.ext (hinj (congrArg Subtype.val h))
  have : Finite {x : 𝟙_ (Over (Sp K)) ⟶ A | x ^ d = 1} := Finite.of_injective φ hφ
  refine ⟨Set.toFinite _, ?_⟩
  rw [← Nat.card_coe_set_eq, ← hc]
  exact Nat.card_le_card_of_injective φ hφ

end GlobalTheory.GoodRedTorsion

namespace GlobalTheory.GoodRedTorsion

/- English proof (translation)
Introduce `R K _ _ _ _ _ hS A _ _ hA g hg hinf`. Take `⟨G, inst, hG, he, c, hc, hs⟩` from `GlobalTheory.SS.exists_neutral_group_model R K hS A hA (GlobalTheory.T.abelianVariety_isProjectiveOverRingByCharts K A hA)`. Take `⟨hDVR, hHen, hAC, hFR⟩` from `hS`. Use `hG.1` as an intermediate fact. Use `hG.2.1` as an intermediate fact.

Use `hG.2.2.1` as an intermediate fact. Use `GlobalTheory.schemeTheoreticallyDominant_fractionField R K` as an intermediate fact. Establish `heL : IsIso G.e.hom.left` using `inferInstanceAs (IsIso ((Over.forget _).map G.e.hom))`. Establish `hgenP : IsProper ((Over.pullback (spMap (algebraMap R K))).obj G.Y).hom`. Rewrite using `[← Over.w G.e.hom]`.

Use `hA.proper` as an intermediate fact. Use `infer_instance`. Establish `hGg : SmoothOfRelativeDimension g ((Over.pullback (spMap (algebraMap R K))).obj G.Y).hom` using `(smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (IsPullback.of_horiz_isIso (g := 𝟙 _) ⟨(Over.w G.e.hom).trans (Category.comp_id _).symm⟩) hg`. Set `ψ : (𝟙_ (Over (Sp R)) ⟶ G.Y) →* (𝟙_ (Over (Sp K)) ⟶ A)` to `{ toFun := fun t => secHom (spMap (algebraMap R K)) G.Y t ≫ G.e.hom map_one' := by rw [map_one]; exact MonObj.one_comp _ map_mul' := fun t t' => by rw [map_mul]; exact MonObj.mul_comp _ _ _ }`. Establish `hψinj : Function.Injective ψ` using `fun t t' h => GlobalTheory.IsogRed.sec_injective (spMap (algebraMap R K)) ((cancel_mono G.e.hom).1 h)`.

Establish `hψ : ∀ a : 𝟙_ (Over (Sp K)) ⟶ A, ∃ t, ψ t = a ^ c` using `fun a => by`. Take `⟨s, hs'⟩` from `hs a`. Use `⟨s, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `GlobalTheory.IsogRed.sec _ s ≫ G.e.hom = _`. Rewrite using `[GlobalTheory.IsogRed.sec_eq_comp _ G.e s (a ^ c) hs', Category.assoc, Iso.inv_hom_id, Category.comp_id]`.

Use `choose sA hsA using hψ`. Establish `hred : ∀ t : 𝟙_ (Over (Sp R)) ⟶ G.Y, ∀ n : ℕ, IsUnit (n : R) → t ^ n = 1 → secHom (spMap (residue R)) G.Y t = 1 → t = 1`. Introduce `t n hn htn ht`. Use `GlobalTheory.RedPts.eq_one_of_pow_of_closedPoint G.Y (𝟙 (Sp R)) hn t htn (Z := Over.mk (spMap (residue R))) (Over.homMk (spMap (residue R)) (Category.comp_id _)) ⟨IsLocalRing.closedPoint _, IsLocalRing.comap_closedPoint (IsLocalRing.residue R)⟩ ?_` and prove the remaining obligations. Rewrite using `[← MonObj.comp_one (Over.homMk (spMap (residue R)) (Category.comp_id _) : Over.mk (spMap (residue R)) ⟶ Over.mk (𝟙 (Sp R)))]`.

Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Establish `e1` using `GlobalTheory.IsogRed.sec_left (spMap (residue R)) t`. Establish `e2` using `GlobalTheory.IsogRed.sec_left (spMap (residue R)) (1 : 𝟙_ (Over (Sp R)) ⟶ G.Y)`. Establish `e3 : GlobalTheory.IsogRed.sec (spMap (residue R)) t = GlobalTheory.IsogRed.sec (spMap (residue R)) 1`. Rewrite using `[← secHom_apply, ← secHom_apply, map_one]`.

Conclude with `ht`. Express the relevant statement in the definitionally equal form `spMap (residue R) ≫ t.left = spMap (residue R) ≫ (1 : 𝟙_ (Over (Sp R)) ⟶ G.Y).left`. Rewrite using `[← e1, ← e2, e3]`. Establish `hunit : ∀ m : ℕ, (m : ResidueField R) ≠ 0 → IsUnit (m : R)` using `fun m hm => by`. Assume the negation of the conclusion as `h`.

Conclude with `hm (by rw [← map_natCast (residue R)]; exact (residue_eq_zero_iff _).2 ((mem_maximalIdeal _).2 h))`. Establish `hsp : IsProper (GlobalTheory.SS.spFibre G.Y).hom`. Use `GlobalTheory.T.isProper_of_infinitely_many_large_torsion (ResidueField R) (GlobalTheory.SS.spFibre G.Y) (GlobalTheory.IsogRed.smConn_baseChange _ _ hG) g (GlobalTheory.IsogRed.relDim_spFibre (K := K) G.Y hG g hGg) (c ^ (2 * g)) (hinf.mono ?_)` and prove the remaining obligations. Introduce and unpack `m ⟨hm, hcard⟩`. Use `⟨hm, ?_⟩` and prove the remaining obligations.

Establish `hm0 : m ≠ 0` using `by rintro rfl; exact hm Nat.cast_zero`. Establish `hmK : (m : K) ≠ 0`. Use `((hunit m hm).map (algebraMap R K)).ne_zero` as an intermediate fact. Rewrite `this` using `[map_natCast]`. Then use the resulting hypothesis. Establish `hfinT : {x : 𝟙_ (Over (Sp K)) ⟶ A | x ^ m = 1}.Finite`.

Establish `: Finite {x : 𝟙_ (Over (Sp K)) ⟶ A // x ^ m = 1}` using `Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ hm0)`. Conclude with `Set.finite_coe_iff.mp this`. Establish `hTcard : hfinT.toFinset.card = m ^ (2 * g)`. Rewrite using `[← hcard, ← Set.ncard_eq_toFinset_card _ hfinT, ← Nat.card_coe_set_eq]`. Both sides reduce to the same expression.

Establish `hT : ∀ a ∈ hfinT.toFinset, a ^ m = 1` using `fun a ha => by simpa using ha`. Establish `hsAm : ∀ a : 𝟙_ (Over (Sp K)) ⟶ A, a ^ m = 1 → sA a ^ m = 1` using `fun a ha => hψinj (by rw [map_pow, hsA, map_one, ← pow_mul, mul_comm, pow_mul, ha, one_pow])`. Use `⟨hfinT.toFinset.image fun a => secHom (spMap (residue R)) G.Y (sA a), ?_, ?_⟩` and prove the remaining obligations. Introduce `x hx`. Take `⟨a, ha, rfl⟩` from `Finset.mem_image.1 hx`.

Rewrite using `[← map_pow, hsAm a (hT a ha), map_one]`. Establish `hd : ((Nat.gcd m c : ℕ) : K) ≠ 0`. Take `⟨k, hk⟩` from `Nat.gcd_dvd_left m c`. Introduce `h0`. Apply `hmK` to reduce the goal to its premises.

Rewrite using `[hk, Nat.cast_mul, h0, zero_mul]`. Take `⟨hfin, hB⟩` from `torsion_finite_ncard_le K A hA g hg _ hd`. Rewrite using `[← hTcard]`. Use `card_le_of_fibres _ m c (c ^ (2 * g)) hT _ ?_ hfin (hB.trans (Nat.pow_le_pow_left (Nat.le_of_dvd hc (Nat.gcd_dvd_right m c)) _))` and prove the remaining obligations. Introduce `a ha b hb hab`.

Establish `ht : (sA a * (sA b)⁻¹) ^ m = 1`. Rewrite using `[mul_pow, inv_pow, hsAm a (hT a ha), hsAm b (hT b hb)]`. Simplify using the standard rewrite rules. Establish `h1` using `hred _ m (hunit m hm) ht (by rw [map_mul, map_inv, hab, mul_inv_cancel])`. Rewrite using `[← hsA a, ← hsA b, mul_inv_eq_one.1 h1]`.

Establish `hprop : IsProper G.Y.hom` using `GlobalTheory.T.isProper_smoothConnGroupScheme_dvr_of_proper_fibres R K G.Y hG hgenP hsp`. Conclude with `⟨G.Y, inst, GlobalTheory.T.isAbelianScheme_of_smConn_of_isProper' _ G.Y hG hprop, G.e, he⟩`.
-/
theorem hasGoodReduction_of_torsion : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [Algebra R K], GlobalTheory.SS.SH R K → ∀ (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ g : ℕ, SmoothOfRelativeDimension g A.hom → {m : ℕ | (m : ResidueField R) ≠ 0 ∧ Nat.card {x : 𝟙_ (Over (Sp K)) ⟶ A // x ^ m = 1} = m ^ (2 * g)}.Infinite → HasGoodReduction R K A := by
  intro R K _ _ _ _ _ hS A _ _ hA g hg hinf
  obtain ⟨G, inst, hG, he, c, hc, hs⟩ :=
    GlobalTheory.SS.exists_neutral_group_model R K hS A hA (GlobalTheory.T.abelianVariety_isProjectiveOverRingByCharts K A hA)
  obtain ⟨hDVR, hHen, hAC, hFR⟩ := hS
  have := hG.1
  have := hG.2.1
  have := hG.2.2.1
  have := GlobalTheory.schemeTheoreticallyDominant_fractionField R K
  have heL : IsIso G.e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map G.e.hom))
  have hgenP : IsProper ((Over.pullback (spMap (algebraMap R K))).obj G.Y).hom := by
    rw [← Over.w G.e.hom]; have := hA.proper; infer_instance
  have hGg : SmoothOfRelativeDimension g ((Over.pullback (spMap (algebraMap R K))).obj G.Y).hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback
      (IsPullback.of_horiz_isIso (g := 𝟙 _) ⟨(Over.w G.e.hom).trans (Category.comp_id _).symm⟩) hg
  let ψ : (𝟙_ (Over (Sp R)) ⟶ G.Y) →* (𝟙_ (Over (Sp K)) ⟶ A) :=
    { toFun := fun t => secHom (spMap (algebraMap R K)) G.Y t ≫ G.e.hom
      map_one' := by rw [map_one]; exact MonObj.one_comp _
      map_mul' := fun t t' => by rw [map_mul]; exact MonObj.mul_comp _ _ _ }
  have hψinj : Function.Injective ψ := fun t t' h =>
    GlobalTheory.IsogRed.sec_injective (spMap (algebraMap R K)) ((cancel_mono G.e.hom).1 h)
  have hψ : ∀ a : 𝟙_ (Over (Sp K)) ⟶ A, ∃ t, ψ t = a ^ c := fun a => by
    obtain ⟨s, hs'⟩ := hs a
    refine ⟨s, ?_⟩
    change GlobalTheory.IsogRed.sec _ s ≫ G.e.hom = _
    rw [GlobalTheory.IsogRed.sec_eq_comp _ G.e s (a ^ c) hs', Category.assoc, Iso.inv_hom_id, Category.comp_id]
  choose sA hsA using hψ
  have hred : ∀ t : 𝟙_ (Over (Sp R)) ⟶ G.Y, ∀ n : ℕ, IsUnit (n : R) → t ^ n = 1 →
      secHom (spMap (residue R)) G.Y t = 1 → t = 1 := by
    intro t n hn htn ht
    refine GlobalTheory.RedPts.eq_one_of_pow_of_closedPoint G.Y (𝟙 (Sp R)) hn t htn (Z := Over.mk (spMap (residue R)))
      (Over.homMk (spMap (residue R)) (Category.comp_id _))
      ⟨IsLocalRing.closedPoint _, IsLocalRing.comap_closedPoint (IsLocalRing.residue R)⟩ ?_
    rw [← MonObj.comp_one (Over.homMk (spMap (residue R)) (Category.comp_id _) :
      Over.mk (spMap (residue R)) ⟶ Over.mk (𝟙 (Sp R)))]
    apply Over.OverMorphism.ext
    have e1 := GlobalTheory.IsogRed.sec_left (spMap (residue R)) t
    have e2 := GlobalTheory.IsogRed.sec_left (spMap (residue R)) (1 : 𝟙_ (Over (Sp R)) ⟶ G.Y)
    have e3 : GlobalTheory.IsogRed.sec (spMap (residue R)) t = GlobalTheory.IsogRed.sec (spMap (residue R)) 1 := by
      rw [← secHom_apply, ← secHom_apply, map_one]; exact ht
    change spMap (residue R) ≫ t.left = spMap (residue R) ≫ (1 : 𝟙_ (Over (Sp R)) ⟶ G.Y).left
    rw [← e1, ← e2, e3]
  have hunit : ∀ m : ℕ, (m : ResidueField R) ≠ 0 → IsUnit (m : R) := fun m hm => by
    by_contra h
    exact hm (by rw [← map_natCast (residue R)]; exact (residue_eq_zero_iff _).2 ((mem_maximalIdeal _).2 h))
  have hsp : IsProper (GlobalTheory.SS.spFibre G.Y).hom := by
    refine GlobalTheory.T.isProper_of_infinitely_many_large_torsion (ResidueField R) (GlobalTheory.SS.spFibre G.Y) (GlobalTheory.IsogRed.smConn_baseChange _ _ hG) g
      (GlobalTheory.IsogRed.relDim_spFibre (K := K) G.Y hG g hGg) (c ^ (2 * g)) (hinf.mono ?_)
    rintro m ⟨hm, hcard⟩
    refine ⟨hm, ?_⟩
    have hm0 : m ≠ 0 := by rintro rfl; exact hm Nat.cast_zero
    have hmK : (m : K) ≠ 0 := by
      have := ((hunit m hm).map (algebraMap R K)).ne_zero
      rwa [map_natCast] at this
    have hfinT : {x : 𝟙_ (Over (Sp K)) ⟶ A | x ^ m = 1}.Finite := by
      have : Finite {x : 𝟙_ (Over (Sp K)) ⟶ A // x ^ m = 1} :=
        Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ hm0)
      exact Set.finite_coe_iff.mp this
    have hTcard : hfinT.toFinset.card = m ^ (2 * g) := by
      rw [← hcard, ← Set.ncard_eq_toFinset_card _ hfinT, ← Nat.card_coe_set_eq]; rfl
    have hT : ∀ a ∈ hfinT.toFinset, a ^ m = 1 := fun a ha => by simpa using ha
    have hsAm : ∀ a : 𝟙_ (Over (Sp K)) ⟶ A, a ^ m = 1 → sA a ^ m = 1 := fun a ha =>
      hψinj (by rw [map_pow, hsA, map_one, ← pow_mul, mul_comm, pow_mul, ha, one_pow])
    classical
    refine ⟨hfinT.toFinset.image fun a => secHom (spMap (residue R)) G.Y (sA a), ?_, ?_⟩
    · intro x hx
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hx
      rw [← map_pow, hsAm a (hT a ha), map_one]
    · have hd : ((Nat.gcd m c : ℕ) : K) ≠ 0 := by
        obtain ⟨k, hk⟩ := Nat.gcd_dvd_left m c
        intro h0
        apply hmK
        rw [hk, Nat.cast_mul, h0, zero_mul]
      obtain ⟨hfin, hB⟩ := torsion_finite_ncard_le K A hA g hg _ hd
      rw [← hTcard]
      refine card_le_of_fibres _ m c (c ^ (2 * g)) hT _ ?_ hfin
        (hB.trans (Nat.pow_le_pow_left (Nat.le_of_dvd hc (Nat.gcd_dvd_right m c)) _))
      intro a ha b hb hab
      have ht : (sA a * (sA b)⁻¹) ^ m = 1 := by
        rw [mul_pow, inv_pow, hsAm a (hT a ha), hsAm b (hT b hb)]; simp
      have h1 := hred _ m (hunit m hm) ht (by rw [map_mul, map_inv, hab, mul_inv_cancel])
      rw [← hsA a, ← hsA b, mul_inv_eq_one.1 h1]
  have hprop : IsProper G.Y.hom := GlobalTheory.T.isProper_smoothConnGroupScheme_dvr_of_proper_fibres R K G.Y hG hgenP hsp
  exact ⟨G.Y, inst, GlobalTheory.T.isAbelianScheme_of_smConn_of_isProper' _ G.Y hG hprop, G.e, he⟩

end GlobalTheory.GoodRedTorsion
