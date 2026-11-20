import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumLifts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsCompModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedPointBelowAlgebraic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PotentialChartContDiffAtTwo
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualRef
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescentMapContinuousSurjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackSmoothFunctionCInfAtStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointHeightDualAndLinearCombStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EquidistributionAverageOverOrbitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeModelInducesRootMetricStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjPointNormPowEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChIntInvariantUnderConjugationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChIntAddFunctionsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NumericalIntersectionSmoothPullbackStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjInvariantNormPotentialCombStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConjSymmetricSmoothFunctionStatement

open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ArInt GlobalTheory.Mean4 GlobalTheory.Mean4O

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Mean4O.OnModel

section Generic

variable {F : Type} [Field F] [NumberField F] {Y : Var F} {V : Cover Y} {e : ℕ} {M : Man e} {I : ManIs M Y}
  {ε : (𝓞 F →+* ℂ) → Fin (M.n + 1)} {π : ∀ σ, CxPts V.p σ → M.X (ε σ)}

/- English proof (translation)
Introduce `a` and use `⟨(I.ε a).comp (algebraMap (𝓞 F) F), I.ε.injective (IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 F)) (hd _).1)⟩`.
-/
theorem surjective_idx (hd : V.IsDown I ε π) : Function.Surjective ε := fun a =>
  ⟨(I.ε a).comp (algebraMap (𝓞 F) F), I.ε.injective (IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 F)) (hd _).1)⟩

/- English proof (translation)
Rewrite using `[CompModel.sp_comp, show (starRingEnd ℂ).comp (starRingEnd ℂ) = RingHom.id ℂ from RingHom.ext Complex.conj_conj]`. Conclude with `Spec.map_id _`.
-/
theorem conj_conj : spMap (starRingEnd ℂ) ≫ spMap (starRingEnd ℂ) = 𝟙 (Sp ℂ) := by
  rw [CompModel.sp_comp, show (starRingEnd ℂ).comp (starRingEnd ℂ) = RingHom.id ℂ from RingHom.ext Complex.conj_conj]
  exact Spec.map_id _

/- English proof (translation)
Rewrite using `[h, ← Category.assoc, conj_conj, Category.id_comp]`.
-/
theorem conj_symm {X : Scheme.{0}} {y y' : Sp ℂ ⟶ X} (h : y' = spMap (starRingEnd ℂ) ≫ y) :
    y = spMap (starRingEnd ℂ) ≫ y' := by
  rw [h, ← Category.assoc, conj_conj, Category.id_comp]

/- English proof (translation)
Establish `h₁ : spMap (I.ε a) = spMap (I.ε b)` using `by rw [← (I.pt a x).2, ← (I.pt b y).2, h]`. Take `rfl : a = b` from `I.ε.injective (congrArg CommRingCat.Hom.hom (Spec.map_injective h₁))`. Rewrite using `[(I.pt a).injective (Subtype.ext h)]`.
-/
theorem val_eq (u : M.Fun) {a b : Fin (M.n + 1)} {x : M.X a} {y : M.X b} (h : (I.pt a x).1 = (I.pt b y).1) :
    u a x = u b y := by
  have h₁ : spMap (I.ε a) = spMap (I.ε b) := by rw [← (I.pt a x).2, ← (I.pt b y).2, h]
  obtain rfl : a = b := I.ε.injective (congrArg CommRingCat.Hom.hom (Spec.map_injective h₁))
  rw [(I.pt a).injective (Subtype.ext h)]

/- English proof (translation)
Use `CoverHt.isPreimmersion_j V` as an intermediate fact. Take `⟨w, h₁, h₂⟩` from `(hd σ).2 z`. Take `⟨w', h₁', h₂'⟩` from `(hd σ').2 z'`. Establish `h₃ : w' = spMap (starRingEnd ℂ) ≫ w` using `by rw [← cancel_mono V.j, h₁', Category.assoc, h₁, h]`. Rewrite using `[← h₂, ← h₂', h₃, Category.assoc]`.
-/
theorem down_conj (hd : V.IsDown I ε π) {σ σ' : 𝓞 F →+* ℂ} {z : CxPts V.p σ} {z' : CxPts V.p σ'}
    (h : z'.1 = spMap (starRingEnd ℂ) ≫ z.1) :
    (I.pt _ (π σ' z')).1 = spMap (starRingEnd ℂ) ≫ (I.pt _ (π σ z)).1 := by
  have := CoverHt.isPreimmersion_j V
  obtain ⟨w, h₁, h₂⟩ := (hd σ).2 z
  obtain ⟨w', h₁', h₂'⟩ := (hd σ').2 z'
  have h₃ : w' = spMap (starRingEnd ℂ) ≫ w := by rw [← cancel_mono V.j, h₁', Category.assoc, h₁, h]
  rw [← h₂, ← h₂', h₃, Category.assoc]

/- English proof (translation)
Take `⟨σ, rfl⟩` from `surjective_idx hd a`. Take `⟨z, rfl⟩` from `hs σ x`. Set `z' : CxPts V.p ((starRingEnd ℂ).comp σ)` to `⟨spMap (starRingEnd ℂ) ≫ z.1, by rw [Category.assoc, z.2, CompModel.sp_comp]⟩`. Conclude with `(val_eq u (h.trans (down_conj hd (z' := z') rfl).symm)).trans (hc σ _ PUnit.unit z z' rfl CxPts.mem_ptsIn_top)`.
-/
theorem inv_of_pull (hd : V.IsDown I ε π) (hs : ∀ σ, Function.Surjective (π σ)) {u : M.Fun}
    (hc : ∀ σ σ', (Weight.ofFun (M.pull ε π u σ)).IsConj (Weight.ofFun (M.pull ε π u σ')))
    (a a' : Fin (M.n + 1)) (x : M.X a) (x' : M.X a') (h : (I.pt a' x').1 = spMap (starRingEnd ℂ) ≫ (I.pt a x).1) :
    u a' x' = u a x := by
  obtain ⟨σ, rfl⟩ := surjective_idx hd a
  obtain ⟨z, rfl⟩ := hs σ x
  let z' : CxPts V.p ((starRingEnd ℂ).comp σ) :=
    ⟨spMap (starRingEnd ℂ) ≫ z.1, by rw [Category.assoc, z.2, CompModel.sp_comp]⟩
  exact (val_eq u (h.trans (down_conj hd (z' := z') rfl).symm)).trans
    (hc σ _ PUnit.unit z z' rfl CxPts.mem_ptsIn_top)

/- English proof (translation)
Assemble the required witnesses or components as `⟨I.ε.piCongrLeft (fun σ => Pts Y σ → ℝ) fun a y => f a ((I.pt a).symm y), fun a x => by rw [Equiv.piCongrLeft_apply_apply, Homeomorph.symm_apply_apply]⟩`.
-/
theorem exists_read (I : ManIs M Y) (f : M.Fun) :
    ∃ g : ∀ σ : F →+* ℂ, Pts Y σ → ℝ, ∀ a x, g (I.ε a) (I.pt a x) = f a x :=
  ⟨I.ε.piCongrLeft (fun σ => Pts Y σ → ℝ) fun a y => f a ((I.pt a).symm y), fun a x => by
    rw [Equiv.piCongrLeft_apply_apply, Homeomorph.symm_apply_apply]⟩

/- English proof (translation)
Introduce `u hu hu' hc n f hfs`. Establish `hcs` using `GlobalTheory.T.descent_map_continuous_surjective F Y V e M I ε π hd`. Take `⟨N, hN⟩` from `hf u hu (fun a a' x x' h => mul_left_cancel₀ (two_ne_zero (α := ℝ)) (inv_of_pull hd (fun σ => (hcs σ).2) hc a a' x x' h)) n`. Take `⟨f', hfs', hff⟩` from `GlobalTheory.T.exists_conj_symmetric_smooth_function F Y e M I f hfs`. Take `⟨g, hg⟩` from `exists_read I f`.

Take `⟨g', hg'⟩` from `exists_read I f'`. Establish `h₁` using `GlobalTheory.T.chInt_invariant_under_conjugation F Y.X Y.str Y.isProjOver N e g g' fun σ σ' y y' h => by`. Take `⟨a, rfl⟩` from `I.ε.surjective σ`. Take `⟨a', rfl⟩` from `I.ε.surjective σ'`. Take `⟨x, rfl⟩` from `(I.pt a).surjective y`.

Take `⟨x', rfl⟩` from `(I.pt a').surjective y'`. Rewrite using `[hg, hg', hff a a' x x' h]`. Rewrite `h₁` using `[hN f g hfs hg, hN f' g' hfs' hg']`. Establish `hsum : M.Smooth (f + f')` using `(InhabCalc.smSub M).add_mem hfs hfs'`. Establish `h₂` using `GlobalTheory.T.numerical_intersection_smooth_pullback hA e M _ V.X V.p K ε π ν ι L v har (GlobalTheory.T.pullback_smooth_function_cInfAt F Y V e M I ε π hd) hn u hu hu' hc n (f + f') hsum fun σ σ' _ z z' h _ => by`.

Establish `h'` using `down_conj hd h`. Express the relevant statement in the definitionally equal form `f _ _ + f' _ _ = f _ _ + f' _ _`. Rewrite using `[hff _ _ _ _ h', hff _ _ _ _ (conj_symm h'), add_comm]`. Establish `hcont (f : M.Fun) (hf : M.Smooth f) (σ) : Continuous (M.pull ε π f σ)` using `(projLine_continuous_of_smooth _ (hf _)).comp (hcs σ).1`. Establish `h₃` using `GlobalTheory.T.chInt_add_functions hA _ V.X V.p e har _ (fun o : Option ι => o.elim (fnB (M.pull ε π ((2 : ℝ) • u)) hu' hc) L) n _ _ (hcont f hfs) (hcont f' hfs')`.

Establish `h₄` using `GlobalTheory.T.chInt_invariant_under_conjugation _ V.X V.p har.isProjOver (ArInt.comb (fun o : Option ι => o.elim (fnB (M.pull ε π ((2 : ℝ) • u)) hu' hc) L) n) e (M.pull ε π f) (M.pull ε π f') fun σ σ' z z' h => hff _ _ _ _ (down_conj hd h)`. Establish `h₅ (a)` using `st_mInt_finset_sum (M.A a) (fun _ => K.c1 (∑ i, (n (some i) : ℝ) • v i + (n none : ℝ) • K.ar u) a) (fun _ => K.firstChern_isPotential _ a) (Finset.univ : Finset Bool) (fun b => if b then f a else f' a) (fun b => by cases b; exacts [projLine_continuous_of_smooth _ (hfs' a), projLi …`. Simplify using `only [Fintype.sum_bool, if_true, Bool.false_eq_true, if_false] at h₅`. Use `replace h₂ := h₃.symm.trans h₂`. Rewrite `h₂` using `[h₄, Man.int, Finset.sum_congr (f := fun a => mInt (M.A a) _ ((f + f') a)) rfl fun a _ => h₅ a, Finset.sum_add_distrib, h₁]`.

Rewrite using `[Man.int]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem chernOn_of (hA : GlobalTheory.Published.ArCalc) (hd : V.IsDown I ε π) (har : IsArithVar V.p e) {K : Calc M} {ν : ℝ}
    {ι : Type} [Fintype ι] {L : ι → HermLB V.p} {v : ι → K.V} (hn : K.NumOn ε π ν L v)
    (hf : ∀ u : M.Fun, M.Smooth u →
      (∀ a a' x x', (I.pt a' x').1 = spMap (starRingEnd ℂ) ≫ (I.pt a x).1 → u a' x' = u a x) → ∀ n : Option ι → ℤ,
      ∃ N : HermLB Y.str, ∀ (f : M.Fun) (g : ∀ σ : F →+* ℂ, Pts Y σ → ℝ), M.Smooth f →
        (∀ a x, g (I.ε a) (I.pt a x) = f a x) → chInt N e g = ∑ a, mInt (M.A a)
          (fun _ => K.c1 (∑ i, (n (some i) : ℝ) • v i + (n none : ℝ) • K.ar u) a) (f a)) :
    K.ChernOn ε π ν L v := by
  intro u hu hu' hc n f hfs
  have hcs := GlobalTheory.T.descent_map_continuous_surjective F Y V e M I ε π hd
  obtain ⟨N, hN⟩ := hf u hu (fun a a' x x' h => mul_left_cancel₀ (two_ne_zero (α := ℝ))
    (inv_of_pull hd (fun σ => (hcs σ).2) hc a a' x x' h)) n
  obtain ⟨f', hfs', hff⟩ := GlobalTheory.T.exists_conj_symmetric_smooth_function F Y e M I f hfs
  obtain ⟨g, hg⟩ := exists_read I f
  obtain ⟨g', hg'⟩ := exists_read I f'
  have h₁ := GlobalTheory.T.chInt_invariant_under_conjugation F Y.X Y.str Y.isProjOver N e g g' fun σ σ' y y' h => by
    obtain ⟨a, rfl⟩ := I.ε.surjective σ
    obtain ⟨a', rfl⟩ := I.ε.surjective σ'
    obtain ⟨x, rfl⟩ := (I.pt a).surjective y
    obtain ⟨x', rfl⟩ := (I.pt a').surjective y'
    rw [hg, hg', hff a a' x x' h]
  rw [hN f g hfs hg, hN f' g' hfs' hg'] at h₁
  have hsum : M.Smooth (f + f') := (InhabCalc.smSub M).add_mem hfs hfs'
  have h₂ := GlobalTheory.T.numerical_intersection_smooth_pullback hA e M _ V.X V.p K ε π ν ι L v har (GlobalTheory.T.pullback_smooth_function_cInfAt F Y V e M I ε π hd) hn u hu hu' hc n (f + f') hsum
    fun σ σ' _ z z' h _ => by
      have h' := down_conj hd h
      change f _ _ + f' _ _ = f _ _ + f' _ _
      rw [hff _ _ _ _ h', hff _ _ _ _ (conj_symm h'), add_comm]
  have hcont (f : M.Fun) (hf : M.Smooth f) (σ) : Continuous (M.pull ε π f σ) :=
    (projLine_continuous_of_smooth _ (hf _)).comp (hcs σ).1
  have h₃ := GlobalTheory.T.chInt_add_functions hA _ V.X V.p e har _ (fun o : Option ι => o.elim (fnB (M.pull ε π ((2 : ℝ) • u)) hu' hc) L) n _ _
    (hcont f hfs) (hcont f' hfs')
  have h₄ := GlobalTheory.T.chInt_invariant_under_conjugation _ V.X V.p har.isProjOver
    (ArInt.comb (fun o : Option ι => o.elim (fnB (M.pull ε π ((2 : ℝ) • u)) hu' hc) L) n) e (M.pull ε π f)
    (M.pull ε π f') fun σ σ' z z' h => hff _ _ _ _ (down_conj hd h)
  have h₅ (a) := st_mInt_finset_sum (M.A a)
    (fun _ => K.c1 (∑ i, (n (some i) : ℝ) • v i + (n none : ℝ) • K.ar u) a) (fun _ => K.firstChern_isPotential _ a)
    (Finset.univ : Finset Bool) (fun b => if b then f a else f' a)
    (fun b => by cases b; exacts [projLine_continuous_of_smooth _ (hfs' a), projLine_continuous_of_smooth _ (hfs a)])
  simp only [Fintype.sum_bool, if_true, Bool.false_eq_true, if_false] at h₅
  replace h₂ := h₃.symm.trans h₂
  rw [h₄, Man.int, Finset.sum_congr (f := fun a => mInt (M.A a) _ ((f + f') a)) rfl fun a _ => h₅ a,
    Finset.sum_add_distrib, h₁] at h₂
  rw [Man.int]
  linarith

/- English proof (translation)
Set `σ : F →+* AlgebraicClosure ℚ` to `(IsAlgClosed.lift (R := ℚ) (S := F) (M := AlgebraicClosure ℚ)).toRingHom`. Take `⟨z, rfl⟩` from `exists_geomPt V.ar (σ.comp (algebraMap (𝓞 F) F)) hx`. Establish `hz : z.1 ≫ V.p = spMap σ ≫ spMap (algebraMap (𝓞 F) F)` using `by rw [CompModel.sp_comp]; exact z.2`. Establish `hσ : σ.IsIntegral`. Establish `h : (σ.comp (algebraMap ℚ F)).IsIntegral`.

Rewrite using `[Subsingleton.elim (σ.comp (algebraMap ℚ F)) (algebraMap ℚ _)]`. Conclude with `fun x => (AlgebraicClosure.isAlgebraic ℚ).isIntegral.1 x`. Conclude with `RingHom.IsIntegral.tower_top _ _ h`. Establish `hint : IsIntegralHom (V.pb.lift z.1 (spMap σ) hz ≫ V.π ≫ Y.str)`. Rewrite using `[V.pb.lift_snd]`.

Conclude with `IsIntegralHom.SpecMap_iff.2 hσ`. Establish `hp : IsIntegralHom (V.pb.lift z.1 (spMap σ) hz)` using `IsIntegralHom.of_comp _ (V.π ≫ Y.str)`. Use `⟨below (V.pb.lift z.1 (spMap σ) hz), ?_, congrArg (fun q : Sp (AlgebraicClosure ℚ) ⟶ V.X => q (IsLocalRing.closedPoint _)) (V.pb.lift_fst z.1 (spMap σ) hz)⟩` and prove the remaining obligations. Use `(V.pb.lift z.1 (spMap σ) hz).isClosedMap _ (IsLocalRing.isClosed_singleton_closedPoint (AlgebraicClosure ℚ))` as an intermediate fact. Conclude with `(Set.image_singleton (f := ⇑(V.pb.lift z.1 (spMap σ) hz)) (a := IsLocalRing.closedPoint (AlgebraicClosure ℚ))) ▸ this`.
-/
theorem exists_closed_of_isAlgPt (V : Cover Y) {x : V.X} (hx : IsAlgPt x) :
    ∃ w : V.G, IsClosed ({w} : Set V.G) ∧ V.j w = x := by
  let σ : F →+* AlgebraicClosure ℚ := (IsAlgClosed.lift (R := ℚ) (S := F) (M := AlgebraicClosure ℚ)).toRingHom
  obtain ⟨z, rfl⟩ := exists_geomPt V.ar (σ.comp (algebraMap (𝓞 F) F)) hx
  have hz : z.1 ≫ V.p = spMap σ ≫ spMap (algebraMap (𝓞 F) F) := by rw [CompModel.sp_comp]; exact z.2
  have hσ : σ.IsIntegral := by
    have h : (σ.comp (algebraMap ℚ F)).IsIntegral := by
      rw [Subsingleton.elim (σ.comp (algebraMap ℚ F)) (algebraMap ℚ _)]
      exact fun x => (AlgebraicClosure.isAlgebraic ℚ).isIntegral.1 x
    exact RingHom.IsIntegral.tower_top _ _ h
  have hint : IsIntegralHom (V.pb.lift z.1 (spMap σ) hz ≫ V.π ≫ Y.str) := by
    rw [V.pb.lift_snd]
    exact IsIntegralHom.SpecMap_iff.2 hσ
  have hp : IsIntegralHom (V.pb.lift z.1 (spMap σ) hz) := IsIntegralHom.of_comp _ (V.π ≫ Y.str)
  refine ⟨below (V.pb.lift z.1 (spMap σ) hz), ?_,
    congrArg (fun q : Sp (AlgebraicClosure ℚ) ⟶ V.X => q (IsLocalRing.closedPoint _)) (V.pb.lift_fst z.1 (spMap σ) hz)⟩
  have := (V.pb.lift z.1 (spMap σ) hz).isClosedMap _ (IsLocalRing.isClosed_singleton_closedPoint (AlgebraicClosure ℚ))
  exact (Set.image_singleton (f := ⇑(V.pb.lift z.1 (spMap σ) hz))
    (a := IsLocalRing.closedPoint (AlgebraicClosure ℚ))) ▸ this

/- English proof (translation)
Take `⟨w₀, h₀⟩` from `V.π.surjective b`. Establish `hc : IsClosed (V.π ⁻¹' {b})` using `hb.preimage V.π.continuous`. Establish `: CompactSpace V.G` using `QuasiCompact.compactSpace_of_compactSpace (V.π ≫ Y.str)`. Take `⟨w, hw, hw'⟩` from `hc.exists_closed_singleton ⟨w₀, h₀⟩`. Conclude with `⟨w, hw', hw⟩`.
-/
theorem exists_closed_over (V : Cover Y) {b : Y.X} (hb : IsClosed ({b} : Set Y.X)) :
    ∃ w : V.G, IsClosed ({w} : Set V.G) ∧ V.π w = b := by
  obtain ⟨w₀, h₀⟩ := V.π.surjective b
  have hc : IsClosed (V.π ⁻¹' {b}) := hb.preimage V.π.continuous
  have : CompactSpace V.G := QuasiCompact.compactSpace_of_compactSpace (V.π ≫ Y.str)
  obtain ⟨w, hw, hw'⟩ := hc.exists_closed_singleton ⟨w₀, h₀⟩
  exact ⟨w, hw', hw⟩

end Generic

section Flag

open GlobalTheory.ShFam GlobalTheory.ShFam.Pad

variable {D : D7} {O : Setup D} {A : SlopeTestRemainingChoices O.Y} {T : Real0 O.Y} {H : Ht O.Y}

/- English proof (translation)
Establish `: IsAlgClosed Qb` using `(algebraicClosure.isAlgClosure ℚ ℂ).isAlgClosed`. Use `letI : Algebra D.what₂.LL Qb := (IsAlgClosed.lift (R := ℚ) (S := D.what₂.LL) (M := Qb)).toRingHom.toAlgebra`. Take `⟨⟨⟨p, -⟩, rfl⟩⟩` from `(ExtConj.closed_point_geometric_fibres_finite (K := Qb) (O.var c).str b hb).1`. Take `⟨y, h₁, h₂⟩` from `CompModel.exists_flagPt (O.Φ.C c) p`. Establish `h : LiesUnder O.Φ c y (below p)` using `⟨p, h₁, h₂, rfl⟩`.

Take `rfl : compPt O.s y = c` from `h.compPt_eq`. Conclude with `⟨y, rfl, (existsUnique_liesUnder O.Φ y).unique (liesUnder_basePt O.Φ y) h⟩`.
-/
theorem exists_baseOn (c : O.s.Comp) {b : (O.var c).X} (hb : IsClosed ({b} : Set (O.var c).X)) :
    ∃ y : Pt O.s, compPt O.s y = c ∧ baseOn O.Φ c y = b := by
  have : IsAlgClosed Qb := (algebraicClosure.isAlgClosure ℚ ℂ).isAlgClosed
  letI : Algebra D.what₂.LL Qb := (IsAlgClosed.lift (R := ℚ) (S := D.what₂.LL) (M := Qb)).toRingHom.toAlgebra
  obtain ⟨⟨⟨p, -⟩, rfl⟩⟩ := (ExtConj.closed_point_geometric_fibres_finite (K := Qb) (O.var c).str b hb).1
  obtain ⟨y, h₁, h₂⟩ := CompModel.exists_flagPt (O.Φ.C c) p
  have h : LiesUnder O.Φ c y (below p) := ⟨p, h₁, h₂, rfl⟩
  obtain rfl : compPt O.s y = c := h.compPt_eq
  exact ⟨y, rfl, (existsUnique_liesUnder O.Φ y).unique (liesUnder_basePt O.Φ y) h⟩

/- English proof (translation)
Take `⟨p, -, -, hp⟩` from `liesUnder_basePt O.Φ y`. Rewrite using `[← hp]`. Conclude with `isClosed_below_algebraic _ _ p`.
-/
theorem isClosed_basePt (y : Pt O.s) : IsClosed ({basePt O.Φ y} : Set (O.var (compPt O.s y)).X) := by
  obtain ⟨p, -, -, hp⟩ := liesUnder_basePt O.Φ y
  rw [← hp]
  exact isClosed_below_algebraic _ _ p

/- English proof (translation)
Establish `hu' : (T.M c).Smooth ((n none : ℝ) • u)` using `(InhabCalc.smSub (T.M c)).smul_mem _ hu`. Use `GlobalTheory.T.conj_invariant_norm_potential_comb _ (cxSt _) (O.var c) _ (T.M c) (h.man c) (Option (DV.Rt D.what₂.Tau O.N)) (fun o => o.elim (O.met.ab c).D fun x => divOf (O.Φ.C c) (O.ex x)) (fun o σ => match o with` and prove the remaining obligations. Consider the case `none => (O.met.ab c).m σ`. Consider the case `some x => O.met.h0 c σ (O.ex x))`. Use the proof step `(fun o => o.elim (n (some none) * W.k) fun x => -n (some (some x))) _ _ ?_ hu'`.

Use the proof step `(fun a a' x x' e => congrArg ((n none : ℝ) * ·) (hc a a' x x' e)) ((T.K B c).firstChern_isPotential _) fun a => ?_`. Introduce and unpack `(_ | x) σ σ' y y' e`. Establish `pos (σ) (y : Pts (O.var c) σ) : PosAt ((O.met.ab c).m σ) y`. Take `⟨a, rfl⟩` from `(h.man c).ε.surjective σ`. Take `⟨x, rfl⟩` from `((h.man c).pt a).surjective y`.

Take `⟨Q, hQ, -⟩` from `(h.an c).a a`. Take `⟨f, hf⟩` from `(hQ ()).1 x`. Conclude with `(hf x ((Q ()).mem_U x)).2.1`. Conclude with `(pow_left_inj₀ (pos σ' y').le (pos σ y).le W.k_pos.ne').1 (GlobalTheory.T.conj_point_norm_pow_eq _ _ _ W.V _ _ _ W.amp_spec σ σ' y y' e)`. Establish `key (r) (hr : expo O.S.Dw (rootSym O.S.Dw (ArIn.ind P) none (DV.tauEmb D x.1) x.2) = r) : (cxSt _).pn _ σ' _ (O.met.h0 c σ' r) ((cxSt _).cx _ σ' (genAt (divOf (O.Φ.C c) r) (under y'))) y' = (cxSt _).pn _ σ _ (O.met.h0 c σ r) ((cxSt _).cx _ σ (genAt (divOf (O.Φ.C c) r) (under y))) …`.

Substitute `hr` using the available equality. Use `GlobalTheory.T.conj_point_norm_pow_eq _ _ _ W.V _ _ _ (GlobalTheory.T.lattice_model_induces_root_metric D O hO P c W P subset_rfl x) σ σ' y y' e` as an intermediate fact. Rewrite `this` using `[pow_one, pow_one]`. Conclude with `this`. Conclude with `key _ (expo_rootSym _ _ _ _ _)`.

Set `U : D.what₂.Tau → Fin O.N → ℝ` to `fun τ i => n (some (some (τ, i)))`. Take `⟨Q₁, h₁, e₁⟩` from `(h.an c).th U a`. Take `⟨Q₂, h₂, e₂⟩` from `(h.an c).a a`. Use `⟨fun o => o.elim (Q₂ ()) Q₁, ?_, fun j y hy w => ?_⟩` and prove the remaining obligations. Introduce and unpack `(_ | x) exacts [h₂ (), h₁ x]`.

Establish `hU : ∑ x : D.what₂.Tau × Fin O.Y.N, (n (some (some x)) : ℝ) • T.gen B c W.mult (some x) = T.L B c U`. Simplify using `only [Real0.gen, Option.elim, ← map_smul, ← map_sum]`. Use `congr 1`. Use function extensionality and compare the values at `τ i`. Simplify using `only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]`.

Rewrite using `[Finset.sum_eq_single (τ, i)]`. Simplify using `[U]`. Introduce and unpack `⟨τ', i'⟩ - hne`. Distinguish the cases in `hτ : τ' = τ`. Substitute `hτ` using the available equality.

Establish `: i ≠ i'` using `fun e => hne (e ▸ rfl)`. Simplify using `[Pi.single_eq_of_ne this]`. Simplify using `[Pi.single_eq_of_ne (Ne.symm hτ)]`. Simplify using the standard rewrite rules. Establish `hn : (((O.met.ab c).n : ℕ) : ℝ) ≠ 0` using `Nat.cast_ne_zero.2 (O.met.ab c).n.ne_zero`.

Establish `pot (v)` using `(T.K B c).firstChern_isPotential v a`. Rewrite using `[Fintype.sum_option, hU, ← map_smul, (T.K B c).isOneCochain_add _ _ a j y hy w, Deg.leviAt_add _ (pot _) (pot _) j hy, (T.K B c).isOneCochain_add _ _ a j y hy w, Deg.leviAt_add _ (pot _) (pot _) j hy, (T.K B c).c1_ar _ hu' a j y hy w, T.c1_L B c U a j y hy w, e₁ j y hy w, (T.K B …`. Simplify using `only [Real0.gen, Option.elim]`. Rewrite using `[(T.K B c).firstChern_smul_leviEq _ _ a j y hy w, Deg.leviAt_rsmul, T.firstChern_leviEq_constant B c a j y hy w, e₂ j y hy w, Fintype.sum_option, Fintype.sum_unique, Setup.LatModel.mult]`. Simplify using `only [Option.elim, U]`.

Use `push_cast`. Clear the denominators using the available nonvanishing facts. Both sides reduce to the same expression.
-/
theorem exists_herm (h : O.Reads A T H) (hO : O.DualRef) (B : ℝ) (c : O.s.Comp) {P : Finset ℕ} (W : O.LatModel P c)
    (u : (T.M c).Fun) (hu : (T.M c).Smooth u)
    (hc : ∀ a a' x x', ((h.man c).pt a' x').1 = spMap (starRingEnd ℂ) ≫ ((h.man c).pt a x).1 → u a' x' = u a x)
    (n : Option (Option (D.what₂.Tau × Fin O.Y.N)) → ℤ) :
    ∃ N : HermLB (O.var c).str, ∀ (f : (T.M c).Fun) (g : ∀ σ : D.what₂.LL →+* ℂ, Pts (O.var c) σ → ℝ), (T.M c).Smooth f →
      (∀ a x, g ((h.man c).ε a) ((h.man c).pt a x) = f a x) → chInt N (Formalism.MainNotions.WeightThresholdDefs.dimY O.Y) g = ∑ a, mInt ((T.M c).A a)
        (fun _ => (T.K B c).c1 (∑ i, (n (some i) : ℝ) • T.gen B c W.mult i + (n none : ℝ) • (T.K B c).ar u) a) (f a) := by
  classical
  have hu' : (T.M c).Smooth ((n none : ℝ) • u) := (InhabCalc.smSub (T.M c)).smul_mem _ hu
  refine GlobalTheory.T.conj_invariant_norm_potential_comb _ (cxSt _) (O.var c) _ (T.M c) (h.man c) (Option (DV.Rt D.what₂.Tau O.N))
    (fun o => o.elim (O.met.ab c).D fun x => divOf (O.Φ.C c) (O.ex x))
    (fun o σ => match o with
      | none => (O.met.ab c).m σ
      | some x => O.met.h0 c σ (O.ex x))
    (fun o => o.elim (n (some none) * W.k) fun x => -n (some (some x))) _ _ ?_ hu'
    (fun a a' x x' e => congrArg ((n none : ℝ) * ·) (hc a a' x x' e)) ((T.K B c).firstChern_isPotential _) fun a => ?_
  · rintro (_ | x) σ σ' y y' e
    · have pos (σ) (y : Pts (O.var c) σ) : PosAt ((O.met.ab c).m σ) y := by
        obtain ⟨a, rfl⟩ := (h.man c).ε.surjective σ
        obtain ⟨x, rfl⟩ := ((h.man c).pt a).surjective y
        obtain ⟨Q, hQ, -⟩ := (h.an c).a a
        obtain ⟨f, hf⟩ := (hQ ()).1 x
        exact (hf x ((Q ()).mem_U x)).2.1
      exact (pow_left_inj₀ (pos σ' y').le (pos σ y).le W.k_pos.ne').1
        (GlobalTheory.T.conj_point_norm_pow_eq _ _ _ W.V _ _ _ W.amp_spec σ σ' y y' e)
    · have key (r) (hr : expo O.S.Dw (rootSym O.S.Dw (ArIn.ind P) none (DV.tauEmb D x.1) x.2) = r) :
          (cxSt _).pn _ σ' _ (O.met.h0 c σ' r) ((cxSt _).cx _ σ' (genAt (divOf (O.Φ.C c) r) (under y'))) y' =
            (cxSt _).pn _ σ _ (O.met.h0 c σ r) ((cxSt _).cx _ σ (genAt (divOf (O.Φ.C c) r) (under y))) y := by
        subst hr
        have := GlobalTheory.T.conj_point_norm_pow_eq _ _ _ W.V _ _ _ (GlobalTheory.T.lattice_model_induces_root_metric D O hO P c W P subset_rfl x) σ σ' y y' e
        rw [pow_one, pow_one] at this
        exact this
      exact key _ (expo_rootSym _ _ _ _ _)
  · let U : D.what₂.Tau → Fin O.N → ℝ := fun τ i => n (some (some (τ, i)))
    obtain ⟨Q₁, h₁, e₁⟩ := (h.an c).th U a
    obtain ⟨Q₂, h₂, e₂⟩ := (h.an c).a a
    refine ⟨fun o => o.elim (Q₂ ()) Q₁, ?_, fun j y hy w => ?_⟩
    · rintro (_ | x)
      exacts [h₂ (), h₁ x]
    have hU : ∑ x : D.what₂.Tau × Fin O.Y.N, (n (some (some x)) : ℝ) • T.gen B c W.mult (some x) = T.L B c U := by
      simp only [Real0.gen, Option.elim, ← map_smul, ← map_sum]
      congr 1
      funext τ i
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [Finset.sum_eq_single (τ, i)]
      · simp [U]
      · rintro ⟨τ', i'⟩ - hne
        by_cases hτ : τ' = τ
        · subst hτ
          have : i ≠ i' := fun e => hne (e ▸ rfl)
          simp [Pi.single_eq_of_ne this]
        · simp [Pi.single_eq_of_ne (Ne.symm hτ)]
      · simp
    have hn : (((O.met.ab c).n : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (O.met.ab c).n.ne_zero
    have pot (v) := (T.K B c).firstChern_isPotential v a
    rw [Fintype.sum_option, hU, ← map_smul, (T.K B c).isOneCochain_add _ _ a j y hy w, Deg.leviAt_add _ (pot _) (pot _) j hy,
      (T.K B c).isOneCochain_add _ _ a j y hy w, Deg.leviAt_add _ (pot _) (pot _) j hy, (T.K B c).c1_ar _ hu' a j y hy w,
      T.c1_L B c U a j y hy w, e₁ j y hy w, (T.K B c).firstChern_smul_leviEq _ _ a j y hy w, Deg.leviAt_rsmul]
    simp only [Real0.gen, Option.elim]
    rw [(T.K B c).firstChern_smul_leviEq _ _ a j y hy w, Deg.leviAt_rsmul, T.firstChern_leviEq_constant B c a j y hy w, e₂ j y hy w, Fintype.sum_option,
      Fintype.sum_unique, Setup.LatModel.mult]
    simp only [Option.elim, U]
    push_cast
    field_simp
    rfl

/- English proof (translation)
Break down `o with _ | x` into its components or cases. Use `(CoverHt.main hA _ _ _ W.V _ _ _ w hw W.amp_spec).2` as an intermediate fact. Rewrite `this` using `[e, ← h.pts_is.a B hB y]`. Simplify using `only [Real0.gen, Option.elim, map_smul, smul_eq_mul, Setup.LatModel.mult, Nat.cast_mul]`. Conclude with `this`.

Take `⟨h₁, h₂⟩` from `CoverHt.main hA _ _ _ W.V _ _ _ w hw (GlobalTheory.T.lattice_model_induces_root_metric D O hO _ _ W _ subset_rfl x)`. Establish `h₃` using `(GlobalTheory.T.point_height_dual_and_linear_comb hA _ _ _ _ W.V.ar _ h₁).1 _ _ h₂`. Establish `h₄ : h.pts.ht B (compPt O.s y) y (T.gen B _ W.mult (some x)) = -(O.root0 _ (FlagAr.setB O.Y B) x).ht (basePt O.Φ y)`. Use `(h.pts_is.L B hB y _).trans (congrArg (-·) ?_)` and prove the remaining obligations. Use `(Finset.sum_eq_single (ι := DV.Rt D.what₂.Tau O.N) x ?_ fun hx => absurd (Finset.mem_univ _) hx).trans ?_` and prove the remaining obligations.

Introduce and unpack `⟨τ', i'⟩ - hne`. Take `⟨τ, i⟩` from `x`. Use `mul_eq_zero_of_left ?_ _` and prove the remaining obligations. Distinguish the cases in `hτ : τ' = τ`. Substitute `hτ` using the available equality.

Conclude with `(congrFun (Pi.single_eq_same _ _) _).trans (Pi.single_eq_of_ne (fun e => hne (Prod.ext rfl e)) _)`. Conclude with `congrFun (Pi.single_eq_of_ne (M := fun _ => Fin O.Y.N → ℝ) hτ _) _`. Conclude with `(congrArg (· * _) ((congrFun (Pi.single_eq_same _ _) _).trans (Pi.single_eq_same _ _))).trans (one_mul _)`. Rewrite using `[h₄, ← e]`. Use `(congrArg _ ?_).mp h₃` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `-(((1 : ℕ) : ℝ) * ((1 : ℕ) : ℝ) * _) = _`. Simplify using the standard rewrite rules.
-/
theorem isPtHt_gens (hA : GlobalTheory.Published.ArExists) (h : O.Reads A T H) (hO : O.DualRef) {B : ℝ} (hB : 2 ≤ B) (y : Pt O.s)
    (W : O.LatModel (FlagAr.setB O.Y B) (compPt O.s y)) {w : W.V.G} (hw : IsClosed ({w} : Set W.V.G))
    (e : W.V.π w = basePt O.Φ y) (o : Option (D.what₂.Tau × Fin O.Y.N)) :
    IsPtHt (W.gens (FlagAr.setB O.Y B) o) (W.V.j w) (h.pts.ht B (compPt O.s y) y (T.gen B _ W.mult o)) := by
  classical
  rcases o with _ | x
  · have := (CoverHt.main hA _ _ _ W.V _ _ _ w hw W.amp_spec).2
    rw [e, ← h.pts_is.a B hB y] at this
    simp only [Real0.gen, Option.elim, map_smul, smul_eq_mul, Setup.LatModel.mult, Nat.cast_mul]
    exact this
  · obtain ⟨h₁, h₂⟩ := CoverHt.main hA _ _ _ W.V _ _ _ w hw (GlobalTheory.T.lattice_model_induces_root_metric D O hO _ _ W _ subset_rfl x)
    have h₃ := (GlobalTheory.T.point_height_dual_and_linear_comb hA _ _ _ _ W.V.ar _ h₁).1 _ _ h₂
    have h₄ : h.pts.ht B (compPt O.s y) y (T.gen B _ W.mult (some x)) =
        -(O.root0 _ (FlagAr.setB O.Y B) x).ht (basePt O.Φ y) := by
      refine (h.pts_is.L B hB y _).trans (congrArg (-·) ?_)
      refine (Finset.sum_eq_single (ι := DV.Rt D.what₂.Tau O.N) x ?_ fun hx => absurd (Finset.mem_univ _) hx).trans ?_
      · rintro ⟨τ', i'⟩ - hne
        obtain ⟨τ, i⟩ := x
        refine mul_eq_zero_of_left ?_ _
        by_cases hτ : τ' = τ
        · subst hτ
          exact (congrFun (Pi.single_eq_same _ _) _).trans (Pi.single_eq_of_ne (fun e => hne (Prod.ext rfl e)) _)
        · exact congrFun (Pi.single_eq_of_ne (M := fun _ => Fin O.Y.N → ℝ) hτ _) _
      · exact (congrArg (· * _) ((congrFun (Pi.single_eq_same _ _) _).trans (Pi.single_eq_same _ _))).trans (one_mul _)
    rw [h₄, ← e]
    refine (congrArg _ ?_).mp h₃
    change -(((1 : ℕ) : ℝ) * ((1 : ℕ) : ℝ) * _) = _
    simp

end Flag

/- English proof (translation)
Introduce `hA D O A T H h hO B hB c`. Take `⟨W, hW⟩ : ∃ W : O.LatModel (FlagAr.setB O.Y B) c, O.NumIs (h.man c) B W` from `⟨_, h.num B hB c⟩`. Take `⟨ε, π, hd⟩` from `W.V.exists_isDown (h.man c)`. Establish `har : IsArithVar W.V.p (Formalism.MainNotions.WeightThresholdDefs.dimY O.Y)`. Use `W.V.ar` as an intermediate fact.

Rewrite `this` using `[O.dim_eq c]`. Conclude with `this`. Use `⟨_, inferInstance, W.V.X, inferInstance, W.V.p, ε, π, W.V.ν, W.mult, W.gens (FlagAr.setB O.Y B), fun x y => O.Y.compPt y = c ∧ ∃ w : W.V.G, IsClosed ({w} : Set _) ∧ W.V.j w = x ∧ W.V.π w = baseOn O.Φ c y, W.mult_pos, ⟨har, W.V.ν_pos, GlobalTheory.T.descent_map_continuous_surjecti …` and prove the remaining obligations. Take `⟨w, hw, rfl⟩` from `exists_closed_of_isAlgPt _ hx`. Establish `hb : IsClosed ({W.V.π w} : Set _)`.

Rewrite using `[← Set.image_singleton]`. Conclude with `W.V.π.isClosedMap _ hw`. Take `⟨y, hy, e⟩` from `exists_baseOn c hb`. Conclude with `⟨y, hy, w, hw, rfl, e.symm⟩`. Substitute `hy` using the available equality.

Take `⟨w, hw, e⟩` from `exists_closed_over W.V (isClosed_basePt y)`. Conclude with `⟨_, rfl, w, hw, rfl, e⟩`. Introduce and unpack `x y ⟨rfl, w, hw, rfl, e⟩`. Establish `halg` using `CoverHt.isAlgPt W.V w hw`. Use `⟨halg, rfl, fun g => ?_, fun n => ?_⟩` and prove the remaining obligations.

Conclude with `GlobalTheory.T.equidistribution_average_over_orbit _ _ _ _ _ (h.man _) ε π hd w hw (h.pts.d y) (h.pts.conj _ y) (by rw [e]; exact h.pts_is.conj y) g`. Rewrite using `[map_sum]`. Simplify using `only [map_smul, smul_eq_mul]`. Conclude with `(GlobalTheory.T.point_height_dual_and_linear_comb hA.arExists _ _ _ _ W.V.ar _ halg).2 _ _ _ (isPtHt_gens hA.arExists h hO hB y W hw e) n`.
-/
theorem onModel : GlobalTheory.Published.ArCalc → ∀ (D : D7) (O : Setup D) (A : SlopeTestRemainingChoices O.Y) (T : Real0 O.Y) (H : Ht O.Y)
    (h : O.Reads A T H), O.DualRef → h.pts.OnModel := by
  intro hA D O A T H h hO B hB c
  obtain ⟨W, hW⟩ : ∃ W : O.LatModel (FlagAr.setB O.Y B) c, O.NumIs (h.man c) B W := ⟨_, h.num B hB c⟩
  obtain ⟨ε, π, hd⟩ := W.V.exists_isDown (h.man c)
  have har : IsArithVar W.V.p (Formalism.MainNotions.WeightThresholdDefs.dimY O.Y) := by
    have := W.V.ar
    rw [O.dim_eq c] at this
    exact this
  refine ⟨_, inferInstance, W.V.X, inferInstance, W.V.p, ε, π, W.V.ν, W.mult, W.gens (FlagAr.setB O.Y B),
    fun x y => O.Y.compPt y = c ∧ ∃ w : W.V.G, IsClosed ({w} : Set _) ∧ W.V.j w = x ∧ W.V.π w = baseOn O.Φ c y,
    W.mult_pos, ⟨har, W.V.ν_pos, GlobalTheory.T.descent_map_continuous_surjective _ _ _ _ _ _ ε π hd, surjective_idx hd, GlobalTheory.T.pullback_smooth_function_cInfAt _ _ _ _ _ _ ε π hd,
      chernOn_of hA hd har (hW ε π hd) (exists_herm h hO B c W), hW ε π hd⟩, fun x hx => ?_, fun y hy => ?_, ?_⟩
  · obtain ⟨w, hw, rfl⟩ := exists_closed_of_isAlgPt _ hx
    have hb : IsClosed ({W.V.π w} : Set _) := by
      rw [← Set.image_singleton]
      exact W.V.π.isClosedMap _ hw
    obtain ⟨y, hy, e⟩ := exists_baseOn c hb
    exact ⟨y, hy, w, hw, rfl, e.symm⟩
  · subst hy
    obtain ⟨w, hw, e⟩ := exists_closed_over W.V (isClosed_basePt y)
    exact ⟨_, rfl, w, hw, rfl, e⟩
  · rintro x y ⟨rfl, w, hw, rfl, e⟩
    have halg := CoverHt.isAlgPt W.V w hw
    refine ⟨halg, rfl, fun g => ?_, fun n => ?_⟩
    · exact GlobalTheory.T.equidistribution_average_over_orbit _ _ _ _ _ (h.man _) ε π hd w hw (h.pts.d y) (h.pts.conj _ y) (by rw [e]; exact h.pts_is.conj y) g
    · rw [map_sum]
      simp only [map_smul, smul_eq_mul]
      exact (GlobalTheory.T.point_height_dual_and_linear_comb hA.arExists _ _ _ _ W.V.ar _ halg).2 _ _ _ (isPtHt_gens hA.arExists h hO hB y W hw e) n

end GlobalTheory.Mean4O.OnModel
