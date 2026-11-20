import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UValThruTopOfDisjoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdealSheafPullbackEqDivisorOfApproxStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryApproxPoincareSeriesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryTraitThroughModuliGenericPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClassicalPointCentredClosedPointArithmeticStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormLocalEquationEqUniformiserPowClassicalPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimeEqOfClassicalPointSameCentreStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationScaledMultiple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryTraitOfClassicalPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryApproxPoincareSeriesAtMulStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenCompactificationGenericSubsetModuliStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

noncomputable section

namespace GlobalTheory.UPoinc.DescentPow

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {C : UCompact Xo c}

/- English proof (translation)
Take `⟨T, ι', j, ξ, hint, hj, hloc, hξ, hT⟩` from `GlobalTheory.T.exists_unitaryTrait_of_classicalPoint E H Dw l Xo c C X₁ Y πY p y hy`. Establish `hgen : gPt p ≫ y = spMap ι' ≫ jK T.V ≫ ξ`. Rewrite using `[← hξ, ← Category.assoc, ← Category.assoc]`. Use `congr 1`. Rewrite using `[← Spec.map_comp, ← Spec.map_comp]`.

Use `congr 1`. Use extensionality with `v`. Conclude with `hj v`. Use `⟨⟨y ≫ πY, ?_, T, ι', hint, ?_⟩, rfl, fun f hf => ?_⟩` and prove the remaining obligations. Rewrite using `[Scheme.Hom.comp_apply]`.

Conclude with `hz`. Rewrite using `[← Category.assoc, ← Category.assoc, hgen]`. Simplify using `only [Category.assoc]`. Rewrite using `[hT]`. Take `⟨tK, h1, h2⟩` from `T.gen`.

Take `⟨a, ha, hI⟩` from `hord T.V T.cdvr T.ϖ T.irr ξ T.y (by rw [← hT]) trivial T.t tK h1 h2 T.P T.be T.lev T.mono`. Establish `hc : ξ (closedPoint T.V) = y (cPt p)`. Rewrite using `[← hξ, Scheme.Hom.comp_apply]`. Conclude with `congrArg ξ (IsLocalRing.comap_closedPoint j).symm`. Rewrite `hf` using `[← hc]`.

Establish `key` using `GlobalTheory.T.norm_localEquation_eq_uniformiser_pow_classicalPoint _ _ Y D T.V T.ϖ a ξ p ι' j hint hj hI f hf`. Rewrite `key` using `[hξ]`. Establish `hpos : 0 < ‖ι' (algebraMap T.V (FractionRing T.V) T.ϖ)‖`. Use `norm_pos_iff.2 ?_` and prove the remaining obligations. Rewrite using `[map_ne_zero, Ne, IsFractionRing.to_map_eq_zero_iff]`.

Conclude with `T.irr.ne_zero`. Use `show _ = Real.exp (-(-Real.log ‖ι' (algebraMap T.V (FractionRing T.V) T.ϖ)‖ * (ι * φ.evalZ T.be)))`. Rewrite using `[key, ← ha, neg_mul, neg_neg, mul_comm, Real.exp_nat_mul, Real.exp_log hpos]`.
-/
theorem exists_uCTrait_norm_eqAt (X₁ : USetup C) (Y : RatModel X₁.o₁ X₁.Ω₁) (πY : Y.Z ⟶ X₁.M.Z)
    (φ : InvFun (𝓞 E)) (ι : ℕ) (D : EffCartierData Y.Z)
    (hord : UValThru Xo c C.i (πY ≫ X₁.π) Set.univ φ D.idealSheaf ι)
    (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ Y.Z) (hy : Set.range (gPt p ≫ y ≫ πY ≫ X₁.π) ⊆ Set.range C.i)
    (z₁ : X₁.M.Z) (hz : πY (y (cPt p)) = z₁) :
    ∃ t : UCTrait X₁ p z₁, t.y = y ≫ πY ∧ ∀ f, EqAt Y D (y (cPt p)) f →
      ‖Y.val (gPt p ≫ y) f‖ = Real.exp (-(t.sc * (ι * φ.evalZ t.T.be))) := by
  obtain ⟨T, ι', j, ξ, hint, hj, hloc, hξ, hT⟩ := GlobalTheory.T.exists_unitaryTrait_of_classicalPoint E H Dw l Xo c C X₁ Y πY p y hy
  have hgen : gPt p ≫ y = spMap ι' ≫ jK T.V ≫ ξ := by
    rw [← hξ, ← Category.assoc, ← Category.assoc]
    congr 1
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext v
    exact hj v
  refine ⟨⟨y ≫ πY, ?_, T, ι', hint, ?_⟩, rfl, fun f hf => ?_⟩
  · rw [Scheme.Hom.comp_apply]; exact hz
  · rw [← Category.assoc, ← Category.assoc, hgen]
    simp only [Category.assoc]
    rw [hT]
  · obtain ⟨tK, h1, h2⟩ := T.gen
    obtain ⟨a, ha, hI⟩ := hord T.V T.cdvr T.ϖ T.irr ξ T.y (by rw [← hT]) trivial T.t tK h1 h2 T.P T.be T.lev T.mono
    have hc : ξ (closedPoint T.V) = y (cPt p) := by
      rw [← hξ, Scheme.Hom.comp_apply]
      exact congrArg ξ (IsLocalRing.comap_closedPoint j).symm
    rw [← hc] at hf
    have key := GlobalTheory.T.norm_localEquation_eq_uniformiser_pow_classicalPoint _ _ Y D T.V T.ϖ a ξ p ι' j hint hj hI f hf
    rw [hξ] at key
    have hpos : 0 < ‖ι' (algebraMap T.V (FractionRing T.V) T.ϖ)‖ := by
      refine norm_pos_iff.2 ?_
      rw [map_ne_zero, Ne, IsFractionRing.to_map_eq_zero_iff]
      exact T.irr.ne_zero
    show _ = Real.exp (-(-Real.log ‖ι' (algebraMap T.V (FractionRing T.V) T.ϖ)‖ * (ι * φ.evalZ T.be)))
    rw [key, ← ha, neg_mul, neg_neg, mul_comm, Real.exp_nat_mul, Real.exp_log hpos]

/- English proof (translation)
Establish `hs : πY ((gPt q ≫ y) (closedPoint (PadicAlgCl q))) ⤳ z` using `hz ▸ (RatModel.gPt_specializes (M := Y) rfl _).map πY.continuous`. Use `hHom.val_comp (gPt q ≫ y) (closedPoint (PadicAlgCl q)) (RatModel.O_le_of_specializes hs ha)` as an intermediate fact. Rewrite using `[← Category.assoc]`. Conclude with `this.symm`.
-/
theorem val_comp_of_centre (X₁ : USetup C) (Y : RatModel X₁.o₁ X₁.Ω₁) (πY : Y.Z ⟶ X₁.M.Z)
    (hHom : X₁.M.IsHom Y (AlgHom.id X₁.o₁ X₁.Ω₁) πY) {q : ℕ} [Fact q.Prime] (y : Sp (OO q) ⟶ Y.Z) {z : X₁.M.Z}
    (hz : πY (y (cPt q)) = z) {a : X₁.Ω₁} (ha : a ∈ X₁.M.O z) :
    Y.val (gPt q ≫ y) a = X₁.M.val (gPt q ≫ y ≫ πY) a := by
  have hs : πY ((gPt q ≫ y) (closedPoint (PadicAlgCl q))) ⤳ z :=
    hz ▸ (RatModel.gPt_specializes (M := Y) rfl _).map πY.continuous
  have := hHom.val_comp (gPt q ≫ y) (closedPoint (PadicAlgCl q)) (RatModel.O_le_of_specializes hs ha)
  rw [← Category.assoc]
  exact this.symm

/- English proof (translation)
Introduce `E _ _ _ H Dw hpq φ hφ l Xo c C X₁ ι Y πY D hι hHom hprop hnorm hsupp hord`. Take `⟨d, hd, hA⟩` from `GlobalTheory.T.exists_unitaryApproxPoincareSeries E H Dw hpq l Xo c C X₁ φ hφ`. Take `⟨k, hk⟩ : ι ∣ Nat.lcm ι d` from `Nat.dvd_lcm_left ι d`. Take `⟨m, hm⟩ : d ∣ Nat.lcm ι d` from `Nat.dvd_lcm_right ι d`. Establish `hL0 : 0 < Nat.lcm ι d` using `Nat.lcm_pos hι hd`.

Establish `hk0 : 0 < k` using `Nat.pos_of_ne_zero fun h => by rw [h, mul_zero] at hk; omega`. Establish `hm0 : 0 < m` using `Nat.pos_of_ne_zero fun h => by rw [h, mul_zero] at hm; omega`. Establish `hAL : UApproxAt X₁ φ (Nat.lcm ι d)` using `hm ▸ GlobalTheory.T.unitaryApproxPoincareSeriesAt_mul E H Dw l Xo c C X₁ φ d m hm0 hA`. Establish `hord' : UValThru Xo c C.i (πY ≫ X₁.π) Set.univ φ (D.nsmul k).idealSheaf (Nat.lcm ι d)`. Introduce `W _ _ _ hW ϖ hϖ χ y hy hA' t tK h1 h2 P be hbe hmono`.

Take `⟨a, ha, hI⟩` from `hord W hW ϖ hϖ χ y hy hA' t tK h1 h2 P be hbe hmono`. Use `⟨k * a, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hk]`. Use `push_cast`. Rewrite using `[ha]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[GlobalTheory.TorRef.Scale.idlAlong_nsmul, hI, Ideal.span_singleton_pow, ← pow_mul, mul_comm a k]`. Establish `hsub : ∀ y ∈ (D.nsmul k).idealSheaf.support, y ∈ D.idealSheaf.support`. Introduce `y hy`. Take `⟨j, hj⟩` from `D.exists_mem y`.

Rewrite `hy` using `[(D.nsmul k).mem_support_iff j hj]`. Rewrite using `[D.mem_support_iff j hj]`. Introduce `h`. Apply `hy` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `y ∈ Y.Z.basicOpen (D.f j ^ k)`.

Rewrite using `[Scheme.basicOpen_pow _ _ hk0]`. Conclude with `h`. Take `⟨W, hWi, hWc⟩` from `GlobalTheory.T.exists_open_compactification_generic_subset_moduli E H Dw l Xo c C`. Set `U : Y.Z.Opens` to `(πY ≫ X₁.π) ⁻¹ᵁ W ⊓ ⟨((D.nsmul k).idealSheaf.support : Set Y.Z)ᶜ, (D.nsmul k).idealSheaf.support.isClosed.isOpen_compl⟩`. Establish `hU : (U : Set Y.Z).Nonempty`.

Establish `e : Y.pt ≫ πY ≫ X₁.π = spMap (AlgHom.id X₁.o₁ X₁.Ω₁).toRingHom ≫ spMap (ratHull X₁.S.R).val.toRingHom ≫ X₁.u ≫ C.i`. Rewrite using `[← Category.assoc, hHom, Category.assoc, X₁.comp]`. Establish `e'` using `congrArg (fun h : Sp X₁.Ω₁ ⟶ C.Z => h (closedPoint X₁.Ω₁)) e`. Simplify using `only [Scheme.Hom.comp_apply] at e'`. Establish `hr : X₁.π (πY (Y.pt (closedPoint X₁.Ω₁))) ∈ Set.range C.i` using `⟨_, e'.symm⟩`.

Use `⟨Y.pt (closedPoint X₁.Ω₁), ?_, ?_⟩` and prove the remaining obligations. Use `show (πY ≫ X₁.π) _ ∈ (W : Set C.Z)`. Rewrite using `[Scheme.Hom.comp_apply]`. Conclude with `hWi hr`. Introduce `hs`.

Conclude with `hsupp _ (hsub _ hs) hr`. Establish `hDU : ∀ x ∈ (D.nsmul k).idealSheaf.support, x ∉ U` using `fun x hx hxU => hxU.2 hx`. Establish `hrange : ∀ {q : ℕ} [Fact q.Prime] (y : Sp (OO q) ⟶ Y.Z), Set.range (gPt q ≫ y) ⊆ U → Set.range (gPt q ≫ y ≫ πY ≫ X₁.π) ⊆ Set.range C.i`. Introduce `q _ y hy`. Establish `h` using `hWc q (y ≫ πY ≫ X₁.π) (by`.

Introduce and unpack `_ ⟨w, rfl⟩`. Establish `h1 : (πY ≫ X₁.π) ((gPt q ≫ y) w) ∈ (W : Set C.Z)` using `(hy ⟨w, rfl⟩).1`. Simplify `h1)` using `only [Scheme.Hom.comp_apply]`. Simplify `h` using `only [Category.assoc]`. Take `⟨J, hJ⟩` from `GlobalTheory.T.exists_idealSheaf_pullback_eq_divisor_of_approx X₁.o₁ X₁.Ω₁ X₁.M Y πY hHom hprop (@GlobalTheory.IsNormalScheme.pred _ X₁.normal) hnorm U (D.nsmul k) hU hDU (by`.

Introduce `z₀ _ x hxz hx`. Take `⟨p, hp, y₀, hcen⟩` from `GlobalTheory.T.exists_classicalPoint_centred_closedPoint_arithmetic _ _ Y x hx U hU`. Take `⟨c₀, hc₀y, hc₀⟩` from `exists_uCTrait_norm_eqAt X₁ Y πY φ (Nat.lcm ι d) (D.nsmul k) hord' p y₀ (hrange y₀ hcen.2) z₀ (by rw [hcen.1, hxz])`. Use `⟨p, hp, y₀, hcen, fun e => ?_⟩` and prove the remaining obligations. Take `⟨f, hf0, hfall⟩` from `hAL p z₀ c₀ e`.

Establish `hfO : X₁.M.stalkHom z₀ f ∈ X₁.M.O z₀` using `(X₁.M.stalkEquiv z₀ f).2`. Use `⟨X₁.M.stalkHom z₀ f, hfO, fun f' hf' => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hc₀ f' (hcen.1 ▸ hf'), val_comp_of_centre X₁ Y πY hHom y₀ (by rw [hcen.1, hxz]) hfO, ← hf0] show _ = ‖X₁.M.val (gPt p ≫ c₀.y) _‖`. Rewrite using `[hc₀y]`. Introduce `q hq y hyz hyU f' hf'`.

Establish `hpq : p = q` using `GlobalTheory.T.prime_eq_of_classicalPoint_same_centre X₁.M.Z p q (y₀ ≫ πY) (y ≫ πY) (by`. Rewrite using `[Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hcen.1, hxz, hyz])`. Substitute `hpq` using the available equality. Take `⟨t, hty, ht⟩` from `exists_uCTrait_norm_eqAt X₁ Y πY φ (Nat.lcm ι d) (D.nsmul k) hord' p y (hrange y hyU) z₀ hyz`. Establish `hcv : ∀ a, t.val a = Y.val (gPt p ≫ y) (X₁.M.stalkHom z₀ a)` using `fun a => by`.

Rewrite using `[val_comp_of_centre X₁ Y πY hHom y hyz (a := X₁.M.stalkHom z₀ a) (X₁.M.stalkEquiv z₀ a).2]`. Use `show X₁.M.val (gPt p ≫ t.y) _ = _`. Rewrite using `[hty]`. Break down `hfall t with h1 | ⟨h, hh, h2⟩` into its components or cases. Use `left`.

Rewrite using `[← hcv, ht f' hf']`. Conclude with `h1`. Use `right`. Use `⟨X₁.M.stalkHom z₀ h, ⟨(X₁.M.stalkEquiv z₀ h).2, ?_⟩, ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hne push_neg at hne`.

Apply `(IsLocalRing.mem_maximalIdeal _).1 hh` to reduce the goal to its premises. Establish `hu : IsUnit (X₁.M.stalkEquiv z₀ h)` using `(RatModel.isUnit_O_iff _).2 ⟨hne.1, hne.2⟩`. Conclude with `(MulEquiv.isUnit_map (X₁.M.stalkEquiv z₀)).1 hu`. Rewrite using `[← hcv, ← hcv]`. Conclude with `h2)`.

Use `⟨Nat.lcm ι d, J, hL0, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hJ]`. Introduce `y hy`. Conclude with `hsupp y (hsub y hy)`. Rewrite using `[hJ]`.

Conclude with `hord'`.
-/
theorem exists_idealSheaf_comap_uValThru : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ φ : InvFun (𝓞 E), IsPolFan H.bar (min Dw.p Dw.q) φ → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C) (ι : ℕ) (Y : RatModel X₁.o₁ X₁.Ω₁) (πY : Y.Z ⟶ X₁.M.Z) (D : GlobalTheory.EffCartierData Y.Z), 1 ≤ ι → X₁.M.IsHom Y (AlgHom.id X₁.o₁ X₁.Ω₁) πY → IsProper πY → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Y.Z → (∀ y ∈ D.idealSheaf.support, X₁.π (πY y) ∉ Set.range C.i) → UValThru Xo c C.i (πY ≫ X₁.π) Set.univ φ D.idealSheaf ι → ∃ (ι' : ℕ) (J₁ : X₁.M.Z.IdealSheafData), 1 ≤ ι' ∧ (∀ y ∈ (J₁.comap πY).support, X₁.π (πY y) ∉ Set.range C.i) ∧ UValThru Xo c C.i (πY ≫ X₁.π) Set.univ φ (J₁.comap πY) ι' := by
  intro E _ _ _ H Dw hpq φ hφ l Xo c C X₁ ι Y πY D hι hHom hprop hnorm hsupp hord
  obtain ⟨d, hd, hA⟩ := GlobalTheory.T.exists_unitaryApproxPoincareSeries E H Dw hpq l Xo c C X₁ φ hφ
  obtain ⟨k, hk⟩ : ι ∣ Nat.lcm ι d := Nat.dvd_lcm_left ι d
  obtain ⟨m, hm⟩ : d ∣ Nat.lcm ι d := Nat.dvd_lcm_right ι d
  have hL0 : 0 < Nat.lcm ι d := Nat.lcm_pos hι hd
  have hk0 : 0 < k := Nat.pos_of_ne_zero fun h => by rw [h, mul_zero] at hk; omega
  have hm0 : 0 < m := Nat.pos_of_ne_zero fun h => by rw [h, mul_zero] at hm; omega
  have hAL : UApproxAt X₁ φ (Nat.lcm ι d) := hm ▸ GlobalTheory.T.unitaryApproxPoincareSeriesAt_mul E H Dw l Xo c C X₁ φ d m hm0 hA

  have hord' : UValThru Xo c C.i (πY ≫ X₁.π) Set.univ φ (D.nsmul k).idealSheaf (Nat.lcm ι d) := by
    intro W _ _ _ hW ϖ hϖ χ y hy hA' t tK h1 h2 P be hbe hmono
    obtain ⟨a, ha, hI⟩ := hord W hW ϖ hϖ χ y hy hA' t tK h1 h2 P be hbe hmono
    refine ⟨k * a, ?_, ?_⟩
    · rw [hk]; push_cast; rw [ha]; ring
    · rw [GlobalTheory.TorRef.Scale.idlAlong_nsmul, hI, Ideal.span_singleton_pow, ← pow_mul, mul_comm a k]
  have hsub : ∀ y ∈ (D.nsmul k).idealSheaf.support, y ∈ D.idealSheaf.support := by
    intro y hy
    obtain ⟨j, hj⟩ := D.exists_mem y
    rw [(D.nsmul k).mem_support_iff j hj] at hy
    rw [D.mem_support_iff j hj]
    intro h
    apply hy
    change y ∈ Y.Z.basicOpen (D.f j ^ k)
    rw [Scheme.basicOpen_pow _ _ hk0]
    exact h

  obtain ⟨W, hWi, hWc⟩ := GlobalTheory.T.exists_open_compactification_generic_subset_moduli E H Dw l Xo c C
  let U : Y.Z.Opens := (πY ≫ X₁.π) ⁻¹ᵁ W ⊓ ⟨((D.nsmul k).idealSheaf.support : Set Y.Z)ᶜ, (D.nsmul k).idealSheaf.support.isClosed.isOpen_compl⟩
  have hU : (U : Set Y.Z).Nonempty := by
    have e : Y.pt ≫ πY ≫ X₁.π = spMap (AlgHom.id X₁.o₁ X₁.Ω₁).toRingHom ≫ spMap (ratHull X₁.S.R).val.toRingHom ≫ X₁.u ≫ C.i := by
      rw [← Category.assoc, hHom, Category.assoc, X₁.comp]
    have e' := congrArg (fun h : Sp X₁.Ω₁ ⟶ C.Z => h (closedPoint X₁.Ω₁)) e
    simp only [Scheme.Hom.comp_apply] at e'
    have hr : X₁.π (πY (Y.pt (closedPoint X₁.Ω₁))) ∈ Set.range C.i := ⟨_, e'.symm⟩
    refine ⟨Y.pt (closedPoint X₁.Ω₁), ?_, ?_⟩
    · show (πY ≫ X₁.π) _ ∈ (W : Set C.Z)
      rw [Scheme.Hom.comp_apply]
      exact hWi hr
    · intro hs
      exact hsupp _ (hsub _ hs) hr
  have hDU : ∀ x ∈ (D.nsmul k).idealSheaf.support, x ∉ U := fun x hx hxU => hxU.2 hx
  have hrange : ∀ {q : ℕ} [Fact q.Prime] (y : Sp (OO q) ⟶ Y.Z), Set.range (gPt q ≫ y) ⊆ U →
      Set.range (gPt q ≫ y ≫ πY ≫ X₁.π) ⊆ Set.range C.i := by
    intro q _ y hy
    have h := hWc q (y ≫ πY ≫ X₁.π) (by
      rintro _ ⟨w, rfl⟩
      have h1 : (πY ≫ X₁.π) ((gPt q ≫ y) w) ∈ (W : Set C.Z) := (hy ⟨w, rfl⟩).1
      simpa only [Scheme.Hom.comp_apply] using h1)
    simpa only [Category.assoc] using h
  obtain ⟨J, hJ⟩ := GlobalTheory.T.exists_idealSheaf_pullback_eq_divisor_of_approx X₁.o₁ X₁.Ω₁ X₁.M Y πY hHom hprop (@GlobalTheory.IsNormalScheme.pred _ X₁.normal) hnorm U (D.nsmul k) hU hDU (by
    intro z₀ _ x hxz hx
    obtain ⟨p, hp, y₀, hcen⟩ := GlobalTheory.T.exists_classicalPoint_centred_closedPoint_arithmetic _ _ Y x hx U hU
    obtain ⟨c₀, hc₀y, hc₀⟩ := exists_uCTrait_norm_eqAt X₁ Y πY φ (Nat.lcm ι d) (D.nsmul k) hord' p y₀ (hrange y₀ hcen.2) z₀
      (by rw [hcen.1, hxz])
    refine ⟨p, hp, y₀, hcen, fun e => ?_⟩
    obtain ⟨f, hf0, hfall⟩ := hAL p z₀ c₀ e
    have hfO : X₁.M.stalkHom z₀ f ∈ X₁.M.O z₀ := (X₁.M.stalkEquiv z₀ f).2
    refine ⟨X₁.M.stalkHom z₀ f, hfO, fun f' hf' => ?_, ?_⟩
    · rw [hc₀ f' (hcen.1 ▸ hf'), val_comp_of_centre X₁ Y πY hHom y₀ (by rw [hcen.1, hxz]) hfO, ← hf0]
      show _ = ‖X₁.M.val (gPt p ≫ c₀.y) _‖
      rw [hc₀y]
    · intro q hq y hyz hyU f' hf'
      have hpq : p = q := GlobalTheory.T.prime_eq_of_classicalPoint_same_centre X₁.M.Z p q (y₀ ≫ πY) (y ≫ πY) (by
        rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hcen.1, hxz, hyz])
      subst hpq
      obtain ⟨t, hty, ht⟩ := exists_uCTrait_norm_eqAt X₁ Y πY φ (Nat.lcm ι d) (D.nsmul k) hord' p y (hrange y hyU) z₀ hyz
      have hcv : ∀ a, t.val a = Y.val (gPt p ≫ y) (X₁.M.stalkHom z₀ a) := fun a => by
        rw [val_comp_of_centre X₁ Y πY hHom y hyz (a := X₁.M.stalkHom z₀ a) (X₁.M.stalkEquiv z₀ a).2]
        show X₁.M.val (gPt p ≫ t.y) _ = _
        rw [hty]
      rcases hfall t with h1 | ⟨h, hh, h2⟩
      · left
        rw [← hcv, ht f' hf']
        exact h1
      · right
        refine ⟨X₁.M.stalkHom z₀ h, ⟨(X₁.M.stalkEquiv z₀ h).2, ?_⟩, ?_⟩
        · by_contra hne
          push_neg at hne
          apply (IsLocalRing.mem_maximalIdeal _).1 hh
          have hu : IsUnit (X₁.M.stalkEquiv z₀ h) :=
            (RatModel.isUnit_O_iff _).2 ⟨hne.1, hne.2⟩
          exact (MulEquiv.isUnit_map (X₁.M.stalkEquiv z₀)).1 hu
        · rw [← hcv, ← hcv]
          exact h2)
  refine ⟨Nat.lcm ι d, J, hL0, ?_, ?_⟩
  · rw [hJ]
    intro y hy
    exact hsupp y (hsub y hy)
  · rw [hJ]
    exact hord'

end GlobalTheory.UPoinc.DescentPow
