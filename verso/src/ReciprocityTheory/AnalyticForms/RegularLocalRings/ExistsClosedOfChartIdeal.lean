import ReciprocityTheory.AnalyticForms.RegularLocalRings.LiftChartIdeal
import ReciprocityTheory.AnalyticForms.RegularLocalRings.BijOnClosedPointsOfIsIso
import ReciprocityTheory.AnalyticForms.RegularLocalRings.ExistsBasicOpenCover

namespace ReciprocityTheory.AnForm.R

open MvPolynomial AlgebraicGeometry CategoryTheory

noncomputable section

/- English proof (translation)
Rewrite using `[Ne, val_eq_zero_iff s f x hx hc, Scheme.evaluation_eq_zero_iff_notMem_basicOpen, not_not]`.
-/
theorem mem_basicOpen_iff_val_ne {S : Scheme.{0}} (s : S ⟶ Spec (.of ℂ)) [LocallyOfFiniteType s]
    {U : S.Opens} (f : Γ(S, U)) (x : S) (hx : x ∈ U) (hc : IsClosed ({x} : Set S)) :
    x ∈ S.basicOpen f ↔ val s f x hx ≠ 0 := by
  rw [Ne, val_eq_zero_iff s f x hx hc, Scheme.evaluation_eq_zero_iff_notMem_basicOpen, not_not]

section Aff

variable {W : Scheme.{0}} {s : W ⟶ Spec (.of ℂ)}

/- English proof (translation)
Rewrite using `[← P.val_secHom y hy hc g, Ne, val_eq_zero_iff s _ y hy hc, Scheme.evaluation_eq_zero_iff_notMem_basicOpen, not_not]`.
-/
theorem AffPres.mem_basicOpen_iff_eval [LocallyOfFiniteType s] (P : AffPres s)
    (g : MvPolynomial (Fin P.n) ℂ) (y : W) (hy : y ∈ P.V) (hc : IsClosed ({y} : Set W)) :
    y ∈ W.basicOpen (P.secHom g) ↔ eval (P.coord y hy) g ≠ 0 := by
  rw [← P.val_secHom y hy hc g, Ne, val_eq_zero_iff s _ y hy hc,
    Scheme.evaluation_eq_zero_iff_notMem_basicOpen, not_not]

/- English proof (translation)
Set `e : Γ(W, P.V) ≅ CommRingCat.of (MvPolynomial (Fin P.n) ℂ ⧸ P.K)` to `P.V.topIso.symm ≪≫ (Scheme.Γ.mapIso P.iso.op).symm ≪≫ Scheme.ΓSpecIso _`. Conclude with `isNoetherianRing_of_ringEquiv _ e.symm.commRingCatIsoToRingEquiv`.
-/
theorem AffPres.isNoetherianRing (P : AffPres s) : IsNoetherianRing Γ(W, P.V) := by
  let e : Γ(W, P.V) ≅ CommRingCat.of (MvPolynomial (Fin P.n) ℂ ⧸ P.K) :=
    P.V.topIso.symm ≪≫ (Scheme.Γ.mapIso P.iso.op).symm ≪≫ Scheme.ΓSpecIso _
  exact isNoetherianRing_of_ringEquiv _ e.symm.commRingCatIsoToRingEquiv

end Aff

variable {K : Type} [Fintype K] [Nonempty K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)} {hP : IsMultiHomogIdeal P}

/- English proof (translation)
Establish `h : (Ideal.Quotient.mk (chartIdeal P p) (X ⟨k, p k⟩) : chartRing P p) = 1`. Rewrite using `[← map_one (Ideal.Quotient.mk (chartIdeal P p)), Ideal.Quotient.eq]`. Conclude with `Ideal.mem_sup_right (Ideal.subset_span ⟨k, rfl⟩)`. Rewrite using `[chartCoord, h, map_one]`.
-/
theorem chartCoord_self (p : (k : K) → ι k) (k : K) : chartCoord hP p ⟨k, p k⟩ = 1 := by
  have h : (Ideal.Quotient.mk (chartIdeal P p) (X ⟨k, p k⟩) : chartRing P p) = 1 := by
    rw [← map_one (Ideal.Quotient.mk (chartIdeal P p)), Ideal.Quotient.eq]
    exact Ideal.mem_sup_right (Ideal.subset_span ⟨k, rfl⟩)
  rw [chartCoord, h, map_one]

/- English proof (translation)
Take `⟨f, hf⟩` from `Ideal.Quotient.mk_surjective (gammaChart hP p a)`. Use `⟨f, fun y hy hc => ?_⟩` and prove the remaining obligations. Establish `ha : a = eval₂ (constSec (toSpecC hP) (chartOpen hP p).1) (chartCoord hP p) f`. Rewrite using `[← gammaChart_symm_mk, hf, RingEquiv.symm_apply_apply]`. Rewrite using `[ha, val_eval₂ (toSpecC hP) _ f y hy hc]`.
-/
theorem val_chart_eq_eval (p : (k : K) → ι k) (a : Γ(projX P hP, (chartOpen hP p).1)) :
    ∃ f : MvPolynomial (Σ k, ι k) ℂ, ∀ (y : projX P hP) (hy : y ∈ (chartOpen hP p).1),
      IsClosed ({y} : Set (projX P hP)) →
      val (toSpecC hP) a y hy = eval (fun q => val (toSpecC hP) (chartCoord hP p q) y hy) f := by
  obtain ⟨f, hf⟩ := Ideal.Quotient.mk_surjective (gammaChart hP p a)
  refine ⟨f, fun y hy hc => ?_⟩
  have ha : a = eval₂ (constSec (toSpecC hP) (chartOpen hP p).1) (chartCoord hP p) f := by
    rw [← gammaChart_symm_mk, hf, RingEquiv.symm_apply_apply]
  rw [ha, val_eval₂ (toSpecC hP) _ f y hy hc]

/- English proof (translation)
Set `_` to `segreGraded hP`. Set `y₀ : ProjectiveSpectrum (segreGrading P)` to `y`. Establish `hpr : y₀.asHomogeneousIdeal.toIdeal.IsPrime` using `y₀.isPrime`. Establish `hy₀ : segreW P p' ∉ y₀.asHomogeneousIdeal.toIdeal` using `hy`. Establish `hk : ∀ k, val (toSpecC hP) (chartCoord hP p' ⟨k, p k⟩) y hy ≠ 0 ↔ segreW P (chartUpd p' ⟨k, p k⟩) ∉ y₀.asHomogeneousIdeal.toIdeal`.

Introduce `k`. Establish `hcc : chartCoord hP p' ⟨k, p k⟩ = (Proj.awayToSection (segreGrading P) (segreW P p')).hom (awayCoord hP p' ⟨k, p k⟩)` using `by show (Proj.awayToSection (segreGrading P) (segreW P p')).hom (polyToAway hP p' (X _)) = _`. Simplify using `only [polyToAway, coe_eval₂Hom, eval₂_X]`. Rewrite using `[Ne, val_eq_zero_iff (toSpecC hP) _ y hy hc, hcc]`. Conclude with `not_congr (evaluation_awayToSection_eq_zero_iff (segreGrading P) (segreW P p') y hy _)`.

Repeatedly rewrite using `[hk]`. Use `show segreW P p ∉ y₀.asHomogeneousIdeal.toIdeal ↔ _`. Establish `hrel` using `segreW_prod_update P p' p`. Prove the components needed by the constructor for the conclusion. Introduce `hp k hk'`.

Apply `hp` to reduce the goal to its premises. Establish `h2 : (∏ j, segreW P (Function.update p' j (p j))) * segreW P p' ∈ y₀.asHomogeneousIdeal.toIdeal` using `Ideal.mul_mem_right _ _ (Ideal.IsPrime.prod_mem_iff.2 ⟨k, Finset.mem_univ _, hk'⟩)`. Rewrite `h2` using `[hrel]`. Break down `hpr.mem_or_mem h2 with h3 | h3` into its components or cases. Conclude with `h3`.

Conclude with `absurd (hpr.mem_of_pow_mem _ h3) hy₀`. Introduce `hall hp`. Establish `h2 : segreW P p * segreW P p' ^ Fintype.card K ∈ y₀.asHomogeneousIdeal.toIdeal` using `Ideal.mul_mem_right _ _ hp`. Rewrite `h2` using `[← hrel]`. Break down `hpr.mem_or_mem h2 with h3 | h3` into its components or cases.

Take `⟨k, -, hk'⟩` from `Ideal.IsPrime.prod_mem_iff.1 h3`. Conclude with `hall k hk'`. Conclude with `hy₀ h3`.
-/
theorem mem_chartOpen_iff_val (p p' : (k : K) → ι k) (y : projX P hP)
    (hy : y ∈ (chartOpen hP p').1) (hc : IsClosed ({y} : Set (projX P hP))) :
    y ∈ (chartOpen hP p).1 ↔ ∀ k, val (toSpecC hP) (chartCoord hP p' ⟨k, p k⟩) y hy ≠ 0 := by
  let _ := segreGraded hP
  classical
  let y₀ : ProjectiveSpectrum (segreGrading P) := y
  have hpr : y₀.asHomogeneousIdeal.toIdeal.IsPrime := y₀.isPrime
  have hy₀ : segreW P p' ∉ y₀.asHomogeneousIdeal.toIdeal := hy
  have hk : ∀ k, val (toSpecC hP) (chartCoord hP p' ⟨k, p k⟩) y hy ≠ 0 ↔
      segreW P (chartUpd p' ⟨k, p k⟩) ∉ y₀.asHomogeneousIdeal.toIdeal := by
    intro k
    have hcc : chartCoord hP p' ⟨k, p k⟩ =
        (Proj.awayToSection (segreGrading P) (segreW P p')).hom (awayCoord hP p' ⟨k, p k⟩) := by
      show (Proj.awayToSection (segreGrading P) (segreW P p')).hom (polyToAway hP p' (X _)) = _
      simp only [polyToAway, coe_eval₂Hom, eval₂_X]
    rw [Ne, val_eq_zero_iff (toSpecC hP) _ y hy hc, hcc]
    exact not_congr (evaluation_awayToSection_eq_zero_iff (segreGrading P) (segreW P p') y hy _)
  simp_rw [hk]
  show segreW P p ∉ y₀.asHomogeneousIdeal.toIdeal ↔ _
  have hrel := segreW_prod_update P p' p
  constructor
  · intro hp k hk'
    apply hp
    have h2 : (∏ j, segreW P (Function.update p' j (p j))) * segreW P p' ∈
        y₀.asHomogeneousIdeal.toIdeal :=
      Ideal.mul_mem_right _ _ (Ideal.IsPrime.prod_mem_iff.2 ⟨k, Finset.mem_univ _, hk'⟩)
    rw [hrel] at h2
    rcases hpr.mem_or_mem h2 with h3 | h3
    · exact h3
    · exact absurd (hpr.mem_of_pow_mem _ h3) hy₀
  · intro hall hp
    have h2 : segreW P p * segreW P p' ^ Fintype.card K ∈ y₀.asHomogeneousIdeal.toIdeal :=
      Ideal.mul_mem_right _ _ hp
    rw [← hrel] at h2
    rcases hpr.mem_or_mem h2 with h3 | h3
    · obtain ⟨k, -, hk'⟩ := Ideal.IsPrime.prod_mem_iff.1 h3
      exact hall k hk'
    · exact hy₀ h3

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Establish `hU : IsAffineOpen (chartOpen hP p).1` using `(chartOpen hP p).2`. Set `V : (projX P hP).Opens` to `⟨({y'} : Set (projX P hP))ᶜ, hc'.isOpen_compl⟩`. Establish `hyV : y ∈ V` using `by show y ∉ ({y'} : Set (projX P hP))`. Conclude with `fun h' => hne h'`.

Take `⟨a, haV, hya⟩` from `hU.exists_basicOpen_le (⟨y, hyV⟩ : V) hy`. Establish `hy'a : y' ∉ (projX P hP).basicOpen a` using `fun h' => haV h' (Set.mem_singleton y')`. Take `⟨f, hf⟩` from `val_chart_eq_eval p a`. Rewrite `hya` using `[mem_basicOpen_iff_val_ne (toSpecC hP) a y hy hc, hf y hy hc]`. Rewrite `hy'a` using `[mem_basicOpen_iff_val_ne (toSpecC hP) a y' hy' hc', hf y' hy' hc']`.

Establish `he : (fun q => val (toSpecC hP) (chartCoord hP p q) y' hy') = fun q => val (toSpecC hP) (chartCoord hP p q) y hy` using `funext fun q => (h q).symm`. Rewrite `hy'a` using `[he]`. Conclude with `hy'a hya`.
-/
theorem eq_of_val_chartCoord (p : (k : K) → ι k) (y y' : projX P hP) (hy : y ∈ (chartOpen hP p).1)
    (hy' : y' ∈ (chartOpen hP p).1) (hc : IsClosed ({y} : Set (projX P hP)))
    (hc' : IsClosed ({y'} : Set (projX P hP)))
    (h : ∀ q, val (toSpecC hP) (chartCoord hP p q) y hy = val (toSpecC hP) (chartCoord hP p q) y' hy') :
    y = y' := by
  by_contra hne
  have hU : IsAffineOpen (chartOpen hP p).1 := (chartOpen hP p).2
  let V : (projX P hP).Opens := ⟨({y'} : Set (projX P hP))ᶜ, hc'.isOpen_compl⟩
  have hyV : y ∈ V := by
    show y ∉ ({y'} : Set (projX P hP))
    exact fun h' => hne h'
  obtain ⟨a, haV, hya⟩ := hU.exists_basicOpen_le (⟨y, hyV⟩ : V) hy
  have hy'a : y' ∉ (projX P hP).basicOpen a := fun h' => haV h' (Set.mem_singleton y')
  obtain ⟨f, hf⟩ := val_chart_eq_eval p a
  rw [mem_basicOpen_iff_val_ne (toSpecC hP) a y hy hc, hf y hy hc] at hya
  rw [mem_basicOpen_iff_val_ne (toSpecC hP) a y' hy' hc', hf y' hy' hc'] at hy'a
  have he : (fun q => val (toSpecC hP) (chartCoord hP p q) y' hy') =
      fun q => val (toSpecC hP) (chartCoord hP p q) y hy := funext fun q => (h q).symm
  rw [he] at hy'a
  exact hy'a hya

/- English proof (translation)
Establish `hU : IsAffineOpen (chartOpen hP p).1` using `(chartOpen hP p).2`. Set `ψ : chartRing P p →+* ℂ` to `Ideal.Quotient.lift _ (eval z) hz`. Set `χ : Γ(projX P hP, (chartOpen hP p).1) →+* ℂ` to `ψ.comp (gammaChart hP p).toRingHom`. Establish `hχC : ∀ c, χ (constSec (toSpecC hP) (chartOpen hP p).1 c) = c`. Introduce `c`.

Rewrite using `[← gammaChart_symm_C]`. Simplify using `[χ, ψ]`. Establish `hχ : Function.Surjective χ` using `fun c => ⟨_, hχC c⟩`. Establish `hm : (RingHom.ker χ).IsMaximal` using `RingHom.ker_isMaximal_of_surjective χ hχ`. Set `pt : PrimeSpectrum Γ(projX P hP, (chartOpen hP p).1)` to `⟨RingHom.ker χ, hm.isPrime⟩`.

Set `y : projX P hP` to `hU.fromSpec.base pt`. Establish `hy : y ∈ (chartOpen hP p).1`. Establish `h0 : y ∈ Set.range hU.fromSpec` using `⟨pt, rfl⟩`. Rewrite `h0` using `[hU.range_fromSpec]`. Then use the resulting hypothesis. Establish `hb : ∀ a, y ∈ (projX P hP).basicOpen a ↔ a ∉ RingHom.ker χ`.

Introduce `a`. Establish `h1 : pt ∈ hU.fromSpec ⁻¹ᵁ (projX P hP).basicOpen a ↔ y ∈ (projX P hP).basicOpen a` using `Iff.rfl`. Rewrite using `[← h1, hU.fromSpec_preimage_basicOpen]`. Conclude with `PrimeSpectrum.mem_basicOpen _ _`. Establish `hpt : IsClosed ({pt} : Set (PrimeSpectrum Γ(projX P hP, (chartOpen hP p).1)))` using `(PrimeSpectrum.isClosed_singleton_iff_isMaximal _).2 hm`.

Set `hh` to `Scheme.homeoOfIso hU.isoSpec.symm`. Establish `hc0 : IsClosed ({hh pt} : Set (chartOpen hP p).1)`. Use `hh.isClosedMap {pt} hpt` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Conclude with `Set.image_singleton.symm`.

Establish `hval : (hh pt).1 = y` using `by show _ = hU.fromSpec.base pt`. Rewrite using `[← hU.isoSpec_inv_ι]`. Both sides reduce to the same expression. Establish `hc : IsClosed ({y} : Set (projX P hP))`. Use `isClosed_of_isClosed_open (sW := toSpecC hP) _ (hh pt) hc0` as an intermediate fact.

Rewrite `this` using `[hval]`. Then use the resulting hypothesis. Take `⟨φ, hφ⟩` from `val_ringHom (toSpecC hP) (chartOpen hP p).1 y hy hc`. Use `⟨y, hy, hc, fun q => ?_⟩` and prove the remaining obligations. Establish `hmem : chartCoord hP p q - constSec (toSpecC hP) (chartOpen hP p).1 (z q) ∈ RingHom.ker χ`. Rewrite using `[RingHom.mem_ker, map_sub, hχC, sub_eq_zero]`.

Simplify using `[χ, ψ, chartCoord]`. Establish `h0 : val (toSpecC hP) (chartCoord hP p q - constSec (toSpecC hP) (chartOpen hP p).1 (z q)) y hy = 0`. Assume the negation of the conclusion as `hne`. Conclude with `((hb _).1 ((mem_basicOpen_iff_val_ne (toSpecC hP) _ y hy hc).2 hne)) hmem`. Rewrite `h0` using `[← hφ, map_sub, hφ, hφ, val_const (toSpecC hP) _ y hy hc, sub_eq_zero]`.

Conclude with `h0`.
-/
theorem exists_closed_of_chartIdeal (p : (k : K) → ι k) (z : (Σ k, ι k) → ℂ)
    (hz : ∀ h ∈ chartIdeal P p, eval z h = 0) :
    ∃ (y : projX P hP) (hy : y ∈ (chartOpen hP p).1), IsClosed ({y} : Set (projX P hP)) ∧
      ∀ q, val (toSpecC hP) (chartCoord hP p q) y hy = z q := by
  have hU : IsAffineOpen (chartOpen hP p).1 := (chartOpen hP p).2
  let ψ : chartRing P p →+* ℂ := Ideal.Quotient.lift _ (eval z) hz
  let χ : Γ(projX P hP, (chartOpen hP p).1) →+* ℂ := ψ.comp (gammaChart hP p).toRingHom
  have hχC : ∀ c, χ (constSec (toSpecC hP) (chartOpen hP p).1 c) = c := by
    intro c
    rw [← gammaChart_symm_C]
    simp [χ, ψ]
  have hχ : Function.Surjective χ := fun c => ⟨_, hχC c⟩
  have hm : (RingHom.ker χ).IsMaximal := RingHom.ker_isMaximal_of_surjective χ hχ
  let pt : PrimeSpectrum Γ(projX P hP, (chartOpen hP p).1) := ⟨RingHom.ker χ, hm.isPrime⟩
  let y : projX P hP := hU.fromSpec.base pt
  have hy : y ∈ (chartOpen hP p).1 := by
    have h0 : y ∈ Set.range hU.fromSpec := ⟨pt, rfl⟩
    rwa [hU.range_fromSpec] at h0
  have hb : ∀ a, y ∈ (projX P hP).basicOpen a ↔ a ∉ RingHom.ker χ := by
    intro a
    have h1 : pt ∈ hU.fromSpec ⁻¹ᵁ (projX P hP).basicOpen a ↔ y ∈ (projX P hP).basicOpen a := Iff.rfl
    rw [← h1, hU.fromSpec_preimage_basicOpen]
    exact PrimeSpectrum.mem_basicOpen _ _
  have hpt : IsClosed ({pt} : Set (PrimeSpectrum Γ(projX P hP, (chartOpen hP p).1))) :=
    (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).2 hm
  let hh := Scheme.homeoOfIso hU.isoSpec.symm
  have hc0 : IsClosed ({hh pt} : Set (chartOpen hP p).1) := by
    have := hh.isClosedMap {pt} hpt
    convert this using 1
    exact Set.image_singleton.symm
  have hval : (hh pt).1 = y := by
    show _ = hU.fromSpec.base pt
    rw [← hU.isoSpec_inv_ι]
    rfl
  have hc : IsClosed ({y} : Set (projX P hP)) := by
    have := isClosed_of_isClosed_open (sW := toSpecC hP) _ (hh pt) hc0
    rwa [hval] at this
  obtain ⟨φ, hφ⟩ := val_ringHom (toSpecC hP) (chartOpen hP p).1 y hy hc
  refine ⟨y, hy, hc, fun q => ?_⟩
  have hmem : chartCoord hP p q - constSec (toSpecC hP) (chartOpen hP p).1 (z q) ∈ RingHom.ker χ := by
    rw [RingHom.mem_ker, map_sub, hχC, sub_eq_zero]
    simp [χ, ψ, chartCoord]
  have h0 : val (toSpecC hP) (chartCoord hP p q - constSec (toSpecC hP) (chartOpen hP p).1 (z q)) y hy = 0 := by
    by_contra hne
    exact ((hb _).1 ((mem_basicOpen_iff_val_ne (toSpecC hP) _ y hy hc).2 hne)) hmem
  rw [← hφ, map_sub, hφ, hφ, val_const (toSpecC hP) _ y hy hc, sub_eq_zero] at h0
  exact h0

/- English proof (translation)
Establish `h1` using `mem_projB_iff (P := P) (D := D) hP hD p y hy`. Use `(SetLike.mem_coe.trans h1).trans (forall₂_congr fun f _ => ?_)` and prove the remaining obligations. Rewrite using `[← val_eq_zero_iff (toSpecC hP) _ y hy hc, gammaChart_symm_mk, val_eval₂ (toSpecC hP) _ f y hy hc]`.
-/
theorem mem_projB_iff_val (hD : IsMultiHomogIdeal D) (p : (k : K) → ι k) (y : projX P hP)
    (hy : y ∈ (chartOpen hP p).1) (hc : IsClosed ({y} : Set (projX P hP))) :
    y ∈ (projB P D hP : Set (projX P hP)) ↔
      ∀ f ∈ D, eval (fun q => val (toSpecC hP) (chartCoord hP p q) y hy) f = 0 := by
  have h1 := mem_projB_iff (P := P) (D := D) hP hD p y hy
  refine (SetLike.mem_coe.trans h1).trans (forall₂_congr fun f _ => ?_)
  rw [← val_eq_zero_iff (toSpecC hP) _ y hy hc, gammaChart_symm_mk,
    val_eval₂ (toSpecC hP) _ f y hy hc]

/- English proof (translation)
Rewrite using `[mem_conePts_iff_chartIdeal hD p z hz]`. Use `⟨fun h f hf => h f (Ideal.mem_sup_left hf), fun h => ?_⟩` and prove the remaining obligations. Establish `hle : chartIdeal D p ≤ RingHom.ker (eval (affCoord p z))`. Use `sup_le (fun f hf => h f hf) ?_` and prove the remaining obligations. Rewrite using `[Ideal.span_le]`.

Introduce and unpack `_ ⟨k, rfl⟩`. Rewrite using `[SetLike.mem_coe, RingHom.mem_ker, map_sub, MvPolynomial.eval_X, map_one, sub_eq_zero]`. Conclude with `div_self (hz k)`. Conclude with `fun g hg => hle hg`.
-/
theorem mem_conePts_iff_affCoord (hD : IsMultiHomogIdeal D) (p : (k : K) → ι k)
    (z : (Σ k, ι k) → ℂ) (hz : ∀ k, z ⟨k, p k⟩ ≠ 0) :
    z ∈ conePts D ↔ ∀ f ∈ D, eval (affCoord p z) f = 0 := by
  rw [mem_conePts_iff_chartIdeal hD p z hz]
  refine ⟨fun h f hf => h f (Ideal.mem_sup_left hf), fun h => ?_⟩
  have hle : chartIdeal D p ≤ RingHom.ker (eval (affCoord p z)) := by
    refine sup_le (fun f hf => h f hf) ?_
    rw [Ideal.span_le]
    rintro _ ⟨k, rfl⟩
    rw [SetLike.mem_coe, RingHom.mem_ker, map_sub, MvPolynomial.eval_X, map_one, sub_eq_zero]
    exact div_self (hz k)
  exact fun g hg => hle hg

/- English proof (translation)
Take `⟨c, hc, rfl⟩` from `h`. Use `⟨fun k => (c k)⁻¹, fun k => inv_ne_zero (hc k), funext fun q => ?_⟩` and prove the remaining obligations. Rewrite using `[← mul_assoc, inv_mul_cancel₀ (hc q.1), one_mul]`.
-/
theorem sameOrbit_symm' {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') : SameOrbit z' z := by
  obtain ⟨c, hc, rfl⟩ := h
  refine ⟨fun k => (c k)⁻¹, fun k => inv_ne_zero (hc k), funext fun q => ?_⟩
  rw [← mul_assoc, inv_mul_cancel₀ (hc q.1), one_mul]

namespace WData

variable (w : WData P D hP)

instance instLft : LocallyOfFiniteType (w.π ≫ toSpecC hP) := w.lft

/- English proof (translation)
The claim follows from `(val_comp (w.π ≫ toSpecC hP) (toSpecC hP) w.π rfl (w.le_pres c.1 c.2) (chartCoord hP c.1 ⟨Classical.arbitrary K, c.1 (Classical.arbitrary K)⟩) x.1 hx x.2).1`.
-/
theorem isClosed_image (c : w.Idx) (x : w.M) (hx : x ∈ w.src c) :
    IsClosed ({w.π.base x.1} : Set (projX P hP)) :=
  (val_comp (w.π ≫ toSpecC hP) (toSpecC hP) w.π rfl (w.le_pres c.1 c.2)
    (chartCoord hP c.1 ⟨Classical.arbitrary K, c.1 (Classical.arbitrary K)⟩) x.1 hx x.2).1

/- English proof (translation)
Conclude with `w.lift_val c x hx q`.
-/
theorem lift_eval_eq_val (c : w.Idx) (x : w.M) (hx : x ∈ w.src c) (q : Σ k, ι k) :
    eval (w.coord c x) (w.lift c q) =
      val (toSpecC hP) (chartCoord hP c.1 q) (w.π.base x.1) (w.le_pres c.1 c.2 hx) := by
  exact w.lift_val c x hx q

instance instIsNoetherianW : IsNoetherian w.W := by
  have htop : (⨆ c : w.Idx, (w.pres c.1 c.2).affOpen : w.W.Opens) = ⊤ := by
    rw [eq_top_iff]
    rintro x -
    obtain ⟨p, hp⟩ := chartOpen_cover hP (w.π.base x)
    have hx : x ∈ w.π ⁻¹ᵁ (chartOpen hP p).1 := hp
    rw [← w.iSup_pres p] at hx
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨p, i⟩, hi⟩
  exact (isNoetherian_iff_of_finite_iSup_eq_top htop).2 fun c => (w.pres c.1 c.2).isNoetherianRing

def Zb : w.W.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal
    ⟨w.π.base ⁻¹' (projB P D hP : Set (projX P hP)),
      IsClosed.preimage w.π.base.hom.continuous (projB P D hP).2⟩

/- English proof (translation)
The claim follows from `w.snc`.
-/
theorem snc_Zb : FinalTheorems.Snc w.Zb := w.snc

/- English proof (translation)
Simplify using `[Zb]`.
-/
theorem support_Zb : (w.Zb.support : Set w.W) = w.π.base ⁻¹' (projB P D hP : Set (projX P hP)) := by
  simp [Zb]

def bd (c : w.Idx) : Ideal (MvPolynomial (Fin (w.pres c.1 c.2).n) ℂ) :=
  (w.pres c.1 c.2).bdIdeal w.Zb

/- English proof (translation)
The claim follows from `(w.pres c.1 c.2).le_bdIdeal w.Zb`.
-/
theorem le_bd (c : w.Idx) : (w.pres c.1 c.2).K ≤ w.bd c :=
  (w.pres c.1 c.2).le_bdIdeal w.Zb

instance finite_comps : Finite (comps (w.Zb.support : Set w.W)) :=
  (comps_finite _).to_subtype

def rc : ℕ := Nat.card (comps (w.Zb.support : Set w.W))

def compEquiv : Fin w.rc ≃ comps (w.Zb.support : Set w.W) :=
  (Finite.equivFin _).symm

def comp (k : Fin w.rc) : Set w.M := {x | x.1 ∈ ((w.compEquiv k : Set w.W))}

/- English proof (translation)
Establish `key : {x : w.M | x.1 ∈ O} = ⋃ c : w.Idx, ⋃ g ∈ Classical.choose ((w.pres c.1 c.2).exists_basicOpen_cover O), w.src c ∩ w.coord c ⁻¹' {z | eval z g ≠ 0}`. Use extensionality with `x`. Simplify using `only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage, exists_prop]`. Prove the components needed by the constructor for the conclusion. Introduce `hxO`.

Take `⟨c, hc⟩` from `w.cover x`. Take `⟨g, hg, hxg⟩` from `(Classical.choose_spec ((w.pres c.1 c.2).exists_basicOpen_cover O) x.1 hc).1 hxO`. Use `⟨c, g, hg, hc, ?_⟩` and prove the remaining obligations. Rewrite using `[w.coord_of_mem c x hc]`. Conclude with `((w.pres c.1 c.2).mem_basicOpen_iff_eval g x.1 hc x.2).1 hxg`.

Introduce and unpack `⟨c, g, hg, hc, hne⟩`. Rewrite `hne` using `[w.coord_of_mem c x hc]`. Conclude with `(Classical.choose_spec ((w.pres c.1 c.2).exists_basicOpen_cover O) x.1 hc).2 ⟨g, hg, ((w.pres c.1 c.2).mem_basicOpen_iff_eval g x.1 hc x.2).2 hne⟩`. Rewrite using `[key]`. Use `isOpen_iUnion fun c => isOpen_iUnion fun g => isOpen_iUnion fun _ => ?_` and prove the remaining obligations.

Conclude with `TopologicalSpace.isOpen_generateFrom_of_mem ⟨c, {z | eval z g ≠ 0}, isOpen_ne_fun (MvPolynomial.continuous_eval g) continuous_const, rfl⟩`.
-/
theorem isOpen_zariski (O : w.W.Opens) : IsOpen {x : w.M | x.1 ∈ O} := by
  have key : {x : w.M | x.1 ∈ O} = ⋃ c : w.Idx, ⋃ g ∈ Classical.choose
      ((w.pres c.1 c.2).exists_basicOpen_cover O),
      w.src c ∩ w.coord c ⁻¹' {z | eval z g ≠ 0} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage, exists_prop]
    constructor
    · intro hxO
      obtain ⟨c, hc⟩ := w.cover x
      obtain ⟨g, hg, hxg⟩ := (Classical.choose_spec
        ((w.pres c.1 c.2).exists_basicOpen_cover O) x.1 hc).1 hxO
      refine ⟨c, g, hg, hc, ?_⟩
      rw [w.coord_of_mem c x hc]
      exact ((w.pres c.1 c.2).mem_basicOpen_iff_eval g x.1 hc x.2).1 hxg
    · rintro ⟨c, g, hg, hc, hne⟩
      rw [w.coord_of_mem c x hc] at hne
      exact (Classical.choose_spec ((w.pres c.1 c.2).exists_basicOpen_cover O) x.1 hc).2
        ⟨g, hg, ((w.pres c.1 c.2).mem_basicOpen_iff_eval g x.1 hc x.2).2 hne⟩
  rw [key]
  refine isOpen_iUnion fun c => isOpen_iUnion fun g => isOpen_iUnion fun _ => ?_
  exact TopologicalSpace.isOpen_generateFrom_of_mem
    ⟨c, {z | eval z g ≠ 0}, isOpen_ne_fun (MvPolynomial.continuous_eval g) continuous_const, rfl⟩

/- English proof (translation)
Rewrite using `[mem_chartOpen_iff_val p c.1 (w.π.base x.1) (w.le_pres c.1 c.2 hx) (w.isClosed_image c x hx)]`. Simplify using `only [w.lift_eval_eq_val c x hx]`.
-/
theorem mem_chartOpen_iff (c : w.Idx) (x : w.M) (hx : x ∈ w.src c) (p : (k : K) → ι k) :
    w.π.base x.1 ∈ (chartOpen hP p).1 ↔ ∀ k, eval (w.coord c x) (w.lift c ⟨k, p k⟩) ≠ 0 := by
  rw [mem_chartOpen_iff_val p c.1 (w.π.base x.1) (w.le_pres c.1 c.2 hx) (w.isClosed_image c x hx)]
  simp only [w.lift_eval_eq_val c x hx]

/- English proof (translation)
Establish `hxc : w.π.base x.1 ∈ (chartOpen hP c.1).1` using `w.le_pres c.1 c.2 hx`. Establish `hcl` using `w.isClosed_image c x hx`. Establish `hboth : w.π.base x.1 ∈ (chartOpen hP p).1 ⊓ (chartOpen hP c.1).1` using `⟨hp, hxc⟩`. Take `⟨φ, hφ⟩` from `val_ringHom (toSpecC hP) _ (w.π.base x.1) hboth hcl`. Establish `h` using `congrArg φ (chartCoord_overlap hP p c.1 q)`.

Rewrite `h` using `[map_mul, hφ, hφ, hφ, val_restrict, val_restrict, val_restrict]`. Rewrite `h` using `[← w.lift_eval_eq_val c x hx, ← w.lift_eval_eq_val c x hx]`. Establish `hne : eval (w.coord c x) (w.lift c ⟨q.1, p q.1⟩) ≠ 0` using `(w.mem_chartOpen_iff c x hx p).1 hp q.1`. Rewrite using `[affCoord]`. Conclude with `eq_div_of_mul_eq hne h`.
-/
theorem val_chartCoord (c : w.Idx) (x : w.M) (hx : x ∈ w.src c) (p : (k : K) → ι k)
    (hp : w.π.base x.1 ∈ (chartOpen hP p).1) (q : Σ k, ι k) :
    val (toSpecC hP) (chartCoord hP p q) (w.π.base x.1) hp =
      affCoord p (fun q => eval (w.coord c x) (w.lift c q)) q := by
  have hxc : w.π.base x.1 ∈ (chartOpen hP c.1).1 := w.le_pres c.1 c.2 hx
  have hcl := w.isClosed_image c x hx
  have hboth : w.π.base x.1 ∈ (chartOpen hP p).1 ⊓ (chartOpen hP c.1).1 := ⟨hp, hxc⟩
  obtain ⟨φ, hφ⟩ := val_ringHom (toSpecC hP) _ (w.π.base x.1) hboth hcl
  have h := congrArg φ (chartCoord_overlap hP p c.1 q)
  rw [map_mul, hφ, hφ, hφ, val_restrict, val_restrict, val_restrict] at h
  rw [← w.lift_eval_eq_val c x hx, ← w.lift_eval_eq_val c x hx] at h
  have hne : eval (w.coord c x) (w.lift c ⟨q.1, p q.1⟩) ≠ 0 :=
    (w.mem_chartOpen_iff c x hx p).1 hp q.1
  rw [affCoord]
  exact eq_div_of_mul_eq hne h

/- English proof (translation)
Establish `hxc : w.π.base x.1 ∈ (chartOpen hP c.1).1` using `w.le_pres c.1 c.2 hx`. Establish `hv : (fun q => val (toSpecC hP) (chartCoord hP c.1 q) (w.π.base x.1) hxc) = fun q => eval (w.coord c x) (w.lift c q)`. Use function extensionality and compare the values at `fun q => (w.lift_eval_eq_val c x hx q).symm`. Rewrite using `[mem_projB_iff_val hD c.1 _ hxc (w.isClosed_image c x hx), hv]`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Use `⟨fun k => ⟨c.1 k, ?_⟩, h⟩` and prove the remaining obligations. Simplify using `[lift]`. Conclude with `fun h => h.2`.
-/
theorem mem_projB_iff_lift (hD : IsMultiHomogIdeal D) (c : w.Idx) (x : w.M) (hx : x ∈ w.src c) :
    w.π.base x.1 ∈ (projB P D hP : Set (projX P hP)) ↔
      (fun q => eval (w.coord c x) (w.lift c q)) ∈ conePts D := by
  have hxc : w.π.base x.1 ∈ (chartOpen hP c.1).1 := w.le_pres c.1 c.2 hx
  have hv : (fun q => val (toSpecC hP) (chartCoord hP c.1 q) (w.π.base x.1) hxc) =
      fun q => eval (w.coord c x) (w.lift c q) :=
    funext fun q => (w.lift_eval_eq_val c x hx q).symm
  rw [mem_projB_iff_val hD c.1 _ hxc (w.isClosed_image c x hx), hv]
  constructor
  · intro h
    refine ⟨fun k => ⟨c.1 k, ?_⟩, h⟩
    simp [lift]
  · exact fun h => h.2

end WData

end

end ReciprocityTheory.AnForm.R
