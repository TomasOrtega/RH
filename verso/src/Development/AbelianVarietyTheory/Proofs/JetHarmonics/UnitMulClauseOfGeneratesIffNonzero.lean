import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ThetaGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.ThetaSectionsClosedFibre
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsGeneratorOfBasis
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExpansionIntegralSectionIntegralNoetherianLocal
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsSmulMemSpanOfExpandsAt
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsPrincipalIdealRingOfIsLocalization
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsSemiAbelianOfUniformisationOverDvr

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.ThetaCompare

open GlobalTheory.FieldBaseChange GlobalTheory.ConstFam GlobalTheory.IndivisibleSection GlobalTheory.IndefiniteRowSideFullHecke.ThetaSectionsClosedFibre

section Module

variable {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]

/- English proof (translation)
Take `⟨u, rfl⟩` from `hu`. Introduce `s`. Take `⟨c, hc, hcu⟩` from `hb s`. Use `⟨c * u⁻¹.val, by simp only [h, smul_smul, Units.inv_mul_cancel_right]; exact hc, fun c' hc' => ?_⟩` and prove the remaining obligations. Rewrite using `[← hcu (c' * u.val) (show s = _ by rw [mul_smul, ← h]; exact hc'), Units.mul_inv_cancel_right]`.
-/
theorem existsUnique_of_isUnit {b g : M} (hb : ∀ s, ∃! a : R, s = a • b) {a : R} (hu : IsUnit a) (h : g = a • b) :
    ∀ s, ∃! c : R, s = c • g := by
  obtain ⟨u, rfl⟩ := hu
  intro s
  obtain ⟨c, hc, hcu⟩ := hb s
  refine ⟨c * u⁻¹.val, by simp only [h, smul_smul, Units.inv_mul_cancel_right]; exact hc, fun c' hc' => ?_⟩
  rw [← hcu (c' * u.val) (show s = _ by rw [mul_smul, ← h]; exact hc'), Units.mul_inv_cancel_right]

/- English proof (translation)
Take `⟨a, ha, -⟩` from `hb g`. Take `⟨c, hc⟩` from `hg b`. Establish `h : c * a = 1` using `(hb b).unique (by rw [mul_smul, ← ha]; exact hc) (one_smul R b).symm`. Conclude with `existsUnique_of_isUnit hb (IsUnit.of_mul_eq_one c (by rw [mul_comm, h])) ha`.
-/
theorem existsUnique_of_exists {b g : M} (hb : ∀ s, ∃! a : R, s = a • b) (hg : ∀ s, ∃ a : R, s = a • g) :
    ∀ s, ∃! c : R, s = c • g := by
  obtain ⟨a, ha, -⟩ := hb g
  obtain ⟨c, hc⟩ := hg b
  have h : c * a = 1 := (hb b).unique (by rw [mul_smul, ← ha]; exact hc) (one_smul R b).symm
  exact existsUnique_of_isUnit hb (IsUnit.of_mul_eq_one c (by rw [mul_comm, h])) ha

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hg`. Take `⟨a, ha⟩` from `ht g`. Take `⟨c, hc⟩` from `hg t`. Break down `isUnit_or_isUnit_one_sub_self (c * a) with h | h` into its components or cases.

Take `⟨u, rfl⟩` from `isUnit_of_mul_isUnit_right h`. Conclude with `⟨u, ha⟩`. Establish `h₀ : t = 0`. Use `(h.smul_eq_zero).1 ?_` and prove the remaining obligations. Rewrite using `[sub_smul, one_smul, mul_smul, ← ha, ← hc, sub_self]`.

Conclude with `⟨1, by rw [ha, h₀, smul_zero, smul_zero]⟩`. Introduce and unpack `⟨u, rfl⟩ s`. Take `⟨a, ha⟩` from `ht s`. Conclude with `⟨a * u⁻¹.val, by rw [smul_smul, Units.inv_mul_cancel_right]; exact ha⟩`.
-/
theorem generates_iff_unit_smul [IsLocalRing R] {t : M} (ht : ∀ s, ∃ a : R, s = a • t) (g : M) :
    (∀ s, ∃ a : R, s = a • g) ↔ ∃ u : Rˣ, g = (u : R) • t := by
  constructor
  · intro hg
    obtain ⟨a, ha⟩ := ht g
    obtain ⟨c, hc⟩ := hg t
    rcases isUnit_or_isUnit_one_sub_self (c * a) with h | h
    · obtain ⟨u, rfl⟩ := isUnit_of_mul_isUnit_right h
      exact ⟨u, ha⟩
    · have h₀ : t = 0 := by
        refine (h.smul_eq_zero).1 ?_
        rw [sub_smul, one_smul, mul_smul, ← ha, ← hc, sub_self]
      exact ⟨1, by rw [ha, h₀, smul_zero, smul_zero]⟩
  · rintro ⟨u, rfl⟩ s
    obtain ⟨a, ha⟩ := ht s
    exact ⟨a * u⁻¹.val, by rw [smul_smul, Units.inv_mul_cancel_right]; exact ha⟩

end Module

section General

variable {R : Type} [CommRing R] {Y : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of R)) {N : LB Y}

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun h => SecOver.ext _ _ h, fun h _ => by rw [h]; rfl⟩`.
-/
theorem secIsMul_iff (a : R) (s t : SecOver p N) : SecIsMul p a s t ↔ s = a • t :=
  ⟨fun h => SecOver.ext _ _ h, fun h _ => by rw [h]; rfl⟩

/- English proof (translation)
The claim follows from `forall_congr' fun s => exists_congr fun a => secIsMul_iff p a s g`.
-/
theorem generates_iff_smul (g : SecOver p N) : Generates p g ↔ ∀ s : SecOver p N, ∃ a : R, s = a • g :=
  forall_congr' fun s => exists_congr fun a => secIsMul_iff p a s g

end General

section Points

/- English proof (translation)
Rewrite using `[gs_stalkMap r z U h, isUnit_map_iff]`.
-/
theorem isUnit_gs_iff {X Z : Scheme.{0}} (r : Z ⟶ X) (z : Z) (U : X.Opens) (h : r z ∈ U) (f : Γ(X, U)) :
    IsUnit (gs r z U f) ↔ IsUnit (gs (𝟙 X) (r z) U f) := by
  rw [gs_stalkMap r z U h, isUnit_map_iff]

/- English proof (translation)
Take `⟨j, hj, hu⟩` from `(Geo.Tor.mem_nonzeroLocus s _).1 h`. Rewrite using `[sval, sec_trans s r z (hJ.mem φ r) hj]`. Conclude with `(Units.isUnit _).mul ((isUnit_gs_iff r z _ hj _).2 hu)`.
-/
theorem isUnit_sval {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (s : LB.Sec (LB.LinComb L φ ε)) (r : Z ⟶ Y) (z : Z) (h : r z ∈ nonzeroLocus s) {J} (hJ : Good L z J) :
    IsUnit (sval s r z J) := by
  obtain ⟨j, hj, hu⟩ := (Geo.Tor.mem_nonzeroLocus s _).1 h
  rw [sval, sec_trans s r z (hJ.mem φ r) hj]
  exact (Units.isUnit _).mul ((isUnit_gs_iff r z _ hj _).2 hu)

/- English proof (translation)
Take `⟨U, hU, b, hb⟩` from `hS (Spec (CommRingCat.of R)) D.P 1 le_rfl (closedPoint R)`. Take `rfl : U = ⊤` from `eq_top_of_closedPoint_mem U hU`. Set `t : Spec (CommRingCat.of (ResidueField R)) ⟶ (overRes (T` to `baseOver (Spec (CommRingCat.of R))) ⊤).left := spMap (residue R) ≫ (Spec (CommRingCat.of R)).topIso.inv`. Establish `ht : t ≫ (overRes (T` using `baseOver (Spec (CommRingCat.of R))) ⊤).hom = spMap (residue R) := by show (spMap (residue R) ≫ (Spec (CommRingCat.of R)).topIso.inv) ≫ (Scheme.Opens.ι ⊤ ≫ 𝟙 _) = _`. Rewrite using `[Category.comp_id, Category.assoc]`.

Conclude with `(congrArg (spMap (residue R) ≫ ·) (Spec (CommRingCat.of R)).topIso.inv_hom_id).trans (Category.comp_id _)`. Establish `pull : ∀ i, ∃ b' : LB.Sec (LPow D.P.A D.P.L (1 : ℕ) (baseAt t)), IsPullSec D.P.A D.P.L (1 : ℕ) (homAt t ▷ D.P.A) (whiskerRight_snd (homAt t) D.P.A) (b i) b'` using `fun i => by`. Take `⟨s', hs'⟩` from `exists_pull_chart (K := Fin 1) (b i) (homAt t ▷ D.P.A).left (fun _ => (snd (baseAt t) D.P.A).left) (fun _ => congrArg CommaMorphism.left (whiskerRight_snd (homAt t) D.P.A))`. Conclude with `⟨s', fun j => hs' j _⟩`. Use `choose b' hb' using pull`.

Take `⟨hli, -⟩` from `hb _ t b' hb'`. Establish `hq : Unique (Fin (1 ^ D.P.g))` using `by rw [one_pow]; infer_instance`. Establish `hnt : Nontrivial Γ((baseAt t).left, ⊤)` using `(Scheme.ΓSpecIso (CommRingCat.of (ResidueField R))).commRingCatIsoToRingEquiv.toEquiv.nontrivial`. Establish `hne` using `hli.ne_zero hq.default`. Choose the witnesses or unpack the hypotheses as in `⟨j, hj⟩ : ∃ j, (b' hq.default).f j ≠ 0 := by`.

Assume the negation of the conclusion as `h`. Use `push Not at h`. Conclude with `hne (Subtype.ext (funext h))`. Use `D.P.isAb.smooth` as an intermediate fact. Establish `: IsReduced (baseAt t).left` using `inferInstanceAs (IsReduced (Spec (CommRingCat.of (ResidueField R))))`.

Establish `hr : IsReduced (baseAt t ⊗ D.P.A).left` using `GlobalTheory.isReduced_of_smooth_of_isReduced (pullback.fst (baseAt t).hom D.P.A.hom)`. Choose the witnesses or unpack the hypotheses as in `⟨y, hy⟩ : ∃ y, y ∈ (baseAt t ⊗ D.P.A).left.basicOpen ((b' hq.default).f j) := by`. Assume the negation of the conclusion as `h`. Use `push Not at h`. Conclude with `hj ((basicOpen_eq_bot_iff _).1 (eq_bot_iff.2 fun y hy => (h y hy).elim))`.

Set `W` to `overRes (T := baseOver (Spec (CommRingCat.of R))) ⊤`. Set `u : D.P.A ⟶ W` to `Over.homMk (D.P.A.hom ≫ (Spec (CommRingCat.of R)).topIso.inv) (by show (_ ≫ (Spec (CommRingCat.of R)).topIso.inv) ≫ (Scheme.Opens.ι ⊤ ≫ 𝟙 _) = _`. Rewrite using `[Category.comp_id, Category.assoc]`. Conclude with `(congrArg (D.P.A.hom ≫ ·) (Spec (CommRingCat.of R)).topIso.inv_hom_id).trans (Category.comp_id _))`. Establish `hmono : Mono W.hom` using `by show Mono (Scheme.Opens.ι ⊤ ≫ 𝟙 _) infer_instance`.

Establish `hu : snd (baseAt t) D.P.A ≫ lift u (𝟙 D.P.A) = homAt t ▷ D.P.A`. Use `CartesianMonoidalCategory.hom_ext _ _ ?_ ?_` and prove the remaining obligations. Use `Over.OverMorphism.ext ((cancel_mono W.hom).1 ?_)` and prove the remaining obligations. Rewrite using `[Over.w, Over.w]`. Rewrite using `[Category.assoc, lift_snd, Category.comp_id]`.

Conclude with `(whiskerRight_snd (homAt t) D.P.A).symm`. Take `⟨th, hth⟩` from `exists_pull_val D.P.isLB (b hq.default) (lift u (𝟙 D.P.A)).left (φ' := D.famφB 0) (ε' := DegPre.famε 1) (fun U _ h => by`. Rewrite using `[prod_fam_zero]`. Establish `e : (lift u (𝟙 D.P.A)).left ≫ (snd W D.P.A).left = 𝟙 _` using `congrArg CommaMorphism.left (lift_snd u (𝟙 D.P.A))`. Simplify using `only [Fin.prod_univ_one]`.

Use `erw [e]`. Use the proof step `simp)`. Use `⟨th, (snd (baseAt t) D.P.A).left y, ?_, ?_⟩` and prove the remaining obligations. Establish `e : (snd (baseAt t) D.P.A).left ≫ D.P.A.hom = (fst (baseAt t) D.P.A).left ≫ spMap (residue R)`. Rewrite using `[Over.w, ← ht]`.

Conclude with `(Over.w (fst (baseAt t) D.P.A)).symm`. Use `(congrArg (fun q => q y) e).trans ?_` and prove the remaining obligations. Conclude with `PrimeSpectrum.comap_residue R _`. Take `⟨J, hJ⟩` from `exists_good' D.P.isLB y`. Establish `h₁` using `hth _ (snd (baseAt t) D.P.A).left y J hJ`.

Establish `e : (snd (baseAt t) D.P.A).left ≫ (lift u (𝟙 D.P.A)).left = (homAt t ▷ D.P.A).left` using `congrArg CommaMorphism.left hu`. Rewrite `h₁` using `[e]`. Establish `hm : (homAt t ▷ D.P.A).left y ∈ nonzeroLocus (b hq.default)`. Rewrite `hy` using `[hb' hq.default j, Scheme.basicOpen_res, ← Scheme.preimage_basicOpen]`. Conclude with `TopologicalSpace.Opens.mem_iSup.2 ⟨j, hy.2⟩`.

Establish `hu'` using `isUnit_sval (b hq.default) _ y hm hJ`. Rewrite `hu'` using `[← h₁]`. Conclude with `(Geo.Tor.mem_nonzeroLocus th _).2 ⟨_, hJ.mem _ _, (isUnit_gs_iff _ y _ (hJ.mem _ _) _).1 hu'⟩`.
-/
theorem exists_nonzero_closed (hS : SecBaseChangeSt) {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]
    [IsNoetherianRing R] (D : DegPre R) :
    ∃ th : D.SecB 1 0, ∃ x, D.P.A.hom x = closedPoint R ∧ x ∈ nonzeroLocus th := by
  obtain ⟨U, hU, b, hb⟩ := hS (Spec (CommRingCat.of R)) D.P 1 le_rfl (closedPoint R)
  obtain rfl : U = ⊤ := eq_top_of_closedPoint_mem U hU
  let t : Spec (CommRingCat.of (ResidueField R)) ⟶ (overRes (T := baseOver (Spec (CommRingCat.of R))) ⊤).left :=
    spMap (residue R) ≫ (Spec (CommRingCat.of R)).topIso.inv
  have ht : t ≫ (overRes (T := baseOver (Spec (CommRingCat.of R))) ⊤).hom = spMap (residue R) := by
    show (spMap (residue R) ≫ (Spec (CommRingCat.of R)).topIso.inv) ≫ (Scheme.Opens.ι ⊤ ≫ 𝟙 _) = _
    rw [Category.comp_id, Category.assoc]
    exact (congrArg (spMap (residue R) ≫ ·) (Spec (CommRingCat.of R)).topIso.inv_hom_id).trans (Category.comp_id _)
  have pull : ∀ i, ∃ b' : LB.Sec (LPow D.P.A D.P.L (1 : ℕ) (baseAt t)),
      IsPullSec D.P.A D.P.L (1 : ℕ) (homAt t ▷ D.P.A) (whiskerRight_snd (homAt t) D.P.A) (b i) b' := fun i => by
    obtain ⟨s', hs'⟩ := exists_pull_chart (K := Fin 1) (b i) (homAt t ▷ D.P.A).left
      (fun _ => (snd (baseAt t) D.P.A).left)
      (fun _ => congrArg CommaMorphism.left (whiskerRight_snd (homAt t) D.P.A))
    exact ⟨s', fun j => hs' j _⟩
  choose b' hb' using pull
  obtain ⟨hli, -⟩ := hb _ t b' hb'
  have hq : Unique (Fin (1 ^ D.P.g)) := by rw [one_pow]; infer_instance
  have hnt : Nontrivial Γ((baseAt t).left, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of (ResidueField R))).commRingCatIsoToRingEquiv.toEquiv.nontrivial
  have hne := hli.ne_zero hq.default
  obtain ⟨j, hj⟩ : ∃ j, (b' hq.default).f j ≠ 0 := by
    by_contra h
    push Not at h
    exact hne (Subtype.ext (funext h))
  have := D.P.isAb.smooth
  have : IsReduced (baseAt t).left := inferInstanceAs (IsReduced (Spec (CommRingCat.of (ResidueField R))))
  have hr : IsReduced (baseAt t ⊗ D.P.A).left :=
    GlobalTheory.isReduced_of_smooth_of_isReduced (pullback.fst (baseAt t).hom D.P.A.hom)
  obtain ⟨y, hy⟩ : ∃ y, y ∈ (baseAt t ⊗ D.P.A).left.basicOpen ((b' hq.default).f j) := by
    by_contra h
    push Not at h
    exact hj ((basicOpen_eq_bot_iff _).1 (eq_bot_iff.2 fun y hy => (h y hy).elim))
  let W := overRes (T := baseOver (Spec (CommRingCat.of R))) ⊤
  let u : D.P.A ⟶ W := Over.homMk (D.P.A.hom ≫ (Spec (CommRingCat.of R)).topIso.inv) (by
    show (_ ≫ (Spec (CommRingCat.of R)).topIso.inv) ≫ (Scheme.Opens.ι ⊤ ≫ 𝟙 _) = _
    rw [Category.comp_id, Category.assoc]
    exact (congrArg (D.P.A.hom ≫ ·) (Spec (CommRingCat.of R)).topIso.inv_hom_id).trans (Category.comp_id _))
  have hmono : Mono W.hom := by
    show Mono (Scheme.Opens.ι ⊤ ≫ 𝟙 _)
    infer_instance
  have hu : snd (baseAt t) D.P.A ≫ lift u (𝟙 D.P.A) = homAt t ▷ D.P.A := by
    refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
    · refine Over.OverMorphism.ext ((cancel_mono W.hom).1 ?_)
      rw [Over.w, Over.w]
    · rw [Category.assoc, lift_snd, Category.comp_id]; exact (whiskerRight_snd (homAt t) D.P.A).symm
  obtain ⟨th, hth⟩ := exists_pull_val D.P.isLB (b hq.default) (lift u (𝟙 D.P.A)).left (φ' := D.famφB 0)
    (ε' := DegPre.famε 1) (fun U _ h => by
      rw [prod_fam_zero]
      have e : (lift u (𝟙 D.P.A)).left ≫ (snd W D.P.A).left = 𝟙 _ := congrArg CommaMorphism.left (lift_snd u (𝟙 D.P.A))
      simp only [Fin.prod_univ_one]
      erw [e]
      simp)
  refine ⟨th, (snd (baseAt t) D.P.A).left y, ?_, ?_⟩
  · have e : (snd (baseAt t) D.P.A).left ≫ D.P.A.hom = (fst (baseAt t) D.P.A).left ≫ spMap (residue R) := by
      rw [Over.w, ← ht]; exact (Over.w (fst (baseAt t) D.P.A)).symm
    refine (congrArg (fun q => q y) e).trans ?_
    exact PrimeSpectrum.comap_residue R _
  · obtain ⟨J, hJ⟩ := exists_good' D.P.isLB y
    have h₁ := hth _ (snd (baseAt t) D.P.A).left y J hJ
    have e : (snd (baseAt t) D.P.A).left ≫ (lift u (𝟙 D.P.A)).left = (homAt t ▷ D.P.A).left :=
      congrArg CommaMorphism.left hu
    rw [e] at h₁
    have hm : (homAt t ▷ D.P.A).left y ∈ nonzeroLocus (b hq.default) := by
      rw [hb' hq.default j, Scheme.basicOpen_res, ← Scheme.preimage_basicOpen] at hy
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨j, hy.2⟩
    have hu' := isUnit_sval (b hq.default) _ y hm hJ
    rw [← h₁] at hu'
    exact (Geo.Tor.mem_nonzeroLocus th _).2 ⟨_, hJ.mem _ _, (isUnit_gs_iff _ y _ (hJ.mem _ _) _).1 hu'⟩

end Points

section Generators

variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)

abbrev Corr (th : H0 D.P.L 1) (g : D.SecB 1 0) : Prop :=
  GeneratorPullback.SecScal D.P.L (fun _ : Fin 1 => 𝟙 D.P.A.left) (fun _ => ((1 : ℕ) : ℤ)) th
    (D.famφB 0) (DegPre.famε 1) g (𝟙 D.P.A.left) 1

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun h y J hJ => by rw [H1.sval_scal h _ y hJ, Category.id_comp], fun h => SectionScalarValuation.secScal_of_sval D.P.isLB fun y J hJ => by rw [Category.id_comp]; exact h y J hJ⟩`.
-/
theorem corr_iff (th : H0 D.P.L 1) (g : D.SecB 1 0) :
    Corr D th g ↔ ∀ y J, Good D.P.L y J → sval g (𝟙 _) y J = sval th (𝟙 _) y J :=
  ⟨fun h y J hJ => by rw [H1.sval_scal h _ y hJ, Category.id_comp],
    fun h => SectionScalarValuation.secScal_of_sval D.P.isLB fun y J hJ => by rw [Category.id_comp]; exact h y J hJ⟩

/- English proof (translation)
Take `⟨th, h⟩` from `exists_pull_val D.P.isLB g (𝟙 _) (φ' := fun _ : Fin 1 => 𝟙 D.P.A.left) (ε' := fun _ => ((1 : ℕ) : ℤ)) (fun U _ h => by`. Rewrite using `[prod_fam_zero D (fun ψ => h (𝟙 _ ≫ ψ))]`. Use the proof step `simp)`. Conclude with `⟨th, (corr_iff D th g).2 fun y J hJ => by rw [h _ _ y J hJ, Category.id_comp]⟩`.
-/
theorem exists_corr_left (g : D.SecB 1 0) : ∃ th, Corr D th g := by
  obtain ⟨th, h⟩ := exists_pull_val D.P.isLB g (𝟙 _) (φ' := fun _ : Fin 1 => 𝟙 D.P.A.left)
    (ε' := fun _ => ((1 : ℕ) : ℤ)) (fun U _ h => by
      rw [prod_fam_zero D (fun ψ => h (𝟙 _ ≫ ψ))]; simp)
  exact ⟨th, (corr_iff D th g).2 fun y J hJ => by rw [h _ _ y J hJ, Category.id_comp]⟩

/- English proof (translation)
Take `⟨g, h⟩` from `exists_pull_val D.P.isLB th (𝟙 _) (φ' := D.famφB 0) (ε' := DegPre.famε 1) (fun U _ h => by`. Rewrite using `[prod_fam_zero]`. Use the proof step `simp)`. Conclude with `⟨g, (corr_iff D th g).2 fun y J hJ => by rw [h _ _ y J hJ, Category.id_comp]⟩`.
-/
theorem exists_corr_right (th : H0 D.P.L 1) : ∃ g, Corr D th g := by
  obtain ⟨g, h⟩ := exists_pull_val D.P.isLB th (𝟙 _) (φ' := D.famφB 0) (ε' := DegPre.famε 1) (fun U _ h => by
    rw [prod_fam_zero]; simp)
  exact ⟨g, (corr_iff D th g).2 fun y J hJ => by rw [h _ _ y J hJ, Category.id_comp]⟩

variable {D}

/- English proof (translation)
Rewrite `h`, `h'` using `[corr_iff]`. Apply the tactic sequence `constructor <;> intro H <;> refine secIsMul_of_sval D.P.isLB fun y J hJ => ?_`. Rewrite using `[h y J hJ, h' y J hJ, sval_of_secIsMul H _ y hJ, Category.id_comp]`. Rewrite using `[← h y J hJ, ← h' y J hJ, sval_of_secIsMul H _ y hJ, Category.id_comp]`.
-/
theorem Corr.secIsMul_iff {th th' : H0 D.P.L 1} {g g' : D.SecB 1 0} (h : Corr D th g) (h' : Corr D th' g') (a : R) :
    SecIsMul D.P.A.hom a th' th ↔ SecIsMul D.P.A.hom a g' g := by
  rw [corr_iff] at h h'
  constructor <;> intro H <;> refine secIsMul_of_sval D.P.isLB fun y J hJ => ?_
  · rw [h y J hJ, h' y J hJ, sval_of_secIsMul H _ y hJ, Category.id_comp]
  · rw [← h y J hJ, ← h' y J hJ, sval_of_secIsMul H _ y hJ, Category.id_comp]

/- English proof (translation)
Apply the tactic sequence `constructor <;> intro H s`. Take `⟨t, ht⟩` from `exists_corr_left D s`. Conclude with `(H t).imp fun a => (h.secIsMul_iff ht a).1`. Take `⟨t, ht⟩` from `exists_corr_right D s`. Conclude with `(H t).imp fun a => (h.secIsMul_iff ht a).2`.
-/
theorem Corr.generates_iff {th : H0 D.P.L 1} {g : D.SecB 1 0} (h : Corr D th g) :
    Generates D.P.A.hom th ↔ Generates D.P.A.hom g := by
  constructor <;> intro H s
  · obtain ⟨t, ht⟩ := exists_corr_left D s
    exact (H t).imp fun a => (h.secIsMul_iff ht a).1
  · obtain ⟨t, ht⟩ := exists_corr_right D s
    exact (H t).imp fun a => (h.secIsMul_iff ht a).2

end Generators

section Notions

variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
  [IsCommMonObj G]

omit [IsLocalRing R] in
/- English proof (translation)
The claim follows from `forall_congr' fun s => existsUnique_congr fun a => secIsMul_iff _ a s g`.
-/
theorem secBGenerates_iff_smul {k : ℕ} {α : D.toPre.X} (g : SecBMod D.toPre k α) :
    SecBGenerates (D := D) k α g ↔ ∀ s : SecBMod D.toPre k α, ∃! a : R, s = a • g :=
  forall_congr' fun s => existsUnique_congr fun a => secIsMul_iff _ a s g

/- English proof (translation)
Take `⟨b, hb⟩` from `exists_generator D.toPre hS`. Use `h.generates_iff.trans ⟨fun H => ?_, fun H s => (H s).exists⟩` and prove the remaining obligations. Conclude with `(secBGenerates_iff_smul g).2 (existsUnique_of_exists ((secBGenerates_iff_smul (D := D) b).1 hb) ((generates_iff_smul _ g).1 H))`.
-/
theorem generates_iff_secBGenerates (hS : SecBaseChangeSt) [IsNoetherianRing R] {th : H0 D.toPre.P.L 1}
    {g : D.toPre.SecB 1 0} (h : Corr D.toPre th g) :
    Generates D.toPre.P.A.hom th ↔ SecBGenerates (D := D) 1 0 g := by
  obtain ⟨b, hb⟩ := exists_generator D.toPre hS
  refine h.generates_iff.trans ⟨fun H => ?_, fun H s => (H s).exists⟩
  exact (secBGenerates_iff_smul g).2 (existsUnique_of_exists ((secBGenerates_iff_smul (D := D) b).1 hb)
    ((generates_iff_smul _ g).1 H))

omit [IsDomain R] in

/- English proof (translation)
Establish `hm : closedPoint R ∈ Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk (J ^ (e + 1))))`. Rewrite using `[_root_.range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker, PrimeSpectrum.mem_zeroLocus]`. Conclude with `(Ideal.pow_le_self (Nat.succ_ne_zero e)).trans hJ`. Take `⟨z, hz⟩` from `hm`. Take `⟨y, hy, -⟩` from `Scheme.exists_preimage_of_isPullback (IsPullback.of_hasPullback X.hom (thick R J e)) x z (hx.trans hz.symm)`.

Conclude with `⟨y, hy⟩`.
-/
theorem exists_thick_pt {J : Ideal R} (hJ : J ≤ maximalIdeal R) (e : ℕ) (X : Over (Spec (CommRingCat.of R)))
    (x : X.left) (hx : X.hom x = closedPoint R) :
    ∃ y : (thickObj R J e X).left, pullback.fst X.hom (thick R J e) y = x := by
  have hm : closedPoint R ∈ Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk (J ^ (e + 1)))) := by
    rw [_root_.range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker,
      PrimeSpectrum.mem_zeroLocus]
    exact (Ideal.pow_le_self (Nat.succ_ne_zero e)).trans hJ
  obtain ⟨z, hz⟩ := hm
  obtain ⟨y, hy, -⟩ := Scheme.exists_preimage_of_isPullback (IsPullback.of_hasPullback X.hom (thick R J e)) x z
    (hx.trans hz.symm)
  exact ⟨y, hy⟩

/- English proof (translation)
Take `⟨x', rfl⟩` from `exists_thick_pt hI e D.toPre.P.A x hx`. Take `⟨y, rfl⟩` from `(U.gt e).q_surj.surj x'`. Conclude with `⟨y, rfl⟩`.
-/
theorem exists_group_pt (hI : I ≤ maximalIdeal R) (U : UnifPre I D A G) (e : ℕ) (x : D.toPre.P.A.left)
    (hx : D.toPre.P.A.hom x = closedPoint R) : ∃ y : (thickObj R I e G).left, pGl U e y = x := by
  obtain ⟨x', rfl⟩ := exists_thick_pt hI e D.toPre.P.A x hx
  obtain ⟨y, rfl⟩ := (U.gt e).q_surj.surj x'
  exact ⟨y, rfl⟩

/- English proof (translation)
Take `⟨th, x, hx, hn⟩` from `exists_nonzero_closed hS D.toPre`. Take `⟨y, rfl⟩` from `exists_group_pt hI U 0 x hx`. Take `⟨J, hJ⟩` from `exists_good' D.toPre.P.isLB y`. Take `⟨c, hc, -⟩` from `hgen th`. Establish `hfu : IsUnit (sval (f 0) (pGl U 0) y J)`.

Use `isUnit_sval th _ y hn hJ` as an intermediate fact. Rewrite `this` using `[sval_of_secIsMul hc _ y hJ]`. Conclude with `isUnit_of_mul_isUnit_right this`. Take `⟨a, ha, -⟩` from `hgen (g 0)`. Set `g' : ∀ α, SecBMod D.toPre 1 α` to `g`.

Set `f' : ∀ α, SecBMod D.toPre 1 α` to `f`. Set `θ : SecOver G.hom (LB.LinComb U.LG.L (K` to `Fin 1) (fun _ => 𝟙 G.left) (fun _ => ((1 : ℕ) : ℤ))) := ϑ`. Establish `hE₀` using `expandsAt_add U (σ := θ) (f := g') hg (expandsAt_smul U (-1 : R) (σ := θ) (f := f') hf)`. Establish `h₁` using `WeightDvd.dvd_on_group U 0 1 0 _ θ _ ((secIsMul_iff _ _ _ _).2 (by rw [neg_one_smul, add_neg_cancel, zero_smul])) hE₀ 0 y J hJ`. Establish `h₂ : (g' + (-1 : R) • f') 0 = (a - 1) • f' 0`.

Rewrite using `[Pi.add_apply, Pi.smul_apply, sub_smul, sub_eq_add_neg, neg_smul, ← (secIsMul_iff _ _ (g' 0) (f' 0)).1 ha]`. Rewrite `h₁` using `[h₂, GermDiv.cst_zero, zero_dvd_iff, sval_of_secIsMul ((secIsMul_iff _ _ _ _).2 rfl) _ y hJ, hfu.mul_left_eq_zero, cst_sub, cst_one', sub_eq_zero]`. Establish `hu : IsUnit a`. Assume the negation of the conclusion as `hn'`. Conclude with `cst_not_isUnit (pGl U 0 ≫ D.toPre.P.A.hom) y hx hn' (h₁ ▸ isUnit_one)`.

Conclude with `(secBGenerates_iff_smul (g' 0)).2 (existsUnique_of_isUnit ((secBGenerates_iff_smul (f' 0)).1 hgen) hu ((secIsMul_iff _ _ (g' 0) (f' 0)).1 ha))`.
-/
theorem secBGenerates_of_expandsAt (hS : SecBaseChangeSt) [IsNoetherianRing R] (hI : I ≤ maximalIdeal R)
    (U : UnifPre I D A G) {ϑ : H0 U.LG.L 1} {f g : ∀ α, D.toPre.SecB 1 α} (hf : U.ExpandsAt 0 1 ϑ f)
    (hg : U.ExpandsAt 0 1 ϑ g) (hgen : SecBGenerates (D := D) 1 0 (f 0)) : SecBGenerates (D := D) 1 0 (g 0) := by
  obtain ⟨th, x, hx, hn⟩ := exists_nonzero_closed hS D.toPre
  obtain ⟨y, rfl⟩ := exists_group_pt hI U 0 x hx
  obtain ⟨J, hJ⟩ := exists_good' D.toPre.P.isLB y
  obtain ⟨c, hc, -⟩ := hgen th
  have hfu : IsUnit (sval (f 0) (pGl U 0) y J) := by
    have := isUnit_sval th _ y hn hJ
    rw [sval_of_secIsMul hc _ y hJ] at this
    exact isUnit_of_mul_isUnit_right this
  obtain ⟨a, ha, -⟩ := hgen (g 0)
  let g' : ∀ α, SecBMod D.toPre 1 α := g
  let f' : ∀ α, SecBMod D.toPre 1 α := f
  let θ : SecOver G.hom (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => ((1 : ℕ) : ℤ))) := ϑ
  have hE₀ := expandsAt_add U (σ := θ) (f := g') hg (expandsAt_smul U (-1 : R) (σ := θ) (f := f') hf)
  have h₁ := WeightDvd.dvd_on_group U 0 1 0 _ θ _ ((secIsMul_iff _ _ _ _).2
    (by rw [neg_one_smul, add_neg_cancel, zero_smul])) hE₀ 0 y J hJ
  have h₂ : (g' + (-1 : R) • f') 0 = (a - 1) • f' 0 := by
    rw [Pi.add_apply, Pi.smul_apply, sub_smul, sub_eq_add_neg, neg_smul, ← (secIsMul_iff _ _ (g' 0) (f' 0)).1 ha]
  rw [h₂, GermDiv.cst_zero, zero_dvd_iff, sval_of_secIsMul ((secIsMul_iff _ _ _ _).2 rfl) _ y hJ,
    hfu.mul_left_eq_zero, cst_sub, cst_one', sub_eq_zero] at h₁
  have hu : IsUnit a := by
    by_contra hn'
    exact cst_not_isUnit (pGl U 0 ≫ D.toPre.P.A.hom) y hx hn' (h₁ ▸ isUnit_one)
  exact (secBGenerates_iff_smul (g' 0)).2 (existsUnique_of_isUnit ((secBGenerates_iff_smul (f' 0)).1 hgen) hu
    ((secIsMul_iff _ _ (g' 0) (f' 0)).1 ha))

def UnitMulClause (U : Unif I D A G) : Prop :=
  ∀ ϑ : H0 U.LG.L 1, IsTheta U ϑ → ∀ σ : H0 U.LG.L 1,
    (∃ u : Rˣ, SecIsMul G.hom (u : R) σ ϑ) ↔ NonzeroOnSpecial U σ

def ThetaClause (U : Unif I D A G) : Prop := ∀ s : H0 U.LG.L 1, NonzeroOnSpecial U s → IsTheta U s

def SpanClause (U : Unif I D A G) : Prop :=
  (∃ ϑ : H0 U.LG.L 1, IsTheta U ϑ) ∧
    ∀ ϑ : H0 U.LG.L 1, IsTheta U ϑ → ∀ s : H0 U.LG.L 1, ∃ a : R, SecIsMul G.hom a s ϑ

variable (hS : SecBaseChangeSt) [IsNoetherianRing R] (hI : I ≤ maximalIdeal R) (U : Unif I D A G)
include hS hI

end Notions

section Closed

abbrev Clause : Type 1 :=
  ∀ {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {I : Ideal R} {D : DegData R I}
    {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
    [IsCommMonObj G], Unif I D A G → Prop

def ClauseValidOverLocalDomain (P : Clause) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R) : Prop :=
  ∀ (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R))))
    (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G →
    ∀ U : Unif I D A G, P U

def ClauseValidDvr (P : Clause) : Prop :=
  Laws → Laws4 → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [IsAdicComplete (maximalIdeal V) V], ClauseValidOverLocalDomain P V (maximalIdeal V)

def ClauseValidArc (P : Clause) : Prop :=
  Laws → Laws4 → ∀ (O' : Type) [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O']
    [IsAdicComplete (maximalIdeal O') O'],
    ClauseValidOverLocalDomain P (PowerSeries O') (Ideal.span {(PowerSeries.X : PowerSeries O')})

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun ⟨_, _, _, _, h⟩ => h, fun h => ⟨inferInstance, inferInstance, inferInstance, inferInstance, h⟩⟩`.
-/
theorem clnd_iff_of_dvr (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] :
    CLND V ↔ IsAdicComplete (maximalIdeal V) V :=
  ⟨fun ⟨_, _, _, _, h⟩ => h, fun h => ⟨inferInstance, inferInstance, inferInstance, inferInstance, h⟩⟩

end Closed

end GlobalTheory.ThetaCompare
