import Mathlib
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.OpensRangeChartYSupOpensRangeChartZ
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddXYZOrChordXYZOrOriginXYZNeZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.EigLatBasis

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.WeierstrassCurve GlobalTheory.AddLaw

noncomputable section

namespace GlobalTheory.WeierstrassLie

variable {R : Type} [CommRing R] (W : WeierstrassCurve R)

/- English proof (translation)
Rewrite using `[equation_origin_iff]`. Simplify using `[pow_succ, TrivSqZeroExt.inr_mul_inr]`.
-/
theorem equation_inr (c : R) : (W.map (algebraMap R (DualNumber R))).toProjective.Equation
    ![TrivSqZeroExt.inr c, -1, 0] := by
  rw [equation_origin_iff]
  simp [pow_succ, TrivSqZeroExt.inr_mul_inr]

def vec (c : R) : Spec (.of (DualNumber R)) ⟶ scheme W :=
  ptHom W (algebraMap R (DualNumber R)) ![TrivSqZeroExt.inr c, -1, 0]
    (isUnimodularSol_origin (equation_inr W c))

/- English proof (translation)
Use `(SpecMap_ptHom W _ _ _ (epsScaleR c)).trans (ptHom_congr W _ _ _ ?_ ?_ _)` and prove the remaining obligations. Apply the tactic sequence `ext a <;> simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]`. Use `ext1 j fin_cases j`. Apply the tactic sequence `ext <;> simp [epsScaleR]`. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules.
-/
theorem scale_vec (c : R) : spMap (epsScaleR c) ≫ vec W 1 = vec W c := by
  refine (SpecMap_ptHom W _ _ _ (epsScaleR c)).trans (ptHom_congr W _ _ _ ?_ ?_ _)
  · ext a <;> simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]
  · ext1 j
    fin_cases j
    · ext <;> simp [epsScaleR]
    · simp
    · simp

/- English proof (translation)
Rewrite `e` using `[vec, vec, ← SpecMap_originEval_chartY W _ _ _ (equation_inr W c), ← SpecMap_originEval_chartY W _ _ _ (equation_inr W d), cancel_mono]`. Establish `e' : originEval W _ _ _ (equation_inr W c) = originEval W _ _ _ (equation_inr W d)` using `congrArg (·.hom) (Spec.map_injective e)`. Use `RingHom.congr_fun e' (originZ W)` as an intermediate fact. Rewrite `this` using `[originEval_originZ, originEval_originZ]`. Simplify using `using congrArg TrivSqZeroExt.snd this`.
-/
theorem vec_inj {c d : R} (e : vec W c = vec W d) : c = d := by
  rw [vec, vec, ← SpecMap_originEval_chartY W _ _ _ (equation_inr W c),
    ← SpecMap_originEval_chartY W _ _ _ (equation_inr W d), cancel_mono] at e
  have e' : originEval W _ _ _ (equation_inr W c) = originEval W _ _ _ (equation_inr W d) :=
    congrArg (·.hom) (Spec.map_injective e)
  have := RingHom.congr_fun e' (originZ W)
  rw [originEval_originZ, originEval_originZ] at this
  simpa using congrArg TrivSqZeroExt.snd this

/- English proof (translation)
Use `(SpecMap_ptHom W _ _ _ (TrivSqZeroExt.fstHom R R R).toRingHom).trans ?_` and prove the remaining obligations. Rewrite using `[zero, ← pt_smul W (A := R) _ _ isUnit_one.neg]`. Use `ptHom_congr W _ _ _ ?_ ?_ _` and prove the remaining obligations. Use extensionality with `a`. Simplify using `[TrivSqZeroExt.algebraMap_eq_inl]`.

Apply the tactic sequence `ext1 j fin_cases j <;> simp`.
-/
theorem fst_vec (c : R) :
    spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ vec W c = zero W := by
  refine (SpecMap_ptHom W _ _ _ (TrivSqZeroExt.fstHom R R R).toRingHom).trans ?_
  rw [zero, ← pt_smul W (A := R) _ _ isUnit_one.neg]
  refine ptHom_congr W _ _ _ ?_ ?_ _
  · ext a; simp [TrivSqZeroExt.algebraMap_eq_inl]
  · ext1 j
    fin_cases j <;> simp

/- English proof (translation)
Introduce `p`. Use `⟨PrimeSpectrum.comap (algebraMap R (DualNumber R)) p, PrimeSpectrum.ext (Ideal.ext fun a => ?_)⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `algebraMap R (DualNumber R) a.fst ∈ p.asIdeal ↔ a ∈ p.asIdeal`. Establish `h : (TrivSqZeroExt.inr a.snd : DualNumber R) ∈ p.asIdeal` using `p.isPrime.mem_of_pow_mem 2 (by rw [pow_two, TrivSqZeroExt.inr_mul_inr]; exact zero_mem _)`. Use `conv_rhs => rw [← TrivSqZeroExt.inl_fst_add_inr_snd_eq a]`.

Conclude with `(Ideal.add_mem_iff_left _ h).symm`.
-/
theorem surjective_fst :
    Function.Surjective (PrimeSpectrum.comap (TrivSqZeroExt.fstHom R R R).toRingHom) := by
  intro p
  refine ⟨PrimeSpectrum.comap (algebraMap R (DualNumber R)) p, PrimeSpectrum.ext (Ideal.ext fun a => ?_)⟩
  change algebraMap R (DualNumber R) a.fst ∈ p.asIdeal ↔ a ∈ p.asIdeal
  have h : (TrivSqZeroExt.inr a.snd : DualNumber R) ∈ p.asIdeal :=
    p.isPrime.mem_of_pow_mem 2 (by rw [pow_two, TrivSqZeroExt.inr_mul_inr]; exact zero_mem _)
  conv_rhs => rw [← TrivSqZeroExt.inl_fst_add_inr_snd_eq a]
  exact (Ideal.add_mem_iff_left _ h).symm

/- English proof (translation)
Establish `hr : Set.range g ⊆ Set.range (chartY W)`. Introduce and unpack `_ ⟨p, rfl⟩`. Take `⟨q, rfl⟩` from `surjective_fst p`. Rewrite using `[← Scheme.Hom.coe_opensRange, opensRange_chartY]`. Establish `: q ∈ zero W ⁻¹ᵁ coordOpen W 1`.

Rewrite using `[zero_preimage_coordOpen_one]`. Discharge the goal by the elementary cases of `trivial`. Rewrite `this` using `[← h0]`. Conclude with `this`. Take `⟨φ, hφ⟩` from `Spec.map_surjective (IsOpenImmersion.lift _ _ hr)`.

Establish `hl : Spec.map φ ≫ chartY W = g` using `hφ ▸ IsOpenImmersion.lift_fac _ _ hr`. Establish `hc : φ.hom.comp (algebraMap R (OriginRing W)) = algebraMap R (DualNumber R)`. Rewrite `hg` using `[← hl, Category.assoc, chartY_toSpec, ← Spec.map_comp]`. Conclude with `congrArg (·.hom) (Spec.map_injective hg)`. Establish `ha : (TrivSqZeroExt.fstHom R R R).toRingHom.comp φ.hom = (originAug W : OriginRing W →+* R)`.

Rewrite `h0` using `[← hl, ← SpecMap_originAug_chartY, ← Category.assoc, cancel_mono]`. Conclude with `congrArg (·.hom) (Spec.map_injective ((Spec.map_comp _ _).trans h0))`. Establish `hz : (φ.hom (originZ W)).fst = 0` using `(RingHom.congr_fun ha _).trans (originAug_originZ W)`. Establish `hw : (φ.hom (originW W)).fst = 0` using `(RingHom.congr_fun ha _).trans (originAug_originW W)`. Establish `hw0 : φ.hom (originW W) = 0`.

Establish `e` using `congrArg φ.hom ((equation_origin_iff _ _ _).mp (equation_originZ_originW W))`. Simplify using `only [map_add, map_mul, map_pow] at e`. Use `ext`. Conclude with `hw`. Rewrite using `[e]`.

Simplify using `[pow_succ, hz, hw]`. Establish `hz0 : φ.hom (originZ W) = TrivSqZeroExt.inr (φ.hom (originZ W)).snd`. Apply the tactic sequence `ext <;> simp [hz]`. Use `⟨(φ.hom (originZ W)).snd, ?_⟩` and prove the remaining obligations. Rewrite using `[← hl, vec, ← SpecMap_originEval_chartY W _ _ _ (equation_inr W _)]`.

Use `congr 2`. Use `ext1`. Use `origin_hom_ext W (fun r => ?_) ?_ ?_` and prove the remaining obligations. Conclude with `(RingHom.congr_fun hc r).trans (originEval_algebraMap W _ _ _ (equation_inr W _) r).symm`. Conclude with `hz0.trans (originEval_originZ W _ _ _ (equation_inr W _)).symm`.

Conclude with `hw0.trans (originEval_originW W _ _ _ (equation_inr W _)).symm`.
-/
theorem exists_eq_vec (g : Spec (.of (DualNumber R)) ⟶ scheme W)
    (hg : g ≫ toSpec W = spMap (algebraMap R (DualNumber R)))
    (h0 : spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ g = zero W) : ∃ c, g = vec W c := by
  have hr : Set.range g ⊆ Set.range (chartY W) := by
    rintro _ ⟨p, rfl⟩
    obtain ⟨q, rfl⟩ := surjective_fst p
    rw [← Scheme.Hom.coe_opensRange, opensRange_chartY]
    have : q ∈ zero W ⁻¹ᵁ coordOpen W 1 := by
      rw [zero_preimage_coordOpen_one]; trivial
    rw [← h0] at this
    exact this
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (IsOpenImmersion.lift _ _ hr)
  have hl : Spec.map φ ≫ chartY W = g := hφ ▸ IsOpenImmersion.lift_fac _ _ hr
  have hc : φ.hom.comp (algebraMap R (OriginRing W)) = algebraMap R (DualNumber R) := by
    rw [← hl, Category.assoc, chartY_toSpec, ← Spec.map_comp] at hg
    exact congrArg (·.hom) (Spec.map_injective hg)
  have ha : (TrivSqZeroExt.fstHom R R R).toRingHom.comp φ.hom =
      (originAug W : OriginRing W →+* R) := by
    rw [← hl, ← SpecMap_originAug_chartY, ← Category.assoc, cancel_mono] at h0
    exact congrArg (·.hom) (Spec.map_injective ((Spec.map_comp _ _).trans h0))
  have hz : (φ.hom (originZ W)).fst = 0 := (RingHom.congr_fun ha _).trans (originAug_originZ W)
  have hw : (φ.hom (originW W)).fst = 0 := (RingHom.congr_fun ha _).trans (originAug_originW W)
  have hw0 : φ.hom (originW W) = 0 := by
    have e := congrArg φ.hom ((equation_origin_iff _ _ _).mp (equation_originZ_originW W))
    simp only [map_add, map_mul, map_pow] at e
    ext
    · exact hw
    · rw [e]
      simp [pow_succ, hz, hw]
  have hz0 : φ.hom (originZ W) = TrivSqZeroExt.inr (φ.hom (originZ W)).snd := by
    ext <;> simp [hz]
  refine ⟨(φ.hom (originZ W)).snd, ?_⟩
  rw [← hl, vec, ← SpecMap_originEval_chartY W _ _ _ (equation_inr W _)]
  congr 2
  ext1
  refine origin_hom_ext W (fun r => ?_) ?_ ?_
  · exact (RingHom.congr_fun hc r).trans (originEval_algebraMap W _ _ _ (equation_inr W _) r).symm
  · exact hz0.trans (originEval_originZ W _ _ _ (equation_inr W _)).symm
  · exact hw0.trans (originEval_originW W _ _ _ (equation_inr W _)).symm

/- English proof (translation)
Introduce `R _ W _ hη`. Set `v : epsR R ⟶ schemeOver W` to `Over.homMk (vec W 1) (ptHom_toSpec ..)`. Establish `key : ∀ (c : Fin 1 → R) (w : epsR R ⟶ schemeOver W), IsLieComb c ![v] w ↔ w.left = vec W (c 0)`. Introduce `c w`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨u, hu, rfl⟩`. Establish `: (List.ofFn u).prod = u 0` using `by simp`. Rewrite using `[this]`. Conclude with `(hu 0).trans (scale_vec W _)`. Introduce `h`.

Use `⟨fun _ => w, fun i => ?_, by simp⟩` and prove the remaining obligations. Take `rfl : i = 0` from `Subsingleton.elim _ _`. Conclude with `h.trans (scale_vec W _).symm`. Use `⟨v, ⟨isUnimodularSol_origin (equation_inr W 1), rfl⟩, fun i => ?_, fun w hw => ?_⟩` and prove the remaining obligations. Take `rfl : i = 0` from `Subsingleton.elim _ _`.

Conclude with `(fst_vec W 1).trans hη.symm`. Take `⟨c, hc⟩` from `exists_eq_vec W w.left (Over.w w) (hw.trans hη)`. Use `⟨fun _ => c, (key _ _).mpr hc, fun d hd => ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`. Take `rfl : i = 0` from `Subsingleton.elim _ _`.

Conclude with `vec_inj W (((key _ _).mp hd).symm.trans hc)`.
-/
theorem isLieBasis_eps : ∀ (R : Type) [CommRing R] (W : WeierstrassCurve R)
    [GrpObj (schemeOver W)], η[schemeOver W].left = zero W → ∃ v : epsR R ⟶ schemeOver W,
      (∃ h : IsUnimodularSol (W.map (algebraMap R (DualNumber R))) ![DualNumber.eps, -1, 0],
        v.left = ptHom W (algebraMap R (DualNumber R)) ![DualNumber.eps, -1, 0] h) ∧
      IsLieBasis ![v] := by
  intro R _ W _ hη
  let v : epsR R ⟶ schemeOver W := Over.homMk (vec W 1) (ptHom_toSpec ..)
  have key : ∀ (c : Fin 1 → R) (w : epsR R ⟶ schemeOver W),
      IsLieComb c ![v] w ↔ w.left = vec W (c 0) := by
    intro c w
    constructor
    · rintro ⟨u, hu, rfl⟩
      have : (List.ofFn u).prod = u 0 := by simp
      rw [this]
      exact (hu 0).trans (scale_vec W _)
    · intro h
      refine ⟨fun _ => w, fun i => ?_, by simp⟩
      obtain rfl : i = 0 := Subsingleton.elim _ _
      exact h.trans (scale_vec W _).symm
  refine ⟨v, ⟨isUnimodularSol_origin (equation_inr W 1), rfl⟩, fun i => ?_, fun w hw => ?_⟩
  · obtain rfl : i = 0 := Subsingleton.elim _ _
    exact (fst_vec W 1).trans hη.symm
  · obtain ⟨c, hc⟩ := exists_eq_vec W w.left (Over.w w) (hw.trans hη)
    refine ⟨fun _ => c, (key _ _).mpr hc, fun d hd => ?_⟩
    funext i
    obtain rfl : i = 0 := Subsingleton.elim _ _
    exact vec_inj W (((key _ _).mp hd).symm.trans hc)

end GlobalTheory.WeierstrassLie
