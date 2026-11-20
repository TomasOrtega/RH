import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.PullChartIsLB
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemRangeCompIffOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnitCharts
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical

noncomputable section
namespace GlobalTheory.ZH.LinFrame
open GlobalTheory.ProjSpace

variable {o : Type} [CommRing o] {m : ℕ} {T : Scheme.{0}}

def chartLB (p : T ⟶ PSpace o m) : LB T :=
  ⟨Fin (m + 1), fun i => p ⁻¹ᵁ chart o m i, fun i j =>
    ⟨pullRatio p _ i inf_le_left j, pullRatio p _ j inf_le_right i,
      pullRatio_mul_pullRatio.trans pullRatio_self, pullRatio_mul_pullRatio.trans pullRatio_self⟩⟩

/- English proof (translation)
Rewrite using `[map_sum, map_sum, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, map_mul, resG_pullRatio, resG_pullRatio, mul_left_comm, pullRatio_mul_pullRatio]`. Use `congr 1`. Conclude with `(DVR.SecOps.resTop_res _ _).trans (DVR.SecOps.resTop_res _ _).symm`.
-/
theorem lin_compat (p : T ⟶ PSpace o m) (b : Fin (m + 1) → Γ(T, ⊤)) (i j : Fin (m + 1)) :
    resG T (inf_le_left : p ⁻¹ᵁ chart o m i ⊓ p ⁻¹ᵁ chart o m j ≤ _)
        (∑ k, resG T le_top (b k) * pullRatio p (p ⁻¹ᵁ chart o m i) i le_rfl k) =
      pullRatio p (p ⁻¹ᵁ chart o m i ⊓ p ⁻¹ᵁ chart o m j) i inf_le_left j *
        resG T (inf_le_right : p ⁻¹ᵁ chart o m i ⊓ p ⁻¹ᵁ chart o m j ≤ _)
          (∑ k, resG T le_top (b k) * pullRatio p (p ⁻¹ᵁ chart o m j) j le_rfl k) := by
  rw [map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, map_mul, resG_pullRatio, resG_pullRatio, mul_left_comm, pullRatio_mul_pullRatio]
  congr 1
  exact (DVR.SecOps.resTop_res _ _).trans (DVR.SecOps.resTop_res _ _).symm

def linSec (p : T ⟶ PSpace o m) (b : Fin (m + 1) → Γ(T, ⊤)) : (chartLB p).Sec where
  f l := ∑ k, resG T le_top (b k) * pullRatio p (p ⁻¹ᵁ chart o m l) l le_rfl k
  compat i j := lin_compat p b i j

variable {K : Type} [Field K]

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem crd_iff (x : Sp K ⟶ PSpace o m) (v : Fin (m + 1) → K) : Crd (O1 o m) (coord o m) x v ↔
    ∃ (l : Fin (m + 1)) (c : Kˣ), ⊤ ≤ x ⁻¹ᵁ chart o m l ∧
      ∀ j, v j = (c : K) * valR x (chart o m l) (ratio o m l j) := Iff.rfl

/- English proof (translation)
The claim follows from `Points.valR_appLE x p hl h _`.
-/
theorem valR_pullRatio (x : Sp K ⟶ T) (p : T ⟶ PSpace o m) {W : T.Opens} {l : Fin (m + 1)}
    (hl : W ≤ p ⁻¹ᵁ chart o m l) (h : ⊤ ≤ x ⁻¹ᵁ W) (k : Fin (m + 1)) :
    valR x W (pullRatio p W l hl k) = valR (x ≫ p) (chart o m l) (ratio o m l k) :=
  Points.valR_appLE x p hl h _

/- English proof (translation)
Express the relevant statement in the definitionally equal form `valR x (p ⁻¹ᵁ chart o m l) (∑ k, resG T le_top (b i k) * pullRatio p (p ⁻¹ᵁ chart o m l) l le_rfl k) = ∑ k, valR x ⊤ (b i k) * valR (x ≫ p) (chart o m l) (ratio o m l k)`. Rewrite using `[CrdCalc.valR_eq x _ h, map_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[← CrdCalc.valR_eq x _ h, CrdCalc.valR_mul x _ h, CrdCalc.valR_res x _ h, valR_pullRatio x p _ h]`.
-/
theorem valR_linSec (x : Sp K ⟶ T) (p : T ⟶ PSpace o m) (b : Matrix (Fin (m + 1)) (Fin (m + 1)) Γ(T, ⊤))
    {l : Fin (m + 1)} (h : ⊤ ≤ x ⁻¹ᵁ p ⁻¹ᵁ chart o m l) (i : Fin (m + 1)) :
    valR x (p ⁻¹ᵁ chart o m l) ((linSec p (b i)).f l) =
      (b.map (valR x ⊤)).mulVec (fun k => valR (x ≫ p) (chart o m l) (ratio o m l k)) i := by
  change valR x (p ⁻¹ᵁ chart o m l) (∑ k, resG T le_top (b i k) * pullRatio p (p ⁻¹ᵁ chart o m l) l le_rfl k) =
    ∑ k, valR x ⊤ (b i k) * valR (x ≫ p) (chart o m l) (ratio o m l k)
  rw [CrdCalc.valR_eq x _ h, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← CrdCalc.valR_eq x _ h, CrdCalc.valR_mul x _ h, CrdCalc.valR_res x _ h, valR_pullRatio x p _ h]

/- English proof (translation)
Rewrite using `[ratio, ratioOn_self, Points.valR_one x _ h]`.
-/
theorem valR_ratio_self (x : Sp K ⟶ PSpace o m) {l : Fin (m + 1)} (h : ⊤ ≤ x ⁻¹ᵁ chart o m l) :
    valR x (chart o m l) (ratio o m l l) = 1 := by
  rw [ratio, ratioOn_self, Points.valR_one x _ h]

/- English proof (translation)
Assume the negation of the conclusion as `hn`. Establish `e : b.map (valR x ⊤) = (CrdCalc.valHom x ⊤ le_top).mapMatrix b`. Use extensionality with `i j`. Conclude with `CrdCalc.valR_eq x ⊤ le_top _`. Establish `hd : (b.map (valR x ⊤)).det ≠ 0`.

Rewrite using `[e, ← RingHom.map_det]`. Conclude with `(hb.map _).ne_zero`. Establish `h0` using `Matrix.eq_zero_of_mulVec_eq_zero hd (v := fun k => valR (x ≫ p) (chart o m l) (ratio o m l k)) (funext fun i => by`. Rewrite using `[← valR_linSec x p b h]`. Assume the negation of the conclusion as `hi`.

Conclude with `hn ⟨i, Ne.isUnit hi⟩)`. Establish `h1` using `congrFun h0 l`. Rewrite `h1` using `[valR_ratio_self (x ≫ p) h]`. Conclude with `one_ne_zero h1`.
-/
theorem exists_isUnit_valR_linSec (x : Sp K ⟶ T) (p : T ⟶ PSpace o m)
    {b : Matrix (Fin (m + 1)) (Fin (m + 1)) Γ(T, ⊤)} (hb : IsUnit b.det)
    {l : Fin (m + 1)} (h : ⊤ ≤ x ⁻¹ᵁ p ⁻¹ᵁ chart o m l) :
    ∃ i, IsUnit (valR x (p ⁻¹ᵁ chart o m l) ((linSec p (b i)).f l)) := by
  by_contra hn
  have e : b.map (valR x ⊤) = (CrdCalc.valHom x ⊤ le_top).mapMatrix b := by
    ext i j
    exact CrdCalc.valR_eq x ⊤ le_top _
  have hd : (b.map (valR x ⊤)).det ≠ 0 := by
    rw [e, ← RingHom.map_det]
    exact (hb.map _).ne_zero
  have h0 := Matrix.eq_zero_of_mulVec_eq_zero hd
    (v := fun k => valR (x ≫ p) (chart o m l) (ratio o m l k)) (funext fun i => by
      rw [← valR_linSec x p b h]
      by_contra hi
      exact hn ⟨i, Ne.isUnit hi⟩)
  have h1 := congrFun h0 l
  rw [valR_ratio_self (x ≫ p) h] at h1
  exact one_ne_zero h1

/- English proof (translation)
Use `top_le_iff.1 fun y _ => ?_` and prove the remaining obligations. Take `⟨l, hl⟩` from `TopologicalSpace.Opens.mem_iSup.1 ((iSup_chart o m).ge (Set.mem_univ (p y)))`. Set `x : Sp (T.residueField y) ⟶ T` to `T.fromSpecResidueField y`. Establish `hx : ∀ z, x z = y` using `fun z => T.fromSpecResidueField_apply y z`. Establish `h : ⊤ ≤ x ⁻¹ᵁ p ⁻¹ᵁ chart o m l` using `fun z _ => by`.

Express the relevant statement in the definitionally equal form `p (x z) ∈ chart o m l`. Rewrite using `[hx]`. Conclude with `hl`. Take `⟨i, hi⟩` from `exists_isUnit_valR_linSec x p hb h`. Establish `h2 : x (IsLocalRing.closedPoint _) ∈ T.basicOpen ((linSec p (b i)).f l)` using `(CrdCalc.isUnit_valR_iff x _ h _).1 hi (Set.mem_univ _)`.

Conclude with `TopologicalSpace.Opens.mem_iSup.2 ⟨i, TopologicalSpace.Opens.mem_iSup.2 ⟨l, (congrArg (· ∈ T.basicOpen ((linSec p (b i)).f l)) (hx _)).mp h2⟩⟩`.
-/
theorem iSup_nonzeroLocus_linSec (p : T ⟶ PSpace o m)
    {b : Matrix (Fin (m + 1)) (Fin (m + 1)) Γ(T, ⊤)} (hb : IsUnit b.det) :
    ⨆ i, nonzeroLocus (linSec p (b i)) = ⊤ := by
  refine top_le_iff.1 fun y _ => ?_
  obtain ⟨l, hl⟩ := TopologicalSpace.Opens.mem_iSup.1 ((iSup_chart o m).ge (Set.mem_univ (p y)))
  let x : Sp (T.residueField y) ⟶ T := T.fromSpecResidueField y
  have hx : ∀ z, x z = y := fun z => T.fromSpecResidueField_apply y z
  have h : ⊤ ≤ x ⁻¹ᵁ p ⁻¹ᵁ chart o m l := fun z _ => by
    change p (x z) ∈ chart o m l
    rw [hx]; exact hl
  obtain ⟨i, hi⟩ := exists_isUnit_valR_linSec x p hb h
  have h2 : x (IsLocalRing.closedPoint _) ∈ T.basicOpen ((linSec p (b i)).f l) :=
    (CrdCalc.isUnit_valR_iff x _ h _).1 hi (Set.mem_univ _)
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, TopologicalSpace.Opens.mem_iSup.2 ⟨l, (congrArg (· ∈ T.basicOpen ((linSec p (b i)).f l)) (hx _)).mp h2⟩⟩

/- English proof (translation)
Take `⟨l, u, hl, hv⟩` from `(crd_iff _ _).1 hv`. Establish `h : ⊤ ≤ x ⁻¹ᵁ p ⁻¹ᵁ chart o m l` using `hl`. Take `⟨i, hi⟩` from `exists_isUnit_valR_linSec x p hb h`. Use `set g := toProj c (fun i => linSec p (b i)) (iSup_nonzeroLocus_linSec p hb) with hg`. Establish `h₁ : ⊤ ≤ x ⁻¹ᵁ g ⁻¹ᵁ chart A m i`.

Rewrite using `[hg, toProj_preimage_chart]`. Conclude with `((CrdCalc.isUnit_valR_iff x _ h _).1 hi).trans (x.preimage_mono (le_iSup (fun k => T.basicOpen ((linSec p (b i)).f k)) l))`. Establish `h₂ : ⊤ ≤ x ⁻¹ᵁ (g ⁻¹ᵁ chart A m i ⊓ p ⁻¹ᵁ chart o m l)` using `fun z hz => ⟨h₁ hz, h hz⟩`. Use `(crd_iff _ _).2 ⟨i, u * hi.unit, h₁, fun j => ?_⟩` and prove the remaining obligations. Establish `e` using `congrArg (valR x _) (sec_eq_pullRatio_toProj_mul c (fun i => linSec p (b i)) (iSup_nonzeroLocus_linSec p hb) i j l (W := g ⁻¹ᵁ chart A m i ⊓ p ⁻¹ᵁ chart o m l) inf_le_left inf_le_right)`.

Establish `r : ∀ t : (chartLB p).Sec, _ = valR x (p ⁻¹ᵁ chart o m l) (t.f l)` using `fun t => CrdCalc.valR_res x inf_le_right h₂ (t.f l)`. Use `replace e := (r _).symm.trans (e.trans ((CrdCalc.valR_mul x _ h₂ _ _).trans (congrArg₂ (· * ·) (valR_pullRatio x _ _ h₂ _) (r _))))`. Establish `ev : v = (u : K) • fun k => valR (x ≫ p) (chart o m l) (ratio o m l k)` using `funext hv`. Rewrite using `[ev, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, ← valR_linSec x p b h, Units.val_mul, IsUnit.unit_spec, _root_.mul_assoc]`. Conclude with `congrArg (_ * ·) (e.trans (mul_comm _ _))`.
-/
theorem crd_toProj_linSec {A : Type} [CommRing A] (c : T ⟶ Sp A) (p : T ⟶ PSpace o m)
    {b : Matrix (Fin (m + 1)) (Fin (m + 1)) Γ(T, ⊤)} (hb : IsUnit b.det) (x : Sp K ⟶ T) {v : Fin (m + 1) → K}
    (hv : Crd (O1 o m) (coord o m) (x ≫ p) v) :
    Crd (O1 A m) (coord A m) (x ≫ toProj c (fun i => linSec p (b i)) (iSup_nonzeroLocus_linSec p hb))
      ((b.map (valR x ⊤)).mulVec v) := by
  obtain ⟨l, u, hl, hv⟩ := (crd_iff _ _).1 hv
  have h : ⊤ ≤ x ⁻¹ᵁ p ⁻¹ᵁ chart o m l := hl
  obtain ⟨i, hi⟩ := exists_isUnit_valR_linSec x p hb h
  set g := toProj c (fun i => linSec p (b i)) (iSup_nonzeroLocus_linSec p hb) with hg
  have h₁ : ⊤ ≤ x ⁻¹ᵁ g ⁻¹ᵁ chart A m i := by
    rw [hg, toProj_preimage_chart]
    exact ((CrdCalc.isUnit_valR_iff x _ h _).1 hi).trans
      (x.preimage_mono (le_iSup (fun k => T.basicOpen ((linSec p (b i)).f k)) l))
  have h₂ : ⊤ ≤ x ⁻¹ᵁ (g ⁻¹ᵁ chart A m i ⊓ p ⁻¹ᵁ chart o m l) := fun z hz => ⟨h₁ hz, h hz⟩
  refine (crd_iff _ _).2 ⟨i, u * hi.unit, h₁, fun j => ?_⟩
  have e := congrArg (valR x _) (sec_eq_pullRatio_toProj_mul c (fun i => linSec p (b i))
    (iSup_nonzeroLocus_linSec p hb) i j l (W := g ⁻¹ᵁ chart A m i ⊓ p ⁻¹ᵁ chart o m l) inf_le_left inf_le_right)
  have r : ∀ t : (chartLB p).Sec, _ = valR x (p ⁻¹ᵁ chart o m l) (t.f l) := fun t =>
    CrdCalc.valR_res x inf_le_right h₂ (t.f l)
  replace e := (r _).symm.trans (e.trans ((CrdCalc.valR_mul x _ h₂ _ _).trans
    (congrArg₂ (· * ·) (valR_pullRatio x _ _ h₂ _) (r _))))
  have ev : v = (u : K) • fun k => valR (x ≫ p) (chart o m l) (ratio o m l k) := funext hv
  rw [ev, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, ← valR_linSec x p b h, Units.val_mul, IsUnit.unit_spec,
    _root_.mul_assoc]
  exact congrArg (_ * ·) (e.trans (mul_comm _ _))

/- English proof (translation)
Take `⟨l, c, hl, hw⟩` from `(crd_iff _ _).1 h`. Take `⟨l', c', hl', hw'⟩` from `(crd_iff _ _).1 h'`. Establish `h1 : w l = c` using `by rw [hw, valR_ratio_self x hl, mul_one]`. Establish `h2 : ⊤ ≤ x' ⁻¹ᵁ chart o m l`. Establish `hu : IsUnit (valR x' (chart o m l') (ratio o m l' l))` using `(Units.isUnit_units_mul c' _).1 ((hw' l).symm.trans h1 ▸ c.isUnit)`.

Use `((CrdCalc.isUnit_valR_iff x' _ hl' _).1 hu).trans (x'.preimage_mono ?_)` and prove the remaining obligations. Rewrite using `[ratio, basicOpen_ratioOn]`. Conclude with `inf_le_right`. Take `⟨u, hu⟩` from `CrdCalc.exists_unit_charts (O1 o m) x' l' l hl' h2`. Establish `hw'' : ∀ j, w j = (c' : K) * u * valR x' (chart o m l) (ratio o m l j)` using `fun j => by`.

Rewrite using `[hw', _root_.mul_assoc]`. Conclude with `congrArg (_ * ·) (hu (coord o m j))`. Establish `h3 : (c' : K) * u = c` using `by rw [← h1, hw'', valR_ratio_self x' h2, mul_one]`. Use `hom_ext hs fun _ => ⟨⊤, trivial, l, hl, h2, fun j => ?_⟩` and prove the remaining obligations. Establish `e` using `(hw j).symm.trans (hw'' j)`.

Rewrite `e` using `[h3, Units.mul_right_inj, CrdCalc.valR_eq x _ hl, CrdCalc.valR_eq x' _ h2]`. Conclude with `(Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.injective e`.
-/
theorem eq_of_crd {x x' : Sp K ⟶ PSpace o m} (hs : x ≫ PSpace.str o m = x' ≫ PSpace.str o m)
    {w : Fin (m + 1) → K} (h : Crd (O1 o m) (coord o m) x w) (h' : Crd (O1 o m) (coord o m) x' w) : x = x' := by
  obtain ⟨l, c, hl, hw⟩ := (crd_iff _ _).1 h
  obtain ⟨l', c', hl', hw'⟩ := (crd_iff _ _).1 h'
  have h1 : w l = c := by rw [hw, valR_ratio_self x hl, mul_one]
  have h2 : ⊤ ≤ x' ⁻¹ᵁ chart o m l := by
    have hu : IsUnit (valR x' (chart o m l') (ratio o m l' l)) :=
      (Units.isUnit_units_mul c' _).1 ((hw' l).symm.trans h1 ▸ c.isUnit)
    refine ((CrdCalc.isUnit_valR_iff x' _ hl' _).1 hu).trans (x'.preimage_mono ?_)
    rw [ratio, basicOpen_ratioOn]
    exact inf_le_right
  obtain ⟨u, hu⟩ := CrdCalc.exists_unit_charts (O1 o m) x' l' l hl' h2
  have hw'' : ∀ j, w j = (c' : K) * u * valR x' (chart o m l) (ratio o m l j) := fun j => by
    rw [hw', _root_.mul_assoc]
    exact congrArg (_ * ·) (hu (coord o m j))
  have h3 : (c' : K) * u = c := by rw [← h1, hw'', valR_ratio_self x' h2, mul_one]
  refine hom_ext hs fun _ => ⟨⊤, trivial, l, hl, h2, fun j => ?_⟩
  have e := (hw j).symm.trans (hw'' j)
  rw [h3, Units.mul_right_inj, CrdCalc.valR_eq x _ hl, CrdCalc.valR_eq x' _ h2] at e
  exact (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.injective e

/- English proof (translation)
Introduce `o _ Y Z _ s f m π h H`. Use `choose W A iA c ψ a K iK η v hy hψ hc ha hη h₁ h₂ using H`. Establish `: MorphismProperty.RespectsRight @IsImmersion @IsOpenImmersion` using `⟨fun i hi g hg => by`. Establish `: IsOpenImmersion i` using `hi`. Establish `: IsImmersion g` using `hg`.

Use the proof step `infer_instance⟩`. Establish `hj : pullback.lift π f h ≫ pullback.snd (PSpace.str o m) s = f` using `pullback.lift_snd _ _ _`. Establish `hπ : pullback.lift π f h ≫ pullback.fst (PSpace.str o m) s = π` using `pullback.lift_fst _ _ _`. Generalize the expression as in `pullback.lift π f h = j at hj hπ ⊢`. Generalize the expression as in `pullback.fst (PSpace.str o m) s = q at hπ`.

Generalize the expression as in `pullback.snd (PSpace.str o m) s = r at hj`. Substitute `hj hπ` using the available equality. Use `IsZariskiLocalAtTarget.of_range_subset_iSup (fun y => r ⁻¹ᵁ W y) ?_ fun y => ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨y, rfl⟩`. Conclude with `TopologicalSpace.Opens.mem_iSup.2 ⟨y, hy y⟩`.

Use `hψ y` as an intermediate fact. Use `hη y` as an intermediate fact. Establish `hT : (⊤ : (r ⁻¹ᵁ W y).toScheme.Opens) ≤ ((r ⁻¹ᵁ W y).ι ≫ r) ⁻¹ᵁ W y` using `(r ⁻¹ᵁ W y).ι_preimage_self.ge`. Set `b` to `(((r ⁻¹ᵁ W y).ι ≫ r).appLE (W y) ⊤ hT).hom.mapMatrix (a y)`. Establish `hb : IsUnit b.det`.

Rewrite using `[← RingHom.map_det]`. Conclude with `(ha y).map _`. Set `j' : ((j ≫ r) ⁻¹ᵁ W y).toScheme ⟶ (r ⁻¹ᵁ W y).toScheme` to `j ∣_ (r ⁻¹ᵁ W y)`. Establish `hj' : j' ≫ (r ⁻¹ᵁ W y).ι = ((j ≫ r) ⁻¹ᵁ W y).ι ≫ j` using `morphismRestrict_ι j _`. Set `g` to `toProj ((r ∣_ W y) ≫ c y) (fun i => linSec ((r ⁻¹ᵁ W y).ι ≫ q) (b i)) (iSup_nonzeroLocus_linSec _ hb)`.

Establish `hs : (j' ≫ g) ≫ PSpace.str (A y) m = ψ y ≫ PSpace.str (A y) m`. Rewrite using `[Category.assoc, toProj_str, hc, morphismRestrict_comp]`. Conclude with `(Category.assoc _ _ _).symm`. Establish `e : j' ≫ g = ψ y`. Use `ext_of_isDominant_of_isSeparated _ hs (η y) (eq_of_crd ?_ ?_ (h₂ y))` and prove the remaining obligations.

Rewrite using `[Category.assoc, hs, Category.assoc]`. Establish `k` using `crd_toProj_linSec ((r ∣_ W y) ≫ c y) ((r ⁻¹ᵁ W y).ι ≫ q) hb (η y ≫ j') (v := v y) (by`. Rewrite using `[Category.assoc, reassoc_of% hj']`. Conclude with `h₁ y)`. Establish `eb : b.map (valR (η y ≫ j') ⊤) = (a y).map (valF (η y ≫ ((j ≫ r) ⁻¹ᵁ W y).ι ≫ j ≫ r) (W y))`.

Use extensionality with `i k`. Use `(Points.valR_appLE (η y ≫ j') _ hT le_top (a y i k)).trans ?_` and prove the remaining obligations. Rewrite using `[Category.assoc, reassoc_of% hj']`. Both sides reduce to the same expression. Rewrite `k` using `[eb, Category.assoc]`.

Conclude with `k`. Establish `: IsImmersion (j' ≫ g)` using `e ▸ hψ y`. Conclude with `IsImmersion.of_comp j' g`.
-/
theorem isImmersion_lift_of_linear_change : ∀ (o : Type) [CommRing o] (Y Z : Scheme.{0}) [IsReduced Y] (s : Z ⟶ Sp o) (f : Y ⟶ Z) (m : ℕ) (π : Y ⟶ PSpace o m) (h : π ≫ PSpace.str o m = f ≫ s), (∀ y : Y, ∃ (W : Z.Opens) (A : Type) (_ : CommRing A) (c : W.toScheme ⟶ Sp A) (ψ : (f ⁻¹ᵁ W).toScheme ⟶ PSpace A m) (a : Matrix (Fin (m + 1)) (Fin (m + 1)) Γ(Z, W)) (K : Type) (_ : Field K) (η : Sp K ⟶ (f ⁻¹ᵁ W).toScheme) (v : Fin (m + 1) → K), f y ∈ W ∧ IsImmersion ψ ∧ ψ ≫ PSpace.str A m = (f ∣_ W) ≫ c ∧ IsUnit a.det ∧ IsDominant η ∧ Crd (ProjSpace.O1 o m) (ProjSpace.coord o m) (η ≫ (f ⁻¹ᵁ W).ι ≫ π) v ∧ Crd (ProjSpace.O1 A m) (ProjSpace.coord A m) (η ≫ ψ) ((a.map (valF (η ≫ (f ⁻¹ᵁ W).ι ≫ f) W)).mulVec v)) → IsImmersion (pullback.lift π f h) := by
  intro o _ Y Z _ s f m π h H
  choose W A iA c ψ a K iK η v hy hψ hc ha hη h₁ h₂ using H
  have : MorphismProperty.RespectsRight @IsImmersion @IsOpenImmersion :=
    ⟨fun i hi g hg => by
      have : IsOpenImmersion i := hi
      have : IsImmersion g := hg
      infer_instance⟩
  have hj : pullback.lift π f h ≫ pullback.snd (PSpace.str o m) s = f := pullback.lift_snd _ _ _
  have hπ : pullback.lift π f h ≫ pullback.fst (PSpace.str o m) s = π := pullback.lift_fst _ _ _
  generalize pullback.lift π f h = j at hj hπ ⊢
  generalize pullback.fst (PSpace.str o m) s = q at hπ
  generalize pullback.snd (PSpace.str o m) s = r at hj
  subst hj hπ
  refine IsZariskiLocalAtTarget.of_range_subset_iSup (fun y => r ⁻¹ᵁ W y) ?_ fun y => ?_
  · rintro _ ⟨y, rfl⟩
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨y, hy y⟩
  have := hψ y
  have := hη y
  have hT : (⊤ : (r ⁻¹ᵁ W y).toScheme.Opens) ≤ ((r ⁻¹ᵁ W y).ι ≫ r) ⁻¹ᵁ W y := (r ⁻¹ᵁ W y).ι_preimage_self.ge
  let b := (((r ⁻¹ᵁ W y).ι ≫ r).appLE (W y) ⊤ hT).hom.mapMatrix (a y)
  have hb : IsUnit b.det := by
    rw [← RingHom.map_det]
    exact (ha y).map _
  let j' : ((j ≫ r) ⁻¹ᵁ W y).toScheme ⟶ (r ⁻¹ᵁ W y).toScheme := j ∣_ (r ⁻¹ᵁ W y)
  have hj' : j' ≫ (r ⁻¹ᵁ W y).ι = ((j ≫ r) ⁻¹ᵁ W y).ι ≫ j := morphismRestrict_ι j _
  let g := toProj ((r ∣_ W y) ≫ c y) (fun i => linSec ((r ⁻¹ᵁ W y).ι ≫ q) (b i)) (iSup_nonzeroLocus_linSec _ hb)
  have hs : (j' ≫ g) ≫ PSpace.str (A y) m = ψ y ≫ PSpace.str (A y) m := by
    rw [Category.assoc, toProj_str, hc, morphismRestrict_comp]
    exact (Category.assoc _ _ _).symm
  have e : j' ≫ g = ψ y := by
    refine ext_of_isDominant_of_isSeparated _ hs (η y) (eq_of_crd ?_ ?_ (h₂ y))
    · rw [Category.assoc, hs, Category.assoc]
    · have k := crd_toProj_linSec ((r ∣_ W y) ≫ c y) ((r ⁻¹ᵁ W y).ι ≫ q) hb (η y ≫ j') (v := v y) (by
        rw [Category.assoc, reassoc_of% hj']
        exact h₁ y)
      have eb : b.map (valR (η y ≫ j') ⊤) = (a y).map (valF (η y ≫ ((j ≫ r) ⁻¹ᵁ W y).ι ≫ j ≫ r) (W y)) := by
        ext i k
        refine (Points.valR_appLE (η y ≫ j') _ hT le_top (a y i k)).trans ?_
        rw [Category.assoc, reassoc_of% hj']
        rfl
      rw [eb, Category.assoc] at k
      exact k
  have : IsImmersion (j' ≫ g) := e ▸ hψ y
  exact IsImmersion.of_comp j' g

end GlobalTheory.ZH.LinFrame
end
