import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.LocTheta
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnitCharts
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsInvertibleMatrixChangeOfSpanEqStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLineBundleSectionsOfUnimodularTuplesStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsAffineOpenOfLocalSectionCombinationLocusStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.ZH.SecCoord
open GlobalTheory.Points Matrix

section General
variable {X Y : Scheme.{0}}

/- English proof (translation)
Establish `key : ∀ (K : Type) [Field K] (y : Sp K ⟶ X), y (IsLocalRing.closedPoint K) = p → ∀ U : X.Opens, ⊤ ≤ y ⁻¹ᵁ U ↔ p ∈ U` using `fun K _ y e U => (le_preimage_iff y U).trans (by rw [e])`. Conclude with `⟨X.residueField p, inferInstance, X.fromSpecResidueField p, X.fromSpecResidueField_apply p _, key _ _ (X.fromSpecResidueField_apply p _)⟩`.
-/
theorem exists_pt (p : X) : ∃ (K : Type) (_ : Field K) (y : Sp K ⟶ X), y (IsLocalRing.closedPoint K) = p ∧
    ∀ U : X.Opens, ⊤ ≤ y ⁻¹ᵁ U ↔ p ∈ U := by
  have key : ∀ (K : Type) [Field K] (y : Sp K ⟶ X), y (IsLocalRing.closedPoint K) = p →
      ∀ U : X.Opens, ⊤ ≤ y ⁻¹ᵁ U ↔ p ∈ U := fun K _ y e U => (le_preimage_iff y U).trans (by rw [e])
  exact ⟨X.residueField p, inferInstance, X.fromSpecResidueField p, X.fromSpecResidueField_apply p _,
    key _ _ (X.fromSpecResidueField_apply p _)⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨IsOpenImmersion.lift U.ι y (by rw [Scheme.Opens.range_ι]; exact (top_le_preimage_iff y U).1 h), IsOpenImmersion.lift_fac _ _ _⟩`.
-/
theorem exists_lift {R : Type} [CommRing R] (y : Sp R ⟶ X) (U : X.Opens) (h : ⊤ ≤ y ⁻¹ᵁ U) :
    ∃ y' : Sp R ⟶ U.toScheme, y' ≫ U.ι = y :=
  ⟨IsOpenImmersion.lift U.ι y (by rw [Scheme.Opens.range_ι]; exact (top_le_preimage_iff y U).1 h),
    IsOpenImmersion.lift_fac _ _ _⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨l, 1, h, fun j => by simp⟩`.
-/
theorem crd_chart {H : LB X} {J : Type} (s : J → H.Sec) {R : Type} [CommRing R] (x : Sp R ⟶ X) (l : H.ι)
    (h : ⊤ ≤ x ⁻¹ᵁ H.U l) : Crd H s x (fun j => valR x (H.U l) ((s j).f l)) :=
  ⟨l, 1, h, fun j => by simp⟩

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨l, c, hl, hv⟩`. Use `⟨l ⟨⟩, c, le_preimage_comp x f (LB.wchart_le H (fun _ : PUnit => f) l ⟨⟩) hl, fun j => ?_⟩` and prove the remaining obligations. Rewrite using `[hv]`. Conclude with `congrArg _ (valR_appLE x f _ hl _)`.

Introduce and unpack `⟨l, c, hl, hv⟩`. Establish `h : ⊤ ≤ x ⁻¹ᵁ (H.pull f).U (fun _ => l)` using `fun z hz => Set.mem_iInter.2 fun _ => hl hz`. Use `⟨fun _ => l, c, h, fun j => ?_⟩` and prove the remaining obligations. Rewrite using `[hv]`. Conclude with `congrArg _ (valR_appLE x f _ h _).symm`.
-/
theorem crd_secPull {H : LB X} {J : Type} (s : J → H.Sec) (f : Y ⟶ X) {R : Type} [CommRing R] (x : Sp R ⟶ Y)
    (v : J → R) : Crd (H.pull f) (fun j => GlobalTheory.secPull (s j) f) x v ↔ Crd H s (x ≫ f) v := by
  constructor
  · rintro ⟨l, c, hl, hv⟩
    refine ⟨l ⟨⟩, c, le_preimage_comp x f (LB.wchart_le H (fun _ : PUnit => f) l ⟨⟩) hl, fun j => ?_⟩
    rw [hv]
    exact congrArg _ (valR_appLE x f _ hl _)
  · rintro ⟨l, c, hl, hv⟩
    have h : ⊤ ≤ x ⁻¹ᵁ (H.pull f).U (fun _ => l) := fun z hz => Set.mem_iInter.2 fun _ => hl hz
    refine ⟨fun _ => l, c, h, fun j => ?_⟩
    rw [hv]
    exact congrArg _ (valR_appLE x f _ h _).symm

/- English proof (translation)
Take `⟨i, hi⟩` from `exists_le_preimage_of_iSup_eq_top x hs`. Conclude with `fun h0 => ((CrdCalc.crd_isUnit_iff i h).2 hi).ne_zero (congrFun h0 i)`.
-/
theorem crd_ne_zero {H : LB X} {J : Type} {s : J → H.Sec} (hs : ⨆ i, nonzeroLocus (s i) = ⊤) {K : Type} [Field K]
    {x : Sp K ⟶ X} {v : J → K} (h : Crd H s x v) : v ≠ 0 := by
  obtain ⟨i, hi⟩ := exists_le_preimage_of_iSup_eq_top x hs
  exact fun h0 => ((CrdCalc.crd_isUnit_iff i h).2 hi).ne_zero (congrFun h0 i)

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Establish `h0 : X.basicOpen (f - g) ≠ ⊥` using `fun e => hne (sub_eq_zero.1 ((basicOpen_eq_bot_iff _).1 e))`. Take `⟨p, hp⟩ : ((X.basicOpen (f - g) : X.Opens) : Set X).Nonempty` from `Set.nonempty_iff_ne_empty.2 fun e => h0 (SetLike.coe_injective e)`. Establish `h1` using `(hy _).2 ((genericPoint_specializes p).mem_open (X.basicOpen (f - g)).isOpen hp)`. Establish `h2` using `le_preimage_mono y (X.basicOpen_le _) h1`.

Establish `h3` using `(le_preimage_basicOpen_iff y h2 _).1 h1`. Establish `h4` using `h h2`. Rewrite `h4` using `[valR_eq y N h2, valR_eq y N h2]`. Rewrite `h3` using `[valR_eq y N h2, map_sub, h4, sub_self]`. Conclude with `not_isUnit_zero h3`.
-/
theorem eq_of_valR_generic [IsIntegral X] {K : Type} [Field K] (y : Sp K ⟶ X)
    (hy : ∀ U : X.Opens, ⊤ ≤ y ⁻¹ᵁ U ↔ genericPoint X ∈ U) {N : X.Opens} (f g : Γ(X, N))
    (h : ⊤ ≤ y ⁻¹ᵁ N → valR y N f = valR y N g) : f = g := by
  by_contra hne
  have h0 : X.basicOpen (f - g) ≠ ⊥ := fun e => hne (sub_eq_zero.1 ((basicOpen_eq_bot_iff _).1 e))
  obtain ⟨p, hp⟩ : ((X.basicOpen (f - g) : X.Opens) : Set X).Nonempty :=
    Set.nonempty_iff_ne_empty.2 fun e => h0 (SetLike.coe_injective e)
  have h1 := (hy _).2 ((genericPoint_specializes p).mem_open (X.basicOpen (f - g)).isOpen hp)
  have h2 := le_preimage_mono y (X.basicOpen_le _) h1
  have h3 := (le_preimage_basicOpen_iff y h2 _).1 h1
  have h4 := h h2
  rw [valR_eq y N h2, valR_eq y N h2] at h4
  rw [valR_eq y N h2, map_sub, h4, sub_self] at h3
  exact not_isUnit_zero h3

/- English proof (translation)
Establish `: valR x U = (valMap x U h).hom` using `funext (valR_eq x U h)`. Rewrite using `[this]`. Conclude with `(IsUnit.of_mul_eq_one m' e).map (valMap x U h).hom.mapMatrix`.
-/
theorem isUnit_map_valR {J : Type} [Fintype J] [DecidableEq J] {R : Type} [CommRing R] (x : Sp R ⟶ X) {U : X.Opens}
    (h : ⊤ ≤ x ⁻¹ᵁ U) {m m' : Matrix J J Γ(X, U)} (e : m * m' = 1) : IsUnit (m.map (valR x U)) := by
  have : valR x U = (valMap x U h).hom := funext (valR_eq x U h)
  rw [this]
  exact (IsUnit.of_mul_eq_one m' e).map (valMap x U h).hom.mapMatrix

end General

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} {ρ : S.Real} {M : RatModel o Ω}
  {U₀ : M.Z.Opens} {EE : M.Lat S.J}

/- English proof (translation)
Use `⟨(RatModel.valLoc y _ h).comp ((RingHom.id Ω).codRestrict (M.O (genericPoint M.Z)) fun x => by rw [M.O_genericPoint]; trivial), fun U hU f => ?_⟩` and prove the remaining obligations. Conclude with `(RatModel.valLoc_valF y h ((genericPoint_specializes hU.some).mem_open U.isOpen hU.some_mem) f).symm`.
-/
theorem exists_hom_generic {K : Type} [Field K] (y : Sp K ⟶ M.Z)
    (h : y (IsLocalRing.closedPoint K) ⤳ genericPoint M.Z) :
    ∃ β : Ω →+* K, ∀ U : M.Z.Opens, (U : Set M.Z).Nonempty → ∀ f, valR y U f = β (valF M.pt U f) := by
  refine ⟨(RatModel.valLoc y _ h).comp ((RingHom.id Ω).codRestrict (M.O (genericPoint M.Z))
    fun x => by rw [M.O_genericPoint]; trivial), fun U hU f => ?_⟩
  exact (RatModel.valLoc_valF y h ((genericPoint_specializes hU.some).mem_open U.isOpen hU.some_mem) f).symm

/- English proof (translation)
Take `⟨u, hu⟩` from `CrdCalc.crd_unique hv (Q.rel l K y w hw)`. Use `⟨u, ?_⟩` and prove the remaining obligations. Establish `e1 : m.map (valR (y ≫ (Q.P.hom ⁻¹ᵁ Q.W l).ι ≫ Q.P.hom) (W ⊓ Q.W l)) = (m.map (valF M.pt (W ⊓ Q.W l))).map β`. Use extensionality with `i j`. Conclude with `hβ _ hne _`.

Establish `e2 : (Q.c l).map (valR (y ≫ (Q.P.hom ⁻¹ᵁ Q.W l).ι ≫ Q.P.hom) (Q.W l)) = ((Q.c l).map (valF M.pt (Q.W l))).map β`. Use extensionality with `i j`. Conclude with `hβ _ (Q.ne l) _`. Establish `e3 : (Q.c l).map (valR (y ≫ (Q.P.hom ⁻¹ᵁ Q.W l).ι ≫ Q.P.hom) (Q.W l)) *ᵥ w = (u : K) • v` using `funext hu`. Rewrite using `[e1, hm, Matrix.map_mul, ← e2, ← Matrix.mulVec_mulVec, e3, Matrix.mulVec_smul]`.
-/
theorem exists_unit_generic (Q : Clos ρ M U₀ EE) (l : Q.Λ) {W : M.Z.Opens} {b : Matrix S.J S.J Ω}
    {m : Matrix S.J S.J Γ(M.Z, W ⊓ Q.W l)} (hne : ((W ⊓ Q.W l : M.Z.Opens) : Set M.Z).Nonempty)
    (hm : m.map (valF M.pt (W ⊓ Q.W l)) = b * (Q.c l).map (valF M.pt (Q.W l)))
    {K : Type} [Field K] (y : Sp K ⟶ (Q.P.hom ⁻¹ᵁ Q.W l).toScheme) (β : Ω →+* K)
    (hβ : ∀ U : M.Z.Opens, (U : Set M.Z).Nonempty → ∀ f,
      valR (y ≫ (Q.P.hom ⁻¹ᵁ Q.W l).ι ≫ Q.P.hom) U f = β (valF M.pt U f))
    {w v : S.J → K} (hw : Crd (Q.O1.pull (Q.P.hom ⁻¹ᵁ Q.W l).ι) (Q.σ l) y w)
    (hv : Crd Q.O1 Q.st (y ≫ (Q.P.hom ⁻¹ᵁ Q.W l).ι) v) :
    ∃ u : Kˣ, (m.map (valR (y ≫ (Q.P.hom ⁻¹ᵁ Q.W l).ι ≫ Q.P.hom) (W ⊓ Q.W l))) *ᵥ w =
      (u : K) • (b.map β *ᵥ v) := by
  obtain ⟨u, hu⟩ := CrdCalc.crd_unique hv (Q.rel l K y w hw)
  refine ⟨u, ?_⟩
  have e1 : m.map (valR (y ≫ (Q.P.hom ⁻¹ᵁ Q.W l).ι ≫ Q.P.hom) (W ⊓ Q.W l)) =
      (m.map (valF M.pt (W ⊓ Q.W l))).map β := by
    ext i j
    exact hβ _ hne _
  have e2 : (Q.c l).map (valR (y ≫ (Q.P.hom ⁻¹ᵁ Q.W l).ι ≫ Q.P.hom) (Q.W l)) =
      ((Q.c l).map (valF M.pt (Q.W l))).map β := by
    ext i j
    exact hβ _ (Q.ne l) _
  have e3 : (Q.c l).map (valR (y ≫ (Q.P.hom ⁻¹ᵁ Q.W l).ι ≫ Q.P.hom) (Q.W l)) *ᵥ w = (u : K) • v := funext hu
  rw [e1, hm, Matrix.map_mul, ← e2, ← Matrix.mulVec_mulVec, e3, Matrix.mulVec_smul]

/- English proof (translation)
Set `jj : ∀ l, (Q.P.hom ⁻¹ᵁ Q.W l).toScheme ⟶ Q.P.left` to `fun l => (Q.P.hom ⁻¹ᵁ Q.W l).ι`. Set `H : ∀ l, LB (Q.P.hom ⁻¹ᵁ Q.W l).toScheme` to `fun l => Q.O1.pull (jj l)`. Set `A : Type` to `Σ l, (H l).ι`. Set `V : A → Q.P.left.Opens` to `fun a => jj a.1 ''ᵁ (H a.1).U a.2 ⊓ Q.P.hom ⁻¹ᵁ W`. Establish `le0 : ∀ a : A, jj a.1 ''ᵁ (H a.1).U a.2 ≤ Q.P.hom ⁻¹ᵁ Q.W a.1`.

Introduce and unpack `a _ ⟨x, -, rfl⟩`. Conclude with `x.2`. Establish `le1 : ∀ a : A, V a ≤ Q.P.hom ⁻¹ᵁ (W ⊓ Q.W a.1)` using `fun a x hx => ⟨hx.2, le0 a hx.1⟩`. Set `t : ∀ a : A, S.J → Γ(Q.P.left, V a)` to `fun a i => ∑ k, (Q.P.hom.appLE (W ⊓ Q.W a.1) (V a) (le1 a)).hom (m a.1 i k) * resG Q.P.left inf_le_left (((jj a.1).appIso ((H a.1).U a.2)).inv.hom ((Q.σ a.1 k).f a.2))`. Establish `hin : ∀ (a : A) (K : Type) [Field K] (y : Sp K ⟶ (Q.P.hom ⁻¹ᵁ Q.W a.1).toScheme), ⊤ ≤ (y ≫ jj a.1) ⁻¹ᵁ V a → ⊤ ≤ y ⁻¹ᵁ (H a.1).U a.2` using `fun a K _ y h => le_preimage_mono y ((jj a.1).preimage_image_eq _).le (le_preimage_mono (y ≫ jj a.1) inf_le_left h)`.

Establish `hval : ∀ (a : A) (K : Type) [Field K] (y : Sp K ⟶ (Q.P.hom ⁻¹ᵁ Q.W a.1).toScheme), ⊤ ≤ (y ≫ jj a.1) ⁻¹ᵁ V a → (fun i => valR (y ≫ jj a.1) (V a) (t a i)) = (m a.1).map (valR (y ≫ jj a.1 ≫ Q.P.hom) (W ⊓ Q.W a.1)) *ᵥ fun k => valR y ((H a.1).U a.2) ((Q.σ a.1 k).f a.2)`. Introduce `a K _ y h`. Use function extensionality and compare the values at `i`. Establish `hy` using `hin a K y h`. Rewrite using `[valR_eq _ _ h]`.

Use `(map_sum _ _ _).trans (Finset.sum_congr rfl fun k _ => ?_)` and prove the remaining obligations. Rewrite using `[map_mul, ← valR_eq _ _ h, ← valR_eq _ _ h]`. Use `congrArg₂ (fun a b : K => a * b) ?_ ?_` and prove the remaining obligations. Rewrite using `[valR_appLE _ _ _ h, Category.assoc]`. Both sides reduce to the same expression.

Rewrite using `[valR_res _ _ h, ← valR_appLE y (jj a.1) ((jj a.1).preimage_image_eq _).ge hy, ← CommRingCat.comp_apply, Scheme.Hom.appIso_inv_appLE]`. Conclude with `valR_res y le_rfl hy _`. Establish `hne : ∀ (a : A) (K : Type) [Field K] (y : Sp K ⟶ Q.P.left), ⊤ ≤ y ⁻¹ᵁ V a → ((W ⊓ Q.W a.1 : M.Z.Opens) : Set M.Z).Nonempty` using `fun a K _ y h => ⟨_, le1 a (h (x := IsLocalRing.closedPoint K) trivial)⟩`. Take `⟨g, T, hT⟩` from `GlobalTheory.T.exists_lineBundle_sections_of_unimodular_tuples Q.P.left A S.J V t (fun a p hp => by`. Take `⟨K, _, y, -, hy⟩` from `exists_pt p`.

Take `⟨y, rfl⟩` from `exists_lift y _ ((hy _).2 (le0 a hp.1))`. Establish `h` using `(hy _).2 hp`. Take `⟨m', hm'⟩` from `hu a.1`. Establish `h1` using `isUnit_map_valR (y ≫ jj a.1 ≫ Q.P.hom) (le_preimage_comp (y ≫ jj a.1) Q.P.hom (le1 a) h) hm'`. Establish `h2` using `crd_ne_zero (by simpa using (Q.imm a.1).1) (crd_chart (Q.σ a.1) y a.2 (hin a K y h))`.

Establish `h3 : (fun i => valR (y ≫ jj a.1) (V a) (t a i)) ≠ 0`. Rewrite using `[hval a K y h]`. Conclude with `fun e => h2 ((Matrix.mulVec_injective_of_isUnit h1) (e.trans (Matrix.mulVec_zero _).symm))`. Take `⟨i, hi⟩` from `Function.ne_iff.1 h3`. Conclude with `TopologicalSpace.Opens.mem_iSup.2 ⟨i, (hy _).1 ((le_preimage_basicOpen_iff _ h _).2 (Ne.isUnit hi))⟩) (fun a a' i j => by`.

Take `⟨K, _, y, e, hy⟩` from `exists_pt (genericPoint Q.P.left)`. Use `eq_of_valR_generic y hy _ _ fun h => ?_` and prove the remaining obligations. Take `⟨β, hβ⟩` from `exists_hom_generic (y ≫ Q.P.hom) (by`. Take `⟨p, hp⟩` from `hs (genericPoint M.Z)`. Rewrite using `[← hp]`.

Conclude with `(congrArg (fun q => Q.P.hom q ⤳ Q.P.hom p) e).mpr ((genericPoint_specializes p).map Q.P.hom.continuous))`. Take `⟨v, hv⟩` from `CrdCalc.crd_exists Q.isLB Q.st y`. Establish `key : ∀ a : A, ⊤ ≤ y ⁻¹ᵁ V a → ∃ u : K, ∀ i, valR y (V a) (t a i) = u * (b.map β *ᵥ v) i`. Introduce `a h`. Take `⟨y, rfl⟩` from `exists_lift y _ (le_preimage_mono y (inf_le_left.trans (le0 a)) h)`.

Take `⟨u, hu⟩` from `exists_unit_generic Q a.1 (hne a K _ h) (hm _ (hne a K _ h)) y β (by simpa only [Category.assoc] using hβ) (crd_chart (Q.σ a.1) y a.2 (hin a K y h)) hv`. Conclude with `⟨u, fun i => congrFun ((hval a K y h).trans hu) i⟩`. Take `⟨u, hu⟩` from `key a (le_preimage_mono y inf_le_left h)`. Take `⟨u', hu'⟩` from `key a' (le_preimage_mono y inf_le_right h)`. Rewrite using `[valR_mul _ _ h, valR_mul _ _ h, valR_res _ _ h, valR_res _ _ h, valR_res _ _ h, valR_res _ _ h, hu, hu, hu', hu']`.

Use the proof step `ring)`. Use `⟨⟨A, V, g⟩, T, fun i => iSup_le fun a => (Q.P.left.basicOpen_le _).trans inf_le_right, ?_⟩` and prove the remaining obligations. Introduce and unpack `l K _ y w hW ⟨j, c, hj, hw⟩`. Establish `h : ⊤ ≤ (y ≫ jj l) ⁻¹ᵁ V ⟨l, j⟩` using `fun z hz => ⟨⟨y z, hj hz, rfl⟩, hW hz⟩`. Use `⟨⟨l, j⟩, c, h, fun i => ?_⟩` and prove the remaining obligations.

Establish `e : w = (c : K) • fun k => valR y ((H l).U j) ((Q.σ l k).f j)` using `funext hw`. Rewrite using `[hT, e, Matrix.mulVec_smul]`. Conclude with `congrArg ((c : K) * ·) (congrFun (hval ⟨l, j⟩ K y h) i).symm`.
-/
theorem exists_bundle (Q : Clos ρ M U₀ EE) (hs : Function.Surjective Q.P.hom) (W : M.Z.Opens)
    (b : Matrix S.J S.J Ω) (m : ∀ l, Matrix S.J S.J Γ(M.Z, W ⊓ Q.W l)) (hu : ∀ l, ∃ m', m l * m' = 1)
    (hm : ∀ l, ((W ⊓ Q.W l : M.Z.Opens) : Set M.Z).Nonempty →
      (m l).map (valF M.pt (W ⊓ Q.W l)) = b * (Q.c l).map (valF M.pt (Q.W l))) :
    ∃ (L : LB Q.P.left) (T : S.J → L.Sec), (∀ i, nonzeroLocus (T i) ≤ Q.P.hom ⁻¹ᵁ W) ∧
      ∀ l (K : Type) [Field K] (y : Sp K ⟶ (Q.P.hom ⁻¹ᵁ Q.W l).toScheme) (w : S.J → K),
        ⊤ ≤ (y ≫ (Q.P.hom ⁻¹ᵁ Q.W l).ι ≫ Q.P.hom) ⁻¹ᵁ W → Crd (Q.O1.pull (Q.P.hom ⁻¹ᵁ Q.W l).ι) (Q.σ l) y w →
        Crd L T (y ≫ (Q.P.hom ⁻¹ᵁ Q.W l).ι)
          ((m l).map (valR (y ≫ (Q.P.hom ⁻¹ᵁ Q.W l).ι ≫ Q.P.hom) (W ⊓ Q.W l)) *ᵥ w) := by
  let jj : ∀ l, (Q.P.hom ⁻¹ᵁ Q.W l).toScheme ⟶ Q.P.left := fun l => (Q.P.hom ⁻¹ᵁ Q.W l).ι
  let H : ∀ l, LB (Q.P.hom ⁻¹ᵁ Q.W l).toScheme := fun l => Q.O1.pull (jj l)
  let A : Type := Σ l, (H l).ι
  let V : A → Q.P.left.Opens := fun a => jj a.1 ''ᵁ (H a.1).U a.2 ⊓ Q.P.hom ⁻¹ᵁ W
  have le0 : ∀ a : A, jj a.1 ''ᵁ (H a.1).U a.2 ≤ Q.P.hom ⁻¹ᵁ Q.W a.1 := by
    rintro a _ ⟨x, -, rfl⟩
    exact x.2
  have le1 : ∀ a : A, V a ≤ Q.P.hom ⁻¹ᵁ (W ⊓ Q.W a.1) := fun a x hx => ⟨hx.2, le0 a hx.1⟩
  let t : ∀ a : A, S.J → Γ(Q.P.left, V a) := fun a i =>
    ∑ k, (Q.P.hom.appLE (W ⊓ Q.W a.1) (V a) (le1 a)).hom (m a.1 i k) *
      resG Q.P.left inf_le_left (((jj a.1).appIso ((H a.1).U a.2)).inv.hom ((Q.σ a.1 k).f a.2))
  have hin : ∀ (a : A) (K : Type) [Field K] (y : Sp K ⟶ (Q.P.hom ⁻¹ᵁ Q.W a.1).toScheme),
      ⊤ ≤ (y ≫ jj a.1) ⁻¹ᵁ V a → ⊤ ≤ y ⁻¹ᵁ (H a.1).U a.2 := fun a K _ y h =>
    le_preimage_mono y ((jj a.1).preimage_image_eq _).le (le_preimage_mono (y ≫ jj a.1) inf_le_left h)
  have hval : ∀ (a : A) (K : Type) [Field K] (y : Sp K ⟶ (Q.P.hom ⁻¹ᵁ Q.W a.1).toScheme),
      ⊤ ≤ (y ≫ jj a.1) ⁻¹ᵁ V a → (fun i => valR (y ≫ jj a.1) (V a) (t a i)) =
        (m a.1).map (valR (y ≫ jj a.1 ≫ Q.P.hom) (W ⊓ Q.W a.1)) *ᵥ
          fun k => valR y ((H a.1).U a.2) ((Q.σ a.1 k).f a.2) := by
    intro a K _ y h
    funext i
    have hy := hin a K y h
    rw [valR_eq _ _ h]
    refine (map_sum _ _ _).trans (Finset.sum_congr rfl fun k _ => ?_)
    rw [map_mul, ← valR_eq _ _ h, ← valR_eq _ _ h]
    refine congrArg₂ (fun a b : K => a * b) ?_ ?_
    · rw [valR_appLE _ _ _ h, Category.assoc]
      rfl
    · rw [valR_res _ _ h, ← valR_appLE y (jj a.1) ((jj a.1).preimage_image_eq _).ge hy, ← CommRingCat.comp_apply,
        Scheme.Hom.appIso_inv_appLE]
      exact valR_res y le_rfl hy _
  have hne : ∀ (a : A) (K : Type) [Field K] (y : Sp K ⟶ Q.P.left), ⊤ ≤ y ⁻¹ᵁ V a →
      ((W ⊓ Q.W a.1 : M.Z.Opens) : Set M.Z).Nonempty := fun a K _ y h =>
    ⟨_, le1 a (h (x := IsLocalRing.closedPoint K) trivial)⟩
  obtain ⟨g, T, hT⟩ := GlobalTheory.T.exists_lineBundle_sections_of_unimodular_tuples Q.P.left A S.J V t (fun a p hp => by
    obtain ⟨K, _, y, -, hy⟩ := exists_pt p
    obtain ⟨y, rfl⟩ := exists_lift y _ ((hy _).2 (le0 a hp.1))
    have h := (hy _).2 hp
    obtain ⟨m', hm'⟩ := hu a.1
    have h1 := isUnit_map_valR (y ≫ jj a.1 ≫ Q.P.hom) (le_preimage_comp (y ≫ jj a.1) Q.P.hom (le1 a) h) hm'
    have h2 := crd_ne_zero (by simpa using (Q.imm a.1).1) (crd_chart (Q.σ a.1) y a.2 (hin a K y h))
    have h3 : (fun i => valR (y ≫ jj a.1) (V a) (t a i)) ≠ 0 := by
      rw [hval a K y h]
      exact fun e => h2 ((Matrix.mulVec_injective_of_isUnit h1) (e.trans (Matrix.mulVec_zero _).symm))
    obtain ⟨i, hi⟩ := Function.ne_iff.1 h3
    exact TopologicalSpace.Opens.mem_iSup.2
      ⟨i, (hy _).1 ((le_preimage_basicOpen_iff _ h _).2 (Ne.isUnit hi))⟩) (fun a a' i j => by
    obtain ⟨K, _, y, e, hy⟩ := exists_pt (genericPoint Q.P.left)
    refine eq_of_valR_generic y hy _ _ fun h => ?_
    obtain ⟨β, hβ⟩ := exists_hom_generic (y ≫ Q.P.hom) (by
      obtain ⟨p, hp⟩ := hs (genericPoint M.Z)
      rw [← hp]
      exact (congrArg (fun q => Q.P.hom q ⤳ Q.P.hom p) e).mpr
        ((genericPoint_specializes p).map Q.P.hom.continuous))
    obtain ⟨v, hv⟩ := CrdCalc.crd_exists Q.isLB Q.st y
    have key : ∀ a : A, ⊤ ≤ y ⁻¹ᵁ V a → ∃ u : K, ∀ i, valR y (V a) (t a i) = u * (b.map β *ᵥ v) i := by
      intro a h
      obtain ⟨y, rfl⟩ := exists_lift y _ (le_preimage_mono y (inf_le_left.trans (le0 a)) h)
      obtain ⟨u, hu⟩ := exists_unit_generic Q a.1 (hne a K _ h) (hm _ (hne a K _ h)) y β
        (by simpa only [Category.assoc] using hβ) (crd_chart (Q.σ a.1) y a.2 (hin a K y h)) hv
      exact ⟨u, fun i => congrFun ((hval a K y h).trans hu) i⟩
    obtain ⟨u, hu⟩ := key a (le_preimage_mono y inf_le_left h)
    obtain ⟨u', hu'⟩ := key a' (le_preimage_mono y inf_le_right h)
    rw [valR_mul _ _ h, valR_mul _ _ h, valR_res _ _ h, valR_res _ _ h, valR_res _ _ h, valR_res _ _ h,
      hu, hu, hu', hu']
    ring)
  refine ⟨⟨A, V, g⟩, T, fun i => iSup_le fun a => (Q.P.left.basicOpen_le _).trans inf_le_right, ?_⟩
  rintro l K _ y w hW ⟨j, c, hj, hw⟩
  have h : ⊤ ≤ (y ≫ jj l) ⁻¹ᵁ V ⟨l, j⟩ := fun z hz => ⟨⟨y z, hj hz, rfl⟩, hW hz⟩
  refine ⟨⟨l, j⟩, c, h, fun i => ?_⟩
  have e : w = (c : K) • fun k => valR y ((H l).U j) ((Q.σ l k).f j) := funext hw
  rw [hT, e, Matrix.mulVec_smul]
  exact congrArg ((c : K) * ·) (congrFun (hval ⟨l, j⟩ K y h) i).symm

/- English proof (translation)
Establish `hσ : ∀ l, ⨆ i, nonzeroLocus (Q.σ l i) = ⊤` using `fun l => by simpa using (Q.imm l).1`. Use `⟨fun p hp => ?_, fun i => ?_⟩` and prove the remaining obligations. Take `⟨K, _, y, -, hy⟩` from `exists_pt p`. Take `⟨l, hl⟩` from `exists_le_preimage_of_iSup_eq_top (y ≫ Q.P.hom) Q.cover`. Take `⟨y, rfl⟩` from `exists_lift y (Q.P.hom ⁻¹ᵁ Q.W l) hl`.

Establish `h : ⊤ ≤ (y ≫ (Q.P.hom ⁻¹ᵁ Q.W l).ι ≫ Q.P.hom) ⁻¹ᵁ W` using `(hy _).2 hp`. Take `⟨w, hw⟩` from `CrdCalc.crd_exists (LB.isLB_pull Q.isLB _) (Q.σ l) y`. Take `⟨m', hm'⟩` from `hu l`. Establish `h1` using `isUnit_map_valR (y ≫ (Q.P.hom ⁻¹ᵁ Q.W l).ι ≫ Q.P.hom) (U := W ⊓ Q.W l) (fun z hz => ⟨h hz, hl hz⟩) hm'`. Establish `h3 : (m l).map (valR (y ≫ (Q.P.hom ⁻¹ᵁ Q.W l).ι ≫ Q.P.hom) (W ⊓ Q.W l)) *ᵥ w ≠ 0` using `fun e => crd_ne_zero (hσ l) hw ((Matrix.mulVec_injective_of_isUnit h1) (e.trans (Matrix.mulVec_zero _).symm))`.

Take `⟨i, hi⟩` from `Function.ne_iff.1 h3`. Conclude with `TopologicalSpace.Opens.mem_iSup.2 ⟨i, (hy _).1 ((CrdCalc.crd_isUnit_iff i (hT l K y w h hw)).1 (Ne.isUnit hi))⟩`. Use `Q.proper` as an intermediate fact. Use `GlobalTheory.T.isAffineOpen_of_local_sectionCombination_locus Q.P.left M.Z Q.P.hom S.J _ W hW (hle i) fun z _ => ?_` and prove the remaining obligations. Take `⟨l, hl⟩` from `TopologicalSpace.Opens.mem_iSup.1 (Q.cover.ge (Set.mem_univ z))`.

Use `⟨Q.W l, _, Q.σ l, m l i, hl, Q.aff l, hσ l, fun k => ((Q.imm l).2 k trivial).1, fun K _ y w h hw => ?_⟩` and prove the remaining obligations. Conclude with `(CrdCalc.crd_isUnit_iff i (hT l K y w h hw)).symm.trans isUnit_iff_ne_zero`.
-/
theorem cover_affine (Q : Clos ρ M U₀ EE) {W : M.Z.Opens} (hW : IsAffineOpen W)
    (m : ∀ l, Matrix S.J S.J Γ(M.Z, W ⊓ Q.W l)) (hu : ∀ l, ∃ m', m l * m' = 1)
    {L : LB Q.P.left} {T : S.J → L.Sec} (hle : ∀ i, nonzeroLocus (T i) ≤ Q.P.hom ⁻¹ᵁ W)
    (hT : ∀ l (K : Type) [Field K] (y : Sp K ⟶ (Q.P.hom ⁻¹ᵁ Q.W l).toScheme) (w : S.J → K),
        ⊤ ≤ (y ≫ (Q.P.hom ⁻¹ᵁ Q.W l).ι ≫ Q.P.hom) ⁻¹ᵁ W → Crd (Q.O1.pull (Q.P.hom ⁻¹ᵁ Q.W l).ι) (Q.σ l) y w →
        Crd L T (y ≫ (Q.P.hom ⁻¹ᵁ Q.W l).ι)
          ((m l).map (valR (y ≫ (Q.P.hom ⁻¹ᵁ Q.W l).ι ≫ Q.P.hom) (W ⊓ Q.W l)) *ᵥ w)) :
    Q.P.hom ⁻¹ᵁ W ≤ ⨆ i, nonzeroLocus (T i) ∧ ∀ i, IsAffineOpen (nonzeroLocus (T i)) := by
  have hσ : ∀ l, ⨆ i, nonzeroLocus (Q.σ l i) = ⊤ := fun l => by simpa using (Q.imm l).1
  refine ⟨fun p hp => ?_, fun i => ?_⟩
  · obtain ⟨K, _, y, -, hy⟩ := exists_pt p
    obtain ⟨l, hl⟩ := exists_le_preimage_of_iSup_eq_top (y ≫ Q.P.hom) Q.cover
    obtain ⟨y, rfl⟩ := exists_lift y (Q.P.hom ⁻¹ᵁ Q.W l) hl
    have h : ⊤ ≤ (y ≫ (Q.P.hom ⁻¹ᵁ Q.W l).ι ≫ Q.P.hom) ⁻¹ᵁ W := (hy _).2 hp
    obtain ⟨w, hw⟩ := CrdCalc.crd_exists (LB.isLB_pull Q.isLB _) (Q.σ l) y
    obtain ⟨m', hm'⟩ := hu l
    have h1 := isUnit_map_valR (y ≫ (Q.P.hom ⁻¹ᵁ Q.W l).ι ≫ Q.P.hom) (U := W ⊓ Q.W l)
      (fun z hz => ⟨h hz, hl hz⟩) hm'
    have h3 : (m l).map (valR (y ≫ (Q.P.hom ⁻¹ᵁ Q.W l).ι ≫ Q.P.hom) (W ⊓ Q.W l)) *ᵥ w ≠ 0 := fun e =>
      crd_ne_zero (hσ l) hw ((Matrix.mulVec_injective_of_isUnit h1) (e.trans (Matrix.mulVec_zero _).symm))
    obtain ⟨i, hi⟩ := Function.ne_iff.1 h3
    exact TopologicalSpace.Opens.mem_iSup.2
      ⟨i, (hy _).1 ((CrdCalc.crd_isUnit_iff i (hT l K y w h hw)).1 (Ne.isUnit hi))⟩
  · have := Q.proper
    refine GlobalTheory.T.isAffineOpen_of_local_sectionCombination_locus Q.P.left M.Z Q.P.hom S.J _ W hW (hle i) fun z _ => ?_
    obtain ⟨l, hl⟩ := TopologicalSpace.Opens.mem_iSup.1 (Q.cover.ge (Set.mem_univ z))
    refine ⟨Q.W l, _, Q.σ l, m l i, hl, Q.aff l, hσ l, fun k => ((Q.imm l).2 k trivial).1, fun K _ y w h hw => ?_⟩
    exact (CrdCalc.crd_isUnit_iff i (hT l K y w h hw)).symm.trans isUnit_iff_ne_zero

/- English proof (translation)
Substitute `h` using the available equality. Conclude with `⟨g, rfl, by rw [eq_of_heq hφ, ex.a_eq]⟩`.
-/
theorem exists_transport (Q : Clos ρ M U₀ EE) (ex : Q.Ext) {u : U₀.toScheme ⟶ Sp S.R} (h : u = Q.u₀)
    (φ : pullback ρ.P.A.hom u ⟶ Q.G.toScheme) (hφ : HEq φ ex.a) {T : Scheme.{0}} (g : T ⟶ pullback ρ.P.A.hom u) :
    ∃ g₀ : T ⟶ pullback ρ.P.A.hom Q.u₀, g₀ ≫ pullback.fst _ _ = g ≫ pullback.fst _ _ ∧
      g₀ ≫ Q.a₀ = g ≫ φ ≫ Q.G.ι := by
  subst h
  exact ⟨g, rfl, by rw [eq_of_heq hφ, ex.a_eq]⟩

/- English proof (translation)
Introduce and unpack `o Ω _ _ _ _ S ρ M U₀ EE Q ex Z ⟨e, he, hu₀, hφ⟩ - hAb hind W b hW hb`. Establish `hs : Function.Surjective Q.P.hom` using `fun z => ⟨(ex.e ≫ Q.G.ι) z, by rw [← Scheme.Hom.comp_apply, Category.assoc, ex.e_sec]; rfl⟩`. Use `choose m m' hu hm using fun l => GlobalTheory.T.exists_invertible_matrix_change_of_span_eq o Ω M S.J W (Q.W l) b (Q.B l) (Q.c l) (fun z hz => (hb z hz.1).symm.trans (Q.basis l z hz.2)) (Q.c_inv l)`. Take `⟨L, T, hle, hT⟩` from `exists_bundle Q hs W b m (fun l => ⟨_, hu l⟩) hm`. Take `⟨hcov, haff⟩` from `cover_affine Q hW m (fun l => ⟨_, hu l⟩) hle hT`.

Set `F : (Z.G.hom ⁻¹ᵁ W).toScheme ⟶ Q.P.left` to `(Z.G.hom ⁻¹ᵁ W).ι ≫ e.hom ≫ Q.G.ι`. Establish `hF : F ≫ Q.P.hom = (Z.G.hom ⁻¹ᵁ W).ι ≫ Z.G.hom` using `by simp only [F, Category.assoc, he]`. Take `⟨F', hF'⟩ : ∃ F' : (Z.G.hom ⁻¹ᵁ W).toScheme ⟶ (Q.P.hom ⁻¹ᵁ W).toScheme, F' ≫ (Q.P.hom ⁻¹ᵁ W).ι = F` from `⟨IsOpenImmersion.lift _ F (by`. Introduce and unpack `_ ⟨x, rfl⟩`. Rewrite using `[Scheme.Opens.range_ι]`.

Conclude with `(congrArg (fun q => q x ∈ W) hF).mpr x.2), IsOpenImmersion.lift_fac _ _ _⟩`. Set `T' : S.J → (L.pull (Q.P.hom ⁻¹ᵁ W).ι).Sec` to `fun i => GlobalTheory.secPull (T i) _`. Establish `hT' : ⨆ i, nonzeroLocus (T' i) = ⊤`. Simplify using `only [T', nonzeroLocus_secPull, ← Scheme.Hom.preimage_iSup]`. Conclude with `top_le_iff.1 fun x _ => hcov x.2`.

Establish `hL'` using `(isGenerated_of_finite T' hT').isLB`. Establish `hcrd : ∀ (K : Type) [Field K] (x : Sp K ⟶ (Z.G.hom ⁻¹ᵁ W).toScheme) (v : S.J → K), Crd ((L.pull (Q.P.hom ⁻¹ᵁ W).ι).pull F') (fun i => GlobalTheory.secPull (T' i) F') x v ↔ Crd L T (x ≫ F) v` using `fun K _ x v => (crd_secPull T' F' x v).trans ((crd_secPull T _ _ v).trans (by rw [Category.assoc, hF']))`. Use `⟨(L.pull (Q.P.hom ⁻¹ᵁ W).ι).pull F', fun i => GlobalTheory.secPull (T' i) F', LB.isLB_pull hL' _, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Simplify using `only [nonzeroLocus_secPull (T' _), ← Scheme.Hom.preimage_iSup, hT', Scheme.Hom.preimage_top]`. Introduce `K _ β g g' r jP jO h1 h2 h3 h4 h5`.

Take `⟨g₀, e1, e2⟩` from `exists_transport Q ex hu₀ _ hφ g`. Establish `hr : ⊤ ≤ r ⁻¹ᵁ (LPow ρ.P.A ρ.P.L S.N (baseOver (Sp S.R))).U (fun _ => jP)` using `fun z _ => Set.mem_iInter.2 fun _ => h4 ⟨z, (congrArg (fun q => q z) h3).symm⟩`. Establish `hv` using `Q.crd K g₀ _ ⟨r, h3.trans e1.symm, crd_chart ρ.s r _ hr⟩`. Establish `e3 : g₀ ≫ Q.a₀ = g' ≫ F`. Rewrite using `[e2]`.

Simplify using `only [F, Category.assoc, reassoc_of% h2]`. Establish `e4 : (g' ≫ F) ≫ Q.P.hom = spMap β ≫ M.pt`. Rewrite using `[Category.assoc, hF, reassoc_of% h2, ← h1]`. Conclude with `congrArg (g ≫ ·) Z.cart.1.w`. Establish `hW' : ⊤ ≤ ((g' ≫ F) ≫ Q.P.hom) ⁻¹ᵁ W`.

Rewrite using `[Category.assoc, hF]`. Conclude with `fun z _ => (g' z).2`. Establish `hO` using `(hcrd K g' _).1 (crd_chart _ g' jO ((top_le_preimage_iff _ _).2 h5))`. Rewrite `hv` using `[e3]`. Take `⟨l, hl⟩` from `exists_le_preimage_of_iSup_eq_top ((g' ≫ F) ≫ Q.P.hom) Q.cover`.

Take `⟨y, hy⟩` from `exists_lift (g' ≫ F) (Q.P.hom ⁻¹ᵁ Q.W l) hl`. Establish `hne : ((W ⊓ Q.W l : M.Z.Opens) : Set M.Z).Nonempty` using `⟨_, hW' (x := IsLocalRing.closedPoint K) trivial, hl (x := IsLocalRing.closedPoint K) trivial⟩`. Rewrite `hv`, `hO`, `e4`, `hW'` using `[← hy]`. Rewrite `e4`, `hW'` using `[Category.assoc]`. Take `⟨w, hw⟩` from `CrdCalc.crd_exists (LB.isLB_pull Q.isLB _) (Q.σ l) y`.

Take `⟨u, hu⟩` from `exists_unit_generic Q l hne (hm l hne) y β (fun U hU f => by`. Rewrite using `[e4]`. Conclude with `(CrdCalc.valR_spMap β M.pt U (M.top_le_preimage_pt hU)).2 f) hw hv`. Take `⟨c, hc⟩` from `CrdCalc.crd_unique hO (hT l K y w hW' hw)`. Use `⟨((u⁻¹ * c : Kˣ) : K), Units.ne_zero _, fun i => ?_⟩` and prove the remaining obligations.

Rewrite using `[Units.val_mul, _root_.mul_assoc, Units.eq_inv_mul_iff_mul_eq]`. Conclude with `(congrFun hu i).symm.trans (hc i)`. Introduce `z hz hcl`. Take `⟨l, hl⟩` from `TopologicalSpace.Opens.mem_iSup.1 (Q.cover.ge (Set.mem_univ z))`. Take `⟨K, _, x, hx, hc⟩` from `hind l z hl hcl`.

Use `⟨K, _, x, hx, fun c h => ?_⟩` and prove the remaining obligations. Establish `hxW : ⊤ ≤ x ⁻¹ᵁ (W ⊓ Q.W l)` using `(top_le_preimage_iff _ _).2 (by rw [hx]; exact Set.singleton_subset_iff.2 ⟨hz, hl⟩)`. Establish `h1` using `isUnit_map_valR x hxW (hu l)`. Use `Matrix.vecMul_injective_of_isUnit h1 ((hc _ fun g j hg hgx => ?_).trans (Matrix.zero_vecMul _).symm)` and prove the remaining obligations. Distinguish the cases in `hj : ⊤ ≤ g ⁻¹ᵁ (Q.O1.pull (Q.P.hom ⁻¹ᵁ Q.W l).ι).U j`.

Establish `h2` using `hT l K g _ (by rw [hgx]; exact le_preimage_mono x inf_le_left hxW) (crd_chart (Q.σ l) g j hj)`. Rewrite `h2` using `[hgx]`. Take `⟨y₁, hy₁⟩` from `exists_lift (g ≫ (Q.P.hom ⁻¹ᵁ Q.W l).ι) Q.G ((top_le_preimage_iff _ _).2 hg)`. Establish `e1 : (y₁ ≫ e.inv) ≫ Z.G.hom = x`. Rewrite using `[← he, Category.assoc, Iso.inv_hom_id_assoc, reassoc_of% hy₁, hgx]`.

Take `⟨g', hg'⟩` from `exists_lift (y₁ ≫ e.inv) (Z.G.hom ⁻¹ᵁ W) (by`. Rewrite using `[← Scheme.Hom.comp_preimage, e1]`. Conclude with `le_preimage_mono x inf_le_left hxW)`. Establish `e2 : g' ≫ F = g ≫ (Q.P.hom ⁻¹ᵁ Q.W l).ι`. Simplify using `only [F, reassoc_of% hg', Iso.inv_hom_id_assoc, hy₁]`.

Rewrite `h2` using `[← e2]`. Take `⟨jO, u, -, hv⟩` from `(hcrd K g' _).2 h2`. Establish `h3` using `h g' jO (by rw [reassoc_of% hg', ← e1, Category.assoc])`. Express the relevant statement in the definitionally equal form `(c ᵥ* _) ⬝ᵥ (fun k => valR g _ ((Q.σ l k).f j)) = 0`. Rewrite using `[← Matrix.dotProduct_mulVec]`.

Combine the equalities or inequalities in the displayed calculation. Conclude with `Finset.sum_eq_zero fun i _ => mul_eq_zero_of_right _ (dif_neg hj)`. Introduce `hab`. Use `hAb.2 W hab` as an intermediate fact. Establish `hp : IsProper (Z.G.hom ∣_ W)` using `by delta morphismRestrict infer_instance`.

Establish `: IsAffine W` using `hW`. Establish `: CompactSpace (Z.G.hom ⁻¹ᵁ W).toScheme` using `QuasiCompact.compactSpace_of_compactSpace (Z.G.hom ∣_ W)`. Establish `: IsOpenImmersion (F' ≫ (Q.P.hom ⁻¹ᵁ W).ι)` using `by rw [hF']; infer_instance`. Establish `: IsOpenImmersion F'` using `IsOpenImmersion.of_comp F' (Q.P.hom ⁻¹ᵁ W).ι`. Establish `ha : IsAmpleLB (L.pull (Q.P.hom ⁻¹ᵁ W).ι)` using `isAmpleLB_of_cover hL' le_rfl (fun i => secToPow (T' i) 1) (by simp only [nonzeroLocus_secToPow _ le_rfl, hT']) fun i => by`.

Rewrite using `[nonzeroLocus_secToPow _ le_rfl, nonzeroLocus_secPull]`. Conclude with `(haff i).preimage_of_isOpenImmersion _ (by rw [Scheme.Opens.opensRange_ι]; exact hle i)`. Establish `: IsProper (Over.mk (Z.G.hom ∣_ W)).hom` using `hp`. Conclude with `(relAmple_iff_isAmpleLB_of_isAffine (Over.mk (Z.G.hom ∣_ W)) (LB.isLB_pull hL' _)).2 (ha.pull_of_isOpenImmersion F')`.
-/
theorem secO : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (Q : Clos ρ M U₀ EE) (ex : Q.Ext) (Z : ZHPre ρ M U₀), (∃ e : Z.G.left ≅ Q.G.toScheme, e.hom ≫ Q.G.ι ≫ Q.P.hom = Z.G.hom ∧ Z.u₀ = Q.u₀ ∧ HEq (Z.φ ≫ e.hom) ex.a) → BaseFacts S M U₀ EE → Z.Ab → (∀ l, ∀ z ∈ Q.W l, IsClosed ({z} : Set M.Z) → ∃ (K : Type) (_ : Field K) (x : Sp K ⟶ M.Z), Set.range x = {z} ∧ ∀ c : S.J → K, (∀ (g : Sp K ⟶ (Q.P.hom ⁻¹ᵁ Q.W l).toScheme) (j), Set.range (g ≫ (Q.P.hom ⁻¹ᵁ Q.W l).ι) ⊆ Q.G → g ≫ (Q.P.hom ⁻¹ᵁ Q.W l).ι ≫ Q.P.hom = x → ∑ i, c i * valF g _ ((Q.σ l i).f j) = 0) → c = 0) → Z.SecO EE := by
  rintro o Ω _ _ _ _ S ρ M U₀ EE Q ex Z ⟨e, he, hu₀, hφ⟩ - hAb hind W b hW hb
  have hs : Function.Surjective Q.P.hom := fun z =>
    ⟨(ex.e ≫ Q.G.ι) z, by rw [← Scheme.Hom.comp_apply, Category.assoc, ex.e_sec]; rfl⟩
  choose m m' hu hm using fun l => GlobalTheory.T.exists_invertible_matrix_change_of_span_eq o Ω M S.J W (Q.W l) b (Q.B l) (Q.c l)
    (fun z hz => (hb z hz.1).symm.trans (Q.basis l z hz.2)) (Q.c_inv l)
  obtain ⟨L, T, hle, hT⟩ := exists_bundle Q hs W b m (fun l => ⟨_, hu l⟩) hm
  obtain ⟨hcov, haff⟩ := cover_affine Q hW m (fun l => ⟨_, hu l⟩) hle hT
  let F : (Z.G.hom ⁻¹ᵁ W).toScheme ⟶ Q.P.left := (Z.G.hom ⁻¹ᵁ W).ι ≫ e.hom ≫ Q.G.ι
  have hF : F ≫ Q.P.hom = (Z.G.hom ⁻¹ᵁ W).ι ≫ Z.G.hom := by simp only [F, Category.assoc, he]
  obtain ⟨F', hF'⟩ : ∃ F' : (Z.G.hom ⁻¹ᵁ W).toScheme ⟶ (Q.P.hom ⁻¹ᵁ W).toScheme, F' ≫ (Q.P.hom ⁻¹ᵁ W).ι = F :=
    ⟨IsOpenImmersion.lift _ F (by
      rintro _ ⟨x, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact (congrArg (fun q => q x ∈ W) hF).mpr x.2), IsOpenImmersion.lift_fac _ _ _⟩
  let T' : S.J → (L.pull (Q.P.hom ⁻¹ᵁ W).ι).Sec := fun i => GlobalTheory.secPull (T i) _
  have hT' : ⨆ i, nonzeroLocus (T' i) = ⊤ := by
    simp only [T', nonzeroLocus_secPull, ← Scheme.Hom.preimage_iSup]
    exact top_le_iff.1 fun x _ => hcov x.2
  have hL' := (isGenerated_of_finite T' hT').isLB
  have hcrd : ∀ (K : Type) [Field K] (x : Sp K ⟶ (Z.G.hom ⁻¹ᵁ W).toScheme) (v : S.J → K),
      Crd ((L.pull (Q.P.hom ⁻¹ᵁ W).ι).pull F') (fun i => GlobalTheory.secPull (T' i) F') x v ↔ Crd L T (x ≫ F) v :=
    fun K _ x v => (crd_secPull T' F' x v).trans ((crd_secPull T _ _ v).trans (by rw [Category.assoc, hF']))
  refine ⟨(L.pull (Q.P.hom ⁻¹ᵁ W).ι).pull F', fun i => GlobalTheory.secPull (T' i) F', LB.isLB_pull hL' _, ?_, ?_, ?_, ?_⟩
  · simp only [nonzeroLocus_secPull (T' _), ← Scheme.Hom.preimage_iSup, hT', Scheme.Hom.preimage_top]
  · intro K _ β g g' r jP jO h1 h2 h3 h4 h5
    obtain ⟨g₀, e1, e2⟩ := exists_transport Q ex hu₀ _ hφ g
    have hr : ⊤ ≤ r ⁻¹ᵁ (LPow ρ.P.A ρ.P.L S.N (baseOver (Sp S.R))).U (fun _ => jP) := fun z _ =>
      Set.mem_iInter.2 fun _ => h4 ⟨z, (congrArg (fun q => q z) h3).symm⟩
    have hv := Q.crd K g₀ _ ⟨r, h3.trans e1.symm, crd_chart ρ.s r _ hr⟩
    have e3 : g₀ ≫ Q.a₀ = g' ≫ F := by
      rw [e2]
      simp only [F, Category.assoc, reassoc_of% h2]
    have e4 : (g' ≫ F) ≫ Q.P.hom = spMap β ≫ M.pt := by
      rw [Category.assoc, hF, reassoc_of% h2, ← h1]
      exact congrArg (g ≫ ·) Z.cart.1.w
    have hW' : ⊤ ≤ ((g' ≫ F) ≫ Q.P.hom) ⁻¹ᵁ W := by
      rw [Category.assoc, hF]
      exact fun z _ => (g' z).2
    have hO := (hcrd K g' _).1 (crd_chart _ g' jO ((top_le_preimage_iff _ _).2 h5))
    rw [e3] at hv
    obtain ⟨l, hl⟩ := exists_le_preimage_of_iSup_eq_top ((g' ≫ F) ≫ Q.P.hom) Q.cover
    obtain ⟨y, hy⟩ := exists_lift (g' ≫ F) (Q.P.hom ⁻¹ᵁ Q.W l) hl
    have hne : ((W ⊓ Q.W l : M.Z.Opens) : Set M.Z).Nonempty :=
      ⟨_, hW' (x := IsLocalRing.closedPoint K) trivial, hl (x := IsLocalRing.closedPoint K) trivial⟩
    rw [← hy] at hv hO e4 hW'
    rw [Category.assoc] at e4 hW'
    obtain ⟨w, hw⟩ := CrdCalc.crd_exists (LB.isLB_pull Q.isLB _) (Q.σ l) y
    obtain ⟨u, hu⟩ := exists_unit_generic Q l hne (hm l hne) y β (fun U hU f => by
      rw [e4]
      exact (CrdCalc.valR_spMap β M.pt U (M.top_le_preimage_pt hU)).2 f) hw hv
    obtain ⟨c, hc⟩ := CrdCalc.crd_unique hO (hT l K y w hW' hw)
    refine ⟨((u⁻¹ * c : Kˣ) : K), Units.ne_zero _, fun i => ?_⟩
    rw [Units.val_mul, _root_.mul_assoc, Units.eq_inv_mul_iff_mul_eq]
    exact (congrFun hu i).symm.trans (hc i)
  · intro z hz hcl
    obtain ⟨l, hl⟩ := TopologicalSpace.Opens.mem_iSup.1 (Q.cover.ge (Set.mem_univ z))
    obtain ⟨K, _, x, hx, hc⟩ := hind l z hl hcl
    refine ⟨K, _, x, hx, fun c h => ?_⟩
    have hxW : ⊤ ≤ x ⁻¹ᵁ (W ⊓ Q.W l) := (top_le_preimage_iff _ _).2 (by rw [hx]; exact Set.singleton_subset_iff.2 ⟨hz, hl⟩)
    have h1 := isUnit_map_valR x hxW (hu l)
    refine Matrix.vecMul_injective_of_isUnit h1 ((hc _ fun g j hg hgx => ?_).trans (Matrix.zero_vecMul _).symm)
    by_cases hj : ⊤ ≤ g ⁻¹ᵁ (Q.O1.pull (Q.P.hom ⁻¹ᵁ Q.W l).ι).U j
    · have h2 := hT l K g _ (by rw [hgx]; exact le_preimage_mono x inf_le_left hxW) (crd_chart (Q.σ l) g j hj)
      rw [hgx] at h2
      obtain ⟨y₁, hy₁⟩ := exists_lift (g ≫ (Q.P.hom ⁻¹ᵁ Q.W l).ι) Q.G ((top_le_preimage_iff _ _).2 hg)
      have e1 : (y₁ ≫ e.inv) ≫ Z.G.hom = x := by
        rw [← he, Category.assoc, Iso.inv_hom_id_assoc, reassoc_of% hy₁, hgx]
      obtain ⟨g', hg'⟩ := exists_lift (y₁ ≫ e.inv) (Z.G.hom ⁻¹ᵁ W) (by
        rw [← Scheme.Hom.comp_preimage, e1]
        exact le_preimage_mono x inf_le_left hxW)
      have e2 : g' ≫ F = g ≫ (Q.P.hom ⁻¹ᵁ Q.W l).ι := by
        simp only [F, reassoc_of% hg', Iso.inv_hom_id_assoc, hy₁]
      rw [← e2] at h2
      obtain ⟨jO, u, -, hv⟩ := (hcrd K g' _).2 h2
      have h3 := h g' jO (by rw [reassoc_of% hg', ← e1, Category.assoc])
      change (c ᵥ* _) ⬝ᵥ (fun k => valR g _ ((Q.σ l k).f j)) = 0
      rw [← Matrix.dotProduct_mulVec]
      calc _ = ∑ i, (u : K) * (c i * valR g' _ ((GlobalTheory.secPull (T' i) F').f jO)) :=
          Finset.sum_congr rfl fun i _ => by rw [hv i, mul_left_comm]
        _ = 0 := by rw [← Finset.mul_sum]; exact mul_eq_zero_of_right _ h3
    · exact Finset.sum_eq_zero fun i _ => mul_eq_zero_of_right _ (dif_neg hj)
  · intro hab
    have := hAb.2 W hab
    have hp : IsProper (Z.G.hom ∣_ W) := by
      delta morphismRestrict
      infer_instance
    have : IsAffine W := hW
    have : CompactSpace (Z.G.hom ⁻¹ᵁ W).toScheme := QuasiCompact.compactSpace_of_compactSpace (Z.G.hom ∣_ W)
    have : IsOpenImmersion (F' ≫ (Q.P.hom ⁻¹ᵁ W).ι) := by rw [hF']; infer_instance
    have : IsOpenImmersion F' := IsOpenImmersion.of_comp F' (Q.P.hom ⁻¹ᵁ W).ι
    have ha : IsAmpleLB (L.pull (Q.P.hom ⁻¹ᵁ W).ι) :=
      isAmpleLB_of_cover hL' le_rfl (fun i => secToPow (T' i) 1)
        (by simp only [nonzeroLocus_secToPow _ le_rfl, hT']) fun i => by
          rw [nonzeroLocus_secToPow _ le_rfl, nonzeroLocus_secPull]
          exact (haff i).preimage_of_isOpenImmersion _ (by rw [Scheme.Opens.opensRange_ι]; exact hle i)
    have : IsProper (Over.mk (Z.G.hom ∣_ W)).hom := hp
    exact (relAmple_iff_isAmpleLB_of_isAffine (Over.mk (Z.G.hom ∣_ W)) (LB.isLB_pull hL' _)).2
      (ha.pull_of_isOpenImmersion F')

end GlobalTheory.ZH.SecCoord
end
