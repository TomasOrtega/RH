import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.AppellHumbertTrivialOfNowhereVanishing
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory
namespace PullHermitian

section Values

variable {X : Scheme.{0}} (x : Sp ℂ ⟶ X)

def unitVal {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) : Γ(X, U)ˣ →* ℂˣ :=
  Units.map ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom.comp (x.appLE U ⊤ h).hom).toMonoidHom

/- English proof (translation)
Rewrite using `[valAt', dif_pos h]`. Both sides reduce to the same expression.
-/
lemma valAt'_eq_unitVal {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(X, U)ˣ) :
    valAt' x U f.val = unitVal x h f := by
  rw [valAt', dif_pos h]; rfl

/- English proof (translation)
Use `ext`. Express the relevant statement in the definitionally equal form `(Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom ((X.presheaf.map (homOfLE hVU).op ≫ x.appLE V ⊤ h).hom f.val) = _`. Rewrite using `[Scheme.Hom.map_appLE]`. Both sides reduce to the same expression.
-/
lemma unitVal_res {U V : X.Opens} (hVU : V ≤ U) (h : ⊤ ≤ x ⁻¹ᵁ V) (h' : ⊤ ≤ x ⁻¹ᵁ U)
    (f : Γ(X, U)ˣ) : unitVal x h (res hVU f) = unitVal x h' f := by
  ext
  change (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom
    ((X.presheaf.map (homOfLE hVU).op ≫ x.appLE V ⊤ h).hom f.val) = _
  rw [Scheme.Hom.map_appLE]
  rfl

/- English proof (translation)
Use `ext`. Express the relevant statement in the definitionally equal form `(Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom ((φ.app U ≫ x.appLE _ ⊤ h).hom f.val) = _`. Rewrite using `[← Scheme.Hom.comp_appLE x φ U ⊤ h']`. Both sides reduce to the same expression.
-/
lemma unitVal_pullU {Y : Scheme.{0}} (φ : X ⟶ Y) (U : Y.Opens) (h : ⊤ ≤ x ⁻¹ᵁ (φ ⁻¹ᵁ U))
    (h' : ⊤ ≤ (x ≫ φ) ⁻¹ᵁ U) (f : Γ(Y, U)ˣ) :
    unitVal x h (pullU φ U f) = unitVal (x ≫ φ) h' f := by
  ext
  change (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom
    ((φ.app U ≫ x.appLE _ ⊤ h).hom f.val) = _
  rw [← Scheme.Hom.comp_appLE x φ U ⊤ h']
  rfl

/- English proof (translation)
Simplify using `only [Category.comp_id]`.
-/
lemma unitVal_comp_id {U : X.Opens} (h : ⊤ ≤ (x ≫ 𝟙 X) ⁻¹ᵁ U) (h' : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(X, U)ˣ) :
    unitVal (x ≫ 𝟙 X) h f = unitVal x h' f := by
  simp only [Category.comp_id]

/- English proof (translation)
Introduce `_ hp` and use `⟨h hp, h' hp⟩`.
-/
lemma inf_of {U V : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) (h' : ⊤ ≤ x ⁻¹ᵁ V) : ⊤ ≤ x ⁻¹ᵁ (U ⊓ V) :=
  fun _ hp => ⟨h hp, h' hp⟩

/- English proof (translation)
Introduce `_ hp` and use `Set.mem_iInter.2 fun _ => h hp`.
-/
lemma wchart_of {Y : Scheme.{0}} (L : LB Y) (φ : X ⟶ Y) (j : L.ι)
    (h : ⊤ ≤ (x ≫ φ) ⁻¹ᵁ L.U j) :
    ⊤ ≤ x ⁻¹ᵁ L.wchart (K := PUnit) (fun _ => φ) (fun _ => j) :=
  fun _ hp => Set.mem_iInter.2 fun _ => h hp

/- English proof (translation)
Establish `h : x (default : PrimeSpectrum ℂ) ∈ ⨆ i, L.U i`. Rewrite using `[hL.cover]`. Discharge the goal by the elementary cases of `trivial`. Take `⟨i, hi⟩` from `TopologicalSpace.Opens.mem_iSup.1 h`. Use `⟨i, fun p _ => ?_⟩` and prove the remaining obligations.

Establish `: p = (default : PrimeSpectrum ℂ)` using `Subsingleton.elim (α := PrimeSpectrum ℂ) _ _`. Substitute `this` using the available equality. Conclude with `hi`.
-/
lemma exists_chart {L : LB X} (hL : L.IsLB) : ∃ i, ⊤ ≤ x ⁻¹ᵁ L.U i := by
  have h : x (default : PrimeSpectrum ℂ) ∈ ⨆ i, L.U i := by
    rw [hL.cover]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 h
  refine ⟨i, fun p _ => ?_⟩
  have : p = (default : PrimeSpectrum ℂ) := Subsingleton.elim (α := PrimeSpectrum ℂ) _ _
  subst this
  exact hi

/- English proof (translation)
Use `(map_prod (unitVal x h) _ _).trans ?_` and prove the remaining obligations. Rewrite using `[Fintype.prod_unique]`. Use `(map_zpow (unitVal x h) _ _).trans ?_` and prove the remaining obligations. Conclude with `congrArg (· ^ ε) ((unitVal_res x (U := φ ⁻¹ᵁ (L.U j ⊓ L.U j')) _ h h' _).trans (unitVal_pullU x φ (L.U j ⊓ L.U j') h' h' _))`.
-/
lemma unitVal_linComb {Y : Scheme.{0}} (L : LB Y) (φ : X ⟶ Y) (ε : ℤ) (j j' : L.ι)
    (h : ⊤ ≤ x ⁻¹ᵁ ((L.LinComb (K := PUnit) (fun _ => φ) (fun _ => ε)).U (fun _ => j) ⊓
      (L.LinComb (K := PUnit) (fun _ => φ) (fun _ => ε)).U (fun _ => j')))
    (h' : ⊤ ≤ (x ≫ φ) ⁻¹ᵁ (L.U j ⊓ L.U j')) :
    unitVal x h ((L.LinComb (K := PUnit) (fun _ => φ) (fun _ => ε)).g (fun _ => j) (fun _ => j')) =
      unitVal (x ≫ φ) h' (L.g j j') ^ ε := by
  refine (map_prod (unitVal x h) _ _).trans ?_
  rw [Fintype.prod_unique]
  refine (map_zpow (unitVal x h) _ _).trans ?_
  exact congrArg (· ^ ε) ((unitVal_res x (U := φ ⁻¹ᵁ (L.U j ⊓ L.U j')) _ h h' _).trans
    (unitVal_pullU x φ (L.U j ⊓ L.U j') h' h' _))

/- English proof (translation)
Establish `h : ⊤ ≤ x ⁻¹ᵁ ((LB.div M N).U (i, j) ⊓ (LB.div M N).U (i', j'))` using `inf_of x (inf_of x hi hj) (inf_of x hi' hj')`. Use `(unitVal_res x inf_le_left h _ _).symm.trans ?_` and prove the remaining obligations. Use `(congrArg (unitVal x h) (hw (i, j) (i', j'))).trans ?_` and prove the remaining obligations. Use `(map_mul (unitVal x h) _ _).trans ?_` and prove the remaining obligations. Use `congrArg₂ (· * ·) ?_ (unitVal_res x inf_le_right h _ _)` and prove the remaining obligations.

Use `(map_mul (unitVal x h) _ _).trans ?_` and prove the remaining obligations. Conclude with `congrArg₂ (· * ·) (unitVal_res x _ h _ _) ((map_inv (unitVal x h) _).trans (congrArg (·⁻¹) (unitVal_res x _ h _ _)))`.
-/
lemma unitVal_iso {M N : LB X} (w : LB.Iso N M) (hw : w.IsGen) (i i' : M.ι) (j j' : N.ι)
    (hi : ⊤ ≤ x ⁻¹ᵁ M.U i) (hi' : ⊤ ≤ x ⁻¹ᵁ M.U i') (hj : ⊤ ≤ x ⁻¹ᵁ N.U j)
    (hj' : ⊤ ≤ x ⁻¹ᵁ N.U j') :
    unitVal x (U := (LB.div M N).U (i, j)) (inf_of x hi hj) (w.s (i, j)) =
      unitVal x (inf_of x hi hi') (M.g i i') * (unitVal x (inf_of x hj hj') (N.g j j'))⁻¹ *
        unitVal x (U := (LB.div M N).U (i', j')) (inf_of x hi' hj') (w.s (i', j')) := by
  have h : ⊤ ≤ x ⁻¹ᵁ ((LB.div M N).U (i, j) ⊓ (LB.div M N).U (i', j')) :=
    inf_of x (inf_of x hi hj) (inf_of x hi' hj')
  refine (unitVal_res x inf_le_left h _ _).symm.trans ?_
  refine (congrArg (unitVal x h) (hw (i, j) (i', j'))).trans ?_
  refine (map_mul (unitVal x h) _ _).trans ?_
  refine congrArg₂ (· * ·) ?_ (unitVal_res x inf_le_right h _ _)
  refine (map_mul (unitVal x h) _ _).trans ?_
  exact congrArg₂ (· * ·) (unitVal_res x _ h _ _)
    ((map_inv (unitVal x h) _).trans (congrArg (·⁻¹) (unitVal_res x _ h _ _)))

abbrev idx {Y : Scheme.{0}} {L : LB X} {L' : LB Y} (f : X ⟶ Y) (m n : ℕ) (i : L.ι) (j : L'.ι) :
    (LB.div (lbPow L n) (lbPow (L'.pull f) m)).ι := (fun _ => i, fun _ _ => j)

/- English proof (translation)
The claim follows from `inf_of x (wchart_of x L (𝟙 X) i (by simpa using hi)) (wchart_of x (L'.pull f) (𝟙 X) _ (wchart_of x L' f j hj))`.
-/
lemma idx_chart {Y : Scheme.{0}} {L : LB X} {L' : LB Y} (f : X ⟶ Y) (m n : ℕ) (i : L.ι) (j : L'.ι)
    (hi : ⊤ ≤ x ⁻¹ᵁ L.U i) (hj : ⊤ ≤ (x ≫ f) ⁻¹ᵁ L'.U j) :
    ⊤ ≤ x ⁻¹ᵁ (LB.div (lbPow L n) (lbPow (L'.pull f) m)).U (idx f m n i j) :=
  inf_of x (wchart_of x L (𝟙 X) i (by simpa using hi))
    (wchart_of x (L'.pull f) (𝟙 X) _ (wchart_of x L' f j hj))

/- English proof (translation)
Establish `a` using `wchart_of x L (𝟙 X) i (by simpa using hi)`. Establish `a'` using `wchart_of x L (𝟙 X) i' (by simpa using hi')`. Establish `c` using `wchart_of x L' f j hj`. Establish `c'` using `wchart_of x L' f j' hj'`. Establish `b` using `wchart_of x (L'.pull f) (𝟙 X) (fun _ => j) c`.

Establish `b'` using `wchart_of x (L'.pull f) (𝟙 X) (fun _ => j') c'`. Establish `h` using `unitVal_iso x w hw (fun _ => i) (fun _ => i') (fun _ _ => j) (fun _ _ => j') a a' b b'`. Establish `h1` using `unitVal_linComb x L (𝟙 X) n i i' (inf_of x a a') (inf_of x hi hi')`. Establish `h2` using `unitVal_linComb x (L'.pull f) (𝟙 X) m (fun _ => j) (fun _ => j') (inf_of x b b') (inf_of x c c')`. Establish `h3` using `unitVal_linComb x L' f 1 j j' (inf_of x c c') (inf_of _ hj hj')`.

Use `replace h1 := h1.trans (congrArg (· ^ (n : ℤ)) (unitVal_comp_id x _ (inf_of x hi hi') _))`. Use `replace h2 := h2.trans (congrArg (· ^ (m : ℤ)) ((unitVal_comp_id x _ (inf_of x c c') _).trans h3))`. Use `replace h := h.trans (congrArg₂ (fun a b => a * b⁻¹ * _) h1 h2)`. Rewrite using `[valAt'_eq_unitVal x (idx_chart x f m n i j hi hj), valAt'_eq_unitVal x (idx_chart x f m n i' j' hi' hj'), valAt'_eq_unitVal x (inf_of x hi hi'), valAt'_eq_unitVal _ (inf_of _ hj hj')]`. Establish `h4` using `congrArg Units.val h`.

Simplify using `only [Units.val_mul, zpow_natCast, zpow_one, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val] at h4`. Use `(congrArg (· * _) h4).trans ?_` and prove the remaining obligations. Clear the denominators using the available nonvanishing facts.
-/
lemma val_iso_pow {Y : Scheme.{0}} {L : LB X} {L' : LB Y} (f : X ⟶ Y) (m n : ℕ)
    (w : LB.Iso (lbPow (L'.pull f) m) (lbPow L n)) (hw : w.IsGen) (i i' : L.ι) (j j' : L'.ι)
    (hi : ⊤ ≤ x ⁻¹ᵁ L.U i) (hi' : ⊤ ≤ x ⁻¹ᵁ L.U i') (hj : ⊤ ≤ (x ≫ f) ⁻¹ᵁ L'.U j)
    (hj' : ⊤ ≤ (x ≫ f) ⁻¹ᵁ L'.U j') :
    valAt' x _ (w.s (idx f m n i j)).val *
        valAt' (x ≫ f) (L'.U j ⊓ L'.U j') (L'.g j j').val ^ m =
      valAt' x (L.U i ⊓ L.U i') (L.g i i').val ^ n * valAt' x _ (w.s (idx f m n i' j')).val := by
  have a := wchart_of x L (𝟙 X) i (by simpa using hi)
  have a' := wchart_of x L (𝟙 X) i' (by simpa using hi')
  have c := wchart_of x L' f j hj
  have c' := wchart_of x L' f j' hj'
  have b := wchart_of x (L'.pull f) (𝟙 X) (fun _ => j) c
  have b' := wchart_of x (L'.pull f) (𝟙 X) (fun _ => j') c'
  have h := unitVal_iso x w hw (fun _ => i) (fun _ => i') (fun _ _ => j) (fun _ _ => j') a a' b b'
  have h1 := unitVal_linComb x L (𝟙 X) n i i' (inf_of x a a') (inf_of x hi hi')
  have h2 := unitVal_linComb x (L'.pull f) (𝟙 X) m (fun _ => j) (fun _ => j') (inf_of x b b')
    (inf_of x c c')
  have h3 := unitVal_linComb x L' f 1 j j' (inf_of x c c') (inf_of _ hj hj')
  replace h1 := h1.trans (congrArg (· ^ (n : ℤ)) (unitVal_comp_id x _ (inf_of x hi hi') _))
  replace h2 := h2.trans (congrArg (· ^ (m : ℤ))
    ((unitVal_comp_id x _ (inf_of x c c') _).trans h3))
  replace h := h.trans (congrArg₂ (fun a b => a * b⁻¹ * _) h1 h2)
  rw [valAt'_eq_unitVal x (idx_chart x f m n i j hi hj),
    valAt'_eq_unitVal x (idx_chart x f m n i' j' hi' hj'),
    valAt'_eq_unitVal x (inf_of x hi hi'), valAt'_eq_unitVal _ (inf_of _ hj hj')]
  have h4 := congrArg Units.val h
  simp only [Units.val_mul, zpow_natCast, zpow_one, Units.val_inv_eq_inv_val,
    Units.val_pow_eq_pow_val] at h4
  refine (congrArg (· * _) h4).trans ?_
  field_simp

end Values

/- English proof (translation)
Use `choose c hc using hc`. Establish `hr : ∀ i z, z ∈ V i → φ (c z) z = φ i z` using `fun i z hz => ha _ _ z (hc z) hz`. Use `⟨fun z => φ (c z) z, fun z => ?_, hr⟩` and prove the remaining obligations. Establish `hn` using `(hV (c z)).mem_nhds (hc z)`. Conclude with `((hφ (c z)).differentiableAt hn).congr_of_eventuallyEq (Filter.mem_of_superset hn fun y hy => hr _ y hy)`.
-/
lemma exists_glue {E κ : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (V : κ → Set E)
    (hV : ∀ i, IsOpen (V i)) (hc : ∀ z, ∃ i, z ∈ V i) (φ : κ → E → ℂ)
    (hφ : ∀ i, DifferentiableOn ℂ (φ i) (V i))
    (ha : ∀ i j z, z ∈ V i → z ∈ V j → φ i z = φ j z) :
    ∃ r : E → ℂ, Differentiable ℂ r ∧ ∀ i z, z ∈ V i → r z = φ i z := by
  choose c hc using hc
  have hr : ∀ i z, z ∈ V i → φ (c z) z = φ i z := fun i z hz => ha _ _ z (hc z) hz
  refine ⟨fun z => φ (c z) z, fun z => ?_, hr⟩
  have hn := (hV (c z)).mem_nhds (hc z)
  exact ((hφ (c z)).differentiableAt hn).congr_of_eventuallyEq
    (Filter.mem_of_superset hn fun y hy => hr _ y hy)

/- English proof (translation)
Rewrite using `[← LinearMap.toMatrix'_mulVec F z, ← LinearMap.toMatrix'_mulVec F w]`. Generalize the expression as in `LinearMap.toMatrix' F = P`. Unfold `hermForm`. Rewrite using `[← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec z, Matrix.vecMul_transpose, Matrix.mulVec_conjTranspose, star_star, Matrix.vecMul_transpose]`.
-/
lemma hermForm_pull {g g' : ℕ} (H : Matrix (Fin g') (Fin g') ℂ)
    (F : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)) (z w : Fin g → ℂ) :
    hermForm ((LinearMap.toMatrix' F).transpose * H * (LinearMap.toMatrix' F).transpose.conjTranspose) z w =
      hermForm H (F z) (F w) := by
  rw [← LinearMap.toMatrix'_mulVec F z, ← LinearMap.toMatrix'_mulVec F w]
  generalize LinearMap.toMatrix' F = P
  unfold hermForm
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec z,
    Matrix.vecMul_transpose, Matrix.mulVec_conjTranspose, star_star, Matrix.vecMul_transpose]

/- English proof (translation)
Simplify using `[hermForm, Matrix.sub_mulVec, Matrix.smul_mulVec]`.
-/
lemma hermForm_sub_smul {g : ℕ} (H H' : Matrix (Fin g) (Fin g) ℂ) (a b : ℂ) (z w : Fin g → ℂ) :
    hermForm (a • H - b • H') z w = a * hermForm H z w - b * hermForm H' z w := by
  simp [hermForm, Matrix.sub_mulVec, Matrix.smul_mulVec]

end PullHermitian

open PullHermitian in

/- English proof (translation)
Introduce `A A' _ _ L L' hL hL' g g' u u' Hm χ Hm' χ' hu hu' f F hF m n ⟨w, hw⟩`. Establish `hFl : ∀ z, (u'.ex (F z)).left = (u.ex z).left ≫ f.left` using `fun z => by`. Rewrite using `[hF, Over.comp_left]`. Establish `hΛ : ∀ l : u.Λ, F l ∈ u'.Λ` using `fun l => by`. Rewrite using `[← u'.ker, hF, (u.ker l).2 l.2, ← (u.ker 0).2 u.Λ.zero_mem, ← hF, map_zero]`.

Conclude with `(u'.ker 0).2 u'.Λ.zero_mem`. Establish `hper : ∀ (l : u.Λ) z, u.ex (z + l) = u.ex z` using `fun l z => by`. Rewrite using `[u.ex_add, (u.ker l).2 l.2, _root_.mul_one]`. Establish `hFd : Differentiable ℂ F` using `(LinearMap.toContinuousLinearMap F).differentiable`. Take `⟨r, hr, hrφ⟩` from `exists_glue (fun p : L.ι × L'.ι => {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U p.1} ∩ F ⁻¹' {z | ⊤ ≤ (u'.ex z).left ⁻¹ᵁ L'.U p.2}) (fun p => (u.hol _ 0).1.inter ((u'.hol _ 0).1.preimage hFd.continuous)) (fun z => by`.

Take `⟨i, hi⟩` from `exists_chart (u.ex z).left hL`. Take `⟨j, hj⟩` from `exists_chart (u'.ex (F z)).left hL'`. Conclude with `⟨(i, j), hi, hj⟩)`. Use the proof step `(fun p z => valAt' (u.ex z).left _ (w.s (idx f.left m n p.1 p.2)).val * u'.fr p.2 (F z) ^ m / u.fr p.1 z ^ n)`. Use the proof step `(fun p => by`.

Establish `d1` using `(u.hol _ (w.s (idx f.left m n p.1 p.2)).val).2.mono (s := {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U p.1} ∩ F ⁻¹' {z | ⊤ ≤ (u'.ex z).left ⁻¹ᵁ L'.U p.2}) fun z hz => idx_chart _ _ _ _ _ _ hz.1 (hFl z ▸ hz.2)`. Establish `d2` using `(u'.fr_hol p.2).comp (s := {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U p.1} ∩ F ⁻¹' {z | ⊤ ≤ (u'.ex z).left ⁻¹ᵁ L'.U p.2}) hFd.differentiableOn fun z hz => hz.2`. Establish `d3` using `(u.fr_hol p.1).mono (s := {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U p.1} ∩ F ⁻¹' {z | ⊤ ≤ (u'.ex z).left ⁻¹ᵁ L'.U p.2}) Set.inter_subset_left`. Simplify using `only [div_eq_mul_inv]`. Conclude with `(d1.mul (d2.pow m)).mul ((d3.pow n).inv fun z hz => pow_ne_zero n (u.fr_ne p.1 z hz.1)))`.

Use the proof step `(fun p q z hp hq => by`. Establish `h` using `val_iso_pow (u.ex z).left f.left m n w hw p.1 q.1 p.2 q.2 hp.1 hq.1 (hFl z ▸ hp.2) (hFl z ▸ hq.2)`. Establish `h1` using `u.fr_compat p.1 q.1 z (inf_of _ hp.1 hq.1)`. Establish `h2` using `u'.fr_compat p.2 q.2 (F z) (inf_of _ hp.2 hq.2)`. Rewrite `h2` using `[hFl]`.

Rewrite using `[div_eq_div_iff (pow_ne_zero _ (u.fr_ne _ _ hp.1)) (pow_ne_zero _ (u.fr_ne _ _ hq.1)), h1, h2, mul_pow, mul_pow, ← _root_.mul_assoc, h]`. Use the proof step `ring)`. Use `set H₂ := (LinearMap.toMatrix' F).transpose * Hm' * (LinearMap.toMatrix' F).transpose.conjTranspose with hH₂`. Establish `hH₂h : H₂.IsHermitian` using `Matrix.isHermitian_mul_mul_conjTranspose _ hu'.1`. Establish `hchart : ∀ z, ∃ i j, ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i ∧ ⊤ ≤ (u'.ex (F z)).left ⁻¹ᵁ L'.U j` using `fun z => by`.

Take `⟨i, hi⟩` from `exists_chart (u.ex z).left hL`. Take `⟨j, hj⟩` from `exists_chart (u'.ex (F z)).left hL'`. Conclude with `⟨i, j, hi, hj⟩`. Use `haveI := u.discrete`. Establish `key` using `appellHumbert_trivial_of_nowhere_vanishing g u.Λ u.full ((n : ℂ) • Hm - (m : ℂ) • H₂) (fun l => χ l ^ n / χ' ⟨F l, hΛ l⟩ ^ m) r ((hu.1.smul (by simp [IsSelfAdjoint])).sub (hH₂h.smul (by simp [IsSelfAdjoint]))) (fun l => by simp [hu.2.2.1, hu'.2.2.1]) hr (fun z => by`.

Take `⟨i, j, hi, hj⟩` from `hchart z`. Rewrite using `[hrφ (i, j) z ⟨hi, hj⟩, valAt'_eq_unitVal _ (idx_chart _ _ _ _ _ _ hi (hFl z ▸ hj))]`. Conclude with `div_ne_zero (mul_ne_zero (Units.ne_zero _) (pow_ne_zero _ (u'.fr_ne _ _ hj))) (pow_ne_zero _ (u.fr_ne _ _ hi)))`. Use the proof step `(fun l z => by`. Take `⟨i, j, hi, hj⟩` from `hchart z`.

Establish `hi' : ⊤ ≤ (u.ex (z + l)).left ⁻¹ᵁ L.U i` using `by rwa [hper]`. Establish `hj' : ⊤ ≤ (u'.ex (F (z + l))).left ⁻¹ᵁ L'.U j` using `by rwa [hF, hper, ← hF]`. Establish `h1` using `hu.2.2.2 l i z hi`. Establish `h2` using `hu'.2.2.2 ⟨F l, hΛ l⟩ j (F z) hj`. Establish `h3 : χ l ≠ 0` using `norm_ne_zero_iff.1 (by rw [hu.2.2.1]; exact one_ne_zero)`.

Establish `h4 : χ' ⟨F l, hΛ l⟩ ≠ 0` using `norm_ne_zero_iff.1 (by rw [hu'.2.2.1]; exact one_ne_zero)`. Establish `h5` using `u.fr_ne _ _ hi'`. Rewrite using `[hrφ (i, j) z ⟨hi, hj⟩, hrφ (i, j) (z + l) ⟨hi', hj'⟩]`. Simplify using `only [hper, hermForm_sub_smul, hH₂, hermForm_pull, map_add]`. Rewrite using `[h1, h2]`.

Simplify using `only [hermForm]`. Generalize the expression as in `(z ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))) = a`. Generalize the expression as in `((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))) = b`. Generalize the expression as in `(F z ⬝ᵥ Hm'.mulVec (star (F l))) = a'`. Generalize the expression as in `(F l ⬝ᵥ Hm'.mulVec (star (F l))) = b'`.

Establish `e : Complex.exp (Real.pi * (n * a - m * a') + Real.pi / 2 * (n * b - m * b')) = Complex.exp (Real.pi * a + Real.pi / 2 * b) ^ n / Complex.exp (Real.pi * a' + Real.pi / 2 * b') ^ m`. Rewrite using `[← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_sub]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Establish `h6` using `Complex.exp_ne_zero (Real.pi * a + Real.pi / 2 * b)`.

Establish `h7` using `Complex.exp_ne_zero (Real.pi * a' + Real.pi / 2 * b')`. Rewrite using `[e]`. Generalize the expression as in `Complex.exp (Real.pi * a + Real.pi / 2 * b) = s at h6`. Generalize the expression as in `Complex.exp (Real.pi * a' + Real.pi / 2 * b') = s' at h7`. Simplify using `only [mul_pow]`.

Use the proof step `field_simp)`. Introduce `z v`. Establish `h` using `hermForm_sub_smul Hm H₂ n m z v`. Rewrite `h` using `[key.1, hH₂, hermForm_pull]`. Simplify using `only [hermForm, Matrix.zero_mulVec, dotProduct_zero] at h`.

Conclude with `(sub_eq_zero.1 h.symm).symm`.
-/
theorem hermForm_pull_eq_of_lbIso_pow :
    ∀ (A A' : Over (Sp ℂ)) [GrpObj A] [GrpObj A'] (L : LB A.left) (L' : LB A'.left), L.IsLB → L'.IsLB →
  ∀ (g g' : ℕ) (u : HolUnif A L g) (u' : HolUnif A' L' g') (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ)
    (Hm' : Matrix (Fin g') (Fin g') ℂ) (χ' : u'.Λ → ℂ), u.IsAH Hm χ → u'.IsAH Hm' χ' →
  ∀ (f : A ⟶ A') (F : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)), (∀ z, u'.ex (F z) = u.ex z ≫ f) →
  ∀ m n : ℕ, LBIso (lbPow (L'.pull f.left) m) (lbPow L n) →
  ∀ z w, (m : ℂ) * hermForm Hm' (F z) (F w) = (n : ℂ) * hermForm Hm z w := by
  intro A A' _ _ L L' hL hL' g g' u u' Hm χ Hm' χ' hu hu' f F hF m n ⟨w, hw⟩
  have hFl : ∀ z, (u'.ex (F z)).left = (u.ex z).left ≫ f.left := fun z => by
    rw [hF, Over.comp_left]
  have hΛ : ∀ l : u.Λ, F l ∈ u'.Λ := fun l => by
    rw [← u'.ker, hF, (u.ker l).2 l.2, ← (u.ker 0).2 u.Λ.zero_mem, ← hF, map_zero]
    exact (u'.ker 0).2 u'.Λ.zero_mem
  have hper : ∀ (l : u.Λ) z, u.ex (z + l) = u.ex z := fun l z => by
    rw [u.ex_add, (u.ker l).2 l.2, _root_.mul_one]
  have hFd : Differentiable ℂ F := (LinearMap.toContinuousLinearMap F).differentiable
  obtain ⟨r, hr, hrφ⟩ := exists_glue
    (fun p : L.ι × L'.ι => {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U p.1} ∩
      F ⁻¹' {z | ⊤ ≤ (u'.ex z).left ⁻¹ᵁ L'.U p.2})
    (fun p => (u.hol _ 0).1.inter ((u'.hol _ 0).1.preimage hFd.continuous))
    (fun z => by
      obtain ⟨i, hi⟩ := exists_chart (u.ex z).left hL
      obtain ⟨j, hj⟩ := exists_chart (u'.ex (F z)).left hL'
      exact ⟨(i, j), hi, hj⟩)
    (fun p z => valAt' (u.ex z).left _ (w.s (idx f.left m n p.1 p.2)).val *
      u'.fr p.2 (F z) ^ m / u.fr p.1 z ^ n)
    (fun p => by
      have d1 := (u.hol _ (w.s (idx f.left m n p.1 p.2)).val).2.mono
        (s := {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U p.1} ∩ F ⁻¹' {z | ⊤ ≤ (u'.ex z).left ⁻¹ᵁ L'.U p.2})
        fun z hz => idx_chart _ _ _ _ _ _ hz.1 (hFl z ▸ hz.2)
      have d2 := (u'.fr_hol p.2).comp
        (s := {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U p.1} ∩ F ⁻¹' {z | ⊤ ≤ (u'.ex z).left ⁻¹ᵁ L'.U p.2})
        hFd.differentiableOn fun z hz => hz.2
      have d3 := (u.fr_hol p.1).mono
        (s := {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U p.1} ∩ F ⁻¹' {z | ⊤ ≤ (u'.ex z).left ⁻¹ᵁ L'.U p.2})
        Set.inter_subset_left
      simp only [div_eq_mul_inv]
      exact (d1.mul (d2.pow m)).mul
        ((d3.pow n).inv fun z hz => pow_ne_zero n (u.fr_ne p.1 z hz.1)))
    (fun p q z hp hq => by
      have h := val_iso_pow (u.ex z).left f.left m n w hw p.1 q.1 p.2 q.2 hp.1 hq.1
        (hFl z ▸ hp.2) (hFl z ▸ hq.2)
      have h1 := u.fr_compat p.1 q.1 z (inf_of _ hp.1 hq.1)
      have h2 := u'.fr_compat p.2 q.2 (F z) (inf_of _ hp.2 hq.2)
      rw [hFl] at h2
      rw [div_eq_div_iff (pow_ne_zero _ (u.fr_ne _ _ hp.1)) (pow_ne_zero _ (u.fr_ne _ _ hq.1)),
        h1, h2, mul_pow, mul_pow, ← _root_.mul_assoc, h]
      ring)
  set H₂ := (LinearMap.toMatrix' F).transpose * Hm' * (LinearMap.toMatrix' F).transpose.conjTranspose
    with hH₂
  have hH₂h : H₂.IsHermitian := Matrix.isHermitian_mul_mul_conjTranspose _ hu'.1
  have hchart : ∀ z, ∃ i j, ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i ∧ ⊤ ≤ (u'.ex (F z)).left ⁻¹ᵁ L'.U j :=
    fun z => by
      obtain ⟨i, hi⟩ := exists_chart (u.ex z).left hL
      obtain ⟨j, hj⟩ := exists_chart (u'.ex (F z)).left hL'
      exact ⟨i, j, hi, hj⟩
  haveI := u.discrete
  have key := appellHumbert_trivial_of_nowhere_vanishing g u.Λ u.full
    ((n : ℂ) • Hm - (m : ℂ) • H₂) (fun l => χ l ^ n / χ' ⟨F l, hΛ l⟩ ^ m) r
    ((hu.1.smul (by simp [IsSelfAdjoint])).sub (hH₂h.smul (by simp [IsSelfAdjoint])))
    (fun l => by simp [hu.2.2.1, hu'.2.2.1]) hr
    (fun z => by
      obtain ⟨i, j, hi, hj⟩ := hchart z
      rw [hrφ (i, j) z ⟨hi, hj⟩, valAt'_eq_unitVal _ (idx_chart _ _ _ _ _ _ hi (hFl z ▸ hj))]
      exact div_ne_zero (mul_ne_zero (Units.ne_zero _) (pow_ne_zero _ (u'.fr_ne _ _ hj)))
        (pow_ne_zero _ (u.fr_ne _ _ hi)))
    (fun l z => by
      obtain ⟨i, j, hi, hj⟩ := hchart z
      have hi' : ⊤ ≤ (u.ex (z + l)).left ⁻¹ᵁ L.U i := by rwa [hper]
      have hj' : ⊤ ≤ (u'.ex (F (z + l))).left ⁻¹ᵁ L'.U j := by rwa [hF, hper, ← hF]
      have h1 := hu.2.2.2 l i z hi
      have h2 := hu'.2.2.2 ⟨F l, hΛ l⟩ j (F z) hj
      have h3 : χ l ≠ 0 := norm_ne_zero_iff.1 (by rw [hu.2.2.1]; exact one_ne_zero)
      have h4 : χ' ⟨F l, hΛ l⟩ ≠ 0 := norm_ne_zero_iff.1 (by rw [hu'.2.2.1]; exact one_ne_zero)
      have h5 := u.fr_ne _ _ hi'
      rw [hrφ (i, j) z ⟨hi, hj⟩, hrφ (i, j) (z + l) ⟨hi', hj'⟩]
      simp only [hper, hermForm_sub_smul, hH₂, hermForm_pull, map_add]
      rw [h1, h2]
      simp only [hermForm]
      generalize (z ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))) = a
      generalize ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))) = b
      generalize (F z ⬝ᵥ Hm'.mulVec (star (F l))) = a'
      generalize (F l ⬝ᵥ Hm'.mulVec (star (F l))) = b'
      have e : Complex.exp (Real.pi * (n * a - m * a') + Real.pi / 2 * (n * b - m * b')) =
          Complex.exp (Real.pi * a + Real.pi / 2 * b) ^ n /
            Complex.exp (Real.pi * a' + Real.pi / 2 * b') ^ m := by
        rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_sub]
        congr 1
        ring
      have h6 := Complex.exp_ne_zero (Real.pi * a + Real.pi / 2 * b)
      have h7 := Complex.exp_ne_zero (Real.pi * a' + Real.pi / 2 * b')
      rw [e]
      generalize Complex.exp (Real.pi * a + Real.pi / 2 * b) = s at h6
      generalize Complex.exp (Real.pi * a' + Real.pi / 2 * b') = s' at h7
      simp only [mul_pow]
      field_simp)
  intro z v
  have h := hermForm_sub_smul Hm H₂ n m z v
  rw [key.1, hH₂, hermForm_pull] at h
  simp only [hermForm, Matrix.zero_mulVec, dotProduct_zero] at h
  exact (sub_eq_zero.1 h.symm).symm

end GlobalTheory
