import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyEquivLocProdTriv
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuotientAverageAddOfPeriodicStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsStandardAdelicAddCharStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentColumnWhittakerTransformMirabolicInvariStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousUnipotentColumnWhittakerTransformStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentColumnWhittakerTransformColumnLawStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ColumnWhittakerTransformKeepsLaterLawStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuotientAverageUnipotentBlockColumnTransformEqZeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerLawUpperTriangularUnipotentAdelicStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsMirabolicWhittakerStageOfIsCuspFormStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentColumnWhittakerTransformNeZeroStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSplitAdelicMatrixLocalComponentStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalUpperUnipotentAdelicUpperUnipotentStatement

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric

namespace GlobalTheory.CuspRep.Generic

variable {E : Type} [Field E] [NumberField E] {a : ℕ} {ψ : AddChar (Ad E) ℂ}

/- English proof (translation)
The claim follows from `GlobalTheory.T.continuous_unipotentColumnWhittakerTransform E a ψ hψ m f hf left := GlobalTheory.T.unipotentColumnWhittakerTransform_mirabolic_invariant E a ψ hψ m f h hf law k hk y g := by rcases Nat.lt_or_ge (m + 1) k with h1 | h1 · exact GlobalTheory.T.columnWhittakerTransform …`.
-/
theorem good_colT (hψ : StdPsi ψ) {m : ℕ} {f : GA E a → ℂ} (h : m + 1 < a) (hf : Good ψ (m + 1) f) :
    Good ψ m (colT ψ (m + 1) f) where
  cont := GlobalTheory.T.continuous_unipotentColumnWhittakerTransform E a ψ hψ m f hf
  left := GlobalTheory.T.unipotentColumnWhittakerTransform_mirabolic_invariant E a ψ hψ m f h hf
  law k hk y g := by
    rcases Nat.lt_or_ge (m + 1) k with h1 | h1
    · exact GlobalTheory.T.columnWhittakerTransform_keeps_later_law E a ψ m f hf k h1 y g
    · obtain rfl : k = m + 1 := by omega
      exact GlobalTheory.T.unipotentColumnWhittakerTransform_column_law E a ψ hψ m f hf y g
  van := GlobalTheory.T.quotientAverage_unipotentBlock_columnTransform_eq_zero E a ψ hψ m f h hf

/- English proof (translation)
Use `hf.left _ (fun i j h => isMir_blkU c i j ?_) g` and prove the remaining obligations. Use linear arithmetic over natural numbers and integers.
-/
theorem hl_of_good {m : ℕ} {f : GA E a → ℂ} (hf : Good ψ m f) {k : ℕ} (hk : k ≤ m) (c : UnipotentBlockColumnIndex a k k → E) (g : GA E a) :
    f (ratGL E a (blkU c) * g) = f g := by
  refine hf.left _ (fun i j h => isMir_blkU c i j ?_) g
  omega

/- English proof (translation)
Use function extensionality and compare the values at `g`. Use `GlobalTheory.T.quotientAverage_add_of_periodic _ (ratV E (UnipotentBlockColumnIndex a (m + 1) (m + 1))) (isCoLat_ratV E _) _ _ (per_coef hψ (eLast a (m + 1)) hf.cont (hl_of_good hf le_rfl) g) (per_coef hψ (eLast a (m + 1)) hf'.cont (hl_of_good hf' le_rfl) g)` as an intermediate fact. Simplify using `only [colT, coefF, mul_add]`. Conclude with `this`.
-/
theorem colT_add (hψ : StdPsi ψ) {m : ℕ} {f f' : GA E a → ℂ} (hf : Good ψ (m + 1) f) (hf' : Good ψ (m + 1) f') :
    colT ψ (m + 1) (fun g => f g + f' g) = fun g => colT ψ (m + 1) f g + colT ψ (m + 1) f' g := by
  funext g
  have := GlobalTheory.T.quotientAverage_add_of_periodic _ (ratV E (UnipotentBlockColumnIndex a (m + 1) (m + 1))) (isCoLat_ratV E _) _ _
    (per_coef hψ (eLast a (m + 1)) hf.cont (hl_of_good hf le_rfl) g)
    (per_coef hψ (eLast a (m + 1)) hf'.cont (hl_of_good hf' le_rfl) g)
  simp only [colT, coefF, mul_add]
  exact this

/- English proof (translation)
Use function extensionality and compare the values at `g`. Simplify using `only [colT, coefF]`. Rewrite using `[← avg_const_mul]`. Use `congr 1`. Use function extensionality and compare the values at `x`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem colT_smul (m : ℕ) (c : ℂ) (f : GA E a → ℂ) :
    colT ψ (m + 1) (fun g => c * f g) = fun g => c * colT ψ (m + 1) f g := by
  funext g
  simp only [colT, coefF]
  rw [← avg_const_mul]
  congr 1
  funext x
  ring

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => exact fun _ f hf => ⟨hf, id⟩`. Consider the case `succ m ih`. Introduce `h f hf`. Establish `h1 : m + 1 < a` using `by omega`.

Take `⟨h2, h3⟩` from `ih (Or.inl (by omega)) (good_colT hψ h1 hf)`. Conclude with `⟨h2, fun h0 => h3 (GlobalTheory.T.unipotentColumnWhittakerTransform_ne_zero E a ψ hψ m f h1 hf h0)⟩`.
-/
theorem whit_good (hψ : StdPsi ψ) (m : ℕ) : (m < a ∨ m = 0) → ∀ {f : GA E a → ℂ}, Good ψ m f →
    Good ψ 0 (whit ψ m f) ∧ (f ≠ 0 → whit ψ m f ≠ 0) := by
  induction m with
  | zero => exact fun _ f hf => ⟨hf, id⟩
  | succ m ih =>
    intro h f hf
    have h1 : m + 1 < a := by omega
    obtain ⟨h2, h3⟩ := ih (Or.inl (by omega)) (good_colT hψ h1 hf)
    exact ⟨h2, fun h0 => h3 (GlobalTheory.T.unipotentColumnWhittakerTransform_ne_zero E a ψ hψ m f h1 hf h0)⟩

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => exact fun _ f f' _ _ => rfl`. Consider the case `succ m ih`. Introduce `h f f' hf hf'`. Establish `h1 : m + 1 < a` using `by omega`.

Rewrite using `[whit_succ, whit_succ, whit_succ, colT_add hψ hf hf']`. Conclude with `ih (Or.inl (by omega)) (good_colT hψ h1 hf) (good_colT hψ h1 hf')`.
-/
theorem whit_add (hψ : StdPsi ψ) (m : ℕ) : (m < a ∨ m = 0) → ∀ {f f' : GA E a → ℂ}, Good ψ m f → Good ψ m f' →
    whit ψ m (fun g => f g + f' g) = fun g => whit ψ m f g + whit ψ m f' g := by
  induction m with
  | zero => exact fun _ f f' _ _ => rfl
  | succ m ih =>
    intro h f f' hf hf'
    have h1 : m + 1 < a := by omega
    rw [whit_succ, whit_succ, whit_succ, colT_add hψ hf hf']
    exact ih (Or.inl (by omega)) (good_colT hψ h1 hf) (good_colT hψ h1 hf')

/- English proof (translation)
Proceed by induction on `m generalizing f with`. Consider the case `zero => rfl`. Consider the case `succ m ih => rw [whit_succ, whit_succ, colT_smul, ih]`.
-/
theorem whit_smul (m : ℕ) (c : ℂ) (f : GA E a → ℂ) : whit ψ m (fun g => c * f g) = fun g => c * whit ψ m f g := by
  induction m generalizing f with
  | zero => rfl
  | succ m ih => rw [whit_succ, whit_succ, colT_smul, ih]

/- English proof (translation)
Proceed by induction on `m generalizing f g with`. Consider the case `zero => rfl`. Consider the case `succ m ih`. Rewrite using `[whit_succ, whit_succ, ← ih]`. Use `congr 1`.

Use function extensionality and compare the values at `x`. Simplify using `only [colT, coefF, mul_assoc]`.
-/
theorem whit_rt (m : ℕ) (f : GA E a → ℂ) (h g : GA E a) : whit ψ m (fun x => f (x * h)) g = whit ψ m f (g * h) := by
  induction m generalizing f g with
  | zero => rfl
  | succ m ih =>
    rw [whit_succ, whit_succ, ← ih]
    congr 1
    funext x
    simp only [colT, coefF, mul_assoc]

def locPsi (hψ : StdPsi ψ) (w : HeightOneSpectrum (𝓞 E)) : AddChar (w.adicCompletion E) Circle where
  toFun y := ⟨ψ (sFin E (sLoc E w y)), by simpa [Submonoid.unitSphere] using hψ.norm _⟩
  map_zero_eq_one' := by
    apply Circle.ext
    simp
  map_add_eq_mul' x y := by
    apply Circle.ext
    change ψ (sFin E (sLoc E w (x + y))) = ψ (sFin E (sLoc E w x)) * ψ (sFin E (sLoc E w y))
    rw [map_add, map_add, AddChar.map_add_eq_mul]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coe_locPsi (hψ : StdPsi ψ) (w : HeightOneSpectrum (𝓞 E)) (y : w.adicCompletion E) :
    (locPsi hψ w y : ℂ) = ψ (sFin E (sLoc E w y)) := rfl

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField in

/- English proof (translation)
Introduce and unpack `E _ _ _ a P w σ ⟨f, hf0, hf⟩`. Take `⟨ψ, hψ⟩` from `GlobalTheory.T.exists_standardAdelicAddChar E`. Establish `hg : ∀ v, Good ψ (a - 1) (f v).1.1` using `fun v => GlobalTheory.T.isMirabolicWhittakerStage_of_isCuspForm E a ψ (f v).1 (P.cusp _ (f v).2)`. Establish `h0 : a - 1 < a ∨ a - 1 = 0` using `by omega`. Choose the witnesses or unpack the hypotheses as in `⟨v₀, hv₀⟩ : ∃ v, f v ≠ 0 := by`.

Assume the negation of the conclusion as `h`. Use `push Not at h`. Conclude with `hf0 (LinearMap.ext h)`. Establish `hv1 : (f v₀).1.1 ≠ 0` using `fun h => hv₀ (Subtype.ext (Subtype.ext h))`. Take `⟨g₀, hg₀⟩` from `Function.ne_iff.1 ((whit_good hψ (a - 1) h0 (hg v₀)).2 hv1)`.

Take `⟨h, gw, e, hc⟩` from `GlobalTheory.T.exists_split_adelicMatrix_localComponent E a w g₀`. Establish `hrt : ∀ u v x, whit ψ (a - 1) (f (σ.ρ u v)).1.1 x = whit ψ (a - 1) (f v).1.1 (x * finGL E a (locGL E a w u))` using `fun u v x => by`. Rewrite using `[hf u v]`. Conclude with `whit_rt _ _ _ _`. Set `l : σ.V →ₗ[ℂ] ℂ` to `{ toFun := fun v => whit ψ (a - 1) (f v).1.1 h map_add' := fun v v' => by`.

Rewrite using `[map_add f]`. Conclude with `congrFun (whit_add hψ (a - 1) h0 (hg v) (hg v')) h`. Use the proof step `map_smul' := fun c v => by`. Rewrite using `[map_smul f]`. Conclude with `congrFun (whit_smul (a - 1) c (f v).1.1) h }`.

Establish `hl : ∀ v, l v = whit ψ (a - 1) (f v).1.1 h` using `fun _ => rfl`. Establish `hne : l (σ.ρ gw v₀) ≠ 0`. Rewrite using `[hl, hrt, ← e]`. Conclude with `hg₀`. Establish `hlaw : ∀ (u : GlobalTheory.SmGL.unipB (w.adicCompletion E) (Fin a)) v, l (σ.ρ u v) = (locPsi hψ w (∑ p : Fin a × Fin a with (p.2 : ℕ) = p.1 + 1, (u : GL (Fin a) (w.adicCompletion E)).val p.1 p.2) : ℂ) * l v`.

Introduce `u v`. Take `⟨u1, u2⟩` from `(GlobalTheory.SmGL.mem_unipB _).1 u.2`. Take `⟨t1, t2, t3⟩` from `GlobalTheory.T.localUpperUnipotent_adelic_upperUnipotent E a w u u1 u2`. Establish `hlw` using `(whit_good hψ (a - 1) h0 (hg v)).1.law`. Use `GlobalTheory.T.whittakerLaw_upperTriangularUnipotent_adelic E a ψ _ (fun k hk => hlw k hk) _ t1 t2 h` as an intermediate fact.

Rewrite using `[hl, hrt, hc, this, t3]`. Both sides reduce to the same expression. Use `⟨locPsi hψ w, ?_, fun h1 => ?_, ?_⟩` and prove the remaining obligations. Use `Continuous.subtype_mk (hψ.cont.comp ?_) _` and prove the remaining obligations. Conclude with `(continuous_const.prodMk continuous_id : Continuous fun x : Af E => ((0, x) : InfiniteAdeleRing E × Af E)).comp (CuspSub.continuous_sLoc w)`.

Take `⟨y, hy⟩` from `hψ.loc w`. Apply `hy` to reduce the goal to its premises. Use `congrArg (fun c : Circle => (c : ℂ)) (DFunLike.congr_fun h1 y)` as an intermediate fact. Simplify `this` using `[coe_locPsi]`. Use `Submodule.Quotient.nontrivial_iff.2 fun htop => hne ?_` and prove the remaining obligations.

Establish `hle : GlobalTheory.PRep.twKer σ.ρ (GlobalTheory.SmGL.unipB (w.adicCompletion E) (Fin a)) (GlobalTheory.LocGL.whitChar (locPsi hψ w) a) ≤ LinearMap.ker l`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨u, v, rfl⟩`. Simplify using `only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, map_smul, hlaw, smul_eq_mul]`. Conclude with `sub_eq_zero.2 rfl`.

Conclude with `hle (htop ▸ Submodule.mem_top)`.
-/
theorem isGeneric_of_isLocComp : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (P : CuspSub E a)
    (w : HeightOneSpectrum (𝓞 E)) (σ : SmIrr (GL (Fin a) (w.adicCompletion E))), P.IsLocComp w σ →
    GlobalTheory.LocGL.IsGeneric σ.ρ := by
  rintro E _ _ _ a P w σ ⟨f, hf0, hf⟩
  obtain ⟨ψ, hψ⟩ := GlobalTheory.T.exists_standardAdelicAddChar E
  have hg : ∀ v, Good ψ (a - 1) (f v).1.1 := fun v => GlobalTheory.T.isMirabolicWhittakerStage_of_isCuspForm E a ψ (f v).1 (P.cusp _ (f v).2)
  have h0 : a - 1 < a ∨ a - 1 = 0 := by omega
  obtain ⟨v₀, hv₀⟩ : ∃ v, f v ≠ 0 := by
    by_contra h
    push Not at h
    exact hf0 (LinearMap.ext h)
  have hv1 : (f v₀).1.1 ≠ 0 := fun h => hv₀ (Subtype.ext (Subtype.ext h))
  obtain ⟨g₀, hg₀⟩ := Function.ne_iff.1 ((whit_good hψ (a - 1) h0 (hg v₀)).2 hv1)
  obtain ⟨h, gw, e, hc⟩ := GlobalTheory.T.exists_split_adelicMatrix_localComponent E a w g₀
  have hrt : ∀ u v x, whit ψ (a - 1) (f (σ.ρ u v)).1.1 x =
      whit ψ (a - 1) (f v).1.1 (x * finGL E a (locGL E a w u)) := fun u v x => by
    rw [hf u v]
    exact whit_rt _ _ _ _
  let l : σ.V →ₗ[ℂ] ℂ :=
    { toFun := fun v => whit ψ (a - 1) (f v).1.1 h
      map_add' := fun v v' => by
        rw [map_add f]
        exact congrFun (whit_add hψ (a - 1) h0 (hg v) (hg v')) h
      map_smul' := fun c v => by
        rw [map_smul f]
        exact congrFun (whit_smul (a - 1) c (f v).1.1) h }
  have hl : ∀ v, l v = whit ψ (a - 1) (f v).1.1 h := fun _ => rfl
  have hne : l (σ.ρ gw v₀) ≠ 0 := by
    rw [hl, hrt, ← e]
    exact hg₀
  have hlaw : ∀ (u : GlobalTheory.SmGL.unipB (w.adicCompletion E) (Fin a)) v,
      l (σ.ρ u v) = (locPsi hψ w (∑ p : Fin a × Fin a with (p.2 : ℕ) = p.1 + 1, (u : GL (Fin a) (w.adicCompletion E)).val p.1 p.2) : ℂ) * l v := by
    intro u v
    obtain ⟨u1, u2⟩ := (GlobalTheory.SmGL.mem_unipB _).1 u.2
    obtain ⟨t1, t2, t3⟩ := GlobalTheory.T.localUpperUnipotent_adelic_upperUnipotent E a w u u1 u2
    have hlw := (whit_good hψ (a - 1) h0 (hg v)).1.law
    have := GlobalTheory.T.whittakerLaw_upperTriangularUnipotent_adelic E a ψ _ (fun k hk => hlw k hk) _ t1 t2 h
    rw [hl, hrt, hc, this, t3]
    rfl
  refine ⟨locPsi hψ w, ?_, fun h1 => ?_, ?_⟩
  · refine Continuous.subtype_mk (hψ.cont.comp ?_) _
    exact (continuous_const.prodMk continuous_id : Continuous fun x : Af E => ((0, x) : InfiniteAdeleRing E × Af E)).comp
      (CuspSub.continuous_sLoc w)
  · obtain ⟨y, hy⟩ := hψ.loc w
    apply hy
    have := congrArg (fun c : Circle => (c : ℂ)) (DFunLike.congr_fun h1 y)
    simpa [coe_locPsi] using this
  · refine Submodule.Quotient.nontrivial_iff.2 fun htop => hne ?_
    have hle : GlobalTheory.PRep.twKer σ.ρ (GlobalTheory.SmGL.unipB (w.adicCompletion E) (Fin a)) (GlobalTheory.LocGL.whitChar (locPsi hψ w) a) ≤
        LinearMap.ker l := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨u, v, rfl⟩
      simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, map_smul, hlaw, smul_eq_mul]
      exact sub_eq_zero.2 rfl
    exact hle (htop ▸ Submodule.mem_top)

end GlobalTheory.CuspRep.Generic
