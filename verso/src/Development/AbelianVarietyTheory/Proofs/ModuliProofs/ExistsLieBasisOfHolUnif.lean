import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.ChartLaw
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

noncomputable section

namespace GlobalTheory.UnifLieBasis

open TangentOrigin
open ReciprocityTheory.ChartRestriction.G.Chart (JetR jetAug qD rD scaleD IsTan isTan_iff prodPts isLieComb_iff)

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)

/- English proof (translation)
Introduce `q`. Establish `: q ∈ Set.range (PrimeSpectrum.comap (jetAug ℂ (Fin 2) 1).toRingHom)`. Rewrite using `[range_comap_of_surjective _ _ (fun a => ⟨algebraMap ℂ _ a, (jetAug ℂ (Fin 2) 1).commutes a⟩)]`. Introduce `b hb`. Use `q.2.mem_of_pow_mem (1 + 1) ?_` and prove the remaining obligations.

Establish `h` using `Ideal.pow_mem_pow (I := RingHom.ker (jetAug ℂ (Fin 2) 1)) hb (1 + 1)`. Rewrite `h` using `[Chart.ker_jetAug_pow, Ideal.mem_bot]`. Rewrite using `[h]`. Conclude with `zero_mem _`. Conclude with `this`.
-/
theorem spMap_jetAug_surjective :
    Function.Surjective (spMap (jetAug ℂ (Fin 2) 1).toRingHom) := by
  intro q
  have : q ∈ Set.range (PrimeSpectrum.comap (jetAug ℂ (Fin 2) 1).toRingHom) := by
    rw [range_comap_of_surjective _ _ (fun a => ⟨algebraMap ℂ _ a, (jetAug ℂ (Fin 2) 1).commutes a⟩)]
    intro b hb
    refine q.2.mem_of_pow_mem (1 + 1) ?_
    have h := Ideal.pow_mem_pow (I := RingHom.ker (jetAug ℂ (Fin 2) 1)) hb (1 + 1)
    rw [Chart.ker_jetAug_pow, Ideal.mem_bot] at h
    rw [h]
    exact zero_mem _
  exact this

omit u in

/- English proof (translation)
Set `P : Chart.sp (R₀` to `ℂ) (JetR ℂ (Fin 2) 1) ⟶ A := (Chart.spMap (qD 0) ≫ v) * (Chart.spMap (qD 1) ≫ v')`. Establish `hP : Chart.spMap (jetAug ℂ (Fin 2) 1) ≫ P = 1`. Rewrite using `[MonObj.comp_mul, ← Category.assoc, ← Category.assoc, Chart.spMap_comp, Chart.spMap_comp, Chart.jetAug_comp_qD, Chart.jetAug_comp_qD, hv, hv', _root_.mul_one]`. Establish `hPU : ⊤ ≤ P.left ⁻¹ᵁ U` using `fun p _ => by`. Take `⟨q, rfl⟩` from `spMap_jetAug_surjective p`.

Rewrite `h0` using `[← hP]`. Conclude with `h0 (Set.mem_univ q)`. Establish `hval : ∀ l : ℂ × ℂ →ₗ[ℂ] ℂ, Chart.spMap (rD l) ≫ P = (Chart.spMap (scaleD (l ((1 : ℂ), (0 : ℂ)))) ≫ v) * (Chart.spMap (scaleD (l ((0 : ℂ), (1 : ℂ)))) ≫ v')`. Introduce `l`. Rewrite using `[MonObj.comp_mul, ← Category.assoc, ← Category.assoc, Chart.spMap_comp, Chart.spMap_comp, Chart.restrictDiag_comp_incl_fst, Chart.restrictDiag_comp_incl_snd]`.

Establish `key : ∀ (l : ℂ × ℂ →ₗ[ℂ] ℂ) (w : epsR ℂ ⟶ A) (hw : ⊤ ≤ w.left ⁻¹ᵁ U), Chart.spMap (rD l) ≫ P = w → evalPt (R` using `DualNumber ℂ) w.left U hw f = rD l (evalPt (R := JetR ℂ (Fin 2) 1) P.left U hPU f) := by`. Introduce and unpack `l w hw rfl`. Conclude with `evalPt_spMap_comp (rD l : JetR ℂ (Fin 2) 1 →+* DualNumber ℂ) P.left U hPU hw f`. Rewrite using `[key (LinearMap.fst ℂ ℂ ℂ) v h, key (LinearMap.snd ℂ ℂ ℂ) v' h', key (LinearMap.fst ℂ ℂ ℂ + LinearMap.snd ℂ ℂ ℂ) (v * v') h'', Chart.snd_rD_add]`. Rewrite using `[hval]`.

Simplify using `only [LinearMap.add_apply, LinearMap.fst_apply, LinearMap.snd_apply, add_zero, zero_add]`. Rewrite using `[Chart.scaleD_one, Chart.spMap_id, Category.id_comp, Category.id_comp]`. Rewrite using `[hval]`. Simplify using `only [LinearMap.fst_apply, LinearMap.snd_apply]`. Rewrite using `[Chart.scaleD_one, Chart.spMap_id, Category.id_comp, Chart.spMap_scaleD_zero hv, _root_.one_mul]`.

Rewrite using `[hval]`. Simplify using `only [LinearMap.fst_apply, LinearMap.snd_apply]`. Rewrite using `[Chart.scaleD_one, Chart.spMap_id, Category.id_comp, Chart.spMap_scaleD_zero hv', _root_.mul_one]`.
-/
theorem snd_evalPt_mul {v v' : epsR ℂ ⟶ A} (hv : IsTan (R := ℂ) (G := A) v) (hv' : IsTan (R := ℂ) (G := A) v')
    (U : A.left.Opens) (h0 : ⊤ ≤ (1 : Chart.sp (R₀ := ℂ) ℂ ⟶ A).left ⁻¹ᵁ U)
    (h : ⊤ ≤ v.left ⁻¹ᵁ U) (h' : ⊤ ≤ v'.left ⁻¹ᵁ U) (h'' : ⊤ ≤ (v * v').left ⁻¹ᵁ U) (f : Γ(A.left, U)) :
    (evalPt (R := DualNumber ℂ) (v * v').left U h'' f).snd =
      (evalPt (R := DualNumber ℂ) v.left U h f).snd + (evalPt (R := DualNumber ℂ) v'.left U h' f).snd := by
  let P : Chart.sp (R₀ := ℂ) (JetR ℂ (Fin 2) 1) ⟶ A := (Chart.spMap (qD 0) ≫ v) * (Chart.spMap (qD 1) ≫ v')
  have hP : Chart.spMap (jetAug ℂ (Fin 2) 1) ≫ P = 1 := by
    rw [MonObj.comp_mul, ← Category.assoc, ← Category.assoc, Chart.spMap_comp, Chart.spMap_comp,
      Chart.jetAug_comp_qD, Chart.jetAug_comp_qD, hv, hv', _root_.mul_one]
  have hPU : ⊤ ≤ P.left ⁻¹ᵁ U := fun p _ => by
    obtain ⟨q, rfl⟩ := spMap_jetAug_surjective p
    rw [← hP] at h0
    exact h0 (Set.mem_univ q)
  have hval : ∀ l : ℂ × ℂ →ₗ[ℂ] ℂ, Chart.spMap (rD l) ≫ P =
      (Chart.spMap (scaleD (l ((1 : ℂ), (0 : ℂ)))) ≫ v) * (Chart.spMap (scaleD (l ((0 : ℂ), (1 : ℂ)))) ≫ v') := by
    intro l
    rw [MonObj.comp_mul, ← Category.assoc, ← Category.assoc, Chart.spMap_comp, Chart.spMap_comp,
      Chart.restrictDiag_comp_incl_fst, Chart.restrictDiag_comp_incl_snd]
  have key : ∀ (l : ℂ × ℂ →ₗ[ℂ] ℂ) (w : epsR ℂ ⟶ A) (hw : ⊤ ≤ w.left ⁻¹ᵁ U), Chart.spMap (rD l) ≫ P = w →
      evalPt (R := DualNumber ℂ) w.left U hw f = rD l (evalPt (R := JetR ℂ (Fin 2) 1) P.left U hPU f) := by
    rintro l w hw rfl
    exact evalPt_spMap_comp (rD l : JetR ℂ (Fin 2) 1 →+* DualNumber ℂ) P.left U hPU hw f
  rw [key (LinearMap.fst ℂ ℂ ℂ) v h, key (LinearMap.snd ℂ ℂ ℂ) v' h',
    key (LinearMap.fst ℂ ℂ ℂ + LinearMap.snd ℂ ℂ ℂ) (v * v') h'', Chart.snd_rD_add]
  · rw [hval]
    simp only [LinearMap.add_apply, LinearMap.fst_apply, LinearMap.snd_apply, add_zero, zero_add]
    rw [Chart.scaleD_one, Chart.spMap_id, Category.id_comp, Category.id_comp]
  · rw [hval]
    simp only [LinearMap.fst_apply, LinearMap.snd_apply]
    rw [Chart.scaleD_one, Chart.spMap_id, Category.id_comp, Chart.spMap_scaleD_zero hv, _root_.one_mul]
  · rw [hval]
    simp only [LinearMap.fst_apply, LinearMap.snd_apply]
    rw [Chart.scaleD_one, Chart.spMap_id, Category.id_comp, Chart.spMap_scaleD_zero hv', _root_.mul_one]

/- English proof (translation)
Introduce `U h'' f`. Establish `ht` using `Chart.isTan_mul hv hv'`. Establish `h0` using `(tangent_mem_iff (u := u) ((isTan_iff _).1 ht) U).1 h''`. Establish `h` using `(tangent_mem_iff (u := u) ((isTan_iff _).1 hv) U).2 h0`. Establish `h'` using `(tangent_mem_iff (u := u) ((isTan_iff _).1 hv') U).2 h0`.

Establish `h1 : ⊤ ≤ (1 : Chart.sp (R₀` using `ℂ) ℂ ⟶ A).left ⁻¹ᵁ U := by`. Rewrite using `[← hv]`. Conclude with `fun p _ => h (Set.mem_univ _)`. Rewrite using `[map_add, ← hd U h f, ← hd' U h' f]`. Conclude with `snd_evalPt_mul hv hv' U h1 h h' h'' f`.
-/
theorem isDiff_add {w w' : Fin g → ℂ} {v v' : epsR ℂ ⟶ A} (hv : IsTan (R := ℂ) (G := A) v)
    (hv' : IsTan (R := ℂ) (G := A) v') (hd : u.IsDiff w v) (hd' : u.IsDiff w' v') : u.IsDiff (w + w') (v * v') := by
  intro U h'' f
  have ht := Chart.isTan_mul hv hv'
  have h0 := (tangent_mem_iff (u := u) ((isTan_iff _).1 ht) U).1 h''
  have h := (tangent_mem_iff (u := u) ((isTan_iff _).1 hv) U).2 h0
  have h' := (tangent_mem_iff (u := u) ((isTan_iff _).1 hv') U).2 h0
  have h1 : ⊤ ≤ (1 : Chart.sp (R₀ := ℂ) ℂ ⟶ A).left ⁻¹ᵁ U := by
    rw [← hv]
    exact fun p _ => h (Set.mem_univ _)
  rw [map_add, ← hd U h f, ← hd' U h' f]
  exact snd_evalPt_mul hv hv' U h1 h h' h'' f

/- English proof (translation)
Introduce `U h' f`. Establish `h0` using `(tangent_mem_iff (u := u) ((isTan_iff _).1 (Chart.isTan_scale c hv)) U).1 h'`. Establish `h` using `(tangent_mem_iff (u := u) ((isTan_iff _).1 hv) U).2 h0`. Rewrite using `[map_smul, ← hd U h f]`. Use `(congrArg TrivSqZeroExt.snd (evalPt_spMap_comp (scaleD c : DualNumber ℂ →+* DualNumber ℂ) v.left U h h' f)).trans ?_` and prove the remaining obligations.

Conclude with `TrivSqZeroExt.snd_map _ _`.
-/
theorem isDiff_smul {w : Fin g → ℂ} {v : epsR ℂ ⟶ A} (hv : IsTan (R := ℂ) (G := A) v) (hd : u.IsDiff w v) (c : ℂ) :
    u.IsDiff (c • w) (Chart.spMap (scaleD c) ≫ v) := by
  intro U h' f
  have h0 := (tangent_mem_iff (u := u) ((isTan_iff _).1 (Chart.isTan_scale c hv)) U).1 h'
  have h := (tangent_mem_iff (u := u) ((isTan_iff _).1 hv) U).2 h0
  rw [map_smul, ← hd U h f]
  refine (congrArg TrivSqZeroExt.snd
    (evalPt_spMap_comp (scaleD c : DualNumber ℂ →+* DualNumber ℂ) v.left U h h' f)).trans ?_
  exact TrivSqZeroExt.snd_map _ _

/- English proof (translation)
Introduce `U h f`. Establish `ht : IsTan (R` using `ℂ) (G := A) (1 : epsR ℂ ⟶ A) := Chart.isTan_one`. Establish `h1 : ⊤ ≤ (1 : Chart.sp (R₀` using `ℂ) ℂ ⟶ A).left ⁻¹ᵁ U := by`. Rewrite using `[← ht]`. Conclude with `fun p _ => h (Set.mem_univ _)`.

Establish `key : ∀ (w : epsR ℂ ⟶ A) (hw : ⊤ ≤ w.left ⁻¹ᵁ U), w = 1 → (evalPt (R` using `DualNumber ℂ) w.left U hw f).snd = (evalPt (R := DualNumber ℂ) (1 : epsR ℂ ⟶ A).left U h f).snd := by`. Introduce and unpack `w hw rfl`. Both sides reduce to the same expression. Establish `h2 : ⊤ ≤ (1 * 1 : epsR ℂ ⟶ A).left ⁻¹ᵁ U` using `by rwa [_root_.mul_one]`. Use `snd_evalPt_mul ht ht U h1 h h h2 f` as an intermediate fact.

Rewrite `this` using `[key _ h2 (_root_.mul_one _)]`. Rewrite using `[map_zero]`. Conclude with `left_eq_add.1 this`.
-/
theorem isDiff_zero : u.IsDiff 0 (1 : epsR ℂ ⟶ A) := by
  intro U h f
  have ht : IsTan (R := ℂ) (G := A) (1 : epsR ℂ ⟶ A) := Chart.isTan_one
  have h1 : ⊤ ≤ (1 : Chart.sp (R₀ := ℂ) ℂ ⟶ A).left ⁻¹ᵁ U := by
    rw [← ht]
    exact fun p _ => h (Set.mem_univ _)
  have key : ∀ (w : epsR ℂ ⟶ A) (hw : ⊤ ≤ w.left ⁻¹ᵁ U), w = 1 →
      (evalPt (R := DualNumber ℂ) w.left U hw f).snd = (evalPt (R := DualNumber ℂ) (1 : epsR ℂ ⟶ A).left U h f).snd := by
    rintro w hw rfl
    rfl
  have h2 : ⊤ ≤ (1 * 1 : epsR ℂ ⟶ A).left ⁻¹ᵁ U := by rwa [_root_.mul_one]
  have := snd_evalPt_mul ht ht U h1 h h h2 f
  rw [key _ h2 (_root_.mul_one _)] at this
  rw [map_zero]
  exact left_eq_add.1 this

/- English proof (translation)
The claim follows from `| 0, w, v, _, _ => by simp only [List.ofFn_zero, List.prod_nil, Finset.univ_eq_empty, Finset.sum_empty] exact ⟨Chart.isTan_one, isDiff_zero u⟩ | k + 1, w, v, hv, hd => by obtain ⟨h1, h2⟩ := isDiff_list_prod (fun i => w i.succ) (fun i => v i.succ) (fun i => hv _) (fun i => hd _) r …`.
-/
theorem isDiff_list_prod : ∀ {k : ℕ} (w : Fin k → Fin g → ℂ) (v : Fin k → (epsR ℂ ⟶ A)),
    (∀ i, IsTan (R := ℂ) (G := A) (v i)) → (∀ i, u.IsDiff (w i) (v i)) →
    IsTan (R := ℂ) (G := A) (List.ofFn v).prod ∧ u.IsDiff (∑ i, w i) (List.ofFn v).prod
  | 0, w, v, _, _ => by
    simp only [List.ofFn_zero, List.prod_nil, Finset.univ_eq_empty, Finset.sum_empty]
    exact ⟨Chart.isTan_one, isDiff_zero u⟩
  | k + 1, w, v, hv, hd => by
    obtain ⟨h1, h2⟩ := isDiff_list_prod (fun i => w i.succ) (fun i => v i.succ) (fun i => hv _) (fun i => hd _)
    rw [List.ofFn_succ, List.prod_cons, Fin.sum_univ_succ]
    exact ⟨Chart.isTan_mul (hv 0) h1, isDiff_add u (hv 0) h1 (hd 0) h2⟩

/- English proof (translation)
Unfold `IsTangent at hv ⊢`. Rewrite using `[Over.comp_left, ← Category.assoc, hv, ← Over.comp_left, IsMonHom.one_hom]`.
-/
theorem isTangent_comp (f : A ⟶ A) [IsMonHom f] {v : epsR ℂ ⟶ A} (hv : IsTangent v) : IsTangent (v ≫ f) := by
  unfold IsTangent at hv ⊢
  rw [Over.comp_left, ← Category.assoc, hv, ← Over.comp_left, IsMonHom.one_hom]

/- English proof (translation)
Introduce `U h s`. Establish `h1` using `hd (f.left ⁻¹ᵁ U) h ((f.left.app U).hom s)`. Establish `e : ((v ≫ f).left.appLE U ⊤ h).hom s = (v.left.appLE (f.left ⁻¹ᵁ U) ⊤ h).hom ((f.left.app U).hom s)`. Use `Scheme.Hom.comp_appLE v.left f.left U ⊤ h` as an intermediate fact. Conclude with `congrArg (fun φ => φ.hom s) this`.

Establish `hdiff` using `differentiableAt_val u ((tangent_mem_iff (u := u) (isTangent_comp f hv) U).1 h) s`. Establish `hfun : (fun z => valAt' (u.ex z).left (f.left ⁻¹ᵁ U) ((f.left.app U).hom s)) = (fun z => valAt' (u.ex z).left U s) ∘ F`. Use function extensionality and compare the values at `z`. Rewrite using `[valAt'_comp, Function.comp_apply, hF]`. Both sides reduce to the same expression.

Establish `hch` using `(HasFDerivAt.comp (0 : Fin g → ℂ) (f := F) (by rw [map_zero]; exact hdiff.hasFDerivAt) F.hasFDerivAt).fderiv`. Rewrite `h1` using `[hfun, hch]`. Rewrite using `[e]`. Conclude with `h1`.
-/
theorem isDiff_comp (f : A ⟶ A) [IsMonHom f] (F : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ))
    (hF : ∀ z, u.ex (F z) = u.ex z ≫ f) {w : Fin g → ℂ} {v : epsR ℂ ⟶ A}
    (hv : IsTangent v) (hd : u.IsDiff w v) : u.IsDiff (F w) (v ≫ f) := by
  intro U h s
  have h1 := hd (f.left ⁻¹ᵁ U) h ((f.left.app U).hom s)
  have e : ((v ≫ f).left.appLE U ⊤ h).hom s =
      (v.left.appLE (f.left ⁻¹ᵁ U) ⊤ h).hom ((f.left.app U).hom s) := by
    have := Scheme.Hom.comp_appLE v.left f.left U ⊤ h
    exact congrArg (fun φ => φ.hom s) this
  have hdiff := differentiableAt_val u ((tangent_mem_iff (u := u) (isTangent_comp f hv) U).1 h) s
  have hfun : (fun z => valAt' (u.ex z).left (f.left ⁻¹ᵁ U) ((f.left.app U).hom s)) =
      (fun z => valAt' (u.ex z).left U s) ∘ F := by
    funext z
    rw [valAt'_comp, Function.comp_apply, hF]
    rfl
  have hch := (HasFDerivAt.comp (0 : Fin g → ℂ) (f := F)
    (by rw [map_zero]; exact hdiff.hasFDerivAt) F.hasFDerivAt).fderiv
  rw [hfun, hch] at h1
  rw [e]
  exact h1

end GlobalTheory.UnifLieBasis

open GlobalTheory.UnifLieBasis in
open ReciprocityTheory.ChartRestriction.G.Chart (IsTan isTan_iff prodPts isLieComb_iff isTan_scale) in

/- English proof (translation)
Introduce `A _ L g u _ h1 h2`. Use `choose v hv using fun i : Fin g => (h2 (Pi.single i 1)).exists`. Establish `ht : ∀ i, IsTan (R` using `ℂ) (G := A) (v i) := fun i => (isTan_iff _).2 (hv i).1`. Establish `hp : ∀ c : Fin g → ℂ, IsTangent (prodPts (R` using `ℂ) (G := A) c v) ∧ u.IsDiff c (prodPts (R := ℂ) (G := A) c v) := by`. Introduce `c`.

Take `⟨a, b⟩` from `isDiff_list_prod u (fun i => c i • (Pi.single i 1 : Fin g → ℂ)) _ (fun i => isTan_scale (c i) (ht i)) (fun i => isDiff_smul u (ht i) (hv i).2 (c i))`. Rewrite `b` using `[← pi_eq_sum_univ' c]`. Conclude with `⟨(isTan_iff _).1 a, b⟩`. Use `⟨v, ⟨fun i => (hv i).1, fun w hw => ?_⟩, fun f c hf hF i => ?_⟩` and prove the remaining obligations. Take `⟨c, hc, hcu⟩` from `h1 w hw`.

Use `⟨c, (isLieComb_iff c v w).2 ((h2 c).unique ⟨hw, hc⟩ (hp c)), fun c' hc' => hcu c' ?_⟩` and prove the remaining obligations. Rewrite using `[(isLieComb_iff c' v w).1 hc']`. Conclude with `(hp c').2`. Set `F : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ)` to `ContinuousLinearMap.pi fun k => c k • ContinuousLinearMap.proj k`. Establish `hd` using `isDiff_comp u f F hF (hv i).1 (hv i).2`.

Establish `e : F (Pi.single i 1) = c i • (Pi.single i 1 : Fin g → ℂ)`. Use function extensionality and compare the values at `k`. Apply the tactic sequence `by_cases hk : k = i <;> simp [F, hk]`. Rewrite `hd` using `[e]`. Conclude with `congrArg CommaMorphism.left ((h2 _).unique ⟨isTangent_comp f (hv i).1, hd⟩ ⟨(isTan_iff _).1 (isTan_scale (c i) (ht i)), isDiff_smul u (ht i) (hv i).2 (c i)⟩)`.
-/
theorem GlobalTheory.exists_lieBasis_of_holUnif : ∀ (A : Over (Sp ℂ)) [GrpObj A] (L : LB A.left) (g : ℕ) (u : HolUnif A L g), Smooth A.hom → (∀ v, IsTangent v → ∃! w, u.IsDiff w v) → (∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v) → ∃ v : Fin g → (epsR ℂ ⟶ A), IsLieBasis v ∧ ∀ (f : A ⟶ A) (c : Fin g → ℂ), IsMonHom f → (∀ z, u.ex (fun k => c k * z k) = u.ex z ≫ f) → ∀ i, (v i ≫ f).left = spMap (epsScale (c i)) ≫ (v i).left := by
  intro A _ L g u _ h1 h2
  choose v hv using fun i : Fin g => (h2 (Pi.single i 1)).exists
  have ht : ∀ i, IsTan (R := ℂ) (G := A) (v i) := fun i => (isTan_iff _).2 (hv i).1
  have hp : ∀ c : Fin g → ℂ, IsTangent (prodPts (R := ℂ) (G := A) c v) ∧ u.IsDiff c (prodPts (R := ℂ) (G := A) c v) := by
    intro c
    obtain ⟨a, b⟩ := isDiff_list_prod u (fun i => c i • (Pi.single i 1 : Fin g → ℂ)) _
      (fun i => isTan_scale (c i) (ht i)) (fun i => isDiff_smul u (ht i) (hv i).2 (c i))
    rw [← pi_eq_sum_univ' c] at b
    exact ⟨(isTan_iff _).1 a, b⟩
  refine ⟨v, ⟨fun i => (hv i).1, fun w hw => ?_⟩, fun f c hf hF i => ?_⟩
  · obtain ⟨c, hc, hcu⟩ := h1 w hw
    refine ⟨c, (isLieComb_iff c v w).2 ((h2 c).unique ⟨hw, hc⟩ (hp c)), fun c' hc' => hcu c' ?_⟩
    rw [(isLieComb_iff c' v w).1 hc']
    exact (hp c').2
  · let F : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ) := ContinuousLinearMap.pi fun k => c k • ContinuousLinearMap.proj k
    have hd := isDiff_comp u f F hF (hv i).1 (hv i).2
    have e : F (Pi.single i 1) = c i • (Pi.single i 1 : Fin g → ℂ) := by
      funext k
      by_cases hk : k = i <;> simp [F, hk]
    rw [e] at hd
    exact congrArg CommaMorphism.left ((h2 _).unique ⟨isTangent_comp f (hv i).1, hd⟩
      ⟨(isTan_iff _).1 (isTan_scale (c i) (ht i)), isDiff_smul u (ht i) (hv i).2 (c i)⟩)
