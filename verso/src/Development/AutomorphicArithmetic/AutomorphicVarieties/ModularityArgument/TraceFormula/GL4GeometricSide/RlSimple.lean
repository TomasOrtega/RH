import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4GeometricSide.InnerEq
import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.UnitaryCurves.StarMulOfPlaces

noncomputable section

open NumberField Matrix MeasureTheory Finset
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.GKCoh GlobalTheory.WigAlg
open PositivityTheory.RgBcC PositivityTheory.RgBcC.RealD PositivityTheory.RgBcC.Bridge PositivityTheory.Rg.BcB.Desc PositivityTheory.Rg.Cz PositivityTheory.Rg.Cz.GK
open scoped InnerProductSpace Classical

namespace UpperTheory.V.Z.GSp4Splitting.RealLieSimple

section Dbl

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]

/- English proof (translation)
Use `haveI : DiscreteTopology (G ⧸ K) := QuotientGroup.discreteTopology hKo`. Set `A : Set (G ⧸ K)` to `(fun k : G => ((k * g : G) : G ⧸ K)) '' K`. Establish `hA : A.Finite` using `(hKc.image (QuotientGroup.continuous_mk.comp (continuous_id.mul continuous_const))).finite_of_discrete`. Establish `hex : ∀ x : G ⧸ K, ∃ k : G, x ∈ A → k ∈ K ∧ ((k * g : G) : G ⧸ K) = x` using `fun x => by`. Distinguish the cases in `hx : x ∈ A`.

Take `⟨k, hk, e⟩` from `hx`. Conclude with `⟨k, fun _ => ⟨hk, e⟩⟩`. Conclude with `⟨1, fun h => (hx h).elim⟩`. Use `choose r hr using hex`. Establish `left : ∀ k ∈ K, ∀ y : G, (y : G ⧸ K) ∈ A → ((k * y : G) : G ⧸ K) ∈ A`.

Introduce and unpack `k hk y ⟨k', hk', e⟩`. Use `⟨k * k', K.mul_mem hk hk', ?_⟩` and prove the remaining obligations. Establish `e'` using `QuotientGroup.eq.1 e`. Use `QuotientGroup.eq.2 ?_` and prove the remaining obligations. Simplify `e'` using `[mul_assoc]`.

Establish `hpos : μ (K : Set G) ≠ 0` using `hKo.measure_ne_zero μ ⟨1, K.one_mem⟩`. Establish `hfin : μ (K : Set G) ≠ ⊤` using `hKc.measure_lt_top.ne`. Use `⟨fun y => if (y : G ⧸ K) ∈ A then 1 else 0, hA.toFinset, r, (μ.real (K : Set G) : ℂ), ?_, ⟨_, hA.mem_toFinset.2 ⟨1, K.one_mem, rfl⟩⟩, fun x hx => (hr x (hA.mem_toFinset.1 hx)).1, ?_, ?_, fun F hF => ?_⟩` and prove the remaining obligations. Conclude with `Complex.ofReal_ne_zero.2 (ENNReal.toReal_ne_zero.2 ⟨hpos, hfin⟩)`. Use `HasCompactSupport.intro ((hKc.prod hKc).image (f := fun p : G × G => p.1 * g * p.2) (by fun_prop)) fun y hy => if_neg ?_` and prove the remaining obligations.

Introduce and unpack `⟨k, hk, e⟩`. Conclude with `hy ⟨(k, (k * g)⁻¹ * y), ⟨hk, QuotientGroup.eq.1 e⟩, mul_inv_cancel_left _ _⟩`. Introduce `k₁ h₁ k₂ h₂ y`. Establish `e : ((k₁ * y * k₂ : G) : G ⧸ K) ∈ A ↔ (y : G ⧸ K) ∈ A`. Rewrite using `[QuotientGroup.mk_mul_of_mem _ h₂]`.

Conclude with `⟨fun h => by simpa using left _ (K.inv_mem h₁) _ h, left _ h₁ _⟩`. Simplify using `only [e]`. Set `C : G ⧸ K → Set G` to `fun x => (fun y => (r x * g)⁻¹ * y) ⁻¹' (K : Set G)`. Establish `hCm : ∀ x, MeasurableSet (C x)` using `fun x => (hKo.preimage (continuous_const.mul continuous_id)).measurableSet`. Establish `hCμ : ∀ x, μ (C x) = μ (K : Set G)` using `fun x => measure_preimage_mul μ _ _`.

Establish `hC : ∀ x ∈ A, ∀ y : G, y ∈ C x ↔ (y : G ⧸ K) = x` using `fun x hx y => by conv_rhs => rw [← (hr x hx).2, eq_comm]`. Conclude with `QuotientGroup.eq.symm`. Establish `hpt : ∀ y : G, (if (y : G ⧸ K) ∈ A then (1 : ℂ) else 0) * F y = ∑ x ∈ hA.toFinset, (C x).indicator (fun _ => F (r x * g)) y` using `fun y => by`. Distinguish the cases in `hy : (y : G ⧸ K) ∈ A`. Establish `hm` using `(hC _ hy y).2 rfl`.

Rewrite using `[if_pos hy, one_mul, Finset.sum_eq_single (y : G ⧸ K), Set.indicator_of_mem hm]`. Rewrite using `[← hF (r y * g) _ hm, mul_inv_cancel_left]`. Conclude with `fun x hx hne => Set.indicator_of_notMem (fun h => hne ((hC x (hA.mem_toFinset.1 hx) y).1 h).symm) _`. Conclude with `fun h => (h (hA.mem_toFinset.2 hy)).elim`. Rewrite using `[if_neg hy, zero_mul]`.

Use `(Finset.sum_eq_zero fun x hx => Set.indicator_of_notMem (fun h => hy ?_) _).symm` and prove the remaining obligations. Rewrite using `[(hC x (hA.mem_toFinset.1 hx) y).1 h]`. Conclude with `hA.mem_toFinset.1 hx`. Simplify using `only [hpt]`. Rewrite using `[integral_finset_sum, Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations. Rewrite using `[integral_indicator_const _ (hCm x)]`. Simplify using `only [Measure.real, hCμ, Complex.real_smul]`. Conclude with `fun x _ => (integrable_indicator_iff (hCm x)).2 (integrableOn_const (by rw [hCμ]; exact hfin))`.
-/
private theorem dbl (μ : Measure G) [μ.IsHaarMeasure] (K : Subgroup G) (hKo : IsOpen (K : Set G))
    (hKc : IsCompact (K : Set G)) (g : G) :
    ∃ (h : G → ℂ) (T : Finset (G ⧸ K)) (r : G ⧸ K → G) (c : ℂ), c ≠ 0 ∧ T.Nonempty ∧ (∀ x ∈ T, r x ∈ K) ∧
      HasCompactSupport h ∧ (∀ k₁ ∈ K, ∀ k₂ ∈ K, ∀ y, h (k₁ * y * k₂) = h y) ∧
      ∀ F : G → ℂ, (∀ y, ∀ k ∈ K, F (y * k) = F y) → ∫ y, h y * F y ∂μ = c * ∑ x ∈ T, F (r x * g) := by
  haveI : DiscreteTopology (G ⧸ K) := QuotientGroup.discreteTopology hKo
  let A : Set (G ⧸ K) := (fun k : G => ((k * g : G) : G ⧸ K)) '' K
  have hA : A.Finite :=
    (hKc.image (QuotientGroup.continuous_mk.comp (continuous_id.mul continuous_const))).finite_of_discrete
  have hex : ∀ x : G ⧸ K, ∃ k : G, x ∈ A → k ∈ K ∧ ((k * g : G) : G ⧸ K) = x := fun x => by
    by_cases hx : x ∈ A
    · obtain ⟨k, hk, e⟩ := hx
      exact ⟨k, fun _ => ⟨hk, e⟩⟩
    · exact ⟨1, fun h => (hx h).elim⟩
  choose r hr using hex
  have left : ∀ k ∈ K, ∀ y : G, (y : G ⧸ K) ∈ A → ((k * y : G) : G ⧸ K) ∈ A := by
    rintro k hk y ⟨k', hk', e⟩
    refine ⟨k * k', K.mul_mem hk hk', ?_⟩
    have e' := QuotientGroup.eq.1 e
    refine QuotientGroup.eq.2 ?_
    simpa [mul_assoc] using e'
  have hpos : μ (K : Set G) ≠ 0 := hKo.measure_ne_zero μ ⟨1, K.one_mem⟩
  have hfin : μ (K : Set G) ≠ ⊤ := hKc.measure_lt_top.ne
  refine ⟨fun y => if (y : G ⧸ K) ∈ A then 1 else 0, hA.toFinset, r, (μ.real (K : Set G) : ℂ), ?_,
    ⟨_, hA.mem_toFinset.2 ⟨1, K.one_mem, rfl⟩⟩, fun x hx => (hr x (hA.mem_toFinset.1 hx)).1, ?_, ?_, fun F hF => ?_⟩
  · exact Complex.ofReal_ne_zero.2 (ENNReal.toReal_ne_zero.2 ⟨hpos, hfin⟩)
  · refine HasCompactSupport.intro ((hKc.prod hKc).image
      (f := fun p : G × G => p.1 * g * p.2) (by fun_prop)) fun y hy => if_neg ?_
    rintro ⟨k, hk, e⟩
    exact hy ⟨(k, (k * g)⁻¹ * y), ⟨hk, QuotientGroup.eq.1 e⟩, mul_inv_cancel_left _ _⟩
  · intro k₁ h₁ k₂ h₂ y
    have e : ((k₁ * y * k₂ : G) : G ⧸ K) ∈ A ↔ (y : G ⧸ K) ∈ A := by
      rw [QuotientGroup.mk_mul_of_mem _ h₂]
      exact ⟨fun h => by simpa using left _ (K.inv_mem h₁) _ h, left _ h₁ _⟩
    simp only [e]
  · let C : G ⧸ K → Set G := fun x => (fun y => (r x * g)⁻¹ * y) ⁻¹' (K : Set G)
    have hCm : ∀ x, MeasurableSet (C x) := fun x =>
      (hKo.preimage (continuous_const.mul continuous_id)).measurableSet
    have hCμ : ∀ x, μ (C x) = μ (K : Set G) := fun x => measure_preimage_mul μ _ _
    have hC : ∀ x ∈ A, ∀ y : G, y ∈ C x ↔ (y : G ⧸ K) = x := fun x hx y => by
      conv_rhs => rw [← (hr x hx).2, eq_comm]
      exact QuotientGroup.eq.symm
    have hpt : ∀ y : G, (if (y : G ⧸ K) ∈ A then (1 : ℂ) else 0) * F y =
        ∑ x ∈ hA.toFinset, (C x).indicator (fun _ => F (r x * g)) y := fun y => by
      by_cases hy : (y : G ⧸ K) ∈ A
      · have hm := (hC _ hy y).2 rfl
        rw [if_pos hy, one_mul, Finset.sum_eq_single (y : G ⧸ K), Set.indicator_of_mem hm]
        · rw [← hF (r y * g) _ hm, mul_inv_cancel_left]
        · exact fun x hx hne => Set.indicator_of_notMem
            (fun h => hne ((hC x (hA.mem_toFinset.1 hx) y).1 h).symm) _
        · exact fun h => (h (hA.mem_toFinset.2 hy)).elim
      · rw [if_neg hy, zero_mul]
        refine (Finset.sum_eq_zero fun x hx => Set.indicator_of_notMem (fun h => hy ?_) _).symm
        rw [(hC x (hA.mem_toFinset.1 hx) y).1 h]
        exact hA.mem_toFinset.1 hx
    simp only [hpt]
    rw [integral_finset_sum, Finset.mul_sum]
    · refine Finset.sum_congr rfl fun x _ => ?_
      rw [integral_indicator_const _ (hCm x)]
      simp only [Measure.real, hCμ, Complex.real_smul]
    · exact fun x _ => (integrable_indicator_iff (hCm x)).2 (integrableOn_const (by rw [hCμ]; exact hfin))

end Dbl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

/- English proof (translation)
Establish `hX : X = ∑ i, ∑ j, ∑ w : InfinitePlace E, ((X i j w).re • toL (Matrix.single i j (atEmb w.embedding 1)) + (X i j w).im • toL (Matrix.single i j (atEmb w.embedding Complex.I)))`. Use function extensionality and compare the values at `a b v`. Simplify using `only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply, toL, Matrix.single_apply]`. Rewrite using `[Finset.sum_eq_single a, Finset.sum_eq_single b, Finset.sum_eq_single v]`. Simplify using `[atEmb_apply]`.

Introduce `w _ hw`. Simplify using `[atEmb_apply, hw.symm]`. Simplify using the standard rewrite rules. Introduce `j _ hj`. Simplify using `[hj]`.

Simplify using the standard rewrite rules. Introduce `i _ hi`. Simplify using `[hi]`. Simplify using the standard rewrite rules. Rewrite using `[hX]`.

Simplify using `only [map_sum, map_add, map_smul, ← lieS_apply, lieS_atEmb_one, lieS_atEmb_I, LinearMap.sum_apply, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.sub_apply]`. Use `N.sum_mem fun i _ => N.sum_mem fun j _ => N.sum_mem fun w _ => N.add_mem ?_ ?_` and prove the remaining obligations. Conclude with `N.smul_of_tower_mem _ (N.add_mem (h1 w i j x hx) (h2 w i j x hx))`. Conclude with `N.smul_of_tower_mem _ (N.smul_mem _ (N.sub_mem (h1 w i j x hx) (h2 w i j x hx)))`.
-/
private theorem lie_mem (N : Submodule ℂ (Sm E n))
    (h1 : ∀ (w : InfinitePlace E) a b, ∀ x ∈ N, Eop w.embedding a b x ∈ N)
    (h2 : ∀ (w : InfinitePlace E) a b, ∀ x ∈ N, Eop (ComplexEmbedding.conjugate w.embedding) a b x ∈ N)
    (X : Lie E n) (x : Sm E n) (hx : x ∈ N) : lie E n X x ∈ N := by
  have hX : X = ∑ i, ∑ j, ∑ w : InfinitePlace E,
      ((X i j w).re • toL (Matrix.single i j (atEmb w.embedding 1)) +
        (X i j w).im • toL (Matrix.single i j (atEmb w.embedding Complex.I))) := by
    funext a b v
    simp only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply, toL, Matrix.single_apply]
    rw [Finset.sum_eq_single a, Finset.sum_eq_single b, Finset.sum_eq_single v]
    · simp [atEmb_apply]
    · intro w _ hw
      simp [atEmb_apply, hw.symm]
    · simp
    · intro j _ hj
      simp [hj]
    · simp
    · intro i _ hi
      simp [hi]
    · simp
  rw [hX]
  simp only [map_sum, map_add, map_smul, ← lieS_apply, lieS_atEmb_one, lieS_atEmb_I, LinearMap.sum_apply,
    LinearMap.add_apply, LinearMap.smul_apply, LinearMap.sub_apply]
  refine N.sum_mem fun i _ => N.sum_mem fun j _ => N.sum_mem fun w _ => N.add_mem ?_ ?_
  · exact N.smul_of_tower_mem _ (N.add_mem (h1 w i j x hx) (h2 w i j x hx))
  · exact N.smul_of_tower_mem _ (N.smul_mem _ (N.sub_mem (h1 w i j x hx) (h2 w i j x hx)))

variable (E n) in

private def fam : (InfinitePlace E → Un n) →* GL (Fin n) (Cinf E) :=
  MonoidHom.toHomUnits
    (((Matrix.piRingEquiv (n := Fin n) (β := fun _ : InfinitePlace E => ℂ)).symm.toRingHom.toMonoidHom).comp
      (MonoidHom.pi fun w => (Matrix.unitaryGroup (Fin n) ℂ).subtype.comp
        (Pi.evalMonoidHom (fun _ : InfinitePlace E => Un n) w)))

omit [NumberField E] [IsCMField E] in
/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem fam_val (u : InfinitePlace E → Un n) (i j : Fin n) (v : InfinitePlace E) :
    (fam E n u).val i j v = (u v).1 i j := rfl

omit [NumberField E] [IsCMField E] in
/- English proof (translation)
Use function extensionality and compare the values at `i j v`. Use `show (fam E n (Pi.mulSingle w k)).val i j v = _`. Rewrite using `[fam_val]`. Distinguish the cases in `hv : v = w`. Substitute `hv` using the available equality.

Simplify using `[atW]`. Simplify using `[atW, hv]`.
-/
private theorem toL_fam (w : InfinitePlace E) (k : Un n) : toL (fam E n (Pi.mulSingle w k)).val = atW w k.1 := by
  funext i j v
  show (fam E n (Pi.mulSingle w k)).val i j v = _
  rw [fam_val]
  by_cases hv : v = w
  · subst hv
    simp [atW]
  · simp [atW, hv]

/- English proof (translation)
Use `⟨fun v => ⟨k.1.map (Pi.evalRingHom (fun _ : InfinitePlace E => ℂ) v), ?_⟩, Units.ext rfl⟩` and prove the remaining obligations. Use `Matrix.mem_unitaryGroup_iff'.2 ?_` and prove the remaining obligations. Establish `h` using `congrArg (fun M : Matrix (Fin n) (Fin n) (Cinf E) => M.map (Pi.evalRingHom (fun _ : InfinitePlace E => ℂ) v)) (Matrix.mem_unitaryGroup_iff'.1 k.2)`. Simplify using `only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] at h`. Conclude with `h`.
-/
private theorem exists_fam (k : Kinf E n) : ∃ u, fam E n u = Unitary.toUnits k := by
  refine ⟨fun v => ⟨k.1.map (Pi.evalRingHom (fun _ : InfinitePlace E => ℂ) v), ?_⟩, Units.ext rfl⟩
  refine Matrix.mem_unitaryGroup_iff'.2 ?_
  have h := congrArg (fun M : Matrix (Fin n) (Fin n) (Cinf E) => M.map (Pi.evalRingHom (fun _ : InfinitePlace E => ℂ) v))
    (Matrix.mem_unitaryGroup_iff'.1 k.2)
  simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] at h
  exact h

/- English proof (translation)
Set `S : Subgroup (InfinitePlace E → Un n)` to `{ carrier := {u | (∀ x ∈ N, rt E n (infGL E n (fam E n u)) x ∈ N) ∧ ∀ x ∈ N, rt E n (infGL E n (fam E n u⁻¹)) x ∈ N} mul_mem' := fun {a b} ha hb => by`. Simplify using `only [Set.mem_setOf_eq, _root_.mul_inv_rev, map_mul, Module.End.mul_apply] at ha hb ⊢`. Conclude with `⟨fun x hx => ha.1 _ (hb.1 x hx), fun x hx => hb.2 _ (ha.2 x hx)⟩`. Use the proof step `one_mem' := by simp`. Use the proof step `inv_mem' := fun {a} ha => ⟨ha.2, by simpa only [inv_inv] using ha.1⟩ }`.

Take `⟨u, hu⟩` from `exists_fam k`. Establish `: u ∈ S` using `Subgroup.pi_mem_of_mulSingle_mem u fun w => ⟨h w _, by`. Rewrite using `[← Pi.mulSingle_inv]`. Conclude with `h w _⟩`. Rewrite using `[← hu]`.

Conclude with `this.1 x hx`.
-/
private theorem cpt_mem (N : Submodule ℂ (Sm E n))
    (h : ∀ (w : InfinitePlace E) (k : Un n), ∀ x ∈ N, rt E n (infGL E n (fam E n (Pi.mulSingle w k))) x ∈ N)
    (k : Kinf E n) (x : Sm E n) (hx : x ∈ N) : rt E n (infGL E n (Unitary.toUnits k)) x ∈ N := by
  let S : Subgroup (InfinitePlace E → Un n) :=
    { carrier := {u | (∀ x ∈ N, rt E n (infGL E n (fam E n u)) x ∈ N) ∧ ∀ x ∈ N, rt E n (infGL E n (fam E n u⁻¹)) x ∈ N}
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq, _root_.mul_inv_rev, map_mul, Module.End.mul_apply] at ha hb ⊢
        exact ⟨fun x hx => ha.1 _ (hb.1 x hx), fun x hx => hb.2 _ (ha.2 x hx)⟩
      one_mem' := by simp
      inv_mem' := fun {a} ha => ⟨ha.2, by simpa only [inv_inv] using ha.1⟩ }
  obtain ⟨u, hu⟩ := exists_fam k
  have : u ∈ S := Subgroup.pi_mem_of_mulSingle_mem u fun w => ⟨h w _, by
    rw [← Pi.mulSingle_inv]
    exact h w _⟩
  rw [← hu]
  exact this.1 x hx

/- English proof (translation)
Introduce `o φ hφ`. Use `Submodule.mem_comap.1 (Submodule.span_le.2 ?_ hφ)` and prove the remaining obligations. Introduce and unpack `_ ⟨g, x, hx, rfl⟩`. Use `Submodule.subset_span ?_` and prove the remaining obligations. Consider the cases of `o with`.

Consider the case `fin k`. Use `⟨k * g, x, hx, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul]`. Both sides reduce to the same expression. Consider the case `cpt k`.

Use `⟨g, _, h2 k x hx, ?_⟩` and prove the remaining obligations. Use `show (rt E n (infGL E n (Unitary.toUnits k)) * rt E n (finGL E n g)) x = (rt E n (finGL E n g) * rt E n (infGL E n (Unitary.toUnits k))) x`. Rewrite using `[← map_mul, ← map_mul, infGL_comm]`. Consider the case `lie X => exact ⟨g, _, h1 X x hx, LinearMap.congr_fun (lie_rt_fin X g) x⟩`.
-/
private theorem span_stable (N : Submodule ℂ (Sm E n)) (h1 : ∀ X, ∀ x ∈ N, lie E n X x ∈ N)
    (h2 : ∀ k : Kinf E n, ∀ x ∈ N, rt E n (infGL E n (Unitary.toUnits k)) x ∈ N) :
    IsStable (Submodule.span ℂ {φ | ∃ g, ∃ x ∈ N, φ = finRep E n g x}) := by
  intro o φ hφ
  refine Submodule.mem_comap.1 (Submodule.span_le.2 ?_ hφ)
  rintro _ ⟨g, x, hx, rfl⟩
  refine Submodule.subset_span ?_
  cases o with
  | fin k =>
    refine ⟨k * g, x, hx, ?_⟩
    rw [map_mul]
    rfl
  | cpt k =>
    refine ⟨g, _, h2 k x hx, ?_⟩
    show (rt E n (infGL E n (Unitary.toUnits k)) * rt E n (finGL E n g)) x =
      (rt E n (finGL E n g) * rt E n (infGL E n (Unitary.toUnits k))) x
    rw [← map_mul, ← map_mul, infGL_comm]
  | lie X => exact ⟨g, _, h1 X x hx, LinearMap.congr_fun (lie_rt_fin X g) x⟩

end UpperTheory.V.Z.GSp4Splitting.RealLieSimple

open UpperTheory.V.Z.GSp4Splitting UpperTheory.V.Z.GSp4Splitting.RealLieSimple in
/- English proof (translation)
Introduce `_ hL hK E _ _ _ n hn π hθ K hKo hKc hKθ _ _ μf _ D W hW hR`. Establish `hσ : ∀ w k, ∀ x ∈ W, D.σ w k x ∈ W` using `fun w => hL n D.U (D.σ w) _ (hK E n hn π hθ K hKo hKc hKθ μf D w).2 W fun a b x hx => W.add_mem (hW w a b x hx).1 (hW w a b x hx).2`. Set `ι : D.U →ₗ[ℂ] Sm E n` to `π.V.subtype ∘ₗ D.i`. Establish `hfix : ∀ u, ∀ k ∈ K, finRep E n k (D.i u).1 = (D.i u).1` using `fun u => (D.rng (D.i u)).1 ⟨u, rfl⟩`. Establish `hst` using `span_stable (W.map ι) (lie_mem _ ?_ ?_) (cpt_mem _ ?_)`.

Use `rotate_left`. Introduce and unpack `w a b _ ⟨x, hx, rfl⟩`. Conclude with `⟨_, (hW w a b x hx).1, D.hE1 w a b x⟩`. Introduce and unpack `w a b _ ⟨x, hx, rfl⟩`. Use `⟨_, W.neg_mem (hW w b a x hx).2, ?_⟩` and prove the remaining obligations.

Rewrite using `[map_neg]`. Conclude with `neg_eq_iff_eq_neg.2 (D.hE2 w b a x)`. Introduce and unpack `w k _ ⟨x, hx, rfl⟩`. Use `⟨_, hσ w k x hx, Subtype.ext (funext fun g => (D.hσ w k x g).trans ?_)⟩` and prove the remaining obligations. Rewrite using `[along, ← toL_fam]`.

Conclude with `chart_val _ g _`. Use `set M := Submodule.span ℂ {φ | ∃ g, ∃ x ∈ W.map ι, φ = finRep E n g x} with hM`. Establish `hle : M ≤ π.V` using `Submodule.span_le.2 (by`. Introduce and unpack `_ ⟨g, _, ⟨x, -, rfl⟩, rfl⟩`. Conclude with `π.stable (.fin g) _ (D.i x).2)`.

Break down `π.irred M hle hst with h0 | h1` into its components or cases. Use `Or.inl (eq_bot_iff.2 fun x hx => D.inj (Subtype.ext ?_))` and prove the remaining obligations. Establish `: ι x ∈ M` using `Submodule.subset_span ⟨1, _, ⟨x, hx, rfl⟩, by simp⟩`. Rewrite `this` using `[h0]`. Rewrite using `[map_zero]`.

Conclude with `this`. Use `right`. Establish `key : ∀ φ ∈ M, ∀ hφ : φ ∈ π.V, ∃ x ∈ W, ∀ u, D.H (D.i u) ⟨φ, hφ⟩ = D.H (D.i u) (D.i x)`. Introduce `φ hφ`. Proceed by induction on `hφ using Submodule.span_induction with`.

Consider the case `zero => exact fun _ => ⟨0, W.zero_mem, fun u => by rw [map_zero]; rfl⟩`. Consider the case `add a b ha hb iha ihb`. Introduce `_`. Take `⟨x, hx, e⟩` from `iha (hle ha)`. Take `⟨y, hy, e'⟩` from `ihb (hle hb)`.

Use `⟨x + y, W.add_mem hx hy, fun u => ?_⟩` and prove the remaining obligations. Rewrite using `[map_add, map_add, ← e, ← e', ← map_add]`. Both sides reduce to the same expression. Consider the case `smul c a ha iha`. Introduce `_`.

Take `⟨x, hx, e⟩` from `iha (hle ha)`. Use `⟨c • x, W.smul_mem c hx, fun u => ?_⟩` and prove the remaining obligations. Rewrite using `[map_smul, map_smul, ← e, ← map_smul]`. Both sides reduce to the same expression. Consider the case `mem φ hφ`.

Take `⟨g, _, ⟨x, hx, rfl⟩, rfl⟩` from `hφ`. Introduce `hφ`. Take `⟨h, T, r, c, hc, hT, hr, hs, hbi, hint⟩` from `dbl μf K hKo hKc g`. Set `t : GL (Fin n) (Af E) → π.V` to `fun y => ⟨finRep E n y (ι x), π.stable (.fin y) _ (D.i x).2⟩`. Establish `e1 : D.i (D.R ⟨h, hs, hbi⟩ x) = c • ∑ a ∈ T, t (r a * g)`.

Use `Subtype.ext (Subtype.ext ((D.hR _ x).trans (funext fun z => ?_)))` and prove the remaining obligations. Rewrite using `[heckeOp, hint (fun y => (D.i x).1.1 (z * finGL E n y)) fun y k hk => ?_]`. Simplify using `only [Submodule.coe_smul, Submodule.coe_sum, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]`. Both sides reduce to the same expression. Use `congrArg (fun ψ : Sm E n => ψ.1 (z * finGL E n y)) (hfix x k hk)` as an intermediate fact.

Rewrite using `[map_mul, ← mul_assoc]`. Conclude with `this`. Establish `e2 : ∀ u, ∀ a ∈ T, D.H (D.i u) (t (r a * g)) = D.H (D.i u) (t g)` using `fun u a ha => D.pet.2.2.2.1 (finGL E n (r a)) _ _ _ _ (fun z => (congrArg (fun ψ : Sm E n => ψ.1 z) (hfix u _ (hr a ha))).symm) (fun z => by show (D.i x).1.1 (z * finGL E n (r a * g)) = (D.i x).1.1 (z * finGL E n (r a) * finGL E n g)`. Rewrite using `[map_mul, mul_assoc])`. Establish `hN : (T.card : ℂ) ≠ 0` using `Nat.cast_ne_zero.2 hT.card_pos.ne'`.

Use `⟨(c * T.card)⁻¹ • D.R ⟨h, hs, hbi⟩ x, W.smul_mem _ (hR _ x hx), fun u => ?_⟩` and prove the remaining obligations. Rewrite using `[map_smul, map_smul, e1, map_smul, map_sum, Finset.sum_congr rfl (e2 u), Finset.sum_const, nsmul_eq_mul, smul_eq_mul, smul_eq_mul, ← mul_assoc c, inv_mul_cancel_left₀ (mul_ne_zero hc hN)]`. Use `eq_top_iff.2 fun v _ => ?_` and prove the remaining obligations. Take `⟨x, hx, e⟩` from `key (D.i v).1 (h1.ge (D.i v).2) (D.i v).2`. Establish `: v = x` using `ext_inner_left ℂ fun u => by`.

Rewrite using `[D.inner_eq, D.inner_eq]`. Conclude with `e u`. Conclude with `this ▸ hx`.
-/
theorem UpperTheory.V.Z.GSp4Splitting.rlSimple :
    HeckeMem → LieStab → RlK → RlSimple := by
  intro _ hL hK E _ _ _ n hn π hθ K hKo hKc hKθ _ _ μf _ D W hW hR
  have hσ : ∀ w k, ∀ x ∈ W, D.σ w k x ∈ W := fun w =>
    hL n D.U (D.σ w) _ (hK E n hn π hθ K hKo hKc hKθ μf D w).2 W fun a b x hx =>
      W.add_mem (hW w a b x hx).1 (hW w a b x hx).2
  let ι : D.U →ₗ[ℂ] Sm E n := π.V.subtype ∘ₗ D.i
  have hfix : ∀ u, ∀ k ∈ K, finRep E n k (D.i u).1 = (D.i u).1 := fun u => (D.rng (D.i u)).1 ⟨u, rfl⟩
  have hst := span_stable (W.map ι) (lie_mem _ ?_ ?_) (cpt_mem _ ?_)
  rotate_left
  · rintro w a b _ ⟨x, hx, rfl⟩
    exact ⟨_, (hW w a b x hx).1, D.hE1 w a b x⟩
  · rintro w a b _ ⟨x, hx, rfl⟩
    refine ⟨_, W.neg_mem (hW w b a x hx).2, ?_⟩
    rw [map_neg]
    exact neg_eq_iff_eq_neg.2 (D.hE2 w b a x)
  · rintro w k _ ⟨x, hx, rfl⟩
    refine ⟨_, hσ w k x hx, Subtype.ext (funext fun g => (D.hσ w k x g).trans ?_)⟩
    rw [along, ← toL_fam]
    exact chart_val _ g _
  set M := Submodule.span ℂ {φ | ∃ g, ∃ x ∈ W.map ι, φ = finRep E n g x} with hM
  have hle : M ≤ π.V := Submodule.span_le.2 (by
    rintro _ ⟨g, _, ⟨x, -, rfl⟩, rfl⟩
    exact π.stable (.fin g) _ (D.i x).2)
  rcases π.irred M hle hst with h0 | h1
  · refine Or.inl (eq_bot_iff.2 fun x hx => D.inj (Subtype.ext ?_))
    have : ι x ∈ M := Submodule.subset_span ⟨1, _, ⟨x, hx, rfl⟩, by simp⟩
    rw [h0] at this
    rw [map_zero]
    exact this
  right

  have key : ∀ φ ∈ M, ∀ hφ : φ ∈ π.V, ∃ x ∈ W, ∀ u, D.H (D.i u) ⟨φ, hφ⟩ = D.H (D.i u) (D.i x) := by
    intro φ hφ
    induction hφ using Submodule.span_induction with
    | zero => exact fun _ => ⟨0, W.zero_mem, fun u => by rw [map_zero]; rfl⟩
    | add a b ha hb iha ihb =>
      intro _
      obtain ⟨x, hx, e⟩ := iha (hle ha)
      obtain ⟨y, hy, e'⟩ := ihb (hle hb)
      refine ⟨x + y, W.add_mem hx hy, fun u => ?_⟩
      rw [map_add, map_add, ← e, ← e', ← map_add]
      rfl
    | smul c a ha iha =>
      intro _
      obtain ⟨x, hx, e⟩ := iha (hle ha)
      refine ⟨c • x, W.smul_mem c hx, fun u => ?_⟩
      rw [map_smul, map_smul, ← e, ← map_smul]
      rfl
    | mem φ hφ =>
      obtain ⟨g, _, ⟨x, hx, rfl⟩, rfl⟩ := hφ
      intro hφ
      obtain ⟨h, T, r, c, hc, hT, hr, hs, hbi, hint⟩ := dbl μf K hKo hKc g
      let t : GL (Fin n) (Af E) → π.V := fun y => ⟨finRep E n y (ι x), π.stable (.fin y) _ (D.i x).2⟩
      have e1 : D.i (D.R ⟨h, hs, hbi⟩ x) = c • ∑ a ∈ T, t (r a * g) := by
        refine Subtype.ext (Subtype.ext ((D.hR _ x).trans (funext fun z => ?_)))
        rw [heckeOp, hint (fun y => (D.i x).1.1 (z * finGL E n y)) fun y k hk => ?_]
        · simp only [Submodule.coe_smul, Submodule.coe_sum, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
          rfl
        · have := congrArg (fun ψ : Sm E n => ψ.1 (z * finGL E n y)) (hfix x k hk)
          rw [map_mul, ← mul_assoc]
          exact this
      have e2 : ∀ u, ∀ a ∈ T, D.H (D.i u) (t (r a * g)) = D.H (D.i u) (t g) := fun u a ha =>
        D.pet.2.2.2.1 (finGL E n (r a)) _ _ _ _
          (fun z => (congrArg (fun ψ : Sm E n => ψ.1 z) (hfix u _ (hr a ha))).symm) (fun z => by
            show (D.i x).1.1 (z * finGL E n (r a * g)) = (D.i x).1.1 (z * finGL E n (r a) * finGL E n g)
            rw [map_mul, mul_assoc])
      have hN : (T.card : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hT.card_pos.ne'
      refine ⟨(c * T.card)⁻¹ • D.R ⟨h, hs, hbi⟩ x, W.smul_mem _ (hR _ x hx), fun u => ?_⟩
      rw [map_smul, map_smul, e1, map_smul, map_sum, Finset.sum_congr rfl (e2 u), Finset.sum_const, nsmul_eq_mul,
        smul_eq_mul, smul_eq_mul, ← mul_assoc c, inv_mul_cancel_left₀ (mul_ne_zero hc hN)]
  refine eq_top_iff.2 fun v _ => ?_
  obtain ⟨x, hx, e⟩ := key (D.i v).1 (h1.ge (D.i v).2) (D.i v).2
  have : v = x := ext_inner_left ℂ fun u => by
    rw [D.inner_eq, D.inner_eq]
    exact e u
  exact this ▸ hx
