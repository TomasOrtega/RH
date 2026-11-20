import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoSpan
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoSurj
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoEvLow
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoMvps
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoRes
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.HomogOfStable
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.EigenMem

open IsLocalRing MvPowerSeries UpperTheory.V.Alg

/- English proof (translation)
Rewrite using `[← res_eq_zero_iff O, res_map, res_eq_zero_iff]`. Conclude with `hx`.
-/
private theorem map_mem_max {O : Type} [CommRing O] [IsLocalRing O] {R : Type} [CommRing R] [Algebra O R]
    [IsCO O R] {R' : Type} [CommRing R'] [Algebra O R'] [IsCO O R'] (f : R →ₐ[O] R') {x : R}
    (hx : x ∈ maximalIdeal R) : f x ∈ maximalIdeal R' := by
  rw [← res_eq_zero_iff O, res_map, res_eq_zero_iff]
  exact hx

/- English proof (translation)
Establish `hC : ∀ (H : MvPowerSeries σ O →ₐ[O] R') (x : O), H (C x) = Algebra.ofId O R' x` using `fun H x => by`. Use `H.commutes x` as an intermediate fact. Rewrite `this` using `[MvPowerSeries.algebraMap_apply]`. Conclude with `this`. Conclude with `(co_ev O O R' σ (Algebra.ofId O R') (fun s => F (X s)) hm).unique ⟨hC F, fun _ => rfl⟩ ⟨hC G, fun s => (h s).symm⟩`.
-/
private theorem ext_X {O : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    [IsAdicComplete (maximalIdeal O) O] {σ : Type} [Finite σ] {R' : Type} [CommRing R'] [Algebra O R']
    [IsCO O R'] (F G : MvPowerSeries σ O →ₐ[O] R') (hm : ∀ s, F (X s) ∈ maximalIdeal R')
    (h : ∀ s, F (X s) = G (X s)) : F = G := by
  have hC : ∀ (H : MvPowerSeries σ O →ₐ[O] R') (x : O), H (C x) = Algebra.ofId O R' x := fun H x => by
    have := H.commutes x
    rw [MvPowerSeries.algebraMap_apply] at this
    exact this
  exact (co_ev O O R' σ (Algebra.ofId O R') (fun s => F (X s)) hm).unique ⟨hC F, fun _ => rfl⟩
    ⟨hC G, fun s => (h s).symm⟩

/- English proof (translation)
Introduce `O _ _ _ _ X _ _ _ R _ _ _ S e wt hem hgen hst`. Establish `hspan : maximalIdeal R ≤ Ideal.span (Set.range e) ⊔ (maximalIdeal O).map (Algebra.ofId O R) ⊔ maximalIdeal R ^ 2`. Use `co_span O R O (Algebra.ofId O R) (Set.range e) (by rintro _ ⟨s, rfl⟩; exact hem s) ?_` and prove the remaining obligations. Introduce `f f' _ h`. Use `haveI := (co_res O).2`.

Conclude with `hgen _ f f' fun s => h _ ⟨s, rfl⟩`. Take `⟨T, hT, hTs⟩` from `(Submodule.fg_span_iff_fg_span_finset_subset (R := R) (Set.range e)).1 (IsNoetherian.noetherian _)`. Use `choose u hu using fun i : T => hT i.2`. Take `⟨π, ⟨hπC, hπX⟩, -⟩` from `co_ev O O R T (Algebra.ofId O R) (fun i => e (u i)) fun i => hem _`. Establish `hsurj : Function.Surjective π` using `by haveI := co_mvps O O T`.

Use `co_surj O (MvPowerSeries T O) R π (hspan.trans (sup_le_sup_right (sup_le ?_ ?_) _))` and prove the remaining obligations. Use `show Submodule.span R (Set.range e) ≤ _`. Rewrite using `[hTs, Submodule.span_le]`. Introduce `x hx`. Establish `h1 : x = π (MvPowerSeries.X ⟨x, hx⟩)` using `by rw [hπX, hu]`.

Rewrite using `[h1]`. Use `Ideal.mem_map_of_mem π fun hU => ?_` and prove the remaining obligations. Use `hU.map π` as an intermediate fact. Rewrite `this` using `[hπX]`. Conclude with `hem _ this`.

Rewrite using `[Ideal.map_le_iff_le_comap]`. Introduce `a ha`. Rewrite using `[Ideal.mem_comap, ← hπC]`. Use `Ideal.mem_map_of_mem π fun hU => ?_` and prove the remaining obligations. Use `hU.map (constantCoeff : MvPowerSeries T O →+* O)` as an intermediate fact.

Rewrite `this` using `[constantCoeff_C]`. Conclude with `ha this`. Establish `hπm : ∀ i, π (MvPowerSeries.X i) ∈ maximalIdeal R` using `fun i => by rw [hπX]; exact hem _`. Establish `hhom : IsHomog O (fun i : T => wt (u i)) (RingHom.ker π)`. Use `homog_of_stable O X R T _ π hπm ?_` and prove the remaining obligations.

Introduce `R' _ _ _ f t ht hf f' hf' x hx`. Set `g : R →ₐ[O] R'` to `(Ideal.Quotient.liftₐ (RingHom.ker π) f hf).comp (Ideal.quotientKerAlgEquivOfSurjective hsurj).symm.toAlgHom`. Establish `hg : ∀ y, g (π y) = f y` using `fun y => by`. Establish `: (Ideal.quotientKerAlgEquivOfSurjective hsurj).symm (π y) = Ideal.Quotient.mk _ y`. Rewrite using `[AlgEquiv.symm_apply_eq]`.

Both sides reduce to the same expression. Use `show Ideal.Quotient.liftₐ (RingHom.ker π) f hf ((Ideal.quotientKerAlgEquivOfSurjective hsurj).symm (π y)) = _`. Rewrite using `[this]`. Both sides reduce to the same expression. Take `⟨g', hg'⟩` from `hst R' g t ht`.

Establish `: g'.comp π = f'` using `ext_X _ _ (fun i => map_mem_max g' (hπm i)) fun i => by`. Rewrite using `[AlgHom.comp_apply, hf', ← hg, hπX, hg']`. Rewrite using `[← this, AlgHom.comp_apply, hx, map_zero]`. Set `W : WPres O X R` to `{ σ := T, wt := fun i => wt (u i), π := π, surj := hsurj, homog := hhom }`. Use `⟨W, u, fun i => ⟨hπX i, rfl⟩, fun s => eigen_mem O X R W hπm (e s) (wt s) ?_⟩` and prove the remaining obligations.

Introduce `R' _ _ _ f f' t ht h`. Take `⟨g', hg'⟩` from `hst R' f t ht`. Establish `h1 : g'.comp π = f'.comp π` using `ext_X _ _ (fun i => map_mem_max g' (hπm i)) fun i => by`. Establish `h2 : f' (π (MvPowerSeries.X i)) = t (Multiplicative.ofAdd (wt (u i))) * f (π (MvPowerSeries.X i))` using `h i`. Rewrite using `[AlgHom.comp_apply, AlgHom.comp_apply, h2, hπX, hg']`.

Establish `h3 : f' (e s) = g' (e s)`. Take `⟨y, hy⟩` from `hsurj (e s)`. Rewrite using `[← hy]`. Conclude with `(DFunLike.congr_fun h1 y).symm`. Rewrite using `[h3, hg']`.
-/
theorem UpperTheory.V.Alg.coord_grading :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (S : Type) (e : S → R) (wt : S → X), (∀ s, e s ∈ maximalIdeal R) →
      (∀ (R' : Type) [CommRing R'] [Algebra O R'] [IsCO O R'] (f f' : R →ₐ[O] R'), (∀ s, f (e s) = f' (e s)) → f = f') →
      (∀ (R' : Type) [CommRing R'] [Algebra O R'] [IsCO O R'] (f : R →ₐ[O] R') (t : Multiplicative X →* R'ˣ), (∀ j, res O R' (t j) = 1) →
        ∃ f' : R →ₐ[O] R', ∀ s, f' (e s) = t (Multiplicative.ofAdd (wt s)) * f (e s)) →
      ∃ (W : WPres O X R) (u : W.σ → S), (∀ i, W.z i = e (u i) ∧ W.wt i = wt (u i)) ∧ ∀ s, e s ∈ W.part (wt s) := by
  intro O _ _ _ _ X _ _ _ R _ _ _ S e wt hem hgen hst
  classical
  have hspan : maximalIdeal R ≤ Ideal.span (Set.range e) ⊔ (maximalIdeal O).map (Algebra.ofId O R) ⊔
      maximalIdeal R ^ 2 := by
    refine co_span O R O (Algebra.ofId O R) (Set.range e) (by rintro _ ⟨s, rfl⟩; exact hem s) ?_
    intro f f' _ h
    haveI := (co_res O).2
    exact hgen _ f f' fun s => h _ ⟨s, rfl⟩
  obtain ⟨T, hT, hTs⟩ := (Submodule.fg_span_iff_fg_span_finset_subset (R := R) (Set.range e)).1
    (IsNoetherian.noetherian _)
  choose u hu using fun i : T => hT i.2
  obtain ⟨π, ⟨hπC, hπX⟩, -⟩ := co_ev O O R T (Algebra.ofId O R) (fun i => e (u i)) fun i => hem _
  have hsurj : Function.Surjective π := by
    haveI := co_mvps O O T
    refine co_surj O (MvPowerSeries T O) R π (hspan.trans (sup_le_sup_right (sup_le ?_ ?_) _))
    · show Submodule.span R (Set.range e) ≤ _
      rw [hTs, Submodule.span_le]
      intro x hx
      have h1 : x = π (MvPowerSeries.X ⟨x, hx⟩) := by rw [hπX, hu]
      rw [h1]
      refine Ideal.mem_map_of_mem π fun hU => ?_
      have := hU.map π
      rw [hπX] at this
      exact hem _ this
    · rw [Ideal.map_le_iff_le_comap]
      intro a ha
      rw [Ideal.mem_comap, ← hπC]
      refine Ideal.mem_map_of_mem π fun hU => ?_
      have := hU.map (constantCoeff : MvPowerSeries T O →+* O)
      rw [constantCoeff_C] at this
      exact ha this
  have hπm : ∀ i, π (MvPowerSeries.X i) ∈ maximalIdeal R := fun i => by rw [hπX]; exact hem _
  have hhom : IsHomog O (fun i : T => wt (u i)) (RingHom.ker π) := by
    refine homog_of_stable O X R T _ π hπm ?_
    intro R' _ _ _ f t ht hf f' hf' x hx
    let g : R →ₐ[O] R' := (Ideal.Quotient.liftₐ (RingHom.ker π) f hf).comp
      (Ideal.quotientKerAlgEquivOfSurjective hsurj).symm.toAlgHom
    have hg : ∀ y, g (π y) = f y := fun y => by
      have : (Ideal.quotientKerAlgEquivOfSurjective hsurj).symm (π y) = Ideal.Quotient.mk _ y := by
        rw [AlgEquiv.symm_apply_eq]; rfl
      show Ideal.Quotient.liftₐ (RingHom.ker π) f hf ((Ideal.quotientKerAlgEquivOfSurjective hsurj).symm (π y)) = _
      rw [this]
      rfl
    obtain ⟨g', hg'⟩ := hst R' g t ht
    have : g'.comp π = f' := ext_X _ _ (fun i => map_mem_max g' (hπm i)) fun i => by
      rw [AlgHom.comp_apply, hf', ← hg, hπX, hg']
    rw [← this, AlgHom.comp_apply, hx, map_zero]
  let W : WPres O X R := { σ := T, wt := fun i => wt (u i), π := π, surj := hsurj, homog := hhom }
  refine ⟨W, u, fun i => ⟨hπX i, rfl⟩, fun s => eigen_mem O X R W hπm (e s) (wt s) ?_⟩
  intro R' _ _ _ f f' t ht h
  obtain ⟨g', hg'⟩ := hst R' f t ht
  have h1 : g'.comp π = f'.comp π := ext_X _ _ (fun i => map_mem_max g' (hπm i)) fun i => by
    have h2 : f' (π (MvPowerSeries.X i)) = t (Multiplicative.ofAdd (wt (u i))) * f (π (MvPowerSeries.X i)) := h i
    rw [AlgHom.comp_apply, AlgHom.comp_apply, h2, hπX, hg']
  have h3 : f' (e s) = g' (e s) := by
    obtain ⟨y, hy⟩ := hsurj (e s)
    rw [← hy]
    exact (DFunLike.congr_fun h1 y).symm
  rw [h3, hg']
