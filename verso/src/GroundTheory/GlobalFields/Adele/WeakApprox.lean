import Mathlib

namespace GroundTheory.Global

open IsDedekindDomain NumberField

variable {K : Type*} [Field K] [NumberField K]

section AbsoluteValues

/- English proof (translation)
Rewrite using `[← FinitePlace.norm_embedding]`. Conclude with `FinitePlace.norm_lt_one_iff_mem K v x`.
-/
theorem adicAbv_lt_one_iff_mem (v : HeightOneSpectrum (𝓞 K)) (x : 𝓞 K) :
    NumberField.HeightOneSpectrum.adicAbv K v (algebraMap (𝓞 K) K x) < 1 ↔ x ∈ v.asIdeal := by
  rw [← FinitePlace.norm_embedding]
  exact FinitePlace.norm_lt_one_iff_mem K v x

/- English proof (translation)
Take `⟨x, hxv, hx0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot`. Use `⟨algebraMap (𝓞 K) K x, ?_, ?_⟩` and prove the remaining obligations. Simplify using `using hx0`. Conclude with `((adicAbv_lt_one_iff_mem v x).2 hxv).ne`.
-/
theorem adicAbv_isNontrivial (v : HeightOneSpectrum (𝓞 K)) : (NumberField.HeightOneSpectrum.adicAbv K v).IsNontrivial := by
  obtain ⟨x, hxv, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
  refine ⟨algebraMap (𝓞 K) K x, ?_, ?_⟩
  · simpa using hx0
  · exact ((adicAbv_lt_one_iff_mem v x).2 hxv).ne

/- English proof (translation)
Introduce `he`. Establish `hle : ¬ v.asIdeal ≤ v'.asIdeal` using `fun hle ↦ h (HeightOneSpectrum.ext (v.isMaximal.eq_of_le v'.isPrime.ne_top hle))`. Take `⟨x, hxv, hxv'⟩` from `Set.not_subset.1 hle`. Establish `h1` using `(adicAbv_lt_one_iff_mem v x).2 hxv`. Rewrite `h1` using `[he.lt_one_iff]`.

Conclude with `hxv' ((adicAbv_lt_one_iff_mem v' x).1 h1)`.
-/
theorem not_isEquiv_adicAbv {v v' : HeightOneSpectrum (𝓞 K)} (h : v ≠ v') :
    ¬ (NumberField.HeightOneSpectrum.adicAbv K v).IsEquiv (NumberField.HeightOneSpectrum.adicAbv K v') := by
  intro he
  have hle : ¬ v.asIdeal ≤ v'.asIdeal := fun hle ↦
    h (HeightOneSpectrum.ext (v.isMaximal.eq_of_le v'.isPrime.ne_top hle))
  obtain ⟨x, hxv, hxv'⟩ := Set.not_subset.1 hle
  have h1 := (adicAbv_lt_one_iff_mem v x).2 hxv
  rw [he.lt_one_iff] at h1
  exact hxv' ((adicAbv_lt_one_iff_mem v' x).1 h1)

/- English proof (translation)
Introduce `he`. Establish `h1 : NumberField.HeightOneSpectrum.adicAbv K v (2 : K) ≤ 1`. Simplify using `using NumberField.HeightOneSpectrum.adicAbv_natCast_le_one K v 2`. Rewrite `h1` using `[he.le_one_iff]`. Establish `h2 : w.1 (2 : K) = 2`.

Establish `h` using `w.map_natCast 2`. Rewrite `h` using `[Nat.cast_ofNat, Nat.cast_ofNat]`. Conclude with `h`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem not_isEquiv_adicAbv_infinitePlace (v : HeightOneSpectrum (𝓞 K)) (w : InfinitePlace K) :
    ¬ (NumberField.HeightOneSpectrum.adicAbv K v).IsEquiv w.1 := by
  intro he
  have h1 : NumberField.HeightOneSpectrum.adicAbv K v (2 : K) ≤ 1 := by
    simpa using NumberField.HeightOneSpectrum.adicAbv_natCast_le_one K v 2
  rw [he.le_one_iff] at h1
  have h2 : w.1 (2 : K) = 2 := by
    have h := w.map_natCast 2
    rw [Nat.cast_ofNat, Nat.cast_ofNat] at h
    exact h
  linarith

end AbsoluteValues

section Density

variable (S : Finset (HeightOneSpectrum (𝓞 K))) (T : Finset (InfinitePlace K))

noncomputable def placeAbv : S ⊕ T → AbsoluteValue K ℝ :=
  Sum.elim (fun v ↦ NumberField.HeightOneSpectrum.adicAbv K v.1) (fun w ↦ w.1.1)

/- English proof (translation)
The claim follows from `| .inl v => adicAbv_isNontrivial v.1 | .inr w => w.1.isNontrivial`.
-/
theorem placeAbv_isNontrivial : ∀ i, (placeAbv S T i).IsNontrivial
  | .inl v => adicAbv_isNontrivial v.1
  | .inr w => w.1.isNontrivial

/- English proof (translation)
Introduce and unpack `(⟨v, hv⟩ | ⟨w, hw⟩) (⟨v', hv'⟩ | ⟨w', hw'⟩) hij he`. Conclude with `not_isEquiv_adicAbv (fun h ↦ hij (by subst h; rfl)) he`. Conclude with `not_isEquiv_adicAbv_infinitePlace v w' he`. Conclude with `not_isEquiv_adicAbv_infinitePlace v' w he.symm`. Conclude with `hij (by`.

Establish `: w = w'` using `InfinitePlace.eq_iff_isEquiv.2 he`. Substitute `this` using the available equality. Use the proof step `rfl)`.
-/
theorem placeAbv_pairwise_not_isEquiv :
    Pairwise fun i j ↦ ¬ (placeAbv S T i).IsEquiv (placeAbv S T j) := by
  rintro (⟨v, hv⟩ | ⟨w, hw⟩) (⟨v', hv'⟩ | ⟨w', hw'⟩) hij he
  · exact not_isEquiv_adicAbv (fun h ↦ hij (by subst h; rfl)) he
  · exact not_isEquiv_adicAbv_infinitePlace v w' he
  · exact not_isEquiv_adicAbv_infinitePlace v' w he.symm
  · exact hij (by
      have : w = w' := InfinitePlace.eq_iff_isEquiv.2 he
      subst this; rfl)

/- English proof (translation)
Use `AddMonoidHomClass.isometry_of_norm _ fun x ↦ ?_` and prove the remaining obligations. Rewrite using `[WithAbs.norm_eq_apply_ofAbs, ← FinitePlace.norm_embedding]`. Both sides reduce to the same expression.
-/
theorem isometry_algebraMap_adicCompletion (v : HeightOneSpectrum (𝓞 K)) :
    Isometry ((algebraMap K (v.adicCompletion K)).comp
      (WithAbs.equiv (NumberField.HeightOneSpectrum.adicAbv K v)).toRingHom) := by
  refine AddMonoidHomClass.isometry_of_norm _ fun x ↦ ?_
  rw [WithAbs.norm_eq_apply_ofAbs, ← FinitePlace.norm_embedding]
  rfl

/- English proof (translation)
Set `φ : ∀ v : S, WithAbs (placeAbv S T (.inl v)) → v.1.adicCompletion K` to `fun v ↦ (algebraMap K (v.1.adicCompletion K)).comp (WithAbs.equiv (NumberField.HeightOneSpectrum.adicAbv K v.1)).toRingHom`. Set `ψ : ∀ w : T, WithAbs (placeAbv S T (.inr w)) → w.1.Completion` to `fun w y ↦ ((show WithAbs w.1.1 from y) : w.1.Completion)`. Establish `hφc : ∀ v, Continuous (φ v)` using `fun v ↦ (isometry_algebraMap_adicCompletion v.1).continuous`. Establish `hφd : ∀ v, DenseRange (φ v)`. Introduce `v`.

Establish `h` using `HeightOneSpectrum.denseRange_algebraMap (R := 𝓞 K) (K := K) v.1`. Unfold `DenseRange at h ⊢`. Use `h using 1` and compare the differences between its conclusion and the goal. Use `show Set.range (⇑(algebraMap K (v.1.adicCompletion K)) ∘ ⇑(WithAbs.equiv (NumberField.HeightOneSpectrum.adicAbv K v.1))) = _`. Conclude with `(WithAbs.equiv (NumberField.HeightOneSpectrum.adicAbv K v.1)).surjective.range_comp _`.

Establish `hψc : ∀ w, Continuous (ψ w)` using `fun w ↦ InfinitePlace.Completion.continuous_coe w.1`. Establish `hψd : ∀ w, DenseRange (ψ w)` using `fun w ↦ InfinitePlace.Completion.denseRange_coe w.1`. Set `e` to `Homeomorph.sumPiEquivProdPi S T (fun i ↦ WithAbs (placeAbv S T i))`. Establish `hc : Continuous (Prod.map (Pi.map φ) (Pi.map ψ) ∘ e)` using `((continuous_pi fun v ↦ (hφc v).comp (continuous_apply v)).prodMap (continuous_pi fun w ↦ (hψc w).comp (continuous_apply w))).comp e.continuous`. Establish `hg : DenseRange (Prod.map (Pi.map φ) (Pi.map ψ) ∘ e)` using `((DenseRange.piMap hφd).prodMap (DenseRange.piMap hψd)).comp e.surjective.denseRange ((continuous_pi fun v ↦ (hφc v).comp (continuous_apply v)).prodMap (continuous_pi fun w ↦ (hψc w).comp (continuous_apply w)))`.

Establish `hd` using `AbsoluteValue.denseRange_algebraMap_pi (placeAbv_isNontrivial S T) (placeAbv_pairwise_not_isEquiv S T)`. Use `hg.comp hd hc using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `x`. Both sides reduce to the same expression.
-/
theorem denseRange_algebraMap_prod_pi :
    DenseRange (fun x : K ↦ ((fun v : S ↦ algebraMap K (v.1.adicCompletion K) x),
      (fun w : T ↦ algebraMap K w.1.Completion x))) := by
  classical
  let φ : ∀ v : S, WithAbs (placeAbv S T (.inl v)) → v.1.adicCompletion K := fun v ↦
    (algebraMap K (v.1.adicCompletion K)).comp
      (WithAbs.equiv (NumberField.HeightOneSpectrum.adicAbv K v.1)).toRingHom
  let ψ : ∀ w : T, WithAbs (placeAbv S T (.inr w)) → w.1.Completion := fun w y ↦
    ((show WithAbs w.1.1 from y) : w.1.Completion)
  have hφc : ∀ v, Continuous (φ v) := fun v ↦ (isometry_algebraMap_adicCompletion v.1).continuous
  have hφd : ∀ v, DenseRange (φ v) := by
    intro v
    have h := HeightOneSpectrum.denseRange_algebraMap (R := 𝓞 K) (K := K) v.1
    unfold DenseRange at h ⊢
    convert h using 1
    show Set.range (⇑(algebraMap K (v.1.adicCompletion K)) ∘
      ⇑(WithAbs.equiv (NumberField.HeightOneSpectrum.adicAbv K v.1))) = _
    exact (WithAbs.equiv (NumberField.HeightOneSpectrum.adicAbv K v.1)).surjective.range_comp _
  have hψc : ∀ w, Continuous (ψ w) := fun w ↦ InfinitePlace.Completion.continuous_coe w.1
  have hψd : ∀ w, DenseRange (ψ w) := fun w ↦ InfinitePlace.Completion.denseRange_coe w.1
  let e := Homeomorph.sumPiEquivProdPi S T (fun i ↦ WithAbs (placeAbv S T i))
  have hc : Continuous (Prod.map (Pi.map φ) (Pi.map ψ) ∘ e) :=
    ((continuous_pi fun v ↦ (hφc v).comp (continuous_apply v)).prodMap
      (continuous_pi fun w ↦ (hψc w).comp (continuous_apply w))).comp e.continuous
  have hg : DenseRange (Prod.map (Pi.map φ) (Pi.map ψ) ∘ e) :=
    ((DenseRange.piMap hφd).prodMap (DenseRange.piMap hψd)).comp e.surjective.denseRange
      ((continuous_pi fun v ↦ (hφc v).comp (continuous_apply v)).prodMap
        (continuous_pi fun w ↦ (hψc w).comp (continuous_apply w)))
  have hd := AbsoluteValue.denseRange_algebraMap_pi (placeAbv_isNontrivial S T)
    (placeAbv_pairwise_not_isEquiv S T)
  convert hg.comp hd hc using 1
  funext x
  rfl

end Density

end GroundTheory.Global
