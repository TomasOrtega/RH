import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
import Formalism.LocalRingCardinality.DataForms
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension

open NumberField

namespace GlobalTheory.InverseHalfDifferent

/- English proof (translation)
Consider the cases of `nonempty_fintype ι`. Set `χ : ι → (𝓞 E →* M)` to `fun j => ((f j).comp (algebraMap (𝓞 E) E)).toMonoidHom`. Establish `hχ : Function.Injective χ`. Introduce `j k h`. Apply `hf` to reduce the goal to its premises.

Apply `IsFractionRing.ringHom_ext (A := 𝓞 E)` to reduce the goal to its premises. Introduce `x`. Conclude with `DFunLike.congr_fun h x`. Establish `hli : LinearIndependent M (fun j => (χ j : 𝓞 E → M))` using `(linearIndependent_monoidHom (𝓞 E) M).comp χ hχ`. Establish `htop : Submodule.span M (Set.range fun a : 𝓞 E => fun j => f j (a : E)) = ⊤`.

Assume the negation of the conclusion as `hne`. Take `⟨φ, hφ0, hφ⟩` from `Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hne)`. Apply `hφ0` to reduce the goal to its premises. Establish `hc : ∀ j, φ (fun k => if j = k then 1 else 0) = 0`. Establish `key : ∑ j, φ (fun k => if j = k then 1 else 0) • (χ j : 𝓞 E → M) = 0`.

Use function extensionality and compare the values at `a`. Establish `ha : φ (fun j => f j (a : E)) = 0` using `hφ (Submodule.subset_span ⟨a, rfl⟩)`. Rewrite `ha` using `[LinearMap.pi_apply_eq_sum_univ]`. Simplify `ha` using `[χ, Finset.sum_apply, mul_comm]`. Conclude with `Fintype.linearIndependent_iff.mp hli _ key`.

Use `LinearMap.ext fun x => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.pi_apply_eq_sum_univ]`. Simplify using `[hc]`. Establish `h1 : (Pi.single i 1 : ι → M) ∈ Submodule.span M (Set.range fun a : 𝓞 E => fun j => f j (a : E))`. Rewrite using `[htop]`.

Conclude with `Submodule.mem_top`. Take `⟨y, hy, z, hz⟩` from `(IsLocalization.mem_span_iff (nonZeroDivisors (𝓞 M))).mp h1`. Use `⟨algebraMap (𝓞 M) M z, IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors z.2, ?_⟩` and prove the remaining obligations. Establish `hy' : y = algebraMap (𝓞 M) M z • (Pi.single i 1 : ι → M)`. Rewrite using `[hz, smul_smul, IsLocalization.mk'_spec', map_one, one_smul]`.

Establish `: (Pi.single i (algebraMap (𝓞 M) M z) : ι → M) = y`. Rewrite using `[hy']`. Use extensionality with `k`. Distinguish the cases in `hk : k = i`. Substitute `hk` using the available equality.

Simplify using the standard rewrite rules. Simplify using `[hk]`. Rewrite using `[this]`. Conclude with `hy`.
-/
theorem exists_single_mem_span {E M ι : Type} [Field E] [NumberField E] [Field M] [NumberField M]
    [Finite ι] [DecidableEq ι] (f : ι → E →+* M) (hf : Function.Injective f) (i : ι) :
    ∃ s : M, s ≠ 0 ∧ (Pi.single i s : ι → M) ∈
      Submodule.span (𝓞 M) (Set.range fun a : 𝓞 E => fun j => f j (a : E)) := by
  classical
  cases nonempty_fintype ι

  let χ : ι → (𝓞 E →* M) := fun j => ((f j).comp (algebraMap (𝓞 E) E)).toMonoidHom
  have hχ : Function.Injective χ := by
    intro j k h
    apply hf
    apply IsFractionRing.ringHom_ext (A := 𝓞 E)
    intro x
    exact DFunLike.congr_fun h x
  have hli : LinearIndependent M (fun j => (χ j : 𝓞 E → M)) :=
    (linearIndependent_monoidHom (𝓞 E) M).comp χ hχ

  have htop : Submodule.span M (Set.range fun a : 𝓞 E => fun j => f j (a : E)) = ⊤ := by
    by_contra hne
    obtain ⟨φ, hφ0, hφ⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hne)
    apply hφ0
    have hc : ∀ j, φ (fun k => if j = k then 1 else 0) = 0 := by
      have key : ∑ j, φ (fun k => if j = k then 1 else 0) • (χ j : 𝓞 E → M) = 0 := by
        funext a
        have ha : φ (fun j => f j (a : E)) = 0 := hφ (Submodule.subset_span ⟨a, rfl⟩)
        rw [LinearMap.pi_apply_eq_sum_univ] at ha
        simpa [χ, Finset.sum_apply, mul_comm] using ha
      exact Fintype.linearIndependent_iff.mp hli _ key
    refine LinearMap.ext fun x => ?_
    rw [LinearMap.pi_apply_eq_sum_univ]
    simp [hc]

  have h1 : (Pi.single i 1 : ι → M) ∈ Submodule.span M (Set.range fun a : 𝓞 E => fun j => f j (a : E)) := by
    rw [htop]; exact Submodule.mem_top
  obtain ⟨y, hy, z, hz⟩ := (IsLocalization.mem_span_iff (nonZeroDivisors (𝓞 M))).mp h1
  refine ⟨algebraMap (𝓞 M) M z, IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors z.2, ?_⟩
  have hy' : y = algebraMap (𝓞 M) M z • (Pi.single i 1 : ι → M) := by
    rw [hz, smul_smul, IsLocalization.mk'_spec', map_one, one_smul]
  have : (Pi.single i (algebraMap (𝓞 M) M z) : ι → M) = y := by
    rw [hy']
    ext k
    by_cases hk : k = i
    · subst hk; simp
    · simp [hk]
  rw [this]
  exact hy

open Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric

/- English proof (translation)
Establish `hb : H.𝔟 ≠ ⊥`. Introduce `h`. Establish `h2` using `H.𝔟_spec.2`. Simplify using `[h] at h2`. Establish `hle : (H.𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 H.E)) H.E) ≤ 1` using `FractionalIdeal.coeIdeal_le_one`.

Establish `hne : (H.𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 H.E)) H.E) ≠ 0` using `FractionalIdeal.coeIdeal_ne_zero.mpr hb`. Establish `h1 : (1 : FractionalIdeal (nonZeroDivisors (𝓞 H.E)) H.E) ≤ H.AA0`. Use `FractionalIdeal.inv_anti_mono hne one_ne_zero hle` as an intermediate fact. Simplify `this` using `[Host.AA0]`. Conclude with `h1 ((FractionalIdeal.mem_one_iff _).mpr ⟨a, rfl⟩)`.
-/
theorem integers_mem_inverse_half_different {R : Ranks} (H : Host R) (a : 𝓞 H.E) :
    (a : H.E) ∈ (H.AA0 : Submodule (𝓞 H.E) H.E) := by

  have hb : H.𝔟 ≠ ⊥ := by
    intro h
    have h2 := H.𝔟_spec.2
    simp [h] at h2
  have hle : (H.𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 H.E)) H.E) ≤ 1 := FractionalIdeal.coeIdeal_le_one
  have hne : (H.𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 H.E)) H.E) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.mpr hb

  have h1 : (1 : FractionalIdeal (nonZeroDivisors (𝓞 H.E)) H.E) ≤ H.AA0 := by
    have := FractionalIdeal.inv_anti_mono hne one_ne_zero hle
    simpa [Host.AA0] using this
  exact h1 ((FractionalIdeal.mem_one_iff _).mpr ⟨a, rfl⟩)

/- English proof (translation)
Introduce `g g' h`. Establish `hσ : H.sigmaOf g = H.sigmaOf g'`. Use extensionality with `x`. Establish `hx` using `DFunLike.congr_fun h x`. Simplify using `only [Host.emb, RingHom.comp_apply] at hx`.

Conclude with `H.φ₀.injective hx`. Conclude with `H.gal.symm.injective hσ`.
-/
theorem emb_injective {R : Ranks} (H : Host R) : Function.Injective H.emb := by
  intro g g' h
  have hσ : H.sigmaOf g = H.sigmaOf g' := by
    ext x
    have hx := DFunLike.congr_fun h x
    simp only [Host.emb, RingHom.comp_apply] at hx
    exact H.φ₀.injective hx
  exact H.gal.symm.injective hσ

/- English proof (translation)
Introduce `τ τ' h`. Conclude with `D.eTau.injective (Subtype.ext (emb_injective D.host h))`.
-/
theorem embT_injective (D : D7) : Function.Injective (embT D) := by
  intro τ τ' h
  exact D.eTau.injective (Subtype.ext (emb_injective D.host h))

/- English proof (translation)
Set `f : D.what₂.Tau → D.host.E →+* M` to `fun σ => (embT D σ).codRestrict M (hM σ)`. Establish `hf : Function.Injective f`. Introduce `σ σ' h`. Apply `embT_injective D` to reduce the goal to its premises. Use extensionality with `x`.

Conclude with `congrArg Subtype.val (DFunLike.congr_fun h x)`. Take `⟨s, hs0, hs⟩` from `exists_single_mem_span f hf τ`. Establish `hle : Submodule.span (𝓞 M) (Set.range fun a : 𝓞 D.host.E => fun j => f j (a : D.host.E)) ≤ mmM D M`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨a, rfl⟩`.

Use `Submodule.subset_span ⟨(a : D.host.E), integers_mem_inverse_half_different D.host a, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `j`. Unfold `Formalism.MainNotions.TaylorLogMetric.liftM`. Rewrite using `[dif_pos (hM j _)]`. Both sides reduce to the same expression.

Introduce `h`. Establish `hs' : s ∈ ellT D M τ`. Rewrite using `[ellT, Submodule.mem_comap]`. Simplify using `using hle hs`. Rewrite `hs'` using `[h, Submodule.mem_bot]`.

Conclude with `hs0 hs'`.
-/
theorem ellT_ne_bot {D : D7} {M : IntermediateField ℚ ℂ} [NumberField M]
    (hM : ∀ (τ : D.what₂.Tau) (x : D.host.E), (embT D τ : D.host.E → ℂ) x ∈ M)
    (τ : D.what₂.Tau) : ellT D M τ ≠ ⊥ := by
  classical

  let f : D.what₂.Tau → D.host.E →+* M := fun σ => (embT D σ).codRestrict M (hM σ)
  have hf : Function.Injective f := by
    intro σ σ' h
    apply embT_injective D
    ext x
    exact congrArg Subtype.val (DFunLike.congr_fun h x)
  obtain ⟨s, hs0, hs⟩ := exists_single_mem_span f hf τ

  have hle : Submodule.span (𝓞 M) (Set.range fun a : 𝓞 D.host.E => fun j => f j (a : D.host.E)) ≤ mmM D M := by
    rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    refine Submodule.subset_span ⟨(a : D.host.E), integers_mem_inverse_half_different D.host a, ?_⟩
    funext j
    unfold Formalism.MainNotions.TaylorLogMetric.liftM
    rw [dif_pos (hM j _)]
    rfl
  intro h
  have hs' : s ∈ ellT D M τ := by
    rw [ellT, Submodule.mem_comap]
    simpa using hle hs
  rw [h, Submodule.mem_bot] at hs'
  exact hs0 hs'

end GlobalTheory.InverseHalfDifferent
