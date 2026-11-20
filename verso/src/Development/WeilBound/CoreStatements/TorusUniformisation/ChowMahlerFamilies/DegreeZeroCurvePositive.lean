import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GenericCentreSpecializes
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LocalComponentsSurjective
import Development.AutomorphicSpectrum.Statements.GeometryStatements.PropZ
open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

namespace PositivityTheory.Xgn.CurvePositivity

/- English proof (translation)
Establish `hfM : f ^ M ≠ 0` using `pow_ne_zero _ hf`. Rewrite using `[div_pow, div_pow, div_pow, div_div_eq_mul_div, div_div_eq_mul_div]`. Distinguish the cases in `hσ : σ ^ M = 0`. Simplify using `[hσ]`. Clear the denominators using the available nonvanishing facts.
-/
theorem change_gen {Ω : Type} [Field Ω] (σ π e f : Ω) (M : ℕ) (hf : f ≠ 0) :
    π / (σ / e) ^ M = π / (σ / f) ^ M * (e / f) ^ M := by
  have hfM : f ^ M ≠ 0 := pow_ne_zero _ hf
  rw [div_pow, div_pow, div_pow, div_div_eq_mul_div, div_div_eq_mul_div]
  by_cases hσ : σ ^ M = 0
  · simp [hσ]
  · field_simp

/- English proof (translation)
Establish `ht0 : ∀ j, t j ≠ 0` using `fun j h => hc (by rw [hct j, h, zero_mul])`. Establish `hvt : ∀ j, C.v j (t j) ≠ 0` using `fun j => (Valuation.ne_zero_iff _).2 (ht0 j)`. Establish `hvr : ∀ j, C.v j (r j) ≠ 0` using `fun j => (Valuation.ne_zero_iff _).2 (hr j)`. Establish `hL : ∀ j, WithZero.log (C.v j c) = WithZero.log (C.v j (t j)) + (M : ℤ) * WithZero.log (C.v j (r j))`. Introduce `j`.

Rewrite using `[hct j, map_mul, map_pow, WithZero.log_mul (hvt j) (pow_ne_zero _ (hvr j)), WithZero.log_pow]`. Simplify using the standard rewrite rules. Establish `hle : ∀ j, WithZero.log (C.v j (t j)) ≤ 0`. Introduce `j`. Use `(WithZero.log_le_log (hvt j) one_ne_zero).2 (ht j)` as an intermediate fact.

Rewrite `this` using `[WithZero.log_one]`. Then use the resulting hypothesis. Use `set A : C.I → ℤ := fun j => (C.w j : ℤ) * WithZero.log (C.v j (t j)) with hA`. Use `set B : C.I → ℤ := fun j => (C.w j : ℤ) * WithZero.log (C.v j c) with hB`. Use `set D : C.I → ℤ := fun j => (C.w j : ℤ) * (-WithZero.log (C.v j (r j))) with hD`. Establish `hsB : (Function.support B).Finite` using `(C.fin c hc).subset (fun j hj => by`.

Simplify using `only [Function.mem_support, hB] at hj`. Introduce `h1`. Apply `hj` to reduce the goal to its premises. Rewrite using `[h1, WithZero.log_one, mul_zero])`. Establish `hsD : (Function.support D).Finite` using `hfin.subset (fun j hj => by`.

Simplify using `only [Function.mem_support, hD] at hj`. Introduce `h1`. Apply `hj` to reduce the goal to its premises. Rewrite using `[h1, WithZero.log_one, neg_zero, mul_zero])`. Establish `hABD : A = fun j => B j + (M : ℤ) * D j`.

Use function extensionality and compare the values at `j`. Simplify using `only [hA, hB, hD]`. Rewrite using `[hL j]`. Expand and normalize the polynomial expressions, which then agree. Establish `hsMD : (Function.support fun j => (M : ℤ) * D j).Finite` using `hsD.subset (Function.support_mul_subset_right _ _)`.

Establish `hsA : (Function.support A).Finite`. Rewrite using `[hABD]`. Conclude with `(hsB.union hsMD).subset (Function.support_add _ _)`. Establish `hsum : ∑ᶠ j, A j = 0`. Rewrite using `[hABD, finsum_add_distrib hsB hsMD, ← mul_finsum]`.

Simplify using `only [hB, hD]`. Rewrite using `[C.prod c hc, hd, mul_zero, add_zero]`. Establish `hnn : ∀ j, 0 ≤ -A j` using `fun j => by`. Simplify using `only [hA]`. Use `hle j` as an intermediate fact.

Use `hw j` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. Establish `hsA' : (Function.support fun j => -A j).Finite` using `hsA.subset (fun j hj => by simpa [Function.mem_support] using hj)`. Establish `h1` using `single_le_finsum i hsA' hnn`. Rewrite `h1` using `[finsum_neg_distrib, hsum, neg_zero]`.

Establish `h2 : WithZero.log (C.v i (t i)) = 0`. Establish `h3 : A i = 0` using `by have := hnn i; linarith`. Simplify using `only [hA] at h3`. Break down `mul_eq_zero.1 h3 with h4 | h4` into its components or cases. Conclude with `absurd h4 (by have := hw i; omega)`.

Conclude with `h4`. Rewrite using `[← WithZero.exp_log (hvt i), h2, WithZero.exp_zero]`.
-/
theorem val_one {K : Type} [Field K] (C : Crv.ACurve K) (hw : ∀ i, 0 < C.w i) (c : K) (hc : c ≠ 0)
    (r t : C.I → K) (M : ℕ) (hr : ∀ i, r i ≠ 0) (hfin : {i | C.v i (r i) ≠ 1}.Finite)
    (hd : ∑ᶠ i, (C.w i : ℤ) * (-WithZero.log (C.v i (r i))) = 0)
    (ht : ∀ i, C.v i (t i) ≤ 1) (hct : ∀ i, c = t i * r i ^ M) (i : C.I) : C.v i (t i) = 1 := by
  have ht0 : ∀ j, t j ≠ 0 := fun j h => hc (by rw [hct j, h, zero_mul])
  have hvt : ∀ j, C.v j (t j) ≠ 0 := fun j => (Valuation.ne_zero_iff _).2 (ht0 j)
  have hvr : ∀ j, C.v j (r j) ≠ 0 := fun j => (Valuation.ne_zero_iff _).2 (hr j)
  have hL : ∀ j, WithZero.log (C.v j c) =
      WithZero.log (C.v j (t j)) + (M : ℤ) * WithZero.log (C.v j (r j)) := by
    intro j
    rw [hct j, map_mul, map_pow, WithZero.log_mul (hvt j) (pow_ne_zero _ (hvr j)), WithZero.log_pow]
    simp
  have hle : ∀ j, WithZero.log (C.v j (t j)) ≤ 0 := by
    intro j
    have := (WithZero.log_le_log (hvt j) one_ne_zero).2 (ht j)
    rwa [WithZero.log_one] at this
  set A : C.I → ℤ := fun j => (C.w j : ℤ) * WithZero.log (C.v j (t j)) with hA
  set B : C.I → ℤ := fun j => (C.w j : ℤ) * WithZero.log (C.v j c) with hB
  set D : C.I → ℤ := fun j => (C.w j : ℤ) * (-WithZero.log (C.v j (r j))) with hD
  have hsB : (Function.support B).Finite := (C.fin c hc).subset (fun j hj => by
    simp only [Function.mem_support, hB] at hj
    intro h1; apply hj; rw [h1, WithZero.log_one, mul_zero])
  have hsD : (Function.support D).Finite := hfin.subset (fun j hj => by
    simp only [Function.mem_support, hD] at hj
    intro h1; apply hj; rw [h1, WithZero.log_one, neg_zero, mul_zero])
  have hABD : A = fun j => B j + (M : ℤ) * D j := by
    funext j; simp only [hA, hB, hD]; rw [hL j]; ring
  have hsMD : (Function.support fun j => (M : ℤ) * D j).Finite :=
    hsD.subset (Function.support_mul_subset_right _ _)
  have hsA : (Function.support A).Finite := by
    rw [hABD]; exact (hsB.union hsMD).subset (Function.support_add _ _)
  have hsum : ∑ᶠ j, A j = 0 := by
    rw [hABD, finsum_add_distrib hsB hsMD, ← mul_finsum]
    simp only [hB, hD]
    rw [C.prod c hc, hd, mul_zero, add_zero]
  have hnn : ∀ j, 0 ≤ -A j := fun j => by
    simp only [hA]; have := hle j; have := hw j; nlinarith
  have hsA' : (Function.support fun j => -A j).Finite :=
    hsA.subset (fun j hj => by simpa [Function.mem_support] using hj)
  have h1 := single_le_finsum i hsA' hnn
  rw [finsum_neg_distrib, hsum, neg_zero] at h1
  have h2 : WithZero.log (C.v i (t i)) = 0 := by
    have h3 : A i = 0 := by have := hnn i; linarith
    simp only [hA] at h3
    rcases mul_eq_zero.1 h3 with h4 | h4
    · exact absurd h4 (by have := hw i; omega)
    · exact h4
  rw [← WithZero.exp_log (hvt i), h2, WithZero.exp_zero]

end PositivityTheory.Xgn.CurvePositivity

/- English proof (translation)
Introduce `X Ω _ ξ O _ s _ _ ϖ L σ π M Γ hξ _ _ hdeg hreg hunit i h e he`. Take `⟨e0, f, r, he0, hf, hr, hfin, hd⟩` from `hdeg`. Establish `hf' : ∀ j, L.IsGenAt ⟨centre (Γ.z j), Γ.z_spec j⟩ (f j)` using `fun j => (hf j).2`. Take `⟨c, hc⟩` from `ProjectiveLinePlaces.valAt_of_unit Γ.η_spec (hunit e0 he0)`. Use `choose g hg using fun j => hreg _ _ (hf' j)`.

Set `t : ∀ j, (Γ.C.v j).valuationSubring` to `fun j => (Scheme.stalkClosedPointTo (Γ.z j)).hom (g j)`. Establish `hz : ∀ j, ValAt ξ (Γ.z j) (π / (σ / f j) ^ M) (t j)` using `fun j => ⟨Γ.z_spec j, g j, hg j, rfl⟩`. Establish `hη : ∀ j, ValAt ξ Γ.η (π / (σ / f j) ^ M) (t j : Γ.κ)` using `fun j => ProjectiveLinePlaces.valAt_restrict _ (Γ.z_gen j) Γ.η_spec (hz j)`. Establish `hct : ∀ j, (c : Γ.κ) = (t j : Γ.κ) * r j ^ M` using `fun j => by`. Establish `h2` using `CoordModel.valAt_mul (hη j) (ProjectiveLinePlaces.valAt_pow (hr j).2 M)`.

Rewrite `h2` using `[← PositivityTheory.Xgn.CurvePositivity.change_gen σ π e0 (f j) M (hf' j).1]`. Conclude with `CoordModel.valAt_unique hξ hc h2`. Establish `hv` using `PositivityTheory.Xgn.CurvePositivity.val_one Γ.C Γ.w_pos c c.ne_zero r (fun j => (t j : Γ.κ)) M (fun j => (hr j).1) hfin hd (fun j => (t j).2) hct i`. Establish `ht0 : (t i : Γ.κ) ≠ 0` using `fun h0 => by simp [h0] at hv`. Establish `hu : IsUnit (t i)`.

Use `IsUnit.of_mul_eq_one ⟨(t i : Γ.κ)⁻¹, ?_⟩ (Subtype.ext (mul_inv_cancel₀ ht0))` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Γ.C.v i _ ≤ 1`. Rewrite using `[map_inv₀, hv, inv_one]`. Establish `hgu : IsUnit (g i)` using `(Scheme.isLocalHom_stalkClosedPointTo' (Γ.z i)).map_nonunit (g i) hu`. Take `⟨u, hu1, hu2⟩` from `(CptModel.unitAt_iff ξ _ _).1 (ProjectiveLinePlaces.unitAt_div he (hf' i))`.

Use `(CptModel.unitAt_iff ξ _ _).2 ⟨g i * u ^ M, hgu.mul (hu1.pow M), ?_⟩` and prove the remaining obligations. Rewrite using `[PositivityTheory.Xgn.CurvePositivity.change_gen σ π e (f i) M (hf' i).1, map_mul, map_pow, hu2]`. Conclude with `congrArg (· * (e / f i) ^ M) (hg i)`.
-/
theorem PositivityTheory.Xgn.degree_zero_curve_positive : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (O : Type) [CommRing O] (s : X ⟶ Spec (CommRingCat.of O)) [IsSeparated s] [LocallyOfFiniteType s] (ϖ : Ω) (L : Lat ξ Ω) (σ π : Ω) (M : ℕ) (Γ : FibreCurve ξ ϖ), IsCptGen ξ → L.IsVB 1 ⊤ → 0 < M → Γ.HasDeg L 0 → (∀ (p : Cpt ξ) (e : Ω), L.IsGenAt p e → π / (σ / e) ^ M ∈ regAt ξ p) → (∀ e, L.IsGenAt ⟨centre Γ.η, Γ.η_spec⟩ e → unitAt ξ ⟨centre Γ.η, Γ.η_spec⟩ (π / (σ / e) ^ M)) → ∀ (i : Γ.C.I) (h : genPt ξ ⤳ centre (Γ.z i)) (e : Ω), L.IsGenAt ⟨centre (Γ.z i), h⟩ e → unitAt ξ ⟨centre (Γ.z i), h⟩ (π / (σ / e) ^ M) := by
  intro X Ω _ ξ O _ s _ _ ϖ L σ π M Γ hξ _ _ hdeg hreg hunit i h e he
  obtain ⟨e0, f, r, he0, hf, hr, hfin, hd⟩ := hdeg
  have hf' : ∀ j, L.IsGenAt ⟨centre (Γ.z j), Γ.z_spec j⟩ (f j) := fun j => (hf j).2
  obtain ⟨c, hc⟩ := ProjectiveLinePlaces.valAt_of_unit Γ.η_spec (hunit e0 he0)
  choose g hg using fun j => hreg _ _ (hf' j)
  let t : ∀ j, (Γ.C.v j).valuationSubring := fun j => (Scheme.stalkClosedPointTo (Γ.z j)).hom (g j)
  have hz : ∀ j, ValAt ξ (Γ.z j) (π / (σ / f j) ^ M) (t j) := fun j => ⟨Γ.z_spec j, g j, hg j, rfl⟩
  have hη : ∀ j, ValAt ξ Γ.η (π / (σ / f j) ^ M) (t j : Γ.κ) := fun j =>
    ProjectiveLinePlaces.valAt_restrict _ (Γ.z_gen j) Γ.η_spec (hz j)
  have hct : ∀ j, (c : Γ.κ) = (t j : Γ.κ) * r j ^ M := fun j => by
    have h2 := CoordModel.valAt_mul (hη j) (ProjectiveLinePlaces.valAt_pow (hr j).2 M)
    rw [← PositivityTheory.Xgn.CurvePositivity.change_gen σ π e0 (f j) M (hf' j).1] at h2
    exact CoordModel.valAt_unique hξ hc h2
  have hv := PositivityTheory.Xgn.CurvePositivity.val_one Γ.C Γ.w_pos c c.ne_zero r (fun j => (t j : Γ.κ)) M
    (fun j => (hr j).1) hfin hd (fun j => (t j).2) hct i
  have ht0 : (t i : Γ.κ) ≠ 0 := fun h0 => by simp [h0] at hv
  have hu : IsUnit (t i) := by
    refine IsUnit.of_mul_eq_one ⟨(t i : Γ.κ)⁻¹, ?_⟩ (Subtype.ext (mul_inv_cancel₀ ht0))
    change Γ.C.v i _ ≤ 1
    rw [map_inv₀, hv, inv_one]
  have hgu : IsUnit (g i) := (Scheme.isLocalHom_stalkClosedPointTo' (Γ.z i)).map_nonunit (g i) hu
  obtain ⟨u, hu1, hu2⟩ := (CptModel.unitAt_iff ξ _ _).1 (ProjectiveLinePlaces.unitAt_div he (hf' i))
  refine (CptModel.unitAt_iff ξ _ _).2 ⟨g i * u ^ M, hgu.mul (hu1.pow M), ?_⟩
  rw [PositivityTheory.Xgn.CurvePositivity.change_gen σ π e (f i) M (hf' i).1, map_mul, map_pow, hu2]
  exact congrArg (· * (e / f i) ^ M) (hg i)
