import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.SectionsHaveFiniteDimension
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ExistsMulMemAdjoinOfMemPowRange
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.RingKrullDimQuotientLeOne
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ExistsSectionRing
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.RingKrullDimOfEtaleMvPolynomial
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsIntegralOfIsAbelianSchemeField
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.CardZerosOnTorsionCosetLe
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.MulAPullbackIsoPowSqSymmetricAbelianVarietyStatement

noncomputable section

namespace GlobalTheory.TorsionZero

section Core

open MvPolynomial

variable {K R : Type} [Field K] [CommRing R] [Algebra K R]

/- English proof (translation)
Set `S : Set R` to `Set.range x ∪ ({s} ∪ Set.range f)`. Establish `hS : ∀ y ∈ S, ∃ e, y ∈ 𝒜 (N * e)`. Introduce and unpack `y (⟨j, rfl⟩ | rfl | ⟨j, rfl⟩)`. Conclude with `⟨1, by simpa using hx j⟩`. Conclude with `⟨d, hs⟩`.

Conclude with `⟨a, hf j⟩`. Establish `hSfin : S.Finite` using `(Set.finite_range x).union ((Set.finite_singleton s).union (Set.finite_range f))`. Take `⟨inst⟩` from `nonempty_gradedAlgebra_subGrading 𝒜 hN S hS`. Use `set T := Algebra.adjoin K S with hT`. Use `set ℬ := subGrading 𝒜 N T with hℬ`.

Set `x' : Fin m → T` to `fun j => ⟨x j, Algebra.subset_adjoin (Or.inl ⟨j, rfl⟩)⟩`. Set `s' : T` to `⟨s, Algebra.subset_adjoin (Or.inr (Or.inl rfl))⟩`. Set `f' : ι → T` to `fun j => ⟨f j, Algebra.subset_adjoin (Or.inr (Or.inr ⟨j, rfl⟩))⟩`. Establish `hx' : ∀ j, x' j ∈ ℬ 1` using `fun j => by`. Rewrite using `[hℬ, mem_subGrading]`.

Simplify using `using hx j`. Establish `hval : ∀ G : MvPolynomial (Fin m) K, ((aeval x' G : T) : R) = aeval x G` using `fun G => comp_aeval_apply x' T.val G`. Establish `hform' : ∀ e, ∀ y ∈ ℬ e, ∀ i, ∃ (n : ℕ) (G : MvPolynomial (Fin m) K), G.IsHomogeneous (n + e) ∧ y * x' i ^ n = aeval x' G` using `fun e y hy i => by`. Take `⟨n, G, hG, h⟩` from `hform e y hy i`. Conclude with `⟨n, G, hG, Subtype.ext (by rw [hval, ← h]; rfl)⟩`.

Use `haveI : Algebra.FiniteType K T := Algebra.FiniteType.adjoin_of_finite hSfin`. Use `haveI : Algebra.IsIntegral (Algebra.adjoin K (Set.range x')) T := ⟨fun y => by`. Proceed by induction on `y using DirectSum.Decomposition.inductionOn ℬ with`. Consider the case `zero => exact isIntegral_zero`. Consider the case `@homogeneous e y`.

Use `isIntegral_adjoin_of_mul_pow_mem K T ℬ m x' hx' ⟨i₀, fun h => hx₀ (congrArg Subtype.val h)⟩ e y y.2 fun i => ?_` and prove the remaining obligations. Take `⟨n, G, -, h⟩` from `hform' e y y.2 i`. Use `⟨n, ?_⟩` and prove the remaining obligations. Rewrite using `[h, Algebra.adjoin_range_eq_range_aeval]`. Conclude with `⟨G, rfl⟩`.

Consider the case `add a b ha hb => exact ha.add hb⟩`. Use `haveI : Algebra.FiniteType (Algebra.adjoin K (Set.range x')) T := Algebra.FiniteType.of_restrictScalars_finiteType K _ _`. Establish `hdim : ringKrullDim T = (g + 1 : ℕ)` using `ringKrullDim_cone ℬ hx' r i₀ hi₀ hr (fun n G hG => by`. Rewrite using `[← hrel n G hG, ← hval]`. Conclude with `⟨fun h => by rw [h]; rfl, fun h => Subtype.ext h⟩) g hC`.

Use `haveI : Finite {p : Pt // p ∈ Z ∧ ev p s = 0} := (hZ.subset (fun p hp => hp.1 : {p | p ∈ Z ∧ ev p s = 0} ⊆ Z)).to_subtype`. Set `E` to `(Finite.equivFin {p : Pt // p ∈ Z ∧ ev p s = 0}).symm`. Use `graded_bezout_bound K T ℬ m g B d a x' s' (Set.range f') hg hx' Algebra.IsIntegral.finite hdim (fun e he => ?_) hs (fun h => hs0 (congrArg Subtype.val h)) ?_ ⟨(fun p => (ev p).comp T.val) '' Z, hZ.image _, fun φ hφ hφf => ?_⟩ _ (fun j => (ev (E j).1).comp T.val) (fun j => hcov _) …` and prove the remaining obligations. Take `⟨h1, h2⟩` from `hfin e he`. Use `le_trans ?_ h2` and prove the remaining obligations.

Use `LinearMap.finrank_le_finrank_of_injective (f := T.val.toLinearMap.restrict (p := ℬ e) (q := 𝒜 (N * e)) fun y hy => hy) fun y z h => ?_` and prove the remaining obligations. Establish `h3` using `congrArg Subtype.val h`. Conclude with `Subtype.ext (Subtype.ext h3)`. Introduce and unpack `_ ⟨j, rfl⟩`. Conclude with `hf j`.

Take `⟨i, hi⟩` from `hφ`. Take `⟨p, hp, hp'⟩` from `hpt (fun j => φ (x' j) * (φ (x' i))⁻¹) i (mul_inv_cancel₀ hi) fun n G hG h => by`. Establish `h0 : aeval x' G = 0` using `Subtype.ext (by rw [hval, h]; rfl)`. Rewrite using `[aeval_mul_of_isHomogeneous _ _ hG, ← comp_aeval_apply, h0, map_zero, zero_mul]`. Establish `hc : ∀ e, ∀ y ∈ ℬ e, φ y = (φ (x' i) * (ev p (x i))⁻¹) ^ e * (ev p).comp T.val y` using `fun e y hy => by`.

Take `⟨n, G, hG, h⟩` from `hform' e y hy i`. Use `map_eq_pow_mul (fun j => ?_) hi hG h` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `_ = ev p (x j) * _`. Rewrite using `[hp' j]`. Clear the denominators using the available nonvanishing facts.

Use `⟨_, ⟨p, (hZf p).2 fun j => ?_, rfl⟩, _, hc⟩` and prove the remaining obligations. Establish `h1` using `hc a (f' j) (hf j)`. Rewrite `h1` using `[hφf _ ⟨j, rfl⟩]`. Conclude with `(mul_eq_zero.1 h1.symm).resolve_left (pow_ne_zero _ (mul_ne_zero hi (inv_ne_zero hp)))`. Introduce and unpack `_ ⟨l, rfl⟩`.

Conclude with `(hZf _).1 (E j).2.1 l`. Introduce and unpack `j j' ⟨c, hc⟩`. Use `E.injective (Subtype.ext (hsep _ _ c fun l => ?_).symm)` and prove the remaining obligations. Simplify using `using hc 1 _ (hx' l)`.
-/
theorem card_zeros_le_of_growth [IsAlgClosed K] [IsDomain R] (𝒜 : ℕ → Submodule K R) [GradedAlgebra 𝒜]
    {m g N B d a : ℕ} (hg : 1 ≤ g) (hN : 1 ≤ N) (x : Fin m → R) (hx : ∀ j, x j ∈ 𝒜 N)
    (hform : ∀ e, ∀ y ∈ 𝒜 (N * e), ∀ i, ∃ (n : ℕ) (G : MvPolynomial (Fin m) K),
      G.IsHomogeneous (n + e) ∧ y * x i ^ n = aeval x G)
    {C : Type} [CommRing C] [IsDomain C] [Algebra K C] (r : Fin m → C) (i₀ : Fin m) (hi₀ : r i₀ = 1)
    (hx₀ : x i₀ ≠ 0)
    (hr : Function.Surjective (aeval r : MvPolynomial (Fin m) K →ₐ[K] C))
    (hrel : ∀ n (G : MvPolynomial (Fin m) K), G.IsHomogeneous n → (aeval x G = 0 ↔ aeval r G = 0))
    (hC : ringKrullDim C = g)
    (hfin : ∀ e, 1 ≤ e → Module.Finite K (𝒜 (N * e)) ∧ Module.finrank K (𝒜 (N * e)) ≤ (B * e) ^ g)
    (s : R) (hs : s ∈ 𝒜 (N * d)) (hs0 : s ≠ 0) {ι : Type} [Finite ι] (f : ι → R)
    (hf : ∀ j, f j ∈ 𝒜 (N * a)) {Pt : Type} (ev : Pt → (R →ₐ[K] K))
    (hcov : ∀ p, ∃ i, ev p (x i) ≠ 0)
    (hpt : ∀ (v : Fin m → K) (i : Fin m), v i = 1 →
      (∀ n (G : MvPolynomial (Fin m) K), G.IsHomogeneous n → aeval x G = 0 → aeval v G = 0) →
      ∃ p, ev p (x i) ≠ 0 ∧ ∀ j, ev p (x j) = v j * ev p (x i))
    (hsep : ∀ p q (c : K), (∀ j, ev p (x j) = c * ev q (x j)) → p = q)
    (Z : Set Pt) (hZ : Z.Finite) (hZf : ∀ p, p ∈ Z ↔ ∀ j, ev p (f j) = 0) :
    Nat.card {p : Pt // p ∈ Z ∧ ev p s = 0} ≤ B ^ g * g.factorial * d * a ^ (g - 1) := by
  classical
  let S : Set R := Set.range x ∪ ({s} ∪ Set.range f)
  have hS : ∀ y ∈ S, ∃ e, y ∈ 𝒜 (N * e) := by
    rintro y (⟨j, rfl⟩ | rfl | ⟨j, rfl⟩)
    · exact ⟨1, by simpa using hx j⟩
    · exact ⟨d, hs⟩
    · exact ⟨a, hf j⟩
  have hSfin : S.Finite := (Set.finite_range x).union ((Set.finite_singleton s).union (Set.finite_range f))
  obtain ⟨inst⟩ := nonempty_gradedAlgebra_subGrading 𝒜 hN S hS
  set T := Algebra.adjoin K S with hT
  set ℬ := subGrading 𝒜 N T with hℬ
  let x' : Fin m → T := fun j => ⟨x j, Algebra.subset_adjoin (Or.inl ⟨j, rfl⟩)⟩
  let s' : T := ⟨s, Algebra.subset_adjoin (Or.inr (Or.inl rfl))⟩
  let f' : ι → T := fun j => ⟨f j, Algebra.subset_adjoin (Or.inr (Or.inr ⟨j, rfl⟩))⟩
  have hx' : ∀ j, x' j ∈ ℬ 1 := fun j => by
    rw [hℬ, mem_subGrading]
    simpa using hx j
  have hval : ∀ G : MvPolynomial (Fin m) K, ((aeval x' G : T) : R) = aeval x G := fun G =>
    comp_aeval_apply x' T.val G
  have hform' : ∀ e, ∀ y ∈ ℬ e, ∀ i, ∃ (n : ℕ) (G : MvPolynomial (Fin m) K),
      G.IsHomogeneous (n + e) ∧ y * x' i ^ n = aeval x' G := fun e y hy i => by
    obtain ⟨n, G, hG, h⟩ := hform e y hy i
    exact ⟨n, G, hG, Subtype.ext (by rw [hval, ← h]; rfl)⟩
  haveI : Algebra.FiniteType K T := Algebra.FiniteType.adjoin_of_finite hSfin
  haveI : Algebra.IsIntegral (Algebra.adjoin K (Set.range x')) T := ⟨fun y => by
    induction y using DirectSum.Decomposition.inductionOn ℬ with
    | zero => exact isIntegral_zero
    | @homogeneous e y =>
      refine isIntegral_adjoin_of_mul_pow_mem K T ℬ m x' hx' ⟨i₀, fun h => hx₀ (congrArg Subtype.val h)⟩ e y y.2 fun i => ?_
      obtain ⟨n, G, -, h⟩ := hform' e y y.2 i
      refine ⟨n, ?_⟩
      rw [h, Algebra.adjoin_range_eq_range_aeval]
      exact ⟨G, rfl⟩
    | add a b ha hb => exact ha.add hb⟩
  haveI : Algebra.FiniteType (Algebra.adjoin K (Set.range x')) T :=
    Algebra.FiniteType.of_restrictScalars_finiteType K _ _
  have hdim : ringKrullDim T = (g + 1 : ℕ) :=
    ringKrullDim_cone ℬ hx' r i₀ hi₀ hr (fun n G hG => by
      rw [← hrel n G hG, ← hval]
      exact ⟨fun h => by rw [h]; rfl, fun h => Subtype.ext h⟩) g hC
  haveI : Finite {p : Pt // p ∈ Z ∧ ev p s = 0} :=
    (hZ.subset (fun p hp => hp.1 : {p | p ∈ Z ∧ ev p s = 0} ⊆ Z)).to_subtype
  let E := (Finite.equivFin {p : Pt // p ∈ Z ∧ ev p s = 0}).symm
  refine graded_bezout_bound K T ℬ m g B d a x' s' (Set.range f') hg hx' Algebra.IsIntegral.finite hdim
    (fun e he => ?_) hs (fun h => hs0 (congrArg Subtype.val h)) ?_
    ⟨(fun p => (ev p).comp T.val) '' Z, hZ.image _, fun φ hφ hφf => ?_⟩ _
    (fun j => (ev (E j).1).comp T.val) (fun j => hcov _) (fun j => ⟨(E j).2.2, ?_⟩) ?_
  · obtain ⟨h1, h2⟩ := hfin e he
    refine le_trans ?_ h2
    refine LinearMap.finrank_le_finrank_of_injective
      (f := T.val.toLinearMap.restrict (p := ℬ e) (q := 𝒜 (N * e)) fun y hy => hy) fun y z h => ?_
    have h3 := congrArg Subtype.val h
    exact Subtype.ext (Subtype.ext h3)
  · rintro _ ⟨j, rfl⟩
    exact hf j
  · obtain ⟨i, hi⟩ := hφ
    obtain ⟨p, hp, hp'⟩ := hpt (fun j => φ (x' j) * (φ (x' i))⁻¹) i (mul_inv_cancel₀ hi)
      fun n G hG h => by
        have h0 : aeval x' G = 0 := Subtype.ext (by rw [hval, h]; rfl)
        rw [aeval_mul_of_isHomogeneous _ _ hG, ← comp_aeval_apply, h0, map_zero, zero_mul]
    have hc : ∀ e, ∀ y ∈ ℬ e, φ y = (φ (x' i) * (ev p (x i))⁻¹) ^ e * (ev p).comp T.val y :=
      fun e y hy => by
        obtain ⟨n, G, hG, h⟩ := hform' e y hy i
        refine map_eq_pow_mul (fun j => ?_) hi hG h
        change _ = ev p (x j) * _
        rw [hp' j]
        field_simp
    refine ⟨_, ⟨p, (hZf p).2 fun j => ?_, rfl⟩, _, hc⟩
    have h1 := hc a (f' j) (hf j)
    rw [hφf _ ⟨j, rfl⟩] at h1
    exact (mul_eq_zero.1 h1.symm).resolve_left (pow_ne_zero _ (mul_ne_zero hi (inv_ne_zero hp)))
  · rintro _ ⟨l, rfl⟩
    exact (hZf _).1 (E j).2.1 l
  · rintro j j' ⟨c, hc⟩
    refine E.injective (Subtype.ext (hsep _ _ c fun l => ?_).symm)
    simpa using hc 1 _ (hx' l)

end Core

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZV

/- English proof (translation)
Substitute `hU` using the available equality. Use `choose ev hev hevr using fun z => exists_ev p Φ ρ hL hρc hρ (pt z) (hpt z)`. Use `letI alg : ∀ i, Algebra K Γ(X, Out.nonzeroLocus (s i)) := fun i => (constHom p _).toAlgebra`. Establish `hgen' : ∀ i, Function.Surjective (MvPolynomial.aeval (r i) : MvPolynomial (Fin m) K →ₐ[K] _)` using `fun i f => by`. Take `⟨F, hF⟩` from `hgen i f`.

Conclude with `⟨F, hF.symm⟩`. Establish `hch` using `fun i hi => chart_facts p Φ ρ hL hρc hρ s i hi (fun _ => rfl) (r i) (hr i) (hgen' i)`. Establish `hmem : ∀ y : X, ∃ i, y ∈ Out.nonzeroLocus (s i)` using `fun y => TopologicalSpace.Opens.mem_iSup.1 (by rw [hcov]; trivial)`. Use `set x : Fin m → R := fun j => (Φ N (s j) : R) with hx`. Establish `hxz : ∀ z i, ev z (x i) ≠ 0 ↔ ⊤ ≤ pt z ⁻¹ᵁ Out.nonzeroLocus (s i)` using `fun z i => hev z N (s i)`.

Establish `hxr : ∀ z i (h : ⊤ ≤ pt z ⁻¹ᵁ Out.nonzeroLocus (s i)) j, ev z (x j) = val (pt z) _ h (r i j) * ev z (x i)` using `fun z i h j => hevr z N (s j) (s i) _ h (r i j) (hr i j)`. Establish `hcov' : ∀ z, ∃ i, ev z (x i) ≠ 0` using `fun z => by`. Take `⟨i, hi⟩` from `hmem (pt z (default : PrimeSpectrum K))`. Conclude with `⟨i, (hxz z i).2 ((top_le_iff _ _).2 hi)⟩`. Establish `hsep : ∀ z w (c : K), (∀ j, ev z (x j) = c * ev w (x j)) → z = w` using `fun z w c h => by`.

Take `⟨i, hi⟩` from `hcov' z`. Establish `hi' : ev w (x i) ≠ 0` using `fun h0 => hi (by rw [h i, h0, mul_zero])`. Establish `hz` using `(hxz z i).1 hi`. Establish `hw` using `(hxz w i).1 hi'`. Use `hinj (point_ext (haff i) hz hw (RingHom.ext fun f => ?_))` and prove the remaining obligations.

Take `⟨F, rfl⟩` from `hgen i f`. Rewrite using `[MvPolynomial.eval₂_comp_left, MvPolynomial.eval₂_comp_left]`. Use `congr 1`. Conclude with `RingHom.ext fun t => (val_const p _ (hpt z) _ hz t).trans (val_const p _ (hpt w) _ hw t).symm`. Use function extensionality and compare the values at `j`.

Use `mul_right_cancel₀ hi ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `val (pt z) _ hz (r i j) * _ = val (pt w) _ hw (r i j) * _`. Rewrite using `[← hxr z i hz j, h j, h i, hxr w i hw j]`. Expand and normalize the polynomial expressions, which then agree. Take `⟨i₀, hi₀⟩` from `hcov' b`.

Establish `hb` using `(hxz b i₀).1 hi₀`. Establish `hη : genericPoint X ∈ Out.nonzeroLocus (s i₀)` using `genericPoint_mem ((top_le_iff _ _).1 hb)`. Establish `hlin : ∀ j, x j - (ev b (x j) * (ev b (x i₀))⁻¹) • x i₀ ∈ 𝒜 N` using `fun j => sub_mem (Φ N (s j)).2 (Submodule.smul_mem _ _ (Φ N (s i₀)).2)`. Use `choose h' hh' using fun j => hpull ((Φ N).symm ⟨_, hlin j⟩)`. Establish `hzero : ∀ z j, ev z (Φ _ (h' j)) = 0 ↔ ev (ν z) (x j) = ev b (x j) * (ev b (x i₀))⁻¹ * ev (ν z) (x i₀)` using `fun z j => by`.

Rewrite using `[← not_iff_not]`. Use `(hev z _ (h' j)).trans ((hh' j z).trans ((hev (ν z) N _).symm.trans ?_))` and prove the remaining obligations. Rewrite using `[Equiv.apply_symm_apply]`. Express the relevant statement in the definitionally equal form `ev (ν z) (x j - _ • x i₀) ≠ 0 ↔ _`. Rewrite using `[map_sub, map_smul, smul_eq_mul, sub_ne_zero]`.

Establish `: Nonempty (Out.nonzeroLocus (s i₀))` using `⟨⟨_, hη⟩⟩`. Establish `key` using `card_zeros_le_of_growth 𝒜 (B := B) (d := d) (a := a) hg hN x (fun j => (Φ N (s j)).2) (fun e y hy i => ?_) (r i₀) i₀ (hch i₀ hη).1 (fun h => hi₀ (by rw [h, map_zero])) (hgen' i₀) (hch i₀ hη).2.1 (hdim _ (haff i₀) ⟨_, hη⟩) (fun e he => ?_) (Φ _ u) (Subtype.prop _) (fun h => ?_) (f …`. Use `le_trans (le_of_eq (Nat.card_congr (Equiv.subtypeEquivRight fun z => ?_))) key` and prove the remaining obligations. Use `and_congr Iff.rfl ?_` and prove the remaining obligations. Rewrite using `[← hev z _ u, not_not]`.

Distinguish the cases in `hi : genericPoint X ∈ Out.nonzeroLocus (s i)`. Conclude with `(hch i hi).2.2 e y hy`. Use `⟨1, 0, MvPolynomial.isHomogeneous_zero _ _ _, ?_⟩` and prove the remaining obligations. Rewrite using `[show x i = 0 from eq_zero_of_not_mem Φ ρ hL hρ (s i) hi]`. Simplify using the standard rewrite rules.

Take `⟨n, hn, c, hc⟩` from `hspan e he`. Take `⟨h1, h2⟩` from `finrank_le_of_span p Φ ρ hL hρc hρ _ _ c hc`. Conclude with `⟨h1, h2.trans hn⟩`. Take `⟨j, hj⟩` from `hu`. Conclude with `hj ((hρ j _ u).symm.trans ((congrArg (ρ j) h).trans (map_zero _)))`.

Establish `hi : genericPoint X ∈ Out.nonzeroLocus (s i)`. Assume the negation of the conclusion as `hi`. Establish `h1` using `h 1 (MvPolynomial.X i) (MvPolynomial.isHomogeneous_X K i) ((MvPolynomial.aeval_X _ _).trans (eq_zero_of_not_mem Φ ρ hL hρ (s i) hi))`. Rewrite `h1` using `[MvPolynomial.aeval_X, hv]`. Conclude with `one_ne_zero h1`.

Take `⟨χ, hχ⟩` from `exists_algHom_of_relations (r i) i (hch i hi).1 (hgen' i) v hv fun n G hG h0 => h n G hG (((hch i hi).2.1 n G hG).2 h0)`. Take `⟨z, hz, hzi, hzv⟩` from `exists_point p (haff i) χ.toRingHom fun t => χ.commutes t`. Take `⟨w, rfl⟩` from `hsurj z hz`. Use `⟨w, (hxz w i).2 hzi, fun j => ?_⟩` and prove the remaining obligations. Rewrite using `[hxr w i hzi j, hzv]`.

Conclude with `congrArg (· * _) (hχ j)`. Simplify using `only [hzero]`. Use `⟨fun h j => ?_, fun h => hsep _ _ (ev (ν z) (x i₀) * (ev b (x i₀))⁻¹) fun j => ?_⟩` and prove the remaining obligations. Rewrite using `[show ν z = b from h, inv_mul_cancel_right₀ hi₀]`. Rewrite using `[h j]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem card_fibre_zeros_le_of_growth {K : Type} [Field K] [IsAlgClosed K] {X : Scheme.{0}} [IsIntegral X]
    (p : X ⟶ Sp K) {L : LB X} (hL : L.IsLB) {R : Type} [CommRing R] [IsDomain R] [Algebra K R]
    {𝒜 : ℕ → Submodule K R} [GradedAlgebra 𝒜] (Φ : ∀ e : ℕ, (lbPow L e).Sec ≃ 𝒜 e)
    (ρ : ∀ j : PUnit → L.ι, R →+* Γ(X, (lbPow L 0).U j))
    (hρc : ∀ j a, ρ j (algebraMap K R a) = constFn p _ a)
    (hρ : ∀ j e (s : (lbPow L e).Sec), ρ j (Φ e s) = s.f j)
    {m g N B d a : ℕ} (hg : 1 ≤ g) (hN : 1 ≤ N) (s : Fin m → (lbPow L N).Sec)
    (U : Fin m → X.Opens) (hU : (fun i => Out.nonzeroLocus (s i)) = U)
    (hcov : ⨆ i, U i = ⊤) (haff : ∀ i, IsAffineOpen (U i))
    (r : ∀ i, Fin m → Γ(X, U i))
    (hr : ∀ i j k, resG X (inf_le_right : U i ⊓ (lbPow L N).U k ≤ _) ((s j).f k) =
      resG X inf_le_left (r i j) * resG X inf_le_right ((s i).f k))
    (hgen : ∀ i (f : Γ(X, U i)), ∃ F : MvPolynomial (Fin m) K,
      f = MvPolynomial.eval₂ (constHom p _) (r i) F)
    (hdim : ∀ U : X.Opens, IsAffineOpen U → (U : Set X).Nonempty → ringKrullDim Γ(X, U) = g)
    (hspan : ∀ e, 1 ≤ e → ∃ n ≤ (B * e) ^ g, ∃ b : Fin n → (lbPow L (N * e)).Sec,
      ∀ t : (lbPow L (N * e)).Sec, ∃ c : Fin n → K, ∀ j, t.f j = ∑ i, constFn p _ (c i) * (b i).f j)
    {Pt : Type} (pt : Pt → (Sp K ⟶ X)) (hpt : ∀ z, pt z ≫ p = 𝟙 _) (hinj : Function.Injective pt)
    (hsurj : ∀ z : Sp K ⟶ X, z ≫ p = 𝟙 _ → ∃ w, pt w = z)
    (ν : Pt → Pt) (b : Pt) (hfin : {z | ν z = b}.Finite)
    (hpull : ∀ h : (lbPow L N).Sec, ∃ h' : (lbPow L (N * a)).Sec, ∀ z,
      ⊤ ≤ pt z ⁻¹ᵁ Out.nonzeroLocus h' ↔ ⊤ ≤ pt (ν z) ⁻¹ᵁ Out.nonzeroLocus h)
    (u : (lbPow L (N * d)).Sec) (hu : ∃ j, u.f j ≠ 0) :
    Nat.card {z : Pt // ν z = b ∧ ¬ ⊤ ≤ pt z ⁻¹ᵁ Out.nonzeroLocus u} ≤
      B ^ g * g.factorial * d * a ^ (g - 1) := by
  subst hU
  choose ev hev hevr using fun z => exists_ev p Φ ρ hL hρc hρ (pt z) (hpt z)
  letI alg : ∀ i, Algebra K Γ(X, Out.nonzeroLocus (s i)) := fun i => (constHom p _).toAlgebra
  have hgen' : ∀ i, Function.Surjective (MvPolynomial.aeval (r i) : MvPolynomial (Fin m) K →ₐ[K] _) :=
    fun i f => by
      obtain ⟨F, hF⟩ := hgen i f
      exact ⟨F, hF.symm⟩
  have hch := fun i hi => chart_facts p Φ ρ hL hρc hρ s i hi (fun _ => rfl) (r i) (hr i) (hgen' i)
  have hmem : ∀ y : X, ∃ i, y ∈ Out.nonzeroLocus (s i) := fun y =>
    TopologicalSpace.Opens.mem_iSup.1 (by rw [hcov]; trivial)
  set x : Fin m → R := fun j => (Φ N (s j) : R) with hx
  have hxz : ∀ z i, ev z (x i) ≠ 0 ↔ ⊤ ≤ pt z ⁻¹ᵁ Out.nonzeroLocus (s i) := fun z i => hev z N (s i)
  have hxr : ∀ z i (h : ⊤ ≤ pt z ⁻¹ᵁ Out.nonzeroLocus (s i)) j,
      ev z (x j) = val (pt z) _ h (r i j) * ev z (x i) := fun z i h j =>
    hevr z N (s j) (s i) _ h (r i j) (hr i j)
  have hcov' : ∀ z, ∃ i, ev z (x i) ≠ 0 := fun z => by
    obtain ⟨i, hi⟩ := hmem (pt z (default : PrimeSpectrum K))
    exact ⟨i, (hxz z i).2 ((top_le_iff _ _).2 hi)⟩
  have hsep : ∀ z w (c : K), (∀ j, ev z (x j) = c * ev w (x j)) → z = w := fun z w c h => by
    obtain ⟨i, hi⟩ := hcov' z
    have hi' : ev w (x i) ≠ 0 := fun h0 => hi (by rw [h i, h0, mul_zero])
    have hz := (hxz z i).1 hi
    have hw := (hxz w i).1 hi'
    refine hinj (point_ext (haff i) hz hw (RingHom.ext fun f => ?_))
    obtain ⟨F, rfl⟩ := hgen i f
    rw [MvPolynomial.eval₂_comp_left, MvPolynomial.eval₂_comp_left]
    congr 1
    · exact RingHom.ext fun t => (val_const p _ (hpt z) _ hz t).trans (val_const p _ (hpt w) _ hw t).symm
    · funext j
      refine mul_right_cancel₀ hi ?_
      change val (pt z) _ hz (r i j) * _ = val (pt w) _ hw (r i j) * _
      rw [← hxr z i hz j, h j, h i, hxr w i hw j]
      ring
  obtain ⟨i₀, hi₀⟩ := hcov' b
  have hb := (hxz b i₀).1 hi₀
  have hη : genericPoint X ∈ Out.nonzeroLocus (s i₀) := genericPoint_mem ((top_le_iff _ _).1 hb)
  have hlin : ∀ j, x j - (ev b (x j) * (ev b (x i₀))⁻¹) • x i₀ ∈ 𝒜 N := fun j =>
    sub_mem (Φ N (s j)).2 (Submodule.smul_mem _ _ (Φ N (s i₀)).2)
  choose h' hh' using fun j => hpull ((Φ N).symm ⟨_, hlin j⟩)
  have hzero : ∀ z j, ev z (Φ _ (h' j)) = 0 ↔
      ev (ν z) (x j) = ev b (x j) * (ev b (x i₀))⁻¹ * ev (ν z) (x i₀) := fun z j => by
    rw [← not_iff_not]
    refine (hev z _ (h' j)).trans ((hh' j z).trans ((hev (ν z) N _).symm.trans ?_))
    rw [Equiv.apply_symm_apply]
    change ev (ν z) (x j - _ • x i₀) ≠ 0 ↔ _
    rw [map_sub, map_smul, smul_eq_mul, sub_ne_zero]
  have : Nonempty (Out.nonzeroLocus (s i₀)) := ⟨⟨_, hη⟩⟩
  have key := card_zeros_le_of_growth 𝒜 (B := B) (d := d) (a := a) hg hN x (fun j => (Φ N (s j)).2)
    (fun e y hy i => ?_) (r i₀) i₀ (hch i₀ hη).1 (fun h => hi₀ (by rw [h, map_zero])) (hgen' i₀)
    (hch i₀ hη).2.1 (hdim _ (haff i₀) ⟨_, hη⟩) (fun e he => ?_) (Φ _ u) (Subtype.prop _) (fun h => ?_)
    (fun j => (Φ _ (h' j) : R)) (fun j => Subtype.prop _) ev hcov' (fun v i hv h => ?_) hsep
    {z | ν z = b} hfin fun z => ?_
  · refine le_trans (le_of_eq (Nat.card_congr (Equiv.subtypeEquivRight fun z => ?_))) key
    refine and_congr Iff.rfl ?_
    rw [← hev z _ u, not_not]
  · by_cases hi : genericPoint X ∈ Out.nonzeroLocus (s i)
    · exact (hch i hi).2.2 e y hy
    · refine ⟨1, 0, MvPolynomial.isHomogeneous_zero _ _ _, ?_⟩
      rw [show x i = 0 from eq_zero_of_not_mem Φ ρ hL hρ (s i) hi]
      simp
  · obtain ⟨n, hn, c, hc⟩ := hspan e he
    obtain ⟨h1, h2⟩ := finrank_le_of_span p Φ ρ hL hρc hρ _ _ c hc
    exact ⟨h1, h2.trans hn⟩
  · obtain ⟨j, hj⟩ := hu
    exact hj ((hρ j _ u).symm.trans ((congrArg (ρ j) h).trans (map_zero _)))
  · have hi : genericPoint X ∈ Out.nonzeroLocus (s i) := by
      by_contra hi
      have h1 := h 1 (MvPolynomial.X i) (MvPolynomial.isHomogeneous_X K i)
        ((MvPolynomial.aeval_X _ _).trans (eq_zero_of_not_mem Φ ρ hL hρ (s i) hi))
      rw [MvPolynomial.aeval_X, hv] at h1
      exact one_ne_zero h1
    obtain ⟨χ, hχ⟩ := exists_algHom_of_relations (r i) i (hch i hi).1 (hgen' i) v hv
      fun n G hG h0 => h n G hG (((hch i hi).2.1 n G hG).2 h0)
    obtain ⟨z, hz, hzi, hzv⟩ := exists_point p (haff i) χ.toRingHom fun t => χ.commutes t
    obtain ⟨w, rfl⟩ := hsurj z hz
    refine ⟨w, (hxz w i).2 hzi, fun j => ?_⟩
    rw [hxr w i hzi j, hzv]
    exact congrArg (· * _) (hχ j)
  · simp only [hzero]
    refine ⟨fun h j => ?_, fun h => hsep _ _ (ev (ν z) (x i₀) * (ev b (x i₀))⁻¹) fun j => ?_⟩
    · rw [show ν z = b from h, inv_mul_cancel_right₀ hi₀]
    · rw [h j]
      ring

def secOne {X : Scheme.{0}} {M : LB X} (s : M.Sec) : (lbPow M 1).Sec :=
  powSecMk 1 s.f fun i j => by
    rw [pow_one]
    exact s.compat i j

/- English proof (translation)
The claim follows from `nonzeroLocus_powSecMk 1 s.f _`.
-/
theorem nonzeroLocus_secOne {X : Scheme.{0}} {M : LB X} (s : M.Sec) :
    Out.nonzeroLocus (secOne s) = Out.nonzeroLocus s :=
  nonzeroLocus_powSecMk 1 s.f _

/- English proof (translation)
The claim follows from `fn_ext fun y hy => by have hy' : y ∈ V ⊓ M.U (k PUnit.unit) := ⟨hy.1, mem_powChart.1 hy.2⟩ have e := congrArg (gs (𝟙 X) y _) (h (k PUnit.unit)) rw [gs_res _ y _ hy', gs_mul _ y _ hy', gs_res _ y _ hy', gs_res _ y _ hy'] at e rw [gs_res _ y _ hy, gs_mul _ y _ hy, gs_res _ y _ hy, …`.
-/
theorem secOne_ratio {X : Scheme.{0}} {M : LB X} (s t : M.Sec) (V : X.Opens) (r : Γ(X, V))
    (h : ∀ k, resG X (inf_le_right : V ⊓ M.U k ≤ M.U k) (s.f k) =
      resG X inf_le_left r * resG X inf_le_right (t.f k)) (k : PUnit → M.ι) :
    resG X (inf_le_right : V ⊓ (lbPow M 1).U k ≤ _) ((secOne s).f k) =
      resG X inf_le_left r * resG X inf_le_right ((secOne t).f k) :=
  fn_ext fun y hy => by
    have hy' : y ∈ V ⊓ M.U (k PUnit.unit) := ⟨hy.1, mem_powChart.1 hy.2⟩
    have e := congrArg (gs (𝟙 X) y _) (h (k PUnit.unit))
    rw [gs_res _ y _ hy', gs_mul _ y _ hy', gs_res _ y _ hy', gs_res _ y _ hy'] at e
    rw [gs_res _ y _ hy, gs_mul _ y _ hy, gs_res _ y _ hy, gs_res _ y _ hy]
    exact (gs_res (𝟙 X) y _ hy.2 _).trans (e.trans (congrArg (_ * ·) (gs_res (𝟙 X) y _ hy.2 _).symm))

end GlobalTheory.TorsionZero

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZV

namespace GlobalTheory

open TorsionZero in

/- English proof (translation)
Introduce `hL _ K _ _ P M σ _ th C d k hM hsym hva hgrow hg hk u hu`. Use `polAV_isIntegral_of_isAlgClosed K P` as an intermediate fact. Take `⟨R, _, _, _, 𝒜, _, Φ, -, -, -, hρ⟩` from `SectionRing.exists_sectionRing K P.A.left P.A.hom M hM`. Use `choose ρ hρc hρ using hρ`. Take `⟨hcov, hs⟩` from `hva`.

Use `choose haff r hr hgen using hs`. Take `⟨m, ⟨E⟩⟩` from `Finite.exists_equiv_fin σ`. Establish `hk1 : 1 ≤ k` using `Nat.pos_of_ne_zero fun h => hk (by rw [h, Nat.cast_zero])`. Establish `hcard` using `(hL.mulN (Sp K) P k hk1).2.2.2.2 K (𝟙 _) hk`. Establish `e : ∀ z : Out.baseOver (Sp K) ⟶ P.A, z ^ k = z ≫ Out.mulA P.A k` using `fun z => (congrArg (· ^ k) (Category.comp_id z).symm).trans (MonObj.comp_pow (𝟙 P.A) k z).symm`.

Establish `key` using `card_fibre_zeros_le_of_growth P.A.hom hM Φ ρ hρc hρ (N := 1) (B := C) (d := d) (a := k ^ 2) hg le_rfl (fun i => secOne (th (E.symm i))) (fun i => Out.nonzeroLocus (th (E.symm i))) (funext fun i => nonzeroLocus_secOne _) ((E.symm.iSup_comp (g := fun i => Out.nonzeroLocus (th i))). …`. Rewrite `key` using `[← pow_mul, show 2 * (P.g - 1) = 2 * P.g - 2 by omega]`. Then use the resulting hypothesis. Take `⟨F, hF⟩` from `hgen (E.symm i) f`. Use `⟨MvPolynomial.rename E F, hF.trans ?_⟩` and prove the remaining obligations. Rewrite using `[MvPolynomial.eval₂_rename]`.

Use `congr 1`. Use function extensionality and compare the values at `j`. Simplify using the standard rewrite rules. Rewrite using `[Nat.one_mul]`. Take `⟨l, hl, c, hc⟩` from `hgrow n hn`.

Conclude with `⟨l, hl, c, fun t => (hc t).exists⟩`. Take `⟨h', hh'⟩` from `exists_sec_nonzeroLocus_eq_of_lbIso (isLB_lbPow hM (k ^ 2)) (pull_isLB hM _) (LBIso.symm (GlobalTheory.T.mulA_pullback_iso_pow_sq_symmetric_abelianVariety K P M k hM hsym)) (secPull (secOfPowOne h) (Out.mulA P.A k).left)`. Use `⟨secCast (Nat.one_mul _).symm h', fun z => ?_⟩` and prove the remaining obligations. Rewrite using `[nonzeroLocus_secCast, hh', nonzeroLocus_secPull, nonzeroLocus_secOfPowOne]`. Use `beta_reduce`.

Rewrite using `[e z]`. Both sides reduce to the same expression.
-/
theorem card_zeros_on_torsion_le_of_symmetric_veryAmple :
    Out.Laws → Out.Laws2 → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (M : LB P.A.left) (σ : Type) [Finite σ] (th : σ → M.Sec) (C d k : ℕ), M.IsLB → SymB M → VAmp P.A.hom M th → (∀ e ≥ 1, ∃ r ≤ (C * e) ^ P.g, SectionsHaveFiniteDimension P.A.hom (lbPow M e) r) → 1 ≤ P.g → (k : K) ≠ 0 → ∀ s : (lbPow M d).Sec, (∃ j, s.f j ≠ 0) → Nat.card {x : Out.baseOver (Sp K) ⟶ P.A // x ^ k = 1 ∧ ¬ ⊤ ≤ x.left ⁻¹ᵁ Out.nonzeroLocus s} ≤ C ^ P.g * P.g.factorial * d * k ^ (2 * P.g - 2) := by
  intro hL _ K _ _ P M σ _ th C d k hM hsym hva hgrow hg hk u hu
  have := polAV_isIntegral_of_isAlgClosed K P
  obtain ⟨R, _, _, _, 𝒜, _, Φ, -, -, -, hρ⟩ := SectionRing.exists_sectionRing K P.A.left P.A.hom M hM
  choose ρ hρc hρ using hρ
  obtain ⟨hcov, hs⟩ := hva
  choose haff r hr hgen using hs
  obtain ⟨m, ⟨E⟩⟩ := Finite.exists_equiv_fin σ
  have hk1 : 1 ≤ k := Nat.pos_of_ne_zero fun h => hk (by rw [h, Nat.cast_zero])
  have hcard := (hL.mulN (Sp K) P k hk1).2.2.2.2 K (𝟙 _) hk
  have e : ∀ z : Out.baseOver (Sp K) ⟶ P.A, z ^ k = z ≫ Out.mulA P.A k := fun z =>
    (congrArg (· ^ k) (Category.comp_id z).symm).trans (MonObj.comp_pow (𝟙 P.A) k z).symm
  have key := card_fibre_zeros_le_of_growth P.A.hom hM Φ ρ hρc hρ (N := 1) (B := C) (d := d) (a := k ^ 2) hg
    le_rfl (fun i => secOne (th (E.symm i))) (fun i => Out.nonzeroLocus (th (E.symm i)))
    (funext fun i => nonzeroLocus_secOne _)
    ((E.symm.iSup_comp (g := fun i => Out.nonzeroLocus (th i))).trans hcov) (fun i => haff _)
    (fun i j => r (E.symm i) (E.symm j)) (fun i j => secOne_ratio _ _ _ _ (hr _ _)) (fun i f => ?_)
    (SmoothDim.ringKrullDim_affineOpen K P.A.left P.A.hom P.g P.smoothDim)
    (fun n hn => ?_) (Pt := Out.baseOver (Sp K) ⟶ P.A) (fun z => z.left) (fun z => Over.w z)
    (fun z w h => Over.OverMorphism.ext h) (fun z hz => ⟨Over.homMk z hz, rfl⟩) (fun z => z ^ k) 1
    (finite_pow_eq (by rw [hcard]; exact pow_ne_zero _ (by omega)) 1) (fun h => ?_)
    (secCast (Nat.one_mul d).symm u) hu
  · rwa [← pow_mul, show 2 * (P.g - 1) = 2 * P.g - 2 by omega] at key
  · obtain ⟨F, hF⟩ := hgen (E.symm i) f
    refine ⟨MvPolynomial.rename E F, hF.trans ?_⟩
    rw [MvPolynomial.eval₂_rename]
    congr 1
    funext j
    simp
  · rw [Nat.one_mul]
    obtain ⟨l, hl, c, hc⟩ := hgrow n hn
    exact ⟨l, hl, c, fun t => (hc t).exists⟩
  · obtain ⟨h', hh'⟩ := exists_sec_nonzeroLocus_eq_of_lbIso (isLB_lbPow hM (k ^ 2)) (pull_isLB hM _)
      (LBIso.symm (GlobalTheory.T.mulA_pullback_iso_pow_sq_symmetric_abelianVariety K P M k hM hsym)) (secPull (secOfPowOne h) (Out.mulA P.A k).left)
    refine ⟨secCast (Nat.one_mul _).symm h', fun z => ?_⟩
    rw [nonzeroLocus_secCast, hh', nonzeroLocus_secPull, nonzeroLocus_secOfPowOne]
    beta_reduce
    rw [e z]
    rfl

end GlobalTheory
