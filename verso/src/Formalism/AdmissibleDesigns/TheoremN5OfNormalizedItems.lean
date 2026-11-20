import Formalism.AdmissibleDesigns.GlobalIndexTheoremPlacesOfRNAdm

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Formalism.MainNotions.N Topology

namespace Formalism.MainNotions.N.K.Norm

section Adic

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O]
  [IsTopologicalRing O]

/- English proof (translation)
Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible O`. Take `⟨k, u, rfl⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hc hϖ`. Use `⟨k, fun n y hy => ?_⟩` and prove the remaining obligations. Establish `hm` using `(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ`. Rewrite `hy`, the goal using `[hm, Ideal.span_singleton_pow]`.

Rewrite `hy` using `[mul_assoc, Ideal.unit_mul_mem_iff_mem _ u.isUnit, Ideal.mem_span_singleton, pow_add, mul_comm (ϖ ^ n)]`. Rewrite using `[Ideal.mem_span_singleton]`. Conclude with `(mul_dvd_mul_iff_left (pow_ne_zero k hϖ.ne_zero)).1 hy`.
-/
theorem mem_pow_of_mul {c : O} (hc : c ≠ 0) : ∃ k : ℕ, ∀ (n : ℕ) (y : O),
    c * y ∈ (IsLocalRing.maximalIdeal O) ^ (n + k) → y ∈ (IsLocalRing.maximalIdeal O) ^ n := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨k, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hc hϖ
  refine ⟨k, fun n y hy => ?_⟩
  have hm := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ
  rw [hm, Ideal.span_singleton_pow] at hy ⊢
  rw [mul_assoc, Ideal.unit_mul_mem_iff_mem _ u.isUnit, Ideal.mem_span_singleton, pow_add, mul_comm (ϖ ^ n)] at hy
  rw [Ideal.mem_span_singleton]
  exact (mul_dvd_mul_iff_left (pow_ne_zero k hϖ.ne_zero)).1 hy

/- English proof (translation)
Take `⟨k, hk⟩` from `mem_pow_of_mul hc`. Take `⟨hopen, hbasis⟩` from `isAdic_iff.1 hadic`. Rewrite using `[continuous_iff_continuousAt]`. Introduce `x0`. Rewrite using `[ContinuousAt, Filter.tendsto_def]`.

Introduce `s hs`. Establish `hs0 : (fun y => f x0 + y) ⁻¹' s ∈ 𝓝 (0 : O)`. Establish `hcont : Continuous fun y : O => f x0 + y` using `continuous_const.add continuous_id`. Use `hcont.continuousAt (x := 0)` as an intermediate fact. Rewrite `this` using `[ContinuousAt, add_zero]`.

Conclude with `this hs`. Take `⟨n, hn⟩` from `hbasis _ hs0`. Set `V : Set X` to `(fun x => c * f x - c * f x0) ⁻¹' (((IsLocalRing.maximalIdeal O) ^ (n + k) : Ideal O) : Set O)`. Establish `hV : V ∈ 𝓝 x0`. Use `(hopen (n + k)).preimage (hf.sub continuous_const) |>.mem_nhds ?_` and prove the remaining obligations.

Use `show c * f x0 - c * f x0 ∈ (IsLocalRing.maximalIdeal O) ^ (n + k)`. Rewrite using `[sub_self]`. Conclude with `Ideal.zero_mem _`. Use `Filter.mem_of_superset hV (fun x hx => ?_)` and prove the remaining obligations. Establish `h1 : c * (f x - f x0) ∈ (IsLocalRing.maximalIdeal O) ^ (n + k)`.

Rewrite using `[mul_sub]`. Conclude with `hx`. Establish `h2` using `hn (hk n _ h1)`. Simplify using `using h2`.
-/
theorem continuous_of_mul {X : Type} [TopologicalSpace X] (hadic : IsAdic (IsLocalRing.maximalIdeal O))
    {c : O} (hc : c ≠ 0) {f : X → O} (hf : Continuous fun x => c * f x) : Continuous f := by
  obtain ⟨k, hk⟩ := mem_pow_of_mul hc
  obtain ⟨hopen, hbasis⟩ := isAdic_iff.1 hadic
  rw [continuous_iff_continuousAt]
  intro x0
  rw [ContinuousAt, Filter.tendsto_def]
  intro s hs
  have hs0 : (fun y => f x0 + y) ⁻¹' s ∈ 𝓝 (0 : O) := by
    have hcont : Continuous fun y : O => f x0 + y := continuous_const.add continuous_id
    have := hcont.continuousAt (x := 0)
    rw [ContinuousAt, add_zero] at this
    exact this hs
  obtain ⟨n, hn⟩ := hbasis _ hs0
  let V : Set X := (fun x => c * f x - c * f x0) ⁻¹' (((IsLocalRing.maximalIdeal O) ^ (n + k) : Ideal O) : Set O)
  have hV : V ∈ 𝓝 x0 := by
    refine (hopen (n + k)).preimage (hf.sub continuous_const) |>.mem_nhds ?_
    show c * f x0 - c * f x0 ∈ (IsLocalRing.maximalIdeal O) ^ (n + k)
    rw [sub_self]
    exact Ideal.zero_mem _
  refine Filter.mem_of_superset hV (fun x hx => ?_)
  have h1 : c * (f x - f x0) ∈ (IsLocalRing.maximalIdeal O) ^ (n + k) := by
    rw [mul_sub]
    exact hx
  have h2 := hn (hk n _ h1)
  simpa using h2

end Adic

section Rec

variable {D : D7} (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)

/- English proof (translation)
Use extensionality with `a b`. Simplify using `[Matrix.smul_apply]`.
-/
theorem map_smul_toK' (c : D.nd.O i) (A : MatN D.nd i) :
    (c • A).map (toK D.nd i) = toK D.nd i c • A.map (toK D.nd i) := by
  ext a b
  simp [Matrix.smul_apply]

/- English proof (translation)
Take `⟨b, hb⟩` from `IsLocalization.exist_integer_multiples (nonZeroDivisors (D.nd.O i)) Finset.univ (fun ab : Fin D.R.nV × Fin D.R.nV => M ab.1 ab.2)`. Use `choose M0 hM0 using fun ab : Fin D.R.nV × Fin D.R.nV => hb ab (Finset.mem_univ _)`. Use `⟨b, fun a c => M0 (a, c), nonZeroDivisors.coe_ne_zero b, ?_⟩` and prove the remaining obligations. Use extensionality with `a c`. Simplify using `only [Matrix.smul_apply]`.

Conclude with `hM0 (a, c)`.
-/
theorem exists_integral_mul (M : Matrix (Fin D.R.nV) (Fin D.R.nV) (KK D.nd i)) :
    ∃ (b : D.nd.O i) (M0 : MatN D.nd i), b ≠ 0 ∧ M0.map (toK D.nd i) = b • M := by
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (D.nd.O i)) Finset.univ
    (fun ab : Fin D.R.nV × Fin D.R.nV => M ab.1 ab.2)
  choose M0 hM0 using fun ab : Fin D.R.nV × Fin D.R.nV => hb ab (Finset.mem_univ _)
  refine ⟨b, fun a c => M0 (a, c), nonZeroDivisors.coe_ne_zero b, ?_⟩
  ext a c
  simp only [Matrix.smul_apply]
  exact hM0 (a, c)

/- English proof (translation)
Take `⟨P, Q, hPQ, hQP, hconj⟩` from `conjK_self i r ρ π hd`. Establish `hA : ∀ g, (rO D.nd i (rN i r ρ π) π g).map (toK D.nd i) = P * (rO D.nd i r π g).map (toK D.nd i) * Q`. Introduce `g`. Establish `h` using `hconj g`. Use `beta_reduce at h`.

Rewrite using `[h, Matrix.mul_assoc, hPQ, Matrix.mul_one]`. Take `⟨b1, P0, hb1, hP0⟩` from `exists_integral_mul i P`. Take `⟨b2, Q0, hb2, hQ0⟩` from `exists_integral_mul i Q`. Establish `hid : ∀ g, (b1 * b2) • rO D.nd i (rN i r ρ π) π g = P0 * rO D.nd i r π g * Q0`. Introduce `g`.

Apply `Matrix.map_injective (toK_inj i)` to reduce the goal to its premises. Use `show ((b1 * b2) • rO D.nd i (rN i r ρ π) π g).map (toK D.nd i) = (P0 * rO D.nd i r π g * Q0).map (toK D.nd i)`. Rewrite using `[Matrix.map_mul, Matrix.map_mul, hP0, hQ0, map_smul_toK', hA, map_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, smul_smul, mul_comm (toK D.nd i b1), ← map_mul]`. Conclude with `algebraMap_smul (KK D.nd i) (b2 * b1) _`. Establish `hcont : Continuous fun g => (b1 * b2) • rO D.nd i (rN i r ρ π) π g`.

Simplify using `only [hid]`. Conclude with `(continuous_const.matrix_mul (hc π)).matrix_mul continuous_const`. Establish `hne : b1 * b2 ≠ 0` using `mul_ne_zero hb1 hb2`. Unfold `RhoCont`. Use `continuous_pi fun a => continuous_pi fun b => ?_` and prove the remaining obligations.

Use `continuous_of_mul (D.nd.O_adic i) hne ?_` and prove the remaining obligations. Establish `h2 : Continuous fun g => ((b1 * b2) • rO D.nd i (rN i r ρ π) π g) (Fin.castAdd D.R.t a) (Fin.castAdd D.R.t b)` using `(continuous_apply_apply _ _).comp hcont`. Use `h2.congr (fun g => ?_)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(b1 * b2) * rO D.nd i (rN i r ρ π) π g (Fin.castAdd D.R.t a) (Fin.castAdd D.R.t b) = _`. Rewrite using `[(normAt_rN i r ρ π).2.2 g a b]`.
-/
theorem rhoCont_of (hd : TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π) (hc : TruncatedSeriesCountingIdentities.FamilyContinuous i r) : RhoCont i ρ π := by
  obtain ⟨P, Q, hPQ, hQP, hconj⟩ := conjK_self i r ρ π hd
  have hA : ∀ g, (rO D.nd i (rN i r ρ π) π g).map (toK D.nd i) = P * (rO D.nd i r π g).map (toK D.nd i) * Q := by
    intro g
    have h := hconj g
    beta_reduce at h
    rw [h, Matrix.mul_assoc, hPQ, Matrix.mul_one]
  obtain ⟨b1, P0, hb1, hP0⟩ := exists_integral_mul i P
  obtain ⟨b2, Q0, hb2, hQ0⟩ := exists_integral_mul i Q
  have hid : ∀ g, (b1 * b2) • rO D.nd i (rN i r ρ π) π g = P0 * rO D.nd i r π g * Q0 := by
    intro g
    apply Matrix.map_injective (toK_inj i)
    show ((b1 * b2) • rO D.nd i (rN i r ρ π) π g).map (toK D.nd i) = (P0 * rO D.nd i r π g * Q0).map (toK D.nd i)
    rw [Matrix.map_mul, Matrix.map_mul, hP0, hQ0, map_smul_toK', hA, map_mul, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.smul_mul, smul_smul, mul_comm (toK D.nd i b1), ← map_mul]
    exact algebraMap_smul (KK D.nd i) (b2 * b1) _
  have hcont : Continuous fun g => (b1 * b2) • rO D.nd i (rN i r ρ π) π g := by
    simp only [hid]
    exact (continuous_const.matrix_mul (hc π)).matrix_mul continuous_const
  have hne : b1 * b2 ≠ 0 := mul_ne_zero hb1 hb2
  unfold RhoCont
  refine continuous_pi fun a => continuous_pi fun b => ?_
  refine continuous_of_mul (D.nd.O_adic i) hne ?_
  have h2 : Continuous fun g => ((b1 * b2) • rO D.nd i (rN i r ρ π) π g) (Fin.castAdd D.R.t a) (Fin.castAdd D.R.t b) :=
    (continuous_apply_apply _ _).comp hcont
  refine h2.congr (fun g => ?_)
  change (b1 * b2) * rO D.nd i (rN i r ρ π) π g (Fin.castAdd D.R.t a) (Fin.castAdd D.R.t b) = _
  rw [(normAt_rN i r ρ π).2.2 g a b]

/- English proof (translation)
The claim follows from `admitted_items_normalized i r ρ π (rhoCont_of i r ρ π hA.2.2.2.2.2.2.2.2.2.2.2.1 hA.2.2.2.2.2.2.2.2.2.1) hA`.
-/
theorem admitted_items_normalized_self (hA : AdmR i r ρ π) : AdmR i (rN i r ρ π) ρ π :=
  admitted_items_normalized i r ρ π (rhoCont_of i r ρ π hA.2.2.2.2.2.2.2.2.2.2.2.1 hA.2.2.2.2.2.2.2.2.2.1) hA

/- English proof (translation)
The claim follows from `globalIndexTheoremPlaces_of_rN i r ρ π dc lenRow e' cB (rhoCont_of i r ρ π hA.2.2.2.2.2.2.2.2.2.2.2.1 hA.2.2.2.2.2.2.2.2.2.1) H hA`.
-/
theorem theorem_n5_of_normalized_items (dc : TruncatedSeriesCountingIdentities.Decl D i) (lenRow : HeightOneSpectrum (𝓞 D.host.E) → ℚ)
    (e' : HeightOneSpectrum (𝓞 D.host.E) → ℕ) (cB : ℕ)
    (H : AdmR i (rN i r ρ π) ρ π → LargeLevelLemmas.GlobalIndexTheoremPlaces i (rN i r ρ π) ρ π dc lenRow e' cB)
    (hA : AdmR i r ρ π) : LargeLevelLemmas.GlobalIndexTheoremPlaces i r ρ π dc lenRow e' cB :=
  globalIndexTheoremPlaces_of_rN i r ρ π dc lenRow e' cB (rhoCont_of i r ρ π hA.2.2.2.2.2.2.2.2.2.2.2.1 hA.2.2.2.2.2.2.2.2.2.1) H hA

/- English proof (translation)
The claim follows from `theorem_n5_of_normalized_items i r ρ π dc lenRow e' cB H (admitted_items_of_adm i r ρ π hA)`.
-/
theorem theorem_n5_normalized_of_adm (dc : TruncatedSeriesCountingIdentities.Decl D i) (lenRow : HeightOneSpectrum (𝓞 D.host.E) → ℚ)
    (e' : HeightOneSpectrum (𝓞 D.host.E) → ℕ) (cB : ℕ)
    (H : AdmR i (rN i r ρ π) ρ π → LargeLevelLemmas.GlobalIndexTheoremPlaces i (rN i r ρ π) ρ π dc lenRow e' cB)
    (hA : LargeLevelLemmas.admitted i r ρ π) : LargeLevelLemmas.GlobalIndexTheoremPlaces i r ρ π dc lenRow e' cB :=
  theorem_n5_of_normalized_items i r ρ π dc lenRow e' cB H (admitted_items_of_adm i r ρ π hA)

end Rec

end Formalism.MainNotions.N.K.Norm
