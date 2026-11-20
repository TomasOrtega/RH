import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.EpresDefs
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MemSpanVariable

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

section
open MvPowerSeries
/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.MemSpanVariable.mem_span_X f hf`.
-/
private theorem mem_span_X {O σ : Type} [CommRing O] [Fintype σ] (f : MvPowerSeries σ O)
    (hf : constantCoeff f = 0) : f ∈ Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ O)) :=
  _root_.UpperTheory.Reformulated.B.MemSpanVariable.mem_span_X f hf
end

/- English proof (translation)
Establish `hm : ∀ f g, D (f * g) = res O R f • D g + res O R g • D f` using `hD`. Establish `h1 : D 1 = 0`. Use `hm 1 1` as an intermediate fact. Simplify using `only [mul_one, map_one, one_smul] at this`. Conclude with `left_eq_add.1 this`.

Establish `hs : ∀ g ∈ Ideal.span (Set.range (MvPowerSeries.X : _ → MvPowerSeries (Fin P.a ⊕ Fin P.g) O)), res O R (P.p g) = 0 ∧ D (P.p g) = 0` using `fun g hg => by`. Use `Submodule.span_induction (p := fun g _ => res O R (P.p g) = 0 ∧ D (P.p g) = 0) ?_ (by simp) ?_ ?_ hg` and prove the remaining obligations. Introduce and unpack `_ ⟨s, rfl⟩`. Conclude with `⟨(res_eq_zero_iff O R _).2 (P.var s), h s⟩`. Introduce and unpack `x y - - ⟨a, b⟩ ⟨c, d⟩`.

Simplify using `[a, b, c, d]`. Introduce and unpack `x y - ⟨a, b⟩`. Rewrite using `[smul_eq_mul, map_mul, map_mul, hm, a, b]`. Simplify using the standard rewrite rules. Use extensionality with `x`.

Take `⟨f, rfl⟩` from `P.surj x`. Establish `e : f = (f - algebraMap O _ (MvPowerSeries.constantCoeff f)) + (MvPowerSeries.constantCoeff f) • 1`. Rewrite using `[Algebra.algebraMap_eq_smul_one, sub_add_cancel]`. Establish `h2` using `(hs _ (mem_span_X (f - algebraMap O _ (MvPowerSeries.constantCoeff f)) (by simp [MvPowerSeries.algebraMap_apply]))).2`. Rewrite using `[e, map_add, map_add, h2, map_smul, map_smul, map_one, h1]`.

Simplify using the standard rewrite rules.
-/
private theorem der_zero {O : Type} [CommRing O] [IsLocalRing O] {R : Type} [CommRing R] [Algebra O R] [IsCO O R]
    {σ : R →ₐ[O] R} (P : GPres O σ) (D : R →ₗ[O] ResidueField O) (hD : D ∈ PtDer (res O R) (ResidueField O))
    (h : ∀ s, D (P.p (MvPowerSeries.X s)) = 0) : D = 0 := by
  have hm : ∀ f g, D (f * g) = res O R f • D g + res O R g • D f := hD
  have h1 : D 1 = 0 := by
    have := hm 1 1
    simp only [mul_one, map_one, one_smul] at this
    exact left_eq_add.1 this
  have hs : ∀ g ∈ Ideal.span (Set.range (MvPowerSeries.X : _ → MvPowerSeries (Fin P.a ⊕ Fin P.g) O)),
      res O R (P.p g) = 0 ∧ D (P.p g) = 0 := fun g hg => by
    refine Submodule.span_induction (p := fun g _ => res O R (P.p g) = 0 ∧ D (P.p g) = 0) ?_ (by simp) ?_ ?_ hg
    · rintro _ ⟨s, rfl⟩
      exact ⟨(res_eq_zero_iff O R _).2 (P.var s), h s⟩
    · rintro x y - - ⟨a, b⟩ ⟨c, d⟩
      simp [a, b, c, d]
    · rintro x y - ⟨a, b⟩
      rw [smul_eq_mul, map_mul, map_mul, hm, a, b]
      simp
  ext x
  obtain ⟨f, rfl⟩ := P.surj x
  have e : f = (f - algebraMap O _ (MvPowerSeries.constantCoeff f)) + (MvPowerSeries.constantCoeff f) • 1 := by
    rw [Algebra.algebraMap_eq_smul_one, sub_add_cancel]
  have h2 := (hs _ (mem_span_X (f - algebraMap O _ (MvPowerSeries.constantCoeff f))
    (by simp [MvPowerSeries.algebraMap_apply]))).2
  rw [e, map_add, map_add, h2, map_smul, map_smul, map_one, h1]
  simp

/- English proof (translation)
Establish `h1 : P.p (MvPowerSeries.X s) ∈ evp σ (Space.Loc.par P.a P.g s)`. Rewrite using `[← P.part]`. Conclude with `⟨_, X_mem_wtPart O _ s, rfl⟩`. Establish `h3 : σ (P.p (MvPowerSeries.X s)) = sg R (Space.Loc.par P.a P.g s) * P.p (MvPowerSeries.X s)` using `h1`. Establish `h4 : D (σ (P.p (MvPowerSeries.X s))) = sg (ResidueField O) j * D (P.p (MvPowerSeries.X s))` using `hD.2 _`.

Establish `h5 : (2 : ResidueField O) ≠ 0`. Use `(h2.map (residue O)).ne_zero` as an intermediate fact. Rewrite `this` using `[map_ofNat]`. Then use the resulting hypothesis. Rewrite `h4` using `[h3]`. Generalize the expression as in `Space.Loc.par P.a P.g s = i at hs h4`.

Generalize the expression as in `P.p (MvPowerSeries.X s) = y at h4`. Establish `v1 : (1 : ZMod 2).val = 1` using `rfl`. Establish `hc : ∀ i : ZMod 2, i = 0 ∨ i = 1` using `by decide`. Apply `(mul_eq_zero.1 (show 2 * D y = 0 from ?_)).resolve_left h5` to reduce the goal to its premises. Apply the tactic sequence `rcases hc i with rfl | rfl <;> rcases hc j with rfl | rfl`.

Conclude with `absurd rfl hs`. Simplify using `only [sg, ZMod.val_zero, v1, pow_zero, pow_one, one_mul, neg_mul] at h4`. Take the linear combination `h4`. Simplify using `only [sg, ZMod.val_zero, v1, pow_zero, pow_one, one_mul, neg_mul, map_neg] at h4`. Take the linear combination `-h4`.

Conclude with `absurd rfl hs`.
-/
private theorem der_off {O : Type} [CommRing O] [IsLocalRing O] (h2 : IsUnit (2 : O)) {R : Type} [CommRing R]
    [Algebra O R] [IsCO O R] {σ : R →ₐ[O] R} (P : GPres O σ) (j : ZMod 2) (D : R →ₗ[O] ResidueField O)
    (hD : D ∈ derp O σ j) (s : Fin P.a ⊕ Fin P.g) (hs : Space.Loc.par P.a P.g s ≠ j) :
    D (P.p (MvPowerSeries.X s)) = 0 := by
  have h1 : P.p (MvPowerSeries.X s) ∈ evp σ (Space.Loc.par P.a P.g s) := by
    rw [← P.part]
    exact ⟨_, X_mem_wtPart O _ s, rfl⟩
  have h3 : σ (P.p (MvPowerSeries.X s)) = sg R (Space.Loc.par P.a P.g s) * P.p (MvPowerSeries.X s) := h1
  have h4 : D (σ (P.p (MvPowerSeries.X s))) = sg (ResidueField O) j * D (P.p (MvPowerSeries.X s)) := hD.2 _
  have h5 : (2 : ResidueField O) ≠ 0 := by
    have := (h2.map (residue O)).ne_zero
    rwa [map_ofNat] at this
  rw [h3] at h4
  generalize Space.Loc.par P.a P.g s = i at hs h4
  generalize P.p (MvPowerSeries.X s) = y at h4
  have v1 : (1 : ZMod 2).val = 1 := rfl
  have hc : ∀ i : ZMod 2, i = 0 ∨ i = 1 := by decide
  apply (mul_eq_zero.1 (show 2 * D y = 0 from ?_)).resolve_left h5
  rcases hc i with rfl | rfl <;> rcases hc j with rfl | rfl
  · exact absurd rfl hs
  · simp only [sg, ZMod.val_zero, v1, pow_zero, pow_one, one_mul, neg_mul] at h4
    linear_combination h4
  · simp only [sg, ZMod.val_zero, v1, pow_zero, pow_one, one_mul, neg_mul, map_neg] at h4
    linear_combination -h4
  · exact absurd rfl hs

/- English proof (translation)
Set `φ : N →ₗ[ResidueField O] (ι → ResidueField O)` to `{ toFun := fun D i => D.1 (y i) map_add' := fun _ _ => rfl map_smul' := fun _ _ => rfl }`. Establish `hφ : Function.Injective φ` using `(injective_iff_map_eq_zero φ).2 fun D hD => Subtype.ext (h D.1 D.2 fun i => congrFun hD i)`. Conclude with `⟨Module.Finite.of_injective φ hφ, by`. Simplify using `using LinearMap.finrank_le_finrank_of_injective hφ⟩`.
-/
private theorem der_bound {O : Type} [CommRing O] [IsLocalRing O] {R : Type} [CommRing R]
    [Algebra O R] (N : Submodule (ResidueField O) (R →ₗ[O] ResidueField O)) {ι : Type} [Fintype ι] (y : ι → R)
    (h : ∀ D ∈ N, (∀ i, D (y i) = 0) → D = 0) :
    Module.Finite (ResidueField O) N ∧ Module.finrank (ResidueField O) N ≤ Fintype.card ι := by
  let φ : N →ₗ[ResidueField O] (ι → ResidueField O) :=
    { toFun := fun D i => D.1 (y i)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hφ : Function.Injective φ := (injective_iff_map_eq_zero φ).2 fun D hD =>
    Subtype.ext (h D.1 D.2 fun i => congrFun hD i)
  exact ⟨Module.Finite.of_injective φ hφ, by
    simpa using LinearMap.finrank_le_finrank_of_injective hφ⟩

/- English proof (translation)
Introduce `O _ _ _ _ h2 R _ _ _ σ P`. Use `⟨fun j => (der_bound (derp O σ j) (fun s => P.p (MvPowerSeries.X s)) fun D hD h => der_zero P D hD.1 h).1, ?_, ?_⟩` and prove the remaining obligations. Use `(der_bound (derp O σ 0) (fun i : Fin P.a => P.p (MvPowerSeries.X (.inl i))) fun D hD h => der_zero P D hD.1 fun s => by` as an intermediate fact. Break down `s with i | i` into its components or cases. Conclude with `h i`.

Conclude with `der_off h2 P 0 D hD _ (show (1 : ZMod 2) ≠ 0 by decide)).2`. Simplify using `using this`. Use `(der_bound (derp O σ 1) (fun i : Fin P.g => P.p (MvPowerSeries.X (.inr i))) fun D hD h => der_zero P D hD.1 fun s => by` as an intermediate fact. Break down `s with i | i` into its components or cases. Conclude with `der_off h2 P 1 D hD _ (show (0 : ZMod 2) ≠ 1 by decide)`.

Conclude with `h i).2`. Simplify using `using this`.
-/
theorem UpperTheory.V.Fr.ep_der :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O], IsUnit (2 : O) → ∀ (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (σ : R →ₐ[O] R) (P : GPres O σ), (∀ j, Module.Finite (ResidueField O) (derp O σ j)) ∧ Module.finrank (ResidueField O) (derp O σ 0) ≤ P.a ∧ Module.finrank (ResidueField O) (derp O σ 1) ≤ P.g := by
  intro O _ _ _ _ h2 R _ _ _ σ P
  refine ⟨fun j => (der_bound (derp O σ j) (fun s => P.p (MvPowerSeries.X s))
    fun D hD h => der_zero P D hD.1 h).1, ?_, ?_⟩
  · have := (der_bound (derp O σ 0) (fun i : Fin P.a => P.p (MvPowerSeries.X (.inl i)))
      fun D hD h => der_zero P D hD.1 fun s => by
        rcases s with i | i
        · exact h i
        · exact der_off h2 P 0 D hD _ (show (1 : ZMod 2) ≠ 0 by decide)).2
    simpa using this
  · have := (der_bound (derp O σ 1) (fun i : Fin P.g => P.p (MvPowerSeries.X (.inr i)))
      fun D hD h => der_zero P D hD.1 fun s => by
        rcases s with i | i
        · exact der_off h2 P 1 D hD _ (show (0 : ZMod 2) ≠ 1 by decide)
        · exact h i).2
    simpa using this
