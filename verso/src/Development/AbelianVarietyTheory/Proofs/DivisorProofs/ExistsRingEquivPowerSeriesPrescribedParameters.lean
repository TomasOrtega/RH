import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCoefficientFieldOfCharZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SurjectiveOfResidueOfCotangent
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CohenChart

open IsLocalRing MvPowerSeries

/- English proof (translation)
Establish `h : (⟨∑ i, a i * y i, sum_mem fun i _ => Ideal.mul_mem_left _ _ (hy i)⟩ : maximalIdeal R) = ∑ i, a i • (⟨y i, hy i⟩ : maximalIdeal R)` using `by ext; simp [smul_eq_mul]`. Rewrite using `[h, map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, ← IsLocalRing.ResidueField.algebraMap_eq, algebraMap_smul]`.
-/
theorem sum_residue_smul_toCotangent {R : Type} [CommRing R] [IsLocalRing R] {Idx : Type} [Fintype Idx]
    (a : Idx → R) (y : Idx → R) (hy : ∀ i, y i ∈ maximalIdeal R) :
    ∑ i, residue R (a i) • (maximalIdeal R).toCotangent ⟨y i, hy i⟩ =
      (maximalIdeal R).toCotangent ⟨∑ i, a i * y i, sum_mem fun i _ => Ideal.mul_mem_left _ _ (hy i)⟩ := by
  have h : (⟨∑ i, a i * y i, sum_mem fun i _ => Ideal.mul_mem_left _ _ (hy i)⟩ : maximalIdeal R) =
      ∑ i, a i • (⟨y i, hy i⟩ : maximalIdeal R) := by
    ext; simp [smul_eq_mul]
  rw [h, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, ← IsLocalRing.ResidueField.algebraMap_eq, algebraMap_smul]

end GlobalTheory.CohenChart

namespace GlobalTheory.CohenChart

open IsLocalRing MvPowerSeries

/- English proof (translation)
Introduce `R _ _ hc hQ m t ht hind`. Take `⟨q⟩` from `hQ`. Use `letI : Algebra ℚ (ResidueField R) := ((IsLocalRing.residue R).comp q).toAlgebra`. Use `haveI : CharZero (ResidueField R) := algebraRat.charZero _`. Use `haveI := hc`.

Take `⟨Λ, hF, hΛ⟩` from `GlobalTheory.CohenRegular.exists_coefficientField_of_charZero R`. Use `letI := hF.toField`. Set `v : Fin m → CotangentSpace R` to `fun i => (maximalIdeal R).toCotangent ⟨t i, ht i⟩`. Establish `hv : LinearIndependent (ResidueField R) v`. Rewrite using `[Fintype.linearIndependent_iff]`.

Introduce `g hg i`. Use `choose a ha using fun j => residue_surjective (R := R) (g j)`. Establish `h1 : ∑ j, residue R (a j) • v j = 0` using `by simpa [ha] using hg`. Rewrite `h1` using `[sum_residue_smul_toCotangent, Ideal.toCotangent_eq_zero]`. Rewrite using `[← ha i, residue_eq_zero_iff]`.

Conclude with `hind a h1 i`. Use `set d := Module.finrank (ResidueField R) (CotangentSpace R) with hd`. Establish `hmd : m ≤ d` using `by simpa using hv.fintype_card_le_finrank`. Use `set W := Submodule.span (ResidueField R) (Set.range v) with hW`. Establish `hWd : Module.finrank (ResidueField R) (CotangentSpace R ⧸ W) = d - m`.

Establish `h1` using `Submodule.finrank_quotient_add_finrank W`. Establish `h2 : Module.finrank (ResidueField R) W = m` using `by rw [finrank_span_eq_card hv]; simp`. Use linear arithmetic over natural numbers and integers. Set `b` to `Module.finBasisOfFinrankEq (ResidueField R) (CotangentSpace R ⧸ W) hWd`. Use `choose w hw using fun j => W.mkQ_surjective (b j)`.

Use `choose s hs using fun j => (maximalIdeal R).toCotangent_surjective (w j)`. Set `x : Fin m ⊕ Fin (d - m) → R` to `Sum.elim t (fun j => (s j : R))`. Establish `hx : ∀ j, x j ∈ maximalIdeal R`. Introduce and unpack `(j | j)`. Use `exacts [ht j, (s j).2]`.

Set `g : Fin m ⊕ Fin (d - m) → CotangentSpace R` to `fun j => (maximalIdeal R).toCotangent ⟨x j, hx j⟩`. Use `set U := Submodule.span (ResidueField R) (Set.range g) with hU`. Establish `hUtop : ∀ y : CotangentSpace R, y ∈ U`. Introduce `y`. Establish `hWU : W ≤ U` using `Submodule.span_mono (by rintro _ ⟨i, rfl⟩; exact ⟨Sum.inl i, rfl⟩)`.

Establish `hwU : ∀ j, w j ∈ U` using `fun j => Submodule.subset_span ⟨Sum.inr j, by simp [g, x, hs]⟩`. Establish `h1 : W.mkQ (y - ∑ j, b.repr (W.mkQ y) j • w j) = 0`. Simplify using `only [map_sub, map_sum, map_smul, hw, b.sum_repr, sub_self]`. Establish `h2 : y - ∑ j, b.repr (W.mkQ y) j • w j ∈ W`. Rewrite `h1` using `[← LinearMap.mem_ker, Submodule.ker_mkQ]`. Then use the resulting hypothesis.

Establish `h3 : ∑ j, b.repr (W.mkQ y) j • w j ∈ U` using `U.sum_mem fun j _ => U.smul_mem _ (hwU j)`. Use `U.add_mem (hWU h2) h3` as an intermediate fact. Simplify using `using this`. Establish `hb : maximalIdeal Λ = ⊥` using `isField_iff_maximalIdeal_eq.1 hF`. Use `haveI : IsAdicComplete (maximalIdeal Λ) Λ := by rw [hb]; infer_instance`.

Set `f : ChartRing Λ m (d - m) →ₐ[Λ] R` to `GlobalTheory.mvEvalAdic Λ (maximalIdeal R) x hx`. Establish `hfX : ∀ j, f (X j) = x j` using `fun j => GlobalTheory.mvEvalAdic_X (A := Λ) (maximalIdeal R) x hx j`. Establish `hfC : ∀ a : Λ, f (C a) = a` using `fun a => GlobalTheory.mvEvalAdic_C (A := Λ) (maximalIdeal R) x hx a`. Establish `hle : ∀ g ∈ maximalIdeal (ChartRing Λ m (d - m)), f g ∈ maximalIdeal R`. Introduce `g hg`.

Establish `h4` using `GlobalTheory.algHom_sub_constantCoeff_mem f (K := maximalIdeal R) (fun j => by rw [hfX]; exact hx j) g`. Establish `h5` using `GlobalTheory.FormalIsogeny.mem_maximalIdeal_iff_constantCoeff.1 hg`. Rewrite `h5` using `[hb, Ideal.mem_bot]`. Rewrite `h4` using `[h5, map_zero, sub_zero]`. Then use the resulting hypothesis. Establish `hXm : ∀ j, (X j : ChartRing Λ m (d - m)) ∈ maximalIdeal (ChartRing Λ m (d - m))` using `fun j => GlobalTheory.FormalIsogeny.mem_maximalIdeal_iff_constantCoeff.2 (by simp)`.

Establish `hloc : IsLocalHom (f : ChartRing Λ m (d - m) →+* R)` using `⟨fun g hg => by`. Assume the negation of the conclusion as `hn`. Conclude with `(hle g hn) hg⟩`. Establish `hres : ∀ z : R, ∃ r, z - (f : ChartRing Λ m (d - m) →+* R) r ∈ maximalIdeal R`. Introduce `z`.

Take `⟨a, ha, h⟩` from `hΛ z`. Conclude with `⟨C ⟨a, ha⟩, by simpa [hfC] using h⟩`. Establish `hcot : maximalIdeal R ≤ (maximalIdeal (ChartRing Λ m (d - m))).map (f : ChartRing Λ m (d - m) →+* R) ⊔ maximalIdeal R ^ 2`. Introduce `z hz`. Take `⟨c, hc'⟩` from `(Submodule.mem_span_range_iff_exists_fun (ResidueField R)).1 (hUtop ((maximalIdeal R).toCotangent ⟨z, hz⟩))`.

Use `choose a ha using fun j => residue_surjective (R := R) (c j)`. Establish `h1 : ∑ j, residue R (a j) • g j = (maximalIdeal R).toCotangent ⟨z, hz⟩` using `by simpa [ha] using hc'`. Rewrite `h1` using `[sum_residue_smul_toCotangent, Ideal.toCotangent_eq]`. Establish `h2 : ∑ j, a j * x j ∈ (maximalIdeal (ChartRing Λ m (d - m))).map (f : ChartRing Λ m (d - m) →+* R)` using `sum_mem fun j _ => Ideal.mul_mem_left _ _ (by rw [← hfX]; exact Ideal.mem_map_of_mem _ (hXm j))`. Establish `h3 : z = ∑ j, a j * x j + (z - ∑ j, a j * x j)` using `by ring`.

Rewrite using `[h3]`. Use `Submodule.add_mem_sup h2 ?_` and prove the remaining obligations. Establish `: (z - ∑ j, a j * x j) = -((∑ j, a j * x j) - z)` using `by ring`. Rewrite using `[this]`. Conclude with `neg_mem h1`.

Establish `hcA : IsAdicComplete (maximalIdeal (ChartRing Λ m (d - m))) (ChartRing Λ m (d - m))` using `GlobalTheory.CohenStructure.isAdicComplete_of_ringEquiv (MvPowerSeries.renameEquiv Λ finSumFinEquiv.symm).toRingEquiv (h := GlobalTheory.CohenStructure.isAdicComplete_mvPowerSeries Λ (m + (d - m)))`. Establish `hsurj : Function.Surjective (f : ChartRing Λ m (d - m) →+* R)` using `GlobalTheory.LocalSurj.surjective_of_residue_of_cotangent _ R _ hcA hloc hres hcot`. Use `letI : Algebra (ChartRing Λ m (d - m)) R := (f : ChartRing Λ m (d - m) →+* R).toAlgebra`. Use `haveI : Module.Finite (ChartRing Λ m (d - m)) R := Module.Finite.of_surjective (Algebra.linearMap (ChartRing Λ m (d - m)) R) hsurj`. Establish `hdA : ringKrullDim (ChartRing Λ m (d - m)) = ((m + (d - m) : ℕ) : WithBot ℕ∞)`.

Rewrite using `[GlobalTheory.FormalIsogeny.ringKrullDim_mvPowerSeries, ringKrullDim_eq_zero_of_isField hF, Nat.card_sum, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_fin, Fintype.card_fin, zero_add]`. Establish `hdR : ringKrullDim R = ((m + (d - m) : ℕ) : WithBot ℕ∞)`. Rewrite using `[← (IsRegularLocalRing.iff_finrank_cotangentSpace R).mp inferInstance, ← hd]`. Establish `hmd' : m + (d - m) = d` using `by omega`. Rewrite using `[hmd']`.

Establish `hinj : Function.Injective (f : ChartRing Λ m (d - m) →+* R)` using `GlobalTheory.CohenStructure.injective_of_ringKrullDim_eq hdA hdR`. Set `φ` to `RingEquiv.ofBijective (f : ChartRing Λ m (d - m) →+* R) ⟨hinj, hsurj⟩`. Use `⟨Λ, inferInstance, d - m, φ.symm, fun i => ?_⟩` and prove the remaining obligations. Rewrite using `[RingEquiv.symm_apply_eq]`. Use `show t i = f (X (Sum.inl i))`.

Rewrite using `[hfX]`. Both sides reduce to the same expression.
-/
theorem exists_ringEquiv_chartRing : ∀ (R : Type) [CommRing R] [IsRegularLocalRing R],
    IsAdicComplete (maximalIdeal R) R → Nonempty (ℚ →+* R) → ∀ (m : ℕ) (t : Fin m → R),
    (∀ i, t i ∈ maximalIdeal R) →
    (∀ a : Fin m → R, ∑ i, a i * t i ∈ maximalIdeal R ^ 2 → ∀ i, a i ∈ maximalIdeal R) →
    ∃ (k : Type) (_ : Field k) (e : ℕ) (σ : R ≃+* ChartRing k m e), ∀ i, σ (t i) = bdParam k m e i := by
  intro R _ _ hc hQ m t ht hind
  classical
  obtain ⟨q⟩ := hQ
  letI : Algebra ℚ (ResidueField R) := ((IsLocalRing.residue R).comp q).toAlgebra
  haveI : CharZero (ResidueField R) := algebraRat.charZero _
  haveI := hc
  obtain ⟨Λ, hF, hΛ⟩ := GlobalTheory.CohenRegular.exists_coefficientField_of_charZero R
  letI := hF.toField

  let v : Fin m → CotangentSpace R := fun i => (maximalIdeal R).toCotangent ⟨t i, ht i⟩
  have hv : LinearIndependent (ResidueField R) v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    choose a ha using fun j => residue_surjective (R := R) (g j)
    have h1 : ∑ j, residue R (a j) • v j = 0 := by simpa [ha] using hg
    rw [sum_residue_smul_toCotangent, Ideal.toCotangent_eq_zero] at h1
    rw [← ha i, residue_eq_zero_iff]
    exact hind a h1 i
  set d := Module.finrank (ResidueField R) (CotangentSpace R) with hd
  have hmd : m ≤ d := by simpa using hv.fintype_card_le_finrank
  set W := Submodule.span (ResidueField R) (Set.range v) with hW
  have hWd : Module.finrank (ResidueField R) (CotangentSpace R ⧸ W) = d - m := by
    have h1 := Submodule.finrank_quotient_add_finrank W
    have h2 : Module.finrank (ResidueField R) W = m := by rw [finrank_span_eq_card hv]; simp
    omega
  let b := Module.finBasisOfFinrankEq (ResidueField R) (CotangentSpace R ⧸ W) hWd
  choose w hw using fun j => W.mkQ_surjective (b j)
  choose s hs using fun j => (maximalIdeal R).toCotangent_surjective (w j)
  let x : Fin m ⊕ Fin (d - m) → R := Sum.elim t (fun j => (s j : R))
  have hx : ∀ j, x j ∈ maximalIdeal R := by
    rintro (j | j)
    exacts [ht j, (s j).2]
  let g : Fin m ⊕ Fin (d - m) → CotangentSpace R := fun j => (maximalIdeal R).toCotangent ⟨x j, hx j⟩
  set U := Submodule.span (ResidueField R) (Set.range g) with hU
  have hUtop : ∀ y : CotangentSpace R, y ∈ U := by
    intro y
    have hWU : W ≤ U := Submodule.span_mono (by rintro _ ⟨i, rfl⟩; exact ⟨Sum.inl i, rfl⟩)
    have hwU : ∀ j, w j ∈ U := fun j => Submodule.subset_span ⟨Sum.inr j, by simp [g, x, hs]⟩
    have h1 : W.mkQ (y - ∑ j, b.repr (W.mkQ y) j • w j) = 0 := by
      simp only [map_sub, map_sum, map_smul, hw, b.sum_repr, sub_self]
    have h2 : y - ∑ j, b.repr (W.mkQ y) j • w j ∈ W := by
      rwa [← LinearMap.mem_ker, Submodule.ker_mkQ] at h1
    have h3 : ∑ j, b.repr (W.mkQ y) j • w j ∈ U := U.sum_mem fun j _ => U.smul_mem _ (hwU j)
    have := U.add_mem (hWU h2) h3
    simpa using this

  have hb : maximalIdeal Λ = ⊥ := isField_iff_maximalIdeal_eq.1 hF
  haveI : IsAdicComplete (maximalIdeal Λ) Λ := by rw [hb]; infer_instance
  let f : ChartRing Λ m (d - m) →ₐ[Λ] R := GlobalTheory.mvEvalAdic Λ (maximalIdeal R) x hx
  have hfX : ∀ j, f (X j) = x j := fun j => GlobalTheory.mvEvalAdic_X (A := Λ) (maximalIdeal R) x hx j
  have hfC : ∀ a : Λ, f (C a) = a := fun a => GlobalTheory.mvEvalAdic_C (A := Λ) (maximalIdeal R) x hx a
  have hle : ∀ g ∈ maximalIdeal (ChartRing Λ m (d - m)), f g ∈ maximalIdeal R := by
    intro g hg
    have h4 := GlobalTheory.algHom_sub_constantCoeff_mem f (K := maximalIdeal R) (fun j => by rw [hfX]; exact hx j) g
    have h5 := GlobalTheory.FormalIsogeny.mem_maximalIdeal_iff_constantCoeff.1 hg
    rw [hb, Ideal.mem_bot] at h5
    rwa [h5, map_zero, sub_zero] at h4
  have hXm : ∀ j, (X j : ChartRing Λ m (d - m)) ∈ maximalIdeal (ChartRing Λ m (d - m)) := fun j =>
    GlobalTheory.FormalIsogeny.mem_maximalIdeal_iff_constantCoeff.2 (by simp)
  have hloc : IsLocalHom (f : ChartRing Λ m (d - m) →+* R) := ⟨fun g hg => by
    by_contra hn
    exact (hle g hn) hg⟩
  have hres : ∀ z : R, ∃ r, z - (f : ChartRing Λ m (d - m) →+* R) r ∈ maximalIdeal R := by
    intro z
    obtain ⟨a, ha, h⟩ := hΛ z
    exact ⟨C ⟨a, ha⟩, by simpa [hfC] using h⟩
  have hcot : maximalIdeal R ≤ (maximalIdeal (ChartRing Λ m (d - m))).map (f : ChartRing Λ m (d - m) →+* R) ⊔
      maximalIdeal R ^ 2 := by
    intro z hz
    obtain ⟨c, hc'⟩ := (Submodule.mem_span_range_iff_exists_fun (ResidueField R)).1
      (hUtop ((maximalIdeal R).toCotangent ⟨z, hz⟩))
    choose a ha using fun j => residue_surjective (R := R) (c j)
    have h1 : ∑ j, residue R (a j) • g j = (maximalIdeal R).toCotangent ⟨z, hz⟩ := by simpa [ha] using hc'
    rw [sum_residue_smul_toCotangent, Ideal.toCotangent_eq] at h1
    have h2 : ∑ j, a j * x j ∈ (maximalIdeal (ChartRing Λ m (d - m))).map (f : ChartRing Λ m (d - m) →+* R) :=
      sum_mem fun j _ => Ideal.mul_mem_left _ _ (by rw [← hfX]; exact Ideal.mem_map_of_mem _ (hXm j))
    have h3 : z = ∑ j, a j * x j + (z - ∑ j, a j * x j) := by ring
    rw [h3]
    refine Submodule.add_mem_sup h2 ?_
    have : (z - ∑ j, a j * x j) = -((∑ j, a j * x j) - z) := by ring
    rw [this]
    exact neg_mem h1
  have hcA : IsAdicComplete (maximalIdeal (ChartRing Λ m (d - m))) (ChartRing Λ m (d - m)) :=
    GlobalTheory.CohenStructure.isAdicComplete_of_ringEquiv
      (MvPowerSeries.renameEquiv Λ finSumFinEquiv.symm).toRingEquiv
      (h := GlobalTheory.CohenStructure.isAdicComplete_mvPowerSeries Λ (m + (d - m)))
  have hsurj : Function.Surjective (f : ChartRing Λ m (d - m) →+* R) :=
    GlobalTheory.LocalSurj.surjective_of_residue_of_cotangent _ R _ hcA hloc hres hcot
  letI : Algebra (ChartRing Λ m (d - m)) R := (f : ChartRing Λ m (d - m) →+* R).toAlgebra
  haveI : Module.Finite (ChartRing Λ m (d - m)) R :=
    Module.Finite.of_surjective (Algebra.linearMap (ChartRing Λ m (d - m)) R) hsurj
  have hdA : ringKrullDim (ChartRing Λ m (d - m)) = ((m + (d - m) : ℕ) : WithBot ℕ∞) := by
    rw [GlobalTheory.FormalIsogeny.ringKrullDim_mvPowerSeries, ringKrullDim_eq_zero_of_isField hF, Nat.card_sum,
      Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_fin, Fintype.card_fin, zero_add]
  have hdR : ringKrullDim R = ((m + (d - m) : ℕ) : WithBot ℕ∞) := by
    rw [← (IsRegularLocalRing.iff_finrank_cotangentSpace R).mp inferInstance, ← hd]
    have hmd' : m + (d - m) = d := by omega
    rw [hmd']
  have hinj : Function.Injective (f : ChartRing Λ m (d - m) →+* R) :=
    GlobalTheory.CohenStructure.injective_of_ringKrullDim_eq hdA hdR
  let φ := RingEquiv.ofBijective (f : ChartRing Λ m (d - m) →+* R) ⟨hinj, hsurj⟩
  refine ⟨Λ, inferInstance, d - m, φ.symm, fun i => ?_⟩
  rw [RingEquiv.symm_apply_eq]
  show t i = f (X (Sum.inl i))
  rw [hfX]
  rfl

end GlobalTheory.CohenChart
