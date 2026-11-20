import Formalism.LocalRingCardinality.SpanPowerMembership.NDLocE

noncomputable section

namespace Formalism.BasicNotions.Examples₂.LB

open NumberField IsDedekindDomain Polynomial IsLocalRing Formalism.BasicNotions Formalism.BasicNotions.Loc

variable {l : ℕ} [hl : Fact l.Prime] (LL : FinExt l)

/- English proof (translation)
Establish `h` using `PadicInt.toZMod_spec c`. Rewrite `h` using `[PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton]`. Take `⟨d, hd⟩` from `h`. Establish `hc : c = (((PadicInt.toZMod c).val : ℕ) : ℤ_[l]) + (l : ℤ_[l]) * d`. Rewrite using `[← hd, ZMod.natCast_val]`.

Expand and normalize the polynomial expressions, which then agree. Use `conv_lhs => rw [hc]`. Rewrite using `[map_add, map_add, map_mul, map_mul, map_natCast, map_natCast, map_natCast, map_natCast]`. Establish `h0 : (((l : ℕ) : ResidueField ↥(OL LL))) = 0`. Rewrite using `[← map_natCast (residue ↥(OL LL))]`.

Conclude with `(residue_eq_zero_iff _).mpr (l_mem_max LL)`. Rewrite using `[h0, zero_mul, add_zero]`.
-/
theorem residue_algebraMap (c : ℤ_[l]) :
    residue ↥(OL LL) (algebraMap ℤ_[l] ↥(OL LL) c) = (((PadicInt.toZMod c).val : ℕ) : ResidueField ↥(OL LL)) := by
  have h := PadicInt.toZMod_spec c
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at h
  obtain ⟨d, hd⟩ := h
  have hc : c = (((PadicInt.toZMod c).val : ℕ) : ℤ_[l]) + (l : ℤ_[l]) * d := by
    rw [← hd, ZMod.natCast_val]; ring
  conv_lhs => rw [hc]
  rw [map_add, map_add, map_mul, map_mul, map_natCast, map_natCast, map_natCast, map_natCast]
  have h0 : (((l : ℕ) : ResidueField ↥(OL LL))) = 0 := by
    rw [← map_natCast (residue ↥(OL LL))]
    exact (residue_eq_zero_iff _).mpr (l_mem_max LL)
  rw [h0, zero_mul, add_zero]

/- English proof (translation)
Take `⟨n, s, hs⟩` from `Module.Finite.exists_fin (R := ℤ_[l]) (M := ↥(OL LL))`. Use `haveI : NeZero l := ⟨hl.out.ne_zero⟩`. Set `f : (Fin n → ZMod l) → ResidueField ↥(OL LL)` to `fun a => ∑ i, (((a i).val : ℕ) : ResidueField ↥(OL LL)) * residue ↥(OL LL) (s i)`. Use `Finite.of_surjective f fun y => ?_` and prove the remaining obligations. Take `⟨x, rfl⟩` from `residue_surjective y`.

Establish `hx : x ∈ Submodule.span ℤ_[l] (Set.range s)` using `hs ▸ Submodule.mem_top`. Take `⟨c, rfl⟩` from `(Submodule.mem_span_range_iff_exists_fun ℤ_[l]).mp hx`. Use `⟨fun i => PadicInt.toZMod (c i), ?_⟩` and prove the remaining obligations. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[Algebra.smul_def, map_mul, residue_algebraMap]`.
-/
theorem OL_resFinite : Finite (ResidueField ↥(OL LL)) := by
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := ℤ_[l]) (M := ↥(OL LL))
  haveI : NeZero l := ⟨hl.out.ne_zero⟩
  let f : (Fin n → ZMod l) → ResidueField ↥(OL LL) :=
    fun a => ∑ i, (((a i).val : ℕ) : ResidueField ↥(OL LL)) * residue ↥(OL LL) (s i)
  refine Finite.of_surjective f fun y => ?_
  obtain ⟨x, rfl⟩ := residue_surjective y
  have hx : x ∈ Submodule.span ℤ_[l] (Set.range s) := hs ▸ Submodule.mem_top
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ_[l]).mp hx
  refine ⟨fun i => PadicInt.toZMod (c i), ?_⟩
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.smul_def, map_mul, residue_algebraMap]

def toOm : ↥(OL LL) →+* PadicAlgCl l := LL.1.val.toRingHom.comp (OL LL).val.toRingHom

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem toOm_apply (a : ↥(OL LL)) : toOm LL a = ((a : ↥LL.1) : PadicAlgCl l) := rfl

/- English proof (translation)
Introduce `a b h` and use `Subtype.ext (Subtype.ext h)`.
-/
theorem toOm_injective : Function.Injective (toOm LL) := fun a b h => Subtype.ext (Subtype.ext h)

/- English proof (translation)
The claim follows from `Topology.IsInducing.subtypeVal.comp Topology.IsInducing.subtypeVal`.
-/
theorem inducing_toOm : Topology.IsInducing (toOm LL) :=
  Topology.IsInducing.subtypeVal.comp Topology.IsInducing.subtypeVal

instance OL_topRing : IsTopologicalRing ↥(OL LL) :=
  { toContinuousAdd := (inducing_toOm LL).continuousAdd (toOm LL)
    toContinuousMul := (inducing_toOm LL).continuousMul (toOm LL)
    toContinuousNeg := (inducing_toOm LL).continuousNeg (map_neg (toOm LL)) }

/- English proof (translation)
The claim follows from `norm_pow _ _`.
-/
theorem nrm_pow (a : ↥(OL LL)) (n : ℕ) : nrm LL (a ^ n) = nrm LL a ^ n := norm_pow _ _

/- English proof (translation)
Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible ↥(OL LL)`. Establish `h1 : nrm LL ϖ < 1` using `(mem_max LL ϖ).mp hϖ.not_isUnit`. Establish `h0 : 0 < nrm LL ϖ` using `lt_of_le_of_ne (norm_nonneg _) fun e => hϖ.ne_zero ((nrm_eq_zero LL ϖ).mp e.symm)`. Establish `key : ∀ n : ℕ, ((maximalIdeal ↥(OL LL) ^ n : Ideal ↥(OL LL)) : Set ↥(OL LL)) = toOm LL ⁻¹' Metric.closedBall 0 (nrm LL ϖ ^ n)` using `fun n => by`. Use extensionality with `a`.

Rewrite using `[hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, SetLike.mem_coe, Ideal.mem_span_singleton, dvd_iff, nrm_pow, Set.mem_preimage, Metric.mem_closedBall, dist_zero_right]`. Both sides reduce to the same expression. Use `isAdic_iff.mpr ⟨fun n => ?_, fun s hs => ?_⟩` and prove the remaining obligations. Rewrite using `[key]`. Conclude with `(IsUltrametricDist.isOpen_closedBall _ (pow_pos h0 n).ne').preimage (inducing_toOm LL).continuous`.

Rewrite `hs` using `[(inducing_toOm LL).nhds_eq_comap, Filter.mem_comap]`. Take `⟨t, ht, hts⟩` from `hs`. Rewrite `ht` using `[map_zero]`. Take `⟨ε, hε, h⟩` from `Metric.mem_nhds_iff.mp ht`. Take `⟨n, hn⟩` from `exists_pow_lt_of_lt_one hε h1`.

Conclude with `⟨n, by`. Rewrite using `[key]`. Conclude with `(Set.preimage_mono ((Metric.closedBall_subset_ball hn).trans h)).trans hts⟩`.
-/
theorem OL_adic : IsAdic (maximalIdeal ↥(OL LL)) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible ↥(OL LL)
  have h1 : nrm LL ϖ < 1 := (mem_max LL ϖ).mp hϖ.not_isUnit
  have h0 : 0 < nrm LL ϖ := lt_of_le_of_ne (norm_nonneg _) fun e => hϖ.ne_zero ((nrm_eq_zero LL ϖ).mp e.symm)
  have key : ∀ n : ℕ, ((maximalIdeal ↥(OL LL) ^ n : Ideal ↥(OL LL)) : Set ↥(OL LL)) =
      toOm LL ⁻¹' Metric.closedBall 0 (nrm LL ϖ ^ n) := fun n => by
    ext a
    rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, SetLike.mem_coe, Ideal.mem_span_singleton, dvd_iff,
      nrm_pow, Set.mem_preimage, Metric.mem_closedBall, dist_zero_right]
    rfl
  refine isAdic_iff.mpr ⟨fun n => ?_, fun s hs => ?_⟩
  · rw [key]
    exact (IsUltrametricDist.isOpen_closedBall _ (pow_pos h0 n).ne').preimage (inducing_toOm LL).continuous
  · rw [(inducing_toOm LL).nhds_eq_comap, Filter.mem_comap] at hs
    obtain ⟨t, ht, hts⟩ := hs
    rw [map_zero] at ht
    obtain ⟨ε, hε, h⟩ := Metric.mem_nhds_iff.mp ht
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε h1
    exact ⟨n, by
      rw [key]
      exact (Set.preimage_mono ((Metric.closedBall_subset_ball hn).trans h)).trans hts⟩

def toC : ↥(OL LL) →+* ℂ_[l] := (algebraMap (PadicAlgCl l) ℂ_[l]).comp (toOm LL)

/- English proof (translation)
Introduce `a b h` and use `toOm_injective LL ((algebraMap (PadicAlgCl l) ℂ_[l]).injective h)`.
-/
theorem toC_injective : Function.Injective (toC LL) := fun a b h =>
  toOm_injective LL ((algebraMap (PadicAlgCl l) ℂ_[l]).injective h)

/- English proof (translation)
The claim follows from `PadicComplex.norm_extends l _`.
-/
theorem norm_toC (a : ↥(OL LL)) : ‖toC LL a‖ = nrm LL a := PadicComplex.norm_extends l _

def toFrac : ↥LL.1 →+* FractionRing ↥(OL LL) := (FractionRing.algEquiv ↥(OL LL) ↥LL.1).symm.toRingEquiv.toRingHom

/- English proof (translation)
Use `show (FractionRing.algEquiv ↥(OL LL) ↥LL.1).symm (a : ↥LL.1) = _`. Rewrite using `[AlgEquiv.symm_apply_eq, AlgEquiv.commutes]`. Both sides reduce to the same expression.
-/
theorem toFrac_coe (a : ↥(OL LL)) : toFrac LL (a : ↥LL.1) = algebraMap ↥(OL LL) (FractionRing ↥(OL LL)) a := by
  show (FractionRing.algEquiv ↥(OL LL) ↥LL.1).symm (a : ↥LL.1) = _
  rw [AlgEquiv.symm_apply_eq, AlgEquiv.commutes]
  rfl

/- English proof (translation)
Rewrite using `[← toFrac_coe]`. Conclude with `(FractionRing.algEquiv ↥(OL LL) ↥LL.1).symm.injective.eq_iff`.
-/
theorem toFrac_eq_iff (x : ↥LL.1) (a : ↥(OL LL)) :
    algebraMap ↥(OL LL) (FractionRing ↥(OL LL)) a = toFrac LL x ↔ (a : ↥LL.1) = x := by
  rw [← toFrac_coe]
  exact (FractionRing.algEquiv ↥(OL LL) ↥LL.1).symm.injective.eq_iff

end Formalism.BasicNotions.Examples₂.LB
