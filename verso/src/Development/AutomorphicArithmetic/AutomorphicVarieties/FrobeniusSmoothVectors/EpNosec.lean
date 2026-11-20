import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.EpresGr
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoSurj
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoMvps
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.PredMulSumPadicValNatFactorialAddCardLe

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

/- English proof (translation)
Rewrite using `[mem_maximalIdeal, mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff]`.
-/
private theorem ns_mem_max {O σ : Type} [CommRing O] [IsLocalRing O] (x : MvPowerSeries σ O) :
    x ∈ maximalIdeal (MvPowerSeries σ O) ↔ MvPowerSeries.constantCoeff x ∈ maximalIdeal O := by
  rw [mem_maximalIdeal, mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff,
    MvPowerSeries.isUnit_iff_constantCoeff]

/- English proof (translation)
Rewrite using `[← res_eq_zero_iff O, res_map, res_eq_zero_iff]`.
-/
private theorem ns_loc {O R R' : Type} [CommRing O] [IsLocalRing O] [CommRing R] [Algebra O R] [IsCO O R]
    [CommRing R'] [Algebra O R'] [IsCO O R'] (f : R →ₐ[O] R') (x : R) :
    f x ∈ maximalIdeal R' ↔ x ∈ maximalIdeal R := by
  rw [← res_eq_zero_iff O, res_map, res_eq_zero_iff]

/- English proof (translation)
Rewrite using `[MvPowerSeries.X, MvPowerSeries.coeff_monomial_mul]`. Distinguish the cases in `h : t = s`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Rewrite using `[if_neg h, if_neg]`.

Introduce `hle`. Use `hle t` as an intermediate fact. Simplify using `[Finsupp.single_apply, Ne.symm h] at this`.
-/
private theorem ns_coeff {O σ : Type} [CommRing O] [DecidableEq σ] (s t : σ) (k : MvPowerSeries σ O) :
    MvPowerSeries.coeff (Finsupp.single s 1) (MvPowerSeries.X t * k) =
      if t = s then MvPowerSeries.constantCoeff k else 0 := by
  rw [MvPowerSeries.X, MvPowerSeries.coeff_monomial_mul]
  by_cases h : t = s
  · subst h
    simp
  · rw [if_neg h, if_neg]
    intro hle
    have := hle t
    simp [Finsupp.single_apply, Ne.symm h] at this

/- English proof (translation)
Take `⟨h, -, hh⟩` from `GlobalTheory.exists_eq_sum_X_mul (n := 0) (g := g - algebraMap O _ (MvPowerSeries.constantCoeff g)) (by`. Introduce `d hd`. Establish `hd0 : d.degree = 0` using `by omega`. Establish `: d = 0` using `(Finsupp.degree_eq_zero_iff d).mp hd0`. Substitute `this` using the available equality.

Simplify using `[Algebra.algebraMap_eq_smul_one])`. Establish `e : g = algebraMap O _ (MvPowerSeries.constantCoeff g) + ∑ i, MvPowerSeries.X i * h i`. Rewrite using `[← hh]`. Expand and normalize the polynomial expressions, which then agree. Use `⟨h, fun s => ?_, e⟩` and prove the remaining obligations.

Rewrite using `[ns_mem_max]`. Establish `hs` using `hg s`. Rewrite `hs` using `[e, map_add, map_sum]`. Simplify using `only [ns_coeff] at hs`. Simplify `hs` using `[Algebra.algebraMap_eq_smul_one, MvPowerSeries.coeff_one]`.
-/
private theorem ns_dec {O σ : Type} [CommRing O] [IsLocalRing O] [Fintype σ] (g : MvPowerSeries σ O)
    (hg : ∀ s, MvPowerSeries.coeff (Finsupp.single s 1) g ∈ maximalIdeal O) :
    ∃ k : σ → MvPowerSeries σ O, (∀ s, k s ∈ maximalIdeal (MvPowerSeries σ O)) ∧
      g = algebraMap O _ (MvPowerSeries.constantCoeff g) + ∑ s, MvPowerSeries.X s * k s := by
  classical
  obtain ⟨h, -, hh⟩ := GlobalTheory.exists_eq_sum_X_mul (n := 0)
    (g := g - algebraMap O _ (MvPowerSeries.constantCoeff g)) (by
      intro d hd
      have hd0 : d.degree = 0 := by omega
      have : d = 0 := (Finsupp.degree_eq_zero_iff d).mp hd0
      subst this
      simp [Algebra.algebraMap_eq_smul_one])
  have e : g = algebraMap O _ (MvPowerSeries.constantCoeff g) + ∑ i, MvPowerSeries.X i * h i := by
    rw [← hh]
    ring
  refine ⟨h, fun s => ?_, e⟩
  rw [ns_mem_max]
  have hs := hg s
  rw [e, map_add, map_sum] at hs
  simp only [ns_coeff] at hs
  simpa [Algebra.algebraMap_eq_smul_one, MvPowerSeries.coeff_one] using hs

/- English proof (translation)
Introduce `O _ _ _ _ ι _ R _ _ _ C _ _ _ π p s hπ hmin hX hps`. Use `haveI : Fintype ι := Fintype.ofFinite ι`. Use `haveI : IsCO O O := ⟨‹IsAdicComplete (maximalIdeal O) O›, ⟨fun a ha => by simpa using ha⟩, fun x => ⟨x, by simp⟩⟩`. Use `haveI : IsCO O (MvPowerSeries ι O) := co_mvps O O ι`. Establish `hq : ∀ x : C, p (s (p x)) = p x` using `fun x => by`.

Use `congrArg (fun φ : R →ₐ[O] R => φ (p x)) hps` as an intermediate fact. Simplify using `using this`. Establish `hE : ∀ x : C, x - s (p x) ∈ RingHom.ker p` using `fun x => by`. Rewrite using `[RingHom.mem_ker, map_sub, hq, sub_self]`. Establish `hloc : ∀ x : C, x ∈ maximalIdeal C → s (p x) ∈ maximalIdeal C` using `fun x hx => (ns_loc s (p x)).2 ((ns_loc p x).2 hx)`.

Establish `hle : RingHom.ker p ≤ maximalIdeal C • RingHom.ker p`. Introduce `t ht`. Take `⟨g, rfl⟩` from `hπ t`. Establish `hpt : p (π g) = 0` using `RingHom.mem_ker.mp ht`. Establish `hg : g ∈ RingHom.ker (p.comp π)`.

Rewrite using `[RingHom.mem_ker, AlgHom.comp_apply, hpt]`. Take `⟨k, hk, hgk⟩` from `ns_dec g (hmin.2 g hg)`. Establish `e : π g = π g - s (p (π g))` using `by rw [hpt, map_zero, sub_zero]`. Rewrite using `[e, hgk]`. Simplify using `only [map_add, map_sum, map_mul, AlgHom.commutes]`.

Rewrite using `[add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]`. Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Establish `hk' : π (k i) ∈ maximalIdeal C` using `(ns_loc π (k i)).2 (hk i)`. Establish `eq : π (MvPowerSeries.X i) * π (k i) - s (p (π (MvPowerSeries.X i))) * s (p (π (k i))) = π (k i) • (π (MvPowerSeries.X i) - s (p (π (MvPowerSeries.X i)))) + s (p (π (MvPowerSeries.X i))) • (π (k i) - s (p (π (k i))))`. Simplify using `only [smul_eq_mul]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[eq]`. Conclude with `Submodule.add_mem _ (Submodule.smul_mem_smul hk' (hE _)) (Submodule.smul_mem_smul (hloc _ (hX i)) (hE _))`. Establish `hbot : RingHom.ker p = ⊥` using `Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal C) _ (IsNoetherian.noetherian _) hle (IsLocalRing.maximalIdeal_le_jacobson _)`. Conclude with `(RingHom.injective_iff_ker_eq_bot p).2 hbot`.
-/
theorem UpperTheory.V.Fr.ep_nosec :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] (ι : Type) [Finite ι] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (C : Type) [CommRing C] [Algebra O C] [IsCO O C] (π : MvPowerSeries ι O →ₐ[O] C) (p : C →ₐ[O] R) (s : R →ₐ[O] C), Function.Surjective π → IsMinPres (p.comp π) → (∀ i, π (MvPowerSeries.X i) ∈ maximalIdeal C) → p.comp s = AlgHom.id O R → Function.Injective p := by
  intro O _ _ _ _ ι _ R _ _ _ C _ _ _ π p s hπ hmin hX hps
  classical
  haveI : Fintype ι := Fintype.ofFinite ι
  haveI : IsCO O O := ⟨‹IsAdicComplete (maximalIdeal O) O›, ⟨fun a ha => by simpa using ha⟩,
    fun x => ⟨x, by simp⟩⟩
  haveI : IsCO O (MvPowerSeries ι O) := co_mvps O O ι
  have hq : ∀ x : C, p (s (p x)) = p x := fun x => by
    have := congrArg (fun φ : R →ₐ[O] R => φ (p x)) hps
    simpa using this
  have hE : ∀ x : C, x - s (p x) ∈ RingHom.ker p := fun x => by
    rw [RingHom.mem_ker, map_sub, hq, sub_self]
  have hloc : ∀ x : C, x ∈ maximalIdeal C → s (p x) ∈ maximalIdeal C := fun x hx =>
    (ns_loc s (p x)).2 ((ns_loc p x).2 hx)
  have hle : RingHom.ker p ≤ maximalIdeal C • RingHom.ker p := by
    intro t ht
    obtain ⟨g, rfl⟩ := hπ t
    have hpt : p (π g) = 0 := RingHom.mem_ker.mp ht
    have hg : g ∈ RingHom.ker (p.comp π) := by
      rw [RingHom.mem_ker, AlgHom.comp_apply, hpt]
    obtain ⟨k, hk, hgk⟩ := ns_dec g (hmin.2 g hg)
    have e : π g = π g - s (p (π g)) := by rw [hpt, map_zero, sub_zero]
    rw [e, hgk]
    simp only [map_add, map_sum, map_mul, AlgHom.commutes]
    rw [add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
    refine Submodule.sum_mem _ fun i _ => ?_
    have hk' : π (k i) ∈ maximalIdeal C := (ns_loc π (k i)).2 (hk i)
    have eq : π (MvPowerSeries.X i) * π (k i) - s (p (π (MvPowerSeries.X i))) * s (p (π (k i))) =
        π (k i) • (π (MvPowerSeries.X i) - s (p (π (MvPowerSeries.X i)))) +
          s (p (π (MvPowerSeries.X i))) • (π (k i) - s (p (π (k i)))) := by
      simp only [smul_eq_mul]
      ring
    rw [eq]
    exact Submodule.add_mem _ (Submodule.smul_mem_smul hk' (hE _))
      (Submodule.smul_mem_smul (hloc _ (hX i)) (hE _))
  have hbot : RingHom.ker p = ⊥ :=
    Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal C) _ (IsNoetherian.noetherian _) hle
      (IsLocalRing.maximalIdeal_le_jacobson _)
  exact (RingHom.injective_iff_ker_eq_bot p).2 hbot
