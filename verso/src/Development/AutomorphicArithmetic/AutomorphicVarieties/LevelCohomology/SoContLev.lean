import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.SoDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.ContTw
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.DvrFacts
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.LocallyConstantMaps

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.X

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.LocallyConstantMaps.locConst ψ h`.
-/
private theorem locConst {Γ A : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Group A] (ψ : Γ →* A)
    (h : IsOpen (ψ.ker : Set Γ)) : IsLocallyConstant ψ :=
  _root_.UpperTheory.Reformulated.B.LocallyConstantMaps.locConst ψ h

/- English proof (translation)
Take `⟨-, -, -, -, -, h0, -, hval, -⟩` from `dvrFacts l O`. Rewrite `h0` using `[hval, Ne, IsDiscreteValuationRing.addVal_eq_zero_iff]`. Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible O`. Take `⟨N, hN⟩` from `IsDiscreteValuationRing.associated_pow_irreducible ha hϖ`. Establish `hl : ϖ ∣ (l : O)`.

Rewrite using `[← Ideal.mem_span_singleton, ← hϖ.maximalIdeal_eq]`. Conclude with `h0`. Conclude with `⟨N, hN.dvd.trans (pow_dvd_pow_of_dvd hl N)⟩`.
-/
private theorem dvd_pow_l (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] (a : O) (ha : a ≠ 0) : ∃ N : ℕ, a ∣ (l : O) ^ N := by
  obtain ⟨-, -, -, -, -, h0, -, hval, -⟩ := dvrFacts l O
  rw [hval, Ne, IsDiscreteValuationRing.addVal_eq_zero_iff] at h0
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨N, hN⟩ := IsDiscreteValuationRing.associated_pow_irreducible ha hϖ
  have hl : ϖ ∣ (l : O) := by
    rw [← Ideal.mem_span_singleton, ← hϖ.maximalIdeal_eq]
    exact h0
  exact ⟨N, hN.dvd.trans (pow_dvd_pow_of_dvd hl N)⟩

/- English proof (translation)
Rewrite using `[IsLocallyConstant.iff_eventually_eq]`. Introduce `c`. Establish `hp : (0 : ℝ) < (l : ℝ) ^ (-(N : ℤ))` using `zpow_pos (by exact_mod_cast (Fact.out : l.Prime).pos) _`. Use `filter_upwards [Metric.closedBall_mem_nhds c hp] with x hx`. Rewrite `hx` using `[Metric.mem_closedBall, dist_eq_norm, PadicInt.norm_le_pow_iff_mem_span_pow, Ideal.mem_span_singleton']`.

Take `⟨t, ht⟩` from `hx`. Rewrite using `[← sub_eq_zero, ← sub_smul, ← map_sub, ← ht, map_mul, map_pow, map_natCast, mul_smul, hm, smul_zero]`.
-/
private theorem locConst_smul (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O] (M : Type)
    [AddCommGroup M] [Module O M] (N : ℕ) (m : M) (hm : (l : O) ^ N • m = 0) :
    IsLocallyConstant fun c : ℤ_[l] => algebraMap ℤ_[l] O c • m := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro c
  have hp : (0 : ℝ) < (l : ℝ) ^ (-(N : ℤ)) := zpow_pos (by exact_mod_cast (Fact.out : l.Prime).pos) _
  filter_upwards [Metric.closedBall_mem_nhds c hp] with x hx
  rw [Metric.mem_closedBall, dist_eq_norm, PadicInt.norm_le_pow_iff_mem_span_pow, Ideal.mem_span_singleton'] at hx
  obtain ⟨t, ht⟩ := hx
  rw [← sub_eq_zero, ← sub_smul, ← map_sub, ← ht, map_mul, map_pow, map_natCast, mul_smul, hm, smul_zero]

/- English proof (translation)
Introduce `k Ω _ _ _ _ _ l _ O _ _ _ _ _ ψ n hψ a M _ _ _ _ ρ h`. Establish `hc` using `(contTw k Ω l).1`. Take `⟨N, b, hb⟩` from `dvd_pow_l l O a h.ne`. Take `⟨e⟩` from `h.cyc`. Use `continuous_prod_of_discrete_right.2 fun m => ?_` and prove the remaining obligations.

Establish `hm : (l : O) ^ N • m = 0`. Apply `e.injective` to reduce the goal to its premises. Take `⟨x, hx⟩` from `Ideal.Quotient.mk_surjective (e m)`. Rewrite using `[map_smul, map_zero, ← hx]`. Use `show Ideal.Quotient.mk _ ((l : O) ^ N * x) = 0`.

Rewrite using `[Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton, hb, mul_assoc]`. Conclude with `dvd_mul_right _ _`. Establish `h1` using `(locConst_smul l O M N m hm).comp_continuous (f := fun g => ((cycZ k Ω l g ^ n : ℤ_[l]ˣ) : ℤ_[l])) (Units.continuous_val.comp (hc.zpow n))`. Establish `h2` using `((locConst ψ hψ).prodMk h1).comp fun p : Oˣ × M => (p.1 : O) • p.2`. Use `h2.continuous.congr fun g => ?_` and prove the remaining obligations.

Use `show (ψ g : O) • (algebraMap ℤ_[l] O ((cycZ k Ω l g ^ n : ℤ_[l]ˣ) : ℤ_[l]) • m) = ρ g m`. Establish `e' : chiO k Ω l O g ^ n = Units.map (algebraMap ℤ_[l] O).toMonoidHom (cycZ k Ω l g ^ n)` using `(map_zpow (Units.map (algebraMap ℤ_[l] O).toMonoidHom) (cycZ k Ω l g) n).symm`. Rewrite using `[h.act]`. Use `show _ = ((ψ g * chiO k Ω l O g ^ n : Oˣ) : O) • m`. Rewrite using `[Units.val_mul, mul_smul, e']`.

Both sides reduce to the same expression.
-/
theorem UpperTheory.V.X.So.contLev :
    ∀ (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] (ψ : G k Ω →* Oˣ) (n : ℤ), IsOpen (ψ.ker : Set (G k Ω)) → ∀ (a : O) (M : Type) [AddCommGroup M] [Module O M] [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation O (G k Ω) M), IsLev a (ψ * chiO k Ω l O ^ n) ρ → ContAction ρ := by
  intro k Ω _ _ _ _ _ l _ O _ _ _ _ _ ψ n hψ a M _ _ _ _ ρ h
  have hc := (contTw k Ω l).1
  obtain ⟨N, b, hb⟩ := dvd_pow_l l O a h.ne
  obtain ⟨e⟩ := h.cyc
  refine continuous_prod_of_discrete_right.2 fun m => ?_
  have hm : (l : O) ^ N • m = 0 := by
    apply e.injective
    obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (e m)
    rw [map_smul, map_zero, ← hx]
    show Ideal.Quotient.mk _ ((l : O) ^ N * x) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton, hb, mul_assoc]
    exact dvd_mul_right _ _
  have h1 := (locConst_smul l O M N m hm).comp_continuous
    (f := fun g => ((cycZ k Ω l g ^ n : ℤ_[l]ˣ) : ℤ_[l])) (Units.continuous_val.comp (hc.zpow n))
  have h2 := ((locConst ψ hψ).prodMk h1).comp fun p : Oˣ × M => (p.1 : O) • p.2
  refine h2.continuous.congr fun g => ?_
  show (ψ g : O) • (algebraMap ℤ_[l] O ((cycZ k Ω l g ^ n : ℤ_[l]ˣ) : ℤ_[l]) • m) = ρ g m
  have e' : chiO k Ω l O g ^ n = Units.map (algebraMap ℤ_[l] O).toMonoidHom (cycZ k Ω l g ^ n) :=
    (map_zpow (Units.map (algebraMap ℤ_[l] O).toMonoidHom) (cycZ k Ω l g) n).symm
  rw [h.act]
  show _ = ((ψ g * chiO k Ω l O g ^ n : Oˣ) : O) • m
  rw [Units.val_mul, mul_smul, e']
  rfl
