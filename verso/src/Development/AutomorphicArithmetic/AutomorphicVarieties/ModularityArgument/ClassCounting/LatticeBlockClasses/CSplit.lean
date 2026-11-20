import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LatticeBlockClasses.CBlockValAlt

open NumberField IsDedekindDomain UpperTheory.V UpperTheory.V.KL UpperTheory.V.ZK UpperTheory.V.ZK.Cl

/- English proof (translation)
Set `B` to `Module.finBasis L F`. Take `⟨m, hm, hi⟩` from `exists_integral_multiples ℤ ℚ (L := F) (Finset.univ.image B ∪ Finset.univ.image B.traceDual)`. Use `⟨_, fun i => ⟨m • B.traceDual i, hi _ (by simp)⟩, fun i => ⟨m • B i, hi _ (by simp)⟩, (m : 𝓞 L) ^ 2, pow_ne_zero _ (Int.cast_ne_zero.2 hm), fun x => ?_⟩` and prove the remaining obligations. Establish `h` using `B.traceDual.sum_repr x`. Use `conv_lhs => rw [← h]`.

Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Module.Basis.traceDual_repr_apply, Algebra.traceForm_apply, Algebra.smul_def]`. Express the relevant statement in the definitionally equal form `_ = algebraMap L F (Algebra.trace L F (x * (m • B i))) * (m • B.traceDual i)`. Rewrite using `[mul_smul_comm m x, map_zsmul, map_zsmul]`.

Simplify using `only [zsmul_eq_mul, map_pow, map_intCast]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem dualFam (L F : Type) [Field L] [NumberField L] [Field F] [NumberField F] [Algebra L F] :
    ∃ (n : ℕ) (e f : Fin n → 𝓞 F) (b : 𝓞 L), b ≠ 0 ∧ ∀ x : F,
      algebraMap L F b * x = ∑ i, algebraMap L F (Algebra.trace L F (x * f i)) * e i := by
  classical
  let B := Module.finBasis L F
  obtain ⟨m, hm, hi⟩ := exists_integral_multiples ℤ ℚ (L := F)
    (Finset.univ.image B ∪ Finset.univ.image B.traceDual)
  refine ⟨_, fun i => ⟨m • B.traceDual i, hi _ (by simp)⟩, fun i => ⟨m • B i, hi _ (by simp)⟩,
    (m : 𝓞 L) ^ 2, pow_ne_zero _ (Int.cast_ne_zero.2 hm), fun x => ?_⟩
  have h := B.traceDual.sum_repr x
  conv_lhs => rw [← h]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Module.Basis.traceDual_repr_apply, Algebra.traceForm_apply, Algebra.smul_def]
  change _ = algebraMap L F (Algebra.trace L F (x * (m • B i))) * (m • B.traceDual i)
  rw [mul_smul_comm m x, map_zsmul, map_zsmul]
  simp only [zsmul_eq_mul, map_pow, map_intCast]
  ring

/- English proof (translation)
Establish `hli` using `(linearIndependent_monoidHom F F).comp (fun ρ : F ≃ₐ[L] F => (ρ : F →* F)) (fun ρ ρ' hh => AlgEquiv.ext fun x => DFunLike.congr_fun hh x)`. Use `(Fintype.linearIndependent_iffₛ.1 hli) (fun ρ => ∑ i, ρ (f i) * σ (e i)) (fun ρ => if ρ = σ then algebraMap L F b else 0) (by` as an intermediate fact. Use function extensionality and compare the values at `x`. Establish `h1` using `congrArg σ (h x)`. Simplify using `only [map_mul, map_sum, AlgEquiv.commutes] at h1`.

Simplify using `only [trace_eq_sum_automorphisms, map_mul, Finset.sum_mul] at h1`. Rewrite `h1` using `[Finset.sum_comm]`. Simplify using `only [Finset.sum_apply, Pi.smul_apply, Function.comp_apply, smul_eq_mul, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true, MonoidHom.coe_coe, Finset.sum_mul]`. Rewrite using `[h1]`. Conclude with `Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring) τ`.

Use `this` and compare the differences between its conclusion and the goal.
-/
private theorem orth {L F : Type} [Field L] [NumberField L] [Field F] [NumberField F] [Algebra L F] [IsGalois L F]
    {n : ℕ} (e f : Fin n → F) (b : L)
    (h : ∀ x : F, algebraMap L F b * x = ∑ i, algebraMap L F (Algebra.trace L F (x * f i)) * e i)
    (σ τ : F ≃ₐ[L] F) [Decidable (τ = σ)] : ∑ i, τ (f i) * σ (e i) = if τ = σ then algebraMap L F b else 0 := by
  classical
  have hli := (linearIndependent_monoidHom F F).comp (fun ρ : F ≃ₐ[L] F => (ρ : F →* F))
    (fun ρ ρ' hh => AlgEquiv.ext fun x => DFunLike.congr_fun hh x)
  have := (Fintype.linearIndependent_iffₛ.1 hli) (fun ρ => ∑ i, ρ (f i) * σ (e i))
    (fun ρ => if ρ = σ then algebraMap L F b else 0) (by
      funext x
      have h1 := congrArg σ (h x)
      simp only [map_mul, map_sum, AlgEquiv.commutes] at h1
      simp only [trace_eq_sum_automorphisms, map_mul, Finset.sum_mul] at h1
      rw [Finset.sum_comm] at h1
      simp only [Finset.sum_apply, Pi.smul_apply, Function.comp_apply, smul_eq_mul, ite_mul, zero_mul,
        Finset.sum_ite_eq', Finset.mem_univ, if_true, MonoidHom.coe_coe, Finset.sum_mul]
      rw [h1]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring) τ
  convert this

/- English proof (translation)
Introduce `L F _ _ _ _ _ hG`. Take `⟨n, e, f, b, hb, h⟩` from `dualFam L F`. Use `⟨b, hb, fun k _ _ r hr hrb => ⟨fun v => ?_, fun a ha => ?_⟩⟩` and prove the remaining obligations. Use `choose s hs using hr`. Establish `hs' : ∀ y, r (algebraMap (𝓞 L) (𝓞 F) (s y)) = y` using `hs`.

Establish `hσ : ∀ (σ : F ≃ₐ[L] F) (c : 𝓞 L), actO σ (algebraMap (𝓞 L) (𝓞 F) c) = algebraMap (𝓞 L) (𝓞 F) c` using `fun σ c => RingOfIntegers.ext (σ.commutes (c : L))`. Establish `ho : ∀ σ τ : F ≃ₐ[L] F, ∑ i, actO τ (f i) * actO σ (e i) = if τ = σ then algebraMap (𝓞 L) (𝓞 F) b else 0`. Introduce `σ τ`. Apply `RingOfIntegers.ext` to reduce the goal to its premises. Use `orth (fun i => (e i : F)) (fun i => (f i : F)) (b : L) h σ τ` as an intermediate fact.

Simplify using `only [map_sum, map_mul]`. Use `this.trans ?_` and prove the remaining obligations. Use `split_ifs`. Both sides reduce to the same expression. Simplify using the standard rewrite rules.

Use `⟨∑ i, algebraMap (𝓞 L) (𝓞 F) (s (∑ τ, (r (algebraMap (𝓞 L) (𝓞 F) b))⁻¹ * v τ * r (actO τ (f i)))) * e i, fun σ => ?_⟩` and prove the remaining obligations. Simplify using `only [map_sum, map_mul, hσ, hs', Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`. Simplify using `only [mul_assoc, ← Finset.mul_sum, ← map_mul, ← map_sum, ho]`. Simplify using `only [apply_ite r, map_zero, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]`.

Clear the denominators using the available nonvanishing facts. Set `c : Fin n → 𝓞 L` to `fun i => ⟨Algebra.trace L F (a * f i), Algebra.isIntegral_trace (R := ℤ) (a * f i).isIntegral_coe⟩`. Establish `hc : ∀ i, algebraMap (𝓞 L) (𝓞 F) (c i) = ∑ σ : F ≃ₐ[L] F, actO σ a * actO σ (f i)`. Introduce `i`. Apply `RingOfIntegers.ext` to reduce the goal to its premises.

Use `trace_eq_sum_automorphisms (K := L) ((a : F) * f i)` as an intermediate fact. Simplify using `only [map_sum, map_mul] at this ⊢`. Conclude with `this`. Establish `hba : algebraMap (𝓞 L) (𝓞 F) b * a = ∑ i, algebraMap (𝓞 L) (𝓞 F) (c i) * e i`. Apply `RingOfIntegers.ext` to reduce the goal to its premises.

Simplify using `only [map_sum, map_mul]`. Conclude with `h a`. Take `⟨b', hb'⟩` from `hr (r (algebraMap (𝓞 L) (𝓞 F) b))⁻¹`. Establish `h1 : a = algebraMap (𝓞 L) (𝓞 F) (1 - b' * b) * a + algebraMap (𝓞 L) (𝓞 F) b' * ∑ i, algebraMap (𝓞 L) (𝓞 F) (c i) * e i`. Rewrite using `[← hba, map_sub, map_mul, map_one]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h1]`. Use `Ideal.add_mem _ (Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ?_)) (Ideal.mul_mem_left _ _ (Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ?_)))` and prove the remaining obligations. Rewrite using `[RingHom.mem_ker, map_sub, map_mul, map_one, hb', RingHom.comp_apply, inv_mul_cancel₀ hrb, sub_self]`. Rewrite using `[RingHom.mem_ker, RingHom.comp_apply, hc]`.

Simplify using `[ha]`.
-/
theorem UpperTheory.V.ZK.Cl.cSplit :
    UpperTheory.V.ZK.Cl.CSplit := by
  classical
  intro L F _ _ _ _ _ hG
  obtain ⟨n, e, f, b, hb, h⟩ := dualFam L F
  refine ⟨b, hb, fun k _ _ r hr hrb => ⟨fun v => ?_, fun a ha => ?_⟩⟩
  · choose s hs using hr
    have hs' : ∀ y, r (algebraMap (𝓞 L) (𝓞 F) (s y)) = y := hs
    have hσ : ∀ (σ : F ≃ₐ[L] F) (c : 𝓞 L), actO σ (algebraMap (𝓞 L) (𝓞 F) c) = algebraMap (𝓞 L) (𝓞 F) c :=
      fun σ c => RingOfIntegers.ext (σ.commutes (c : L))
    have ho : ∀ σ τ : F ≃ₐ[L] F, ∑ i, actO τ (f i) * actO σ (e i) =
        if τ = σ then algebraMap (𝓞 L) (𝓞 F) b else 0 := by
      intro σ τ
      apply RingOfIntegers.ext
      have := orth (fun i => (e i : F)) (fun i => (f i : F)) (b : L) h σ τ
      simp only [map_sum, map_mul]
      refine this.trans ?_
      split_ifs
      · rfl
      · simp
    refine ⟨∑ i, algebraMap (𝓞 L) (𝓞 F)
      (s (∑ τ, (r (algebraMap (𝓞 L) (𝓞 F) b))⁻¹ * v τ * r (actO τ (f i)))) * e i, fun σ => ?_⟩
    simp only [map_sum, map_mul, hσ, hs', Finset.sum_mul]
    rw [Finset.sum_comm]
    simp only [mul_assoc, ← Finset.mul_sum, ← map_mul, ← map_sum, ho]
    simp only [apply_ite r, map_zero, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    field_simp
  · let c : Fin n → 𝓞 L := fun i => ⟨Algebra.trace L F (a * f i),
      Algebra.isIntegral_trace (R := ℤ) (a * f i).isIntegral_coe⟩
    have hc : ∀ i, algebraMap (𝓞 L) (𝓞 F) (c i) = ∑ σ : F ≃ₐ[L] F, actO σ a * actO σ (f i) := by
      intro i
      apply RingOfIntegers.ext
      have := trace_eq_sum_automorphisms (K := L) ((a : F) * f i)
      simp only [map_sum, map_mul] at this ⊢
      exact this
    have hba : algebraMap (𝓞 L) (𝓞 F) b * a = ∑ i, algebraMap (𝓞 L) (𝓞 F) (c i) * e i := by
      apply RingOfIntegers.ext
      simp only [map_sum, map_mul]
      exact h a
    obtain ⟨b', hb'⟩ := hr (r (algebraMap (𝓞 L) (𝓞 F) b))⁻¹
    have h1 : a = algebraMap (𝓞 L) (𝓞 F) (1 - b' * b) * a +
        algebraMap (𝓞 L) (𝓞 F) b' * ∑ i, algebraMap (𝓞 L) (𝓞 F) (c i) * e i := by
      rw [← hba, map_sub, map_mul, map_one]; ring
    rw [h1]
    refine Ideal.add_mem _ (Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ?_))
      (Ideal.mul_mem_left _ _ (Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ?_)))
    · rw [RingHom.mem_ker, map_sub, map_mul, map_one, hb', RingHom.comp_apply, inv_mul_cancel₀ hrb, sub_self]
    · rw [RingHom.mem_ker, RingHom.comp_apply, hc]
      simp [ha]
