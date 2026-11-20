import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.RhoFrob
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChebotarevDegreeOne

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ
open UpperTheory.V.Z.Kato.Joint Polynomial

section

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω]

/- English proof (translation)
Establish `hint : IsIntegral ℚ ζ` using `((IsAlgClosure.isAlgebraic (R := ℚ) (K := Ω)).isAlgebraic ζ).isIntegral`. Use `haveI : FiniteDimensional ℚ (IntermediateField.adjoin ℚ {ζ}) := IntermediateField.adjoin.finiteDimensional hint`. Establish `hH : IsOpen (((IntermediateField.adjoin ℚ {ζ}).fixingSubgroup : Subgroup (Ω ≃ₐ[ℚ] Ω)) : Set (Ω ≃ₐ[ℚ] Ω))` using `IntermediateField.fixingSubgroup_isOpen _`. Use `continuous_iff_continuousAt.2 fun t => ?_` and prove the remaining obligations. Establish `hU : IsOpen ((fun s : Ω ≃ₐ[ℚ] Ω => t⁻¹ * s) ⁻¹' (((IntermediateField.adjoin ℚ {ζ}).fixingSubgroup : Subgroup (Ω ≃ₐ[ℚ] Ω)) : Set (Ω ≃ₐ[ℚ] Ω)))` using `hH.preimage (continuous_mul_left _)`.

Establish `ht : t ∈ (fun s : Ω ≃ₐ[ℚ] Ω => t⁻¹ * s) ⁻¹' (((IntermediateField.adjoin ℚ {ζ}).fixingSubgroup : Subgroup (Ω ≃ₐ[ℚ] Ω)) : Set (Ω ≃ₐ[ℚ] Ω))`. Simplify using `only [Set.mem_preimage, inv_mul_cancel, SetLike.mem_coe]`. Conclude with `Subgroup.one_mem _`. Use `(continuousAt_const (y := f t)).congr ?_` and prove the remaining obligations. Use `filter_upwards [hU.mem_nhds ht] with s hs`.

Establish `h1 : (t⁻¹ * s) ζ = ζ` using `(IntermediateField.mem_fixingSubgroup_iff _ _).1 hs ζ (IntermediateField.mem_adjoin_simple_self ℚ ζ)`. Establish `h2 : s ζ = t ζ`. Establish `h3` using `congrArg t h1`. Rewrite `h3` using `[AlgEquiv.mul_apply]`. Simplify using `using h3`.

Conclude with `(h s t h2).symm`.
-/
private theorem cont_of_apply [IsAlgClosure ℚ Ω] {Y : Type} [TopologicalSpace Y] (ζ : Ω) (f : G ℚ Ω → Y)
    (h : ∀ s t : G ℚ Ω, s ζ = t ζ → f s = f t) : Continuous f := by
  have hint : IsIntegral ℚ ζ :=
    ((IsAlgClosure.isAlgebraic (R := ℚ) (K := Ω)).isAlgebraic ζ).isIntegral
  haveI : FiniteDimensional ℚ (IntermediateField.adjoin ℚ {ζ}) :=
    IntermediateField.adjoin.finiteDimensional hint
  have hH : IsOpen (((IntermediateField.adjoin ℚ {ζ}).fixingSubgroup : Subgroup (Ω ≃ₐ[ℚ] Ω)) :
      Set (Ω ≃ₐ[ℚ] Ω)) := IntermediateField.fixingSubgroup_isOpen _
  refine continuous_iff_continuousAt.2 fun t => ?_
  have hU : IsOpen ((fun s : Ω ≃ₐ[ℚ] Ω => t⁻¹ * s) ⁻¹'
      (((IntermediateField.adjoin ℚ {ζ}).fixingSubgroup : Subgroup (Ω ≃ₐ[ℚ] Ω)) :
        Set (Ω ≃ₐ[ℚ] Ω))) := hH.preimage (continuous_mul_left _)
  have ht : t ∈ (fun s : Ω ≃ₐ[ℚ] Ω => t⁻¹ * s) ⁻¹'
      (((IntermediateField.adjoin ℚ {ζ}).fixingSubgroup : Subgroup (Ω ≃ₐ[ℚ] Ω)) :
        Set (Ω ≃ₐ[ℚ] Ω)) := by
    simp only [Set.mem_preimage, inv_mul_cancel, SetLike.mem_coe]
    exact Subgroup.one_mem _
  refine (continuousAt_const (y := f t)).congr ?_
  filter_upwards [hU.mem_nhds ht] with s hs
  have h1 : (t⁻¹ * s) ζ = ζ :=
    (IntermediateField.mem_fixingSubgroup_iff _ _).1 hs ζ
      (IntermediateField.mem_adjoin_simple_self ℚ ζ)
  have h2 : s ζ = t ζ := by
    have h3 := congrArg t h1
    rw [AlgEquiv.mul_apply] at h3
    simpa using h3
  exact (h s t h2).symm

/- English proof (translation)
Establish `hN : ¬ B.valuation (M : Ω) < 1` using `fun h => hv ((hB _).1 (by simpa using h))`. Use `eq_of_pow_eq_one B hN ?_ ?_ (hs ζ (valuation_eq_one_of_pow_eq_one B hM hζ).le)` and prove the remaining obligations. Rewrite using `[← map_pow, hζ, map_one]`. Rewrite using `[← pow_mul, mul_comm, pow_mul, hζ, one_pow]`.
-/
private theorem root_pow {M n : ℕ} (hM : M ≠ 0) {B : ValuationSubring Ω} {v : Pl} (hB : IsPlaceOver B v)
    (hv : ((M : ℕ) : 𝓞 ℚ) ∉ v.asIdeal) {s : G ℚ Ω} {ζ : Ω} (hζ : ζ ^ M = 1)
    (hs : ∀ x, B.valuation x ≤ 1 → B.valuation (s x - x ^ n) < 1) : s ζ = ζ ^ n := by
  have hN : ¬ B.valuation (M : Ω) < 1 := fun h => hv ((hB _).1 (by simpa using h))
  refine eq_of_pow_eq_one B hN ?_ ?_ (hs ζ (valuation_eq_one_of_pow_eq_one B hM hζ).le)
  · rw [← map_pow, hζ, map_one]
  · rw [← pow_mul, mul_comm, pow_mul, hζ, one_pow]

/- English proof (translation)
Establish `hu` using `hζ.isUnit (NeZero.ne M)`. Establish `h1 : IsPrimitiveRoot hu.unit M` using `IsPrimitiveRoot.coe_units_iff.mp (by simpa using hζ)`. Establish `h2 : hu.unit ^ a = hu.unit ^ b` using `Units.ext (by simpa using h)`. Rewrite `h2` using `[pow_eq_pow_iff_modEq, ← h1.eq_orderOf]`. Conclude with `(ZMod.natCast_eq_natCast_iff _ _ _).mpr h2`.
-/
private theorem expo_eq {M a b : ℕ} [NeZero M] {ζ : Ω} (hζ : IsPrimitiveRoot ζ M) (h : ζ ^ a = ζ ^ b) :
    (a : ZMod M) = b := by
  have hu := hζ.isUnit (NeZero.ne M)
  have h1 : IsPrimitiveRoot hu.unit M := IsPrimitiveRoot.coe_units_iff.mp (by simpa using hζ)
  have h2 : hu.unit ^ a = hu.unit ^ b := Units.ext (by simpa using h)
  rw [pow_eq_pow_iff_modEq, ← h1.eq_orderOf] at h2
  exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr h2

/- English proof (translation)
Establish `h0` using `congrArg (fun p => Polynomial.coeff p 0) h`. Simplify using `[Polynomial.coeff_map] at h0`. Rewrite using `[Matrix.det_eq_sign_charpoly_coeff]`. Simplify using `[h0]`.
-/
private theorem det_of_charpoly {K : Type} [Field K] (ι : K ≃+* ℂ) {A : Matrix (Fin 2) (Fin 2) K} {a d : ℂ}
    (h : A.charpoly.map ι.toRingHom = X ^ 2 - C a * X + C d) : ι A.det = d := by
  have h0 := congrArg (fun p => Polynomial.coeff p 0) h
  simp [Polynomial.coeff_map] at h0
  rw [Matrix.det_eq_sign_charpoly_coeff]
  simp [h0]

end

/- English proof (translation)
Introduce `l _ Ω _ _ _ ι e S A W g χ hN hK hl hAtt s hs`. Establish `hM : g.M ≠ 0` using `g.pos.ne'`. Use `haveI : NeZero g.M := ⟨hM⟩`. Establish `hl0 : l ≠ 0` using `(Fact.out : l.Prime).ne_zero`. Use `haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ`.

Use `haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective`. Use `haveI : NeZero ((g.M : ℕ) : Ω) := ⟨Nat.cast_ne_zero.2 hM⟩`. Use `haveI : NeZero ((l : ℕ) : Ω) := ⟨Nat.cast_ne_zero.2 hl0⟩`. Take `⟨ζ, hζ⟩` from `HasEnoughRootsOfUnity.exists_primitiveRoot Ω g.M`. Take `⟨η, hη⟩` from `HasEnoughRootsOfUnity.exists_primitiveRoot Ω l`.

Set `F : Ω → Qbar l` to `fun x => ι.symm (g.χ ((Classical.epsilon (fun k : ℕ => ζ ^ k = x) : ℕ) : ZMod g.M))`. Establish `hF : ∀ k : ℕ, F (ζ ^ k) = ι.symm (g.χ k)`. Introduce `k`. Establish `h1 : ζ ^ (Classical.epsilon (fun j : ℕ => ζ ^ j = ζ ^ k)) = ζ ^ k` using `Classical.epsilon_spec (p := fun j : ℕ => ζ ^ j = ζ ^ k) ⟨k, rfl⟩`. Use `show ι.symm (g.χ _) = _`.

Rewrite using `[expo_eq hζ h1]`. Set `f : G ℚ Ω → Qbar l` to `fun t => ((dt W t * (χ t)⁻¹ ^ 2 : (Qbar l)ˣ) : Qbar l)`. Establish `hf'c : Continuous (fun t : G ℚ Ω => F (t ζ))` using `cont_of_apply ζ _ (fun a b h => by simp only [h])`. Establish `hcop : ∀ w : Pl, ((l : ℕ) : 𝓞 ℚ) ∈ w.asIdeal → ((g.M : ℕ) : 𝓞 ℚ) ∉ w.asIdeal`. Introduce `w hlw hmem`.

Take `⟨a, b, hab⟩ : IsCoprime (l : ℤ) (g.M : ℤ)` from `Nat.isCoprime_iff_coprime.2 ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hl)`. Apply `w.isPrime.ne_top` to reduce the goal to its premises. Rewrite using `[Ideal.eq_top_iff_one]`. Establish `h2 : (a : 𝓞 ℚ) * (l : 𝓞 ℚ) + (b : 𝓞 ℚ) * (g.M : 𝓞 ℚ) = 1`. Conclude with `congrArg (Int.cast : ℤ → 𝓞 ℚ) hab` after adjusting the coercions.

Rewrite using `[← h2]`. Conclude with `Ideal.add_mem _ (Ideal.mul_mem_left _ _ hlw) (Ideal.mul_mem_left _ _ hmem)`. Establish `key : f = fun t => F (t ζ)`. Establish `hχc : Continuous (fun t : G ℚ Ω => (((χ t)⁻¹ ^ 2 : (Qbar l)ˣ) : Qbar l))`. Use `cont_of_apply η _ (fun a b hab => ?_)` and prove the remaining obligations.

Establish `h0 : χ (b⁻¹ * a) = 1` using `hK (b⁻¹ * a) (fun x hx => by`. Take `⟨i, -, rfl⟩` from `hη.eq_pow_of_pow_eq_one hx`. Rewrite using `[map_pow]`. Simplify using `[AlgEquiv.mul_apply, hab])`. Rewrite `h0` using `[map_mul, map_inv, inv_mul_eq_one]`.

Rewrite using `[h0]`. Establish `hdt : ∀ t, ((W t : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l)).det = ((dt W t : (Qbar l)ˣ) : Qbar l)` using `fun t => rfl`. Establish `hdc : Continuous (fun t : G ℚ Ω => ((dt W t : (Qbar l)ˣ) : Qbar l))`. Simplify using `only [← hdt]`. Conclude with `(Units.continuous_val.comp hN.cont).matrix_det`.

Establish `hfc : Continuous f`. Establish `h3 : f = fun t => ((dt W t : (Qbar l)ˣ) : Qbar l) * (((χ t)⁻¹ ^ 2 : (Qbar l)ˣ) : Qbar l)`. Use function extensionality and compare the values at `t`. Simplify using `only [f, Units.val_mul]`. Rewrite using `[h3]`.

Conclude with `hdc.mul hχc`. Establish `hbad` using `Filter.eventually_cofinite.1 hAtt.2`. Establish `hI : Ideal.span {((g.M * l : ℕ) : 𝓞 ℚ)} ≠ 0`. Rewrite using `[Ideal.zero_eq_bot, Ne, Ideal.span_singleton_eq_bot]`. Conclude with `Nat.cast_ne_zero.2 (mul_ne_zero hM hl0)`.

Use `GlobalTheory.Published.ChebotarevDegreeOne.eq_of_frob GlobalTheory.Published.chebotarevDegreeOne' (hbad.union (Ideal.finite_factors hI)) hfc hf'c ?_` and prove the remaining obligations. Introduce `w hw _ B hB σ hσ`. Simplify using `only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hw`. Take `⟨hP, hdiv⟩` from `hw`. Establish `hlw : ((l : ℕ) : 𝓞 ℚ) ∉ w.asIdeal`.

Introduce `h4`. Apply `hdiv` to reduce the goal to its premises. Rewrite using `[Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem, Nat.cast_mul]`. Conclude with `Ideal.mul_mem_left _ _ h4`. Establish `hMw : ((g.M : ℕ) : 𝓞 ℚ) ∉ w.asIdeal`.

Introduce `h4`. Apply `hdiv` to reduce the goal to its premises. Rewrite using `[Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem, Nat.cast_mul]`. Conclude with `Ideal.mul_mem_right _ _ h4`. Establish `hσζ : σ ζ = ζ ^ normV w` using `root_pow hM hB hMw hζ.pow_eq_one hσ.2`.

Use `show f σ = F (σ ζ)`. Rewrite using `[hσζ, hF]`. Establish `hch` using `(hP B hB).2 σ hσ`. Rewrite `hch` using `[Newform.heckePoly]`. Establish `hdet` using `det_of_charpoly ι hch`.

Establish `hcyc : ((cycBar ℚ Ω l σ : (Qbar l)ˣ) : Qbar l) = (normV w : Qbar l)`. Establish `h5` using `cycZ_of_isFrob hlw hB hσ`. Simplify using `[cycBar, h5]`. Rewrite `hdet` using `[tw_val, Matrix.det_smul, Fintype.card_fin, hdt]`. Simplify using `[map_inv, hcyc] at hdet`.

Establish `hd0 : ι ((dt W σ : (Qbar l)ˣ) : Qbar l) ≠ 0` using `(map_ne_zero ι).2 (Units.ne_zero _)`. Establish `hx0 : ι ((χ σ : (Qbar l)ˣ) : Qbar l) ≠ 0` using `(map_ne_zero ι).2 (Units.ne_zero _)`. Establish `hn0 : (normV w : ℂ) ≠ 0`. Establish `h6 : (normV w : Qbar l) ≠ 0` using `hcyc ▸ Units.ne_zero _`. Conclude with `(Nat.cast_ne_zero.1 h6)` after adjusting the coercions.

Apply `ι.injective` to reduce the goal to its premises. Rewrite using `[RingEquiv.apply_symm_apply]`. Simplify using `only [f]`. Simplify using `[map_inv]`. Apply `mul_right_cancel₀ (pow_ne_zero (2 * e) hn0)` to reduce the goal to its premises.

Rewrite using `[← hdet]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Take `⟨v, hv, hlv⟩` from `hN.atL`. Establish `hs' : s ∈ Inertia A` using `hs`.

Establish `hsζ : s ζ = ζ ^ 1` using `root_pow hM hv (hcop v hlv) hζ.pow_eq_one (fun x hx => by simpa using hs'.2 x hx)`. Establish `h1` using `congrFun key s`. Simplify using `only [f, hsζ, hF, Nat.cast_one, map_one, Units.val_eq_one] at h1`. Rewrite `h1` using `[inv_pow, mul_inv_eq_one]`. Conclude with `h1`.
-/
theorem UpperTheory.V.Z.Kato.Joint.detIne :
    UpperTheory.V.Z.Kato.Joint.DetIne := by
  intro l _ Ω _ _ _ ι e S A W g χ hN hK hl hAtt s hs
  have hM : g.M ≠ 0 := g.pos.ne'
  haveI : NeZero g.M := ⟨hM⟩
  have hl0 : l ≠ 0 := (Fact.out : l.Prime).ne_zero
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  haveI : NeZero ((g.M : ℕ) : Ω) := ⟨Nat.cast_ne_zero.2 hM⟩
  haveI : NeZero ((l : ℕ) : Ω) := ⟨Nat.cast_ne_zero.2 hl0⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω g.M
  obtain ⟨η, hη⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω l
  let F : Ω → Qbar l := fun x =>
    ι.symm (g.χ ((Classical.epsilon (fun k : ℕ => ζ ^ k = x) : ℕ) : ZMod g.M))
  have hF : ∀ k : ℕ, F (ζ ^ k) = ι.symm (g.χ k) := by
    intro k
    have h1 : ζ ^ (Classical.epsilon (fun j : ℕ => ζ ^ j = ζ ^ k)) = ζ ^ k :=
      Classical.epsilon_spec (p := fun j : ℕ => ζ ^ j = ζ ^ k) ⟨k, rfl⟩
    show ι.symm (g.χ _) = _
    rw [expo_eq hζ h1]
  let f : G ℚ Ω → Qbar l := fun t => ((dt W t * (χ t)⁻¹ ^ 2 : (Qbar l)ˣ) : Qbar l)
  have hf'c : Continuous (fun t : G ℚ Ω => F (t ζ)) :=
    cont_of_apply ζ _ (fun a b h => by simp only [h])
  have hcop : ∀ w : Pl, ((l : ℕ) : 𝓞 ℚ) ∈ w.asIdeal → ((g.M : ℕ) : 𝓞 ℚ) ∉ w.asIdeal := by
    intro w hlw hmem
    obtain ⟨a, b, hab⟩ : IsCoprime (l : ℤ) (g.M : ℤ) :=
      Nat.isCoprime_iff_coprime.2 ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hl)
    apply w.isPrime.ne_top
    rw [Ideal.eq_top_iff_one]
    have h2 : (a : 𝓞 ℚ) * (l : 𝓞 ℚ) + (b : 𝓞 ℚ) * (g.M : 𝓞 ℚ) = 1 := by
      exact_mod_cast congrArg (Int.cast : ℤ → 𝓞 ℚ) hab
    rw [← h2]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hlw) (Ideal.mul_mem_left _ _ hmem)
  have key : f = fun t => F (t ζ) := by
    have hχc : Continuous (fun t : G ℚ Ω => (((χ t)⁻¹ ^ 2 : (Qbar l)ˣ) : Qbar l)) := by
      refine cont_of_apply η _ (fun a b hab => ?_)
      have h0 : χ (b⁻¹ * a) = 1 := hK (b⁻¹ * a) (fun x hx => by
        obtain ⟨i, -, rfl⟩ := hη.eq_pow_of_pow_eq_one hx
        rw [map_pow]
        simp [AlgEquiv.mul_apply, hab])
      rw [map_mul, map_inv, inv_mul_eq_one] at h0
      rw [h0]
    have hdt : ∀ t, ((W t : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l)).det =
        ((dt W t : (Qbar l)ˣ) : Qbar l) := fun t => rfl
    have hdc : Continuous (fun t : G ℚ Ω => ((dt W t : (Qbar l)ˣ) : Qbar l)) := by
      simp only [← hdt]
      exact (Units.continuous_val.comp hN.cont).matrix_det
    have hfc : Continuous f := by
      have h3 : f = fun t => ((dt W t : (Qbar l)ˣ) : Qbar l) *
          (((χ t)⁻¹ ^ 2 : (Qbar l)ˣ) : Qbar l) := by
        funext t
        simp only [f, Units.val_mul]
      rw [h3]
      exact hdc.mul hχc
    have hbad := Filter.eventually_cofinite.1 hAtt.2
    have hI : Ideal.span {((g.M * l : ℕ) : 𝓞 ℚ)} ≠ 0 := by
      rw [Ideal.zero_eq_bot, Ne, Ideal.span_singleton_eq_bot]
      exact Nat.cast_ne_zero.2 (mul_ne_zero hM hl0)
    refine GlobalTheory.Published.ChebotarevDegreeOne.eq_of_frob GlobalTheory.Published.chebotarevDegreeOne'
      (hbad.union (Ideal.finite_factors hI)) hfc hf'c ?_
    intro w hw _ B hB σ hσ
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hw
    obtain ⟨hP, hdiv⟩ := hw
    have hlw : ((l : ℕ) : 𝓞 ℚ) ∉ w.asIdeal := by
      intro h4
      apply hdiv
      rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem, Nat.cast_mul]
      exact Ideal.mul_mem_left _ _ h4
    have hMw : ((g.M : ℕ) : 𝓞 ℚ) ∉ w.asIdeal := by
      intro h4
      apply hdiv
      rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem, Nat.cast_mul]
      exact Ideal.mul_mem_right _ _ h4
    have hσζ : σ ζ = ζ ^ normV w := root_pow hM hB hMw hζ.pow_eq_one hσ.2
    show f σ = F (σ ζ)
    rw [hσζ, hF]
    have hch := (hP B hB).2 σ hσ
    rw [Newform.heckePoly] at hch
    have hdet := det_of_charpoly ι hch
    have hcyc : ((cycBar ℚ Ω l σ : (Qbar l)ˣ) : Qbar l) = (normV w : Qbar l) := by
      have h5 := cycZ_of_isFrob hlw hB hσ
      simp [cycBar, h5]
    rw [tw_val, Matrix.det_smul, Fintype.card_fin, hdt] at hdet
    simp [map_inv, hcyc] at hdet
    have hd0 : ι ((dt W σ : (Qbar l)ˣ) : Qbar l) ≠ 0 := (map_ne_zero ι).2 (Units.ne_zero _)
    have hx0 : ι ((χ σ : (Qbar l)ˣ) : Qbar l) ≠ 0 := (map_ne_zero ι).2 (Units.ne_zero _)
    have hn0 : (normV w : ℂ) ≠ 0 := by
      have h6 : (normV w : Qbar l) ≠ 0 := hcyc ▸ Units.ne_zero _
      exact_mod_cast (Nat.cast_ne_zero.1 h6)
    apply ι.injective
    rw [RingEquiv.apply_symm_apply]
    simp only [f]
    simp [map_inv]
    apply mul_right_cancel₀ (pow_ne_zero (2 * e) hn0)
    rw [← hdet]
    field_simp
    ring
  obtain ⟨v, hv, hlv⟩ := hN.atL
  have hs' : s ∈ Inertia A := hs
  have hsζ : s ζ = ζ ^ 1 :=
    root_pow hM hv (hcop v hlv) hζ.pow_eq_one (fun x hx => by simpa using hs'.2 x hx)
  have h1 := congrFun key s
  simp only [f, hsζ, hF, Nat.cast_one, map_one, Units.val_eq_one] at h1
  rw [inv_pow, mul_inv_eq_one] at h1
  exact h1
