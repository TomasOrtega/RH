import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.ChiQuadAlt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChebotarevDegreeOne

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ
open UpperTheory.V.Z.Kato.Joint Polynomial

section

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω]

/- English proof (translation)
Establish `halg : Algebra.IsAlgebraic ℚ Ω` using `IsAlgClosure.isAlgebraic`. Establish `hint : IsIntegral ℚ ζ` using `(Algebra.IsAlgebraic.isAlgebraic ζ).isIntegral`. Use `haveI : FiniteDimensional ℚ (IntermediateField.adjoin ℚ {ζ}) := IntermediateField.adjoin.finiteDimensional hint`. Establish `hopen : IsOpen ((IntermediateField.adjoin ℚ {ζ}).fixingSubgroup : Set (Ω ≃ₐ[ℚ] Ω))` using `IntermediateField.fixingSubgroup_isOpen _`. Apply `IsLocallyConstant.continuous` to reduce the goal to its premises.

Rewrite using `[IsLocallyConstant.iff_eventually_eq]`. Introduce `s`. Establish `hc : Continuous fun y : Ω ≃ₐ[ℚ] Ω => s⁻¹ * y` using `continuous_const.mul continuous_id`. Establish `hmem : s⁻¹ * s ∈ ((IntermediateField.adjoin ℚ {ζ}).fixingSubgroup : Set (Ω ≃ₐ[ℚ] Ω))`. Simplify using `only [inv_mul_cancel]`.

Conclude with `Subgroup.one_mem _`. Use `filter_upwards [hc.continuousAt.preimage_mem_nhds (hopen.mem_nhds hmem)] with y hy`. Apply `h` to reduce the goal to its premises. Establish `hz : (s⁻¹ * y) ζ = ζ`. Use `(IntermediateField.mem_fixingSubgroup_iff _ _).mp hy ζ (IntermediateField.mem_adjoin_simple_self ℚ ζ)` as an intermediate fact.

Conclude with `this`. Establish `: s ((s⁻¹ * y) ζ) = s ζ` using `by rw [hz]`. Simplify using `using this`.
-/
private theorem cont_of_apply [IsAlgClosure ℚ Ω] {Y : Type} [TopologicalSpace Y] (ζ : Ω) (f : G ℚ Ω → Y)
    (h : ∀ s t : G ℚ Ω, s ζ = t ζ → f s = f t) : Continuous f := by
  have halg : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  have hint : IsIntegral ℚ ζ := (Algebra.IsAlgebraic.isAlgebraic ζ).isIntegral
  haveI : FiniteDimensional ℚ (IntermediateField.adjoin ℚ {ζ}) := IntermediateField.adjoin.finiteDimensional hint
  have hopen : IsOpen ((IntermediateField.adjoin ℚ {ζ}).fixingSubgroup : Set (Ω ≃ₐ[ℚ] Ω)) :=
    IntermediateField.fixingSubgroup_isOpen _
  apply IsLocallyConstant.continuous
  rw [IsLocallyConstant.iff_eventually_eq]
  intro s
  have hc : Continuous fun y : Ω ≃ₐ[ℚ] Ω => s⁻¹ * y := continuous_const.mul continuous_id
  have hmem : s⁻¹ * s ∈ ((IntermediateField.adjoin ℚ {ζ}).fixingSubgroup : Set (Ω ≃ₐ[ℚ] Ω)) := by
    simp only [inv_mul_cancel]
    exact Subgroup.one_mem _
  filter_upwards [hc.continuousAt.preimage_mem_nhds (hopen.mem_nhds hmem)] with y hy
  apply h
  have hz : (s⁻¹ * y) ζ = ζ := by
    have := (IntermediateField.mem_fixingSubgroup_iff _ _).mp hy ζ (IntermediateField.mem_adjoin_simple_self ℚ ζ)
    exact this
  have : s ((s⁻¹ * y) ζ) = s ζ := by rw [hz]
  simpa using this

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
Take `⟨u, rfl⟩` from `hζ.isUnit (NeZero.ne M)`. Rewrite using `[ZMod.natCast_eq_natCast_iff, hζ.eq_orderOf, orderOf_units]`. Apply `pow_eq_pow_iff_modEq.mp` to reduce the goal to its premises. Conclude with `Units.ext (by simpa using h)`.
-/
private theorem expo_eq {M a b : ℕ} [NeZero M] {ζ : Ω} (hζ : IsPrimitiveRoot ζ M) (h : ζ ^ a = ζ ^ b) :
    (a : ZMod M) = b := by
  obtain ⟨u, rfl⟩ := hζ.isUnit (NeZero.ne M)
  rw [ZMod.natCast_eq_natCast_iff, hζ.eq_orderOf, orderOf_units]
  apply pow_eq_pow_iff_modEq.mp
  exact Units.ext (by simpa using h)

/- English proof (translation)
Establish `h0` using `congrArg (fun p => Polynomial.coeff p 0) h`. Simplify using `only [Polynomial.coeff_map] at h0`. Rewrite using `[Matrix.det_eq_sign_charpoly_coeff]`. Simplify using `at h0 ⊢`. Conclude with `h0`.
-/
private theorem det_of_charpoly {K : Type} [Field K] (ι : K ≃+* ℂ) {A : Matrix (Fin 2) (Fin 2) K} {a d : ℂ}
    (h : A.charpoly.map ι.toRingHom = X ^ 2 - C a * X + C d) : ι A.det = d := by
  have h0 := congrArg (fun p => Polynomial.coeff p 0) h
  simp only [Polynomial.coeff_map] at h0
  rw [Matrix.det_eq_sign_charpoly_coeff]
  simp at h0 ⊢
  exact h0

/- English proof (translation)
Use `haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ`. Use `haveI : CharZero Ω := (RingHom.charZero_iff (algebraMap ℚ Ω).injective).mp inferInstance`. Use `haveI : NeZero (n : Ω) := ⟨Nat.cast_ne_zero.mpr hn⟩`. Use `haveI : NeZero n := ⟨hn⟩`. Establish `hpos : 0 < n` using `Nat.pos_of_ne_zero hn`.

Take `⟨ζ, hζ⟩` from `IsAlgClosed.exists_root (Polynomial.cyclotomic n Ω) (by`. Rewrite using `[Polynomial.degree_cyclotomic]`. Conclude with `(Nat.totient_pos.mpr hpos).ne')` after adjusting the coercions. Establish `hprim : IsPrimitiveRoot ζ n` using `Polynomial.isRoot_cyclotomic_iff.mp hζ`. Establish `hprim' : IsPrimitiveRoot (ζ ^ c) n` using `hprim.pow_of_coprime c hc`.

Establish `hev : ∀ μ : Ω, IsPrimitiveRoot μ n → Polynomial.aeval μ (Polynomial.cyclotomic n ℚ) = 0`. Introduce `μ hμ`. Rewrite using `[Polynomial.aeval_def, ← Polynomial.eval_map, Polynomial.map_cyclotomic]`. Conclude with `hμ.isRoot_cyclotomic hpos`. Establish `hmin : Polynomial.cyclotomic n ℚ = minpoly ℚ ζ` using `minpoly.eq_of_irreducible_of_monic (Polynomial.cyclotomic.irreducible_rat hpos) (hev ζ hprim) (Polynomial.cyclotomic.monic n ℚ)`.

Establish `halg : IsAlgebraic ℚ ζ` using `⟨_, Polynomial.cyclotomic_ne_zero n ℚ, hev ζ hprim⟩`. Establish `hroot : Polynomial.aeval (ζ ^ c) (minpoly ℚ ζ) = 0`. Rewrite using `[← hmin]`. Conclude with `hev _ hprim'`. Take `⟨s, hs⟩` from `minpoly.exists_algEquiv_of_root' halg hroot`.

Use `⟨s, fun z hz => ?_⟩` and prove the remaining obligations. Take `⟨i, -, rfl⟩` from `hprim.eq_pow_of_pow_eq_one hz`. Rewrite using `[map_pow, hs, ← pow_mul, ← pow_mul, mul_comm]`.
-/
private theorem exists_aut_pow [IsAlgClosure ℚ Ω] {n c : ℕ} (hn : n ≠ 0) (hc : c.Coprime n) :
    ∃ s : G ℚ Ω, ∀ z : Ω, z ^ n = 1 → s z = z ^ c := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := (RingHom.charZero_iff (algebraMap ℚ Ω).injective).mp inferInstance
  haveI : NeZero (n : Ω) := ⟨Nat.cast_ne_zero.mpr hn⟩
  haveI : NeZero n := ⟨hn⟩
  have hpos : 0 < n := Nat.pos_of_ne_zero hn
  obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic n Ω) (by
    rw [Polynomial.degree_cyclotomic]
    exact_mod_cast (Nat.totient_pos.mpr hpos).ne')
  have hprim : IsPrimitiveRoot ζ n := Polynomial.isRoot_cyclotomic_iff.mp hζ
  have hprim' : IsPrimitiveRoot (ζ ^ c) n := hprim.pow_of_coprime c hc
  have hev : ∀ μ : Ω, IsPrimitiveRoot μ n → Polynomial.aeval μ (Polynomial.cyclotomic n ℚ) = 0 := by
    intro μ hμ
    rw [Polynomial.aeval_def, ← Polynomial.eval_map, Polynomial.map_cyclotomic]
    exact hμ.isRoot_cyclotomic hpos
  have hmin : Polynomial.cyclotomic n ℚ = minpoly ℚ ζ :=
    minpoly.eq_of_irreducible_of_monic (Polynomial.cyclotomic.irreducible_rat hpos) (hev ζ hprim)
      (Polynomial.cyclotomic.monic n ℚ)
  have halg : IsAlgebraic ℚ ζ := ⟨_, Polynomial.cyclotomic_ne_zero n ℚ, hev ζ hprim⟩
  have hroot : Polynomial.aeval (ζ ^ c) (minpoly ℚ ζ) = 0 := by
    rw [← hmin]
    exact hev _ hprim'
  obtain ⟨s, hs⟩ := minpoly.exists_algEquiv_of_root' halg hroot
  refine ⟨s, fun z hz => ?_⟩
  obtain ⟨i, -, rfl⟩ := hprim.eq_pow_of_pow_eq_one hz
  rw [map_pow, hs, ← pow_mul, ← pow_mul, mul_comm]

end

/- English proof (translation)
Unfold `UpperTheory.V.Z.Kato.Joint.ChiQuad`. Introduce `l _ Ω _ _ _ ι e S A W g χ hN hK hl hAtt d hd`. Establish `hlp : Nat.Prime l` using `Fact.out`. Establish `hM0 : g.M ≠ 0` using `g.pos.ne'`. Establish `hN0 : l * g.M ≠ 0` using `mul_ne_zero hlp.ne_zero hM0`.

Use `haveI : NeZero g.M := ⟨hM0⟩`. Use `haveI : NeZero (l * g.M) := ⟨hN0⟩`. Take `⟨ζ, hζ⟩ : ∃ ζ : Ω, IsPrimitiveRoot ζ (l * g.M)` from `by haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ haveI : CharZero Ω := (RingHom.charZero_iff (algebraMap ℚ Ω).injective).mp inferInstance`. Take `⟨z, hz⟩` from `IsAlgClosed.exists_root (Polynomial.cyclotomic (l * g.M) Ω) (by`. Rewrite using `[Polynomial.degree_cyclotomic]`.

Conclude with `(Nat.totient_pos.mpr (Nat.pos_of_ne_zero hN0)).ne')` after adjusting the coercions. Conclude with `⟨z, Polynomial.isRoot_cyclotomic_iff.mp hz⟩`. Establish `hζM : IsPrimitiveRoot (ζ ^ l) g.M` using `hζ.pow (Nat.pos_of_ne_zero hN0) rfl`. Establish `hζMN : (ζ ^ l) ^ (l * g.M) = 1`. Rewrite using `[← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]`.

Establish `hroot : ∀ s : G ℚ Ω, ∃ i : ℕ, s (ζ ^ l) = (ζ ^ l) ^ i`. Introduce `s`. Establish `h1 : (s (ζ ^ l)) ^ g.M = 1` using `by rw [← map_pow, hζM.pow_eq_one, map_one]`. Take `⟨i, -, hi⟩` from `hζM.eq_pow_of_pow_eq_one h1`. Conclude with `⟨i, hi.symm⟩`.

Use `choose u hu using hroot`. Establish `hsame : ∀ s t : G ℚ Ω, s ζ = t ζ → ∀ z : Ω, z ^ (l * g.M) = 1 → s z = t z`. Introduce `s t hst z hz`. Take `⟨i, -, rfl⟩` from `hζ.eq_pow_of_pow_eq_one hz`. Rewrite using `[map_pow, map_pow, hst]`.

Establish `hχ : ∀ s t : G ℚ Ω, s ζ = t ζ → χ s = χ t`. Introduce `s t hst`. Establish `h1 : χ (t⁻¹ * s) = 1`. Apply `hK` to reduce the goal to its premises. Introduce `z hz`.

Establish `h2` using `hsame s t hst z (by rw [pow_mul, hz, one_pow])`. Rewrite using `[AlgEquiv.mul_apply, h2]`. Conclude with `t.symm_apply_apply z`. Rewrite `h1` using `[map_mul, map_inv, inv_mul_eq_one]`. Conclude with `h1.symm`.

Establish `hu_eq : ∀ s t : G ℚ Ω, s ζ = t ζ → (u s : ZMod g.M) = u t`. Introduce `s t hst`. Apply `expo_eq hζM` to reduce the goal to its premises. Rewrite using `[← hu, ← hu]`. Conclude with `hsame s t hst _ hζMN`.

Set `f : G ℚ Ω → ℂ` to `fun s => ι (χ s : Qbar l) ^ 4 * g.χ (u s : ZMod g.M) ^ 2`. Establish `hf : Continuous f` using `cont_of_apply ζ f (fun s t h => by simp only [f, hχ s t h, hu_eq s t h])`. Establish `hcof : ∀ᶠ w : Pl in Filter.cofinite, ((l * g.M : ℕ) : 𝓞 ℚ) ∉ w.asIdeal`. Rewrite using `[Filter.eventually_cofinite]`. Use `(Ideal.finite_factors (I := Ideal.span {((l * g.M : ℕ) : 𝓞 ℚ)}) ?_).subset ?_` and prove the remaining obligations.

Rewrite using `[Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]`. Conclude with `hN0` after adjusting the coercions. Introduce `w hw`. Simplify using `only [Set.mem_setOf_eq, not_not] at hw ⊢`. Conclude with `Ideal.dvd_span_singleton.mpr hw`.

Establish `hev` using `hcof.and hAtt.2`. Establish `hfeq : f = fun _ => 1`. Use `GlobalTheory.Published.ChebotarevDegreeOne.eq_of_frob GlobalTheory.Published.chebotarevDegreeOne' (Filter.eventually_cofinite.mp hev) hf continuous_const ?_` and prove the remaining obligations. Introduce `v hv _ B hB σ hσ`. Take `⟨hvN, hvA⟩` from `not_not.mp hv`.

Establish `hvM : ((g.M : ℕ) : 𝓞 ℚ) ∉ v.asIdeal` using `fun h => hvN (by push_cast; exact Ideal.mul_mem_left _ _ h)`. Establish `hvl : ((l : ℕ) : 𝓞 ℚ) ∉ v.asIdeal` using `fun h => hvN (by push_cast; exact Ideal.mul_mem_right _ _ h)`. Establish `hcp` using `(hvA B hB).2 σ hσ`. Establish `hdet` using `det_of_charpoly (a := g.a (normV v)) (d := g.χ (normV v) * (normV v : ℂ) ^ (2 * e + 1 - 1)) ι hcp`. Establish `hfr : σ (ζ ^ l) = (ζ ^ l) ^ normV v` using `root_pow hM0 hB hvM hζM.pow_eq_one hσ.2`.

Establish `hus : (u σ : ZMod g.M) = normV v` using `expo_eq hζM (by rw [← hu, hfr])`. Establish `hcz` using `cycZ_of_isFrob hvl hB hσ`. Establish `hcyc : ((cycBar ℚ Ω l σ : (Qbar l)ˣ) : Qbar l) = (normV v : Qbar l)`. Simplify using `[cycBar, hcz]`. Establish `hd2 : (dt W σ) ^ 2 = 1`.

Use `congrArg (fun φ => φ σ) hN.det2` as an intermediate fact. Simplify using `using this`. Rewrite `hdet` using `[tw_val, Matrix.det_smul]`. Simplify using `only [Fintype.card_fin, map_inv, MonoidHom.mul_apply, MonoidHom.inv_apply, MonoidHom.zpow_apply] at hdet`. Establish `hw : ((↑((W σ)⁻¹) : Matrix (Fin 2) (Fin 2) (Qbar l))).det = (((dt W σ)⁻¹ : (Qbar l)ˣ) : Qbar l)`.

Express the relevant statement in the definitionally equal form `((Matrix.GeneralLinearGroup.det ((W σ)⁻¹) : (Qbar l)ˣ) : Qbar l) = _`. Rewrite using `[map_inv]`. Both sides reduce to the same expression. Rewrite `hdet` using `[hw]`. Simplify using `only [mul_inv_rev, inv_inv, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_zpow_eq_zpow_val, Units.val_inv_eq_inv_val, map_mul, map_pow, map_inv₀, map_zpow₀, hcyc, map_natCast] at hdet`.

Use `set a := ι ((χ σ : (Qbar l)ˣ) : Qbar l) with ha_def`. Use `set δ := ι ((dt W σ : (Qbar l)ˣ) : Qbar l) with hδ_def`. Establish `ha : a ≠ 0` using `(map_ne_zero ι).mpr (χ σ).ne_zero`. Establish `hδ : δ ^ 2 = 1`. Use `congrArg (fun x : (Qbar l)ˣ => ι (x : Qbar l)) hd2` as an intermediate fact.

Simplify `this` using `[hδ_def]`. Establish `hδ0 : δ ≠ 0` using `(map_ne_zero ι).mpr (dt W σ).ne_zero`. Establish `hp : ((normV v : ℕ) : ℂ) ≠ 0`. Establish `h1 : ι ((cycBar ℚ Ω l σ : (Qbar l)ˣ) : Qbar l) ≠ 0` using `(map_ne_zero ι).mpr (cycBar ℚ Ω l σ).ne_zero`. Rewrite `h1` using `[hcyc, map_natCast]`. Then use the resulting hypothesis.

Rewrite `hdet` using `[Nat.add_sub_cancel, zpow_neg, inv_inv, zpow_natCast]`. Establish `hχp : g.χ (normV v : ZMod g.M) = δ * a⁻¹ ^ 2`. Apply `mul_right_cancel₀ (pow_ne_zero (2 * e) hp)` to reduce the goal to its premises. Rewrite using `[← hdet]`. Clear the denominators using the available nonvanishing facts.

Apply the tactic sequence `try ring`. Use `show a ^ 4 * g.χ (u σ : ZMod g.M) ^ 2 = 1`. Rewrite using `[hus, hχp, mul_pow, hδ]`. Clear the denominators using the available nonvanishing facts. Apply the tactic sequence `try ring`.

Take `⟨c, hc1, hcd⟩` from `Nat.chineseRemainder ((Nat.Prime.coprime_iff_not_dvd hlp).mpr hl) 1 d`. Establish `hcop : c.Coprime (l * g.M)`. Apply `Nat.Coprime.mul_right` to reduce the goal to its premises. Use `hc1.gcd_eq` as an intermediate fact. Rewrite `this` using `[Nat.gcd_one_left]`.

Conclude with `this`. Use `hcd.gcd_eq show c.gcd g.M = 1` as an intermediate fact. Rewrite using `[this]`. Conclude with `hd`. Take `⟨s, hs⟩` from `exists_aut_pow (Ω := Ω) hN0 hcop`.

Establish `hχs : χ s = 1`. Apply `hK` to reduce the goal to its premises. Introduce `z hz`. Rewrite using `[hs z (by rw [pow_mul, hz, one_pow])]`. Rewrite using `[← Nat.div_add_mod c l, pow_add, pow_mul, hz, one_pow, one_mul, show c % l = 1 % l from hc1, Nat.mod_eq_of_lt hlp.one_lt, pow_one]`.

Establish `hus : (u s : ZMod g.M) = d` using `(expo_eq hζM ((hu s).symm.trans (hs _ hζMN))).trans ((ZMod.natCast_eq_natCast_iff _ _ _).mpr hcd)`. Establish `h1` using `congrFun hfeq s`. Simplify using `only [f, hχs, hus, Units.val_one, map_one, one_pow, one_mul] at h1`. Rewrite `h1` using `[sq]`. Conclude with `mul_self_eq_one_iff.mp h1`.
-/
theorem UpperTheory.V.Z.Kato.Joint.chiQuad :
    UpperTheory.V.Z.Kato.Joint.ChiQuad := by
  unfold UpperTheory.V.Z.Kato.Joint.ChiQuad
  intro l _ Ω _ _ _ ι e S A W g χ hN hK hl hAtt d hd
  have hlp : Nat.Prime l := Fact.out
  have hM0 : g.M ≠ 0 := g.pos.ne'
  have hN0 : l * g.M ≠ 0 := mul_ne_zero hlp.ne_zero hM0
  haveI : NeZero g.M := ⟨hM0⟩
  haveI : NeZero (l * g.M) := ⟨hN0⟩
  obtain ⟨ζ, hζ⟩ : ∃ ζ : Ω, IsPrimitiveRoot ζ (l * g.M) := by
    haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
    haveI : CharZero Ω := (RingHom.charZero_iff (algebraMap ℚ Ω).injective).mp inferInstance
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic (l * g.M) Ω) (by
      rw [Polynomial.degree_cyclotomic]
      exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hN0)).ne')
    exact ⟨z, Polynomial.isRoot_cyclotomic_iff.mp hz⟩
  have hζM : IsPrimitiveRoot (ζ ^ l) g.M := hζ.pow (Nat.pos_of_ne_zero hN0) rfl
  have hζMN : (ζ ^ l) ^ (l * g.M) = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  have hroot : ∀ s : G ℚ Ω, ∃ i : ℕ, s (ζ ^ l) = (ζ ^ l) ^ i := by
    intro s
    have h1 : (s (ζ ^ l)) ^ g.M = 1 := by rw [← map_pow, hζM.pow_eq_one, map_one]
    obtain ⟨i, -, hi⟩ := hζM.eq_pow_of_pow_eq_one h1
    exact ⟨i, hi.symm⟩
  choose u hu using hroot
  have hsame : ∀ s t : G ℚ Ω, s ζ = t ζ → ∀ z : Ω, z ^ (l * g.M) = 1 → s z = t z := by
    intro s t hst z hz
    obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hz
    rw [map_pow, map_pow, hst]
  have hχ : ∀ s t : G ℚ Ω, s ζ = t ζ → χ s = χ t := by
    intro s t hst
    have h1 : χ (t⁻¹ * s) = 1 := by
      apply hK
      intro z hz
      have h2 := hsame s t hst z (by rw [pow_mul, hz, one_pow])
      rw [AlgEquiv.mul_apply, h2]
      exact t.symm_apply_apply z
    rw [map_mul, map_inv, inv_mul_eq_one] at h1
    exact h1.symm
  have hu_eq : ∀ s t : G ℚ Ω, s ζ = t ζ → (u s : ZMod g.M) = u t := by
    intro s t hst
    apply expo_eq hζM
    rw [← hu, ← hu]
    exact hsame s t hst _ hζMN
  let f : G ℚ Ω → ℂ := fun s => ι (χ s : Qbar l) ^ 4 * g.χ (u s : ZMod g.M) ^ 2
  have hf : Continuous f := cont_of_apply ζ f (fun s t h => by simp only [f, hχ s t h, hu_eq s t h])
  have hcof : ∀ᶠ w : Pl in Filter.cofinite, ((l * g.M : ℕ) : 𝓞 ℚ) ∉ w.asIdeal := by
    rw [Filter.eventually_cofinite]
    refine (Ideal.finite_factors (I := Ideal.span {((l * g.M : ℕ) : 𝓞 ℚ)}) ?_).subset ?_
    · rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
      exact_mod_cast hN0
    · intro w hw
      simp only [Set.mem_setOf_eq, not_not] at hw ⊢
      exact Ideal.dvd_span_singleton.mpr hw
  have hev := hcof.and hAtt.2
  have hfeq : f = fun _ => 1 := by
    refine GlobalTheory.Published.ChebotarevDegreeOne.eq_of_frob GlobalTheory.Published.chebotarevDegreeOne'
      (Filter.eventually_cofinite.mp hev) hf continuous_const ?_
    intro v hv _ B hB σ hσ
    obtain ⟨hvN, hvA⟩ := not_not.mp hv
    have hvM : ((g.M : ℕ) : 𝓞 ℚ) ∉ v.asIdeal := fun h => hvN (by push_cast; exact Ideal.mul_mem_left _ _ h)
    have hvl : ((l : ℕ) : 𝓞 ℚ) ∉ v.asIdeal := fun h => hvN (by push_cast; exact Ideal.mul_mem_right _ _ h)
    have hcp := (hvA B hB).2 σ hσ
    have hdet := det_of_charpoly (a := g.a (normV v)) (d := g.χ (normV v) * (normV v : ℂ) ^ (2 * e + 1 - 1)) ι hcp
    have hfr : σ (ζ ^ l) = (ζ ^ l) ^ normV v := root_pow hM0 hB hvM hζM.pow_eq_one hσ.2
    have hus : (u σ : ZMod g.M) = normV v := expo_eq hζM (by rw [← hu, hfr])
    have hcz := cycZ_of_isFrob hvl hB hσ
    have hcyc : ((cycBar ℚ Ω l σ : (Qbar l)ˣ) : Qbar l) = (normV v : Qbar l) := by
      simp [cycBar, hcz]
    have hd2 : (dt W σ) ^ 2 = 1 := by
      have := congrArg (fun φ => φ σ) hN.det2
      simpa using this
    rw [tw_val, Matrix.det_smul] at hdet
    simp only [Fintype.card_fin, map_inv, MonoidHom.mul_apply, MonoidHom.inv_apply, MonoidHom.zpow_apply] at hdet
    have hw : ((↑((W σ)⁻¹) : Matrix (Fin 2) (Fin 2) (Qbar l))).det = (((dt W σ)⁻¹ : (Qbar l)ˣ) : Qbar l) := by
      change ((Matrix.GeneralLinearGroup.det ((W σ)⁻¹) : (Qbar l)ˣ) : Qbar l) = _
      rw [map_inv]
      rfl
    rw [hw] at hdet
    simp only [mul_inv_rev, inv_inv, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_zpow_eq_zpow_val,
      Units.val_inv_eq_inv_val, map_mul, map_pow, map_inv₀, map_zpow₀, hcyc, map_natCast] at hdet
    set a := ι ((χ σ : (Qbar l)ˣ) : Qbar l) with ha_def
    set δ := ι ((dt W σ : (Qbar l)ˣ) : Qbar l) with hδ_def
    have ha : a ≠ 0 := (map_ne_zero ι).mpr (χ σ).ne_zero
    have hδ : δ ^ 2 = 1 := by
      have := congrArg (fun x : (Qbar l)ˣ => ι (x : Qbar l)) hd2
      simpa [hδ_def] using this
    have hδ0 : δ ≠ 0 := (map_ne_zero ι).mpr (dt W σ).ne_zero
    have hp : ((normV v : ℕ) : ℂ) ≠ 0 := by
      have h1 : ι ((cycBar ℚ Ω l σ : (Qbar l)ˣ) : Qbar l) ≠ 0 := (map_ne_zero ι).mpr (cycBar ℚ Ω l σ).ne_zero
      rwa [hcyc, map_natCast] at h1
    rw [Nat.add_sub_cancel, zpow_neg, inv_inv, zpow_natCast] at hdet
    have hχp : g.χ (normV v : ZMod g.M) = δ * a⁻¹ ^ 2 := by
      apply mul_right_cancel₀ (pow_ne_zero (2 * e) hp)
      rw [← hdet]
      field_simp
      try ring
    show a ^ 4 * g.χ (u σ : ZMod g.M) ^ 2 = 1
    rw [hus, hχp, mul_pow, hδ]
    field_simp
    try ring
  obtain ⟨c, hc1, hcd⟩ := Nat.chineseRemainder ((Nat.Prime.coprime_iff_not_dvd hlp).mpr hl) 1 d
  have hcop : c.Coprime (l * g.M) := by
    apply Nat.Coprime.mul_right
    · have := hc1.gcd_eq
      rw [Nat.gcd_one_left] at this
      exact this
    · have := hcd.gcd_eq
      show c.gcd g.M = 1
      rw [this]
      exact hd
  obtain ⟨s, hs⟩ := exists_aut_pow (Ω := Ω) hN0 hcop
  have hχs : χ s = 1 := by
    apply hK
    intro z hz
    rw [hs z (by rw [pow_mul, hz, one_pow])]
    rw [← Nat.div_add_mod c l, pow_add, pow_mul, hz, one_pow, one_mul,
      show c % l = 1 % l from hc1, Nat.mod_eq_of_lt hlp.one_lt, pow_one]
  have hus : (u s : ZMod g.M) = d :=
    (expo_eq hζM ((hu s).symm.trans (hs _ hζMN))).trans ((ZMod.natCast_eq_natCast_iff _ _ _).mpr hcd)
  have h1 := congrFun hfeq s
  simp only [f, hχs, hus, Units.val_one, map_one, one_pow, one_mul] at h1
  rw [sq] at h1
  exact mul_self_eq_one_iff.mp h1
