import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.SelmerOrderCounts.TwoLe

open NumberField IsDedekindDomain UpperTheory.V UpperTheory.V.ZK UpperTheory.V.ZK.Ct

/- English proof (translation)
Use extensionality with `x`. Express the relevant statement in the definitionally equal form `((RingOfIntegers.mapRingEquiv γ⁻¹.toRingEquiv).symm ((RingOfIntegers.mapRingEquiv γ.toRingEquiv).symm x)) ∈ Q.asIdeal ↔ x ∈ Q.asIdeal`. Establish `: ((RingOfIntegers.mapRingEquiv γ⁻¹.toRingEquiv).symm ((RingOfIntegers.mapRingEquiv γ.toRingEquiv).symm x)) = x`. Apply `RingOfIntegers.ext` to reduce the goal to its premises. Simplify using `[RingOfIntegers.mapRingEquiv]`.

Rewrite using `[AlgEquiv.aut_inv, AlgEquiv.symm_symm, AlgEquiv.apply_symm_apply]`. Rewrite using `[this]`.
-/
private theorem actP_actP_inv' {L F : Type} [Field L] [Field F] [Algebra L F] (γ : Gal(F/L))
    (Q : HeightOneSpectrum (𝓞 F)) : actP γ (actP γ⁻¹ Q) = Q := by
  ext x
  change ((RingOfIntegers.mapRingEquiv γ⁻¹.toRingEquiv).symm
    ((RingOfIntegers.mapRingEquiv γ.toRingEquiv).symm x)) ∈ Q.asIdeal ↔ x ∈ Q.asIdeal
  have : ((RingOfIntegers.mapRingEquiv γ⁻¹.toRingEquiv).symm
      ((RingOfIntegers.mapRingEquiv γ.toRingEquiv).symm x)) = x := by
    apply RingOfIntegers.ext
    simp [RingOfIntegers.mapRingEquiv]
    rw [AlgEquiv.aut_inv, AlgEquiv.symm_symm, AlgEquiv.apply_symm_apply]
  rw [this]

/- English proof (translation)
Establish `: Fintype H` using `Fintype.ofFinite H`. Establish `hinj : Function.Injective (fun ψ : H →+ ZMod q => ZMod.stdAddChar.compAddMonoidHom ψ)`. Introduce `ψ₁ ψ₂ h`. Use extensionality with `x`. Use `DFunLike.congr_fun h x` as an intermediate fact.

Simplify using `only [AddChar.compAddMonoidHom_apply] at this`. Conclude with `ZMod.injective_stdAddChar this`. Combine the equalities or inequalities in the displayed calculation.
-/
private theorem card_addMonoidHom_zmod_le_card (H : Type) [AddCommGroup H] [Finite H] (q : ℕ) [NeZero q] :
    Nat.card (H →+ ZMod q) ≤ Nat.card H := by
  have : Fintype H := Fintype.ofFinite H
  have hinj : Function.Injective (fun ψ : H →+ ZMod q => ZMod.stdAddChar.compAddMonoidHom ψ) := by
    intro ψ₁ ψ₂ h
    ext x
    have := DFunLike.congr_fun h x
    simp only [AddChar.compAddMonoidHom_apply] at this
    exact ZMod.injective_stdAddChar this
  calc Nat.card (H →+ ZMod q) ≤ Nat.card (AddChar H ℂ) := Nat.card_le_card_of_injective _ hinj
    _ = Nat.card H := by rw [Nat.card_eq_fintype_card, AddChar.card_eq, Nat.card_eq_fintype_card]

/- English proof (translation)
Use `haveI : NeZero (l ^ ν) := ⟨pow_ne_zero _ hl.ne_zero⟩`. Establish `hn0 : Nat.card G ≠ 0` using `Nat.card_pos.ne'`. Establish `hcop : l.Coprime (Nat.card G / l ^ (Nat.card G).factorization l)` using `Nat.coprime_ordCompl hl hn0`. Establish `hnm` using `Nat.ordProj_mul_ordCompl_eq_self (Nat.card G) l`. Use `set e := (Nat.card G).factorization l`.

Use `set m := Nat.card G / l ^ e`. Set `H` to `(nsmulAddMonoidHom (α := G) m).range`. Use `haveI : Finite (H →+ ZMod (l ^ ν)) := Finite.of_injective _ DFunLike.coe_injective`. Establish `hres : Function.Injective (fun ψ : G →+ ZMod (l ^ ν) => ψ.comp H.subtype)`. Introduce `ψ₁ ψ₂ h`.

Use extensionality with `x`. Establish `hx : ψ₁ (m • x) = ψ₂ (m • x)`. Use `DFunLike.congr_fun h ⟨m • x, x, rfl⟩` as an intermediate fact. Simplify using `using this`. Rewrite `hx` using `[map_nsmul, map_nsmul, nsmul_eq_mul, nsmul_eq_mul]`.

Establish `hu : IsUnit ((m : ZMod (l ^ ν)))` using `(ZMod.unitOfCoprime m (Nat.Coprime.pow_left ν hcop).symm).isUnit`. Conclude with `hu.mul_left_cancel hx`. Establish `h1 : Nat.card (G →+ ZMod (l ^ ν)) ≤ Nat.card (H →+ ZMod (l ^ ν))` using `Nat.card_le_card_of_injective _ hres`. Establish `h2` using `card_addMonoidHom_zmod_le_card H (l ^ ν)`. Establish `hkill : ∀ h : H, (l ^ e) • h = 0`.

Introduce and unpack `⟨_, x, rfl⟩`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `only [AddSubgroup.coe_nsmul, AddSubgroup.coe_zero, nsmulAddMonoidHom_apply]`. Rewrite using `[smul_smul, hnm]`. Conclude with `card_nsmul_eq_zero'`.

Establish `hcopH : (Nat.card H).Coprime m`. Apply `Nat.coprime_of_dvd` to reduce the goal to its premises. Introduce `k hk hkH hkm`. Use `haveI := Fact.mk hk`. Take `⟨h, hh⟩` from `exists_prime_addOrderOf_dvd_card' k hkH`.

Establish `hk' : k ∣ l ^ e` using `hh ▸ addOrderOf_dvd_of_nsmul_eq_zero (hkill h)`. Establish `: k = l` using `(Nat.prime_dvd_prime_iff_eq hk hl).1 (hk.dvd_of_dvd_pow hk')`. Substitute `this` using the available equality. Conclude with `(Nat.Prime.coprime_iff_not_dvd hk).1 hcop hkm`. Establish `hdvd : Nat.card H ∣ l ^ e`.

Use `AddSubgroup.card_addSubgroup_dvd_card H` as an intermediate fact. Rewrite `this` using `[← hnm]`. Conclude with `hcopH.dvd_of_dvd_mul_right this`. Conclude with `h1.trans (h2.trans (Nat.le_of_dvd (pow_pos hl.pos _) hdvd))`.
-/
private theorem card_addMonoidHom_zmod_prime_pow_le_pow_factorization (G : Type) [AddCommGroup G] [Finite G] (l ν : ℕ) (hl : l.Prime) :
    Nat.card (G →+ ZMod (l ^ ν)) ≤ l ^ (Nat.card G).factorization l := by
  haveI : NeZero (l ^ ν) := ⟨pow_ne_zero _ hl.ne_zero⟩
  have hn0 : Nat.card G ≠ 0 := Nat.card_pos.ne'
  have hcop : l.Coprime (Nat.card G / l ^ (Nat.card G).factorization l) := Nat.coprime_ordCompl hl hn0
  have hnm := Nat.ordProj_mul_ordCompl_eq_self (Nat.card G) l
  set e := (Nat.card G).factorization l
  set m := Nat.card G / l ^ e
  let H := (nsmulAddMonoidHom (α := G) m).range
  haveI : Finite (H →+ ZMod (l ^ ν)) := Finite.of_injective _ DFunLike.coe_injective
  have hres : Function.Injective (fun ψ : G →+ ZMod (l ^ ν) => ψ.comp H.subtype) := by
    intro ψ₁ ψ₂ h
    ext x
    have hx : ψ₁ (m • x) = ψ₂ (m • x) := by
      have := DFunLike.congr_fun h ⟨m • x, x, rfl⟩
      simpa using this
    rw [map_nsmul, map_nsmul, nsmul_eq_mul, nsmul_eq_mul] at hx
    have hu : IsUnit ((m : ZMod (l ^ ν))) :=
      (ZMod.unitOfCoprime m (Nat.Coprime.pow_left ν hcop).symm).isUnit
    exact hu.mul_left_cancel hx
  have h1 : Nat.card (G →+ ZMod (l ^ ν)) ≤ Nat.card (H →+ ZMod (l ^ ν)) :=
    Nat.card_le_card_of_injective _ hres
  have h2 := card_addMonoidHom_zmod_le_card H (l ^ ν)
  have hkill : ∀ h : H, (l ^ e) • h = 0 := by
    rintro ⟨_, x, rfl⟩
    apply Subtype.ext
    simp only [AddSubgroup.coe_nsmul, AddSubgroup.coe_zero, nsmulAddMonoidHom_apply]
    rw [smul_smul, hnm]
    exact card_nsmul_eq_zero'
  have hcopH : (Nat.card H).Coprime m := by
    apply Nat.coprime_of_dvd
    intro k hk hkH hkm
    haveI := Fact.mk hk
    obtain ⟨h, hh⟩ := exists_prime_addOrderOf_dvd_card' k hkH
    have hk' : k ∣ l ^ e := hh ▸ addOrderOf_dvd_of_nsmul_eq_zero (hkill h)
    have : k = l := (Nat.prime_dvd_prime_iff_eq hk hl).1 (hk.dvd_of_dvd_pow hk')
    subst this
    exact (Nat.Prime.coprime_iff_not_dvd hk).1 hcop hkm
  have hdvd : Nat.card H ∣ l ^ e := by
    have := AddSubgroup.card_addSubgroup_dvd_card H
    rw [← hnm] at this
    exact hcopH.dvd_of_dvd_mul_right this
  exact h1.trans (h2.trans (Nat.le_of_dvd (pow_pos hl.pos _) hdvd))

/- English proof (translation)
Introduce `L F _ _ _ _ _ γ a l ν D hl hD hfin`. Use `haveI : NeZero (l ^ ν) := ⟨pow_ne_zero _ hl.ne_zero⟩`. Establish `hinv : ∀ Q, actP γ⁻¹ (actP γ Q) = Q` using `fun Q => by`. Simplify using `using actP_actP_inv' γ⁻¹ Q`. Establish `hsingle : ∀ (P : HeightOneSpectrum (𝓞 F)) (n : ℤ), D.gI (Finsupp.single P n) = Finsupp.single (actP γ⁻¹ P) n`.

Introduce `P n`. Use extensionality with `Q`. Rewrite using `[hD.gI_eq, Finsupp.single_apply, Finsupp.single_apply]`. Establish `hiff : (P = actP γ Q) ↔ (actP γ⁻¹ P = Q)` using `⟨fun h => h ▸ hinv Q, fun h => h ▸ (actP_actP_inv' γ P).symm⟩`. Use `split_ifs with h1 h2 h2`.

Both sides reduce to the same expression. Conclude with `absurd (hiff.1 h1) h2`. Conclude with `absurd (hiff.2 h2) h1`. Both sides reduce to the same expression. Set `ψ0 : (HeightOneSpectrum (𝓞 F) → ZMod (l ^ ν)) → ((HeightOneSpectrum (𝓞 F) →₀ ℤ) →+ ZMod (l ^ ν))` to `fun φ => Finsupp.liftAddHom fun P => (AddMonoidHom.mulRight (φ P)).comp (Int.castAddHom (ZMod (l ^ ν)))`.

Establish `hψs : ∀ φ P (n : ℤ), ψ0 φ (Finsupp.single P n) = (n : ZMod (l ^ ν)) * φ P`. Introduce `φ P n`. Simplify using `[ψ0]`. Establish `hle : ∀ φ ∈ EqHom γ a (l ^ ν), LinearMap.range D.d ⊔ LinearMap.range D.delI ≤ LinearMap.ker (ψ0 φ).toIntLinearMap`. Introduce `φ hφ`.

Apply `sup_le` to reduce the goal to its premises. Introduce and unpack `_ ⟨y, rfl⟩`. Rewrite using `[LinearMap.mem_ker, AddMonoidHom.coe_toIntLinearMap]`. Establish `h1` using `hφ.1 (Additive.toMul y)`. Rewrite using `[← h1]`.

Simplify using `only [ψ0, Finsupp.liftAddHom_apply, Finsupp.sum]`. Rewrite using `[finsum_eq_sum_of_support_subset]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `P _`. Simplify using `[← hD.d_eq]`.

Introduce `P hP`. Rewrite `hP` using `[Function.mem_support]`. Rewrite using `[Finset.mem_coe, Finsupp.mem_support_iff]`. Introduce `h0`. Apply `hP` to reduce the goal to its premises.

Rewrite using `[← hD.d_eq]`. Simplify using `[h0]`. Establish `key : ∀ 𝔡, ψ0 φ (D.gI 𝔡) = (a : ZMod (l ^ ν)) * ψ0 φ 𝔡`. Introduce `𝔡`. Proceed by induction on `𝔡 using Finsupp.induction_linear with`.

Consider the case `zero => simp`. Consider the case `add f g hf hg => rw [map_add, map_add, map_add, hf, hg, mul_add]`. Consider the case `single P n`. Rewrite using `[hsingle, hψs, hψs, hφ.2 P]`. Expand and normalize the polynomial expressions, which then agree.

Introduce and unpack `_ ⟨𝔡, rfl⟩`. Rewrite using `[LinearMap.mem_ker, AddMonoidHom.coe_toIntLinearMap]`. Simplify using `only [Dat.delI, LinearMap.sub_apply, map_sub, key, hD.a_eq]`. Simplify using the standard rewrite rules. Set `f : EqHom γ a (l ^ ν) → (D.ClQ →+ ZMod (l ^ ν))` to `fun φ => ((LinearMap.range D.d ⊔ LinearMap.range D.delI).liftQ (ψ0 φ.1).toIntLinearMap (hle φ.1 φ.2)).toAddMonoidHom`.

Establish `hf : Function.Injective f`. Introduce `φ₁ φ₂ h`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `P`. Use `DFunLike.congr_fun h (Submodule.Quotient.mk (Finsupp.single P 1))` as an intermediate fact.

Simplify `this` using `[f, hψs]`. Use `haveI : Finite (D.ClQ →+ ZMod (l ^ ν)) := Finite.of_injective _ DFunLike.coe_injective`. Use `⟨Finite.of_injective f hf, ?_⟩` and prove the remaining obligations. Conclude with `(Nat.card_le_card_of_injective f hf).trans (card_addMonoidHom_zmod_prime_pow_le_pow_factorization D.ClQ l ν hl)`.
-/
theorem UpperTheory.V.ZK.Ct.eqHomLe :
    ∀ (L F : Type) [Field L] [NumberField L] [Field F] [NumberField F] [Algebra L F] (γ : F ≃ₐ[L] F) (a l ν : ℕ) (D : Dat (Additive Fˣ) (HeightOneSpectrum (𝓞 F) →₀ ℤ)), l.Prime → IsDat γ a D → Finite D.ClQ → Finite (EqHom γ a (l ^ ν)) ∧ Nat.card (EqHom γ a (l ^ ν)) ≤ l ^ (Nat.card D.ClQ).factorization l := by
  classical
  intro L F _ _ _ _ _ γ a l ν D hl hD hfin
  haveI : NeZero (l ^ ν) := ⟨pow_ne_zero _ hl.ne_zero⟩
  have hinv : ∀ Q, actP γ⁻¹ (actP γ Q) = Q := fun Q => by
    simpa using actP_actP_inv' γ⁻¹ Q
  have hsingle : ∀ (P : HeightOneSpectrum (𝓞 F)) (n : ℤ),
      D.gI (Finsupp.single P n) = Finsupp.single (actP γ⁻¹ P) n := by
    intro P n
    ext Q
    rw [hD.gI_eq, Finsupp.single_apply, Finsupp.single_apply]
    have hiff : (P = actP γ Q) ↔ (actP γ⁻¹ P = Q) :=
      ⟨fun h => h ▸ hinv Q, fun h => h ▸ (actP_actP_inv' γ P).symm⟩
    split_ifs with h1 h2 h2
    · rfl
    · exact absurd (hiff.1 h1) h2
    · exact absurd (hiff.2 h2) h1
    · rfl
  let ψ0 : (HeightOneSpectrum (𝓞 F) → ZMod (l ^ ν)) → ((HeightOneSpectrum (𝓞 F) →₀ ℤ) →+ ZMod (l ^ ν)) :=
    fun φ => Finsupp.liftAddHom fun P => (AddMonoidHom.mulRight (φ P)).comp (Int.castAddHom (ZMod (l ^ ν)))
  have hψs : ∀ φ P (n : ℤ), ψ0 φ (Finsupp.single P n) = (n : ZMod (l ^ ν)) * φ P := by
    intro φ P n
    simp [ψ0]
  have hle : ∀ φ ∈ EqHom γ a (l ^ ν),
      LinearMap.range D.d ⊔ LinearMap.range D.delI ≤ LinearMap.ker (ψ0 φ).toIntLinearMap := by
    intro φ hφ
    apply sup_le
    · rintro _ ⟨y, rfl⟩
      rw [LinearMap.mem_ker, AddMonoidHom.coe_toIntLinearMap]
      have h1 := hφ.1 (Additive.toMul y)
      rw [← h1]
      simp only [ψ0, Finsupp.liftAddHom_apply, Finsupp.sum]
      rw [finsum_eq_sum_of_support_subset]
      · apply Finset.sum_congr rfl
        intro P _
        simp [← hD.d_eq]
      · intro P hP
        rw [Function.mem_support] at hP
        rw [Finset.mem_coe, Finsupp.mem_support_iff]
        intro h0
        apply hP
        rw [← hD.d_eq]
        simp [h0]
    · have key : ∀ 𝔡, ψ0 φ (D.gI 𝔡) = (a : ZMod (l ^ ν)) * ψ0 φ 𝔡 := by
        intro 𝔡
        induction 𝔡 using Finsupp.induction_linear with
        | zero => simp
        | add f g hf hg => rw [map_add, map_add, map_add, hf, hg, mul_add]
        | single P n =>
          rw [hsingle, hψs, hψs, hφ.2 P]
          ring
      rintro _ ⟨𝔡, rfl⟩
      rw [LinearMap.mem_ker, AddMonoidHom.coe_toIntLinearMap]
      simp only [Dat.delI, LinearMap.sub_apply, map_sub, key, hD.a_eq]
      simp
  let f : EqHom γ a (l ^ ν) → (D.ClQ →+ ZMod (l ^ ν)) := fun φ =>
    ((LinearMap.range D.d ⊔ LinearMap.range D.delI).liftQ (ψ0 φ.1).toIntLinearMap (hle φ.1 φ.2)).toAddMonoidHom
  have hf : Function.Injective f := by
    intro φ₁ φ₂ h
    apply Subtype.ext
    funext P
    have := DFunLike.congr_fun h (Submodule.Quotient.mk (Finsupp.single P 1))
    simpa [f, hψs] using this
  haveI : Finite (D.ClQ →+ ZMod (l ^ ν)) := Finite.of_injective _ DFunLike.coe_injective
  refine ⟨Finite.of_injective f hf, ?_⟩
  exact (Nat.card_le_card_of_injective f hf).trans (card_addMonoidHom_zmod_prime_pow_le_pow_factorization D.ClQ l ν hl)
