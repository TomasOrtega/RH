import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.EntryMem
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.LMemMax
import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.QocEquiv
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.ContTw
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

/- English proof (translation)
Take `⟨hN, hA⟩` from `isFiniteLength_iff_isNoetherian_isArtinian.1 (Module.length_ne_top_iff.1 h)`. Take `⟨p, hp⟩` from `IsDiscreteValuationRing.exists_irreducible O`. Take `⟨n, hn⟩` from `IsArtinian.range_smul_pow_stabilizes M p`. Establish `h1` using `hn (n + 1) (Nat.le_succ n)`. Establish `h2 : LinearMap.range (p ^ n • LinearMap.id : M →ₗ[O] M) = ⊥`.

Use `Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal O) _ (IsNoetherian.noetherian _) ?_ (maximalIdeal_le_jacobson _)` and prove the remaining obligations. Introduce `y hy`. Rewrite `hy` using `[h1]`. Take `⟨x, rfl⟩` from `hy`. Establish `: (p ^ (n + 1) • LinearMap.id : M →ₗ[O] M) x = p • (p ^ n • LinearMap.id : M →ₗ[O] M) x`.

Simplify using `[smul_smul, pow_succ']`. Rewrite using `[this]`. Conclude with `Submodule.smul_mem_smul ((mem_maximalIdeal _).2 hp.not_isUnit) ⟨x, rfl⟩`. Use `⟨p ^ n, pow_ne_zero _ hp.ne_zero, fun x => ?_⟩` and prove the remaining obligations. Establish `: (p ^ n • LinearMap.id : M →ₗ[O] M) x ∈ (⊥ : Submodule O M)` using `h2 ▸ ⟨x, rfl⟩`.

Simplify using `using this`.
-/
private theorem kill_of_len {O M : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [AddCommGroup M]
    [Module O M] (h : Module.length O M ≠ ⊤) : ∃ b : O, b ≠ 0 ∧ ∀ x : M, b • x = 0 := by
  obtain ⟨hN, hA⟩ := isFiniteLength_iff_isNoetherian_isArtinian.1 (Module.length_ne_top_iff.1 h)
  obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨n, hn⟩ := IsArtinian.range_smul_pow_stabilizes M p
  have h1 := hn (n + 1) (Nat.le_succ n)
  have h2 : LinearMap.range (p ^ n • LinearMap.id : M →ₗ[O] M) = ⊥ := by
    refine Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal O) _ (IsNoetherian.noetherian _) ?_
      (maximalIdeal_le_jacobson _)
    intro y hy
    rw [h1] at hy
    obtain ⟨x, rfl⟩ := hy
    have : (p ^ (n + 1) • LinearMap.id : M →ₗ[O] M) x = p • (p ^ n • LinearMap.id : M →ₗ[O] M) x := by
      simp [smul_smul, pow_succ']
    rw [this]
    exact Submodule.smul_mem_smul ((mem_maximalIdeal _).2 hp.not_isUnit) ⟨x, rfl⟩
  refine ⟨p ^ n, pow_ne_zero _ hp.ne_zero, fun x => ?_⟩
  have : (p ^ n • LinearMap.id : M →ₗ[O] M) x ∈ (⊥ : Submodule O M) := h2 ▸ ⟨x, rfl⟩
  simpa using this

section Abs

variable {O W Γ : Type} [CommRing O] [AddCommGroup W] [Module O W] [TopologicalSpace W] [DiscreteTopology W]
  [IsTopologicalAddGroup W] [ContinuousConstSMul O W] [Group Γ] [TopologicalSpace Γ]

/- English proof (translation)
Take `⟨u, hu⟩` from `hu`. Set `t : Γ → (⊤ : Subgroup Γ)` to `fun g => ⟨g, trivial⟩`. Set `n : Z1U (Formalism.GaloisCohomology.scalRep W θ) ⊤ →ₗ[O] (Γ → W)` to `{ toFun := fun z g => z.1 (t g) - ((θ g : O) - 1) • ((u⁻¹ : Oˣ) : O) • z.1 (t g0) map_add' := fun z z' => by`. Use function extensionality and compare the values at `g`. Simplify using `only [Submodule.coe_add, Pi.add_apply, smul_add]`.

Normalize the expressions using the abelian group laws. Use the proof step `map_smul' := fun r z => by`. Use function extensionality and compare the values at `g`. Simplify using `only [Submodule.coe_smul, Pi.smul_apply, smul_sub, RingHom.id_apply, smul_smul]`. Use `congr 2`.

Use `ring }`. Establish `hn : ∀ z g, n z g = z.1 (t g) - ((θ g : O) - 1) • ((u⁻¹ : Oˣ) : O) • z.1 (t g0)` using `fun _ _ => rfl`. Establish `hker : ∀ z, n z = 0 ↔ ∃ m : W, ∀ g : (⊤ : Subgroup Γ), z.1 g = (θ g : O) • m - m` using `fun z => by`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Use `⟨((u⁻¹ : Oˣ) : O) • z.1 (t g0), fun g => ?_⟩` and prove the remaining obligations. Use `congrFun h g` as an intermediate fact. Rewrite `this` using `[hn, Pi.zero_apply, sub_eq_zero, sub_smul, one_smul]`. Conclude with `this`. Introduce and unpack `⟨m, hm⟩`.

Use function extensionality and compare the values at `g`. Establish `e : z.1 (t g0) = (u : O) • m` using `by rw [hm, hu, sub_smul, one_smul]`. Rewrite using `[hn, e, smul_smul _ _ m, Units.inv_mul, one_smul, hm, sub_smul, one_smul]`. Conclude with `sub_self _`. Use `⟨Submodule.liftQ _ n fun z hz => (hker z).2 ((mem_coboundaries1 _ _).1 hz), ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[injective_iff_map_eq_zero]`. Introduce `x hx`. Take `⟨z, rfl⟩` from `Submodule.Quotient.mk_surjective _ x`. Conclude with `(Submodule.Quotient.mk_eq_zero _).2 ((mem_coboundaries1 _ _).2 ((hker z).1 hx))`. Introduce `x`.

Take `⟨z, rfl⟩` from `Submodule.Quotient.mk_surjective _ x`. Rewrite using `[IsLocallyConstant.iff_continuous]`. Use `show Continuous (n z)`. Establish `h1 : Continuous fun g => z.1 (t g)` using `z.2.1.comp (continuous_id.subtype_mk _)`. Use `(h1.sub ((hc (((u⁻¹ : Oˣ) : O) • z.1 (t g0))).sub (continuous_const (y := ((u⁻¹ : Oˣ) : O) • z.1 (t g0))))).congr fun g => ?_` and prove the remaining obligations.

Rewrite using `[hn, sub_smul, one_smul]`. Both sides reduce to the same expression. Introduce `x g h`. Take `⟨z, rfl⟩` from `Submodule.Quotient.mk_surjective _ x`. Use `show n z _ = n z _ + _ • n z _`.

Establish `e : z.1 (t (g * h)) = z.1 (t g) + (θ g : O) • z.1 (t h)` using `z.2.2 (t g) (t h)`. Rewrite using `[hn, hn, hn, e, map_mul, Units.val_mul]`. Use `module`. Introduce `x`. Take `⟨z, rfl⟩` from `Submodule.Quotient.mk_surjective _ x`.

Use `show n z _ = 0`. Rewrite using `[hn, ← hu, smul_smul, Units.mul_inv, one_smul, sub_self]`. Introduce `𝒟 x hx D hD`. Take `⟨z, rfl⟩` from `Submodule.Quotient.mk_surjective _ x`. Take `⟨m, hm⟩` from `mk_mem_locSel.1 hx D hD`.

Use `⟨m - ((u⁻¹ : Oˣ) : O) • z.1 (t g0), fun g hg => ?_⟩` and prove the remaining obligations. Use `show n z _ = _`. Establish `e : z.1 (t g) = (θ g : O) • m - m` using `hm (t g) hg`. Rewrite using `[hn, e]`. Use `module`.
-/
private theorem exists_norm (θ : Γ →* Oˣ) (hc : ∀ m : W, Continuous fun g => (θ g : O) • m) (g0 : Γ)
    (hu : IsUnit ((θ g0 : O) - 1)) :
    ∃ N : H1U (Formalism.GaloisCohomology.scalRep W θ) ⊤ →ₗ[O] (Γ → W), Function.Injective N ∧ (∀ x, IsLocallyConstant (N x)) ∧
      (∀ x g h, N x (g * h) = N x g + (θ g : O) • N x h) ∧ (∀ x, N x g0 = 0) ∧
      ∀ (𝒟 : Set (Subgroup Γ)) x, x ∈ LocSel (Formalism.GaloisCohomology.scalRep W θ) ⊤ 𝒟 → ∀ D ∈ 𝒟, ∃ m : W, ∀ g ∈ D,
        N x g = (θ g : O) • m - m := by
  obtain ⟨u, hu⟩ := hu
  let t : Γ → (⊤ : Subgroup Γ) := fun g => ⟨g, trivial⟩
  let n : Z1U (Formalism.GaloisCohomology.scalRep W θ) ⊤ →ₗ[O] (Γ → W) :=
    { toFun := fun z g => z.1 (t g) - ((θ g : O) - 1) • ((u⁻¹ : Oˣ) : O) • z.1 (t g0)
      map_add' := fun z z' => by
        funext g
        simp only [Submodule.coe_add, Pi.add_apply, smul_add]
        abel
      map_smul' := fun r z => by
        funext g
        simp only [Submodule.coe_smul, Pi.smul_apply, smul_sub, RingHom.id_apply, smul_smul]
        congr 2
        ring }
  have hn : ∀ z g, n z g = z.1 (t g) - ((θ g : O) - 1) • ((u⁻¹ : Oˣ) : O) • z.1 (t g0) := fun _ _ => rfl
  have hker : ∀ z, n z = 0 ↔ ∃ m : W, ∀ g : (⊤ : Subgroup Γ), z.1 g = (θ g : O) • m - m := fun z => by
    constructor
    · intro h
      refine ⟨((u⁻¹ : Oˣ) : O) • z.1 (t g0), fun g => ?_⟩
      have := congrFun h g
      rw [hn, Pi.zero_apply, sub_eq_zero, sub_smul, one_smul] at this
      exact this
    · rintro ⟨m, hm⟩
      funext g
      have e : z.1 (t g0) = (u : O) • m := by rw [hm, hu, sub_smul, one_smul]
      rw [hn, e, smul_smul _ _ m, Units.inv_mul, one_smul, hm, sub_smul, one_smul]
      exact sub_self _
  refine ⟨Submodule.liftQ _ n fun z hz => (hker z).2 ((mem_coboundaries1 _ _).1 hz), ?_, ?_, ?_, ?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    exact (Submodule.Quotient.mk_eq_zero _).2 ((mem_coboundaries1 _ _).2 ((hker z).1 hx))
  · intro x
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [IsLocallyConstant.iff_continuous]
    show Continuous (n z)
    have h1 : Continuous fun g => z.1 (t g) := z.2.1.comp (continuous_id.subtype_mk _)
    refine (h1.sub ((hc (((u⁻¹ : Oˣ) : O) • z.1 (t g0))).sub (continuous_const (y := ((u⁻¹ : Oˣ) : O) • z.1 (t g0))))).congr fun g => ?_
    rw [hn, sub_smul, one_smul]
    rfl
  · intro x g h
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    show n z _ = n z _ + _ • n z _
    have e : z.1 (t (g * h)) = z.1 (t g) + (θ g : O) • z.1 (t h) := z.2.2 (t g) (t h)
    rw [hn, hn, hn, e, map_mul, Units.val_mul]
    module
  · intro x
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    show n z _ = 0
    rw [hn, ← hu, smul_smul, Units.mul_inv, one_smul, sub_self]
  · intro 𝒟 x hx D hD
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨m, hm⟩ := mk_mem_locSel.1 hx D hD
    refine ⟨m - ((u⁻¹ : Oˣ) : O) • z.1 (t g0), fun g hg => ?_⟩
    show n z _ = _
    have e : z.1 (t g) = (θ g : O) • m - m := hm (t g) hg
    rw [hn, e]
    module

omit [TopologicalSpace W] [DiscreteTopology W] [IsTopologicalAddGroup W] [ContinuousConstSMul O W] in
/- English proof (translation)
Set `ι : (O ⧸ Ideal.span {a}) →ₗ[O] W` to `Submodule.liftQ (Ideal.span {a}) (LinearMap.toSpanSingleton O W w) fun y hy => (hw y).2 (Ideal.mem_span_singleton.1 hy)`. Use `⟨ι, Function.invFun ι, ?_, fun m hm => Function.invFun_eq ?_⟩` and prove the remaining obligations. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `x hx`. Take `⟨y, rfl⟩` from `Submodule.Quotient.mk_surjective _ x`.

Conclude with `(Submodule.Quotient.mk_eq_zero _).2 (Ideal.mem_span_singleton.2 ((hw y).1 hx))`. Take `⟨y, rfl⟩` from `hg m hm`. Conclude with `⟨Submodule.Quotient.mk y, rfl⟩`.
-/
private theorem exists_j (a : O) (w : W) (hw : ∀ y : O, y • w = 0 ↔ a ∣ y) (hg : ∀ w' : W, a • w' = 0 → ∃ y : O, w' = y • w) :
    ∃ (ι : (O ⧸ Ideal.span {a}) →ₗ[O] W) (j : W → O ⧸ Ideal.span {a}), Function.Injective ι ∧
      ∀ m, a • m = 0 → ι (j m) = m := by
  let ι : (O ⧸ Ideal.span {a}) →ₗ[O] W := Submodule.liftQ (Ideal.span {a}) (LinearMap.toSpanSingleton O W w)
    fun y hy => (hw y).2 (Ideal.mem_span_singleton.1 hy)
  refine ⟨ι, Function.invFun ι, ?_, fun m hm => Function.invFun_eq ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    exact (Submodule.Quotient.mk_eq_zero _).2 (Ideal.mem_span_singleton.2 ((hw y).1 hx))
  · obtain ⟨y, rfl⟩ := hg m hm
    exact ⟨Submodule.Quotient.mk y, rfl⟩

/- English proof (translation)
Take `⟨N, hi, hl, hco, h0, hloc⟩` from `exists_norm θ hc g0 hu`. Use `choose! s hs hs1 using fun v hv => (hG v hv).2`. Set `a : O` to `b * ∏ v ∈ T, ((θ (s v) : O) - 1)`. Establish `ha : a ≠ 0` using `mul_ne_zero hb (Finset.prod_ne_zero_iff.2 fun v hv h => hs1 v hv (Units.ext (sub_eq_zero.1 h)))`. Take `⟨w, hw, hg⟩` from `hW a ha`.

Take `⟨ι, j, hι, hj⟩` from `exists_j a w hw hg`. Establish `hbN : ∀ (x : LocSel (Formalism.GaloisCohomology.scalRep W θ) ⊤ 𝒟) g, b • N x g = 0` using `fun x g => by`. Establish `h1 : b • (x : H1U (Formalism.GaloisCohomology.scalRep W θ) ⊤) = 0` using `congrArg Subtype.val (hk x)`. Establish `h2` using `congrFun (map_smul N b x.1) g`. Rewrite `h2` using `[h1, map_zero]`.

Conclude with `h2.symm`. Establish `haN : ∀ (x : LocSel (Formalism.GaloisCohomology.scalRep W θ) ⊤ 𝒟) g, ι (j (N x g)) = N x g` using `fun x g => hj _ (by show (b * _) • _ = _`. Rewrite using `[mul_comm b, mul_smul, hbN, smul_zero])`. Establish `hmul : ∀ (r : O) (q : O ⧸ Ideal.span {a}), ι (Ideal.Quotient.mk _ r * q) = r • ι q` using `fun r q => map_smul ι r q`. Set `Z : LocSel (Formalism.GaloisCohomology.scalRep W θ) ⊤ 𝒟 →+ (Γ → O ⧸ Ideal.span {a})` to `AddMonoidHom.mk' (fun x g => j (N x g)) fun x y => funext fun g => hι (by show ι (j (N (x + y).1 g)) = ι (j (N x.1 g) + j (N y.1 g))`.

Rewrite using `[ι.map_add, haN, haN, haN, Submodule.coe_add, N.map_add, Pi.add_apply])`. Establish `hZ : ∀ x g, ι (Z x g) = N x g` using `haN`. Use `⟨a, ha, Z, fun x y h => Subtype.ext (hi (funext fun g => by rw [← hZ, ← hZ, h])), fun x => ⟨(hl x).comp j, fun g h => hι ?_, fun D hD g hg h1 => hι ?_, hι ?_, fun v hv => ?_⟩⟩` and prove the remaining obligations. Rewrite using `[map_add, hmul, hZ, hZ, hZ, hco]`. Take `⟨m, hm⟩` from `hloc 𝒟 x x.2 D hD`.

Rewrite using `[hZ, hm g hg, h1, map_zero, Units.val_one, one_smul, sub_self]`. Rewrite using `[hZ, h0, map_zero]`. Take `⟨m, hm⟩` from `hloc 𝒟 x x.2 _ (hG v hv).1`. Establish `h1 : a • m = 0`. Establish `e : (((θ (s v) : O) - 1)) • m = N x (s v)` using `by rw [hm _ (hs v hv), sub_smul, one_smul]`.

Take `⟨d, hd⟩` from `Finset.dvd_prod_of_mem (fun v => (θ (s v) : O) - 1) hv`. Establish `: a = d * (b * ((θ (s v) : O) - 1))` using `by show b * _ = _`. Rewrite using `[hd]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this, mul_smul, mul_smul, e, hbN, smul_zero]`.

Use `⟨j m, fun g hg => hι ?_⟩` and prove the remaining obligations. Rewrite using `[hZ, map_sub, hmul, hj m h1, hm g hg]`.
-/
private theorem main_abs [IsDomain O] (θ : Γ →* Oˣ) (hc : ∀ m : W, Continuous fun g => (θ g : O) • m) (g0 : Γ)
    (hu : IsUnit ((θ g0 : O) - 1)) (𝒟 : Set (Subgroup Γ)) (b : O) (hb : b ≠ 0)
    (hk : ∀ x : LocSel (Formalism.GaloisCohomology.scalRep W θ) ⊤ 𝒟, b • x = 0) (T : Finset ℕ) (Gp : ℕ → Subgroup Γ)
    (hG : ∀ v ∈ T, Gp v ∈ 𝒟 ∧ ∃ s ∈ Gp v, θ s ≠ 1)
    (hW : ∀ a : O, a ≠ 0 → ∃ w : W, (∀ y : O, y • w = 0 ↔ a ∣ y) ∧ ∀ w' : W, a • w' = 0 → ∃ y : O, w' = y • w) :
    ∃ a : O, a ≠ 0 ∧ ∃ Z : LocSel (Formalism.GaloisCohomology.scalRep W θ) ⊤ 𝒟 →+ (Γ → O ⧸ Ideal.span {a}), Function.Injective Z ∧
      ∀ x, IsLocallyConstant (Z x) ∧ (∀ g h, Z x (g * h) = Z x g + Ideal.Quotient.mk _ (θ g : O) * Z x h) ∧
        (∀ D ∈ 𝒟, ∀ g ∈ D, θ g = 1 → Z x g = 0) ∧ Z x g0 = 0 ∧
        ∀ v ∈ T, ∃ m : O ⧸ Ideal.span {a}, ∀ g ∈ Gp v, Z x g = Ideal.Quotient.mk _ (θ g : O) * m - m := by
  obtain ⟨N, hi, hl, hco, h0, hloc⟩ := exists_norm θ hc g0 hu
  choose! s hs hs1 using fun v hv => (hG v hv).2
  let a : O := b * ∏ v ∈ T, ((θ (s v) : O) - 1)
  have ha : a ≠ 0 := mul_ne_zero hb (Finset.prod_ne_zero_iff.2 fun v hv h =>
    hs1 v hv (Units.ext (sub_eq_zero.1 h)))
  obtain ⟨w, hw, hg⟩ := hW a ha
  obtain ⟨ι, j, hι, hj⟩ := exists_j a w hw hg
  have hbN : ∀ (x : LocSel (Formalism.GaloisCohomology.scalRep W θ) ⊤ 𝒟) g, b • N x g = 0 := fun x g => by
    have h1 : b • (x : H1U (Formalism.GaloisCohomology.scalRep W θ) ⊤) = 0 := congrArg Subtype.val (hk x)
    have h2 := congrFun (map_smul N b x.1) g
    rw [h1, map_zero] at h2
    exact h2.symm
  have haN : ∀ (x : LocSel (Formalism.GaloisCohomology.scalRep W θ) ⊤ 𝒟) g, ι (j (N x g)) = N x g := fun x g =>
    hj _ (by
      show (b * _) • _ = _
      rw [mul_comm b, mul_smul, hbN, smul_zero])
  have hmul : ∀ (r : O) (q : O ⧸ Ideal.span {a}), ι (Ideal.Quotient.mk _ r * q) = r • ι q := fun r q =>
    map_smul ι r q
  let Z : LocSel (Formalism.GaloisCohomology.scalRep W θ) ⊤ 𝒟 →+ (Γ → O ⧸ Ideal.span {a}) := AddMonoidHom.mk' (fun x g => j (N x g))
    fun x y => funext fun g => hι (by
      show ι (j (N (x + y).1 g)) = ι (j (N x.1 g) + j (N y.1 g))
      rw [ι.map_add, haN, haN, haN, Submodule.coe_add, N.map_add, Pi.add_apply])
  have hZ : ∀ x g, ι (Z x g) = N x g := haN
  refine ⟨a, ha, Z, fun x y h => Subtype.ext (hi (funext fun g => by rw [← hZ, ← hZ, h])), fun x =>
    ⟨(hl x).comp j, fun g h => hι ?_, fun D hD g hg h1 => hι ?_, hι ?_, fun v hv => ?_⟩⟩
  · rw [map_add, hmul, hZ, hZ, hZ, hco]
  · obtain ⟨m, hm⟩ := hloc 𝒟 x x.2 D hD
    rw [hZ, hm g hg, h1, map_zero, Units.val_one, one_smul, sub_self]
  · rw [hZ, h0, map_zero]
  · obtain ⟨m, hm⟩ := hloc 𝒟 x x.2 _ (hG v hv).1
    have h1 : a • m = 0 := by
      have e : (((θ (s v) : O) - 1)) • m = N x (s v) := by rw [hm _ (hs v hv), sub_smul, one_smul]
      obtain ⟨d, hd⟩ := Finset.dvd_prod_of_mem (fun v => (θ (s v) : O) - 1) hv
      have : a = d * (b * ((θ (s v) : O) - 1)) := by
        show b * _ = _
        rw [hd]; ring
      rw [this, mul_smul, mul_smul, e, hbN, smul_zero]
    refine ⟨j m, fun g hg => hι ?_⟩
    rw [hZ, map_sub, hmul, hj m h1, hm g hg]

end Abs

section Conc

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c)

/- English proof (translation)
Rewrite using `[MonoidHom.inv_apply]`. Establish `h1 : IsUnit (1 - (D.Psi D.g0 : c.O))`. Rewrite using `[← residue_ne_zero_iff_isUnit, map_sub, map_one]`. Conclude with `fun h => hD.genElt_Psi (sub_eq_zero.1 h).symm`. Use `(Units.isUnit (D.Psi D.g0)⁻¹).mul h1` as an intermediate fact.

Rewrite `this` using `[mul_sub, mul_one, Units.inv_mul]`. Then use the resulting hypothesis.
-/
private theorem isUnit_inverse_character_sub_one (hD : D.Good) : IsUnit (((D.Psi⁻¹ D.g0 : c.Oˣ) : c.O) - 1) := by
  rw [MonoidHom.inv_apply]
  have h1 : IsUnit (1 - (D.Psi D.g0 : c.O)) := by
    rw [← residue_ne_zero_iff_isUnit, map_sub, map_one]
    exact fun h => hD.genElt_Psi (sub_eq_zero.1 h).symm
  have := (Units.isUnit (D.Psi D.g0)⁻¹).mul h1
  rwa [mul_sub, mul_one, Units.inv_mul] at this

/- English proof (translation)
Take `⟨-, -, -, -, hP, -, hinj, -⟩` from `facts D hD`. Establish `hθ1 : ∀ g, D.Psi⁻¹ g = 1 ↔ D.Psi g = 1` using `fun g => by rw [MonoidHom.inv_apply, inv_eq_one]`. Establish `hvS : v ∈ D.S`. Break down `Finset.mem_insert.1 hv with h | h` into its components or cases. Conclude with `h ▸ hD.l_mem`.

Use `⟨Chr.shaFam_mono (Finset.dvd_prod_of_mem (fun p => p) hvS) (Or.inl ⟨D.pl v, hD.pl_over v (hD.S_prime v hvS), rfl⟩), ?_⟩` and prove the remaining obligations. Break down `Finset.mem_insert.1 hv with h | h` into its components or cases. Rewrite using `[h]`. Use `⟨D.s0, D.s0.2, fun h => ?_⟩` and prove the remaining obligations. Establish `h1 : D.ps 1 D.s0 = D.ps 3 D.s0` using `(hθ1 _).1 h`.

Establish `h2 : (1 : Fin 4) = 3` using `hinj (congrArg Units.val h1)`. Conclude with `absurd h2 (by decide)`. Assume the negation of the conclusion as `hne`. Establish `h1 : (D.Ip v).map D.ψ = ⊥`. Rewrite using `[Subgroup.map_eq_bot_iff]`.

Introduce `s hs`. Assume the negation of the conclusion as `h2`. Conclude with `hne ⟨s, hs.1, fun h3 => h2 (((hP v h s hs).2.1).symm.trans ((hθ1 _).1 h3))⟩`. Establish `h3 : l ∣ Nat.card ((D.Ip v).map D.ψ)` using `by classical exact (Finset.mem_filter.1 h).2.2`. Rewrite `h3` using `[h1, Subgroup.card_bot]`.

Conclude with `(Fact.out : l.Prime).one_lt.ne' (Nat.dvd_one.1 h3)`.
-/
private theorem local_group_in_family_nontrivial (hD : D.Good) (v : ℕ) (hv : v ∈ D.T) :
    D.Gp v ∈ shaFam ℚ Ω (∏ p ∈ D.S, p) ∧ ∃ s ∈ D.Gp v, D.Psi⁻¹ s ≠ 1 := by
  obtain ⟨-, -, -, -, hP, -, hinj, -⟩ := facts D hD
  have hθ1 : ∀ g, D.Psi⁻¹ g = 1 ↔ D.Psi g = 1 := fun g => by rw [MonoidHom.inv_apply, inv_eq_one]
  have hvS : v ∈ D.S := by
    rcases Finset.mem_insert.1 hv with h | h
    · exact h ▸ hD.l_mem
    · classical exact (Finset.mem_filter.1 h).1
  refine ⟨Chr.shaFam_mono (Finset.dvd_prod_of_mem (fun p => p) hvS)
    (Or.inl ⟨D.pl v, hD.pl_over v (hD.S_prime v hvS), rfl⟩), ?_⟩
  rcases Finset.mem_insert.1 hv with h | h
  · rw [h]
    refine ⟨D.s0, D.s0.2, fun h => ?_⟩
    have h1 : D.ps 1 D.s0 = D.ps 3 D.s0 := (hθ1 _).1 h
    have h2 : (1 : Fin 4) = 3 := hinj (congrArg Units.val h1)
    exact absurd h2 (by decide)
  · by_contra hne
    have h1 : (D.Ip v).map D.ψ = ⊥ := by
      rw [Subgroup.map_eq_bot_iff]
      intro s hs
      by_contra h2
      exact hne ⟨s, hs.1, fun h3 => h2 (((hP v h s hs).2.1).symm.trans ((hθ1 _).1 h3))⟩
    have h3 : l ∣ Nat.card ((D.Ip v).map D.ψ) := by classical exact (Finset.mem_filter.1 h).2.2
    rw [h1, Subgroup.card_bot] at h3
    exact (Fact.out : l.Prime).one_lt.ne' (Nat.dvd_one.1 h3)

/- English proof (translation)
Establish `hθ : D.Psi⁻¹ = D.ψ⁻¹ * chiO ℚ Ω l c.O ^ (-(D.e : ℤ))` using `Chr.Psi_inv l D.e D.ψ`. Establish `hker : (D.ψ⁻¹).ker = D.ψ.ker`. Use extensionality with `g`. Rewrite using `[MonoidHom.mem_ker, MonoidHom.mem_ker, MonoidHom.inv_apply, inv_eq_one]`. Establish `hc` using `(contTw ℚ Ω l).2.2 c.O D.ψ⁻¹ (-(D.e : ℤ)) (by rw [hker]; exact hD.psi_open)`.

Rewrite `hc` using `[← hθ]`. Conclude with `(continuous_prod_of_discrete_right.1 hc) m`.
-/
private theorem cont_Psi (hD : D.Good) (m : QO l c.O) : Continuous fun g => ((D.Psi⁻¹ g : c.Oˣ) : c.O) • m := by
  have hθ : D.Psi⁻¹ = D.ψ⁻¹ * chiO ℚ Ω l c.O ^ (-(D.e : ℤ)) := Chr.Psi_inv l D.e D.ψ
  have hker : (D.ψ⁻¹).ker = D.ψ.ker := by
    ext g
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, MonoidHom.inv_apply, inv_eq_one]
  have hc := (contTw ℚ Ω l).2.2 c.O D.ψ⁻¹ (-(D.e : ℤ)) (by rw [hker]; exact hD.psi_open)
  rw [← hθ] at hc
  exact (continuous_prod_of_discrete_right.1 hc) m

/- English proof (translation)
Substitute `hρ` using the available equality. Establish `hU` using `(facts D hD).2.2.1 1`. Establish `q1` using `(ML.qoCyc l c.O).2.1`. Establish `q2` using `(ML.qoCyc l c.O).2.2.1`. Establish `HH` using `fun b hb hk => main_abs (W := QO l c.O) D.Psi⁻¹ (cont_Psi D hD) D.g0 (isUnit_inverse_character_sub_one D hD) (shaFam ℚ Ω (∏ p ∈ D.S, p)) b hb hk D.T D.Gp (local_group_in_family_nontrivial D hD) (fun a ha => (q1 a ha).imp fun w hw => ⟨hw, q2 a w ha hw⟩)`.

Use `(kill_of_len hfin).elim fun b hb => (HH b hb.1 hb.2).imp fun a h => ⟨h.1, h.2.imp fun Z hZ => ⟨hZ.1, fun x => ?_⟩⟩` and prove the remaining obligations. Establish `H` using `hZ.2 x`. Use `⟨H.1, H.2.1, fun A hA g hg hr => H.2.2.1 _ (Or.inr ⟨A, rfl⟩) g hg ?_, H.2.2.2.1, H.2.2.2.2⟩` and prove the remaining obligations. Rewrite using `[MonoidHom.inv_apply, inv_eq_one]`. Conclude with `hU A hA g hg hr`.
-/
private theorem conc (hD : D.Good) (ρ : Representation c.O (G ℚ Ω) (QO l c.O)) (hρ : ρ = twist₂ l D.Psi⁻¹)
    (hfin : Module.length c.O (ShaU ρ (∏ p ∈ D.S, p) ⊤) ≠ ⊤) :
    ∃ a : c.O, a ≠ 0 ∧ ∃ Z : ShaU ρ (∏ p ∈ D.S, p) ⊤ →+ (G ℚ Ω → c.O ⧸ Ideal.span {a}), Function.Injective Z ∧
      ∀ x, D.ShaCoc a (Z x) := by
  subst hρ
  have hU := (facts D hD).2.2.1 1
  have q1 := (ML.qoCyc l c.O).2.1
  have q2 := (ML.qoCyc l c.O).2.2.1
  have HH := fun b hb hk => main_abs (W := QO l c.O) D.Psi⁻¹ (cont_Psi D hD) D.g0 (isUnit_inverse_character_sub_one D hD)
    (shaFam ℚ Ω (∏ p ∈ D.S, p)) b hb hk D.T D.Gp (local_group_in_family_nontrivial D hD)
    (fun a ha => (q1 a ha).imp fun w hw => ⟨hw, q2 a w ha hw⟩)
  refine (kill_of_len hfin).elim fun b hb => (HH b hb.1 hb.2).imp fun a h => ⟨h.1, h.2.imp fun Z hZ => ⟨hZ.1, fun x => ?_⟩⟩
  have H := hZ.2 x
  refine ⟨H.1, H.2.1, fun A hA g hg hr => H.2.2.1 _ (Or.inr ⟨A, rfl⟩) g hg ?_, H.2.2.2.1, H.2.2.2.2⟩
  rw [MonoidHom.inv_apply, inv_eq_one]
  exact hU A hA g hg hr

end Conc

/- English proof (translation)
Introduce `Ω _ _ _ l _ c D hD hS`. Establish `hfin : D.sha ≠ ⊤` using `ne_top_of_le_ne_top (hS c D.ψ hD.psi_open D.e (le_trans one_le_two hD.two_le)) (Chr.VS_anti l (Finset.dvd_prod_of_mem (fun p => p) hD.l_mem) D.e D.ψ)`. Conclude with `⟨hfin, conc D hD _ (Chr.rho_eq l D.e D.ψ) hfin⟩`.
-/
theorem UpperTheory.V.GradeZeroInterpolatingElement.shaCoc :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → SoFin Ω l → D.sha ≠ ⊤ ∧ ∃ a : c.O, a ≠ 0 ∧ ∃ Z : ShaU (Chr.rho l D.e D.ψ) (∏ p ∈ D.S, p) ⊤ →+ (G ℚ Ω → c.O ⧸ Ideal.span {a}), Function.Injective Z ∧ ∀ x, D.ShaCoc a (Z x) := by
  intro Ω _ _ _ l _ c D hD hS
  have hfin : D.sha ≠ ⊤ := ne_top_of_le_ne_top (hS c D.ψ hD.psi_open D.e (le_trans one_le_two hD.two_le))
    (Chr.VS_anti l (Finset.dvd_prod_of_mem (fun p => p) hD.l_mem) D.e D.ψ)
  exact ⟨hfin, conc D hD _ (Chr.rho_eq l D.e D.ψ) hfin⟩
