import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ShaFamMono
import Development.AutomorphicArithmetic.AutomorphicVarieties.PartsSign
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.RootVal
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.KerResAb
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.QoFacts

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Chr

/- English proof (translation)
Use `set K : Subgroup U := U'.subgroupOf U with hK`. Use `set N := LinearMap.ker ((n : R) • (LinearMap.id : M →ₗ[R] M)) with hN`. Establish `hadd : ∀ z ∈ Z1U ρ U, ∀ a b : U, z (a * b) = z a + z b`. Introduce `z hz a b`. Use `((mem_Z1_iff_cocycle (ρ.comp U.subtype) z).mp hz).2 a b` as an intermediate fact.

Rewrite using `[this, MonoidHom.comp_apply, Subgroup.coe_subtype, hρ a a.2]`. Establish `hone : ∀ z ∈ Z1U ρ U, z 1 = 0`. Introduce `z hz`. Use `hadd z hz 1 1` as an intermediate fact. Rewrite `this` using `[mul_one]`.

Conclude with `left_eq_add.mp this`. Establish `hinv : ∀ z ∈ Z1U ρ U, ∀ a : U, z a⁻¹ = - z a`. Introduce `z hz a`. Use `hadd z hz a a⁻¹` as an intermediate fact. Rewrite `this` using `[mul_inv_cancel, hone z hz]`.

Conclude with `eq_neg_of_add_eq_zero_right this.symm`. Establish `hpow : ∀ z ∈ Z1U ρ U, ∀ a : U, ∀ k : ℕ, z (a ^ k) = k • z a`. Introduce `z hz a k`. Proceed by induction on `k with`. Consider the case `zero => rw [pow_zero, hone z hz, zero_smul]`.

Consider the case `succ k ih => rw [pow_succ, hadd z hz, ih, succ_nsmul]`. Establish `hB : ∀ z ∈ Submodule.comap (Z1U ρ U).subtype (B1 (ρ.comp U.subtype)), (z : U → M) = 0`. Introduce `z hz`. Rewrite `hz` using `[Submodule.mem_comap, B1, LinearMap.mem_range]`. Take `⟨m, hm⟩` from `hz`.

Use function extensionality and compare the values at `u`. Rewrite `hm` using `[Submodule.coe_subtype]`. Rewrite using `[← hm, amitsur_d0_apply, MonoidHom.comp_apply, Subgroup.coe_subtype, hρ u u.2, sub_self]`. Both sides reduce to the same expression. Set `ev : (Z1U ρ U) →ₗ[R] (U ⧸ K → M)` to `LinearMap.pi (fun q => (LinearMap.proj (Quotient.out q) : (U → M) →ₗ[R] M) ∘ₗ (Z1U ρ U).subtype)`.

Establish `hev : ∀ z q, ev z q = (z : U → M) (Quotient.out q)` using `fun z q => rfl`. Set `Φ : H1U ρ U →ₗ[R] (U ⧸ K → M)` to `(Submodule.comap (Z1U ρ U).subtype (B1 (ρ.comp U.subtype))).liftQ ev (by`. Introduce `z hz`. Rewrite using `[LinearMap.mem_ker]`. Use function extensionality and compare the values at `q`.

Rewrite using `[hev, hB z hz]`. Use the proof step `rfl)`. Establish `hΦ : ∀ z q, Φ (Submodule.Quotient.mk z) q = (z : U → M) (Quotient.out q)` using `fun z q => rfl`. Establish `hvan : ∀ z : Z1U ρ U, resU ρ h (Submodule.Quotient.mk z) = 0 → ∀ u : U, (u : G) ∈ U' → (z : U → M) u = 0`. Introduce `z hz u hu`.

Take `⟨m, hm⟩` from `(resU_mk_eq_zero ρ h z).mp hz`. Use `hm ⟨(u : G), hu⟩` as an intermediate fact. Rewrite `this` using `[hρ _ (h hu), sub_self]`. Conclude with `this`. Establish `key : ∀ x ∈ LinearMap.ker (resU ρ h), ∀ q, Φ x q ∈ N`.

Introduce `x hx q`. Take `⟨z, rfl⟩` from `Submodule.Quotient.mk_surjective _ x`. Rewrite `hx` using `[LinearMap.mem_ker]`. Rewrite using `[hΦ, hN, LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply, Nat.cast_smul_eq_nsmul, ← hpow z z.2]`. Conclude with `hvan z hx _ (hn _ (Quotient.out q).2)`.

Set `Ψ : LinearMap.ker (resU ρ h) →ₗ[R] (U ⧸ K → N)` to `LinearMap.pi (fun q => LinearMap.codRestrict N ((LinearMap.proj q : (U ⧸ K → M) →ₗ[R] M) ∘ₗ Φ ∘ₗ (LinearMap.ker (resU ρ h)).subtype) (fun x => key x.1 x.2 q))`. Establish `hΨ : Function.Injective Ψ`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce and unpack `⟨x, hxk⟩ hx0`. Take `⟨z, rfl⟩` from `Submodule.Quotient.mk_surjective _ x`.

Establish `hq : ∀ q : U ⧸ K, (z : U → M) (Quotient.out q) = 0`. Introduce `q`. Use `congrArg (fun f => ((f q : N) : M)) hx0` as an intermediate fact. Conclude with `this`. Establish `hz : (z : U → M) = 0`.

Use function extensionality and compare the values at `u`. Take `⟨k, hk⟩` from `QuotientGroup.mk_out_eq_mul K u`. Establish `hkU : ((k : U) : G) ∈ U'` using `Subgroup.mem_subgroupOf.mp k.2`. Establish `hu : u = Quotient.out (QuotientGroup.mk u : U ⧸ K) * (k : U)⁻¹`. Rewrite using `[hk]`.

Use `group`. Rewrite using `[hu, hadd z z.2, hq, hinv z z.2, hvan z hxk _ hkU, neg_zero, add_zero]`. Both sides reduce to the same expression. Establish `hz' : z = 0` using `Subtype.ext hz`. Substitute `hz'` using the available equality.

Both sides reduce to the same expression. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Module.length_pi_of_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_eq_nat_card, Fintype.card_eq_nat_card]`.
-/
private theorem kerFin_triv {R G M : Type} [CommRing R] [Group G] [TopologicalSpace G] [AddCommGroup M] [Module R M]
    [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M] (ρ : Representation R G M)
    (U' U : Subgroup G) (h : U' ≤ U) (hρ : ∀ u ∈ U, ∀ m, ρ u m = m) (n : ℕ) (hn : ∀ u ∈ U, u ^ n ∈ U')
    [Fintype (U ⧸ U'.subgroupOf U)] :
    Module.length R (LinearMap.ker (resU ρ h)) ≤ (Fintype.card (U ⧸ U'.subgroupOf U) : ℕ∞) *
      Module.length R (LinearMap.ker ((n : R) • (LinearMap.id : M →ₗ[R] M))) := by
  classical
  set K : Subgroup U := U'.subgroupOf U with hK
  set N := LinearMap.ker ((n : R) • (LinearMap.id : M →ₗ[R] M)) with hN
  have hadd : ∀ z ∈ Z1U ρ U, ∀ a b : U, z (a * b) = z a + z b := by
    intro z hz a b
    have := ((mem_Z1_iff_cocycle (ρ.comp U.subtype) z).mp hz).2 a b
    rw [this, MonoidHom.comp_apply, Subgroup.coe_subtype, hρ a a.2]
  have hone : ∀ z ∈ Z1U ρ U, z 1 = 0 := by
    intro z hz
    have := hadd z hz 1 1
    rw [mul_one] at this
    exact left_eq_add.mp this
  have hinv : ∀ z ∈ Z1U ρ U, ∀ a : U, z a⁻¹ = - z a := by
    intro z hz a
    have := hadd z hz a a⁻¹
    rw [mul_inv_cancel, hone z hz] at this
    exact eq_neg_of_add_eq_zero_right this.symm
  have hpow : ∀ z ∈ Z1U ρ U, ∀ a : U, ∀ k : ℕ, z (a ^ k) = k • z a := by
    intro z hz a k
    induction k with
    | zero => rw [pow_zero, hone z hz, zero_smul]
    | succ k ih => rw [pow_succ, hadd z hz, ih, succ_nsmul]
  have hB : ∀ z ∈ Submodule.comap (Z1U ρ U).subtype (B1 (ρ.comp U.subtype)), (z : U → M) = 0 := by
    intro z hz
    rw [Submodule.mem_comap, B1, LinearMap.mem_range] at hz
    obtain ⟨m, hm⟩ := hz
    funext u
    rw [Submodule.coe_subtype] at hm
    rw [← hm, amitsur_d0_apply, MonoidHom.comp_apply, Subgroup.coe_subtype, hρ u u.2, sub_self]
    rfl
  let ev : (Z1U ρ U) →ₗ[R] (U ⧸ K → M) :=
    LinearMap.pi (fun q => (LinearMap.proj (Quotient.out q) : (U → M) →ₗ[R] M) ∘ₗ (Z1U ρ U).subtype)
  have hev : ∀ z q, ev z q = (z : U → M) (Quotient.out q) := fun z q => rfl
  let Φ : H1U ρ U →ₗ[R] (U ⧸ K → M) :=
    (Submodule.comap (Z1U ρ U).subtype (B1 (ρ.comp U.subtype))).liftQ ev (by
      intro z hz
      rw [LinearMap.mem_ker]
      funext q
      rw [hev, hB z hz]
      rfl)
  have hΦ : ∀ z q, Φ (Submodule.Quotient.mk z) q = (z : U → M) (Quotient.out q) := fun z q => rfl
  have hvan : ∀ z : Z1U ρ U, resU ρ h (Submodule.Quotient.mk z) = 0 → ∀ u : U, (u : G) ∈ U' → (z : U → M) u = 0 := by
    intro z hz u hu
    obtain ⟨m, hm⟩ := (resU_mk_eq_zero ρ h z).mp hz
    have := hm ⟨(u : G), hu⟩
    rw [hρ _ (h hu), sub_self] at this
    exact this
  have key : ∀ x ∈ LinearMap.ker (resU ρ h), ∀ q, Φ x q ∈ N := by
    intro x hx q
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [LinearMap.mem_ker] at hx
    rw [hΦ, hN, LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply, Nat.cast_smul_eq_nsmul,
      ← hpow z z.2]
    exact hvan z hx _ (hn _ (Quotient.out q).2)
  let Ψ : LinearMap.ker (resU ρ h) →ₗ[R] (U ⧸ K → N) :=
    LinearMap.pi (fun q => LinearMap.codRestrict N
      ((LinearMap.proj q : (U ⧸ K → M) →ₗ[R] M) ∘ₗ Φ ∘ₗ (LinearMap.ker (resU ρ h)).subtype)
      (fun x => key x.1 x.2 q))
  have hΨ : Function.Injective Ψ := by
    rw [injective_iff_map_eq_zero]
    rintro ⟨x, hxk⟩ hx0
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have hq : ∀ q : U ⧸ K, (z : U → M) (Quotient.out q) = 0 := by
      intro q
      have := congrArg (fun f => ((f q : N) : M)) hx0
      exact this
    have hz : (z : U → M) = 0 := by
      funext u
      obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K u
      have hkU : ((k : U) : G) ∈ U' := Subgroup.mem_subgroupOf.mp k.2
      have hu : u = Quotient.out (QuotientGroup.mk u : U ⧸ K) * (k : U)⁻¹ := by
        rw [hk]; group
      rw [hu, hadd z z.2, hq, hinv z z.2, hvan z hxk _ hkU, neg_zero, add_zero]
      rfl
    have hz' : z = 0 := Subtype.ext hz
    subst hz'
    rfl
  calc Module.length R (LinearMap.ker (resU ρ h)) ≤ Module.length R (U ⧸ K → N) :=
        Module.length_le_of_injective Ψ hΨ
    _ = _ := by
      rw [Module.length_pi_of_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        Fintype.card_eq_nat_card, Fintype.card_eq_nat_card]

/- English proof (translation)
Use `set K : Subgroup U := U'.subgroupOf U with hK`. Establish `hfi : K.FiniteIndex` using `⟨by rw [hK]; exact h0⟩`. Use `haveI : Finite (U ⧸ K) := Subgroup.finite_quotient_of_finiteIndex`. Use `letI : Fintype (U ⧸ K) := Fintype.ofFinite _`. Use `⟨Finset.univ.image (fun q : U ⧸ K => ((Quotient.out q : U) : G)), ?_, ?_, ?_⟩` and prove the remaining obligations.

Introduce `x hx`. Simplify using `only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at hx`. Take `⟨q, rfl⟩` from `hx`. Conclude with `(Quotient.out q).2`. Use `(Finset.card_image_le).trans ?_` and prove the remaining obligations.

Rewrite using `[Finset.card_univ, ← Nat.card_eq_fintype_card, Subgroup.relIndex, ← hK, Subgroup.index]`. Introduce `u hu`. Take `⟨k, hk⟩` from `QuotientGroup.mk_out_eq_mul K (⟨u, hu⟩ : U)`. Establish `hkU' : ((k : U) : G) ∈ U'` using `Subgroup.mem_subgroupOf.mp k.2`. Establish `hout : ((Quotient.out (QuotientGroup.mk (⟨u, hu⟩ : U) : U ⧸ K) : U) : G) ∈ Subgroup.closure ((Finset.univ.image (fun q : U ⧸ K => ((Quotient.out q : U) : G)) : Finset G) : Set G)`.

Apply `Subgroup.subset_closure` to reduce the goal to its premises. Simplify using the standard rewrite rules. Establish `heq : u = ((Quotient.out (QuotientGroup.mk (⟨u, hu⟩ : U) : U ⧸ K) : U) : G) * ((k : U) : G)⁻¹`. Use `congrArg (fun x : U => (x : G)) hk` as an intermediate fact. Simplify using `only [Subgroup.coe_mul] at this`.

Rewrite using `[this]`. Use `group`. Rewrite using `[heq]`. Conclude with `Subgroup.mul_mem_sup hout (U'.inv_mem hkU')`.
-/
private theorem exists_doubleCoset_section {G : Type} [Group G] (U' U : Subgroup G) (h0 : U'.relIndex U ≠ 0) :
    ∃ T : Finset G, (T : Set G) ⊆ U ∧ T.card ≤ U'.relIndex U ∧ U ≤ Subgroup.closure (T : Set G) ⊔ U' := by
  classical
  set K : Subgroup U := U'.subgroupOf U with hK
  have hfi : K.FiniteIndex := ⟨by rw [hK]; exact h0⟩
  haveI : Finite (U ⧸ K) := Subgroup.finite_quotient_of_finiteIndex
  letI : Fintype (U ⧸ K) := Fintype.ofFinite _
  refine ⟨Finset.univ.image (fun q : U ⧸ K => ((Quotient.out q : U) : G)), ?_, ?_, ?_⟩
  · intro x hx
    simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at hx
    obtain ⟨q, rfl⟩ := hx
    exact (Quotient.out q).2
  · refine (Finset.card_image_le).trans ?_
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card, Subgroup.relIndex, ← hK, Subgroup.index]
  · intro u hu
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K (⟨u, hu⟩ : U)
    have hkU' : ((k : U) : G) ∈ U' := Subgroup.mem_subgroupOf.mp k.2
    have hout : ((Quotient.out (QuotientGroup.mk (⟨u, hu⟩ : U) : U ⧸ K) : U) : G) ∈ Subgroup.closure
        ((Finset.univ.image (fun q : U ⧸ K => ((Quotient.out q : U) : G)) : Finset G) : Set G) := by
      apply Subgroup.subset_closure
      simp
    have heq : u = ((Quotient.out (QuotientGroup.mk (⟨u, hu⟩ : U) : U ⧸ K) : U) : G) * ((k : U) : G)⁻¹ := by
      have := congrArg (fun x : U => (x : G)) hk
      simp only [Subgroup.coe_mul] at this
      rw [this]; group
    rw [heq]
    exact Subgroup.mul_mem_sup hout (U'.inv_mem hkU')

/- English proof (translation)
Introduce `l _ O _ _ _ _ _ G _ _ _ θ hc U' U h hker hcomm n hn hdiv`. Establish `h0 : U'.relIndex U ≠ 0` using `fun hz => hn (Nat.eq_zero_of_zero_dvd (hz ▸ hdiv))`. Use `set K : Subgroup U := U'.subgroupOf U with hK`. Establish `hfi : K.FiniteIndex` using `⟨by rw [hK]; exact h0⟩`. Use `haveI : Finite (U ⧸ K) := Subgroup.finite_quotient_of_finiteIndex`.

Use `letI : Fintype (U ⧸ K) := Fintype.ofFinite _`. Establish `hnorm : K.Normal`. Prove the components needed by the constructor for the conclusion. Introduce `k hk g`. Rewrite `hk`, the goal using `[hK, Subgroup.mem_subgroupOf]`.

Establish `hcm` using `hcomm g g.2 k k.2`. Establish `: ((g * k * g⁻¹ : U) : G) = ((g : G) * k * (g : G)⁻¹ * (k : G)⁻¹) * k` using `by push_cast; group`. Rewrite using `[this]`. Conclude with `U'.mul_mem hcm hk`. Establish `hcardK : Nat.card (U ⧸ K) = U'.relIndex U`.

Rewrite using `[Subgroup.relIndex, ← hK, Subgroup.index]`. Establish `hpowU : ∀ u ∈ U, u ^ n ∈ U'`. Introduce `u hu`. Take `⟨c, hc'⟩` from `hdiv`. Establish `h1 : (QuotientGroup.mk (⟨u, hu⟩ : U) : U ⧸ K) ^ (U'.relIndex U) = 1`.

Rewrite using `[← hcardK]`. Conclude with `pow_card_eq_one'`. Rewrite `h1` using `[← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, hK, Subgroup.mem_subgroupOf]`. Rewrite using `[hc', pow_mul]`. Establish `: ((⟨u, hu⟩ : U) ^ (U'.relIndex U) : U) = (u ^ (U'.relIndex U) : G)` using `by simp`.

Rewrite `h1` using `[this]`. Conclude with `U'.pow_mem h1 c`. Establish `hrel_le : U'.relIndex U ≤ n` using `Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hdiv`. Take `⟨_, hζ, heOtop, _⟩` from `rootVal l O n hn`. Establish `hact : ∀ g m, twist₂ l θ g m = ((θ g : Oˣ) : O) • m` using `fun g m => by`.

Rewrite using `[twist₂, scalRep_apply]`. Distinguish the cases in `htriv : U ≤ θ.ker`. Establish `hρ : ∀ u ∈ U, ∀ m, twist₂ l θ u m = m`. Introduce `u hu m`. Rewrite using `[hact, htriv hu, Units.val_one, one_smul]`.

Use `kerFin_triv (twist₂ l θ) U' U h hρ n hpowU` as an intermediate fact. Use `this.trans ?_` and prove the remaining obligations. Rewrite using `[(qoFacts l O).2.2.2, (rootVal l O n hn).1, Fintype.card_eq_nat_card, hcardK]`. Use `push_cast`. Rewrite using `[← mul_assoc]`.

Use `gcongr`. Take `⟨g, hg, hgk⟩` from `SetLike.not_le_iff_exists.mp htriv set ζ : O := ((θ g : Oˣ) : O) with hζdef`. Establish `hθn : (θ g) ^ n = 1`. Rewrite using `[← map_pow]`. Conclude with `hker (hpowU g hg)`.

Establish `hζn : ζ ^ n = 1`. Rewrite using `[hζdef, ← Units.val_pow_eq_pow_val, hθn, Units.val_one]`. Establish `hζ1 : ζ ≠ 1`. Introduce `h1`. Apply `hgk` to reduce the goal to its premises.

Rewrite using `[MonoidHom.mem_ker]`. Conclude with `Units.ext h1`. Establish `hsub : H0U (twist₂ l θ) U ≤ ((ζ - 1) • LinearMap.id : QO l O →ₗ[O] QO l O).ker`. Introduce `m hm`. Rewrite `hm` using `[H0U, mem_riemannRochSpace_iff_regularAt_everywhere]`.

Establish `h1` using `hm ⟨g, hg⟩`. Rewrite `h1` using `[MonoidHom.comp_apply, Subgroup.coe_subtype, hact]`. Rewrite using `[LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply, sub_smul, one_smul, hζdef, h1, sub_self]`. Establish `hbound : Module.length O (H0U (twist₂ l θ) U) ≤ (n.factorization l : ℕ∞) * eO l O`. Use `(Module.length_le_of_injective (Submodule.inclusion hsub) (Submodule.inclusion_injective hsub)).trans ?_` and prove the remaining obligations.

Rewrite using `[(qoFacts l O).2.2.2]`. Conclude with `hζ ζ hζn hζ1`. Take `⟨T, hTU, hTcard, hTcl⟩` from `exists_doubleCoset_section U' U h0`. Establish `key` using `kerResAb O G (QO l O) (twist₂ l θ) hc (qoFacts l O).1 (fun g => ⟨(θ g : O), fun m => hact g m⟩) U' U h hcomm T hTU (hTcl.trans (Subgroup.le_topologicalClosure _))`. Use `key.trans ?_` and prove the remaining obligations.

Establish `hle : T.card ≤ n` using `hTcard.trans hrel_le`. Combine the equalities or inequalities in the displayed calculation. Use `push_cast`. Rewrite using `[mul_assoc]`.
-/
theorem UpperTheory.V.Chr.kerFin :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (θ : G →* Oˣ), ContAction (twist₂ l θ) →
          ∀ (U' U : Subgroup G) (h : U' ≤ U), U' ≤ θ.ker → (∀ a ∈ U, ∀ b ∈ U, a * b * a⁻¹ * b⁻¹ ∈ U') → ∀ n : ℕ, n ≠ 0 → U'.relIndex U ∣ n →
          Module.length O (LinearMap.ker (resU (twist₂ l θ) h)) ≤ ((n * n.factorization l : ℕ) : ℕ∞) * eO l O := by
  intro l _ O _ _ _ _ _ G _ _ _ θ hc U' U h hker hcomm n hn hdiv
  classical
  have h0 : U'.relIndex U ≠ 0 := fun hz => hn (Nat.eq_zero_of_zero_dvd (hz ▸ hdiv))
  set K : Subgroup U := U'.subgroupOf U with hK
  have hfi : K.FiniteIndex := ⟨by rw [hK]; exact h0⟩
  haveI : Finite (U ⧸ K) := Subgroup.finite_quotient_of_finiteIndex
  letI : Fintype (U ⧸ K) := Fintype.ofFinite _
  have hnorm : K.Normal := by
    constructor
    intro k hk g
    rw [hK, Subgroup.mem_subgroupOf] at hk ⊢
    have hcm := hcomm g g.2 k k.2
    have : ((g * k * g⁻¹ : U) : G) = ((g : G) * k * (g : G)⁻¹ * (k : G)⁻¹) * k := by
      push_cast; group
    rw [this]
    exact U'.mul_mem hcm hk
  have hcardK : Nat.card (U ⧸ K) = U'.relIndex U := by
    rw [Subgroup.relIndex, ← hK, Subgroup.index]
  have hpowU : ∀ u ∈ U, u ^ n ∈ U' := by
    intro u hu
    obtain ⟨c, hc'⟩ := hdiv
    have h1 : (QuotientGroup.mk (⟨u, hu⟩ : U) : U ⧸ K) ^ (U'.relIndex U) = 1 := by
      rw [← hcardK]; exact pow_card_eq_one'
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, hK, Subgroup.mem_subgroupOf] at h1
    rw [hc', pow_mul]
    have : ((⟨u, hu⟩ : U) ^ (U'.relIndex U) : U) = (u ^ (U'.relIndex U) : G) := by simp
    rw [this] at h1
    exact U'.pow_mem h1 c
  have hrel_le : U'.relIndex U ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hdiv
  obtain ⟨_, hζ, heOtop, _⟩ := rootVal l O n hn
  have hact : ∀ g m, twist₂ l θ g m = ((θ g : Oˣ) : O) • m := fun g m => by
    rw [twist₂, scalRep_apply]
  by_cases htriv : U ≤ θ.ker
  · have hρ : ∀ u ∈ U, ∀ m, twist₂ l θ u m = m := by
      intro u hu m
      rw [hact, htriv hu, Units.val_one, one_smul]
    have := kerFin_triv (twist₂ l θ) U' U h hρ n hpowU
    refine this.trans ?_
    rw [(qoFacts l O).2.2.2, (rootVal l O n hn).1, Fintype.card_eq_nat_card, hcardK]
    push_cast
    rw [← mul_assoc]
    gcongr
  · obtain ⟨g, hg, hgk⟩ := SetLike.not_le_iff_exists.mp htriv
    set ζ : O := ((θ g : Oˣ) : O) with hζdef
    have hθn : (θ g) ^ n = 1 := by
      rw [← map_pow]
      exact hker (hpowU g hg)
    have hζn : ζ ^ n = 1 := by
      rw [hζdef, ← Units.val_pow_eq_pow_val, hθn, Units.val_one]
    have hζ1 : ζ ≠ 1 := by
      intro h1
      apply hgk
      rw [MonoidHom.mem_ker]
      exact Units.ext h1
    have hsub : H0U (twist₂ l θ) U ≤ ((ζ - 1) • LinearMap.id : QO l O →ₗ[O] QO l O).ker := by
      intro m hm
      rw [H0U, mem_riemannRochSpace_iff_regularAt_everywhere] at hm
      have h1 := hm ⟨g, hg⟩
      rw [MonoidHom.comp_apply, Subgroup.coe_subtype, hact] at h1
      rw [LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply, sub_smul, one_smul, hζdef, h1, sub_self]
    have hbound : Module.length O (H0U (twist₂ l θ) U) ≤ (n.factorization l : ℕ∞) * eO l O := by
      refine (Module.length_le_of_injective (Submodule.inclusion hsub) (Submodule.inclusion_injective hsub)).trans ?_
      rw [(qoFacts l O).2.2.2]
      exact hζ ζ hζn hζ1
    obtain ⟨T, hTU, hTcard, hTcl⟩ := exists_doubleCoset_section U' U h0
    have key := kerResAb O G (QO l O) (twist₂ l θ) hc (qoFacts l O).1
      (fun g => ⟨(θ g : O), fun m => hact g m⟩) U' U h hcomm T hTU
      (hTcl.trans (Subgroup.le_topologicalClosure _))
    refine key.trans ?_
    have hle : T.card ≤ n := hTcard.trans hrel_le
    calc (T.card : ℕ∞) * Module.length O (H0U (twist₂ l θ) U) ≤ (n : ℕ∞) * ((n.factorization l : ℕ∞) * eO l O) := by
          gcongr
      _ = ((n * n.factorization l : ℕ) : ℕ∞) * eO l O := by
          push_cast
          rw [mul_assoc]
