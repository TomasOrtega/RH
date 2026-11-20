import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.KatoUse
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.AdRepBaseLiftApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.DatFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.FdAdjoinRange
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsNeOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsIntBasis
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Z1fCoef
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IotaFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ArtKer
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ToGalDict
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Places
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.GalEmbTop
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ClsFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.PartsConj
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PoitouTateDualityOfNormalised

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.GalOfCusp Matrix IsLocalRing
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.U3

/- English proof (translation)
Use `haveI : Finite (Set.range f) := (Set.finite_range _).to_subtype`. Conclude with `IntermediateField.finiteDimensional_adjoin fun z _ => (Algebra.IsAlgebraic.isAlgebraic z).isIntegral`.
-/
private theorem fd_adjoin_range (l : ℕ) [Fact l.Prime] {ι : Type} [Finite ι] (f : ι → PadicAlgCl l) :
    FiniteDimensional ℚ_[l] (IntermediateField.adjoin ℚ_[l] (Set.range f)) := by
  haveI : Finite (Set.range f) := (Set.finite_range _).to_subtype
  exact IntermediateField.finiteDimensional_adjoin fun z _ =>
      (Algebra.IsAlgebraic.isAlgebraic z).isIntegral

/- English proof (translation)
Use `haveI : Finite (Γ ⧸ ψ.ker) := Subgroup.quotient_finite_of_isOpen _ hψ`. Use `⟨_, fd_adjoin_range l (fun q : Γ ⧸ ψ.ker => (ψ q.out : PadicAlgCl l)), fun g => ?_⟩` and prove the remaining obligations. Take `⟨h, hh⟩` from `QuotientGroup.mk_out_eq_mul ψ.ker g`. Use `IntermediateField.subset_adjoin _ _ ⟨(g : Γ ⧸ ψ.ker), ?_⟩` and prove the remaining obligations. Establish `h1 : ψ (h : Γ) = 1` using `h.2`.

Simplify using `only [hh, map_mul, h1, mul_one]`.
-/
private theorem char_finext (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] (ψ : Γ →* (PadicAlgCl l)ˣ) (hψ : IsOpen (ψ.ker : Set Γ)) :
    ∃ K : IntermediateField ℚ_[l] (PadicAlgCl l), FiniteDimensional ℚ_[l] K ∧ ∀ g, (ψ g : PadicAlgCl l) ∈ K := by
  haveI : Finite (Γ ⧸ ψ.ker) := Subgroup.quotient_finite_of_isOpen _ hψ
  refine ⟨_, fd_adjoin_range l (fun q : Γ ⧸ ψ.ker => (ψ q.out : PadicAlgCl l)), fun g => ?_⟩
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul ψ.ker g
  refine IntermediateField.subset_adjoin _ _ ⟨(g : Γ ⧸ ψ.ker), ?_⟩
  have h1 : ψ (h : Γ) = 1 := h.2
  simp only [hh, map_mul, h1, mul_one]

open TensorProduct in

/- English proof (translation)
Take `⟨⟨hcc, hcoc⟩, x, hx⟩` from `hc`. Take `⟨S, rfl⟩` from `TensorProduct.exists_finset x`. Take `⟨T⟩` from `Loc.tiedP l`. Use `haveI : IsDomain (Loc.Bcr l) := GlobalTheory.RegularRing.isDomain_of_tied T (Loc.botExt l)`. Use `haveI := fd_adjoin_range l (fun p : S => p.1.1)`.

Set `E : IntermediateField ℚ_[l] (PadicAlgCl l)` to `E₀ ⊔ IntermediateField.adjoin ℚ_[l] (Set.range fun p : S => p.1.1)`. Establish `hκE : ∀ g, (κ g : PadicAlgCl l) ∈ E` using `fun g => (le_sup_left : E₀ ≤ E) (hκ g)`. Establish `hS : ∀ p ∈ S, p.1 ∈ E` using `fun p hp => (le_sup_right : _ ≤ E) (IntermediateField.subset_adjoin _ _ ⟨⟨p, hp⟩, rfl⟩)`. Take `⟨π, hπ⟩` from `LinearMap.exists_leftInverse_of_injective (Algebra.linearMap E (PadicAlgCl l)) (LinearMap.ker_eq_bot.2 (algebraMap E (PadicAlgCl l)).injective)`. Establish `hπ1 : ∀ y : E, π (y : PadicAlgCl l) = y` using `fun y => LinearMap.congr_fun hπ y`.

Set `κ' : H →* Eˣ` to `MonoidHom.toHomUnits { toFun := fun g => ⟨κ g, hκE g⟩ map_one' := Subtype.ext (by simp) map_mul' := fun g h => Subtype.ext (by simp) }`. Establish `hκ' : ∀ g, ((κ' g : E) : PadicAlgCl l) = κ g` using `fun g => rfl`. Establish `hπ2 : ∀ g y, π (κ g * y) = κ' g * π y` using `fun g y => map_smul π (κ' g : E) y`. Set `f : PadicAlgCl l →ₗ[ℚ_[l]] E` to `π.restrictScalars ℚ_[l]`. Set `i : E →ₗ[ℚ_[l]] PadicAlgCl l` to `E.val.toLinearMap`.

Establish `key : ∀ g (y : PadicAlgCl l ⊗[ℚ_[l]] Loc.Bcr l), LinearMap.rTensor (Loc.Bcr l) f (Loc.actC φ (Loc.chRep κ) g y) = Loc.actC φ (Loc.chRep κ') g (LinearMap.rTensor (Loc.Bcr l) f y)`. Introduce `g y`. Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a b => simp [Loc.actC, Loc.chRep, f, hπ2]`.

Consider the case `add a b ha hb => simp only [map_add, ha, hb]`. Establish `key' : ∀ g (y : E ⊗[ℚ_[l]] Loc.Bcr l), LinearMap.rTensor (Loc.Bcr l) i (Loc.actC φ (Loc.chRep κ') g y) = Loc.actC φ (Loc.chRep κ) g (LinearMap.rTensor (Loc.Bcr l) i y)`. Introduce `g y`. Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp`.

Consider the case `tmul a b => simp [Loc.actC, Loc.chRep, i, hκ']`. Consider the case `add a b ha hb => simp only [map_add, ha, hb]`. Use `set x := ∑ p ∈ S, p.1 ⊗ₜ[ℚ_[l]] p.2 with hxd`. Establish `hix : LinearMap.rTensor (Loc.Bcr l) i (LinearMap.rTensor (Loc.Bcr l) f x) = x`. Rewrite using `[hxd, map_sum, map_sum]`.

Use `Finset.sum_congr rfl fun p hp => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.rTensor_tmul, LinearMap.rTensor_tmul]`. Use `congr 1`. Conclude with `congrArg Subtype.val (hπ1 ⟨p.1, hS p hp⟩)`. Establish `hx' : ∀ g, f (c g) ⊗ₜ[ℚ_[l]] (1 : Loc.Bcr l) = Loc.actC φ (Loc.chRep κ') g (LinearMap.rTensor (Loc.Bcr l) f x) - LinearMap.rTensor (Loc.Bcr l) f x` using `fun g => by`.

Rewrite using `[← key, ← map_sub, ← hx g, LinearMap.rTensor_tmul]`. Establish `hcE : ∀ g, ((f (c g) : E) : PadicAlgCl l) = c g` using `fun g => by`. Establish `h1` using `congrArg (LinearMap.rTensor (Loc.Bcr l) i) (hx' g)`. Rewrite `h1` using `[map_sub, key', hix, ← hx g, LinearMap.rTensor_tmul]`. Conclude with `Algebra.TensorProduct.includeLeft_injective (R := ℚ_[l]) (S := ℚ_[l]) (B := Loc.Bcr l) (algebraMap ℚ_[l] (Loc.Bcr l)).injective h1`.

Use `⟨E, inferInstance, κ', fun g => f (c g), hκ', hcE, ⟨?_, fun g h => ?_⟩, _, hx'⟩` and prove the remaining obligations. Conclude with `continuous_induced_rng.2 (hcc.congr fun g => (hcE g).symm)`. Use `hcoc g h` as an intermediate fact. Simplify using `only [Loc.chRep] at this ⊢`. Simplify using `[this, f, hπ2]`.
-/
private theorem desc {l : ℕ} [Fact l.Prime] {H : Type} [Group H] [TopologicalSpace H] (φ : H →* GQ l)
    (κ : H →* (PadicAlgCl l)ˣ) (E₀ : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] E₀]
    (hκ : ∀ g, (κ g : PadicAlgCl l) ∈ E₀) (c : H → PadicAlgCl l) (hc : c ∈ Loc.finiteCocycles φ (Loc.chRep κ)) :
    ∃ (E : IntermediateField ℚ_[l] (PadicAlgCl l)) (_ : FiniteDimensional ℚ_[l] E) (κ' : H →* Eˣ) (c' : H → E),
      (∀ g, ((κ' g : E) : PadicAlgCl l) = κ g) ∧ (∀ g, (c' g : PadicAlgCl l) = c g) ∧ c' ∈ Loc.finiteCocycles φ (Loc.chRep κ') := by
  obtain ⟨⟨hcc, hcoc⟩, x, hx⟩ := hc
  obtain ⟨S, rfl⟩ := TensorProduct.exists_finset x
  obtain ⟨T⟩ := Loc.tiedP l
  haveI : IsDomain (Loc.Bcr l) := GlobalTheory.RegularRing.isDomain_of_tied T (Loc.botExt l)
  haveI := fd_adjoin_range l (fun p : S => p.1.1)
  let E : IntermediateField ℚ_[l] (PadicAlgCl l) := E₀ ⊔ IntermediateField.adjoin ℚ_[l] (Set.range fun p : S => p.1.1)
  have hκE : ∀ g, (κ g : PadicAlgCl l) ∈ E := fun g => (le_sup_left : E₀ ≤ E) (hκ g)
  have hS : ∀ p ∈ S, p.1 ∈ E := fun p hp =>
    (le_sup_right : _ ≤ E) (IntermediateField.subset_adjoin _ _ ⟨⟨p, hp⟩, rfl⟩)
  obtain ⟨π, hπ⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap E (PadicAlgCl l))
    (LinearMap.ker_eq_bot.2 (algebraMap E (PadicAlgCl l)).injective)
  have hπ1 : ∀ y : E, π (y : PadicAlgCl l) = y := fun y => LinearMap.congr_fun hπ y
  let κ' : H →* Eˣ := MonoidHom.toHomUnits
    { toFun := fun g => ⟨κ g, hκE g⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun g h => Subtype.ext (by simp) }
  have hκ' : ∀ g, ((κ' g : E) : PadicAlgCl l) = κ g := fun g => rfl
  have hπ2 : ∀ g y, π (κ g * y) = κ' g * π y := fun g y => map_smul π (κ' g : E) y
  let f : PadicAlgCl l →ₗ[ℚ_[l]] E := π.restrictScalars ℚ_[l]
  let i : E →ₗ[ℚ_[l]] PadicAlgCl l := E.val.toLinearMap
  have key : ∀ g (y : PadicAlgCl l ⊗[ℚ_[l]] Loc.Bcr l), LinearMap.rTensor (Loc.Bcr l) f (Loc.actC φ (Loc.chRep κ) g y) =
      Loc.actC φ (Loc.chRep κ') g (LinearMap.rTensor (Loc.Bcr l) f y) := by
    intro g y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [Loc.actC, Loc.chRep, f, hπ2]
    | add a b ha hb => simp only [map_add, ha, hb]
  have key' : ∀ g (y : E ⊗[ℚ_[l]] Loc.Bcr l), LinearMap.rTensor (Loc.Bcr l) i (Loc.actC φ (Loc.chRep κ') g y) =
      Loc.actC φ (Loc.chRep κ) g (LinearMap.rTensor (Loc.Bcr l) i y) := by
    intro g y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [Loc.actC, Loc.chRep, i, hκ']
    | add a b ha hb => simp only [map_add, ha, hb]
  set x := ∑ p ∈ S, p.1 ⊗ₜ[ℚ_[l]] p.2 with hxd
  have hix : LinearMap.rTensor (Loc.Bcr l) i (LinearMap.rTensor (Loc.Bcr l) f x) = x := by
    rw [hxd, map_sum, map_sum]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [LinearMap.rTensor_tmul, LinearMap.rTensor_tmul]
    congr 1
    exact congrArg Subtype.val (hπ1 ⟨p.1, hS p hp⟩)
  have hx' : ∀ g, f (c g) ⊗ₜ[ℚ_[l]] (1 : Loc.Bcr l) =
      Loc.actC φ (Loc.chRep κ') g (LinearMap.rTensor (Loc.Bcr l) f x) - LinearMap.rTensor (Loc.Bcr l) f x := fun g => by
    rw [← key, ← map_sub, ← hx g, LinearMap.rTensor_tmul]
  have hcE : ∀ g, ((f (c g) : E) : PadicAlgCl l) = c g := fun g => by
    have h1 := congrArg (LinearMap.rTensor (Loc.Bcr l) i) (hx' g)
    rw [map_sub, key', hix, ← hx g, LinearMap.rTensor_tmul] at h1
    exact Algebra.TensorProduct.includeLeft_injective (R := ℚ_[l]) (S := ℚ_[l]) (B := Loc.Bcr l)
      (algebraMap ℚ_[l] (Loc.Bcr l)).injective h1
  refine ⟨E, inferInstance, κ', fun g => f (c g), hκ', hcE, ⟨?_, fun g h => ?_⟩, _, hx'⟩
  · exact continuous_induced_rng.2 (hcc.congr fun g => (hcE g).symm)
  · have := hcoc g h
    simp only [Loc.chRep] at this ⊢
    simp [this, f, hπ2]

/- English proof (translation)
Take `⟨m, hm⟩` from `h`. Use `⟨θ g * m - c g, fun s hs => ?_⟩` and prove the remaining obligations. Establish `h1` using `hm _ (hS s hs)`. Establish `h2` using `hc g (g⁻¹ * s * g)`. Establish `h3` using `hc s g`.

Establish `h4 : θ (g⁻¹ * s * g) = θ s` using `by rw [map_mul, map_mul, map_inv, mul_comm _ (θ s), inv_mul_cancel_right]`. Rewrite `h2` using `[show g * (g⁻¹ * s * g) = s * g by group, h3, h1, h4]`. Take the linear combination `h2`.
-/
private theorem cob_conj {Γ k : Type} [Group Γ] [Field k] (θ : Γ →* kˣ) (c : Γ → k)
    (hc : ∀ g h, c (g * h) = c g + θ g * c h) (S S' : Subgroup Γ) (g : Γ) (hS : ∀ s ∈ S', g⁻¹ * s * g ∈ S)
    (h : ∃ m, ∀ s ∈ S, c s = θ s * m - m) : ∃ m, ∀ s ∈ S', c s = θ s * m - m := by
  obtain ⟨m, hm⟩ := h
  refine ⟨θ g * m - c g, fun s hs => ?_⟩
  have h1 := hm _ (hS s hs)
  have h2 := hc g (g⁻¹ * s * g)
  have h3 := hc s g
  have h4 : θ (g⁻¹ * s * g) = θ s := by rw [map_mul, map_mul, map_inv, mul_comm _ (θ s), inv_mul_cancel_right]
  rw [show g * (g⁻¹ * s * g) = s * g by group, h3, h1, h4] at h2
  linear_combination h2

open scoped Pointwise in
/- English proof (translation)
Take `⟨g, hg⟩` from `exists_smul_eq_of_isPlaceOver (F := k) hA hB`. Establish `h : IsLift (RingEquiv.refl k) g.toRingEquiv` using `fun x => g.commutes x`. Establish `hm : ∀ x, g.toRingEquiv x ∈ B ↔ x ∈ A` using `fun x => by show g • x ∈ B ↔ _`. Rewrite using `[← hg]`. Conclude with `ValuationSubring.smul_mem_pointwise_smul_iff`.

Conclude with `⟨g, fun τ hτ => conjGal_mem_Ine h hm hτ, fun τ hτ => conjGal_mem_Dec h hm hτ⟩`.
-/
private theorem conj_place {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    {A B : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 k)} (hA : IsPlaceOver A v) (hB : IsPlaceOver B v) :
    ∃ g : G k Ω, (∀ τ ∈ Ine (F := k) B, g⁻¹ * τ * g ∈ Ine (F := k) A) ∧ ∀ τ ∈ Dec (F := k) B, g⁻¹ * τ * g ∈ Dec (F := k) A := by
  obtain ⟨g, hg⟩ := exists_smul_eq_of_isPlaceOver (F := k) hA hB
  have h : IsLift (RingEquiv.refl k) g.toRingEquiv := fun x => g.commutes x
  have hm : ∀ x, g.toRingEquiv x ∈ B ↔ x ∈ A := fun x => by
    show g • x ∈ B ↔ _
    rw [← hg]
    exact ValuationSubring.smul_mem_pointwise_smul_iff
  exact ⟨g, fun τ hτ => conjGal_mem_Ine h hm hτ, fun τ hτ => conjGal_mem_Dec h hm hτ⟩

/- English proof (translation)
Set `F : G K Ω →* Multiplicative (PadicAlgCl l)` to `MonoidHom.mk' (fun g => Multiplicative.ofAdd (f g)) hm`. Establish `hpow : ∀ g (n : ℕ), n ≠ 0 → f (g ^ n) = 0 → f g = 0` using `fun g n hn h => by`. Establish `h1 : f (g ^ n) = n • f g` using `congrArg Multiplicative.toAdd (map_pow F g n)`. Rewrite `h1` using `[h, nsmul_eq_mul]`. Conclude with `(mul_eq_zero.1 h1.symm).resolve_left (Nat.cast_ne_zero.2 hn)`.

Establish `h1 : f 1 = 0` using `congrArg Multiplicative.toAdd (map_one F)`. Establish `key : ∀ g ∈ (Kum.artCl K Ω).ker, f g = 0` using `fun g hg => by`. Assume the negation of the conclusion as `h0`. Establish `hr : 0 < ‖f g‖` using `norm_pos_iff.2 h0`. Set `B : OpenAddSubgroup (PadicAlgCl l)` to `IsUltrametricDist.ball_openAddSubgroup (PadicAlgCl l) hr`.

Set `χ : G K Ω →* Multiplicative (PadicAlgCl l ⧸ B.toAddSubgroup)` to `(AddMonoidHom.toMultiplicative (QuotientAddGroup.mk' B.toAddSubgroup)).comp F`. Establish `hχ : ∀ s, χ s = 1 ↔ f s ∈ B` using `fun s => QuotientAddGroup.eq_zero_iff (f s)`. Use `Kum.artKer K Ω _ χ (by` as an intermediate fact. Establish `: (χ.ker : Set (G K Ω)) = f ⁻¹' B` using `Set.ext hχ`. Rewrite using `[this]`.

Conclude with `B.isOpen.preimage hf)`. Use the proof step `(fun A s hs => (hχ s).2 (by rw [hI A s hs]; exact zero_mem _))`. Use the proof step `(fun c hc => (hχ c).2 (by`. Take `⟨j, hj⟩` from `hc`. Establish `h2 : c ^ 2 = 1` using `AlgEquiv.ext fun x => j.injective (by`.

Rewrite using `[pow_two, AlgEquiv.mul_apply]`. Conclude with `(hj _).trans ((congrArg _ (hj x)).trans (Complex.conj_conj _)))`. Rewrite using `[hpow c 2 two_ne_zero (by rw [h2, h1])]`. Conclude with `zero_mem _)) hg`. Establish `h3 : f g ∈ Metric.ball (0 : PadicAlgCl l) ‖f g‖` using `(hχ g).1 this`.

Simplify using `at h3`. Use `hpow g (Nat.card (ClassGroup (𝓞 K))) Nat.card_pos.ne' (key _ ?_)` and prove the remaining obligations. Rewrite using `[MonoidHom.mem_ker, map_pow, pow_card_eq_one']`.
-/
private theorem unr_zero (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    (l : ℕ) [Fact l.Prime] (f : G K Ω → PadicAlgCl l) (hf : Continuous f) (hm : ∀ g h, f (g * h) = f g + f h)
    (hI : ∀ A : ValuationSubring Ω, ∀ g ∈ Ine (F := K) A, f g = 0) (g : G K Ω) : f g = 0 := by
  let F : G K Ω →* Multiplicative (PadicAlgCl l) := MonoidHom.mk' (fun g => Multiplicative.ofAdd (f g)) hm
  have hpow : ∀ g (n : ℕ), n ≠ 0 → f (g ^ n) = 0 → f g = 0 := fun g n hn h => by
    have h1 : f (g ^ n) = n • f g := congrArg Multiplicative.toAdd (map_pow F g n)
    rw [h, nsmul_eq_mul] at h1
    exact (mul_eq_zero.1 h1.symm).resolve_left (Nat.cast_ne_zero.2 hn)
  have h1 : f 1 = 0 := congrArg Multiplicative.toAdd (map_one F)
  have key : ∀ g ∈ (Kum.artCl K Ω).ker, f g = 0 := fun g hg => by
    by_contra h0
    have hr : 0 < ‖f g‖ := norm_pos_iff.2 h0
    let B : OpenAddSubgroup (PadicAlgCl l) := IsUltrametricDist.ball_openAddSubgroup (PadicAlgCl l) hr
    let χ : G K Ω →* Multiplicative (PadicAlgCl l ⧸ B.toAddSubgroup) :=
      (AddMonoidHom.toMultiplicative (QuotientAddGroup.mk' B.toAddSubgroup)).comp F
    have hχ : ∀ s, χ s = 1 ↔ f s ∈ B := fun s => QuotientAddGroup.eq_zero_iff (f s)
    have := Kum.artKer K Ω _ χ (by
        have : (χ.ker : Set (G K Ω)) = f ⁻¹' B := Set.ext hχ
        rw [this]
        exact B.isOpen.preimage hf)
      (fun A s hs => (hχ s).2 (by rw [hI A s hs]; exact zero_mem _))
      (fun c hc => (hχ c).2 (by
        obtain ⟨j, hj⟩ := hc
        have h2 : c ^ 2 = 1 := AlgEquiv.ext fun x => j.injective (by
          rw [pow_two, AlgEquiv.mul_apply]
          exact (hj _).trans ((congrArg _ (hj x)).trans (Complex.conj_conj _)))
        rw [hpow c 2 two_ne_zero (by rw [h2, h1])]
        exact zero_mem _)) hg
    have h3 : f g ∈ Metric.ball (0 : PadicAlgCl l) ‖f g‖ := (hχ g).1 this
    simp at h3
  refine hpow g (Nat.card (ClassGroup (𝓞 K))) Nat.card_pos.ne' (key _ ?_)
  rw [MonoidHom.mem_ker, map_pow, pow_card_eq_one']

section Char

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime]

/- English proof (translation)
Establish `hcoc : ∀ g h, c (g * h) = c g + θ g * c h` using `hc.2`. Use `⟨fun A hA => ?_, ?_⟩` and prove the remaining obligations. Take `⟨p1, p2, p3, -⟩` from `places ℚ Ω l A`. Distinguish the cases in `hT : A = ⊤`. Use `⟨0, fun g hg => ?_⟩` and prove the remaining obligations.

Rewrite `hg` using `[(p2 hT).1, Subgroup.mem_bot]`. Use `hcoc 1 1` as an intermediate fact. Simplify using `only [mul_one, map_one, Units.val_one, one_mul] at this`. Rewrite using `[hg, left_eq_add.1 this]`. Simplify using the standard rewrite rules.

Take `⟨v, hv⟩` from `p1 hT`. Take `⟨B, hB, hx⟩` from `hb.away v fun h => hA ((p3 v hv).2 h)`. Take `⟨g, hg, -⟩` from `conj_place hB hv`. Conclude with `cob_conj θ c hcoc _ _ g hg hx`. Take `⟨j, -, -, x, hx⟩` from `hb.above (algebraMap ℚ (Om l))`.

Take `⟨i1, -, -, -, -, i6, -⟩` from `Loc.iotaFacts j`. Use `⟨j, ⟨⟨hc.1.comp i1.continuous, fun g h => ?_⟩, x, fun σ => ?_⟩, ?_, fun A hA => ?_⟩` and prove the remaining obligations. Conclude with `(congrArg c (map_mul _ g h)).trans (hc.2 _ _)`. Conclude with `hx ⟨(Loc.iota j σ, σ), fun y => (Loc.iota_spec j σ y).symm⟩`. Rewrite using `[← ValuationSubring.mem_nonunits_iff, ValuationSubring.mem_nonunits_iff_or]`.

Use `Or.inr fun h => ?_` and prove the remaining obligations. Establish `h1 : (Valued.v : Valuation (Om l) NNReal) (j (l : Ω)⁻¹) ≤ 1` using `h`. Rewrite `h1` using `[map_inv₀, map_natCast, map_inv₀, PadicAlgCl.valuation_p, one_div, inv_inv]`. Conclude with `absurd (Nat.cast_le_one.1 h1) (Fact.out : l.Prime).one_lt.not_ge`. Take `⟨p1, p2, p3, -⟩` from `places ℚ Ω l A`.

Take `⟨v, hv⟩` from `p1 fun h => (p2 h).2 hA`. Conclude with `conj_place ((i6 v).2 ((p3 v hv).1 hA)) hv`.
-/
private theorem bk_loc (θ : G ℚ Ω →* (PadicAlgCl l)ˣ) (c : G ℚ Ω → PadicAlgCl l) (hc : c ∈ Z1 (Loc.chRep θ))
    (hb : Af.IsBK l (Loc.chRep θ) c) :
    (∀ A : ValuationSubring Ω, ¬ A.valuation (l : Ω) < 1 → ∃ m, ∀ g ∈ Ine (F := ℚ) A, c g = θ g * m - m) ∧
    ∃ j : Ω →+* Om l, (fun σ => c (Loc.iota j σ)) ∈ Loc.finiteCocycles (MonoidHom.id (GQ l)) (Loc.chRep (θ.comp (Loc.iota j))) ∧
      (Loc.placeJ j).valuation (l : Ω) < 1 ∧ ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → ∃ g : G ℚ Ω,
        (∀ τ ∈ Ine (F := ℚ) A, g⁻¹ * τ * g ∈ Ine (F := ℚ) (Loc.placeJ j)) ∧
        ∀ τ ∈ Dec (F := ℚ) A, g⁻¹ * τ * g ∈ Dec (F := ℚ) (Loc.placeJ j) := by
  have hcoc : ∀ g h, c (g * h) = c g + θ g * c h := hc.2
  refine ⟨fun A hA => ?_, ?_⟩
  · obtain ⟨p1, p2, p3, -⟩ := places ℚ Ω l A
    by_cases hT : A = ⊤
    · refine ⟨0, fun g hg => ?_⟩
      rw [(p2 hT).1, Subgroup.mem_bot] at hg
      have := hcoc 1 1
      simp only [mul_one, map_one, Units.val_one, one_mul] at this
      rw [hg, left_eq_add.1 this]
      simp
    obtain ⟨v, hv⟩ := p1 hT
    obtain ⟨B, hB, hx⟩ := hb.away v fun h => hA ((p3 v hv).2 h)
    obtain ⟨g, hg, -⟩ := conj_place hB hv
    exact cob_conj θ c hcoc _ _ g hg hx
  · obtain ⟨j, -, -, x, hx⟩ := hb.above (algebraMap ℚ (Om l))
    obtain ⟨i1, -, -, -, -, i6, -⟩ := Loc.iotaFacts j
    refine ⟨j, ⟨⟨hc.1.comp i1.continuous, fun g h => ?_⟩, x, fun σ => ?_⟩, ?_, fun A hA => ?_⟩
    · exact (congrArg c (map_mul _ g h)).trans (hc.2 _ _)
    · exact hx ⟨(Loc.iota j σ, σ), fun y => (Loc.iota_spec j σ y).symm⟩
    · rw [← ValuationSubring.mem_nonunits_iff, ValuationSubring.mem_nonunits_iff_or]
      refine Or.inr fun h => ?_
      have h1 : (Valued.v : Valuation (Om l) NNReal) (j (l : Ω)⁻¹) ≤ 1 := h
      rw [map_inv₀, map_natCast, map_inv₀, PadicAlgCl.valuation_p, one_div, inv_inv] at h1
      exact absurd (Nat.cast_le_one.1 h1) (Fact.out : l.Prime).one_lt.not_ge
    · obtain ⟨p1, p2, p3, -⟩ := places ℚ Ω l A
      obtain ⟨v, hv⟩ := p1 fun h => (p2 h).2 hA
      exact conj_place ((i6 v).2 ((p3 v hv).1 hA)) hv

/- English proof (translation)
Establish `hcoc : ∀ g h, c (g * h) = c g + θ g * c h` using `hc.2`. Take `⟨CK, hK⟩` from `hP.lemK`. Take `⟨h1, j, hj, -, h2⟩` from `bk_loc θ c hc hb`. Take `⟨i1, i2, -, -, i5, -, -⟩` from `Loc.iotaFacts j`. Take `⟨K₀, hK₀, hψK⟩` from `char_finext l (G ℚ Ω) χ hχ`.

Establish `hθK : ∀ g, (θ g : PadicAlgCl l) ∈ K₀` using `fun g => by`. Establish `h` using `hθ g`. Rewrite `h` using `[mul_assoc]`. Rewrite using `[eq_inv_of_mul_eq_one_left h]`. Use `inv_mem (mul_mem (hψK g) (pow_mem ?_ _))` and prove the remaining obligations.

Rewrite using `[IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l)]`. Conclude with `K₀.algebraMap_mem _`. Take `⟨E, _, κ, c', hκ, hc', hf⟩` from `desc _ (θ.comp (Loc.iota j)) K₀ (fun g => hθK _) _ hj`. Use `haveI : IsModuleTopology ℚ_[l] E := isModuleTopologyOfFiniteDimensional`. Establish `hw : Loc.HasWeight (MonoidHom.id (GQ l)) κ (-(e : ℤ))`.

Use `⟨χ.ker.comap (Loc.iota j), hχ.preimage i1.continuous, fun g hg _ => ?_⟩` and prove the remaining obligations. Rewrite using `[_root_.zpow_neg, zpow_natCast]`. Use `eq_inv_of_mul_eq_one_left (Units.ext (Subtype.ext ?_))` and prove the remaining obligations. Establish `h3` using `hθ (Loc.iota j g)`. Establish `h4 : χ (Loc.iota j g) = 1` using `hg`.

Establish `h5 : cycZ ℚ Ω l (Loc.iota j g) = Loc.cyc l l g` using `DFunLike.congr_fun (i5 l) g`. Rewrite `h3` using `[h4, h5, Units.val_one, mul_one]`. Rewrite using `[Units.val_mul, MulMemClass.coe_mul, hκ, Units.val_pow_eq_pow_val, SubmonoidClass.coe_pow]`. Conclude with `h3`. Establish `hz` using `(Loc.z1fChar hP.loc (MonoidHom.id (GQ l)) Topology.IsOpenEmbedding.id κ (continuous_induced_rng.2 ((hθc.comp i1.continuous).congr fun g => (hκ g).symm)) _ hw).1 (by omega)`.

Rewrite `hf` using `[hz.1, mem_coboundaries1]`. Take `⟨m, hm⟩` from `hf`. Establish `h3 : ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → ∃ m, ∀ g ∈ Dec (F` using `ℚ) A, c g = θ g * m - m := by`. Introduce `A hA`. Take `⟨g, -, hg⟩` from `h2 A hA`.

Use `cob_conj θ c hcoc _ _ g hg ⟨m, fun s hs => ?_⟩` and prove the remaining obligations. Rewrite `hs` using `[← i2]`. Take `⟨σ, rfl⟩` from `hs`. Establish `h4 : c' σ = κ σ * m - m` using `hm σ`. Establish `h5` using `hc' σ`.

Rewrite using `[← h5, h4, AddSubgroupClass.coe_sub, MulMemClass.coe_mul, hκ]`. Both sides reduce to the same expression. Use `X.soBar CK hK (GlobalTheory.PoitouTateConj.poitouTateDuality_of_normalised hP.pt) hP.loc.lfK hP.loc.ltK ℚ Ω l χ hχ e he (fun g => θ g) hθ c hc.1 hcoc (fun A => ?_) h3` and prove the remaining obligations. Distinguish the cases in `hA : A.valuation (l : Ω) < 1`. Take `⟨m, hm⟩` from `h3 A hA`.

Conclude with `⟨m, fun g hg => hm g hg.1⟩`. Conclude with `h1 A hA`.
-/
private theorem neg_case (hP : CohInp) (θ χ : G ℚ Ω →* (PadicAlgCl l)ˣ) (hχ : IsOpen (χ.ker : Set (G ℚ Ω))) (e : ℕ)
    (he : 1 ≤ e) (hθc : Continuous fun g => (θ g : PadicAlgCl l))
    (hθ : ∀ g, (θ g : PadicAlgCl l) * χ g * algebraMap ℤ_[l] (PadicAlgCl l) (cycZ ℚ Ω l g : ℤ_[l]) ^ e = 1)
    (c : G ℚ Ω → PadicAlgCl l) (hc : c ∈ Z1 (Loc.chRep θ)) (hb : Af.IsBK l (Loc.chRep θ) c) :
    ∃ m, ∀ g, c g = θ g * m - m := by
  have hcoc : ∀ g h, c (g * h) = c g + θ g * c h := hc.2
  obtain ⟨CK, hK⟩ := hP.lemK
  obtain ⟨h1, j, hj, -, h2⟩ := bk_loc θ c hc hb
  obtain ⟨i1, i2, -, -, i5, -, -⟩ := Loc.iotaFacts j
  obtain ⟨K₀, hK₀, hψK⟩ := char_finext l (G ℚ Ω) χ hχ
  have hθK : ∀ g, (θ g : PadicAlgCl l) ∈ K₀ := fun g => by
    have h := hθ g
    rw [mul_assoc] at h
    rw [eq_inv_of_mul_eq_one_left h]
    refine inv_mem (mul_mem (hψK g) (pow_mem ?_ _))
    rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l)]
    exact K₀.algebraMap_mem _
  obtain ⟨E, _, κ, c', hκ, hc', hf⟩ := desc _ (θ.comp (Loc.iota j)) K₀ (fun g => hθK _) _ hj
  haveI : IsModuleTopology ℚ_[l] E := isModuleTopologyOfFiniteDimensional
  have hw : Loc.HasWeight (MonoidHom.id (GQ l)) κ (-(e : ℤ)) := by
    refine ⟨χ.ker.comap (Loc.iota j), hχ.preimage i1.continuous, fun g hg _ => ?_⟩
    rw [_root_.zpow_neg, zpow_natCast]
    refine eq_inv_of_mul_eq_one_left (Units.ext (Subtype.ext ?_))
    have h3 := hθ (Loc.iota j g)
    have h4 : χ (Loc.iota j g) = 1 := hg
    have h5 : cycZ ℚ Ω l (Loc.iota j g) = Loc.cyc l l g := DFunLike.congr_fun (i5 l) g
    rw [h4, h5, Units.val_one, mul_one] at h3
    rw [Units.val_mul, MulMemClass.coe_mul, hκ, Units.val_pow_eq_pow_val, SubmonoidClass.coe_pow]
    exact h3
  have hz := (Loc.z1fChar hP.loc (MonoidHom.id (GQ l)) Topology.IsOpenEmbedding.id κ
    (continuous_induced_rng.2 ((hθc.comp i1.continuous).congr fun g => (hκ g).symm)) _ hw).1 (by omega)
  rw [hz.1, mem_coboundaries1] at hf
  obtain ⟨m, hm⟩ := hf
  have h3 : ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → ∃ m, ∀ g ∈ Dec (F := ℚ) A, c g = θ g * m - m := by
    intro A hA
    obtain ⟨g, -, hg⟩ := h2 A hA
    refine cob_conj θ c hcoc _ _ g hg ⟨m, fun s hs => ?_⟩
    rw [← i2] at hs
    obtain ⟨σ, rfl⟩ := hs
    have h4 : c' σ = κ σ * m - m := hm σ
    have h5 := hc' σ
    rw [← h5, h4, AddSubgroupClass.coe_sub, MulMemClass.coe_mul, hκ]
    rfl
  refine X.soBar CK hK (GlobalTheory.PoitouTateConj.poitouTateDuality_of_normalised hP.pt) hP.loc.lfK hP.loc.ltK ℚ Ω l χ hχ e he
    (fun g => θ g) hθ c hc.1 hcoc (fun A => ?_) h3
  by_cases hA : A.valuation (l : Ω) < 1
  · obtain ⟨m, hm⟩ := h3 A hA
    exact ⟨m, fun g hg => hm g hg.1⟩
  · exact h1 A hA

/- English proof (translation)
Establish `hcoc : ∀ g h, c (g * h) = c g + θ g * c h` using `hc.2`. Use `haveI : IsAlgClosure K Ω := ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) K⟩`. Take `⟨g1, g2, -⟩` from `galEmbTop ℚ K Ω`. Take `⟨-, hIne, -, -⟩` from `Kum.toGalDict ℚ Ω K _ le_rfl`. Establish `hχ : IsOpen (θ.ker : Set (G ℚ Ω))` using `Subgroup.isOpen_mono hθ g2`.

Establish `hθc : Continuous θ` using `continuous_of_continuousAt_one θ (by`. Use `(continuousAt_const (y := (1 : (PadicAlgCl l)ˣ))).congr ?_` and prove the remaining obligations. Use `filter_upwards [hχ.mem_nhds θ.ker.one_mem] with g hg using hg.symm)`. Take `⟨h1, j, hj, hjl, h2⟩` from `bk_loc θ c hc hb`. Take `⟨i1, -, -, i4, -, -, -⟩` from `Loc.iotaFacts j`.

Take `⟨K₀, hK₀, hψK⟩` from `char_finext l (G ℚ Ω) θ hχ`. Take `⟨E, _, κ, c', hκ, hc', hf⟩` from `desc _ (θ.comp (Loc.iota j)) K₀ (fun g => hψK _) _ hj`. Use `haveI : IsModuleTopology ℚ_[l] E := isModuleTopologyOfFiniteDimensional`. Establish `hκc : Continuous fun g => (κ g : E)` using `continuous_induced_rng.2 (((Units.continuous_val.comp hθc).comp i1.continuous).congr fun g => (hκ g).symm)`. Establish `hz` using `(Loc.z1fUnr hP.loc (MonoidHom.id (GQ l)) Topology.IsOpenEmbedding.id (Loc.chRep κ) ((hκc.comp continuous_fst).mul continuous_snd) (fun g hg => by`.

Establish `h3 : θ (Loc.iota j g) = 1` using `hθ (hI _ hjl (i4 ▸ ⟨g, hg, rfl⟩))`. Establish `h4 : (κ g : E) = 1` using `Subtype.ext ((hκ g).trans (congrArg Units.val h3))`. Use `LinearMap.ext fun y => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(κ g : E) * y = y`. Rewrite using `[h4, one_mul]) c' hf.1).1 hf`.

Establish `h3 : ∀ A : ValuationSubring Ω, ∃ m, ∀ g ∈ Ine (F` using `ℚ) A, c g = θ g * m - m := by`. Introduce `A`. Distinguish the cases in `hA : A.valuation (l : Ω) < 1`. Take `⟨g, hg, -⟩` from `h2 A hA`. Use `cob_conj θ c hcoc _ _ g hg ⟨0, fun s hs => ?_⟩` and prove the remaining obligations.

Rewrite `hs` using `[← i4]`. Take `⟨σ, hσ, rfl⟩` from `hs`. Establish `h5` using `hc' σ`. Rewrite using `[← h5, hz σ hσ]`. Simplify using the standard rewrite rules.

Conclude with `h1 A hA`. Establish `h4 : ∀ s : G K Ω, θ (galEmb ℚ K Ω s) = 1` using `fun s => hθ (galEmb_mem ℚ K Ω s)`. Introduce `g hg`. Rewrite `hg` using `[← range_galEmb]`. Take `⟨s, rfl⟩` from `hg`.

Use `unr_zero K Ω l (fun s => c (galEmb ℚ K Ω s)) (hc.1.comp g1.continuous) (fun s t => ?_) (fun A s hs => ?_) s` and prove the remaining obligations. Rewrite using `[map_mul, hcoc, h4, Units.val_one, one_mul]`. Take `⟨m, hm⟩` from `h3 A`. Rewrite using `[hm _ ((hIne A ⟨_, galEmb_mem ℚ K Ω s⟩).1 hs), h4, Units.val_one, one_mul, sub_self]`.
-/
private theorem zero_case (hP : CohInp) (K : Type) [Field K] [NumberField K] [Algebra K Ω]
    (θ : G ℚ Ω →* (PadicAlgCl l)ˣ) (hθ : galOf ℚ K Ω ≤ θ.ker)
    (hI : ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → Ine (F := ℚ) A ≤ galOf ℚ K Ω)
    (c : G ℚ Ω → PadicAlgCl l) (hc : c ∈ Z1 (Loc.chRep θ)) (hb : Af.IsBK l (Loc.chRep θ) c) :
    ∀ g ∈ galOf ℚ K Ω, c g = 0 := by
  have hcoc : ∀ g h, c (g * h) = c g + θ g * c h := hc.2
  haveI : IsAlgClosure K Ω := ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) K⟩
  obtain ⟨g1, g2, -⟩ := galEmbTop ℚ K Ω
  obtain ⟨-, hIne, -, -⟩ := Kum.toGalDict ℚ Ω K _ le_rfl
  have hχ : IsOpen (θ.ker : Set (G ℚ Ω)) := Subgroup.isOpen_mono hθ g2
  have hθc : Continuous θ := continuous_of_continuousAt_one θ (by
    refine (continuousAt_const (y := (1 : (PadicAlgCl l)ˣ))).congr ?_
    filter_upwards [hχ.mem_nhds θ.ker.one_mem] with g hg using hg.symm)
  obtain ⟨h1, j, hj, hjl, h2⟩ := bk_loc θ c hc hb
  obtain ⟨i1, -, -, i4, -, -, -⟩ := Loc.iotaFacts j
  obtain ⟨K₀, hK₀, hψK⟩ := char_finext l (G ℚ Ω) θ hχ
  obtain ⟨E, _, κ, c', hκ, hc', hf⟩ := desc _ (θ.comp (Loc.iota j)) K₀ (fun g => hψK _) _ hj
  haveI : IsModuleTopology ℚ_[l] E := isModuleTopologyOfFiniteDimensional
  have hκc : Continuous fun g => (κ g : E) :=
    continuous_induced_rng.2 (((Units.continuous_val.comp hθc).comp i1.continuous).congr fun g => (hκ g).symm)
  have hz := (Loc.z1fUnr hP.loc (MonoidHom.id (GQ l)) Topology.IsOpenEmbedding.id (Loc.chRep κ)
    ((hκc.comp continuous_fst).mul continuous_snd) (fun g hg => by
      have h3 : θ (Loc.iota j g) = 1 := hθ (hI _ hjl (i4 ▸ ⟨g, hg, rfl⟩))
      have h4 : (κ g : E) = 1 := Subtype.ext ((hκ g).trans (congrArg Units.val h3))
      refine LinearMap.ext fun y => ?_
      change (κ g : E) * y = y
      rw [h4, one_mul]) c' hf.1).1 hf
  have h3 : ∀ A : ValuationSubring Ω, ∃ m, ∀ g ∈ Ine (F := ℚ) A, c g = θ g * m - m := by
    intro A
    by_cases hA : A.valuation (l : Ω) < 1
    · obtain ⟨g, hg, -⟩ := h2 A hA
      refine cob_conj θ c hcoc _ _ g hg ⟨0, fun s hs => ?_⟩
      rw [← i4] at hs
      obtain ⟨σ, hσ, rfl⟩ := hs
      have h5 := hc' σ
      rw [← h5, hz σ hσ]
      simp
    · exact h1 A hA
  have h4 : ∀ s : G K Ω, θ (galEmb ℚ K Ω s) = 1 := fun s => hθ (galEmb_mem ℚ K Ω s)
  intro g hg
  rw [← range_galEmb] at hg
  obtain ⟨s, rfl⟩ := hg
  refine unr_zero K Ω l (fun s => c (galEmb ℚ K Ω s)) (hc.1.comp g1.continuous) (fun s t => ?_) (fun A s hs => ?_) s
  · rw [map_mul, hcoc, h4, Units.val_one, one_mul]
  · obtain ⟨m, hm⟩ := h3 A
    rw [hm _ ((hIne A ⟨_, galEmb_mem ℚ K Ω s⟩).1 hs), h4, Units.val_one, one_mul, sub_self]

end Char

/- English proof (translation)
Use `revert a b`. Evaluate the decidable proposition.
-/
private theorem wt_rev (a b : Fin 3) : wt b.rev a.rev = wt a b := by
  revert a b
  decide

/- English proof (translation)
Introduce `hP Ω _ _ _ K _ _ _ l _ c N _ e ψ D j hj γ hγ hw hb`. Take `⟨d1, d2, d3, d4, -, -, -, -, d5, -, d6⟩` from `dat_facts D`. Set `η : G ℚ Ω →* (PadicAlgCl l)ˣ` to `(Units.map (Int.castRingHom (PadicAlgCl l)).toMonoidHom).comp D.η`. Establish `hη1 : ∀ g, D.η g = 1 → η g = 1` using `fun g h => by simp [η, h]`. Establish `hη2 : ∀ g, D.η g ≠ 1 → η g = -1` using `fun g h => by`.

Apply `Units.ext` to reduce the goal to its premises. Simplify using `[η, (Int.units_eq_one_or _).resolve_left h]`. Establish `hηo : IsOpen (D.η.ker : Set (G ℚ Ω))` using `d4.isOpen_fiber 1`. Establish `hch : ∀ (θ : G ℚ Ω →* (PadicAlgCl l)ˣ), θ = 1 ∨ θ = η → ∀ f ∈ Z1 (Loc.chRep (D.ΨQ ^ j * θ)), Af.IsBK l (Loc.chRep (D.ΨQ ^ j * θ)) f → ∃ m, ∀ g, f g = (D.ΨQ g ^ j * θ g : (PadicAlgCl l)ˣ) * m - m`. Introduce `θ hθ f hf hfb`.

Establish `hk : D.η.ker ≤ θ.ker` using `fun g hg => by`. Break down `hθ with rfl | rfl` into its components or cases. Both sides reduce to the same expression. Conclude with `hη1 g hg`. Break down `hj.eq_or_lt with rfl | hj` into its components or cases.

Simplify using `only [zpow_zero, one_mul] at hf hfb ⊢`. Establish `hcoc : ∀ g h, f (g * h) = f g + θ g * f h` using `hf.2`. Establish `h0` using `zero_case hP K θ (D.η_ker ▸ hk) (fun A hA => D.η_ker ▸ (d6 A hA).1) f hf hfb`. Rewrite `h0` using `[← D.η_ker]`. Establish `h1 : ∀ g, D.η g ≠ 1 → f g = f D.cc` using `fun g hg => by`.

Establish `h2 : g * D.cc ∈ D.η.ker`. Rewrite using `[MonoidHom.mem_ker, map_mul, d2, (Int.units_eq_one_or _).resolve_left hg]`. Simplify using the standard rewrite rules. Establish `h3` using `hcoc (g * D.cc) D.cc`. Rewrite `h3` using `[mul_assoc, d1, mul_one, h0 _ h2, show θ (g * D.cc) = 1 from hk h2, Units.val_one, one_mul, zero_add]`. Then use the resulting hypothesis.

Use `⟨-f D.cc / 2, fun g => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hg : D.η g = 1`. Rewrite using `[h0 g hg, show θ g = 1 from hk hg]`. Simplify using the standard rewrite rules. Rewrite using `[h1 g hg]`.

Break down `hθ with rfl | rfl` into its components or cases. Establish `h3` using `hcoc D.cc D.cc`. Rewrite `h3` using `[d1, h0 1 (one_mem _)]`. Simplify using `only [MonoidHom.one_apply, Units.val_one] at h3 ⊢`. Take the linear combination `(-1 / 2 : PadicAlgCl l) * h3`.

Rewrite using `[hη2 g hg]`. Simplify using `only [Units.val_neg, Units.val_one]`. Expand and normalize the polynomial expressions, which then agree. Take `⟨n, rfl⟩ : ∃ n : ℕ, j = -(n : ℤ)` from `⟨(-j).toNat, by omega⟩`. Set `ψQ : G ℚ Ω →* (PadicAlgCl l)ˣ` to `(Units.map (algebraMap c.O (PadicAlgCl l)).toMonoidHom).comp (Chr.dirG ℚ Ω ψ)`.

Establish `hθc : Continuous θ` using `continuous_of_continuousAt_one θ (by`. Use `(continuousAt_const (y := (1 : (PadicAlgCl l)ˣ))).congr ?_` and prove the remaining obligations. Use `filter_upwards [hηo.mem_nhds D.η.ker.one_mem] with g hg using (hk hg).symm)`. Use `neg_case hP _ (ψQ ^ n * θ⁻¹) ?_ (e * n) (Nat.mul_pos D.gd.e_pos (by omega)) (Units.continuous_val.comp ((d5.zpow _).mul hθc)) (fun g => ?_) f hf hfb` and prove the remaining obligations. Use `Subgroup.isOpen_mono (H₁ := (Chr.cls ℚ Ω N).ker ⊓ D.η.ker) (fun g hg => ?_) ((Chr.clsFacts ℚ Ω N).1.inter hηo)` and prove the remaining obligations.

Establish `h1 : Chr.cls ℚ Ω N g = 1` using `hg.1`. Establish `h2 : θ g = 1` using `hk hg.2`. Simplify using `[ψQ, Chr.dirG, h1, h2]`. Establish `h1 : (D.ΨQ g : PadicAlgCl l) = algebraMap ℤ_[l] (PadicAlgCl l) (cycZ ℚ Ω l g : ℤ_[l]) ^ e * ψQ g`. Simplify using `[Dat.ΨQ, Dat.Ψ, Chr.Psi, chiO, ψQ]`.

Simplify using `only [MonoidHom.mul_apply, MonoidHom.zpow_apply, MonoidHom.pow_apply, MonoidHom.inv_apply, Units.val_mul, _root_.zpow_neg, zpow_natCast, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, pow_mul]`. Establish `h2` using `(D.ΨQ g).ne_zero`. Establish `h3` using `(θ g).ne_zero`. Clear the denominators using the available nonvanishing facts. Rewrite using `[h1, mul_pow, mul_comm]`.

Establish `hpr : ∀ (s : PadicAlgCl l) (θ : G ℚ Ω →* (PadicAlgCl l)ˣ), (s = -1 ∧ θ = 1) ∨ (s = 1 ∧ θ = η) → ∀ a b : Fin 3, ∃ m, ∀ g, γ g a b + s * γ g b.rev a.rev = (D.ΨQ g ^ wt a b * θ g : (PadicAlgCl l)ˣ) * m - m`. Introduce `s θ hs a b`. Distinguish the cases in `hab : wt a b = j`. Use `swap`. Conclude with `⟨0, fun g => by rw [hw g a b hab, hw g _ _ (by rwa [wt_rev])]; simp⟩`.

Set `f : Matrix (Fin 3) (Fin 3) (PadicAlgCl l) →ₗ[ℚ_[l]] PadicAlgCl l` to `{ toFun := fun X => X a b + s * X b.rev a.rev map_add' := fun X Y => by simp only [Matrix.add_apply]; ring map_smul' := fun r X => by simp only [Matrix.smul_apply, RingHom.id_apply, smul_add, mul_smul_comm] }`. Establish `hfc : Continuous f`. Express the relevant statement in the definitionally equal form `Continuous fun X : Matrix (Fin 3) (Fin 3) (PadicAlgCl l) => X a b + s * X b.rev a.rev`. Use `fun_prop`. Establish `hfe : ∀ g X, f (adRep (r0 D.η D.ΨQ) g X) = Loc.chRep (D.ΨQ ^ j * θ) g (f X)` using `fun g X => by`.

Express the relevant statement in the definitionally equal form `adRep (r0 D.η D.ΨQ) g X a b + s * adRep (r0 D.η D.ΨQ) g X b.rev a.rev = (D.ΨQ g ^ j * θ g : (PadicAlgCl l)ˣ) * (X a b + s * X b.rev a.rev)`. Rewrite using `[adRep_baseLift_apply, adRep_baseLift_apply, wt_rev, hab, Fin.rev_rev, Fin.rev_rev, Units.val_mul]`. Distinguish the cases in `hg : D.η g = 1`. Break down `hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩` into its components or cases. Simplify using `[hg, mul_add]`.

Simplify using `[hg, hη1 g hg, mul_add]`. Break down `hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩` into its components or cases. Simplify using `only [hg, if_false, MonoidHom.one_apply, Units.val_one]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [hg, if_false, hη2 g hg, Units.val_neg, Units.val_one]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hab]`. Use `hch θ (hs.imp And.right And.right) (fun g => f (γ g)) ⟨hfc.comp hγ.1, fun g h => ?_⟩ ⟨fun w hw => ?_, fun τ => ?_⟩` and prove the remaining obligations. Conclude with `(congrArg f (hγ.2 g h)).trans (by rw [map_add, hfe])`. Take `⟨A, hA, x, hx⟩` from `hb.away w hw`.

Conclude with `⟨A, hA, f x, fun s hs => by rw [hx s hs, map_sub, hfe]⟩`. Take `⟨i, hi, hx⟩` from `hb.above τ`. Use `⟨i, hi, Loc.z1fCoef _ _ _ f hfc ?_ _ hx⟩` and prove the remaining obligations. Conclude with `fun g x => hfe g.1.1 x`. Use `choose p hp using hpr 1 η (Or.inr ⟨rfl, rfl⟩)`.

Use `choose q hq using hpr (-1) 1 (Or.inl ⟨rfl, rfl⟩)`. Use `(mem_coboundaries1 _ _).2 ⟨Matrix.of fun a b => (p a b + p b.rev a.rev + q a b - q b.rev a.rev) / 4, fun g => ?_⟩` and prove the remaining obligations. Use extensionality with `a b`. Establish `h1` using `hp a b g`. Establish `h2` using `hp b.rev a.rev g`.

Establish `h3` using `hq a b g`. Establish `h4` using `hq b.rev a.rev g`. Rewrite using `[Matrix.sub_apply, adRep_baseLift_apply]`. Simplify using `only [wt_rev, Fin.rev_rev, Units.val_mul, MonoidHom.one_apply, Units.val_one, Matrix.of_apply] at h1 h2 h3 h4 ⊢`. Distinguish the cases in `hg : D.η g = 1`.

Rewrite `h1`, `h2` using `[hη1 g hg, Units.val_one]`. Rewrite using `[if_pos hg]`. Take the linear combination `(h1 + h2 + h3 - h4) / 4`. Rewrite `h1`, `h2` using `[hη2 g hg, Units.val_neg, Units.val_one]`. Rewrite using `[if_neg hg]`.

Take the linear combination `(h1 + h2 + h3 - h4) / 4`.
-/
theorem UpperTheory.V.U3.bloch_kato_nonpositive_weight :
    CohInp → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K] [Algebra K Ω]
      {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N} (D : Dat Ω K c e ψ) (j : ℤ), j ≤ 0 → ∀ γ ∈ Z1 (adRep (r0 D.η D.ΨQ)), (∀ g, γ g ∈ gw (PadicAlgCl l) j) →
      Af.IsBK l (adRep (r0 D.η D.ΨQ)) γ → γ ∈ ReciprocityTheory.Gal.B1 (adRep (r0 D.η D.ΨQ)) := by
  intro hP Ω _ _ _ K _ _ _ l _ c N _ e ψ D j hj γ hγ hw hb
  obtain ⟨d1, d2, d3, d4, -, -, -, -, d5, -, d6⟩ := dat_facts D
  let η : G ℚ Ω →* (PadicAlgCl l)ˣ := (Units.map (Int.castRingHom (PadicAlgCl l)).toMonoidHom).comp D.η
  have hη1 : ∀ g, D.η g = 1 → η g = 1 := fun g h => by simp [η, h]
  have hη2 : ∀ g, D.η g ≠ 1 → η g = -1 := fun g h => by
    apply Units.ext
    simp [η, (Int.units_eq_one_or _).resolve_left h]
  have hηo : IsOpen (D.η.ker : Set (G ℚ Ω)) := d4.isOpen_fiber 1

  have hch : ∀ (θ : G ℚ Ω →* (PadicAlgCl l)ˣ), θ = 1 ∨ θ = η → ∀ f ∈ Z1 (Loc.chRep (D.ΨQ ^ j * θ)),
      Af.IsBK l (Loc.chRep (D.ΨQ ^ j * θ)) f → ∃ m, ∀ g, f g = (D.ΨQ g ^ j * θ g : (PadicAlgCl l)ˣ) * m - m := by
    intro θ hθ f hf hfb
    have hk : D.η.ker ≤ θ.ker := fun g hg => by
      rcases hθ with rfl | rfl
      · rfl
      · exact hη1 g hg
    rcases hj.eq_or_lt with rfl | hj
    · simp only [zpow_zero, one_mul] at hf hfb ⊢
      have hcoc : ∀ g h, f (g * h) = f g + θ g * f h := hf.2
      have h0 := zero_case hP K θ (D.η_ker ▸ hk) (fun A hA => D.η_ker ▸ (d6 A hA).1) f hf hfb
      rw [← D.η_ker] at h0
      have h1 : ∀ g, D.η g ≠ 1 → f g = f D.cc := fun g hg => by
        have h2 : g * D.cc ∈ D.η.ker := by
          rw [MonoidHom.mem_ker, map_mul, d2, (Int.units_eq_one_or _).resolve_left hg]
          simp
        have h3 := hcoc (g * D.cc) D.cc
        rwa [mul_assoc, d1, mul_one, h0 _ h2, show θ (g * D.cc) = 1 from hk h2, Units.val_one, one_mul, zero_add] at h3
      refine ⟨-f D.cc / 2, fun g => ?_⟩
      by_cases hg : D.η g = 1
      · rw [h0 g hg, show θ g = 1 from hk hg]
        simp
      · rw [h1 g hg]
        rcases hθ with rfl | rfl
        · have h3 := hcoc D.cc D.cc
          rw [d1, h0 1 (one_mem _)] at h3
          simp only [MonoidHom.one_apply, Units.val_one] at h3 ⊢
          linear_combination (-1 / 2 : PadicAlgCl l) * h3
        · rw [hη2 g hg]
          simp only [Units.val_neg, Units.val_one]
          ring
    · obtain ⟨n, rfl⟩ : ∃ n : ℕ, j = -(n : ℤ) := ⟨(-j).toNat, by omega⟩
      let ψQ : G ℚ Ω →* (PadicAlgCl l)ˣ :=
        (Units.map (algebraMap c.O (PadicAlgCl l)).toMonoidHom).comp (Chr.dirG ℚ Ω ψ)
      have hθc : Continuous θ := continuous_of_continuousAt_one θ (by
        refine (continuousAt_const (y := (1 : (PadicAlgCl l)ˣ))).congr ?_
        filter_upwards [hηo.mem_nhds D.η.ker.one_mem] with g hg using (hk hg).symm)
      refine neg_case hP _ (ψQ ^ n * θ⁻¹) ?_ (e * n) (Nat.mul_pos D.gd.e_pos (by omega))
        (Units.continuous_val.comp ((d5.zpow _).mul hθc)) (fun g => ?_) f hf hfb
      · refine Subgroup.isOpen_mono (H₁ := (Chr.cls ℚ Ω N).ker ⊓ D.η.ker) (fun g hg => ?_)
          ((Chr.clsFacts ℚ Ω N).1.inter hηo)
        have h1 : Chr.cls ℚ Ω N g = 1 := hg.1
        have h2 : θ g = 1 := hk hg.2
        simp [ψQ, Chr.dirG, h1, h2]
      · have h1 : (D.ΨQ g : PadicAlgCl l) = algebraMap ℤ_[l] (PadicAlgCl l) (cycZ ℚ Ω l g : ℤ_[l]) ^ e * ψQ g := by
          simp [Dat.ΨQ, Dat.Ψ, Chr.Psi, chiO, ψQ]
        simp only [MonoidHom.mul_apply, MonoidHom.zpow_apply, MonoidHom.pow_apply, MonoidHom.inv_apply, Units.val_mul,
          _root_.zpow_neg, zpow_natCast, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, pow_mul]
        have h2 := (D.ΨQ g).ne_zero
        have h3 := (θ g).ne_zero
        field_simp
        rw [h1, mul_pow, mul_comm]

  have hpr : ∀ (s : PadicAlgCl l) (θ : G ℚ Ω →* (PadicAlgCl l)ˣ), (s = -1 ∧ θ = 1) ∨ (s = 1 ∧ θ = η) → ∀ a b : Fin 3,
      ∃ m, ∀ g, γ g a b + s * γ g b.rev a.rev = (D.ΨQ g ^ wt a b * θ g : (PadicAlgCl l)ˣ) * m - m := by
    intro s θ hs a b
    by_cases hab : wt a b = j
    swap
    · exact ⟨0, fun g => by rw [hw g a b hab, hw g _ _ (by rwa [wt_rev])]; simp⟩
    let f : Matrix (Fin 3) (Fin 3) (PadicAlgCl l) →ₗ[ℚ_[l]] PadicAlgCl l :=
      { toFun := fun X => X a b + s * X b.rev a.rev
        map_add' := fun X Y => by simp only [Matrix.add_apply]; ring
        map_smul' := fun r X => by simp only [Matrix.smul_apply, RingHom.id_apply, smul_add, mul_smul_comm] }
    have hfc : Continuous f := by
      change Continuous fun X : Matrix (Fin 3) (Fin 3) (PadicAlgCl l) => X a b + s * X b.rev a.rev
      fun_prop
    have hfe : ∀ g X, f (adRep (r0 D.η D.ΨQ) g X) = Loc.chRep (D.ΨQ ^ j * θ) g (f X) := fun g X => by
      change adRep (r0 D.η D.ΨQ) g X a b + s * adRep (r0 D.η D.ΨQ) g X b.rev a.rev =
        (D.ΨQ g ^ j * θ g : (PadicAlgCl l)ˣ) * (X a b + s * X b.rev a.rev)
      rw [adRep_baseLift_apply, adRep_baseLift_apply, wt_rev, hab, Fin.rev_rev, Fin.rev_rev, Units.val_mul]
      by_cases hg : D.η g = 1
      · rcases hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · simp [hg, mul_add]
        · simp [hg, hη1 g hg, mul_add]
      · rcases hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · simp only [hg, if_false, MonoidHom.one_apply, Units.val_one]
          ring
        · simp only [hg, if_false, hη2 g hg, Units.val_neg, Units.val_one]
          ring
    rw [hab]
    refine hch θ (hs.imp And.right And.right) (fun g => f (γ g)) ⟨hfc.comp hγ.1, fun g h => ?_⟩
      ⟨fun w hw => ?_, fun τ => ?_⟩
    · exact (congrArg f (hγ.2 g h)).trans (by rw [map_add, hfe])
    · obtain ⟨A, hA, x, hx⟩ := hb.away w hw
      exact ⟨A, hA, f x, fun s hs => by rw [hx s hs, map_sub, hfe]⟩
    · obtain ⟨i, hi, hx⟩ := hb.above τ
      refine ⟨i, hi, Loc.z1fCoef _ _ _ f hfc ?_ _ hx⟩
      exact fun g x => hfe g.1.1 x
  choose p hp using hpr 1 η (Or.inr ⟨rfl, rfl⟩)
  choose q hq using hpr (-1) 1 (Or.inl ⟨rfl, rfl⟩)
  refine (mem_coboundaries1 _ _).2 ⟨Matrix.of fun a b => (p a b + p b.rev a.rev + q a b - q b.rev a.rev) / 4, fun g => ?_⟩
  ext a b
  have h1 := hp a b g
  have h2 := hp b.rev a.rev g
  have h3 := hq a b g
  have h4 := hq b.rev a.rev g
  rw [Matrix.sub_apply, adRep_baseLift_apply]
  simp only [wt_rev, Fin.rev_rev, Units.val_mul, MonoidHom.one_apply, Units.val_one, Matrix.of_apply] at h1 h2 h3 h4 ⊢
  by_cases hg : D.η g = 1
  · rw [hη1 g hg, Units.val_one] at h1 h2
    rw [if_pos hg]
    linear_combination (h1 + h2 + h3 - h4) / 4
  · rw [hη2 g hg, Units.val_neg, Units.val_one] at h1 h2
    rw [if_neg hg]
    linear_combination (h1 + h2 + h3 - h4) / 4
