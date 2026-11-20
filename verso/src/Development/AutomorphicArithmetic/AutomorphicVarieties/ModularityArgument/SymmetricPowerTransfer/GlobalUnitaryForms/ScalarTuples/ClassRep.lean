import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.HodgeTateFromSandwich
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.FormsFin
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.ScalarTuples.FourValues
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.ScalarTuples.IsUnitP
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.NormEx
import GroundTheory.GlobalFields.IdeleGroups.ClassGroup

open NumberField IsDedekindDomain Matrix UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob
open scoped nonZeroDivisors

/- English proof (translation)
Set `H : Subgroup G` to `((N.comp ι).range ⊔ U.map N).comap N`. Use `haveI : H.Normal := Subgroup.Normal.comap inferInstance N`. Establish `hUH : U ≤ H` using `fun u hu => Subgroup.mem_sup_right ⟨u, hu, rfl⟩`. Establish `h1 : H.relIndex (H ⊔ K) ≠ 0`. Rewrite using `[Subgroup.relIndex_sup_left]`.

Conclude with `fun h => hUK (Subgroup.relIndex_eq_zero_of_le_left hUH h)`. Establish `h2 : Finite (G ⧸ (H ⊔ K))`. Use `Finite.of_injective (fun q : G ⧸ (H ⊔ K) => c q.out) fun p q h => ?_` and prove the remaining obligations. Take `⟨γ, k, hk, e⟩` from `hc _ _ h`. Rewrite using `[← p.out_eq', ← q.out_eq', eq_comm, QuotientGroup.eq]`.

Establish `: q.out⁻¹ * p.out * k⁻¹ ∈ H`. Use `Subgroup.mem_sup_left ⟨γ, ?_⟩` and prove the remaining obligations. Simplify using `only [MonoidHom.comp_apply, map_mul, map_inv, e]`. Simplify using `[mul_assoc]`. Simplify using `using mul_mem (Subgroup.mem_sup_left this : _ ∈ H ⊔ K) (Subgroup.mem_sup_right hk)`.

Establish `h3 : H.index ≠ 0`. Rewrite using `[← Subgroup.relIndex_mul_index (le_sup_left : H ≤ H ⊔ K)]`. Conclude with `mul_ne_zero h1 Subgroup.index_ne_zero_of_finite`. Use `haveI := Subgroup.fintypeOfIndexNeZero h3`. Use `choose γ u hu ho using hw`.

Use `⟨Finset.univ.image fun q : G ⧸ H => ι (γ q.out) * q.out * u q.out, ?_, fun g => ?_⟩` and prove the remaining obligations. Introduce `y hy`. Take `⟨q, -, rfl⟩` from `Finset.mem_image.1 hy`. Conclude with `ho _`. Use `set g' := (g : G ⧸ H).out with hg'`.

Establish `: g'⁻¹ * g ∈ H` using `QuotientGroup.eq.1 (QuotientGroup.out_eq' _)`. Take `⟨_, ⟨γ₁, rfl⟩, _, ⟨u₁, hu₁, rfl⟩, e⟩` from `Subgroup.mem_sup.1 (Subgroup.mem_comap.1 this)`. Establish `e' : N g = N g' * (N (ι γ₁) * N u₁)`. Rewrite `e` using `[MonoidHom.comp_apply]`. Rewrite using `[e, map_mul, map_inv, mul_inv_cancel_left]`.

Use `⟨γ₁ * (γ g')⁻¹, (ι (γ₁ * (γ g')⁻¹))⁻¹ * g * ((u g')⁻¹ * u₁)⁻¹ * (ι (γ g') * g' * u g')⁻¹, ?_, ι (γ g') * g' * u g', Finset.mem_image.2 ⟨_, Finset.mem_univ _, rfl⟩, (u g')⁻¹ * u₁, mul_mem (inv_mem (hu _)) hu₁, by group⟩` and prove the remaining obligations. Simplify using `only [map_mul, map_inv, e']`. Apply `Additive.ofMul.injective` to reduce the goal to its premises. Simplify using `only [ofMul_mul, ofMul_inv, ofMul_one]`. Normalize the expressions using the abelian group laws.
-/
private theorem reps {G Γ A C : Type} [Group G] [Group Γ] [CommGroup A] [Finite C] (ι : Γ →* G) (N : G →* A)
    (U K : Subgroup G) (Off : G → Prop) (hUK : U.relIndex K ≠ 0) (c : G → C)
    (hc : ∀ g g', c g = c g' → ∃ γ, ∃ k ∈ K, N g = N g' * N (ι γ) * N k)
    (hw : ∀ g, ∃ γ, ∃ u ∈ U, Off (ι γ * g * u)) :
    ∃ Y : Finset G, (∀ y ∈ Y, Off y) ∧ ∀ g, ∃ γ, ∃ s, N s = 1 ∧ ∃ y ∈ Y, ∃ u ∈ U, g = ι γ * s * y * u := by
  classical
  let H : Subgroup G := ((N.comp ι).range ⊔ U.map N).comap N
  haveI : H.Normal := Subgroup.Normal.comap inferInstance N
  have hUH : U ≤ H := fun u hu => Subgroup.mem_sup_right ⟨u, hu, rfl⟩
  have h1 : H.relIndex (H ⊔ K) ≠ 0 := by
    rw [Subgroup.relIndex_sup_left]
    exact fun h => hUK (Subgroup.relIndex_eq_zero_of_le_left hUH h)
  have h2 : Finite (G ⧸ (H ⊔ K)) := by
    refine Finite.of_injective (fun q : G ⧸ (H ⊔ K) => c q.out) fun p q h => ?_
    obtain ⟨γ, k, hk, e⟩ := hc _ _ h
    rw [← p.out_eq', ← q.out_eq', eq_comm, QuotientGroup.eq]
    have : q.out⁻¹ * p.out * k⁻¹ ∈ H := by
      refine Subgroup.mem_sup_left ⟨γ, ?_⟩
      simp only [MonoidHom.comp_apply, map_mul, map_inv, e]
      simp [mul_assoc]
    simpa using mul_mem (Subgroup.mem_sup_left this : _ ∈ H ⊔ K) (Subgroup.mem_sup_right hk)
  have h3 : H.index ≠ 0 := by
    rw [← Subgroup.relIndex_mul_index (le_sup_left : H ≤ H ⊔ K)]
    exact mul_ne_zero h1 Subgroup.index_ne_zero_of_finite
  haveI := Subgroup.fintypeOfIndexNeZero h3
  choose γ u hu ho using hw
  refine ⟨Finset.univ.image fun q : G ⧸ H => ι (γ q.out) * q.out * u q.out, ?_, fun g => ?_⟩
  · intro y hy
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hy
    exact ho _
  · set g' := (g : G ⧸ H).out with hg'
    have : g'⁻¹ * g ∈ H := QuotientGroup.eq.1 (QuotientGroup.out_eq' _)
    obtain ⟨_, ⟨γ₁, rfl⟩, _, ⟨u₁, hu₁, rfl⟩, e⟩ := Subgroup.mem_sup.1 (Subgroup.mem_comap.1 this)
    have e' : N g = N g' * (N (ι γ₁) * N u₁) := by
      rw [MonoidHom.comp_apply] at e
      rw [e, map_mul, map_inv, mul_inv_cancel_left]
    refine ⟨γ₁ * (γ g')⁻¹, (ι (γ₁ * (γ g')⁻¹))⁻¹ * g * ((u g')⁻¹ * u₁)⁻¹ * (ι (γ g') * g' * u g')⁻¹, ?_,
      ι (γ g') * g' * u g', Finset.mem_image.2 ⟨_, Finset.mem_univ _, rfl⟩, (u g')⁻¹ * u₁, mul_mem (inv_mem (hu _)) hu₁, by group⟩
    simp only [map_mul, map_inv, e']
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_one]
    abel

/- English proof (translation)
Establish `h : (⨅ v : S, (J v).comap (P.p v)).relIndex (P.box K) ≠ 0`. Use `Subgroup.relIndex_iInf_ne_zero fun v h => h1 v v.2 ?_` and prove the remaining obligations. Rewrite `h` using `[Subgroup.relIndex_comap]`. Conclude with `Subgroup.relIndex_eq_zero_of_le_right (Subgroup.map_le_iff_le_comap.2 (iInf_le (fun w => (K w).comap (P.p w)) v.1)) h`. Rewrite `h` using `[← Subgroup.inf_relIndex_right]`.

Use `fun h' => h (Subgroup.relIndex_eq_zero_of_le_left (fun g hg => Subgroup.mem_iInf.2 fun v => ?_) h')` and prove the remaining obligations. Distinguish the cases in `hv : v ∈ S`. Conclude with `Subgroup.mem_iInf.1 hg.1 ⟨v, hv⟩`. Conclude with `h2 v hv (Subgroup.mem_iInf.1 hg.2 v)`.
-/
private theorem box_idx {I G : Type} [Group G] {Gv : I → Type} [∀ v, Group (Gv v)] {K : ∀ v, Subgroup (Gv v)} (P : RPG G Gv K)
    (J : ∀ v, Subgroup (Gv v)) (S : Finset I) (h1 : ∀ v ∈ S, (J v).relIndex (K v) ≠ 0) (h2 : ∀ v ∉ S, K v ≤ J v) :
    (P.box J).relIndex (P.box K) ≠ 0 := by
  have h : (⨅ v : S, (J v).comap (P.p v)).relIndex (P.box K) ≠ 0 := by
    refine Subgroup.relIndex_iInf_ne_zero fun v h => h1 v v.2 ?_
    rw [Subgroup.relIndex_comap] at h
    exact Subgroup.relIndex_eq_zero_of_le_right (Subgroup.map_le_iff_le_comap.2 (iInf_le (fun w => (K w).comap (P.p w)) v.1)) h
  rw [← Subgroup.inf_relIndex_right] at h
  refine fun h' => h (Subgroup.relIndex_eq_zero_of_le_left (fun g hg => Subgroup.mem_iInf.2 fun v => ?_) h')
  by_cases hv : v ∈ S
  · exact Subgroup.mem_iInf.1 hg.1 ⟨v, hv⟩
  · exact h2 v hv (Subgroup.mem_iInf.1 hg.2 v)

/- English proof (translation)
Establish `h : ∀ I J : (FractionalIdeal (𝓞 F)⁰ F)ˣ, ClassGroup.mk F I = ClassGroup.mk F J → ∃ z : F, z ≠ 0 ∧ ∀ v : Pl F, FractionalIdeal.count F v (I : FractionalIdeal (𝓞 F)⁰ F) = FractionalIdeal.count F v (J : FractionalIdeal (𝓞 F)⁰ F) - WithZero.log (v.valuation F z)`. Introduce `I J e`. Establish `h1 : ClassGroup.mk F (I * J⁻¹) = 1` using `by rw [map_mul, map_inv, e, mul_inv_cancel]`. Take `⟨x, hx⟩` from `(FractionalIdeal.isPrincipal_iff _).1 (ClassGroup.mk_eq_one_iff.1 h1)`. Establish `hx0 : x ≠ 0`.

Introduce and unpack `rfl`. Conclude with `Units.ne_zero _ (hx.trans FractionalIdeal.spanSingleton_zero)`. Use `⟨x, hx0, fun v => ?_⟩` and prove the remaining obligations. Use `FractionalIdeal.count_mul F v (I * J⁻¹).ne_zero J.ne_zero` as an intermediate fact. Rewrite `this` using `[← Units.val_mul, inv_mul_cancel_right, hx, GroundTheory.Global.count_spanSingleton v hx0]`.

Use linear arithmetic over natural numbers and integers. Set `ρ : ClassGroup (𝓞 F) → (FractionalIdeal (𝓞 F)⁰ F)ˣ` to `Function.invFun (ClassGroup.mk F)`. Establish `hρ : ∀ I, ClassGroup.mk F I = ClassGroup.mk F (ρ (ClassGroup.mk F I))` using `fun I => (Function.invFun_eq ⟨I, rfl⟩).symm`. Use `choose z hz hv using fun I => h I _ (hρ I)`. Set `J : (Pl F → ℤ) → (FractionalIdeal (𝓞 F)⁰ F)ˣ` to `fun n => ∏ᶠ w, GroundTheory.Global.primeIdealUnit w ^ n w`.

Use `⟨ClassGroup (𝓞 F) × ((F →+* ℝ) → Prop), inferInstance, fun n => (ClassGroup.mk F (J n), fun σ => 0 < σ (z (J n))), ?_⟩` and prove the remaining obligations. Introduce `n m hn hm e`. Take `⟨e1, e2⟩` from `Prod.ext_iff.1 e`. Use `⟨z (J m) / z (J n), div_ne_zero (hz _) (hz _), fun σ => ?_, fun v => ?_⟩` and prove the remaining obligations. Establish `e3 : 0 < σ (z (J n)) ↔ 0 < σ (z (J m))` using `iff_of_eq (congrFun e2 σ)`.

Establish `a` using `(map_ne_zero σ).2 (hz (J n))`. Establish `b` using `(map_ne_zero σ).2 (hz (J m))`. Rewrite using `[map_div₀]`. Break down `a.lt_or_gt with a | a` into its components or cases. Conclude with `div_pos_of_neg_of_neg (b.lt_or_gt.resolve_right fun b => a.not_gt (e3.2 b)) a`.

Conclude with `div_pos (e3.1 a) a`. Establish `a` using `hv (J n) v`. Establish `b` using `hv (J m) v`. Rewrite `a` using `[GroundTheory.Global.count_finprod_primeIdealUnit_zpow _ hn]`. Rewrite `b` using `[GroundTheory.Global.count_finprod_primeIdealUnit_zpow _ hm]`.

Simplify using `only at e1`. Rewrite `a` using `[e1]`. Rewrite using `[map_div₀, WithZero.log_div ((map_ne_zero _).2 (hz _)) ((map_ne_zero _).2 (hz _))]`. Use linear arithmetic over natural numbers and integers.
-/
private theorem narrow (F : Type) [Field F] [NumberField F] : ∃ (C : Type) (_ : Finite C) (c : (Pl F → ℤ) → C), ∀ n m,
    (∀ᶠ v in Filter.cofinite, n v = 0) → (∀ᶠ v in Filter.cofinite, m v = 0) → c n = c m →
    ∃ z : F, z ≠ 0 ∧ TPos z ∧ ∀ v : Pl F, n v = m v + WithZero.log (v.valuation F z) := by
  have h : ∀ I J : (FractionalIdeal (𝓞 F)⁰ F)ˣ, ClassGroup.mk F I = ClassGroup.mk F J → ∃ z : F, z ≠ 0 ∧ ∀ v : Pl F,
      FractionalIdeal.count F v (I : FractionalIdeal (𝓞 F)⁰ F) = FractionalIdeal.count F v (J : FractionalIdeal (𝓞 F)⁰ F) - WithZero.log (v.valuation F z) := by
    intro I J e
    have h1 : ClassGroup.mk F (I * J⁻¹) = 1 := by rw [map_mul, map_inv, e, mul_inv_cancel]
    obtain ⟨x, hx⟩ := (FractionalIdeal.isPrincipal_iff _).1 (ClassGroup.mk_eq_one_iff.1 h1)
    have hx0 : x ≠ 0 := by
      rintro rfl
      exact Units.ne_zero _ (hx.trans FractionalIdeal.spanSingleton_zero)
    refine ⟨x, hx0, fun v => ?_⟩
    have := FractionalIdeal.count_mul F v (I * J⁻¹).ne_zero J.ne_zero
    rw [← Units.val_mul, inv_mul_cancel_right, hx, GroundTheory.Global.count_spanSingleton v hx0] at this
    omega
  let ρ : ClassGroup (𝓞 F) → (FractionalIdeal (𝓞 F)⁰ F)ˣ := Function.invFun (ClassGroup.mk F)
  have hρ : ∀ I, ClassGroup.mk F I = ClassGroup.mk F (ρ (ClassGroup.mk F I)) := fun I => (Function.invFun_eq ⟨I, rfl⟩).symm
  choose z hz hv using fun I => h I _ (hρ I)
  let J : (Pl F → ℤ) → (FractionalIdeal (𝓞 F)⁰ F)ˣ := fun n => ∏ᶠ w, GroundTheory.Global.primeIdealUnit w ^ n w
  refine ⟨ClassGroup (𝓞 F) × ((F →+* ℝ) → Prop), inferInstance, fun n => (ClassGroup.mk F (J n), fun σ => 0 < σ (z (J n))), ?_⟩
  intro n m hn hm e
  obtain ⟨e1, e2⟩ := Prod.ext_iff.1 e
  refine ⟨z (J m) / z (J n), div_ne_zero (hz _) (hz _), fun σ => ?_, fun v => ?_⟩
  · have e3 : 0 < σ (z (J n)) ↔ 0 < σ (z (J m)) := iff_of_eq (congrFun e2 σ)
    have a := (map_ne_zero σ).2 (hz (J n))
    have b := (map_ne_zero σ).2 (hz (J m))
    rw [map_div₀]
    rcases a.lt_or_gt with a | a
    · exact div_pos_of_neg_of_neg (b.lt_or_gt.resolve_right fun b => a.not_gt (e3.2 b)) a
    · exact div_pos (e3.1 a) a
  · have a := hv (J n) v
    have b := hv (J m) v
    rw [GroundTheory.Global.count_finprod_primeIdealUnit_zpow _ hn] at a
    rw [GroundTheory.Global.count_finprod_primeIdealUnit_zpow _ hm] at b
    dsimp only at e1
    rw [e1] at a
    rw [map_div₀, WithZero.log_div ((map_ne_zero _).2 (hz _)) ((map_ne_zero _).2 (hz _))]
    omega

section Loc

variable {K : Type} [Field K] {Δ : K}

/- English proof (translation)
Establish `h : GeneralLinearGroup.map (starRingEnd (Lsq K Δ)) g.1 = (wJ Δ)⁻¹ * g.1 * (wJ Δ)⁻¹⁻¹` using `g.2`. Establish `h1` using `congrArg (fun x => (GeneralLinearGroup.det x : Lsq K Δ)) h`. Simplify using `only [map_mul, map_inv, mul_right_comm _ (GeneralLinearGroup.det g.1), mul_inv_cancel, one_mul] at h1`. Establish `h2 : star (mt g).det = (mt g).det`. Rewrite using `[← starRingEnd_apply, RingHom.map_det]`.

Conclude with `h1`. Establish `h3` using `congrArg QuadraticAlgebra.im h2`. Rewrite `h3` using `[QuadraticAlgebra.im_star]`. Use `ext`. Simplify using the standard rewrite rules.

Simplify using `using (self_eq_neg.1 h3.symm)`.
-/
private theorem det_eq [CharZero K] (g : DX Δ) : (mt g).det = algebraMap K _ (mt g).det.re := by
  have h : GeneralLinearGroup.map (starRingEnd (Lsq K Δ)) g.1 = (wJ Δ)⁻¹ * g.1 * (wJ Δ)⁻¹⁻¹ := g.2
  have h1 := congrArg (fun x => (GeneralLinearGroup.det x : Lsq K Δ)) h
  simp only [map_mul, map_inv, mul_right_comm _ (GeneralLinearGroup.det g.1), mul_inv_cancel, one_mul] at h1
  have h2 : star (mt g).det = (mt g).det := by
    rw [← starRingEnd_apply, RingHom.map_det]
    exact h1
  have h3 := congrArg QuadraticAlgebra.im h2
  rw [QuadraticAlgebra.im_star] at h3
  ext
  · simp
  · simpa using (self_eq_neg.1 h3.symm)

/- English proof (translation)
Set `f : DX Δ →* K` to `{ toFun := fun g => (Glob.mt g).det.re map_one' := (congrArg QuadraticAlgebra.re (det_one (n := Fin 2) (R := Lsq K Δ))).trans QuadraticAlgebra.re_one map_mul' := fun a b => by`. Establish `: (mt (a * b)).det = (mt a).det * (mt b).det` using `by rw [← det_mul]; rfl`. Rewrite using `[this, det_eq a, det_eq b, ← map_mul]`. Simplify using `}`. Conclude with `⟨f.toHomUnits, det_eq⟩`.
-/
private theorem nrd_ex [CharZero K] (Δ : K) : ∃ N : DX Δ →* Kˣ, ∀ g : DX Δ, (Glob.mt g).det = algebraMap K _ (N g : K) := by
  let f : DX Δ →* K :=
    { toFun := fun g => (Glob.mt g).det.re
      map_one' := (congrArg QuadraticAlgebra.re (det_one (n := Fin 2) (R := Lsq K Δ))).trans QuadraticAlgebra.re_one
      map_mul' := fun a b => by
        have : (mt (a * b)).det = (mt a).det * (mt b).det := by rw [← det_mul]; rfl
        rw [this, det_eq a, det_eq b, ← map_mul]
        simp }
  exact ⟨f.toHomUnits, det_eq⟩

variable (O : Type) [CommRing O] [Algebra O K]

/- English proof (translation)
Take `⟨k, hk⟩` from `h`. Establish `: mt g = ((integralClosure O (Lsq K Δ)).val : integralClosure O (Lsq K Δ) →+* Lsq K Δ).mapMatrix k.1` using `(congrArg Units.val hk).symm`. Rewrite using `[this, ← RingHom.map_det]`. Conclude with `(k.1.det).2`.
-/
private theorem det_int {g : DX Δ} (h : g ∈ KD Δ O) : IsIntegral O (mt g).det := by
  obtain ⟨k, hk⟩ := h
  have : mt g = ((integralClosure O (Lsq K Δ)).val : integralClosure O (Lsq K Δ) →+* Lsq K Δ).mapMatrix k.1 :=
    (congrArg Units.val hk).symm
  rw [this, ← RingHom.map_det]
  exact (k.1.det).2

/- English proof (translation)
Set `f : Lsq K Δ →ₐ[O] Lsq K Δ` to `{ starRingEnd (Lsq K Δ) with commutes' := fun r => by`. Rewrite using `[Algebra.algebraMap_eq_smul_one]`. Apply the tactic sequence `ext <;> simp [starRingEnd_apply, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one] }`. Conclude with `h.map f`.
-/
private theorem star_int {x : Lsq K Δ} (h : IsIntegral O x) : IsIntegral O (star x) := by
  let f : Lsq K Δ →ₐ[O] Lsq K Δ := { starRingEnd (Lsq K Δ) with
    commutes' := fun r => by
      rw [Algebra.algebraMap_eq_smul_one]
      ext <;> simp [starRingEnd_apply, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one] }
  exact h.map f

/- English proof (translation)
Set `R` to `integralClosure O (Lsq K Δ)`. Set `a : R` to `⟨ν, h⟩`. Set `b : R` to `⟨star ν, star_int O h⟩`. Establish `e1 : ν * star ν = algebraMap K _ (algebraMap O K u)` using `by rw [← e, QuadraticAlgebra.algebraMap_norm_eq_mul_star]`. Establish `e2 : a * b = algebraMap O R u` using `Subtype.ext (e1.trans (IsScalarTower.algebraMap_apply O K (Lsq K Δ) u).symm)`.

Establish `hu : IsUnit (!![a, 0; 0, b]).det`. Rewrite using `[det_fin_two_of, mul_zero, sub_zero, e2]`. Conclude with `u.isUnit.map _`. Set `k : GL (Fin 2) R` to `GeneralLinearGroup.mk'' _ hu`. Set `g` to `GeneralLinearGroup.map (R.val : R →+* Lsq K Δ) k`.

Establish `hg : (g : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) = !![ν, 0; 0, star ν]`. Use extensionality with `i j : 1`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> rfl`. Establish `hD : g ∈ DX Δ`. Express the relevant statement in the definitionally equal form `GeneralLinearGroup.map (starRingEnd (Lsq K Δ)) g = (wJ Δ)⁻¹ * g * (wJ Δ)⁻¹⁻¹`.

Apply `Units.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `(g : Matrix (Fin 2) (Fin 2) (Lsq K Δ)).map (starRingEnd _) = !![0, -1; 1, 0] * (g : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) * !![0, 1; -1, 0]`. Rewrite using `[hg]`. Use extensionality with `i j : 1`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [starRingEnd_apply]`.

Use `⟨⟨g, hD⟩, ⟨k, rfl⟩, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(g : Matrix (Fin 2) (Fin 2) (Lsq K Δ)).det = _`. Rewrite using `[hg, det_fin_two_of, mul_zero, sub_zero, e1]`.
-/
private theorem unit_ex (u : Oˣ) (ν : Lsq K Δ) (h : IsIntegral O ν) (e : QuadraticAlgebra.norm ν = algebraMap O K u) :
    ∃ k ∈ KD Δ O, (mt k).det = algebraMap K _ (algebraMap O K u) := by
  let R := integralClosure O (Lsq K Δ)
  let a : R := ⟨ν, h⟩
  let b : R := ⟨star ν, star_int O h⟩
  have e1 : ν * star ν = algebraMap K _ (algebraMap O K u) := by rw [← e, QuadraticAlgebra.algebraMap_norm_eq_mul_star]
  have e2 : a * b = algebraMap O R u := Subtype.ext (e1.trans (IsScalarTower.algebraMap_apply O K (Lsq K Δ) u).symm)
  have hu : IsUnit (!![a, 0; 0, b]).det := by
    rw [det_fin_two_of, mul_zero, sub_zero, e2]
    exact u.isUnit.map _
  let k : GL (Fin 2) R := GeneralLinearGroup.mk'' _ hu
  let g := GeneralLinearGroup.map (R.val : R →+* Lsq K Δ) k
  have hg : (g : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) = !![ν, 0; 0, star ν] := by
    ext i j : 1
    fin_cases i <;> fin_cases j <;> rfl
  have hD : g ∈ DX Δ := by
    change GeneralLinearGroup.map (starRingEnd (Lsq K Δ)) g = (wJ Δ)⁻¹ * g * (wJ Δ)⁻¹⁻¹
    apply Units.ext
    change (g : Matrix (Fin 2) (Fin 2) (Lsq K Δ)).map (starRingEnd _) = !![0, -1; 1, 0] * (g : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) * !![0, 1; -1, 0]
    rw [hg]
    ext i j : 1
    fin_cases i <;> fin_cases j <;> simp [starRingEnd_apply]
  refine ⟨⟨g, hD⟩, ⟨k, rfl⟩, ?_⟩
  change (g : Matrix (Fin 2) (Fin 2) (Lsq K Δ)).det = _
  rw [hg, det_fin_two_of, mul_zero, sub_zero, e1]

/- English proof (translation)
Take `⟨s, rfl⟩` from `h`. Establish `hs : s ≠ 0` using `left_ne_zero_of_mul h0`. Use `set x := algebraMap O K u with hx`. Set `ν : Lsq K (s * s)` to `⟨(x + 1) / 2, (x - 1) / (2 * s)⟩`. Use `⟨ν, ⟨(Polynomial.X - Polynomial.C (u : O)) * (Polynomial.X - Polynomial.C 1), (Polynomial.monic_X_sub_C _).mul (Polynomial.monic_X_sub_C _), ?_⟩, ?_⟩` and prove the remaining obligations.

Rewrite using `[Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_C, Polynomial.eval₂_C, IsScalarTower.algebraMap_apply O K (Lsq K (s * s)) u, map_one, ← hx]`. Apply the tactic sequence `ext <;> simp [ν, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one] <;> field_simp <;> ring`. Simplify using `only [QuadraticAlgebra.norm_def, ν]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem split_ex [CharZero K] (h0 : Δ ≠ 0) (h : IsSquare Δ) (u : Oˣ) :
    ∃ ν : Lsq K Δ, IsIntegral O ν ∧ QuadraticAlgebra.norm ν = algebraMap O K u := by
  obtain ⟨s, rfl⟩ := h
  have hs : s ≠ 0 := left_ne_zero_of_mul h0
  set x := algebraMap O K u with hx
  let ν : Lsq K (s * s) := ⟨(x + 1) / 2, (x - 1) / (2 * s)⟩
  refine ⟨ν, ⟨(Polynomial.X - Polynomial.C (u : O)) * (Polynomial.X - Polynomial.C 1),
    (Polynomial.monic_X_sub_C _).mul (Polynomial.monic_X_sub_C _), ?_⟩, ?_⟩
  · rw [Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_C,
      Polynomial.eval₂_C, IsScalarTower.algebraMap_apply O K (Lsq K (s * s)) u, map_one, ← hx]
    ext <;> simp [ν, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one] <;> field_simp <;> ring
  · simp only [QuadraticAlgebra.norm_def, ν]
    field_simp
    ring

end Loc

section Place

variable {F : Type} [Field F] [NumberField F] {v : Pl F} {Δ : Kv v} {N : DX Δ →* (Kv v)ˣ}

/- English proof (translation)
Establish `h : ∀ g ∈ KD Δ (Ov v), Valued.v (N g : Kv v) ≤ 1` using `fun g hg => by`. Establish `h1` using `det_int (Ov v) hg`. Rewrite `h1` using `[hN, isIntegral_algebraMap_iff QuadraticAlgebra.algebraMap_injective]`. Take `⟨y, hy⟩` from `IsIntegrallyClosed.isIntegral_iff.1 h1`. Rewrite using `[← hy]`.

Conclude with `y.2`. Establish `h2` using `h _ (inv_mem hg)`. Rewrite `h2` using `[map_inv, Units.val_inv_eq_inv_val, map_inv₀, inv_le_one₀ (zero_lt_iff.2 ((map_ne_zero _).2 (N g).ne_zero))]`. Conclude with `le_antisymm (h g hg) h2`.
-/
private theorem val_one (hN : ∀ g : DX Δ, (Glob.mt g).det = algebraMap _ _ (N g : Kv v)) {g : DX Δ} (hg : g ∈ KD Δ (Ov v)) :
    Valued.v (N g : Kv v) = 1 := by
  have h : ∀ g ∈ KD Δ (Ov v), Valued.v (N g : Kv v) ≤ 1 := fun g hg => by
    have h1 := det_int (Ov v) hg
    rw [hN, isIntegral_algebraMap_iff QuadraticAlgebra.algebraMap_injective] at h1
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h1
    rw [← hy]
    exact y.2
  have h2 := h _ (inv_mem hg)
  rw [map_inv, Units.val_inv_eq_inv_val, map_inv₀, inv_le_one₀ (zero_lt_iff.2 ((map_ne_zero _).2 (N g).ne_zero))] at h2
  exact le_antisymm (h g hg) h2

/- English proof (translation)
Take `⟨u, hu⟩` from `(HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one (a := (⟨x, hx.le⟩ : Ov v))).2 hx`. Take `⟨ν, h1, h2⟩` from `h u`. Take `⟨k, hk, e⟩` from `unit_ex (Ov v) u ν h1 h2`. Use `⟨k, hk, Units.ext ?_⟩` and prove the remaining obligations. Rewrite `e` using `[hN]`.

Rewrite using `[QuadraticAlgebra.algebraMap_injective e, hu]`. Both sides reduce to the same expression.
-/
private theorem of_val_one (hN : ∀ g : DX Δ, (Glob.mt g).det = algebraMap _ _ (N g : Kv v))
    (h : ∀ u : (Ov v)ˣ, ∃ ν : Lsq (Kv v) Δ, IsIntegral (Ov v) ν ∧ QuadraticAlgebra.norm ν = algebraMap (Ov v) (Kv v) u)
    (x : (Kv v)ˣ) (hx : Valued.v (x : Kv v) = 1) : ∃ k ∈ KD Δ (Ov v), N k = x := by
  obtain ⟨u, hu⟩ := (HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one (a := (⟨x, hx.le⟩ : Ov v))).2 hx
  obtain ⟨ν, h1, h2⟩ := h u
  obtain ⟨k, hk, e⟩ := unit_ex (Ov v) u ν h1 h2
  refine ⟨k, hk, Units.ext ?_⟩
  rw [hN] at e
  rw [QuadraticAlgebra.algebraMap_injective e, hu]
  rfl

end Place

/- English proof (translation)
Introduce `F _ _ Δ D hD ι hι`. Establish `hΔ : Δ ≠ 0` using `by haveI := hD.real`. Take `⟨w⟩ : Nonempty (InfinitePlace F)` from `inferInstance`. Introduce and unpack `rfl`. Simplify using `using hD.neg (InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal w))`.

Use `haveI : ∀ v : Pl F, CharZero (Kv v) := fun v => charZero_of_injective_algebraMap (cv v).injective`. Use `choose Nv hNv using fun v : Pl F => nrd_ex (cv v Δ)`. Set `P` to `rpg (fun v : Pl F => DX (cv v Δ)) fun v => KD (cv v Δ) (Ov v)`. Set `N : DA Δ →* ∀ v : Pl F, (Kv v)ˣ` to `Pi.monoidHom fun v => (Nv v).comp (P.p v)`. Establish `hN : ∀ g v, N g v = Nv v (P.p v g)` using `fun _ _ => rfl`.

Take `⟨C, _, c, hc⟩` from `narrow F`. Establish `hae : ∀ g : DA Δ, ∀ᶠ v in Filter.cofinite, WithZero.log (Valued.v (N g v : Kv v)) = 0` using `fun g => (P.ae g).mono fun v hv => by rw [hN, val_one (hNv v) hv, WithZero.log_one]`. Establish `hloc : ∀ (v : Pl F) (u : (Ov v)ˣ), ∃ ν : Lsq (Kv v) (cv v Δ), IsIntegral (Ov v) ν ∧ QuadraticAlgebra.norm ν = algebraMap (Ov v) (Kv v) u` using `fun v u => by`. Distinguish the cases in `hv : v ∈ D.Sg`. Conclude with `split_ex (Ov v) ((map_ne_zero _).2 hΔ) (hD.split v hv) u`.

Conclude with `normEx _ _ _ (hD.off v hv) u`. Establish `hidx : D.U2.relIndex (P.box fun v => KD (cv v Δ) (Ov v)) ≠ 0` using `box_idx P D.J2v D.Sg (fun v hv => by rw [Dat.J2v, if_pos hv]; exact (hD.sig v hv).levelTwoFiniteIndex) fun v hv => by rw [Dat.J2v, if_neg hv]`. Take `⟨Y, hY, h⟩` from `reps ι N D.U2 _ D.Off hidx (fun g => c fun v => WithZero.log (Valued.v (N g v : Kv v))) (fun g g' e => by`. Take `⟨z, hz, hp, e⟩` from `hc _ _ (hae g) (hae g') e`. Take `⟨γ, hγ⟩` from `normD F Δ D hD z hp`.

Establish `h1 : ∀ v, (N (ι γ) v : Kv v) = cv v z` using `fun v => by`. Apply `QuadraticAlgebra.algebraMap_injective (a := cv v Δ) (b := 0)` to reduce the goal to its premises. Rewrite using `[hN, ← hNv]`. Express the relevant statement in the definitionally equal form `(Glob.mt ((ι γ).1 v)).det = _`. Rewrite using `[hι, ← RingHom.mapMatrix_apply, ← RingHom.map_det, hγ]`.

Apply the tactic sequence `ext <;> simp [lmap]`. Establish `h2 : ∀ v, Valued.v ((((N g' v * N (ι γ) v)⁻¹ * N g v : (Kv v)ˣ)) : Kv v) = 1` using `fun v => by`. Establish `a : ∀ x : (Kv v)ˣ, Valued.v (x : Kv v) ≠ 0` using `fun x => (map_ne_zero _).2 x.ne_zero`. Establish `b : Valued.v (cv v z) = v.valuation F z` using `HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v z`. Establish `d : Valued.v (N g v : Kv v) = Valued.v ((N g' v * N (ι γ) v : (Kv v)ˣ) : Kv v)`.

Rewrite using `[← WithZero.exp_log (a (N g v)), ← WithZero.exp_log (a (_ * _)), e v, Units.val_mul, map_mul, WithZero.log_mul (a _) (a _), h1, b]`. Rewrite using `[Units.val_mul, map_mul, d, ← map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, map_one]`. Use `choose k hk ek using fun v => of_val_one (hNv v) (hloc v) _ (h2 v)`. Take `⟨k', hk'⟩` from `P.surj k (Filter.Eventually.of_forall hk)`. Use `⟨γ, k', Subgroup.mem_iInf.2 fun v => ?_, funext fun v => ?_⟩` and prove the remaining obligations.

Rewrite using `[Subgroup.mem_comap, hk']`. Conclude with `hk v`. Rewrite using `[Pi.mul_apply, Pi.mul_apply, hN k', hk', ek, mul_inv_cancel_left])`. Use the proof step `(weakD F Δ D hD ι hι)`. Use `⟨Y, hY, fun g => ?_⟩` and prove the remaining obligations.

Take `⟨γ, s, hs, r⟩` from `h g`. Use `⟨γ, s, Subgroup.mem_iInf.2 fun v => ?_, r⟩` and prove the remaining obligations. Establish `h1` using `hNv v (P.p v s)`. Rewrite `h1` using `[← hN, hs, Pi.one_apply, Units.val_one, map_one]`. Conclude with `Units.ext h1`.
-/
theorem UpperTheory.V.Z.Sym.Glob.classRep :
    UpperTheory.V.Z.Sym.Glob.ClassRep := by
  intro F _ _ Δ D hD ι hι
  have hΔ : Δ ≠ 0 := by
    haveI := hD.real
    obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
    rintro rfl
    simpa using hD.neg (InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal w))
  haveI : ∀ v : Pl F, CharZero (Kv v) := fun v => charZero_of_injective_algebraMap (cv v).injective
  choose Nv hNv using fun v : Pl F => nrd_ex (cv v Δ)
  let P := rpg (fun v : Pl F => DX (cv v Δ)) fun v => KD (cv v Δ) (Ov v)
  let N : DA Δ →* ∀ v : Pl F, (Kv v)ˣ := Pi.monoidHom fun v => (Nv v).comp (P.p v)
  have hN : ∀ g v, N g v = Nv v (P.p v g) := fun _ _ => rfl
  obtain ⟨C, _, c, hc⟩ := narrow F
  have hae : ∀ g : DA Δ, ∀ᶠ v in Filter.cofinite, WithZero.log (Valued.v (N g v : Kv v)) = 0 := fun g =>
    (P.ae g).mono fun v hv => by rw [hN, val_one (hNv v) hv, WithZero.log_one]
  have hloc : ∀ (v : Pl F) (u : (Ov v)ˣ), ∃ ν : Lsq (Kv v) (cv v Δ), IsIntegral (Ov v) ν ∧
      QuadraticAlgebra.norm ν = algebraMap (Ov v) (Kv v) u := fun v u => by
    by_cases hv : v ∈ D.Sg
    · exact split_ex (Ov v) ((map_ne_zero _).2 hΔ) (hD.split v hv) u
    · exact normEx _ _ _ (hD.off v hv) u
  have hidx : D.U2.relIndex (P.box fun v => KD (cv v Δ) (Ov v)) ≠ 0 :=
    box_idx P D.J2v D.Sg (fun v hv => by rw [Dat.J2v, if_pos hv]; exact (hD.sig v hv).levelTwoFiniteIndex)
      fun v hv => by rw [Dat.J2v, if_neg hv]
  obtain ⟨Y, hY, h⟩ := reps ι N D.U2 _ D.Off hidx (fun g => c fun v => WithZero.log (Valued.v (N g v : Kv v)))
    (fun g g' e => by
      obtain ⟨z, hz, hp, e⟩ := hc _ _ (hae g) (hae g') e
      obtain ⟨γ, hγ⟩ := normD F Δ D hD z hp
      have h1 : ∀ v, (N (ι γ) v : Kv v) = cv v z := fun v => by
        apply QuadraticAlgebra.algebraMap_injective (a := cv v Δ) (b := 0)
        rw [hN, ← hNv]
        change (Glob.mt ((ι γ).1 v)).det = _
        rw [hι, ← RingHom.mapMatrix_apply, ← RingHom.map_det, hγ]
        ext <;> simp [lmap]
      have h2 : ∀ v, Valued.v ((((N g' v * N (ι γ) v)⁻¹ * N g v : (Kv v)ˣ)) : Kv v) = 1 := fun v => by
        have a : ∀ x : (Kv v)ˣ, Valued.v (x : Kv v) ≠ 0 := fun x => (map_ne_zero _).2 x.ne_zero
        have b : Valued.v (cv v z) = v.valuation F z := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v z
        have d : Valued.v (N g v : Kv v) = Valued.v ((N g' v * N (ι γ) v : (Kv v)ˣ) : Kv v) := by
          rw [← WithZero.exp_log (a (N g v)), ← WithZero.exp_log (a (_ * _)), e v, Units.val_mul, map_mul,
            WithZero.log_mul (a _) (a _), h1, b]
        rw [Units.val_mul, map_mul, d, ← map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, map_one]
      choose k hk ek using fun v => of_val_one (hNv v) (hloc v) _ (h2 v)
      obtain ⟨k', hk'⟩ := P.surj k (Filter.Eventually.of_forall hk)
      refine ⟨γ, k', Subgroup.mem_iInf.2 fun v => ?_, funext fun v => ?_⟩
      · rw [Subgroup.mem_comap, hk']
        exact hk v
      · rw [Pi.mul_apply, Pi.mul_apply, hN k', hk', ek, mul_inv_cancel_left])
    (weakD F Δ D hD ι hι)
  refine ⟨Y, hY, fun g => ?_⟩
  obtain ⟨γ, s, hs, r⟩ := h g
  refine ⟨γ, s, Subgroup.mem_iInf.2 fun v => ?_, r⟩
  have h1 := hNv v (P.p v s)
  rw [← hN, hs, Pi.one_apply, Units.val_one, map_one] at h1
  exact Units.ext h1
