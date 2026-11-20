import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoRes
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoFinite

open IsLocalRing MvPowerSeries UpperTheory.V.Alg

/- English proof (translation)
Establish `hb : (I ^ N • ⊤ : Submodule R R) = ⊥` using `by rw [h, Submodule.bot_smul]`. Establish `key : ∀ x y : R, x ≡ y [SMOD (I ^ N • ⊤ : Submodule R R)] → x = y`. Introduce `x y hxy`. Rewrite `hxy` using `[hb, SModEq.sub_mem, Submodule.mem_bot, sub_eq_zero]`. Conclude with `hxy`.

Use `{ haus' := ?_, prec' := ?_ }` and prove the remaining obligations. Introduce `x hx`. Conclude with `key x 0 (hx N)`. Introduce `f hf`. Use `⟨f N, fun n => ?_⟩` and prove the remaining obligations.

Break down `le_total n N with hn | hn` into its components or cases. Conclude with `hf hn`. Establish `e` using `key _ _ (hf hn)`. Rewrite using `[SModEq.sub_mem, e, sub_self]`. Conclude with `Submodule.zero_mem _`.
-/
private theorem complete_of_pow {R : Type} [CommRing R] (I : Ideal R) (N : ℕ) (h : I ^ N = ⊥) :
    IsAdicComplete I R := by
  have hb : (I ^ N • ⊤ : Submodule R R) = ⊥ := by rw [h, Submodule.bot_smul]
  have key : ∀ x y : R, x ≡ y [SMOD (I ^ N • ⊤ : Submodule R R)] → x = y := by
    intro x y hxy
    rw [hb, SModEq.sub_mem, Submodule.mem_bot, sub_eq_zero] at hxy
    exact hxy
  refine { haus' := ?_, prec' := ?_ }
  · intro x hx
    exact key x 0 (hx N)
  · intro f hf
    refine ⟨f N, fun n => ?_⟩
    rcases le_total n N with hn | hn
    · exact hf hn
    · have e := key _ _ (hf hn)
      rw [SModEq.sub_mem, e, sub_self]
      exact Submodule.zero_mem _

/- English proof (translation)
Substitute `h` using the available equality. Introduce `x y hxy`. Rewrite `hxy` using `[Ideal.Quotient.eq, Ideal.mem_bot, sub_eq_zero]`. Conclude with `hxy`.
-/
private theorem mk_inj {R : Type} [CommRing R] (I : Ideal R) (h : I = ⊥) :
    Function.Injective (Ideal.Quotient.mk I) := by
  subst h
  intro x y hxy
  rw [Ideal.Quotient.eq, Ideal.mem_bot, sub_eq_zero] at hxy
  exact hxy

/- English proof (translation)
Use `haveI : Finite (ResidueField A) := Finite.of_surjective _ (resMap_bijective O A).2`. Use `haveI : Finite (A ⧸ maximalIdeal A) := this`. Use `haveI := Ideal.finite_quotient_pow (IsNoetherian.noetherian (maximalIdeal A)) N`. Conclude with `Finite.of_injective _ (mk_inj _ h)`.
-/
private theorem finite_of_pow (O : Type) [CommRing O] [IsLocalRing O] [Finite (ResidueField O)]
    (A : Type) [CommRing A] [Algebra O A] [IsCO O A] (N : ℕ) (h : maximalIdeal A ^ N = ⊥) : Finite A := by
  haveI : Finite (ResidueField A) := Finite.of_surjective _ (resMap_bijective O A).2
  haveI : Finite (A ⧸ maximalIdeal A) := this
  haveI := Ideal.finite_quotient_pow (IsNoetherian.noetherian (maximalIdeal A)) N
  exact Finite.of_injective _ (mk_inj _ h)

/- English proof (translation)
Use `haveI : Finite A₁ := finite_of_pow O A₁ N h₁`. Use `haveI : Finite A₂ := finite_of_pow O A₂ N h₂`. Establish `hinj' : Function.Injective (fun x : B => (p₁ x, p₂ x))` using `fun x y hxy => hinj x y (congrArg Prod.fst hxy) (congrArg Prod.snd hxy)`. Use `haveI : Finite B := Finite.of_injective _ hinj'`. Set `φ : B →ₐ[O] ResidueField O` to `(res O A₁).comp p₁`.

Establish `hφ1 : ∀ x, φ x = res O A₁ (p₁ x)` using `fun x => rfl`. Establish `hφ2 : ∀ x, φ x = res O A₂ (p₂ x)` using `fun x => hres x`. Establish `hunit : ∀ x : B, φ x ≠ 0 → IsUnit x`. Introduce `x hx`. Establish `u1 : IsUnit (p₁ x)`.

Assume the negation of the conclusion as `hn`. Apply `hx` to reduce the goal to its premises. Rewrite using `[hφ1, res_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]`. Conclude with `hn`. Establish `u2 : IsUnit (p₂ x)`.

Assume the negation of the conclusion as `hn`. Apply `hx` to reduce the goal to its premises. Rewrite using `[hφ2, res_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]`. Conclude with `hn`. Establish `hmul : Function.Injective (fun y : B => x * y)`.

Introduce `y z hyz`. Establish `e1` using `congrArg p₁ hyz`. Establish `e2` using `congrArg p₂ hyz`. Simplify using `only [map_mul] at e1 e2`. Conclude with `hinj y z (u1.mul_left_cancel e1) (u2.mul_left_cancel e2)`.

Take `⟨y, hy⟩` from `(Finite.injective_iff_surjective.mp hmul) 1`. Establish `hy' : x * y = 1` using `hy`. Conclude with `⟨⟨x, y, hy', by rw [mul_comm]; exact hy'⟩, rfl⟩`. Establish `hnon : ∀ x : B, IsUnit x → φ x ≠ 0` using `fun x hx => (hx.map φ).ne_zero`. Use `haveI : Nontrivial B := ⟨⟨0, 1, fun h01 => by`.

Establish `e` using `congrArg φ h01`. Rewrite `e` using `[map_zero, map_one]`. Conclude with `zero_ne_one e⟩⟩`. Use `haveI : IsLocalRing B := IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => by`. Distinguish the cases in `ha : φ a = 0`.

Use `right`. Apply `hunit` to reduce the goal to its premises. Rewrite using `[map_sub, map_one, ha, sub_zero]`. Conclude with `one_ne_zero`. Use `left`.

Conclude with `hunit a ha`. Establish `hmax : ∀ x : B, x ∈ maximalIdeal B ↔ φ x = 0`. Introduce `x`. Rewrite using `[IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]`. Prove the components needed by the constructor for the conclusion.

Introduce `hx`. Assume the negation of the conclusion as `hne`. Conclude with `hx (hunit x hne)`. Introduce `hx hu`. Conclude with `hnon x hu hx`.

Use `haveI : IsNoetherian B B := inferInstance`. Establish `hpow : maximalIdeal B ^ N = ⊥`. Rewrite using `[eq_bot_iff]`. Introduce `x hx`. Rewrite using `[Ideal.mem_bot]`.

Establish `m1 : Ideal.map p₁ (maximalIdeal B) ≤ maximalIdeal A₁`. Rewrite using `[Ideal.map_le_iff_le_comap]`. Introduce `y hy`. Rewrite using `[Ideal.mem_comap, ← res_eq_zero_iff O, ← hφ1]`. Conclude with `(hmax y).mp hy`.

Establish `m2 : Ideal.map p₂ (maximalIdeal B) ≤ maximalIdeal A₂`. Rewrite using `[Ideal.map_le_iff_le_comap]`. Introduce `y hy`. Rewrite using `[Ideal.mem_comap, ← res_eq_zero_iff O, ← hφ2]`. Conclude with `(hmax y).mp hy`.

Establish `x1 : p₁ x ∈ maximalIdeal A₁ ^ N`. Apply `pow_le_pow_left' m1 N` to reduce the goal to its premises. Rewrite using `[← Ideal.map_pow]`. Conclude with `Ideal.mem_map_of_mem p₁ hx`. Establish `x2 : p₂ x ∈ maximalIdeal A₂ ^ N`.

Apply `pow_le_pow_left' m2 N` to reduce the goal to its premises. Rewrite using `[← Ideal.map_pow]`. Conclude with `Ideal.mem_map_of_mem p₂ hx`. Rewrite `x1` using `[h₁, Ideal.mem_bot]`. Rewrite `x2` using `[h₂, Ideal.mem_bot]`.

Conclude with `hinj x 0 (by rw [x1, map_zero]) (by rw [x2, map_zero])`. Use `⟨{ complete := complete_of_pow _ N hpow, isLocalHom := ⟨fun a ha => ?_⟩, res_surj := fun x => ?_ }, hpow⟩` and prove the remaining obligations. Rewrite using `[← IsLocalRing.residue_ne_zero_iff_isUnit, ← ResidueField.algebraMap_eq, ← AlgHom.commutes φ]`. Conclude with `hnon _ ha`. Take `⟨a, ha⟩` from `IsLocalRing.residue_surjective (φ x)`.

Use `⟨a, (hmax _).mpr ?_⟩` and prove the remaining obligations. Rewrite using `[map_sub, AlgHom.commutes, ResidueField.algebraMap_eq, ha, sub_self]`.
-/
private theorem sub_co (O : Type) [CommRing O] [IsLocalRing O] [Finite (ResidueField O)] (N : ℕ)
    (A₁ : Type) [CommRing A₁] [Algebra O A₁] [IsCO O A₁] (A₂ : Type) [CommRing A₂] [Algebra O A₂] [IsCO O A₂]
    (h₁ : maximalIdeal A₁ ^ N = ⊥) (h₂ : maximalIdeal A₂ ^ N = ⊥) (B : Type) [CommRing B] [Algebra O B]
    (p₁ : B →ₐ[O] A₁) (p₂ : B →ₐ[O] A₂) (hinj : ∀ x y, p₁ x = p₁ y → p₂ x = p₂ y → x = y)
    (hres : ∀ x, res O A₁ (p₁ x) = res O A₂ (p₂ x)) :
    ∃ _ : IsCO O B, maximalIdeal B ^ N = ⊥ := by
  classical
  haveI : Finite A₁ := finite_of_pow O A₁ N h₁
  haveI : Finite A₂ := finite_of_pow O A₂ N h₂
  have hinj' : Function.Injective (fun x : B => (p₁ x, p₂ x)) := fun x y hxy =>
    hinj x y (congrArg Prod.fst hxy) (congrArg Prod.snd hxy)
  haveI : Finite B := Finite.of_injective _ hinj'
  let φ : B →ₐ[O] ResidueField O := (res O A₁).comp p₁
  have hφ1 : ∀ x, φ x = res O A₁ (p₁ x) := fun x => rfl
  have hφ2 : ∀ x, φ x = res O A₂ (p₂ x) := fun x => hres x
  have hunit : ∀ x : B, φ x ≠ 0 → IsUnit x := by
    intro x hx
    have u1 : IsUnit (p₁ x) := by
      by_contra hn
      apply hx
      rw [hφ1, res_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      exact hn
    have u2 : IsUnit (p₂ x) := by
      by_contra hn
      apply hx
      rw [hφ2, res_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      exact hn
    have hmul : Function.Injective (fun y : B => x * y) := by
      intro y z hyz
      have e1 := congrArg p₁ hyz
      have e2 := congrArg p₂ hyz
      simp only [map_mul] at e1 e2
      exact hinj y z (u1.mul_left_cancel e1) (u2.mul_left_cancel e2)
    obtain ⟨y, hy⟩ := (Finite.injective_iff_surjective.mp hmul) 1
    have hy' : x * y = 1 := hy
    exact ⟨⟨x, y, hy', by rw [mul_comm]; exact hy'⟩, rfl⟩
  have hnon : ∀ x : B, IsUnit x → φ x ≠ 0 := fun x hx => (hx.map φ).ne_zero
  haveI : Nontrivial B := ⟨⟨0, 1, fun h01 => by
    have e := congrArg φ h01
    rw [map_zero, map_one] at e
    exact zero_ne_one e⟩⟩
  haveI : IsLocalRing B := IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => by
    by_cases ha : φ a = 0
    · right
      apply hunit
      rw [map_sub, map_one, ha, sub_zero]
      exact one_ne_zero
    · left
      exact hunit a ha
  have hmax : ∀ x : B, x ∈ maximalIdeal B ↔ φ x = 0 := by
    intro x
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    constructor
    · intro hx
      by_contra hne
      exact hx (hunit x hne)
    · intro hx hu
      exact hnon x hu hx
  haveI : IsNoetherian B B := inferInstance
  have hpow : maximalIdeal B ^ N = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Ideal.mem_bot]
    have m1 : Ideal.map p₁ (maximalIdeal B) ≤ maximalIdeal A₁ := by
      rw [Ideal.map_le_iff_le_comap]
      intro y hy
      rw [Ideal.mem_comap, ← res_eq_zero_iff O, ← hφ1]
      exact (hmax y).mp hy
    have m2 : Ideal.map p₂ (maximalIdeal B) ≤ maximalIdeal A₂ := by
      rw [Ideal.map_le_iff_le_comap]
      intro y hy
      rw [Ideal.mem_comap, ← res_eq_zero_iff O, ← hφ2]
      exact (hmax y).mp hy
    have x1 : p₁ x ∈ maximalIdeal A₁ ^ N := by
      apply pow_le_pow_left' m1 N
      rw [← Ideal.map_pow]
      exact Ideal.mem_map_of_mem p₁ hx
    have x2 : p₂ x ∈ maximalIdeal A₂ ^ N := by
      apply pow_le_pow_left' m2 N
      rw [← Ideal.map_pow]
      exact Ideal.mem_map_of_mem p₂ hx
    rw [h₁, Ideal.mem_bot] at x1
    rw [h₂, Ideal.mem_bot] at x2
    exact hinj x 0 (by rw [x1, map_zero]) (by rw [x2, map_zero])
  refine ⟨{ complete := complete_of_pow _ N hpow, isLocalHom := ⟨fun a ha => ?_⟩, res_surj := fun x => ?_ }, hpow⟩
  · rw [← IsLocalRing.residue_ne_zero_iff_isUnit, ← ResidueField.algebraMap_eq, ← AlgHom.commutes φ]
    exact hnon _ ha
  · obtain ⟨a, ha⟩ := IsLocalRing.residue_surjective (φ x)
    refine ⟨a, (hmax _).mpr ?_⟩
    rw [map_sub, AlgHom.commutes, ResidueField.algebraMap_eq, ha, sub_self]

/- English proof (translation)
Introduce `O _ _ _ Γ ι _ _ _ _ rbar N A₁ _ _ _ A₂ _ _ _ r₁ r₂ h₁ h₂`. Set `gen : Set (A₁ × A₂)` to `{x | ∃ g a b, x = (r₁.hom g a b, r₂.hom g a b)}`. Set `S : Subalgebra O (A₁ × A₂)` to `Algebra.adjoin O gen`. Set `p₁ : S →ₐ[O] A₁` to `(AlgHom.fst O A₁ A₂).comp S.val`. Set `p₂ : S →ₐ[O] A₂` to `(AlgHom.snd O A₁ A₂).comp S.val`.

Establish `hinj : ∀ x y : S, p₁ x = p₁ y → p₂ x = p₂ y → x = y` using `fun x y e1 e2 => Subtype.ext (Prod.ext e1 e2)`. Establish `hle : S ≤ AlgHom.equalizer ((res O A₁).comp (AlgHom.fst O A₁ A₂)) ((res O A₂).comp (AlgHom.snd O A₁ A₂))`. Apply `Algebra.adjoin_le` to reduce the goal to its premises. Introduce and unpack `x ⟨g, a, b, rfl⟩`. Rewrite using `[SetLike.mem_coe, AlgHom.mem_equalizer]`.

Use `show res O A₁ (r₁.hom g a b) = res O A₂ (r₂.hom g a b)`. Conclude with `(r₁.red g a b).trans (r₂.red g a b).symm`. Establish `hres : ∀ x : S, res O A₁ (p₁ x) = res O A₂ (p₂ x)` using `fun x => (AlgHom.mem_equalizer _ _ _).mp (hle x.2)`. Take `⟨hCO, hpow⟩` from `sub_co O N A₁ A₂ h₁ h₂ S p₁ p₂ hinj hres`. Use `haveI := hCO`.

Set `M : Γ → Matrix ι ι S` to `fun g => Matrix.of fun a b => ⟨(r₁.hom g a b, r₂.hom g a b), Algebra.subset_adjoin ⟨g, a, b, rfl⟩⟩`. Establish `hMv : ∀ g a b, ((M g a b : S) : A₁ × A₂) = (r₁.hom g a b, r₂.hom g a b)` using `fun _ _ _ => rfl`. Set `hom : Γ →* Matrix ι ι S` to `{ toFun := M map_one' := by`. Use `Matrix.ext fun a b => Subtype.ext ?_` and prove the remaining obligations. Rewrite using `[hMv, map_one r₁.hom, map_one r₂.hom]`.

Distinguish the cases in `hab : a = b`. Substitute `hab` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Matrix.one_apply_ne hab]`. Use the proof step `map_mul' := by`.

Introduce `g h`. Use `Matrix.ext fun a b => Subtype.ext ?_` and prove the remaining obligations. Rewrite using `[hMv, map_mul r₁.hom, map_mul r₂.hom, Matrix.mul_apply, Matrix.mul_apply, Matrix.mul_apply]`. Use `show _ = S.val (∑ c, M g a c * M h c b)`. Rewrite using `[map_sum]`.

Simplify using `only [map_mul]`. Express the relevant statement in the definitionally equal form `_ = ∑ c, ((M g a c : A₁ × A₂) * (M h c b : A₁ × A₂))`. Simplify using `only [hMv]`. Apply the tactic sequence `ext <;> simp [Prod.fst_sum, Prod.snd_sum] }`. Establish `hloc : ∀ a b, IsLocallyConstant fun g => M g a b`.

Introduce `a b`. Establish `l1 : IsLocallyConstant fun g => r₁.hom g a b` using `IsLocallyConstant.desc _ _ (r₁.cont a b N) (mk_inj _ h₁)`. Establish `l2 : IsLocallyConstant fun g => r₂.hom g a b` using `IsLocallyConstant.desc _ _ (r₂.cont a b N) (mk_inj _ h₂)`. Conclude with `IsLocallyConstant.desc _ (Subtype.val : S → A₁ × A₂) (l1.prodMk l2) Subtype.val_injective`. Set `r : Lift O rbar S` to `{ hom := hom cont := fun a b n => (hloc a b).comp _ red := fun g a b => by`.

Rewrite using `[← res_map p₁]`. Conclude with `r₁.red g a b }`. Use `⟨S, inferInstance, inferInstance, hCO, r, p₁, p₂, hpow, ?_, ?_, ?_⟩` and prove the remaining obligations. Apply `Subalgebra.map_injective (f := S.val) Subtype.val_injective` to reduce the goal to its premises. Rewrite using `[AlgHom.map_adjoin, Algebra.map_top, Subalgebra.range_val]`.

Use `congr 1`. Use extensionality with `y`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, ⟨g, a, b, rfl⟩, rfl⟩`. Conclude with `⟨g, a, b, rfl⟩`.

Introduce and unpack `⟨g, a, b, rfl⟩`. Conclude with `⟨M g a b, ⟨g, a, b, rfl⟩, rfl⟩`. Conclude with `Lift.ext (MonoidHom.ext fun g => Matrix.ext fun a b => rfl)`. Conclude with `Lift.ext (MonoidHom.ext fun g => Matrix.ext fun a b => rfl)`.
-/
theorem UpperTheory.exists_lift_dominating_pair_of_maximalIdeal_pow_eq_bot :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] [Finite (ResidueField O)] (Γ ι : Type) [Group Γ] [TopologicalSpace Γ] [Fintype ι] [DecidableEq ι] (rbar : Γ →* Matrix ι ι (ResidueField O)) (N : ℕ) (A₁ : Type) [CommRing A₁] [Algebra O A₁] [IsCO O A₁] (A₂ : Type) [CommRing A₂] [Algebra O A₂] [IsCO O A₂] (r₁ : Lift O rbar A₁) (r₂ : Lift O rbar A₂), maximalIdeal A₁ ^ N = ⊥ → maximalIdeal A₂ ^ N = ⊥ →
          ∃ (B : Type) (_ : CommRing B) (_ : Algebra O B) (_ : IsCO O B) (r : Lift O rbar B) (p₁ : B →ₐ[O] A₁) (p₂ : B →ₐ[O] A₂), maximalIdeal B ^ N = ⊥ ∧ Algebra.adjoin O {x : B | ∃ g a b, x = r.hom g a b} = ⊤ ∧ r.map p₁ = r₁ ∧ r.map p₂ = r₂ := by
  intro O _ _ _ Γ ι _ _ _ _ rbar N A₁ _ _ _ A₂ _ _ _ r₁ r₂ h₁ h₂
  classical
  let gen : Set (A₁ × A₂) := {x | ∃ g a b, x = (r₁.hom g a b, r₂.hom g a b)}
  let S : Subalgebra O (A₁ × A₂) := Algebra.adjoin O gen
  let p₁ : S →ₐ[O] A₁ := (AlgHom.fst O A₁ A₂).comp S.val
  let p₂ : S →ₐ[O] A₂ := (AlgHom.snd O A₁ A₂).comp S.val
  have hinj : ∀ x y : S, p₁ x = p₁ y → p₂ x = p₂ y → x = y := fun x y e1 e2 =>
    Subtype.ext (Prod.ext e1 e2)
  have hle : S ≤ AlgHom.equalizer ((res O A₁).comp (AlgHom.fst O A₁ A₂))
      ((res O A₂).comp (AlgHom.snd O A₁ A₂)) := by
    apply Algebra.adjoin_le
    rintro x ⟨g, a, b, rfl⟩
    rw [SetLike.mem_coe, AlgHom.mem_equalizer]
    show res O A₁ (r₁.hom g a b) = res O A₂ (r₂.hom g a b)
    exact (r₁.red g a b).trans (r₂.red g a b).symm
  have hres : ∀ x : S, res O A₁ (p₁ x) = res O A₂ (p₂ x) := fun x =>
    (AlgHom.mem_equalizer _ _ _).mp (hle x.2)
  obtain ⟨hCO, hpow⟩ := sub_co O N A₁ A₂ h₁ h₂ S p₁ p₂ hinj hres
  haveI := hCO
  let M : Γ → Matrix ι ι S := fun g => Matrix.of fun a b =>
    ⟨(r₁.hom g a b, r₂.hom g a b), Algebra.subset_adjoin ⟨g, a, b, rfl⟩⟩
  have hMv : ∀ g a b, ((M g a b : S) : A₁ × A₂) = (r₁.hom g a b, r₂.hom g a b) := fun _ _ _ => rfl
  let hom : Γ →* Matrix ι ι S :=
    { toFun := M
      map_one' := by
        refine Matrix.ext fun a b => Subtype.ext ?_
        rw [hMv, map_one r₁.hom, map_one r₂.hom]
        by_cases hab : a = b
        · subst hab
          simp
        · simp [Matrix.one_apply_ne hab]
      map_mul' := by
        intro g h
        refine Matrix.ext fun a b => Subtype.ext ?_
        rw [hMv, map_mul r₁.hom, map_mul r₂.hom, Matrix.mul_apply, Matrix.mul_apply, Matrix.mul_apply]
        show _ = S.val (∑ c, M g a c * M h c b)
        rw [map_sum]
        simp only [map_mul]
        change _ = ∑ c, ((M g a c : A₁ × A₂) * (M h c b : A₁ × A₂))
        simp only [hMv]
        ext <;> simp [Prod.fst_sum, Prod.snd_sum] }
  have hloc : ∀ a b, IsLocallyConstant fun g => M g a b := by
    intro a b
    have l1 : IsLocallyConstant fun g => r₁.hom g a b :=
      IsLocallyConstant.desc _ _ (r₁.cont a b N) (mk_inj _ h₁)
    have l2 : IsLocallyConstant fun g => r₂.hom g a b :=
      IsLocallyConstant.desc _ _ (r₂.cont a b N) (mk_inj _ h₂)
    exact IsLocallyConstant.desc _ (Subtype.val : S → A₁ × A₂) (l1.prodMk l2) Subtype.val_injective
  let r : Lift O rbar S :=
    { hom := hom
      cont := fun a b n => (hloc a b).comp _
      red := fun g a b => by
        rw [← res_map p₁]
        exact r₁.red g a b }
  refine ⟨S, inferInstance, inferInstance, hCO, r, p₁, p₂, hpow, ?_, ?_, ?_⟩
  · apply Subalgebra.map_injective (f := S.val) Subtype.val_injective
    rw [AlgHom.map_adjoin, Algebra.map_top, Subalgebra.range_val]
    congr 1
    ext y
    constructor
    · rintro ⟨x, ⟨g, a, b, rfl⟩, rfl⟩
      exact ⟨g, a, b, rfl⟩
    · rintro ⟨g, a, b, rfl⟩
      exact ⟨M g a b, ⟨g, a, b, rfl⟩, rfl⟩
  · exact Lift.ext (MonoidHom.ext fun g => Matrix.ext fun a b => rfl)
  · exact Lift.ext (MonoidHom.ext fun g => Matrix.ext fun a b => rfl)
