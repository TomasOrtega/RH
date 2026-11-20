import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PresDefs

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

section
variable {O : Type} [CommRing O] [IsLocalRing O] {R : Type} [CommRing R] [Algebra O R] [IsCO O R]

/- English proof (translation)
Establish `hsurj : Function.Surjective g`. Introduce `y`. Take `⟨a, rfl⟩` from `IsLocalRing.residue_surjective y`. Conclude with `⟨algebraMap O R a, by rw [g.commutes, IsLocalRing.ResidueField.algebraMap_eq]⟩`. Establish `hker : RingHom.ker (g : R →+* ResidueField O) = maximalIdeal R` using `IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective _ hsurj)`.

Take `⟨a, ha⟩` from `IsCO.res_surj (O := O) x`. Establish `h1 : g (x - algebraMap O R a) = 0`. Establish `hm : x - algebraMap O R a ∈ RingHom.ker (g : R →+* ResidueField O)`. Rewrite using `[hker]`. Conclude with `ha`.

Conclude with `(RingHom.mem_ker).1 hm`. Establish `h2 : res O R (x - algebraMap O R a) = 0` using `(res_eq_zero_iff O R _).2 ha`. Rewrite `h1`, `h2` using `[map_sub, sub_eq_zero]`. Rewrite using `[h1, h2, AlgHom.commutes, AlgHom.commutes]`.
-/
private theorem hom_eq_res (g : R →ₐ[O] ResidueField O) (x : R) : g x = res O R x := by
  have hsurj : Function.Surjective g := by
    intro y
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective y
    exact ⟨algebraMap O R a, by rw [g.commutes, IsLocalRing.ResidueField.algebraMap_eq]⟩
  have hker : RingHom.ker (g : R →+* ResidueField O) = maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective _ hsurj)
  obtain ⟨a, ha⟩ := IsCO.res_surj (O := O) x
  have h1 : g (x - algebraMap O R a) = 0 := by
    have hm : x - algebraMap O R a ∈ RingHom.ker (g : R →+* ResidueField O) := by
      rw [hker]
      exact ha
    exact (RingHom.mem_ker).1 hm
  have h2 : res O R (x - algebraMap O R a) = 0 := (res_eq_zero_iff O R _).2 ha
  rw [map_sub, sub_eq_zero] at h1 h2
  rw [h1, h2, AlgHom.commutes, AlgHom.commutes]

/- English proof (translation)
The claim follows from `D.2 f g`.
-/
private theorem tan_mul (D : Tan O R) (f g : R) :
    D.1 (f * g) = res O R f * D.1 g + res O R g * D.1 f := D.2 f g

/- English proof (translation)
Simplify using `using tan_mul D 1 1`.
-/
private theorem tan_one (D : Tan O R) : D.1 1 = 0 := by
  simpa using tan_mul D 1 1

/- English proof (translation)
Rewrite using `[Algebra.algebraMap_eq_smul_one, map_smul, tan_one, smul_zero]`.
-/
private theorem tan_alg (D : Tan O R) (a : O) : D.1 (algebraMap O R a) = 0 := by
  rw [Algebra.algebraMap_eq_smul_one, map_smul, tan_one, smul_zero]

/- English proof (translation)
Take `⟨s, hs⟩` from `(IsNoetherian.noetherian (maximalIdeal R) : (maximalIdeal R).FG)`. Set `φ : Tan O R →ₗ[ResidueField O] (s → ResidueField O)` to `{ toFun := fun D i => D.1 (i : R) map_add' := fun _ _ => rfl map_smul' := fun _ _ => rfl }`. Use `Module.Finite.of_injective φ ((injective_iff_map_eq_zero φ).2 fun D hD => ?_)` and prove the remaining obligations. Establish `h0 : ∀ i ∈ s, D.1 i = 0` using `fun i hi => congrFun hD ⟨i, hi⟩`. Establish `hm : ∀ y ∈ maximalIdeal R, D.1 y = 0`.

Introduce `y hy`. Rewrite `hy` using `[← hs]`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem z hz => exact h0 z hz`. Consider the case `zero => exact map_zero _`.

Consider the case `add a b _ _ ha hb => rw [map_add, ha, hb, add_zero]`. Consider the case `smul c z hz ih`. Establish `hz' : z ∈ maximalIdeal R`. Rewrite using `[← hs]`. Conclude with `hz`.

Rewrite using `[smul_eq_mul, tan_mul, ih, (res_eq_zero_iff O R z).2 hz', mul_zero, zero_mul, add_zero]`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `x`. Take `⟨a, ha⟩` from `IsCO.res_surj (O := O) x`.

Establish `h` using `hm _ ha`. Rewrite `h` using `[map_sub, tan_alg, sub_zero]`. Conclude with `h`.
-/
private theorem tan_finite : Module.Finite (ResidueField O) (Tan O R) := by
  classical
  obtain ⟨s, hs⟩ := (IsNoetherian.noetherian (maximalIdeal R) : (maximalIdeal R).FG)
  let φ : Tan O R →ₗ[ResidueField O] (s → ResidueField O) :=
    { toFun := fun D i => D.1 (i : R)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine Module.Finite.of_injective φ ((injective_iff_map_eq_zero φ).2 fun D hD => ?_)
  have h0 : ∀ i ∈ s, D.1 i = 0 := fun i hi => congrFun hD ⟨i, hi⟩
  have hm : ∀ y ∈ maximalIdeal R, D.1 y = 0 := by
    intro y hy
    rw [← hs] at hy
    induction hy using Submodule.span_induction with
    | mem z hz => exact h0 z hz
    | zero => exact map_zero _
    | add a b _ _ ha hb => rw [map_add, ha, hb, add_zero]
    | smul c z hz ih =>
      have hz' : z ∈ maximalIdeal R := by
        rw [← hs]
        exact hz
      rw [smul_eq_mul, tan_mul, ih, (res_eq_zero_iff O R z).2 hz', mul_zero, zero_mul, add_zero]
  apply Subtype.ext
  apply LinearMap.ext
  intro x
  obtain ⟨a, ha⟩ := IsCO.res_surj (O := O) x
  have h := hm _ ha
  rw [map_sub, tan_alg, sub_zero] at h
  exact h

private noncomputable def tanEquiv : (R →ₐ[O] DualNumber (ResidueField O)) ≃ Tan O R where
  toFun f := ⟨{ toFun := fun x => (f x).snd
                map_add' := fun x y => by simp
                map_smul' := fun a x => by simp }, fun x y => by
    have h : ∀ z, (f z).fst = res O R z := fun z =>
      hom_eq_res ((TrivSqZeroExt.fstHom O (ResidueField O) (ResidueField O)).comp f) z
    show (f (x * y)).snd = res O R x • (f y).snd + res O R y • (f x).snd
    rw [map_mul, DualNumber.snd_mul, h, h, smul_eq_mul, smul_eq_mul, mul_comm (f x).snd]⟩
  invFun D :=
    { toFun := fun x => TrivSqZeroExt.inl (res O R x) + TrivSqZeroExt.inr (D.1 x)
      map_one' := by ext <;> simp [tan_one]
      map_mul' := fun x y => by ext <;> simp [tan_mul, mul_comm]
      map_zero' := by ext <;> simp
      map_add' := fun x y => by ext <;> simp
      commutes' := fun a => by
        ext
        · simp [TrivSqZeroExt.algebraMap_eq_inl']
        · simp [tan_alg, TrivSqZeroExt.algebraMap_eq_inl'] }
  left_inv f := by
    have h : ∀ z, (f z).fst = res O R z := fun z =>
      hom_eq_res ((TrivSqZeroExt.fstHom O (ResidueField O) (ResidueField O)).comp f) z
    refine AlgHom.ext fun x => ?_
    ext <;> simp [h]
  right_inv D := Subtype.ext (LinearMap.ext fun x => by simp)

end

/- English proof (translation)
Introduce `O _ _ R _ _ _`. Conclude with `⟨tan_finite, Nat.card_congr tanEquiv⟩`.
-/
theorem UpperTheory.V.Fr.pr_tan :
    ∀ (O : Type) [CommRing O] [IsLocalRing O], ∀ (R : Type) [CommRing R] [Algebra O R] [IsCO O R], Module.Finite (ResidueField O) (Tan O R) ∧ Nat.card (R →ₐ[O] (DualNumber (ResidueField O))) = Nat.card (Tan O R) := by
  intro O _ _ R _ _ _
  exact ⟨tan_finite, Nat.card_congr tanEquiv⟩
