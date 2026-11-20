import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisCochains.GLinkQuot

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module UpperTheory.V UpperTheory.V.Fr UpperTheory.V.GC

private noncomputable def subquotEquiv {R R' X : Type*} [CommRing R] [CommRing R'] [AddCommGroup X]
    [Module R X] [Module R' X] (Z B : Submodule R X) (Z' B' : Submodule R' X)
    (hZ : ∀ x, x ∈ Z ↔ x ∈ Z') (hB : ∀ x, x ∈ B ↔ x ∈ B') :
    (Z ⧸ B.comap Z.subtype) ≃ (Z' ⧸ B'.comap Z'.subtype) :=
  Quotient.congr (Equiv.subtypeEquivRight hZ) fun a b => by
    rw [Submodule.quotientRel_def, Submodule.quotientRel_def]
    exact hB _

/- English proof (translation)
Introduce `hF hE F Ω _ _ _ _ _ l _ hl hR S hS k _ _ _ M _ _ _ _ _ ρ hρ c hc`. Use `haveI : Finite M := Module.finite_of_finite k`. Use `haveI : CharP k (l ^ 1) := by rw [pow_one]; infer_instance`. Use `letI : Module (ZMod (l ^ 1)) M := Module.compHom _ (ZMod.castHom (dvd_refl _) k)`. Set `ρ' : Representation (ZMod (l ^ 1)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M` to `{ toFun := fun g => { toFun := ρ g map_add' := map_add (ρ g) map_smul' := fun c m => map_smul (ρ g) (ZMod.castHom (dvd_refl _) k c) m } map_one' := LinearMap.ext fun m => show ρ 1 m = m by rw [map_one]; rfl map_mul' := fun g h => LinearMap.ext fun m => show ρ (g * h) m = ρ g (ρ h …`.

Rewrite using `[map_mul]`. Use `rfl }`. Establish `e0 : H0 ρ ≃ H0 ρ'` using `Equiv.subtypeEquivRight fun _ => Iff.rfl`. Establish `e1 : H1 ρ ≃ H1 ρ'` using `subquotEquiv _ _ _ _ (fun _ => Iff.rfl) (fun _ => Iff.rfl)`. Establish `e2 : H2 ρ ≃ H2 ρ'` using `subquotEquiv _ _ _ _ (fun _ => Iff.rfl) (fun _ => Iff.rfl)`.

Establish `ec : ∀ w, Nat.card {m : M // ρ' (toGS Ω _ (c w)) m = m} = Nat.card k ^ finrank k (LinearMap.ker (ρ (toGS Ω _ (c w)) - 1))` using `fun w => by`. Rewrite using `[← Module.natCard_eq_pow_finrank]`. Use `Nat.card_congr (Equiv.subtypeEquivRight fun m => ?_)` and prove the remaining obligations. Rewrite using `[LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]`. Conclude with `Iff.rfl`.

Take `⟨-, f1, f2, -⟩` from `hF F Ω l 1 M S ρ' one_pos hS hρ`. Establish `h` using `hE F Ω l 1 M S ρ' one_pos hS hρ c fun w _ => hc w`. Establish `hr : ∀ w : InfinitePlace F, w.IsReal` using `fun w => IsTotallyReal.isReal w`. Rewrite `h` using `[archH0Card, IsTotallyReal.nrComplexPlaces_eq_zero, pow_zero, mul_one, Finset.filter_true_of_mem fun w _ => hr w, Finset.prod_congr rfl fun w _ => ec w, Finset.prod_pow_eq_pow_sum]`. Use `haveI : Finite (H1 ρ) := Finite.of_equiv _ e1.symm`.

Use `haveI : Finite (H2 ρ) := Finite.of_equiv _ e2.symm`. Use `haveI : Module.Finite k (H1 ρ) := Module.Finite.of_finite`. Use `haveI : Module.Finite k (H2 ρ) := Module.Finite.of_finite`. Establish `hk : 1 < Nat.card k` using `Finite.one_lt_card`. Use `⟨inferInstance, inferInstance, ?_⟩` and prove the remaining obligations.

Apply `Nat.pow_right_injective hk` to reduce the goal to its premises. Use `beta_reduce`. Rewrite using `[pow_add, pow_add, pow_add, mul_comm (finrank ℚ F), pow_mul, ← Module.natCard_eq_pow_finrank (V := H1 ρ), ← Module.natCard_eq_pow_finrank (V := H0 ρ), ← Module.natCard_eq_pow_finrank (V := H2 ρ), ← Module.natCard_eq_pow_finrank (V := M), Nat.card_congr e0, Nat.card_congr e1, Nat. …`. Conclude with `h.symm`.
-/
theorem UpperTheory.V.GC.globEuler :
    GlobalFiniteness → GlobalEulerChar → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime], l ≠ 2 → IsTotallyReal F → ∀ (S : Finset (HeightOneSpectrum (𝓞 F))), ContainsAbove S l → ∀ (k : Type) [Field k] [Finite k] [CharP k l] (M : Type) [AddCommGroup M] [Module k M] [Module.Finite k M] [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation k (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M), ContAction ρ →
    ∀ c : InfinitePlace F → G F Ω, (∀ w, IsCCAt w (c w)) → Module.Finite k (H1 ρ) ∧ Module.Finite k (H2 ρ) ∧
    finrank k (H1 ρ) + ∑ w, finrank k (LinearMap.ker (ρ (toGS Ω _ (c w)) - 1)) = finrank k (H0 ρ) + finrank k (H2 ρ) + finrank ℚ F * finrank k M := by
  classical
  intro hF hE F Ω _ _ _ _ _ l _ hl hR S hS k _ _ _ M _ _ _ _ _ ρ hρ c hc
  haveI : Finite M := Module.finite_of_finite k
  haveI : CharP k (l ^ 1) := by rw [pow_one]; infer_instance
  letI : Module (ZMod (l ^ 1)) M := Module.compHom _ (ZMod.castHom (dvd_refl _) k)
  let ρ' : Representation (ZMod (l ^ 1)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M :=
    { toFun := fun g =>
        { toFun := ρ g
          map_add' := map_add (ρ g)
          map_smul' := fun c m => map_smul (ρ g) (ZMod.castHom (dvd_refl _) k c) m }
      map_one' := LinearMap.ext fun m => show ρ 1 m = m by rw [map_one]; rfl
      map_mul' := fun g h => LinearMap.ext fun m => show ρ (g * h) m = ρ g (ρ h m) by
        rw [map_mul]; rfl }
  have e0 : H0 ρ ≃ H0 ρ' := Equiv.subtypeEquivRight fun _ => Iff.rfl
  have e1 : H1 ρ ≃ H1 ρ' := subquotEquiv _ _ _ _ (fun _ => Iff.rfl) (fun _ => Iff.rfl)
  have e2 : H2 ρ ≃ H2 ρ' := subquotEquiv _ _ _ _ (fun _ => Iff.rfl) (fun _ => Iff.rfl)
  have ec : ∀ w, Nat.card {m : M // ρ' (toGS Ω _ (c w)) m = m} =
      Nat.card k ^ finrank k (LinearMap.ker (ρ (toGS Ω _ (c w)) - 1)) := fun w => by
    rw [← Module.natCard_eq_pow_finrank]
    refine Nat.card_congr (Equiv.subtypeEquivRight fun m => ?_)
    rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
    exact Iff.rfl
  obtain ⟨-, f1, f2, -⟩ := hF F Ω l 1 M S ρ' one_pos hS hρ
  have h := hE F Ω l 1 M S ρ' one_pos hS hρ c fun w _ => hc w
  have hr : ∀ w : InfinitePlace F, w.IsReal := fun w => IsTotallyReal.isReal w
  rw [archH0Card, IsTotallyReal.nrComplexPlaces_eq_zero, pow_zero, mul_one,
    Finset.filter_true_of_mem fun w _ => hr w, Finset.prod_congr rfl fun w _ => ec w,
    Finset.prod_pow_eq_pow_sum] at h
  haveI : Finite (H1 ρ) := Finite.of_equiv _ e1.symm
  haveI : Finite (H2 ρ) := Finite.of_equiv _ e2.symm
  haveI : Module.Finite k (H1 ρ) := Module.Finite.of_finite
  haveI : Module.Finite k (H2 ρ) := Module.Finite.of_finite
  have hk : 1 < Nat.card k := Finite.one_lt_card
  refine ⟨inferInstance, inferInstance, ?_⟩
  apply Nat.pow_right_injective hk
  beta_reduce
  rw [pow_add, pow_add, pow_add, mul_comm (finrank ℚ F), pow_mul, ← Module.natCard_eq_pow_finrank (V := H1 ρ),
    ← Module.natCard_eq_pow_finrank (V := H0 ρ), ← Module.natCard_eq_pow_finrank (V := H2 ρ),
    ← Module.natCard_eq_pow_finrank (V := M),
    Nat.card_congr e0, Nat.card_congr e1, Nat.card_congr e2]
  exact h.symm
