import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.KatoUse
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.BoxDefs

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Matrix IsLocalRing
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.U3

section Transport

variable {R R' Γ Γ' M : Type} [CommRing R] [CommRing R'] [Group Γ] [TopologicalSpace Γ] [Group Γ']
  [TopologicalSpace Γ'] [AddCommGroup M] [Module R M] [Module R' M] [TopologicalSpace M] [DiscreteTopology M]
  (ρ : Representation R Γ M) (ρ' : Representation R' Γ' M) (e : Γ' ≃* Γ) (he : Continuous e)
  (he' : Continuous e.symm) (h : ∀ g m, ρ' g m = ρ (e g) m)

include h in
/- English proof (translation)
Use `⟨Equiv.subtypeEquivRight fun m => ?_⟩` and prove the remaining obligations. Rewrite using `[mem_riemannRochSpace_iff_regularAt_everywhere, mem_riemannRochSpace_iff_regularAt_everywhere]`. Prove the components needed by the constructor for the conclusion. Introduce `H g`. Rewrite using `[h]`.

Conclude with `H _`. Introduce `H g`. Use `H (e.symm g)` as an intermediate fact. Rewrite `this` using `[h, e.apply_symm_apply]`. Then use the resulting hypothesis.
-/
private theorem invariants_equiv : Nonempty (H0 ρ ≃ H0 ρ') := by
  refine ⟨Equiv.subtypeEquivRight fun m => ?_⟩
  rw [mem_riemannRochSpace_iff_regularAt_everywhere, mem_riemannRochSpace_iff_regularAt_everywhere]
  constructor
  · intro H g
    rw [h]
    exact H _
  · intro H g
    have := H (e.symm g)
    rwa [h, e.apply_symm_apply] at this

include he he' h in
/- English proof (translation)
Establish `key : ∀ f : Γ → M, f ∈ Z1 ρ ↔ (fun g => f (e g)) ∈ Z1 ρ'`. Introduce `f`. Use `show (Continuous f ∧ _) ↔ (Continuous _ ∧ _)`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hc, hf⟩`.

Use `⟨hc.comp he, fun a b => ?_⟩` and prove the remaining obligations. Simplify using `only [map_mul, h]`. Conclude with `hf _ _`. Introduce and unpack `⟨hc, hf⟩`. Use `⟨?_, fun a b => ?_⟩` and prove the remaining obligations.

Use `hc.comp he'` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `x`. Simplify using the standard rewrite rules. Use `hf (e.symm a) (e.symm b)` as an intermediate fact.

Simplify `this` using `[map_mul, h]`. Establish `keyB : ∀ f : Γ → M, f ∈ B1 ρ ↔ (fun g => f (e g)) ∈ B1 ρ'`. Introduce `f`. Rewrite using `[mem_coboundaries1, mem_coboundaries1]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨m, hm⟩`. Conclude with `⟨m, fun g => by simp [hm, h]⟩`. Introduce and unpack `⟨m, hm⟩`. Use `⟨m, fun g => ?_⟩` and prove the remaining obligations. Use `hm (e.symm g)` as an intermediate fact.

Simplify `this` using `[h]`. Set `φ : Z1 ρ ≃ Z1 ρ'` to `{ toFun := fun f => ⟨fun g => f.1 (e g), (key f.1).1 f.2⟩ invFun := fun f => ⟨fun g => f.1 (e.symm g), (key _).2 (by`. Rewrite using `[show (fun g => f.1 (e.symm (e g))) = f.1 from funext fun g => by simp]`. Conclude with `f.2)⟩`. Use `left_inv := fun f => Subtype.ext (funext fun g => by simp)`.

Use `right_inv := fun f => Subtype.ext (funext fun g => by simp) }`. Use `⟨Quotient.congr φ fun a b => ?_⟩` and prove the remaining obligations. Rewrite using `[Submodule.quotientRel_def, Submodule.quotientRel_def, Submodule.mem_comap, Submodule.mem_comap]`. Conclude with `keyB _`.
-/
private theorem first_cohomology_equiv : Nonempty (H1 ρ ≃ H1 ρ') := by
  have key : ∀ f : Γ → M, f ∈ Z1 ρ ↔ (fun g => f (e g)) ∈ Z1 ρ' := by
    intro f
    show (Continuous f ∧ _) ↔ (Continuous _ ∧ _)
    constructor
    · rintro ⟨hc, hf⟩
      refine ⟨hc.comp he, fun a b => ?_⟩
      simp only [map_mul, h]
      exact hf _ _
    · rintro ⟨hc, hf⟩
      refine ⟨?_, fun a b => ?_⟩
      · have := hc.comp he'
        convert this using 1
        funext x
        simp
      · have := hf (e.symm a) (e.symm b)
        simpa [map_mul, h] using this
  have keyB : ∀ f : Γ → M, f ∈ B1 ρ ↔ (fun g => f (e g)) ∈ B1 ρ' := by
    intro f
    rw [mem_coboundaries1, mem_coboundaries1]
    constructor
    · rintro ⟨m, hm⟩
      exact ⟨m, fun g => by simp [hm, h]⟩
    · rintro ⟨m, hm⟩
      refine ⟨m, fun g => ?_⟩
      have := hm (e.symm g)
      simpa [h] using this
  let φ : Z1 ρ ≃ Z1 ρ' :=
    { toFun := fun f => ⟨fun g => f.1 (e g), (key f.1).1 f.2⟩
      invFun := fun f => ⟨fun g => f.1 (e.symm g), (key _).2 (by
        rw [show (fun g => f.1 (e.symm (e g))) = f.1 from funext fun g => by simp]
        exact f.2)⟩
      left_inv := fun f => Subtype.ext (funext fun g => by simp)
      right_inv := fun f => Subtype.ext (funext fun g => by simp) }
  refine ⟨Quotient.congr φ fun a b => ?_⟩
  rw [Submodule.quotientRel_def, Submodule.quotientRel_def, Submodule.mem_comap, Submodule.mem_comap]
  exact keyB _

include he he' h in
/- English proof (translation)
Establish `key : ∀ f : Γ × Γ → M, f ∈ Z2 ρ ↔ (fun p => f (e p.1, e p.2)) ∈ Z2 ρ'`. Introduce `f`. Use `show (Continuous f ∧ _) ↔ (Continuous _ ∧ _)`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hc, hf⟩`.

Use `⟨hc.comp (he.prodMap he), fun a b c => ?_⟩` and prove the remaining obligations. Simplify using `only [map_mul, h]`. Conclude with `hf _ _ _`. Introduce and unpack `⟨hc, hf⟩`. Use `⟨?_, fun a b c => ?_⟩` and prove the remaining obligations.

Use `hc.comp (he'.prodMap he')` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `x`. Simplify using the standard rewrite rules. Use `hf (e.symm a) (e.symm b) (e.symm c)` as an intermediate fact.

Simplify `this` using `[map_mul, h]`. Establish `keyB : ∀ f : Γ × Γ → M, f ∈ B2 ρ ↔ (fun p => f (e p.1, e p.2)) ∈ B2 ρ'`. Introduce `f`. Rewrite using `[separated_dvr_second_cohomology_mem, separated_dvr_second_cohomology_mem]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨c, hc, rfl⟩`. Use `⟨fun g => c (e g), hc.comp he, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `⟨a, b⟩`. Simplify using `[d1_apply, h, map_mul]`. Introduce and unpack `⟨c, hc, hcf⟩`.

Use `⟨fun g => c (e.symm g), hc.comp he', ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `⟨a, b⟩`. Use `congrFun hcf (e.symm a, e.symm b)` as an intermediate fact. Rewrite `this` using `[d1_apply]`. Rewrite using `[d1_apply]`.

Simplify `this` using `[h, map_mul]`. Set `φ : Z2 ρ ≃ Z2 ρ'` to `{ toFun := fun f => ⟨fun p => f.1 (e p.1, e p.2), (key f.1).1 f.2⟩ invFun := fun f => ⟨fun p => f.1 (e.symm p.1, e.symm p.2), (key _).2 (by`. Rewrite using `[show (fun p : Γ' × Γ' => f.1 (e.symm (e p.1), e.symm (e p.2))) = f.1 from`. Use function extensionality and compare the values at `fun p => by simp]`. Conclude with `f.2)⟩`.

Use `left_inv := fun f => Subtype.ext (funext fun p => by simp)`. Use `right_inv := fun f => Subtype.ext (funext fun p => by simp) }`. Use `⟨Quotient.congr φ fun a b => ?_⟩` and prove the remaining obligations. Rewrite using `[Submodule.quotientRel_def, Submodule.quotientRel_def, Submodule.mem_comap, Submodule.mem_comap]`. Conclude with `keyB _`.
-/
private theorem second_cohomology_equiv : Nonempty (H2 ρ ≃ H2 ρ') := by
  have key : ∀ f : Γ × Γ → M, f ∈ Z2 ρ ↔ (fun p => f (e p.1, e p.2)) ∈ Z2 ρ' := by
    intro f
    show (Continuous f ∧ _) ↔ (Continuous _ ∧ _)
    constructor
    · rintro ⟨hc, hf⟩
      refine ⟨hc.comp (he.prodMap he), fun a b c => ?_⟩
      simp only [map_mul, h]
      exact hf _ _ _
    · rintro ⟨hc, hf⟩
      refine ⟨?_, fun a b c => ?_⟩
      · have := hc.comp (he'.prodMap he')
        convert this using 1
        funext x
        simp
      · have := hf (e.symm a) (e.symm b) (e.symm c)
        simpa [map_mul, h] using this
  have keyB : ∀ f : Γ × Γ → M, f ∈ B2 ρ ↔ (fun p => f (e p.1, e p.2)) ∈ B2 ρ' := by
    intro f
    rw [separated_dvr_second_cohomology_mem, separated_dvr_second_cohomology_mem]
    constructor
    · rintro ⟨c, hc, rfl⟩
      refine ⟨fun g => c (e g), hc.comp he, ?_⟩
      funext ⟨a, b⟩
      simp [d1_apply, h, map_mul]
    · rintro ⟨c, hc, hcf⟩
      refine ⟨fun g => c (e.symm g), hc.comp he', ?_⟩
      funext ⟨a, b⟩
      have := congrFun hcf (e.symm a, e.symm b)
      rw [d1_apply] at this
      rw [d1_apply]
      simpa [h, map_mul] using this
  let φ : Z2 ρ ≃ Z2 ρ' :=
    { toFun := fun f => ⟨fun p => f.1 (e p.1, e p.2), (key f.1).1 f.2⟩
      invFun := fun f => ⟨fun p => f.1 (e.symm p.1, e.symm p.2), (key _).2 (by
        rw [show (fun p : Γ' × Γ' => f.1 (e.symm (e p.1), e.symm (e p.2))) = f.1 from
          funext fun p => by simp]
        exact f.2)⟩
      left_inv := fun f => Subtype.ext (funext fun p => by simp)
      right_inv := fun f => Subtype.ext (funext fun p => by simp) }
  refine ⟨Quotient.congr φ fun a b => ?_⟩
  rw [Submodule.quotientRel_def, Submodule.quotientRel_def, Submodule.mem_comap, Submodule.mem_comap]
  exact keyB _

end Transport

private def resC (R : Type) {k Γ M : Type} [CommRing R] [CommRing k] [Algebra R k] [Group Γ] [AddCommGroup M]
    [Module R M] [Module k M] [IsScalarTower R k M] (ρ : Representation k Γ M) : Representation R Γ M where
  toFun g := (ρ g).restrictScalars R
  map_one' := by ext; simp
  map_mul' g h := by ext; simp

/- English proof (translation)
Introduce `hfin hec Ω _ _ _ l _ k M _ _ _ _ _ _ _ _ _ _ A v hv hl ρ hc`. Use `haveI : Finite M := Module.finite_of_finite k`. Use `haveI : CharP k (l ^ 1) := by rw [pow_one]; infer_instance`. Use `letI : Algebra (ZMod (l ^ 1)) k := ZMod.algebra k (l ^ 1)`. Use `letI : Module (ZMod (l ^ 1)) M := Module.compHom M (algebraMap (ZMod (l ^ 1)) k)`.

Use `haveI : IsScalarTower (ZMod (l ^ 1)) k M := ⟨fun a b m => by rw [Algebra.smul_def, mul_smul]; rfl⟩`. Set `ρ₀` to `resC (ZMod (l ^ 1)) ρ`. Establish `hc₀ : ContAction ρ₀` using `hc`. Take `⟨-, hF1, hF2, -⟩` from `hfin ℚ Ω l 1 M A ρ₀ v one_pos hv hc₀`. Establish `hE` using `(hec ℚ Ω l 1 M A ρ₀ v one_pos hv hc₀).2 hl`.

Establish `hr : ∀ g m, ρ g m = ρ₀ (MulEquiv.refl _ g) m` using `fun _ _ => rfl`. Take `⟨e0⟩` from `invariants_equiv ρ₀ ρ (MulEquiv.refl _) hr`. Take `⟨e1⟩` from `first_cohomology_equiv ρ₀ ρ (MulEquiv.refl _) continuous_id continuous_id hr`. Take `⟨e2⟩` from `second_cohomology_equiv ρ₀ ρ (MulEquiv.refl _) continuous_id continuous_id hr`. Use `haveI : Finite (H1 ρ) := Finite.of_equiv _ e1`.

Use `haveI : Finite (H2 ρ) := Finite.of_equiv _ e2`. Use `⟨Module.Finite.of_finite, Module.Finite.of_finite, ?_⟩` and prove the remaining obligations. Establish `hcard : Nat.card (H1 ρ) = Nat.card (H0 ρ) * Nat.card (H2 ρ)`. Rewrite using `[← Nat.card_congr e1, ← Nat.card_congr e0, ← Nat.card_congr e2]`. Conclude with `hE`.

Establish `pw : ∀ (V : Type) [AddCommGroup V] [Module k V] [Finite V], Nat.card V = Nat.card k ^ Module.finrank k V`. Introduce `V _ _ _`. Use `haveI := Fintype.ofFinite V`. Use `haveI := Fintype.ofFinite k`. Rewrite using `[Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]`.

Conclude with `Module.card_eq_pow_finrank`. Rewrite `hcard` using `[pw (H1 ρ), pw (H0 ρ), pw (H2 ρ), ← pow_add]`. Conclude with `Nat.pow_right_injective Finite.one_lt_card hcard`.
-/
theorem UpperTheory.local_euler_characteristic_of_prime_not_mem :
    LocalFiniteness → LocalEulerChar → ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (k M : Type) [Field k] [Finite k] [CharP k l] [AddCommGroup M] [Module k M] [Module.Finite k M] [TopologicalSpace M] [DiscreteTopology M] [IsTopologicalAddGroup M] [ContinuousConstSMul k M] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 ℚ)), IsPlaceOver A v → ((l : ℕ) : 𝓞 ℚ) ∉ v.asIdeal →
          ∀ ρ : Representation k (Dec (F := ℚ) A) M, ContAction ρ →
          Module.Finite k (H1 ρ) ∧ Module.Finite k (H2 ρ) ∧ Module.finrank k (H1 ρ) = Module.finrank k (H0 ρ) + Module.finrank k (H2 ρ) := by
  intro hfin hec Ω _ _ _ l _ k M _ _ _ _ _ _ _ _ _ _ A v hv hl ρ hc
  haveI : Finite M := Module.finite_of_finite k
  haveI : CharP k (l ^ 1) := by rw [pow_one]; infer_instance
  letI : Algebra (ZMod (l ^ 1)) k := ZMod.algebra k (l ^ 1)
  letI : Module (ZMod (l ^ 1)) M := Module.compHom M (algebraMap (ZMod (l ^ 1)) k)
  haveI : IsScalarTower (ZMod (l ^ 1)) k M := ⟨fun a b m => by rw [Algebra.smul_def, mul_smul]; rfl⟩
  let ρ₀ := resC (ZMod (l ^ 1)) ρ
  have hc₀ : ContAction ρ₀ := hc
  obtain ⟨-, hF1, hF2, -⟩ := hfin ℚ Ω l 1 M A ρ₀ v one_pos hv hc₀
  have hE := (hec ℚ Ω l 1 M A ρ₀ v one_pos hv hc₀).2 hl
  have hr : ∀ g m, ρ g m = ρ₀ (MulEquiv.refl _ g) m := fun _ _ => rfl
  obtain ⟨e0⟩ := invariants_equiv ρ₀ ρ (MulEquiv.refl _) hr
  obtain ⟨e1⟩ := first_cohomology_equiv ρ₀ ρ (MulEquiv.refl _) continuous_id continuous_id hr
  obtain ⟨e2⟩ := second_cohomology_equiv ρ₀ ρ (MulEquiv.refl _) continuous_id continuous_id hr
  haveI : Finite (H1 ρ) := Finite.of_equiv _ e1
  haveI : Finite (H2 ρ) := Finite.of_equiv _ e2
  refine ⟨Module.Finite.of_finite, Module.Finite.of_finite, ?_⟩
  have hcard : Nat.card (H1 ρ) = Nat.card (H0 ρ) * Nat.card (H2 ρ) := by
    rw [← Nat.card_congr e1, ← Nat.card_congr e0, ← Nat.card_congr e2]
    exact hE
  have pw : ∀ (V : Type) [AddCommGroup V] [Module k V] [Finite V],
      Nat.card V = Nat.card k ^ Module.finrank k V := by
    intro V _ _ _
    haveI := Fintype.ofFinite V
    haveI := Fintype.ofFinite k
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    exact Module.card_eq_pow_finrank
  rw [pw (H1 ρ), pw (H0 ρ), pw (H2 ρ), ← pow_add] at hcard
  exact Nat.pow_right_injective Finite.one_lt_card hcard
