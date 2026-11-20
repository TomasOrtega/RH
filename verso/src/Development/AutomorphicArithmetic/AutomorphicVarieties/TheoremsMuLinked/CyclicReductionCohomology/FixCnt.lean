import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.DualPair
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.LemmaB
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CardEqPowLength

open IsLocalRing Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV UpperTheory.V.Th GlobalTheory.GalOfCusp

/- English proof (translation)
Take `⟨e, he⟩` from `UpperTheory.V.AlgebraTools.lemma_B f`. Use `⟨e, fun m E' _ _ r T hk hT => ?_⟩` and prove the remaining obligations. Establish `h` using `he m`. Use `set N := (⨅ s, (IsLocalRing.maximalIdeal A ^ m • (⊤ : Submodule A E)).comap (f s)).map (IsLocalRing.maximalIdeal A ^ m • (⊤ : Submodule A E)).mkQ with hN`. Establish `hne : Module.length A N ≠ ⊤` using `ne_top_of_le_ne_top (ENat.coe_ne_top _) h`.

Establish `hfin : Finite N` using `(UpperTheory.V.AlgebraTools.card_eq_pow_length (A := A) (X := N)).1.2 hne`. Establish `hc` using `(UpperTheory.V.AlgebraTools.card_eq_pow_length (A := A) (X := N)).2 hfin`. Establish `hsub : T ⊆ ((IsLocalRing.maximalIdeal A ^ m • (⊤ : Submodule A E)).liftQ r hk.ge) '' (SetLike.coe N)`. Introduce `Y hY`. Take `⟨Z, rfl, hZ⟩` from `hT Y hY`.

Use `⟨_, Submodule.mem_map_of_mem (r := Z) ?_, rfl⟩` and prove the remaining obligations. Rewrite using `[Submodule.mem_iInf]`. Introduce `s`. Rewrite using `[Submodule.mem_comap, ← hk]`. Conclude with `hZ s`.

Establish `hf : (SetLike.coe N).Finite` using `Set.toFinite _`. Use `(Set.ncard_le_ncard hsub (hf.image _)).trans ((Set.ncard_image_le hf).trans ?_)` and prove the remaining obligations. Establish `: (SetLike.coe N).ncard = Nat.card N` using `rfl`. Rewrite using `[this, hc]`. Use `Nat.pow_le_pow_right Nat.card_pos ?_` and prove the remaining obligations.

Rewrite using `[mul_comm]`. Conclude with `ENat.toNat_le_of_le_coe h`.
-/
private theorem fixBd_abs {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Finite (IsLocalRing.ResidueField A)] {E S : Type} [AddCommGroup E] [Module A E] [Module.Finite A E]
    (f : S → E →ₗ[A] E) : ∃ C : ℕ, ∀ (m : ℕ) (E' : Type) [AddCommGroup E'] [Module A E'] (r : E →ₗ[A] E')
      (T : Set E'), LinearMap.ker r = IsLocalRing.maximalIdeal A ^ m • (⊤ : Submodule A E) →
      (∀ Y ∈ T, ∃ Z, r Z = Y ∧ ∀ s, r (f s Z) = 0) →
      T.ncard ≤ Nat.card (IsLocalRing.ResidueField A) ^
        (m * Module.finrank A (⨅ s, LinearMap.ker (f s) : Submodule A E) + C) := by
  obtain ⟨e, he⟩ := UpperTheory.V.AlgebraTools.lemma_B f
  refine ⟨e, fun m E' _ _ r T hk hT => ?_⟩
  have h := he m
  set N := (⨅ s, (IsLocalRing.maximalIdeal A ^ m • (⊤ : Submodule A E)).comap (f s)).map
    (IsLocalRing.maximalIdeal A ^ m • (⊤ : Submodule A E)).mkQ with hN
  have hne : Module.length A N ≠ ⊤ := ne_top_of_le_ne_top (ENat.coe_ne_top _) h
  have hfin : Finite N := (UpperTheory.V.AlgebraTools.card_eq_pow_length (A := A) (X := N)).1.2 hne
  have hc := (UpperTheory.V.AlgebraTools.card_eq_pow_length (A := A) (X := N)).2 hfin
  have hsub : T ⊆ ((IsLocalRing.maximalIdeal A ^ m • (⊤ : Submodule A E)).liftQ r hk.ge) '' (SetLike.coe N) := by
    intro Y hY
    obtain ⟨Z, rfl, hZ⟩ := hT Y hY
    refine ⟨_, Submodule.mem_map_of_mem (r := Z) ?_, rfl⟩
    rw [Submodule.mem_iInf]
    intro s
    rw [Submodule.mem_comap, ← hk]
    exact hZ s
  have hf : (SetLike.coe N).Finite := Set.toFinite _
  refine (Set.ncard_le_ncard hsub (hf.image _)).trans ((Set.ncard_image_le hf).trans ?_)
  have : (SetLike.coe N).ncard = Nat.card N := rfl
  rw [this, hc]
  refine Nat.pow_le_pow_right Nat.card_pos ?_
  rw [mul_comm]
  exact ENat.toNat_le_of_le_coe h

/- English proof (translation)
Introduce `l _ O _ _ _ hO _ n S Φ`. Take `⟨-, hfin, -⟩` from `hO`. Take `⟨C, hC⟩` from `fixBd_abs Φ`. Use `⟨C, fun m => hC m (Mm O n m) (Ideal.Quotient.mkₐ O (maximalIdeal O ^ m)).toLinearMap.mapMatrix _ ?_ fun Y hY => hY⟩` and prove the remaining obligations. Use extensionality with `Z`.

Rewrite using `[LinearMap.mem_ker]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Rewrite using `[Matrix.matrix_eq_sum_single Z]`. Use `Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => ?_` and prove the remaining obligations.

Establish `h1 : Z i j ∈ maximalIdeal O ^ m` using `Ideal.Quotient.eq_zero_iff_mem.1 (congrFun (congrFun h i) j)`. Establish `e : Matrix.single i j (Z i j) = Z i j • Matrix.single i j (1 : O)` using `by simp`. Rewrite using `[e]`. Conclude with `Submodule.smul_mem_smul h1 Submodule.mem_top`. Introduce `h`.

Use `Submodule.smul_induction_on h (fun a ha Y _ => ?_) fun a b ha hb => by rw [map_add, ha, hb, add_zero]` and prove the remaining obligations. Use extensionality with `i j`. Conclude with `Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mul_mem_right _ _ ha)`.
-/
theorem UpperTheory.V.Th.fixCnt :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (n : ℕ) (S : Type) (Φ : S → Matrix (Fin n) (Fin n) O →ₗ[O] Matrix (Fin n) (Fin n) O), ∃ C : ℕ, ∀ m, {Y : Mm O n m | ∃ Y', red m Y' = Y ∧ ∀ s, red m (Φ s Y') = 0}.ncard ≤ Nat.card (ResidueField O) ^ (m * Module.finrank O (⨅ s, LinearMap.ker (Φ s) : Submodule O (Matrix (Fin n) (Fin n) O)) + C) := by
  intro l _ O _ _ _ hO _ n S Φ
  obtain ⟨-, hfin, -⟩ := hO
  obtain ⟨C, hC⟩ := fixBd_abs Φ
  refine ⟨C, fun m => hC m (Mm O n m) (Ideal.Quotient.mkₐ O (maximalIdeal O ^ m)).toLinearMap.mapMatrix _ ?_ fun Y hY => hY⟩
  ext Z
  rw [LinearMap.mem_ker]
  constructor
  · intro h
    rw [Matrix.matrix_eq_sum_single Z]
    refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => ?_
    have h1 : Z i j ∈ maximalIdeal O ^ m := Ideal.Quotient.eq_zero_iff_mem.1 (congrFun (congrFun h i) j)
    have e : Matrix.single i j (Z i j) = Z i j • Matrix.single i j (1 : O) := by simp
    rw [e]
    exact Submodule.smul_mem_smul h1 Submodule.mem_top
  · intro h
    refine Submodule.smul_induction_on h (fun a ha Y _ => ?_) fun a b ha hb => by rw [map_add, ha, hb, add_zero]
    ext i j
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mul_mem_right _ _ ha)
