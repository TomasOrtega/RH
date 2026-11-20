import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ConjugateOrderData
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical

noncomputable section

namespace GlobalTheory.EigenLattice

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {c : Ideal (OF E)}
variable {O : Type} [CommRing O] {K : Type} [Field K] [Algebra O K]
variable {H : Type} [AddCommGroup H] [Module O H]

def tensAct (ρ : orderC c →+* Module.End O H) : orderC c ⊗[ℤ] O →ₗ[ℤ] Module.End O H :=
  TensorProduct.lift (LinearMap.mk₂ ℤ (fun (a : orderC c) (x : O) => x • ρ a)
    (fun a b x => by simp [map_add, smul_add])
    (fun n a x => by rw [map_zsmul, smul_comm])
    (fun a x y => by simp [add_smul])
    (fun n a x => smul_assoc n x (ρ a)))

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem tensAct_tmul (ρ : orderC c →+* Module.End O H) (a : orderC c) (x : O) :
    tensAct ρ (a ⊗ₜ x) = x • ρ a := by
  rfl

/- English proof (translation)
Establish `hv' : ∀ a : orderC c, (ρ a).baseChange K v = σ a • v` using `fun a => Module.End.mem_eigenspace_iff.1 ((Submodule.mem_iInf _).1 hv a)`. Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a x`. Rewrite using `[tensAct_tmul, LinearMap.baseChange_smul, LinearMap.smul_apply, hv' a]`.

Use `show x • ((σ a : K) • v) = (σ a * algebraMap O K x) • v`. Rewrite using `[mul_smul, algebraMap_smul, smul_comm]`. Consider the case `add t₁ t₂ h₁ h₂`. Rewrite using `[map_add, LinearMap.baseChange_add, LinearMap.add_apply, h₁, h₂, map_add, add_smul]`.
-/
theorem tensAct_eig (ρ : orderC c →+* Module.End O H) (σ : E →+* K) (v : K ⊗[O] H)
    (hv : v ∈ eigK ρ σ) (t : orderC c ⊗[ℤ] O) :
    ((tensAct ρ t).baseChange K) v = coordAt O c σ t • v := by
  have hv' : ∀ a : orderC c, (ρ a).baseChange K v = σ a • v := fun a =>
    Module.End.mem_eigenspace_iff.1 ((Submodule.mem_iInf _).1 hv a)
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    rw [tensAct_tmul, LinearMap.baseChange_smul, LinearMap.smul_apply, hv' a]
    show x • ((σ a : K) • v) = (σ a * algebraMap O K x) • v
    rw [mul_smul, algebraMap_smul, smul_comm]
  | add t₁ t₂ h₁ h₂ =>
    rw [map_add, LinearMap.baseChange_add, LinearMap.add_apply, h₁, h₂, map_add, add_smul]

/- English proof (translation)
Simplify using `[inK, LinearMap.baseChange_tmul]`.
-/
theorem inK_apply_map (f : Module.End O H) (h : H) :
    inK (O := O) K H (f h) = (f.baseChange K) (inK K H h) := by
  simp [inK, LinearMap.baseChange_tmul]

/- English proof (translation)
Introduce `E _ _ _ c _ l _ O _ _ _ _ K _ _ _ _ hcard D _ hclr I _ φ _ H _ _ ρ Fil B hlat hint`. Establish `hfree : Module.Free O H` using `hlat.1`. Establish `hinj : Function.Injective (inK (O` using `O) K H) := by`. Establish `h1` using `Module.Flat.rTensor_preserves_injective_linearMap (M := H) (Algebra.linearMap O K) (IsFractionRing.injective O K)`. Establish `: inK (O` using `O) K H = (LinearMap.rTensor H (Algebra.linearMap O K)) ∘ₗ (TensorProduct.lid O H).symm.toLinearMap := by`.

Use extensionality with `h`. Simplify using `[inK]`. Rewrite using `[this]`. Conclude with `h1.comp (TensorProduct.lid O H).symm.injective`. Establish `hindK` using `hint.submodule_iSupIndep`.

Establish `htop : ∀ v : K ⊗[O] H, v ∈ ⨆ σ, eigK ρ σ` using `fun v => by`. Rewrite using `[hint.submodule_iSup_eq_top]`. Discharge the goal by the elementary cases of `trivial`. Prove the components needed by the constructor for the conclusion. Introduce `σ`.

Rewrite using `[Submodule.disjoint_def]`. Introduce `x hx1 hx2`. Establish `hle : (⨆ j, ⨆ (_ : j ≠ σ), eigLat ρ j) ≤ ((⨆ j, ⨆ (_ : j ≠ σ), eigK ρ j).restrictScalars O).comap (inK K H)`. Use `iSup₂_le fun j hj y hy => ?_` and prove the remaining obligations. Conclude with `(le_iSup₂ (f := fun j (_ : j ≠ σ) => eigK ρ j) j hj) hy`.

Establish `h0` using `(Submodule.disjoint_def.1 (hindK σ)) _ hx1 (hle hx2)`. Conclude with `hinj (by rw [h0, map_zero])`. Establish `hfin : Finite (E →+* K)` using `Nat.finite_of_card_ne_zero (by rw [hcard]; exact Module.finrank_pos.ne')`. Use `letI := Fintype.ofFinite (E →+* K)`. Use `choose t ht using hclr`.

Establish `hA : ∀ (σ σ' : E →+* K) v, v ∈ eigK ρ σ' → ((tensAct ρ (t σ)).baseChange K) v = if σ' = σ then algebraMap O K D • v else 0`. Introduce `σ σ' v hv`. Rewrite using `[tensAct_eig ρ σ' v hv, ht σ σ']`. Apply the tactic sequence `split_ifs <;> simp`. Establish `hsum : ∀ v : K ⊗[O] H, ∑ σ, ((tensAct ρ (t σ)).baseChange K) v = algebraMap O K D • v`.

Introduce `v`. Use `Submodule.iSup_induction (fun σ => eigK ρ σ) (motive := fun v => ∑ σ, ((tensAct ρ (t σ)).baseChange K) v = algebraMap O K D • v) (htop v) ?_ ?_ ?_` and prove the remaining obligations. Introduce `σ' w hw`. Rewrite using `[Finset.sum_congr rfl (fun σ _ => hA σ σ' w hw)]`. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules. Introduce `x y hx hy`. Simplify using `only [map_add, Finset.sum_add_distrib, smul_add] at hx hy ⊢`. Rewrite using `[hx, hy]`. Establish `hmem : ∀ σ v, ((tensAct ρ (t σ)).baseChange K) v ∈ eigK ρ σ`.

Introduce `σ v`. Use `Submodule.iSup_induction (fun σ => eigK ρ σ) (motive := fun v => ((tensAct ρ (t σ)).baseChange K) v ∈ eigK ρ σ) (htop v) ?_ ?_ ?_` and prove the remaining obligations. Introduce `σ' w hw`. Rewrite using `[hA σ σ' w hw]`. Use `split_ifs with h`.

Substitute `h` using the available equality. Conclude with `Submodule.smul_mem _ _ hw`. Conclude with `zero_mem _`. Simplify using the standard rewrite rules. Introduce `x y hx hy`.

Simplify using `only [map_add] at hx hy ⊢`. Conclude with `add_mem hx hy`. Introduce `h`. Establish `key : ∑ σ, tensAct ρ (t σ) h = D • h`. Apply `hinj` to reduce the goal to its premises.

Rewrite using `[map_sum, map_smul]`. Repeatedly rewrite using `[inK_apply_map, hsum, algebraMap_smul]`. Rewrite using `[← key]`. Use `Submodule.sum_mem _ fun σ _ => (le_iSup (fun σ => eigLat ρ σ) σ) ?_` and prove the remaining obligations. Use `show inK K H _ ∈ eigK ρ σ`.

Rewrite using `[inK_apply_map]`. Conclude with `hmem σ _`.
-/
theorem iSupIndep_and_smul_mem_iSup : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)), c ≠ ⊥ → ∀ (l : ℕ), l.Prime → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (K : Type) [Field K] [Algebra O K] [IsFractionRing O K], (l : O) ∈ IsLocalRing.maximalIdeal O → Nat.card (E →+* K) = Module.finrank ℚ E → ∀ (D : O), D ≠ 0 → ClearsIdem K c D → ∀ (I : Type) [Fintype I] (φ : I → E →+* K), IsCMTypeIn φ → ∀ (H : Type) [AddCommGroup H] [Module O H] (ρ : orderC c →+* Module.End O H) (Fil : Submodule O H) (B : LinearMap.BilinForm O H), IsCMLattice φ ρ Fil B → DirectSum.IsInternal (fun σ : E →+* K => eigK ρ σ) → iSupIndep (fun σ : E →+* K => eigLat ρ σ) ∧ ∀ h : H, D • h ∈ ⨆ σ : E →+* K, eigLat ρ σ := by
  intro E _ _ _ c _ l _ O _ _ _ _ K _ _ _ _ hcard D _ hclr I _ φ _ H _ _ ρ Fil B hlat hint
  have hfree : Module.Free O H := hlat.1
  have hinj : Function.Injective (inK (O := O) K H) := by
    have h1 := Module.Flat.rTensor_preserves_injective_linearMap (M := H) (Algebra.linearMap O K)
      (IsFractionRing.injective O K)
    have : inK (O := O) K H = (LinearMap.rTensor H (Algebra.linearMap O K)) ∘ₗ
        (TensorProduct.lid O H).symm.toLinearMap := by
      ext h; simp [inK]
    rw [this]; exact h1.comp (TensorProduct.lid O H).symm.injective
  have hindK := hint.submodule_iSupIndep
  have htop : ∀ v : K ⊗[O] H, v ∈ ⨆ σ, eigK ρ σ := fun v => by
    rw [hint.submodule_iSup_eq_top]; trivial
  constructor
  · intro σ
    rw [Submodule.disjoint_def]
    intro x hx1 hx2
    have hle : (⨆ j, ⨆ (_ : j ≠ σ), eigLat ρ j) ≤
        ((⨆ j, ⨆ (_ : j ≠ σ), eigK ρ j).restrictScalars O).comap (inK K H) := by
      refine iSup₂_le fun j hj y hy => ?_
      exact (le_iSup₂ (f := fun j (_ : j ≠ σ) => eigK ρ j) j hj) hy
    have h0 := (Submodule.disjoint_def.1 (hindK σ)) _ hx1 (hle hx2)
    exact hinj (by rw [h0, map_zero])
  · have hfin : Finite (E →+* K) :=
      Nat.finite_of_card_ne_zero (by rw [hcard]; exact Module.finrank_pos.ne')
    letI := Fintype.ofFinite (E →+* K)
    choose t ht using hclr
    have hA : ∀ (σ σ' : E →+* K) v, v ∈ eigK ρ σ' →
        ((tensAct ρ (t σ)).baseChange K) v = if σ' = σ then algebraMap O K D • v else 0 := by
      intro σ σ' v hv
      rw [tensAct_eig ρ σ' v hv, ht σ σ']
      split_ifs <;> simp
    have hsum : ∀ v : K ⊗[O] H, ∑ σ, ((tensAct ρ (t σ)).baseChange K) v = algebraMap O K D • v := by
      intro v
      refine Submodule.iSup_induction (fun σ => eigK ρ σ)
        (motive := fun v => ∑ σ, ((tensAct ρ (t σ)).baseChange K) v = algebraMap O K D • v) (htop v) ?_ ?_ ?_
      · intro σ' w hw
        rw [Finset.sum_congr rfl (fun σ _ => hA σ σ' w hw)]
        simp
      · simp
      · intro x y hx hy
        simp only [map_add, Finset.sum_add_distrib, smul_add] at hx hy ⊢
        rw [hx, hy]
    have hmem : ∀ σ v, ((tensAct ρ (t σ)).baseChange K) v ∈ eigK ρ σ := by
      intro σ v
      refine Submodule.iSup_induction (fun σ => eigK ρ σ)
        (motive := fun v => ((tensAct ρ (t σ)).baseChange K) v ∈ eigK ρ σ) (htop v) ?_ ?_ ?_
      · intro σ' w hw
        rw [hA σ σ' w hw]
        split_ifs with h
        · subst h; exact Submodule.smul_mem _ _ hw
        · exact zero_mem _
      · simp
      · intro x y hx hy
        simp only [map_add] at hx hy ⊢
        exact add_mem hx hy
    intro h
    have key : ∑ σ, tensAct ρ (t σ) h = D • h := by
      apply hinj
      rw [map_sum, map_smul]
      simp_rw [inK_apply_map, hsum, algebraMap_smul]
    rw [← key]
    refine Submodule.sum_mem _ fun σ _ => (le_iSup (fun σ => eigLat ρ σ) σ) ?_
    show inK K H _ ∈ eigK ρ σ
    rw [inK_apply_map]
    exact hmem σ _

end GlobalTheory.EigenLattice
