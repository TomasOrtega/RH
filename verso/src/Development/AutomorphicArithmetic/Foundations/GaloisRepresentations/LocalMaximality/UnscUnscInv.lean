import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.LiftFactorization
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

section
variable {S E κ : Type} [CommRing S] [Algebra ℂ S] [AddCommGroup E] [Module ℂ E]
  (act : S →ₐ[ℂ] Module.End ℂ E)

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
private lemma act_inv_act (v : Sˣ) (m : E) : act ((v⁻¹ : Sˣ) : S) (act (v : S) m) = m := by
  rw [← Module.End.mul_apply, ← map_mul, Units.inv_mul, map_one, Module.End.one_apply]

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
private lemma act_act_inv (v : Sˣ) (m : E) : act (v : S) (act ((v⁻¹ : Sˣ) : S) m) = m := by
  rw [← Module.End.mul_apply, ← map_mul, Units.mul_inv, map_one, Module.End.one_apply]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
private lemma prod_inv_inv (u : κ → Sˣ) (L : Finset κ) : (∏ l ∈ L, (u⁻¹) l)⁻¹ = ∏ l ∈ L, u l := by
  simp [Finset.prod_inv_distrib]

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
private lemma unsc_inv_unsc (u : κ → Sˣ) (c : Finset κ → E) : unsc act u⁻¹ (unsc act u c) = c := by
  funext L
  simp only [unsc]
  rw [prod_inv_inv]
  exact act_act_inv act _ _

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
private lemma unsc_unsc_inv (u : κ → Sˣ) (c : Finset κ → E) : unsc act u (unsc act u⁻¹ c) = c := by
  funext L
  simp only [unsc]
  rw [prod_inv_inv]
  exact act_inv_act act _ _

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
private lemma unsc_inj (u : κ → Sˣ) {c c' : Finset κ → E} (h : unsc act u c = unsc act u c') : c = c' := by
  rw [← unsc_inv_unsc act u c, h, unsc_inv_unsc]

variable [LinearOrder κ]

/- English proof (translation)
Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Consider separately whether the proposition holds or fails. Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion.

Assume the hypotheses and unpack their components. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Supply the required witnesses or components.

Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. A detailed English derivation is pending.
-/
private lemma mem_C_iff (M : Submodule ℂ E) (u : κ → Sˣ) (z r : κ → S) (n : ℤ) (c : Finset κ → E) :
    c ∈ (kosT act M u z).C n ↔ unsc act u c ∈ (kos act M r).C n := by
  simp only [kosT, kos, acx, Submodule.mem_pi, Set.mem_univ, true_imp_iff]
  refine forall_congr' fun s => ?_
  by_cases h : (s.card : ℤ) = n
  · simp only [h, if_true]
    constructor
    · rintro ⟨m, hm, hc⟩
      change act _ (c s) ∈ M
      rw [← hc, act_inv_act]
      exact hm
    · intro hm
      exact ⟨_, hm, act_act_inv act _ _⟩
  · simp only [h, if_false, Submodule.mem_bot]
    constructor
    · intro h0
      simp [unsc, h0]
    · intro h0
      have h1 : act ((∏ l ∈ s, u l : Sˣ) : S) (unsc act u c s) = 0 := by rw [h0, map_zero]
      simpa only [unsc, act_act_inv] using h1

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Reduce the equality to equality of the corresponding arguments. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Expand and normalize the polynomial expressions, which then agree.
-/
private lemma unsc_wd (u : κ → Sˣ) (z r : κ → S) (hr : ∀ l, r l = z l * ((u l)⁻¹ : Sˣ)) (c : Finset κ → E) :
    unsc act u (wd (fun l => act (z l)) c) = wd (fun l => act (r l)) (unsc act u c) := by
  funext t
  simp only [unsc, wd, LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply,
    LinearMap.proj_apply, map_sum, map_zsmul]
  refine Finset.sum_congr rfl fun i hi => ?_
  congr 1
  have hp : (∏ l ∈ t, u l) = u i * ∏ l ∈ t.erase i, u l := (Finset.mul_prod_erase t u hi).symm
  rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, hr, hp, mul_inv, Units.val_mul]
  congr 2
  ring

end

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Apply function extensionality and compare values at an arbitrary argument.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Supply the required witnesses or components.

Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Use the resulting assumption. Rewrite the conclusion using the stated equalities.
-/
theorem UpperTheory.Gal.productCup_of_system.rS_of :
    RS := by
  intro S E _ _ _ _ act κ _ _ M u r z hr n c
  have hD : ∀ c, unsc act u ((kosT act M u z).D c) = (kos act M r).D (unsc act u c) :=
    fun c => unsc_wd act u z r hr c
  have hC : ∀ n c, c ∈ (kosT act M u z).C n ↔ unsc act u c ∈ (kos act M r).C n :=
    fun n c => mem_C_iff act M u z r n c
  refine ⟨hC n c, ?_, ?_, unsc_inv_unsc act u c, unsc_unsc_inv act u c⟩
  · simp only [Cx.Z, Submodule.mem_inf, LinearMap.mem_ker]
    refine and_congr (hC n c) ?_
    rw [← hD]
    constructor
    · intro h
      rw [h]
      funext L
      simp [unsc]
    · intro h
      refine unsc_inj act u (h.trans ?_)
      funext L
      simp [unsc]
  · simp only [Cx.B, Submodule.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨unsc act u y, (hC _ y).1 hy, (hD y).symm⟩
    · rintro ⟨y, hy, h⟩
      refine ⟨unsc act u⁻¹ y, (hC _ _).2 ?_, unsc_inj act u ?_⟩
      · rwa [unsc_unsc_inv]
      · rw [hD, unsc_unsc_inv, h]
