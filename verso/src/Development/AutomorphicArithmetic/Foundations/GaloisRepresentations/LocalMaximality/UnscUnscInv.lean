import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.LiftFactorization
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

section
variable {S E κ : Type} [CommRing S] [Algebra ℂ S] [AddCommGroup E] [Module ℂ E]
  (act : S →ₐ[ℂ] Module.End ℂ E)

/- English proof (translation)
Rewrite using `[← Module.End.mul_apply, ← map_mul, Units.inv_mul, map_one, Module.End.one_apply]`.
-/
private lemma act_inv_act (v : Sˣ) (m : E) : act ((v⁻¹ : Sˣ) : S) (act (v : S) m) = m := by
  rw [← Module.End.mul_apply, ← map_mul, Units.inv_mul, map_one, Module.End.one_apply]

/- English proof (translation)
Rewrite using `[← Module.End.mul_apply, ← map_mul, Units.mul_inv, map_one, Module.End.one_apply]`.
-/
private lemma act_act_inv (v : Sˣ) (m : E) : act (v : S) (act ((v⁻¹ : Sˣ) : S) m) = m := by
  rw [← Module.End.mul_apply, ← map_mul, Units.mul_inv, map_one, Module.End.one_apply]

/- English proof (translation)
Simplify using `[Finset.prod_inv_distrib]`.
-/
private lemma prod_inv_inv (u : κ → Sˣ) (L : Finset κ) : (∏ l ∈ L, (u⁻¹) l)⁻¹ = ∏ l ∈ L, u l := by
  simp [Finset.prod_inv_distrib]

/- English proof (translation)
Use function extensionality and compare the values at `L`. Simplify using `only [unsc]`. Rewrite using `[prod_inv_inv]`. Conclude with `act_act_inv act _ _`.
-/
private lemma unsc_inv_unsc (u : κ → Sˣ) (c : Finset κ → E) : unsc act u⁻¹ (unsc act u c) = c := by
  funext L
  simp only [unsc]
  rw [prod_inv_inv]
  exact act_act_inv act _ _

/- English proof (translation)
Use function extensionality and compare the values at `L`. Simplify using `only [unsc]`. Rewrite using `[prod_inv_inv]`. Conclude with `act_inv_act act _ _`.
-/
private lemma unsc_unsc_inv (u : κ → Sˣ) (c : Finset κ → E) : unsc act u (unsc act u⁻¹ c) = c := by
  funext L
  simp only [unsc]
  rw [prod_inv_inv]
  exact act_inv_act act _ _

/- English proof (translation)
Rewrite using `[← unsc_inv_unsc act u c, h, unsc_inv_unsc]`.
-/
private lemma unsc_inj (u : κ → Sˣ) {c c' : Finset κ → E} (h : unsc act u c = unsc act u c') : c = c' := by
  rw [← unsc_inv_unsc act u c, h, unsc_inv_unsc]

variable [LinearOrder κ]

/- English proof (translation)
Simplify using `only [kosT, kos, acx, Submodule.mem_pi, Set.mem_univ, true_imp_iff]`. Use `forall_congr' fun s => ?_` and prove the remaining obligations. Distinguish the cases in `h : (s.card : ℤ) = n`. Simplify using `only [h, if_true]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨m, hm, hc⟩`. Express the relevant statement in the definitionally equal form `act _ (c s) ∈ M`. Rewrite using `[← hc, act_inv_act]`. Conclude with `hm`. Introduce `hm`.

Conclude with `⟨_, hm, act_act_inv act _ _⟩`. Simplify using `only [h, if_false, Submodule.mem_bot]`. Prove the components needed by the constructor for the conclusion. Introduce `h0`. Simplify using `[unsc, h0]`.

Introduce `h0`. Establish `h1 : act ((∏ l ∈ s, u l : Sˣ) : S) (unsc act u c s) = 0` using `by rw [h0, map_zero]`. Simplify `h1` using `only [unsc, act_act_inv]`.
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
Use function extensionality and compare the values at `t`. Simplify using `only [unsc, wd, LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.proj_apply, map_sum, map_zsmul]`. Use `Finset.sum_congr rfl fun i hi => ?_` and prove the remaining obligations. Use `congr 1`. Establish `hp : (∏ l ∈ t, u l) = u i * ∏ l ∈ t.erase i, u l` using `(Finset.mul_prod_erase t u hi).symm`.

Rewrite using `[← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, hr, hp, mul_inv, Units.val_mul]`. Use `congr 2`. Expand and normalize the polynomial expressions, which then agree.
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
Introduce `S E _ _ _ _ act κ _ _ M u r z hr n c`. Establish `hD : ∀ c, unsc act u ((kosT act M u z).D c) = (kos act M r).D (unsc act u c)` using `fun c => unsc_wd act u z r hr c`. Establish `hC : ∀ n c, c ∈ (kosT act M u z).C n ↔ unsc act u c ∈ (kos act M r).C n` using `fun n c => mem_C_iff act M u z r n c`. Use `⟨hC n c, ?_, ?_, unsc_inv_unsc act u c, unsc_unsc_inv act u c⟩` and prove the remaining obligations. Simplify using `only [Cx.Z, Submodule.mem_inf, LinearMap.mem_ker]`.

Use `and_congr (hC n c) ?_` and prove the remaining obligations. Rewrite using `[← hD]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Rewrite using `[h]`.

Use function extensionality and compare the values at `L`. Simplify using `[unsc]`. Introduce `h`. Use `unsc_inj act u (h.trans ?_)` and prove the remaining obligations. Use function extensionality and compare the values at `L`.

Simplify using `[unsc]`. Simplify using `only [Cx.B, Submodule.mem_map]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, rfl⟩`. Conclude with `⟨unsc act u y, (hC _ y).1 hy, (hD y).symm⟩`.

Introduce and unpack `⟨y, hy, h⟩`. Use `⟨unsc act u⁻¹ y, (hC _ _).2 ?_, unsc_inj act u ?_⟩` and prove the remaining obligations. Rewrite using `[unsc_unsc_inv]` and apply the resulting hypothesis. Rewrite using `[hD, unsc_unsc_inv, h]`.
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
