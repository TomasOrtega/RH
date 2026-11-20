import Mathlib
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.OneMemOfMulMemOfForallPrimeNotDvd
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.OneMemVirtualCharactersOfIntegralCombinationStatement
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.ExistsInducedIntPrimeToStatement
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.IndMulClassFunEqIndMulRestrict
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.VirtualCharactersMulComapConjIndLinearStatement
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

namespace GlobalTheory.BI

/- English proof (translation)
Introduce `G _ _`. Use `set A : Set (G → ℂ) := {f : G → ℂ | ∃ (E : Subgroup G) (ψ : E → ℂ), (∃ l : ℕ, l.Prime ∧ ∀ y : E, ∃ j : ℕ, y ^ l ^ j ∈ Subgroup.center E) ∧ ψ ∈ Virt ℂ ℂ E ∧ f = ind E ψ} with hA`. Take `⟨hmul, hpull, hclass, hind, -⟩` from `GlobalTheory.T.virtualCharacters_mul_comap_conj_ind_linear G`. Establish `hAV : ∀ f ∈ A, f ∈ Virt ℂ ℂ G`. Introduce and unpack `f ⟨E, ψ, -, hψ, rfl⟩`.

Conclude with `hind E ψ hψ`. Establish `hJV : AddSubgroup.closure A ≤ Virt ℂ ℂ G` using `(AddSubgroup.closure_le _).2 hAV`. Establish `hAA : ∀ f ∈ A, ∀ g ∈ A, f * g ∈ A`. Introduce `f hf g hg`. Establish `hgV` using `hAV g hg`.

Take `⟨E, ψ, hE, hψ, rfl⟩` from `hf`. Use `⟨E, fun h => ψ h * g h, hE, ?_, ind_mul_classFun_eq_ind_mul_restrict G E ψ g (hclass g hgV)⟩` and prove the remaining obligations. Conclude with `(GlobalTheory.T.virtualCharacters_mul_comap_conj_ind_linear E).1 ψ hψ _ (hpull g hgV E E.subtype)`. Set `R` to `integralClosure ℤ ℂ`. Set `J : Submodule R (G → ℂ)` to `Submodule.span R A`.

Establish `hJJ : ∀ f ∈ J, ∀ g ∈ J, f * g ∈ J`. Introduce `f hf g hg`. Proceed by induction on `hf, hg using Submodule.span_induction₂ with`. Consider the case `mem_mem x y hx hy => exact Submodule.subset_span (hAA x hx y hy)`. Consider the case `zero_left y hy => simp`.

Consider the case `zero_right x hx => simp`. Consider the case `add_left x y z hx hy hz h1 h2 => rw [add_mul]`. Conclude with `J.add_mem h1 h2`. Consider the case `add_right x y z hx hy hz h1 h2 => rw [mul_add]`. Conclude with `J.add_mem h1 h2`.

Consider the case `smul_left r x y hx hy h => rw [smul_mul_assoc]`. Conclude with `J.smul_mem r h`. Consider the case `smul_right r x y hx hy h => rw [mul_smul_comm]`. Conclude with `J.smul_mem r h`. Set `c : (G → ℤ) →+* (G → ℂ)` to `(Int.castRingHom ℂ).compLeft G`.

Set `S : AddSubgroup (G → ℤ)` to `J.toAddSubgroup.comap c.toAddMonoidHom`. Establish `hS : ∀ f, f ∈ S ↔ c f ∈ J` using `fun f => Iff.rfl`. Establish `h1 : (1 : G → ℤ) ∈ S`. Use `GlobalTheory.one_mem_of_mul_mem_of_forall_prime_not_dvd G S ?_ ?_` and prove the remaining obligations. Introduce `f hf g hg`.

Rewrite `hf`, `hg`, the goal using `[hS]`. Rewrite using `[map_mul]`. Conclude with `hJJ _ hf _ hg`. Introduce `x p hp`. Take `⟨E, f, ι, _, r, lam, hE, hf, hr, hsum⟩` from `GlobalTheory.T.exists_integral_comb_induced_linear_not_dvd G x p hp`.

Use `⟨f, ?_, hf⟩` and prove the remaining obligations. Rewrite using `[hS]`. Establish `: c f = ∑ i, (⟨r i, hr i⟩ : R) • ind E (fun e => (lam i e : ℂ))`. Use function extensionality and compare the values at `g`. Rewrite using `[Finset.sum_apply]`.

Conclude with `hsum g`. Rewrite using `[this]`. Use `J.sum_mem fun i _ => J.smul_mem _ (Submodule.subset_span ?_)` and prove the remaining obligations. Conclude with `⟨E, _, hE, (GlobalTheory.T.virtualCharacters_mul_comap_conj_ind_linear E).2.2.2.2 (lam i), rfl⟩`. Rewrite `h1` using `[hS, map_one]`.

Take `⟨n, r, s, hsum⟩` from `Submodule.mem_span_set'.1 h1`. Use `GlobalTheory.T.one_mem_virtualCharacters_of_integral_combination G _ hJV (Fin n) (fun i => (r i : ℂ)) (fun i => (s i : G → ℂ)) (fun i => (r i).2) (fun i => AddSubgroup.subset_closure (s i).2) fun g => ?_` and prove the remaining obligations. Use `congrFun hsum g` as an intermediate fact. Rewrite `this` using `[Finset.sum_apply]`. Conclude with `this`.
-/
theorem one_mem_closure_ind_centralByPrime :
    ∀ (G : Type) [Group G] [Finite G], (1 : G → ℂ) ∈ AddSubgroup.closure {f : G → ℂ | ∃ (E : Subgroup G) (ψ : E → ℂ), (∃ l : ℕ, l.Prime ∧ ∀ y : E, ∃ j : ℕ, y ^ l ^ j ∈ Subgroup.center E) ∧ ψ ∈ Virt ℂ ℂ E ∧ f = ind E ψ} := by
  intro G _ _
  classical
  set A : Set (G → ℂ) := {f : G → ℂ | ∃ (E : Subgroup G) (ψ : E → ℂ), (∃ l : ℕ, l.Prime ∧ ∀ y : E, ∃ j : ℕ, y ^ l ^ j ∈ Subgroup.center E) ∧ ψ ∈ Virt ℂ ℂ E ∧ f = ind E ψ} with hA
  obtain ⟨hmul, hpull, hclass, hind, -⟩ := GlobalTheory.T.virtualCharacters_mul_comap_conj_ind_linear G
  have hAV : ∀ f ∈ A, f ∈ Virt ℂ ℂ G := by
    rintro f ⟨E, ψ, -, hψ, rfl⟩
    exact hind E ψ hψ
  have hJV : AddSubgroup.closure A ≤ Virt ℂ ℂ G := (AddSubgroup.closure_le _).2 hAV
  have hAA : ∀ f ∈ A, ∀ g ∈ A, f * g ∈ A := by
    intro f hf g hg
    have hgV := hAV g hg
    obtain ⟨E, ψ, hE, hψ, rfl⟩ := hf
    refine ⟨E, fun h => ψ h * g h, hE, ?_, ind_mul_classFun_eq_ind_mul_restrict G E ψ g (hclass g hgV)⟩
    exact (GlobalTheory.T.virtualCharacters_mul_comap_conj_ind_linear E).1 ψ hψ _ (hpull g hgV E E.subtype)
  let R := integralClosure ℤ ℂ
  let J : Submodule R (G → ℂ) := Submodule.span R A
  have hJJ : ∀ f ∈ J, ∀ g ∈ J, f * g ∈ J := by
    intro f hf g hg
    induction hf, hg using Submodule.span_induction₂ with
    | mem_mem x y hx hy => exact Submodule.subset_span (hAA x hx y hy)
    | zero_left y hy => simp
    | zero_right x hx => simp
    | add_left x y z hx hy hz h1 h2 => rw [add_mul]; exact J.add_mem h1 h2
    | add_right x y z hx hy hz h1 h2 => rw [mul_add]; exact J.add_mem h1 h2
    | smul_left r x y hx hy h => rw [smul_mul_assoc]; exact J.smul_mem r h
    | smul_right r x y hx hy h => rw [mul_smul_comm]; exact J.smul_mem r h
  let c : (G → ℤ) →+* (G → ℂ) := (Int.castRingHom ℂ).compLeft G
  let S : AddSubgroup (G → ℤ) := J.toAddSubgroup.comap c.toAddMonoidHom
  have hS : ∀ f, f ∈ S ↔ c f ∈ J := fun f => Iff.rfl
  have h1 : (1 : G → ℤ) ∈ S := by
    refine GlobalTheory.one_mem_of_mul_mem_of_forall_prime_not_dvd G S ?_ ?_
    · intro f hf g hg
      rw [hS] at hf hg ⊢
      rw [map_mul]
      exact hJJ _ hf _ hg
    · intro x p hp
      obtain ⟨E, f, ι, _, r, lam, hE, hf, hr, hsum⟩ := GlobalTheory.T.exists_integral_comb_induced_linear_not_dvd G x p hp
      refine ⟨f, ?_, hf⟩
      rw [hS]
      have : c f = ∑ i, (⟨r i, hr i⟩ : R) • ind E (fun e => (lam i e : ℂ)) := by
        funext g
        rw [Finset.sum_apply]
        exact hsum g
      rw [this]
      refine J.sum_mem fun i _ => J.smul_mem _ (Submodule.subset_span ?_)
      exact ⟨E, _, hE, (GlobalTheory.T.virtualCharacters_mul_comap_conj_ind_linear E).2.2.2.2 (lam i), rfl⟩
  rw [hS, map_one] at h1
  obtain ⟨n, r, s, hsum⟩ := Submodule.mem_span_set'.1 h1
  refine GlobalTheory.T.one_mem_virtualCharacters_of_integral_combination G _ hJV (Fin n) (fun i => (r i : ℂ)) (fun i => (s i : G → ℂ)) (fun i => (r i).2)
    (fun i => AddSubgroup.subset_closure (s i).2) fun g => ?_
  have := congrFun hsum g
  rw [Finset.sum_apply] at this
  exact this

end GlobalTheory.BI
