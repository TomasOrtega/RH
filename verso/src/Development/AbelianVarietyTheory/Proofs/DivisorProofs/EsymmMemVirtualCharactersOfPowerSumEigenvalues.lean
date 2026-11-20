import Mathlib
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.MatrixTraceIffIsCharacterOverSubfieldComplex
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.VirtualCharactersMulComapConjIndLinear
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.RootsCharpolyPowEqMapPow
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsCharacterEsymmRootsCharpoly
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.MultisetPowerSumNewtonIdentity
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

namespace GlobalTheory.EsymmVirt

/- English proof (translation)
Simplify using `[Multiset.esymm]`.
-/
theorem esymm_zero' (s : Multiset ℂ) : s.esymm 0 = 1 := by
  simp [Multiset.esymm]

/- English proof (translation)
Simplify using `[Multiset.esymm, Multiset.powersetCard_cons, Multiset.map_map, Multiset.sum_map_mul_left]`.
-/
theorem esymm_cons_succ (a : ℂ) (s : Multiset ℂ) (n : ℕ) :
    (a ::ₘ s).esymm (n + 1) = s.esymm (n + 1) + a * s.esymm n := by
  simp [Multiset.esymm, Multiset.powersetCard_cons, Multiset.map_map, Multiset.sum_map_mul_left]

/- English proof (translation)
Proceed by induction on `s using Multiset.induction_on generalizing n with`. Consider the case `empty`. Consider the cases of `n with`. Consider the case `zero => simp [Multiset.esymm]`. Consider the case `succ n => simp [Multiset.esymm, Polynomial.coeff_one, Multiset.powersetCard_zero_right]`.

Consider the case `cons a s ih`. Rewrite using `[Multiset.map_cons, Multiset.prod_cons, add_mul, one_mul, mul_assoc, coeff_add, coeff_C_mul]`. Consider the cases of `n with`. Consider the case `zero => simp [ih, esymm_zero']`. Consider the case `succ n => rw [coeff_X_mul, ih, ih, esymm_cons_succ]`.
-/
theorem coeff_prod_one_add (s : Multiset ℂ) (n : ℕ) :
    ((s.map fun a => (1 + C a * X : ℂ[X])).prod).coeff n = s.esymm n := by
  induction s using Multiset.induction_on generalizing n with
  | empty =>
    cases n with
    | zero => simp [Multiset.esymm]
    | succ n => simp [Multiset.esymm, Polynomial.coeff_one, Multiset.powersetCard_zero_right]
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, add_mul, one_mul, mul_assoc, coeff_add, coeff_C_mul]
    cases n with
    | zero => simp [ih, esymm_zero']
    | succ n => rw [coeff_X_mul, ih, ih, esymm_cons_succ]

/- English proof (translation)
Rewrite using `[← coeff_prod_one_add, Multiset.map_add, Multiset.prod_add, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]`. Simplify using `only [coeff_prod_one_add]`.
-/
theorem esymm_add (s t : Multiset ℂ) (n : ℕ) :
    (s + t).esymm n = ∑ i ∈ Finset.range (n + 1), s.esymm i * t.esymm (n - i) := by
  rw [← coeff_prod_one_add, Multiset.map_add, Multiset.prod_add, coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [coeff_prod_one_add]

/- English proof (translation)
Proceed by induction on `n using Nat.strong_induction_on with`. Consider the case `_ n ih`. Break down `Nat.eq_zero_or_pos n with rfl | hn` into its components or cases. Rewrite using `[esymm_zero', esymm_zero']`. Establish `h1` using `GlobalTheory.multiset_newton_psum s n hn`.

Establish `h2` using `GlobalTheory.multiset_newton_psum t n hn`. Establish `h3 : ∑ i ∈ Finset.Ioo 0 n, (-1) ^ i * s.esymm i * (s.map (· ^ (n - i))).sum = ∑ i ∈ Finset.Ioo 0 n, (-1) ^ i * t.esymm i * (t.map (· ^ (n - i))).sum`. Use `Finset.sum_congr rfl fun i hi => ?_` and prove the remaining obligations. Rewrite `hi` using `[Finset.mem_Ioo]`. Rewrite using `[ih i hi.2, h (n - i) (by omega)]`.

Establish `h4 : ((-1) ^ (n + 1) * (n : ℂ)) ≠ 0` using `mul_ne_zero (pow_ne_zero _ (by norm_num)) (by exact_mod_cast hn.ne')`. Apply `mul_left_cancel₀ h4` to reduce the goal to its premises. Take the linear combination `h2 - h1 + h n hn + h3`.
-/
theorem esymm_eq_of_psum_eq (s t : Multiset ℂ)
    (h : ∀ j : ℕ, 0 < j → (s.map (· ^ j)).sum = (t.map (· ^ j)).sum) (n : ℕ) :
    s.esymm n = t.esymm n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [esymm_zero', esymm_zero']
    have h1 := GlobalTheory.multiset_newton_psum s n hn
    have h2 := GlobalTheory.multiset_newton_psum t n hn
    have h3 : ∑ i ∈ Finset.Ioo 0 n, (-1) ^ i * s.esymm i * (s.map (· ^ (n - i))).sum
        = ∑ i ∈ Finset.Ioo 0 n, (-1) ^ i * t.esymm i * (t.map (· ^ (n - i))).sum := by
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [Finset.mem_Ioo] at hi
      rw [ih i hi.2, h (n - i) (by omega)]
    have h4 : ((-1) ^ (n + 1) * (n : ℂ)) ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ (by norm_num)) (by exact_mod_cast hn.ne')
    apply mul_left_cancel₀ h4
    linear_combination h2 - h1 + h n hn + h3

variable {G : Type} [Group G] [Finite G]

/- English proof (translation)
Simplify using `using (virt_mul_comap_conj_ind_linear G).2.2.2.2 1`.
-/
theorem one_mem_virt : (fun _ : G => (1 : ℂ)) ∈ Virt ℂ ℂ G := by
  simpa using (virt_mul_comap_conj_ind_linear G).2.2.2.2 1

/- English proof (translation)
Establish `: (fun g => (A g + B g).esymm s) = ∑ i ∈ Finset.range (s + 1), (fun g => (A g).esymm i) * (fun g => (B g).esymm (s - i))`. Use function extensionality and compare the values at `g`. Simplify using `[esymm_add, Finset.sum_apply]`. Rewrite using `[this]`. Conclude with `sum_mem fun i _ => (virt_mul_comap_conj_ind_linear G).1 _ (hA _) _ (hB _)`.
-/
theorem esymm_add_mem_virt {A B : G → Multiset ℂ}
    (hA : ∀ s, (fun g => (A g).esymm s) ∈ Virt ℂ ℂ G)
    (hB : ∀ s, (fun g => (B g).esymm s) ∈ Virt ℂ ℂ G) (s : ℕ) :
    (fun g => (A g + B g).esymm s) ∈ Virt ℂ ℂ G := by
  have : (fun g => (A g + B g).esymm s) = ∑ i ∈ Finset.range (s + 1),
      (fun g => (A g).esymm i) * (fun g => (B g).esymm (s - i)) := by
    funext g
    simp [esymm_add, Finset.sum_apply]
  rw [this]
  exact sum_mem fun i _ => (virt_mul_comap_conj_ind_linear G).1 _ (hA _) _ (hB _)

/- English proof (translation)
Establish `h0 : ∀ s, (fun _ : G => (0 : Multiset ℂ).esymm s) ∈ Virt ℂ ℂ G`. Introduce `s`. Consider the cases of `s with`. Consider the case `zero => simpa only [esymm_zero'] using one_mem_virt`. Consider the case `succ s`.

Establish `: (fun _ : G => (0 : Multiset ℂ).esymm (s + 1)) = 0`. Use function extensionality and compare the values at `g`. Simplify using `[Multiset.esymm, Multiset.powersetCard_zero_right]`. Rewrite using `[this]`. Conclude with `zero_mem _`.

Proceed by induction on `hφ using AddSubgroup.closure_induction with`. Consider the case `mem a ha`. Take `⟨n, ρ, hρ⟩` from `(matrixChar_iff_isChar G a).2 ha`. Use `⟨fun g => (Matrix.charpoly (ρ g : Matrix (Fin n) (Fin n) ℂ)).roots, fun _ => 0, fun s => isChar_mem_virt_complex (isChar_esymm_roots_charpoly G n s ρ), h0, fun g j _ => ?_⟩` and prove the remaining obligations. Rewrite using `[hρ, map_pow, Units.val_pow_eq_pow_val, Matrix.trace_eq_sum_roots_charpoly, GlobalTheory.CharpolyPow.roots_charpoly_pow]`.

Simplify using the standard rewrite rules. Consider the case `zero => exact ⟨fun _ => 0, fun _ => 0, h0, h0, fun g j _ => by simp⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨A, B, hA, hB, h⟩` from `hx`. Take `⟨A', B', hA', hB', h'⟩` from `hy`.

Use `⟨fun g => A g + A' g, fun g => B g + B' g, esymm_add_mem_virt hA hA', esymm_add_mem_virt hB hB', fun g j hj => ?_⟩` and prove the remaining obligations. Simplify using `only [Pi.add_apply, Multiset.map_add, Multiset.sum_add]`. Take the linear combination `h g j hj + h' g j hj`. Consider the case `neg x _ hx`. Take `⟨A, B, hA, hB, h⟩` from `hx`.

Use `⟨B, A, hB, hA, fun g j hj => ?_⟩` and prove the remaining obligations. Simplify using `only [Pi.neg_apply]`. Take the linear combination `- h g j hj`.
-/
theorem exists_multisets {φ : G → ℂ} (hφ : φ ∈ Virt ℂ ℂ G) :
    ∃ A B : G → Multiset ℂ, (∀ s, (fun g => (A g).esymm s) ∈ Virt ℂ ℂ G) ∧
      (∀ s, (fun g => (B g).esymm s) ∈ Virt ℂ ℂ G) ∧
      ∀ g j, 0 < j → φ (g ^ j) + ((B g).map (· ^ j)).sum = ((A g).map (· ^ j)).sum := by
  have h0 : ∀ s, (fun _ : G => (0 : Multiset ℂ).esymm s) ∈ Virt ℂ ℂ G := by
    intro s
    cases s with
    | zero => simpa only [esymm_zero'] using one_mem_virt
    | succ s =>
      have : (fun _ : G => (0 : Multiset ℂ).esymm (s + 1)) = 0 := by
        funext g
        simp [Multiset.esymm, Multiset.powersetCard_zero_right]
      rw [this]
      exact zero_mem _
  induction hφ using AddSubgroup.closure_induction with
  | mem a ha =>
    obtain ⟨n, ρ, hρ⟩ := (matrixChar_iff_isChar G a).2 ha
    refine ⟨fun g => (Matrix.charpoly (ρ g : Matrix (Fin n) (Fin n) ℂ)).roots, fun _ => 0,
      fun s => isChar_mem_virt_complex (isChar_esymm_roots_charpoly G n s ρ), h0, fun g j _ => ?_⟩
    rw [hρ, map_pow, Units.val_pow_eq_pow_val, Matrix.trace_eq_sum_roots_charpoly,
      GlobalTheory.CharpolyPow.roots_charpoly_pow]
    simp
  | zero => exact ⟨fun _ => 0, fun _ => 0, h0, h0, fun g j _ => by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨A, B, hA, hB, h⟩ := hx
    obtain ⟨A', B', hA', hB', h'⟩ := hy
    refine ⟨fun g => A g + A' g, fun g => B g + B' g, esymm_add_mem_virt hA hA',
      esymm_add_mem_virt hB hB', fun g j hj => ?_⟩
    simp only [Pi.add_apply, Multiset.map_add, Multiset.sum_add]
    linear_combination h g j hj + h' g j hj
  | neg x _ hx =>
    obtain ⟨A, B, hA, hB, h⟩ := hx
    refine ⟨B, A, hB, hA, fun g j hj => ?_⟩
    simp only [Pi.neg_apply]
    linear_combination - h g j hj

/- English proof (translation)
Introduce `G _ _ φ x hφ hx s`. Take `⟨A, B, hA, hB, h⟩` from `exists_multisets hφ`. Establish `he : ∀ g n, (x g + B g).esymm n = (A g).esymm n` using `fun g n => esymm_eq_of_psum_eq _ _ (fun j hj => by`. Rewrite using `[Multiset.map_add, Multiset.sum_add, ← hx g j hj, h g j hj]) n`. Proceed by induction on `s using Nat.strong_induction_on with`.

Consider the case `_ s ih`. Establish `: (fun g => (x g).esymm s) = (fun g => (A g).esymm s) - ∑ i ∈ Finset.range s, (fun g => (x g).esymm i) * (fun g => (B g).esymm (s - i))`. Use function extensionality and compare the values at `g`. Use `he g s` as an intermediate fact. Rewrite `this` using `[esymm_add, Finset.sum_range_succ, Nat.sub_self, esymm_zero', mul_one]`.

Simplify using `only [Pi.sub_apply, Finset.sum_apply, Pi.mul_apply]`. Take the linear combination `this`. Rewrite using `[this]`. Conclude with `sub_mem (hA s) (sum_mem fun i hi => (virt_mul_comap_conj_ind_linear G).1 _ (ih i (Finset.mem_range.1 hi)) _ (hB _))`.
-/
theorem esymm_mem_virt : ∀ (G : Type) [Group G] [Finite G] (φ : G → ℂ) (x : G → Multiset ℂ),
    φ ∈ Virt ℂ ℂ G → (∀ (g : G) (j : ℕ), 0 < j → φ (g ^ j) = ((x g).map (· ^ j)).sum) →
    ∀ s : ℕ, (fun g => (x g).esymm s) ∈ Virt ℂ ℂ G := by
  intro G _ _ φ x hφ hx s
  obtain ⟨A, B, hA, hB, h⟩ := exists_multisets hφ
  have he : ∀ g n, (x g + B g).esymm n = (A g).esymm n := fun g n =>
    esymm_eq_of_psum_eq _ _ (fun j hj => by
      rw [Multiset.map_add, Multiset.sum_add, ← hx g j hj, h g j hj]) n
  induction s using Nat.strong_induction_on with
  | _ s ih =>
    have : (fun g => (x g).esymm s) = (fun g => (A g).esymm s) - ∑ i ∈ Finset.range s,
        (fun g => (x g).esymm i) * (fun g => (B g).esymm (s - i)) := by
      funext g
      have := he g s
      rw [esymm_add, Finset.sum_range_succ, Nat.sub_self, esymm_zero', mul_one] at this
      simp only [Pi.sub_apply, Finset.sum_apply, Pi.mul_apply]
      linear_combination this
    rw [this]
    exact sub_mem (hA s) (sum_mem fun i hi =>
      (virt_mul_comap_conj_ind_linear G).1 _ (ih i (Finset.mem_range.1 hi)) _ (hB _))

end GlobalTheory.EsymmVirt
