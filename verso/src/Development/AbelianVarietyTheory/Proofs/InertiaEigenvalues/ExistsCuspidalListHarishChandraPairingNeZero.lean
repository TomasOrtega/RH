import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraFrobeniusReciprocityStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraInductionExteriorProductAssocCommStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharacterDecompositionAndClassFunctionExpansionStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraInductionCharacterRestrictionDecompStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraProductListIsCharacterAndPermInvariStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CentralIdempotentOfIrrCharacterOrthogonalCentralStatement

noncomputable section

open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

namespace GlobalTheory.GLq.SuppCusp

section general
variable {G : Type} [Group G] [Fintype G]

/- English proof (translation)
Unfold `ip`. Rewrite using `[← mul_add, ← Finset.sum_add_distrib]`. Use `congr 1`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `x _`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem ip_add_left (u v w : G → ℂ) : ip (fun x => u x + v x) w = ip u w + ip v w := by
  unfold ip; rw [← mul_add, ← Finset.sum_add_distrib]; congr 1
  apply Finset.sum_congr rfl; intro x _; ring

/- English proof (translation)
Unfold `ip`. Rewrite using `[← mul_add, ← Finset.sum_add_distrib]`. Use `congr 1`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `x _`.

Simplify using `only [Pi.add_apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem ip_add_right (u v w : G → ℂ) : ip u (v + w) = ip u v + ip u w := by
  unfold ip; rw [← mul_add, ← Finset.sum_add_distrib]; congr 1
  apply Finset.sum_congr rfl; intro x _; simp only [Pi.add_apply]; ring

/- English proof (translation)
Take `⟨V, -, hV⟩` from `h`. Conclude with `⟨V, hV⟩`.
-/
theorem irr_char {χ : G → ℂ} (h : IsIrr χ) : IsChar χ := by
  obtain ⟨V, -, hV⟩ := h; exact ⟨V, hV⟩

/- English proof (translation)
The claim follows from `(GlobalTheory.T.character_decomposition_and_classFunction_expansion G χ).2.2.1 h`.
-/
theorem char_class {χ : G → ℂ} (h : IsChar χ) : IsClass χ := (GlobalTheory.T.character_decomposition_and_classFunction_expansion G χ).2.2.1 h

/- English proof (translation)
Take `⟨L, hL, rfl⟩` from `(GlobalTheory.T.character_decomposition_and_classFunction_expansion G A).1 hA`. Use `clear hA`. Proceed by induction on `L with`. Consider the case `nil => exact ⟨0, by simp [ip]⟩`. Consider the case `cons ρ L ih`.

Take `⟨c, hc⟩` from `ih (fun r hr => hL r (List.mem_cons_of_mem _ hr))`. Establish `h1` using `(GlobalTheory.T.centralIdempotentOfIrrCharacter_orthogonal_central G α ρ hα (hL ρ (by simp))).2.2`. Use `⟨(if α = ρ then 1 else 0) + c, ?_⟩` and prove the remaining obligations. Apply the tactic sequence `rw [List.sum_cons, ip_add_right, hc, h1]; split_ifs <;> simp`.
-/
theorem ip_irr_char_nat {α A : G → ℂ} (hα : IsIrr α) (hA : IsChar A) : ∃ c : ℕ, ip α A = c := by
  obtain ⟨L, hL, rfl⟩ := (GlobalTheory.T.character_decomposition_and_classFunction_expansion G A).1 hA
  clear hA
  induction L with
  | nil => exact ⟨0, by simp [ip]⟩
  | cons ρ L ih =>
    obtain ⟨c, hc⟩ := ih (fun r hr => hL r (List.mem_cons_of_mem _ hr))
    have h1 := (GlobalTheory.T.centralIdempotentOfIrrCharacter_orthogonal_central G α ρ hα (hL ρ (by simp))).2.2
    refine ⟨(if α = ρ then 1 else 0) + c, ?_⟩
    rw [List.sum_cons, ip_add_right, hc, h1]; split_ifs <;> simp

end general

section prod
variable {G H : Type} [Group G] [Fintype G] [Group H] [Fintype H]

/- English proof (translation)
Unfold `ip`. Rewrite using `[Fintype.card_prod, Fintype.sum_prod_type]`. Simplify using `only [Prod.fst_inv, Prod.snd_inv]`. Establish `e : ∀ x y, α x * β y * (A x⁻¹ * B y⁻¹) = (α x * A x⁻¹) * (β y * B y⁻¹)` using `by intros; ring`. Simplify using `only [e]`.

Rewrite using `[show ((Fintype.card G : ℂ))⁻¹ * (∑ x, α x * A x⁻¹) * (((Fintype.card H : ℂ))⁻¹ * ∑ y, β y * B y⁻¹) = ((Fintype.card G : ℂ))⁻¹ * ((Fintype.card H : ℂ))⁻¹ * ((∑ x, α x * A x⁻¹) * ∑ y, β y * B y⁻¹) by ring, Finset.sum_mul_sum, Nat.cast_mul, mul_inv]`.
-/
theorem ip_prod_single (α A : G → ℂ) (β B : H → ℂ) :
    ip (fun p : G × H => α p.1 * β p.2) (fun p => A p.1 * B p.2) = ip α A * ip β B := by
  unfold ip
  rw [Fintype.card_prod, Fintype.sum_prod_type]
  simp only [Prod.fst_inv, Prod.snd_inv]
  have e : ∀ x y, α x * β y * (A x⁻¹ * B y⁻¹) = (α x * A x⁻¹) * (β y * B y⁻¹) := by intros; ring
  simp only [e]
  rw [show ((Fintype.card G : ℂ))⁻¹ * (∑ x, α x * A x⁻¹) * (((Fintype.card H : ℂ))⁻¹ * ∑ y, β y * B y⁻¹) =
    ((Fintype.card G : ℂ))⁻¹ * ((Fintype.card H : ℂ))⁻¹ * ((∑ x, α x * A x⁻¹) * ∑ y, β y * B y⁻¹) by ring,
    Finset.sum_mul_sum, Nat.cast_mul, mul_inv]

/- English proof (translation)
Proceed by induction on `R with`. Consider the case `nil => simp [ip]`. Consider the case `cons k R ih`. Simplify using `only [List.map_cons, List.sum_cons]`. Rewrite using `[ip_add_left (fun p : G × H => k.1 p.1 * k.2 p.2), ih, ip_prod_single]`.
-/
theorem ip_prod_list (R : List ((G → ℂ) × (H → ℂ))) (A : G → ℂ) (B : H → ℂ) :
    ip (fun p : G × H => (R.map fun k => k.1 p.1 * k.2 p.2).sum) (fun p => A p.1 * B p.2) =
      (R.map fun k => ip k.1 A * ip k.2 B).sum := by
  induction R with
  | nil => simp [ip]
  | cons k R ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [ip_add_left (fun p : G × H => k.1 p.1 * k.2 p.2), ih, ip_prod_single]

/- English proof (translation)
Proceed by induction on `R with`. Consider the case `nil => exact ⟨0, by simp, by simp⟩`. Consider the case `cons k R ih`. Take `⟨N, hN, hN0⟩` from `ih (fun r hr => hR r (List.mem_cons_of_mem _ hr))`. Take `⟨c, hc⟩` from `ip_irr_char_nat (hR k (by simp)).1 hA`.

Take `⟨d, hd⟩` from `ip_irr_char_nat (hR k (by simp)).2 hB`. Use `⟨c * d + N, by simp [List.sum_cons, hN, hc, hd], ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨k', hk', h1, h2⟩`. Break down `List.mem_cons.1 hk' with rfl | hk'` into its components or cases. Rewrite `h1` using `[hc]`.

Rewrite `h2` using `[hd]`. Establish `hc0 : c ≠ 0` using `by rintro rfl; simp at h1`. Establish `hd0 : d ≠ 0` using `by rintro rfl; simp at h2`. Use `Nat.mul_ne_zero hc0 hd0` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Use `hN0 ⟨k', hk', h1, h2⟩` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem sum_nat_ne_zero (R : List ((G → ℂ) × (H → ℂ))) (A : G → ℂ) (B : H → ℂ)
    (hR : ∀ k ∈ R, IsIrr k.1 ∧ IsIrr k.2) (hA : IsChar A) (hB : IsChar B) :
    ∃ N : ℕ, (R.map fun k => ip k.1 A * ip k.2 B).sum = N ∧
      ((∃ k ∈ R, ip k.1 A ≠ 0 ∧ ip k.2 B ≠ 0) → N ≠ 0) := by
  induction R with
  | nil => exact ⟨0, by simp, by simp⟩
  | cons k R ih =>
    obtain ⟨N, hN, hN0⟩ := ih (fun r hr => hR r (List.mem_cons_of_mem _ hr))
    obtain ⟨c, hc⟩ := ip_irr_char_nat (hR k (by simp)).1 hA
    obtain ⟨d, hd⟩ := ip_irr_char_nat (hR k (by simp)).2 hB
    refine ⟨c * d + N, by simp [List.sum_cons, hN, hc, hd], ?_⟩
    rintro ⟨k', hk', h1, h2⟩
    rcases List.mem_cons.1 hk' with rfl | hk'
    · rw [hc] at h1; rw [hd] at h2
      have hc0 : c ≠ 0 := by rintro rfl; simp at h1
      have hd0 : d ≠ 0 := by rintro rfl; simp at h2
      have := Nat.mul_ne_zero hc0 hd0; omega
    · have := hN0 ⟨k', hk', h1, h2⟩; omega

end prod

section lists
variable {g : ℕ} [Fact g.Prime]

/- English proof (translation)
Simplify using `[degL, List.map_append, List.sum_append]`.
-/
theorem degL_append (L₁ L₂ : List (Pc g)) : degL (L₁ ++ L₂) = degL L₁ + degL L₂ := by
  simp [degL, List.map_append, List.sum_append]

/- English proof (translation)
The claim follows from `char_class (GlobalTheory.T.harishChandraProductList_isCharacter_and_perm_invariant g L L (degL L) rfl hL).1`.
-/
theorem class_hcL (L : List (Pc g)) (hL : ∀ p ∈ L, IsChar p.2) : IsClass (hcL L (degL L)) :=
  char_class (GlobalTheory.T.harishChandraProductList_isCharacter_and_perm_invariant g L L (degL L) rfl hL).1

/- English proof (translation)
The claim follows from `(GlobalTheory.T.harishChandraProductList_isCharacter_and_perm_invariant g L L (degL L) rfl hL).1`.
-/
theorem char_hcL (L : List (Pc g)) (hL : ∀ p ∈ L, IsChar p.2) : IsChar (hcL L (degL L)) :=
  (GlobalTheory.T.harishChandraProductList_isCharacter_and_perm_invariant g L L (degL L) rfl hL).1

/- English proof (translation)
Proceed by induction on `L₁ generalizing n with`. Consider the case `nil`. Establish `h2 : ∀ p ∈ L₂, IsChar p.2` using `fun p hp => h p (by simpa using hp)`. Express the relevant statement in the definitionally equal form `n = 0 + degL L₂ at hn`. Rewrite `hn` using `[Nat.zero_add]`.

Substitute `hn` using the available equality. Conclude with `((GlobalTheory.T.harishChandraInductionExteriorProduct_assoc_comm g (degL L₂) 0 0 (degL L₂) (hcL L₂ (degL L₂)) (fun _ => 1) (fun _ => 1) (class_hcL L₂ h2) (fun _ _ => rfl) (fun _ _ => rfl)).2.2.1).symm`. Consider the case `cons p L₁ ih`. Establish `hp : IsChar p.2` using `h p (by simp)`. Establish `h1 : ∀ q ∈ L₁, IsChar q.2` using `fun q hq => h q (by simp [hq])`.

Establish `h2 : ∀ q ∈ L₂, IsChar q.2` using `fun q hq => h q (by simp [hq])`. Establish `h12 : ∀ q ∈ L₁ ++ L₂, IsChar q.2` using `fun q hq => h q (by simp at hq ⊢; tauto)`. Establish `e1` using `degL_append L₁ L₂`. Establish `e2 : degL (p :: L₁) = p.1 + degL L₁` using `by simp [degL]`. Rewrite using `[List.cons_append, hcL_cons, hcL_cons, ih h12 (degL (L₁ ++ L₂)) e1, e1, e2]`.

Conclude with `((GlobalTheory.T.harishChandraInductionExteriorProduct_assoc_comm g p.1 (degL L₁) (degL L₂) n p.2 (hcL L₁ (degL L₁)) (hcL L₂ (degL L₂)) (char_class hp) (class_hcL L₁ h1) (class_hcL L₂ h2)).1 (by omega)).symm`.
-/
theorem hcL_append (L₁ L₂ : List (Pc g)) (h : ∀ p ∈ L₁ ++ L₂, IsChar p.2) (n : ℕ)
    (hn : n = degL L₁ + degL L₂) :
    hcL (L₁ ++ L₂) n = hc (degL L₁) (degL L₂) (hcL L₁ (degL L₁)) (hcL L₂ (degL L₂)) n := by
  induction L₁ generalizing n with
  | nil =>
    have h2 : ∀ p ∈ L₂, IsChar p.2 := fun p hp => h p (by simpa using hp)
    change n = 0 + degL L₂ at hn
    rw [Nat.zero_add] at hn; subst hn
    exact ((GlobalTheory.T.harishChandraInductionExteriorProduct_assoc_comm g (degL L₂) 0 0 (degL L₂) (hcL L₂ (degL L₂)) (fun _ => 1) (fun _ => 1)
      (class_hcL L₂ h2) (fun _ _ => rfl) (fun _ _ => rfl)).2.2.1).symm
  | cons p L₁ ih =>
    have hp : IsChar p.2 := h p (by simp)
    have h1 : ∀ q ∈ L₁, IsChar q.2 := fun q hq => h q (by simp [hq])
    have h2 : ∀ q ∈ L₂, IsChar q.2 := fun q hq => h q (by simp [hq])
    have h12 : ∀ q ∈ L₁ ++ L₂, IsChar q.2 := fun q hq => h q (by simp at hq ⊢; tauto)
    have e1 := degL_append L₁ L₂
    have e2 : degL (p :: L₁) = p.1 + degL L₁ := by simp [degL]
    rw [List.cons_append, hcL_cons, hcL_cons, ih h12 (degL (L₁ ++ L₂)) e1, e1, e2]
    exact ((GlobalTheory.T.harishChandraInductionExteriorProduct_assoc_comm g p.1 (degL L₁) (degL L₂) n p.2 (hcL L₁ (degL L₁)) (hcL L₂ (degL L₂))
      (char_class hp) (class_hcL L₁ h1) (class_hcL L₂ h2)).1 (by omega)).symm

end lists

/- English proof (translation)
Proceed by induction on `n using Nat.strong_induction_on with`. Consider the case `_ n ih`. Establish `hcls : IsClass χ` using `char_class (irr_char hχ)`. Establish `hself : ip χ χ = 1` using `by simpa using (GlobalTheory.T.centralIdempotentOfIrrCharacter_orthogonal_central _ χ χ hχ hχ).2.2`. Distinguish the cases in `hn : n = 0`.

Substitute `hn` using the available equality. Establish `hsub : ∀ x : Gn g 0, x = 1` using `fun x => Units.ext (Matrix.ext fun i _ => i.elim0)`. Establish `hu : (Finset.univ : Finset (Gn g 0)) = {1}` using `by ext x; simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]; exact hsub x`. Establish `hcard : Fintype.card (Gn g 0) = 1` using `by rw [← Finset.card_univ, hu]; simp`. Establish `hc1 : ∀ f : Gn g 0 → ℂ, ip χ f = χ 1 * f 1`.

Introduce `f`. Unfold `ip`. Rewrite using `[hcard, hu]`. Simplify using the standard rewrite rules. Use `⟨[], by simp, rfl, ?_⟩` and prove the remaining obligations.

Rewrite using `[hcL_nil, hc1]`. Rewrite `hself` using `[hc1]`. Simplify using `only [mul_one]`. Introduce `h0`. Rewrite `hself` using `[h0]`.

Simplify using `at hself`. Distinguish the cases in `hcu : IsCusp χ`. Use `⟨[⟨n, χ⟩], by simpa using hcu, by simp [degL], ?_⟩` and prove the remaining obligations. Establish `e : hcL [(⟨n, χ⟩ : Pc g)] n = χ`. Rewrite using `[hcL_cons]`.

Conclude with `(GlobalTheory.T.harishChandraInductionExteriorProduct_assoc_comm g n 0 0 n χ (fun _ => 1) (fun _ => 1) hcls (fun _ _ => rfl) (fun _ _ => rfl)).2.2.2`. Rewrite using `[e, hself]`. Conclude with `one_ne_zero`. Establish `hne : ∃ a, 0 < a ∧ a < n ∧ res a (n - a) χ 1 1 ≠ 0`. Assume the negation of the conclusion as `hc`.

Use `push_neg at hc`. Conclude with `hcu ⟨Nat.pos_of_ne_zero hn, hχ, fun a h1 h2 => hc a h1 h2⟩`. Take `⟨a, ha0, han, hres⟩` from `hne`. Generalize the expression as in `hb : n - a = b at hres`. Establish `hnab : n = a + b` using `by omega`.

Take `⟨R, hR, hRes⟩` from `(GlobalTheory.T.harishChandra_induction_character_restriction_decomp g a b n hnab).2 χ (irr_char hχ)`. Choose the witnesses or unpack the hypotheses as in `⟨k, hk⟩ : ∃ k, k ∈ R := by`. Break down `R with _ | ⟨k, R⟩` into its components or cases. Conclude with `absurd (by simpa using hRes 1 1) hres`. Conclude with `⟨k, by simp⟩`.

Take `⟨L₁, hL₁c, hL₁d, hL₁⟩` from `ih a han k.1 (hR k hk).1`. Take `⟨L₂, hL₂c, hL₂d, hL₂⟩` from `ih b (by omega) k.2 (hR k hk).2`. Establish `hch : ∀ p ∈ L₁ ++ L₂, IsChar p.2`. Introduce `p hp`. Break down `List.mem_append.1 hp with h | h` into its components or cases.

Use `exacts [irr_char (hL₁c p h).2.1, irr_char (hL₂c p h).2.1]`. Use `⟨L₁ ++ L₂, fun p hp => ?_, ?_, ?_⟩` and prove the remaining obligations. Break down `List.mem_append.1 hp with h | h exacts [hL₁c p h, hL₂c p h]` into its components or cases. Rewrite using `[degL_append]`. Use linear arithmetic over natural numbers and integers.

Substitute `hL₁d` using the available equality. Substitute `hL₂d` using the available equality. Establish `hc1 : IsChar (hcL L₁ (degL L₁))` using `char_hcL L₁ fun p hp => hch p (by simp [hp])`. Establish `hc2 : IsChar (hcL L₂ (degL L₂))` using `char_hcL L₂ fun p hp => hch p (by simp [hp])`. Rewrite using `[hcL_append L₁ L₂ hch n hnab]`.

Establish `e : ip χ (hc (degL L₁) (degL L₂) (hcL L₁ (degL L₁)) (hcL L₂ (degL L₂)) n) = ip (fun p : Gn g (degL L₁) × Gn g (degL L₂) => (R.map fun k => k.1 p.1 * k.2 p.2).sum) (fun p => hcL L₁ (degL L₁) p.1 * hcL L₂ (degL L₂) p.2)`. Rewrite using `[← funext fun p : Gn g (degL L₁) × Gn g (degL L₂) => hRes p.1 p.2]`. Conclude with `GlobalTheory.T.harishChandra_frobenius_reciprocity g _ _ n hnab χ (fun x y => hcL L₁ (degL L₁) x * hcL L₂ (degL L₂) y) hcls`. Rewrite using `[e, ip_prod_list]`. Take `⟨N, hN, hN0⟩` from `sum_nat_ne_zero R _ _ hR hc1 hc2`.

Rewrite using `[hN]`. Conclude with `hN0 ⟨k, hk, hL₁, hL₂⟩` after adjusting the coercions.
-/
theorem exists_cusp_list (g : ℕ) [Fact g.Prime] (n : ℕ) (χ : Gn g n → ℂ) (hχ : IsIrr χ) :
    ∃ L : List (Pc g), (∀ p ∈ L, IsCusp p.2) ∧ degL L = n ∧ ip χ (hcL L n) ≠ 0 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  have hcls : IsClass χ := char_class (irr_char hχ)
  have hself : ip χ χ = 1 := by simpa using (GlobalTheory.T.centralIdempotentOfIrrCharacter_orthogonal_central _ χ χ hχ hχ).2.2
  by_cases hn : n = 0
  · subst hn
    have hsub : ∀ x : Gn g 0, x = 1 := fun x => Units.ext (Matrix.ext fun i _ => i.elim0)
    have hu : (Finset.univ : Finset (Gn g 0)) = {1} := by ext x; simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]; exact hsub x
    have hcard : Fintype.card (Gn g 0) = 1 := by rw [← Finset.card_univ, hu]; simp
    have hc1 : ∀ f : Gn g 0 → ℂ, ip χ f = χ 1 * f 1 := by
      intro f; unfold ip; rw [hcard, hu]; simp
    refine ⟨[], by simp, rfl, ?_⟩
    rw [hcL_nil, hc1]; rw [hc1] at hself
    simp only [mul_one]; intro h0; rw [h0] at hself; simp at hself
  · by_cases hcu : IsCusp χ
    · refine ⟨[⟨n, χ⟩], by simpa using hcu, by simp [degL], ?_⟩
      have e : hcL [(⟨n, χ⟩ : Pc g)] n = χ := by
        rw [hcL_cons]
        exact (GlobalTheory.T.harishChandraInductionExteriorProduct_assoc_comm g n 0 0 n χ (fun _ => 1) (fun _ => 1) hcls (fun _ _ => rfl)
          (fun _ _ => rfl)).2.2.2
      rw [e, hself]; exact one_ne_zero
    · have hne : ∃ a, 0 < a ∧ a < n ∧ res a (n - a) χ 1 1 ≠ 0 := by
        by_contra hc; push_neg at hc
        exact hcu ⟨Nat.pos_of_ne_zero hn, hχ, fun a h1 h2 => hc a h1 h2⟩
      obtain ⟨a, ha0, han, hres⟩ := hne
      generalize hb : n - a = b at hres
      have hnab : n = a + b := by omega
      obtain ⟨R, hR, hRes⟩ := (GlobalTheory.T.harishChandra_induction_character_restriction_decomp g a b n hnab).2 χ (irr_char hχ)
      obtain ⟨k, hk⟩ : ∃ k, k ∈ R := by
        rcases R with _ | ⟨k, R⟩
        · exact absurd (by simpa using hRes 1 1) hres
        · exact ⟨k, by simp⟩
      obtain ⟨L₁, hL₁c, hL₁d, hL₁⟩ := ih a han k.1 (hR k hk).1
      obtain ⟨L₂, hL₂c, hL₂d, hL₂⟩ := ih b (by omega) k.2 (hR k hk).2
      have hch : ∀ p ∈ L₁ ++ L₂, IsChar p.2 := by
        intro p hp
        rcases List.mem_append.1 hp with h | h
        exacts [irr_char (hL₁c p h).2.1, irr_char (hL₂c p h).2.1]
      refine ⟨L₁ ++ L₂, fun p hp => ?_, ?_, ?_⟩
      · rcases List.mem_append.1 hp with h | h
        exacts [hL₁c p h, hL₂c p h]
      · rw [degL_append]; omega
      · subst hL₁d; subst hL₂d
        have hc1 : IsChar (hcL L₁ (degL L₁)) := char_hcL L₁ fun p hp => hch p (by simp [hp])
        have hc2 : IsChar (hcL L₂ (degL L₂)) := char_hcL L₂ fun p hp => hch p (by simp [hp])
        rw [hcL_append L₁ L₂ hch n hnab]
        have e : ip χ (hc (degL L₁) (degL L₂) (hcL L₁ (degL L₁)) (hcL L₂ (degL L₂)) n) =
            ip (fun p : Gn g (degL L₁) × Gn g (degL L₂) => (R.map fun k => k.1 p.1 * k.2 p.2).sum)
              (fun p => hcL L₁ (degL L₁) p.1 * hcL L₂ (degL L₂) p.2) := by
          rw [← funext fun p : Gn g (degL L₁) × Gn g (degL L₂) => hRes p.1 p.2]
          exact GlobalTheory.T.harishChandra_frobenius_reciprocity g _ _ n hnab χ (fun x y => hcL L₁ (degL L₁) x * hcL L₂ (degL L₂) y) hcls
        rw [e, ip_prod_list]
        obtain ⟨N, hN, hN0⟩ := sum_nat_ne_zero R _ _ hR hc1 hc2
        rw [hN]; exact_mod_cast hN0 ⟨k, hk, hL₁, hL₂⟩

end GlobalTheory.GLq.SuppCusp
