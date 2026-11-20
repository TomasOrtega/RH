import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraRestrictionCuspidalProductSumSubset
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerDimensionHarishChandraInductionMul
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraProductListIsCharacterAndPermInvari

open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq
open scoped Classical

namespace GlobalTheory.GLq.Leibniz

variable {g : ℕ} [Fact g.Prime]

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion repeatedly using the stated equalities. A detailed English derivation is pending.
-/
theorem wh_sum (ψ : AddChar (ZMod g) ℂ) {n : ℕ} {ι : Type} (s : Finset ι) (f : ι → Gn g n → ℂ) :
    wh ψ (fun x => ∑ j ∈ s, f j x) = ∑ j ∈ s, wh ψ (f j) := by
  unfold wh tr
  simp_rw [Finset.mul_sum]
  exact Finset.sum_comm

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem wh_const_mul (ψ : AddChar (ZMod g) ℂ) {n : ℕ} (c : ℂ) (f : Gn g n → ℂ) :
    wh ψ (fun x => c * f x) = c * wh ψ f := by
  unfold wh tr
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => by ring

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem wh_mul_const (ψ : AddChar (ZMod g) ℂ) {n : ℕ} (c : ℂ) (f : Gn g n → ℂ) :
    wh ψ (fun x => f x * c) = wh ψ f * c := by
  unfold wh tr
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun x _ => by ring

/- English proof (translation)
Extract witnesses or component facts from the available result. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.
-/
theorem isClass_of_isChar {G : Type} [Group G] {χ : G → ℂ} (h : IsChar χ) : IsClass χ := by
  obtain ⟨V, hV⟩ := h
  intro x y
  rw [← hV, ← hV, FDRep.char_conj]

/- English proof (translation)
Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem isChar_of_isIrr {G : Type} [Group G] {χ : G → ℂ} (h : IsIrr χ) : IsChar χ := by
  obtain ⟨V, -, hV⟩ := h
  exact ⟨V, hV⟩

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Establish an intermediate fact.

Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem wh_gl_zero (ψ : AddChar (ZMod g) ℂ) : wh ψ (fun _ : Gn g 0 => (1 : ℂ)) = 1 := by
  have hsub : ∀ x : Gn g 0, x = 1 := fun x => Units.ext (Subsingleton.elim _ _)
  have huniv : (Finset.univ : Finset (Gn g 0)) = {1} := by
    ext x
    simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
    exact hsub x
  have hP : IsUniUp ((1 : Gn g 0) : Mt g 0) := fun a _ => a.elim0
  unfold wh tr eU eDat
  rw [huniv, Finset.sum_singleton]
  rw [Finset.filter_singleton, if_pos hP, Finset.sum_singleton, Finset.card_singleton]
  simp

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem degL_sort_map (L : List (Pc g)) (I : Finset (Fin L.length)) :
    degL ((I.sort (· ≤ ·)).map L.get) = ∑ j ∈ I, (L.get j).1 := by
  unfold degL
  rw [List.map_map]
  have := Finset.sort_eq I (· ≤ ·)
  rw [Finset.sum_eq_multiset_sum, ← this, Multiset.map_coe, Multiset.sum_coe]
  rfl

/- English proof (translation)
Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem degL_eq_sum (L : List (Pc g)) : degL L = ∑ j : Fin L.length, (L.get j).1 := by
  have h := degL_sort_map L Finset.univ
  rw [Fin.sort_univ, List.map_get_finRange] at h
  exact h

/- English proof (translation)
Extract witnesses or component facts from the available result. A detailed English derivation is pending.
-/
theorem mem_of_sort_map (L : List (Pc g)) (I : Finset (Fin L.length)) {p : Pc g}
    (hp : p ∈ (I.sort (· ≤ ·)).map L.get) : p ∈ L := by
  obtain ⟨j, -, rfl⟩ := List.mem_map.1 hp
  exact List.get_mem L j

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Rewrite the conclusion repeatedly using the stated equalities. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem wh_hcL (ψ : AddChar (ZMod g) ℂ) (hψ : ψ ≠ 1) :
    ∀ L : List (Pc g), (∀ p ∈ L, IsCusp p.2 ∧ wh ψ p.2 = 1) → wh ψ (hcL L (degL L)) = 1 := by
  intro L
  induction L with
  | nil => intro _; exact wh_gl_zero ψ
  | cons p L ih =>
    intro hL
    have hp := hL p List.mem_cons_self
    have hL' : ∀ q ∈ L, IsCusp q.2 ∧ wh ψ q.2 = 1 := fun q hq => hL q (List.mem_cons_of_mem p hq)
    have hβ : IsClass (hcL L (degL L)) :=
      isClass_of_isChar (GlobalTheory.gl_list_product_perm_char g L L (degL L) rfl (fun q hq => isChar_of_isIrr (hL' q hq).1.2.1)).1
    have hα : IsClass p.2 := isClass_of_isChar (isChar_of_isIrr hp.1.2.1)
    have hdeg : degL (p :: L) = p.1 + degL L := by simp [degL]
    rw [hcL_cons]
    unfold hc
    rw [GlobalTheory.GLq.WhMul.wh_hcT g ψ hψ p.1 (degL L) (degL (p :: L)) hdeg]
    · simp_rw [wh_const_mul]
      rw [wh_mul_const, ih hL', hp.2, one_mul]
    · intro y x z
      simp only
      rw [hα]
    · intro x y z
      simp only
      rw [hβ]

/- English proof (translation)
Substitute using the available equality. A detailed English derivation is pending.
-/
theorem wh_hcL_of_deg (ψ : AddChar (ZMod g) ℂ) (hψ : ψ ≠ 1) (L : List (Pc g)) (n : ℕ) (hn : degL L = n)
    (hL : ∀ p ∈ L, IsCusp p.2 ∧ wh ψ p.2 = 1) : wh ψ (hcL L n) = 1 := by
  subst hn
  exact wh_hcL ψ hψ L hL

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Substitute using the available equality. Establish an intermediate fact.

Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem main : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ), ψ ≠ 1 → ∀ (L : List (Pc g)) (n i : ℕ),
    degL L = n → i ≤ n → (∀ p ∈ L, IsCusp p.2 ∧ wh ψ p.2 = 1) →
      wh ψ (der ψ i (hcL L n)) = (((Finset.univ : Finset (Finset (Fin L.length))).filter
        (fun I => ∑ j ∈ I, (L.get j).1 = i)).card : ℂ) ∧ wh ψ (hcL L n) = 1 := by
  intro g _ ψ hψ L n i hn hi hL
  refine ⟨?_, wh_hcL_of_deg ψ hψ L n hn hL⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hi
  have hcusp : ∀ p ∈ L, IsCusp p.2 := fun p hp => (hL p hp).1
  have htot : ∑ j : Fin L.length, (L.get j).1 = i + k := by rw [← degL_eq_sum]; exact hn
  have hsub : ∀ (I : Finset (Fin L.length)), ∀ p ∈ (I.sort (· ≤ ·)).map L.get, IsCusp p.2 ∧ wh ψ p.2 = 1 :=
    fun I p hp => hL p (mem_of_sort_map L I hp)
  have hB : ∀ I ∈ (Finset.univ : Finset (Finset (Fin L.length))).filter (fun I => ∑ j ∈ I, (L.get j).1 = i),
      wh ψ (hcL ((Iᶜ.sort (· ≤ ·)).map L.get) k) = 1 := by
    intro I hI
    rw [Finset.mem_filter] at hI
    refine wh_hcL_of_deg ψ hψ _ k ?_ (hsub Iᶜ)
    rw [degL_sort_map]
    have := Finset.sum_compl_add_sum I (fun j => (L.get j).1)
    omega
  have hA : ∀ I ∈ (Finset.univ : Finset (Finset (Fin L.length))).filter (fun I => ∑ j ∈ I, (L.get j).1 = i),
      wh ψ (hcL ((I.sort (· ≤ ·)).map L.get) i) = 1 := by
    intro I hI
    rw [Finset.mem_filter] at hI
    exact wh_hcL_of_deg ψ hψ _ i (by rw [degL_sort_map]; exact hI.2) (hsub I)
  have key : ∀ b, b = k → ∀ h : Gn g i, wh ψ (res i b (hcL L (i + k)) h) =
      ∑ I ∈ (Finset.univ : Finset (Finset (Fin L.length))).filter (fun I => ∑ j ∈ I, (L.get j).1 = i),
        hcL ((I.sort (· ≤ ·)).map L.get) i h * wh ψ (hcL ((Iᶜ.sort (· ≤ ·)).map L.get) k) := by
    intro b hb h
    subst hb
    have hr : res i b (hcL L (i + b)) h = fun y => ∑ I ∈ (Finset.univ : Finset (Finset (Fin L.length))).filter
        (fun I => ∑ j ∈ I, (L.get j).1 = i),
          hcL ((I.sort (· ≤ ·)).map L.get) i h * hcL ((Iᶜ.sort (· ≤ ·)).map L.get) b y :=
      funext fun y => GlobalTheory.GLq.ResCuspProd.main g L i b hn hcusp h y
    rw [hr, wh_sum]
    exact Finset.sum_congr rfl fun I _ => wh_const_mul ψ _ _
  have hder : der ψ i (hcL L (i + k)) = fun h =>
      ∑ I ∈ (Finset.univ : Finset (Finset (Fin L.length))).filter (fun I => ∑ j ∈ I, (L.get j).1 = i),
        hcL ((I.sort (· ≤ ·)).map L.get) i h * wh ψ (hcL ((Iᶜ.sort (· ≤ ·)).map L.get) k) :=
    funext fun h => key (i + k - i) (by omega) h
  rw [hder, wh_sum, Finset.sum_congr rfl fun I hI => by rw [wh_mul_const, hA I hI, hB I hI, one_mul]]
  simp

end GlobalTheory.GLq.Leibniz
