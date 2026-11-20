import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEqOnMirabolicFin

noncomputable section

open Matrix Topology GlobalTheory.SmGL GlobalTheory.Whittaker

namespace GlobalTheory.JSW.Cut

open GlobalTheory.JSW.KirFin

section Act

variable {G : Type} [Monoid G]

def act (T : G →₀ ℂ) (f : G → ℂ) (g : G) : ℂ :=
  T.sum fun k c => c * f (g * k)

def comp (T T' : G →₀ ℂ) : G →₀ ℂ :=
  T.sum fun a c => T'.sum fun b d => Finsupp.single (a * b) (c * d)

/- English proof (translation)
Simplify using `[act]`.
-/
@[simp] theorem act_zero (f : G → ℂ) (g : G) : act (0 : G →₀ ℂ) f g = 0 := by
  simp [act]

/- English proof (translation)
The claim follows from `Finsupp.sum_add_index' (fun _ => zero_mul _) fun _ _ _ => add_mul _ _ _`.
-/
theorem act_add (T T' : G →₀ ℂ) (f : G → ℂ) (g : G) : act (T + T') f g = act T f g + act T' f g :=
  Finsupp.sum_add_index' (fun _ => zero_mul _) fun _ _ _ => add_mul _ _ _

/- English proof (translation)
The claim follows from `Finsupp.sum_single_index (zero_mul _)`.
-/
@[simp] theorem act_single (k : G) (c : ℂ) (f : G → ℂ) (g : G) :
    act (Finsupp.single k c) f g = c * f (g * k) :=
  Finsupp.sum_single_index (zero_mul _)

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, act_add, ih]`.
-/
theorem act_finset_sum {ι : Type} (s : Finset ι) (T : ι → G →₀ ℂ) (f : G → ℂ) (g : G) :
    act (∑ i ∈ s, T i) f g = ∑ i ∈ s, act (T i) f g := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, act_add, ih]

/- English proof (translation)
The claim follows from `act_finset_sum _ _ _ _`.
-/
theorem act_finsupp_sum {α : Type} (T : α →₀ ℂ) (t : α → ℂ → G →₀ ℂ) (f : G → ℂ) (g : G) :
    act (T.sum t) f g = T.sum fun a c => act (t a c) f g :=
  act_finset_sum _ _ _ _

/- English proof (translation)
Unfold `comp`. Rewrite using `[act_finsupp_sum]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Simplify using `only`. Rewrite using `[act_finsupp_sum]`.

Unfold `act`. Rewrite using `[Finsupp.mul_sum]`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Simplify using `only`. Rewrite using `[Finsupp.sum_single_index (zero_mul _), mul_assoc, mul_assoc]`.
-/
theorem act_comp (T T' : G →₀ ℂ) (f : G → ℂ) (g : G) : act (comp T T') f g = act T (act T' f) g := by
  unfold comp
  rw [act_finsupp_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only
  rw [act_finsupp_sum]
  unfold act
  rw [Finsupp.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only
  rw [Finsupp.sum_single_index (zero_mul _), mul_assoc, mul_assoc]

/- English proof (translation)
The claim follows from `Finset.sum_congr rfl fun k hk => by simp only; rw [h k hk]`.
-/
theorem act_congr (T : G →₀ ℂ) {f f' : G → ℂ} {g : G} (h : ∀ k ∈ T.support, f (g * k) = f' (g * k)) :
    act T f g = act T f' g :=
  Finset.sum_congr rfl fun k hk => by simp only; rw [h k hk]

/- English proof (translation)
Unfold `comp Finsupp.sum at hk`. Take `⟨a, ha, hk⟩` from `Finset.mem_biUnion.1 (Finsupp.support_finset_sum hk)`. Take `⟨b, hb, hk⟩` from `Finset.mem_biUnion.1 (Finsupp.support_finset_sum hk)`. Conclude with `⟨a, ha, b, hb, Finset.mem_singleton.1 (Finsupp.support_single_subset hk)⟩`.
-/
theorem mem_support_comp {T T' : G →₀ ℂ} {k : G} (hk : k ∈ (comp T T').support) :
    ∃ a ∈ T.support, ∃ b ∈ T'.support, k = a * b := by
  classical
  unfold comp Finsupp.sum at hk
  obtain ⟨a, ha, hk⟩ := Finset.mem_biUnion.1 (Finsupp.support_finset_sum hk)
  obtain ⟨b, hb, hk⟩ := Finset.mem_biUnion.1 (Finsupp.support_finset_sum hk)
  exact ⟨a, ha, b, hb, Finset.mem_singleton.1 (Finsupp.support_single_subset hk)⟩

/- English proof (translation)
Use `⟨T.support.card, fun i => (T.support.equivFin.symm i).1, fun i => T (T.support.equivFin.symm i).1, fun i => (T.support.equivFin.symm i).2, fun f g => ?_⟩` and prove the remaining obligations. Unfold `act Finsupp.sum`. Rewrite using `[← Finset.sum_coe_sort T.support]`. Conclude with `Fintype.sum_equiv T.support.equivFin _ _ fun x => by simp`.
-/
theorem exists_fin (T : G →₀ ℂ) : ∃ (n : ℕ) (h : Fin n → G) (c : Fin n → ℂ),
    (∀ i, h i ∈ T.support) ∧ ∀ f g, act T f g = ∑ i, c i * f (g * h i) := by
  classical
  refine ⟨T.support.card, fun i => (T.support.equivFin.symm i).1, fun i => T (T.support.equivFin.symm i).1,
    fun i => (T.support.equivFin.symm i).2, fun f g => ?_⟩
  unfold act Finsupp.sum
  rw [← Finset.sum_coe_sort T.support]
  exact Fintype.sum_equiv T.support.equivFin _ _ fun x => by simp

end Act

variable {F : Type} [NormedField F]

def cell {n : ℕ} (z : GL (Fin n) F) (U : Set (GL (Fin n) F)) : Set (GL (Fin n) F) :=
  {g | ∃ u ∈ unipB F (Fin n), ∃ k ∈ U, g = u * z * k}

def Cuts (ψ : AddChar F ℂ) {n : ℕ} (U X A : Set (GL (Fin n) F)) : Prop :=
  ∃ T : GL (Fin n) F →₀ ℂ, ∀ f : GL (Fin n) F → ℂ, Eqv ψ f → (∀ u ∈ U, ∀ g, f (g * u) = f g) →
    ∀ g ∈ A, act T f g = X.indicator f g

/- English proof (translation)
Assemble the required witnesses or components as `⟨Finsupp.single 1 1, fun f _ _ g _ => by simp⟩`.
-/
example (ψ : AddChar F ℂ) {n : ℕ} (U A : Set (GL (Fin n) F)) : Cuts ψ U Set.univ A :=
  ⟨Finsupp.single 1 1, fun f _ _ g _ => by simp⟩

end GlobalTheory.JSW.Cut
