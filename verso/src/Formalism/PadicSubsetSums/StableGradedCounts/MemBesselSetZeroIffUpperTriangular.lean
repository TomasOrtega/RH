import Formalism.PadicSubsetSums.StableGradedCounts.LocalEstimateIVOfTypeSetWeight
import Lemmata.TwistedIdempotents.TwistedIdem

section
open Finset

namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

section GelfandTrick
variable {G : Type} [Group G] [Fintype G]

open Classical in
/- English proof (translation)
Rewrite using `[twistedIdem_def, Finset.sum_mul, Finset.smul_sum]`. Use `Fintype.sum_equiv (Equiv.mulRight v) _ _ (fun u => ?_)` and prove the remaining obligations. Simplify using `only [Equiv.coe_mulRight, smul_mul_assoc, ← map_mul, smul_smul, Subgroup.coe_mul]`. Use `congr 1`. Establish `h1 : ((χ v : ℂˣ) : ℂ) ≠ 0` using `(χ v).ne_zero`.

Establish `h2 : ((χ u : ℂˣ) : ℂ) ≠ 0` using `(χ u).ne_zero`. Rewrite using `[map_mul, mul_inv, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val]`. Clear the denominators using the available nonvanishing facts.
-/
theorem twistedIdem_mul_of (J : Subgroup G) (χ : J →* ℂˣ)
    (v : J) : twistedIdem J χ * MonoidAlgebra.of ℂ G (v : G)
      = ((χ v : ℂˣ) : ℂ) • twistedIdem J χ := by
  rw [twistedIdem_def, Finset.sum_mul, Finset.smul_sum]
  refine Fintype.sum_equiv (Equiv.mulRight v) _ _ (fun u => ?_)
  simp only [Equiv.coe_mulRight, smul_mul_assoc, ← map_mul, smul_smul, Subgroup.coe_mul]
  congr 1
  have h1 : ((χ v : ℂˣ) : ℂ) ≠ 0 := (χ v).ne_zero
  have h2 : ((χ u : ℂˣ) : ℂ) ≠ 0 := (χ u).ne_zero
  rw [map_mul, mul_inv, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val]
  field_simp

/- English proof (translation)
Rewrite using `[map_mul, map_mul]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[twistedIdem_mul_of, of_mul_twistedIdem, smul_mul_assoc, smul_mul_assoc, mul_smul_comm, smul_smul, Units.val_mul]`.
-/
theorem idem_sandwich (J : Subgroup G) (χ : J →* ℂˣ) (u u' : J) (g : G) :
    twistedIdem J χ * MonoidAlgebra.of ℂ G ((u : G) * g * u') * twistedIdem J χ =
      (((χ u * χ u' : ℂˣ)) : ℂ) •
        (twistedIdem J χ * MonoidAlgebra.of ℂ G g * twistedIdem J χ) := by
  rw [map_mul, map_mul]
  calc twistedIdem J χ * (MonoidAlgebra.of ℂ G (u : G) * MonoidAlgebra.of ℂ G g *
        MonoidAlgebra.of ℂ G (u' : G)) * twistedIdem J χ
      = (twistedIdem J χ * MonoidAlgebra.of ℂ G (u : G)) * MonoidAlgebra.of ℂ G g *
        (MonoidAlgebra.of ℂ G (u' : G) * twistedIdem J χ) := by simp only [mul_assoc]
    _ = _ := by
      rw [twistedIdem_mul_of, of_mul_twistedIdem, smul_mul_assoc, smul_mul_assoc, mul_smul_comm,
        smul_smul, Units.val_mul]

/- English proof (translation)
Establish `h1` using `idem_sandwich J χ u u' g`. Rewrite `h1` using `[h]`. Use `set X := twistedIdem J χ * MonoidAlgebra.of ℂ G g * twistedIdem J χ`. Establish `h2 : ((1 : ℂ) - ((χ u * χ u' : ℂˣ) : ℂ)) • X = 0`. Rewrite using `[sub_smul, one_smul, ← h1, sub_self]`.

Break down `smul_eq_zero.mp h2 with h3 | h3` into its components or cases. It suffices to derive a contradiction. Apply `hne` to reduce the goal to its premises. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[Units.val_one]`.

Conclude with `(sub_eq_zero.mp h3).symm`. Conclude with `h3`.
-/
theorem idem_sandwich_zero (J : Subgroup G) (χ : J →* ℂˣ) (u u' : J) (g : G)
    (h : (u : G) * g * u' = g) (hne : χ u * χ u' ≠ 1) :
    twistedIdem J χ * MonoidAlgebra.of ℂ G g * twistedIdem J χ = 0 := by
  have h1 := idem_sandwich J χ u u' g
  rw [h] at h1
  set X := twistedIdem J χ * MonoidAlgebra.of ℂ G g * twistedIdem J χ
  have h2 : ((1 : ℂ) - ((χ u * χ u' : ℂˣ) : ℂ)) • X = 0 := by
    rw [sub_smul, one_smul, ← h1, sub_self]
  rcases smul_eq_zero.mp h2 with h3 | h3
  · exfalso
    apply hne
    apply Units.ext
    rw [Units.val_one]
    exact (sub_eq_zero.mp h3).symm
  · exact h3

noncomputable def antiLift (σ : G → G) (hσ : ∀ x y, σ (x * y) = σ y * σ x) :
    MonoidAlgebra ℂ G →ₐ[ℂ] (MonoidAlgebra ℂ G)ᵐᵒᵖ :=
  MonoidAlgebra.lift ℂ _ G
    { toFun := fun g => MulOpposite.op (MonoidAlgebra.of ℂ G (σ g))
      map_one' := by
        have h1 : σ 1 = 1 := by
          have := hσ 1 1
          rw [mul_one] at this
          exact (mul_eq_left.mp this.symm)
        rw [h1, map_one, MulOpposite.op_one]
      map_mul' := by
        intro x y
        rw [hσ, map_mul, MulOpposite.op_mul] }

/- English proof (translation)
Simplify using `[antiLift]`.
-/
theorem antiLift_of (σ : G → G) (hσ : ∀ x y, σ (x * y) = σ y * σ x) (g : G) :
    antiLift σ hσ (MonoidAlgebra.of ℂ G g) = MulOpposite.op (MonoidAlgebra.of ℂ G (σ g)) := by
  simp [antiLift]

open Classical in
/- English proof (translation)
Set `s : J ≃ J` to `{ toFun := fun u => ⟨σ u, (hJ u).1⟩ invFun := fun u => ⟨σ u, (hJ u).1⟩ left_inv := fun u => Subtype.ext (hσσ u) right_inv := fun u => Subtype.ext (hσσ u) }`. Rewrite using `[twistedIdem_def, map_sum]`. Use `show _ = MulOpposite.opAddEquiv _`. Rewrite using `[map_sum]`. Use `Fintype.sum_equiv s _ _ (fun u => ?_)` and prove the remaining obligations.

Rewrite using `[map_smul, antiLift_of, MulOpposite.opAddEquiv_apply, MulOpposite.op_smul]`. Establish `: χ (s u) = χ u` using `(hJ u).2`. Rewrite using `[this]`. Both sides reduce to the same expression.
-/
theorem antiLift_idem (σ : G → G) (hσ : ∀ x y, σ (x * y) = σ y * σ x) (hσσ : ∀ x, σ (σ x) = x)
    (J : Subgroup G) (χ : J →* ℂˣ) (hJ : ∀ u : J, ∃ h : σ u ∈ J, χ ⟨σ u, h⟩ = χ u) :
    antiLift σ hσ (twistedIdem J χ) = MulOpposite.op (twistedIdem J χ) := by
  let s : J ≃ J :=
    { toFun := fun u => ⟨σ u, (hJ u).1⟩
      invFun := fun u => ⟨σ u, (hJ u).1⟩
      left_inv := fun u => Subtype.ext (hσσ u)
      right_inv := fun u => Subtype.ext (hσσ u) }
  rw [twistedIdem_def, map_sum]
  show _ = MulOpposite.opAddEquiv _
  rw [map_sum]
  refine Fintype.sum_equiv s _ _ (fun u => ?_)
  rw [map_smul, antiLift_of, MulOpposite.opAddEquiv_apply, MulOpposite.op_smul]
  have : χ (s u) = χ u := (hJ u).2
  rw [this]
  rfl

/- English proof (translation)
Establish `key : ∀ g, twistedIdem J χ * MonoidAlgebra.of ℂ G (σ g) * twistedIdem J χ = twistedIdem J χ * MonoidAlgebra.of ℂ G g * twistedIdem J χ`. Introduce `g`. Break down `H g with ⟨u, u', h1, h2⟩ | ⟨u, u', h1, h2⟩` into its components or cases. Rewrite using `[h1, idem_sandwich, h2, Units.val_one, one_smul]`. Rewrite using `[idem_sandwich_zero J χ u u' g h1 h2]`.

Take `⟨m, hm⟩` from `hJ u`. Take `⟨m', hm'⟩` from `hJ u'`. Use `idem_sandwich_zero J χ ⟨σ u', m'⟩ ⟨σ u, m⟩ (σ g) ?_ ?_` and prove the remaining obligations. Use `show σ u' * σ g * σ u = σ g`. Rewrite using `[← hσ, ← hσ, ← mul_assoc, h1]`.

Rewrite using `[hm, hm', mul_comm]`. Conclude with `h2`. Establish `fix : ∀ a, antiLift σ hσ (twistedIdem J χ * a * twistedIdem J χ) = MulOpposite.op (twistedIdem J χ * a * twistedIdem J χ)`. Introduce `a`. Proceed by induction on `a using MonoidAlgebra.induction_on with`.

Consider the case `of g`. Rewrite using `[map_mul, map_mul, antiLift_idem σ hσ hσσ J χ hJ, antiLift_of, ← MulOpposite.op_mul, ← MulOpposite.op_mul, ← mul_assoc, key]`. Consider the case `add x y hx hy => rw [mul_add, add_mul, map_add, hx, hy, MulOpposite.op_add]`. Consider the case `smul r x hx => rw [mul_smul_comm, smul_mul_assoc, map_smul, hx, MulOpposite.op_smul]`. Establish `h` using `map_mul (antiLift σ hσ) (twistedIdem J χ * MonoidAlgebra.of ℂ G g * twistedIdem J χ) (twistedIdem J χ * MonoidAlgebra.of ℂ G g' * twistedIdem J χ)`.

Rewrite `h` using `[fix, fix, ← MulOpposite.op_mul]`. Establish `h' : (twistedIdem J χ * MonoidAlgebra.of ℂ G g * twistedIdem J χ) * (twistedIdem J χ * MonoidAlgebra.of ℂ G g' * twistedIdem J χ) = twistedIdem J χ * (MonoidAlgebra.of ℂ G g * twistedIdem J χ * twistedIdem J χ * MonoidAlgebra.of ℂ G g') * twistedIdem J χ` using `by simp only [mul_assoc]`. Rewrite `h` using `[h', fix, ← h']`. Conclude with `MulOpposite.op_injective h`.
-/
theorem hecke_comm (σ : G → G) (hσ : ∀ x y, σ (x * y) = σ y * σ x) (hσσ : ∀ x, σ (σ x) = x)
    (J : Subgroup G) (χ : J →* ℂˣ) (hJ : ∀ u : J, ∃ h : σ u ∈ J, χ ⟨σ u, h⟩ = χ u)
    (H : ∀ g, (∃ u u' : J, σ g = u * g * u' ∧ χ u * χ u' = 1) ∨
      (∃ u u' : J, (u : G) * g * u' = g ∧ χ u * χ u' ≠ 1)) (g g' : G) :
    (twistedIdem J χ * MonoidAlgebra.of ℂ G g * twistedIdem J χ) *
        (twistedIdem J χ * MonoidAlgebra.of ℂ G g' * twistedIdem J χ) =
      (twistedIdem J χ * MonoidAlgebra.of ℂ G g' * twistedIdem J χ) *
        (twistedIdem J χ * MonoidAlgebra.of ℂ G g * twistedIdem J χ) := by
  have key : ∀ g, twistedIdem J χ * MonoidAlgebra.of ℂ G (σ g) * twistedIdem J χ =
      twistedIdem J χ * MonoidAlgebra.of ℂ G g * twistedIdem J χ := by
    intro g
    rcases H g with ⟨u, u', h1, h2⟩ | ⟨u, u', h1, h2⟩
    · rw [h1, idem_sandwich, h2, Units.val_one, one_smul]
    · rw [idem_sandwich_zero J χ u u' g h1 h2]
      obtain ⟨m, hm⟩ := hJ u
      obtain ⟨m', hm'⟩ := hJ u'
      refine idem_sandwich_zero J χ ⟨σ u', m'⟩ ⟨σ u, m⟩ (σ g) ?_ ?_
      · show σ u' * σ g * σ u = σ g
        rw [← hσ, ← hσ, ← mul_assoc, h1]
      · rw [hm, hm', mul_comm]; exact h2
  have fix : ∀ a, antiLift σ hσ (twistedIdem J χ * a * twistedIdem J χ) =
      MulOpposite.op (twistedIdem J χ * a * twistedIdem J χ) := by
    intro a
    induction a using MonoidAlgebra.induction_on with
    | of g =>
      rw [map_mul, map_mul, antiLift_idem σ hσ hσσ J χ hJ, antiLift_of, ← MulOpposite.op_mul,
        ← MulOpposite.op_mul, ← mul_assoc, key]
    | add x y hx hy => rw [mul_add, add_mul, map_add, hx, hy, MulOpposite.op_add]
    | smul r x hx => rw [mul_smul_comm, smul_mul_assoc, map_smul, hx, MulOpposite.op_smul]
  have h := map_mul (antiLift σ hσ) (twistedIdem J χ * MonoidAlgebra.of ℂ G g * twistedIdem J χ)
    (twistedIdem J χ * MonoidAlgebra.of ℂ G g' * twistedIdem J χ)
  rw [fix, fix, ← MulOpposite.op_mul] at h
  have h' : (twistedIdem J χ * MonoidAlgebra.of ℂ G g * twistedIdem J χ) *
      (twistedIdem J χ * MonoidAlgebra.of ℂ G g' * twistedIdem J χ) =
      twistedIdem J χ * (MonoidAlgebra.of ℂ G g * twistedIdem J χ * twistedIdem J χ *
        MonoidAlgebra.of ℂ G g') * twistedIdem J χ := by simp only [mul_assoc]
  rw [h', fix, ← h'] at h
  exact MulOpposite.op_injective h

/- English proof (translation)
Apply the tactic sequence `first | exact Bl.CyclicComponents.goal1 .. | (apply Bl.CyclicComponents.goal1 <;> assumption) | (intros; apply Bl.CyclicComponents.goal1 <;> assumption) | (apply @Bl.CyclicComponents.goal1 <;> assumption) | (intros; apply @Bl.CyclicComponents.goal1 <;> assumption) | (apply @Bl.Cy …`.
-/
theorem gelfand_trick {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (J : Subgroup G) (χ : J →* ℂˣ)
    (hcomm : ∀ g g' : G, (twistedIdem J χ * MonoidAlgebra.of ℂ G g * twistedIdem J χ) *
        (twistedIdem J χ * MonoidAlgebra.of ℂ G g' * twistedIdem J χ) =
      (twistedIdem J χ * MonoidAlgebra.of ℂ G g' * twistedIdem J χ) *
        (twistedIdem J χ * MonoidAlgebra.of ℂ G g * twistedIdem J χ))
    (hirr : IsIrr ρ) :
    Module.finrank ℂ (eqvSpace ρ (fun u : J => (u : G)) (fun u => ((χ u : ℂˣ) : ℂ))) ≤ 1 := by
  first | exact Bl.CyclicComponents.goal1 .. | (apply Bl.CyclicComponents.goal1 <;> assumption) | (intros; apply Bl.CyclicComponents.goal1 <;> assumption) | (apply @Bl.CyclicComponents.goal1 <;> assumption) | (intros; apply @Bl.CyclicComponents.goal1 <;> assumption) | (apply @Bl.CyclicComponents.goal1 <;> first | assumption | infer_instance)

end GelfandTrick

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end

section
open Finset Matrix

namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

section GG
variable {K : Type} [Field K] {N : ℕ}

def IsUT (A : Matrix (Fin N) (Fin N) K) : Prop :=
  (∀ i, A i i = 1) ∧ ∀ i j, j < i → A i j = 0

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2, -⟩`. Conclude with `⟨h1, h2⟩`. Introduce and unpack `⟨h1, h2⟩`. Use `⟨h1, h2, ?_⟩` and prove the remaining obligations.

Introduce `i j _ h`. Use linear arithmetic over natural numbers and integers.
-/
theorem mem_besselSet_zero_iff_upper_triangular (u : GL (Fin N) K) : u ∈ besselSet K 0 0 N ↔ IsUT (u : Matrix (Fin N) (Fin N) K) := by
  constructor
  · rintro ⟨h1, h2, -⟩
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, h2, ?_⟩
    intro i j _ h
    omega

/- English proof (translation)
Rewrite using `[Matrix.det_of_upperTriangular (fun i j hij => h.2 i j hij)]`. Conclude with `Finset.prod_eq_one fun i _ => h.1 i`.
-/
theorem IsUT.det {A : Matrix (Fin N) (Fin N) K} (h : IsUT A) : A.det = 1 := by
  rw [Matrix.det_of_upperTriangular (fun i j hij => h.2 i j hij)]
  exact Finset.prod_eq_one fun i _ => h.1 i

noncomputable def utMk (A : Matrix (Fin N) (Fin N) K) (h : IsUT A) : GL (Fin N) K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero A (by rw [h.det]; exact one_ne_zero)

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem utMk_val (A : Matrix (Fin N) (Fin N) K) (h : IsUT A) :
    ((utMk A h : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) = A := rfl

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun i => Matrix.one_apply_eq i, fun i j h => Matrix.one_apply_ne (ne_of_gt h)⟩`.
-/
theorem IsUT.one : IsUT (1 : Matrix (Fin N) (Fin N) K) :=
  ⟨fun i => Matrix.one_apply_eq i, fun i j h => Matrix.one_apply_ne (ne_of_gt h)⟩

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `i`. Rewrite using `[Matrix.mul_apply, Finset.sum_eq_single i, hA.1, hB.1, one_mul]`. Introduce `m _ hm`. Break down `lt_or_gt_of_ne hm with h | h` into its components or cases.

Rewrite using `[hA.2 i m h, zero_mul]`. Rewrite using `[hB.2 m i h, mul_zero]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`. Introduce `i j hij`.

Rewrite using `[Matrix.mul_apply]`. Use `Finset.sum_eq_zero fun m _ => ?_` and prove the remaining obligations. Break down `lt_or_ge m i with h | h` into its components or cases. Rewrite using `[hA.2 i m h, zero_mul]`. Rewrite using `[hB.2 m j (lt_of_lt_of_le hij h), mul_zero]`.
-/
theorem IsUT.mul {A B : Matrix (Fin N) (Fin N) K} (hA : IsUT A) (hB : IsUT B) : IsUT (A * B) := by
  constructor
  · intro i
    rw [Matrix.mul_apply, Finset.sum_eq_single i, hA.1, hB.1, one_mul]
    · intro m _ hm
      rcases lt_or_gt_of_ne hm with h | h
      · rw [hA.2 i m h, zero_mul]
      · rw [hB.2 m i h, mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro i j hij
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun m _ => ?_
    rcases lt_or_ge m i with h | h
    · rw [hA.2 i m h, zero_mul]
    · rw [hB.2 m j (lt_of_lt_of_le hij h), mul_zero]

def edgeSum (A : Matrix (Fin N) (Fin N) K) : K :=
  ∑ i : Fin N, ∑ j : Fin N, if (j : ℕ) = i + 1 then A i j else 0

/- English proof (translation)
Unfold `besselChar edgeSum`. Use `congr 1`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Establish `: besselEdge 0 0 i j ↔ (j : ℕ) = i + 1`. Unfold `besselEdge`.

Use linear arithmetic over natural numbers and integers. Simplify using `only [this]`.
-/
theorem besselChar_zero_eq_edge_sum (ψ₀ : AddChar K ℂ) (u : GL (Fin N) K) :
    besselChar ψ₀ 0 0 N u = ψ₀ (edgeSum (u : Matrix (Fin N) (Fin N) K)) := by
  unfold besselChar edgeSum
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have : besselEdge 0 0 i j ↔ (j : ℕ) = i + 1 := by
    unfold besselEdge
    omega
  simp only [this]

/- English proof (translation)
Unfold `edgeSum`. Rewrite using `[← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Use `split_ifs with h`. Establish `hij : i ≠ j`. Introduce `h'`. Rewrite `h` using `[h']`. Use linear arithmetic over natural numbers and integers.

Rewrite using `[Matrix.mul_apply, ← Finset.add_sum_erase _ _ (Finset.mem_univ i), ← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩), hA.1, hB.1, one_mul, mul_one, Finset.sum_eq_zero, add_zero, add_comm]`. Introduce `m hm`. Simplify using `only [Finset.mem_erase, Finset.mem_univ, and_true] at hm`. Break down `lt_or_ge m i with h1 | h1` into its components or cases. Rewrite using `[hA.2 i m h1, zero_mul]`.

Establish `: j < m`. Establish `h2 : (m : ℕ) ≠ i` using `fun h' => hm.2 (Fin.ext h')`. Establish `h3 : (m : ℕ) ≠ j` using `fun h' => hm.1 (Fin.ext h')`. Establish `h4 : (i : ℕ) ≤ m` using `h1`. Use `show (j : ℕ) < m`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[hB.2 m j this, mul_zero]`. Rewrite using `[add_zero]`.
-/
theorem edgeSum_mul {A B : Matrix (Fin N) (Fin N) K} (hA : IsUT A) (hB : IsUT B) :
    edgeSum (A * B) = edgeSum A + edgeSum B := by
  unfold edgeSum
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs with h
  · have hij : i ≠ j := by
      intro h'; rw [h'] at h; omega
    rw [Matrix.mul_apply, ← Finset.add_sum_erase _ _ (Finset.mem_univ i),
      ← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩),
      hA.1, hB.1, one_mul, mul_one, Finset.sum_eq_zero, add_zero, add_comm]
    intro m hm
    simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hm
    rcases lt_or_ge m i with h1 | h1
    · rw [hA.2 i m h1, zero_mul]
    · have : j < m := by
        have h2 : (m : ℕ) ≠ i := fun h' => hm.2 (Fin.ext h')
        have h3 : (m : ℕ) ≠ j := fun h' => hm.1 (Fin.ext h')
        have h4 : (i : ℕ) ≤ m := h1
        show (j : ℕ) < m
        omega
      rw [hB.2 m j this, mul_zero]
  · rw [add_zero]

/- English proof (translation)
Establish `hlow : ∀ i j, j < i → ((u⁻¹ : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) i j = 0`. Introduce `i j hij`. Rewrite using `[Matrix.coe_units_inv]`. Establish `: Invertible (u : Matrix (Fin N) (Fin N) K)` using `u.invertible`. Establish `hb : Matrix.BlockTriangular (u : Matrix (Fin N) (Fin N) K) id` using `fun i j hij => h.2 i j hij`.

Conclude with `Matrix.blockTriangular_inv_of_blockTriangular hb hij`. Use `⟨fun i => ?_, hlow⟩` and prove the remaining obligations. Establish `h1 : ((u * u⁻¹ : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) i i = 1`. Rewrite using `[mul_inv_cancel]`. Simplify using the standard rewrite rules.

Rewrite `h1` using `[Units.val_mul, Matrix.mul_apply, Finset.sum_eq_single i, h.1, one_mul]`. Conclude with `h1`. Introduce `m _ hm`. Break down `lt_or_gt_of_ne hm with h' | h'` into its components or cases. Rewrite using `[h.2 i m h', zero_mul]`.

Rewrite using `[hlow m i h', mul_zero]`. Introduce `h'`. Conclude with `absurd (Finset.mem_univ _) h'`.
-/
theorem IsUT.inv_val (u : GL (Fin N) K) (h : IsUT (u : Matrix (Fin N) (Fin N) K)) :
    IsUT ((u⁻¹ : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) := by
  have hlow : ∀ i j, j < i → ((u⁻¹ : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) i j = 0 := by
    intro i j hij
    rw [Matrix.coe_units_inv]
    have : Invertible (u : Matrix (Fin N) (Fin N) K) := u.invertible
    have hb : Matrix.BlockTriangular (u : Matrix (Fin N) (Fin N) K) id := fun i j hij => h.2 i j hij
    exact Matrix.blockTriangular_inv_of_blockTriangular hb hij
  refine ⟨fun i => ?_, hlow⟩
  have h1 : ((u * u⁻¹ : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) i i = 1 := by
    rw [mul_inv_cancel]; simp
  rw [Units.val_mul, Matrix.mul_apply, Finset.sum_eq_single i, h.1, one_mul] at h1
  · exact h1
  · intro m _ hm
    rcases lt_or_gt_of_ne hm with h' | h'
    · rw [h.2 i m h', zero_mul]
    · rw [hlow m i h', mul_zero]
  · intro h'; exact absurd (Finset.mem_univ _) h'

def uniSub (K : Type) [Field K] (N : ℕ) : Subgroup (GL (Fin N) K) where
  carrier := {u | IsUT (u : Matrix (Fin N) (Fin N) K)}
  mul_mem' := fun {a b} ha hb => by
    show IsUT ((a * b : GL (Fin N) K) : Matrix (Fin N) (Fin N) K)
    rw [Units.val_mul]; exact IsUT.mul ha hb
  one_mem' := by
    show IsUT ((1 : GL (Fin N) K) : Matrix (Fin N) (Fin N) K)
    rw [Units.val_one]; exact IsUT.one
  inv_mem' := fun {a} ha => IsUT.inv_val a ha

noncomputable def uniChar (ψ₀ : AddChar K ℂ) (N : ℕ) : uniSub K N →* ℂˣ where
  toFun u := (ψ₀.toMonoidHom.toHomUnits) (Multiplicative.ofAdd (edgeSum ((u : GL (Fin N) K) : Matrix (Fin N) (Fin N) K)))
  map_one' := by
    have : edgeSum (((1 : uniSub K N) : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) = 0 := by
      have h := edgeSum_mul (K := K) (N := N) IsUT.one IsUT.one
      rw [mul_one] at h
      simpa using h
    rw [this]; simp
  map_mul' := fun a b => by
    have : edgeSum (((a * b : uniSub K N) : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) =
        edgeSum ((a : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) +
          edgeSum ((b : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) := by
      rw [Subgroup.coe_mul, Units.val_mul]
      exact edgeSum_mul a.2 b.2
    rw [this, ofAdd_add, map_mul]

/- English proof (translation)
Simplify using `[uniChar]`.
-/
theorem uniChar_val (ψ₀ : AddChar K ℂ) (u : uniSub K N) :
    ((uniChar ψ₀ N u : ℂˣ) : ℂ) = ψ₀ (edgeSum ((u : GL (Fin N) K) : Matrix (Fin N) (Fin N) K)) := by
  simp [uniChar]

/- English proof (translation)
Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce `h u`. Use `h ⟨u.1, (mem_besselSet_zero_iff_upper_triangular _).mpr u.2⟩` as an intermediate fact. Use `show ρ (u : GL (Fin N) K) x = ((uniChar ψ₀ N u : ℂˣ) : ℂ) • x`.

Rewrite using `[uniChar_val, ← besselChar_zero_eq_edge_sum]`. Conclude with `this`. Introduce `h u`. Establish `: ρ (u : GL (Fin N) K) x = ((uniChar ψ₀ N ⟨u.1, (mem_besselSet_zero_iff_upper_triangular _).mp u.2⟩ : ℂˣ) : ℂ) • x` using `h ⟨u.1, (mem_besselSet_zero_iff_upper_triangular _).mp u.2⟩`. Rewrite `this` using `[uniChar_val, ← besselChar_zero_eq_edge_sum]`.

Conclude with `this`.
-/
theorem besselSpace_zero_eq_equivariant {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GL (Fin N) K) V) (ψ₀ : AddChar K ℂ) :
    besselSpace ρ ψ₀ 0 0 = eqvSpace ρ (fun u : uniSub K N => (u : GL (Fin N) K))
      (fun u => ((uniChar ψ₀ N u : ℂˣ) : ℂ)) := by
  ext x
  constructor
  · intro h u
    have := h ⟨u.1, (mem_besselSet_zero_iff_upper_triangular _).mpr u.2⟩
    show ρ (u : GL (Fin N) K) x = ((uniChar ψ₀ N u : ℂˣ) : ℂ) • x
    rw [uniChar_val, ← besselChar_zero_eq_edge_sum]
    exact this
  · intro h u
    have : ρ (u : GL (Fin N) K) x =
        ((uniChar ψ₀ N ⟨u.1, (mem_besselSet_zero_iff_upper_triangular _).mp u.2⟩ : ℂˣ) : ℂ) • x :=
      h ⟨u.1, (mem_besselSet_zero_iff_upper_triangular _).mp u.2⟩
    rw [uniChar_val, ← besselChar_zero_eq_edge_sum] at this
    exact this

end GG
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end

section
open Finset

namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

section Comb
variable {N : ℕ}

/- English proof (translation)
Introduce `d`. Proceed by induction on `d with`. Consider the case `zero`. Introduce `i j hj hlt`. Establish `: j = i` using `Fin.ext (by omega)`.

Rewrite `hlt` using `[this]`. Conclude with `absurd hlt (lt_irrefl _)`. Consider the case `succ d ih`. Introduce `i j hj hlt m him hmj`. Establish `hi' : (i : ℕ) + 1 < N` using `by have := j.2; omega`.

Use `set i' : Fin N := ⟨i + 1, hi'⟩ with hi'def`. Establish `hi'v : (i' : ℕ) = i + 1` using `rfl`. Establish `hne : τ i' ≠ τ i`. Introduce `h'`. Use `τ.injective h'` as an intermediate fact.

Use `congrArg Fin.val this` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hlt' : (τ j : ℕ) < τ i` using `hlt`. Establish `him' : (i : ℕ) ≤ m` using `him`. Establish `hmj' : (m : ℕ) ≤ j` using `hmj`.

Distinguish the cases in `hmi : m = i`. Rewrite using `[hmi]`. Establish `hmi' : (m : ℕ) ≠ i` using `fun h' => hmi (Fin.ext h')`. Break down `lt_or_gt_of_ne hne with h1 | h1` into its components or cases. Establish `h2` using `h i i' hi'v h1`.

Distinguish the cases in `hji : j = i'`. Establish `: m = i'` using `Fin.ext (by rw [hji] at hmj'; omega)`. Rewrite using `[this]`. Use linear arithmetic over natural numbers and integers. Establish `h3 : τ j ≠ τ i'` using `fun h' => hji (τ.injective h')`.

Establish `h3' : (τ j : ℕ) ≠ τ i'` using `fun h' => h3 (Fin.ext h')`. Establish `h4 : τ j < τ i'` using `by show (τ j : ℕ) < τ i'`. Use linear arithmetic over natural numbers and integers. Use `ih i' j (by omega) h4 m (by show (i' : ℕ) ≤ m; omega) hmj` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

It suffices to derive a contradiction. Establish `h1' : (τ i : ℕ) < τ i'` using `h1`. Establish `h4 : τ j < τ i'` using `lt_trans hlt h1`. Establish `hall` using `ih i' j (by omega) h4`. Establish `hjj` using `hall j (by show (i' : ℕ) ≤ j; omega) le_rfl`.

Establish `hm0 : (i' : ℕ) + ((τ i' : ℕ) - τ i) < N` using `by have := j.2; omega`. Use `set m0 : Fin N := ⟨i' + ((τ i' : ℕ) - τ i), hm0⟩ with hm0def`. Establish `hm0v : (m0 : ℕ) = i' + ((τ i' : ℕ) - τ i)` using `rfl`. Use `hall m0 (by show (i' : ℕ) ≤ m0; omega) (by show (m0 : ℕ) ≤ j; omega)` as an intermediate fact. Establish `h5 : τ m0 = τ i` using `Fin.ext (by omega)`.

Establish `h6` using `congrArg Fin.val (τ.injective h5)`. Use linear arithmetic over natural numbers and integers.
-/
theorem desc_run (τ : Equiv.Perm (Fin N))
    (h : ∀ i j : Fin N, (j : ℕ) = i + 1 → τ j < τ i → (τ i : ℕ) = τ j + 1) :
    ∀ d : ℕ, ∀ i j : Fin N, (j : ℕ) = i + d → τ j < τ i → ∀ m : Fin N, i ≤ m → m ≤ j →
      (τ m : ℕ) + m = τ i + i := by
  intro d
  induction d with
  | zero =>
    intro i j hj hlt
    have : j = i := Fin.ext (by omega)
    rw [this] at hlt
    exact absurd hlt (lt_irrefl _)
  | succ d ih =>
    intro i j hj hlt m him hmj
    have hi' : (i : ℕ) + 1 < N := by have := j.2; omega
    set i' : Fin N := ⟨i + 1, hi'⟩ with hi'def
    have hi'v : (i' : ℕ) = i + 1 := rfl
    have hne : τ i' ≠ τ i := by
      intro h'
      have := τ.injective h'
      have := congrArg Fin.val this
      omega
    have hlt' : (τ j : ℕ) < τ i := hlt
    have him' : (i : ℕ) ≤ m := him
    have hmj' : (m : ℕ) ≤ j := hmj
    by_cases hmi : m = i
    · rw [hmi]
    have hmi' : (m : ℕ) ≠ i := fun h' => hmi (Fin.ext h')
    rcases lt_or_gt_of_ne hne with h1 | h1
    · have h2 := h i i' hi'v h1
      by_cases hji : j = i'
      · have : m = i' := Fin.ext (by rw [hji] at hmj'; omega)
        rw [this]; omega
      · have h3 : τ j ≠ τ i' := fun h' => hji (τ.injective h')
        have h3' : (τ j : ℕ) ≠ τ i' := fun h' => h3 (Fin.ext h')
        have h4 : τ j < τ i' := by
          show (τ j : ℕ) < τ i'
          omega
        have := ih i' j (by omega) h4 m (by show (i' : ℕ) ≤ m; omega) hmj
        omega
    · exfalso
      have h1' : (τ i : ℕ) < τ i' := h1
      have h4 : τ j < τ i' := lt_trans hlt h1
      have hall := ih i' j (by omega) h4
      have hjj := hall j (by show (i' : ℕ) ≤ j; omega) le_rfl
      have hm0 : (i' : ℕ) + ((τ i' : ℕ) - τ i) < N := by have := j.2; omega
      set m0 : Fin N := ⟨i' + ((τ i' : ℕ) - τ i), hm0⟩ with hm0def
      have hm0v : (m0 : ℕ) = i' + ((τ i' : ℕ) - τ i) := rfl
      have := hall m0 (by show (i' : ℕ) ≤ m0; omega) (by show (m0 : ℕ) ≤ j; omega)
      have h5 : τ m0 = τ i := Fin.ext (by omega)
      have h6 := congrArg Fin.val (τ.injective h5)
      omega

/- English proof (translation)
Establish `run` using `desc_run τ h`. Establish `run' : ∀ i j : Fin N, i < j → τ j < τ i → ∀ m : Fin N, i ≤ m → m ≤ j → (τ m : ℕ) + m = τ i + i`. Introduce `i j hij`. Establish `hij' : (i : ℕ) < j` using `hij`. Conclude with `run (j - i) i j (by omega)`.

Take `⟨j0, hj0⟩` from `τ.surjective i`. Break down `lt_trichotomy (τ i) i with hc | hc | hc` into its components or cases. Establish `hne : j0 ≠ i`. Introduce `h'`. Rewrite `hj0` using `[h']`.

Rewrite `hc` using `[hj0]`. Conclude with `lt_irrefl _ hc`. Break down `lt_or_gt_of_ne hne with h1 | h1` into its components or cases. Use `run' j0 i h1 (by rw [hj0]; exact hc) i h1.le le_rfl` as an intermediate fact. Rewrite `this` using `[hj0]`.

Establish `h2 : τ i = j0` using `Fin.ext (by omega)`. Rewrite using `[h2, hj0]`. It suffices to derive a contradiction. Establish `hp : ∃ p, p < i ∧ i < τ p`. Assume the negation of the conclusion as `hcon`.

Use `push_neg at hcon`. Establish `hmaps : ∀ p ∈ Finset.Iio i, τ p ∈ (Finset.Iio i).erase (τ i)`. Introduce `p hp`. Establish `hp' : p < i` using `Finset.mem_Iio.mp hp`. Use `Finset.mem_erase.mpr ⟨fun h' => (ne_of_lt hp') (τ.injective h'), ?_⟩` and prove the remaining obligations.

Use `Finset.mem_Iio.mpr (lt_of_le_of_ne (hcon p hp') ?_)` and prove the remaining obligations. Introduce `h'`. Rewrite `h'` using `[← hj0]`. Use `τ.injective h'` as an intermediate fact. Rewrite `hp'` using `[this]`.

Conclude with `lt_asymm hp' h1`. Establish `hcard` using `Finset.card_le_card_of_injOn τ hmaps (τ.injective.injOn)`. Rewrite `hcard` using `[Finset.card_erase_of_mem (Finset.mem_Iio.mpr hc)]`. Establish `: 0 < (Finset.Iio i).card` using `Finset.card_pos.mpr ⟨_, Finset.mem_Iio.mpr hc⟩`. Use linear arithmetic over natural numbers and integers.

Take `⟨p, hp1, hp2⟩` from `hp`. Establish `hr` using `run' p j0 (lt_trans hp1 h1) (by rw [hj0]; exact hp2)`. Establish `e1` using `hr i hp1.le h1.le`. Establish `e2` using `hr j0 (lt_trans hp1 h1).le le_rfl`. Rewrite `e2` using `[hj0]`.

Establish `hc' : (τ i : ℕ) < i` using `hc`. Establish `h1' : (i : ℕ) < j0` using `h1`. Use linear arithmetic over natural numbers and integers. Rewrite using `[hc, hc]`. Establish `hne : j0 ≠ i`.

Introduce `h'`. Rewrite `hj0` using `[h']`. Rewrite `hc` using `[hj0]`. Conclude with `lt_irrefl _ hc`. Break down `lt_or_gt_of_ne hne with h1 | h1` into its components or cases.

It suffices to derive a contradiction. Establish `hp : ∃ p, i < p ∧ τ p < i`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Establish `hmaps : ∀ p ∈ Finset.Ioi i, τ p ∈ (Finset.Ioi i).erase (τ i)`.

Introduce `p hp`. Establish `hp' : i < p` using `Finset.mem_Ioi.mp hp`. Use `Finset.mem_erase.mpr ⟨fun h' => (ne_of_gt hp') (τ.injective h'), ?_⟩` and prove the remaining obligations. Use `Finset.mem_Ioi.mpr (lt_of_le_of_ne (hcon p hp') ?_)` and prove the remaining obligations. Introduce `h'`.

Rewrite `h'` using `[← hj0]`. Use `τ.injective h'` as an intermediate fact. Rewrite `hp'` using `[← this]`. Conclude with `lt_asymm hp' h1`. Establish `hcard` using `Finset.card_le_card_of_injOn τ hmaps (τ.injective.injOn)`.

Rewrite `hcard` using `[Finset.card_erase_of_mem (Finset.mem_Ioi.mpr hc)]`. Establish `: 0 < (Finset.Ioi i).card` using `Finset.card_pos.mpr ⟨_, Finset.mem_Ioi.mpr hc⟩`. Use linear arithmetic over natural numbers and integers. Take `⟨p, hp1, hp2⟩` from `hp`. Establish `hr` using `run' j0 p (lt_trans h1 hp1) (by rw [hj0]; exact hp2)`.

Establish `e1` using `hr i h1.le hp1.le`. Rewrite `e1` using `[hj0]`. Establish `hc' : (i : ℕ) < τ i` using `hc`. Establish `h1' : (j0 : ℕ) < i` using `h1`. Use linear arithmetic over natural numbers and integers.

Use `run' i j0 h1 (by rw [hj0]; exact hc) j0 h1.le le_rfl` as an intermediate fact. Rewrite `this` using `[hj0]`. Establish `h2 : τ i = j0` using `Fin.ext (by omega)`. Rewrite using `[h2, hj0]`.
-/
theorem desc_invol (τ : Equiv.Perm (Fin N))
    (h : ∀ i j : Fin N, (j : ℕ) = i + 1 → τ j < τ i → (τ i : ℕ) = τ j + 1) (i : Fin N) :
    τ (τ i) = i := by
  have run := desc_run τ h
  have run' : ∀ i j : Fin N, i < j → τ j < τ i → ∀ m : Fin N, i ≤ m → m ≤ j →
      (τ m : ℕ) + m = τ i + i := by
    intro i j hij
    have hij' : (i : ℕ) < j := hij
    exact run (j - i) i j (by omega)
  obtain ⟨j0, hj0⟩ := τ.surjective i
  rcases lt_trichotomy (τ i) i with hc | hc | hc
  · have hne : j0 ≠ i := by
      intro h'; rw [h'] at hj0; rw [hj0] at hc; exact lt_irrefl _ hc
    rcases lt_or_gt_of_ne hne with h1 | h1
    · have := run' j0 i h1 (by rw [hj0]; exact hc) i h1.le le_rfl
      rw [hj0] at this
      have h2 : τ i = j0 := Fin.ext (by omega)
      rw [h2, hj0]
    · exfalso
      have hp : ∃ p, p < i ∧ i < τ p := by
        by_contra hcon
        push_neg at hcon
        have hmaps : ∀ p ∈ Finset.Iio i, τ p ∈ (Finset.Iio i).erase (τ i) := by
          intro p hp
          have hp' : p < i := Finset.mem_Iio.mp hp
          refine Finset.mem_erase.mpr ⟨fun h' => (ne_of_lt hp') (τ.injective h'), ?_⟩
          refine Finset.mem_Iio.mpr (lt_of_le_of_ne (hcon p hp') ?_)
          intro h'
          rw [← hj0] at h'
          have := τ.injective h'
          rw [this] at hp'
          exact lt_asymm hp' h1
        have hcard := Finset.card_le_card_of_injOn τ hmaps (τ.injective.injOn)
        rw [Finset.card_erase_of_mem (Finset.mem_Iio.mpr hc)] at hcard
        have : 0 < (Finset.Iio i).card := Finset.card_pos.mpr ⟨_, Finset.mem_Iio.mpr hc⟩
        omega
      obtain ⟨p, hp1, hp2⟩ := hp
      have hr := run' p j0 (lt_trans hp1 h1) (by rw [hj0]; exact hp2)
      have e1 := hr i hp1.le h1.le
      have e2 := hr j0 (lt_trans hp1 h1).le le_rfl
      rw [hj0] at e2
      have hc' : (τ i : ℕ) < i := hc
      have h1' : (i : ℕ) < j0 := h1
      omega
  · rw [hc, hc]
  · have hne : j0 ≠ i := by
      intro h'; rw [h'] at hj0; rw [hj0] at hc; exact lt_irrefl _ hc
    rcases lt_or_gt_of_ne hne with h1 | h1
    · exfalso
      have hp : ∃ p, i < p ∧ τ p < i := by
        by_contra hcon
        push_neg at hcon
        have hmaps : ∀ p ∈ Finset.Ioi i, τ p ∈ (Finset.Ioi i).erase (τ i) := by
          intro p hp
          have hp' : i < p := Finset.mem_Ioi.mp hp
          refine Finset.mem_erase.mpr ⟨fun h' => (ne_of_gt hp') (τ.injective h'), ?_⟩
          refine Finset.mem_Ioi.mpr (lt_of_le_of_ne (hcon p hp') ?_)
          intro h'
          rw [← hj0] at h'
          have := τ.injective h'
          rw [← this] at hp'
          exact lt_asymm hp' h1
        have hcard := Finset.card_le_card_of_injOn τ hmaps (τ.injective.injOn)
        rw [Finset.card_erase_of_mem (Finset.mem_Ioi.mpr hc)] at hcard
        have : 0 < (Finset.Ioi i).card := Finset.card_pos.mpr ⟨_, Finset.mem_Ioi.mpr hc⟩
        omega
      obtain ⟨p, hp1, hp2⟩ := hp
      have hr := run' j0 p (lt_trans h1 hp1) (by rw [hj0]; exact hp2)
      have e1 := hr i h1.le hp1.le
      rw [hj0] at e1
      have hc' : (i : ℕ) < τ i := hc
      have h1' : (j0 : ℕ) < i := h1
      omega
    · have := run' i j0 h1 (by rw [hj0]; exact hc) j0 h1.le le_rfl
      rw [hj0] at this
      have h2 : τ i = j0 := Fin.ext (by omega)
      rw [h2, hj0]

/- English proof (translation)
Establish `inv` using `desc_invol τ h`. Establish `main : ∀ i : Fin N, i < τ i → t (τ i) = t i`. Introduce `i hi`. Establish `hi' : (i : ℕ) < τ i` using `hi`. Establish `hr` using `desc_run τ h ((τ i : ℕ) - i) i (τ i) (by omega) (by rw [inv]; exact hi)`.

Establish `step : ∀ d : ℕ, ∀ m : Fin N, (m : ℕ) = i + d → m ≤ τ i → t m = t i`. Introduce `d`. Proceed by induction on `d with`. Consider the case `zero => intro m hm _; rw [show m = i from Fin.ext (by omega)]`. Consider the case `succ d ih`.

Introduce `m hm hle`. Establish `hle' : (m : ℕ) ≤ τ i` using `hle`. Establish `hm1 : (i : ℕ) + d < N` using `by have := m.2; omega`. Use `set m1 : Fin N := ⟨i + d, hm1⟩ with hm1def`. Establish `hm1v : (m1 : ℕ) = i + d` using `rfl`.

Establish `e1` using `hr m1 (by show (i : ℕ) ≤ m1; omega) (by show (m1 : ℕ) ≤ τ i; omega)`. Establish `e2` using `hr m (by show (i : ℕ) ≤ m; omega) hle`. Rewrite using `[← ih m1 hm1v (by show (m1 : ℕ) ≤ τ i; omega)]`. Conclude with `(ht m1 m (by omega) (by show (τ m : ℕ) < τ m1; omega)).symm`. Conclude with `step ((τ i : ℕ) - i) (τ i) (by omega) le_rfl`.

Break down `lt_trichotomy (τ i) i with hc | hc | hc` into its components or cases. Use `main (τ i) (by rw [inv]; exact hc)` as an intermediate fact. Rewrite `this` using `[inv]`. Conclude with `this.symm`. Rewrite using `[hc]`.

Conclude with `main i hc`.
-/
theorem desc_const {α : Type} (τ : Equiv.Perm (Fin N))
    (h : ∀ i j : Fin N, (j : ℕ) = i + 1 → τ j < τ i → (τ i : ℕ) = τ j + 1) (t : Fin N → α)
    (ht : ∀ i j : Fin N, (j : ℕ) = i + 1 → τ j < τ i → t i = t j) (i : Fin N) :
    t (τ i) = t i := by
  have inv := desc_invol τ h
  have main : ∀ i : Fin N, i < τ i → t (τ i) = t i := by
    intro i hi
    have hi' : (i : ℕ) < τ i := hi
    have hr := desc_run τ h ((τ i : ℕ) - i) i (τ i) (by omega) (by rw [inv]; exact hi)
    have step : ∀ d : ℕ, ∀ m : Fin N, (m : ℕ) = i + d → m ≤ τ i → t m = t i := by
      intro d
      induction d with
      | zero => intro m hm _; rw [show m = i from Fin.ext (by omega)]
      | succ d ih =>
        intro m hm hle
        have hle' : (m : ℕ) ≤ τ i := hle
        have hm1 : (i : ℕ) + d < N := by have := m.2; omega
        set m1 : Fin N := ⟨i + d, hm1⟩ with hm1def
        have hm1v : (m1 : ℕ) = i + d := rfl
        have e1 := hr m1 (by show (i : ℕ) ≤ m1; omega) (by show (m1 : ℕ) ≤ τ i; omega)
        have e2 := hr m (by show (i : ℕ) ≤ m; omega) hle
        rw [← ih m1 hm1v (by show (m1 : ℕ) ≤ τ i; omega)]
        exact (ht m1 m (by omega) (by show (τ m : ℕ) < τ m1; omega)).symm
    exact step ((τ i : ℕ) - i) (τ i) (by omega) le_rfl
  rcases lt_trichotomy (τ i) i with hc | hc | hc
  · have := main (τ i) (by rw [inv]; exact hc)
    rw [inv] at this
    exact this.symm
  · rw [hc]
  · exact main i hc

end Comb
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end

section
open Finset Matrix

namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

section Bruhat
variable {K : Type} [Field K] {N : ℕ}

def rowOp (a : Fin N → K) (r : Fin N) : Matrix (Fin N) (Fin N) K :=
  1 + Matrix.of fun i m => if m = r then a i else 0

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `i`. Simplify using `only [rowOp, Matrix.add_apply, Matrix.one_apply_eq, Matrix.of_apply]`. Use `split_ifs with h`. Rewrite using `[ha i (h ▸ le_rfl), add_zero]`.

Rewrite using `[add_zero]`. Introduce `i j hij`. Simplify using `only [rowOp, Matrix.add_apply, Matrix.one_apply_ne (ne_of_gt hij), Matrix.of_apply, zero_add]`. Use `split_ifs with h`. Conclude with `ha i (h ▸ hij.le)`.

Both sides reduce to the same expression.
-/
theorem rowOp_isUT (a : Fin N → K) (r : Fin N) (ha : ∀ i, r ≤ i → a i = 0) :
    IsUT (rowOp a r) := by
  constructor
  · intro i
    simp only [rowOp, Matrix.add_apply, Matrix.one_apply_eq, Matrix.of_apply]
    split_ifs with h
    · rw [ha i (h ▸ le_rfl), add_zero]
    · rw [add_zero]
  · intro i j hij
    simp only [rowOp, Matrix.add_apply, Matrix.one_apply_ne (ne_of_gt hij), Matrix.of_apply,
      zero_add]
    split_ifs with h
    · exact ha i (h ▸ hij.le)
    · rfl

/- English proof (translation)
Rewrite using `[rowOp, Matrix.add_mul, Matrix.one_mul, Matrix.add_apply, Matrix.mul_apply, Finset.sum_eq_single r]`. Simplify using the standard rewrite rules. Introduce `m _ hm`. Simplify using `[hm]`. Introduce `h'`.

Conclude with `absurd (Finset.mem_univ _) h'`.
-/
theorem rowOp_mul (a : Fin N → K) (r : Fin N) (h : Matrix (Fin N) (Fin N) K) (i c : Fin N) :
    (rowOp a r * h) i c = h i c + a i * h r c := by
  rw [rowOp, Matrix.add_mul, Matrix.one_mul, Matrix.add_apply, Matrix.mul_apply,
    Finset.sum_eq_single r]
  · simp
  · intro m _ hm; simp [hm]
  · intro h'; exact absurd (Finset.mem_univ _) h'

def colOp (k : Fin N) (b : Fin N → K) : Matrix (Fin N) (Fin N) K :=
  1 + Matrix.of fun m c => if m = k then b c else 0

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `i`. Simplify using `only [colOp, Matrix.add_apply, Matrix.one_apply_eq, Matrix.of_apply]`. Use `split_ifs with h`. Rewrite using `[hb i (h ▸ le_rfl), add_zero]`.

Rewrite using `[add_zero]`. Introduce `i j hij`. Simplify using `only [colOp, Matrix.add_apply, Matrix.one_apply_ne (ne_of_gt hij), Matrix.of_apply, zero_add]`. Use `split_ifs with h`. Conclude with `hb j (h ▸ hij.le)`.

Both sides reduce to the same expression.
-/
theorem colOp_isUT (k : Fin N) (b : Fin N → K) (hb : ∀ c, c ≤ k → b c = 0) :
    IsUT (colOp k b) := by
  constructor
  · intro i
    simp only [colOp, Matrix.add_apply, Matrix.one_apply_eq, Matrix.of_apply]
    split_ifs with h
    · rw [hb i (h ▸ le_rfl), add_zero]
    · rw [add_zero]
  · intro i j hij
    simp only [colOp, Matrix.add_apply, Matrix.one_apply_ne (ne_of_gt hij), Matrix.of_apply,
      zero_add]
    split_ifs with h
    · exact hb j (h ▸ hij.le)
    · rfl

/- English proof (translation)
Rewrite using `[colOp, Matrix.mul_add, Matrix.mul_one, Matrix.add_apply, Matrix.mul_apply, Finset.sum_eq_single k]`. Simplify using the standard rewrite rules. Introduce `m _ hm`. Simplify using `[hm]`. Introduce `h'`.

Conclude with `absurd (Finset.mem_univ _) h'`.
-/
theorem mul_colOp (k : Fin N) (b : Fin N → K) (h : Matrix (Fin N) (Fin N) K) (i c : Fin N) :
    (h * colOp k b) i c = h i c + h i k * b c := by
  rw [colOp, Matrix.mul_add, Matrix.mul_one, Matrix.add_apply, Matrix.mul_apply,
    Finset.sum_eq_single k]
  · simp
  · intro m _ hm; simp [hm]
  · intro h'; exact absurd (Finset.mem_univ _) h'

def Cleared (h : Matrix (Fin N) (Fin N) K) (k : ℕ) (p : Fin N → Fin N) : Prop :=
  ∀ j : Fin N, (j : ℕ) < k →
    h (p j) j ≠ 0 ∧ (∀ i, i ≠ p j → h i j = 0) ∧ (∀ c, c ≠ j → h (p j) c = 0)

open Classical in
/- English proof (translation)
Introduce `k`. Proceed by induction on `k with`. Consider the case `zero`. Introduce `_`. Use `⟨1, 1, ?_, ?_, id, ?_⟩` and prove the remaining obligations.

Rewrite using `[Units.val_one]`. Conclude with `IsUT.one`. Rewrite using `[Units.val_one]`. Conclude with `IsUT.one`. Introduce `j hj`.

Use linear arithmetic over natural numbers and integers. Consider the case `succ k ih`. Introduce `hk`. Take `⟨u, u', hu, hu', p, hp⟩` from `ih (by omega)`. Use `set hh : GL (Fin N) K := u * g * u' with hhdef`.

Use `set h : Matrix (Fin N) (Fin N) K := (hh : Matrix (Fin N) (Fin N) K) with hdef`. Use `set kk : Fin N := ⟨k, by omega⟩ with hkk`. Establish `hex : ∃ r, h r kk ≠ 0`. Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`.

Establish `h0 : h.det = 0` using `Matrix.det_eq_zero_of_column_eq_zero kk hcon`. Establish `h1 : IsUnit h.det` using `(Matrix.isUnit_iff_isUnit_det _).mp hh.isUnit`. Conclude with `h1.ne_zero h0`. Use `set S : Finset (Fin N) := Finset.univ.filter (fun r => h r kk ≠ 0) with hS`. Establish `hSne : S.Nonempty`.

Take `⟨r, hr⟩` from `hex`. Conclude with `⟨r, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr⟩⟩`. Use `set r0 := S.max' hSne with hr0`. Establish `hd : h r0 kk ≠ 0` using `(Finset.mem_filter.mp (Finset.max'_mem S hSne)).2`. Establish `hmax : ∀ i, r0 < i → h i kk = 0`.

Introduce `i hi`. Assume the negation of the conclusion as `hne`. Use `Finset.le_max' S i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩)` as an intermediate fact. Conclude with `absurd hi (not_lt.mpr this)`. Use `set d := h r0 kk with hddef`.

Use `set a : Fin N → K := fun i => if i < r0 then - h i kk / d else 0 with hadef`. Use `set b : Fin N → K := fun c => if kk < c then - h r0 c / d else 0 with hbdef`. Establish `haUT : IsUT (rowOp a r0)` using `rowOp_isUT a r0 (fun i hi => by`. Simplify using `only [hadef]`. Rewrite using `[if_neg (not_lt.mpr hi)])`.

Establish `hbUT : IsUT (colOp kk b)` using `colOp_isUT kk b (fun c hc => by`. Simplify using `only [hbdef]`. Rewrite using `[if_neg (not_lt.mpr hc)])`. Use `⟨utMk _ haUT * u, u' * utMk _ hbUT, ?_, ?_, Function.update p kk r0, ?_⟩` and prove the remaining obligations. Rewrite using `[Units.val_mul]`.

Conclude with `IsUT.mul haUT hu`. Rewrite using `[Units.val_mul]`. Conclude with `IsUT.mul hu' hbUT`. Establish `hprod : ((utMk _ haUT * u * g * (u' * utMk _ hbUT) : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) = rowOp a r0 * h * colOp kk b`. Establish `: utMk _ haUT * u * g * (u' * utMk _ hbUT) = utMk _ haUT * hh * utMk _ hbUT`.

Rewrite using `[hhdef]`. Use `group`. Rewrite using `[this, Units.val_mul, Units.val_mul, utMk_val, utMk_val]`. Rewrite using `[hprod]`. Establish `hform : ∀ i c, (rowOp a r0 * h * colOp kk b) i c = h i c + a i * h r0 c + (h i kk + a i * d) * b c`.

Introduce `i c`. Rewrite using `[mul_colOp, rowOp_mul, rowOp_mul]`. Establish `F1 : ∀ j : Fin N, (j : ℕ) < k → p j ≠ r0`. Introduce `j hj h'`. Establish `hne : kk ≠ j` using `fun h'' => by rw [← h''] at hj; simp [hkk] at hj`.

Use `(hp j hj).2.2 kk hne` as an intermediate fact. Rewrite `this` using `[h']`. Conclude with `hd this`. Establish `F2 : ∀ j : Fin N, (j : ℕ) < k → h r0 j = 0` using `fun j hj => (hp j hj).2.1 r0 (F1 j hj).symm`. Establish `F3 : ∀ i, h i kk + a i * d = if i = r0 then d else 0`.

Introduce `i`. Break down `lt_trichotomy i r0 with h1 | h1 | h1` into its components or cases. Simplify using `only [hadef]`. Rewrite using `[if_pos h1, if_neg (ne_of_lt h1)]`. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree. Simplify using `only [hadef]`. Rewrite using `[if_pos h1, h1, if_neg (lt_irrefl _), zero_mul, add_zero]`. Simplify using `only [hadef]`. Rewrite using `[if_neg (ne_of_gt h1), if_neg (not_lt.mpr h1.le), hmax i h1, zero_mul, add_zero]`.

Establish `F4 : ∀ j : Fin N, (j : ℕ) < k → a (p j) = 0`. Introduce `j hj`. Establish `hne : kk ≠ j` using `fun h'' => by rw [← h''] at hj; simp [hkk] at hj`. Simplify using `only [hadef]`. Rewrite using `[(hp j hj).2.2 kk hne]`.

Simplify using the standard rewrite rules. Establish `F5 : ∀ c, c ≤ kk → b c = 0` using `fun c hc => by`. Simplify using `only [hbdef]`. Rewrite using `[if_neg (not_lt.mpr hc)]`. Establish `F6 : a r0 = 0` using `by simp only [hadef]; rw [if_neg (lt_irrefl _)]`.

Introduce `j hj`. Distinguish the cases in `hjk : j = kk`. Rewrite using `[hjk, Function.update_self]`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hform, F6, F5 kk le_rfl]`.

Simplify using `using hd`. Introduce `i hi`. Rewrite using `[hform, F5 kk le_rfl, mul_zero, add_zero, F3, if_neg hi]`. Introduce `c hc`. Rewrite using `[hform, F6, zero_mul, zero_mul, add_zero, add_zero]`.

Break down `lt_or_gt_of_ne hc with h1 | h1` into its components or cases. Rewrite using `[F5 c h1.le, mul_zero, add_zero]`. Conclude with `F2 c h1`. Simplify using `only [hbdef]`. Rewrite using `[if_pos h1]`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `hjlt : (j : ℕ) < k`. Establish `: (j : ℕ) ≠ k` using `fun h' => hjk (Fin.ext h')`. Use linear arithmetic over natural numbers and integers.

Establish `hjle : j ≤ kk` using `by show (j : ℕ) ≤ k; omega`. Rewrite using `[Function.update_of_ne hjk]`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hform, F5 j hjle, F4 j hjlt]`. Simplify using `using (hp j hjlt).1`.

Introduce `i hi`. Rewrite using `[hform, F5 j hjle, F2 j hjlt, (hp j hjlt).2.1 i hi]`. Simplify using the standard rewrite rules. Introduce `c hc`. Rewrite using `[hform, F3, if_neg (F1 j hjlt), F4 j hjlt, (hp j hjlt).2.2 c hc]`.

Simplify using the standard rewrite rules.
-/
theorem bruhat_step (g : GL (Fin N) K) : ∀ k : ℕ, k ≤ N → ∃ u u' : GL (Fin N) K,
    IsUT (u : Matrix (Fin N) (Fin N) K) ∧ IsUT (u' : Matrix (Fin N) (Fin N) K) ∧
    ∃ p, Cleared ((u * g * u' : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) k p := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨1, 1, ?_, ?_, id, ?_⟩
    · rw [Units.val_one]; exact IsUT.one
    · rw [Units.val_one]; exact IsUT.one
    · intro j hj; omega
  | succ k ih =>
    intro hk
    obtain ⟨u, u', hu, hu', p, hp⟩ := ih (by omega)
    set hh : GL (Fin N) K := u * g * u' with hhdef
    set h : Matrix (Fin N) (Fin N) K := (hh : Matrix (Fin N) (Fin N) K) with hdef
    set kk : Fin N := ⟨k, by omega⟩ with hkk
    have hex : ∃ r, h r kk ≠ 0 := by
      by_contra hcon
      push Not at hcon
      have h0 : h.det = 0 := Matrix.det_eq_zero_of_column_eq_zero kk hcon
      have h1 : IsUnit h.det := (Matrix.isUnit_iff_isUnit_det _).mp hh.isUnit
      exact h1.ne_zero h0
    set S : Finset (Fin N) := Finset.univ.filter (fun r => h r kk ≠ 0) with hS
    have hSne : S.Nonempty := by
      obtain ⟨r, hr⟩ := hex
      exact ⟨r, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr⟩⟩
    set r0 := S.max' hSne with hr0
    have hd : h r0 kk ≠ 0 := (Finset.mem_filter.mp (Finset.max'_mem S hSne)).2
    have hmax : ∀ i, r0 < i → h i kk = 0 := by
      intro i hi
      by_contra hne
      have := Finset.le_max' S i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩)
      exact absurd hi (not_lt.mpr this)
    set d := h r0 kk with hddef
    set a : Fin N → K := fun i => if i < r0 then - h i kk / d else 0 with hadef
    set b : Fin N → K := fun c => if kk < c then - h r0 c / d else 0 with hbdef
    have haUT : IsUT (rowOp a r0) := rowOp_isUT a r0 (fun i hi => by
      simp only [hadef]; rw [if_neg (not_lt.mpr hi)])
    have hbUT : IsUT (colOp kk b) := colOp_isUT kk b (fun c hc => by
      simp only [hbdef]; rw [if_neg (not_lt.mpr hc)])
    refine ⟨utMk _ haUT * u, u' * utMk _ hbUT, ?_, ?_, Function.update p kk r0, ?_⟩
    · rw [Units.val_mul]; exact IsUT.mul haUT hu
    · rw [Units.val_mul]; exact IsUT.mul hu' hbUT
    have hprod : ((utMk _ haUT * u * g * (u' * utMk _ hbUT) : GL (Fin N) K) :
        Matrix (Fin N) (Fin N) K) = rowOp a r0 * h * colOp kk b := by
      have : utMk _ haUT * u * g * (u' * utMk _ hbUT) = utMk _ haUT * hh * utMk _ hbUT := by
        rw [hhdef]; group
      rw [this, Units.val_mul, Units.val_mul, utMk_val, utMk_val]
    rw [hprod]
    have hform : ∀ i c, (rowOp a r0 * h * colOp kk b) i c =
        h i c + a i * h r0 c + (h i kk + a i * d) * b c := by
      intro i c
      rw [mul_colOp, rowOp_mul, rowOp_mul]
    have F1 : ∀ j : Fin N, (j : ℕ) < k → p j ≠ r0 := by
      intro j hj h'
      have hne : kk ≠ j := fun h'' => by rw [← h''] at hj; simp [hkk] at hj
      have := (hp j hj).2.2 kk hne
      rw [h'] at this
      exact hd this
    have F2 : ∀ j : Fin N, (j : ℕ) < k → h r0 j = 0 := fun j hj =>
      (hp j hj).2.1 r0 (F1 j hj).symm
    have F3 : ∀ i, h i kk + a i * d = if i = r0 then d else 0 := by
      intro i
      rcases lt_trichotomy i r0 with h1 | h1 | h1
      · simp only [hadef]
        rw [if_pos h1, if_neg (ne_of_lt h1)]
        field_simp
        ring
      · simp only [hadef]
        rw [if_pos h1, h1, if_neg (lt_irrefl _), zero_mul, add_zero]
      · simp only [hadef]
        rw [if_neg (ne_of_gt h1), if_neg (not_lt.mpr h1.le), hmax i h1, zero_mul, add_zero]
    have F4 : ∀ j : Fin N, (j : ℕ) < k → a (p j) = 0 := by
      intro j hj
      have hne : kk ≠ j := fun h'' => by rw [← h''] at hj; simp [hkk] at hj
      simp only [hadef]
      rw [(hp j hj).2.2 kk hne]
      simp
    have F5 : ∀ c, c ≤ kk → b c = 0 := fun c hc => by
      simp only [hbdef]; rw [if_neg (not_lt.mpr hc)]
    have F6 : a r0 = 0 := by simp only [hadef]; rw [if_neg (lt_irrefl _)]
    intro j hj
    by_cases hjk : j = kk
    · rw [hjk, Function.update_self]
      refine ⟨?_, ?_, ?_⟩
      · rw [hform, F6, F5 kk le_rfl]
        simpa using hd
      · intro i hi
        rw [hform, F5 kk le_rfl, mul_zero, add_zero, F3, if_neg hi]
      · intro c hc
        rw [hform, F6, zero_mul, zero_mul, add_zero, add_zero]
        rcases lt_or_gt_of_ne hc with h1 | h1
        · rw [F5 c h1.le, mul_zero, add_zero]
          exact F2 c h1
        · simp only [hbdef]
          rw [if_pos h1]
          field_simp
          ring
    · have hjlt : (j : ℕ) < k := by
        have : (j : ℕ) ≠ k := fun h' => hjk (Fin.ext h')
        omega
      have hjle : j ≤ kk := by show (j : ℕ) ≤ k; omega
      rw [Function.update_of_ne hjk]
      refine ⟨?_, ?_, ?_⟩
      · rw [hform, F5 j hjle, F4 j hjlt]
        simpa using (hp j hjlt).1
      · intro i hi
        rw [hform, F5 j hjle, F2 j hjlt, (hp j hjlt).2.1 i hi]
        simp
      · intro c hc
        rw [hform, F3, if_neg (F1 j hjlt), F4 j hjlt, (hp j hjlt).2.2 c hc]
        simp

/- English proof (translation)
Take `⟨u, u', hu, hu', p, hp⟩` from `bruhat_step g N le_rfl`. Use `⟨u, u', hu, hu', ?_⟩` and prove the remaining obligations. Use `set h : Matrix (Fin N) (Fin N) K := ((u * g * u' : GL (Fin N) K) : Matrix (Fin N) (Fin N) K)`. Establish `hinj : Function.Injective p`. Introduce `j j' hjj`.

Assume the negation of the conclusion as `hne`. Establish `h1` using `(hp j j.2).2.2 j' (Ne.symm hne)`. Rewrite `h1` using `[hjj]`. Conclude with `(hp j' j'.2).1 h1`. Use `⟨Equiv.ofBijective p (Finite.injective_iff_bijective.mp hinj), fun j => h (p j) j, fun j => (hp j j.2).1, ?_⟩` and prove the remaining obligations.

Introduce `i j`. Rewrite using `[Equiv.ofBijective_apply]`. Use `split_ifs with hij`. Rewrite using `[hij]`. Conclude with `(hp j j.2).2.1 i hij`.
-/
theorem bruhat_exists (g : GL (Fin N) K) : ∃ u u' : GL (Fin N) K,
    IsUT (u : Matrix (Fin N) (Fin N) K) ∧ IsUT (u' : Matrix (Fin N) (Fin N) K) ∧
    ∃ (π : Equiv.Perm (Fin N)) (t : Fin N → K), (∀ j, t j ≠ 0) ∧
      ∀ i j, ((u * g * u' : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) i j =
        if i = π j then t j else 0 := by
  obtain ⟨u, u', hu, hu', p, hp⟩ := bruhat_step g N le_rfl
  refine ⟨u, u', hu, hu', ?_⟩
  set h : Matrix (Fin N) (Fin N) K := ((u * g * u' : GL (Fin N) K) : Matrix (Fin N) (Fin N) K)
  have hinj : Function.Injective p := by
    intro j j' hjj
    by_contra hne
    have h1 := (hp j j.2).2.2 j' (Ne.symm hne)
    rw [hjj] at h1
    exact (hp j' j'.2).1 h1
  refine ⟨Equiv.ofBijective p (Finite.injective_iff_bijective.mp hinj), fun j => h (p j) j,
    fun j => (hp j j.2).1, ?_⟩
  intro i j
  rw [Equiv.ofBijective_apply]
  split_ifs with hij
  · rw [hij]
  · exact (hp j j.2).2.1 i hij

end Bruhat
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end

section
open Finset Matrix

namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

section Transfer
variable {G : Type} [Group G]

def GTAlt (σ : G → G) (J : Subgroup G) (χ : J →* ℂˣ) (g : G) : Prop :=
  (∃ u u' : J, σ g = u * g * u' ∧ χ u * χ u' = 1) ∨
    (∃ u u' : J, (u : G) * g * u' = g ∧ χ u * χ u' ≠ 1)

/- English proof (translation)
Break down `h with ⟨a, b, h1, h2⟩ | ⟨a, b, h1, h2⟩` into its components or cases. Use `left`. Take `⟨m1, e1⟩` from `hJ u1`. Take `⟨m2, e2⟩` from `hJ u2`. Use `⟨(⟨σ u2, m2⟩ : J)⁻¹ * a * u1, u2 * b * (⟨σ u1, m1⟩ : J)⁻¹, ?_, ?_⟩` and prove the remaining obligations.

Rewrite `h1` using `[hσ, hσ]`. Simplify using `only [Subgroup.coe_mul, Subgroup.coe_inv]`. Establish `: σ g = (σ u2)⁻¹ * (σ u2 * (σ g * σ u1)) * (σ u1)⁻¹` using `by group`. Rewrite using `[this, h1]`. Use `group`.

Simplify using `only [map_mul, map_inv, e1, e2]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [mul_assoc, mul_comm, mul_left_comm]`. Use `_ = 1 := by rw [h2]; simp`. Use `right`.

Use `⟨u1⁻¹ * a * u1, u2 * b * u2⁻¹, ?_, ?_⟩` and prove the remaining obligations. Simplify using `only [Subgroup.coe_mul, Subgroup.coe_inv]`. Establish `: (u1 : G)⁻¹ * a * u1 * g * (u2 * b * (u2 : G)⁻¹) = (u1 : G)⁻¹ * (a * (u1 * g * u2) * b) * (u2 : G)⁻¹` using `by group`. Rewrite using `[this, h1]`. Use `group`.

Simplify using `only [map_mul, map_inv]`. Introduce `h3`. Apply `h2` to reduce the goal to its premises. Combine the equalities or inequalities in the displayed calculation. Establish `: (χ u1)⁻¹ * χ a * χ u1 * (χ u2 * χ b * (χ u2)⁻¹) = (χ a * χ b) * ((χ u1)⁻¹ * χ u1) * (χ u2 * (χ u2)⁻¹)`.

Simplify using `only [mul_assoc, mul_comm, mul_left_comm]`. Rewrite using `[this]`. Simplify using the standard rewrite rules. Use `_ = 1 := h3`.
-/
theorem GTAlt.transfer (σ : G → G) (hσ : ∀ x y, σ (x * y) = σ y * σ x)
    (J : Subgroup G) (χ : J →* ℂˣ) (hJ : ∀ u : J, ∃ h : σ u ∈ J, χ ⟨σ u, h⟩ = χ u)
    (u1 u2 : J) (g : G) (h : GTAlt σ J χ ((u1 : G) * g * u2)) : GTAlt σ J χ g := by
  rcases h with ⟨a, b, h1, h2⟩ | ⟨a, b, h1, h2⟩
  · left
    obtain ⟨m1, e1⟩ := hJ u1
    obtain ⟨m2, e2⟩ := hJ u2
    refine ⟨(⟨σ u2, m2⟩ : J)⁻¹ * a * u1, u2 * b * (⟨σ u1, m1⟩ : J)⁻¹, ?_, ?_⟩
    · rw [hσ, hσ] at h1
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      have : σ g = (σ u2)⁻¹ * (σ u2 * (σ g * σ u1)) * (σ u1)⁻¹ := by group
      rw [this, h1]
      group
    · simp only [map_mul, map_inv, e1, e2]
      calc (χ u2)⁻¹ * χ a * χ u1 * (χ u2 * χ b * (χ u1)⁻¹)
          = (χ a * χ b) * ((χ u2)⁻¹ * χ u2) * (χ u1 * (χ u1)⁻¹) := by
            simp only [mul_assoc, mul_comm, mul_left_comm]
        _ = 1 := by rw [h2]; simp
  · right
    refine ⟨u1⁻¹ * a * u1, u2 * b * u2⁻¹, ?_, ?_⟩
    · simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      have : (u1 : G)⁻¹ * a * u1 * g * (u2 * b * (u2 : G)⁻¹) =
          (u1 : G)⁻¹ * (a * (u1 * g * u2) * b) * (u2 : G)⁻¹ := by group
      rw [this, h1]
      group
    · simp only [map_mul, map_inv]
      intro h3
      apply h2
      calc χ a * χ b = (χ u1)⁻¹ * χ a * χ u1 * (χ u2 * χ b * (χ u2)⁻¹) := by
            have : (χ u1)⁻¹ * χ a * χ u1 * (χ u2 * χ b * (χ u2)⁻¹) =
              (χ a * χ b) * ((χ u1)⁻¹ * χ u1) * (χ u2 * (χ u2)⁻¹) := by
                simp only [mul_assoc, mul_comm, mul_left_comm]
            rw [this]; simp
        _ = 1 := h3

end Transfer

section Flip
variable {K : Type} [Field K] {N : ℕ}

def flipM (A : Matrix (Fin N) (Fin N) K) : Matrix (Fin N) (Fin N) K :=
  Matrix.of fun i j => A (Fin.rev j) (Fin.rev i)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem flipM_apply (A : Matrix (Fin N) (Fin N) K) (i j : Fin N) :
    flipM A i j = A (Fin.rev j) (Fin.rev i) := rfl

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [flipM_apply, Matrix.mul_apply]`. Use `Fintype.sum_equiv Fin.revPerm _ _ (fun m => ?_)` and prove the remaining obligations. Simplify using `[mul_comm]`.
-/
theorem flipM_mul (A B : Matrix (Fin N) (Fin N) K) : flipM (A * B) = flipM B * flipM A := by
  ext i j
  simp only [flipM_apply, Matrix.mul_apply]
  refine Fintype.sum_equiv Fin.revPerm _ _ (fun m => ?_)
  simp [mul_comm]

/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[flipM_apply, Matrix.one_apply, Matrix.one_apply]`. Simplify using `only [Fin.rev_inj]`. Distinguish the cases in `h : i = j`. Rewrite using `[if_pos h, if_pos h.symm]`.

Rewrite using `[if_neg h, if_neg (Ne.symm h)]`.
-/
theorem flipM_one : flipM (1 : Matrix (Fin N) (Fin N) K) = 1 := by
  ext i j
  rw [flipM_apply, Matrix.one_apply, Matrix.one_apply]
  simp only [Fin.rev_inj]
  by_cases h : i = j
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (Ne.symm h)]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[flipM_apply]`.
-/
theorem flipM_flipM (A : Matrix (Fin N) (Fin N) K) : flipM (flipM A) = A := by
  ext i j
  simp [flipM_apply]

def flipG (g : GL (Fin N) K) : GL (Fin N) K :=
  ⟨flipM g.1, flipM (g⁻¹).1, by
    rw [← flipM_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, flipM_one], by
    rw [← flipM_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, flipM_one]⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem flipG_val (g : GL (Fin N) K) :
    ((flipG g : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) = flipM g.1 := rfl

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[Units.val_mul, flipG_val, flipG_val, flipG_val, Units.val_mul, flipM_mul]`.
-/
theorem flipG_mul (x y : GL (Fin N) K) : flipG (x * y) = flipG y * flipG x := by
  apply Units.ext
  rw [Units.val_mul, flipG_val, flipG_val, flipG_val, Units.val_mul, flipM_mul]

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[flipG_val, flipG_val, flipM_flipM]`.
-/
theorem flipG_flipG (x : GL (Fin N) K) : flipG (flipG x) = x := by
  apply Units.ext
  rw [flipG_val, flipG_val, flipM_flipM]

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun i => h.1 _, fun i j hij => h.2 _ _ (Fin.rev_lt_rev.mpr hij)⟩`.
-/
theorem IsUT.flip {A : Matrix (Fin N) (Fin N) K} (h : IsUT A) : IsUT (flipM A) :=
  ⟨fun i => h.1 _, fun i j hij => h.2 _ _ (Fin.rev_lt_rev.mpr hij)⟩

/- English proof (translation)
Unfold `edgeSum`. Rewrite using `[Finset.sum_comm]`. Use `Fintype.sum_equiv Fin.revPerm _ _ (fun j => ?_)` and prove the remaining obligations. Use `Fintype.sum_equiv Fin.revPerm _ _ (fun i => ?_)` and prove the remaining obligations. Simplify using `only [Fin.revPerm_apply, flipM_apply]`.

Establish `: ((j : ℕ) = i + 1) ↔ ((Fin.rev i : Fin N) : ℕ) = (Fin.rev j : Fin N) + 1`. Rewrite using `[Fin.val_rev, Fin.val_rev]`. Use `i.2` as an intermediate fact. Use `j.2` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Simplify using `only [this]`.
-/
theorem edgeSum_flip (A : Matrix (Fin N) (Fin N) K) : edgeSum (flipM A) = edgeSum A := by
  unfold edgeSum
  rw [Finset.sum_comm]
  refine Fintype.sum_equiv Fin.revPerm _ _ (fun j => ?_)
  refine Fintype.sum_equiv Fin.revPerm _ _ (fun i => ?_)
  simp only [Fin.revPerm_apply, flipM_apply]
  have : ((j : ℕ) = i + 1) ↔ ((Fin.rev i : Fin N) : ℕ) = (Fin.rev j : Fin N) + 1 := by
    rw [Fin.val_rev, Fin.val_rev]
    have := i.2
    have := j.2
    omega
  simp only [this]

/- English proof (translation)
Use `⟨IsUT.flip u.2, ?_⟩` and prove the remaining obligations. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[uniChar_val, uniChar_val]`. Use `show ψ₀ (edgeSum (flipM _)) = _`. Rewrite using `[edgeSum_flip]`.
-/
theorem flip_char (ψ₀ : AddChar K ℂ) (u : uniSub K N) :
    ∃ h : flipG (u : GL (Fin N) K) ∈ uniSub K N, uniChar ψ₀ N ⟨flipG u, h⟩ = uniChar ψ₀ N u := by
  refine ⟨IsUT.flip u.2, ?_⟩
  apply Units.ext
  rw [uniChar_val, uniChar_val]
  show ψ₀ (edgeSum (flipM _)) = _
  rw [edgeSum_flip]

end Flip

section Elem
variable {K : Type} [Field K] {N : ℕ}

def elM (p q : Fin N) (v : K) : Matrix (Fin N) (Fin N) K :=
  1 + Matrix.of fun x c => if x = p ∧ c = q then v else 0

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `i`. Simplify using `only [elM, Matrix.add_apply, Matrix.one_apply_eq, Matrix.of_apply]`. Rewrite using `[if_neg, add_zero]`. Introduce and unpack `⟨h1, h2⟩`.

Rewrite `h` using `[← h1, ← h2]`. Conclude with `lt_irrefl _ h`. Introduce `i j hij`. Simplify using `only [elM, Matrix.add_apply, Matrix.one_apply_ne (ne_of_gt hij), Matrix.of_apply, zero_add]`. Rewrite using `[if_neg]`.

Introduce and unpack `⟨h1, h2⟩`. Rewrite `h` using `[← h1, ← h2]`. Conclude with `lt_asymm h hij`.
-/
theorem elM_isUT (p q : Fin N) (v : K) (h : p < q) : IsUT (elM p q v) := by
  constructor
  · intro i
    simp only [elM, Matrix.add_apply, Matrix.one_apply_eq, Matrix.of_apply]
    rw [if_neg, add_zero]
    rintro ⟨h1, h2⟩
    rw [← h1, ← h2] at h
    exact lt_irrefl _ h
  · intro i j hij
    simp only [elM, Matrix.add_apply, Matrix.one_apply_ne (ne_of_gt hij), Matrix.of_apply, zero_add]
    rw [if_neg]
    rintro ⟨h1, h2⟩
    rw [← h1, ← h2] at h
    exact lt_asymm h hij

/- English proof (translation)
Rewrite using `[elM, Matrix.add_mul, Matrix.one_mul, Matrix.add_apply, Matrix.mul_apply, Finset.sum_eq_single q]`. Apply the tactic sequence `by_cases hx : x = p <;> simp [hx]`. Introduce `m _ hm`. Simplify using `[hm]`. Introduce `h'`.

Conclude with `absurd (Finset.mem_univ _) h'`.
-/
theorem elM_mul (p q : Fin N) (v : K) (h : Matrix (Fin N) (Fin N) K) (x c : Fin N) :
    (elM p q v * h) x c = h x c + if x = p then v * h q c else 0 := by
  rw [elM, Matrix.add_mul, Matrix.one_mul, Matrix.add_apply, Matrix.mul_apply,
    Finset.sum_eq_single q]
  · by_cases hx : x = p <;> simp [hx]
  · intro m _ hm; simp [hm]
  · intro h'; exact absurd (Finset.mem_univ _) h'

/- English proof (translation)
Rewrite using `[elM, Matrix.mul_add, Matrix.mul_one, Matrix.add_apply, Matrix.mul_apply, Finset.sum_eq_single p]`. Apply the tactic sequence `by_cases hx : c = q <;> simp [hx]`. Introduce `m _ hm`. Simplify using `[hm]`. Introduce `h'`.

Conclude with `absurd (Finset.mem_univ _) h'`.
-/
theorem mul_elM (p q : Fin N) (v : K) (h : Matrix (Fin N) (Fin N) K) (x c : Fin N) :
    (h * elM p q v) x c = h x c + if c = q then h x p * v else 0 := by
  rw [elM, Matrix.mul_add, Matrix.mul_one, Matrix.add_apply, Matrix.mul_apply,
    Finset.sum_eq_single p]
  · by_cases hx : c = q <;> simp [hx]
  · intro m _ hm; simp [hm]
  · intro h'; exact absurd (Finset.mem_univ _) h'

/- English proof (translation)
Unfold `edgeSum`. Rewrite using `[Finset.sum_eq_single p]`. Rewrite using `[Finset.sum_eq_single q]`. Distinguish the cases in `h : (q : ℕ) = p + 1`. Establish `hpq : p ≠ q` using `by intro h'; rw [h'] at h; omega`.

Simplify using `[h, elM, Matrix.one_apply_ne hpq]`. Simplify using `[h]`. Introduce `c _ hc split_ifs with h`. Establish `hpc : p ≠ c` using `by intro h'; rw [h'] at h; omega`. Simplify using `[elM, Matrix.one_apply_ne hpc, hc]`.

Both sides reduce to the same expression. Introduce `h'`. Conclude with `absurd (Finset.mem_univ _) h'`. Introduce `x _ hx`. Use `Finset.sum_eq_zero fun c _ => ?_` and prove the remaining obligations.

Use `split_ifs with h`. Establish `hxc : x ≠ c` using `by intro h'; rw [h'] at h; omega`. Simplify using `[elM, Matrix.one_apply_ne hxc, hx]`. Both sides reduce to the same expression. Introduce `h'`.

Conclude with `absurd (Finset.mem_univ _) h'`.
-/
theorem edgeSum_elM (p q : Fin N) (v : K) :
    edgeSum (elM p q v) = if (q : ℕ) = p + 1 then v else 0 := by
  unfold edgeSum
  rw [Finset.sum_eq_single p]
  · rw [Finset.sum_eq_single q]
    · by_cases h : (q : ℕ) = p + 1
      · have hpq : p ≠ q := by intro h'; rw [h'] at h; omega
        simp [h, elM, Matrix.one_apply_ne hpq]
      · simp [h]
    · intro c _ hc
      split_ifs with h
      · have hpc : p ≠ c := by intro h'; rw [h'] at h; omega
        simp [elM, Matrix.one_apply_ne hpc, hc]
      · rfl
    · intro h'; exact absurd (Finset.mem_univ _) h'
  · intro x _ hx
    refine Finset.sum_eq_zero fun c _ => ?_
    split_ifs with h
    · have hxc : x ≠ c := by intro h'; rw [h'] at h; omega
      simp [elM, Matrix.one_apply_ne hxc, hx]
    · rfl
  · intro h'; exact absurd (Finset.mem_univ _) h'

end Elem

section Mono
variable {K : Type} [Field K] {N : ℕ}

def MonoAdm (π : Equiv.Perm (Fin N)) (t : Fin N → K) : Prop :=
  ∀ i j : Fin N, (j : ℕ) = i + 1 → π i < π j → (π j : ℕ) = π i + 1 ∧ t i = t j

/- English proof (translation)
Use `set τ : Equiv.Perm (Fin N) := π.trans Fin.revPerm with hτ`. Establish `hτv : ∀ i, τ i = Fin.rev (π i)` using `fun i => rfl`. Establish `hlt : ∀ i j, τ j < τ i ↔ π i < π j`. Introduce `i j`. Rewrite using `[hτv, hτv, Fin.rev_lt_rev]`.

Establish `h1 : ∀ i j : Fin N, (j : ℕ) = i + 1 → τ j < τ i → (τ i : ℕ) = τ j + 1`. Introduce `i j hij hl`. Use `(hadm i j hij ((hlt i j).mp hl)).1` as an intermediate fact. Rewrite using `[hτv, hτv, Fin.val_rev, Fin.val_rev]`. Use `(π j).2` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Establish `h2 : ∀ i j : Fin N, (j : ℕ) = i + 1 → τ j < τ i → t i = t j` using `fun i j hij hl => (hadm i j hij ((hlt i j).mp hl)).2`. Establish `inv` using `desc_invol τ h1`. Establish `cst` using `desc_const τ h1 t h2`. Establish `hπ : ∀ x, π x = Fin.rev (τ x)` using `fun x => by rw [hτv, Fin.rev_rev]`.

Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `i j`. Rewrite using `[flipG_val, flipM_apply, hn, hn]`. Distinguish the cases in `hij : i = π j`. Establish `e1 : Fin.rev i = τ j` using `by rw [hij, hτv]`.

Rewrite using `[if_pos hij, e1, hπ (τ j), inv, if_pos rfl, cst]`. Rewrite using `[if_neg hij, if_neg]`. Introduce `h3`. Apply `hij` to reduce the goal to its premises. Establish `e2 : j = τ (Fin.rev i)` using `by rw [hτv, ← h3, Fin.rev_rev]`.

Establish `e3 : τ j = Fin.rev i` using `by rw [e2, inv]`. Rewrite using `[hπ j, e3, Fin.rev_rev]`.
-/
theorem flip_mono (n : GL (Fin N) K) (π : Equiv.Perm (Fin N)) (t : Fin N → K)
    (hn : ∀ i j, (n : Matrix (Fin N) (Fin N) K) i j = if i = π j then t j else 0)
    (hadm : MonoAdm π t) : flipG n = n := by
  set τ : Equiv.Perm (Fin N) := π.trans Fin.revPerm with hτ
  have hτv : ∀ i, τ i = Fin.rev (π i) := fun i => rfl
  have hlt : ∀ i j, τ j < τ i ↔ π i < π j := by
    intro i j
    rw [hτv, hτv, Fin.rev_lt_rev]
  have h1 : ∀ i j : Fin N, (j : ℕ) = i + 1 → τ j < τ i → (τ i : ℕ) = τ j + 1 := by
    intro i j hij hl
    have := (hadm i j hij ((hlt i j).mp hl)).1
    rw [hτv, hτv, Fin.val_rev, Fin.val_rev]
    have := (π j).2
    omega
  have h2 : ∀ i j : Fin N, (j : ℕ) = i + 1 → τ j < τ i → t i = t j := fun i j hij hl =>
    (hadm i j hij ((hlt i j).mp hl)).2
  have inv := desc_invol τ h1
  have cst := desc_const τ h1 t h2
  have hπ : ∀ x, π x = Fin.rev (τ x) := fun x => by rw [hτv, Fin.rev_rev]
  apply Units.ext
  ext i j
  rw [flipG_val, flipM_apply, hn, hn]
  by_cases hij : i = π j
  · have e1 : Fin.rev i = τ j := by rw [hij, hτv]
    rw [if_pos hij, e1, hπ (τ j), inv, if_pos rfl, cst]
  · rw [if_neg hij, if_neg]
    intro h3
    apply hij
    have e2 : j = τ (Fin.rev i) := by rw [hτv, ← h3, Fin.rev_rev]
    have e3 : τ j = Fin.rev i := by rw [e2, inv]
    rw [hπ j, e3, Fin.rev_rev]

/- English proof (translation)
Unfold `MonoAdm at hadm`. Use `push Not at hadm`. Take `⟨i, j, hij, hlt, hbad⟩` from `hadm`. Take `⟨a0, ha0⟩` from `(AddChar.ne_one_iff).mp hψ`. Establish `hilt : i < j` using `by show (i : ℕ) < j; omega`.

Use `set s : K := if (π j : ℕ) = π i + 1 then t i / t j else 0 with hs`. Establish `hs1 : 1 - s ≠ 0`. Rewrite using `[hs]`. Use `split_ifs with h`. Use `hbad h` as an intermediate fact.

Introduce `h'`. Apply `this` to reduce the goal to its premises. Establish `h'' : t i / t j = 1` using `(sub_eq_zero.mp h').symm`. Rewrite `h''` using `[div_eq_one_iff_eq (ht j)]`. Then use the resulting hypothesis. Simplify using the standard rewrite rules.

Use `set a : K := a0 / (1 - s) with ha`. Use `set c0 : K := a * t i / t j with hc0`. Use `⟨⟨utMk _ (elM_isUT (π i) (π j) (-c0) hlt), elM_isUT (π i) (π j) (-c0) hlt⟩, ⟨utMk _ (elM_isUT i j a hilt), elM_isUT i j a hilt⟩, ?_, ?_⟩` and prove the remaining obligations. Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `x c`.

Simplify using `only [Units.val_mul, utMk_val]`. Rewrite using `[mul_elM, elM_mul, elM_mul, hn, hn, hn, hn]`. Establish `hne : π j ≠ π i` using `ne_of_gt hlt`. Rewrite using `[if_neg hne]`. Distinguish the cases in `hx : x = π i`.

Distinguish the cases in `hc : c = j`. Rewrite using `[if_pos hx, if_pos hc, hc, if_pos rfl, if_pos hx]`. Rewrite using `[hx, if_neg hne.symm, hc0]`. Establish `htj` using `ht j`. Simplify using `only [if_true, mul_zero, add_zero, zero_add]`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `: π j ≠ π c` using `fun h' => hc (π.injective h').symm`. Rewrite using `[if_neg hc, if_neg this]`. Simplify using the standard rewrite rules.

Rewrite using `[if_neg hx, if_neg hx]`. Simplify using the standard rewrite rules. Introduce `h`. Apply `ha0` to reduce the goal to its premises. Establish `h'` using `congrArg (fun z : ℂˣ => (z : ℂ)) h`.

Simplify using `only [Units.val_mul, uniChar_val, Units.val_one, utMk_val] at h'`. Rewrite `h'` using `[← AddChar.map_add_eq_mul, edgeSum_elM, edgeSum_elM, if_pos hij]`. Establish `e : (if (π j : ℕ) = π i + 1 then -c0 else 0) + a = a0`. Establish `e1 : (if (π j : ℕ) = π i + 1 then -c0 else 0) = - (a * s)`. Rewrite using `[hs]`.

Use `split_ifs with h`. Rewrite using `[hc0]`. Expand and normalize the polynomial expressions, which then agree. Simplify using the standard rewrite rules. Rewrite using `[e1, ha]`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Rewrite `h'` using `[e]`. Conclude with `h'`.
-/
theorem mono_not_adm (ψ₀ : AddChar K ℂ) (hψ : ψ₀ ≠ 1) (n : GL (Fin N) K)
    (π : Equiv.Perm (Fin N)) (t : Fin N → K) (ht : ∀ j, t j ≠ 0)
    (hn : ∀ i j, (n : Matrix (Fin N) (Fin N) K) i j = if i = π j then t j else 0)
    (hadm : ¬ MonoAdm π t) :
    ∃ u u' : uniSub K N, (u : GL (Fin N) K) * n * u' = n ∧
      uniChar ψ₀ N u * uniChar ψ₀ N u' ≠ 1 := by
  unfold MonoAdm at hadm
  push Not at hadm
  obtain ⟨i, j, hij, hlt, hbad⟩ := hadm
  obtain ⟨a0, ha0⟩ := (AddChar.ne_one_iff).mp hψ
  have hilt : i < j := by show (i : ℕ) < j; omega
  set s : K := if (π j : ℕ) = π i + 1 then t i / t j else 0 with hs
  have hs1 : 1 - s ≠ 0 := by
    rw [hs]
    split_ifs with h
    · have := hbad h
      intro h'
      apply this
      have h'' : t i / t j = 1 := (sub_eq_zero.mp h').symm
      rwa [div_eq_one_iff_eq (ht j)] at h''
    · simp
  set a : K := a0 / (1 - s) with ha
  set c0 : K := a * t i / t j with hc0
  refine ⟨⟨utMk _ (elM_isUT (π i) (π j) (-c0) hlt), elM_isUT (π i) (π j) (-c0) hlt⟩,
    ⟨utMk _ (elM_isUT i j a hilt), elM_isUT i j a hilt⟩, ?_, ?_⟩
  · apply Units.ext
    ext x c
    simp only [Units.val_mul, utMk_val]
    rw [mul_elM, elM_mul, elM_mul, hn, hn, hn, hn]
    have hne : π j ≠ π i := ne_of_gt hlt
    rw [if_neg hne]
    by_cases hx : x = π i
    · by_cases hc : c = j
      · rw [if_pos hx, if_pos hc, hc, if_pos rfl, if_pos hx]
        rw [hx, if_neg hne.symm, hc0]
        have htj := ht j
        simp only [if_true, mul_zero, add_zero, zero_add]
        field_simp
        ring
      · have : π j ≠ π c := fun h' => hc (π.injective h').symm
        rw [if_neg hc, if_neg this]
        simp
    · rw [if_neg hx, if_neg hx]
      simp
  · intro h
    apply ha0
    have h' := congrArg (fun z : ℂˣ => (z : ℂ)) h
    simp only [Units.val_mul, uniChar_val, Units.val_one, utMk_val] at h'
    rw [← AddChar.map_add_eq_mul, edgeSum_elM, edgeSum_elM, if_pos hij] at h'
    have e : (if (π j : ℕ) = π i + 1 then -c0 else 0) + a = a0 := by
      have e1 : (if (π j : ℕ) = π i + 1 then -c0 else 0) = - (a * s) := by
        rw [hs]
        split_ifs with h
        · rw [hc0]; ring
        · simp
      rw [e1, ha]
      field_simp
      ring
    rw [e] at h'
    exact h'

end Mono

/- English proof (translation)
Introduce `K V _ _ _ _ _ N ψ₀ ρ hψ hirr`. Establish `: Fintype (GL (Fin N) K)` using `Fintype.ofFinite _`. Rewrite using `[besselSpace_zero_eq_equivariant]`. Use `gelfand_trick ρ (uniSub K N) (uniChar ψ₀ N) ?_ hirr` and prove the remaining obligations. Use `hecke_comm flipG flipG_mul flipG_flipG (uniSub K N) (uniChar ψ₀ N) (flip_char ψ₀) ?_` and prove the remaining obligations.

Introduce `g`. Take `⟨u, u', hu, hu', π, t, ht, hn⟩` from `bruhat_exists g`. Use `GTAlt.transfer flipG flipG_mul (uniSub K N) (uniChar ψ₀ N) (flip_char ψ₀) ⟨u, hu⟩ ⟨u', hu'⟩ g ?_` and prove the remaining obligations. Distinguish the cases in `hadm : MonoAdm π t`. Use `left`.

Use `⟨1, 1, ?_, by simp⟩` and prove the remaining obligations. Rewrite using `[flip_mono _ π t hn hadm]`. Simplify using the standard rewrite rules. Use `right`. Conclude with `mono_not_adm ψ₀ hψ _ π t ht hn hadm`.
-/
theorem gelfand_graev_multiplicity_one : GelfandGraevMultOne := by
  intro K V _ _ _ _ _ N ψ₀ ρ hψ hirr
  classical
  have : Fintype (GL (Fin N) K) := Fintype.ofFinite _
  rw [besselSpace_zero_eq_equivariant]
  refine gelfand_trick ρ (uniSub K N) (uniChar ψ₀ N) ?_ hirr
  refine hecke_comm flipG flipG_mul flipG_flipG (uniSub K N) (uniChar ψ₀ N) (flip_char ψ₀) ?_
  intro g
  obtain ⟨u, u', hu, hu', π, t, ht, hn⟩ := bruhat_exists g
  refine GTAlt.transfer flipG flipG_mul (uniSub K N) (uniChar ψ₀ N) (flip_char ψ₀) ⟨u, hu⟩ ⟨u', hu'⟩
    g ?_
  by_cases hadm : MonoAdm π t
  · left
    refine ⟨1, 1, ?_, by simp⟩
    rw [flip_mono _ π t hn hadm]
    simp
  · right
    exact mono_not_adm ψ₀ hψ _ π t ht hn hadm

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end
