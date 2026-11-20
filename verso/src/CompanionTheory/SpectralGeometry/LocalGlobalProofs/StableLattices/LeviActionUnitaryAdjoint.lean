import Mathlib
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.FarRegularity.LKTExists
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.CreationOperators.DifferentialBoundedSupport

open Finset CompanionTheory.RgExh CompanionTheory.RgExh.U
open CompanionTheory.D.LK (Pos Cn ann cre lift bd om cpt allT LocFin sg)
open CompanionTheory.D.LK.Car (ann_apply cre_apply sg_erase tw_self)
open Formalism.REAL (GlRel KHighest IsWeight)
open CompanionTheory.D.DSIC (KUnit)
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.RgExhFarReg.ChainAdj

variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

def ip (x z : Cn n V) : ℂ := ∑ A, ⟪x A, z A⟫_ℂ

/- English proof (translation)
Unfold `sg`. Simplify using the standard rewrite rules.
-/
theorem sg_conj (i : Pos n) (A : Finset (Pos n)) : (starRingEnd ℂ) (sg i A) = sg i A := by
  unfold sg
  simp

/- English proof (translation)
Rewrite using `[sg_erase i h, tw_self, one_mul]`.
-/
theorem sg_erase_self (i : Pos n) {A : Finset (Pos n)} (h : i ∈ A) : sg i (A.erase i) = sg i A := by
  rw [sg_erase i h, tw_self, one_mul]

/- English proof (translation)
Unfold `ip`. Establish `h1 : ∀ A : Finset (Pos n), ⟪cre i x A, z A⟫_ℂ = if i ∈ A then sg i A * ⟪x (A.erase i), z A⟫_ℂ else 0` using `fun A => by`. Rewrite using `[cre_apply]`. Use `split_ifs`. Rewrite using `[inner_smul_left, sg_conj]`.

Simplify using the standard rewrite rules. Establish `h2 : ∀ A : Finset (Pos n), ⟪x A, ann i z A⟫_ℂ = if i ∈ A then 0 else sg i A * ⟪x A, z (insert i A)⟫_ℂ` using `fun A => by`. Rewrite using `[ann_apply]`. Use `split_ifs`. Simplify using the standard rewrite rules.

Rewrite using `[inner_smul_right]`. Simplify using `only [h1, h2]`. Rewrite using `[← Finset.sum_filter, Finset.sum_ite, Finset.sum_const_zero, zero_add]`. Use `Finset.sum_bij' (fun A _ => A.erase i) (fun A _ => insert i A) ?_ ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `A hA`.

Simplify using the standard rewrite rules. Introduce `A hA`. Simplify using the standard rewrite rules. Introduce `A hA`. Conclude with `Finset.insert_erase (by simpa using hA)`.

Introduce `A hA`. Conclude with `Finset.erase_insert (by simpa using hA)`. Introduce `A hA`. Establish `hA' : i ∈ A` using `by simpa using hA`. Rewrite using `[sg_erase_self i hA', Finset.insert_erase hA']`.
-/
theorem ip_cre (i : Pos n) (x z : Cn n V) : ip (cre i x) z = ip x (ann i z) := by
  unfold ip
  have h1 : ∀ A : Finset (Pos n), ⟪cre i x A, z A⟫_ℂ =
      if i ∈ A then sg i A * ⟪x (A.erase i), z A⟫_ℂ else 0 := fun A => by
    rw [cre_apply]
    split_ifs
    · rw [inner_smul_left, sg_conj]
    · simp
  have h2 : ∀ A : Finset (Pos n), ⟪x A, ann i z A⟫_ℂ =
      if i ∈ A then 0 else sg i A * ⟪x A, z (insert i A)⟫_ℂ := fun A => by
    rw [ann_apply]
    split_ifs
    · simp
    · rw [inner_smul_right]
  simp only [h1, h2]
  rw [← Finset.sum_filter, Finset.sum_ite, Finset.sum_const_zero, zero_add]
  refine Finset.sum_bij' (fun A _ => A.erase i) (fun A _ => insert i A) ?_ ?_ ?_ ?_ ?_
  · intro A hA
    simp
  · intro A hA
    simp
  · intro A hA
    exact Finset.insert_erase (by simpa using hA)
  · intro A hA
    exact Finset.erase_insert (by simpa using hA)
  · intro A hA
    have hA' : i ∈ A := by simpa using hA
    rw [sg_erase_self i hA', Finset.insert_erase hA']

/- English proof (translation)
Unfold `ip`. Rewrite using `[map_sum]`. Conclude with `Finset.sum_congr rfl fun A _ => inner_conj_symm _ _`.
-/
theorem ip_conj (x z : Cn n V) : (starRingEnd ℂ) (ip x z) = ip z x := by
  unfold ip
  rw [map_sum]
  exact Finset.sum_congr rfl fun A _ => inner_conj_symm _ _

/- English proof (translation)
Rewrite using `[← ip_conj, ← ip_cre, ip_conj]`.
-/
theorem ip_ann (i : Pos n) (x z : Cn n V) : ip (ann i x) z = ip x (cre i z) := by
  rw [← ip_conj, ← ip_cre, ip_conj]

/- English proof (translation)
Simplify using `only [Module.End.mul_apply]`. Rewrite using `[ip_cre, ip_ann]`.
-/
theorem ip_cre_ann (i k : Pos n) (x z : Cn n V) :
    ip ((cre k * ann i : Module.End ℂ (Cn n V)) x) z = ip x ((cre i * ann k : Module.End ℂ (Cn n V)) z) := by
  simp only [Module.End.mul_apply]
  rw [ip_cre, ip_ann]

/- English proof (translation)
Simplify using `only [ip, Pi.add_apply, inner_add_left, Finset.sum_add_distrib]`.
-/
theorem ip_add_left (x y z : Cn n V) : ip (x + y) z = ip x z + ip y z := by
  simp only [ip, Pi.add_apply, inner_add_left, Finset.sum_add_distrib]

/- English proof (translation)
Simplify using `only [ip, Pi.add_apply, inner_add_right, Finset.sum_add_distrib]`.
-/
theorem ip_add_right (x y z : Cn n V) : ip x (y + z) = ip x y + ip x z := by
  simp only [ip, Pi.add_apply, inner_add_right, Finset.sum_add_distrib]

/- English proof (translation)
Simplify using `only [ip, Pi.smul_apply, inner_smul_left, Finset.mul_sum]`.
-/
theorem ip_smul_left (c : ℂ) (x z : Cn n V) : ip (c • x) z = (starRingEnd ℂ) c * ip x z := by
  simp only [ip, Pi.smul_apply, inner_smul_left, Finset.mul_sum]

/- English proof (translation)
Simplify using `only [ip, Pi.smul_apply, inner_smul_right, Finset.mul_sum]`.
-/
theorem ip_smul_right (c : ℂ) (x z : Cn n V) : ip x (c • z) = c * ip x z := by
  simp only [ip, Pi.smul_apply, inner_smul_right, Finset.mul_sum]

/- English proof (translation)
Simplify using `only [ip, Finset.sum_apply, sum_inner]`. Conclude with `Finset.sum_comm`.
-/
theorem ip_sum_left {ι : Type} (s : Finset ι) (f : ι → Cn n V) (z : Cn n V) :
    ip (∑ a ∈ s, f a) z = ∑ a ∈ s, ip (f a) z := by
  simp only [ip, Finset.sum_apply, sum_inner]
  exact Finset.sum_comm

/- English proof (translation)
Simplify using `only [ip, Finset.sum_apply, inner_sum]`. Conclude with `Finset.sum_comm`.
-/
theorem ip_sum_right {ι : Type} (s : Finset ι) (x : Cn n V) (f : ι → Cn n V) :
    ip x (∑ a ∈ s, f a) = ∑ a ∈ s, ip x (f a) := by
  simp only [ip, Finset.sum_apply, inner_sum]
  exact Finset.sum_comm

/- English proof (translation)
Unfold `adC`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem adC_conj (p q : Fin n) (i k : Pos n) : (starRingEnd ℂ) (adC p q i k) = adC p q i k := by
  unfold adC
  split_ifs <;> simp

/- English proof (translation)
Establish `e1 : (q = i.1.1 ∧ k.1 = (p, i.1.2)) ↔ (p = k.1.1 ∧ i.1 = (q, k.1.2))`. Take `⟨⟨a, b⟩, hi⟩` from `i`. Take `⟨⟨c, d⟩, hk⟩` from `k`. Simplify using `only [Prod.mk.injEq]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨rfl, rfl, rfl⟩`. Conclude with `⟨rfl, rfl, rfl⟩`. Introduce and unpack `⟨rfl, rfl, rfl⟩`. Conclude with `⟨rfl, rfl, rfl⟩`. Establish `e2 : (i.1.2 = p ∧ k.1 = (i.1.1, q)) ↔ (k.1.2 = q ∧ i.1 = (k.1.1, p))`.

Take `⟨⟨a, b⟩, hi⟩` from `i`. Take `⟨⟨c, d⟩, hk⟩` from `k`. Simplify using `only [Prod.mk.injEq]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨rfl, rfl, rfl⟩`.

Conclude with `⟨rfl, rfl, rfl⟩`. Introduce and unpack `⟨rfl, rfl, rfl⟩`. Conclude with `⟨rfl, rfl, rfl⟩`. Unfold `adC`. Simplify using `only [e1, e2]`.
-/
theorem adC_swap (p q : Fin n) (i k : Pos n) : adC p q i k = adC q p k i := by
  have e1 : (q = i.1.1 ∧ k.1 = (p, i.1.2)) ↔ (p = k.1.1 ∧ i.1 = (q, k.1.2)) := by
    obtain ⟨⟨a, b⟩, hi⟩ := i
    obtain ⟨⟨c, d⟩, hk⟩ := k
    simp only [Prod.mk.injEq]
    constructor
    · rintro ⟨rfl, rfl, rfl⟩; exact ⟨rfl, rfl, rfl⟩
    · rintro ⟨rfl, rfl, rfl⟩; exact ⟨rfl, rfl, rfl⟩
  have e2 : (i.1.2 = p ∧ k.1 = (i.1.1, q)) ↔ (k.1.2 = q ∧ i.1 = (k.1.1, p)) := by
    obtain ⟨⟨a, b⟩, hi⟩ := i
    obtain ⟨⟨c, d⟩, hk⟩ := k
    simp only [Prod.mk.injEq]
    constructor
    · rintro ⟨rfl, rfl, rfl⟩; exact ⟨rfl, rfl, rfl⟩
    · rintro ⟨rfl, rfl, rfl⟩; exact ⟨rfl, rfl, rfl⟩
  unfold adC
  simp only [e1, e2]

/- English proof (translation)
Simplify using `only [adL, LinearMap.sum_apply, LinearMap.smul_apply, ip_sum_left, ip_sum_right, ip_smul_left, ip_smul_right, adC_conj, ip_cre_ann]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[adC_swap]`.
-/
theorem ip_adL (p q : Fin n) (x z : Cn n V) : ip (adL p q x) z = ip x (adL q p z) := by
  simp only [adL, LinearMap.sum_apply, LinearMap.smul_apply, ip_sum_left, ip_sum_right, ip_smul_left,
    ip_smul_right, adC_conj, ip_cre_ann]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
  rw [adC_swap]

/- English proof (translation)
The claim follows from `Finset.sum_congr rfl fun A _ => hU p q h (x A) (z A)`.
-/
theorem ip_lift {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ V} (hU : KUnit ε E) {p q : Fin n}
    (h : ε p = ε q) (x z : Cn n V) : ip (lift n (E p q) x) z = ip x (lift n (E q p) z) :=
  Finset.sum_congr rfl fun A _ => hU p q h (x A) (z A)

/- English proof (translation)
Introduce `n ε V _ _ E hU p q h x z`. Express the relevant statement in the definitionally equal form `ip (lF E p q x) z = ip x (lF E q p z)`. Simplify using `only [lF, LinearMap.add_apply, ip_add_left, ip_add_right]`. Rewrite using `[ip_lift hU h, ip_adL]`.
-/
theorem lF_adjoint : ∀ (n : ℕ) (ε : Fin n → Bool) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (E : Fin n → Fin n → Module.End ℂ V), KUnit ε E → ∀ p q : Fin n, ε p = ε q → ∀ x z : Cn n V,
      ∑ A, ⟪lF E p q x A, z A⟫_ℂ = ∑ A, ⟪x A, lF E q p z A⟫_ℂ := by
  intro n ε V _ _ E hU p q h x z
  change ip (lF E p q x) z = ip x (lF E q p z)
  simp only [lF, LinearMap.add_apply, ip_add_left, ip_add_right]
  rw [ip_lift hU h, ip_adL]

end GlobalTheory.CompanionTheory.RgExhFarReg.ChainAdj
