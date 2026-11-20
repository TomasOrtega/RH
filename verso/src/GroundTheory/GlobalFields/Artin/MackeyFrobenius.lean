import Mathlib
import GroundTheory.GlobalFields.Artin.Mackey
set_option maxSynthPendingDepth 1

noncomputable section

open scoped Pointwise

namespace GroundTheory.Global.Artin

open GroundTheory.LocalField

section Cyclic

variable {Γ : Type*} [Group Γ] {N : Subgroup Γ} [N.Normal] {g : Γ}

/- English proof (translation)
Establish `ha : a ∈ Subgroup.zpowers c` using `by rw [h]; exact Subgroup.mem_top a`. Establish `hb : b ∈ Subgroup.zpowers c` using `by rw [h]; exact Subgroup.mem_top b`. Take `⟨j, rfl⟩` from `Subgroup.mem_zpowers_iff.1 ha`. Take `⟨k, rfl⟩` from `Subgroup.mem_zpowers_iff.1 hb`. Conclude with `zpow_mul_comm c j k`.
-/
theorem mul_comm_of_zpowers_eq_top {Q : Type*} [Group Q] {c : Q} (h : Subgroup.zpowers c = ⊤)
    (a b : Q) : a * b = b * a := by
  have ha : a ∈ Subgroup.zpowers c := by rw [h]; exact Subgroup.mem_top a
  have hb : b ∈ Subgroup.zpowers c := by rw [h]; exact Subgroup.mem_top b
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
  exact zpow_mul_comm c j k

/- English proof (translation)
Rewrite using `[← QuotientGroup.eq]`. Simplify using `only [QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_zpow]`. Rewrite using `[mul_comm_of_zpowers_eq_top hgen (a : Γ ⧸ N)⁻¹, inv_mul_cancel_right]`.
-/
theorem zpow_inv_mul_conj_mem (hgen : Subgroup.zpowers (g : Γ ⧸ N) = ⊤) (a : Γ) (m : ℤ) :
    (g ^ m)⁻¹ * (a⁻¹ * g ^ m * a) ∈ N := by
  rw [← QuotientGroup.eq]
  simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_zpow]
  rw [mul_comm_of_zpowers_eq_top hgen (a : Γ ⧸ N)⁻¹, inv_mul_cancel_right]

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun n hn a ↦ by have h1 : a * n * a⁻¹ * n⁻¹ ∈ N := by rw [← QuotientGroup.eq_one_iff] simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv] rw [mul_comm_of_zpowers_eq_top hgen (a : Γ ⧸ N) (n : Γ ⧸ N)] group have := K.mul_mem (hNK h1) hn simpa using this⟩`.
-/
theorem normal_of_le_of_zpowers_eq_top (hgen : Subgroup.zpowers (g : Γ ⧸ N) = ⊤)
    {K : Subgroup Γ} (hNK : N ≤ K) : K.Normal := ⟨fun n hn a ↦ by
  have h1 : a * n * a⁻¹ * n⁻¹ ∈ N := by
    rw [← QuotientGroup.eq_one_iff]
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rw [mul_comm_of_zpowers_eq_top hgen (a : Γ ⧸ N) (n : Γ ⧸ N)]
    group
  have := K.mul_mem (hNK h1) hn
  simpa using this⟩

/- English proof (translation)
Use `normal_of_le_of_zpowers_eq_top hgen hNK` as an intermediate fact. Establish `hgenK : ∀ y : Γ ⧸ K, y ∈ Subgroup.zpowers (g : Γ ⧸ K)`. Introduce `y`. Proceed by induction on `y using QuotientGroup.induction_on with | H d => ?_`. Establish `hd : (d : Γ ⧸ N) ∈ Subgroup.zpowers (g : Γ ⧸ N)` using `by rw [hgen]; exact Subgroup.mem_top _`.

Take `⟨j, hj⟩` from `Subgroup.mem_zpowers_iff.1 hd`. Use `Subgroup.mem_zpowers_iff.2 ⟨j, ?_⟩` and prove the remaining obligations. Rewrite using `[← QuotientGroup.mk_zpow, QuotientGroup.eq]`. Rewrite `hj` using `[← QuotientGroup.mk_zpow, QuotientGroup.eq]`. Conclude with `hNK hj`.

Rewrite using `[Subgroup.index_eq_card, ← orderOf_eq_card_of_forall_mem_zpowers hgenK, orderOf_dvd_iff_zpow_eq_one, ← QuotientGroup.mk_zpow, QuotientGroup.eq_one_iff]`.
-/
theorem zpow_mem_iff_index_dvd [Finite Γ] (hgen : Subgroup.zpowers (g : Γ ⧸ N) = ⊤)
    {K : Subgroup Γ} (hNK : N ≤ K) (m : ℤ) : g ^ m ∈ K ↔ (K.index : ℤ) ∣ m := by
  have := normal_of_le_of_zpowers_eq_top hgen hNK
  have hgenK : ∀ y : Γ ⧸ K, y ∈ Subgroup.zpowers (g : Γ ⧸ K) := by
    intro y
    induction y using QuotientGroup.induction_on with | H d => ?_
    have hd : (d : Γ ⧸ N) ∈ Subgroup.zpowers (g : Γ ⧸ N) := by rw [hgen]; exact Subgroup.mem_top _
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 hd
    refine Subgroup.mem_zpowers_iff.2 ⟨j, ?_⟩
    rw [← QuotientGroup.mk_zpow, QuotientGroup.eq]
    rw [← QuotientGroup.mk_zpow, QuotientGroup.eq] at hj
    exact hNK hj
  rw [Subgroup.index_eq_card, ← orderOf_eq_card_of_forall_mem_zpowers hgenK,
    orderOf_dvd_iff_zpow_eq_one, ← QuotientGroup.mk_zpow, QuotientGroup.eq_one_iff]

end Cyclic

section Frobenius

variable {G : Type*} [Group G]

def frobIndex (H D I : Subgroup G) (x : G) : ℕ :=
  (I ⊔ ((MulAut.conj x⁻¹ • H : Subgroup G) ⊓ D)).relIndex D

def cosetAvg {Γ : Type*} [Group Γ] (I : Subgroup Γ) [Fintype I] (φ : Γ) (F : Γ → ℂ) (m : ℤ) :
    ℂ :=
  (Nat.card I : ℂ)⁻¹ * ∑ i : I, F (φ ^ m * i)

variable {H D I : Subgroup G}

/- English proof (translation)
Use `hN.conj_mem ⟨i, hID hi⟩ (Subgroup.mem_subgroupOf.2 hi) (⟨t, ht⟩⁻¹)` as an intermediate fact. Simplify using `using Subgroup.mem_subgroupOf.1 this`.
-/
theorem inv_mul_mul_mem_of_normal (hID : I ≤ D) [hN : (I.subgroupOf D).Normal] {t i : G}
    (ht : t ∈ D) (hi : i ∈ I) : t⁻¹ * i * t ∈ I := by
  have := hN.conj_mem ⟨i, hID hi⟩ (Subgroup.mem_subgroupOf.2 hi) (⟨t, ht⟩⁻¹)
  simpa using Subgroup.mem_subgroupOf.1 this

/- English proof (translation)
Use `zpow_inv_mul_conj_mem hgen ⟨t, ht⟩ m` as an intermediate fact. Simplify using `using Subgroup.mem_subgroupOf.1 this`.
-/
theorem zpow_inv_mul_conj_mem_of_le [(I.subgroupOf D).Normal] {φ : G} (hφ : φ ∈ D)
    (hgen : Subgroup.zpowers ((⟨φ, hφ⟩ : D) : D ⧸ I.subgroupOf D) = ⊤) {t : G} (ht : t ∈ D)
    (m : ℤ) : (φ ^ m)⁻¹ * (t⁻¹ * φ ^ m * t) ∈ I := by
  have := zpow_inv_mul_conj_mem hgen ⟨t, ht⟩ m
  simpa using Subgroup.mem_subgroupOf.1 this

/- English proof (translation)
Establish `h : ((⟨a, ha⟩ : D) : D ⧸ I.subgroupOf D) = ((⟨b, hb⟩ : D) : D ⧸ I.subgroupOf D)`. Rewrite using `[QuotientGroup.eq, Subgroup.mem_subgroupOf]`. Simplify using `using hab`. Establish `h2 : (((⟨a, ha⟩ : D) ^ k : D) : D ⧸ I.subgroupOf D) = (((⟨b, hb⟩ : D) ^ k : D) : D ⧸ I.subgroupOf D)`. Rewrite using `[QuotientGroup.mk_zpow, QuotientGroup.mk_zpow, h]`.

Rewrite `h2` using `[QuotientGroup.eq, Subgroup.mem_subgroupOf]`. Simplify using `using h2`.
-/
theorem zpow_inv_mul_zpow_mem [(I.subgroupOf D).Normal] {a b : G} (ha : a ∈ D) (hb : b ∈ D)
    (hab : a⁻¹ * b ∈ I) (k : ℤ) : (a ^ k)⁻¹ * b ^ k ∈ I := by
  have h : ((⟨a, ha⟩ : D) : D ⧸ I.subgroupOf D) = ((⟨b, hb⟩ : D) : D ⧸ I.subgroupOf D) := by
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simpa using hab
  have h2 : (((⟨a, ha⟩ : D) ^ k : D) : D ⧸ I.subgroupOf D) =
      (((⟨b, hb⟩ : D) ^ k : D) : D ⧸ I.subgroupOf D) := by
    rw [QuotientGroup.mk_zpow, QuotientGroup.mk_zpow, h]
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at h2
  simpa using h2

/- English proof (translation)
Establish `h` using `zpow_mem_iff_index_dvd hgen (K := K.subgroupOf D) (fun y hy ↦ Subgroup.mem_subgroupOf.2 (hIK (Subgroup.mem_subgroupOf.1 hy))) m`. Rewrite `h` using `[Subgroup.mem_subgroupOf]`. Simplify `h` using `[Subgroup.relIndex]`.
-/
theorem zpow_mem_iff_relIndex_dvd [Finite G] [(I.subgroupOf D).Normal] {φ : G} (hφ : φ ∈ D)
    (hgen : Subgroup.zpowers ((⟨φ, hφ⟩ : D) : D ⧸ I.subgroupOf D) = ⊤) {K : Subgroup G}
    (hIK : I ≤ K) (m : ℤ) : φ ^ m ∈ K ↔ (K.relIndex D : ℤ) ∣ m := by
  have h := zpow_mem_iff_index_dvd hgen (K := K.subgroupOf D)
    (fun y hy ↦ Subgroup.mem_subgroupOf.2 (hIK (Subgroup.mem_subgroupOf.1 hy))) m
  rw [Subgroup.mem_subgroupOf] at h
  simpa [Subgroup.relIndex] using h

/- English proof (translation)
Rewrite using `[← Finset.sum_filter_of_ne (p := fun i : I ↦ x * i * x⁻¹ ∈ H) (fun i _ hne ↦ by`. Assume the negation of the conclusion as `h`. Conclude with `hne (hF _ h))]`. Use `Finset.sum_bij' (fun i hi ↦ ⟨⟨x * i * x⁻¹, (Finset.mem_filter.1 hi).2⟩, ?_⟩) (fun j _ ↦ ⟨x⁻¹ * ((j : H) : G) * x, (mem_conj_smul_iff I x _).1 (Subgroup.mem_subgroupOf.1 j.2)⟩) ?_ ?_ ?_ ?_ ?_` and prove the remaining obligations. Name the introduced variables `i hi`.

Rewrite using `[Subgroup.mem_subgroupOf, mem_conj_smul_iff]`. Express the relevant statement in the definitionally equal form `x⁻¹ * (x * (i : G) * x⁻¹) * x ∈ I`. Rewrite using `[show x⁻¹ * (x * (i : G) * x⁻¹) * x = i by group]`. Conclude with `i.2`. Introduce `i _`.

Conclude with `Finset.mem_univ _`. Introduce `j _`. Rewrite using `[Finset.mem_filter]`. Use `⟨Finset.mem_univ _, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `x * (x⁻¹ * ((j : H) : G) * x) * x⁻¹ ∈ H`.

Rewrite using `[show x * (x⁻¹ * ((j : H) : G) * x) * x⁻¹ = (j : H) by group]`. Conclude with `(j : H).2`. Introduce `i _`. Apply `Subtype.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `x⁻¹ * (x * (i : G) * x⁻¹) * x = i`.

Use `group`. Introduce `j _`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `x * (x⁻¹ * ((j : H) : G) * x) * x⁻¹ = (j : H)`.

Use `group`. Introduce `i _`. Both sides reduce to the same expression.
-/
theorem sum_conj_eq_sum_subgroupOf (H I : Subgroup G) [Fintype I] (x : G)
    [Fintype ((MulAut.conj x • I : Subgroup G).subgroupOf H)] (F : G → ℂ)
    (hF : ∀ g ∉ H, F g = 0) :
    ∑ i : I, F (x * i * x⁻¹) =
      ∑ j : (MulAut.conj x • I : Subgroup G).subgroupOf H, F ((j : H) : G) := by
  classical
  rw [← Finset.sum_filter_of_ne (p := fun i : I ↦ x * i * x⁻¹ ∈ H)
    (fun i _ hne ↦ by
      by_contra h
      exact hne (hF _ h))]
  refine Finset.sum_bij' (fun i hi ↦ ⟨⟨x * i * x⁻¹, (Finset.mem_filter.1 hi).2⟩, ?_⟩)
    (fun j _ ↦ ⟨x⁻¹ * ((j : H) : G) * x,
      (mem_conj_smul_iff I x _).1 (Subgroup.mem_subgroupOf.1 j.2)⟩) ?_ ?_ ?_ ?_ ?_
  · rename_i i hi
    rw [Subgroup.mem_subgroupOf, mem_conj_smul_iff]
    change x⁻¹ * (x * (i : G) * x⁻¹) * x ∈ I
    rw [show x⁻¹ * (x * (i : G) * x⁻¹) * x = i by group]
    exact i.2
  · intro i _
    exact Finset.mem_univ _
  · intro j _
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    change x * (x⁻¹ * ((j : H) : G) * x) * x⁻¹ ∈ H
    rw [show x * (x⁻¹ * ((j : H) : G) * x) * x⁻¹ = (j : H) by group]
    exact (j : H).2
  · intro i _
    apply Subtype.ext
    change x⁻¹ * (x * (i : G) * x⁻¹) * x = i
    group
  · intro j _
    apply Subtype.ext
    apply Subtype.ext
    change x * (x⁻¹ * ((j : H) : G) * x) * x⁻¹ = (j : H)
    group
  · intro i _
    rfl

/- English proof (translation)
Take `⟨c, hcdef⟩ : ∃ c, c = (φ ^ m)⁻¹ * (t⁻¹ * φ ^ m * t)` from `⟨_, rfl⟩`. Establish `hc : c ∈ I` using `hcdef ▸ zpow_inv_mul_conj_mem_of_le hφ hgen ht m`. Set `σ : I → I` to `fun i ↦ ⟨c * (t⁻¹ * i * t), I.mul_mem hc (inv_mul_mul_mem_of_normal hID ht i.2)⟩`. Establish `hσ : Function.Injective σ`. Introduce `i j hij`.

Establish `h1 : c * (t⁻¹ * (i : G) * t) = c * (t⁻¹ * (j : G) * t)` using `congrArg Subtype.val hij`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `using h1`. Use `Fintype.sum_bijective σ (Finite.injective_iff_bijective.1 hσ) _ _ fun i ↦ ?_` and prove the remaining obligations. Use `congr 1`.

Express the relevant statement in the definitionally equal form `t⁻¹ * (φ ^ m * i) * t = φ ^ m * (c * (t⁻¹ * i * t))`. Rewrite using `[hcdef]`. Use `group`.
-/
theorem sum_conj_coset [Fintype I] (hID : I ≤ D) [(I.subgroupOf D).Normal] {φ : G} (hφ : φ ∈ D)
    (hgen : Subgroup.zpowers ((⟨φ, hφ⟩ : D) : D ⧸ I.subgroupOf D) = ⊤) {t : G} (ht : t ∈ D)
    (F : G → ℂ) (m : ℤ) :
    ∑ i : I, F (t⁻¹ * (φ ^ m * i) * t) = ∑ i : I, F (φ ^ m * i) := by
  obtain ⟨c, hcdef⟩ : ∃ c, c = (φ ^ m)⁻¹ * (t⁻¹ * φ ^ m * t) := ⟨_, rfl⟩
  have hc : c ∈ I := hcdef ▸ zpow_inv_mul_conj_mem_of_le hφ hgen ht m
  let σ : I → I := fun i ↦ ⟨c * (t⁻¹ * i * t), I.mul_mem hc (inv_mul_mul_mem_of_normal hID ht i.2)⟩
  have hσ : Function.Injective σ := by
    intro i j hij
    have h1 : c * (t⁻¹ * (i : G) * t) = c * (t⁻¹ * (j : G) * t) := congrArg Subtype.val hij
    apply Subtype.ext
    simpa using h1
  refine Fintype.sum_bijective σ (Finite.injective_iff_bijective.1 hσ) _ _ fun i ↦ ?_
  congr 1
  change t⁻¹ * (φ ^ m * i) * t = φ ^ m * (c * (t⁻¹ * i * t))
  rw [hcdef]
  group

/- English proof (translation)
Use `set I' := I.subgroupOf D with hI'`. Use `set E := (MulAut.conj x⁻¹ • H : Subgroup G).subgroupOf D with hE`. Establish `hK : (I ⊔ ((MulAut.conj x⁻¹ • H : Subgroup G) ⊓ D)).subgroupOf D = I' ⊔ E`. Rewrite using `[Subgroup.subgroupOf_sup hID inf_le_right, Subgroup.inf_subgroupOf_right]`. Establish `hr : frobIndex H D I x = (I' ⊔ E).index`.

Rewrite using `[frobIndex, Subgroup.relIndex, hK]`. Establish `h1 : Nat.card D = Nat.card (I' ⊔ E : Subgroup D) * (I' ⊔ E).index` using `(Subgroup.card_mul_index _).symm`. Establish `h2 : Nat.card (I' ⊔ E : Subgroup D) = Nat.card I' * I'.relIndex E`. Rewrite using `[← Subgroup.relIndex_sup_left, ← Subgroup.card_mul_index (I'.subgroupOf (I' ⊔ E)), Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_left : I' ≤ I' ⊔ E)).toEquiv]`. Both sides reduce to the same expression.

Establish `h3 : Nat.card E = Nat.card (I'.subgroupOf E) * I'.relIndex E` using `(Subgroup.card_mul_index _).symm`. Establish `h4 : Nat.card I' = Nat.card I` using `Nat.card_congr (Subgroup.subgroupOfEquivOfLe hID).toEquiv`. Establish `hw : ∀ w : (MulAut.conj x • I : Subgroup G).subgroupOf H, x⁻¹ * ((w : H) : G) * x ∈ I` using `fun w ↦ (mem_conj_smul_iff I x _).1 (Subgroup.mem_subgroupOf.1 w.2)`. Establish `h5 : Nat.card ((MulAut.conj x • I : Subgroup G).subgroupOf H) = Nat.card (I'.subgroupOf E)`. Use `Nat.card_congr { toFun := fun w ↦ ⟨⟨⟨x⁻¹ * ((w : H) : G) * x, hID (hw w)⟩, ?_⟩, ?_⟩ invFun := fun z ↦ ⟨⟨x * (((z : E) : D) : G) * x⁻¹, ?_⟩, ?_⟩ left_inv := ?_ right_inv := ?_ }` and prove the remaining obligations.

Name the introduced variables `w`. Rewrite using `[hE, Subgroup.mem_subgroupOf, mem_conj_inv_smul_iff]`. Express the relevant statement in the definitionally equal form `x * (x⁻¹ * ((w : H) : G) * x) * x⁻¹ ∈ H`. Rewrite using `[show x * (x⁻¹ * ((w : H) : G) * x) * x⁻¹ = (w : H) by group]`. Conclude with `(w : H).2`.

Name the introduced variables `w`. Rewrite using `[Subgroup.mem_subgroupOf, hI', Subgroup.mem_subgroupOf]`. Conclude with `hw w`. Name the introduced variables `z`. Conclude with `(mem_conj_inv_smul_iff H x _).1 (Subgroup.mem_subgroupOf.1 (z : E).2)`.

Name the introduced variables `z`. Rewrite using `[Subgroup.mem_subgroupOf, mem_conj_smul_iff]`. Express the relevant statement in the definitionally equal form `x⁻¹ * (x * (((z : E) : D) : G) * x⁻¹) * x ∈ I`. Rewrite using `[show x⁻¹ * (x * (((z : E) : D) : G) * x⁻¹) * x = ((z : E) : D) by group]`. Conclude with `Subgroup.mem_subgroupOf.1 (Subgroup.mem_subgroupOf.1 z.2)`.

Introduce `w`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `x * (x⁻¹ * ((w : H) : G) * x) * x⁻¹ = (w : H)`. Use `group`.

Introduce `z`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `x⁻¹ * (x * (((z : E) : D) : G) * x⁻¹) * x = ((z : E) : D)`.

Use `group`. Rewrite using `[h1, h2, h3, h4, h5, hr]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem card_mul_card_eq [Finite G] (hID : I ≤ D) [hN : (I.subgroupOf D).Normal] (x : G) :
    Nat.card D * Nat.card ((MulAut.conj x • I : Subgroup G).subgroupOf H) =
      frobIndex H D I x * Nat.card I *
        Nat.card ((MulAut.conj x⁻¹ • H : Subgroup G).subgroupOf D) := by
  set I' := I.subgroupOf D with hI'
  set E := (MulAut.conj x⁻¹ • H : Subgroup G).subgroupOf D with hE
  have hK : (I ⊔ ((MulAut.conj x⁻¹ • H : Subgroup G) ⊓ D)).subgroupOf D = I' ⊔ E := by
    rw [Subgroup.subgroupOf_sup hID inf_le_right, Subgroup.inf_subgroupOf_right]
  have hr : frobIndex H D I x = (I' ⊔ E).index := by
    rw [frobIndex, Subgroup.relIndex, hK]
  have h1 : Nat.card D = Nat.card (I' ⊔ E : Subgroup D) * (I' ⊔ E).index :=
    (Subgroup.card_mul_index _).symm
  have h2 : Nat.card (I' ⊔ E : Subgroup D) = Nat.card I' * I'.relIndex E := by
    rw [← Subgroup.relIndex_sup_left, ← Subgroup.card_mul_index (I'.subgroupOf (I' ⊔ E)),
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_left : I' ≤ I' ⊔ E)).toEquiv]
    rfl
  have h3 : Nat.card E = Nat.card (I'.subgroupOf E) * I'.relIndex E :=
    (Subgroup.card_mul_index _).symm
  have h4 : Nat.card I' = Nat.card I := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hID).toEquiv
  have hw : ∀ w : (MulAut.conj x • I : Subgroup G).subgroupOf H, x⁻¹ * ((w : H) : G) * x ∈ I :=
    fun w ↦ (mem_conj_smul_iff I x _).1 (Subgroup.mem_subgroupOf.1 w.2)
  have h5 : Nat.card ((MulAut.conj x • I : Subgroup G).subgroupOf H) =
      Nat.card (I'.subgroupOf E) := by
    refine Nat.card_congr
      { toFun := fun w ↦ ⟨⟨⟨x⁻¹ * ((w : H) : G) * x, hID (hw w)⟩, ?_⟩, ?_⟩
        invFun := fun z ↦ ⟨⟨x * (((z : E) : D) : G) * x⁻¹, ?_⟩, ?_⟩
        left_inv := ?_
        right_inv := ?_ }
    · rename_i w
      rw [hE, Subgroup.mem_subgroupOf, mem_conj_inv_smul_iff]
      change x * (x⁻¹ * ((w : H) : G) * x) * x⁻¹ ∈ H
      rw [show x * (x⁻¹ * ((w : H) : G) * x) * x⁻¹ = (w : H) by group]
      exact (w : H).2
    · rename_i w
      rw [Subgroup.mem_subgroupOf, hI', Subgroup.mem_subgroupOf]
      exact hw w
    · rename_i z
      exact (mem_conj_inv_smul_iff H x _).1 (Subgroup.mem_subgroupOf.1 (z : E).2)
    · rename_i z
      rw [Subgroup.mem_subgroupOf, mem_conj_smul_iff]
      change x⁻¹ * (x * (((z : E) : D) : G) * x⁻¹) * x ∈ I
      rw [show x⁻¹ * (x * (((z : E) : D) : G) * x⁻¹) * x = ((z : E) : D) by group]
      exact Subgroup.mem_subgroupOf.1 (Subgroup.mem_subgroupOf.1 z.2)
    · intro w
      apply Subtype.ext
      apply Subtype.ext
      change x * (x⁻¹ * ((w : H) : G) * x) * x⁻¹ = (w : H)
      group
    · intro z
      apply Subtype.ext
      apply Subtype.ext
      apply Subtype.ext
      change x⁻¹ * (x * (((z : E) : D) : G) * x⁻¹) * x = ((z : E) : D)
      group
  rw [h1, h2, h3, h4, h5, hr]
  ring

end Frobenius

section Formula

variable {G : Type*} [Group G] [Fintype G] {H D I : Subgroup G}

open Classical in

/- English proof (translation)
Use `set K : Subgroup G := I ⊔ ((MulAut.conj x⁻¹ • H : Subgroup G) ⊓ D) with hK`. Establish `hIK : I ≤ K` using `le_sup_left`. Establish `hKr : ∀ n : ℤ, φ ^ n ∈ K ↔ (frobIndex H D I x : ℤ) ∣ n` using `zpow_mem_iff_relIndex_dvd hφ hgen hIK`. Repeatedly rewrite using `[indFun_subtype_apply, extendByZero_conjFun]`. Rewrite using `[← Finset.mul_sum, Finset.sum_comm]`.

Simplify using `only [Subgroup.coe_mul, Subgroup.coe_inv]`. Establish `hA : ∀ t : D, ∑ i : I, extendByZero H f (x * ((t : G)⁻¹ * (φ ^ m * i) * t) * x⁻¹) = ∑ i : I, extendByZero H f (x * (φ ^ m * i) * x⁻¹)` using `fun t ↦ sum_conj_coset hID hφ hgen t.2 (fun g ↦ extendByZero H f (x * g * x⁻¹)) m`. Repeatedly rewrite using `[hA]`. Rewrite using `[Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card]`. Establish `hcount` using `card_mul_card_eq (H := H) hID x`.

Establish `hI0 : (Nat.card I : ℂ) ≠ 0` using `Nat.cast_ne_zero.2 Nat.card_pos.ne'`. Establish `hE0 : (Nat.card ((MulAut.conj x⁻¹ • H : Subgroup G).subgroupOf D) : ℂ) ≠ 0` using `Nat.cast_ne_zero.2 Nat.card_pos.ne'`. Establish `hIx0 : (Nat.card ((MulAut.conj x • I : Subgroup G).subgroupOf H) : ℂ) ≠ 0` using `Nat.cast_ne_zero.2 Nat.card_pos.ne'`. Use `split_ifs with hdiv`. Take `⟨k, hk⟩` from `hdiv`.

Establish `hr0 : (frobIndex H D I x : ℤ) ≠ 0`. Introduce `h0`. Rewrite `hk` using `[h0, zero_mul]`. Establish `h1 : (frobIndex H D I x : ℤ) ∣ 0` using `dvd_zero _`. Rewrite `h1` using `[← hKr, zpow_zero]`.

Rewrite `h0` using `[Nat.cast_eq_zero]`. Use `(Subgroup.card_mul_index ((I ⊔ ((MulAut.conj x⁻¹ • H : Subgroup G) ⊓ D)).subgroupOf D))` as an intermediate fact. Rewrite `this` using `[← Subgroup.relIndex, ← frobIndex, h0, mul_zero]`. Conclude with `Nat.card_pos.ne' this.symm`. Rewrite using `[hk, Int.mul_ediv_cancel_left _ hr0]`.

Take `⟨i0, hi0, hφxeq⟩` from `hφx`. Take `⟨ψ, hψ⟩ : ∃ ψ, ψ = x⁻¹ * (φx : G) * x` from `⟨_, rfl⟩`. Establish `hj0 : (φ ^ (frobIndex H D I x : ℤ))⁻¹ * ψ ∈ I`. Rewrite using `[show (φ ^ (frobIndex H D I x : ℤ))⁻¹ * ψ = x⁻¹ * i0 * x by rw [hψ, hφxeq]; group]`. Conclude with `(mem_conj_smul_iff I x i0).1 hi0`.

Establish `hψD : ψ ∈ D`. Use `D.mul_mem (D.zpow_mem hφ (frobIndex H D I x : ℤ)) (hID hj0)` as an intermediate fact. Simplify using `using this`. Establish `hi1 : (ψ ^ k)⁻¹ * φ ^ ((frobIndex H D I x : ℤ) * k) ∈ I`. Establish `h1 : ψ⁻¹ * φ ^ (frobIndex H D I x : ℤ) ∈ I` using `by simpa using I.inv_mem hj0`.

Use `zpow_inv_mul_zpow_mem hψD (D.zpow_mem hφ (frobIndex H D I x : ℤ)) h1 k` as an intermediate fact. Rewrite `this` using `[← zpow_mul]`. Then use the resulting hypothesis. Establish `hψk : ψ ^ k = x⁻¹ * (φx : G) ^ k * x`. Use `conj_zpow (i := k) (a := x⁻¹) (b := (φx : G))` as an intermediate fact. Rewrite `this` using `[inv_inv]`.

Rewrite using `[hψ, this]`. Establish `hS : ∑ i : I, extendByZero H f (x * (φ ^ ((frobIndex H D I x : ℤ) * k) * i) * x⁻¹) = ∑ i : I, extendByZero H f (x * (ψ ^ k * i) * x⁻¹)` using `Fintype.sum_equiv (Equiv.mulLeft (⟨_, hi1⟩ : I)) _ _ fun i ↦ by`. Use `congr 1`. Simplify using `only [Equiv.coe_mulLeft, Subgroup.coe_mul]`. Use `group`.

Establish `hS2 : ∑ i : I, extendByZero H f (x * (ψ ^ k * i) * x⁻¹) = ∑ i : I, (fun g ↦ extendByZero H f ((φx : G) ^ k * g)) (x * i * x⁻¹)`. Use `Finset.sum_congr rfl fun i _ ↦ ?_` and prove the remaining obligations. Simplify using `only`. Rewrite using `[hψk]`. Use `congr 1`.

Use `group`. Establish `hF : ∀ g ∉ H, (fun g ↦ extendByZero H f ((φx : G) ^ k * g)) g = 0` using `fun g hg ↦ extendByZero_of_notMem H f fun hm ↦ hg (by`. Use `H.mul_mem (H.inv_mem (H.zpow_mem φx.2 k)) hm` as an intermediate fact. Simplify using `using this)`. Establish `hS3 : ∑ j : (MulAut.conj x • I : Subgroup G).subgroupOf H, (fun g ↦ extendByZero H f ((φx : G) ^ k * g)) ((j : H) : G) = ∑ j : (MulAut.conj x • I : Subgroup G).subgroupOf H, f (φx ^ k * j)` using `Finset.sum_congr rfl fun j _ ↦ by`.

Simplify using `only`. Rewrite using `[show (φx : G) ^ k * ((j : H) : G) = ((φx ^ k * (j : H) : H) : G) by simp, extendByZero_coe]`. Rewrite using `[hS, hS2, sum_conj_eq_sum_subgroupOf H I x _ hF, hS3, cosetAvg]`. Establish `hc : (Nat.card D : ℂ) * Nat.card ((MulAut.conj x • I : Subgroup G).subgroupOf H) = frobIndex H D I x * Nat.card I * Nat.card ((MulAut.conj x⁻¹ • H : Subgroup G).subgroupOf D)`. Conclude with `hcount` after adjusting the coercions.

Clear the denominators using the available nonvanishing facts. Take the linear combination `(∑ j : (MulAut.conj x • I : Subgroup G).subgroupOf H, f (φx ^ k * j)) * hc`. Establish `h0 : ∀ i : I, extendByZero H f (x * (φ ^ m * i) * x⁻¹) = 0` using `fun i ↦ extendByZero_of_notMem H f fun hm ↦ hdiv ((hKr m).1 (by`. Establish `h1 : φ ^ m * i ∈ K` using `Subgroup.mem_sup_right (Subgroup.mem_inf.2 ⟨(mem_conj_inv_smul_iff H x _).2 hm, D.mul_mem (D.zpow_mem hφ m) (hID i.2)⟩)`. Use `K.mul_mem h1 (hIK (I.inv_mem i.2))` as an intermediate fact.

Simplify using `using this))`. Simplify using `[h0]`.
-/
theorem cosetAvg_indFun_conjFun [Fintype H] [Fintype D] [Fintype I] (hID : I ≤ D)
    [(I.subgroupOf D).Normal] {φ : G} (hφ : φ ∈ D)
    (hgen : Subgroup.zpowers ((⟨φ, hφ⟩ : D) : D ⧸ I.subgroupOf D) = ⊤) (f : H → ℂ) (x : G)
    (φx : H) (hφx : ∃ i ∈ (MulAut.conj x • I : Subgroup G),
      (φx : G) = x * φ ^ (frobIndex H D I x : ℤ) * x⁻¹ * i) (m : ℤ) :
    (Nat.card I : ℂ)⁻¹ * ∑ i : I,
        indFun ((MulAut.conj x⁻¹ • H : Subgroup G).subgroupOf D).subtype (conjFun H D x f)
          ⟨φ ^ m * i, D.mul_mem (D.zpow_mem hφ m) (hID i.2)⟩ =
      if (frobIndex H D I x : ℤ) ∣ m then
        (frobIndex H D I x : ℂ) *
          cosetAvg ((MulAut.conj x • I : Subgroup G).subgroupOf H) φx f (m / frobIndex H D I x)
      else 0 := by
  classical
  set K : Subgroup G := I ⊔ ((MulAut.conj x⁻¹ • H : Subgroup G) ⊓ D) with hK
  have hIK : I ≤ K := le_sup_left
  have hKr : ∀ n : ℤ, φ ^ n ∈ K ↔ (frobIndex H D I x : ℤ) ∣ n :=
    zpow_mem_iff_relIndex_dvd hφ hgen hIK
  simp_rw [indFun_subtype_apply, extendByZero_conjFun]
  rw [← Finset.mul_sum, Finset.sum_comm]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  have hA : ∀ t : D, ∑ i : I, extendByZero H f (x * ((t : G)⁻¹ * (φ ^ m * i) * t) * x⁻¹) =
      ∑ i : I, extendByZero H f (x * (φ ^ m * i) * x⁻¹) := fun t ↦
    sum_conj_coset hID hφ hgen t.2 (fun g ↦ extendByZero H f (x * g * x⁻¹)) m
  simp_rw [hA]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card]
  have hcount := card_mul_card_eq (H := H) hID x
  have hI0 : (Nat.card I : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have hE0 : (Nat.card ((MulAut.conj x⁻¹ • H : Subgroup G).subgroupOf D) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have hIx0 : (Nat.card ((MulAut.conj x • I : Subgroup G).subgroupOf H) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.2 Nat.card_pos.ne'
  split_ifs with hdiv
  · obtain ⟨k, hk⟩ := hdiv
    have hr0 : (frobIndex H D I x : ℤ) ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at hk
      have h1 : (frobIndex H D I x : ℤ) ∣ 0 := dvd_zero _
      rw [← hKr, zpow_zero] at h1
      rw [Nat.cast_eq_zero] at h0
      have := (Subgroup.card_mul_index ((I ⊔ ((MulAut.conj x⁻¹ • H : Subgroup G) ⊓ D)).subgroupOf
        D))
      rw [← Subgroup.relIndex, ← frobIndex, h0, mul_zero] at this
      exact Nat.card_pos.ne' this.symm
    rw [hk, Int.mul_ediv_cancel_left _ hr0]
    obtain ⟨i0, hi0, hφxeq⟩ := hφx
    obtain ⟨ψ, hψ⟩ : ∃ ψ, ψ = x⁻¹ * (φx : G) * x := ⟨_, rfl⟩
    have hj0 : (φ ^ (frobIndex H D I x : ℤ))⁻¹ * ψ ∈ I := by
      rw [show (φ ^ (frobIndex H D I x : ℤ))⁻¹ * ψ = x⁻¹ * i0 * x by rw [hψ, hφxeq]; group]
      exact (mem_conj_smul_iff I x i0).1 hi0
    have hψD : ψ ∈ D := by
      have := D.mul_mem (D.zpow_mem hφ (frobIndex H D I x : ℤ)) (hID hj0)
      simpa using this
    have hi1 : (ψ ^ k)⁻¹ * φ ^ ((frobIndex H D I x : ℤ) * k) ∈ I := by
      have h1 : ψ⁻¹ * φ ^ (frobIndex H D I x : ℤ) ∈ I := by simpa using I.inv_mem hj0
      have := zpow_inv_mul_zpow_mem hψD (D.zpow_mem hφ (frobIndex H D I x : ℤ)) h1 k
      rwa [← zpow_mul] at this
    have hψk : ψ ^ k = x⁻¹ * (φx : G) ^ k * x := by
      have := conj_zpow (i := k) (a := x⁻¹) (b := (φx : G))
      rw [inv_inv] at this
      rw [hψ, this]
    have hS : ∑ i : I, extendByZero H f (x * (φ ^ ((frobIndex H D I x : ℤ) * k) * i) * x⁻¹) =
        ∑ i : I, extendByZero H f (x * (ψ ^ k * i) * x⁻¹) :=
      Fintype.sum_equiv (Equiv.mulLeft (⟨_, hi1⟩ : I)) _ _ fun i ↦ by
        congr 1
        simp only [Equiv.coe_mulLeft, Subgroup.coe_mul]
        group
    have hS2 : ∑ i : I, extendByZero H f (x * (ψ ^ k * i) * x⁻¹) =
        ∑ i : I, (fun g ↦ extendByZero H f ((φx : G) ^ k * g)) (x * i * x⁻¹) := by
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      simp only
      rw [hψk]
      congr 1
      group
    have hF : ∀ g ∉ H, (fun g ↦ extendByZero H f ((φx : G) ^ k * g)) g = 0 := fun g hg ↦
      extendByZero_of_notMem H f fun hm ↦ hg (by
        have := H.mul_mem (H.inv_mem (H.zpow_mem φx.2 k)) hm
        simpa using this)
    have hS3 : ∑ j : (MulAut.conj x • I : Subgroup G).subgroupOf H,
        (fun g ↦ extendByZero H f ((φx : G) ^ k * g)) ((j : H) : G) =
        ∑ j : (MulAut.conj x • I : Subgroup G).subgroupOf H, f (φx ^ k * j) :=
      Finset.sum_congr rfl fun j _ ↦ by
        simp only
        rw [show (φx : G) ^ k * ((j : H) : G) = ((φx ^ k * (j : H) : H) : G) by simp,
          extendByZero_coe]
    rw [hS, hS2, sum_conj_eq_sum_subgroupOf H I x _ hF, hS3, cosetAvg]
    have hc : (Nat.card D : ℂ) * Nat.card ((MulAut.conj x • I : Subgroup G).subgroupOf H) =
        frobIndex H D I x * Nat.card I *
          Nat.card ((MulAut.conj x⁻¹ • H : Subgroup G).subgroupOf D) := by
      exact_mod_cast hcount
    field_simp
    linear_combination (∑ j : (MulAut.conj x • I : Subgroup G).subgroupOf H, f (φx ^ k * j)) * hc
  · have h0 : ∀ i : I, extendByZero H f (x * (φ ^ m * i) * x⁻¹) = 0 := fun i ↦
      extendByZero_of_notMem H f fun hm ↦ hdiv ((hKr m).1 (by
        have h1 : φ ^ m * i ∈ K := Subgroup.mem_sup_right (Subgroup.mem_inf.2
          ⟨(mem_conj_inv_smul_iff H x _).2 hm, D.mul_mem (D.zpow_mem hφ m) (hID i.2)⟩)
        have := K.mul_mem h1 (hIK (I.inv_mem i.2))
        simpa using this))
    simp [h0]

end Formula

section Main

variable {G : Type*} [Group G] [Fintype G] {H D I : Subgroup G}

open Classical in

/- English proof (translation)
Establish `hA : ∀ i : I, indFun H.subtype f (φ ^ m * i) = ∑ q, indFun ((MulAut.conj (x q)⁻¹ • H : Subgroup G).subgroupOf D).subtype (conjFun H D (x q) f) ⟨φ ^ m * i, D.mul_mem (D.zpow_mem hφ m) (hID i.2)⟩`. Introduce `i`. Use `congrFun (indFun_comp_subtype_eq_sum H D hf x hx) ⟨φ ^ m * i, D.mul_mem (D.zpow_mem hφ m) (hID i.2)⟩` as an intermediate fact. Rewrite `this` using `[Finset.sum_apply]`. Conclude with `this`.

Rewrite using `[cosetAvg]`. Repeatedly rewrite using `[hA]`. Rewrite using `[Finset.sum_comm, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun q _ ↦ cosetAvg_indFun_conjFun hID hφ hgen f (x q) (φx q) (hφx q) m`.
-/
theorem cosetAvg_indFun [Fintype H] [Fintype D] [Fintype I] (hID : I ≤ D)
    [(I.subgroupOf D).Normal] {φ : G} (hφ : φ ∈ D)
    (hgen : Subgroup.zpowers ((⟨φ, hφ⟩ : D) : D ⧸ I.subgroupOf D) = ⊤) {f : H → ℂ}
    (hf : IsClassFun f) (x : DoubleCoset.Quotient (H : Set G) D → G)
    (hx : ∀ q, DoubleCoset.mk H D (x q) = q) (φx : DoubleCoset.Quotient (H : Set G) D → H)
    (hφx : ∀ q, ∃ i ∈ (MulAut.conj (x q) • I : Subgroup G),
      (φx q : G) = x q * φ ^ (frobIndex H D I (x q) : ℤ) * (x q)⁻¹ * i) (m : ℤ) :
    cosetAvg I φ (indFun H.subtype f) m =
      ∑ q, if (frobIndex H D I (x q) : ℤ) ∣ m then
        (frobIndex H D I (x q) : ℂ) *
          cosetAvg ((MulAut.conj (x q) • I : Subgroup G).subgroupOf H) (φx q) f
            (m / frobIndex H D I (x q))
      else 0 := by
  classical
  have hA : ∀ i : I, indFun H.subtype f (φ ^ m * i) = ∑ q,
      indFun ((MulAut.conj (x q)⁻¹ • H : Subgroup G).subgroupOf D).subtype (conjFun H D (x q) f)
        ⟨φ ^ m * i, D.mul_mem (D.zpow_mem hφ m) (hID i.2)⟩ := by
    intro i
    have := congrFun (indFun_comp_subtype_eq_sum H D hf x hx)
      ⟨φ ^ m * i, D.mul_mem (D.zpow_mem hφ m) (hID i.2)⟩
    rw [Finset.sum_apply] at this
    exact this
  rw [cosetAvg]
  simp_rw [hA]
  rw [Finset.sum_comm, Finset.mul_sum]
  exact Finset.sum_congr rfl fun q _ ↦
    cosetAvg_indFun_conjFun hID hφ hgen f (x q) (φx q) (hφx q) m

end Main

end GroundTheory.Global.Artin
