import Mathlib

namespace GlobalTheory
namespace FiniteOrderUnipotent

open Finset

variable {A : Type} [AddCommGroup A]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem end_mul_apply (f h : AddMonoid.End A) (x : A) : (f * h) x = f (h x) := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem end_add_apply (f h : AddMonoid.End A) (x : A) : (f + h) x = f x + h x := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem end_nsmul_apply (n : ℕ) (f : AddMonoid.End A) (x : A) : (n • f) x = n • f x := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem end_neg_apply (f : AddMonoid.End A) (x : A) : (-f) x = -f x := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem end_zero_apply (x : A) : (0 : AddMonoid.End A) x = 0 := rfl

/- English proof (translation)
Introduce `x hx`. Take `⟨j, hj⟩` from `hprim x`. Proceed by induction on `j generalizing x with`. Consider the case `zero => simpa using hj`. Consider the case `succ j ih`.

Establish `hgx : g • x = 0`. Apply `ih (g • x)` to reduce the goal to its premises. Rewrite using `[smul_comm, hx, ← map_nsmul, ← map_nsmul]`. Rewrite using `[← mul_smul, ← pow_succ]`. Conclude with `hj`.

Establish `key : ∀ i : ℕ, c ^ i • x = ((N * Z) ^ i) x`. Introduce `i`. Proceed by induction on `i with`. Consider the case `zero => simp`. Consider the case `succ i ih2`.

Rewrite using `[pow_succ', mul_smul, ih2, ← map_nsmul, hx, pow_succ, end_mul_apply, end_mul_apply]`. Establish `hck : c ^ k • x = 0`. Rewrite using `[key k, hc.mul_pow k, end_mul_apply]`. Apply `hk` to reduce the goal to its premises. Rewrite using `[← map_nsmul, hgx, map_zero]`.

Establish `h1` using `addOrderOf_dvd_of_nsmul_eq_zero hck`. Establish `h2` using `addOrderOf_dvd_of_nsmul_eq_zero hgx`. Establish `h3` using `Nat.dvd_gcd h1 h2`. Rewrite `h3` using `[Nat.Coprime.gcd_eq_one (hcg.pow_left k)]`. Conclude with `AddMonoid.addOrderOf_eq_one_iff.mp (Nat.dvd_one.mp h3)`.
-/
theorem inj_core {g : ℕ} (hprim : ∀ x : A, ∃ j : ℕ, g ^ j • x = 0)
    (N Z : AddMonoid.End A) (hc : Commute N Z) (k c : ℕ) (hcg : Nat.Coprime c g)
    (hk : ∀ x : A, g • x = 0 → (N ^ k) x = 0) :
    ∀ x : A, c • x = N (Z x) → x = 0 := by
  intro x hx
  obtain ⟨j, hj⟩ := hprim x
  induction j generalizing x with
  | zero => simpa using hj
  | succ j ih =>
    have hgx : g • x = 0 := by
      apply ih (g • x)
      · rw [smul_comm, hx, ← map_nsmul, ← map_nsmul]
      · rw [← mul_smul, ← pow_succ]; exact hj
    have key : ∀ i : ℕ, c ^ i • x = ((N * Z) ^ i) x := by
      intro i
      induction i with
      | zero => simp
      | succ i ih2 =>
        rw [pow_succ', mul_smul, ih2, ← map_nsmul, hx, pow_succ, end_mul_apply, end_mul_apply]
    have hck : c ^ k • x = 0 := by
      rw [key k, hc.mul_pow k, end_mul_apply]
      apply hk
      rw [← map_nsmul, hgx, map_zero]
    have h1 := addOrderOf_dvd_of_nsmul_eq_zero hck
    have h2 := addOrderOf_dvd_of_nsmul_eq_zero hgx
    have h3 := Nat.dvd_gcd h1 h2
    rw [Nat.Coprime.gcd_eq_one (hcg.pow_left k)] at h3
    exact AddMonoid.addOrderOf_eq_one_iff.mp (Nat.dvd_one.mp h3)

/- English proof (translation)
The claim follows from `Commute.sum_right _ _ _ fun i _ => ((Commute.refl B).pow_right i).sub_left (Commute.one_left _)`.
-/
theorem comm_geom (B : AddMonoid.End A) (n : ℕ) : Commute (B - 1) (∑ i ∈ range n, B ^ i) :=
  Commute.sum_right _ _ _ fun i _ => ((Commute.refl B).pow_right i).sub_left (Commute.one_left _)

/- English proof (translation)
Introduce `x hx`. Rewrite using `[hc.mul_pow k, end_mul_apply]`. Apply `hk` to reduce the goal to its premises. Rewrite using `[← map_nsmul, hx, map_zero]`.
-/
theorem kill_mul {g k : ℕ} (N P : AddMonoid.End A) (hc : Commute N P)
    (hk : ∀ x : A, g • x = 0 → (N ^ k) x = 0) : ∀ x : A, g • x = 0 → ((N * P) ^ k) x = 0 := by
  intro x hx
  rw [hc.mul_pow k, end_mul_apply]
  apply hk
  rw [← map_nsmul, hx, map_zero]

/- English proof (translation)
Use `set Z : AddMonoid.End A := ∑ i ∈ range n, ∑ j ∈ range i, B ^ j with hZ`. Establish `hS : (∑ i ∈ range n, B ^ i) = (n : AddMonoid.End A) + (B - 1) * Z`. Rewrite using `[hZ, Finset.mul_sum]`. Repeatedly rewrite using `[mul_geom_sum]`. Rewrite using `[Finset.sum_sub_distrib]`.

Simplify using the standard rewrite rules. Establish `hSN : (∑ i ∈ range n, B ^ i) * (B - 1) = 0`. Rewrite using `[geom_sum_mul, hB, sub_self]`. Establish `hcZ : Commute (B - 1) (-Z)`. Use `Commute.neg_right ?_` and prove the remaining obligations.

Conclude with `Commute.sum_right _ _ _ fun i _ => comm_geom B i`. Rewrite using `[← sub_eq_zero]`. Use extensionality with `y`. Establish `hx` using `congrArg (fun F : AddMonoid.End A => F y) hSN`. Simplify using `only [end_mul_apply] at hx`.

Rewrite `hx` using `[hS]`. Express the relevant statement in the definitionally equal form `(n : AddMonoid.End A) ((B - 1) y) + (B - 1) (Z ((B - 1) y)) = (0 : AddMonoid.End A) y at hx`. Establish `hx' : n • ((B - 1) y) = (B - 1) ((-Z) ((B - 1) y))`. Establish `e0 : (-Z) ((B - 1) y) = -(Z ((B - 1) y))` using `rfl`. Rewrite using `[e0, map_neg, eq_neg_iff_add_eq_zero, ← AddMonoid.End.natCast_apply]`.

Conclude with `hx`. Simplify using `using inj_core hprim (B - 1) (-Z) hcZ k n hng hk _ hx'`.
-/
theorem coprime_order {g : ℕ} (hprim : ∀ x : A, ∃ j : ℕ, g ^ j • x = 0)
    (B : AddMonoid.End A) (n k : ℕ) (hB : B ^ n = 1) (hng : Nat.Coprime n g)
    (hk : ∀ x : A, g • x = 0 → ((B - 1) ^ k) x = 0) : B = 1 := by
  set Z : AddMonoid.End A := ∑ i ∈ range n, ∑ j ∈ range i, B ^ j with hZ
  have hS : (∑ i ∈ range n, B ^ i) = (n : AddMonoid.End A) + (B - 1) * Z := by
    rw [hZ, Finset.mul_sum]
    simp_rw [mul_geom_sum]
    rw [Finset.sum_sub_distrib]
    simp
  have hSN : (∑ i ∈ range n, B ^ i) * (B - 1) = 0 := by
    rw [geom_sum_mul, hB, sub_self]
  have hcZ : Commute (B - 1) (-Z) := by
    refine Commute.neg_right ?_
    exact Commute.sum_right _ _ _ fun i _ => comm_geom B i
  rw [← sub_eq_zero]
  ext y
  have hx := congrArg (fun F : AddMonoid.End A => F y) hSN
  simp only [end_mul_apply] at hx
  rw [hS] at hx
  change (n : AddMonoid.End A) ((B - 1) y) + (B - 1) (Z ((B - 1) y)) = (0 : AddMonoid.End A) y at hx
  have hx' : n • ((B - 1) y) = (B - 1) ((-Z) ((B - 1) y)) := by
    have e0 : (-Z) ((B - 1) y) = -(Z ((B - 1) y)) := rfl
    rw [e0, map_neg, eq_neg_iff_add_eq_zero, ← AddMonoid.End.natCast_apply]
    exact hx
  simpa using inj_core hprim (B - 1) (-Z) hcZ k n hng hk _ hx'

/- English proof (translation)
Rewrite using `[(Commute.one_right N).add_pow, sum_range_succ, sum_range_succ', sum_range_succ']`. Simplify using `only [one_pow, mul_one]`. Establish `hmid : (∑ m ∈ range h, N ^ (m + 1 + 1) * (((h + 2).choose (m + 1 + 1) : ℕ) : AddMonoid.End A)) = (h + 2) • (N ^ 2 * ∑ m ∈ range h, ((h + 2).choose (m + 2) / (h + 2)) • N ^ m)`. Rewrite using `[Finset.mul_sum]`. Rewrite using `[← Finset.sum_nsmul]`.

Use `Finset.sum_congr rfl fun m hm => ?_` and prove the remaining obligations. Establish `hlt : m + 2 < h + 2` using `by simp at hm; omega`. Establish `hdvd` using `hp.dvd_choose_self (k := m + 2) (by omega) hlt`. Rewrite using `[mul_smul_comm, smul_smul, Nat.mul_div_cancel' hdvd, ← pow_add, ← nsmul_eq_mul']`. Use `congr 2`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[hmid]`. Simplify using `only [pow_zero, pow_one, Nat.choose_zero_right, Nat.choose_one_right, Nat.choose_self, Nat.cast_one, mul_one, zero_add]`. Rewrite using `[← nsmul_eq_mul']`. Normalize the expressions using the abelian group laws.
-/
theorem binom_identity (N : AddMonoid.End A) (h : ℕ) (hp : (h + 2).Prime) :
    (N + 1) ^ (h + 2) = 1 + (h + 2) • N
      + (h + 2) • (N ^ 2 * ∑ m ∈ range h, ((h + 2).choose (m + 2) / (h + 2)) • N ^ m)
      + N ^ (h + 2) := by
  rw [(Commute.one_right N).add_pow, sum_range_succ, sum_range_succ', sum_range_succ']
  simp only [one_pow, mul_one]
  have hmid : (∑ m ∈ range h, N ^ (m + 1 + 1) * (((h + 2).choose (m + 1 + 1) : ℕ) : AddMonoid.End A))
      = (h + 2) • (N ^ 2 * ∑ m ∈ range h, ((h + 2).choose (m + 2) / (h + 2)) • N ^ m) := by
    rw [Finset.mul_sum]
    rw [← Finset.sum_nsmul]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hlt : m + 2 < h + 2 := by simp at hm; omega
    have hdvd := hp.dvd_choose_self (k := m + 2) (by omega) hlt
    rw [mul_smul_comm, smul_smul, Nat.mul_div_cancel' hdvd, ← pow_add, ← nsmul_eq_mul']
    congr 2
    omega
  rw [hmid]
  simp only [pow_zero, pow_one, Nat.choose_zero_right, Nat.choose_one_right, Nat.choose_self,
    Nat.cast_one, mul_one, zero_add]
  rw [← nsmul_eq_mul']
  abel

/- English proof (translation)
Take `⟨e, rfl⟩ : ∃ e, g = k + e + 2` from `⟨g - k - 2, by omega⟩`. Use `set N := B - 1 with hN`. Establish `hBN : B = N + 1` using `by rw [hN, sub_add_cancel]`. Use `set V : AddMonoid.End A := ∑ m ∈ range (k + e), ((k + e + 2).choose (m + 2) / (k + e + 2)) • N ^ m with hV`. Establish `hid` using `binom_identity N (k + e) hg`.

Rewrite `hid` using `[← hBN, hB]`. Establish `hid' : (k + e + 2) • N + ((k + e + 2) • (N ^ 2 * V) + N ^ (k + e + 2)) = 0`. Rewrite `hid` using `[eq_comm, add_assoc, add_assoc, add_eq_left]`. Conclude with `hid`. Establish `hNV : Commute N V` using `Commute.sum_right _ _ _ fun m _ => ((Commute.refl N).pow_right m).smul_right _`.

Use `choose d hd using hdiv`. Set `M : AddMonoid.End A` to `{ toFun := fun y => (N ^ k) (d y) map_zero' := hk _ (hd 0) map_add' := fun a b => by`. Rewrite using `[← map_add, ← sub_eq_zero, ← map_sub]`. Apply `hk` to reduce the goal to its premises. Rewrite using `[smul_sub, smul_add, hd, hd, hd, sub_self] }`.

Establish `hMy : ∀ y, M y = (N ^ k) (d y)` using `fun y => rfl`. Establish `hMN : ∀ y, M (N y) = N (M y)`. Introduce `y`. Rewrite using `[hMy, hMy, ← end_mul_apply N, (Commute.self_pow N k).eq, end_mul_apply, ← sub_eq_zero, ← map_sub]`. Apply `hk` to reduce the goal to its premises.

Rewrite using `[smul_sub, hd, ← map_nsmul, hd, sub_self]`. Establish `hcM : Commute N M` using `by show N * M = M * N`. Use extensionality with `y`. Conclude with `(hMN y).symm`. Establish `hcZ : Commute N (-(V + N ^ e * M))` using `(hNV.add_right (((Commute.refl N).pow_right e).mul_right hcM)).neg_right`.

Rewrite using `[← sub_eq_zero]`. Use extensionality with `y`. Establish `h0` using `congrArg (fun F : AddMonoid.End A => F (d y)) hid'`. Simplify using `only [end_add_apply, end_nsmul_apply, end_mul_apply, end_zero_apply] at h0`. Rewrite `h0` using `[← map_nsmul, hd, ← map_nsmul, ← map_nsmul, hd]`.

Establish `hpow : N ^ (k + e + 2) = N ^ e * N * N * N ^ k`. Rewrite using `[← pow_succ, ← pow_succ, ← pow_add]`. Use `congr 1`. Use linear arithmetic over natural numbers and integers. Rewrite `h0` using `[hpow, end_mul_apply, end_mul_apply, end_mul_apply, ← hMy, ← hMN, sq, end_mul_apply, ← end_mul_apply N V, hNV.eq, end_mul_apply]`.

Establish `hx : 1 • (N y) = N ((-(V + N ^ e * M)) (N y))`. Rewrite using `[one_smul, end_neg_apply, map_neg, end_add_apply, end_mul_apply, map_add, eq_neg_iff_add_eq_zero]`. Rewrite using `[← end_mul_apply N (N ^ e), ← pow_succ', pow_succ, end_mul_apply]`. Conclude with `h0`. Conclude with `inj_core hprim N _ hcZ k 1 (Nat.coprime_one_left _) hk _ hx`.
-/
theorem prime_order {g : ℕ} (hg : g.Prime) (hprim : ∀ x : A, ∃ j : ℕ, g ^ j • x = 0)
    (hdiv : ∀ x : A, ∃ y : A, g • y = x)
    (B : AddMonoid.End A) (k : ℕ) (hkg : k + 2 ≤ g) (hB : B ^ g = 1)
    (hk : ∀ x : A, g • x = 0 → ((B - 1) ^ k) x = 0) : B = 1 := by
  obtain ⟨e, rfl⟩ : ∃ e, g = k + e + 2 := ⟨g - k - 2, by omega⟩
  set N := B - 1 with hN
  have hBN : B = N + 1 := by rw [hN, sub_add_cancel]
  set V : AddMonoid.End A :=
    ∑ m ∈ range (k + e), ((k + e + 2).choose (m + 2) / (k + e + 2)) • N ^ m with hV
  have hid := binom_identity N (k + e) hg
  rw [← hBN, hB] at hid
  have hid' : (k + e + 2) • N + ((k + e + 2) • (N ^ 2 * V) + N ^ (k + e + 2)) = 0 := by
    rw [eq_comm, add_assoc, add_assoc, add_eq_left] at hid
    exact hid
  have hNV : Commute N V :=
    Commute.sum_right _ _ _ fun m _ => ((Commute.refl N).pow_right m).smul_right _
  choose d hd using hdiv
  let M : AddMonoid.End A :=
    { toFun := fun y => (N ^ k) (d y)
      map_zero' := hk _ (hd 0)
      map_add' := fun a b => by
        rw [← map_add, ← sub_eq_zero, ← map_sub]
        apply hk
        rw [smul_sub, smul_add, hd, hd, hd, sub_self] }
  have hMy : ∀ y, M y = (N ^ k) (d y) := fun y => rfl
  have hMN : ∀ y, M (N y) = N (M y) := by
    intro y
    rw [hMy, hMy, ← end_mul_apply N, (Commute.self_pow N k).eq, end_mul_apply,
      ← sub_eq_zero, ← map_sub]
    apply hk
    rw [smul_sub, hd, ← map_nsmul, hd, sub_self]
  have hcM : Commute N M := by
    show N * M = M * N
    ext y
    exact (hMN y).symm
  have hcZ : Commute N (-(V + N ^ e * M)) :=
    (hNV.add_right (((Commute.refl N).pow_right e).mul_right hcM)).neg_right
  rw [← sub_eq_zero]
  ext y
  have h0 := congrArg (fun F : AddMonoid.End A => F (d y)) hid'
  simp only [end_add_apply, end_nsmul_apply, end_mul_apply, end_zero_apply] at h0
  rw [← map_nsmul, hd, ← map_nsmul, ← map_nsmul, hd] at h0
  have hpow : N ^ (k + e + 2) = N ^ e * N * N * N ^ k := by
    rw [← pow_succ, ← pow_succ, ← pow_add]
    congr 1
    omega
  rw [hpow, end_mul_apply, end_mul_apply, end_mul_apply, ← hMy, ← hMN, sq, end_mul_apply,
    ← end_mul_apply N V, hNV.eq, end_mul_apply] at h0
  have hx : 1 • (N y) = N ((-(V + N ^ e * M)) (N y)) := by
    rw [one_smul, end_neg_apply, map_neg, end_add_apply, end_mul_apply, map_add, eq_neg_iff_add_eq_zero]
    rw [← end_mul_apply N (N ^ e), ← pow_succ', pow_succ, end_mul_apply]
    exact h0
  exact inj_core hprim N _ hcZ k 1 (Nat.coprime_one_left _) hk _ hx

/- English proof (translation)
Use `haveI := Fact.mk hg`. Set `S : AddSubgroup A` to `{ carrier := {x | g • x = 0} add_mem' := fun {a b} ha hb => by`. Simplify using `only [Set.mem_setOf_eq] at ha hb ⊢`. Rewrite using `[smul_add, ha, hb, add_zero]`. Use the proof step `zero_mem' := smul_zero _`.

Use the proof step `neg_mem' := fun {a} ha => by`. Simplify using `only [Set.mem_setOf_eq] at ha ⊢`. Rewrite using `[smul_neg, ha, neg_zero] }`. Establish `hS : ∀ x : A, x ∈ S ↔ g • x = 0` using `fun x => Iff.rfl`. Take `⟨_⟩ : Nonempty (Module (ZMod g) S)` from `⟨AddCommGroup.zmodModule (fun x => Subtype.ext (by`.

Simplify using `using (hS x.1).mp x.2))⟩`. Use `haveI : Finite S := Finite.of_injective (fun x : S => (⟨x.1, hTA x.1 ((hS x.1).mp x.2)⟩ : T)) (by intro a b h; apply Subtype.ext; simpa using congrArg Subtype.val h)`. Use `haveI : Module.Finite (ZMod g) S := Module.Finite.of_finite`. Establish `hcard : Nat.card S ≤ g ^ r`. Use `Nat.card_le_card_of_injective (fun x : S => (⟨x.1, hTA x.1 ((hS x.1).mp x.2)⟩ : T)) (by intro a b h; apply Subtype.ext; simpa using congrArg Subtype.val h)` as an intermediate fact.

Rewrite `this` using `[Nat.card_eq_fintype_card (α := T), Fintype.card_coe]`. Conclude with `this.trans hT`. Establish `hc2 : Nat.card S = g ^ Module.finrank (ZMod g) S`. Use `@Module.natCard_eq_pow_finrank (ZMod g) S _ _ _ _` as an intermediate fact. Rewrite using `[this, Nat.card_zmod]`.

Rewrite `hcard` using `[hc2]`. Establish `hle : Module.finrank (ZMod g) S ≤ r` using `(Nat.pow_le_pow_iff_right hg.one_lt).mp hcard`. Set `f : S →+ S` to `{ toFun := fun x => ⟨N x.1, by`. Rewrite using `[hS, ← map_nsmul, (hS x.1).mp x.2, map_zero]⟩`. Use the proof step `map_zero' := Subtype.ext (by simp)`.

Use the proof step `map_add' := fun a b => Subtype.ext (by simp) }`. Set `fl : S →ₗ[ZMod g] S` to `f.toZModLinearMap g`. Establish `hpow : ∀ (i : ℕ) (x : S), ((fl ^ i) x : A) = (N ^ i) x.1`. Introduce `i`. Proceed by induction on `i with`.

Consider the case `zero => intro x`. Both sides reduce to the same expression. Consider the case `succ i ih`. Introduce `x`. Rewrite using `[pow_succ, Module.End.mul_apply, ih, pow_succ, end_mul_apply]`.

Both sides reduce to the same expression. Establish `hnil : IsNilpotent fl` using `⟨m, LinearMap.ext fun x => Subtype.ext (by`. Rewrite using `[hpow]`. Conclude with `hm _ ((hS x.1).mp x.2))⟩`. Establish `hfin : fl ^ Module.finrank (ZMod g) S = 0`.

Establish `h` using `LinearMap.aeval_self_charpoly fl`. Rewrite `h` using `[hnil.charpoly_eq_X_pow_finrank, Polynomial.aeval_X_pow]`. Conclude with `h`. Establish `hr : fl ^ r = 0` using `pow_eq_zero_of_le hle hfin`. Introduce `x hx`.

Use `hpow r ⟨x, (hS x).mpr hx⟩` as an intermediate fact. Rewrite `this` using `[hr]`. Conclude with `this.symm`.
-/
theorem nil_index {g r : ℕ} (hg : g.Prime) (T : Finset A) (hT : T.card ≤ g ^ r)
    (hTA : ∀ x : A, g • x = 0 → x ∈ T) (N : AddMonoid.End A) (m : ℕ)
    (hm : ∀ x : A, g • x = 0 → (N ^ m) x = 0) : ∀ x : A, g • x = 0 → (N ^ r) x = 0 := by
  haveI := Fact.mk hg
  let S : AddSubgroup A :=
    { carrier := {x | g • x = 0}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [smul_add, ha, hb, add_zero]
      zero_mem' := smul_zero _
      neg_mem' := fun {a} ha => by
        simp only [Set.mem_setOf_eq] at ha ⊢
        rw [smul_neg, ha, neg_zero] }
  have hS : ∀ x : A, x ∈ S ↔ g • x = 0 := fun x => Iff.rfl
  obtain ⟨_⟩ : Nonempty (Module (ZMod g) S) := ⟨AddCommGroup.zmodModule (fun x => Subtype.ext (by
    simpa using (hS x.1).mp x.2))⟩
  haveI : Finite S := Finite.of_injective (fun x : S => (⟨x.1, hTA x.1 ((hS x.1).mp x.2)⟩ : T))
    (by intro a b h; apply Subtype.ext; simpa using congrArg Subtype.val h)
  haveI : Module.Finite (ZMod g) S := Module.Finite.of_finite
  have hcard : Nat.card S ≤ g ^ r := by
    have := Nat.card_le_card_of_injective (fun x : S => (⟨x.1, hTA x.1 ((hS x.1).mp x.2)⟩ : T))
      (by intro a b h; apply Subtype.ext; simpa using congrArg Subtype.val h)
    rw [Nat.card_eq_fintype_card (α := T), Fintype.card_coe] at this
    exact this.trans hT
  have hc2 : Nat.card S = g ^ Module.finrank (ZMod g) S := by
    have := @Module.natCard_eq_pow_finrank (ZMod g) S _ _ _ _
    rw [this, Nat.card_zmod]
  rw [hc2] at hcard
  have hle : Module.finrank (ZMod g) S ≤ r := (Nat.pow_le_pow_iff_right hg.one_lt).mp hcard
  let f : S →+ S :=
    { toFun := fun x => ⟨N x.1, by
        rw [hS, ← map_nsmul, (hS x.1).mp x.2, map_zero]⟩
      map_zero' := Subtype.ext (by simp)
      map_add' := fun a b => Subtype.ext (by simp) }
  let fl : S →ₗ[ZMod g] S := f.toZModLinearMap g
  have hpow : ∀ (i : ℕ) (x : S), ((fl ^ i) x : A) = (N ^ i) x.1 := by
    intro i
    induction i with
    | zero => intro x; rfl
    | succ i ih =>
      intro x
      rw [pow_succ, Module.End.mul_apply, ih, pow_succ, end_mul_apply]
      rfl
  have hnil : IsNilpotent fl := ⟨m, LinearMap.ext fun x => Subtype.ext (by
    rw [hpow]; exact hm _ ((hS x.1).mp x.2))⟩
  have hfin : fl ^ Module.finrank (ZMod g) S = 0 := by
    have h := LinearMap.aeval_self_charpoly fl
    rw [hnil.charpoly_eq_X_pow_finrank, Polynomial.aeval_X_pow] at h
    exact h
  have hr : fl ^ r = 0 := pow_eq_zero_of_le hle hfin
  intro x hx
  have := hpow r ⟨x, (hS x).mpr hx⟩
  rw [hr] at this
  exact this.symm

/- English proof (translation)
Rewrite using `[← mul_geom_sum]`. Conclude with `kill_mul _ _ (comm_geom C s) h`.
-/
theorem kill_geom {g r : ℕ} (C : AddMonoid.End A) (s : ℕ)
    (h : ∀ x : A, g • x = 0 → ((C - 1) ^ r) x = 0) :
    ∀ x : A, g • x = 0 → ((C ^ s - 1) ^ r) x = 0 := by
  rw [← mul_geom_sum]
  exact kill_mul _ _ (comm_geom C s) h

end FiniteOrderUnipotent

open FiniteOrderUnipotent in

/- English proof (translation)
Introduce `A _ β n g r m hn hβ hg hrg hdiv hprim hT hu`. Take `⟨T, hTc, hTA⟩` from `hT`. Set `B : AddMonoid.End A` to `β`. Establish `hBn : B ^ n = 1`. Use extensionality with `x`.

Rewrite using `[AddMonoid.End.coe_pow]`. Conclude with `hβ x`. Establish `hcoe : ⇑(B - 1) = fun z => β z - z` using `rfl`. Establish `hm : ∀ x : A, g • x = 0 → ((B - 1) ^ m) x = 0`. Introduce `x hx`.

Rewrite using `[AddMonoid.End.coe_pow, hcoe]`. Conclude with `hu x hx`. Establish `hr` using `nil_index hg T hTc hTA (B - 1) m hm`. Take `⟨a, n', hndvd, hnn⟩` from `Nat.exists_eq_pow_mul_and_not_dvd hn.ne' g hg.ne_one`. Establish `hcop : Nat.Coprime n' g` using `((Nat.Prime.coprime_iff_not_dvd hg).mpr hndvd).symm`.

Establish `claim : ∀ (a : ℕ) (C : AddMonoid.End A), (∀ x : A, g • x = 0 → ((C - 1) ^ r) x = 0) → C ^ (g ^ a) = 1 → C = 1`. Introduce `a`. Proceed by induction on `a with`. Consider the case `zero => intro C _ h`. Simplify using `using h`.

Consider the case `succ a ih`. Introduce `C hC hCa`. Establish `hCg : C ^ g = 1` using `ih (C ^ g) (kill_geom C g hC) (by rw [← pow_mul, ← pow_succ']; exact hCa)`. Conclude with `prime_order hg hprim hdiv C r hrg hCg hC`. Establish `hB1 : B ^ (g ^ a) = 1`.

Use `coprime_order hprim (B ^ (g ^ a)) n' r ?_ hcop (kill_geom B (g ^ a) hr)` and prove the remaining obligations. Rewrite using `[← pow_mul, ← hnn, hBn]`. Establish `hB : B = 1` using `claim a B hr hB1`. Introduce `x`. Use `show B x = x`.

Rewrite using `[hB]`. Both sides reduce to the same expression.
-/
theorem finite_order_unipotent_eq_id : ∀ (A : Type) [AddCommGroup A] (β : A →+ A) (n g r m : ℕ),
    0 < n → (∀ x : A, β^[n] x = x) → g.Prime → r + 2 ≤ g → (∀ x : A, ∃ y : A, g • y = x) →
    (∀ x : A, ∃ j : ℕ, g ^ j • x = 0) →
    (∃ T : Finset A, T.card ≤ g ^ r ∧ ∀ x : A, g • x = 0 → x ∈ T) →
    (∀ x : A, g • x = 0 → (fun z => β z - z)^[m] x = 0) → ∀ x : A, β x = x := by
  intro A _ β n g r m hn hβ hg hrg hdiv hprim hT hu
  obtain ⟨T, hTc, hTA⟩ := hT
  let B : AddMonoid.End A := β
  have hBn : B ^ n = 1 := by
    ext x
    rw [AddMonoid.End.coe_pow]
    exact hβ x
  have hcoe : ⇑(B - 1) = fun z => β z - z := rfl
  have hm : ∀ x : A, g • x = 0 → ((B - 1) ^ m) x = 0 := by
    intro x hx
    rw [AddMonoid.End.coe_pow, hcoe]
    exact hu x hx
  have hr := nil_index hg T hTc hTA (B - 1) m hm
  obtain ⟨a, n', hndvd, hnn⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn.ne' g hg.ne_one
  have hcop : Nat.Coprime n' g := ((Nat.Prime.coprime_iff_not_dvd hg).mpr hndvd).symm
  have claim : ∀ (a : ℕ) (C : AddMonoid.End A), (∀ x : A, g • x = 0 → ((C - 1) ^ r) x = 0) →
      C ^ (g ^ a) = 1 → C = 1 := by
    intro a
    induction a with
    | zero => intro C _ h; simpa using h
    | succ a ih =>
      intro C hC hCa
      have hCg : C ^ g = 1 :=
        ih (C ^ g) (kill_geom C g hC) (by rw [← pow_mul, ← pow_succ']; exact hCa)
      exact prime_order hg hprim hdiv C r hrg hCg hC
  have hB1 : B ^ (g ^ a) = 1 := by
    refine coprime_order hprim (B ^ (g ^ a)) n' r ?_ hcop (kill_geom B (g ^ a) hr)
    rw [← pow_mul, ← hnn, hBn]
  have hB : B = 1 := claim a B hr hB1
  intro x
  show B x = x
  rw [hB]
  rfl

end GlobalTheory
