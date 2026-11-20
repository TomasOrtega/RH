import Mathlib
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.KurDefs

noncomputable section

namespace ReciprocityTheory.ChartRestriction.L1

open Formalism.L2.Th1.CM Polynomial

variable (l : ℕ) [Fact l.Prime]

def muM : Submonoid ℂ_[l] where
  carrier := muP l
  one_mem' := ⟨1, one_pos, fun h => (Fact.out : l.Prime).one_lt.ne' (Nat.dvd_one.1 h), one_pow 1⟩
  mul_mem' := by
    rintro a b ⟨n, hn, hln, ha⟩ ⟨m, hm, hlm, hb⟩
    refine ⟨n * m, Nat.mul_pos hn hm, fun h => ?_, ?_⟩
    · rcases ((Fact.out : l.Prime).dvd_mul).1 h with h | h
      · exact hln h
      · exact hlm h
    · rw [mul_pow, pow_mul, ha, one_pow, mul_comm n m, pow_mul, hb, one_pow, one_mul]

/- English proof (translation)
Proceed by induction on `S using Finset.induction_on with`. Consider the case `empty => exact ⟨1, one_pos, fun h => (Fact.out : l.Prime).one_lt.ne' (Nat.dvd_one.1 h), by simp⟩`. Consider the case `insert a S _ ih`. Take `⟨n, hn, hln, hS⟩` from `ih`. Take `⟨m, hm, hlm, ha⟩` from `a.2`.

Use `⟨n * m, Nat.mul_pos hn hm, fun h => ?_, ?_⟩` and prove the remaining obligations. Break down `((Fact.out : l.Prime).dvd_mul).1 h with h | h` into its components or cases. Conclude with `hln h`. Conclude with `hlm h`. Introduce `b hb`.

Break down `Finset.mem_insert.1 hb with rfl | hb` into its components or cases. Rewrite using `[mul_comm, pow_mul, ha, one_pow]`. Rewrite using `[pow_mul, hS b hb, one_pow]`.
-/
theorem muM_common (S : Finset (muM l)) :
    ∃ n : ℕ, 0 < n ∧ ¬ l ∣ n ∧ ∀ a ∈ S, (a : ℂ_[l]) ^ n = 1 := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, one_pos, fun h => (Fact.out : l.Prime).one_lt.ne' (Nat.dvd_one.1 h), by simp⟩
  | insert a S _ ih =>
    obtain ⟨n, hn, hln, hS⟩ := ih
    obtain ⟨m, hm, hlm, ha⟩ := a.2
    refine ⟨n * m, Nat.mul_pos hn hm, fun h => ?_, ?_⟩
    · rcases ((Fact.out : l.Prime).dvd_mul).1 h with h | h
      · exact hln h
      · exact hlm h
    · intro b hb
      rcases Finset.mem_insert.1 hb with rfl | hb
      · rw [mul_comm, pow_mul, ha, one_pow]
      · rw [pow_mul, hS b hb, one_pow]

/- English proof (translation)
Establish `: NeZero n` using `⟨hn.ne'⟩`. Take `⟨g, hg⟩` from `IsCyclic.exists_monoid_generator (α := rootsOfUnity n ℂ_[l])`. Use `⟨((g : ℂ_[l]ˣ) : ℂ_[l]), ?_, fun a ha => ?_⟩` and prove the remaining obligations. Use `g.2` as an intermediate fact. Rewrite `this` using `[mem_rootsOfUnity']`.

Conclude with `this`. Take `⟨k, hk⟩` from `hg (rootsOfUnity.mkOfPowEq a ha)`. Use `⟨k, ?_⟩` and prove the remaining obligations. Use `congrArg (fun x : rootsOfUnity n ℂ_[l] => ((x : ℂ_[l]ˣ) : ℂ_[l])) hk` as an intermediate fact. Simplify using `using this`.
-/
theorem muM_exists_gen (n : ℕ) (hn : 0 < n) :
    ∃ g : ℂ_[l], g ^ n = 1 ∧ ∀ a : ℂ_[l], a ^ n = 1 → ∃ k : ℕ, g ^ k = a := by
  have : NeZero n := ⟨hn.ne'⟩
  obtain ⟨g, hg⟩ := IsCyclic.exists_monoid_generator (α := rootsOfUnity n ℂ_[l])
  refine ⟨((g : ℂ_[l]ˣ) : ℂ_[l]), ?_, fun a ha => ?_⟩
  · have := g.2
    rw [mem_rootsOfUnity'] at this
    exact this
  · obtain ⟨k, hk⟩ := hg (rootsOfUnity.mkOfPowEq a ha)
    refine ⟨k, ?_⟩
    have := congrArg (fun x : rootsOfUnity n ℂ_[l] => ((x : ℂ_[l]ˣ) : ℂ_[l])) hk
    simpa using this

/- English proof (translation)
Rewrite `hp`, the goal using `[← algebraMap_int_eq, ← aeval_def]`. Establish `hd : orderOf g ∣ n` using `orderOf_dvd_of_pow_eq_one hg`. Establish `hd0 : 0 < orderOf g` using `Nat.pos_of_dvd_of_pos hd hn`. Establish `hprim : IsPrimitiveRoot g (orderOf g)` using `IsPrimitiveRoot.orderOf g`. Establish `hcop : Nat.Coprime l (orderOf g)` using `((Fact.out : l.Prime).coprime_iff_not_dvd).2 fun h => hln (h.trans hd)`.

Establish `hdvd : minpoly ℤ g ∣ p` using `minpoly.isIntegrallyClosed_dvd (hprim.isIntegral hd0) hp`. Rewrite `hdvd` using `[hprim.minpoly_eq_pow_coprime hcop]`. Conclude with `aeval_eq_zero_of_dvd_aeval_eq_zero hdvd (minpoly.aeval ℤ (g ^ l))`.
-/
theorem muM_eval_pow_eq_zero {K : Type*} [Field K] [CharZero K] (n : ℕ) (hn : 0 < n) (hln : ¬ l ∣ n)
    (g : K) (hg : g ^ n = 1) (p : ℤ[X]) (hp : p.eval₂ (Int.castRingHom K) g = 0) :
    p.eval₂ (Int.castRingHom K) (g ^ l) = 0 := by
  rw [← algebraMap_int_eq, ← aeval_def] at hp ⊢
  have hd : orderOf g ∣ n := orderOf_dvd_of_pow_eq_one hg
  have hd0 : 0 < orderOf g := Nat.pos_of_dvd_of_pos hd hn
  have hprim : IsPrimitiveRoot g (orderOf g) := IsPrimitiveRoot.orderOf g
  have hcop : Nat.Coprime l (orderOf g) :=
    ((Fact.out : l.Prime).coprime_iff_not_dvd).2 fun h => hln (h.trans hd)
  have hdvd : minpoly ℤ g ∣ p := minpoly.isIntegrallyClosed_dvd (hprim.isIntegral hd0) hp
  rw [hprim.minpoly_eq_pow_coprime hcop] at hdvd
  exact aeval_eq_zero_of_dvd_aeval_eq_zero hdvd (minpoly.aeval ℤ (g ^ l))

def phiM : MonoidAlgebra ℤ (muM l) →ₐ[ℤ] ℂ_[l] := MonoidAlgebra.lift ℤ ℂ_[l] (muM l) (muM l).subtype

def psiM : MonoidAlgebra ℤ (muM l) →ₐ[ℤ] ℂ_[l] :=
  MonoidAlgebra.lift ℤ ℂ_[l] (muM l) ((muM l).subtype.comp (powMonoidHom l))

/- English proof (translation)
Take `⟨n, hn, hln, hS⟩` from `muM_common l f.coeff.support`. Take `⟨g, hg, hgen⟩` from `muM_exists_gen l n hn`. Establish `hk : ∀ a : muM l, ∃ k : ℕ, a ∈ f.coeff.support → g ^ k = (a : ℂ_[l])`. Introduce `a`. Distinguish the cases in `ha : a ∈ f.coeff.support`.

Take `⟨k, hk⟩` from `hgen a (hS a ha)`. Conclude with `⟨k, fun _ => hk⟩`. Conclude with `⟨0, fun h => absurd h ha⟩`. Use `choose k hk using hk`. Set `p : ℤ[X]` to `∑ a ∈ f.coeff.support, C (f.coeff a) * X ^ (k a)`.

Establish `h1 : p.eval₂ (Int.castRingHom ℂ_[l]) g = 0`. Rewrite using `[← hf, phiM, MonoidAlgebra.lift_apply, Finsupp.sum, eval₂_finsetSum]`. Use `Finset.sum_congr rfl fun a ha => ?_` and prove the remaining obligations. Rewrite using `[eval₂_mul, eval₂_C, eval₂_pow, eval₂_X, hk a ha]`. Simplify using `[zsmul_eq_mul]`.

Establish `h2` using `muM_eval_pow_eq_zero l n hn hln g hg p h1`. Rewrite using `[← h2, psiM, MonoidAlgebra.lift_apply, Finsupp.sum, eval₂_finsetSum]`. Use `Finset.sum_congr rfl fun a ha => ?_` and prove the remaining obligations. Rewrite using `[eval₂_mul, eval₂_C, eval₂_pow, eval₂_X, ← pow_mul, mul_comm l, pow_mul, hk a ha]`. Simplify using `[zsmul_eq_mul]`.
-/
theorem phiM_ker_le (f : MonoidAlgebra ℤ (muM l)) (hf : phiM l f = 0) : psiM l f = 0 := by
  classical
  obtain ⟨n, hn, hln, hS⟩ := muM_common l f.coeff.support
  obtain ⟨g, hg, hgen⟩ := muM_exists_gen l n hn
  have hk : ∀ a : muM l, ∃ k : ℕ, a ∈ f.coeff.support → g ^ k = (a : ℂ_[l]) := by
    intro a
    by_cases ha : a ∈ f.coeff.support
    · obtain ⟨k, hk⟩ := hgen a (hS a ha)
      exact ⟨k, fun _ => hk⟩
    · exact ⟨0, fun h => absurd h ha⟩
  choose k hk using hk
  let p : ℤ[X] := ∑ a ∈ f.coeff.support, C (f.coeff a) * X ^ (k a)
  have h1 : p.eval₂ (Int.castRingHom ℂ_[l]) g = 0 := by
    rw [← hf, phiM, MonoidAlgebra.lift_apply, Finsupp.sum, eval₂_finsetSum]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [eval₂_mul, eval₂_C, eval₂_pow, eval₂_X, hk a ha]
    simp [zsmul_eq_mul]
  have h2 := muM_eval_pow_eq_zero l n hn hln g hg p h1
  rw [← h2, psiM, MonoidAlgebra.lift_apply, Finsupp.sum, eval₂_finsetSum]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [eval₂_mul, eval₂_C, eval₂_pow, eval₂_X, ← pow_mul, mul_comm l, pow_mul, hk a ha]
  simp [zsmul_eq_mul]

/- English proof (translation)
Rewrite using `[phiM, MonoidAlgebra.lift_apply]`. Conclude with `Subring.sum_mem _ fun a _ => Subring.zsmul_mem _ (Subring.subset_closure a.2) _`.
-/
theorem phiM_mem (f : MonoidAlgebra ℤ (muM l)) : phiM l f ∈ Rmu l := by
  rw [phiM, MonoidAlgebra.lift_apply]
  exact Subring.sum_mem _ fun a _ => Subring.zsmul_mem _ (Subring.subset_closure a.2) _

/- English proof (translation)
Rewrite using `[psiM, MonoidAlgebra.lift_apply]`. Conclude with `Subring.sum_mem _ fun a _ => Subring.zsmul_mem _ (Subring.subset_closure (a ^ l).2) _`.
-/
theorem psiM_mem (f : MonoidAlgebra ℤ (muM l)) : psiM l f ∈ Rmu l := by
  rw [psiM, MonoidAlgebra.lift_apply]
  exact Subring.sum_mem _ fun a _ => Subring.zsmul_mem _ (Subring.subset_closure (a ^ l).2) _

/- English proof (translation)
Establish `: Rmu l ≤ (phiM l : MonoidAlgebra ℤ (muM l) →+* ℂ_[l]).range`. Use `Subring.closure_le.2 fun ζ hζ => ⟨MonoidAlgebra.single ⟨ζ, hζ⟩ 1, ?_⟩` and prove the remaining obligations. Simplify using `[phiM]`. Conclude with `this hx`.
-/
theorem phiM_surj (x : ℂ_[l]) (hx : x ∈ Rmu l) : ∃ f, phiM l f = x := by
  have : Rmu l ≤ (phiM l : MonoidAlgebra ℤ (muM l) →+* ℂ_[l]).range := by
    refine Subring.closure_le.2 fun ζ hζ => ⟨MonoidAlgebra.single ⟨ζ, hζ⟩ 1, ?_⟩
    simp [phiM]
  exact this hx

/- English proof (translation)
Set `φ : MonoidAlgebra ℤ (muM l) →+* Rmu l` to `(phiM l : MonoidAlgebra ℤ (muM l) →+* ℂ_[l]).codRestrict (Rmu l) (phiM_mem l)`. Set `ψ : MonoidAlgebra ℤ (muM l) →+* Rmu l` to `(psiM l : MonoidAlgebra ℤ (muM l) →+* ℂ_[l]).codRestrict (Rmu l) (psiM_mem l)`. Establish `hφ : Function.Surjective φ`. Introduce and unpack `⟨x, hx⟩`. Take `⟨f, hf⟩` from `phiM_surj l x hx`.

Conclude with `⟨f, Subtype.ext hf⟩`. Establish `hker : RingHom.ker φ ≤ RingHom.ker ψ`. Introduce `f hf`. Rewrite `hf`, the goal using `[RingHom.mem_ker]`. Conclude with `Subtype.ext (phiM_ker_le l f (congrArg Subtype.val hf))`.

Use `⟨RingHom.liftOfSurjective φ hφ ⟨ψ, hker⟩, fun ζ hζ => ?_⟩` and prove the remaining obligations. Establish `h1 : (⟨ζ, Subring.subset_closure hζ⟩ : Rmu l) = φ (MonoidAlgebra.single ⟨ζ, hζ⟩ 1)` using `Subtype.ext (by simp [φ, phiM])`. Rewrite using `[h1, RingHom.liftOfRightInverse_comp_apply]`. Simplify using `[ψ, psiM]`.
-/
theorem rmu_sigma : ∃ s : Rmu l →+* Rmu l,
    ∀ (ζ : ℂ_[l]) (hζ : ζ ∈ muP l), ((s ⟨ζ, Subring.subset_closure hζ⟩ : Rmu l) : ℂ_[l]) = ζ ^ l := by
  let φ : MonoidAlgebra ℤ (muM l) →+* Rmu l :=
    (phiM l : MonoidAlgebra ℤ (muM l) →+* ℂ_[l]).codRestrict (Rmu l) (phiM_mem l)
  let ψ : MonoidAlgebra ℤ (muM l) →+* Rmu l :=
    (psiM l : MonoidAlgebra ℤ (muM l) →+* ℂ_[l]).codRestrict (Rmu l) (psiM_mem l)
  have hφ : Function.Surjective φ := by
    rintro ⟨x, hx⟩
    obtain ⟨f, hf⟩ := phiM_surj l x hx
    exact ⟨f, Subtype.ext hf⟩
  have hker : RingHom.ker φ ≤ RingHom.ker ψ := by
    intro f hf
    rw [RingHom.mem_ker] at hf ⊢
    exact Subtype.ext (phiM_ker_le l f (congrArg Subtype.val hf))
  refine ⟨RingHom.liftOfSurjective φ hφ ⟨ψ, hker⟩, fun ζ hζ => ?_⟩
  have h1 : (⟨ζ, Subring.subset_closure hζ⟩ : Rmu l) = φ (MonoidAlgebra.single ⟨ζ, hζ⟩ 1) :=
    Subtype.ext (by simp [φ, phiM])
  rw [h1, RingHom.liftOfRightInverse_comp_apply]
  simp [ψ, psiM]

/- English proof (translation)
Establish `hl : l.Prime` using `Fact.out`. Establish `key : ∀ (y : ℂ_[l]) (hy : y ∈ Rmu l), ∃ r : Rmu l, s ⟨y, hy⟩ - ⟨y, hy⟩ ^ l = (l : Rmu l) * r`. Introduce `y hy`. Proceed by induction on `hy using Subring.closure_induction with`. Consider the case `mem ζ hζ => exact ⟨0, Subtype.ext (by simp [hs ζ hζ])⟩`.

Consider the case `zero`. Use `⟨0, ?_⟩` and prove the remaining obligations. Establish `: (⟨0, zero_mem _⟩ : Rmu l) = 0` using `rfl`. Rewrite using `[this, map_zero, zero_pow hl.ne_zero]`. Simplify using the standard rewrite rules.

Consider the case `one`. Use `⟨0, ?_⟩` and prove the remaining obligations. Establish `: (⟨1, one_mem _⟩ : Rmu l) = 1` using `rfl`. Rewrite using `[this, map_one, one_pow]`. Simplify using the standard rewrite rules.

Consider the case `add a b ha hb iha ihb`. Take `⟨r, hr⟩` from `iha`. Take `⟨t, ht⟩` from `ihb`. Take `⟨u, hu⟩` from `exists_add_pow_prime_eq hl (⟨a, ha⟩ : Rmu l) ⟨b, hb⟩`. Use `⟨r + t - ⟨a, ha⟩ * ⟨b, hb⟩ * u, ?_⟩` and prove the remaining obligations.

Establish `: (⟨a + b, add_mem ha hb⟩ : Rmu l) = ⟨a, ha⟩ + ⟨b, hb⟩` using `rfl`. Rewrite using `[this, map_add, hu]`. Take the linear combination `hr + ht`. Consider the case `neg a ha iha`. Take `⟨r, hr⟩` from `iha`.

Establish `: (⟨-a, neg_mem ha⟩ : Rmu l) = -⟨a, ha⟩` using `rfl`. Rewrite using `[this, map_neg]`. Break down `hl.eq_two_or_odd' with h2 | hodd` into its components or cases. Use `⟨-r - ⟨a, ha⟩ ^ 2, ?_⟩` and prove the remaining obligations. Substitute `h2` using the available equality.

Move the coercions through the operations in `at hr ⊢`. Take the linear combination `-hr`. Use `⟨-r, ?_⟩` and prove the remaining obligations. Rewrite using `[hodd.neg_pow]`. Take the linear combination `-hr`.

Consider the case `mul a b ha hb iha ihb`. Take `⟨r, hr⟩` from `iha`. Take `⟨t, ht⟩` from `ihb`. Use `⟨r * s ⟨b, hb⟩ + ⟨a, ha⟩ ^ l * t, ?_⟩` and prove the remaining obligations. Establish `: (⟨a * b, mul_mem ha hb⟩ : Rmu l) = ⟨a, ha⟩ * ⟨b, hb⟩` using `rfl`.

Rewrite using `[this, map_mul, mul_pow]`. Take the linear combination `s ⟨b, hb⟩ * hr + ⟨a, ha⟩ ^ l * ht`. Take `⟨r, hr⟩` from `key x.1 x.2`. Use `⟨r, r.2, ?_⟩` and prove the remaining obligations. Use `congrArg (Subtype.val) hr` as an intermediate fact.

Simplify using `using this`.
-/
theorem rmu_sigma_congr (s : Rmu l →+* Rmu l)
    (hs : ∀ (ζ : ℂ_[l]) (hζ : ζ ∈ muP l),
      ((s ⟨ζ, Subring.subset_closure hζ⟩ : Rmu l) : ℂ_[l]) = ζ ^ l) (x : Rmu l) :
    ∃ r ∈ Rmu l, ((s x : Rmu l) : ℂ_[l]) - (x : ℂ_[l]) ^ l = (l : ℂ_[l]) * r := by
  have hl : l.Prime := Fact.out
  have key : ∀ (y : ℂ_[l]) (hy : y ∈ Rmu l), ∃ r : Rmu l, s ⟨y, hy⟩ - ⟨y, hy⟩ ^ l = (l : Rmu l) * r := by
    intro y hy
    induction hy using Subring.closure_induction with
    | mem ζ hζ => exact ⟨0, Subtype.ext (by simp [hs ζ hζ])⟩
    | zero =>
      refine ⟨0, ?_⟩
      have : (⟨0, zero_mem _⟩ : Rmu l) = 0 := rfl
      rw [this, map_zero, zero_pow hl.ne_zero]; simp
    | one =>
      refine ⟨0, ?_⟩
      have : (⟨1, one_mem _⟩ : Rmu l) = 1 := rfl
      rw [this, map_one, one_pow]; simp
    | add a b ha hb iha ihb =>
      obtain ⟨r, hr⟩ := iha
      obtain ⟨t, ht⟩ := ihb
      obtain ⟨u, hu⟩ := exists_add_pow_prime_eq hl (⟨a, ha⟩ : Rmu l) ⟨b, hb⟩
      refine ⟨r + t - ⟨a, ha⟩ * ⟨b, hb⟩ * u, ?_⟩
      have : (⟨a + b, add_mem ha hb⟩ : Rmu l) = ⟨a, ha⟩ + ⟨b, hb⟩ := rfl
      rw [this, map_add, hu]
      linear_combination hr + ht
    | neg a ha iha =>
      obtain ⟨r, hr⟩ := iha
      have : (⟨-a, neg_mem ha⟩ : Rmu l) = -⟨a, ha⟩ := rfl
      rw [this, map_neg]
      rcases hl.eq_two_or_odd' with h2 | hodd
      · refine ⟨-r - ⟨a, ha⟩ ^ 2, ?_⟩
        subst h2
        push_cast at hr ⊢
        linear_combination -hr
      · refine ⟨-r, ?_⟩
        rw [hodd.neg_pow]
        linear_combination -hr
    | mul a b ha hb iha ihb =>
      obtain ⟨r, hr⟩ := iha
      obtain ⟨t, ht⟩ := ihb
      refine ⟨r * s ⟨b, hb⟩ + ⟨a, ha⟩ ^ l * t, ?_⟩
      have : (⟨a * b, mul_mem ha hb⟩ : Rmu l) = ⟨a, ha⟩ * ⟨b, hb⟩ := rfl
      rw [this, map_mul, mul_pow]
      linear_combination s ⟨b, hb⟩ * hr + ⟨a, ha⟩ ^ l * ht
  obtain ⟨r, hr⟩ := key x.1 x.2
  refine ⟨r, r.2, ?_⟩
  have := congrArg (Subtype.val) hr
  simpa using this

end ReciprocityTheory.ChartRestriction.L1
