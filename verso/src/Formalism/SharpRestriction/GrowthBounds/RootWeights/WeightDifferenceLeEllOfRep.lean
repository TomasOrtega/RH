import Formalism.SharpRestriction.GrowthBounds.RootWeights.DegreeZeroWeightsBounded

noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

attribute [local instance 100] LieRing.ofAssociativeRing

variable {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/- English proof (translation)
Simplify using `only [weightSp, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero]`.
-/
private theorem mem_weightSp_iff (E : GLOps n K V) (μ : Fin n → ℤ) (x : V) :
    x ∈ weightSp E μ ↔ ∀ c, E c c x = (μ c : K) • x := by
  simp only [weightSp, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero]

/- English proof (translation)
Rewrite `hx`, the goal using `[mem_weightSp_iff]`. Introduce `c`. Establish `hc` using `LinearMap.congr_fun (hE.1 c c a b) x`. Simplify using `only [LinearMap.sub_apply, Module.End.mul_apply, hx c, map_smul] at hc`. Rewrite `hc` using `[sub_eq_iff_eq_add]`.

Distinguish the cases in `h1 : c = a`. Establish `h2 : ¬ b = c` using `fun h => hab (h1.symm.trans h.symm)`. Rewrite `hc` using `[if_pos h1, if_neg h2, h1]`. Rewrite `*` using `[h1]`. Simplify using `only [LinearMap.zero_apply, sub_zero] at hc`.

Rewrite using `[hc]`. Simplify using `only [rootW, Pi.add_apply, Pi.sub_apply, Pi.single_eq_same, Pi.single_apply, hab, if_false, sub_zero, Int.cast_add, Int.cast_one, add_smul, one_smul]`. Normalize the expressions using the abelian group laws. Distinguish the cases in `h2 : b = c`. Rewrite `hc` using `[if_neg h1, if_pos h2]`.

Substitute `h2` using the available equality. Simplify using `only [LinearMap.zero_apply, zero_sub] at hc`. Rewrite using `[hc]`. Simplify using `only [rootW, Pi.add_apply, Pi.sub_apply, Pi.single_eq_same, Pi.single_apply, Ne.symm hab, if_false, zero_sub, Int.cast_add, Int.cast_neg, Int.cast_one, add_smul, neg_smul, one_smul]`. Normalize the expressions using the abelian group laws.

Rewrite `hc` using `[if_neg h1, if_neg h2]`. Simplify using `only [LinearMap.zero_apply, sub_zero, zero_add] at hc`. Rewrite using `[hc]`. Establish `h2' : c ≠ b` using `fun h => h2 h.symm`. Simplify using `only [rootW, Pi.add_apply, Pi.sub_apply, Pi.single_apply, h1, h2', if_false, sub_zero, add_zero]`.
-/
private theorem E_apply_mem_weightSp_add_rootW_of_ne {E : GLOps n K V} (hE : IsGLRep E) {a b : Fin n} (hab : a ≠ b)
    {μ : Fin n → ℤ} {x : V} (hx : x ∈ weightSp E μ) : E a b x ∈ weightSp E (μ + rootW a b) := by
  rw [mem_weightSp_iff] at hx ⊢
  intro c
  have hc := LinearMap.congr_fun (hE.1 c c a b) x
  simp only [LinearMap.sub_apply, Module.End.mul_apply, hx c, map_smul] at hc
  rw [sub_eq_iff_eq_add] at hc
  by_cases h1 : c = a
  · have h2 : ¬ b = c := fun h => hab (h1.symm.trans h.symm)
    rw [if_pos h1, if_neg h2, h1] at hc
    rw [h1] at *
    simp only [LinearMap.zero_apply, sub_zero] at hc
    rw [hc]
    simp only [rootW, Pi.add_apply, Pi.sub_apply, Pi.single_eq_same, Pi.single_apply, hab, if_false,
      sub_zero, Int.cast_add, Int.cast_one, add_smul, one_smul]
    abel
  · by_cases h2 : b = c
    · rw [if_neg h1, if_pos h2] at hc
      subst h2
      simp only [LinearMap.zero_apply, zero_sub] at hc
      rw [hc]
      simp only [rootW, Pi.add_apply, Pi.sub_apply, Pi.single_eq_same, Pi.single_apply,
        Ne.symm hab, if_false, zero_sub, Int.cast_add, Int.cast_neg, Int.cast_one, add_smul,
        neg_smul, one_smul]
      abel
    · rw [if_neg h1, if_neg h2] at hc
      simp only [LinearMap.zero_apply, sub_zero, zero_add] at hc
      rw [hc]
      have h2' : c ≠ b := fun h => h2 h.symm
      simp only [rootW, Pi.add_apply, Pi.sub_apply, Pi.single_apply, h1, h2', if_false, sub_zero,
        add_zero]

/- English proof (translation)
Establish `hNK : (N : K) = (μ a : K) - (μ b : K)` using `by exact_mod_cast hN`. Establish `hlow : ∀ k : ℕ, (E b a ^ k) v ∈ weightSp E (μ + (k : ℤ) • rootW b a)`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => simpa using hv`.

Consider the case `succ k ih`. Establish `h` using `E_apply_mem_weightSp_add_rootW_of_ne hE (Ne.symm hab) ih`. Establish `e : μ + ((k + 1 : ℕ) : ℤ) • rootW b a = μ + (k : ℤ) • rootW b a + rootW b a`. Use `push_cast`. Rewrite using `[add_smul, one_smul, add_assoc]`.

Rewrite using `[pow_succ', Module.End.mul_apply, e]`. Conclude with `h`. Establish `hcomm : ∀ w : V, E a b (E b a w) = E b a (E a b w) + (E a a w - E b b w)`. Introduce `w`. Establish `h` using `LinearMap.congr_fun (hE.1 a b b a) w`.

Simplify using `only [LinearMap.sub_apply, Module.End.mul_apply] at h`. Conclude with `sub_eq_iff_eq_add'.1 h`. Establish `hdiag : ∀ k : ℕ, E a a ((E b a ^ k) v) - E b b ((E b a ^ k) v) = ((N : K) - 2 * k) • (E b a ^ k) v`. Introduce `k`. Establish `h` using `(mem_weightSp_iff E _ _).1 (hlow k)`.

Rewrite using `[h a, h b, ← sub_smul]`. Use `congr 1`. Simplify using `only [rootW, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, Pi.single_eq_same, Pi.single_apply, hab, Ne.symm hab, if_false, smul_eq_mul]`. Use `push_cast`. Rewrite using `[hNK]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hQ : ∀ k : ℕ, E a b ((E b a ^ (k + 1)) v) = (((k : K) + 1) * ((N : K) - k)) • (E b a ^ k) v`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero`.

Establish `h0` using `hdiag 0`. Simplify using `only [pow_zero, Module.End.one_apply, Nat.cast_zero, mul_zero, sub_zero] at h0`. Simplify using `only [zero_add, pow_one, pow_zero, Module.End.one_apply, Nat.cast_zero, sub_zero, one_mul]`. Rewrite using `[hcomm, htop, map_zero, zero_add, h0]`. Consider the case `succ k ih`.

Establish `fold : E b a ((E b a ^ k) v) = (E b a ^ (k + 1)) v`. Rewrite using `[pow_succ', Module.End.mul_apply]`. Rewrite using `[pow_succ' (E b a) (k + 1), Module.End.mul_apply, hcomm, ih, map_smul, fold, hdiag (k + 1), ← add_smul]`. Use `congr 1`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Establish `hne : ∀ k : ℕ, k ≤ N → (E b a ^ k) v ≠ 0`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => intro _`.

Simplify using `using hv0`. Consider the case `succ k ih`. Introduce `hk h`. Apply `ih (by omega)` to reduce the goal to its premises. Establish `hq` using `hQ k`.

Rewrite `hq` using `[h, map_zero]`. Establish `hc : ((k : K) + 1) * ((N : K) - k) ≠ 0`. Apply `mul_ne_zero` to reduce the goal to its premises. Conclude with `Nat.succ_ne_zero k` after adjusting the coercions. Conclude with `sub_ne_zero.2 (by exact_mod_cast (show N ≠ k by omega))`.

Conclude with `(smul_eq_zero.1 hq.symm).resolve_left hc`. Conclude with `⟨hlow N, hne N le_rfl⟩`.
-/
private theorem E_pow_apply_mem_weightSp_ne_zero_of_highest [CharZero K] {E : GLOps n K V} (hE : IsGLRep E) {a b : Fin n}
    (hab : a ≠ b) {μ : Fin n → ℤ} {v : V} (hv : v ∈ weightSp E μ) (hv0 : v ≠ 0)
    (htop : E a b v = 0) (N : ℕ) (hN : (N : ℤ) = μ a - μ b) :
    (E b a ^ N) v ∈ weightSp E (μ + (N : ℤ) • rootW b a) ∧ (E b a ^ N) v ≠ 0 := by
  have hNK : (N : K) = (μ a : K) - (μ b : K) := by exact_mod_cast hN
  have hlow : ∀ k : ℕ, (E b a ^ k) v ∈ weightSp E (μ + (k : ℤ) • rootW b a) := by
    intro k
    induction k with
    | zero => simpa using hv
    | succ k ih =>
      have h := E_apply_mem_weightSp_add_rootW_of_ne hE (Ne.symm hab) ih
      have e : μ + ((k + 1 : ℕ) : ℤ) • rootW b a = μ + (k : ℤ) • rootW b a + rootW b a := by
        push_cast
        rw [add_smul, one_smul, add_assoc]
      rw [pow_succ', Module.End.mul_apply, e]
      exact h
  have hcomm : ∀ w : V, E a b (E b a w) = E b a (E a b w) + (E a a w - E b b w) := by
    intro w
    have h := LinearMap.congr_fun (hE.1 a b b a) w
    simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
    exact sub_eq_iff_eq_add'.1 h
  have hdiag : ∀ k : ℕ, E a a ((E b a ^ k) v) - E b b ((E b a ^ k) v) =
      ((N : K) - 2 * k) • (E b a ^ k) v := by
    intro k
    have h := (mem_weightSp_iff E _ _).1 (hlow k)
    rw [h a, h b, ← sub_smul]
    congr 1
    simp only [rootW, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, Pi.single_eq_same, Pi.single_apply,
      hab, Ne.symm hab, if_false, smul_eq_mul]
    push_cast
    rw [hNK]
    ring
  have hQ : ∀ k : ℕ, E a b ((E b a ^ (k + 1)) v) = (((k : K) + 1) * ((N : K) - k)) • (E b a ^ k) v := by
    intro k
    induction k with
    | zero =>
      have h0 := hdiag 0
      simp only [pow_zero, Module.End.one_apply, Nat.cast_zero, mul_zero, sub_zero] at h0
      simp only [zero_add, pow_one, pow_zero, Module.End.one_apply, Nat.cast_zero, sub_zero, one_mul]
      rw [hcomm, htop, map_zero, zero_add, h0]
    | succ k ih =>
      have fold : E b a ((E b a ^ k) v) = (E b a ^ (k + 1)) v := by
        rw [pow_succ', Module.End.mul_apply]
      rw [pow_succ' (E b a) (k + 1), Module.End.mul_apply, hcomm, ih, map_smul, fold, hdiag (k + 1),
        ← add_smul]
      congr 1
      push_cast
      ring
  have hne : ∀ k : ℕ, k ≤ N → (E b a ^ k) v ≠ 0 := by
    intro k
    induction k with
    | zero => intro _; simpa using hv0
    | succ k ih =>
      intro hk h
      apply ih (by omega)
      have hq := hQ k
      rw [h, map_zero] at hq
      have hc : ((k : K) + 1) * ((N : K) - k) ≠ 0 := by
        apply mul_ne_zero
        · exact_mod_cast Nat.succ_ne_zero k
        · exact sub_ne_zero.2 (by exact_mod_cast (show N ≠ k by omega))
      exact (smul_eq_zero.1 hq.symm).resolve_left hc
  exact ⟨hlow N, hne N le_rfl⟩

/- English proof (translation)
Establish `hfin : ∀ c : Fin n, {z : ℤ | (E c c).HasEigenvalue (z : K)}.Finite` using `fun c => (Module.End.finite_hasEigenvalue (E c c)).preimage Int.cast_injective.injOn`. Use `(Set.Finite.pi (t := fun c => {z : ℤ | (E c c).HasEigenvalue (z : K)}) hfin).subset ?_` and prove the remaining obligations. Introduce `μ hμ`. Take `⟨x, hx, hx0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hμ`. Rewrite `hx` using `[mem_weightSp_iff]`.

Simplify using `only [Set.mem_pi, Set.mem_univ, Set.mem_ofPred_eq, true_implies]`. Introduce `c`. Conclude with `Module.End.hasEigenvalue_of_hasEigenvector (Module.End.hasEigenvector_iff.2 ⟨Module.End.mem_eigenspace_iff.2 (hx c), hx0⟩)`.
-/
private theorem finite_set_of_nonzero_weightSp [CharZero K] [FiniteDimensional K V] (E : GLOps n K V) :
    {μ : Fin n → ℤ | weightSp E μ ≠ ⊥}.Finite := by
  have hfin : ∀ c : Fin n, {z : ℤ | (E c c).HasEigenvalue (z : K)}.Finite := fun c =>
    (Module.End.finite_hasEigenvalue (E c c)).preimage Int.cast_injective.injOn
  refine (Set.Finite.pi (t := fun c => {z : ℤ | (E c c).HasEigenvalue (z : K)}) hfin).subset ?_
  intro μ hμ
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hμ
  rw [mem_weightSp_iff] at hx
  simp only [Set.mem_pi, Set.mem_univ, Set.mem_ofPred_eq, true_implies]
  intro c
  exact Module.End.hasEigenvalue_of_hasEigenvector
    (Module.End.hasEigenvector_iff.2 ⟨Module.End.mem_eigenspace_iff.2 (hx c), hx0⟩)

/- English proof (translation)
Establish `hinj : Function.Injective (fun t : ℕ => ν + (t : ℤ) • rootW a b)`. Introduce `t1 t2 h`. Establish `h'` using `congr_fun h a`. Simplify using `[rootW, hab] at h'`. Conclude with `h'` after adjusting the coercions.

Take `⟨T, hTdef⟩ : ∃ T : Set ℕ, T = {t : ℕ | weightSp E (ν + (t : ℤ) • rootW a b) ≠ ⊥}` from `⟨_, rfl⟩`. Establish `hT : T.Finite`. Rewrite using `[hTdef]`. Conclude with `(finite_set_of_nonzero_weightSp E).preimage hinj.injOn`. Establish `h0 : (0 : ℕ) ∈ T`.

Rewrite using `[hTdef]`. Simplify using `using hν`. Establish `ht : sSup T ∈ T` using `Nat.sSup_mem ⟨0, h0⟩ hT.bddAbove`. Establish `ht1 : sSup T + 1 ∉ T` using `fun h => by`. Use `le_csSup hT.bddAbove h` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Establish `ht' : weightSp E (ν + ((sSup T : ℕ) : ℤ) • rootW a b) ≠ ⊥` using `(Set.ext_iff.1 hTdef _).1 ht`. Establish `ht1' : ¬ weightSp E (ν + ((sSup T + 1 : ℕ) : ℤ) • rootW a b) ≠ ⊥` using `fun h => ht1 ((Set.ext_iff.1 hTdef _).2 h)`. Take `⟨v, hv, hv0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot ht'`. Establish `htop : E a b v = 0`.

Establish `h1` using `E_apply_mem_weightSp_add_rootW_of_ne hE hab hv`. Establish `e : ν + ((sSup T : ℕ) : ℤ) • rootW a b + rootW a b = ν + ((sSup T + 1 : ℕ) : ℤ) • rootW a b`. Use `push_cast`. Rewrite using `[add_smul, one_smul, add_assoc]`. Rewrite `h1` using `[e]`.

Establish `hbot : weightSp E (ν + ((sSup T + 1 : ℕ) : ℤ) • rootW a b) = ⊥`. Assume the negation of the conclusion as `hne`. Conclude with `ht1' hne`. Rewrite `h1` using `[hbot, Submodule.mem_bot]`. Conclude with `h1`.

Establish `hμa : (ν + ((sSup T : ℕ) : ℤ) • rootW a b) a = ν a + sSup T`. Simplify using `[rootW, hab]`. Establish `hμb : (ν + ((sSup T : ℕ) : ℤ) • rootW a b) b = ν b - sSup T`. Simplify using `[rootW, Ne.symm hab]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hnn : 0 ≤ ν a - ν b + 2 * ((sSup T : ℕ) : ℤ)` using `by omega`. Use `⟨sSup T, (ν a - ν b + 2 * ((sSup T : ℕ) : ℤ)).toNat, Int.toNat_of_nonneg hnn, ht', ?_⟩` and prove the remaining obligations. Take `⟨hmem, hne⟩` from `E_pow_apply_mem_weightSp_ne_zero_of_highest hE hab hv hv0 htop _ (by rw [Int.toNat_of_nonneg hnn, hμa, hμb]; ring)`. Introduce `hbot`. Rewrite `hmem` using `[hbot, Submodule.mem_bot]`.

Conclude with `hne hmem`.
-/
theorem root_string_through_weight [CharZero K] [FiniteDimensional K V] {E : GLOps n K V} (hE : IsGLRep E) (ν : Fin n → ℤ)
    (hν : weightSp E ν ≠ ⊥) (a b : Fin n) (hab : a ≠ b) (hpos : 0 < ν a - ν b) :
    ∃ t N : ℕ, (N : ℤ) = ν a - ν b + 2 * t ∧ weightSp E (ν + (t : ℤ) • rootW a b) ≠ ⊥ ∧
      weightSp E (ν + (t : ℤ) • rootW a b + (N : ℤ) • rootW b a) ≠ ⊥ := by
  classical
  have hinj : Function.Injective (fun t : ℕ => ν + (t : ℤ) • rootW a b) := by
    intro t1 t2 h
    have h' := congr_fun h a
    simp [rootW, hab] at h'
    exact_mod_cast h'
  obtain ⟨T, hTdef⟩ : ∃ T : Set ℕ, T = {t : ℕ | weightSp E (ν + (t : ℤ) • rootW a b) ≠ ⊥} := ⟨_, rfl⟩
  have hT : T.Finite := by
    rw [hTdef]
    exact (finite_set_of_nonzero_weightSp E).preimage hinj.injOn
  have h0 : (0 : ℕ) ∈ T := by
    rw [hTdef]
    simpa using hν
  have ht : sSup T ∈ T := Nat.sSup_mem ⟨0, h0⟩ hT.bddAbove
  have ht1 : sSup T + 1 ∉ T := fun h => by
    have := le_csSup hT.bddAbove h
    omega
  have ht' : weightSp E (ν + ((sSup T : ℕ) : ℤ) • rootW a b) ≠ ⊥ := (Set.ext_iff.1 hTdef _).1 ht
  have ht1' : ¬ weightSp E (ν + ((sSup T + 1 : ℕ) : ℤ) • rootW a b) ≠ ⊥ :=
    fun h => ht1 ((Set.ext_iff.1 hTdef _).2 h)
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot ht'
  have htop : E a b v = 0 := by
    have h1 := E_apply_mem_weightSp_add_rootW_of_ne hE hab hv
    have e : ν + ((sSup T : ℕ) : ℤ) • rootW a b + rootW a b =
        ν + ((sSup T + 1 : ℕ) : ℤ) • rootW a b := by
      push_cast
      rw [add_smul, one_smul, add_assoc]
    rw [e] at h1
    have hbot : weightSp E (ν + ((sSup T + 1 : ℕ) : ℤ) • rootW a b) = ⊥ := by
      by_contra hne
      exact ht1' hne
    rw [hbot, Submodule.mem_bot] at h1
    exact h1
  have hμa : (ν + ((sSup T : ℕ) : ℤ) • rootW a b) a = ν a + sSup T := by
    simp [rootW, hab]
  have hμb : (ν + ((sSup T : ℕ) : ℤ) • rootW a b) b = ν b - sSup T := by
    simp [rootW, Ne.symm hab]
    ring
  have hnn : 0 ≤ ν a - ν b + 2 * ((sSup T : ℕ) : ℤ) := by omega
  refine ⟨sSup T, (ν a - ν b + 2 * ((sSup T : ℕ) : ℤ)).toNat, Int.toNat_of_nonneg hnn, ht', ?_⟩
  obtain ⟨hmem, hne⟩ := E_pow_apply_mem_weightSp_ne_zero_of_highest hE hab hv hv0 htop _
    (by rw [Int.toNat_of_nonneg hnn, hμa, hμb]; ring)
  intro hbot
  rw [hbot, Submodule.mem_bot] at hmem
  exact hne hmem

/- English proof (translation)
Establish `hW` using `finite_set_of_nonzero_weightSp E`. Establish `hsub : {k : ℕ | ∃ mu ∈ wtsOf E (⊤ : Submodule K V), ∃ nu ∈ wtsOf E (⊤ : Submodule K V), ∃ a b, a ≠ b ∧ mu - nu = (k : ℤ) • rootW a b} ⊆ (fun p : (Fin n → ℤ) × (Fin n → ℤ) × Fin n => (p.1 p.2.2 - p.2.1 p.2.2).toNat) '' ({μ : Fin n → ℤ | weightSp E μ ≠ ⊥} ×ˢ ({μ : Fin n → ℤ | weigh …`. Introduce and unpack `k ⟨mu, hmu, nu, hnu, a, b, hab, h⟩`. Establish `hmu' : weightSp E mu ≠ ⊥` using `by simpa [wtsOf] using hmu`. Establish `hnu' : weightSp E nu ≠ ⊥` using `by simpa [wtsOf] using hnu`.

Use `⟨(mu, nu, a), ⟨hmu', hnu', Set.mem_univ _⟩, ?_⟩` and prove the remaining obligations. Establish `h'` using `congr_fun h a`. Simplify using `[rootW, hab] at h'`. Simplify using `[h']`. Conclude with `((hW.prod (hW.prod Set.finite_univ)).image _).subset hsub |>.bddAbove`.
-/
theorem root_differences_bddAbove_top [CharZero K] [FiniteDimensional K V] (E : GLOps n K V) :
    BddAbove {k : ℕ | ∃ mu ∈ wtsOf E (⊤ : Submodule K V), ∃ nu ∈ wtsOf E (⊤ : Submodule K V), ∃ a b, a ≠ b ∧
      mu - nu = (k : ℤ) • rootW a b} := by
  classical
  have hW := finite_set_of_nonzero_weightSp E
  have hsub : {k : ℕ | ∃ mu ∈ wtsOf E (⊤ : Submodule K V), ∃ nu ∈ wtsOf E (⊤ : Submodule K V), ∃ a b,
      a ≠ b ∧ mu - nu = (k : ℤ) • rootW a b} ⊆
      (fun p : (Fin n → ℤ) × (Fin n → ℤ) × Fin n => (p.1 p.2.2 - p.2.1 p.2.2).toNat) ''
        ({μ : Fin n → ℤ | weightSp E μ ≠ ⊥} ×ˢ ({μ : Fin n → ℤ | weightSp E μ ≠ ⊥} ×ˢ Set.univ)) := by
    rintro k ⟨mu, hmu, nu, hnu, a, b, hab, h⟩
    have hmu' : weightSp E mu ≠ ⊥ := by simpa [wtsOf] using hmu
    have hnu' : weightSp E nu ≠ ⊥ := by simpa [wtsOf] using hnu
    refine ⟨(mu, nu, a), ⟨hmu', hnu', Set.mem_univ _⟩, ?_⟩
    have h' := congr_fun h a
    simp [rootW, hab] at h'
    simp [h']
  exact ((hW.prod (hW.prod Set.finite_univ)).image _).subset hsub |>.bddAbove

/- English proof (translation)
Take `⟨t, N, hN, h1, h2⟩` from `root_string_through_weight hE ν hν a b hab hpos`. Establish `hr : rootW b a = -rootW a b`. Use extensionality with `c`. Simplify using `only [rootW, Pi.sub_apply, Pi.neg_apply]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hmem : N ∈ {k : ℕ | ∃ mu ∈ wtsOf E (⊤ : Submodule K V), ∃ nu ∈ wtsOf E (⊤ : Submodule K V), ∃ a b, a ≠ b ∧ mu - nu = (k : ℤ) • rootW a b}`. Use `⟨_, by simpa [wtsOf] using h1, _, by simpa [wtsOf] using h2, a, b, hab, ?_⟩` and prove the remaining obligations. Rewrite using `[hr]`. Use extensionality with `c`. Simplify using `only [Pi.sub_apply, Pi.add_apply, Pi.mul_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul, Pi.natCast_apply]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hle : N ≤ ellOf E (⊤ : Submodule K V)` using `le_csSup (root_differences_bddAbove_top E) hmem`. Establish `hle'` using `(Nat.cast_le (α := ℤ)).2 hle`. Use linear arithmetic over natural numbers and integers.
-/
theorem weight_difference_le_ell_of_rep [CharZero K] [FiniteDimensional K V] {E : GLOps n K V} (hE : IsGLRep E) (ν : Fin n → ℤ)
    (hν : weightSp E ν ≠ ⊥) (a b : Fin n) (hab : a ≠ b) (hpos : 0 < ν a - ν b) :
    ν a - ν b ≤ (ellOf E (⊤ : Submodule K V) : ℤ) := by
  obtain ⟨t, N, hN, h1, h2⟩ := root_string_through_weight hE ν hν a b hab hpos
  have hr : rootW b a = -rootW a b := by
    ext c
    simp only [rootW, Pi.sub_apply, Pi.neg_apply]
    ring
  have hmem : N ∈ {k : ℕ | ∃ mu ∈ wtsOf E (⊤ : Submodule K V), ∃ nu ∈ wtsOf E (⊤ : Submodule K V),
      ∃ a b, a ≠ b ∧ mu - nu = (k : ℤ) • rootW a b} := by
    refine ⟨_, by simpa [wtsOf] using h1, _, by simpa [wtsOf] using h2, a, b, hab, ?_⟩
    rw [hr]
    ext c
    simp only [Pi.sub_apply, Pi.add_apply, Pi.mul_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul,
      Pi.natCast_apply]
    ring
  have hle : N ≤ ellOf E (⊤ : Submodule K V) := le_csSup (root_differences_bddAbove_top E) hmem
  have hle' := (Nat.cast_le (α := ℤ)).2 hle
  omega

end Formalism.MainNotions.G.GLWeightTheory
