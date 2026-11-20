import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsGenericFlag
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.JoinCoordsCentreChartStatement
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

namespace GlobalTheory.CompanionTheory.Ar.ChNorm

/- English proof (translation)
Take `⟨p, hp, hpv⟩` from `hv`. Establish `huv : v * v⁻¹ = 1` using `mul_inv_cancel₀ hv0`. Establish `key : ∀ i m : ℕ, i ≤ m → v ^ i * v⁻¹ ^ m = v⁻¹ ^ (m - i)`. Introduce `i m him`. Take `⟨k, rfl⟩` from `Nat.exists_eq_add_of_le him`.

Rewrite using `[pow_add, ← mul_assoc, ← mul_pow, huv, one_pow, one_mul, Nat.add_sub_cancel_left]`. Rewrite `hpv` using `[hp.as_sum]`. Simplify using `only [Polynomial.eval₂_add, Polynomial.eval₂_finsetSum, Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X_pow] at hpv`. Generalize the expression as in `p.natDegree = n at hpv`. Consider the cases of `n with`.

Consider the case `zero => simp at hpv`. Consider the case `succ m`. Establish `h2` using `congrArg (· * v⁻¹ ^ m) hpv`. Simplify using `only [add_mul, Finset.sum_mul, zero_mul] at h2`. Rewrite `h2` using `[pow_succ, mul_comm (v ^ m) v, mul_assoc, key m m le_rfl, Nat.sub_self, pow_zero, mul_one]`.

Establish `e : v = -∑ i ∈ Finset.range (m + 1), algebraMap R Ω (p.coeff i) * v⁻¹ ^ (m - i)`. Rewrite using `[eq_neg_iff_add_eq_zero, ← h2]`. Use `congr 1`. Use `Finset.sum_congr rfl fun i hi => ?_` and prove the remaining obligations. Rewrite using `[mul_assoc, key i m (by simp at hi; omega)]`.

Rewrite using `[e]`. Use `neg_mem (sum_mem fun i _ => mul_mem ?_ (pow_mem hu _))` and prove the remaining obligations. Conclude with `(p.coeff i).2`.
-/
theorem mem_of_isIntegral_of_inv_mem {Ω : Type} [Field Ω] (R : Subring Ω) {v : Ω} (hv : IsIntegral R v)
    (hv0 : v ≠ 0) (hu : v⁻¹ ∈ R) : v ∈ R := by
  obtain ⟨p, hp, hpv⟩ := hv
  have huv : v * v⁻¹ = 1 := mul_inv_cancel₀ hv0
  have key : ∀ i m : ℕ, i ≤ m → v ^ i * v⁻¹ ^ m = v⁻¹ ^ (m - i) := by
    intro i m him
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le him
    rw [pow_add, ← mul_assoc, ← mul_pow, huv, one_pow, one_mul, Nat.add_sub_cancel_left]
  rw [hp.as_sum] at hpv
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_finsetSum, Polynomial.eval₂_mul, Polynomial.eval₂_C,
    Polynomial.eval₂_X_pow] at hpv
  generalize p.natDegree = n at hpv
  cases n with
  | zero => simp at hpv
  | succ m =>
    have h2 := congrArg (· * v⁻¹ ^ m) hpv
    simp only [add_mul, Finset.sum_mul, zero_mul] at h2
    rw [pow_succ, mul_comm (v ^ m) v, mul_assoc, key m m le_rfl, Nat.sub_self, pow_zero, mul_one] at h2
    have e : v = -∑ i ∈ Finset.range (m + 1), algebraMap R Ω (p.coeff i) * v⁻¹ ^ (m - i) := by
      rw [eq_neg_iff_add_eq_zero, ← h2]
      congr 1
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [mul_assoc, key i m (by simp at hi; omega)]
    rw [e]
    refine neg_mem (sum_mem fun i _ => mul_mem ?_ (pow_mem hu _))
    exact (p.coeff i).2

end GlobalTheory.CompanionTheory.Ar.ChNorm

namespace GlobalTheory.CompanionTheory.Ar.ChNorm

/- English proof (translation)
Establish `hd : x c ^ d ≠ 0` using `pow_ne_zero _ hc`. Establish `hrat : ∀ q : κ × (κ ⊕ Fin n), joinCo (RingHom.id Ω) x z q / joinCo (RingHom.id Ω) x z (c, Sum.inl c) = x q.1 / x c * (z q.2 / x c ^ d)`. Introduce `q`. Simplify using `only [joinCo, RingHom.id_apply, hz c]`. Conclude with `mul_div_mul_comm _ _ _ _`.

Establish `hT : chRing o (joinCo (RingHom.id Ω) x z) (c, Sum.inl c) = Algebra.adjoin o (Set.range (fun j => x j / x c) ∪ Set.range (fun k => z k / x c ^ d))`. Apply `le_antisymm` to reduce the goal to its premises. Apply `Algebra.adjoin_le` to reduce the goal to its premises. Introduce and unpack `_ ⟨q, rfl⟩`. Simplify using `only`.

Rewrite using `[hrat]`. Conclude with `mul_mem (Algebra.subset_adjoin (Or.inl ⟨q.1, rfl⟩)) (Algebra.subset_adjoin (Or.inr ⟨q.2, rfl⟩))`. Apply `Algebra.adjoin_le` to reduce the goal to its premises. Introduce and unpack `_ (⟨j, rfl⟩ | ⟨k, rfl⟩)`. Establish `h1 : joinCo (RingHom.id Ω) x z (j, Sum.inl c) / joinCo (RingHom.id Ω) x z (c, Sum.inl c) ∈ chRing o (joinCo (RingHom.id Ω) x z) (c, Sum.inl c)` using `Algebra.subset_adjoin (Set.mem_range_self (j, Sum.inl c))`.

Rewrite `h1` using `[hrat, hz c, div_self hd, mul_one]`. Conclude with `h1`. Establish `h1 : joinCo (RingHom.id Ω) x z (c, k) / joinCo (RingHom.id Ω) x z (c, Sum.inl c) ∈ chRing o (joinCo (RingHom.id Ω) x z) (c, Sum.inl c)` using `Algebra.subset_adjoin (Set.mem_range_self (c, k))`. Rewrite `h1` using `[hrat, div_self hc, one_mul]`. Conclude with `h1`.

Rewrite using `[hT]`.
-/
theorem chRing_join_iff {o : Type} [CommRing o] {Ω : Type} [Field Ω] [Algebra o Ω] {κ : Type} (x : κ → Ω)
    {d n : ℕ} (z : κ ⊕ Fin n → Ω) (hz : ∀ c, z (Sum.inl c) = x c ^ d) (c : κ) (hc : x c ≠ 0) (a : Ω) :
    a ∈ chRing o (joinCo (RingHom.id Ω) x z) (c, Sum.inl c) ↔
      a ∈ Algebra.adjoin o (Set.range (fun j => x j / x c) ∪ Set.range (fun k => z k / x c ^ d)) := by
  have hd : x c ^ d ≠ 0 := pow_ne_zero _ hc
  have hrat : ∀ q : κ × (κ ⊕ Fin n), joinCo (RingHom.id Ω) x z q / joinCo (RingHom.id Ω) x z (c, Sum.inl c) =
      x q.1 / x c * (z q.2 / x c ^ d) := by
    intro q
    simp only [joinCo, RingHom.id_apply, hz c]
    exact mul_div_mul_comm _ _ _ _
  have hT : chRing o (joinCo (RingHom.id Ω) x z) (c, Sum.inl c) =
      Algebra.adjoin o (Set.range (fun j => x j / x c) ∪ Set.range (fun k => z k / x c ^ d)) := by
    apply le_antisymm
    · apply Algebra.adjoin_le
      rintro _ ⟨q, rfl⟩
      dsimp only
      rw [hrat]
      exact mul_mem (Algebra.subset_adjoin (Or.inl ⟨q.1, rfl⟩)) (Algebra.subset_adjoin (Or.inr ⟨q.2, rfl⟩))
    · apply Algebra.adjoin_le
      rintro _ (⟨j, rfl⟩ | ⟨k, rfl⟩)
      · have h1 : joinCo (RingHom.id Ω) x z (j, Sum.inl c) / joinCo (RingHom.id Ω) x z (c, Sum.inl c) ∈
            chRing o (joinCo (RingHom.id Ω) x z) (c, Sum.inl c) :=
          Algebra.subset_adjoin (Set.mem_range_self (j, Sum.inl c))
        rw [hrat, hz c, div_self hd, mul_one] at h1
        exact h1
      · have h1 : joinCo (RingHom.id Ω) x z (c, k) / joinCo (RingHom.id Ω) x z (c, Sum.inl c) ∈
            chRing o (joinCo (RingHom.id Ω) x z) (c, Sum.inl c) :=
          Algebra.subset_adjoin (Set.mem_range_self (c, k))
        rw [hrat, div_self hc, one_mul] at h1
        exact h1
  rw [hT]

end GlobalTheory.CompanionTheory.Ar.ChNorm

namespace GlobalTheory.CompanionTheory.Ar.ChNorm

/- English proof (translation)
Simplify using `only [joinCo, RingHom.id_apply, hz c]`. Conclude with `mul_div_mul_comm _ _ _ _`.
-/
theorem joinCo_div {Ω : Type} [Field Ω] {κ : Type} (x : κ → Ω) {d n : ℕ} (z : κ ⊕ Fin n → Ω)
    (hz : ∀ c, z (Sum.inl c) = x c ^ d) (c : κ) (q : κ × (κ ⊕ Fin n)) :
    joinCo (RingHom.id Ω) x z q / joinCo (RingHom.id Ω) x z (c, Sum.inl c) = x q.1 / x c * (z q.2 / x c ^ d) := by
  simp only [joinCo, RingHom.id_apply, hz c]
  exact mul_div_mul_comm _ _ _ _

/- English proof (translation)
Introduce `o _ Ω _ _ κ _ x d n z M' hz hspan c hc`. Establish `hd : x c ^ d ≠ 0` using `pow_ne_zero _ hc`. Establish `hyS : ∀ k, IsIntegral (chRing o x c) (z k / x c ^ d)` using `fun k => (hspan c hc _).2 (Submodule.subset_span ⟨k, rfl⟩)`. Establish `hxS : ∀ j, x j / x c ∈ chRing o x c` using `fun j => Algebra.subset_adjoin ⟨j, rfl⟩`. Use `⟨fun a => ?_, fun p' hp' => ?_⟩` and prove the remaining obligations.

Rewrite using `[chRing_join_iff x z hz c hc a]`. Prove the components needed by the constructor for the conclusion. Introduce `ha`. Establish `hle : Algebra.adjoin o (Set.range (fun j => x j / x c) ∪ Set.range (fun k => z k / x c ^ d)) ≤ (integralClosure (chRing o x c) Ω).restrictScalars o`. Apply `Algebra.adjoin_le` to reduce the goal to its premises.

Introduce and unpack `_ (⟨j, rfl⟩ | ⟨k, rfl⟩)`. Conclude with `(Subalgebra.mem_restrictScalars o).2 ((mem_integralClosure_iff _ _).2 (isIntegral_algebraMap (x := (⟨_, hxS j⟩ : chRing o x c))))`. Conclude with `(Subalgebra.mem_restrictScalars o).2 ((mem_integralClosure_iff _ _).2 (hyS k))`. Conclude with `(mem_integralClosure_iff _ _).1 ((Subalgebra.mem_restrictScalars o).1 (hle ha))`. Introduce `ha`.

Establish `hSle : chRing o x c ≤ Algebra.adjoin o (Set.range (fun j => x j / x c) ∪ Set.range (fun k => z k / x c ^ d))` using `Algebra.adjoin_mono Set.subset_union_left`. Use `Submodule.span_induction (p := fun b _ => b ∈ Algebra.adjoin o (Set.range (fun j => x j / x c) ∪ Set.range (fun k => z k / x c ^ d))) ?_ ?_ ?_ ?_ ((hspan c hc a).1 ha)` and prove the remaining obligations. Introduce and unpack `_ ⟨k, rfl⟩`. Conclude with `Algebra.subset_adjoin (Or.inr ⟨k, rfl⟩)`. Conclude with `zero_mem _`.

Introduce `a b _ _ ha hb`. Conclude with `add_mem ha hb`. Introduce `s b _ hb`. Rewrite using `[Subalgebra.smul_def]`. Conclude with `mul_mem (hSle s.2) hb`.

Take `⟨hctr, l, hl⟩` from `GlobalTheory.T.join_coords_centre_chart o Ω κ (κ ⊕ Fin n) x Ω (RingHom.id Ω) z M' (fun _ => rfl) p'`. Take `⟨c', -, hc'⟩` from `hctr`. Establish `ho : ∀ r : o, algebraMap o Ω r ∈ regAt M'.ξ p'` using `fun r => hc' _ (Subalgebra.algebraMap_mem _ r)`. Establish `hSle : ∀ a ∈ chRing o x c, a ∈ regAt M'.ξ p'`. Introduce `a ha`.

Establish `h1 : a ∈ (chRing o x c).toSubring` using `ha`. Rewrite `h1` using `[chRing, Algebra.adjoin_eq_ring_closure]`. Conclude with `(Subring.closure_le.2 (Set.union_subset (by rintro _ ⟨r, rfl⟩; exact ho r) (by rintro _ ⟨j, rfl⟩; exact hp' j))) h1`. Set `φ : chRing o x c →+* regAt M'.ξ p'` to `{ toFun := fun s => ⟨s, hSle s s.2⟩ map_one' := rfl map_mul' := fun _ _ => rfl map_zero' := rfl map_add' := fun _ _ => rfl }`. Establish `hvint : IsIntegral (regAt M'.ξ p') (z l / x c ^ d)` using `IsIntegral.map_of_comp_eq φ (RingHom.id Ω) (by ext; rfl) (hyS l)`.

Take `⟨hzl, hzr⟩` from `hl`. Establish `hv : z l / x c ^ d ∈ regAt M'.ξ p'` using `mem_of_isIntegral_of_inv_mem _ hvint (div_ne_zero hzl hd) (by rw [inv_div, ← hz c]; exact hzr _)`. Establish `hy : ∀ k, z k / x c ^ d ∈ regAt M'.ξ p'` using `fun k => by`. Establish `e : z k / x c ^ d = z k / z l * (z l / x c ^ d)` using `by field_simp`. Rewrite using `[e]`.

Conclude with `mul_mem (hzr k) hv`. Use `⟨?_, fun q => ?_⟩` and prove the remaining obligations. Simplify using `only [joinCo, RingHom.id_apply, hz c]`. Conclude with `mul_ne_zero hc hd`. Rewrite using `[joinCo_div x z hz c q]`.

Conclude with `mul_mem (hp' q.1) (hy q.2)`.
-/
theorem join_chart_normalisation : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (d n : ℕ) (z : κ ⊕ Fin n → Ω) (M' : PModel o (joinCo (RingHom.id Ω) x z)), (∀ c, z (Sum.inl c) = x c ^ d) → (∀ c, x c ≠ 0 → ∀ a : Ω, IsIntegral (chRing o x c) a ↔ a ∈ Submodule.span (chRing o x c) (Set.range fun k => z k / x c ^ d)) → ∀ c, x c ≠ 0 → (∀ a : Ω, a ∈ chRing o (joinCo (RingHom.id Ω) x z) (c, Sum.inl c) ↔ IsIntegral (chRing o x c) a) ∧ ∀ p' : Cpt M'.ξ, (∀ j, x j / x c ∈ regAt M'.ξ p') → InChart M'.ξ (joinCo (RingHom.id Ω) x z) (c, Sum.inl c) p' := by
  intro o _ Ω _ _ κ _ x d n z M' hz hspan c hc
  have hd : x c ^ d ≠ 0 := pow_ne_zero _ hc
  have hyS : ∀ k, IsIntegral (chRing o x c) (z k / x c ^ d) := fun k =>
    (hspan c hc _).2 (Submodule.subset_span ⟨k, rfl⟩)
  have hxS : ∀ j, x j / x c ∈ chRing o x c := fun j => Algebra.subset_adjoin ⟨j, rfl⟩
  refine ⟨fun a => ?_, fun p' hp' => ?_⟩
  · rw [chRing_join_iff x z hz c hc a]
    constructor
    · intro ha
      have hle : Algebra.adjoin o (Set.range (fun j => x j / x c) ∪ Set.range (fun k => z k / x c ^ d)) ≤
          (integralClosure (chRing o x c) Ω).restrictScalars o := by
        apply Algebra.adjoin_le
        rintro _ (⟨j, rfl⟩ | ⟨k, rfl⟩)
        · exact (Subalgebra.mem_restrictScalars o).2 ((mem_integralClosure_iff _ _).2
            (isIntegral_algebraMap (x := (⟨_, hxS j⟩ : chRing o x c))))
        · exact (Subalgebra.mem_restrictScalars o).2 ((mem_integralClosure_iff _ _).2 (hyS k))
      exact (mem_integralClosure_iff _ _).1 ((Subalgebra.mem_restrictScalars o).1 (hle ha))
    · intro ha
      have hSle : chRing o x c ≤
          Algebra.adjoin o (Set.range (fun j => x j / x c) ∪ Set.range (fun k => z k / x c ^ d)) :=
        Algebra.adjoin_mono Set.subset_union_left
      refine Submodule.span_induction
        (p := fun b _ => b ∈ Algebra.adjoin o (Set.range (fun j => x j / x c) ∪ Set.range (fun k => z k / x c ^ d)))
        ?_ ?_ ?_ ?_ ((hspan c hc a).1 ha)
      · rintro _ ⟨k, rfl⟩
        exact Algebra.subset_adjoin (Or.inr ⟨k, rfl⟩)
      · exact zero_mem _
      · intro a b _ _ ha hb
        exact add_mem ha hb
      · intro s b _ hb
        rw [Subalgebra.smul_def]
        exact mul_mem (hSle s.2) hb
  · obtain ⟨hctr, l, hl⟩ :=
      GlobalTheory.T.join_coords_centre_chart o Ω κ (κ ⊕ Fin n) x Ω (RingHom.id Ω) z M' (fun _ => rfl) p'
    obtain ⟨c', -, hc'⟩ := hctr
    have ho : ∀ r : o, algebraMap o Ω r ∈ regAt M'.ξ p' := fun r =>
      hc' _ (Subalgebra.algebraMap_mem _ r)
    have hSle : ∀ a ∈ chRing o x c, a ∈ regAt M'.ξ p' := by
      intro a ha
      have h1 : a ∈ (chRing o x c).toSubring := ha
      rw [chRing, Algebra.adjoin_eq_ring_closure] at h1
      exact (Subring.closure_le.2 (Set.union_subset (by rintro _ ⟨r, rfl⟩; exact ho r)
        (by rintro _ ⟨j, rfl⟩; exact hp' j))) h1
    let φ : chRing o x c →+* regAt M'.ξ p' :=
      { toFun := fun s => ⟨s, hSle s s.2⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl
        map_zero' := rfl
        map_add' := fun _ _ => rfl }
    have hvint : IsIntegral (regAt M'.ξ p') (z l / x c ^ d) :=
      IsIntegral.map_of_comp_eq φ (RingHom.id Ω) (by ext; rfl) (hyS l)
    obtain ⟨hzl, hzr⟩ := hl
    have hv : z l / x c ^ d ∈ regAt M'.ξ p' :=
      mem_of_isIntegral_of_inv_mem _ hvint (div_ne_zero hzl hd) (by rw [inv_div, ← hz c]; exact hzr _)
    have hy : ∀ k, z k / x c ^ d ∈ regAt M'.ξ p' := fun k => by
      have e : z k / x c ^ d = z k / z l * (z l / x c ^ d) := by field_simp
      rw [e]
      exact mul_mem (hzr k) hv
    refine ⟨?_, fun q => ?_⟩
    · simp only [joinCo, RingHom.id_apply, hz c]
      exact mul_ne_zero hc hd
    · rw [joinCo_div x z hz c q]
      exact mul_mem (hp' q.1) (hy q.2)

end GlobalTheory.CompanionTheory.Ar.ChNorm
