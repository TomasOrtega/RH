import Mathlib

namespace FunctorialResolution.EmbeddedResolution

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Treat this case separately. Treat this case separately.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem derivation_apply_mem_of_mem_span {k : Type*} [CommRing k] {S : Type*} [CommRing S] [Algebra k S]
    (D : Derivation k S S) {G : Set S} {T : Ideal S} (hGT : Ideal.span G ≤ T)
    (hD : ∀ g ∈ G, D g ∈ T) {x : S} (hx : x ∈ Ideal.span G) : D x ∈ T := by
  induction hx using Submodule.span_induction with
  | mem g hg => exact hD g hg
  | zero => simp
  | add a b _ _ iha ihb => simpa using Submodule.add_mem T iha ihb
  | smul a b hb ihb =>
      have hb' : b ∈ T := hGT hb
      have hD' : D (a • b) = a • D b + b • D a := by
        rw [smul_eq_mul, D.leibniz]
      rw [hD', smul_eq_mul, smul_eq_mul]
      exact Submodule.add_mem T (Ideal.mul_mem_left T a ihb) (Ideal.mul_mem_right (D a) T hb')

def derivIdeal (k : Type*) [CommRing k] {S : Type*} [CommRing S] [Algebra k S]
    (J : Ideal S) : Ideal S :=
  J ⊔ Ideal.span {x : S | ∃ D : Derivation k S S, ∃ y ∈ J, D y = x}

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem derivIdeal_eq_sup_span (k : Type*) [CommRing k] {S : Type*} [CommRing S] [Algebra k S]
    (J : Ideal S) :
    derivIdeal k J = J ⊔ Ideal.span {x : S | ∃ D : Derivation k S S, ∃ y ∈ J, D y = x} := rfl

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem le_derivIdeal (k : Type*) [CommRing k] {S : Type*} [CommRing S] [Algebra k S]
    (J : Ideal S) : J ≤ derivIdeal k J := by
  rw [derivIdeal_eq_sup_span]
  exact le_sup_left

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem derivation_apply_mem_derivIdeal (k : Type*) [CommRing k] {S : Type*} [CommRing S]
    [Algebra k S] (J : Ideal S) (D : Derivation k S S) {x : S} (hx : x ∈ J) :
    D x ∈ derivIdeal k J := by
  rw [derivIdeal_eq_sup_span]
  exact Submodule.mem_sup_right (Ideal.subset_span ⟨D, x, hx, rfl⟩)

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Supply the required witnesses or components. Assume the hypotheses and unpack their components.

Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. A detailed English derivation is pending.
-/
theorem derivIdeal_le_iff (k : Type*) [CommRing k] {S : Type*} [CommRing S] [Algebra k S]
    (J K : Ideal S) :
    derivIdeal k J ≤ K ↔ J ≤ K ∧ ∀ D : Derivation k S S, ∀ x ∈ J, D x ∈ K := by
  rw [derivIdeal_eq_sup_span, sup_le_iff, Ideal.span_le]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun D x hx => h2 ⟨D, x, hx, rfl⟩⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    rintro x ⟨D, y, hy, rfl⟩
    exact h2 D y hy

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Supply the required witnesses or components.
-/
theorem derivIdeal_mono (k : Type*) [CommRing k] {S : Type*} [CommRing S] [Algebra k S] :
    Monotone (derivIdeal k : Ideal S → Ideal S) := by
  intro I J h
  rw [derivIdeal_le_iff]
  exact ⟨h.trans (le_derivIdeal k J), fun D x hx => derivation_apply_mem_derivIdeal k J D (h hx)⟩

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem derivIdeal_le_derivIdeal (k : Type*) [CommRing k] {S : Type*} [CommRing S] [Algebra k S]
    {I J : Ideal S} (h : I ≤ J) : derivIdeal k I ≤ derivIdeal k J :=
  derivIdeal_mono k h

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem derivIdeal_top (k : Type*) [CommRing k] {S : Type*} [CommRing S] [Algebra k S] :
    derivIdeal k (⊤ : Ideal S) = ⊤ :=
  eq_top_iff.mpr (le_derivIdeal k ⊤)

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the indicated hypotheses using the stated equalities. Substitute using the available equality.

Simplify using the standard rewrite rules.
-/
theorem derivIdeal_bot (k : Type*) [CommRing k] {S : Type*} [CommRing S] [Algebra k S] :
    derivIdeal k (⊥ : Ideal S) = ⊥ := by
  refine le_antisymm ?_ bot_le
  rw [derivIdeal_le_iff]
  refine ⟨le_rfl, fun D x hx => ?_⟩
  rw [Ideal.mem_bot] at hx
  subst hx
  simp

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the indicated hypotheses using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result.

Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem derivIdeal_iSup_le (k : Type*) [CommRing k] {S : Type*} [CommRing S] [Algebra k S]
    {ι : Sort*} (J : ι → Ideal S) :
    derivIdeal k (⨆ i, J i) ≤ ⨆ i, derivIdeal k (J i) := by
  have hspan : (⨆ i, J i) = Ideal.span (⋃ i, (J i : Set S)) := Submodule.iSup_eq_span J
  have hle : (⨆ i, J i) ≤ ⨆ i, derivIdeal k (J i) :=
    iSup_le fun i => (le_derivIdeal k (J i)).trans (le_iSup (fun j => derivIdeal k (J j)) i)
  rw [derivIdeal_le_iff]
  refine ⟨hle, ?_⟩
  intro D x hx
  rw [hspan] at hx
  refine derivation_apply_mem_of_mem_span D ?_ ?_ hx
  · rw [← hspan]
    exact hle
  · intro g hg
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hg
    have hi' : g ∈ J i := hi
    exact le_iSup (fun j => derivIdeal k (J j)) i
      (derivation_apply_mem_derivIdeal k (J i) D hi')

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Fix the arbitrary inputs or assume the hypotheses.

Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem derivIdeal_mul_le (k : Type*) [CommRing k] {S : Type*} [CommRing S] [Algebra k S]
    (I J : Ideal S) :
    derivIdeal k (I * J) ≤ I * derivIdeal k J ⊔ J * derivIdeal k I := by
  rw [derivIdeal_le_iff]
  constructor
  · rw [Ideal.mul_le]
    intro r hr s hs
    exact Submodule.mem_sup_left (Ideal.mul_mem_mul hr (le_derivIdeal k J hs))
  · intro D x hx
    refine Submodule.mul_induction_on hx ?_ ?_
    · intro m hm n hn
      simp only [Derivation.leibniz, smul_eq_mul]
      refine Submodule.add_mem _ ?_ ?_
      · exact Submodule.mem_sup_left
          (Ideal.mul_mem_mul hm (derivation_apply_mem_derivIdeal k J D hn))
      · exact Submodule.mem_sup_right
          (Ideal.mul_mem_mul hn (derivation_apply_mem_derivIdeal k I D hm))
    · intro a b ha hb
      rw [map_add]
      exact Submodule.add_mem _ ha hb

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.

Fix the arbitrary inputs or assume the hypotheses. Simplify to obtain the desired conclusion from the available facts. A detailed English derivation is pending.
-/
private theorem derivation_apply_mem_pow_mul_derivIdeal (k : Type*) [CommRing k] {S : Type*} [CommRing S]
    [Algebra k S] (J : Ideal S) (D : Derivation k S S) :
    ∀ n : ℕ, ∀ x ∈ J ^ (n + 1), D x ∈ J ^ n * derivIdeal k J := by
  intro n
  induction n with
  | zero =>
      intro x hx
      have hx' : x ∈ J := by simpa using hx
      have h := derivation_apply_mem_derivIdeal k J D hx'
      simpa using h
  | succ n ih =>
      intro x hx
      rw [pow_succ] at hx
      refine Submodule.mul_induction_on hx ?_ ?_
      · intro a ha b hb
        have hL : D (a * b) = a * D b + b * D a := by
          rw [D.leibniz, smul_eq_mul, smul_eq_mul]
        rw [hL]
        refine Submodule.add_mem _ ?_ ?_
        · exact Ideal.mul_mem_mul ha (derivation_apply_mem_derivIdeal k J D hb)
        · have h2 : b * D a ∈ J * (J ^ n * derivIdeal k J) :=
            Ideal.mul_mem_mul hb (ih a ha)
          have h3 : J * (J ^ n * derivIdeal k J) = J ^ (n + 1) * derivIdeal k J := by
            rw [← mul_assoc, pow_succ, mul_comm J (J ^ n)]
          rwa [h3] at h2
      · intro y z hy hz
        simpa using Submodule.add_mem _ hy hz

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem derivIdeal_pow_succ_le (k : Type*) [CommRing k] {S : Type*} [CommRing S] [Algebra k S]
    (J : Ideal S) (n : ℕ) : derivIdeal k (J ^ (n + 1)) ≤ J ^ n * derivIdeal k J := by
  rw [derivIdeal_le_iff]
  refine ⟨?_, ?_⟩
  · rw [pow_succ]
    exact Ideal.mul_le.mpr fun a ha b hb => Ideal.mul_mem_mul ha (le_derivIdeal k J hb)
  · intro D x hx
    exact derivation_apply_mem_pow_mul_derivIdeal k J D n x hx

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses.

Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
private theorem derivation_apply_mem_pow_of_mem_pow_succ {k : Type*} [CommRing k] {S : Type*}
    [CommRing S] [Algebra k S] (J : Ideal S) (D : Derivation k S S) :
    ∀ n : ℕ, ∀ x ∈ J ^ (n + 1), D x ∈ J ^ n := by
  intro n
  induction n with
  | zero =>
      intro x _
      rw [pow_zero, Ideal.one_eq_top]
      exact Submodule.mem_top
  | succ n ih =>
      intro x hx
      rw [pow_succ] at hx
      refine Submodule.mul_induction_on hx ?_ ?_
      · intro a ha b hb
        simp only [Derivation.leibniz, smul_eq_mul]
        refine Submodule.add_mem _ (Ideal.mul_mem_right _ _ ha) ?_
        have hb' : D a * b ∈ J ^ n * J := Ideal.mul_mem_mul (ih a ha) hb
        rw [← pow_succ] at hb'
        rw [mul_comm b (D a)]
        exact hb'
      · intro a b ha hb
        rw [map_add]
        exact Submodule.add_mem _ ha hb

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Fix the arbitrary inputs or assume the hypotheses. Fix the arbitrary inputs or assume the hypotheses. Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem derivIdeal_pow_succ_le_pow (k : Type*) [CommRing k] {S : Type*} [CommRing S] [Algebra k S]
    (J : Ideal S) (n : ℕ) : derivIdeal k (J ^ (n + 1)) ≤ J ^ n := by
  rw [derivIdeal_le_iff]
  refine ⟨?_, ?_⟩
  · intro x hx
    rw [pow_succ] at hx
    refine Submodule.mul_induction_on hx ?_ ?_
    · intro m hm y _
      exact Ideal.mul_mem_right _ _ hm
    · intro a b ha hb
      exact Submodule.add_mem _ ha hb
  · intro D x hx
    exact derivation_apply_mem_pow_of_mem_pow_succ J D n x hx

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
private theorem pow_succ_le_pow {S : Type*} [CommRing S] (J : Ideal S) (m : ℕ) :
    J ^ (m + 1) ≤ J ^ m := by
  rw [pow_succ]
  exact Ideal.mul_le.mpr fun r hr s _ => Ideal.mul_mem_right s _ hr

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Supply the required witnesses or components.

A detailed English derivation is pending.
-/
theorem derivIdeal_pow_le (k : Type*) [CommRing k] {S : Type*} [CommRing S] [Algebra k S]
    (J : Ideal S) (n : ℕ) : derivIdeal k (J ^ n) ≤ J ^ (n - 1) := by
  obtain _ | m := n
  · have h : (J ^ (0 - 1 : ℕ) : Ideal S) = ⊤ := by simp
    exact le_top.trans h.ge
  · have key : derivIdeal k (J ^ (m + 1)) ≤ J ^ m := by
      rw [derivIdeal_le_iff]
      exact ⟨pow_succ_le_pow J m,
        fun D x hx => derivation_apply_mem_pow_of_mem_pow_succ J D m x hx⟩
    exact key

/- English proof (translation)
Split into cases according to the possible forms of the given data. Treat this case separately. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Treat this case separately.

Establish an intermediate fact. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem derivIdeal_le_pow_of_le_pow (k : Type*) [CommRing k] {S : Type*} [CommRing S] [Algebra k S]
    {I P : Ideal S} {n : ℕ} (h : I ≤ P ^ n) : derivIdeal k I ≤ P ^ (n - 1) := by
  cases n with
  | zero =>
      have hP : P ^ (0 - 1) = (⊤ : Ideal S) := by
        rw [Nat.zero_sub, pow_zero, Ideal.one_eq_top]
      exact le_of_le_of_eq le_top hP.symm
  | succ m =>
      have h2 : derivIdeal k I ≤ P ^ m :=
        (derivIdeal_mono k h).trans (derivIdeal_pow_succ_le_pow k P m)
      have hm : m + 1 - 1 = m := by omega
      exact le_of_le_of_eq h2 (congrArg (fun i => P ^ i) hm.symm)

def derivIdealIterate (k : Type*) [CommRing k] {S : Type*} [CommRing S] [Algebra k S] :
    ℕ → Ideal S → Ideal S
  | 0, J => J
  | r + 1, J => derivIdeal k (derivIdealIterate k r J)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem derivIdealIterate_zero (k : Type*) [CommRing k] {S : Type*} [CommRing S] [Algebra k S]
    (J : Ideal S) : derivIdealIterate k 0 J = J := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem derivIdealIterate_succ (k : Type*) [CommRing k] {S : Type*} [CommRing S] [Algebra k S]
    (r : ℕ) (J : Ideal S) :
    derivIdealIterate k (r + 1) J = derivIdeal k (derivIdealIterate k r J) := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem derivIdealIterate_one (k : Type*) [CommRing k] {S : Type*} [CommRing S] [Algebra k S]
    (J : Ideal S) : derivIdealIterate k 1 J = derivIdeal k J := rfl

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately.
-/
theorem derivIdealIterate_add (k : Type*) [CommRing k] {S : Type*} [CommRing S] [Algebra k S]
    (r s : ℕ) (J : Ideal S) :
    derivIdealIterate k (r + s) J = derivIdealIterate k r (derivIdealIterate k s J) := by
  induction r with
  | zero => rw [Nat.zero_add, derivIdealIterate_zero]
  | succ r ih => rw [Nat.succ_add, derivIdealIterate_succ, derivIdealIterate_succ, ih]

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem le_derivIdealIterate (k : Type*) [CommRing k] {S : Type*} [CommRing S] [Algebra k S]
    (r : ℕ) (J : Ideal S) : J ≤ derivIdealIterate k r J := by
  induction r with
  | zero => exact (derivIdealIterate_zero k J).ge
  | succ r ih =>
      rw [derivIdealIterate_succ]
      exact ih.trans (le_derivIdeal k _)

/- English proof (translation)
Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem derivIdealIterate_le_of_le (k : Type*) [CommRing k] {S : Type*} [CommRing S] [Algebra k S]
    {r r' : ℕ} (h : r ≤ r') (J : Ideal S) :
    derivIdealIterate k r J ≤ derivIdealIterate k r' J := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Nat.add_comm r d, derivIdealIterate_add]
  exact le_derivIdealIterate k d _

/- English proof (translation)
Proceed by induction. Treat this case separately. Rewrite the conclusion using the stated equalities. Treat this case separately. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem derivIdealIterate_le_pow_of_le_pow (k : Type*) [CommRing k] {S : Type*} [CommRing S]
    [Algebra k S] {I P : Ideal S} {n : ℕ} (r : ℕ) (h : I ≤ P ^ n) :
    derivIdealIterate k r I ≤ P ^ (n - r) := by
  induction r with
  | zero =>
      rw [derivIdealIterate_zero, Nat.sub_zero]
      exact h
  | succ r ih =>
      rw [derivIdealIterate_succ]
      have h1 : derivIdeal k (derivIdealIterate k r I) ≤ derivIdeal k (P ^ (n - r)) :=
        derivIdeal_mono k ih
      have h2 : derivIdeal k (P ^ (n - r)) ≤ P ^ (n - r - 1) := derivIdeal_pow_le k P (n - r)
      have h3 : n - r - 1 = n - (r + 1) := by omega
      rw [h3] at h2
      exact h1.trans h2

end FunctorialResolution.EmbeddedResolution
