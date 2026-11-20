import Development.EtaleCohomology.DivisorCycles.CycleCount

open Matrix

namespace LateralTheory.DivDb.ConjugateIdempotents
open LateralTheory.DivDb

variable {C : Type} [Field C] {N n : ℕ}

/- English proof (translation)
Introduce `ht`. Apply `h0` to reduce the goal to its premises. Establish `hi : IsIdempotentElem (Matrix.toLin' P)`. Unfold `IsIdempotentElem`. Rewrite using `[Module.End.mul_eq_comp, ← Matrix.toLin'_mul, hP.eq]`.

Establish `h1` using `LinearMap.IsIdempotentElem.eq_zero_of_trace_eq_zero hi (by`. Rewrite using `[LinearMap.trace_eq_matrix_trace C (Pi.basisFun C (Fin N)), LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin']`. Conclude with `ht)`. Conclude with `Matrix.toLin'.injective (by rw [h1, map_zero])`.
-/
theorem trace_ne_zero [CharZero C] (P : Mat C N) (hP : IsIdempotentElem P) (h0 : P ≠ 0) :
    P.trace ≠ 0 := by
  intro ht
  apply h0
  have hi : IsIdempotentElem (Matrix.toLin' P) := by
    unfold IsIdempotentElem
    rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, hP.eq]
  have h1 := LinearMap.IsIdempotentElem.eq_zero_of_trace_eq_zero hi (by
    rw [LinearMap.trace_eq_matrix_trace C (Pi.basisFun C (Fin N)), LinearMap.toMatrix_eq_toMatrix',
      LinearMap.toMatrix'_toLin']
    exact ht)
  exact Matrix.toLin'.injective (by rw [h1, map_zero])

def Iso (A : Subalgebra C (Mat C N)) (q p : Mat C N) : Prop :=
  ∃ α ∈ A, ∃ β ∈ A, α * β = q ∧ β * α = p ∧ q * α * p = α ∧ p * β * q = β

/- English proof (translation)
Rewrite using `[← h, mul_assoc, hP.eq]`.
-/
theorem right_p {P Q α : Mat C N} (hP : IsIdempotentElem P) (h : Q * α * P = α) : α * P = α := by
  rw [← h, mul_assoc, hP.eq]

/- English proof (translation)
Rewrite using `[← h, ← mul_assoc, ← mul_assoc, hQ.eq]`.
-/
theorem left_q {P Q α : Mat C N} (hQ : IsIdempotentElem Q) (h : Q * α * P = α) : Q * α = α := by
  rw [← h, ← mul_assoc, ← mul_assoc, hQ.eq]

/- English proof (translation)
Take `⟨d, hd⟩` from `hd`. Establish `hαP` using `right_p hP hα`. Establish `e : (α * β) * (α * β) = α * β`. Rewrite using `[mul_assoc, ← mul_assoc β, hβα, ← mul_assoc, hαP]`. Rewrite `e` using `[hd, smul_mul_smul_comm, hQ.eq]`.

Establish `hdd : d * d = d` using `smul_left_injective C hQ0 e`. Establish `hne : d ≠ 0`. Introduce and unpack `rfl`. Apply `hα0` to reduce the goal to its premises. Rewrite `hd` using `[zero_smul]`.

Rewrite using `[← hαP, ← hβα, ← mul_assoc, hd, zero_mul]`. Establish `: d = 1`. Use `mul_left_cancel₀ hne (hdd.trans (mul_one d).symm)` as an intermediate fact. Conclude with `this`. Rewrite using `[hd, this, one_smul]`.
-/
theorem fin_step {P Q α β : Mat C N} (hP : IsIdempotentElem P) (hQ : IsIdempotentElem Q) (hQ0 : Q ≠ 0)
    (hα : Q * α * P = α) (hβα : β * α = P) (hd : ∃ d : C, α * β = d • Q) (hα0 : α ≠ 0) :
    α * β = Q := by
  obtain ⟨d, hd⟩ := hd
  have hαP := right_p hP hα
  have e : (α * β) * (α * β) = α * β := by
    rw [mul_assoc, ← mul_assoc β, hβα, ← mul_assoc, hαP]
  rw [hd, smul_mul_smul_comm, hQ.eq] at e
  have hdd : d * d = d := smul_left_injective C hQ0 e
  have hne : d ≠ 0 := by
    rintro rfl
    apply hα0
    rw [zero_smul] at hd
    rw [← hαP, ← hβα, ← mul_assoc, hd, zero_mul]
  have : d = 1 := by
    have := mul_left_cancel₀ hne (hdd.trans (mul_one d).symm)
    exact this
  rw [hd, this, one_smul]

/- English proof (translation)
Establish `hpi` using `hp.1.idem k`. Establish `hqi` using `hq.1.idem j`. Establish `hαA : q j * a * p k ∈ A` using `A.mul_mem (A.mul_mem (hqc.1 j) ha) (hpc.1 k)`. Establish `hα : q j * (q j * a * p k) * p k = q j * a * p k`. Simplify using `only [← mul_assoc, hqi.eq]`.

Rewrite using `[mul_assoc _ (p k), hpi.eq]`. Choose the witnesses or unpack the hypotheses as in `⟨a', ha', h'⟩ : ∃ a' ∈ A, p k * a' * (q j * a * p k) ≠ 0 := by`. Assume the negation of the conclusion as `hc`. Use `push Not at hc`. Apply `h` to reduce the goal to its premises.

Apply `hA _ hαA` to reduce the goal to its premises. Introduce `b hb`. Use `⟨2, ?_⟩` and prove the remaining obligations. Rewrite using `[pow_two]`. Establish `: b * (q j * a * p k) * (b * (q j * a * p k)) = b * q j * a * (p k * b * (q j * a * p k))`.

Simplify using `only [mul_assoc]`. Rewrite using `[this, hc b hb, mul_zero]`. Take `⟨c, hc⟩` from `hpc.2 (a' * q j * a) (A.mul_mem (A.mul_mem ha' (hqc.1 j)) ha) k`. Establish `hpa : p k * a' * (q j * a * p k) = c • p k`. Rewrite using `[← hc]`.

Simplify using `only [mul_assoc]`. Establish `hc0 : c ≠ 0` using `by rintro rfl; rw [zero_smul] at hpa; exact h' hpa`. Use `set α := q j * a * p k with hαdef`. Use `set β := c⁻¹ • (p k * a' * q j) with hβdef`. Establish `hβA : β ∈ A` using `A.smul_mem (A.mul_mem (A.mul_mem (hpc.1 k) ha') (hqc.1 j)) _`.

Establish `hβ : p k * β * q j = β`. Simplify using `only [hβdef, mul_smul_comm, smul_mul_assoc, ← mul_assoc, hpi.eq]`. Rewrite using `[mul_assoc _ (q j), hqi.eq]`. Establish `hβα : β * α = p k`. Establish `: β * α = c⁻¹ • (p k * a' * α)`.

Simplify using `only [hβdef, smul_mul_assoc, hαdef, mul_assoc, ← mul_assoc (q j) (q j), hqi.eq]`. Rewrite using `[this, hpa, smul_smul, inv_mul_cancel₀ hc0, one_smul]`. Use `⟨α, hαA, β, hβA, ?_, hβα, hα, hβ⟩` and prove the remaining obligations. Use `fin_step hpi hqi (hq.2 j) hα hβα ?_ h` and prove the remaining obligations. Take `⟨d, hd⟩` from `hqc.2 (α * β) (A.mul_mem hαA hβA) j`.

Use `⟨d, ?_⟩` and prove the remaining obligations. Rewrite using `[← hd]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem key (A : Subalgebra C (Mat C N)) (p q : Fin n → Mat C N) (hp : Sys p) (hpc : Corner A p)
    (hq : Sys q) (hqc : Corner A q) (hA : NoNil A) (j k : Fin n) (a : Mat C N) (ha : a ∈ A)
    (h : q j * a * p k ≠ 0) : Iso A (q j) (p k) := by
  have hpi := hp.1.idem k
  have hqi := hq.1.idem j
  have hαA : q j * a * p k ∈ A := A.mul_mem (A.mul_mem (hqc.1 j) ha) (hpc.1 k)
  have hα : q j * (q j * a * p k) * p k = q j * a * p k := by
    simp only [← mul_assoc, hqi.eq]; rw [mul_assoc _ (p k), hpi.eq]
  obtain ⟨a', ha', h'⟩ : ∃ a' ∈ A, p k * a' * (q j * a * p k) ≠ 0 := by
    by_contra hc
    push Not at hc
    apply h
    apply hA _ hαA
    intro b hb
    refine ⟨2, ?_⟩
    rw [pow_two]
    have : b * (q j * a * p k) * (b * (q j * a * p k)) = b * q j * a * (p k * b * (q j * a * p k)) := by
      simp only [mul_assoc]
    rw [this, hc b hb, mul_zero]
  obtain ⟨c, hc⟩ := hpc.2 (a' * q j * a) (A.mul_mem (A.mul_mem ha' (hqc.1 j)) ha) k
  have hpa : p k * a' * (q j * a * p k) = c • p k := by
    rw [← hc]; simp only [mul_assoc]
  have hc0 : c ≠ 0 := by rintro rfl; rw [zero_smul] at hpa; exact h' hpa
  set α := q j * a * p k with hαdef
  set β := c⁻¹ • (p k * a' * q j) with hβdef
  have hβA : β ∈ A := A.smul_mem (A.mul_mem (A.mul_mem (hpc.1 k) ha') (hqc.1 j)) _
  have hβ : p k * β * q j = β := by
    simp only [hβdef, mul_smul_comm, smul_mul_assoc, ← mul_assoc, hpi.eq]
    rw [mul_assoc _ (q j), hqi.eq]
  have hβα : β * α = p k := by
    have : β * α = c⁻¹ • (p k * a' * α) := by
      simp only [hβdef, smul_mul_assoc, hαdef, mul_assoc, ← mul_assoc (q j) (q j), hqi.eq]
    rw [this, hpa, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  refine ⟨α, hαA, β, hβA, ?_, hβα, hα, hβ⟩
  refine fin_step hpi hqi (hq.2 j) hα hβα ?_ h
  obtain ⟨d, hd⟩ := hqc.2 (α * β) (A.mul_mem hαA hβA) j
  refine ⟨d, ?_⟩
  rw [← hd]
  calc α * β = (q j * α) * (β * q j) := by rw [left_q hqi hα, right_p hqi hβ]
    _ = _ := by simp only [mul_assoc]

/- English proof (translation)
Take `⟨α1, hα1, β1, hβ1, e1, f1, g1, k1⟩` from `h1`. Take `⟨α2, hα2, β2, hβ2, e2, f2, g2, k2⟩` from `h2`. Take `⟨α3, hα3, β3, hβ3, e3, f3, g3, k3⟩` from `h3`. Establish `a3p` using `right_p (hp.1.idem k) g3`. Establish `qa1` using `left_q (hq.1.idem j) g1`.

Establish `qa2` using `left_q (hq.1.idem j) g2`. Establish `pb1` using `left_q (hp.1.idem k) k1`. Establish `b2q` using `right_p (hq.1.idem j) k2`. Establish `pb3` using `left_q (hp.1.idem k) k3`. Establish `qa3` using `left_q (hq.1.idem j') g3`.

Establish `a2p` using `right_p (hp.1.idem k') g2`. Establish `pb2` using `left_q (hp.1.idem k') k2`. Establish `b3q` using `right_p (hq.1.idem j') k3`. Use `⟨α3 * β1 * α2, A.mul_mem (A.mul_mem hα3 hβ1) hα2, β2 * α1 * β3, A.mul_mem (A.mul_mem hβ2 hα1) hβ3, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Simplify using `only [mul_assoc]`.

Rewrite using `[← mul_assoc α2 β2, e2, ← mul_assoc (q j) α1, qa1, ← mul_assoc β1 α1, f1, ← mul_assoc, a3p, e3]`. Simplify using `only [mul_assoc]`. Rewrite using `[← mul_assoc β3 α3, f3, ← mul_assoc (p k) β1, pb1, ← mul_assoc α1 β1, e1, qa2, f2]`. Rewrite using `[← mul_assoc, ← mul_assoc, qa3, mul_assoc, a2p]`. Rewrite using `[← mul_assoc, ← mul_assoc, pb2, mul_assoc, b3q]`.
-/
theorem compose {A : Subalgebra C (Mat C N)} {p q : Fin n → Mat C N} (hp : Sys p) (hq : Sys q)
    {j j' k k' : Fin n} (h1 : Iso A (q j) (p k)) (h2 : Iso A (q j) (p k')) (h3 : Iso A (q j') (p k)) :
    Iso A (q j') (p k') := by
  obtain ⟨α1, hα1, β1, hβ1, e1, f1, g1, k1⟩ := h1
  obtain ⟨α2, hα2, β2, hβ2, e2, f2, g2, k2⟩ := h2
  obtain ⟨α3, hα3, β3, hβ3, e3, f3, g3, k3⟩ := h3
  have a3p := right_p (hp.1.idem k) g3
  have qa1 := left_q (hq.1.idem j) g1
  have qa2 := left_q (hq.1.idem j) g2
  have pb1 := left_q (hp.1.idem k) k1
  have b2q := right_p (hq.1.idem j) k2
  have pb3 := left_q (hp.1.idem k) k3
  have qa3 := left_q (hq.1.idem j') g3
  have a2p := right_p (hp.1.idem k') g2
  have pb2 := left_q (hp.1.idem k') k2
  have b3q := right_p (hq.1.idem j') k3
  refine ⟨α3 * β1 * α2, A.mul_mem (A.mul_mem hα3 hβ1) hα2, β2 * α1 * β3,
    A.mul_mem (A.mul_mem hβ2 hα1) hβ3, ?_, ?_, ?_, ?_⟩
  · simp only [mul_assoc]
    rw [← mul_assoc α2 β2, e2, ← mul_assoc (q j) α1, qa1, ← mul_assoc β1 α1, f1, ← mul_assoc, a3p, e3]
  · simp only [mul_assoc]
    rw [← mul_assoc β3 α3, f3, ← mul_assoc (p k) β1, pb1, ← mul_assoc α1 β1, e1, qa2, f2]
  · rw [← mul_assoc, ← mul_assoc, qa3, mul_assoc, a2p]
  · rw [← mul_assoc, ← mul_assoc, pb2, mul_assoc, b3q]

/- English proof (translation)
Establish `htr : ∀ j k, Iso A (q j) (p k) → (q j).trace = (p k).trace`. Introduce and unpack `j k ⟨α, -, β, -, e, f, -, -⟩`. Rewrite using `[← e, ← f, Matrix.trace_mul_comm]`. Establish `hsum : ∑ k ∈ Finset.univ.filter (fun k => Q k = Q k0), p k = ∑ j ∈ Q k0, q j`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[← Finset.sum_mul, hq.1.complete, one_mul]`. Use `_ = ∑ j, if j ∈ Q k0 then q j else 0 := by`. Use `Finset.sum_congr rfl (fun j _ => ?_)` and prove the remaining obligations. Use `split_ifs with hj`. Rewrite using `[Finset.mul_sum, Finset.sum_subset (Finset.subset_univ _), ← Finset.mul_sum, hp.1.complete, mul_one]`.

Introduce `k _ hk`. Apply `hF1` to reduce the goal to its premises. Introduce `hR`. Apply `hk` to reduce the goal to its premises. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and]`.

Conclude with `hQ j k k0 ((hQd j k).2 hR) hj`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_eq_zero (fun k hk => hF1 j k ?_)` and prove the remaining obligations. Introduce `hR`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at hk`.

Apply `hj` to reduce the goal to its premises. Rewrite using `[← hk]`. Conclude with `(hQd j k).2 hR`. Use `_ = ∑ j ∈ Q k0, q j := by rw [Finset.sum_ite_mem, Finset.univ_inter]`. Establish `ht` using `congrArg Matrix.trace hsum`.

Rewrite `ht` using `[Matrix.trace_sum, Matrix.trace_sum]`. Take `⟨j0, hj0⟩` from `hne k0`. Establish `h1 : ∀ k ∈ Finset.univ.filter (fun k => Q k = Q k0), (p k).trace = (p k0).trace`. Introduce `k hk`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at hk`.

Establish `: j0 ∈ Q k` using `by rw [hk]; exact hj0`. Rewrite using `[← htr j0 k ((hQd j0 k).1 this), htr j0 k0 ((hQd j0 k0).1 hj0)]`. Establish `h2 : ∀ j ∈ Q k0, (q j).trace = (p k0).trace` using `fun j hj => htr j k0 ((hQd j k0).1 hj)`. Rewrite `ht` using `[Finset.sum_congr rfl h1, Finset.sum_congr rfl h2, Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]`. Establish `t0` using `trace_ne_zero (p k0) (hp.1.idem k0) (hp.2 k0)`.

Conclude with `mul_right_cancel₀ t0 ht` after adjusting the coercions.
-/
theorem count (A : Subalgebra C (Mat C N)) [CharZero C] (p q : Fin n → Mat C N) (hp : Sys p) (hq : Sys q)
    (Q : Fin n → Finset (Fin n)) (hQd : ∀ j k, j ∈ Q k ↔ Iso A (q j) (p k))
    (hF1 : ∀ j k, ¬ Iso A (q j) (p k) → q j * p k = 0)
    (hQ : ∀ j k k', j ∈ Q k → j ∈ Q k' → Q k = Q k') (hne : ∀ k, (Q k).Nonempty) (k0 : Fin n) :
    (Finset.univ.filter (fun k => Q k = Q k0)).card = (Q k0).card := by
  classical
  have htr : ∀ j k, Iso A (q j) (p k) → (q j).trace = (p k).trace := by
    rintro j k ⟨α, -, β, -, e, f, -, -⟩
    rw [← e, ← f, Matrix.trace_mul_comm]
  have hsum : ∑ k ∈ Finset.univ.filter (fun k => Q k = Q k0), p k = ∑ j ∈ Q k0, q j := by
    calc ∑ k ∈ Finset.univ.filter (fun k => Q k = Q k0), p k
        = ∑ j, q j * ∑ k ∈ Finset.univ.filter (fun k => Q k = Q k0), p k := by
          rw [← Finset.sum_mul, hq.1.complete, one_mul]
      _ = ∑ j, if j ∈ Q k0 then q j else 0 := by
          refine Finset.sum_congr rfl (fun j _ => ?_)
          split_ifs with hj
          · rw [Finset.mul_sum, Finset.sum_subset (Finset.subset_univ _), ← Finset.mul_sum,
              hp.1.complete, mul_one]
            intro k _ hk
            apply hF1
            intro hR
            apply hk
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            exact hQ j k k0 ((hQd j k).2 hR) hj
          · rw [Finset.mul_sum]
            refine Finset.sum_eq_zero (fun k hk => hF1 j k ?_)
            intro hR
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
            apply hj
            rw [← hk]
            exact (hQd j k).2 hR
      _ = ∑ j ∈ Q k0, q j := by rw [Finset.sum_ite_mem, Finset.univ_inter]
  have ht := congrArg Matrix.trace hsum
  rw [Matrix.trace_sum, Matrix.trace_sum] at ht
  obtain ⟨j0, hj0⟩ := hne k0
  have h1 : ∀ k ∈ Finset.univ.filter (fun k => Q k = Q k0), (p k).trace = (p k0).trace := by
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
    have : j0 ∈ Q k := by rw [hk]; exact hj0
    rw [← htr j0 k ((hQd j0 k).1 this), htr j0 k0 ((hQd j0 k0).1 hj0)]
  have h2 : ∀ j ∈ Q k0, (q j).trace = (p k0).trace := fun j hj => htr j k0 ((hQd j k0).1 hj)
  rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2, Finset.sum_const, Finset.sum_const,
    nsmul_eq_mul, nsmul_eq_mul] at ht
  have t0 := trace_ne_zero (p k0) (hp.1.idem k0) (hp.2 k0)
  exact_mod_cast mul_right_cancel₀ t0 ht

/- English proof (translation)
Introduce `C _ _ N n A p q hp hpc hq hqc hA`. Take `⟨Q, hQd⟩ : ∃ Q : Fin n → Finset (Fin n), ∀ j k, j ∈ Q k ↔ Iso A (q j) (p k)` from `⟨fun k => Finset.univ.filter (fun j => Iso A (q j) (p k)), by simp⟩`. Establish `hF1 : ∀ j k, ¬ Iso A (q j) (p k) → q j * p k = 0` using `fun j k h => by`. Assume the negation of the conclusion as `h'`. Conclude with `h (key A p q hp hpc hq hqc hA j k 1 A.one_mem (by rwa [mul_one]))`.

Establish `hQ : ∀ j k k', j ∈ Q k → j ∈ Q k' → Q k = Q k'`. Introduce `j k k' h1 h2`. Rewrite `h1`, `h2` using `[hQd]`. Use extensionality with `j'`. Rewrite using `[hQd, hQd]`.

Conclude with `⟨fun h3 => compose hp hq h1 h2 h3, fun h3 => compose hp hq h2 h1 h3⟩`. Establish `hne : ∀ k, (Q k).Nonempty`. Introduce `k`. Assume the negation of the conclusion as `h`. Rewrite `h` using `[Finset.not_nonempty_iff_eq_empty]`.

Apply `hp.2 k` to reduce the goal to its premises. Rewrite using `[← one_mul (p k), ← hq.1.complete, Finset.sum_mul]`. Use `Finset.sum_eq_zero (fun j _ => hF1 j k (fun hR => ?_))` and prove the remaining obligations. Use `(hQd j k).2 hR` as an intermediate fact. Rewrite `this` using `[h]`.

Conclude with `Finset.notMem_empty _ this`. Establish `hcard` using `count A p q hp hq Q hQd hF1 hQ hne`. Take `⟨L, hL⟩ : ∃ L : Finset (Fin n) → Finset (Fin n), ∀ S k, k ∈ L S ↔ Q k = S ∧ k ∉ S` from `⟨fun S => Finset.univ.filter (fun k => Q k = S ∧ k ∉ S), by simp⟩`. Take `⟨M, hM⟩ : ∃ M : Finset (Fin n) → Finset (Fin n), ∀ S j, j ∈ M S ↔ j ∈ S ∧ Q j ≠ S` from `⟨fun S => Finset.univ.filter (fun j => j ∈ S ∧ Q j ≠ S), by simp⟩`. Establish `hLM : ∀ k0, (L (Q k0)).card = (M (Q k0)).card`.

Introduce `k0`. Establish `e1` using `Finset.card_filter_add_card_filter_not (s := Finset.univ.filter (fun k => Q k = Q k0)) (fun k => k ∈ Q k0)`. Establish `e2` using `Finset.card_filter_add_card_filter_not (s := Q k0) (fun j => Q j = Q k0)`. Rewrite `e1` using `[hcard k0]`. Establish `e3 : (Finset.univ.filter (fun k => Q k = Q k0)).filter (fun k => k ∈ Q k0) = (Q k0).filter (fun j => Q j = Q k0)`.

Use extensionality with `x`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and]`. The claim follows by propositional logic. Establish `e4 : (Finset.univ.filter (fun k => Q k = Q k0)).filter (fun k => ¬ k ∈ Q k0) = L (Q k0)`. Use extensionality with `x`.

Simplify using `only [hL, Finset.mem_filter, Finset.mem_univ, true_and]`. Establish `e5 : (Q k0).filter (fun j => ¬ Q j = Q k0) = M (Q k0)`. Use extensionality with `x`. Simplify using `only [hM, Finset.mem_filter]`. Rewrite `e1` using `[e3, e4]`.

Rewrite `e2` using `[e5]`. Use linear arithmetic over natural numbers and integers. Set `g : Finset (Fin n) → Fin n → Fin n` to `fun S k => if h : (L S).card = (M S).card ∧ k ∈ L S then ((L S).equivOfCardEq h.1 ⟨k, h.2⟩ : Fin n) else k`. Establish `hg : ∀ S k (h : (L S).card = (M S).card ∧ k ∈ L S), g S k = ((L S).equivOfCardEq h.1 ⟨k, h.2⟩ : Fin n)` using `fun S k h => by`. Simplify using `only [g, dif_pos h]`.

Set `f : Fin n → Fin n` to `fun k => if k ∈ Q k then k else g (Q k) k`. Establish `hkL : ∀ k, k ∉ Q k → (L (Q k)).card = (M (Q k)).card ∧ k ∈ L (Q k)` using `fun k hk => ⟨hLM k, (hL _ _).2 ⟨rfl, hk⟩⟩`. Establish `hfM : ∀ k, k ∉ Q k → f k ∈ Q k ∧ Q (f k) ≠ Q k`. Introduce `k hk`. Establish `e : f k = g (Q k) k` using `by simp only [f, if_neg hk]`.

Rewrite using `[e, hg _ _ (hkL k hk), ← hM]`. Conclude with `((L (Q k)).equivOfCardEq (hkL k hk).1 ⟨k, (hkL k hk).2⟩).2`. Establish `hfQ : ∀ k, f k ∈ Q k`. Introduce `k`. Distinguish the cases in `hk : k ∈ Q k`.

Simplify using `only [f, if_pos hk]`. Conclude with `hk`. Conclude with `(hfM k hk).1`. Establish `hfix : ∀ k, k ∈ Q k → f k = k` using `fun k hk => by simp only [f, if_pos hk]`. Establish `hinj : Function.Injective f`.

Introduce `k k' hkk`. Apply the tactic sequence `by_cases hk : k ∈ Q k <;> by_cases hk' : k' ∈ Q k'`. Rewrite `hkk` using `[hfix k hk, hfix k' hk']`. Then use the resulting hypothesis. It suffices to derive a contradiction. Establish `hm` using `hfM k' hk'`.

Rewrite `hm` using `[← hkk, hfix k hk]`. Conclude with `hm.2 (hQ k k k' hk hm.1)`. It suffices to derive a contradiction. Establish `hm` using `hfM k hk`. Rewrite `hm` using `[hkk, hfix k' hk']`.

Conclude with `hm.2 (hQ k' k' k hk' hm.1)`. Establish `hQQ : Q k = Q k'` using `hQ (f k) k k' (hfQ k) (by rw [hkk]; exact hfQ k')`. Establish `e1 : f k = g (Q k) k` using `by simp only [f, if_neg hk]`. Establish `e2 : f k' = g (Q k) k'` using `by simp only [f, if_neg hk']; rw [hQQ]`. Establish `hk'L : (L (Q k)).card = (M (Q k)).card ∧ k' ∈ L (Q k)` using `⟨hLM k, (hL _ _).2 ⟨hQQ.symm, by rw [hQQ]; exact hk'⟩⟩`.

Rewrite `hkk` using `[e1, e2, hg _ _ (hkL k hk), hg _ _ hk'L]`. Use `((L (Q k)).equivOfCardEq (hkL k hk).1).injective (Subtype.ext hkk)` as an intermediate fact. Conclude with `congrArg Subtype.val this`. Set `π` to `Equiv.ofBijective f (Finite.injective_iff_bijective.mp hinj)`. Establish `hR : ∀ j, Iso A (q (f j)) (p j)` using `fun j => (hQd _ _).1 (hfQ j)`.

Unfold `Iso at hR`. Use `choose α hαA β hβA hab hba hqa hpb using hR`. Establish `hαp : ∀ j, α j * p j = α j` using `fun j => right_p (hp.1.idem j) (hqa j)`. Establish `hqα : ∀ j, q (f j) * α j = α j` using `fun j => left_q (hq.1.idem _) (hqa j)`. Establish `hpβ : ∀ j, p j * β j = β j` using `fun j => left_q (hp.1.idem j) (hpb j)`.

Establish `hβq : ∀ j, β j * q (f j) = β j` using `fun j => right_p (hq.1.idem _) (hpb j)`. Establish `hvw : (∑ j, α j) * ∑ j, β j = 1`. Rewrite using `[Finset.sum_mul_sum]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.sum_eq_single i]`.

Conclude with `hab i`. Introduce `j _ hji`. Rewrite using `[← hαp i, ← hpβ j, mul_assoc, ← mul_assoc (p i), hp.1.ortho (Ne.symm hji), zero_mul, mul_zero]`. Use the proof step `simp)`. Use `_ = ∑ i, q i := Equiv.sum_comp π q`.

Use `_ = 1 := hq.1.complete`. Establish `hwv : (∑ j, β j) * ∑ j, α j = 1`. Rewrite using `[Finset.sum_mul_sum]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.sum_eq_single i]`.

Conclude with `hba i`. Introduce `j _ hji`. Rewrite using `[← hβq i, ← hqα j, mul_assoc, ← mul_assoc (q (f i)), hq.1.ortho (hinj.ne (Ne.symm hji)), zero_mul, mul_zero]`. Use the proof step `simp)`. Use `_ = 1 := hp.1.complete`.

Use `⟨∑ j, α j, A.sum_mem (fun j _ => hαA j), ⟨⟨_, _, hvw, hwv⟩, rfl⟩, π, ?_, ?_⟩` and prove the remaining obligations. Introduce `j`. Establish `h1 : (∑ k, α k) * p j = α j`. Rewrite using `[Finset.sum_mul, Finset.sum_eq_single j]`. Conclude with `hαp j`.

Introduce `k _ hkj`. Rewrite using `[← hαp k, mul_assoc, hp.1.ortho hkj, mul_zero]`. Simplify using the standard rewrite rules. Establish `h2 : q (f j) * ∑ k, α k = α j`. Rewrite using `[Finset.mul_sum, Finset.sum_eq_single j]`.

Conclude with `hqα j`. Introduce `k _ hkj`. Rewrite using `[← hqα k, ← mul_assoc, hq.1.ortho (hinj.ne (Ne.symm hkj)), zero_mul]`. Simplify using the standard rewrite rules. Use `show (∑ k, α k) * p j = q (f j) * ∑ k, α k`.

Rewrite using `[h1, h2]`. Introduce and unpack `i ⟨a, ha, h⟩ show f i = i`. Conclude with `hfix i ((hQd i i).2 (key A p q hp hpc hq hqc hA i i a ha h))`.
-/
theorem IdemConj_of : IdemConj := by
  intro C _ _ N n A p q hp hpc hq hqc hA
  classical
  obtain ⟨Q, hQd⟩ : ∃ Q : Fin n → Finset (Fin n), ∀ j k, j ∈ Q k ↔ Iso A (q j) (p k) :=
    ⟨fun k => Finset.univ.filter (fun j => Iso A (q j) (p k)), by simp⟩
  have hF1 : ∀ j k, ¬ Iso A (q j) (p k) → q j * p k = 0 := fun j k h => by
    by_contra h'
    exact h (key A p q hp hpc hq hqc hA j k 1 A.one_mem (by rwa [mul_one]))
  have hQ : ∀ j k k', j ∈ Q k → j ∈ Q k' → Q k = Q k' := by
    intro j k k' h1 h2
    rw [hQd] at h1 h2
    ext j'
    rw [hQd, hQd]
    exact ⟨fun h3 => compose hp hq h1 h2 h3, fun h3 => compose hp hq h2 h1 h3⟩
  have hne : ∀ k, (Q k).Nonempty := by
    intro k
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    apply hp.2 k
    rw [← one_mul (p k), ← hq.1.complete, Finset.sum_mul]
    refine Finset.sum_eq_zero (fun j _ => hF1 j k (fun hR => ?_))
    have := (hQd j k).2 hR
    rw [h] at this
    exact Finset.notMem_empty _ this
  have hcard := count A p q hp hq Q hQd hF1 hQ hne
  obtain ⟨L, hL⟩ : ∃ L : Finset (Fin n) → Finset (Fin n), ∀ S k, k ∈ L S ↔ Q k = S ∧ k ∉ S :=
    ⟨fun S => Finset.univ.filter (fun k => Q k = S ∧ k ∉ S), by simp⟩
  obtain ⟨M, hM⟩ : ∃ M : Finset (Fin n) → Finset (Fin n), ∀ S j, j ∈ M S ↔ j ∈ S ∧ Q j ≠ S :=
    ⟨fun S => Finset.univ.filter (fun j => j ∈ S ∧ Q j ≠ S), by simp⟩
  have hLM : ∀ k0, (L (Q k0)).card = (M (Q k0)).card := by
    intro k0
    have e1 := Finset.card_filter_add_card_filter_not
      (s := Finset.univ.filter (fun k => Q k = Q k0)) (fun k => k ∈ Q k0)
    have e2 := Finset.card_filter_add_card_filter_not (s := Q k0) (fun j => Q j = Q k0)
    rw [hcard k0] at e1
    have e3 : (Finset.univ.filter (fun k => Q k = Q k0)).filter (fun k => k ∈ Q k0) =
        (Q k0).filter (fun j => Q j = Q k0) := by
      ext x; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; tauto
    have e4 : (Finset.univ.filter (fun k => Q k = Q k0)).filter (fun k => ¬ k ∈ Q k0) = L (Q k0) := by
      ext x; simp only [hL, Finset.mem_filter, Finset.mem_univ, true_and]
    have e5 : (Q k0).filter (fun j => ¬ Q j = Q k0) = M (Q k0) := by
      ext x; simp only [hM, Finset.mem_filter]
    rw [e3, e4] at e1
    rw [e5] at e2
    omega
  let g : Finset (Fin n) → Fin n → Fin n := fun S k =>
    if h : (L S).card = (M S).card ∧ k ∈ L S then ((L S).equivOfCardEq h.1 ⟨k, h.2⟩ : Fin n) else k
  have hg : ∀ S k (h : (L S).card = (M S).card ∧ k ∈ L S),
      g S k = ((L S).equivOfCardEq h.1 ⟨k, h.2⟩ : Fin n) := fun S k h => by
    simp only [g, dif_pos h]
  let f : Fin n → Fin n := fun k => if k ∈ Q k then k else g (Q k) k
  have hkL : ∀ k, k ∉ Q k → (L (Q k)).card = (M (Q k)).card ∧ k ∈ L (Q k) :=
    fun k hk => ⟨hLM k, (hL _ _).2 ⟨rfl, hk⟩⟩
  have hfM : ∀ k, k ∉ Q k → f k ∈ Q k ∧ Q (f k) ≠ Q k := by
    intro k hk
    have e : f k = g (Q k) k := by simp only [f, if_neg hk]
    rw [e, hg _ _ (hkL k hk), ← hM]
    exact ((L (Q k)).equivOfCardEq (hkL k hk).1 ⟨k, (hkL k hk).2⟩).2
  have hfQ : ∀ k, f k ∈ Q k := by
    intro k
    by_cases hk : k ∈ Q k
    · simp only [f, if_pos hk]; exact hk
    · exact (hfM k hk).1
  have hfix : ∀ k, k ∈ Q k → f k = k := fun k hk => by simp only [f, if_pos hk]
  have hinj : Function.Injective f := by
    intro k k' hkk
    by_cases hk : k ∈ Q k <;> by_cases hk' : k' ∈ Q k'
    · rwa [hfix k hk, hfix k' hk'] at hkk
    · exfalso
      have hm := hfM k' hk'
      rw [← hkk, hfix k hk] at hm
      exact hm.2 (hQ k k k' hk hm.1)
    · exfalso
      have hm := hfM k hk
      rw [hkk, hfix k' hk'] at hm
      exact hm.2 (hQ k' k' k hk' hm.1)
    · have hQQ : Q k = Q k' := hQ (f k) k k' (hfQ k) (by rw [hkk]; exact hfQ k')
      have e1 : f k = g (Q k) k := by simp only [f, if_neg hk]
      have e2 : f k' = g (Q k) k' := by simp only [f, if_neg hk']; rw [hQQ]
      have hk'L : (L (Q k)).card = (M (Q k)).card ∧ k' ∈ L (Q k) :=
        ⟨hLM k, (hL _ _).2 ⟨hQQ.symm, by rw [hQQ]; exact hk'⟩⟩
      rw [e1, e2, hg _ _ (hkL k hk), hg _ _ hk'L] at hkk
      have := ((L (Q k)).equivOfCardEq (hkL k hk).1).injective (Subtype.ext hkk)
      exact congrArg Subtype.val this
  let π := Equiv.ofBijective f (Finite.injective_iff_bijective.mp hinj)
  have hR : ∀ j, Iso A (q (f j)) (p j) := fun j => (hQd _ _).1 (hfQ j)
  unfold Iso at hR
  choose α hαA β hβA hab hba hqa hpb using hR
  have hαp : ∀ j, α j * p j = α j := fun j => right_p (hp.1.idem j) (hqa j)
  have hqα : ∀ j, q (f j) * α j = α j := fun j => left_q (hq.1.idem _) (hqa j)
  have hpβ : ∀ j, p j * β j = β j := fun j => left_q (hp.1.idem j) (hpb j)
  have hβq : ∀ j, β j * q (f j) = β j := fun j => right_p (hq.1.idem _) (hpb j)
  have hvw : (∑ j, α j) * ∑ j, β j = 1 := by
    rw [Finset.sum_mul_sum]
    calc ∑ i, ∑ j, α i * β j = ∑ i, q (π i) := Finset.sum_congr rfl (fun i _ => by
            rw [Finset.sum_eq_single i]
            · exact hab i
            · intro j _ hji
              rw [← hαp i, ← hpβ j, mul_assoc, ← mul_assoc (p i), hp.1.ortho (Ne.symm hji), zero_mul,
                mul_zero]
            · simp)
      _ = ∑ i, q i := Equiv.sum_comp π q
      _ = 1 := hq.1.complete
  have hwv : (∑ j, β j) * ∑ j, α j = 1 := by
    rw [Finset.sum_mul_sum]
    calc ∑ i, ∑ j, β i * α j = ∑ i, p i := Finset.sum_congr rfl (fun i _ => by
            rw [Finset.sum_eq_single i]
            · exact hba i
            · intro j _ hji
              rw [← hβq i, ← hqα j, mul_assoc, ← mul_assoc (q (f i)),
                hq.1.ortho (hinj.ne (Ne.symm hji)), zero_mul, mul_zero]
            · simp)
      _ = 1 := hp.1.complete
  refine ⟨∑ j, α j, A.sum_mem (fun j _ => hαA j), ⟨⟨_, _, hvw, hwv⟩, rfl⟩, π, ?_, ?_⟩
  · intro j
    have h1 : (∑ k, α k) * p j = α j := by
      rw [Finset.sum_mul, Finset.sum_eq_single j]
      · exact hαp j
      · intro k _ hkj
        rw [← hαp k, mul_assoc, hp.1.ortho hkj, mul_zero]
      · simp
    have h2 : q (f j) * ∑ k, α k = α j := by
      rw [Finset.mul_sum, Finset.sum_eq_single j]
      · exact hqα j
      · intro k _ hkj
        rw [← hqα k, ← mul_assoc, hq.1.ortho (hinj.ne (Ne.symm hkj)), zero_mul]
      · simp
    show (∑ k, α k) * p j = q (f j) * ∑ k, α k
    rw [h1, h2]
  · rintro i ⟨a, ha, h⟩
    show f i = i
    exact hfix i ((hQd i i).2 (key A p q hp hpc hq hqc hA i i a ha h))

end LateralTheory.DivDb.ConjugateIdempotents
