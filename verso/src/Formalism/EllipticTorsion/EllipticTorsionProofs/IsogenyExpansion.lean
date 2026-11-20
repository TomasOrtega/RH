import Formalism.EllipticTorsion.IsoExpand

open Finset

namespace Formalism.ELL.QuadraticDifferenceHypotheses

universe u

section Exact
variable {O M Q : Type u} [CommRing O] [AddCommGroup M] [Module O M] [AddCommGroup Q]

structure BiHyp (bar : O → O) (ψ : M → Q) : Prop where
  add1 : ∀ a a' b : M, quadDiff ψ (a + a') b = quadDiff ψ a b + quadDiff ψ a' b
  zero : ψ 0 = 0
  adj : ∀ (α : O) (a b : M), quadDiff ψ (α • a) b = quadDiff ψ a (bar α • b)

/- English proof (translation)
Unfold `quadDiff`. Rewrite using `[add_comm]`. Normalize the expressions using the abelian group laws.
-/
theorem qd_comm (ψ : M → Q) (a b : M) : quadDiff ψ a b = quadDiff ψ b a := by
  unfold quadDiff; rw [add_comm]; abel

/- English proof (translation)
The claim follows from `map_sum (AddMonoidHom.mk' (fun a => quadDiff ψ a b) (fun a a' => H.add1 a a' b)) x s`.
-/
theorem sum1 {bar : O → O} {ψ : M → Q} (H : BiHyp bar ψ) {ι : Type*}
    (s : Finset ι) (x : ι → M) (b : M) :
    quadDiff ψ (∑ e ∈ s, x e) b = ∑ e ∈ s, quadDiff ψ (x e) b :=
  map_sum (AddMonoidHom.mk' (fun a => quadDiff ψ a b) (fun a a' => H.add1 a a' b)) x s

/- English proof (translation)
Rewrite using `[qd_comm, sum1 H]`. Conclude with `Finset.sum_congr rfl fun e _ => qd_comm _ _ _`.
-/
theorem sum2 {bar : O → O} {ψ : M → Q} (H : BiHyp bar ψ) {ι : Type*}
    (s : Finset ι) (x : ι → M) (a : M) :
    quadDiff ψ a (∑ e ∈ s, x e) = ∑ e ∈ s, quadDiff ψ a (x e) := by
  rw [qd_comm, sum1 H]
  exact Finset.sum_congr rfl fun e _ => qd_comm _ _ _

/- English proof (translation)
Use `Finset.induction_on_max s ?_ ?_` and prove the remaining obligations. Simplify using `[H.zero]`. Introduce `a s hlt ih`. Establish `ha : a ∉ s` using `fun h => lt_irrefl a (hlt a h)`. Establish `hdef : ∀ p q : M, ψ (p + q) = quadDiff ψ p q + ψ p + ψ q`.

Introduce `p q`. Unfold `quadDiff`. Normalize the expressions using the abelian group laws. Establish `hfa : (insert a s).filter (fun e' => a < e') = ∅`. Rewrite using `[Finset.filter_eq_empty_iff]`.

Introduce `z hz`. Break down `Finset.mem_insert.mp hz with rfl | hz` into its components or cases. Conclude with `lt_irrefl _`. Conclude with `not_lt.mpr (hlt z hz).le`. Establish `hse : ∀ e ∈ s, ∑ e' ∈ (insert a s).filter (fun e' => e < e'), quadDiff ψ (x e) (x e') = quadDiff ψ (x e) (x a) + ∑ e' ∈ s.filter (fun e' => e < e'), quadDiff ψ (x e) (x e')`.

Introduce `e he`. Rewrite using `[Finset.filter_insert, if_pos (hlt e he), Finset.sum_insert (fun h => ha (Finset.mem_filter.mp h).1)]`. Rewrite using `[Finset.sum_insert ha, hdef, ih, Finset.sum_insert ha, Finset.sum_insert ha, hfa, Finset.sum_empty, Finset.sum_congr rfl hse, Finset.sum_add_distrib, qd_comm, sum1 H]`. Normalize the expressions using the abelian group laws.
-/
theorem expand {bar : O → O} {ψ : M → Q} (H : BiHyp bar ψ) {ι : Type*}
    [LinearOrder ι] (s : Finset ι) (x : ι → M) :
    ψ (∑ e ∈ s, x e) = ∑ e ∈ s, ψ (x e) +
      ∑ e ∈ s, ∑ e' ∈ s.filter (fun e' => e < e'), quadDiff ψ (x e) (x e') := by
  refine Finset.induction_on_max s ?_ ?_
  · simp [H.zero]
  · intro a s hlt ih
    have ha : a ∉ s := fun h => lt_irrefl a (hlt a h)
    have hdef : ∀ p q : M, ψ (p + q) = quadDiff ψ p q + ψ p + ψ q := by
      intro p q; unfold quadDiff; abel
    have hfa : (insert a s).filter (fun e' => a < e') = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact lt_irrefl _
      · exact not_lt.mpr (hlt z hz).le
    have hse : ∀ e ∈ s, ∑ e' ∈ (insert a s).filter (fun e' => e < e'), quadDiff ψ (x e) (x e') =
        quadDiff ψ (x e) (x a) + ∑ e' ∈ s.filter (fun e' => e < e'), quadDiff ψ (x e) (x e') := by
      intro e he
      rw [Finset.filter_insert, if_pos (hlt e he),
        Finset.sum_insert (fun h => ha (Finset.mem_filter.mp h).1)]
    rw [Finset.sum_insert ha, hdef, ih, Finset.sum_insert ha, Finset.sum_insert ha, hfa,
      Finset.sum_empty, Finset.sum_congr rfl hse, Finset.sum_add_distrib, qd_comm, sum1 H]
    abel

end Exact

section Quot
variable {O S M T : Type u} [CommRing O] [CommRing S] [AddCommGroup M] [Module O M]
    [AddCommGroup T] [Module S T]

/- English proof (translation)
Simplify using `[quadDiff, map_sub]`.
-/
theorem mk_quadDiff (N : AddSubgroup T) (φ : M → T) (a b : M) :
    QuotientAddGroup.mk' N (quadDiff φ a b) =
      quadDiff (fun a => QuotientAddGroup.mk' N (φ a)) a b := by
  simp [quadDiff, map_sub]

/- English proof (translation)
Establish `key : ∀ x : T, x ∈ N → QuotientAddGroup.mk' N x = 0` using `fun x hx => (QuotientAddGroup.eq_zero_iff x).mpr hx`. Use `⟨?_, key _ h.2.1, ?_⟩` and prove the remaining obligations. Introduce `a a' b`. Use `key _ (h.1 a a' b)` as an intermediate fact. Simplify using `only [map_sub, mk_quadDiff] at this`.

Rewrite `this` using `[sub_sub, sub_eq_zero]`. Conclude with `this`. Introduce `α a b`. Use `key _ (h.2.2.2 α a b)` as an intermediate fact. Simplify using `only [map_sub, mk_quadDiff] at this`.

Conclude with `sub_eq_zero.mp this`.
-/
theorem biHyp_of {N : AddSubgroup T} {bar : O → O} {nrm : O → S} {φ : M → T}
    (h : QuadHyp N bar nrm φ) : BiHyp bar (fun a => QuotientAddGroup.mk' N (φ a)) := by
  have key : ∀ x : T, x ∈ N → QuotientAddGroup.mk' N x = 0 :=
    fun x hx => (QuotientAddGroup.eq_zero_iff x).mpr hx
  refine ⟨?_, key _ h.2.1, ?_⟩
  · intro a a' b
    have := key _ (h.1 a a' b)
    simp only [map_sub, mk_quadDiff] at this
    rw [sub_sub, sub_eq_zero] at this
    exact this
  · intro α a b
    have := key _ (h.2.2.2 α a b)
    simp only [map_sub, mk_quadDiff] at this
    exact sub_eq_zero.mp this

/- English proof (translation)
The claim follows from `sub_eq_zero.mp (by rw [← map_sub]; exact (QuotientAddGroup.eq_zero_iff _).mpr (h.2.2.1 α s))`.
-/
theorem mk_nrm {N : AddSubgroup T} {bar : O → O} {nrm : O → S} {φ : M → T}
    (h : QuadHyp N bar nrm φ) (α : O) (s : M) :
    QuotientAddGroup.mk' N (φ (α • s)) = QuotientAddGroup.mk' N (nrm α • φ s) :=
  sub_eq_zero.mp (by rw [← map_sub]; exact (QuotientAddGroup.eq_zero_iff _).mpr (h.2.2.1 α s))

/- English proof (translation)
Use `set f := QuotientAddGroup.mk' N`. Establish `H` using `biHyp_of h`. Establish `e1 : ∀ i, f (φ (∑ e, y e i • t e)) = ∑ e, f (nrm (y e i) • φ (t e)) + ∑ e, ∑ e' ∈ Finset.univ.filter (fun e' => e < e'), quadDiff (fun a => f (φ a)) (t e) ((bar (y e i) * y e' i) • t e')`. Introduce `i`. Rewrite using `[expand H]`.

Use `congr 1`. Conclude with `Finset.sum_congr rfl fun e _ => mk_nrm h _ _`. Use `Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun e' _ => ?_` and prove the remaining obligations. Rewrite using `[H.adj, smul_smul]`. Rewrite using `[map_sum, Finset.sum_congr rfl fun i _ => e1 i, Finset.sum_add_distrib, map_add, map_sum, map_sum]`.

Use `congr 1`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun e _ => ?_` and prove the remaining obligations. Rewrite using `[← map_sum, ← Finset.sum_smul]`. Rewrite using `[Finset.sum_comm]`.

Use `Finset.sum_congr rfl fun e _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_comm, map_sum]`. Use `Finset.sum_congr rfl fun e' _ => ?_` and prove the remaining obligations. Rewrite using `[mk_quadDiff, Finset.sum_smul, sum2 H]`.
-/
theorem expand_mk {N : AddSubgroup T} {bar : O → O} {nrm : O → S} {φ : M → T}
    (h : QuadHyp N bar nrm φ) (n m : ℕ) (y : Fin m → Fin n → O) (t : Fin m → M) :
    QuotientAddGroup.mk' N (∑ i, φ (∑ e, y e i • t e)) =
      QuotientAddGroup.mk' N ((∑ e, (∑ i, nrm (y e i)) • φ (t e))
        + (∑ e, ∑ e' ∈ Finset.univ.filter (fun e' => e < e'),
            quadDiff φ (t e) ((∑ i, bar (y e i) * y e' i) • t e'))) := by
  set f := QuotientAddGroup.mk' N
  have H := biHyp_of h
  have e1 : ∀ i, f (φ (∑ e, y e i • t e)) = ∑ e, f (nrm (y e i) • φ (t e)) +
      ∑ e, ∑ e' ∈ Finset.univ.filter (fun e' => e < e'),
        quadDiff (fun a => f (φ a)) (t e) ((bar (y e i) * y e' i) • t e') := by
    intro i
    rw [expand H]
    congr 1
    · exact Finset.sum_congr rfl fun e _ => mk_nrm h _ _
    · refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun e' _ => ?_
      rw [H.adj, smul_smul]
  rw [map_sum, Finset.sum_congr rfl fun i _ => e1 i, Finset.sum_add_distrib, map_add, map_sum,
    map_sum]
  congr 1
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [← map_sum, ← Finset.sum_smul]
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [Finset.sum_comm, map_sum]
    refine Finset.sum_congr rfl fun e' _ => ?_
    rw [mk_quadDiff, Finset.sum_smul, sum2 H]

end Quot

end Formalism.ELL.QuadraticDifferenceHypotheses

namespace Formalism.ELL

open Formalism.ELL.QuadraticDifferenceHypotheses

universe u

/- English proof (translation)
Introduce `O S M T _ _ _ _ _ _ N bar nrm φ h n m y t`. Establish `E` using `expand_mk h n m y t`. Rewrite `E` using `[← sub_eq_zero, ← map_sub]`. Conclude with `(QuotientAddGroup.eq_zero_iff _).mp E`.
-/
theorem isogeny_expansion : IsoExpand.{u} := by
  intro O S M T _ _ _ _ _ _ N bar nrm φ h n m y t
  have E := expand_mk h n m y t
  rw [← sub_eq_zero, ← map_sub] at E
  exact (QuotientAddGroup.eq_zero_iff _).mp E

/- English proof (translation)
Introduce `O S M T _ _ _ _ _ _ N bar nrm φ h n m y t hiso hnrm`. Establish `E` using `isogeny_expansion O S M T N bar nrm φ h n m y t`. Establish `hz : ∀ a : M, quadDiff φ a 0 ∈ N` using `fun a => by`. Simplify `neg_mem h.2.1` using `[quadDiff]`. Simplify using `only [hiso, hnrm, zero_smul, Finset.sum_const_zero, zero_add] at E`.

Establish `hS : (∑ e, ∑ e' ∈ Finset.univ.filter (fun e' => e < e'), quadDiff φ (t e) 0) ∈ N` using `sum_mem fun e _ => sum_mem fun e' _ => hz _`. Use `add_mem E hS` as an intermediate fact. Rewrite `this` using `[sub_add_cancel]`. Then use the resulting hypothesis.
-/
theorem isogeny_vanishing : IsoVanish.{u} := by
  intro O S M T _ _ _ _ _ _ N bar nrm φ h n m y t hiso hnrm
  have E := isogeny_expansion O S M T N bar nrm φ h n m y t
  have hz : ∀ a : M, quadDiff φ a 0 ∈ N := fun a => by
    simpa [quadDiff] using neg_mem h.2.1
  simp only [hiso, hnrm, zero_smul, Finset.sum_const_zero, zero_add] at E
  have hS : (∑ e, ∑ e' ∈ Finset.univ.filter (fun e' => e < e'), quadDiff φ (t e) 0) ∈ N :=
    sum_mem fun e _ => sum_mem fun e' _ => hz _
  have := add_mem E hS
  rwa [sub_add_cancel] at this

end Formalism.ELL
