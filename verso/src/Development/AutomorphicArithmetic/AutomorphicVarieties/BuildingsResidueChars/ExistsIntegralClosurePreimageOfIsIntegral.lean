import Mathlib

open Polynomial in
/- English proof (translation)
Introduce `R E k _ _ _ _ _ _ ψ x hx`. Take `⟨p, hpm, hpx⟩` from `hx`. Use `set q : E[X] := p.map (algebraMap ℤ E) with hq`. Establish `hqm : q.Monic` using `hpm.map _`. Establish `hqs : q.Splits` using `IsAlgClosed.splits q`.

Set `lift : E → integralClosure R E` to `fun a => if h : IsIntegral R a then ⟨a, h⟩ else 0`. Establish `hlift : ∀ a ∈ q.roots, ((lift a : integralClosure R E) : E) = a`. Introduce `a ha`. Establish `hr : q.IsRoot a` using `(mem_roots hqm.ne_zero).1 ha`. Establish `hi : IsIntegral ℤ a` using `⟨p, hpm, by`.

Rewrite using `[eval₂_eq_eval_map]`. Conclude with `hr⟩`. Establish `hiR : IsIntegral R a` using `hi.tower_top`. Simplify using `[lift, hiR]`. Establish `hfac : p.map (algebraMap ℤ (integralClosure R E)) = (q.roots.map fun a => X - C (lift a)).prod`.

Apply `Polynomial.map_injective (algebraMap (integralClosure R E) E) Subtype.val_injective` to reduce the goal to its premises. Rewrite using `[Polynomial.map_map, Polynomial.map_multiset_prod, Multiset.map_map]`. Establish `e : (algebraMap (integralClosure R E) E).comp (algebraMap ℤ (integralClosure R E)) = algebraMap ℤ E` using `RingHom.ext_int _ _`. Rewrite using `[e, ← hq]`. Use `conv_lhs => rw [hqs.eq_prod_roots_of_monic hqm]`.

Use `congr 1`. Apply `Multiset.map_congr rfl` to reduce the goal to its premises. Introduce `a ha`. Simplify using `only [Function.comp_apply, Polynomial.map_sub, map_X, map_C]`. Use `congr 2`.

Conclude with `(hlift a ha).symm`. Establish `hk : p.map (algebraMap ℤ k) = (q.roots.map fun a => X - C (ψ (lift a))).prod`. Establish `e : ψ.comp (algebraMap ℤ (integralClosure R E)) = algebraMap ℤ k` using `RingHom.ext_int _ _`. Rewrite using `[← e, ← Polynomial.map_map, hfac, Polynomial.map_multiset_prod, Multiset.map_map]`. Use `congr 1`.

Apply `Multiset.map_congr rfl` to reduce the goal to its premises. Introduce `a _`. Simplify using the standard rewrite rules. Establish `h0 : (p.map (algebraMap ℤ k)).eval x = 0`. Rewrite using `[eval_map]`.

Conclude with `hpx`. Rewrite `h0` using `[hk, eval_multiset_prod, Multiset.map_map, Multiset.prod_eq_zero_iff]`. Take `⟨a, _, ha⟩` from `Multiset.mem_map.1 h0`. Use `⟨lift a, ?_⟩` and prove the remaining obligations. Simplify using `only [Function.comp_apply, eval_sub, eval_X, eval_C] at ha`.

Conclude with `(sub_eq_zero.1 ha).symm`.
-/
theorem UpperTheory.exists_integralClosure_preimage_of_isIntegral :
    ∀ (R E k : Type) [CommRing R] [Field E] [IsAlgClosed E] [Algebra R E] [CommRing k] [IsDomain k] (ψ : integralClosure R E →+* k) (x : k), IsIntegral ℤ x → ∃ y, ψ y = x := by
  intro R E k _ _ _ _ _ _ ψ x hx
  classical
  obtain ⟨p, hpm, hpx⟩ := hx
  set q : E[X] := p.map (algebraMap ℤ E) with hq
  have hqm : q.Monic := hpm.map _
  have hqs : q.Splits := IsAlgClosed.splits q
  let lift : E → integralClosure R E := fun a => if h : IsIntegral R a then ⟨a, h⟩ else 0
  have hlift : ∀ a ∈ q.roots, ((lift a : integralClosure R E) : E) = a := by
    intro a ha
    have hr : q.IsRoot a := (mem_roots hqm.ne_zero).1 ha
    have hi : IsIntegral ℤ a := ⟨p, hpm, by
      rw [eval₂_eq_eval_map]
      exact hr⟩
    have hiR : IsIntegral R a := hi.tower_top
    simp [lift, hiR]
  have hfac : p.map (algebraMap ℤ (integralClosure R E)) = (q.roots.map fun a => X - C (lift a)).prod := by
    apply Polynomial.map_injective (algebraMap (integralClosure R E) E) Subtype.val_injective
    rw [Polynomial.map_map, Polynomial.map_multiset_prod, Multiset.map_map]
    have e : (algebraMap (integralClosure R E) E).comp (algebraMap ℤ (integralClosure R E)) = algebraMap ℤ E :=
      RingHom.ext_int _ _
    rw [e, ← hq]
    conv_lhs => rw [hqs.eq_prod_roots_of_monic hqm]
    congr 1
    apply Multiset.map_congr rfl
    intro a ha
    simp only [Function.comp_apply, Polynomial.map_sub, map_X, map_C]
    congr 2
    exact (hlift a ha).symm
  have hk : p.map (algebraMap ℤ k) = (q.roots.map fun a => X - C (ψ (lift a))).prod := by
    have e : ψ.comp (algebraMap ℤ (integralClosure R E)) = algebraMap ℤ k := RingHom.ext_int _ _
    rw [← e, ← Polynomial.map_map, hfac, Polynomial.map_multiset_prod, Multiset.map_map]
    congr 1
    apply Multiset.map_congr rfl
    intro a _
    simp
  have h0 : (p.map (algebraMap ℤ k)).eval x = 0 := by
    rw [eval_map]
    exact hpx
  rw [hk, eval_multiset_prod, Multiset.map_map, Multiset.prod_eq_zero_iff] at h0
  obtain ⟨a, _, ha⟩ := Multiset.mem_map.1 h0
  refine ⟨lift a, ?_⟩
  simp only [Function.comp_apply, eval_sub, eval_X, eval_C] at ha
  exact (sub_eq_zero.1 ha).symm
