import Formalism.WachLatticeTwists.LatticeDualFibres.MapHOneCommSquare

universe u
open ReciprocityTheory.Gal
namespace Formalism.RepresentationBoundsCohomology.LOC

/- English proof (translation)
Introduce `O G T V A _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ρT ρV ρA j q hj ej eq hq hker hc hdiv htors`. Establish `hjinj : Function.Injective j` using `hj.injective`. Set `W : Submodule O V` to `(H0 ρA).comap q`. Establish `hW : ∀ v ∈ W, ∀ g, ∃ t, j t = ρV g v - v`. Introduce `v hv g`.

Establish `h : ρV g v - v ∈ LinearMap.ker q`. Rewrite using `[LinearMap.mem_ker, map_sub, eq, (mem_riemannRochSpace_iff_regularAt_everywhere ρA _).1 hv g, sub_self]`. Rewrite `h` using `[hker]`. Conclude with `h`. Use `choose! s hs using hW`.

Set `c : W →ₗ[O] Z1 ρT` to `{ toFun := fun v => ⟨fun g => s v g, by`. Use `⟨hj.continuous_iff.2 ?_, fun g h => hjinj ?_⟩` and prove the remaining obligations. Establish `: (j ∘ fun g => s (v:V) g) = fun g => ρV g v - v` using `funext fun g => hs v v.2 g`. Rewrite using `[this]`. Conclude with `(hc.comp (continuous_id.prodMk continuous_const)).sub continuous_const`.

Rewrite using `[map_add, ej, hs v v.2, hs v v.2, hs v v.2, map_mul, Module.End.mul_apply, map_sub] abel⟩`. Use the proof step `map_add' := fun v w => Subtype.ext (funext fun g => hjinj (by show j (s ((v + w : W) : V) g) = j (s v g + s w g)`. Rewrite using `[map_add, hs _ (v+w).2, hs v v.2, hs w w.2, Submodule.coe_add, map_add]`. Use the proof step `abel))`. Use the proof step `map_smul' := fun r v => Subtype.ext (funext fun g => hjinj (by show j (s ((r • v : W) : V) g) = j (r • s v g)`.

Rewrite using `[map_smul, hs _ (r • v).2, hs v v.2, Submodule.coe_smul, map_smul, smul_sub])) }`. Set `δ0 : W →ₗ[O] H1 ρT` to `(Submodule.mkQ _).comp c`. Set `qW : W →ₗ[O] H0 ρA` to `q.restrict (fun v hv => hv)`. Establish `hqW : Function.Surjective qW` using `fun a => by`. Take `⟨v, hv⟩` from `hq a`.

Conclude with `⟨⟨v, by show q v ∈ H0 ρA; rw [hv]; exact a.2⟩, Subtype.ext hv⟩`. Establish `hk : LinearMap.ker qW ≤ LinearMap.ker δ0`. Introduce `v hv`. Establish `h1 : q v = 0` using `congrArg Subtype.val hv`. Establish `h2 : (v:V) ∈ LinearMap.range j` using `hker ▸ h1`.

Take `⟨t, ht⟩` from `h2`. Rewrite using `[LinearMap.mem_ker]`. Use `show Submodule.Quotient.mk (c v) = 0`. Rewrite using `[Submodule.Quotient.mk_eq_zero]`. Use `(mem_coboundaries1 _ _).2 ⟨t, fun g => hjinj ?_⟩` and prove the remaining obligations.

Use `show j (s v g) = _`. Rewrite using `[hs v v.2, map_sub, ej, ht]`. Set `δ : H0 ρA →ₗ[O] H1 ρT` to `((LinearMap.ker qW).liftQ δ0 hk).comp (qW.quotKerEquivOfSurjective hqW).symm.toLinearMap`. Establish `hδ : ∀ v : W, δ (qW v) = δ0 v`. Introduce `v`.

Establish `: (qW.quotKerEquivOfSurjective hqW).symm (qW v) = Submodule.Quotient.mk v` using `(LinearEquiv.symm_apply_eq _).2 rfl`. Use `show (LinearMap.ker qW).liftQ δ0 hk ((qW.quotKerEquivOfSurjective hqW).symm (qW v)) = _`. Rewrite using `[this]`. Both sides reduce to the same expression. Use `⟨δ, ?_⟩` and prove the remaining obligations.

Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, rfl⟩`. Take `⟨c0, hc0, hca⟩` from `htors a`. Use `(Submodule.mem_torsion_iff _).2 ⟨⟨c0, mem_nonZeroDivisors_of_ne_zero hc0⟩, ?_⟩` and prove the remaining obligations.

Use `show c0 • δ a = 0`. Rewrite using `[← map_smul, show c0 • a = 0 from Subtype.ext hca, map_zero]`. Introduce `hx`. Take `⟨n, hn⟩` from `(Submodule.mem_torsion_iff _).1 hx`. Proceed by induction on `x using Submodule.Quotient.induction_on with`.

Consider the case `H z`. Establish `hn' : (Submodule.Quotient.mk ((n : O) • z) : H1 ρT) = 0` using `hn`. Rewrite `hn'` using `[Submodule.Quotient.mk_eq_zero]`. Take `⟨t, ht⟩` from `(mem_coboundaries1 _ _).1 hn'`. Establish `hn0 : (n : O) ≠ 0` using `nonZeroDivisors.coe_ne_zero n`.

Take `⟨v, hv⟩` from `(hdiv n hn0).2 (j t)`. Establish `hv' : (n : O) • v = j t` using `hv`. Establish `hz : ∀ g, ρV g v - v = j (z.1 g)`. Introduce `g`. Apply `(hdiv n hn0).1` to reduce the goal to its premises.

Use `show (n : O) • (ρV g v - v) = (n : O) • j (z.1 g)`. Establish `e` using `ht g`. Establish `e' : (n : O) • z.1 g = ρT g t - t` using `e`. Rewrite using `[smul_sub, ← map_smul, hv', ← ej, ← map_sub, ← e', map_smul]`. Establish `hvW : v ∈ W`.

Use `(mem_riemannRochSpace_iff_regularAt_everywhere ρA _).2 fun g => ?_` and prove the remaining obligations. Establish `: q (ρV g v - v) = 0`. Rewrite using `[hz g]`. Conclude with `LinearMap.mem_ker.1 (hker ▸ LinearMap.mem_range_self j _)`. Rewrite `this` using `[map_sub, eq, sub_eq_zero]`.

Conclude with `this`. Use `⟨qW ⟨v, hvW⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[hδ]`. Use `show Submodule.Quotient.mk (c ⟨v, hvW⟩) = Submodule.Quotient.mk z`. Use `congr 1`.

Use `Subtype.ext (funext fun g => hjinj ?_)` and prove the remaining obligations. Use `show j (s v g) = _`. Rewrite using `[hs v hvW, hz]`.
-/
theorem connTors : StatConnTors.{u} := by
  intro O G T V A _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ρT ρV ρA j q hj ej eq hq hker hc hdiv htors
  classical
  have hjinj : Function.Injective j := hj.injective
  let W : Submodule O V := (H0 ρA).comap q
  have hW : ∀ v ∈ W, ∀ g, ∃ t, j t = ρV g v - v := by
    intro v hv g
    have h : ρV g v - v ∈ LinearMap.ker q := by
      rw [LinearMap.mem_ker, map_sub, eq, (mem_riemannRochSpace_iff_regularAt_everywhere ρA _).1 hv g, sub_self]
    rw [hker] at h
    exact h
  choose! s hs using hW
  let c : W →ₗ[O] Z1 ρT :=
    { toFun := fun v => ⟨fun g => s v g, by
          refine ⟨hj.continuous_iff.2 ?_, fun g h => hjinj ?_⟩
          · have : (j ∘ fun g => s (v:V) g) = fun g => ρV g v - v := funext fun g => hs v v.2 g
            rw [this]
            exact (hc.comp (continuous_id.prodMk continuous_const)).sub continuous_const
          · rw [map_add, ej, hs v v.2, hs v v.2, hs v v.2, map_mul, Module.End.mul_apply, map_sub]
            abel⟩
      map_add' := fun v w => Subtype.ext (funext fun g => hjinj (by
          show j (s ((v + w : W) : V) g) = j (s v g + s w g)
          rw [map_add, hs _ (v+w).2, hs v v.2, hs w w.2, Submodule.coe_add, map_add]; abel))
      map_smul' := fun r v => Subtype.ext (funext fun g => hjinj (by
          show j (s ((r • v : W) : V) g) = j (r • s v g)
          rw [map_smul, hs _ (r • v).2, hs v v.2, Submodule.coe_smul, map_smul, smul_sub])) }
  let δ0 : W →ₗ[O] H1 ρT := (Submodule.mkQ _).comp c
  let qW : W →ₗ[O] H0 ρA := q.restrict (fun v hv => hv)
  have hqW : Function.Surjective qW := fun a => by
    obtain ⟨v, hv⟩ := hq a
    exact ⟨⟨v, by show q v ∈ H0 ρA; rw [hv]; exact a.2⟩, Subtype.ext hv⟩
  have hk : LinearMap.ker qW ≤ LinearMap.ker δ0 := by
    intro v hv
    have h1 : q v = 0 := congrArg Subtype.val hv
    have h2 : (v:V) ∈ LinearMap.range j := hker ▸ h1
    obtain ⟨t, ht⟩ := h2
    rw [LinearMap.mem_ker]
    show Submodule.Quotient.mk (c v) = 0
    rw [Submodule.Quotient.mk_eq_zero]
    refine (mem_coboundaries1 _ _).2 ⟨t, fun g => hjinj ?_⟩
    show j (s v g) = _
    rw [hs v v.2, map_sub, ej, ht]
  let δ : H0 ρA →ₗ[O] H1 ρT :=
    ((LinearMap.ker qW).liftQ δ0 hk).comp (qW.quotKerEquivOfSurjective hqW).symm.toLinearMap
  have hδ : ∀ v : W, δ (qW v) = δ0 v := by
    intro v
    have : (qW.quotKerEquivOfSurjective hqW).symm (qW v) = Submodule.Quotient.mk v :=
      (LinearEquiv.symm_apply_eq _).2 rfl
    show (LinearMap.ker qW).liftQ δ0 hk ((qW.quotKerEquivOfSurjective hqW).symm (qW v)) = _
    rw [this]; rfl
  refine ⟨δ, ?_⟩
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    obtain ⟨c0, hc0, hca⟩ := htors a
    refine (Submodule.mem_torsion_iff _).2 ⟨⟨c0, mem_nonZeroDivisors_of_ne_zero hc0⟩, ?_⟩
    show c0 • δ a = 0
    rw [← map_smul, show c0 • a = 0 from Subtype.ext hca, map_zero]
  · intro hx
    obtain ⟨n, hn⟩ := (Submodule.mem_torsion_iff _).1 hx
    induction x using Submodule.Quotient.induction_on with
    | H z =>
      have hn' : (Submodule.Quotient.mk ((n : O) • z) : H1 ρT) = 0 := hn
      rw [Submodule.Quotient.mk_eq_zero] at hn'
      obtain ⟨t, ht⟩ := (mem_coboundaries1 _ _).1 hn'
      have hn0 : (n : O) ≠ 0 := nonZeroDivisors.coe_ne_zero n
      obtain ⟨v, hv⟩ := (hdiv n hn0).2 (j t)
      have hv' : (n : O) • v = j t := hv
      have hz : ∀ g, ρV g v - v = j (z.1 g) := by
        intro g
        apply (hdiv n hn0).1
        show (n : O) • (ρV g v - v) = (n : O) • j (z.1 g)
        have e := ht g
        have e' : (n : O) • z.1 g = ρT g t - t := e
        rw [smul_sub, ← map_smul, hv', ← ej, ← map_sub, ← e', map_smul]
      have hvW : v ∈ W := by
        refine (mem_riemannRochSpace_iff_regularAt_everywhere ρA _).2 fun g => ?_
        have : q (ρV g v - v) = 0 := by
          rw [hz g]
          exact LinearMap.mem_ker.1 (hker ▸ LinearMap.mem_range_self j _)
        rw [map_sub, eq, sub_eq_zero] at this
        exact this
      refine ⟨qW ⟨v, hvW⟩, ?_⟩
      rw [hδ]
      show Submodule.Quotient.mk (c ⟨v, hvW⟩) = Submodule.Quotient.mk z
      congr 1
      refine Subtype.ext (funext fun g => hjinj ?_)
      show j (s v g) = _
      rw [hs v hvW, hz]

end Formalism.RepresentationBoundsCohomology.LOC
