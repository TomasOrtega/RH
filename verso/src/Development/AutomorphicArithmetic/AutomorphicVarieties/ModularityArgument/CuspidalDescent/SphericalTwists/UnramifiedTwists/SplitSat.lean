import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.SphericalTwists.RowProps
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParameterSphericalProductSpehQuotients

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual GlobalTheory.WeilDeligne GlobalTheory.LFun GlobalTheory.PRep UpperTheory.V.Af.Gu

/- English proof (translation)
Establish `he : ∀ g v, e.toLinearEquiv (ρ g v) = ρ' g (e.toLinearEquiv v)` using `fun g v => e.toIntertwiningMap.isIntertwining _ _ g v`. Prove the components needed by the constructor for the conclusion. Take `⟨x, hx⟩` from `h.exists_vec`. Establish `h1` using `hx.map e.toLinearEquiv.toLinearMap he ((map_ne_zero_iff _ e.toLinearEquiv.injective).2 hx.1)`. Conclude with `(Submodule.ne_bot_iff _).2 ⟨_, h1.2.1, h1.1⟩`.

Introduce `y hy h0`. Take `⟨x, rfl⟩` from `e.toLinearEquiv.surjective y`. Use `(h.2 x (GlobalTheory.LGrp.mem_fixed.2 fun k hk => e.toLinearEquiv.injective ?_) fun hx => h0 (by rw [hx, map_zero])).map e.toLinearEquiv.toLinearMap he h0` and prove the remaining obligations. Rewrite using `[he]`. Conclude with `GlobalTheory.LGrp.mem_fixed.1 hy k hk`.
-/
private theorem sat_of_equiv {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {n : ℕ} {V W : Type}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V} {ρ' : Representation ℂ (GL (Fin n) (w.adicCompletion E)) W}
    (e : ρ.Equiv ρ') {B : Multiset ℂˣ} (h : HasSatGL w ρ B) : HasSatGL w ρ' B := by
  have he : ∀ g v, e.toLinearEquiv (ρ g v) = ρ' g (e.toLinearEquiv v) := fun g v =>
    e.toIntertwiningMap.isIntertwining _ _ g v
  constructor
  · obtain ⟨x, hx⟩ := h.exists_vec
    have h1 := hx.map e.toLinearEquiv.toLinearMap he ((map_ne_zero_iff _ e.toLinearEquiv.injective).2 hx.1)
    exact (Submodule.ne_bot_iff _).2 ⟨_, h1.2.1, h1.1⟩
  · intro y hy h0
    obtain ⟨x, rfl⟩ := e.toLinearEquiv.surjective y
    refine (h.2 x (GlobalTheory.LGrp.mem_fixed.2 fun k hk => e.toLinearEquiv.injective ?_) fun hx => h0 (by rw [hx, map_zero])).map
      e.toLinearEquiv.toLinearMap he h0
    rw [he]
    exact GlobalTheory.LGrp.mem_fixed.1 hy k hk

/- English proof (translation)
Introduce and unpack `- E _ _ n c a d hn w ρ σ had hsp S hS τ ⟨e⟩ B hB`. Take `⟨S', s1, s2⟩` from `GlobalTheory.SatInd.satake_locProd_speh E w c n a d hn ρ σ (fun i => (had i).2) hsp B (sat_of_equiv e hB)`. Take `rfl : S = S'` from `funext fun i => (hS i).unique (s1 i)`. Simplify using `only [Multiset.bind_def, Multiset.pure_def, Multiset.bind_singleton, Multiset.map_map, Function.comp_def] at s2`. Apply `Multiset.map_injective (f := fun z : ℂˣ => (z : ℂ)) Units.val_injective` to reduce the goal to its premises.

Rewrite using `[← s2]`. Unfold `satTot`. Rewrite using `[← Multiset.coe_mapAddMonoidHom (fun z : ℂˣ => (z : ℂ)), map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_sum, ← Equiv.sum_comp Fin.revPerm]`.

Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[Multiset.coe_mapAddMonoidHom, Multiset.map_map]`. Use `Multiset.map_congr rfl fun x _ => ?_` and prove the remaining obligations. Establish `hq : Ideal.absNorm w.asIdeal = normV w` using `rfl`. Simplify using `only [Function.comp_apply, Units.val_mul, coe_qPow, Fin.revPerm_apply, Fin.val_rev, hq]`.

Use `congr 2`. Rewrite using `[Nat.cast_sub k.2]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem UpperTheory.V.Z.Desc.W.splitSat :
    UpperTheory.V.Z.Desc.W.SplitSat := by
  rintro - E _ _ n c a d hn w ρ σ had hsp S hS τ ⟨e⟩ B hB
  obtain ⟨S', s1, s2⟩ := GlobalTheory.SatInd.satake_locProd_speh E w c n a d hn ρ σ (fun i => (had i).2) hsp B (sat_of_equiv e hB)
  obtain rfl : S = S' := funext fun i => (hS i).unique (s1 i)
  simp only [Multiset.bind_def, Multiset.pure_def, Multiset.bind_singleton, Multiset.map_map, Function.comp_def] at s2
  apply Multiset.map_injective (f := fun z : ℂˣ => (z : ℂ)) Units.val_injective
  rw [← s2]
  unfold satTot
  rw [← Multiset.coe_mapAddMonoidHom (fun z : ℂˣ => (z : ℂ)), map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_sum, ← Equiv.sum_comp Fin.revPerm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Multiset.coe_mapAddMonoidHom, Multiset.map_map]
  refine Multiset.map_congr rfl fun x _ => ?_
  have hq : Ideal.absNorm w.asIdeal = normV w := rfl
  simp only [Function.comp_apply, Units.val_mul, coe_qPow, Fin.revPerm_apply, Fin.val_rev, hq]
  congr 2
  rw [Nat.cast_sub k.2]
  push_cast
  ring
