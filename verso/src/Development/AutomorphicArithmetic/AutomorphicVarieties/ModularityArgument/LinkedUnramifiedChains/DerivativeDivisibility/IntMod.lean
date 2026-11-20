import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CmpPrime

open Polynomial

namespace UpperTheory.V.J

section

variable {O Λ B : Type} [CommRing O] [CommRing Λ] [CommRing B] [Algebra O Λ] [Algebra O B]
  (lam : Λ →ₐ[O] B) (M : Type) [AddCommGroup M] [Module B M] [Module Λ M]
  (hs : ∀ (a : Λ) (m : M), a • m = lam a • m)

/- English proof (translation)
Proceed by induction on `n generalizing m with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Rewrite using `[pow_succ, Module.End.mul_apply, ih, pow_succ, mul_smul]`. Both sides reduce to the same expression.
-/
private theorem actL_pow (a : B) (n : ℕ) (m : M) :
    ((actL lam M hs a) ^ n) m = (a ^ n) • m := by
  induction n generalizing m with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Module.End.mul_apply, ih, pow_succ, mul_smul]
    rfl

/- English proof (translation)
Use `Polynomial.induction_on' q (fun p r hp hr => ?_) (fun n c => ?_)` and prove the remaining obligations. Rewrite using `[eval₂_add, add_smul, hp, hr, map_add, LinearMap.add_apply]`. Rewrite using `[eval₂_monomial, aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply, actL_pow, mul_smul, hs]`. Both sides reduce to the same expression.
-/
private theorem act_eval (a : B) (q : Λ[X]) (m : M) :
    q.eval₂ (lam : Λ →+* B) a • m = (aeval (actL lam M hs a) q) m := by
  refine Polynomial.induction_on' q (fun p r hp hr => ?_) (fun n c => ?_)
  · rw [eval₂_add, add_smul, hp, hr, map_add, LinearMap.add_apply]
  · rw [eval₂_monomial, aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply,
      actL_pow, mul_smul, hs]
    rfl

end

end UpperTheory.V.J

/- English proof (translation)
Introduce `O Λ B _ _ _ _ _ _ lam J M _ _ _ d a`. Use `d.free` as an intermediate fact. Use `d.fin` as an intermediate fact. Use `⟨(actL lam M d.hs a).charpoly, (actL lam M d.hs a).charpoly_monic, ?_⟩` and prove the remaining obligations. Establish `hann : eval₂ (lam : Λ →+* B) a (actL lam M d.hs a).charpoly ∈ Module.annihilator B M`.

Rewrite using `[Module.mem_annihilator]`. Introduce `m`. Rewrite using `[act_eval lam M d.hs, LinearMap.aeval_self_charpoly]`. Both sides reduce to the same expression. Generalize the expression as in `eval₂ (lam : Λ →+* B) a (actL lam M d.hs a).charpoly = x at hann ⊢`.

Rewrite using `[← d.rad.radical, Ideal.radical_eq_sInf, Submodule.mem_sInf]`. Introduce and unpack `p ⟨hJp, hp⟩`. Conclude with `(d.supp p hp).2 hJp hann`.
-/
theorem UpperTheory.V.J.intMod :
    UpperTheory.V.J.IntMod := by
  intro O Λ B _ _ _ _ _ _ lam J M _ _ _ d a
  have := d.free
  have := d.fin
  refine ⟨(actL lam M d.hs a).charpoly, (actL lam M d.hs a).charpoly_monic, ?_⟩
  have hann : eval₂ (lam : Λ →+* B) a (actL lam M d.hs a).charpoly ∈ Module.annihilator B M := by
    rw [Module.mem_annihilator]
    intro m
    rw [act_eval lam M d.hs, LinearMap.aeval_self_charpoly]
    rfl
  generalize eval₂ (lam : Λ →+* B) a (actL lam M d.hs a).charpoly = x at hann ⊢
  rw [← d.rad.radical, Ideal.radical_eq_sInf, Submodule.mem_sInf]
  rintro p ⟨hJp, hp⟩
  exact (d.supp p hp).2 hJp hann
