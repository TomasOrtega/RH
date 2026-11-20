import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.MixedUnlinkedExponents.ValsExtOf

noncomputable section

open NumberField IsDedekindDomain Polynomial Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.HenQ UpperTheory.V.Z.Bc UpperTheory.V.Published
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL UpperTheory.Zero.LLC UpperTheory.V.Z.Inf UpperTheory.V.Z.Gam UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter
open GroundTheory.Global.SemiLocal
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

namespace UpperTheory.Gal.GamX

/- English proof (translation)
Simplify using `[lp]`.
-/
private theorem lp_zero : lp 0 = 1 := by simp [lp]

/- English proof (translation)
Simplify using `[lp]`.
-/
private theorem lp_add (A B : Multiset ℂˣ) : lp (A + B) = lp A * lp B := by simp [lp]

/- English proof (translation)
Proceed by induction on `t using Finset.induction_on with`. Consider the case `empty => simp [lp_zero]`. Consider the case `insert a t ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, lp_add, ih]`.
-/
private theorem lp_sum {ι : Type} (t : Finset ι) (A : ι → Multiset ℂˣ) :
    lp (∑ i ∈ t, A i) = ∏ i ∈ t, lp (A i) := by
  induction t using Finset.induction_on with
  | empty => simp [lp_zero]
  | insert a t ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, lp_add, ih]

/- English proof (translation)
Express the relevant statement in the definitionally equal form `(χ ^ a).1 _ = _`. Rewrite using `[SubgroupClass.coe_pow, MonoidHom.pow_apply]`. Both sides reduce to the same expression.
-/
private theorem loc_pow_apply {E : Type} [Field E] [NumberField E] (χ : HChar E) (a : ℕ) (v x) :
    (χ ^ a).loc v x = χ.loc v x ^ a := by
  change (χ ^ a).1 _ = _
  rw [SubgroupClass.coe_pow, MonoidHom.pow_apply]
  rfl

/- English proof (translation)
Unfold `GamSumOf GamSum`. Introduce `hM hN hV hP hC hF hT K L _ _ _ _ _ _ _ _ hp n hn π P hW v s s' hs hs' θ hθ`. Take `⟨η, h1, h2⟩` from `hN K L hp`. Take `⟨⟨w₀⟩, hf⟩` from `hF K L v`. Establish `hfw : ∀ w : PlacesOver L v, fdeg w = fdeg w₀` using `fun w => hf w w₀`.

Establish `hf0 : 0 < fdeg w₀` using `(hV K L v w₀ 1).2.2.1`. Establish `he : ∀ (j : ℕ) (w : PlacesOver L v), ((η ^ j).loc v).comp (nm w) = 1`. Introduce `j w`. Use `MonoidHom.ext fun x => ?_` and prove the remaining obligations. Establish `hx` using `DFunLike.congr_fun (h2 v w).1 x`.

Simplify using `only [MonoidHom.comp_apply, MonoidHom.one_apply] at hx ⊢`. Rewrite using `[loc_pow_apply, hx, one_pow]`. Establish `hm` using `hM K L hp n hn π P hW η h1 v s s' hs hs' θ hθ`. Establish `hlp : lp (∑ j ∈ Finset.range (Module.finrank K L), vals (chs s) (θ * (η ^ j).loc v)) = (lp (∑ w, vals (chs (s' w)) (θ.comp (nm w)))).comp (X ^ fdeg w₀)`. Rewrite using `[lp_sum, lp_sum, Polynomial.prod_comp]`.

Simplify using `only [← (hC _ _).2.2]`. Rewrite using `[hm]`. Conclude with `Finset.prod_congr rfl fun w _ => by rw [hfw w]`. Establish `h3` using `hP (fdeg w₀) hf0 _ _ hlp`. Establish `h4` using `hT K L v (Module.finrank K L) (fdeg w₀) (fun j => (η ^ j).loc v) hfw ⟨w₀⟩ he (fun w w' μ h => (h2 v w).2.1 w' μ h) (fun w μ hμ h => ((h2 v w).2.2 μ hμ).2.2 h) (chs s) (hC _ s).2.1 θ hθ`.

Establish `h5` using `h3.symm.trans h4`. Use `Multiset.ext.2 fun a => ?_` and prove the remaining obligations. Establish `h6` using `congrArg (Multiset.count a) h5`. Rewrite `h6` using `[Multiset.count_nsmul, Multiset.count_nsmul]`. Conclude with `Nat.eq_of_mul_eq_mul_left hf0 h6`.
-/
theorem gamSumOf : GamSumOf := by
  unfold GamSumOf GamSum
  intro hM hN hV hP hC hF hT K L _ _ _ _ _ _ _ _ hp n hn π P hW v s s' hs hs' θ hθ
  obtain ⟨η, h1, h2⟩ := hN K L hp
  obtain ⟨⟨w₀⟩, hf⟩ := hF K L v
  have hfw : ∀ w : PlacesOver L v, fdeg w = fdeg w₀ := fun w => hf w w₀
  have hf0 : 0 < fdeg w₀ := (hV K L v w₀ 1).2.2.1
  have he : ∀ (j : ℕ) (w : PlacesOver L v), ((η ^ j).loc v).comp (nm w) = 1 := by
    intro j w
    refine MonoidHom.ext fun x => ?_
    have hx := DFunLike.congr_fun (h2 v w).1 x
    simp only [MonoidHom.comp_apply, MonoidHom.one_apply] at hx ⊢
    rw [loc_pow_apply, hx, one_pow]
  have hm := hM K L hp n hn π P hW η h1 v s s' hs hs' θ hθ
  have hlp : lp (∑ j ∈ Finset.range (Module.finrank K L), vals (chs s) (θ * (η ^ j).loc v)) =
      (lp (∑ w, vals (chs (s' w)) (θ.comp (nm w)))).comp (X ^ fdeg w₀) := by
    rw [lp_sum, lp_sum, Polynomial.prod_comp]
    simp only [← (hC _ _).2.2]
    rw [hm]
    exact Finset.prod_congr rfl fun w _ => by rw [hfw w]
  have h3 := hP (fdeg w₀) hf0 _ _ hlp
  have h4 := hT K L v (Module.finrank K L) (fdeg w₀) (fun j => (η ^ j).loc v) hfw ⟨w₀⟩ he
    (fun w w' μ h => (h2 v w).2.1 w' μ h) (fun w μ hμ h => ((h2 v w).2.2 μ hμ).2.2 h)
    (chs s) (hC _ s).2.1 θ hθ
  have h5 := h3.symm.trans h4
  refine Multiset.ext.2 fun a => ?_
  have h6 := congrArg (Multiset.count a) h5
  rw [Multiset.count_nsmul, Multiset.count_nsmul] at h6
  exact Nat.eq_of_mul_eq_mul_left hf0 h6

end UpperTheory.Gal.GamX
