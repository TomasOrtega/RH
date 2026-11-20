import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.TorsionRankCounts.RankCount

open NumberField UpperTheory.V UpperTheory.V.KL UpperTheory.V.ZK UpperTheory.V.ZK.Up CategoryTheory

/- English proof (translation)
Introduce `q`. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `G _ m z`. Proceed by induction on `z using Finsupp.induction_linear with`. Consider the case `zero => simp`.

Consider the case `add x y hx hy => simp only [map_add, hx, hy]`. Consider the case `single g a`. Use extensionality with `i`. Simplify using `only [bd, rq, Finsupp.mapRange.addMonoidHom_apply, Finsupp.mapRange_single, Finsupp.linearCombination_single, Finsupp.smul_apply, Finsupp.add_apply, Finsupp.finset_sum_apply, Finsupp.mapRange_apply, smul_eq_mul]`. Use `push_cast`.

Unfold `Finsupp.single`. Apply the tactic sequence `split_ifs <;> simp [Pi.single_apply, apply_ite]`. Introduce `G H _ _ f m z`. Simplify using `only [cm, rq, Finsupp.lmapDomain_apply, Finsupp.mapRange.addMonoidHom_apply]`. Conclude with `Finsupp.mapDomain_mapRange _ _ _ _ (fun _ _ => by simp)`.

Introduce `G m y`. Use `⟨Finsupp.mapRange (fun x : ZMod q => (x.cast : ℤ)) (by simp) y, ?_⟩` and prove the remaining obligations. Use extensionality with `i`. Simplify using `[rq]`. Introduce `G m z`.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `hd : ∀ i, (q : ℤ) ∣ z i`. Introduce `i`. Use `DFunLike.congr_fun h i` as an intermediate fact.

Simplify `this` using `[rq, ZMod.intCast_zmod_eq_zero_iff_dvd]`. Use `⟨Finsupp.mapRange (fun x : ℤ => x / q) (by simp) z, ?_⟩` and prove the remaining obligations. Use extensionality with `i`. Simplify using `[Int.mul_ediv_cancel' (hd i)]`. Introduce and unpack `⟨w, rfl⟩`.

Use extensionality with `i`. Simplify using `[rq]`.
-/
theorem UpperTheory.V.ZK.Up.rqFacts : UpperTheory.V.ZK.Up.RqFacts := by
  intro q
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro G _ m z
    induction z using Finsupp.induction_linear with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | single g a =>
      ext i
      simp only [bd, rq, Finsupp.mapRange.addMonoidHom_apply, Finsupp.mapRange_single,
        Finsupp.linearCombination_single, Finsupp.smul_apply, Finsupp.add_apply,
        Finsupp.finset_sum_apply, Finsupp.mapRange_apply, smul_eq_mul]
      push_cast
      unfold Finsupp.single
      split_ifs <;> simp [Pi.single_apply, apply_ite]
  · intro G H _ _ f m z
    simp only [cm, rq, Finsupp.lmapDomain_apply, Finsupp.mapRange.addMonoidHom_apply]
    exact Finsupp.mapDomain_mapRange _ _ _ _ (fun _ _ => by simp)
  · intro G m y
    refine ⟨Finsupp.mapRange (fun x : ZMod q => (x.cast : ℤ)) (by simp) y, ?_⟩
    ext i
    simp [rq]
  · intro G m z
    constructor
    · intro h
      have hd : ∀ i, (q : ℤ) ∣ z i := by
        intro i
        have := DFunLike.congr_fun h i
        simpa [rq, ZMod.intCast_zmod_eq_zero_iff_dvd] using this
      refine ⟨Finsupp.mapRange (fun x : ℤ => x / q) (by simp) z, ?_⟩
      ext i
      simp [Int.mul_ediv_cancel' (hd i)]
    · rintro ⟨w, rfl⟩
      ext i
      simp [rq]
