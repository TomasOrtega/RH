import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PFrameEx
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraMapQrOneBijective
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

/- English proof (translation)
Introduce `hF hLat hEq hPerf hInj hOnto hKp p _ D G L _ hm B`. Take `⟨A⟩` from `hF p D G L hm B.β B.sym`. Set `i : Gp G ≃* Gr G 1` to `MulEquiv.ofBijective (inclG G 1) (GlobalTheory.TorCls.AtP.inclG_one_bijective G)`. Establish `hi : ∀ g, i g = inclG G 1 g` using `fun _ => rfl`. Use `choose M hM hMl using hLat p D G L B.β A hm`.

Use `⟨{ lat := fun hp => M (i.symm hp), isLat := fun hp => hMl _, perf := ?_, equiv := ?_, inj := ?_, onto := ?_ }⟩` and prove the remaining obligations. Introduce `hp`. Establish `hp0 : (p : ℚ) ≠ 0` using `by exact_mod_cast (Fact.out : p.Prime).ne_zero`. Establish `hp1 : (0 : ℝ) < p` using `by exact_mod_cast (Fact.out : p.Prime).pos`. Use `set g := i.symm hp with hg`.

Use `set v : ℤ := (g.1 : ℚ_[p]).valuation with hv`. Use `⟨(p : ℚ) ^ (-v), zpow_pos (by exact_mod_cast (Fact.out : p.Prime).pos) _, ?_⟩` and prove the remaining obligations. Use `hPerf p D G L B.β A g _ ?_ _ (hM g)` and prove the remaining obligations. Establish `hne : (g.1 : ℚ_[p]) ≠ 0` using `g.1.ne_zero`. Rewrite using `[norm_mul, Padic.norm_eq_zpow_neg_valuation hne, ← hv]`.

Use `push_cast`. Rewrite using `[norm_zpow, Padic.norm_p, inv_zpow', neg_neg, ← zpow_add₀ hp1.ne']`. Simplify using the standard rewrite rules. Introduce `y hp w`. Establish `e : i.symm (GlobalTheory.LKCx.toP1 G B.β y * hp) = locC G (y : G.Cˣ × ℚˣ) * i.symm hp`.

Rewrite using `[map_mul]`. Use `congr 1`. Conclude with `i.symm_apply_apply (locC G (y : G.Cˣ × ℚˣ))`. Express the relevant statement in the definitionally equal form `actY L y w ∈ M (i.symm (GlobalTheory.LKCx.toP1 G B.β y * hp)) ↔ w ∈ M (i.symm hp)`. Rewrite using `[e, hM, hM]`.

Conclude with `hEq p D G L B.β A y _ w`. Introduce `hp hp'`. Establish `e : hp⁻¹ * hp' = inclG G 1 ((i.symm hp)⁻¹ * i.symm hp')`. Rewrite using `[← hi, map_mul, map_inv, i.apply_symm_apply, i.apply_symm_apply]`. Express the relevant statement in the definitionally equal form `M (i.symm hp) = M (i.symm hp') ↔ _`.

Rewrite using `[e, hKp p G, ← hInj p D G L B.β A]`. Prove the components needed by the constructor for the conclusion. Introduce `h x`. Rewrite using `[← hM, ← hM, h]`. Introduce `h`.

Use extensionality with `x`. Rewrite using `[hM, hM]`. Conclude with `h x`. Introduce and unpack `N hN ⟨s, hs, hP⟩`. Take `⟨g, hg⟩` from `hOnto p D G L B.β A hm N s hN hs hP`.

Use `⟨i g, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `M (i.symm (i g)) = N`. Rewrite using `[i.symm_apply_apply]`. Use extensionality with `x`. Rewrite using `[hM, hg]`.
-/
theorem UpperTheory.Gal.W2.pkTop_of :
    UpperTheory.Gal.W2.PFrameEx → UpperTheory.Gal.W2.PkLat → UpperTheory.Gal.W2.PkEquiv → UpperTheory.Gal.W2.PkPerf → UpperTheory.Gal.W2.PkInj → UpperTheory.Gal.W2.PkOnto → UpperTheory.Gal.W2.KpMem → UpperTheory.Gal.W2.PDicEx := by
  intro hF hLat hEq hPerf hInj hOnto hKp p _ D G L _ hm B
  obtain ⟨A⟩ := hF p D G L hm B.β B.sym
  let i : Gp G ≃* Gr G 1 := MulEquiv.ofBijective (inclG G 1) (GlobalTheory.TorCls.AtP.inclG_one_bijective G)
  have hi : ∀ g, i g = inclG G 1 g := fun _ => rfl
  choose M hM hMl using hLat p D G L B.β A hm
  refine ⟨{ lat := fun hp => M (i.symm hp), isLat := fun hp => hMl _, perf := ?_, equiv := ?_, inj := ?_, onto := ?_ }⟩
  · intro hp
    have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
    have hp1 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
    set g := i.symm hp with hg
    set v : ℤ := (g.1 : ℚ_[p]).valuation with hv
    refine ⟨(p : ℚ) ^ (-v), zpow_pos (by exact_mod_cast (Fact.out : p.Prime).pos) _, ?_⟩
    refine hPerf p D G L B.β A g _ ?_ _ (hM g)
    have hne : (g.1 : ℚ_[p]) ≠ 0 := g.1.ne_zero
    rw [norm_mul, Padic.norm_eq_zpow_neg_valuation hne, ← hv]
    push_cast
    rw [norm_zpow, Padic.norm_p, inv_zpow', neg_neg, ← zpow_add₀ hp1.ne']
    simp
  · intro y hp w
    have e : i.symm (GlobalTheory.LKCx.toP1 G B.β y * hp) = locC G (y : G.Cˣ × ℚˣ) * i.symm hp := by
      rw [map_mul]
      congr 1
      exact i.symm_apply_apply (locC G (y : G.Cˣ × ℚˣ))
    change actY L y w ∈ M (i.symm (GlobalTheory.LKCx.toP1 G B.β y * hp)) ↔ w ∈ M (i.symm hp)
    rw [e, hM, hM]
    exact hEq p D G L B.β A y _ w
  · intro hp hp'
    have e : hp⁻¹ * hp' = inclG G 1 ((i.symm hp)⁻¹ * i.symm hp') := by
      rw [← hi, map_mul, map_inv, i.apply_symm_apply, i.apply_symm_apply]
    change M (i.symm hp) = M (i.symm hp') ↔ _
    rw [e, hKp p G, ← hInj p D G L B.β A]
    constructor
    · intro h x
      rw [← hM, ← hM, h]
    · intro h
      ext x
      rw [hM, hM]
      exact h x
  · rintro N hN ⟨s, hs, hP⟩
    obtain ⟨g, hg⟩ := hOnto p D G L B.β A hm N s hN hs hP
    refine ⟨i g, ?_⟩
    change M (i.symm (i g)) = N
    rw [i.symm_apply_apply]
    ext x
    rw [hM, hg]
