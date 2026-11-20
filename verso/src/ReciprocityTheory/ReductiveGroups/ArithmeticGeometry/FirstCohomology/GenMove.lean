import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.H1

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {X X' Y Y' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X}

/- English proof (translation)
Set `O : (K → L'.ι) → (K → L.ι) → Y'.Opens` to `fun q p => LB.wchart L' φ' q ⊓ LB.wchart (L.pull F) φ' (fun k _ => p k)`. Establish `le1 : ∀ q p k, O q p ≤ φ' k ⁻¹ᵁ ((L.pull F).U (fun _ => p k) ⊓ L'.U (q k))` using `fun q p k y hy => ⟨Set.mem_iInter.1 hy.2 k, Set.mem_iInter.1 hy.1 k⟩`. Establish `le2 : ∀ q p, O q p ≤ h ⁻¹ᵁ LB.wchart L φ p` using `fun q p y hy => Set.mem_iInter.2 fun k => by`. Use `mem_pull.1 (Set.mem_iInter.1 hy.2 k)` as an intermediate fact. Use `show φ k (h y) ∈ L.U (p k)`.

Rewrite using `[pt_eq hc]`. Conclude with `this`. Set `v : ∀ q p, Γ(Y', O q p)ˣ` to `fun q p => (∏ k, res (le1 q p k) (pullU (φ' k) _ (w.s (fun _ => p k, q k))) ^ ε k)⁻¹ * res (le2 q p) (pullU h _ (t.s p))`. Establish `germ : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) q p, r z ∈ O q p → gm r z (O q p) (v q p) = (∏ k, gw w (r ≫ φ' k) z (p k) (q k) ^ ε k)⁻¹ * gm (r ≫ h) z (LB.wchart L φ p) (t.s p)`. Introduce `Z r z q p hz`.

Establish `m2` using `le2 q p hz`. Use `show gm r z (O q p) ((∏ k, _)⁻¹ * _) = _`. Rewrite using `[map_mul, map_inv, map_prod]`. Use `congrArg₂ (· * ·) (congrArg (·⁻¹) (Finset.prod_congr rfl fun k _ => ?_)) ((gm_res r z (le2 q p) hz _).trans (gm_pull r h z _ m2 _))` and prove the remaining obligations. Establish `m` using `le1 q p k hz`.

Conclude with `(map_zpow _ _ _).trans (congrArg (· ^ ε k) ((gm_res r z (le1 q p k) hz _).trans (gm_pull r (φ' k) z _ m _)))`. Establish `memO : ∀ q (y : Y'), y ∈ LB.wchart L' φ' q → ∃ p, y ∈ O q p` using `fun q y hy => by choose p hp using fun k => exists_chart hL (F (φ' k y))`. Conclude with `⟨p, hy, Set.mem_iInter.2 fun k => mem_pull.2 (hp k)⟩`. Establish `glue : ∀ q, ∃ s : Γ(Y', LB.wchart L' φ' q)ˣ, ∀ p, res (inf_le_left : O q p ≤ _) s = v q p`. Introduce `q`.

Use `glue_unit _ (O q) (fun p => inf_le_left) (fun y hy => ?_) (v q) fun p p' y hy => ?_` and prove the remaining obligations. Take `⟨p, hp⟩` from `memO q y hy`. Conclude with `Opens.mem_iSup.2 ⟨p, hp⟩`. Rewrite using `[germ _ _ y q p hy.1, germ _ _ y q p' hy.2]`. Establish `hp : ∀ k, F (φ' k y) ∈ L.U (p k)` using `fun k => mem_pull.1 (Set.mem_iInter.1 hy.1.2 k)`.

Establish `hp' : ∀ k, F (φ' k y) ∈ L.U (p' k)` using `fun k => mem_pull.1 (Set.mem_iInter.1 hy.2.2 k)`. Establish `hq : ∀ k, φ' k y ∈ L'.U (q k)` using `fun k => Set.mem_iInter.1 hy.1.1 k`. Establish `e1 : ∀ k, gw w (𝟙 Y' ≫ φ' k) y (p k) (q k) = gm (φ' k ≫ F) y _ (L.g (p k) (p' k)) * gw w (𝟙 Y' ≫ φ' k) y (p' k) (q k)` using `fun k => by`. Rewrite using `[Category.id_comp, hw _ (φ' k) y (p k) (p' k) (q k) (q k) (hp k) (hp' k) (hq k) (hq k), gm_self hL' _ y (hq k), inv_one, mul_one]`. Establish `e2 : trF φ ε (𝟙 Y' ≫ h) y p p' = ∏ k, gm (φ' k ≫ F) y _ (L.g (p k) (p' k)) ^ ε k` using `Finset.prod_congr rfl fun k _ => by rw [Category.id_comp, ← hc k]`.

Rewrite using `[gen_trans ht (𝟙 Y' ≫ h) y (le2 q p hy.1) (le2 q p' hy.2), e2]`. Simplify using `only [e1, mul_zpow, Finset.prod_mul_distrib, mul_inv_rev]`. Rewrite using `[mul_assoc, inv_mul_cancel_left]`. Use `choose s hs using glue`. Establish `vals : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) q p, r z ∈ O q p → gm r z (LB.wchart L' φ' q) (s q) = (∏ k, gw w (r ≫ φ' k) z (p k) (q k) ^ ε k)⁻¹ * gm (r ≫ h) z (LB.wchart L φ p) (t.s p)`.

Introduce `Z r z q p hz`. Rewrite using `[← gm_res r z (inf_le_left : O q p ≤ _) hz, hs q p, germ Z r z q p hz]`. Use `⟨⟨s⟩, fun q q' => unit_ext fun y hy => ?_, fun Z r z p q hp hq => ?_⟩` and prove the remaining obligations. Establish `hq : ∀ k, φ' k y ∈ L'.U (q k)` using `fun k => Set.mem_iInter.1 hy.1 k`. Establish `hq' : ∀ k, φ' k y ∈ L'.U (q' k)` using `fun k => Set.mem_iInter.1 hy.2 k`.

Use `choose p hp using fun k => exists_chart hL (F (φ' k y))`. Establish `m : y ∈ O q p` using `⟨hy.1, Set.mem_iInter.2 fun k => mem_pull.2 (hp k)⟩`. Establish `m' : y ∈ O q' p` using `⟨hy.2, Set.mem_iInter.2 fun k => mem_pull.2 (hp k)⟩`. Rewrite using `[gm_res _ y _ hy, map_mul, gm_res _ y _ hy]`. Use `show gm (𝟙 Y') y (LB.wchart L' φ' q) (s q) = gm (𝟙 Y') y (LB.wchart L' φ' q ⊓ LB.wchart L' φ' q') ((LB.LinComb L' φ' ε).g q q') * gm (𝟙 Y') y (LB.wchart L' φ' q') (s q')`.

Rewrite using `[gm_linComb L' φ' ε (𝟙 Y') y q q' hy.1 hy.2, vals _ _ y q p m, vals _ _ y q' p m']`. Establish `e3 : ∀ k, gw w (𝟙 Y' ≫ φ' k) y (p k) (q k) = (gm (𝟙 Y' ≫ φ' k) y _ (L'.g (q k) (q' k)))⁻¹ * gw w (𝟙 Y' ≫ φ' k) y (p k) (q' k)` using `fun k => by`. Rewrite using `[Category.id_comp, hw _ (φ' k) y (p k) (p k) (q k) (q' k) (hp k) (hp k) (hq k) (hq' k), gm_self hL _ y (hp k), one_mul]`. Simplify using `only [e3, mul_zpow, inv_zpow, Finset.prod_mul_distrib, Finset.prod_inv_distrib, mul_inv_rev, inv_inv]`. Conclude with `(congrArg (· * _) (mul_comm _ _)).trans (mul_assoc _ _ _)`.

Establish `m : r z ∈ O q p` using `⟨Set.mem_iInter.2 hq, Set.mem_iInter.2 fun k => mem_pull.2 (hp k)⟩ show _ = _ * gm r z (LB.wchart L' φ' q) (s q)`. Rewrite using `[vals Z r z q p m, mul_inv_cancel_left]`.
-/
theorem exists_gen_move (hL : L.IsLB) (hL' : L'.IsLB) (w : LB.Iso L' (L.pull F)) (hw : PGen w)
    {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (φ' : K → (Y' ⟶ X')) (ε : K → ℤ) (h : Y' ⟶ Y)
    (hc : ∀ k, φ' k ≫ F = h ≫ φ k) (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) :
    ∃ a : LB.Gen (LB.LinComb L' φ' ε), a.IsGen ∧ PMaps w φ' φ ε a t h := by
  classical
  let O : (K → L'.ι) → (K → L.ι) → Y'.Opens := fun q p =>
    LB.wchart L' φ' q ⊓ LB.wchart (L.pull F) φ' (fun k _ => p k)
  have le1 : ∀ q p k, O q p ≤ φ' k ⁻¹ᵁ ((L.pull F).U (fun _ => p k) ⊓ L'.U (q k)) := fun q p k y hy =>
    ⟨Set.mem_iInter.1 hy.2 k, Set.mem_iInter.1 hy.1 k⟩
  have le2 : ∀ q p, O q p ≤ h ⁻¹ᵁ LB.wchart L φ p := fun q p y hy => Set.mem_iInter.2 fun k => by
    have := mem_pull.1 (Set.mem_iInter.1 hy.2 k)
    show φ k (h y) ∈ L.U (p k)
    rw [pt_eq hc]; exact this
  let v : ∀ q p, Γ(Y', O q p)ˣ := fun q p =>
    (∏ k, res (le1 q p k) (pullU (φ' k) _ (w.s (fun _ => p k, q k))) ^ ε k)⁻¹ * res (le2 q p) (pullU h _ (t.s p))
  have germ : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) q p, r z ∈ O q p →
      gm r z (O q p) (v q p) = (∏ k, gw w (r ≫ φ' k) z (p k) (q k) ^ ε k)⁻¹ * gm (r ≫ h) z (LB.wchart L φ p) (t.s p) := by
    intro Z r z q p hz
    have m2 := le2 q p hz
    show gm r z (O q p) ((∏ k, _)⁻¹ * _) = _
    rw [map_mul, map_inv, map_prod]
    refine congrArg₂ (· * ·) (congrArg (·⁻¹) (Finset.prod_congr rfl fun k _ => ?_))
      ((gm_res r z (le2 q p) hz _).trans (gm_pull r h z _ m2 _))
    have m := le1 q p k hz
    exact (map_zpow _ _ _).trans (congrArg (· ^ ε k) ((gm_res r z (le1 q p k) hz _).trans (gm_pull r (φ' k) z _ m _)))
  have memO : ∀ q (y : Y'), y ∈ LB.wchart L' φ' q → ∃ p, y ∈ O q p := fun q y hy => by
    choose p hp using fun k => exists_chart hL (F (φ' k y))
    exact ⟨p, hy, Set.mem_iInter.2 fun k => mem_pull.2 (hp k)⟩
  have glue : ∀ q, ∃ s : Γ(Y', LB.wchart L' φ' q)ˣ, ∀ p, res (inf_le_left : O q p ≤ _) s = v q p := by
    intro q
    refine glue_unit _ (O q) (fun p => inf_le_left) (fun y hy => ?_) (v q) fun p p' y hy => ?_
    · obtain ⟨p, hp⟩ := memO q y hy
      exact Opens.mem_iSup.2 ⟨p, hp⟩
    · rw [germ _ _ y q p hy.1, germ _ _ y q p' hy.2]
      have hp : ∀ k, F (φ' k y) ∈ L.U (p k) := fun k => mem_pull.1 (Set.mem_iInter.1 hy.1.2 k)
      have hp' : ∀ k, F (φ' k y) ∈ L.U (p' k) := fun k => mem_pull.1 (Set.mem_iInter.1 hy.2.2 k)
      have hq : ∀ k, φ' k y ∈ L'.U (q k) := fun k => Set.mem_iInter.1 hy.1.1 k
      have e1 : ∀ k, gw w (𝟙 Y' ≫ φ' k) y (p k) (q k) =
          gm (φ' k ≫ F) y _ (L.g (p k) (p' k)) * gw w (𝟙 Y' ≫ φ' k) y (p' k) (q k) := fun k => by
        rw [Category.id_comp, hw _ (φ' k) y (p k) (p' k) (q k) (q k) (hp k) (hp' k) (hq k) (hq k),
          gm_self hL' _ y (hq k), inv_one, mul_one]
      have e2 : trF φ ε (𝟙 Y' ≫ h) y p p' = ∏ k, gm (φ' k ≫ F) y _ (L.g (p k) (p' k)) ^ ε k :=
        Finset.prod_congr rfl fun k _ => by rw [Category.id_comp, ← hc k]
      rw [gen_trans ht (𝟙 Y' ≫ h) y (le2 q p hy.1) (le2 q p' hy.2), e2]
      simp only [e1, mul_zpow, Finset.prod_mul_distrib, mul_inv_rev]
      rw [mul_assoc, inv_mul_cancel_left]
  choose s hs using glue
  have vals : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) q p, r z ∈ O q p →
      gm r z (LB.wchart L' φ' q) (s q) =
        (∏ k, gw w (r ≫ φ' k) z (p k) (q k) ^ ε k)⁻¹ * gm (r ≫ h) z (LB.wchart L φ p) (t.s p) := by
    intro Z r z q p hz
    rw [← gm_res r z (inf_le_left : O q p ≤ _) hz, hs q p, germ Z r z q p hz]
  refine ⟨⟨s⟩, fun q q' => unit_ext fun y hy => ?_, fun Z r z p q hp hq => ?_⟩
  · have hq : ∀ k, φ' k y ∈ L'.U (q k) := fun k => Set.mem_iInter.1 hy.1 k
    have hq' : ∀ k, φ' k y ∈ L'.U (q' k) := fun k => Set.mem_iInter.1 hy.2 k
    choose p hp using fun k => exists_chart hL (F (φ' k y))
    have m : y ∈ O q p := ⟨hy.1, Set.mem_iInter.2 fun k => mem_pull.2 (hp k)⟩
    have m' : y ∈ O q' p := ⟨hy.2, Set.mem_iInter.2 fun k => mem_pull.2 (hp k)⟩
    rw [gm_res _ y _ hy, map_mul, gm_res _ y _ hy]
    show gm (𝟙 Y') y (LB.wchart L' φ' q) (s q) = gm (𝟙 Y') y (LB.wchart L' φ' q ⊓ LB.wchart L' φ' q')
      ((LB.LinComb L' φ' ε).g q q') * gm (𝟙 Y') y (LB.wchart L' φ' q') (s q')
    rw [gm_linComb L' φ' ε (𝟙 Y') y q q' hy.1 hy.2, vals _ _ y q p m, vals _ _ y q' p m']
    have e3 : ∀ k, gw w (𝟙 Y' ≫ φ' k) y (p k) (q k) =
        (gm (𝟙 Y' ≫ φ' k) y _ (L'.g (q k) (q' k)))⁻¹ * gw w (𝟙 Y' ≫ φ' k) y (p k) (q' k) := fun k => by
      rw [Category.id_comp, hw _ (φ' k) y (p k) (p k) (q k) (q' k) (hp k) (hp k) (hq k) (hq' k),
        gm_self hL _ y (hp k), one_mul]
    simp only [e3, mul_zpow, inv_zpow, Finset.prod_mul_distrib, Finset.prod_inv_distrib, mul_inv_rev, inv_inv]
    exact (congrArg (· * _) (mul_comm _ _)).trans (mul_assoc _ _ _)
  · have m : r z ∈ O q p := ⟨Set.mem_iInter.2 hq, Set.mem_iInter.2 fun k => mem_pull.2 (hp k)⟩
    show _ = _ * gm r z (LB.wchart L' φ' q) (s q)
    rw [vals Z r z q p m, mul_inv_cancel_left]

end ReciprocityTheory.ChartRestriction.G.H1
