import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.OrbitalFiberDecomposition
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.OrbitalFiberPushforwardEqZero

open MulAction

/- English proof (translation)
Introduce `H X' X _ _ _ H₀ q k hN hq hH₀ hk hT hfin hidx`. Set `F : orbitRel.Quotient H X → Set X'` to `fun i => {y | q y = Quotient.out i}`. Use `letI act : ∀ i : orbitRel.Quotient H X, MulAction (stabilizer H (Quotient.out i)) (F i) := fun i => { smul := fun h y => ⟨(h : H) • (y : X'), by show q ((h : H) • (y : X')) = Quotient.out i`. Rewrite using `[hq, show q (y : X') = Quotient.out i from y.2]`. Conclude with `mem_stabilizer_iff.mp h.2⟩`.

Use `one_smul := fun y => Subtype.ext (one_smul H (y : X'))`. Use `mul_smul := fun a b y => Subtype.ext (mul_smul (a : H) (b : H) (y : X')) }`. Establish `hD` using `UpperTheory.orbitalFiber_decomposition H X' (orbitRel.Quotient H X) H₀ k (fun i => stabilizer H (Quotient.out i)) (fun i => F i) (fun i => (stabilizer H (Quotient.out i)).subtype) (fun i y => (y : X')) (fun i y => k (y : X')) hN hk hT (fun i h y => rfl) (fun i => Subtype.val_inje …`. Use `case cover =>`. Introduce `x hx`.

Take `⟨g, hg⟩` from `orbitRel_apply.mp (Quotient.mk_out (s := orbitRel H X) (q x))`. Use `⟨Quotient.mk _ (q x), ⟨g • x, ?_⟩, g⁻¹, ?_, ?_⟩` and prove the remaining obligations. Use `show q (g • x) = _`. Rewrite using `[hq]`. Conclude with `hg`.

Use `show k (g • x) ≠ 0`. Rewrite using `[hk]`. Conclude with `hx`. Use `show x = g⁻¹ • g • x`. Rewrite using `[inv_smul_smul]`.

Use `case disj =>`. Introduce `i j y y' h _ _ he`. Establish `hqe : h • Quotient.out i = Quotient.out j`. Establish `h1 : q (h • (y : X')) = q (y' : X')` using `congrArg q he`. Rewrite `h1` using `[hq, show q (y : X') = Quotient.out i from y.2, show q (y' : X') = Quotient.out j from y'.2]`.

Conclude with `h1`. Establish `hij : i = j`. Rewrite using `[← Quotient.out_eq i, ← Quotient.out_eq j]`. Conclude with `(Quotient.sound (orbitRel_apply.mpr ⟨h, hqe⟩)).symm`. Substitute `hij` using the available equality.

Use `⟨rfl, ?_⟩` and prove the remaining obligations. Rewrite using `[Subgroup.range_subtype]`. Conclude with `mem_stabilizer_iff.mpr hqe`. Rewrite using `[hD]`. Use `conv_rhs => unfold UpperTheory.V.Z.Sym.gq`.

Use `finsum_congr (fun i => ?_)` and prove the remaining obligations. Use `beta_reduce`. Distinguish the cases in `hz : ∃ y : X', q y = Quotient.out i ∧ k y ≠ 0`. Take `⟨y₀, hy₀, hk₀⟩` from `hz`. Establish `hind : (Subgroup.comap (stabilizer H (Quotient.out i)).subtype H₀).index ≠ 0`.

Use `hidx y₀ hk₀` as an intermediate fact. Rewrite `this` using `[hy₀]`. Conclude with `this`. Rewrite using `[UpperTheory.orbitalFiber_pushforward_eq_zero _ (F i) _ _ hind (fun z hz y => Subtype.ext (hH₀ (z : H) (Subgroup.mem_comap.mp hz) (y : X'))) (fun h y => hk (h : H) (y : X')) (((hfin (Quotient.out i)).preimage Subtype.val_injective.injOn).subset (fun y hy => ⟨y.2, hy⟩))]`. Rewrite using `[finsum_set_coe_eq_finsum_mem (f := k) (F i)]`.

Both sides reduce to the same expression. Use `push_neg at hz`. Establish `h0 : (∑ᶠ (y : X') (_ : q y = Quotient.out i), k y) = 0`. Apply `finsum_eq_zero_of_forall_eq_zero` to reduce the goal to its premises. Introduce `y`.

Rewrite using `[finsum_eq_if]`. Use `split_ifs with hy`. Conclude with `hz y hy`. Both sides reduce to the same expression. Rewrite using `[h0, zero_div]`.

Unfold `UpperTheory.V.Z.Sym.gq`. Apply `finsum_eq_zero_of_forall_eq_zero` to reduce the goal to its premises. Introduce `o`. Use `beta_reduce`. Rewrite using `[hz _ (Quotient.out o).2, zero_div]`.
-/
theorem UpperTheory.orbitalFiber_pushforward :
    UpperTheory.V.Z.Sym.Glob.Fib.Push := by
  intro H X' X _ _ _ H₀ q k hN hq hH₀ hk hT hfin hidx
  classical
  let F : orbitRel.Quotient H X → Set X' := fun i => {y | q y = Quotient.out i}
  letI act : ∀ i : orbitRel.Quotient H X, MulAction (stabilizer H (Quotient.out i)) (F i) := fun i =>
    { smul := fun h y => ⟨(h : H) • (y : X'), by
          show q ((h : H) • (y : X')) = Quotient.out i
          rw [hq, show q (y : X') = Quotient.out i from y.2]
          exact mem_stabilizer_iff.mp h.2⟩
      one_smul := fun y => Subtype.ext (one_smul H (y : X'))
      mul_smul := fun a b y => Subtype.ext (mul_smul (a : H) (b : H) (y : X')) }
  have hD := UpperTheory.orbitalFiber_decomposition H X' (orbitRel.Quotient H X) H₀ k
    (fun i => stabilizer H (Quotient.out i)) (fun i => F i)
    (fun i => (stabilizer H (Quotient.out i)).subtype) (fun i y => (y : X'))
    (fun i y => k (y : X')) hN hk hT
    (fun i h y => rfl) (fun i => Subtype.val_injective)
    (fun i h y => hk (h : H) (y : X')) (fun i y _ => rfl) ?cover ?disj
  case cover =>
    intro x hx
    obtain ⟨g, hg⟩ := orbitRel_apply.mp (Quotient.mk_out (s := orbitRel H X) (q x))
    refine ⟨Quotient.mk _ (q x), ⟨g • x, ?_⟩, g⁻¹, ?_, ?_⟩
    · show q (g • x) = _
      rw [hq]; exact hg
    · show k (g • x) ≠ 0
      rw [hk]; exact hx
    · show x = g⁻¹ • g • x
      rw [inv_smul_smul]
  case disj =>
    intro i j y y' h _ _ he
    have hqe : h • Quotient.out i = Quotient.out j := by
      have h1 : q (h • (y : X')) = q (y' : X') := congrArg q he
      rw [hq, show q (y : X') = Quotient.out i from y.2,
        show q (y' : X') = Quotient.out j from y'.2] at h1
      exact h1
    have hij : i = j := by
      rw [← Quotient.out_eq i, ← Quotient.out_eq j]
      exact (Quotient.sound (orbitRel_apply.mpr ⟨h, hqe⟩)).symm
    subst hij
    refine ⟨rfl, ?_⟩
    rw [Subgroup.range_subtype]
    exact mem_stabilizer_iff.mpr hqe
  rw [hD]
  conv_rhs => unfold UpperTheory.V.Z.Sym.gq
  refine finsum_congr (fun i => ?_)
  beta_reduce
  by_cases hz : ∃ y : X', q y = Quotient.out i ∧ k y ≠ 0
  · obtain ⟨y₀, hy₀, hk₀⟩ := hz
    have hind : (Subgroup.comap (stabilizer H (Quotient.out i)).subtype H₀).index ≠ 0 := by
      have := hidx y₀ hk₀
      rw [hy₀] at this
      exact this
    rw [UpperTheory.orbitalFiber_pushforward_eq_zero _ (F i) _ _ hind
      (fun z hz y => Subtype.ext (hH₀ (z : H) (Subgroup.mem_comap.mp hz) (y : X')))
      (fun h y => hk (h : H) (y : X'))
      (((hfin (Quotient.out i)).preimage Subtype.val_injective.injOn).subset
        (fun y hy => ⟨y.2, hy⟩))]
    rw [finsum_set_coe_eq_finsum_mem (f := k) (F i)]
    rfl
  · push_neg at hz
    have h0 : (∑ᶠ (y : X') (_ : q y = Quotient.out i), k y) = 0 := by
      apply finsum_eq_zero_of_forall_eq_zero
      intro y
      rw [finsum_eq_if]
      split_ifs with hy
      · exact hz y hy
      · rfl
    rw [h0, zero_div]
    unfold UpperTheory.V.Z.Sym.gq
    apply finsum_eq_zero_of_forall_eq_zero
    intro o
    beta_reduce
    rw [hz _ (Quotient.out o).2, zero_div]
