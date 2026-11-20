import Mathlib
import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.CasselmanSuffTemp
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BernsteinUnitaryProductIrreducible
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.TotallyDisjointProductIrreducibleOfPolynomialRin
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.LanglandsClassificationCuspidalSupport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CentralExponentBoundOver
import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.MFront
import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.MBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.Imports
import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.TScalarFull

open Filter Topology GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult UpperTheory.Lit.Cas

section SlopeTestRemainingChoices

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

variable (k) in
/- English proof (translation)
Take `⟨z, h1, h2⟩` from `GlobalTheory.CentralExponent.exists_nabs_lt_one k`. Use `⟨z, ?_, h2⟩` and prove the remaining obligations. Establish `h3 : ValuativeRel.valuation k (z : k) < 1` using `lt_of_le_of_ne h1 fun h => h2.ne ((nabs_eq_one_iff z).2 h)`. Use `haveI : MulArchimedean (ValuativeRel.ValueGroupWithZero k) := ValuativeRel.isRankLeOne_iff_mulArchimedean.1 inferInstance`. Use `(IsValuativeTopology.hasBasis_nhds_zero k).tendsto_right_iff.2 fun γ _ => ?_` and prove the remaining obligations.

Take `⟨n, hn⟩` from `exists_pow_lt₀ h3 γ`. Use `filter_upwards [eventually_ge_atTop n] with i hi`. Use `show ValuativeRel.valuation k ((z : k) ^ i) < γ`. Rewrite using `[map_pow]`. Conclude with `lt_of_le_of_lt (pow_le_pow_right_of_le_one' h1 hi) hn`.
-/
private theorem exists_small : ∃ z : kˣ, Tendsto (fun i : ℕ => (z : k) ^ i) atTop (𝓝 0) ∧ nabs k z < 1 := by
  obtain ⟨z, h1, h2⟩ := GlobalTheory.CentralExponent.exists_nabs_lt_one k
  refine ⟨z, ?_, h2⟩
  have h3 : ValuativeRel.valuation k (z : k) < 1 :=
    lt_of_le_of_ne h1 fun h => h2.ne ((nabs_eq_one_iff z).2 h)
  haveI : MulArchimedean (ValuativeRel.ValueGroupWithZero k) :=
    ValuativeRel.isRankLeOne_iff_mulArchimedean.1 inferInstance
  refine (IsValuativeTopology.hasBasis_nhds_zero k).tendsto_right_iff.2 fun γ _ => ?_
  obtain ⟨n, hn⟩ := exists_pow_lt₀ h3 γ
  filter_upwards [eventually_ge_atTop n] with i hi
  show ValuativeRel.valuation k ((z : k) ^ i) < γ
  rw [map_pow]
  exact lt_of_le_of_lt (pow_le_pow_right_of_le_one' h1 hi) hn

/- English proof (translation)
Establish `key : ∀ w : ℂ, (IrrRep.det (Fin 1) χ hχ).ρ (Matrix.GeneralLinearGroup.scalar (Fin 1) z) w = (χ z : ℂ) • w`. Introduce `w`. Establish `hd : Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin 1) z) = z`. Use `ext`. Simplify using the standard rewrite rules.

Express the relevant statement in the definitionally equal form `((χ (Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin 1) z)) : ℂ) • (LinearMap.id : ℂ →ₗ[ℂ] ℂ)) w = _`. Rewrite using `[hd]`. Both sides reduce to the same expression. Introduce `v`. Set `φ` to `equivRep (IrrRep.det (Fin 1) χ hχ)`.

Take `⟨w, rfl⟩ : ∃ w, φ.toLinearEquiv w = v` from `⟨φ.toLinearEquiv.symm v, φ.toLinearEquiv.apply_symm_apply v⟩`. Establish `h` using `φ.toIntertwiningMap.isIntertwining _ _ (Matrix.GeneralLinearGroup.scalar (Fin 1) z) w`. Establish `h2 : φ.toIntertwiningMap ((IrrRep.det (Fin 1) χ hχ).ρ (Matrix.GeneralLinearGroup.scalar (Fin 1) z) w) = (χ z : ℂ) • φ.toIntertwiningMap w`. Rewrite using `[← map_smul]`. Use `congr 1`.

Conclude with `key w`. Conclude with `h.symm.trans h2`.
-/
private theorem scalarBy_ofChar (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) (z : kˣ) :
    ScalarBy (IrrGL.ofChar χ hχ) z (χ z : ℂ) := by
  have key : ∀ w : ℂ, (IrrRep.det (Fin 1) χ hχ).ρ (Matrix.GeneralLinearGroup.scalar (Fin 1) z) w =
      (χ z : ℂ) • w := by
    intro w
    have hd : Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin 1) z) = z := by
      ext
      simp
    change ((χ (Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin 1) z)) : ℂ) •
      (LinearMap.id : ℂ →ₗ[ℂ] ℂ)) w = _
    rw [hd]
    rfl
  intro v
  let φ := equivRep (IrrRep.det (Fin 1) χ hχ)
  obtain ⟨w, rfl⟩ : ∃ w, φ.toLinearEquiv w = v :=
    ⟨φ.toLinearEquiv.symm v, φ.toLinearEquiv.apply_symm_apply v⟩
  have h := φ.toIntertwiningMap.isIntertwining _ _ (Matrix.GeneralLinearGroup.scalar (Fin 1) z) w
  have h2 : φ.toIntertwiningMap ((IrrRep.det (Fin 1) χ hχ).ρ (Matrix.GeneralLinearGroup.scalar (Fin 1) z) w) =
      (χ z : ℂ) • φ.toIntertwiningMap w := by
    rw [← map_smul]
    congr 1
    exact key w
  exact h.symm.trans h2

/- English proof (translation)
Unfold `IrrGL.nu`. Rewrite using `[IrrGL.tw_ofChar]`. Establish `e : (χ z : ℂ) * ((nabs k z ^ s : ℝ) : ℂ) = ((χ * absPow k (s : ℂ)) z : ℂ)`. Rewrite using `[MonoidHom.mul_apply, Units.val_mul, val_absPow_ofReal]`. Rewrite using `[e]`.

Conclude with `scalarBy_ofChar _ _ z`.
-/
private theorem scalarBy_nu (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) (z : kˣ) (s : ℝ) :
    ScalarBy ((IrrGL.ofChar χ hχ).nu s) z ((χ z : ℂ) * ((nabs k z ^ s : ℝ) : ℂ)) := by
  unfold IrrGL.nu
  rw [IrrGL.tw_ofChar]
  have e : (χ z : ℂ) * ((nabs k z ^ s : ℝ) : ℂ) = ((χ * absPow k (s : ℂ)) z : ℂ) := by
    rw [MonoidHom.mul_apply, Units.val_mul, val_absPow_ofReal]
  rw [e]
  exact scalarBy_ofChar _ _ z

end SlopeTestRemainingChoices

/- English proof (translation)
Introduce `hG hBZ hZ k _ _ _ _ r t V _ _ σ A χ hχ hrt hA hU hχu hmem`. Use `set c0 : ℝ := -((t : ℝ) - 1) / 2 with hc0`. Set `B : ℝ → IrrGL k` to `fun e => (IrrGL.ofChar χ hχ).nu (e : ℂ)`. Establish `hB_inj : ∀ {e e' : ℝ}, B e = B e' → e = e'` using `fun h => (IrrGL.nu_ofChar_inj χ hχ).mp h`. Establish `hmem' : B c0 ∈ A`.

Establish `e : ((c0 : ℝ) : ℂ) = -((t : ℂ) - 1) / 2`. Rewrite using `[hc0]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Use `show (IrrGL.ofChar χ hχ).nu (c0 : ℂ) ∈ A`.

Rewrite using `[e]`. Conclude with `hmem`. Take `⟨h, x, hxA, -⟩` from `id hA`. Set `P : Fin h → Prop` to `fun a => ∃ j : ℤ, x a = B (c0 + j)`. Set `L : Finset (Fin h)` to `Finset.univ.filter P`.

Set `g : Fin h → ℤ` to `fun a => if ha : P a then ha.choose else 0`. Establish `hg : ∀ a ∈ L, x a = B (c0 + g a)`. Introduce `a ha`. Establish `ha' : P a` using `(Finset.mem_filter.mp ha).2`. Simplify using `only [g, dif_pos ha']`.

Conclude with `ha'.choose_spec`. Rewrite `hmem'` using `[← hxA]`. Take `⟨a₀, -, ha₀⟩` from `Multiset.mem_map.mp hmem'`. Establish `ha₀L : a₀ ∈ L` using `Finset.mem_filter.mpr ⟨Finset.mem_univ _, 0, by rw [ha₀]; simp⟩`. Establish `hga₀ : g a₀ = 0`.

Establish `e` using `hg a₀ ha₀L`. Rewrite `e` using `[ha₀]`. Establish `e'` using `hB_inj e`. Establish `e'' : (g a₀ : ℝ) = 0` using `by linarith`. Conclude with `e''` after adjusting the coercions.

Take `⟨S, hSL, hSne, hsep, hsum⟩` from `UpperTheory.Lit.Mix.comb h L g ⟨a₀, ha₀L, hga₀.le⟩`. Establish `hr : ∑ a, (x a).1 = r`. Establish `e` using `hA.sum_fst`. Rewrite `e` using `[← hxA, Multiset.map_map, Fintype.card_fin]`. Conclude with `e`.

Establish `hS1 : ∀ a ∈ S, (x a).1 = 1` using `fun a ha => by rw [hg a (hSL ha)]; rfl`. Establish `hScard : S.card ≤ r`. Rewrite using `[← hr]`. Combine the equalities or inequalities in the displayed calculation. Take `⟨n, rfl⟩ : ∃ n, r = S.card + n` from `⟨r - S.card, by omega⟩`.

Establish `e0 : Finset.univ.val.filter (· ∈ S) = S.val`. Rewrite using `[← Finset.filter_val]`. Use `congr 1`. Use extensionality with `a`. Simplify using the standard rewrite rules.

Establish `e1 : Finset.univ.val.filter (· ∉ S) = Sᶜ.val`. Rewrite using `[← Finset.filter_val]`. Use `congr 1`. Use extensionality with `a`. Simplify using the standard rewrite rules.

Set `A₀ : Multiset (IrrGL k)` to `S.val.map x`. Set `A₁ : Multiset (IrrGL k)` to `Sᶜ.val.map x`. Establish `hA01 : A₀ + A₁ = A` using `by show S.val.map x + Sᶜ.val.map x = A`. Rewrite using `[← hxA, ← e0, ← e1, ← Multiset.map_add, Multiset.filter_add_not]`. Establish `hA₀sum : (A₀.map Sigma.fst).sum = S.card`.

Simplify using `only [A₀, Multiset.map_map]`. Rewrite using `[← Finset.sum_eq_multiset_sum]`. Simplify using `only [Function.comp_apply]`. Rewrite using `[Finset.sum_congr rfl hS1]`. Simplify using the standard rewrite rules.

Establish `hsep' : ∀ y ∈ A₀, ∀ y' ∈ A₁, ∀ j : ℤ, |j| ≤ 1 → y ≠ y'.nu j`. Introduce `y hy y' hy' j hj hyy`. Simplify using `only [A₀, A₁, Multiset.mem_map, Finset.mem_val, Finset.mem_compl] at hy hy'`. Take `⟨a, haS, rfl⟩` from `hy`. Take `⟨b, hbS, rfl⟩` from `hy'`.

Rewrite `hyy` using `[hg a (hSL haS)]`. Establish `hb' : x b = B (c0 + ((g a - j : ℤ) : ℝ))`. Establish `e` using `congrArg (fun y => y.nu (-(j : ℂ))) hyy`. Simplify using `only [B, IrrGL.nu_nu] at e`. Rewrite `e` using `[add_neg_cancel, IrrGL.nu_zero]`.

Rewrite using `[← e]`. Simplify using `only [B]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Establish `hbL : b ∈ L` using `Finset.mem_filter.mpr ⟨Finset.mem_univ _, g a - j, hb'⟩`. Establish `h2` using `hsep a haS b hbL hbS`. Rewrite `hb'` using `[hg b hbL]`. Establish `e` using `hB_inj hb'`. Establish `e' : (g b : ℝ) = g a - j`.

Move the coercions through the operations in `at e`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `e'' : g b = g a - j` using `by exact_mod_cast e'`. Rewrite `h2` using `[e'', sub_sub_cancel]`. Combine the linear equalities and inequalities to obtain the conclusion.

Take `⟨h₀, h₁, u, w, hu, hw, huA, f, hf⟩` from `UpperTheory.Lit.Mix.front hG hBZ hZ k S.card n V σ A₀ A₁ (by rw [hA01]; exact hA) hA₀sum hsep'`. Take `⟨z, hzt, hz1⟩` from `exists_small k`. Establish `hzpos` using `nabs_pos' k z`. Set `E : IrrGL k → ℝ` to `fun y => if hy : ∃ e : ℝ, y = B e then hy.choose else 0`. Establish `hE : ∀ e, E (B e) = e`.

Introduce `e`. Establish `hy : ∃ e' : ℝ, B e = B e'` using `⟨e, rfl⟩`. Simplify using `only [E, dif_pos hy]`. Conclude with `(hB_inj hy.choose_spec).symm`. Establish `hu_form : ∀ a, u a = B (E (u a))`.

Introduce `a`. Establish `hmem0 : u a ∈ A₀`. Rewrite using `[← huA]`. Conclude with `Multiset.mem_map_of_mem u (Finset.mem_univ_val a)`. Simplify using `only [A₀, Multiset.mem_map, Finset.mem_val] at hmem0`.

Take `⟨b, hb, hxb⟩` from `hmem0`. Rewrite using `[← hxb, hg b (hSL hb), hE]`. Establish `hEsum : ∑ a, E (u a) = ∑ b ∈ S, (c0 + g b)`. Establish `h1 : ∑ a, E (u a) = (A₀.map E).sum`. Rewrite using `[← huA, Multiset.map_map]`.

Both sides reduce to the same expression. Rewrite using `[h1]`. Simplify using `only [A₀, Multiset.map_map]`. Rewrite using `[← Finset.sum_eq_multiset_sum]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises.

Introduce `b hb`. Simplify using `only [Function.comp_apply]`. Rewrite using `[hg b (hSL hb), hE]`. Set `c : Fin h₀ → ℂ` to `fun a => (χ z : ℂ) * ((nabs k z ^ E (u a) : ℝ) : ℂ)`. Establish `hsc : ∀ a, ScalarBy (u a) z (c a)`.

Introduce `a`. Establish `key` using `scalarBy_nu χ hχ z (E (u a))`. Establish `e` using `hu_form a`. Simplify using `only [B] at e`. Rewrite `key` using `[← e]`.

Conclude with `key`. Establish `hscal` using `scalarFull k h₀ S.card u hu z c hsc`. Establish `hadm : IsAdmissible σ` using `(hBZ k).1 _ V σ hA.isSmooth hA.isIrreducible`. Establish `hnt : Nontrivial V` using `Model.nontrivial_of_isIrreducible hA.isIrreducible`. Establish `hb` using `UpperTheory.Lit.Mix.bound k S.card n V _ _ σ (prodIrr u hu) (prodIrr w hw) hadm hnt hU ⟨f, hf⟩ z hzt (∏ a, c a) hscal`.

Establish `hnorm : ‖(∏ a, c a) * ((absPow k (((S.card * n : ℕ) : ℂ) / 2)) z : ℂ)‖ = nabs k z ^ (∑ a, E (u a) + (S.card * n : ℝ) / 2)`. Establish `e2 : (((S.card * n : ℕ) : ℂ) / 2) = ((((S.card * n : ℝ) / 2 : ℝ)) : ℂ)`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e2, val_absPow_ofReal, norm_mul, norm_prod]`.

Simplify using `only [c, norm_mul, hχu z, one_mul, Complex.norm_real, Real.norm_eq_abs]`. Rewrite using `[Real.rpow_add hzpos, Real.rpow_sum_of_pos hzpos]`. Use `congr 1`. Apply `Finset.prod_congr rfl` to reduce the goal to its premises. Introduce `a _`.

Conclude with `abs_of_pos (Real.rpow_pos_of_pos hzpos _)`. Conclude with `abs_of_pos (Real.rpow_pos_of_pos hzpos _)`. Rewrite `hb` using `[hnorm]`. Establish `hexp : 0 ≤ ∑ a, E (u a) + (S.card * n : ℝ) / 2`. Assume the negation of the conclusion as `hneg`.

Use `push_neg at hneg`. Establish `h3` using `Real.one_lt_rpow_of_pos_of_lt_one_of_neg hzpos hz1 hneg`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite `hexp` using `[hEsum, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]`. Establish `hsumR : 2 * ∑ b ∈ S, (g b : ℝ) ≤ (S.card : ℝ) * (S.card - 1)`.

Establish `h4` using `hsum`. Conclude with `h4` after adjusting the coercions. Establish `hm : (1 : ℝ) ≤ S.card` using `by exact_mod_cast hSne.card_pos`. Establish `hmn : (S.card : ℝ) + n + 1 ≤ t` using `by exact_mod_cast Nat.succ_le_of_lt hrt`. Rewrite `hexp` using `[hc0]`.

Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left hmn (by linarith : (0 : ℝ) ≤ S.card)]`.
-/
theorem UpperTheory.Lit.Mix.nolow :
    GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.ZelevinskyPolynomialRing → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ (GL (Fin r) k) V) (A : Multiset (IrrGL k)) (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ), r < t → HasSupport σ A → IsUnitarisable σ → IsUnitaryChar χ → (IrrGL.ofChar χ hχ).nu (-((t : ℂ) - 1) / 2) ∉ A := by
  intro hG hBZ hZ k _ _ _ _ r t V _ _ σ A χ hχ hrt hA hU hχu hmem
  classical
  set c0 : ℝ := -((t : ℝ) - 1) / 2 with hc0
  let B : ℝ → IrrGL k := fun e => (IrrGL.ofChar χ hχ).nu (e : ℂ)
  have hB_inj : ∀ {e e' : ℝ}, B e = B e' → e = e' := fun h => (IrrGL.nu_ofChar_inj χ hχ).mp h
  have hmem' : B c0 ∈ A := by
    have e : ((c0 : ℝ) : ℂ) = -((t : ℂ) - 1) / 2 := by
      rw [hc0]
      push_cast
      ring
    show (IrrGL.ofChar χ hχ).nu (c0 : ℂ) ∈ A
    rw [e]
    exact hmem
  obtain ⟨h, x, hxA, -⟩ := id hA
  let P : Fin h → Prop := fun a => ∃ j : ℤ, x a = B (c0 + j)
  let L : Finset (Fin h) := Finset.univ.filter P
  let g : Fin h → ℤ := fun a => if ha : P a then ha.choose else 0
  have hg : ∀ a ∈ L, x a = B (c0 + g a) := by
    intro a ha
    have ha' : P a := (Finset.mem_filter.mp ha).2
    simp only [g, dif_pos ha']
    exact ha'.choose_spec
  rw [← hxA] at hmem'
  obtain ⟨a₀, -, ha₀⟩ := Multiset.mem_map.mp hmem'
  have ha₀L : a₀ ∈ L := Finset.mem_filter.mpr ⟨Finset.mem_univ _, 0, by rw [ha₀]; simp⟩
  have hga₀ : g a₀ = 0 := by
    have e := hg a₀ ha₀L
    rw [ha₀] at e
    have e' := hB_inj e
    have e'' : (g a₀ : ℝ) = 0 := by linarith
    exact_mod_cast e''
  obtain ⟨S, hSL, hSne, hsep, hsum⟩ := UpperTheory.Lit.Mix.comb h L g ⟨a₀, ha₀L, hga₀.le⟩
  have hr : ∑ a, (x a).1 = r := by
    have e := hA.sum_fst
    rw [← hxA, Multiset.map_map, Fintype.card_fin] at e
    exact e
  have hS1 : ∀ a ∈ S, (x a).1 = 1 := fun a ha => by rw [hg a (hSL ha)]; rfl
  have hScard : S.card ≤ r := by
    rw [← hr]
    calc S.card = ∑ a ∈ S, (x a).1 := by rw [Finset.sum_congr rfl hS1]; simp
      _ ≤ ∑ a, (x a).1 := Finset.sum_le_sum_of_subset (Finset.subset_univ S)
  obtain ⟨n, rfl⟩ : ∃ n, r = S.card + n := ⟨r - S.card, by omega⟩
  have e0 : Finset.univ.val.filter (· ∈ S) = S.val := by
    rw [← Finset.filter_val]
    congr 1
    ext a
    simp
  have e1 : Finset.univ.val.filter (· ∉ S) = Sᶜ.val := by
    rw [← Finset.filter_val]
    congr 1
    ext a
    simp
  let A₀ : Multiset (IrrGL k) := S.val.map x
  let A₁ : Multiset (IrrGL k) := Sᶜ.val.map x
  have hA01 : A₀ + A₁ = A := by
    show S.val.map x + Sᶜ.val.map x = A
    rw [← hxA, ← e0, ← e1, ← Multiset.map_add, Multiset.filter_add_not]
  have hA₀sum : (A₀.map Sigma.fst).sum = S.card := by
    simp only [A₀, Multiset.map_map]
    rw [← Finset.sum_eq_multiset_sum]
    simp only [Function.comp_apply]
    rw [Finset.sum_congr rfl hS1]
    simp
  have hsep' : ∀ y ∈ A₀, ∀ y' ∈ A₁, ∀ j : ℤ, |j| ≤ 1 → y ≠ y'.nu j := by
    intro y hy y' hy' j hj hyy
    simp only [A₀, A₁, Multiset.mem_map, Finset.mem_val, Finset.mem_compl] at hy hy'
    obtain ⟨a, haS, rfl⟩ := hy
    obtain ⟨b, hbS, rfl⟩ := hy'
    rw [hg a (hSL haS)] at hyy
    have hb' : x b = B (c0 + ((g a - j : ℤ) : ℝ)) := by
      have e := congrArg (fun y => y.nu (-(j : ℂ))) hyy
      simp only [B, IrrGL.nu_nu] at e
      rw [add_neg_cancel, IrrGL.nu_zero] at e
      rw [← e]
      simp only [B]
      congr 1
      push_cast
      ring
    have hbL : b ∈ L := Finset.mem_filter.mpr ⟨Finset.mem_univ _, g a - j, hb'⟩
    have h2 := hsep a haS b hbL hbS
    rw [hg b hbL] at hb'
    have e := hB_inj hb'
    have e' : (g b : ℝ) = g a - j := by
      push_cast at e
      linarith
    have e'' : g b = g a - j := by exact_mod_cast e'
    rw [e'', sub_sub_cancel] at h2
    linarith
  obtain ⟨h₀, h₁, u, w, hu, hw, huA, f, hf⟩ :=
    UpperTheory.Lit.Mix.front hG hBZ hZ k S.card n V σ A₀ A₁ (by rw [hA01]; exact hA) hA₀sum hsep'
  obtain ⟨z, hzt, hz1⟩ := exists_small k
  have hzpos := nabs_pos' k z
  let E : IrrGL k → ℝ := fun y => if hy : ∃ e : ℝ, y = B e then hy.choose else 0
  have hE : ∀ e, E (B e) = e := by
    intro e
    have hy : ∃ e' : ℝ, B e = B e' := ⟨e, rfl⟩
    simp only [E, dif_pos hy]
    exact (hB_inj hy.choose_spec).symm
  have hu_form : ∀ a, u a = B (E (u a)) := by
    intro a
    have hmem0 : u a ∈ A₀ := by
      rw [← huA]
      exact Multiset.mem_map_of_mem u (Finset.mem_univ_val a)
    simp only [A₀, Multiset.mem_map, Finset.mem_val] at hmem0
    obtain ⟨b, hb, hxb⟩ := hmem0
    rw [← hxb, hg b (hSL hb), hE]
  have hEsum : ∑ a, E (u a) = ∑ b ∈ S, (c0 + g b) := by
    have h1 : ∑ a, E (u a) = (A₀.map E).sum := by
      rw [← huA, Multiset.map_map]
      rfl
    rw [h1]
    simp only [A₀, Multiset.map_map]
    rw [← Finset.sum_eq_multiset_sum]
    apply Finset.sum_congr rfl
    intro b hb
    simp only [Function.comp_apply]
    rw [hg b (hSL hb), hE]
  let c : Fin h₀ → ℂ := fun a => (χ z : ℂ) * ((nabs k z ^ E (u a) : ℝ) : ℂ)
  have hsc : ∀ a, ScalarBy (u a) z (c a) := by
    intro a
    have key := scalarBy_nu χ hχ z (E (u a))
    have e := hu_form a
    simp only [B] at e
    rw [← e] at key
    exact key
  have hscal := scalarFull k h₀ S.card u hu z c hsc
  have hadm : IsAdmissible σ := (hBZ k).1 _ V σ hA.isSmooth hA.isIrreducible
  have hnt : Nontrivial V := Model.nontrivial_of_isIrreducible hA.isIrreducible
  have hb := UpperTheory.Lit.Mix.bound k S.card n V _ _ σ (prodIrr u hu) (prodIrr w hw) hadm hnt hU
    ⟨f, hf⟩ z hzt (∏ a, c a) hscal
  have hnorm : ‖(∏ a, c a) * ((absPow k (((S.card * n : ℕ) : ℂ) / 2)) z : ℂ)‖ =
      nabs k z ^ (∑ a, E (u a) + (S.card * n : ℝ) / 2) := by
    have e2 : (((S.card * n : ℕ) : ℂ) / 2) = ((((S.card * n : ℝ) / 2 : ℝ)) : ℂ) := by
      push_cast
      ring
    rw [e2, val_absPow_ofReal, norm_mul, norm_prod]
    simp only [c, norm_mul, hχu z, one_mul, Complex.norm_real, Real.norm_eq_abs]
    rw [Real.rpow_add hzpos, Real.rpow_sum_of_pos hzpos]
    congr 1
    · apply Finset.prod_congr rfl
      intro a _
      exact abs_of_pos (Real.rpow_pos_of_pos hzpos _)
    · exact abs_of_pos (Real.rpow_pos_of_pos hzpos _)
  rw [hnorm] at hb
  have hexp : 0 ≤ ∑ a, E (u a) + (S.card * n : ℝ) / 2 := by
    by_contra hneg
    push_neg at hneg
    have h3 := Real.one_lt_rpow_of_pos_of_lt_one_of_neg hzpos hz1 hneg
    linarith
  rw [hEsum, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul] at hexp
  have hsumR : 2 * ∑ b ∈ S, (g b : ℝ) ≤ (S.card : ℝ) * (S.card - 1) := by
    have h4 := hsum
    exact_mod_cast h4
  have hm : (1 : ℝ) ≤ S.card := by exact_mod_cast hSne.card_pos
  have hmn : (S.card : ℝ) + n + 1 ≤ t := by exact_mod_cast Nat.succ_le_of_lt hrt
  rw [hc0] at hexp
  nlinarith [mul_le_mul_of_nonneg_left hmn (by linarith : (0 : ℝ) ≤ S.card)]
