import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.GdegMetric

/- English proof (translation)
Set `P : Polynomial ℝ` to `∑ j ∈ Finset.range (N + 1), Polynomial.C (γ j) * Polynomial.X ^ j`. Establish `hP : P = Polynomial.C K`. Use `Polynomial.eq_of_infinite_eval_eq _ _ ?_` and prove the remaining obligations. Use `Set.infinite_of_injective_forall_mem (f := fun c : ℕ => (c : ℝ)) Nat.cast_injective fun c => ?_` and prove the remaining obligations. Simplify using `only [Set.mem_ofPred_eq, P, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]`.

Rewrite using `[← h c]`. Conclude with `Finset.sum_congr rfl fun j _ => mul_comm _ _`. Establish `e` using `congrArg (fun Q : Polynomial ℝ => Q.coeff m) hP`. Simplify using `only [P, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C] at e`. Rewrite `e` using `[Finset.sum_ite_eq (Finset.range (N + 1)) m, if_pos (Finset.mem_range.2 (by omega)), if_neg (by omega)]`.

Conclude with `e`.
-/
theorem coeff_eq_zero_of_const (N : ℕ) (γ : ℕ → ℝ) (K : ℝ)
    (h : ∀ c : ℕ, ∑ m ∈ Finset.range (N + 1), (c : ℝ) ^ m * γ m = K) {m : ℕ} (hm : 1 ≤ m) (hmN : m ≤ N) :
    γ m = 0 := by
  let P : Polynomial ℝ := ∑ j ∈ Finset.range (N + 1), Polynomial.C (γ j) * Polynomial.X ^ j
  have hP : P = Polynomial.C K := by
    refine Polynomial.eq_of_infinite_eval_eq _ _ ?_
    refine Set.infinite_of_injective_forall_mem (f := fun c : ℕ => (c : ℝ)) Nat.cast_injective fun c => ?_
    simp only [Set.mem_ofPred_eq, P, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X]
    rw [← h c]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have e := congrArg (fun Q : Polynomial ℝ => Q.coeff m) hP
  simp only [P, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C] at e
  rw [Finset.sum_ite_eq (Finset.range (N + 1)) m, if_pos (Finset.mem_range.2 (by omega)),
    if_neg (by omega)] at e
  exact e

/- English proof (translation)
Rewrite using `[add_pow, Finset.mul_sum, map_sum]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Establish `e : A * ((MvPolynomial.C c * x) ^ m * y ^ (n - m) * (n.choose m : MvPolynomial ι ℝ)) = (c ^ m * (n.choose m : ℝ)) • (A * x ^ m * y ^ (n - m))`. Rewrite using `[MvPolynomial.smul_eq_C_mul, map_mul, map_pow, map_natCast, mul_pow, ← map_pow]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e, map_smul, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem map_mul_add_pow {ι : Type} (Φ : MvPolynomial ι ℝ →ₗ[ℝ] ℝ) (A x y : MvPolynomial ι ℝ) (c : ℝ) (n : ℕ) :
    Φ (A * (MvPolynomial.C c * x + y) ^ n) =
      ∑ m ∈ Finset.range (n + 1), c ^ m * ((n.choose m : ℝ) * Φ (A * x ^ m * y ^ (n - m))) := by
  rw [add_pow, Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  have e : A * ((MvPolynomial.C c * x) ^ m * y ^ (n - m) * (n.choose m : MvPolynomial ι ℝ)) =
      (c ^ m * (n.choose m : ℝ)) • (A * x ^ m * y ^ (n - m)) := by
    rw [MvPolynomial.smul_eq_C_mul, map_mul, map_pow, map_natCast, mul_pow, ← map_pow]
    ring
  rw [e, map_smul, smul_eq_mul]
  ring

end GlobalTheory.GdegMetric

namespace GlobalTheory.GdegMetric

open MvPolynomial HermLB

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k}

/- English proof (translation)
Simplify using `[lin, Pi.single_apply, apply_ite, ite_mul]`.
-/
theorem lin_single' {ι : Type} [Fintype ι] [DecidableEq ι] (i : ι) :
    (lin fun j => (((Pi.single i 1 : ι → ℤ) j : ℤ) : ℝ)) = MvPolynomial.X i := by
  simp [lin, Pi.single_apply, apply_ite, ite_mul]

/- English proof (translation)
Introduce `i y y' h hy` and use `congrArg (c * ·) (hc σ σ' i y y' h hy)`.
-/
theorem isConj_const_mul {u : ∀ σ : k →+* ℂ, CxPts p σ → ℝ}
    (hc : ∀ σ σ', (Weight.ofFun (u σ)).IsConj (Weight.ofFun (u σ'))) (c : ℝ) (σ σ' : k →+* ℂ) :
    (Weight.ofFun fun y => c * u σ y).IsConj (Weight.ofFun fun y => c * u σ' y) :=
  fun i y y' h hy => congrArg (c * ·) (hc σ σ' i y y' h hy)

/- English proof (translation)
Rewrite using `[← icls_tens, icls_eq_iff.2 (isometric_tens_fnB _ v hv hd)]`. Conclude with `icls_eq_iff.2 (isometric_of_eqOn fun σ _ y _ => (e σ y).symm)`.
-/
theorem icls_fnB_sum {u v w : ∀ σ : k →+* ℂ, CxPts p σ → ℝ} (hu hc hv hd hw he) (e : ∀ σ y, w σ y = u σ y + v σ y) :
    (fnB w hw he).icls = (fnB u hu hc).icls + (fnB v hv hd).icls := by
  rw [← icls_tens, icls_eq_iff.2 (isometric_tens_fnB _ v hv hd)]
  exact icls_eq_iff.2 (isometric_of_eqOn fun σ _ y _ => (e σ y).symm)

/- English proof (translation)
Establish `key (m : ℤ)` using `icls_fnB_sum (p := p) (w := fun σ y => ((m + 1 : ℤ) : ℝ) * u σ y) (u := fun σ y => (m : ℝ) * u σ y) (fun σ y => (hu σ y).const_mul _) (isConj_const_mul hc _) hu hc (fun σ y => (hu σ y).const_mul _) (isConj_const_mul hc _) fun σ y => by push_cast; ring`. Proceed by induction on `n using Int.induction_on with`. Consider the case `zero`. Use `icls_fnB_sum (p := p) (w := u) (u := fun σ y => ((0 : ℤ) : ℝ) * u σ y) (fun σ y => (hu σ y).const_mul _) (isConj_const_mul hc _) hu hc hu hc fun σ y => by push_cast; ring` as an intermediate fact. Rewrite using `[zero_smul]`.

Conclude with `right_eq_add.1 this`. Consider the case `succ n ih => rw [key, ih, add_smul, one_smul]`. Consider the case `pred n ih`. Use `key (-(n : ℤ) - 1)` as an intermediate fact. Simplify using `only [sub_add_cancel] at this`.

Rewrite using `[sub_smul, one_smul, ← ih, this, add_sub_cancel_right]`.
-/
theorem icls_fnB_zsmul {u : ∀ σ : k →+* ℂ, CxPts p σ → ℝ} (hu : ∀ σ y, CInfAt (u σ) y)
    (hc : ∀ σ σ', (Weight.ofFun (u σ)).IsConj (Weight.ofFun (u σ'))) (n : ℤ) :
    (fnB (fun σ y => (n : ℝ) * u σ y) (fun σ y => (hu σ y).const_mul _) (isConj_const_mul hc _)).icls =
      n • (fnB u hu hc).icls := by
  have key (m : ℤ) := icls_fnB_sum (p := p) (w := fun σ y => ((m + 1 : ℤ) : ℝ) * u σ y)
    (u := fun σ y => (m : ℝ) * u σ y)
    (fun σ y => (hu σ y).const_mul _) (isConj_const_mul hc _) hu hc (fun σ y => (hu σ y).const_mul _)
    (isConj_const_mul hc _) fun σ y => by push_cast; ring
  induction n using Int.induction_on with
  | zero =>
    have := icls_fnB_sum (p := p) (w := u) (u := fun σ y => ((0 : ℤ) : ℝ) * u σ y)
      (fun σ y => (hu σ y).const_mul _) (isConj_const_mul hc _) hu hc hu hc fun σ y => by push_cast; ring
    rw [zero_smul]
    exact right_eq_add.1 this
  | succ n ih => rw [key, ih, add_smul, one_smul]
  | pred n ih =>
    have := key (-(n : ℤ) - 1)
    simp only [sub_add_cancel] at this
    rw [sub_smul, one_smul, ← ih, this, add_sub_cancel_right]

/- English proof (translation)
Simplify using `only [chInt, HermLB.raise, Weight.chernInt, Weight.chernPart_addFn_const]`.
-/
theorem chInt_raise_const (N : HermLB p) (t : ℝ) (hu : ∀ σ (y : CxPts p σ), CInfAt (fun _ => t) y) (hc) (D : ℕ)
    (f : ∀ σ : k →+* ℂ, CxPts p σ → ℝ) :
    chInt (N.raise (fun _ _ => t) hu hc) D f = chInt N D f := by
  simp only [chInt, HermLB.raise, Weight.chernInt, Weight.chernPart_addFn_const]

end GlobalTheory.GdegMetric

namespace GlobalTheory.GdegMetric

open MvPolynomial HermLB

/- English proof (translation)
Introduce `HC k _ S _ p D hX L u`. Set `one : ∀ σ : k →+* ℂ, CxPts p σ → ℝ` to `fun _ _ => 1`. Establish `h1 : ∀ σ (y : CxPts p σ), CInfAt (one σ) y` using `fun σ y => cInfAt_const 1 y`. Establish `hc1 : ∀ σ σ', (Weight.ofFun (one σ)).IsConj (Weight.ofFun (one σ'))` using `fun _ _ _ _ _ _ _ => rfl`. Set `T : HermLB p` to `fnB one h1 hc1`.

Set `U : HermLB p` to `fnB u.u u.cInf u.conj`. Set `G : Fin 3 → HermLB p` to `![T, L, U]`. Take `⟨Φ, hΦ⟩` from `((HC.arExists k S p D hX).2 _ G).1`. Set `eA : Option (Fin 3) → Fin 3` to `fun o => o.elim 2 id`. Establish `hA : IsArFun (fun o : Option (Fin 3) => o.elim U G) D (Φ ∘ₗ (MvPolynomial.aeval fun o => (MvPolynomial.X (eA o) : MvPolynomial (Fin 3) ℝ)).toLinearMap)`.

Use `((HC.arIso k S p D hX).2 _ G Φ hΦ).2.2 (Option (Fin 3)) (fun o => o.elim U G) (fun o => Pi.single (eA o) 1) fun o => by` as an intermediate fact. Break down `o with _ | j` into its components or cases. Conclude with `isometric_comb_single G 2`. Conclude with `isometric_comb_single G j`. Simplify `this` using `only [lin_single']`.

Set `eB : Option (Fin 2) → Fin 3` to `fun o => o.elim 0 Fin.succ`. Establish `hB : IsArFun (fun o : Option (Fin 2) => o.elim T ![L, U]) D (Φ ∘ₗ (MvPolynomial.aeval fun o => (MvPolynomial.X (eB o) : MvPolynomial (Fin 3) ℝ)).toLinearMap)`. Use `((HC.arIso k S p D hX).2 _ G Φ hΦ).2.2 (Option (Fin 2)) (fun o => o.elim T ![L, U]) (fun o => Pi.single (eB o) 1) fun o => by` as an intermediate fact. Break down `o with _ | j` into its components or cases. Conclude with `isometric_comb_single G 0`.

Use `fin_cases j`. Conclude with `isometric_comb_single G 1`. Conclude with `isometric_comb_single G 2`. Simplify `this` using `only [lin_single']`. Establish `chA : ∀ c b : ℤ, Φ (X 2 * (C (c : ℝ) * X 0 + (X 1 + C (b : ℝ) * X 2)) ^ D) = 1 / 2 * chInt (comb G ![c, 1, b]) D u.u`.

Introduce `c b`. Use `HC.arChange k S p D hX (Fin 3) G u.u u.cInf u.conj _ hA ![c, 1, b]` as an intermediate fact. Rewrite `this` using `[LinearMap.comp_apply, AlgHom.toLinearMap_apply]`. Rewrite using `[← this]`. Use `congr 1`.

Simplify using `[lin, Fin.sum_univ_three, MvPolynomial.aeval_rename, MvPolynomial.algebraMap_eq, eA]`. Expand and normalize the polynomial expressions, which then agree. Establish `chB : ∀ b : ℤ, Φ (X 0 * (X 1 + C (b : ℝ) * X 2) ^ D) = 1 / 2 * gdeg (comb ![L, U] ![1, b]) D`. Introduce `b`. Use `HC.arChange k S p D hX (Fin 2) ![L, U] one h1 hc1 _ hB ![1, b]` as an intermediate fact.

Rewrite `this` using `[LinearMap.comp_apply, AlgHom.toLinearMap_apply]`. Rewrite using `[gdeg, ← this]`. Use `congr 1`. Simplify using `[lin, Fin.sum_univ_two, MvPolynomial.aeval_rename, MvPolynomial.algebraMap_eq, eB]`. Establish `iso : ∀ c b : ℤ, (comb G ![c, 1, b]).Isometric ((comb ![L, U] ![1, b]).raise (fun _ _ => (c : ℝ) * 1) (fun σ y => cInfAt_const _ y) (fun _ _ _ _ _ _ _ => rfl))`.

Introduce `c b`. Use `Isometric.trans (icls_eq_iff.1 ?_) (isometric_tens_fnB _ _ _ _)` and prove the remaining obligations. Rewrite using `[icls_tens]`. Establish `e : (fnB (p` using `p) (fun _ _ => (c : ℝ) * 1) (fun σ y => cInfAt_const _ y) (fun _ _ _ _ _ _ _ => rfl)).icls = c • T.icls := icls_fnB_zsmul h1 hc1 c`. Rewrite using `[e, icls_comb, icls_comb, Fin.sum_univ_three, Fin.sum_univ_two]`.

Simplify using `[G]`. Normalize the expressions using the abelian group laws. Establish `hind : ∀ c b : ℤ, chInt (comb G ![c, 1, b]) D u.u = chInt (comb G ![0, 1, b]) D u.u`. Introduce `c b`. Rewrite using `[(iso c b).chInt_eq, (iso 0 b).chInt_eq]`.

Conclude with `(chInt_raise_const _ _ _ _ _ _).trans (chInt_raise_const _ _ _ _ _ _).symm`. Establish `i1 : (comb ![L, U] ![1, 1]).Isometric (up L u)` using `icls_eq_iff.1 (by`. Rewrite using `[← icls_eq_iff.2 (isometric_tens_fnB L u.u u.cInf u.conj), icls_tens, icls_comb, Fin.sum_univ_two]`. Simplify using `[U])`. Establish `i0 : (comb ![L, U] ![1, 0]).Isometric L` using `icls_eq_iff.1 (by`.

Rewrite using `[icls_comb, Fin.sum_univ_two]`. Use the proof step `simp)`. Rewrite using `[← i1.gdeg_eq, ← i0.gdeg_eq]`. Establish `e1` using `chB 1`. Establish `e0` using `chB 0`.

Consider the cases of `D with`. Consider the case `zero`. Simplify using `only [pow_zero, mul_one] at e1 e0`. Combine the linear equalities and inequalities to obtain the conclusion. Consider the case `succ d`.

Establish `s1 : ∀ b : ℤ, Φ (X 2 * X 0 * (X 1 + C (b : ℝ) * X 2) ^ d) = 0`. Introduce `b`. Establish `h` using `coeff_eq_zero_of_const (d + 1) (fun m => ((d + 1).choose m : ℝ) * Φ (X 2 * X 0 ^ m * (X 1 + C (b : ℝ) * X 2) ^ (d + 1 - m))) (1 / 2 * chInt (comb G ![0, 1, b]) (d + 1) u.u) (fun c => by beta_reduce`. Rewrite using `[← map_mul_add_pow, ← hind c b, ← chA c b]`. Use `push_cast`.

Use the proof step `rfl) (le_refl 1) (by omega)`. Simplify using `only [Nat.choose_one_right, pow_one, Nat.add_sub_cancel] at h`. Break down `mul_eq_zero.1 h with h | h` into its components or cases. Conclude with `absurd h (by positivity)`. Conclude with `h`.

Establish `s2 : ∀ m ≤ d, Φ (X 2 * X 0 * X 2 ^ m * X 1 ^ (d - m)) = 0`. Introduce `m hm`. Establish `hs : ∀ c : ℕ, ∑ j ∈ Finset.range (d + 1), (c : ℝ) ^ j * ((d.choose j : ℝ) * Φ (X 2 * X 0 * X 2 ^ j * X 1 ^ (d - j))) = 0`. Introduce `c`. Rewrite using `[← map_mul_add_pow]`.

Use `s1 c` as an intermediate fact. Rewrite `this` using `[add_comm]`. Move the coercions through the operations in `at this`. Conclude with `this`. Break down `Nat.eq_zero_or_pos m with rfl | hm0` into its components or cases.

Use `hs 0` as an intermediate fact. Rewrite `this` using `[Finset.sum_range_succ']`. Simplify using `using this`. Establish `h` using `coeff_eq_zero_of_const d _ 0 hs hm0 hm`. Break down `mul_eq_zero.1 h with h | h` into its components or cases.

Conclude with `absurd h (by exact_mod_cast (Nat.choose_pos hm).ne')`. Conclude with `h`. Establish `ex` using `map_mul_add_pow Φ (X 0) (X 2) (X 1) 1 (d + 1)`. Rewrite `ex` using `[Finset.sum_range_succ']`. Establish `hz : ∀ i ∈ Finset.range (d + 1), (1 : ℝ) ^ (i + 1) * (((d + 1).choose (i + 1) : ℝ) * Φ (X 0 * X 2 ^ (i + 1) * X 1 ^ (d + 1 - (i + 1)))) = 0`.

Introduce `i hi`. Establish `hi' : i ≤ d` using `Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)`. Rewrite using `[Nat.add_sub_add_right, show (X 0 * X 2 ^ (i + 1) * X 1 ^ (d - i) : MvPolynomial (Fin 3) ℝ) = X 2 * X 0 * X 2 ^ i * X 1 ^ (d - i) by ring, s2 i hi', mul_zero, mul_zero]`. Rewrite `ex` using `[Finset.sum_eq_zero hz, zero_add]`. Establish `e1' : Φ (X 0 * (C 1 * X 2 + X 1) ^ (d + 1)) = 1 / 2 * gdeg (comb ![L, U] ![1, 1]) (d + 1)`.

Rewrite using `[← e1, add_comm]`. Use `push_cast`. Both sides reduce to the same expression. Establish `e0' : Φ (X 0 * X 1 ^ (d + 1)) = 1 / 2 * gdeg (comb ![L, U] ![1, 0]) (d + 1)`. Rewrite using `[← e0]`.

Simplify using the standard rewrite rules. Simplify using `only [pow_zero, one_mul, Nat.choose_zero_right, Nat.cast_one, mul_one, Nat.sub_zero] at ex`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem gdeg_up : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k)
    (D : ℕ), IsArithVar p D → ∀ (L : HermLB p) (u : SmFn p), gdeg (up L u) D = gdeg L D := by
  intro HC k _ S _ p D hX L u
  classical
  let one : ∀ σ : k →+* ℂ, CxPts p σ → ℝ := fun _ _ => 1
  have h1 : ∀ σ (y : CxPts p σ), CInfAt (one σ) y := fun σ y => cInfAt_const 1 y
  have hc1 : ∀ σ σ', (Weight.ofFun (one σ)).IsConj (Weight.ofFun (one σ')) := fun _ _ _ _ _ _ _ => rfl
  let T : HermLB p := fnB one h1 hc1
  let U : HermLB p := fnB u.u u.cInf u.conj
  let G : Fin 3 → HermLB p := ![T, L, U]
  obtain ⟨Φ, hΦ⟩ := ((HC.arExists k S p D hX).2 _ G).1
  let eA : Option (Fin 3) → Fin 3 := fun o => o.elim 2 id
  have hA : IsArFun (fun o : Option (Fin 3) => o.elim U G) D
      (Φ ∘ₗ (MvPolynomial.aeval fun o => (MvPolynomial.X (eA o) : MvPolynomial (Fin 3) ℝ)).toLinearMap) := by
    have := ((HC.arIso k S p D hX).2 _ G Φ hΦ).2.2 (Option (Fin 3)) (fun o => o.elim U G)
      (fun o => Pi.single (eA o) 1) fun o => by
        rcases o with _ | j
        · exact isometric_comb_single G 2
        · exact isometric_comb_single G j
    simpa only [lin_single'] using this
  let eB : Option (Fin 2) → Fin 3 := fun o => o.elim 0 Fin.succ
  have hB : IsArFun (fun o : Option (Fin 2) => o.elim T ![L, U]) D
      (Φ ∘ₗ (MvPolynomial.aeval fun o => (MvPolynomial.X (eB o) : MvPolynomial (Fin 3) ℝ)).toLinearMap) := by
    have := ((HC.arIso k S p D hX).2 _ G Φ hΦ).2.2 (Option (Fin 2)) (fun o => o.elim T ![L, U])
      (fun o => Pi.single (eB o) 1) fun o => by
        rcases o with _ | j
        · exact isometric_comb_single G 0
        · fin_cases j
          · exact isometric_comb_single G 1
          · exact isometric_comb_single G 2
    simpa only [lin_single'] using this
  have chA : ∀ c b : ℤ, Φ (X 2 * (C (c : ℝ) * X 0 + (X 1 + C (b : ℝ) * X 2)) ^ D) =
      1 / 2 * chInt (comb G ![c, 1, b]) D u.u := by
    intro c b
    have := HC.arChange k S p D hX (Fin 3) G u.u u.cInf u.conj _ hA ![c, 1, b]
    rw [LinearMap.comp_apply, AlgHom.toLinearMap_apply] at this
    rw [← this]
    congr 1
    simp [lin, Fin.sum_univ_three, MvPolynomial.aeval_rename, MvPolynomial.algebraMap_eq, eA]
    ring
  have chB : ∀ b : ℤ, Φ (X 0 * (X 1 + C (b : ℝ) * X 2) ^ D) = 1 / 2 * gdeg (comb ![L, U] ![1, b]) D := by
    intro b
    have := HC.arChange k S p D hX (Fin 2) ![L, U] one h1 hc1 _ hB ![1, b]
    rw [LinearMap.comp_apply, AlgHom.toLinearMap_apply] at this
    rw [gdeg, ← this]
    congr 1
    simp [lin, Fin.sum_univ_two, MvPolynomial.aeval_rename, MvPolynomial.algebraMap_eq, eB]

  have iso : ∀ c b : ℤ, (comb G ![c, 1, b]).Isometric ((comb ![L, U] ![1, b]).raise (fun _ _ => (c : ℝ) * 1)
      (fun σ y => cInfAt_const _ y) (fun _ _ _ _ _ _ _ => rfl)) := by
    intro c b
    refine Isometric.trans (icls_eq_iff.1 ?_) (isometric_tens_fnB _ _ _ _)
    rw [icls_tens]
    have e : (fnB (p := p) (fun _ _ => (c : ℝ) * 1) (fun σ y => cInfAt_const _ y)
        (fun _ _ _ _ _ _ _ => rfl)).icls = c • T.icls := icls_fnB_zsmul h1 hc1 c
    rw [e, icls_comb, icls_comb, Fin.sum_univ_three, Fin.sum_univ_two]
    simp [G]
    abel
  have hind : ∀ c b : ℤ, chInt (comb G ![c, 1, b]) D u.u = chInt (comb G ![0, 1, b]) D u.u := by
    intro c b
    rw [(iso c b).chInt_eq, (iso 0 b).chInt_eq]
    exact (chInt_raise_const _ _ _ _ _ _).trans (chInt_raise_const _ _ _ _ _ _).symm
  have i1 : (comb ![L, U] ![1, 1]).Isometric (up L u) := icls_eq_iff.1 (by
    rw [← icls_eq_iff.2 (isometric_tens_fnB L u.u u.cInf u.conj), icls_tens, icls_comb, Fin.sum_univ_two]
    simp [U])
  have i0 : (comb ![L, U] ![1, 0]).Isometric L := icls_eq_iff.1 (by
    rw [icls_comb, Fin.sum_univ_two]
    simp)
  rw [← i1.gdeg_eq, ← i0.gdeg_eq]
  have e1 := chB 1
  have e0 := chB 0
  cases D with
  | zero =>
    simp only [pow_zero, mul_one] at e1 e0
    linarith
  | succ d =>
    have s1 : ∀ b : ℤ, Φ (X 2 * X 0 * (X 1 + C (b : ℝ) * X 2) ^ d) = 0 := by
      intro b
      have h := coeff_eq_zero_of_const (d + 1)
        (fun m => ((d + 1).choose m : ℝ) * Φ (X 2 * X 0 ^ m * (X 1 + C (b : ℝ) * X 2) ^ (d + 1 - m)))
        (1 / 2 * chInt (comb G ![0, 1, b]) (d + 1) u.u) (fun c => by
          beta_reduce
          rw [← map_mul_add_pow, ← hind c b, ← chA c b]
          push_cast
          rfl) (le_refl 1) (by omega)
      simp only [Nat.choose_one_right, pow_one, Nat.add_sub_cancel] at h
      rcases mul_eq_zero.1 h with h | h
      · exact absurd h (by positivity)
      · exact h
    have s2 : ∀ m ≤ d, Φ (X 2 * X 0 * X 2 ^ m * X 1 ^ (d - m)) = 0 := by
      intro m hm
      have hs : ∀ c : ℕ, ∑ j ∈ Finset.range (d + 1),
          (c : ℝ) ^ j * ((d.choose j : ℝ) * Φ (X 2 * X 0 * X 2 ^ j * X 1 ^ (d - j))) = 0 := by
        intro c
        rw [← map_mul_add_pow]
        have := s1 c
        rw [add_comm] at this
        push_cast at this
        exact this
      rcases Nat.eq_zero_or_pos m with rfl | hm0
      · have := hs 0
        rw [Finset.sum_range_succ'] at this
        simpa using this
      · have h := coeff_eq_zero_of_const d _ 0 hs hm0 hm
        rcases mul_eq_zero.1 h with h | h
        · exact absurd h (by exact_mod_cast (Nat.choose_pos hm).ne')
        · exact h
    have ex := map_mul_add_pow Φ (X 0) (X 2) (X 1) 1 (d + 1)
    rw [Finset.sum_range_succ'] at ex
    have hz : ∀ i ∈ Finset.range (d + 1), (1 : ℝ) ^ (i + 1) * (((d + 1).choose (i + 1) : ℝ) *
        Φ (X 0 * X 2 ^ (i + 1) * X 1 ^ (d + 1 - (i + 1)))) = 0 := by
      intro i hi
      have hi' : i ≤ d := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
      rw [Nat.add_sub_add_right, show (X 0 * X 2 ^ (i + 1) * X 1 ^ (d - i) : MvPolynomial (Fin 3) ℝ) =
        X 2 * X 0 * X 2 ^ i * X 1 ^ (d - i) by ring, s2 i hi', mul_zero, mul_zero]
    rw [Finset.sum_eq_zero hz, zero_add] at ex
    have e1' : Φ (X 0 * (C 1 * X 2 + X 1) ^ (d + 1)) = 1 / 2 * gdeg (comb ![L, U] ![1, 1]) (d + 1) := by
      rw [← e1, add_comm]
      push_cast
      rfl
    have e0' : Φ (X 0 * X 1 ^ (d + 1)) = 1 / 2 * gdeg (comb ![L, U] ![1, 0]) (d + 1) := by
      rw [← e0]
      simp
    simp only [pow_zero, one_mul, Nat.choose_zero_right, Nat.cast_one, mul_one, Nat.sub_zero] at ex
    linarith

end GlobalTheory.GdegMetric
