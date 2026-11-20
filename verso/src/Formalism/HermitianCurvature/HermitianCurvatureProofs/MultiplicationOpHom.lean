import Formalism.HermitianCurvature.StatementM

open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset

namespace Formalism.FourierDecayAlt.P.Mx1

/- English proof (translation)
Simplify using `[coord]`.
-/
theorem coord_ne (r : ℕ) (v : Var r) : coord v ≠ 0 := by
  simp [coord]

/- English proof (translation)
Simplify using `[vz, vzb]`.
-/
theorem vz_ne {r : ℕ} : (vz : Var r) ≠ vzb := by
  simp [vz, vzb]

/- English proof (translation)
Introduce `γ hγ`. Rewrite `hγ`, the goal using `[HahnSeries.mem_support]`. Introduce `h`. Apply `hγ` to reduce the goal to its premises. Use `show ((ofLex γ v : ℤ) : ℂ) * f.coeff γ = 0`.

Rewrite using `[h, mul_zero]`.
-/
theorem euler_support {r : ℕ} (v : Var r) (f : Fn r) : (euler v f).support ⊆ f.support := by
  intro γ hγ
  rw [HahnSeries.mem_support] at hγ ⊢
  intro h
  apply hγ
  show ((ofLex γ v : ℤ) : ℂ) * f.coeff γ = 0
  rw [h, mul_zero]

/- English proof (translation)
Unfold `sc`. Use extensionality with `i j`. Rewrite using `[Matrix.star_apply]`. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality.

Simplify using the standard rewrite rules. Simplify using `[Matrix.scalar_apply, Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ (Ne.symm h)]`.
-/
theorem star_sc (P : Par) (w : Pr P.r) : star (sc P w) = sc P (star w) := by
  unfold sc
  ext i j
  rw [Matrix.star_apply]
  by_cases h : i = j
  · subst h
    simp
  · simp [Matrix.scalar_apply, Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ (Ne.symm h)]

end Formalism.FourierDecayAlt.P.Mx1

namespace Formalism.FourierDecayAlt.P

open Mx1

/- English proof (translation)
Introduce `r f g z`. Apply the tactic sequence `refine ⟨?_, ?_, ?_, ?_⟩ <;> refine LinearMap.ext fun x => ?_ <;>`. Simplify using `[mulOp, mul_assoc, add_mul, Algebra.smul_def]`.
-/
theorem multiplication_op_hom : Formalism.FourierDecayAlt.M.MulOpHom := by
  intro r f g z
  refine ⟨?_, ?_, ?_, ?_⟩ <;> refine LinearMap.ext fun x => ?_ <;>
    simp [mulOp, mul_assoc, add_mul, Algebra.smul_def]

/- English proof (translation)
Introduce `r v f g`. Establish `hc : ∀ (v : Var r) (h : Fn r) (γ : Expo r), (euler v h).coeff γ = ((ofLex γ v : ℤ) : ℂ) * h.coeff γ` using `fun _ _ _ => rfl`. Use extensionality with `γ`. Rewrite using `[hc, HahnSeries.coeff_add, HahnSeries.coeff_mul_left' f.isPWO_support (Mx1.euler_support v f), HahnSeries.coeff_mul_right' g.isPWO_support (Mx1.euler_support v g), HahnSeries.coeff_mul, Finset.mul_sum, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun ij hij => ?_` and prove the remaining obligations.

Take `⟨-, -, hsum⟩` from `Finset.mem_addAntidiagonal.1 hij`. Rewrite using `[hc, hc, ← hsum, ofLex_add, Pi.add_apply]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem euler_leibniz : Formalism.FourierDecayAlt.M.EulerLeibniz := by
  intro r v f g
  have hc : ∀ (v : Var r) (h : Fn r) (γ : Expo r), (euler v h).coeff γ = ((ofLex γ v : ℤ) : ℂ) * h.coeff γ :=
    fun _ _ _ => rfl
  ext γ
  rw [hc, HahnSeries.coeff_add, HahnSeries.coeff_mul_left' f.isPWO_support (Mx1.euler_support v f),
    HahnSeries.coeff_mul_right' g.isPWO_support (Mx1.euler_support v g), HahnSeries.coeff_mul,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ij hij => ?_
  obtain ⟨-, -, hsum⟩ := Finset.mem_addAntidiagonal.1 hij
  rw [hc, hc, ← hsum, ofLex_add, Pi.add_apply]
  push_cast
  ring

/- English proof (translation)
Introduce `r v w z`. Establish `hc : ∀ (v : Var r) (h : Fn r) (γ : Expo r), (euler v h).coeff γ = ((ofLex γ v : ℤ) : ℂ) * h.coeff γ` using `fun _ _ _ => rfl`. Prove the components needed by the constructor for the conclusion. Use extensionality with `γ`. Rewrite using `[hc]`.

Distinguish the cases in `hvw : v = w`. Substitute `hvw` using the available equality. Rewrite using `[if_pos rfl]`. Simplify using `only [coord, HahnSeries.coeff_single]`. Use `split_ifs with hγ`.

Substitute `hγ` using the available equality. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Rewrite using `[if_neg hvw]`. Simplify using `only [coord, HahnSeries.coeff_single, HahnSeries.coeff_zero]`.

Use `split_ifs with hγ`. Substitute `hγ` using the available equality. Simplify using `[Pi.single_apply, hvw]`. Simplify using the standard rewrite rules. Use extensionality with `γ`.

Rewrite using `[hc]`. Simplify using `only [HahnSeries.algebraMap_apply, HahnSeries.C_apply, HahnSeries.coeff_single, HahnSeries.coeff_zero, Algebra.algebraMap_self, RingHom.id_apply]`. Use `split_ifs with hγ`. Substitute `hγ` using the available equality. Simplify using the standard rewrite rules.

Use `left`. Both sides reduce to the same expression. Simplify using the standard rewrite rules.
-/
theorem euler_coordinates : Formalism.FourierDecayAlt.M.EulerCoord := by
  intro r v w z
  have hc : ∀ (v : Var r) (h : Fn r) (γ : Expo r), (euler v h).coeff γ = ((ofLex γ v : ℤ) : ℂ) * h.coeff γ :=
    fun _ _ _ => rfl
  constructor
  · ext γ
    rw [hc]
    by_cases hvw : v = w
    · subst hvw
      rw [if_pos rfl]
      simp only [coord, HahnSeries.coeff_single]
      split_ifs with hγ
      · subst hγ
        simp
      · simp
    · rw [if_neg hvw]
      simp only [coord, HahnSeries.coeff_single, HahnSeries.coeff_zero]
      split_ifs with hγ
      · subst hγ
        simp [Pi.single_apply, hvw]
      · simp
  · ext γ
    rw [hc]
    simp only [HahnSeries.algebraMap_apply, HahnSeries.C_apply, HahnSeries.coeff_single,
      HahnSeries.coeff_zero, Algebra.algebraMap_self, RingHom.id_apply]
    split_ifs with hγ
    · subst hγ
      simp
      left
      rfl
    · simp

/- English proof (translation)
Introduce `r v w`. Establish `hc : ∀ (v : Var r) (h : Fn r) (γ : Expo r), (euler v h).coeff γ = ((ofLex γ v : ℤ) : ℂ) * h.coeff γ` using `fun _ _ _ => rfl`. Use `LinearMap.ext fun f => ?_` and prove the remaining obligations. Use extensionality with `γ`. Simplify using `only [Module.End.mul_apply, hc]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem euler_commute : Formalism.FourierDecayAlt.M.EulerComm := by
  intro r v w
  have hc : ∀ (v : Var r) (h : Fn r) (γ : Expo r), (euler v h).coeff γ = ((ofLex γ v : ℤ) : ℂ) * h.coeff γ :=
    fun _ _ _ => rfl
  refine LinearMap.ext fun f => ?_
  ext γ
  simp only [Module.End.mul_apply, hc]
  ring

/- English proof (translation)
Introduce `r v f`. Use `LinearMap.ext fun g => ?_` and prove the remaining obligations. Simplify using `only [Module.End.mul_apply, LinearMap.add_apply, mulOp, LinearMap.mulLeft_apply]`. Rewrite using `[euler_leibniz r v f g, add_comm]`.
-/
theorem eulerMul_statement : Formalism.FourierDecayAlt.M.EulerMul := by
  intro r v f
  refine LinearMap.ext fun g => ?_
  simp only [Module.End.mul_apply, LinearMap.add_apply, mulOp, LinearMap.mulLeft_apply]
  rw [euler_leibniz r v f g, add_comm]

/- English proof (translation)
Introduce `r v TT`. Use `⟨coord_ne r v, fun h => ?_⟩` and prove the remaining obligations. Establish `he : (toLex (Pi.single vz 1) + toLex (Pi.single vzb 1) : Expo r) ≠ 0`. Introduce `h0`. Use `congrFun (congrArg ofLex h0) vz` as an intermediate fact.

Express the relevant statement in the definitionally equal form `((Pi.single vz (1 : ℤ) + Pi.single vzb 1 : Var r → ℤ) vz) = (0 : Var r → ℤ) vz at this`. Simplify using `[Pi.single_apply, vz_ne (r := r)] at this`. Establish `hc` using `congrArg (fun s : Fn r => s.coeff (toLex (Pi.single vz 1) + toLex (Pi.single vzb 1))) h`. Simplify using `[gg, coord, HahnSeries.single_mul_single, HahnSeries.algebraMap_apply, HahnSeries.C_apply, HahnSeries.coeff_single, he] at hc`.
-/
theorem function_nonzero : Formalism.FourierDecayAlt.M.FnNonzero := by
  intro r v TT
  refine ⟨coord_ne r v, fun h => ?_⟩
  have he : (toLex (Pi.single vz 1) + toLex (Pi.single vzb 1) : Expo r) ≠ 0 := by
    intro h0
    have := congrFun (congrArg ofLex h0) vz
    change ((Pi.single vz (1 : ℤ) + Pi.single vzb 1 : Var r → ℤ) vz) = (0 : Var r → ℤ) vz at this
    simp [Pi.single_apply, vz_ne (r := r)] at this
  have hc := congrArg (fun s : Fn r => s.coeff (toLex (Pi.single vz 1) + toLex (Pi.single vzb 1))) h
  simp [gg, coord, HahnSeries.single_mul_single, HahnSeries.algebraMap_apply, HahnSeries.C_apply,
    HahnSeries.coeff_single, he] at hc

/- English proof (translation)
Introduce `P`. Establish `key : ∀ w : Pr P.r, sc P w = 0 → w = 0`. Introduce `w h`. Use `congrFun (congrFun h (fun _ => 0)) (fun _ => 0)` as an intermediate fact. Simplify `this` using `[sc]`.

Use `⟨⟨⟨0, 1, fun h => ?_⟩⟩, fun f fb h => ?_⟩` and prove the remaining obligations. Establish `h1 : (1 : Pr P.r) = 0` using `key 1 (by unfold sc; rw [map_one]; exact h.symm)`. Establish `h2 : (1 : Op P.r) (1 : Fn P.r) = (0 : Op P.r) 1` using `congrArg (fun w : Pr P.r => (w.1 : Op P.r) (1 : Fn P.r)) h1`. Simplify using `at h2`. Establish `h1` using `key _ h`.

Establish `h2 : (mulOp f) (1 : Fn P.r) = (0 : Op P.r) 1` using `congrArg (fun w : Pr P.r => (w.1 : Op P.r) (1 : Fn P.r)) h1`. Simplify `h2` using `[mulOp]`.
-/
theorem model_nontrivial : Formalism.FourierDecayAlt.M.ModelNontrivial := by
  intro P
  have key : ∀ w : Pr P.r, sc P w = 0 → w = 0 := by
    intro w h
    have := congrFun (congrFun h (fun _ => 0)) (fun _ => 0)
    simpa [sc] using this
  refine ⟨⟨⟨0, 1, fun h => ?_⟩⟩, fun f fb h => ?_⟩
  · have h1 : (1 : Pr P.r) = 0 := key 1 (by unfold sc; rw [map_one]; exact h.symm)
    have h2 : (1 : Op P.r) (1 : Fn P.r) = (0 : Op P.r) 1 :=
      congrArg (fun w : Pr P.r => (w.1 : Op P.r) (1 : Fn P.r)) h1
    simp at h2
  · have h1 := key _ h
    have h2 : (mulOp f) (1 : Fn P.r) = (0 : Op P.r) 1 :=
      congrArg (fun w : Pr P.r => (w.1 : Op P.r) (1 : Fn P.r)) h1
    simpa [mulOp] using h2

/- English proof (translation)
Introduce `P`. Establish `hs : ∀ X Y : Op P.r, star (mk X Y) = mk Y X` using `fun X Y => rfl`. Establish `hneg : ∀ X Y : Op P.r, -(mk X Y : Pr P.r) = mk (-X) (-Y)` using `fun X Y => rfl`. Establish `mc : ∀ f g : Fn P.r, mulOp f * mulOp g = mulOp g * mulOp f` using `fun f g => by`. Use `LinearMap.ext fun x => ?_` and prove the remaining obligations.

Simplify using `only [mulOp, Module.End.mul_apply, LinearMap.mulLeft_apply, ← mul_assoc, mul_comm f g]`. Use `⟨fun l => ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Unfold `cA cbA`. Rewrite using `[star_sc]`. Both sides reduce to the same expression.

Unfold `ciA cbiA`. Rewrite using `[star_sc]`. Both sides reduce to the same expression. Unfold `pA pbA`. Rewrite using `[star_sc]`.

Unfold `sc`. Rewrite using `[← map_neg]`. Use `congr 1`. Unfold `pP pbP`. Rewrite using `[hs, hneg, neg_neg]`.

Unfold `zA zbA`. Rewrite using `[star_sc]`. Both sides reduce to the same expression. Unfold `ziA zbiA`. Rewrite using `[star_sc]`.

Both sides reduce to the same expression. Unfold `ggA`. Rewrite using `[star_sc]`. Both sides reduce to the same expression. Unfold `ggiA`.

Rewrite using `[star_sc]`. Both sides reduce to the same expression. Establish `e1 : star (dzP : Pr P.r) = -dzbP`. Unfold `dzP dzbP`. Rewrite using `[hs, hneg, neg_neg]`.

Establish `e2 : star (zbP : Pr P.r) = zP` using `rfl`. Establish `e3 : star (ggiP P.TT : Pr P.r) = ggiP P.TT` using `rfl`. Establish `e4 : (ggiP P.TT : Pr P.r) * zP = zP * ggiP P.TT`. Unfold `ggiP zP fnP M.mk`. Use `Prod.ext (mc _ _) ?_` and prove the remaining obligations.

Use `show MulOpposite.op _ * MulOpposite.op _ = MulOpposite.op _ * MulOpposite.op _`. Rewrite using `[← MulOpposite.op_mul, ← MulOpposite.op_mul, mc]`. Unfold `nabA nabsA`. Rewrite using `[Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]`. Use `congr 1`.

Use function extensionality and compare the values at `π`. Rewrite using `[Pi.star_apply, star_add, star_smul, star_mul, e1, e2, e3, e4, Complex.star_def, Complex.conj_ofReal]`.
-/
theorem star_generators : Formalism.FourierDecayAlt.M.StarGens := by
  intro P
  have hs : ∀ X Y : Op P.r, star (mk X Y) = mk Y X := fun X Y => rfl
  have hneg : ∀ X Y : Op P.r, -(mk X Y : Pr P.r) = mk (-X) (-Y) := fun X Y => rfl
  have mc : ∀ f g : Fn P.r, mulOp f * mulOp g = mulOp g * mulOp f := fun f g => by
    refine LinearMap.ext fun x => ?_
    simp only [mulOp, Module.End.mul_apply, LinearMap.mulLeft_apply, ← mul_assoc, mul_comm f g]
  refine ⟨fun l => ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · unfold cA cbA; rw [star_sc]; rfl
  · unfold ciA cbiA; rw [star_sc]; rfl
  · unfold pA pbA
    rw [star_sc]
    unfold sc
    rw [← map_neg]
    congr 1
    unfold pP pbP
    rw [hs, hneg, neg_neg]
  · unfold zA zbA; rw [star_sc]; rfl
  · unfold ziA zbiA; rw [star_sc]; rfl
  · unfold ggA; rw [star_sc]; rfl
  · unfold ggiA; rw [star_sc]; rfl
  · have e1 : star (dzP : Pr P.r) = -dzbP := by
      unfold dzP dzbP
      rw [hs, hneg, neg_neg]
    have e2 : star (zbP : Pr P.r) = zP := rfl
    have e3 : star (ggiP P.TT : Pr P.r) = ggiP P.TT := rfl
    have e4 : (ggiP P.TT : Pr P.r) * zP = zP * ggiP P.TT := by
      unfold ggiP zP fnP M.mk
      refine Prod.ext (mc _ _) ?_
      show MulOpposite.op _ * MulOpposite.op _ = MulOpposite.op _ * MulOpposite.op _
      rw [← MulOpposite.op_mul, ← MulOpposite.op_mul, mc]
    unfold nabA nabsA
    rw [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
    congr 1
    funext π
    rw [Pi.star_apply, star_add, star_smul, star_mul, e1, e2, e3, e4, Complex.star_def, Complex.conj_ofReal]

/- English proof (translation)
Introduce `P L hL`. Take `⟨-, -, -, -, -, -, hz, -, hzb, -, -, -, hn, hns, hT⟩` from `hL`. Establish `hS` using `star_generators P`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hz, hzb]`.

Conclude with `hS.2.1`. Rewrite using `[hn, hns]`. Conclude with `hS.2.2.2.2.2`. Rewrite using `[hT]`. Simplify using `[Complex.star_def, Complex.conj_ofReal]`.
-/
theorem level_star : Formalism.FourierDecayAlt.M.LevelStar := by
  intro P L hL
  obtain ⟨-, -, -, -, -, -, hz, -, hzb, -, -, -, hn, hns, hT⟩ := hL
  have hS := star_generators P
  refine ⟨?_, ?_, ?_⟩
  · rw [hz, hzb]
    exact hS.2.1
  · rw [hn, hns]
    exact hS.2.2.2.2.2
  · rw [hT]
    simp [Complex.star_def, Complex.conj_ofReal]

end Formalism.FourierDecayAlt.P
