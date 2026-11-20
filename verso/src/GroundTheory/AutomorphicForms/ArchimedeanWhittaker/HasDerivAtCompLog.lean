import Mathlib
import GroundTheory.AutomorphicForms.ArchimedeanWhittaker.Density
import GroundTheory.AutomorphicForms.ArchimedeanWhittaker.WronskianEqZeroOfModerate

namespace GroundTheory.Automorphic.ArchWhittaker

open Matrix NormedSpace Complex MeasureTheory Filter Topology Set
open scoped Matrix.Norms.L2Operator Real InnerProductSpace ContDiff

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (σ : UnitaryRep FiltrationCocycleLiftCriterion H)

noncomputable abbrev πσ : BanachRep FiltrationCocycleLiftCriterion H := BanachRep.ofUnitary σ

abbrev IsSm (v : H) : Prop := hGL2.IsSmoothVector (πσ σ) v

/- English proof (translation)
The claim follows from `σ.norm_map_le g`.
-/
theorem norm_πσ_le (g : FiltrationCocycleLiftCriterion) : ‖πσ σ g‖ ≤ 1 := σ.norm_map_le g

/- English proof (translation)
The claim follows from `hGL2.isSmoothVector_map (πσ σ) hv g`.
-/
theorem isSm_map {v : H} (hv : IsSm σ v) (g : FiltrationCocycleLiftCriterion) : IsSm σ (σ g v) :=
  hGL2.isSmoothVector_map (πσ σ) hv g

noncomputable abbrev dπ (X : gl2) (v : H) : H := hGL2.derivOp (πσ σ) X v

/- English proof (translation)
The claim follows from `hGL2.isSmoothVector_derivOp (πσ σ) hv X`.
-/
theorem isSm_dπ {v : H} (hv : IsSm σ v) (X : gl2) : IsSm σ (dπ σ X v) :=
  hGL2.isSmoothVector_derivOp (πσ σ) hv X

variable (l : hGL2.smoothVectors (πσ σ) →ₗ[ℂ] ℂ)

open Classical in

noncomputable def lT (x : H) : ℂ := if hx : IsSm σ x then l ⟨x, hx⟩ else 0

variable {σ l}

/- English proof (translation)
Rewrite using `[lT, dif_pos hx]`.
-/
theorem lT_of {x : H} (hx : IsSm σ x) : lT σ l x = l ⟨x, hx⟩ := by
  rw [lT, dif_pos hx]

/- English proof (translation)
Rewrite using `[lT_of hx, lT_of hy, lT_of ((hGL2.smoothVectors (πσ σ)).add_mem hx hy), ← map_add]`. Both sides reduce to the same expression.
-/
theorem lT_add {x y : H} (hx : IsSm σ x) (hy : IsSm σ y) :
    lT σ l (x + y) = lT σ l x + lT σ l y := by
  rw [lT_of hx, lT_of hy, lT_of ((hGL2.smoothVectors (πσ σ)).add_mem hx hy), ← map_add]; rfl

/- English proof (translation)
Rewrite using `[lT_of hx, lT_of ((hGL2.smoothVectors (πσ σ)).smul_mem c hx), ← smul_eq_mul, ← map_smul]`. Both sides reduce to the same expression.
-/
theorem lT_smul {x : H} (hx : IsSm σ x) (c : ℂ) : lT σ l (c • x) = c * lT σ l x := by
  rw [lT_of hx, lT_of ((hGL2.smoothVectors (πσ σ)).smul_mem c hx), ← smul_eq_mul, ← map_smul]; rfl

/- English proof (translation)
Rewrite using `[lT_of hx, lT_of hy, lT_of ((hGL2.smoothVectors (πσ σ)).sub_mem hx hy), ← map_sub]`. Both sides reduce to the same expression.
-/
theorem lT_sub {x y : H} (hx : IsSm σ x) (hy : IsSm σ y) :
    lT σ l (x - y) = lT σ l x - lT σ l y := by
  rw [lT_of hx, lT_of hy, lT_of ((hGL2.smoothVectors (πσ σ)).sub_mem hx hy), ← map_sub]; rfl

/- English proof (translation)
Rewrite using `[lT_of (hGL2.isSmoothVector_zero (πσ σ))]`. Conclude with `map_zero l`.
-/
theorem lT_zero : lT σ l 0 = 0 := by
  rw [lT_of (hGL2.isSmoothVector_zero (πσ σ))]
  exact map_zero l

variable (σ l)

noncomputable def Wt (u : H) (t : ℝ) : ℂ := lT σ l (σ (aT t) u)

variable {σ l}

/- English proof (translation)
Simplify using `only [Wt, map_add]`. Conclude with `lT_add (isSm_map σ hu _) (isSm_map σ hv _)`.
-/
theorem Wt_add {u v : H} (hu : IsSm σ u) (hv : IsSm σ v) (t : ℝ) :
    Wt σ l (u + v) t = Wt σ l u t + Wt σ l v t := by
  simp only [Wt, map_add]
  exact lT_add (isSm_map σ hu _) (isSm_map σ hv _)

/- English proof (translation)
Simplify using `only [Wt, map_smul]`. Conclude with `lT_smul (isSm_map σ hu _) c`.
-/
theorem Wt_smul {u : H} (hu : IsSm σ u) (c : ℂ) (t : ℝ) : Wt σ l (c • u) t = c * Wt σ l u t := by
  simp only [Wt, map_smul]
  exact lT_smul (isSm_map σ hu _) c

/- English proof (translation)
Simplify using `only [Wt, map_sub]`. Conclude with `lT_sub (isSm_map σ hu _) (isSm_map σ hv _)`.
-/
theorem Wt_sub {u v : H} (hu : IsSm σ u) (hv : IsSm σ v) (t : ℝ) :
    Wt σ l (u - v) t = Wt σ l u t - Wt σ l v t := by
  simp only [Wt, map_sub]
  exact lT_sub (isSm_map σ hu _) (isSm_map σ hv _)

/- English proof (translation)
Establish `key` using `hl.hasDerivAt_map_expG (norm_πσ_le σ) hu (aT t) lH`. Establish `e1 : (fun s : ℝ => l (hGL2.smoothMap (πσ σ) hu (aT t * hGL2.expG (s • lH)))) = fun s => Wt σ l u (t + s)`. Use function extensionality and compare the values at `s`. Rewrite using `[Wt, expG_lH, ← aT_add, lT_of (isSm_map σ hu _)]`. Both sides reduce to the same expression.

Establish `e2 : l (hGL2.smoothMap (πσ σ) (hGL2.isSmoothVector_derivOp (πσ σ) hu lH) (aT t)) = Wt σ l (dπ σ lH u) t`. Rewrite using `[Wt, lT_of (isSm_map σ (isSm_dπ σ hu lH) _)]`. Both sides reduce to the same expression. Rewrite `key` using `[e1, e2]`. Establish `key' : HasDerivAt (fun s : ℝ => Wt σ l u (t + s)) (Wt σ l (dπ σ lH u) t) (t - t)`.

Rewrite using `[sub_self]`. Conclude with `key`. Use `key'.comp_sub_const t t` as an intermediate fact. Use `this.congr_of_eventuallyEq (Eventually.of_forall fun s => ?_)` and prove the remaining obligations. Simplify using `only`.

Rewrite using `[add_sub_cancel]`.
-/
theorem hasDerivAt_Wt (hl : hGL2.IsSmoothContinuous (πσ σ) l) {u : H} (hu : IsSm σ u) (t : ℝ) :
    HasDerivAt (Wt σ l u) (Wt σ l (dπ σ lH u) t) t := by
  have key := hl.hasDerivAt_map_expG (norm_πσ_le σ) hu (aT t) lH
  have e1 : (fun s : ℝ => l (hGL2.smoothMap (πσ σ) hu (aT t * hGL2.expG (s • lH)))) =
      fun s => Wt σ l u (t + s) := by
    funext s
    rw [Wt, expG_lH, ← aT_add, lT_of (isSm_map σ hu _)]
    rfl
  have e2 : l (hGL2.smoothMap (πσ σ) (hGL2.isSmoothVector_derivOp (πσ σ) hu lH) (aT t)) =
      Wt σ l (dπ σ lH u) t := by
    rw [Wt, lT_of (isSm_map σ (isSm_dπ σ hu lH) _)]
    rfl
  rw [e1, e2] at key
  have key' : HasDerivAt (fun s : ℝ => Wt σ l u (t + s)) (Wt σ l (dπ σ lH u) t) (t - t) := by
    rw [sub_self]; exact key
  have := key'.comp_sub_const t t
  refine this.congr_of_eventuallyEq (Eventually.of_forall fun s => ?_)
  simp only
  rw [add_sub_cancel]

/- English proof (translation)
Establish `key` using `hl.hasDerivAt_map_expG (norm_πσ_le σ) hw 1 lE`. Establish `e1 : (fun s : ℝ => l (hGL2.smoothMap (πσ σ) hw (1 * hGL2.expG (s • lE)))) = fun s => ψ s * lT σ l w`. Use function extensionality and compare the values at `s`. Rewrite using `[one_mul, expG_lE, ← hW s w hw, lT_of (isSm_map σ hw _)]`. Both sides reduce to the same expression.

Rewrite `key` using `[e1]`. Establish `e2 : l (hGL2.smoothMap (πσ σ) (hGL2.isSmoothVector_derivOp (πσ σ) hw lE) 1) = lT σ l (dπ σ lE w)`. Rewrite using `[lT_of (isSm_dπ σ hw lE)]`. Use `congr 1`. Apply `Subtype.ext` to reduce the goal to its premises.

Simplify using the standard rewrite rules. Rewrite `key` using `[e2]`. Conclude with `key.unique (hψ.mul_const _)`.
-/
theorem lT_dπ_lE (hl : hGL2.IsSmoothContinuous (πσ σ) l) {ψ : ℝ → ℂ} {β : ℂ}
    (hψ : HasDerivAt ψ β 0)
    (hW : ∀ (x : ℝ) (w : H), IsSm σ w → lT σ l (σ (nMat x) w) = ψ x * lT σ l w)
    {w : H} (hw : IsSm σ w) : lT σ l (dπ σ lE w) = β * lT σ l w := by
  have key := hl.hasDerivAt_map_expG (norm_πσ_le σ) hw 1 lE
  have e1 : (fun s : ℝ => l (hGL2.smoothMap (πσ σ) hw (1 * hGL2.expG (s • lE)))) =
      fun s => ψ s * lT σ l w := by
    funext s
    rw [one_mul, expG_lE, ← hW s w hw, lT_of (isSm_map σ hw _)]
    rfl
  rw [e1] at key
  have e2 : l (hGL2.smoothMap (πσ σ) (hGL2.isSmoothVector_derivOp (πσ σ) hw lE) 1) =
      lT σ l (dπ σ lE w) := by
    rw [lT_of (isSm_dπ σ hw lE)]
    congr 1
    apply Subtype.ext
    simp
  rw [e2] at key
  exact key.unique (hψ.mul_const _)

/- English proof (translation)
Establish `e : σ (aT t) (dπ σ lE u) = ((Real.exp (2 * t) : ℝ) : ℂ) • dπ σ lE (σ (aT t) u)`. Use `hGL2.derivOp_map (πσ σ) hu (aT t) lE` as an intermediate fact. Rewrite `this` using `[Ad_aT_lE, hGL2.derivOp_smul_left]`. Rewrite using `[Complex.coe_smul]`. Conclude with `this.symm`.

Rewrite using `[Wt, e, lT_smul (isSm_dπ σ (isSm_map σ hu _) lE), lT_dπ_lE hl hψ hW (isSm_map σ hu _), Wt]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem Wt_dπ_lE (hl : hGL2.IsSmoothContinuous (πσ σ) l) {ψ : ℝ → ℂ} {β : ℂ}
    (hψ : HasDerivAt ψ β 0)
    (hW : ∀ (x : ℝ) (w : H), IsSm σ w → lT σ l (σ (nMat x) w) = ψ x * lT σ l w)
    {u : H} (hu : IsSm σ u) (t : ℝ) :
    Wt σ l (dπ σ lE u) t = β * Real.exp (2 * t) * Wt σ l u t := by
  have e : σ (aT t) (dπ σ lE u) = ((Real.exp (2 * t) : ℝ) : ℂ) • dπ σ lE (σ (aT t) u) := by
    have := hGL2.derivOp_map (πσ σ) hu (aT t) lE
    rw [Ad_aT_lE, hGL2.derivOp_smul_left] at this
    rw [Complex.coe_smul]
    exact this.symm
  rw [Wt, e, lT_smul (isSm_dπ σ (isSm_map σ hu _) lE), lT_dπ_lE hl hψ hW (isSm_map σ hu _), Wt]
  ring

end GroundTheory.Automorphic.ArchWhittaker

namespace GroundTheory.Automorphic.ArchWhittaker

open Matrix NormedSpace Complex MeasureTheory Filter Topology Set
open scoped Matrix.Norms.L2Operator Real InnerProductSpace ContDiff

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {σ : UnitaryRep FiltrationCocycleLiftCriterion H}

/- English proof (translation)
Establish `h0 : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t`. Simplify using `using (hasDerivAt_id t).ofReal_comp`. Establish `h1 : HasDerivAt (fun s : ℝ => (k : ℂ) * (s : ℂ) * I) ((k : ℂ) * 1 * I) t` using `(h0.const_mul (k : ℂ)).mul_const I`. Conclude with `h1.cexp.congr_deriv (by simp [chi])`.
-/
theorem hasDerivAt_chi (k : ℤ) (t : ℝ) : HasDerivAt (chi k) (chi k t * ((k : ℂ) * I)) t := by
  have h0 : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := by
    simpa using (hasDerivAt_id t).ofReal_comp
  have h1 : HasDerivAt (fun s : ℝ => (k : ℂ) * (s : ℂ) * I) ((k : ℂ) * 1 * I) t :=
    (h0.const_mul (k : ℂ)).mul_const I
  exact h1.cexp.congr_deriv (by simp [chi])

/- English proof (translation)
The claim follows from `hGL2.derivOp_add_left _ X Y u`.
-/
theorem dπ_add_left (X Y : gl2) (u : H) : dπ σ (X + Y) u = dπ σ X u + dπ σ Y u :=
  hGL2.derivOp_add_left _ X Y u

/- English proof (translation)
The claim follows from `hGL2.derivOp_smul_left _ r X u`.
-/
theorem dπ_smul_left (r : ℝ) (X : gl2) (u : H) : dπ σ (r • X) u = r • dπ σ X u :=
  hGL2.derivOp_smul_left _ r X u

/- English proof (translation)
The claim follows from `hGL2.derivOp_neg_left _ X u`.
-/
theorem dπ_neg_left (X : gl2) (u : H) : dπ σ (-X) u = -dπ σ X u :=
  hGL2.derivOp_neg_left _ X u

/- English proof (translation)
Rewrite using `[sub_eq_add_neg, dπ_add_left, dπ_neg_left, ← sub_eq_add_neg]`.
-/
theorem dπ_sub_left (X Y : gl2) (u : H) : dπ σ (X - Y) u = dπ σ X u - dπ σ Y u := by
  rw [sub_eq_add_neg, dπ_add_left, dπ_neg_left, ← sub_eq_add_neg]

/- English proof (translation)
Establish `h1` using `hGL2.hasDerivAt_derivOp (πσ σ) hu lW`. Establish `e : (fun t : ℝ => (πσ σ) (hGL2.expG (t • lW)) u) = fun t => chi k t • u`. Use function extensionality and compare the values at `t`. Rewrite using `[expG_lW]`. Conclude with `hk t`.

Rewrite `h1` using `[e]`. Establish `h2` using `(hasDerivAt_chi k 0).smul_const u`. Use `h1.unique h2` as an intermediate fact. Rewrite using `[show dπ σ lW u = hGL2.derivOp (πσ σ) lW u from rfl, this]`. Simplify using `[chi]`.
-/
theorem dπ_lW_of_mem {k : ℤ} {u : H} (hu : IsSm σ u) (hk : u ∈ weightSpace σ k) :
    dπ σ lW u = ((k : ℂ) * I) • u := by
  have h1 := hGL2.hasDerivAt_derivOp (πσ σ) hu lW
  have e : (fun t : ℝ => (πσ σ) (hGL2.expG (t • lW)) u) = fun t => chi k t • u := by
    funext t
    rw [expG_lW]
    exact hk t
  rw [e] at h1
  have h2 := (hasDerivAt_chi k 0).smul_const u
  have := h1.unique h2
  rw [show dπ σ lW u = hGL2.derivOp (πσ σ) lW u from rfl, this]
  simp [chi]

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `only [coe_lS, Submodule.coe_sub, Submodule.coe_smul, coe_lE, coe_lW]`. Apply the tactic sequence `ext i j; fin_cases i <;> fin_cases j <;> simp; norm_num`.
-/
theorem lS_eq_two_lE_sub_lW : lS = (2 : ℝ) • lE - lW := by
  apply Subtype.ext
  simp only [coe_lS, Submodule.coe_sub, Submodule.coe_smul, coe_lE, coe_lW]
  ext i j; fin_cases i <;> fin_cases j <;> simp; norm_num

/- English proof (translation)
Rewrite using `[lS_eq_two_lE_sub_lW, dπ_sub_left, dπ_smul_left]`.
-/
theorem dπ_lS (u : H) : dπ σ lS u = (2 : ℝ) • dπ σ lE u - dπ σ lW u := by
  rw [lS_eq_two_lE_sub_lW, dπ_sub_left, dπ_smul_left]

noncomputable def Rop (σ : UnitaryRep FiltrationCocycleLiftCriterion H) (u : H) : H := dπ σ lH u + I • dπ σ lS u

noncomputable def Lop (σ : UnitaryRep FiltrationCocycleLiftCriterion H) (u : H) : H := dπ σ lH u - I • dπ σ lS u

/- English proof (translation)
The claim follows from `(hGL2.smoothVectors (πσ σ)).add_mem (isSm_dπ σ hu lH) ((hGL2.smoothVectors (πσ σ)).smul_mem I (isSm_dπ σ hu lS))`.
-/
theorem isSm_Rop {u : H} (hu : IsSm σ u) : IsSm σ (Rop σ u) :=
  (hGL2.smoothVectors (πσ σ)).add_mem (isSm_dπ σ hu lH)
    ((hGL2.smoothVectors (πσ σ)).smul_mem I (isSm_dπ σ hu lS))

/- English proof (translation)
The claim follows from `(hGL2.smoothVectors (πσ σ)).sub_mem (isSm_dπ σ hu lH) ((hGL2.smoothVectors (πσ σ)).smul_mem I (isSm_dπ σ hu lS))`.
-/
theorem isSm_Lop {u : H} (hu : IsSm σ u) : IsSm σ (Lop σ u) :=
  (hGL2.smoothVectors (πσ σ)).sub_mem (isSm_dπ σ hu lH)
    ((hGL2.smoothVectors (πσ σ)).smul_mem I (isSm_dπ σ hu lS))

/- English proof (translation)
The claim follows from `(hGL2.derivOp_map (πσ σ) hu g X).symm`.
-/
theorem map_dπ {u : H} (hu : IsSm σ u) (g : FiltrationCocycleLiftCriterion) (X : gl2) :
    σ g (dπ σ X u) = dπ σ (hGL2.Ad g X) (σ g u) :=
  (hGL2.derivOp_map (πσ σ) hu g X).symm

/- English proof (translation)
The claim follows from `hGL2.derivOp_smul (πσ σ) hu c X`.
-/
theorem dπ_smul_vec {u : H} (hu : IsSm σ u) (c : ℂ) (X : gl2) : dπ σ X (c • u) = c • dπ σ X u :=
  hGL2.derivOp_smul (πσ σ) hu c X

/- English proof (translation)
Rewrite using `[show (2 : ℂ) * θ * I = ((2 * θ : ℝ) : ℂ) * I by push_cast; ring, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]`.
-/
theorem exp_two_mul_I (θ : ℝ) :
    Complex.exp ((2 : ℂ) * θ * I) = (Real.cos (2 * θ) : ℂ) + (Real.sin (2 * θ) : ℂ) * I := by
  rw [show (2 : ℂ) * θ * I = ((2 * θ : ℝ) : ℂ) * I by push_cast; ring, Complex.exp_mul_I,
    ← Complex.ofReal_cos, ← Complex.ofReal_sin]

/- English proof (translation)
Introduce `θ`. Simplify using `only [Rop, map_add, map_smul, map_dπ hu, Ad_kMat_lH, Ad_kMat_lS, hk θ, dπ_smul_vec hu, dπ_sub_left, dπ_add_left, dπ_smul_left]`. Establish `hchi : chi (k + 2) θ = chi k θ * ((Real.cos (2 * θ) : ℂ) + (Real.sin (2 * θ) : ℂ) * I)`. Rewrite using `[← exp_two_mul_I, chi, chi, ← Complex.exp_add]`. Use `congr 1`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hchi]`. Simplify using `only [← Complex.coe_smul]`. Use `match_scalars`.

Apply the tactic sequence `all_goals ring_nf`. Apply the tactic sequence `all_goals (try simp only [Complex.I_sq])`. Apply the tactic sequence `all_goals ring`.
-/
theorem Rop_mem {k : ℤ} {u : H} (hu : IsSm σ u) (hk : u ∈ weightSpace σ k) :
    Rop σ u ∈ weightSpace σ (k + 2) := by
  intro θ
  simp only [Rop, map_add, map_smul, map_dπ hu, Ad_kMat_lH, Ad_kMat_lS, hk θ, dπ_smul_vec hu,
    dπ_sub_left, dπ_add_left, dπ_smul_left]
  have hchi : chi (k + 2) θ = chi k θ * ((Real.cos (2 * θ) : ℂ) + (Real.sin (2 * θ) : ℂ) * I) := by
    rw [← exp_two_mul_I, chi, chi, ← Complex.exp_add]; congr 1; push_cast; ring
  rw [hchi]
  simp only [← Complex.coe_smul]
  match_scalars
  all_goals ring_nf
  all_goals (try simp only [Complex.I_sq])
  all_goals ring

/- English proof (translation)
Introduce `θ`. Simplify using `only [Lop, map_sub, map_smul, map_dπ hu, Ad_kMat_lH, Ad_kMat_lS, hk θ, dπ_smul_vec hu, dπ_sub_left, dπ_add_left, dπ_smul_left]`. Establish `hchi : chi (k - 2) θ = chi k θ * ((Real.cos (2 * θ) : ℂ) - (Real.sin (2 * θ) : ℂ) * I)`. Establish `: (Real.cos (2 * θ) : ℂ) - (Real.sin (2 * θ) : ℂ) * I = Complex.exp (-((2 : ℂ) * θ * I))`. Rewrite using `[show -((2 : ℂ) * θ * I) = ((-(2 * θ) : ℝ) : ℂ) * I by push_cast; ring, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this, chi, chi, ← Complex.exp_add]`. Use `congr 1`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hchi]`. Simplify using `only [← Complex.coe_smul]`. Use `match_scalars`. Apply the tactic sequence `all_goals ring_nf`.

Apply the tactic sequence `all_goals (try simp only [Complex.I_sq])`. Apply the tactic sequence `all_goals ring`.
-/
theorem Lop_mem {k : ℤ} {u : H} (hu : IsSm σ u) (hk : u ∈ weightSpace σ k) :
    Lop σ u ∈ weightSpace σ (k - 2) := by
  intro θ
  simp only [Lop, map_sub, map_smul, map_dπ hu, Ad_kMat_lH, Ad_kMat_lS, hk θ, dπ_smul_vec hu,
    dπ_sub_left, dπ_add_left, dπ_smul_left]
  have hchi : chi (k - 2) θ = chi k θ * ((Real.cos (2 * θ) : ℂ) - (Real.sin (2 * θ) : ℂ) * I) := by
    have : (Real.cos (2 * θ) : ℂ) - (Real.sin (2 * θ) : ℂ) * I = Complex.exp (-((2 : ℂ) * θ * I)) := by
      rw [show -((2 : ℂ) * θ * I) = ((-(2 * θ) : ℝ) : ℂ) * I by push_cast; ring, Complex.exp_mul_I,
        ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg]
      push_cast; ring
    rw [this, chi, chi, ← Complex.exp_add]; congr 1; push_cast; ring
  rw [hchi]
  simp only [← Complex.coe_smul]
  match_scalars
  all_goals ring_nf
  all_goals (try simp only [Complex.I_sq])
  all_goals ring

/- English proof (translation)
Establish `hv'` using `hGL2.hasDerivAt_derivOp (πσ σ) hv X`. Establish `hw'` using `hGL2.hasDerivAt_derivOp (πσ σ) hw X`. Establish `hd` using `hv'.inner ℂ hw'`. Establish `hconst : (fun t : ℝ => ⟪(πσ σ) (hGL2.expG (t • X)) v, (πσ σ) (hGL2.expG (t • X)) w⟫_ℂ) = fun _ => ⟪v, w⟫_ℂ`. Use function extensionality and compare the values at `t`.

Conclude with `σ.inner_map_map _ v w`. Rewrite `hd` using `[hconst]`. Establish `h0` using `hd.unique (hasDerivAt_const 0 _)`. Simplify using `only [zero_smul, IsExpLieAlgebra.expG_zero, BanachRep.map_one_apply] at h0`. Take the linear combination `h0`.
-/
theorem inner_dπ_left {v w : H} (hv : IsSm σ v) (hw : IsSm σ w) (X : gl2) :
    ⟪dπ σ X v, w⟫_ℂ = -⟪v, dπ σ X w⟫_ℂ := by
  have hv' := hGL2.hasDerivAt_derivOp (πσ σ) hv X
  have hw' := hGL2.hasDerivAt_derivOp (πσ σ) hw X
  have hd := hv'.inner ℂ hw'
  have hconst : (fun t : ℝ => ⟪(πσ σ) (hGL2.expG (t • X)) v, (πσ σ) (hGL2.expG (t • X)) w⟫_ℂ) =
      fun _ => ⟪v, w⟫_ℂ := by
    funext t; exact σ.inner_map_map _ v w
  rw [hconst] at hd
  have h0 := hd.unique (hasDerivAt_const 0 _)
  simp only [zero_smul, IsExpLieAlgebra.expG_zero, BanachRep.map_one_apply] at h0
  linear_combination h0

/- English proof (translation)
Simplify using `only [Rop, Lop, inner_add_left, inner_smul_left, inner_sub_right, inner_smul_right, inner_dπ_left hv hw, Complex.conj_I]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem inner_Rop {v w : H} (hv : IsSm σ v) (hw : IsSm σ w) :
    ⟪Rop σ v, w⟫_ℂ = -⟪v, Lop σ w⟫_ℂ := by
  simp only [Rop, Lop, inner_add_left, inner_smul_left, inner_sub_right, inner_smul_right,
    inner_dπ_left hv hw, Complex.conj_I]
  ring

/- English proof (translation)
Simplify using `only [Lop, Rop, map_sub, map_smul, map_dπ hu, Ad_eps_lH, Ad_eps_lS, dπ_neg_left]`. Rewrite using `[smul_neg, sub_neg_eq_add]`.
-/
theorem map_eps_Lop {u : H} (hu : IsSm σ u) : σ eps (Lop σ u) = Rop σ (σ eps u) := by
  simp only [Lop, Rop, map_sub, map_smul, map_dπ hu, Ad_eps_lH, Ad_eps_lS, dπ_neg_left]
  rw [smul_neg, sub_neg_eq_add]

end GroundTheory.Automorphic.ArchWhittaker

namespace GroundTheory.Automorphic.ArchWhittaker

open Matrix NormedSpace Complex MeasureTheory Filter Topology Set
open scoped Matrix.Norms.L2Operator Real InnerProductSpace ContDiff

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {σ : UnitaryRep FiltrationCocycleLiftCriterion H} {l : hGL2.smoothVectors (πσ σ) →ₗ[ℂ] ℂ}

noncomputable def bT (β : ℂ) (t : ℝ) : ℂ := 2 * I * β * (Real.exp (2 * t) : ℂ)

section Whittaker

variable (hl : hGL2.IsSmoothContinuous (πσ σ) l) {ψ : ℝ → ℂ} {β : ℂ} (hψ : HasDerivAt ψ β 0)
  (hW : ∀ (x : ℝ) (w : H), IsSm σ w → lT σ l (σ (nMat x) w) = ψ x * lT σ l w)
include hl hψ hW

/- English proof (translation)
Rewrite using `[dπ_lS, ← Complex.coe_smul, Wt_sub ((hGL2.smoothVectors (πσ σ)).smul_mem _ (isSm_dπ σ hu lE)) (isSm_dπ σ hu lW), Wt_smul (isSm_dπ σ hu lE), Wt_dπ_lE hl hψ hW hu, dπ_lW_of_mem hu hk, Wt_smul hu]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem Wt_dπ_lS {k : ℤ} {u : H} (hu : IsSm σ u) (hk : u ∈ weightSpace σ k) (t : ℝ) :
    Wt σ l (dπ σ lS u) t = (2 * β * Real.exp (2 * t) - (k : ℂ) * I) * Wt σ l u t := by
  rw [dπ_lS, ← Complex.coe_smul, Wt_sub ((hGL2.smoothVectors (πσ σ)).smul_mem _ (isSm_dπ σ hu lE))
    (isSm_dπ σ hu lW), Wt_smul (isSm_dπ σ hu lE), Wt_dπ_lE hl hψ hW hu, dπ_lW_of_mem hu hk,
    Wt_smul hu]
  push_cast
  ring

/- English proof (translation)
Rewrite using `[Rop, Wt_add (isSm_dπ σ hu lH) ((hGL2.smoothVectors (πσ σ)).smul_mem _ (isSm_dπ σ hu lS)), Wt_smul (isSm_dπ σ hu lS), Wt_dπ_lS hl hψ hW hu hk, bT]`. Put the polynomial expressions in normal form. Rewrite using `[Complex.I_sq]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem Wt_Rop {k : ℤ} {u : H} (hu : IsSm σ u) (hk : u ∈ weightSpace σ k) (t : ℝ) :
    Wt σ l (Rop σ u) t = Wt σ l (dπ σ lH u) t + (bT β t + k) * Wt σ l u t := by
  rw [Rop, Wt_add (isSm_dπ σ hu lH) ((hGL2.smoothVectors (πσ σ)).smul_mem _ (isSm_dπ σ hu lS)),
    Wt_smul (isSm_dπ σ hu lS), Wt_dπ_lS hl hψ hW hu hk, bT]
  ring_nf
  rw [Complex.I_sq]
  ring

/- English proof (translation)
Rewrite using `[Lop, Wt_sub (isSm_dπ σ hu lH) ((hGL2.smoothVectors (πσ σ)).smul_mem _ (isSm_dπ σ hu lS)), Wt_smul (isSm_dπ σ hu lS), Wt_dπ_lS hl hψ hW hu hk, bT]`. Put the polynomial expressions in normal form. Rewrite using `[Complex.I_sq]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem Wt_Lop {k : ℤ} {u : H} (hu : IsSm σ u) (hk : u ∈ weightSpace σ k) (t : ℝ) :
    Wt σ l (Lop σ u) t = Wt σ l (dπ σ lH u) t - (bT β t + k) * Wt σ l u t := by
  rw [Lop, Wt_sub (isSm_dπ σ hu lH) ((hGL2.smoothVectors (πσ σ)).smul_mem _ (isSm_dπ σ hu lS)),
    Wt_smul (isSm_dπ σ hu lS), Wt_dπ_lS hl hψ hW hu hk, bT]
  ring_nf
  rw [Complex.I_sq]
  ring

/- English proof (translation)
Establish `h1 : HasDerivAt (fun s : ℝ => ((Real.exp (2 * s) : ℝ) : ℂ)) ((Real.exp (2 * t) * (2 * 1) : ℝ) : ℂ) t` using `(((hasDerivAt_id t).const_mul 2).exp).ofReal_comp`. Use `h1.const_mul (2 * I * β)` as an intermediate fact. Use `this.congr_deriv ?_` and prove the remaining obligations. Simplify using `only [bT]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem hasDerivAt_bT (t : ℝ) : HasDerivAt (bT β) (2 * bT β t) t := by
  have h1 : HasDerivAt (fun s : ℝ => ((Real.exp (2 * s) : ℝ) : ℂ)) ((Real.exp (2 * t) * (2 * 1) : ℝ) : ℂ) t :=
    (((hasDerivAt_id t).const_mul 2).exp).ofReal_comp
  have := h1.const_mul (2 * I * β)
  refine this.congr_deriv ?_
  simp only [bT]; push_cast; ring

/- English proof (translation)
Establish `hR` using `isSm_Rop hv`. Establish `hRk : Rop σ v ∈ weightSpace σ (k + 2)` using `Rop_mem hv hk`. Establish `d1` using `hasDerivAt_Wt hl hR t`. Establish `d2 : HasDerivAt (Wt σ l (Rop σ v)) (Wt σ l (dπ σ lH (dπ σ lH v)) t + (2 * bT β t * Wt σ l v t + (bT β t + k) * Wt σ l (dπ σ lH v) t)) t`. Establish `e : Wt σ l (Rop σ v) = fun s => Wt σ l (dπ σ lH v) s + (bT β s + k) * Wt σ l v s`.

Use function extensionality and compare the values at `s`. Conclude with `Wt_Rop hl hψ hW hv hk s`. Rewrite using `[e]`. Conclude with `(hasDerivAt_Wt hl (isSm_dπ σ hv lH) t).add (((hasDerivAt_bT hl hψ hW t).add_const (k : ℂ)).mul (hasDerivAt_Wt hl hv t)) |>.congr_deriv (by ring)`. Establish `hd` using `d1.unique d2`.

Establish `hL` using `Wt_Lop hl hψ hW hR hRk t`. Rewrite `hL` using `[hα, Wt_smul hv, hd, Wt_Rop hl hψ hW hv hk t]`. Move the coercions through the operations in `at hL`. Take the linear combination `-hL`.
-/
theorem Wt_second_order {k : ℤ} {v : H} (hv : IsSm σ v) (hk : v ∈ weightSpace σ k) {α : ℂ}
    (hα : Lop σ (Rop σ v) = α • v) (t : ℝ) :
    Wt σ l (dπ σ lH (dπ σ lH v)) t = 2 * Wt σ l (dπ σ lH v) t +
      (α + (bT β t + k) * (bT β t + k + 2) - 2 * bT β t) * Wt σ l v t := by
  have hR := isSm_Rop hv
  have hRk : Rop σ v ∈ weightSpace σ (k + 2) := Rop_mem hv hk

  have d1 := hasDerivAt_Wt hl hR t
  have d2 : HasDerivAt (Wt σ l (Rop σ v))
      (Wt σ l (dπ σ lH (dπ σ lH v)) t + (2 * bT β t * Wt σ l v t +
        (bT β t + k) * Wt σ l (dπ σ lH v) t)) t := by
    have e : Wt σ l (Rop σ v) = fun s => Wt σ l (dπ σ lH v) s + (bT β s + k) * Wt σ l v s := by
      funext s; exact Wt_Rop hl hψ hW hv hk s
    rw [e]
    exact (hasDerivAt_Wt hl (isSm_dπ σ hv lH) t).add
      (((hasDerivAt_bT hl hψ hW t).add_const (k : ℂ)).mul (hasDerivAt_Wt hl hv t)) |>.congr_deriv
        (by ring)
  have hd := d1.unique d2
  have hL := Wt_Lop hl hψ hW hR hRk t
  rw [hα, Wt_smul hv, hd, Wt_Rop hl hψ hW hv hk t] at hL
  push_cast at hL
  linear_combination -hL

end Whittaker

end GroundTheory.Automorphic.ArchWhittaker

namespace GroundTheory.Automorphic.ArchWhittaker

open Matrix NormedSpace Complex MeasureTheory Filter Topology Set
open scoped Matrix.Norms.L2Operator Real InnerProductSpace ContDiff

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {σ : UnitaryRep FiltrationCocycleLiftCriterion H} {l : hGL2.smoothVectors (πσ σ) →ₗ[ℂ] ℂ}

/- English proof (translation)
Establish `e : (((aT t : FiltrationCocycleLiftCriterion) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = Matrix.diagonal ![Real.exp t, Real.exp (-t)]`. Apply the tactic sequence `rw [coe_aT]; ext i j; fin_cases i <;> fin_cases j <;> simp`. Rewrite using `[e, Matrix.l2_opNorm_diagonal]`. Use `(pi_norm_le_iff_of_nonneg (Real.exp_pos _).le).2 fun i => ?_` and prove the remaining obligations. Use `fin_cases i`.

Simplify using `only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]`. Conclude with `Real.exp_le_exp.2 (le_abs_self t)`. Simplify using `only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]`. Conclude with `Real.exp_le_exp.2 (neg_le_abs t)`.
-/
theorem norm_aT_le (t : ℝ) :
    ‖(((aT t : FiltrationCocycleLiftCriterion) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)‖ ≤ Real.exp |t| := by
  have e : (((aT t : FiltrationCocycleLiftCriterion) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      Matrix.diagonal ![Real.exp t, Real.exp (-t)] := by
    rw [coe_aT]; ext i j; fin_cases i <;> fin_cases j <;> simp
  rw [e, Matrix.l2_opNorm_diagonal]
  refine (pi_norm_le_iff_of_nonneg (Real.exp_pos _).le).2 fun i => ?_
  fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.2 (le_abs_self t)
  · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.2 (neg_le_abs t)

/- English proof (translation)
Use `ContinuousLinearMap.opNorm_le_bound _ (Real.exp_pos _).le fun X => ?_` and prove the remaining obligations. Rewrite using `[IsExpLieAlgebra.AdL_apply]`. Use `show ‖((hGL2.Ad (aT t)⁻¹ X : gl2) : Matrix (Fin 2) (Fin 2) ℝ)‖ ≤ _ * ‖(X : Matrix (Fin 2) (Fin 2) ℝ)‖`. Rewrite using `[coe_Ad_GL2, inv_inv, aT_inv]`. Combine the equalities or inequalities in the displayed calculation.

Use `(norm_mul_le _ _).trans ?_` and prove the remaining obligations. Use `gcongr`. Conclude with `norm_mul_le _ _`. Use `_ ≤ Real.exp |t| * ‖(X : Matrix (Fin 2) (Fin 2) ℝ)‖ * Real.exp |t| := by gcongr`. Use `norm_aT_le (-t)` as an intermediate fact.

Rewrite `this` using `[abs_neg]`. Then use the resulting hypothesis. Conclude with `norm_aT_le t`. Use `_ = Real.exp (2 * |t|) * ‖(X : Matrix (Fin 2) (Fin 2) ℝ)‖ := by`. Rewrite using `[mul_comm _ (Real.exp |t|), ← mul_assoc, ← Real.exp_add]`. Put the polynomial expressions in normal form.
-/
theorem norm_AdL_aT_inv_le (t : ℝ) : ‖hGL2.AdL (aT t)⁻¹‖ ≤ Real.exp (2 * |t|) := by
  refine ContinuousLinearMap.opNorm_le_bound _ (Real.exp_pos _).le fun X => ?_
  rw [IsExpLieAlgebra.AdL_apply]
  show ‖((hGL2.Ad (aT t)⁻¹ X : gl2) : Matrix (Fin 2) (Fin 2) ℝ)‖ ≤ _ * ‖(X : Matrix (Fin 2) (Fin 2) ℝ)‖
  rw [coe_Ad_GL2, inv_inv, aT_inv]
  calc ‖(((aT (-t) : FiltrationCocycleLiftCriterion) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) * (X : Matrix (Fin 2) (Fin 2) ℝ) *
        (((aT t : FiltrationCocycleLiftCriterion) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)‖
      ≤ ‖(((aT (-t) : FiltrationCocycleLiftCriterion) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)‖ * ‖(X : Matrix (Fin 2) (Fin 2) ℝ)‖ *
        ‖(((aT t : FiltrationCocycleLiftCriterion) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)‖ := by
        refine (norm_mul_le _ _).trans ?_
        gcongr
        exact norm_mul_le _ _
    _ ≤ Real.exp |t| * ‖(X : Matrix (Fin 2) (Fin 2) ℝ)‖ * Real.exp |t| := by
        gcongr
        · have := norm_aT_le (-t); rwa [abs_neg] at this
        · exact norm_aT_le t
    _ = Real.exp (2 * |t|) * ‖(X : Matrix (Fin 2) (Fin 2) ℝ)‖ := by
        rw [mul_comm _ (Real.exp |t|), ← mul_assoc, ← Real.exp_add]; ring_nf

/- English proof (translation)
Take `⟨C, N, hC⟩` from `hl.exists_norm_map_le (norm_πσ_le σ) hu`. Use `⟨|C| * 2 ^ N, N, fun t ht => ?_⟩` and prove the remaining obligations. Establish `h1` using `hC (aT t)`. Establish `e : Wt σ l u t = l (hGL2.smoothMap (πσ σ) hu (aT t))`. Rewrite using `[Wt, lT_of (isSm_map σ hu _)]`.

Both sides reduce to the same expression. Rewrite using `[e]`. Establish `h2 : (1 + ‖hGL2.AdL (aT t)⁻¹‖) ^ N ≤ (2 * Real.exp (2 * t)) ^ N`. Establish `h3` using `norm_AdL_aT_inv_le t`. Rewrite `h3` using `[abs_of_nonneg ht]`.

Establish `h4 : 1 ≤ Real.exp (2 * t)` using `Real.one_le_exp (by linarith)`. Use `gcongr`. Combine the linear equalities and inequalities to obtain the conclusion. Combine the equalities or inequalities in the displayed calculation.
-/
theorem exists_Wt_bound (hl : hGL2.IsSmoothContinuous (πσ σ) l) {u : H} (hu : IsSm σ u) :
    ∃ (C : ℝ) (N : ℕ), ∀ t ≥ 0, ‖Wt σ l u t‖ ≤ C * Real.exp (2 * t) ^ N := by
  obtain ⟨C, N, hC⟩ := hl.exists_norm_map_le (norm_πσ_le σ) hu
  refine ⟨|C| * 2 ^ N, N, fun t ht => ?_⟩
  have h1 := hC (aT t)
  have e : Wt σ l u t = l (hGL2.smoothMap (πσ σ) hu (aT t)) := by
    rw [Wt, lT_of (isSm_map σ hu _)]; rfl
  rw [e]
  have h2 : (1 + ‖hGL2.AdL (aT t)⁻¹‖) ^ N ≤ (2 * Real.exp (2 * t)) ^ N := by
    have h3 := norm_AdL_aT_inv_le t
    rw [abs_of_nonneg ht] at h3
    have h4 : 1 ≤ Real.exp (2 * t) := Real.one_le_exp (by linarith)
    gcongr
    linarith
  calc ‖l (hGL2.smoothMap (πσ σ) hu (aT t))‖ ≤ C * (1 + ‖hGL2.AdL (aT t)⁻¹‖) ^ N := h1
    _ ≤ |C| * (1 + ‖hGL2.AdL (aT t)⁻¹‖) ^ N := by gcongr; exact le_abs_self C
    _ ≤ |C| * (2 * Real.exp (2 * t)) ^ N := by gcongr
    _ = |C| * 2 ^ N * Real.exp (2 * t) ^ N := by rw [mul_pow]; ring

/- English proof (translation)
Substitute `ht` using the available equality. Establish `hs : HasDerivAt (fun y : ℝ => Real.log y / 2) (y⁻¹ / 2) y` using `(Real.hasDerivAt_log hy.ne').div_const 2`. Use `hF.scomp y hs` as an intermediate fact. Use `this.congr_deriv ?_` and prove the remaining obligations. Rewrite using `[Complex.real_smul]`.

Use `push_cast`. Clear the denominators using the available nonvanishing facts.
-/
theorem hasDerivAt_comp_log {F F' : ℝ → ℂ} {t₀ : ℝ} {y : ℝ} (hy : 0 < y)
    (hF : HasDerivAt F (F' t₀) t₀) (ht : t₀ = Real.log y / 2) :
    HasDerivAt (fun y => F (Real.log y / 2)) (F' t₀ / (2 * y)) y := by
  subst ht
  have hs : HasDerivAt (fun y : ℝ => Real.log y / 2) (y⁻¹ / 2) y :=
    (Real.hasDerivAt_log hy.ne').div_const 2
  have := hF.scomp y hs
  refine this.congr_deriv ?_
  rw [Complex.real_smul]
  push_cast
  field_simp

/- English proof (translation)
Rewrite using `[show 2 * (Real.log y / 2) = Real.log y by ring, Real.exp_log hy]`.
-/
theorem exp_log_half {y : ℝ} (hy : 0 < y) : Real.exp (2 * (Real.log y / 2)) = y := by
  rw [show 2 * (Real.log y / 2) = Real.log y by ring, Real.exp_log hy]

/- English proof (translation)
Establish `hθ2 : 0 < θ ^ 2` using `by positivity`. Use `⟨max 1 (2 * (‖A‖ + ‖B‖) / θ ^ 2), lt_of_lt_of_le one_pos (le_max_left _ _), ?_, ?_⟩` and prove the remaining obligations. Introduce `y hy`. Establish `hy1 : 1 ≤ y` using `le_trans (le_max_left _ _) hy`. Establish `hy0 : 0 < y` using `lt_of_lt_of_le one_pos hy1`.

Establish `hy2 : 2 * (‖A‖ + ‖B‖) / θ ^ 2 ≤ y` using `le_trans (le_max_right _ _) hy`. Establish `hA : |(A / y).re| ≤ ‖A‖ / y`. Combine the equalities or inequalities in the displayed calculation. Establish `hB : |(B / y ^ 2).re| ≤ ‖B‖ / y`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[show (B / (y : ℂ) ^ 2) = B / ((y ^ 2 : ℝ) : ℂ) by push_cast; ring]`. Conclude with `Complex.abs_re_le_norm _`. Use `_ = ‖B‖ / y ^ 2 := by rw [norm_div, norm_pow, Complex.norm_real, Real.norm_of_nonneg hy0.le]`. Use `_ ≤ ‖B‖ / y := by`. Apply `div_le_div_of_nonneg_left (norm_nonneg _) hy0` to reduce the goal to its premises.

Use the polynomial consequences of the given equalities and inequalities. Establish `hre : ((θ ^ 2 : ℝ) + A / y + B / y ^ 2 : ℂ).re = θ ^ 2 + (A / y).re + (B / y ^ 2).re`. Simplify using `only [Complex.add_re, Complex.ofReal_re]`. Rewrite using `[hre]`. Establish `hsum : (‖A‖ + ‖B‖) / y ≤ θ ^ 2 / 2`.

Rewrite using `[div_le_iff₀ hy0]`. Rewrite `hy2` using `[div_le_iff₀ hθ2]`. Use the polynomial consequences of the given equalities and inequalities. Establish `: (‖A‖ / y) + (‖B‖ / y) = (‖A‖ + ‖B‖) / y` using `by ring`. Establish `hab : |θ| ^ 2 = θ ^ 2` using `sq_abs θ`.

Use polynomial arithmetic with `[abs_le.1 hA, abs_le.1 hB]`. Introduce `y hy`. Establish `hy1 : 1 ≤ y` using `le_trans (le_max_left _ _) hy`. Establish `hy0 : 0 < y` using `lt_of_lt_of_le one_pos hy1`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[Complex.norm_real, Real.norm_of_nonneg hθ2.le, norm_div, norm_div, norm_pow, Complex.norm_real, Real.norm_of_nonneg hy0.le]`. Use `gcongr`. Conclude with `div_le_self (norm_nonneg _) hy1`. Conclude with `div_le_self (norm_nonneg _) (one_le_pow₀ hy1)`.
-/
theorem q_bounds {θ : ℝ} (hθ : θ ≠ 0) (A B : ℂ) : ∃ Y₀ > (0 : ℝ),
    (∀ y ≥ Y₀, (|θ| / 2) ^ 2 ≤ ((θ ^ 2 : ℝ) + A / y + B / y ^ 2 : ℂ).re) ∧
    (∀ y ≥ Y₀, ‖((θ ^ 2 : ℝ) + A / y + B / y ^ 2 : ℂ)‖ ≤ θ ^ 2 + ‖A‖ + ‖B‖) := by
  have hθ2 : 0 < θ ^ 2 := by positivity
  refine ⟨max 1 (2 * (‖A‖ + ‖B‖) / θ ^ 2), lt_of_lt_of_le one_pos (le_max_left _ _), ?_, ?_⟩
  · intro y hy
    have hy1 : 1 ≤ y := le_trans (le_max_left _ _) hy
    have hy0 : 0 < y := lt_of_lt_of_le one_pos hy1
    have hy2 : 2 * (‖A‖ + ‖B‖) / θ ^ 2 ≤ y := le_trans (le_max_right _ _) hy
    have hA : |(A / y).re| ≤ ‖A‖ / y := by
      calc |(A / y).re| ≤ ‖A / y‖ := Complex.abs_re_le_norm _
        _ = ‖A‖ / y := by rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hy0.le]
    have hB : |(B / y ^ 2).re| ≤ ‖B‖ / y := by
      calc |(B / y ^ 2).re| ≤ ‖B / (y : ℂ) ^ 2‖ := by
            rw [show (B / (y : ℂ) ^ 2) = B / ((y ^ 2 : ℝ) : ℂ) by push_cast; ring]
            exact Complex.abs_re_le_norm _
        _ = ‖B‖ / y ^ 2 := by rw [norm_div, norm_pow, Complex.norm_real, Real.norm_of_nonneg hy0.le]
        _ ≤ ‖B‖ / y := by
            apply div_le_div_of_nonneg_left (norm_nonneg _) hy0
            nlinarith
    have hre : ((θ ^ 2 : ℝ) + A / y + B / y ^ 2 : ℂ).re = θ ^ 2 + (A / y).re + (B / y ^ 2).re := by
      simp only [Complex.add_re, Complex.ofReal_re]
    rw [hre]
    have hsum : (‖A‖ + ‖B‖) / y ≤ θ ^ 2 / 2 := by
      rw [div_le_iff₀ hy0]
      rw [div_le_iff₀ hθ2] at hy2
      nlinarith
    have : (‖A‖ / y) + (‖B‖ / y) = (‖A‖ + ‖B‖) / y := by ring
    have hab : |θ| ^ 2 = θ ^ 2 := sq_abs θ
    nlinarith [abs_le.1 hA, abs_le.1 hB]
  · intro y hy
    have hy1 : 1 ≤ y := le_trans (le_max_left _ _) hy
    have hy0 : 0 < y := lt_of_lt_of_le one_pos hy1
    calc ‖((θ ^ 2 : ℝ) + A / y + B / y ^ 2 : ℂ)‖ ≤ ‖((θ ^ 2 : ℝ) : ℂ)‖ + ‖A / y‖ + ‖B / (y : ℂ) ^ 2‖ :=
          norm_add₃_le
      _ ≤ θ ^ 2 + ‖A‖ + ‖B‖ := by
          rw [Complex.norm_real, Real.norm_of_nonneg hθ2.le, norm_div, norm_div, norm_pow,
            Complex.norm_real, Real.norm_of_nonneg hy0.le]
          gcongr
          · exact div_le_self (norm_nonneg _) hy1
          · exact div_le_self (norm_nonneg _) (one_le_pow₀ hy1)

end GroundTheory.Automorphic.ArchWhittaker

namespace GroundTheory.Automorphic.ArchWhittaker

open Matrix NormedSpace Complex MeasureTheory Filter Topology Set
open scoped Matrix.Norms.L2Operator Real InnerProductSpace ContDiff

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {σ : UnitaryRep FiltrationCocycleLiftCriterion H}

/- English proof (translation)
Rewrite using `[Wt, map_zero, lT_zero]`.
-/
theorem Wt_zero (l : hGL2.smoothVectors (πσ σ) →ₗ[ℂ] ℂ) (t : ℝ) : Wt σ l 0 t = 0 := by
  rw [Wt, map_zero, lT_zero]

/- English proof (translation)
Take `⟨C, N, hC⟩` from `exists_Wt_bound hl hu`. Use `⟨C, N, fun y hy => ?_⟩` and prove the remaining obligations. Establish `hy0 : 0 < y` using `lt_of_lt_of_le one_pos hy`. Use `hC (Real.log y / 2) (div_nonneg (Real.log_nonneg hy) zero_le_two)` as an intermediate fact. Rewrite `this` using `[exp_log_half hy0]`. Then use the resulting hypothesis.
-/
theorem exists_Wt_bound_y {l : hGL2.smoothVectors (πσ σ) →ₗ[ℂ] ℂ}
    (hl : hGL2.IsSmoothContinuous (πσ σ) l) {u : H} (hu : IsSm σ u) :
    ∃ (C : ℝ) (N : ℕ), ∀ y ≥ 1, ‖Wt σ l u (Real.log y / 2)‖ ≤ C * y ^ N := by
  obtain ⟨C, N, hC⟩ := exists_Wt_bound hl hu
  refine ⟨C, N, fun y hy => ?_⟩
  have hy0 : 0 < y := lt_of_lt_of_le one_pos hy
  have := hC (Real.log y / 2) (div_nonneg (Real.log_nonneg hy) zero_le_two)
  rwa [exp_log_half hy0] at this

section Whittaker

variable {l : hGL2.smoothVectors (πσ σ) →ₗ[ℂ] ℂ}
  (hl : hGL2.IsSmoothContinuous (πσ σ) l) {ψ : ℝ → ℂ} {θ : ℝ} (hψ : HasDerivAt ψ (I * θ) 0)
  (hW : ∀ (x : ℝ) (w : H), IsSm σ w → lT σ l (σ (nMat x) w) = ψ x * lT σ l w)
include hl hψ hW

/- English proof (translation)
Rewrite using `[bT, exp_log_half hy]`. Put the polynomial expressions in normal form. Rewrite using `[Complex.I_sq]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem bT_log_half {y : ℝ} (hy : 0 < y) : bT (I * θ) (Real.log y / 2) = -2 * θ * y := by
  rw [bT, exp_log_half hy]
  ring_nf
  rw [Complex.I_sq]
  ring

/- English proof (translation)
Establish `h1` using `hasDerivAt_comp_log hy (hasDerivAt_Wt hl (isSm_dπ σ hv lH) (Real.log y / 2)) rfl`. Establish `h2 : HasDerivAt (fun y : ℝ => (2 * y : ℂ)) 2 y`. Use `((hasDerivAt_id y).ofReal_comp).const_mul (2 : ℂ)` as an intermediate fact. Simplify using `using this`. Establish `hy' : (2 * y : ℂ) ≠ 0`.

Establish `: (y : ℂ) ≠ 0` using `by exact_mod_cast hy.ne'`. Conclude with `mul_ne_zero two_ne_zero this`. Establish `h3` using `h1.div h2 hy'`. Use `h3.congr_deriv ?_` and prove the remaining obligations. Rewrite using `[Wt_second_order hl hψ hW hv hk hα, bT_log_half hl hψ hW hy]`.

Establish `: (y : ℂ) ≠ 0` using `by exact_mod_cast hy.ne'`. Clear the denominators using the available nonvanishing facts. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hasDerivAt_Wt_y' {k : ℤ} {v : H} (hv : IsSm σ v) (hk : v ∈ weightSpace σ k) {α : ℂ}
    (hα : Lop σ (Rop σ v) = α • v) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun y => Wt σ l (dπ σ lH v) (Real.log y / 2) / (2 * y))
      ((((θ ^ 2 : ℝ) : ℂ) + (-(θ * k) : ℂ) / y + ((k * (k + 2) + α) / 4) / y ^ 2) *
        Wt σ l v (Real.log y / 2)) y := by
  have h1 := hasDerivAt_comp_log hy (hasDerivAt_Wt hl (isSm_dπ σ hv lH) (Real.log y / 2)) rfl
  have h2 : HasDerivAt (fun y : ℝ => (2 * y : ℂ)) 2 y := by
    have := ((hasDerivAt_id y).ofReal_comp).const_mul (2 : ℂ)
    simpa using this
  have hy' : (2 * y : ℂ) ≠ 0 := by
    have : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
    exact mul_ne_zero two_ne_zero this
  have h3 := h1.div h2 hy'
  refine h3.congr_deriv ?_
  rw [Wt_second_order hl hψ hW hv hk hα, bT_log_half hl hψ hW hy]
  have : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  field_simp
  push_cast
  ring

/- English proof (translation)
The claim follows from `hasDerivAt_comp_log hy (hasDerivAt_Wt hl hv (Real.log y / 2)) rfl`.
-/
theorem hasDerivAt_Wt_y {v : H} (hv : IsSm σ v) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun y => Wt σ l v (Real.log y / 2))
      (Wt σ l (dπ σ lH v) (Real.log y / 2) / (2 * y)) y :=
  hasDerivAt_comp_log hy (hasDerivAt_Wt hl hv (Real.log y / 2)) rfl

/- English proof (translation)
Establish `hc : ContinuousOn (fun y : ℝ => (y : ℂ)) (Ioi 0)` using `Complex.continuous_ofReal.continuousOn`. Use `(continuousOn_const.add (continuousOn_const.div hc fun y hy => ?_)).add (continuousOn_const.div (hc.pow 2) fun y hy => ?_)` and prove the remaining obligations. Conclude with `(ne_of_gt hy)` after adjusting the coercions. Conclude with `pow_ne_zero 2 (by exact_mod_cast (ne_of_gt hy))`.
-/
theorem continuousOn_q (θ : ℝ) (A B : ℂ) :
    ContinuousOn (fun y : ℝ => (((θ ^ 2 : ℝ) : ℂ) + A / y + B / y ^ 2)) (Ioi 0) := by
  have hc : ContinuousOn (fun y : ℝ => (y : ℂ)) (Ioi 0) := Complex.continuous_ofReal.continuousOn
  refine (continuousOn_const.add (continuousOn_const.div hc fun y hy => ?_)).add
    (continuousOn_const.div (hc.pow 2) fun y hy => ?_)
  · exact_mod_cast (ne_of_gt hy)
  · exact pow_ne_zero 2 (by exact_mod_cast (ne_of_gt hy))

end Whittaker

/- English proof (translation)
Take `⟨Y₀, hY₀, hre, hnorm⟩` from `q_bounds hθ (-(θ * k) : ℂ) ((k * (k + 2) + α) / 4)`. Take `⟨Cl, Nl, hCl⟩` from `exists_Wt_bound_y hl hv`. Take `⟨Cm, Nm, hCm⟩` from `exists_Wt_bound_y hm hv`. Establish `hY : 0 < max Y₀ 1` using `lt_of_lt_of_le one_pos (le_max_right _ _)`. Establish `key` using `ArchWhittaker.wronskian_eq_zero_of_moderate (Y₀ := max Y₀ 1) (q := fun y : ℝ => (((θ ^ 2 : ℝ) : ℂ) + (-(θ * k) : ℂ) / y + ((k * (k + 2) + α) / 4) / y ^ 2)) hY (c := |θ| / 2) (by positivity) (fun y hy => hre y (le_trans (le_max_left _ _) hy)) (fun y hy => hnorm y (le_trans (le_max …`.

Simplify using `only [Real.log_one, zero_div, Complex.ofReal_one, mul_one] at key`. Take the linear combination `2 * key`.
-/
theorem Wt_wronskian {l m : hGL2.smoothVectors (πσ σ) →ₗ[ℂ] ℂ}
    (hl : hGL2.IsSmoothContinuous (πσ σ) l) (hm : hGL2.IsSmoothContinuous (πσ σ) m)
    {ψ : ℝ → ℂ} {θ : ℝ} (hθ : θ ≠ 0) (hψ : HasDerivAt ψ (I * θ) 0)
    (hWl : ∀ (x : ℝ) (w : H), IsSm σ w → lT σ l (σ (nMat x) w) = ψ x * lT σ l w)
    (hWm : ∀ (x : ℝ) (w : H), IsSm σ w → lT σ m (σ (nMat x) w) = ψ x * lT σ m w)
    {k : ℤ} {v : H} (hv : IsSm σ v) (hk : v ∈ weightSpace σ k) {α : ℂ}
    (hα : Lop σ (Rop σ v) = α • v) :
    Wt σ l v 0 * Wt σ m (dπ σ lH v) 0 - Wt σ l (dπ σ lH v) 0 * Wt σ m v 0 = 0 := by
  obtain ⟨Y₀, hY₀, hre, hnorm⟩ := q_bounds hθ (-(θ * k) : ℂ) ((k * (k + 2) + α) / 4)
  obtain ⟨Cl, Nl, hCl⟩ := exists_Wt_bound_y hl hv
  obtain ⟨Cm, Nm, hCm⟩ := exists_Wt_bound_y hm hv
  have hY : 0 < max Y₀ 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have key := ArchWhittaker.wronskian_eq_zero_of_moderate (Y₀ := max Y₀ 1)
    (q := fun y : ℝ => (((θ ^ 2 : ℝ) : ℂ) + (-(θ * k) : ℂ) / y + ((k * (k + 2) + α) / 4) / y ^ 2))
    hY (c := |θ| / 2) (by positivity)
    (fun y hy => hre y (le_trans (le_max_left _ _) hy))
    (fun y hy => hnorm y (le_trans (le_max_left _ _) hy))
    (fun y hy => hasDerivAt_Wt_y hl hψ hWl hv hy)
    (fun y hy => hasDerivAt_Wt_y' hl hψ hWl hv hk hα hy)
    (fun y hy => hasDerivAt_Wt_y hm hψ hWm hv hy)
    (fun y hy => hasDerivAt_Wt_y' hm hψ hWm hv hk hα hy)
    ⟨Cl, Nl, fun y hy => hCl y (le_trans (le_max_right _ _) hy)⟩
    ⟨Cm, Nm, fun y hy => hCm y (le_trans (le_max_right _ _) hy)⟩
  simp only [Real.log_one, zero_div, Complex.ofReal_one, mul_one] at key
  linear_combination 2 * key

/- English proof (translation)
Establish `key` using `ArchWhittaker.eq_zero_of_ode (q := fun y : ℝ => (((θ ^ 2 : ℝ) : ℂ) + (-(θ * k) : ℂ) / y + ((k * (k + 2) + α) / 4) / y ^ 2)) (continuousOn_q hl hψ hW θ _ _) (fun y hy => hasDerivAt_Wt_y hl hψ hW hv hy) (fun y hy => hasDerivAt_Wt_y' hl hψ hW hv hk hα hy) (by simp [h0]) (by simp [h1 …`. Introduce `t`. Use `key (Real.exp (2 * t)) (Real.exp_pos _)` as an intermediate fact. Rewrite `this` using `[Real.log_exp, mul_div_cancel_left₀ t two_ne_zero]`. Then use the resulting hypothesis.
-/
theorem Wt_eq_zero_of_init {l : hGL2.smoothVectors (πσ σ) →ₗ[ℂ] ℂ}
    (hl : hGL2.IsSmoothContinuous (πσ σ) l) {ψ : ℝ → ℂ} {θ : ℝ} (hψ : HasDerivAt ψ (I * θ) 0)
    (hW : ∀ (x : ℝ) (w : H), IsSm σ w → lT σ l (σ (nMat x) w) = ψ x * lT σ l w)
    {k : ℤ} {v : H} (hv : IsSm σ v) (hk : v ∈ weightSpace σ k) {α : ℂ}
    (hα : Lop σ (Rop σ v) = α • v) (h0 : Wt σ l v 0 = 0) (h1 : Wt σ l (dπ σ lH v) 0 = 0) :
    ∀ t, Wt σ l v t = 0 := by
  have key := ArchWhittaker.eq_zero_of_ode
    (q := fun y : ℝ => (((θ ^ 2 : ℝ) : ℂ) + (-(θ * k) : ℂ) / y + ((k * (k + 2) + α) / 4) / y ^ 2))
    (continuousOn_q hl hψ hW θ _ _)
    (fun y hy => hasDerivAt_Wt_y hl hψ hW hv hy)
    (fun y hy => hasDerivAt_Wt_y' hl hψ hW hv hk hα hy)
    (by simp [h0]) (by simp [h1])
  intro t
  have := key (Real.exp (2 * t)) (Real.exp_pos _)
  rwa [Real.log_exp, mul_div_cancel_left₀ t two_ne_zero] at this

/- English proof (translation)
Establish `hF : ∀ y > 0, HasDerivAt (fun y => Wt σ l v (Real.log y / 2)) ((((k : ℝ) / (2 * y) + (-θ) : ℝ) : ℂ) * Wt σ l v (Real.log y / 2)) y`. Introduce `y hy`. Use `(hasDerivAt_Wt_y hl hψ hW hv hy).congr_deriv ?_` and prove the remaining obligations. Establish `e` using `Wt_Lop hl hψ hW hv hk (Real.log y / 2)`. Rewrite `e` using `[hL, Wt_zero, bT_log_half hl hψ hW hy]`.

Rewrite using `[show Wt σ l (dπ σ lH v) (Real.log y / 2) = (-2 * θ * y + k) * Wt σ l v (Real.log y / 2) by`. Take the linear combination `-e]`. Establish `: (y : ℂ) ≠ 0` using `by exact_mod_cast hy.ne'`. Use `push_cast`. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree. Take `⟨C, N, hC⟩` from `exists_Wt_bound_y hl hv`. Establish `key` using `ArchWhittaker.eq_zero_of_first_order (m := k) (b := -θ) (by linarith) hF ⟨C, N, hC⟩`. Introduce `t`. Use `key (Real.exp (2 * t)) (Real.exp_pos _)` as an intermediate fact.

Rewrite `this` using `[Real.log_exp, mul_div_cancel_left₀ t two_ne_zero]`. Then use the resulting hypothesis.
-/
theorem Wt_eq_zero_of_Lop {l : hGL2.smoothVectors (πσ σ) →ₗ[ℂ] ℂ}
    (hl : hGL2.IsSmoothContinuous (πσ σ) l) {ψ : ℝ → ℂ} {θ : ℝ} (hθ : θ < 0)
    (hψ : HasDerivAt ψ (I * θ) 0)
    (hW : ∀ (x : ℝ) (w : H), IsSm σ w → lT σ l (σ (nMat x) w) = ψ x * lT σ l w)
    {k : ℤ} {v : H} (hv : IsSm σ v) (hk : v ∈ weightSpace σ k) (hL : Lop σ v = 0) :
    ∀ t, Wt σ l v t = 0 := by
  have hF : ∀ y > 0, HasDerivAt (fun y => Wt σ l v (Real.log y / 2))
      ((((k : ℝ) / (2 * y) + (-θ) : ℝ) : ℂ) * Wt σ l v (Real.log y / 2)) y := by
    intro y hy
    refine (hasDerivAt_Wt_y hl hψ hW hv hy).congr_deriv ?_
    have e := Wt_Lop hl hψ hW hv hk (Real.log y / 2)
    rw [hL, Wt_zero, bT_log_half hl hψ hW hy] at e
    rw [show Wt σ l (dπ σ lH v) (Real.log y / 2) = (-2 * θ * y + k) * Wt σ l v (Real.log y / 2) by
      linear_combination -e]
    have : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
    push_cast
    field_simp
    ring
  obtain ⟨C, N, hC⟩ := exists_Wt_bound_y hl hv
  have key := ArchWhittaker.eq_zero_of_first_order (m := k) (b := -θ) (by linarith) hF ⟨C, N, hC⟩
  intro t
  have := key (Real.exp (2 * t)) (Real.exp_pos _)
  rwa [Real.log_exp, mul_div_cancel_left₀ t two_ne_zero] at this

/- English proof (translation)
Establish `hF : ∀ y > 0, HasDerivAt (fun y => Wt σ l v (Real.log y / 2)) (((((-k : ℤ) : ℝ) / (2 * y) + θ : ℝ) : ℂ) * Wt σ l v (Real.log y / 2)) y`. Introduce `y hy`. Use `(hasDerivAt_Wt_y hl hψ hW hv hy).congr_deriv ?_` and prove the remaining obligations. Establish `e` using `Wt_Rop hl hψ hW hv hk (Real.log y / 2)`. Rewrite `e` using `[hR, Wt_zero, bT_log_half hl hψ hW hy]`.

Rewrite using `[show Wt σ l (dπ σ lH v) (Real.log y / 2) = -((-2 * θ * y + k) * Wt σ l v (Real.log y / 2)) by`. Take the linear combination `-e]`. Establish `: (y : ℂ) ≠ 0` using `by exact_mod_cast hy.ne'`. Use `push_cast`. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree. Take `⟨C, N, hC⟩` from `exists_Wt_bound_y hl hv`. Establish `key` using `ArchWhittaker.eq_zero_of_first_order (m := -k) (b := θ) hθ hF ⟨C, N, hC⟩`. Introduce `t`. Use `key (Real.exp (2 * t)) (Real.exp_pos _)` as an intermediate fact.

Rewrite `this` using `[Real.log_exp, mul_div_cancel_left₀ t two_ne_zero]`. Then use the resulting hypothesis.
-/
theorem Wt_eq_zero_of_Rop {l : hGL2.smoothVectors (πσ σ) →ₗ[ℂ] ℂ}
    (hl : hGL2.IsSmoothContinuous (πσ σ) l) {ψ : ℝ → ℂ} {θ : ℝ} (hθ : 0 < θ)
    (hψ : HasDerivAt ψ (I * θ) 0)
    (hW : ∀ (x : ℝ) (w : H), IsSm σ w → lT σ l (σ (nMat x) w) = ψ x * lT σ l w)
    {k : ℤ} {v : H} (hv : IsSm σ v) (hk : v ∈ weightSpace σ k) (hR : Rop σ v = 0) :
    ∀ t, Wt σ l v t = 0 := by
  have hF : ∀ y > 0, HasDerivAt (fun y => Wt σ l v (Real.log y / 2))
      (((((-k : ℤ) : ℝ) / (2 * y) + θ : ℝ) : ℂ) * Wt σ l v (Real.log y / 2)) y := by
    intro y hy
    refine (hasDerivAt_Wt_y hl hψ hW hv hy).congr_deriv ?_
    have e := Wt_Rop hl hψ hW hv hk (Real.log y / 2)
    rw [hR, Wt_zero, bT_log_half hl hψ hW hy] at e
    rw [show Wt σ l (dπ σ lH v) (Real.log y / 2) = -((-2 * θ * y + k) * Wt σ l v (Real.log y / 2)) by
      linear_combination -e]
    have : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
    push_cast
    field_simp
    ring
  obtain ⟨C, N, hC⟩ := exists_Wt_bound_y hl hv
  have key := ArchWhittaker.eq_zero_of_first_order (m := -k) (b := θ) hθ hF ⟨C, N, hC⟩
  intro t
  have := key (Real.exp (2 * t)) (Real.exp_pos _)
  rwa [Real.log_exp, mul_div_cancel_left₀ t two_ne_zero] at this

end GroundTheory.Automorphic.ArchWhittaker
