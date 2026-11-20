import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsThetaMeanSquareNorm
import Development.AutomorphicSpectrum.Statements.GeometryStatements.ZhangDimensionPushDownGrassmannianHeightBounds
import GroundTheory.HeightsAndTheta.Heights.KernelsLattice
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsBundles
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.LevelThreeSeparatesTangents

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Sl.Jump

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl
open Filter Topology

/- English proof (translation)
Establish `h1` using `natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (n := n) hf`. Establish `h2` using `natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (n := n + 1) hf`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `⟨h1.1 h.ge, fun hn => ?_⟩` and prove the remaining obligations.

Establish `h3 : ((n + 1 : ℕ) : ℕ∞) ≤ analyticOrderAt f 0` using `h2.2 fun i hi => by`. Break down `Nat.lt_succ_iff_lt_or_eq.1 hi with h' | rfl` into its components or cases. Conclude with `h1.1 h.ge i h'`. Conclude with `hn`. Rewrite `h3` using `[h]`.

Conclude with `absurd (Nat.cast_le.1 h3) (by omega)`. Introduce and unpack `⟨ha, hb⟩`. Establish `hle` using `h1.2 ha`. Establish `hnot : ¬ ((n + 1 : ℕ) : ℕ∞) ≤ analyticOrderAt f 0` using `fun h => hb (h2.1 h n (Nat.lt_succ_self n))`. Generalize the expression as in `analyticOrderAt f 0 = x at hle hnot ⊢`.

Proceed by induction on `x using ENat.recTopCoe with`. Consider the case `top => simp at hnot`. Consider the case `coe x`. Establish `e1 : n ≤ x` using `by exact_mod_cast hle`. Establish `e2 : ¬ n + 1 ≤ x` using `by exact_mod_cast hnot`.

Establish `: x = n` using `by omega`. Rewrite using `[this]`.
-/
theorem analyticOrderAt_eq_iff {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (n : ℕ) :
    analyticOrderAt f 0 = n ↔ (∀ k < n, iteratedDeriv k f 0 = 0) ∧ iteratedDeriv n f 0 ≠ 0 := by
  have h1 := natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (n := n) hf
  have h2 := natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (n := n + 1) hf
  constructor
  · intro h
    refine ⟨h1.1 h.ge, fun hn => ?_⟩
    have h3 : ((n + 1 : ℕ) : ℕ∞) ≤ analyticOrderAt f 0 := h2.2 fun i hi => by
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h' | rfl
      · exact h1.1 h.ge i h'
      · exact hn
    rw [h] at h3
    exact absurd (Nat.cast_le.1 h3) (by omega)
  · rintro ⟨ha, hb⟩
    have hle := h1.2 ha
    have hnot : ¬ ((n + 1 : ℕ) : ℕ∞) ≤ analyticOrderAt f 0 := fun h => hb (h2.1 h n (Nat.lt_succ_self n))
    generalize analyticOrderAt f 0 = x at hle hnot ⊢
    induction x using ENat.recTopCoe with
    | top => simp at hnot
    | coe x =>
      have e1 : n ≤ x := by exact_mod_cast hle
      have e2 : ¬ n + 1 ≤ x := by exact_mod_cast hnot
      have : x = n := by omega
      rw [this]

/- English proof (translation)
Establish `aφ : AnalyticAt ℂ φ 0` using `hφ.analyticAt 0`. Establish `aψ : AnalyticAt ℂ ψ 0` using `hψ.analyticAt 0`. Establish `oφ : analyticOrderAt φ 0 = 0` using `aφ.analyticOrderAt_eq_zero.2 h0`. Establish `oψ : analyticOrderAt ψ 0 = ((1 : ℕ) : ℕ∞)`. Use `(analyticOrderAt_eq_iff aψ 1).2 ⟨fun k hk => ?_, ?_⟩` and prove the remaining obligations.

Take `rfl : k = 0` from `by omega`. Simplify using `using h1`. Simplify `h2` using `[iteratedDeriv_one]`. Rewrite using `[analyticOrderAt_mul (aφ.pow m) (aψ.pow i), analyticOrderAt_pow aφ, analyticOrderAt_pow aψ, oφ, oψ]`. Simplify using the standard rewrite rules.
-/
theorem order_of_product {φ ψ : ℂ → ℂ} (hφ : Differentiable ℂ φ) (hψ : Differentiable ℂ ψ) (h0 : φ 0 ≠ 0)
    (h1 : ψ 0 = 0) (h2 : deriv ψ 0 ≠ 0) (m i : ℕ) : analyticOrderAt (φ ^ m * ψ ^ i) 0 = i := by
  have aφ : AnalyticAt ℂ φ 0 := hφ.analyticAt 0
  have aψ : AnalyticAt ℂ ψ 0 := hψ.analyticAt 0
  have oφ : analyticOrderAt φ 0 = 0 := aφ.analyticOrderAt_eq_zero.2 h0
  have oψ : analyticOrderAt ψ 0 = ((1 : ℕ) : ℕ∞) := by
    refine (analyticOrderAt_eq_iff aψ 1).2 ⟨fun k hk => ?_, ?_⟩
    · obtain rfl : k = 0 := by omega
      simpa using h1
    · simpa [iteratedDeriv_one] using h2
  rw [analyticOrderAt_mul (aφ.pow m) (aψ.pow i), analyticOrderAt_pow aφ, analyticOrderAt_pow aψ, oφ, oψ]
  simp

def tri {g : ℕ} (θ : (Fin g → ℂ) → ℂ) (p q w : Fin g → ℂ) : ℂ := θ (w + p) * θ (w + q) * θ (w - p - q)

/- English proof (translation)
Simplify using `[tri]`.
-/
theorem tri_zero {g : ℕ} (θ : (Fin g → ℂ) → ℂ) (p q : Fin g → ℂ) : tri θ p q 0 = θ p * θ q * θ (-p - q) := by
  simp [tri]

/- English proof (translation)
Establish `han : AnalyticOnNhd ℂ θ Set.univ` using `fun x _ => SCV.analyticAt_of_differentiableOn (s := Set.univ) hd.differentiableOn univ_mem`. Use `⟨isOpen_ne_fun hd.continuous continuous_const, fun x => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hx`. Apply `h0` to reduce the goal to its premises. Use `han.eq_of_eventuallyEq (g := 0) (z₀ := x) analyticOnNhd_const ?_` and prove the remaining obligations.

Use `filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hx] with y hy`. Assume the negation of the conclusion as `hy'`. Conclude with `hy (subset_closure hy')`.
-/
theorem dense_ne {g : ℕ} {θ : (Fin g → ℂ) → ℂ} (hd : Differentiable ℂ θ) (h0 : θ ≠ 0) :
    IsOpen {x | θ x ≠ 0} ∧ Dense {x | θ x ≠ 0} := by
  have han : AnalyticOnNhd ℂ θ Set.univ := fun x _ =>
    SCV.analyticAt_of_differentiableOn (s := Set.univ) hd.differentiableOn univ_mem
  refine ⟨isOpen_ne_fun hd.continuous continuous_const, fun x => ?_⟩
  by_contra hx
  apply h0
  refine han.eq_of_eventuallyEq (g := 0) (z₀ := x) analyticOnNhd_const ?_
  filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hx] with y hy
  by_contra hy'
  exact hy (subset_closure hy')

section Frame

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {P : RigLB G} {z : Sp ℂ ⟶ S} {g : ℕ}
  (a : ArchFrame P z g)

/- English proof (translation)
Simplify using `[ArchFrame.herm, add_dotProduct]`.
-/
theorem herm_add_left (w w' l : Fin g → ℂ) : a.herm (w + w') l = a.herm w l + a.herm w' l := by
  simp [ArchFrame.herm, add_dotProduct]

/- English proof (translation)
Simplify using `[ArchFrame.herm, smul_dotProduct]`.
-/
theorem herm_smul_left (t : ℂ) (w l : Fin g → ℂ) : a.herm (t • w) l = t * a.herm w l := by
  simp [ArchFrame.herm, smul_dotProduct]

/- English proof (translation)
Simplify using `[ArchFrame.herm, Matrix.mulVec_add, dotProduct_add]`.
-/
theorem herm_add_right (w l l' : Fin g → ℂ) : a.herm w (l + l') = a.herm w l + a.herm w l' := by
  simp [ArchFrame.herm, Matrix.mulVec_add, dotProduct_add]

/- English proof (translation)
Simplify using `[ArchFrame.herm, star_smul, Matrix.mulVec_smul, dotProduct_smul]`.
-/
theorem herm_smul_right (t : ℂ) (w l : Fin g → ℂ) : a.herm w (t • l) = star t * a.herm w l := by
  simp [ArchFrame.herm, star_smul, Matrix.mulVec_smul, dotProduct_smul]

/- English proof (translation)
Simplify using `only [ArchFrame.herm, add_dotProduct, sub_dotProduct]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem herm_tri (w p q l : Fin g → ℂ) :
    a.herm (w + p) l + a.herm (w + q) l + a.herm (w - p - q) l = 3 * a.herm w l := by
  simp only [ArchFrame.herm, add_dotProduct, sub_dotProduct]
  ring

/- English proof (translation)
Introduce `h`. Use `a.ah.2.1 c hc` as an intermediate fact. Establish `h' : c ⬝ᵥ a.Hm.mulVec (star c) = 0` using `h`. Rewrite `this` using `[h']`. Simplify using `at this`.
-/
theorem herm_self_ne {c : Fin g → ℂ} (hc : c ≠ 0) : a.herm c c ≠ 0 := by
  intro h
  have := a.ah.2.1 c hc
  have h' : c ⬝ᵥ a.Hm.mulVec (star c) = 0 := h
  rw [h'] at this
  simp at this

/- English proof (translation)
Introduce `h`. Use `a.ah.2.2.1 l` as an intermediate fact. Simplify using `[h] at this`.
-/
theorem chi_ne (l : a.u.Λ) : a.χ l ≠ 0 := by
  intro h
  have := a.ah.2.2.1 l
  simp [h] at this

/- English proof (translation)
Use `⟨(h.1.const_mul c).sub (h'.1.const_mul c'), fun l w => ?_⟩` and prove the remaining obligations. Simplify using `only [h.2 l w, h'.2 l w]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem IsTheta.lin {n : ℕ} {θ θ' : (Fin g → ℂ) → ℂ} (h : a.IsTheta n θ) (h' : a.IsTheta n θ') (c c' : ℂ) :
    a.IsTheta n (fun w => c * θ w - c' * θ' w) := by
  refine ⟨(h.1.const_mul c).sub (h'.1.const_mul c'), fun l w => ?_⟩
  simp only [h.2 l w, h'.2 l w]
  ring

/- English proof (translation)
Use `⟨h.1.mul h'.1, fun l w => ?_⟩` and prove the remaining obligations. Simplify using `only [h.2 l w, h'.2 l w]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem IsTheta.mul {m n : ℕ} {θ θ' : (Fin g → ℂ) → ℂ} (h : a.IsTheta m θ) (h' : a.IsTheta n θ') :
    a.IsTheta (m + n) (fun w => θ w * θ' w) := by
  refine ⟨h.1.mul h'.1, fun l w => ?_⟩
  simp only [h.2 l w, h'.2 l w]
  ring

/- English proof (translation)
Use `⟨h.1.pow k, fun l w => ?_⟩` and prove the remaining obligations. Simplify using `only [h.2 l w]`. Rewrite using `[mul_pow, pow_mul]`.
-/
theorem IsTheta.pow {n : ℕ} {θ : (Fin g → ℂ) → ℂ} (h : a.IsTheta n θ) (k : ℕ) :
    a.IsTheta (n * k) (fun w => θ w ^ k) := by
  refine ⟨h.1.pow k, fun l w => ?_⟩
  simp only [h.2 l w]
  rw [mul_pow, pow_mul]

/- English proof (translation)
Establish `hd` using `h.1`. Use `⟨?_, fun l w => ?_⟩` and prove the remaining obligations. Unfold `tri`. Conclude with `((hd.comp (differentiable_id.add_const p)).mul (hd.comp (differentiable_id.add_const q))).mul (hd.comp ((differentiable_id.sub_const p).sub_const q))`. Establish `e1 : w + (l : Fin g → ℂ) + p = (w + p) + l` using `by abel`.

Establish `e2 : w + (l : Fin g → ℂ) + q = (w + q) + l` using `by abel`. Establish `e3 : w + (l : Fin g → ℂ) - p - q = (w - p - q) + l` using `by abel`. Simplify using `only [tri]`. Rewrite using `[e1, e2, e3, h.2 l (w + p), h.2 l (w + q), h.2 l (w - p - q)]`. Establish `hE : Complex.exp (Real.pi * a.herm (w + p) l + Real.pi / 2 * a.herm l l) * Complex.exp (Real.pi * a.herm (w + q) l + Real.pi / 2 * a.herm l l) * Complex.exp (Real.pi * a.herm (w - p - q) l + Real.pi / 2 * a.herm l l) = Complex.exp (Real.pi * a.herm w l + Real.pi / 2 * a.herm l l) …`.

Rewrite using `[← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_nat_mul]`. Use `congr 1`. Use `push_cast`. Take the linear combination `(Real.pi : ℂ) * herm_tri a w p q l`. Simplify using `only [pow_one, mul_pow]`.

Take the linear combination `(a.χ l ^ 3 * θ (w + p) * θ (w + q) * θ (w - p - q)) * hE`.
-/
theorem isTheta_tri {θ : (Fin g → ℂ) → ℂ} (h : a.IsTheta 1 θ) (p q : Fin g → ℂ) : a.IsTheta 3 (tri θ p q) := by
  have hd := h.1
  refine ⟨?_, fun l w => ?_⟩
  · unfold tri
    exact ((hd.comp (differentiable_id.add_const p)).mul (hd.comp (differentiable_id.add_const q))).mul
      (hd.comp ((differentiable_id.sub_const p).sub_const q))
  · have e1 : w + (l : Fin g → ℂ) + p = (w + p) + l := by abel
    have e2 : w + (l : Fin g → ℂ) + q = (w + q) + l := by abel
    have e3 : w + (l : Fin g → ℂ) - p - q = (w - p - q) + l := by abel
    simp only [tri]
    rw [e1, e2, e3, h.2 l (w + p), h.2 l (w + q), h.2 l (w - p - q)]
    have hE : Complex.exp (Real.pi * a.herm (w + p) l + Real.pi / 2 * a.herm l l) *
        Complex.exp (Real.pi * a.herm (w + q) l + Real.pi / 2 * a.herm l l) *
        Complex.exp (Real.pi * a.herm (w - p - q) l + Real.pi / 2 * a.herm l l) =
        Complex.exp (Real.pi * a.herm w l + Real.pi / 2 * a.herm l l) ^ 3 := by
      rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_nat_mul]
      congr 1
      push_cast
      linear_combination (Real.pi : ℂ) * herm_tri a w p q l
    simp only [pow_one, mul_pow]
    linear_combination (a.χ l ^ 3 * θ (w + p) * θ (w + q) * θ (w - p - q)) * hE

/- English proof (translation)
Take `⟨hd, hl⟩` from `h`. Set `A₀ : (Fin g → ℂ) →ₗ[ℂ] ℂ` to `{ toFun := fun w => a.herm w l map_add' := fun x y => herm_add_left a x y l map_smul' := fun t x => by simpa using herm_smul_left a t x l }`. Set `A : (Fin g → ℂ) →L[ℂ] ℂ` to `LinearMap.toContinuousLinearMap A₀`. Establish `hA : ∀ w, A w = a.herm w l` using `fun w => rfl`. Establish `h1 : HasFDerivAt (fun v => θ (v + l)) (fderiv ℂ θ (p + l)) p` using `(hasFDerivAt_comp_add_right (l : Fin g → ℂ)).2 (hd _).hasFDerivAt`.

Establish `h2` using `((((A.hasFDerivAt (x := p)).const_mul (Real.pi : ℂ)).add_const ((Real.pi : ℂ) / 2 * a.herm l l)).cexp.const_mul (a.χ l)).mul (hd p).hasFDerivAt`. Establish `h3 : (fun v => θ (v + l)) = fun v => a.χ l * Complex.exp (Real.pi * A v + Real.pi / 2 * a.herm l l) * θ v`. Use function extensionality and compare the values at `v`. Rewrite using `[hl l v, pow_one, hA]`. Rewrite `h1` using `[h3]`.

Establish `h4` using `congrArg (fun B => B c) (h1.unique h2)`. Establish `h5 : θ (p + l) = a.χ l * Complex.exp (Real.pi * A p + Real.pi / 2 * a.herm l l) * θ p` using `congrFun h3 p`. Rewrite using `[h4, h5]`. Simplify using `[hA]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem fderiv_law {θ : (Fin g → ℂ) → ℂ} (h : a.IsTheta 1 θ) (l : a.u.Λ) (p c : Fin g → ℂ) :
    fderiv ℂ θ (p + l) c * θ p = θ (p + l) * (Real.pi * a.herm c l * θ p + fderiv ℂ θ p c) := by
  obtain ⟨hd, hl⟩ := h
  let A₀ : (Fin g → ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun w => a.herm w l
      map_add' := fun x y => herm_add_left a x y l
      map_smul' := fun t x => by simpa using herm_smul_left a t x l }
  let A : (Fin g → ℂ) →L[ℂ] ℂ := LinearMap.toContinuousLinearMap A₀
  have hA : ∀ w, A w = a.herm w l := fun w => rfl
  have h1 : HasFDerivAt (fun v => θ (v + l)) (fderiv ℂ θ (p + l)) p :=
    (hasFDerivAt_comp_add_right (l : Fin g → ℂ)).2 (hd _).hasFDerivAt
  have h2 := ((((A.hasFDerivAt (x := p)).const_mul (Real.pi : ℂ)).add_const
    ((Real.pi : ℂ) / 2 * a.herm l l)).cexp.const_mul (a.χ l)).mul (hd p).hasFDerivAt
  have h3 : (fun v => θ (v + l)) = fun v => a.χ l * Complex.exp (Real.pi * A v + Real.pi / 2 * a.herm l l) * θ v := by
    funext v
    rw [hl l v, pow_one, hA]
  rw [h3] at h1
  have h4 := congrArg (fun B => B c) (h1.unique h2)
  have h5 : θ (p + l) = a.χ l * Complex.exp (Real.pi * A p + Real.pi / 2 * a.herm l l) * θ p := congrFun h3 p
  rw [h4, h5]
  simp [hA]
  ring

/- English proof (translation)
Establish `hd : Differentiable ℂ θ` using `hθ.1`. Establish `han : AnalyticOnNhd ℂ θ Set.univ` using `fun x _ => SCV.analyticAt_of_differentiableOn (s := Set.univ) hd.differentiableOn univ_mem`. Take `⟨ho, hden⟩` from `dense_ne hd h0`. Use `set U : Set (Fin g → ℂ) := {x | θ x ≠ 0} with hU`. Establish `hder : ∀ p q, fderiv ℂ (tri θ p q) 0 c = fderiv ℂ θ p c * θ q * θ (-p - q) + θ p * fderiv ℂ θ q c * θ (-p - q) + θ p * θ q * fderiv ℂ θ (-p - q) c`.

Introduce `p q`. Establish `ht : ∀ x, HasFDerivAt (fun v => θ (v + x)) (fderiv ℂ θ x) 0` using `fun x => (hasFDerivAt_comp_add_right x).2 (by simpa using (hd x).hasFDerivAt)`. Establish `e : tri θ p q = ((fun v => θ (v + p)) * fun v => θ (v + q)) * fun v => θ (v + (-p - q))`. Use function extensionality and compare the values at `v`. Simplify using `only [tri, Pi.mul_apply]`.

Use `congr 2`. Normalize the expressions using the abelian group laws. Rewrite using `[e, (((ht p).mul (ht q)).mul (ht (-p - q))).fderiv]`. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.

Use `set f : (Fin g → ℂ) → ℂ := fun x => fderiv ℂ θ x c / θ x with hfdef`. Establish `hf : ∀ p ∈ U, ∀ q ∈ U, -p - q ∈ U → c₀ + f p + f q + f (-p - q) = 0`. Introduce `p hp q hq hpq`. Establish `hp' : θ p ≠ 0` using `hp`. Establish `hq' : θ q ≠ 0` using `hq`.

Establish `hpq' : θ (-p - q) ≠ 0` using `hpq`. Use `h p q` as an intermediate fact. Rewrite `this` using `[hder, tri_zero]`. Simplify using `only [hfdef]`. Clear the denominators using the available nonvanishing facts.

Take the linear combination `this`. Take `⟨a₀, ha₀⟩` from `hden.nonempty`. Establish `ha₀' : θ a₀ ≠ 0` using `ha₀`. Establish `hdf : DifferentiableAt ℂ f a₀`. Simplify using `only [hfdef, div_eq_mul_inv]`.

Conclude with `(((han a₀ trivial).fderiv.differentiableAt).clm_apply (differentiableAt_const c)).mul ((hd a₀).inv ha₀')`. Take `⟨L, hL⟩` from `GlobalTheory.exists_linear_increment ho hden hf ha₀ hdf`. Establish `hlat : ∀ l : a.u.Λ, L l = Real.pi * a.herm c l`. Introduce `l`. Establish `hne : θ (a₀ + l) ≠ 0`.

Rewrite using `[hθ.2 l a₀, pow_one]`. Conclude with `mul_ne_zero (mul_ne_zero (chi_ne a l) (Complex.exp_ne_zero _)) ha₀'`. Rewrite using `[← hL a₀ l ha₀ hne]`. Use `fderiv_law a hθ l a₀ c` as an intermediate fact. Simplify using `only [hfdef]`.

Clear the denominators using the available nonvanishing facts. Take the linear combination `this`. Set `M : (Fin g → ℂ) →ₗ[ℝ] ℂ` to `{ toFun := fun v => Real.pi * a.herm c v map_add' := fun x y => by rw [herm_add_right]; ring map_smul' := fun r x => by`. Establish `: r • x = (r : ℂ) • x`. Use function extensionality and compare the values at `j`.

Simplify using the standard rewrite rules. Rewrite using `[this, herm_smul_right]`. Simplify using the standard rewrite rules. Use `ring }`. Establish `hM : (L : (Fin g → ℂ) →ₗ[ℂ] ℂ).restrictScalars ℝ = M` using `LinearMap.ext_on a.u.full fun x hx => hlat ⟨x, hx⟩`.

Establish `hLM : ∀ v, L v = Real.pi * a.herm c v` using `fun v => LinearMap.congr_fun hM v`. Assume the negation of the conclusion as `hc`. Establish `h1` using `hLM (Complex.I • c)`. Rewrite `h1` using `[map_smul, hLM, herm_smul_right, smul_eq_mul]`. Establish `h2 : (2 * Complex.I * Real.pi) * a.herm c c = 0`.

Establish `: star Complex.I = -Complex.I` using `by simp`. Rewrite `h1` using `[this]`. Take the linear combination `h1`. Establish `h3 : (2 * Complex.I * Real.pi : ℂ) ≠ 0` using `by simp [Real.pi_ne_zero]`. Conclude with `herm_self_ne a hc ((mul_eq_zero.1 h2).resolve_left h3)`.
-/
theorem separates {θ : (Fin g → ℂ) → ℂ} (hθ : a.IsTheta 1 θ) (h0 : θ ≠ 0) (c₀ : ℂ) (c : Fin g → ℂ)
    (h : ∀ p q, c₀ * tri θ p q 0 + fderiv ℂ (tri θ p q) 0 c = 0) : c = 0 := by
  have hd : Differentiable ℂ θ := hθ.1
  have han : AnalyticOnNhd ℂ θ Set.univ := fun x _ =>
    SCV.analyticAt_of_differentiableOn (s := Set.univ) hd.differentiableOn univ_mem
  obtain ⟨ho, hden⟩ := dense_ne hd h0
  set U : Set (Fin g → ℂ) := {x | θ x ≠ 0} with hU
  have hder : ∀ p q, fderiv ℂ (tri θ p q) 0 c =
      fderiv ℂ θ p c * θ q * θ (-p - q) + θ p * fderiv ℂ θ q c * θ (-p - q)
        + θ p * θ q * fderiv ℂ θ (-p - q) c := by
    intro p q
    have ht : ∀ x, HasFDerivAt (fun v => θ (v + x)) (fderiv ℂ θ x) 0 := fun x =>
      (hasFDerivAt_comp_add_right x).2 (by simpa using (hd x).hasFDerivAt)
    have e : tri θ p q = ((fun v => θ (v + p)) * fun v => θ (v + q)) * fun v => θ (v + (-p - q)) := by
      funext v
      simp only [tri, Pi.mul_apply]
      congr 2
      abel
    rw [e, (((ht p).mul (ht q)).mul (ht (-p - q))).fderiv]
    simp
    ring
  set f : (Fin g → ℂ) → ℂ := fun x => fderiv ℂ θ x c / θ x with hfdef
  have hf : ∀ p ∈ U, ∀ q ∈ U, -p - q ∈ U → c₀ + f p + f q + f (-p - q) = 0 := by
    intro p hp q hq hpq
    have hp' : θ p ≠ 0 := hp
    have hq' : θ q ≠ 0 := hq
    have hpq' : θ (-p - q) ≠ 0 := hpq
    have := h p q
    rw [hder, tri_zero] at this
    simp only [hfdef]
    field_simp
    linear_combination this
  obtain ⟨a₀, ha₀⟩ := hden.nonempty
  have ha₀' : θ a₀ ≠ 0 := ha₀
  have hdf : DifferentiableAt ℂ f a₀ := by
    simp only [hfdef, div_eq_mul_inv]
    exact (((han a₀ trivial).fderiv.differentiableAt).clm_apply (differentiableAt_const c)).mul
      ((hd a₀).inv ha₀')
  obtain ⟨L, hL⟩ := GlobalTheory.exists_linear_increment ho hden hf ha₀ hdf
  have hlat : ∀ l : a.u.Λ, L l = Real.pi * a.herm c l := by
    intro l
    have hne : θ (a₀ + l) ≠ 0 := by
      rw [hθ.2 l a₀, pow_one]
      exact mul_ne_zero (mul_ne_zero (chi_ne a l) (Complex.exp_ne_zero _)) ha₀'
    rw [← hL a₀ l ha₀ hne]
    have := fderiv_law a hθ l a₀ c
    simp only [hfdef]
    field_simp
    linear_combination this
  let M : (Fin g → ℂ) →ₗ[ℝ] ℂ :=
    { toFun := fun v => Real.pi * a.herm c v
      map_add' := fun x y => by rw [herm_add_right]; ring
      map_smul' := fun r x => by
        have : r • x = (r : ℂ) • x := by
          funext j
          simp
        rw [this, herm_smul_right]
        simp
        ring }
  have hM : (L : (Fin g → ℂ) →ₗ[ℂ] ℂ).restrictScalars ℝ = M :=
    LinearMap.ext_on a.u.full fun x hx => hlat ⟨x, hx⟩
  have hLM : ∀ v, L v = Real.pi * a.herm c v := fun v => LinearMap.congr_fun hM v
  by_contra hc
  have h1 := hLM (Complex.I • c)
  rw [map_smul, hLM, herm_smul_right, smul_eq_mul] at h1
  have h2 : (2 * Complex.I * Real.pi) * a.herm c c = 0 := by
    have : star Complex.I = -Complex.I := by simp
    rw [this] at h1
    linear_combination h1
  have h3 : (2 * Complex.I * Real.pi : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
  exact herm_self_ne a hc ((mul_eq_zero.1 h2).resolve_left h3)

/- English proof (translation)
Take `⟨ho, hden⟩` from `dense_ne hθ.1 h0`. Take `⟨p, hp⟩` from `hden.nonempty`. Take `⟨q, hq1, hq2, -⟩` from `GlobalTheory.exists_mem_four_of_open_dense ho hden (Homeomorph.refl _) (Homeomorph.subLeft (-p)) (Homeomorph.refl _) (Homeomorph.refl _)`. Establish `hs₀` using `isTheta_tri a hθ p q`. Establish `hne : tri θ p q 0 ≠ 0`.

Rewrite using `[tri_zero]`. Conclude with `mul_ne_zero (mul_ne_zero hp hq1) hq2`. Use `set s₀ := tri θ p q with hs₀def`. Choose the witnesses or unpack the hypotheses as in `⟨p', q', hpq⟩ : ∃ p' q', (-(fderiv ℂ s₀ 0 v) / s₀ 0) * tri θ p' q' 0 + fderiv ℂ (tri θ p' q') 0 v ≠ 0 := by`. Assume the negation of the conclusion as `hall`.

Use `push_neg at hall`. Conclude with `hv (separates a hθ h0 _ v hall)`. Establish `hs` using `isTheta_tri a hθ p' q'`. Use `⟨s₀, fun w => s₀ 0 * tri θ p' q' w - tri θ p' q' 0 * s₀ w, hs₀, IsTheta.lin a hs hs₀ _ _, hne, by ring, ?_⟩` and prove the remaining obligations. Establish `hD` using `(((hs.1 0).hasFDerivAt.const_mul (s₀ 0)).sub ((hs₀.1 0).hasFDerivAt.const_mul (tri θ p' q' 0))).fderiv`.

Establish `hD' : fderiv ℂ (fun w => s₀ 0 * tri θ p' q' w - tri θ p' q' 0 * s₀ w) 0 v = s₀ 0 * fderiv ℂ (tri θ p' q') 0 v - tri θ p' q' 0 * fderiv ℂ s₀ 0 v`. Establish `e : (fun w => s₀ 0 * tri θ p' q' w - tri θ p' q' 0 * s₀ w) = (fun y => s₀ 0 * tri θ p' q' y) - fun y => tri θ p' q' 0 * s₀ y` using `rfl`. Rewrite using `[e]`. Use `congrArg (fun B => B v) hD` as an intermediate fact. Simplify using `using this`.

Rewrite using `[hD']`. Introduce `hz`. Apply `hpq` to reduce the goal to its premises. Clear the denominators using the available nonvanishing facts. Take the linear combination `hz`.
-/
theorem exists_pair {θ : (Fin g → ℂ) → ℂ} (hθ : a.IsTheta 1 θ) (h0 : θ ≠ 0) {v : Fin g → ℂ} (hv : v ≠ 0) :
    ∃ s₀ s₁ : (Fin g → ℂ) → ℂ, a.IsTheta 3 s₀ ∧ a.IsTheta 3 s₁ ∧ s₀ 0 ≠ 0 ∧ s₁ 0 = 0 ∧ fderiv ℂ s₁ 0 v ≠ 0 := by
  obtain ⟨ho, hden⟩ := dense_ne hθ.1 h0
  obtain ⟨p, hp⟩ := hden.nonempty
  obtain ⟨q, hq1, hq2, -⟩ := GlobalTheory.exists_mem_four_of_open_dense ho hden (Homeomorph.refl _)
    (Homeomorph.subLeft (-p)) (Homeomorph.refl _) (Homeomorph.refl _)
  have hs₀ := isTheta_tri a hθ p q
  have hne : tri θ p q 0 ≠ 0 := by
    rw [tri_zero]
    exact mul_ne_zero (mul_ne_zero hp hq1) hq2
  set s₀ := tri θ p q with hs₀def
  obtain ⟨p', q', hpq⟩ : ∃ p' q', (-(fderiv ℂ s₀ 0 v) / s₀ 0) * tri θ p' q' 0 + fderiv ℂ (tri θ p' q') 0 v ≠ 0 := by
    by_contra hall
    push_neg at hall
    exact hv (separates a hθ h0 _ v hall)
  have hs := isTheta_tri a hθ p' q'
  refine ⟨s₀, fun w => s₀ 0 * tri θ p' q' w - tri θ p' q' 0 * s₀ w, hs₀, IsTheta.lin a hs hs₀ _ _, hne, by ring, ?_⟩
  have hD := (((hs.1 0).hasFDerivAt.const_mul (s₀ 0)).sub ((hs₀.1 0).hasFDerivAt.const_mul (tri θ p' q' 0))).fderiv
  have hD' : fderiv ℂ (fun w => s₀ 0 * tri θ p' q' w - tri θ p' q' 0 * s₀ w) 0 v =
      s₀ 0 * fderiv ℂ (tri θ p' q') 0 v - tri θ p' q' 0 * fderiv ℂ s₀ 0 v := by
    have e : (fun w => s₀ 0 * tri θ p' q' w - tri θ p' q' 0 * s₀ w) =
        (fun y => s₀ 0 * tri θ p' q' y) - fun y => tri θ p' q' 0 * s₀ y := rfl
    rw [e]
    have := congrArg (fun B => B v) hD
    simpa using this
  rw [hD']
  intro hz
  apply hpq
  field_simp
  linear_combination hz

end Frame

end GlobalTheory.CompanionTheory.Ar.Sl.Jump

namespace GlobalTheory.CompanionTheory.Ar.Sl.Jump

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

/- English proof (translation)
Introduce `_ _ _ θ v n' i hθ h0 hv hi`. Take `⟨s₀, s₁, h₀, h₁, e₀, e₁, e₂⟩` from `exists_pair a hθ h0 hv`. Establish `hF` using `IsTheta.mul a (IsTheta.pow a h₀ (n' - i)) (IsTheta.pow a h₁ i)`. Establish `hn : 3 * (n' - i) + 3 * i = 3 * n'` using `by omega`. Rewrite `hF` using `[hn]`.

Use `⟨_, hF, ?_⟩` and prove the remaining obligations. Establish `hline : Differentiable ℂ (fun τ : ℂ => τ • v)` using `differentiable_id.smul_const v`. Establish `hφ : Differentiable ℂ (fun τ : ℂ => s₀ (τ • v))` using `h₀.1.comp hline`. Establish `hψ : Differentiable ℂ (fun τ : ℂ => s₁ (τ • v))` using `h₁.1.comp hline`. Establish `hd : deriv (fun τ : ℂ => s₁ (τ • v)) 0 = fderiv ℂ s₁ 0 v`.

Establish `h1 : HasDerivAt (fun τ : ℂ => τ • v) v 0`. Simplify using `using (hasDerivAt_id (0 : ℂ)).smul_const v`. Establish `h2 : HasFDerivAt s₁ (fderiv ℂ s₁ 0) ((0 : ℂ) • v)`. Simplify using `using (h₁.1 0).hasFDerivAt`. Conclude with `(h2.comp_hasDerivAt (0 : ℂ) h1).deriv`.

Establish `ho` using `order_of_product hφ hψ (by simpa using e₀) (by simpa using e₁) (by rwa [hd]) (n' - i) i`. Establish `han : AnalyticAt ℂ ((fun τ : ℂ => s₀ (τ • v)) ^ (n' - i) * (fun τ : ℂ => s₁ (τ • v)) ^ i) 0` using `((hφ.analyticAt 0).pow _).mul ((hψ.analyticAt 0).pow _)`. Conclude with `(analyticOrderAt_eq_iff han i).1 ho`.
-/
theorem lefschetz_direction {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {P : RigLB G} {z : Sp ℂ ⟶ S} {g : ℕ} (a : ArchFrame P z g) : (∀ l l' : a.u.Λ, ∃ k : ℤ, (a.herm l l').im = k) → (∀ w : Fin g → ℂ, (∀ l : a.u.Λ, ∃ k : ℤ, (a.herm w l).im = k) → w ∈ a.u.Λ) → (∀ l l' : a.u.Λ, a.χ (l + l') = a.χ l * a.χ l' * Complex.exp (Real.pi * Complex.I * (a.herm l l').im)) → ∀ (θ : (Fin g → ℂ) → ℂ) (v : Fin g → ℂ) (n' i : ℕ), a.IsTheta 1 θ → θ ≠ 0 → v ≠ 0 → i ≤ n' → ∃ F, a.IsTheta (3 * n') F ∧ (∀ k < i, iteratedDeriv k (fun τ : ℂ => F (τ • v)) 0 = 0) ∧ iteratedDeriv i (fun τ : ℂ => F (τ • v)) 0 ≠ 0 := by
  intro _ _ _ θ v n' i hθ h0 hv hi
  obtain ⟨s₀, s₁, h₀, h₁, e₀, e₁, e₂⟩ := exists_pair a hθ h0 hv
  have hF := IsTheta.mul a (IsTheta.pow a h₀ (n' - i)) (IsTheta.pow a h₁ i)
  have hn : 3 * (n' - i) + 3 * i = 3 * n' := by omega
  rw [hn] at hF
  refine ⟨_, hF, ?_⟩
  have hline : Differentiable ℂ (fun τ : ℂ => τ • v) := differentiable_id.smul_const v
  have hφ : Differentiable ℂ (fun τ : ℂ => s₀ (τ • v)) := h₀.1.comp hline
  have hψ : Differentiable ℂ (fun τ : ℂ => s₁ (τ • v)) := h₁.1.comp hline
  have hd : deriv (fun τ : ℂ => s₁ (τ • v)) 0 = fderiv ℂ s₁ 0 v := by
    have h1 : HasDerivAt (fun τ : ℂ => τ • v) v 0 := by
      simpa using (hasDerivAt_id (0 : ℂ)).smul_const v
    have h2 : HasFDerivAt s₁ (fderiv ℂ s₁ 0) ((0 : ℂ) • v) := by
      simpa using (h₁.1 0).hasFDerivAt
    exact (h2.comp_hasDerivAt (0 : ℂ) h1).deriv
  have ho := order_of_product hφ hψ (by simpa using e₀) (by simpa using e₁) (by rwa [hd]) (n' - i) i
  have han : AnalyticAt ℂ ((fun τ : ℂ => s₀ (τ • v)) ^ (n' - i) * (fun τ : ℂ => s₁ (τ • v)) ^ i) 0 :=
    ((hφ.analyticAt 0).pow _).mul ((hψ.analyticAt 0).pow _)
  exact (analyticOrderAt_eq_iff han i).1 ho

end GlobalTheory.CompanionTheory.Ar.Sl.Jump
