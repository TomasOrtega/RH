import Development.AutomorphicArithmetic.Foundations.LocalLanglands.RecTTransport
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.WDBasic
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.ClBasic
import Development.DiscreteGroups.GlobalIrreducibility.DzIsoKO
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ApplyMemTwKerOfNormalizer

noncomputable section

namespace UpperTheory.Zero.LLC.ParameterDuality

open Polynomial GlobalTheory.PRep GlobalTheory.LocGL

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨w0, v1, hv1⟩ : ∃ w v, B w v ≠ 0 := by`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Conclude with `hB (LinearMap.ext fun w => LinearMap.ext fun v => hc w v)`. Establish `hfix : ∀ (w : W) (x : H) (v : V), B w (π x v) = B w v` using `fun w x v => by`.

Take `⟨k, hk, hk1⟩` from `h2 x x.2`. Use `hinv k w v` as an intermediate fact. Rewrite `this` using `[hk1, map_one, hk]`. Simplify using `using this`. Establish `hker : ∀ w, ∀ u ∈ twKer π H 1, B w u = 0` using `fun w u hu => by`.

Proceed by induction on `hu using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨n, v, rfl⟩` from `hx`. Simplify using `[hfix]`. Consider the case `zero => simp`.

Consider the case `add _ _ _ _ h h' => simp [h, h']`. Consider the case `smul c _ _ h => simp [h]`. Take `⟨v0, hv0, b, hb, rfl⟩ : ∃ v0 ∈ fixed π H, ∃ b ∈ twKer π H 1, v0 + b = v1` from `Submodule.mem_sup.1 ((isCompl_fixed_twKer hπ hH).sup_eq_top ▸ Submodule.mem_top)`. Establish `hw0 : B w0 v0 ≠ 0` using `by simpa [hker w0 b hb] using hv1`. Use `choose s hs using hq`.

Establish `hv0' : ∀ k, q k = 1 → π (ι k) v0 = v0` using `fun k hk => by`. Conclude with `GlobalTheory.Parabolic.mem_fixed.1 hv0 _ (h1 k hk)`. Set `ψ : Module.Dual ℂ W →ₗ[ℂ] V` to `∑ γ : Γ, LinearMap.smulRight (Module.Dual.eval ℂ W (ρ γ w0)) (π (ι (s γ)) v0)`. Establish `hψ : ∀ l, ψ l = ∑ γ : Γ, l (ρ γ w0) • π (ι (s γ)) v0` using `fun l => by`. Simplify using `[ψ, LinearMap.sum_apply]`.

Use `⟨ψ, fun h0 => ?_, fun k l => ?_⟩` and prove the remaining obligations. Set `f : Module.Dual ℂ W` to `B.flip v0`. Set `P : Module.End ℂ W` to `f.smulRight w0`. Set `T : Module.End ℂ W` to `∑ γ : Γ, ρ γ * P * ρ γ⁻¹`. Establish `hT : T = 0`.

Use `LinearMap.ext fun w => (Module.forall_dual_apply_eq_zero_iff ℂ _).1 fun l => ?_` and prove the remaining obligations. Establish `e : B w (ψ l) = 0` using `by rw [h0]; simp`. Rewrite `e` using `[hψ, map_sum]`. Rewrite using `[← e]`. Simplify using `only [T, LinearMap.sum_apply, map_sum, LinearMap.zero_apply]`.

Use `Finset.sum_congr rfl fun γ _ => ?_` and prove the remaining obligations. Establish `e2` using `hinv (s γ) (ρ γ⁻¹ w) v0`. Rewrite `e2` using `[hs γ, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]`. Simplify using `only [map_smul, e2, smul_eq_mul, Module.End.mul_apply, P, f, LinearMap.smulRight_apply, LinearMap.flip_apply]`. Expand and normalize the polynomial expressions, which then agree.

Establish `ht : LinearMap.trace ℂ W T = (Fintype.card Γ : ℂ) * f w0`. Establish `hP : LinearMap.trace ℂ W P = f w0`. Establish `: P = dualTensorHom ℂ W W (f ⊗ₜ w0)`. Use extensionality with `x`. Simplify using `[P, dualTensorHom_apply]`.

Rewrite using `[this, LinearMap.trace_eq_contract_apply]`. Simplify using the standard rewrite rules. Simplify using `only [T, map_sum]`. Establish `: ∀ γ : Γ, LinearMap.trace ℂ W (ρ γ * P * ρ γ⁻¹) = f w0` using `fun γ => by`. Rewrite using `[LinearMap.trace_mul_cycle, ← map_mul, inv_mul_cancel, map_one, one_mul, hP]`.

Simplify using `[this]`. Rewrite `ht` using `[hT, map_zero]`. Establish `hc : (Fintype.card Γ : ℂ) ≠ 0` using `Nat.cast_ne_zero.2 Fintype.card_ne_zero`. Conclude with `hw0 (by simpa [f, hc] using ht.symm)`. Rewrite using `[hψ, hψ, map_sum]`.

Use `(Fintype.sum_equiv (Equiv.mulLeft (q k)⁻¹) _ _ fun γ => ?_)` and prove the remaining obligations. Establish `e : π (ι (s γ)) v0 = π (ι k) (π (ι (s ((q k)⁻¹ * γ))) v0)`. Establish `hu : q ((k * s ((q k)⁻¹ * γ))⁻¹ * s γ) = 1`. Simplify using `[hs]`. Establish `e2 : ι (s γ) = ι (k * s ((q k)⁻¹ * γ)) * ι ((k * s ((q k)⁻¹ * γ))⁻¹ * s γ)`.

Rewrite using `[← map_mul]`. Use `congr 1`. Use `group`. Rewrite using `[e2, map_mul π, Module.End.mul_apply, hv0' _ hu, map_mul ι, map_mul π, Module.End.mul_apply]`. Simplify using `only [Equiv.coe_mulLeft]`.

Rewrite using `[map_smul, ← e, Representation.dual_apply, map_mul, Module.End.mul_apply]`. Both sides reduce to the same expression.
-/
private theorem exists_dual_map {G K Γ V W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group K] [Group Γ]
    [Fintype Γ] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (π : Representation ℂ G V) (hπ : IsSmooth π) (ρ : Representation ℂ Γ W)
    (ι : K →* G) (q : K →* Γ) (hq : Function.Surjective q) (H : Subgroup G) (hH : IsCompact (H : Set G))
    (h1 : ∀ k, q k = 1 → ι k ∈ H) (h2 : ∀ x ∈ H, ∃ k, ι k = x ∧ q k = 1)
    (B : W →ₗ[ℂ] Module.Dual ℂ V) (hB : B ≠ 0)
    (hinv : ∀ k w v, B (ρ (q k) w) (π (ι k) v) = B w v) :
    ∃ ψ : Module.Dual ℂ W →ₗ[ℂ] V, ψ ≠ 0 ∧ ∀ k l, ψ (ρ.dual (q k) l) = π (ι k) (ψ l) := by
  classical
  obtain ⟨w0, v1, hv1⟩ : ∃ w v, B w v ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hB (LinearMap.ext fun w => LinearMap.ext fun v => hc w v)
  have hfix : ∀ (w : W) (x : H) (v : V), B w (π x v) = B w v := fun w x v => by
    obtain ⟨k, hk, hk1⟩ := h2 x x.2
    have := hinv k w v
    rw [hk1, map_one, hk] at this
    simpa using this
  have hker : ∀ w, ∀ u ∈ twKer π H 1, B w u = 0 := fun w u hu => by
    induction hu using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨n, v, rfl⟩ := hx
      simp [hfix]
    | zero => simp
    | add _ _ _ _ h h' => simp [h, h']
    | smul c _ _ h => simp [h]
  obtain ⟨v0, hv0, b, hb, rfl⟩ : ∃ v0 ∈ fixed π H, ∃ b ∈ twKer π H 1, v0 + b = v1 :=
    Submodule.mem_sup.1 ((isCompl_fixed_twKer hπ hH).sup_eq_top ▸ Submodule.mem_top)
  have hw0 : B w0 v0 ≠ 0 := by simpa [hker w0 b hb] using hv1
  choose s hs using hq
  have hv0' : ∀ k, q k = 1 → π (ι k) v0 = v0 := fun k hk => by
    exact GlobalTheory.Parabolic.mem_fixed.1 hv0 _ (h1 k hk)
  let ψ : Module.Dual ℂ W →ₗ[ℂ] V :=
    ∑ γ : Γ, LinearMap.smulRight (Module.Dual.eval ℂ W (ρ γ w0)) (π (ι (s γ)) v0)
  have hψ : ∀ l, ψ l = ∑ γ : Γ, l (ρ γ w0) • π (ι (s γ)) v0 := fun l => by
    simp [ψ, LinearMap.sum_apply]
  refine ⟨ψ, fun h0 => ?_, fun k l => ?_⟩
  · let f : Module.Dual ℂ W := B.flip v0
    let P : Module.End ℂ W := f.smulRight w0
    let T : Module.End ℂ W := ∑ γ : Γ, ρ γ * P * ρ γ⁻¹
    have hT : T = 0 := by
      refine LinearMap.ext fun w => (Module.forall_dual_apply_eq_zero_iff ℂ _).1 fun l => ?_
      have e : B w (ψ l) = 0 := by rw [h0]; simp
      rw [hψ, map_sum] at e
      rw [← e]
      simp only [T, LinearMap.sum_apply, map_sum, LinearMap.zero_apply]
      refine Finset.sum_congr rfl fun γ _ => ?_
      have e2 := hinv (s γ) (ρ γ⁻¹ w) v0
      rw [hs γ, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] at e2
      simp only [map_smul, e2, smul_eq_mul, Module.End.mul_apply, P, f, LinearMap.smulRight_apply,
        LinearMap.flip_apply]
      ring
    have ht : LinearMap.trace ℂ W T = (Fintype.card Γ : ℂ) * f w0 := by
      have hP : LinearMap.trace ℂ W P = f w0 := by
        have : P = dualTensorHom ℂ W W (f ⊗ₜ w0) := by
          ext x
          simp [P, dualTensorHom_apply]
        rw [this, LinearMap.trace_eq_contract_apply]
        simp
      simp only [T, map_sum]
      have : ∀ γ : Γ, LinearMap.trace ℂ W (ρ γ * P * ρ γ⁻¹) = f w0 := fun γ => by
        rw [LinearMap.trace_mul_cycle, ← map_mul, inv_mul_cancel, map_one, one_mul, hP]
      simp [this]
    rw [hT, map_zero] at ht
    have hc : (Fintype.card Γ : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
    exact hw0 (by simpa [f, hc] using ht.symm)
  · rw [hψ, hψ, map_sum]
    refine (Fintype.sum_equiv (Equiv.mulLeft (q k)⁻¹) _ _ fun γ => ?_)
    have e : π (ι (s γ)) v0 = π (ι k) (π (ι (s ((q k)⁻¹ * γ))) v0) := by
      have hu : q ((k * s ((q k)⁻¹ * γ))⁻¹ * s γ) = 1 := by
        simp [hs]
      have e2 : ι (s γ) = ι (k * s ((q k)⁻¹ * γ)) * ι ((k * s ((q k)⁻¹ * γ))⁻¹ * s γ) := by
        rw [← map_mul]
        congr 1
        group
      rw [e2, map_mul π, Module.End.mul_apply, hv0' _ hu, map_mul ι, map_mul π, Module.End.mul_apply]
    simp only [Equiv.coe_mulLeft]
    rw [map_smul, ← e, Representation.dual_apply, map_mul, Module.End.mul_apply]
    rfl

section Finite

open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders

variable {g : ℕ} [Fact g.Prime]

/- English proof (translation)
Establish `deg : ∀ {q : F[X]}, q.coeff 0 ≠ 0 → q.reverse.natDegree = q.natDegree` using `fun {q} h => by`. Rewrite using `[reverse_natDegree, natTrailingDegree_eq_zero.2 (Or.inr h), Nat.sub_zero]`. Establish `rr : ∀ {q : F[X]}, q.coeff 0 ≠ 0 → q.reverse.reverse = q` using `fun {q} h => by`. Rewrite using `[reverse, deg h, reverse, reflect_reflect]`. Establish `un : ∀ {q : F[X]}, q.coeff 0 ≠ 0 → IsUnit q.reverse → IsUnit q` using `fun {q} h hu => by`.

Establish `h1 : q.natDegree = 0` using `by rw [← deg h]; exact natDegree_eq_zero_of_isUnit hu`. Rewrite using `[eq_C_of_natDegree_eq_zero h1]`. Conclude with `isUnit_C.2 (IsUnit.mk0 _ h)`. Establish `r0 : p.reverse.coeff 0 ≠ 0`. Rewrite using `[coeff_zero_reverse]`.

Conclude with `leadingCoeff_ne_zero.2 hp.ne_zero`. Use `⟨fun hu => hp.not_isUnit (un h0 hu), fun a b hab => ?_⟩` and prove the remaining obligations. Establish `ha : a.coeff 0 ≠ 0` using `fun e => r0 (by rw [hab, mul_coeff_zero, e, zero_mul])`. Establish `hb : b.coeff 0 ≠ 0` using `fun e => r0 (by rw [hab, mul_coeff_zero, e, mul_zero])`. Establish `e : p = a.reverse * b.reverse` using `by rw [← reverse_mul_of_domain, ← hab, rr h0]`.

Conclude with `(hp.isUnit_or_isUnit e).imp (un ha) (un hb)`.
-/
private theorem irreducible_reverse {F : Type} [Field F] {p : F[X]} (hp : Irreducible p) (h0 : p.coeff 0 ≠ 0) :
    Irreducible p.reverse := by
  have deg : ∀ {q : F[X]}, q.coeff 0 ≠ 0 → q.reverse.natDegree = q.natDegree := fun {q} h => by
    rw [reverse_natDegree, natTrailingDegree_eq_zero.2 (Or.inr h), Nat.sub_zero]
  have rr : ∀ {q : F[X]}, q.coeff 0 ≠ 0 → q.reverse.reverse = q := fun {q} h => by
    rw [reverse, deg h, reverse, reflect_reflect]
  have un : ∀ {q : F[X]}, q.coeff 0 ≠ 0 → IsUnit q.reverse → IsUnit q := fun {q} h hu => by
    have h1 : q.natDegree = 0 := by rw [← deg h]; exact natDegree_eq_zero_of_isUnit hu
    rw [eq_C_of_natDegree_eq_zero h1]
    exact isUnit_C.2 (IsUnit.mk0 _ h)
  have r0 : p.reverse.coeff 0 ≠ 0 := by
    rw [coeff_zero_reverse]
    exact leadingCoeff_ne_zero.2 hp.ne_zero
  refine ⟨fun hu => hp.not_isUnit (un h0 hu), fun a b hab => ?_⟩
  have ha : a.coeff 0 ≠ 0 := fun e => r0 (by rw [hab, mul_coeff_zero, e, zero_mul])
  have hb : b.coeff 0 ≠ 0 := fun e => r0 (by rw [hab, mul_coeff_zero, e, mul_zero])
  have e : p = a.reverse * b.reverse := by rw [← reverse_mul_of_domain, ← hab, rr h0]
  exact (hp.isUnit_or_isUnit e).imp (un ha) (un hb)

/- English proof (translation)
Establish `hY : ((y⁻¹ : Gn g n) : Mt g n) * (y : Mt g n) = 1` using `by simp`. Establish `key : Matrix.charmatrix ((y⁻¹ : Gn g n) : Mt g n) * (C : ZMod g →+* (ZMod g)[X]).mapMatrix (y : Mt g n) = -(1 - (X : (ZMod g)[X]) • (y : Mt g n).map C)`. Rewrite using `[Matrix.charmatrix, sub_mul, ← map_mul, hY, map_one, neg_sub]`. Use `congr 1`. Use extensionality with `i j`.

Simplify using `[Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.mul_apply, Matrix.smul_apply]`. Use `congrArg Matrix.det key` as an intermediate fact. Rewrite `this` using `[Matrix.det_mul, ← RingHom.map_det, Matrix.det_neg]`. Rewrite using `[Matrix.reverse_charpoly, Matrix.charpolyRev, Matrix.charpoly, this]`. Simplify using the standard rewrite rules.
-/
private theorem charpoly_inv_mul {n : ℕ} (y : Gn g n) :
    ((y⁻¹ : Gn g n) : Mt g n).charpoly * C (y : Mt g n).det = C ((-1) ^ n) * (y : Mt g n).charpoly.reverse := by
  have hY : ((y⁻¹ : Gn g n) : Mt g n) * (y : Mt g n) = 1 := by simp
  have key : Matrix.charmatrix ((y⁻¹ : Gn g n) : Mt g n) * (C : ZMod g →+* (ZMod g)[X]).mapMatrix (y : Mt g n) =
      -(1 - (X : (ZMod g)[X]) • (y : Mt g n).map C) := by
    rw [Matrix.charmatrix, sub_mul, ← map_mul, hY, map_one, neg_sub]
    congr 1
    ext i j
    simp [Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.mul_apply, Matrix.smul_apply]
  have := congrArg Matrix.det key
  rw [Matrix.det_mul, ← RingHom.map_det, Matrix.det_neg] at this
  rw [Matrix.reverse_charpoly, Matrix.charpolyRev, Matrix.charpoly, this]
  simp

/- English proof (translation)
Establish `hd : IsUnit (y : Mt g n).det` using `(Matrix.isUnit_iff_isUnit_det _).1 y.isUnit`. Establish `h0 : (y : Mt g n).charpoly.coeff 0 ≠ 0` using `fun e => by`. Use `Matrix.det_eq_sign_charpoly_coeff (y : Mt g n)` as an intermediate fact. Rewrite `this` using `[e, mul_zero]`. Conclude with `hd.ne_zero this`.

Establish `h1` using `irreducible_reverse h h0`. Establish `h2 : IsUnit (C ((-1 : ZMod g) ^ n))` using `isUnit_C.2 ((isUnit_one.neg).pow n)`. Rewrite `h1` using `[← irreducible_isUnit_mul h2, ← charpoly_inv_mul]`. Conclude with `(irreducible_mul_isUnit (isUnit_C.2 hd)).1 h1`.
-/
private theorem irreducible_charpoly_inv {n : ℕ} {y : Gn g n} (h : Irreducible (y : Mt g n).charpoly) :
    Irreducible ((y⁻¹ : Gn g n) : Mt g n).charpoly := by
  have hd : IsUnit (y : Mt g n).det := (Matrix.isUnit_iff_isUnit_det _).1 y.isUnit
  have h0 : (y : Mt g n).charpoly.coeff 0 ≠ 0 := fun e => by
    have := Matrix.det_eq_sign_charpoly_coeff (y : Mt g n)
    rw [e, mul_zero] at this
    exact hd.ne_zero this
  have h1 := irreducible_reverse h h0
  have h2 : IsUnit (C ((-1 : ZMod g) ^ n)) := isUnit_C.2 ((isUnit_one.neg).pow n)
  rw [← irreducible_isUnit_mul h2, ← charpoly_inv_mul] at h1
  exact (irreducible_mul_isUnit (isUnit_C.2 hd)).1 h1

/- English proof (translation)
Establish `hd : IsUnit (y : Mt g n).det` using `(Matrix.isUnit_iff_isUnit_det _).1 y.isUnit`. Establish `e` using `congrArg (aeval (((z⁻¹ : Kˣ)) : K)) (charpoly_inv_mul y)`. Use `letI : Invertible (z : K) := invertibleOfNonzero z.ne_zero`. Establish `r : aeval (((z⁻¹ : Kˣ)) : K) (y : Mt g n).charpoly.reverse = 0`. Rewrite using `[aeval_def, Units.val_inv_eq_inv_val, ← invOf_eq_inv, eval₂_reverse_eq_zero_iff, ← aeval_def, h]`.

Rewrite `e` using `[map_mul, map_mul, r, mul_zero, aeval_C, mul_eq_zero]`. Use `e.resolve_right ?_` and prove the remaining obligations. Conclude with `(_root_.map_ne_zero _).2 hd.ne_zero`.
-/
private theorem aeval_charpoly_inv {n : ℕ} {K : Type} [Field K] [Algebra (ZMod g) K] {y : Gn g n} {z : Kˣ}
    (h : aeval (z : K) (y : Mt g n).charpoly = 0) :
    aeval (((z⁻¹ : Kˣ)) : K) ((y⁻¹ : Gn g n) : Mt g n).charpoly = 0 := by
  have hd : IsUnit (y : Mt g n).det := (Matrix.isUnit_iff_isUnit_det _).1 y.isUnit
  have e := congrArg (aeval (((z⁻¹ : Kˣ)) : K)) (charpoly_inv_mul y)
  letI : Invertible (z : K) := invertibleOfNonzero z.ne_zero
  have r : aeval (((z⁻¹ : Kˣ)) : K) (y : Mt g n).charpoly.reverse = 0 := by
    rw [aeval_def, Units.val_inv_eq_inv_val, ← invOf_eq_inv, eval₂_reverse_eq_zero_iff, ← aeval_def, h]
  rw [map_mul, map_mul, r, mul_zero, aeval_C, mul_eq_zero] at e
  refine e.resolve_right ?_
  exact (_root_.map_ne_zero _).2 hd.ne_zero

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2, h3⟩ i j hne`. Assume the negation of the conclusion as `hc`. Apply `hne` to reduce the goal to its premises. Distinguish the cases in `hi : (i : ℕ) < a`.

Establish `hj : (j : ℕ) < a`. Assume the negation of the conclusion as `hj`. Conclude with `hc ⟨hi, not_lt.1 hj⟩`. Use `congrFun (congrFun h2 ⟨i, hi⟩) ⟨j, hj⟩` as an intermediate fact. Simplify `this` using `[tl, entN, Matrix.one_apply, Fin.ext_iff]`.

Distinguish the cases in `hj : (j : ℕ) < a`. Rewrite using `[h1 i j hj (not_lt.1 hi), Matrix.one_apply_ne]`. Introduce `e`. Rewrite `hi` using `[e]`. Conclude with `hi hj`.

Establish `hi' : (i : ℕ) - a < b` using `by omega`. Establish `hj' : (j : ℕ) - a < b` using `by omega`. Use `congrFun (congrFun h3 ⟨i - a, hi'⟩) ⟨j - a, hj'⟩` as an intermediate fact. Establish `e1 : a + ((i : ℕ) - a) = i` using `by omega`. Establish `e2 : a + ((j : ℕ) - a) = j` using `by omega`.

Simplify using `only [br, entN, e1, e2, i.2, j.2, and_self, dif_pos, Units.val_one] at this`. Rewrite using `[this, Matrix.one_apply, Matrix.one_apply]`. Simplify using `only [Fin.ext_iff]`. Use `congr 1`. Apply `propext` to reduce the goal to its premises.

Use linear arithmetic over natural numbers and integers. Introduce `h`. Use `⟨fun i j hj hi => ?_, ?_, ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hc`. Establish `hne : M i j ≠ (1 : Mt g n) i j`.

Rewrite using `[Matrix.one_apply_ne]`. Conclude with `hc`. Introduce `e`. Rewrite `hi` using `[e]`. Use linear arithmetic over natural numbers and integers.

Use `h i j hne` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Use extensionality with `i j`. Establish `hi : (i : ℕ) < n` using `by omega`. Establish `hj : (j : ℕ) < n` using `by omega`.

Establish `hh : M ⟨i, hi⟩ ⟨j, hj⟩ = (1 : Mt g n) ⟨i, hi⟩ ⟨j, hj⟩`. Assume the negation of the conclusion as `hc`. Use `h _ _ hc` as an intermediate fact. Simplify using `only at this`. Use linear arithmetic over natural numbers and integers.

Simplify using `only [tl, entN, hi, hj, and_self, dif_pos, Units.val_one, hh, Matrix.one_apply, Fin.ext_iff]`. Use extensionality with `i j`. Establish `hi : a + (i : ℕ) < n` using `by omega`. Establish `hj : a + (j : ℕ) < n` using `by omega`. Establish `hh : M ⟨a + i, hi⟩ ⟨a + j, hj⟩ = (1 : Mt g n) ⟨a + i, hi⟩ ⟨a + j, hj⟩`.

Assume the negation of the conclusion as `hc`. Use `h _ _ hc` as an intermediate fact. Simplify using `only at this`. Use linear arithmetic over natural numbers and integers. Simplify using `only [br, entN, hi, hj, and_self, dif_pos, Units.val_one, hh, Matrix.one_apply, Fin.ext_iff]`.

Simplify using the standard rewrite rules.
-/
private theorem rad_iff {a b n : ℕ} (hn : a + b = n) (M : Mt g n) :
    (InPar a M ∧ tl a M = ((1 : Gn g a) : Mt g a) ∧ br a b M = ((1 : Gn g b) : Mt g b)) ↔
      ∀ i j : Fin n, M i j ≠ (1 : Mt g n) i j → (i : ℕ) < a ∧ a ≤ (j : ℕ) := by
  constructor
  · rintro ⟨h1, h2, h3⟩ i j hne
    by_contra hc
    apply hne
    by_cases hi : (i : ℕ) < a
    · have hj : (j : ℕ) < a := by
        by_contra hj
        exact hc ⟨hi, not_lt.1 hj⟩
      have := congrFun (congrFun h2 ⟨i, hi⟩) ⟨j, hj⟩
      simpa [tl, entN, Matrix.one_apply, Fin.ext_iff] using this
    · by_cases hj : (j : ℕ) < a
      · rw [h1 i j hj (not_lt.1 hi), Matrix.one_apply_ne]
        intro e
        rw [e] at hi
        exact hi hj
      · have hi' : (i : ℕ) - a < b := by omega
        have hj' : (j : ℕ) - a < b := by omega
        have := congrFun (congrFun h3 ⟨i - a, hi'⟩) ⟨j - a, hj'⟩
        have e1 : a + ((i : ℕ) - a) = i := by omega
        have e2 : a + ((j : ℕ) - a) = j := by omega
        simp only [br, entN, e1, e2, i.2, j.2, and_self, dif_pos, Units.val_one] at this
        rw [this, Matrix.one_apply, Matrix.one_apply]
        simp only [Fin.ext_iff]
        congr 1
        apply propext
        omega
  · intro h
    refine ⟨fun i j hj hi => ?_, ?_, ?_⟩
    · by_contra hc
      have hne : M i j ≠ (1 : Mt g n) i j := by
        rw [Matrix.one_apply_ne]
        · exact hc
        · intro e
          rw [e] at hi
          omega
      have := h i j hne
      omega
    · ext i j
      have hi : (i : ℕ) < n := by omega
      have hj : (j : ℕ) < n := by omega
      have hh : M ⟨i, hi⟩ ⟨j, hj⟩ = (1 : Mt g n) ⟨i, hi⟩ ⟨j, hj⟩ := by
        by_contra hc
        have := h _ _ hc
        simp only at this
        omega
      simp only [tl, entN, hi, hj, and_self, dif_pos, Units.val_one, hh, Matrix.one_apply, Fin.ext_iff]
    · ext i j
      have hi : a + (i : ℕ) < n := by omega
      have hj : a + (j : ℕ) < n := by omega
      have hh : M ⟨a + i, hi⟩ ⟨a + j, hj⟩ = (1 : Mt g n) ⟨a + i, hi⟩ ⟨a + j, hj⟩ := by
        by_contra hc
        have := h _ _ hc
        simp only at this
        omega
      simp only [br, entN, hi, hj, and_self, dif_pos, Units.val_one, hh, Matrix.one_apply, Fin.ext_iff]
      simp

/- English proof (translation)
Establish `h` using `(rad_iff hn _).1 hx`. Use `set Y : Mt g n := (x : Mt g n) - 1 with hY`. Establish `hYi : ∀ i j, Y i j ≠ 0 → (i : ℕ) < a ∧ a ≤ (j : ℕ)` using `fun i j hne => h i j fun e => hne (by simp [hY, e])`. Establish `hsq : Y * Y = 0`. Use extensionality with `i j`.

Rewrite using `[Matrix.mul_apply, Matrix.zero_apply]`. Use `Finset.sum_eq_zero fun k _ => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hc`. Establish `h1` using `hYi i k (left_ne_zero_of_mul hc)`. Establish `h2` using `hYi k j (right_ne_zero_of_mul hc)`.

Use linear arithmetic over natural numbers and integers. Establish `hinv : ((x⁻¹ : Gn g n) : Mt g n) = 1 - Y`. Use `Units.inv_eq_of_mul_eq_one_right ?_` and prove the remaining obligations. Establish `: (x : Mt g n) = 1 + Y` using `by simp [hY]`. Rewrite using `[this]`.

Use `noncomm_ring`. Rewrite using `[hsq]`. Simplify using the standard rewrite rules. Rewrite using `[rad_iff hn, hinv]`. Introduce `i j hne`.

Use `hYi i j fun e => hne ?_` and prove the remaining obligations. Simplify using `[e]`.
-/
private theorem rad_inv {a b n : ℕ} (hn : a + b = n) {x : Gn g n}
    (hx : InPar a (x : Mt g n) ∧ tl a (x : Mt g n) = ((1 : Gn g a) : Mt g a) ∧
      br a b (x : Mt g n) = ((1 : Gn g b) : Mt g b)) :
    InPar a ((x⁻¹ : Gn g n) : Mt g n) ∧ tl a ((x⁻¹ : Gn g n) : Mt g n) = ((1 : Gn g a) : Mt g a) ∧
      br a b ((x⁻¹ : Gn g n) : Mt g n) = ((1 : Gn g b) : Mt g b) := by
  have h := (rad_iff hn _).1 hx
  set Y : Mt g n := (x : Mt g n) - 1 with hY
  have hYi : ∀ i j, Y i j ≠ 0 → (i : ℕ) < a ∧ a ≤ (j : ℕ) := fun i j hne =>
    h i j fun e => hne (by simp [hY, e])
  have hsq : Y * Y = 0 := by
    ext i j
    rw [Matrix.mul_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_contra hc
    have h1 := hYi i k (left_ne_zero_of_mul hc)
    have h2 := hYi k j (right_ne_zero_of_mul hc)
    omega
  have hinv : ((x⁻¹ : Gn g n) : Mt g n) = 1 - Y := by
    refine Units.inv_eq_of_mul_eq_one_right ?_
    have : (x : Mt g n) = 1 + Y := by simp [hY]
    rw [this]
    noncomm_ring
    rw [hsq]
    simp
  rw [rad_iff hn, hinv]
  intro i j hne
  refine hYi i j fun e => hne ?_
  simp [e]

/- English proof (translation)
Use `⟨h.1, ?_, fun a ha ha' => ?_⟩` and prove the remaining obligations. Take `⟨V, hV, hc⟩` from `h.2.1`. Use `⟨FDRep.of (Representation.dual V.ρ), ?_, fun x => ?_⟩` and prove the remaining obligations. Rewrite `hV`, the goal using `[FDRep.simple_iff_char_is_norm_one]`. Rewrite using `[← hV]`.

Simplify using `only [FDRep.char_dual, inv_inv]`. Conclude with `Finset.sum_congr rfl fun _ _ => mul_comm _ _`. Rewrite using `[FDRep.char_dual, FDRep.char_dual, hc]`. Establish `h3` using `h.2.2 a ha ha'`. Establish `hn : a + (n - a) = n` using `by omega`.

Rewrite `h3`, the goal using `[res]`. Establish `hP : ∀ x : Gn g n, (InPar a (x : Mt g n) ∧ tl a (x : Mt g n) = ((1 : Gn g a) : Mt g a) ∧ br a (n - a) (x : Mt g n) = ((1 : Gn g (n - a)) : Mt g (n - a))) ↔ (InPar a ((x⁻¹ : Gn g n) : Mt g n) ∧ tl a ((x⁻¹ : Gn g n) : Mt g n) = ((1 : Gn g a) : Mt g a) ∧ br a (n - a) ((x⁻¹ : Gn g n) …` using `fun x => ⟨rad_inv hn, fun e => by simpa using rad_inv hn e⟩`. Rewrite using `[← Equiv.sum_comp (Equiv.inv (Gn g n))]`. Use `Eq.trans (congrArg _ (Finset.sum_congr rfl fun x _ => ?_)) h3` and prove the remaining obligations. Simplify using `only [FDRep.char_dual, Equiv.inv_apply, inv_inv]`.

Use `split_ifs with c1 c2 c2`. Both sides reduce to the same expression. Conclude with `absurd ((hP x).2 c1) c2`. Conclude with `absurd ((hP x).1 c2) c1`. Both sides reduce to the same expression.
-/
private theorem isCusp_dual {n : ℕ} {τ : FDRep ℂ (Gn g n)} (h : IsCusp τ.character) :
    IsCusp (FDRep.of (Representation.dual τ.ρ)).character := by
  refine ⟨h.1, ?_, fun a ha ha' => ?_⟩
  · obtain ⟨V, hV, hc⟩ := h.2.1
    refine ⟨FDRep.of (Representation.dual V.ρ), ?_, fun x => ?_⟩
    · rw [FDRep.simple_iff_char_is_norm_one] at hV ⊢
      rw [← hV]
      simp only [FDRep.char_dual, inv_inv]
      exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
    · rw [FDRep.char_dual, FDRep.char_dual, hc]
  · have h3 := h.2.2 a ha ha'
    have hn : a + (n - a) = n := by omega
    rw [res] at h3 ⊢
    have hP : ∀ x : Gn g n, (InPar a (x : Mt g n) ∧ tl a (x : Mt g n) = ((1 : Gn g a) : Mt g a) ∧
        br a (n - a) (x : Mt g n) = ((1 : Gn g (n - a)) : Mt g (n - a))) ↔
        (InPar a ((x⁻¹ : Gn g n) : Mt g n) ∧ tl a ((x⁻¹ : Gn g n) : Mt g n) = ((1 : Gn g a) : Mt g a) ∧
        br a (n - a) ((x⁻¹ : Gn g n) : Mt g n) = ((1 : Gn g (n - a)) : Mt g (n - a))) := fun x =>
      ⟨rad_inv hn, fun e => by simpa using rad_inv hn e⟩
    rw [← Equiv.sum_comp (Equiv.inv (Gn g n))]
    refine Eq.trans (congrArg _ (Finset.sum_congr rfl fun x _ => ?_)) h3
    simp only [FDRep.char_dual, Equiv.inv_apply, inv_inv]
    split_ifs with c1 c2 c2
    · rfl
    · exact absurd ((hP x).2 c1) c2
    · exact absurd ((hP x).1 c2) c1
    · rfl

/- English proof (translation)
Introduce `y hy z hz`. Rewrite using `[FDRep.char_dual, h y⁻¹ (irreducible_charpoly_inv hy) z⁻¹ (aeval_charpoly_inv hz)]`. Use `congr 1`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Simplify using `[inv_pow]`.
-/
private theorem names_dual {n : ℕ} {K : Type} [Field K] [Algebra (ZMod g) K] {θ : Kˣ →* ℂˣ} {τ : FDRep ℂ (Gn g n)}
    (h : Names g n θ τ) : Names g n θ⁻¹ (FDRep.of (Representation.dual τ.ρ)) := by
  intro y hy z hz
  rw [FDRep.char_dual, h y⁻¹ (irreducible_charpoly_inv hy) z⁻¹ (aeval_charpoly_inv hz)]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [inv_pow]

/- English proof (translation)
Introduce `i j hi hj e` and use `h i j hi hj (inv_injective (by simpa [inv_pow] using e))`.
-/
private theorem isRegularChar_inv {n : ℕ} {K : Type} [Field K] {θ : Kˣ →* ℂˣ} (h : GlobalTheory.Published.IsRegularChar g n θ) :
    GlobalTheory.Published.IsRegularChar g n θ⁻¹ := fun i j hi hj e =>
  h i j hi hj (inv_injective (by simpa [inv_pow] using e))

end Finite

end UpperTheory.Zero.LLC.ParameterDuality

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Zero.LLC.ParameterDuality

/- English proof (translation)
Take `⟨φ, hφ0, hφ⟩` from `hinf`. Set `ι : GL (Fin n) ℤ_[g] →* GL (Fin n) (w.adicCompletion E)` to `(GeneralLinearGroup.map i.toRingHom).comp (GlobalTheory.GLp.inc g n)`. Set `e'` to `e.toIntertwiningMap`. Set `B : τ →ₗ[ℂ] Module.Dual ℂ π.V` to `(smoothPart (Representation.dual π.ρ)).subtype ∘ₗ e'.toLinearMap ∘ₗ φ`. Establish `hB : B ≠ 0` using `fun h0 => hφ0 (LinearMap.ext fun w' => by`.

Establish `h1 : B w' = 0` using `by rw [h0]; rfl`. Establish `h2 : e.toLinearEquiv (φ w') = 0` using `Subtype.ext h1`. Simplify using `using h2)`. Establish `hq : Function.Surjective (GlobalTheory.GLp.red g n)` using `fun x => by`. Take `⟨m, rfl⟩` from `DiscreteGroups.sglob.DzIso.redKO_surjective i hi n x`.

Take `⟨k, rfl⟩` from `DiscreteGroups.sglob.DzIso.toKO_surjective i hi n m`. Conclude with `⟨k, (DiscreteGroups.sglob.DzIso.redKO_toKO i hi n k).symm⟩`. Establish `hker` using `DiscreteGroups.sglob.DzIso.ker_redKO i hi n`. Establish `h1 : ∀ k, GlobalTheory.GLp.red g n k = 1 → ι k ∈ KOne (w.adicCompletion E) (Fin n)` using `fun k hk => by`. Establish `: DiscreteGroups.sglob.DzIso.toKO i hi n k ∈ (DiscreteGroups.sglob.DzIso.redKO i hi n).ker`.

Rewrite using `[MonoidHom.mem_ker, DiscreteGroups.sglob.DzIso.redKO_toKO, hk]`. Rewrite `this` using `[hker, Subgroup.mem_subgroupOf, DiscreteGroups.sglob.DzIso.coe_toKO]`. Conclude with `this`. Establish `h2 : ∀ x ∈ KOne (w.adicCompletion E) (Fin n), ∃ k, ι k = x ∧ GlobalTheory.GLp.red g n k = 1` using `fun x hx => by`. Establish `hxK : x ∈ KO (w.adicCompletion E) (Fin n)`.

Take `⟨b, -, rfl⟩` from `Subgroup.mem_map.1 hx`. Conclude with `⟨b, rfl⟩`. Take `⟨k, hk⟩` from `DiscreteGroups.sglob.DzIso.toKO_surjective i hi n ⟨x, hxK⟩`. Use `⟨k, ?_, ?_⟩` and prove the remaining obligations. Use `show GeneralLinearGroup.map i.toRingHom (GlobalTheory.GLp.inc g n k) = x`.

Rewrite using `[← DiscreteGroups.sglob.DzIso.coe_toKO i hi, hk]`. Rewrite using `[← DiscreteGroups.sglob.DzIso.redKO_toKO i hi, hk, ← MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf]`. Conclude with `hx`. Establish `hinv : ∀ k w' v, B (τ.ρ (GlobalTheory.GLp.red g n k) w') (π.ρ (ι k) v) = B w' v` using `fun k w' v => by`. Establish `e1 : e' (φ (τ.ρ (GlobalTheory.GLp.red g n k) w')) = contra π.ρ (ι k) (e' (φ w'))`.

Rewrite using `[hφ k w']`. Conclude with `Representation.IntertwiningMap.isIntertwining _ _ e' (ι k) (φ w')`. Use `show ((e' (φ (τ.ρ (GlobalTheory.GLp.red g n k) w')) : smoothPart _) : Module.Dual ℂ π.V) (π.ρ (ι k) v) = ((e' (φ w') : smoothPart _) : Module.Dual ℂ π.V) v`. Rewrite using `[e1, contra_apply, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]`. Both sides reduce to the same expression.

Take `⟨ψ, hψ0, hψ⟩` from `exists_dual_map π.ρ π.smooth τ.ρ ι (GlobalTheory.GLp.red g n) hq (KOne (w.adicCompletion E) (Fin n)) GlobalTheory.DepthZeroJac.isCompact_KOne h1 h2 B hB hinv`. Conclude with `⟨ψ, hψ0, hψ⟩`.
-/
private theorem inflates_dual {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {g : ℕ} [Fact g.Prime]
    (i : ℚ_[g] ≃+* w.adicCompletion E) (hi : Continuous i) {n : ℕ} (π σ : IrrRep (GL (Fin n) (w.adicCompletion E)))
    (e : σ.ρ.Equiv (contra π.ρ)) (τ : FDRep ℂ (Gn g n))
    (hinf : GlobalTheory.SerSys.TameGen.Inflates (σ.ρ.comp (GeneralLinearGroup.map i.toRingHom)) τ) :
    GlobalTheory.SerSys.TameGen.Inflates (π.ρ.comp (GeneralLinearGroup.map i.toRingHom))
      (FDRep.of (Representation.dual τ.ρ)) := by
  obtain ⟨φ, hφ0, hφ⟩ := hinf
  let ι : GL (Fin n) ℤ_[g] →* GL (Fin n) (w.adicCompletion E) :=
    (GeneralLinearGroup.map i.toRingHom).comp (GlobalTheory.GLp.inc g n)
  let e' := e.toIntertwiningMap
  let B : τ →ₗ[ℂ] Module.Dual ℂ π.V :=
    (smoothPart (Representation.dual π.ρ)).subtype ∘ₗ e'.toLinearMap ∘ₗ φ
  have hB : B ≠ 0 := fun h0 => hφ0 (LinearMap.ext fun w' => by
    have h1 : B w' = 0 := by rw [h0]; rfl
    have h2 : e.toLinearEquiv (φ w') = 0 := Subtype.ext h1
    simpa using h2)
  have hq : Function.Surjective (GlobalTheory.GLp.red g n) := fun x => by
    obtain ⟨m, rfl⟩ := DiscreteGroups.sglob.DzIso.redKO_surjective i hi n x
    obtain ⟨k, rfl⟩ := DiscreteGroups.sglob.DzIso.toKO_surjective i hi n m
    exact ⟨k, (DiscreteGroups.sglob.DzIso.redKO_toKO i hi n k).symm⟩
  have hker := DiscreteGroups.sglob.DzIso.ker_redKO i hi n
  have h1 : ∀ k, GlobalTheory.GLp.red g n k = 1 → ι k ∈ KOne (w.adicCompletion E) (Fin n) := fun k hk => by
    have : DiscreteGroups.sglob.DzIso.toKO i hi n k ∈ (DiscreteGroups.sglob.DzIso.redKO i hi n).ker := by
      rw [MonoidHom.mem_ker, DiscreteGroups.sglob.DzIso.redKO_toKO, hk]
    rw [hker, Subgroup.mem_subgroupOf, DiscreteGroups.sglob.DzIso.coe_toKO] at this
    exact this
  have h2 : ∀ x ∈ KOne (w.adicCompletion E) (Fin n), ∃ k, ι k = x ∧ GlobalTheory.GLp.red g n k = 1 := fun x hx => by
    have hxK : x ∈ KO (w.adicCompletion E) (Fin n) := by
      obtain ⟨b, -, rfl⟩ := Subgroup.mem_map.1 hx
      exact ⟨b, rfl⟩
    obtain ⟨k, hk⟩ := DiscreteGroups.sglob.DzIso.toKO_surjective i hi n ⟨x, hxK⟩
    refine ⟨k, ?_, ?_⟩
    · show GeneralLinearGroup.map i.toRingHom (GlobalTheory.GLp.inc g n k) = x
      rw [← DiscreteGroups.sglob.DzIso.coe_toKO i hi, hk]
    · rw [← DiscreteGroups.sglob.DzIso.redKO_toKO i hi, hk, ← MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf]
      exact hx
  have hinv : ∀ k w' v, B (τ.ρ (GlobalTheory.GLp.red g n k) w') (π.ρ (ι k) v) = B w' v := fun k w' v => by
    have e1 : e' (φ (τ.ρ (GlobalTheory.GLp.red g n k) w')) = contra π.ρ (ι k) (e' (φ w')) := by
      rw [hφ k w']
      exact Representation.IntertwiningMap.isIntertwining _ _ e' (ι k) (φ w')
    show ((e' (φ (τ.ρ (GlobalTheory.GLp.red g n k) w')) : smoothPart _) : Module.Dual ℂ π.V) (π.ρ (ι k) v) =
      ((e' (φ w') : smoothPart _) : Module.Dual ℂ π.V) v
    rw [e1, contra_apply, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]
    rfl
  obtain ⟨ψ, hψ0, hψ⟩ := exists_dual_map π.ρ π.smooth τ.ρ ι (GlobalTheory.GLp.red g n) hq
    (KOne (w.adicCompletion E) (Fin n)) GlobalTheory.DepthZeroJac.isCompact_KOne h1 h2 B hB hinv
  exact ⟨ψ, hψ0, hψ⟩

end UpperTheory.Zero.LLC.ParameterDuality

/- English proof (translation)
Introduce `E Ω _ _ _ _ _ A w h a ha _ _ i₀ _ y y' _ _ hD V hV`. Take `⟨-, -, -, hIrr, hTame, hDim, hDet, hPol, -⟩` from `UpperTheory.Zero.LLC.wDBasic E Ω A w h V`. Take `⟨hIrrD, -⟩ : IsIrrWD V.lpDual ∧ True` from `⟨(hIrr hV.irr).2.2, trivial⟩`. Take `⟨-, -, -, hIrr', -⟩` from `UpperTheory.Zero.LLC.wDBasic E Ω A w h V.lpDual`. Establish `hC : CharZero (w.adicCompletion E)` using `charZero_of_injective_ringHom (f := i₀.toRingHom) i₀.injective`.

Take `⟨⟨ω₀, -, hω₀, -⟩, -, -, -, -, -, hdual⟩` from `UpperTheory.Zero.LLC.clBasic (w.adicCompletion E) y`. Take `⟨hy1, -, -, -, -, -, hcen⟩` from `hdual y' hD`. Take `⟨⟨ω₁, -, -, huniq⟩, -⟩` from `UpperTheory.Zero.LLC.clBasic (w.adicCompletion E) y'`. Use `⟨hIrrD, ?_, hTame hV.tame, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hDim, hV.dim, hy1]`.

Introduce `ω hω σ`. Establish `e : ω = ω₀⁻¹` using `(huniq ω hω).trans (huniq _ (hcen ω₀ hω₀)).symm`. Rewrite using `[hDet, hV.central ω₀ hω₀ σ, e]`. Simplify using the standard rewrite rules. Introduce `g _ i hi n hn D R hR θ hθ τ hτ hN σ hσ hinf`.

Take `⟨m, π, π', rfl, rfl, ⟨e⟩⟩` from `hD`. Take `rfl : n = m` from `congrArg Sigma.fst hσ`. Take `⟨e₁⟩` from `IrrRep.cl_eq_iff.1 (sigma_mk_injective (β := fun n => IrrCl (GL (Fin n) (w.adicCompletion E))) hσ)`. Establish `hI` using `ParameterDuality.inflates_dual i hi π σ (e₁.trans e) τ hinf`. Take `⟨-, hIn⟩` from `hV.type g i hi n hn D R hR θ⁻¹ (ParameterDuality.isRegularChar_inv hθ) _ (ParameterDuality.isCusp_dual hτ) (ParameterDuality.names_dual hN) π rfl hI`.

Use `⟨(hIrr' hIrrD).1, fun t => ?_⟩` and prove the remaining obligations. Establish `h3` using `(hPol t ((Finset.range n).val.map fun j => (θ⁻¹ (R t ^ g ^ j))) (by`. Rewrite using `[hIn t]`. Express the relevant statement in the definitionally equal form `_ = (Multiset.map (fun z : ℂ => X - C z) (Multiset.bind _ fun a : ℂˣ => {(a : ℂ)})).prod`. Rewrite using `[Multiset.bind_singleton, Multiset.map_map, Multiset.map_map]`.

Use the proof step `rfl)).2.1`. Rewrite using `[h3, Multiset.map_map]`. Simplify using `[Finset.prod]`.
-/
theorem UpperTheory.Zero.LLC.parDual :
    UpperTheory.Zero.LLC.ParDual := by
  intro E Ω _ _ _ _ _ A w h a ha _ _ i₀ _ y y' _ _ hD V hV
  obtain ⟨-, -, -, hIrr, hTame, hDim, hDet, hPol, -⟩ := UpperTheory.Zero.LLC.wDBasic E Ω A w h V
  obtain ⟨hIrrD, -⟩ : IsIrrWD V.lpDual ∧ True := ⟨(hIrr hV.irr).2.2, trivial⟩
  obtain ⟨-, -, -, hIrr', -⟩ := UpperTheory.Zero.LLC.wDBasic E Ω A w h V.lpDual
  have hC : CharZero (w.adicCompletion E) := charZero_of_injective_ringHom (f := i₀.toRingHom) i₀.injective
  obtain ⟨⟨ω₀, -, hω₀, -⟩, -, -, -, -, -, hdual⟩ := UpperTheory.Zero.LLC.clBasic (w.adicCompletion E) y
  obtain ⟨hy1, -, -, -, -, -, hcen⟩ := hdual y' hD
  obtain ⟨⟨ω₁, -, -, huniq⟩, -⟩ := UpperTheory.Zero.LLC.clBasic (w.adicCompletion E) y'
  refine ⟨hIrrD, ?_, hTame hV.tame, ?_, ?_⟩
  · rw [hDim, hV.dim, hy1]
  · intro ω hω σ
    have e : ω = ω₀⁻¹ := (huniq ω hω).trans (huniq _ (hcen ω₀ hω₀)).symm
    rw [hDet, hV.central ω₀ hω₀ σ, e]
    simp
  · intro g _ i hi n hn D R hR θ hθ τ hτ hN σ hσ hinf
    obtain ⟨m, π, π', rfl, rfl, ⟨e⟩⟩ := hD
    obtain rfl : n = m := congrArg Sigma.fst hσ
    obtain ⟨e₁⟩ := IrrRep.cl_eq_iff.1 (sigma_mk_injective (β := fun n => IrrCl (GL (Fin n) (w.adicCompletion E))) hσ)
    have hI := ParameterDuality.inflates_dual i hi π σ (e₁.trans e) τ hinf
    obtain ⟨-, hIn⟩ := hV.type g i hi n hn D R hR θ⁻¹ (ParameterDuality.isRegularChar_inv hθ) _
      (ParameterDuality.isCusp_dual hτ) (ParameterDuality.names_dual hN) π rfl hI
    refine ⟨(hIrr' hIrrD).1, fun t => ?_⟩
    have h3 := (hPol t ((Finset.range n).val.map fun j => (θ⁻¹ (R t ^ g ^ j))) (by
      rw [hIn t]
      change _ = (Multiset.map (fun z : ℂ => X - C z) (Multiset.bind _ fun a : ℂˣ => {(a : ℂ)})).prod
      rw [Multiset.bind_singleton, Multiset.map_map, Multiset.map_map]
      rfl)).2.1
    rw [h3, Multiset.map_map]
    simp [Finset.prod]

end
