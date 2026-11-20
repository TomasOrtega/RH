import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.AbsInvOf

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry CrystallineSemistableComparison TensorProduct

namespace UpperTheory.Ru.crystallineComparison

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}
  {R : Per l K} {G : Model l K → Prop} {D : Dat R}

/- English proof (translation)
Use `show a • ((1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] v : ℚ_[l] ⊗[ℤ_[l]] M.T n) = _`. Rewrite using `[TensorProduct.smul_tmul', smul_eq_mul, mul_one]`.
-/
private theorem smul_toV {M : Model l K} {n : ℕ} (a : ℚ_[l]) (v : M.T n) :
    a • M.toV n v = (a ⊗ₜ[ℤ_[l]] v : ℚ_[l] ⊗[ℤ_[l]] M.T n) := by
  show a • ((1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] v : ℚ_[l] ⊗[ℤ_[l]] M.T n) = _
  rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]

/- English proof (translation)
Use `TensorProduct.induction_on (motive := fun w : ℚ_[l] ⊗[ℤ_[l]] M.T n => P w) (show ℚ_[l] ⊗[ℤ_[l]] M.T n from w) h0 ?_ h2` and prove the remaining obligations. Introduce `a v`. Use `h1 a v` as an intermediate fact. Rewrite `this` using `[smul_toV]`. Conclude with `this`.
-/
private theorem V_induction {M : Model l K} {n : ℕ} {P : M.V n → Prop} (h0 : P 0)
    (h1 : ∀ (a : ℚ_[l]) (v : M.T n), P (a • M.toV n v)) (h2 : ∀ x y, P x → P y → P (x + y)) (w : M.V n) : P w := by
  refine TensorProduct.induction_on (motive := fun w : ℚ_[l] ⊗[ℤ_[l]] M.T n => P w) (show ℚ_[l] ⊗[ℤ_[l]] M.T n from w) h0 ?_ h2
  intro a v
  have := h1 a v
  rw [smul_toV] at this
  exact this

private structure IsVal (e : EMap G D) (b : BMap G D) (p : PMap G D) {M : Model l K} (a : D.Ch M) (n : ℕ)
    (C : M.V n →+ (Module.Dual K (HdR M.q n) → R.B)) : Prop where
  smul : ∀ (z : ℚ_[l]) (w : M.V n) φ, C (z • w) φ = R.q z * C w φ
  spec : ∀ (c : R.A) (v : M.T n) (x : (D.H a).N n), b.β a n x = c • e.e a n v →
    ∀ φ, p.κ a n x φ = R.i c * C (M.toV n v) φ

/- English proof (translation)
Rewrite using `[map_pow]`. Conclude with `pow_ne_zero _ hF.t_ne`.
-/
private theorem tB_pow_ne (hF : R.Facts) (m : ℕ) : R.i (R.t ^ m) ≠ 0 := by
  rw [map_pow]; exact pow_ne_zero _ hF.t_ne

/- English proof (translation)
Take `⟨N, hN⟩` from `b.surj a hM n`. Take `⟨m, hm⟩` from `b.inj a hM n`. Establish `hx : ∀ v, ∃ x, b.β a n x = R.t ^ N • e.e a n v` using `fun v => let ⟨x, _, h⟩ := hN (e.e a n v)`. Use the proof step `⟨x, h⟩`. Use `choose xs hxs using hx`.

Establish `hκ : ∀ x x' : (D.H a).N n, b.β a n x = b.β a n x' → ∀ φ, p.κ a n x φ = p.κ a n x' φ`. Introduce `x x' h φ`. Establish `h1` using `hm (x - x') (by rw [map_sub, h, sub_self])`. Establish `h2` using `congrArg (fun y => p.κ a n y φ) h1`. Simplify using `only [p.lin a hM, map_zero, AddMonoidHom.zero_apply, map_sub, AddMonoidHom.sub_apply] at h2`.

Conclude with `sub_eq_zero.mp ((mul_eq_zero.mp h2).resolve_left (tB_pow_ne hF m))`. Establish `hu` using `tB_pow_ne hF (R := R) N`. Set `c0 : M.T n → Module.Dual K (HdR M.q n) → R.B` to `fun v φ => (R.i (R.t ^ N))⁻¹ * p.κ a n (xs v) φ`. Establish `spec0 : ∀ (c : R.A) (v : M.T n) (x : (D.H a).N n), b.β a n x = c • e.e a n v → ∀ φ, p.κ a n x φ = R.i c * c0 v φ`. Introduce `c v x h φ`.

Establish `h1` using `hκ (R.t ^ N • x) (c • xs v) (by`. Rewrite using `[map_smul, map_smul, h, hxs, smul_smul, smul_smul, mul_comm]) φ`. Rewrite `h1` using `[p.lin a hM, p.lin a hM]`. Simplify using `only [c0]`. Clear the denominators using the available nonvanishing facts.

Take the linear combination `h1`. Establish `add0 : ∀ v v' φ, c0 (v + v') φ = c0 v φ + c0 v' φ`. Introduce `v v' φ`. Use `spec0 (R.t ^ N) (v + v') (xs v + xs v') (by rw [map_add, hxs, hxs, map_add, smul_add]) φ` as an intermediate fact. Rewrite `this` using `[map_add, AddMonoidHom.add_apply]`.

Simplify using `only [c0]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[this]`. Simplify using `only [c0]`. Clear the denominators using the available nonvanishing facts.

Establish `sm0 : ∀ (z : ℤ_[l]) v φ, c0 (z • v) φ = R.q z * c0 v φ`. Introduce `z v φ`. Use `spec0 (R.t ^ N) (z • v) (R.z z • xs v) (by` as an intermediate fact. Rewrite using `[map_smul, hxs, e.lin a hM, smul_smul, smul_smul, mul_comm]) φ`. Rewrite `this` using `[p.lin a hM, hF.thetaSetup_structureMap_comp]`.

Establish `h3 : c0 (z • v) φ = (R.i (R.t ^ N))⁻¹ * (R.q z * p.κ a n (xs v) φ)` using `by rw [this]; field_simp`. Rewrite using `[h3]`. Simplify using `only [c0]`. Expand and normalize the polynomial expressions, which then agree. Set `f : ℚ_[l] →+ M.T n →+ (Module.Dual K (HdR M.q n) → R.B)` to `AddMonoidHom.mk' (fun s => AddMonoidHom.mk' (fun v φ => R.q s * c0 v φ) (by intro v v'; funext φ; simp only [add0, Pi.add_apply, mul_add])) (by`.

Introduce `s s'`. Use extensionality with `v φ`. Simplify using `[add_mul])`. Set `C : M.V n →+ (Module.Dual K (HdR M.q n) → R.B)` to `TensorProduct.liftAddHom f (by`. Introduce `r s v`.

Use function extensionality and compare the values at `φ`. Use `show R.q (r • s) * c0 v φ = R.q s * c0 (r • v) φ`. Rewrite using `[sm0, Algebra.smul_def, map_mul]`. Use `show R.q (r : ℚ_[l]) * _ * _ = _`. Use the proof step `ring)`.

Establish `hC : ∀ (s : ℚ_[l]) (v : M.T n) φ, C (s • M.toV n v) φ = R.q s * c0 v φ`. Introduce `s v φ`. Rewrite using `[smul_toV]`. Use `show (TensorProduct.liftAddHom f _ (s ⊗ₜ v)) φ = _`. Rewrite using `[TensorProduct.liftAddHom_tmul]`.

Both sides reduce to the same expression. Establish `hC1 : ∀ (v : M.T n) φ, C (M.toV n v) φ = c0 v φ`. Introduce `v φ`. Use `hC 1 v φ` as an intermediate fact. Rewrite `this` using `[one_smul, map_one, one_mul]`. Then use the resulting hypothesis.

Use `⟨C, ?_, ?_⟩` and prove the remaining obligations. Introduce `z w φ`. Use `V_induction (P := fun w => C (z • w) φ = R.q z * C w φ) ?_ ?_ ?_ w` and prove the remaining obligations. Simplify using the standard rewrite rules. Introduce `s v`.

Rewrite using `[smul_smul, hC, hC, map_mul]`. Expand and normalize the polynomial expressions, which then agree. Introduce `x y hx hy`. Rewrite using `[smul_add, map_add, map_add, Pi.add_apply, Pi.add_apply, hx, hy, mul_add]`. Introduce `c v x h φ`.

Rewrite using `[hC1]`. Conclude with `spec0 c v x h φ`.
-/
private theorem exists_val (hF : R.Facts) (e : EMap G D) (b : BMap G D) (p : PMap G D) {M : Model l K} (hM : G M)
    (a : D.Ch M) (n : ℕ) : ∃ C, IsVal e b p a n C := by
  obtain ⟨N, hN⟩ := b.surj a hM n
  obtain ⟨m, hm⟩ := b.inj a hM n
  have hx : ∀ v, ∃ x, b.β a n x = R.t ^ N • e.e a n v := fun v => let ⟨x, _, h⟩ := hN (e.e a n v); ⟨x, h⟩
  choose xs hxs using hx
  have hκ : ∀ x x' : (D.H a).N n, b.β a n x = b.β a n x' → ∀ φ, p.κ a n x φ = p.κ a n x' φ := by
    intro x x' h φ
    have h1 := hm (x - x') (by rw [map_sub, h, sub_self])
    have h2 := congrArg (fun y => p.κ a n y φ) h1
    simp only [p.lin a hM, map_zero, AddMonoidHom.zero_apply, map_sub, AddMonoidHom.sub_apply] at h2
    exact sub_eq_zero.mp ((mul_eq_zero.mp h2).resolve_left (tB_pow_ne hF m))
  have hu := tB_pow_ne hF (R := R) N
  let c0 : M.T n → Module.Dual K (HdR M.q n) → R.B := fun v φ => (R.i (R.t ^ N))⁻¹ * p.κ a n (xs v) φ
  have spec0 : ∀ (c : R.A) (v : M.T n) (x : (D.H a).N n), b.β a n x = c • e.e a n v →
      ∀ φ, p.κ a n x φ = R.i c * c0 v φ := by
    intro c v x h φ
    have h1 := hκ (R.t ^ N • x) (c • xs v) (by
      rw [map_smul, map_smul, h, hxs, smul_smul, smul_smul, mul_comm]) φ
    rw [p.lin a hM, p.lin a hM] at h1
    simp only [c0]
    field_simp
    linear_combination h1
  have add0 : ∀ v v' φ, c0 (v + v') φ = c0 v φ + c0 v' φ := by
    intro v v' φ
    have := spec0 (R.t ^ N) (v + v') (xs v + xs v') (by rw [map_add, hxs, hxs, map_add, smul_add]) φ
    rw [map_add, AddMonoidHom.add_apply] at this
    simp only [c0]
    field_simp
    rw [this]; simp only [c0]; field_simp
  have sm0 : ∀ (z : ℤ_[l]) v φ, c0 (z • v) φ = R.q z * c0 v φ := by
    intro z v φ
    have := spec0 (R.t ^ N) (z • v) (R.z z • xs v) (by
      rw [map_smul, hxs, e.lin a hM, smul_smul, smul_smul, mul_comm]) φ
    rw [p.lin a hM, hF.thetaSetup_structureMap_comp] at this
    have h3 : c0 (z • v) φ = (R.i (R.t ^ N))⁻¹ * (R.q z * p.κ a n (xs v) φ) := by rw [this]; field_simp
    rw [h3]; simp only [c0]; ring
  let f : ℚ_[l] →+ M.T n →+ (Module.Dual K (HdR M.q n) → R.B) :=
    AddMonoidHom.mk' (fun s => AddMonoidHom.mk' (fun v φ => R.q s * c0 v φ)
      (by intro v v'; funext φ; simp only [add0, Pi.add_apply, mul_add])) (by
        intro s s'; ext v φ; simp [add_mul])
  let C : M.V n →+ (Module.Dual K (HdR M.q n) → R.B) := TensorProduct.liftAddHom f (by
    intro r s v; funext φ
    show R.q (r • s) * c0 v φ = R.q s * c0 (r • v) φ
    rw [sm0, Algebra.smul_def, map_mul]
    show R.q (r : ℚ_[l]) * _ * _ = _
    ring)
  have hC : ∀ (s : ℚ_[l]) (v : M.T n) φ, C (s • M.toV n v) φ = R.q s * c0 v φ := by
    intro s v φ
    rw [smul_toV]
    show (TensorProduct.liftAddHom f _ (s ⊗ₜ v)) φ = _
    rw [TensorProduct.liftAddHom_tmul]
    rfl
  have hC1 : ∀ (v : M.T n) φ, C (M.toV n v) φ = c0 v φ := by
    intro v φ
    have := hC 1 v φ
    rwa [one_smul, map_one, one_mul] at this
  refine ⟨C, ?_, ?_⟩
  · intro z w φ
    refine V_induction (P := fun w => C (z • w) φ = R.q z * C w φ) ?_ ?_ ?_ w
    · simp
    · intro s v
      rw [smul_smul, hC, hC, map_mul]; ring
    · intro x y hx hy
      rw [smul_add, map_add, map_add, Pi.add_apply, Pi.add_apply, hx, hy, mul_add]
  · intro c v x h φ
    rw [hC1]; exact spec0 c v x h φ

/- English proof (translation)
Take `⟨N, hN⟩` from `b.surj a hM n`. Conclude with `⟨N, fun v => let ⟨x, _, h⟩ := hN (e.e a n v); ⟨x, h⟩⟩`.
-/
private theorem exists_rep (e : EMap G D) (b : BMap G D) {M : Model l K} (hM : G M) (a : D.Ch M) (n : ℕ) :
    ∃ N : ℕ, ∀ v, ∃ x, b.β a n x = R.t ^ N • e.e a n v := by
  obtain ⟨N, hN⟩ := b.surj a hM n
  exact ⟨N, fun v => let ⟨x, _, h⟩ := hN (e.e a n v); ⟨x, h⟩⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem act_toV {M : Model l K} {n : ℕ} (σ : K.fixingSubgroup) (v : M.T n) :
    M.act n σ (M.toV n v) = M.toV n (M.actT n σ v) := rfl

variable {e : EMap G D} {b : BMap G D} {p : PMap G D} {M : Model l K} {a : D.Ch M}

/- English proof (translation)
Use `V_induction (P := fun w => C (M.act n σ w) φ = R.σ σ (C w φ)) (by simp) ?_ ?_ w` and prove the remaining obligations. Introduce `s v`. Rewrite using `[map_smul, hC.smul, hC.smul, map_mul, hF.σ_q, act_toV]`. Use `congr 1`. Take `⟨N, hN⟩` from `exists_rep e b hM a n`.

Take `⟨x, hx⟩` from `hN v`. Establish `h1` using `hC.spec (R.σA σ (R.t ^ N)) (M.actT n σ v) ((D.H a).act n σ x) (by`. Rewrite using `[b.act a hM, hx, hL.act_smul, e.act a hM]) φ`. Rewrite `h1` using `[p.act a hM, hC.spec _ _ _ hx, map_mul, hF.i_σ]`. Conclude with `(mul_left_cancel₀ ((map_ne_zero _).mpr (tB_pow_ne hF N)) h1).symm`.

Introduce `x y hx hy`. Rewrite using `[map_add, map_add, Pi.add_apply, hx, hy, map_add, Pi.add_apply, map_add]`.
-/
private theorem IsVal.equi {n : ℕ} {C : M.V n →+ (Module.Dual K (HdR M.q n) → R.B)} (hC : IsVal e b p a n C)
    (hF : R.Facts) (hL : D.Laws G) (hM : G M) (σ : K.fixingSubgroup) (w : M.V n) (φ) :
    C (M.act n σ w) φ = R.σ σ (C w φ) := by
  refine V_induction (P := fun w => C (M.act n σ w) φ = R.σ σ (C w φ)) (by simp) ?_ ?_ w
  · intro s v
    rw [map_smul, hC.smul, hC.smul, map_mul, hF.σ_q, act_toV]
    congr 1
    obtain ⟨N, hN⟩ := exists_rep e b hM a n
    obtain ⟨x, hx⟩ := hN v
    have h1 := hC.spec (R.σA σ (R.t ^ N)) (M.actT n σ v) ((D.H a).act n σ x) (by
      rw [b.act a hM, hx, hL.act_smul, e.act a hM]) φ
    rw [p.act a hM, hC.spec _ _ _ hx, map_mul, hF.i_σ] at h1
    exact (mul_left_cancel₀ ((map_ne_zero _).mpr (tB_pow_ne hF N)) h1).symm
  · intro x y hx hy
    rw [map_add, map_add, Pi.add_apply, hx, hy, map_add, Pi.add_apply, map_add]

/- English proof (translation)
Take `⟨N, hN⟩` from `exists_rep e b hM a i`. Take `⟨N', hN'⟩` from `exists_rep e b hM a j`. Take `⟨X, hX⟩` from `hN x`. Take `⟨Y, hY⟩` from `hN' y`. Take `⟨Z, hZ⟩` from `hL.cup_ex a X Y`.

Establish `h1` using `b.cup a hM X Y Z hZ`. Rewrite `h1` using `[hX, hY]`. Establish `h2` using `hL.cup_uniq a _ _ _ _ h1 (hL.cup_smul a _ _ _ _ _ (e.cup a hM x y z h))`. Establish `h3` using `p.cup a hM X Y Z hZ bb bb' φ`. Rewrite `h3` using `[hij.spec _ _ _ h2]`.

Simplify using `only [hi.spec _ _ _ hX, hj.spec _ _ _ hY] at h3`. Rewrite `h3` using `[map_mul]`. Use `mul_left_cancel₀ (mul_ne_zero (tB_pow_ne hF N) (tB_pow_ne hF N')) (h3.trans ?_)` and prove the remaining obligations. Simplify using `only [Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring`.
-/
private theorem IsVal.cup {i j : ℕ} {Ci : M.V i →+ (Module.Dual K (HdR M.q i) → R.B)}
    {Cj : M.V j →+ (Module.Dual K (HdR M.q j) → R.B)} {Cij : M.V (i + j) →+ (Module.Dual K (HdR M.q (i + j)) → R.B)}
    (hi : IsVal e b p a i Ci) (hj : IsVal e b p a j Cj) (hij : IsVal e b p a (i + j) Cij)
    (hF : R.Facts) (hL : D.Laws G) (hM : G M) (x : M.T i) (y : M.T j) (z : M.T (i + j)) (h : M.CupT x y z)
    {m m' : ℕ} (bb : Module.Basis (Fin m) K (HdR M.q i)) (bb' : Module.Basis (Fin m') K (HdR M.q j)) (φ) :
    Cij (M.toV _ z) φ = ∑ s, ∑ s', Ci (M.toV _ x) (bb.coord s) * Cj (M.toV _ y) (bb'.coord s') *
      R.o (φ (p.cupR M i j (bb s) (bb' s'))) := by
  obtain ⟨N, hN⟩ := exists_rep e b hM a i
  obtain ⟨N', hN'⟩ := exists_rep e b hM a j
  obtain ⟨X, hX⟩ := hN x
  obtain ⟨Y, hY⟩ := hN' y
  obtain ⟨Z, hZ⟩ := hL.cup_ex a X Y
  have h1 := b.cup a hM X Y Z hZ
  rw [hX, hY] at h1
  have h2 := hL.cup_uniq a _ _ _ _ h1 (hL.cup_smul a _ _ _ _ _ (e.cup a hM x y z h))
  have h3 := p.cup a hM X Y Z hZ bb bb' φ
  rw [hij.spec _ _ _ h2] at h3
  simp only [hi.spec _ _ _ hX, hj.spec _ _ _ hY] at h3
  rw [map_mul] at h3
  refine mul_left_cancel₀ (mul_ne_zero (tB_pow_ne hF N) (tB_pow_ne hF N')) (h3.trans ?_)
  simp only [Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero`. Take `⟨w, hw⟩` from `e.one a hM`. Conclude with `⟨w, by rw [pow_zero, one_smul]; exact hL.one_uniq a _ _ (b.one a hM z hz) hw⟩`. Consider the case `succ k ih`.

Take `⟨y, hy, hc⟩` from `hz`. Take `⟨w, hw⟩` from `ih y hy`. Take `⟨w', hw'⟩` from `hS.cup_ex M w v`. Establish `h1` using `b.cup a hM y x z hc`. Rewrite `h1` using `[hw, hx]`.

Use `⟨w', ?_⟩` and prove the remaining obligations. Establish `h2` using `hL.cup_uniq a _ _ _ _ h1 (hL.cup_smul a _ _ _ _ _ (e.cup a hM w v w' hw'))`. Rewrite using `[pow_succ]`. Conclude with `h2`.
-/
private theorem pow_rep (hS : EtSide G) (hL : D.Laws G) (hM : G M) (x : (D.H a).N 2) (v : M.T 2)
    (hx : b.β a 2 x = R.t • e.e a 2 v) (k : ℕ) (z : (D.H a).N (2 * k))
    (hz : IsPow (N := (D.H a).N) (D.H a).one (D.H a).cup x k z) :
    ∃ w : M.T (2 * k), b.β a (2 * k) z = R.t ^ k • e.e a (2 * k) w := by
  induction k with
  | zero =>
    obtain ⟨w, hw⟩ := e.one a hM
    exact ⟨w, by rw [pow_zero, one_smul]; exact hL.one_uniq a _ _ (b.one a hM z hz) hw⟩
  | succ k ih =>
    obtain ⟨y, hy, hc⟩ := hz
    obtain ⟨w, hw⟩ := ih y hy
    obtain ⟨w', hw'⟩ := hS.cup_ex M w v
    have h1 := b.cup a hM y x z hc
    rw [hw, hx] at h1
    refine ⟨w', ?_⟩
    have h2 := hL.cup_uniq a _ _ _ _ h1 (hL.cup_smul a _ _ _ _ _ (e.cup a hM w v w' hw'))
    rw [pow_succ]
    exact h2

/- English proof (translation)
Take `⟨x, z, φ, hx, hz, hU⟩` from `p.c1 a hM d hd`. Take `⟨v, hv⟩` from `e.c1 a hM`. Establish `h1` using `hL.first_chern_class_unique a _ _ (b.c1 a hM x hx) hv`. Take `⟨w, hw⟩` from `pow_rep hS hL hM x v h1 d z hz`. Use `⟨M.toV _ w, φ, fun h0 => ?_⟩` and prove the remaining obligations.

Take `⟨_, y, _, hy⟩` from `hU`. Rewrite `hy` using `[hC.spec _ _ _ hw, h0, mul_zero, zero_mul]`. Conclude with `zero_ne_one hy`.
-/
private theorem IsVal.top {d : ℕ} {C : M.V (2 * d) →+ (Module.Dual K (HdR M.q (2 * d)) → R.B)} (hC : IsVal e b p a (2 * d) C)
    (hF : R.Facts) (hS : EtSide G) (hL : D.Laws G) (hM : G M) (hd : M.Conn d) : ∃ w φ, C w φ ≠ 0 := by
  obtain ⟨x, z, φ, hx, hz, hU⟩ := p.c1 a hM d hd
  obtain ⟨v, hv⟩ := e.c1 a hM
  have h1 := hL.first_chern_class_unique a _ _ (b.c1 a hM x hx) hv
  obtain ⟨w, hw⟩ := pow_rep hS hL hM x v h1 d z hz
  refine ⟨M.toV _ w, φ, fun h0 => ?_⟩
  obtain ⟨_, y, _, hy⟩ := hU
  rw [hC.spec _ _ _ hw, h0, mul_zero, zero_mul] at hy
  exact zero_ne_one hy

/- English proof (translation)
Take `⟨N, hN⟩` from `exists_rep e b hM a n`. Take `⟨m, hm⟩` from `b.inj a hM n`. Use `choose xs hxs using fun k => hN (v k)`. Establish `h1` using `hm (R.t ^ u • ∑ k, (c k • xs k)) (by`. Simplify using `only [map_smul, map_sum, hxs]`.

Simplify using `only [smul_comm (c _) (R.t ^ N), ← Finset.smul_sum]`. Rewrite using `[smul_comm, h, smul_zero])`. Establish `h2` using `congrArg (fun y => p.κ a n y ψ) h1`. Simplify using `only [p.lin a hM, map_zero, AddMonoidHom.zero_apply, map_sum, AddMonoidHom.finset_sum_apply, hC.spec _ _ _ (hxs _)] at h2`. Establish `h3` using `(mul_eq_zero.mp ((mul_eq_zero.mp h2).resolve_left (tB_pow_ne hF m))).resolve_left (tB_pow_ne hF u)`.

Establish `h4 : R.i (R.t ^ N) * ∑ k, R.i (c k) * C (M.toV n (v k)) ψ = 0`. Rewrite using `[Finset.mul_sum, ← h3]`. Conclude with `Finset.sum_congr rfl fun _ _ => by ring`. Conclude with `(mul_eq_zero.mp h4).resolve_left (tB_pow_ne hF N)`.
-/
private theorem IsVal.van {n : ℕ} {C : M.V n →+ (Module.Dual K (HdR M.q n) → R.B)} (hC : IsVal e b p a n C)
    (hF : R.Facts) (hM : G M) {ι : Type} [Fintype ι] (v : ι → M.T n) (c : ι → R.A) (u : ℕ)
    (h : R.t ^ u • ∑ k, c k • e.e a n (v k) = 0) (ψ) : ∑ k, R.i (c k) * C (M.toV n (v k)) ψ = 0 := by
  obtain ⟨N, hN⟩ := exists_rep e b hM a n
  obtain ⟨m, hm⟩ := b.inj a hM n
  choose xs hxs using fun k => hN (v k)
  have h1 := hm (R.t ^ u • ∑ k, (c k • xs k)) (by
    simp only [map_smul, map_sum, hxs]
    simp only [smul_comm (c _) (R.t ^ N), ← Finset.smul_sum]
    rw [smul_comm, h, smul_zero])
  have h2 := congrArg (fun y => p.κ a n y ψ) h1
  simp only [p.lin a hM, map_zero, AddMonoidHom.zero_apply, map_sum, AddMonoidHom.finset_sum_apply,
    hC.spec _ _ _ (hxs _)] at h2
  have h3 := (mul_eq_zero.mp ((mul_eq_zero.mp h2).resolve_left (tB_pow_ne hF m))).resolve_left (tB_pow_ne hF u)
  have h4 : R.i (R.t ^ N) * ∑ k, R.i (c k) * C (M.toV n (v k)) ψ = 0 := by
    rw [Finset.mul_sum, ← h3]
    exact Finset.sum_congr rfl fun _ _ => by ring
  exact (mul_eq_zero.mp h4).resolve_left (tB_pow_ne hF N)

/- English proof (translation)
Take `⟨hsub, hdual⟩` from `hS.dual M hM d hd`. Distinguish the cases in `hj : 2 * d < j`. Use `hsub j hj` as an intermediate fact. Use `Finset.sum_eq_zero fun k _ => ?_` and prove the remaining obligations. Rewrite using `[Subsingleton.elim (M.toV j (v k)) 0, map_zero, map_zero, zero_mul]`.

Take `⟨j', hj'⟩ : ∃ j', j + j' = 2 * d` from `⟨2 * d - j, by omega⟩`. Take `⟨r, g, hspan, htrans, hfun⟩` from `hdual j j' hj'`. Use `choose C hC using fun n => exists_val hF e b p hM a n`. Establish `htop : ∀ N, N = 2 * d → ∃ w φ, C N w φ ≠ 0`. Introduce and unpack `_ rfl`.

Conclude with `(hC _).top hF hS hL hM hd`. Take `⟨w, φ, hw⟩` from `htop _ hj'`. Establish `hg : ∃ s, C (j + j') (g s) φ ≠ 0`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`.

Establish `hw' : w ∈ Submodule.span ℚ_[l] (Set.range g)` using `by rw [hspan]; trivial`. Use `hw (Submodule.span_induction (p := fun w _ => C (j + j') w φ = 0) ?_ (by simp) ?_ ?_ hw')` and prove the remaining obligations. Introduce and unpack `_ ⟨s, rfl⟩`. Conclude with `hcon s`. Introduce `x y _ _ hx hy`.

Rewrite using `[map_add, Pi.add_apply, hx, hy, add_zero]`. Introduce `z x _ hx`. Rewrite using `[(hC _).smul, hx, mul_zero]`. Take `⟨s₀, hs₀⟩` from `hg`. Establish `hall : ∀ s, C (j + j') (g s) φ ≠ 0`.

Introduce `s h0`. Take `⟨σ, z, hz, hact⟩` from `htrans s s₀`. Establish `h1` using `(hC _).equi hF hL hM σ (g s) φ`. Rewrite `h1` using `[hact, (hC _).smul, h0, map_zero]`. Conclude with `(mul_ne_zero ((map_ne_zero _).mpr hz) hs₀) h1`.

Use `haveI := (p.fin M hM j).1`. Use `haveI := (p.fin M hM j').1`. Set `bb` to `Module.finBasis K (HdR M.q j)`. Set `bb'` to `Module.finBasis K (HdR M.q j')`. Establish `hf : f ∈ Submodule.span ℚ_[l] {f : Module.Dual ℚ_[l] (M.V j) | ∃ (s : Fin r) (y : M.T j'), ∀ x : M.T j, ∃ z, M.CupT x y z ∧ M.toV (j + j') z = f (M.toV j x) • g s}` using `by rw [hfun]; trivial`.

Use `Submodule.span_induction (p := fun f _ => ∑ k, R.q (f (M.toV j (v k))) * R.i (c k) = 0) ?_ (by simp) ?_ ?_ hf` and prove the remaining obligations. Introduce and unpack `f ⟨s, y, hy⟩ choose zs hz1 hz2 using fun k => hy (v k)`. Establish `h1 : ∑ k, R.i (c k) * C (j + j') (M.toV _ (zs k)) φ = 0`. Simplify using `only [fun k => (hC j).cup (hC j') (hC (j + j')) hF hL hM _ y _ (hz1 k) bb bb' φ, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`.

Use `Finset.sum_eq_zero fun s₁ _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_eq_zero fun s₂ _ => ?_` and prove the remaining obligations. Establish `h2` using `(hC j).van hF hM v c u h (bb.coord s₁)`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[Finset.sum_mul]; exact Finset.sum_congr rfl fun _ _ => by ring`. Use `_ = 0 := by rw [h2, zero_mul]`. Simplify using `only [hz2, (hC _).smul] at h1`. Establish `h3 : (∑ k, R.q (f (M.toV j (v k))) * R.i (c k)) * C (j + j') (g s) φ = 0`. Rewrite using `[Finset.sum_mul, ← h1]; exact Finset.sum_congr rfl fun _ _ => by ring`.

Conclude with `(mul_eq_zero.mp h3).resolve_right (hall s)`. Introduce `x y _ _ hx hy`. Simplify using `only [LinearMap.add_apply, map_add, add_mul, Finset.sum_add_distrib, hx, hy, add_zero]`. Introduce `z x _ hx`. Simplify using `only [LinearMap.smul_apply, smul_eq_mul, map_mul, mul_assoc, ← Finset.mul_sum, hx, mul_zero]`.
-/
private theorem inj_conn (hF : R.Facts) (hS : EtSide G) (hL : D.Laws G) (e : EMap G D) (b : BMap G D) (p : PMap G D)
    {M : Model l K} (hM : G M) {d : ℕ} (hd : M.Conn d) (a : D.Ch M) (j : ℕ) {ι : Type} [Fintype ι]
    (v : ι → M.T j) (c : ι → R.A) (u : ℕ) (h : R.t ^ u • ∑ k, c k • e.e a j (v k) = 0)
    (f : Module.Dual ℚ_[l] (M.V j)) : ∑ k, R.q (f (M.toV j (v k))) * R.i (c k) = 0 := by
  obtain ⟨hsub, hdual⟩ := hS.dual M hM d hd
  by_cases hj : 2 * d < j
  · have := hsub j hj
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [Subsingleton.elim (M.toV j (v k)) 0, map_zero, map_zero, zero_mul]
  obtain ⟨j', hj'⟩ : ∃ j', j + j' = 2 * d := ⟨2 * d - j, by omega⟩
  obtain ⟨r, g, hspan, htrans, hfun⟩ := hdual j j' hj'
  choose C hC using fun n => exists_val hF e b p hM a n
  have htop : ∀ N, N = 2 * d → ∃ w φ, C N w φ ≠ 0 := by
    rintro _ rfl; exact (hC _).top hF hS hL hM hd
  obtain ⟨w, φ, hw⟩ := htop _ hj'
  have hg : ∃ s, C (j + j') (g s) φ ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    have hw' : w ∈ Submodule.span ℚ_[l] (Set.range g) := by rw [hspan]; trivial
    refine hw (Submodule.span_induction (p := fun w _ => C (j + j') w φ = 0) ?_ (by simp) ?_ ?_ hw')
    · rintro _ ⟨s, rfl⟩; exact hcon s
    · intro x y _ _ hx hy; rw [map_add, Pi.add_apply, hx, hy, add_zero]
    · intro z x _ hx; rw [(hC _).smul, hx, mul_zero]
  obtain ⟨s₀, hs₀⟩ := hg
  have hall : ∀ s, C (j + j') (g s) φ ≠ 0 := by
    intro s h0
    obtain ⟨σ, z, hz, hact⟩ := htrans s s₀
    have h1 := (hC _).equi hF hL hM σ (g s) φ
    rw [hact, (hC _).smul, h0, map_zero] at h1
    exact (mul_ne_zero ((map_ne_zero _).mpr hz) hs₀) h1
  haveI := (p.fin M hM j).1
  haveI := (p.fin M hM j').1
  let bb := Module.finBasis K (HdR M.q j)
  let bb' := Module.finBasis K (HdR M.q j')
  have hf : f ∈ Submodule.span ℚ_[l] {f : Module.Dual ℚ_[l] (M.V j) | ∃ (s : Fin r) (y : M.T j'),
      ∀ x : M.T j, ∃ z, M.CupT x y z ∧ M.toV (j + j') z = f (M.toV j x) • g s} := by rw [hfun]; trivial
  refine Submodule.span_induction (p := fun f _ => ∑ k, R.q (f (M.toV j (v k))) * R.i (c k) = 0) ?_ (by simp) ?_ ?_ hf
  · rintro f ⟨s, y, hy⟩
    choose zs hz1 hz2 using fun k => hy (v k)
    have h1 : ∑ k, R.i (c k) * C (j + j') (M.toV _ (zs k)) φ = 0 := by
      simp only [fun k => (hC j).cup (hC j') (hC (j + j')) hF hL hM _ y _ (hz1 k) bb bb' φ, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun s₁ _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun s₂ _ => ?_
      have h2 := (hC j).van hF hM v c u h (bb.coord s₁)
      calc _ = (∑ k, R.i (c k) * C j (M.toV j (v k)) (bb.coord s₁)) * (C j' (M.toV j' y) (bb'.coord s₂) *
              R.o (φ (p.cupR M j j' (bb s₁) (bb' s₂)))) := by
            rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun _ _ => by ring
        _ = 0 := by rw [h2, zero_mul]
    simp only [hz2, (hC _).smul] at h1
    have h3 : (∑ k, R.q (f (M.toV j (v k))) * R.i (c k)) * C (j + j') (g s) φ = 0 := by
      rw [Finset.sum_mul, ← h1]; exact Finset.sum_congr rfl fun _ _ => by ring
    exact (mul_eq_zero.mp h3).resolve_right (hall s)
  · intro x y _ _ hx hy
    simp only [LinearMap.add_apply, map_add, add_mul, Finset.sum_add_distrib, hx, hy, add_zero]
  · intro z x _ hx
    simp only [LinearMap.smul_apply, smul_eq_mul, map_mul, mul_assoc, ← Finset.mul_sum, hx, mul_zero]

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem toV_pullT {M N : Model l K} (u : M.X ⟶ N.X) (hu : u ≫ N.p = M.p) (n : ℕ) (v : N.T n) :
    M.toV n (Model.pullT u hu n v) = Model.pullV u hu n (N.toV n v) := rfl

/- English proof (translation)
Introduce `l _ K R G D hF hS hL e b p M hM a j ι _ v c u h f`. Take `⟨r, P, d, uu, hu, hP, hinj⟩` from `hS.comp M hM`. Establish `hs : ∀ s (f' : Module.Dual ℚ_[l] ((P s).V j)), ∑ k, R.q (f' (Model.pullV (uu s) (hu s) j (M.toV j (v k)))) * R.i (c k) = 0`. Introduce `s f'`. Take `⟨a₀⟩` from `hL.ch (P s) (hP s).1`.

Take `⟨a', _, ⟨m⟩⟩` from `hL.refine (P s) M (uu s) (hu s) (hP s).1 hM a₀ a`. Use `inj_conn hF hS hL e b p (hP s).1 (hP s).2 a' j (fun k => Model.pullT (uu s) (hu s) j (v k)) c u (by` as an intermediate fact. Establish `h1` using `congrArg (D.pullA m j) h`. Simplify `h1) f'` using `only [map_smul, map_sum, map_zero, ← e.nat m (hP s).1 hM]`. Simplify `this` using `only [toV_pullT]`.

Set `L : M.V j →ₗ[ℚ_[l]] ∀ s, (P s).V j` to `LinearMap.pi fun s => Model.pullV (uu s) (hu s) j`. Establish `hk : LinearMap.ker L = ⊥` using `LinearMap.ker_eq_bot'.2 fun w hw => hinj j w fun s => congrFun hw s`. Take `⟨g, hg⟩` from `L.exists_leftInverse_of_injective hk`. Set `f' : ∀ s, Module.Dual ℚ_[l] ((P s).V j)` to `fun s => (f ∘ₗ g) ∘ₗ LinearMap.single ℚ_[l] (fun s => (P s).V j) s`. Establish `hf : ∀ w, f w = ∑ s, f' s (Model.pullV (uu s) (hu s) j w)`.

Introduce `w`. Establish `h1 : g (L w) = w` using `LinearMap.congr_fun hg w`. Use `conv_lhs => rw [← h1, ← Finset.univ_sum_single (L w), map_sum, map_sum]`. Both sides reduce to the same expression. Simplify using `only [hf, map_sum, Finset.sum_mul]`.

Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_eq_zero fun s _ => hs s (f' s)`.
-/
theorem injAbs : UpperTheory.Ru.crystallineComparison.InjAbs := by
  intro l _ K R G D hF hS hL e b p M hM a j ι _ v c u h f
  obtain ⟨r, P, d, uu, hu, hP, hinj⟩ := hS.comp M hM
  have hs : ∀ s (f' : Module.Dual ℚ_[l] ((P s).V j)),
      ∑ k, R.q (f' (Model.pullV (uu s) (hu s) j (M.toV j (v k)))) * R.i (c k) = 0 := by
    intro s f'
    obtain ⟨a₀⟩ := hL.ch (P s) (hP s).1
    obtain ⟨a', _, ⟨m⟩⟩ := hL.refine (P s) M (uu s) (hu s) (hP s).1 hM a₀ a
    have := inj_conn hF hS hL e b p (hP s).1 (hP s).2 a' j (fun k => Model.pullT (uu s) (hu s) j (v k)) c u (by
      have h1 := congrArg (D.pullA m j) h
      simpa only [map_smul, map_sum, map_zero, ← e.nat m (hP s).1 hM] using h1) f'
    simpa only [toV_pullT] using this
  let L : M.V j →ₗ[ℚ_[l]] ∀ s, (P s).V j := LinearMap.pi fun s => Model.pullV (uu s) (hu s) j
  have hk : LinearMap.ker L = ⊥ := LinearMap.ker_eq_bot'.2 fun w hw => hinj j w fun s => congrFun hw s
  obtain ⟨g, hg⟩ := L.exists_leftInverse_of_injective hk
  let f' : ∀ s, Module.Dual ℚ_[l] ((P s).V j) := fun s => (f ∘ₗ g) ∘ₗ LinearMap.single ℚ_[l] (fun s => (P s).V j) s
  have hf : ∀ w, f w = ∑ s, f' s (Model.pullV (uu s) (hu s) j w) := by
    intro w
    have h1 : g (L w) = w := LinearMap.congr_fun hg w
    conv_lhs => rw [← h1, ← Finset.univ_sum_single (L w), map_sum, map_sum]
    rfl
  simp only [hf, map_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_eq_zero fun s _ => hs s (f' s)

end UpperTheory.Ru.crystallineComparison
