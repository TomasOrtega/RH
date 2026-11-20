import Formalism.CoboundaryTransfers.StatementAPI

noncomputable section

namespace Formalism.CoboundaryTransfers

/- English proof (translation)
Introduce `O A _ _ _ B M D _ _ _ _ W u hu i n hn`. Take `⟨t, ht⟩` from `hu`. Take `⟨n', hn', hγ⟩` from `W.γ_N n hn`. Establish `hw : ∀ k : ℕ, ∃ r : A, (algebraMap O A u + B.X * t) ^ k = algebraMap O A (u ^ k) + B.X * r`. Introduce `k`.

Proceed by induction on `k with`. Consider the case `zero => exact ⟨0, by simp⟩`. Consider the case `succ k ih`. Take `⟨r, hr⟩` from `ih`. Use `⟨r * (algebraMap O A u + B.X * t) + algebraMap O A (u ^ k) * t, ?_⟩` and prove the remaining obligations.

Rewrite using `[pow_succ, hr, pow_succ, map_mul]`. Expand and normalize the polynomial expressions, which then agree. Take `⟨r, hr⟩` from `hw i`. Establish `hγn : W.γ n = n + B.X • n'` using `by rw [← hγ]; abel`. Use `⟨r • n + (algebraMap O A u + B.X * t) ^ i • n', ?_, ?_⟩` and prove the remaining obligations.

Conclude with `W.N.add_mem (W.N.smul_mem _ hn) (W.N.smul_mem _ hn')`. Rewrite using `[W.γ_smul, map_pow, ht, mul_pow, hγn, hr, ← algebraMap_smul A (u ^ i) (B.X ^ i • n)] module`.
-/
theorem gammaGradedStep_holds : GradedStep := by
  intro O A _ _ _ B M D _ _ _ _ W u hu i n hn
  obtain ⟨t, ht⟩ := hu
  obtain ⟨n', hn', hγ⟩ := W.γ_N n hn
  have hw : ∀ k : ℕ, ∃ r : A, (algebraMap O A u + B.X * t) ^ k
      = algebraMap O A (u ^ k) + B.X * r := by
    intro k
    induction k with
    | zero => exact ⟨0, by simp⟩
    | succ k ih =>
      obtain ⟨r, hr⟩ := ih
      refine ⟨r * (algebraMap O A u + B.X * t) + algebraMap O A (u ^ k) * t, ?_⟩
      rw [pow_succ, hr, pow_succ, map_mul]; ring
  obtain ⟨r, hr⟩ := hw i
  have hγn : W.γ n = n + B.X • n' := by rw [← hγ]; abel
  refine ⟨r • n + (algebraMap O A u + B.X * t) ^ i • n', ?_, ?_⟩
  · exact W.N.add_mem (W.N.smul_mem _ hn) (W.N.smul_mem _ hn')
  · rw [W.γ_smul, map_pow, ht, mul_pow, hγn, hr,
      ← algebraMap_smul A (u ^ i) (B.X ^ i • n)]
    module

/- English proof (translation)
Introduce `O A _ _ _ B M D _ _ _ _ W u a hyp`. It suffices to establish `h : ∀ j, j ≤ a → ∀ n ∈ W.N, ∃ x ∈ W.N, ∃ z' ∈ W.N, (∏ i ∈ Finset.Icc 1 j, (1 - u ^ i)) • (B.X • n) = (W.γ (B.X • x) - B.X • x) + B.X ^ (j + 1) • z' from h a le_rfl`. Introduce `j`. Proceed by induction on `j with`. Consider the case `zero => intro _ n hn; exact ⟨0, W.N.zero_mem, n, hn, by simp⟩`.

Consider the case `succ j ih`. Introduce `hj n hn`. Take `⟨x, hx, m, hm, he⟩` from `ih (by omega) n hn`. Take `⟨n', hn', hg⟩` from `hyp (j+1) (by omega) hj m hm`. Use `⟨(1 - u^(j+1)) • x - B.X ^ j • m, ?_, n', hn', ?_⟩` and prove the remaining obligations.

Conclude with `W.N.sub_mem (W.N.smul_of_tower_mem _ hx) (W.N.smul_mem _ hm)`. Rewrite using `[Finset.prod_Icc_succ_top (by omega), mul_comm, mul_smul, he]`. Establish `e1 : B.X • ((1 - u^(j+1)) • x - B.X ^ j • m) = (1 - u^(j+1)) • (B.X • x) - B.X ^ (j+1) • m`. Rewrite using `[smul_sub, smul_comm, smul_smul, ← pow_succ']`. Rewrite using `[e1, map_sub, LinearMap.map_smul, hg]`.

Simplify using `only [smul_sub, smul_add, sub_smul, one_smul]`. Normalize the expressions using the abelian group laws.
-/
theorem gammaImageProduct_holds : GammaOnto := by
  intro O A _ _ _ B M D _ _ _ _ W u a hyp
  suffices h : ∀ j, j ≤ a → ∀ n ∈ W.N, ∃ x ∈ W.N, ∃ z' ∈ W.N,
      (∏ i ∈ Finset.Icc 1 j, (1 - u ^ i)) • (B.X • n) =
        (W.γ (B.X • x) - B.X • x) + B.X ^ (j + 1) • z' from h a le_rfl
  intro j
  induction j with
  | zero => intro _ n hn; exact ⟨0, W.N.zero_mem, n, hn, by simp⟩
  | succ j ih =>
    intro hj n hn
    obtain ⟨x, hx, m, hm, he⟩ := ih (by omega) n hn
    obtain ⟨n', hn', hg⟩ := hyp (j+1) (by omega) hj m hm
    refine ⟨(1 - u^(j+1)) • x - B.X ^ j • m, ?_, n', hn', ?_⟩
    · exact W.N.sub_mem (W.N.smul_of_tower_mem _ hx) (W.N.smul_mem _ hm)
    · rw [Finset.prod_Icc_succ_top (by omega), mul_comm, mul_smul, he]
      have e1 : B.X • ((1 - u^(j+1)) • x - B.X ^ j • m)
          = (1 - u^(j+1)) • (B.X • x) - B.X ^ (j+1) • m := by
        rw [smul_sub, smul_comm, smul_smul, ← pow_succ']
      rw [e1, map_sub, LinearMap.map_smul, hg]
      simp only [smul_sub, smul_add, sub_smul, one_smul]
      abel

section Claim
variable {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {B : Base O A} {M : ℕ}
  {D : Type} [AddCommGroup D] [Module A D] [Module O D] [IsScalarTower O A D]

/- English proof (translation)
Proceed by induction on `f using Polynomial.induction_on with`. Consider the case `C a`. Introduce `y hy`. Rewrite using `[Polynomial.aeval_C, Module.algebraMap_end_apply]`. Conclude with `S.smul_mem a hy`.

Consider the case `add p q hp hq`. Introduce `y hy`. Rewrite using `[map_add, LinearMap.add_apply]`. Conclude with `S.add_mem (hp y hy) (hq y hy)`. Consider the case `monomial n a ih`.

Introduce `y hy`. Rewrite using `[pow_succ, ← mul_assoc, map_mul, Polynomial.aeval_X, Module.End.mul_apply]`. Conclude with `ih _ (hS y hy)`.
-/
lemma aeval_stable (δ : D →ₗ[O] D) (S : Submodule O D) (hS : ∀ y ∈ S, δ y ∈ S)
    (f : Polynomial O) : ∀ y ∈ S, Polynomial.aeval δ f y ∈ S := by
  induction f using Polynomial.induction_on with
  | C a =>
    intro y hy
    rw [Polynomial.aeval_C, Module.algebraMap_end_apply]
    exact S.smul_mem a hy
  | add p q hp hq =>
    intro y hy
    rw [map_add, LinearMap.add_apply]
    exact S.add_mem (hp y hy) (hq y hy)
  | monomial n a ih =>
    intro y hy
    rw [pow_succ, ← mul_assoc, map_mul, Polynomial.aeval_X, Module.End.mul_apply]
    exact ih _ (hS y hy)

def QS (W : WachMod B M D) : Submodule O D where
  carrier := {y | B.Q ^ M • y ∈ W.N}
  add_mem' := by
    intro x y hx hy; show B.Q ^ M • (x + y) ∈ W.N; rw [smul_add]; exact W.N.add_mem hx hy
  zero_mem' := by show B.Q ^ M • (0 : D) ∈ W.N; simp
  smul_mem' := by
    intro c y hy; show B.Q ^ M • (c • y) ∈ W.N; rw [smul_comm]; exact W.N.smul_of_tower_mem c hy

/- English proof (translation)
The claim follows from `W.N.smul_mem _ hx`.
-/
lemma N_QInv (W : WachMod B M D) {x : D} (hx : x ∈ W.N) : W.QInv x := W.N.smul_mem _ hx

/- English proof (translation)
Use `show B.Q ^ M • (b • y) ∈ W.N`. Rewrite using `[smul_comm]`. Conclude with `W.N.smul_mem b hy`.
-/
lemma QInv_smulA (W : WachMod B M D) (b : A) {y : D} (hy : W.QInv y) : W.QInv (b • y) := by
  show B.Q ^ M • (b • y) ∈ W.N
  rw [smul_comm]
  exact W.N.smul_mem b hy

/- English proof (translation)
Introduce `y hy`. Take `⟨y', hy', hyy⟩` from `W.γ_QN y hy`. Establish `h3 : δ y = y'`. Establish `h` using `W.X_inj (δ y - y') (by rw [smul_sub, h2, hyy, sub_self])`. Conclude with `sub_eq_zero.mp h`.

Use `show B.Q ^ M • δ y ∈ W.N`. Rewrite using `[h3]`. Conclude with `hy'`.
-/
lemma δ_QInv (W : WachMod B M D) (δ : D →ₗ[O] D) (h2 : ∀ y, B.X • δ y = W.γ y - y) :
    ∀ y, W.QInv y → W.QInv (δ y) := by
  intro y hy
  obtain ⟨y', hy', hyy⟩ := W.γ_QN y hy
  have h3 : δ y = y' := by
    have h := W.X_inj (δ y - y') (by rw [smul_sub, h2, hyy, sub_self])
    exact sub_eq_zero.mp h
  show B.Q ^ M • δ y ∈ W.N
  rw [h3]
  exact hy'

/- English proof (translation)
Introduce `n hn`. Take `⟨x', hx', hxx⟩` from `W.γ_N n hn`. Establish `h3 : δ n = x'`. Establish `h` using `W.X_inj (δ n - x') (by rw [smul_sub, h2, hxx, sub_self])`. Conclude with `sub_eq_zero.mp h`.

Rewrite using `[h3]`. Conclude with `hx'`.
-/
lemma δ_N (W : WachMod B M D) (δ : D →ₗ[O] D) (h2 : ∀ y, B.X • δ y = W.γ y - y) :
    ∀ n ∈ W.N, δ n ∈ W.N := by
  intro n hn
  obtain ⟨x', hx', hxx⟩ := W.γ_N n hn
  have h3 : δ n = x' := by
    have h := W.X_inj (δ n - x') (by rw [smul_sub, h2, hxx, sub_self])
    exact sub_eq_zero.mp h
  rw [h3]
  exact hx'

/- English proof (translation)
Establish `δN` using `δ_N W δ h2`. Establish `RN : ∀ f : Polynomial O, ∀ n ∈ W.N, Polynomial.aeval δ f n ∈ W.N` using `fun f => aeval_stable δ (W.N.restrictScalars O) δN f`. Establish `RQ : ∀ f : Polynomial O, ∀ y, W.QInv y → W.QInv (Polynomial.aeval δ f y)` using `fun f => aeval_stable δ (QS W) (δ_QInv W δ h2) f`. Establish `Lφ : ∀ m ∈ W.N, ∃ m' ∈ W.N, W.φ (B.X ^ (a + 1) • m) = B.X ^ (a + 1) • m'`. Introduce `m hm`.

Take `⟨v, hv⟩` from `h1`. Use `⟨v ^ (a + 1) • B.Q ^ (k * (a + 1) - M) • (B.Q ^ M • W.φ m), W.N.smul_mem _ (W.N.smul_mem _ (W.φ_N m hm)), ?_⟩` and prove the remaining obligations. Establish `hexp : B.Q ^ (k * (a + 1) - M) * B.Q ^ M = (B.Q ^ k) ^ (a + 1)`. Rewrite using `[← pow_add, Nat.sub_add_cancel h1', pow_mul]`. Rewrite using `[W.φ_smul, map_pow, hv, smul_smul, smul_smul, smul_smul]`.

Use `congr 1`. Rewrite using `[mul_assoc (B.X ^ (a + 1) * v ^ (a + 1)), hexp]`. Expand and normalize the polynomial expressions, which then agree. Establish `φπ : ∀ x ∈ W.N, W.QInv (W.φ (B.X • x))`. Introduce `x hx`.

Rewrite using `[W.φ_smul]`. Conclude with `QInv_smulA W _ (W.φ_N x hx)`. Establish `tf : ∀ i : ℕ, ∀ v, W.QInv v → ((B.p : O) ^ i) • v ∈ W.N → v ∈ W.N`. Introduce `i`. Proceed by induction on `i with`.

Consider the case `zero => intro v _ h`. Simplify using `using h`. Consider the case `succ i ih`. Introduce `v hv h`. Apply `ih v hv` to reduce the goal to its premises.

Apply `h4 _ ((QS W).smul_mem _ hv)` to reduce the goal to its premises. Rewrite using `[smul_smul, ← pow_succ']`. Conclude with `h`. Take `⟨hy, n, hn, hzn⟩` from `hyz`. Substitute `hzn` using the available equality.

Take `⟨x, hx, z', hz', hc⟩` from `h6 n hn`. Take `⟨m', hm', hφm⟩` from `Lφ z' hz'`. Use `set Y' := cΓ • y - (W.φ (B.X • x) - B.X • x) with hY'`. Establish `hY'Q : W.QInv Y'` using `(QS W).sub_mem ((QS W).smul_mem _ hy) ((QS W).sub_mem (φπ x hx) (N_QInv W (W.N.smul_mem _ hx)))`. Establish `eA : B.X • (cΓ • ((B.p : O) ^ j) • w - δ Y' - B.X ^ a • (z' - m')) = 0`.

Establish `e1 : cΓ • ((B.p : O) ^ j) • (B.X • w) = cΓ • W.d1 y (B.X • n)` using `by rw [hj]`. Establish `e2 : cΓ • W.d1 y (B.X • n) = (W.γ Y' - Y') + (B.X ^ (a + 1) • z' - B.X ^ (a + 1) • m')`. Simplify using `only [WachMod.d1, smul_sub, ← LinearMap.map_smul, hc, hY', map_sub, map_add, W.comm, hφm]`. Normalize the expressions using the abelian group laws. Rewrite using `[smul_sub, smul_sub, h2, smul_comm B.X cΓ, smul_comm B.X ((B.p : O) ^ j), e1, e2, smul_smul, ← pow_succ', smul_sub]`.

Normalize the expressions using the abelian group laws. Establish `eA' : cΓ • ((B.p : O) ^ j) • w = δ Y' + B.X ^ a • (z' - m')`. Use `W.X_inj _ eA` as an intermediate fact. Rewrite `this` using `[sub_sub, sub_eq_zero]`. Conclude with `this`.

Establish `eB : ((B.p : O) ^ j) • (cΓ • Polynomial.aeval δ R w) ∈ W.N`. Rewrite using `[smul_comm, ← LinearMap.map_smul, ← LinearMap.map_smul, eA', map_add]`. Use `W.N.add_mem ?_ (RN R _ (W.N.smul_mem _ (W.N.sub_mem hz' hm')))` and prove the remaining obligations. Establish `: Polynomial.aeval δ R (δ Y') = Polynomial.aeval δ (Polynomial.X * R) Y'`. Rewrite using `[mul_comm, map_mul, Polynomial.aeval_X, Module.End.mul_apply]`.

Rewrite using `[this]`. Conclude with `h3 Y' hY'Q`. Rewrite using `[LinearMap.map_smul]`. Conclude with `tf j _ ((QS W).smul_mem _ (RQ R w hw)) eB`.
-/
lemma claim_key (W : WachMod B M D) (δ : D →ₗ[O] D) (R : Polynomial O) (a k : ℕ) (cΓ : O)
    (h1 : B.PhiX k) (h1' : M ≤ k * (a + 1))
    (h2 : ∀ y, B.X • δ y = W.γ y - y)
    (h3 : ∀ y, W.QInv y → Polynomial.aeval δ (Polynomial.X * R) y ∈ W.N)
    (h4 : ∀ y, W.QInv y → (B.p : O) • y ∈ W.N → y ∈ W.N)
    (h6 : ∀ n ∈ W.N, ∃ x ∈ W.N, ∃ z' ∈ W.N,
      cΓ • (B.X • n) = (W.γ (B.X • x) - B.X • x) + B.X ^ (a + 1) • z')
    (w : D) (hw : W.QInv w) (j : ℕ) (y z : D) (hyz : W.C1 y z)
    (hj : ((B.p : O) ^ j) • (B.X • w) = W.d1 y z) :
    Polynomial.aeval δ R (cΓ • w) ∈ W.N := by
  have δN := δ_N W δ h2
  have RN : ∀ f : Polynomial O, ∀ n ∈ W.N, Polynomial.aeval δ f n ∈ W.N :=
    fun f => aeval_stable δ (W.N.restrictScalars O) δN f
  have RQ : ∀ f : Polynomial O, ∀ y, W.QInv y → W.QInv (Polynomial.aeval δ f y) :=
    fun f => aeval_stable δ (QS W) (δ_QInv W δ h2) f
  have Lφ : ∀ m ∈ W.N, ∃ m' ∈ W.N, W.φ (B.X ^ (a + 1) • m) = B.X ^ (a + 1) • m' := by
    intro m hm
    obtain ⟨v, hv⟩ := h1
    refine ⟨v ^ (a + 1) • B.Q ^ (k * (a + 1) - M) • (B.Q ^ M • W.φ m),
      W.N.smul_mem _ (W.N.smul_mem _ (W.φ_N m hm)), ?_⟩
    have hexp : B.Q ^ (k * (a + 1) - M) * B.Q ^ M = (B.Q ^ k) ^ (a + 1) := by
      rw [← pow_add, Nat.sub_add_cancel h1', pow_mul]
    rw [W.φ_smul, map_pow, hv, smul_smul, smul_smul, smul_smul]
    congr 1
    rw [mul_assoc (B.X ^ (a + 1) * v ^ (a + 1)), hexp]
    ring
  have φπ : ∀ x ∈ W.N, W.QInv (W.φ (B.X • x)) := by
    intro x hx
    rw [W.φ_smul]; exact QInv_smulA W _ (W.φ_N x hx)
  have tf : ∀ i : ℕ, ∀ v, W.QInv v → ((B.p : O) ^ i) • v ∈ W.N → v ∈ W.N := by
    intro i
    induction i with
    | zero => intro v _ h; simpa using h
    | succ i ih =>
      intro v hv h
      apply ih v hv
      apply h4 _ ((QS W).smul_mem _ hv)
      rw [smul_smul, ← pow_succ']; exact h
  obtain ⟨hy, n, hn, hzn⟩ := hyz
  subst hzn
  obtain ⟨x, hx, z', hz', hc⟩ := h6 n hn
  obtain ⟨m', hm', hφm⟩ := Lφ z' hz'
  set Y' := cΓ • y - (W.φ (B.X • x) - B.X • x) with hY'
  have hY'Q : W.QInv Y' :=
    (QS W).sub_mem ((QS W).smul_mem _ hy) ((QS W).sub_mem (φπ x hx) (N_QInv W (W.N.smul_mem _ hx)))
  have eA : B.X • (cΓ • ((B.p : O) ^ j) • w - δ Y' - B.X ^ a • (z' - m')) = 0 := by
    have e1 : cΓ • ((B.p : O) ^ j) • (B.X • w) = cΓ • W.d1 y (B.X • n) := by rw [hj]
    have e2 : cΓ • W.d1 y (B.X • n) = (W.γ Y' - Y') + (B.X ^ (a + 1) • z' - B.X ^ (a + 1) • m') := by
      simp only [WachMod.d1, smul_sub, ← LinearMap.map_smul, hc, hY', map_sub, map_add, W.comm, hφm]
      abel
    rw [smul_sub, smul_sub, h2, smul_comm B.X cΓ, smul_comm B.X ((B.p : O) ^ j), e1, e2,
      smul_smul, ← pow_succ', smul_sub]
    abel
  have eA' : cΓ • ((B.p : O) ^ j) • w = δ Y' + B.X ^ a • (z' - m') := by
    have := W.X_inj _ eA; rw [sub_sub, sub_eq_zero] at this; exact this
  have eB : ((B.p : O) ^ j) • (cΓ • Polynomial.aeval δ R w) ∈ W.N := by
    rw [smul_comm, ← LinearMap.map_smul, ← LinearMap.map_smul, eA', map_add]
    refine W.N.add_mem ?_ (RN R _ (W.N.smul_mem _ (W.N.sub_mem hz' hm')))
    have : Polynomial.aeval δ R (δ Y') = Polynomial.aeval δ (Polynomial.X * R) Y' := by
      rw [mul_comm, map_mul, Polynomial.aeval_X, Module.End.mul_apply]
    rw [this]; exact h3 Y' hY'Q
  rw [LinearMap.map_smul]
  exact tf j _ ((QS W).smul_mem _ (RQ R w hw)) eB

/- English proof (translation)
Establish `RQ : ∀ f : Polynomial O, ∀ y, W.QInv y → W.QInv (Polynomial.aeval δ f y)` using `fun f => aeval_stable δ (QS W) (δ_QInv W δ h2) f`. Take `⟨R1, hR1⟩` from `Polynomial.X_dvd_sub_C (p := R)`. Establish `eD : (R.eval 0) • w = Polynomial.aeval δ R w - δ (Polynomial.aeval δ R1 w)`. Establish `: R = Polynomial.C (R.coeff 0) + Polynomial.X * R1` using `by rw [← hR1]; ring`. Use `conv_rhs => rw [this]`.

Rewrite using `[map_add, map_mul, Polynomial.aeval_C, Polynomial.aeval_X, LinearMap.add_apply, Module.End.mul_apply, Polynomial.coeff_zero_eq_eval_zero, Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply, Module.End.one_apply]`. Normalize the expressions using the abelian group laws. Take `⟨x2, hx2, z2, hz2, hc2⟩` from `h6 _ hm`. Take `⟨z3, hz3, h73⟩` from `h7 z2 hz2`. Use `⟨B.X • x2 - cΓ • Polynomial.aeval δ R1 w, B.X • (B.X ^ a • z3), ⟨?_, _, W.N.smul_mem _ hz3, rfl⟩, ?_⟩` and prove the remaining obligations.

Conclude with `(QS W).sub_mem (N_QInv W (W.N.smul_mem _ hx2)) ((QS W).smul_mem _ (RQ R1 w hw))`. Establish `e3 : B.X • (B.X ^ a • z3) = B.X ^ (a + 1) • z3` using `by rw [smul_smul, ← pow_succ']`. Simplify using `only [WachMod.d1, e3]`. Establish `e4 : (R.eval 0 * cΓ) • (B.X • w) = cΓ • (B.X • ((R.eval 0) • w))`. Rewrite using `[mul_comm, mul_smul, smul_comm (R.eval 0) B.X]`.

Rewrite using `[e4, eD, smul_sub, smul_sub, hc2, h73]`. Simplify using `only [h2, map_sub, LinearMap.map_smul, smul_sub]`. Normalize the expressions using the abelian group laws.
-/
lemma claim_fin (W : WachMod B M D) (δ : D →ₗ[O] D) (R : Polynomial O) (a : ℕ) (cΓ : O)
    (h2 : ∀ y, B.X • δ y = W.γ y - y)
    (h6 : ∀ n ∈ W.N, ∃ x ∈ W.N, ∃ z' ∈ W.N,
      cΓ • (B.X • n) = (W.γ (B.X • x) - B.X • x) + B.X ^ (a + 1) • z')
    (h7 : ∀ n ∈ W.N, ∃ z ∈ W.N, B.X ^ (a + 1) • n = B.X ^ (a + 1) • z - W.φ (B.X ^ (a + 1) • z))
    (w : D) (hw : W.QInv w) (hm : Polynomial.aeval δ R w ∈ W.N) :
    W.IsCob2 ((R.eval 0 * cΓ) • (B.X • w)) := by
  have RQ : ∀ f : Polynomial O, ∀ y, W.QInv y → W.QInv (Polynomial.aeval δ f y) :=
    fun f => aeval_stable δ (QS W) (δ_QInv W δ h2) f
  obtain ⟨R1, hR1⟩ := Polynomial.X_dvd_sub_C (p := R)
  have eD : (R.eval 0) • w = Polynomial.aeval δ R w - δ (Polynomial.aeval δ R1 w) := by
    have : R = Polynomial.C (R.coeff 0) + Polynomial.X * R1 := by rw [← hR1]; ring
    conv_rhs => rw [this]
    rw [map_add, map_mul, Polynomial.aeval_C, Polynomial.aeval_X, LinearMap.add_apply,
      Module.End.mul_apply, Polynomial.coeff_zero_eq_eval_zero, Algebra.algebraMap_eq_smul_one,
      LinearMap.smul_apply, Module.End.one_apply]
    abel
  obtain ⟨x2, hx2, z2, hz2, hc2⟩ := h6 _ hm
  obtain ⟨z3, hz3, h73⟩ := h7 z2 hz2
  refine ⟨B.X • x2 - cΓ • Polynomial.aeval δ R1 w, B.X • (B.X ^ a • z3),
    ⟨?_, _, W.N.smul_mem _ hz3, rfl⟩, ?_⟩
  · exact (QS W).sub_mem (N_QInv W (W.N.smul_mem _ hx2)) ((QS W).smul_mem _ (RQ R1 w hw))
  · have e3 : B.X • (B.X ^ a • z3) = B.X ^ (a + 1) • z3 := by rw [smul_smul, ← pow_succ']
    simp only [WachMod.d1, e3]
    have e4 : (R.eval 0 * cΓ) • (B.X • w) = cΓ • (B.X • ((R.eval 0) • w)) := by
      rw [mul_comm, mul_smul, smul_comm (R.eval 0) B.X]
    rw [e4, eD, smul_sub, smul_sub, hc2, h73]
    simp only [h2, map_sub, LinearMap.map_smul, smul_sub]
    abel

/- English proof (translation)
Introduce `O A _ _ _ B M D _ _ _ _ W δ R a k cΓ h1 h1' h2 h3 h4 h5 h6 h7 ω ⟨w, hw, hωw⟩ ⟨j, y, z, hyz, hj⟩`. Substitute `hωw` using the available equality. Establish `hk` using `claim_key W δ R a k cΓ h1 h1' h2 h3 h4 h6 w hw j y z hyz hj`. Rewrite `hk` using `[LinearMap.map_smul]`. Establish `RQ : W.QInv (Polynomial.aeval δ R w)` using `aeval_stable δ (QS W) (δ_QInv W δ h2) R w hw`.

Conclude with `claim_fin W δ R a cΓ h2 h6 h7 w hw (h5 _ RQ hk)`.
-/
theorem torsionKilledCriterion_holds : CoboundaryTransfer := by
  intro O A _ _ _ B M D _ _ _ _ W δ R a k cΓ h1 h1' h2 h3 h4 h5 h6 h7
    ω ⟨w, hw, hωw⟩ ⟨j, y, z, hyz, hj⟩
  subst hωw
  have hk := claim_key W δ R a k cΓ h1 h1' h2 h3 h4 h6 w hw j y z hyz hj
  rw [LinearMap.map_smul] at hk
  have RQ : W.QInv (Polynomial.aeval δ R w) :=
    aeval_stable δ (QS W) (δ_QInv W δ h2) R w hw
  exact claim_fin W δ R a cΓ h2 h6 h7 w hw (h5 _ RQ hk)

/- English proof (translation)
Introduce `ω ⟨w, hw, hωw⟩ ⟨j, y, z, hyz, hj⟩`. Substitute `hωw` using the available equality. Establish `hk` using `claim_key W δ R a k cΓ h1 h1' h2 h3 h4 h6 w hw j y z hyz hj`. Use `claim_fin W δ R a cΓ h2 h6 h7 (cΓ • w) ((QS W).smul_mem _ hw) hk` as an intermediate fact. Establish `e : (R.eval 0 * cΓ) • (B.X • (cΓ • w)) = (R.eval 0 * cΓ ^ 2) • (B.X • w)`.

Rewrite using `[smul_comm B.X cΓ w, smul_smul, pow_two, mul_assoc]`. Rewrite `this` using `[e]`. Then use the resulting hypothesis.
-/
theorem claimD_sq {O A : Type} [CommRing O] [CommRing A] [Algebra O A] (B : Base O A) (M : ℕ)
    (D : Type) [AddCommGroup D] [Module A D] [Module O D] [IsScalarTower O A D]
    (W : WachMod B M D) (δ : D →ₗ[O] D) (R : Polynomial O) (a k : ℕ) (cΓ : O)
    (h1 : B.PhiX k) (h1' : M ≤ k * (a + 1))
    (h2 : ∀ y, B.X • δ y = W.γ y - y)
    (h3 : ∀ y, W.QInv y → Polynomial.aeval δ (Polynomial.X * R) y ∈ W.N)
    (h4 : ∀ y, W.QInv y → (B.p : O) • y ∈ W.N → y ∈ W.N)
    (h6 : ∀ n ∈ W.N, ∃ x ∈ W.N, ∃ z' ∈ W.N,
      cΓ • (B.X • n) = (W.γ (B.X • x) - B.X • x) + B.X ^ (a + 1) • z')
    (h7 : ∀ n ∈ W.N, ∃ z ∈ W.N, B.X ^ (a + 1) • n = B.X ^ (a + 1) • z - W.φ (B.X ^ (a + 1) • z)) :
    W.TorsKilled (R.eval 0 * cΓ ^ 2) := by
  intro ω ⟨w, hw, hωw⟩ ⟨j, y, z, hyz, hj⟩
  subst hωw
  have hk := claim_key W δ R a k cΓ h1 h1' h2 h3 h4 h6 w hw j y z hyz hj
  have := claim_fin W δ R a cΓ h2 h6 h7 (cΓ • w) ((QS W).smul_mem _ hw) hk
  have e : (R.eval 0 * cΓ) • (B.X • (cΓ • w)) = (R.eval 0 * cΓ ^ 2) • (B.X • w) := by
    rw [smul_comm B.X cΓ w, smul_smul, pow_two, mul_assoc]
  rwa [e] at this

end Claim

end Formalism.CoboundaryTransfers
