import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.FrameWith
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.ExtFree
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.CompSel
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.PushSel
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.SelSub
open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

/- English proof (translation)
Introduce `l _ F n x x' j hE k`. Take `⟨m, b, p, -, hb, hp, -, hc, e, u, -, hu⟩` from `UpperTheory.V.Pa.Det.extFree j hE.1.1 hE.1.2.1 hE.1.2.2.1`. Take `⟨pS, pB, pL⟩` from `UpperTheory.V.Pa.Det.pushSel x x' j hE`. Establish `cS` using `fun i => (UpperTheory.V.Pa.Det.compSel x x' j hE (p i) (hp i) (fun N => (hc N).imp fun _ h y hy => h y hy i)).1`. Establish `cB` using `fun i => (UpperTheory.V.Pa.Det.compSel x x' j hE (p i) (hp i) (fun N => (hc N).imp fun _ h y hy => h y hy i)).2`.

Take `⟨S, hS⟩` from `(UpperTheory.V.Pa.Det.selSub F x'.t (x'.ρX x'.A) (x'.wX x'.A) (x'.wiX x'.A) (Od x'.A x'.A n x'.a)).2`. Establish `ha : x'.a = x.a` using `hE.1.2.2.2.2.1`. Use `⟨⟨k.g, fun i g => (k.κ i g).map j, fun i => pS _ (k.mem i), fun i v => (k.Y i v).map j, ?_, fun i v => pL _ _ _ (k.loc i v), ?_, ?_⟩, rfl, fun _ _ => rfl, fun _ _ => rfl⟩` and prove the remaining obligations. Introduce `i v r s`. Use `⟨fun h => ?_, fun _ => Submodule.mem_top⟩` and prove the remaining obligations.

Use `(k.Y_mem i v r s).1 (by rw [← ha]; exact h)` as an intermediate fact. Rewrite `this`, the goal using `[Submodule.mem_bot]`. Simplify using `[this]`. Introduce `c hcB`. Establish `h0 : ∀ i, (fun a => p i (c a)) = 0`.

Introduce `i`. Apply `k.indep` to reduce the goal to its premises. Use `cB i _ hcB using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `g`. Use extensionality with `r s : 1`.

Simplify using `only [Finset.sum_apply, Pi.smul_apply, Matrix.map_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, map_sum]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[mul_comm (c a), hp, mul_comm]`. Use function extensionality and compare the values at `a`. Rewrite using `[hb (c a)]`.

Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations. Rewrite using `[show p i (c a) = 0 from congrFun (h0 i) a, map_zero, zero_mul]`. Introduce `z hz choose s c hsc using fun i => k.gen _ (cS i z hz)`. Establish `hle : ∀ i, s i ≤ ∑ i, s i` using `fun i => Finset.single_le_sum (f := s) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)`. Use `set N := ∑ i, s i with hN`.

Set `d : Fin m → x'.A` to `fun i => ((u⁻¹ ^ N : (PowerSeries x'.K)ˣ) : x'.A) * b i * j (x.t ^ (N - s i))`. Establish `h3 : (u : x'.A) ^ N * ((u⁻¹ ^ N : (PowerSeries x'.K)ˣ) : x'.A) = 1`. Rewrite using `[← Units.val_pow_eq_pow_val, ← Units.val_mul, ← mul_pow, mul_inv_cancel, one_pow, Units.val_one]`. Establish `key : ∀ y : x'.A, ∑ i, d i * j (x.t ^ s i * p i y) = x'.t ^ (e * N) * y`. Introduce `y`.

Use `conv_rhs => rw [hb y, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Establish `h4 : j (x.t ^ (N - s i)) * j (x.t ^ s i) = (u : x'.A) ^ N * x'.t ^ (e * N)`. Rewrite using `[← map_mul, ← pow_add, Nat.sub_add_cancel (hle i), map_pow, hu, mul_pow, pow_mul]`. Simplify using `only [d, map_mul]`.

Take the linear combination `(((u⁻¹ ^ N : (PowerSeries x'.K)ˣ) : x'.A) * b i * j (p i y)) * h4 + (x'.t ^ (e * N) * b i * j (p i y)) * h3`. Use `⟨e * N, fun a => ∑ i, d i * j (c i a), ?_⟩` and prove the remaining obligations. Establish `hm : ∑ i, d i • (fun g => ((x.t ^ s i • (fun g => (z g).map (p i)) - ∑ a, c i a • k.κ a) g).map j) ∈ S`. Use `S.sum_mem fun i _ => S.smul_mem _ ?_` and prove the remaining obligations. Use `pB _ (hsc i)` as an intermediate fact.

Rewrite `this` using `[← hS]`. Conclude with `this`. Rewrite using `[← hS, SetLike.mem_coe]`. Use `hm using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `g`.

Use extensionality with `r t : 1`. Simplify using `only [Finset.sum_apply, Pi.smul_apply, Pi.sub_apply, Matrix.map_apply, Matrix.sum_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, map_sum, map_sub, mul_sub, Finset.sum_sub_distrib, key, Finset.sum_mul, Finset.mul_sum]`. Use `congr 1`. Rewrite using `[Finset.sum_comm]`. Simplify using `only [map_mul, mul_assoc]`.
-/
theorem UpperTheory.V.Pa.Det.kapPush :
    ∀ {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} (x x' : NP F n) (j : x.A →+* x'.A), x.Ext2 x' j → ∀ k : Kap x, ∃ (k' : Kap x') (e : k'.g = k.g), (∀ i g, k'.κ i g = (k.κ (Fin.cast e i) g).map j) ∧ ∀ i v, k'.Y i v = (k.Y (Fin.cast e i) v).map j := by
  intro l _ F n x x' j hE k
  obtain ⟨m, b, p, -, hb, hp, -, hc, e, u, -, hu⟩ := UpperTheory.V.Pa.Det.extFree j hE.1.1 hE.1.2.1 hE.1.2.2.1
  obtain ⟨pS, pB, pL⟩ := UpperTheory.V.Pa.Det.pushSel x x' j hE
  have cS := fun i => (UpperTheory.V.Pa.Det.compSel x x' j hE (p i) (hp i) (fun N => (hc N).imp fun _ h y hy => h y hy i)).1
  have cB := fun i => (UpperTheory.V.Pa.Det.compSel x x' j hE (p i) (hp i) (fun N => (hc N).imp fun _ h y hy => h y hy i)).2
  obtain ⟨S, hS⟩ := (UpperTheory.V.Pa.Det.selSub F x'.t (x'.ρX x'.A) (x'.wX x'.A) (x'.wiX x'.A) (Od x'.A x'.A n x'.a)).2
  have ha : x'.a = x.a := hE.1.2.2.2.2.1
  refine ⟨⟨k.g, fun i g => (k.κ i g).map j, fun i => pS _ (k.mem i), fun i v => (k.Y i v).map j, ?_,
    fun i v => pL _ _ _ (k.loc i v), ?_, ?_⟩, rfl, fun _ _ => rfl, fun _ _ => rfl⟩
  · intro i v r s
    refine ⟨fun h => ?_, fun _ => Submodule.mem_top⟩
    have := (k.Y_mem i v r s).1 (by rw [← ha]; exact h)
    rw [Submodule.mem_bot] at this ⊢
    simp [this]
  · intro c hcB
    have h0 : ∀ i, (fun a => p i (c a)) = 0 := by
      intro i
      apply k.indep
      convert cB i _ hcB using 1
      funext g
      ext r s : 1
      simp only [Finset.sum_apply, Pi.smul_apply, Matrix.map_apply, Matrix.sum_apply, Matrix.smul_apply,
        smul_eq_mul, map_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [mul_comm (c a), hp, mul_comm]
    funext a
    rw [hb (c a)]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [show p i (c a) = 0 from congrFun (h0 i) a, map_zero, zero_mul]
  · intro z hz
    choose s c hsc using fun i => k.gen _ (cS i z hz)
    have hle : ∀ i, s i ≤ ∑ i, s i := fun i =>
      Finset.single_le_sum (f := s) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    set N := ∑ i, s i with hN
    let d : Fin m → x'.A := fun i => ((u⁻¹ ^ N : (PowerSeries x'.K)ˣ) : x'.A) * b i * j (x.t ^ (N - s i))
    have h3 : (u : x'.A) ^ N * ((u⁻¹ ^ N : (PowerSeries x'.K)ˣ) : x'.A) = 1 := by
      rw [← Units.val_pow_eq_pow_val, ← Units.val_mul, ← mul_pow, mul_inv_cancel, one_pow, Units.val_one]
    have key : ∀ y : x'.A, ∑ i, d i * j (x.t ^ s i * p i y) = x'.t ^ (e * N) * y := by
      intro y
      conv_rhs => rw [hb y, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      have h4 : j (x.t ^ (N - s i)) * j (x.t ^ s i) = (u : x'.A) ^ N * x'.t ^ (e * N) := by
        rw [← map_mul, ← pow_add, Nat.sub_add_cancel (hle i), map_pow, hu, mul_pow, pow_mul]
      simp only [d, map_mul]
      linear_combination (((u⁻¹ ^ N : (PowerSeries x'.K)ˣ) : x'.A) * b i * j (p i y)) * h4
        + (x'.t ^ (e * N) * b i * j (p i y)) * h3
    refine ⟨e * N, fun a => ∑ i, d i * j (c i a), ?_⟩
    have hm : ∑ i, d i • (fun g => ((x.t ^ s i • (fun g => (z g).map (p i)) - ∑ a, c i a • k.κ a) g).map j) ∈ S := by
      refine S.sum_mem fun i _ => S.smul_mem _ ?_
      have := pB _ (hsc i)
      rw [← hS] at this
      exact this
    rw [← hS, SetLike.mem_coe]
    convert hm using 1
    funext g
    ext r t : 1
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.sub_apply, Matrix.map_apply, Matrix.sum_apply, Matrix.smul_apply,
      Matrix.sub_apply, smul_eq_mul, map_sum, map_sub, mul_sub, Finset.sum_sub_distrib, key, Finset.sum_mul,
      Finset.mul_sum]
    congr 1
    rw [Finset.sum_comm]
    simp only [map_mul, mul_assoc]
