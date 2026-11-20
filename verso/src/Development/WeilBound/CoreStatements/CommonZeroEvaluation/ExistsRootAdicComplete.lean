import Mathlib

open Polynomial

namespace ModelDimension.Alg

/- English proof (translation)
Set `c : ℕ → V` to `fun n => Nat.rec 0 (fun _ b => -e - b ^ 2 * q.eval b) n`. Establish `hc : ∀ n, c (n + 1) = -e - c n ^ 2 * q.eval (c n)` using `fun n => rfl`. Establish `hI : ∀ n, c n ∈ I`. Introduce `n`. Proceed by induction on `n with`.

Consider the case `zero => exact I.zero_mem`. Consider the case `succ n ih`. Rewrite using `[hc]`. Conclude with `I.sub_mem (I.neg_mem he) (I.mul_mem_right _ (I.pow_mem_of_mem ih 2 (by norm_num)))`. Establish `key : ∀ (y z : V) (n : ℕ), y ∈ I → z ∈ I → y - z ∈ I ^ n → y ^ 2 * q.eval y - z ^ 2 * q.eval z ∈ I ^ (n + 1)`.

Introduce `y z n hy hz h`. Take `⟨k, hk⟩` from `Polynomial.sub_dvd_eval_sub y z q`. Establish `: y ^ 2 * q.eval y - z ^ 2 * q.eval z = (y - z) * ((y + z) * q.eval y + z * (z * k))`. Take the linear combination `z ^ 2 * hk`. Rewrite using `[this, pow_succ]`.

Conclude with `Ideal.mul_mem_mul h (I.add_mem (I.mul_mem_right _ (I.add_mem hy hz)) (I.mul_mem_right _ hz))`. Establish `hstep : ∀ n, c (n + 1) - c n ∈ I ^ n`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => simp`.

Consider the case `succ n ih`. Use `key _ _ n (hI (n + 1)) (hI n) ih` as an intermediate fact. Establish `e2 : c (n + 1 + 1) - c (n + 1) = -(c (n + 1) ^ 2 * q.eval (c (n + 1)) - c n ^ 2 * q.eval (c n))`. Rewrite using `[hc (n + 1)]`. Take the linear combination `-(hc n)`.

Rewrite using `[e2]`. Conclude with `(I ^ (n + 1)).neg_mem this`. Establish `aux : ∀ m n, m ≤ n → c m ≡ c n [SMOD (I ^ m • ⊤ : Ideal V)]`. Introduce `m n hmn`. Rewrite using `[← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one, SModEq.sub_mem]`.

Proceed by induction on `n, hmn using Nat.le_induction with`. Consider the case `base => simp`. Consider the case `succ n hmn ih`. Establish `: c m - c (n + 1) = (c m - c n) - (c (n + 1) - c n)` using `by ring`. Rewrite using `[this]`.

Conclude with `(I ^ m).sub_mem ih (Ideal.pow_le_pow_right hmn (hstep n))`. Take `⟨a, ha⟩` from `IsPrecomplete.prec' c (aux _ _)`. Establish `ha' : ∀ n, c n - a ∈ I ^ n` using `fun n => by`. Use `ha n` as an intermediate fact. Rewrite `this` using `[← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one, SModEq.sub_mem]`. Then use the resulting hypothesis.

Establish `haI : a ∈ I`. Establish `h1` using `ha' 1`. Rewrite `h1` using `[pow_one]`. Establish `: a = c 1 - (c 1 - a)` using `by ring`. Rewrite using `[this]`.

Conclude with `I.sub_mem (hI 1) h1`. Use `⟨a, haI, IsHausdorff.haus' (I := I) _ fun n => ?_⟩` and prove the remaining obligations. Rewrite using `[← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one, SModEq.zero]`. Establish `h1` using `key _ _ n (hI n) haI (ha' n)`. Establish `h2` using `ha' (n + 1)`.

Establish `: e + a + a ^ 2 * q.eval a = -(c (n + 1) - a) - (c n ^ 2 * q.eval (c n) - a ^ 2 * q.eval a)`. Rewrite using `[hc]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Conclude with `Ideal.pow_le_pow_right (Nat.le_succ n) ((I ^ (n + 1)).sub_mem ((I ^ (n + 1)).neg_mem h2) h1)`.
-/
theorem exists_root_adic_complete {V : Type} [CommRing V] (I : Ideal V) [IsAdicComplete I V] (e : V) (he : e ∈ I)
    (q : V[X]) : ∃ y ∈ I, e + y + y ^ 2 * q.eval y = 0 := by
  let c : ℕ → V := fun n => Nat.rec 0 (fun _ b => -e - b ^ 2 * q.eval b) n
  have hc : ∀ n, c (n + 1) = -e - c n ^ 2 * q.eval (c n) := fun n => rfl
  have hI : ∀ n, c n ∈ I := by
    intro n
    induction n with
    | zero => exact I.zero_mem
    | succ n ih =>
      rw [hc]
      exact I.sub_mem (I.neg_mem he) (I.mul_mem_right _ (I.pow_mem_of_mem ih 2 (by norm_num)))
  have key : ∀ (y z : V) (n : ℕ), y ∈ I → z ∈ I → y - z ∈ I ^ n →
      y ^ 2 * q.eval y - z ^ 2 * q.eval z ∈ I ^ (n + 1) := by
    intro y z n hy hz h
    obtain ⟨k, hk⟩ := Polynomial.sub_dvd_eval_sub y z q
    have : y ^ 2 * q.eval y - z ^ 2 * q.eval z = (y - z) * ((y + z) * q.eval y + z * (z * k)) := by
      linear_combination z ^ 2 * hk
    rw [this, pow_succ]
    exact Ideal.mul_mem_mul h (I.add_mem (I.mul_mem_right _ (I.add_mem hy hz)) (I.mul_mem_right _ hz))
  have hstep : ∀ n, c (n + 1) - c n ∈ I ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have := key _ _ n (hI (n + 1)) (hI n) ih
      have e2 : c (n + 1 + 1) - c (n + 1) =
          -(c (n + 1) ^ 2 * q.eval (c (n + 1)) - c n ^ 2 * q.eval (c n)) := by
        rw [hc (n + 1)]
        linear_combination -(hc n)
      rw [e2]
      exact (I ^ (n + 1)).neg_mem this
  have aux : ∀ m n, m ≤ n → c m ≡ c n [SMOD (I ^ m • ⊤ : Ideal V)] := by
    intro m n hmn
    rw [← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one, SModEq.sub_mem]
    induction n, hmn using Nat.le_induction with
    | base => simp
    | succ n hmn ih =>
      have : c m - c (n + 1) = (c m - c n) - (c (n + 1) - c n) := by ring
      rw [this]
      exact (I ^ m).sub_mem ih (Ideal.pow_le_pow_right hmn (hstep n))
  obtain ⟨a, ha⟩ := IsPrecomplete.prec' c (aux _ _)
  have ha' : ∀ n, c n - a ∈ I ^ n := fun n => by
    have := ha n
    rwa [← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one, SModEq.sub_mem] at this
  have haI : a ∈ I := by
    have h1 := ha' 1
    rw [pow_one] at h1
    have : a = c 1 - (c 1 - a) := by ring
    rw [this]
    exact I.sub_mem (hI 1) h1
  refine ⟨a, haI, IsHausdorff.haus' (I := I) _ fun n => ?_⟩
  rw [← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one, SModEq.zero]
  have h1 := key _ _ n (hI n) haI (ha' n)
  have h2 := ha' (n + 1)
  have : e + a + a ^ 2 * q.eval a = -(c (n + 1) - a) - (c n ^ 2 * q.eval (c n) - a ^ 2 * q.eval a) := by
    rw [hc]; ring
  rw [this]
  exact Ideal.pow_le_pow_right (Nat.le_succ n) ((I ^ (n + 1)).sub_mem ((I ^ (n + 1)).neg_mem h2) h1)

/- English proof (translation)
Use `set d := f.derivative.eval α with hd`. Take `⟨k, hk⟩` from `(f.map (C : V →+* V[X])).binomExpansion (C α) (C d * X)`. Take `⟨y, hy, hq⟩` from `exists_root_adic_complete _ e he k`. Establish `h1` using `congrArg (Polynomial.evalRingHom y) hk`. Establish `hev : ∀ (p : V[X]) (z : V[X]), (evalRingHom y) ((p.map (C : V →+* V[X])).eval z) = p.eval (z.eval y)`.

Introduce `p z`. Rewrite using `[eval_map, hom_eval₂]`. Establish `: (evalRingHom y).comp (C : V →+* V[X]) = RingHom.id V` using `by ext; simp`. Rewrite using `[this]`. Both sides reduce to the same expression.

Rewrite `h1` using `[derivative_map]`. Simplify using `only [map_add, map_mul, map_pow, hev] at h1`. Simplify using `only [coe_evalRingHom, eval_C, eval_X, eval_add, eval_mul, ← hd] at h1`. Use `⟨α + d * y, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[h1, h]`.

Take the linear combination `d ^ 2 * hq`. Establish `hu : IsUnit (1 + y * k.eval y)`. Use `IsLocalRing.isUnit_one_sub_self_of_mem_nonunits (-(y * k.eval y)) ((IsLocalRing.mem_maximalIdeal _).1 (Submodule.neg_mem _ (Ideal.mul_mem_right _ _ hy)))` as an intermediate fact. Simplify using `using this`. Establish `: e ∣ y * (1 + y * k.eval y)` using `⟨-1, by linear_combination hq⟩`.

Rewrite using `[add_sub_cancel_left]`. Conclude with `Dvd.dvd.mul_left ((hu.dvd_mul_right).1 this) d`.
-/
theorem exists_root {V : Type} [CommRing V] [IsLocalRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V]
    (f : V[X]) (α e : V) (he : e ∈ IsLocalRing.maximalIdeal V)
    (h : f.eval α = (f.derivative.eval α) ^ 2 * e) : ∃ β, f.eval β = 0 ∧ e ∣ β - α := by
  set d := f.derivative.eval α with hd
  obtain ⟨k, hk⟩ := (f.map (C : V →+* V[X])).binomExpansion (C α) (C d * X)
  obtain ⟨y, hy, hq⟩ := exists_root_adic_complete _ e he k
  have h1 := congrArg (Polynomial.evalRingHom y) hk
  have hev : ∀ (p : V[X]) (z : V[X]), (evalRingHom y) ((p.map (C : V →+* V[X])).eval z) = p.eval (z.eval y) := by
    intro p z
    rw [eval_map, hom_eval₂]
    have : (evalRingHom y).comp (C : V →+* V[X]) = RingHom.id V := by ext; simp
    rw [this]
    rfl
  rw [derivative_map] at h1
  simp only [map_add, map_mul, map_pow, hev] at h1
  simp only [coe_evalRingHom, eval_C, eval_X, eval_add, eval_mul, ← hd] at h1
  refine ⟨α + d * y, ?_, ?_⟩
  · rw [h1, h]
    linear_combination d ^ 2 * hq
  · have hu : IsUnit (1 + y * k.eval y) := by
      have := IsLocalRing.isUnit_one_sub_self_of_mem_nonunits (-(y * k.eval y))
        ((IsLocalRing.mem_maximalIdeal _).1 (Submodule.neg_mem _ (Ideal.mul_mem_right _ _ hy)))
      simpa using this
    have : e ∣ y * (1 + y * k.eval y) := ⟨-1, by linear_combination hq⟩
    rw [add_sub_cancel_left]
    exact Dvd.dvd.mul_left ((hu.dvd_mul_right).1 this) d

/- English proof (translation)
Set `s : Set V` to `Set.range (Function.surjInv (Ideal.Quotient.mk_surjective (I := Ideal.span {(N : V)})))`. Establish `hs : s.Finite` using `Set.finite_range _`. Establish `hsp : ∀ (k : ℕ) (x : V), ∃ y ∈ Submodule.span ℤ s, (N : V) ^ k ∣ x - y`. Introduce `k`. Proceed by induction on `k with`.

Consider the case `zero => exact fun x => ⟨0, Submodule.zero_mem _, by simp⟩`. Consider the case `succ k ih`. Introduce `x`. Take `⟨y, hy, z, hz⟩` from `ih x`. Set `w` to `Function.surjInv (Ideal.Quotient.mk_surjective (I := Ideal.span {(N : V)})) (Ideal.Quotient.mk _ z)`.

Establish `hw : Ideal.Quotient.mk (Ideal.span {(N : V)}) w = Ideal.Quotient.mk _ z` using `Function.surjInv_eq _ _`. Take `⟨u, hu⟩` from `Ideal.mem_span_singleton.1 (Ideal.Quotient.eq.1 hw.symm)`. Use `⟨y + ((N : ℤ) ^ k) • w, Submodule.add_mem _ hy (Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)), u, ?_⟩` and prove the remaining obligations. Rewrite using `[zsmul_eq_mul]`. Use `push_cast`.

Take the linear combination `hz + (N : V) ^ k * hu`. Use `⟨s.ncard, fun α k => ?_⟩` and prove the remaining obligations. Set `J : Ideal V` to `Ideal.span {(N : V) ^ k}`. Establish `htop : Submodule.span ℤ (Ideal.Quotient.mk J '' s) = ⊤`. Rewrite using `[eq_top_iff]`.

Introduce `x _`. Take `⟨x, rfl⟩` from `Ideal.Quotient.mk_surjective x`. Take `⟨y, hy, hd⟩` from `hsp k x`. Establish `: Ideal.Quotient.mk J x = Ideal.Quotient.mk J y` using `Ideal.Quotient.eq.2 (Ideal.mem_span_singleton.2 hd)`. Rewrite using `[this]`.

Use `Submodule.mem_map_of_mem (f := (Ideal.Quotient.mkₐ ℤ J).toLinearMap) hy` as an intermediate fact. Rewrite `this` using `[Submodule.map_span]`. Then use the resulting hypothesis. Use `haveI : Module.Finite ℤ (V ⧸ J) := ⟨htop ▸ Submodule.fg_span (hs.image _)⟩`. Take `⟨p, hp, hdeg, h0⟩` from `LinearMap.exists_monic_and_natDegree_eq_and_aeval_eq_zero ℤ (Algebra.lmul ℤ (V ⧸ J) (Ideal.Quotient.mk J α))`. Establish `hle : p.natDegree ≤ s.ncard`.

Rewrite using `[hdeg, ← htop]`. Conclude with `(Submodule.spanFinrank_span_le_ncard_of_finite (hs.image _)).trans (Set.ncard_image_le hs)`. Establish `h1 : aeval (Ideal.Quotient.mk J α) p = 0`. Rewrite `h0` using `[aeval_algHom_apply]`. Conclude with `Algebra.lmul_injective (h0.trans (map_zero _).symm)`.

Establish `h2 : (N : V) ^ k ∣ aeval α p`. Rewrite using `[← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `(aeval_algHom_apply (Ideal.Quotient.mkₐ ℤ J) α p).symm.trans h1`. Use `⟨p * X ^ (s.ncard - p.natDegree), hp.mul (monic_X_pow _), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hp.natDegree_mul (monic_X_pow _), natDegree_X_pow]`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[map_mul]`. Conclude with `h2.mul_right _`.
-/
theorem exists_monic {V : Type} [CommRing V] (N : ℕ) [Finite (V ⧸ Ideal.span {(N : V)})] :
    ∃ m : ℕ, ∀ (α : V) (k : ℕ), ∃ P : ℤ[X], P.Monic ∧ P.natDegree = m ∧ (N : V) ^ k ∣ aeval α P := by
  classical
  let s : Set V := Set.range (Function.surjInv (Ideal.Quotient.mk_surjective (I := Ideal.span {(N : V)})))
  have hs : s.Finite := Set.finite_range _
  have hsp : ∀ (k : ℕ) (x : V), ∃ y ∈ Submodule.span ℤ s, (N : V) ^ k ∣ x - y := by
    intro k
    induction k with
    | zero => exact fun x => ⟨0, Submodule.zero_mem _, by simp⟩
    | succ k ih =>
      intro x
      obtain ⟨y, hy, z, hz⟩ := ih x
      let w := Function.surjInv (Ideal.Quotient.mk_surjective (I := Ideal.span {(N : V)})) (Ideal.Quotient.mk _ z)
      have hw : Ideal.Quotient.mk (Ideal.span {(N : V)}) w = Ideal.Quotient.mk _ z := Function.surjInv_eq _ _
      obtain ⟨u, hu⟩ := Ideal.mem_span_singleton.1 (Ideal.Quotient.eq.1 hw.symm)
      refine ⟨y + ((N : ℤ) ^ k) • w, Submodule.add_mem _ hy
        (Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)), u, ?_⟩
      rw [zsmul_eq_mul]
      push_cast
      linear_combination hz + (N : V) ^ k * hu
  refine ⟨s.ncard, fun α k => ?_⟩
  let J : Ideal V := Ideal.span {(N : V) ^ k}
  have htop : Submodule.span ℤ (Ideal.Quotient.mk J '' s) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨y, hy, hd⟩ := hsp k x
    have : Ideal.Quotient.mk J x = Ideal.Quotient.mk J y := Ideal.Quotient.eq.2 (Ideal.mem_span_singleton.2 hd)
    rw [this]
    have := Submodule.mem_map_of_mem (f := (Ideal.Quotient.mkₐ ℤ J).toLinearMap) hy
    rwa [Submodule.map_span] at this
  haveI : Module.Finite ℤ (V ⧸ J) := ⟨htop ▸ Submodule.fg_span (hs.image _)⟩
  obtain ⟨p, hp, hdeg, h0⟩ := LinearMap.exists_monic_and_natDegree_eq_and_aeval_eq_zero ℤ
    (Algebra.lmul ℤ (V ⧸ J) (Ideal.Quotient.mk J α))
  have hle : p.natDegree ≤ s.ncard := by
    rw [hdeg, ← htop]
    exact (Submodule.spanFinrank_span_le_ncard_of_finite (hs.image _)).trans (Set.ncard_image_le hs)
  have h1 : aeval (Ideal.Quotient.mk J α) p = 0 := by
    rw [aeval_algHom_apply] at h0
    exact Algebra.lmul_injective (h0.trans (map_zero _).symm)
  have h2 : (N : V) ^ k ∣ aeval α p := by
    rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem]
    exact (aeval_algHom_apply (Ideal.Quotient.mkₐ ℤ J) α p).symm.trans h1
  refine ⟨p * X ^ (s.ncard - p.natDegree), hp.mul (monic_X_pow _), ?_, ?_⟩
  · rw [hp.natDegree_mul (monic_X_pow _), natDegree_X_pow]; omega
  · rw [map_mul]; exact h2.mul_right _

end ModelDimension.Alg
