import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointMemSp4

open IsLocalRing UpperTheory.V UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

namespace UpperTheory.V.Ws.X1

variable {A R : Type} [CommRing A] [CommRing R]

private def lowOf (a b c d : A) : M4 A := !![1, 0, 0, 0; a, 1, 0, 0; b, c, 1, 0; d, b - a * c, -a, 1]

/- English proof (translation)
Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Unfold `IsGSp`. Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;>`. Apply the tactic sequence `simp [adj, lowOf, Matrix.mul_apply, Fin.sum_univ_four, sgn, Fin.rev, Matrix.one_apply] <;> ring`.

Apply the tactic sequence `intro i fin_cases i <;> simp [lowOf]`. Apply the tactic sequence `intro i j hij fin_cases i <;> fin_cases j <;> simp_all [lowOf] <;> omega`.
-/
private theorem lowOf_low (a b c d : A) : IsLow (lowOf a b c d) := by
  refine ⟨?_, ?_, ?_⟩
  · unfold IsGSp
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [adj, lowOf, Matrix.mul_apply, Fin.sum_univ_four, sgn, Fin.rev, Matrix.one_apply] <;> ring
  · intro i
    fin_cases i <;> simp [lowOf]
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [lowOf] <;> omega

/- English proof (translation)
Take `⟨hg, hd, hu⟩` from `h`. Establish `h01` using `hu 0 1 (by decide); have h02 := hu 0 2 (by decide); have h03 := hu 0 3 (by decide)`. Establish `h12` using `hu 1 2 (by decide); have h13 := hu 1 3 (by decide); have h23 := hu 2 3 (by decide)`. Establish `d0` using `hd 0`. Establish `d1` using `hd 1`.

Establish `d2` using `hd 2`. Establish `d3` using `hd 3`. Establish `e1` using `congrFun (congrFun hg 1) 0`. Establish `e4` using `congrFun (congrFun hg 3) 1`. Simplify using `[adj, Matrix.mul_apply, Fin.sum_univ_four, sgn, Fin.rev, Matrix.one_apply, h01, h02, h03, h12, h13, h23, d0, d1, d2, d3] at e1 e4`.

Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [lowOf, h01, h02, h03, h12, h13, h23, d0, d1, d2, d3]`. Take the linear combination `e4`. Take the linear combination `e1`.
-/
private theorem eq_lowOf {n : M4 A} (h : IsLow n) : n = lowOf (n 1 0) (n 2 0) (n 2 1) (n 3 0) := by
  obtain ⟨hg, hd, hu⟩ := h
  have h01 := hu 0 1 (by decide); have h02 := hu 0 2 (by decide); have h03 := hu 0 3 (by decide)
  have h12 := hu 1 2 (by decide); have h13 := hu 1 3 (by decide); have h23 := hu 2 3 (by decide)
  have d0 := hd 0; have d1 := hd 1; have d2 := hd 2; have d3 := hd 3
  have e1 := congrFun (congrFun hg 1) 0
  have e4 := congrFun (congrFun hg 3) 1
  simp [adj, Matrix.mul_apply, Fin.sum_univ_four, sgn, Fin.rev, Matrix.one_apply, h01, h02, h03, h12, h13,
    h23, d0, d1, d2, d3] at e1 e4
  ext i j
  fin_cases i <;> fin_cases j <;> simp [lowOf, h01, h02, h03, h12, h13, h23, d0, d1, d2, d3]
  · linear_combination e4
  · linear_combination e1

/- English proof (translation)
Use `⟨by simpa using (grp A).2.2.2.2.2.2.2.1 1 1 m n hm.1 hn.1, ?_, ?_⟩` and prove the remaining obligations. Introduce `i`. Rewrite using `[eq_lowOf hm, eq_lowOf hn]`. Apply the tactic sequence `fin_cases i <;> simp [lowOf, Matrix.mul_apply, Fin.sum_univ_four]`. Introduce `i j hij`.

Rewrite using `[eq_lowOf hm, eq_lowOf hn]`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp_all [lowOf, Matrix.mul_apply, Fin.sum_univ_four] <;> omega`.
-/
private theorem low_mul {m n : M4 A} (hm : IsLow m) (hn : IsLow n) : IsLow (m * n) := by
  refine ⟨by simpa using (grp A).2.2.2.2.2.2.2.1 1 1 m n hm.1 hn.1, ?_, ?_⟩
  · intro i
    rw [eq_lowOf hm, eq_lowOf hn]
    fin_cases i <;> simp [lowOf, Matrix.mul_apply, Fin.sum_univ_four]
  · intro i j hij
    rw [eq_lowOf hm, eq_lowOf hn]
    fin_cases i <;> fin_cases j <;> simp_all [lowOf, Matrix.mul_apply, Fin.sum_univ_four] <;> omega

/- English proof (translation)
Introduce `i j hij`. Rewrite using `[adj_apply, h j.rev i.rev (by simpa [Fin.lt_def, Fin.val_rev] using (by omega : (3 : ℕ) - i.val < 3 - j.val)), smul_zero]`.
-/
private theorem up_adj {b : M4 A} (h : IsUp b) : IsUp (adj b) := by
  intro i j hij
  rw [adj_apply, h j.rev i.rev (by simpa [Fin.lt_def, Fin.val_rev] using (by omega : (3 : ℕ) - i.val < 3 - j.val)), smul_zero]

/- English proof (translation)
Take `⟨-, -, hadd, hsmul, hone, hmap, -, hgsp, -⟩` from `grp A`. Establish `kz : ∀ X Z : M4 A, X.map p = 0 → Z.map p = 0 → X * Z = 0`. Introduce `X Z hX hZ`. Use extensionality with `i j`. Simplify using `only [Matrix.mul_apply, Matrix.zero_apply]`.

Conclude with `Finset.sum_eq_zero fun k _ => hp _ _ (by simpa using congrFun (congrFun hX i) k) (by simpa using congrFun (congrFun hZ k) j)`. Establish `adj0 : adj (0 : M4 A) = 0` using `by simpa using hsmul 0 (0 : M4 A)`. Establish `adjneg : ∀ X : M4 A, adj (-X) = -adj X`. Introduce `X`. Simplify using `using hsmul (-1) X`.

Establish `madj : ∀ X : M4 A, X.map p = 0 → (adj X).map p = 0`. Introduce `X hX`. Rewrite using `[← hmap R p X, hX]`. Simplify using `using (grp R).2.2.2.1 (0 : R) (0 : M4 R)`. Use `set m0 := lowOf (n' 1 0) (n' 2 0) (n' 2 1) (n' 3 0) with hm0d`.

Establish `hm0 : IsLow m0` using `lowOf_low _ _ _ _`. Establish `hm0l : adj m0 * m0 = 1` using `by simpa [IsGSp] using hm0.1`. Establish `hm0r : m0 * adj m0 = 1` using `mul_eq_one_comm.mp hm0l`. Establish `hmap0 : m0.map p = n'.map p`. Rewrite using `[eq_lowOf hl]`.

Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [hm0d, lowOf]`. Establish `hN : adj (n'.map p) * n'.map p = 1` using `by simpa [IsGSp] using hl.1`. Use `set Y := adj m0 * n' - 1 with hYd`. Establish `hY : Y.map p = 0` using `by show p.mapMatrix Y = 0`.

Rewrite using `[hYd, map_sub, map_mul, map_one, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, ← hmap R p m0, hmap0, hN, sub_self]`. Establish `h1Y : adj m0 * n' = 1 + Y` using `by rw [hYd]; abel`. Establish `ha : IsGSp 1 (adj m0)` using `by show adj (adj m0) * adj m0 = (1 : A) • 1`. Rewrite using `[(grp A).2.1, hm0r, one_smul]`. Establish `hadjY : adj Y + Y = 0`.

Establish `g : IsGSp 1 (adj m0 * n')` using `by simpa using hgsp 1 1 _ _ ha hn`. Establish `g' : adj (1 + Y) * (1 + Y) = 1` using `by simpa [IsGSp, h1Y] using g`. Rewrite `g'` using `[hadd, hone]`. Establish `e : (1 + adj Y) * (1 + Y) = 1 + (adj Y + Y) + adj Y * Y` using `by noncomm_ring`. Rewrite `g'` using `[e, kz _ _ (madj Y hY) hY, add_zero]`.

Simplify using `using g'`. Use `set Yu : M4 A := Matrix.of fun i j => if i ≤ j then Y i j else 0 with hYud`. Establish `hYu : Yu.map p = 0`. Use extensionality with `i j`. Use `congrFun (congrFun hY i) j` as an intermediate fact.

Simplify using `only [Matrix.map_apply, Matrix.zero_apply] at this`. Simplify using `only [hYud, Matrix.map_apply, Matrix.of_apply, Matrix.zero_apply]`. Apply the tactic sequence `split_ifs <;> simp [this]`. Establish `hadjYu : adj Yu + Yu = 0`. Use extensionality with `i j`.

Establish `h` using `congrFun (congrFun hadjY i) j`. Simplify using `only [Matrix.add_apply, adj_apply, Matrix.zero_apply] at h`. Simplify using `only [Matrix.add_apply, adj_apply, Matrix.zero_apply, hYud, Matrix.of_apply, Fin.rev_le_rev]`. Apply the tactic sequence `split_ifs <;> simp_all`. Use `set b : M4 A := 1 - Yu with hbd`.

Establish `hbup : IsUp b`. Introduce `i j hij`. Simplify using `[hbd, hYud, Matrix.one_apply, hij.ne', not_le.mpr hij]`. Establish `hbg : IsGSp 1 b` using `by show adj b * b = (1 : A) • 1`. Establish `ea : adj b = 1 - adj Yu`.

Rewrite using `[hbd, sub_eq_add_neg, hadd, adjneg, hone, ← sub_eq_add_neg]`. Rewrite using `[ea, one_smul]`. Establish `e : (1 - adj Yu) * (1 - Yu) = 1 - (adj Yu + Yu) + adj Yu * Yu` using `by noncomm_ring`. Rewrite using `[e, hadjYu, kz _ _ (madj Yu hYu) hYu]`. Simplify using the standard rewrite rules.

Establish `hbmap : p.mapMatrix b = 1`. Rewrite using `[hbd, map_sub, map_one, RingHom.mapMatrix_apply, hYu, sub_zero]`. Establish `e1 : adj m0 * n' * b = 1 + (Y - Yu)`. Rewrite using `[h1Y, hbd]`. Establish `e : (1 + Y) * (1 - Yu) = 1 + (Y - Yu) - Y * Yu` using `by noncomm_ring`.

Rewrite using `[e, kz _ _ hY hYu, sub_zero]`. Establish `hlow : IsLow (adj m0 * n' * b)`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Simplify `hgsp 1 1 _ _ ha hn) hbg` using `using hgsp _ _ _ _ (by simpa`. Introduce `i`.

Rewrite using `[e1]`. Simplify using `[hYud]`. Introduce `i j hij`. Rewrite using `[e1]`. Simplify using `[hYud, Matrix.one_apply, hij.ne, hij.le]`.

Establish `hm` using `low_mul hm0 hlow`. Establish `hmeq : m0 * (adj m0 * n' * b) = n' * b`. Rewrite using `[← mul_assoc, ← mul_assoc, hm0r, one_mul]`. Use `⟨m0 * (adj m0 * n' * b), b, hm, hbg, hbup, up_adj hbup, ?_, hmeq⟩` and prove the remaining obligations. Rewrite using `[hmeq]`.

Use `show p.mapMatrix (n' * b) = p.mapMatrix n'`. Rewrite using `[map_mul, hbmap, mul_one]`.
-/
private theorem aux (p : A →+* R) (hp : ∀ x y, p x = 0 → p y = 0 → x * y = 0) (n' : M4 A) (hn : IsGSp 1 n')
    (hl : IsLow (n'.map p)) :
    ∃ m b : M4 A, IsLow m ∧ IsGSp 1 b ∧ IsUp b ∧ IsUp (adj b) ∧ m.map p = n'.map p ∧ m = n' * b := by
  obtain ⟨-, -, hadd, hsmul, hone, hmap, -, hgsp, -⟩ := grp A
  have kz : ∀ X Z : M4 A, X.map p = 0 → Z.map p = 0 → X * Z = 0 := by
    intro X Z hX hZ
    ext i j
    simp only [Matrix.mul_apply, Matrix.zero_apply]
    exact Finset.sum_eq_zero fun k _ =>
      hp _ _ (by simpa using congrFun (congrFun hX i) k) (by simpa using congrFun (congrFun hZ k) j)
  have adj0 : adj (0 : M4 A) = 0 := by simpa using hsmul 0 (0 : M4 A)
  have adjneg : ∀ X : M4 A, adj (-X) = -adj X := by
    intro X
    simpa using hsmul (-1) X
  have madj : ∀ X : M4 A, X.map p = 0 → (adj X).map p = 0 := by
    intro X hX
    rw [← hmap R p X, hX]
    simpa using (grp R).2.2.2.1 (0 : R) (0 : M4 R)
  set m0 := lowOf (n' 1 0) (n' 2 0) (n' 2 1) (n' 3 0) with hm0d
  have hm0 : IsLow m0 := lowOf_low _ _ _ _
  have hm0l : adj m0 * m0 = 1 := by simpa [IsGSp] using hm0.1
  have hm0r : m0 * adj m0 = 1 := mul_eq_one_comm.mp hm0l
  have hmap0 : m0.map p = n'.map p := by
    rw [eq_lowOf hl]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hm0d, lowOf]
  have hN : adj (n'.map p) * n'.map p = 1 := by simpa [IsGSp] using hl.1
  set Y := adj m0 * n' - 1 with hYd
  have hY : Y.map p = 0 := by
    show p.mapMatrix Y = 0
    rw [hYd, map_sub, map_mul, map_one, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, ← hmap R p m0,
      hmap0, hN, sub_self]
  have h1Y : adj m0 * n' = 1 + Y := by rw [hYd]; abel
  have ha : IsGSp 1 (adj m0) := by
    show adj (adj m0) * adj m0 = (1 : A) • 1
    rw [(grp A).2.1, hm0r, one_smul]
  have hadjY : adj Y + Y = 0 := by
    have g : IsGSp 1 (adj m0 * n') := by simpa using hgsp 1 1 _ _ ha hn
    have g' : adj (1 + Y) * (1 + Y) = 1 := by simpa [IsGSp, h1Y] using g
    rw [hadd, hone] at g'
    have e : (1 + adj Y) * (1 + Y) = 1 + (adj Y + Y) + adj Y * Y := by noncomm_ring
    rw [e, kz _ _ (madj Y hY) hY, add_zero] at g'
    simpa using g'
  set Yu : M4 A := Matrix.of fun i j => if i ≤ j then Y i j else 0 with hYud
  have hYu : Yu.map p = 0 := by
    ext i j
    have := congrFun (congrFun hY i) j
    simp only [Matrix.map_apply, Matrix.zero_apply] at this
    simp only [hYud, Matrix.map_apply, Matrix.of_apply, Matrix.zero_apply]
    split_ifs <;> simp [this]
  have hadjYu : adj Yu + Yu = 0 := by
    ext i j
    have h := congrFun (congrFun hadjY i) j
    simp only [Matrix.add_apply, adj_apply, Matrix.zero_apply] at h
    simp only [Matrix.add_apply, adj_apply, Matrix.zero_apply, hYud, Matrix.of_apply, Fin.rev_le_rev]
    split_ifs <;> simp_all
  set b : M4 A := 1 - Yu with hbd
  have hbup : IsUp b := by
    intro i j hij
    simp [hbd, hYud, Matrix.one_apply, hij.ne', not_le.mpr hij]
  have hbg : IsGSp 1 b := by
    show adj b * b = (1 : A) • 1
    have ea : adj b = 1 - adj Yu := by
      rw [hbd, sub_eq_add_neg, hadd, adjneg, hone, ← sub_eq_add_neg]
    rw [ea, one_smul]
    have e : (1 - adj Yu) * (1 - Yu) = 1 - (adj Yu + Yu) + adj Yu * Yu := by noncomm_ring
    rw [e, hadjYu, kz _ _ (madj Yu hYu) hYu]
    simp
  have hbmap : p.mapMatrix b = 1 := by
    rw [hbd, map_sub, map_one, RingHom.mapMatrix_apply, hYu, sub_zero]
  have e1 : adj m0 * n' * b = 1 + (Y - Yu) := by
    rw [h1Y, hbd]
    have e : (1 + Y) * (1 - Yu) = 1 + (Y - Yu) - Y * Yu := by noncomm_ring
    rw [e, kz _ _ hY hYu, sub_zero]
  have hlow : IsLow (adj m0 * n' * b) := by
    refine ⟨?_, ?_, ?_⟩
    · simpa using hgsp _ _ _ _ (by simpa using hgsp 1 1 _ _ ha hn) hbg
    · intro i
      rw [e1]
      simp [hYud]
    · intro i j hij
      rw [e1]
      simp [hYud, Matrix.one_apply, hij.ne, hij.le]
  have hm := low_mul hm0 hlow
  have hmeq : m0 * (adj m0 * n' * b) = n' * b := by
    rw [← mul_assoc, ← mul_assoc, hm0r, one_mul]
  refine ⟨m0 * (adj m0 * n' * b), b, hm, hbg, hbup, up_adj hbup, ?_, hmeq⟩
  rw [hmeq]
  show p.mapMatrix (n' * b) = p.mapMatrix n'
  rw [map_mul, hbmap, mul_one]

end UpperTheory.V.Ws.X1

/- English proof (translation)
Introduce `Λ _ _ _ _ A R _ _ _ _ _ _ p _ hker n' hn hl`. Establish `hle : RingHom.ker p ≤ maximalIdeal A`. Apply `IsLocalRing.le_maximalIdeal` to reduce the goal to its premises. Introduce `htop`. Establish `h1 : (1 : A) ∈ RingHom.ker p` using `by rw [htop]; trivial`.

Rewrite `h1` using `[RingHom.mem_ker, map_one]`. Conclude with `one_ne_zero h1`. Use `aux (p : A →+* R) (fun x y hx hy => ?_) n' hn hl` and prove the remaining obligations. Establish `hm : x * y ∈ maximalIdeal A * RingHom.ker p` using `Ideal.mul_mem_mul (hle (by simpa [RingHom.mem_ker] using hx)) (by simpa [RingHom.mem_ker] using hy)`. Rewrite `hm` using `[hker]`.

Simplify using `using hm`.
-/
theorem UpperTheory.V.Ws.X1.lowLift :
    ∀ {Λ : Type} [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ] {A R : Type} [CommRing A] [Algebra Λ A] [IsCO Λ A] [CommRing R] [Algebra Λ R] [IsCO Λ R] (p : A →ₐ[Λ] R), Function.Surjective p → maximalIdeal A * RingHom.ker p = ⊥ → ∀ n' : M4 A, IsGSp 1 n' → IsLow (n'.map p) → ∃ m b : M4 A, IsLow m ∧ IsGSp 1 b ∧ IsUp b ∧ IsUp (adj b) ∧ m.map p = n'.map p ∧ m = n' * b := by
  intro Λ _ _ _ _ A R _ _ _ _ _ _ p _ hker n' hn hl
  have hle : RingHom.ker p ≤ maximalIdeal A := by
    apply IsLocalRing.le_maximalIdeal
    intro htop
    have h1 : (1 : A) ∈ RingHom.ker p := by rw [htop]; trivial
    rw [RingHom.mem_ker, map_one] at h1
    exact one_ne_zero h1
  refine aux (p : A →+* R) (fun x y hx hy => ?_) n' hn hl
  have hm : x * y ∈ maximalIdeal A * RingHom.ker p :=
    Ideal.mul_mem_mul (hle (by simpa [RingHom.mem_ker] using hx)) (by simpa [RingHom.mem_ker] using hy)
  rw [hker] at hm
  simpa using hm
