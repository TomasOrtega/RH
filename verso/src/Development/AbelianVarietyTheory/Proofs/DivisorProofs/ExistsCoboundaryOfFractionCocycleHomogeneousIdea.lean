import Mathlib
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CubeComplexGradedModuleExactAtOfLargeDegree
open MvPolynomial DirectSum

namespace GlobalTheory

/- English proof (translation)
Take `⟨L₃, h₃⟩` from `hcoc i i i`. Establish `h₃' : x i ^ (3 * L₃ + N) * f i i = 0` using `by linear_combination h₃`. Break down `lt_trichotomy i j with h | rfl | h` into its components or cases. Conclude with `hlt i j h`. Conclude with `⟨3 * L₃ + N, by linear_combination (x i ^ (3 * L₃ + N + 2 * N')) * h₃'⟩`.

Take `⟨L₁, h₁⟩` from `hlt j i h`. Take `⟨L₂, h₂⟩` from `hcoc i j i`. Establish `hs : x i ^ (2 * L₂ + 3 * L₃ + 2 * N) * x j ^ L₂ * (f i j + f j i) = 0`. Take the linear combination `(x i ^ (3 * L₃ + N)) * h₂ + ((x i ^ 2 * x j) ^ L₂ * x j ^ N) * h₃'`. Use `⟨3 * L₂ + 3 * L₃ + 2 * N + L₁, ?_⟩` and prove the remaining obligations.

Take the linear combination `(x i ^ L₂ * x j ^ (2 * L₂ + 3 * L₃ + 2 * N) * (x i * x j) ^ L₁ * (x i * x j) ^ N') * hs - (x i * x j) ^ (3 * L₂ + 3 * L₃ + 2 * N) * h₁`.
-/
theorem cocycle_all_pairs_of_lt {Q : Type*} [CommRing Q] {ι : Type*} [LinearOrder ι]
    (x : ι → Q) (f : ι → ι → Q) (g : ι → Q) (N N' : ℕ)
    (hcoc : ∀ i j l, ∃ L : ℕ, (x i * x j * x l) ^ L * (x l ^ N * f i j + x i ^ N * f j l - x j ^ N * f i l) = 0)
    (hlt : ∀ i j, i < j → ∃ L : ℕ, (x i * x j) ^ L *
      ((x i * x j) ^ N' * f i j - (x i * x j) ^ N * (x j ^ N' * g i - x i ^ N' * g j)) = 0)
    (i j : ι) : ∃ L : ℕ, (x i * x j) ^ L *
      ((x i * x j) ^ N' * f i j - (x i * x j) ^ N * (x j ^ N' * g i - x i ^ N' * g j)) = 0 := by
  obtain ⟨L₃, h₃⟩ := hcoc i i i
  have h₃' : x i ^ (3 * L₃ + N) * f i i = 0 := by linear_combination h₃
  rcases lt_trichotomy i j with h | rfl | h
  · exact hlt i j h
  · exact ⟨3 * L₃ + N, by linear_combination (x i ^ (3 * L₃ + N + 2 * N')) * h₃'⟩
  · obtain ⟨L₁, h₁⟩ := hlt j i h
    obtain ⟨L₂, h₂⟩ := hcoc i j i
    have hs : x i ^ (2 * L₂ + 3 * L₃ + 2 * N) * x j ^ L₂ * (f i j + f j i) = 0 := by
      linear_combination (x i ^ (3 * L₃ + N)) * h₂ + ((x i ^ 2 * x j) ^ L₂ * x j ^ N) * h₃'
    refine ⟨3 * L₂ + 3 * L₃ + 2 * N + L₁, ?_⟩
    linear_combination (x i ^ L₂ * x j ^ (2 * L₂ + 3 * L₃ + 2 * N) * (x i * x j) ^ L₁ *
      (x i * x j) ^ N') * hs - (x i * x j) ^ (3 * L₂ + 3 * L₃ + 2 * N) * h₁

/- English proof (translation)
Take `⟨a, b, c, hab, hac, hbc, rfl⟩` from `Finset.card_eq_three.1 ht`. Apply the tactic sequence `rcases lt_or_gt_of_ne hab with h1 | h1 <;> rcases lt_or_gt_of_ne hac with h2 | h2 <;>`. Break down `lt_or_gt_of_ne hbc with h3 | h3` into its components or cases. Apply the tactic sequence `all_goals first`. Consider the case `exact ⟨a, b, c, by assumption, by assumption, rfl⟩`.

Consider the case `exact ⟨a, b, c, by assumption, by assumption, by ext; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto⟩`. Consider the case `exact ⟨a, c, b, by assumption, by assumption, by ext; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto⟩`. Consider the case `exact ⟨b, a, c, by assumption, by assumption, by ext; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto⟩`. Consider the case `exact ⟨b, c, a, by assumption, by assumption, by ext; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto⟩`. Consider the case `exact ⟨c, a, b, by assumption, by assumption, by ext; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto⟩`.

Consider the case `exact ⟨c, b, a, by assumption, by assumption, by ext; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto⟩`. Consider the case `(exfalso; order)`.
-/
theorem exists_triple_of_card_eq_three {ι : Type*} [LinearOrder ι] {t : Finset ι}
    (ht : t.card = 3) : ∃ i j l, i < j ∧ j < l ∧ t = {i, j, l} := by
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.1 ht
  rcases lt_or_gt_of_ne hab with h1 | h1 <;> rcases lt_or_gt_of_ne hac with h2 | h2 <;>
    rcases lt_or_gt_of_ne hbc with h3 | h3
  all_goals first
    | exact ⟨a, b, c, by assumption, by assumption, rfl⟩
    | exact ⟨a, b, c, by assumption, by assumption, by ext; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto⟩
    | exact ⟨a, c, b, by assumption, by assumption, by ext; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto⟩
    | exact ⟨b, a, c, by assumption, by assumption, by ext; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto⟩
    | exact ⟨b, c, a, by assumption, by assumption, by ext; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto⟩
    | exact ⟨c, a, b, by assumption, by assumption, by ext; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto⟩
    | exact ⟨c, b, a, by assumption, by assumption, by ext; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto⟩
    | (exfalso; order)

/- English proof (translation)
Establish `hil` using `hij.trans hjl`. Rewrite using `[Cube.d_apply_extend, Finset.sum_insert (by simp [hij.ne, hil.ne]), Finset.sum_pair hjl.ne, ← Cube.extend_apply_of_eq A x (Finset.card_pair hjl.ne), ← Cube.extend_apply_of_eq A x (Finset.card_pair hil.ne), ← Cube.extend_apply_of_eq A x (Finset.card_pair hij.ne)]`. Establish `e1 : ({i, j, l} : Finset ι).erase i = {j, l}`. Use extensionality with `k`. Simplify using `only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]`.

Prove the components needed by the constructor for the conclusion. Apply the tactic sequence `rintro ⟨hk, h | h | h⟩ <;> first | exact absurd h hk | simp [h]`. Apply the tactic sequence `rintro (rfl | rfl) <;> simp [hij.ne', hil.ne']`. Establish `e2 : ({i, j, l} : Finset ι).erase j = {i, l}`. Use extensionality with `k`.

Simplify using `only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]`. Prove the components needed by the constructor for the conclusion. Apply the tactic sequence `rintro ⟨hk, h | h | h⟩ <;> first | exact absurd h hk | simp [h]`. Apply the tactic sequence `rintro (rfl | rfl) <;> simp [hij.ne, hjl.ne']`. Establish `e3 : ({i, j, l} : Finset ι).erase l = {i, j}`.

Use extensionality with `k`. Simplify using `only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]`. Prove the components needed by the constructor for the conclusion. Apply the tactic sequence `rintro ⟨hk, h | h | h⟩ <;> first | exact absurd h hk | simp [h]`. Apply the tactic sequence `rintro (rfl | rfl) <;> simp [hil.ne, hjl.ne]`.

Establish `s1 : cubeSign ({i, j, l} : Finset ι) i = 1` using `cubeSign_eq_one_of_forall_le (by simp [hij.le, hil.le])`. Establish `s2 : cubeSign ({i, j, l} : Finset ι) j = -1`. Use `cubeSign_erase_of_lt (t := {i, j, l}) (by simp) hij` as an intermediate fact. Rewrite `this` using `[e1, cubeSign_eq_one_of_forall_le (by simp [hjl.le])]`. Use linear arithmetic over natural numbers and integers.

Establish `s3 : cubeSign ({i, j, l} : Finset ι) l = 1`. Establish `a1` using `cubeSign_erase_of_lt (t := {i, j, l}) (by simp) hil`. Rewrite `a1` using `[e1]`. Establish `a2` using `cubeSign_erase_of_lt (t := {j, l}) (by simp) hjl`. Rewrite `a2` using `[Finset.erase_insert (by simp [hjl.ne]), cubeSign_singleton]`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[Cube.res_congr A _ e1 _ (by intro k; simp; tauto), Cube.res_congr A _ e2 _ (by intro k; simp; tauto), Cube.res_congr A _ e3 _ (by intro k; simp; tauto), s1, s2, s3]`. Simplify using `only [one_smul, neg_smul]`. Normalize the expressions using the abelian group laws.
-/
theorem Cube.d_two_apply_triple {ι : Type} [LinearOrder ι] {R : Type*} [Ring R]
    (A : Cube ι R) (x : Cube.Term A 2) {i j l : ι} (hij : i < j) (hjl : j < l) :
    Cube.d A 2 x ⟨{i, j, l}, by rw [Finset.card_eq_three]; exact ⟨i, j, l, hij.ne, (hij.trans hjl).ne, hjl.ne, rfl⟩⟩ =
      Cube.res A (by intro k; simp; tauto) (x ⟨{j, l}, Finset.card_pair hjl.ne⟩) -
        Cube.res A (by intro k; simp; tauto) (x ⟨{i, l}, Finset.card_pair (hij.trans hjl).ne⟩) +
        Cube.res A (by intro k; simp; tauto) (x ⟨{i, j}, Finset.card_pair hij.ne⟩) := by
  have hil := hij.trans hjl
  rw [Cube.d_apply_extend, Finset.sum_insert (by simp [hij.ne, hil.ne]), Finset.sum_pair hjl.ne,
    ← Cube.extend_apply_of_eq A x (Finset.card_pair hjl.ne),
    ← Cube.extend_apply_of_eq A x (Finset.card_pair hil.ne),
    ← Cube.extend_apply_of_eq A x (Finset.card_pair hij.ne)]
  have e1 : ({i, j, l} : Finset ι).erase i = {j, l} := by
    ext k; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hk, h | h | h⟩ <;> first | exact absurd h hk | simp [h]
    · rintro (rfl | rfl) <;> simp [hij.ne', hil.ne']
  have e2 : ({i, j, l} : Finset ι).erase j = {i, l} := by
    ext k; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hk, h | h | h⟩ <;> first | exact absurd h hk | simp [h]
    · rintro (rfl | rfl) <;> simp [hij.ne, hjl.ne']
  have e3 : ({i, j, l} : Finset ι).erase l = {i, j} := by
    ext k; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hk, h | h | h⟩ <;> first | exact absurd h hk | simp [h]
    · rintro (rfl | rfl) <;> simp [hil.ne, hjl.ne]
  have s1 : cubeSign ({i, j, l} : Finset ι) i = 1 :=
    cubeSign_eq_one_of_forall_le (by simp [hij.le, hil.le])
  have s2 : cubeSign ({i, j, l} : Finset ι) j = -1 := by
    have := cubeSign_erase_of_lt (t := {i, j, l}) (by simp) hij
    rw [e1, cubeSign_eq_one_of_forall_le (by simp [hjl.le])] at this
    omega
  have s3 : cubeSign ({i, j, l} : Finset ι) l = 1 := by
    have a1 := cubeSign_erase_of_lt (t := {i, j, l}) (by simp) hil
    rw [e1] at a1
    have a2 := cubeSign_erase_of_lt (t := {j, l}) (by simp) hjl
    rw [Finset.erase_insert (by simp [hjl.ne]), cubeSign_singleton] at a2
    omega
  rw [Cube.res_congr A _ e1 _ (by intro k; simp; tauto), Cube.res_congr A _ e2 _ (by intro k; simp; tauto),
    Cube.res_congr A _ e3 _ (by intro k; simp; tauto), s1, s2, s3]
  simp only [one_smul, neg_smul]
  abel

section GrCubeVal
variable {ι : Type} {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M]
  [Module (MvPolynomial ι R) M] [IsScalarTower R (MvPolynomial ι R) M]
  {ℳ : ℤ → Submodule R M} [PolyGradedSMul ι ℳ] {n : ℤ}

abbrev grCubeVal {s : Finset ι} (z : (grCube ι ℳ n).obj s) :
    LocalizedModule.Away (xProd R s) M :=
  Subtype.val (p := fun w => w ∈ homLoc ℳ s n) z

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem grCubeVal_add {s : Finset ι} (a b : (grCube ι ℳ n).obj s) :
    grCubeVal (a + b) = grCubeVal a + grCubeVal b := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem grCubeVal_sub {s : Finset ι} (a b : (grCube ι ℳ n).obj s) :
    grCubeVal (a - b) = grCubeVal a - grCubeVal b := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem grCubeVal_zero {s : Finset ι} : grCubeVal (0 : (grCube ι ℳ n).obj s) = 0 := rfl

/- English proof (translation)
Introduce `_ _ h` and use `Subtype.ext h`.
-/
theorem grCubeVal_injective {s : Finset ι} :
    Function.Injective (grCubeVal : (grCube ι ℳ n).obj s → _) := fun _ _ h => Subtype.ext h

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem grCubeVal_res {s t : Finset ι} (h : s ⊆ t) (z : (grCube ι ℳ n).obj s) :
    grCubeVal (Cube.res (grCube ι ℳ n) h z) = locRes X M h (grCubeVal z) := rfl

end GrCubeVal

/- English proof (translation)
Establish `hne : ∀ s : {s : Finset ι // s.card = 2}, s.1.Nonempty` using `fun s => Finset.card_pos.1 (by rw [s.2]; norm_num)`. Set `x : Cube.Term (grCube ι (grQuot (polyGrading ι A) J) (d : ℤ)) 2` to `fun s => ⟨awayFrac _ (xProd A s.1) N (Submodule.Quotient.mk (p := J) (F (s.1.min' (hne s)) (s.1.max' (hne s)))), awayFrac_mem_homLoc ⟨_, mem_polyGrading_natCast.2 (hF _ _), rfl⟩ (by rw [s.2]; push_cast; ring)⟩`. Establish `hmin : ∀ i j, i < j → ∀ hn : ({i, j} : Finset ι).Nonempty, ({i, j} : Finset ι).min' hn = i` using `fun i j h hn => le_antisymm (Finset.min'_le _ _ (by simp)) (Finset.le_min' _ _ _ (by simp [h.le]))`. Establish `hmax : ∀ i j, i < j → ∀ hn : ({i, j} : Finset ι).Nonempty, ({i, j} : Finset ι).max' hn = j` using `fun i j h hn => le_antisymm (Finset.max'_le _ _ _ (by simp [h.le])) (Finset.le_max' _ _ (by simp))`. Establish `hx : ∀ i j (h : i < j), grCubeVal (x ⟨{i, j}, Finset.card_pair h.ne⟩) = awayFrac _ (xProd A {i, j}) N (Submodule.Quotient.mk (p` using `J) (F i j)) := by`.

Introduce `i j h`. Use `show awayFrac _ _ N _ = _`. Rewrite using `[hmin i j h, hmax i j h]`. Establish `hdx : Cube.d _ 2 x = 0`. Use function extensionality and compare the values at `⟨t, ht⟩`.

Take `⟨i, j, l, hij, hjl, rfl⟩` from `exists_triple_of_card_eq_three ht`. Rewrite using `[Cube.d_two_apply_triple _ x hij hjl]`. Establish `hil` using `hij.trans hjl`. Apply `grCubeVal_injective` to reduce the goal to its premises. Rewrite using `[grCubeVal_add, grCubeVal_sub, grCubeVal_res, grCubeVal_res, grCubeVal_res, hx j l hjl, hx i l hil, hx i j hij, Pi.zero_apply, grCubeVal_zero]`.

Establish `hP : (∏ k ∈ ({i, j, l} : Finset ι), (X k : MvPolynomial ι A)) = X i * X j * X l`. Rewrite using `[Finset.prod_insert (by simp [hij.ne, hil.ne]), Finset.prod_pair hjl.ne, mul_assoc]`. Rewrite using `[locRes_awayFrac X _ (c := X i) (by rw [hP, Finset.prod_pair hjl.ne]; ring), locRes_awayFrac X _ (c := X j) (by rw [hP, Finset.prod_pair hil.ne]; ring), locRes_awayFrac X _ (c := X l) (by rw [hP, Finset.prod_pair hij.ne]; ring), ← map_sub, ← map_add, awayFrac_eq_zero_iff]`. Take `⟨L, hL⟩` from `hcoc i j l`. Use `⟨L, ?_⟩` and prove the remaining obligations.

Establish `hL'` using `Ideal.Quotient.eq_zero_iff_mem.2 hL`. Rewrite using `[hP]`. Simplify using `only [map_mul, map_pow, map_add, map_sub] at hL'`. Simplify using `only [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.mk_eq_mk, map_mul, map_pow]`. Take the linear combination `hL'`.

Take `⟨y, hy⟩` from `(hex x).1 hdx`. Establish `hk` using `fun i : ι => exists_awayFrac_of_mem_homLoc (grQuot (polyGrading ι A) J) (Subtype.property (p := fun w => w ∈ homLoc (grQuot (polyGrading ι A) J) {i} (d : ℤ)) (y ⟨{i}, Finset.card_singleton i⟩))`. Use `choose k₀ hk₀ using hk`. Use `set N' := Finset.univ.sup k₀ with hN'`. Use `choose m hm hmeq using fun i => hk₀ i N' (Finset.le_sup (Finset.mem_univ i))`.

Establish `hmeq' : ∀ i, grCubeVal (y ⟨{i}, Finset.card_singleton i⟩) = awayFrac _ (xProd A {i}) N' (m i)` using `fun i => (hmeq i).symm`. Use `choose g hg hgm using fun i => mem_grQuot.1 (hm i)`. Use `⟨N', fun i => -g i, fun i => ?_, fun i j h => ?_⟩` and prove the remaining obligations. Use `mem_polyGrading_natCast.1 ?_` and prove the remaining obligations. Use `neg_mem (hg i)` as an intermediate fact.

Simplify using `only [Finset.card_singleton] at this`. Use `this using 2` and compare the differences between its conclusion and the goal. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `e` using `congrArg grCubeVal (congrFun hy ⟨{i, j}, Finset.card_pair h.ne⟩)`.

Rewrite `e` using `[Cube.d_one_apply_pair _ _ h, grCubeVal_sub, grCubeVal_res, grCubeVal_res, hx i j h, hmeq' i, hmeq' j, ← hgm i, ← hgm j, locRes_awayFrac X _ (c := X i) (by rw [Finset.prod_pair h.ne, Finset.prod_singleton]), locRes_awayFrac X _ (c := X j) (by rw [Finset.prod_pair h.ne, Finset.pro …`. Take `⟨l, hl⟩` from `e`. Rewrite `hl` using `[Finset.prod_pair h.ne]`. Simplify using `only [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.mk_eq_mk, map_mul, map_pow, mul_sub] at hl`. Use `⟨l, Ideal.Quotient.eq_zero_iff_mem.1 ?_⟩` and prove the remaining obligations.

Simplify using `only [map_mul, map_pow, map_sub, map_neg]`. Take the linear combination `(exp := 1) -hl`.
-/
theorem exists_coboundary_lt {ι : Type} [LinearOrder ι] [Fintype ι] {A : Type} [CommRing A]
    (J : Ideal (MvPolynomial ι A)) (d : ℕ)
    (hex : Function.Exact (Cube.d (grCube ι (grQuot (polyGrading ι A) J) (d : ℤ)) 1)
      (Cube.d (grCube ι (grQuot (polyGrading ι A) J) (d : ℤ)) 2))
    (N : ℕ) (F : ι → ι → MvPolynomial ι A) (hF : ∀ i j, (F i j).IsHomogeneous (d + 2 * N))
    (hcoc : ∀ i j l, ∃ L : ℕ, ((X i : MvPolynomial ι A) * X j * X l) ^ L *
      (X l ^ N * F i j + X i ^ N * F j l - X j ^ N * F i l) ∈ J) :
    ∃ (N' : ℕ) (G : ι → MvPolynomial ι A), (∀ i, (G i).IsHomogeneous (d + N')) ∧
      ∀ i j, i < j → ∃ L : ℕ, ((X i : MvPolynomial ι A) * X j) ^ L *
        ((X i * X j) ^ N' * F i j - (X i * X j) ^ N * (X j ^ N' * G i - X i ^ N' * G j)) ∈ J := by
  classical
  have hne : ∀ s : {s : Finset ι // s.card = 2}, s.1.Nonempty := fun s =>
    Finset.card_pos.1 (by rw [s.2]; norm_num)
  let x : Cube.Term (grCube ι (grQuot (polyGrading ι A) J) (d : ℤ)) 2 := fun s =>
    ⟨awayFrac _ (xProd A s.1) N
        (Submodule.Quotient.mk (p := J) (F (s.1.min' (hne s)) (s.1.max' (hne s)))),
      awayFrac_mem_homLoc ⟨_, mem_polyGrading_natCast.2 (hF _ _), rfl⟩
        (by rw [s.2]; push_cast; ring)⟩
  have hmin : ∀ i j, i < j → ∀ hn : ({i, j} : Finset ι).Nonempty, ({i, j} : Finset ι).min' hn = i :=
    fun i j h hn => le_antisymm (Finset.min'_le _ _ (by simp)) (Finset.le_min' _ _ _ (by simp [h.le]))
  have hmax : ∀ i j, i < j → ∀ hn : ({i, j} : Finset ι).Nonempty, ({i, j} : Finset ι).max' hn = j :=
    fun i j h hn => le_antisymm (Finset.max'_le _ _ _ (by simp [h.le])) (Finset.le_max' _ _ (by simp))
  have hx : ∀ i j (h : i < j), grCubeVal (x ⟨{i, j}, Finset.card_pair h.ne⟩) =
      awayFrac _ (xProd A {i, j}) N (Submodule.Quotient.mk (p := J) (F i j)) := by
    intro i j h
    show awayFrac _ _ N _ = _
    rw [hmin i j h, hmax i j h]
  have hdx : Cube.d _ 2 x = 0 := by
    funext ⟨t, ht⟩
    obtain ⟨i, j, l, hij, hjl, rfl⟩ := exists_triple_of_card_eq_three ht
    rw [Cube.d_two_apply_triple _ x hij hjl]
    have hil := hij.trans hjl
    apply grCubeVal_injective
    rw [grCubeVal_add, grCubeVal_sub, grCubeVal_res, grCubeVal_res, grCubeVal_res, hx j l hjl,
      hx i l hil, hx i j hij, Pi.zero_apply, grCubeVal_zero]
    have hP : (∏ k ∈ ({i, j, l} : Finset ι), (X k : MvPolynomial ι A)) = X i * X j * X l := by
      rw [Finset.prod_insert (by simp [hij.ne, hil.ne]), Finset.prod_pair hjl.ne, mul_assoc]
    rw [locRes_awayFrac X _ (c := X i) (by rw [hP, Finset.prod_pair hjl.ne]; ring),
      locRes_awayFrac X _ (c := X j) (by rw [hP, Finset.prod_pair hil.ne]; ring),
      locRes_awayFrac X _ (c := X l) (by rw [hP, Finset.prod_pair hij.ne]; ring),
      ← map_sub, ← map_add, awayFrac_eq_zero_iff]
    obtain ⟨L, hL⟩ := hcoc i j l
    refine ⟨L, ?_⟩
    have hL' := Ideal.Quotient.eq_zero_iff_mem.2 hL
    rw [hP]
    simp only [map_mul, map_pow, map_add, map_sub] at hL'
    simp only [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.mk_eq_mk, map_mul,
      map_pow]
    linear_combination hL'
  obtain ⟨y, hy⟩ := (hex x).1 hdx
  have hk := fun i : ι => exists_awayFrac_of_mem_homLoc (grQuot (polyGrading ι A) J)
    (Subtype.property (p := fun w => w ∈ homLoc (grQuot (polyGrading ι A) J) {i} (d : ℤ))
      (y ⟨{i}, Finset.card_singleton i⟩))
  choose k₀ hk₀ using hk
  set N' := Finset.univ.sup k₀ with hN'
  choose m hm hmeq using fun i => hk₀ i N' (Finset.le_sup (Finset.mem_univ i))
  have hmeq' : ∀ i, grCubeVal (y ⟨{i}, Finset.card_singleton i⟩) =
      awayFrac _ (xProd A {i}) N' (m i) := fun i => (hmeq i).symm
  choose g hg hgm using fun i => mem_grQuot.1 (hm i)
  refine ⟨N', fun i => -g i, fun i => ?_, fun i j h => ?_⟩
  · refine mem_polyGrading_natCast.1 ?_
    have := neg_mem (hg i)
    simp only [Finset.card_singleton] at this
    convert this using 2
    push_cast
    ring
  · have e := congrArg grCubeVal (congrFun hy ⟨{i, j}, Finset.card_pair h.ne⟩)
    rw [Cube.d_one_apply_pair _ _ h, grCubeVal_sub, grCubeVal_res, grCubeVal_res, hx i j h,
      hmeq' i, hmeq' j, ← hgm i, ← hgm j,
      locRes_awayFrac X _ (c := X i) (by rw [Finset.prod_pair h.ne, Finset.prod_singleton]),
      locRes_awayFrac X _ (c := X j) (by rw [Finset.prod_pair h.ne, Finset.prod_singleton]; ring),
      ← map_sub, awayFrac_eq_iff] at e
    obtain ⟨l, hl⟩ := e
    rw [Finset.prod_pair h.ne] at hl
    simp only [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.mk_eq_mk, map_mul,
      map_pow, mul_sub] at hl
    refine ⟨l, Ideal.Quotient.eq_zero_iff_mem.1 ?_⟩
    simp only [map_mul, map_pow, map_sub, map_neg]
    linear_combination (exp := 1) -hl

/- English proof (translation)
Introduce `A _ _ n J hJ`. Establish `hJh : (J : Submodule (MvPolynomial (Fin (n + 1)) A) (MvPolynomial (Fin (n + 1)) A)).IsHomogeneous (polyGrading (Fin (n + 1)) A)`. Establish `e : J = Submodule.span (MvPolynomial (Fin (n + 1)) A) {g | ∃ F ∈ J, ∃ k : ℕ, g = homogeneousComponent k F}`. Apply `le_antisymm` to reduce the goal to its premises. Introduce `F hF`.

Rewrite using `[← sum_homogeneousComponent F]`. Conclude with `Submodule.sum_mem _ fun k _ => Submodule.subset_span ⟨F, hF, k, rfl⟩`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨F, hF, k, rfl⟩`. Conclude with `hJ F hF k`.

Rewrite using `[e]`. Conclude with `isHomogeneous_span_gr _ (by`. Introduce and unpack `_ ⟨F, _, k, rfl⟩`. Conclude with `⟨k, mem_polyGrading_natCast.2 (homogeneousComponent_isHomogeneous k F)⟩)`. Use `letI := grQuotDecomposition (polyGrading (Fin (n + 1)) A) hJh`.

Take `⟨n₀, h₀⟩` from `cubeComplex_grCube_exactAt_of_finite (Fin (n + 1)) A (MvPolynomial (Fin (n + 1)) A ⧸ J) (grQuot (polyGrading (Fin (n + 1)) A) J) inferInstance`. Use `⟨n₀.toNat, fun d hd N F hF hcoc => ?_⟩` and prove the remaining obligations. Establish `hex` using `(cubeComplex_exactAt_succ_iff _ 1).1 (h₀ d (by omega) 2)`. Take `⟨N', G, hG, hlt⟩` from `exists_coboundary_lt J d hex N F hF hcoc`. Use `⟨N', G, hG, fun i j => ?_⟩` and prove the remaining obligations.

Take `⟨L, hL⟩` from `cocycle_all_pairs_of_lt (fun i => Ideal.Quotient.mk J (X i)) (fun i j => Ideal.Quotient.mk J (F i j)) (fun i => Ideal.Quotient.mk J (G i)) N N' (fun i j l => (hcoc i j l).imp fun L hL => by`. Simplify `Ideal.Quotient.eq_zero_iff_mem.2 hL)` using `only [map_mul, map_pow, map_sub, map_add]`. Use the proof step `(fun i j h => (hlt i j h).imp fun L hL => by`. Simplify `Ideal.Quotient.eq_zero_iff_mem.2 hL)` using `only [map_mul, map_pow, map_sub, map_add]`. Use `i j`.

Conclude with `⟨L, Ideal.Quotient.eq_zero_iff_mem.1 (by simpa only [map_mul, map_pow, map_sub] using hL)⟩`.
-/
theorem exists_coboundary_of_cocycle_homogeneous : ∀ (A : Type) [CommRing A] [IsNoetherianRing A] (n : ℕ) (J : Ideal (MvPolynomial (Fin (n + 1)) A)), (∀ F ∈ J, ∀ d, homogeneousComponent d F ∈ J) → ∃ d₀ : ℕ, ∀ d, d₀ ≤ d → ∀ (N : ℕ) (F : Fin (n + 1) → Fin (n + 1) → MvPolynomial (Fin (n + 1)) A), (∀ i j, (F i j).IsHomogeneous (d + 2 * N)) → (∀ i j l, ∃ L : ℕ, ((X i : MvPolynomial (Fin (n + 1)) A) * X j * X l) ^ L * (X l ^ N * F i j + X i ^ N * F j l - X j ^ N * F i l) ∈ J) → ∃ (N' : ℕ) (G : Fin (n + 1) → MvPolynomial (Fin (n + 1)) A), (∀ i, (G i).IsHomogeneous (d + N')) ∧ ∀ i j, ∃ L : ℕ, ((X i : MvPolynomial (Fin (n + 1)) A) * X j) ^ L * ((X i * X j) ^ N' * F i j - (X i * X j) ^ N * (X j ^ N' * G i - X i ^ N' * G j)) ∈ J := by
  intro A _ _ n J hJ
  classical
  have hJh : (J : Submodule (MvPolynomial (Fin (n + 1)) A) (MvPolynomial (Fin (n + 1)) A)).IsHomogeneous
      (polyGrading (Fin (n + 1)) A) := by
    have e : J = Submodule.span (MvPolynomial (Fin (n + 1)) A)
        {g | ∃ F ∈ J, ∃ k : ℕ, g = homogeneousComponent k F} := by
      apply le_antisymm
      · intro F hF
        rw [← sum_homogeneousComponent F]
        exact Submodule.sum_mem _ fun k _ => Submodule.subset_span ⟨F, hF, k, rfl⟩
      · rw [Submodule.span_le]
        rintro _ ⟨F, hF, k, rfl⟩
        exact hJ F hF k
    rw [e]
    exact isHomogeneous_span_gr _ (by
      rintro _ ⟨F, _, k, rfl⟩
      exact ⟨k, mem_polyGrading_natCast.2 (homogeneousComponent_isHomogeneous k F)⟩)
  letI := grQuotDecomposition (polyGrading (Fin (n + 1)) A) hJh
  obtain ⟨n₀, h₀⟩ := cubeComplex_grCube_exactAt_of_finite (Fin (n + 1)) A
    (MvPolynomial (Fin (n + 1)) A ⧸ J) (grQuot (polyGrading (Fin (n + 1)) A) J) inferInstance
  refine ⟨n₀.toNat, fun d hd N F hF hcoc => ?_⟩
  have hex := (cubeComplex_exactAt_succ_iff _ 1).1 (h₀ d (by omega) 2)
  obtain ⟨N', G, hG, hlt⟩ := exists_coboundary_lt J d hex N F hF hcoc
  refine ⟨N', G, hG, fun i j => ?_⟩
  obtain ⟨L, hL⟩ := cocycle_all_pairs_of_lt (fun i => Ideal.Quotient.mk J (X i))
    (fun i j => Ideal.Quotient.mk J (F i j)) (fun i => Ideal.Quotient.mk J (G i)) N N'
    (fun i j l => (hcoc i j l).imp fun L hL => by
      simpa only [map_mul, map_pow, map_sub, map_add] using Ideal.Quotient.eq_zero_iff_mem.2 hL)
    (fun i j h => (hlt i j h).imp fun L hL => by
      simpa only [map_mul, map_pow, map_sub, map_add] using Ideal.Quotient.eq_zero_iff_mem.2 hL)
    i j
  exact ⟨L, Ideal.Quotient.eq_zero_iff_mem.1 (by simpa only [map_mul, map_pow, map_sub] using hL)⟩

end GlobalTheory
