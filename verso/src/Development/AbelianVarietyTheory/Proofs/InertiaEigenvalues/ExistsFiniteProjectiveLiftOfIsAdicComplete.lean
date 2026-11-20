import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdIPowLe
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral

open GlobalTheory.Prism

namespace GlobalTheory.BSP.LiftProj

variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]

/- English proof (translation)
Rewrite using `[Matrix.mul_apply]`. Conclude with `Ideal.sum_mem _ fun k _ => Ideal.mul_mem_mul (hx i k) (hy k j)`.
-/
theorem mul_mem {I J : Ideal A} {x y : Matrix n n A} (hx : ∀ i j, x i j ∈ I) (hy : ∀ i j, y i j ∈ J)
    (i j : n) : (x * y) i j ∈ I * J := by
  rw [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_mul (hx i k) (hy k j)

/- English proof (translation)
Rewrite using `[Matrix.mul_apply]`. Conclude with `Ideal.sum_mem _ fun k _ => Ideal.mul_mem_right _ _ (hx i k)`.
-/
theorem mul_mem_right {I : Ideal A} {x : Matrix n n A} (y : Matrix n n A) (hx : ∀ i j, x i j ∈ I)
    (i j : n) : (x * y) i j ∈ I := by
  rw [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_right _ _ (hx i k)

/- English proof (translation)
Rewrite using `[Matrix.mul_apply]`. Conclude with `Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ (hy k j)`.
-/
theorem mul_mem_left {I : Ideal A} {y : Matrix n n A} (x : Matrix n n A) (hy : ∀ i j, y i j ∈ I)
    (i j : n) : (x * y) i j ∈ I := by
  rw [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ (hy k j)

/- English proof (translation)
Set `f : ℕ → Matrix n n A` to `fun k => Nat.rec x (fun _ y => 3 * (y * y) - 2 * (y * y * y)) k`. Establish `f0 : f 0 = x` using `rfl`. Establish `fs : ∀ k, f (k + 1) = 3 * (f k * f k) - 2 * (f k * f k * f k)` using `fun k => rfl`. Establish `h1 : ∀ k i j, (f k * f k - f k) i j ∈ 𝔞 ^ (k + 1)`. Introduce `k`.

Proceed by induction on `k with`. Consider the case `zero => simpa [f0] using hx`. Consider the case `succ k ih`. Establish `e : f (k + 1) * f (k + 1) - f (k + 1) = ((f k * f k - f k) * (f k * f k - f k)) * (4 * (f k * f k) - 4 * f k - 3)`. Rewrite using `[fs]`.

Use `noncomm_ring`. Introduce `i j`. Rewrite using `[e]`. Use `mul_mem_right _ (fun i j => ?_) i j` and prove the remaining obligations. Use `mul_mem ih ih i j` as an intermediate fact.

Rewrite `this` using `[← pow_add]`. Conclude with `Ideal.pow_le_pow_right (by omega) this`. Establish `h2 : ∀ k i j, (f (k + 1) - f k) i j ∈ 𝔞 ^ (k + 1)`. Introduce `k i j`. Establish `e : f (k + 1) - f k = (f k * f k - f k) * (1 - 2 * f k)`.

Rewrite using `[fs]`. Use `noncomm_ring`. Rewrite using `[e]`. Conclude with `mul_mem_right _ (h1 k) i j`. Establish `h3 : ∀ k m, k ≤ m → ∀ i j, (f m - f k) i j ∈ 𝔞 ^ (k + 1)`.

Introduce `k m hkm`. Proceed by induction on `m, hkm using Nat.le_induction with`. Consider the case `base => intro i j`. Simplify using the standard rewrite rules. Consider the case `succ m hkm ih`.

Introduce `i j`. Establish `e : f (m + 1) - f k = (f (m + 1) - f m) + (f m - f k)` using `by abel`. Rewrite using `[e, Matrix.add_apply]`. Conclude with `add_mem (Ideal.pow_le_pow_right (by omega) (h2 m i j)) (ih i j)`. Establish `h4 : ∀ i j, ∃ L : A, ∀ k, f k i j - L ∈ 𝔞 ^ k`.

Introduce `i j`. Take `⟨L, hL⟩` from `IsPrecomplete.prec' (I := 𝔞) (fun k => f k i j) (fun {k m} hkm => by`. Rewrite using `[SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, ← neg_mem_iff, neg_sub]`. Conclude with `Ideal.pow_le_pow_right (Nat.le_succ k) (h3 k m hkm i j))`. Use `⟨L, fun k => ?_⟩` and prove the remaining obligations.

Use `hL k` as an intermediate fact. Rewrite `this` using `[SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]`. Then use the resulting hypothesis. Use `choose L hL using h4`. Set `e : Matrix n n A` to `Matrix.of L`. Establish `hL' : ∀ k i j, (f k - e) i j ∈ 𝔞 ^ k` using `fun k i j => hL i j k`.

Use `⟨e, ?_, fun i j => ?_⟩` and prove the remaining obligations. Rewrite using `[← sub_eq_zero]`. Use extensionality with `i j`. Use `IsHausdorff.haus' (I := 𝔞) _ fun k => ?_` and prove the remaining obligations. Rewrite using `[SModEq.zero, smul_eq_mul, Ideal.mul_top]`.

Establish `e1 : e * e - e = (f k * f k - f k) - ((f k - e) * (f k - 1) + e * (f k - e))` using `by noncomm_ring`. Rewrite using `[e1, Matrix.sub_apply, Matrix.add_apply]`. Conclude with `sub_mem (Ideal.pow_le_pow_right (Nat.le_succ k) (h1 k i j)) (add_mem (mul_mem_right _ (hL' k) i j) (mul_mem_left _ (hL' k) i j))`. Establish `e1 : e - x = (f 1 - f 0) - (f 1 - e)` using `by rw [f0]; abel`. Rewrite using `[e1, Matrix.sub_apply]`.

Establish `a` using `h2 0 i j`. Establish `b` using `hL' 1 i j`. Rewrite `a` using `[zero_add, pow_one]`. Rewrite `b` using `[pow_one]`. Conclude with `sub_mem a b`.
-/
theorem exists_idem (𝔞 : Ideal A) [IsAdicComplete 𝔞 A] (x : Matrix n n A)
    (hx : ∀ i j, (x * x - x) i j ∈ 𝔞) :
    ∃ e : Matrix n n A, e * e = e ∧ ∀ i j, (e - x) i j ∈ 𝔞 := by
  let f : ℕ → Matrix n n A := fun k => Nat.rec x (fun _ y => 3 * (y * y) - 2 * (y * y * y)) k
  have f0 : f 0 = x := rfl
  have fs : ∀ k, f (k + 1) = 3 * (f k * f k) - 2 * (f k * f k * f k) := fun k => rfl
  have h1 : ∀ k i j, (f k * f k - f k) i j ∈ 𝔞 ^ (k + 1) := by
    intro k
    induction k with
    | zero => simpa [f0] using hx
    | succ k ih =>
      have e : f (k + 1) * f (k + 1) - f (k + 1) =
          ((f k * f k - f k) * (f k * f k - f k)) * (4 * (f k * f k) - 4 * f k - 3) := by
        rw [fs]; noncomm_ring
      intro i j
      rw [e]
      refine mul_mem_right _ (fun i j => ?_) i j
      have := mul_mem ih ih i j
      rw [← pow_add] at this
      exact Ideal.pow_le_pow_right (by omega) this
  have h2 : ∀ k i j, (f (k + 1) - f k) i j ∈ 𝔞 ^ (k + 1) := by
    intro k i j
    have e : f (k + 1) - f k = (f k * f k - f k) * (1 - 2 * f k) := by
      rw [fs]; noncomm_ring
    rw [e]
    exact mul_mem_right _ (h1 k) i j
  have h3 : ∀ k m, k ≤ m → ∀ i j, (f m - f k) i j ∈ 𝔞 ^ (k + 1) := by
    intro k m hkm
    induction m, hkm using Nat.le_induction with
    | base => intro i j; simp
    | succ m hkm ih =>
      intro i j
      have e : f (m + 1) - f k = (f (m + 1) - f m) + (f m - f k) := by abel
      rw [e, Matrix.add_apply]
      exact add_mem (Ideal.pow_le_pow_right (by omega) (h2 m i j)) (ih i j)
  have h4 : ∀ i j, ∃ L : A, ∀ k, f k i j - L ∈ 𝔞 ^ k := by
    intro i j
    obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := 𝔞) (fun k => f k i j) (fun {k m} hkm => by
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, ← neg_mem_iff, neg_sub]
      exact Ideal.pow_le_pow_right (Nat.le_succ k) (h3 k m hkm i j))
    refine ⟨L, fun k => ?_⟩
    have := hL k
    rwa [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at this
  choose L hL using h4
  let e : Matrix n n A := Matrix.of L
  have hL' : ∀ k i j, (f k - e) i j ∈ 𝔞 ^ k := fun k i j => hL i j k
  refine ⟨e, ?_, fun i j => ?_⟩
  · rw [← sub_eq_zero]
    ext i j
    refine IsHausdorff.haus' (I := 𝔞) _ fun k => ?_
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
    have e1 : e * e - e = (f k * f k - f k) - ((f k - e) * (f k - 1) + e * (f k - e)) := by
      noncomm_ring
    rw [e1, Matrix.sub_apply, Matrix.add_apply]
    exact sub_mem (Ideal.pow_le_pow_right (Nat.le_succ k) (h1 k i j))
      (add_mem (mul_mem_right _ (hL' k) i j) (mul_mem_left _ (hL' k) i j))
  · have e1 : e - x = (f 1 - f 0) - (f 1 - e) := by rw [f0]; abel
    rw [e1, Matrix.sub_apply]
    have a := h2 0 i j
    have b := hL' 1 i j
    rw [zero_add, pow_one] at a
    rw [pow_one] at b
    exact sub_mem a b

/- English proof (translation)
Use `choose g hg using Ideal.Quotient.mk_surjective (I := 𝔞)`. Establish `hxy : (y.map g).map (Ideal.Quotient.mk 𝔞) = y`. Use extensionality with `i j`. Simplify using `[hg]`. Take `⟨e, he, hex⟩` from `exists_idem 𝔞 (y.map g) fun i j => by`.

Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem]`. Establish `: (Ideal.Quotient.mk 𝔞).mapMatrix (y.map g * y.map g - y.map g) = 0`. Rewrite using `[map_sub, map_mul, RingHom.mapMatrix_apply, hxy, hy, sub_self]`. Conclude with `congrFun (congrFun this i) j`. Use `⟨e, he, ?_⟩` and prove the remaining obligations.

Use extensionality with `i j`. Use `(Ideal.Quotient.eq).2 (hex i j)` as an intermediate fact. Simplify `this` using `[hg]`.
-/
theorem exists_idem_lift (𝔞 : Ideal A) [IsAdicComplete 𝔞 A] (y : Matrix n n (A ⧸ 𝔞))
    (hy : y * y = y) :
    ∃ e : Matrix n n A, e * e = e ∧ e.map (Ideal.Quotient.mk 𝔞) = y := by
  choose g hg using Ideal.Quotient.mk_surjective (I := 𝔞)
  have hxy : (y.map g).map (Ideal.Quotient.mk 𝔞) = y := by
    ext i j; simp [hg]
  obtain ⟨e, he, hex⟩ := exists_idem 𝔞 (y.map g) fun i j => by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    have : (Ideal.Quotient.mk 𝔞).mapMatrix (y.map g * y.map g - y.map g) = 0 := by
      rw [map_sub, map_mul, RingHom.mapMatrix_apply, hxy, hy, sub_self]
    exact congrFun (congrFun this i) j
  refine ⟨e, he, ?_⟩
  ext i j
  have := (Ideal.Quotient.eq).2 (hex i j)
  simpa [hg] using this

/- English proof (translation)
Introduce `A _ 𝔞 _ N _ _ _ _`. Take `⟨n, p, hp⟩` from `Module.Finite.exists_fin' (A ⧸ 𝔞) N`. Take `⟨s, hs⟩` from `Module.projective_lifting_property p LinearMap.id hp`. Establish `hs' : ∀ z, p (s z) = z` using `fun z => LinearMap.congr_fun hs z`. Take `⟨e, he, hey⟩` from `exists_idem_lift 𝔞 (LinearMap.toMatrix' (s ∘ₗ p)) (by`.

Rewrite using `[← LinearMap.toMatrix'_comp]`. Use `congr 1`. Use `ext1 z`. Use `ext1`. Simplify using `[hs'])`.

Set `red : (Fin n → A) →ₛₗ[Ideal.Quotient.mk 𝔞] (Fin n → A ⧸ 𝔞)` to `{ toFun := fun z i => Ideal.Quotient.mk 𝔞 (z i) map_add' := fun a b => by ext i; simp map_smul' := fun a b => by ext i; simp }`. Establish `red_surj : Function.Surjective red` using `fun z => by choose g hg using Ideal.Quotient.mk_surjective (I := 𝔞)`. Conclude with `⟨fun i => g (z i), funext fun i => hg (z i)⟩`. Set `E : (Fin n → A) →ₗ[A] (Fin n → A)` to `Matrix.toLin' e`. Establish `hEE : ∀ z, E (E z) = E z` using `fun z => by`.

Simplify using `only [E, Matrix.toLin'_apply, Matrix.mulVec_mulVec, he]`. Establish `hred : ∀ z, red (E z) = s (p (red z))` using `fun z => by`. Establish `h1 : s (p (red z)) = Matrix.toLin' (LinearMap.toMatrix' (s ∘ₗ p)) (red z)`. Rewrite using `[Matrix.toLin'_toMatrix']`. Both sides reduce to the same expression.

Rewrite using `[h1, ← hey]`. Use extensionality with `i`. Simplify using `[red, E, Matrix.mulVec, dotProduct]`. Set `P` to `LinearMap.range E`. Set `q : (Fin n → A) →ₗ[A] P` to `E.rangeRestrict`.

Establish `hq : ∀ y : P, q y = y`. Introduce and unpack `⟨_, z, rfl⟩`. Conclude with `Subtype.ext (hEE z)`. Establish `hproj : Module.Projective A P` using `Module.Projective.of_split P.subtype q (LinearMap.ext hq)`. Set `u : P →ₛₗ[Ideal.Quotient.mk 𝔞] N` to `p.comp (red.comp P.subtype)`.

Establish `hu : ∀ y : P, u y = p (red y)` using `fun y => rfl`. Establish `u_surj : Function.Surjective u` using `fun z => by`. Take `⟨t, ht⟩` from `red_surj (s z)`. Use `⟨q t, ?_⟩` and prove the remaining obligations. Rewrite using `[hu]`.

Express the relevant statement in the definitionally equal form `p (red (E t)) = z`. Rewrite using `[hred, ht, hs', hs']`. Use `⟨P, inferInstance, inferInstance, inferInstance, hproj, u, ?_⟩` and prove the remaining obligations. Introduce `Q _ _ v`. Set `w0 : (Fin n → A ⧸ 𝔞) →ₗ[A ⧸ 𝔞] Q` to `(Pi.basisFun (A ⧸ 𝔞) (Fin n)).constr ℕ fun i => v (q (Pi.single i 1))`.

Establish `hw0 : w0.comp red = v.comp q`. Use `(Pi.basisFun A (Fin n)).ext fun i => ?_` and prove the remaining obligations. Establish `: red (Pi.basisFun A (Fin n) i) = Pi.basisFun (A ⧸ 𝔞) (Fin n) i`. Use extensionality with `j`. Distinguish the cases in `h : j = i`.

Substitute `h` using the available equality. Simplify using `[red]`. Simplify using `[red, h]`. Rewrite using `[LinearMap.comp_apply, this, LinearMap.comp_apply, Pi.basisFun_apply A]`. Conclude with `Module.Basis.constr_basis _ _ _ _`.

Establish `key : ∀ y : P, (w0 ∘ₗ s) (u y) = v y` using `fun y => by`. Establish `h1 : E y = y` using `congrArg Subtype.val (hq y)`. Rewrite using `[hu, LinearMap.comp_apply, ← hred, h1]`. Use `LinearMap.congr_fun hw0 (y : Fin n → A)` as an intermediate fact. Rewrite `this` using `[LinearMap.comp_apply, LinearMap.comp_apply, hq]`.

Conclude with `this`. Use `⟨w0 ∘ₗ s, key, fun w hw => ?_⟩` and prove the remaining obligations. Use extensionality with `z`. Take `⟨y, rfl⟩` from `u_surj z`. Rewrite using `[hw, key]`.
-/
theorem exists_lift : ∀ (A : Type) [CommRing A] (𝔞 : Ideal A) [IsAdicComplete 𝔞 A] (N : Type)
    [AddCommGroup N] [Module (A ⧸ 𝔞) N] [Module.Finite (A ⧸ 𝔞) N] [Module.Projective (A ⧸ 𝔞) N],
    ∃ (P : Type) (_ : AddCommGroup P) (_ : Module A P) (_ : Module.Finite A P)
      (_ : Module.Projective A P) (u : P →ₛₗ[Ideal.Quotient.mk 𝔞] N), SemiBC u := by
  intro A _ 𝔞 _ N _ _ _ _
  obtain ⟨n, p, hp⟩ := Module.Finite.exists_fin' (A ⧸ 𝔞) N
  obtain ⟨s, hs⟩ := Module.projective_lifting_property p LinearMap.id hp
  have hs' : ∀ z, p (s z) = z := fun z => LinearMap.congr_fun hs z
  obtain ⟨e, he, hey⟩ := exists_idem_lift 𝔞 (LinearMap.toMatrix' (s ∘ₗ p)) (by
    rw [← LinearMap.toMatrix'_comp]
    congr 1
    ext1 z
    ext1
    simp [hs'])
  let red : (Fin n → A) →ₛₗ[Ideal.Quotient.mk 𝔞] (Fin n → A ⧸ 𝔞) :=
    { toFun := fun z i => Ideal.Quotient.mk 𝔞 (z i)
      map_add' := fun a b => by ext i; simp
      map_smul' := fun a b => by ext i; simp }
  have red_surj : Function.Surjective red := fun z => by
    choose g hg using Ideal.Quotient.mk_surjective (I := 𝔞)
    exact ⟨fun i => g (z i), funext fun i => hg (z i)⟩
  let E : (Fin n → A) →ₗ[A] (Fin n → A) := Matrix.toLin' e
  have hEE : ∀ z, E (E z) = E z := fun z => by
    simp only [E, Matrix.toLin'_apply, Matrix.mulVec_mulVec, he]
  have hred : ∀ z, red (E z) = s (p (red z)) := fun z => by
    have h1 : s (p (red z)) = Matrix.toLin' (LinearMap.toMatrix' (s ∘ₗ p)) (red z) := by
      rw [Matrix.toLin'_toMatrix']; rfl
    rw [h1, ← hey]
    ext i
    simp [red, E, Matrix.mulVec, dotProduct]
  let P := LinearMap.range E
  let q : (Fin n → A) →ₗ[A] P := E.rangeRestrict
  have hq : ∀ y : P, q y = y := by
    rintro ⟨_, z, rfl⟩
    exact Subtype.ext (hEE z)
  have hproj : Module.Projective A P := Module.Projective.of_split P.subtype q (LinearMap.ext hq)
  let u : P →ₛₗ[Ideal.Quotient.mk 𝔞] N := p.comp (red.comp P.subtype)
  have hu : ∀ y : P, u y = p (red y) := fun y => rfl
  have u_surj : Function.Surjective u := fun z => by
    obtain ⟨t, ht⟩ := red_surj (s z)
    refine ⟨q t, ?_⟩
    rw [hu]
    change p (red (E t)) = z
    rw [hred, ht, hs', hs']
  refine ⟨P, inferInstance, inferInstance, inferInstance, hproj, u, ?_⟩
  intro Q _ _ v
  let w0 : (Fin n → A ⧸ 𝔞) →ₗ[A ⧸ 𝔞] Q :=
    (Pi.basisFun (A ⧸ 𝔞) (Fin n)).constr ℕ fun i => v (q (Pi.single i 1))
  have hw0 : w0.comp red = v.comp q := by
    refine (Pi.basisFun A (Fin n)).ext fun i => ?_
    have : red (Pi.basisFun A (Fin n) i) = Pi.basisFun (A ⧸ 𝔞) (Fin n) i := by
      ext j
      by_cases h : j = i
      · subst h; simp [red]
      · simp [red, h]
    rw [LinearMap.comp_apply, this, LinearMap.comp_apply, Pi.basisFun_apply A]
    exact Module.Basis.constr_basis _ _ _ _
  have key : ∀ y : P, (w0 ∘ₗ s) (u y) = v y := fun y => by
    have h1 : E y = y := congrArg Subtype.val (hq y)
    rw [hu, LinearMap.comp_apply, ← hred, h1]
    have := LinearMap.congr_fun hw0 (y : Fin n → A)
    rw [LinearMap.comp_apply, LinearMap.comp_apply, hq] at this
    exact this
  refine ⟨w0 ∘ₗ s, key, fun w hw => ?_⟩
  ext z
  obtain ⟨y, rfl⟩ := u_surj z
  rw [hw, key]

end GlobalTheory.BSP.LiftProj
