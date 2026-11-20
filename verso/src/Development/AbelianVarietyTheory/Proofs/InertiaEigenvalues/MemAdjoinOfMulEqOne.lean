import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUnitBasePointAdjoinTwistedSigmaStatement

namespace GlobalTheory.UnitLemma.TwistUnit

open GlobalTheory.UnitLemma Polynomial

/- English proof (translation)
Take `⟨p, hp, hpt⟩` from `ht`. Establish `e : aeval t p = 0` using `hpt`. Rewrite `e` using `[aeval_eq_sum_range, Finset.sum_range_succ, hp.coeff_natDegree, one_smul]`. Break down `Nat.eq_zero_or_pos p.natDegree with h0 | hpos` into its components or cases. Rewrite `e` using `[h0]`.

Simplify using `at e`. Establish `: t = 0` using `by simpa using congrArg (t * ·) e`. Rewrite using `[this]`. Conclude with `Subalgebra.zero_mem _`. Take `⟨k, hk⟩ : ∃ k, p.natDegree = k + 1` from `⟨_, (Nat.succ_pred_eq_of_pos hpos).symm⟩`.

Rewrite `e` using `[hk]`. Establish `hts : t * s = 1` using `by rw [mul_comm]; exact h`. Establish `h1 : t ^ (k + 1) * s ^ k = t`. Rewrite using `[pow_succ', mul_assoc, ← mul_pow, hts, one_pow, mul_one]`. Establish `h2 : ∀ i ∈ Finset.range (k + 1), p.coeff i • t ^ i * s ^ k = p.coeff i • s ^ (k - i)`.

Introduce `i hi`. Establish `hik : i ≤ k` using `Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)`. Rewrite using `[smul_mul_assoc]`. Use `congr 1`. Rewrite using `[show s ^ k = s ^ i * s ^ (k - i) by rw [← pow_add, Nat.add_sub_cancel' hik], ← mul_assoc, ← mul_pow, hts, one_pow, one_mul]`.

Establish `e2` using `congrArg (· * s ^ k) e`. Simplify using `only [add_mul, zero_mul, Finset.sum_mul] at e2`. Rewrite `e2` using `[Finset.sum_congr rfl h2, h1]`. Establish `key : t = -∑ i ∈ Finset.range (k + 1), p.coeff i • s ^ (k - i)`. Take the linear combination `e2`.

Rewrite using `[key]`. Conclude with `Subalgebra.neg_mem _ (Subalgebra.sum_mem _ fun i _ => Subalgebra.smul_mem _ (Subalgebra.pow_mem _ (Algebra.self_mem_adjoin_singleton O s) _) _)`.
-/
theorem mem_adjoin_of_mul_eq_one {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {s t : A}
    (h : s * t = 1) (ht : IsIntegral O t) : t ∈ Algebra.adjoin O {s} := by
  obtain ⟨p, hp, hpt⟩ := ht
  have e : aeval t p = 0 := hpt
  rw [aeval_eq_sum_range, Finset.sum_range_succ, hp.coeff_natDegree, one_smul] at e
  rcases Nat.eq_zero_or_pos p.natDegree with h0 | hpos
  · rw [h0] at e
    simp at e
    have : t = 0 := by simpa using congrArg (t * ·) e
    rw [this]; exact Subalgebra.zero_mem _
  obtain ⟨k, hk⟩ : ∃ k, p.natDegree = k + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hpos).symm⟩
  rw [hk] at e
  have hts : t * s = 1 := by rw [mul_comm]; exact h
  have h1 : t ^ (k + 1) * s ^ k = t := by
    rw [pow_succ', mul_assoc, ← mul_pow, hts, one_pow, mul_one]
  have h2 : ∀ i ∈ Finset.range (k + 1), p.coeff i • t ^ i * s ^ k = p.coeff i • s ^ (k - i) := by
    intro i hi
    have hik : i ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    rw [smul_mul_assoc]
    congr 1
    rw [show s ^ k = s ^ i * s ^ (k - i) by rw [← pow_add, Nat.add_sub_cancel' hik], ← mul_assoc,
      ← mul_pow, hts, one_pow, one_mul]
  have e2 := congrArg (· * s ^ k) e
  simp only [add_mul, zero_mul, Finset.sum_mul] at e2
  rw [Finset.sum_congr rfl h2, h1] at e2
  have key : t = -∑ i ∈ Finset.range (k + 1), p.coeff i • s ^ (k - i) := by
    linear_combination e2
  rw [key]
  exact Subalgebra.neg_mem _ (Subalgebra.sum_mem _ fun i _ =>
    Subalgebra.smul_mem _ (Subalgebra.pow_mem _ (Algebra.self_mem_adjoin_singleton O s) _) _)

/- English proof (translation)
Proceed by induction on `ha using Algebra.adjoin_induction with`. Consider the case `mem x hx`. Rewrite `hx` using `[Set.mem_singleton_iff]`. Substitute `hx` using the available equality. Conclude with `hL`.

Consider the case `algebraMap r`. Introduce `y hy`. Rewrite using `[← Algebra.smul_def]`. Conclude with `L.smul_mem r hy`. Consider the case `add x z _ _ hx hz`.

Introduce `y hy`. Rewrite using `[add_mul]`. Conclude with `L.add_mem (hx y hy) (hz y hy)`. Consider the case `mul x z _ _ hx hz`. Introduce `y hy`.

Rewrite using `[mul_assoc]`. Conclude with `hx _ (hz y hy)`.
-/
theorem adjoin_stab {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {s : A} (L : Submodule O A)
    (hL : ∀ y ∈ L, s * y ∈ L) {a : A} (ha : a ∈ Algebra.adjoin O {s}) : ∀ y ∈ L, a * y ∈ L := by
  induction ha using Algebra.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff] at hx
    subst hx; exact hL
  | algebraMap r =>
    intro y hy
    rw [← Algebra.smul_def]; exact L.smul_mem r hy
  | add x z _ _ hx hz =>
    intro y hy
    rw [add_mul]; exact L.add_mem (hx y hy) (hz y hy)
  | mul x z _ _ hx hz =>
    intro y hy
    rw [mul_assoc]; exact hx _ (hz y hy)

variable {K : UQ}

/- English proof (translation)
Set `b` to `Module.Free.chooseBasis K.E B.A`. Establish `hsm : ∀ (e : K.E) (y : B.A), B.σ (e • y) = K.c e • B.σ y`. Introduce `e y`. Rewrite using `[Algebra.smul_def, map_mul, B.σ_alg, ← Algebra.smul_def]`. Establish `hli : LinearIndependent K.E ((B.σ : B.A →+ B.A) ∘ b)`.

Use `b.linearIndependent.map_of_injective_injective (fun r => K.c.symm r) (B.σ : B.A →+ B.A) ?_ ?_ ?_` and prove the remaining obligations. Introduce `r hr`. Simplify using `using hr`. Introduce `m hm`. Establish `: B.σ m = 0` using `hm`.

Simplify using `using this`. Introduce `r m show B.σ (K.c.symm r • m) = r • B.σ m`. Rewrite using `[hsm, RingEquiv.apply_symm_apply]`. Establish `hsp : ⊤ ≤ Submodule.span K.E (Set.range ((B.σ : B.A →+ B.A) ∘ b))`. Introduce `y _`.

Establish `h1 : y = ∑ j, K.c (b.repr (B.σ.symm y) j) • B.σ (b j)` using `by conv_lhs => rw [← B.σ.apply_symm_apply y, ← b.sum_repr (B.σ.symm y)]`. Rewrite using `[map_sum]`. Conclude with `Finset.sum_congr rfl fun j _ => hsm _ _`. Rewrite using `[h1]`. Conclude with `Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)`.

Set `b' : Module.Basis (Module.Free.ChooseBasisIndex K.E B.A) K.E B.A` to `Module.Basis.mk hli hsp`. Establish `hb' : ∀ i, b' i = B.σ (b i)` using `fun i => by`. Simplify using `only [b', Module.Basis.mk_apply]`. Both sides reduce to the same expression. Establish `hrepr : ∀ y i, b'.repr (B.σ y) i = K.c (b.repr y i)`.

Introduce `y i`. Establish `h1 : B.σ y = ∑ j, K.c (b.repr y j) • b' j` using `by conv_lhs => rw [← b.sum_repr y]`. Rewrite using `[map_sum]`. Conclude with `Finset.sum_congr rfl fun j _ => by rw [hsm, hb']`. Rewrite using `[h1, b'.repr_sum_self]`.

Rewrite using `[Algebra.trace_eq_matrix_trace b', Algebra.trace_eq_matrix_trace b, Matrix.trace, Matrix.trace, map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `only [Matrix.diag_apply, Algebra.leftMulMatrix_eq_repr_mul]`. Rewrite using `[hb', ← map_mul, hrepr]`.
-/
theorem trace_σ (B : InvAlg K) (a : B.A) :
    Algebra.trace K.E B.A (B.σ a) = K.c (Algebra.trace K.E B.A a) := by
  classical
  let b := Module.Free.chooseBasis K.E B.A
  have hsm : ∀ (e : K.E) (y : B.A), B.σ (e • y) = K.c e • B.σ y := by
    intro e y
    rw [Algebra.smul_def, map_mul, B.σ_alg, ← Algebra.smul_def]
  have hli : LinearIndependent K.E ((B.σ : B.A →+ B.A) ∘ b) := by
    refine b.linearIndependent.map_of_injective_injective (fun r => K.c.symm r) (B.σ : B.A →+ B.A) ?_ ?_ ?_
    · intro r hr
      simpa using hr
    · intro m hm
      have : B.σ m = 0 := hm
      simpa using this
    · intro r m
      show B.σ (K.c.symm r • m) = r • B.σ m
      rw [hsm, RingEquiv.apply_symm_apply]
  have hsp : ⊤ ≤ Submodule.span K.E (Set.range ((B.σ : B.A →+ B.A) ∘ b)) := by
    intro y _
    have h1 : y = ∑ j, K.c (b.repr (B.σ.symm y) j) • B.σ (b j) := by
      conv_lhs => rw [← B.σ.apply_symm_apply y, ← b.sum_repr (B.σ.symm y)]
      rw [map_sum]
      exact Finset.sum_congr rfl fun j _ => hsm _ _
    rw [h1]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  let b' : Module.Basis (Module.Free.ChooseBasisIndex K.E B.A) K.E B.A := Module.Basis.mk hli hsp
  have hb' : ∀ i, b' i = B.σ (b i) := fun i => by
    simp only [b', Module.Basis.mk_apply]
    rfl
  have hrepr : ∀ y i, b'.repr (B.σ y) i = K.c (b.repr y i) := by
    intro y i
    have h1 : B.σ y = ∑ j, K.c (b.repr y j) • b' j := by
      conv_lhs => rw [← b.sum_repr y]
      rw [map_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [hsm, hb']
    rw [h1, b'.repr_sum_self]
  rw [Algebra.trace_eq_matrix_trace b', Algebra.trace_eq_matrix_trace b, Matrix.trace, Matrix.trace,
    map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Matrix.diag_apply, Algebra.leftMulMatrix_eq_repr_mul]
  rw [hb', ← map_mul, hrepr]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, ha⟩`. Take `⟨b, hb⟩` from `K.c_int a`. Use `⟨b, ?_⟩` and prove the remaining obligations. Rewrite using `[← hb, ha, K.c_c]`.

Introduce and unpack `⟨a, rfl⟩`. Take `⟨b, hb⟩` from `K.c_int a`. Conclude with `⟨b, hb.symm⟩`.
-/
theorem mem_range_c (e : K.E) : K.c e ∈ (algebraMap K.O K.E).range ↔ e ∈ (algebraMap K.O K.E).range := by
  constructor
  · rintro ⟨a, ha⟩
    obtain ⟨b, hb⟩ := K.c_int a
    refine ⟨b, ?_⟩
    rw [← hb, ha, K.c_c]
  · rintro ⟨a, rfl⟩
    obtain ⟨b, hb⟩ := K.c_int a
    exact ⟨b, hb.symm⟩

/- English proof (translation)
Rewrite using `[trace_σ, mem_range_c]`.
-/
theorem trace_σ_mem (B : InvAlg K) (a : B.A) :
    Algebra.trace K.E B.A (B.σ a) ∈ (algebraMap K.O K.E).range ↔
      Algebra.trace K.E B.A a ∈ (algebraMap K.O K.E).range := by
  rw [trace_σ, mem_range_c]

/- English proof (translation)
Introduce `K B hg hs hi ε hε`. Take `⟨β₀, hβ, hb1, hb2⟩` from `GlobalTheory.T.exists_unit_basePoint_adjoin_twisted_sigma K B hg hs hi ε hε`. Use `⟨β₀, hβ, fun x hx => ?_⟩` and prove the remaining obligations. Use `set R := (algebraMap K.O K.E).range with hR`. Use `set T := Algebra.trace K.E B.A with hT`.

Establish `hεT : ∀ a, T (ε * a) ∈ R ↔ T a ∈ R`. Introduce `a`. Break down `hε with rfl | rfl` into its components or cases. Rewrite using `[one_mul]`. Rewrite using `[neg_one_mul, map_neg, neg_mem_iff]`.

Establish `hstab : ∀ L : Submodule K.O B.A, (∀ y ∈ L, B.g * y ∈ L) → ∀ w : B.A, ((∀ y ∈ L, T ((β₀ : B.A) * x * y * B.σ w) ∈ R) ↔ ∀ y ∈ L, T ((x : B.A) * y * B.σ w) ∈ R)`. Introduce `L hL w`. Establish `s1` using `adjoin_stab L hL hb1`. Establish `s2` using `adjoin_stab L hL hb2`. Prove the components needed by the constructor for the conclusion.

Introduce `h y hy`. Use `h _ (s2 y hy)` as an intermediate fact. Establish `e : (β₀ : B.A) * x * (((β₀⁻¹ : B.Aˣ) : B.A) * y) * B.σ w = x * y * B.σ w`. Use `β₀.mul_inv` as an intermediate fact. Take the linear combination `(↑x * y * B.σ w) * this`.

Rewrite `this` using `[e]`. Then use the resulting hypothesis. Introduce `h y hy`. Use `h _ (s1 y hy)` as an intermediate fact. Rewrite `this` using `[show (x : B.A) * ((β₀ : B.A) * y) * B.σ w = β₀ * x * y * B.σ w by ring]`. Then use the resulting hypothesis. Establish `hX' : ∀ (L : Submodule K.O B.A) (w : B.A), ((∀ y ∈ L, T ((x : B.A) * w * B.σ y) ∈ R) ↔ ∀ y ∈ L, T ((x : B.A) * y * B.σ w) ∈ R)`.

Introduce `L w`. Use `forall₂_congr fun y _ => ?_` and prove the remaining obligations. Rewrite using `[← trace_σ_mem B]`. Rewrite using `[show B.σ ((x : B.A) * w * B.σ y) = x * y * B.σ w by`. Rewrite using `[map_mul, map_mul, hx, B.σ_σ]`.

Use the proof step `ring]`. Establish `hsym : ∀ a b : B.A, T ((β₀ : B.A) * x * a * B.σ b) ∈ R ↔ T ((β₀ : B.A) * x * (B.g * b) * B.σ a) ∈ R`. Introduce `a b`. Rewrite using `[← trace_σ_mem B ((β₀ : B.A) * x * a * B.σ b), show B.σ ((β₀ : B.A) * x * a * B.σ b) = ε * ((β₀ : B.A) * x * (B.g * b) * B.σ a) by`. Rewrite using `[map_mul, map_mul, map_mul, hβ, hx, B.σ_σ]`.

Use the proof step `ring, hεT]`. Establish `hgg : B.σ B.g * B.g = 1` using `by rw [mul_comm]; exact hg`. Establish `hgad : B.g ∈ Algebra.adjoin K.O {B.σ B.g}` using `mem_adjoin_of_mul_eq_one hgg hi`. Use extensionality with `L`. Simplify using `only [Set.mem_setOf_eq, InvAlg.X, InvAlg.herm, Units.val_mul, ← hT, ← hR]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hLat, hU⟩`. Establish `h1 : ∀ y ∈ L, B.σ B.g * y ∈ L`. Introduce `y hy`. Rewrite using `[hU]`.

Introduce `y' hy'`. Rewrite using `[hsym, show (β₀ : B.A) * x * (B.g * (B.σ B.g * y)) * B.σ y' = β₀ * x * y * B.σ y' by`. Take the linear combination `((β₀ : B.A) * x * y * B.σ y') * hg]`. Conclude with `(hU y').1 hy' y hy`. Establish `h2 : ∀ y ∈ L, B.g * y ∈ L` using `adjoin_stab L h1 hgad`.

Use `⟨hLat, h2, fun y => ?_⟩` and prove the remaining obligations. Rewrite using `[hX' L y, ← hstab L h2, ← hU]`. Introduce and unpack `⟨hLat, h2, hXc⟩`. Use `⟨hLat, fun z => ?_⟩` and prove the remaining obligations. Rewrite using `[hstab L h2, ← hX', ← hXc]`.
-/
theorem twisted_unit_eq_unit : ∀ (K : UQ) (B : InvAlg K), B.g * B.σ B.g = 1 → B.P.Separable → IsIntegral K.O B.g →
    ∀ (ε : B.A), (ε = 1 ∨ ε = -1) → ∃ β₀ : B.Aˣ, B.σ (β₀ : B.A) = β₀ * (ε * B.g) ∧
      ∀ x : B.Aˣ, B.σ (x : B.A) = x →
        {L : Submodule K.O B.A | IsLat K.O K.E L ∧ ∀ z, z ∈ L ↔ ∀ y ∈ L,
          B.herm (β₀ * x) y z ∈ (algebraMap K.O K.E).range} = B.X x := by
  intro K B hg hs hi ε hε
  obtain ⟨β₀, hβ, hb1, hb2⟩ := GlobalTheory.T.exists_unit_basePoint_adjoin_twisted_sigma K B hg hs hi ε hε
  refine ⟨β₀, hβ, fun x hx => ?_⟩
  set R := (algebraMap K.O K.E).range with hR
  set T := Algebra.trace K.E B.A with hT
  have hεT : ∀ a, T (ε * a) ∈ R ↔ T a ∈ R := by
    intro a
    rcases hε with rfl | rfl
    · rw [one_mul]
    · rw [neg_one_mul, map_neg, neg_mem_iff]
  have hstab : ∀ L : Submodule K.O B.A, (∀ y ∈ L, B.g * y ∈ L) → ∀ w : B.A,
      ((∀ y ∈ L, T ((β₀ : B.A) * x * y * B.σ w) ∈ R) ↔ ∀ y ∈ L, T ((x : B.A) * y * B.σ w) ∈ R) := by
    intro L hL w
    have s1 := adjoin_stab L hL hb1
    have s2 := adjoin_stab L hL hb2
    constructor
    · intro h y hy
      have := h _ (s2 y hy)
      have e : (β₀ : B.A) * x * (((β₀⁻¹ : B.Aˣ) : B.A) * y) * B.σ w = x * y * B.σ w := by
        have := β₀.mul_inv
        linear_combination (↑x * y * B.σ w) * this
      rwa [e] at this
    · intro h y hy
      have := h _ (s1 y hy)
      rwa [show (x : B.A) * ((β₀ : B.A) * y) * B.σ w = β₀ * x * y * B.σ w by ring] at this
  have hX' : ∀ (L : Submodule K.O B.A) (w : B.A),
      ((∀ y ∈ L, T ((x : B.A) * w * B.σ y) ∈ R) ↔ ∀ y ∈ L, T ((x : B.A) * y * B.σ w) ∈ R) := by
    intro L w
    refine forall₂_congr fun y _ => ?_
    rw [← trace_σ_mem B]
    rw [show B.σ ((x : B.A) * w * B.σ y) = x * y * B.σ w by
      rw [map_mul, map_mul, hx, B.σ_σ]; ring]
  have hsym : ∀ a b : B.A, T ((β₀ : B.A) * x * a * B.σ b) ∈ R ↔
      T ((β₀ : B.A) * x * (B.g * b) * B.σ a) ∈ R := by
    intro a b
    rw [← trace_σ_mem B ((β₀ : B.A) * x * a * B.σ b),
      show B.σ ((β₀ : B.A) * x * a * B.σ b) = ε * ((β₀ : B.A) * x * (B.g * b) * B.σ a) by
        rw [map_mul, map_mul, map_mul, hβ, hx, B.σ_σ]; ring, hεT]
  have hgg : B.σ B.g * B.g = 1 := by rw [mul_comm]; exact hg
  have hgad : B.g ∈ Algebra.adjoin K.O {B.σ B.g} := mem_adjoin_of_mul_eq_one hgg hi
  ext L
  simp only [Set.mem_setOf_eq, InvAlg.X, InvAlg.herm, Units.val_mul, ← hT, ← hR]
  constructor
  · rintro ⟨hLat, hU⟩
    have h1 : ∀ y ∈ L, B.σ B.g * y ∈ L := by
      intro y hy
      rw [hU]
      intro y' hy'
      rw [hsym, show (β₀ : B.A) * x * (B.g * (B.σ B.g * y)) * B.σ y' = β₀ * x * y * B.σ y' by
        linear_combination ((β₀ : B.A) * x * y * B.σ y') * hg]
      exact (hU y').1 hy' y hy
    have h2 : ∀ y ∈ L, B.g * y ∈ L := adjoin_stab L h1 hgad
    refine ⟨hLat, h2, fun y => ?_⟩
    rw [hX' L y, ← hstab L h2, ← hU]
  · rintro ⟨hLat, h2, hXc⟩
    refine ⟨hLat, fun z => ?_⟩
    rw [hstab L h2, ← hX', ← hXc]

end GlobalTheory.UnitLemma.TwistUnit
