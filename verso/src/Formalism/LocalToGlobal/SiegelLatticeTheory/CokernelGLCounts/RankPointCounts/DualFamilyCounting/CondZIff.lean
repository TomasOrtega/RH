import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.DivMulMemSPOfSub

open NumberField Module Matrix

open scoped Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds

noncomputable section

namespace Formalism.L2.SG.Pf.fibreCountingData

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.G2 Formalism.L2.SG.Pf.G5

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "jK" => algebraMap (𝓞 K) K

section

variable {𝔭 : Ideal (𝓞 F)} [h𝔭 : 𝔭.IsMaximal] {k : ℕ}

local notation "mk" => Ideal.Quotient.mk (extP K 𝔭 ^ k)

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨w, hw⟩`. Take `⟨w, rfl⟩` from `Ideal.Quotient.mk_surjective w`. Establish `e : mk z = mk (w * ι d)` using `by rw [hw, map_mul]`. Conclude with `div_mem_SP_of_sub h𝔭 hd hk (Ideal.Quotient.eq.mp e)`.

Introduce `h`. Take `⟨w, hw⟩` from `exists_sub_mul_mem h𝔭 hd h k`. Use `⟨mk w, ?_⟩` and prove the remaining obligations. Establish `e : mk z = mk (w * ι d)` using `Ideal.Quotient.eq.mpr hw`. Rewrite using `[e, map_mul]`.
-/
theorem exists_mk_iff {d : 𝓞 F} (hd : d ≠ 0) (hk : vF 𝔭 d ≤ k) (z : 𝓞 K) :
    (∃ w : 𝓞 K ⧸ extP K 𝔭 ^ k, mk z = w * mk (ι d)) ↔ jK z / jK (ι d) ∈ HU.SP K 𝔭 := by
  constructor
  · rintro ⟨w, hw⟩
    obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective w
    have e : mk z = mk (w * ι d) := by rw [hw, map_mul]
    exact div_mem_SP_of_sub h𝔭 hd hk (Ideal.Quotient.eq.mp e)
  · intro h
    obtain ⟨w, hw⟩ := exists_sub_mul_mem h𝔭 hd h k
    refine ⟨mk w, ?_⟩
    have e : mk z = mk (w * ι d) := Ideal.Quotient.eq.mpr hw
    rw [e, map_mul]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨w, hw⟩`. Take `⟨w, rfl⟩` from `Ideal.Quotient.mk_surjective w`. Establish `e : mk z = mk (ι d * w * ι d')` using `by rw [hw, map_mul, map_mul]`. Establish `h1` using `div_mul_mem_SP_of_mem h𝔭 hd hd' hk (Ideal.Quotient.eq.mp e)`.

Establish `h2 : jK w ∈ HU.SP K 𝔭` using `HU.mem_SP.mpr ⟨1, (Ideal.ne_top_iff_one _).mp h𝔭.ne_top, w, by simp⟩`. Establish `hd0 : jK (ι d) ≠ 0` using `jK_ι_ne_zero (K := K) hd`. Establish `hd0' : jK (ι d') ≠ 0` using `jK_ι_ne_zero (K := K) hd'`. Establish `key : jK z / (jK (ι d) * jK (ι d')) = jK (z - ι d * w * ι d') / (jK (ι d) * jK (ι d')) + jK w`. Simplify using `only [map_sub, map_mul]`.

Rewrite using `[div_add' _ _ _ (mul_ne_zero hd0 hd0')]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[key]`. Conclude with `add_mem h1 h2`.

Introduce `h`. Establish `h' : jK z / jK (ι (d * d')) ∈ HU.SP K 𝔭` using `by rwa [map_mul, map_mul]`. Take `⟨w, hw⟩` from `exists_sub_mul_mem h𝔭 (mul_ne_zero hd hd') h' k`. Use `⟨mk w, ?_⟩` and prove the remaining obligations. Establish `e1 : z - ι d * w * ι d' = z - w * ι (d * d')` using `by rw [map_mul]; ring`.

Establish `e : mk z = mk (ι d * w * ι d')`. Rewrite using `[Ideal.Quotient.eq, e1]`. Conclude with `hw`. Rewrite using `[e, map_mul, map_mul]`.
-/
theorem exists_mk_mul_iff {d d' : 𝓞 F} (hd : d ≠ 0) (hd' : d' ≠ 0) (hk : vF 𝔭 d + vF 𝔭 d' ≤ k)
    (z : 𝓞 K) :
    (∃ w : 𝓞 K ⧸ extP K 𝔭 ^ k, mk z = mk (ι d) * w * mk (ι d')) ↔
      jK z / (jK (ι d) * jK (ι d')) ∈ HU.SP K 𝔭 := by
  constructor
  · rintro ⟨w, hw⟩
    obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective w
    have e : mk z = mk (ι d * w * ι d') := by rw [hw, map_mul, map_mul]
    have h1 := div_mul_mem_SP_of_mem h𝔭 hd hd' hk (Ideal.Quotient.eq.mp e)
    have h2 : jK w ∈ HU.SP K 𝔭 :=
      HU.mem_SP.mpr ⟨1, (Ideal.ne_top_iff_one _).mp h𝔭.ne_top, w, by simp⟩
    have hd0 : jK (ι d) ≠ 0 := jK_ι_ne_zero (K := K) hd
    have hd0' : jK (ι d') ≠ 0 := jK_ι_ne_zero (K := K) hd'
    have key : jK z / (jK (ι d) * jK (ι d')) =
        jK (z - ι d * w * ι d') / (jK (ι d) * jK (ι d')) + jK w := by
      simp only [map_sub, map_mul]
      rw [div_add' _ _ _ (mul_ne_zero hd0 hd0')]
      congr 1
      ring
    rw [key]
    exact add_mem h1 h2
  · intro h
    have h' : jK z / jK (ι (d * d')) ∈ HU.SP K 𝔭 := by rwa [map_mul, map_mul]
    obtain ⟨w, hw⟩ := exists_sub_mul_mem h𝔭 (mul_ne_zero hd hd') h' k
    refine ⟨mk w, ?_⟩
    have e1 : z - ι d * w * ι d' = z - w * ι (d * d') := by rw [map_mul]; ring
    have e : mk z = mk (ι d * w * ι d') := by
      rw [Ideal.Quotient.eq, e1]
      exact hw
    rw [e, map_mul, map_mul]

variable {m : ℕ} (a : Fin m → 𝓞 F)

def gramO (Y : Matrix (Fin m) (Fin m) (𝓞 K)) : Matrix (Fin m) (Fin m) (𝓞 K) :=
  Yᴴ * diagonal (fun i => ι (a i)) * Y - diagonal (fun i => ι (a i))

variable {a}

/- English proof (translation)
Unfold `diagQ`. Rewrite using `[Matrix.diagonal_map (map_zero _)]`.
-/
theorem diagQ_eq : diagQ K 𝔭 k a = (diagonal fun i => ι (a i)).map mk := by
  unfold diagQ
  rw [Matrix.diagonal_map (map_zero _)]

/- English proof (translation)
Unfold `diagQ`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨P, hP⟩ i j`. Use `(exists_mk_iff (ha j) (hk j) _).mp ⟨P i j, ?_⟩` and prove the remaining obligations. Use `congrFun (congrFun hP i) j` as an intermediate fact.

Simplify using `only [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.map_apply] at this`. Rewrite using `[map_mul, this]`. Introduce `h choose P hP using fun i j => (exists_mk_iff (ha j) (hk j) (ι (a i) * Y i j)).mpr (h i j)`. Use `⟨Matrix.of P, ?_⟩` and prove the remaining obligations. Use extensionality with `i j`.

Simplify using `only [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.map_apply, Matrix.of_apply]`. Rewrite using `[← hP i j, map_mul]`.
-/
theorem condP_iff_eqP (ha : ∀ i, a i ≠ 0) (hk : ∀ i, vF 𝔭 (a i) ≤ k)
    (Y : Matrix (Fin m) (Fin m) (𝓞 K)) [Fact (IsFixF K F)] :
    (∃ P, P * diagQ K 𝔭 k a = diagQ K 𝔭 k a * Y.map mk) ↔
      ∀ i j, jK (ι (a i) * Y i j) / jK (ι (a j)) ∈ HU.SP K 𝔭 := by
  unfold diagQ
  constructor
  · rintro ⟨P, hP⟩ i j
    refine (exists_mk_iff (ha j) (hk j) _).mp ⟨P i j, ?_⟩
    have := congrFun (congrFun hP i) j
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.map_apply] at this
    rw [map_mul, this]
  · intro h
    choose P hP using fun i j => (exists_mk_iff (ha j) (hk j) (ι (a i) * Y i j)).mpr (h i j)
    refine ⟨Matrix.of P, ?_⟩
    ext i j
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.map_apply, Matrix.of_apply]
    rw [← hP i j, map_mul]

/- English proof (translation)
Establish `hs : Function.Semiconj (Ideal.Quotient.mk (extP K 𝔭 ^ k)) star star` using `fun x => (idealPowerSpanBounds.star_mk 𝔭 k x).symm`. Establish `e : ∀ M : Matrix (Fin m) (Fin m) (𝓞 K), M.map (Ideal.Quotient.mk (extP K 𝔭 ^ k)) = (Ideal.Quotient.mk (extP K 𝔭 ^ k)).mapMatrix M` using `fun _ => rfl`. Rewrite using `[e (gramO a Y)]`. Unfold `gramO`. Rewrite using `[map_sub, map_mul, map_mul, ← e, ← e, ← e, diagQ_eq, Matrix.conjTranspose_map _ hs]`.
-/
theorem form_eq_map (Y : Matrix (Fin m) (Fin m) (𝓞 K)) [Fact (IsFixF K F)] :
    (Y.map mk)ᴴ * diagQ K 𝔭 k a * Y.map mk - diagQ K 𝔭 k a = (gramO a Y).map mk := by
  have hs : Function.Semiconj (Ideal.Quotient.mk (extP K 𝔭 ^ k)) star star :=
    fun x => (idealPowerSpanBounds.star_mk 𝔭 k x).symm
  have e : ∀ M : Matrix (Fin m) (Fin m) (𝓞 K),
      M.map (Ideal.Quotient.mk (extP K 𝔭 ^ k)) = (Ideal.Quotient.mk (extP K 𝔭 ^ k)).mapMatrix M :=
    fun _ => rfl
  rw [e (gramO a Y)]
  unfold gramO
  rw [map_sub, map_mul, map_mul, ← e, ← e, ← e, diagQ_eq, Matrix.conjTranspose_map _ hs]

/- English proof (translation)
Rewrite using `[form_eq_map Y]`. Unfold `diagQ`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨W, hW⟩ i j`. Use `(exists_mk_mul_iff (ha i) (ha j) (hk i j) _).mp ⟨W i j, ?_⟩` and prove the remaining obligations.

Use `congrFun (congrFun hW i) j` as an intermediate fact. Simplify `this` using `only [Matrix.map_apply, Matrix.mul_diagonal, Matrix.diagonal_mul]`. Introduce `h choose W hW using fun i j => (exists_mk_mul_iff (ha i) (ha j) (hk i j) (gramO a Y i j)).mpr (h i j)`. Use `⟨Matrix.of W, ?_⟩` and prove the remaining obligations. Use extensionality with `i j`.

Simplify using `only [Matrix.map_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.of_apply]`. Conclude with `hW i j`.
-/
theorem condW_iff (ha : ∀ i, a i ≠ 0) (hk : ∀ i j, vF 𝔭 (a i) + vF 𝔭 (a j) ≤ k)
    (Y : Matrix (Fin m) (Fin m) (𝓞 K)) [Fact (IsFixF K F)] :
    (∃ W, (Y.map mk)ᴴ * diagQ K 𝔭 k a * Y.map mk - diagQ K 𝔭 k a =
        diagQ K 𝔭 k a * W * diagQ K 𝔭 k a) ↔
      ∀ i j, jK (gramO a Y i j) / (jK (ι (a i)) * jK (ι (a j))) ∈ HU.SP K 𝔭 := by
  rw [form_eq_map Y]
  unfold diagQ
  constructor
  · rintro ⟨W, hW⟩ i j
    refine (exists_mk_mul_iff (ha i) (ha j) (hk i j) _).mp ⟨W i j, ?_⟩
    have := congrFun (congrFun hW i) j
    simpa only [Matrix.map_apply, Matrix.mul_diagonal, Matrix.diagonal_mul] using this
  · intro h
    choose W hW using fun i j => (exists_mk_mul_iff (ha i) (ha j) (hk i j) (gramO a Y i j)).mpr (h i j)
    refine ⟨Matrix.of W, ?_⟩
    ext i j
    simp only [Matrix.map_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.of_apply]
    exact hW i j

/- English proof (translation)
Unfold `diagQ`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨Z, hZ⟩ i j`. Use `(exists_mk_iff (ha j) (hk j) _).mp ⟨Z i j, ?_⟩` and prove the remaining obligations. Use `congrFun (congrFun hZ i) j` as an intermediate fact.

Simplify using `only [Matrix.sub_apply, Matrix.map_apply, Matrix.mul_diagonal] at this`. Rewrite using `[map_sub, this]`. Introduce `h choose Z hZ using fun i j => (exists_mk_iff (ha j) (hk j) (Y i j - Y' i j)).mpr (h i j)`. Use `⟨Matrix.of Z, ?_⟩` and prove the remaining obligations. Use extensionality with `i j`.

Simplify using `only [Matrix.sub_apply, Matrix.map_apply, Matrix.mul_diagonal, Matrix.of_apply]`. Rewrite using `[← hZ i j, map_sub]`.
-/
theorem condZ_iff (ha : ∀ i, a i ≠ 0) (hk : ∀ i, vF 𝔭 (a i) ≤ k)
    (Y Y' : Matrix (Fin m) (Fin m) (𝓞 K)) [Fact (IsFixF K F)] :
    (∃ Z, Y.map mk - Y'.map mk = Z * diagQ K 𝔭 k a) ↔
      ∀ i j, jK (Y i j - Y' i j) / jK (ι (a j)) ∈ HU.SP K 𝔭 := by
  unfold diagQ
  constructor
  · rintro ⟨Z, hZ⟩ i j
    refine (exists_mk_iff (ha j) (hk j) _).mp ⟨Z i j, ?_⟩
    have := congrFun (congrFun hZ i) j
    simp only [Matrix.sub_apply, Matrix.map_apply, Matrix.mul_diagonal] at this
    rw [map_sub, this]
  · intro h
    choose Z hZ using fun i j => (exists_mk_iff (ha j) (hk j) (Y i j - Y' i j)).mpr (h i j)
    refine ⟨Matrix.of Z, ?_⟩
    ext i j
    simp only [Matrix.sub_apply, Matrix.map_apply, Matrix.mul_diagonal, Matrix.of_apply]
    rw [← hZ i j, map_sub]

end

end Formalism.L2.SG.Pf.fibreCountingData
