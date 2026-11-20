import Mathlib
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsLocalData

open NumberField Matrix

noncomputable section

namespace Formalism.L2.SG.Pf.discriminantNormShapes

open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds Formalism.HermitianLattices.Ext.L3.traceDeterminantCongruences

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {c : Type} [Fintype c] [DecidableEq c]

def Ent (J : Ideal (𝓞 K)) (A : Matrix c c (𝓞 K)) : Prop := ∀ i j, A i j ∈ J

/- English proof (translation)
Introduce `i j` and use `by rw [Matrix.mul_apply] exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_mul (hA i k) (hB k j)`.
-/
theorem ent_mul {I J : Ideal (𝓞 K)} {A B : Matrix c c (𝓞 K)} (hA : Ent I A) (hB : Ent J B) :
    Ent (I * J) (A * B) := fun i j => by
  rw [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_mul (hA i k) (hB k j)

/- English proof (translation)
Introduce `i j` and use `by rw [Matrix.mul_apply] exact Ideal.sum_mem _ fun k _ => J.mul_mem_left _ (hB k j)`.
-/
theorem ent_mul_left {J : Ideal (𝓞 K)} (A : Matrix c c (𝓞 K)) {B : Matrix c c (𝓞 K)} (hB : Ent J B) :
    Ent J (A * B) := fun i j => by
  rw [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun k _ => J.mul_mem_left _ (hB k j)

/- English proof (translation)
Introduce `i j` and use `by rw [Matrix.mul_apply] exact Ideal.sum_mem _ fun k _ => J.mul_mem_right _ (hA i k)`.
-/
theorem ent_mul_right {J : Ideal (𝓞 K)} {A : Matrix c c (𝓞 K)} (hA : Ent J A) (B : Matrix c c (𝓞 K)) :
    Ent J (A * B) := fun i j => by
  rw [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun k _ => J.mul_mem_right _ (hA i k)

/- English proof (translation)
Introduce `i j` and use `J.add_mem (hA i j) (hB i j)`.
-/
theorem ent_add {J : Ideal (𝓞 K)} {A B : Matrix c c (𝓞 K)} (hA : Ent J A) (hB : Ent J B) :
    Ent J (A + B) := fun i j => J.add_mem (hA i j) (hB i j)

/- English proof (translation)
Introduce `i j` and use `J.sub_mem (hA i j) (hB i j)`.
-/
theorem ent_sub {J : Ideal (𝓞 K)} {A B : Matrix c c (𝓞 K)} (hA : Ent J A) (hB : Ent J B) :
    Ent J (A - B) := fun i j => J.sub_mem (hA i j) (hB i j)

/- English proof (translation)
Introduce `i j` and use `J.neg_mem (hA i j)`.
-/
theorem ent_neg {J : Ideal (𝓞 K)} {A : Matrix c c (𝓞 K)} (hA : Ent J A) : Ent J (-A) := fun i j => J.neg_mem (hA i j)

/- English proof (translation)
Introduce `i j` and use `J.mul_mem_left a (hA i j)`.
-/
theorem ent_smul {J : Ideal (𝓞 K)} (a : 𝓞 K) {A : Matrix c c (𝓞 K)} (hA : Ent J A) : Ent J (a • A) := fun i j => J.mul_mem_left a (hA i j)

/- English proof (translation)
Introduce `i j` and use `hIJ (hA i j)`.
-/
theorem ent_mono {I J : Ideal (𝓞 K)} (hIJ : I ≤ J) {A : Matrix c c (𝓞 K)} (hA : Ent I A) : Ent J A := fun i j => hIJ (hA i j)

/- English proof (translation)
Introduce `_ _` and use `Submodule.mem_top`.
-/
theorem ent_top (A : Matrix c c (𝓞 K)) : Ent (⊤ : Ideal (𝓞 K)) A := fun _ _ => Submodule.mem_top

/- English proof (translation)
Introduce `i j` and use `conjO_mem_pow hF 𝔭 k _ (hA j i)`.
-/
theorem ent_conjTranspose (hF : IsFixF K F) (𝔭 : Ideal (𝓞 F)) (k : ℕ) {A : Matrix c c (𝓞 K)}
    (hA : Ent (extP K 𝔭 ^ k) A) : Ent (extP K 𝔭 ^ k) Aᴴ := fun i j => conjO_mem_pow hF 𝔭 k _ (hA j i)

/- English proof (translation)
Introduce `i j` and use `J.mul_mem_right _ hx`.
-/
theorem ent_smul_of_mem {J : Ideal (𝓞 K)} {x : 𝓞 K} (hx : x ∈ J) (A : Matrix c c (𝓞 K)) :
    Ent J (x • A) := fun i j => J.mul_mem_right _ hx

/- English proof (translation)
Distinguish the cases in `h : ∃ t : 𝓞 K, t + conjO K t ∉ extP K 𝔭`. Take `⟨t0, ht0⟩` from `h`. Take `⟨a, ha⟩` from `exists_tr hF t0`. Establish `haP : a ∉ 𝔭`. Introduce `haP`.

Apply `ht0` to reduce the goal to its premises. Rewrite using `[← ha]`. Conclude with `Ideal.mem_map_of_mem _ haP`. Take `⟨b, c, hc, hbc⟩` from `h𝔭.exists_inv haP`. Use `⟨algebraMap (𝓞 F) (𝓞 K) b * t0, ?_⟩` and prove the remaining obligations.

Establish `e1 : algebraMap (𝓞 F) (𝓞 K) b * t0 + conjO K (algebraMap (𝓞 F) (𝓞 K) b * t0) - 1 = algebraMap (𝓞 F) (𝓞 K) (b * a - 1)`. Rewrite using `[map_mul, conjO_map hF, map_sub, map_mul, map_one, ha]`. Expand and normalize the polynomial expressions, which then agree. Establish `e2 : b * a - 1 = -c` using `by linear_combination hbc`. Rewrite using `[e1, e2, map_neg]`.

Conclude with `(extP K 𝔭).neg_mem (Ideal.mem_map_of_mem _ hc)`. Use `push_neg at h`. Establish `h1 : (1 : 𝓞 K) ∈ extP K 𝔭`. Apply `BallB.mem_of_unram hK` to reduce the goal to its premises. Introduce `θ`.

Establish `e : (θ - conjO K θ) * 1 = θ * (1 + conjO K 1) - (θ + conjO K θ)`. Rewrite using `[map_one]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `(extP K 𝔭).sub_mem ((extP K 𝔭).mul_mem_left _ (h 1)) (h θ)`.

Use `⟨0, ?_⟩` and prove the remaining obligations. Simplify using `using (extP K 𝔭).neg_mem h1`.
-/
private theorem exists_add_conj_sub_one_mem_extP (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) : ∃ t : 𝓞 K, t + conjO K t - 1 ∈ extP K 𝔭 := by
  by_cases h : ∃ t : 𝓞 K, t + conjO K t ∉ extP K 𝔭
  · obtain ⟨t0, ht0⟩ := h
    obtain ⟨a, ha⟩ := exists_tr hF t0
    have haP : a ∉ 𝔭 := by
      intro haP
      apply ht0
      rw [← ha]
      exact Ideal.mem_map_of_mem _ haP
    obtain ⟨b, c, hc, hbc⟩ := h𝔭.exists_inv haP
    refine ⟨algebraMap (𝓞 F) (𝓞 K) b * t0, ?_⟩
    have e1 : algebraMap (𝓞 F) (𝓞 K) b * t0 + conjO K (algebraMap (𝓞 F) (𝓞 K) b * t0) - 1 = algebraMap (𝓞 F) (𝓞 K) (b * a - 1) := by
      rw [map_mul, conjO_map hF, map_sub, map_mul, map_one, ha]; ring
    have e2 : b * a - 1 = -c := by linear_combination hbc
    rw [e1, e2, map_neg]
    exact (extP K 𝔭).neg_mem (Ideal.mem_map_of_mem _ hc)
  · push_neg at h
    have h1 : (1 : 𝓞 K) ∈ extP K 𝔭 := by
      apply BallB.mem_of_unram hK
      intro θ
      have e : (θ - conjO K θ) * 1 = θ * (1 + conjO K 1) - (θ + conjO K θ) := by
        rw [map_one]; ring
      rw [e]
      exact (extP K 𝔭).sub_mem ((extP K 𝔭).mul_mem_left _ (h 1)) (h θ)
    refine ⟨0, ?_⟩
    simpa using (extP K 𝔭).neg_mem h1

/- English proof (translation)
Take `⟨t, ht⟩` from `exists_add_conj_sub_one_mem_extP hK hF h𝔭`. Introduce `j`. Proceed by induction on `j with`. Consider the case `zero`. Introduce `_`.

Use `⟨0, fun _ _ => ?_⟩` and prove the remaining obligations. Rewrite using `[pow_zero, Ideal.one_eq_top]`. Conclude with `Submodule.mem_top`. Consider the case `succ j ih`. Introduce `hj`.

Take `⟨Z, hZ⟩` from `ih (by omega)`. Use `set E := S + Pᴴ * Z + Zᴴ * P + Zᴴ * H * Z with hE`. Use `set Y : Matrix c c (𝓞 K) := -(t • E) with hYdef`. Use `set W := Q * Y with hW`. Use `⟨Z + W, ?_⟩` and prove the remaining obligations.

Establish `hJ : extP K 𝔭 ^ (j + 1) = extP K 𝔭 * extP K 𝔭 ^ j` using `pow_succ' _ _`. Establish `hJ' : extP K 𝔭 ^ (j + 1) = extP K 𝔭 ^ j * extP K 𝔭` using `pow_succ _ _`. Establish `hY : Ent (extP K 𝔭 ^ j) Y` using `ent_neg (ent_smul t hZ)`. Establish `hYh : Ent (extP K 𝔭 ^ j) Yᴴ` using `ent_conjTranspose hF 𝔭 j hY`. Establish `hWj : Ent (extP K 𝔭 ^ j) W` using `ent_mul_left Q hY`.

Establish `hWh : Ent (extP K 𝔭 ^ j) Wᴴ` using `ent_conjTranspose hF 𝔭 j hWj`. Establish `hPQh : Ent (extP K 𝔭) (Pᴴ * Q - 1)ᴴ`. Use `ent_conjTranspose hF 𝔭 1 (A := Pᴴ * Q - 1) (by rw [pow_one]; exact hPQ)` as an intermediate fact. Rewrite `this` using `[pow_one]`. Then use the resulting hypothesis. Establish `hEh : Ent (extP K 𝔭 ^ (j + 1)) (Eᴴ - E)`.

Establish `e : Eᴴ - E = (Sᴴ - S) + Zᴴ * (Hᴴ - H) * Z`. Simplify using `only [hE, Matrix.conjTranspose_add, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]`. Normalize the expressions using the abelian group laws. Rewrite using `[e]`. Establish `hN : extP K 𝔭 ^ N ≤ extP K 𝔭 ^ (j + 1)` using `Ideal.pow_le_pow_right hj`.

Conclude with `ent_mono hN (ent_add hS (ent_mul_right (ent_mul_left _ hHh) _))`. Establish `eq1 : S + Pᴴ * (Z + W) + (Z + W)ᴴ * P + (Z + W)ᴴ * H * (Z + W) = E + Pᴴ * W + Wᴴ * P + Zᴴ * H * W + Wᴴ * H * Z + Wᴴ * H * W`. Simplify using `only [Matrix.conjTranspose_add, Matrix.mul_add, Matrix.add_mul]`. Rewrite using `[hE]`. Normalize the expressions using the abelian group laws.

Establish `eq2 : Pᴴ * W = (Pᴴ * Q - 1) * Y + Y`. Rewrite using `[hW, ← Matrix.mul_assoc, Matrix.sub_mul, Matrix.one_mul]`. Normalize the expressions using the abelian group laws. Establish `eq3 : Wᴴ * P = Yᴴ * (Pᴴ * Q - 1)ᴴ + Yᴴ`. Rewrite using `[hW, Matrix.conjTranspose_mul, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_one, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_assoc]`.

Normalize the expressions using the abelian group laws. Establish `eq4 : E + Y + Yᴴ = (1 - t - star t) • E - star t • (Eᴴ - E)`. Rewrite using `[hYdef, Matrix.conjTranspose_neg, Matrix.conjTranspose_smul]`. Simplify using `only [sub_smul, one_smul, smul_sub]`. Normalize the expressions using the abelian group laws.

Establish `hx : (1 - t - star t) ∈ extP K 𝔭`. Use `(extP K 𝔭).neg_mem ht` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Use `show 1 - t - conjO K t = -(t + conjO K t - 1)`. Expand and normalize the polynomial expressions, which then agree.

Establish `T1 : Ent (extP K 𝔭 ^ (j + 1)) ((1 - t - star t) • E)` using `fun a b => by`. Rewrite using `[hJ]`. Conclude with `Ideal.mul_mem_mul hx (hZ a b)`. Establish `T2 : Ent (extP K 𝔭 ^ (j + 1)) (star t • (Eᴴ - E))` using `ent_smul _ hEh`. Establish `T3 : Ent (extP K 𝔭 ^ (j + 1)) ((Pᴴ * Q - 1) * Y)`.

Rewrite using `[hJ]`. Conclude with `ent_mul hPQ hY`. Establish `T4 : Ent (extP K 𝔭 ^ (j + 1)) (Yᴴ * (Pᴴ * Q - 1)ᴴ)`. Rewrite using `[hJ']`. Conclude with `ent_mul hYh hPQh`.

Establish `T5 : Ent (extP K 𝔭 ^ (j + 1)) (Zᴴ * H * W)`. Rewrite using `[hJ]`. Conclude with `ent_mul (ent_mul_left Zᴴ hH) hWj`. Establish `FreeQuotientRank : Ent (extP K 𝔭 ^ (j + 1)) (Wᴴ * H * Z)`. Rewrite using `[hJ']`.

Conclude with `ent_mul_right (ent_mul hWh hH) Z`. Establish `T7 : Ent (extP K 𝔭 ^ (j + 1)) (Wᴴ * H * W)`. Rewrite using `[hJ']`. Conclude with `ent_mul_right (ent_mul hWh hH) W`. Establish `eq5 : E + Pᴴ * W + Wᴴ * P + Zᴴ * H * W + Wᴴ * H * Z + Wᴴ * H * W = ((1 - t - star t) • E - star t • (Eᴴ - E)) + (Pᴴ * Q - 1) * Y + Yᴴ * (Pᴴ * Q - 1)ᴴ + Zᴴ * H * W + Wᴴ * H * Z + Wᴴ * H * W`.

Rewrite using `[eq2, eq3, ← eq4]`. Normalize the expressions using the abelian group laws. Rewrite using `[eq1, eq5]`. Conclude with `ent_add (ent_add (ent_add (ent_add (ent_add (ent_sub T1 T2) T3) T4) T5) FreeQuotientRank) T7`.
-/
theorem exists_solve_herm (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {H P Q S : Matrix c c (𝓞 K)} (hH : Ent (extP K 𝔭) H)
    (hPQ : Ent (extP K 𝔭) (Pᴴ * Q - 1)) {N : ℕ} (hHh : Ent (extP K 𝔭 ^ N) (Hᴴ - H))
    (hS : Ent (extP K 𝔭 ^ N) (Sᴴ - S)) :
    ∀ j, j ≤ N → ∃ Z : Matrix c c (𝓞 K),
      Ent (extP K 𝔭 ^ j) (S + Pᴴ * Z + Zᴴ * P + Zᴴ * H * Z) := by
  obtain ⟨t, ht⟩ := exists_add_conj_sub_one_mem_extP hK hF h𝔭
  intro j
  induction j with
  | zero =>
    intro _
    refine ⟨0, fun _ _ => ?_⟩
    rw [pow_zero, Ideal.one_eq_top]
    exact Submodule.mem_top
  | succ j ih =>
    intro hj
    obtain ⟨Z, hZ⟩ := ih (by omega)
    set E := S + Pᴴ * Z + Zᴴ * P + Zᴴ * H * Z with hE
    set Y : Matrix c c (𝓞 K) := -(t • E) with hYdef
    set W := Q * Y with hW
    refine ⟨Z + W, ?_⟩
    have hJ : extP K 𝔭 ^ (j + 1) = extP K 𝔭 * extP K 𝔭 ^ j := pow_succ' _ _
    have hJ' : extP K 𝔭 ^ (j + 1) = extP K 𝔭 ^ j * extP K 𝔭 := pow_succ _ _
    have hY : Ent (extP K 𝔭 ^ j) Y := ent_neg (ent_smul t hZ)
    have hYh : Ent (extP K 𝔭 ^ j) Yᴴ := ent_conjTranspose hF 𝔭 j hY
    have hWj : Ent (extP K 𝔭 ^ j) W := ent_mul_left Q hY
    have hWh : Ent (extP K 𝔭 ^ j) Wᴴ := ent_conjTranspose hF 𝔭 j hWj
    have hPQh : Ent (extP K 𝔭) (Pᴴ * Q - 1)ᴴ := by
      have := ent_conjTranspose hF 𝔭 1 (A := Pᴴ * Q - 1) (by rw [pow_one]; exact hPQ)
      rwa [pow_one] at this
    have hEh : Ent (extP K 𝔭 ^ (j + 1)) (Eᴴ - E) := by
      have e : Eᴴ - E = (Sᴴ - S) + Zᴴ * (Hᴴ - H) * Z := by
        simp only [hE, Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
          Matrix.conjTranspose_conjTranspose, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
        abel
      rw [e]
      have hN : extP K 𝔭 ^ N ≤ extP K 𝔭 ^ (j + 1) := Ideal.pow_le_pow_right hj
      exact ent_mono hN (ent_add hS (ent_mul_right (ent_mul_left _ hHh) _))
    have eq1 : S + Pᴴ * (Z + W) + (Z + W)ᴴ * P + (Z + W)ᴴ * H * (Z + W) =
        E + Pᴴ * W + Wᴴ * P + Zᴴ * H * W + Wᴴ * H * Z + Wᴴ * H * W := by
      simp only [Matrix.conjTranspose_add, Matrix.mul_add, Matrix.add_mul]
      rw [hE]
      abel
    have eq2 : Pᴴ * W = (Pᴴ * Q - 1) * Y + Y := by
      rw [hW, ← Matrix.mul_assoc, Matrix.sub_mul, Matrix.one_mul]
      abel
    have eq3 : Wᴴ * P = Yᴴ * (Pᴴ * Q - 1)ᴴ + Yᴴ := by
      rw [hW, Matrix.conjTranspose_mul, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul,
        Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_one, Matrix.mul_sub,
        Matrix.mul_one, Matrix.mul_assoc]
      abel
    have eq4 : E + Y + Yᴴ = (1 - t - star t) • E - star t • (Eᴴ - E) := by
      rw [hYdef, Matrix.conjTranspose_neg, Matrix.conjTranspose_smul]
      simp only [sub_smul, one_smul, smul_sub]
      abel
    have hx : (1 - t - star t) ∈ extP K 𝔭 := by
      have := (extP K 𝔭).neg_mem ht
      convert this using 1
      show 1 - t - conjO K t = -(t + conjO K t - 1)
      ring
    have T1 : Ent (extP K 𝔭 ^ (j + 1)) ((1 - t - star t) • E) := fun a b => by
      rw [hJ]; exact Ideal.mul_mem_mul hx (hZ a b)
    have T2 : Ent (extP K 𝔭 ^ (j + 1)) (star t • (Eᴴ - E)) := ent_smul _ hEh
    have T3 : Ent (extP K 𝔭 ^ (j + 1)) ((Pᴴ * Q - 1) * Y) := by
      rw [hJ]; exact ent_mul hPQ hY
    have T4 : Ent (extP K 𝔭 ^ (j + 1)) (Yᴴ * (Pᴴ * Q - 1)ᴴ) := by
      rw [hJ']; exact ent_mul hYh hPQh
    have T5 : Ent (extP K 𝔭 ^ (j + 1)) (Zᴴ * H * W) := by
      rw [hJ]; exact ent_mul (ent_mul_left Zᴴ hH) hWj
    have FreeQuotientRank : Ent (extP K 𝔭 ^ (j + 1)) (Wᴴ * H * Z) := by
      rw [hJ']; exact ent_mul_right (ent_mul hWh hH) Z
    have T7 : Ent (extP K 𝔭 ^ (j + 1)) (Wᴴ * H * W) := by
      rw [hJ']; exact ent_mul_right (ent_mul hWh hH) W
    have eq5 : E + Pᴴ * W + Wᴴ * P + Zᴴ * H * W + Wᴴ * H * Z + Wᴴ * H * W =
        ((1 - t - star t) • E - star t • (Eᴴ - E)) + (Pᴴ * Q - 1) * Y + Yᴴ * (Pᴴ * Q - 1)ᴴ
          + Zᴴ * H * W + Wᴴ * H * Z + Wᴴ * H * W := by
      rw [eq2, eq3, ← eq4]
      abel
    rw [eq1, eq5]
    exact ent_add (ent_add (ent_add (ent_add (ent_add (ent_sub T1 T2) T3) T4) T5) FreeQuotientRank) T7

variable [Fact (IsFixF K F)]

/- English proof (translation)
Introduce `i j` and use `by obtain ⟨x, hx, hxe⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 (hA i j) have h1 : A i j - x ∈ extP K 𝔭 ^ k := by rw [← Ideal.Quotient.eq]; exact hxe.symm have h2 : extP K 𝔭 ^ k ≤ extP K 𝔭 := by calc extP K 𝔭 ^ k ≤ extP K 𝔭 ^ 1 := Ideal.pow_le_pow_rig …`.
-/
theorem ent_lift {𝔭 : Ideal (𝓞 F)} {k : ℕ} (hk : 1 ≤ k)
    {A : Matrix c c (𝓞 K)}
    (hA : ∀ i j, Ideal.Quotient.mk (extP K 𝔭 ^ k) (A i j) ∈ (extP K 𝔭).map (Ideal.Quotient.mk (extP K 𝔭 ^ k))) :
    Ent (extP K 𝔭) A := fun i j => by
  obtain ⟨x, hx, hxe⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 (hA i j)
  have h1 : A i j - x ∈ extP K 𝔭 ^ k := by
    rw [← Ideal.Quotient.eq]; exact hxe.symm
  have h2 : extP K 𝔭 ^ k ≤ extP K 𝔭 := by
    calc extP K 𝔭 ^ k ≤ extP K 𝔭 ^ 1 := Ideal.pow_le_pow_right hk
      _ = extP K 𝔭 := pow_one _
  have := (extP K 𝔭).add_mem (h2 h1) hx
  simpa using this

/- English proof (translation)
Introduce `i j` and use `by have := congrFun (congrFun hA i) j simpa [Ideal.Quotient.eq_zero_iff_mem] using this`.
-/
theorem ent_of_map_eq_zero {𝔭 : Ideal (𝓞 F)} {k : ℕ} {A : Matrix c c (𝓞 K)}
    (hA : A.map (Ideal.Quotient.mk (extP K 𝔭 ^ k)) = 0) : Ent (extP K 𝔭 ^ k) A := fun i j => by
  have := congrFun (congrFun hA i) j
  simpa [Ideal.Quotient.eq_zero_iff_mem] using this

/- English proof (translation)
Establish `hF : IsFixF K F` using `Fact.out`. Take `⟨H', rfl⟩` from `reductionMapsOfForms.exists_lift 𝔭 k H`. Take `⟨P', rfl⟩` from `reductionMapsOfForms.exists_lift 𝔭 k P`. Take `⟨Q', rfl⟩` from `reductionMapsOfForms.exists_lift 𝔭 k Q`. Take `⟨S', rfl⟩` from `reductionMapsOfForms.exists_lift 𝔭 k S`.

Establish `hmap : ∀ A : Matrix c c (𝓞 K), A.map (reductionMapsOfForms.mkk K 𝔭 k) = 0 → Ent (extP K 𝔭 ^ k) A` using `fun A hA => ent_of_map_eq_zero hA`. Establish `hH' : Ent (extP K 𝔭) H'` using `ent_lift hk hH`. Establish `hPQ' : Ent (extP K 𝔭) (P'ᴴ * Q' - 1)`. Apply `ent_lift hk` to reduce the goal to its premises. Introduce `i j`.

Establish `e : (P'ᴴ * Q' - 1).map (reductionMapsOfForms.mkk K 𝔭 k) = (P'.map (reductionMapsOfForms.mkk K 𝔭 k))ᴴ * Q'.map (reductionMapsOfForms.mkk K 𝔭 k) - 1`. Apply the tactic sequence `rw [reductionMapsOfForms.map_conjTranspose, Matrix.map_sub, Matrix.map_mul, Matrix.map_one] <;> simp`. Use `hPQ i j` as an intermediate fact. Rewrite `this` using `[← e]`. Conclude with `this`.

Establish `hHh' : Ent (extP K 𝔭 ^ k) (H'ᴴ - H')`. Apply `hmap` to reduce the goal to its premises. Rewrite using `[Matrix.map_sub, ← reductionMapsOfForms.map_conjTranspose, hHh, sub_self]`. Simplify using the standard rewrite rules. Establish `hS' : Ent (extP K 𝔭 ^ k) (S'ᴴ - S')`.

Apply `hmap` to reduce the goal to its premises. Rewrite using `[Matrix.map_sub, ← reductionMapsOfForms.map_conjTranspose, hS, sub_self]`. Simplify using the standard rewrite rules. Take `⟨Z', hZ'⟩` from `exists_solve_herm hK hF h𝔭 hH' hPQ' hHh' hS' k le_rfl`. Use `⟨Z'.map (reductionMapsOfForms.mkk K 𝔭 k), ?_⟩` and prove the remaining obligations.

Establish `e : (S' + P'ᴴ * Z' + Z'ᴴ * P' + Z'ᴴ * H' * Z').map (reductionMapsOfForms.mkk K 𝔭 k) = S'.map (reductionMapsOfForms.mkk K 𝔭 k) + (P'.map (reductionMapsOfForms.mkk K 𝔭 k))ᴴ * Z'.map (reductionMapsOfForms.mkk K 𝔭 k) + (Z'.map (reductionMapsOfForms.mkk K 𝔭 k))ᴴ * P'.map (reductionMap …`. Simplify using `only [reductionMapsOfForms.map_conjTranspose]`. Simplify using `only [← RingHom.mapMatrix_apply, map_add, map_mul]`. Rewrite using `[← e]`. Use extensionality with `i j`.

Use `show Ideal.Quotient.mk (extP K 𝔭 ^ k) _ = 0`. Conclude with `Ideal.Quotient.eq_zero_iff_mem.2 (hZ' i j)`.
-/
theorem exists_solve_quot (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {k : ℕ}
    (hk : 1 ≤ k) {H P Q S : Matrix c c (𝓞 K ⧸ extP K 𝔭 ^ k)} (hHh : Hᴴ = H)
    (hH : ∀ i j, H i j ∈ (extP K 𝔭).map (Ideal.Quotient.mk (extP K 𝔭 ^ k)))
    (hPQ : ∀ i j, (Pᴴ * Q - 1) i j ∈ (extP K 𝔭).map (Ideal.Quotient.mk (extP K 𝔭 ^ k)))
    (hS : Sᴴ = S) : ∃ Z, S + Pᴴ * Z + Zᴴ * P + Zᴴ * H * Z = 0 := by
  have hF : IsFixF K F := Fact.out
  obtain ⟨H', rfl⟩ := reductionMapsOfForms.exists_lift 𝔭 k H
  obtain ⟨P', rfl⟩ := reductionMapsOfForms.exists_lift 𝔭 k P
  obtain ⟨Q', rfl⟩ := reductionMapsOfForms.exists_lift 𝔭 k Q
  obtain ⟨S', rfl⟩ := reductionMapsOfForms.exists_lift 𝔭 k S
  have hmap : ∀ A : Matrix c c (𝓞 K), A.map (reductionMapsOfForms.mkk K 𝔭 k) = 0 → Ent (extP K 𝔭 ^ k) A :=
    fun A hA => ent_of_map_eq_zero hA
  have hH' : Ent (extP K 𝔭) H' := ent_lift hk hH
  have hPQ' : Ent (extP K 𝔭) (P'ᴴ * Q' - 1) := by
    apply ent_lift hk
    intro i j
    have e : (P'ᴴ * Q' - 1).map (reductionMapsOfForms.mkk K 𝔭 k) = (P'.map (reductionMapsOfForms.mkk K 𝔭 k))ᴴ * Q'.map (reductionMapsOfForms.mkk K 𝔭 k) - 1 := by
      rw [reductionMapsOfForms.map_conjTranspose, Matrix.map_sub, Matrix.map_mul, Matrix.map_one] <;> simp
    have := hPQ i j
    rw [← e] at this
    exact this
  have hHh' : Ent (extP K 𝔭 ^ k) (H'ᴴ - H') := by
    apply hmap
    rw [Matrix.map_sub, ← reductionMapsOfForms.map_conjTranspose, hHh, sub_self]
    simp
  have hS' : Ent (extP K 𝔭 ^ k) (S'ᴴ - S') := by
    apply hmap
    rw [Matrix.map_sub, ← reductionMapsOfForms.map_conjTranspose, hS, sub_self]
    simp
  obtain ⟨Z', hZ'⟩ := exists_solve_herm hK hF h𝔭 hH' hPQ' hHh' hS' k le_rfl
  refine ⟨Z'.map (reductionMapsOfForms.mkk K 𝔭 k), ?_⟩
  have e : (S' + P'ᴴ * Z' + Z'ᴴ * P' + Z'ᴴ * H' * Z').map (reductionMapsOfForms.mkk K 𝔭 k) =
      S'.map (reductionMapsOfForms.mkk K 𝔭 k) + (P'.map (reductionMapsOfForms.mkk K 𝔭 k))ᴴ * Z'.map (reductionMapsOfForms.mkk K 𝔭 k) +
        (Z'.map (reductionMapsOfForms.mkk K 𝔭 k))ᴴ * P'.map (reductionMapsOfForms.mkk K 𝔭 k) +
        (Z'.map (reductionMapsOfForms.mkk K 𝔭 k))ᴴ * H'.map (reductionMapsOfForms.mkk K 𝔭 k) * Z'.map (reductionMapsOfForms.mkk K 𝔭 k) := by
    simp only [reductionMapsOfForms.map_conjTranspose]
    simp only [← RingHom.mapMatrix_apply, map_add, map_mul]
  rw [← e]
  ext i j
  show Ideal.Quotient.mk (extP K 𝔭 ^ k) _ = 0
  exact Ideal.Quotient.eq_zero_iff_mem.2 (hZ' i j)

end Formalism.L2.SG.Pf.discriminantNormShapes
