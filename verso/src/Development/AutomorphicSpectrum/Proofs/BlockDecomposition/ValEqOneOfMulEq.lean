import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.UnitTestFunctions.LiftUnit

noncomputable section

open NumberField IsDedekindDomain

namespace GlobalTheory.CompanionTheory.EisTF

open PositivityTheory.RgEis PositivityTheory.RgEis.TF GroundTheory.Global

/- English proof (translation)
Establish `key : ∀ {p q : Γ}, p ≤ 1 → q ≤ 1 → p * q = 1 → p = 1`. Introduce `p q hp hq hpq`. Use `le_antisymm hp (not_lt.mp fun hc => ?_)` and prove the remaining obligations. Establish `h2 : p * q < 1` using `lt_of_le_of_lt (mul_le_of_le_one_right' hq) hc`. Rewrite `h2` using `[hpq]`.

Conclude with `lt_irrefl _ h2`. Establish `hwu : w u = 1` using `key hu hu' (by rw [← map_mul, huu, map_one])`. Establish `hwm : w m < 1`. Use `not_le.mp fun hc => ?_` and prove the remaining obligations. Establish `h1 : w m * w mi = 1` using `by rw [← map_mul, hm, map_one]`.

Establish `h2 : w mi ≤ w m * w mi` using `le_mul_of_one_le_left' hc`. Rewrite `h2` using `[h1]`. Conclude with `absurd hmi (not_lt.mpr h2)`. Establish `hmy : w (m * y) < w u`. Rewrite using `[map_mul, hwu]`.

Conclude with `lt_of_le_of_lt (mul_le_of_le_one_right' hy) hwm`. Establish `hab : a * b = m * y + u` using `sub_eq_iff_eq_add.mp h`. Establish `hprod : w a * w b = 1`. Rewrite using `[← map_mul, hab, Valuation.map_add_eq_of_lt_right _ hmy, hwu]`. Conclude with `key ha hb hprod`.
-/
theorem val_eq_one_of_mul_eq {F Γ : Type*} [Field F] [LinearOrderedCommGroupWithZero Γ]
    (w : Valuation F Γ) {a b u u' m mi y : F} (ha : w a ≤ 1) (hb : w b ≤ 1) (hu : w u ≤ 1)
    (hu' : w u' ≤ 1) (huu : u * u' = 1) (hy : w y ≤ 1) (hm : m * mi = 1) (hmi : 1 < w mi)
    (h : a * b - u = m * y) : w a = 1 := by
  have key : ∀ {p q : Γ}, p ≤ 1 → q ≤ 1 → p * q = 1 → p = 1 := by
    intro p q hp hq hpq
    refine le_antisymm hp (not_lt.mp fun hc => ?_)
    have h2 : p * q < 1 := lt_of_le_of_lt (mul_le_of_le_one_right' hq) hc
    rw [hpq] at h2
    exact lt_irrefl _ h2
  have hwu : w u = 1 := key hu hu' (by rw [← map_mul, huu, map_one])
  have hwm : w m < 1 := by
    refine not_le.mp fun hc => ?_
    have h1 : w m * w mi = 1 := by rw [← map_mul, hm, map_one]
    have h2 : w mi ≤ w m * w mi := le_mul_of_one_le_left' hc
    rw [h1] at h2
    exact absurd hmi (not_lt.mpr h2)
  have hmy : w (m * y) < w u := by
    rw [map_mul, hwu]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' hy) hwm
  have hab : a * b = m * y + u := sub_eq_iff_eq_add.mp h
  have hprod : w a * w b = 1 := by
    rw [← map_mul, hab, Valuation.map_add_eq_of_lt_right _ hmy, hwu]
  exact key ha hb hprod

/- English proof (translation)
Introduce `k _ _ M hM a ha b hb u hu hab`. Take `⟨y, hy, hyeq⟩` from `hab`. Establish `hint : ∀ x : FiniteAdeleRing (𝓞 k) k, x ∈ OH k → ∀ v : HeightOneSpectrum (𝓞 k), Valued.v (x v) ≤ 1` using `fun x hx v => (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 k) k v).mp (hx v)`. Establish `hM0 : ∀ v : HeightOneSpectrum (𝓞 k), (M : v.adicCompletion k) ≠ 0`. Introduce `v`.

Rewrite using `[← map_natCast (algebraMap k (v.adicCompletion k)) M]`. Conclude with `(map_ne_zero _).mpr (Nat.cast_ne_zero.mpr hM)`. Establish `hMle : ∀ v : HeightOneSpectrum (𝓞 k), Valued.v (M : v.adicCompletion k) ≤ 1` using `fun v => (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 k) k v).mp (natCast_mem _ M)`. Take `⟨huU1, huU2⟩` from `Subgroup.mem_comap.mp hu`. Establish `hu1 : (u : FiniteAdeleRing (𝓞 k) k) ∈ OH k` using `fun v => huU1 v`.

Establish `hu2 : ((u⁻¹ : (FiniteAdeleRing (𝓞 k) k)ˣ) : FiniteAdeleRing (𝓞 k) k) ∈ OH k` using `fun v => huU2 v`. Establish `hunit : ∀ v : HeightOneSpectrum (𝓞 k), Valued.v (M : v.adicCompletion k) < 1 → Valued.v (a v) = 1`. Introduce `v hv`. Establish `hmul : (u : FiniteAdeleRing (𝓞 k) k) v * ((u⁻¹ : (FiniteAdeleRing (𝓞 k) k)ˣ) : FiniteAdeleRing (𝓞 k) k) v = 1` using `congrArg (fun z : FiniteAdeleRing (𝓞 k) k => z v) (Units.mul_inv u)`. Establish `hcomp : a v * b v - (u : FiniteAdeleRing (𝓞 k) k) v = (M : v.adicCompletion k) * y v` using `congrArg (fun z : FiniteAdeleRing (𝓞 k) k => z v) hyeq`.

Conclude with `val_eq_one_of_mul_eq Valued.v (hint a ha v) (hint b hb v) (hint _ hu1 v) (hint _ hu2 v) hmul (hint y hy v) (mul_inv_cancel₀ (hM0 v)) ((Valuation.one_lt_val_iff Valued.v (inv_ne_zero (hM0 v))).mpr (by rwa [inv_inv])) hcomp`. Set `f : ∀ v : HeightOneSpectrum (𝓞 k), v.adicCompletion k` to `fun v => if Valued.v (M : v.adicCompletion k) < 1 then a v else 1`. Set `g : ∀ v : HeightOneSpectrum (𝓞 k), v.adicCompletion k` to `fun v => if Valued.v (M : v.adicCompletion k) < 1 then (a v)⁻¹ else 1`. Establish `hf : ∀ v : HeightOneSpectrum (𝓞 k), f v ∈ v.adicCompletionIntegers k`. Introduce `v`.

Distinguish the cases in `hv : Valued.v (M : v.adicCompletion k) < 1`. Simplify using `only [f, if_pos hv]`. Conclude with `ha v`. Simplify using `only [f, if_neg hv]`. Conclude with `one_mem _`.

Establish `hg : ∀ v : HeightOneSpectrum (𝓞 k), g v ∈ v.adicCompletionIntegers k`. Introduce `v`. Distinguish the cases in `hv : Valued.v (M : v.adicCompletion k) < 1`. Simplify using `only [g, if_pos hv]`. Rewrite using `[HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 k) k v, map_inv₀, hunit v hv, inv_one]`.

Simplify using `only [g, if_neg hv]`. Conclude with `one_mem _`. Set `F : FiniteAdeleRing (𝓞 k) k` to `RestrictedProduct.mk f (Filter.Eventually.of_forall hf)`. Set `G : FiniteAdeleRing (𝓞 k) k` to `RestrictedProduct.mk g (Filter.Eventually.of_forall hg)`. Establish `hFG : F * G = 1`.

Use `RestrictedProduct.ext _ _ fun v => ?_` and prove the remaining obligations. Use `show f v * g v = 1`. Distinguish the cases in `hv : Valued.v (M : v.adicCompletion k) < 1`. Simplify using `only [f, g, if_pos hv]`. Use `mul_inv_cancel₀ fun h0 => ?_` and prove the remaining obligations.

Establish `h1` using `hunit v hv`. Rewrite `h1` using `[h0, map_zero]`. Conclude with `zero_ne_one h1`. Simplify using `only [f, g, if_neg hv, mul_one]`. Establish `hGF : G * F = 1`.

Rewrite using `[mul_comm]`. Conclude with `hFG`. Set `U : (FiniteAdeleRing (𝓞 k) k)ˣ` to `⟨F, G, hFG, hGF⟩`. Establish `hU : U ∈ finiteIntegralUnits k` using `Subgroup.mem_comap.mpr (Submonoid.mem_units_of_val_mem_inv_val_mem _ (fun v => hf v) (fun v => hg v))`. Use `⟨U, hU, ?_⟩` and prove the remaining obligations.

Set `Y : ∀ v : HeightOneSpectrum (𝓞 k), v.adicCompletion k` to `fun v => if Valued.v (M : v.adicCompletion k) < 1 then 0 else (a v - 1) * (M : v.adicCompletion k)⁻¹`. Establish `hY : ∀ v : HeightOneSpectrum (𝓞 k), Y v ∈ v.adicCompletionIntegers k`. Introduce `v`. Distinguish the cases in `hv : Valued.v (M : v.adicCompletion k) < 1`. Simplify using `only [Y, if_pos hv]`.

Conclude with `zero_mem _`. Simplify using `only [Y, if_neg hv]`. Establish `hM1 : Valued.v (M : v.adicCompletion k) = 1` using `le_antisymm (hMle v) (not_lt.mp hv)`. Rewrite using `[HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 k) k v, map_mul, map_inv₀, hM1, inv_one, mul_one]`. Conclude with `(Valuation.map_sub Valued.v (a v) 1).trans (max_le (hint a ha v) (Valuation.map_one Valued.v).le)`.

Use `⟨RestrictedProduct.mk Y (Filter.Eventually.of_forall hY), fun v => hY v, ?_⟩` and prove the remaining obligations. Use `RestrictedProduct.ext _ _ fun v => ?_` and prove the remaining obligations. Use `show a v - f v = (M : v.adicCompletion k) * Y v`. Distinguish the cases in `hv : Valued.v (M : v.adicCompletion k) < 1`. Simplify using `only [f, Y, if_pos hv, sub_self, mul_zero]`.

Simplify using `only [f, Y, if_neg hv]`. Rewrite using `[mul_comm, mul_assoc, inv_mul_cancel₀ (hM0 v), mul_one]`.
-/
theorem liftUnit : LiftUnit := by
  intro k _ _ M hM a ha b hb u hu hab
  obtain ⟨y, hy, hyeq⟩ := hab
  classical
  have hint : ∀ x : FiniteAdeleRing (𝓞 k) k, x ∈ OH k →
      ∀ v : HeightOneSpectrum (𝓞 k), Valued.v (x v) ≤ 1 :=
    fun x hx v => (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 k) k v).mp (hx v)
  have hM0 : ∀ v : HeightOneSpectrum (𝓞 k), (M : v.adicCompletion k) ≠ 0 := by
    intro v
    rw [← map_natCast (algebraMap k (v.adicCompletion k)) M]
    exact (map_ne_zero _).mpr (Nat.cast_ne_zero.mpr hM)
  have hMle : ∀ v : HeightOneSpectrum (𝓞 k), Valued.v (M : v.adicCompletion k) ≤ 1 := fun v =>
    (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 k) k v).mp (natCast_mem _ M)
  obtain ⟨huU1, huU2⟩ := Subgroup.mem_comap.mp hu
  have hu1 : (u : FiniteAdeleRing (𝓞 k) k) ∈ OH k := fun v => huU1 v
  have hu2 : ((u⁻¹ : (FiniteAdeleRing (𝓞 k) k)ˣ) : FiniteAdeleRing (𝓞 k) k) ∈ OH k :=
    fun v => huU2 v
  have hunit : ∀ v : HeightOneSpectrum (𝓞 k), Valued.v (M : v.adicCompletion k) < 1 →
      Valued.v (a v) = 1 := by
    intro v hv
    have hmul : (u : FiniteAdeleRing (𝓞 k) k) v *
        ((u⁻¹ : (FiniteAdeleRing (𝓞 k) k)ˣ) : FiniteAdeleRing (𝓞 k) k) v = 1 :=
      congrArg (fun z : FiniteAdeleRing (𝓞 k) k => z v) (Units.mul_inv u)
    have hcomp : a v * b v - (u : FiniteAdeleRing (𝓞 k) k) v = (M : v.adicCompletion k) * y v :=
      congrArg (fun z : FiniteAdeleRing (𝓞 k) k => z v) hyeq
    exact val_eq_one_of_mul_eq Valued.v (hint a ha v) (hint b hb v) (hint _ hu1 v) (hint _ hu2 v)
      hmul (hint y hy v) (mul_inv_cancel₀ (hM0 v))
      ((Valuation.one_lt_val_iff Valued.v (inv_ne_zero (hM0 v))).mpr (by rwa [inv_inv])) hcomp
  let f : ∀ v : HeightOneSpectrum (𝓞 k), v.adicCompletion k := fun v =>
    if Valued.v (M : v.adicCompletion k) < 1 then a v else 1
  let g : ∀ v : HeightOneSpectrum (𝓞 k), v.adicCompletion k := fun v =>
    if Valued.v (M : v.adicCompletion k) < 1 then (a v)⁻¹ else 1
  have hf : ∀ v : HeightOneSpectrum (𝓞 k), f v ∈ v.adicCompletionIntegers k := by
    intro v
    by_cases hv : Valued.v (M : v.adicCompletion k) < 1
    · simp only [f, if_pos hv]
      exact ha v
    · simp only [f, if_neg hv]
      exact one_mem _
  have hg : ∀ v : HeightOneSpectrum (𝓞 k), g v ∈ v.adicCompletionIntegers k := by
    intro v
    by_cases hv : Valued.v (M : v.adicCompletion k) < 1
    · simp only [g, if_pos hv]
      rw [HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 k) k v, map_inv₀, hunit v hv, inv_one]
    · simp only [g, if_neg hv]
      exact one_mem _
  let F : FiniteAdeleRing (𝓞 k) k := RestrictedProduct.mk f (Filter.Eventually.of_forall hf)
  let G : FiniteAdeleRing (𝓞 k) k := RestrictedProduct.mk g (Filter.Eventually.of_forall hg)
  have hFG : F * G = 1 := by
    refine RestrictedProduct.ext _ _ fun v => ?_
    show f v * g v = 1
    by_cases hv : Valued.v (M : v.adicCompletion k) < 1
    · simp only [f, g, if_pos hv]
      refine mul_inv_cancel₀ fun h0 => ?_
      have h1 := hunit v hv
      rw [h0, map_zero] at h1
      exact zero_ne_one h1
    · simp only [f, g, if_neg hv, mul_one]
  have hGF : G * F = 1 := by
    rw [mul_comm]
    exact hFG
  let U : (FiniteAdeleRing (𝓞 k) k)ˣ := ⟨F, G, hFG, hGF⟩
  have hU : U ∈ finiteIntegralUnits k :=
    Subgroup.mem_comap.mpr
      (Submonoid.mem_units_of_val_mem_inv_val_mem _ (fun v => hf v) (fun v => hg v))
  refine ⟨U, hU, ?_⟩
  let Y : ∀ v : HeightOneSpectrum (𝓞 k), v.adicCompletion k := fun v =>
    if Valued.v (M : v.adicCompletion k) < 1 then 0 else (a v - 1) * (M : v.adicCompletion k)⁻¹
  have hY : ∀ v : HeightOneSpectrum (𝓞 k), Y v ∈ v.adicCompletionIntegers k := by
    intro v
    by_cases hv : Valued.v (M : v.adicCompletion k) < 1
    · simp only [Y, if_pos hv]
      exact zero_mem _
    · simp only [Y, if_neg hv]
      have hM1 : Valued.v (M : v.adicCompletion k) = 1 := le_antisymm (hMle v) (not_lt.mp hv)
      rw [HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 k) k v, map_mul, map_inv₀, hM1, inv_one,
        mul_one]
      exact (Valuation.map_sub Valued.v (a v) 1).trans
        (max_le (hint a ha v) (Valuation.map_one Valued.v).le)
  refine ⟨RestrictedProduct.mk Y (Filter.Eventually.of_forall hY), fun v => hY v, ?_⟩
  refine RestrictedProduct.ext _ _ fun v => ?_
  show a v - f v = (M : v.adicCompletion k) * Y v
  by_cases hv : Valued.v (M : v.adicCompletion k) < 1
  · simp only [f, Y, if_pos hv, sub_self, mul_zero]
  · simp only [f, Y, if_neg hv]
    rw [mul_comm, mul_assoc, inv_mul_cancel₀ (hM0 v), mul_one]

end GlobalTheory.CompanionTheory.EisTF
