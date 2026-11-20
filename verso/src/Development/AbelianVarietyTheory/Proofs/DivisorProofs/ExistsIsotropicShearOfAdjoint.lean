import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EquivOfIsometryApply

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LowDat GlobalTheory.LowFilt

namespace GlobalTheory.LowFilt

/- English proof (translation)
Use `choose c hc using h`. Establish `hn' : (n : ℤ) ≠ 0` using `by exact_mod_cast hn.ne'`. Set `ψ : D.La →+ ℤ` to `AddMonoidHom.mk' c fun x y => mul_left_cancel₀ hn' (by rw [mul_add, ← hc, ← hc, ← hc, map_add])`. Take `⟨e, he⟩` from `D.unimod.2 ψ.toIntLinearMap`. Use `⟨e, D.unimod.1 (LinearMap.ext fun b => ?_)⟩` and prove the remaining obligations.

Rewrite using `[map_nsmul, he, hc, LinearMap.smul_apply, nsmul_eq_mul]`. Both sides reduce to the same expression.
-/
theorem exists_eq_nsmul_of_forall_ef_dvd {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H)
    {n : ℕ} (hn : 0 < n) (a : D.La) (h : ∀ b, (n : ℤ) ∣ D.EF a b) : ∃ e, a = n • e := by
  choose c hc using h
  have hn' : (n : ℤ) ≠ 0 := by exact_mod_cast hn.ne'
  let ψ : D.La →+ ℤ := AddMonoidHom.mk' c fun x y => mul_left_cancel₀ hn' (by rw [mul_add, ← hc, ← hc, ← hc, map_add])
  obtain ⟨e, he⟩ := D.unimod.2 ψ.toIntLinearMap
  refine ⟨e, D.unimod.1 (LinearMap.ext fun b => ?_)⟩
  rw [map_nsmul, he, hc, LinearMap.smul_apply, nsmul_eq_mul]
  rfl

/- English proof (translation)
Introduce `E _ _ _ H D X _ _ y n N hn hNn hC Z Z' hO σ w hσZ hσb hσy hσN hw hsat`. Establish `hN : 0 < N` using `Nat.pos_of_dvd_of_pos hNn hn`. Take `⟨k, hk⟩` from `hNn`. Establish `hnZ : (n : ℤ) ≠ 0` using `by exact_mod_cast hn.ne'`. Establish `ha : ∀ z ∈ Z, ∃ e ∈ perp D Z', w z = z + N • e`.

Introduce `z hz`. Take `⟨e, he⟩` from `exists_eq_nsmul_of_forall_ef_dvd D hN (w z - z) fun b => by`. Take `⟨b', hb', e, he⟩` from `hσN b`. Establish `h0 : D.EF z b' = 0` using `by rw [ef_swap, hb' z hz, neg_zero]`. Use `⟨D.EF z e, ?_⟩` and prove the remaining obligations.

Simplify using `only [map_sub, LinearMap.sub_apply, hw, he, map_add, map_nsmul, h0, nsmul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Use `⟨e, mem_perp.2 fun b hb => ?_, (sub_eq_iff_eq_add'.1 he)⟩` and prove the remaining obligations. Establish `h1 : D.EF (w z - z) b = 0` using `by rw [map_sub, LinearMap.sub_apply, hw, hσb b hb, sub_self]`. Rewrite `h1` using `[he, map_nsmul, LinearMap.smul_apply, smul_eq_zero]`.

Conclude with `h1.resolve_left hN.ne'`. Establish `hb : ∀ z a : D.La, (∃ e, y a = n • e) → (n : ℤ) ∣ D.EF (w z) a`. Introduce and unpack `z a ⟨e, he⟩`. Take `⟨e₁, he₁⟩` from `hσy a`. Take `⟨e', -, he'⟩` from `hsat (σ a) (hσZ a) ⟨e + e₁, by rw [he₁, he, smul_add]⟩`.

Use `⟨D.EF z e', ?_⟩` and prove the remaining obligations. Rewrite using `[hw, he', map_nsmul, nsmul_eq_mul]`. Establish `hwy : ∀ z, ∃ e, y (w z) = n • e` using `fun z => hC.2 (w z) fun b hb' => hb z b hb'`. Establish `hww : ∀ z z', (n : ℤ) ∣ D.EF (w z) (w z')` using `fun z z' => hb z (w z') (hwy z')`. Take `⟨f, hf⟩ : ∃ f : Z → Z → ℤ, ∀ z z', (n : ℤ) * f z z' = D.EF (w z) (w z')` from `⟨fun z z' => D.EF (w z) (w z') / n, fun z z' => Int.mul_ediv_cancel' (hww _ _)⟩`.

Take `⟨β, hβ⟩ : ∃ β : LinearMap.BilinForm ℤ Z, ∀ a b, β a b = f a b` from `⟨LinearMap.mk₂ ℤ f (fun z₁ z₂ z' => mul_left_cancel₀ hnZ (by rw [mul_add, hf, hf, hf]; simp)) (fun c z z' => mul_left_cancel₀ hnZ (by rw [smul_eq_mul, mul_left_comm, hf, hf]; simp)) (fun z z₁ z₂ => mul_left_cancel₀ hnZ (by rw [mul_add, hf, hf, hf]; simp)) (fun c z z' => mul_left_ …`. Establish `hskew : ∀ a b, β a b = -β b a` using `fun a b => by`. Rewrite using `[hβ, hβ]`. Conclude with `mul_left_cancel₀ hnZ (by rw [mul_neg, hf, hf, ef_swap])`. Establish `hadj : ∀ (c : 𝓞 E) a b, β (c • a) b = β a (H.bar c • b)` using `fun c a b => by`.

Rewrite using `[hβ, hβ]`. Conclude with `mul_left_cancel₀ hnZ (by rw [hf, hf, Submodule.coe_smul, Submodule.coe_smul, w.map_smul, w.map_smul, D.adj])`. Take `⟨c, hc⟩` from `exists_skew_solve hO.2.2.1 β hskew hadj`. Establish `ht : ∀ z : Z, (w ∘ₗ Z.subtype - n • (Z'.subtype ∘ₗ c)) z = w z - n • (c z : D.La)` using `fun z => rfl`. Use `⟨w ∘ₗ Z.subtype - n • (Z'.subtype ∘ₗ c), fun z => ?_, fun z z' => ?_, fun z a ha' => ?_⟩` and prove the remaining obligations.

Take `⟨e₁, he₁, hwz⟩` from `ha z z.2`. Use `⟨e₁ - k • (c z : D.La), sub_mem he₁ (nsmul_mem (hO.2.1 (c z).2) k), ?_⟩` and prove the remaining obligations. Rewrite using `[ht, hwz, hk, smul_sub, mul_smul]`. Normalize the expressions using the abelian group laws. Establish `e1 : D.EF (w z) (c z') = D.EF z (c z')` using `by rw [hw, hσb _ (c z').2]`.

Establish `e2 : D.EF (c z) (w z') = D.EF (c z) z'` using `by rw [ef_swap, hw, hσb _ (c z).2, ← ef_swap]`. Establish `e3 : D.EF (c z) (c z') = 0` using `hO.2.1 (c z).2 _ (c z').2`. Establish `e4 : (n : ℤ) * β z z' = D.EF (w z) (w z')` using `by rw [hβ, hf]`. Establish `e5` using `hc z z'`. Rewrite using `[ht, ht]`.

Simplify using `only [map_sub, map_nsmul, LinearMap.sub_apply, LinearMap.smul_apply, nsmul_eq_mul, e1, e2, e3]`. Take the linear combination `(-1 : ℤ) * e4 - (n : ℤ) * e5`. Rewrite using `[ht, map_sub, map_nsmul, LinearMap.sub_apply, LinearMap.smul_apply, nsmul_eq_mul]`. Conclude with `dvd_sub (hb z a ha') (dvd_mul_right _ _)`.
-/
theorem exists_shear_of_adjoint : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H) {X : Type}
    [AddCommGroup X] [Module (𝓞 E) X]
    (y : D.La →ₗ[𝓞 E] X) (n N : ℕ), 0 < n → N ∣ n → Cois D y n → ∀ Z Z' : Submodule (𝓞 E) D.La, IsOpp D Z Z' →
    ∀ σ w : D.La →ₗ[𝓞 E] D.La, (∀ a, σ a ∈ Z') → (∀ b ∈ Z', σ b = b) → (∀ a, ∃ e, y (σ a) = y a + n • e) →
    (∀ a, ∃ b ∈ perp D Z, ∃ e, σ a = a + b + N • e) → (∀ a b, D.EF (w a) b = D.EF a (σ b)) →
    (∀ b ∈ Z', (∃ e, y b = n • e) → ∃ e ∈ Z', b = n • e) →
    ∃ t : Z →ₗ[𝓞 E] D.La, (∀ z : Z, ∃ e ∈ perp D Z', t z = (z : D.La) + N • e) ∧ (∀ z z' : Z, D.EF (t z) (t z') = 0) ∧
      ∀ (z : Z) (a : D.La), (∃ e, y a = n • e) → (n : ℤ) ∣ D.EF (t z) a := by
  intro E _ _ _ H D X _ _ y n N hn hNn hC Z Z' hO σ w hσZ hσb hσy hσN hw hsat
  have hN : 0 < N := Nat.pos_of_dvd_of_pos hNn hn
  obtain ⟨k, hk⟩ := hNn
  have hnZ : (n : ℤ) ≠ 0 := by exact_mod_cast hn.ne'

  have ha : ∀ z ∈ Z, ∃ e ∈ perp D Z', w z = z + N • e := by
    intro z hz
    obtain ⟨e, he⟩ := exists_eq_nsmul_of_forall_ef_dvd D hN (w z - z) fun b => by
      obtain ⟨b', hb', e, he⟩ := hσN b
      have h0 : D.EF z b' = 0 := by rw [ef_swap, hb' z hz, neg_zero]
      refine ⟨D.EF z e, ?_⟩
      simp only [map_sub, LinearMap.sub_apply, hw, he, map_add, map_nsmul, h0, nsmul_eq_mul]
      ring
    refine ⟨e, mem_perp.2 fun b hb => ?_, (sub_eq_iff_eq_add'.1 he)⟩
    have h1 : D.EF (w z - z) b = 0 := by rw [map_sub, LinearMap.sub_apply, hw, hσb b hb, sub_self]
    rw [he, map_nsmul, LinearMap.smul_apply, smul_eq_zero] at h1
    exact h1.resolve_left hN.ne'

  have hb : ∀ z a : D.La, (∃ e, y a = n • e) → (n : ℤ) ∣ D.EF (w z) a := by
    rintro z a ⟨e, he⟩
    obtain ⟨e₁, he₁⟩ := hσy a
    obtain ⟨e', -, he'⟩ := hsat (σ a) (hσZ a) ⟨e + e₁, by rw [he₁, he, smul_add]⟩
    refine ⟨D.EF z e', ?_⟩
    rw [hw, he', map_nsmul, nsmul_eq_mul]
  have hwy : ∀ z, ∃ e, y (w z) = n • e := fun z => hC.2 (w z) fun b hb' => hb z b hb'
  have hww : ∀ z z', (n : ℤ) ∣ D.EF (w z) (w z') := fun z z' => hb z (w z') (hwy z')
  obtain ⟨f, hf⟩ : ∃ f : Z → Z → ℤ, ∀ z z', (n : ℤ) * f z z' = D.EF (w z) (w z') :=
    ⟨fun z z' => D.EF (w z) (w z') / n, fun z z' => Int.mul_ediv_cancel' (hww _ _)⟩
  obtain ⟨β, hβ⟩ : ∃ β : LinearMap.BilinForm ℤ Z, ∀ a b, β a b = f a b :=
    ⟨LinearMap.mk₂ ℤ f
      (fun z₁ z₂ z' => mul_left_cancel₀ hnZ (by rw [mul_add, hf, hf, hf]; simp))
      (fun c z z' => mul_left_cancel₀ hnZ (by rw [smul_eq_mul, mul_left_comm, hf, hf]; simp))
      (fun z z₁ z₂ => mul_left_cancel₀ hnZ (by rw [mul_add, hf, hf, hf]; simp))
      (fun c z z' => mul_left_cancel₀ hnZ (by rw [smul_eq_mul, mul_left_comm, hf, hf]; simp)),
      fun _ _ => rfl⟩
  have hskew : ∀ a b, β a b = -β b a := fun a b => by
    rw [hβ, hβ]
    exact mul_left_cancel₀ hnZ (by rw [mul_neg, hf, hf, ef_swap])
  have hadj : ∀ (c : 𝓞 E) a b, β (c • a) b = β a (H.bar c • b) := fun c a b => by
    rw [hβ, hβ]
    exact mul_left_cancel₀ hnZ (by rw [hf, hf, Submodule.coe_smul, Submodule.coe_smul, w.map_smul, w.map_smul, D.adj])
  obtain ⟨c, hc⟩ := exists_skew_solve hO.2.2.1 β hskew hadj
  have ht : ∀ z : Z, (w ∘ₗ Z.subtype - n • (Z'.subtype ∘ₗ c)) z = w z - n • (c z : D.La) := fun z => rfl
  refine ⟨w ∘ₗ Z.subtype - n • (Z'.subtype ∘ₗ c), fun z => ?_, fun z z' => ?_, fun z a ha' => ?_⟩
  · obtain ⟨e₁, he₁, hwz⟩ := ha z z.2
    refine ⟨e₁ - k • (c z : D.La), sub_mem he₁ (nsmul_mem (hO.2.1 (c z).2) k), ?_⟩
    rw [ht, hwz, hk, smul_sub, mul_smul]
    abel
  · have e1 : D.EF (w z) (c z') = D.EF z (c z') := by rw [hw, hσb _ (c z').2]
    have e2 : D.EF (c z) (w z') = D.EF (c z) z' := by rw [ef_swap, hw, hσb _ (c z).2, ← ef_swap]
    have e3 : D.EF (c z) (c z') = 0 := hO.2.1 (c z).2 _ (c z').2
    have e4 : (n : ℤ) * β z z' = D.EF (w z) (w z') := by rw [hβ, hf]
    have e5 := hc z z'
    rw [ht, ht]
    simp only [map_sub, map_nsmul, LinearMap.sub_apply, LinearMap.smul_apply, nsmul_eq_mul, e1, e2, e3]
    linear_combination (-1 : ℤ) * e4 - (n : ℤ) * e5
  · rw [ht, map_sub, map_nsmul, LinearMap.sub_apply, LinearMap.smul_apply, nsmul_eq_mul]
    exact dvd_sub (hb z a ha') (dvd_mul_right _ _)

end GlobalTheory.LowFilt
