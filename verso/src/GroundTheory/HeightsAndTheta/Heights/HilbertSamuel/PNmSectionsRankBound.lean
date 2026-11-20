import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsNmSectionsRankBound
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsNmSectionsFinite
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSecMRankBound
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

namespace NmSectionsRankBound

variable {K : Type} [Fintype K] {ι : K → Type} [∀ κ, Fintype (ι κ)] {Ω : Type} [Field Ω]

omit [∀ κ, Fintype (ι κ)] in

/- English proof (translation)
Introduce `c' hc'`. Establish `hmem : ∀ κ, y ⟨κ, c κ⟩ / y ⟨κ, c' κ⟩ ∈ chartRingZ y c'` using `fun κ => Algebra.subset_adjoin ⟨⟨κ, c κ⟩, rfl⟩`. Establish `hk : ∀ κ, y ⟨κ, c' κ⟩ ^ (-((τ' : ℤ) * a' κ)) = y ⟨κ, c' κ⟩ ^ (-((τ : ℤ) * a κ)) * (y ⟨κ, c' κ⟩ ^ e κ)⁻¹`. Introduce `κ`. Rewrite using `[← he κ, neg_add, zpow_add₀ (hc' κ), zpow_neg (y ⟨κ, c' κ⟩) (e κ : ℤ), zpow_natCast]`.

Establish `heq : (∏ κ, y ⟨κ, c κ⟩ ^ e κ) * s * ∏ κ, y ⟨κ, c' κ⟩ ^ (-((τ' : ℤ) * a' κ)) = (s * ∏ κ, y ⟨κ, c' κ⟩ ^ (-((τ : ℤ) * a κ))) * ∏ κ, (y ⟨κ, c κ⟩ / y ⟨κ, c' κ⟩) ^ e κ`. Simplify using `only [hk, div_pow, Finset.prod_mul_distrib, Finset.prod_div_distrib, Finset.prod_inv_distrib]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[heq]`. Use `Subalgebra.mul_mem _ (hs c' hc') (Subalgebra.prod_mem _ fun κ _ => Subalgebra.pow_mem _ ?_ _)` and prove the remaining obligations.

Conclude with `(integralClosure (chartRingZ y c') Ω).algebraMap_mem ⟨_, hmem κ⟩`.
-/
theorem shift_mem (y : (Σ κ, ι κ) → Ω) (c : ∀ κ, ι κ) (a a' : K → ℤ) (τ τ' : ℕ) (e : K → ℕ)
    (he : ∀ κ, (τ : ℤ) * a κ + e κ = τ' * a' κ) {s : Ω} (hs : s ∈ chartLatNm y a τ) :
    (∏ κ, y ⟨κ, c κ⟩ ^ e κ) * s ∈ chartLatNm y a' τ' := by
  intro c' hc'
  have hmem : ∀ κ, y ⟨κ, c κ⟩ / y ⟨κ, c' κ⟩ ∈ chartRingZ y c' := fun κ =>
    Algebra.subset_adjoin ⟨⟨κ, c κ⟩, rfl⟩
  have hk : ∀ κ, y ⟨κ, c' κ⟩ ^ (-((τ' : ℤ) * a' κ)) =
      y ⟨κ, c' κ⟩ ^ (-((τ : ℤ) * a κ)) * (y ⟨κ, c' κ⟩ ^ e κ)⁻¹ := by
    intro κ
    rw [← he κ, neg_add, zpow_add₀ (hc' κ), zpow_neg (y ⟨κ, c' κ⟩) (e κ : ℤ), zpow_natCast]
  have heq : (∏ κ, y ⟨κ, c κ⟩ ^ e κ) * s * ∏ κ, y ⟨κ, c' κ⟩ ^ (-((τ' : ℤ) * a' κ)) =
      (s * ∏ κ, y ⟨κ, c' κ⟩ ^ (-((τ : ℤ) * a κ))) * ∏ κ, (y ⟨κ, c κ⟩ / y ⟨κ, c' κ⟩) ^ e κ := by
    simp only [hk, div_pow, Finset.prod_mul_distrib, Finset.prod_div_distrib, Finset.prod_inv_distrib]
    ring
  rw [heq]
  refine Subalgebra.mul_mem _ (hs c' hc') (Subalgebra.prod_mem _ fun κ _ => Subalgebra.pow_mem _ ?_ _)
  exact (integralClosure (chartRingZ y c') Ω).algebraMap_mem ⟨_, hmem κ⟩

/- English proof (translation)
Introduce `K _ ι _ Ω _ y D a hvar hbir`. Establish `hy : ∀ κ, ∃ i, y ⟨κ, i⟩ ≠ 0`. Introduce `κ`. Take `⟨i, hi⟩` from `hvar.2.1.2.2 κ`. Use `⟨i, fun h0 => hi ?_⟩` and prove the remaining obligations.

Simplify using `[mCoordIdeal, RingHom.mem_ker, mConeMap, h0]`. Establish `hchar : CharZero Ω`. Use `charZero_of_inj_zero fun n hn => ?_` and prove the remaining obligations. Establish `hmem : (n : ℤ) ∈ (mCoordIdeal y).comap (C : ℤ →+* MRing ι)`. Simplify using `[mCoordIdeal, RingHom.mem_ker, mConeMap]`.

Rewrite using `[← map_natCast (MvPolynomial.C : Ω →+* MvPolynomial K Ω), hn, map_zero]`. Rewrite `hmem` using `[hvar.2.2.1, Ideal.mem_bot]`. Conclude with `hmem` after adjusting the coercions. Use `choose c hc using hy`. Use `set b : K → ℕ := fun κ => (a κ).toNat + 1 with hb`.

Establish `hb1 : ∀ κ, 1 ≤ b κ` using `fun κ => Nat.le_add_left 1 _`. Establish `hab : ∀ κ, a κ ≤ (b κ : ℤ)` using `fun κ => by simp only [hb]; push_cast; omega`. Take `⟨J, _, d, e, τ₁, -, hgen⟩` from `h₁ K ι Ω y b hb1 (fun κ => ⟨c κ, hc κ⟩) hbir 0`. Take `⟨hfin, C, hC0, hC⟩` from `h₂ K ι Ω y D b hvar hb1`. Establish `hbig : ∀ τ, τ₁ ≤ τ → Module.Finite ℤ (chartLatNm y (fun κ => (b κ : ℤ)) τ) ∧ (Module.finrank ℤ (chartLatNm y (fun κ => (b κ : ℤ)) τ) : ℝ) ≤ Fintype.card J * C * ((τ : ℝ) + 1) ^ D`.

Introduce `τ hτ`. Set `M : J → AddSubgroup Ω` to `fun j => secM y (fun κ => (τ - d j) * b κ)`. Set `Φ : (∀ j, M j) →ₗ[ℤ] Ω` to `∑ j, (LinearMap.mulRight ℤ (e j)).comp ((M j).subtype.toIntLinearMap.comp (LinearMap.proj j))`. Establish `hle : ∀ s ∈ chartLatNm y (fun κ => (b κ : ℤ)) τ, s ∈ LinearMap.range Φ`. Introduce `s hs`.

Take `⟨r, hr, rfl⟩` from `hgen τ hτ s hs`. Conclude with `⟨fun j => ⟨r j, hr j⟩, by simp [Φ, M]⟩`. Set `f : chartLatNm y (fun κ => (b κ : ℤ)) τ →ₗ[ℤ] LinearMap.range Φ` to `LinearMap.codRestrict _ (chartLatNm y (fun κ => (b κ : ℤ)) τ).subtype.toIntLinearMap (fun x => hle x x.2)`. Establish `hinj : Function.Injective f` using `fun x x' hxx => by`. Establish `h` using `congrArg Subtype.val hxx`.

Conclude with `Subtype.ext h`. Establish `: ∀ j, Module.Finite ℤ (M j)` using `fun j => hfin (τ - d j)`. Establish `: ∀ j, Module.IsTorsionFree ℤ (M j)` using `fun j => Function.Injective.moduleIsTorsionFree (M j).subtype Subtype.val_injective (fun _ _ => rfl)`. Use `⟨Module.Finite.of_injective f hinj, ?_⟩` and prove the remaining obligations. Establish `h1 : Module.finrank ℤ (chartLatNm y (fun κ => (b κ : ℤ)) τ) ≤ ∑ j, Module.finrank ℤ (M j)` using `(LinearMap.finrank_le_finrank_of_injective hinj).trans ((LinearMap.finrank_range_le Φ).trans_eq (Module.finrank_pi_fintype ℤ))`.

Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_le_sum fun j _ => (hC (τ - d j)).trans ?_` and prove the remaining obligations. Use `gcongr`. Conclude with `Nat.sub_le τ (d j)` after adjusting the coercions. Use `_ = Fintype.card J * C * ((τ : ℝ) + 1) ^ D := by`.

Rewrite using `[Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_assoc]`. Establish `hmap : ∀ τ, ∃ f : chartLatNm y a τ →ₗ[ℤ] chartLatNm y (fun κ => (b κ : ℤ)) (max τ τ₁), Function.Injective f`. Introduce `τ`. Use `set τ' := max τ τ₁`. Use `set ex : K → ℕ := fun κ => ((τ' : ℤ) * b κ - τ * a κ).toNat`.

Establish `hex : ∀ κ, (τ : ℤ) * a κ + ex κ = τ' * (b κ : ℤ)`. Introduce `κ`. Establish `h0 : (τ : ℤ) * a κ ≤ τ' * b κ`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [ex]`.

Rewrite using `[Int.toNat_of_nonneg (by linarith)]`. Expand and normalize the polynomial expressions, which then agree. Use `set u : Ω := ∏ κ, y ⟨κ, c κ⟩ ^ ex κ`. Establish `hu : u ≠ 0` using `Finset.prod_ne_zero_iff.mpr fun κ _ => pow_ne_zero _ (hc κ)`. Set `F : chartLatNm y a τ →+ chartLatNm y (fun κ => (b κ : ℤ)) τ'` to `((AddMonoidHom.mulLeft u).comp (chartLatNm y a τ).subtype).codRestrict _ (fun x => shift_mem y c a _ τ τ' ex hex x.2)`.

Use `⟨F.toIntLinearMap, fun x x' hxx => ?_⟩` and prove the remaining obligations. Establish `h : u * (x : Ω) = u * x'` using `congrArg Subtype.val hxx`. Conclude with `Subtype.ext (mul_left_cancel₀ hu h)`. Use `⟨fun τ => ?_, Fintype.card J * C * ((τ₁ : ℝ) + 1) ^ D, by positivity, fun τ => ?_⟩` and prove the remaining obligations. Take `⟨f, hf⟩` from `hmap τ`.

Use `(hbig (max τ τ₁) (le_max_right _ _)).1` as an intermediate fact. Conclude with `Module.Finite.of_injective f hf`. Take `⟨f, hf⟩` from `hmap τ`. Take `⟨hF, hR⟩` from `hbig (max τ τ₁) (le_max_right _ _)`. Establish `h1 : (Module.finrank ℤ (chartLatNm y a τ) : ℝ) ≤ Module.finrank ℤ (chartLatNm y (fun κ => (b κ : ℤ)) (max τ τ₁))`.

Conclude with `LinearMap.finrank_le_finrank_of_injective hf` after adjusting the coercions. Establish `h2 : ((max τ τ₁ : ℕ) : ℝ) + 1 ≤ ((τ₁ : ℝ) + 1) * ((τ : ℝ) + 1)`. Break down `le_total τ τ₁ with h | h` into its components or cases. Rewrite using `[max_eq_right h]`. Use polynomial arithmetic with `[(Nat.cast_nonneg τ : (0 : ℝ) ≤ τ), (Nat.cast_nonneg τ₁ : (0 : ℝ) ≤ τ₁)]`.

Rewrite using `[max_eq_left h]`. Use polynomial arithmetic with `[(Nat.cast_nonneg τ : (0 : ℝ) ≤ τ), (Nat.cast_nonneg τ₁ : (0 : ℝ) ≤ τ₁)]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem proof (h₁ : NmSectionsFinite.Statement) (h₂ : SecMRankBound.Statement) :
    NmSectionsRankBound.Statement := by
  intro K _ ι _ Ω _ y D a hvar hbir
  classical

  have hy : ∀ κ, ∃ i, y ⟨κ, i⟩ ≠ 0 := by
    intro κ
    obtain ⟨i, hi⟩ := hvar.2.1.2.2 κ
    refine ⟨i, fun h0 => hi ?_⟩
    simp [mCoordIdeal, RingHom.mem_ker, mConeMap, h0]

  have hchar : CharZero Ω := by
    refine charZero_of_inj_zero fun n hn => ?_
    have hmem : (n : ℤ) ∈ (mCoordIdeal y).comap (C : ℤ →+* MRing ι) := by
      simp [mCoordIdeal, RingHom.mem_ker, mConeMap]
      rw [← map_natCast (MvPolynomial.C : Ω →+* MvPolynomial K Ω), hn, map_zero]
    rw [hvar.2.2.1, Ideal.mem_bot] at hmem
    exact_mod_cast hmem
  choose c hc using hy
  set b : K → ℕ := fun κ => (a κ).toNat + 1 with hb
  have hb1 : ∀ κ, 1 ≤ b κ := fun κ => Nat.le_add_left 1 _
  have hab : ∀ κ, a κ ≤ (b κ : ℤ) := fun κ => by simp only [hb]; push_cast; omega
  obtain ⟨J, _, d, e, τ₁, -, hgen⟩ := h₁ K ι Ω y b hb1 (fun κ => ⟨c κ, hc κ⟩) hbir 0
  obtain ⟨hfin, C, hC0, hC⟩ := h₂ K ι Ω y D b hvar hb1

  have hbig : ∀ τ, τ₁ ≤ τ → Module.Finite ℤ (chartLatNm y (fun κ => (b κ : ℤ)) τ) ∧
      (Module.finrank ℤ (chartLatNm y (fun κ => (b κ : ℤ)) τ) : ℝ) ≤
        Fintype.card J * C * ((τ : ℝ) + 1) ^ D := by
    intro τ hτ
    let M : J → AddSubgroup Ω := fun j => secM y (fun κ => (τ - d j) * b κ)
    let Φ : (∀ j, M j) →ₗ[ℤ] Ω :=
      ∑ j, (LinearMap.mulRight ℤ (e j)).comp ((M j).subtype.toIntLinearMap.comp (LinearMap.proj j))
    have hle : ∀ s ∈ chartLatNm y (fun κ => (b κ : ℤ)) τ, s ∈ LinearMap.range Φ := by
      intro s hs
      obtain ⟨r, hr, rfl⟩ := hgen τ hτ s hs
      exact ⟨fun j => ⟨r j, hr j⟩, by simp [Φ, M]⟩
    let f : chartLatNm y (fun κ => (b κ : ℤ)) τ →ₗ[ℤ] LinearMap.range Φ :=
      LinearMap.codRestrict _ (chartLatNm y (fun κ => (b κ : ℤ)) τ).subtype.toIntLinearMap
        (fun x => hle x x.2)
    have hinj : Function.Injective f := fun x x' hxx => by
      have h := congrArg Subtype.val hxx
      exact Subtype.ext h
    have : ∀ j, Module.Finite ℤ (M j) := fun j => hfin (τ - d j)
    have : ∀ j, Module.IsTorsionFree ℤ (M j) := fun j =>
      Function.Injective.moduleIsTorsionFree (M j).subtype Subtype.val_injective (fun _ _ => rfl)
    refine ⟨Module.Finite.of_injective f hinj, ?_⟩
    have h1 : Module.finrank ℤ (chartLatNm y (fun κ => (b κ : ℤ)) τ) ≤ ∑ j, Module.finrank ℤ (M j) :=
      (LinearMap.finrank_le_finrank_of_injective hinj).trans
        ((LinearMap.finrank_range_le Φ).trans_eq (Module.finrank_pi_fintype ℤ))
    calc (Module.finrank ℤ (chartLatNm y (fun κ => (b κ : ℤ)) τ) : ℝ)
        ≤ ∑ j, (Module.finrank ℤ (M j) : ℝ) := by exact_mod_cast h1
      _ ≤ ∑ _j : J, C * ((τ : ℝ) + 1) ^ D := by
          refine Finset.sum_le_sum fun j _ => (hC (τ - d j)).trans ?_
          gcongr
          exact_mod_cast Nat.sub_le τ (d j)
      _ = Fintype.card J * C * ((τ : ℝ) + 1) ^ D := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_assoc]

  have hmap : ∀ τ, ∃ f : chartLatNm y a τ →ₗ[ℤ] chartLatNm y (fun κ => (b κ : ℤ)) (max τ τ₁),
      Function.Injective f := by
    intro τ
    set τ' := max τ τ₁
    set ex : K → ℕ := fun κ => ((τ' : ℤ) * b κ - τ * a κ).toNat
    have hex : ∀ κ, (τ : ℤ) * a κ + ex κ = τ' * (b κ : ℤ) := by
      intro κ
      have h0 : (τ : ℤ) * a κ ≤ τ' * b κ :=
        calc (τ : ℤ) * a κ ≤ τ * b κ := mul_le_mul_of_nonneg_left (hab κ) (by positivity)
          _ ≤ τ' * b κ := mul_le_mul_of_nonneg_right (by exact_mod_cast le_max_left τ τ₁) (by positivity)
      simp only [ex]
      rw [Int.toNat_of_nonneg (by linarith)]
      ring
    set u : Ω := ∏ κ, y ⟨κ, c κ⟩ ^ ex κ
    have hu : u ≠ 0 := Finset.prod_ne_zero_iff.mpr fun κ _ => pow_ne_zero _ (hc κ)
    let F : chartLatNm y a τ →+ chartLatNm y (fun κ => (b κ : ℤ)) τ' :=
      ((AddMonoidHom.mulLeft u).comp (chartLatNm y a τ).subtype).codRestrict _
        (fun x => shift_mem y c a _ τ τ' ex hex x.2)
    refine ⟨F.toIntLinearMap, fun x x' hxx => ?_⟩
    have h : u * (x : Ω) = u * x' := congrArg Subtype.val hxx
    exact Subtype.ext (mul_left_cancel₀ hu h)
  refine ⟨fun τ => ?_, Fintype.card J * C * ((τ₁ : ℝ) + 1) ^ D, by positivity, fun τ => ?_⟩
  · obtain ⟨f, hf⟩ := hmap τ
    have := (hbig (max τ τ₁) (le_max_right _ _)).1
    exact Module.Finite.of_injective f hf
  · obtain ⟨f, hf⟩ := hmap τ
    obtain ⟨hF, hR⟩ := hbig (max τ τ₁) (le_max_right _ _)
    have h1 : (Module.finrank ℤ (chartLatNm y a τ) : ℝ) ≤
        Module.finrank ℤ (chartLatNm y (fun κ => (b κ : ℤ)) (max τ τ₁)) := by
      exact_mod_cast LinearMap.finrank_le_finrank_of_injective hf
    have h2 : ((max τ τ₁ : ℕ) : ℝ) + 1 ≤ ((τ₁ : ℝ) + 1) * ((τ : ℝ) + 1) := by
      rcases le_total τ τ₁ with h | h
      · rw [max_eq_right h]; nlinarith [(Nat.cast_nonneg τ : (0 : ℝ) ≤ τ), (Nat.cast_nonneg τ₁ : (0 : ℝ) ≤ τ₁)]
      · rw [max_eq_left h]; nlinarith [(Nat.cast_nonneg τ : (0 : ℝ) ≤ τ), (Nat.cast_nonneg τ₁ : (0 : ℝ) ≤ τ₁)]
    calc (Module.finrank ℤ (chartLatNm y a τ) : ℝ)
        ≤ Fintype.card J * C * (((max τ τ₁ : ℕ) : ℝ) + 1) ^ D := h1.trans hR
      _ ≤ Fintype.card J * C * ((((τ₁ : ℝ) + 1) * ((τ : ℝ) + 1)) ^ D) := by
          gcongr
      _ = Fintype.card J * C * ((τ₁ : ℝ) + 1) ^ D * ((τ : ℝ) + 1) ^ D := by rw [mul_pow]; ring

end NmSectionsRankBound

end GroundTheory.Heights₂.Heights.HilbertSamuel
