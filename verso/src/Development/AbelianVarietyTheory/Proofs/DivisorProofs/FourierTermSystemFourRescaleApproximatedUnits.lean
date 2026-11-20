import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMemberP
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.VPre

/- English proof (translation)
Introduce `O _ bar q s W A _ _ Φ N₁ hF w hw (y₀ : Φ.Y) N₀`. Take `⟨N, hN0, hN1, k, hk0, hku, hmain⟩` from `hF y₀ N₀`. Use `⟨N, hN0, hN1, k, hk0, hku, ?_⟩` and prove the remaining obligations. Introduce `l a c e`. Take `⟨f, hf⟩` from `hmain l a c e`.

Take `⟨b, hb⟩` from `hw (e + 1)`. Establish `hmax : ∀ (y : Φ.Y) (x : A), x ∈ maximalIdeal A → Φ.ev y x ∈ maximalIdeal (Φ.V y)`. Introduce `y x hx`. Use `haveI := Φ.ev_loc y`. Rewrite using `[IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]`.

Introduce `hu`. Conclude with `(IsLocalRing.mem_maximalIdeal _ |>.mp hx) (isUnit_of_map_unit (Φ.ev y) x hu)`. Establish `hle : ∀ y : Φ.Y, (maximalIdeal A ^ (e + 1)).map (Φ.ev y) ≤ maximalIdeal (Φ.V y)`. Introduce `y`. Rewrite using `[Ideal.map_le_iff_le_comap]`.

Conclude with `le_trans (Ideal.pow_le_self (Nat.succ_ne_zero e)) (fun x hx => hmax y x hx)`. Establish `hbu : IsUnit b`. Assume the negation of the conclusion as `hn`. Establish `hbm : b ∈ maximalIdeal A` using `(IsLocalRing.mem_maximalIdeal _).mpr hn`. Establish `h1 : Φ.ev y₀ b ∈ maximalIdeal (Φ.V y₀)` using `hmax y₀ b hbm`.

Establish `h2` using `hle y₀ (hb y₀)`. Establish `h3 : (((w y₀)⁻¹ : (Φ.V y₀)ˣ) : Φ.V y₀) ∈ maximalIdeal (Φ.V y₀)`. Use `Ideal.sub_mem _ h1 h2` as an intermediate fact. Simplify using `using this`. Conclude with `(IsLocalRing.mem_maximalIdeal _ |>.mp h3) (Units.isUnit _)`.

Use `⟨f * ((hbu.unit⁻¹ : Aˣ) : A) ^ l, fun (y : Φ.Y) j => ?_⟩` and prove the remaining obligations. Take `⟨S, hS1, hS2, hS3⟩` from `hf y j`. Use `⟨S, hS1, hS2, ?_⟩` and prove the remaining obligations. Use `set J := maximalIdeal (Φ.V y) ^ j ⊔ (maximalIdeal A ^ e).map (Φ.ev y) with hJ`. Establish `hIe : (maximalIdeal A ^ (e + 1)).map (Φ.ev y) ≤ J` using `le_trans (Ideal.map_mono (Ideal.pow_le_pow_right (Nat.le_succ e))) le_sup_right`.

Use `set z : Φ.V y := Φ.ev y ((hbu.unit⁻¹ : Aˣ) : A) with hz`. Use `set ww : Φ.V y := ((w y : (Φ.V y)ˣ) : Φ.V y) with hww`. Establish `hzb : z * Φ.ev y b = 1`. Rewrite using `[hz, ← map_mul]`. Simplify using the standard rewrite rules.

Establish `hzw : z - ww ∈ J`. Apply `hIe` to reduce the goal to its premises. Establish `h` using `(hb y)`. Establish `hx : z - ww = -(z * ww * (Φ.ev y b - (((w y)⁻¹ : (Φ.V y)ˣ) : Φ.V y)))`. Establish `: ww * (((w y)⁻¹ : (Φ.V y)ˣ) : Φ.V y) = 1` using `by simp [hww]`.

Take the linear combination `ww * hzb - z * this`. Rewrite using `[hx]`. Conclude with `neg_mem (Ideal.mul_mem_left _ _ h)`. Establish `hprod : ∀ mu : Fin l × Fin s → Φ.X y, (∏ i, (Φ.u y (fun x => mu (i, x)) (c i) * ww) * mono W (Φ.t y) (Φ.δ y) (fun x => mu (i, x))) = (∏ i, Φ.u y (fun x => mu (i, x)) (c i) * mono W (Φ.t y) (Φ.δ y) (fun x => mu (i, x))) * ww ^ l`. Introduce `mu`.

Rewrite using `[show (fun i => Φ.u y (fun x => mu (i, x)) (c i) * ww * mono W (Φ.t y) (Φ.δ y) (fun x => mu (i, x))) = fun i => (Φ.u y (fun x => mu (i, x)) (c i) * mono W (Φ.t y) (Φ.δ y) (fun x => mu (i, x))) * ww from`. Use function extensionality and compare the values at `fun i => by ring]`. Rewrite using `[Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]`. Use `show Φ.ev y (f * ((hbu.unit⁻¹ : Aˣ) : A) ^ l) - ∑ mu ∈ S, (∏ i, (Φ.u y (fun x => mu (i, x)) (c i) * ww) * mono W (Φ.t y) (Φ.δ y) (fun x => mu (i, x))) ∈ J`. Repeatedly rewrite using `[hprod]`.

Rewrite using `[← Finset.sum_mul, map_mul, map_pow, ← hz]`. Use `set P := ∑ mu ∈ S, ∏ i, Φ.u y (fun x => mu (i, x)) (c i) * mono W (Φ.t y) (Φ.δ y) (fun x => mu (i, x))`. Establish `hd : z ^ l - ww ^ l ∈ J`. Take `⟨r, hr⟩` from `sub_dvd_pow_sub_pow z ww l`. Rewrite using `[hr]`.

Conclude with `Ideal.mul_mem_right _ _ hzw`. Establish `: Φ.ev y f * z ^ l - P * ww ^ l = z ^ l * (Φ.ev y f - P) + P * (z ^ l - ww ^ l)` using `by ring`. Rewrite using `[this]`. Conclude with `Ideal.add_mem _ (Ideal.mul_mem_left _ _ hS3) (Ideal.mul_mem_left _ _ hd)`.
-/
theorem four_rescale : ∀ (O : Type) [CommRing O] (bar : O → O) (q s : ℕ) (W : Matrix (Fin s) (Fin s) ℤ) (A : Type) [CommRing A] [IsLocalRing A] (Φ : VPre bar q W A) (N₁ : ℕ), Φ.Four N₁ → ∀ v : ∀ y, (Φ.V y)ˣ, (∀ e : ℕ, ∃ a : A, ∀ y, Φ.ev y a - ((v y)⁻¹ : (Φ.V y)ˣ) ∈ (maximalIdeal A ^ e).map (Φ.ev y)) → (Φ.rescale v).Four N₁ := by
  intro O _ bar q s W A _ _ Φ N₁ hF w hw (y₀ : Φ.Y) N₀
  obtain ⟨N, hN0, hN1, k, hk0, hku, hmain⟩ := hF y₀ N₀
  refine ⟨N, hN0, hN1, k, hk0, hku, ?_⟩
  intro l a c e
  obtain ⟨f, hf⟩ := hmain l a c e
  obtain ⟨b, hb⟩ := hw (e + 1)

  have hmax : ∀ (y : Φ.Y) (x : A), x ∈ maximalIdeal A → Φ.ev y x ∈ maximalIdeal (Φ.V y) := by
    intro y x hx
    haveI := Φ.ev_loc y
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    exact (IsLocalRing.mem_maximalIdeal _ |>.mp hx) (isUnit_of_map_unit (Φ.ev y) x hu)
  have hle : ∀ y : Φ.Y, (maximalIdeal A ^ (e + 1)).map (Φ.ev y) ≤ maximalIdeal (Φ.V y) := by
    intro y
    rw [Ideal.map_le_iff_le_comap]
    exact le_trans (Ideal.pow_le_self (Nat.succ_ne_zero e)) (fun x hx => hmax y x hx)
  have hbu : IsUnit b := by
    by_contra hn
    have hbm : b ∈ maximalIdeal A := (IsLocalRing.mem_maximalIdeal _).mpr hn
    have h1 : Φ.ev y₀ b ∈ maximalIdeal (Φ.V y₀) := hmax y₀ b hbm
    have h2 := hle y₀ (hb y₀)
    have h3 : (((w y₀)⁻¹ : (Φ.V y₀)ˣ) : Φ.V y₀) ∈ maximalIdeal (Φ.V y₀) := by
      have := Ideal.sub_mem _ h1 h2
      simpa using this
    exact (IsLocalRing.mem_maximalIdeal _ |>.mp h3) (Units.isUnit _)
  refine ⟨f * ((hbu.unit⁻¹ : Aˣ) : A) ^ l, fun (y : Φ.Y) j => ?_⟩
  obtain ⟨S, hS1, hS2, hS3⟩ := hf y j
  refine ⟨S, hS1, hS2, ?_⟩
  set J := maximalIdeal (Φ.V y) ^ j ⊔ (maximalIdeal A ^ e).map (Φ.ev y) with hJ
  have hIe : (maximalIdeal A ^ (e + 1)).map (Φ.ev y) ≤ J :=
    le_trans (Ideal.map_mono (Ideal.pow_le_pow_right (Nat.le_succ e))) le_sup_right
  set z : Φ.V y := Φ.ev y ((hbu.unit⁻¹ : Aˣ) : A) with hz
  set ww : Φ.V y := ((w y : (Φ.V y)ˣ) : Φ.V y) with hww
  have hzb : z * Φ.ev y b = 1 := by
    rw [hz, ← map_mul]
    simp
  have hzw : z - ww ∈ J := by
    apply hIe
    have h := (hb y)
    have hx : z - ww = -(z * ww * (Φ.ev y b - (((w y)⁻¹ : (Φ.V y)ˣ) : Φ.V y))) := by
      have : ww * (((w y)⁻¹ : (Φ.V y)ˣ) : Φ.V y) = 1 := by simp [hww]
      linear_combination ww * hzb - z * this
    rw [hx]
    exact neg_mem (Ideal.mul_mem_left _ _ h)
  have hprod : ∀ mu : Fin l × Fin s → Φ.X y,
      (∏ i, (Φ.u y (fun x => mu (i, x)) (c i) * ww) * mono W (Φ.t y) (Φ.δ y) (fun x => mu (i, x)))
        = (∏ i, Φ.u y (fun x => mu (i, x)) (c i) * mono W (Φ.t y) (Φ.δ y) (fun x => mu (i, x))) * ww ^ l := by
    intro mu
    rw [show (fun i => Φ.u y (fun x => mu (i, x)) (c i) * ww * mono W (Φ.t y) (Φ.δ y) (fun x => mu (i, x)))
        = fun i => (Φ.u y (fun x => mu (i, x)) (c i) * mono W (Φ.t y) (Φ.δ y) (fun x => mu (i, x))) * ww from
        funext fun i => by ring]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  show Φ.ev y (f * ((hbu.unit⁻¹ : Aˣ) : A) ^ l) - ∑ mu ∈ S, (∏ i, (Φ.u y (fun x => mu (i, x)) (c i) * ww) * mono W (Φ.t y) (Φ.δ y) (fun x => mu (i, x))) ∈ J
  simp_rw [hprod]
  rw [← Finset.sum_mul, map_mul, map_pow, ← hz]
  set P := ∑ mu ∈ S, ∏ i, Φ.u y (fun x => mu (i, x)) (c i) * mono W (Φ.t y) (Φ.δ y) (fun x => mu (i, x))
  have hd : z ^ l - ww ^ l ∈ J := by
    obtain ⟨r, hr⟩ := sub_dvd_pow_sub_pow z ww l
    rw [hr]
    exact Ideal.mul_mem_right _ _ hzw
  have : Φ.ev y f * z ^ l - P * ww ^ l = z ^ l * (Φ.ev y f - P) + P * (z ^ l - ww ^ l) := by ring
  rw [this]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hS3) (Ideal.mul_mem_left _ _ hd)

end GlobalTheory.Poinc.VPre
