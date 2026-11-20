import Mathlib
import GroundTheory.PAdicHodge.ExistsWeightLeOfConvergesAt
import GroundTheory.PAdicHodge.ExtRobbaDMSplit
set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false

namespace GroundTheory.PAdicHodge

open Laurent Filter Topology UniformSpace

namespace TeichLift

variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] (T : TeichLift p L Γ)

def lowerPart (b : T.B) : T.B :=
  algebraMap Γ T.B (T.partialSum (T.num b) (T.den b)) * IsLocalization.Away.invSelf T.π ^ T.den b

def upperPart (b : T.B) : T.B :=
  algebraMap Γ T.B (T.num b - T.partialSum (T.num b) (T.den b)) *
    IsLocalization.Away.invSelf T.π ^ T.den b

/- English proof (translation)
Rewrite using `[lowerPart, upperPart, ← add_mul, ← map_add, add_sub_cancel, ← T.eq_num_mul]`.
-/
theorem lowerPart_add_upperPart (b : T.B) : T.lowerPart b + T.upperPart b = b := by
  rw [lowerPart, upperPart, ← add_mul, ← map_add, add_sub_cancel, ← T.eq_num_mul]

/- English proof (translation)
Rewrite using `[lowerPart, T.coeffB_eq (T.mul_pow_eq_of_invSelf _), T.coeffB_eq (T.num_spec b)]`. Simplify using `only`. Break down `lt_or_ge (n + T.den b) 0 with h | h` into its components or cases. Rewrite using `[T.zcoeff_of_neg _ h, T.zcoeff_of_neg _ h]`. Simplify using the standard rewrite rules.

Use `lift n + T.den b to ℕ using h with k hk`. Rewrite using `[zcoeff_natCast, zcoeff_natCast, partialSum, coeff_finSum]`. Distinguish the cases in `hn : n < 0`. Rewrite using `[if_pos (by omega), if_pos hn]`. Rewrite using `[if_neg (by omega), if_neg hn]`.
-/
theorem coeffB_lowerPart (b : T.B) (n : ℤ) :
    T.coeffB (T.lowerPart b) n = if n < 0 then T.coeffB b n else 0 := by
  rw [lowerPart, T.coeffB_eq (T.mul_pow_eq_of_invSelf _), T.coeffB_eq (T.num_spec b)]
  simp only
  rcases lt_or_ge (n + T.den b) 0 with h | h
  · rw [T.zcoeff_of_neg _ h, T.zcoeff_of_neg _ h]; simp
  · lift n + T.den b to ℕ using h with k hk
    rw [zcoeff_natCast, zcoeff_natCast, partialSum, coeff_finSum]
    by_cases hn : n < 0
    · rw [if_pos (by omega), if_pos hn]
    · rw [if_neg (by omega), if_neg hn]

/- English proof (translation)
Rewrite using `[upperPart, T.coeffB_eq (T.mul_pow_eq_of_invSelf _), T.coeffB_eq (T.num_spec b)]`. Simplify using `only`. Break down `lt_or_ge (n + T.den b) 0 with h | h` into its components or cases. Rewrite using `[T.zcoeff_of_neg _ h, T.zcoeff_of_neg _ h]`. Simplify using the standard rewrite rules.

Use `lift n + T.den b to ℕ using h with k hk`. Rewrite using `[zcoeff_natCast, zcoeff_natCast, coeff_sub_partialSum]`. Distinguish the cases in `hn : n < 0`. Rewrite using `[if_pos (by omega), if_pos hn]`. Rewrite using `[if_neg (by omega), if_neg hn]`.
-/
theorem coeffB_upperPart (b : T.B) (n : ℤ) :
    T.coeffB (T.upperPart b) n = if n < 0 then 0 else T.coeffB b n := by
  rw [upperPart, T.coeffB_eq (T.mul_pow_eq_of_invSelf _), T.coeffB_eq (T.num_spec b)]
  simp only
  rcases lt_or_ge (n + T.den b) 0 with h | h
  · rw [T.zcoeff_of_neg _ h, T.zcoeff_of_neg _ h]; simp
  · lift n + T.den b to ℕ using h with k hk
    rw [zcoeff_natCast, zcoeff_natCast, coeff_sub_partialSum]
    by_cases hn : n < 0
    · rw [if_pos (by omega), if_pos hn]
    · rw [if_neg (by omega), if_neg hn]

/- English proof (translation)
Apply the tactic sequence `rw [coeffB_lowerPart]; split_ifs <;> simp`.
-/
theorem norm_coeffB_lowerPart_le (b : T.B) (n : ℤ) :
    ‖T.coeffB (T.lowerPart b) n‖ ≤ ‖T.coeffB b n‖ := by
  rw [coeffB_lowerPart]; split_ifs <;> simp

/- English proof (translation)
Apply the tactic sequence `rw [coeffB_upperPart]; split_ifs <;> simp`.
-/
theorem norm_coeffB_upperPart_le (b : T.B) (n : ℤ) :
    ‖T.coeffB (T.upperPart b) n‖ ≤ ‖T.coeffB b n‖ := by
  rw [coeffB_upperPart]; split_ifs <;> simp

variable {T}

/- English proof (translation)
Introduce `ρ h0 h1` and use `(convergesAt_of_norm_le h0 (T.norm_coeffB_lowerPart_le b) (hb ρ h0 h1)).1`.
-/
theorem ConvAll.lowerPart {b : T.B} (hb : T.ConvAll b) : T.ConvAll (T.lowerPart b) :=
  fun ρ h0 h1 => (convergesAt_of_norm_le h0 (T.norm_coeffB_lowerPart_le b) (hb ρ h0 h1)).1

/- English proof (translation)
Introduce `ρ h0 h1` and use `(convergesAt_of_norm_le h0 (T.norm_coeffB_upperPart_le b) (hb ρ h0 h1)).1`.
-/
theorem ConvAll.upperPart {b : T.B} (hb : T.ConvAll b) : T.ConvAll (T.upperPart b) :=
  fun ρ h0 h1 => (convergesAt_of_norm_le h0 (T.norm_coeffB_upperPart_le b) (hb ρ h0 h1)).1

/- English proof (translation)
Use `gaussNorm_le fun n => ?_` and prove the remaining obligations. Rewrite using `[coeffB_lowerPart]`. Use `split_ifs with hn`. Establish `h3 : r ^ n ≤ r' ^ n`. Rewrite using `[show r ^ n = (r ^ (-n))⁻¹ by rw [zpow_neg, inv_inv], show r' ^ n = (r' ^ (-n))⁻¹ by rw [zpow_neg, inv_inv]]`.

Conclude with `inv_anti₀ (by positivity) (zpow_le_zpow_left₀ (by omega) h0.le hle)`. Conclude with `(mul_le_mul_of_nonneg_left h3 (norm_nonneg _)).trans ((hb r' h0 h1).le_gaussNorm n)`. Rewrite using `[norm_zero, zero_mul]`. Conclude with `gaussNorm_nonneg h0`.
-/
theorem gaussNorm_lowerPart_le {b : T.B} (hb : T.ConvAll b) {r r' : ℝ} (h0 : 0 < r')
    (hle : r' ≤ r) (h1 : r' < 1) :
    gaussNorm (T.coeffB (T.lowerPart b)) r ≤ gaussNorm (T.coeffB b) r' := by
  refine gaussNorm_le fun n => ?_
  rw [coeffB_lowerPart]
  split_ifs with hn
  · have h3 : r ^ n ≤ r' ^ n := by
      rw [show r ^ n = (r ^ (-n))⁻¹ by rw [zpow_neg, inv_inv],
        show r' ^ n = (r' ^ (-n))⁻¹ by rw [zpow_neg, inv_inv]]
      exact inv_anti₀ (by positivity) (zpow_le_zpow_left₀ (by omega) h0.le hle)
    exact (mul_le_mul_of_nonneg_left h3 (norm_nonneg _)).trans ((hb r' h0 h1).le_gaussNorm n)
  · rw [norm_zero, zero_mul]; exact gaussNorm_nonneg h0

/- English proof (translation)
Use `gaussNorm_le fun n => ?_` and prove the remaining obligations. Rewrite using `[coeffB_upperPart]`. Use `split_ifs with hn`. Rewrite using `[norm_zero, zero_mul]`. Conclude with `gaussNorm_nonneg (h0.trans_le hle)`.

Conclude with `(mul_le_mul_of_nonneg_left (zpow_le_zpow_left₀ (by omega) h0.le hle) (norm_nonneg _)).trans ((hb r' (h0.trans_le hle) h1).le_gaussNorm n)`.
-/
theorem gaussNorm_upperPart_le {b : T.B} (hb : T.ConvAll b) {r r' : ℝ} (h0 : 0 < r)
    (hle : r ≤ r') (h1 : r' < 1) :
    gaussNorm (T.coeffB (T.upperPart b)) r ≤ gaussNorm (T.coeffB b) r' := by
  refine gaussNorm_le fun n => ?_
  rw [coeffB_upperPart]
  split_ifs with hn
  · rw [norm_zero, zero_mul]; exact gaussNorm_nonneg (h0.trans_le hle)
  · exact (mul_le_mul_of_nonneg_left (zpow_le_zpow_left₀ (by omega) h0.le hle)
      (norm_nonneg _)).trans ((hb r' (h0.trans_le hle) h1).le_gaussNorm n)

end TeichLift

end GroundTheory.PAdicHodge

namespace GroundTheory.PAdicHodge

open Laurent Filter Topology UniformSpace

namespace TeichLift

variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] {T : TeichLift p L Γ}

/- English proof (translation)
The claim follows from `(T.extNorm_add_le ρ _ _).trans (max_le ((T.extNorm_add_le ρ _ _).trans (max_le_max le_rfl (le_max_left _ _))) (le_max_of_le_right (le_max_right _ _)))`.
-/
theorem extNorm_add_add_le_max {σ : Set.Ioo (0 : ℝ) 1} (ρ : Set.Ioc (0 : ℝ) σ) (a b c : T.RobbaExt σ) :
    T.extNorm σ ρ (a + b + c) ≤ max (T.extNorm σ ρ a) (max (T.extNorm σ ρ b) (T.extNorm σ ρ c)) :=
  (T.extNorm_add_le ρ _ _).trans (max_le ((T.extNorm_add_le ρ _ _).trans
    (max_le_max le_rfl (le_max_left _ _))) (le_max_of_le_right (le_max_right _ _)))

/- English proof (translation)
Rewrite using `[← ofAll_sub ha hb, extNorm_ofAll]`.
-/
theorem gaussNorm_ofAll_sub {a b : T.B} (ha : T.ConvAll a) (hb : T.ConvAll b)
    {σ : Set.Ioo (0 : ℝ) 1} (ρ : Set.Ioc (0 : ℝ) σ) :
    gaussNorm (T.coeffB (a - b)) ρ = T.extNorm σ ρ (T.ofAll a ha σ - T.ofAll b hb σ) := by
  rw [← ofAll_sub ha hb, extNorm_ofAll]

/- English proof (translation)
Establish `hex : ∃ t, (r (t + 1) : ℝ) < ρ`. Use `((tendsto_add_atTop_iff_nat 1).2 hr0).eventually (gt_mem_nhds hρ0)` as an intermediate fact. Conclude with `this.exists`. Use `⟨Nat.find hex, (Nat.find_spec hex).le, ?_⟩` and prove the remaining obligations. Break down `h : Nat.find hex with _ | s` into its components or cases.

Conclude with `hρ`. Use `Nat.find_min hex (show s < Nat.find hex by omega)` as an intermediate fact. Conclude with `not_lt.1 this`.
-/
theorem exists_mem_annulus (r : ℕ → Set.Ioo (0 : ℝ) 1) (hr0 : Tendsto (fun t => (r t : ℝ)) atTop (𝓝 0))
    {ρ : ℝ} (hρ0 : 0 < ρ) (hρ : ρ ≤ r 0) : ∃ s, (r (s + 1) : ℝ) ≤ ρ ∧ ρ ≤ r s := by
  classical
  have hex : ∃ t, (r (t + 1) : ℝ) < ρ := by
    have := ((tendsto_add_atTop_iff_nat 1).2 hr0).eventually (gt_mem_nhds hρ0)
    exact this.exists
  refine ⟨Nat.find hex, (Nat.find_spec hex).le, ?_⟩
  rcases h : Nat.find hex with _ | s
  · exact hρ
  · have := Nat.find_min hex (show s < Nat.find hex by omega)
    exact not_lt.1 this

/- English proof (translation)
Establish `hanti : Antitone fun t => (r t : ℝ)` using `antitone_nat_of_succ_le hr`. Establish `hhalf : ∀ J : ℕ, (0 : ℝ) < (1 / 2) ^ J` using `fun J => by positivity`. Establish `hhalf_le : ∀ ε > (0 : ℝ), ∃ J₀ : ℕ, ∀ J ≥ J₀, ((1 : ℝ) / 2) ^ J ≤ ε`. Introduce `ε hε`. Take `⟨J₀, hJ₀⟩` from `exists_pow_lt_of_lt_one hε (by norm_num : (1 / 2 : ℝ) < 1)`.

Conclude with `⟨J₀, fun J hJ => (pow_le_pow_of_le_one (by norm_num) (by norm_num) hJ).trans hJ₀.le⟩`. Use `choose d hdc hdx using fun (t J : ℕ) => exists_approx_convAll (x t J) (⟨r (t + 1), (r (t + 1)).2.1, hr t⟩ : Set.Ioc (0 : ℝ) (r t)) (hhalf J)`. Establish `hdC : ∀ t, ∀ ε > 0, ∃ J₀, ∀ J ≥ J₀, ∀ K ≥ J₀, ∀ ρ : Set.Ioc (0 : ℝ) (r t), (r (t + 1) : ℝ) ≤ ρ → gaussNorm (T.coeffB (d t J - d t K)) ρ ≤ ε`. Introduce `t ε hε`. Take `⟨J₁, hJ₁⟩` from `hC t ε hε`.

Take `⟨J₂, hJ₂⟩` from `hhalf_le ε hε`. Use `⟨max J₁ J₂, fun J hJ K hK ρ hρ => ?_⟩` and prove the remaining obligations. Rewrite using `[gaussNorm_ofAll_sub (hdc t J) (hdc t K)]`. Establish `e : T.ofAll (d t J) (hdc t J) (r t) - T.ofAll (d t K) (hdc t K) (r t) = -(x t J - T.ofAll (d t J) (hdc t J) (r t)) + (x t J - x t K) + (x t K - T.ofAll (d t K) (hdc t K) (r t))` using `by ring`. Rewrite using `[e]`.

Use `(extNorm_add_add_le_max ρ _ _ _).trans (max_le ?_ (max_le ?_ ?_))` and prove the remaining obligations. Rewrite using `[extNorm_neg]`. Conclude with `(hdx t J ρ hρ).trans (hJ₂ J (le_of_max_le_right hJ))`. Take `⟨h1, h2⟩` from `hJ₁ J (le_of_max_le_left hJ) K (le_of_max_le_left hK)`. Conclude with `(T.extNorm_le_max _ (topRad (r t)) ρ hρ ρ.2.2 _).trans (max_le h2 h1)`.

Conclude with `(hdx t K ρ hρ).trans (hJ₂ K (le_of_max_le_right hK))`. Use `set δ : ℕ → ℕ → T.B := fun t J => d t J - d (t + 1) J with hδdef`. Establish `hδc : ∀ t J, T.ConvAll (δ t J)` using `fun t J => (hdc t J).sub (hdc (t + 1) J)`. Establish `hδ : ∀ t, ∀ ε > 0, ∀ᶠ J in atTop, gaussNorm (T.coeffB (δ t J)) (r (t + 1)) ≤ ε`. Introduce `t ε hε`.

Take `⟨J₁, hJ₁⟩` from `hD t ε hε`. Take `⟨J₂, hJ₂⟩` from `hhalf_le ε hε`. Use `eventually_atTop.2 ⟨max J₁ J₂, fun J hJ => ?_⟩` and prove the remaining obligations. Rewrite using `[show (r (t + 1) : ℝ) = ((topRad (r (t + 1)) : Set.Ioc (0 : ℝ) (r (t + 1))) : ℝ) from rfl, gaussNorm_ofAll_sub (hdc t J) (hdc (t + 1) J)]`. Establish `e : T.ofAll (d t J) (hdc t J) (r (t + 1)) - T.ofAll (d (t + 1) J) (hdc (t + 1) J) (r (t + 1)) = -T.res (hr t) (x t J - T.ofAll (d t J) (hdc t J) (r t)) + (T.res (hr t) (x t J) - x (t + 1) J) + (x (t + 1) J - T.ofAll (d (t + 1) J) (hdc (t + 1) J) (r (t + 1)))`.

Rewrite using `[map_sub, res_ofAll]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Use `(extNorm_add_add_le_max _ _ _ _).trans (max_le ?_ (max_le (hJ₁ J (le_of_max_le_left hJ)) ?_))` and prove the remaining obligations. Rewrite using `[extNorm_neg, extNorm_res]`.

Conclude with `(hdx t J _ le_rfl).trans (hJ₂ J (le_of_max_le_right hJ))`. Conclude with `(hdx (t + 1) J _ (hr (t + 1))).trans (hJ₂ J (le_of_max_le_right hJ))`. Establish `hsel : ∀ k : ℕ, ∃ J, k ≤ J ∧ ∀ t < k, gaussNorm (T.coeffB (δ t J)) (r (t + 1)) ≤ (1 / 2) ^ k`. Introduce `k`. Establish `h1 : ∀ᶠ J in atTop, ∀ t ∈ Finset.range k, gaussNorm (T.coeffB (δ t J)) (r (t + 1)) ≤ (1 / 2) ^ k` using `(Finset.range k).eventually_all.2 fun t _ => hδ t _ (hhalf k)`.

Take `⟨J, hJ1, hJ2⟩` from `((eventually_ge_atTop k).and h1).exists`. Conclude with `⟨J, hJ1, fun t ht => hJ2 t (Finset.mem_range.2 ht)⟩`. Use `choose Jk hJk hJδ using hsel`. Use `set G : ℕ → T.B := fun k => d 0 (Jk k) - ∑ t ∈ Finset.range k, T.lowerPart (δ t (Jk k)) with hGdef`. Establish `hGc : ∀ k, T.ConvAll (G k)` using `fun k => (hdc 0 (Jk k)).sub (convAll_sum _ _ fun t _ => (hδc t (Jk k)).lowerPart)`.

Establish `hkey : ∀ s k, s ≤ k → ∀ ρ : ℝ, (r (s + 1) : ℝ) ≤ ρ → ρ ≤ r s → gaussNorm (T.coeffB (G k - d s (Jk k))) ρ ≤ (1 / 2) ^ k`. Introduce `s k hsk ρ hρ1 hρ2`. Use `set J := Jk k`. Establish `hρ0 : 0 < ρ` using `(r (s + 1)).2.1.trans_le hρ1`. Establish `hρ1' : ρ < 1` using `hρ2.trans_lt (r s).2.2`.

Establish `h1 : ∑ t ∈ Finset.range s, δ t J = d 0 J - d s J` using `Finset.sum_range_sub' (fun t => d t J) s`. Establish `h2` using `Finset.sum_range_add_sum_Ico (fun t => T.lowerPart (δ t J)) hsk`. Establish `h3 : ∀ t, T.upperPart (δ t J) = δ t J - T.lowerPart (δ t J)` using `fun t => eq_sub_of_add_eq' (T.lowerPart_add_upperPart _)`. Establish `e : G k - d s J = ∑ t ∈ Finset.range s, T.upperPart (δ t J) - ∑ t ∈ Finset.Ico s k, T.lowerPart (δ t J)`. Rewrite using `[Finset.sum_congr rfl (fun t _ => h3 t), Finset.sum_sub_distrib, h1, hGdef]`.

Simplify using `only`. Rewrite using `[← h2]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, sub_eq_add_neg]`. Establish `hU` using `T.gaussNorm_finsetSum_le (Finset.range s) (fun t => T.upperPart (δ t J)) hρ0 hρ1' (hhalf k).le fun t ht => by`.

Establish `ht'` using `Finset.mem_range.1 ht`. Use `⟨(hδc t J).upperPart ρ hρ0 hρ1', ?_⟩` and prove the remaining obligations. Establish `hle : ρ ≤ r (t + 1)` using `hρ2.trans (hanti (show t + 1 ≤ s by omega))`. Conclude with `(gaussNorm_upperPart_le (hδc t J) hρ0 hle (r (t + 1)).2.2).trans (hJδ k t (by omega))`. Establish `hL` using `T.gaussNorm_finsetSum_le (Finset.Ico s k) (fun t => T.lowerPart (δ t J)) hρ0 hρ1' (hhalf k).le fun t ht => by`.

Establish `ht'` using `Finset.mem_Ico.1 ht`. Use `⟨(hδc t J).lowerPart ρ hρ0 hρ1', ?_⟩` and prove the remaining obligations. Establish `hle : (r (t + 1) : ℝ) ≤ ρ` using `(hanti (show s + 1 ≤ t + 1 by omega)).trans hρ1`. Conclude with `(gaussNorm_lowerPart_le (hδc t J) (r (t + 1)).2.1 hle (r (t + 1)).2.2).trans (hJδ k t ht'.2)`. Take `⟨hLn1, hLn2⟩` from `T.convergesAt_coeffB_neg hρ0 hρ1' hL.1`.

Use `(T.convergesAt_coeffB_add hρ0 hρ1' hU.1 hLn1).2.trans (max_le hU.2 ?_)` and prove the remaining obligations. Rewrite using `[hLn2]`. Conclude with `hL.2`. Establish `hGC : ∀ ρ : Set.Ioc (0 : ℝ) (r 0), ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N, gaussNorm (T.coeffB (G m - G n)) ρ < ε`. Introduce `ρ ε hε`.

Take `⟨s, hs1, hs2⟩` from `exists_mem_annulus r hr0 ρ.2.1 ρ.2.2`. Take `⟨J₁, hJ₁⟩` from `hdC s (ε / 2) (half_pos hε)`. Take `⟨J₂, hJ₂⟩` from `hhalf_le (ε / 2) (half_pos hε)`. Use `⟨max s (max J₁ J₂), fun m hm n hn => ?_⟩` and prove the remaining obligations. Establish `hρ0 : (0 : ℝ) < ρ` using `ρ.2.1`.

Establish `hρ1 : (ρ : ℝ) < 1` using `rad_lt_one (r 0) ρ`. Establish `e : G m - G n = (G m - d s (Jk m)) + (d s (Jk m) - d s (Jk n)) + -(G n - d s (Jk n))`. Expand and normalize the polynomial expressions, which then agree. Establish `c1` using `hkey s m (le_of_max_le_left hm) ρ hs1 hs2`. Establish `c2` using `hkey s n (le_of_max_le_left hn) ρ hs1 hs2`.

Establish `hmJ : J₁ ≤ Jk m` using `(le_of_max_le_left (le_of_max_le_right hm)).trans (hJk m)`. Establish `hnJ : J₁ ≤ Jk n` using `(le_of_max_le_left (le_of_max_le_right hn)).trans (hJk n)`. Establish `c4` using `hJ₁ (Jk m) hmJ (Jk n) hnJ ⟨ρ, ρ.2.1, hs2⟩ hs1`. Establish `hm2` using `hJ₂ m (le_of_max_le_right (le_of_max_le_right hm))`. Establish `hn2` using `hJ₂ n (le_of_max_le_right (le_of_max_le_right hn))`.

Establish `cv : ∀ b : T.B, T.ConvAll b → ConvergesAt (T.coeffB b) ρ` using `fun b hb => hb ρ hρ0 hρ1`. Establish `hA` using `T.convergesAt_coeffB_add hρ0 hρ1 (cv (G m - d s (Jk m)) ((hGc m).sub (hdc s _))) (cv (d s (Jk m) - d s (Jk n)) ((hdc s _).sub (hdc s _)))`. Take `⟨hN1, hN2⟩` from `T.convergesAt_coeffB_neg hρ0 hρ1 (cv (G n - d s (Jk n)) ((hGc n).sub (hdc s _)))`. Establish `hB` using `T.convergesAt_coeffB_add hρ0 hρ1 hA.1 hN1`. Rewrite using `[e]`.

Use `lt_of_le_of_lt (hB.2.trans (max_le (hA.2.trans (max_le (c1.trans hm2) c4)) ?_)) (half_lt_self hε)` and prove the remaining obligations. Rewrite using `[hN2]`. Conclude with `c2.trans hn2`. Take `⟨g, hg⟩` from `exists_tendsto_of_gaussNorm (T := T) (σ := r 0) (fun k => ⟨G k, hGc k (r 0) (r 0).2.1 (r 0).2.2⟩) hGC`. Use `⟨g, fun ε hε => ?_⟩` and prove the remaining obligations.

Establish `hgk : ∀ ρ : Set.Ioc (0 : ℝ) (r 0), ∀ᶠ k in atTop, T.extNorm (r 0) ρ (g - T.ofAll (G k) (hGc k) (r 0)) ≤ ε`. Introduce `ρ`. Establish `h1 : Tendsto (fun k => T.extNorm (r 0) ρ (g - T.ofAll (G k) (hGc k) (r 0))) atTop (𝓝 (T.extNorm (r 0) ρ (g - g)))` using `((T.continuous_extNorm ρ).tendsto _).comp (tendsto_const_nhds.sub hg)`. Rewrite `h1` using `[sub_self, extNorm_zero]`. Conclude with `h1.eventually (ge_mem_nhds hε)`.

Take `⟨J₁, hJ₁⟩` from `hdC 0 ε hε`. Take `⟨J₂, hJ₂⟩` from `hhalf_le ε hε`. Take `⟨k, hk1, hk2, hk3, hk4⟩` from `((eventually_ge_atTop J₁).and ((eventually_ge_atTop J₂).and ((hgk (topRad (r 0))).and (hgk ⟨r 1, (r 1).2.1, hr 0⟩)))).exists`. Establish `hbound : ∀ ρ : Set.Ioc (0 : ℝ) (r 0), (r 1 : ℝ) ≤ ρ → T.extNorm (r 0) ρ (g - T.ofAll (G k) (hGc k) (r 0)) ≤ ε → ∀ J ≥ max J₁ J₂, T.extNorm (r 0) ρ (g - x 0 J) ≤ ε`. Introduce `ρ hρ hgρ J hJ`.

Establish `e : g - x 0 J = (g - T.ofAll (G k) (hGc k) (r 0)) + (T.ofAll (G k - d 0 (Jk k) + (d 0 (Jk k) - d 0 J)) (((hGc k).sub (hdc 0 _)).add ((hdc 0 _).sub (hdc 0 J))) (r 0)) + -(x 0 J - T.ofAll (d 0 J) (hdc 0 J) (r 0))`. Rewrite using `[ofAll_add ((hGc k).sub (hdc 0 _)) ((hdc 0 _).sub (hdc 0 J)), ofAll_sub (hGc k) (hdc 0 _), ofAll_sub (hdc 0 _) (hdc 0 J)]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Use `(extNorm_add_add_le_max ρ _ _ _).trans (max_le hgρ (max_le ?_ ?_))` and prove the remaining obligations.

Rewrite using `[extNorm_ofAll]`. Establish `hρ0 : (0 : ℝ) < ρ` using `ρ.2.1`. Establish `hρ1 : (ρ : ℝ) < 1` using `rad_lt_one (r 0) ρ`. Use `(T.convergesAt_coeffB_add hρ0 hρ1 (((hGc k).sub (hdc 0 _)) ρ hρ0 hρ1) (((hdc 0 _).sub (hdc 0 J)) ρ hρ0 hρ1)).2.trans (max_le ?_ ?_)` and prove the remaining obligations. Conclude with `(hkey 0 k (Nat.zero_le _) ρ hρ ρ.2.2).trans (hJ₂ k hk2)`.

Conclude with `hJ₁ (Jk k) (hk1.trans (hJk k)) J (le_of_max_le_left hJ) ρ hρ`. Rewrite using `[extNorm_neg]`. Conclude with `(hdx 0 J ρ hρ).trans (hJ₂ J (le_of_max_le_right hJ))`. Conclude with `⟨max J₁ J₂, fun J hJ => ⟨hbound _ (hr 0) hk3 J hJ, hbound _ le_rfl hk4 J hJ⟩⟩`.
-/
theorem exists_glue (r : ℕ → Set.Ioo (0 : ℝ) 1) (hr : ∀ t, (r (t + 1) : ℝ) ≤ r t)
    (hr0 : Tendsto (fun t => (r t : ℝ)) atTop (𝓝 0)) (x : (t : ℕ) → ℕ → T.RobbaExt (r t))
    (hC : ∀ t, ∀ ε > 0, ∃ J₀, ∀ J ≥ J₀, ∀ K ≥ J₀,
      T.extNorm (r t) (topRad (r t)) (x t J - x t K) ≤ ε ∧
      T.extNorm (r t) ⟨r (t + 1), (r (t + 1)).2.1, hr t⟩ (x t J - x t K) ≤ ε)
    (hD : ∀ t, ∀ ε > 0, ∃ J₀, ∀ J ≥ J₀,
      T.extNorm (r (t + 1)) (topRad (r (t + 1))) (T.res (hr t) (x t J) - x (t + 1) J) ≤ ε) :
    ∃ g : T.RobbaExt (r 0), ∀ ε > 0, ∃ J₀, ∀ J ≥ J₀,
      T.extNorm (r 0) (topRad (r 0)) (g - x 0 J) ≤ ε ∧
      T.extNorm (r 0) ⟨r 1, (r 1).2.1, hr 0⟩ (g - x 0 J) ≤ ε := by
  have hanti : Antitone fun t => (r t : ℝ) := antitone_nat_of_succ_le hr
  have hhalf : ∀ J : ℕ, (0 : ℝ) < (1 / 2) ^ J := fun J => by positivity
  have hhalf_le : ∀ ε > (0 : ℝ), ∃ J₀ : ℕ, ∀ J ≥ J₀, ((1 : ℝ) / 2) ^ J ≤ ε := by
    intro ε hε
    obtain ⟨J₀, hJ₀⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (1 / 2 : ℝ) < 1)
    exact ⟨J₀, fun J hJ => (pow_le_pow_of_le_one (by norm_num) (by norm_num) hJ).trans hJ₀.le⟩

  choose d hdc hdx using fun (t J : ℕ) =>
    exists_approx_convAll (x t J) (⟨r (t + 1), (r (t + 1)).2.1, hr t⟩ : Set.Ioc (0 : ℝ) (r t))
      (hhalf J)

  have hdC : ∀ t, ∀ ε > 0, ∃ J₀, ∀ J ≥ J₀, ∀ K ≥ J₀, ∀ ρ : Set.Ioc (0 : ℝ) (r t),
      (r (t + 1) : ℝ) ≤ ρ → gaussNorm (T.coeffB (d t J - d t K)) ρ ≤ ε := by
    intro t ε hε
    obtain ⟨J₁, hJ₁⟩ := hC t ε hε
    obtain ⟨J₂, hJ₂⟩ := hhalf_le ε hε
    refine ⟨max J₁ J₂, fun J hJ K hK ρ hρ => ?_⟩
    rw [gaussNorm_ofAll_sub (hdc t J) (hdc t K)]
    have e : T.ofAll (d t J) (hdc t J) (r t) - T.ofAll (d t K) (hdc t K) (r t) =
        -(x t J - T.ofAll (d t J) (hdc t J) (r t)) + (x t J - x t K) +
          (x t K - T.ofAll (d t K) (hdc t K) (r t)) := by ring
    rw [e]
    refine (extNorm_add_add_le_max ρ _ _ _).trans (max_le ?_ (max_le ?_ ?_))
    · rw [extNorm_neg]; exact (hdx t J ρ hρ).trans (hJ₂ J (le_of_max_le_right hJ))
    · obtain ⟨h1, h2⟩ := hJ₁ J (le_of_max_le_left hJ) K (le_of_max_le_left hK)
      exact (T.extNorm_le_max _ (topRad (r t)) ρ hρ ρ.2.2 _).trans (max_le h2 h1)
    · exact (hdx t K ρ hρ).trans (hJ₂ K (le_of_max_le_right hK))

  set δ : ℕ → ℕ → T.B := fun t J => d t J - d (t + 1) J with hδdef
  have hδc : ∀ t J, T.ConvAll (δ t J) := fun t J => (hdc t J).sub (hdc (t + 1) J)
  have hδ : ∀ t, ∀ ε > 0, ∀ᶠ J in atTop, gaussNorm (T.coeffB (δ t J)) (r (t + 1)) ≤ ε := by
    intro t ε hε
    obtain ⟨J₁, hJ₁⟩ := hD t ε hε
    obtain ⟨J₂, hJ₂⟩ := hhalf_le ε hε
    refine eventually_atTop.2 ⟨max J₁ J₂, fun J hJ => ?_⟩
    rw [show (r (t + 1) : ℝ) = ((topRad (r (t + 1)) : Set.Ioc (0 : ℝ) (r (t + 1))) : ℝ) from rfl,
      gaussNorm_ofAll_sub (hdc t J) (hdc (t + 1) J)]
    have e : T.ofAll (d t J) (hdc t J) (r (t + 1)) - T.ofAll (d (t + 1) J) (hdc (t + 1) J) (r (t + 1)) =
        -T.res (hr t) (x t J - T.ofAll (d t J) (hdc t J) (r t)) +
          (T.res (hr t) (x t J) - x (t + 1) J) +
          (x (t + 1) J - T.ofAll (d (t + 1) J) (hdc (t + 1) J) (r (t + 1))) := by
      rw [map_sub, res_ofAll]; ring
    rw [e]
    refine (extNorm_add_add_le_max _ _ _ _).trans (max_le ?_ (max_le (hJ₁ J (le_of_max_le_left hJ)) ?_))
    · rw [extNorm_neg, extNorm_res]
      exact (hdx t J _ le_rfl).trans (hJ₂ J (le_of_max_le_right hJ))
    · exact (hdx (t + 1) J _ (hr (t + 1))).trans (hJ₂ J (le_of_max_le_right hJ))

  have hsel : ∀ k : ℕ, ∃ J, k ≤ J ∧ ∀ t < k, gaussNorm (T.coeffB (δ t J)) (r (t + 1)) ≤ (1 / 2) ^ k := by
    intro k
    have h1 : ∀ᶠ J in atTop, ∀ t ∈ Finset.range k,
        gaussNorm (T.coeffB (δ t J)) (r (t + 1)) ≤ (1 / 2) ^ k :=
      (Finset.range k).eventually_all.2 fun t _ => hδ t _ (hhalf k)
    obtain ⟨J, hJ1, hJ2⟩ := ((eventually_ge_atTop k).and h1).exists
    exact ⟨J, hJ1, fun t ht => hJ2 t (Finset.mem_range.2 ht)⟩
  choose Jk hJk hJδ using hsel

  set G : ℕ → T.B := fun k => d 0 (Jk k) - ∑ t ∈ Finset.range k, T.lowerPart (δ t (Jk k)) with hGdef
  have hGc : ∀ k, T.ConvAll (G k) := fun k =>
    (hdc 0 (Jk k)).sub (convAll_sum _ _ fun t _ => (hδc t (Jk k)).lowerPart)
  have hkey : ∀ s k, s ≤ k → ∀ ρ : ℝ, (r (s + 1) : ℝ) ≤ ρ → ρ ≤ r s →
      gaussNorm (T.coeffB (G k - d s (Jk k))) ρ ≤ (1 / 2) ^ k := by
    intro s k hsk ρ hρ1 hρ2
    set J := Jk k
    have hρ0 : 0 < ρ := (r (s + 1)).2.1.trans_le hρ1
    have hρ1' : ρ < 1 := hρ2.trans_lt (r s).2.2
    have h1 : ∑ t ∈ Finset.range s, δ t J = d 0 J - d s J :=
      Finset.sum_range_sub' (fun t => d t J) s
    have h2 := Finset.sum_range_add_sum_Ico (fun t => T.lowerPart (δ t J)) hsk
    have h3 : ∀ t, T.upperPart (δ t J) = δ t J - T.lowerPart (δ t J) := fun t =>
      eq_sub_of_add_eq' (T.lowerPart_add_upperPart _)
    have e : G k - d s J = ∑ t ∈ Finset.range s, T.upperPart (δ t J) -
        ∑ t ∈ Finset.Ico s k, T.lowerPart (δ t J) := by
      rw [Finset.sum_congr rfl (fun t _ => h3 t), Finset.sum_sub_distrib, h1, hGdef]
      simp only
      rw [← h2]; ring
    rw [e, sub_eq_add_neg]
    have hU := T.gaussNorm_finsetSum_le (Finset.range s) (fun t => T.upperPart (δ t J)) hρ0 hρ1'
      (hhalf k).le fun t ht => by
        have ht' := Finset.mem_range.1 ht
        refine ⟨(hδc t J).upperPart ρ hρ0 hρ1', ?_⟩
        have hle : ρ ≤ r (t + 1) := hρ2.trans (hanti (show t + 1 ≤ s by omega))
        exact (gaussNorm_upperPart_le (hδc t J) hρ0 hle (r (t + 1)).2.2).trans
          (hJδ k t (by omega))
    have hL := T.gaussNorm_finsetSum_le (Finset.Ico s k) (fun t => T.lowerPart (δ t J)) hρ0 hρ1'
      (hhalf k).le fun t ht => by
        have ht' := Finset.mem_Ico.1 ht
        refine ⟨(hδc t J).lowerPart ρ hρ0 hρ1', ?_⟩
        have hle : (r (t + 1) : ℝ) ≤ ρ := (hanti (show s + 1 ≤ t + 1 by omega)).trans hρ1
        exact (gaussNorm_lowerPart_le (hδc t J) (r (t + 1)).2.1 hle (r (t + 1)).2.2).trans
          (hJδ k t ht'.2)
    obtain ⟨hLn1, hLn2⟩ := T.convergesAt_coeffB_neg hρ0 hρ1' hL.1
    refine (T.convergesAt_coeffB_add hρ0 hρ1' hU.1 hLn1).2.trans (max_le hU.2 ?_)
    rw [hLn2]; exact hL.2

  have hGC : ∀ ρ : Set.Ioc (0 : ℝ) (r 0), ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N,
      gaussNorm (T.coeffB (G m - G n)) ρ < ε := by
    intro ρ ε hε
    obtain ⟨s, hs1, hs2⟩ := exists_mem_annulus r hr0 ρ.2.1 ρ.2.2
    obtain ⟨J₁, hJ₁⟩ := hdC s (ε / 2) (half_pos hε)
    obtain ⟨J₂, hJ₂⟩ := hhalf_le (ε / 2) (half_pos hε)
    refine ⟨max s (max J₁ J₂), fun m hm n hn => ?_⟩
    have hρ0 : (0 : ℝ) < ρ := ρ.2.1
    have hρ1 : (ρ : ℝ) < 1 := rad_lt_one (r 0) ρ
    have e : G m - G n = (G m - d s (Jk m)) + (d s (Jk m) - d s (Jk n)) + -(G n - d s (Jk n)) := by
      ring
    have c1 := hkey s m (le_of_max_le_left hm) ρ hs1 hs2
    have c2 := hkey s n (le_of_max_le_left hn) ρ hs1 hs2
    have hmJ : J₁ ≤ Jk m := (le_of_max_le_left (le_of_max_le_right hm)).trans (hJk m)
    have hnJ : J₁ ≤ Jk n := (le_of_max_le_left (le_of_max_le_right hn)).trans (hJk n)
    have c4 := hJ₁ (Jk m) hmJ (Jk n) hnJ ⟨ρ, ρ.2.1, hs2⟩ hs1
    have hm2 := hJ₂ m (le_of_max_le_right (le_of_max_le_right hm))
    have hn2 := hJ₂ n (le_of_max_le_right (le_of_max_le_right hn))
    have cv : ∀ b : T.B, T.ConvAll b → ConvergesAt (T.coeffB b) ρ := fun b hb => hb ρ hρ0 hρ1
    have hA := T.convergesAt_coeffB_add hρ0 hρ1 (cv (G m - d s (Jk m)) ((hGc m).sub (hdc s _)))
      (cv (d s (Jk m) - d s (Jk n)) ((hdc s _).sub (hdc s _)))
    obtain ⟨hN1, hN2⟩ := T.convergesAt_coeffB_neg hρ0 hρ1 (cv (G n - d s (Jk n)) ((hGc n).sub (hdc s _)))
    have hB := T.convergesAt_coeffB_add hρ0 hρ1 hA.1 hN1
    rw [e]
    refine lt_of_le_of_lt (hB.2.trans (max_le (hA.2.trans (max_le (c1.trans hm2) c4)) ?_))
      (half_lt_self hε)
    rw [hN2]; exact c2.trans hn2
  obtain ⟨g, hg⟩ := exists_tendsto_of_gaussNorm (T := T) (σ := r 0)
    (fun k => ⟨G k, hGc k (r 0) (r 0).2.1 (r 0).2.2⟩) hGC
  refine ⟨g, fun ε hε => ?_⟩

  have hgk : ∀ ρ : Set.Ioc (0 : ℝ) (r 0), ∀ᶠ k in atTop,
      T.extNorm (r 0) ρ (g - T.ofAll (G k) (hGc k) (r 0)) ≤ ε := by
    intro ρ
    have h1 : Tendsto (fun k => T.extNorm (r 0) ρ (g - T.ofAll (G k) (hGc k) (r 0))) atTop
        (𝓝 (T.extNorm (r 0) ρ (g - g))) :=
      ((T.continuous_extNorm ρ).tendsto _).comp (tendsto_const_nhds.sub hg)
    rw [sub_self, extNorm_zero] at h1
    exact h1.eventually (ge_mem_nhds hε)
  obtain ⟨J₁, hJ₁⟩ := hdC 0 ε hε
  obtain ⟨J₂, hJ₂⟩ := hhalf_le ε hε
  obtain ⟨k, hk1, hk2, hk3, hk4⟩ := ((eventually_ge_atTop J₁).and ((eventually_ge_atTop J₂).and
    ((hgk (topRad (r 0))).and (hgk ⟨r 1, (r 1).2.1, hr 0⟩)))).exists
  have hbound : ∀ ρ : Set.Ioc (0 : ℝ) (r 0), (r 1 : ℝ) ≤ ρ →
      T.extNorm (r 0) ρ (g - T.ofAll (G k) (hGc k) (r 0)) ≤ ε →
      ∀ J ≥ max J₁ J₂, T.extNorm (r 0) ρ (g - x 0 J) ≤ ε := by
    intro ρ hρ hgρ J hJ
    have e : g - x 0 J = (g - T.ofAll (G k) (hGc k) (r 0)) +
        (T.ofAll (G k - d 0 (Jk k) + (d 0 (Jk k) - d 0 J)) (((hGc k).sub (hdc 0 _)).add
          ((hdc 0 _).sub (hdc 0 J))) (r 0)) + -(x 0 J - T.ofAll (d 0 J) (hdc 0 J) (r 0)) := by
      rw [ofAll_add ((hGc k).sub (hdc 0 _)) ((hdc 0 _).sub (hdc 0 J)), ofAll_sub (hGc k) (hdc 0 _),
        ofAll_sub (hdc 0 _) (hdc 0 J)]; ring
    rw [e]
    refine (extNorm_add_add_le_max ρ _ _ _).trans (max_le hgρ (max_le ?_ ?_))
    · rw [extNorm_ofAll]
      have hρ0 : (0 : ℝ) < ρ := ρ.2.1
      have hρ1 : (ρ : ℝ) < 1 := rad_lt_one (r 0) ρ
      refine (T.convergesAt_coeffB_add hρ0 hρ1 (((hGc k).sub (hdc 0 _)) ρ hρ0 hρ1)
        (((hdc 0 _).sub (hdc 0 J)) ρ hρ0 hρ1)).2.trans (max_le ?_ ?_)
      · exact (hkey 0 k (Nat.zero_le _) ρ hρ ρ.2.2).trans (hJ₂ k hk2)
      · exact hJ₁ (Jk k) (hk1.trans (hJk k)) J (le_of_max_le_left hJ) ρ hρ
    · rw [extNorm_neg]; exact (hdx 0 J ρ hρ).trans (hJ₂ J (le_of_max_le_right hJ))
  exact ⟨max J₁ J₂, fun J hJ => ⟨hbound _ (hr 0) hk3 J hJ, hbound _ le_rfl hk4 J hJ⟩⟩

end TeichLift

end GroundTheory.PAdicHodge

namespace GroundTheory.PAdicHodge

open Laurent Filter Topology UniformSpace

section Dense

/- English proof (translation)
Establish `hβ : 0 < β` using `hα.trans hαβ`. Take `⟨t, ht0, ht1⟩` from `NormedField.exists_norm_lt_one L`. Establish `hr0 : 0 < α / β` using `div_pos hα hβ`. Establish `hr1 : α / β < 1` using `(div_lt_one hβ).2 hαβ`. Take `⟨m, hm⟩` from `exists_pow_lt_of_lt_one ht0 hr1`.

Use `set s : L := (iterateFrobeniusEquiv L p m).symm t`. Establish `hs : s ^ p ^ m = t`. Rewrite using `[← iterateFrobeniusEquiv_def]`. Conclude with `RingEquiv.apply_symm_apply _ _`. Establish `hsn : ‖s‖ ^ p ^ m = ‖t‖` using `by rw [← norm_pow, hs]`.

Establish `hpm : m ≤ p ^ m` using `(Nat.lt_pow_self hp.out.one_lt).le`. Establish `hγ1 : ‖s‖ < 1`. Assume the negation of the conclusion as `h`. Use `one_le_pow₀ (n := p ^ m) (not_lt.1 h)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hγ0 : 0 < ‖s‖`. Break down `(norm_nonneg s).lt_or_eq with h | h` into its components or cases. Conclude with `h`. Rewrite `hsn` using `[← h, zero_pow (pow_ne_zero _ hp.out.ne_zero)]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hγ : α / β < ‖s‖`. Establish `h1 : (α / β) ^ p ^ m < ‖s‖ ^ p ^ m`. Rewrite using `[hsn]`. Conclude with `(pow_le_pow_of_le_one hr0.le hr1.le hpm).trans_lt hm`. Conclude with `lt_of_pow_lt_pow_left₀ _ (norm_nonneg _) h1`.

Take `⟨n, hn1, hn2⟩` from `exists_mem_Ioc_zpow hβ (one_lt_inv₀ hγ0 |>.2 hγ1)`. Use `⟨s⁻¹ ^ n, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[norm_zpow, norm_inv]`. Establish `e : ‖s‖⁻¹ ^ n = ‖s‖ * ‖s‖⁻¹ ^ (n + 1)`. Rewrite using `[zpow_add_one₀ (inv_ne_zero hγ0.ne'), mul_comm (‖s‖⁻¹ ^ n), ← mul_assoc, mul_inv_cancel₀ hγ0.ne', one_mul]`.

Rewrite using `[e]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[norm_zpow, norm_inv]`. Conclude with `hn1`.
-/
theorem exists_norm_mem_Ioo_of_perfect (p : ℕ) [hp : Fact p.Prime] {L : Type*}
    [NontriviallyNormedField L] [CharP L p] [PerfectRing L p] {α β : ℝ} (hα : 0 < α) (hαβ : α < β) :
    ∃ c : L, α < ‖c‖ ∧ ‖c‖ < β := by
  have hβ : 0 < β := hα.trans hαβ
  obtain ⟨t, ht0, ht1⟩ := NormedField.exists_norm_lt_one L
  have hr0 : 0 < α / β := div_pos hα hβ
  have hr1 : α / β < 1 := (div_lt_one hβ).2 hαβ
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one ht0 hr1
  set s : L := (iterateFrobeniusEquiv L p m).symm t
  have hs : s ^ p ^ m = t := by
    rw [← iterateFrobeniusEquiv_def]; exact RingEquiv.apply_symm_apply _ _
  have hsn : ‖s‖ ^ p ^ m = ‖t‖ := by rw [← norm_pow, hs]
  have hpm : m ≤ p ^ m := (Nat.lt_pow_self hp.out.one_lt).le
  have hγ1 : ‖s‖ < 1 := by
    by_contra h
    have := one_le_pow₀ (n := p ^ m) (not_lt.1 h)
    linarith
  have hγ0 : 0 < ‖s‖ := by
    rcases (norm_nonneg s).lt_or_eq with h | h
    · exact h
    · rw [← h, zero_pow (pow_ne_zero _ hp.out.ne_zero)] at hsn; linarith
  have hγ : α / β < ‖s‖ := by
    have h1 : (α / β) ^ p ^ m < ‖s‖ ^ p ^ m := by
      rw [hsn]; exact (pow_le_pow_of_le_one hr0.le hr1.le hpm).trans_lt hm
    exact lt_of_pow_lt_pow_left₀ _ (norm_nonneg _) h1
  obtain ⟨n, hn1, hn2⟩ := exists_mem_Ioc_zpow hβ (one_lt_inv₀ hγ0 |>.2 hγ1)
  refine ⟨s⁻¹ ^ n, ?_, ?_⟩
  · rw [norm_zpow, norm_inv]
    have e : ‖s‖⁻¹ ^ n = ‖s‖ * ‖s‖⁻¹ ^ (n + 1) := by
      rw [zpow_add_one₀ (inv_ne_zero hγ0.ne'), mul_comm (‖s‖⁻¹ ^ n), ← mul_assoc,
        mul_inv_cancel₀ hγ0.ne', one_mul]
    rw [e]
    calc α = α / β * β := by field_simp
      _ < ‖s‖ * β := mul_lt_mul_of_pos_right hγ hβ
      _ ≤ ‖s‖ * ‖s‖⁻¹ ^ (n + 1) := mul_le_mul_of_nonneg_left hn2 hγ0.le
  · rw [norm_zpow, norm_inv]; exact hn1

end Dense

namespace TeichLift

variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] {T : TeichLift p L Γ}

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => rw [Finset.sum_empty, extNorm_zero]`. Conclude with `hM`. Consider the case `insert i s hi ih`. Rewrite using `[Finset.sum_insert hi]`.

Conclude with `(T.extNorm_add_le ρ _ _).trans (max_le (h i (Finset.mem_insert_self i s)) (ih fun j hj => h j (Finset.mem_insert_of_mem hj)))`.
-/
theorem extNorm_sum_le {σ : Set.Ioo (0 : ℝ) 1} (ρ : Set.Ioc (0 : ℝ) σ) {ι : Type*} (s : Finset ι)
    (f : ι → T.RobbaExt σ) {M : ℝ} (hM : 0 ≤ M) (h : ∀ i ∈ s, T.extNorm σ ρ (f i) ≤ M) :
    T.extNorm σ ρ (∑ i ∈ s, f i) ≤ M := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, extNorm_zero]; exact hM
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (T.extNorm_add_le ρ _ _).trans (max_le (h i (Finset.mem_insert_self i s))
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj)))

namespace TeichFrob

variable (F : T.TeichFrob)

/- English proof (translation)
The claim follows from `Completion.continuous_map`.
-/
theorem continuous_extFrobSymm (τ : Set.Ioo (0 : ℝ) 1) : Continuous (F.extFrobSymm τ) :=
  Completion.continuous_map

def powRad {σ : Set.Ioo (0 : ℝ) 1} (r : Set.Ioc (0 : ℝ) σ) : Set.Ioc (0 : ℝ) (F.powRadius σ) :=
  ⟨(r : ℝ) ^ p ^ F.a, pow_pos r.2.1 _, pow_le_pow_left₀ r.2.1.le r.2.2 _⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem coe_powRad {σ : Set.Ioo (0 : ℝ) 1} (r : Set.Ioc (0 : ℝ) σ) :
    ((F.powRad r : Set.Ioc (0 : ℝ) (F.powRadius σ)) : ℝ) = (r : ℝ) ^ p ^ F.a := rfl

/- English proof (translation)
Proceed by induction on `x using Completion.induction_on with`. Consider the case `hp`. Conclude with `isClosed_eq ((T.continuous_extNorm _).comp (F.continuous_extFrob σ)) ((T.continuous_extNorm r).pow _)`. Consider the case `ih b`. Rewrite using `[F.extFrob_coe, extNorm_coe, extNorm_coe, coe_econFrob, coe_powRad]`.

Conclude with `F.gaussNorm_coeffB_toB r.2.1 (rad_lt_one σ r) (T.convergesAt_rad σ b r)`.
-/
theorem extNorm_extFrob (σ : Set.Ioo (0 : ℝ) 1) (r : Set.Ioc (0 : ℝ) σ) (x : T.RobbaExt σ) :
    T.extNorm (F.powRadius σ) (F.powRad r) (F.extFrob σ x) = T.extNorm σ r x ^ p ^ F.a := by
  induction x using Completion.induction_on with
  | hp =>
    exact isClosed_eq ((T.continuous_extNorm _).comp (F.continuous_extFrob σ))
      ((T.continuous_extNorm r).pow _)
  | ih b =>
    rw [F.extFrob_coe, extNorm_coe, extNorm_coe, coe_econFrob, coe_powRad]
    exact F.gaussNorm_coeffB_toB r.2.1 (rad_lt_one σ r) (T.convergesAt_rad σ b r)

def powRadRoot {τ : Set.Ioo (0 : ℝ) 1} (r : Set.Ioc (0 : ℝ) (F.rootRadius τ)) : Set.Ioc (0 : ℝ) τ :=
  ⟨(r : ℝ) ^ p ^ F.a, pow_pos r.2.1 _, by
    have h := pow_le_pow_left₀ r.2.1.le r.2.2 (p ^ F.a)
    have e : ((F.rootRadius τ : Set.Ioo (0 : ℝ) 1) : ℝ) ^ p ^ F.a = τ :=
      congrArg Subtype.val (F.powRadius_rootRadius τ)
    exact h.trans e.le⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem coe_powRadRoot {τ : Set.Ioo (0 : ℝ) 1} (r : Set.Ioc (0 : ℝ) (F.rootRadius τ)) :
    ((F.powRadRoot r : Set.Ioc (0 : ℝ) τ) : ℝ) = (r : ℝ) ^ p ^ F.a := rfl

/- English proof (translation)
Proceed by induction on `x using Completion.induction_on with`. Consider the case `hp`. Conclude with `isClosed_eq (((T.continuous_extNorm r).comp (F.continuous_extFrobSymm τ)).pow _) (T.continuous_extNorm _)`. Consider the case `ih b`. Rewrite using `[F.extFrobSymm_coe, extNorm_coe, extNorm_coe, coe_econFrobSymm, coe_powRadRoot]`.

Establish `hc` using `T.convergesAt_rad _ (F.econFrobSymm τ b) r`. Rewrite `hc` using `[coe_econFrobSymm]`. Use `F.gaussNorm_coeffB_toB r.2.1 (rad_lt_one _ r) hc` as an intermediate fact. Rewrite `this` using `[RingEquiv.apply_symm_apply]`. Conclude with `this.symm`.
-/
theorem extNorm_extFrobSymm (τ : Set.Ioo (0 : ℝ) 1) (r : Set.Ioc (0 : ℝ) (F.rootRadius τ))
    (x : T.RobbaExt τ) :
    T.extNorm (F.rootRadius τ) r (F.extFrobSymm τ x) ^ p ^ F.a = T.extNorm τ (F.powRadRoot r) x := by
  induction x using Completion.induction_on with
  | hp =>
    exact isClosed_eq (((T.continuous_extNorm r).comp (F.continuous_extFrobSymm τ)).pow _)
      (T.continuous_extNorm _)
  | ih b =>
    rw [F.extFrobSymm_coe, extNorm_coe, extNorm_coe, coe_econFrobSymm, coe_powRadRoot]
    have hc := T.convergesAt_rad _ (F.econFrobSymm τ b) r
    rw [coe_econFrobSymm] at hc
    have := F.gaussNorm_coeffB_toB r.2.1 (rad_lt_one _ r) hc
    rw [RingEquiv.apply_symm_apply] at this
    exact this.symm

/- English proof (translation)
Proceed by induction on `x using Completion.induction_on with`. Consider the case `hp`. Conclude with `isClosed_eq ((F.continuous_extFrob σ).comp ((T.continuous_res h).comp (F.continuous_extFrobSymm τ))) (T.continuous_res h')`. Consider the case `ih b`. Rewrite using `[F.extFrobSymm_coe, res_coe, F.extFrob_coe, res_coe]`.

Use `congr 1`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[coe_econFrob, coe_incl, coe_incl, coe_econFrobSymm, RingEquiv.apply_symm_apply]`.
-/
theorem extFrob_res_extFrobSymm {τ σ : Set.Ioo (0 : ℝ) 1} (h : (σ : ℝ) ≤ F.rootRadius τ)
    (h' : ((F.powRadius σ : Set.Ioo (0 : ℝ) 1) : ℝ) ≤ τ) (x : T.RobbaExt τ) :
    F.extFrob σ (T.res h (F.extFrobSymm τ x)) = T.res h' x := by
  induction x using Completion.induction_on with
  | hp =>
    exact isClosed_eq ((F.continuous_extFrob σ).comp ((T.continuous_res h).comp
      (F.continuous_extFrobSymm τ))) (T.continuous_res h')
  | ih b =>
    rw [F.extFrobSymm_coe, res_coe, F.extFrob_coe, res_coe]
    congr 1
    apply Subtype.ext
    rw [coe_econFrob, coe_incl, coe_incl, coe_econFrobSymm, RingEquiv.apply_symm_apply]

end TeichFrob

end TeichLift

end GroundTheory.PAdicHodge
