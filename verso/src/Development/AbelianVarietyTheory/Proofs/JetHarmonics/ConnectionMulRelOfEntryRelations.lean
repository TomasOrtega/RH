import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SameFns

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

namespace GlobalTheory.HatNF.MulRelAlg

/- English proof (translation)
Take `⟨Y, hY⟩` from `Infinite.exists_notMem_finset (((Finset.univ : Finset (M.Ty P)) ×ˢ Finset.Icc 1 (P.k - 1)).image fun x => -M.rho P x.1 x.2)`. Use `⟨Y, fun ρ => ?_⟩` and prove the remaining obligations. Unfold `M.xC`. Use `Finset.prod_ne_zero_iff.2 fun i hi h => hY ?_` and prove the remaining obligations. Use `Finset.mem_image.2 ⟨(ρ, i), Finset.mem_product.2 ⟨Finset.mem_univ _, hi⟩, ?_⟩` and prove the remaining obligations.

Establish `h' : Y + M.rho P ρ i = 0` using `by exact_mod_cast h`. Use `show -M.rho P ρ i = Y`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem exists_real_xC_ne_zero (P : M.Par) : ∃ Y : ℝ, ∀ ρ : M.Ty P, M.xC P ρ (Y : ℂ) ≠ 0 := by
  classical
  obtain ⟨Y, hY⟩ := Infinite.exists_notMem_finset
    (((Finset.univ : Finset (M.Ty P)) ×ˢ Finset.Icc 1 (P.k - 1)).image fun x => -M.rho P x.1 x.2)
  refine ⟨Y, fun ρ => ?_⟩
  unfold M.xC
  refine Finset.prod_ne_zero_iff.2 fun i hi h => hY ?_
  refine Finset.mem_image.2 ⟨(ρ, i), Finset.mem_product.2 ⟨Finset.mem_univ _, hi⟩, ?_⟩
  have h' : Y + M.rho P ρ i = 0 := by exact_mod_cast h
  show -M.rho P ρ i = Y
  linarith

/- English proof (translation)
Use function extensionality and compare the values at `i`. Conclude with `Fin.ext ((h i).trans (h' i).symm)`.
-/
theorem up_unique {P : M.Par} {l : ℕ} {σ ρ ρ' : M.Ty P} (h : M.Up P l σ ρ) (h' : M.Up P l σ ρ') : ρ = ρ' := by
  funext i
  exact Fin.ext ((h i).trans (h' i).symm)

/- English proof (translation)
Introduce `h`. Rewrite `hl` using `[Finset.mem_Icc]`. Use `h ⟨l - 1, by omega⟩` as an intermediate fact. Rewrite `this` using `[if_pos (by show l - 1 + 1 = l; omega)]`. Use linear arithmetic over natural numbers and integers.
-/
theorem not_up_self {P : M.Par} {l : ℕ} (hl : l ∈ Finset.Icc 1 (P.k - 1)) (ρ : M.Ty P) : ¬ M.Up P l ρ ρ := by
  intro h
  rw [Finset.mem_Icc] at hl
  have := h ⟨l - 1, by omega⟩
  rw [if_pos (by show l - 1 + 1 = l; omega)] at this
  omega

variable {P : M.Par} {A : Type} [Ring A] [StarRing A] [Algebra ℂ A]

/- English proof (translation)
Unfold `Q.NFData.weightedSumBis`. Rewrite using `[Finset.mul_sum, Finset.sum_mul]`. Use `Finset.sum_eq_zero fun l hl => ?_` and prove the remaining obligations. Establish `h4` using `h.2.2.2.1 l (fun σ => if M.Up P l σ ρ then 1 else 0) (Pi.single ρ 1) (by`. Introduce `σ σ' hu`.

Distinguish the cases in `e : σ' = ρ`. Substitute `e` using the available equality. Simplify using `[hu]`. Establish `: ¬ M.Up P l σ ρ` using `fun h2 => e (up_unique hu h2)`. Simplify using `[this, e])`.

Rewrite using `[← mul_assoc, h4, mul_assoc, mul_assoc, ← map_mul, ← map_mul]`. Establish `: ((fun σ => if M.Up P l σ ρ then (1 : ℂ) else 0) * ((fun σ => M.xEx P {l} σ Y) * Pi.single ρ 1) : M.Ty P → ℂ) = 0`. Use function extensionality and compare the values at `σ`. Distinguish the cases in `e : σ = ρ`. Substitute `e` using the available equality.

Simplify using `[not_up_self hl]`. Simplify using `[e]`. Rewrite using `[this, map_zero, mul_zero]`.
-/
theorem proj_raising_sum_proj_eq_zero (d : Q.NFData P A) (h : d.Rel) (Y : ℂ) (ρ : M.Ty P) :
    d.κ (Pi.single ρ 1) * d.weightedSumBis Y * d.κ (Pi.single ρ 1) = 0 := by
  classical
  unfold Q.NFData.weightedSumBis
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_eq_zero fun l hl => ?_
  have h4 := h.2.2.2.1 l (fun σ => if M.Up P l σ ρ then 1 else 0) (Pi.single ρ 1) (by
    intro σ σ' hu
    by_cases e : σ' = ρ
    · subst e; simp [hu]
    · have : ¬ M.Up P l σ ρ := fun h2 => e (up_unique hu h2)
      simp [this, e])
  rw [← mul_assoc, h4, mul_assoc, mul_assoc, ← map_mul, ← map_mul]
  have : ((fun σ => if M.Up P l σ ρ then (1 : ℂ) else 0) *
      ((fun σ => M.xEx P {l} σ Y) * Pi.single ρ 1) : M.Ty P → ℂ) = 0 := by
    funext σ
    by_cases e : σ = ρ
    · subst e; simp [not_up_self hl]
    · simp [e]
  rw [this, map_zero, mul_zero]

/- English proof (translation)
Establish `h1 : ∀ ρ, d.κ (Pi.single ρ 1) * X = 0`. Introduce `ρ`. Use `h0 ρ` as an intermediate fact. Rewrite `this` using `[mul_assoc, ← (hc _).eq, ← mul_assoc, ← map_mul, ← Pi.single_mul, mul_one]`. Conclude with `this`.

Establish `h2 : ∑ ρ : M.Ty P, d.κ (Pi.single ρ 1) = 1`. Rewrite using `[← map_sum, ← map_one d.κ]`. Use `congr 1`. Conclude with `Finset.univ_sum_single (1 : M.Ty P → ℂ)`. Rewrite using `[← one_mul X, ← h2, Finset.sum_mul]`.

Conclude with `Finset.sum_eq_zero fun ρ _ => h1 ρ`.
-/
theorem eq_zero_of_blocks (d : Q.NFData P A) (X : A) (hc : ∀ f, Commute (d.κ f) X)
    (h0 : ∀ ρ, d.κ (Pi.single ρ 1) * X * d.κ (Pi.single ρ 1) = 0) : X = 0 := by
  classical
  have h1 : ∀ ρ, d.κ (Pi.single ρ 1) * X = 0 := by
    intro ρ
    have := h0 ρ
    rw [mul_assoc, ← (hc _).eq, ← mul_assoc, ← map_mul, ← Pi.single_mul, mul_one] at this
    exact this
  have h2 : ∑ ρ : M.Ty P, d.κ (Pi.single ρ 1) = 1 := by
    rw [← map_sum, ← map_one d.κ]
    congr 1
    exact Finset.univ_sum_single (1 : M.Ty P → ℂ)
  rw [← one_mul X, ← h2, Finset.sum_mul]
  exact Finset.sum_eq_zero fun ρ _ => h1 ρ

/- English proof (translation)
Establish `hb : star L.ζb = L.ζ` using `by rw [← h.1, star_star]`. Establish `hG : star L.GG = L.GG`. Rewrite using `[L.GG_def, star_sub, star_mul, h.1, hb, ← algebraMap_star_comm, h.2.2]`. Establish `: star L.GGi * L.GG = 1` using `by rw [← hG, ← star_mul, L.GG_GGi, star_one]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem star_GGi [StarModule ℂ A] {r : ℕ} (L : LevelData A r) (h : IsStarLevel L) : star L.GGi = L.GGi := by
  have hb : star L.ζb = L.ζ := by rw [← h.1, star_star]
  have hG : star L.GG = L.GG := by
    rw [L.GG_def, star_sub, star_mul, h.1, hb, ← algebraMap_star_comm, h.2.2]
  have : star L.GGi * L.GG = 1 := by rw [← hG, ← star_mul, L.GG_GGi, star_one]
  calc star L.GGi = star L.GGi * L.GG * L.GGi := by rw [mul_assoc, L.GG_GGi, mul_one]
    _ = L.GGi := by rw [this, one_mul]

/- English proof (translation)
Take `⟨Y, hY⟩` from `exists_real_xC_ne_zero P`. Establish `hQ` using `hQ Y`. Establish `e10 : d.QQ Y 1 0 = d.L.GG * d.x Y * d.L.l0 Y + d.weightedSumBis Y` using `rfl`. Establish `e11 : d.QQ Y 1 1 = d.L.GG * d.x Y` using `rfl`. Rewrite `hQ` using `[e10, e11]`.

Establish `mG : d.L.GG ∈ d.L.fns` using `by simp [LevelData.fns]`. Establish `mGi : d.L.GGi ∈ d.L.fns` using `by simp [LevelData.fns]`. Establish `mz : d.L.ζb ∈ d.L.fns` using `by simp [LevelData.fns]`. Establish `kG : ∀ f, Commute (d.κ f) d.L.GG` using `fun f => h.2.1 f _ (Or.inl mG)`. Establish `kGi : ∀ f, Commute (d.κ f) d.L.GGi` using `fun f => h.2.1 f _ (Or.inl mGi)`.

Establish `kz : ∀ f, Commute (d.κ f) d.L.ζb` using `fun f => h.2.1 f _ (Or.inl mz)`. Establish `kn : ∀ f, Commute (d.κ f) d.L.nab` using `fun f => h.2.1 f _ (Or.inr (by simp))`. Establish `kk : ∀ f, Commute (d.κ f) (d.x Y)` using `fun f => by`. Unfold `Q.NFData.x`. Conclude with `(Commute.all _ _).map d.κ`.

Use `set Z : A := m * d.L.nab + d.L.ζb * d.L.GGi * m' - d.L.nab * m with hZ`. Use `set g : A := d.L.GG * d.x Y with hg`. Establish `kZ : ∀ f, Commute (d.κ f) Z` using `fun f => (((hκ f).mul_right (kn f)).add_right (((kz f).mul_right (kGi f)).mul_right (hκ' f))).sub_right ((kn f).mul_right (hκ f))`. Establish `gm : Commute g m` using `(hf _ mG).mul_left (hκ _)`. Establish `gw : Commute g (d.L.ζb * d.L.GGi * m')` using `(Commute.mul_right (Commute.mul_right (d.L.fns_comm _ mG _ mz) (d.L.fns_comm _ mG _ mGi)) (hf' _ mG)).mul_left (((kz _).mul_right (kGi _)).mul_right (hκ' _))`.

Establish `um : Commute (algebraMap ℂ A ((Y : ℂ) + 1 / 2) * (d.L.ζb * d.L.GGi)) m` using `Commute.mul_left (Algebra.commutes _ _) ((hf _ mz).mul_left (hf _ mGi))`. Establish `hX : g * Z = m * d.weightedSumBis Y - d.weightedSumBis Y * m`. Establish `e1 : m * (g * d.L.l0 Y) = g * (m * d.L.l0 Y)` using `by rw [← mul_assoc, ← gm.eq, mul_assoc]`. Rewrite `hQ` using `[add_mul, mul_add, e1, ← gw.eq]`. Establish `e2 : Z = d.L.l0 Y * m - m * d.L.l0 Y + d.L.ζb * d.L.GGi * m'`.

Unfold `LevelData.l0`. Rewrite using `[sub_mul, mul_sub, um.eq, hZ]`. Use `noncomm_ring`. Rewrite using `[e2, mul_add, mul_sub, ← mul_assoc g _ m, eq_sub_of_add_eq hQ]`. Normalize the expressions using the abelian group laws.

Establish `hX0 : g * Z = 0`. Use `eq_zero_of_blocks d _ (fun f => ((kG f).mul_right (kk f)).mul_right (kZ f)) fun ρ => ?_` and prove the remaining obligations. Use `proj_raising_sum_proj_eq_zero d h Y ρ` as an intermediate fact. Rewrite using `[hX, mul_sub, sub_mul, ← mul_assoc, (hκ _).eq, mul_assoc m, mul_assoc m, this, ← mul_assoc _ _ m, mul_assoc _ m, ← (hκ _).eq, ← mul_assoc, this]`. Simplify using the standard rewrite rules.

Establish `hinv : d.κ (fun ρ => (M.xC P ρ Y)⁻¹) * d.L.GGi * g = 1`. Rewrite using `[hg, mul_assoc, ← mul_assoc d.L.GGi, d.L.GGi_GG, one_mul]`. Unfold `Q.NFData.x`. Rewrite using `[← map_mul, ← map_one d.κ]`. Use `congr 1`.

Use function extensionality and compare the values at `ρ`. Conclude with `inv_mul_cancel₀ (hY ρ)`. Establish `: Z = 0` using `by rw [← one_mul Z, ← hinv, mul_assoc, hX0, mul_zero]`. Conclude with `(sub_eq_zero.1 this).symm`.
-/
theorem nab_rel (d : Q.NFData P A) (h : d.Rel) (m m' : A) (hf : ∀ f ∈ d.L.fns, Commute f m)
    (hf' : ∀ f ∈ d.L.fns, Commute f m') (hκ : ∀ f, Commute (d.κ f) m) (hκ' : ∀ f, Commute (d.κ f) m')
    (hQ : ∀ Y : ℝ, d.QQ Y 1 0 * m = m * d.QQ Y 1 0 - d.L.ζb * d.L.GGi * m' * d.QQ Y 1 1) :
    d.L.nab * m = m * d.L.nab + d.L.ζb * d.L.GGi * m' := by
  classical
  obtain ⟨Y, hY⟩ := exists_real_xC_ne_zero P
  have hQ := hQ Y
  have e10 : d.QQ Y 1 0 = d.L.GG * d.x Y * d.L.l0 Y + d.weightedSumBis Y := rfl
  have e11 : d.QQ Y 1 1 = d.L.GG * d.x Y := rfl
  rw [e10, e11] at hQ
  have mG : d.L.GG ∈ d.L.fns := by simp [LevelData.fns]
  have mGi : d.L.GGi ∈ d.L.fns := by simp [LevelData.fns]
  have mz : d.L.ζb ∈ d.L.fns := by simp [LevelData.fns]
  have kG : ∀ f, Commute (d.κ f) d.L.GG := fun f => h.2.1 f _ (Or.inl mG)
  have kGi : ∀ f, Commute (d.κ f) d.L.GGi := fun f => h.2.1 f _ (Or.inl mGi)
  have kz : ∀ f, Commute (d.κ f) d.L.ζb := fun f => h.2.1 f _ (Or.inl mz)
  have kn : ∀ f, Commute (d.κ f) d.L.nab := fun f => h.2.1 f _ (Or.inr (by simp))
  have kk : ∀ f, Commute (d.κ f) (d.x Y) := fun f => by
    unfold Q.NFData.x; exact (Commute.all _ _).map d.κ
  set Z : A := m * d.L.nab + d.L.ζb * d.L.GGi * m' - d.L.nab * m with hZ
  set g : A := d.L.GG * d.x Y with hg
  have kZ : ∀ f, Commute (d.κ f) Z := fun f =>
    (((hκ f).mul_right (kn f)).add_right (((kz f).mul_right (kGi f)).mul_right (hκ' f))).sub_right
      ((kn f).mul_right (hκ f))
  have gm : Commute g m := (hf _ mG).mul_left (hκ _)
  have gw : Commute g (d.L.ζb * d.L.GGi * m') :=
    (Commute.mul_right (Commute.mul_right (d.L.fns_comm _ mG _ mz) (d.L.fns_comm _ mG _ mGi)) (hf' _ mG)).mul_left
      (((kz _).mul_right (kGi _)).mul_right (hκ' _))
  have um : Commute (algebraMap ℂ A ((Y : ℂ) + 1 / 2) * (d.L.ζb * d.L.GGi)) m :=
    Commute.mul_left (Algebra.commutes _ _) ((hf _ mz).mul_left (hf _ mGi))
  have hX : g * Z = m * d.weightedSumBis Y - d.weightedSumBis Y * m := by
    have e1 : m * (g * d.L.l0 Y) = g * (m * d.L.l0 Y) := by rw [← mul_assoc, ← gm.eq, mul_assoc]
    rw [add_mul, mul_add, e1, ← gw.eq] at hQ
    have e2 : Z = d.L.l0 Y * m - m * d.L.l0 Y + d.L.ζb * d.L.GGi * m' := by
      unfold LevelData.l0
      rw [sub_mul, mul_sub, um.eq, hZ]
      noncomm_ring
    rw [e2, mul_add, mul_sub, ← mul_assoc g _ m, eq_sub_of_add_eq hQ]
    abel
  have hX0 : g * Z = 0 := by
    refine eq_zero_of_blocks d _ (fun f => ((kG f).mul_right (kk f)).mul_right (kZ f)) fun ρ => ?_
    have := proj_raising_sum_proj_eq_zero d h Y ρ
    rw [hX, mul_sub, sub_mul, ← mul_assoc, (hκ _).eq, mul_assoc m, mul_assoc m, this, ← mul_assoc _ _ m,
      mul_assoc _ m, ← (hκ _).eq, ← mul_assoc, this]
    simp
  have hinv : d.κ (fun ρ => (M.xC P ρ Y)⁻¹) * d.L.GGi * g = 1 := by
    rw [hg, mul_assoc, ← mul_assoc d.L.GGi, d.L.GGi_GG, one_mul]
    unfold Q.NFData.x
    rw [← map_mul, ← map_one d.κ]
    congr 1
    funext ρ
    exact inv_mul_cancel₀ (hY ρ)
  have : Z = 0 := by rw [← one_mul Z, ← hinv, mul_assoc, hX0, mul_zero]
  exact (sub_eq_zero.1 this).symm

/- English proof (translation)
Introduce `P A _ _ _ _ d hd m hm q`. Take `⟨-, hs, hr, -⟩` from `hd`. Take `⟨h1, h2, h3, h4, h5, h6⟩` from `hm q`. Take `⟨k1, -, -, k4, k5, -⟩` from `hm (q + 1)`. Establish `hn` using `nab_rel d hr (m q) (m (q + 1)) h1 k1 h4 k4 h6`.

Use `⟨h1, h2, h3, hn, ?_⟩` and prove the remaining obligations. Establish `hb : star d.L.ζb = d.L.ζ` using `by rw [← hs.1, star_star]`. Establish `mGi : d.L.GGi ∈ d.L.fns` using `by simp [LevelData.fns]`. Establish `mz : d.L.ζ ∈ d.L.fns` using `by simp [LevelData.fns]`. Establish `hst` using `congrArg star hn`.

Rewrite `hst` using `[star_add, star_mul, star_mul, star_mul, star_mul, hs.2.1, h5, k5, hb, star_GGi d.L hs, d.L.fns_comm _ mGi _ mz, ← ((k1 _ mz).mul_left (k1 _ mGi)).eq]`. Rewrite using `[hst]`. Normalize the expressions using the abelian group laws.
-/
theorem mulRel_of_entries : ∀ (P : M.Par) (A : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] (d : Q.NFData P A), HatHyp d → ∀ m : ℕ → A, (∀ q, (∀ f ∈ d.L.fns, Commute f (m q)) ∧ (∀ l, d.L.p l * m q = m q * d.L.p l + m (q + 1)) ∧ (∀ l, d.L.pb l * m q = m q * d.L.pb l + m (q + 1)) ∧ (∀ f : M.Ty P → ℂ, Commute (d.κ f) (m q)) ∧ star (m q) = m q ∧ ∀ Y : ℝ, d.QQ Y 1 0 * m q = m q * d.QQ Y 1 0 - d.L.ζb * d.L.GGi * m (q + 1) * d.QQ Y 1 1) → MulRel d.L m := by
  intro P A _ _ _ _ d hd m hm q
  obtain ⟨-, hs, hr, -⟩ := hd
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hm q
  obtain ⟨k1, -, -, k4, k5, -⟩ := hm (q + 1)
  have hn := nab_rel d hr (m q) (m (q + 1)) h1 k1 h4 k4 h6
  refine ⟨h1, h2, h3, hn, ?_⟩
  have hb : star d.L.ζb = d.L.ζ := by rw [← hs.1, star_star]
  have mGi : d.L.GGi ∈ d.L.fns := by simp [LevelData.fns]
  have mz : d.L.ζ ∈ d.L.fns := by simp [LevelData.fns]
  have hst := congrArg star hn
  rw [star_add, star_mul, star_mul, star_mul, star_mul, hs.2.1, h5, k5, hb, star_GGi d.L hs,
    d.L.fns_comm _ mGi _ mz, ← ((k1 _ mz).mul_left (k1 _ mGi)).eq] at hst
  rw [hst]
  abel

end GlobalTheory.HatNF.MulRelAlg
