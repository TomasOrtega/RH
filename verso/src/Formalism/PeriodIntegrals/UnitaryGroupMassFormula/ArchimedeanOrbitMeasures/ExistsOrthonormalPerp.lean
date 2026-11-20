import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.GoodChartExOfWitt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.PerpPosV
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.WittExtensionTheorem
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianDiagonalization.ExistsOrthogonalFamily

noncomputable section

namespace PI.AprimeInfW

open Matrix Finset

section Lin

variable {n : ℕ} (ε : Fin n → Bool)

def BJ : (Fin n → ℂ) →ₗ⋆[ℂ] (Fin n → ℂ) →ₗ[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) (fun x y => star x ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ y))
    (fun x x' y => by rw [star_add, add_dotProduct])
    (fun c x y => by rw [star_smul, smul_dotProduct]; rfl)
    (fun x y y' => by rw [mulVec_add, dotProduct_add])
    (fun c x y => by rw [mulVec_smul, dotProduct_smul]; rfl)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem BJ_apply (x y : Fin n → ℂ) : BJ ε x y = star x ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ y) := rfl

def dJ (i : Fin n) : ℂ := if ε i then 1 else -1

/- English proof (translation)
Rewrite using `[BJ_apply]`. Simplify using `only [dotProduct, Formalism.REAL.Jm, mulVec_diagonal, Pi.star_apply]`. Both sides reduce to the same expression.
-/
theorem BJ_sum (x y : Fin n → ℂ) : BJ ε x y = ∑ i, star (x i) * (dJ ε i * y i) := by
  rw [BJ_apply]
  simp only [dotProduct, Formalism.REAL.Jm, mulVec_diagonal, Pi.star_apply]
  rfl

/- English proof (translation)
Apply the tactic sequence `unfold dJ; split_ifs <;> simp`.
-/
theorem dJ_star (i : Fin n) : star (dJ ε i) = dJ ε i := by
  unfold dJ; split_ifs <;> simp

/- English proof (translation)
Unfold `dJ`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem dJ_ne (i : Fin n) : dJ ε i ≠ 0 := by
  unfold dJ
  split_ifs <;> simp

/- English proof (translation)
Rewrite using `[BJ_sum, BJ_sum, star_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[star_mul', star_mul', star_star, dJ_star]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem BJ_herm (x y : Fin n → ℂ) : star (BJ ε x y) = BJ ε y x := by
  rw [BJ_sum, BJ_sum, star_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [star_mul', star_mul', star_star, dJ_star]
  ring

/- English proof (translation)
Use function extensionality and compare the values at `j`. Establish `h1` using `h (Pi.single j 1)`. Rewrite `h1` using `[BJ_sum, Finset.sum_eq_single j]`. Rewrite `h1` using `[Pi.single_eq_same, mul_one]`. Break down `mul_eq_zero.mp h1 with h2 | h2` into its components or cases.

Simplify using `using h2`. Conclude with `absurd h2 (dJ_ne ε j)`. Introduce `b _ hb`. Rewrite using `[Pi.single_eq_of_ne hb, mul_zero, mul_zero]`. Introduce `hj`.

Conclude with `absurd (Finset.mem_univ j) hj`.
-/
theorem BJ_nondeg (x : Fin n → ℂ) (h : ∀ y, BJ ε x y = 0) : x = 0 := by
  funext j
  have h1 := h (Pi.single j 1)
  rw [BJ_sum, Finset.sum_eq_single j] at h1
  · rw [Pi.single_eq_same, mul_one] at h1
    rcases mul_eq_zero.mp h1 with h2 | h2
    · simpa using h2
    · exact absurd h2 (dJ_ne ε j)
  · intro b _ hb
    rw [Pi.single_eq_of_ne hb, mul_zero, mul_zero]
  · intro hj
    exact absurd (Finset.mem_univ j) hj

/- English proof (translation)
Rewrite using `[BJ_sum]`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Rewrite using `[Finset.sum_eq_single i]`. Simplify using `[Formalism.REAL.Jm, dJ]`.

Introduce `b _ hb`. Simplify using `[Pi.single_eq_of_ne hb]`. Introduce `hi`. Conclude with `absurd (Finset.mem_univ i) hi`. Rewrite using `[show Formalism.REAL.Jm ε i j = 0 by simp [Formalism.REAL.Jm, hij]]`.

Use `Finset.sum_eq_zero fun l _ => ?_` and prove the remaining obligations. Distinguish the cases in `hli : l = i`. Substitute `hli` using the available equality. Simplify using `[Pi.single_eq_of_ne hij]`. Simplify using `[Pi.single_eq_of_ne hli]`.
-/
theorem BJ_single (i j : Fin n) : BJ ε (Pi.single i 1) (Pi.single j 1) = Formalism.REAL.Jm ε i j := by
  rw [BJ_sum]
  by_cases hij : i = j
  · subst hij
    rw [Finset.sum_eq_single i]
    · simp [Formalism.REAL.Jm, dJ]
    · intro b _ hb
      simp [Pi.single_eq_of_ne hb]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  · rw [show Formalism.REAL.Jm ε i j = 0 by simp [Formalism.REAL.Jm, hij]]
    refine Finset.sum_eq_zero fun l _ => ?_
    by_cases hli : l = i
    · subst hli
      simp [Pi.single_eq_of_ne hij]
    · simp [Pi.single_eq_of_ne hli]

/- English proof (translation)
Conclude with `Complex.conj_eq_iff_re.mp (BJ_herm ε x x)`.
-/
theorem BJ_self_real (x : Fin n → ℂ) : ((BJ ε x x).re : ℂ) = BJ ε x x := by
  exact Complex.conj_eq_iff_re.mp (BJ_herm ε x x)

/- English proof (translation)
Set `L : (Fin n → ℂ) →ₗ[ℂ] (Fin m → ℂ)` to `LinearMap.pi fun b => BJ ε (w b)`. Establish `hW : k ≤ Module.finrank ℂ (LinearMap.ker L)`. Establish `h1` using `LinearMap.finrank_range_add_finrank_ker L`. Establish `h2 : Module.finrank ℂ (LinearMap.range L) ≤ m`. Simplify using `using Submodule.finrank_le (LinearMap.range L)`.

Simplify using `only [Module.finrank_fin_fun] at h1`. Use linear arithmetic over natural numbers and integers. Establish `hker : ∀ (x : LinearMap.ker L) b, BJ ε (w b) (x : Fin n → ℂ) = 0`. Introduce `x b`. Establish `hx` using `x.2`.

Rewrite `hx` using `[LinearMap.mem_ker]`. Conclude with `congrFun hx b`. Take `⟨v, hvli, hvo⟩` from `PI.UnitaryGroupMassFormula.HermConj.exists_orthogonal_family (starRingEnd ℂ) (Module.finrank ℂ (LinearMap.ker L)) (LinearMap.ker L) rfl (fun x y => BJ ε (x : Fin n → ℂ) (y : Fin n → ℂ)) ⟨fun x y z => by simp, fun x a y => by simp, fun x y => by rw [starRingEnd_apply, BJ_herm]⟩`. Use `⟨fun j => ((Real.sqrt (BJ ε (v (Fin.castLE hW j)) (v (Fin.castLE hW j))).re)⁻¹ : ℂ) • ((v (Fin.castLE hW j) : LinearMap.ker L) : Fin n → ℂ), ?_, ?_⟩` and prove the remaining obligations. Introduce `j b`.

Rewrite using `[map_smul, hker, smul_zero]`. Introduce `i j dsimp only`. Simplify using `only [LinearMap.map_smulₛₗ, LinearMap.smul_apply, map_smul, smul_eq_mul, RingHom.id_apply]`. Use `split_ifs with hij`. Substitute `hij set z := ((v (Fin.castLE hW i) : LinearMap.ker L) : Fin n → ℂ) with hzdef` using the available equality.

Establish `hz : z ≠ 0` using `fun h => hvli.ne_zero _ (Submodule.coe_eq_zero.mp h)`. Establish `hp : 0 < (BJ ε z z).re` using `hpos z hz (fun b => hker _ b)`. Establish `hb : BJ ε z z = ((BJ ε z z).re : ℂ)` using `(BJ_self_real ε z).symm`. Use `set r := (BJ ε z z).re with hr`. Rewrite using `[hb]`.

Establish `key : (Real.sqrt r)⁻¹ * ((Real.sqrt r)⁻¹ * r) = 1`. Rewrite using `[← mul_assoc, ← mul_inv, Real.mul_self_sqrt hp.le, inv_mul_cancel₀ hp.ne']`. Rewrite using `[map_inv₀, Complex.conj_ofReal]`. Conclude with `key` after adjusting the coercions. Establish `hne : Fin.castLE hW i ≠ Fin.castLE hW j` using `fun h => hij (Fin.castLE_injective hW h)`.

Establish `h0` using `hvo _ _ hne`. Rewrite using `[h0]`. Simplify using the standard rewrite rules.
-/
theorem exists_orthonormal_perp {m k : ℕ} (hn : n = m + k) (w : Fin m → Fin n → ℂ)
    (hpos : ∀ z : Fin n → ℂ, z ≠ 0 → (∀ b, BJ ε (w b) z = 0) → 0 < (BJ ε z z).re) :
    ∃ u : Fin k → Fin n → ℂ, (∀ j b, BJ ε (w b) (u j) = 0) ∧ ∀ i j, BJ ε (u i) (u j) = if i = j then 1 else 0 := by
  classical
  let L : (Fin n → ℂ) →ₗ[ℂ] (Fin m → ℂ) := LinearMap.pi fun b => BJ ε (w b)
  have hW : k ≤ Module.finrank ℂ (LinearMap.ker L) := by
    have h1 := LinearMap.finrank_range_add_finrank_ker L
    have h2 : Module.finrank ℂ (LinearMap.range L) ≤ m := by
      simpa using Submodule.finrank_le (LinearMap.range L)
    simp only [Module.finrank_fin_fun] at h1
    omega
  have hker : ∀ (x : LinearMap.ker L) b, BJ ε (w b) (x : Fin n → ℂ) = 0 := by
    intro x b
    have hx := x.2
    rw [LinearMap.mem_ker] at hx
    exact congrFun hx b
  obtain ⟨v, hvli, hvo⟩ := PI.UnitaryGroupMassFormula.HermConj.exists_orthogonal_family (starRingEnd ℂ)
    (Module.finrank ℂ (LinearMap.ker L)) (LinearMap.ker L) rfl
    (fun x y => BJ ε (x : Fin n → ℂ) (y : Fin n → ℂ))
    ⟨fun x y z => by simp, fun x a y => by simp, fun x y => by rw [starRingEnd_apply, BJ_herm]⟩
  refine ⟨fun j => ((Real.sqrt (BJ ε (v (Fin.castLE hW j)) (v (Fin.castLE hW j))).re)⁻¹ : ℂ) •
    ((v (Fin.castLE hW j) : LinearMap.ker L) : Fin n → ℂ), ?_, ?_⟩
  · intro j b
    rw [map_smul, hker, smul_zero]
  · intro i j
    dsimp only
    simp only [LinearMap.map_smulₛₗ, LinearMap.smul_apply, map_smul, smul_eq_mul, RingHom.id_apply]
    split_ifs with hij
    · subst hij
      set z := ((v (Fin.castLE hW i) : LinearMap.ker L) : Fin n → ℂ) with hzdef
      have hz : z ≠ 0 := fun h => hvli.ne_zero _ (Submodule.coe_eq_zero.mp h)
      have hp : 0 < (BJ ε z z).re := hpos z hz (fun b => hker _ b)
      have hb : BJ ε z z = ((BJ ε z z).re : ℂ) := (BJ_self_real ε z).symm
      set r := (BJ ε z z).re with hr
      rw [hb]
      have key : (Real.sqrt r)⁻¹ * ((Real.sqrt r)⁻¹ * r) = 1 := by
        rw [← mul_assoc, ← mul_inv, Real.mul_self_sqrt hp.le, inv_mul_cancel₀ hp.ne']
      rw [map_inv₀, Complex.conj_ofReal]
      exact_mod_cast key
    · have hne : Fin.castLE hW i ≠ Fin.castLE hW j := fun h => hij (Fin.castLE_injective hW h)
      have h0 := hvo _ _ hne
      rw [h0]
      simp

/- English proof (translation)
Simplify using `[map_sum, huo]`.
-/
private theorem card_true_ge_lemma {k : ℕ} (u : Fin k → Fin n → ℂ)
    (huo : ∀ i j, BJ ε (u i) (u j) = if i = j then 1 else 0) (c : Fin k → ℂ) (j : Fin k) :
    BJ ε (u j) (∑ l, c l • u l) = c j := by
  simp [map_sum, huo]

/- English proof (translation)
Rewrite using `[map_sum (BJ ε), LinearMap.sum_apply]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.map_smulₛₗ, LinearMap.smul_apply, card_true_ge_lemma ε u huo c l, smul_eq_mul, starRingEnd_apply]`.
-/
private theorem card_true_ge_lemma_2 {k : ℕ} (u : Fin k → Fin n → ℂ)
    (huo : ∀ i j, BJ ε (u i) (u j) = if i = j then 1 else 0) (c : Fin k → ℂ) :
    BJ ε (∑ l, c l • u l) (∑ l, c l • u l) = ∑ l, star (c l) * c l := by
  rw [map_sum (BJ ε), LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, card_true_ge_lemma ε u huo c l, smul_eq_mul,
    starRingEnd_apply]

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.Cut in

/- English proof (translation)
Set `A : (Fin k → ℂ) →ₗ[ℂ] (Fin n → ℂ)` to `∑ l, (LinearMap.proj l).smulRight (u l)`. Establish `hA : ∀ c, A c = ∑ l, c l • u l`. Introduce `c`. Simplify using `[A, LinearMap.sum_apply]`. Set `φ : (Fin k → ℂ) →ₗ[ℂ] ({i // ε i = true} → ℂ)` to `LinearMap.pi fun t => (LinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) t.1).comp A`.

Establish `hinj : Function.Injective φ`. Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce `c hc`. Use `set x := ∑ l, c l • u l with hxdef`. Establish `hx : ∀ i, ε i = true → x i = 0` using `fun i hi => by`.

Establish `h1` using `congrFun hc ⟨i, hi⟩`. Simplify using `only [hxdef, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]`. Simplify `h1` using `[φ, hA]`. Establish `e1` using `card_true_ge_lemma_2 ε u huo c`. Rewrite `e1` using `[← hxdef, BJ_sum]`.

Establish `e2` using `congrArg Complex.re e1`. Rewrite `e2` using `[Complex.re_sum, Complex.re_sum]`. Establish `h1 : ∀ l, (star (c l) * c l).re = Complex.normSq (c l)` using `fun l => by`. Simplify using `[Complex.mul_re, Complex.normSq_apply]`. Establish `h2 : ∀ i, (star (x i) * (dJ ε i * x i)).re ≤ 0`.

Introduce `i`. Unfold `dJ`. Use `split_ifs with hi`. Rewrite using `[hx i hi]`. Simplify using the standard rewrite rules.

Simplify using `[Complex.mul_re]`. Use polynomial arithmetic with `[sq_nonneg (x i).re, sq_nonneg (x i).im]`. Establish `hle : ∑ l, Complex.normSq (c l) ≤ 0`. Rewrite using `[← Finset.sum_congr rfl fun l _ => h1 l, ← e2]`. Conclude with `Finset.sum_nonpos fun i _ => h2 i`.

Establish `hz` using `(Finset.sum_eq_zero_iff_of_nonneg fun l _ => Complex.normSq_nonneg (c l)).mp (le_antisymm hle (Finset.sum_nonneg fun l _ => Complex.normSq_nonneg (c l)))`. Use function extensionality and compare the values at `l`. Conclude with `Complex.normSq_eq_zero.mp (hz l (Finset.mem_univ l))`. Establish `h3` using `LinearMap.finrank_le_finrank_of_injective hinj`. Simplify `h3` using `[Module.finrank_fin_fun, Fintype.card_subtype]`.
-/
theorem card_true_ge {k : ℕ} (u : Fin k → Fin n → ℂ) (huo : ∀ i j, BJ ε (u i) (u j) = if i = j then 1 else 0) :
    k ≤ (univ.filter fun i => ε i = true).card := by
  classical
  let A : (Fin k → ℂ) →ₗ[ℂ] (Fin n → ℂ) := ∑ l, (LinearMap.proj l).smulRight (u l)
  have hA : ∀ c, A c = ∑ l, c l • u l := by
    intro c
    simp [A, LinearMap.sum_apply]
  let φ : (Fin k → ℂ) →ₗ[ℂ] ({i // ε i = true} → ℂ) :=
    LinearMap.pi fun t => (LinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) t.1).comp A
  have hinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro c hc
    set x := ∑ l, c l • u l with hxdef
    have hx : ∀ i, ε i = true → x i = 0 := fun i hi => by
      have h1 := congrFun hc ⟨i, hi⟩
      simp only [hxdef, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      simpa [φ, hA] using h1
    have e1 := card_true_ge_lemma_2 ε u huo c
    rw [← hxdef, BJ_sum] at e1
    have e2 := congrArg Complex.re e1
    rw [Complex.re_sum, Complex.re_sum] at e2
    have h1 : ∀ l, (star (c l) * c l).re = Complex.normSq (c l) := fun l => by
      simp [Complex.mul_re, Complex.normSq_apply]
    have h2 : ∀ i, (star (x i) * (dJ ε i * x i)).re ≤ 0 := by
      intro i
      unfold dJ
      split_ifs with hi
      · rw [hx i hi]
        simp
      · simp [Complex.mul_re]
        nlinarith [sq_nonneg (x i).re, sq_nonneg (x i).im]
    have hle : ∑ l, Complex.normSq (c l) ≤ 0 := by
      rw [← Finset.sum_congr rfl fun l _ => h1 l, ← e2]
      exact Finset.sum_nonpos fun i _ => h2 i
    have hz := (Finset.sum_eq_zero_iff_of_nonneg fun l _ => Complex.normSq_nonneg (c l)).mp
      (le_antisymm hle (Finset.sum_nonneg fun l _ => Complex.normSq_nonneg (c l)))
    funext l
    exact Complex.normSq_eq_zero.mp (hz l (Finset.mem_univ l))
  have h3 := LinearMap.finrank_le_finrank_of_injective hinj
  simpa [Module.finrank_fin_fun, Fintype.card_subtype] using h3

/- English proof (translation)
Conclude with `card_true_ge_lemma ε u huo c j`.
-/
theorem BJ_orth_sum {k : ℕ} (u : Fin k → Fin n → ℂ) (huo : ∀ i j, BJ ε (u i) (u j) = if i = j then 1 else 0)
    (c : Fin k → ℂ) (j : Fin k) : BJ ε (u j) (∑ l, c l • u l) = c j := by
  exact card_true_ge_lemma ε u huo c j

/- English proof (translation)
Simplify using `only [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, map_smul, h]`.
-/
private theorem wittLin_holds_lemma {k : ℕ} (a b : Fin k → Fin n → ℂ)
    (h : ∀ i j, BJ ε (a i) (a j) = BJ ε (b i) (b j)) (c d : Fin k → ℂ) :
    BJ ε (∑ i, c i • a i) (∑ j, d j • a j) = BJ ε (∑ i, c i • b i) (∑ j, d j • b j) := by
  simp only [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, map_smul, h]

/- English proof (translation)
Rewrite using `[BJ_apply]`. Unfold `Formalism.REAL.Jm`. Rewrite using `[Matrix.mul_apply]`. Simplify using `only [Matrix.mul_diagonal]`. Simplify using `[mulVec_diagonal, mulVec_single_one, dotProduct, conjTranspose_apply, mul_assoc]`.
-/
private theorem wittLin_holds_lemma_2 (c : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    (cᴴ * Formalism.REAL.Jm ε * c) i j = BJ ε (c *ᵥ Pi.single i 1) (c *ᵥ Pi.single j 1) := by
  rw [BJ_apply]
  unfold Formalism.REAL.Jm
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal]
  simp [mulVec_diagonal, mulVec_single_one, dotProduct, conjTranspose_apply, mul_assoc]

/- English proof (translation)
Introduce `n m k hn ε w hli hpos`. Establish `hpos' : ∀ z : Fin n → ℂ, z ≠ 0 → (∀ b, BJ ε (w b) z = 0) → 0 < (BJ ε z z).re`. Introduce `z hz h`. Rewrite using `[BJ_apply]`. Conclude with `hpos z hz (fun b => by rw [← BJ_apply]; exact h b)`.

Take `⟨u, hperp, huo⟩` from `exists_orthonormal_perp ε hn w hpos'`. Take `⟨S, hSsub, hScard⟩` from `Finset.exists_subset_card_eq (card_true_ge ε u huo)`. Establish `hST : ∀ i ∈ S, ε i = true` using `fun i hi => (Finset.mem_filter.mp (hSsub hi)).2`. Set `s : Fin k → Fin n` to `fun j => (S.equivFin.symm (Fin.cast hScard.symm j)).1`. Establish `hs_mem : ∀ j, s j ∈ S` using `fun j => (S.equivFin.symm (Fin.cast hScard.symm j)).2`.

Establish `hs_inj : Function.Injective s`. Introduce `a b hab`. Establish `h1` using `S.equivFin.symm.injective (Subtype.ext hab)`. Conclude with `Fin.cast_injective _ h1`. Establish `hs_surj : ∀ i ∈ S, ∃ j, s j = i`.

Introduce `i hi`. Use `⟨Fin.cast hScard (S.equivFin ⟨i, hi⟩), ?_⟩` and prove the remaining obligations. Simplify using `[s]`. Establish `hliu : LinearIndependent ℂ u`. Rewrite using `[Fintype.linearIndependent_iff]`.

Introduce `c hc j`. Establish `h1` using `BJ_orth_sum ε u huo c j`. Rewrite `h1` using `[hc, map_zero]`. Conclude with `h1.symm`. Set `bU` to `Module.Basis.span hliu`.

Set `f : Submodule.span ℂ (Set.range u) →ₗ[ℂ] (Fin n → ℂ)` to `bU.constr ℂ fun j => Pi.single (s j) 1`. Establish `hfb : ∀ j, f (bU j) = Pi.single (s j) 1` using `fun j => bU.constr_basis ℂ _ j`. Establish `hx : ∀ x : Submodule.span ℂ (Set.range u), (x : Fin n → ℂ) = ∑ i, bU.repr x i • u i`. Introduce `x`. Use `conv_lhs => rw [← bU.sum_repr x]`.

Simplify using `[bU, Module.Basis.span_apply]`. Establish `hfx : ∀ x : Submodule.span ℂ (Set.range u), f x = ∑ i, bU.repr x i • Pi.single (s i) 1`. Introduce `x`. Use `conv_lhs => rw [← bU.sum_repr x]`. Rewrite using `[map_sum]`.

Simplify using `only [map_smul, hfb]`. Establish `hgram : ∀ i j, BJ ε (u i) (u j) = BJ ε (Pi.single (s i) 1) (Pi.single (s j) 1)`. Introduce `i j`. Rewrite using `[BJ_single, huo]`. Distinguish the cases in `hij : i = j`.

Substitute `hij` using the available equality. Simplify using `[Formalism.REAL.Jm, hST _ (hs_mem i)]`. Simplify using `[Formalism.REAL.Jm, hij, hs_inj.ne hij]`. Establish `hiso : ∀ x y : Submodule.span ℂ (Set.range u), BJ ε (f x) (f y) = BJ ε x y`. Introduce `x y`.

Rewrite using `[hfx, hfx, hx, hx]`. Conclude with `(wittLin_holds_lemma ε u (fun j => Pi.single (s j) 1) hgram _ _).symm`. Establish `hfinj : Function.Injective f`. Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce `x hx0`.

Establish `hr : ∀ j, bU.repr x j = 0`. Introduce `j`. Establish `h1` using `congrFun ((hfx x).symm.trans hx0) (s j)`. Simplify `h1` using `[Finset.sum_apply, Pi.single_apply, hs_inj.eq_iff]`. Establish `h2 : bU.repr x = 0` using `Finsupp.ext hr`.

Simplify using `using h2`. Take `⟨g, hg, hgU⟩` from `witt_extension_theorem ℂ (Fin n → ℂ) (BJ ε) (BJ_herm ε) (BJ_nondeg ε) _ f hfinj hiso`. Establish `hgu : ∀ j, g (u j) = Pi.single (s j) 1`. Introduce `j`. Establish `h1` using `hgU (bU j)`.

Rewrite `h1` using `[hfb, Module.Basis.span_apply]`. Conclude with `h1`. Set `cM : Matrix (Fin n) (Fin n) ℂ` to `LinearMap.toMatrix' (g.symm : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ))`. Set `dM : Matrix (Fin n) (Fin n) ℂ` to `LinearMap.toMatrix' (g : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ))`. Establish `hcd : cM * dM = 1`.

Rewrite using `[← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_id]`. Use `congr 1`. Use extensionality with `x`. Simplify using the standard rewrite rules. Establish `hdc : dM * cM = 1`.

Rewrite using `[← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_id]`. Use `congr 1`. Use extensionality with `x`. Simplify using the standard rewrite rules. Set `cU : (Matrix (Fin n) (Fin n) ℂ)ˣ` to `⟨cM, dM, hcd, hdc⟩`.

Establish `hmem : cU ∈ Formalism.REAL.UJ ε` using `by show Formalism.REAL.inUJ ε cM`. Unfold `Formalism.REAL.inUJ`. Use extensionality with `i j`. Rewrite using `[wittLin_holds_lemma_2 ε cM i j, ← BJ_single ε i j]`. Simplify using `only [cM, LinearMap.toMatrix'_mulVec, LinearEquiv.coe_coe]`.

Establish `h1` using `hg (g.symm (Pi.single i 1)) (g.symm (Pi.single j 1))`. Simplify using `only [LinearEquiv.apply_symm_apply] at h1`. Conclude with `h1.symm`. Use `⟨S, ⟨cU, hmem⟩, ⟨hScard, hST⟩, ?_⟩` and prove the remaining obligations. Establish `hgw : ∀ b, Formalism.MainNotions.S.uMat (⟨cU, hmem⟩ : Formalism.REAL.UJ ε)⁻¹ *ᵥ w b = g (w b)`.

Introduce `b`. Use `show dM *ᵥ w b = g (w b)`. Conclude with `LinearMap.toMatrix'_mulVec _ _`. Simplify using `only [hgw]`. Apply `Submodule.eq_of_le_of_finrank_le` to reduce the goal to its premises.

Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨b, rfl⟩`. Use `set x := g (w b) with hxb`. Establish `hx0 : ∀ i ∈ S, x i = 0`. Introduce `i hi`.

Take `⟨j, rfl⟩` from `hs_surj i hi`. Establish `h1 : BJ ε (Pi.single (s j) 1) x = 0`. Rewrite using `[← hgu j, hxb, hg, ← BJ_herm, hperp j b, star_zero]`. Rewrite `h1` using `[BJ_sum, Finset.sum_eq_single (s j)]`. Simplify using `only [Pi.single_eq_same, star_one, one_mul] at h1`.

Break down `mul_eq_zero.mp h1 with h2 | h2` into its components or cases. Conclude with `absurd h2 (dJ_ne ε _)`. Conclude with `h2`. Introduce `l _ hl`. Simplify using `[Pi.single_eq_of_ne hl]`.

Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`. Use `show x ∈ Submodule.span ℂ _`. Rewrite using `[← Finset.univ_sum_single x]`. Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations.

Distinguish the cases in `hi : i ∈ S`. Rewrite using `[hx0 i hi, Pi.single_zero]`. Conclude with `Submodule.zero_mem _`. Establish `h1 : Pi.single i (x i) = x i • (Pi.single i 1 : Fin n → ℂ)`. Use extensionality with `l`.

Distinguish the cases in `hl : l = i`. Substitute `hl` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Pi.single_eq_of_ne hl]`. Rewrite using `[h1]`.

Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, by simpa using hi, rfl⟩)`. Establish `hl1 : LinearIndependent ℂ (fun b => g (w b))` using `hli.map' g.toLinearMap g.ker`. Rewrite using `[finrank_span_eq_card hl1, Fintype.card_fin]`. Establish `hset : (fun i : Fin n => (Pi.single i 1 : Fin n → ℂ)) '' (↑S)ᶜ = ↑(Sᶜ.image fun i : Fin n => (Pi.single i 1 : Fin n → ℂ))`. Simplify using `[Finset.coe_image, Finset.coe_compl]`.

Rewrite using `[hset]`. Use `(finrank_span_finset_le_card _).trans ?_` and prove the remaining obligations. Use `Finset.card_image_le.trans ?_` and prove the remaining obligations. Rewrite using `[Finset.card_compl, Fintype.card_fin, hScard]`. Use linear arithmetic over natural numbers and integers.
-/
theorem wittLin_holds : WittLin := by
  intro n m k hn ε w hli hpos
  classical
  have hpos' : ∀ z : Fin n → ℂ, z ≠ 0 → (∀ b, BJ ε (w b) z = 0) → 0 < (BJ ε z z).re := by
    intro z hz h
    rw [BJ_apply]
    exact hpos z hz (fun b => by rw [← BJ_apply]; exact h b)
  obtain ⟨u, hperp, huo⟩ := exists_orthonormal_perp ε hn w hpos'
  obtain ⟨S, hSsub, hScard⟩ := Finset.exists_subset_card_eq (card_true_ge ε u huo)
  have hST : ∀ i ∈ S, ε i = true := fun i hi => (Finset.mem_filter.mp (hSsub hi)).2
  let s : Fin k → Fin n := fun j => (S.equivFin.symm (Fin.cast hScard.symm j)).1
  have hs_mem : ∀ j, s j ∈ S := fun j => (S.equivFin.symm (Fin.cast hScard.symm j)).2
  have hs_inj : Function.Injective s := by
    intro a b hab
    have h1 := S.equivFin.symm.injective (Subtype.ext hab)
    exact Fin.cast_injective _ h1
  have hs_surj : ∀ i ∈ S, ∃ j, s j = i := by
    intro i hi
    refine ⟨Fin.cast hScard (S.equivFin ⟨i, hi⟩), ?_⟩
    simp [s]
  have hliu : LinearIndependent ℂ u := by
    rw [Fintype.linearIndependent_iff]
    intro c hc j
    have h1 := BJ_orth_sum ε u huo c j
    rw [hc, map_zero] at h1
    exact h1.symm
  let bU := Module.Basis.span hliu
  let f : Submodule.span ℂ (Set.range u) →ₗ[ℂ] (Fin n → ℂ) := bU.constr ℂ fun j => Pi.single (s j) 1
  have hfb : ∀ j, f (bU j) = Pi.single (s j) 1 := fun j => bU.constr_basis ℂ _ j
  have hx : ∀ x : Submodule.span ℂ (Set.range u), (x : Fin n → ℂ) = ∑ i, bU.repr x i • u i := by
    intro x
    conv_lhs => rw [← bU.sum_repr x]
    simp [bU, Module.Basis.span_apply]
  have hfx : ∀ x : Submodule.span ℂ (Set.range u), f x = ∑ i, bU.repr x i • Pi.single (s i) 1 := by
    intro x
    conv_lhs => rw [← bU.sum_repr x]
    rw [map_sum]
    simp only [map_smul, hfb]
  have hgram : ∀ i j, BJ ε (u i) (u j) = BJ ε (Pi.single (s i) 1) (Pi.single (s j) 1) := by
    intro i j
    rw [BJ_single, huo]
    by_cases hij : i = j
    · subst hij
      simp [Formalism.REAL.Jm, hST _ (hs_mem i)]
    · simp [Formalism.REAL.Jm, hij, hs_inj.ne hij]
  have hiso : ∀ x y : Submodule.span ℂ (Set.range u), BJ ε (f x) (f y) = BJ ε x y := by
    intro x y
    rw [hfx, hfx, hx, hx]
    exact (wittLin_holds_lemma ε u (fun j => Pi.single (s j) 1) hgram _ _).symm
  have hfinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx0
    have hr : ∀ j, bU.repr x j = 0 := by
      intro j
      have h1 := congrFun ((hfx x).symm.trans hx0) (s j)
      simpa [Finset.sum_apply, Pi.single_apply, hs_inj.eq_iff] using h1
    have h2 : bU.repr x = 0 := Finsupp.ext hr
    simpa using h2
  obtain ⟨g, hg, hgU⟩ := witt_extension_theorem ℂ (Fin n → ℂ) (BJ ε) (BJ_herm ε) (BJ_nondeg ε) _ f hfinj hiso
  have hgu : ∀ j, g (u j) = Pi.single (s j) 1 := by
    intro j
    have h1 := hgU (bU j)
    rw [hfb, Module.Basis.span_apply] at h1
    exact h1
  let cM : Matrix (Fin n) (Fin n) ℂ := LinearMap.toMatrix' (g.symm : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ))
  let dM : Matrix (Fin n) (Fin n) ℂ := LinearMap.toMatrix' (g : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ))
  have hcd : cM * dM = 1 := by
    rw [← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_id]
    congr 1
    ext x
    simp
  have hdc : dM * cM = 1 := by
    rw [← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_id]
    congr 1
    ext x
    simp
  let cU : (Matrix (Fin n) (Fin n) ℂ)ˣ := ⟨cM, dM, hcd, hdc⟩
  have hmem : cU ∈ Formalism.REAL.UJ ε := by
    show Formalism.REAL.inUJ ε cM
    unfold Formalism.REAL.inUJ
    ext i j
    rw [wittLin_holds_lemma_2 ε cM i j, ← BJ_single ε i j]
    simp only [cM, LinearMap.toMatrix'_mulVec, LinearEquiv.coe_coe]
    have h1 := hg (g.symm (Pi.single i 1)) (g.symm (Pi.single j 1))
    simp only [LinearEquiv.apply_symm_apply] at h1
    exact h1.symm
  refine ⟨S, ⟨cU, hmem⟩, ⟨hScard, hST⟩, ?_⟩
  have hgw : ∀ b, Formalism.MainNotions.S.uMat (⟨cU, hmem⟩ : Formalism.REAL.UJ ε)⁻¹ *ᵥ w b = g (w b) := by
    intro b
    show dM *ᵥ w b = g (w b)
    exact LinearMap.toMatrix'_mulVec _ _
  simp only [hgw]
  apply Submodule.eq_of_le_of_finrank_le
  · rw [Submodule.span_le]
    rintro _ ⟨b, rfl⟩
    set x := g (w b) with hxb
    have hx0 : ∀ i ∈ S, x i = 0 := by
      intro i hi
      obtain ⟨j, rfl⟩ := hs_surj i hi
      have h1 : BJ ε (Pi.single (s j) 1) x = 0 := by
        rw [← hgu j, hxb, hg, ← BJ_herm, hperp j b, star_zero]
      rw [BJ_sum, Finset.sum_eq_single (s j)] at h1
      · simp only [Pi.single_eq_same, star_one, one_mul] at h1
        rcases mul_eq_zero.mp h1 with h2 | h2
        · exact absurd h2 (dJ_ne ε _)
        · exact h2
      · intro l _ hl
        simp [Pi.single_eq_of_ne hl]
      · intro h
        exact absurd (Finset.mem_univ _) h
    show x ∈ Submodule.span ℂ _
    rw [← Finset.univ_sum_single x]
    refine Submodule.sum_mem _ fun i _ => ?_
    by_cases hi : i ∈ S
    · rw [hx0 i hi, Pi.single_zero]
      exact Submodule.zero_mem _
    · have h1 : Pi.single i (x i) = x i • (Pi.single i 1 : Fin n → ℂ) := by
        ext l
        by_cases hl : l = i
        · subst hl
          simp
        · simp [Pi.single_eq_of_ne hl]
      rw [h1]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, by simpa using hi, rfl⟩)
  · have hl1 : LinearIndependent ℂ (fun b => g (w b)) := hli.map' g.toLinearMap g.ker
    rw [finrank_span_eq_card hl1, Fintype.card_fin]
    have hset : (fun i : Fin n => (Pi.single i 1 : Fin n → ℂ)) '' (↑S)ᶜ =
        ↑(Sᶜ.image fun i : Fin n => (Pi.single i 1 : Fin n → ℂ)) := by
      simp [Finset.coe_image, Finset.coe_compl]
    rw [hset]
    refine (finrank_span_finset_le_card _).trans ?_
    refine Finset.card_image_le.trans ?_
    rw [Finset.card_compl, Fintype.card_fin, hScard]
    omega

end Lin

end PI.AprimeInfW
