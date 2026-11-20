import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsMoveRight
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemParahoricOfTrivialReduction
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.RedPEqZeroOfDiv
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedK1BlockDecomposition
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

noncomputable section

namespace GlobalTheory.LamRowCong

open GlobalTheory.TopStep

section Gen

variable {E K : Type} [Field E] [NumberField E] [Field K] {P : HeightOneSpectrum (𝓞 E)}

/- English proof (translation)
Establish `hd : redP P A.det = 1` using `by rw [(det_int hA).2, h1, Matrix.det_one]`. Establish `hu : IsUnit (redP P A.det)` using `hd ▸ isUnit_one`. Unfold `LocE.unitV`. Rewrite using `[dif_pos hu]`. Establish `: hu.unit = 1` using `Units.ext (by simp [hd])`.

Rewrite using `[this, map_one, Units.val_one]`.
-/
theorem unitV_det_eq_one (χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) {t : ℕ} (A : Matrix (Fin t) (Fin t) E)
    (hA : ∀ s s', IntAt P (A s s')) (h1 : A.map (redP P) = 1) : LocE.unitV χ A.det = 1 := by
  have hd : redP P A.det = 1 := by rw [(det_int hA).2, h1, Matrix.det_one]
  have hu : IsUnit (redP P A.det) := hd ▸ isUnit_one
  unfold LocE.unitV
  rw [dif_pos hu]
  have : hu.unit = 1 := Units.ext (by simp [hd])
  rw [this, map_one, Units.val_one]

/- English proof (translation)
Establish `hI : ∀ i ∈ Finset.range n, IntAt P (M (a i) (b i))` using `fun i hi => by`. Establish `h` using `hab i (Finset.mem_range.1 hi)`. Conclude with `(hM _ _ h.1 h.2.1).1`. Use `⟨intAt_sum _ hI, ?_⟩` and prove the remaining obligations. Rewrite using `[reduction_sum₂ _ hI]`.

Use `Finset.sum_eq_zero fun i hi => ?_` and prove the remaining obligations. Establish `h` using `hab i (Finset.mem_range.1 hi)`. Rewrite using `[(hM _ _ h.1 h.2.1).2, if_neg h.2.2]`.
-/
theorem sum_red_zero (M : ℕ → ℕ → E) {B : ℕ}
    (hM : ∀ p p', p < B → p' < B → IntAt P (M p p') ∧ redP P (M p p') = if p = p' then 1 else 0)
    (a b : ℕ → ℕ) (n : ℕ) (hab : ∀ i < n, a i < B ∧ b i < B ∧ a i ≠ b i) :
    IntAt P (∑ i ∈ Finset.range n, M (a i) (b i)) ∧ redP P (∑ i ∈ Finset.range n, M (a i) (b i)) = 0 := by
  have hI : ∀ i ∈ Finset.range n, IntAt P (M (a i) (b i)) := fun i hi => by
    have h := hab i (Finset.mem_range.1 hi)
    exact (hM _ _ h.1 h.2.1).1
  refine ⟨intAt_sum _ hI, ?_⟩
  rw [reduction_sum₂ _ hI]
  refine Finset.sum_eq_zero fun i hi => ?_
  have h := hab i (Finset.mem_range.1 hi)
  rw [(hM _ _ h.1 h.2.1).2, if_neg h.2.2]

/- English proof (translation)
Use `Finset.prod_eq_one fun i hi => ?_` and prove the remaining obligations. Establish `hij : i + 1 ≤ j` using `Finset.mem_range.1 hi`. Establish `h2 : i * t + t ≤ j * t`. Use `Nat.mul_le_mul_right t hij` as an intermediate fact. Rewrite `this` using `[Nat.add_mul, one_mul]`. Then use the resulting hypothesis.

Establish `hb : ∀ s : Fin t, r + i * t + s.1 < B` using `fun s => by`. Use `s.2` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Use `unitV_det_eq_one _ _ (fun s s' => (hM _ _ (hb s) (hb s')).1) ?_` and prove the remaining obligations. Use extensionality with `s s'`.

Rewrite using `[Matrix.map_apply, Matrix.of_apply, (hM _ _ (hb s) (hb s')).2, Matrix.one_apply]`. Distinguish the cases in `h : s = s'`. Rewrite using `[if_pos h, if_pos (by rw [h])]`. Rewrite using `[if_neg h, if_neg (fun h' => h (Fin.ext (by omega)))]`.
-/
theorem prod_blocks_eq_one (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (M : ℕ → ℕ → E) {B r t j : ℕ}
    (hM : ∀ p p', p < B → p' < B → IntAt P (M p p') ∧ redP P (M p p') = if p = p' then 1 else 0)
    (hrj : r + j * t ≤ B) :
    ∏ i ∈ Finset.range j, LocE.unitV (χ i) (Matrix.det (Matrix.of fun s s' : Fin t => M (r + i * t + s.1) (r + i * t + s'.1))) = 1 := by
  refine Finset.prod_eq_one fun i hi => ?_
  have hij : i + 1 ≤ j := Finset.mem_range.1 hi
  have h2 : i * t + t ≤ j * t := by
    have := Nat.mul_le_mul_right t hij
    rwa [Nat.add_mul, one_mul] at this
  have hb : ∀ s : Fin t, r + i * t + s.1 < B := fun s => by
    have := s.2
    omega
  refine unitV_det_eq_one _ _ (fun s s' => (hM _ _ (hb s) (hb s')).1) ?_
  ext s s'
  rw [Matrix.map_apply, Matrix.of_apply, (hM _ _ (hb s) (hb s')).2, Matrix.one_apply]
  by_cases h : s = s'
  · rw [if_pos h, if_pos (by rw [h])]
  · rw [if_neg h, if_neg (fun h' => h (Fin.ext (by omega)))]

/- English proof (translation)
Unfold `LocE.lamGv`. Rewrite using `[(sum_red_zero M hM (fun i => i) (fun i => i + 1) (r - 1) fun i hi => ⟨by omega, by omega, by omega⟩).2, AddChar.map_zero_eq_one, one_mul]`. Conclude with `prod_blocks_eq_one χ M hM hrj`.
-/
theorem lamGv_eq_one (ψ₀ : AddChar (𝓞 E ⧸ P.asIdeal) K) (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (M : ℕ → ℕ → E)
    {B r t j : ℕ} (hM : ∀ p p', p < B → p' < B → IntAt P (M p p') ∧ redP P (M p p') = if p = p' then 1 else 0)
    (hr : r ≤ B) (hrj : r + j * t ≤ B) : LocE.lamGv ψ₀ χ r t j M = 1 := by
  unfold LocE.lamGv
  rw [(sum_red_zero M hM (fun i => i) (fun i => i + 1) (r - 1) fun i hi => ⟨by omega, by omega, by omega⟩).2,
    AddChar.map_zero_eq_one, one_mul]
  exact prod_blocks_eq_one χ M hM hrj

/- English proof (translation)
Unfold `LocE.lamGvS`. Establish `h1` using `sum_red_zero M hM (fun i => i) (fun i => i + 1) (k₀ - 1) fun i hi => ⟨by omega, by omega, by omega⟩`. Establish `h2` using `sum_red_zero M hM (fun i => k₀ + i) (fun i => k₀ + i + 1) (r - k₀ - 1) fun i hi => ⟨by omega, by omega, by omega⟩`. Rewrite using `[reduction_add h1.1 h2.1, h1.2, h2.2, add_zero, AddChar.map_zero_eq_one, one_mul]`. Conclude with `prod_blocks_eq_one χ M hM hrj`.
-/
theorem lamGvS_eq_one (ψ₀ : AddChar (𝓞 E ⧸ P.asIdeal) K) (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (M : ℕ → ℕ → E)
    {B k₀ r t j : ℕ} (hM : ∀ p p', p < B → p' < B → IntAt P (M p p') ∧ redP P (M p p') = if p = p' then 1 else 0)
    (hk : k₀ ≤ r) (hr : r ≤ B) (hrj : r + j * t ≤ B) : LocE.lamGvS ψ₀ χ k₀ r t j M = 1 := by
  unfold LocE.lamGvS
  have h1 := sum_red_zero M hM (fun i => i) (fun i => i + 1) (k₀ - 1) fun i hi => ⟨by omega, by omega, by omega⟩
  have h2 := sum_red_zero M hM (fun i => k₀ + i) (fun i => k₀ + i + 1) (r - k₀ - 1)
    fun i hi => ⟨by omega, by omega, by omega⟩
  rw [reduction_add h1.1 h2.1, h1.2, h2.2, add_zero, AddChar.map_zero_eq_one, one_mul]
  exact prod_blocks_eq_one χ M hM hrj

end Gen

section Ent

variable {E : Type} [Field E] [NumberField E] [StarRing E] {P : HeightOneSpectrum (𝓞 E)}

/- English proof (translation)
Unfold `LocE.fIdx`. Apply the tactic sequence `split_ifs <;> omega`.
-/
theorem fIdx_lt {k₀ c n p : ℕ} (hk : k₀ ≤ n) (hp : p < n + c) : LocE.fIdx k₀ c n p < n + c := by
  unfold LocE.fIdx
  split_ifs <;> omega

/- English proof (translation)
Unfold `LocE.fIdx at h`. Apply the tactic sequence `split_ifs at h <;> omega`.
-/
theorem fIdx_inj {k₀ c n p p' : ℕ} (hk : k₀ ≤ n) (hp : p < n + c) (hp' : p' < n + c)
    (h : LocE.fIdx k₀ c n p = LocE.fIdx k₀ c n p') : p = p' := by
  unfold LocE.fIdx at h
  split_ifs at h <;> omega

/- English proof (translation)
Establish `hQ0 : ((qOf P : ℕ) : E) ≠ 0` using `qOf_ne_zero`. Establish `hfl : LocE.fIdx k₀ c n p < n + c` using `fIdx_lt hk hp`. Establish `hfl' : LocE.fIdx k₀ c n p' < n + c` using `fIdx_lt hk hp'`. Establish `hb : IntAt P ((((qOf P : ℕ) : E) ^ LocE.scE n ex (LocE.fIdx k₀ c n p))⁻¹ * (((qOf P : ℕ) : E) ^ LocE.scE n ex (LocE.fIdx k₀ c n p') * y (Loc.eN E (n + c) (LocE.fIdx k₀ c n p')) ⟨_, hfl⟩))`. Establish `h1` using `hy _ (GlobalTheory.CongLevel.bvec_mem P (qOf P) hQ0 (n + c) (LocE.scE n ex) (LocE.fIdx k₀ c n p'))`.

Establish `h2` using `(GlobalTheory.CongLevel.mem_sclLat P (qOf P) (n + c) _ _).1 h1 ⟨_, hfl⟩`. Rewrite `h2` using `[map_smul, Pi.smul_apply, smul_eq_mul]`. Conclude with `h2`. Establish `key : LocE.entB (qOf P) k₀ c n c n ex ex (LinearMap.id + ((qOf P : ℕ) : E) • y) p p' = (if p = p' then 1 else 0) + ((qOf P : ℕ) : E) * ((((qOf P : ℕ) : E) ^ LocE.scE n ex (LocE.fIdx k₀ c n p))⁻¹ * (((qOf P : ℕ) : E) ^ LocE.scE n ex (LocE.fIdx k₀ c n p') * y (Loc.eN E (n + c) (Loc …`. Unfold `LocE.entB Loc.atN`.

Rewrite using `[dif_pos hfl, LinearMap.add_apply, LinearMap.id_apply, LinearMap.smul_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]`. Distinguish the cases in `hpp : p = p'`. Substitute `hpp` using the available equality. Establish `: Loc.eN E (n + c) (LocE.fIdx k₀ c n p) ⟨_, hfl⟩ = 1` using `by simp [Loc.eN]`. Rewrite using `[this, if_pos rfl, sub_self, zpow_zero, mul_one]`.

Establish `h0` using `zpow_ne_zero (LocE.scE n ex (LocE.fIdx k₀ c n p)) hQ0`. Clear the denominators using the available nonvanishing facts. Establish `hff : LocE.fIdx k₀ c n p ≠ LocE.fIdx k₀ c n p'` using `fun h => hpp (fIdx_inj hk hp hp' h)`. Establish `: Loc.eN E (n + c) (LocE.fIdx k₀ c n p') ⟨_, hfl⟩ = 0` using `by simp [Loc.eN, hff]`. Rewrite using `[this, if_neg hpp, zero_add, zero_add, zpow_sub₀ hQ0]`.

Establish `h0` using `zpow_ne_zero (LocE.scE n ex (LocE.fIdx k₀ c n p)) hQ0`. Clear the denominators using the available nonvanishing facts. Establish `hd : IntAt P (if p = p' then (1 : E) else 0)` using `by split_ifs`. Conclude with `intAt_one`. Conclude with `intAt_zero`.

Establish `hqb` using `(intAt_nat (P := P) (qOf P)).mul hb`. Rewrite using `[key]`. Use `⟨hd.add hqb, ?_⟩` and prove the remaining obligations. Rewrite using `[reduction_add hd hqb, reduction_mul (intAt_nat _) hb, reduction_absNorm_eq_zero, zero_mul, add_zero]`. Use `split_ifs`.

Conclude with `reduction_one₂`. Conclude with `reduction_zero`.
-/
theorem entB_one_add_q {k₀ n c : ℕ} (hk : k₀ ≤ n) (ex : ℕ → ℕ) (y : HomE E (n + c) (n + c))
    (hy : ∀ x ∈ LocE.lamY P (qOf P) n c ex, y x ∈ LocE.lamY P (qOf P) n c ex) {p p' : ℕ}
    (hp : p < n + c) (hp' : p' < n + c) :
    IntAt P (LocE.entB (qOf P) k₀ c n c n ex ex (LinearMap.id + ((qOf P : ℕ) : E) • y) p p') ∧
      redP P (LocE.entB (qOf P) k₀ c n c n ex ex (LinearMap.id + ((qOf P : ℕ) : E) • y) p p') =
        if p = p' then 1 else 0 := by
  have hQ0 : ((qOf P : ℕ) : E) ≠ 0 := qOf_ne_zero
  have hfl : LocE.fIdx k₀ c n p < n + c := fIdx_lt hk hp
  have hfl' : LocE.fIdx k₀ c n p' < n + c := fIdx_lt hk hp'
  have hb : IntAt P ((((qOf P : ℕ) : E) ^ LocE.scE n ex (LocE.fIdx k₀ c n p))⁻¹ *
      (((qOf P : ℕ) : E) ^ LocE.scE n ex (LocE.fIdx k₀ c n p') *
        y (Loc.eN E (n + c) (LocE.fIdx k₀ c n p')) ⟨_, hfl⟩)) := by
    have h1 := hy _ (GlobalTheory.CongLevel.bvec_mem P (qOf P) hQ0 (n + c) (LocE.scE n ex) (LocE.fIdx k₀ c n p'))
    have h2 := (GlobalTheory.CongLevel.mem_sclLat P (qOf P) (n + c) _ _).1 h1 ⟨_, hfl⟩
    rw [map_smul, Pi.smul_apply, smul_eq_mul] at h2
    exact h2
  have key : LocE.entB (qOf P) k₀ c n c n ex ex (LinearMap.id + ((qOf P : ℕ) : E) • y) p p' =
      (if p = p' then 1 else 0) + ((qOf P : ℕ) : E) * ((((qOf P : ℕ) : E) ^ LocE.scE n ex (LocE.fIdx k₀ c n p))⁻¹ *
      (((qOf P : ℕ) : E) ^ LocE.scE n ex (LocE.fIdx k₀ c n p') *
        y (Loc.eN E (n + c) (LocE.fIdx k₀ c n p')) ⟨_, hfl⟩)) := by
    unfold LocE.entB Loc.atN
    rw [dif_pos hfl, LinearMap.add_apply, LinearMap.id_apply, LinearMap.smul_apply, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul]
    by_cases hpp : p = p'
    · subst hpp
      have : Loc.eN E (n + c) (LocE.fIdx k₀ c n p) ⟨_, hfl⟩ = 1 := by simp [Loc.eN]
      rw [this, if_pos rfl, sub_self, zpow_zero, mul_one]
      have h0 := zpow_ne_zero (LocE.scE n ex (LocE.fIdx k₀ c n p)) hQ0
      field_simp
    · have hff : LocE.fIdx k₀ c n p ≠ LocE.fIdx k₀ c n p' := fun h => hpp (fIdx_inj hk hp hp' h)
      have : Loc.eN E (n + c) (LocE.fIdx k₀ c n p') ⟨_, hfl⟩ = 0 := by simp [Loc.eN, hff]
      rw [this, if_neg hpp, zero_add, zero_add, zpow_sub₀ hQ0]
      have h0 := zpow_ne_zero (LocE.scE n ex (LocE.fIdx k₀ c n p)) hQ0
      field_simp
  have hd : IntAt P (if p = p' then (1 : E) else 0) := by
    split_ifs
    · exact intAt_one
    · exact intAt_zero
  have hqb := (intAt_nat (P := P) (qOf P)).mul hb
  rw [key]
  refine ⟨hd.add hqb, ?_⟩
  rw [reduction_add hd hqb, reduction_mul (intAt_nat _) hb, reduction_absNorm_eq_zero, zero_mul, add_zero]
  split_ifs
  · exact reduction_one₂
  · exact reduction_zero

end Ent

/- English proof (translation)
Introduce `X Pr R Ch S mu sharp j P hP y hy`. Establish `hm` using `R.two_le_m`. Establish `hk : R.k ≤ R.N j` using `by unfold Ranks.N; omega`. Establish `hkr : R.k ≤ R.r` using `by unfold Ranks.r; omega`. Establish `hNj : R.N j = R.k + j * R.t + j` using `by unfold Ranks.N; ring`.

Establish `hr : R.r ≤ R.N j + cOf R j`. Rewrite using `[hNj]`. Unfold `Ranks.r cOf`. Generalize the expression as in `j * R.t = u`. Use linear arithmetic over natural numbers and integers.

Establish `hrj : R.r + j * R.t ≤ R.N j + cOf R j`. Rewrite using `[hNj]`. Unfold `Ranks.r cOf`. Generalize the expression as in `j * R.t = u`. Use linear arithmetic over natural numbers and integers.

Establish `hy' : ∀ x ∈ LocE.lamY P (qOf P) (R.N j) (cOf R j) (fun i => i + 1), y x ∈ LocE.lamY P (qOf P) (R.N j) (cOf R j) (fun i => i + 1)`. Introduce `x hx`. Establish `h` using `hy x (by unfold lamYat; rw [if_pos hP]; exact hx)`. Unfold `lamYat at h`. Rewrite `h` using `[if_pos hP]`.

Conclude with `h`. Establish `hM` using `fun p p' (hp : p < R.N j + cOf R j) (hp' : p' < R.N j + cOf R j) => entB_one_add_q (k₀ := R.k) hk (fun i => i + 1) y hy' hp hp'`. Unfold `lamRow`. Rewrite using `[if_pos hP]`. Consider the cases of `sharp`.

Simplify using `only [Bool.false_eq_true, if_false]`. Unfold `LocE.lamGB`. Conclude with `lamGv_eq_one _ _ _ hM hr hrj`. Simplify using `only [if_true]`. Unfold `LocE.lamGBS`.

Conclude with `lamGvS_eq_one _ _ _ hM hkr hr hrj`.
-/
theorem lamRow_one_add_q : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (sharp : Bool) (j : ℕ) (P : HeightOneSpectrum (𝓞 X.E)), P ∈ Pr.vGs → ∀ y : HomE X.E (R.N j + cOf R j) (R.N j + cOf R j), (∀ x ∈ lamYat (Pr := Pr) (R := R) j P, y x ∈ lamYat (Pr := Pr) (R := R) j P) → lamRow Ch mu sharp j P (LinearMap.id + (qOf P : X.E) • y) = 1 := by
  intro X Pr R Ch S mu sharp j P hP y hy
  have hm := R.two_le_m
  have hk : R.k ≤ R.N j := by unfold Ranks.N; omega
  have hkr : R.k ≤ R.r := by unfold Ranks.r; omega
  have hNj : R.N j = R.k + j * R.t + j := by unfold Ranks.N; ring
  have hr : R.r ≤ R.N j + cOf R j := by
    rw [hNj]
    unfold Ranks.r cOf
    generalize j * R.t = u
    omega
  have hrj : R.r + j * R.t ≤ R.N j + cOf R j := by
    rw [hNj]
    unfold Ranks.r cOf
    generalize j * R.t = u
    omega
  have hy' : ∀ x ∈ LocE.lamY P (qOf P) (R.N j) (cOf R j) (fun i => i + 1),
      y x ∈ LocE.lamY P (qOf P) (R.N j) (cOf R j) (fun i => i + 1) := by
    intro x hx
    have h := hy x (by unfold lamYat; rw [if_pos hP]; exact hx)
    unfold lamYat at h
    rw [if_pos hP] at h
    exact h
  have hM := fun p p' (hp : p < R.N j + cOf R j) (hp' : p' < R.N j + cOf R j) =>
    entB_one_add_q (k₀ := R.k) hk (fun i => i + 1) y hy' hp hp'
  unfold lamRow
  rw [if_pos hP]
  cases sharp
  · simp only [Bool.false_eq_true, if_false]
    unfold LocE.lamGB
    exact lamGv_eq_one _ _ _ hM hr hrj
  · simp only [if_true]
    unfold LocE.lamGBS
    exact lamGvS_eq_one _ _ _ hM hkr hr hrj

end GlobalTheory.LamRowCong
