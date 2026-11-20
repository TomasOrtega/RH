import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.MemMCoordIdealIffOfIsWeightedHomogeneous
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.Imports
set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def invLine (A : Geo.HermLine ι) : Geo.HermLine ι where
  a := -A.a
  h z := (A.h z)⁻¹
  pos z hz := inv_pos.mpr (A.pos z hz)
  smul c z hc := by
    rw [A.smul c z hc, mul_inv, ← Finset.prod_inv_distrib]
    congr 1
    refine Finset.prod_congr rfl fun k _ ↦ ?_
    rw [Pi.neg_apply, zpow_neg]

def constLine (M : ℝ) (hM : 0 < M) : Geo.HermLine ι where
  a := 0
  h _ := M
  pos _ _ := hM
  smul c z hc := by simp

def powLine (A : Geo.HermLine ι) : ℕ → Geo.HermLine ι
  | 0 => constLine 1 one_pos
  | m + 1 => (powLine A m).tensor A

/- English proof (translation)
The claim follows from `ContDiffOn.inv hA fun z hz ↦ (A.pos z hz).ne'`.
-/
theorem isSmoothHerm_invLine {A : Geo.HermLine ι} (hA : IsSmoothHerm A) : IsSmoothHerm (invLine A) :=
  ContDiffOn.inv hA fun z hz ↦ (A.pos z hz).ne'

/- English proof (translation)
The claim follows from `contDiffOn_const`.
-/
theorem isSmoothHerm_constLine (M : ℝ) (hM : 0 < M) : IsSmoothHerm (constLine (ι := ι) M hM) :=
  contDiffOn_const

/- English proof (translation)
The claim follows from `ContDiffOn.mul hA hB`.
-/
theorem isSmoothHerm_tensor {A B : Geo.HermLine ι} (hA : IsSmoothHerm A) (hB : IsSmoothHerm B) :
    IsSmoothHerm (A.tensor B) :=
  ContDiffOn.mul hA hB

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => exact isSmoothHerm_constLine 1 one_pos`. Consider the case `succ m ih => exact isSmoothHerm_tensor ih hA`.
-/
theorem isSmoothHerm_powLine {A : Geo.HermLine ι} (hA : IsSmoothHerm A) (m : ℕ) :
    IsSmoothHerm (powLine A m) := by
  induction m with
  | zero => exact isSmoothHerm_constLine 1 one_pos
  | succ m ih => exact isSmoothHerm_tensor ih hA

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => simp [powLine, constLine]`. Consider the case `succ m ih`. Simplify using `only [powLine, Geo.HermLine.tensor, Pi.add_apply, ih]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem powLine_a (A : Geo.HermLine ι) (m : ℕ) (k : K) : (powLine A m).a k = m * A.a k := by
  induction m with
  | zero => simp [powLine, constLine]
  | succ m ih =>
    simp only [powLine, Geo.HermLine.tensor, Pi.add_apply, ih]
    push_cast
    ring

/- English proof (translation)
Introduce `m hm k`. Take `⟨m₁, hm₁, m₂, hm₂, rfl⟩` from `Finset.mem_add.mp (support_mul p q hm)`. Simplify using `only [Finsupp.add_apply, Finset.sum_add_distrib, Pi.add_apply, hp m₁ hm₁ k, hq m₂ hm₂ k]`.
-/
theorem isMultiHomog_mul {p q : MRing ι} {a b : K → ℕ} (hp : IsMultiHomog p a)
    (hq : IsMultiHomog q b) : IsMultiHomog (p * q) (a + b) := by
  classical
  intro m hm k
  obtain ⟨m₁, hm₁, m₂, hm₂, rfl⟩ := Finset.mem_add.mp (support_mul p q hm)
  simp only [Finsupp.add_apply, Finset.sum_add_distrib, Pi.add_apply, hp m₁ hm₁ k, hq m₂ hm₂ k]

/- English proof (translation)
Introduce `m hm k`. Rewrite `hm` using `[← C_1, support_C, if_neg one_ne_zero, Finset.mem_singleton]`. Substitute `hm` using the available equality. Simplify using the standard rewrite rules.
-/
theorem isMultiHomog_one : IsMultiHomog (1 : MRing ι) 0 := by
  intro m hm k
  rw [← C_1, support_C, if_neg one_ne_zero, Finset.mem_singleton] at hm
  subst hm
  simp

/- English proof (translation)
Introduce `m hm k`. Rewrite `hm` using `[support_X, Finset.mem_singleton]`. Substitute `hm` using the available equality. Take `⟨k₀, i₀⟩` from `p`. Distinguish the cases in `hk : k = k₀`.

Substitute `hk` using the available equality. Rewrite using `[Pi.single_eq_same, Finset.sum_eq_single i₀]`. Simplify using the standard rewrite rules. Introduce `i _ hi`. Rewrite using `[Finsupp.single_apply, if_neg]`.

Introduce `h`. Conclude with `hi (eq_of_heq (Sigma.mk.inj_iff.mp h).2).symm`. Simplify using the standard rewrite rules. Rewrite using `[Pi.single_eq_of_ne hk]`. Use `Finset.sum_eq_zero fun i _ ↦ ?_` and prove the remaining obligations.

Rewrite using `[Finsupp.single_apply, if_neg]`. Introduce `h`. Conclude with `hk (Sigma.mk.inj_iff.mp h).1.symm`.
-/
theorem isMultiHomog_X [DecidableEq K] (p : Σ k, ι k) : IsMultiHomog (X p : MRing ι) (Pi.single p.1 1) := by
  classical
  intro m hm k
  rw [support_X, Finset.mem_singleton] at hm
  subst hm
  obtain ⟨k₀, i₀⟩ := p
  by_cases hk : k = k₀
  · subst hk
    rw [Pi.single_eq_same, Finset.sum_eq_single i₀]
    · simp
    · intro i _ hi
      rw [Finsupp.single_apply, if_neg]
      intro h
      exact hi (eq_of_heq (Sigma.mk.inj_iff.mp h).2).symm
    · simp
  · rw [Pi.single_eq_of_ne hk]
    refine Finset.sum_eq_zero fun i _ ↦ ?_
    rw [Finsupp.single_apply, if_neg]
    intro h
    exact hk (Sigma.mk.inj_iff.mp h).1.symm

/- English proof (translation)
Proceed by induction on `e with`. Consider the case `zero => simpa using isMultiHomog_one`. Consider the case `succ e ih => rw [pow_succ, succ_nsmul]`. Conclude with `isMultiHomog_mul ih hp`.
-/
theorem isMultiHomog_pow {p : MRing ι} {a : K → ℕ} (hp : IsMultiHomog p a) (e : ℕ) :
    IsMultiHomog (p ^ e) (e • a) := by
  induction e with
  | zero => simpa using isMultiHomog_one
  | succ e ih => rw [pow_succ, succ_nsmul]; exact isMultiHomog_mul ih hp

def chartMon (c : (k : K) → ι k) (d : K → ℕ) : MRing ι :=
  ∏ k, X ⟨k, c k⟩ ^ d k

/- English proof (translation)
Establish `h : ∀ S : Finset K, IsMultiHomog (∏ k ∈ S, (X ⟨k, c k⟩ : MRing ι) ^ d k) (∑ k ∈ S, d k • Pi.single k 1)`. Introduce `S`. Proceed by induction on `S using Finset.induction_on with`. Consider the case `empty => simpa using isMultiHomog_one`. Consider the case `insert k S hk ih`.

Rewrite using `[Finset.prod_insert hk, Finset.sum_insert hk]`. Conclude with `isMultiHomog_mul (isMultiHomog_pow (isMultiHomog_X ⟨k, c k⟩) (d k)) ih`. Establish `e : (∑ k, d k • Pi.single k 1 : K → ℕ) = d`. Use function extensionality and compare the values at `k`. Simplify using `[Finset.sum_apply, Pi.single_apply]`.

Use `h Finset.univ` as an intermediate fact. Rewrite `this` using `[e]`. Then use the resulting hypothesis.
-/
theorem isMultiHomog_chartMon (c : (k : K) → ι k) (d : K → ℕ) :
    IsMultiHomog (chartMon c d) d := by
  classical
  have h : ∀ S : Finset K, IsMultiHomog (∏ k ∈ S, (X ⟨k, c k⟩ : MRing ι) ^ d k)
      (∑ k ∈ S, d k • Pi.single k 1) := by
    intro S
    induction S using Finset.induction_on with
    | empty => simpa using isMultiHomog_one
    | insert k S hk ih =>
      rw [Finset.prod_insert hk, Finset.sum_insert hk]
      exact isMultiHomog_mul (isMultiHomog_pow (isMultiHomog_X ⟨k, c k⟩) (d k)) ih
  have e : (∑ k, d k • Pi.single k 1 : K → ℕ) = d := by
    funext k
    simp [Finset.sum_apply, Pi.single_apply]
  have := h Finset.univ
  rwa [e] at this

/- English proof (translation)
Simplify using `[chartMon]`.
-/
theorem chartMon_zero (c : (k : K) → ι k) : chartMon c 0 = (1 : MRing ι) := by
  simp [chartMon]

/- English proof (translation)
Simplify using `[chartMon, map_prod, map_pow]`.
-/
theorem eval_chartMon (c : (k : K) → ι k) (d : K → ℕ) (z : (Σ k, ι k) → ℂ) :
    eval z (map (Int.castRingHom ℂ) (chartMon c d)) = ∏ k, z ⟨k, c k⟩ ^ d k := by
  simp [chartMon, map_prod, map_pow]

/- English proof (translation)
Establish `hprime : W.IsPrime` using `hW.2.1.1`. Establish `hrel` using `hW.2.1.2.2`. Use `⟨fun k ↦ (hrel k).choose, fun d h ↦ ?_⟩` and prove the remaining obligations. Take `⟨k, -, hk⟩` from `Ideal.IsPrime.prod_mem_iff.mp h`. Conclude with `(hrel k).choose_spec (hprime.mem_of_pow_mem _ hk)`.
-/
theorem exists_chartMon_notMem {W : Ideal (MRing ι)} (hW : IsArithVar W 1) :
    ∃ c : (k : K) → ι k, ∀ d : K → ℕ, chartMon c d ∉ W := by
  have hprime : W.IsPrime := hW.2.1.1
  have hrel := hW.2.1.2.2
  refine ⟨fun k ↦ (hrel k).choose, fun d h ↦ ?_⟩
  obtain ⟨k, -, hk⟩ := Ideal.IsPrime.prod_mem_iff.mp h
  exact (hrel k).choose_spec (hprime.mem_of_pow_mem _ hk)

/- English proof (translation)
Simplify using `[maDensity, mixedDisc]`.
-/
theorem maDensity_fin_zero (φ : Fin 0 → (Fin 0 → ℂ) → ℝ) (y : Fin 0 → ℂ) : maDensity φ y = 1 := by
  simp [maDensity, mixedDisc]

/- English proof (translation)
Use `finsum_nonneg (f := fun a ↦ -f a) fun a ↦ neg_nonneg.mpr (h a)` as an intermediate fact. Rewrite `this` using `[finsum_neg_distrib, neg_nonneg]`. Then use the resulting hypothesis.
-/
theorem finsum_nonpos' {α : Sort*} {f : α → ℝ} (h : ∀ a, f a ≤ 0) : ∑ᶠ a, f a ≤ 0 := by
  have := finsum_nonneg (f := fun a ↦ -f a) fun a ↦ neg_nonneg.mpr (h a)
  rwa [finsum_neg_distrib, neg_nonneg] at this

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `[segre, Finset.prod_mul_distrib]`.
-/
theorem segre_torus_smul (c : K → ℂ) (z : (Σ k, ι k) → ℂ) :
    segre (fun p ↦ c p.1 * z p) = (∏ k, c k) • segre z := by
  funext i
  simp [segre, Finset.prod_mul_distrib]

/- English proof (translation)
Unfold `ptsIntegral ptsIntegralAt`. Use `split_ifs with hΨ`. Use `integral_nonpos fun y ↦ finsum_nonpos' fun w ↦ finsum_nonpos' fun _ ↦ ?_` and prove the remaining obligations. Unfold `sheetDensity`. Use `split_ifs with hγ`.

Rewrite using `[maDensity_fin_zero, mul_one]`. Conclude with `hg _ hγ.choose_spec.2.self_of_nhds.2.1`. Conclude with `le_rfl`. Conclude with `le_rfl`.
-/
theorem ptsIntegral_nonpos (P : Ideal (MRing ι)) (φ : Fin 0 → ((Σ k, ι k) → ℂ) → ℝ)
    {g : ((Σ k, ι k) → ℂ) → ℝ} (hg : ∀ z ∈ mcPts P, g z ≤ 0) : ptsIntegral P φ g ≤ 0 := by
  unfold ptsIntegral ptsIntegralAt
  split_ifs with hΨ
  · refine integral_nonpos fun y ↦ finsum_nonpos' fun w ↦ finsum_nonpos' fun _ ↦ ?_
    unfold sheetDensity
    split_ifs with hγ
    · rw [maDensity_fin_zero, mul_one]
      exact hg _ hγ.choose_spec.2.self_of_nhds.2.1
    · exact le_rfl
  · exact le_rfl

/- English proof (translation)
Unfold `ptsIntegral ptsIntegralAt`. Use `split_ifs with hΨ`. Use `set Ψ := hΨ.choose`. Establish `hvol : (volume : Measure (Fin 0 → ℂ)) = Measure.dirac (fun i ↦ i.elim0)`. Rewrite using `[volume_pi]`.

Conclude with `Measure.pi_of_empty _`. Rewrite using `[hvol, integral_dirac]`. Use `set y₀ : Fin 0 → ℂ := fun i ↦ i.elim0`. Unfold `degC at hP ⊢`. Take `⟨-, hfinQ⟩` from `Nat.card_pos_iff.mp hP`.

Set `r` to `fun z z' : mcPts P ↦ ∃ c : K → ℂ, (∀ k, c k ≠ 0) ∧ (z' : (Σ k, ι k) → ℂ) = fun p ↦ c p.1 * (z : (Σ k, ι k) → ℂ) p`. Set `G : Quot r → (((k : K) → ι k) → ℂ)` to `Quot.lift (fun z : mcPts P ↦ (Ψ (segre (z : (Σ k, ι k) → ℂ)) 0)⁻¹ • segre (z : (Σ k, ι k) → ℂ)) (by`. Introduce and unpack `z z' ⟨c, hc, hz'⟩`. Rewrite using `[hz', segre_torus_smul, map_smul, Pi.smul_apply, smul_eq_mul, smul_smul, mul_inv]`. Establish `hμ : (∏ k, c k) ≠ 0` using `Finset.prod_ne_zero_iff.mpr fun k _ ↦ hc k`.

Use `congr 1`. Use the proof step `field_simp)`. Set `F : fibre P Ψ y₀ → Quot r` to `fun w ↦ Quot.mk r ⟨w.2.choose, w.2.choose_spec.1⟩`. Establish `hGF : ∀ w, G (F w) = w`. Introduce `w`.

Take `⟨h1, h2, h3⟩` from `w.2.choose_spec`. Use `show (Ψ (segre w.2.choose) 0)⁻¹ • segre w.2.choose = (w : ((k : K) → ι k) → ℂ)`. Rewrite using `[h2, h3]`. Simplify using the standard rewrite rules. Establish `hinj : Function.Injective F` using `fun a b hab ↦ Subtype.ext (by`.

Rewrite using `[← hGF a, ← hGF b, hab])`. Establish `: Finite (fibre P Ψ y₀)` using `Finite.of_injective F hinj`. Establish `hcard` using `Nat.card_le_card_of_injective F hinj`. Establish `hfin : (fibre P Ψ y₀).Finite` using `Set.toFinite _`. Rewrite using `[finsum_mem_eq_finite_toFinset_sum _ hfin]`.

Establish `hterm : ∀ w ∈ hfin.toFinset, t ≤ sheetDensity P Ψ φ (fun _ ↦ t) y₀ w`. Introduce `w _`. Unfold `sheetDensity`. Use `split_ifs`. Rewrite using `[maDensity_fin_zero, mul_one]`.

Conclude with `ht`. Establish `hsum` using `Finset.card_nsmul_le_sum _ _ t hterm`. Rewrite `hsum` using `[nsmul_eq_mul]`. Establish `hc : (hfin.toFinset.card : ℝ) ≤ Nat.card (Quot r)`. Rewrite using `[← Set.ncard_eq_toFinset_card _ hfin, ← Nat.card_coe_set_eq]`.

Conclude with `hcard` after adjusting the coercions. Use the polynomial consequences of the given equalities and inequalities. Establish `: (0 : ℝ) ≤ degC P` using `Nat.cast_nonneg _`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem ptsIntegral_const_ge (P : Ideal (MRing ι)) (φ : Fin 0 → ((Σ k, ι k) → ℂ) → ℝ) {t : ℝ}
    (ht : t ≤ 0) (hP : 0 < degC P) : t * degC P ≤ ptsIntegral P φ (fun _ ↦ t) := by
  unfold ptsIntegral ptsIntegralAt
  split_ifs with hΨ
  · set Ψ := hΨ.choose
    have hvol : (volume : Measure (Fin 0 → ℂ)) = Measure.dirac (fun i ↦ i.elim0) := by
      rw [volume_pi]
      exact Measure.pi_of_empty _
    rw [hvol, integral_dirac]
    set y₀ : Fin 0 → ℂ := fun i ↦ i.elim0
    unfold degC at hP ⊢
    obtain ⟨-, hfinQ⟩ := Nat.card_pos_iff.mp hP

    let r := fun z z' : mcPts P ↦
      ∃ c : K → ℂ, (∀ k, c k ≠ 0) ∧ (z' : (Σ k, ι k) → ℂ) = fun p ↦ c p.1 * (z : (Σ k, ι k) → ℂ) p
    let G : Quot r → (((k : K) → ι k) → ℂ) := Quot.lift
      (fun z : mcPts P ↦ (Ψ (segre (z : (Σ k, ι k) → ℂ)) 0)⁻¹ • segre (z : (Σ k, ι k) → ℂ))
      (by
        rintro z z' ⟨c, hc, hz'⟩
        rw [hz', segre_torus_smul, map_smul, Pi.smul_apply, smul_eq_mul, smul_smul, mul_inv]
        have hμ : (∏ k, c k) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ ↦ hc k
        congr 1
        field_simp)
    let F : fibre P Ψ y₀ → Quot r := fun w ↦ Quot.mk r ⟨w.2.choose, w.2.choose_spec.1⟩
    have hGF : ∀ w, G (F w) = w := by
      intro w
      obtain ⟨h1, h2, h3⟩ := w.2.choose_spec
      show (Ψ (segre w.2.choose) 0)⁻¹ • segre w.2.choose = (w : ((k : K) → ι k) → ℂ)
      rw [h2, h3]
      simp
    have hinj : Function.Injective F := fun a b hab ↦ Subtype.ext (by
      rw [← hGF a, ← hGF b, hab])
    have : Finite (fibre P Ψ y₀) := Finite.of_injective F hinj
    have hcard := Nat.card_le_card_of_injective F hinj
    have hfin : (fibre P Ψ y₀).Finite := Set.toFinite _
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
    have hterm : ∀ w ∈ hfin.toFinset, t ≤ sheetDensity P Ψ φ (fun _ ↦ t) y₀ w := by
      intro w _
      unfold sheetDensity
      split_ifs
      · rw [maDensity_fin_zero, mul_one]
      · exact ht
    have hsum := Finset.card_nsmul_le_sum _ _ t hterm
    rw [nsmul_eq_mul] at hsum
    have hc : (hfin.toFinset.card : ℝ) ≤ Nat.card (Quot r) := by
      rw [← Set.ncard_eq_toFinset_card _ hfin, ← Nat.card_coe_set_eq]
      exact_mod_cast hcard
    nlinarith
  · have : (0 : ℝ) ≤ degC P := Nat.cast_nonneg _
    nlinarith

variable (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → Geo.HermLine ι) → ℝ)

/- English proof (translation)
Use function extensionality and compare the values at `i`. Use `fin_cases i`. Both sides reduce to the same expression.
-/
theorem snoc_elim0 (C : Geo.HermLine ι) :
    (Fin.snoc (Fin.elim0 : Fin 0 → Geo.HermLine ι) C : Fin 1 → _) = ![C] := by
  funext i
  fin_cases i
  rfl

/- English proof (translation)
Rewrite using `[geoNum]`. Apply the tactic sequence `split_ifs <;> positivity`.
-/
theorem geoNum_zero_nonneg (V : Ideal (MRing ι)) (a : Fin 0 → K → ℤ) : 0 ≤ geoNum 0 V a := by
  rw [geoNum]
  split_ifs <;> positivity

/- English proof (translation)
Establish `h : divSupp P 1 = ∅`. Use extensionality with `V`. Simplify using `only [divSupp, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]`. Introduce `hV _`. Establish `hp : V.IsPrime` using `hV.1.1`.

Establish `hle : P ⊔ Ideal.span {1} ≤ V` using `hV.1.2`. Rewrite `hle` using `[Ideal.span_singleton_one, sup_top_eq, top_le_iff]`. Conclude with `hp.ne_top hle`. Unfold `recR`. Rewrite using `[h, finsum_mem_empty, zero_sub]`.
-/
theorem recR_one (P : Ideal (MRing ι)) {n : ℕ} (L : Fin n → Geo.HermLine ι) (E : Geo.HermLine ι) :
    recR I P L E 1 = -arInt P 1 E L := by
  have h : divSupp P 1 = ∅ := by
    ext V
    simp only [divSupp, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
    intro hV _
    have hp : V.IsPrime := hV.1.1
    have hle : P ⊔ Ideal.span {1} ≤ V := hV.1.2
    rw [Ideal.span_singleton_one, sup_top_eq, top_le_iff] at hle
    exact hp.ne_top hle
  unfold recR
  rw [h, finsum_mem_empty, zero_sub]

/- English proof (translation)
Establish `h` using `hI.2.2 W 0 Fin.elim0 E s d hW (fun j ↦ j.elim0) hE hd hs hsW`. Rewrite `h` using `[snoc_elim0]`. Then use the resulting hypothesis.
-/
theorem inter_eq_recR (hI : IsIntersectionFamily I) {W : Ideal (MRing ι)} (hW : IsArithVar W 1)
    {E : Geo.HermLine ι} (hE : IsSmoothHerm E) {d : K → ℕ} (hd : ∀ k, E.a k = d k)
    {s : MRing ι} (hs : IsMultiHomog s d) (hsW : s ∉ W) :
    I W 1 ![E] = recR I W (Fin.elim0 : Fin 0 → Geo.HermLine ι) E s := by
  have h := hI.2.2 W 0 Fin.elim0 E s d hW (fun j ↦ j.elim0) hE hd hs hsW
  rwa [snoc_elim0] at h

/- English proof (translation)
Establish `h` using `hI.2.1 W 0 Fin.elim0 A B hW (fun j ↦ j.elim0) hA hB`. Simplify `h` using `only [snoc_elim0]`.
-/
theorem inter_tensor (hI : IsIntersectionFamily I) {W : Ideal (MRing ι)} (hW : IsArithVar W 1)
    {A B : Geo.HermLine ι} (hA : IsSmoothHerm A) (hB : IsSmoothHerm B) :
    I W 1 ![A.tensor B] = I W 1 ![A] + I W 1 ![B] := by
  have h := hI.2.1 W 0 Fin.elim0 A B hW (fun j ↦ j.elim0) hA hB
  simpa only [snoc_elim0] using h

/- English proof (translation)
Take `⟨c, hc⟩` from `exists_chartMon_notMem hW`. Rewrite using `[inter_eq_recR I hI hW hB hd (isMultiHomog_chartMon c d) (hc d), inter_eq_recR I hI hW hB' hd' (isMultiHomog_chartMon c d) (hc d)]`. Conclude with `recR_congr I W Fin.elim0 (chartMon c d) hh`.
-/
theorem inter_congr (hI : IsIntersectionFamily I) {W : Ideal (MRing ι)} (hW : IsArithVar W 1)
    {B B' : Geo.HermLine ι} (hB : IsSmoothHerm B) (hB' : IsSmoothHerm B') {d : K → ℕ}
    (hd : ∀ k, B.a k = d k) (hd' : ∀ k, B'.a k = d k) (hh : ∀ z ∈ mcPts W, B.h z = B'.h z) :
    I W 1 ![B] = I W 1 ![B'] := by
  obtain ⟨c, hc⟩ := exists_chartMon_notMem hW
  rw [inter_eq_recR I hI hW hB hd (isMultiHomog_chartMon c d) (hc d),
    inter_eq_recR I hI hW hB' hd' (isMultiHomog_chartMon c d) (hc d)]
  exact recR_congr I W Fin.elim0 (chartMon c d) hh

/- English proof (translation)
Take `⟨c, hc⟩` from `exists_chartMon_notMem hW`. Rewrite using `[inter_eq_recR I hI hW (isSmoothHerm_constLine 1 one_pos) (d := 0) (fun k ↦ rfl) (isMultiHomog_chartMon c 0) (hc 0), chartMon_zero, recR_one, neg_eq_zero]`. Establish `h : logNorm (constLine (ι` using `ι) 1 one_pos) 1 = fun _ ↦ 0 := by`. Use function extensionality and compare the values at `z`. Simplify using `[logNorm, constLine]`.

Unfold `arInt`. Rewrite using `[h]`. Simplify using `[ptsIntegral, ptsIntegralAt, sheetDensity]`.
-/
theorem inter_constLine_one (hI : IsIntersectionFamily I) {W : Ideal (MRing ι)}
    (hW : IsArithVar W 1) : I W 1 ![constLine 1 one_pos] = 0 := by
  obtain ⟨c, hc⟩ := exists_chartMon_notMem hW
  rw [inter_eq_recR I hI hW (isSmoothHerm_constLine 1 one_pos) (d := 0) (fun k ↦ rfl)
    (isMultiHomog_chartMon c 0) (hc 0), chartMon_zero, recR_one, neg_eq_zero]
  have h : logNorm (constLine (ι := ι) 1 one_pos) 1 = fun _ ↦ 0 := by
    funext z
    simp [logNorm, constLine]
  unfold arInt
  rw [h]
  simp [ptsIntegral, ptsIntegralAt, sheetDensity]

/- English proof (translation)
Establish `h1` using `inter_tensor I hI hW hA (isSmoothHerm_invLine hA)`. Establish `h2 : I W 1 ![A.tensor (invLine A)] = I W 1 ![constLine 1 one_pos]` using `inter_congr I hI hW (isSmoothHerm_tensor hA (isSmoothHerm_invLine hA)) (isSmoothHerm_constLine 1 one_pos) (d := 0) (fun k ↦ by simp [Geo.HermLine.tensor, invLine]) (fun k ↦ rfl) (fun z hz ↦ by`. Simplify using `only [Geo.HermLine.tensor, invLine, constLine]`. Conclude with `mul_inv_cancel₀ (A.pos z hz.1).ne')`. Rewrite `h2` using `[inter_constLine_one I hI hW]`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem inter_invLine (hI : IsIntersectionFamily I) {W : Ideal (MRing ι)} (hW : IsArithVar W 1)
    {A : Geo.HermLine ι} (hA : IsSmoothHerm A) : I W 1 ![invLine A] = -I W 1 ![A] := by
  have h1 := inter_tensor I hI hW hA (isSmoothHerm_invLine hA)
  have h2 : I W 1 ![A.tensor (invLine A)] = I W 1 ![constLine 1 one_pos] :=
    inter_congr I hI hW (isSmoothHerm_tensor hA (isSmoothHerm_invLine hA))
      (isSmoothHerm_constLine 1 one_pos) (d := 0)
      (fun k ↦ by simp [Geo.HermLine.tensor, invLine]) (fun k ↦ rfl)
      (fun z hz ↦ by
        simp only [Geo.HermLine.tensor, invLine, constLine]
        exact mul_inv_cancel₀ (A.pos z hz.1).ne')
  rw [inter_constLine_one I hI hW] at h2
  linarith

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => simpa [powLine] using inter_constLine_one I hI hW`. Consider the case `succ m ih`. Rewrite using `[powLine, inter_tensor I hI hW (isSmoothHerm_powLine hA m) hA, ih]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem inter_powLine (hI : IsIntersectionFamily I) {W : Ideal (MRing ι)} (hW : IsArithVar W 1)
    {A : Geo.HermLine ι} (hA : IsSmoothHerm A) (m : ℕ) :
    I W 1 ![powLine A m] = m * I W 1 ![A] := by
  induction m with
  | zero => simpa [powLine] using inter_constLine_one I hI hW
  | succ m ih =>
    rw [powLine, inter_tensor I hI hW (isSmoothHerm_powLine hA m) hA, ih]
    push_cast
    ring

/- English proof (translation)
Take `⟨c, hc⟩` from `exists_chartMon_notMem hW`. Rewrite using `[inter_eq_recR I hI hW (isSmoothHerm_constLine M hM0) (d := 0) (fun k ↦ rfl) (isMultiHomog_chartMon c 0) (hc 0), chartMon_zero, recR_one]`. Establish `h : logNorm (constLine (ι` using `ι) M hM0) 1 = fun _ ↦ -Real.log M := by`. Use function extensionality and compare the values at `z`. Simplify using `[logNorm, constLine, Real.log_inv]`.

Unfold `arInt`. Rewrite using `[h]`. Use `ptsIntegral_const_ge W (fun j z ↦ Real.log (((Fin.elim0 : Fin 0 → Geo.HermLine ι) j).h z)) (neg_nonpos.mpr (Real.log_nonneg hM)) hdeg` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem inter_constLine_le (hI : IsIntersectionFamily I) {W : Ideal (MRing ι)}
    (hW : IsArithVar W 1) {M : ℝ} (hM0 : 0 < M) (hM : 1 ≤ M) (hdeg : 0 < degC W) :
    I W 1 ![constLine M hM0] ≤ Real.log M * degC W := by
  obtain ⟨c, hc⟩ := exists_chartMon_notMem hW
  rw [inter_eq_recR I hI hW (isSmoothHerm_constLine M hM0) (d := 0) (fun k ↦ rfl)
    (isMultiHomog_chartMon c 0) (hc 0), chartMon_zero, recR_one]
  have h : logNorm (constLine (ι := ι) M hM0) 1 = fun _ ↦ -Real.log M := by
    funext z
    simp [logNorm, constLine, Real.log_inv]
  unfold arInt
  rw [h]
  have := ptsIntegral_const_ge W (fun j z ↦ Real.log (((Fin.elim0 : Fin 0 → Geo.HermLine ι) j).h z))
    (neg_nonpos.mpr (Real.log_nonneg hM)) hdeg
  linarith

/- English proof (translation)
Rewrite using `[inter_eq_recR I hI hW hE hd (isMultiHomog_chartMon c d) hc]`. Establish `h2 : arInt W (chartMon c d) E (Fin.elim0 : Fin 0 → Geo.HermLine ι) ≤ 0` using `ptsIntegral_nonpos _ _ fun z hz ↦ by`. Establish `hpos` using `E.pos z hz.1`. Unfold `logNorm`. Rewrite using `[eval_chartMon]`.

Conclude with `Real.log_nonpos (div_nonneg (norm_nonneg _) hpos.le) ((div_le_one hpos).mpr (hle z hz))`. Unfold `recR`. Rewrite using `[sub_nonneg]`. Use `le_trans h2 (finsum_nonneg fun V ↦ finsum_nonneg fun hV' ↦ ?_)` and prove the remaining obligations. Rewrite using `[if_neg (hV K ι W _ d hW (isMultiHomog_chartMon c d) hc V hV')]`.

Conclude with `mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (Int.cast_nonneg (geoNum_zero_nonneg _ _)) (Real.log_natCast_nonneg _))`.
-/
theorem inter_nonneg (hV : CurveDivVertical.Statement) (hI : IsIntersectionFamily I)
    {W : Ideal (MRing ι)} (hW : IsArithVar W 1) {E : Geo.HermLine ι} (hE : IsSmoothHerm E)
    {d : K → ℕ} (hd : ∀ k, E.a k = d k) (c : (k : K) → ι k) (hc : chartMon c d ∉ W)
    (hle : ∀ z ∈ mcPts W, ‖∏ k, z ⟨k, c k⟩ ^ d k‖ ≤ E.h z) : 0 ≤ I W 1 ![E] := by
  rw [inter_eq_recR I hI hW hE hd (isMultiHomog_chartMon c d) hc]
  have h2 : arInt W (chartMon c d) E (Fin.elim0 : Fin 0 → Geo.HermLine ι) ≤ 0 :=
    ptsIntegral_nonpos _ _ fun z hz ↦ by
      have hpos := E.pos z hz.1
      unfold logNorm
      rw [eval_chartMon]
      exact Real.log_nonpos (div_nonneg (norm_nonneg _) hpos.le)
        ((div_le_one hpos).mpr (hle z hz))
  unfold recR
  rw [sub_nonneg]
  refine le_trans h2 (finsum_nonneg fun V ↦ finsum_nonneg fun hV' ↦ ?_)
  rw [if_neg (hV K ι W _ d hW (isMultiHomog_chartMon c d) hc V hV')]
  exact mul_nonneg (Nat.cast_nonneg _)
    (mul_nonneg (Int.cast_nonneg (geoNum_zero_nonneg _ _)) (Real.log_natCast_nonneg _))

/- English proof (translation)
Use `set U : Set ((Σ k, ι k) → ℂ) := {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0}`. Use `set S : Set ((Σ k, ι k) → ℂ) := {z | ∀ k, ∑ i, ‖z ⟨k, i⟩‖ ^ 2 = 1}`. Establish `hsq : ∀ (z : (Σ k, ι k) → ℂ) (k : K) (i : ι k), ‖z ⟨k, i⟩‖ ^ 2 ≤ ∑ i', ‖z ⟨k, i'⟩‖ ^ 2` using `fun z k i ↦ Finset.single_le_sum (f := fun i' ↦ ‖z ⟨k, i'⟩‖ ^ 2) (fun _ _ ↦ sq_nonneg _) (Finset.mem_univ i)`. Establish `hSU : S ⊆ U`. Introduce `z hz k`.

Assume the negation of the conclusion as `h`. Use `push Not at h`. Use `hz k` as an intermediate fact. Simplify using `[h] at this`. Establish `hS_le : ∀ z ∈ S, ∀ p, ‖z p‖ ≤ 1`.

Introduce `z hz p`. Establish `h1 : ‖z ⟨p.1, p.2⟩‖ ^ 2 ≤ 1` using `(hz p.1) ▸ hsq z p.1 p.2`. Use polynomial arithmetic with `[norm_nonneg (z p)]`. Establish `hSc : IsCompact S`. Use `Metric.isCompact_of_isClosed_isBounded ?_ ?_` and prove the remaining obligations.

Establish `: S = ⋂ k, (fun z : (Σ k, ι k) → ℂ ↦ ∑ i, ‖z ⟨k, i⟩‖ ^ 2) ⁻¹' {1}`. Use extensionality with `z`. Simplify using `[S]`. Rewrite using `[this]`. Conclude with `isClosed_iInter fun k ↦ isClosed_singleton.preimage (by fun_prop)`.

Use `(Metric.isBounded_closedBall (x := 0) (r := 1)).subset fun z hz ↦ ?_` and prove the remaining obligations. Rewrite using `[Metric.mem_closedBall, dist_zero_right]`. Conclude with `(pi_norm_le_iff_of_nonneg zero_le_one).mpr (hS_le z hz)`. Establish `hcont : ContinuousOn (fun z ↦ (E.h z)⁻¹) S` using `(hE.continuousOn.mono hSU).inv₀ fun z hz ↦ (E.pos z (hSU hz)).ne'`. Take `⟨M₀, hM₀⟩` from `hSc.bddAbove_image hcont`.

Use `⟨max M₀ 1, le_max_right _ _, fun c z hz ↦ ?_⟩` and prove the remaining obligations. Use `set r : K → ℝ := fun k ↦ Real.sqrt (∑ i, ‖z ⟨k, i⟩‖ ^ 2)`. Establish `hsum : ∀ k, 0 < ∑ i, ‖z ⟨k, i⟩‖ ^ 2`. Introduce `k`. Take `⟨i, hi⟩` from `hz k`.

Conclude with `lt_of_lt_of_le (by positivity) (hsq z k i)`. Establish `hr : ∀ k, 0 < r k` using `fun k ↦ Real.sqrt_pos.mpr (hsum k)`. Use `set t : K → ℂ := fun k ↦ (((r k)⁻¹ : ℝ) : ℂ)`. Establish `hnt : ∀ k, ‖t k‖ = (r k)⁻¹` using `fun k ↦ by`. Simplify using `[t, abs_of_pos (hr k)]`.

Establish `ht : ∀ k, t k ≠ 0` using `fun k ↦ by`. Rewrite using `[← norm_ne_zero_iff, hnt]`. Conclude with `(inv_pos.mpr (hr k)).ne'`. Use `set w : (Σ k, ι k) → ℂ := fun p ↦ t p.1 * z p`. Establish `hw : w ∈ S`.

Introduce `k`. Simplify using `only [w, norm_mul, mul_pow, ← Finset.mul_sum, hnt, inv_pow]`. Rewrite using `[Real.sq_sqrt (hsum k).le]`. Conclude with `inv_mul_cancel₀ (hsum k).ne'`. Establish `hEw : E.h w = (∏ k, ‖t k‖ ^ d k) * E.h z`.

Rewrite using `[E.smul t z ht]`. Use `congr 1`. Use `Finset.prod_congr rfl fun k _ ↦ ?_` and prove the remaining obligations. Rewrite using `[hd k, zpow_natCast]`. Establish `hmon : ‖∏ k, w ⟨k, c k⟩ ^ d k‖ = (∏ k, ‖t k‖ ^ d k) * ‖∏ k, z ⟨k, c k⟩ ^ d k‖`.

Simplify using `only [w, mul_pow, Finset.prod_mul_distrib, norm_mul, norm_prod, norm_pow]`. Establish `hmon1 : ‖∏ k, w ⟨k, c k⟩ ^ d k‖ ≤ 1`. Rewrite using `[norm_prod]`. Conclude with `Finset.prod_le_one (fun _ _ ↦ norm_nonneg _) fun k _ ↦ by`. Rewrite using `[norm_pow]`.

Conclude with `pow_le_one₀ (norm_nonneg _) (hS_le w hw _)`. Establish `hEw1 : 1 ≤ max M₀ 1 * E.h w`. Establish `h1 : (E.h w)⁻¹ ≤ M₀` using `hM₀ (Set.mem_image_of_mem _ hw)`. Establish `hpos` using `E.pos w (hSU hw)`. Combine the equalities or inequalities in the displayed calculation.

Establish `hT : 0 < ∏ k, ‖t k‖ ^ d k` using `Finset.prod_pos fun k _ ↦ pow_pos (norm_pos_iff.mpr (ht k)) _`. Establish `key : (∏ k, ‖t k‖ ^ d k) * ‖∏ k, z ⟨k, c k⟩ ^ d k‖ ≤ (∏ k, ‖t k‖ ^ d k) * (max M₀ 1 * E.h z)`. Rewrite using `[← hmon]`. Combine the equalities or inequalities in the displayed calculation. Conclude with `le_of_mul_le_mul_left key hT`.
-/
theorem exists_chartMon_bound {E : Geo.HermLine ι} (hE : IsSmoothHerm E) {d : K → ℕ}
    (hd : ∀ k, E.a k = d k) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ (c : (k : K) → ι k) (z : (Σ k, ι k) → ℂ), (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) →
      ‖∏ k, z ⟨k, c k⟩ ^ d k‖ ≤ M * E.h z := by
  set U : Set ((Σ k, ι k) → ℂ) := {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0}
  set S : Set ((Σ k, ι k) → ℂ) := {z | ∀ k, ∑ i, ‖z ⟨k, i⟩‖ ^ 2 = 1}
  have hsq : ∀ (z : (Σ k, ι k) → ℂ) (k : K) (i : ι k),
      ‖z ⟨k, i⟩‖ ^ 2 ≤ ∑ i', ‖z ⟨k, i'⟩‖ ^ 2 := fun z k i ↦
    Finset.single_le_sum (f := fun i' ↦ ‖z ⟨k, i'⟩‖ ^ 2) (fun _ _ ↦ sq_nonneg _)
      (Finset.mem_univ i)
  have hSU : S ⊆ U := by
    intro z hz k
    by_contra h
    push Not at h
    have := hz k
    simp [h] at this
  have hS_le : ∀ z ∈ S, ∀ p, ‖z p‖ ≤ 1 := by
    intro z hz p
    have h1 : ‖z ⟨p.1, p.2⟩‖ ^ 2 ≤ 1 := (hz p.1) ▸ hsq z p.1 p.2
    nlinarith [norm_nonneg (z p)]
  have hSc : IsCompact S := by
    refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
    · have : S = ⋂ k, (fun z : (Σ k, ι k) → ℂ ↦ ∑ i, ‖z ⟨k, i⟩‖ ^ 2) ⁻¹' {1} := by
        ext z
        simp [S]
      rw [this]
      exact isClosed_iInter fun k ↦ isClosed_singleton.preimage (by fun_prop)
    · refine (Metric.isBounded_closedBall (x := 0) (r := 1)).subset fun z hz ↦ ?_
      rw [Metric.mem_closedBall, dist_zero_right]
      exact (pi_norm_le_iff_of_nonneg zero_le_one).mpr (hS_le z hz)
  have hcont : ContinuousOn (fun z ↦ (E.h z)⁻¹) S :=
    (hE.continuousOn.mono hSU).inv₀ fun z hz ↦ (E.pos z (hSU hz)).ne'
  obtain ⟨M₀, hM₀⟩ := hSc.bddAbove_image hcont
  refine ⟨max M₀ 1, le_max_right _ _, fun c z hz ↦ ?_⟩
  set r : K → ℝ := fun k ↦ Real.sqrt (∑ i, ‖z ⟨k, i⟩‖ ^ 2)
  have hsum : ∀ k, 0 < ∑ i, ‖z ⟨k, i⟩‖ ^ 2 := by
    intro k
    obtain ⟨i, hi⟩ := hz k
    exact lt_of_lt_of_le (by positivity) (hsq z k i)
  have hr : ∀ k, 0 < r k := fun k ↦ Real.sqrt_pos.mpr (hsum k)
  set t : K → ℂ := fun k ↦ (((r k)⁻¹ : ℝ) : ℂ)
  have hnt : ∀ k, ‖t k‖ = (r k)⁻¹ := fun k ↦ by
    simp [t, abs_of_pos (hr k)]
  have ht : ∀ k, t k ≠ 0 := fun k ↦ by
    rw [← norm_ne_zero_iff, hnt]
    exact (inv_pos.mpr (hr k)).ne'
  set w : (Σ k, ι k) → ℂ := fun p ↦ t p.1 * z p
  have hw : w ∈ S := by
    intro k
    simp only [w, norm_mul, mul_pow, ← Finset.mul_sum, hnt, inv_pow]
    rw [Real.sq_sqrt (hsum k).le]
    exact inv_mul_cancel₀ (hsum k).ne'
  have hEw : E.h w = (∏ k, ‖t k‖ ^ d k) * E.h z := by
    rw [E.smul t z ht]
    congr 1
    refine Finset.prod_congr rfl fun k _ ↦ ?_
    rw [hd k, zpow_natCast]
  have hmon : ‖∏ k, w ⟨k, c k⟩ ^ d k‖ = (∏ k, ‖t k‖ ^ d k) * ‖∏ k, z ⟨k, c k⟩ ^ d k‖ := by
    simp only [w, mul_pow, Finset.prod_mul_distrib, norm_mul, norm_prod, norm_pow]
  have hmon1 : ‖∏ k, w ⟨k, c k⟩ ^ d k‖ ≤ 1 := by
    rw [norm_prod]
    exact Finset.prod_le_one (fun _ _ ↦ norm_nonneg _) fun k _ ↦ by
      rw [norm_pow]
      exact pow_le_one₀ (norm_nonneg _) (hS_le w hw _)
  have hEw1 : 1 ≤ max M₀ 1 * E.h w := by
    have h1 : (E.h w)⁻¹ ≤ M₀ := hM₀ (Set.mem_image_of_mem _ hw)
    have hpos := E.pos w (hSU hw)
    calc (1 : ℝ) = (E.h w)⁻¹ * E.h w := (inv_mul_cancel₀ hpos.ne').symm
      _ ≤ max M₀ 1 * E.h w := mul_le_mul_of_nonneg_right (h1.trans (le_max_left _ _)) hpos.le
  have hT : 0 < ∏ k, ‖t k‖ ^ d k :=
    Finset.prod_pos fun k _ ↦ pow_pos (norm_pos_iff.mpr (ht k)) _
  have key : (∏ k, ‖t k‖ ^ d k) * ‖∏ k, z ⟨k, c k⟩ ^ d k‖ ≤
      (∏ k, ‖t k‖ ^ d k) * (max M₀ 1 * E.h z) := by
    rw [← hmon]
    calc ‖∏ k, w ⟨k, c k⟩ ^ d k‖ ≤ 1 := hmon1
      _ ≤ max M₀ 1 * E.h w := hEw1
      _ = (∏ k, ‖t k‖ ^ d k) * (max M₀ 1 * E.h z) := by rw [hEw]; ring
  exact le_of_mul_le_mul_left key hT

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet
