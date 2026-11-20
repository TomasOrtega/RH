import Formalism.SharpRestriction.Divisibility.GeneratorPowers.CIndFrFix
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FBIdJet
import ReciprocityTheory.ReductiveGroups.Models.FiniteGeneration.FiniteGenerationProofs.SolveV

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp2a

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.FG.SolveVAux Formalism.L2.Pj

variable {S : Type} [CommRing S]

/- English proof (translation)
Introduce `e he`. Rewrite using `[map_smul, hp e he, smul_zero]`.
-/
theorem low_smul {τ : Type} {N : ℕ} (a : S) {p : MvPowerSeries τ S} (hp : Low N p) : Low N (a • p) := by
  intro e he
  rw [map_smul, hp e he, smul_zero]

/- English proof (translation)
Conclude with `Finset.sum_induction _ (Low N) (fun _ _ h1 h2 => low_add h1 h2) (fun e _ => by simp) hp`.
-/
theorem low_sum {τ ι : Type} {N : ℕ} (s : Finset ι) {p : ι → MvPowerSeries τ S} (hp : ∀ i ∈ s, Low N (p i)) :
    Low N (∑ i ∈ s, p i) := by
  exact Finset.sum_induction _ (Low N) (fun _ _ h1 h2 => low_add h1 h2) (fun e _ => by simp) hp

/- English proof (translation)
Establish `hk0 : ∀ i, constantCoeff (k i) = 0` using `fun i => (low_one_iff _).1 (hk i)`. Establish `ha : HasSubst k` using `⟨fun s => by rw [hk0 s]; exact IsNilpotent.zero, fun _ => Set.toFinite _⟩`. Establish `key : ∀ (m : ι →₀ ℕ) (t : Finset ι), Low (∑ s ∈ t, m s) (∏ s ∈ t, k s ^ m s)`. Introduce `m t`. Use `Finset.induction_on t ?_ ?_` and prove the remaining obligations.

Rewrite using `[Finset.sum_empty]`. Conclude with `low_zero _`. Introduce `a t hat ih`. Rewrite using `[Finset.sum_insert hat, Finset.prod_insert hat]`. Conclude with `low_mul (low_pow (hk a) (m a)) ih`.

Introduce `e he`. Establish `hz : ∀ m : ι →₀ ℕ, coeff m g • coeff e (m.prod fun s n => k s ^ n) = 0`. Introduce `m`. Distinguish the cases in `hm : m.degree < N`. Rewrite using `[hg m hm, zero_smul]`.

Establish `hprod : Low m.degree (m.prod fun s n => k s ^ n)` using `key m m.support`. Rewrite using `[hprod e (lt_of_lt_of_le he (not_lt.mp hm)), smul_zero]`. Rewrite using `[coeff_subst ha]`. Simplify using `only [hz, finsum_zero]`.
-/
theorem low_subst' {ι τ : Type} [Finite ι] {N : ℕ} {k : ι → MvPowerSeries τ S} (hk : ∀ i, Low 1 (k i))
    {g : MvPowerSeries ι S} (hg : Low N g) : Low N (subst k g) := by
  classical
  have hk0 : ∀ i, constantCoeff (k i) = 0 := fun i => (low_one_iff _).1 (hk i)
  have ha : HasSubst k := ⟨fun s => by rw [hk0 s]; exact IsNilpotent.zero, fun _ => Set.toFinite _⟩
  have key : ∀ (m : ι →₀ ℕ) (t : Finset ι), Low (∑ s ∈ t, m s) (∏ s ∈ t, k s ^ m s) := by
    intro m t
    refine Finset.induction_on t ?_ ?_
    · rw [Finset.sum_empty]
      exact low_zero _
    · intro a t hat ih
      rw [Finset.sum_insert hat, Finset.prod_insert hat]
      exact low_mul (low_pow (hk a) (m a)) ih
  intro e he
  have hz : ∀ m : ι →₀ ℕ, coeff m g • coeff e (m.prod fun s n => k s ^ n) = 0 := by
    intro m
    by_cases hm : m.degree < N
    · rw [hg m hm, zero_smul]
    · have hprod : Low m.degree (m.prod fun s n => k s ^ n) := key m m.support
      rw [hprod e (lt_of_lt_of_le he (not_lt.mp hm)), smul_zero]
  rw [coeff_subst ha]
  simp only [hz, finsum_zero]

variable [Algebra ℚ S] {d : ℕ}

/- English proof (translation)
Introduce `e he`. Distinguish the cases in `hz : e = 0`. Substitute `hz` using the available equality. Rewrite using `[coeff_zero_eq_constantCoeff_apply]`. Conclude with `h0`.

Take `⟨w, hw⟩` from `Finsupp.support_nonempty_iff.mpr hz`. Establish `hdeg : e.degree = ∑ s ∈ e.support, e s` using `rfl`. Rewrite `he` using `[hdeg]`. Establish `hw1 : 1 ≤ e w` using `Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hw)`. Establish `hwle : e w ≤ ∑ s ∈ e.support, e s` using `Finset.single_le_sum (fun _ _ => Nat.zero_le _) hw`.

Establish `hew : e w = 1` using `by omega`. Establish `hv : ∀ v, v ≠ w → e v = 0`. Introduce `v hvw`. Assume the negation of the conclusion as `hne`. Establish `hvs : v ∈ e.support` using `Finsupp.mem_support_iff.mpr hne`.

Establish `hsub : ({v, w} : Finset σ) ⊆ e.support` using `Finset.insert_subset_iff.mpr ⟨hvs, Finset.singleton_subset_iff.mpr hw⟩`. Establish `hle` using `Finset.sum_le_sum_of_subset (f := fun s => e s) hsub`. Rewrite `hle` using `[Finset.sum_pair hvw]`. Establish `hv1 : 1 ≤ e v` using `Nat.one_le_iff_ne_zero.mpr hne`. Use linear arithmetic over natural numbers and integers.

Establish `he1 : e = Finsupp.single w 1`. Use extensionality with `v`. Distinguish the cases in `hvw : v = w`. Substitute `hvw` using the available equality. Simplify using `[hew]`.

Rewrite using `[hv v hvw, Finsupp.single_apply, if_neg (Ne.symm hvw)]`. Rewrite using `[he1]`. Conclude with `h1 w`.
-/
private lemma low_two_of_lemma {σ : Type} {f : MvPowerSeries σ S} (h0 : constantCoeff f = 0)
    (h1 : ∀ w, coeff (Finsupp.single w 1) f = 0) : Low 2 f := by
  classical
  intro e he
  by_cases hz : e = 0
  · subst hz
    rw [coeff_zero_eq_constantCoeff_apply]
    exact h0
  · obtain ⟨w, hw⟩ := Finsupp.support_nonempty_iff.mpr hz
    have hdeg : e.degree = ∑ s ∈ e.support, e s := rfl
    rw [hdeg] at he
    have hw1 : 1 ≤ e w := Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hw)
    have hwle : e w ≤ ∑ s ∈ e.support, e s := Finset.single_le_sum (fun _ _ => Nat.zero_le _) hw
    have hew : e w = 1 := by omega
    have hv : ∀ v, v ≠ w → e v = 0 := by
      intro v hvw
      by_contra hne
      have hvs : v ∈ e.support := Finsupp.mem_support_iff.mpr hne
      have hsub : ({v, w} : Finset σ) ⊆ e.support :=
        Finset.insert_subset_iff.mpr ⟨hvs, Finset.singleton_subset_iff.mpr hw⟩
      have hle := Finset.sum_le_sum_of_subset (f := fun s => e s) hsub
      rw [Finset.sum_pair hvw] at hle
      have hv1 : 1 ≤ e v := Nat.one_le_iff_ne_zero.mpr hne
      omega
    have he1 : e = Finsupp.single w 1 := by
      ext v
      by_cases hvw : v = w
      · subst hvw
        simp [hew]
      · rw [hv v hvw, Finsupp.single_apply, if_neg (Ne.symm hvw)]
    rw [he1]
    exact h1 w

/- English proof (translation)
Establish `ha : HasSubst a` using `⟨fun s => by rw [ha0 s]; exact IsNilpotent.zero, fun _ => Set.toFinite _⟩`. Establish `hR : Low 1 (f - coeff 0 f • (1 : MvPowerSeries σ S))`. Rewrite using `[low_one_iff, ← coeff_zero_eq_constantCoeff_apply, map_sub, map_smul, coeff_zero_one, smul_eq_mul, mul_one, sub_self]`. Establish `hS : Low 1 (subst a (f - coeff 0 f • (1 : MvPowerSeries σ S)))` using `low_subst (fun s => (low_one_iff _).2 (ha0 s)) hR`. Establish `hsub : subst a (f - coeff 0 f • (1 : MvPowerSeries σ S)) =`.

Substitute `a f - coeff 0 f • (1 : MvPowerSeries τ S) := by` using the available equality. Rewrite using `[← coe_substAlgHom ha, map_sub, map_smul, map_one]`. Rewrite `hS` using `[hsub]`. Establish `h0` using `hS 0 (by simp)`. Rewrite `h0` using `[map_sub, map_smul, coeff_zero_one, smul_eq_mul, mul_one, sub_eq_zero]`.

Conclude with `h0`.
-/
private lemma cc_subst_lemma_2 {σ τ : Type} [Finite σ] {a : σ → MvPowerSeries τ S}
    (ha0 : ∀ s, constantCoeff (a s) = 0) (f : MvPowerSeries σ S) :
    coeff 0 (subst a f) = coeff 0 f := by
  have ha : HasSubst a := ⟨fun s => by rw [ha0 s]; exact IsNilpotent.zero, fun _ => Set.toFinite _⟩
  have hR : Low 1 (f - coeff 0 f • (1 : MvPowerSeries σ S)) := by
    rw [low_one_iff, ← coeff_zero_eq_constantCoeff_apply, map_sub, map_smul, coeff_zero_one, smul_eq_mul,
      mul_one, sub_self]
  have hS : Low 1 (subst a (f - coeff 0 f • (1 : MvPowerSeries σ S))) :=
    low_subst (fun s => (low_one_iff _).2 (ha0 s)) hR
  have hsub : subst a (f - coeff 0 f • (1 : MvPowerSeries σ S)) =
      subst a f - coeff 0 f • (1 : MvPowerSeries τ S) := by
    rw [← coe_substAlgHom ha, map_sub, map_smul, map_one]
  rw [hsub] at hS
  have h0 := hS 0 (by simp)
  rw [map_sub, map_smul, coeff_zero_one, smul_eq_mul, mul_one, sub_eq_zero] at h0
  exact h0

/- English proof (translation)
Establish `ha : HasSubst a` using `⟨fun s => by rw [ha0 s]; exact IsNilpotent.zero, fun _ => Set.toFinite _⟩`. Establish `hR : Low 2 (f - ∑ s, coeff (Finsupp.single s 1) f • X s)`. Apply `low_two_of_lemma` to reduce the goal to its premises. Rewrite using `[← coeff_zero_eq_constantCoeff_apply, map_sub, map_sum]`. Simplify using `only [map_smul, coeff_zero_X, smul_zero, Finset.sum_const_zero, sub_zero]`.

Rewrite using `[coeff_zero_eq_constantCoeff_apply]`. Conclude with `hf0`. Introduce `v`. Simplify using `[coeff_X, Finsupp.single_left_inj Nat.one_ne_zero]`. Establish `hS` using `low_subst' (fun s => (low_one_iff _).2 (ha0 s)) hR`.

Establish `hsplit : subst a f = subst a (f - ∑ s, coeff (Finsupp.single s 1) f • X s) + ∑ s, coeff (Finsupp.single s 1) f • a s`. Rewrite using `[← coe_substAlgHom ha, map_sub, map_sum]`. Simplify using `only [map_smul]`. Simplify using `only [coe_substAlgHom, subst_X ha, sub_add_cancel]`. Rewrite using `[hsplit, map_add, hS (Finsupp.single w 1) (by simp), zero_add, map_sum]`.

Simplify using `only [map_smul, smul_eq_mul]`.
-/
private lemma lin_subst_lemma_3 {σ τ : Type} [Fintype σ] {a : σ → MvPowerSeries τ S}
    (ha0 : ∀ s, constantCoeff (a s) = 0) {f : MvPowerSeries σ S} (hf0 : constantCoeff f = 0) (w : τ) :
    coeff (Finsupp.single w 1) (subst a f) =
      ∑ s, coeff (Finsupp.single s 1) f * coeff (Finsupp.single w 1) (a s) := by
  classical
  have ha : HasSubst a := ⟨fun s => by rw [ha0 s]; exact IsNilpotent.zero, fun _ => Set.toFinite _⟩
  have hR : Low 2 (f - ∑ s, coeff (Finsupp.single s 1) f • X s) := by
    apply low_two_of_lemma
    · rw [← coeff_zero_eq_constantCoeff_apply, map_sub, map_sum]
      simp only [map_smul, coeff_zero_X, smul_zero, Finset.sum_const_zero, sub_zero]
      rw [coeff_zero_eq_constantCoeff_apply]
      exact hf0
    · intro v
      simp [coeff_X, Finsupp.single_left_inj Nat.one_ne_zero]
  have hS := low_subst' (fun s => (low_one_iff _).2 (ha0 s)) hR
  have hsplit : subst a f = subst a (f - ∑ s, coeff (Finsupp.single s 1) f • X s) +
      ∑ s, coeff (Finsupp.single s 1) f • a s := by
    rw [← coe_substAlgHom ha, map_sub, map_sum]
    simp only [map_smul]
    simp only [coe_substAlgHom, subst_X ha, sub_add_cancel]
  rw [hsplit, map_add, hS (Finsupp.single w 1) (by simp), zero_add, map_sum]
  simp only [map_smul, smul_eq_mul]

/- English proof (translation)
Establish `hlin : ∀ i b : Fin d, coeff (Finsupp.single ((1 : Fin 2), b) 1) (G.F i) = if b = i then 1 else 0`. Introduce `i b`. Establish `hu` using `congrArg (coeff (Finsupp.single ((0 : Fin 1), b) 1)) (G.unit i)`. Establish `ha0 : ∀ p : Fin 2 × Fin d, constantCoeff ((![0, pt S d 0] : Fin 2 → Pt S 1 d) p.1 p.2) = 0`. Introduce and unpack `⟨a, j⟩`.

Apply the tactic sequence `fin_cases a <;> simp [ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.pt]`. Express the relevant statement in the definitionally equal form `coeff _ (subst (fun p : Fin 2 × Fin d => (![0, pt S d 0] : Fin 2 → Pt S 1 d) p.1 p.2) (G.F i)) = _ at hu`. Rewrite `hu` using `[lin_subst_lemma_3 ha0 (G.const i), Fintype.sum_prod_type, Fin.sum_univ_two]`. Simplify `hu` using `[ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.pt, coeff_X, Finsupp.single_left_inj Nat.one_ne_zero]`. Establish `hJ : ∀ i b : Fin d, constantCoeff (ReciprocityTheory.ChartRestriction.G.TB.LogPf.Jac G i b) = if i = b then 1 else 0`.

Introduce `i b`. Establish `ha0 : ∀ p : Fin 2 × Fin d, constantCoeff ((![pt S d 0, 0] : Fin 2 → Pt S 1 d) p.1 p.2) = 0`. Introduce and unpack `⟨a, j⟩`. Apply the tactic sequence `fin_cases a <;> simp [ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.pt]`. Express the relevant statement in the definitionally equal form `constantCoeff (subst (fun p : Fin 2 × Fin d => (![pt S d 0, 0] : Fin 2 → Pt S 1 d) p.1 p.2) (pderiv S ((1 : Fin 2), b) (G.F i))) = _`.

Rewrite using `[← coeff_zero_eq_constantCoeff_apply, cc_subst_lemma_2 ha0, coeff_pderiv, zero_add, hlin i b]`. Distinguish the cases in `h : i = b`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using `[h, Ne.symm h]`.

Establish `hM : (ReciprocityTheory.ChartRestriction.G.TB.LogPf.JM G).map constantCoeff = 1`. Use extensionality with `i b`. Rewrite using `[Matrix.map_apply, Matrix.one_apply]`. Conclude with `hJ i b`. Establish `hdet : IsUnit (ReciprocityTheory.ChartRestriction.G.TB.LogPf.JM G).det`.

Rewrite using `[isUnit_iff_constantCoeff, RingHom.map_det, RingHom.mapMatrix_apply, hM, Matrix.det_one]`. Conclude with `isUnit_one`. Establish `hOm : (ReciprocityTheory.ChartRestriction.G.TB.LogPf.Om G).map constantCoeff = 1`. Establish `h1` using `congrArg (fun A : Matrix (Fin d) (Fin d) (MvPowerSeries (Fin 1 × Fin d) S) => A.map constantCoeff) (Matrix.mul_nonsing_inv _ hdet)`. Simplify using `only [Matrix.map_mul, hM, Matrix.one_mul, Matrix.map_one, map_zero, map_one] at h1`.

Conclude with `h1`. Use extensionality with `i j`. Establish `hcoef : coeff (Finsupp.single ((0 : Fin 1), j) 1) (ReciprocityTheory.ChartRestriction.G.TB.LogPf.logOf G i) = constantCoeff (ReciprocityTheory.ChartRestriction.G.TB.LogPf.Om G i j)` using `by show algebraMap ℚ S (((Finsupp.degree (Finsupp.single ((0 : Fin 1), j) (1 : ℕ)) : ℕ) : ℚ)⁻¹) * _ = _`. Rewrite using `[Finset.sum_eq_single ((0 : Fin 1), j)]`. Simplify using `[coeff_zero_eq_constantCoeff_apply]`.

Introduce `w _ hw`. Simplify using `[Finsupp.single_apply, Ne.symm hw]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`. Use `show coeff (Finsupp.single ((0 : Fin 1), j) 1) (ReciprocityTheory.ChartRestriction.G.TB.LogPf.logOf G i) = (1 : Matrix (Fin d) (Fin d) S) i j`.

Rewrite using `[hcoef]`. Establish `h2 : ((ReciprocityTheory.ChartRestriction.G.TB.LogPf.Om G).map constantCoeff) i j = (1 : Matrix (Fin d) (Fin d) S) i j`. Rewrite using `[hOm]`. Rewrite `h2` using `[Matrix.map_apply]`. Conclude with `h2`.
-/
theorem dLin_logOf (G : FGLaw S d) : ReciprocityTheory.ChartRestriction.G.TB.dLin (fun i => ReciprocityTheory.ChartRestriction.G.TB.LogPf.logOf G i) = 1 := by
  have hlin : ∀ i b : Fin d, coeff (Finsupp.single ((1 : Fin 2), b) 1) (G.F i) = if b = i then 1 else 0 := by
    intro i b
    have hu := congrArg (coeff (Finsupp.single ((0 : Fin 1), b) 1)) (G.unit i)
    have ha0 : ∀ p : Fin 2 × Fin d, constantCoeff ((![0, pt S d 0] : Fin 2 → Pt S 1 d) p.1 p.2) = 0 := by
      rintro ⟨a, j⟩
      fin_cases a <;> simp [ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.pt]
    change coeff _ (subst (fun p : Fin 2 × Fin d => (![0, pt S d 0] : Fin 2 → Pt S 1 d) p.1 p.2) (G.F i)) = _
      at hu
    rw [lin_subst_lemma_3 ha0 (G.const i), Fintype.sum_prod_type, Fin.sum_univ_two] at hu
    simpa [ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.pt, coeff_X, Finsupp.single_left_inj Nat.one_ne_zero] using hu
  have hJ : ∀ i b : Fin d, constantCoeff (ReciprocityTheory.ChartRestriction.G.TB.LogPf.Jac G i b) = if i = b then 1 else 0 := by
    intro i b
    have ha0 : ∀ p : Fin 2 × Fin d, constantCoeff ((![pt S d 0, 0] : Fin 2 → Pt S 1 d) p.1 p.2) = 0 := by
      rintro ⟨a, j⟩
      fin_cases a <;> simp [ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.pt]
    change constantCoeff (subst (fun p : Fin 2 × Fin d => (![pt S d 0, 0] : Fin 2 → Pt S 1 d) p.1 p.2)
      (pderiv S ((1 : Fin 2), b) (G.F i))) = _
    rw [← coeff_zero_eq_constantCoeff_apply, cc_subst_lemma_2 ha0, coeff_pderiv, zero_add, hlin i b]
    by_cases h : i = b
    · subst h
      simp
    · simp [h, Ne.symm h]
  have hM : (ReciprocityTheory.ChartRestriction.G.TB.LogPf.JM G).map constantCoeff = 1 := by
    ext i b
    rw [Matrix.map_apply, Matrix.one_apply]
    exact hJ i b
  have hdet : IsUnit (ReciprocityTheory.ChartRestriction.G.TB.LogPf.JM G).det := by
    rw [isUnit_iff_constantCoeff, RingHom.map_det, RingHom.mapMatrix_apply, hM, Matrix.det_one]
    exact isUnit_one
  have hOm : (ReciprocityTheory.ChartRestriction.G.TB.LogPf.Om G).map constantCoeff = 1 := by
    have h1 := congrArg (fun A : Matrix (Fin d) (Fin d) (MvPowerSeries (Fin 1 × Fin d) S) => A.map constantCoeff)
      (Matrix.mul_nonsing_inv _ hdet)
    simp only [Matrix.map_mul, hM, Matrix.one_mul, Matrix.map_one, map_zero, map_one] at h1
    exact h1
  ext i j
  have hcoef : coeff (Finsupp.single ((0 : Fin 1), j) 1) (ReciprocityTheory.ChartRestriction.G.TB.LogPf.logOf G i) =
      constantCoeff (ReciprocityTheory.ChartRestriction.G.TB.LogPf.Om G i j) := by
    show algebraMap ℚ S (((Finsupp.degree (Finsupp.single ((0 : Fin 1), j) (1 : ℕ)) : ℕ) : ℚ)⁻¹) * _ = _
    rw [Finset.sum_eq_single ((0 : Fin 1), j)]
    · simp [coeff_zero_eq_constantCoeff_apply]
    · intro w _ hw
      simp [Finsupp.single_apply, Ne.symm hw]
    · intro h
      exact absurd (Finset.mem_univ _) h
  show coeff (Finsupp.single ((0 : Fin 1), j) 1) (ReciprocityTheory.ChartRestriction.G.TB.LogPf.logOf G i) = (1 : Matrix (Fin d) (Fin d) S) i j
  rw [hcoef]
  have h2 : ((ReciprocityTheory.ChartRestriction.G.TB.LogPf.Om G).map constantCoeff) i j = (1 : Matrix (Fin d) (Fin d) S) i j := by
    rw [hOm]
  rw [Matrix.map_apply] at h2
  exact h2

/- English proof (translation)
Rewrite using `[← coeff_zero_eq_constantCoeff_apply]`. Use `show algebraMap ℚ S (((0 : Fin 1 × Fin d →₀ ℕ).degree : ℚ)⁻¹) * _ = 0`. Simplify using the standard rewrite rules.
-/
theorem cc_logOf (G : FGLaw S d) (i : Fin d) : constantCoeff (ReciprocityTheory.ChartRestriction.G.TB.LogPf.logOf G i) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply]
  show algebraMap ℚ S (((0 : Fin 1 × Fin d →₀ ℕ).degree : ℚ)⁻¹) * _ = 0
  simp

/- English proof (translation)
Apply `low_two_of_lemma` to reduce the goal to its premises. Rewrite using `[map_sub, cc_logOf, constantCoeff_X, sub_zero]`. Introduce `w`. Take `⟨a, j⟩` from `w`. Establish `ha : a = 0` using `Subsingleton.elim a 0`.

Substitute `ha` using the available equality. Establish `h : ReciprocityTheory.ChartRestriction.G.TB.dLin (fun i => ReciprocityTheory.ChartRestriction.G.TB.LogPf.logOf G i) i j = (1 : Matrix (Fin d) (Fin d) S) i j`. Rewrite using `[dLin_logOf G]`. Express the relevant statement in the definitionally equal form `coeff (Finsupp.single ((0 : Fin 1), j) 1) (ReciprocityTheory.ChartRestriction.G.TB.LogPf.logOf G i) = (1 : Matrix (Fin d) (Fin d) S) i j at h`. Rewrite using `[map_sub, coeff_X, h, Matrix.one_apply]`.

Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Simplify using the standard rewrite rules. Simplify using `[hij, Ne.symm hij, Finsupp.single_left_inj Nat.one_ne_zero]`.
-/
theorem low_logOf (G : FGLaw S d) (i : Fin d) :
    Low 2 (ReciprocityTheory.ChartRestriction.G.TB.LogPf.logOf G i - X ((0 : Fin 1), i)) := by
  apply low_two_of_lemma
  · rw [map_sub, cc_logOf, constantCoeff_X, sub_zero]
  · intro w
    obtain ⟨a, j⟩ := w
    have ha : a = 0 := Subsingleton.elim a 0
    subst ha
    have h : ReciprocityTheory.ChartRestriction.G.TB.dLin (fun i => ReciprocityTheory.ChartRestriction.G.TB.LogPf.logOf G i) i j =
        (1 : Matrix (Fin d) (Fin d) S) i j := by
      rw [dLin_logOf G]
    change coeff (Finsupp.single ((0 : Fin 1), j) 1) (ReciprocityTheory.ChartRestriction.G.TB.LogPf.logOf G i) =
      (1 : Matrix (Fin d) (Fin d) S) i j at h
    rw [map_sub, coeff_X, h, Matrix.one_apply]
    by_cases hij : i = j
    · subst hij
      simp
    · simp [hij, Ne.symm hij, Finsupp.single_left_inj Nat.one_ne_zero]

/- English proof (translation)
Establish `hk : ∀ p : Fin 1 × Fin d, Low 1 (![pt S d b] p.1 p.2)`. Introduce `p`. Rewrite using `[low_one_iff]`. Simplify using `[ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.pt]`. Establish `hk0 : ∀ p : Fin 1 × Fin d, constantCoeff (![pt S d b] p.1 p.2) = 0` using `fun p => (low_one_iff _).1 (hk p)`.

Establish `ha : HasSubst (fun p : Fin 1 × Fin d => ![pt S d b] p.1 p.2)` using `⟨fun s => by rw [hk0 s]; exact IsNilpotent.zero, fun _ => Set.toFinite _⟩`. Establish `e1 : CIndFrFix.lg G b i - X (b, i) =`. Substitute `(fun p : Fin 1 × Fin d => ![pt S d b] p.1 p.2) (ReciprocityTheory.ChartRestriction.G.TB.LogPf.logOf G i - X ((0 : Fin 1), i)) := by` using the available equality. Rewrite using `[← coe_substAlgHom ha, map_sub, coe_substAlgHom, subst_X ha]`. Both sides reduce to the same expression.

Rewrite using `[e1]`. Conclude with `low_subst' hk (low_logOf G i)`.
-/
theorem low_lg (G : FGLaw S d) (b : Fin 2) (i : Fin d) :
    Low 2 (CIndFrFix.lg G b i - X (b, i)) := by
  have hk : ∀ p : Fin 1 × Fin d, Low 1 (![pt S d b] p.1 p.2) := by
    intro p
    rw [low_one_iff]
    simp [ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.pt]
  have hk0 : ∀ p : Fin 1 × Fin d, constantCoeff (![pt S d b] p.1 p.2) = 0 :=
    fun p => (low_one_iff _).1 (hk p)
  have ha : HasSubst (fun p : Fin 1 × Fin d => ![pt S d b] p.1 p.2) := ⟨fun s => by rw [hk0 s]; exact IsNilpotent.zero, fun _ => Set.toFinite _⟩
  have e1 : CIndFrFix.lg G b i - X (b, i) =
      subst (fun p : Fin 1 × Fin d => ![pt S d b] p.1 p.2)
        (ReciprocityTheory.ChartRestriction.G.TB.LogPf.logOf G i - X ((0 : Fin 1), i)) := by
    rw [← coe_substAlgHom ha, map_sub, coe_substAlgHom, subst_X ha]
    rfl
  rw [e1]
  exact low_subst' hk (low_logOf G i)

/- English proof (translation)
Establish `h` using `low_add (low_mono (by norm_num) (low_lg G b i)) ((low_one_iff (X (b, i))).2 (constantCoeff_X _))`. Rewrite `h` using `[sub_add_cancel]`. Then use the resulting hypothesis.
-/
theorem log_low_order_one (G : FGLaw S d) (b : Fin 2) (i : Fin d) : Low 1 (CIndFrFix.lg G b i) := by
  have h := low_add (low_mono (by norm_num) (low_lg G b i)) ((low_one_iff (X (b, i))).2 (constantCoeff_X _))
  rwa [sub_add_cancel] at h

/- English proof (translation)
Establish `hB0 : constantCoeff B = 0` using `(low_one_iff _).1 (low_mono (by norm_num) hB2)`. Establish `hB : PowerSeries.HasSubst B` using `PowerSeries.HasSubst.of_constantCoeff_zero hB0`. Establish `hexp : PowerSeries.exp S = 1 + PowerSeries.X + PowerSeries.X ^ 2 * PowerSeries.mk (fun n => algebraMap ℚ S (1 / ((n + 2).factorial : ℚ)))`. Use extensionality with `n`. Apply the tactic sequence `rcases n with _ | _ | n <;> simp [PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X, PowerSeries.coeff_one]`.

Rewrite using `[hexp, ← PowerSeries.coe_substAlgHom hB, map_add, map_add, map_mul, map_pow, map_one, PowerSeries.coe_substAlgHom, PowerSeries.subst_X hB]`. Establish `h4 : Low (2 + 2 + 0) (B ^ 2 * PowerSeries.subst B (PowerSeries.mk (fun n => algebraMap ℚ S (1 / ((n + 2).factorial : ℚ)))))`. Rewrite using `[pow_two]`. Conclude with `low_mul (low_mul hB2 hB2) (low_zero _)`. Establish `h3` using `low_mono (by norm_num : 3 ≤ 2 + 2 + 0) h4`.

Use `h3 using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree.
-/
private lemma exp_split_lemma_4 {σ : Type} {B : MvPowerSeries σ S} (hB2 : Low 2 B) :
    Low 3 (PowerSeries.subst B (PowerSeries.exp S) - 1 - B) := by
  have hB0 : constantCoeff B = 0 := (low_one_iff _).1 (low_mono (by norm_num) hB2)
  have hB : PowerSeries.HasSubst B := PowerSeries.HasSubst.of_constantCoeff_zero hB0
  have hexp : PowerSeries.exp S = 1 + PowerSeries.X + PowerSeries.X ^ 2 *
      PowerSeries.mk (fun n => algebraMap ℚ S (1 / ((n + 2).factorial : ℚ))) := by
    ext n
    rcases n with _ | _ | n <;> simp [PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X, PowerSeries.coeff_one]
  rw [hexp, ← PowerSeries.coe_substAlgHom hB, map_add, map_add, map_mul, map_pow, map_one,
    PowerSeries.coe_substAlgHom, PowerSeries.subst_X hB]
  have h4 : Low (2 + 2 + 0) (B ^ 2 * PowerSeries.subst B
      (PowerSeries.mk (fun n => algebraMap ℚ S (1 / ((n + 2).factorial : ℚ))))) := by
    rw [pow_two]
    exact low_mul (low_mul hB2 hB2) (low_zero _)
  have h3 := low_mono (by norm_num : 3 ≤ 2 + 2 + 0) h4
  convert h3 using 1
  ring

/- English proof (translation)
Establish `hB2 : Low 2 (CIndFrFix.bilL G c)`. Unfold `CIndFrFix.bilL`. Conclude with `low_sum _ (fun i _ => low_sum _ (fun l _ => low_smul _ (low_mul (log_low_order_one G 0 i) (log_low_order_one G 1 l))))`. Establish `hBQ : Low 3 (CIndFrFix.bilL G c - ∑ i, ∑ l, c i l • (X ((0 : Fin 2), i) * X ((1 : Fin 2), l)))`. Unfold `CIndFrFix.bilL`.

Rewrite using `[← Finset.sum_sub_distrib]`. Apply `low_sum` to reduce the goal to its premises. Introduce `i _`. Rewrite using `[← Finset.sum_sub_distrib]`. Apply `low_sum` to reduce the goal to its premises.

Introduce `l _`. Rewrite using `[← smul_sub]`. Apply `low_smul` to reduce the goal to its premises. Establish `key : Low 3 ((CIndFrFix.lg G (0 : Fin 2) i - X ((0 : Fin 2), i)) * CIndFrFix.lg G (1 : Fin 2) l + X ((0 : Fin 2), i) * (CIndFrFix.lg G (1 : Fin 2) l - X ((1 : Fin 2), l)))` using `low_add (low_mul (low_lg G 0 i) (log_low_order_one G 1 l)) (low_mul ((low_one_iff _).2 (constantCoeff_X _)) (low_lg G 1 l))`. Use `key using 1` and compare the differences between its conclusion and the goal.

Expand and normalize the polynomial expressions, which then agree. Establish `hcoe : ((1 + ∑ i, ∑ l, MvPolynomial.C (c i l) * (MvPolynomial.X ((0 : Fin 2), i) * MvPolynomial.X ((1 : Fin 2), l)) : MvPolynomial (Fin 2 × Fin d) S) : MvPowerSeries (Fin 2 × Fin d) S) = 1 + ∑ i, ∑ l, c i l • (X ((0 : Fin 2), i) * X ((1 : Fin 2), l))`. Rewrite using `[← MvPolynomial.coeToMvPowerSeries.ringHom_apply, map_add, map_one, map_sum]`. Simplify using `only [map_sum, map_mul, MvPolynomial.coeToMvPowerSeries.ringHom_apply, MvPolynomial.coe_C, MvPolynomial.coe_X, MvPowerSeries.smul_eq_C_mul]`. Establish `hdiff : Low 3 (CIndFrFix.expP (CIndFrFix.bilL G c) - ((1 + ∑ i, ∑ l, MvPolynomial.C (c i l) * (MvPolynomial.X ((0 : Fin 2), i) * MvPolynomial.X ((1 : Fin 2), l)) : MvPolynomial (Fin 2 × Fin d) S) : MvPowerSeries (Fin 2 × Fin d) S))`.

Rewrite using `[hcoe]`. Establish `h1 : Low 3 (CIndFrFix.expP (CIndFrFix.bilL G c) - 1 - CIndFrFix.bilL G c)` using `exp_split_lemma_4 hB2`. Use `low_add h1 hBQ using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree. Establish `hmem : ∀ e : Fin 2 × Fin d →₀ ℕ, e ∈ degLE 2 ↔ e.degree ≤ 2`.

Introduce `e`. Simplify using `only [degLE, Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨_, h⟩`. Conclude with `h`.

Introduce `h`. Use `⟨⟨fun i => ⟨e i, ?_⟩, ?_⟩, h⟩` and prove the remaining obligations. Establish `hle : e i ≤ e.degree` using `by show e i ≤ ∑ j ∈ e.support, e j`. Distinguish the cases in `hi : i ∈ e.support`. Conclude with `Finset.single_le_sum (f := fun j => e j) (fun _ _ => Nat.zero_le _) hi`.

Establish `h0 : e i = 0` using `by simpa using hi`. Rewrite using `[h0]`. Conclude with `Nat.zero_le _`. Use linear arithmetic over natural numbers and integers. Use extensionality with `i`.

Simplify using the standard rewrite rules. Establish `hpt : ∀ (g : MvPowerSeries (Fin 2 × Fin d) S) (e : Fin 2 × Fin d →₀ ℕ), MvPolynomial.coeff e (psTrunc 2 g) = if e.degree ≤ 2 then coeff e g else 0`. Introduce `g e`. Rewrite using `[psTrunc, MvPolynomial.coeff_sum]`. Simplify using `only [MvPolynomial.coeff_monomial, Finset.sum_ite_eq', Finset.sum_ite_eq]`.

Distinguish the cases in `h : e.degree ≤ 2`. Rewrite using `[if_pos ((hmem e).2 h), if_pos h]`. Rewrite using `[if_neg (fun h' => h ((hmem e).1 h')), if_neg h]`. Establish `hXX : ∀ (a b : Fin 2 × Fin d) (e : Fin 2 × Fin d →₀ ℕ), 2 < e.degree → coeff e (X a * X b : MvPowerSeries (Fin 2 × Fin d) S) = 0`. Introduce `a b e he`.

Rewrite using `[MvPowerSeries.X, MvPowerSeries.X, monomial_mul_monomial, coeff_monomial, if_neg]`. Introduce and unpack `rfl`. Establish `hdeg : (Finsupp.single a 1 + Finsupp.single b 1 : Fin 2 × Fin d →₀ ℕ).degree = 2` using `by show (Finsupp.single a 1 + Finsupp.single b 1 : Fin 2 × Fin d →₀ ℕ).sum (fun _ k => k) = 2`. Rewrite using `[Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), Finsupp.sum_single_index rfl, Finsupp.sum_single_index rfl]`. Use linear arithmetic over natural numbers and integers.

Use extensionality with `e`. Rewrite using `[hpt]`. Distinguish the cases in `hd : e.degree ≤ 2`. Rewrite using `[if_pos hd, ← MvPolynomial.coeff_coe]`. Establish `h` using `hdiff e (by omega)`.

Rewrite `h` using `[map_sub, sub_eq_zero]`. Then use the resulting hypothesis. Rewrite using `[if_neg hd, ← MvPolynomial.coeff_coe, hcoe, map_add, map_sum]`. Establish `h2 : 2 < e.degree` using `by omega`. Establish `hz : ∀ a b : Fin 2 × Fin d, coeff e (X a * X b : MvPowerSeries (Fin 2 × Fin d) S) = 0` using `fun a b => hXX a b e h2`. Simplify using `only [map_sum, map_smul, hz, smul_zero, Finset.sum_const_zero, add_zero]`.

Rewrite using `[coeff_one, if_neg]`. Introduce and unpack `rfl`. Simplify using `at hd`.
-/
theorem psTrunc_two_twist (G : FGLaw S d) (c : Fin d → Fin d → S) :
    psTrunc 2 (CIndFrFix.expP (CIndFrFix.bilL G c)) =
      1 + ∑ i, ∑ l, MvPolynomial.C (c i l) * (MvPolynomial.X ((0 : Fin 2), i) * MvPolynomial.X ((1 : Fin 2), l)) := by
  have hB2 : Low 2 (CIndFrFix.bilL G c) := by
    unfold CIndFrFix.bilL
    exact low_sum _ (fun i _ => low_sum _ (fun l _ => low_smul _ (low_mul (log_low_order_one G 0 i) (log_low_order_one G 1 l))))
  have hBQ : Low 3 (CIndFrFix.bilL G c - ∑ i, ∑ l, c i l • (X ((0 : Fin 2), i) * X ((1 : Fin 2), l))) := by
    unfold CIndFrFix.bilL
    rw [← Finset.sum_sub_distrib]
    apply low_sum
    intro i _
    rw [← Finset.sum_sub_distrib]
    apply low_sum
    intro l _
    rw [← smul_sub]
    apply low_smul
    have key : Low 3 ((CIndFrFix.lg G (0 : Fin 2) i - X ((0 : Fin 2), i)) * CIndFrFix.lg G (1 : Fin 2) l +
        X ((0 : Fin 2), i) * (CIndFrFix.lg G (1 : Fin 2) l - X ((1 : Fin 2), l))) :=
      low_add (low_mul (low_lg G 0 i) (log_low_order_one G 1 l))
        (low_mul ((low_one_iff _).2 (constantCoeff_X _)) (low_lg G 1 l))
    convert key using 1
    ring
  have hcoe : ((1 + ∑ i, ∑ l, MvPolynomial.C (c i l) * (MvPolynomial.X ((0 : Fin 2), i) * MvPolynomial.X ((1 : Fin 2), l)) :
        MvPolynomial (Fin 2 × Fin d) S) : MvPowerSeries (Fin 2 × Fin d) S) =
      1 + ∑ i, ∑ l, c i l • (X ((0 : Fin 2), i) * X ((1 : Fin 2), l)) := by
    rw [← MvPolynomial.coeToMvPowerSeries.ringHom_apply, map_add, map_one, map_sum]
    simp only [map_sum, map_mul, MvPolynomial.coeToMvPowerSeries.ringHom_apply, MvPolynomial.coe_C,
      MvPolynomial.coe_X, MvPowerSeries.smul_eq_C_mul]
  have hdiff : Low 3 (CIndFrFix.expP (CIndFrFix.bilL G c) - ((1 + ∑ i, ∑ l, MvPolynomial.C (c i l) * (MvPolynomial.X ((0 : Fin 2), i) * MvPolynomial.X ((1 : Fin 2), l)) :
        MvPolynomial (Fin 2 × Fin d) S) : MvPowerSeries (Fin 2 × Fin d) S)) := by
    rw [hcoe]
    have h1 : Low 3 (CIndFrFix.expP (CIndFrFix.bilL G c) - 1 - CIndFrFix.bilL G c) := exp_split_lemma_4 hB2
    convert low_add h1 hBQ using 1
    ring
  have hmem : ∀ e : Fin 2 × Fin d →₀ ℕ, e ∈ degLE 2 ↔ e.degree ≤ 2 := by
    intro e
    simp only [degLE, Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨_, h⟩
      exact h
    · intro h
      refine ⟨⟨fun i => ⟨e i, ?_⟩, ?_⟩, h⟩
      · have hle : e i ≤ e.degree := by
          show e i ≤ ∑ j ∈ e.support, e j
          by_cases hi : i ∈ e.support
          · exact Finset.single_le_sum (f := fun j => e j) (fun _ _ => Nat.zero_le _) hi
          · have h0 : e i = 0 := by simpa using hi
            rw [h0]
            exact Nat.zero_le _
        omega
      · ext i
        simp
  have hpt : ∀ (g : MvPowerSeries (Fin 2 × Fin d) S) (e : Fin 2 × Fin d →₀ ℕ),
      MvPolynomial.coeff e (psTrunc 2 g) = if e.degree ≤ 2 then coeff e g else 0 := by
    intro g e
    rw [psTrunc, MvPolynomial.coeff_sum]
    simp only [MvPolynomial.coeff_monomial, Finset.sum_ite_eq', Finset.sum_ite_eq]
    by_cases h : e.degree ≤ 2
    · rw [if_pos ((hmem e).2 h), if_pos h]
    · rw [if_neg (fun h' => h ((hmem e).1 h')), if_neg h]
  have hXX : ∀ (a b : Fin 2 × Fin d) (e : Fin 2 × Fin d →₀ ℕ), 2 < e.degree →
      coeff e (X a * X b : MvPowerSeries (Fin 2 × Fin d) S) = 0 := by
    intro a b e he
    rw [MvPowerSeries.X, MvPowerSeries.X, monomial_mul_monomial, coeff_monomial, if_neg]
    rintro rfl
    have hdeg : (Finsupp.single a 1 + Finsupp.single b 1 : Fin 2 × Fin d →₀ ℕ).degree = 2 := by
      show (Finsupp.single a 1 + Finsupp.single b 1 : Fin 2 × Fin d →₀ ℕ).sum (fun _ k => k) = 2
      rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), Finsupp.sum_single_index rfl,
        Finsupp.sum_single_index rfl]
    omega
  ext e
  rw [hpt]
  by_cases hd : e.degree ≤ 2
  · rw [if_pos hd, ← MvPolynomial.coeff_coe]
    have h := hdiff e (by omega)
    rwa [map_sub, sub_eq_zero] at h
  · rw [if_neg hd, ← MvPolynomial.coeff_coe, hcoe, map_add, map_sum]
    have h2 : 2 < e.degree := by omega
    have hz : ∀ a b : Fin 2 × Fin d, coeff e (X a * X b : MvPowerSeries (Fin 2 × Fin d) S) = 0 :=
      fun a b => hXX a b e h2
    simp only [map_sum, map_smul, hz, smul_zero, Finset.sum_const_zero, add_zero]
    rw [coeff_one, if_neg]
    rintro rfl
    simp at hd

end Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp2a
