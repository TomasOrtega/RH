import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormPrimitiveRootPrimePowSubOnePadicComplex
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegersEqSumZetaPowStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCyclotomicTowerLevelGeneratorPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TateDecompositionCompletedCyclotomicIntegersStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc

noncomputable section

namespace GlobalTheory.Cyc.TateS

variable {l : ℕ} [Fact l.Prime]

/- English proof (translation)
Use `sup_le_sup_left (IntermediateField.adjoin.mono _ _ _ ?_) _` and prove the remaining obligations. Introduce `x hx`. Take `⟨c, rfl⟩` from `Nat.exists_eq_add_of_le h`. Simplify using `only [Set.mem_setOf_eq] at hx ⊢`. Rewrite using `[pow_add, pow_mul, hx, one_pow]`.
-/
theorem Ks_mono (K : FinExt l) {m n : ℕ} (h : m ≤ n) : Ks K m ≤ Ks K n := by
  refine sup_le_sup_left (IntermediateField.adjoin.mono _ _ _ ?_) _
  intro x hx
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le h
  simp only [Set.mem_setOf_eq] at hx ⊢
  rw [pow_add, pow_mul, hx, one_pow]

/- English proof (translation)
The claim follows from `(le_sup_right : _ ≤ Ks K m) (IntermediateField.subset_adjoin _ _ hx)`.
-/
theorem root_mem (K : FinExt l) {m : ℕ} {x : Om l} (hx : x ^ (l ^ m) = 1) : x ∈ Ks K m :=
  (le_sup_right : _ ≤ Ks K m) (IntermediateField.subset_adjoin _ _ hx)

/- English proof (translation)
Introduce `x` and use `hg ⟨x.1, (le_sup_left : _ ≤ Ks K j) x.2⟩`.
-/
theorem Gj_le (K : FinExt l) (j : ℕ) {g : GQ l} (hg : g ∈ Gj K j) :
    g ∈ (K0 K).fixingSubgroup := fun x => hg ⟨x.1, (le_sup_left : _ ≤ Ks K j) x.2⟩

/- English proof (translation)
The claim follows from `hg ⟨x, hx⟩`.
-/
theorem Gj_fix (K : FinExt l) {j : ℕ} {g : GQ l} (hg : g ∈ Gj K j) {x : Om l} (hx : x ∈ Ks K j) :
    g x = x := hg ⟨x, hx⟩

/- English proof (translation)
Establish `: Ks K m ≤ (Ks K m).comap (g : Om l →ₐ[ℚ_[l]] Om l)`. Use `sup_le ?_ ?_` and prove the remaining obligations. Introduce `y hy`. Establish `h1 : g y = y` using `hg ⟨y, hy⟩`. Express the relevant statement in the definitionally equal form `g y ∈ Ks K m`.

Rewrite using `[h1]`. Conclude with `(le_sup_left : _ ≤ Ks K m) hy`. Rewrite using `[IntermediateField.adjoin_le_iff]`. Introduce `y hy`. Express the relevant statement in the definitionally equal form `g y ∈ Ks K m`.

Apply `root_mem` to reduce the goal to its premises. Establish `hy' : y ^ (l ^ m) = 1` using `hy`. Rewrite using `[← map_pow, hy', map_one]`. Conclude with `this hx`.
-/
theorem Ks_stable (K : FinExt l) (m : ℕ) {g : GQ l} (hg : g ∈ (K0 K).fixingSubgroup) {x : Om l}
    (hx : x ∈ Ks K m) : g x ∈ Ks K m := by
  have : Ks K m ≤ (Ks K m).comap (g : Om l →ₐ[ℚ_[l]] Om l) := by
    refine sup_le ?_ ?_
    · intro y hy
      have h1 : g y = y := hg ⟨y, hy⟩
      change g y ∈ Ks K m
      rw [h1]
      exact (le_sup_left : _ ≤ Ks K m) hy
    · rw [IntermediateField.adjoin_le_iff]
      intro y hy
      change g y ∈ Ks K m
      apply root_mem
      have hy' : y ^ (l ^ m) = 1 := hy
      rw [← map_pow, hy', map_one]
  exact this hx

/- English proof (translation)
Use `haveI : NeZero (n : Om l) := ⟨Nat.cast_ne_zero.mpr hn⟩`. Conclude with `HasEnoughRootsOfUnity.exists_primitiveRoot (Om l) n`.
-/
theorem exists_prim (n : ℕ) (hn : n ≠ 0) : ∃ z : Om l, IsPrimitiveRoot z n := by
  haveI : NeZero (n : Om l) := ⟨Nat.cast_ne_zero.mpr hn⟩
  exact HasEnoughRootsOfUnity.exists_primitiveRoot (Om l) n

/- English proof (translation)
The claim follows from `(algebraMap (Om l) (PadicComplex l)).injective`.
-/
theorem coe_inj : Function.Injective (algebraMap (Om l) (PadicComplex l)) :=
  (algebraMap (Om l) (PadicComplex l)).injective

/- English proof (translation)
Use `haveI : NeZero n := ⟨hn⟩`. Take `⟨z, hz⟩` from `exists_prim (l := l) n hn`. Establish `hz'` using `hz.map_of_injective (coe_inj (l := l))`. Take `⟨i, -, hi⟩` from `hz'.eq_pow_of_pow_eq_one h.pow_eq_one`. Use `⟨z ^ i, by rw [map_pow, hi], ?_⟩` and prove the remaining obligations.

Apply `IsPrimitiveRoot.of_map_of_injective _ (coe_inj (l := l))` to reduce the goal to its premises. Rewrite using `[map_pow, hi]`. Conclude with `h`.
-/
theorem prim_lift {n : ℕ} (hn : n ≠ 0) {ζ : PadicComplex l} (h : IsPrimitiveRoot ζ n) :
    ∃ z : Om l, algebraMap _ _ z = ζ ∧ IsPrimitiveRoot z n := by
  haveI : NeZero n := ⟨hn⟩
  obtain ⟨z, hz⟩ := exists_prim (l := l) n hn
  have hz' := hz.map_of_injective (coe_inj (l := l))
  obtain ⟨i, -, hi⟩ := hz'.eq_pow_of_pow_eq_one h.pow_eq_one
  refine ⟨z ^ i, by rw [map_pow, hi], ?_⟩
  apply IsPrimitiveRoot.of_map_of_injective _ (coe_inj (l := l))
  rw [map_pow, hi]
  exact h

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_inC {F : IntermediateField ℚ_[l] (Om l)} {y : PadicComplex l} :
    y ∈ inC F ↔ ∃ x ∈ F, algebraMap (Om l) (PadicComplex l) x = y := Iff.rfl

/- English proof (translation)
The claim follows from `PadicComplex.norm_extends l x`.
-/
theorem norm_coe (x : Om l) : ‖algebraMap (Om l) (PadicComplex l) x‖ = ‖x‖ :=
  PadicComplex.norm_extends l x

def algC (K : FinExt l) : Subring (PadicComplex l) where
  carrier := {y | ∃ m, y ∈ inC (Ks K m)}
  zero_mem' := ⟨0, mem_inC.2 ⟨0, zero_mem _, map_zero _⟩⟩
  one_mem' := ⟨0, mem_inC.2 ⟨1, one_mem _, map_one _⟩⟩
  add_mem' := by
    rintro _ _ ⟨m, hm⟩ ⟨n, hn⟩
    obtain ⟨a, ha, rfl⟩ := mem_inC.1 hm
    obtain ⟨b, hb, rfl⟩ := mem_inC.1 hn
    exact ⟨max m n, mem_inC.2 ⟨a + b, add_mem (Ks_mono K (le_max_left _ _) ha)
      (Ks_mono K (le_max_right _ _) hb), map_add _ _ _⟩⟩
  mul_mem' := by
    rintro _ _ ⟨m, hm⟩ ⟨n, hn⟩
    obtain ⟨a, ha, rfl⟩ := mem_inC.1 hm
    obtain ⟨b, hb, rfl⟩ := mem_inC.1 hn
    exact ⟨max m n, mem_inC.2 ⟨a * b, mul_mem (Ks_mono K (le_max_left _ _) ha)
      (Ks_mono K (le_max_right _ _) hb), map_mul _ _ _⟩⟩
  neg_mem' := by
    rintro _ ⟨m, hm⟩
    obtain ⟨a, ha, rfl⟩ := mem_inC.1 hm
    exact ⟨m, mem_inC.2 ⟨-a, neg_mem ha, map_neg _ _⟩⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨m, mem_inC.2 ⟨x, hx, rfl⟩⟩`.
-/
theorem coe_mem_algC (K : FinExt l) {m : ℕ} {x : Om l} (hx : x ∈ Ks K m) :
    algebraMap (Om l) (PadicComplex l) x ∈ algC K := ⟨m, mem_inC.2 ⟨x, hx, rfl⟩⟩

def Xalg (K : FinExt l) (j : ℕ) : AddSubgroup (PadicComplex l) := ⨆ (i : ℕ) (_ : j < i), Xlev K i

/- English proof (translation)
The claim follows from `AddSubgroup.le_topologicalClosure _`.
-/
theorem Xalg_le (K : FinExt l) (j : ℕ) : Xalg K j ≤ Xj K j := AddSubgroup.le_topologicalClosure _

/- English proof (translation)
Use `iSup₂_le fun i hi => (AddSubgroup.closure_le _).2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨ζ, y, hζ, ⟨hy, hy1⟩, rfl⟩`. Take `⟨z, rfl, hz⟩` from `prim_lift (pow_ne_zero i (Fact.out : l.Prime).ne_zero) hζ`. Take `⟨y, hy', rfl⟩` from `mem_inC.1 hy`. Rewrite `hy1` using `[norm_coe]`.

Rewrite using `[← map_mul]`. Conclude with `h i hi z y hz hy' hy1`.
-/
theorem Xalg_le_of (K : FinExt l) (j : ℕ) (B : AddSubgroup (PadicComplex l))
    (h : ∀ i, j < i → ∀ z y : Om l, IsPrimitiveRoot z (l ^ i) → y ∈ Ks K (i - 1) → ‖y‖ ≤ 1 →
      algebraMap (Om l) (PadicComplex l) (z * y) ∈ B) : Xalg K j ≤ B := by
  refine iSup₂_le fun i hi => (AddSubgroup.closure_le _).2 ?_
  rintro _ ⟨ζ, y, hζ, ⟨hy, hy1⟩, rfl⟩
  obtain ⟨z, rfl, hz⟩ := prim_lift (pow_ne_zero i (Fact.out : l.Prime).ne_zero) hζ
  obtain ⟨y, hy', rfl⟩ := mem_inC.1 hy
  rw [norm_coe] at hy1
  rw [← map_mul]
  exact h i hi z y hz hy' hy1

/- English proof (translation)
Establish `h : Xlev K i ≤ Xalg K j` using `le_iSup₂_of_le (f := fun (i : ℕ) (_ : j < i) => Xlev K i) i hi le_rfl`. Use `h (AddSubgroup.subset_closure ⟨_, _, hz.map_of_injective (coe_inj (l := l)), ⟨mem_inC.2 ⟨y, hy, rfl⟩, by rwa [norm_coe]⟩, map_mul _ _ _⟩)` and prove the remaining obligations.
-/
theorem mem_Xalg (K : FinExt l) {j i : ℕ} (hi : j < i) {z y : Om l}
    (hz : IsPrimitiveRoot z (l ^ i)) (hy : y ∈ Ks K (i - 1)) (hy1 : ‖y‖ ≤ 1) :
    algebraMap (Om l) (PadicComplex l) (z * y) ∈ Xalg K j := by
  have h : Xlev K i ≤ Xalg K j := le_iSup₂_of_le (f := fun (i : ℕ) (_ : j < i) => Xlev K i) i hi le_rfl
  refine h (AddSubgroup.subset_closure ⟨_, _, hz.map_of_injective (coe_inj (l := l)),
    ⟨mem_inC.2 ⟨y, hy, rfl⟩, by rwa [norm_coe]⟩, map_mul _ _ _⟩)

/- English proof (translation)
The claim follows from `Xalg_le_of K j (algC K).toAddSubgroup (fun i _ _ _ hz hy _ => coe_mem_algC K (mul_mem (root_mem K hz.pow_eq_one) (Ks_mono K (Nat.sub_le i 1) hy))) hx`.
-/
theorem Xalg_alg (K : FinExt l) (j : ℕ) {x : PadicComplex l} (hx : x ∈ Xalg K j) : x ∈ algC K :=
  Xalg_le_of K j (algC K).toAddSubgroup (fun i _ _ _ hz hy _ =>
    coe_mem_algC K (mul_mem (root_mem K hz.pow_eq_one) (Ks_mono K (Nat.sub_le i 1) hy))) hx

/- English proof (translation)
Proceed by induction on `c with`. Consider the case `zero => exact fun x hx _ => ⟨x, hx, 0, zero_mem _, (add_zero _).symm⟩`. Consider the case `succ c ih`. Introduce `x hx hx1`. Establish `hp : l.Prime` using `Fact.out`.

Use `haveI : NeZero l := ⟨hp.ne_zero⟩`. Take `⟨z, hz⟩` from `exists_prim (l := l) (l ^ (j + (c + 1))) (pow_ne_zero _ hp.ne_zero)`. Take `⟨y, hy, rfl⟩` from `(GlobalTheory.T.integers_eq_sum_zeta_pow_unique l K (j + (c + 1)) (by omega) z hz).1 x hx hx1`. Take `⟨o, ho, d, hd, hod⟩` from `ih (y 0) (hy 0).1 (hy 0).2`. Use `⟨o, ho, d + ∑ a ∈ Finset.univ.erase (0 : Fin l), algebraMap (Om l) (PadicComplex l) (z ^ (a : ℕ) * y a), add_mem hd (sum_mem fun a ha => ?_), ?_⟩` and prove the remaining obligations.

Use `mem_Xalg K (i := j + (c + 1)) (by omega) (hz.pow_of_coprime _ ?_) (hy a).1 (hy a).2` and prove the remaining obligations. Apply `Nat.Coprime.pow_right` to reduce the goal to its premises. Establish `ha0 : (a : ℕ) ≠ 0` using `fun h => (Finset.ne_of_mem_erase ha) (Fin.ext h)`. Conclude with `(Nat.coprime_of_lt_prime ha0 a.2 hp).symm`. Rewrite using `[← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : Fin l)), map_add, map_sum, ← add_assoc, ← hod]`.

Simplify using the standard rewrite rules.
-/
theorem int_decomp (K : FinExt l) {j : ℕ} (hj : 1 ≤ j) (c : ℕ) : ∀ x : Om l, x ∈ Ks K (j + c) →
    ‖x‖ ≤ 1 → ∃ o ∈ Ks K j, ∃ d ∈ Xalg K j,
      algebraMap (Om l) (PadicComplex l) x = algebraMap (Om l) (PadicComplex l) o + d := by
  induction c with
  | zero => exact fun x hx _ => ⟨x, hx, 0, zero_mem _, (add_zero _).symm⟩
  | succ c ih =>
    intro x hx hx1
    have hp : l.Prime := Fact.out
    haveI : NeZero l := ⟨hp.ne_zero⟩
    obtain ⟨z, hz⟩ := exists_prim (l := l) (l ^ (j + (c + 1))) (pow_ne_zero _ hp.ne_zero)
    obtain ⟨y, hy, rfl⟩ := (GlobalTheory.T.integers_eq_sum_zeta_pow_unique l K (j + (c + 1)) (by omega) z hz).1 x hx hx1
    obtain ⟨o, ho, d, hd, hod⟩ := ih (y 0) (hy 0).1 (hy 0).2
    refine ⟨o, ho, d + ∑ a ∈ Finset.univ.erase (0 : Fin l),
      algebraMap (Om l) (PadicComplex l) (z ^ (a : ℕ) * y a), add_mem hd (sum_mem fun a ha => ?_), ?_⟩
    · refine mem_Xalg K (i := j + (c + 1)) (by omega) (hz.pow_of_coprime _ ?_) (hy a).1 (hy a).2
      apply Nat.Coprime.pow_right
      have ha0 : (a : ℕ) ≠ 0 := fun h => (Finset.ne_of_mem_erase ha) (Fin.ext h)
      exact (Nat.coprime_of_lt_prime ha0 a.2 hp).symm
    · rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : Fin l)), map_add, map_sum, ← add_assoc,
        ← hod]
      simp

variable {act : GQ l →* (PadicComplex l ≃+* PadicComplex l)} {χ : GQ l →* ℚ_[l]ˣ}

/- English proof (translation)
The claim follows from `hact.1 g x`.
-/
theorem act_coe (hact : IsActC act) (g : GQ l) (x : Om l) :
    act g (algebraMap (Om l) (PadicComplex l) x) = algebraMap (Om l) (PadicComplex l) (g x) :=
  hact.1 g x

/- English proof (translation)
Take `⟨m, hm⟩` from `hx`. Take `⟨a, ha, rfl⟩` from `mem_inC.1 hm`. Rewrite using `[act_coe hact]`. Conclude with `coe_mem_algC K (Ks_stable K m hg ha)`.
-/
theorem act_algC (hact : IsActC act) (K : FinExt l) {g : GQ l} (hg : g ∈ (K0 K).fixingSubgroup)
    {x : PadicComplex l} (hx : x ∈ algC K) : act g x ∈ algC K := by
  obtain ⟨m, hm⟩ := hx
  obtain ⟨a, ha, rfl⟩ := mem_inC.1 hm
  rw [act_coe hact]
  exact coe_mem_algC K (Ks_stable K m hg ha)

/- English proof (translation)
Take `⟨m, hm⟩` from `hx'`. Take `⟨a, ha, rfl⟩` from `mem_inC.1 hm`. Rewrite `hfix` using `[act_coe hact]`. Establish `hga : g a = a` using `coe_inj hfix`. Establish `hpow : ∀ k : ℕ, (g ^ k) a = a`.

Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => rfl`. Consider the case `succ k ih => rw [pow_succ, AlgEquiv.mul_apply, hga, ih]`. Establish `haj : a ∈ Ks K j`.

Rewrite using `[← InfiniteGalois.fixedField_fixingSubgroup (Ks K j), IntermediateField.mem_fixedField_iff]`. Introduce `σ hσ`. Take `⟨k, hk⟩` from `((GlobalTheory.T.exists_cyclotomicTowerLevelGenerator_properties l act χ hact hχ K j hj).2 g hg).2.1 σ hσ m`. Establish `h1` using `Gj_fix K hk ha`. Establish `h2 : σ = σ * (g ^ k)⁻¹ * g ^ k` using `by group`.

Rewrite using `[h2, AlgEquiv.mul_apply, hpow, h1]`. Conclude with `(GlobalTheory.T.tate_decomposition_completed_cyclotomic_integers l act χ hact hχ K j hj.1).2.1 _ (mem_inC.2 ⟨a, haj, rfl⟩) _ hx 0 (by simp)`.
-/
theorem fixed_alg_eq_zero (hact : IsActC act) (hχ : IsCyc χ) (K : FinExt l) {j : ℕ} (hj : Lev l j)
    {g : GQ l} (hg : IsGen χ K j g) {x : PadicComplex l} (hx : x ∈ Xj K j) (hx' : x ∈ algC K)
    (hfix : act g x = x) : x = 0 := by
  obtain ⟨m, hm⟩ := hx'
  obtain ⟨a, ha, rfl⟩ := mem_inC.1 hm
  rw [act_coe hact] at hfix
  have hga : g a = a := coe_inj hfix
  have hpow : ∀ k : ℕ, (g ^ k) a = a := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [pow_succ, AlgEquiv.mul_apply, hga, ih]
  have haj : a ∈ Ks K j := by
    rw [← InfiniteGalois.fixedField_fixingSubgroup (Ks K j), IntermediateField.mem_fixedField_iff]
    intro σ hσ
    obtain ⟨k, hk⟩ := ((GlobalTheory.T.exists_cyclotomicTowerLevelGenerator_properties l act χ hact hχ K j hj).2 g hg).2.1 σ hσ m
    have h1 := Gj_fix K hk ha
    have h2 : σ = σ * (g ^ k)⁻¹ * g ^ k := by group
    rw [h2, AlgEquiv.mul_apply, hpow, h1]
  exact (GlobalTheory.T.tate_decomposition_completed_cyclotomic_integers l act χ hact hχ K j hj.1).2.1 _ (mem_inC.2 ⟨a, haj, rfl⟩) _ hx 0 (by simp)

/- English proof (translation)
Establish `h1` using `GlobalTheory.Cyc.norm_primitiveRoot_sub_one l 1 le_rfl (algebraMap (Om l) (PadicComplex l) η) (by rw [pow_one]; exact h.map_of_injective (coe_inj (l := l)))`. Rewrite using `[← h1, ← norm_coe, map_sub, map_one]`.
-/
theorem norm_prim_sub_one {η : Om l} (h : IsPrimitiveRoot η l) :
    ‖η - 1‖ = (l : ℝ) ^ (-(1 : ℝ) / ((l : ℝ) ^ (1 - 1) * ((l : ℝ) - 1))) := by
  have h1 := GlobalTheory.Cyc.norm_primitiveRoot_sub_one l 1 le_rfl (algebraMap (Om l) (PadicComplex l) η)
    (by rw [pow_one]; exact h.map_of_injective (coe_inj (l := l)))
  rw [← h1, ← norm_coe, map_sub, map_one]

/- English proof (translation)
Establish `hp : l.Prime` using `Fact.out`. Establish `hz0 : z ≠ 0` using `hz.ne_zero (pow_ne_zero _ hp.ne_zero)`. Establish `h1 : g (z ^ l) = z ^ l` using `Gj_fix K hg.1 (root_mem K (by rw [← pow_mul, ← pow_succ', hz.pow_eq_one]))`. Establish `h2 : (g z / z) ^ l = 1`. Rewrite using `[div_pow, ← map_pow, h1, div_self (pow_ne_zero _ hz0)]`.

Establish `h3 : g z / z ≠ 1`. Introduce `h`. Establish `hgz : g z = z` using `by rwa [div_eq_one_iff_eq hz0] at h`. Take `⟨a, ha, hga⟩` from `hχ g (i + 1) z hz.pow_eq_one`. Establish `h4 : z ^ ((a : ℤ) - 1) = 1`.

Rewrite using `[zpow_sub₀ hz0, zpow_natCast, ← hga, hgz, zpow_one, div_self hz0]`. Rewrite `h4` using `[hz.zpow_eq_one_iff_dvd]`. Establish `h5` using `(Padic.norm_int_le_pow_iff_dvd (p := l) ((a : ℤ) - 1) (i + 1)).2 (by exact_mod_cast h4)`. Establish `h6 : ‖(χ g : ℚ_[l]) - 1‖ ≤ (l : ℝ) ^ (-((i + 1 : ℕ) : ℤ))`. Establish `: (χ g : ℚ_[l]) - 1 = ((χ g : ℚ_[l]) - a) + (((a : ℤ) - 1 : ℤ) : ℚ_[l])` using `by push_cast; ring`.

Rewrite using `[this]`. Conclude with `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha h5)`. Rewrite `h6` using `[hg.2]`. Establish `hl : (1 : ℝ) < l` using `by exact_mod_cast hp.one_lt`. Rewrite `h6` using `[zpow_le_zpow_iff_right₀ hl]`.

Move the coercions through the operations in `at h6`. Use linear arithmetic over natural numbers and integers. Use `⟨g z / z, ?_, (div_mul_cancel₀ _ hz0).symm⟩` and prove the remaining obligations. Use `orderOf_eq_prime h2 h3` as an intermediate fact. Establish `h7` using `IsPrimitiveRoot.orderOf (g z / z)`.

Rewrite `h7` using `[this]`. Then use the resulting hypothesis.
-/
theorem gen_root (hχ : IsCyc χ) (K : FinExt l) {i : ℕ} {g : GQ l} (hg : IsGen χ K i g) {z : Om l}
    (hz : IsPrimitiveRoot z (l ^ (i + 1))) : ∃ η : Om l, IsPrimitiveRoot η l ∧ g z = η * z := by
  have hp : l.Prime := Fact.out
  have hz0 : z ≠ 0 := hz.ne_zero (pow_ne_zero _ hp.ne_zero)
  have h1 : g (z ^ l) = z ^ l :=
    Gj_fix K hg.1 (root_mem K (by rw [← pow_mul, ← pow_succ', hz.pow_eq_one]))
  have h2 : (g z / z) ^ l = 1 := by
    rw [div_pow, ← map_pow, h1, div_self (pow_ne_zero _ hz0)]
  have h3 : g z / z ≠ 1 := by
    intro h
    have hgz : g z = z := by rwa [div_eq_one_iff_eq hz0] at h
    obtain ⟨a, ha, hga⟩ := hχ g (i + 1) z hz.pow_eq_one
    have h4 : z ^ ((a : ℤ) - 1) = 1 := by
      rw [zpow_sub₀ hz0, zpow_natCast, ← hga, hgz, zpow_one, div_self hz0]
    rw [hz.zpow_eq_one_iff_dvd] at h4
    have h5 := (Padic.norm_int_le_pow_iff_dvd (p := l) ((a : ℤ) - 1) (i + 1)).2 (by exact_mod_cast h4)
    have h6 : ‖(χ g : ℚ_[l]) - 1‖ ≤ (l : ℝ) ^ (-((i + 1 : ℕ) : ℤ)) := by
      have : (χ g : ℚ_[l]) - 1 = ((χ g : ℚ_[l]) - a) + (((a : ℤ) - 1 : ℤ) : ℚ_[l]) := by
        push_cast; ring
      rw [this]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha h5)
    rw [hg.2] at h6
    have hl : (1 : ℝ) < l := by exact_mod_cast hp.one_lt
    rw [zpow_le_zpow_iff_right₀ hl] at h6
    push_cast at h6
    omega
  refine ⟨g z / z, ?_, (div_mul_cancel₀ _ hz0).symm⟩
  have := orderOf_eq_prime h2 h3
  have h7 := IsPrimitiveRoot.orderOf (g z / z)
  rwa [this] at h7

/- English proof (translation)
Establish `hp : l.Prime` using `Fact.out`. Set `B : AddSubgroup (PadicComplex l)` to `{ carrier := {x | ∃ y ∈ Xj K j, y ∈ algC K ∧ act g y - y = (ζ - 1) * x} zero_mem' := ⟨0, zero_mem _, zero_mem _, by simp⟩ add_mem' := by`. Introduce and unpack `a b ⟨y, hy, hy', h⟩ ⟨y', hz, hz', h'⟩`. Conclude with `⟨y + y', add_mem hy hz, add_mem hy' hz', by rw [map_add]; linear_combination h + h'⟩`. Use the proof step `neg_mem' := by`.

Introduce and unpack `a ⟨y, hy, hy', h⟩`. Conclude with `⟨-y, neg_mem hy, neg_mem hy', by rw [map_neg]; linear_combination -h⟩ }`. Use `Xalg_le_of K j B (fun i hi z y hz hy hy1 => ?_) hx` and prove the remaining obligations. Take `⟨b, rfl⟩ : ∃ b, i = j + b + 1` from `⟨i - j - 1, by omega⟩`. Rewrite `hy` using `[Nat.add_sub_cancel]`.

Establish `hg'` using `((GlobalTheory.T.exists_cyclotomicTowerLevelGenerator_properties l act χ hact hχ K j hj).2 g hg).1 b`. Take `⟨η, hη, hgz⟩` from `gen_root hχ K hg' hz`. Take `⟨ζ₀, rfl, hζ₀⟩` from `prim_lift hp.ne_zero hζ`. Establish `hη1 : η - 1 ≠ 0` using `sub_ne_zero.2 (hη.ne_one hp.one_lt)`. Establish `hj1 : 1 ≤ j + b` using `by have := hj.1; omega`.

Establish `hmem : ∀ {e : Om l}, IsPrimitiveRoot e l → e - 1 ∈ Ks K (j + b)` using `fun h => sub_mem (Ks_mono K hj1 (root_mem K (by rw [pow_one, h.pow_eq_one]))) (one_mem _)`. Use `set w : Om l := (ζ₀ - 1) / (η - 1) * y with hw`. Establish `hwK : w ∈ Ks K (j + b)` using `mul_mem (div_mem (hmem hζ₀) (hmem hη)) hy`. Establish `hw1 : ‖w‖ ≤ 1`. Rewrite using `[hw, norm_mul, norm_div, norm_prim_sub_one hζ₀, ← norm_prim_sub_one hη, div_self (norm_ne_zero_iff.2 hη1), one_mul]`.

Conclude with `hy1`. Establish `hu : algebraMap (Om l) (PadicComplex l) (z * w) ∈ Xalg K j` using `mem_Xalg K hi hz (by rwa [Nat.add_sub_cancel]) hw1`. Use `set u := algebraMap (Om l) (PadicComplex l) (z * w) with hu'`. Establish `hgk : ∀ k : ℕ, g ^ k ∈ (K0 K).fixingSubgroup` using `fun k => pow_mem (Gj_le K j hg.1) k`. Use `⟨∑ k ∈ Finset.range (l ^ b), act (g ^ k) u, sum_mem fun k _ => (GlobalTheory.T.tate_decomposition_completed_cyclotomic_integers l act χ hact hχ K j hj.1).2.2.2.2.1 _ (hgk k) _ (Xalg_le K j hu), sum_mem fun k _ => act_algC hact K (hgk k) (Xalg_alg K j hu), ?_⟩` and prove the remaining obligations.

Establish `hs : act g (∑ k ∈ Finset.range (l ^ b), act (g ^ k) u) - ∑ k ∈ Finset.range (l ^ b), act (g ^ k) u = act (g ^ l ^ b) u - act (g ^ 0) u`. Rewrite using `[← Finset.sum_range_sub (fun k => act (g ^ k) u), map_sum, ← Finset.sum_sub_distrib]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[pow_succ', map_mul]`. Both sides reduce to the same expression.

Rewrite using `[hs, pow_zero, map_one, hu', act_coe hact, map_mul (g ^ l ^ b), hgz, Gj_fix K hg'.1 hwK]`. Express the relevant statement in the definitionally equal form `_ - algebraMap (Om l) (PadicComplex l) (z * w) = _`. Rewrite using `[← map_one (algebraMap (Om l) (PadicComplex l)), ← map_sub, ← map_sub, ← map_mul]`. Use `congr 1`. Rewrite using `[hw]`.

Clear the denominators using the available nonvanishing facts.
-/
theorem solve_alg (hact : IsActC act) (hχ : IsCyc χ) (K : FinExt l) {j : ℕ} (hj : Lev l j)
    {g : GQ l} (hg : IsGen χ K j g) {ζ : PadicComplex l} (hζ : IsPrimitiveRoot ζ l)
    {x : PadicComplex l} (hx : x ∈ Xalg K j) :
    ∃ y ∈ Xj K j, y ∈ algC K ∧ act g y - y = (ζ - 1) * x := by
  have hp : l.Prime := Fact.out
  let B : AddSubgroup (PadicComplex l) :=
    { carrier := {x | ∃ y ∈ Xj K j, y ∈ algC K ∧ act g y - y = (ζ - 1) * x}
      zero_mem' := ⟨0, zero_mem _, zero_mem _, by simp⟩
      add_mem' := by
        rintro a b ⟨y, hy, hy', h⟩ ⟨y', hz, hz', h'⟩
        exact ⟨y + y', add_mem hy hz, add_mem hy' hz', by rw [map_add]; linear_combination h + h'⟩
      neg_mem' := by
        rintro a ⟨y, hy, hy', h⟩
        exact ⟨-y, neg_mem hy, neg_mem hy', by rw [map_neg]; linear_combination -h⟩ }
  refine Xalg_le_of K j B (fun i hi z y hz hy hy1 => ?_) hx
  obtain ⟨b, rfl⟩ : ∃ b, i = j + b + 1 := ⟨i - j - 1, by omega⟩
  rw [Nat.add_sub_cancel] at hy
  have hg' := ((GlobalTheory.T.exists_cyclotomicTowerLevelGenerator_properties l act χ hact hχ K j hj).2 g hg).1 b
  obtain ⟨η, hη, hgz⟩ := gen_root hχ K hg' hz
  obtain ⟨ζ₀, rfl, hζ₀⟩ := prim_lift hp.ne_zero hζ
  have hη1 : η - 1 ≠ 0 := sub_ne_zero.2 (hη.ne_one hp.one_lt)
  have hj1 : 1 ≤ j + b := by have := hj.1; omega
  have hmem : ∀ {e : Om l}, IsPrimitiveRoot e l → e - 1 ∈ Ks K (j + b) := fun h =>
    sub_mem (Ks_mono K hj1 (root_mem K (by rw [pow_one, h.pow_eq_one]))) (one_mem _)
  set w : Om l := (ζ₀ - 1) / (η - 1) * y with hw
  have hwK : w ∈ Ks K (j + b) := mul_mem (div_mem (hmem hζ₀) (hmem hη)) hy
  have hw1 : ‖w‖ ≤ 1 := by
    rw [hw, norm_mul, norm_div, norm_prim_sub_one hζ₀, ← norm_prim_sub_one hη,
      div_self (norm_ne_zero_iff.2 hη1), one_mul]
    exact hy1
  have hu : algebraMap (Om l) (PadicComplex l) (z * w) ∈ Xalg K j :=
    mem_Xalg K hi hz (by rwa [Nat.add_sub_cancel]) hw1
  set u := algebraMap (Om l) (PadicComplex l) (z * w) with hu'
  have hgk : ∀ k : ℕ, g ^ k ∈ (K0 K).fixingSubgroup := fun k => pow_mem (Gj_le K j hg.1) k
  refine ⟨∑ k ∈ Finset.range (l ^ b), act (g ^ k) u, sum_mem fun k _ =>
    (GlobalTheory.T.tate_decomposition_completed_cyclotomic_integers l act χ hact hχ K j hj.1).2.2.2.2.1 _ (hgk k) _ (Xalg_le K j hu),
    sum_mem fun k _ => act_algC hact K (hgk k) (Xalg_alg K j hu), ?_⟩
  have hs : act g (∑ k ∈ Finset.range (l ^ b), act (g ^ k) u) -
      ∑ k ∈ Finset.range (l ^ b), act (g ^ k) u = act (g ^ l ^ b) u - act (g ^ 0) u := by
    rw [← Finset.sum_range_sub (fun k => act (g ^ k) u), map_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [pow_succ', map_mul]
    rfl
  rw [hs, pow_zero, map_one, hu', act_coe hact, map_mul (g ^ l ^ b), hgz, Gj_fix K hg'.1 hwK]
  change _ - algebraMap (Om l) (PadicComplex l) (z * w) = _
  rw [← map_one (algebraMap (Om l) (PadicComplex l)), ← map_sub, ← map_sub, ← map_mul]
  congr 1
  rw [hw]
  field_simp

/- English proof (translation)
Rewrite using `[← map_natCast (algebraMap (Om l) (PadicComplex l)), norm_coe, ← map_natCast (algebraMap ℚ_[l] (Om l)), PadicAlgCl.norm_extends, Padic.norm_p]`.
-/
theorem norm_l : ‖(l : PadicComplex l)‖ = (l : ℝ)⁻¹ := by
  rw [← map_natCast (algebraMap (Om l) (PadicComplex l)), norm_coe,
    ← map_natCast (algebraMap ℚ_[l] (Om l)), PadicAlgCl.norm_extends, Padic.norm_p]

/- English proof (translation)
The claim follows from `closure_minimal (t := {y : PadicComplex l | ‖y‖ ≤ 1}) (fun _ hy => hy.2) (isClosed_le continuous_norm continuous_const) ((GlobalTheory.T.tate_decomposition_completed_cyclotomic_integers l act χ hact hχ K j hj).2.2.1 x hx)`.
-/
theorem norm_le_one (hact : IsActC act) (hχ : IsCyc χ) (K : FinExt l) {j : ℕ} (hj : 1 ≤ j)
    {x : PadicComplex l} (hx : x ∈ Xj K j) : ‖x‖ ≤ 1 :=
  closure_minimal (t := {y : PadicComplex l | ‖y‖ ≤ 1}) (fun _ hy => hy.2)
    (isClosed_le continuous_norm continuous_const)
    ((GlobalTheory.T.tate_decomposition_completed_cyclotomic_integers l act χ hact hχ K j hj).2.2.1 x hx)

/- English proof (translation)
Take `⟨a, ha, rfl⟩` from `mem_inC.1 hy`. Rewrite using `[act_coe hact, Gj_fix K hg ha]`.
-/
theorem act_fix (hact : IsActC act) (K : FinExt l) {j : ℕ} {g : GQ l} (hg : g ∈ Gj K j)
    {y : PadicComplex l} (hy : y ∈ inC (Ks K j)) : act g y = y := by
  obtain ⟨a, ha, rfl⟩ := mem_inC.1 hy
  rw [act_coe hact, Gj_fix K hg ha]

/- English proof (translation)
Establish `hp : l.Prime` using `Fact.out`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Take `⟨ζ₀, rfl, hζ₀⟩` from `prim_lift hp.ne_zero hζ`. Conclude with `mem_inC.2 ⟨ζ₀ - 1, sub_mem (Ks_mono K hj (root_mem K (by rw [pow_one, hζ₀.pow_eq_one]))) (one_mem _), by rw [map_sub, map_one]⟩`. Establish `h1 : ‖ζ‖ = 1`.

Use `congrArg norm hζ.pow_eq_one` as an intermediate fact. Rewrite `this` using `[norm_pow, norm_one]`. Conclude with `(pow_eq_one_iff_of_nonneg (norm_nonneg _) hp.ne_zero).1 this`. Rewrite using `[sub_eq_add_neg]`. Use `(IsUltrametricDist.norm_add_le_max _ _).trans ?_` and prove the remaining obligations.

Simplify using `[h1]`.
-/
theorem zeta_sub_one_mem (K : FinExt l) {j : ℕ} (hj : 1 ≤ j) {ζ : PadicComplex l}
    (hζ : IsPrimitiveRoot ζ l) : ζ - 1 ∈ intC (Ks K j) := by
  have hp : l.Prime := Fact.out
  refine ⟨?_, ?_⟩
  · obtain ⟨ζ₀, rfl, hζ₀⟩ := prim_lift hp.ne_zero hζ
    exact mem_inC.2 ⟨ζ₀ - 1, sub_mem (Ks_mono K hj (root_mem K (by rw [pow_one, hζ₀.pow_eq_one])))
      (one_mem _), by rw [map_sub, map_one]⟩
  · have h1 : ‖ζ‖ = 1 := by
      have := congrArg norm hζ.pow_eq_one
      rw [norm_pow, norm_one] at this
      exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hp.ne_zero).1 this
    rw [sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans ?_
    simp [h1]

/- English proof (translation)
Establish `hp : l.Prime` using `Fact.out`. Establish `T1` using `GlobalTheory.T.tate_decomposition_completed_cyclotomic_integers l act χ hact hχ K j hj.1`. Establish `hg0` using `Gj_le K j hg.1`. Establish `hdX` using `Xalg_le K j hd`. Establish `hdA` using `Xalg_alg K j hd`.

Establish `hwX : act g d - d ∈ Xj K j` using `sub_mem (T1.2.2.2.2.1 g hg0 d hdX) hdX`. Take `⟨m, hm⟩ : act g d - d ∈ algC K` from `sub_mem (act_algC hact K hg0 hdA) hdA`. Take `⟨a, ha, hwa⟩` from `mem_inC.1 hm`. Establish `hlO : ((l : Om l)) ^ n ≠ 0` using `pow_ne_zero _ (Nat.cast_ne_zero.2 hp.ne_zero)`. Establish `hlC : ((l : PadicComplex l)) ^ n ≠ 0` using `pow_ne_zero _ (Nat.cast_ne_zero.2 hp.ne_zero)`.

Establish `hnl : ‖(l : PadicComplex l) ^ n‖ = (l : ℝ)⁻¹ ^ n` using `by rw [norm_pow, norm_l]`. Establish `hcoe : algebraMap (Om l) (PadicComplex l) (a / (l : Om l) ^ n) = (act g d - d) / (l : PadicComplex l) ^ n`. Rewrite using `[map_div₀, map_pow, map_natCast, hwa]`. Take `⟨o, ho, d', hd', hod⟩` from `int_decomp K hj.1 m (a / (l : Om l) ^ n) (div_mem (Ks_mono K (Nat.le_add_left _ _) ha) (pow_mem (natCast_mem _ _) _)) (by`. Rewrite using `[← norm_coe, hcoe, norm_div, div_le_one (norm_pos_iff.2 hlC), hnl]`.

Conclude with `hn)`. Rewrite `hod` using `[hcoe, div_eq_iff hlC]`. Establish `hmul : ∀ {x : PadicComplex l}, x ∈ Xj K j → (l : PadicComplex l) ^ n * x ∈ Xj K j`. Introduce `x hx`. Use `nsmul_mem hx (l ^ n)` as an intermediate fact.

Rewrite `this` using `[nsmul_eq_mul, Nat.cast_pow]`. Then use the resulting hypothesis. Establish `ho0 : algebraMap (Om l) (PadicComplex l) o = 0` using `T1.2.1 _ (mem_inC.2 ⟨o, ho, rfl⟩) _ (sub_mem hwX (hmul (Xalg_le K j hd'))) n (by rw [hod]; ring)`. Rewrite `hod` using `[ho0, zero_add]`. Take `⟨y, hyX, hyA, hy⟩` from `solve_alg hact hχ K hj hg hζ hd'`. Establish `hz` using `zeta_sub_one_mem K hj.1 hζ`.

Establish `h0` using `fixed_alg_eq_zero hact hχ K hj hg (x := (ζ - 1) * d - (l : PadicComplex l) ^ n * y) (sub_mem (T1.2.2.2.1 _ hz d hdX) (hmul hyX)) (sub_mem (mul_mem ⟨j, hz.1⟩ hdA) (mul_mem (pow_mem (natCast_mem _ _) _) hyA)) (by`. Rewrite using `[map_sub, map_mul, map_mul, act_fix hact K hg.1 hz.1, map_pow, map_natCast]`. Take the linear combination `(ζ - 1) * hod - (l : PadicComplex l) ^ n * hy)`. Rewrite using `[sub_eq_zero.1 h0, norm_mul, hnl]`. Conclude with `mul_le_of_le_one_right (by positivity) (norm_le_one hact hχ K hj.1 hyX)`.
-/
theorem est_pow (hact : IsActC act) (hχ : IsCyc χ) (K : FinExt l) {j : ℕ} (hj : Lev l j)
    {g : GQ l} (hg : IsGen χ K j g) {ζ : PadicComplex l} (hζ : IsPrimitiveRoot ζ l)
    {d : PadicComplex l} (hd : d ∈ Xalg K j) (n : ℕ) (hn : ‖act g d - d‖ ≤ (l : ℝ)⁻¹ ^ n) :
    ‖(ζ - 1) * d‖ ≤ (l : ℝ)⁻¹ ^ n := by
  have hp : l.Prime := Fact.out
  have T1 := GlobalTheory.T.tate_decomposition_completed_cyclotomic_integers l act χ hact hχ K j hj.1
  have hg0 := Gj_le K j hg.1
  have hdX := Xalg_le K j hd
  have hdA := Xalg_alg K j hd
  have hwX : act g d - d ∈ Xj K j := sub_mem (T1.2.2.2.2.1 g hg0 d hdX) hdX
  obtain ⟨m, hm⟩ : act g d - d ∈ algC K := sub_mem (act_algC hact K hg0 hdA) hdA
  obtain ⟨a, ha, hwa⟩ := mem_inC.1 hm
  have hlO : ((l : Om l)) ^ n ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 hp.ne_zero)
  have hlC : ((l : PadicComplex l)) ^ n ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 hp.ne_zero)
  have hnl : ‖(l : PadicComplex l) ^ n‖ = (l : ℝ)⁻¹ ^ n := by rw [norm_pow, norm_l]
  have hcoe : algebraMap (Om l) (PadicComplex l) (a / (l : Om l) ^ n) =
      (act g d - d) / (l : PadicComplex l) ^ n := by
    rw [map_div₀, map_pow, map_natCast, hwa]
  obtain ⟨o, ho, d', hd', hod⟩ := int_decomp K hj.1 m (a / (l : Om l) ^ n)
    (div_mem (Ks_mono K (Nat.le_add_left _ _) ha) (pow_mem (natCast_mem _ _) _))
    (by
      rw [← norm_coe, hcoe, norm_div, div_le_one (norm_pos_iff.2 hlC), hnl]
      exact hn)
  rw [hcoe, div_eq_iff hlC] at hod
  have hmul : ∀ {x : PadicComplex l}, x ∈ Xj K j → (l : PadicComplex l) ^ n * x ∈ Xj K j := by
    intro x hx
    have := nsmul_mem hx (l ^ n)
    rwa [nsmul_eq_mul, Nat.cast_pow] at this
  have ho0 : algebraMap (Om l) (PadicComplex l) o = 0 :=
    T1.2.1 _ (mem_inC.2 ⟨o, ho, rfl⟩) _ (sub_mem hwX (hmul (Xalg_le K j hd'))) n
      (by rw [hod]; ring)
  rw [ho0, zero_add] at hod
  obtain ⟨y, hyX, hyA, hy⟩ := solve_alg hact hχ K hj hg hζ hd'
  have hz := zeta_sub_one_mem K hj.1 hζ
  have h0 := fixed_alg_eq_zero hact hχ K hj hg
    (x := (ζ - 1) * d - (l : PadicComplex l) ^ n * y)
    (sub_mem (T1.2.2.2.1 _ hz d hdX) (hmul hyX))
    (sub_mem (mul_mem ⟨j, hz.1⟩ hdA) (mul_mem (pow_mem (natCast_mem _ _) _) hyA))
    (by
      rw [map_sub, map_mul, map_mul, act_fix hact K hg.1 hz.1, map_pow, map_natCast]
      linear_combination (ζ - 1) * hod - (l : PadicComplex l) ^ n * hy)
  rw [sub_eq_zero.1 h0, norm_mul, hnl]
  exact mul_le_of_le_one_right (by positivity) (norm_le_one hact hχ K hj.1 hyX)

/- English proof (translation)
The claim follows from `(AddMonoidHomClass.isometry_of_norm (act g) (hact.2 g)).continuous`.
-/
theorem act_continuous (hact : IsActC act) (g : GQ l) : Continuous (act g) :=
  (AddMonoidHomClass.isometry_of_norm (act g) (hact.2 g)).continuous

/- English proof (translation)
Establish `hp : l.Prime` using `Fact.out`. Establish `hl : (1 : ℝ) < l` using `by exact_mod_cast hp.one_lt`. Establish `hl0 : (0 : ℝ) < (l : ℝ)⁻¹` using `by positivity`. Establish `hl1 : (l : ℝ)⁻¹ < 1` using `inv_lt_one_of_one_lt₀ hl`. Use `closure_minimal (s := (Xalg K j : Set (PadicComplex l))) (t := {x : PadicComplex l | ‖ζ - 1‖ * ‖x‖ ≤ l * ‖act g x - x‖}) (fun d hd => ?_) (isClosed_le (continuous_const.mul continuous_norm) (continuous_const.mul ((act_continuous hact g).sub continuous_id).norm)) hx` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `‖ζ - 1‖ * ‖d‖ ≤ l * ‖act g d - d‖`. Rewrite using `[← norm_mul]`. Establish `hdX` using `Xalg_le K j hd`. Break down `(norm_nonneg (act g d - d)).eq_or_lt with h | h` into its components or cases. Rewrite using `[← h, mul_zero]`.

Conclude with `ge_of_tendsto' (tendsto_pow_atTop_nhds_zero_of_lt_one hl0.le hl1) fun n => est_pow hact hχ K hj hg hζ hd n (by rw [← h]; positivity)`. Establish `h1 : ‖act g d - d‖ ≤ 1` using `norm_le_one hact hχ K hj.1 (sub_mem ((GlobalTheory.T.tate_decomposition_completed_cyclotomic_integers l act χ hact hχ K j hj.1).2.2.2.2.1 g (Gj_le K j hg.1) d hdX) hdX)`. Take `⟨n, hn, hn'⟩` from `exists_nat_pow_near_of_lt_one h h1 hl0 hl1`. Use `(est_pow hact hχ K hj hg hζ hd n hn').trans ?_` and prove the remaining obligations. Establish `: (l : ℝ)⁻¹ ^ n = l * (l : ℝ)⁻¹ ^ (n + 1)`.

Rewrite using `[pow_succ]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[this]`. Conclude with `mul_le_mul_of_nonneg_left hn.le (by positivity)`.
-/
theorem est (hact : IsActC act) (hχ : IsCyc χ) (K : FinExt l) {j : ℕ} (hj : Lev l j)
    {g : GQ l} (hg : IsGen χ K j g) {ζ : PadicComplex l} (hζ : IsPrimitiveRoot ζ l)
    {x : PadicComplex l} (hx : x ∈ Xj K j) : ‖ζ - 1‖ * ‖x‖ ≤ l * ‖act g x - x‖ := by
  have hp : l.Prime := Fact.out
  have hl : (1 : ℝ) < l := by exact_mod_cast hp.one_lt
  have hl0 : (0 : ℝ) < (l : ℝ)⁻¹ := by positivity
  have hl1 : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hl
  refine closure_minimal (s := (Xalg K j : Set (PadicComplex l)))
    (t := {x : PadicComplex l | ‖ζ - 1‖ * ‖x‖ ≤ l * ‖act g x - x‖}) (fun d hd => ?_)
    (isClosed_le (continuous_const.mul continuous_norm)
      (continuous_const.mul ((act_continuous hact g).sub continuous_id).norm)) hx
  change ‖ζ - 1‖ * ‖d‖ ≤ l * ‖act g d - d‖
  rw [← norm_mul]
  have hdX := Xalg_le K j hd
  rcases (norm_nonneg (act g d - d)).eq_or_lt with h | h
  · rw [← h, mul_zero]
    exact ge_of_tendsto' (tendsto_pow_atTop_nhds_zero_of_lt_one hl0.le hl1) fun n =>
      est_pow hact hχ K hj hg hζ hd n (by rw [← h]; positivity)
  · have h1 : ‖act g d - d‖ ≤ 1 := norm_le_one hact hχ K hj.1
      (sub_mem ((GlobalTheory.T.tate_decomposition_completed_cyclotomic_integers l act χ hact hχ K j hj.1).2.2.2.2.1 g (Gj_le K j hg.1) d hdX) hdX)
    obtain ⟨n, hn, hn'⟩ := exists_nat_pow_near_of_lt_one h h1 hl0 hl1
    refine (est_pow hact hχ K hj hg hζ hd n hn').trans ?_
    have : (l : ℝ)⁻¹ ^ n = l * (l : ℝ)⁻¹ ^ (n + 1) := by
      rw [pow_succ]; field_simp
    rw [this]
    exact mul_le_mul_of_nonneg_left hn.le (by positivity)

/- English proof (translation)
Establish `hp : l.Prime` using `Fact.out`. Establish `hζ1 : 0 < ‖ζ - 1‖` using `norm_pos_iff.2 (sub_ne_zero.2 (hζ.ne_one hp.one_lt))`. Establish `hcl : IsClosed (Xj K j : Set (PadicComplex l))` using `AddSubgroup.isClosed_topologicalClosure _`. Use `haveI : CompleteSpace ↥(Xj K j) := hcl.completeSpace_coe`. Set `f : ↥(Xj K j) → PadicComplex l` to `fun y => act g y - y`.

Establish `hanti : AntilipschitzWith (Real.toNNReal (l / ‖ζ - 1‖)) f`. Use `AntilipschitzWith.of_le_mul_dist fun a b => ?_` and prove the remaining obligations. Establish `h` using `est hact hχ K hj hg hζ (sub_mem a.2 b.2)`. Rewrite using `[Real.coe_toNNReal _ (by positivity), Subtype.dist_eq, dist_eq_norm, dist_eq_norm, div_mul_eq_mul_div, le_div_iff₀ hζ1, mul_comm]`. Establish `e : f a - f b = act g ((a : PadicComplex l) - b) - ((a : PadicComplex l) - b)`.

Simplify using `only [f, map_sub]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `h`. Establish `huc : UniformContinuous f` using `((AddMonoidHomClass.isometry_of_norm (act g) (hact.2 g)).uniformContinuous.comp uniformContinuous_subtype_val).sub uniformContinuous_subtype_val`.

Establish `hr` using `(hanti.isClosed_range huc).preimage (continuous_const_mul (ζ - 1))`. Establish `hsub : (Xalg K j : Set (PadicComplex l)) ⊆ (fun b => (ζ - 1) * b) ⁻¹' Set.range f`. Introduce `d hd`. Take `⟨y, hy, -, h⟩` from `solve_alg hact hχ K hj hg hζ hd`. Conclude with `⟨⟨y, hy⟩, h⟩`.

Take `⟨y, hy⟩` from `closure_minimal hsub hr hx`. Conclude with `⟨y, y.2, hy⟩`.
-/
theorem solve (hact : IsActC act) (hχ : IsCyc χ) (K : FinExt l) {j : ℕ} (hj : Lev l j)
    {g : GQ l} (hg : IsGen χ K j g) {ζ : PadicComplex l} (hζ : IsPrimitiveRoot ζ l)
    {x : PadicComplex l} (hx : x ∈ Xj K j) : ∃ y ∈ Xj K j, act g y - y = (ζ - 1) * x := by
  have hp : l.Prime := Fact.out
  have hζ1 : 0 < ‖ζ - 1‖ := norm_pos_iff.2 (sub_ne_zero.2 (hζ.ne_one hp.one_lt))
  have hcl : IsClosed (Xj K j : Set (PadicComplex l)) := AddSubgroup.isClosed_topologicalClosure _
  haveI : CompleteSpace ↥(Xj K j) := hcl.completeSpace_coe
  let f : ↥(Xj K j) → PadicComplex l := fun y => act g y - y
  have hanti : AntilipschitzWith (Real.toNNReal (l / ‖ζ - 1‖)) f := by
    refine AntilipschitzWith.of_le_mul_dist fun a b => ?_
    have h := est hact hχ K hj hg hζ (sub_mem a.2 b.2)
    rw [Real.coe_toNNReal _ (by positivity), Subtype.dist_eq, dist_eq_norm, dist_eq_norm,
      div_mul_eq_mul_div, le_div_iff₀ hζ1, mul_comm]
    have e : f a - f b = act g ((a : PadicComplex l) - b) - ((a : PadicComplex l) - b) := by
      simp only [f, map_sub]
      ring
    rw [e]
    exact h
  have huc : UniformContinuous f :=
    ((AddMonoidHomClass.isometry_of_norm (act g) (hact.2 g)).uniformContinuous.comp
      uniformContinuous_subtype_val).sub uniformContinuous_subtype_val
  have hr := (hanti.isClosed_range huc).preimage (continuous_const_mul (ζ - 1))
  have hsub : (Xalg K j : Set (PadicComplex l)) ⊆ (fun b => (ζ - 1) * b) ⁻¹' Set.range f := by
    intro d hd
    obtain ⟨y, hy, -, h⟩ := solve_alg hact hχ K hj hg hζ hd
    exact ⟨⟨y, hy⟩, h⟩
  obtain ⟨y, hy⟩ := closure_minimal hsub hr hx
  exact ⟨y, y.2, hy⟩

end GlobalTheory.Cyc.TateS

namespace GlobalTheory.Cyc

open TateS

/- English proof (translation)
Introduce `l _ act χ hact hχ K j hj g hg ζ hζ`. Establish `hp : l.Prime` using `Fact.out`. Establish `T1` using `GlobalTheory.T.tate_decomposition_completed_cyclotomic_integers l act χ hact hχ K j hj.1`. Establish `hζ1 : 0 < ‖ζ - 1‖` using `norm_pos_iff.2 (sub_ne_zero.2 (hζ.ne_one hp.one_lt))`. Establish `hz` using `zeta_sub_one_mem K hj.1 hζ`.

Establish `hex : ∀ x, ∃ y, x ∈ Xj K j → y ∈ Xj K j ∧ act g y - y = (ζ - 1) * x`. Introduce `x`. Distinguish the cases in `hx : x ∈ Xj K j`. Take `⟨y, hy⟩` from `solve hact hχ K hj hg hζ hx`. Conclude with `⟨y, fun _ => hy⟩`.

Conclude with `⟨0, fun h => absurd h hx⟩`. Use `choose S hS using hex`. Establish `huniq : ∀ x ∈ Xj K j, ∀ y ∈ Xj K j, act g y - y = (ζ - 1) * x → S x = y`. Introduce `x hx y hy h`. Establish `h1` using `est hact hχ K hj hg hζ (sub_mem (hS x hx).1 hy)`.

Establish `h2 : act g (S x - y) - (S x - y) = 0`. Rewrite using `[map_sub]`. Take the linear combination `(hS x hx).2 - h`. Rewrite `h1` using `[h2, norm_zero, mul_zero]`. Establish `h3 : ‖S x - y‖ ≤ 0`.

Assume the negation of the conclusion as `hc`. Conclude with `absurd h1 (not_le.2 (mul_pos hζ1 (not_le.1 hc)))`. Conclude with `sub_eq_zero.1 (norm_le_zero_iff.1 h3)`. Use `⟨S, fun x hx => ⟨(hS x hx).1, ?_, (hS x hx).2, ?_⟩, fun x hx x' hx' => ?_, fun y hy x hx => ?_⟩` and prove the remaining obligations. Establish `h1` using `est hact hχ K hj hg hζ (hS x hx).1`.

Rewrite `h1` using `[(hS x hx).2, norm_mul, mul_left_comm]`. Conclude with `le_of_mul_le_mul_left h1 hζ1`. Use `huniq _ (sub_mem (T1.2.2.2.2.1 g (Gj_le K j hg.1) x hx) hx) _ (T1.2.2.2.1 _ hz x hx) ?_` and prove the remaining obligations. Rewrite using `[map_mul, act_fix hact K hg.1 hz.1]`. Expand and normalize the polynomial expressions, which then agree.

Use `huniq _ (add_mem hx hx') _ (add_mem (hS x hx).1 (hS x' hx').1) ?_` and prove the remaining obligations. Rewrite using `[map_add]`. Take the linear combination `(hS x hx).2 + (hS x' hx').2`. Use `huniq _ (T1.2.2.2.1 y hy x hx) _ (T1.2.2.2.1 y hy _ (hS x hx).1) ?_` and prove the remaining obligations. Rewrite using `[map_mul, act_fix hact K hg.1 hy.1]`.

Take the linear combination `y * (hS x hx).2`.
-/
theorem exists_tate_operator_bound : ∀ (l : ℕ) [Fact l.Prime] (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) (χ : GQ l →* ℚ_[l]ˣ), IsActC act → IsCyc χ → ∀ (K : FinExt l), ∀ j : ℕ, Lev l j → ∀ g, IsGen χ K j g → ∀ ζ : PadicComplex l, IsPrimitiveRoot ζ l → ∃ S : PadicComplex l → PadicComplex l, (∀ x ∈ Xj K j, S x ∈ Xj K j ∧ ‖S x‖ ≤ (l : ℝ) * ‖x‖ ∧ act g (S x) - S x = (ζ - 1) * x ∧ S (act g x - x) = (ζ - 1) * x) ∧ (∀ x ∈ Xj K j, ∀ x' ∈ Xj K j, S (x + x') = S x + S x') ∧ ∀ y ∈ intC (Ks K j), ∀ x ∈ Xj K j, S (y * x) = y * S x := by
  classical
  intro l _ act χ hact hχ K j hj g hg ζ hζ
  have hp : l.Prime := Fact.out
  have T1 := GlobalTheory.T.tate_decomposition_completed_cyclotomic_integers l act χ hact hχ K j hj.1
  have hζ1 : 0 < ‖ζ - 1‖ := norm_pos_iff.2 (sub_ne_zero.2 (hζ.ne_one hp.one_lt))
  have hz := zeta_sub_one_mem K hj.1 hζ
  have hex : ∀ x, ∃ y, x ∈ Xj K j → y ∈ Xj K j ∧ act g y - y = (ζ - 1) * x := by
    intro x
    by_cases hx : x ∈ Xj K j
    · obtain ⟨y, hy⟩ := solve hact hχ K hj hg hζ hx
      exact ⟨y, fun _ => hy⟩
    · exact ⟨0, fun h => absurd h hx⟩
  choose S hS using hex
  have huniq : ∀ x ∈ Xj K j, ∀ y ∈ Xj K j, act g y - y = (ζ - 1) * x → S x = y := by
    intro x hx y hy h
    have h1 := est hact hχ K hj hg hζ (sub_mem (hS x hx).1 hy)
    have h2 : act g (S x - y) - (S x - y) = 0 := by
      rw [map_sub]; linear_combination (hS x hx).2 - h
    rw [h2, norm_zero, mul_zero] at h1
    have h3 : ‖S x - y‖ ≤ 0 := by
      by_contra hc
      exact absurd h1 (not_le.2 (mul_pos hζ1 (not_le.1 hc)))
    exact sub_eq_zero.1 (norm_le_zero_iff.1 h3)
  refine ⟨S, fun x hx => ⟨(hS x hx).1, ?_, (hS x hx).2, ?_⟩, fun x hx x' hx' => ?_,
    fun y hy x hx => ?_⟩
  · have h1 := est hact hχ K hj hg hζ (hS x hx).1
    rw [(hS x hx).2, norm_mul, mul_left_comm] at h1
    exact le_of_mul_le_mul_left h1 hζ1
  · refine huniq _ (sub_mem (T1.2.2.2.2.1 g (Gj_le K j hg.1) x hx) hx) _ (T1.2.2.2.1 _ hz x hx) ?_
    rw [map_mul, act_fix hact K hg.1 hz.1]
    ring
  · refine huniq _ (add_mem hx hx') _ (add_mem (hS x hx).1 (hS x' hx').1) ?_
    rw [map_add]
    linear_combination (hS x hx).2 + (hS x' hx').2
  · refine huniq _ (T1.2.2.2.1 y hy x hx) _ (T1.2.2.2.1 y hy _ (hS x hx).1) ?_
    rw [map_mul, act_fix hact K hg.1 hy.1]
    linear_combination y * (hS x hx).2

/- English proof (translation)
Introduce `l _ act χ hact hχ K j hj g hg ζ hζ`. Take `⟨S, h1, h2⟩` from `exists_tate_operator_bound l act χ hact hχ K j hj g hg ζ hζ`. Conclude with `⟨S, fun x hx => ⟨(h1 x hx).1, (h1 x hx).2.2⟩, h2⟩`.
-/
theorem exists_tate_operator : ∀ (l : ℕ) [Fact l.Prime] (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) (χ : GQ l →* ℚ_[l]ˣ), IsActC act → IsCyc χ → ∀ (K : FinExt l), ∀ j : ℕ, Lev l j → ∀ g, IsGen χ K j g → ∀ ζ : PadicComplex l, IsPrimitiveRoot ζ l → ∃ S : PadicComplex l → PadicComplex l, (∀ x ∈ Xj K j, S x ∈ Xj K j ∧ act g (S x) - S x = (ζ - 1) * x ∧ S (act g x - x) = (ζ - 1) * x) ∧ (∀ x ∈ Xj K j, ∀ x' ∈ Xj K j, S (x + x') = S x + S x') ∧ ∀ y ∈ intC (Ks K j), ∀ x ∈ Xj K j, S (y * x) = y * S x := by
  intro l _ act χ hact hχ K j hj g hg ζ hζ
  obtain ⟨S, h1, h2⟩ := exists_tate_operator_bound l act χ hact hχ K j hj g hg ζ hζ
  exact ⟨S, fun x hx => ⟨(h1 x hx).1, (h1 x hx).2.2⟩, h2⟩

end GlobalTheory.Cyc
