import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.SubThickRees
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.IsCompl

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry Polynomial DividedPowers GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B

namespace GlobalTheory.CompanionTheory.PDFil

variable {B : Type} [CommRing B] {J : Ideal B}

/- English proof (translation)
Unfold `GlobalTheory.PDA.fil`. Rewrite using `[Ideal.span_mul_span']`. Use `Ideal.span_mono ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨_, ⟨l, hl, hn, rfl⟩, _, ⟨m, hm, hk, rfl⟩, rfl⟩`. Use `⟨l ++ m, ?_, ?_, ?_⟩` and prove the remaining obligations.

Introduce `p hp`. Break down `List.mem_append.1 hp with h | h` into its components or cases. Conclude with `hl p h`. Conclude with `hm p h`. Simplify using `only [List.map_append, List.sum_append]`.

Use linear arithmetic over natural numbers and integers. Simplify using `only [List.map_append, List.prod_append]`.
-/
theorem fil_mul_le (δ : DividedPowers J) (a c : ℕ) :
    GlobalTheory.PDA.fil δ a * GlobalTheory.PDA.fil δ c ≤ GlobalTheory.PDA.fil δ (a + c) := by
  unfold GlobalTheory.PDA.fil
  rw [Ideal.span_mul_span']
  refine Ideal.span_mono ?_
  rintro _ ⟨_, ⟨l, hl, hn, rfl⟩, _, ⟨m, hm, hk, rfl⟩, rfl⟩
  refine ⟨l ++ m, ?_, ?_, ?_⟩
  · intro p hp
    rcases List.mem_append.1 hp with h | h
    · exact hl p h
    · exact hm p h
  · simp only [List.map_append, List.sum_append]
    omega
  · simp only [List.map_append, List.prod_append]

/- English proof (translation)
Use `Ideal.span_mono ?_` and prove the remaining obligations. Introduce and unpack `b ⟨l, h1, h2, h3⟩`. Conclude with `⟨l, h1, h.trans h2, h3⟩`.
-/
theorem fil_anti (δ : DividedPowers J) {a c : ℕ} (h : a ≤ c) :
    GlobalTheory.PDA.fil δ c ≤ GlobalTheory.PDA.fil δ a := by
  refine Ideal.span_mono ?_
  rintro b ⟨l, h1, h2, h3⟩
  exact ⟨l, h1, h.trans h2, h3⟩

/- English proof (translation)
The claim follows from `(Ideal.eq_top_iff_one _).2 (Ideal.subset_span ⟨[], by simp, by simp, by simp⟩)`.
-/
theorem fil_zero (δ : DividedPowers J) : GlobalTheory.PDA.fil δ 0 = ⊤ :=
  (Ideal.eq_top_iff_one _).2 (Ideal.subset_span ⟨[], by simp, by simp, by simp⟩)

/- English proof (translation)
The claim follows from `Ideal.subset_span ⟨[(n, x)], by simpa using hx, by simp, by simp⟩`.
-/
theorem dpow_mem_fil (δ : DividedPowers J) (n : ℕ) {x : B} (hx : x ∈ J) :
    δ.dpow n x ∈ GlobalTheory.PDA.fil δ n :=
  Ideal.subset_span ⟨[(n, x)], by simpa using hx, by simp, by simp⟩

def coefFil (δ : DividedPowers J) (Q : PDPoly B) (r : ℕ) : Submodule B Q.P where
  carrier := {z | ∀ k, Q.e.repr z k ∈ GlobalTheory.PDA.fil δ (r - k)}
  add_mem' := by
    intro x y hx hy k
    simpa using Ideal.add_mem _ (hx k) (hy k)
  zero_mem' := by
    intro k
    simp
  smul_mem' := by
    intro c x hx k
    simpa using Ideal.mul_mem_left _ c (hx k)

/- English proof (translation)
The claim follows from `fun k ↦ fil_anti δ (by omega) (hz k)`.
-/
theorem coefFil_anti (δ : DividedPowers J) (Q : PDPoly B) {a c : ℕ} (h : a ≤ c) {z : Q.P}
    (hz : z ∈ coefFil δ Q c) : z ∈ coefFil δ Q a :=
  fun k ↦ fil_anti δ (by omega) (hz k)

/- English proof (translation)
Introduce `k`. Simplify using `[fil_zero]`.
-/
theorem mem_coefFil_zero (δ : DividedPowers J) (Q : PDPoly B) (z : Q.P) :
    z ∈ coefFil δ Q 0 := by
  intro k
  simp [fil_zero]

/- English proof (translation)
Introduce `j`. Distinguish the cases in `h : j = k`. Substitute `h` using the available equality. Simplify using `using hb`. Establish `: Q.e.repr (b • Q.e k) j = 0`.

Simplify using `[Finsupp.single_apply, Ne.symm h]`. Rewrite using `[this]`. Conclude with `Ideal.zero_mem _`.
-/
theorem smul_e_mem_coefFil (δ : DividedPowers J) (Q : PDPoly B) {r k : ℕ} {b : B}
    (hb : b ∈ GlobalTheory.PDA.fil δ (r - k)) : b • Q.e k ∈ coefFil δ Q r := by
  intro j
  by_cases h : j = k
  · subst h
    simpa using hb
  · have : Q.e.repr (b • Q.e k) j = 0 := by
      simp [Finsupp.single_apply, Ne.symm h]
    rw [this]
    exact Ideal.zero_mem _

/- English proof (translation)
Use `conv_lhs => rw [← Q.e.linearCombination_repr z]`. Both sides reduce to the same expression.
-/
theorem eq_sum_repr (Q : PDPoly B) (z : Q.P) :
    z = ∑ k ∈ (Q.e.repr z).support, Q.e.repr z k • Q.e k := by
  conv_lhs => rw [← Q.e.linearCombination_repr z]
  rfl

/- English proof (translation)
Establish `h1 : b * b' ∈ GlobalTheory.PDA.fil δ (a + c - (k + l))` using `fil_anti δ (by omega) (fil_mul_le δ _ _ (Ideal.mul_mem_mul hb hb'))`. Rewrite using `[smul_mul_smul_comm, Q.e_mul, ← nsmul_eq_mul, smul_comm]`. Conclude with `nsmul_mem (smul_e_mem_coefFil δ Q h1) _`.
-/
theorem smul_e_mul_smul_e_mem (δ : DividedPowers J) (Q : PDPoly B) {a c k l : ℕ} {b b' : B}
    (hb : b ∈ GlobalTheory.PDA.fil δ (a - k)) (hb' : b' ∈ GlobalTheory.PDA.fil δ (c - l)) :
    (b • Q.e k) * (b' • Q.e l) ∈ coefFil δ Q (a + c) := by
  have h1 : b * b' ∈ GlobalTheory.PDA.fil δ (a + c - (k + l)) :=
    fil_anti δ (by omega) (fil_mul_le δ _ _ (Ideal.mul_mem_mul hb hb'))
  rw [smul_mul_smul_comm, Q.e_mul, ← nsmul_eq_mul, smul_comm]
  exact nsmul_mem (smul_e_mem_coefFil δ Q h1) _

/- English proof (translation)
Rewrite using `[eq_sum_repr Q z, eq_sum_repr Q w, Finset.sum_mul_sum]`. Conclude with `Submodule.sum_mem _ fun k _ ↦ Submodule.sum_mem _ fun l _ ↦ smul_e_mul_smul_e_mem δ Q (hz k) (hw l)`.
-/
theorem mul_mem_coefFil (δ : DividedPowers J) (Q : PDPoly B) {a c : ℕ} {z w : Q.P}
    (hz : z ∈ coefFil δ Q a) (hw : w ∈ coefFil δ Q c) : z * w ∈ coefFil δ Q (a + c) := by
  rw [eq_sum_repr Q z, eq_sum_repr Q w, Finset.sum_mul_sum]
  exact Submodule.sum_mem _ fun k _ ↦ Submodule.sum_mem _ fun l _ ↦
    smul_e_mul_smul_e_mem δ Q (hz k) (hw l)

def coefIdeal (δ : DividedPowers J) (Q : PDPoly B) (r : ℕ) : Ideal Q.P where
  carrier := coefFil δ Q r
  add_mem' := (coefFil δ Q r).add_mem
  zero_mem' := (coefFil δ Q r).zero_mem
  smul_mem' := by
    intro c x hx
    simpa using mul_mem_coefFil δ Q (mem_coefFil_zero δ Q c) hx

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_coefIdeal (δ : DividedPowers J) (Q : PDPoly B) (r : ℕ) (z : Q.P) :
    z ∈ coefIdeal δ Q r ↔ z ∈ coefFil δ Q r := Iff.rfl

/- English proof (translation)
Establish `: algebraMap B Q.P b = b • Q.e 0`. Rewrite using `[Q.e_zero, Algebra.algebraMap_eq_smul_one]`. Rewrite using `[this]`. Conclude with `smul_e_mem_coefFil δ Q (by simpa using hb)`.
-/
theorem algebraMap_mem_coefFil (δ : DividedPowers J) (Q : PDPoly B) {r : ℕ} {b : B}
    (hb : b ∈ GlobalTheory.PDA.fil δ r) : algebraMap B Q.P b ∈ coefFil δ Q r := by
  have : algebraMap B Q.P b = b • Q.e 0 := by
    rw [Q.e_zero, Algebra.algebraMap_eq_smul_one]
  rw [this]
  exact smul_e_mem_coefFil δ Q (by simpa using hb)

/- English proof (translation)
Establish `: (1 : B) ∈ GlobalTheory.PDA.fil δ (n - m)`. Rewrite using `[Nat.sub_eq_zero_of_le h, fil_zero]`. Discharge the goal by the elementary cases of `trivial`. Simplify using `using smul_e_mem_coefFil δ Q this`.
-/
theorem e_mem_coefFil (δ : DividedPowers J) (Q : PDPoly B) {n m : ℕ} (h : n ≤ m) :
    Q.e m ∈ coefFil δ Q n := by
  have : (1 : B) ∈ GlobalTheory.PDA.fil δ (n - m) := by
    rw [Nat.sub_eq_zero_of_le h, fil_zero]
    trivial
  simpa using smul_e_mem_coefFil δ Q this

/- English proof (translation)
The claim follows from `Ideal.mem_sup_right (Ideal.subset_span ⟨k, rfl⟩)`.
-/
theorem e_mem_ext (Q : PDPoly B) (J : Ideal B) (k : ℕ) : Q.e (k + 1) ∈ Q.ext J :=
  Ideal.mem_sup_right (Ideal.subset_span ⟨k, rfl⟩)

/- English proof (translation)
Set `S : Ideal Q.P` to `{ carrier := {y | y ∈ Q.ext J ∧ ∀ n, η.dpow n y ∈ coefFil δ Q n} add_mem' := by`. Introduce and unpack `x y ⟨hx, hx'⟩ ⟨hy, hy'⟩`. Use `⟨Ideal.add_mem _ hx hy, fun n ↦ ?_⟩` and prove the remaining obligations. Rewrite using `[η.dpow_add hx hy]`. Use `Submodule.sum_mem _ fun p hp ↦ ?_` and prove the remaining obligations.

Use `mul_mem_coefFil δ Q (hx' p.1) (hy' p.2)` as an intermediate fact. Rewrite `this` using `[Finset.HasAntidiagonal.mem_antidiagonal.1 hp]`. Then use the resulting hypothesis. Use the proof step `zero_mem' := by`. Use `⟨Ideal.zero_mem _, fun n ↦ ?_⟩` and prove the remaining obligations. Break down `Nat.eq_zero_or_pos n with rfl | hn` into its components or cases.

Conclude with `mem_coefFil_zero δ Q _`. Rewrite using `[η.dpow_eval_zero hn.ne']`. Conclude with `Submodule.zero_mem _`. Use the proof step `smul_mem' := by`. Introduce and unpack `a y ⟨hy, hy'⟩`.

Use `⟨Ideal.mul_mem_left _ a hy, fun n ↦ ?_⟩` and prove the remaining obligations. Rewrite using `[smul_eq_mul, η.dpow_mul hy]`. Conclude with `(coefIdeal δ Q n).mul_mem_left _ (hy' n) }`. Establish `hS : Q.ext J ≤ S`. Use `sup_le (Ideal.map_le_iff_le_comap.2 fun j hj ↦ ?_) (Ideal.span_le.2 ?_)` and prove the remaining obligations.

Use `⟨Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hj), fun n ↦ ?_⟩` and prove the remaining obligations. Rewrite using `[h.dp.dpow_comp j hj]`. Conclude with `algebraMap_mem_coefFil δ Q (dpow_mem_fil δ n hj)`. Introduce and unpack `_ ⟨k, rfl⟩`. Establish `h1 : Q.e 1 ∈ Q.ext J` using `e_mem_ext Q J 0`.

Use `⟨e_mem_ext Q J k, fun n ↦ ?_⟩` and prove the remaining obligations. Use `show η.dpow n (Q.e (k + 1)) ∈ coefFil δ Q n`. Rewrite using `[← h.var (k + 1), η.dpow_comp (Nat.succ_ne_zero k) h1, h.var, ← nsmul_eq_mul]`. Conclude with `nsmul_mem (e_mem_coefFil δ Q (Nat.le_mul_of_pos_right n (Nat.succ_pos k))) _`. Conclude with `(hS hy).2 n`.
-/
theorem dpow_mem_coefFil (δ : DividedPowers J) (Q : PDPoly B) (η : DividedPowers (Q.ext J))
    (h : Q.IsStd δ η) {y : Q.P} (hy : y ∈ Q.ext J) (n : ℕ) :
    η.dpow n y ∈ coefFil δ Q n := by
  let S : Ideal Q.P :=
    { carrier := {y | y ∈ Q.ext J ∧ ∀ n, η.dpow n y ∈ coefFil δ Q n}
      add_mem' := by
        rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
        refine ⟨Ideal.add_mem _ hx hy, fun n ↦ ?_⟩
        rw [η.dpow_add hx hy]
        refine Submodule.sum_mem _ fun p hp ↦ ?_
        have := mul_mem_coefFil δ Q (hx' p.1) (hy' p.2)
        rwa [Finset.HasAntidiagonal.mem_antidiagonal.1 hp] at this
      zero_mem' := by
        refine ⟨Ideal.zero_mem _, fun n ↦ ?_⟩
        rcases Nat.eq_zero_or_pos n with rfl | hn
        · exact mem_coefFil_zero δ Q _
        · rw [η.dpow_eval_zero hn.ne']
          exact Submodule.zero_mem _
      smul_mem' := by
        rintro a y ⟨hy, hy'⟩
        refine ⟨Ideal.mul_mem_left _ a hy, fun n ↦ ?_⟩
        rw [smul_eq_mul, η.dpow_mul hy]
        exact (coefIdeal δ Q n).mul_mem_left _ (hy' n) }
  have hS : Q.ext J ≤ S := by
    refine sup_le (Ideal.map_le_iff_le_comap.2 fun j hj ↦ ?_) (Ideal.span_le.2 ?_)
    · refine ⟨Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hj), fun n ↦ ?_⟩
      rw [h.dp.dpow_comp j hj]
      exact algebraMap_mem_coefFil δ Q (dpow_mem_fil δ n hj)
    · rintro _ ⟨k, rfl⟩
      have h1 : Q.e 1 ∈ Q.ext J := e_mem_ext Q J 0
      refine ⟨e_mem_ext Q J k, fun n ↦ ?_⟩
      show η.dpow n (Q.e (k + 1)) ∈ coefFil δ Q n
      rw [← h.var (k + 1), η.dpow_comp (Nat.succ_ne_zero k) h1, h.var, ← nsmul_eq_mul]
      exact nsmul_mem (e_mem_coefFil δ Q (Nat.le_mul_of_pos_right n (Nat.succ_pos k))) _
  exact (hS hy).2 n

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => simpa using mem_coefFil_zero δ Q 1`. Consider the case `cons p l ih`. Simplify using `only [List.map_cons, List.prod_cons, List.sum_cons]`. Conclude with `mul_mem_coefFil δ Q (dpow_mem_coefFil δ Q η h (hl p (by simp)) p.1) (ih fun q hq ↦ hl q (List.mem_cons_of_mem _ hq))`.
-/
theorem prod_dpow_mem_coefFil (δ : DividedPowers J) (Q : PDPoly B) (η : DividedPowers (Q.ext J))
    (h : Q.IsStd δ η) (l : List (ℕ × Q.P)) (hl : ∀ p ∈ l, p.2 ∈ Q.ext J) :
    (l.map fun p ↦ η.dpow p.1 p.2).prod ∈ coefFil δ Q (l.map Prod.fst).sum := by
  induction l with
  | nil => simpa using mem_coefFil_zero δ Q 1
  | cons p l ih =>
    simp only [List.map_cons, List.prod_cons, List.sum_cons]
    exact mul_mem_coefFil δ Q (dpow_mem_coefFil δ Q η h (hl p (by simp)) p.1)
      (ih fun q hq ↦ hl q (List.mem_cons_of_mem _ hq))

/- English proof (translation)
Use `Ideal.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨l, hl, hn, rfl⟩`. Conclude with `coefFil_anti δ Q hn (prod_dpow_mem_coefFil δ Q η h l hl)`.
-/
theorem fil_le_coefIdeal (δ : DividedPowers J) (Q : PDPoly B) (η : DividedPowers (Q.ext J))
    (h : Q.IsStd δ η) (r : ℕ) : GlobalTheory.PDA.fil η r ≤ coefIdeal δ Q r := by
  refine Ideal.span_le.2 ?_
  rintro _ ⟨l, hl, hn, rfl⟩
  exact coefFil_anti δ Q hn (prod_dpow_mem_coefFil δ Q η h l hl)

/- English proof (translation)
Establish `: (GlobalTheory.PDA.fil δ r).map (algebraMap B Q.P) ≤ GlobalTheory.PDA.fil η r`. Use `Ideal.map_le_iff_le_comap.2 (Ideal.span_le.2 ?_)` and prove the remaining obligations. Introduce and unpack `_ ⟨l, hl, hn, rfl⟩`. Establish `hmem : ∀ p ∈ l, algebraMap B Q.P p.2 ∈ Q.ext J` using `fun p hp ↦ Ideal.mem_sup_left (Ideal.mem_map_of_mem _ (hl p hp))`. Establish `key : algebraMap B Q.P (l.map fun p ↦ δ.dpow p.1 p.2).prod = ((l.map fun p ↦ (p.1, algebraMap B Q.P p.2)).map fun p ↦ η.dpow p.1 p.2).prod`.

Rewrite using `[map_list_prod, List.map_map, List.map_map]`. Use `congr 1`. Use `List.map_congr_left fun p hp ↦ ?_` and prove the remaining obligations. Conclude with `(h.dp.dpow_comp p.2 (hl p hp)).symm`. Use `show algebraMap B Q.P _ ∈ GlobalTheory.PDA.fil η r`.

Rewrite using `[key]`. Use `Ideal.subset_span ⟨_, ?_, ?_, rfl⟩` and prove the remaining obligations. Introduce `p hp`. Take `⟨q, hq, rfl⟩` from `List.mem_map.1 hp`. Conclude with `hmem q hq`.

Simplify `hn` using `[List.map_map, Function.comp_def]`. Conclude with `this (Ideal.mem_map_of_mem _ hb)`.
-/
theorem algebraMap_mem_fil (δ : DividedPowers J) (Q : PDPoly B) (η : DividedPowers (Q.ext J))
    (h : Q.IsStd δ η) (r : ℕ) {b : B} (hb : b ∈ GlobalTheory.PDA.fil δ r) :
    algebraMap B Q.P b ∈ GlobalTheory.PDA.fil η r := by
  have : (GlobalTheory.PDA.fil δ r).map (algebraMap B Q.P) ≤ GlobalTheory.PDA.fil η r := by
    refine Ideal.map_le_iff_le_comap.2 (Ideal.span_le.2 ?_)
    rintro _ ⟨l, hl, hn, rfl⟩
    have hmem : ∀ p ∈ l, algebraMap B Q.P p.2 ∈ Q.ext J := fun p hp ↦
      Ideal.mem_sup_left (Ideal.mem_map_of_mem _ (hl p hp))
    have key : algebraMap B Q.P (l.map fun p ↦ δ.dpow p.1 p.2).prod =
        ((l.map fun p ↦ (p.1, algebraMap B Q.P p.2)).map fun p ↦ η.dpow p.1 p.2).prod := by
      rw [map_list_prod, List.map_map, List.map_map]
      congr 1
      refine List.map_congr_left fun p hp ↦ ?_
      exact (h.dp.dpow_comp p.2 (hl p hp)).symm
    show algebraMap B Q.P _ ∈ GlobalTheory.PDA.fil η r
    rw [key]
    refine Ideal.subset_span ⟨_, ?_, ?_, rfl⟩
    · intro p hp
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
      exact hmem q hq
    · simpa [List.map_map, Function.comp_def] using hn
  exact this (Ideal.mem_map_of_mem _ hb)

/- English proof (translation)
Rewrite using `[eq_sum_repr Q z]`. Use `Ideal.sum_mem _ fun k _ ↦ ?_` and prove the remaining obligations. Establish `h1 : Q.e 1 ∈ Q.ext J` using `e_mem_ext Q J 0`. Establish `hk : Q.e k ∈ GlobalTheory.PDA.fil η k`. Rewrite using `[← h.var k]`.

Conclude with `dpow_mem_fil η k h1`. Rewrite using `[Algebra.smul_def]`. Conclude with `fil_anti η (by omega) (fil_mul_le η _ _ (Ideal.mul_mem_mul (algebraMap_mem_fil δ Q η h _ (hz k)) hk))`.
-/
theorem coefFil_le_fil (δ : DividedPowers J) (Q : PDPoly B) (η : DividedPowers (Q.ext J))
    (h : Q.IsStd δ η) (r : ℕ) {z : Q.P} (hz : z ∈ coefFil δ Q r) : z ∈ GlobalTheory.PDA.fil η r := by
  rw [eq_sum_repr Q z]
  refine Ideal.sum_mem _ fun k _ ↦ ?_
  have h1 : Q.e 1 ∈ Q.ext J := e_mem_ext Q J 0
  have hk : Q.e k ∈ GlobalTheory.PDA.fil η k := by
    rw [← h.var k]
    exact dpow_mem_fil η k h1
  rw [Algebra.smul_def]
  exact fil_anti η (by omega)
    (fil_mul_le η _ _ (Ideal.mul_mem_mul (algebraMap_mem_fil δ Q η h _ (hz k)) hk))

/- English proof (translation)
Introduce `B _ J δ Q η h`. Conclude with `⟨fil_mul_le δ, fun _ _ hac ↦ fil_anti δ hac, fil_zero δ, fun r z ↦ ⟨fun hz ↦ fil_le_coefIdeal δ Q η h r hz, fun hz ↦ coefFil_le_fil δ Q η h r hz⟩⟩`.
-/
theorem fil_pdPoly : ∀ {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) (Q : PDPoly B) (η : DividedPowers (Q.ext J)), Q.IsStd δ η → (∀ a c, fil δ a * fil δ c ≤ fil δ (a + c)) ∧ (∀ a c, a ≤ c → fil δ c ≤ fil δ a) ∧ fil δ 0 = ⊤ ∧ ∀ (r : ℕ) (z : Q.P), z ∈ fil η r ↔ ∀ k, Q.e.repr z k ∈ fil δ (r - k) := by
  intro B _ J δ Q η h
  exact ⟨fil_mul_le δ, fun _ _ hac ↦ fil_anti δ hac, fil_zero δ, fun r z ↦
    ⟨fun hz ↦ fil_le_coefIdeal δ Q η h r hz, fun hz ↦ coefFil_le_fil δ Q η h r hz⟩⟩

end GlobalTheory.CompanionTheory.PDFil
