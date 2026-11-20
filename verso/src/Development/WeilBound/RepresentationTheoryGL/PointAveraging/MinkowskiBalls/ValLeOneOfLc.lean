import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.GermIntegrals.StepSt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HermitianFormNormSqLeReMulReStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField

open MeasureTheory PositivityTheory.Tls2.Ming3 GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL ValuativeRel

noncomputable section

namespace PositivityTheory.Rg.Ming.CoreX

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
The claim follows from `mul_lt_mul_of_pos_right h (zero_lt_iff.2 hc)`.
-/
theorem vmul_lt {a b c : ValueGroupWithZero k} (h : a < b) (hc : c ≠ 0) : a * c < b * c :=
  mul_lt_mul_of_pos_right h (zero_lt_iff.2 hc)

/- English proof (translation)
Apply the tactic sequence `first | exact mul_le_mul_left₀ hc | exact mul_le_mul_iff_right₀ (zero_lt_iff.2 hc)`.
-/
theorem vmul_le_iff {a b c : ValueGroupWithZero k} (hc : c ≠ 0) : c * a ≤ c * b ↔ a ≤ b := by
  first | exact mul_le_mul_left₀ hc | exact mul_le_mul_iff_right₀ (zero_lt_iff.2 hc)

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Use `push_neg at hne`. Take `⟨a0, -, ha0⟩` from `Finset.exists_max_image Finset.univ (fun b => valuation k (t b)) ⟨a, Finset.mem_univ _⟩`. Establish `hm : γ < valuation k (t a0)` using `hne.trans_le (ha0 a (Finset.mem_univ _))`. Establish `hm0 : valuation k (t a0) ≠ 0` using `(lt_of_le_of_lt zero_le' hm).ne'`.

Establish `hS : valuation k (∑ b, E a0 b * t b) < valuation k (t a0)`. Apply `Valuation.map_sum_lt _ hm0` to reduce the goal to its premises. Introduce `b _`. Rewrite using `[Valuation.map_mul]`. Combine the equalities or inequalities in the displayed calculation.

Establish `he : t a0 = (t a0 + ∑ b, E a0 b * t b) + -∑ b, E a0 b * t b` using `by ring`. Establish `h2 : valuation k (t a0) < valuation k (t a0)` using `by conv_lhs => rw [he]`. Conclude with `(valuation k).map_add_lt ((h a0).trans_lt hm) (by rw [Valuation.map_neg]; exact hS)`. Conclude with `lt_irrefl _ h2`.
-/
theorem near_id {j : ℕ} (E : Fin j → Fin j → k) (hE : ∀ a b, valuation k (E a b) < 1)
    (t : Fin j → k) (γ : ValueGroupWithZero k)
    (h : ∀ a, valuation k (t a + ∑ b, E a b * t b) ≤ γ) (a : Fin j) : valuation k (t a) ≤ γ := by
  by_contra hne
  push_neg at hne
  obtain ⟨a0, -, ha0⟩ := Finset.exists_max_image Finset.univ (fun b => valuation k (t b))
    ⟨a, Finset.mem_univ _⟩
  have hm : γ < valuation k (t a0) := hne.trans_le (ha0 a (Finset.mem_univ _))
  have hm0 : valuation k (t a0) ≠ 0 := (lt_of_le_of_lt zero_le' hm).ne'
  have hS : valuation k (∑ b, E a0 b * t b) < valuation k (t a0) := by
    apply Valuation.map_sum_lt _ hm0
    intro b _
    rw [Valuation.map_mul]
    calc valuation k (E a0 b) * valuation k (t b) ≤ valuation k (E a0 b) * valuation k (t a0) :=
          mul_le_mul' le_rfl (ha0 b (Finset.mem_univ _))
      _ < 1 * valuation k (t a0) := vmul_lt (hE a0 b) hm0
      _ = _ := one_mul _
  have he : t a0 = (t a0 + ∑ b, E a0 b * t b) + -∑ b, E a0 b * t b := by ring
  have h2 : valuation k (t a0) < valuation k (t a0) := by
    conv_lhs => rw [he]
    exact (valuation k).map_add_lt ((h a0).trans_lt hm) (by rw [Valuation.map_neg]; exact hS)
  exact lt_irrefl _ h2

section Mat

variable {n r j : ℕ}

def Lc (hjr : j ≤ r) (c : kˣ) (x : Matrix (Fin n) (Fin r) k) : Prop :=
  ∀ i (a : Fin j), valuation k (x i (Fin.castLE hjr a) - idem k r n j i (Fin.castLE hjr a)) ≤ valuation k (c : k)

/- English proof (translation)
Simplify using `only [idem, Matrix.of_apply, Fin.coe_castLE]`. Distinguish the cases in `h : a = b`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Rewrite using `[if_neg h, if_neg]`.

Introduce `h'`. Conclude with `h (Fin.ext h'.1)`.
-/
theorem idem_JJ (hjn : j ≤ n) (hjr : j ≤ r) (a b : Fin j) :
    idem k r n j (Fin.castLE hjn a) (Fin.castLE hjr b) = if a = b then 1 else 0 := by
  simp only [idem, Matrix.of_apply, Fin.coe_castLE]
  by_cases h : a = b
  · subst h; simp
  · rw [if_neg h, if_neg]; intro h'; exact h (Fin.ext h'.1)

/- English proof (translation)
Simplify using `only [idem, Matrix.of_apply]`. Rewrite using `[if_neg]`. Use linear arithmetic over natural numbers and integers.
-/
theorem idem_right (i : Fin n) (l : Fin r) (hl : j ≤ l.val) : idem k r n j i l = 0 := by
  simp only [idem, Matrix.of_apply]
  rw [if_neg]; omega

/- English proof (translation)
Establish `h1 : valuation k (idem k r n j i (Fin.castLE hjr a)) ≤ 1`. Apply the tactic sequence `simp only [idem, Matrix.of_apply]; split_ifs <;> simp`. Establish `: x i (Fin.castLE hjr a) = (x i (Fin.castLE hjr a) - idem k r n j i (Fin.castLE hjr a)) + idem k r n j i (Fin.castLE hjr a)` using `by ring`. Rewrite using `[this]`. Conclude with `(valuation k).map_add_le ((hL i a).trans hc.le) h1`.
-/
theorem val_le_one_of_Lc (hjr : j ≤ r) {c : kˣ} (hc : valuation k (c : k) < 1)
    {x : Matrix (Fin n) (Fin r) k} (hL : Lc hjr c x) (i : Fin n) (a : Fin j) :
    valuation k (x i (Fin.castLE hjr a)) ≤ 1 := by
  have h1 : valuation k (idem k r n j i (Fin.castLE hjr a)) ≤ 1 := by
    simp only [idem, Matrix.of_apply]; split_ifs <;> simp
  have : x i (Fin.castLE hjr a) = (x i (Fin.castLE hjr a) - idem k r n j i (Fin.castLE hjr a)) +
      idem k r n j i (Fin.castLE hjr a) := by ring
  rw [this]
  exact (valuation k).map_add_le ((hL i a).trans hc.le) h1

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h a`. Use `near_id (fun a b => x (Fin.castLE hjn a) (Fin.castLE hjr b) - idem k r n j (Fin.castLE hjn a) (Fin.castLE hjr b)) (fun a b => (hL _ b).trans_lt hc) v γ ?_ a` and prove the remaining obligations. Introduce `a`. Establish `e1 : ∀ b, (x (Fin.castLE hjn a) (Fin.castLE hjr b) - idem k r n j (Fin.castLE hjn a) (Fin.castLE hjr b)) * v b = v b * x (Fin.castLE hjn a) (Fin.castLE hjr b) - (if a = b then v b else 0)`.

Apply the tactic sequence `intro b; rw [idem_JJ hjn hjr]; split_ifs <;> ring`. Rewrite using `[Finset.sum_congr rfl (fun b _ => e1 b), Finset.sum_sub_distrib, Finset.sum_ite_eq]`. Simplify using `using h (Fin.castLE hjn a)`. Introduce `h i`. Apply `Valuation.map_sum_le` to reduce the goal to its premises.

Introduce `a _`. Rewrite using `[Valuation.map_mul]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem colC (hjn : j ≤ n) (hjr : j ≤ r) {c : kˣ} (hc : valuation k (c : k) < 1)
    {x : Matrix (Fin n) (Fin r) k} (hL : Lc hjr c x) (v : Fin j → k) (γ : ValueGroupWithZero k) :
    (∀ i, valuation k (∑ a, v a * x i (Fin.castLE hjr a)) ≤ γ) ↔ ∀ a, valuation k (v a) ≤ γ := by
  constructor
  · intro h a
    refine near_id (fun a b => x (Fin.castLE hjn a) (Fin.castLE hjr b) -
      idem k r n j (Fin.castLE hjn a) (Fin.castLE hjr b)) (fun a b => (hL _ b).trans_lt hc) v γ ?_ a
    intro a
    have e1 : ∀ b, (x (Fin.castLE hjn a) (Fin.castLE hjr b) - idem k r n j (Fin.castLE hjn a) (Fin.castLE hjr b)) * v b
        = v b * x (Fin.castLE hjn a) (Fin.castLE hjr b) - (if a = b then v b else 0) := by
      intro b; rw [idem_JJ hjn hjr]; split_ifs <;> ring
    rw [Finset.sum_congr rfl (fun b _ => e1 b), Finset.sum_sub_distrib, Finset.sum_ite_eq]
    simpa using h (Fin.castLE hjn a)
  · intro h i
    apply Valuation.map_sum_le
    intro a _
    rw [Valuation.map_mul]
    calc valuation k (v a) * valuation k (x i (Fin.castLE hjr a)) ≤ γ * 1 :=
          mul_le_mul' (h a) (val_le_one_of_Lc hjr hc hL i a)
      _ = γ := mul_one _

/- English proof (translation)
Set `v : Fin j → (Fin n → k)` to `fun a i => x i (Fin.castLE hjr a)`. Establish `hli : LinearIndependent k v`. Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `g hg a`. Establish `h0 : ∀ i, valuation k (∑ b, g b * x i (Fin.castLE hjr b)) ≤ 0`.

Introduce `i`. Use `congrFun hg i` as an intermediate fact. Simplify using `only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, v] at this`. Rewrite using `[this, Valuation.map_zero]`. Use `(colC hjn hjr hc hL g 0).1 h0 a` as an intermediate fact.

Conclude with `(valuation k).zero_iff.1 (le_antisymm this zero_le')`. Establish `hsub : Submodule.span k (Set.range v) ≤ LinearMap.range x.mulVecLin`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨a, rfl⟩`. Use `⟨Pi.single (Fin.castLE hjr a) 1, ?_⟩` and prove the remaining obligations.

Use function extensionality and compare the values at `i`. Simplify using `[Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Pi.single_apply, v]`. Establish `heq : Submodule.span k (Set.range v) = LinearMap.range x.mulVecLin`. Apply `Submodule.eq_of_le_of_finrank_le hsub` to reduce the goal to its premises. Rewrite using `[finrank_span_eq_card hli, Fintype.card_fin]`.

Conclude with `hrk`. Establish `hmem : ∀ l : Fin r, (fun i => x i l) ∈ Submodule.span k (Set.range v)`. Introduce `l`. Rewrite using `[heq]`. Use `⟨Pi.single l 1, ?_⟩` and prove the remaining obligations.

Use function extensionality and compare the values at `i`. Simplify using `[Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Pi.single_apply]`. Use `choose T hT using fun l => (Submodule.mem_span_range_iff_exists_fun k).1 (hmem l)`. Use `⟨fun a l => T l a, fun i l => ?_⟩` and prove the remaining obligations. Use `congrFun (hT l) i` as an intermediate fact.

Simplify using `only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, v] at this`. Conclude with `this.symm`.
-/
theorem exists_strictHenselian_absolutely_closed_local_ring (hjn : j ≤ n) (hjr : j ≤ r) {c : kˣ} (hc : valuation k (c : k) < 1)
    {x : Matrix (Fin n) (Fin r) k} (hL : Lc hjr c x) (hrk : x.rank ≤ j) :
    ∃ T : Fin j → Fin r → k, ∀ i l, x i l = ∑ a, T a l * x i (Fin.castLE hjr a) := by
  let v : Fin j → (Fin n → k) := fun a i => x i (Fin.castLE hjr a)
  have hli : LinearIndependent k v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg a
    have h0 : ∀ i, valuation k (∑ b, g b * x i (Fin.castLE hjr b)) ≤ 0 := by
      intro i
      have := congrFun hg i
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, v] at this
      rw [this, Valuation.map_zero]
    have := (colC hjn hjr hc hL g 0).1 h0 a
    exact (valuation k).zero_iff.1 (le_antisymm this zero_le')
  have hsub : Submodule.span k (Set.range v) ≤ LinearMap.range x.mulVecLin := by
    rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    refine ⟨Pi.single (Fin.castLE hjr a) 1, ?_⟩
    funext i
    simp [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Pi.single_apply, v]
  have heq : Submodule.span k (Set.range v) = LinearMap.range x.mulVecLin := by
    apply Submodule.eq_of_le_of_finrank_le hsub
    rw [finrank_span_eq_card hli, Fintype.card_fin]
    exact hrk
  have hmem : ∀ l : Fin r, (fun i => x i l) ∈ Submodule.span k (Set.range v) := by
    intro l
    rw [heq]
    refine ⟨Pi.single l 1, ?_⟩
    funext i
    simp [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Pi.single_apply]
  choose T hT using fun l => (Submodule.mem_span_range_iff_exists_fun k).1 (hmem l)
  refine ⟨fun a l => T l a, fun i l => ?_⟩
  have := congrFun (hT l) i
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, v] at this
  exact this.symm

/- English proof (translation)
Simplify using `only [ballM, Set.mem_setOf_eq]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `⟨fun i a => h i _, fun i l hl => ?_⟩` and prove the remaining obligations. Use `h i l` as an intermediate fact.

Rewrite `this` using `[idem_right i l hl, sub_zero]`. Then use the resulting hypothesis. Introduce and unpack `⟨h1, h2⟩ i l`. Distinguish the cases in `hl : l.val < j`. Use `h1 i ⟨l.val, hl⟩` as an intermediate fact. Establish `e : Fin.castLE hjr ⟨l.val, hl⟩ = l` using `Fin.ext rfl`.

Rewrite `this` using `[e]`. Then use the resulting hypothesis. Rewrite using `[idem_right i l (not_lt.1 hl), sub_zero]`. Conclude with `h2 i l (not_lt.1 hl)`.
-/
theorem mem_ball_iff (hjr : j ≤ r) (c : kˣ) (x : Matrix (Fin n) (Fin r) k) :
    x ∈ ballM c (idem k r n j) ↔
      Lc hjr c x ∧ ∀ i (l : Fin r), j ≤ l.val → valuation k (x i l) ≤ valuation k (c : k) := by
  simp only [ballM, Set.mem_setOf_eq]
  constructor
  · intro h
    refine ⟨fun i a => h i _, fun i l hl => ?_⟩
    have := h i l
    rwa [idem_right i l hl, sub_zero] at this
  · rintro ⟨h1, h2⟩ i l
    by_cases hl : l.val < j
    · have := h1 i ⟨l.val, hl⟩
      have e : Fin.castLE hjr ⟨l.val, hl⟩ = l := Fin.ext rfl
      rwa [e] at this
    · rw [idem_right i l (not_lt.1 hl), sub_zero]; exact h2 i l (not_lt.1 hl)

/- English proof (translation)
Establish `hm` using `Finset.sum_map Finset.univ ⟨Fin.castLE hjr, Fin.castLE_injective hjr⟩ f`. Simplify using `only [Function.Embedding.coeFn_mk] at hm`. Rewrite using `[← hm]`. Use `symm`. Apply `Finset.sum_subset (Finset.subset_univ _)` to reduce the goal to its premises.

Introduce `l _ hl`. Apply `hf` to reduce the goal to its premises. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `hl (Finset.mem_map.2 ⟨⟨l.val, h⟩, Finset.mem_univ _, Fin.ext rfl⟩)`.
-/
theorem sumJ (hjr : j ≤ r) (f : Fin r → k) (hf : ∀ l : Fin r, j ≤ l.val → f l = 0) :
    ∑ l, f l = ∑ a : Fin j, f (Fin.castLE hjr a) := by
  have hm := Finset.sum_map Finset.univ ⟨Fin.castLE hjr, Fin.castLE_injective hjr⟩ f
  simp only [Function.Embedding.coeFn_mk] at hm
  rw [← hm]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro l _ hl
  apply hf
  by_contra h
  push_neg at h
  exact hl (Finset.mem_map.2 ⟨⟨l.val, h⟩, Finset.mem_univ _, Fin.ext rfl⟩)

def Mr (j : ℕ) (w c : k) (L : 𝓀[k] → 𝒪[k]) (ρ : Fin j → {l : Fin r // j ≤ l.val} → 𝓀[k]) :
    Matrix (Fin r) (Fin r) k :=
  Matrix.of fun l l' => if h' : l'.val < j then (if l = l' then 1 else 0)
    else w * ((if h : l.val < j then c * (L (ρ ⟨l.val, h⟩ ⟨l', not_lt.1 h'⟩) : k) else 0) +
      if l = l' then 1 else 0)

/- English proof (translation)
Establish `hup : (Mr j w c L ρ).BlockTriangular id`. Introduce `l l' hll`. Establish `hne : l ≠ l'` using `fun h => lt_irrefl _ (h ▸ hll)`. Establish `hv : l'.val < l.val` using `hll`. Simplify using `only [Mr, Matrix.of_apply, if_neg hne, add_zero]`.

Use `split_ifs with h1 h2`. Both sides reduce to the same expression. Use linear arithmetic over natural numbers and integers. Simplify using the standard rewrite rules. Rewrite using `[Matrix.det_of_upperTriangular hup]`.

Establish `hd : ∀ l : Fin r, Mr j w c L ρ l l = if l.val < j then 1 else w`. Introduce `l`. Simplify using `only [Mr, Matrix.of_apply, if_true]`. Apply the tactic sequence `split_ifs with h1 <;> simp_all`. Simplify using `only [hd]`.

Rewrite using `[Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const, Fintype.card_subtype]`. Use `congr 2`. Use extensionality with `l`. Simplify using `[not_lt]`.
-/
theorem Mr_det (j : ℕ) (w c : k) (L : 𝓀[k] → 𝒪[k]) (ρ : Fin j → {l : Fin r // j ≤ l.val} → 𝓀[k]) :
    (Mr j w c L ρ).det = w ^ Fintype.card {l : Fin r // j ≤ l.val} := by
  have hup : (Mr j w c L ρ).BlockTriangular id := by
    intro l l' hll
    have hne : l ≠ l' := fun h => lt_irrefl _ (h ▸ hll)
    have hv : l'.val < l.val := hll
    simp only [Mr, Matrix.of_apply, if_neg hne, add_zero]
    split_ifs with h1 h2
    · rfl
    · omega
    · simp
  rw [Matrix.det_of_upperTriangular hup]
  have hd : ∀ l : Fin r, Mr j w c L ρ l l = if l.val < j then 1 else w := by
    intro l
    simp only [Mr, Matrix.of_apply, if_true]
    split_ifs with h1 <;> simp_all
  simp only [hd]
  rw [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const, Fintype.card_subtype]
  congr 2
  ext l
  simp [not_lt]

/- English proof (translation)
Rewrite using `[Matrix.mul_apply]`. Simplify using `[Mr, a.isLt]`.
-/
theorem mulMr_left (hjr : j ≤ r) (w c : k) (L : 𝓀[k] → 𝒪[k])
    (ρ : Fin j → {l : Fin r // j ≤ l.val} → 𝓀[k]) (x : Matrix (Fin n) (Fin r) k) (i : Fin n) (a : Fin j) :
    (x * Mr j w c L ρ) i (Fin.castLE hjr a) = x i (Fin.castLE hjr a) := by
  rw [Matrix.mul_apply]
  simp [Mr, a.isLt]

/- English proof (translation)
Rewrite using `[Matrix.mul_apply]`. Establish `e : ∀ l0 : Fin r, x i l0 * Mr j w c L ρ l0 l = w * (x i l0 * (if h2 : l0.val < j then (c : k) * (L (ρ ⟨l0.val, h2⟩ ⟨l, hl⟩) : k) else 0)) + w * (x i l0 * if l0 = l then 1 else 0)`. Introduce `l0`. Simplify using `only [Mr, Matrix.of_apply, dif_neg (not_lt.2 hl)]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[Finset.sum_congr rfl (fun l0 _ => e l0), Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← mul_add]`. Use `congr 2`. Rewrite using `[sumJ hjr]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `a _`.

Simplify using `[a.isLt]`. Introduce `l0 hl0`. Simplify using `[not_lt.2 hl0]`. Simplify using the standard rewrite rules.
-/
theorem mulMr_right (hjr : j ≤ r) (w c : k) (L : 𝓀[k] → 𝒪[k])
    (ρ : Fin j → {l : Fin r // j ≤ l.val} → 𝓀[k]) (x : Matrix (Fin n) (Fin r) k) (i : Fin n) (l : Fin r)
    (hl : j ≤ l.val) :
    (x * Mr j w c L ρ) i l =
      w * (∑ a : Fin j, x i (Fin.castLE hjr a) * ((c : k) * (L (ρ a ⟨l, hl⟩) : k)) + x i l) := by
  rw [Matrix.mul_apply]
  have e : ∀ l0 : Fin r, x i l0 * Mr j w c L ρ l0 l =
      w * (x i l0 * (if h2 : l0.val < j then (c : k) * (L (ρ ⟨l0.val, h2⟩ ⟨l, hl⟩) : k) else 0)) +
        w * (x i l0 * if l0 = l then 1 else 0) := by
    intro l0
    simp only [Mr, Matrix.of_apply, dif_neg (not_lt.2 hl)]
    ring
  rw [Finset.sum_congr rfl (fun l0 _ => e l0), Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    ← mul_add]
  congr 2
  · rw [sumJ hjr]
    · apply Finset.sum_congr rfl
      intro a _
      simp [a.isLt]
    · intro l0 hl0
      simp [not_lt.2 hl0]
  · simp

end Mat

/- English proof (translation)
Take `⟨p, hp⟩` from `IsDiscreteValuationRing.exists_irreducible 𝒪[k]`. Establish `hp0 : (p : k) ≠ 0` using `fun h => hp.ne_zero (Subtype.ext h)`. Use `⟨Units.mk0 (p : k) hp0, ?_, ?_, nabs_uniformiser hp rfl⟩` and prove the remaining obligations. Conclude with `Valuation.Integer.not_isUnit_iff_valuation_lt_one.1 hp.not_isUnit`. Introduce `y`.

Rewrite using `[IsLocalRing.residue_eq_zero_iff, hp.maximalIdeal_eq, Ideal.mem_span_singleton]`. Conclude with `Valuation.Integers.le_iff_dvd (Valuation.integer.integers (valuation k)) (x := y) (y := p)`.
-/
theorem exists_unif : ∃ ϖ : kˣ, valuation k (ϖ : k) < 1 ∧
    (∀ y : 𝒪[k], valuation k (y : k) ≤ valuation k (ϖ : k) ↔ IsLocalRing.residue 𝒪[k] y = 0) ∧
    nabs k ϖ = (resCard k : ℝ)⁻¹ := by
  obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[k]
  have hp0 : (p : k) ≠ 0 := fun h => hp.ne_zero (Subtype.ext h)
  refine ⟨Units.mk0 (p : k) hp0, ?_, ?_, nabs_uniformiser hp rfl⟩
  · exact Valuation.Integer.not_isUnit_iff_valuation_lt_one.1 hp.not_isUnit
  · intro y
    rw [IsLocalRing.residue_eq_zero_iff, hp.maximalIdeal_eq, Ideal.mem_span_singleton]
    exact Valuation.Integers.le_iff_dvd (Valuation.integer.integers (valuation k)) (x := y) (y := p)

/- English proof (translation)
Establish `e : t = ((c : k) * y + t) - (c : k) * y` using `by ring`. Rewrite using `[e]`. Apply `Valuation.map_sub_le` to reduce the goal to its premises. Conclude with `h.trans (mul_le_of_le_one_right' hϖ.le)`. Rewrite using `[Valuation.map_mul]`.

Conclude with `mul_le_of_le_one_right' ((Valuation.mem_integer_iff _ _).1 y.2)`.
-/
theorem entry1 {c ϖ : kˣ} (hϖ : valuation k (ϖ : k) < 1) (t : k) (y : 𝒪[k])
    (h : valuation k ((c : k) * y + t) ≤ valuation k (c : k) * valuation k (ϖ : k)) :
    valuation k t ≤ valuation k (c : k) := by
  have e : t = ((c : k) * y + t) - (c : k) * y := by ring
  rw [e]
  apply Valuation.map_sub_le
  · exact h.trans (mul_le_of_le_one_right' hϖ.le)
  · rw [Valuation.map_mul]; exact mul_le_of_le_one_right' ((Valuation.mem_integer_iff _ _).1 y.2)

/- English proof (translation)
Rewrite using `[← mul_add, Valuation.map_mul, vmul_le_iff (by simp), show (y : k) + τ = ((y + τ : 𝒪[k]) : k) from rfl, hU, map_add, hy, eq_neg_iff_add_eq_zero]`.
-/
theorem entry2 {c ϖ : kˣ}
    (hU : ∀ y : 𝒪[k], valuation k (y : k) ≤ valuation k (ϖ : k) ↔ IsLocalRing.residue 𝒪[k] y = 0)
    (y τ : 𝒪[k]) (ρ0 : 𝓀[k]) (hy : IsLocalRing.residue 𝒪[k] y = ρ0) :
    valuation k ((c : k) * y + (c : k) * τ) ≤ valuation k (c : k) * valuation k (ϖ : k) ↔
      ρ0 = -IsLocalRing.residue 𝒪[k] τ := by
  rw [← mul_add, Valuation.map_mul, vmul_le_iff (by simp),
    show (y : k) + τ = ((y + τ : 𝒪[k]) : k) from rfl, hU, map_add, hy, eq_neg_iff_add_eq_zero]

/- English proof (translation)
Distinguish the cases in `hT : ∀ a (l : Fin r), j ≤ l.val → valuation k (T a l) ≤ valuation k (c : k)`. Rewrite using `[if_pos hT]`. Establish `hc0 : valuation k (c : k) ≠ 0` using `by simp`. Set `τ : Fin j → {l : Fin r // j ≤ l.val} → 𝒪[k]` to `fun a l => ⟨T a l / c, by`. Rewrite using `[Valuation.mem_integer_iff, map_div₀, div_le_iff₀ (zero_lt_iff.2 hc0), one_mul]`.

Conclude with `hT a l l.2⟩`. Establish `hTe : ∀ a (l : {l : Fin r // j ≤ l.val}), T a l = (c : k) * τ a l`. Introduce `a l`. Use `show T a l = (c : k) * (T a l / c)`. Rewrite using `[mul_div_cancel₀ _ (Units.ne_zero c)]`.

Establish `key : ∀ ρ : Fin j → {l : Fin r // j ≤ l.val} → 𝓀[k], (∀ a (l : {l : Fin r // j ≤ l.val}), valuation k ((c : k) * L (ρ a l) + T a l) ≤ valuation k (c : k) * valuation k (ϖ : k)) ↔ ρ = fun a l => -IsLocalRing.residue 𝒪[k] (τ a l)`. Introduce `ρ`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Use function extensionality and compare the values at `a l`.

Conclude with `(entry2 hU (L (ρ a l)) (τ a l) (ρ a l) (hL _)).1 (by rw [← hTe]; exact h a l)`. Introduce and unpack `rfl a l`. Rewrite using `[hTe]`. Conclude with `(entry2 hU _ _ _ (hL _)).2 rfl`. Rewrite using `[Finset.sum_congr rfl (fun ρ _ => if_congr (key ρ) rfl rfl)]`.

Simplify using the standard rewrite rules. Rewrite using `[if_neg hT]`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `ρ _`. Rewrite using `[if_neg]`.

Introduce `h`. Apply `hT` to reduce the goal to its premises. Introduce `a l hl`. Conclude with `entry1 hϖ (T a l) (L (ρ a ⟨l, hl⟩)) (h a ⟨l, hl⟩)`.
-/
theorem count [Fintype 𝓀[k]] [DecidableEq 𝓀[k]] {j r : ℕ} {c ϖ : kˣ} (hϖ : valuation k (ϖ : k) < 1)
    (hU : ∀ y : 𝒪[k], valuation k (y : k) ≤ valuation k (ϖ : k) ↔ IsLocalRing.residue 𝒪[k] y = 0)
    (L : 𝓀[k] → 𝒪[k]) (hL : ∀ z, IsLocalRing.residue 𝒪[k] (L z) = z) (T : Fin j → Fin r → k) :
    (∑ ρ : Fin j → {l : Fin r // j ≤ l.val} → 𝓀[k],
      if (∀ a (l : {l : Fin r // j ≤ l.val}),
        valuation k ((c : k) * L (ρ a l) + T a l) ≤ valuation k (c : k) * valuation k (ϖ : k)) then (1 : ℂ)
      else 0) =
    if (∀ a (l : Fin r), j ≤ l.val → valuation k (T a l) ≤ valuation k (c : k)) then 1 else 0 := by
  classical
  by_cases hT : ∀ a (l : Fin r), j ≤ l.val → valuation k (T a l) ≤ valuation k (c : k)
  · rw [if_pos hT]
    have hc0 : valuation k (c : k) ≠ 0 := by simp
    let τ : Fin j → {l : Fin r // j ≤ l.val} → 𝒪[k] := fun a l => ⟨T a l / c, by
      rw [Valuation.mem_integer_iff, map_div₀, div_le_iff₀ (zero_lt_iff.2 hc0), one_mul]
      exact hT a l l.2⟩
    have hTe : ∀ a (l : {l : Fin r // j ≤ l.val}), T a l = (c : k) * τ a l := by
      intro a l
      show T a l = (c : k) * (T a l / c)
      rw [mul_div_cancel₀ _ (Units.ne_zero c)]
    have key : ∀ ρ : Fin j → {l : Fin r // j ≤ l.val} → 𝓀[k],
        (∀ a (l : {l : Fin r // j ≤ l.val}),
          valuation k ((c : k) * L (ρ a l) + T a l) ≤ valuation k (c : k) * valuation k (ϖ : k)) ↔
        ρ = fun a l => -IsLocalRing.residue 𝒪[k] (τ a l) := by
      intro ρ
      constructor
      · intro h
        funext a l
        exact (entry2 hU (L (ρ a l)) (τ a l) (ρ a l) (hL _)).1 (by rw [← hTe]; exact h a l)
      · rintro rfl a l
        rw [hTe]
        exact (entry2 hU _ _ _ (hL _)).2 rfl
    rw [Finset.sum_congr rfl (fun ρ _ => if_congr (key ρ) rfl rfl)]
    simp
  · rw [if_neg hT]
    apply Finset.sum_eq_zero
    intro ρ _
    rw [if_neg]
    intro h
    apply hT
    intro a l hl
    exact entry1 hϖ (T a l) (L (ρ a ⟨l, hl⟩)) (h a ⟨l, hl⟩)

/- English proof (translation)
Establish `hLeq : ∀ ρ, Lc hjr c (x * Mr j ((ϖ : k)⁻¹) c L ρ) ↔ Lc hjr c x`. Introduce `ρ`. Use `forall_congr' fun i => forall_congr' fun a => ?_` and prove the remaining obligations. Establish `e` using `mulMr_left hjr ((ϖ : k)⁻¹) (c : k) L ρ x i a`. Apply the tactic sequence `first | rw [e] | erw [e] | (simp only [Matrix.mul_apply] at e ⊢; rw [e])`.

Simplify using `only [Set.indicator_apply, mem_ball_iff hjr, hLeq]`. Distinguish the cases in `hx : Lc hjr c x`. Take `⟨T, hT⟩` from `exists_strictHenselian_absolutely_closed_local_ring hjn hjr hc hx hrk`. Establish `h1 : (∀ i (l : Fin r), j ≤ l.val → valuation k (x i l) ≤ valuation k (c : k)) ↔ ∀ a (l : Fin r), j ≤ l.val → valuation k (T a l) ≤ valuation k (c : k)`. Prove the components needed by the constructor for the conclusion.

Introduce `h a l hl`. Conclude with `(colC hjn hjr hc hx (fun a => T a l) _).1 (fun i => by rw [← hT]; exact h i l hl) a`. Introduce `h i l hl`. Rewrite using `[hT]`. Conclude with `(colC hjn hjr hc hx (fun a => T a l) _).2 (fun a => h a l hl) i`.

Establish `ev : ∀ y : k, valuation k ((ϖ : k)⁻¹ * y) ≤ valuation k (c : k) ↔ valuation k y ≤ valuation k (c : k) * valuation k (ϖ : k)`. Introduce `y`. Rewrite using `[Valuation.map_mul, map_inv₀, inv_mul_eq_div, div_le_iff₀ (zero_lt_iff.2 (by simp))]`. Establish `h2 : ∀ ρ : Fin j → {l : Fin r // j ≤ l.val} → 𝓀[k], (∀ i (l : Fin r), j ≤ l.val → valuation k ((x * Mr j ((ϖ : k)⁻¹) c L ρ) i l) ≤ valuation k (c : k)) ↔ ∀ a (l : {l : Fin r // j ≤ l.val}), valuation k ((c : k) * L (ρ a l) + T a l) ≤ valuation k (c : k) * valuation k (ϖ : k)`. Introduce `ρ`.

Establish `e : ∀ i (l : Fin r) (hl : j ≤ l.val), (x * Mr j ((ϖ : k)⁻¹) c L ρ) i l = (ϖ : k)⁻¹ * ∑ a, ((c : k) * L (ρ a ⟨l, hl⟩) + T a l) * x i (Fin.castLE hjr a)`. Introduce `i l hl`. Rewrite using `[mulMr_right hjr _ _ _ _ _ _ _ hl, hT i l, ← Finset.sum_add_distrib]`. Use `congr 1`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises.

Introduce `a _`. Expand and normalize the polynomial expressions, which then agree. Prove the components needed by the constructor for the conclusion. Introduce `h a l`. Conclude with `(colC hjn hjr hc hx (fun a => (c : k) * L (ρ a l) + T a l) _).1 (fun i => by rw [← ev, ← e i l l.2]; exact h i l l.2) a`.

Introduce `h i l hl`. Rewrite using `[e i l hl, ev]`. Conclude with `(colC hjn hjr hc hx (fun a => (c : k) * L (ρ a ⟨l, hl⟩) + T a l) _).2 (fun a => h a ⟨l, hl⟩) i`. Simplify using `only [hx, true_and, h1, h2]`. Use `(count (c := c) hϖ hU L hL T).symm.trans (Finset.sum_congr rfl fun ρ _ => ?_)` and prove the remaining obligations.

Establish `hx'` using `(hLeq ρ).2 hx`. Use `split_ifs with hp hq hq`. Both sides reduce to the same expression. Conclude with `absurd ⟨hx', hp⟩ hq`. Conclude with `absurd hq.2 hp`.

Both sides reduce to the same expression. Rewrite using `[if_neg (fun h => hx h.1)]`. Use `symm`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `ρ _`.

Rewrite using `[if_neg]`. Introduce `h`. Conclude with `hx ((hLeq ρ).1 h.1)`.
-/
theorem ind_eq [Fintype 𝓀[k]] [DecidableEq 𝓀[k]] {n r j : ℕ} (hjn : j ≤ n) (hjr : j ≤ r) {c ϖ : kˣ}
    (hc : valuation k (c : k) < 1) (hϖ : valuation k (ϖ : k) < 1)
    (hU : ∀ y : 𝒪[k], valuation k (y : k) ≤ valuation k (ϖ : k) ↔ IsLocalRing.residue 𝒪[k] y = 0)
    (L : 𝓀[k] → 𝒪[k]) (hL : ∀ z, IsLocalRing.residue 𝒪[k] (L z) = z)
    (x : Matrix (Fin n) (Fin r) k) (hrk : x.rank ≤ j) :
    (ballM c (idem k r n j)).indicator (fun _ => (1 : ℂ)) x =
      ∑ ρ : Fin j → {l : Fin r // j ≤ l.val} → 𝓀[k],
        (ballM c (idem k r n j)).indicator (fun _ => (1 : ℂ)) (x * Mr j ((ϖ : k)⁻¹) c L ρ) := by
  classical
  have hLeq : ∀ ρ, Lc hjr c (x * Mr j ((ϖ : k)⁻¹) c L ρ) ↔ Lc hjr c x := by
    intro ρ
    refine forall_congr' fun i => forall_congr' fun a => ?_
    have e := mulMr_left hjr ((ϖ : k)⁻¹) (c : k) L ρ x i a
    first | rw [e] | erw [e] | (simp only [Matrix.mul_apply] at e ⊢; rw [e])
  simp only [Set.indicator_apply, mem_ball_iff hjr, hLeq]
  by_cases hx : Lc hjr c x
  · obtain ⟨T, hT⟩ := exists_strictHenselian_absolutely_closed_local_ring hjn hjr hc hx hrk
    have h1 : (∀ i (l : Fin r), j ≤ l.val → valuation k (x i l) ≤ valuation k (c : k)) ↔
        ∀ a (l : Fin r), j ≤ l.val → valuation k (T a l) ≤ valuation k (c : k) := by
      constructor
      · intro h a l hl
        exact (colC hjn hjr hc hx (fun a => T a l) _).1 (fun i => by rw [← hT]; exact h i l hl) a
      · intro h i l hl
        rw [hT]; exact (colC hjn hjr hc hx (fun a => T a l) _).2 (fun a => h a l hl) i
    have ev : ∀ y : k, valuation k ((ϖ : k)⁻¹ * y) ≤ valuation k (c : k) ↔
        valuation k y ≤ valuation k (c : k) * valuation k (ϖ : k) := by
      intro y
      rw [Valuation.map_mul, map_inv₀, inv_mul_eq_div, div_le_iff₀ (zero_lt_iff.2 (by simp))]
    have h2 : ∀ ρ : Fin j → {l : Fin r // j ≤ l.val} → 𝓀[k],
        (∀ i (l : Fin r), j ≤ l.val → valuation k ((x * Mr j ((ϖ : k)⁻¹) c L ρ) i l) ≤ valuation k (c : k)) ↔
        ∀ a (l : {l : Fin r // j ≤ l.val}),
          valuation k ((c : k) * L (ρ a l) + T a l) ≤ valuation k (c : k) * valuation k (ϖ : k) := by
      intro ρ
      have e : ∀ i (l : Fin r) (hl : j ≤ l.val), (x * Mr j ((ϖ : k)⁻¹) c L ρ) i l =
          (ϖ : k)⁻¹ * ∑ a, ((c : k) * L (ρ a ⟨l, hl⟩) + T a l) * x i (Fin.castLE hjr a) := by
        intro i l hl
        rw [mulMr_right hjr _ _ _ _ _ _ _ hl, hT i l, ← Finset.sum_add_distrib]
        congr 1
        apply Finset.sum_congr rfl
        intro a _
        ring
      constructor
      · intro h a l
        exact (colC hjn hjr hc hx (fun a => (c : k) * L (ρ a l) + T a l) _).1
          (fun i => by rw [← ev, ← e i l l.2]; exact h i l l.2) a
      · intro h i l hl
        rw [e i l hl, ev]
        exact (colC hjn hjr hc hx (fun a => (c : k) * L (ρ a ⟨l, hl⟩) + T a l) _).2 (fun a => h a ⟨l, hl⟩) i
    simp only [hx, true_and, h1, h2]
    refine (count (c := c) hϖ hU L hL T).symm.trans (Finset.sum_congr rfl fun ρ _ => ?_)
    have hx' := (hLeq ρ).2 hx
    split_ifs with hp hq hq
    · rfl
    · exact absurd ⟨hx', hp⟩ hq
    · exact absurd hq.2 hp
    · rfl
  · rw [if_neg (fun h => hx h.1)]
    symm
    apply Finset.sum_eq_zero
    intro ρ _
    rw [if_neg]
    intro h
    exact hx ((hLeq ρ).1 h.1)

/- English proof (translation)
Take `⟨Bf, hsym, hpos, hinv⟩` from `hσ`. Assume the negation of the conclusion as `hv0`. Establish `hR : 0 < (Bf v v).re` using `hpos v hv0`. Establish `hs0 : 0 < ‖s‖` using `lt_of_le_of_lt (Nat.cast_nonneg _) hs`. Establish `hterm : ∀ i, ‖Bf (σ (g i) v) v‖ ≤ (Bf v v).re`.

Introduce `i`. Establish `h` using `GlobalTheory.T.hermitian_norm_sq_le_re_mul_re_of_posDef V Bf hsym hpos (σ (g i) v) v`. Rewrite `h` using `[hinv]`. Establish `h' : ‖Bf (σ (g i) v) v‖ ^ 2 ≤ (Bf v v).re ^ 2` using `by rw [sq ((Bf v v).re)]; exact h`. Conclude with `(pow_le_pow_iff_left₀ (norm_nonneg _) hR.le two_ne_zero).1 h'`.

Establish `hexp : Bf v v = ∑ i, s⁻¹ * Bf (σ (g i) v) v`. Establish `: Bf v v = Bf (∑ i, s⁻¹ • σ (g i) v) v` using `by rw [← hv]`. Rewrite using `[this, map_sum, LinearMap.sum_apply]`. Simplify using `only [map_smul, LinearMap.smul_apply, smul_eq_mul]`. Establish `hle : (Bf v v).re ≤ (Fintype.card ι : ℝ) * ‖s‖⁻¹ * (Bf v v).re`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[norm_mul, norm_inv]`. Conclude with `mul_le_mul_of_nonneg_left (hterm i) (inv_nonneg.2 (norm_nonneg _))`. Use `_ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring`. Establish `hlt : (Fintype.card ι : ℝ) * ‖s‖⁻¹ < 1`.

Rewrite using `[← div_eq_mul_inv, div_lt_one hs0]`. Conclude with `hs`. Use `mul_lt_mul_of_pos_right hlt hR` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem avg_zero {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ G V) (hσ : IsUnitarisable σ) {ι : Type} [Fintype ι] (g : ι → G) (s : ℂ)
    (hs : (Fintype.card ι : ℝ) < ‖s‖) (v : V) (hv : v = ∑ i, s⁻¹ • σ (g i) v) : v = 0 := by
  obtain ⟨Bf, hsym, hpos, hinv⟩ := hσ
  by_contra hv0
  have hR : 0 < (Bf v v).re := hpos v hv0
  have hs0 : 0 < ‖s‖ := lt_of_le_of_lt (Nat.cast_nonneg _) hs
  have hterm : ∀ i, ‖Bf (σ (g i) v) v‖ ≤ (Bf v v).re := by
    intro i
    have h := GlobalTheory.T.hermitian_norm_sq_le_re_mul_re_of_posDef V Bf hsym hpos (σ (g i) v) v
    rw [hinv] at h
    have h' : ‖Bf (σ (g i) v) v‖ ^ 2 ≤ (Bf v v).re ^ 2 := by rw [sq ((Bf v v).re)]; exact h
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) hR.le two_ne_zero).1 h'
  have hexp : Bf v v = ∑ i, s⁻¹ * Bf (σ (g i) v) v := by
    have : Bf v v = Bf (∑ i, s⁻¹ • σ (g i) v) v := by rw [← hv]
    rw [this, map_sum, LinearMap.sum_apply]
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  have hle : (Bf v v).re ≤ (Fintype.card ι : ℝ) * ‖s‖⁻¹ * (Bf v v).re :=
    calc (Bf v v).re ≤ ‖Bf v v‖ := by first | exact Complex.re_le_norm _ | exact Complex.re_le_abs _
      _ = ‖∑ i, s⁻¹ * Bf (σ (g i) v) v‖ := by rw [← hexp]
      _ ≤ ∑ i, ‖s⁻¹ * Bf (σ (g i) v) v‖ := norm_sum_le _ _
      _ ≤ ∑ _i : ι, ‖s‖⁻¹ * (Bf v v).re := Finset.sum_le_sum fun i _ => by
          rw [norm_mul, norm_inv]; exact mul_le_mul_of_nonneg_left (hterm i) (inv_nonneg.2 (norm_nonneg _))
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
  have hlt : (Fintype.card ι : ℝ) * ‖s‖⁻¹ < 1 := by
    rw [← div_eq_mul_inv, div_lt_one hs0]; exact hs
  have := mul_lt_mul_of_pos_right hlt hR
  linarith

end PositivityTheory.Rg.Ming.CoreX

namespace PositivityTheory.Rg.Ming

/- English proof (translation)
Introduce `_ _ k _ _ _ _ n r μ V _ _ W _ _ σ π B j hjr hjn2 hμ hσ hE hvan c hc Φ hΦ`. Use `letI : Fintype 𝓀[k] := Fintype.ofFinite _`. Establish `hjn : j ≤ n` using `by omega`. Establish `hjr' : j ≤ r` using `hjr.le`. Take `⟨ϖ, hϖ1, hU, hnabs⟩` from `PositivityTheory.Rg.Ming.CoreX.exists_unif (k := k)`.

Set `L : 𝓀[k] → 𝒪[k]` to `Function.surjInv IsLocalRing.residue_surjective`. Establish `hL : ∀ z, IsLocalRing.residue 𝒪[k] (L z) = z` using `Function.surjInv_eq _`. Establish `hA : 1 ≤ Fintype.card {l : Fin r // j ≤ l.val}` using `Fintype.card_pos_iff.2 ⟨⟨⟨j, hjr⟩, le_rfl⟩⟩`. Establish `hw : ((ϖ : k))⁻¹ ≠ 0` using `by simp`. Establish `hdet : ∀ ρ : Fin j → {l : Fin r // j ≤ l.val} → 𝓀[k], (PositivityTheory.Rg.Ming.CoreX.Mr j (ϖ : k)⁻¹ (c : k) L ρ).det ≠ 0`.

Introduce `ρ`. Rewrite using `[PositivityTheory.Rg.Ming.CoreX.Mr_det]`. Conclude with `pow_ne_zero _ hw`. Set `g : (Fin j → {l : Fin r // j ≤ l.val} → 𝓀[k]) → GL (Fin r) k` to `fun ρ => Matrix.GeneralLinearGroup.mkOfDetNeZero _ (hdet ρ)`. Establish `hgv : ∀ ρ, ((g ρ : GL (Fin r) k) : Matrix (Fin r) (Fin r) k) = PositivityTheory.Rg.Ming.CoreX.Mr j (ϖ : k)⁻¹ (c : k) L ρ` using `fun ρ => rfl`.

Set `D : kˣ` to `ϖ⁻¹ ^ Fintype.card {l : Fin r // j ≤ l.val}`. Establish `hgD : ∀ ρ, Matrix.GeneralLinearGroup.det (g ρ) = D`. Introduce `ρ`. Use `ext`. Rewrite using `[Matrix.GeneralLinearGroup.val_det_apply, hgv, PositivityTheory.Rg.Ming.CoreX.Mr_det]`.

Simplify using `[D]`. Set `s : ℂ` to `(μ D : ℂ) * ((nabs k D ^ ((n : ℝ) / 2) : ℝ) : ℂ)`. Establish `hnD : nabs k D = (resCard k : ℝ) ^ Fintype.card {l : Fin r // j ≤ l.val}`. Establish `e1 : nabs k D = (nabs k ϖ)⁻¹ ^ Fintype.card {l : Fin r // j ≤ l.val}` using `by simp [D, nabs]`. Rewrite using `[e1, hnabs, inv_inv]`.

Establish `hqr : (resCard k : ℝ) = Fintype.card 𝓀[k]` using `by rw [resCard, Nat.card_eq_fintype_card]`. Establish `hq1 : 1 < Fintype.card 𝓀[k]` using `Fintype.one_lt_card`. Establish `hns : ‖s‖ = ((Fintype.card 𝓀[k] : ℝ) ^ Fintype.card {l : Fin r // j ≤ l.val}) ^ ((n : ℝ) / 2)`. Simplify using `only [s, norm_mul, hμ D, one_mul]`. Rewrite using `[hnD, hqr, Complex.norm_of_nonneg (by positivity)]`.

Establish `hs0 : s ≠ 0`. Introduce `h`. Establish `: ‖s‖ = 0` using `by rw [h, norm_zero]`. Rewrite `this` using `[hns]`. Establish `hpos : (0 : ℝ) < ((Fintype.card 𝓀[k] : ℝ) ^ Fintype.card {l : Fin r // j ≤ l.val}) ^ ((n : ℝ) / 2)`.

Check the signs of the components of the expression. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hcard : (Fintype.card (Fin j → {l : Fin r // j ≤ l.val} → 𝓀[k]) : ℝ) < ‖s‖`. Rewrite using `[hns, Fintype.card_fun, Fintype.card_fun, Fintype.card_fin]`. Use `push_cast`.

Establish `hQ : (1 : ℝ) < (Fintype.card 𝓀[k] : ℝ) ^ Fintype.card {l : Fin r // j ≤ l.val}` using `one_lt_pow₀ (by exact_mod_cast hq1) (by omega)`. Rewrite using `[← Real.rpow_natCast]`. Conclude with `Real.rpow_lt_rpow_of_exponent_lt hQ (by`. Rewrite using `[lt_div_iff₀ two_pos]; exact_mod_cast (by omega : j * 2 < n))`. Establish `hom : ∀ ρ (f : Matrix (Fin n) (Fin r) k → ℂ) x, om μ (g ρ) 1 f x = s * f (x * PositivityTheory.Rg.Ming.CoreX.Mr j (ϖ : k)⁻¹ (c : k) L ρ)`.

Introduce `ρ f x`. Simplify using `only [om, hgD, map_one, inv_one, Units.val_one, GlobalTheory.SplitWeil.Model.nabs_one, Real.one_rpow, Complex.ofReal_one, mul_one, Matrix.one_mul, Fintype.card_fin, hgv, s]`. Set `Φρ : (Fin j → {l : Fin r // j ≤ l.val} → 𝓀[k]) → SB (Matrix (Fin n) (Fin r) k)` to `fun ρ => ⟨om μ (g ρ) 1 Φ.1, GlobalTheory.SplitWeil.Model.om_mem_SB μ (g ρ) 1 Φ.2⟩`. Establish `hΨ : B (Φ - ∑ ρ, s⁻¹ • Φρ ρ) = 0`. Apply `hvan` to reduce the goal to its premises.

Introduce `x hx`. Simplify using `only [Submodule.coe_sub, Submodule.coe_sum, Submodule.coe_smul, Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Φρ, hom, inv_mul_cancel_left₀ hs0, hΦ]`. Rewrite using `[PositivityTheory.Rg.Ming.CoreX.ind_eq hjn hjr' hc hϖ1 hU L hL x (by omega)]`. Conclude with `sub_self _`. Establish `hBΦ : ∀ w, B Φ w = ∑ ρ, s⁻¹ • σ (g ρ) (B Φ w)`.

Introduce `w`. Establish `h1` using `congrArg (fun f => f w) hΨ`. Simplify using `only [map_sub, map_sum, map_smul, LinearMap.sub_apply, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.zero_apply] at h1`. Establish `h2 : ∀ ρ, B (Φρ ρ) w = σ (g ρ) (B Φ w)`. Introduce `ρ`.

Use `hE (g ρ) 1 Φ (Φρ ρ) rfl w` as an intermediate fact. Rewrite `this` using `[map_one]`. Conclude with `this`. Simplify using `only [h2] at h1`. Conclude with `sub_eq_zero.1 h1`.

Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `w`. Rewrite using `[LinearMap.zero_apply]`. Conclude with `PositivityTheory.Rg.Ming.CoreX.avg_zero σ hσ g s hcard (B Φ w) (hBΦ w)`.
-/
theorem core : BallSt → RkSt → CoreSt := by
  intro _ _ k _ _ _ _ n r μ V _ _ W _ _ σ π B j hjr hjn2 hμ hσ hE hvan c hc Φ hΦ
  classical
  letI : Fintype 𝓀[k] := Fintype.ofFinite _
  have hjn : j ≤ n := by omega
  have hjr' : j ≤ r := hjr.le
  obtain ⟨ϖ, hϖ1, hU, hnabs⟩ := PositivityTheory.Rg.Ming.CoreX.exists_unif (k := k)
  let L : 𝓀[k] → 𝒪[k] := Function.surjInv IsLocalRing.residue_surjective
  have hL : ∀ z, IsLocalRing.residue 𝒪[k] (L z) = z := Function.surjInv_eq _
  have hA : 1 ≤ Fintype.card {l : Fin r // j ≤ l.val} :=
    Fintype.card_pos_iff.2 ⟨⟨⟨j, hjr⟩, le_rfl⟩⟩
  have hw : ((ϖ : k))⁻¹ ≠ 0 := by simp
  have hdet : ∀ ρ : Fin j → {l : Fin r // j ≤ l.val} → 𝓀[k],
      (PositivityTheory.Rg.Ming.CoreX.Mr j (ϖ : k)⁻¹ (c : k) L ρ).det ≠ 0 := by
    intro ρ; rw [PositivityTheory.Rg.Ming.CoreX.Mr_det]; exact pow_ne_zero _ hw
  let g : (Fin j → {l : Fin r // j ≤ l.val} → 𝓀[k]) → GL (Fin r) k := fun ρ =>
    Matrix.GeneralLinearGroup.mkOfDetNeZero _ (hdet ρ)
  have hgv : ∀ ρ, ((g ρ : GL (Fin r) k) : Matrix (Fin r) (Fin r) k) = PositivityTheory.Rg.Ming.CoreX.Mr j (ϖ : k)⁻¹ (c : k) L ρ :=
    fun ρ => rfl
  let D : kˣ := ϖ⁻¹ ^ Fintype.card {l : Fin r // j ≤ l.val}
  have hgD : ∀ ρ, Matrix.GeneralLinearGroup.det (g ρ) = D := by
    intro ρ
    ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, hgv, PositivityTheory.Rg.Ming.CoreX.Mr_det]
    simp [D]
  let s : ℂ := (μ D : ℂ) * ((nabs k D ^ ((n : ℝ) / 2) : ℝ) : ℂ)
  have hnD : nabs k D = (resCard k : ℝ) ^ Fintype.card {l : Fin r // j ≤ l.val} := by
    have e1 : nabs k D = (nabs k ϖ)⁻¹ ^ Fintype.card {l : Fin r // j ≤ l.val} := by simp [D, nabs]
    rw [e1, hnabs, inv_inv]
  have hqr : (resCard k : ℝ) = Fintype.card 𝓀[k] := by rw [resCard, Nat.card_eq_fintype_card]
  have hq1 : 1 < Fintype.card 𝓀[k] := Fintype.one_lt_card
  have hns : ‖s‖ = ((Fintype.card 𝓀[k] : ℝ) ^ Fintype.card {l : Fin r // j ≤ l.val}) ^ ((n : ℝ) / 2) := by
    simp only [s, norm_mul, hμ D, one_mul]
    rw [hnD, hqr, Complex.norm_of_nonneg (by positivity)]
  have hs0 : s ≠ 0 := by
    intro h
    have : ‖s‖ = 0 := by rw [h, norm_zero]
    rw [hns] at this
    have hpos : (0 : ℝ) < ((Fintype.card 𝓀[k] : ℝ) ^ Fintype.card {l : Fin r // j ≤ l.val}) ^ ((n : ℝ) / 2) := by
      positivity
    linarith
  have hcard : (Fintype.card (Fin j → {l : Fin r // j ≤ l.val} → 𝓀[k]) : ℝ) < ‖s‖ := by
    rw [hns, Fintype.card_fun, Fintype.card_fun, Fintype.card_fin]
    push_cast
    have hQ : (1 : ℝ) < (Fintype.card 𝓀[k] : ℝ) ^ Fintype.card {l : Fin r // j ≤ l.val} :=
      one_lt_pow₀ (by exact_mod_cast hq1) (by omega)
    rw [← Real.rpow_natCast]
    exact Real.rpow_lt_rpow_of_exponent_lt hQ (by
      rw [lt_div_iff₀ two_pos]; exact_mod_cast (by omega : j * 2 < n))
  have hom : ∀ ρ (f : Matrix (Fin n) (Fin r) k → ℂ) x,
      om μ (g ρ) 1 f x = s * f (x * PositivityTheory.Rg.Ming.CoreX.Mr j (ϖ : k)⁻¹ (c : k) L ρ) := by
    intro ρ f x
    simp only [om, hgD, map_one, inv_one, Units.val_one, GlobalTheory.SplitWeil.Model.nabs_one, Real.one_rpow,
      Complex.ofReal_one, mul_one, Matrix.one_mul, Fintype.card_fin, hgv, s]
  let Φρ : (Fin j → {l : Fin r // j ≤ l.val} → 𝓀[k]) → SB (Matrix (Fin n) (Fin r) k) := fun ρ =>
    ⟨om μ (g ρ) 1 Φ.1, GlobalTheory.SplitWeil.Model.om_mem_SB μ (g ρ) 1 Φ.2⟩
  have hΨ : B (Φ - ∑ ρ, s⁻¹ • Φρ ρ) = 0 := by
    apply hvan
    intro x hx
    simp only [Submodule.coe_sub, Submodule.coe_sum, Submodule.coe_smul, Pi.sub_apply, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul, Φρ, hom, inv_mul_cancel_left₀ hs0, hΦ]
    rw [PositivityTheory.Rg.Ming.CoreX.ind_eq hjn hjr' hc hϖ1 hU L hL x (by omega)]
    exact sub_self _
  have hBΦ : ∀ w, B Φ w = ∑ ρ, s⁻¹ • σ (g ρ) (B Φ w) := by
    intro w
    have h1 := congrArg (fun f => f w) hΨ
    simp only [map_sub, map_sum, map_smul, LinearMap.sub_apply, LinearMap.sum_apply, LinearMap.smul_apply,
      LinearMap.zero_apply] at h1
    have h2 : ∀ ρ, B (Φρ ρ) w = σ (g ρ) (B Φ w) := by
      intro ρ
      have := hE (g ρ) 1 Φ (Φρ ρ) rfl w
      rw [map_one] at this
      exact this
    simp only [h2] at h1
    exact sub_eq_zero.1 h1
  apply LinearMap.ext
  intro w
  rw [LinearMap.zero_apply]
  exact PositivityTheory.Rg.Ming.CoreX.avg_zero σ hσ g s hcard (B Φ w) (hBΦ w)

end PositivityTheory.Rg.Ming
