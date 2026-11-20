import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DefsMod
import Formalism.GradedWeylDivisibility.StatementD
import Lemmata.GeneralBFactSecondTer.Imports

noncomputable section

open MvPolynomial Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

def qa_nu {n : ℕ} [NeZero n] (mu : Fin n → ℤ) : Fin n → ℕ := fun t => (mu t - mu (lastIdx n)).toNat

def qa_row {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (I : TIdx mu) (c : ↥(TCols mu)) : Fin (colH mu c) → Fin n :=
  fun p => (I c).1.orderEmbOfFin (I c).2 p

/- English proof (translation)
The claim follows from `((I c).1.orderEmbOfFin (I c).2).strictMono`.
-/
lemma qa_row_strictMono {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (I : TIdx mu) (c : ↥(TCols mu)) :
    StrictMono (qa_row I c) := ((I c).1.orderEmbOfFin (I c).2).strictMono

def qa_exp {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (I : TIdx mu) : Fin n × Fin n →₀ ℕ :=
  ∑ c : ↥(TCols mu), ∑ p : Fin (colH mu c), Finsupp.single (qa_row I c p, Fin.castLE (colH_le mu c) p) 1

/- English proof (translation)
Apply the tactic sequence `first | exact Bl.general_b_fact_second_ter.goal1 .. | (apply Bl.general_b_fact_second_ter.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_second_ter.goal1 <;> assumption)`.
-/
lemma qa_lower_iff {n : ℕ} (Q : Fin n → Prop) [DecidablePred Q] (hQ : ∀ q q', q' ≤ q → Q q → Q q') (p : Fin n) :
    Q p ↔ p.val < (univ.filter Q).card := by
  first | exact Bl.general_b_fact_second_ter.goal1 .. | (apply Bl.general_b_fact_second_ter.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_second_ter.goal1 <;> assumption)

/- English proof (translation)
The claim follows from `(qa_lower_iff (fun m => c ≤ mu m) (fun _ _ hqq hq => hq.trans (hmu hqq)) p).symm`.
-/
lemma qa_lt_colH {n : ℕ} {mu : Fin n → ℤ} (hmu : Dominant mu) (c : ℤ) (p : Fin n) :
    p.val < colH mu c ↔ c ≤ mu p :=
  (qa_lower_iff (fun m => c ≤ mu m) (fun _ _ hqq hq => hq.trans (hmu hqq)) p).symm

/- English proof (translation)
Establish `h1 : (J.filter (· ≤ a)).card = (univ.filter fun q : Fin h => J.orderEmbOfFin hJ q ≤ a).card` using `by conv_lhs => rw [← Finset.map_orderEmbOfFin_univ J hJ]`. Rewrite using `[Finset.filter_map, Finset.card_map]`. Both sides reduce to the same expression. Rewrite using `[h1]`. Conclude with `qa_lower_iff (fun q : Fin h => J.orderEmbOfFin hJ q ≤ a) (fun q q' hqq hq => ((J.orderEmbOfFin hJ).monotone hqq).trans hq) p`.
-/
lemma qa_emb_le_iff {n h : ℕ} (J : Finset (Fin n)) (hJ : J.card = h) (p : Fin h) (a : Fin n) :
    J.orderEmbOfFin hJ p ≤ a ↔ p.val < (J.filter (· ≤ a)).card := by
  have h1 : (J.filter (· ≤ a)).card = (univ.filter fun q : Fin h => J.orderEmbOfFin hJ q ≤ a).card := by
    conv_lhs => rw [← Finset.map_orderEmbOfFin_univ J hJ]
    rw [Finset.filter_map, Finset.card_map]
    rfl
  rw [h1]
  exact qa_lower_iff (fun q : Fin h => J.orderEmbOfFin hJ q ≤ a)
    (fun q q' hqq hq => ((J.orderEmbOfFin hJ).monotone hqq).trans hq) p

/- English proof (translation)
Rewrite `hc` using `[Finset.mem_Ioc]`. Establish `hdown : ∀ k : ℕ, ∀ d, L < d → d + k ≤ U → Q (d + k) → Q d`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => intro d _ _ h`.

Simplify using `using h`. Consider the case `succ k ih`. Introduce `d hd hU h`. Apply `ih d hd (by push_cast at hU; omega)` to reduce the goal to its premises. Apply `hQ _ (by omega) (by push_cast at hU; omega)` to reduce the goal to its premises.

Establish `: d + (k : ℤ) + 1 = d + ((k + 1 : ℕ) : ℤ)` using `by push_cast; ring`. Rewrite using `[this]`. Conclude with `h`. Establish `hdown' : ∀ d e, L < d → d ≤ e → e ≤ U → Q e → Q d`. Introduce `d e hd hde he h`.

Use `hdown (e - d).toNat d hd (by omega)` as an intermediate fact. Apply `this` to reduce the goal to its premises. Establish `h3 : d + ((e - d).toNat : ℤ) = e` using `by omega`. Rewrite using `[h3]`. Conclude with `h`.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `: Finset.Ioc L c ⊆ (Finset.Ioc L U).filter Q`. Introduce `d hd`. Rewrite `hd` using `[Finset.mem_Ioc]`.

Rewrite using `[Finset.mem_filter, Finset.mem_Ioc]`. Conclude with `⟨⟨hd.1, hd.2.trans hc.2⟩, hdown' d c hd.1 hd.2 hc.2 h⟩`. Establish `h2` using `Finset.card_le_card this`. Rewrite `h2` using `[Int.card_Ioc]`. Use linear arithmetic over natural numbers and integers.

Introduce `h`. Assume the negation of the conclusion as `hn`. Establish `: (Finset.Ioc L U).filter Q ⊆ Finset.Ioo L c`. Introduce `d hd`. Rewrite `hd` using `[Finset.mem_filter, Finset.mem_Ioc]`.

Rewrite using `[Finset.mem_Ioo]`. Use `⟨hd.1.1, ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hle`. Conclude with `hn (hdown' c d hc.1 (not_lt.mp hle) hd.1.2 hd.2)`. Establish `h2` using `Finset.card_le_card this`.

Rewrite `h2` using `[Int.card_Ioo]`. Use linear arithmetic over natural numbers and integers.
-/
lemma qa_seg (L U : ℤ) (Q : ℤ → Prop) [DecidablePred Q] (hQ : ∀ c, L < c → c + 1 ≤ U → Q (c + 1) → Q c)
    (c : ℤ) (hc : c ∈ Finset.Ioc L U) : Q c ↔ c - L ≤ ((Finset.Ioc L U).filter Q).card := by
  rw [Finset.mem_Ioc] at hc
  have hdown : ∀ k : ℕ, ∀ d, L < d → d + k ≤ U → Q (d + k) → Q d := by
    intro k
    induction k with
    | zero => intro d _ _ h; simpa using h
    | succ k ih =>
      intro d hd hU h
      apply ih d hd (by push_cast at hU; omega)
      apply hQ _ (by omega) (by push_cast at hU; omega)
      have : d + (k : ℤ) + 1 = d + ((k + 1 : ℕ) : ℤ) := by push_cast; ring
      rw [this]; exact h
  have hdown' : ∀ d e, L < d → d ≤ e → e ≤ U → Q e → Q d := by
    intro d e hd hde he h
    have := hdown (e - d).toNat d hd (by omega)
    apply this
    have h3 : d + ((e - d).toNat : ℤ) = e := by omega
    rw [h3]; exact h
  constructor
  · intro h
    have : Finset.Ioc L c ⊆ (Finset.Ioc L U).filter Q := by
      intro d hd
      rw [Finset.mem_Ioc] at hd
      rw [Finset.mem_filter, Finset.mem_Ioc]
      exact ⟨⟨hd.1, hd.2.trans hc.2⟩, hdown' d c hd.1 hd.2 hc.2 h⟩
    have h2 := Finset.card_le_card this
    rw [Int.card_Ioc] at h2
    omega
  · intro h
    by_contra hn
    have : (Finset.Ioc L U).filter Q ⊆ Finset.Ioo L c := by
      intro d hd
      rw [Finset.mem_filter, Finset.mem_Ioc] at hd
      rw [Finset.mem_Ioo]
      refine ⟨hd.1.1, ?_⟩
      by_contra hle
      exact hn (hdown' c d hc.1 (not_lt.mp hle) hd.1.2 hd.2)
    have h2 := Finset.card_le_card this
    rw [Int.card_Ioo] at h2
    omega

def qa_cnt {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (I : TIdx mu) (c : ↥(TCols mu)) (a : Fin n) : ℕ :=
  ((I c).1.filter (· ≤ a)).card

/- English proof (translation)
The claim follows from `(card_filter_le _ _).trans (I c).2.le`.
-/
lemma qa_cnt_le {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (I : TIdx mu) (c : ↥(TCols mu)) (a : Fin n) :
    qa_cnt I c a ≤ colH mu c := (card_filter_le _ _).trans (I c).2.le

/- English proof (translation)
The claim follows from `qa_emb_le_iff (I c).1 (I c).2 q a`.
-/
lemma qa_row_le_iff {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (I : TIdx mu) (c : ↥(TCols mu)) (q : Fin (colH mu c))
    (a : Fin n) : qa_row I c q ≤ a ↔ q.val < qa_cnt I c a := qa_emb_le_iff (I c).1 (I c).2 q a

/- English proof (translation)
Simplify using `only [qa_exp, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.single_apply, Prod.mk.injEq, Fin.ext_iff, Fin.val_castLE]`.
-/
lemma qa_exp_apply {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (I : TIdx mu) (b p : Fin n) :
    qa_exp I (b, p) = ∑ c : ↥(TCols mu), ∑ q : Fin (colH mu c),
      if qa_row I c q = b ∧ q.val = p.val then 1 else 0 := by
  simp only [qa_exp, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.single_apply, Prod.mk.injEq, Fin.ext_iff,
    Fin.val_castLE]

/- English proof (translation)
Simplify using `only [qa_exp_apply]`. Rewrite using `[Finset.sum_comm, Finset.card_filter]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_comm]`. Establish `h1 : ∀ q : Fin (colH mu c), (∑ b : Fin n with b ≤ a, if qa_row I c q = b ∧ q.val = p.val then 1 else 0) = if (q.val = p.val ∧ q.val < qa_cnt I c a) then 1 else 0`.

Introduce `q`. Rewrite using `[Finset.sum_filter, Finset.sum_eq_single (qa_row I c q)]`. Use `qa_row_le_iff I c q a` as an intermediate fact. Distinguish the cases in `h : qa_row I c q ≤ a`. Simplify using `[h, this.mp h]`.

Establish `h' : ¬ q.val < qa_cnt I c a` using `fun hh => h (this.mpr hh)`. Simplify using `[h, h']`. Introduce `b _ hb`. Simplify using `[Ne.symm hb]`. Simplify using the standard rewrite rules.

Simplify using `only [h1]`. Use `split_ifs with hp`. Establish `hq : p.val < colH mu c` using `hp.trans_le (qa_cnt_le I c a)`. Rewrite using `[Finset.sum_eq_single ⟨p.val, hq⟩]`. Simplify using `[hp]`.

Introduce `q _ hq'`. Rewrite using `[if_neg]`. Introduce and unpack `⟨h2, _⟩`. Conclude with `hq' (Fin.ext h2)`. Simplify using the standard rewrite rules.

Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `q _`. Rewrite using `[if_neg]`. Introduce and unpack `⟨h2, h3⟩`. Conclude with `hp (h2 ▸ h3)`.
-/
lemma qa_cum {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (I : TIdx mu) (a p : Fin n) :
    ∑ b : Fin n with b ≤ a, qa_exp I (b, p) =
      (univ.filter fun c : ↥(TCols mu) => p.val < qa_cnt I c a).card := by
  simp only [qa_exp_apply]
  rw [Finset.sum_comm, Finset.card_filter]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_comm]
  have h1 : ∀ q : Fin (colH mu c),
      (∑ b : Fin n with b ≤ a, if qa_row I c q = b ∧ q.val = p.val then 1 else 0) =
        if (q.val = p.val ∧ q.val < qa_cnt I c a) then 1 else 0 := by
    intro q
    rw [Finset.sum_filter, Finset.sum_eq_single (qa_row I c q)]
    · have := qa_row_le_iff I c q a
      by_cases h : qa_row I c q ≤ a
      · simp [h, this.mp h]
      · have h' : ¬ q.val < qa_cnt I c a := fun hh => h (this.mpr hh)
        simp [h, h']
    · intro b _ hb
      simp [Ne.symm hb]
    · simp
  simp only [h1]
  split_ifs with hp
  · have hq : p.val < colH mu c := hp.trans_le (qa_cnt_le I c a)
    rw [Finset.sum_eq_single ⟨p.val, hq⟩]
    · simp [hp]
    · intro q _ hq'
      rw [if_neg]
      rintro ⟨h2, _⟩
      exact hq' (Fin.ext h2)
    · simp
  · apply Finset.sum_eq_zero
    intro q _
    rw [if_neg]
    rintro ⟨h2, h3⟩
    exact hp (h2 ▸ h3)

/- English proof (translation)
Rewrite using `[← Finset.card_map (Function.Embedding.subtype _)]`. Use `congr 1`. Use extensionality with `d`. Simplify using `only [mem_map, mem_filter, mem_univ, true_and, Function.Embedding.coe_subtype, Subtype.exists, exists_and_right, exists_eq_right]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨h, hp⟩`. Conclude with `⟨h, h, hp⟩`. Introduce and unpack `⟨_, h, hp⟩`. Conclude with `⟨h, hp⟩`.
-/
lemma qa_card_sub {T : Finset ℤ} (P : ↥T → Prop) [DecidablePred P]
    [DecidablePred fun d => ∃ h : d ∈ T, P ⟨d, h⟩] :
    (univ.filter P).card = (T.filter fun d => ∃ h : d ∈ T, P ⟨d, h⟩).card := by
  rw [← Finset.card_map (Function.Embedding.subtype _)]
  congr 1
  ext d
  simp only [mem_map, mem_filter, mem_univ, true_and, Function.Embedding.coe_subtype, Subtype.exists,
    exists_and_right, exists_eq_right]
  constructor
  · rintro ⟨h, hp⟩; exact ⟨h, h, hp⟩
  · rintro ⟨_, h, hp⟩; exact ⟨h, hp⟩

/- English proof (translation)
Rewrite using `[qa_cum, qa_card_sub]`. Use `qa_seg (mu (lastIdx n)) (mu 0) (fun d => ∃ h : d ∈ TCols mu, p.val < qa_cnt I ⟨d, h⟩ a) ?_ c c.2` as an intermediate fact. Rewrite `this` using `[← TCols]`. Rewrite using `[← this]`. Conclude with `⟨fun h => ⟨c.2, h⟩, fun ⟨_, h⟩ => h⟩`.

Introduce and unpack `d hd hU ⟨h, hp⟩`. Establish `hd' : d ∈ TCols mu` using `Finset.mem_Ioc.mpr ⟨hd, by omega⟩`. Conclude with `⟨hd', hp.trans_le (hI ⟨d, hd'⟩ h a)⟩`.
-/
lemma qa_std_iff {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (I : TIdx mu) (hI : StdT I) (c : ↥(TCols mu))
    (a p : Fin n) :
    p.val < qa_cnt I c a ↔
      (c : ℤ) - mu (lastIdx n) ≤ ((∑ b : Fin n with b ≤ a, qa_exp I (b, p) : ℕ) : ℤ) := by
  classical
  rw [qa_cum, qa_card_sub]
  have := qa_seg (mu (lastIdx n)) (mu 0) (fun d => ∃ h : d ∈ TCols mu, p.val < qa_cnt I ⟨d, h⟩ a) ?_ c c.2
  · rw [← TCols] at this
    rw [← this]
    exact ⟨fun h => ⟨c.2, h⟩, fun ⟨_, h⟩ => h⟩
  · rintro d hd hU ⟨h, hp⟩
    have hd' : d ∈ TCols mu := Finset.mem_Ioc.mpr ⟨hd, by omega⟩
    exact ⟨hd', hp.trans_le (hI ⟨d, hd'⟩ h a)⟩

/- English proof (translation)
Use function extensionality and compare the values at `c`. Apply `Subtype.ext` to reduce the goal to its premises. Establish `hrow : ∀ q, qa_row I c q = qa_row J c q`. Introduce `q`. Establish `hq : q.val < n` using `q.2.trans_le (colH_le mu c)`.

Establish `key : ∀ a, qa_row I c q ≤ a ↔ qa_row J c q ≤ a`. Introduce `a`. Rewrite using `[qa_row_le_iff, qa_row_le_iff]`. Establish `h1` using `qa_std_iff I hI c a ⟨q.val, hq⟩`. Establish `h2` using `qa_std_iff J hJ c a ⟨q.val, hq⟩`.

Rewrite `h1` using `[h]`. Conclude with `h1.trans h2.symm`. Conclude with `le_antisymm ((key _).mpr le_rfl) ((key _).mp le_rfl)`. Rewrite using `[← Finset.map_orderEmbOfFin_univ (I c).1 (I c).2, ← Finset.map_orderEmbOfFin_univ (J c).1 (J c).2]`. Use extensionality with `x`.

Simplify using `only [mem_map, mem_univ, true_and]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨q, rfl⟩`. Conclude with `⟨q, (hrow q).symm⟩`. Introduce and unpack `⟨q, rfl⟩`.

Conclude with `⟨q, hrow q⟩`.
-/
theorem qa_exp_inj {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (I J : TIdx mu) (hI : StdT I) (hJ : StdT J)
    (h : qa_exp I = qa_exp J) : I = J := by
  funext c
  apply Subtype.ext
  have hrow : ∀ q, qa_row I c q = qa_row J c q := by
    intro q
    have hq : q.val < n := q.2.trans_le (colH_le mu c)
    have key : ∀ a, qa_row I c q ≤ a ↔ qa_row J c q ≤ a := by
      intro a
      rw [qa_row_le_iff, qa_row_le_iff]
      have h1 := qa_std_iff I hI c a ⟨q.val, hq⟩
      have h2 := qa_std_iff J hJ c a ⟨q.val, hq⟩
      rw [h] at h1
      exact h1.trans h2.symm
    exact le_antisymm ((key _).mpr le_rfl) ((key _).mp le_rfl)
  rw [← Finset.map_orderEmbOfFin_univ (I c).1 (I c).2, ← Finset.map_orderEmbOfFin_univ (J c).1 (J c).2]
  ext x
  simp only [mem_map, mem_univ, true_and]
  constructor
  · rintro ⟨q, rfl⟩; exact ⟨q, (hrow q).symm⟩
  · rintro ⟨q, rfl⟩; exact ⟨q, hrow q⟩

end Formalism.InvariantFactorPaths.ColumnFamilies
