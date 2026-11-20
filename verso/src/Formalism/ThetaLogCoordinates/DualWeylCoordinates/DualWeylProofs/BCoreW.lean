import Formalism.ThetaLogCoordinates.DualWeylCoordinates.FiltrationTheoremOfClauses

noncomputable section

open Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

variable {n : ℕ}

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun _ => le_rfl, rfl⟩`.
-/
lemma qb_domLE_refl (mu : Fin n → ℤ) : DomLE mu mu := ⟨fun _ => le_rfl, rfl⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun i => (h1.1 i).trans (h2.1 i), h1.2.trans h2.2⟩`.
-/
lemma qb_domLE_trans {a b c : Fin n → ℤ} (h1 : DomLE a b) (h2 : DomLE b c) : DomLE a c :=
  ⟨fun i => (h1.1 i).trans (h2.1 i), h1.2.trans h2.2⟩

/- English proof (translation)
Use function extensionality and compare the values at `a`. Proceed by induction on `a using WellFoundedLT.induction with`. Consider the case `_ a ih`. Establish `h1` using `h a`. Establish `e : (univ.filter (· ≤ a) : Finset (Fin n)) = insert a (univ.filter (· < a))`.

Use extensionality with `b`. Simplify using `[le_iff_eq_or_lt]`. Rewrite `h1` using `[e, sum_insert (by simp), sum_insert (by simp)]`. Establish `h2 : ∑ b ∈ univ.filter (· < a), f b = ∑ b ∈ univ.filter (· < a), g b` using `sum_congr rfl fun b hb => ih b (by simpa using hb)`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma qb_eq_of_psum_eq {f g : Fin n → ℤ}
    (h : ∀ a : Fin n, ∑ b ∈ univ.filter (· ≤ a), f b = ∑ b ∈ univ.filter (· ≤ a), g b) : f = g := by
  funext a
  induction a using WellFoundedLT.induction with
  | _ a ih =>
    have h1 := h a
    have e : (univ.filter (· ≤ a) : Finset (Fin n)) = insert a (univ.filter (· < a)) := by
      ext b; simp [le_iff_eq_or_lt]
    rw [e, sum_insert (by simp), sum_insert (by simp)] at h1
    have h2 : ∑ b ∈ univ.filter (· < a), f b = ∑ b ∈ univ.filter (· < a), g b :=
      sum_congr rfl fun b hb => ih b (by simpa using hb)
    linarith

def qb_psi (mu : Fin n → ℤ) : ℤ := ∑ a, ∑ b ∈ univ.filter (· ≤ a), mu b

/- English proof (translation)
The claim follows from `sum_le_sum fun a _ => h.1 a`.
-/
lemma qb_psi_le {nu mu : Fin n → ℤ} (h : DomLE nu mu) : qb_psi nu ≤ qb_psi mu :=
  sum_le_sum fun a _ => h.1 a

/- English proof (translation)
Apply `qb_eq_of_psum_eq` to reduce the goal to its premises. Assume the negation of the conclusion as `hne`. Use `push Not at hne`. Take `⟨a, ha⟩` from `hne`. Establish `: qb_psi nu < qb_psi mu` using `sum_lt_sum (fun i _ => h.1 i) ⟨a, mem_univ _, lt_of_le_of_ne (h.1 a) ha⟩`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma qb_eq_of_psi {nu mu : Fin n → ℤ} (h : DomLE nu mu) (h2 : qb_psi mu ≤ qb_psi nu) : nu = mu := by
  apply qb_eq_of_psum_eq
  by_contra hne
  push Not at hne
  obtain ⟨a, ha⟩ := hne
  have : qb_psi nu < qb_psi mu :=
    sum_lt_sum (fun i _ => h.1 i) ⟨a, mem_univ _, lt_of_le_of_ne (h.1 a) ha⟩
  linarith

/- English proof (translation)
The claim follows from `qb_eq_of_psi h1 (qb_psi_le h2)`.
-/
lemma qb_domLE_antisymm {nu mu : Fin n → ℤ} (h1 : DomLE nu mu) (h2 : DomLE mu nu) : nu = mu :=
  qb_eq_of_psi h1 (qb_psi_le h2)

/- English proof (translation)
Take `⟨nu, hnu, hmax⟩` from `s.exists_max_image qb_psi hs`. Conclude with `⟨nu, hnu, fun mu hmu hle => (qb_eq_of_psi hle (hmax mu hmu)).symm⟩`.
-/
lemma qb_exists_max (s : Finset (Fin n → ℤ)) (hs : s.Nonempty) :
    ∃ nu ∈ s, ∀ mu ∈ s, DomLE nu mu → mu = nu := by
  obtain ⟨nu, hnu, hmax⟩ := s.exists_max_image qb_psi hs
  exact ⟨nu, hnu, fun mu hmu hle => (qb_eq_of_psi hle (hmax mu hmu)).symm⟩

/- English proof (translation)
Take `⟨nu, hnu, hmax⟩` from `qb_exists_max (s.filter fun mu => DomLE mu0 mu) ⟨mu0, by simp [h0, qb_domLE_refl]⟩`. Rewrite `hnu` using `[mem_filter]`. Conclude with `⟨nu, hnu.1, hnu.2, fun mu hmu hle => hmax mu (by rw [mem_filter]; exact ⟨hmu, qb_domLE_trans hnu.2 hle⟩) hle⟩`.
-/
lemma qb_exists_max_above (s : Finset (Fin n → ℤ)) {mu0 : Fin n → ℤ} (h0 : mu0 ∈ s) :
    ∃ nu ∈ s, DomLE mu0 nu ∧ ∀ mu ∈ s, DomLE nu mu → mu = nu := by
  classical
  obtain ⟨nu, hnu, hmax⟩ := qb_exists_max (s.filter fun mu => DomLE mu0 mu)
    ⟨mu0, by simp [h0, qb_domLE_refl]⟩
  rw [mem_filter] at hnu
  exact ⟨nu, hnu.1, hnu.2, fun mu hmu hle =>
    hmax mu (by rw [mem_filter]; exact ⟨hmu, qb_domLE_trans hnu.2 hle⟩) hle⟩

variable [NeZero n]

def qb_wtT (mu : Fin n → ℤ) (I : TIdx mu) : Fin n → ℤ :=
  fun a => mu (lastIdx n) + ((univ.filter fun c : ↥(TCols mu) => a ∈ (I c).1).card : ℤ)

/- English proof (translation)
Unfold `qb_wtT`. Rewrite using `[sum_add_distrib, sum_const, nsmul_eq_mul]`. Use `congr 1`. Simplify using `only [card_filter, Nat.cast_sum]`. Rewrite using `[sum_comm]`.
-/
lemma qb_sum_wtT (mu : Fin n → ℤ) (I : TIdx mu) (s : Finset (Fin n)) :
    ∑ b ∈ s, qb_wtT mu I b =
      (s.card : ℤ) * mu (lastIdx n) + ∑ c : ↥(TCols mu), ((s.filter (· ∈ (I c).1)).card : ℤ) := by
  unfold qb_wtT
  rw [sum_add_distrib, sum_const, nsmul_eq_mul]
  congr 1
  simp only [card_filter, Nat.cast_sum]
  rw [sum_comm]

/- English proof (translation)
Simplify using `only [canT, mem_map, mem_univ, true_and]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, rfl⟩`. Conclude with `x.2`. Introduce `h; exact ⟨⟨b.val, h⟩, by ext; rfl⟩`.
-/
lemma qb_mem_canT (mu : Fin n → ℤ) (c : ↥(TCols mu)) (b : Fin n) :
    b ∈ (canT mu c).1 ↔ b.val < colH mu c := by
  simp only [canT, mem_map, mem_univ, true_and]
  constructor
  · rintro ⟨x, rfl⟩; exact x.2
  · intro h; exact ⟨⟨b.val, h⟩, by ext; rfl⟩

/- English proof (translation)
Distinguish the cases in `h : a.val < colH mu c`. Apply `card_le_card` to reduce the goal to its premises. Introduce `b hb`. Simplify using `only [mem_filter, mem_univ, true_and] at hb ⊢`. Conclude with `⟨hb.1, (qb_mem_canT mu c b).2 (lt_of_le_of_lt hb.1 h)⟩`.

Combine the equalities or inequalities in the displayed calculation. Simplify using `only [mem_filter, mem_univ, true_and]`. Use `⟨?_, hb⟩` and prove the remaining obligations. Use `(qb_mem_canT mu c b).1 hb` as an intermediate fact. Conclude with `Fin.le_def.2 (by omega)`.
-/
lemma qb_col_le (mu : Fin n → ℤ) (c : ↥(TCols mu)) (J : Finset (Fin n)) (hJ : J.card = colH mu c) (a : Fin n) :
    ((univ.filter (· ≤ a)).filter (· ∈ J)).card ≤ ((univ.filter (· ≤ a)).filter (· ∈ (canT mu c).1)).card := by
  by_cases h : a.val < colH mu c
  · apply card_le_card
    intro b hb
    simp only [mem_filter, mem_univ, true_and] at hb ⊢
    exact ⟨hb.1, (qb_mem_canT mu c b).2 (lt_of_le_of_lt hb.1 h)⟩
  · calc ((univ.filter (· ≤ a)).filter (· ∈ J)).card ≤ J.card :=
          card_le_card fun b hb => (mem_filter.1 hb).2
      _ = (canT mu c).1.card := by rw [hJ, (canT mu c).2]
      _ ≤ _ := card_le_card fun b hb => by
          simp only [mem_filter, mem_univ, true_and]
          refine ⟨?_, hb⟩
          have := (qb_mem_canT mu c b).1 hb
          exact Fin.le_def.2 (by omega)

/- English proof (translation)
Break down `Nat.eq_zero_or_pos (colH mu c) with h0 | hpos` into its components or cases. Establish `h1 : J = ∅` using `card_eq_zero.1 (hJ.trans h0)`. Establish `h2 : (canT mu c).1 = ∅` using `card_eq_zero.1 ((canT mu c).2.trans h0)`. Rewrite using `[h1, h2]`. Establish `hn` using `colH_le mu c`.

Set `a : Fin n` to `⟨colH mu c - 1, by omega⟩`. Establish `hc : (canT mu c).1 ⊆ (univ.filter (· ≤ a)).filter (· ∈ (canT mu c).1)` using `fun b hb => by`. Simplify using `only [mem_filter, mem_univ, true_and]`. Use `⟨?_, hb⟩` and prove the remaining obligations. Use `(qb_mem_canT mu c b).1 hb` as an intermediate fact.

Conclude with `Fin.le_def.2 (by simp only [a]; omega)`. Establish `h3 : J.card ≤ ((univ.filter (· ≤ a)).filter (· ∈ J)).card`. Rewrite using `[h a, hJ]`. Conclude with `(canT mu c).2.symm.le.trans (card_le_card hc)`. Establish `h4 : (univ.filter (· ≤ a)).filter (· ∈ J) = J` using `eq_of_subset_of_card_le (fun b hb => (mem_filter.1 hb).2) h3`.

Apply `eq_of_subset_of_card_le` to reduce the goal to its premises. Introduce `b hb`. Rewrite `hb` using `[← h4]`. Simplify using `only [mem_filter, mem_univ, true_and] at hb`. Use `Fin.le_def.1 hb.1` as an intermediate fact.

Conclude with `(qb_mem_canT mu c b).2 (by simp only [a] at this; omega)`. Rewrite using `[hJ, (canT mu c).2]`.
-/
lemma qb_col_eq (mu : Fin n → ℤ) (c : ↥(TCols mu)) (J : Finset (Fin n)) (hJ : J.card = colH mu c)
    (h : ∀ a : Fin n, ((univ.filter (· ≤ a)).filter (· ∈ J)).card =
      ((univ.filter (· ≤ a)).filter (· ∈ (canT mu c).1)).card) : J = (canT mu c).1 := by
  rcases Nat.eq_zero_or_pos (colH mu c) with h0 | hpos
  · have h1 : J = ∅ := card_eq_zero.1 (hJ.trans h0)
    have h2 : (canT mu c).1 = ∅ := card_eq_zero.1 ((canT mu c).2.trans h0)
    rw [h1, h2]
  · have hn := colH_le mu c
    let a : Fin n := ⟨colH mu c - 1, by omega⟩
    have hc : (canT mu c).1 ⊆ (univ.filter (· ≤ a)).filter (· ∈ (canT mu c).1) := fun b hb => by
      simp only [mem_filter, mem_univ, true_and]
      refine ⟨?_, hb⟩
      have := (qb_mem_canT mu c b).1 hb
      exact Fin.le_def.2 (by simp only [a]; omega)
    have h3 : J.card ≤ ((univ.filter (· ≤ a)).filter (· ∈ J)).card := by
      rw [h a, hJ]; exact (canT mu c).2.symm.le.trans (card_le_card hc)
    have h4 : (univ.filter (· ≤ a)).filter (· ∈ J) = J :=
      eq_of_subset_of_card_le (fun b hb => (mem_filter.1 hb).2) h3
    apply eq_of_subset_of_card_le
    · intro b hb
      rw [← h4] at hb
      simp only [mem_filter, mem_univ, true_and] at hb
      have := Fin.le_def.1 hb.1
      exact (qb_mem_canT mu c b).2 (by simp only [a] at this; omega)
    · rw [hJ, (canT mu c).2]

/- English proof (translation)
Unfold `colH`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Assume the negation of the conclusion as `hc`. Establish `: (univ.filter fun m => c ≤ mu m) ⊆ Finset.Iio b` using `fun m hm => by`.

Simplify using `only [mem_filter, mem_univ, true_and] at hm`. Rewrite using `[mem_Iio]`. Assume the negation of the conclusion as `hmb`. Conclude with `hc (hm.trans (hmu (not_lt.1 hmb)))`. Use `card_le_card this` as an intermediate fact.

Rewrite `this` using `[Fin.card_Iio]`. Use linear arithmetic over natural numbers and integers. Introduce `h`. Establish `: Finset.Iic b ⊆ (univ.filter fun m => c ≤ mu m)` using `fun m hm => by`. Simplify using `only [mem_filter, mem_univ, true_and]`.

Conclude with `h.trans (hmu (mem_Iic.1 hm))`. Use `card_le_card this` as an intermediate fact. Rewrite `this` using `[Fin.card_Iic]`. Use linear arithmetic over natural numbers and integers.
-/
lemma qb_lt_colH_iff {mu : Fin n → ℤ} (hmu : Dominant mu) (c : ℤ) (b : Fin n) :
    b.val < colH mu c ↔ c ≤ mu b := by
  unfold colH
  constructor
  · intro h
    by_contra hc
    have : (univ.filter fun m => c ≤ mu m) ⊆ Finset.Iio b := fun m hm => by
      simp only [mem_filter, mem_univ, true_and] at hm
      rw [mem_Iio]
      by_contra hmb
      exact hc (hm.trans (hmu (not_lt.1 hmb)))
    have := card_le_card this
    rw [Fin.card_Iio] at this
    omega
  · intro h
    have : Finset.Iic b ⊆ (univ.filter fun m => c ≤ mu m) := fun m hm => by
      simp only [mem_filter, mem_univ, true_and]
      exact h.trans (hmu (mem_Iic.1 hm))
    have := card_le_card this
    rw [Fin.card_Iic] at this
    omega

/- English proof (translation)
The claim follows from `Fin.le_def.2 (by have := b.2; simp only [lastIdx]; omega)`.
-/
lemma qb_le_lastIdx (b : Fin n) : b ≤ lastIdx n := Fin.le_def.2 (by have := b.2; simp only [lastIdx]; omega)

/- English proof (translation)
Use function extensionality and compare the values at `b`. Unfold `qb_wtT`. Establish `e : ((univ.filter fun c : ↥(TCols mu) => b ∈ (canT mu c).1).map (Function.Embedding.subtype _)) = Finset.Ioc (mu (lastIdx n)) (mu b)`. Use extensionality with `c`. Rewrite using `[mem_map, mem_Ioc]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨c', hc'⟩, h1, rfl⟩`. Rewrite `h1` using `[mem_filter, qb_mem_canT, qb_lt_colH_iff hmu]`. Conclude with `⟨(mem_Ioc.1 hc').1, h1.2⟩`. Introduce and unpack `⟨h1, h2⟩`.

Use `⟨⟨c, mem_Ioc.2 ⟨h1, h2.trans (hmu (Fin.zero_le b))⟩⟩, ?_, rfl⟩` and prove the remaining obligations. Rewrite using `[mem_filter, qb_mem_canT, qb_lt_colH_iff hmu]`. Conclude with `⟨mem_univ _, h2⟩`. Rewrite using `[← card_map (Function.Embedding.subtype _), e, Int.card_Ioc]`. Use `hmu (qb_le_lastIdx b)` as an intermediate fact.

Rewrite using `[Int.toNat_of_nonneg (by omega)]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma qb_wtT_can {mu : Fin n → ℤ} (hmu : Dominant mu) : qb_wtT mu (canT mu) = mu := by
  funext b
  unfold qb_wtT
  have e : ((univ.filter fun c : ↥(TCols mu) => b ∈ (canT mu c).1).map (Function.Embedding.subtype _)) =
      Finset.Ioc (mu (lastIdx n)) (mu b) := by
    ext c
    rw [mem_map, mem_Ioc]
    constructor
    · rintro ⟨⟨c', hc'⟩, h1, rfl⟩
      rw [mem_filter, qb_mem_canT, qb_lt_colH_iff hmu] at h1
      exact ⟨(mem_Ioc.1 hc').1, h1.2⟩
    · rintro ⟨h1, h2⟩
      refine ⟨⟨c, mem_Ioc.2 ⟨h1, h2.trans (hmu (Fin.zero_le b))⟩⟩, ?_, rfl⟩
      rw [mem_filter, qb_mem_canT, qb_lt_colH_iff hmu]
      exact ⟨mem_univ _, h2⟩
  rw [← card_map (Function.Embedding.subtype _), e, Int.card_Ioc]
  have := hmu (qb_le_lastIdx b)
  rw [Int.toNat_of_nonneg (by omega)]
  ring

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `a conv_rhs => rw [← qb_wtT_can hmu]`. Rewrite using `[qb_sum_wtT, qb_sum_wtT]`. Establish `: ∑ c : ↥(TCols mu), (((univ.filter (· ≤ a)).filter (· ∈ (I c).1)).card : ℤ) ≤ ∑ c : ↥(TCols mu), (((univ.filter (· ≤ a)).filter (· ∈ (canT mu c).1)).card : ℤ)` using `sum_le_sum fun c _ => by exact_mod_cast qb_col_le mu c (I c).1 (I c).2 a`. Combine the linear equalities and inequalities to obtain the conclusion.

Use `conv_rhs => rw [← qb_wtT_can hmu]`. Rewrite using `[qb_sum_wtT, qb_sum_wtT]`. Use `congr 1`. Use `sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Simplify using `only [filter_univ_mem]`.

Rewrite using `[(I c).2, (canT mu c).2]`.
-/
lemma qb_wtT_le {mu : Fin n → ℤ} (hmu : Dominant mu) (I : TIdx mu) : DomLE (qb_wtT mu I) mu := by
  constructor
  · intro a
    conv_rhs => rw [← qb_wtT_can hmu]
    rw [qb_sum_wtT, qb_sum_wtT]
    have : ∑ c : ↥(TCols mu), (((univ.filter (· ≤ a)).filter (· ∈ (I c).1)).card : ℤ) ≤
        ∑ c : ↥(TCols mu), (((univ.filter (· ≤ a)).filter (· ∈ (canT mu c).1)).card : ℤ) :=
      sum_le_sum fun c _ => by exact_mod_cast qb_col_le mu c (I c).1 (I c).2 a
    linarith
  · conv_rhs => rw [← qb_wtT_can hmu]
    rw [qb_sum_wtT, qb_sum_wtT]
    congr 1
    refine sum_congr rfl fun c _ => ?_
    simp only [filter_univ_mem]
    rw [(I c).2, (canT mu c).2]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Use function extensionality and compare the values at `c`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `qb_col_eq mu c (I c).1 (I c).2` to reduce the goal to its premises.

Introduce `a`. Establish `h1 : ∑ b ∈ univ.filter (· ≤ a), qb_wtT mu I b = ∑ b ∈ univ.filter (· ≤ a), qb_wtT mu (canT mu) b`. Rewrite using `[h, qb_wtT_can hmu]`. Rewrite `h1` using `[qb_sum_wtT, qb_sum_wtT]`. Establish `h2 : ∑ c : ↥(TCols mu), ((((univ.filter (· ≤ a)).filter (· ∈ (canT mu c).1)).card : ℤ) - (((univ.filter (· ≤ a)).filter (· ∈ (I c).1)).card : ℤ)) = 0`.

Rewrite using `[sum_sub_distrib]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h3` using `(sum_eq_zero_iff_of_nonneg (fun c _ => by`. Use `qb_col_le mu c (I c).1 (I c).2 a` as an intermediate fact. Establish `: (((univ.filter (· ≤ a)).filter (· ∈ (I c).1)).card : ℤ) ≤ (((univ.filter (· ≤ a)).filter (· ∈ (canT mu c).1)).card : ℤ)` using `by exact_mod_cast this`.

Use the proof step `linarith)).1 h2 c (mem_univ c)`. Establish `: (((univ.filter (· ≤ a)).filter (· ∈ (I c).1)).card : ℤ) = (((univ.filter (· ≤ a)).filter (· ∈ (canT mu c).1)).card : ℤ)` using `by linarith`. Conclude with `this` after adjusting the coercions. Introduce and unpack `rfl`. Conclude with `qb_wtT_can hmu`.
-/
lemma qb_wtT_eq_iff {mu : Fin n → ℤ} (hmu : Dominant mu) (I : TIdx mu) : qb_wtT mu I = mu ↔ I = canT mu := by
  constructor
  · intro h
    funext c
    apply Subtype.ext
    apply qb_col_eq mu c (I c).1 (I c).2
    intro a
    have h1 : ∑ b ∈ univ.filter (· ≤ a), qb_wtT mu I b = ∑ b ∈ univ.filter (· ≤ a), qb_wtT mu (canT mu) b := by
      rw [h, qb_wtT_can hmu]
    rw [qb_sum_wtT, qb_sum_wtT] at h1
    have h2 : ∑ c : ↥(TCols mu), ((((univ.filter (· ≤ a)).filter (· ∈ (canT mu c).1)).card : ℤ) -
        (((univ.filter (· ≤ a)).filter (· ∈ (I c).1)).card : ℤ)) = 0 := by
      rw [sum_sub_distrib]; linarith
    have h3 := (sum_eq_zero_iff_of_nonneg (fun c _ => by
      have := qb_col_le mu c (I c).1 (I c).2 a
      have : (((univ.filter (· ≤ a)).filter (· ∈ (I c).1)).card : ℤ) ≤
        (((univ.filter (· ≤ a)).filter (· ∈ (canT mu c).1)).card : ℤ) := by exact_mod_cast this
      linarith)).1 h2 c (mem_univ c)
    have : (((univ.filter (· ≤ a)).filter (· ∈ (I c).1)).card : ℤ) =
        (((univ.filter (· ≤ a)).filter (· ∈ (canT mu c).1)).card : ℤ) := by linarith
    exact_mod_cast this
  · rintro rfl; exact qb_wtT_can hmu

end Formalism.InvariantFactorPaths.ColumnFamilies
