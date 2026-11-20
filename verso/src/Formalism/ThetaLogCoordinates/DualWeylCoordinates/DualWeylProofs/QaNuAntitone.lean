import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.QaRowStrictMono

noncomputable section

open MvPolynomial Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

def qa_S {n : ℕ} (m : Fin n × Fin n →₀ ℕ) (a p : Fin n) : ℕ := ∑ b : Fin n with b ≤ a, m (b, p)

/- English proof (translation)
Unfold `qa_S`. Apply `Finset.sum_le_sum_of_subset` to reduce the goal to its premises. Introduce `b hb`. Simplify using `only [mem_filter, mem_univ, true_and] at hb ⊢`. Conclude with `hb.trans h`.
-/
lemma qa_S_mono {n : ℕ} (m : Fin n × Fin n →₀ ℕ) (p : Fin n) {a a' : Fin n} (h : a ≤ a') :
    qa_S m a p ≤ qa_S m a' p := by
  unfold qa_S
  apply Finset.sum_le_sum_of_subset
  intro b hb
  simp only [mem_filter, mem_univ, true_and] at hb ⊢
  exact hb.trans h

/- English proof (translation)
Unfold `qa_S`. Conclude with `Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)`.
-/
lemma qa_S_le {n : ℕ} (m : Fin n × Fin n →₀ ℕ) (a p : Fin n) : qa_S m a p ≤ ∑ b : Fin n, m (b, p) := by
  unfold qa_S
  exact Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)

/- English proof (translation)
Unfold `qa_S`. Use `congr 1`. Use extensionality with `b`. Simplify using `only [mem_filter, mem_univ, true_and, iff_true]`. Rewrite using `[Fin.le_def]`.

Use `b.2` as an intermediate fact. Simplify using `only [lastIdx]`. Use linear arithmetic over natural numbers and integers.
-/
lemma qa_S_last {n : ℕ} [NeZero n] (m : Fin n × Fin n →₀ ℕ) (p : Fin n) :
    qa_S m (lastIdx n) p = ∑ b : Fin n, m (b, p) := by
  unfold qa_S
  congr 1
  ext b
  simp only [mem_filter, mem_univ, true_and, iff_true]
  rw [Fin.le_def]
  have := b.2
  simp only [lastIdx]
  omega

/- English proof (translation)
Take `⟨a, ha⟩` from `a`. Consider the cases of `a with`. Consider the case `zero => left`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `b hb`.

Simplify using `only [mem_filter, mem_univ, true_and, Fin.lt_def] at hb`. Use linear arithmetic over natural numbers and integers. Consider the case `succ k => right`. Use `⟨⟨k, by omega⟩, by simp [Fin.lt_def], ?_⟩` and prove the remaining obligations. Unfold `qa_S`.

Use `congr 1`. Use extensionality with `b`. Simplify using `only [mem_filter, mem_univ, true_and, Fin.lt_def, Fin.le_def]`. Use linear arithmetic over natural numbers and integers.
-/
lemma qa_Slt {n : ℕ} (m : Fin n × Fin n →₀ ℕ) (a p : Fin n) :
    (∑ b : Fin n with b < a, m (b, p)) = 0 ∨ ∃ b, b < a ∧ (∑ b : Fin n with b < a, m (b, p)) = qa_S m b p := by
  obtain ⟨a, ha⟩ := a
  cases a with
  | zero =>
    left
    apply Finset.sum_eq_zero
    intro b hb
    simp only [mem_filter, mem_univ, true_and, Fin.lt_def] at hb
    omega
  | succ k =>
    right
    refine ⟨⟨k, by omega⟩, by simp [Fin.lt_def], ?_⟩
    unfold qa_S
    congr 1
    ext b
    simp only [mem_filter, mem_univ, true_and, Fin.lt_def, Fin.le_def]
    omega

/- English proof (translation)
Use extensionality with `⟨a, p⟩`. Establish `hsplit : ∀ (m : Fin n × Fin n →₀ ℕ), qa_S m a p = m (a, p) + ∑ b : Fin n with b < a, m (b, p)`. Introduce `m`. Unfold `qa_S`. Establish `: (univ.filter fun b : Fin n => b ≤ a) = insert a (univ.filter fun b : Fin n => b < a)`.

Use extensionality with `b`. Simplify using `only [mem_filter, mem_univ, true_and, mem_insert]`. Conclude with `le_iff_eq_or_lt`. Rewrite using `[this, Finset.sum_insert (by simp)]`. Establish `h1` using `h a p`.

Rewrite `h1` using `[hsplit m, hsplit m']`. Break down `qa_Slt m a p with h0 | ⟨b, hb, h2⟩` into its components or cases. Break down `qa_Slt m' a p with h0' | ⟨b', hb', h2'⟩` into its components or cases. Use linear arithmetic over natural numbers and integers. Establish `h3 : qa_S m b' p ≤ ∑ b : Fin n with b < a, m (b, p)`.

Unfold `qa_S`. Apply `Finset.sum_le_sum_of_subset` to reduce the goal to its premises. Introduce `x hx`. Simplify using `only [mem_filter, mem_univ, true_and] at hx ⊢`. Conclude with `lt_of_le_of_lt hx hb'`.

Use `h b' p` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `h3 : qa_S m' b p ≤ ∑ b : Fin n with b < a, m' (b, p)`. Unfold `qa_S`. Apply `Finset.sum_le_sum_of_subset` to reduce the goal to its premises.

Introduce `x hx`. Simplify using `only [mem_filter, mem_univ, true_and] at hx ⊢`. Conclude with `lt_of_le_of_lt hx hb`. Break down `qa_Slt m' a p with h0' | ⟨b', hb', h2'⟩` into its components or cases. Use `h b p` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Establish `h4 : qa_S m b' p ≤ ∑ b : Fin n with b < a, m (b, p)`. Unfold `qa_S`. Apply `Finset.sum_le_sum_of_subset` to reduce the goal to its premises. Introduce `x hx`.

Simplify using `only [mem_filter, mem_univ, true_and] at hx ⊢`. Conclude with `lt_of_le_of_lt hx hb'`. Use `h b p` as an intermediate fact. Use `h b' p` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
lemma qa_of_cum {n : ℕ} (m m' : Fin n × Fin n →₀ ℕ) (h : ∀ a p, qa_S m a p = qa_S m' a p) : m = m' := by
  ext ⟨a, p⟩
  have hsplit : ∀ (m : Fin n × Fin n →₀ ℕ), qa_S m a p = m (a, p) + ∑ b : Fin n with b < a, m (b, p) := by
    intro m
    unfold qa_S
    have : (univ.filter fun b : Fin n => b ≤ a) = insert a (univ.filter fun b : Fin n => b < a) := by
      ext b
      simp only [mem_filter, mem_univ, true_and, mem_insert]
      exact le_iff_eq_or_lt
    rw [this, Finset.sum_insert (by simp)]
  have h1 := h a p
  rw [hsplit m, hsplit m'] at h1
  rcases qa_Slt m a p with h0 | ⟨b, hb, h2⟩
  · rcases qa_Slt m' a p with h0' | ⟨b', hb', h2'⟩
    · omega
    ·
      have h3 : qa_S m b' p ≤ ∑ b : Fin n with b < a, m (b, p) := by
        unfold qa_S
        apply Finset.sum_le_sum_of_subset
        intro x hx
        simp only [mem_filter, mem_univ, true_and] at hx ⊢
        exact lt_of_le_of_lt hx hb'
      have := h b' p
      omega
  · have h3 : qa_S m' b p ≤ ∑ b : Fin n with b < a, m' (b, p) := by
      unfold qa_S
      apply Finset.sum_le_sum_of_subset
      intro x hx
      simp only [mem_filter, mem_univ, true_and] at hx ⊢
      exact lt_of_le_of_lt hx hb
    rcases qa_Slt m' a p with h0' | ⟨b', hb', h2'⟩
    · have := h b p
      omega
    · have h4 : qa_S m b' p ≤ ∑ b : Fin n with b < a, m (b, p) := by
        unfold qa_S
        apply Finset.sum_le_sum_of_subset
        intro x hx
        simp only [mem_filter, mem_univ, true_and] at hx ⊢
        exact lt_of_le_of_lt hx hb'
      have := h b p
      have := h b' p
      omega

def qa_g {n : ℕ} [NeZero n] (m : Fin n × Fin n →₀ ℕ) (k : ℤ) (p : Fin n) : Fin n :=
  if h : (univ.filter fun a : Fin n => (qa_S m a p : ℤ) < k).card < n then
    ⟨(univ.filter fun a : Fin n => (qa_S m a p : ℤ) < k).card, h⟩ else lastIdx n

/- English proof (translation)
Establish `hl` using `qa_lower_iff (fun a : Fin n => (qa_S m a p : ℤ) < k) (fun q q' hqq hq => lt_of_le_of_lt (by exact_mod_cast qa_S_mono m p hqq) hq)`. Establish `hn : (univ.filter fun a : Fin n => (qa_S m a p : ℤ) < k).card < n`. Establish `h1` using `hl (lastIdx n)`. Rewrite `h1` using `[qa_S_last]`. Establish `h2 : ¬ (lastIdx n).val < (univ.filter fun a : Fin n => (qa_S m a p : ℤ) < k).card` using `fun hh => absurd (h1.mpr hh) (not_lt.mpr hk)`.

Establish `h3 : (lastIdx n).val = n - 1` using `rfl`. Use `NeZero.pos n` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Unfold `qa_g`. Rewrite using `[dif_pos hn, Fin.le_def]`.

Establish `h1` using `hl a`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Assume the negation of the conclusion as `hc`. Use `h1.mp (not_le.mp hc)` as an intermediate fact.

Simplify using `only at h`. Use linear arithmetic over natural numbers and integers. Introduce `h`. Assume the negation of the conclusion as `hc`. Use `h1.mpr (not_le.mp hc)` as an intermediate fact.

Use linear arithmetic over natural numbers and integers.
-/
lemma qa_g_le_iff {n : ℕ} [NeZero n] (m : Fin n × Fin n →₀ ℕ) (k : ℤ) (p : Fin n)
    (hk : k ≤ (∑ b : Fin n, m (b, p) : ℕ)) (a : Fin n) : qa_g m k p ≤ a ↔ k ≤ qa_S m a p := by
  have hl := qa_lower_iff (fun a : Fin n => (qa_S m a p : ℤ) < k)
    (fun q q' hqq hq => lt_of_le_of_lt (by exact_mod_cast qa_S_mono m p hqq) hq)
  have hn : (univ.filter fun a : Fin n => (qa_S m a p : ℤ) < k).card < n := by
    have h1 := hl (lastIdx n)
    rw [qa_S_last] at h1
    have h2 : ¬ (lastIdx n).val < (univ.filter fun a : Fin n => (qa_S m a p : ℤ) < k).card :=
      fun hh => absurd (h1.mpr hh) (not_lt.mpr hk)
    have h3 : (lastIdx n).val = n - 1 := rfl
    have := NeZero.pos n
    omega
  unfold qa_g
  rw [dif_pos hn, Fin.le_def]
  have h1 := hl a
  constructor
  · intro h
    by_contra hc
    have := h1.mp (not_le.mp hc)
    simp only at h
    omega
  · intro h
    by_contra hc
    have := h1.mpr (not_le.mp hc)
    omega

/- English proof (translation)
Rewrite using `[Fin.le_def]`. Use `p.2` as an intermediate fact. Simplify using `only [lastIdx]`. Use linear arithmetic over natural numbers and integers.
-/
lemma qa_last_le {n : ℕ} [NeZero n] (p : Fin n) : p ≤ lastIdx n := by
  rw [Fin.le_def]
  have := p.2
  simp only [lastIdx]
  omega

/- English proof (translation)
Unfold `qa_nu`. Establish `: mu (lastIdx n) ≤ mu p` using `hmu (qa_last_le p)`. Use linear arithmetic over natural numbers and integers.
-/
lemma qa_nu_cast {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (hmu : Dominant mu) (p : Fin n) :
    (qa_nu mu p : ℤ) = mu p - mu (lastIdx n) := by
  unfold qa_nu
  have : mu (lastIdx n) ≤ mu p := hmu (qa_last_le p)
  omega

/- English proof (translation)
Introduce `p p' h`. Use `hmu h` as an intermediate fact. Unfold `qa_nu`. Use linear arithmetic over natural numbers and integers.
-/
lemma qa_nu_antitone {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (hmu : Dominant mu) : Antitone (qa_nu mu) := by
  intro p p' h
  have := hmu h
  unfold qa_nu
  omega

/- English proof (translation)
Establish `h1 : k ≤ qa_S m (qa_g m k p') p'` using `(qa_g_le_iff m k p' hk' _).mp le_rfl`. Establish `h2 : qa_S m (qa_g m k p') p' ≤ 0 + ∑ b : Fin n with b < qa_g m k p', m (b, p)` using `hint p p' hpp (qa_g m k p')`. Assume the negation of the conclusion as `hc`. Break down `qa_Slt m (qa_g m k p') p with h0 | ⟨b, hb, h3⟩` into its components or cases. Use linear arithmetic over natural numbers and integers.

Establish `h4 : ¬ qa_g m k p ≤ b` using `fun hh => hc (lt_of_le_of_lt hh hb)`. Rewrite `h4` using `[qa_g_le_iff m k p hk]`. Use linear arithmetic over natural numbers and integers.
-/
lemma qa_g_step {n : ℕ} [NeZero n] (m : Fin n × Fin n →₀ ℕ) (hint : Formalism.GradedWeylDivisibility.Interlaced m) (k : ℤ) (hk1 : 1 ≤ k)
    (p p' : Fin n) (hpp : p'.val = p.val + 1) (hk : k ≤ (∑ b : Fin n, m (b, p) : ℕ))
    (hk' : k ≤ (∑ b : Fin n, m (b, p') : ℕ)) : qa_g m k p < qa_g m k p' := by
  have h1 : k ≤ qa_S m (qa_g m k p') p' := (qa_g_le_iff m k p' hk' _).mp le_rfl
  have h2 : qa_S m (qa_g m k p') p' ≤ 0 + ∑ b : Fin n with b < qa_g m k p', m (b, p) :=
    hint p p' hpp (qa_g m k p')
  by_contra hc
  rcases qa_Slt m (qa_g m k p') p with h0 | ⟨b, hb, h3⟩
  · omega
  · have h4 : ¬ qa_g m k p ≤ b := fun hh => hc (lt_of_le_of_lt hh hb)
    rw [qa_g_le_iff m k p hk] at h4
    omega

/- English proof (translation)
Introduce `d`. Proceed by induction on `d with`. Consider the case `zero`. Introduce `p p' hpp hk`. Establish `h1 : ν p' ≤ ν p` using `hν (by rw [Fin.le_def]; omega)`.

Conclude with `qa_g_step m hint k hk1 p p' (by omega) (by rw [hcol]; omega) (by rw [hcol]; exact hk)`. Consider the case `succ d ih`. Introduce `p p' hpp hk`. Establish `hlt : p.val + d + 1 < n` using `by have := p'.2; omega`. Establish `h1 : ν p' ≤ ν ⟨p.val + d + 1, hlt⟩` using `hν (by rw [Fin.le_def]; simp only; omega)`.

Use `(ih p ⟨p.val + d + 1, hlt⟩ rfl (by omega)).trans ?_` and prove the remaining obligations. Conclude with `qa_g_step m hint k hk1 _ p' (by simp only; omega) (by rw [hcol]; omega) (by rw [hcol]; exact hk)`.
-/
lemma qa_g_lt {n : ℕ} [NeZero n] (m : Fin n × Fin n →₀ ℕ) (hint : Formalism.GradedWeylDivisibility.Interlaced m) (ν : Fin n → ℕ)
    (hν : Antitone ν) (hcol : ∀ t, ∑ a : Fin n, m (a, t) = ν t) (k : ℤ) (hk1 : 1 ≤ k) :
    ∀ (d : ℕ) (p p' : Fin n), p'.val = p.val + d + 1 → k ≤ ν p' → qa_g m k p < qa_g m k p' := by
  intro d
  induction d with
  | zero =>
    intro p p' hpp hk
    have h1 : ν p' ≤ ν p := hν (by rw [Fin.le_def]; omega)
    exact qa_g_step m hint k hk1 p p' (by omega) (by rw [hcol]; omega) (by rw [hcol]; exact hk)
  | succ d ih =>
    intro p p' hpp hk
    have hlt : p.val + d + 1 < n := by have := p'.2; omega
    have h1 : ν p' ≤ ν ⟨p.val + d + 1, hlt⟩ := hν (by rw [Fin.le_def]; simp only; omega)
    refine (ih p ⟨p.val + d + 1, hlt⟩ rfl (by omega)).trans ?_
    exact qa_g_step m hint k hk1 _ p' (by simp only; omega) (by rw [hcol]; omega) (by rw [hcol]; exact hk)

/- English proof (translation)
Establish `hf : ∀ c : ↥(TCols mu), StrictMono fun q : Fin (colH mu c) => qa_g m ((c : ℤ) - mu (lastIdx n)) (Fin.castLE (colH_le mu c) q)`. Introduce `c q q' hqq`. Establish `hc` using `Finset.mem_Ioc.mp c.2`. Rewrite `hqq` using `[Fin.lt_def]`. Use `qa_g_lt m hint (qa_nu mu) (qa_nu_antitone hmu) hcol _ (by omega) (q'.val - q.val - 1) _ _ ?_ ?_` and prove the remaining obligations.

Simplify using `only [Fin.val_castLE]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[qa_nu_cast hmu]`. Use `(qa_lt_colH hmu c (Fin.castLE (colH_le mu c) q')).mp q'.2` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Use `⟨fun c => ⟨univ.map ⟨_, (hf c).injective⟩, by simp⟩, fun c q => ?_⟩` and prove the remaining obligations. Use `Finset.orderEmbOfFin_unique (s := univ.map ⟨_, (hf c).injective⟩) (by simp) (f := fun q : Fin (colH mu c) => qa_g m ((c : ℤ) - mu (lastIdx n)) (Fin.castLE (colH_le mu c) q)) (by simp) (hf c)` as an intermediate fact. Conclude with `(congrFun this q).symm`.
-/
lemma qa_fill_exists {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (hmu : Dominant mu) (m : Fin n × Fin n →₀ ℕ)
    (hint : Formalism.GradedWeylDivisibility.Interlaced m) (hcol : ∀ t, ∑ a : Fin n, m (a, t) = qa_nu mu t) :
    ∃ I : TIdx mu, ∀ c q, qa_row I c q = qa_g m ((c : ℤ) - mu (lastIdx n)) (Fin.castLE (colH_le mu c) q) := by
  have hf : ∀ c : ↥(TCols mu), StrictMono fun q : Fin (colH mu c) =>
      qa_g m ((c : ℤ) - mu (lastIdx n)) (Fin.castLE (colH_le mu c) q) := by
    intro c q q' hqq
    have hc := Finset.mem_Ioc.mp c.2
    rw [Fin.lt_def] at hqq
    refine qa_g_lt m hint (qa_nu mu) (qa_nu_antitone hmu) hcol _ (by omega) (q'.val - q.val - 1) _ _ ?_ ?_
    · simp only [Fin.val_castLE]; omega
    · rw [qa_nu_cast hmu]
      have := (qa_lt_colH hmu c (Fin.castLE (colH_le mu c) q')).mp q'.2
      omega
  refine ⟨fun c => ⟨univ.map ⟨_, (hf c).injective⟩, by simp⟩, fun c q => ?_⟩
  have := Finset.orderEmbOfFin_unique (s := univ.map ⟨_, (hf c).injective⟩) (by simp) (f := fun q : Fin (colH mu c) =>
      qa_g m ((c : ℤ) - mu (lastIdx n)) (Fin.castLE (colH_le mu c) q)) (by simp) (hf c)
  exact (congrFun this q).symm

/- English proof (translation)
Establish `hc` using `Finset.mem_Ioc.mp c.2`. Establish `key : ∀ hp : p.val < colH mu c, (p.val < qa_cnt I c a ↔ (c : ℤ) - mu (lastIdx n) ≤ qa_S m a p)`. Introduce `hp`. Establish `h1` using `qa_row_le_iff I c ⟨p.val, hp⟩ a`. Rewrite `h1` using `[hI]`.

Establish `h2 : Fin.castLE (colH_le mu c) ⟨p.val, hp⟩ = p` using `Fin.ext rfl`. Rewrite `h1` using `[h2, qa_g_le_iff]`. Conclude with `h1.symm`. Rewrite using `[hcol, qa_nu_cast hmu]`. Use `(qa_lt_colH hmu c p).mp hp` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Prove the components needed by the constructor for the conclusion. Introduce `h`. Conclude with `(key (h.trans_le (qa_cnt_le I c a))).mp h`. Introduce `h`.

Establish `h1` using `qa_S_le m a p`. Rewrite `h1` using `[hcol]`. Establish `h2` using `qa_nu_cast hmu p`. Establish `hp : p.val < colH mu c` using `(qa_lt_colH hmu c p).mpr (by omega)`. Conclude with `(key hp).mpr h`.
-/
lemma qa_fill_cnt {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (hmu : Dominant mu) (m : Fin n × Fin n →₀ ℕ)
    (hcol : ∀ t, ∑ a : Fin n, m (a, t) = qa_nu mu t) (I : TIdx mu)
    (hI : ∀ c q, qa_row I c q = qa_g m ((c : ℤ) - mu (lastIdx n)) (Fin.castLE (colH_le mu c) q))
    (c : ↥(TCols mu)) (a p : Fin n) :
    p.val < qa_cnt I c a ↔ (c : ℤ) - mu (lastIdx n) ≤ qa_S m a p := by
  have hc := Finset.mem_Ioc.mp c.2
  have key : ∀ hp : p.val < colH mu c, (p.val < qa_cnt I c a ↔ (c : ℤ) - mu (lastIdx n) ≤ qa_S m a p) := by
    intro hp
    have h1 := qa_row_le_iff I c ⟨p.val, hp⟩ a
    rw [hI] at h1
    have h2 : Fin.castLE (colH_le mu c) ⟨p.val, hp⟩ = p := Fin.ext rfl
    rw [h2, qa_g_le_iff] at h1
    · exact h1.symm
    · rw [hcol, qa_nu_cast hmu]
      have := (qa_lt_colH hmu c p).mp hp
      omega
  constructor
  · intro h
    exact (key (h.trans_le (qa_cnt_le I c a))).mp h
  · intro h
    have h1 := qa_S_le m a p
    rw [hcol] at h1
    have h2 := qa_nu_cast hmu p
    have hp : p.val < colH mu c := (qa_lt_colH hmu c p).mpr (by omega)
    exact (key hp).mpr h

/- English proof (translation)
Introduce `c hc a`. Express the relevant statement in the definitionally equal form `qa_cnt I ⟨(c : ℤ) + 1, hc⟩ a ≤ qa_cnt I c a`. Assume the negation of the conclusion as `hlt`. Establish `hlt` using `not_le.mp hlt`. Establish `hn : qa_cnt I c a < n` using `hlt.trans_le ((qa_cnt_le I _ a).trans (colH_le mu _))`.

Establish `h1` using `(qa_fill_cnt hmu m hcol I hI ⟨(c : ℤ) + 1, hc⟩ a ⟨qa_cnt I c a, hn⟩).mp hlt`. Establish `h2` using `(qa_fill_cnt hmu m hcol I hI c a ⟨qa_cnt I c a, hn⟩).mpr (by simp only at h1; omega)`. Conclude with `lt_irrefl _ h2`.
-/
lemma qa_fill_std {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (hmu : Dominant mu) (m : Fin n × Fin n →₀ ℕ)
    (hcol : ∀ t, ∑ a : Fin n, m (a, t) = qa_nu mu t) (I : TIdx mu)
    (hI : ∀ c q, qa_row I c q = qa_g m ((c : ℤ) - mu (lastIdx n)) (Fin.castLE (colH_le mu c) q)) : StdT I := by
  intro c hc a
  change qa_cnt I ⟨(c : ℤ) + 1, hc⟩ a ≤ qa_cnt I c a
  by_contra hlt
  have hlt := not_le.mp hlt
  have hn : qa_cnt I c a < n := hlt.trans_le ((qa_cnt_le I _ a).trans (colH_le mu _))
  have h1 := (qa_fill_cnt hmu m hcol I hI ⟨(c : ℤ) + 1, hc⟩ a ⟨qa_cnt I c a, hn⟩).mp hlt
  have h2 := (qa_fill_cnt hmu m hcol I hI c a ⟨qa_cnt I c a, hn⟩).mpr (by simp only at h1; omega)
  exact lt_irrefl _ h2

/- English proof (translation)
Apply `qa_of_cum` to reduce the goal to its premises. Introduce `a p`. Express the relevant statement in the definitionally equal form `∑ b : Fin n with b ≤ a, qa_exp I (b, p) = qa_S m a p`. Rewrite using `[qa_cum, qa_card_sub]`. Establish `h1` using `qa_S_le m a p`.

Rewrite `h1` using `[hcol]`. Establish `h2` using `qa_nu_cast hmu p`. Establish `h3 : mu p ≤ mu 0` using `hmu (Fin.zero_le p)`. Establish `: ((TCols mu).filter fun d => ∃ h : d ∈ TCols mu, p.val < qa_cnt I ⟨d, h⟩ a) = Finset.Ioc (mu (lastIdx n)) (mu (lastIdx n) + qa_S m a p)`. Use extensionality with `d`.

Simplify using `only [mem_filter, Finset.mem_Ioc]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hd, h, hp⟩`. Use `(qa_fill_cnt hmu m hcol I hI ⟨d, h⟩ a p).mp hp` as an intermediate fact. Establish `hd'` using `Finset.mem_Ioc.mp hd`.

Simplify using `only at this`. Use linear arithmetic over natural numbers and integers. Introduce and unpack `⟨hd1, hd2⟩`. Establish `hd : d ∈ TCols mu` using `Finset.mem_Ioc.mpr ⟨hd1, by omega⟩`. Conclude with `⟨hd, hd, (qa_fill_cnt hmu m hcol I hI ⟨d, hd⟩ a p).mpr (by simp only; omega)⟩`.

Rewrite using `[this, Int.card_Ioc]`. Simplify using the standard rewrite rules.
-/
lemma qa_fill_exp {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (hmu : Dominant mu) (m : Fin n × Fin n →₀ ℕ)
    (hcol : ∀ t, ∑ a : Fin n, m (a, t) = qa_nu mu t) (I : TIdx mu)
    (hI : ∀ c q, qa_row I c q = qa_g m ((c : ℤ) - mu (lastIdx n)) (Fin.castLE (colH_le mu c) q)) :
    qa_exp I = m := by
  classical
  apply qa_of_cum
  intro a p
  change ∑ b : Fin n with b ≤ a, qa_exp I (b, p) = qa_S m a p
  rw [qa_cum, qa_card_sub]
  have h1 := qa_S_le m a p
  rw [hcol] at h1
  have h2 := qa_nu_cast hmu p
  have h3 : mu p ≤ mu 0 := hmu (Fin.zero_le p)
  have : ((TCols mu).filter fun d => ∃ h : d ∈ TCols mu, p.val < qa_cnt I ⟨d, h⟩ a) =
      Finset.Ioc (mu (lastIdx n)) (mu (lastIdx n) + qa_S m a p) := by
    ext d
    simp only [mem_filter, Finset.mem_Ioc]
    constructor
    · rintro ⟨hd, h, hp⟩
      have := (qa_fill_cnt hmu m hcol I hI ⟨d, h⟩ a p).mp hp
      have hd' := Finset.mem_Ioc.mp hd
      simp only at this
      omega
    · rintro ⟨hd1, hd2⟩
      have hd : d ∈ TCols mu := Finset.mem_Ioc.mpr ⟨hd1, by omega⟩
      exact ⟨hd, hd, (qa_fill_cnt hmu m hcol I hI ⟨d, hd⟩ a p).mpr (by simp only; omega)⟩
  rw [this, Int.card_Ioc]
  simp

/- English proof (translation)
Take `⟨I, hI⟩` from `qa_fill_exists hmu m hm.1 hm.2`. Conclude with `⟨I, qa_fill_std hmu m hm.2 I hI, qa_fill_exp hmu m hm.2 I hI⟩`.
-/
theorem qa_exp_surj {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (hmu : Dominant mu) (m : Fin n × Fin n →₀ ℕ)
    (hm : m ∈ Formalism.GradedWeylDivisibility.ssIdx n n (qa_nu mu)) : ∃ I : TIdx mu, StdT I ∧ qa_exp I = m := by
  obtain ⟨I, hI⟩ := qa_fill_exists hmu m hm.1 hm.2
  exact ⟨I, qa_fill_std hmu m hm.2 I hI, qa_fill_exp hmu m hm.2 I hI⟩

end Formalism.InvariantFactorPaths.ColumnFamilies
