import Mathlib

noncomputable def UpperTheory.Reformulated.B.ProjectiveCharts.HomogIdeal :
    {B : Type} → [inst : CommRing B] → {n : ℕ} → Ideal (MvPolynomial (Fin n) B) → Prop :=
    fun {B : Type} [CommRing B] {n : ℕ} (P : Ideal (MvPolynomial (Fin n) B)) ↦
      ∀ (d : ℕ), ∀ f ∈ P, (MvPolynomial.homogeneousComponent d : MvPolynomial (Fin n) B → MvPolynomial (Fin n) B) f ∈ P

noncomputable def UpperTheory.Reformulated.B.ProjectiveCharts.V0 :
    {B : Type} →
      [inst : CommRing B] →
        {M : ℕ} → Finset (Fin M) → Ideal (MvPolynomial (Fin M) B) → Ideal (MvPolynomial (Fin M) B) → ℕ → Prop :=
    fun {B : Type} [CommRing B] {M : ℕ} (W : Finset (Fin M)) (P Q : Ideal (MvPolynomial (Fin M) B)) (n₀ : ℕ) ↦
      ∀ (n : ℕ), n₀ ≤ n → ∀ f ∈ P, f.IsHomogeneous n → (∀ i ∈ W, ∃ (m : ℕ), MvPolynomial.X i ^ m * f ∈ Q) → f ∈ Q

noncomputable def UpperTheory.Reformulated.B.ProjectiveCharts.V1 :
    {B : Type} →
      [inst : CommRing B] →
        {M : ℕ} → Finset (Fin M) → Ideal (MvPolynomial (Fin M) B) → Ideal (MvPolynomial (Fin M) B) → ℕ → Prop :=
    fun {B : Type} [CommRing B] {M : ℕ} (W : Finset (Fin M)) (P Q : Ideal (MvPolynomial (Fin M) B)) (n₀ : ℕ) ↦
      ∀ (n : ℕ),
        n₀ ≤ n →
          ∀ (k : ℕ) (f : Fin M → MvPolynomial (Fin M) B),
            (∀ i ∈ W, f i ∈ P ∧ (f i).IsHomogeneous (n + k)) →
              (∀ i ∈ W,
                  ∀ j ∈ W,
                    ∃ (m : ℕ),
                      (MvPolynomial.X i * MvPolynomial.X j) ^ m *
                          (MvPolynomial.X j ^ k * f i - MvPolynomial.X i ^ k * f j) ∈
                        Q) →
                ∃ g ∈ P, g.IsHomogeneous n ∧ ∀ i ∈ W, ∃ (m : ℕ), MvPolynomial.X i ^ m * (MvPolynomial.X i ^ k * g - f i) ∈ Q

section Helpers
open MvPolynomial

variable {B : Type} [CommRing B] {M : ℕ}

/- English proof (translation)
Proceed by induction on `h using MvPolynomial.induction_on' with`. Consider the case `monomial u c`. Establish `h1 : (monomial u c : MvPolynomial (Fin M) B).IsHomogeneous u.degree` using `isHomogeneous_monomial c rfl`. Rewrite using `[homogeneousComponent_of_mem (hp.mul h1), homogeneousComponent_of_mem h1]`. Distinguish the cases in `hd : d = u.degree`.

Simplify using `[hd]`. Simplify using `[hd]`. Consider the case `add a b ha hb => rw [mul_add, map_add, map_add, mul_add, ha, hb]`.
-/
private theorem comp_mul {p : MvPolynomial (Fin M) B} {e : ℕ} (hp : p.IsHomogeneous e) (d : ℕ)
    (h : MvPolynomial (Fin M) B) :
    homogeneousComponent (e + d) (p * h) = p * homogeneousComponent d h := by
  induction h using MvPolynomial.induction_on' with
  | monomial u c =>
    have h1 : (monomial u c : MvPolynomial (Fin M) B).IsHomogeneous u.degree :=
      isHomogeneous_monomial c rfl
    rw [homogeneousComponent_of_mem (hp.mul h1), homogeneousComponent_of_mem h1]
    by_cases hd : d = u.degree
    · simp [hd]
    · simp [hd]
  | add a b ha hb => rw [mul_add, map_add, map_add, mul_add, ha, hb]

/- English proof (translation)
Take `⟨c, rfl⟩` from `Nat.exists_eq_add_of_le hmk`. Establish `: r ^ (m + c) * f = r ^ c * (r ^ m * f)` using `by ring`. Rewrite using `[this]`. Conclude with `Q.mul_mem_left _ h`.
-/
private theorem pow_mul_mem {R : Type} [CommRing R] {Q : Ideal R} {r f : R} {m k : ℕ}
    (hmk : m ≤ k) (h : r ^ m * f ∈ Q) : r ^ k * f ∈ Q := by
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hmk
  have : r ^ (m + c) * f = r ^ c * (r ^ m * f) := by ring
  rw [this]
  exact Q.mul_mem_left _ h

/- English proof (translation)
Take `⟨s, hs⟩` from `IsNoetherian.noetherian T`. Substitute `hs` using the available equality. Use `choose! m hm using h`. Use `⟨s.sup m, fun f hf => ?_⟩` and prove the remaining obligations. Proceed by induction on `hf using Submodule.span_induction with`.

Consider the case `mem t ht => exact pow_mul_mem (Finset.le_sup ht) (hm t (Submodule.subset_span ht))`. Consider the case `zero => simp`. Consider the case `add a b _ _ ha hb => rw [mul_add]`. Conclude with `Q.add_mem ha hb`. Consider the case `smul a b _ hb`.

Rewrite using `[smul_eq_mul, mul_left_comm]`. Conclude with `Q.mul_mem_left _ hb`.
-/
private theorem unif {R : Type} [CommRing R] [IsNoetherianRing R] (T Q : Ideal R) (r : R)
    (h : ∀ f ∈ T, ∃ m : ℕ, r ^ m * f ∈ Q) : ∃ k : ℕ, ∀ f ∈ T, r ^ k * f ∈ Q := by
  classical
  obtain ⟨s, hs⟩ := IsNoetherian.noetherian T
  subst hs
  choose! m hm using h
  refine ⟨s.sup m, fun f hf => ?_⟩
  induction hf using Submodule.span_induction with
  | mem t ht => exact pow_mul_mem (Finset.le_sup ht) (hm t (Submodule.subset_span ht))
  | zero => simp
  | add a b _ _ ha hb => rw [mul_add]; exact Q.add_mem ha hb
  | smul a b _ hb =>
    rw [smul_eq_mul, mul_left_comm]
    exact Q.mul_mem_left _ hb

/- English proof (translation)
Use `choose k hk using fun i => unif T Q (X i) (h i)`. Take `⟨s, hs⟩` from `IsNoetherian.noetherian T`. Substitute `hs` using the available equality. Use `⟨(∑ i, k i) + s.sup totalDegree + 1, fun n hn f hf => ?_⟩` and prove the remaining obligations. Establish `key : ∀ a, homogeneousComponent n (a * f) ∈ Q`.

Proceed by induction on `hf using Submodule.span_induction with`. Consider the case `mem t ht`. Introduce `a`. Proceed by induction on `a using MvPolynomial.induction_on' with`. Consider the case `monomial u c`.

Distinguish the cases in `hu : ∃ i, k i ≤ u i`. Take `⟨i, hi⟩` from `hu`. Apply `hQ` to reduce the goal to its premises. Establish `h1 : (X i : MvPolynomial (Fin M) B) ^ k i ∣ monomial u c`. Rewrite using `[X_pow_eq_monomial]`.

Use `⟨monomial (u - Finsupp.single i (k i)) c, ?_⟩` and prove the remaining obligations. Rewrite using `[monomial_mul, one_mul, add_tsub_cancel_of_le (Finsupp.single_le_iff.mpr hi)]`. Take `⟨w, hw⟩` from `h1`. Rewrite using `[hw, mul_comm _ w, mul_assoc]`. Conclude with `Q.mul_mem_left _ (hk i t (Submodule.subset_span ht))`.

Use `push Not at hu`. Establish `h1 : (monomial u c : MvPolynomial (Fin M) B).totalDegree ≤ ∑ i, k i`. Use `(totalDegree_monomial_le u c).trans ?_` and prove the remaining obligations. Rewrite using `[Finsupp.sum_fintype _ _ (fun _ => rfl)]`. Conclude with `Finset.sum_le_sum fun i _ => (hu i).le`.

Establish `h2 : t.totalDegree ≤ s.sup totalDegree` using `Finset.le_sup (f := totalDegree) ht`. Establish `h3` using `totalDegree_mul (monomial u c) t`. Rewrite using `[homogeneousComponent_eq_zero _ _ (by omega)]`. Conclude with `Q.zero_mem`. Consider the case `add a b ha hb => rw [add_mul, map_add]`.

Conclude with `Q.add_mem ha hb`. Consider the case `zero => intro a`. Simplify using the standard rewrite rules. Consider the case `add x y _ _ hx hy => intro a`. Rewrite using `[mul_add, map_add]`.

Conclude with `Q.add_mem (hx a) (hy a)`. Consider the case `smul b x _ hx => intro a`. Rewrite using `[smul_eq_mul, ← mul_assoc]`. Conclude with `hx _`. Simplify using `using key 1`.
-/
private theorem comp_mem_of_nilp [IsNoetherianRing B] (T Q : Ideal (MvPolynomial (Fin M) B))
    (hQ : UpperTheory.Reformulated.B.ProjectiveCharts.HomogIdeal Q)
    (h : ∀ i, ∀ f ∈ T, ∃ m : ℕ, X i ^ m * f ∈ Q) :
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → ∀ f ∈ T, homogeneousComponent n f ∈ Q := by
  classical
  choose k hk using fun i => unif T Q (X i) (h i)
  obtain ⟨s, hs⟩ := IsNoetherian.noetherian T
  subst hs
  refine ⟨(∑ i, k i) + s.sup totalDegree + 1, fun n hn f hf => ?_⟩
  have key : ∀ a, homogeneousComponent n (a * f) ∈ Q := by
    induction hf using Submodule.span_induction with
    | mem t ht =>
      intro a
      induction a using MvPolynomial.induction_on' with
      | monomial u c =>
        by_cases hu : ∃ i, k i ≤ u i
        · obtain ⟨i, hi⟩ := hu
          apply hQ
          have h1 : (X i : MvPolynomial (Fin M) B) ^ k i ∣ monomial u c := by
            rw [X_pow_eq_monomial]
            refine ⟨monomial (u - Finsupp.single i (k i)) c, ?_⟩
            rw [monomial_mul, one_mul, add_tsub_cancel_of_le (Finsupp.single_le_iff.mpr hi)]
          obtain ⟨w, hw⟩ := h1
          rw [hw, mul_comm _ w, mul_assoc]
          exact Q.mul_mem_left _ (hk i t (Submodule.subset_span ht))
        · push Not at hu
          have h1 : (monomial u c : MvPolynomial (Fin M) B).totalDegree ≤ ∑ i, k i := by
            refine (totalDegree_monomial_le u c).trans ?_
            rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
            exact Finset.sum_le_sum fun i _ => (hu i).le
          have h2 : t.totalDegree ≤ s.sup totalDegree := Finset.le_sup (f := totalDegree) ht
          have h3 := totalDegree_mul (monomial u c) t
          rw [homogeneousComponent_eq_zero _ _ (by omega)]
          exact Q.zero_mem
      | add a b ha hb => rw [add_mul, map_add]; exact Q.add_mem ha hb
    | zero => intro a; simp
    | add x y _ _ hx hy => intro a; rw [mul_add, map_add]; exact Q.add_mem (hx a) (hy a)
    | smul b x _ hx => intro a; rw [smul_eq_mul, ← mul_assoc]; exact hx _
  simpa using key 1

/- English proof (translation)
Set `T : Ideal (MvPolynomial (Fin M) B)` to `{ carrier := {f | ∀ i, ∃ m : ℕ, X i ^ m * f ∈ Q} zero_mem' := fun i => ⟨0, by simp⟩ add_mem' := by`. Introduce `a b ha hb i`. Take `⟨m, hm⟩` from `ha i`. Take `⟨l, hl⟩` from `hb i`. Use `⟨m + l, ?_⟩` and prove the remaining obligations.

Rewrite using `[mul_add]`. Conclude with `Q.add_mem (pow_mul_mem (by omega) hm) (pow_mul_mem (by omega) hl)`. Use the proof step `smul_mem' := by`. Introduce `c a ha i`. Take `⟨m, hm⟩` from `ha i`.

Use `⟨m, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_eq_mul, mul_left_comm]`. Conclude with `Q.mul_mem_left _ hm }`. Take `⟨n₀, h⟩` from `comp_mem_of_nilp T Q hQ (fun i f hf => hf i)`. Use `⟨n₀, fun n hn f hfP hf hi => ?_⟩` and prove the remaining obligations.

Rewrite using `[← homogeneousComponent_eq_self hf]`. Use `h n hn f (fun i => ?_)` and prove the remaining obligations. Distinguish the cases in `hiW : i ∈ W`. Conclude with `hi i hiW`. Take `⟨k, hk⟩` from `hW i hiW`.

Conclude with `⟨k, hk f hfP⟩`.
-/
private theorem v0 [IsNoetherianRing B] (W : Finset (Fin M))
    (P Q : Ideal (MvPolynomial (Fin M) B)) (hQ : UpperTheory.Reformulated.B.ProjectiveCharts.HomogIdeal Q)
    (hW : ∀ j ∉ W, ∃ k : ℕ, ∀ f ∈ P, X j ^ k * f ∈ Q) :
    ∃ n₀ : ℕ, UpperTheory.Reformulated.B.ProjectiveCharts.V0 W P Q n₀ := by
  let T : Ideal (MvPolynomial (Fin M) B) :=
    { carrier := {f | ∀ i, ∃ m : ℕ, X i ^ m * f ∈ Q}
      zero_mem' := fun i => ⟨0, by simp⟩
      add_mem' := by
        intro a b ha hb i
        obtain ⟨m, hm⟩ := ha i
        obtain ⟨l, hl⟩ := hb i
        refine ⟨m + l, ?_⟩
        rw [mul_add]
        exact Q.add_mem (pow_mul_mem (by omega) hm) (pow_mul_mem (by omega) hl)
      smul_mem' := by
        intro c a ha i
        obtain ⟨m, hm⟩ := ha i
        refine ⟨m, ?_⟩
        rw [smul_eq_mul, mul_left_comm]
        exact Q.mul_mem_left _ hm }
  obtain ⟨n₀, h⟩ := comp_mem_of_nilp T Q hQ (fun i f hf => hf i)
  refine ⟨n₀, fun n hn f hfP hf hi => ?_⟩
  rw [← homogeneousComponent_eq_self hf]
  refine h n hn f (fun i => ?_)
  by_cases hiW : i ∈ W
  · exact hi i hiW
  · obtain ⟨k, hk⟩ := hW i hiW
    exact ⟨k, hk f hfP⟩

private def sat {R : Type} [CommRing R] (P Q : Ideal R) (x : R) : Ideal R where
  carrier := {f | f ∈ P ∧ ∃ m : ℕ, x ^ m * f ∈ Q}
  zero_mem' := ⟨P.zero_mem, 0, by simp⟩
  add_mem' := by
    rintro a b ⟨ha, m, hm⟩ ⟨hb, l, hl⟩
    refine ⟨P.add_mem ha hb, m + l, ?_⟩
    rw [mul_add]
    exact Q.add_mem (pow_mul_mem (by omega) hm) (pow_mul_mem (by omega) hl)
  smul_mem' := by
    rintro c a ⟨ha, m, hm⟩
    refine ⟨P.mul_mem_left _ ha, m, ?_⟩
    rw [smul_eq_mul, mul_left_comm]
    exact Q.mul_mem_left _ hm

private def plus {R : Type} [CommRing R] (P Q : Ideal R) (x : R) : Ideal R where
  carrier := {g | ∃ q ∈ Q, ∃ h ∈ P, g = q + x * h}
  zero_mem' := ⟨0, Q.zero_mem, 0, P.zero_mem, by simp⟩
  add_mem' := by
    rintro _ _ ⟨q, hq, h, hh, rfl⟩ ⟨q', hq', h', hh', rfl⟩
    exact ⟨q + q', Q.add_mem hq hq', h + h', P.add_mem hh hh', by ring⟩
  smul_mem' := by
    rintro c _ ⟨q, hq, h, hh, rfl⟩
    exact ⟨c * q, Q.mul_mem_left _ hq, c * h, P.mul_mem_left _ hh, by rw [smul_eq_mul]; ring⟩

/- English proof (translation)
Introduce and unpack `d f ⟨hf, m, hm⟩`. Use `⟨hP d f hf, m, ?_⟩` and prove the remaining obligations. Rewrite using `[← comp_mul (isHomogeneous_X_pow a m)]`. Conclude with `hQ _ _ hm`.
-/
private theorem sat_homog {P Q : Ideal (MvPolynomial (Fin M) B)}
    (hP : UpperTheory.Reformulated.B.ProjectiveCharts.HomogIdeal P) (hQ : UpperTheory.Reformulated.B.ProjectiveCharts.HomogIdeal Q) (a : Fin M) :
    UpperTheory.Reformulated.B.ProjectiveCharts.HomogIdeal (sat P Q (X a)) := by
  rintro d f ⟨hf, m, hm⟩
  refine ⟨hP d f hf, m, ?_⟩
  rw [← comp_mul (isHomogeneous_X_pow a m)]
  exact hQ _ _ hm

/- English proof (translation)
Introduce and unpack `d _ ⟨q, hq, h, hh, rfl⟩`. Rewrite using `[map_add]`. Break down `d with _ | d` into its components or cases. Use `⟨_, hQ 0 q hq, 0, P.zero_mem, ?_⟩` and prove the remaining obligations. Use `congr 1`.

Rewrite using `[homogeneousComponent_zero, ← constantCoeff_eq]`. Simplify using the standard rewrite rules. Use `⟨_, hQ (d + 1) q hq, _, hP d h hh, ?_⟩` and prove the remaining obligations. Use `congr 1`. Rewrite using `[add_comm d 1]`.

Conclude with `comp_mul (isHomogeneous_X B a) d h`.
-/
private theorem plus_homog {P Q : Ideal (MvPolynomial (Fin M) B)}
    (hP : UpperTheory.Reformulated.B.ProjectiveCharts.HomogIdeal P) (hQ : UpperTheory.Reformulated.B.ProjectiveCharts.HomogIdeal Q) (a : Fin M) :
    UpperTheory.Reformulated.B.ProjectiveCharts.HomogIdeal (plus P Q (X a)) := by
  rintro d _ ⟨q, hq, h, hh, rfl⟩
  rw [map_add]
  rcases d with _ | d
  · refine ⟨_, hQ 0 q hq, 0, P.zero_mem, ?_⟩
    congr 1
    rw [homogeneousComponent_zero, ← constantCoeff_eq]
    simp
  · refine ⟨_, hQ (d + 1) q hq, _, hP d h hh, ?_⟩
    congr 1
    rw [add_comm d 1]
    exact comp_mul (isHomogeneous_X B a) d h

/- English proof (translation)
Establish `step : ∀ l : ℕ, (∃ g ∈ P, g.IsHomogeneous (n + l) ∧ ∀ i ∈ W, ∃ m : ℕ, X i ^ m * (X i ^ k * g - X a ^ l * f i) ∈ sat P Q (X a)) → ∃ g ∈ P, g.IsHomogeneous n ∧ ∀ i ∈ W, ∃ m : ℕ, X i ^ m * (X i ^ k * g - f i) ∈ sat P Q (X a)`. Introduce `l`. Proceed by induction on `l with`. Consider the case `zero => simp`. Consider the case `succ l ih`.

Introduce and unpack `⟨g, hgP, hg, hi⟩`. Apply `ih` to reduce the goal to its premises. Establish `hgR : g ∈ plus P (sat P Q (X a)) (X a)`. Use `h0 (n + (l + 1)) (by omega) g hgP hg (fun i hiW => ?_)` and prove the remaining obligations. Take `⟨m, hm⟩` from `hi i hiW`.

Use `⟨m + k, _, hm, X i ^ m * X a ^ l * f i, P.mul_mem_left _ (hf i hiW).1, by ring⟩` and prove the remaining obligations. Take `⟨q, hq, h, hh, hgq⟩` from `hgR`. Establish `hq'` using `sat_homog hP hQ a (n + (l + 1)) q hq`. Establish `e : g = homogeneousComponent (n + (l + 1)) q + X a * homogeneousComponent (n + l) h`. Rewrite using `[← comp_mul (isHomogeneous_X B a), show 1 + (n + l) = n + (l + 1) by omega, ← map_add, ← hgq, homogeneousComponent_eq_self hg]`.

Establish `hh'` using `hP (n + l) h hh`. Use `⟨_, hh', homogeneousComponent_isHomogeneous _ _, fun i hiW => ?_⟩` and prove the remaining obligations. Take `⟨m, hm⟩` from `hi i hiW`. Generalize the expression as in `homogeneousComponent (n + (l + 1)) q = q' at hq' e`. Generalize the expression as in `homogeneousComponent (n + l) h = h' at hh' e ⊢`.

Take `⟨-, r, hr⟩` from `(sat P Q (X a)).sub_mem hm ((sat P Q (X a)).mul_mem_left (X i ^ m * X i ^ k) hq')`. Use `⟨m, P.mul_mem_left _ (P.sub_mem (P.mul_mem_left _ hh') (P.mul_mem_left _ (hf i hiW).1)), r + 1, ?_⟩` and prove the remaining obligations. Use `hr using 1` and compare the differences between its conclusion and the goal. Rewrite using `[e]`. Expand and normalize the polynomial expressions, which then agree.

Use `step k ⟨f a, (hf a ha).1, (hf a ha).2, fun i hiW => ?_⟩` and prove the remaining obligations. Take `⟨m, hm⟩` from `hc a ha i hiW`. Use `⟨m, P.mul_mem_left _ (P.sub_mem (P.mul_mem_left _ (hf a ha).1) (P.mul_mem_left _ (hf i hiW).1)), m, ?_⟩` and prove the remaining obligations. Use `hm using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem lift_sat {W : Finset (Fin M)} {P Q : Ideal (MvPolynomial (Fin M) B)}
    (hP : UpperTheory.Reformulated.B.ProjectiveCharts.HomogIdeal P) (hQ : UpperTheory.Reformulated.B.ProjectiveCharts.HomogIdeal Q) {a : Fin M}
    (ha : a ∈ W) {n₀ : ℕ}
    (h0 : UpperTheory.Reformulated.B.ProjectiveCharts.V0 W P (plus P (sat P Q (X a)) (X a)) n₀) {n : ℕ} (hn : n₀ ≤ n)
    {k : ℕ} {f : Fin M → MvPolynomial (Fin M) B}
    (hf : ∀ i ∈ W, f i ∈ P ∧ (f i).IsHomogeneous (n + k))
    (hc : ∀ i ∈ W, ∀ j ∈ W, ∃ m : ℕ, (X i * X j) ^ m * (X j ^ k * f i - X i ^ k * f j) ∈ Q) :
    ∃ g ∈ P, g.IsHomogeneous n ∧
      ∀ i ∈ W, ∃ m : ℕ, X i ^ m * (X i ^ k * g - f i) ∈ sat P Q (X a) := by
  have step : ∀ l : ℕ, (∃ g ∈ P, g.IsHomogeneous (n + l) ∧
      ∀ i ∈ W, ∃ m : ℕ, X i ^ m * (X i ^ k * g - X a ^ l * f i) ∈ sat P Q (X a)) →
      ∃ g ∈ P, g.IsHomogeneous n ∧
      ∀ i ∈ W, ∃ m : ℕ, X i ^ m * (X i ^ k * g - f i) ∈ sat P Q (X a) := by
    intro l
    induction l with
    | zero => simp
    | succ l ih =>
      rintro ⟨g, hgP, hg, hi⟩
      apply ih
      have hgR : g ∈ plus P (sat P Q (X a)) (X a) := by
        refine h0 (n + (l + 1)) (by omega) g hgP hg (fun i hiW => ?_)
        obtain ⟨m, hm⟩ := hi i hiW
        refine ⟨m + k, _, hm, X i ^ m * X a ^ l * f i, P.mul_mem_left _ (hf i hiW).1, by ring⟩
      obtain ⟨q, hq, h, hh, hgq⟩ := hgR
      have hq' := sat_homog hP hQ a (n + (l + 1)) q hq
      have e : g = homogeneousComponent (n + (l + 1)) q
          + X a * homogeneousComponent (n + l) h := by
        rw [← comp_mul (isHomogeneous_X B a), show 1 + (n + l) = n + (l + 1) by omega,
          ← map_add, ← hgq, homogeneousComponent_eq_self hg]
      have hh' := hP (n + l) h hh
      refine ⟨_, hh', homogeneousComponent_isHomogeneous _ _, fun i hiW => ?_⟩
      obtain ⟨m, hm⟩ := hi i hiW
      generalize homogeneousComponent (n + (l + 1)) q = q' at hq' e
      generalize homogeneousComponent (n + l) h = h' at hh' e ⊢
      obtain ⟨-, r, hr⟩ := (sat P Q (X a)).sub_mem hm
        ((sat P Q (X a)).mul_mem_left (X i ^ m * X i ^ k) hq')
      refine ⟨m, P.mul_mem_left _ (P.sub_mem (P.mul_mem_left _ hh')
        (P.mul_mem_left _ (hf i hiW).1)), r + 1, ?_⟩
      convert hr using 1
      rw [e]; ring
  refine step k ⟨f a, (hf a ha).1, (hf a ha).2, fun i hiW => ?_⟩
  obtain ⟨m, hm⟩ := hc a ha i hiW
  refine ⟨m, P.mul_mem_left _ (P.sub_mem (P.mul_mem_left _ (hf a ha).1)
        (P.mul_mem_left _ (hf i hiW).1)), m, ?_⟩
  convert hm using 1
  ring

/- English proof (translation)
Proceed by induction on `W using Finset.induction_on with`. Consider the case `empty`. Introduce `P Q _ _ _ _`. Conclude with `⟨0, fun n _ k f _ _ => ⟨0, P.zero_mem, isHomogeneous_zero _ _ _, by simp⟩⟩`. Consider the case `insert a W haW ih`.

Introduce `P Q hP hQ hQP hW`. Establish `hQS : Q ≤ sat P Q (X a)` using `fun f hf => ⟨hQP hf, 0, by simpa using hf⟩`. Take `⟨n₁, h1⟩` from `ih (sat P Q (X a)) Q (sat_homog hP hQ a) hQ hQS (by`. Introduce `j hj`. Distinguish the cases in `hja : j = a`.

Substitute `hja` using the available equality. Conclude with `unif _ _ _ (fun f hf => hf.2)`. Take `⟨k, hk⟩` from `hW j (by simp [hja, hj])`. Conclude with `⟨k, fun f hf => hk f hf.1⟩)`. Take `⟨n₂, h2⟩` from `v0 (insert a W) P (plus P (sat P Q (X a)) (X a)) (plus_homog hP (sat_homog hP hQ a) a) (by`.

Introduce `j hj`. Take `⟨k, hk⟩` from `hW j hj`. Conclude with `⟨k, fun f hf => ⟨_, hQS (hk f hf), 0, P.zero_mem, by simp⟩⟩)`. Use `⟨n₁ + n₂, fun n hn k f hf hc => ?_⟩` and prove the remaining obligations. Take `⟨g₀, hg₀P, hg₀, hi⟩` from `lift_sat hP hQ (Finset.mem_insert_self a W) h2 (n := n) (by omega) hf hc`.

Use `choose! e he using hi`. Choose the witnesses or unpack the hypotheses as in `⟨m, hm⟩ : ∃ m : ℕ, ∀ i ∈ insert a W, X i ^ m * (f i - X i ^ k * g₀) ∈ sat P Q (X a) := by`. Use `⟨(insert a W).sup e, fun i hi => pow_mul_mem (Finset.le_sup hi) ?_⟩` and prove the remaining obligations. Use `(sat P Q (X a)).neg_mem (he i hi) using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree.

Take `⟨g₁, hg₁S, hg₁, hj⟩` from `h1 n (by omega) (k + m) (fun i => X i ^ m * (f i - X i ^ k * g₀)) (by`. Introduce `i hi`. Establish `hi'` using `Finset.mem_insert_of_mem (b := a) hi`. Use `⟨hm i hi', ?_⟩` and prove the remaining obligations. Establish `t1` using `(isHomogeneous_X_pow (R := B) i k).mul hg₀`.

Rewrite `t1` using `[add_comm]`. Establish `t2` using `(isHomogeneous_X_pow (R := B) i m).mul ((hf i hi').2.sub t1)`. Rewrite using `[show m + (n + k) = n + (k + m) by omega] at t2) (by` and apply the resulting hypothesis. Introduce `i hi j hj`. Take `⟨r, hr⟩` from `hc i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj)`.

Use `⟨r, ?_⟩` and prove the remaining obligations. Use `Q.mul_mem_left ((X i * X j) ^ m) hr using 1` and compare the differences between its conclusion and the goal. Use the proof step `ring)`. Use `⟨g₀ + g₁, P.add_mem hg₀P hg₁S.1, hg₀.add hg₁, fun i hi => ?_⟩` and prove the remaining obligations. Establish `: ∃ r : ℕ, X i ^ r * (X i ^ (k + m) * g₁ - X i ^ m * (f i - X i ^ k * g₀)) ∈ Q`.

Break down `Finset.mem_insert.mp hi with rfl | hiW` into its components or cases. Conclude with `((sat P Q (X i)).sub_mem ((sat P Q (X i)).mul_mem_left _ hg₁S) (hm i hi)).2`. Conclude with `hj i hiW`. Take `⟨r, hr⟩` from `this`. Use `⟨r + m, ?_⟩` and prove the remaining obligations.

Use `hr using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem v1 [IsNoetherianRing B] (W : Finset (Fin M)) :
    ∀ (P Q : Ideal (MvPolynomial (Fin M) B)), UpperTheory.Reformulated.B.ProjectiveCharts.HomogIdeal P →
      UpperTheory.Reformulated.B.ProjectiveCharts.HomogIdeal Q → Q ≤ P →
      (∀ j ∉ W, ∃ k : ℕ, ∀ f ∈ P, X j ^ k * f ∈ Q) →
      ∃ n₀ : ℕ, UpperTheory.Reformulated.B.ProjectiveCharts.V1 W P Q n₀ := by
  classical
  induction W using Finset.induction_on with
  | empty =>
    intro P Q _ _ _ _
    exact ⟨0, fun n _ k f _ _ => ⟨0, P.zero_mem, isHomogeneous_zero _ _ _, by simp⟩⟩
  | insert a W haW ih =>
    intro P Q hP hQ hQP hW
    have hQS : Q ≤ sat P Q (X a) := fun f hf => ⟨hQP hf, 0, by simpa using hf⟩
    obtain ⟨n₁, h1⟩ := ih (sat P Q (X a)) Q (sat_homog hP hQ a) hQ hQS (by
      intro j hj
      by_cases hja : j = a
      · subst hja
        exact unif _ _ _ (fun f hf => hf.2)
      · obtain ⟨k, hk⟩ := hW j (by simp [hja, hj])
        exact ⟨k, fun f hf => hk f hf.1⟩)
    obtain ⟨n₂, h2⟩ := v0 (insert a W) P (plus P (sat P Q (X a)) (X a))
      (plus_homog hP (sat_homog hP hQ a) a) (by
      intro j hj
      obtain ⟨k, hk⟩ := hW j hj
      exact ⟨k, fun f hf => ⟨_, hQS (hk f hf), 0, P.zero_mem, by simp⟩⟩)
    refine ⟨n₁ + n₂, fun n hn k f hf hc => ?_⟩
    obtain ⟨g₀, hg₀P, hg₀, hi⟩ :=
      lift_sat hP hQ (Finset.mem_insert_self a W) h2 (n := n) (by omega) hf hc
    choose! e he using hi
    obtain ⟨m, hm⟩ : ∃ m : ℕ, ∀ i ∈ insert a W,
        X i ^ m * (f i - X i ^ k * g₀) ∈ sat P Q (X a) := by
      refine ⟨(insert a W).sup e, fun i hi => pow_mul_mem (Finset.le_sup hi) ?_⟩
      convert (sat P Q (X a)).neg_mem (he i hi) using 1
      ring
    obtain ⟨g₁, hg₁S, hg₁, hj⟩ := h1 n (by omega) (k + m)
      (fun i => X i ^ m * (f i - X i ^ k * g₀)) (by
        intro i hi
        have hi' := Finset.mem_insert_of_mem (b := a) hi
        refine ⟨hm i hi', ?_⟩
        have t1 := (isHomogeneous_X_pow (R := B) i k).mul hg₀
        rw [add_comm] at t1
        have t2 := (isHomogeneous_X_pow (R := B) i m).mul ((hf i hi').2.sub t1)
        rwa [show m + (n + k) = n + (k + m) by omega] at t2) (by
        intro i hi j hj
        obtain ⟨r, hr⟩ := hc i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj)
        refine ⟨r, ?_⟩
        convert Q.mul_mem_left ((X i * X j) ^ m) hr using 1
        ring)
    refine ⟨g₀ + g₁, P.add_mem hg₀P hg₁S.1, hg₀.add hg₁, fun i hi => ?_⟩
    have : ∃ r : ℕ, X i ^ r * (X i ^ (k + m) * g₁ - X i ^ m * (f i - X i ^ k * g₀)) ∈ Q := by
      rcases Finset.mem_insert.mp hi with rfl | hiW
      · exact ((sat P Q (X i)).sub_mem ((sat P Q (X i)).mul_mem_left _ hg₁S) (hm i hi)).2
      · exact hj i hiW
    obtain ⟨r, hr⟩ := this
    refine ⟨r + m, ?_⟩
    convert hr using 1
    ring

end Helpers

/- English proof (translation)
Introduce `B _ M _ W P Q hP hQ hQP hW`. Take `⟨n₀, h0⟩` from `v0 W P Q hQ hW`. Take `⟨n₁, h1⟩` from `v1 W P Q hP hQ hQP hW`. Conclude with `⟨n₀ + n₁, fun n hn => h0 n (by omega), fun n hn => h1 n (by omega)⟩`.
-/
theorem UpperTheory.Reformulated.B.ProjectiveCharts.charts :
    ∀ {B : Type} [inst : CommRing B] {M : ℕ} [IsNoetherianRing B] (W : Finset (Fin M))
      (P Q : Ideal (MvPolynomial (Fin M) B)),
      UpperTheory.Reformulated.B.ProjectiveCharts.HomogIdeal P →
        UpperTheory.Reformulated.B.ProjectiveCharts.HomogIdeal Q →
          Q ≤ P →
            (∀ j ∉ W, ∃ (k : ℕ), ∀ f ∈ P, MvPolynomial.X j ^ k * f ∈ Q) →
              ∃ (n₀ : ℕ), UpperTheory.Reformulated.B.ProjectiveCharts.V0 W P Q n₀ ∧ UpperTheory.Reformulated.B.ProjectiveCharts.V1 W P Q n₀ := by
  intro B _ M _ W P Q hP hQ hQP hW
  obtain ⟨n₀, h0⟩ := v0 W P Q hQ hW
  obtain ⟨n₁, h1⟩ := v1 W P Q hP hQ hQP hW
  exact ⟨n₀ + n₁, fun n hn => h0 n (by omega), fun n hn => h1 n (by omega)⟩
