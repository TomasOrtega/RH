import Development.AutomorphicArithmetic.ThickFrames.MarkedLow

open Finset UpperTheory.BernoulliSumsFrobeniusOrbits Formalism.G0

section
variable {p : ℕ → ℝ}

/- English proof (translation)
Simplify using `[exP]`.
-/
private theorem ex_empty (f : Finset ℕ → ℝ) : exP p ∅ f = f ∅ := by simp [exP]

/- English proof (translation)
Unfold `exP`. Rewrite using `[Finset.sum_powerset_insert ha, Finset.mul_sum, Finset.mul_sum]`. Use `congr 1`. Use `Finset.sum_congr rfl fun T hT => ?_` and prove the remaining obligations. Establish `haT : a ∉ T` using `fun h => ha (Finset.mem_powerset.1 hT h)`.

Establish `h2 : a ∉ S \ T` using `fun h => ha (Finset.mem_sdiff.1 h).1`. Rewrite using `[Finset.insert_sdiff_of_notMem _ haT, Finset.prod_insert h2]`. Expand and normalize the polynomial expressions, which then agree. Use `Finset.sum_congr rfl fun T hT => ?_` and prove the remaining obligations. Establish `haT : a ∉ T` using `fun h => ha (Finset.mem_powerset.1 hT h)`.

Establish `e : insert a S \ insert a T = S \ T`. Use extensionality with `x`. Simplify using `only [Finset.mem_sdiff, Finset.mem_insert]`. Prove the components needed by the constructor for the conclusion. The claim follows by propositional logic.

Introduce and unpack `⟨h1, h2⟩`. Use `⟨Or.inr h1, ?_⟩` and prove the remaining obligations. Introduce and unpack `(rfl | h)`. Conclude with `ha h1`. Conclude with `h2 h`.

Rewrite using `[Finset.prod_insert haT, e]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem ex_insert {a : ℕ} {S : Finset ℕ} (ha : a ∉ S) (f : Finset ℕ → ℝ) :
    exP p (insert a S) f = (1 - p a) * exP p S f + p a * exP p S (fun T => f (insert a T)) := by
  unfold exP
  rw [Finset.sum_powerset_insert ha, Finset.mul_sum, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun T hT => ?_
    have haT : a ∉ T := fun h => ha (Finset.mem_powerset.1 hT h)
    have h2 : a ∉ S \ T := fun h => ha (Finset.mem_sdiff.1 h).1
    rw [Finset.insert_sdiff_of_notMem _ haT, Finset.prod_insert h2]
    ring
  · refine Finset.sum_congr rfl fun T hT => ?_
    have haT : a ∉ T := fun h => ha (Finset.mem_powerset.1 hT h)
    have e : insert a S \ insert a T = S \ T := by
      ext x
      simp only [Finset.mem_sdiff, Finset.mem_insert]
      constructor
      · tauto
      · rintro ⟨h1, h2⟩
        refine ⟨Or.inr h1, ?_⟩
        rintro (rfl | h)
        · exact ha h1
        · exact h2 h
    rw [Finset.prod_insert haT, e]
    ring

/- English proof (translation)
The claim follows from `Finset.sum_congr rfl fun T hT => by rw [h T (Finset.mem_powerset.1 hT)]`.
-/
private theorem ex_congr {S : Finset ℕ} {f g : Finset ℕ → ℝ} (h : ∀ T ⊆ S, f T = g T) :
    exP p S f = exP p S g :=
  Finset.sum_congr rfl fun T hT => by rw [h T (Finset.mem_powerset.1 hT)]

/- English proof (translation)
Proceed by induction on `S using Finset.induction_on with`. Consider the case `empty => exact ex_empty _`. Consider the case `insert a S ha ih => rw [ex_insert ha, ih]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem ex_const (S : Finset ℕ) (c : ℝ) : exP p S (fun _ => c) = c := by
  induction S using Finset.induction_on with
  | empty => exact ex_empty _
  | insert a S ha ih => rw [ex_insert ha, ih]; ring

/- English proof (translation)
Unfold `exP`. Rewrite using `[← Finset.sum_add_distrib]`. Conclude with `Finset.sum_congr rfl fun T _ => by ring`.
-/
private theorem ex_add (S : Finset ℕ) (f g : Finset ℕ → ℝ) :
    exP p S (fun T => f T + g T) = exP p S f + exP p S g := by
  unfold exP
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun T _ => by ring

/- English proof (translation)
Unfold `exP`. Rewrite using `[Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun T _ => by ring`.
-/
private theorem ex_mul_left (S : Finset ℕ) (c : ℝ) (f : Finset ℕ → ℝ) :
    exP p S (fun T => c * f T) = c * exP p S f := by
  unfold exP
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun T _ => by ring

/- English proof (translation)
Unfold `exP`. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun T _ => by rw [Finset.mul_sum]`.
-/
private theorem ex_sum {ι : Type*} (S : Finset ℕ) (I : Finset ι) (f : ι → Finset ℕ → ℝ) :
    exP p S (fun T => ∑ i ∈ I, f i T) = ∑ i ∈ I, exP p S (f i) := by
  unfold exP
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun T _ => by rw [Finset.mul_sum]

/- English proof (translation)
Use `Finset.sum_le_sum fun T hT => ?_` and prove the remaining obligations. Establish `hT'` using `Finset.mem_powerset.1 hT`. Use `mul_le_mul_of_nonneg_left (h T hT') (mul_nonneg ?_ ?_)` and prove the remaining obligations. Conclude with `Finset.prod_nonneg fun a ha => (hp a (hT' ha)).1`. Conclude with `Finset.prod_nonneg fun a ha => sub_nonneg.2 (hp a (Finset.mem_sdiff.1 ha).1).2`.
-/
private theorem ex_mono {S : Finset ℕ} (hp : ∀ a ∈ S, 0 ≤ p a ∧ p a ≤ 1) {f g : Finset ℕ → ℝ}
    (h : ∀ T ⊆ S, f T ≤ g T) : exP p S f ≤ exP p S g := by
  refine Finset.sum_le_sum fun T hT => ?_
  have hT' := Finset.mem_powerset.1 hT
  refine mul_le_mul_of_nonneg_left (h T hT') (mul_nonneg ?_ ?_)
  · exact Finset.prod_nonneg fun a ha => (hp a (hT' ha)).1
  · exact Finset.prod_nonneg fun a ha => sub_nonneg.2 (hp a (Finset.mem_sdiff.1 ha).1).2

/- English proof (translation)
Proceed by induction on `A using Finset.induction_on generalizing f with`. Consider the case `empty => rw [ex_empty]`. Simplify using the standard rewrite rules. Consider the case `insert a A ha ih`. Rewrite `hAB` using `[Finset.disjoint_insert_left]`.

Establish `: a ∉ A ∪ B` using `by simp [ha, hAB.1]`. Rewrite using `[Finset.insert_union, ex_insert this, ex_insert ha, ih hAB.2, ih hAB.2]`. Simplify using `only [Finset.insert_union]`.
-/
private theorem ex_union {A B : Finset ℕ} (hAB : Disjoint A B) (f : Finset ℕ → ℝ) :
    exP p (A ∪ B) f = exP p A (fun T => exP p B (fun U => f (T ∪ U))) := by
  induction A using Finset.induction_on generalizing f with
  | empty => rw [ex_empty]; simp
  | insert a A ha ih =>
    rw [Finset.disjoint_insert_left] at hAB
    have : a ∉ A ∪ B := by simp [ha, hAB.1]
    rw [Finset.insert_union, ex_insert this, ex_insert ha, ih hAB.2, ih hAB.2]
    simp only [Finset.insert_union]

/- English proof (translation)
Use `conv_lhs => rw [← Finset.union_sdiff_of_subset hA]`. Rewrite using `[ex_union Finset.disjoint_sdiff, mul_comm, ← ex_mul_left]`. Use `ex_congr fun T hT => ?_` and prove the remaining obligations. Rewrite using `[mul_comm, ← ex_mul_left]`. Use `ex_congr fun U hU => ?_` and prove the remaining obligations.

Establish `e1 : (T ∪ U) ∩ A = T`. Use extensionality with `x`. Use `@hT x` as an intermediate fact. Use `@hU x` as an intermediate fact. Simplify using `only [Finset.mem_inter, Finset.mem_union, Finset.mem_sdiff] at *`.

The claim follows by propositional logic. Establish `e2 : (T ∪ U) \ A = U`. Use extensionality with `x`. Use `@hT x` as an intermediate fact. Use `@hU x` as an intermediate fact.

Simplify using `only [Finset.mem_union, Finset.mem_sdiff] at *`. The claim follows by propositional logic. Rewrite using `[e1, e2]`.
-/
private theorem ex_split {A S : Finset ℕ} (hA : A ⊆ S) (f g : Finset ℕ → ℝ) :
    exP p S (fun T => f (T ∩ A) * g (T \ A)) = exP p A f * exP p (S \ A) g := by
  conv_lhs => rw [← Finset.union_sdiff_of_subset hA]
  rw [ex_union Finset.disjoint_sdiff, mul_comm, ← ex_mul_left]
  refine ex_congr fun T hT => ?_
  rw [mul_comm, ← ex_mul_left]
  refine ex_congr fun U hU => ?_
  have e1 : (T ∪ U) ∩ A = T := by
    ext x
    have := @hT x
    have := @hU x
    simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_sdiff] at *
    tauto
  have e2 : (T ∪ U) \ A = U := by
    ext x
    have := @hT x
    have := @hU x
    simp only [Finset.mem_union, Finset.mem_sdiff] at *
    tauto
  rw [e1, e2]

/- English proof (translation)
Use `ex_split (p := p) hA f (fun _ => 1)` as an intermediate fact. Simplify `this` using `[ex_const]`.
-/
private theorem ex_restrict {A S : Finset ℕ} (hA : A ⊆ S) (f : Finset ℕ → ℝ) :
    exP p S (fun T => f (T ∩ A)) = exP p A f := by
  have := ex_split (p := p) hA f (fun _ => 1)
  simpa [ex_const] using this

/- English proof (translation)
Proceed by induction on `J using Finset.induction_on generalizing S with`. Consider the case `empty => simp [ex_const]`. Consider the case `insert a J ha ih`. Establish `hda : ∀ j ∈ J, Disjoint (A a) (A j)` using `fun j hj => hd a (Finset.mem_insert_self _ _) j (Finset.mem_insert_of_mem hj) (fun h => ha (h ▸ hj))`. Rewrite using `[Finset.prod_insert ha, ← ih (fun i hi j hj => hd i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj)) (S \ A a) (fun j hj => Finset.subset_sdiff.2 ⟨hS j (Finset.mem_insert_of_mem hj), (hda j hj).symm⟩), ← ex_split (hS a (Finset.mem_insert_self _ _))]`.

Use `ex_congr fun T _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.prod_insert ha]`. Use `congr 1`. Use `Finset.prod_congr rfl fun j hj => ?_` and prove the remaining obligations. Use `congr 1`.

Use extensionality with `x`. Establish `: x ∈ A a → x ∉ A j` using `fun h => Finset.disjoint_left.1 (hda j hj) h`. Simplify using `only [Finset.mem_inter, Finset.mem_sdiff]`. The claim follows by propositional logic.
-/
private theorem ex_prod {ι : Type*} (J : Finset ι) (A : ι → Finset ℕ) (g : ι → Finset ℕ → ℝ)
    (hd : ∀ i ∈ J, ∀ j ∈ J, i ≠ j → Disjoint (A i) (A j)) (S : Finset ℕ)
    (hS : ∀ j ∈ J, A j ⊆ S) :
    exP p S (fun T => ∏ j ∈ J, g j (T ∩ A j)) = ∏ j ∈ J, exP p (A j) (g j) := by
  classical
  induction J using Finset.induction_on generalizing S with
  | empty => simp [ex_const]
  | insert a J ha ih =>
    have hda : ∀ j ∈ J, Disjoint (A a) (A j) := fun j hj =>
      hd a (Finset.mem_insert_self _ _) j (Finset.mem_insert_of_mem hj) (fun h => ha (h ▸ hj))
    rw [Finset.prod_insert ha,
      ← ih (fun i hi j hj => hd i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj))
        (S \ A a) (fun j hj => Finset.subset_sdiff.2
          ⟨hS j (Finset.mem_insert_of_mem hj), (hda j hj).symm⟩),
      ← ex_split (hS a (Finset.mem_insert_self _ _))]
    refine ex_congr fun T _ => ?_
    rw [Finset.prod_insert ha]
    congr 1
    refine Finset.prod_congr rfl fun j hj => ?_
    congr 1
    ext x
    have : x ∈ A a → x ∉ A j := fun h => Finset.disjoint_left.1 (hda j hj) h
    simp only [Finset.mem_inter, Finset.mem_sdiff]
    tauto

end

/- English proof (translation)
Introduce `p`. Conclude with `⟨ex_const, ex_add, fun S I f => ex_sum S I f, fun _ _ _ hp h => ex_mono hp h, fun _ _ f ha => ex_insert ha f, fun _ _ f hA => ex_restrict hA f, fun J A g S hd hS => ex_prod J A g hd S hS⟩`.
-/
theorem UpperTheory.BernoulliSumsFrobeniusOrbits.expectation_spec :
    ∀ (p : ℕ → ℝ),
      (∀ (S : Finset ℕ) (c : ℝ), exP p S (fun _ => c) = c) ∧
      (∀ (S : Finset ℕ) (f g : Finset ℕ → ℝ), exP p S (fun T => f T + g T) = exP p S f + exP p S g) ∧
      (∀ (S : Finset ℕ) (I : Finset ℕ) (f : ℕ → Finset ℕ → ℝ), exP p S (fun T => ∑ i ∈ I, f i T) = ∑ i ∈ I, exP p S (f i)) ∧
      (∀ (S : Finset ℕ) (f g : Finset ℕ → ℝ), (∀ a ∈ S, 0 ≤ p a ∧ p a ≤ 1) → (∀ T ⊆ S, f T ≤ g T) → exP p S f ≤ exP p S g) ∧
      (∀ (a : ℕ) (S : Finset ℕ) (f : Finset ℕ → ℝ), a ∉ S →
        exP p (insert a S) f = (1 - p a) * exP p S f + p a * exP p S (fun T => f (insert a T))) ∧
      (∀ (A S : Finset ℕ) (f : Finset ℕ → ℝ), A ⊆ S → exP p S (fun T => f (T ∩ A)) = exP p A f) ∧
      (∀ (J : Finset ℕ) (A : ℕ → Finset ℕ) (g : ℕ → Finset ℕ → ℝ) (S : Finset ℕ),
        (∀ i ∈ J, ∀ j ∈ J, i ≠ j → Disjoint (A i) (A j)) → (∀ j ∈ J, A j ⊆ S) →
        exP p S (fun T => ∏ j ∈ J, g j (T ∩ A j)) = ∏ j ∈ J, exP p (A j) (g j)) := by
  intro p
  exact ⟨ex_const, ex_add, fun S I f => ex_sum S I f, fun _ _ _ hp h => ex_mono hp h,
    fun _ _ f ha => ex_insert ha f, fun _ _ f hA => ex_restrict hA f,
    fun J A g S hd hS => ex_prod J A g hd S hS⟩
