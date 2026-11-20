import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LieLatticeData
open GlobalTheory.CompanionTheory.Ar.Num

namespace PositivityTheory.Xgn.A_powspan

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

/- English proof (translation)
The claim follows from `AddSubgroup.subset_closure ⟨a, ha, e, he, rfl⟩`.
-/
theorem mul_mem_gen (R : Subalgebra o Ω) (S : Set Ω) {a e : Ω} (ha : a ∈ R) (he : e ∈ S) :
    a * e ∈ spanOver R S :=
  AddSubgroup.subset_closure ⟨a, ha, e, he, rfl⟩

/- English proof (translation)
Proceed by induction on `hv using AddSubgroup.closure_induction with`. Consider the case `mem x hx`. Take `⟨a', ha', e, he, rfl⟩` from `hx`. Rewrite using `[smul_eq_mul, ← mul_assoc]`. Conclude with `mul_mem_gen R S (R.mul_mem ha ha') he`.

Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => rw [mul_add]`. Conclude with `add_mem hx hy`. Consider the case `neg x _ hx => rw [mul_neg]`. Conclude with `neg_mem hx`.
-/
theorem span_stable (R : Subalgebra o Ω) (S : Set Ω) {a : Ω} (ha : a ∈ R) {v : Ω}
    (hv : v ∈ spanOver R S) : a * v ∈ spanOver R S := by
  induction hv using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a', ha', e, he, rfl⟩ := hx
    rw [smul_eq_mul, ← mul_assoc]
    exact mul_mem_gen R S (R.mul_mem ha ha') he
  | zero => simp
  | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
  | neg x _ hx => rw [mul_neg]; exact neg_mem hx

/- English proof (translation)
Use `(AddSubgroup.closure_le _).2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨a, ha, e, he, rfl⟩`. Conclude with `hT a ha e (hS e he)`.
-/
theorem span_le (R : Subalgebra o Ω) (S : Set Ω) (T : AddSubgroup Ω)
    (hT : ∀ a ∈ R, ∀ v ∈ T, a * v ∈ T) (hS : ∀ e ∈ S, e ∈ T) : spanOver R S ≤ T := by
  refine (AddSubgroup.closure_le _).2 ?_
  rintro _ ⟨a, ha, e, he, rfl⟩
  exact hT a ha e (hS e he)

/- English proof (translation)
Proceed by induction on `hv using AddSubgroup.closure_induction with`. Consider the case `mem x hx`. Take `⟨a, ha, e, he, rfl⟩` from `hx`. Take `⟨n, hn⟩` from `hS e he`. Use `⟨n, ?_⟩` and prove the remaining obligations.

Establish `: f ^ n * (a • e / b) = a * (f ^ n * (e / b))` using `by rw [smul_eq_mul]; ring`. Rewrite using `[this]`. Conclude with `R.mul_mem ha hn`. Consider the case `zero => exact ⟨0, by simp⟩`. Consider the case `add x y _ _ hx hy`.

Take `⟨n, hn⟩` from `hx`. Take `⟨m, hm⟩` from `hy`. Use `⟨n + m, ?_⟩` and prove the remaining obligations. Establish `: f ^ (n + m) * ((x + y) / b) = f ^ m * (f ^ n * (x / b)) + f ^ n * (f ^ m * (y / b))`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[this]`. Conclude with `R.add_mem (R.mul_mem (R.pow_mem hf m) hn) (R.mul_mem (R.pow_mem hf n) hm)`. Consider the case `neg x _ hx`. Take `⟨n, hn⟩` from `hx`. Use `⟨n, ?_⟩` and prove the remaining obligations.

Establish `: f ^ n * (-x / b) = -(f ^ n * (x / b))` using `by ring`. Rewrite using `[this]`. Conclude with `R.neg_mem hn`.
-/
theorem span_loc (R : Subalgebra o Ω) (S : Set Ω) {f : Ω} (hf : f ∈ R) (b : Ω)
    (hS : ∀ e ∈ S, ∃ n : ℕ, f ^ n * (e / b) ∈ R) {v : Ω} (hv : v ∈ spanOver R S) :
    ∃ n : ℕ, f ^ n * (v / b) ∈ R := by
  induction hv using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a, ha, e, he, rfl⟩ := hx
    obtain ⟨n, hn⟩ := hS e he
    refine ⟨n, ?_⟩
    have : f ^ n * (a • e / b) = a * (f ^ n * (e / b)) := by rw [smul_eq_mul]; ring
    rw [this]; exact R.mul_mem ha hn
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨n, hn⟩ := hx
    obtain ⟨m, hm⟩ := hy
    refine ⟨n + m, ?_⟩
    have : f ^ (n + m) * ((x + y) / b) = f ^ m * (f ^ n * (x / b)) + f ^ n * (f ^ m * (y / b)) := by
      ring
    rw [this]
    exact R.add_mem (R.mul_mem (R.pow_mem hf m) hn) (R.mul_mem (R.pow_mem hf n) hm)
  | neg x _ hx =>
    obtain ⟨n, hn⟩ := hx
    refine ⟨n, ?_⟩
    have : f ^ n * (-x / b) = -(f ^ n * (x / b)) := by ring
    rw [this]; exact R.neg_mem hn

/- English proof (translation)
Set `I : Ideal R` to `{ carrier := {r | (r : Ω) * w ∈ T} add_mem' := fun {x y} hx hy => by`. Express the relevant statement in the definitionally equal form `((x + y : R) : Ω) * w ∈ T`. Rewrite using `[Subalgebra.coe_add, add_mul]`. Conclude with `add_mem hx hy`. Use the proof step `zero_mem' := by`.

Express the relevant statement in the definitionally equal form `((0 : R) : Ω) * w ∈ T`. Simplify using the standard rewrite rules. Use the proof step `smul_mem' := fun r x hx => by`. Express the relevant statement in the definitionally equal form `((r * x : R) : Ω) * w ∈ T`. Rewrite using `[Subalgebra.coe_mul, mul_assoc]`.

Conclude with `hT r r.2 _ hx }`. Establish `h1 : (1 : R) ∈ I.radical`. Establish `: (1 : R) = ∑ l, (⟨c l, hc l⟩ : R) * ⟨f l, hf l⟩`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `[hs]`.

Rewrite using `[this]`. Use `Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ ?_` and prove the remaining obligations. Take `⟨n, hn⟩` from `hw l`. Conclude with `⟨n, by`. Express the relevant statement in the definitionally equal form `(((⟨f l, hf l⟩ : R) ^ n : R) : Ω) * w ∈ T`.

Simplify using `using hn⟩`. Take `⟨n, hn⟩` from `h1`. Rewrite `hn` using `[one_pow]`. Establish `: ((1 : R) : Ω) * w ∈ T` using `hn`. Simplify using `using this`.
-/
theorem mem_of_loc (R : Subalgebra o Ω) (T : AddSubgroup Ω) (hT : ∀ a ∈ R, ∀ v ∈ T, a * v ∈ T)
    {k : ℕ} (f c : Fin k → Ω) (hf : ∀ l, f l ∈ R) (hc : ∀ l, c l ∈ R) (hs : ∑ l, c l * f l = 1)
    {w : Ω} (hw : ∀ l, ∃ n : ℕ, f l ^ n * w ∈ T) : w ∈ T := by
  let I : Ideal R :=
    { carrier := {r | (r : Ω) * w ∈ T}
      add_mem' := fun {x y} hx hy => by
        change ((x + y : R) : Ω) * w ∈ T
        rw [Subalgebra.coe_add, add_mul]; exact add_mem hx hy
      zero_mem' := by
        change ((0 : R) : Ω) * w ∈ T
        simp
      smul_mem' := fun r x hx => by
        change ((r * x : R) : Ω) * w ∈ T
        rw [Subalgebra.coe_mul, mul_assoc]; exact hT r r.2 _ hx }
  have h1 : (1 : R) ∈ I.radical := by
    have : (1 : R) = ∑ l, (⟨c l, hc l⟩ : R) * ⟨f l, hf l⟩ := by
      apply Subtype.ext
      simp [hs]
    rw [this]
    refine Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ ?_
    obtain ⟨n, hn⟩ := hw l
    exact ⟨n, by
      change (((⟨f l, hf l⟩ : R) ^ n : R) : Ω) * w ∈ T
      simpa using hn⟩
  obtain ⟨n, hn⟩ := h1
  rw [one_pow] at hn
  have : ((1 : R) : Ω) * w ∈ T := hn
  simpa using this

/- English proof (translation)
Take `⟨b, hb, -, h⟩` from `h`. Establish `hb0 : b 0 ≠ 0` using `hb.ne_zero 0`. Use `⟨b 0, hb0, ?_, fun x hx => ?_⟩` and prove the remaining obligations. Conclude with `(h (b 0)).2 ⟨fun _ => 1, fun _ => ⟨0, by simpa using R.one_mem⟩, by simp⟩`. Take `⟨a, ha, hx'⟩` from `(h x).1 ⟨0, by simpa using hx⟩`.

Take `⟨n, hn⟩` from `ha 0`. Use `⟨n, ?_⟩` and prove the remaining obligations. Establish `: x / b 0 = a 0`. Rewrite using `[hx']`. Simplify using `[hb0]`.

Rewrite using `[this]` and apply the resulting hypothesis.
-/
theorem unpack (R : Subalgebra o Ω) (X : AddSubgroup Ω) (f : Ω)
    (h : ∃ b : Fin 1 → Ω, LinearIndependent Ω b ∧ Submodule.span Ω (Set.range b) = ⊤ ∧
      ∀ e, (∃ n : ℕ, f ^ n • e ∈ X) ↔
        ∃ a : Fin 1 → Ω, (∀ q, ∃ n : ℕ, f ^ n * a q ∈ R) ∧ e = ∑ q, a q • b q) :
    ∃ b : Ω, b ≠ 0 ∧ (∃ m : ℕ, f ^ m * b ∈ X) ∧ ∀ x ∈ X, ∃ n : ℕ, f ^ n * (x / b) ∈ R := by
  obtain ⟨b, hb, -, h⟩ := h
  have hb0 : b 0 ≠ 0 := hb.ne_zero 0
  refine ⟨b 0, hb0, ?_, fun x hx => ?_⟩
  · exact (h (b 0)).2 ⟨fun _ => 1, fun _ => ⟨0, by simpa using R.one_mem⟩, by simp⟩
  · obtain ⟨a, ha, hx'⟩ := (h x).1 ⟨0, by simpa using hx⟩
    obtain ⟨n, hn⟩ := ha 0
    refine ⟨n, ?_⟩
    have : x / b 0 = a 0 := by
      rw [hx']; simp [hb0]
    rwa [this]

/- English proof (translation)
Take `⟨-, k, f, c, hf, hc, hs, hl⟩` from `hX`. Use `⟨fun a ha e he => span_stable R _ ha he, k, f, c, hf, hc, hs, fun l => ?_⟩` and prove the remaining obligations. Take `⟨b, hb, ⟨m, hm⟩, hx⟩` from `unpack R X (f l) (hl l)`. Establish `hbp : b ^ p ≠ 0` using `pow_ne_zero p hb`. Use `⟨fun _ => b ^ p, ?_, ?_, fun e => ⟨?_, ?_⟩⟩` and prove the remaining obligations.

Conclude with `linearIndependent_unique_iff.2 hbp`. Rewrite using `[eq_top_iff]`. Introduce `v _`. Establish `: v = (v / b ^ p) • b ^ p` using `by simp [hbp]`. Rewrite using `[this]`.

Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩)`. Introduce and unpack `⟨n, hn⟩`. Take `⟨n', hn'⟩` from `span_loc R _ (hf l) (b ^ p) (by`. Introduce and unpack `_ ⟨x, hx', rfl⟩`. Take `⟨j, hj⟩` from `hx x hx'`.

Use `⟨j * p, ?_⟩` and prove the remaining obligations. Use `R.pow_mem hj p` as an intermediate fact. Rewrite using `[mul_pow, ← pow_mul, div_pow] at this) hn` and apply the resulting hypothesis. Use `⟨fun _ => e / b ^ p, fun _ => ⟨n' + n, ?_⟩, by simp [hbp]⟩` and prove the remaining obligations. Establish `: f l ^ (n' + n) * (e / b ^ p) = f l ^ n' * (f l ^ n • e / b ^ p)`.

Rewrite using `[smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]` and apply the resulting hypothesis. Introduce and unpack `⟨a, ha, rfl⟩`. Take `⟨n, hn⟩` from `ha 0`.

Use `⟨n + m * p, ?_⟩` and prove the remaining obligations. Establish `: f l ^ (n + m * p) • (∑ q : Fin 1, a q • b ^ p) = (f l ^ n * a 0) * (f l ^ m * b) ^ p`. Simplify using `only [Fin.sum_univ_one, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`.

Conclude with `mul_mem_gen R _ hn ⟨_, hm, rfl⟩`.
-/
theorem locFree_pow (R : Subalgebra o Ω) (p : ℕ) (X : AddSubgroup Ω) (hX : LocFree R 1 X) :
    LocFree R 1 (powSpan R p X) := by
  obtain ⟨-, k, f, c, hf, hc, hs, hl⟩ := hX
  refine ⟨fun a ha e he => span_stable R _ ha he, k, f, c, hf, hc, hs, fun l => ?_⟩
  obtain ⟨b, hb, ⟨m, hm⟩, hx⟩ := unpack R X (f l) (hl l)
  have hbp : b ^ p ≠ 0 := pow_ne_zero p hb
  refine ⟨fun _ => b ^ p, ?_, ?_, fun e => ⟨?_, ?_⟩⟩
  · exact linearIndependent_unique_iff.2 hbp
  · rw [eq_top_iff]
    intro v _
    have : v = (v / b ^ p) • b ^ p := by simp [hbp]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩)
  · rintro ⟨n, hn⟩
    obtain ⟨n', hn'⟩ := span_loc R _ (hf l) (b ^ p) (by
      rintro _ ⟨x, hx', rfl⟩
      obtain ⟨j, hj⟩ := hx x hx'
      refine ⟨j * p, ?_⟩
      have := R.pow_mem hj p
      rwa [mul_pow, ← pow_mul, div_pow] at this) hn
    refine ⟨fun _ => e / b ^ p, fun _ => ⟨n' + n, ?_⟩, by simp [hbp]⟩
    have : f l ^ (n' + n) * (e / b ^ p) = f l ^ n' * (f l ^ n • e / b ^ p) := by
      rw [smul_eq_mul]; ring
    rwa [this]
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨n, hn⟩ := ha 0
    refine ⟨n + m * p, ?_⟩
    have : f l ^ (n + m * p) • (∑ q : Fin 1, a q • b ^ p) = (f l ^ n * a 0) * (f l ^ m * b) ^ p := by
      simp only [Fin.sum_univ_one, smul_eq_mul]; ring
    rw [this]
    exact mul_mem_gen R _ hn ⟨_, hm, rfl⟩

end PositivityTheory.Xgn.A_powspan

open PositivityTheory.Xgn.A_powspan in
/- English proof (translation)
Introduce `o Ω C _ _ _ _ _ _ _ R RC hR p X hX`. Use `⟨locFree_pow R p X hX, le_antisymm ?_ ?_⟩` and prove the remaining obligations. Take `⟨-, k, f, c, hf, hc, hs, hl⟩` from `hX`. Use `span_le RC _ _ (fun a ha v hv => span_stable RC _ ha hv) ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨z, hz, rfl⟩`.

Use `mem_of_loc RC _ (fun a ha v hv => span_stable RC _ ha hv) (fun l => algebraMap Ω C (f l)) (fun l => algebraMap Ω C (c l)) (fun l => hR _ (hf l)) (fun l => hR _ (hc l)) ?_ fun l => ?_` and prove the remaining obligations. Use `congrArg (algebraMap Ω C) hs` as an intermediate fact. Simplify `this` using `[map_sum]`. Take `⟨b, hb, ⟨m, hm⟩, hx⟩` from `unpack R X (f l) (hl l)`. Establish `hb' : algebraMap Ω C b ≠ 0` using `by simpa using hb`.

Take `⟨n, hn⟩` from `span_loc RC _ (hR _ (hf l)) (algebraMap Ω C b) (by`. Introduce and unpack `_ ⟨x, hx', rfl⟩`. Take `⟨j, hj⟩` from `hx x hx'`. Conclude with `⟨j, by simpa using hR _ hj⟩) hz`. Use `⟨(n + m) * p, ?_⟩` and prove the remaining obligations.

Establish `: algebraMap Ω C (f l) ^ ((n + m) * p) * z ^ p = (algebraMap Ω C (f l) ^ n * (z / algebraMap Ω C b)) ^ p * algebraMap Ω C (1 * (f l ^ m * b) ^ p)`. Rewrite using `[one_mul, map_pow, map_mul, map_pow, ← mul_pow, pow_mul, ← mul_pow]`. Use `congr 1`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.

Use `beta_reduce`. Rewrite using `[this]`. Conclude with `mul_mem_gen RC _ (RC.pow_mem hn p) ⟨_, mul_mem_gen R _ R.one_mem ⟨_, hm, rfl⟩, rfl⟩`. Use `span_le RC _ _ (fun a ha v hv => span_stable RC _ ha hv) ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨y, hy, rfl⟩`.

Establish `: powSpan R p X ≤ (powSpan RC p (spanOver RC (algebraMap Ω C '' X))).comap (algebraMap Ω C).toAddMonoidHom`. Use `span_le R _ _ (fun a ha v hv => ?_) ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `algebraMap Ω C (a * v) ∈ powSpan RC p _`. Rewrite using `[map_mul]`. Conclude with `span_stable RC _ (hR a ha) hv`.

Introduce and unpack `_ ⟨x, hx, rfl⟩`. Express the relevant statement in the definitionally equal form `algebraMap Ω C (x ^ p) ∈ powSpan RC p _`. Establish `h1 : algebraMap Ω C (x ^ p) = 1 * (1 * algebraMap Ω C x) ^ p` using `by simp`. Rewrite using `[h1]`. Conclude with `mul_mem_gen RC _ RC.one_mem ⟨_, mul_mem_gen RC _ RC.one_mem ⟨x, hx, rfl⟩, rfl⟩`.

Conclude with `this hy`.
-/
theorem PositivityTheory.Xgn.t_powspan : ∀ {o Ω C : Type} [CommRing o] [Field Ω] [Field C] [Algebra o Ω] [Algebra o C] [Algebra Ω C] [IsScalarTower o Ω C] (R : Subalgebra o Ω) (RC : Subalgebra o C), (∀ a ∈ R, algebraMap Ω C a ∈ RC) → ∀ (p : ℕ) (X : AddSubgroup Ω), LocFree R 1 X → LocFree R 1 (powSpan R p X) ∧ powSpan RC p (spanOver RC (algebraMap Ω C '' X)) = spanOver RC (algebraMap Ω C '' powSpan R p X) := by
  intro o Ω C _ _ _ _ _ _ _ R RC hR p X hX
  refine ⟨locFree_pow R p X hX, le_antisymm ?_ ?_⟩
  · obtain ⟨-, k, f, c, hf, hc, hs, hl⟩ := hX
    refine span_le RC _ _ (fun a ha v hv => span_stable RC _ ha hv) ?_
    rintro _ ⟨z, hz, rfl⟩
    refine mem_of_loc RC _ (fun a ha v hv => span_stable RC _ ha hv)
      (fun l => algebraMap Ω C (f l)) (fun l => algebraMap Ω C (c l)) (fun l => hR _ (hf l))
      (fun l => hR _ (hc l)) ?_ fun l => ?_
    · have := congrArg (algebraMap Ω C) hs
      simpa [map_sum] using this
    · obtain ⟨b, hb, ⟨m, hm⟩, hx⟩ := unpack R X (f l) (hl l)
      have hb' : algebraMap Ω C b ≠ 0 := by simpa using hb
      obtain ⟨n, hn⟩ := span_loc RC _ (hR _ (hf l)) (algebraMap Ω C b) (by
        rintro _ ⟨x, hx', rfl⟩
        obtain ⟨j, hj⟩ := hx x hx'
        exact ⟨j, by simpa using hR _ hj⟩) hz
      refine ⟨(n + m) * p, ?_⟩
      have : algebraMap Ω C (f l) ^ ((n + m) * p) * z ^ p =
          (algebraMap Ω C (f l) ^ n * (z / algebraMap Ω C b)) ^ p *
            algebraMap Ω C (1 * (f l ^ m * b) ^ p) := by
        rw [one_mul, map_pow, map_mul, map_pow, ← mul_pow, pow_mul, ← mul_pow]
        congr 1
        field_simp
        ring
      beta_reduce
      rw [this]
      exact mul_mem_gen RC _ (RC.pow_mem hn p)
        ⟨_, mul_mem_gen R _ R.one_mem ⟨_, hm, rfl⟩, rfl⟩
  · refine span_le RC _ _ (fun a ha v hv => span_stable RC _ ha hv) ?_
    rintro _ ⟨y, hy, rfl⟩
    have : powSpan R p X ≤ (powSpan RC p (spanOver RC (algebraMap Ω C '' X))).comap
        (algebraMap Ω C).toAddMonoidHom := by
      refine span_le R _ _ (fun a ha v hv => ?_) ?_
      · change algebraMap Ω C (a * v) ∈ powSpan RC p _
        rw [map_mul]
        exact span_stable RC _ (hR a ha) hv
      · rintro _ ⟨x, hx, rfl⟩
        change algebraMap Ω C (x ^ p) ∈ powSpan RC p _
        have h1 : algebraMap Ω C (x ^ p) = 1 * (1 * algebraMap Ω C x) ^ p := by simp
        rw [h1]
        exact mul_mem_gen RC _ RC.one_mem ⟨_, mul_mem_gen RC _ RC.one_mem ⟨x, hx, rfl⟩, rfl⟩
    exact this hy
