import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsPeriodAtRestrict
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IntegralClosureHeightEqOneOfLiesOver
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatLineGenerator
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CardComapMulFinsumEqFinsumFibres
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SncPts
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsTwistedGenerators
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenMapGermEqGenMapGerm

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase GlobalTheory.CompanionTheory.Ar.GeoModel
open GroundTheory.Heights₂.Heights.LowerBoundFree

namespace GlobalTheory.CompanionTheory.Ar.GeoModel.DeltaLine

open GlobalTheory.CompanionTheory.Ar.FlagBun.Twist

section Basic

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

/- English proof (translation)
Assemble the required witnesses or components as `⟨one_ne_zero, one_mem _, by simpa using one_mem (regAt ξ q)⟩`.
-/
theorem ua_one (q : Cpt ξ) : unitAt ξ q 1 :=
  ⟨one_ne_zero, one_mem _, by simpa using one_mem (regAt ξ q)⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨mul_ne_zero ha.1 hb.1, mul_mem ha.2.1 hb.2.1, by rw [mul_inv]; exact mul_mem ha.2.2 hb.2.2⟩`.
-/
theorem ua_mul {q : Cpt ξ} {a b : Ω} (ha : unitAt ξ q a) (hb : unitAt ξ q b) : unitAt ξ q (a * b) :=
  ⟨mul_ne_zero ha.1 hb.1, mul_mem ha.2.1 hb.2.1, by rw [mul_inv]; exact mul_mem ha.2.2 hb.2.2⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨inv_ne_zero ha.1, ha.2.2, by rw [inv_inv]; exact ha.2.1⟩`.
-/
theorem ua_inv {q : Cpt ξ} {a : Ω} (ha : unitAt ξ q a) : unitAt ξ q a⁻¹ :=
  ⟨inv_ne_zero ha.1, ha.2.2, by rw [inv_inv]; exact ha.2.1⟩

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simpa using ua_one q`. Consider the case `succ n ih => rw [pow_succ]`. Conclude with `ua_mul ih ha`.
-/
theorem ua_pow {q : Cpt ξ} {a : Ω} (ha : unitAt ξ q a) (n : ℕ) : unitAt ξ q (a ^ n) := by
  induction n with
  | zero => simpa using ua_one q
  | succ n ih => rw [pow_succ]; exact ua_mul ih ha

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using ua_one q`. Consider the case `insert a s ha ih`. Rewrite using `[Finset.prod_insert ha]`. Conclude with `ua_mul (h _ (Finset.mem_insert_self _ _)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))`.
-/
theorem ua_prod {A : Type} (s : Finset A) {f : A → Ω} {q : Cpt ξ} (h : ∀ i ∈ s, unitAt ξ q (f i)) :
    unitAt ξ q (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using ua_one q
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact ua_mul (h _ (Finset.mem_insert_self _ _)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/- English proof (translation)
Establish `e : g = u⁻¹ * (u * g)` using `by rw [inv_mul_cancel_left₀ hu.1]`. Rewrite using `[e]`. Conclude with `mul_mem hu.2.2 h`.
-/
theorem reg_of_mul {q : Cpt ξ} {u g : Ω} (hu : unitAt ξ q u) (h : u * g ∈ regAt ξ q) : g ∈ regAt ξ q := by
  have e : g = u⁻¹ * (u * g) := by rw [inv_mul_cancel_left₀ hu.1]
  rw [e]
  exact mul_mem hu.2.2 h

/- English proof (translation)
Rewrite using `[Matrix.det_apply']`. Conclude with `sum_mem fun σ _ => mul_mem (intCast_mem _ _) (prod_mem fun i _ => h _ _)`.
-/
theorem det_mem {r : ℕ} (R : Subring Ω) (A : Matrix (Fin r) (Fin r) Ω) (h : ∀ i j, A i j ∈ R) : A.det ∈ R := by
  rw [Matrix.det_apply']
  exact sum_mem fun σ _ => mul_mem (intCast_mem _ _) (prod_mem fun i _ => h _ _)

variable {E : Type} [AddCommGroup E] [Module Ω E]

/- English proof (translation)
Simplify using `only [Matrix.mul_apply, Finset.smul_sum, Finset.sum_smul, smul_smul]`. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ => by rw [mul_comm]`.
-/
theorem comb_comb {r : ℕ} (v : Fin r → E) (M N : Matrix (Fin r) (Fin r) Ω) (k : Fin r) :
    ∑ j, N j k • ∑ l, M l j • v l = ∑ l, (M * N) l k • v l := by
  simp only [Matrix.mul_apply, Finset.smul_sum, Finset.sum_smul, smul_smul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ => by rw [mul_comm]

/- English proof (translation)
Use extensionality with `i k`. Use `Fintype.linearIndependent_iff.1 hv (fun l => M l k - N l k) (by simp only [sub_smul, Finset.sum_sub_distrib, h k, sub_self]) i` as an intermediate fact. Conclude with `sub_eq_zero.1 this`.
-/
theorem mat_ext {r : ℕ} {v : Fin r → E} (hv : LinearIndependent Ω v) {M N : Matrix (Fin r) (Fin r) Ω}
    (h : ∀ k, ∑ l, M l k • v l = ∑ l, N l k • v l) : M = N := by
  ext i k
  have := Fintype.linearIndependent_iff.1 hv (fun l => M l k - N l k)
    (by simp only [sub_smul, Finset.sum_sub_distrib, h k, sub_self]) i
  exact sub_eq_zero.1 this

/- English proof (translation)
Establish `h : ∀ k, ∃ f : Fin r → regAt ξ q, ∑ k', f k' • b k' = c k` using `fun k => by`. Establish `hk : c k ∈ L q`. Rewrite using `[hc.2]`. Conclude with `Submodule.subset_span ⟨k, rfl⟩`. Rewrite `hk` using `[hb.2]`.

Conclude with `(Submodule.mem_span_range_iff_exists_fun _).1 hk`. Use `choose f hf using h`. Conclude with `⟨Matrix.of fun k' k => (f k k' : Ω), fun i j => (f j i).2, fun k => by rw [← hf k]; rfl⟩`.
-/
theorem exists_reg_change {L : Lat ξ E} {r : ℕ} {b c : Fin r → E} {q : Cpt ξ} (hb : L.IsFrameAt b q)
    (hc : L.IsFrameAt c q) :
    ∃ A : Matrix (Fin r) (Fin r) Ω, (∀ i j, A i j ∈ regAt ξ q) ∧ ∀ k, c k = ∑ k', A k' k • b k' := by
  have h : ∀ k, ∃ f : Fin r → regAt ξ q, ∑ k', f k' • b k' = c k := fun k => by
    have hk : c k ∈ L q := by
      rw [hc.2]
      exact Submodule.subset_span ⟨k, rfl⟩
    rw [hb.2] at hk
    exact (Submodule.mem_span_range_iff_exists_fun _).1 hk
  choose f hf using h
  exact ⟨Matrix.of fun k' k => (f k k' : Ω), fun i j => (f j i).2, fun k => by rw [← hf k]; rfl⟩

/- English proof (translation)
Take `⟨A', hA'r, hA'⟩` from `exists_reg_change hb hc`. Take `⟨B, hBr, hB⟩` from `exists_reg_change hc hb`. Establish `e : A = A'` using `mat_ext hb.1 fun k => by rw [← hA, ← hA']`. Establish `h1 : A * B = 1` using `mat_ext hb.1 fun k => by`. Rewrite using `[← comb_comb b A B k]`.

Simplify using `only [← hA]`. Rewrite using `[← hB k]`. Simplify using `[Matrix.one_apply]`. Establish `h2 : A.det * B.det = 1` using `by rw [← Matrix.det_mul, h1, Matrix.det_one]`. Use `⟨left_ne_zero_of_mul_eq_one h2, det_mem _ _ (e ▸ hA'r), ?_⟩` and prove the remaining obligations.

Rewrite using `[← eq_inv_of_mul_eq_one_right h2]`. Conclude with `det_mem _ _ hBr`.
-/
theorem det_unit {L : Lat ξ E} {r : ℕ} {b c : Fin r → E} {q : Cpt ξ} (hb : L.IsFrameAt b q)
    (hc : L.IsFrameAt c q) {A : Matrix (Fin r) (Fin r) Ω} (hA : ∀ k, c k = ∑ k', A k' k • b k') :
    unitAt ξ q A.det := by
  obtain ⟨A', hA'r, hA'⟩ := exists_reg_change hb hc
  obtain ⟨B, hBr, hB⟩ := exists_reg_change hc hb
  have e : A = A' := mat_ext hb.1 fun k => by rw [← hA, ← hA']
  have h1 : A * B = 1 := mat_ext hb.1 fun k => by
    rw [← comb_comb b A B k]
    simp only [← hA]
    rw [← hB k]
    simp [Matrix.one_apply]
  have h2 : A.det * B.det = 1 := by rw [← Matrix.det_mul, h1, Matrix.det_one]
  refine ⟨left_ne_zero_of_mul_eq_one h2, det_mem _ _ (e ▸ hA'r), ?_⟩
  rw [← eq_inv_of_mul_eq_one_right h2]
  exact det_mem _ _ hBr

/- English proof (translation)
Take `⟨A, -, hA⟩` from `exists_reg_change hb hb₂`. Take `⟨B, -, hB⟩` from `exists_reg_change hc hc₂`. Establish `uA` using `det_unit hb hb₂ hA`. Establish `uB` using `det_unit hc hc₂ hB`. Establish `e : T * B = A * T₂` using `mat_ext hb.1 fun k => by`.

Rewrite using `[← comb_comb b T B k, ← comb_comb b A T₂ k]`. Simplify using `only [← hT, ← hA]`. Rewrite using `[← hB k, ← hT₂ k]`. Use `⟨B.det * A.det⁻¹, ua_mul uB (ua_inv uA), ?_⟩` and prove the remaining obligations. Establish `h` using `congrArg Matrix.det e`.

Rewrite `h` using `[Matrix.det_mul, Matrix.det_mul]`. Apply `mul_left_cancel₀ uA.1` to reduce the goal to its premises. Rewrite using `[← h]`. Clear denominators, using `[uA.1]` for the nonvanishing conditions.
-/
theorem det_ratio {L M : Lat ξ E} {r : ℕ} {b b₂ c c₂ : Fin r → E} {q : Cpt ξ} {T T₂ : Matrix (Fin r) (Fin r) Ω}
    (hb : L.IsFrameAt b q) (hb₂ : L.IsFrameAt b₂ q) (hc : M.IsFrameAt c q) (hc₂ : M.IsFrameAt c₂ q)
    (hT : ∀ k, c k = ∑ k', T k' k • b k') (hT₂ : ∀ k, c₂ k = ∑ k', T₂ k' k • b₂ k') :
    ∃ u, unitAt ξ q u ∧ T₂.det = u * T.det := by
  obtain ⟨A, -, hA⟩ := exists_reg_change hb hb₂
  obtain ⟨B, -, hB⟩ := exists_reg_change hc hc₂
  have uA := det_unit hb hb₂ hA
  have uB := det_unit hc hc₂ hB
  have e : T * B = A * T₂ := mat_ext hb.1 fun k => by
    rw [← comb_comb b T B k, ← comb_comb b A T₂ k]
    simp only [← hT, ← hA]
    rw [← hB k, ← hT₂ k]
  refine ⟨B.det * A.det⁻¹, ua_mul uB (ua_inv uA), ?_⟩
  have h := congrArg Matrix.det e
  rw [Matrix.det_mul, Matrix.det_mul] at h
  apply mul_left_cancel₀ uA.1
  rw [← h]
  field_simp [uA.1]

def deltaLat (ξ : Spec (CommRingCat.of Ω) ⟶ X) {Li : Type} [AddCommGroup Li] [Module Ω Li] {I : Type} [Fintype I]
    (r : I → ℕ) (V W : I → Lat ξ Li) (p : ℕ) : Lat ξ Ω := fun q =>
  open Classical in
  if InFibre ξ p q then
    Submodule.span (regAt ξ q) {t | ∃ (b b' : ∀ i, Fin (r i) → Li) (T : ∀ i, Matrix (Fin (r i)) (Fin (r i)) Ω),
      (∀ i, (V i).IsFrameAt (b i) q) ∧ (∀ i, (W i).IsFrameAt (b' i) q) ∧
        (∀ i k, b' i k = ∑ k', T i k' k • b i k') ∧ t = ∏ i, (T i).det}
  else Submodule.span (regAt ξ q) {1}

variable {Li : Type} [AddCommGroup Li] [Module Ω Li] {I : Type} [Fintype I] {r : I → ℕ} {V W : I → Lat ξ Li} {p : ℕ}

/- English proof (translation)
Simplify using `only [deltaLat, if_neg hq]`.
-/
theorem deltaLat_off {q : Cpt ξ} (hq : ¬ InFibre ξ p q) :
    deltaLat ξ r V W p q = Submodule.span (regAt ξ q) {1} := by
  simp only [deltaLat, if_neg hq]

/- English proof (translation)
Simplify using `only [deltaLat, if_pos hq]`. Apply `le_antisymm` to reduce the goal to its premises. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `t ⟨b₂, b₂', T₂, h1, h2, h3, rfl⟩`. Use `choose u hu e using fun i => det_ratio (hb i) (h1 i) (hb' i) (h2 i) (hT i) (h3 i)`.

Establish `hU : unitAt ξ q (∏ i, u i)` using `ua_prod _ fun i _ => hu i`. Use `SetLike.mem_coe.2 (Submodule.mem_span_singleton.2 ⟨⟨_, hU.2.1⟩, ?_⟩)` and prove the remaining obligations. Use `show (∏ i, u i) * _ = _`. Rewrite using `[← Finset.prod_mul_distrib]`. Conclude with `Finset.prod_congr rfl fun i _ => (e i).symm`.

Conclude with `Submodule.span_mono (Set.singleton_subset_iff.2 ⟨b, b', T, hb, hb', hT, rfl⟩)`.
-/
theorem deltaLat_fibre {q : Cpt ξ} (hq : InFibre ξ p q) {b b' : ∀ i, Fin (r i) → Li}
    {T : ∀ i, Matrix (Fin (r i)) (Fin (r i)) Ω} (hb : ∀ i, (V i).IsFrameAt (b i) q)
    (hb' : ∀ i, (W i).IsFrameAt (b' i) q) (hT : ∀ i k, b' i k = ∑ k', T i k' k • b i k') :
    deltaLat ξ r V W p q = Submodule.span (regAt ξ q) {∏ i, (T i).det} := by
  simp only [deltaLat, if_pos hq]
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro t ⟨b₂, b₂', T₂, h1, h2, h3, rfl⟩
    choose u hu e using fun i => det_ratio (hb i) (h1 i) (hb' i) (h2 i) (hT i) (h3 i)
    have hU : unitAt ξ q (∏ i, u i) := ua_prod _ fun i _ => hu i
    refine SetLike.mem_coe.2 (Submodule.mem_span_singleton.2 ⟨⟨_, hU.2.1⟩, ?_⟩)
    show (∏ i, u i) * _ = _
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => (e i).symm
  · exact Submodule.span_mono (Set.singleton_subset_iff.2 ⟨b, b', T, hb, hb', hT, rfl⟩)

/- English proof (translation)
Use `⟨linearIndependent_unique_iff.2 h0, ?_⟩` and prove the remaining obligations. Rewrite using `[h, Set.range_const]`.
-/
theorem frame_gen {L : Lat ξ Ω} {t : Ω} {q : Cpt ξ} (h0 : t ≠ 0) (h : L q = Submodule.span (regAt ξ q) {t}) :
    L.IsFrameAt (fun _ : Fin 1 => t) q := by
  refine ⟨linearIndependent_unique_iff.2 h0, ?_⟩
  rw [h, Set.range_const]

/- English proof (translation)
Rewrite using `[Set.range_const, eq_top_iff]`. Introduce `a _`. Conclude with `Submodule.mem_span_singleton.2 ⟨a / t, by simp [h0]⟩`.
-/
theorem span_const {t : Ω} (h0 : t ≠ 0) : Submodule.span Ω (Set.range fun _ : Fin 1 => t) = ⊤ := by
  rw [Set.range_const, eq_top_iff]
  intro a _
  exact Submodule.mem_span_singleton.2 ⟨a / t, by simp [h0]⟩

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Use `Submodule.span_le.2 (Set.singleton_subset_iff.2 ?_)` and prove the remaining obligations. Use `SetLike.mem_coe.2 (Submodule.mem_span_singleton.2 ⟨⟨_, h.2.2⟩, ?_⟩)` and prove the remaining obligations. Use `show t⁻¹ * t = 1`. Conclude with `inv_mul_cancel₀ h.1`.

Use `Submodule.span_le.2 (Set.singleton_subset_iff.2 ?_)` and prove the remaining obligations. Use `SetLike.mem_coe.2 (Submodule.mem_span_singleton.2 ⟨⟨_, h.2.1⟩, ?_⟩)` and prove the remaining obligations. Use `show t * 1 = t`. Conclude with `mul_one t`.
-/
theorem span_one_eq {t : Ω} {q : Cpt ξ} (h : unitAt ξ q t) :
    Submodule.span (regAt ξ q) {(1 : Ω)} = Submodule.span (regAt ξ q) {t} := by
  apply le_antisymm
  · refine Submodule.span_le.2 (Set.singleton_subset_iff.2 ?_)
    refine SetLike.mem_coe.2 (Submodule.mem_span_singleton.2 ⟨⟨_, h.2.2⟩, ?_⟩)
    show t⁻¹ * t = 1
    exact inv_mul_cancel₀ h.1
  · refine Submodule.span_le.2 (Set.singleton_subset_iff.2 ?_)
    refine SetLike.mem_coe.2 (Submodule.mem_span_singleton.2 ⟨⟨_, h.2.1⟩, ?_⟩)
    show t * 1 = t
    exact mul_one t

/- English proof (translation)
Assemble the required witnesses or components as `⟨⟨⋂ i, (U i : Set X), isOpen_iInter_of_finite fun i => (U i).isOpen⟩, Set.mem_iInter.2 h, fun i _ hz => Set.mem_iInter.1 hz i⟩`.
-/
theorem exists_open_le {I : Type} [Finite I] (U : I → X.Opens) {y : X} (h : ∀ i, y ∈ U i) :
    ∃ W : X.Opens, y ∈ W ∧ ∀ i, W ≤ U i :=
  ⟨⟨⋂ i, (U i : Set X), isOpen_iInter_of_finite fun i => (U i).isOpen⟩, Set.mem_iInter.2 h,
    fun i _ hz => Set.mem_iInter.1 hz i⟩

/- English proof (translation)
Set `J : Ideal (chartR x c)` to `{ carrier := {d | (d : Ω) * g ∈ chartR x c} add_mem' := by`. Introduce and unpack `d d' hd hd'`. Establish `e : ((d + d' : chartR x c) : Ω) * g = (d : Ω) * g + (d' : Ω) * g`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Use `show ((d + d' : chartR x c) : Ω) * g ∈ chartR x c`. Rewrite using `[e]`. Conclude with `add_mem hd hd'`. Use the proof step `zero_mem' := by show ((0 : chartR x c) : Ω) * g ∈ chartR x c`. Simplify using the standard rewrite rules.

Use the proof step `smul_mem' := by`. Introduce and unpack `t d hd`. Establish `e : ((t • d : chartR x c) : Ω) * g = (t : Ω) * ((d : Ω) * g)`. Rewrite using `[smul_eq_mul]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Use `show ((t • d : chartR x c) : Ω) * g ∈ chartR x c`. Rewrite using `[e]`. Conclude with `mul_mem t.2 hd }`. Set `S : Submonoid (chartR x c)` to `{ carrier := {y | ∃ m N : ℕ, 0 < m ∧ y = (m : chartR x c) * s ^ N} mul_mem' := by`.

Introduce and unpack `_ _ ⟨m, N, hm, rfl⟩ ⟨m', N', hm', rfl⟩`. Conclude with `⟨m * m', N + N', Nat.mul_pos hm hm', by push_cast; ring⟩`. Use the proof step `one_mem' := ⟨1, 0, one_pos, by simp⟩ }`. Assume the negation of the conclusion as `hn`. Establish `hd : Disjoint (J : Set (chartR x c)) (S : Set (chartR x c))`.

Rewrite using `[Set.disjoint_left]`. Introduce and unpack `y hy ⟨m, N, hm, rfl⟩`. Use `hn ⟨m, N, hm, ?_⟩` and prove the remaining obligations. Establish `hy' : (((m : chartR x c) * s ^ N : chartR x c) : Ω) * g ∈ chartR x c` using `hy`. Simplify using `using hy'`.

Take `⟨Q, hQ, hJQ, hQS⟩` from `Ideal.exists_le_prime_disjoint J S hd`. Take `⟨q, hqc, f1, f2⟩` from `chart_prime h hc Q hQ`. Establish `hmem : ∀ y ∈ S, unitAt ξ q (y : Ω)` using `fun y hy => by`. Assume the negation of the conclusion as `hu`. Conclude with `Set.disjoint_left.1 hQS ((f1 y).2 hu) hy`.

Establish `hch : Char0 ξ q` using `fun l hl hf => hf (by simpa using hmem (l : chartR x c) ⟨l, 0, hl.pos, by simp⟩)`. Establish `hs : unitAt ξ q (s : Ω)` using `hmem s ⟨1, 1, one_pos, by simp⟩`. Take `⟨u, v, hv, e⟩` from `f2 g (hg q hqc hch hs)`. Apply `hv` to reduce the goal to its premises. Apply `hJQ` to reduce the goal to its premises.

Use `show (v : Ω) * g ∈ chartR x c`. Rewrite using `[mul_comm, e]`. Conclude with `u.2`.
-/
theorem exists_den {κ : Type} {x : κ → Ω} (h : CoordTie ℤ ξ x) {c : κ} (hc : x c ≠ 0) (s : chartR x c) (g : Ω)
    (hg : ∀ q : Cpt ξ, InChart ξ x c q → Char0 ξ q → unitAt ξ q (s : Ω) → g ∈ regAt ξ q) :
    ∃ m N : ℕ, 0 < m ∧ (m : Ω) * (s : Ω) ^ N * g ∈ chartR x c := by
  let J : Ideal (chartR x c) :=
    { carrier := {d | (d : Ω) * g ∈ chartR x c}
      add_mem' := by
        rintro d d' hd hd'
        have e : ((d + d' : chartR x c) : Ω) * g = (d : Ω) * g + (d' : Ω) * g := by
          push_cast
          ring
        show ((d + d' : chartR x c) : Ω) * g ∈ chartR x c
        rw [e]
        exact add_mem hd hd'
      zero_mem' := by
        show ((0 : chartR x c) : Ω) * g ∈ chartR x c
        simp
      smul_mem' := by
        rintro t d hd
        have e : ((t • d : chartR x c) : Ω) * g = (t : Ω) * ((d : Ω) * g) := by
          rw [smul_eq_mul]
          push_cast
          ring
        show ((t • d : chartR x c) : Ω) * g ∈ chartR x c
        rw [e]
        exact mul_mem t.2 hd }
  let S : Submonoid (chartR x c) :=
    { carrier := {y | ∃ m N : ℕ, 0 < m ∧ y = (m : chartR x c) * s ^ N}
      mul_mem' := by
        rintro _ _ ⟨m, N, hm, rfl⟩ ⟨m', N', hm', rfl⟩
        exact ⟨m * m', N + N', Nat.mul_pos hm hm', by push_cast; ring⟩
      one_mem' := ⟨1, 0, one_pos, by simp⟩ }
  by_contra hn
  have hd : Disjoint (J : Set (chartR x c)) (S : Set (chartR x c)) := by
    rw [Set.disjoint_left]
    rintro y hy ⟨m, N, hm, rfl⟩
    refine hn ⟨m, N, hm, ?_⟩
    have hy' : (((m : chartR x c) * s ^ N : chartR x c) : Ω) * g ∈ chartR x c := hy
    simpa using hy'
  obtain ⟨Q, hQ, hJQ, hQS⟩ := Ideal.exists_le_prime_disjoint J S hd
  obtain ⟨q, hqc, f1, f2⟩ := chart_prime h hc Q hQ
  have hmem : ∀ y ∈ S, unitAt ξ q (y : Ω) := fun y hy => by
    by_contra hu
    exact Set.disjoint_left.1 hQS ((f1 y).2 hu) hy
  have hch : Char0 ξ q := fun l hl hf => hf (by simpa using hmem (l : chartR x c) ⟨l, 0, hl.pos, by simp⟩)
  have hs : unitAt ξ q (s : Ω) := hmem s ⟨1, 1, one_pos, by simp⟩
  obtain ⟨u, v, hv, e⟩ := f2 g (hg q hqc hch hs)
  apply hv
  apply hJQ
  show (v : Ω) * g ∈ chartR x c
  rw [mul_comm, e]
  exact u.2

end Basic

section Line

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] [CharZero Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {Li : Type} [AddCommGroup Li] [Module Ω Li] {I : Type} [Fintype I] {r : I → ℕ} {V W : I → Lat ξ Li} {p : ℕ}

/- English proof (translation)
Establish `hTp : ∀ q : Cpt ξ, InFibre ξ p q → ∀ l : ℕ, l.Prime → l ≠ p → ¬ InFibre ξ l q` using `fun q hq l hl hne => Lat.not_inFibre_of_coprime q ((Nat.coprime_primes hp hl).2 hne.symm) hq`. Use `choose U hU b hbs hb using fun i => hV i q₀ (Set.mem_univ _)`. Use `choose U' hU' b' hbs' hb' using fun i => hW i q₀ (hTp q₀ hq₀)`. Take `⟨U₁, hU₁, hle⟩` from `exists_open_le (fun i : I ⊕ I => Sum.elim U U' i) (y := q₀.1) (by rintro (i | i); exacts [hU i, hU' i])`. Establish `hbq : ∀ i (q : Cpt ξ), q.1 ∈ U₁ → (V i).IsFrameAt (b i) q` using `fun i q hq => hb i q (Set.mem_univ _) (hle (Sum.inl i) hq)`.

Establish `hbq' : ∀ i (q : Cpt ξ), q.1 ∈ U₁ → (∀ l : ℕ, l.Prime → l ≠ p → ¬ InFibre ξ l q) → (W i).IsFrameAt (b' i) q` using `fun i q hq ht => hb' i q ht (hle (Sum.inr i) hq)`. Establish `hex : ∀ i k, ∃ f : Fin (r i) → Ω, ∑ k', f k' • b i k' = b' i k` using `fun i k => by`. Establish `h : b' i k ∈ Submodule.span Ω (Set.range (b i))`. Rewrite using `[hbs i, ← hbs' i]`. Conclude with `Submodule.subset_span ⟨k, rfl⟩`.

Conclude with `(Submodule.mem_span_range_iff_exists_fun _).1 h`. Use `choose f hf using hex`. Set `T : ∀ i, Matrix (Fin (r i)) (Fin (r i)) Ω` to `fun i => Matrix.of fun k' k => f i k k'`. Establish `hTm : ∀ i k, b' i k = ∑ k', T i k' k • b i k'` using `fun i k => (hf i k).symm`. Take `⟨t, ht⟩ : ∃ t : Ω, t = ∏ i, (T i).det` from `⟨_, rfl⟩`.

Establish `hunit : ∀ q : Cpt ξ, Char0 ξ q → q.1 ∈ U₁ → unitAt ξ q t` using `fun q hc hq => by`. Rewrite using `[ht]`. Use `ua_prod _ fun i _ => ?_` and prove the remaining obligations. Establish `h1` using `hbq i q hq`. Establish `h2` using `hbq' i q hq fun l hl _ => hc l hl`.

Conclude with `det_unit h1 ⟨h2.1, by rw [← hVW i q hc]; exact h2.2⟩ (hTm i)`. Establish `ht0 : t ≠ 0`. Set `g : Cpt ξ` to `⟨genPt ξ, specializes_rfl⟩`. Establish `hg : Char0 ξ g` using `fun l hl hf => hf ⟨Nat.cast_ne_zero.2 hl.ne_zero, regAt_gen hT.gen _, regAt_gen hT.gen _⟩`. Conclude with `(hunit g hg (q₀.2.mem_open U₁.isOpen hU₁)).1`.

Take `⟨c, hc⟩` from `hT.cover q₀`. Take `⟨s, hs, hsU⟩` from `chart_nbhd hT hc.1 q₀ hc U₁ hU₁`. Take `⟨m₁, N₁, hm₁, e₁⟩` from `exists_den hT hc.1 s t fun q hq hch hu => (hunit q hch (hsU q hq hu)).2.1`. Take `⟨m₂, N₂, hm₂, e₂⟩` from `exists_den hT hc.1 s t⁻¹ fun q hq hch hu => (hunit q hch (hsU q hq hu)).2.2`. Take `⟨a, m, hnd, hn⟩` from `Nat.exists_eq_pow_mul_and_not_dvd (Nat.mul_pos hm₁ hm₂).ne' p hp.ne_one`.

Establish `hmu : unitAt ξ q₀ (m : Ω)` using `not_not.1 (Lat.not_inFibre_of_coprime q₀ ((Nat.Prime.coprime_iff_not_dvd hp).2 hnd) hq₀)`. Take `⟨U₂, hU₂, hmU⟩` from `(regAt_unitAt_open X Ω ξ q₀ (m : Ω)).2 hmu`. Take `⟨U₃, hU₃, hsU₃⟩` from `(regAt_unitAt_open X Ω ξ q₀ (s : Ω)).2 hs`. Take `⟨C, -, hC⟩` from `hT.affine c hc.1`. Establish `hq₀C : q₀.1 ∈ C` using `(hC _).2 ⟨q₀.2, hc⟩`.

Use `⟨C ⊓ U₂ ⊓ U₃, ⟨⟨hq₀C, hU₂⟩, hU₃⟩, fun _ => t, span_const ht0, fun q _ hq => frame_gen ht0 ?_⟩` and prove the remaining obligations. Take `⟨⟨hqC, hqm⟩, hqs⟩` from `hq`. Take `⟨_, hqc⟩` from `(hC q.1).1 hqC`. Establish `hqs'` using `hsU₃ q hqs`. Establish `hqU` using `hsU q hqc hqs'`.

Distinguish the cases in `hqF : InFibre ξ p q`. Rewrite using `[ht]`. Conclude with `deltaLat_fibre hqF (fun i => hbq i q hqU) (fun i => hbq' i q hqU (hTp q hqF)) hTm`. Rewrite using `[deltaLat_off hqF]`. Establish `hpu : unitAt ξ q (p : Ω)` using `not_not.1 hqF`.

Establish `hnu : unitAt ξ q ((m₁ * m₂ : ℕ) : Ω)`. Rewrite using `[hn]`. Use `push_cast`. Conclude with `ua_mul (ua_pow hpu a) (hmU q hqm)`. Establish `r1 : t ∈ regAt ξ q` using `reg_of_mul (ua_mul hnu (ua_pow hqs' N₁)) (by`.

Establish `h` using `mul_mem (natCast_mem (regAt ξ q) m₂) (chartR_le hT hc.1 e₁ hqc)`. Use `h using 1` and compare the differences between its conclusion and the goal. Use `push_cast`. Use the proof step `ring)`. Establish `r2 : t⁻¹ ∈ regAt ξ q` using `reg_of_mul (ua_mul hnu (ua_pow hqs' N₂)) (by`.

Establish `h` using `mul_mem (natCast_mem (regAt ξ q) m₁) (chartR_le hT hc.1 e₂ hqc)`. Use `h using 1` and compare the differences between its conclusion and the goal. Use `push_cast`. Use the proof step `ring)`. Conclude with `span_one_eq ⟨ht0, r1, r2⟩`.
-/
theorem isVB_at_fibre {κ : Type} {x : κ → Ω} {Vg : I → Submodule Ω Li} (hT : CoordTie ℤ ξ x) (hp : p.Prime)
    (hV : ∀ i, (V i).IsVB (r i) (Vg i))
    (hW : ∀ i, (W i).IsVBOn {q | ∀ l : ℕ, l.Prime → l ≠ p → ¬ InFibre ξ l q} (r i) (Vg i))
    (hVW : ∀ i (q : Cpt ξ), Char0 ξ q → W i q = V i q) {q₀ : Cpt ξ} (hq₀ : InFibre ξ p q₀) :
    ∃ U : X.Opens, q₀.1 ∈ U ∧ ∃ b : Fin 1 → Ω, Submodule.span Ω (Set.range b) = ⊤ ∧
      ∀ q ∈ (Set.univ : Set (Cpt ξ)), q.1 ∈ U → (deltaLat ξ r V W p).IsFrameAt b q := by
  have hTp : ∀ q : Cpt ξ, InFibre ξ p q → ∀ l : ℕ, l.Prime → l ≠ p → ¬ InFibre ξ l q := fun q hq l hl hne =>
    Lat.not_inFibre_of_coprime q ((Nat.coprime_primes hp hl).2 hne.symm) hq
  choose U hU b hbs hb using fun i => hV i q₀ (Set.mem_univ _)
  choose U' hU' b' hbs' hb' using fun i => hW i q₀ (hTp q₀ hq₀)
  obtain ⟨U₁, hU₁, hle⟩ := exists_open_le (fun i : I ⊕ I => Sum.elim U U' i) (y := q₀.1)
    (by rintro (i | i); exacts [hU i, hU' i])
  have hbq : ∀ i (q : Cpt ξ), q.1 ∈ U₁ → (V i).IsFrameAt (b i) q :=
    fun i q hq => hb i q (Set.mem_univ _) (hle (Sum.inl i) hq)
  have hbq' : ∀ i (q : Cpt ξ), q.1 ∈ U₁ → (∀ l : ℕ, l.Prime → l ≠ p → ¬ InFibre ξ l q) →
      (W i).IsFrameAt (b' i) q := fun i q hq ht => hb' i q ht (hle (Sum.inr i) hq)
  have hex : ∀ i k, ∃ f : Fin (r i) → Ω, ∑ k', f k' • b i k' = b' i k := fun i k => by
    have h : b' i k ∈ Submodule.span Ω (Set.range (b i)) := by
      rw [hbs i, ← hbs' i]
      exact Submodule.subset_span ⟨k, rfl⟩
    exact (Submodule.mem_span_range_iff_exists_fun _).1 h
  choose f hf using hex
  let T : ∀ i, Matrix (Fin (r i)) (Fin (r i)) Ω := fun i => Matrix.of fun k' k => f i k k'
  have hTm : ∀ i k, b' i k = ∑ k', T i k' k • b i k' := fun i k => (hf i k).symm
  obtain ⟨t, ht⟩ : ∃ t : Ω, t = ∏ i, (T i).det := ⟨_, rfl⟩
  have hunit : ∀ q : Cpt ξ, Char0 ξ q → q.1 ∈ U₁ → unitAt ξ q t := fun q hc hq => by
    rw [ht]
    refine ua_prod _ fun i _ => ?_
    have h1 := hbq i q hq
    have h2 := hbq' i q hq fun l hl _ => hc l hl
    exact det_unit h1 ⟨h2.1, by rw [← hVW i q hc]; exact h2.2⟩ (hTm i)
  have ht0 : t ≠ 0 := by
    let g : Cpt ξ := ⟨genPt ξ, specializes_rfl⟩
    have hg : Char0 ξ g := fun l hl hf =>
      hf ⟨Nat.cast_ne_zero.2 hl.ne_zero, regAt_gen hT.gen _, regAt_gen hT.gen _⟩
    exact (hunit g hg (q₀.2.mem_open U₁.isOpen hU₁)).1
  obtain ⟨c, hc⟩ := hT.cover q₀
  obtain ⟨s, hs, hsU⟩ := chart_nbhd hT hc.1 q₀ hc U₁ hU₁
  obtain ⟨m₁, N₁, hm₁, e₁⟩ := exists_den hT hc.1 s t
    fun q hq hch hu => (hunit q hch (hsU q hq hu)).2.1
  obtain ⟨m₂, N₂, hm₂, e₂⟩ := exists_den hT hc.1 s t⁻¹
    fun q hq hch hu => (hunit q hch (hsU q hq hu)).2.2
  obtain ⟨a, m, hnd, hn⟩ := Nat.exists_eq_pow_mul_and_not_dvd (Nat.mul_pos hm₁ hm₂).ne' p hp.ne_one
  have hmu : unitAt ξ q₀ (m : Ω) :=
    not_not.1 (Lat.not_inFibre_of_coprime q₀ ((Nat.Prime.coprime_iff_not_dvd hp).2 hnd) hq₀)
  obtain ⟨U₂, hU₂, hmU⟩ := (regAt_unitAt_open X Ω ξ q₀ (m : Ω)).2 hmu
  obtain ⟨U₃, hU₃, hsU₃⟩ := (regAt_unitAt_open X Ω ξ q₀ (s : Ω)).2 hs
  obtain ⟨C, -, hC⟩ := hT.affine c hc.1
  have hq₀C : q₀.1 ∈ C := (hC _).2 ⟨q₀.2, hc⟩
  refine ⟨C ⊓ U₂ ⊓ U₃, ⟨⟨hq₀C, hU₂⟩, hU₃⟩, fun _ => t, span_const ht0, fun q _ hq => frame_gen ht0 ?_⟩
  obtain ⟨⟨hqC, hqm⟩, hqs⟩ := hq
  obtain ⟨_, hqc⟩ := (hC q.1).1 hqC
  have hqs' := hsU₃ q hqs
  have hqU := hsU q hqc hqs'
  by_cases hqF : InFibre ξ p q
  · rw [ht]
    exact deltaLat_fibre hqF (fun i => hbq i q hqU) (fun i => hbq' i q hqU (hTp q hqF)) hTm
  · rw [deltaLat_off hqF]
    have hpu : unitAt ξ q (p : Ω) := not_not.1 hqF
    have hnu : unitAt ξ q ((m₁ * m₂ : ℕ) : Ω) := by
      rw [hn]
      push_cast
      exact ua_mul (ua_pow hpu a) (hmU q hqm)
    have r1 : t ∈ regAt ξ q := reg_of_mul (ua_mul hnu (ua_pow hqs' N₁)) (by
      have h := mul_mem (natCast_mem (regAt ξ q) m₂) (chartR_le hT hc.1 e₁ hqc)
      convert h using 1
      push_cast
      ring)
    have r2 : t⁻¹ ∈ regAt ξ q := reg_of_mul (ua_mul hnu (ua_pow hqs' N₂)) (by
      have h := mul_mem (natCast_mem (regAt ξ q) m₁) (chartR_le hT hc.1 e₂ hqc)
      convert h using 1
      push_cast
      ring)
    exact span_one_eq ⟨ht0, r1, r2⟩

end Line

/- English proof (translation)
Introduce `X Ω _ _ ξ κ _ x Li _ _ I _ r Vg V W p hT _ hp hV hW hVW`. Use `⟨deltaLat ξ r V W p, ?_, fun q hq => deltaLat_off hq, fun q hq b b' T hb hb' hT' => deltaLat_fibre hq hb hb' hT'⟩` and prove the remaining obligations. Introduce `q₀ _`. Distinguish the cases in `hq₀ : InFibre ξ p q₀`. Conclude with `isVB_at_fibre hT hp hV hW hVW hq₀`.

Take `⟨U, hU, h⟩` from `(regAt_unitAt_open X Ω ξ q₀ (p : Ω)).2 (not_not.1 hq₀)`. Conclude with `⟨U, hU, fun _ => 1, span_const one_ne_zero, fun q _ hqU => frame_gen one_ne_zero (deltaLat_off (not_not.2 (h q hqU)))⟩`.
-/
theorem exists_delta : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Sp Ω ⟶ X) (κ : Type) [Finite κ] (x : κ → Ω) (Li : Type) [AddCommGroup Li] [Module Ω Li] (I : Type) [Fintype I] (r : I → ℕ) (Vg : I → Submodule Ω Li) (V W : I → Lat ξ Li) (p : ℕ), CoordTie ℤ ξ x → (∀ q : X, genPt ξ ⤳ q) → p.Prime → (∀ i, (V i).IsVB (r i) (Vg i)) → (∀ i, (W i).IsVBOn {q | ∀ l : ℕ, l.Prime → l ≠ p → ¬ InFibre ξ l q} (r i) (Vg i)) → (∀ i (q : Cpt ξ), Char0 ξ q → W i q = V i q) → ∃ Δ : Lat ξ Ω, Δ.IsVB 1 ⊤ ∧ (∀ q, ¬ InFibre ξ p q → Δ q = Submodule.span (regAt ξ q) {1}) ∧ ∀ q, InFibre ξ p q → ∀ (b b' : ∀ i, Fin (r i) → Li) (T : ∀ i, Matrix (Fin (r i)) (Fin (r i)) Ω), (∀ i, (V i).IsFrameAt (b i) q) → (∀ i, (W i).IsFrameAt (b' i) q) → (∀ i k, b' i k = ∑ k', T i k' k • b i k') → Δ q = Submodule.span (regAt ξ q) {∏ i, (T i).det} := by
  intro X Ω _ _ ξ κ _ x Li _ _ I _ r Vg V W p hT _ hp hV hW hVW
  refine ⟨deltaLat ξ r V W p, ?_, fun q hq => deltaLat_off hq,
    fun q hq b b' T hb hb' hT' => deltaLat_fibre hq hb hb' hT'⟩
  intro q₀ _
  by_cases hq₀ : InFibre ξ p q₀
  · exact isVB_at_fibre hT hp hV hW hVW hq₀
  · obtain ⟨U, hU, h⟩ := (regAt_unitAt_open X Ω ξ q₀ (p : Ω)).2 (not_not.1 hq₀)
    exact ⟨U, hU, fun _ => 1, span_const one_ne_zero, fun q _ hqU =>
      frame_gen one_ne_zero (deltaLat_off (not_not.2 (h q hqU)))⟩

end GlobalTheory.CompanionTheory.Ar.GeoModel.DeltaLine
