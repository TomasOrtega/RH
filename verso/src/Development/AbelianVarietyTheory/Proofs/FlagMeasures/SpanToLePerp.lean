import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.EichlerIsometry
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.FrameOnto
open GlobalTheory.HL.Eichler

section
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

/- English proof (translation)
Use `⟨fun v => ⟨fun hv => ?_, fun hv => ?_⟩, h1⟩` and prove the remaining obligations. Establish `h3` using `A.add_mem (hBA (h2 _ hv)) hv`. Establish `h4 : g⁻¹ (g v) = v` using `g.symm_apply_apply v`. Rewrite `h3` using `[h4, sub_add_cancel]`. Then use the resulting hypothesis. Simplify using `using A.add_mem (hBA (h1 _ hv)) hv`.
-/
theorem mem_unipOn {n : ℕ} {A B : Submodule E (Fin n → E)} (hBA : B ≤ A)
    (g : (Fin n → E) ≃ₗ[E] (Fin n → E)) (h1 : ∀ v ∈ A, g v - v ∈ B) (h2 : ∀ v ∈ A, g⁻¹ v - v ∈ B) :
    g ∈ unipOn A B := by
  refine ⟨fun v => ⟨fun hv => ?_, fun hv => ?_⟩, h1⟩
  · have h3 := A.add_mem (hBA (h2 _ hv)) hv
    have h4 : g⁻¹ (g v) = v := g.symm_apply_apply v
    rwa [h4, sub_add_cancel] at h3
  · simpa using A.add_mem (hBA (h1 _ hv)) hv

/- English proof (translation)
The claim follows from `Submodule.span_mono (Set.image_mono fun _ hi => lt_of_lt_of_le hi h)`.
-/
theorem spanTo_mono (g : Fin (r + 1) → S.V) {a b : ℕ} (h : a ≤ b) : S.spanTo g a ≤ S.spanTo g b :=
  Submodule.span_mono (Set.image_mono fun _ hi => lt_of_lt_of_le hi h)

/- English proof (translation)
The claim follows from `Submodule.subset_span ⟨i, h, rfl⟩`.
-/
theorem mem_spanTo (g : Fin (r + 1) → S.V) {i : Fin (r + 1)} {a : ℕ} (h : (i : ℕ) < a) :
    g i ∈ S.spanTo g a := Submodule.subset_span ⟨i, h, rfl⟩

/- English proof (translation)
Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem x hx => obtain ⟨i, hi, rfl⟩ := hx`. Conclude with `h i hi`. Consider the case `zero => simp [hf]`. Consider the case `add x y _ _ hx hy => rw [hf_add_l, hx, hy, add_zero]`.

Consider the case `smul c x _ hx => rw [hf_smul_l, hx, mul_zero]`.
-/
theorem hf_spanTo (g : Fin (r + 1) → S.V) {a : ℕ} {v w : S.V} (hv : v ∈ S.spanTo g a)
    (h : ∀ i : Fin (r + 1), (i : ℕ) < a → hf L S.Hm (g i) w = 0) : hf L S.Hm v w = 0 := by
  induction hv using Submodule.span_induction with
  | mem x hx => obtain ⟨i, hi, rfl⟩ := hx; exact h i hi
  | zero => simp [hf]
  | add x y _ _ hx hy => rw [hf_add_l, hx, hy, add_zero]
  | smul c x _ hx => rw [hf_smul_l, hx, mul_zero]

/- English proof (translation)
Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨i, hi, rfl⟩` from `hx`. Use `⟨Pi.single i 1, fun j hj => ?_, ?_⟩` and prove the remaining obligations. Establish `hi' : (i : ℕ) < a` using `hi`.

Rewrite using `[Pi.single_eq_of_ne]`. Introduce and unpack `rfl`. Use linear arithmetic over natural numbers and integers. Simplify using `[Pi.single_apply]`. Consider the case `zero => exact ⟨0, fun _ _ => rfl, by simp⟩`.

Consider the case `add x y _ _ hx hy`. Take `⟨c, hc, rfl⟩` from `hx`. Take `⟨d, hd, rfl⟩` from `hy`. Conclude with `⟨c + d, fun i hi => by simp [hc i hi, hd i hi], by simp [add_smul, Finset.sum_add_distrib]⟩`. Consider the case `smul t x _ hx`.

Take `⟨c, hc, rfl⟩` from `hx`. Conclude with `⟨t • c, fun i hi => by simp [hc i hi], by simp [Finset.smul_sum, smul_smul]⟩`.
-/
theorem coords (g : Fin (r + 1) → S.V) {a : ℕ} {v : S.V} (hv : v ∈ S.spanTo g a) :
    ∃ c : Fin (r + 1) → E, (∀ i : Fin (r + 1), a ≤ (i : ℕ) → c i = 0) ∧ v = ∑ i, c i • g i := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, hi, rfl⟩ := hx
    refine ⟨Pi.single i 1, fun j hj => ?_, ?_⟩
    · have hi' : (i : ℕ) < a := hi
      rw [Pi.single_eq_of_ne]
      rintro rfl
      omega
    · simp [Pi.single_apply]
  | zero => exact ⟨0, fun _ _ => rfl, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨c, hc, rfl⟩ := hx
    obtain ⟨d, hd, rfl⟩ := hy
    exact ⟨c + d, fun i hi => by simp [hc i hi, hd i hi], by simp [add_smul, Finset.sum_add_distrib]⟩
  | smul t x _ hx =>
    obtain ⟨c, hc, rfl⟩ := hx
    exact ⟨t • c, fun i hi => by simp [hc i hi], by simp [Finset.smul_sum, smul_smul]⟩

variable (g : Fin (r + 1) → S.V) (gs : Fin r → S.V) (T : Fˣ)
  (gram : ∀ a b, hf L S.Hm (g a) (g b) =
    if a = Fin.last r ∧ b = Fin.last r then -algebraMap F E T else 0)
  (dual : ∀ a j, hf L S.Hm (g a) (gs j) = if a = j.castSucc then 1 else 0)

include gram in
/- English proof (translation)
Introduce `y hy`. Rewrite using `[← hf_cj L S.herm.1, hf_spanTo S g hy, map_zero]`. Introduce `i hi`. Rewrite using `[gram, if_neg]`. Introduce and unpack `⟨rfl, -⟩`.

Simplify using `at hi`.
-/
theorem mem_perp (j : Fin (r + 1)) : g j ∈ perp L S.Hm (S.spanTo g r) := by
  intro y hy
  rw [← hf_cj L S.herm.1, hf_spanTo S g hy, map_zero]
  intro i hi
  rw [gram, if_neg]
  rintro ⟨rfl, -⟩
  simp at hi

include gram in
/- English proof (translation)
Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨i, -, rfl⟩`. Conclude with `mem_perp S g T gram i`.
-/
theorem spanTo_le_perp : S.spanTo g r ≤ perp L S.Hm (S.spanTo g r) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨i, -, rfl⟩
  exact mem_perp S g T gram i

include gram in

/- English proof (translation)
Establish `key : ∀ j : Fin (r + 1), n (g j) - g j ∈ S.spanTo g j`. Introduce `j`. Use `Fin.lastCases ?_ (fun j => ?_) j` and prove the remaining obligations. Conclude with `hn.2.2 _ (mem_perp S g T gram _)`. Conclude with `(Subgroup.mem_iInf.1 hn.1.2 j).2 _ (mem_spanTo S g (by simp))`.

Use `choose c hc hc' using fun j => coords S g (key j)`. Use `⟨fun i j => c j i + if i = j then 1 else 0, ⟨fun i j hij => ?_, fun i => ?_⟩, fun j => ?_⟩` and prove the remaining obligations. Simplify using `[hc j i hij.le, hij.ne']`. Simplify using `[hc i i le_rfl]`. Simplify using `[add_smul, Finset.sum_add_distrib, ← hc' j]`.
-/
theorem exists_matrix (n : S.GLV) (hn : n ∈ S.Nof g) :
    ∃ s : Matrix (Fin (r + 1)) (Fin (r + 1)) E, ((∀ i j, j < i → s i j = 0) ∧ (∀ i, s i i = 1)) ∧
      ∀ j, n (g j) = ∑ i, s i j • g i := by
  have key : ∀ j : Fin (r + 1), n (g j) - g j ∈ S.spanTo g j := by
    intro j
    refine Fin.lastCases ?_ (fun j => ?_) j
    · exact hn.2.2 _ (mem_perp S g T gram _)
    · exact (Subgroup.mem_iInf.1 hn.1.2 j).2 _ (mem_spanTo S g (by simp))
  choose c hc hc' using fun j => coords S g (key j)
  refine ⟨fun i j => c j i + if i = j then 1 else 0, ⟨fun i j hij => ?_, fun i => ?_⟩, fun j => ?_⟩
  · simp [hc j i hij.le, hij.ne']
  · simp [hc i i le_rfl]
  · simp [add_smul, Finset.sum_add_distrib, ← hc' j]

include gram dual in
/- English proof (translation)
Use `Fin.lastCases ?_ (fun j => ⟨gs j, fun i => dual i j⟩) j` and prove the remaining obligations. Use `⟨algebraMap F E (-(T : F)⁻¹) • g (Fin.last r), fun i => ?_⟩` and prove the remaining obligations. Rewrite using `[hf_smul_r, gram, AlgEquiv.commutes]`. Distinguish the cases in `h : i = Fin.last r`. Simplify using `[h, ← map_mul]`.

Simplify using `[h]`.
-/
theorem exists_dual (j : Fin (r + 1)) : ∃ u : S.V, ∀ i, hf L S.Hm (g i) u = if i = j then 1 else 0 := by
  refine Fin.lastCases ?_ (fun j => ⟨gs j, fun i => dual i j⟩) j
  refine ⟨algebraMap F E (-(T : F)⁻¹) • g (Fin.last r), fun i => ?_⟩
  rw [hf_smul_r, gram, AlgEquiv.commutes]
  by_cases h : i = Fin.last r
  · simp [h, ← map_mul]
  · simp [h]

include gram dual in

/- English proof (translation)
Take `⟨u, hu⟩` from `exists_dual S g gs T gram dual j`. Establish `hjr : (j : ℕ) ≤ r` using `Nat.lt_succ_iff.1 j.2`. Establish `hxX : x ∈ S.spanTo g r` using `spanTo_mono S g hjr hx`. Establish `hlow : ∀ v ∈ S.spanTo g j, hf L S.Hm v u = 0` using `fun v hv => hf_spanTo S g hv fun i hi => by`. Rewrite using `[hu, if_neg]`.

Introduce and unpack `rfl`. Use linear arithmetic over natural numbers and integers. Establish `hux : hf L S.Hm u x = 0` using `by rw [← hf_cj L S.herm.1, hlow x hx, map_zero]`. Establish `hs : algebraMap F E 2⁻¹ * hf L S.Hm u u + L.cj (algebraMap F E 2⁻¹ * hf L S.Hm u u) = hf L S.Hm u u`. Rewrite using `[map_mul, AlgEquiv.commutes, hf_cj L S.herm.1, ← add_mul, ← map_add]`.

Evaluate the numerical expressions. Apply the tactic sequence `obtain ⟨n, hn, h1, h2⟩ := eichler_isometry L S.Hm S.herm x u _ (spanTo_le_perp S g T gram hxX x hxX) hux hs`. Establish `e1 : ∀ v ∈ perp L S.Hm (S.spanTo g r), n v - v = hf L S.Hm v u • x` using `fun v hv => by`. Rewrite using `[h1, eich, hv x hxX]`. Simplify using the standard rewrite rules.

Establish `e2 : ∀ v ∈ perp L S.Hm (S.spanTo g r), n⁻¹ v - v = -(hf L S.Hm v u • x)` using `fun v hv => by`. Rewrite using `[h2, eich, hv x hxX, hf_neg_r]`. Simplify using the standard rewrite rules. Establish `e3 : ∀ l : Fin r, ∀ v ∈ S.spanTo g (l + 1), hf L S.Hm v u • x ∈ S.spanTo g l`. Introduce `l v hv`.

Distinguish the cases in `h : (j : ℕ) ≤ l`. Conclude with `Submodule.smul_mem _ _ (spanTo_mono S g h hx)`. Rewrite using `[hlow v (spanTo_mono S g (by omega) hv)]; simp`. Use `⟨n, ⟨⟨hn, Subgroup.mem_iInf.2 fun l => ?_⟩, ?_⟩, ?_, fun i hi => ?_, fun v hv => ?_⟩` and prove the remaining obligations. Establish `hl : S.spanTo g (l + 1) ≤ perp L S.Hm (S.spanTo g r)` using `(spanTo_mono S g l.2).trans (spanTo_le_perp S g T gram)`.

Use `mem_unipOn (spanTo_mono S g (Nat.le_succ _)) n (fun v hv => ?_) (fun v hv => ?_)` and prove the remaining obligations. Rewrite using `[e1 v (hl hv)]`. Conclude with `e3 l v hv`. Rewrite using `[e2 v (hl hv)]`. Conclude with `Submodule.neg_mem _ (e3 l v hv)`.

Use `mem_unipOn (spanTo_le_perp S g T gram) n (fun v hv => ?_) (fun v hv => ?_)` and prove the remaining obligations. Rewrite using `[e1 v hv]`. Conclude with `Submodule.smul_mem _ _ hxX`. Rewrite using `[e2 v hv]`. Conclude with `Submodule.neg_mem _ (Submodule.smul_mem _ _ hxX)`.

Use `e1 _ (mem_perp S g T gram j)` as an intermediate fact. Rewrite `this` using `[hu, if_pos rfl, one_smul]`. Rewrite using `[← this]`. Normalize the expressions using the abelian group laws. Use `e1 _ (mem_perp S g T gram i)` as an intermediate fact.

Rewrite `this` using `[hu, if_neg hi, zero_smul]`. Conclude with `sub_eq_zero.1 this`. Use `e1 _ (spanTo_le_perp S g T gram (spanTo_mono S g hjr hv))` as an intermediate fact. Rewrite `this` using `[hlow v hv, zero_smul]`. Conclude with `sub_eq_zero.1 this`.
-/
theorem exists_step [IsNonarchimedeanLocalField F] [CharZero F] (j : Fin (r + 1)) (x : S.V)
    (hx : x ∈ S.spanTo g j) :
    ∃ n ∈ S.Nof g, n (g j) = g j + x ∧ (∀ i, i ≠ j → n (g i) = g i) ∧
      ∀ v ∈ S.spanTo g j, n v = v := by
  obtain ⟨u, hu⟩ := exists_dual S g gs T gram dual j
  have hjr : (j : ℕ) ≤ r := Nat.lt_succ_iff.1 j.2
  have hxX : x ∈ S.spanTo g r := spanTo_mono S g hjr hx
  have hlow : ∀ v ∈ S.spanTo g j, hf L S.Hm v u = 0 := fun v hv =>
    hf_spanTo S g hv fun i hi => by
      rw [hu, if_neg]
      rintro rfl
      omega
  have hux : hf L S.Hm u x = 0 := by rw [← hf_cj L S.herm.1, hlow x hx, map_zero]
  have hs : algebraMap F E 2⁻¹ * hf L S.Hm u u + L.cj (algebraMap F E 2⁻¹ * hf L S.Hm u u) =
      hf L S.Hm u u := by
    rw [map_mul, AlgEquiv.commutes, hf_cj L S.herm.1, ← add_mul, ← map_add]
    norm_num
  obtain ⟨n, hn, h1, h2⟩ := eichler_isometry L S.Hm S.herm x u _
    (spanTo_le_perp S g T gram hxX x hxX) hux hs
  have e1 : ∀ v ∈ perp L S.Hm (S.spanTo g r), n v - v = hf L S.Hm v u • x := fun v hv => by
    rw [h1, eich, hv x hxX]; simp
  have e2 : ∀ v ∈ perp L S.Hm (S.spanTo g r), n⁻¹ v - v = -(hf L S.Hm v u • x) := fun v hv => by
    rw [h2, eich, hv x hxX, hf_neg_r]; simp
  have e3 : ∀ l : Fin r, ∀ v ∈ S.spanTo g (l + 1), hf L S.Hm v u • x ∈ S.spanTo g l := by
    intro l v hv
    by_cases h : (j : ℕ) ≤ l
    · exact Submodule.smul_mem _ _ (spanTo_mono S g h hx)
    · rw [hlow v (spanTo_mono S g (by omega) hv)]; simp
  refine ⟨n, ⟨⟨hn, Subgroup.mem_iInf.2 fun l => ?_⟩, ?_⟩, ?_, fun i hi => ?_, fun v hv => ?_⟩
  · have hl : S.spanTo g (l + 1) ≤ perp L S.Hm (S.spanTo g r) :=
      (spanTo_mono S g l.2).trans (spanTo_le_perp S g T gram)
    refine mem_unipOn (spanTo_mono S g (Nat.le_succ _)) n (fun v hv => ?_) (fun v hv => ?_)
    · rw [e1 v (hl hv)]; exact e3 l v hv
    · rw [e2 v (hl hv)]; exact Submodule.neg_mem _ (e3 l v hv)
  · refine mem_unipOn (spanTo_le_perp S g T gram) n (fun v hv => ?_) (fun v hv => ?_)
    · rw [e1 v hv]; exact Submodule.smul_mem _ _ hxX
    · rw [e2 v hv]; exact Submodule.neg_mem _ (Submodule.smul_mem _ _ hxX)
  · have := e1 _ (mem_perp S g T gram j)
    rw [hu, if_pos rfl, one_smul] at this
    rw [← this]; abel
  · have := e1 _ (mem_perp S g T gram i)
    rw [hu, if_neg hi, zero_smul] at this
    exact sub_eq_zero.1 this
  · have := e1 _ (spanTo_le_perp S g T gram (spanTo_mono S g hjr hv))
    rw [hlow v hv, zero_smul] at this
    exact sub_eq_zero.1 this

include gram dual in
/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => exact ⟨1, one_mem _, fun j => by simp⟩`. Consider the case `succ m ih`. Take `⟨n, hn, h⟩` from `ih`. Distinguish the cases in `hm : m < r + 1`.

Take `⟨e, he, h1, h2, h3⟩` from `exists_step S g gs T gram dual ⟨m, hm⟩ _ (hx ⟨m, hm⟩)`. Use `⟨e * n, mul_mem he hn, fun j => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `e (n (g j)) = _`. Rewrite using `[h]`. Break down `lt_trichotomy (j : ℕ) m with hj | hj | hj` into its components or cases.

Rewrite using `[if_pos hj, if_pos (by omega)]`. Conclude with `h3 _ (add_mem (mem_spanTo S g hj) (spanTo_mono S g hj.le (hx j)))`. Take `rfl : j = ⟨m, hm⟩` from `Fin.ext hj`. Rewrite using `[if_neg (by simp), if_pos (by simp), h1]`. Rewrite using `[if_neg (by omega), if_neg (by omega)]`.

Conclude with `h2 j fun hh => by rw [hh] at hj; simp at hj`. Use `⟨n, hn, fun j => ?_⟩` and prove the remaining obligations. Use `j.2` as an intermediate fact. Rewrite using `[h, if_pos (by omega), if_pos (by omega)]`.
-/
theorem exists_upto [IsNonarchimedeanLocalField F] [CharZero F] (x : Fin (r + 1) → S.V)
    (hx : ∀ j : Fin (r + 1), x j ∈ S.spanTo g j) (m : ℕ) :
    ∃ n ∈ S.Nof g, ∀ j : Fin (r + 1), n (g j) = if (j : ℕ) < m then g j + x j else g j := by
  induction m with
  | zero => exact ⟨1, one_mem _, fun j => by simp⟩
  | succ m ih =>
    obtain ⟨n, hn, h⟩ := ih
    by_cases hm : m < r + 1
    · obtain ⟨e, he, h1, h2, h3⟩ := exists_step S g gs T gram dual ⟨m, hm⟩ _ (hx ⟨m, hm⟩)
      refine ⟨e * n, mul_mem he hn, fun j => ?_⟩
      change e (n (g j)) = _
      rw [h]
      rcases lt_trichotomy (j : ℕ) m with hj | hj | hj
      · rw [if_pos hj, if_pos (by omega)]
        exact h3 _ (add_mem (mem_spanTo S g hj) (spanTo_mono S g hj.le (hx j)))
      · obtain rfl : j = ⟨m, hm⟩ := Fin.ext hj
        rw [if_neg (by simp), if_pos (by simp), h1]
      · rw [if_neg (by omega), if_neg (by omega)]
        exact h2 j fun hh => by rw [hh] at hj; simp at hj
    · refine ⟨n, hn, fun j => ?_⟩
      have := j.2
      rw [h, if_pos (by omega), if_pos (by omega)]

include gram dual in

/- English proof (translation)
Establish `hx : ∀ j : Fin (r + 1), ∑ i ∈ Finset.univ.erase j, s i j • g i ∈ S.spanTo g j`. Introduce `j`. Use `Submodule.sum_mem _ fun i hi => ?_` and prove the remaining obligations. Break down `lt_or_gt_of_ne (Finset.ne_of_mem_erase hi) with h | h` into its components or cases. Conclude with `Submodule.smul_mem _ _ (mem_spanTo S g h)`.

Rewrite using `[hs.1 i j h]`. Simplify using the standard rewrite rules. Take `⟨n, hn, h⟩` from `exists_upto S g gs T gram dual _ hx (r + 1)`. Use `⟨n, hn, fun j => ?_⟩` and prove the remaining obligations. Rewrite using `[h, if_pos j.2, ← Finset.add_sum_erase _ _ (Finset.mem_univ j), hs.2, one_smul]`.
-/
theorem exists_elt [IsNonarchimedeanLocalField F] [CharZero F]
    (s : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (hs : (∀ i j, j < i → s i j = 0) ∧ (∀ i, s i i = 1)) :
    ∃ n ∈ S.Nof g, ∀ j, n (g j) = ∑ i, s i j • g i := by
  have hx : ∀ j : Fin (r + 1), ∑ i ∈ Finset.univ.erase j, s i j • g i ∈ S.spanTo g j := by
    intro j
    refine Submodule.sum_mem _ fun i hi => ?_
    rcases lt_or_gt_of_ne (Finset.ne_of_mem_erase hi) with h | h
    · exact Submodule.smul_mem _ _ (mem_spanTo S g h)
    · rw [hs.1 i j h]; simp
  obtain ⟨n, hn, h⟩ := exists_upto S g gs T gram dual _ hx (r + 1)
  refine ⟨n, hn, fun j => ?_⟩
  rw [h, if_pos j.2, ← Finset.add_sum_erase _ _ (Finset.mem_univ j), hs.2, one_smul]

end

/- English proof (translation)
Introduce `F _ _ _ _ _ E _ _ _ L r k S`. Conclude with `⟨exists_matrix S S.f S.T S.gram, exists_matrix S S.f' S.T' S.gram', fun s hs => ⟨exists_elt S S.f S.es S.T S.gram S.dual s hs, exists_elt S S.f' S.es' S.T' S.gram' S.dual' s hs⟩⟩`.
-/
theorem unipotent_onto : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), (∀ n ∈ S.N, ∃ s : Matrix (Fin (r + 1)) (Fin (r + 1)) E, ((∀ i j, j < i → s i j = 0) ∧ (∀ i, s i i = 1)) ∧ ∀ j, n (S.f j) = ∑ i, s i j • S.f i) ∧ (∀ n ∈ S.N', ∃ s : Matrix (Fin (r + 1)) (Fin (r + 1)) E, ((∀ i j, j < i → s i j = 0) ∧ (∀ i, s i i = 1)) ∧ ∀ j, n (S.f' j) = ∑ i, s i j • S.f' i) ∧ ∀ s : Matrix (Fin (r + 1)) (Fin (r + 1)) E, ((∀ i j, j < i → s i j = 0) ∧ (∀ i, s i i = 1)) → (∃ n ∈ S.N, ∀ j, n (S.f j) = ∑ i, s i j • S.f i) ∧ ∃ n ∈ S.N', ∀ j, n (S.f' j) = ∑ i, s i j • S.f' i := by
  intro F _ _ _ _ _ E _ _ _ L r k S
  exact ⟨exists_matrix S S.f S.T S.gram, exists_matrix S S.f' S.T' S.gram', fun s hs =>
    ⟨exists_elt S S.f S.es S.T S.gram S.dual s hs, exists_elt S S.f' S.es' S.T' S.gram' S.dual' s hs⟩⟩

end GlobalTheory.HL.FrameOnto
