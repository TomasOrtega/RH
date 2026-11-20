import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormAdditiveCharacterTypePrimeEqOne
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SpanToLePerp
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemPerpSpan
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.WitIndep
open GlobalTheory.HL.Eichler

section
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

/- English proof (translation)
Unfold `Frames.th`. Use `split_ifs`. Conclude with `fun h => S.ϖ_irr.ne_zero (Subtype.ext h)`. Conclude with `one_ne_zero`.
-/
theorem th_ne : S.th ≠ 0 := by
  unfold Frames.th
  split_ifs
  · exact fun h => S.ϖ_irr.ne_zero (Subtype.ext h)
  · exact one_ne_zero

/- English proof (translation)
Rewrite using `[← map_mul, inv_mul_cancel₀ (th_ne S), map_one]`.
-/
theorem th_mul : algebraMap F E S.th⁻¹ * algebraMap F E S.th = 1 := by
  rw [← map_mul, inv_mul_cancel₀ (th_ne S), map_one]

/- English proof (translation)
Simplify using `only [Finset.smul_sum, Finset.sum_smul, smul_smul]`. Rewrite using `[Finset.sum_comm]`. Simplify using `only [mul_comm]`.
-/
theorem sum_sum {m : ℕ} {V : Type} [AddCommGroup V] [Module E V] (g : Fin m → V)
    (A : Matrix (Fin m) (Fin m) E) (b : Fin m → E) :
    ∑ j, b j • ∑ i, A i j • g i = ∑ i, (∑ j, A i j * b j) • g i := by
  simp only [Finset.smul_sum, Finset.sum_smul, smul_smul]
  rw [Finset.sum_comm]
  simp only [mul_comm]

/- English proof (translation)
Take `⟨A, A', hA, hA', h0, h1, hc, e, e'⟩` from `H`. Introduce and unpack `p ⟨B, B', hB, hB', k0, k1, kc, d, d'⟩`. Establish `tri : ∀ i j l : Fin (r + 1), (j < i ∨ (i = j ∧ l ≠ i)) → A i l * B l j = 0 ∧ A' i l * B' l j = 0`. Introduce `i j l hh`. Distinguish the cases in `hl : l < i`.

Simplify using `[h0 i l hl]`. Establish `: j < l`. Break down `hh with hh | ⟨rfl, hh⟩` into its components or cases. Conclude with `lt_of_lt_of_le hh (not_lt.1 hl)`. Conclude with `lt_of_le_of_ne (not_lt.1 hl) hh.symm`.

Simplify using `[k0 l j this]`. Use `⟨A * B, A' * B', fun i j => ?_, fun i j => ?_, fun i j hij => ?_, fun i => ?_, fun i j => ?_, fun j => ?_, fun j => ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.mul_apply]`. Conclude with `L.O.sum_mem fun l _ => L.O.mul_mem (hA i l) (hB l j)`. Rewrite using `[Matrix.mul_apply]`.

Conclude with `L.O.sum_mem fun l _ => L.O.mul_mem (hA' i l) (hB' l j)`. Rewrite using `[Matrix.mul_apply, Matrix.mul_apply]`. Conclude with `⟨Finset.sum_eq_zero fun l _ => (tri i j l (.inl hij)).1, Finset.sum_eq_zero fun l _ => (tri i j l (.inl hij)).2⟩`. Prove the components needed by the constructor for the conclusion. Rewrite using `[Matrix.mul_apply, Finset.sum_eq_single i (fun l _ hl => (tri i i l (.inr ⟨rfl, hl⟩)).1) (by simp), (h1 i).1, (k1 i).1, one_mul]`.

Rewrite using `[Matrix.mul_apply, Finset.sum_eq_single i (fun l _ hl => (tri i i l (.inr ⟨rfl, hl⟩)).2) (by simp), (h1 i).2, (k1 i).2, one_mul]`. Use `choose c hcO hc using hc choose c' hcO' kc using kc`. Use `⟨∑ l, (c i l * B' l j + A i l * c' l j), L.O.sum_mem fun l _ => L.O.add_mem (L.O.mul_mem (hcO i l) (hB' l j)) (L.O.mul_mem (hA i l) (hcO' l j)), ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.mul_apply, Matrix.mul_apply, ← Finset.sum_sub_distrib, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations.

Take the linear combination `B' l j * hc i l + A i l * kc l j`. Simplify using `only at e`. Rewrite using `[d]`. Simplify using `only [e, sum_sum, Matrix.mul_apply]`. Simplify using `only at e'`.

Rewrite using `[d']`. Simplify using `only [e', sum_sum, Matrix.mul_apply]`.
-/
theorem cls_subset {g g' h h' : Fin (r + 1) → S.V} (H : (h, h') ∈ S.frameCls g g') :
    S.frameCls h h' ⊆ S.frameCls g g' := by
  obtain ⟨A, A', hA, hA', h0, h1, hc, e, e'⟩ := H
  rintro p ⟨B, B', hB, hB', k0, k1, kc, d, d'⟩
  have tri : ∀ i j l : Fin (r + 1), (j < i ∨ (i = j ∧ l ≠ i)) →
      A i l * B l j = 0 ∧ A' i l * B' l j = 0 := by
    intro i j l hh
    by_cases hl : l < i
    · simp [h0 i l hl]
    · have : j < l := by
        rcases hh with hh | ⟨rfl, hh⟩
        · exact lt_of_lt_of_le hh (not_lt.1 hl)
        · exact lt_of_le_of_ne (not_lt.1 hl) hh.symm
      simp [k0 l j this]
  refine ⟨A * B, A' * B', fun i j => ?_, fun i j => ?_, fun i j hij => ?_, fun i => ?_,
    fun i j => ?_, fun j => ?_, fun j => ?_⟩
  · rw [Matrix.mul_apply]
    exact L.O.sum_mem fun l _ => L.O.mul_mem (hA i l) (hB l j)
  · rw [Matrix.mul_apply]
    exact L.O.sum_mem fun l _ => L.O.mul_mem (hA' i l) (hB' l j)
  · rw [Matrix.mul_apply, Matrix.mul_apply]
    exact ⟨Finset.sum_eq_zero fun l _ => (tri i j l (.inl hij)).1,
      Finset.sum_eq_zero fun l _ => (tri i j l (.inl hij)).2⟩
  · constructor
    · rw [Matrix.mul_apply, Finset.sum_eq_single i (fun l _ hl => (tri i i l (.inr ⟨rfl, hl⟩)).1)
        (by simp), (h1 i).1, (k1 i).1, one_mul]
    · rw [Matrix.mul_apply, Finset.sum_eq_single i (fun l _ hl => (tri i i l (.inr ⟨rfl, hl⟩)).2)
        (by simp), (h1 i).2, (k1 i).2, one_mul]
  · choose c hcO hc using hc
    choose c' hcO' kc using kc
    refine ⟨∑ l, (c i l * B' l j + A i l * c' l j), L.O.sum_mem fun l _ =>
      L.O.add_mem (L.O.mul_mem (hcO i l) (hB' l j)) (L.O.mul_mem (hA i l) (hcO' l j)), ?_⟩
    rw [Matrix.mul_apply, Matrix.mul_apply, ← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    linear_combination B' l j * hc i l + A i l * kc l j
  · simp only at e
    rw [d]
    simp only [e, sum_sum, Matrix.mul_apply]
  · simp only at e'
    rw [d']
    simp only [e', sum_sum, Matrix.mul_apply]

/- English proof (translation)
Take `⟨A, A', hA, hA', -, -, hc, e, e'⟩` from `H`. Simplify using `only at e e'`. Use `choose c hcO hc using hc`. Establish `m1 : ∀ i, g i ∈ S.Mof g g'` using `fun i => Submodule.subset_span (.inl ⟨i, rfl⟩)`. Establish `m2 : ∀ i, algebraMap F E S.th⁻¹ • (g' i - g i) ∈ S.Mof g g'` using `fun i => Submodule.subset_span (.inr ⟨i, rfl⟩)`.

Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ (⟨j, rfl⟩ | ⟨j, rfl⟩)`. Rewrite using `[e]`. Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ (⟨_, hA i j⟩ : L.O) (m1 i)`. Establish `: algebraMap F E S.th⁻¹ • (h' j - h j) = ∑ i, (A' i j • algebraMap F E S.th⁻¹ • (g' i - g i) + c i j • g i)`.

Rewrite using `[e, e', ← Finset.sum_sub_distrib, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Establish `h3 : c i j = algebraMap F E S.th⁻¹ * (A' i j - A i j)`. Rewrite using `[hc, ← mul_assoc, th_mul, one_mul]`. Rewrite using `[h3]`.

Use `module`. Simplify using `only [SetLike.mem_coe, this]`. Conclude with `Submodule.sum_mem _ fun i _ => Submodule.add_mem _ (Submodule.smul_mem _ (⟨_, hA' i j⟩ : L.O) (m2 i)) (Submodule.smul_mem _ (⟨_, hcO i j⟩ : L.O) (m1 i))`.
-/
theorem Mof_le {g g' h h' : Fin (r + 1) → S.V} (H : (h, h') ∈ S.frameCls g g') :
    S.Mof h h' ≤ S.Mof g g' := by
  obtain ⟨A, A', hA, hA', -, -, hc, e, e'⟩ := H
  simp only at e e'
  choose c hcO hc using hc
  have m1 : ∀ i, g i ∈ S.Mof g g' := fun i => Submodule.subset_span (.inl ⟨i, rfl⟩)
  have m2 : ∀ i, algebraMap F E S.th⁻¹ • (g' i - g i) ∈ S.Mof g g' := fun i =>
    Submodule.subset_span (.inr ⟨i, rfl⟩)
  refine Submodule.span_le.2 ?_
  rintro _ (⟨j, rfl⟩ | ⟨j, rfl⟩)
  · rw [e]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ (⟨_, hA i j⟩ : L.O) (m1 i)
  · have : algebraMap F E S.th⁻¹ • (h' j - h j) =
        ∑ i, (A' i j • algebraMap F E S.th⁻¹ • (g' i - g i) + c i j • g i) := by
      rw [e, e', ← Finset.sum_sub_distrib, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      have h3 : c i j = algebraMap F E S.th⁻¹ * (A' i j - A i j) := by
        rw [hc, ← mul_assoc, th_mul, one_mul]
      rw [h3]
      module
    simp only [SetLike.mem_coe, this]
    exact Submodule.sum_mem _ fun i _ => Submodule.add_mem _
      (Submodule.smul_mem _ (⟨_, hA' i j⟩ : L.O) (m2 i))
      (Submodule.smul_mem _ (⟨_, hcO i j⟩ : L.O) (m1 i))

/- English proof (translation)
Take `⟨A, A', hA, hA', h0, -, hc, e, e'⟩` from `H`. Simplify using `only at e e'`. Take `⟨al, al', rfl, hR⟩` from `hb`. Use `⟨fun i => ∑ l, A i l * al l, fun i => ∑ l, A' i l * al' l, by simp only [e, e', sum_sum], fun i hi => ?_⟩` and prove the remaining obligations. Establish `key : ∀ l, S.RR (A i l * al l) (A' i l * al' l)`.

Introduce `l`. Distinguish the cases in `hl : l < i`. Rewrite using `[(h0 i l hl).1, (h0 i l hl).2, zero_mul, zero_mul]`. Conclude with `⟨L.O.zero_mem, 0, L.O.zero_mem, by simp⟩`. Take `⟨h1, c, hcO, h2⟩` from `hR l (hi.trans (not_lt.1 hl))`.

Take `⟨d, hdO, h3⟩` from `hc i l`. Conclude with `⟨L.O.mul_mem (hA' i l) h1, A i l * c + d * al' l, L.O.add_mem (L.O.mul_mem (hA i l) hcO) (L.O.mul_mem hdO h1), by linear_combination A i l * h2 + al' l * h3⟩`. Use `⟨L.O.sum_mem fun l _ => (key l).1, ?_⟩` and prove the remaining obligations. Use `choose c hcO hc using fun l => (key l).2`. Use `⟨∑ l, c l, L.O.sum_mem fun l _ => hcO l, ?_⟩` and prove the remaining obligations.

Simplify using `only [← Finset.sum_add_distrib, hc, Finset.mul_sum]`.
-/
theorem lev_step {g g' h h' : Fin (r + 1) → S.V} (H : (h, h') ∈ S.frameCls g g') (b : S.V) (j : ℕ)
    (hb : ∃ al al' : Fin (r + 1) → E, b = ∑ i, al i • h i + ∑ i, al' i • h' i ∧
      ∀ i : Fin (r + 1), j ≤ (i : ℕ) → S.RR (al i) (al' i)) :
    ∃ al al' : Fin (r + 1) → E, b = ∑ i, al i • g i + ∑ i, al' i • g' i ∧
      ∀ i : Fin (r + 1), j ≤ (i : ℕ) → S.RR (al i) (al' i) := by
  obtain ⟨A, A', hA, hA', h0, -, hc, e, e'⟩ := H
  simp only at e e'
  obtain ⟨al, al', rfl, hR⟩ := hb
  refine ⟨fun i => ∑ l, A i l * al l, fun i => ∑ l, A' i l * al' l, by simp only [e, e', sum_sum],
    fun i hi => ?_⟩
  have key : ∀ l, S.RR (A i l * al l) (A' i l * al' l) := by
    intro l
    by_cases hl : l < i
    · rw [(h0 i l hl).1, (h0 i l hl).2, zero_mul, zero_mul]
      exact ⟨L.O.zero_mem, 0, L.O.zero_mem, by simp⟩
    · obtain ⟨h1, c, hcO, h2⟩ := hR l (hi.trans (not_lt.1 hl))
      obtain ⟨d, hdO, h3⟩ := hc i l
      exact ⟨L.O.mul_mem (hA' i l) h1, A i l * c + d * al' l,
        L.O.add_mem (L.O.mul_mem (hA i l) hcO) (L.O.mul_mem hdO h1),
        by linear_combination A i l * h2 + al' l * h3⟩
  refine ⟨L.O.sum_mem fun l _ => (key l).1, ?_⟩
  choose c hcO hc using fun l => (key l).2
  refine ⟨∑ l, c l, L.O.sum_mem fun l _ => hcO l, ?_⟩
  simp only [← Finset.sum_add_distrib, hc, Finset.mul_sum]

variable [IsNonarchimedeanLocalField F] [CharZero F]

/- English proof (translation)
Establish `h1 : ∑ i, c i • n (g i) = n • ∑ i, c i • g i`. Express the relevant statement in the definitionally equal form `_ = n (∑ i, c i • g i)`. Simplify using the standard rewrite rules. Establish `h2` using `(StdLat.stdLat_spec L r k S g gs hg A hA).2.1 (r + 1) le_rfl (∑ i, c i • g i)`. Establish `h3 : ∑ i, c i • g i ∈ S.spanTo g (r + 1)` using `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (FrameOnto.mem_spanTo S g i.2)`.

Establish `h4 : g '' {i | (i : ℕ) < r + 1} = Set.range g`. Use extensionality with `x`. Simplify using `[Fin.is_le]`. Establish `h5 : ∀ j, ∃ u : S.V, ∀ i, hf L S.Hm (g i) u = if i = j then 1 else 0`. Break down `hg with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩` into its components or cases.

Conclude with `FrameOnto.exists_dual S _ _ S.T S.gram S.dual`. Conclude with `FrameOnto.exists_dual S _ _ S.T' S.gram' S.dual'`. Establish `h6 : ∀ x : S.V, n • x ∈ n • S.stdLat g gs A ↔ x ∈ S.stdLat g gs A` using `fun x => by`. Rewrite using `[Submodule.mem_smul_pointwise_iff_exists]`. Conclude with `⟨fun ⟨y, hy, e⟩ => MulAction.injective n e ▸ hy, fun h => ⟨x, h, rfl⟩⟩`.

Rewrite using `[h1, h6, ((and_iff_left h3).symm.trans h2), h4, Submodule.mem_span_range_iff_exists_fun]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨d, hd⟩ j`. Take `⟨u, hu⟩` from `h5 j`. Use `congrArg (fun x => hf L S.Hm x u) hd` as an intermediate fact.

Establish `e : ∀ i, d i • g i = (d i : E) • g i` using `fun _ => rfl`. Simplify using `[e, StdLat.hf_sum_l, hf_smul_l, hu] at this`. Rewrite using `[← this]`. Conclude with `(d j).2`. Conclude with `fun h => ⟨fun i => ⟨c i, h i⟩, rfl⟩`.
-/
theorem coords_mem (g : Fin (r + 1) → S.V) (gs : Fin r → S.V)
    (hg : (g = S.f ∧ gs = S.es) ∨ (g = S.f' ∧ gs = S.es')) (A : Submodule L.O S.V)
    (hA : S.IsInner g gs A) (n : S.GLV) (c : Fin (r + 1) → E) :
    ∑ i, c i • n (g i) ∈ n • S.stdLat g gs A ↔ ∀ i, c i ∈ L.O := by
  have h1 : ∑ i, c i • n (g i) = n • ∑ i, c i • g i := by
    change _ = n (∑ i, c i • g i)
    simp
  have h2 := (StdLat.stdLat_spec L r k S g gs hg A hA).2.1 (r + 1) le_rfl (∑ i, c i • g i)
  have h3 : ∑ i, c i • g i ∈ S.spanTo g (r + 1) := Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ _ (FrameOnto.mem_spanTo S g i.2)
  have h4 : g '' {i | (i : ℕ) < r + 1} = Set.range g := by
    ext x; simp [Fin.is_le]
  have h5 : ∀ j, ∃ u : S.V, ∀ i, hf L S.Hm (g i) u = if i = j then 1 else 0 := by
    rcases hg with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact FrameOnto.exists_dual S _ _ S.T S.gram S.dual
    · exact FrameOnto.exists_dual S _ _ S.T' S.gram' S.dual'
  have h6 : ∀ x : S.V, n • x ∈ n • S.stdLat g gs A ↔ x ∈ S.stdLat g gs A := fun x => by
    rw [Submodule.mem_smul_pointwise_iff_exists]
    exact ⟨fun ⟨y, hy, e⟩ => MulAction.injective n e ▸ hy, fun h => ⟨x, h, rfl⟩⟩
  rw [h1, h6, ((and_iff_left h3).symm.trans h2), h4,
    Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨d, hd⟩ j
    obtain ⟨u, hu⟩ := h5 j
    have := congrArg (fun x => hf L S.Hm x u) hd
    have e : ∀ i, d i • g i = (d i : E) • g i := fun _ => rfl
    simp [e, StdLat.hf_sum_l, hf_smul_l, hu] at this
    rw [← this]
    exact (d j).2
  · exact fun h => ⟨fun i => ⟨c i, h i⟩, rfl⟩

/- English proof (translation)
Use `(coords_mem S g gs hg A hA n (Pi.single j 1)).2 fun i => by` as an intermediate fact. Rewrite using `[Pi.single_apply]`. Use `split_ifs`. Use `exacts [L.O.one_mem, L.O.zero_mem]`. Simplify `this` using `[Pi.single_apply]`.
-/
theorem frame_mem (g : Fin (r + 1) → S.V) (gs : Fin r → S.V)
    (hg : (g = S.f ∧ gs = S.es) ∨ (g = S.f' ∧ gs = S.es')) (A : Submodule L.O S.V)
    (hA : S.IsInner g gs A) (n : S.GLV) (j : Fin (r + 1)) : n (g j) ∈ n • S.stdLat g gs A := by
  have := (coords_mem S g gs hg A hA n (Pi.single j 1)).2 fun i => by
    rw [Pi.single_apply]
    split_ifs
    exacts [L.O.one_mem, L.O.zero_mem]
  simpa [Pi.single_apply] using this

/- English proof (translation)
Take `⟨hI, hI', hn, hn', e, e', ht, -⟩` from `H`. Take `⟨-, -, hm, hm', f, f', kt, -⟩` from `K`. Establish `hs` using `mul_mem (inv_mem hn) hm`. Establish `hs'` using `mul_mem (inv_mem hn') hm'`. Take `⟨A, ⟨h0, h1⟩, hA⟩` from `FrameOnto.exists_matrix S S.f S.T S.gram _ hs`.

Take `⟨A', ⟨h0', h1'⟩, hA'⟩` from `FrameOnto.exists_matrix S S.f' S.T' S.gram' _ hs'`. Establish `a1 : ∀ j, m (S.f j) = ∑ i, A i j • n (S.f i)` using `fun j => by`. Use `congrArg n (hA j)` as an intermediate fact. Rewrite `this` using `[show n ((n⁻¹ * m) (S.f j)) = m (S.f j) from n.apply_symm_apply _]`. Simplify using `using this`.

Establish `a1' : ∀ j, m' (S.f' j) = ∑ i, A' i j • n' (S.f' i)` using `fun j => by`. Use `congrArg n' (hA' j)` as an intermediate fact. Rewrite `this` using `[show n' ((n'⁻¹ * m') (S.f' j)) = m' (S.f' j) from n'.apply_symm_apply _]`. Simplify using `using this`. Establish `c1` using `coords_mem S S.f S.es (.inl ⟨rfl, rfl⟩) _ hI n`.

Establish `c1'` using `coords_mem S S.f' S.es' (.inr ⟨rfl, rfl⟩) _ hI' n'`. Rewrite `c1` using `[← e]`. Rewrite `c1'` using `[← e']`. Establish `iA : IsIntM L A` using `fun i j => (c1 fun i => A i j).1 (by`. Rewrite using `[← a1, f]`.

Conclude with `frame_mem S S.f S.es (.inl ⟨rfl, rfl⟩) _ hI m j) i`. Establish `iA' : IsIntM L A'` using `fun i j => (c1' fun i => A' i j).1 (by`. Rewrite using `[← a1', f']`. Conclude with `frame_mem S S.f' S.es' (.inr ⟨rfl, rfl⟩) _ hI' m' j) i`. Establish `cg : ∀ i j, algebraMap F E S.th⁻¹ * (A' i j - A i j) ∈ L.O`.

Introduce `i j`. Use `choose y hy hy' using ht`. Take `⟨z, hz, hz'⟩` from `kt j`. Use `(c1 fun i => algebraMap F E S.th⁻¹ * (A' i j - A i j)).1 ?_ i` and prove the remaining obligations. Establish `b1 : ∀ i, y i = algebraMap F E S.th⁻¹ • (n' (S.f' i) - n (S.f i))` using `fun i => by`.

Rewrite using `[hy', smul_smul, th_mul, one_smul]`. Establish `b2 : z = algebraMap F E S.th⁻¹ • (m' (S.f' j) - m (S.f j))`. Rewrite using `[hz', smul_smul, th_mul, one_smul]`. Establish `: ∑ i, (algebraMap F E S.th⁻¹ * (A' i j - A i j)) • n (S.f i) = z - ∑ i, A' i j • y i`. Rewrite using `[b2, a1, a1', ← Finset.sum_sub_distrib, Finset.smul_sum, ← Finset.sum_sub_distrib]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[b1]`. Use `module`. Rewrite using `[this]`. Conclude with `Λ.sub_mem hz (Λ.sum_mem fun i _ => Λ.smul_mem (⟨_, iA' i j⟩ : L.O) (hy i))`.

Use `⟨⟨A, A', iA, iA', fun i j h => ⟨h0 i j h, h0' i j h⟩, fun i => ⟨h1 i, h1' i⟩, fun i j => ⟨_, cg i j, ?_⟩, a1, a1'⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[← mul_assoc, mul_comm (algebraMap F E S.th), th_mul, one_mul]`. Take `⟨p1, p2, p3, -⟩` from `FramePsi.psi_unitary_character L r k S`. Establish `q1` using `p1 n hn _ hs`. Establish `q2` using `p2 n' hn' _ hs'`.

Rewrite `q1`, `q2` using `[mul_inv_cancel_left]`. Establish `k1 : ∀ j, S.coef S.f S.es (n⁻¹ * m) j = A j.castSucc j.succ` using `fun j => by`. Simplify using `only [Frames.coef, Frames.h, hA, StdLat.hf_sum_l, hf_smul_l, S.dual]`. Simplify using the standard rewrite rules. Establish `k2 : ∀ j, S.coef S.f' S.es' (n'⁻¹ * m') j = A' j.castSucc j.succ` using `fun j => by`.

Simplify using `only [Frames.coef, Frames.h, hA', StdLat.hf_sum_l, hf_smul_l, S.dual']`. Simplify using the standard rewrite rules. Establish `q3 : S.psi' (n'⁻¹ * m') = S.psi (n⁻¹ * m)`. Establish `hO : ∑ j : Fin r, algebraMap F E S.th⁻¹ * (A' j.castSucc j.succ - A j.castSucc j.succ) ∈ L.O` using `L.O.sum_mem fun j _ => cg _ _`. Establish `h2` using `(L.additive_character_dual_ring _).2 hO 1 L.O.one_mem`.

Simplify using `only [Frames.psi, Frames.psi', Frames.psiOf, k1, k2]`. Rewrite using `[← mul_one (L.psi0 (_ * ∑ j : Fin r, A _ _)), ← h2, ← AddChar.map_add_eq_mul, mul_one, ← Finset.mul_sum, Finset.sum_sub_distrib]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Establish `q4 : S.psi (n⁻¹ * m) ≠ 0` using `fun h => by simpa [h] using (p3 (n⁻¹ * m)).1`.

Rewrite using `[q1, q2, q3, mul_inv]`. Clear the denominators using the available nonvanishing facts.
-/
theorem compare {d : S.Datum} {Λ : Submodule L.O S.V} {n n' m m' : S.GLV}
    (H : S.IsTermW d Λ n n') (K : S.IsTermW d Λ m m') :
    (fun b => m (S.f b), fun b => m' (S.f' b)) ∈ S.frameCls (fun b => n (S.f b)) (fun b => n' (S.f' b)) ∧
      S.psi m * (S.psi' m')⁻¹ = S.psi n * (S.psi' n')⁻¹ := by
  obtain ⟨hI, hI', hn, hn', e, e', ht, -⟩ := H
  obtain ⟨-, -, hm, hm', f, f', kt, -⟩ := K
  have hs := mul_mem (inv_mem hn) hm
  have hs' := mul_mem (inv_mem hn') hm'
  obtain ⟨A, ⟨h0, h1⟩, hA⟩ := FrameOnto.exists_matrix S S.f S.T S.gram _ hs
  obtain ⟨A', ⟨h0', h1'⟩, hA'⟩ := FrameOnto.exists_matrix S S.f' S.T' S.gram' _ hs'
  have a1 : ∀ j, m (S.f j) = ∑ i, A i j • n (S.f i) := fun j => by
    have := congrArg n (hA j)
    rw [show n ((n⁻¹ * m) (S.f j)) = m (S.f j) from n.apply_symm_apply _] at this
    simpa using this
  have a1' : ∀ j, m' (S.f' j) = ∑ i, A' i j • n' (S.f' i) := fun j => by
    have := congrArg n' (hA' j)
    rw [show n' ((n'⁻¹ * m') (S.f' j)) = m' (S.f' j) from n'.apply_symm_apply _] at this
    simpa using this
  have c1 := coords_mem S S.f S.es (.inl ⟨rfl, rfl⟩) _ hI n
  have c1' := coords_mem S S.f' S.es' (.inr ⟨rfl, rfl⟩) _ hI' n'
  rw [← e] at c1
  rw [← e'] at c1'
  have iA : IsIntM L A := fun i j => (c1 fun i => A i j).1 (by
    rw [← a1, f]; exact frame_mem S S.f S.es (.inl ⟨rfl, rfl⟩) _ hI m j) i
  have iA' : IsIntM L A' := fun i j => (c1' fun i => A' i j).1 (by
    rw [← a1', f']; exact frame_mem S S.f' S.es' (.inr ⟨rfl, rfl⟩) _ hI' m' j) i
  have cg : ∀ i j, algebraMap F E S.th⁻¹ * (A' i j - A i j) ∈ L.O := by
    intro i j
    choose y hy hy' using ht
    obtain ⟨z, hz, hz'⟩ := kt j
    refine (c1 fun i => algebraMap F E S.th⁻¹ * (A' i j - A i j)).1 ?_ i
    have b1 : ∀ i, y i = algebraMap F E S.th⁻¹ • (n' (S.f' i) - n (S.f i)) := fun i => by
      rw [hy', smul_smul, th_mul, one_smul]
    have b2 : z = algebraMap F E S.th⁻¹ • (m' (S.f' j) - m (S.f j)) := by
      rw [hz', smul_smul, th_mul, one_smul]
    have : ∑ i, (algebraMap F E S.th⁻¹ * (A' i j - A i j)) • n (S.f i) = z - ∑ i, A' i j • y i := by
      rw [b2, a1, a1', ← Finset.sum_sub_distrib, Finset.smul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [b1]
      module
    rw [this]
    exact Λ.sub_mem hz (Λ.sum_mem fun i _ => Λ.smul_mem (⟨_, iA' i j⟩ : L.O) (hy i))
  refine ⟨⟨A, A', iA, iA', fun i j h => ⟨h0 i j h, h0' i j h⟩, fun i => ⟨h1 i, h1' i⟩,
    fun i j => ⟨_, cg i j, ?_⟩, a1, a1'⟩, ?_⟩
  · rw [← mul_assoc, mul_comm (algebraMap F E S.th), th_mul, one_mul]
  · obtain ⟨p1, p2, p3, -⟩ := FramePsi.psi_unitary_character L r k S
    have q1 := p1 n hn _ hs
    have q2 := p2 n' hn' _ hs'
    rw [mul_inv_cancel_left] at q1 q2
    have k1 : ∀ j, S.coef S.f S.es (n⁻¹ * m) j = A j.castSucc j.succ := fun j => by
      simp only [Frames.coef, Frames.h, hA, StdLat.hf_sum_l, hf_smul_l, S.dual]
      simp
    have k2 : ∀ j, S.coef S.f' S.es' (n'⁻¹ * m') j = A' j.castSucc j.succ := fun j => by
      simp only [Frames.coef, Frames.h, hA', StdLat.hf_sum_l, hf_smul_l, S.dual']
      simp
    have q3 : S.psi' (n'⁻¹ * m') = S.psi (n⁻¹ * m) := by
      have hO : ∑ j : Fin r, algebraMap F E S.th⁻¹ * (A' j.castSucc j.succ - A j.castSucc j.succ) ∈ L.O :=
        L.O.sum_mem fun j _ => cg _ _
      have h2 := (L.additive_character_dual_ring _).2 hO 1 L.O.one_mem
      simp only [Frames.psi, Frames.psi', Frames.psiOf, k1, k2]
      rw [← mul_one (L.psi0 (_ * ∑ j : Fin r, A _ _)), ← h2, ← AddChar.map_add_eq_mul, mul_one,
        ← Finset.mul_sum, Finset.sum_sub_distrib]
      congr 1
      ring
    have q4 : S.psi (n⁻¹ * m) ≠ 0 := fun h => by simpa [h] using (p3 (n⁻¹ * m)).1
    rw [q1, q2, q3, mul_inv]
    field_simp

end

/- English proof (translation)
Introduce `F _ _ _ _ _ E _ _ _ L r k S d Λ n n' H`. Establish `hT : S.IsTerm d Λ` using `⟨(n, n'), H⟩`. Establish `K : S.IsTermW d Λ (S.wit d Λ).1 (S.wit d Λ).2`. Rewrite using `[Frames.wit, dif_pos hT]`. Conclude with `hT.choose_spec`.

Take `⟨c1, w1⟩` from `compare S H K`. Take `⟨c2, -⟩` from `compare S K H`. Use `⟨w1, le_antisymm (Mof_le S c1) (Mof_le S c2), Set.Subset.antisymm (cls_subset S c1) (cls_subset S c2), fun y => ?_, ?_⟩` and prove the remaining obligations. Conclude with `congrArg sInf (Set.ext fun j => ⟨lev_step S c1 y j, lev_step S c2 y j⟩)`. Take `⟨-, -, p3, -⟩` from `FramePsi.psi_unitary_character L r k S`.

Rewrite using `[Frames.om, norm_mul, norm_inv, (p3 _).1, (p3 _).2]`. Simplify using the standard rewrite rules.
-/
theorem witness_independence : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ d Λ n n', S.IsTermW d Λ n n' → S.om d Λ = S.psi n * (S.psi' n')⁻¹ ∧ S.M d Λ = S.Mof (fun b => n (S.f b)) (fun b => n' (S.f' b)) ∧ S.Fr d Λ = S.frameCls (fun b => n (S.f b)) (fun b => n' (S.f' b)) ∧ (∀ y, S.lev (S.fr d Λ) (S.fr' d Λ) y = S.lev (fun b => n (S.f b)) (fun b => n' (S.f' b)) y) ∧ ‖S.om d Λ‖ = 1 := by
  intro F _ _ _ _ _ E _ _ _ L r k S d Λ n n' H
  have hT : S.IsTerm d Λ := ⟨(n, n'), H⟩
  have K : S.IsTermW d Λ (S.wit d Λ).1 (S.wit d Λ).2 := by
    rw [Frames.wit, dif_pos hT]
    exact hT.choose_spec
  obtain ⟨c1, w1⟩ := compare S H K
  obtain ⟨c2, -⟩ := compare S K H
  refine ⟨w1, le_antisymm (Mof_le S c1) (Mof_le S c2),
    Set.Subset.antisymm (cls_subset S c1) (cls_subset S c2), fun y => ?_, ?_⟩
  · exact congrArg sInf (Set.ext fun j => ⟨lev_step S c1 y j, lev_step S c2 y j⟩)
  · obtain ⟨-, -, p3, -⟩ := FramePsi.psi_unitary_character L r k S
    rw [Frames.om, norm_mul, norm_inv, (p3 _).1, (p3 _).2]
    simp

end GlobalTheory.HL.WitIndep
