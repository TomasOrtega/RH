import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DualInterSelfDualHermitianLatticeSubspace
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BasisOfIsCompl
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDoubleCosetTermBasicFacts
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.MoveChar

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

/- English proof (translation)
Establish `h1 : ∀ v, n v ∈ S.spanTo g (j + 1) ↔ v ∈ S.spanTo g (j + 1)` using `(Subgroup.mem_iInf.1 hn.1.2 j).1`. Take `⟨y, rfl⟩` from `n.surjective x`. Establish `hy` using `(h1 y).1 hx`. Use `clear hx`. Proceed by induction on `hy using Submodule.span_induction with`.

Consider the case `mem v hv`. Take `⟨i, hi, rfl⟩` from `hv`. Use `⟨Pi.single i 1, fun i' hi' => Pi.single_eq_of_ne ?_ _, ?_⟩` and prove the remaining obligations. Introduce and unpack `rfl`. Conclude with `absurd hi (not_lt.2 hi')`.

Simplify using `[Pi.single_apply]`. Consider the case `zero => exact ⟨0, fun _ _ => rfl, by simp⟩`. Consider the case `add a b _ _ ha hb`. Take `⟨c, h, e⟩` from `ha`. Take `⟨c', h', e'⟩` from `hb`.

Conclude with `⟨c + c', fun i hi => by simp [h i hi, h' i hi], by rw [map_add, e, e']; simp [add_smul, Finset.sum_add_distrib]⟩`. Consider the case `smul t a _ ha`. Take `⟨c, h, e⟩` from `ha`. Conclude with `⟨t • c, fun i hi => by simp [h i hi], by rw [map_smul, e]; simp [Finset.smul_sum, mul_smul]⟩`.
-/
theorem coords {g : Fin (r + 1) → S.V} {n : S.GLV} (hn : n ∈ S.Nof g) (j : Fin r) {x : S.V}
    (hx : x ∈ S.spanTo g (j + 1)) :
    ∃ c : Fin (r + 1) → E, (∀ i : Fin (r + 1), (j : ℕ) + 1 ≤ i → c i = 0) ∧ x = ∑ i, c i • n (g i) := by
  have h1 : ∀ v, n v ∈ S.spanTo g (j + 1) ↔ v ∈ S.spanTo g (j + 1) :=
    (Subgroup.mem_iInf.1 hn.1.2 j).1
  obtain ⟨y, rfl⟩ := n.surjective x
  have hy := (h1 y).1 hx
  clear hx
  induction hy using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨i, hi, rfl⟩ := hv
    refine ⟨Pi.single i 1, fun i' hi' => Pi.single_eq_of_ne ?_ _, ?_⟩
    · rintro rfl
      exact absurd hi (not_lt.2 hi')
    · simp [Pi.single_apply]
  | zero => exact ⟨0, fun _ _ => rfl, by simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨c, h, e⟩ := ha
    obtain ⟨c', h', e'⟩ := hb
    exact ⟨c + c', fun i hi => by simp [h i hi, h' i hi],
      by rw [map_add, e, e']; simp [add_smul, Finset.sum_add_distrib]⟩
  | smul t a _ ha =>
    obtain ⟨c, h, e⟩ := ha
    exact ⟨t • c, fun i hi => by simp [h i hi],
      by rw [map_smul, e]; simp [Finset.smul_sum, mul_smul]⟩

/- English proof (translation)
Use `Fintype.linearIndependent_iffₛ.1 hl (Sum.elim a a') (Sum.elim b b') (by simpa [Fintype.sum_sum_type] using h)` as an intermediate fact. Conclude with `⟨funext fun i => this (.inl i), funext fun i => this (.inr i)⟩`.
-/
theorem uniq {g g' : Fin (r + 1) → S.V} (hl : LinearIndependent E (Sum.elim g g'))
    {a a' b b' : Fin (r + 1) → E}
    (h : ∑ i, a i • g i + ∑ i, a' i • g' i = ∑ i, b i • g i + ∑ i, b' i • g' i) :
    a = b ∧ a' = b' := by
  have := Fintype.linearIndependent_iffₛ.1 hl (Sum.elim a a') (Sum.elim b b')
    (by simpa [Fintype.sum_sum_type] using h)
  exact ⟨funext fun i => this (.inl i), funext fun i => this (.inr i)⟩

/- English proof (translation)
Use `⟨fun h i hi => ?_, fun h => Nat.sInf_le ⟨a, a', rfl, h⟩⟩` and prove the remaining obligations. Establish `hne : {j : ℕ | ∃ al al' : Fin (r + 1) → E, ∑ i, a i • g i + ∑ i, a' i • g' i = ∑ i, al i • g i + ∑ i, al' i • g' i ∧ ∀ i : Fin (r + 1), j ≤ (i : ℕ) → S.RR (al i) (al' i)}.Nonempty` using `⟨r + 1, a, a', rfl, fun i hi => absurd i.2 (not_lt.2 hi)⟩`. Take `⟨b, b', e, hb⟩` from `Nat.sInf_mem hne`. Take `⟨rfl, rfl⟩` from `uniq S hl e`. Conclude with `hb i (le_trans h hi)`.
-/
theorem lev_le_iff {g g' : Fin (r + 1) → S.V} (hl : LinearIndependent E (Sum.elim g g'))
    (a a' : Fin (r + 1) → E) (j : ℕ) :
    S.lev g g' (∑ i, a i • g i + ∑ i, a' i • g' i) ≤ j ↔
      ∀ i : Fin (r + 1), j ≤ (i : ℕ) → S.RR (a i) (a' i) := by
  refine ⟨fun h i hi => ?_, fun h => Nat.sInf_le ⟨a, a', rfl, h⟩⟩
  have hne : {j : ℕ | ∃ al al' : Fin (r + 1) → E,
      ∑ i, a i • g i + ∑ i, a' i • g' i = ∑ i, al i • g i + ∑ i, al' i • g' i ∧
      ∀ i : Fin (r + 1), j ≤ (i : ℕ) → S.RR (al i) (al' i)}.Nonempty :=
    ⟨r + 1, a, a', rfl, fun i hi => absurd i.2 (not_lt.2 hi)⟩
  obtain ⟨b, b', e, hb⟩ := Nat.sInf_mem hne
  obtain ⟨rfl, rfl⟩ := uniq S hl e
  exact hb i (le_trans h hi)

/- English proof (translation)
Use `⟨Sum.elim g g' ∘ (Sum.map (Fin.castLE hJ) (Fin.castLE hJ) ∘ finSumFinEquiv.symm), hl.comp _ (((Fin.castLE_injective hJ).sumMap (Fin.castLE_injective hJ)).comp finSumFinEquiv.symm.injective), ?_⟩` and prove the remaining obligations. Establish `e : ∀ g : Fin (r + 1) → S.V, Set.range (g ∘ Fin.castLE hJ) = g '' {i | (i : ℕ) < J}`. Introduce `g`. Rewrite using `[Set.range_comp, Fin.range_castLE]`. Rewrite using `[← Function.comp_assoc, finSumFinEquiv.symm.surjective.range_comp, Sum.elim_comp_map, Set.Sum.elim_range, e, e, Submodule.span_union]`.

Both sides reduce to the same expression.
-/
theorem exists_family {g g' : Fin (r + 1) → S.V} (hl : LinearIndependent E (Sum.elim g g'))
    {J : ℕ} (hJ : J ≤ r + 1) : ∃ y : Fin (J + J) → S.V, LinearIndependent E y ∧
      Submodule.span E (Set.range y) = S.spanTo g J ⊔ S.spanTo g' J := by
  refine ⟨Sum.elim g g' ∘ (Sum.map (Fin.castLE hJ) (Fin.castLE hJ) ∘ finSumFinEquiv.symm),
    hl.comp _ (((Fin.castLE_injective hJ).sumMap (Fin.castLE_injective hJ)).comp
      finSumFinEquiv.symm.injective), ?_⟩
  have e : ∀ g : Fin (r + 1) → S.V, Set.range (g ∘ Fin.castLE hJ) = g '' {i | (i : ℕ) < J} := by
    intro g
    rw [Set.range_comp, Fin.range_castLE]
  rw [← Function.comp_assoc, finSumFinEquiv.symm.surjective.range_comp, Sum.elim_comp_map,
    Set.Sum.elim_range, e, e, Submodule.span_union]
  rfl

end GlobalTheory.HL.MoveChar

/- English proof (translation)
Introduce `F _ _ _ _ _ E _ _ _ L r k S j β βJ d Λ hT hFF x hx x' hx' _ hlev al al' ex ex'`. Take `⟨hSD, hW, -, h1, h2, hl, -⟩` from `TermBasic.term_basic L r k S d Λ hT`. Take `⟨hl0, -, -, -, -, hth, -⟩` from `GlobalTheory.FrameBasic.main L r k S`. Take `⟨-, -, hn, hn', -⟩` from `hW`. Establish `hRR : ¬ S.RR (al j.castSucc) (al' j.castSucc)`.

Introduce `hR`. Take `⟨c, hc, e⟩` from `MoveChar.coords S hn j hx`. Take `⟨c', hc', e'⟩` from `MoveChar.coords S hn' j hx'`. Take `⟨rfl, rfl⟩` from `MoveChar.uniq S hl (a := al) (a' := al') (b := c) (b' := c') (by rw [← ex, ← ex']; exact congrArg₂ (· + ·) e e')`. Establish `: S.lev (S.fr d Λ) (S.fr' d Λ) (x + x') ≤ j`.

Rewrite using `[ex, ex', MoveChar.lev_le_iff S hl]`. Introduce `i hi`. Break down `hi.eq_or_lt with hi | hi` into its components or cases. Rewrite using `[show i = j.castSucc from Fin.ext hi.symm]` and apply the resulting hypothesis. Rewrite using `[hc i hi, hc' i hi]`.

Conclude with `⟨L.O.zero_mem, 0, L.O.zero_mem, by simp⟩`. Use linear arithmetic over natural numbers and integers. Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Use `set z := al j.castSucc • S.fr d Λ j.succ + al' j.castSucc • S.fr' d Λ j.succ with hz`.

Take `⟨y, hy, ey⟩` from `MoveChar.exists_family S hl0 (J := j + 1) (by omega)`. Establish `hd` using `(DualInter.dual_inter L S.Hm S.herm Λ hSD _ y hy).2.1 (algebraMap F E S.th⁻¹ • z)`. Rewrite `hd` using `[ey]`. Take `⟨a, ha, haY⟩` from `hd.1 fun u hu huY => by`. Establish `: -(algebraMap F E S.th⁻¹ * S.h z u) ∈ L.O`.

Use `(L.additive_character_dual_ring _).1 fun c hc => ?_` and prove the remaining obligations. Use `hcon (L.cj c • u) (Λ.smul_mem ⟨_, GlobalTheory.UnramOrder.cj_mem L hc⟩ hu) (Submodule.smul_mem _ _ huY)` as an intermediate fact. Rewrite using `[← this, Frames.h, Frames.h, DualInter.smul_r, L.cj_cj]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[← DualInter.cj_hf S.herm, DualInter.smul_l]`. Conclude with `GlobalTheory.UnramOrder.cj_mem L (neg_mem_iff.1 this)`. Establish `hjr : (j : ℕ) + 1 ≤ r + 1` using `by omega`. Establish `hzM : z ∈ S.ME` using `Submodule.add_mem_sup (Submodule.smul_mem _ _ ((h1 (r + 1) le_rfl _).2 (Submodule.subset_span ⟨j.succ, j.succ.2, rfl⟩)).2) (Submodule.smul_mem _ _ ((h2 (r + 1) le_rfl _).2 (Submodule.subset_span ⟨j.succ, j.succ.2, rfl⟩)).2)`. Establish `haM : a ∈ S.ME`.

Use `S.ME.sub_mem (S.ME.smul_mem (algebraMap F E S.th⁻¹) hzM) (sup_le_sup (TermBasic.spanTo_mono S S.f hjr) (TermBasic.spanTo_mono S S.f' hjr) haY)` as an intermediate fact. Rewrite `this` using `[sub_sub_cancel]`. Then use the resulting hypothesis. Establish `hla : S.levC d Λ a ≤ j + 1` using `hFF.2.2.1 a ⟨ha, haM⟩`. Take `⟨v, hv, v', hv', e0⟩` from `Submodule.mem_sup.1 (Submodule.smul_mem _ (algebraMap F E S.th) haY)`. Take `⟨c, hc, e⟩` from `MoveChar.coords S hn j hv`.

Take `⟨c', hc', e'⟩` from `MoveChar.coords S hn' j hv'`. Establish `key : algebraMap F E S.th • a = ∑ i, (Pi.single j.succ (al j.castSucc) - c : Fin (r + 1) → E) i • S.fr d Λ i + ∑ i, (Pi.single j.succ (al' j.castSucc) - c' : Fin (r + 1) → E) i • S.fr' d Λ i`. Rewrite `e0` using `[smul_sub, smul_smul, ← map_mul, mul_inv_cancel₀ hth, map_one, one_smul]`. Establish `e1 : v = ∑ i, c i • S.fr d Λ i` using `e`. Establish `e2 : v' = ∑ i, c' i • S.fr' d Λ i` using `e'`.

Simplify using `only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, ← e1, ← e2, Pi.single_apply, ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]`. Rewrite using `[sub_add_sub_comm, e0, ← hz, sub_sub_cancel]`. Rewrite `hla` using `[Frames.levC, key, MoveChar.lev_le_iff S hl]`. Use `hla j.succ (by simp)` as an intermediate fact. Rewrite `this` using `[Pi.sub_apply, Pi.sub_apply, hc _ (by simp), hc' _ (by simp), Pi.single_eq_same, Pi.single_eq_same, sub_zero, sub_zero]`.

Conclude with `hRR this`.
-/
theorem GlobalTheory.HL.MoveChar.chi_ne_one : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (j : Fin r) (β βJ : ℕ) (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → S.InFF β (j + 1) βJ d Λ → ∀ x ∈ S.spanTo S.f (j + 1), ∀ x' ∈ S.spanTo S.f' (j + 1), S.InTh Λ (x + x') → S.lev (S.fr d Λ) (S.fr' d Λ) (x + x') = j + 1 → ∀ al al' : Fin (r + 1) → E, x = ∑ i, al i • S.fr d Λ i → x' = ∑ i, al' i • S.fr' d Λ i → ∃ u ∈ Λ, u ∈ perp L S.Hm (S.spanTo S.f (j + 1) ⊔ S.spanTo S.f' (j + 1)) ∧ L.psi0 (-(algebraMap F E S.th⁻¹ * S.h (al j.castSucc • S.fr d Λ j.succ + al' j.castSucc • S.fr' d Λ j.succ) u)) ≠ 1 := by
  intro F _ _ _ _ _ E _ _ _ L r k S j β βJ d Λ hT hFF x hx x' hx' _ hlev al al' ex ex'
  obtain ⟨hSD, hW, -, h1, h2, hl, -⟩ := TermBasic.term_basic L r k S d Λ hT
  obtain ⟨hl0, -, -, -, -, hth, -⟩ := GlobalTheory.FrameBasic.main L r k S
  obtain ⟨-, -, hn, hn', -⟩ := hW

  have hRR : ¬ S.RR (al j.castSucc) (al' j.castSucc) := by
    intro hR
    obtain ⟨c, hc, e⟩ := MoveChar.coords S hn j hx
    obtain ⟨c', hc', e'⟩ := MoveChar.coords S hn' j hx'
    obtain ⟨rfl, rfl⟩ := MoveChar.uniq S hl (a := al) (a' := al') (b := c) (b' := c')
      (by rw [← ex, ← ex']; exact congrArg₂ (· + ·) e e')
    have : S.lev (S.fr d Λ) (S.fr' d Λ) (x + x') ≤ j := by
      rw [ex, ex', MoveChar.lev_le_iff S hl]
      intro i hi
      rcases hi.eq_or_lt with hi | hi
      · rwa [show i = j.castSucc from Fin.ext hi.symm]
      · rw [hc i hi, hc' i hi]
        exact ⟨L.O.zero_mem, 0, L.O.zero_mem, by simp⟩
    omega
  by_contra hcon
  push Not at hcon
  set z := al j.castSucc • S.fr d Λ j.succ + al' j.castSucc • S.fr' d Λ j.succ with hz
  obtain ⟨y, hy, ey⟩ := MoveChar.exists_family S hl0 (J := j + 1) (by omega)
  have hd := (DualInter.dual_inter L S.Hm S.herm Λ hSD _ y hy).2.1 (algebraMap F E S.th⁻¹ • z)
  rw [ey] at hd
  obtain ⟨a, ha, haY⟩ := hd.1 fun u hu huY => by
    have : -(algebraMap F E S.th⁻¹ * S.h z u) ∈ L.O := by
      refine (L.additive_character_dual_ring _).1 fun c hc => ?_
      have := hcon (L.cj c • u) (Λ.smul_mem ⟨_, GlobalTheory.UnramOrder.cj_mem L hc⟩ hu)
        (Submodule.smul_mem _ _ huY)
      rw [← this, Frames.h, Frames.h, DualInter.smul_r, L.cj_cj]
      congr 1
      ring
    rw [← DualInter.cj_hf S.herm, DualInter.smul_l]
    exact GlobalTheory.UnramOrder.cj_mem L (neg_mem_iff.1 this)
  have hjr : (j : ℕ) + 1 ≤ r + 1 := by omega
  have hzM : z ∈ S.ME :=
    Submodule.add_mem_sup
      (Submodule.smul_mem _ _ ((h1 (r + 1) le_rfl _).2 (Submodule.subset_span ⟨j.succ, j.succ.2, rfl⟩)).2)
      (Submodule.smul_mem _ _ ((h2 (r + 1) le_rfl _).2 (Submodule.subset_span ⟨j.succ, j.succ.2, rfl⟩)).2)
  have haM : a ∈ S.ME := by
    have := S.ME.sub_mem (S.ME.smul_mem (algebraMap F E S.th⁻¹) hzM)
      (sup_le_sup (TermBasic.spanTo_mono S S.f hjr) (TermBasic.spanTo_mono S S.f' hjr) haY)
    rwa [sub_sub_cancel] at this
  have hla : S.levC d Λ a ≤ j + 1 := hFF.2.2.1 a ⟨ha, haM⟩
  obtain ⟨v, hv, v', hv', e0⟩ := Submodule.mem_sup.1 (Submodule.smul_mem _ (algebraMap F E S.th) haY)
  obtain ⟨c, hc, e⟩ := MoveChar.coords S hn j hv
  obtain ⟨c', hc', e'⟩ := MoveChar.coords S hn' j hv'
  have key : algebraMap F E S.th • a =
      ∑ i, (Pi.single j.succ (al j.castSucc) - c : Fin (r + 1) → E) i • S.fr d Λ i +
        ∑ i, (Pi.single j.succ (al' j.castSucc) - c' : Fin (r + 1) → E) i • S.fr' d Λ i := by
    rw [smul_sub, smul_smul, ← map_mul, mul_inv_cancel₀ hth, map_one, one_smul] at e0
    have e1 : v = ∑ i, c i • S.fr d Λ i := e
    have e2 : v' = ∑ i, c' i • S.fr' d Λ i := e'
    simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, ← e1, ← e2, Pi.single_apply, ite_smul,
      zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [sub_add_sub_comm, e0, ← hz, sub_sub_cancel]
  rw [Frames.levC, key, MoveChar.lev_le_iff S hl] at hla
  have := hla j.succ (by simp)
  rw [Pi.sub_apply, Pi.sub_apply, hc _ (by simp), hc' _ (by simp), Pi.single_eq_same, Pi.single_eq_same,
    sub_zero, sub_zero] at this
  exact hRR this
