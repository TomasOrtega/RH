import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormAdditiveCharacterTypePrimeEqOne
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FramesCharactersAgreeCommonStabiliserStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermInvariantsIndependentOfWitnessesStatement

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.FrameAct

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, hxy⟩`. Establish `hyx : y = x` using `h.injective hxy`. Conclude with `hyx ▸ hy`. Introduce `hx`.

Conclude with `⟨x, hx, rfl⟩`.
-/
theorem mem_smul_iff (h : S.GLV) (Λ : Submodule L.O S.V) (x : S.V) : h x ∈ h • Λ ↔ x ∈ Λ := by
  constructor
  · rintro ⟨y, hy, hxy⟩
    have hyx : y = x := h.injective hxy
    exact hyx ▸ hy
  · intro hx
    exact ⟨x, hx, rfl⟩

/- English proof (translation)
Use extensionality with `y`. Establish `hy : h (h.symm y) = y` using `h.apply_symm_apply y`. Rewrite using `[← hy, H, mem_smul_iff]`.
-/
theorem eq_smul_of (h : S.GLV) (Λ Λ' : Submodule L.O S.V) (H : ∀ x, h x ∈ Λ' ↔ x ∈ Λ) :
    Λ' = h • Λ := by
  ext y
  have hy : h (h.symm y) = y := h.apply_symm_apply y
  rw [← hy, H, mem_smul_iff]

/- English proof (translation)
Rewrite using `[Submodule.smul_span]`. Both sides reduce to the same expression.
-/
theorem smul_span (h : S.GLV) (s : Set S.V) :
    h • Submodule.span L.O s = Submodule.span L.O (h '' s) := by
  rw [Submodule.smul_span]
  rfl

/- English proof (translation)
Establish `hA : (h • A).toAddSubgroup = A.toAddSubgroup.map (h.toLinearMap.toAddMonoidHom)`. Use extensionality with `x`. Both sides reduce to the same expression. Establish `hB : (h • B).toAddSubgroup = B.toAddSubgroup.map (h.toLinearMap.toAddMonoidHom)`. Use extensionality with `x`.

Both sides reduce to the same expression. Rewrite using `[hA, hB]`. Conclude with `AddSubgroup.relIndex_map_map_of_injective _ _ h.injective`.
-/
theorem relIndex_smul (h : S.GLV) (A B : Submodule L.O S.V) :
    (h • A).toAddSubgroup.relIndex (h • B).toAddSubgroup =
      A.toAddSubgroup.relIndex B.toAddSubgroup := by
  have hA : (h • A).toAddSubgroup = A.toAddSubgroup.map (h.toLinearMap.toAddMonoidHom) := by
    ext x; rfl
  have hB : (h • B).toAddSubgroup = B.toAddSubgroup.map (h.toLinearMap.toAddMonoidHom) := by
    ext x; rfl
  rw [hA, hB]
  exact AddSubgroup.relIndex_map_map_of_injective _ _ h.injective

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, ⟨z, hz, rfl⟩, hxy⟩`. Use `⟨z, hz, h.injective ?_⟩` and prove the remaining obligations. Rewrite using `[hxy, map_smul]`. Both sides reduce to the same expression.

Introduce and unpack `⟨y, hy, rfl⟩`. Conclude with `⟨h y, ⟨y, hy, rfl⟩, map_smul h _ y⟩`.
-/
theorem inTh_iff (h : S.GLV) (Λ : Submodule L.O S.V) (x : S.V) :
    S.InTh (h • Λ) (h x) ↔ S.InTh Λ x := by
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, hxy⟩
    refine ⟨z, hz, h.injective ?_⟩
    rw [hxy, map_smul]
    rfl
  · rintro ⟨y, hy, rfl⟩
    exact ⟨h y, ⟨y, hy, rfl⟩, map_smul h _ y⟩

/- English proof (translation)
Unfold `Frames.Mof`. Rewrite using `[smul_span, Set.image_union, ← Set.range_comp, ← Set.range_comp]`. Simplify using `only [Function.comp_def, map_sub, LinearEquiv.map_smul]`.
-/
theorem mof_smul (h : S.GLV) (g g' : Fin (r + 1) → S.V) :
    S.Mof (fun b => h (g b)) (fun b => h (g' b)) = h • S.Mof g g' := by
  unfold Frames.Mof
  rw [smul_span, Set.image_union, ← Set.range_comp, ← Set.range_comp]
  simp only [Function.comp_def, map_sub, LinearEquiv.map_smul]

/- English proof (translation)
Establish `key : ∀ (y : S.V) (c : Fin (r + 1) → E) (g0 : Fin (r + 1) → S.V), (h⁻¹ • y = ∑ i, c i • g0 i) ↔ y = ∑ i, c i • h (g0 i)`. Introduce `y c g0`. Establish `hs : ∑ i, c i • h (g0 i) = h (∑ i, c i • g0 i)`. Simplify using `only [map_sum, LinearEquiv.map_smul]`. Rewrite using `[hs]`.

Prove the components needed by the constructor for the conclusion. Introduce `e`. Rewrite using `[← e]`. Conclude with `(h.apply_symm_apply y).symm`. Introduce `e`.

Rewrite using `[e]`. Conclude with `h.symm_apply_apply _`. Use extensionality with `p`. Rewrite using `[Set.mem_smul_set_iff_inv_smul_mem]`. Unfold `Frames.frameCls`.

Simplify using `only [Set.mem_ofPred_eq, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, key]`.
-/
theorem frameCls_smul (h : S.GLV) (g g' : Fin (r + 1) → S.V) :
    S.frameCls (fun b => h (g b)) (fun b => h (g' b)) = h • S.frameCls g g' := by
  have key : ∀ (y : S.V) (c : Fin (r + 1) → E) (g0 : Fin (r + 1) → S.V),
      (h⁻¹ • y = ∑ i, c i • g0 i) ↔ y = ∑ i, c i • h (g0 i) := by
    intro y c g0
    have hs : ∑ i, c i • h (g0 i) = h (∑ i, c i • g0 i) := by
      simp only [map_sum, LinearEquiv.map_smul]
    rw [hs]
    constructor
    · intro e
      rw [← e]
      exact (h.apply_symm_apply y).symm
    · intro e
      rw [e]
      exact h.symm_apply_apply _
  ext p
  rw [Set.mem_smul_set_iff_inv_smul_mem]
  unfold Frames.frameCls
  simp only [Set.mem_ofPred_eq, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, key]

/- English proof (translation)
Unfold `Frames.lev`. Use `congr 1`. Use extensionality with `j`. Simplify using `only [Set.mem_ofPred_eq]`. Establish `hs : ∀ al al' : Fin (r + 1) → E, (∑ i, al i • h (g i) + ∑ i, al' i • h (g' i)) = h (∑ i, al i • g i + ∑ i, al' i • g' i)`.

Introduce `al al'`. Simplify using `only [map_add, map_sum, LinearEquiv.map_smul]`. Simplify using `only [hs, h.injective.eq_iff]`.
-/
theorem lev_smul (h : S.GLV) (g g' : Fin (r + 1) → S.V) (b : S.V) :
    S.lev (fun i => h (g i)) (fun i => h (g' i)) (h b) = S.lev g g' b := by
  unfold Frames.lev
  congr 1
  ext j
  simp only [Set.mem_ofPred_eq]
  have hs : ∀ al al' : Fin (r + 1) → E, (∑ i, al i • h (g i) + ∑ i, al' i • h (g' i)) =
      h (∑ i, al i • g i + ∑ i, al' i • g' i) := by
    intro al al'
    simp only [map_add, map_sum, LinearEquiv.map_smul]
  simp only [hs, h.injective.eq_iff]

/- English proof (translation)
Establish `hN` using `hh`. Simplify using `only [Frames.Nof, Subgroup.mem_inf, Subgroup.mem_iInf] at hN`. Take `⟨⟨_, hflag⟩, htop⟩` from `hN`. Establish `htop' : (∀ w, h w ∈ perp L S.Hm (S.spanTo g r) ↔ w ∈ perp L S.Hm (S.spanTo g r)) ∧ ∀ w ∈ perp L S.Hm (S.spanTo g r), h w - w ∈ S.spanTo g r` using `htop`. Establish `hmono : ∀ a b, a ≤ b → S.spanTo g a ≤ S.spanTo g b`.

Introduce `a b hab`. Conclude with `Submodule.span_mono (Set.image_mono fun i (hi : (i : ℕ) < a) => lt_of_lt_of_le hi hab)`. Establish `hgen : ∀ i : Fin (r + 1), (i : ℕ) < J → h (g i) ∈ S.spanTo g J`. Introduce `i hi`. Distinguish the cases in `hl : i = Fin.last r`.

Substitute `hl` using the available equality. Establish `hperp : g (Fin.last r) ∈ perp L S.Hm (S.spanTo g r)` using `by show ∀ y ∈ S.spanTo g r, hf L S.Hm (g (Fin.last r)) y = 0`. Use `GlobalTheory.FramePsi.hf_span_right L S.Hm _ _ ?_` and prove the remaining obligations. Introduce and unpack `y ⟨i, hi', rfl⟩`. Rewrite using `[hg]`.

Establish `hne : i ≠ Fin.last r`. Introduce `e`. Rewrite `hi'` using `[e]`. Simplify using `at hi'`. Rewrite using `[if_neg (fun e => hne e.2)]`.

Establish `hd : h (g (Fin.last r)) - g (Fin.last r) ∈ S.spanTo g r` using `htop'.2 _ hperp`. Establish `h1 : g (Fin.last r) ∈ S.spanTo g J` using `Submodule.subset_span ⟨Fin.last r, hi, rfl⟩`. Establish `h2 : S.spanTo g r ≤ S.spanTo g J` using `hmono _ _ (by simp at hi; omega)`. Establish `h3` using `Submodule.add_mem _ (h2 hd) h1`. Rewrite `h3` using `[sub_add_cancel]`. Then use the resulting hypothesis.

Establish `hir : (i : ℕ) < r`. Establish `h0` using `i.isLt`. Establish `h4 : (i : ℕ) ≠ r` using `fun e => hl (Fin.ext (by simpa using e))`. Use linear arithmetic over natural numbers and integers. Establish `hmem : g i ∈ S.spanTo g ((i : ℕ) + 1)` using `Submodule.subset_span ⟨i, by simp, rfl⟩`.

Establish `h5 : (∀ w, h w ∈ S.spanTo g ((i : ℕ) + 1) ↔ w ∈ S.spanTo g ((i : ℕ) + 1)) ∧ ∀ w ∈ S.spanTo g ((i : ℕ) + 1), h w - w ∈ S.spanTo g (i : ℕ)` using `hflag ⟨i, hir⟩`. Conclude with `hmono _ _ (by omega) ((h5.1 (g i)).2 hmem)`. Establish `hle : S.spanTo g J ≤ (S.spanTo g J).comap (h : S.V →ₗ[E] S.V)`. Use `Submodule.span_le.mpr ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨i, hi, rfl⟩`.

Conclude with `hgen i hi`. Conclude with `hle hv`.
-/
theorem spanTo_map (g : Fin (r + 1) → S.V) (t : E)
    (hg : ∀ a b, hf L S.Hm (g a) (g b) = if a = Fin.last r ∧ b = Fin.last r then t else 0)
    (h : S.GLV) (hh : h ∈ S.Nof g) (J : ℕ) (v : S.V) (hv : v ∈ S.spanTo g J) :
    h v ∈ S.spanTo g J := by
  have hN := hh
  simp only [Frames.Nof, Subgroup.mem_inf, Subgroup.mem_iInf] at hN
  obtain ⟨⟨_, hflag⟩, htop⟩ := hN
  have htop' : (∀ w, h w ∈ perp L S.Hm (S.spanTo g r) ↔ w ∈ perp L S.Hm (S.spanTo g r)) ∧
      ∀ w ∈ perp L S.Hm (S.spanTo g r), h w - w ∈ S.spanTo g r := htop
  have hmono : ∀ a b, a ≤ b → S.spanTo g a ≤ S.spanTo g b := by
    intro a b hab
    exact Submodule.span_mono (Set.image_mono fun i (hi : (i : ℕ) < a) => lt_of_lt_of_le hi hab)
  have hgen : ∀ i : Fin (r + 1), (i : ℕ) < J → h (g i) ∈ S.spanTo g J := by
    intro i hi
    by_cases hl : i = Fin.last r
    · subst hl
      have hperp : g (Fin.last r) ∈ perp L S.Hm (S.spanTo g r) := by
        show ∀ y ∈ S.spanTo g r, hf L S.Hm (g (Fin.last r)) y = 0
        refine GlobalTheory.FramePsi.hf_span_right L S.Hm _ _ ?_
        rintro y ⟨i, hi', rfl⟩
        rw [hg]
        have hne : i ≠ Fin.last r := by
          intro e
          rw [e] at hi'
          simp at hi'
        rw [if_neg (fun e => hne e.2)]
      have hd : h (g (Fin.last r)) - g (Fin.last r) ∈ S.spanTo g r := htop'.2 _ hperp
      have h1 : g (Fin.last r) ∈ S.spanTo g J := Submodule.subset_span ⟨Fin.last r, hi, rfl⟩
      have h2 : S.spanTo g r ≤ S.spanTo g J := hmono _ _ (by simp at hi; omega)
      have h3 := Submodule.add_mem _ (h2 hd) h1
      rwa [sub_add_cancel] at h3
    · have hir : (i : ℕ) < r := by
        have h0 := i.isLt
        have h4 : (i : ℕ) ≠ r := fun e => hl (Fin.ext (by simpa using e))
        omega
      have hmem : g i ∈ S.spanTo g ((i : ℕ) + 1) :=
        Submodule.subset_span ⟨i, by simp, rfl⟩
      have h5 : (∀ w, h w ∈ S.spanTo g ((i : ℕ) + 1) ↔ w ∈ S.spanTo g ((i : ℕ) + 1)) ∧
          ∀ w ∈ S.spanTo g ((i : ℕ) + 1), h w - w ∈ S.spanTo g (i : ℕ) := hflag ⟨i, hir⟩
      exact hmono _ _ (by omega) ((h5.1 (g i)).2 hmem)
  have hle : S.spanTo g J ≤ (S.spanTo g J).comap (h : S.V →ₗ[E] S.V) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨i, hi, rfl⟩
    exact hgen i hi
  exact hle hv

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hv`. Establish `h1` using `H h⁻¹ (G.inv_mem hh) (h v) hv`. Establish `e : h⁻¹ (h v) = v` using `h.symm_apply_apply v`. Rewrite `h1` using `[e]`. Then use the resulting hypothesis.

Conclude with `H h hh v`.
-/
theorem map_iff_of (A : Submodule E S.V) (G : Subgroup S.GLV)
    (H : ∀ h ∈ G, ∀ v ∈ A, h v ∈ A) (h : S.GLV) (hh : h ∈ G) (v : S.V) : h v ∈ A ↔ v ∈ A := by
  constructor
  · intro hv
    have h1 := H h⁻¹ (G.inv_mem hh) (h v) hv
    have e : h⁻¹ (h v) = v := h.symm_apply_apply v
    rwa [e] at h1
  · exact H h hh v

/- English proof (translation)
Establish `hN : h ∈ S.N` using `(Subgroup.mem_inf.mp hh).1`. Conclude with `map_iff_of S (S.spanTo S.f J) S.N (fun h' hh' w hw => spanTo_map S S.f _ S.gram h' hh' J w hw) h hN v`.
-/
theorem spanTo_iff (h : S.GLV) (hh : h ∈ S.St) (J : ℕ) (v : S.V) :
    h v ∈ S.spanTo S.f J ↔ v ∈ S.spanTo S.f J := by
  have hN : h ∈ S.N := (Subgroup.mem_inf.mp hh).1
  exact map_iff_of S (S.spanTo S.f J) S.N
    (fun h' hh' w hw => spanTo_map S S.f _ S.gram h' hh' J w hw) h hN v

/- English proof (translation)
Establish `hN : h ∈ S.N'` using `(Subgroup.mem_inf.mp hh).2`. Conclude with `map_iff_of S (S.spanTo S.f' J) S.N' (fun h' hh' w hw => spanTo_map S S.f' _ S.gram' h' hh' J w hw) h hN v`.
-/
theorem spanTo_iff' (h : S.GLV) (hh : h ∈ S.St) (J : ℕ) (v : S.V) :
    h v ∈ S.spanTo S.f' J ↔ v ∈ S.spanTo S.f' J := by
  have hN : h ∈ S.N' := (Subgroup.mem_inf.mp hh).2
  exact map_iff_of S (S.spanTo S.f' J) S.N'
    (fun h' hh' w hw => spanTo_map S S.f' _ S.gram' h' hh' J w hw) h hN v

/- English proof (translation)
Establish `hS : ∀ h' ∈ S.St, ∀ w ∈ S.spanTo S.f J ⊔ S.spanTo S.f' J, h' w ∈ S.spanTo S.f J ⊔ S.spanTo S.f' J`. Introduce `h' hh' w hw`. Take `⟨a, ha, b, hb, rfl⟩` from `Submodule.mem_sup.mp hw`. Rewrite using `[map_add]`. Conclude with `Submodule.add_mem_sup ((spanTo_iff S h' hh' J a).2 ha) ((spanTo_iff' S h' hh' J b).2 hb)`.

Conclude with `map_iff_of S _ S.St hS h hh v`.
-/
theorem sup_iff (h : S.GLV) (hh : h ∈ S.St) (J : ℕ) (v : S.V) :
    h v ∈ S.spanTo S.f J ⊔ S.spanTo S.f' J ↔ v ∈ S.spanTo S.f J ⊔ S.spanTo S.f' J := by
  have hS : ∀ h' ∈ S.St, ∀ w ∈ S.spanTo S.f J ⊔ S.spanTo S.f' J,
      h' w ∈ S.spanTo S.f J ⊔ S.spanTo S.f' J := by
    intro h' hh' w hw
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hw
    rw [map_add]
    exact Submodule.add_mem_sup ((spanTo_iff S h' hh' J a).2 ha) ((spanTo_iff' S h' hh' J b).2 hb)
  exact map_iff_of S _ S.St hS h hh v

/- English proof (translation)
Establish `hN : h ∈ S.N` using `(Subgroup.mem_inf.mp hh).1`. Simplify using `only [Frames.N, Frames.Nof, Subgroup.mem_inf] at hN`. Conclude with `hN.1.1 x y`.
-/
theorem isom (h : S.GLV) (hh : h ∈ S.St) (x y : S.V) : hf L S.Hm (h x) (h y) = hf L S.Hm x y := by
  have hN : h ∈ S.N := (Subgroup.mem_inf.mp hh).1
  simp only [Frames.N, Frames.Nof, Subgroup.mem_inf] at hN
  exact hN.1.1 x y

/- English proof (translation)
Use `show (∀ y ∈ A, hf L S.Hm (h v) y = 0) ↔ ∀ y ∈ A, hf L S.Hm v y = 0`. Prove the components needed by the constructor for the conclusion. Introduce `H y hy`. Rewrite using `[← isom S h hh v y]`. Conclude with `H (h y) ((hA y).2 hy)`.

Introduce `H y hy`. Establish `e : h (h⁻¹ y) = y` using `h.apply_symm_apply y`. Establish `hy' : h⁻¹ y ∈ A` using `(hA (h⁻¹ y)).1 (by rw [e]; exact hy)`. Rewrite using `[← e, isom S h hh]`. Conclude with `H _ hy'`.
-/
theorem perp_iff (h : S.GLV) (hh : h ∈ S.St) (A : Submodule E S.V) (hA : ∀ v, h v ∈ A ↔ v ∈ A)
    (v : S.V) : h v ∈ perp L S.Hm A ↔ v ∈ perp L S.Hm A := by
  show (∀ y ∈ A, hf L S.Hm (h v) y = 0) ↔ ∀ y ∈ A, hf L S.Hm v y = 0
  constructor
  · intro H y hy
    rw [← isom S h hh v y]
    exact H (h y) ((hA y).2 hy)
  · intro H y hy
    have e : h (h⁻¹ y) = y := h.apply_symm_apply y
    have hy' : h⁻¹ y ∈ A := (hA (h⁻¹ y)).1 (by rw [e]; exact hy)
    rw [← e, isom S h hh]
    exact H _ hy'

/- English proof (translation)
Use extensionality with `y`. Establish `e : h (h⁻¹ y) = y` using `h.apply_symm_apply y`. Rewrite using `[← e, mem_smul_iff]`. Unfold `Frames.sat Frames.ME`. Rewrite using `[Submodule.mem_inf, Submodule.mem_inf, mem_smul_iff, Submodule.restrictScalars_mem, Submodule.restrictScalars_mem, sup_iff S h hh]`.
-/
theorem sat_smul (h : S.GLV) (hh : h ∈ S.St) (Λ : Submodule L.O S.V) :
    S.sat (h • Λ) = h • S.sat Λ := by
  ext y
  have e : h (h⁻¹ y) = y := h.apply_symm_apply y
  rw [← e, mem_smul_iff]
  unfold Frames.sat Frames.ME
  rw [Submodule.mem_inf, Submodule.mem_inf, mem_smul_iff, Submodule.restrictScalars_mem,
    Submodule.restrictScalars_mem, sup_iff S h hh]

/- English proof (translation)
Introduce and unpack `p ⟨y', hy', y, hy, hy'p, hyp, h1, h2, h3⟩`. Establish `hN : h ∈ S.N` using `(Subgroup.mem_inf.mp hh).1`. Establish `hN' : h ∈ S.N'` using `(Subgroup.mem_inf.mp hh).2`. Simplify using `only [Frames.N, Frames.N', Frames.Nof, Subgroup.mem_inf] at hN hN'`. Establish `u1 : (∀ w, h w ∈ perp L S.Hm (S.spanTo S.f r) ↔ w ∈ perp L S.Hm (S.spanTo S.f r)) ∧ ∀ w ∈ perp L S.Hm (S.spanTo S.f r), h w - w ∈ S.spanTo S.f r` using `hN.2`.

Establish `u2 : (∀ w, h w ∈ perp L S.Hm (S.spanTo S.f' r) ↔ w ∈ perp L S.Hm (S.spanTo S.f' r)) ∧ ∀ w ∈ perp L S.Hm (S.spanTo S.f' r), h w - w ∈ S.spanTo S.f' r` using `hN'.2`. Use `⟨h y', (mem_smul_iff S h Λ y').2 hy', h y, (mem_smul_iff S h Λ y).2 hy, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `(perp_iff S h hh S.X' (fun v => spanTo_iff' S h hh r v) y').2 hy'p`. Conclude with `(perp_iff S h hh S.X (fun v => spanTo_iff S h hh r v) y).2 hyp`. Establish `e : h y' - p.1 = (h y' - y') + (y' - p.1)` using `by abel`.

Rewrite using `[e]`. Conclude with `Submodule.add_mem _ (u2.2 y' hy'p) h1`. Establish `e : h y - p.2 = (h y - y) + (y - p.2)` using `by abel`. Rewrite using `[e]`. Conclude with `Submodule.add_mem _ (u1.2 y hyp) h2`.

Establish `h4` using `(inTh_iff S h Λ (y' - y)).2 h3`. Rewrite `h4` using `[map_sub]`. Conclude with `h4`.
-/
theorem graph_sub (h : S.GLV) (hh : h ∈ S.St) (Λ : Submodule L.O S.V) :
    S.graphOf Λ ⊆ S.graphOf (h • Λ) := by
  rintro p ⟨y', hy', y, hy, hy'p, hyp, h1, h2, h3⟩
  have hN : h ∈ S.N := (Subgroup.mem_inf.mp hh).1
  have hN' : h ∈ S.N' := (Subgroup.mem_inf.mp hh).2
  simp only [Frames.N, Frames.N', Frames.Nof, Subgroup.mem_inf] at hN hN'
  have u1 : (∀ w, h w ∈ perp L S.Hm (S.spanTo S.f r) ↔ w ∈ perp L S.Hm (S.spanTo S.f r)) ∧
      ∀ w ∈ perp L S.Hm (S.spanTo S.f r), h w - w ∈ S.spanTo S.f r := hN.2
  have u2 : (∀ w, h w ∈ perp L S.Hm (S.spanTo S.f' r) ↔ w ∈ perp L S.Hm (S.spanTo S.f' r)) ∧
      ∀ w ∈ perp L S.Hm (S.spanTo S.f' r), h w - w ∈ S.spanTo S.f' r := hN'.2
  refine ⟨h y', (mem_smul_iff S h Λ y').2 hy', h y, (mem_smul_iff S h Λ y).2 hy, ?_, ?_, ?_, ?_, ?_⟩
  · exact (perp_iff S h hh S.X' (fun v => spanTo_iff' S h hh r v) y').2 hy'p
  · exact (perp_iff S h hh S.X (fun v => spanTo_iff S h hh r v) y).2 hyp
  · have e : h y' - p.1 = (h y' - y') + (y' - p.1) := by abel
    rw [e]
    exact Submodule.add_mem _ (u2.2 y' hy'p) h1
  · have e : h y - p.2 = (h y - y) + (y - p.2) := by abel
    rw [e]
    exact Submodule.add_mem _ (u1.2 y hyp) h2
  · have h4 := (inTh_iff S h Λ (y' - y)).2 h3
    rw [map_sub] at h4
    exact h4

/- English proof (translation)
Establish `h1` using `graph_sub S h⁻¹ (S.St.inv_mem hh) (h • Λ)`. Rewrite `h1` using `[inv_smul_smul]`. Conclude with `Set.Subset.antisymm h1 (graph_sub S h hh Λ)`.
-/
theorem graph_smul (h : S.GLV) (hh : h ∈ S.St) (Λ : Submodule L.O S.V) :
    S.graphOf (h • Λ) = S.graphOf Λ := by
  have h1 := graph_sub S h⁻¹ (S.St.inv_mem hh) (h • Λ)
  rw [inv_smul_smul] at h1
  exact Set.Subset.antisymm h1 (graph_sub S h hh Λ)

/- English proof (translation)
Take `⟨i1, i2, hn, hn', e1, e2, hb, hg⟩` from `H`. Establish `hN : h ∈ S.N` using `(Subgroup.mem_inf.mp hh).1`. Establish `hN' : h ∈ S.N'` using `(Subgroup.mem_inf.mp hh).2`. Use `⟨i1, i2, S.N.mul_mem hN hn, S.N'.mul_mem hN' hn', ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[e1, mul_smul]`.

Rewrite using `[e2, mul_smul]`. Introduce `b`. Establish `h4` using `(inTh_iff S h Λ _).2 (hb b)`. Rewrite `h4` using `[map_sub]`. Conclude with `h4`.

Rewrite using `[hg, graph_smul S h hh Λ]`.
-/
theorem isTermW_smul (h : S.GLV) (hh : h ∈ S.St) (d : S.Datum) (Λ : Submodule L.O S.V)
    (n n' : S.GLV) (H : S.IsTermW d Λ n n') : S.IsTermW d (h • Λ) (h * n) (h * n') := by
  obtain ⟨i1, i2, hn, hn', e1, e2, hb, hg⟩ := H
  have hN : h ∈ S.N := (Subgroup.mem_inf.mp hh).1
  have hN' : h ∈ S.N' := (Subgroup.mem_inf.mp hh).2
  refine ⟨i1, i2, S.N.mul_mem hN hn, S.N'.mul_mem hN' hn', ?_, ?_, ?_, ?_⟩
  · rw [e1, mul_smul]
  · rw [e2, mul_smul]
  · intro b
    have h4 := (inTh_iff S h Λ _).2 (hb b)
    rw [map_sub] at h4
    exact h4
  · rw [hg, graph_smul S h hh Λ]

/- English proof (translation)
Unfold `Frames.wit`. Rewrite using `[dif_pos H]`. Conclude with `Exists.choose_spec H`.
-/
theorem wit_spec (d : S.Datum) (Λ : Submodule L.O S.V) (H : S.IsTerm d Λ) :
    S.IsTermW d Λ (S.wit d Λ).1 (S.wit d Λ).2 := by
  unfold Frames.wit
  rw [dif_pos H]
  exact Exists.choose_spec H

/- English proof (translation)
Take `⟨la, hla, la', hla', h1, h2, h3, h4⟩` from `H`. Establish `hN : h ∈ S.N` using `(Subgroup.mem_inf.mp hh).1`. Establish `hN' : h ∈ S.N'` using `(Subgroup.mem_inf.mp hh).2`. Simplify using `only [Frames.N, Frames.N', Frames.Nof, Subgroup.mem_inf] at hN hN'`. Establish `u1 : (∀ v, h v ∈ perp L S.Hm (S.spanTo S.f r) ↔ v ∈ perp L S.Hm (S.spanTo S.f r)) ∧ ∀ v ∈ perp L S.Hm (S.spanTo S.f r), h v - v ∈ S.spanTo S.f r` using `hN.2`.

Establish `u2 : (∀ v, h v ∈ perp L S.Hm (S.spanTo S.f' r) ↔ v ∈ perp L S.Hm (S.spanTo S.f' r)) ∧ ∀ v ∈ perp L S.Hm (S.spanTo S.f' r), h v - v ∈ S.spanTo S.f' r` using `hN'.2`. Establish `hw' : ∀ z ∈ S.ME, hf L S.Hm w z = 0` using `hw`. Establish `hsub : ∀ g : Fin (r + 1) → S.V, S.spanTo g r ≤ S.spanTo g (r + 1)` using `fun g => Submodule.span_mono (Set.image_mono fun i (hi : (i : ℕ) < r) => Nat.lt_succ_of_lt hi)`. Establish `hw1 : w ∈ perp L S.Hm (S.spanTo S.f r)` using `by show ∀ z ∈ S.spanTo S.f r, hf L S.Hm w z = 0`. Introduce `z hz`.

Conclude with `hw' z (le_sup_left (a := S.spanTo S.f (r + 1)) (hsub S.f hz))`. Establish `hw2 : w ∈ perp L S.Hm (S.spanTo S.f' r)` using `by show ∀ z ∈ S.spanTo S.f' r, hf L S.Hm w z = 0`. Introduce `z hz`. Conclude with `hw' z (le_sup_right (b := S.spanTo S.f' (r + 1)) (hsub S.f' hz))`. Establish `e3 : h w - w + h la' - (h w - w + h la) = h (la' - la)`.

Rewrite using `[map_sub]`. Normalize the expressions using the abelian group laws. Use `⟨h w - w + h la, ?_, h w - w + h la', ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `Submodule.add_mem _ (u1.2 w hw1) ((spanTo_iff S h hh r la).2 hla)`. Conclude with `Submodule.add_mem _ (u2.2 w hw2) ((spanTo_iff' S h hh r la').2 hla')`.

Establish `e : w + (h w - w + h la) = h (w + la)`. Rewrite using `[map_add]`. Normalize the expressions using the abelian group laws. Rewrite using `[e]`. Conclude with `(mem_smul_iff S h Λ _).2 h1`.

Establish `e : w + (h w - w + h la') = h (w + la')`. Rewrite using `[map_add]`. Normalize the expressions using the abelian group laws. Rewrite using `[e]`. Conclude with `(mem_smul_iff S h Λ _).2 h2`.

Rewrite using `[e3]`. Conclude with `(inTh_iff S h Λ _).2 h3`. Rewrite using `[e3, ← LinearEquiv.map_smul, ← map_sub, hM]`. Conclude with `(mem_smul_iff S h _ _).2 h4`.
-/
theorem tauRel_map (h : S.GLV) (hh : h ∈ S.St) (d : S.Datum) (Λ : Submodule L.O S.V)
    (hM : S.M d (h • Λ) = h • S.M d Λ) (w : S.V) (hw : w ∈ S.W0) (y : S.V)
    (H : S.TauRel d Λ w y) : S.TauRel d (h • Λ) w (h y) := by
  obtain ⟨la, hla, la', hla', h1, h2, h3, h4⟩ := H
  have hN : h ∈ S.N := (Subgroup.mem_inf.mp hh).1
  have hN' : h ∈ S.N' := (Subgroup.mem_inf.mp hh).2
  simp only [Frames.N, Frames.N', Frames.Nof, Subgroup.mem_inf] at hN hN'
  have u1 : (∀ v, h v ∈ perp L S.Hm (S.spanTo S.f r) ↔ v ∈ perp L S.Hm (S.spanTo S.f r)) ∧
      ∀ v ∈ perp L S.Hm (S.spanTo S.f r), h v - v ∈ S.spanTo S.f r := hN.2
  have u2 : (∀ v, h v ∈ perp L S.Hm (S.spanTo S.f' r) ↔ v ∈ perp L S.Hm (S.spanTo S.f' r)) ∧
      ∀ v ∈ perp L S.Hm (S.spanTo S.f' r), h v - v ∈ S.spanTo S.f' r := hN'.2
  have hw' : ∀ z ∈ S.ME, hf L S.Hm w z = 0 := hw
  have hsub : ∀ g : Fin (r + 1) → S.V, S.spanTo g r ≤ S.spanTo g (r + 1) := fun g =>
    Submodule.span_mono (Set.image_mono fun i (hi : (i : ℕ) < r) => Nat.lt_succ_of_lt hi)
  have hw1 : w ∈ perp L S.Hm (S.spanTo S.f r) := by
    show ∀ z ∈ S.spanTo S.f r, hf L S.Hm w z = 0
    intro z hz
    exact hw' z (le_sup_left (a := S.spanTo S.f (r + 1)) (hsub S.f hz))
  have hw2 : w ∈ perp L S.Hm (S.spanTo S.f' r) := by
    show ∀ z ∈ S.spanTo S.f' r, hf L S.Hm w z = 0
    intro z hz
    exact hw' z (le_sup_right (b := S.spanTo S.f' (r + 1)) (hsub S.f' hz))
  have e3 : h w - w + h la' - (h w - w + h la) = h (la' - la) := by
    rw [map_sub]
    abel
  refine ⟨h w - w + h la, ?_, h w - w + h la', ?_, ?_, ?_, ?_, ?_⟩
  · exact Submodule.add_mem _ (u1.2 w hw1) ((spanTo_iff S h hh r la).2 hla)
  · exact Submodule.add_mem _ (u2.2 w hw2) ((spanTo_iff' S h hh r la').2 hla')
  · have e : w + (h w - w + h la) = h (w + la) := by
      rw [map_add]
      abel
    rw [e]
    exact (mem_smul_iff S h Λ _).2 h1
  · have e : w + (h w - w + h la') = h (w + la') := by
      rw [map_add]
      abel
    rw [e]
    exact (mem_smul_iff S h Λ _).2 h2
  · rw [e3]
    exact (inTh_iff S h Λ _).2 h3
  · rw [e3, ← LinearEquiv.map_smul, ← map_sub, hM]
    exact (mem_smul_iff S h _ _).2 h4

/- English proof (translation)
Establish `hM' : S.M d (h⁻¹ • h • Λ) = h⁻¹ • S.M d (h • Λ)`. Rewrite using `[inv_smul_smul, hM, inv_smul_smul]`. Unfold `Frames.Ihat`. Rewrite using `[Submodule.smul_sup', hM, smul_span]`. Use `congr 2`.

Use extensionality with `y`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨w, hw, hT⟩`. Establish `hw0 : w ∈ S.W0` using `hw.1`. Establish `hinv` using `tauRel_map S h⁻¹ (S.St.inv_mem hh) d (h • Λ) hM' w hw0 y hT`.

Rewrite `hinv` using `[inv_smul_smul]`. Conclude with `⟨h⁻¹ y, ⟨w, hw, hinv⟩, h.apply_symm_apply y⟩`. Introduce and unpack `⟨x, ⟨w, hw, hT⟩, rfl⟩`. Establish `hw0 : w ∈ S.W0` using `hw.1`. Conclude with `⟨w, hw, tauRel_map S h hh d Λ hM w hw0 x hT⟩`.
-/
theorem ihat_smul (h : S.GLV) (hh : h ∈ S.St) (d : S.Datum) (Λ : Submodule L.O S.V)
    (hM : S.M d (h • Λ) = h • S.M d Λ) : S.Ihat d (h • Λ) = h • S.Ihat d Λ := by
  have hM' : S.M d (h⁻¹ • h • Λ) = h⁻¹ • S.M d (h • Λ) := by
    rw [inv_smul_smul, hM, inv_smul_smul]
  unfold Frames.Ihat
  rw [Submodule.smul_sup', hM, smul_span]
  congr 2
  ext y
  constructor
  · rintro ⟨w, hw, hT⟩
    have hw0 : w ∈ S.W0 := hw.1
    have hinv := tauRel_map S h⁻¹ (S.St.inv_mem hh) d (h • Λ) hM' w hw0 y hT
    rw [inv_smul_smul] at hinv
    exact ⟨h⁻¹ y, ⟨w, hw, hinv⟩, h.apply_symm_apply y⟩
  · rintro ⟨x, ⟨w, hw, hT⟩, rfl⟩
    have hw0 : w ∈ S.W0 := hw.1
    exact ⟨w, hw, tauRel_map S h hh d Λ hM w hw0 x hT⟩

/- English proof (translation)
Rewrite using `[sat_smul S h hh]`. Prove the components needed by the constructor for the conclusion. Introduce `H y hy`. Conclude with `H (h y) ((mem_smul_iff S h _ y).2 hy)`. Introduce `H y hy`.

Establish `e : h (h⁻¹ y) = y` using `h.apply_symm_apply y`. Rewrite `hy`, the goal using `[← e]`. Conclude with `H _ ((mem_smul_iff S h _ _).1 hy)`.
-/
theorem forall_sat (h : S.GLV) (hh : h ∈ S.St) (Λ : Submodule L.O S.V) (P : S.V → Prop) :
    (∀ y ∈ S.sat (h • Λ), P y) ↔ ∀ y ∈ S.sat Λ, P (h y) := by
  rw [sat_smul S h hh]
  constructor
  · intro H y hy
    exact H (h y) ((mem_smul_iff S h _ y).2 hy)
  · intro H y hy
    have e : h (h⁻¹ y) = y := h.apply_symm_apply y
    rw [← e] at hy ⊢
    exact H _ ((mem_smul_iff S h _ _).1 hy)

/- English proof (translation)
Rewrite using `[sat_smul S h hh]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, hP⟩`. Establish `e : h (h⁻¹ y) = y` using `h.apply_symm_apply y`. Rewrite `hy`, `hP` using `[← e]`.

Conclude with `⟨_, (mem_smul_iff S h _ _).1 hy, hP⟩`. Introduce and unpack `⟨y, hy, hP⟩`. Conclude with `⟨h y, (mem_smul_iff S h _ y).2 hy, hP⟩`.
-/
theorem exists_sat (h : S.GLV) (hh : h ∈ S.St) (Λ : Submodule L.O S.V) (P : S.V → Prop) :
    (∃ y ∈ S.sat (h • Λ), P y) ↔ ∃ y ∈ S.sat Λ, P (h y) := by
  rw [sat_smul S h hh]
  constructor
  · rintro ⟨y, hy, hP⟩
    have e : h (h⁻¹ y) = y := h.apply_symm_apply y
    rw [← e] at hy hP
    exact ⟨_, (mem_smul_iff S h _ _).1 hy, hP⟩
  · rintro ⟨y, hy, hP⟩
    exact ⟨h y, (mem_smul_iff S h _ y).2 hy, hP⟩

/- English proof (translation)
Unfold `Frames.nLev`. Establish `hC : ∀ y : S.V, {x | x - h y ∈ S.M d (h • Λ)} = (h : S.V → S.V) '' {x | x - y ∈ S.M d Λ}`. Introduce `y`. Use extensionality with `x`. Rewrite using `[hM]`.

Prove the components needed by the constructor for the conclusion. Introduce `hx`. Establish `hx' : x - h y ∈ h • S.M d Λ` using `hx`. Establish `e : x - h y = h (h⁻¹ x - y)`. Rewrite using `[map_sub, show h (h⁻¹ x) = x from h.apply_symm_apply x]`.

Rewrite `hx'` using `[e]`. Conclude with `⟨h⁻¹ x, (mem_smul_iff S h _ _).1 hx', h.apply_symm_apply x⟩`. Introduce and unpack `⟨z, hz, rfl⟩`. Establish `hz' : z - y ∈ S.M d Λ` using `hz`. Use `show h z - h y ∈ h • S.M d Λ`.

Rewrite using `[← map_sub]`. Conclude with `(mem_smul_iff S h _ _).2 hz'`. Establish `hT : {C : Set S.V | ∃ y ∈ S.sat (h • Λ), S.levC d (h • Λ) y = J ∧ C = {x | x - y ∈ S.M d (h • Λ)}} = (fun C => (h : S.V → S.V) '' C) '' {C | ∃ y ∈ S.sat Λ, S.levC d Λ y = J ∧ C = {x | x - y ∈ S.M d Λ}}`. Use extensionality with `C`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨y, hy, hl, rfl⟩`. Rewrite `hy` using `[sat_smul S h hh]`. Take `⟨z, hz, rfl⟩` from `hy`. Use `⟨{x | x - z ∈ S.M d Λ}, ⟨z, hz, ?_, rfl⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[← hL z]`.

Conclude with `hl`. Conclude with `(hC z).symm`. Introduce and unpack `⟨C0, ⟨z, hz, hl, rfl⟩, rfl⟩`. Use `⟨h z, ?_, ?_, (hC z).symm⟩` and prove the remaining obligations. Rewrite using `[sat_smul S h hh]`.

Conclude with `(mem_smul_iff S h _ _).2 hz`. Rewrite using `[hL]`. Conclude with `hl`. Rewrite using `[hT, Set.ncard_image_of_injective _ (Set.image_injective.mpr h.injective)]`.
-/
theorem nLev_smul (h : S.GLV) (hh : h ∈ S.St) (d : S.Datum) (Λ : Submodule L.O S.V)
    (hM : S.M d (h • Λ) = h • S.M d Λ) (hL : ∀ y, S.levC d (h • Λ) (h y) = S.levC d Λ y) (J : ℕ) :
    S.nLev d (h • Λ) J = S.nLev d Λ J := by
  unfold Frames.nLev
  have hC : ∀ y : S.V, {x | x - h y ∈ S.M d (h • Λ)} = (h : S.V → S.V) '' {x | x - y ∈ S.M d Λ} := by
    intro y
    ext x
    rw [hM]
    constructor
    · intro hx
      have hx' : x - h y ∈ h • S.M d Λ := hx
      have e : x - h y = h (h⁻¹ x - y) := by
        rw [map_sub, show h (h⁻¹ x) = x from h.apply_symm_apply x]
      rw [e] at hx'
      exact ⟨h⁻¹ x, (mem_smul_iff S h _ _).1 hx', h.apply_symm_apply x⟩
    · rintro ⟨z, hz, rfl⟩
      have hz' : z - y ∈ S.M d Λ := hz
      show h z - h y ∈ h • S.M d Λ
      rw [← map_sub]
      exact (mem_smul_iff S h _ _).2 hz'
  have hT : {C : Set S.V | ∃ y ∈ S.sat (h • Λ), S.levC d (h • Λ) y = J ∧
        C = {x | x - y ∈ S.M d (h • Λ)}} =
      (fun C => (h : S.V → S.V) '' C) ''
        {C | ∃ y ∈ S.sat Λ, S.levC d Λ y = J ∧ C = {x | x - y ∈ S.M d Λ}} := by
    ext C
    constructor
    · rintro ⟨y, hy, hl, rfl⟩
      rw [sat_smul S h hh] at hy
      obtain ⟨z, hz, rfl⟩ := hy
      refine ⟨{x | x - z ∈ S.M d Λ}, ⟨z, hz, ?_, rfl⟩, ?_⟩
      · rw [← hL z]
        exact hl
      · exact (hC z).symm
    · rintro ⟨C0, ⟨z, hz, hl, rfl⟩, rfl⟩
      refine ⟨h z, ?_, ?_, (hC z).symm⟩
      · rw [sat_smul S h hh]
        exact (mem_smul_iff S h _ _).2 hz
      · rw [hL]
        exact hl
  rw [hT, Set.ncard_image_of_injective _ (Set.image_injective.mpr h.injective)]

/- English proof (translation)
Introduce `F _ _ _ _ _ E _ _ _ L r k S d Λ hT h hh`. Take `⟨⟨n, n'⟩, W⟩` from `hT`. Establish `W0 : S.IsTermW d Λ n n'` using `W`. Establish `W2` using `isTermW_smul S h hh d Λ n n' W0`. Establish `hn : n ∈ S.N` using `W0.2.2.1`.

Establish `hn' : n' ∈ S.N'` using `W0.2.2.2.1`. Establish `hN : h ∈ S.N` using `(Subgroup.mem_inf.mp hh).1`. Establish `hN' : h ∈ S.N'` using `(Subgroup.mem_inf.mp hh).2`. Take `⟨omA, MA, FrA, levA, -⟩` from `GlobalTheory.T.term_invariants_independent_of_witnesses L r k S d Λ n n' W0`. Take `⟨omB, MB, FrB, levB, -⟩` from `GlobalTheory.T.term_invariants_independent_of_witnesses L r k S d (h • Λ) (h * n) (h * n') W2`.

Take `⟨pm, pm', pn, -⟩` from `GlobalTheory.FramePsi.psi_unitary_character L r k S`. Establish `hpp : S.psi h = S.psi' h` using `GlobalTheory.T.frames_characters_agree_commonStabiliser L r k S h hh`. Establish `hM : S.M d (h • Λ) = h • S.M d Λ`. Rewrite using `[MB, MA]`. Conclude with `mof_smul S h _ _`.

Establish `hsat` using `sat_smul S h hh Λ`. Establish `hlev : ∀ y, S.levC d (h • Λ) (h y) = S.levC d Λ y`. Introduce `y`. Unfold `Frames.levC`. Rewrite using `[levB, levA]`.

Establish `e : algebraMap F E S.th • h y = h (algebraMap F E S.th • y)` using `(LinearEquiv.map_smul h _ y).symm`. Rewrite using `[e]`. Conclude with `lev_smul S h _ _ _`. Establish `hom : S.om d (h • Λ) = S.om d Λ`. Rewrite using `[omB, omA, pm h hN n hn, pm' h hN' n' hn', hpp]`.

Establish `hne : S.psi' h ≠ 0`. Introduce `e`. Establish `h1` using `(pn h).2`. Rewrite `h1` using `[e, norm_zero]`. Conclude with `zero_ne_one h1`.

Establish `key : ∀ a b c : ℂ, a ≠ 0 → a * b * (a * c)⁻¹ = b * c⁻¹`. Introduce `a b c ha`. Combine the equalities or inequalities in the displayed calculation. Conclude with `key _ _ _ hne`. Establish `hFr : S.Fr d (h • Λ) = h • S.Fr d Λ`.

Rewrite using `[FrB, FrA]`. Conclude with `frameCls_smul S h _ _`. Establish `hbe : S.be d (h • Λ) = S.be d Λ`. Unfold `Frames.be`. Rewrite using `[hM, hsat]`.

Conclude with `relIndex_smul S h _ _`. Establish `hcard : S.cardI d (h • Λ) = S.cardI d Λ`. Unfold `Frames.cardI`. Rewrite using `[hM, ihat_smul S h hh d Λ hM]`. Conclude with `relIndex_smul S h _ _`.

Establish `hBB : S.BBzero d (h • Λ) ↔ S.BBzero d Λ`. Unfold `Frames.BBzero`. Rewrite using `[hM, hsat]`. Conclude with `(MulAction.injective h).eq_iff`. Establish `hall : ∀ J, (∀ y ∈ S.sat (h • Λ), S.levC d (h • Λ) y ≤ J) ↔ ∀ y ∈ S.sat Λ, S.levC d Λ y ≤ J`.

Introduce `J`. Conclude with `(forall_sat S h hh Λ (fun y => S.levC d (h • Λ) y ≤ J)).trans (by simp only [hlev])`. Establish `hex : ∀ J, (∃ y ∈ S.sat (h • Λ), S.levC d (h • Λ) y = J) ↔ ∃ y ∈ S.sat Λ, S.levC d Λ y = J`. Introduce `J`. Conclude with `(exists_sat S h hh Λ (fun y => S.levC d (h • Λ) y = J)).trans (by simp only [hlev])`.

Establish `hX : ∀ v, h v ∈ S.X ↔ v ∈ S.X` using `fun v => spanTo_iff S h hh r v`. Establish `hX' : ∀ v, h v ∈ S.X' ↔ v ∈ S.X'` using `fun v => spanTo_iff' S h hh r v`. Establish `e : ∀ x, h (h⁻¹ x) = x` using `fun x => h.apply_symm_apply x`. Establish `third : (∀ x₁ ∈ S.X, ∀ x₁' ∈ S.X', ∀ x₂ ∈ S.X, ∀ x₂' ∈ S.X', S.InTh (h • Λ) (x₁ + x₁') → S.InTh (h • Λ) (x₂ + x₂') → ∃ c ∈ L.O, S.h x₁ x₂' = algebraMap F E S.th * c) ↔ (∀ x₁ ∈ S.X, ∀ x₁' ∈ S.X', ∀ x₂ ∈ S.X, ∀ x₂' ∈ S.X', S.InTh Λ (x₁ + x₁') → S.InTh Λ (x₂ + x₂') → ∃ c ∈ L.O, S.h …`. Prove the components needed by the constructor for the conclusion.

Introduce `H x₁ h1 x₁' h1' x₂ h2 x₂' h2' t1 t2`. Establish `t1'` using `(inTh_iff S h Λ (x₁ + x₁')).2 t1`. Establish `t2'` using `(inTh_iff S h Λ (x₂ + x₂')).2 t2`. Rewrite `t1'`, `t2'` using `[map_add]`. Establish `h3` using `H (h x₁) ((hX _).2 h1) (h x₁') ((hX' _).2 h1') (h x₂) ((hX _).2 h2) (h x₂') ((hX' _).2 h2') t1' t2'`.

Unfold `Frames.h at h3 ⊢`. Rewrite `h3` using `[isom S h hh]`. Then use the resulting hypothesis. Introduce `H x₁ h1 x₁' h1' x₂ h2 x₂' h2' t1 t2`. Establish `t1' : S.InTh (h • Λ) (h (h⁻¹ x₁ + h⁻¹ x₁'))`. Rewrite using `[map_add, e, e]`.

Conclude with `t1`. Establish `t2' : S.InTh (h • Λ) (h (h⁻¹ x₂ + h⁻¹ x₂'))`. Rewrite using `[map_add, e, e]`. Conclude with `t2`. Establish `h3` using `H (h⁻¹ x₁) ((hX _).1 (by rw [e]; exact h1)) (h⁻¹ x₁') ((hX' _).1 (by rw [e]; exact h1')) (h⁻¹ x₂) ((hX _).1 (by rw [e]; exact h2)) (h⁻¹ x₂') ((hX' _).1 (by rw [e]; exact h2')) ((inTh_iff S h Λ _).1 t1') ((inTh_iff S h Λ _).1 t2')`.

Unfold `Frames.h at h3 ⊢`. Rewrite `h3` using `[← isom S h hh, e, e]`. Then use the resulting hypothesis. Establish `hTB : S.TypeBe d (h • Λ) ↔ S.TypeBe d Λ`. Unfold `Frames.TypeBe`. Conclude with `and_congr (not_congr hBB) (and_congr (hall r) third)`.

Establish `hFF : ∀ β J βJ, S.InFF β J βJ d (h • Λ) ↔ S.InFF β J βJ d Λ`. Introduce `β J βJ`. Unfold `Frames.InFF`. Rewrite using `[hbe, nLev_smul S h hh d Λ hM hlev J]`. Conclude with `and_congr hTB (and_congr Iff.rfl (and_congr (hall J) (and_congr (hex J) Iff.rfl)))`.

Establish `hmove : ∀ J x x' u s, S.IsMove J d Λ x x' u s ↔ S.IsMove J d (h • Λ) (h x) (h x') (h u) s`. Introduce `J x x' u s`. Establish `ha : h x + h x' = h (x + x')` using `(map_add h x x').symm`. Establish `hl : S.lev (S.fr d (h • Λ)) (S.fr' d (h • Λ)) (h x + h x') = S.lev (S.fr d Λ) (S.fr' d Λ) (x + x')`. Rewrite using `[levB, levA, ha]`.

Conclude with `lev_smul S h _ _ _`. Establish `hin : S.InTh (h • Λ) (h x + h x') ↔ S.InTh Λ (x + x')`. Rewrite using `[ha]`. Conclude with `inTh_iff S h Λ _`. Establish `hu : h u ∈ h • Λ ↔ u ∈ Λ` using `mem_smul_iff S h Λ u`.

Establish `hp : h u ∈ perp L S.Hm (S.spanTo S.f J ⊔ S.spanTo S.f' J) ↔ u ∈ perp L S.Hm (S.spanTo S.f J ⊔ S.spanTo S.f' J)` using `perp_iff S h hh _ (sup_iff S h hh J) u`. Establish `hs : S.h (h u) (h u) = S.h u u` using `isom S h hh u u`. Unfold `Frames.IsMove`. Rewrite using `[spanTo_iff S h hh J x, spanTo_iff' S h hh J x', hin, hl, hu, hp, hs]`. Conclude with `⟨⟨(h * n, h * n'), W2⟩, hom, hM, hsat, hFr, hbe, hcard, hBB, hTB, hFF, hmove⟩`.
-/
theorem stabiliser_acts_on_terms : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → ∀ h ∈ S.St, S.IsTerm d (h • Λ) ∧ S.om d (h • Λ) = S.om d Λ ∧ S.M d (h • Λ) = h • S.M d Λ ∧ S.sat (h • Λ) = h • S.sat Λ ∧ S.Fr d (h • Λ) = h • S.Fr d Λ ∧ S.be d (h • Λ) = S.be d Λ ∧ S.cardI d (h • Λ) = S.cardI d Λ ∧ (S.BBzero d (h • Λ) ↔ S.BBzero d Λ) ∧ (S.TypeBe d (h • Λ) ↔ S.TypeBe d Λ) ∧ (∀ β J βJ, S.InFF β J βJ d (h • Λ) ↔ S.InFF β J βJ d Λ) ∧ ∀ J x x' u s, S.IsMove J d Λ x x' u s ↔ S.IsMove J d (h • Λ) (h x) (h x') (h u) s := by
  intro F _ _ _ _ _ E _ _ _ L r k S d Λ hT h hh
  obtain ⟨⟨n, n'⟩, W⟩ := hT
  have W0 : S.IsTermW d Λ n n' := W
  have W2 := isTermW_smul S h hh d Λ n n' W0
  have hn : n ∈ S.N := W0.2.2.1
  have hn' : n' ∈ S.N' := W0.2.2.2.1
  have hN : h ∈ S.N := (Subgroup.mem_inf.mp hh).1
  have hN' : h ∈ S.N' := (Subgroup.mem_inf.mp hh).2
  obtain ⟨omA, MA, FrA, levA, -⟩ := GlobalTheory.T.term_invariants_independent_of_witnesses L r k S d Λ n n' W0
  obtain ⟨omB, MB, FrB, levB, -⟩ := GlobalTheory.T.term_invariants_independent_of_witnesses L r k S d (h • Λ) (h * n) (h * n') W2
  obtain ⟨pm, pm', pn, -⟩ := GlobalTheory.FramePsi.psi_unitary_character L r k S
  have hpp : S.psi h = S.psi' h := GlobalTheory.T.frames_characters_agree_commonStabiliser L r k S h hh
  have hM : S.M d (h • Λ) = h • S.M d Λ := by
    rw [MB, MA]
    exact mof_smul S h _ _
  have hsat := sat_smul S h hh Λ
  have hlev : ∀ y, S.levC d (h • Λ) (h y) = S.levC d Λ y := by
    intro y
    unfold Frames.levC
    rw [levB, levA]
    have e : algebraMap F E S.th • h y = h (algebraMap F E S.th • y) :=
      (LinearEquiv.map_smul h _ y).symm
    rw [e]
    exact lev_smul S h _ _ _
  have hom : S.om d (h • Λ) = S.om d Λ := by
    rw [omB, omA, pm h hN n hn, pm' h hN' n' hn', hpp]
    have hne : S.psi' h ≠ 0 := by
      intro e
      have h1 := (pn h).2
      rw [e, norm_zero] at h1
      exact zero_ne_one h1
    have key : ∀ a b c : ℂ, a ≠ 0 → a * b * (a * c)⁻¹ = b * c⁻¹ := by
      intro a b c ha
      calc a * b * (a * c)⁻¹ = (a * a⁻¹) * (b * c⁻¹) := by ring
        _ = b * c⁻¹ := by rw [mul_inv_cancel₀ ha, one_mul]
    exact key _ _ _ hne
  have hFr : S.Fr d (h • Λ) = h • S.Fr d Λ := by
    rw [FrB, FrA]
    exact frameCls_smul S h _ _
  have hbe : S.be d (h • Λ) = S.be d Λ := by
    unfold Frames.be
    rw [hM, hsat]
    exact relIndex_smul S h _ _
  have hcard : S.cardI d (h • Λ) = S.cardI d Λ := by
    unfold Frames.cardI
    rw [hM, ihat_smul S h hh d Λ hM]
    exact relIndex_smul S h _ _
  have hBB : S.BBzero d (h • Λ) ↔ S.BBzero d Λ := by
    unfold Frames.BBzero
    rw [hM, hsat]
    exact (MulAction.injective h).eq_iff
  have hall : ∀ J, (∀ y ∈ S.sat (h • Λ), S.levC d (h • Λ) y ≤ J) ↔
      ∀ y ∈ S.sat Λ, S.levC d Λ y ≤ J := by
    intro J
    exact (forall_sat S h hh Λ (fun y => S.levC d (h • Λ) y ≤ J)).trans (by simp only [hlev])
  have hex : ∀ J, (∃ y ∈ S.sat (h • Λ), S.levC d (h • Λ) y = J) ↔
      ∃ y ∈ S.sat Λ, S.levC d Λ y = J := by
    intro J
    exact (exists_sat S h hh Λ (fun y => S.levC d (h • Λ) y = J)).trans (by simp only [hlev])
  have hX : ∀ v, h v ∈ S.X ↔ v ∈ S.X := fun v => spanTo_iff S h hh r v
  have hX' : ∀ v, h v ∈ S.X' ↔ v ∈ S.X' := fun v => spanTo_iff' S h hh r v
  have e : ∀ x, h (h⁻¹ x) = x := fun x => h.apply_symm_apply x
  have third : (∀ x₁ ∈ S.X, ∀ x₁' ∈ S.X', ∀ x₂ ∈ S.X, ∀ x₂' ∈ S.X', S.InTh (h • Λ) (x₁ + x₁') →
        S.InTh (h • Λ) (x₂ + x₂') → ∃ c ∈ L.O, S.h x₁ x₂' = algebraMap F E S.th * c) ↔
      (∀ x₁ ∈ S.X, ∀ x₁' ∈ S.X', ∀ x₂ ∈ S.X, ∀ x₂' ∈ S.X', S.InTh Λ (x₁ + x₁') →
        S.InTh Λ (x₂ + x₂') → ∃ c ∈ L.O, S.h x₁ x₂' = algebraMap F E S.th * c) := by
    constructor
    · intro H x₁ h1 x₁' h1' x₂ h2 x₂' h2' t1 t2
      have t1' := (inTh_iff S h Λ (x₁ + x₁')).2 t1
      have t2' := (inTh_iff S h Λ (x₂ + x₂')).2 t2
      rw [map_add] at t1' t2'
      have h3 := H (h x₁) ((hX _).2 h1) (h x₁') ((hX' _).2 h1') (h x₂) ((hX _).2 h2)
        (h x₂') ((hX' _).2 h2') t1' t2'
      unfold Frames.h at h3 ⊢
      rwa [isom S h hh] at h3
    · intro H x₁ h1 x₁' h1' x₂ h2 x₂' h2' t1 t2
      have t1' : S.InTh (h • Λ) (h (h⁻¹ x₁ + h⁻¹ x₁')) := by
        rw [map_add, e, e]
        exact t1
      have t2' : S.InTh (h • Λ) (h (h⁻¹ x₂ + h⁻¹ x₂')) := by
        rw [map_add, e, e]
        exact t2
      have h3 := H (h⁻¹ x₁) ((hX _).1 (by rw [e]; exact h1)) (h⁻¹ x₁') ((hX' _).1 (by rw [e]; exact h1'))
        (h⁻¹ x₂) ((hX _).1 (by rw [e]; exact h2)) (h⁻¹ x₂') ((hX' _).1 (by rw [e]; exact h2'))
        ((inTh_iff S h Λ _).1 t1') ((inTh_iff S h Λ _).1 t2')
      unfold Frames.h at h3 ⊢
      rwa [← isom S h hh, e, e] at h3
  have hTB : S.TypeBe d (h • Λ) ↔ S.TypeBe d Λ := by
    unfold Frames.TypeBe
    exact and_congr (not_congr hBB) (and_congr (hall r) third)
  have hFF : ∀ β J βJ, S.InFF β J βJ d (h • Λ) ↔ S.InFF β J βJ d Λ := by
    intro β J βJ
    unfold Frames.InFF
    rw [hbe, nLev_smul S h hh d Λ hM hlev J]
    exact and_congr hTB (and_congr Iff.rfl (and_congr (hall J) (and_congr (hex J) Iff.rfl)))
  have hmove : ∀ J x x' u s, S.IsMove J d Λ x x' u s ↔
      S.IsMove J d (h • Λ) (h x) (h x') (h u) s := by
    intro J x x' u s
    have ha : h x + h x' = h (x + x') := (map_add h x x').symm
    have hl : S.lev (S.fr d (h • Λ)) (S.fr' d (h • Λ)) (h x + h x') =
        S.lev (S.fr d Λ) (S.fr' d Λ) (x + x') := by
      rw [levB, levA, ha]
      exact lev_smul S h _ _ _
    have hin : S.InTh (h • Λ) (h x + h x') ↔ S.InTh Λ (x + x') := by
      rw [ha]
      exact inTh_iff S h Λ _
    have hu : h u ∈ h • Λ ↔ u ∈ Λ := mem_smul_iff S h Λ u
    have hp : h u ∈ perp L S.Hm (S.spanTo S.f J ⊔ S.spanTo S.f' J) ↔
        u ∈ perp L S.Hm (S.spanTo S.f J ⊔ S.spanTo S.f' J) :=
      perp_iff S h hh _ (sup_iff S h hh J) u
    have hs : S.h (h u) (h u) = S.h u u := isom S h hh u u
    unfold Frames.IsMove
    rw [spanTo_iff S h hh J x, spanTo_iff' S h hh J x', hin, hl, hu, hp, hs]
  exact ⟨⟨(h * n, h * n'), W2⟩, hom, hM, hsat, hFr, hbe, hcard, hBB, hTB, hFF, hmove⟩

end GlobalTheory.FrameAct
