import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsFieldChartRingOverPnPtZero
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ConstVanishHypSegment
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsBisMore
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (Cell cellMon CechC cellRes faceSign cechD locPart cechCc cechZc cechBc cechHc
  mIdealOver mConeMapOver chartRingOver quotPart)

namespace CechPointVanish

set_option linter.unusedSectionVars false

section Cells

variable {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type} [∀ k, LinearOrder (ι k)]

/- English proof (translation)
Distinguish the cases in `hl : l = k`. Substitute `hl` using the available equality. Rewrite using `[Function.update_self]`. Conclude with `Finset.erase_subset _ _`. Rewrite using `[Function.update_of_ne hl]`.
-/
theorem face_subset (I : ∀ k, Finset (ι k)) (k : K) (i : ι k) (l : K) :
    Function.update I k ((I k).erase i) l ⊆ I l := by
  by_cases hl : l = k
  · subst hl
    rw [Function.update_self]
    exact Finset.erase_subset _ _
  · rw [Function.update_of_ne hl]

/- English proof (translation)
Unfold `constD`. Simplify using `only [map_sum]`. Use `Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Apply the tactic sequence `split_ifs <;> simp [map_zsmul]`.
-/
theorem map_constD {V W : Type} [AddCommGroup V] [AddCommGroup W] (g : V →+ W) (n : ℕ)
    (f : Cell K ι n → V) (I : Cell K ι (n + 1)) :
    g (constD K ι V n f I) = constD K ι W n (fun J => g (f J)) I := by
  unfold constD
  simp only [map_sum]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp [map_zsmul]

/- English proof (translation)
Unfold `constD`. Use `Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Use `split_ifs with hc`. Conclude with `congrArg _ (h _ fun l => (face_subset I.1 k i l).trans (hI l))`. Both sides reduce to the same expression.
-/
theorem constD_congr {V : Type} [AddCommGroup V] (G : ∀ k, Finset (ι k)) (n : ℕ) {f f' : Cell K ι n → V}
    (h : ∀ J : Cell K ι n, (∀ k, J.1 k ⊆ G k) → f J = f' J) (I : Cell K ι (n + 1)) (hI : ∀ k, I.1 k ⊆ G k) :
    constD K ι V n f I = constD K ι V n f' I := by
  unfold constD
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
  split_ifs with hc
  · exact congrArg _ (h _ fun l => (face_subset I.1 k i l).trans (hI l))
  · rfl

variable {S : Type} [CommRing S]

/- English proof (translation)
Apply `Submonoid.closure_mono` to reduce the goal to its premises. Introduce and unpack `f ⟨k, i, hi, rfl⟩`. Conclude with `⟨k, i, h k hi, rfl⟩`.
-/
theorem cellMon_mono {J I : ∀ k, Finset (ι k)} (h : ∀ k, J k ⊆ I k) : cellMon S J ≤ cellMon S I := by
  apply Submonoid.closure_mono
  rintro f ⟨k, i, hi, rfl⟩
  exact ⟨k, i, h k hi, rfl⟩

/- English proof (translation)
Unfold `cellRes`. Rewrite using `[dif_pos h, IsLocalizedModule.mk_eq_mk', IsLocalizedModule.liftOfLE_mk', ← IsLocalizedModule.mk_eq_mk']`.
-/
theorem cellRes_mk {M : Type} [AddCommGroup M] [Module (MRingOver S ι) M] {J I : ∀ k, Finset (ι k)}
    (h : cellMon S J ≤ cellMon S I) (m : M) (t : cellMon S J) :
    cellRes S M J I (LocalizedModule.mk m t) = LocalizedModule.mk m ⟨t.1, h t.2⟩ := by
  unfold cellRes
  rw [dif_pos h, IsLocalizedModule.mk_eq_mk', IsLocalizedModule.liftOfLE_mk', ← IsLocalizedModule.mk_eq_mk']

open Classical in

/- English proof (translation)
Simplify using `only [cechD, LinearMap.pi_apply, LinearMap.sum_apply]`. Use `Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Apply the tactic sequence `split_ifs <;> rfl`.
-/
theorem cechD_apply {M : Type} [AddCommGroup M] [Module (MRingOver S ι) M] (n : ℕ) (f : CechC S ι M n)
    (I : Cell K ι (n + 1)) :
    cechD S ι M n f I = ∑ k, ∑ i ∈ I.1 k,
      if h : (∀ l, (Function.update I.1 k ((I.1 k).erase i) l).Nonempty) ∧
          ∑ l, ((Function.update I.1 k ((I.1 k).erase i) l).card - 1) = n then
        faceSign I.1 k i • cellRes S M _ I.1 (f ⟨Function.update I.1 k ((I.1 k).erase i), h⟩)
      else 0 := by
  simp only [cechD, LinearMap.pi_apply, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> rfl

end Cells

section Point

variable {F : Type} [Field F] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type} [∀ k, Fintype (ι k)]
  [∀ k, LinearOrder (ι k)] {Ω : Type} [Field Ω] [Algebra F Ω] {y : (Σ k, ι k) → Ω}

/- English proof (translation)
Establish `hX : (X ⟨k, i⟩ : MRingOver F ι) ∈ cellMon F I` using `Submonoid.subset_closure ⟨k, i, hi, rfl⟩`. Establish `hmem : (X ⟨k, i⟩ : MRingOver F ι) ∈ mIdealOver F y`. Simplify using `[mIdealOver, mConeMapOver, RingHom.mem_ker, hy]`. Establish `hz : ∀ w : MRingOver F ι ⧸ mIdealOver F y, (X ⟨k, i⟩ : MRingOver F ι) • w = 0`. Introduce `w`.

Take `⟨g, rfl⟩` from `Submodule.Quotient.mk_surjective _ w`. Rewrite using `[← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, smul_eq_mul]`. Conclude with `Ideal.mul_mem_right _ _ hmem`. Use `⟨fun a b => ?_⟩` and prove the remaining obligations. Proceed by induction on `a using LocalizedModule.induction_on with`.

Consider the case `h m t`. Proceed by induction on `b using LocalizedModule.induction_on with`. Consider the case `h m' t'`. Rewrite using `[LocalizedModule.mk_eq]`. Use `⟨⟨_, hX⟩, ?_⟩` and prove the remaining obligations.

Simplify using `only [Submonoid.smul_def]`. Rewrite using `[hz, hz]`.
-/
theorem subsingleton_of_bad {I : ∀ k, Finset (ι k)} {k : K} {i : ι k} (hi : i ∈ I k) (hy : y ⟨k, i⟩ = 0) :
    Subsingleton (LocalizedModule (cellMon F I) (MRingOver F ι ⧸ mIdealOver F y)) := by
  have hX : (X ⟨k, i⟩ : MRingOver F ι) ∈ cellMon F I := Submonoid.subset_closure ⟨k, i, hi, rfl⟩
  have hmem : (X ⟨k, i⟩ : MRingOver F ι) ∈ mIdealOver F y := by
    simp [mIdealOver, mConeMapOver, RingHom.mem_ker, hy]
  have hz : ∀ w : MRingOver F ι ⧸ mIdealOver F y, (X ⟨k, i⟩ : MRingOver F ι) • w = 0 := by
    intro w
    obtain ⟨g, rfl⟩ := Submodule.Quotient.mk_surjective _ w
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, smul_eq_mul]
    exact Ideal.mul_mem_right _ _ hmem
  refine ⟨fun a b => ?_⟩
  induction a using LocalizedModule.induction_on with
  | h m t =>
    induction b using LocalizedModule.induction_on with
    | h m' t' =>
      rw [LocalizedModule.mk_eq]
      refine ⟨⟨_, hX⟩, ?_⟩
      simp only [Submonoid.smul_def]
      rw [hz, hz]

/- English proof (translation)
Distinguish the cases in `h : cellMon F J ≤ cellMon F I`. Proceed by induction on `x using LocalizedModule.induction_on with`. Consider the case `h m t => rw [LocalizedModule.smul'_mk, cellRes_mk h, cellRes_mk h, LocalizedModule.smul'_mk]`. Unfold `cellRes`. Rewrite using `[dif_neg h]`.

Simplify using the standard rewrite rules.
-/
theorem cellRes_smul {J I : ∀ k, Finset (ι k)} (s : F)
    (x : LocalizedModule (cellMon F J) (MRingOver F ι ⧸ mIdealOver F y)) :
    cellRes F _ J I (s • x) = s • cellRes F _ J I x := by
  by_cases h : cellMon F J ≤ cellMon F I
  · induction x using LocalizedModule.induction_on with
    | h m t => rw [LocalizedModule.smul'_mk, cellRes_mk h, cellRes_mk h, LocalizedModule.smul'_mk]
  · unfold cellRes
    rw [dif_neg h]
    simp

/- English proof (translation)
Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨m, t, a, ht, hm, rfl⟩` from `hx`. Rewrite using `[cellRes_mk h]`. Conclude with `Submodule.subset_span ⟨m, ⟨t.1, h t.2⟩, a, ht, hm, rfl⟩`.

Consider the case `zero => rw [map_zero]`. Conclude with `Submodule.zero_mem _`. Consider the case `add x₁ x₂ _ _ h₁ h₂ => rw [map_add]`. Conclude with `add_mem h₁ h₂`. Consider the case `smul s x _ h' => rw [cellRes_smul]`.

Conclude with `Submodule.smul_mem _ s h'`.
-/
theorem cellRes_mem_locPart {J I : ∀ k, Finset (ι k)} (h : cellMon F J ≤ cellMon F I) (β : K → ℤ)
    {x : LocalizedModule (cellMon F J) (MRingOver F ι ⧸ mIdealOver F y)}
    (hx : x ∈ locPart ι (quotPart F (mIdealOver F y)) (cellMon F J) β) :
    cellRes F _ J I x ∈ locPart ι (quotPart F (mIdealOver F y)) (cellMon F I) β := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, t, a, ht, hm, rfl⟩ := hx
    rw [cellRes_mk h]
    exact Submodule.subset_span ⟨m, ⟨t.1, h t.2⟩, a, ht, hm, rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x₁ x₂ _ _ h₁ h₂ => rw [map_add]; exact add_mem h₁ h₂
  | smul s x _ h' => rw [cellRes_smul]; exact Submodule.smul_mem _ s h'

/- English proof (translation)
Rewrite using `[cechD_apply]`. Use `Submodule.sum_mem _ fun k _ => Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Use `split_ifs with hc`. Establish `hJ : f ⟨Function.update I.1 k ((I.1 k).erase i), hc⟩ ∈ locPart ι (quotPart F (mIdealOver F y)) (cellMon F (Function.update I.1 k ((I.1 k).erase i))) β` using `Submodule.mem_pi.mp hf ⟨Function.update I.1 k ((I.1 k).erase i), hc⟩ (Set.mem_univ _)`. Establish `hm` using `cellRes_mem_locPart (J := Function.update I.1 k ((I.1 k).erase i)) (I := I.1) (cellMon_mono (face_subset I.1 k i)) β hJ`.

Conclude with `zsmul_mem hm _`. Conclude with `Submodule.zero_mem _`.
-/
theorem cechD_mem_locPart (β : K → ℤ) (n : ℕ) {f : CechC F ι (MRingOver F ι ⧸ mIdealOver F y) n}
    (hf : f ∈ cechCc ι (quotPart F (mIdealOver F y)) β n) (I : Cell K ι (n + 1)) :
    cechD F ι _ n f I ∈ locPart ι (quotPart F (mIdealOver F y)) (cellMon F I.1) β := by
  rw [cechD_apply]
  refine Submodule.sum_mem _ fun k _ => Submodule.sum_mem _ fun i _ => ?_
  split_ifs with hc
  · have hJ : f ⟨Function.update I.1 k ((I.1 k).erase i), hc⟩ ∈ locPart ι (quotPart F (mIdealOver F y))
        (cellMon F (Function.update I.1 k ((I.1 k).erase i))) β :=
      Submodule.mem_pi.mp hf ⟨Function.update I.1 k ((I.1 k).erase i), hc⟩ (Set.mem_univ _)
    have hm := cellRes_mem_locPart (J := Function.update I.1 k ((I.1 k).erase i)) (I := I.1)
      (cellMon_mono (face_subset I.1 k i)) β hJ
    exact zsmul_mem hm _
  · exact Submodule.zero_mem _

end Point

/- English proof (translation)
Introduce `F _ K _ _ ι _ _ Ω _ _ y hfield β`. Take `⟨V, φ, hφ⟩` from `h₂ F K ι Ω y hfield β`. Set `G : ∀ k, Finset (ι k)` to `fun k => Finset.univ.filter fun i => y ⟨k, i⟩ ≠ 0`. Establish `hG : ∀ I : ∀ k, Finset (ι k), (∀ k, I k ⊆ G k) ↔ ∀ k, ∀ i ∈ I k, y ⟨k, i⟩ ≠ 0`. Introduce `I`.

Simplify using `[G, Finset.subset_iff]`. Establish `hbad : ∀ I : ∀ k, Finset (ι k), ¬ (∀ k, I k ⊆ G k) → Subsingleton (LocalizedModule (cellMon F I) (MRingOver F ι ⧸ mIdealOver F y))`. Introduce `I hI`. Rewrite `hI` using `[hG]`. Use `push Not at hI`.

Take `⟨k, i, hi, hy⟩` from `hI`. Conclude with `subsingleton_of_bad hi hy`. Establish `hres : ∀ J I : ∀ k, Finset (ι k), (∀ k, J k ⊆ I k) → (∀ k, (J k).Nonempty) → (∀ k, I k ⊆ G k) → ∀ x, φ I (cellRes F _ J I x) = φ J x`. Introduce `J I hJI hJ hI x`. Establish `hIg` using `(hG I).mp hI`.

Establish `hJg` using `(hG J).mp fun k => (hJI k).trans (hI k)`. Establish `hIn : ∀ k, (I k).Nonempty` using `fun k => (hJ k).mono (hJI k)`. Proceed by induction on `x using LocalizedModule.induction_on with`. Consider the case `h m t`. Take `⟨g, rfl⟩` from `Ideal.Quotient.mk_surjective m`.

Rewrite using `[cellRes_mk (cellMon_mono hJI), (hφ I hIn hIg).1, (hφ J hJ hJg).1]`. Establish `hdiff : ∀ (n : ℕ) (x : CechC F ι (MRingOver F ι ⧸ mIdealOver F y) n) (I : Cell K ι (n + 1)), (∀ k, I.1 k ⊆ G k) → φ I.1 (cechD F ι _ n x I) = constD K ι Ω n (fun J => φ J.1 (x J)) I`. Introduce `n x I hI`. Rewrite using `[cechD_apply]`. Simplify using `only [constD, map_sum]`.

Use `Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Use `split_ifs with hc`. Rewrite using `[map_zsmul, hres _ _ (face_subset I.1 k i) hc.1 hI]`. Simplify using the standard rewrite rules. Rewrite using `[Submodule.Quotient.subsingleton_iff, eq_top_iff]`.

Introduce and unpack `⟨z, hz⟩ -`. Take `⟨hzC, hzK⟩` from `Submodule.mem_inf.mp hz`. Establish `hzK' : cechD F ι _ 1 z = 0` using `hzK`. Establish `hzC' : ∀ J : Cell K ι 1, z J ∈ locPart ι (quotPart F (mIdealOver F y)) (cellMon F J.1) β` using `fun J => Submodule.mem_pi.mp hzC J (Set.mem_univ _)`. Set `zh : Cell K ι 1 → V` to `fun J => if hJ : ∀ k, J.1 k ⊆ G k then ⟨φ J.1 (z J), by`.

Rewrite using `[← (hφ J.1 J.2.1 ((hG _).mp hJ)).2.2]`. Conclude with `Submodule.mem_map_of_mem (hzC' J)⟩ else 0`. Establish `hzh : ∀ J : Cell K ι 1, (∀ k, J.1 k ⊆ G k) → ((zh J : V) : Ω) = φ J.1 (z J)`. Introduce `J hJ`. Simplify using `only [zh, dif_pos hJ]`.

Establish `hcoc : ∀ I : Cell K ι 2, (∀ k, I.1 k ⊆ G k) → constD K ι V 1 zh I = 0`. Introduce `I hI`. Apply `Subtype.ext` to reduce the goal to its premises. Establish `e` using `map_constD V.subtype.toAddMonoidHom 1 zh I`. Simplify using `only [LinearMap.toAddMonoidHom_coe, Submodule.coe_subtype] at e`.

Rewrite using `[e, constD_congr G 1 hzh I hI, ← hdiff 1 z I hI, hzK']`. Simplify using the standard rewrite rules. Take `⟨fh, hfh⟩` from `h₁ K ι V G zh hcoc`. Establish `hlift : ∀ c : Cell K ι 0, (∀ k, c.1 k ⊆ G k) → ∃ w ∈ locPart ι (quotPart F (mIdealOver F y)) (cellMon F c.1) β, φ c.1 w = fh c`. Introduce `c hc`.

Establish `h : ((fh c : V) : Ω) ∈ (locPart ι (quotPart F (mIdealOver F y)) (cellMon F c.1) β).map (φ c.1)`. Rewrite using `[(hφ c.1 c.2.1 ((hG _).mp hc)).2.2]`. Conclude with `(fh c).2`. Conclude with `Submodule.mem_map.mp h`. Set `f : CechC F ι (MRingOver F ι ⧸ mIdealOver F y) 0` to `fun c => if hc : ∀ k, c.1 k ⊆ G k then (hlift c hc).choose else 0`.

Establish `hfC : f ∈ cechCc ι (quotPart F (mIdealOver F y)) β 0`. Use `Submodule.mem_pi.mpr fun c _ => ?_` and prove the remaining obligations. Distinguish the cases in `hc : ∀ k, c.1 k ⊆ G k`. Simplify using `only [f, dif_pos hc]`. Conclude with `(hlift c hc).choose_spec.1`.

Simplify using `only [f, dif_neg hc]`. Conclude with `Submodule.zero_mem _`. Establish `hfφ : ∀ c : Cell K ι 0, (∀ k, c.1 k ⊆ G k) → φ c.1 (f c) = ((fh c : V) : Ω)`. Introduce `c hc`. Simplify using `only [f, dif_pos hc]`.

Conclude with `(hlift c hc).choose_spec.2`. Establish `hfz : cechD F ι _ 0 f = z`. Use function extensionality and compare the values at `J`. Distinguish the cases in `hJ : ∀ k, J.1 k ⊆ G k`. Use `(hφ J.1 J.2.1 ((hG _).mp hJ)).2.1 (cechD_mem_locPart β 0 hfC J) (hzC' J) ?_` and prove the remaining obligations.

Establish `e` using `map_constD V.subtype.toAddMonoidHom 0 fh J`. Simplify using `only [LinearMap.toAddMonoidHom_coe, Submodule.coe_subtype] at e`. Rewrite using `[hdiff 0 f J hJ, constD_congr G 0 hfφ J hJ, ← e, hfh J hJ, hzh J hJ]`. Use `hbad J.1 hJ` as an intermediate fact. Conclude with `Subsingleton.elim _ _`.

Use `show z ∈ (cechCc ι (quotPart F (mIdealOver F y)) β 0).map ((cechD F ι _ 0).restrictScalars F)`. Conclude with `⟨f, hfC, hfz⟩`.
-/
theorem proof (h₁ : CechConstVanish.Statement) (h₂ : CechPointEval.Statement) : CechPointVanish.Statement := by
  intro F _ K _ _ ι _ _ Ω _ _ y hfield β
  classical
  obtain ⟨V, φ, hφ⟩ := h₂ F K ι Ω y hfield β
  let G : ∀ k, Finset (ι k) := fun k => Finset.univ.filter fun i => y ⟨k, i⟩ ≠ 0
  have hG : ∀ I : ∀ k, Finset (ι k), (∀ k, I k ⊆ G k) ↔ ∀ k, ∀ i ∈ I k, y ⟨k, i⟩ ≠ 0 := by
    intro I
    simp [G, Finset.subset_iff]
  have hbad : ∀ I : ∀ k, Finset (ι k), ¬ (∀ k, I k ⊆ G k) →
      Subsingleton (LocalizedModule (cellMon F I) (MRingOver F ι ⧸ mIdealOver F y)) := by
    intro I hI
    rw [hG] at hI
    push Not at hI
    obtain ⟨k, i, hi, hy⟩ := hI
    exact subsingleton_of_bad hi hy
  have hres : ∀ J I : ∀ k, Finset (ι k), (∀ k, J k ⊆ I k) → (∀ k, (J k).Nonempty) → (∀ k, I k ⊆ G k) →
      ∀ x, φ I (cellRes F _ J I x) = φ J x := by
    intro J I hJI hJ hI x
    have hIg := (hG I).mp hI
    have hJg := (hG J).mp fun k => (hJI k).trans (hI k)
    have hIn : ∀ k, (I k).Nonempty := fun k => (hJ k).mono (hJI k)
    induction x using LocalizedModule.induction_on with
    | h m t =>
      obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective m
      rw [cellRes_mk (cellMon_mono hJI), (hφ I hIn hIg).1, (hφ J hJ hJg).1]
  have hdiff : ∀ (n : ℕ) (x : CechC F ι (MRingOver F ι ⧸ mIdealOver F y) n) (I : Cell K ι (n + 1)),
      (∀ k, I.1 k ⊆ G k) → φ I.1 (cechD F ι _ n x I) = constD K ι Ω n (fun J => φ J.1 (x J)) I := by
    intro n x I hI
    rw [cechD_apply]
    simp only [constD, map_sum]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
    split_ifs with hc
    · rw [map_zsmul, hres _ _ (face_subset I.1 k i) hc.1 hI]
    · simp
  rw [Submodule.Quotient.subsingleton_iff, eq_top_iff]
  rintro ⟨z, hz⟩ -
  obtain ⟨hzC, hzK⟩ := Submodule.mem_inf.mp hz
  have hzK' : cechD F ι _ 1 z = 0 := hzK
  have hzC' : ∀ J : Cell K ι 1, z J ∈ locPart ι (quotPart F (mIdealOver F y)) (cellMon F J.1) β :=
    fun J => Submodule.mem_pi.mp hzC J (Set.mem_univ _)

  let zh : Cell K ι 1 → V := fun J => if hJ : ∀ k, J.1 k ⊆ G k then
    ⟨φ J.1 (z J), by
      rw [← (hφ J.1 J.2.1 ((hG _).mp hJ)).2.2]
      exact Submodule.mem_map_of_mem (hzC' J)⟩ else 0
  have hzh : ∀ J : Cell K ι 1, (∀ k, J.1 k ⊆ G k) → ((zh J : V) : Ω) = φ J.1 (z J) := by
    intro J hJ
    simp only [zh, dif_pos hJ]
  have hcoc : ∀ I : Cell K ι 2, (∀ k, I.1 k ⊆ G k) → constD K ι V 1 zh I = 0 := by
    intro I hI
    apply Subtype.ext
    have e := map_constD V.subtype.toAddMonoidHom 1 zh I
    simp only [LinearMap.toAddMonoidHom_coe, Submodule.coe_subtype] at e
    rw [e, constD_congr G 1 hzh I hI, ← hdiff 1 z I hI, hzK']
    simp
  obtain ⟨fh, hfh⟩ := h₁ K ι V G zh hcoc

  have hlift : ∀ c : Cell K ι 0, (∀ k, c.1 k ⊆ G k) →
      ∃ w ∈ locPart ι (quotPart F (mIdealOver F y)) (cellMon F c.1) β, φ c.1 w = fh c := by
    intro c hc
    have h : ((fh c : V) : Ω) ∈ (locPart ι (quotPart F (mIdealOver F y)) (cellMon F c.1) β).map (φ c.1) := by
      rw [(hφ c.1 c.2.1 ((hG _).mp hc)).2.2]
      exact (fh c).2
    exact Submodule.mem_map.mp h
  let f : CechC F ι (MRingOver F ι ⧸ mIdealOver F y) 0 := fun c =>
    if hc : ∀ k, c.1 k ⊆ G k then (hlift c hc).choose else 0
  have hfC : f ∈ cechCc ι (quotPart F (mIdealOver F y)) β 0 := by
    refine Submodule.mem_pi.mpr fun c _ => ?_
    by_cases hc : ∀ k, c.1 k ⊆ G k
    · simp only [f, dif_pos hc]
      exact (hlift c hc).choose_spec.1
    · simp only [f, dif_neg hc]
      exact Submodule.zero_mem _
  have hfφ : ∀ c : Cell K ι 0, (∀ k, c.1 k ⊆ G k) → φ c.1 (f c) = ((fh c : V) : Ω) := by
    intro c hc
    simp only [f, dif_pos hc]
    exact (hlift c hc).choose_spec.2
  have hfz : cechD F ι _ 0 f = z := by
    funext J
    by_cases hJ : ∀ k, J.1 k ⊆ G k
    · refine (hφ J.1 J.2.1 ((hG _).mp hJ)).2.1 (cechD_mem_locPart β 0 hfC J) (hzC' J) ?_
      have e := map_constD V.subtype.toAddMonoidHom 0 fh J
      simp only [LinearMap.toAddMonoidHom_coe, Submodule.coe_subtype] at e
      rw [hdiff 0 f J hJ, constD_congr G 0 hfφ J hJ, ← e, hfh J hJ, hzh J hJ]
    · have := hbad J.1 hJ
      exact Subsingleton.elim _ _
  show z ∈ (cechCc ι (quotPart F (mIdealOver F y)) β 0).map ((cechD F ι _ 0).restrictScalars F)
  exact ⟨f, hfC, hfz⟩

end CechPointVanish

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
