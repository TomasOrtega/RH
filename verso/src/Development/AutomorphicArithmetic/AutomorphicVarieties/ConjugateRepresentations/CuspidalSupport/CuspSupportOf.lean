import Development.AutomorphicArithmetic.AutomorphicVarieties.IntegralityNearIdentity.TensEig
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.TwoVar
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.CapArith
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.SatArith
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.SumInner
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.MatBlock
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.HkSum
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.HkLocal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.SatOfEig
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.Gl2LocalToAdelicEmbedding
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.TauSat
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.LevelSplit
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.CapAct
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.CapOfEig
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.TypesComm
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.HullBdd
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.HullOps
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.StabSp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.OpComm
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.SingleBdd
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.SliceBdd
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.LocComm
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.Imports
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.CtCap
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.CtSat
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.LieEqLam
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.CapBlock
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.CapRel
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.MemFixed
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.PairEig
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.ImportsAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.CiBasic
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.CiCompl
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.CuspProj
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.SuppCusp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.SuppTwist
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.SuppAdd
import Development.AbelianVarietyTheory.Definitions.Foundations.AbsCharNotUnitary

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.LFun Formalism.L2.Host
open GroundTheory.Automorphic.AutomorphicForm (constantTerm)

namespace UpperTheory.V.Cj.S

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

/- English proof (translation)
Take `⟨ι, _, n, π, μ, h1, h2, h3, h4, h5, h6⟩` from `h`. Use `⟨ι, inferInstance, n, π, μ, h1, h2, h3, h4, fun t => (h5 t).trans (hm t).symm, ?_⟩` and prove the remaining obligations. Use `filter_upwards [h6, hB] with w ⟨C, c1, c2⟩ e`. Conclude with `⟨C, c1, c2.trans e.symm⟩`.
-/
private theorem Supp.congr {a k : ℕ} {m m' : (E →+* ℂ) → Multiset ℂ} {B B' : Pl E → Multiset ℂˣ} (h : Supp E a k m B)
    (hm : ∀ t, m' t = m t) (hB : ∀ᶠ w in Filter.cofinite, B' w = B w) : Supp E a k m' B' := by
  obtain ⟨ι, _, n, π, μ, h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨ι, inferInstance, n, π, μ, h1, h2, h3, h4, fun t => (h5 t).trans (hm t).symm, ?_⟩
  filter_upwards [h6, hB] with w ⟨C, c1, c2⟩ e
  exact ⟨C, c1, c2.trans e.symm⟩

/- English proof (translation)
Take `⟨ι, _, n, π, μ, h1, h2⟩` from `h`. Conclude with `⟨ι, inferInstance, n, π, μ, hl.trans h1, h2⟩`.
-/
private theorem Supp.mono {a k l : ℕ} {m : (E →+* ℂ) → Multiset ℂ} {B : Pl E → Multiset ℂˣ} (h : Supp E a k m B)
    (hl : l ≤ k) : Supp E a l m B := by
  obtain ⟨ι, _, n, π, μ, h1, h2⟩ := h
  exact ⟨ι, inferInstance, n, π, μ, hl.trans h1, h2⟩

/- English proof (translation)
Establish `h1 : ¬ GroundTheory.Automorphic.AutomorphicForm.IsCuspidal φ.1` using `fun h2 => hc ((Cm.isCuspForm_iff φ).2 ⟨(Cm.isAutForm_iff φ).1 h.aut, h2⟩)`. Unfold `GroundTheory.Automorphic.AutomorphicForm.IsCuspidal at h1`. Use `push Not at h1`. Take `⟨r, h0, hr, hg⟩` from `h1`. Take `⟨s, rfl⟩ : ∃ s, a = r + s` from `⟨a - r, by omega⟩`.

Take `⟨φ₁, φ₂, m₁, m₂, B₁, B₂, e₁, e₂, hm, hB⟩` from `hS E r s φ m B h hg`. Establish `hν` using `fun x : ℝ => GlobalTheory.Mem.Chr.CharModel.absChar_isAbsPow (F := E) x`. Conclude with `(hA E r s 1 1 _ _ _ _ (hT E r 1 _ _ (ih r hr h0 _ _ _ e₁) _ _ (hν _)) (hT E s 1 _ _ (ih s (by omega) (by omega) _ _ _ e₂) _ _ (hν _))).congr hm (hB _ _ (hν _) (hν _))`.
-/
private theorem supp_two (hS : Step) (hT : SuppTwist) (hA : SuppAdd) {a : ℕ}
    (ih : ∀ b < a, 1 ≤ b → ∀ (φ : Sm E b) m B, Eig φ m B → Supp E b 1 m B)
    {φ : Sm E a} {m : (E →+* ℂ) → Multiset ℂ} {B : Pl E → Multiset ℂˣ} (h : Eig φ m B) (hc : ¬ IsCuspForm φ) :
    Supp E a 2 m B := by
  have h1 : ¬ GroundTheory.Automorphic.AutomorphicForm.IsCuspidal φ.1 := fun h2 =>
    hc ((Cm.isCuspForm_iff φ).2 ⟨(Cm.isAutForm_iff φ).1 h.aut, h2⟩)
  unfold GroundTheory.Automorphic.AutomorphicForm.IsCuspidal at h1
  push Not at h1
  obtain ⟨r, h0, hr, hg⟩ := h1
  obtain ⟨s, rfl⟩ : ∃ s, a = r + s := ⟨a - r, by omega⟩
  obtain ⟨φ₁, φ₂, m₁, m₂, B₁, B₂, e₁, e₂, hm, hB⟩ := hS E r s φ m B h hg
  have hν := fun x : ℝ => GlobalTheory.Mem.Chr.CharModel.absChar_isAbsPow (F := E) x
  exact (hA E r s 1 1 _ _ _ _ (hT E r 1 _ _ (ih r hr h0 _ _ _ e₁) _ _ (hν _))
    (hT E s 1 _ _ (ih s (by omega) (by omega) _ _ _ e₂) _ _ (hν _))).congr hm (hB _ _ (hν _) (hν _))

/- English proof (translation)
Proceed by induction on `a using Nat.strong_induction_on with`. Consider the case `_ a ih`. Introduce `ha φ m B h`. Distinguish the cases in `hc : IsCuspForm φ`. Conclude with `hC E a ha φ m B h hc`.

Conclude with `(supp_two hS hT hA ih h hc).mono one_le_two`.
-/
private theorem supp_one (hS : Step) (hT : SuppTwist) (hA : SuppAdd) (hC : SuppCusp) (a : ℕ) :
    1 ≤ a → ∀ (φ : Sm E a) m B, Eig φ m B → Supp E a 1 m B := by
  induction a using Nat.strong_induction_on with
  | _ a ih =>
    intro ha φ m B h
    by_cases hc : IsCuspForm φ
    · exact hC E a ha φ m B h hc
    · exact (supp_two hS hT hA ih h hc).mono one_le_two

/- English proof (translation)
Introduce `E _ _ _ a ha τ m j hj hfin haut hcap`. Distinguish the cases in `hc : ∀ v, IsCuspForm (j v)`. Use `left`. Choose the witnesses or unpack the hypotheses as in `⟨v, hv⟩ : ∃ v, j v ≠ 0 := by`. Assume the negation of the conclusion as `h`.

Use `push Not at h`. Conclude with `hj (LinearMap.ext h)`. Set `j' : τ.V →ₗ[ℂ] CI a m` to `j.codRestrict _ fun v => mem_CI.2 ⟨hc v, fun t => (hcap v t).2⟩`. Take `⟨π, h1, p, h2, h3⟩` from `hP E a ha m (fun t => (hcap v t).1) (j' v) fun e => hv (congrArg Subtype.val e)`. Conclude with `⟨π, ⟨p ∘ₗ j', fun e => h2 (LinearMap.congr_fun e v), fun g x => h3 g (j' x) (j' (τ.ρ g x)) (hfin g x)⟩, h1⟩`.

Use `right push Not at hc`. Take `⟨v, hv⟩` from `hc`. Establish `h0 : j v ≠ 0` using `fun e => hv (e ▸ Cm.mem_range_ofCusp.1 (Submodule.zero_mem _))`. Establish `hv0 : v ≠ 0` using `fun e => h0 (by rw [e, map_zero])`. Establish `h1` using `hτ E a τ v hv0`.

Set `B : Pl E → Multiset ℂˣ` to `fun w => if h : ∃ B, HasSatGL w (locOf τ.ρ w) B ∧ IsSatVecGL w (locOf τ.ρ w) v B then h.choose else 0`. Establish `h2 : ∀ᶠ w in Filter.cofinite, HasSatGL w (locOf τ.ρ w) (B w) ∧ IsSatVecGL w (locOf τ.ρ w) v (B w)` using `h1.mono fun w h => by simp only [B, dif_pos h]; exact h.choose_spec`. Establish `he : Eig (j v) m B` using `⟨h0, haut v, hcap v, h2.mono fun w h => h.2.map j (fun g y => hfin _ y) h0⟩`. Take `⟨ι, _, n, π, μ, c1, c2, c3, c4, c5, c6⟩` from `supp_two hS hT hA (fun b _ => supp_one hS hT hA hC b) he hv`. Use `⟨ι, inferInstance, n, π, μ, c1, c2, fun i => ?_, c3, c4, c5, ?_⟩` and prove the remaining obligations.

Take `⟨k, hk⟩` from `Fintype.exists_ne_of_one_lt_card c1 i`. Rewrite using `[← c3]`. Conclude with `Finset.single_lt_sum hk (Finset.mem_univ i) (Finset.mem_univ k) (c2 k) fun _ _ _ => Nat.zero_le _`. Use `filter_upwards [c6, h2] with w ⟨C, d1, d2⟩ h`. Conclude with `⟨C, d1, d2 ▸ h.1⟩`.
-/
theorem cuspSupport_of (hS : Step) (hT : SuppTwist) (hA : SuppAdd) (hC : SuppCusp) (hP : CuspProj) (hτ : TauSat) :
    CuspSupport := by
  intro E _ _ _ a ha τ m j hj hfin haut hcap
  by_cases hc : ∀ v, IsCuspForm (j v)
  · left
    obtain ⟨v, hv⟩ : ∃ v, j v ≠ 0 := by
      by_contra h
      push Not at h
      exact hj (LinearMap.ext h)
    let j' : τ.V →ₗ[ℂ] CI a m := j.codRestrict _ fun v => mem_CI.2 ⟨hc v, fun t => (hcap v t).2⟩
    obtain ⟨π, h1, p, h2, h3⟩ := hP E a ha m (fun t => (hcap v t).1) (j' v) fun e => hv (congrArg Subtype.val e)
    exact ⟨π, ⟨p ∘ₗ j', fun e => h2 (LinearMap.congr_fun e v), fun g x => h3 g (j' x) (j' (τ.ρ g x)) (hfin g x)⟩, h1⟩
  · right
    push Not at hc
    obtain ⟨v, hv⟩ := hc
    have h0 : j v ≠ 0 := fun e => hv (e ▸ Cm.mem_range_ofCusp.1 (Submodule.zero_mem _))
    have hv0 : v ≠ 0 := fun e => h0 (by rw [e, map_zero])
    have h1 := hτ E a τ v hv0
    classical
    let B : Pl E → Multiset ℂˣ := fun w =>
      if h : ∃ B, HasSatGL w (locOf τ.ρ w) B ∧ IsSatVecGL w (locOf τ.ρ w) v B then h.choose else 0
    have h2 : ∀ᶠ w in Filter.cofinite, HasSatGL w (locOf τ.ρ w) (B w) ∧ IsSatVecGL w (locOf τ.ρ w) v (B w) :=
      h1.mono fun w h => by simp only [B, dif_pos h]; exact h.choose_spec
    have he : Eig (j v) m B :=
      ⟨h0, haut v, hcap v, h2.mono fun w h => h.2.map j (fun g y => hfin _ y) h0⟩
    obtain ⟨ι, _, n, π, μ, c1, c2, c3, c4, c5, c6⟩ :=
      supp_two hS hT hA (fun b _ => supp_one hS hT hA hC b) he hv
    refine ⟨ι, inferInstance, n, π, μ, c1, c2, fun i => ?_, c3, c4, c5, ?_⟩
    · obtain ⟨k, hk⟩ := Fintype.exists_ne_of_one_lt_card c1 i
      rw [← c3]
      exact Finset.single_lt_sum hk (Finset.mem_univ i) (Finset.mem_univ k) (c2 k) fun _ _ _ => Nat.zero_le _
    · filter_upwards [c6, h2] with w ⟨C, d1, d2⟩ h
      exact ⟨C, d1, d2 ▸ h.1⟩

/- English proof (translation)
The claim follows from `cuspSupport_of (step (pairEig (twoVar tensEigB) (stabSp capAct levelSplit (hullBdd typesComm) (hullOps capAct)) (opComm capAct) satOfEig capOfEig) (sliceBdd singleBdd) (iwa (rtK capAct)) ctCap ctSat (capRel slice capBlock) (hkRel slice hkSum (hkLocal sumInner matBlock) gl2_local_ …`.
-/
theorem cuspSupport : CuspSupport :=
  cuspSupport_of
    (step (pairEig (twoVar tensEigB) (stabSp capAct levelSplit (hullBdd typesComm) (hullOps capAct)) (opComm capAct) satOfEig capOfEig) (sliceBdd singleBdd) (iwa (rtK capAct)) ctCap ctSat (capRel slice capBlock) (hkRel slice hkSum (hkLocal sumInner matBlock) gl2_local_to_adelic_embedding) capArith satArith)
    suppTwist suppAdd (suppCusp (cuspProj capAct (ciBasic capAct) (ciCompl (ciBasic capAct))))
    (cuspProj capAct (ciBasic capAct) (ciCompl (ciBasic capAct))) tauSat

end UpperTheory.V.Cj.S
