import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.IdeleNormEmbeddingNegOneReal

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder
open UpperTheory.ConvolutionTheory.RankTwoDescent

namespace UpperTheory.ConvolutionTheory.RankTwoDescent.Nz

variable {E : Type} [Field E] [NumberField E]

def FinOne (h : GL (Fin 2) (A E)) : Prop := ∀ i j, (h.val i j).2 = ((1 : Matrix (Fin 2) (Fin 2) (A E)) i j).2

def InfOneG (m : GL (Fin 2) (A E)) : Prop := ∀ i j, (m.val i j).1 = ((1 : Matrix (Fin 2) (Fin 2) (A E)) i j).1

/- English proof (translation)
Set `f1 : A E →+* InfiniteAdeleRing E` to `RingHom.fst (InfiniteAdeleRing E) (FiniteAdeleRing (𝓞 E) E)`. Set `f2 : A E →+* FiniteAdeleRing (𝓞 E) E` to `RingHom.snd (InfiniteAdeleRing E) (FiniteAdeleRing (𝓞 E) E)`. Establish `hm : f1.mapMatrix m.val = 1`. Rewrite using `[← map_one f1.mapMatrix]`. Conclude with `Matrix.ext fun i j => hi i j`.

Establish `hh : f2.mapMatrix h.val = 1`. Rewrite using `[← map_one f2.mapMatrix]`. Conclude with `Matrix.ext fun i j => hf i j`. Establish `e1 : f1.mapMatrix (m * h).val = f1.mapMatrix (h * m).val`. Rewrite using `[Units.val_mul, Units.val_mul, map_mul, map_mul, hm, one_mul, mul_one]`.

Establish `e2 : f2.mapMatrix (m * h).val = f2.mapMatrix (h * m).val`. Rewrite using `[Units.val_mul, Units.val_mul, map_mul, map_mul, hh, one_mul, mul_one]`. Conclude with `Units.ext (Matrix.ext fun i j => Prod.ext (congrFun (congrFun e1 i) j) (congrFun (congrFun e2 i) j))`.
-/
theorem comm_of {h m : GL (Fin 2) (A E)} (hf : FinOne h) (hi : InfOneG m) : m * h = h * m := by
  let f1 : A E →+* InfiniteAdeleRing E := RingHom.fst (InfiniteAdeleRing E) (FiniteAdeleRing (𝓞 E) E)
  let f2 : A E →+* FiniteAdeleRing (𝓞 E) E := RingHom.snd (InfiniteAdeleRing E) (FiniteAdeleRing (𝓞 E) E)
  have hm : f1.mapMatrix m.val = 1 := by
    rw [← map_one f1.mapMatrix]
    exact Matrix.ext fun i j => hi i j
  have hh : f2.mapMatrix h.val = 1 := by
    rw [← map_one f2.mapMatrix]
    exact Matrix.ext fun i j => hf i j
  have e1 : f1.mapMatrix (m * h).val = f1.mapMatrix (h * m).val := by
    rw [Units.val_mul, Units.val_mul, map_mul, map_mul, hm, one_mul, mul_one]
  have e2 : f2.mapMatrix (m * h).val = f2.mapMatrix (h * m).val := by
    rw [Units.val_mul, Units.val_mul, map_mul, map_mul, hh, one_mul, mul_one]
  exact Units.ext (Matrix.ext fun i j => Prod.ext (congrFun (congrFun e1 i) j) (congrFun (congrFun e2 i) j))

/- English proof (translation)
Express the relevant statement in the definitionally equal form `(AdeleBaseChange.adeleMap ℚ E 0).2 + (AdeleBaseChange.adeleMap ℚ E (bI u)).2 * (rt D.θ : A E).2 = 0`. Establish `h : (AdeleBaseChange.adeleMap ℚ E (bI u)).2 = 0`. Express the relevant statement in the definitionally equal form `AdeleBaseChange.finiteAdeleMap ℚ E (bI u).2 = 0`. Rewrite using `[bI_snd, map_zero]`. Rewrite using `[h, map_zero, zero_mul]`.

Conclude with `add_zero _`.
-/
theorem hU_fin (D : Dat ℚ E) (u : ℝ) : (D.mkE 0 (bI u)).2 = 0 := by
  change (AdeleBaseChange.adeleMap ℚ E 0).2 + (AdeleBaseChange.adeleMap ℚ E (bI u)).2 * (rt D.θ : A E).2 = 0
  have h : (AdeleBaseChange.adeleMap ℚ E (bI u)).2 = 0 := by
    change AdeleBaseChange.finiteAdeleMap ℚ E (bI u).2 = 0
    rw [bI_snd, map_zero]
  rw [h, map_zero, zero_mul]
  exact add_zero _

/- English proof (translation)
Introduce `i j`. Establish `h` using `hU_fin D u`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [hU, nE, h]`.
-/
theorem finOne_hU (D : Dat ℚ E) (u : ℝ) : FinOne (hU D u) := by
  intro i j
  have h := hU_fin D u
  fin_cases i <;> fin_cases j <;> simp [hU, nE, h]

/- English proof (translation)
Introduce `i j`. Establish `e : ((em E k).val i j) = AdeleBaseChange.adeleMap ℚ E (k.val i j)` using `rfl`. Establish `e2 : (AdeleBaseChange.adeleMap ℚ E (k.val i j)).1 = (AdeleBaseChange.adeleMap ℚ E ((1 : Matrix (Fin 2) (Fin 2) (A ℚ)) i j)).1`. Rewrite using `[AdeleBaseChange.adeleMap_apply, AdeleBaseChange.adeleMap_apply, h]`. Rewrite using `[e, e2]`.

Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [Matrix.one_apply]`.
-/
theorem infOne_em {k : GL (Fin 2) (A ℚ)} (h : ∀ i j, (k.val i j).1 = ((1 : Matrix (Fin 2) (Fin 2) (A ℚ)) i j).1) :
    InfOneG (em E k) := by
  intro i j
  have e : ((em E k).val i j) = AdeleBaseChange.adeleMap ℚ E (k.val i j) := rfl
  have e2 : (AdeleBaseChange.adeleMap ℚ E (k.val i j)).1 = (AdeleBaseChange.adeleMap ℚ E ((1 : Matrix (Fin 2) (Fin 2) (A ℚ)) i j)).1 := by
    rw [AdeleBaseChange.adeleMap_apply, AdeleBaseChange.adeleMap_apply, h]
  rw [e, e2]
  fin_cases i <;> fin_cases j <;> simp [Matrix.one_apply]

variable [IsTotallyComplex E]

/- English proof (translation)
Use `set z := D.mkE 0 (bI u) with hz`. Establish `hz2 : z.2 = 0` using `hU_fin D u`. Establish `hs : sInf E (GlobalTheory.CuspRep.pInf E z) = z` using `Prod.ext ((infEq E).apply_symm_apply _) hz2.symm`. Apply the tactic sequence `refine ⟨⟨!![1, GlobalTheory.CuspRep.pInf E z; 0, 1], !![1, -GlobalTheory.CuspRep.pInf E z; 0, 1], by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two], by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩, Units.e …`. Use extensionality with `i j`.

Express the relevant statement in the definitionally equal form `(1 : Matrix (Fin 2) (Fin 2) (A E)) i j - sInf E ((1 : Matrix (Fin 2) (Fin 2) (Cinf E)) i j) + sInf E (!![1, GlobalTheory.CuspRep.pInf E z; 0, 1] i j) = _`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [hU, nE, ← hz, hs]`.
-/
theorem exists_X (D : Dat ℚ E) (u : ℝ) : ∃ X, infGL E 2 X = hU D u := by
  set z := D.mkE 0 (bI u) with hz
  have hz2 : z.2 = 0 := hU_fin D u
  have hs : sInf E (GlobalTheory.CuspRep.pInf E z) = z := Prod.ext ((infEq E).apply_symm_apply _) hz2.symm
  refine ⟨⟨!![1, GlobalTheory.CuspRep.pInf E z; 0, 1], !![1, -GlobalTheory.CuspRep.pInf E z; 0, 1],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩, Units.ext ?_⟩
  ext i j
  change (1 : Matrix (Fin 2) (Fin 2) (A E)) i j - sInf E ((1 : Matrix (Fin 2) (Fin 2) (Cinf E)) i j) + sInf E (!![1, GlobalTheory.CuspRep.pInf E z; 0, 1] i j) = _
  fin_cases i <;> fin_cases j <;> simp [hU, nE, ← hz, hs]

/- English proof (translation)
Unfold `Tr at h ⊢`. Proceed by induction on `h using Submodule.span_induction with`. Consider the case `mem f hf`. Take `⟨f', hf', y, rfl⟩` from `hf`. Conclude with `Submodule.subset_span ⟨f', hf', x * y, by funext g; simp [mul_assoc]⟩`.

Consider the case `zero => exact Submodule.zero_mem _`. Consider the case `add a b _ _ ha hb => exact Submodule.add_mem _ ha hb`. Consider the case `smul c a _ ha => exact Submodule.smul_mem _ c ha`.
-/
theorem Tr_translate {P : CuspSub E 2} {φ : GL (Fin 2) (A E) → ℂ} (h : φ ∈ Tr P) (x : GL (Fin 2) (A E)) :
    (fun g => φ (g * x)) ∈ Tr P := by
  unfold Tr at h ⊢
  induction h using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨f', hf', y, rfl⟩ := hf
    exact Submodule.subset_span ⟨f', hf', x * y, by funext g; simp [mul_assoc]⟩
  | zero => exact Submodule.zero_mem _
  | add a b _ _ ha hb => exact Submodule.add_mem _ ha hb
  | smul c a _ ha => exact Submodule.smul_mem _ c ha

/- English proof (translation)
Take `⟨X, hX⟩` from `exists_X D u`. Establish `hc : ∀ k, finGL E 2 k * hU D u = hU D u * finGL E 2 k`. Introduce `k`. Rewrite using `[← hX, infGL_comm]`. Use `⟨hG.pos, hG.dvd, hG.same, Tr_translate hG.mem _, hG.pl, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Introduce `w hw`. Take `⟨h1, B, hB, hE⟩` from `hG.fix w hw`. Use `⟨?_, B, hB, ?_⟩` and prove the remaining obligations. Introduce `g k hk`. Establish `e : H.lc w k = finGL E 2 (locGL E 2 w k)` using `rfl`.

Express the relevant statement in the definitionally equal form `φ (g * H.lc w k * hU D u) = φ (g * hU D u)`. Rewrite using `[e, mul_assoc, hc, ← mul_assoc, ← e]`. Conclude with `h1 _ k hk`. Introduce `g`. Establish `e : (fun y => φ (g * finGL E 2 (locGL E 2 w y) * hU D u)) = fun y => φ (g * hU D u * finGL E 2 (locGL E 2 w y))`.

Use function extensionality and compare the values at `y`. Rewrite using `[mul_assoc, hc, ← mul_assoc]`. Express the relevant statement in the definitionally equal form `UpperTheory.V.Af.Smo.Eig w B fun y => φ (g * finGL E 2 (locGL E 2 w y) * hU D u)`. Rewrite using `[e]`. Conclude with `hE (g * hU D u)`.

Introduce `k hk g`. Express the relevant statement in the definitionally equal form `φ (g * em E k * hU D u) = φ (g * hU D u)`. Rewrite using `[mul_assoc, comm_of (finOne_hU D u) (infOne_em hk.1), ← mul_assoc]`. Conclude with `hG.lev k hk _`. Introduce `y x hne v hv`.

Rewrite `hne` using `[Wo_right, ← hX, mul_assoc, ← map_mul]`. Conclude with `hG.supp y _ hne v hv`. Introduce `t ht hd y x`. Rewrite using `[Wo_right, Wo_right, ← hX, mul_assoc, mul_assoc, ← map_mul]`. Conclude with `hG.tor t ht hd y _`.
-/
theorem Gd_translate {D : Dat ℚ E} {P : CuspSub E 2} {L N : ℕ} {φ : GL (Fin 2) (A E) → ℂ} (hG : Gd D P L N φ) (u : ℝ) :
    Gd D P L N (fun g => φ (g * hU D u)) := by
  obtain ⟨X, hX⟩ := exists_X D u
  have hc : ∀ k, finGL E 2 k * hU D u = hU D u * finGL E 2 k := by
    intro k
    rw [← hX, infGL_comm]
  refine ⟨hG.pos, hG.dvd, hG.same, Tr_translate hG.mem _, hG.pl, ?_, ?_, ?_, ?_⟩
  · intro w hw
    obtain ⟨h1, B, hB, hE⟩ := hG.fix w hw
    refine ⟨?_, B, hB, ?_⟩
    · intro g k hk
      have e : H.lc w k = finGL E 2 (locGL E 2 w k) := rfl
      change φ (g * H.lc w k * hU D u) = φ (g * hU D u)
      rw [e, mul_assoc, hc, ← mul_assoc, ← e]
      exact h1 _ k hk
    · intro g
      have e : (fun y => φ (g * finGL E 2 (locGL E 2 w y) * hU D u)) = fun y => φ (g * hU D u * finGL E 2 (locGL E 2 w y)) := by
        funext y
        rw [mul_assoc, hc, ← mul_assoc]
      change UpperTheory.V.Af.Smo.Eig w B fun y => φ (g * finGL E 2 (locGL E 2 w y) * hU D u)
      rw [e]
      exact hE (g * hU D u)
  · intro k hk g
    change φ (g * em E k * hU D u) = φ (g * hU D u)
    rw [mul_assoc, comm_of (finOne_hU D u) (infOne_em hk.1), ← mul_assoc]
    exact hG.lev k hk _
  · intro y x hne v hv
    rw [Wo_right, ← hX, mul_assoc, ← map_mul] at hne
    exact hG.supp y _ hne v hv
  · intro t ht hd y x
    rw [Wo_right, Wo_right, ← hX, mul_assoc, mul_assoc, ← map_mul]
    exact hG.tor t ht hd y _

end UpperTheory.ConvolutionTheory.RankTwoDescent.Nz
