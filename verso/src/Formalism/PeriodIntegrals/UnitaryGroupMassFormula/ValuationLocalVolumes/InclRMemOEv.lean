import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.HostStarConj

noncomputable section

namespace Formalism.L2.SG.Pf.NcVal.OmVSt.OmW

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol Formalism.L2.SG.TypedSets Formalism.L2.SG.Sub Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  MeasureTheory NumberField IsDedekindDomain Matrix
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def piv (r : ℕ) (a : Fin (r + 1 + r)) : Fin (r + 1 + r) :=
  ⟨if a.val < r then a.val + (r + 1) else if a.val = r then r else a.val - (r + 1), by
    have := a.2; split_ifs <;> omega⟩

/- English proof (translation)
Apply `Fin.ext` to reduce the goal to its premises. Simplify using `[piv]`. Use linear arithmetic over natural numbers and integers.
-/
theorem piv_e (r : ℕ) (i : Fin r) : piv r (Fin.castAdd r i.castSucc) = Fin.natAdd (r + 1) i := by
  apply Fin.ext; simp [piv]; omega

/- English proof (translation)
Apply `Fin.ext` to reduce the goal to its premises. Simplify using `[piv]`.
-/
theorem pivot_castAdd_last (r : ℕ) : piv r (Fin.castAdd r (Fin.last r)) = Fin.castAdd r (Fin.last r) := by
  apply Fin.ext; simp [piv]

/- English proof (translation)
Apply `Fin.ext` to reduce the goal to its premises. Simplify using `only [piv, Fin.val_natAdd, Fin.val_castAdd, Fin.val_castSucc]`. Rewrite using `[if_neg (by omega), if_neg (by omega)]`. Use linear arithmetic over natural numbers and integers.
-/
theorem piv_f (r : ℕ) (i : Fin r) : piv r (Fin.natAdd (r + 1) i) = Fin.castAdd r i.castSucc := by
  apply Fin.ext
  simp only [piv, Fin.val_natAdd, Fin.val_castAdd, Fin.val_castSucc]
  rw [if_neg (by omega), if_neg (by omega)]
  omega

/- English proof (translation)
Introduce `a`. Use `Fin.addCases (fun a => ?_) (fun i => by rw [piv_f, piv_e]) a` and prove the remaining obligations. Conclude with `Fin.lastCases (by rw [pivot_castAdd_last, pivot_castAdd_last]) (fun i => by rw [piv_e, piv_f]) a`.
-/
theorem piv_invol (r : ℕ) : Function.Involutive (piv r) := by
  intro a
  refine Fin.addCases (fun a => ?_) (fun i => by rw [piv_f, piv_e]) a
  exact Fin.lastCases (by rw [pivot_castAdd_last, pivot_castAdd_last]) (fun i => by rw [piv_e, piv_f]) a

variable {D : D7} (X : HidaSetting D) (u' : D.what₂.Word)

/- English proof (translation)
Establish `hs` using `(VS D).herm`. Apply the tactic sequence `refine Fin.addCases (fun a => ?_) (fun a => ?_) a <;> refine Fin.addCases (fun b => ?_) (fun b => ?_) b`. Apply the tactic sequence `refine Fin.lastCases ?_ (fun i => ?_) a <;> refine Fin.lastCases ?_ (fun j => ?_) b`. Rewrite using `[pivot_castAdd_last, if_pos rfl, if_pos (by simp)]`. Simplify using `only [hv, Fin.append_left, Fin.snoc_last]`.

Rewrite using `[X.zu_norm]`. Both sides reduce to the same expression. Apply the tactic sequence `rw [pivot_castAdd_last, if_neg (fun h => by have := congrArg Fin.val h; simp at this <;> omega)]`. Simplify using `only [hv, Fin.append_left, Fin.snoc_last, Fin.snoc_castSucc]`. Conclude with `(hs.eq_iff).1 (X.zu_orth u' j).1`.

Apply the tactic sequence `rw [piv_e, if_neg (fun h => by have := congrArg Fin.val h; simp at this <;> omega)]`. Simplify using `only [hv, Fin.append_left, Fin.snoc_last, Fin.snoc_castSucc]`. Conclude with `(X.zu_orth u' i).1`. Apply the tactic sequence `rw [piv_e, if_neg (fun h => by have := congrArg Fin.val h; simp at this <;> omega)]`. Simplify using `only [hv, Fin.append_left, Fin.snoc_castSucc]`.

Conclude with `X.ee i j`. Use `Fin.lastCases ?_ (fun i => ?_) a` and prove the remaining obligations. Apply the tactic sequence `rw [pivot_castAdd_last, if_neg (fun h => by have := congrArg Fin.val h; simp at this <;> omega)]`. Simplify using `only [hv, Fin.append_left, Fin.append_right, Fin.snoc_last]`. Conclude with `(hs.eq_iff).1 (X.zu_orth u' b).2`.

Rewrite using `[piv_e]`. Simplify using `only [hv, Fin.append_left, Fin.append_right, Fin.snoc_castSucc]`. Rewrite using `[X.ef]`. Distinguish the cases in `h : i = b`. Apply the tactic sequence `subst h; rw [if_pos rfl, if_pos rfl, if_neg (by simp <;> omega)]`.

Rewrite using `[if_neg h, if_neg (fun e => h ((Fin.natAdd_inj _).1 e).symm)]`. Use `Fin.lastCases ?_ (fun j => ?_) b` and prove the remaining obligations. Apply the tactic sequence `rw [piv_f, if_neg (fun h => by have := congrArg Fin.val h; simp at this <;> omega)]`. Simplify using `only [hv, Fin.append_left, Fin.append_right, Fin.snoc_last]`. Conclude with `(X.zu_orth u' a).2`.

Rewrite using `[piv_f]`. Simplify using `only [hv, Fin.append_left, Fin.append_right, Fin.snoc_castSucc]`. Rewrite using `[← (LinearMap.isSymm_def.1 hs) (X.eX j) (X.fY a), X.ef]`. Distinguish the cases in `h : j = a`. Apply the tactic sequence `subst h; rw [if_pos rfl, if_pos rfl, if_neg (by simp <;> omega), map_one]`.

Rewrite using `[if_neg h, if_neg (fun e => h (Fin.castSucc_inj.1 (Fin.castAdd_inj.1 e))), map_zero]`. Apply the tactic sequence `rw [piv_f, if_neg (fun h => by have := congrArg Fin.val h; simp at this <;> omega)]`. Simplify using `only [hv, Fin.append_right]`. Conclude with `X.ff a b`.
-/
theorem hT_hv (a b : Fin (D.R.rS + 1 + D.R.rS)) :
    (VS D).hT (hv X u' a) (hv X u' b) =
      if b = piv D.R.rS a then (if a.val = D.R.rS then -((Tw u' : ℕ) : D.host.E) else 1) else 0 := by
  have hs := (VS D).herm
  refine Fin.addCases (fun a => ?_) (fun a => ?_) a <;> refine Fin.addCases (fun b => ?_) (fun b => ?_) b
  · refine Fin.lastCases ?_ (fun i => ?_) a <;> refine Fin.lastCases ?_ (fun j => ?_) b
    · rw [pivot_castAdd_last, if_pos rfl, if_pos (by simp)]
      simp only [hv, Fin.append_left, Fin.snoc_last]
      rw [X.zu_norm]; rfl
    · rw [pivot_castAdd_last, if_neg (fun h => by have := congrArg Fin.val h; simp at this <;> omega)]
      simp only [hv, Fin.append_left, Fin.snoc_last, Fin.snoc_castSucc]
      exact (hs.eq_iff).1 (X.zu_orth u' j).1
    · rw [piv_e, if_neg (fun h => by have := congrArg Fin.val h; simp at this <;> omega)]
      simp only [hv, Fin.append_left, Fin.snoc_last, Fin.snoc_castSucc]
      exact (X.zu_orth u' i).1
    · rw [piv_e, if_neg (fun h => by have := congrArg Fin.val h; simp at this <;> omega)]
      simp only [hv, Fin.append_left, Fin.snoc_castSucc]
      exact X.ee i j
  · refine Fin.lastCases ?_ (fun i => ?_) a
    · rw [pivot_castAdd_last, if_neg (fun h => by have := congrArg Fin.val h; simp at this <;> omega)]
      simp only [hv, Fin.append_left, Fin.append_right, Fin.snoc_last]
      exact (hs.eq_iff).1 (X.zu_orth u' b).2
    · rw [piv_e]
      simp only [hv, Fin.append_left, Fin.append_right, Fin.snoc_castSucc]
      rw [X.ef]
      by_cases h : i = b
      · subst h; rw [if_pos rfl, if_pos rfl, if_neg (by simp <;> omega)]
      · rw [if_neg h, if_neg (fun e => h ((Fin.natAdd_inj _).1 e).symm)]
  · refine Fin.lastCases ?_ (fun j => ?_) b
    · rw [piv_f, if_neg (fun h => by have := congrArg Fin.val h; simp at this <;> omega)]
      simp only [hv, Fin.append_left, Fin.append_right, Fin.snoc_last]
      exact (X.zu_orth u' a).2
    · rw [piv_f]
      simp only [hv, Fin.append_left, Fin.append_right, Fin.snoc_castSucc]
      rw [← (LinearMap.isSymm_def.1 hs) (X.eX j) (X.fY a), X.ef]
      by_cases h : j = a
      · subst h; rw [if_pos rfl, if_pos rfl, if_neg (by simp <;> omega), map_one]
      · rw [if_neg h, if_neg (fun e => h (Fin.castSucc_inj.1 (Fin.castAdd_inj.1 e))), map_zero]
  · rw [piv_f, if_neg (fun h => by have := congrArg Fin.val h; simp at this <;> omega)]
    simp only [hv, Fin.append_right]
    exact X.ff a b

def cD (a : Fin (D.R.rS + 1 + D.R.rS)) : X.B.I.E := if a.val = D.R.rS then -((Tw u' : ℕ) : X.B.I.E) else 1

/- English proof (translation)
Use extensionality with `a b`. Rewrite using `[diagonal_mul]`. Use `show hE _ _ (tupH (frameOf X u') a) (tupH (frameOf X u') b) = _`. Rewrite using `[tupH_eq, tupH_eq, hE_crdOf, hT_hv]`. Simplify using `only [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq, Function.Involutive.coe_toPerm, cD]`.

Distinguish the cases in `h : b = piv D.R.rS a`. Establish `h' : piv D.R.rS a = b` using `h.symm`. Rewrite using `[if_pos h]`. Simplify using `only [h', if_true, mul_one]`. Apply the tactic sequence `split_ifs <;> simp`.

Establish `h' : ¬ piv D.R.rS a = b` using `fun e => h e.symm`. Simplify using `[h, h']`.
-/
theorem gram_eq : gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')) =
    diagonal (cD X u') * (Function.Involutive.toPerm _ (piv_invol D.R.rS)).permMatrix X.B.I.E := by
  ext a b
  rw [diagonal_mul]
  show hE _ _ (tupH (frameOf X u') a) (tupH (frameOf X u') b) = _
  rw [tupH_eq, tupH_eq, hE_crdOf, hT_hv]
  simp only [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def,
    Option.some.injEq, Function.Involutive.coe_toPerm, cD]
  by_cases h : b = piv D.R.rS a
  · have h' : piv D.R.rS a = b := h.symm
    rw [if_pos h]
    simp only [h', if_true, mul_one]
    split_ifs <;> simp
  · have h' : ¬ piv D.R.rS a = b := fun e => h e.symm
    simp [h, h']

/- English proof (translation)
Rewrite using `[Finset.prod_eq_single (⟨D.R.rS, by omega⟩ : Fin (D.R.rS + 1 + D.R.rS))]`. Simplify using `[cD]`. Introduce `b _ hb`. Establish `: b.val ≠ D.R.rS` using `fun e => hb (Fin.ext e)`. Simplify using `[cD, this]`.

Simplify using the standard rewrite rules.
-/
theorem prod_cD : ∏ a, cD X u' a = -((Tw u' : ℕ) : X.B.I.E) := by
  rw [Finset.prod_eq_single (⟨D.R.rS, by omega⟩ : Fin (D.R.rS + 1 + D.R.rS))]
  · simp [cD]
  · intro b _ hb
    have : b.val ≠ D.R.rS := fun e => hb (Fin.ext e)
    simp [cD, this]
  · simp

/- English proof (translation)
Use `⟨((Equiv.Perm.sign (Function.Involutive.toPerm _ (piv_invol D.R.rS)) : ℤˣ) : ℤ), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← Units.val_mul, Int.units_mul_self, Units.val_one]`. Rewrite using `[gram_eq, det_mul, det_diagonal, det_permutation, prod_cD]`. Use `push_cast`. Both sides reduce to the same expression.
-/
theorem det_gram : ∃ s : ℤ, s * s = 1 ∧
    (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))).det = (((-(Tw u' : ℤ)) * s : ℤ) : X.B.I.E) := by
  refine ⟨((Equiv.Perm.sign (Function.Involutive.toPerm _ (piv_invol D.R.rS)) : ℤˣ) : ℤ), ?_, ?_⟩
  · rw [← Units.val_mul, Int.units_mul_self, Units.val_one]
  · rw [gram_eq, det_mul, det_diagonal, det_permutation, prod_cD]
    push_cast
    rfl

/- English proof (translation)
Establish `h1 : ((t : ℕ) : Fv F v) = algebraMap (𝓞 F) (Fv F v) (t : 𝓞 F)` using `by simp`. Rewrite using `[h1]`. Use `(HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := F) v (t : 𝓞 F)).trans ?_` and prove the remaining obligations. Use `erw [HeightOneSpectrum.valuation_of_algebraMap]`. Conclude with `HeightOneSpectrum.intValuation_eq_one_iff.2 ht`.
-/
theorem val_natCast_eq_one {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (t : ℕ)
    (ht : ((t : 𝓞 F)) ∉ v.asIdeal) : Valued.v ((t : ℕ) : Fv F v) = 1 := by
  have h1 : ((t : ℕ) : Fv F v) = algebraMap (𝓞 F) (Fv F v) (t : 𝓞 F) := by simp
  rw [h1]
  refine (HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := F) v (t : 𝓞 F)).trans ?_
  erw [HeightOneSpectrum.valuation_of_algebraMap]
  exact HeightOneSpectrum.intValuation_eq_one_iff.2 ht

/- English proof (translation)
The claim follows from `Submodule.subset_span ⟨x, trivial, rfl⟩`.
-/
theorem inclR_mem_OEv (v : PlX X) (x : 𝓞 X.B.I.E) :
    inclR (Fv X.B.I.F v) (x : X.B.I.E) ∈ OEv (E := X.B.I.E) v :=
  Submodule.subset_span ⟨x, trivial, rfl⟩

/- English proof (translation)
Introduce `v hT`. Take `⟨s, hs, hd⟩` from `det_gram X u'`. Establish `hdet : (localGramMatrixFrame X u' v).det = inclR (Fv X.B.I.F v) ((((-(Tw u' : ℤ)) * s : ℤ) : 𝓞 X.B.I.E) : X.B.I.E)`. Rewrite using `[localGramMatrixFrame, ← RingHom.mapMatrix_apply, ← RingHom.map_det, hd]`. Use `push_cast`.

Both sides reduce to the same expression. Use `set t : Fv X.B.I.F v := ((Tw u' : ℕ) : Fv X.B.I.F v) with ht_def`. Establish `hv1 : Valued.v t = 1` using `val_natCast_eq_one v _ hT`. Establish `ht0 : t ≠ 0`. Introduce `h0`.

Rewrite `hv1` using `[h0, map_zero]`. Conclude with `zero_ne_one hv1`. Establish `hti : t⁻¹ ∈ v.adicCompletionIntegers X.B.I.F`. Rewrite using `[HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hv1, inv_one]`. Use `⟨(⟨t⁻¹, hti⟩ : v.adicCompletionIntegers X.B.I.F) • inclR (Fv X.B.I.F v) (((-s : ℤ) : 𝓞 X.B.I.E) : X.B.I.E), Submodule.smul_mem _ _ (inclR_mem_OEv X v _), ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[hdet]`. Conclude with `inclR_mem_OEv X v _`. Rewrite using `[hdet]`. Establish `e1 : (⟨t⁻¹, hti⟩ : v.adicCompletionIntegers X.B.I.F) • inclR (Fv X.B.I.F v) (((-s : ℤ) : 𝓞 X.B.I.E) : X.B.I.E) = algebraMap (Fv X.B.I.F v) (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) t⁻¹ * inclR (Fv X.B.I.F v) (((-s : ℤ) : 𝓞 X.B.I.E) : X.B.I.E)`. Rewrite using `[← Algebra.smul_def]`.

Both sides reduce to the same expression. Rewrite using `[e1, mul_left_comm, ← map_mul]`. Establish `e2 : ((((-(Tw u' : ℤ)) * s : ℤ) : 𝓞 X.B.I.E) : X.B.I.E) * (((-s : ℤ) : 𝓞 X.B.I.E) : X.B.I.E) = ((Tw u' : ℕ) : X.B.I.E)`. Establish `: (-(Tw u' : ℤ)) * s * (-s) = (Tw u' : ℤ)`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[← map_mul (algebraMap (𝓞 X.B.I.E) X.B.I.E)]`. Rewrite using `[← Int.cast_mul, this]`. Simplify using the standard rewrite rules. Rewrite using `[e2, map_natCast, ← map_natCast (algebraMap (Fv X.B.I.F v) (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E)), ← map_mul, inv_mul_cancel₀ ht0, map_one]`.
-/
theorem omVDet_holds : OmVDet X u' := by
  intro v hT
  obtain ⟨s, hs, hd⟩ := det_gram X u'
  have hdet : (localGramMatrixFrame X u' v).det = inclR (Fv X.B.I.F v) ((((-(Tw u' : ℤ)) * s : ℤ) : 𝓞 X.B.I.E) : X.B.I.E) := by
    rw [localGramMatrixFrame, ← RingHom.mapMatrix_apply, ← RingHom.map_det, hd]
    push_cast; rfl
  set t : Fv X.B.I.F v := ((Tw u' : ℕ) : Fv X.B.I.F v) with ht_def
  have hv1 : Valued.v t = 1 := val_natCast_eq_one v _ hT
  have ht0 : t ≠ 0 := by
    intro h0; rw [h0, map_zero] at hv1; exact zero_ne_one hv1
  have hti : t⁻¹ ∈ v.adicCompletionIntegers X.B.I.F := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hv1, inv_one]
  refine ⟨(⟨t⁻¹, hti⟩ : v.adicCompletionIntegers X.B.I.F) • inclR (Fv X.B.I.F v) (((-s : ℤ) : 𝓞 X.B.I.E) : X.B.I.E),
    Submodule.smul_mem _ _ (inclR_mem_OEv X v _), ?_, ?_⟩
  · rw [hdet]; exact inclR_mem_OEv X v _
  · rw [hdet]
    have e1 : (⟨t⁻¹, hti⟩ : v.adicCompletionIntegers X.B.I.F) • inclR (Fv X.B.I.F v) (((-s : ℤ) : 𝓞 X.B.I.E) : X.B.I.E) =
        algebraMap (Fv X.B.I.F v) (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) t⁻¹ *
          inclR (Fv X.B.I.F v) (((-s : ℤ) : 𝓞 X.B.I.E) : X.B.I.E) := by
      rw [← Algebra.smul_def]; rfl
    rw [e1, mul_left_comm, ← map_mul]
    have e2 : ((((-(Tw u' : ℤ)) * s : ℤ) : 𝓞 X.B.I.E) : X.B.I.E) * (((-s : ℤ) : 𝓞 X.B.I.E) : X.B.I.E) =
        ((Tw u' : ℕ) : X.B.I.E) := by
      have : (-(Tw u' : ℤ)) * s * (-s) = (Tw u' : ℤ) := by
        calc (-(Tw u' : ℤ)) * s * (-s) = (Tw u' : ℤ) * (s * s) := by ring
          _ = (Tw u' : ℤ) := by rw [hs, mul_one]
      rw [← map_mul (algebraMap (𝓞 X.B.I.E) X.B.I.E)]
      rw [← Int.cast_mul, this]; simp
    rw [e2, map_natCast, ← map_natCast (algebraMap (Fv X.B.I.F v) (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E)), ← map_mul,
      inv_mul_cancel₀ ht0, map_one]

end Formalism.L2.SG.Pf.NcVal.OmVSt.OmW
