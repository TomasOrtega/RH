import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.TupGlob

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.AtPt Formalism.L2.SG.TermLoc
open Classical

namespace Formalism.L2.SG.Pf.TupGlob

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D)

def locL (p : PlF D) (A B : PairVal.MatR D) : MatP D p :=
  match (Zd.M p).split with
  | none => Matrix.diagonal (fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cf Zd p a)) * A.map (D.s.atP p).ιE *
      Matrix.diagonal (fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cfi Zd p a))
  | some g => glue g.e (Matrix.diagonal (cf Zd p) * A.map ((p1 g.e).comp (D.s.atP p).ιE) * Matrix.diagonal (cfi Zd p))
      (Matrix.diagonal (cf Zd p) * (Sg (D.s.atP p).Fp D.R.rS * (B.map ((p2 g.e).comp (D.s.atP p).ιE)).transpose *
        Sg (D.s.atP p).Fp D.R.rS) * Matrix.diagonal (cfi Zd p))

def locR (p : PlF D) (A B : PairVal.MatR D) : MatP D p :=
  match (Zd.M p).split with
  | none => Matrix.diagonal (fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cfi Zd p a)) * B.map (D.s.atP p).ιE *
      Matrix.diagonal (fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cf Zd p a))
  | some g => glue g.e (Matrix.diagonal (cfi Zd p) * B.map ((p1 g.e).comp (D.s.atP p).ιE) * Matrix.diagonal (cf Zd p))
      (Matrix.diagonal (cfi Zd p) * (Sg (D.s.atP p).Fp D.R.rS * (A.map ((p2 g.e).comp (D.s.atP p).ιE)).transpose *
        Sg (D.s.atP p).Fp D.R.rS) * Matrix.diagonal (cf Zd p))

/- English proof (translation)
Simplify using `only [Matrix.transpose_mul, hSt, Matrix.mul_assoc]`. Rewrite using `[← Matrix.mul_assoc S S, hS, Matrix.one_mul]`.
-/
theorem tr_lem {K : Type*} [CommRing K] {n : ℕ} (S L X B : Matrix (Fin n) (Fin n) K) (hS : S * S = 1)
    (hSt : S.transpose = S) :
    (L * (X * S) * B * S).transpose * S = (S * B.transpose * S) * (X.transpose * S) * (S * L.transpose * S) := by
  simp only [Matrix.transpose_mul, hSt, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc S S, hS, Matrix.one_mul]

/- English proof (translation)
Rewrite using `[Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, lo_corner_up hL hU]`.
-/
theorem corner_conj {K : Type*} [CommRing K] {r : ℕ} {L U Y : Matrix (Fin (r + 1)) (Fin (r + 1)) K} (hL : IsLo L)
    (hU : IsUp U) (c : K) : L * (Y - c • Ecorner r) * U = L * Y * U - c • Ecorner r := by
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, lo_corner_up hL hU]

/- English proof (translation)
Establish `hAg` using `(Zd.agree p).2.2.2.2.2`. Apply the tactic sequence `rcases hM : (Zd.M p).split with _ | g <;> rcases hR : (D.s.atP p).split with _ | sg <;>`. Simplify using `only [hM, hR] at hAg`. Use `set fr : Fin (D.R.rS + 1) → (D.s.atP p).Ep := fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cf Zd p a) set fri : Fin (D.R.rS + 1) → (D.s.atP p).Ep := fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cfi Zd p a)`. Establish `hfr : ∀ a, fri a * fr a = 1` using `fun a => by simp only [fr, fri, ← map_mul, cfi_cf, map_one]`.

Rewrite using `[zzp_sgn_ord Zd u u' p hM Z₂, zzp_sgn_ord Zd u u' p hM Z₁, h, Matrix.map_mul, Matrix.map_mul, regroup fr fri hfr]`. Simplify using `only [locL, locR, hM]`. Both sides reduce to the same expression. Take `⟨hge, hgq⟩` from `hAg`. Establish `hcc : ∀ a, cf Zd p a * cfi Zd p a = 1` using `cf_cfi Zd p`.

Establish `hcc' : ∀ a, cfi Zd p a * cf Zd p a = 1` using `cfi_cf Zd p`. Establish `hL1 : IsLo (Matrix.diagonal (cf Zd p) * A.map ((p1 sg.e).comp (D.s.atP p).ιE) * Matrix.diagonal (cfi Zd p))` using `isLo_conj (isLo_map _ hA) _ _ hcc`. Establish `hU1 : IsUp (Matrix.diagonal (cfi Zd p) * B.map ((p1 sg.e).comp (D.s.atP p).ιE) * Matrix.diagonal (cf Zd p))` using `isUp_conj (isUp_map _ hB) _ _ hcc'`. Establish `hL2a : IsLo (Sg (D.s.atP p).Fp D.R.rS * (B.map ((p2 sg.e).comp (D.s.atP p).ιE)).transpose * Sg (D.s.atP p).Fp D.R.rS)` using `(isLo_conj (isLo_transpose (isUp_map ((p2 sg.e).comp (D.s.atP p).ιE) hB)) _ _ (fun a => sgn_sq' D.R.rS a) : IsLo (Sg (D.s.atP p).Fp D.R.rS * (B.map ((p2 sg.e).comp (D.s.atP p).ιE)).transpose * Sg (D.s.atP p).Fp D.R.rS))`. Establish `hU2a : IsUp (Sg (D.s.atP p).Fp D.R.rS * (A.map ((p2 sg.e).comp (D.s.atP p).ιE)).transpose * Sg (D.s.atP p).Fp D.R.rS)` using `(isUp_conj (isUp_transpose (isLo_map ((p2 sg.e).comp (D.s.atP p).ιE) hA)) _ _ (fun a => sgn_sq' D.R.rS a) : IsUp (Sg (D.s.atP p).Fp D.R.rS * (A.map ((p2 sg.e).comp (D.s.atP p).ιE)).transpose * Sg (D.s.atP p).Fp D.R.rS))`.

Establish `hL2` using `isLo_conj hL2a (cf Zd p) (cfi Zd p) hcc`. Establish `hU2` using `isUp_conj hU2a (cfi Zd p) (cf Zd p) hcc'`. Establish `hZ2 : Z₂ = A * (Z₁ * Sg D.host.E D.R.rS) * B * Sg D.host.E D.R.rS`. Rewrite using `[← h, Matrix.mul_assoc, sg_sq, Matrix.mul_one]`. Simplify using `only [locL, locR, hM, hge]`.

Apply `mat_eq sg.e` to reduce the goal to its premises. Establish `l1` using `zz1' Zd p sg hR g hM hge hgq u u' Z₂`. Establish `r1` using `zz1' Zd p sg hR g hM hge hgq u u' Z₁`. Establish `key1 : (A * (Z₁ * Sg D.host.E D.R.rS) * B).map ((p1 sg.e).comp (D.s.atP p).ιE) = A.map ((p1 sg.e).comp (D.s.atP p).ιE) * (Z₁ * Sg D.host.E D.R.rS).map ((p1 sg.e).comp (D.s.atP p).ιE) * B.map ((p1 sg.e).comp (D.s.atP p).ιE)` using `by simp only [Matrix.map_mul]`. Rewrite `l1` using `[h, key1, fact1 (cf Zd p) (cfi Zd p) hcc']`.

Use `l1.trans ?_` and prove the remaining obligations. Use `conv_rhs => rw [Matrix.map_mul, Matrix.map_mul, glue_map_fst, glue_map_fst, r1, corner_conj hL1 hU1]`. Establish `e2 : (Z₂.map ((p2 sg.e).comp (D.s.atP p).ιE)).transpose * Sg (D.s.atP p).Fp D.R.rS = (Sg (D.s.atP p).Fp D.R.rS * (B.map ((p2 sg.e).comp (D.s.atP p).ιE)).transpose * Sg (D.s.atP p).Fp D.R.rS) * ((Z₁.map ((p2 sg.e).comp (D.s.atP p).ιE)).transpose * Sg (D.s.atP p).Fp D.R.rS) * (Sg ( …`. Rewrite using `[hZ2, Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, sg_map]`. Conclude with `tr_lem _ _ _ _ (sg_sq _) (Matrix.diagonal_transpose _)`.

Establish `l2` using `zz2' Zd p sg hR g hM hge hgq u u' Z₂`. Establish `r2` using `zz2' Zd p sg hR g hM hge hgq u u' Z₁`. Rewrite `l2` using `[e2, fact1 (cf Zd p) (cfi Zd p) hcc']`. Use `l2.trans ?_` and prove the remaining obligations. Use `conv_rhs => rw [Matrix.map_mul, Matrix.map_mul, glue_map_snd, glue_map_snd, r2, corner_conj hL2 hU2]`.
-/
theorem locMove (u u' : D.what₂.Word) (p : PlF D) {Z₁ Z₂ A B : PairVal.MatR D} (hA : IsLo A) (hB : IsUp B)
    (h : Z₂ * Sg D.host.E D.R.rS = A * (Z₁ * Sg D.host.E D.R.rS) * B) :
    CntLocal.ZZP (M := Zd.M) Zd.δ u u' p Z₂ * LsDatumB.sgnP p =
      locL Zd p A B * (CntLocal.ZZP (M := Zd.M) Zd.δ u u' p Z₁ * LsDatumB.sgnP p) * locR Zd p A B := by
  have hAg := (Zd.agree p).2.2.2.2.2
  rcases hM : (Zd.M p).split with _ | g <;> rcases hR : (D.s.atP p).split with _ | sg <;>
    simp only [hM, hR] at hAg
  · set fr : Fin (D.R.rS + 1) → (D.s.atP p).Ep := fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cf Zd p a)
    set fri : Fin (D.R.rS + 1) → (D.s.atP p).Ep := fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cfi Zd p a)
    have hfr : ∀ a, fri a * fr a = 1 := fun a => by simp only [fr, fri, ← map_mul, cfi_cf, map_one]
    rw [zzp_sgn_ord Zd u u' p hM Z₂, zzp_sgn_ord Zd u u' p hM Z₁, h, Matrix.map_mul, Matrix.map_mul,
      regroup fr fri hfr]
    simp only [locL, locR, hM]
    rfl
  · obtain ⟨hge, hgq⟩ := hAg
    have hcc : ∀ a, cf Zd p a * cfi Zd p a = 1 := cf_cfi Zd p
    have hcc' : ∀ a, cfi Zd p a * cf Zd p a = 1 := cfi_cf Zd p
    have hL1 : IsLo (Matrix.diagonal (cf Zd p) * A.map ((p1 sg.e).comp (D.s.atP p).ιE) * Matrix.diagonal (cfi Zd p)) :=
      isLo_conj (isLo_map _ hA) _ _ hcc
    have hU1 : IsUp (Matrix.diagonal (cfi Zd p) * B.map ((p1 sg.e).comp (D.s.atP p).ιE) * Matrix.diagonal (cf Zd p)) :=
      isUp_conj (isUp_map _ hB) _ _ hcc'
    have hL2a : IsLo (Sg (D.s.atP p).Fp D.R.rS * (B.map ((p2 sg.e).comp (D.s.atP p).ιE)).transpose *
        Sg (D.s.atP p).Fp D.R.rS) :=
      (isLo_conj (isLo_transpose (isUp_map ((p2 sg.e).comp (D.s.atP p).ιE) hB)) _ _ (fun a => sgn_sq' D.R.rS a) :
        IsLo (Sg (D.s.atP p).Fp D.R.rS * (B.map ((p2 sg.e).comp (D.s.atP p).ιE)).transpose * Sg (D.s.atP p).Fp D.R.rS))
    have hU2a : IsUp (Sg (D.s.atP p).Fp D.R.rS * (A.map ((p2 sg.e).comp (D.s.atP p).ιE)).transpose *
        Sg (D.s.atP p).Fp D.R.rS) :=
      (isUp_conj (isUp_transpose (isLo_map ((p2 sg.e).comp (D.s.atP p).ιE) hA)) _ _ (fun a => sgn_sq' D.R.rS a) :
        IsUp (Sg (D.s.atP p).Fp D.R.rS * (A.map ((p2 sg.e).comp (D.s.atP p).ιE)).transpose * Sg (D.s.atP p).Fp D.R.rS))
    have hL2 := isLo_conj hL2a (cf Zd p) (cfi Zd p) hcc
    have hU2 := isUp_conj hU2a (cfi Zd p) (cf Zd p) hcc'
    have hZ2 : Z₂ = A * (Z₁ * Sg D.host.E D.R.rS) * B * Sg D.host.E D.R.rS := by
      rw [← h, Matrix.mul_assoc, sg_sq, Matrix.mul_one]
    simp only [locL, locR, hM, hge]
    apply mat_eq sg.e
    · have l1 := zz1' Zd p sg hR g hM hge hgq u u' Z₂
      have r1 := zz1' Zd p sg hR g hM hge hgq u u' Z₁
      have key1 : (A * (Z₁ * Sg D.host.E D.R.rS) * B).map ((p1 sg.e).comp (D.s.atP p).ιE) =
          A.map ((p1 sg.e).comp (D.s.atP p).ιE) * (Z₁ * Sg D.host.E D.R.rS).map ((p1 sg.e).comp (D.s.atP p).ιE) *
            B.map ((p1 sg.e).comp (D.s.atP p).ιE) := by simp only [Matrix.map_mul]
      rw [h, key1, fact1 (cf Zd p) (cfi Zd p) hcc'] at l1
      refine l1.trans ?_
      conv_rhs => rw [Matrix.map_mul, Matrix.map_mul, glue_map_fst, glue_map_fst, r1, corner_conj hL1 hU1]
    · have e2 : (Z₂.map ((p2 sg.e).comp (D.s.atP p).ιE)).transpose * Sg (D.s.atP p).Fp D.R.rS =
          (Sg (D.s.atP p).Fp D.R.rS * (B.map ((p2 sg.e).comp (D.s.atP p).ιE)).transpose * Sg (D.s.atP p).Fp D.R.rS) *
            ((Z₁.map ((p2 sg.e).comp (D.s.atP p).ιE)).transpose * Sg (D.s.atP p).Fp D.R.rS) *
            (Sg (D.s.atP p).Fp D.R.rS * (A.map ((p2 sg.e).comp (D.s.atP p).ιE)).transpose * Sg (D.s.atP p).Fp D.R.rS) := by
        rw [hZ2, Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, sg_map]
        exact tr_lem _ _ _ _ (sg_sq _) (Matrix.diagonal_transpose _)
      have l2 := zz2' Zd p sg hR g hM hge hgq u u' Z₂
      have r2 := zz2' Zd p sg hR g hM hge hgq u u' Z₁
      rw [e2, fact1 (cf Zd p) (cfi Zd p) hcc'] at l2
      refine l2.trans ?_
      conv_rhs => rw [Matrix.map_mul, Matrix.map_mul, glue_map_snd, glue_map_snd, r2, corner_conj hL2 hU2]

end Formalism.L2.SG.Pf.TupGlob
