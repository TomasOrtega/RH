import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarFrameLA

noncomputable section

open scoped Classical
open Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.FsLA

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : Formalism.BasicNotions.HSpace E}

/- English proof (translation)
Introduce `i j hij`. Establish `hfe : ∀ a : Fin r, F.fvec (Fin.castSucc a) = F.e a` using `fun a => by simp [FlagG.fvec]`. Establish `hfz : F.fvec (Fin.last r) = F.z` using `by simp [FlagG.fvec]`. Simplify using `only [gram]`. Proceed by induction on `i using Fin.lastCases with`.

Consider the case `last`. Proceed by induction on `j using Fin.lastCases with`. Consider the case `last => simp at hij`. Consider the case `cast b`. Rewrite using `[hfz, hfe, ← LinearMap.IsSymm.eq_iff S.herm]`.

Conclude with `F.z_orth b`. Consider the case `cast a`. Proceed by induction on `j using Fin.lastCases with`. Consider the case `last => rw [hfz, hfe]`. Conclude with `F.z_orth a`.

Consider the case `cast b => rw [hfe, hfe]`. Conclude with `F.e_iso a b`.
-/
theorem gram_fvec_zero {r : ℕ} {T : E} (F : FlagG S r T) :
    ∀ i j, (i ≠ Fin.last r ∨ j ≠ Fin.last r) → gram S F.fvec F.fvec i j = 0 := by
  intro i j hij
  have hfe : ∀ a : Fin r, F.fvec (Fin.castSucc a) = F.e a := fun a => by simp [FlagG.fvec]
  have hfz : F.fvec (Fin.last r) = F.z := by simp [FlagG.fvec]
  simp only [gram]
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => simp at hij
    | cast b =>
      rw [hfz, hfe, ← LinearMap.IsSymm.eq_iff S.herm]
      exact F.z_orth b
  | cast a =>
    induction j using Fin.lastCases with
    | last => rw [hfz, hfe]; exact F.z_orth a
    | cast b => rw [hfe, hfe]; exact F.e_iso a b

/- English proof (translation)
Simplify using `only [gram, FlagG.fvec, Fin.snoc_last]`. Conclude with `F.z_norm`.
-/
theorem gram_fvec_last {r : ℕ} {T : E} (F : FlagG S r T) :
    gram S F.fvec F.fvec (Fin.last r) (Fin.last r) = -T := by
  simp only [gram, FlagG.fvec, Fin.snoc_last]
  exact F.z_norm

/- English proof (translation)
Establish `hg : ∀ a b, S.hT (comb S F.fvec A a) (comb S F.fvec A b) = star (A (Fin.last r) a) * (-T) * A (Fin.last r) b`. Introduce `a b`. Establish `e` using `congrFun (congrFun (show gram S (comb S F.fvec A) (comb S F.fvec A) = Aᴴ * (gram S F.fvec F.fvec * A) by`. Rewrite using `[gram_comb_right, gram_comb_left]) a) b`. Simplify using `only [gram] at e`.

Rewrite using `[e, Matrix.mul_apply, Finset.sum_eq_single (Fin.last r)]`. Rewrite using `[Matrix.mul_apply, Finset.sum_eq_single (Fin.last r), gram_fvec_last, Matrix.conjTranspose_apply, mul_assoc]`. Introduce `c _ hc`. Rewrite using `[gram_fvec_zero F _ _ (Or.inr hc), zero_mul]`. Introduce `h`.

Conclude with `absurd (Finset.mem_univ _) h`. Introduce `c _ hc`. Rewrite using `[Matrix.mul_apply, Finset.sum_eq_zero fun d _ => by rw [gram_fvec_zero F _ _ (Or.inl hc), zero_mul], mul_zero]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`.

Establish `hl : ∀ a, a ≠ Fin.last r → A (Fin.last r) a = 0` using `fun a ha => hA _ _ (Fin.lt_last_iff_ne_last.2 ha)`. Use `⟨fun a b hab => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hg]`. Break down `hab with h | h` into its components or cases. Rewrite using `[hl a h, star_zero, zero_mul, zero_mul]`.

Rewrite using `[hl b h, mul_zero]`. Rewrite using `[hg, hA1, star_one, one_mul, mul_one]`.
-/
theorem comb_frame {r : ℕ} {T : E} (F : FlagG S r T) (A : Matrix (Fin (r + 1)) (Fin (r + 1)) E)
    (hA : ∀ a b, b < a → A a b = 0) (hA1 : ∀ a, A a a = 1) :
    (∀ a b, (a ≠ Fin.last r ∨ b ≠ Fin.last r) → S.hT (comb S F.fvec A a) (comb S F.fvec A b) = 0) ∧
      S.hT (comb S F.fvec A (Fin.last r)) (comb S F.fvec A (Fin.last r)) = -T := by
  have hg : ∀ a b, S.hT (comb S F.fvec A a) (comb S F.fvec A b) =
      star (A (Fin.last r) a) * (-T) * A (Fin.last r) b := by
    intro a b
    have e := congrFun (congrFun (show gram S (comb S F.fvec A) (comb S F.fvec A) = Aᴴ * (gram S F.fvec F.fvec * A) by
      rw [gram_comb_right, gram_comb_left]) a) b
    simp only [gram] at e
    rw [e, Matrix.mul_apply, Finset.sum_eq_single (Fin.last r)]
    · rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.last r), gram_fvec_last, Matrix.conjTranspose_apply, mul_assoc]
      · intro c _ hc; rw [gram_fvec_zero F _ _ (Or.inr hc), zero_mul]
      · intro h; exact absurd (Finset.mem_univ _) h
    · intro c _ hc
      rw [Matrix.mul_apply, Finset.sum_eq_zero fun d _ => by rw [gram_fvec_zero F _ _ (Or.inl hc), zero_mul], mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hl : ∀ a, a ≠ Fin.last r → A (Fin.last r) a = 0 := fun a ha => hA _ _ (Fin.lt_last_iff_ne_last.2 ha)
  refine ⟨fun a b hab => ?_, ?_⟩
  · rw [hg]
    rcases hab with h | h
    · rw [hl a h, star_zero, zero_mul, zero_mul]
    · rw [hl b h, mul_zero]
  · rw [hg, hA1, star_one, one_mul, mul_one]

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.FsLA

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

/- English proof (translation)
Take `⟨hξ1, hξ2⟩` from `inv_unitri _ (admissibility_witness_unitriangular γ.lam (lf D F0) (repF γ)).1 (admissibility_witness_unitriangular γ.lam (lf D F0) (repF γ)).2`. Conclude with `FsLA.comb_frame (repF γ).fl (fun a b => (((admXi D γ.lam (lf D F0) (repF γ))⁻¹ a b : 𝓞 D.host.E) : D.host.E)) (fun a b h => by simp [hξ1 a b h]) (fun a => by simp [hξ2 a])`.
-/
theorem star_frame_orthogonal (γ : TermDef.Term D u u' F0 what₂) :
    (∀ a b, (a ≠ Fin.last D.R.rS ∨ b ≠ Fin.last D.R.rS) → (VS D).hT (starFrame γ a) (starFrame γ b) = 0) ∧
      (VS D).hT (starFrame γ (Fin.last D.R.rS)) (starFrame γ (Fin.last D.R.rS)) = -((Tu D u' : ℕ) : D.host.E) := by
  obtain ⟨hξ1, hξ2⟩ := inv_unitri _ (admissibility_witness_unitriangular γ.lam (lf D F0) (repF γ)).1 (admissibility_witness_unitriangular γ.lam (lf D F0) (repF γ)).2
  exact FsLA.comb_frame (repF γ).fl
    (fun a b => (((admXi D γ.lam (lf D F0) (repF γ))⁻¹ a b : 𝓞 D.host.E) : D.host.E))
    (fun a b h => by simp [hξ1 a b h]) (fun a => by simp [hξ2 a])

variable (u u' F0 what₂)

def StarMinors : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D), Ctx γ Z →
    Z.det ≠ 0 ∧ (starZh (frame (lf D F0)) (starFrame γ)).det ≠ 0 ∧
      leadMinorE (starZh (frame (lf D F0)) (starFrame γ)) D.R.rS * Z.det =
        leadMinorE Z D.R.rS * (starZh (frame (lf D F0)) (starFrame γ)).det

variable {u u' F0 what₂}

/- English proof (translation)
Introduce `γ Z hC`. Take `⟨hZ, hZ₁, hx⟩` from `hM γ Z hC`. Take `⟨h1, h2⟩` from `star_frame_orthogonal γ`. Take `⟨F₂, hZh, hom, -⟩` from `FsLA.frame_la F0 (starFrame γ) h1 h2 Z hZ hZ₁ hx`. Use `⟨⟨F₂, F₂.z⟩, hZh, ?_, ?_⟩` and prove the remaining obligations.

Establish `e : starZh (frame (lf D F0)) (frame (⟨F₂, F₂.z⟩ : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E))) = Z` using `hZh`. Rewrite using `[e, FsLA.leadMinorE_full, FsLA.leadMinorE_full]`. Conclude with `hx`. Establish `e : starZh (frame (lf D F0)) (frame (⟨F₂, F₂.z⟩ : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E))) = Z` using `hZh`. Rewrite using `[FsLA.leadMinorE_full, FsLA.leadMinorE_full, e]`.

Conclude with `hom`.
-/
theorem starFrame_of (hM : StarMinors u u' F0 what₂) : StarFrame u u' F0 what₂ := by
  intro γ Z hC
  obtain ⟨hZ, hZ₁, hx⟩ := hM γ Z hC
  obtain ⟨h1, h2⟩ := star_frame_orthogonal γ
  obtain ⟨F₂, hZh, hom, -⟩ := FsLA.frame_la F0 (starFrame γ) h1 h2 Z hZ hZ₁ hx
  refine ⟨⟨F₂, F₂.z⟩, hZh, ?_, ?_⟩
  · have e : starZh (frame (lf D F0)) (frame (⟨F₂, F₂.z⟩ : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E))) = Z := hZh
    rw [e, FsLA.leadMinorE_full, FsLA.leadMinorE_full]
    exact hx
  · have e : starZh (frame (lf D F0)) (frame (⟨F₂, F₂.z⟩ : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E))) = Z := hZh
    rw [FsLA.leadMinorE_full, FsLA.leadMinorE_full, e]
    exact hom

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
