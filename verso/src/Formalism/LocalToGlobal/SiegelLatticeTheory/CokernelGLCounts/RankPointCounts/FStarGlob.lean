import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarGramPair

noncomputable section

open scoped Classical
open Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

def starInU (γ : TermDef.Term D u u' F0 what₂) (F'₂ : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) : Prop :=
  ∀ b, frame F'₂ b ∈ Submodule.span D.host.E (Set.range (Sum.elim (frame (lf D F0)) (starFrame γ)))

def starOmL (f f' : Fin (D.R.rS + 1) → (VS D).V) : (VS D).V :=
  ∑ a, star ((starZh f f').adjugate (Fin.last D.R.rS) a) • f a

/- English proof (translation)
Take `⟨hξ1, hξ2⟩` from `inv_unitri _ (admissibility_witness_unitriangular γ.lam (lf D F0) (repF γ)).1 (admissibility_witness_unitriangular γ.lam (lf D F0) (repF γ)).2`. Establish `hZ : starZh (frame (lf D F0)) (starFrame γ) = 1 * ZhatL (lf D F0) (repF γ) * (Matrix.of fun a b => (((admXi D γ.lam (lf D F0) (repF γ))⁻¹ a b : 𝓞 D.host.E) : D.host.E))`. Rewrite using `[Matrix.one_mul]`. Conclude with `FsLA.gram_comb_left (S := VS D) (frame (repF γ)) _ (frame (lf D F0))`. Rewrite using `[hZ, Formalism.L2.SG.Pf.leadMinor_uni 1 _ _ (fun a c h => Matrix.one_apply_ne (ne_of_lt h)) (fun a => Matrix.one_apply_eq a) (fun d b h => by simp [Matrix.of_apply, hξ1 d b h]) (fun b => by simp [Matrix.of_apply, hξ2 b]) l]`.
-/
theorem star_frame_lead_minor (γ : TermDef.Term D u u' F0 what₂) (l : ℕ) :
    leadMinorE (starZh (frame (lf D F0)) (starFrame γ)) l = leadMinorE (ZhatL (lf D F0) (repF γ)) l := by
  obtain ⟨hξ1, hξ2⟩ := inv_unitri _ (admissibility_witness_unitriangular γ.lam (lf D F0) (repF γ)).1 (admissibility_witness_unitriangular γ.lam (lf D F0) (repF γ)).2
  have hZ : starZh (frame (lf D F0)) (starFrame γ) =
      1 * ZhatL (lf D F0) (repF γ) *
        (Matrix.of fun a b => (((admXi D γ.lam (lf D F0) (repF γ))⁻¹ a b : 𝓞 D.host.E) : D.host.E)) := by
    rw [Matrix.one_mul]
    exact FsLA.gram_comb_left (S := VS D) (frame (repF γ)) _ (frame (lf D F0))
  rw [hZ, Formalism.L2.SG.Pf.leadMinor_uni 1 _ _ (fun a c h => Matrix.one_apply_ne (ne_of_lt h))
    (fun a => Matrix.one_apply_eq a) (fun d b h => by simp [Matrix.of_apply, hξ1 d b h])
    (fun b => by simp [Matrix.of_apply, hξ2 b]) l]

/- English proof (translation)
Take `⟨-, hG⟩` from `hγ.1`. Take `⟨h2, h2e⟩` from `starRepF_rep γ`. Establish `hrel2` using `(Formalism.L2.SG.Pf.double_coset_equivalence γ.lam (lf D F0) (PD D γ.lam (lf D F0) u') (Quot.out γ.cls) ⟨repF γ, h2⟩).1 ((Quot.out_eq γ.cls).trans h2e.symm)`. Establish `hGv : Gval (lf D F0) (repF γ) ≠ 0`. Rewrite using `[Formalism.L2.SG.Pf.gval_rel (lf D F0) hrel2]`.

Conclude with `hG`. Rewrite using `[← FsLA.leadMinorE_full, star_frame_lead_minor, star_frame_lead_minor]`. Conclude with `hGv`.
-/
theorem starG_ne (γ : TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1)) (hγ : EligAt γ w) :
    (starZh (frame (lf D F0)) (starFrame γ)).det * star (starZh (frame (lf D F0)) (starFrame γ)).det -
      CntLocal.Tn u * ((Tu D u' : ℕ) : D.host.E) *
        (leadMinorE (starZh (frame (lf D F0)) (starFrame γ)) D.R.rS *
          star (leadMinorE (starZh (frame (lf D F0)) (starFrame γ)) D.R.rS)) ≠ 0 := by
  obtain ⟨-, hG⟩ := hγ.1
  obtain ⟨h2, h2e⟩ := starRepF_rep γ
  have hrel2 := (Formalism.L2.SG.Pf.double_coset_equivalence γ.lam (lf D F0) (PD D γ.lam (lf D F0) u') (Quot.out γ.cls)
    ⟨repF γ, h2⟩).1 ((Quot.out_eq γ.cls).trans h2e.symm)
  have hGv : Gval (lf D F0) (repF γ) ≠ 0 := by
    rw [Formalism.L2.SG.Pf.gval_rel (lf D F0) hrel2]; exact hG
  rw [← FsLA.leadMinorE_full, star_frame_lead_minor, star_frame_lead_minor]
  exact hGv

/- English proof (translation)
Take `⟨w, hγ, -⟩` from `id hC`. Take `⟨hZd, hZ₁d, hx⟩` from `starMinors_holds u u' F0 what₂ γ Z hC`. Use `set f := frame (lf D F0) with hf`. Use `set f₁ := starFrame γ with hf₁`. Use `set Z₁ := starZh f f₁ with hZ₁`.

Use `set F₂ := F'₂.fl with hF₂`. Establish `hfF : f = F0.fvec` using `rfl`. Establish `hf₂ : frame F'₂ = F₂.fvec` using `rfl`. Establish `hZe : ∀ a b, (VS D).hT (f a) (F₂.fvec b) = Z a b` using `fun a b => by rw [← hZ]; rfl`. Establish `hg2 : FsLA.gram (VS D) f F₂.fvec = Zᴴ`.

Use `Matrix.ext fun i j => ?_` and prove the remaining obligations. Simplify using `only [FsLA.gram, Matrix.conjTranspose_apply]`. Rewrite using `[← hZe, ← (LinearMap.isSymm_def.1 (VS D).herm) (f j) (F₂.fvec i), starRingEnd_apply]`. Establish `hZ1e : FsLA.gram (VS D) f₁ F0.fvec = Z₁` using `rfl`. Take `⟨hf1a, hf1b⟩` from `star_frame_orthogonal γ`.

Establish `h1f : ∀ a b, (a ≠ Fin.last D.R.rS ∨ b ≠ Fin.last D.R.rS) → (VS D).hT (f a) (f b) = 0` using `fun a b h => FsLA.gram_fvec_zero F0 a b h`. Establish `h2f : (VS D).hT (f (Fin.last D.R.rS)) (f (Fin.last D.R.rS)) = -CntLocal.Tn u` using `FsLA.gram_fvec_last F0`. Establish `hdZ1h : Z₁ᴴ.det ≠ 0` using `by rw [Matrix.det_conjTranspose]; exact star_ne_zero.2 hZ₁d`. Establish `hdg2 : (FsLA.gram (VS D) f F₂.fvec).det ≠ 0`. Rewrite using `[hg2, Matrix.det_conjTranspose]`.

Conclude with `star_ne_zero.2 hZd`. Establish `hx2 : leadMinorE (FsLA.gram (VS D) f F₂.fvec) D.R.rS * Z₁ᴴ.det = leadMinorE Z₁ᴴ D.R.rS * (FsLA.gram (VS D) f F₂.fvec).det`. Rewrite using `[hg2, FsLA.lm_conjTranspose, FsLA.lm_conjTranspose, Matrix.det_conjTranspose, Matrix.det_conjTranspose, ← star_mul', ← star_mul', mul_comm (leadMinorE Z D.R.rS), hx, mul_comm]`. Take `⟨F₃, hZ3, hom3, hsp3⟩` from `FsLA.frame_la F₂ f h1f h2f Z₁ᴴ hdZ1h hdg2 hx2`. Use `set h := F₃.fvec with hh`.

Use `set uu := Sum.elim f f₁ with huu`. Use `set uu' := Sum.elim h F₂.fvec with huu'`. Establish `hZ3e : ∀ a b, (VS D).hT (F₂.fvec a) (h b) = Z₁ᴴ a b` using `fun a b => congrFun (congrFun hZ3 a) b`. Establish `k1 : ∀ a b, (VS D).hT (h a) (h b) = (VS D).hT (f a) (f b)`. Introduce `a b`.

Distinguish the cases in `hab : a ≠ Fin.last D.R.rS ∨ b ≠ Fin.last D.R.rS`. Conclude with `(FsLA.gram_fvec_zero F₃ a b hab).trans (FsLA.gram_fvec_zero F0 a b hab).symm`. Use `push_neg at hab`. Rewrite using `[hab.1, hab.2]`. Conclude with `(FsLA.gram_fvec_last F₃).trans (FsLA.gram_fvec_last F0).symm`.

Establish `k2 : ∀ a b, (VS D).hT (h a) (F₂.fvec b) = (VS D).hT (f a) (f₁ b)`. Introduce `a b`. Rewrite using `[← (LinearMap.isSymm_def.1 (VS D).herm) (F₂.fvec b) (h a), hZ3e, starRingEnd_apply, Matrix.conjTranspose_apply, star_star]`. Both sides reduce to the same expression. Establish `k3 : ∀ a b, (VS D).hT (F₂.fvec a) (h b) = (VS D).hT (f₁ a) (f b)`.

Introduce `a b`. Rewrite using `[hZ3e, Matrix.conjTranspose_apply, ← starRingEnd_apply]`. Conclude with `(LinearMap.isSymm_def.1 (VS D).herm) (f b) (f₁ a)`. Establish `k4 : ∀ a b, (VS D).hT (F₂.fvec a) (F₂.fvec b) = (VS D).hT (f₁ a) (f₁ b)`. Introduce `a b`.

Distinguish the cases in `hab : a ≠ Fin.last D.R.rS ∨ b ≠ Fin.last D.R.rS`. Conclude with `(FsLA.gram_fvec_zero F₂ a b hab).trans (hf1a a b hab).symm`. Use `push_neg at hab`. Rewrite using `[hab.1, hab.2]`. Conclude with `(FsLA.gram_fvec_last F₂).trans hf1b.symm`.

Establish `hGr : FsLA.gram (VS D) uu' uu' = FsLA.gram (VS D) uu uu`. Use `Matrix.ext fun i j => ?_` and prove the remaining obligations. Apply the tactic sequence `rcases i with a | a <;> rcases j with b | b`. Conclude with `k1 a b`. Conclude with `k2 a b`.

Conclude with `k3 a b`. Conclude with `k4 a b`. Establish `hdet : (FsLA.gram (VS D) uu uu).det ≠ 0` using `FsLA.gram_pair_det F0 f₁ hf1a hf1b hZ₁d (starG_ne γ w hγ)`. Establish `hsp : ∀ i, uu' i ∈ Submodule.span D.host.E (Set.range uu)`. Establish `hsub : Set.range (Sum.elim F₂.fvec f) ⊆ Submodule.span D.host.E (Set.range uu)`.

Introduce and unpack `_ ⟨k, rfl⟩`. Break down `k with b | a` into its components or cases. Conclude with `hU b`. Conclude with `Submodule.subset_span ⟨Sum.inl a, rfl⟩`. Introduce `i`.

Break down `i with a | b` into its components or cases. Conclude with `Submodule.span_le.2 hsub (hsp3 a)`. Conclude with `hU b`. Take `⟨g, hiso, hgu, -, hform⟩` from `FsLA.isom_ext uu uu' hGr hdet hsp`. Use `⟨g, fun k => ∑ m, (FsLA.gram (VS D) uu uu)⁻¹ m k • (uu' m - uu m), hiso, fun b => hgu (Sum.inr b), hform, ?_⟩` and prove the remaining obligations.

Establish `homf : FsLA.om (VS D) F₂.fvec f = starOmL f (frame F'₂)`. Rewrite using `[FsLA.om, hg2, ← Matrix.adjugate_conjTranspose]`. Simplify using `only [starOmL, Matrix.conjTranspose_apply]`. Rewrite using `[← hZ]`. Both sides reduce to the same expression.

Establish `homh : FsLA.om (VS D) F₂.fvec h = g (starOmL f f₁)`. Simplify using `only [FsLA.om, starOmL, map_sum, map_smul]`. Establish `e : FsLA.gram (VS D) h F₂.fvec = Z₁ᴴ` using `hZ3`. Rewrite using `[e]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations.

Rewrite using `[← Matrix.adjugate_conjTranspose, Matrix.conjTranspose_apply]`. Use `congr 1`. Conclude with `(hgu (Sum.inl a)).symm`. Establish `e1 : Z₁ᴴ.det = star Z₁.det` using `Matrix.det_conjTranspose _`. Establish `e2 : (FsLA.gram (VS D) f F₂.fvec).det = star Z.det` using `by rw [hg2, Matrix.det_conjTranspose]`.

Rewrite `hom3` using `[e1, e2, homf, homh]`. Conclude with `hom3`.
-/
theorem starGlob (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D) (hC : Ctx γ Z)
    (F'₂ : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (hZ : ZhatL (lf D F0) F'₂ = Z)
    (hU : starInU γ F'₂) :
    ∃ (g : (VS D).V ≃ₗ[D.host.E] (VS D).V) (y : Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1) → (VS D).V),
      (∀ x x', (VS D).hT (g x) (g x') = (VS D).hT x x') ∧ (∀ b, g (starFrame γ b) = frame F'₂ b) ∧
      (∀ v, g v = v + ∑ k, (VS D).hT (Sum.elim (frame (lf D F0)) (starFrame γ) k) v • y k) ∧
      star (starZh (frame (lf D F0)) (starFrame γ)).det • starOmL (frame (lf D F0)) (frame F'₂) -
        star Z.det • g (starOmL (frame (lf D F0)) (starFrame γ)) ∈ Xsp F'₂ := by
  obtain ⟨w, hγ, -⟩ := id hC
  obtain ⟨hZd, hZ₁d, hx⟩ := starMinors_holds u u' F0 what₂ γ Z hC
  set f := frame (lf D F0) with hf
  set f₁ := starFrame γ with hf₁
  set Z₁ := starZh f f₁ with hZ₁
  set F₂ := F'₂.fl with hF₂
  have hfF : f = F0.fvec := rfl
  have hf₂ : frame F'₂ = F₂.fvec := rfl
  have hZe : ∀ a b, (VS D).hT (f a) (F₂.fvec b) = Z a b := fun a b => by rw [← hZ]; rfl
  have hg2 : FsLA.gram (VS D) f F₂.fvec = Zᴴ := by
    refine Matrix.ext fun i j => ?_
    simp only [FsLA.gram, Matrix.conjTranspose_apply]
    rw [← hZe, ← (LinearMap.isSymm_def.1 (VS D).herm) (f j) (F₂.fvec i), starRingEnd_apply]
  have hZ1e : FsLA.gram (VS D) f₁ F0.fvec = Z₁ := rfl
  obtain ⟨hf1a, hf1b⟩ := star_frame_orthogonal γ
  have h1f : ∀ a b, (a ≠ Fin.last D.R.rS ∨ b ≠ Fin.last D.R.rS) → (VS D).hT (f a) (f b) = 0 :=
    fun a b h => FsLA.gram_fvec_zero F0 a b h
  have h2f : (VS D).hT (f (Fin.last D.R.rS)) (f (Fin.last D.R.rS)) = -CntLocal.Tn u := FsLA.gram_fvec_last F0
  have hdZ1h : Z₁ᴴ.det ≠ 0 := by rw [Matrix.det_conjTranspose]; exact star_ne_zero.2 hZ₁d
  have hdg2 : (FsLA.gram (VS D) f F₂.fvec).det ≠ 0 := by
    rw [hg2, Matrix.det_conjTranspose]; exact star_ne_zero.2 hZd
  have hx2 : leadMinorE (FsLA.gram (VS D) f F₂.fvec) D.R.rS * Z₁ᴴ.det =
      leadMinorE Z₁ᴴ D.R.rS * (FsLA.gram (VS D) f F₂.fvec).det := by
    rw [hg2, FsLA.lm_conjTranspose, FsLA.lm_conjTranspose, Matrix.det_conjTranspose, Matrix.det_conjTranspose,
      ← star_mul', ← star_mul', mul_comm (leadMinorE Z D.R.rS), hx, mul_comm]
  obtain ⟨F₃, hZ3, hom3, hsp3⟩ := FsLA.frame_la F₂ f h1f h2f Z₁ᴴ hdZ1h hdg2 hx2
  set h := F₃.fvec with hh
  set uu := Sum.elim f f₁ with huu
  set uu' := Sum.elim h F₂.fvec with huu'
  have hZ3e : ∀ a b, (VS D).hT (F₂.fvec a) (h b) = Z₁ᴴ a b := fun a b => congrFun (congrFun hZ3 a) b
  have k1 : ∀ a b, (VS D).hT (h a) (h b) = (VS D).hT (f a) (f b) := by
    intro a b
    by_cases hab : a ≠ Fin.last D.R.rS ∨ b ≠ Fin.last D.R.rS
    · exact (FsLA.gram_fvec_zero F₃ a b hab).trans (FsLA.gram_fvec_zero F0 a b hab).symm
    · push_neg at hab
      rw [hab.1, hab.2]
      exact (FsLA.gram_fvec_last F₃).trans (FsLA.gram_fvec_last F0).symm
  have k2 : ∀ a b, (VS D).hT (h a) (F₂.fvec b) = (VS D).hT (f a) (f₁ b) := by
    intro a b
    rw [← (LinearMap.isSymm_def.1 (VS D).herm) (F₂.fvec b) (h a), hZ3e, starRingEnd_apply,
      Matrix.conjTranspose_apply, star_star]
    rfl
  have k3 : ∀ a b, (VS D).hT (F₂.fvec a) (h b) = (VS D).hT (f₁ a) (f b) := by
    intro a b
    rw [hZ3e, Matrix.conjTranspose_apply, ← starRingEnd_apply]
    exact (LinearMap.isSymm_def.1 (VS D).herm) (f b) (f₁ a)
  have k4 : ∀ a b, (VS D).hT (F₂.fvec a) (F₂.fvec b) = (VS D).hT (f₁ a) (f₁ b) := by
    intro a b
    by_cases hab : a ≠ Fin.last D.R.rS ∨ b ≠ Fin.last D.R.rS
    · exact (FsLA.gram_fvec_zero F₂ a b hab).trans (hf1a a b hab).symm
    · push_neg at hab
      rw [hab.1, hab.2]
      exact (FsLA.gram_fvec_last F₂).trans hf1b.symm
  have hGr : FsLA.gram (VS D) uu' uu' = FsLA.gram (VS D) uu uu := by
    refine Matrix.ext fun i j => ?_
    rcases i with a | a <;> rcases j with b | b
    · exact k1 a b
    · exact k2 a b
    · exact k3 a b
    · exact k4 a b
  have hdet : (FsLA.gram (VS D) uu uu).det ≠ 0 :=
    FsLA.gram_pair_det F0 f₁ hf1a hf1b hZ₁d (starG_ne γ w hγ)
  have hsp : ∀ i, uu' i ∈ Submodule.span D.host.E (Set.range uu) := by
    have hsub : Set.range (Sum.elim F₂.fvec f) ⊆ Submodule.span D.host.E (Set.range uu) := by
      rintro _ ⟨k, rfl⟩
      rcases k with b | a
      · exact hU b
      · exact Submodule.subset_span ⟨Sum.inl a, rfl⟩
    intro i
    rcases i with a | b
    · exact Submodule.span_le.2 hsub (hsp3 a)
    · exact hU b
  obtain ⟨g, hiso, hgu, -, hform⟩ := FsLA.isom_ext uu uu' hGr hdet hsp
  refine ⟨g, fun k => ∑ m, (FsLA.gram (VS D) uu uu)⁻¹ m k • (uu' m - uu m), hiso, fun b => hgu (Sum.inr b),
    hform, ?_⟩

  have homf : FsLA.om (VS D) F₂.fvec f = starOmL f (frame F'₂) := by
    rw [FsLA.om, hg2, ← Matrix.adjugate_conjTranspose]
    simp only [starOmL, Matrix.conjTranspose_apply]
    rw [← hZ]
    rfl
  have homh : FsLA.om (VS D) F₂.fvec h = g (starOmL f f₁) := by
    simp only [FsLA.om, starOmL, map_sum, map_smul]
    have e : FsLA.gram (VS D) h F₂.fvec = Z₁ᴴ := hZ3
    rw [e]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Matrix.adjugate_conjTranspose, Matrix.conjTranspose_apply]
    congr 1
    exact (hgu (Sum.inl a)).symm
  have e1 : Z₁ᴴ.det = star Z₁.det := Matrix.det_conjTranspose _
  have e2 : (FsLA.gram (VS D) f F₂.fvec).det = star Z.det := by rw [hg2, Matrix.det_conjTranspose]
  rw [e1, e2, homf, homh] at hom3
  exact hom3

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
