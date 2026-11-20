import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PlaneSupports.PlaneSupp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianPlaneStrongApprox

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published GlobalTheory.CompanionTheory.PlaneSA Topology
open scoped TensorProduct Quaternion

noncomputable section

namespace GlobalTheory.CompanionTheory.PlaneSA.CptAdelic

variable {F : Type} [Field F] [NumberField F]

def glue (S : Finset (Pl F)) (c : F) (a : ∀ s : S, Kp s.1) : AF F :=
  algebraMap F (AF F) c + ∑ s : S, inc s.1 (a s - algebraMap F (Kp s.1) c)

/- English proof (translation)
Establish `h : proj u (∑ s : S, inc s.1 (a s - algebraMap F (Kp s.1) c)) = a ⟨u, hu⟩ - algebraMap F (Kp u) c`. Rewrite using `[map_sum, Finset.sum_eq_single (⟨u, hu⟩ : S)]`. Conclude with `proj_inc_same u _`. Introduce `b _ hb`. Conclude with `proj_inc_ne (fun e => hb (Subtype.ext e.symm)) _`.

Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`. Rewrite using `[glue, map_add, h, AlgHom.commutes, add_sub_cancel]`.
-/
theorem proj_glue_mem (S : Finset (Pl F)) (c : F) (a : ∀ s : S, Kp s.1) {u : Pl F} (hu : u ∈ S) :
    proj u (glue S c a) = a ⟨u, hu⟩ := by
  have h : proj u (∑ s : S, inc s.1 (a s - algebraMap F (Kp s.1) c)) =
      a ⟨u, hu⟩ - algebraMap F (Kp u) c := by
    rw [map_sum, Finset.sum_eq_single (⟨u, hu⟩ : S)]
    · exact proj_inc_same u _
    · intro b _ hb
      exact proj_inc_ne (fun e => hb (Subtype.ext e.symm)) _
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [glue, map_add, h, AlgHom.commutes, add_sub_cancel]

/- English proof (translation)
Establish `h : proj u (∑ s : S, inc s.1 (a s - algebraMap F (Kp s.1) c)) = 0`. Rewrite using `[map_sum]`. Use `Finset.sum_eq_zero fun b _ => proj_inc_ne (fun e => hu ?_) _` and prove the remaining obligations. Rewrite using `[e]`. Conclude with `b.2`.

Rewrite using `[glue, map_add, h, AlgHom.commutes, add_zero]`.
-/
theorem proj_glue_notMem (S : Finset (Pl F)) (c : F) (a : ∀ s : S, Kp s.1) {u : Pl F}
    (hu : u ∉ S) : proj u (glue S c a) = algebraMap F (Kp u) c := by
  have h : proj u (∑ s : S, inc s.1 (a s - algebraMap F (Kp s.1) c)) = 0 := by
    rw [map_sum]
    refine Finset.sum_eq_zero fun b _ => proj_inc_ne (fun e => hu ?_) _
    rw [e]
    exact b.2
  rw [glue, map_add, h, AlgHom.commutes, add_zero]

/- English proof (translation)
The claim follows from `continuous_const.add (continuous_finset_sum _ fun s _ => (continuous_inc s.1).comp ((hf s).sub continuous_const))`.
-/
theorem continuous_glue {X : Type*} [TopologicalSpace X] (S : Finset (Pl F)) (c : F)
    {f : X → ∀ s : S, Kp s.1} (hf : ∀ s : S, Continuous fun x => f x s) :
    Continuous fun x => glue S c (f x) :=
  continuous_const.add (continuous_finset_sum _ fun s _ =>
    (continuous_inc s.1).comp ((hf s).sub continuous_const))

def psi (d β : F) (S : Finset (Pl F)) (x : ∀ s : S, Q d β (Kp s.1)) : Q d β (AF F) :=
  ⟨glue S 1 fun s => (x s).re, glue S 0 fun s => (x s).imI, glue S 0 fun s => (x s).imJ,
    glue S 0 fun s => (x s).imK⟩

/- English proof (translation)
Rewrite using `[continuous_q_iff]`. Use `⟨continuous_glue S 1 fun s => continuous_re.comp (continuous_apply s), continuous_glue S 0 fun s => continuous_imI.comp (continuous_apply s), continuous_glue S 0 fun s => continuous_imJ.comp (continuous_apply s), continuous_glue S 0 fun s => continuous_imK.comp (continuous_apply …` and prove the remaining obligations.
-/
theorem continuous_psi (d β : F) (S : Finset (Pl F)) : Continuous (psi d β S) := by
  rw [continuous_q_iff]
  refine ⟨continuous_glue S 1 fun s => continuous_re.comp (continuous_apply s),
    continuous_glue S 0 fun s => continuous_imI.comp (continuous_apply s),
    continuous_glue S 0 fun s => continuous_imJ.comp (continuous_apply s),
    continuous_glue S 0 fun s => continuous_imK.comp (continuous_apply s)⟩

/- English proof (translation)
Use `QuaternionAlgebra.ext ?_ ?_ ?_ ?_` and prove the remaining obligations. Conclude with `proj_glue_mem S 1 _ hu`. Conclude with `proj_glue_mem S 0 _ hu`. Conclude with `proj_glue_mem S 0 _ hu`. Conclude with `proj_glue_mem S 0 _ hu`.
-/
theorem qmap_psi_mem (d β : F) (S : Finset (Pl F)) (x : ∀ s : S, Q d β (Kp s.1)) {u : Pl F}
    (hu : u ∈ S) : qmap (proj u) (psi d β S x) = x ⟨u, hu⟩ := by
  refine QuaternionAlgebra.ext ?_ ?_ ?_ ?_
  · exact proj_glue_mem S 1 _ hu
  · exact proj_glue_mem S 0 _ hu
  · exact proj_glue_mem S 0 _ hu
  · exact proj_glue_mem S 0 _ hu

/- English proof (translation)
Use `QuaternionAlgebra.ext ?_ ?_ ?_ ?_` and prove the remaining obligations. Conclude with `(proj_glue_notMem S 1 _ hu).trans (map_one _)`. Conclude with `(proj_glue_notMem S 0 _ hu).trans (map_zero _)`. Conclude with `(proj_glue_notMem S 0 _ hu).trans (map_zero _)`. Conclude with `(proj_glue_notMem S 0 _ hu).trans (map_zero _)`.
-/
theorem qmap_psi_notMem (d β : F) (S : Finset (Pl F)) (x : ∀ s : S, Q d β (Kp s.1)) {u : Pl F}
    (hu : u ∉ S) : qmap (proj u) (psi d β S x) = 1 := by
  refine QuaternionAlgebra.ext ?_ ?_ ?_ ?_
  · exact (proj_glue_notMem S 1 _ hu).trans (map_one _)
  · exact (proj_glue_notMem S 0 _ hu).trans (map_zero _)
  · exact (proj_glue_notMem S 0 _ hu).trans (map_zero _)
  · exact (proj_glue_notMem S 0 _ hu).trans (map_zero _)

/- English proof (translation)
Use `QuaternionAlgebra.ext ?_ ?_ ?_ ?_` and prove the remaining obligations. Conclude with `adele_ext fun u => congrArg (fun y : Q d β (Kp u) => y.re) (H u)`. Conclude with `adele_ext fun u => congrArg (fun y : Q d β (Kp u) => y.imI) (H u)`. Conclude with `adele_ext fun u => congrArg (fun y : Q d β (Kp u) => y.imJ) (H u)`. Conclude with `adele_ext fun u => congrArg (fun y : Q d β (Kp u) => y.imK) (H u)`.
-/
theorem q_adele_ext {d β : F} {g h : Q d β (AF F)}
    (H : ∀ u : Pl F, qmap (proj u) g = qmap (proj u) h) : g = h := by
  refine QuaternionAlgebra.ext ?_ ?_ ?_ ?_
  · exact adele_ext fun u => congrArg (fun y : Q d β (Kp u) => y.re) (H u)
  · exact adele_ext fun u => congrArg (fun y : Q d β (Kp u) => y.imI) (H u)
  · exact adele_ext fun u => congrArg (fun y : Q d β (Kp u) => y.imJ) (H u)
  · exact adele_ext fun u => congrArg (fun y : Q d β (Kp u) => y.imK) (H u)

/- English proof (translation)
Use extensionality with `g`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hg, hout⟩`. Use `⟨fun s => qmap (proj s.1) g, fun s _ => ?_, q_adele_ext fun u => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `qn (qmap (proj s.1) g) = 1`.

Rewrite using `[qn_qmap, hg, map_one]`. Distinguish the cases in `hu : u ∈ S`. Conclude with `qmap_psi_mem d β S _ hu`. Rewrite using `[qmap_psi_notMem d β S _ hu, hout u (by simpa using hu)]`. Introduce and unpack `⟨x, hx, rfl⟩`.

Establish `hout : ∀ u, u ∉ (S : Set (Pl F)) → qmap (proj u) (psi d β S x) = 1` using `fun u hu => qmap_psi_notMem d β S x (by simpa using hu)`. Use `⟨adele_ext fun u => ?_, hout⟩` and prove the remaining obligations. Rewrite using `[← qn_qmap, map_one]`. Distinguish the cases in `hu : u ∈ S`. Rewrite using `[qmap_psi_mem d β S x hu]`.

Conclude with `hx ⟨u, hu⟩ (Set.mem_univ _)`. Rewrite using `[hout u (by simpa using hu), qn_one]`.
-/
theorem suppAt_eq_image (d β : F) (S : Finset (Pl F)) :
    SuppAt d β (S : Set (Pl F)) =
      psi d β S '' Set.pi Set.univ fun s : S => {x : Q d β (Kp s.1) | qn x = 1} := by
  ext g
  constructor
  · rintro ⟨hg, hout⟩
    refine ⟨fun s => qmap (proj s.1) g, fun s _ => ?_, q_adele_ext fun u => ?_⟩
    · change qn (qmap (proj s.1) g) = 1
      rw [qn_qmap, hg, map_one]
    · by_cases hu : u ∈ S
      · exact qmap_psi_mem d β S _ hu
      · rw [qmap_psi_notMem d β S _ hu, hout u (by simpa using hu)]
  · rintro ⟨x, hx, rfl⟩
    have hout : ∀ u, u ∉ (S : Set (Pl F)) → qmap (proj u) (psi d β S x) = 1 := fun u hu =>
      qmap_psi_notMem d β S x (by simpa using hu)
    refine ⟨adele_ext fun u => ?_, hout⟩
    rw [← qn_qmap, map_one]
    by_cases hu : u ∈ S
    · rw [qmap_psi_mem d β S x hu]
      exact hx ⟨u, hu⟩ (Set.mem_univ _)
    · rw [hout u (by simpa using hu), qn_one]

/- English proof (translation)
Rewrite using `[suppAt_eq_image]`. Conclude with `(isCompact_univ_pi fun s : S => h s.1 s.2).image (continuous_psi d β S)`.
-/
theorem isCompact_suppAt {F : Type} [Field F] [NumberField F] (d β : F) (S : Finset (Pl F))
    (h : ∀ s ∈ S, IsCompact {x : Q d β (Kp s) | qn x = 1}) :
    IsCompact (SuppAt d β (S : Set (Pl F))) := by
  rw [suppAt_eq_image]
  exact (isCompact_univ_pi fun s : S => h s.1 s.2).image (continuous_psi d β S)

end GlobalTheory.CompanionTheory.PlaneSA.CptAdelic
