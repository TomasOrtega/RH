import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TermAttractorConstant.GpMfixMapLoc

noncomputable section

open scoped Classical

set_option linter.style.haveILetI false

namespace PI.TermAttrConst.UnitaryGroupMassFormula

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef PI.DCRelEquiv PI.DCRelEquiv.UnitaryGroupMassFormula
  IsDedekindDomain

section GP4

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T T' : E}
  {Λ : Submodule (𝓞 E) S.V} {g : ℕ} {F : LFlag S r T} {x y : LFlag S r T'} {n m : S.V ≃ₗ[E] S.V}
  {ξ ξ' : Matrix (Fin (r + 1)) (Fin (r + 1)) (𝓞 E)}

/- English proof (translation)
Use `haveI := P.isPrime`. Use `set N := Submodule.span (𝓞 E) (Set.range fun a => n (gpGen g F x ξ a)) with hNdef`. Distinguish the cases in `hg : (g : E) = 0`. Unfold `gpGen`. Rewrite using `[hg, inv_zero, zero_smul]`.

Conclude with `zero_mem _`. Establish `hNΛ : N ≤ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal Λ`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨a, rfl⟩`. Conclude with `gp_locΛ_map _ hn.1 (gp_gen_mem P g hξ hP a)`.

Establish `hdec : ∀ a, frame x a = frameAct (frame F) ξ a + (g : E) • gpGen g F x ξ a`. Introduce `a`. Unfold `gpGen`. Rewrite using `[smul_smul, mul_inv_cancel₀ hg, one_smul]`. Normalize the expressions using the abelian group laws.

Establish `hK : ∀ a, n (frame x a) ∈ gpK P.asIdeal (gpMfix Λ F) N (g : E)`. Introduce `a`. Use `(gp_mem_K _).2 ⟨n (frameAct (frame F) ξ a), gp_Mfix_map_loc _ hFl hn (gp_frameAct_mem P g hFl hFc hP ξ a), n (gpGen g F x ξ a), gp_le_locP _ _ (Submodule.subset_span ⟨a, rfl⟩), ?_⟩` and prove the remaining obligations. Rewrite using `[hdec a, map_add, map_smul]`. Establish `hH : frame y b - n (frame x b) ∈ gpK P.asIdeal (gpMfix Λ F) N (g : E)`.

Establish `hd : m (frame x b) - frame x b ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (XLam Λ x)` using `gp_loc_X _ (sub_mem (gp_locΛ_map _ hm.1 (gp_frame_loc P g hxl hxc hP b)) (gp_frame_loc P g hxl hxc hP b)) (gp_nlam_sub_X hm b)`. Establish `hle` using `gp_XLam_le P g hxc hP ((gpK P.asIdeal (gpMfix Λ F) N (g : E)).comap (fO n)) ?_ ?_`. Establish `h1` using `hle hd`. Rewrite `h1` using `[Submodule.mem_comap, fO_apply, map_sub]`. Rewrite using `[hfr b]`.

Conclude with `h1`. Introduce `s hs k hk`. Rewrite `hk`, the goal using `[Submodule.mem_comap, fO_apply]`. Rewrite `hk` using `[gp_map_osmul]`. Conclude with `gp_K_loc _ hs hk`.

Introduce `a`. Rewrite using `[Submodule.mem_comap, fO_apply, ← frame_castSucc x a]`. Conclude with `hK _`. Conclude with `gp_core P.asIdeal (M := gpMfix Λ F) (Λ := Λ) (N := N) (U := gpU F) (c := (g : E)) (gp_sat _ F hFl hFc.2) (gp_Mfix_le_U F hFl) hNΛ (t := frame y b) (s := frameAct (frame F) ξ' b) (t' := n (frame x b)) (s' := n (frameAct (frame F) ξ b)) (v := gpGen g F y ξ' b) (w := n (gpGen g F x …`.
-/
theorem generator_mem_local_lattice_forward (P : HeightOneSpectrum (𝓞 E)) (hFl : IsLift Λ F) (hFc : IsFixedConv Λ g F)
    (hxl : IsLift Λ x) (hxc : IsFixedConv Λ g x) (hn : n ∈ NLam Λ F) (hm : m ∈ NLam Λ x)
    (hfr : ∀ a, frame y a = n (m (frame x a))) (hξ : AdmWit Λ g F x ξ) (hξ' : AdmWit Λ g F y ξ')
    (hP : (g : 𝓞 E) ∈ P.asIdeal) (b : Fin (r + 1)) :
    (haveI := P.isPrime; gpGen g F y ξ' b ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal
      (gpMfix Λ F ⊔ Submodule.span (𝓞 E) (Set.range fun a => n (gpGen g F x ξ a)))) := by
  haveI := P.isPrime
  set N := Submodule.span (𝓞 E) (Set.range fun a => n (gpGen g F x ξ a)) with hNdef
  by_cases hg : (g : E) = 0
  · unfold gpGen
    rw [hg, inv_zero, zero_smul]
    exact zero_mem _
  have hNΛ : N ≤ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal Λ := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨a, rfl⟩
    exact gp_locΛ_map _ hn.1 (gp_gen_mem P g hξ hP a)
  have hdec : ∀ a, frame x a = frameAct (frame F) ξ a + (g : E) • gpGen g F x ξ a := by
    intro a
    unfold gpGen
    rw [smul_smul, mul_inv_cancel₀ hg, one_smul]
    abel
  have hK : ∀ a, n (frame x a) ∈ gpK P.asIdeal (gpMfix Λ F) N (g : E) := by
    intro a
    refine (gp_mem_K _).2 ⟨n (frameAct (frame F) ξ a),
      gp_Mfix_map_loc _ hFl hn (gp_frameAct_mem P g hFl hFc hP ξ a), n (gpGen g F x ξ a),
      gp_le_locP _ _ (Submodule.subset_span ⟨a, rfl⟩), ?_⟩
    rw [hdec a, map_add, map_smul]
  have hH : frame y b - n (frame x b) ∈ gpK P.asIdeal (gpMfix Λ F) N (g : E) := by
    have hd : m (frame x b) - frame x b ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (XLam Λ x) :=
      gp_loc_X _ (sub_mem (gp_locΛ_map _ hm.1 (gp_frame_loc P g hxl hxc hP b))
        (gp_frame_loc P g hxl hxc hP b)) (gp_nlam_sub_X hm b)
    have hle := gp_XLam_le P g hxc hP ((gpK P.asIdeal (gpMfix Λ F) N (g : E)).comap (fO n)) ?_ ?_
    · have h1 := hle hd
      rw [Submodule.mem_comap, fO_apply, map_sub] at h1
      rw [hfr b]
      exact h1
    · intro s hs k hk
      rw [Submodule.mem_comap, fO_apply] at hk ⊢
      rw [gp_map_osmul] at hk
      exact gp_K_loc _ hs hk
    · intro a
      rw [Submodule.mem_comap, fO_apply, ← frame_castSucc x a]
      exact hK _
  exact gp_core P.asIdeal (M := gpMfix Λ F) (Λ := Λ) (N := N) (U := gpU F) (c := (g : E))
    (gp_sat _ F hFl hFc.2) (gp_Mfix_le_U F hFl) hNΛ (t := frame y b) (s := frameAct (frame F) ξ' b)
    (t' := n (frame x b)) (s' := n (frameAct (frame F) ξ b)) (v := gpGen g F y ξ' b) (w := n (gpGen g F x ξ b)) rfl
    (gp_gen_mem P g hξ' hP b)
    (gp_locP_sub_E _ (gp_Mfix_le_U F hFl) (gp_frameAct_mem P g hFl hFc hP ξ' b))
    (gp_Mfix_map_loc _ hFl hn (gp_frameAct_mem P g hFl hFc hP ξ b))
    (by unfold gpGen; rw [map_smul, map_sub]) (Submodule.subset_span ⟨b, rfl⟩) hH

/- English proof (translation)
Use `haveI := P.isPrime`. Use `set N := Submodule.span (𝓞 E) (Set.range (gpGen g F y ξ')) with hNdef`. Distinguish the cases in `hg : (g : E) = 0`. Unfold `gpGen`. Rewrite using `[hg, inv_zero, zero_smul, map_zero]`.

Conclude with `zero_mem _`. Establish `hNΛ : N ≤ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal Λ`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨a, rfl⟩`. Conclude with `gp_gen_mem P g hξ' hP a`.

Establish `hdec : ∀ a, frame y a = frameAct (frame F) ξ' a + (g : E) • gpGen g F y ξ' a`. Introduce `a`. Unfold `gpGen`. Rewrite using `[smul_smul, mul_inv_cancel₀ hg, one_smul]`. Normalize the expressions using the abelian group laws.

Establish `hH : n (frame x b) - frame y b ∈ gpK P.asIdeal (gpMfix Λ F) N (g : E)`. Establish `hX : n (m (frame x b) - frame x b) ∈ Xsp y`. Establish `hfr' : ∀ a, frame y a = (m.trans n) (frame x a)` using `fun a => hfr a`. Rewrite using `[Xsp_mem_transport hfr', LinearEquiv.symm_trans_apply, LinearEquiv.symm_apply_apply]`. Conclude with `nlam_maps_X (nlam_inv hm) _ (gp_nlam_sub_X hm b)`.

Establish `hd : n (m (frame x b) - frame x b) ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (XLam Λ y)` using `gp_loc_X _ (gp_locΛ_map _ hn.1 (sub_mem (gp_locΛ_map _ hm.1 (gp_frame_loc P g hxl hxc hP b)) (gp_frame_loc P g hxl hxc hP b))) hX`. Establish `hle` using `gp_XLam_le P g hyc hP (gpK P.asIdeal (gpMfix Λ F) N (g : E)) (fun s hs k hk => gp_K_loc _ hs hk) (fun a => by`. Rewrite using `[← frame_castSucc y a]`. Conclude with `(gp_mem_K _).2 ⟨frameAct (frame F) ξ' _, gp_frameAct_mem P g hFl hFc hP ξ' _, gpGen g F y ξ' _, gp_le_locP _ _ (Submodule.subset_span ⟨_, rfl⟩), hdec _⟩)`. Establish `h1` using `neg_mem (hle hd)`.

Rewrite `h1` using `[map_sub, ← hfr b, neg_sub]`. Conclude with `h1`. Conclude with `gp_core P.asIdeal (M := gpMfix Λ F) (Λ := Λ) (N := N) (U := gpU F) (c := (g : E)) (gp_sat _ F hFl hFc.2) (gp_Mfix_le_U F hFl) hNΛ (t := n (frame x b)) (s := n (frameAct (frame F) ξ b)) (t' := frame y b) (s' := frameAct (frame F) ξ' b) (v := n (gpGen g F x ξ b)) (w := gpGen g F y …`.
-/
theorem generator_mem_local_lattice_backward (P : HeightOneSpectrum (𝓞 E)) (hFl : IsLift Λ F) (hFc : IsFixedConv Λ g F)
    (hxl : IsLift Λ x) (hxc : IsFixedConv Λ g x) (hyc : IsFixedConv Λ g y) (hn : n ∈ NLam Λ F)
    (hm : m ∈ NLam Λ x) (hfr : ∀ a, frame y a = n (m (frame x a))) (hξ : AdmWit Λ g F x ξ)
    (hξ' : AdmWit Λ g F y ξ') (hP : (g : 𝓞 E) ∈ P.asIdeal) (b : Fin (r + 1)) :
    (haveI := P.isPrime; n (gpGen g F x ξ b) ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal
      (gpMfix Λ F ⊔ Submodule.span (𝓞 E) (Set.range (gpGen g F y ξ')))) := by
  haveI := P.isPrime
  set N := Submodule.span (𝓞 E) (Set.range (gpGen g F y ξ')) with hNdef
  by_cases hg : (g : E) = 0
  · unfold gpGen
    rw [hg, inv_zero, zero_smul, map_zero]
    exact zero_mem _
  have hNΛ : N ≤ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal Λ := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨a, rfl⟩
    exact gp_gen_mem P g hξ' hP a
  have hdec : ∀ a, frame y a = frameAct (frame F) ξ' a + (g : E) • gpGen g F y ξ' a := by
    intro a
    unfold gpGen
    rw [smul_smul, mul_inv_cancel₀ hg, one_smul]
    abel
  have hH : n (frame x b) - frame y b ∈ gpK P.asIdeal (gpMfix Λ F) N (g : E) := by
    have hX : n (m (frame x b) - frame x b) ∈ Xsp y := by
      have hfr' : ∀ a, frame y a = (m.trans n) (frame x a) := fun a => hfr a
      rw [Xsp_mem_transport hfr', LinearEquiv.symm_trans_apply, LinearEquiv.symm_apply_apply]
      exact nlam_maps_X (nlam_inv hm) _ (gp_nlam_sub_X hm b)
    have hd : n (m (frame x b) - frame x b) ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (XLam Λ y) :=
      gp_loc_X _ (gp_locΛ_map _ hn.1 (sub_mem (gp_locΛ_map _ hm.1 (gp_frame_loc P g hxl hxc hP b))
        (gp_frame_loc P g hxl hxc hP b))) hX
    have hle := gp_XLam_le P g hyc hP (gpK P.asIdeal (gpMfix Λ F) N (g : E))
      (fun s hs k hk => gp_K_loc _ hs hk) (fun a => by
        rw [← frame_castSucc y a]
        exact (gp_mem_K _).2 ⟨frameAct (frame F) ξ' _, gp_frameAct_mem P g hFl hFc hP ξ' _,
          gpGen g F y ξ' _, gp_le_locP _ _ (Submodule.subset_span ⟨_, rfl⟩), hdec _⟩)
    have h1 := neg_mem (hle hd)
    rw [map_sub, ← hfr b, neg_sub] at h1
    exact h1
  exact gp_core P.asIdeal (M := gpMfix Λ F) (Λ := Λ) (N := N) (U := gpU F) (c := (g : E))
    (gp_sat _ F hFl hFc.2) (gp_Mfix_le_U F hFl) hNΛ (t := n (frame x b))
    (s := n (frameAct (frame F) ξ b)) (t' := frame y b) (s' := frameAct (frame F) ξ' b)
    (v := n (gpGen g F x ξ b)) (w := gpGen g F y ξ' b) (by unfold gpGen; rw [map_smul, map_sub]) (gp_locΛ_map _ hn.1 (gp_gen_mem P g hξ hP b))
    (gp_locP_sub_E _ (gp_Mfix_le_U F hFl) (gp_Mfix_map_loc _ hFl hn (gp_frameAct_mem P g hFl hFc hP ξ b)))
    (gp_frameAct_mem P g hFl hFc hP ξ' b) rfl (Submodule.subset_span ⟨b, rfl⟩) hH

/- English proof (translation)
Use `haveI := P.isPrime`. Establish `hMfix_sub : ∀ v ∈ gpMfix Λ F, v ∈ Formalism.HermitianLatticesTheory.gmap n (Mplus Λ g F x ξ)`. Introduce `v hv`. Rewrite using `[mem_gmap_iff, gp_mplus_eq]`. Conclude with `Submodule.mem_sup_left (gp_Mfix_map hFl (nlam_inv hn) v hv)`.

Apply `le_antisymm` to reduce the goal to its premises. Use `locP_le _ ?_` and prove the remaining obligations. Rewrite using `[gp_mplus_eq]`. Use `sup_le (fun v hv => gp_le_locP _ _ (hMfix_sub v hv)) (Submodule.span_le.2 ?_)` and prove the remaining obligations. Introduce and unpack `_ ⟨b, rfl⟩`.

Use `locP_mono _ (sup_le (fun v hv => hMfix_sub v hv) (Submodule.span_le.2 ?_)) (generator_mem_local_lattice_forward P hFl hFc hxl hxc hn hm hfr hξ hξ' hP b)` and prove the remaining obligations. Introduce and unpack `_ ⟨a, rfl⟩`. Use `show n (gpGen g F x ξ a) ∈ Formalism.HermitianLatticesTheory.gmap n (Mplus Λ g F x ξ)`. Rewrite using `[mem_gmap_iff, LinearEquiv.symm_apply_apply, gp_mplus_eq]`. Conclude with `Submodule.mem_sup_right (Submodule.subset_span ⟨a, rfl⟩)`.

Use `locP_le _ ?_` and prove the remaining obligations. Introduce `v hv`. Rewrite `hv` using `[mem_gmap_iff]`. Establish `key : Mplus Λ g F x ξ ≤ (Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Mplus Λ g F y ξ')).comap (fO n)`. Rewrite using `[gp_mplus_eq (F' := x)]`.

Use `sup_le ?_ (Submodule.span_le.2 ?_)` and prove the remaining obligations. Introduce `w hw`. Rewrite using `[Submodule.mem_comap, fO_apply, gp_mplus_eq]`. Conclude with `gp_le_locP _ _ (Submodule.mem_sup_left (gp_Mfix_map hFl hn w hw))`. Introduce and unpack `_ ⟨b, rfl⟩ show n (gpGen g F x ξ b) ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Mplus Λ g F y ξ')`.

Rewrite using `[gp_mplus_eq]`. Conclude with `generator_mem_local_lattice_backward P hFl hFc hxl hxc hyc hn hm hfr hξ hξ' hP b`. Establish `h1` using `key hv`. Rewrite `h1` using `[Submodule.mem_comap, fO_apply, LinearEquiv.apply_symm_apply]`. Conclude with `h1`.
-/
theorem gp_mplus (P : HeightOneSpectrum (𝓞 E)) (hFl : IsLift Λ F) (hFc : IsFixedConv Λ g F)
    (hxl : IsLift Λ x) (hxc : IsFixedConv Λ g x) (hyc : IsFixedConv Λ g y) (hn : n ∈ NLam Λ F)
    (hm : m ∈ NLam Λ x) (hfr : ∀ a, frame y a = n (m (frame x a))) (hξ : AdmWit Λ g F x ξ)
    (hξ' : AdmWit Λ g F y ξ') (hP : (g : 𝓞 E) ∈ P.asIdeal) :
    (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Mplus Λ g F y ξ') =
      Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Formalism.HermitianLatticesTheory.gmap n (Mplus Λ g F x ξ))) := by
  haveI := P.isPrime
  have hMfix_sub : ∀ v ∈ gpMfix Λ F, v ∈ Formalism.HermitianLatticesTheory.gmap n (Mplus Λ g F x ξ) := by
    intro v hv
    rw [mem_gmap_iff, gp_mplus_eq]
    exact Submodule.mem_sup_left (gp_Mfix_map hFl (nlam_inv hn) v hv)
  apply le_antisymm
  · refine locP_le _ ?_
    rw [gp_mplus_eq]
    refine sup_le (fun v hv => gp_le_locP _ _ (hMfix_sub v hv)) (Submodule.span_le.2 ?_)
    rintro _ ⟨b, rfl⟩
    refine locP_mono _ (sup_le (fun v hv => hMfix_sub v hv) (Submodule.span_le.2 ?_))
      (generator_mem_local_lattice_forward P hFl hFc hxl hxc hn hm hfr hξ hξ' hP b)
    rintro _ ⟨a, rfl⟩
    show n (gpGen g F x ξ a) ∈ Formalism.HermitianLatticesTheory.gmap n (Mplus Λ g F x ξ)
    rw [mem_gmap_iff, LinearEquiv.symm_apply_apply, gp_mplus_eq]
    exact Submodule.mem_sup_right (Submodule.subset_span ⟨a, rfl⟩)
  · refine locP_le _ ?_
    intro v hv
    rw [mem_gmap_iff] at hv
    have key : Mplus Λ g F x ξ ≤ (Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Mplus Λ g F y ξ')).comap (fO n) := by
      rw [gp_mplus_eq (F' := x)]
      refine sup_le ?_ (Submodule.span_le.2 ?_)
      · intro w hw
        rw [Submodule.mem_comap, fO_apply, gp_mplus_eq]
        exact gp_le_locP _ _ (Submodule.mem_sup_left (gp_Mfix_map hFl hn w hw))
      · rintro _ ⟨b, rfl⟩
        show n (gpGen g F x ξ b) ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Mplus Λ g F y ξ')
        rw [gp_mplus_eq]
        exact generator_mem_local_lattice_backward P hFl hFc hxl hxc hyc hn hm hfr hξ hξ' hP b
    have h1 := key hv
    rw [Submodule.mem_comap, fO_apply, LinearEquiv.apply_symm_apply] at h1
    exact h1

end GP4

end PI.TermAttrConst.UnitaryGroupMassFormula
