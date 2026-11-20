import Mathlib
import GroundTheory.TateCohomology.CupConnecting
set_option maxSynthPendingDepth 1

open CategoryTheory groupCohomology

namespace GroundTheory.GroupCoh

universe u

variable {k G : Type u} [CommRing k] [Group G] [Fintype G]

noncomputable abbrev tateIsoH (A : Rep k G) (p : ℤ) (n : ℕ) [NeZero n] (hp : p = n) :
    tateCohomology A p ≅ groupCohomology A n :=
  (tateComplexConnectData A).homologyIsoPos n p hp

/- English proof (translation)
Establish `h` using `congr(($((tateComplex A).iCycles_d n (n + 1))).hom z)`. Rewrite `h` using `[ModuleCat.hom_comp, LinearMap.comp_apply, tateComplex_d_ofNat, inhomogeneousCochains.d_def]`. Conclude with `h`.
-/
theorem tate_d_iCycles (A : Rep k G) (n : ℕ) (z : (tateComplex A).cycles n) :
    (inhomogeneousCochains.d A n).hom (((tateComplex A).iCycles n).hom z) = 0 := by
  have h := congr(($((tateComplex A).iCycles_d n (n + 1))).hom z)
  rw [ModuleCat.hom_comp, LinearMap.comp_apply, tateComplex_d_ofNat,
    inhomogeneousCochains.d_def] at h
  exact h

set_option backward.isDefEq.respectTransparency false in

/- English proof (translation)
Use `⟨?C, ?h1, ?h2⟩` and prove the remaining obligations. Use `case h1 => dsimp only [tateIsoH, CochainComplex.ConnectData.homologyIsoPos]`. Simplify using `only [Iso.trans_hom, Iso.symm_hom, HomologicalComplex.homologyMapIso_hom]`. Rewrite using `[HomologicalComplex.homologyπ_restrictionHomologyIso_inv_assoc, HomologicalComplex.homologyπ_naturality]`. Rewrite using `[← Category.assoc]`.

Use `case h2 =>`. Rewrite using `[Category.assoc, HomologicalComplex.cyclesMap_i, HomologicalComplex.restrictionCyclesIso_inv_iCycles_assoc]`. Simplify using `[CochainComplex.ConnectData.restrictionGEIso]`.
-/
theorem tateIsoH_homology_class_eq (A : Rep k G) (n : ℕ) [NeZero n] :
    ∃ C : (tateComplex A).cycles n ⟶ cocycles A n,
      (tateComplex A).homologyπ n ≫ (tateIsoH A n n rfl).hom = C ≫ π A n ∧
        C ≫ iCocycles A n = (tateComplex A).iCycles n := by
  refine ⟨?C, ?h1, ?h2⟩
  case h1 =>
    dsimp only [tateIsoH, CochainComplex.ConnectData.homologyIsoPos]
    simp only [Iso.trans_hom, Iso.symm_hom, HomologicalComplex.homologyMapIso_hom]
    rw [HomologicalComplex.homologyπ_restrictionHomologyIso_inv_assoc,
      HomologicalComplex.homologyπ_naturality]
    rw [← Category.assoc]
  case h2 =>
    rw [Category.assoc, HomologicalComplex.cyclesMap_i,
      HomologicalComplex.restrictionCyclesIso_inv_iCycles_assoc]
    simp [CochainComplex.ConnectData.restrictionGEIso]

/- English proof (translation)
Take `⟨C, h1, h2⟩` from `tateIsoH_homology_class_eq A n`. Establish `e1 : (tateIsoH A n n rfl).hom.hom (((tateComplex A).homologyπ n).hom z) = (π A n).hom (C.hom z)` using `congr(($h1).hom z)`. Rewrite using `[e1]`. Use `congr 1`. Apply `cocycles_ext` to reduce the goal to its premises.

Use `(congr(($h2).hom z)).trans ?_` and prove the remaining obligations. Conclude with `(iCocycles_mk _ _).symm`.
-/
theorem tateIsoH_homologyπ (A : Rep k G) (n : ℕ) [NeZero n] (z : (tateComplex A).cycles n) :
    (tateIsoH A n n rfl).hom.hom (((tateComplex A).homologyπ n).hom z) =
      π A n (cocyclesMk (((tateComplex A).iCycles n).hom z) (tate_d_iCycles A n z)) := by
  obtain ⟨C, h1, h2⟩ := tateIsoH_homology_class_eq A n
  have e1 : (tateIsoH A n n rfl).hom.hom (((tateComplex A).homologyπ n).hom z) =
      (π A n).hom (C.hom z) := congr(($h1).hom z)
  rw [e1]
  congr 1
  apply cocycles_ext
  refine (congr(($h2).hom z)).trans ?_
  exact (iCocycles_mk _ _).symm

noncomputable def tateCyclesMk (A : Rep k G) (i : ℤ) (x : (tateComplex A).X i)
    (hx : ((tateComplex A).d i (i + 1)).hom x = 0) : (tateComplex A).cycles i :=
  (tateComplex A).cyclesMk x (i + 1) (by simp) hx

/- English proof (translation)
The claim follows from `(tateComplex A).i_cyclesMk x (i + 1) (by simp) hx`.
-/
theorem iCycles_tateCyclesMk (A : Rep k G) (i : ℤ) (x : (tateComplex A).X i)
    (hx : ((tateComplex A).d i (i + 1)).hom x = 0) :
    ((tateComplex A).iCycles i).hom (tateCyclesMk A i x hx) = x :=
  (tateComplex A).i_cyclesMk x (i + 1) (by simp) hx

/- English proof (translation)
Apply `(ModuleCat.mono_iff_injective ((tateComplex A).iCycles i)).1 inferInstance` to reduce the goal to its premises. Rewrite using `[iCycles_tateCyclesMk]`.
-/
theorem tateCyclesMk_iCycles (A : Rep k G) (i : ℤ) (z : (tateComplex A).cycles i)
    (hz : ((tateComplex A).d i (i + 1)).hom (((tateComplex A).iCycles i).hom z) = 0) :
    tateCyclesMk A i (((tateComplex A).iCycles i).hom z) hz = z := by
  apply (ModuleCat.mono_iff_injective ((tateComplex A).iCycles i)).1 inferInstance
  rw [iCycles_tateCyclesMk]

/- English proof (translation)
Establish `h` using `congr(($((tateComplex A).iCycles_d i (i + 1))).hom z)`. Rewrite `h` using `[ModuleCat.hom_comp, LinearMap.comp_apply]`. Conclude with `h`.
-/
theorem tate_d_iCycles_int (A : Rep k G) (i : ℤ) (z : (tateComplex A).cycles i) :
    ((tateComplex A).d i (i + 1)).hom (((tateComplex A).iCycles i).hom z) = 0 := by
  have h := congr(($((tateComplex A).iCycles_d i (i + 1))).hom z)
  rw [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  exact h

noncomputable abbrev tδ {S : ShortComplex (Rep k G)} (hS : S.ShortExact) (i j : ℤ)
    (hij : i + 1 = j) :
    tateCohomology S.X₃ i ⟶ tateCohomology S.X₁ j :=
  (TateCohomology.map_tateComplexFunctor_shortExact hS).δ i j hij

set_option backward.isDefEq.respectTransparency false in

/- English proof (translation)
The claim follows from `(TateCohomology.map_tateComplexFunctor_shortExact hS).δ_apply i (i + 1) rfl x₃ hx₃ x₂ hx₂ x₁ hx₁ (i + 1 + 1) (by simp)`.
-/
theorem tδ_apply {S : ShortComplex (Rep k G)} (hS : S.ShortExact) (i : ℤ)
    (x₃ : (tateComplex S.X₃).X i) (hx₃ : ((tateComplex S.X₃).d i (i + 1)).hom x₃ = 0)
    (x₂ : (tateComplex S.X₂).X i) (hx₂ : ((tateComplex.map S.g).f i).hom x₂ = x₃)
    (x₁ : (tateComplex S.X₁).X (i + 1))
    (hx₁ : ((tateComplex.map S.f).f (i + 1)).hom x₁ = ((tateComplex S.X₂).d i (i + 1)).hom x₂)
    (hd : ((tateComplex S.X₁).d (i + 1) (i + 1 + 1)).hom x₁ = 0) :
    (tδ hS i (i + 1) rfl).hom (((tateComplex S.X₃).homologyπ i).hom (tateCyclesMk _ i x₃ hx₃)) =
      ((tateComplex S.X₁).homologyπ (i + 1)).hom (tateCyclesMk _ (i + 1) x₁ hd) :=
  (TateCohomology.map_tateComplexFunctor_shortExact hS).δ_apply i (i + 1) rfl x₃ hx₃ x₂ hx₂ x₁ hx₁
    (i + 1 + 1) (by simp)

set_option backward.isDefEq.respectTransparency false in

/- English proof (translation)
Apply `(cancel_epi ((tateComplex S.X₃).homologyπ n)).1` to reduce the goal to its premises. Use extensionality with `z`. Simplify using `only [ModuleCat.hom_comp, LinearMap.comp_apply]`. Establish `hz` using `tate_d_iCycles_int _ _ z`. Take `⟨y, x, hy, hx⟩` from `exists_lift_of_cocycle hS (cocyclesMk (((tateComplex S.X₃).iCycles n).hom z) (tate_d_iCycles _ n z))`.

Establish `hd : ((tateComplex S.X₁).d (↑n + 1) (↑n + 1 + 1)).hom (iCocycles S.X₁ (n + 1) x) = 0`. Use `d_iCocycles x` as an intermediate fact. Rewrite `this` using `[← inhomogeneousCochains.d_def]`. Conclude with `this`. Establish `hy' : ((tateComplex.map S.g).f n).hom y = ((tateComplex S.X₃).iCycles n).hom z`.

Use function extensionality and compare the values at `fun v => (hy v).trans (congrFun (iCocycles_mk _ _) v)`. Establish `hx' : ((tateComplex.map S.f).f (↑n + 1)).hom (iCocycles S.X₁ (n + 1) x) = ((tateComplex S.X₂).d n (n + 1)).hom y`. Rewrite using `[tateComplex_d_ofNat, inhomogeneousCochains.d_def]`. Conclude with `funext hx`. Establish `h1` using `tateIsoH_homologyπ S.X₃ n z`.

Establish `h2` using `δ_π_eq hS _ y hy x hx`. Establish `h3 : (tδ hS n (n + 1) rfl).hom (((tateComplex S.X₃).homologyπ n).hom z) = ((tateComplex S.X₁).homologyπ (n + 1)).hom (tateCyclesMk S.X₁ (n + 1) (iCocycles S.X₁ (n + 1) x) hd)`. Establish `e` using `tδ_apply hS n _ hz y hy' (iCocycles S.X₁ (n + 1) x) hx' hd`. Rewrite `e` using `[tateCyclesMk_iCycles]`. Conclude with `e`.

Establish `h4` using `tateIsoH_homologyπ S.X₁ (n + 1) (tateCyclesMk S.X₁ (n + 1) (iCocycles S.X₁ (n + 1) x) hd)`. Use `((congrArg (fun w => (tateIsoH S.X₁ (↑n + 1) (n + 1) (Nat.cast_succ n).symm).hom.hom w) h3).trans ?_).trans (congrArg (fun w => (δ hS n (n + 1) rfl).hom w) h1).symm` and prove the remaining obligations. Use `(h4.trans ?_).trans h2.symm` and prove the remaining obligations. Use `congr 1`. Apply `cocycles_ext` to reduce the goal to its premises.

Conclude with `(iCocycles_mk _ _).trans (iCycles_tateCyclesMk _ _ _ _)`.
-/
theorem tδ_comp_tateIsoH {S : ShortComplex (Rep k G)} (hS : S.ShortExact) (n : ℕ) [NeZero n] :
    tδ hS n (n + 1) rfl ≫ (tateIsoH S.X₁ (n + 1) (n + 1) (Nat.cast_succ n).symm).hom =
      (tateIsoH S.X₃ n n rfl).hom ≫ δ hS n (n + 1) rfl := by
  apply (cancel_epi ((tateComplex S.X₃).homologyπ n)).1
  ext z
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
  have hz := tate_d_iCycles_int _ _ z
  obtain ⟨y, x, hy, hx⟩ := exists_lift_of_cocycle hS
    (cocyclesMk (((tateComplex S.X₃).iCycles n).hom z) (tate_d_iCycles _ n z))
  have hd : ((tateComplex S.X₁).d (↑n + 1) (↑n + 1 + 1)).hom (iCocycles S.X₁ (n + 1) x) = 0 := by
    have := d_iCocycles x
    rw [← inhomogeneousCochains.d_def] at this
    exact this
  have hy' : ((tateComplex.map S.g).f n).hom y = ((tateComplex S.X₃).iCycles n).hom z :=
    funext fun v => (hy v).trans (congrFun (iCocycles_mk _ _) v)
  have hx' : ((tateComplex.map S.f).f (↑n + 1)).hom (iCocycles S.X₁ (n + 1) x) =
      ((tateComplex S.X₂).d n (n + 1)).hom y := by
    rw [tateComplex_d_ofNat, inhomogeneousCochains.d_def]
    exact funext hx
  have h1 := tateIsoH_homologyπ S.X₃ n z
  have h2 := δ_π_eq hS _ y hy x hx
  have h3 : (tδ hS n (n + 1) rfl).hom (((tateComplex S.X₃).homologyπ n).hom z) =
      ((tateComplex S.X₁).homologyπ (n + 1)).hom (tateCyclesMk S.X₁ (n + 1) (iCocycles S.X₁ (n + 1) x) hd) := by
    have e := tδ_apply hS n _ hz y hy' (iCocycles S.X₁ (n + 1) x) hx' hd
    rw [tateCyclesMk_iCycles] at e
    exact e
  have h4 := tateIsoH_homologyπ S.X₁ (n + 1) (tateCyclesMk S.X₁ (n + 1) (iCocycles S.X₁ (n + 1) x) hd)
  refine ((congrArg (fun w => (tateIsoH S.X₁ (↑n + 1) (n + 1) (Nat.cast_succ n).symm).hom.hom w)
    h3).trans ?_).trans (congrArg (fun w => (δ hS n (n + 1) rfl).hom w) h1).symm
  refine (h4.trans ?_).trans h2.symm
  congr 1
  apply cocycles_ext
  exact (iCocycles_mk _ _).trans (iCycles_tateCyclesMk _ _ _ _)

section Elements

variable {X Y Z : Rep k G}

/- English proof (translation)
Establish `h` using `(tateComplexFunctor k G).map_comp φ ψ`. Simplify using `only [tateComplexFunctor_map] at h`. Rewrite using `[h]`. Both sides reduce to the same expression.
-/
theorem tateMap_comp_apply (φ : X ⟶ Y) (ψ : Y ⟶ Z) (i : ℤ) (x : (tateComplex X).X i) :
    ((tateComplex.map (φ ≫ ψ)).f i).hom x =
      ((tateComplex.map ψ).f i).hom (((tateComplex.map φ).f i).hom x) := by
  have h := (tateComplexFunctor k G).map_comp φ ψ
  simp only [tateComplexFunctor_map] at h
  rw [h]
  rfl

/- English proof (translation)
Rewrite using `[h]`.
-/
theorem tateMap_congr {φ ψ : X ⟶ Y} (h : φ = ψ) (i : ℤ) (x : (tateComplex X).X i) :
    ((tateComplex.map φ).f i).hom x = ((tateComplex.map ψ).f i).hom x := by
  rw [h]

/- English proof (translation)
Establish `h` using `(tateComplex.map φ).comm i j`. Conclude with `congr(($h).hom x).symm`.
-/
theorem tateMap_d_apply (φ : X ⟶ Y) (i j : ℤ) (x : (tateComplex X).X i) :
    ((tateComplex.map φ).f j).hom (((tateComplex X).d i j).hom x) =
      ((tateComplex Y).d i j).hom (((tateComplex.map φ).f i).hom x) := by
  have h := (tateComplex.map φ).comm i j
  exact congr(($h).hom x).symm

/- English proof (translation)
Rewrite using `[tateComplex.map_zero]`. Both sides reduce to the same expression.
-/
theorem tateMap_zero_apply (i : ℤ) (x : (tateComplex X).X i) :
    ((tateComplex.map (0 : X ⟶ Y)).f i).hom x = 0 := by
  rw [tateComplex.map_zero]
  rfl

/- English proof (translation)
Establish `h` using `(tateComplex X).d_comp_d i j l`. Conclude with `congr(($h).hom x)`.
-/
theorem tateD_tateD_apply (i j l : ℤ) (x : (tateComplex X).X i) :
    ((tateComplex X).d j l).hom (((tateComplex X).d i j).hom x) = 0 := by
  have h := (tateComplex X).d_comp_d i j l
  exact congr(($h).hom x)

variable {S : ShortComplex (Rep k G)} (hS : S.ShortExact)
include hS

/- English proof (translation)
Establish `h` using `(HomologicalComplex.shortExact_iff_degreewise_shortExact _).1 (TateCohomology.map_tateComplexFunctor_shortExact hS) i`. Conclude with `(ModuleCat.epi_iff_surjective _).1 h.epi_g`.
-/
theorem tateMap_g_surjective (i : ℤ) : Function.Surjective ((tateComplex.map S.g).f i).hom := by
  have h := (HomologicalComplex.shortExact_iff_degreewise_shortExact _).1
    (TateCohomology.map_tateComplexFunctor_shortExact hS) i
  exact (ModuleCat.epi_iff_surjective _).1 h.epi_g

/- English proof (translation)
Establish `h` using `(HomologicalComplex.shortExact_iff_degreewise_shortExact _).1 (TateCohomology.map_tateComplexFunctor_shortExact hS) i`. Conclude with `(ModuleCat.mono_iff_injective _).1 h.mono_f`.
-/
theorem tateMap_f_injective (i : ℤ) : Function.Injective ((tateComplex.map S.f).f i).hom := by
  have h := (HomologicalComplex.shortExact_iff_degreewise_shortExact _).1
    (TateCohomology.map_tateComplexFunctor_shortExact hS) i
  exact (ModuleCat.mono_iff_injective _).1 h.mono_f

/- English proof (translation)
Establish `h` using `(HomologicalComplex.shortExact_iff_degreewise_shortExact _).1 (TateCohomology.map_tateComplexFunctor_shortExact hS) i`. Establish `hr` using `h.exact.moduleCat_range_eq_ker`. Establish `hm : y ∈ LinearMap.ker ((S.map (tateComplexFunctor k G)).map (HomologicalComplex.eval _ _ i)).g.hom` using `hy`. Rewrite `hm` using `[← hr]`. Conclude with `hm`.
-/
theorem tateMap_exists_f_eq (i : ℤ) (y : (tateComplex S.X₂).X i)
    (hy : ((tateComplex.map S.g).f i).hom y = 0) :
    ∃ x, ((tateComplex.map S.f).f i).hom x = y := by
  have h := (HomologicalComplex.shortExact_iff_degreewise_shortExact _).1
    (TateCohomology.map_tateComplexFunctor_shortExact hS) i
  have hr := h.exact.moduleCat_range_eq_ker
  have hm : y ∈ LinearMap.ker ((S.map (tateComplexFunctor k G)).map
      (HomologicalComplex.eval _ _ i)).g.hom := hy
  rw [← hr] at hm
  exact hm

end Elements

/- English proof (translation)
Apply `(ModuleCat.mono_iff_injective ((tateComplex A).iCycles i)).1 inferInstance` to reduce the goal to its premises. Rewrite using `[map_neg, iCycles_tateCyclesMk, iCycles_tateCyclesMk]`.
-/
theorem tateCyclesMk_neg (A : Rep k G) (i : ℤ) (x : (tateComplex A).X i)
    (hx : ((tateComplex A).d i (i + 1)).hom x = 0) (hx' : ((tateComplex A).d i (i + 1)).hom (-x) = 0) :
    tateCyclesMk A i (-x) hx' = -tateCyclesMk A i x hx := by
  apply (ModuleCat.mono_iff_injective ((tateComplex A).iCycles i)).1 inferInstance
  rw [map_neg, iCycles_tateCyclesMk, iCycles_tateCyclesMk]

section Anticomm

variable (Q : ShortComplex (ShortComplex (Rep k G)))
  (hR₁ : Q.X₁.ShortExact) (hR₂ : Q.X₂.ShortExact) (hR₃ : Q.X₃.ShortExact)
  (hC₁ : (Q.map ShortComplex.π₁).ShortExact) (hC₂ : (Q.map ShortComplex.π₂).ShortExact)
  (hC₃ : (Q.map ShortComplex.π₃).ShortExact)

include hR₂ hC₂ in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in

/- English proof (translation)
Apply `(cancel_epi ((tateComplex Q.X₃.X₃).homologyπ p)).1` to reduce the goal to its premises. Use extensionality with `z`. Simplify using `only [Preadditive.comp_neg, ModuleCat.hom_comp, ModuleCat.hom_neg, LinearMap.comp_apply, LinearMap.neg_apply]`. Establish `hz` using `tate_d_iCycles_int _ _ z`. Rewrite using `[← tateCyclesMk_iCycles _ _ z hz]`.

Use `set x33 := ((tateComplex Q.X₃.X₃).iCycles p).hom z`. Establish `hQ : Q.f.τ₂ ≫ Q.g.τ₂ = 0` using `by rw [← ShortComplex.comp_τ₂, Q.zero, ShortComplex.zero_τ₂]`. Take `⟨x32, hx32⟩` from `tateMap_g_surjective hR₃ p x33`. Take `⟨x22, hx22⟩ : ∃ x22 : (tateComplex Q.X₂.X₂).X p, ((tateComplex.map Q.g.τ₂).f p).hom x22 = x32` from `tateMap_g_surjective hC₂ p x32`. Use `set x23 := ((tateComplex.map Q.X₂.g).f p).hom x22`.

Establish `hx23 : ((tateComplex.map Q.g.τ₃).f p).hom x23 = x33`. Rewrite using `[← tateMap_comp_apply, tateMap_congr Q.g.comm₂₃.symm, tateMap_comp_apply]`. Conclude with `(congrArg _ hx22).trans hx32`. Establish `hb0 : ((tateComplex.map Q.g.τ₃).f (p + 1)).hom (((tateComplex Q.X₂.X₃).d p (p + 1)).hom x23) = 0`. Rewrite using `[tateMap_d_apply, hx23, hz]`.

Take `⟨b, hb⟩ : ∃ b : (tateComplex Q.X₁.X₃).X (p + 1), ((tateComplex.map Q.f.τ₃).f (p + 1)).hom b = ((tateComplex Q.X₂.X₃).d p (p + 1)).hom x23` from `tateMap_exists_f_eq hC₃ (p + 1) _ hb0`. Establish `hdb : ((tateComplex Q.X₁.X₃).d (p + 1) (p + 1 + 1)).hom b = 0`. Establish `h1 : ((tateComplex.map Q.f.τ₃).f (p + 1 + 1)).hom (((tateComplex Q.X₁.X₃).d (p + 1) (p + 1 + 1)).hom b) = ((tateComplex.map Q.f.τ₃).f (p + 1 + 1)).hom 0`. Rewrite using `[tateMap_d_apply, hb, tateD_tateD_apply, map_zero]`. Conclude with `tateMap_f_injective hC₃ (p + 1 + 1) h1`.

Establish `e1` using `tδ_apply hC₃ p x33 hz x23 hx23 b hb hdb`. Take `⟨c, hc⟩` from `tateMap_g_surjective hR₁ (p + 1) b`. Establish `hw0 : ((tateComplex.map Q.X₁.g).f (p + 1 + 1)).hom (((tateComplex Q.X₁.X₂).d (p + 1) (p + 1 + 1)).hom c) = 0`. Rewrite using `[tateMap_d_apply, hc, hdb]`. Take `⟨w, hw⟩` from `tateMap_exists_f_eq hR₁ (p + 1 + 1) _ hw0`.

Establish `hdw : ((tateComplex Q.X₁.X₁).d (p + 1 + 1) (p + 1 + 1 + 1)).hom w = 0`. Establish `h1 : ((tateComplex.map Q.X₁.f).f (p + 1 + 1 + 1)).hom (((tateComplex Q.X₁.X₁).d (p + 1 + 1) (p + 1 + 1 + 1)).hom w) = ((tateComplex.map Q.X₁.f).f (p + 1 + 1 + 1)).hom 0`. Rewrite using `[tateMap_d_apply, hw, tateD_tateD_apply, map_zero]`. Conclude with `tateMap_f_injective hR₁ _ h1`. Establish `e2` using `tδ_apply hR₁ (p + 1) b hdb c hc w hw hdw`.

Establish `he0 : ((tateComplex.map Q.X₂.g).f (p + 1)).hom (((tateComplex Q.X₂.X₂).d p (p + 1)).hom x22 - ((tateComplex.map Q.f.τ₂).f (p + 1)).hom c) = 0`. Rewrite using `[map_sub, tateMap_d_apply, ← tateMap_comp_apply Q.f.τ₂ Q.X₂.g, tateMap_congr Q.f.comm₂₃, tateMap_comp_apply, hc, sub_eq_zero]`. Conclude with `hb.symm`. Take `⟨e, he⟩` from `tateMap_exists_f_eq hR₂ (p + 1) _ he0`. Establish `hge : ((tateComplex.map Q.X₃.f).f (p + 1)).hom (((tateComplex.map Q.g.τ₁).f (p + 1)).hom e) = ((tateComplex Q.X₃.X₂).d p (p + 1)).hom x32`.

Rewrite using `[← tateMap_comp_apply, tateMap_congr Q.g.comm₁₂, tateMap_comp_apply, he, map_sub, tateMap_d_apply, hx22, ← tateMap_comp_apply Q.f.τ₂ Q.g.τ₂, tateMap_congr hQ, tateMap_zero_apply, sub_zero]`. Establish `hdge : ((tateComplex Q.X₃.X₁).d (p + 1) (p + 1 + 1)).hom (((tateComplex.map Q.g.τ₁).f (p + 1)).hom e) = 0`. Establish `h1 : ((tateComplex.map Q.X₃.f).f (p + 1 + 1)).hom (((tateComplex Q.X₃.X₁).d (p + 1) (p + 1 + 1)).hom (((tateComplex.map Q.g.τ₁).f (p + 1)).hom e)) = ((tateComplex.map Q.X₃.f).f (p + 1 + 1)).hom 0`. Rewrite using `[tateMap_d_apply, hge, tateD_tateD_apply, map_zero]`. Conclude with `tateMap_f_injective hR₃ _ h1`.

Establish `e3` using `tδ_apply hR₃ p x33 hz x32 hx32 _ hge hdge`. Establish `hde : ((tateComplex.map Q.f.τ₁).f (p + 1 + 1)).hom (-w) = ((tateComplex Q.X₂.X₁).d (p + 1) (p + 1 + 1)).hom e`. Apply `tateMap_f_injective hR₂` to reduce the goal to its premises. Rewrite using `[map_neg, map_neg, ← tateMap_comp_apply, tateMap_congr Q.f.comm₁₂, tateMap_comp_apply, hw, tateMap_d_apply, tateMap_d_apply, he, map_sub, tateD_tateD_apply, zero_sub]`. Establish `hdnw : ((tateComplex Q.X₁.X₁).d (p + 1 + 1) (p + 1 + 1 + 1)).hom (-w) = 0`.

Rewrite using `[map_neg, hdw, neg_zero]`. Establish `e4` using `tδ_apply hC₁ (p + 1) _ hdge e rfl (-w) hde hdnw`. Establish `e1' : (tδ hC₃ p (p + 1) rfl).hom (((tateComplex Q.X₃.X₃).homologyπ p).hom (tateCyclesMk Q.X₃.X₃ p x33 hz)) = ((tateComplex Q.X₁.X₃).homologyπ (p + 1)).hom (tateCyclesMk Q.X₁.X₃ (p + 1) b hdb)` using `e1`. Establish `e4' : (tδ hC₁ (p + 1) (p + 1 + 1) rfl).hom (((tateComplex Q.X₃.X₁).homologyπ (p + 1)).hom (tateCyclesMk Q.X₃.X₁ (p + 1) (((tateComplex.map Q.g.τ₁).f (p + 1)).hom e) hdge)) = ((tateComplex Q.X₁.X₁).homologyπ (p + 1 + 1)).hom (tateCyclesMk Q.X₁.X₁ (p + 1 + 1) (-w) hdnw)` using `e4`. Establish `key : (tδ hR₁ (p + 1) (p + 1 + 1) rfl).hom ((tδ hC₃ p (p + 1) rfl).hom (((tateComplex Q.X₃.X₃).homologyπ p).hom (tateCyclesMk Q.X₃.X₃ p x33 hz))) = -(tδ hC₁ (p + 1) (p + 1 + 1) rfl).hom ((tδ hR₃ p (p + 1) rfl).hom (((tateComplex Q.X₃.X₃).homologyπ p).hom (tateCyclesMk Q.X₃.X₃ p x …`.

Rewrite using `[e1', e2, e3, e4', tateCyclesMk_neg _ _ w hdw hdnw, map_neg, neg_neg]`. Conclude with `key`.
-/
theorem tδ_comp_tδ (p : ℤ) :
    tδ hC₃ p (p + 1) rfl ≫ tδ hR₁ (p + 1) (p + 1 + 1) rfl =
      -(tδ hR₃ p (p + 1) rfl ≫ tδ hC₁ (p + 1) (p + 1 + 1) rfl) := by
  apply (cancel_epi ((tateComplex Q.X₃.X₃).homologyπ p)).1
  ext z
  simp only [Preadditive.comp_neg, ModuleCat.hom_comp, ModuleCat.hom_neg, LinearMap.comp_apply,
    LinearMap.neg_apply]
  have hz := tate_d_iCycles_int _ _ z
  rw [← tateCyclesMk_iCycles _ _ z hz]
  set x33 := ((tateComplex Q.X₃.X₃).iCycles p).hom z
  have hQ : Q.f.τ₂ ≫ Q.g.τ₂ = 0 := by rw [← ShortComplex.comp_τ₂, Q.zero, ShortComplex.zero_τ₂]
  obtain ⟨x32, hx32⟩ := tateMap_g_surjective hR₃ p x33
  obtain ⟨x22, hx22⟩ : ∃ x22 : (tateComplex Q.X₂.X₂).X p,
      ((tateComplex.map Q.g.τ₂).f p).hom x22 = x32 := tateMap_g_surjective hC₂ p x32
  set x23 := ((tateComplex.map Q.X₂.g).f p).hom x22
  have hx23 : ((tateComplex.map Q.g.τ₃).f p).hom x23 = x33 := by
    rw [← tateMap_comp_apply, tateMap_congr Q.g.comm₂₃.symm, tateMap_comp_apply]
    exact (congrArg _ hx22).trans hx32
  have hb0 : ((tateComplex.map Q.g.τ₃).f (p + 1)).hom
      (((tateComplex Q.X₂.X₃).d p (p + 1)).hom x23) = 0 := by
    rw [tateMap_d_apply, hx23, hz]
  obtain ⟨b, hb⟩ : ∃ b : (tateComplex Q.X₁.X₃).X (p + 1), ((tateComplex.map Q.f.τ₃).f (p + 1)).hom b =
      ((tateComplex Q.X₂.X₃).d p (p + 1)).hom x23 := tateMap_exists_f_eq hC₃ (p + 1) _ hb0
  have hdb : ((tateComplex Q.X₁.X₃).d (p + 1) (p + 1 + 1)).hom b = 0 := by
    have h1 : ((tateComplex.map Q.f.τ₃).f (p + 1 + 1)).hom
        (((tateComplex Q.X₁.X₃).d (p + 1) (p + 1 + 1)).hom b) =
        ((tateComplex.map Q.f.τ₃).f (p + 1 + 1)).hom 0 := by
      rw [tateMap_d_apply, hb, tateD_tateD_apply, map_zero]
    exact tateMap_f_injective hC₃ (p + 1 + 1) h1
  have e1 := tδ_apply hC₃ p x33 hz x23 hx23 b hb hdb
  obtain ⟨c, hc⟩ := tateMap_g_surjective hR₁ (p + 1) b
  have hw0 : ((tateComplex.map Q.X₁.g).f (p + 1 + 1)).hom
      (((tateComplex Q.X₁.X₂).d (p + 1) (p + 1 + 1)).hom c) = 0 := by
    rw [tateMap_d_apply, hc, hdb]
  obtain ⟨w, hw⟩ := tateMap_exists_f_eq hR₁ (p + 1 + 1) _ hw0
  have hdw : ((tateComplex Q.X₁.X₁).d (p + 1 + 1) (p + 1 + 1 + 1)).hom w = 0 := by
    have h1 : ((tateComplex.map Q.X₁.f).f (p + 1 + 1 + 1)).hom
        (((tateComplex Q.X₁.X₁).d (p + 1 + 1) (p + 1 + 1 + 1)).hom w) =
        ((tateComplex.map Q.X₁.f).f (p + 1 + 1 + 1)).hom 0 := by
      rw [tateMap_d_apply, hw, tateD_tateD_apply, map_zero]
    exact tateMap_f_injective hR₁ _ h1
  have e2 := tδ_apply hR₁ (p + 1) b hdb c hc w hw hdw
  have he0 : ((tateComplex.map Q.X₂.g).f (p + 1)).hom
      (((tateComplex Q.X₂.X₂).d p (p + 1)).hom x22 - ((tateComplex.map Q.f.τ₂).f (p + 1)).hom c) = 0 := by
    rw [map_sub, tateMap_d_apply, ← tateMap_comp_apply Q.f.τ₂ Q.X₂.g, tateMap_congr Q.f.comm₂₃,
      tateMap_comp_apply, hc, sub_eq_zero]
    exact hb.symm
  obtain ⟨e, he⟩ := tateMap_exists_f_eq hR₂ (p + 1) _ he0
  have hge : ((tateComplex.map Q.X₃.f).f (p + 1)).hom (((tateComplex.map Q.g.τ₁).f (p + 1)).hom e) =
      ((tateComplex Q.X₃.X₂).d p (p + 1)).hom x32 := by
    rw [← tateMap_comp_apply, tateMap_congr Q.g.comm₁₂, tateMap_comp_apply, he, map_sub, tateMap_d_apply, hx22,
      ← tateMap_comp_apply Q.f.τ₂ Q.g.τ₂, tateMap_congr hQ, tateMap_zero_apply, sub_zero]
  have hdge : ((tateComplex Q.X₃.X₁).d (p + 1) (p + 1 + 1)).hom
      (((tateComplex.map Q.g.τ₁).f (p + 1)).hom e) = 0 := by
    have h1 : ((tateComplex.map Q.X₃.f).f (p + 1 + 1)).hom
        (((tateComplex Q.X₃.X₁).d (p + 1) (p + 1 + 1)).hom (((tateComplex.map Q.g.τ₁).f (p + 1)).hom e)) =
        ((tateComplex.map Q.X₃.f).f (p + 1 + 1)).hom 0 := by
      rw [tateMap_d_apply, hge, tateD_tateD_apply, map_zero]
    exact tateMap_f_injective hR₃ _ h1
  have e3 := tδ_apply hR₃ p x33 hz x32 hx32 _ hge hdge
  have hde : ((tateComplex.map Q.f.τ₁).f (p + 1 + 1)).hom (-w) =
      ((tateComplex Q.X₂.X₁).d (p + 1) (p + 1 + 1)).hom e := by
    apply tateMap_f_injective hR₂
    rw [map_neg, map_neg, ← tateMap_comp_apply, tateMap_congr Q.f.comm₁₂, tateMap_comp_apply, hw,
      tateMap_d_apply, tateMap_d_apply, he, map_sub, tateD_tateD_apply, zero_sub]
  have hdnw : ((tateComplex Q.X₁.X₁).d (p + 1 + 1) (p + 1 + 1 + 1)).hom (-w) = 0 := by
    rw [map_neg, hdw, neg_zero]
  have e4 := tδ_apply hC₁ (p + 1) _ hdge e rfl (-w) hde hdnw
  have e1' : (tδ hC₃ p (p + 1) rfl).hom (((tateComplex Q.X₃.X₃).homologyπ p).hom
      (tateCyclesMk Q.X₃.X₃ p x33 hz)) =
      ((tateComplex Q.X₁.X₃).homologyπ (p + 1)).hom (tateCyclesMk Q.X₁.X₃ (p + 1) b hdb) := e1
  have e4' : (tδ hC₁ (p + 1) (p + 1 + 1) rfl).hom (((tateComplex Q.X₃.X₁).homologyπ (p + 1)).hom
      (tateCyclesMk Q.X₃.X₁ (p + 1) (((tateComplex.map Q.g.τ₁).f (p + 1)).hom e) hdge)) =
      ((tateComplex Q.X₁.X₁).homologyπ (p + 1 + 1)).hom (tateCyclesMk Q.X₁.X₁ (p + 1 + 1) (-w) hdnw) := e4
  have key : (tδ hR₁ (p + 1) (p + 1 + 1) rfl).hom ((tδ hC₃ p (p + 1) rfl).hom
      (((tateComplex Q.X₃.X₃).homologyπ p).hom (tateCyclesMk Q.X₃.X₃ p x33 hz))) =
      -(tδ hC₁ (p + 1) (p + 1 + 1) rfl).hom ((tδ hR₃ p (p + 1) rfl).hom
        (((tateComplex Q.X₃.X₃).homologyπ p).hom (tateCyclesMk Q.X₃.X₃ p x33 hz))) := by
    rw [e1', e2, e3, e4', tateCyclesMk_neg _ _ w hdw hdnw, map_neg, neg_neg]
  exact key

end Anticomm

end GroundTheory.GroupCoh
