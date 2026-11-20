import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqSplitFinMulSplitInf
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AutomorphicRepDualPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvariantPositivePeterssonFormStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.TrKer
open scoped Classical TensorProduct Topology
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.FrameAut.VecSemis

open GlobalTheory.UnitarySemisimple

/- English proof (translation)
Use `set O := orbSpan ρ y with hO`. Set `ρO` to `O.toRepresentation`. Establish `hρO : ∀ g (w : O.toSubmodule), (ρO g w : V) = ρ g w` using `fun _ _ => rfl`. Set `BO : O.toSubmodule →ₗ⋆[ℂ] O.toSubmodule →ₗ[ℂ] ℂ` to `(B.comp O.toSubmodule.subtype).compl₂ O.toSubmodule.subtype`. Establish `hBO : ∀ u w : O.toSubmodule, BO u w = B u w` using `fun _ _ => rfl`.

Establish `hsmO : ∀ w : O.toSubmodule, IsOpen {k : H | ρO k w = w}`. Introduce `w`. Use `hsm w.1 using 1` and compare the differences between its conclusion and the goal. Use extensionality with `k`. Simplify using `only [Set.mem_setOf_eq]`.

Conclude with `⟨fun h => by rw [← hρO, h], fun h => Subtype.ext (by rw [hρO, h])⟩`. Establish `hfdO : ∀ K : Subgroup H, IsOpen (K : Set H) → FiniteDimensional ℂ (GlobalTheory.PRep.fixed ρO K)`. Introduce `K hK`. Use `haveI := hfd K hK`. Establish `hle : (GlobalTheory.PRep.fixed ρO K).map O.toSubmodule.subtype ≤ GlobalTheory.PRep.fixed ρ K`.

Introduce and unpack `_ ⟨w, hw, rfl⟩ k`. Establish `h1` using `hw k`. Use `show ρ k w.1 = ((1 : K →* ℂˣ) k : ℂ) • w.1`. Rewrite `h1`, the goal using `[MonoidHom.one_apply, Units.val_one, one_smul]`. Rewrite using `[← hρO, h1]`.

Use `haveI : FiniteDimensional ℂ ((GlobalTheory.PRep.fixed ρO K).map O.toSubmodule.subtype) := Submodule.finiteDimensional_of_le hle`. Conclude with `LinearEquiv.finiteDimensional (Submodule.equivMapOfInjective _ O.toSubmodule.injective_subtype _).symm`. Establish `hy0 : (⟨y, mem_orbSpan ρ y⟩ : O.toSubmodule) ≠ 0` using `fun h => hy (congrArg Subtype.val h)`. Take `⟨U', P, hU0, hUst, hUirr, -, -, -⟩` from `GlobalTheory.AdmissibleProjection.exists_irreducible_equivariant_projection H O.toSubmodule ρO BO (fun u w => hh u w) (fun v => hp v) (fun v h => Subtype.ext (hd v h)) (fun g u w => hi g u w) hK0 hsmO hfdO _ hy0`. Use `⟨U'.map O.toSubmodule.subtype, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Introduce `h`. Apply `hU0` to reduce the goal to its premises. Rewrite using `[Submodule.eq_bot_iff]`. Introduce `u hu`. Establish `: u.1 ∈ U'.map O.toSubmodule.subtype` using `⟨u, hu, rfl⟩`.

Rewrite `this` using `[h, Submodule.mem_bot]`. Conclude with `Subtype.ext this`. Introduce and unpack `_ ⟨u, -, rfl⟩`. Conclude with `u.2`. Introduce and unpack `g _ ⟨u, hu, rfl⟩`.

Conclude with `⟨ρO g u, hUst g u hu, rfl⟩`. Introduce `N hNU hN`. Set `N' : Submodule ℂ O.toSubmodule` to `N.comap O.toSubmodule.subtype`. Establish `hN'U : N' ≤ U'`. Introduce `u hu`.

Take `⟨w, hw, hwu⟩` from `hNU hu`. Rewrite using `[← Subtype.ext hwu]`. Conclude with `hw`. Establish `hN'st : ∀ g, ∀ u ∈ N', ρO g u ∈ N'` using `fun g u hu => hN g u.1 hu`. Establish `hNe : N'.map O.toSubmodule.subtype = N`.

Rewrite using `[Submodule.map_comap_subtype]`. Conclude with `inf_eq_right.2 (hNU.trans (Submodule.map_subtype_le _ _))`. Break down `hUirr N' hN'U hN'st with h | h` into its components or cases. Use `left`. Rewrite using `[← hNe, h, Submodule.map_bot]`.

Use `right`. Rewrite using `[← hNe, h]`.
-/
theorem exists_irred_le_orbSpan {H V : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [AddCommGroup V]
    [Module ℂ V] (ρ : Representation ℂ H V) (B : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) (hh : ∀ u v, star (B u v) = B v u)
    (hp : ∀ v, 0 ≤ (B v v).re) (hd : ∀ v, B v v = 0 → v = 0) (hi : ∀ g u v, B (ρ g u) (ρ g v) = B u v)
    (hK0 : ∃ K : Subgroup H, IsOpen (K : Set H) ∧ IsCompact (K : Set H))
    (hsm : ∀ w, IsOpen {k : H | ρ k w = w})
    (hfd : ∀ K : Subgroup H, IsOpen (K : Set H) → FiniteDimensional ℂ (GlobalTheory.PRep.fixed ρ K))
    (y : V) (hy : y ≠ 0) :
    ∃ U : Submodule ℂ V, U ≠ ⊥ ∧ U ≤ (orbSpan ρ y).toSubmodule ∧ (∀ g, ∀ u ∈ U, ρ g u ∈ U) ∧
      (∀ N ≤ U, (∀ g, ∀ u ∈ N, ρ g u ∈ N) → N = ⊥ ∨ N = U) := by
  classical
  set O := orbSpan ρ y with hO
  let ρO := O.toRepresentation
  have hρO : ∀ g (w : O.toSubmodule), (ρO g w : V) = ρ g w := fun _ _ => rfl
  let BO : O.toSubmodule →ₗ⋆[ℂ] O.toSubmodule →ₗ[ℂ] ℂ := (B.comp O.toSubmodule.subtype).compl₂ O.toSubmodule.subtype
  have hBO : ∀ u w : O.toSubmodule, BO u w = B u w := fun _ _ => rfl
  have hsmO : ∀ w : O.toSubmodule, IsOpen {k : H | ρO k w = w} := by
    intro w
    convert hsm w.1 using 1
    ext k
    simp only [Set.mem_setOf_eq]
    exact ⟨fun h => by rw [← hρO, h], fun h => Subtype.ext (by rw [hρO, h])⟩
  have hfdO : ∀ K : Subgroup H, IsOpen (K : Set H) → FiniteDimensional ℂ (GlobalTheory.PRep.fixed ρO K) := by
    intro K hK
    haveI := hfd K hK
    have hle : (GlobalTheory.PRep.fixed ρO K).map O.toSubmodule.subtype ≤ GlobalTheory.PRep.fixed ρ K := by
      rintro _ ⟨w, hw, rfl⟩ k
      have h1 := hw k
      show ρ k w.1 = ((1 : K →* ℂˣ) k : ℂ) • w.1
      rw [MonoidHom.one_apply, Units.val_one, one_smul] at h1 ⊢
      rw [← hρO, h1]
    haveI : FiniteDimensional ℂ ((GlobalTheory.PRep.fixed ρO K).map O.toSubmodule.subtype) :=
      Submodule.finiteDimensional_of_le hle
    exact LinearEquiv.finiteDimensional
      (Submodule.equivMapOfInjective _ O.toSubmodule.injective_subtype _).symm
  have hy0 : (⟨y, mem_orbSpan ρ y⟩ : O.toSubmodule) ≠ 0 := fun h => hy (congrArg Subtype.val h)
  obtain ⟨U', P, hU0, hUst, hUirr, -, -, -⟩ :=
    GlobalTheory.AdmissibleProjection.exists_irreducible_equivariant_projection H O.toSubmodule ρO BO
      (fun u w => hh u w) (fun v => hp v) (fun v h => Subtype.ext (hd v h)) (fun g u w => hi g u w)
      hK0 hsmO hfdO _ hy0
  refine ⟨U'.map O.toSubmodule.subtype, ?_, ?_, ?_, ?_⟩
  · intro h
    apply hU0
    rw [Submodule.eq_bot_iff]
    intro u hu
    have : u.1 ∈ U'.map O.toSubmodule.subtype := ⟨u, hu, rfl⟩
    rw [h, Submodule.mem_bot] at this
    exact Subtype.ext this
  · rintro _ ⟨u, -, rfl⟩
    exact u.2
  · rintro g _ ⟨u, hu, rfl⟩
    exact ⟨ρO g u, hUst g u hu, rfl⟩
  · intro N hNU hN
    let N' : Submodule ℂ O.toSubmodule := N.comap O.toSubmodule.subtype
    have hN'U : N' ≤ U' := by
      intro u hu
      obtain ⟨w, hw, hwu⟩ := hNU hu
      rw [← Subtype.ext hwu]
      exact hw
    have hN'st : ∀ g, ∀ u ∈ N', ρO g u ∈ N' := fun g u hu => hN g u.1 hu
    have hNe : N'.map O.toSubmodule.subtype = N := by
      rw [Submodule.map_comap_subtype]
      exact inf_eq_right.2 (hNU.trans (Submodule.map_subtype_le _ _))
    rcases hUirr N' hN'U hN'st with h | h
    · left; rw [← hNe, h, Submodule.map_bot]
    · right; rw [← hNe, h]

end GlobalTheory.FrameAut.VecSemis

namespace GlobalTheory.FrameAut.VecSemis

open GlobalTheory.UnitarySemisimple GlobalTheory.DefU GlobalTheory.FrameAut.VecProj

/- English proof (translation)
Use `set T : Submodule ℂ (UA E n → ℂ) := ⨆ (π : Submodule ℂ (UA E n → ℂ)) (_ : IsAutRepU π ∧ ∃ f' : W →ₗ[ℂ] (UA E n → ℂ), f' ≠ 0 ∧ (∀ u, f' u ∈ π) ∧ ∀ (x : infU E n) u, f' (ρ x u) = RU E n x (f' u)), π ⊓ fixed (RF E n) K with hT`. Set `Y : Submodule ℂ (forms ρ)` to `{ carrier := {g | ∀ u, g.1 u ∈ T} add_mem' := fun ha hb u => by`. Rewrite using `[Submodule.coe_add, LinearMap.add_apply]`. Conclude with `add_mem (ha u) (hb u)`. Use the proof step `zero_mem' := fun u => by simp`.

Use the proof step `smul_mem' := fun c g hg u => by`. Rewrite using `[Submodule.coe_smul, LinearMap.smul_apply]`. Conclude with `T.smul_mem c (hg u) }`. Set `X` to `GlobalTheory.PRep.fixed (rep ρ) K`. Use `haveI : FiniteDimensional ℂ X := rep_fd ρ K hK`.

Use `haveI : FiniteDimensional ℂ (X ⊓ Y : Submodule ℂ (forms ρ)) := Submodule.finiteDimensional_of_le inf_le_left`. Set `Bf` to `form B ρ`. Establish `hBh` using `form_herm B hh ρ`. Establish `hBp` using `form_nonneg B hp ρ`. Establish `hBd` using `form_def B hh hp hd ρ`.

Establish `hBi` using `form_inv B hi ρ`. Establish `memX : ∀ g : forms ρ, (∀ k ∈ K, rep ρ k g = g) → g ∈ X`. Introduce `g hg k`. Use `show rep ρ k g = ((1 : K →* ℂˣ) k : ℂ) • g`. Rewrite using `[MonoidHom.one_apply, Units.val_one, one_smul]`.

Conclude with `hg k k.2`. Establish `ofX : ∀ g ∈ X, ∀ k ∈ K, rep ρ k g = g`. Introduce `g hg k hk`. Establish `h1` using `hg ⟨k, hk⟩`. Rewrite `h1` using `[MonoidHom.one_apply, Units.val_one, one_smul]`.

Conclude with `h1`. Establish `hfA : f ∈ forms ρ` using `⟨fun v => hfa v, hfe⟩`. Set `ff : forms ρ` to `⟨f, hfA⟩`. Establish `hffX : ff ∈ X`. Use `memX ff fun k hk => Subtype.ext (LinearMap.ext fun u => ?_)` and prove the remaining obligations.

Establish `h1` using `hfK u ⟨k, hk⟩`. Rewrite `h1` using `[MonoidHom.one_apply, Units.val_one, one_smul]`. Conclude with `h1`. It suffices to establish `hY : ff ∈ Y from hY`. Assume the negation of the conclusion as `hffY`.

Take `⟨m, hm, hmo⟩` from `exists_orth_proj Bf hBd (X ⊓ Y) ff`. Take `⟨y, hy⟩ : ∃ y, y = ff - m` from `⟨_, rfl⟩`. Establish `hyX : y ∈ X` using `hy ▸ sub_mem hffX (Submodule.mem_inf.1 hm).1`. Establish `hy0 : y ≠ 0`. Introduce `h`.

Apply `hffY` to reduce the goal to its premises. Rewrite `h` using `[hy, sub_eq_zero]`. Rewrite using `[h]`. Conclude with `(Submodule.mem_inf.1 hm).2`. Take `⟨U, hU0, hUO, hUst, hUirr⟩` from `exists_irred_le_orbSpan (rep ρ) Bf hBh hBp hBd hBi (GlobalTheory.T.definiteUnitaryFinitePoints_exists_openCompact E n) (rep_smooth ρ) (rep_fd ρ) y hy0`.

Establish `hadm` using `GlobalTheory.AdmissibleProjection.hadm_of (rep ρ) (GlobalTheory.T.definiteUnitaryFinitePoints_exists_openCompact E n) (rep_smooth ρ) (rep_fd ρ)`. Set `Z : Subrepresentation (rep ρ)` to `⟨U, fun g _ hv => hUst g _ hv⟩`. Take `⟨P, hP1, hP2, hP3⟩` from `GlobalTheory.AdmissibleProjection.exists_proj (rep ρ) Bf hBd hBi hadm Z`. Take `⟨z, hz⟩ : ∃ z, z = P y` from `⟨_, rfl⟩`. Establish `hzU : z ∈ U` using `hz ▸ hP1 y`.

Establish `hzX : z ∈ X` using `memX z fun k hk => by rw [hz, ← hP3, ofX y hyX k hk]`. Establish `hz0 : z ≠ 0`. Introduce `h0`. Apply `hU0` to reduce the goal to its premises. Establish `hyo : ∀ w ∈ Z.toSubmodule, Bf w y = 0`.

Introduce `w hw`. Use `hP2 y w hw` as an intermediate fact. Rewrite `this` using `[← hz, h0, sub_zero]`. Then use the resulting hypothesis. Rewrite using `[Submodule.eq_bot_iff]`. Introduce `w hw`.

Establish `hle : (orbSpan (rep ρ) y).toSubmodule ≤ LinearMap.ker (Bf w)`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨g, rfl⟩`. Conclude with `orth_stable (rep ρ) Bf hBi Z y hyo g w hw`. Conclude with `hBd _ (hle (hUO hw))`.

Set `M : Submodule ℂ (W →ₗ[ℂ] (UA E n → ℂ))` to `U.map (forms ρ).subtype`. Establish `hM0 : M ≠ ⊥`. Introduce `h`. Apply `hU0` to reduce the goal to its premises. Rewrite using `[Submodule.eq_bot_iff]`.

Introduce `u hu`. Establish `: u.1 ∈ M` using `⟨u, hu, rfl⟩`. Rewrite `this` using `[h, Submodule.mem_bot]`. Conclude with `Subtype.ext this`. Establish `hMf : ∀ g ∈ M, (∀ v, IsAutFormU (g v)) ∧ ∀ (x : infU E n) v, g (ρ x v) = RU E n x (g v)`.

Introduce and unpack `_ ⟨u, -, rfl⟩`. Conclude with `⟨fun v => u.2.1 v, u.2.2⟩`. Establish `hMk : ∀ k ∈ finU E n, ∀ g ∈ M, (RU E n k) ∘ₗ g ∈ M`. Introduce and unpack `k hk _ ⟨u, hu, rfl⟩`. Conclude with `⟨rep ρ ⟨k, hk⟩ u, hUst _ u hu, rfl⟩`.

Establish `hMirr : ∀ N ≤ M, (∀ k ∈ finU E n, ∀ g ∈ N, (RU E n k) ∘ₗ g ∈ N) → N = ⊥ ∨ N = M`. Introduce `N hNM hN`. Set `N' : Submodule ℂ (forms ρ)` to `N.comap (forms ρ).subtype`. Establish `hN'U : N' ≤ U`. Introduce `u hu`.

Take `⟨w, hw, hwu⟩` from `hNM hu`. Rewrite using `[← Subtype.ext hwu]`. Conclude with `hw`. Establish `hN'st : ∀ g, ∀ u ∈ N', rep ρ g u ∈ N'` using `fun g u hu => hN g.1 g.2 u.1 hu`. Establish `hNe : N'.map (forms ρ).subtype = N`.

Rewrite using `[Submodule.map_comap_subtype]`. Conclude with `inf_eq_right.2 (hNM.trans (Submodule.map_subtype_le _ _))`. Break down `hUirr N' hN'U hN'st with h | h` into its components or cases. Use `left`. Rewrite using `[← hNe, h, Submodule.map_bot]`.

Use `right`. Rewrite using `[← hNe, h]`. Establish `hπ` using `GlobalTheory.FrameAut.VecForms.isAutRepU_span_values E n W ρ hsp M hM0 hMf hMk hMirr`. Establish `hzY : z ∈ Y`. Introduce `u`.

Establish `hmemπ : z.1 u ∈ Submodule.span ℂ {φ | ∃ f ∈ M, ∃ v, f v = φ}` using `Submodule.subset_span ⟨z.1, ⟨z, hzU, rfl⟩, u, rfl⟩`. Establish `hfixu : z.1 u ∈ fixed (RF E n) K`. Introduce `k`. Rewrite using `[MonoidHom.one_apply, Units.val_one, one_smul]`. Establish `h1` using `congrArg (fun g : forms ρ => g.1 u) (ofX z hzX k k.2)`.

Conclude with `h1`. Establish `hidx : IsAutRepU (Submodule.span ℂ {φ | ∃ f ∈ M, ∃ v, f v = φ}) ∧ ∃ f' : W →ₗ[ℂ] (UA E n → ℂ), f' ≠ 0 ∧ (∀ u, f' u ∈ Submodule.span ℂ {φ | ∃ f ∈ M, ∃ v, f v = φ}) ∧ ∀ (x : infU E n) u, f' (ρ x u) = RU E n x (f' u)` using `⟨hπ, z.1, fun h => hz0 (Subtype.ext h), fun v => Submodule.subset_span ⟨z.1, ⟨z, hzU, rfl⟩, v, rfl⟩, z.2.2⟩`. Conclude with `(le_iSup₂ (f := fun (π : Submodule ℂ (UA E n → ℂ)) (_ : IsAutRepU π ∧ ∃ f' : W →ₗ[ℂ] (UA E n → ℂ), f' ≠ 0 ∧ (∀ u, f' u ∈ π) ∧ ∀ (x : infU E n) u, f' (ρ x u) = RU E n x (f' u)) => π ⊓ fixed (RF E n) K) _ hidx) ⟨hmemπ, hfixu⟩`. Establish `hzm : Bf z y = 0` using `hy ▸ hmo z ⟨hzX, hzY⟩`. Establish `hzz : Bf z z = 0`.

Establish `h2` using `hP2 y z hzU`. Rewrite `h2` using `[← hz, map_sub, hzm, zero_sub, neg_eq_zero]`. Conclude with `h2`. Conclude with `hz0 (hBd z hzz)`.
-/
theorem mem_iSup_of_form (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ)
    (B : autU E n →ₗ⋆[ℂ] autU E n →ₗ[ℂ] ℂ) (hh : ∀ u v, star (B u v) = B v u) (hp : ∀ v, 0 ≤ (B v v).re)
    (hd : ∀ v, B v v = 0 → v = 0) (hi : ∀ g u v, B (autRep E n g u) (autRep E n g v) = B u v)
    (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (ρ : Representation ℂ (infU E n) W)
    (hsp : Submodule.span ℂ (Set.range ρ) = ⊤) (K : Subgroup (finU E n)) (hK : IsOpen (K : Set (finU E n)))
    (f : W →ₗ[ℂ] (UA E n → ℂ)) (hfa : ∀ u, IsAutFormU (f u)) (hfe : ∀ (x : infU E n) u, f (ρ x u) = RU E n x (f u))
    (hfK : ∀ u, f u ∈ fixed (RF E n) K) :
    ∀ u, f u ∈ ⨆ (π : Submodule ℂ (UA E n → ℂ)) (_ : IsAutRepU π ∧ ∃ f' : W →ₗ[ℂ] (UA E n → ℂ), f' ≠ 0 ∧
      (∀ u, f' u ∈ π) ∧ ∀ (x : infU E n) u, f' (ρ x u) = RU E n x (f' u)), π ⊓ fixed (RF E n) K := by
  classical
  set T : Submodule ℂ (UA E n → ℂ) := ⨆ (π : Submodule ℂ (UA E n → ℂ)) (_ : IsAutRepU π ∧
    ∃ f' : W →ₗ[ℂ] (UA E n → ℂ), f' ≠ 0 ∧ (∀ u, f' u ∈ π) ∧ ∀ (x : infU E n) u, f' (ρ x u) = RU E n x (f' u)),
    π ⊓ fixed (RF E n) K with hT
  let Y : Submodule ℂ (forms ρ) :=
    { carrier := {g | ∀ u, g.1 u ∈ T}
      add_mem' := fun ha hb u => by
        rw [Submodule.coe_add, LinearMap.add_apply]; exact add_mem (ha u) (hb u)
      zero_mem' := fun u => by simp
      smul_mem' := fun c g hg u => by
        rw [Submodule.coe_smul, LinearMap.smul_apply]; exact T.smul_mem c (hg u) }
  let X := GlobalTheory.PRep.fixed (rep ρ) K
  haveI : FiniteDimensional ℂ X := rep_fd ρ K hK
  haveI : FiniteDimensional ℂ (X ⊓ Y : Submodule ℂ (forms ρ)) := Submodule.finiteDimensional_of_le inf_le_left
  let Bf := form B ρ
  have hBh := form_herm B hh ρ
  have hBp := form_nonneg B hp ρ
  have hBd := form_def B hh hp hd ρ
  have hBi := form_inv B hi ρ
  have memX : ∀ g : forms ρ, (∀ k ∈ K, rep ρ k g = g) → g ∈ X := by
    intro g hg k
    show rep ρ k g = ((1 : K →* ℂˣ) k : ℂ) • g
    rw [MonoidHom.one_apply, Units.val_one, one_smul]
    exact hg k k.2
  have ofX : ∀ g ∈ X, ∀ k ∈ K, rep ρ k g = g := by
    intro g hg k hk
    have h1 := hg ⟨k, hk⟩
    rw [MonoidHom.one_apply, Units.val_one, one_smul] at h1
    exact h1
  have hfA : f ∈ forms ρ := ⟨fun v => hfa v, hfe⟩
  let ff : forms ρ := ⟨f, hfA⟩
  have hffX : ff ∈ X := by
    refine memX ff fun k hk => Subtype.ext (LinearMap.ext fun u => ?_)
    have h1 := hfK u ⟨k, hk⟩
    rw [MonoidHom.one_apply, Units.val_one, one_smul] at h1
    exact h1
  suffices hY : ff ∈ Y from hY
  by_contra hffY
  obtain ⟨m, hm, hmo⟩ := exists_orth_proj Bf hBd (X ⊓ Y) ff
  obtain ⟨y, hy⟩ : ∃ y, y = ff - m := ⟨_, rfl⟩
  have hyX : y ∈ X := hy ▸ sub_mem hffX (Submodule.mem_inf.1 hm).1
  have hy0 : y ≠ 0 := by
    intro h
    apply hffY
    rw [hy, sub_eq_zero] at h
    rw [h]
    exact (Submodule.mem_inf.1 hm).2
  obtain ⟨U, hU0, hUO, hUst, hUirr⟩ := exists_irred_le_orbSpan (rep ρ) Bf hBh hBp hBd hBi (GlobalTheory.T.definiteUnitaryFinitePoints_exists_openCompact E n)
    (rep_smooth ρ) (rep_fd ρ) y hy0
  have hadm := GlobalTheory.AdmissibleProjection.hadm_of (rep ρ) (GlobalTheory.T.definiteUnitaryFinitePoints_exists_openCompact E n) (rep_smooth ρ) (rep_fd ρ)
  let Z : Subrepresentation (rep ρ) := ⟨U, fun g _ hv => hUst g _ hv⟩
  obtain ⟨P, hP1, hP2, hP3⟩ := GlobalTheory.AdmissibleProjection.exists_proj (rep ρ) Bf hBd hBi hadm Z
  obtain ⟨z, hz⟩ : ∃ z, z = P y := ⟨_, rfl⟩
  have hzU : z ∈ U := hz ▸ hP1 y
  have hzX : z ∈ X := memX z fun k hk => by rw [hz, ← hP3, ofX y hyX k hk]
  have hz0 : z ≠ 0 := by
    intro h0
    apply hU0
    have hyo : ∀ w ∈ Z.toSubmodule, Bf w y = 0 := by
      intro w hw
      have := hP2 y w hw
      rwa [← hz, h0, sub_zero] at this
    rw [Submodule.eq_bot_iff]
    intro w hw
    have hle : (orbSpan (rep ρ) y).toSubmodule ≤ LinearMap.ker (Bf w) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨g, rfl⟩
      exact orth_stable (rep ρ) Bf hBi Z y hyo g w hw
    exact hBd _ (hle (hUO hw))

  let M : Submodule ℂ (W →ₗ[ℂ] (UA E n → ℂ)) := U.map (forms ρ).subtype
  have hM0 : M ≠ ⊥ := by
    intro h
    apply hU0
    rw [Submodule.eq_bot_iff]
    intro u hu
    have : u.1 ∈ M := ⟨u, hu, rfl⟩
    rw [h, Submodule.mem_bot] at this
    exact Subtype.ext this
  have hMf : ∀ g ∈ M, (∀ v, IsAutFormU (g v)) ∧ ∀ (x : infU E n) v, g (ρ x v) = RU E n x (g v) := by
    rintro _ ⟨u, -, rfl⟩
    exact ⟨fun v => u.2.1 v, u.2.2⟩
  have hMk : ∀ k ∈ finU E n, ∀ g ∈ M, (RU E n k) ∘ₗ g ∈ M := by
    rintro k hk _ ⟨u, hu, rfl⟩
    exact ⟨rep ρ ⟨k, hk⟩ u, hUst _ u hu, rfl⟩
  have hMirr : ∀ N ≤ M, (∀ k ∈ finU E n, ∀ g ∈ N, (RU E n k) ∘ₗ g ∈ N) → N = ⊥ ∨ N = M := by
    intro N hNM hN
    let N' : Submodule ℂ (forms ρ) := N.comap (forms ρ).subtype
    have hN'U : N' ≤ U := by
      intro u hu
      obtain ⟨w, hw, hwu⟩ := hNM hu
      rw [← Subtype.ext hwu]
      exact hw
    have hN'st : ∀ g, ∀ u ∈ N', rep ρ g u ∈ N' := fun g u hu => hN g.1 g.2 u.1 hu
    have hNe : N'.map (forms ρ).subtype = N := by
      rw [Submodule.map_comap_subtype]
      exact inf_eq_right.2 (hNM.trans (Submodule.map_subtype_le _ _))
    rcases hUirr N' hN'U hN'st with h | h
    · left; rw [← hNe, h, Submodule.map_bot]
    · right; rw [← hNe, h]
  have hπ := GlobalTheory.FrameAut.VecForms.isAutRepU_span_values E n W ρ hsp M hM0 hMf hMk hMirr
  have hzY : z ∈ Y := by
    intro u
    have hmemπ : z.1 u ∈ Submodule.span ℂ {φ | ∃ f ∈ M, ∃ v, f v = φ} :=
      Submodule.subset_span ⟨z.1, ⟨z, hzU, rfl⟩, u, rfl⟩
    have hfixu : z.1 u ∈ fixed (RF E n) K := by
      intro k
      rw [MonoidHom.one_apply, Units.val_one, one_smul]
      have h1 := congrArg (fun g : forms ρ => g.1 u) (ofX z hzX k k.2)
      exact h1
    have hidx : IsAutRepU (Submodule.span ℂ {φ | ∃ f ∈ M, ∃ v, f v = φ}) ∧
        ∃ f' : W →ₗ[ℂ] (UA E n → ℂ), f' ≠ 0 ∧ (∀ u, f' u ∈ Submodule.span ℂ {φ | ∃ f ∈ M, ∃ v, f v = φ}) ∧
          ∀ (x : infU E n) u, f' (ρ x u) = RU E n x (f' u) :=
      ⟨hπ, z.1, fun h => hz0 (Subtype.ext h), fun v => Submodule.subset_span ⟨z.1, ⟨z, hzU, rfl⟩, v, rfl⟩, z.2.2⟩
    exact (le_iSup₂ (f := fun (π : Submodule ℂ (UA E n → ℂ)) (_ : IsAutRepU π ∧
      ∃ f' : W →ₗ[ℂ] (UA E n → ℂ), f' ≠ 0 ∧ (∀ u, f' u ∈ π) ∧ ∀ (x : infU E n) u, f' (ρ x u) = RU E n x (f' u)) =>
      π ⊓ fixed (RF E n) K) _ hidx) ⟨hmemπ, hfixu⟩
  have hzm : Bf z y = 0 := hy ▸ hmo z ⟨hzX, hzY⟩
  have hzz : Bf z z = 0 := by
    have h2 := hP2 y z hzU
    rw [← hz, map_sub, hzm, zero_sub, neg_eq_zero] at h2
    exact h2
  exact hz0 (hBd z hzz)

end GlobalTheory.FrameAut.VecSemis

namespace GlobalTheory.FrameAut.VecSemis

open GlobalTheory.DefU

/- English proof (translation)
Introduce `E _ _ _ n W _ _ _ ρ hsp K hK f hfa hfe hfK`. Take `⟨B, hh, hp, hd, hi⟩` from `GlobalTheory.T.exists_invariant_positive_petersson_form E n`. Conclude with `mem_iSup_of_form E n B hh hp hd hi W ρ hsp K hK f hfa hfe hfK`.
-/
theorem mem_iSup_fixed_autRep : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (ρ : Representation ℂ (infU E n) W), Submodule.span ℂ (Set.range ρ) = ⊤ → ∀ (K : Subgroup (finU E n)), IsOpen (K : Set (finU E n)) → ∀ f : W →ₗ[ℂ] (UA E n → ℂ), (∀ u, IsAutFormU (f u)) → (∀ (x : infU E n) u, f (ρ x u) = RU E n x (f u)) → (∀ u, f u ∈ fixed (RF E n) K) → ∀ u, f u ∈ ⨆ (π : Submodule ℂ (UA E n → ℂ)) (_ : IsAutRepU π ∧ ∃ f' : W →ₗ[ℂ] (UA E n → ℂ), f' ≠ 0 ∧ (∀ u, f' u ∈ π) ∧ ∀ (x : infU E n) u, f' (ρ x u) = RU E n x (f' u)), π ⊓ fixed (RF E n) K := by
  intro E _ _ _ n W _ _ _ ρ hsp K hK f hfa hfe hfK
  obtain ⟨B, hh, hp, hd, hi⟩ := GlobalTheory.T.exists_invariant_positive_petersson_form E n
  exact mem_iSup_of_form E n B hh hp hd hi W ρ hsp K hK f hfa hfe hfK

end GlobalTheory.FrameAut.VecSemis
