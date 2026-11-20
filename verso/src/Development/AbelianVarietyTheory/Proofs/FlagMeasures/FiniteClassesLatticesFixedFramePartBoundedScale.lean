import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.HermitianLattices.FinalNeighbourConstruct
import Formalism.HermitianLattices.HermitianLatticesProofs.ClassSetAssembly
import Formalism.HermitianLattices.HermitianLatticesProofs.GenusCovolBound
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LocClosed
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteIsometryClassesDefiniteHermitianBoundedScaStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteLatticesBetweenOfSmulLeStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsComplHermitianOrthogonalOfTotallyPositiveStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIsometryExtendOrthogonalByIdentityStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsLatticeComapSubspaceRingOfIntegersStatement
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LatClassFin

/- English proof (translation)
Use `haveI := isNoetherian_of_fg_of_noetherian L hL`. Establish `h1` using `IsNoetherian.noetherian (N.comap L.subtype)`. Establish `e : (N.comap L.subtype).map L.subtype = N`. Rewrite using `[Submodule.map_comap_subtype, inf_of_le_right h]`. Rewrite using `[← e]`.

Conclude with `h1.map _`.
-/
theorem fg_of_le_fg {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module (𝓞 K) V]
    {N L : Submodule (𝓞 K) V} (hL : L.FG) (h : N ≤ L) : N.FG := by
  haveI := isNoetherian_of_fg_of_noetherian L hL
  have h1 := IsNoetherian.noetherian (N.comap L.subtype)
  have e : (N.comap L.subtype).map L.subtype = N := by
    rw [Submodule.map_comap_subtype, inf_of_le_right h]
  rw [← e]; exact h1.map _

/- English proof (translation)
Proceed by induction on `a using Fin.lastCases with`. Consider the case `last => show Fin.snoc (α := fun _ => S.V) F.fl.e F.fl.z (Fin.last r) ∈ F.fl.X ⊔ E ∙ F.fl.z`. Rewrite using `[Fin.snoc_last]`. Conclude with `Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)`. Consider the case `cast i => show Fin.snoc (α := fun _ => S.V) F.fl.e F.fl.z (Fin.castSucc i) ∈ F.fl.X ⊔ E ∙ F.fl.z`.

Rewrite using `[Fin.snoc_castSucc]`. Conclude with `Submodule.mem_sup_left (Submodule.subset_span ⟨i, rfl⟩)`.
-/
theorem frame_mem_Xplus {E : Type} [Field E] [NumberField E] [StarRing E] {S : Formalism.BasicNotions.HSpace E}
    {r : ℕ} {T : E} (F : LFlag S r T) (a : Fin (r + 1)) : frame F a ∈ Xplus F := by
  induction a using Fin.lastCases with
  | last =>
    show Fin.snoc (α := fun _ => S.V) F.fl.e F.fl.z (Fin.last r) ∈ F.fl.X ⊔ E ∙ F.fl.z
    rw [Fin.snoc_last]
    exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  | cast i =>
    show Fin.snoc (α := fun _ => S.V) F.fl.e F.fl.z (Fin.castSucc i) ∈ F.fl.X ⊔ E ∙ F.fl.z
    rw [Fin.snoc_castSucc]
    exact Submodule.mem_sup_left (Submodule.subset_span ⟨i, rfl⟩)

/- English proof (translation)
Introduce `D T T' F F' hpos A N d c hN hd hc`. Use `set U : Submodule D.host.E (VS D).V := Xplus F ⊔ Xplus F' with hUdef`. Use `set W : Submodule D.host.E (VS D).V := orth (VS D) U with hWdef`. Establish `hcompl : IsCompl U W` using `GlobalTheory.T.isCompl_hermitianOrthogonal_of_totallyPositive (VS D) U hpos`. Set `hW : ↥W →ₗ⋆[D.host.E] ↥W →ₗ[D.host.E] D.host.E` to `(VS D).hT.domRestrict₁₂ W W`.

Establish `hWs : hW.IsSymm` using `(VS D).herm.domRestrict W`. Establish `hWp : ∀ x : ↥W, x ≠ 0 → 0 < Algebra.trace ℚ D.host.E (hW x x)` using `fun x hx => hpos x.1 x.2 (fun h => hx (Subtype.ext h))`. Take `⟨s, hslat, hs⟩` from `GlobalTheory.T.finite_isometryClasses_definiteHermitian_boundedScale hW hWs hWp d c hd hc`. Set `ι : ↥W →ₗ[𝓞 D.host.E] (VS D).V` to `W.subtype.restrictScalars (𝓞 D.host.E)`. Set `Mof : Submodule (𝓞 D.host.E) ↥W → LV D` to `fun L => A ⊔ L.map ι`.

Set `Sset : Set (LV D)` to `⋃ L ∈ s, {Λ' | A.FG ∧ L.FG ∧ Mof L ≤ Λ' ∧ ∀ x ∈ Λ', (N : D.host.E) • x ∈ Mof L}`. Establish `hfin : Sset.Finite`. Use `Set.Finite.biUnion s.finite_toSet fun L _ => ?_` and prove the remaining obligations. Distinguish the cases in `hA : A.FG`. Distinguish the cases in `hL : L.FG`.

Use `(GlobalTheory.T.finite_lattices_between_of_smul_le' (Mof L) (hA.sup (hL.map ι)) N hN).subset ?_` and prove the remaining obligations. Introduce and unpack `Λ' ⟨-, -, h1, h2⟩`. Conclude with `⟨h1, h2⟩`. Conclude with `Set.finite_empty.subset (by rintro Λ' ⟨-, h, -⟩; exact absurd h hL)`. Conclude with `Set.finite_empty.subset (by rintro Λ' ⟨h, -⟩; exact absurd h hA)`.

Use `⟨hfin.toFinset, fun Λ hΛ hAΛ hNΛ hdΛ hcΛ => ?_⟩` and prove the remaining obligations. Use `set L' : Submodule (𝓞 D.host.E) ↥W := Λ.comap ι with hL'`. Establish `hL'lat : Submodule.IsLattice D.host.E L'` using `GlobalTheory.T.isLattice_comap_subspace_ringOfIntegers Λ hΛ W`. Establish `hsc : ∀ x ∈ L', ∀ y ∈ L', (d : D.host.E) * hW x y ∈ Set.range (algebraMap (𝓞 D.host.E) D.host.E)` using `fun x hx y hy => hdΛ x.1 hx y.1 hy`. Establish `hdu : ∀ y : ↥W, (∀ x ∈ L', hW x y ∈ Set.range (algebraMap (𝓞 D.host.E) D.host.E)) → (c : D.host.E) • y ∈ L'`.

Introduce `y hy`. Use `show (c : D.host.E) • (y : (VS D).V) ∈ Λ`. Conclude with `hcΛ y.1 y.2 (fun x hx => hy ⟨x, hx.2⟩ hx.1)`. Take `⟨M₀, hM₀s, g, hg, hgM⟩` from `hs L' hL'lat hsc hdu`. Establish `hgiso : ∀ x y : ↥W, (VS D).hT (g x : (VS D).V) (g y : (VS D).V) = (VS D).hT (x : (VS D).V) (y : (VS D).V)` using `fun x y => hg x y`.

Take `⟨γ, hγi, hγU, hγW⟩` from `GlobalTheory.T.exists_isometry_extend_orthogonal_by_identity (VS D) U hcompl g hgiso`. Establish `hγH : γ ∈ H0 F F'` using `⟨hγi, fun a => hγU _ (Submodule.mem_sup_left (frame_mem_Xplus F a)), fun a => hγU _ (Submodule.mem_sup_right (frame_mem_Xplus F' a))⟩`. Establish `hmem : ∀ x, x ∈ Formalism.HermitianLatticesTheory.gmap γ⁻¹ Λ ↔ γ x ∈ Λ` using `fun x => by`. Rewrite using `[Formalism.HermitianLatticesTheory.isomAct_mem_gmap]`. Both sides reduce to the same expression.

Establish `hAsub : ∀ a ∈ A, a ∈ Λ ∧ a ∈ U` using `fun a ha => by`. Rewrite `ha` using `[← hAΛ]`. Conclude with `⟨ha.1, ha.2⟩`. Use `⟨Formalism.HermitianLatticesTheory.gmap γ⁻¹ Λ, ?_, γ, hγH, by simpa using Formalism.HermitianLatticesTheory.genusBasic_gmap_inv γ⁻¹ Λ⟩` and prove the remaining obligations. Rewrite using `[Set.Finite.mem_toFinset]`.

Establish `hAfg : A.FG`. Rewrite using `[← hAΛ]`. Conclude with `fg_of_le_fg hΛ.fg inf_le_left`. Establish `hWsymm : ∀ w (hw : w ∈ W) (hwΛ : w ∈ Λ), γ.symm w ∈ M₀.map ι`. Introduce `w hw hwΛ`.

Establish `h1 : (⟨w, hw⟩ : ↥W) ∈ Formalism.HermitianLatticesTheory.gmap g M₀` using `by rw [hgM]; exact hwΛ`. Rewrite `h1` using `[Formalism.HermitianLatticesTheory.isomAct_mem_gmap]`. Use `⟨_, h1, ?_⟩` and prove the remaining obligations. Rewrite using `[LinearEquiv.eq_symm_apply]`. Use `show γ ((g.symm ⟨w, hw⟩ : ↥W) : (VS D).V) = w`.

Rewrite using `[hγW, LinearEquiv.apply_symm_apply]`. Use `Set.mem_biUnion hM₀s ⟨hAfg, (hslat M₀ hM₀s).fg, ?_, ?_⟩` and prove the remaining obligations. Use `sup_le (fun a ha => ?_) ?_` and prove the remaining obligations. Rewrite using `[hmem, hγU a (hAsub a ha).2]`. Conclude with `(hAsub a ha).1`.

Introduce and unpack `_ ⟨m, hm, rfl⟩`. Rewrite using `[hmem]`. Use `show γ ((m : ↥W) : (VS D).V) ∈ Λ`. Rewrite using `[hγW]`. Establish `h1 : g m ∈ Formalism.HermitianLatticesTheory.gmap g M₀`.

Rewrite using `[Formalism.HermitianLatticesTheory.isomAct_mem_gmap, LinearEquiv.symm_apply_apply]`. Conclude with `hm`. Rewrite `h1` using `[hgM]`. Conclude with `h1`. Introduce `x hx`.

Rewrite `hx` using `[hmem]`. Take `⟨u, hu, w, hw, huw⟩` from `Submodule.mem_sup.mp (hNΛ _ hx)`. Establish `hx' : (N : D.host.E) • x = γ.symm u + γ.symm w`. Rewrite using `[← map_add, huw, map_smul, LinearEquiv.symm_apply_apply]`. Establish `hu' : γ.symm u = u`.

Rewrite using `[LinearEquiv.symm_apply_eq]`. Conclude with `(hγU u hu.2).symm`. Rewrite using `[hx', hu']`. Use `Submodule.add_mem_sup ?_ (hWsymm w hw.2 hw.1)` and prove the remaining obligations. Rewrite using `[← hAΛ]`.

Conclude with `hu`.
-/
theorem classes_fin : ∀ (D : D7) {T T' : D.host.E} (F : LFlag (VS D) D.R.rS T) (F' : LFlag (VS D) D.R.rS T'), (∀ x ∈ orth (VS D) (Xplus F ⊔ Xplus F'), x ≠ 0 → 0 < Algebra.trace ℚ D.host.E ((VS D).hT x x)) → ∀ (A : LV D) (N d c : ℕ), 0 < N → 0 < d → 0 < c → ∃ S : Finset (LV D), ∀ Λ : LV D, Submodule.IsLattice D.host.E Λ → Λ ⊓ toO (VS D) (Xplus F ⊔ Xplus F') = A → (∀ x ∈ Λ, (N : D.host.E) • x ∈ Λ ⊓ toO (VS D) (Xplus F ⊔ Xplus F') ⊔ Λ ⊓ toO (VS D) (orth (VS D) (Xplus F ⊔ Xplus F'))) → (∀ x ∈ Λ, ∀ y ∈ Λ, (d : D.host.E) * (VS D).hT x y ∈ Set.range (algebraMap (𝓞 D.host.E) D.host.E)) → (∀ y ∈ orth (VS D) (Xplus F ⊔ Xplus F'), (∀ x ∈ Λ ⊓ toO (VS D) (orth (VS D) (Xplus F ⊔ Xplus F')), (VS D).hT x y ∈ Set.range (algebraMap (𝓞 D.host.E) D.host.E)) → (c : D.host.E) • y ∈ Λ) → ∃ Λs ∈ S, ∃ γ ∈ H0 F F', Formalism.HermitianLatticesTheory.gmap γ Λs = Λ := by
  intro D T T' F F' hpos A N d c hN hd hc
  classical
  set U : Submodule D.host.E (VS D).V := Xplus F ⊔ Xplus F' with hUdef
  set W : Submodule D.host.E (VS D).V := orth (VS D) U with hWdef
  have hcompl : IsCompl U W := GlobalTheory.T.isCompl_hermitianOrthogonal_of_totallyPositive (VS D) U hpos
  let hW : ↥W →ₗ⋆[D.host.E] ↥W →ₗ[D.host.E] D.host.E := (VS D).hT.domRestrict₁₂ W W
  have hWs : hW.IsSymm := (VS D).herm.domRestrict W
  have hWp : ∀ x : ↥W, x ≠ 0 → 0 < Algebra.trace ℚ D.host.E (hW x x) := fun x hx =>
    hpos x.1 x.2 (fun h => hx (Subtype.ext h))
  obtain ⟨s, hslat, hs⟩ := GlobalTheory.T.finite_isometryClasses_definiteHermitian_boundedScale hW hWs hWp d c hd hc
  let ι : ↥W →ₗ[𝓞 D.host.E] (VS D).V := W.subtype.restrictScalars (𝓞 D.host.E)
  let Mof : Submodule (𝓞 D.host.E) ↥W → LV D := fun L => A ⊔ L.map ι
  let Sset : Set (LV D) :=
    ⋃ L ∈ s, {Λ' | A.FG ∧ L.FG ∧ Mof L ≤ Λ' ∧ ∀ x ∈ Λ', (N : D.host.E) • x ∈ Mof L}
  have hfin : Sset.Finite := by
    refine Set.Finite.biUnion s.finite_toSet fun L _ => ?_
    by_cases hA : A.FG
    · by_cases hL : L.FG
      · refine (GlobalTheory.T.finite_lattices_between_of_smul_le' (Mof L) (hA.sup (hL.map ι)) N hN).subset ?_
        rintro Λ' ⟨-, -, h1, h2⟩
        exact ⟨h1, h2⟩
      · exact Set.finite_empty.subset (by rintro Λ' ⟨-, h, -⟩; exact absurd h hL)
    · exact Set.finite_empty.subset (by rintro Λ' ⟨h, -⟩; exact absurd h hA)
  refine ⟨hfin.toFinset, fun Λ hΛ hAΛ hNΛ hdΛ hcΛ => ?_⟩
  set L' : Submodule (𝓞 D.host.E) ↥W := Λ.comap ι with hL'
  have hL'lat : Submodule.IsLattice D.host.E L' := GlobalTheory.T.isLattice_comap_subspace_ringOfIntegers Λ hΛ W
  have hsc : ∀ x ∈ L', ∀ y ∈ L', (d : D.host.E) * hW x y ∈ Set.range (algebraMap (𝓞 D.host.E) D.host.E) :=
    fun x hx y hy => hdΛ x.1 hx y.1 hy
  have hdu : ∀ y : ↥W, (∀ x ∈ L', hW x y ∈ Set.range (algebraMap (𝓞 D.host.E) D.host.E)) →
      (c : D.host.E) • y ∈ L' := by
    intro y hy
    show (c : D.host.E) • (y : (VS D).V) ∈ Λ
    exact hcΛ y.1 y.2 (fun x hx => hy ⟨x, hx.2⟩ hx.1)
  obtain ⟨M₀, hM₀s, g, hg, hgM⟩ := hs L' hL'lat hsc hdu
  have hgiso : ∀ x y : ↥W, (VS D).hT (g x : (VS D).V) (g y : (VS D).V) = (VS D).hT (x : (VS D).V) (y : (VS D).V) :=
    fun x y => hg x y
  obtain ⟨γ, hγi, hγU, hγW⟩ := GlobalTheory.T.exists_isometry_extend_orthogonal_by_identity (VS D) U hcompl g hgiso
  have hγH : γ ∈ H0 F F' :=
    ⟨hγi, fun a => hγU _ (Submodule.mem_sup_left (frame_mem_Xplus F a)),
      fun a => hγU _ (Submodule.mem_sup_right (frame_mem_Xplus F' a))⟩
  have hmem : ∀ x, x ∈ Formalism.HermitianLatticesTheory.gmap γ⁻¹ Λ ↔ γ x ∈ Λ := fun x => by
    rw [Formalism.HermitianLatticesTheory.isomAct_mem_gmap]; rfl
  have hAsub : ∀ a ∈ A, a ∈ Λ ∧ a ∈ U := fun a ha => by
    rw [← hAΛ] at ha; exact ⟨ha.1, ha.2⟩
  refine ⟨Formalism.HermitianLatticesTheory.gmap γ⁻¹ Λ, ?_, γ, hγH, by simpa using Formalism.HermitianLatticesTheory.genusBasic_gmap_inv γ⁻¹ Λ⟩
  rw [Set.Finite.mem_toFinset]
  have hAfg : A.FG := by
    rw [← hAΛ]; exact fg_of_le_fg hΛ.fg inf_le_left
  have hWsymm : ∀ w (hw : w ∈ W) (hwΛ : w ∈ Λ), γ.symm w ∈ M₀.map ι := by
    intro w hw hwΛ
    have h1 : (⟨w, hw⟩ : ↥W) ∈ Formalism.HermitianLatticesTheory.gmap g M₀ := by rw [hgM]; exact hwΛ
    rw [Formalism.HermitianLatticesTheory.isomAct_mem_gmap] at h1
    refine ⟨_, h1, ?_⟩
    rw [LinearEquiv.eq_symm_apply]
    show γ ((g.symm ⟨w, hw⟩ : ↥W) : (VS D).V) = w
    rw [hγW, LinearEquiv.apply_symm_apply]
  refine Set.mem_biUnion hM₀s ⟨hAfg, (hslat M₀ hM₀s).fg, ?_, ?_⟩
  · refine sup_le (fun a ha => ?_) ?_
    · rw [hmem, hγU a (hAsub a ha).2]; exact (hAsub a ha).1
    · rintro _ ⟨m, hm, rfl⟩
      rw [hmem]
      show γ ((m : ↥W) : (VS D).V) ∈ Λ
      rw [hγW]
      have h1 : g m ∈ Formalism.HermitianLatticesTheory.gmap g M₀ := by
        rw [Formalism.HermitianLatticesTheory.isomAct_mem_gmap, LinearEquiv.symm_apply_apply]; exact hm
      rw [hgM] at h1
      exact h1
  · intro x hx
    rw [hmem] at hx
    obtain ⟨u, hu, w, hw, huw⟩ := Submodule.mem_sup.mp (hNΛ _ hx)
    have hx' : (N : D.host.E) • x = γ.symm u + γ.symm w := by
      rw [← map_add, huw, map_smul, LinearEquiv.symm_apply_apply]
    have hu' : γ.symm u = u := by
      rw [LinearEquiv.symm_apply_eq]; exact (hγU u hu.2).symm
    rw [hx', hu']
    refine Submodule.add_mem_sup ?_ (hWsymm w hw.2 hw.1)
    rw [← hAΛ]; exact hu

end GlobalTheory.LatClassFin
