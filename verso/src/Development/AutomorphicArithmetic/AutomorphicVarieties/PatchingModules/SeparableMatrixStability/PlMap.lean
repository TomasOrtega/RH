import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.MapEta
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.PlProps
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ResMap

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

/- English proof (translation)
Introduce `l _ Γ Γ' _ _ _ _ _ _ _ _ _ _ f H _ hH hf hsurj`. Establish `hH' : IsOpen ((H.comap f : Subgroup Γ) : Set Γ)` using `hH.preimage hf`. Use `haveI : CompactSpace H := isCompact_iff_compactSpace.mp (Subgroup.isClosed_of_isOpen H hH).isCompact`. Use `haveI : CompactSpace (H.comap f) := isCompact_iff_compactSpace.mp (Subgroup.isClosed_of_isOpen _ hH').isCompact`. Set `g : (H.comap f) →* H` to `f.subgroupComap H`.

Establish `hg : Continuous g` using `(hf.comp continuous_subtype_val).subtype_mk _`. Establish `hgs : Function.Surjective g`. Introduce and unpack `⟨y, hy⟩`. Take `⟨x, rfl⟩` from `hsurj y`. Conclude with `⟨⟨x, hy⟩, rfl⟩`.

Establish `hcomp : f.comp (H.comap f).subtype = H.subtype.comp g`. Use extensionality with `x`. Both sides reduce to the same expression. Rewrite using `[(pl_props l Γ (H.comap f) hH').2.2.2.2.2, (pl_props l Γ' H hH).2.2.2.2.2]`. Unfold `proLResOf`.

Rewrite using `[Subgroup.map_map, hcomp, ← Subgroup.map_map, proLRes_map l _ _ g hg hgs]`.
-/
theorem UpperTheory.V.Pa.pl_map :
    ∀ (l : ℕ) [Fact l.Prime] (Γ Γ' : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ] [Group Γ'] [TopologicalSpace Γ'] [IsTopologicalGroup Γ'] [CompactSpace Γ'] [TotallyDisconnectedSpace Γ'] (f : Γ →* Γ') (H : Subgroup Γ') [H.Normal], IsOpen (H : Set Γ') → Continuous f → Function.Surjective f → (PL l (H.comap f)).map f = PL l H := by
  intro l _ Γ Γ' _ _ _ _ _ _ _ _ _ _ f H _ hH hf hsurj
  have hH' : IsOpen ((H.comap f : Subgroup Γ) : Set Γ) := hH.preimage hf
  haveI : CompactSpace H :=
    isCompact_iff_compactSpace.mp (Subgroup.isClosed_of_isOpen H hH).isCompact
  haveI : CompactSpace (H.comap f) :=
    isCompact_iff_compactSpace.mp (Subgroup.isClosed_of_isOpen _ hH').isCompact
  let g : (H.comap f) →* H := f.subgroupComap H
  have hg : Continuous g := (hf.comp continuous_subtype_val).subtype_mk _
  have hgs : Function.Surjective g := by
    rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := hsurj y
    exact ⟨⟨x, hy⟩, rfl⟩
  have hcomp : f.comp (H.comap f).subtype = H.subtype.comp g := by
    ext x
    rfl
  rw [(pl_props l Γ (H.comap f) hH').2.2.2.2.2, (pl_props l Γ' H hH).2.2.2.2.2]
  unfold proLResOf
  rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, proLRes_map l _ _ g hg hgs]
