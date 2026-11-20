import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMaxThOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemFinPt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TruncMatTranspose
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactOrbitSmoothVectorFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLatLevel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeLevelCompactStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeLevelOpenNbhdStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeLevelPreservesLatticeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizedDataPlacesUnramifiedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizedDataOpenNbhdStatement

noncomputable section

namespace GlobalTheory.ThKLevelEx

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

/- English proof (translation)
Proceed by induction on `S using Finset.induction_on with`. Consider the case `empty`. Establish `: GlobalTheory.TruncFix.truncU (∅ : Finset (Pl F)) l = 1`. Use `Subtype.ext (Units.ext ?_)` and prove the remaining obligations. Use `show GlobalTheory.TruncFix.truncMat (GlobalTheory.TruncFix.idem ∅) (mat l) = 1`.

Simplify using `[GlobalTheory.TruncFix.truncMat, GlobalTheory.TruncFix.idem]`. Rewrite using `[this]`. Conclude with `Subgroup.one_mem _`. Consider the case `insert v S hv ih`. Rewrite using `[GlobalTheory.TruncFix.truncU_insert hv]`.

Conclude with `Subgroup.mul_mem _ (Subgroup.subset_closure (Set.mem_iUnion.2 ⟨v, GlobalTheory.TruncFix.truncU_mem_UAt v l⟩)) ih`.
-/
theorem truncU_mem_closure {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {d : ℕ} (W : Spc F E d) (S : Finset (Pl F)) (l : UA σ W.J) :
    GlobalTheory.TruncFix.truncU S l ∈ Subgroup.closure (⋃ v : Pl F, UAt σ W (GlobalTheory.AdelicU.evFin F v)) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    have : GlobalTheory.TruncFix.truncU (∅ : Finset (Pl F)) l = 1 := by
      refine Subtype.ext (Units.ext ?_)
      show GlobalTheory.TruncFix.truncMat (GlobalTheory.TruncFix.idem ∅) (mat l) = 1
      simp [GlobalTheory.TruncFix.truncMat, GlobalTheory.TruncFix.idem]
    rw [this]; exact Subgroup.one_mem _
  | insert v S hv ih =>
    rw [GlobalTheory.TruncFix.truncU_insert hv]
    exact Subgroup.mul_mem _ (Subgroup.subset_closure (Set.mem_iUnion.2 ⟨v, GlobalTheory.TruncFix.truncU_mem_UAt v l⟩)) ih

/- English proof (translation)
Introduce `hKP F E _ _ _ _ _ σ B a a' G X om om' R Rf hM Φ hΦ`. Establish `hT` using `hM.triple`. Establish `hlat` using `hT.geo.hW.lat`. Set `K` to `GlobalTheory.ThKLevel.latLevel σ G.W`. Establish `hKc : IsCompact (K : Set (UA σ G.W.J))` using `GlobalTheory.T.lattice_level_compact F E σ (a + a') G.W hlat`.

Take `⟨U₁, hU₁o, hU₁1, hU₁⟩` from `GlobalTheory.T.lattice_level_open_nbhd F E σ (a + a') G.W hlat`. Establish `hKfin : (K : Set (UA σ G.W.J)) ⊆ GlobalTheory.ThKAdm.FinPt σ G.W` using `GlobalTheory.ThKLevel.latLevel_le G.W`. Establish `hKlat : ∀ k ∈ K, ∀ (w : Pl F) (γ : Matrix (Fin a) (Fin (a + a')) (AE F E)) (γ' : Matrix (Fin a') (Fin (a + a')) (AE F E)), (γ * Matrix.transpose (mat k) ∈ latAtV G.V G.W w ↔ γ ∈ latAtV G.V G.W w) ∧ (γ' * Matrix.transpose (mat k) ∈ latAtV G.V' G.W w ↔ γ' ∈ latAtV G.V' G.W w)` using `fun k hk w γ γ' => ⟨GlobalTheory.T.lattice_level_preserves_lattice F E σ a (a + a') G.V G.W k hk w γ, GlobalTheory.T.lattice_level_preserves_lattice F E σ a' (a + a') G.V' G.W k hk w γ'⟩`. Establish `smooth : ∀ Ψ ∈ GlobalTheory.ThK.PolData B G.M', ∃ U ∈ nhds (1 : UA σ G.W.J), ∀ h ∈ U, h ∈ K → om' (1, h) Ψ = Ψ`. Introduce `Ψ hΨ`.

Take `⟨S₁, hS₁⟩` from `GlobalTheory.T.polarized_data_places_unramified hKP F E σ B a a' G X om om' hT Ψ hΨ`. Take `⟨U, hU, hUΨ⟩` from `GlobalTheory.T.polarized_data_open_nbhd hKP F E σ B a a' G X om om' hT Ψ hΨ S₁`. Conclude with `⟨U, hU, fun h hh hK => (hS₁ S₁ le_rfl h (hKfin hK) (hKlat h hK)).trans (hUΨ h hh)⟩`. Establish `hΦP : Φ ∈ GlobalTheory.ThK.PolData B G.M'` using `(Submodule.mem_inf.1 hΦ).1`. Take `⟨U₂, hU₂, hU₂Φ⟩` from `smooth Φ hΦP`.

Set `L : Subgroup (UA σ G.W.J)` to `{ carrier := {h | h ∈ K ∧ om' (1, h) Φ = Φ} mul_mem' := by`. Introduce and unpack `x y ⟨hx, hxΦ⟩ ⟨hy, hyΦ⟩`. Use `⟨K.mul_mem hx hy, ?_⟩` and prove the remaining obligations. Rewrite using `[show ((1 : UA σ G.V'.J), x * y) = (1, x) * (1, y) by simp, map_mul, Module.End.mul_apply, hyΦ, hxΦ]`. Use the proof step `one_mem' := ⟨K.one_mem, by`.

Rewrite using `[show ((1 : UA σ G.V'.J), (1 : UA σ G.W.J)) = 1 from rfl, map_one, Module.End.one_apply]⟩`. Use the proof step `inv_mem' := by`. Introduce and unpack `x ⟨hx, hxΦ⟩`. Use `⟨K.inv_mem hx, ?_⟩` and prove the remaining obligations. Establish `h1 : om' (1, x⁻¹) (om' (1, x) Φ) = Φ`.

Rewrite using `[← Module.End.mul_apply, ← map_mul, show ((1 : UA σ G.V'.J), x⁻¹) * (1, x) = 1 by simp, map_one, Module.End.one_apply]`. Rewrite `h1` using `[hxΦ]`. Conclude with `h1 }`. Use `⟨L, ⟨fun h hh => hKfin hh.1, U₁ ∩ interior U₂, hU₁o.inter isOpen_interior, ⟨hU₁1, mem_interior_iff_mem_nhds.2 hU₂⟩, fun h ⟨⟨hh1, hh2⟩, hhf⟩ => ?_⟩, fun l hl => hl.2, fun Ψ hΨ => ?_⟩` and prove the remaining obligations. Establish `hK : h ∈ K` using `hU₁ ⟨hh1, hhf⟩`.

Conclude with `⟨hK, hU₂Φ h (interior_subset hh2) hK⟩`. Establish `hΨP : Ψ ∈ GlobalTheory.ThK.PolData B G.M'` using `(Submodule.mem_inf.1 hΨ).1`. Take `⟨S₁, hS₁⟩` from `GlobalTheory.T.polarized_data_places_unramified hKP F E σ B a a' G X om om' hT Ψ hΨP`. Establish `hfin` using `GlobalTheory.finite_orbit_of_fixed_near_one (om'.comp (MonoidHom.inr _ _)) K hKc Ψ (smooth Ψ hΨP)`. Use `choose k hk hkΨ using fun y : hfin.toFinset => (hfin.mem_toFinset.1 y.2)`.

Use `⟨Finset.univ.image fun y : hfin.toFinset => GlobalTheory.TruncFix.truncU S₁ (k y), fun g hg => ?_, fun l hl => ?_⟩` and prove the remaining obligations. Take `⟨y, -, rfl⟩` from `Finset.mem_image.1 hg`. Conclude with `truncU_mem_closure G.W S₁ (k y)`. Establish `hy : om' (1, l) Ψ ∈ hfin.toFinset` using `hfin.mem_toFinset.2 ⟨l, hl.1, rfl⟩`. Use `⟨GlobalTheory.TruncFix.truncU S₁ (k ⟨_, hy⟩), Finset.mem_image.2 ⟨⟨_, hy⟩, Finset.mem_univ _, rfl⟩, ?_⟩` and prove the remaining obligations.

Rewrite using `[← hS₁ S₁ le_rfl _ (hKfin (hk _)) (hKlat _ (hk _))]`. Conclude with `(hkΨ ⟨_, hy⟩).symm`.
-/
theorem levelEx : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched B G X om om' R Rf → ∀ Φ ∈ (GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁), ∃ L : Subgroup (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ G.W.J), GlobalTheory.ThKAdm.IsLevel G.W L ∧ (∀ l ∈ L, om' (1, l) Φ = Φ) ∧ ∀ Ψ ∈ (GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁), ∃ s : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ G.W.J), (∀ g ∈ s, g ∈ Subgroup.closure (⋃ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ G.W (GlobalTheory.AdelicU.evFin F v))) ∧ ∀ l ∈ L, ∃ g ∈ s, om' (1, l) Ψ = om' (1, g) Ψ := by
  intro hKP F E _ _ _ _ _ σ B a a' G X om om' R Rf hM Φ hΦ
  classical
  have hT := hM.triple
  have hlat := hT.geo.hW.lat
  let K := GlobalTheory.ThKLevel.latLevel σ G.W
  have hKc : IsCompact (K : Set (UA σ G.W.J)) := GlobalTheory.T.lattice_level_compact F E σ (a + a') G.W hlat
  obtain ⟨U₁, hU₁o, hU₁1, hU₁⟩ := GlobalTheory.T.lattice_level_open_nbhd F E σ (a + a') G.W hlat
  have hKfin : (K : Set (UA σ G.W.J)) ⊆ GlobalTheory.ThKAdm.FinPt σ G.W := GlobalTheory.ThKLevel.latLevel_le G.W
  have hKlat : ∀ k ∈ K, ∀ (w : Pl F) (γ : Matrix (Fin a) (Fin (a + a')) (AE F E))
      (γ' : Matrix (Fin a') (Fin (a + a')) (AE F E)),
      (γ * Matrix.transpose (mat k) ∈ latAtV G.V G.W w ↔ γ ∈ latAtV G.V G.W w) ∧
      (γ' * Matrix.transpose (mat k) ∈ latAtV G.V' G.W w ↔ γ' ∈ latAtV G.V' G.W w) := fun k hk w γ γ' =>
    ⟨GlobalTheory.T.lattice_level_preserves_lattice F E σ a (a + a') G.V G.W k hk w γ, GlobalTheory.T.lattice_level_preserves_lattice F E σ a' (a + a') G.V' G.W k hk w γ'⟩
  have smooth : ∀ Ψ ∈ GlobalTheory.ThK.PolData B G.M', ∃ U ∈ nhds (1 : UA σ G.W.J), ∀ h ∈ U, h ∈ K → om' (1, h) Ψ = Ψ := by
    intro Ψ hΨ
    obtain ⟨S₁, hS₁⟩ := GlobalTheory.T.polarized_data_places_unramified hKP F E σ B a a' G X om om' hT Ψ hΨ
    obtain ⟨U, hU, hUΨ⟩ := GlobalTheory.T.polarized_data_open_nbhd hKP F E σ B a a' G X om om' hT Ψ hΨ S₁
    exact ⟨U, hU, fun h hh hK => (hS₁ S₁ le_rfl h (hKfin hK) (hKlat h hK)).trans (hUΨ h hh)⟩
  have hΦP : Φ ∈ GlobalTheory.ThK.PolData B G.M' := (Submodule.mem_inf.1 hΦ).1
  obtain ⟨U₂, hU₂, hU₂Φ⟩ := smooth Φ hΦP
  let L : Subgroup (UA σ G.W.J) :=
    { carrier := {h | h ∈ K ∧ om' (1, h) Φ = Φ}
      mul_mem' := by
        rintro x y ⟨hx, hxΦ⟩ ⟨hy, hyΦ⟩
        refine ⟨K.mul_mem hx hy, ?_⟩
        rw [show ((1 : UA σ G.V'.J), x * y) = (1, x) * (1, y) by simp, map_mul, Module.End.mul_apply, hyΦ, hxΦ]
      one_mem' := ⟨K.one_mem, by
        rw [show ((1 : UA σ G.V'.J), (1 : UA σ G.W.J)) = 1 from rfl, map_one, Module.End.one_apply]⟩
      inv_mem' := by
        rintro x ⟨hx, hxΦ⟩
        refine ⟨K.inv_mem hx, ?_⟩
        have h1 : om' (1, x⁻¹) (om' (1, x) Φ) = Φ := by
          rw [← Module.End.mul_apply, ← map_mul, show ((1 : UA σ G.V'.J), x⁻¹) * (1, x) = 1 by simp, map_one,
            Module.End.one_apply]
        rw [hxΦ] at h1
        exact h1 }
  refine ⟨L, ⟨fun h hh => hKfin hh.1, U₁ ∩ interior U₂, hU₁o.inter isOpen_interior,
    ⟨hU₁1, mem_interior_iff_mem_nhds.2 hU₂⟩, fun h ⟨⟨hh1, hh2⟩, hhf⟩ => ?_⟩, fun l hl => hl.2, fun Ψ hΨ => ?_⟩
  · have hK : h ∈ K := hU₁ ⟨hh1, hhf⟩
    exact ⟨hK, hU₂Φ h (interior_subset hh2) hK⟩
  · have hΨP : Ψ ∈ GlobalTheory.ThK.PolData B G.M' := (Submodule.mem_inf.1 hΨ).1
    obtain ⟨S₁, hS₁⟩ := GlobalTheory.T.polarized_data_places_unramified hKP F E σ B a a' G X om om' hT Ψ hΨP
    have hfin := GlobalTheory.finite_orbit_of_fixed_near_one (om'.comp (MonoidHom.inr _ _)) K hKc Ψ (smooth Ψ hΨP)
    choose k hk hkΨ using fun y : hfin.toFinset => (hfin.mem_toFinset.1 y.2)
    refine ⟨Finset.univ.image fun y : hfin.toFinset => GlobalTheory.TruncFix.truncU S₁ (k y), fun g hg => ?_, fun l hl => ?_⟩
    · obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 hg
      exact truncU_mem_closure G.W S₁ (k y)
    · have hy : om' (1, l) Ψ ∈ hfin.toFinset := hfin.mem_toFinset.2 ⟨l, hl.1, rfl⟩
      refine ⟨GlobalTheory.TruncFix.truncU S₁ (k ⟨_, hy⟩), Finset.mem_image.2 ⟨⟨_, hy⟩, Finset.mem_univ _, rfl⟩, ?_⟩
      rw [← hS₁ S₁ le_rfl _ (hKfin (hk _)) (hKlat _ (hk _))]
      exact (hkΨ ⟨_, hy⟩).symm

end GlobalTheory.ThKLevelEx

end
