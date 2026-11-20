import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRk
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatLocalApproximationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnramifiedLinearBarDualStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRankCoinvariantInducedIsoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InducedFullRankIrreducibleStatement

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.IrrCoinvSmall

/- English proof (translation)
Introduce `hP k _ _ _ _ n d ν hnd hs hu N hA hNF hN`. Take `⟨Z, hZ1, hZ2, hZ3, hZ4⟩` from `GlobalTheory.T.full_rank_coinvariant_induced_iso k n d ν hnd hs`. Break down `GlobalTheory.T.induced_full_rank_irreducible hP k n d ν hnd hs hu (N.map Z) (by rintro _ ⟨Ψ, hΨ, rfl⟩; exact hZ1 Ψ (hNF hΨ)) (by` into its components or cases. Introduce and unpack `_ ⟨Ψ, hΨ, rfl⟩ h₀`. Conclude with `⟨_, hN h₀ Ψ hΨ, hZ4 Ψ (hNF hΨ) h₀⟩) with hE | hE`.

Use `left`. Use `le_antisymm (fun Ψ hΨ => hZ3 Ψ (hNF hΨ) ?_) hA` and prove the remaining obligations. Establish `: Z Ψ ∈ N.map Z` using `⟨Ψ, hΨ, rfl⟩`. Rewrite `this` using `[hE]`. Conclude with `(Submodule.mem_bot ℂ).1 this`.

Use `right`. Use `le_antisymm hNF (fun Ψ hΨ => ?_)` and prove the remaining obligations. Establish `: Z Ψ ∈ N.map Z` using `hE ▸ hZ1 Ψ hΨ`. Take `⟨Ψ', hΨ', he⟩` from `this`. Establish `h1 : Ψ - Ψ' ∈ GlobalTheory.FullRankCoinv.augRk n d ν` using `hZ3 _ (Submodule.sub_mem _ hΨ (hNF hΨ')) (by simp [map_sub, he])`.

Use `N.add_mem hΨ' (hA h1)` as an intermediate fact. Rewrite `this` using `[add_sub_cancel]`. Then use the resulting hypothesis.
-/
theorem fullRk_irred : GlobalTheory.FunPr.Hypotheses₂ → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n d : ℕ) (ν : kˣ →* ℂˣ), n ≤ d → GlobalTheory.SmGL.IsSmoothChar ν → GlobalTheory.SmGL.IsUnitaryChar ν →
    ∀ N : Submodule ℂ (Matrix (Fin n) (Fin d) k → ℂ), GlobalTheory.FullRankCoinv.augRk n d ν ≤ N →
      N ≤ GlobalTheory.FullRankCoinv.fullRk k n d → (∀ h : GL (Fin d) k, ∀ Ψ ∈ N, (fun Y => Ψ (Y * h.1)) ∈ N) →
      N = GlobalTheory.FullRankCoinv.augRk n d ν ∨ N = GlobalTheory.FullRankCoinv.fullRk k n d := by
  intro hP k _ _ _ _ n d ν hnd hs hu N hA hNF hN
  obtain ⟨Z, hZ1, hZ2, hZ3, hZ4⟩ := GlobalTheory.T.full_rank_coinvariant_induced_iso k n d ν hnd hs
  rcases GlobalTheory.T.induced_full_rank_irreducible hP k n d ν hnd hs hu (N.map Z) (by rintro _ ⟨Ψ, hΨ, rfl⟩; exact hZ1 Ψ (hNF hΨ)) (by
    rintro _ ⟨Ψ, hΨ, rfl⟩ h₀; exact ⟨_, hN h₀ Ψ hΨ, hZ4 Ψ (hNF hΨ) h₀⟩) with hE | hE
  · left
    refine le_antisymm (fun Ψ hΨ => hZ3 Ψ (hNF hΨ) ?_) hA
    have : Z Ψ ∈ N.map Z := ⟨Ψ, hΨ, rfl⟩
    rw [hE] at this
    exact (Submodule.mem_bot ℂ).1 this
  · right
    refine le_antisymm hNF (fun Ψ hΨ => ?_)
    have : Z Ψ ∈ N.map Z := hE ▸ hZ1 Ψ hΨ
    obtain ⟨Ψ', hΨ', he⟩ := this
    have h1 : Ψ - Ψ' ∈ GlobalTheory.FullRankCoinv.augRk n d ν :=
      hZ3 _ (Submodule.sub_mem _ hΨ (hNF hΨ')) (by simp [map_sub, he])
    have := N.add_mem hΨ' (hA h1)
    rwa [add_sub_cancel] at this

/- English proof (translation)
Introduce `hP F E _ _ _ _ _ σ B a a' G X om om' hT v hv hν N hAN hNS hN`. Take `⟨t, ι, ν₀, hs, hu, hbij, hso, hg, hh⟩` from `GlobalTheory.T.exists_unramified_linear_bar_dual hP F E σ B a a' G X om om' hT v hv`. Establish `hR` using `GlobalTheory.T.schwartz_bruhat_local_approximation hP F E σ B a a' G X om om' hT v hv hν t`. Establish `haugSB : augAt om' v ≤ SB _` using `Submodule.span_le.2 (by`. Introduce and unpack `_ ⟨g, -, φ, hφ, φ₁, hφ₁, -, rfl⟩`.

Conclude with `Submodule.sub_mem _ hφ₁ hφ)`. Establish `hgen : GlobalTheory.FullRankCoinv.augRk a' (a + a') ν₀ ≤ (augAt om' v).map ι ⊓ GlobalTheory.FullRankCoinv.fullRk (Fv F v) a' (a + a')`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨g₀, Ψ, hΨ, rfl⟩`. Take `⟨φ, hφ, rfl⟩` from `hbij.surjOn hΨ.1`.

Take `⟨g, hgU, hg'⟩` from `hg g₀`. Take `⟨φ₁, hφ₁, hA, he⟩` from `hg' φ hφ`. Use `⟨⟨φ₁ - φ, Submodule.subset_span ⟨g, hgU, φ, hφ, φ₁, hφ₁, hA, rfl⟩, by simp [map_sub, he]⟩, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← he]`. Conclude with `Submodule.sub_mem _ (hbij.mapsTo hφ₁) hΨ.1`.

Introduce `Y hY`. Rewrite using `[← he]`. Use `show ι φ₁ Y - ι φ Y = 0`. Rewrite using `[he, hΨ.2 Y hY]`. Simplify using `only [GlobalTheory.FullRankCoinv.lact, sub_zero]`.

Rewrite using `[hΨ.2 _ (by rwa [Matrix.rank_mul_eq_right_of_isUnit_det _ _ (by`. Rewrite using `[Matrix.det_transpose]`. Conclude with `(Matrix.GeneralLinearGroup.det g₀).isUnit)]), mul_zero]`. Use `set N' := N.map ι ⊓ GlobalTheory.FullRankCoinv.fullRk (Fv F v) a' (a + a') with hN'`. Establish `hA' : GlobalTheory.FullRankCoinv.augRk a' (a + a') ν₀ ≤ N'` using `hgen.trans (inf_le_inf_right _ (Submodule.map_mono hAN))`.

Establish `hst : ∀ h₀ : GL (Fin (a + a')) (Fv F v), ∀ Ψ ∈ N', (fun Y => Ψ (Y * h₀.1)) ∈ N'`. Introduce and unpack `h₀ _ ⟨⟨φ, hφN, rfl⟩, hΨ⟩`. Take `⟨h, hhU, c, hc, hh'⟩` from `hh h₀`. Take `⟨φ₁, hφ₁, hA, he⟩` from `hh' φ (hNS hφN)`. Establish `h1 : (fun Y => ι φ (Y * h₀.1)) = c⁻¹ • ι φ₁`.

Rewrite using `[he]`. Use function extensionality and compare the values at `Y`. Simplify using `[hc]`. Use `⟨⟨c⁻¹ • φ₁, N.smul_mem _ (hN h hhU φ hφN φ₁ hφ₁ hA), by rw [map_smul, h1]⟩, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[h1]`.

Conclude with `Submodule.smul_mem _ _ (hbij.mapsTo hφ₁)`. Introduce `Y hY`. Conclude with `hΨ.2 _ (by rwa [Matrix.rank_mul_eq_left_of_isUnit_det _ _ (Matrix.GeneralLinearGroup.det h₀).isUnit])`. Establish `hinj : ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), ∀ φ' ∈ SB (Fin a' × Fin (a + a') → Fv F v), ι φ = ι φ' → φ = φ'` using `fun φ hφ φ' hφ' e => hbij.injOn hφ hφ' e`. Establish `hloc : ∀ φ₀ ∈ G.M'.SoLoc B.ψ t, ι φ₀ ∈ GlobalTheory.FullRankCoinv.fullRk (Fv F v) a' (a + a')` using `fun φ₀ h0 => ⟨hbij.mapsTo h0.1, (hso φ₀ h0.1).1 h0⟩`.

Break down `fullRk_irred hP (Fv F v) a' (a + a') ν₀ (by omega) hs hu N' hA' inf_le_right hst with hE | hE` into its components or cases. Use `left`. Use `le_antisymm (fun φ hφN => ?_) hAN` and prove the remaining obligations. Take `⟨φ₀, h0, hd⟩` from `hR φ (hNS hφN)`. Establish `h0N : φ₀ ∈ N`.

Use `N.sub_mem hφN (hAN hd)` as an intermediate fact. Rewrite `this` using `[sub_sub_cancel]`. Then use the resulting hypothesis. Establish `h1 : ι φ₀ ∈ GlobalTheory.FullRankCoinv.augRk a' (a + a') ν₀` using `hE ▸ ⟨⟨φ₀, h0N, rfl⟩, hloc φ₀ h0⟩`. Take `⟨⟨w, hw, hwe⟩, -⟩` from `hgen h1`. Establish `: w = φ₀` using `hinj w (haugSB hw) φ₀ h0.1 hwe`.

Substitute `this` using the available equality. Use `(augAt om' v).add_mem hw hd` as an intermediate fact. Rewrite `this` using `[add_sub_cancel]`. Then use the resulting hypothesis. Use `right`. Use `le_antisymm hNS (fun φ hφ => ?_)` and prove the remaining obligations.

Take `⟨φ₀, h0, hd⟩` from `hR φ hφ`. Establish `h1 : ι φ₀ ∈ N'` using `hE ▸ hloc φ₀ h0`. Take `⟨⟨φ', hφ'N, he⟩, -⟩` from `h1`. Establish `: φ' = φ₀` using `hinj φ' (hNS hφ'N) φ₀ h0.1 he`. Substitute `this` using the available equality.

Use `N.add_mem hφ'N (hAN hd)` as an intermediate fact. Rewrite `this` using `[add_sub_cancel]`. Then use the resulting hypothesis.
-/
theorem irr_small : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → ∀ v, X.Good v → (∀ (t : E →ₐ[F] Fv F v) (k : ℤ), k ≠ 0 → chrW X.ν t (unifAt v) ^ k ≠ 1) →
    ∀ N : Submodule ℂ ((Fin a' × Fin (a + a') → Fv F v) → ℂ), augAt om' v ≤ N → N ≤ SB _ →
      (∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ N, ∀ φ₁ ∈ SB _, Acts (evFin F v) (om' (1, h)) φ φ₁ → φ₁ ∈ N) →
      N = augAt om' v ∨ N = SB _ := by
  intro hP F E _ _ _ _ _ σ B a a' G X om om' hT v hv hν N hAN hNS hN
  obtain ⟨t, ι, ν₀, hs, hu, hbij, hso, hg, hh⟩ := GlobalTheory.T.exists_unramified_linear_bar_dual hP F E σ B a a' G X om om' hT v hv
  have hR := GlobalTheory.T.schwartz_bruhat_local_approximation hP F E σ B a a' G X om om' hT v hv hν t
  have haugSB : augAt om' v ≤ SB _ := Submodule.span_le.2 (by
    rintro _ ⟨g, -, φ, hφ, φ₁, hφ₁, -, rfl⟩
    exact Submodule.sub_mem _ hφ₁ hφ)

  have hgen : GlobalTheory.FullRankCoinv.augRk a' (a + a') ν₀ ≤
      (augAt om' v).map ι ⊓ GlobalTheory.FullRankCoinv.fullRk (Fv F v) a' (a + a') := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨g₀, Ψ, hΨ, rfl⟩
    obtain ⟨φ, hφ, rfl⟩ := hbij.surjOn hΨ.1
    obtain ⟨g, hgU, hg'⟩ := hg g₀
    obtain ⟨φ₁, hφ₁, hA, he⟩ := hg' φ hφ
    refine ⟨⟨φ₁ - φ, Submodule.subset_span ⟨g, hgU, φ, hφ, φ₁, hφ₁, hA, rfl⟩, by simp [map_sub, he]⟩, ?_, ?_⟩
    · rw [← he]
      exact Submodule.sub_mem _ (hbij.mapsTo hφ₁) hΨ.1
    · intro Y hY
      rw [← he]
      show ι φ₁ Y - ι φ Y = 0
      rw [he, hΨ.2 Y hY]
      simp only [GlobalTheory.FullRankCoinv.lact, sub_zero]
      rw [hΨ.2 _ (by rwa [Matrix.rank_mul_eq_right_of_isUnit_det _ _ (by
        rw [Matrix.det_transpose]; exact (Matrix.GeneralLinearGroup.det g₀).isUnit)]), mul_zero]
  set N' := N.map ι ⊓ GlobalTheory.FullRankCoinv.fullRk (Fv F v) a' (a + a') with hN'
  have hA' : GlobalTheory.FullRankCoinv.augRk a' (a + a') ν₀ ≤ N' :=
    hgen.trans (inf_le_inf_right _ (Submodule.map_mono hAN))
  have hst : ∀ h₀ : GL (Fin (a + a')) (Fv F v), ∀ Ψ ∈ N', (fun Y => Ψ (Y * h₀.1)) ∈ N' := by
    rintro h₀ _ ⟨⟨φ, hφN, rfl⟩, hΨ⟩
    obtain ⟨h, hhU, c, hc, hh'⟩ := hh h₀
    obtain ⟨φ₁, hφ₁, hA, he⟩ := hh' φ (hNS hφN)
    have h1 : (fun Y => ι φ (Y * h₀.1)) = c⁻¹ • ι φ₁ := by
      rw [he]; funext Y; simp [hc]
    refine ⟨⟨c⁻¹ • φ₁, N.smul_mem _ (hN h hhU φ hφN φ₁ hφ₁ hA), by rw [map_smul, h1]⟩, ?_, ?_⟩
    · rw [h1]; exact Submodule.smul_mem _ _ (hbij.mapsTo hφ₁)
    · intro Y hY
      exact hΨ.2 _ (by rwa [Matrix.rank_mul_eq_left_of_isUnit_det _ _ (Matrix.GeneralLinearGroup.det h₀).isUnit])
  have hinj : ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), ∀ φ' ∈ SB (Fin a' × Fin (a + a') → Fv F v),
      ι φ = ι φ' → φ = φ' := fun φ hφ φ' hφ' e => hbij.injOn hφ hφ' e
  have hloc : ∀ φ₀ ∈ G.M'.SoLoc B.ψ t, ι φ₀ ∈ GlobalTheory.FullRankCoinv.fullRk (Fv F v) a' (a + a') :=
    fun φ₀ h0 => ⟨hbij.mapsTo h0.1, (hso φ₀ h0.1).1 h0⟩
  rcases fullRk_irred hP (Fv F v) a' (a + a') ν₀ (by omega) hs hu N' hA' inf_le_right hst with hE | hE
  · left
    refine le_antisymm (fun φ hφN => ?_) hAN
    obtain ⟨φ₀, h0, hd⟩ := hR φ (hNS hφN)
    have h0N : φ₀ ∈ N := by
      have := N.sub_mem hφN (hAN hd); rwa [sub_sub_cancel] at this
    have h1 : ι φ₀ ∈ GlobalTheory.FullRankCoinv.augRk a' (a + a') ν₀ := hE ▸ ⟨⟨φ₀, h0N, rfl⟩, hloc φ₀ h0⟩
    obtain ⟨⟨w, hw, hwe⟩, -⟩ := hgen h1
    have : w = φ₀ := hinj w (haugSB hw) φ₀ h0.1 hwe
    subst this
    have := (augAt om' v).add_mem hw hd
    rwa [add_sub_cancel] at this
  · right
    refine le_antisymm hNS (fun φ hφ => ?_)
    obtain ⟨φ₀, h0, hd⟩ := hR φ hφ
    have h1 : ι φ₀ ∈ N' := hE ▸ hloc φ₀ h0
    obtain ⟨⟨φ', hφ'N, he⟩, -⟩ := h1
    have : φ' = φ₀ := hinj φ' (hNS hφ'N) φ₀ h0.1 he
    subst this
    have := N.add_mem hφ'N (hAN hd)
    rwa [add_sub_cancel] at this

end GlobalTheory.IrrCoinvSmall
