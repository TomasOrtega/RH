import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EpsVEqOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsHeisenbergCombinationSplitPlaceDatum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalSchrodingerModelUniqTransportExists
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergFrameHalfInverse
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlatPlace GlobalTheory.LocMod GlobalTheory.SplitWeil

noncomputable section

namespace GlobalTheory.FlatPlace.CombAll

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']

/- English proof (translation)
Use `set N : Matrix (Fin S.rank) (Fin T.rank) k := (y.map fun a => p.π (cA D a)).transpose with hN`. Establish `hyN : y = N.transpose.map fun a => cA D (p.ι a)`. Use extensionality with `i j`. Simplify using `only [hN, Matrix.transpose_transpose, Matrix.map_apply, p.ι_π, map_mul, Formalism.L2.Theta.cA_cA]`. Conclude with `(hy i j).symm`.

Use `⟨(FS.γ * ((S.gram⁻¹).map (p.π.comp (incA D)) * N * T.gram.map (p.π.comp (incA D))) * FT.β).transpose, fun t => ?_⟩` and prove the remaining obligations. Rewrite using `[hyN, GlobalTheory.LocSympl.pi_hO_up]`. Rewrite using `[show (S.gram⁻¹).map (p.π.comp (incA D)) * N * T.gram.map (p.π.comp (incA D)) * (FT.β * t * FS.γ) = ((S.gram⁻¹).map (p.π.comp (incA D)) * N * T.gram.map (p.π.comp (incA D)) * FT.β * t) * FS.γ by`. Simplify using `only [Matrix.mul_assoc], Matrix.trace_mul_comm]`. Rewrite using `[show FS.γ * ((S.gram⁻¹).map (p.π.comp (incA D)) * N * T.gram.map (p.π.comp (incA D)) * FT.β * t) = (FS.γ * ((S.gram⁻¹).map (p.π.comp (incA D)) * N * T.gram.map (p.π.comp (incA D))) * FT.β) * t by`.

Simplify using `only [Matrix.mul_assoc]]`. Simplify using `only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply]`. Conclude with `Finset.sum_comm`.
-/
theorem exists_form (p : Place D k) {S T : HSp D} (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) {y : WO S T}
    (hy : IsHalf (cA D p.e) y) : ∃ b : Matrix Y Y' k, ∀ t, p.π (hO S T (p.up FS FT t) y) = ∑ r, ∑ q, b r q * t r q := by
  set N : Matrix (Fin S.rank) (Fin T.rank) k := (y.map fun a => p.π (cA D a)).transpose with hN
  have hyN : y = N.transpose.map fun a => cA D (p.ι a) := by
    ext i j
    simp only [hN, Matrix.transpose_transpose, Matrix.map_apply, p.ι_π, map_mul, Formalism.L2.Theta.cA_cA]
    exact (hy i j).symm
  refine ⟨(FS.γ * ((S.gram⁻¹).map (p.π.comp (incA D)) * N * T.gram.map (p.π.comp (incA D))) * FT.β).transpose, fun t => ?_⟩
  rw [hyN, GlobalTheory.LocSympl.pi_hO_up]
  rw [show (S.gram⁻¹).map (p.π.comp (incA D)) * N * T.gram.map (p.π.comp (incA D)) * (FT.β * t * FS.γ) =
      ((S.gram⁻¹).map (p.π.comp (incA D)) * N * T.gram.map (p.π.comp (incA D)) * FT.β * t) * FS.γ by
    simp only [Matrix.mul_assoc], Matrix.trace_mul_comm]
  rw [show FS.γ * ((S.gram⁻¹).map (p.π.comp (incA D)) * N * T.gram.map (p.π.comp (incA D)) * FT.β * t) =
      (FS.γ * ((S.gram⁻¹).map (p.π.comp (incA D)) * N * T.gram.map (p.π.comp (incA D))) * FT.β) * t by
    simp only [Matrix.mul_assoc]]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply]
  exact Finset.sum_comm

/- English proof (translation)
Take `⟨⟨ψk, hψk⟩, hcn, -, -, -⟩` from `GlobalTheory.LocChar.weil_char_split D k p ψ hψ`. Take `⟨hcont, hne⟩` from `hcn ψk hψk`. Take `⟨d, hd⟩` from `exists_hasConductor_of_continuous ψk hcont hne`. Establish `h1` using `p.split.1`. Establish `h1' : cA D p.e * cA D p.e = cA D p.e` using `by rw [← map_mul, h1]`.

Use `set x := p.down FS FT u with hx`. Use `set y : WO S T := cA D p.e • u with hyd`. Establish `hy : IsHalf (cA D p.e) y` using `fun i j => by`. Simplify using `only [hyd, Matrix.smul_apply, smul_eq_mul]`. Rewrite using `[← mul_assoc, h1']`.

Establish `hux : p.up FS FT x = p.e • u`. Rewrite using `[hx]`. Unfold `Place.down Place.up`. Rewrite using `[← Matrix.mul_assoc, ← Matrix.mul_assoc, FT.βγ, Matrix.one_mul, Matrix.mul_assoc, FS.βγ, Matrix.mul_one]`. Use extensionality with `i j`.

Simplify using `only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]`. Conclude with `p.ι_π _`. Establish `hsum : y + p.up FS FT x = u`. Rewrite using `[hux]`. Use extensionality with `i j`.

Simplify using `only [hyd, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]`. Rewrite using `[← add_mul, add_comm]`. Conclude with `hu i j`. Take `⟨b, hb⟩` from `exists_form p FS FT hy`. Set `Φx : SB (Matrix Y Y' k)` to `⟨fun t => O.1 (t + x), GlobalTheory.LocComb.trans_mem_SB O.2 x⟩`.

Set `Φm : SB (Matrix Y Y' k)` to `⟨fun t => GlobalTheory.LocMod.Inhab.pairing ψk t b * Φx.1 t, GlobalTheory.LocComb.modul_mem_SB hd Φx.2 b⟩`. Use `⟨ψ (-symplOH S T y (p.up FS FT x)) • Φm, fun Tm h => ?_⟩` and prove the remaining obligations. Establish `e1 : Tm Φx = heisO ψ S T (p.up FS FT x) (Tm O)` using `h.trans x O Φx fun _ => rfl`. Establish `e2 : Tm Φm = heisO ψ S T y (Tm Φx)` using `h.modul y hy Φx Φm fun t => by show GlobalTheory.LocMod.Inhab.pairing ψk t b * Φx.1 t = _`. Rewrite using `[GlobalTheory.LocSympl.psi_sympl_up p FS FT ψ ψk hψk t y, hb t]`.

Both sides reduce to the same expression. Establish `e3` using `GlobalTheory.PlaceModel.heisL_heisL S T ψ y (p.up FS FT x) (Tm O)`. Express the relevant statement in the definitionally equal form `heisO ψ S T y (heisO ψ S T (p.up FS FT x) (Tm O)) = ψ (symplOH S T y (p.up FS FT x)) • heisO ψ S T (y + p.up FS FT x) (Tm O) at e3`. Rewrite using `[map_smul, e2, e1, e3, smul_smul, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one, one_smul, hsum]`.
-/
theorem exists_heis (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) {S T : HSp D}
    (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (O : SB (Matrix Y Y' k)) {u : WO S T}
    (hu : IsHalf (p.e + cA D p.e) u) :
    ∃ Φ : SB (Matrix Y Y' k), ∀ Tm, p.IsModel ψ FS FT Tm → Tm Φ = heisO ψ S T u (Tm O) := by
  obtain ⟨⟨ψk, hψk⟩, hcn, -, -, -⟩ := GlobalTheory.LocChar.weil_char_split D k p ψ hψ
  obtain ⟨hcont, hne⟩ := hcn ψk hψk
  obtain ⟨d, hd⟩ := exists_hasConductor_of_continuous ψk hcont hne
  have h1 := p.split.1
  have h1' : cA D p.e * cA D p.e = cA D p.e := by rw [← map_mul, h1]
  set x := p.down FS FT u with hx
  set y : WO S T := cA D p.e • u with hyd
  have hy : IsHalf (cA D p.e) y := fun i j => by
    simp only [hyd, Matrix.smul_apply, smul_eq_mul]
    rw [← mul_assoc, h1']
  have hux : p.up FS FT x = p.e • u := by
    rw [hx]
    unfold Place.down Place.up
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, FT.βγ, Matrix.one_mul, Matrix.mul_assoc, FS.βγ, Matrix.mul_one]
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]
    exact p.ι_π _
  have hsum : y + p.up FS FT x = u := by
    rw [hux]
    ext i j
    simp only [hyd, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    rw [← add_mul, add_comm]
    exact hu i j
  obtain ⟨b, hb⟩ := exists_form p FS FT hy
  let Φx : SB (Matrix Y Y' k) := ⟨fun t => O.1 (t + x), GlobalTheory.LocComb.trans_mem_SB O.2 x⟩
  let Φm : SB (Matrix Y Y' k) := ⟨fun t => GlobalTheory.LocMod.Inhab.pairing ψk t b * Φx.1 t, GlobalTheory.LocComb.modul_mem_SB hd Φx.2 b⟩
  refine ⟨ψ (-symplOH S T y (p.up FS FT x)) • Φm, fun Tm h => ?_⟩
  have e1 : Tm Φx = heisO ψ S T (p.up FS FT x) (Tm O) := h.trans x O Φx fun _ => rfl
  have e2 : Tm Φm = heisO ψ S T y (Tm Φx) := h.modul y hy Φx Φm fun t => by
    show GlobalTheory.LocMod.Inhab.pairing ψk t b * Φx.1 t = _
    rw [GlobalTheory.LocSympl.psi_sympl_up p FS FT ψ ψk hψk t y, hb t]
    rfl
  have e3 := GlobalTheory.PlaceModel.heisL_heisL S T ψ y (p.up FS FT x) (Tm O)
  change heisO ψ S T y (heisO ψ S T (p.up FS FT x) (Tm O)) =
    ψ (symplOH S T y (p.up FS FT x)) • heisO ψ S T (y + p.up FS FT x) (Tm O) at e3
  rw [map_smul, e2, e1, e3, smul_smul, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one, one_smul, hsum]

end GlobalTheory.FlatPlace.CombAll

namespace GlobalTheory.FlatPlace

/- English proof (translation)
Introduce `D k _ _ _ _ p ψ hψ S T Y Y' _ _ _ _ FS FT c hc T₀ hT₀ O Ξ hO hT₀O hΞ`. Establish `hA : ∀ u : c.support, ∃ Φ : SB (Matrix Y Y' k), ∀ Tm, p.IsModel ψ FS FT Tm → Tm Φ = heisO ψ S T u (Tm O)` using `fun u => CombAll.exists_heis p ψ hψ FS FT O (hc u u.2)`. Use `choose Φ hΦ using hA`. Set `Ξ' : SB (Matrix Y Y' k)` to `∑ u : c.support, c u • Φ u`. Establish `hΞ' : ∀ Tm, p.IsModel ψ FS FT Tm → Tm Ξ' = comb ψ S T c (Tm O)` using `fun Tm h => by`.

Simplify using `only [Ξ', map_sum, map_smul, fun u => hΦ u Tm h]`. Rewrite using `[GlobalTheory.HeisComb.comb_eq_sum, Finsupp.sum]`. Conclude with `Finset.sum_coe_sort c.support (fun u => c u • heisO ψ S T u (Tm O))`. Establish `hinj : Ξ = Ξ'`. Assume the negation of the conclusion as `hne`.

Establish `h0 : Ξ - Ξ' ≠ 0` using `sub_ne_zero.2 hne`. Establish `e1 : T₀ (Ξ - Ξ') = ((0 : ℂ) • T₀) (Ξ - Ξ')`. Rewrite using `[map_sub, hΞ, hΞ' T₀ hT₀, sub_self, LinearMap.smul_apply, zero_smul]`. Establish `e2` using `(GlobalTheory.LocModU.localModel_uniq_transport_exist D k p Y Y' S T FS FT ψ hψ).1 T₀ ((0 : ℂ) • T₀) hT₀ (GlobalTheory.LocMod.Witness.isModel_smul p hT₀ 0) _ h0 e1`. Apply `hT₀O` to reduce the goal to its premises.

Rewrite using `[e2, zero_smul, LinearMap.zero_apply]`. Use `⟨hc, fun Tm h Φ₀ Φ' h1 h2 => ?_⟩` and prove the remaining obligations. Establish `e2 : Φ' = Ξ'` using `by rw [← hinj]; exact Subtype.ext h2`. Establish `e3 : Φ₀ = O` using `Subtype.ext (h1.trans hO.symm)`. Rewrite using `[e2, e3, hΞ' Tm h]`.
-/
theorem isCombAt_of_one : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (c : WO S T →₀ ℂ), (∀ u ∈ c.support, IsHalf (p.e + cA D p.e) u) → ∀ T₀, p.IsModel ψ FS FT T₀ → ∀ O Ξ : SB (Matrix Y Y' k), IsOne O → T₀ O ≠ 0 → T₀ Ξ = comb ψ S T c (T₀ O) → p.IsCombAt ψ FS FT c Ξ.1 := by
  intro D k _ _ _ _ p ψ hψ S T Y Y' _ _ _ _ FS FT c hc T₀ hT₀ O Ξ hO hT₀O hΞ
  classical
  have hA : ∀ u : c.support, ∃ Φ : SB (Matrix Y Y' k), ∀ Tm, p.IsModel ψ FS FT Tm → Tm Φ = heisO ψ S T u (Tm O) :=
    fun u => CombAll.exists_heis p ψ hψ FS FT O (hc u u.2)
  choose Φ hΦ using hA
  let Ξ' : SB (Matrix Y Y' k) := ∑ u : c.support, c u • Φ u
  have hΞ' : ∀ Tm, p.IsModel ψ FS FT Tm → Tm Ξ' = comb ψ S T c (Tm O) := fun Tm h => by
    simp only [Ξ', map_sum, map_smul, fun u => hΦ u Tm h]
    rw [GlobalTheory.HeisComb.comb_eq_sum, Finsupp.sum]
    exact Finset.sum_coe_sort c.support (fun u => c u • heisO ψ S T u (Tm O))
  have hinj : Ξ = Ξ' := by
    by_contra hne
    have h0 : Ξ - Ξ' ≠ 0 := sub_ne_zero.2 hne
    have e1 : T₀ (Ξ - Ξ') = ((0 : ℂ) • T₀) (Ξ - Ξ') := by
      rw [map_sub, hΞ, hΞ' T₀ hT₀, sub_self, LinearMap.smul_apply, zero_smul]
    have e2 := (GlobalTheory.LocModU.localModel_uniq_transport_exist D k p Y Y' S T FS FT ψ hψ).1 T₀ ((0 : ℂ) • T₀) hT₀
      (GlobalTheory.LocMod.Witness.isModel_smul p hT₀ 0) _ h0 e1
    apply hT₀O
    rw [e2, zero_smul, LinearMap.zero_apply]
  refine ⟨hc, fun Tm h Φ₀ Φ' h1 h2 => ?_⟩
  have e2 : Φ' = Ξ' := by rw [← hinj]; exact Subtype.ext h2
  have e3 : Φ₀ = O := Subtype.ext (h1.trans hO.symm)
  rw [e2, e3, hΞ' Tm h]

end GlobalTheory.FlatPlace
