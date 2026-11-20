import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ProdDat
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TensorOneApply
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsPlaceModelTensorIntegralIndicator
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CompletedHomLatticeStableSplitIdempotent
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatHalfTensorSplitPlaceSelfDualStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IndicatorLocalHomLatticeMemSchwartzBruhatStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LocMod GlobalTheory.SplitWeil ValuativeRel

noncomputable section

namespace GlobalTheory.LatIdemVac

variable {D : D7}

/- English proof (translation)
Unfold `latO`. Use `AddSubgroup.closure_mono ?_` and prove the remaining obligations. Introduce and unpack `w ⟨α, hα, -, rest⟩`. Conclude with `⟨α, hα, fun _ h => absurd trivial h, rest⟩`.
-/
theorem latO_at_le {S T : HSp D} (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E))
    (v : Pl D) : latO S T LS LT (· = v) ≤ latO S T LS LT fun _ => True := by
  unfold latO
  refine AddSubgroup.closure_mono ?_
  rintro w ⟨α, hα, -, rest⟩
  exact ⟨α, hα, fun _ h => absurd trivial h, rest⟩

/- English proof (translation)
Use `show ((0 : Ainf D.host.F), a) * ((0 : Ainf D.host.F), b) = ((0 : Ainf D.host.F), a * b)`. Rewrite using `[Prod.mk_mul_mk, mul_zero]`.
-/
theorem pairA_zero_mul (a b : Af D.host.F) :
    pairA D.host.F 0 a * pairA D.host.F 0 b = pairA D.host.F 0 (a * b) := by
  show ((0 : Ainf D.host.F), a) * ((0 : Ainf D.host.F), b) = ((0 : Ainf D.host.F), a * b)
  rw [Prod.mk_mul_mk, mul_zero]

/- English proof (translation)
Take `⟨α₀, rfl, h1, h0⟩` from `hε`. Proceed by induction on `hu using AddSubgroup.closure_induction with`. Consider the case `mem w hw`. Take `⟨α, hα, -, a, ha, s, hs, t, ht, rfl⟩` from `hw`. Use `AddSubgroup.subset_closure ⟨α₀ * α, fun w => ?_, fun w hw => ?_, a, ha, s, hs, t, ht, ?_⟩` and prove the remaining obligations.

Rewrite using `[map_mul]`. Distinguish the cases in `hwv : w = v`. Substitute `hwv` using the available equality. Rewrite using `[h1, one_mul]`. Conclude with `hα w`.

Rewrite using `[h0 w hwv, zero_mul]`. Conclude with `zero_mem _`. Rewrite using `[map_mul, h0 w hw, zero_mul]`. Use extensionality with `i j`. Simplify using `only [Matrix.of_apply, Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul, Algebra.algebraMap_self, RingHom.id_apply, pairA_zero_mul]`.

Consider the case `zero`. Use `(latO S T LS LT (· = v)).zero_mem using 1` and compare the differences between its conclusion and the goal. Use extensionality with `i j`. Simplify using the standard rewrite rules. Consider the case `add x y _ _ hx hy`.

Use `add_mem hx hy using 1` and compare the differences between its conclusion and the goal. Use extensionality with `i j`. Simplify using `only [Matrix.of_apply, Matrix.add_apply, mul_add]`. Consider the case `neg x _ hx`. Use `neg_mem hx using 1` and compare the differences between its conclusion and the goal.

Use extensionality with `i j`. Simplify using `only [Matrix.of_apply, Matrix.neg_apply, mul_neg]`.
-/
theorem placeIdem_mul_mem {S T : HSp D} (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E))
    {v : Pl D} {ε : AF D.host.F} (hε : IsPlaceIdem D v ε) {u : WO S T} (hu : u ∈ latO S T LS LT fun _ => True) :
    (Matrix.of fun i j => algebraMap (AF D.host.F) (AE D) ε * u i j : WO S T) ∈ latO S T LS LT (· = v) := by
  obtain ⟨α₀, rfl, h1, h0⟩ := hε
  induction hu using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, -, a, ha, s, hs, t, ht, rfl⟩ := hw
    refine AddSubgroup.subset_closure ⟨α₀ * α, fun w => ?_, fun w hw => ?_, a, ha, s, hs, t, ht, ?_⟩
    · rw [map_mul]
      by_cases hwv : w = v
      · subst hwv; rw [h1, one_mul]; exact hα w
      · rw [h0 w hwv, zero_mul]; exact zero_mem _
    · rw [map_mul, h0 w hw, zero_mul]
    · ext i j
      simp only [Matrix.of_apply, Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
        Algebra.algebraMap_self, RingHom.id_apply, pairA_zero_mul]
  | zero =>
    convert (latO S T LS LT (· = v)).zero_mem using 1
    ext i j; simp
  | add x y _ _ hx hy =>
    convert add_mem hx hy using 1
    ext i j; simp only [Matrix.of_apply, Matrix.add_apply, mul_add]
  | neg x _ hx =>
    convert neg_mem hx using 1
    ext i j; simp only [Matrix.of_apply, Matrix.neg_apply, mul_neg]

/- English proof (translation)
Take `⟨ε, hε, hsum⟩` from `q.above`. Establish `h` using `(GlobalTheory.SplitVac.idem_latO D k q S T LS LT _ (placeIdem_mul_mem _ _ hε hu)).1`. Use `h using 1` and compare the differences between its conclusion and the goal. Use extensionality with `i j`. Simplify using `only [Matrix.map_apply, Matrix.of_apply]`.

Rewrite using `[← hsum, ← mul_assoc, mul_add, q.split.1, q.split.2.1, add_zero]`.
-/
theorem splitIdem_mul_mem {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (q : SplitPt D k) {S T : HSp D} (LS : Lat S) (LT : Lat T) {u : WO S T}
    (hu : u ∈ latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) fun _ => True) :
    u.map (fun a => q.e * a) ∈ latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (· = q.v) := by
  obtain ⟨ε, hε, hsum⟩ := q.above
  have h := (GlobalTheory.SplitVac.idem_latO D k q S T LS LT _ (placeIdem_mul_mem _ _ hε hu)).1
  convert h using 1
  ext i j
  simp only [Matrix.map_apply, Matrix.of_apply]
  rw [← hsum, ← mul_assoc, mul_add, q.split.1, q.split.2.1, add_zero]

end GlobalTheory.LatIdemVac

namespace GlobalTheory.LatIdemVac

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k)
  {S T : HSp D} {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']

def tensorWith (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (Ψ : Matrix Y Y' k → ℂ) :
    (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ) where
  toFun Φ := p.tensorAt FS FT Φ Ψ
  map_add' Φ Φ' := by
    funext t
    simp only [Place.tensorAt, Pi.add_apply, add_mul]
  map_smul' c Φ := by
    funext t
    simp only [Place.tensorAt, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem tensorWith_apply (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (Ψ : Matrix Y Y' k → ℂ) (Φ : WO S T → ℂ) :
    tensorWith p FS FT Ψ Φ = p.tensorAt FS FT Φ Ψ := rfl

/- English proof (translation)
Use function extensionality and compare the values at `t`. Simplify using `only [Place.tensorAt]`. Rewrite using `[GlobalTheory.LocMod.Witness.down_add p FS FT t x, GlobalTheory.LocMod.TOneModel.down_half_zero p FS FT he hx, add_zero, sub_add_eq_add_sub]`.
-/
theorem tensorAt_trans (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) {e : AE D} (he : e * p.e = 0)
    (Φ : WO S T → ℂ) (Ψ : Matrix Y Y' k → ℂ) {x : WO S T} (hx : IsHalf e x) :
    p.tensorAt FS FT (fun t => Φ (t + x)) Ψ = fun t => p.tensorAt FS FT Φ Ψ (t + x) := by
  funext t
  simp only [Place.tensorAt]
  rw [GlobalTheory.LocMod.Witness.down_add p FS FT t x, GlobalTheory.LocMod.TOneModel.down_half_zero p FS FT he hx, add_zero,
    sub_add_eq_add_sub]

/- English proof (translation)
Use function extensionality and compare the values at `t`. Simplify using `only [Place.tensorAt]`. Rewrite using `[GlobalTheory.LocMod.TOneModel.symplO_sub_half p he t (GlobalTheory.LocMod.Witness.up_half p FS FT _) hy, mul_assoc]`.
-/
theorem tensorAt_modul (ψ : AddChar (AF D.host.F) ℂ) (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) {e : AE D}
    (he : e * p.e = 0) (Φ : WO S T → ℂ) (Ψ : Matrix Y Y' k → ℂ) {y : WO S T} (hy : IsHalf (cA D e) y) :
    p.tensorAt FS FT (fun t => ψ (symplO S T t y) * Φ t) Ψ = fun t => ψ (symplO S T t y) * p.tensorAt FS FT Φ Ψ t := by
  funext t
  simp only [Place.tensorAt]
  rw [GlobalTheory.LocMod.TOneModel.symplO_sub_half p he t (GlobalTheory.LocMod.Witness.up_half p FS FT _) hy, mul_assoc]

open Classical in

/- English proof (translation)
Use function extensionality and compare the values at `t`. Simplify using `only [one_smul, Place.tensorAt]`. Rewrite using `[GlobalTheory.LocMod.TOneModel.up_down_eq p FS FT t, Set.indicator_apply]`. Simplify using `only [Set.mem_setOf_eq, GlobalTheory.LocMod.TOneModel.up_down_eq p FS FT t]`. Use `set M : WO S T := t.map (fun a => p.e * a) with hMdef`.

Establish `key : ((t - M ∈ Λ ∧ IsHalf e (t - M)) ∧ M ∈ Λv) ↔ (t ∈ Λ ∧ IsHalf (e + p.e) t)`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨h1, h2⟩, h3⟩`. Use `⟨by simpa using add_mem h1 (hle h3), fun i j => ?_⟩` and prove the remaining obligations. Establish `h` using `h2 i j`.

Simplify using `only [hMdef, Matrix.sub_apply, Matrix.map_apply] at h`. Take the linear combination `h + t i j * he`. Introduce and unpack `⟨h1, h2⟩`. Establish `h3 : M ∈ Λv` using `hstab t h1`. Use `⟨⟨sub_mem h1 (hle h3), fun i j => ?_⟩, h3⟩` and prove the remaining obligations.

Simplify using `only [hMdef, Matrix.sub_apply, Matrix.map_apply]`. Take the linear combination `h2 i j - t i j * he`. Unfold `halfInd`. Distinguish the cases in `hR : t ∈ Λ ∧ IsHalf (e + p.e) t`. Take `⟨⟨h1, h2⟩, h3⟩` from `key.2 hR`.

Rewrite using `[if_pos hR, if_pos ⟨h1, h2⟩, if_pos h3, mul_one]`. Rewrite using `[if_neg hR]`. Distinguish the cases in `h3 : M ∈ Λv`. Rewrite using `[if_pos h3, mul_one, if_neg fun h => hR (key.1 ⟨h, h3⟩)]`. Rewrite using `[if_neg h3, mul_zero]`.
-/
theorem tensorAt_halfInd (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) {e : AE D} (he : e * p.e = 0)
    (Λ Λv : AddSubgroup (WO S T)) (hle : Λv ≤ Λ) (hstab : ∀ t ∈ Λ, t.map (fun a => p.e * a) ∈ Λv) :
    p.tensorAt FS FT ((1 : ℂ) • halfInd e Λ) (Set.indicator {x | p.up FS FT x ∈ Λv} fun _ => 1) =
      (1 : ℂ) • halfInd (e + p.e) Λ := by
  funext t
  simp only [one_smul, Place.tensorAt]
  rw [GlobalTheory.LocMod.TOneModel.up_down_eq p FS FT t, Set.indicator_apply]
  simp only [Set.mem_setOf_eq, GlobalTheory.LocMod.TOneModel.up_down_eq p FS FT t]
  set M : WO S T := t.map (fun a => p.e * a) with hMdef
  have key : ((t - M ∈ Λ ∧ IsHalf e (t - M)) ∧ M ∈ Λv) ↔ (t ∈ Λ ∧ IsHalf (e + p.e) t) := by
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨by simpa using add_mem h1 (hle h3), fun i j => ?_⟩
      have h := h2 i j
      simp only [hMdef, Matrix.sub_apply, Matrix.map_apply] at h
      linear_combination h + t i j * he
    · rintro ⟨h1, h2⟩
      have h3 : M ∈ Λv := hstab t h1
      refine ⟨⟨sub_mem h1 (hle h3), fun i j => ?_⟩, h3⟩
      simp only [hMdef, Matrix.sub_apply, Matrix.map_apply]
      linear_combination h2 i j - t i j * he
  unfold halfInd
  by_cases hR : t ∈ Λ ∧ IsHalf (e + p.e) t
  · obtain ⟨⟨h1, h2⟩, h3⟩ := key.2 hR
    rw [if_pos hR, if_pos ⟨h1, h2⟩, if_pos h3, mul_one]
  · rw [if_neg hR]
    by_cases h3 : M ∈ Λv
    · rw [if_pos h3, mul_one, if_neg fun h => hR (key.1 ⟨h, h3⟩)]
    · rw [if_neg h3, mul_zero]

end GlobalTheory.LatIdemVac

namespace GlobalTheory.LatIdemVac

/- English proof (translation)
Introduce `D ψ S T M M' hM hM' P e he f₀ T' hT'`. Use `set p := ofSplit P.q with hp`. Use `set Ψ : Matrix P.Y P.Y' P.k → ℂ := Set.indicator {x | p.up P.FS P.FT x ∈ latO S T (M : Set _) (M' : Set _) (· = P.q.v)} fun _ => 1 with hΨ`. Establish `hpe : p.e = P.q.e` using `rfl`. Establish `he' : e * p.e = 0` using `he`.

Establish `hΨsb : Ψ ∈ SB (Matrix P.Y P.Y' P.k)` using `GlobalTheory.T.indicator_localHomLattice_mem_schwartzBruhat D ψ S T M M' hM hM' P`. Establish `hsb : ∀ Φ, IsSBHalf e (latO S T (M : Set _) (M' : Set _) fun _ => True) Φ → IsSBHalf (e + P.q.e) (latO S T (M : Set _) (M' : Set _) fun _ => True) (p.tensorAt P.FS P.FT Φ Ψ)` using `fun Φ hΦ => GlobalTheory.T.schwartzBruhatHalf_tensor_split_place_selfDual D ψ S T M M' hM hM' P e he Φ hΦ Ψ hΨsb`. Use `⟨T' ∘ₗ tensorWith p P.FS P.FT Ψ, ⟨fun Φ hΦ x hx => ?_, fun Φ hΦ y hy => ?_, ?_⟩, fun Φ => rfl⟩` and prove the remaining obligations. Rewrite using `[LinearMap.comp_apply, tensorWith_apply, tensorAt_trans p P.FS P.FT he' Φ Ψ hx]`. Conclude with `hT'.trans _ (hsb Φ hΦ) x (GlobalTheory.LocMod.TOneModel.half_sum p he' hx)`.

Rewrite using `[LinearMap.comp_apply, tensorWith_apply, tensorAt_modul p ψ P.FS P.FT he' Φ Ψ hy]`. Conclude with `hT'.modul _ (hsb Φ hΦ) y (GlobalTheory.LocMod.TOneModel.half_sum_conj p he' hy)`. Rewrite using `[LinearMap.comp_apply, tensorWith_apply, tensorAt_halfInd p P.FS P.FT he' _ _ (latO_at_le _ _ P.q.v) (fun t ht => splitIdem_mul_mem P.q M M' ht)]`. Conclude with `hT'.vac`.
-/
theorem isPlaceModel_tensorLat : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (M : Lat S) (M' : Lat T), IsSelfDualC S M → IsSelfDualC T M' → ∀ (P : LocPl ψ S T M M') (e : AE D), e * P.q.e = 0 → ∀ (f₀ : WO S T → ℂ) (T' : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)), IsPlaceModel ψ (symplO S T) (heisO ψ S T) (e + P.q.e) (latO S T (M : Set _) (M' : Set _) fun _ => True) 1 f₀ T' → ∃ T'' : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ), IsPlaceModel ψ (symplO S T) (heisO ψ S T) e (latO S T (M : Set _) (M' : Set _) fun _ => True) 1 f₀ T'' ∧ ∀ Φ, T'' Φ = T' ((ofSplit P.q).tensorAt P.FS P.FT Φ (Set.indicator {x | (ofSplit P.q).up P.FS P.FT x ∈ latO S T (M : Set _) (M' : Set _) (· = P.q.v)} fun _ => 1)) := by
  intro D ψ S T M M' hM hM' P e he f₀ T' hT'
  set p := ofSplit P.q with hp
  set Ψ : Matrix P.Y P.Y' P.k → ℂ :=
    Set.indicator {x | p.up P.FS P.FT x ∈ latO S T (M : Set _) (M' : Set _) (· = P.q.v)} fun _ => 1 with hΨ
  have hpe : p.e = P.q.e := rfl
  have he' : e * p.e = 0 := he
  have hΨsb : Ψ ∈ SB (Matrix P.Y P.Y' P.k) := GlobalTheory.T.indicator_localHomLattice_mem_schwartzBruhat D ψ S T M M' hM hM' P
  have hsb : ∀ Φ, IsSBHalf e (latO S T (M : Set _) (M' : Set _) fun _ => True) Φ →
      IsSBHalf (e + P.q.e) (latO S T (M : Set _) (M' : Set _) fun _ => True) (p.tensorAt P.FS P.FT Φ Ψ) :=
    fun Φ hΦ => GlobalTheory.T.schwartzBruhatHalf_tensor_split_place_selfDual D ψ S T M M' hM hM' P e he Φ hΦ Ψ hΨsb
  refine ⟨T' ∘ₗ tensorWith p P.FS P.FT Ψ, ⟨fun Φ hΦ x hx => ?_, fun Φ hΦ y hy => ?_, ?_⟩, fun Φ => rfl⟩
  · rw [LinearMap.comp_apply, tensorWith_apply, tensorAt_trans p P.FS P.FT he' Φ Ψ hx]
    exact hT'.trans _ (hsb Φ hΦ) x (GlobalTheory.LocMod.TOneModel.half_sum p he' hx)
  · rw [LinearMap.comp_apply, tensorWith_apply, tensorAt_modul p ψ P.FS P.FT he' Φ Ψ hy]
    exact hT'.modul _ (hsb Φ hΦ) y (GlobalTheory.LocMod.TOneModel.half_sum_conj p he' hy)
  · rw [LinearMap.comp_apply, tensorWith_apply, tensorAt_halfInd p P.FS P.FT he' _ _ (latO_at_le _ _ P.q.v)
      (fun t ht => splitIdem_mul_mem P.q M M' ht)]
    exact hT'.vac

end GlobalTheory.LatIdemVac

end
