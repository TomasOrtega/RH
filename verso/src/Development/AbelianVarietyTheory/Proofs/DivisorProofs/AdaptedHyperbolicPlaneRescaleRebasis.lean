import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegIdxOfIsStd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseFits
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DownRight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRescalePrimitiveInLatticeAtSplitPrimes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitPlaceBasisHyperbolicPlaneComplement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLowLat

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open scoped Matrix nonZeroDivisors

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hcm B₀ B hemb n n₁ Y Y₁ H₀ i₀ i₁ h01 h1n hL hL₁ hH`. Establish `hss : ∀ a : E, σ (σ a) = a` using `fun a => by`. Set `τ : E →+* ℂ` to `(IsAlgClosed.lift (M := ℂ) (R := ℚ) (S := E)).toRingHom`. Apply `τ.injective` to reduce the goal to its premises. Rewrite using `[hcm.2.2.2 τ, hcm.2.2.2 τ, star_star]`.

Establish `fsl : ∀ (J : Matrix (Fin n) (Fin n) E) (s : E) (a b : Fin n → E), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form σ J (s • a) b = s * GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form σ J a b` using `fun J s a b => by`. Simplify using `[GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form, smul_dotProduct]`. Establish `fsr : ∀ (J : Matrix (Fin n) (Fin n) E) (s : E) (a b : Fin n → E), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form σ J b (s • a) = σ s * GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form σ J b a` using `fun J s a b => by`. Establish `: (fun i => σ ((s • a) i)) = σ s • fun i => σ (a i)` using `funext fun i => by simp`. Simplify using `only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form, this, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]`.

Establish `hx0 : H₀.x ≠ 0`. Introduce `h`. Use `hH.xy` as an intermediate fact. Rewrite `this` using `[h]`. Simplify using `[GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form] at this`.

Establish `hy0 : H₀.y ≠ 0`. Introduce `h`. Establish `h1` using `hH.xy`. Establish `h2` using `fsr Y.J 0 H₀.y H₀.x`. Rewrite `h2` using `[zero_smul, map_zero, zero_mul, ← h, h1]`.

Conclude with `one_ne_zero h2`. Take `⟨c, hc0, hc⟩` from `GlobalTheory.PlaneSkewScale.exists_rescale_primAt F E σ hcm n Y.L hL H₀.x H₀.y hx0 hy0 B.P B.τ`. Establish `hσc : σ c ≠ 0` using `fun h => hc0 (by rw [← hss c, h, map_zero])`. Use `set x : Fin n → E := c • H₀.x with hxdef`. Use `set y : Fin n → E := (σ c)⁻¹ • H₀.y with hydef`.

Establish `ex : ∀ s : E, (s * c⁻¹) • x = s • H₀.x` using `fun s => by`. Rewrite using `[hxdef, smul_smul, mul_assoc, inv_mul_cancel₀ hc0, mul_one]`. Establish `ey : ∀ t : E, (t * σ c) • y = t • H₀.y` using `fun t => by`. Rewrite using `[hydef, smul_smul, mul_assoc, mul_inv_cancel₀ hσc, mul_one]`. Set `𝔟 : FractionalIdeal (𝓞 E)⁰ E` to `FractionalIdeal.spanSingleton _ c⁻¹ * H₀.𝔟`.

Establish `h𝔟 : ∀ s : E, s ∈ 𝔟 ↔ s • x ∈ Y.L`. Introduce `s`. Rewrite using `[FractionalIdeal.mem_singleton_mul, hxdef, smul_smul]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨t, ht, rfl⟩`.

Rewrite using `[mul_comm c⁻¹ t, mul_assoc, inv_mul_cancel₀ hc0, mul_one]`. Conclude with `(hH.ideal t).1 ht`. Introduce `h`. Use `⟨s * c, (hH.ideal _).2 h, ?_⟩` and prove the remaining obligations. Rewrite using `[mul_comm s c, ← mul_assoc, inv_mul_cancel₀ hc0, one_mul]`.

Establish `hsplit : ∀ z ∈ Y.L, ∃ (s t : E) (u : Fin n₁ → E), s • x ∈ Y.L ∧ t • y ∈ Y.L ∧ u ∈ Y₁.L ∧ z = s • x + H₀.ι *ᵥ u + t • y`. Introduce `z hz`. Take `⟨s, t, u, hs, ht, hu, rfl⟩` from `hH.split z hz`. Conclude with `⟨s * c⁻¹, t * σ c, u, by rw [ex]; exact hs, by rw [ey]; exact ht, hu, by rw [ex, ey]⟩`. Use `haveI : Y₁.L.IsLattice E := hL₁`.

Establish `hcomap : Y.L.comap ((Matrix.mulVecLin H₀.ι).restrictScalars (𝓞 E)) = Y₁.L` using `Submodule.ext fun u => (hH.low u).symm`. Establish `hb₁ : ∀ v : B.P, ∃ β, GlobalTheory.AdelicU.IsSplitBasis (B.τ v) Y₁.L β` using `fun v => GlobalTheory.AdelicU.exists_isSplitBasis (B.τ v) Y₁.L hcm`. Use `choose β₁ hβ₁ using hb₁`. Set `bas₁ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, GL (Fin n₁) (Fv F v)` to `fun v => if h : v ∈ B.P then β₁ ⟨v, h⟩ else Y₁.bas v`. Establish `hbas₁ : ∀ v : B.P, bas₁ v = β₁ v` using `fun v => by simp only [bas₁, dif_pos v.2]`.

Establish `hb : ∀ v : B.P, ∃ β : GL (Fin n) (Fv F v), (∀ i : Fin n, (i.1 = i₀ → ∀ r, β.1 r i = B.τ v (x r)) ∧ (i.1 = i₁ → ∀ r, β.1 r i = B.τ v (y r)) ∧ ∀ j : Fin n₁, i.1 = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.skip i₀ i₁ j → ∀ r, β.1 r i = (H₀.ι.map (B.τ v) * (β₁ v).1) r …` using `fun v => GlobalTheory.PlaneBasis.exists_isSplitBasis_plane F E σ hcm v (B.τ v) n n₁ Y.L x y H₀.ι (β₁ v) i₀ i₁ hH.rank h01 h1n hL (fun z hz => by`. Take `⟨s, t, u, hs, ht, hu, hz'⟩` from `hsplit z hz`. Conclude with `⟨s, t, u, hs, ht, (hH.low u).1 hu, hz'⟩)`. Use the proof step `(by simp only [GlobalTheory.AdelicU.valued_apply_eq_valuation]; exact (hc v).1)`. Use the proof step `(by simp only [GlobalTheory.AdelicU.valued_apply_eq_valuation]; exact (hc v).2)`.

Use the proof step `(by rw [hcomap]; exact hβ₁ v)`. Use `choose β hβ using hb`. Set `bas : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, GL (Fin n) (Fv F v)` to `fun v => if h : v ∈ B.P then β ⟨v, h⟩ else Y.bas v`. Establish `hbas : ∀ v : B.P, bas v = β v` using `fun v => by simp only [bas, dif_pos v.2]`. Set `Y' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n` to `⟨Y.J, Y.L, Y.θ, bas⟩`.

Set `Y₁' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n₁` to `⟨Y₁.J, Y₁.L, Y₁.θ, bas₁⟩`. Use `⟨Y', Y₁', ⟨x, y, H₀.ι, 𝔟⟩, rfl, rfl, fun v => ?_, fun v => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[show Y'.bas v = β v from hbas v]`. Conclude with `(hβ v).2`. Rewrite using `[show Y₁'.bas v = β₁ v from hbas₁ v]`.

Conclude with `hβ₁ v`. Conclude with `{ rank := hH.rank xx := by show GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form σ Y.J x x = 0`. Rewrite using `[hxdef, fsl, fsr, hH.xx, mul_zero, mul_zero]`. Use `yy := by show GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form σ Y.J y y = 0`. Rewrite using `[hydef, fsl, fsr, hH.yy, mul_zero, mul_zero]`.

Use `xy := by show GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form σ Y.J x y = 1`. Rewrite using `[hxdef, hydef, fsl, fsr, hH.xy, map_inv₀, hss, mul_one, mul_inv_cancel₀ hc0]`. Use `orth := fun u => by show GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form σ Y.J (H₀.ι *ᵥ u) x = 0 ∧ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form σ Y.J (H₀.ι *ᵥ u) y = 0`. Rewrite using `[hxdef, hydef, fsr, fsr, (hH.orth u).1, (hH.orth u).2, mul_zero, mul_zero]`. Conclude with `⟨rfl, rfl⟩`.

Use `gram := hH.gram`. Use `low := hH.low`. Use `split := hsplit`. Use `ideal := h𝔟`. Use `cartan := fun w => by`.

Take `⟨hθι, c₀, hc₀, he⟩` from `hH.cartan w`. Rewrite using `[hemb]`. Use `⟨hθι, (B₀.emb w).1 (σ c)⁻¹ * c₀ * ((B₀.emb w).1 c)⁻¹, ?_, ?_⟩` and prove the remaining obligations. Establish `h1 : (B₀.emb w).1 (σ c)⁻¹ ≠ 0` using `(map_ne_zero _).2 (inv_ne_zero hσc)`. Establish `h2 : (B₀.emb w).1 c ≠ 0` using `(map_ne_zero _).2 hc0`.

Conclude with `mul_ne_zero (mul_ne_zero h1 hc₀) (inv_ne_zero h2)`. Establish `h2 : (B₀.emb w).1 c ≠ 0` using `(map_ne_zero _).2 hc0`. Establish `hx' : (fun i => (B₀.emb w).1 (x i)) = (B₀.emb w).1 c • fun i => (B₀.emb w).1 (H₀.x i)`. Use function extensionality and compare the values at `fun i => by simp [hxdef]`. Establish `hy' : (fun i => (B₀.emb w).1 (y i)) = (B₀.emb w).1 (σ c)⁻¹ • fun i => (B₀.emb w).1 (H₀.y i)`.

Use function extensionality and compare the values at `fun i => by simp [hydef]`. Use `show (fun i => (B₀.emb w).1 (y i)) = _ • Y.θ w *ᵥ fun i => (B₀.emb w).1 (x i)`. Rewrite using `[hx', hy', he, Matrix.mulVec_smul, smul_smul, smul_smul]`. Use `congr 1`. Clear the denominators using the available nonvanishing facts.

Use `bas := fun v i => by`. Rewrite using `[show (GlobalTheory.ThK.reS Y Y').bas v = β v from hbas v, show (GlobalTheory.ThK.reS Y₁ Y₁').bas v = β₁ v from hbas₁ v]`. Conclude with `(hβ v).1 i }`.
-/
theorem _root_.GlobalTheory.T.adaptedHyperbolicPlane_rescale_rebasis : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (B₀ B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E), B.emb = B₀.emb → ∀ (n n₁ : ℕ) (Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (Y₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n₁)
    (H₀ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Plane E n n₁) (i₀ i₁ : ℕ), i₀ < i₁ → i₁ < n → Y.L.IsLattice E → Y₁.L.IsLattice E →
    H₀.IsAdapted σ B₀ Y Y₁ i₀ i₁ → ∃ (Y' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (Y₁' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n₁) (H : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Plane E n n₁),
      Y'.θ = Y.θ ∧ Y₁'.θ = Y₁.θ ∧ (∀ v : B.P, GlobalTheory.AdelicU.IsSplitBasis (B.τ v) Y.L (Y'.bas v)) ∧
      (∀ v : B.P, GlobalTheory.AdelicU.IsSplitBasis (B.τ v) Y₁.L (Y₁'.bas v)) ∧
      H.IsAdapted σ B (GlobalTheory.ThK.reS Y Y') (GlobalTheory.ThK.reS Y₁ Y₁') i₀ i₁ := by
  intro F E _ _ _ _ _ σ hcm B₀ B hemb n n₁ Y Y₁ H₀ i₀ i₁ h01 h1n hL hL₁ hH
  classical
  have hss : ∀ a : E, σ (σ a) = a := fun a => by
    let τ : E →+* ℂ := (IsAlgClosed.lift (M := ℂ) (R := ℚ) (S := E)).toRingHom
    apply τ.injective
    rw [hcm.2.2.2 τ, hcm.2.2.2 τ, star_star]
  have fsl : ∀ (J : Matrix (Fin n) (Fin n) E) (s : E) (a b : Fin n → E),
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form σ J (s • a) b = s * GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form σ J a b := fun J s a b => by
    simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form, smul_dotProduct]
  have fsr : ∀ (J : Matrix (Fin n) (Fin n) E) (s : E) (a b : Fin n → E),
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form σ J b (s • a) = σ s * GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form σ J b a := fun J s a b => by
    have : (fun i => σ ((s • a) i)) = σ s • fun i => σ (a i) := funext fun i => by simp
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form, this, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]
  have hx0 : H₀.x ≠ 0 := by
    intro h; have := hH.xy; rw [h] at this; simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form] at this
  have hy0 : H₀.y ≠ 0 := by
    intro h
    have h1 := hH.xy
    have h2 := fsr Y.J 0 H₀.y H₀.x
    rw [zero_smul, map_zero, zero_mul, ← h, h1] at h2
    exact one_ne_zero h2
  obtain ⟨c, hc0, hc⟩ := GlobalTheory.PlaneSkewScale.exists_rescale_primAt F E σ hcm n Y.L hL H₀.x H₀.y hx0 hy0 B.P B.τ
  have hσc : σ c ≠ 0 := fun h => hc0 (by rw [← hss c, h, map_zero])
  set x : Fin n → E := c • H₀.x with hxdef
  set y : Fin n → E := (σ c)⁻¹ • H₀.y with hydef
  have ex : ∀ s : E, (s * c⁻¹) • x = s • H₀.x := fun s => by
    rw [hxdef, smul_smul, mul_assoc, inv_mul_cancel₀ hc0, mul_one]
  have ey : ∀ t : E, (t * σ c) • y = t • H₀.y := fun t => by
    rw [hydef, smul_smul, mul_assoc, mul_inv_cancel₀ hσc, mul_one]
  let 𝔟 : FractionalIdeal (𝓞 E)⁰ E := FractionalIdeal.spanSingleton _ c⁻¹ * H₀.𝔟
  have h𝔟 : ∀ s : E, s ∈ 𝔟 ↔ s • x ∈ Y.L := by
    intro s
    rw [FractionalIdeal.mem_singleton_mul, hxdef, smul_smul]
    constructor
    · rintro ⟨t, ht, rfl⟩
      rw [mul_comm c⁻¹ t, mul_assoc, inv_mul_cancel₀ hc0, mul_one]
      exact (hH.ideal t).1 ht
    · intro h
      refine ⟨s * c, (hH.ideal _).2 h, ?_⟩
      rw [mul_comm s c, ← mul_assoc, inv_mul_cancel₀ hc0, one_mul]
  have hsplit : ∀ z ∈ Y.L, ∃ (s t : E) (u : Fin n₁ → E), s • x ∈ Y.L ∧ t • y ∈ Y.L ∧ u ∈ Y₁.L ∧
      z = s • x + H₀.ι *ᵥ u + t • y := by
    intro z hz
    obtain ⟨s, t, u, hs, ht, hu, rfl⟩ := hH.split z hz
    exact ⟨s * c⁻¹, t * σ c, u, by rw [ex]; exact hs, by rw [ey]; exact ht, hu, by rw [ex, ey]⟩
  haveI : Y₁.L.IsLattice E := hL₁
  have hcomap : Y.L.comap ((Matrix.mulVecLin H₀.ι).restrictScalars (𝓞 E)) = Y₁.L :=
    Submodule.ext fun u => (hH.low u).symm
  have hb₁ : ∀ v : B.P, ∃ β, GlobalTheory.AdelicU.IsSplitBasis (B.τ v) Y₁.L β := fun v =>
    GlobalTheory.AdelicU.exists_isSplitBasis (B.τ v) Y₁.L hcm
  choose β₁ hβ₁ using hb₁
  let bas₁ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, GL (Fin n₁) (Fv F v) := fun v => if h : v ∈ B.P then β₁ ⟨v, h⟩ else Y₁.bas v
  have hbas₁ : ∀ v : B.P, bas₁ v = β₁ v := fun v => by simp only [bas₁, dif_pos v.2]
  have hb : ∀ v : B.P, ∃ β : GL (Fin n) (Fv F v), (∀ i : Fin n, (i.1 = i₀ → ∀ r, β.1 r i = B.τ v (x r)) ∧
      (i.1 = i₁ → ∀ r, β.1 r i = B.τ v (y r)) ∧
      ∀ j : Fin n₁, i.1 = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.skip i₀ i₁ j → ∀ r, β.1 r i = (H₀.ι.map (B.τ v) * (β₁ v).1) r j) ∧
      GlobalTheory.AdelicU.IsSplitBasis (B.τ v) Y.L β := fun v =>
    GlobalTheory.PlaneBasis.exists_isSplitBasis_plane F E σ hcm v (B.τ v) n n₁ Y.L x y H₀.ι (β₁ v) i₀ i₁ hH.rank h01 h1n hL
      (fun z hz => by
        obtain ⟨s, t, u, hs, ht, hu, hz'⟩ := hsplit z hz
        exact ⟨s, t, u, hs, ht, (hH.low u).1 hu, hz'⟩)
      (by simp only [GlobalTheory.AdelicU.valued_apply_eq_valuation]; exact (hc v).1)
      (by simp only [GlobalTheory.AdelicU.valued_apply_eq_valuation]; exact (hc v).2)
      (by rw [hcomap]; exact hβ₁ v)
  choose β hβ using hb
  let bas : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, GL (Fin n) (Fv F v) := fun v => if h : v ∈ B.P then β ⟨v, h⟩ else Y.bas v
  have hbas : ∀ v : B.P, bas v = β v := fun v => by simp only [bas, dif_pos v.2]
  let Y' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n := ⟨Y.J, Y.L, Y.θ, bas⟩
  let Y₁' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n₁ := ⟨Y₁.J, Y₁.L, Y₁.θ, bas₁⟩
  refine ⟨Y', Y₁', ⟨x, y, H₀.ι, 𝔟⟩, rfl, rfl, fun v => ?_, fun v => ?_, ?_⟩
  · rw [show Y'.bas v = β v from hbas v]; exact (hβ v).2
  · rw [show Y₁'.bas v = β₁ v from hbas₁ v]; exact hβ₁ v
  · exact
      { rank := hH.rank
        xx := by
          show GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form σ Y.J x x = 0
          rw [hxdef, fsl, fsr, hH.xx, mul_zero, mul_zero]
        yy := by
          show GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form σ Y.J y y = 0
          rw [hydef, fsl, fsr, hH.yy, mul_zero, mul_zero]
        xy := by
          show GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form σ Y.J x y = 1
          rw [hxdef, hydef, fsl, fsr, hH.xy, map_inv₀, hss, mul_one, mul_inv_cancel₀ hc0]
        orth := fun u => by
          show GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form σ Y.J (H₀.ι *ᵥ u) x = 0 ∧ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form σ Y.J (H₀.ι *ᵥ u) y = 0
          rw [hxdef, hydef, fsr, fsr, (hH.orth u).1, (hH.orth u).2, mul_zero, mul_zero]
          exact ⟨rfl, rfl⟩
        gram := hH.gram
        low := hH.low
        split := hsplit
        ideal := h𝔟
        cartan := fun w => by
          obtain ⟨hθι, c₀, hc₀, he⟩ := hH.cartan w
          rw [hemb]
          refine ⟨hθι, (B₀.emb w).1 (σ c)⁻¹ * c₀ * ((B₀.emb w).1 c)⁻¹, ?_, ?_⟩
          · have h1 : (B₀.emb w).1 (σ c)⁻¹ ≠ 0 := (map_ne_zero _).2 (inv_ne_zero hσc)
            have h2 : (B₀.emb w).1 c ≠ 0 := (map_ne_zero _).2 hc0
            exact mul_ne_zero (mul_ne_zero h1 hc₀) (inv_ne_zero h2)
          · have h2 : (B₀.emb w).1 c ≠ 0 := (map_ne_zero _).2 hc0
            have hx' : (fun i => (B₀.emb w).1 (x i)) = (B₀.emb w).1 c • fun i => (B₀.emb w).1 (H₀.x i) :=
              funext fun i => by simp [hxdef]
            have hy' : (fun i => (B₀.emb w).1 (y i)) = (B₀.emb w).1 (σ c)⁻¹ • fun i => (B₀.emb w).1 (H₀.y i) :=
              funext fun i => by simp [hydef]
            show (fun i => (B₀.emb w).1 (y i)) = _ • Y.θ w *ᵥ fun i => (B₀.emb w).1 (x i)
            rw [hx', hy', he, Matrix.mulVec_smul, smul_smul, smul_smul]
            congr 1
            field_simp
        bas := fun v i => by
          rw [show (GlobalTheory.ThK.reS Y Y').bas v = β v from hbas v, show (GlobalTheory.ThK.reS Y₁ Y₁').bas v = β₁ v from hbas₁ v]
          exact (hβ v).1 i }

end
