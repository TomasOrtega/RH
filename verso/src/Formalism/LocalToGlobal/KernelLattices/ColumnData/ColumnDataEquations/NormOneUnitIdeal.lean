import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.ReductionOf

noncomputable section
open NumberField Formalism.BasicNotions Classical

namespace Formalism.L2.Ker.Cd.PairingIndexBounds.Eq

open Formalism.L2.PairingIndexBounds.Eq Formalism.L2.PairingIndexBounds

open Formalism.MainNotions Matrix
open Formalism.L2.Ker.Cd.IntegralLatticeDensity

variable (D : Car)

/- English proof (translation)
Use `le_antisymm ?_ (DN.vol_mul_cS_le D L L' (DN.sd_int D hL))` and prove the remaining obligations. Establish `hu : DN.vol D L * CU.cS D (DN.vol D L) = 1` using `le_antisymm (DN.vol_mul_cS_le_one D L (DN.sd_int D hL)) (DN.unitDisc D N L hL)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hu, mul_one]`. Use `_ = TaylorLogMetric.detId D L L' * DN.vol D L * CU.cS D (DN.vol D L) := (mul_assoc _ _ _).symm`.

Use `_ ≤ DN.vol D L' * CU.cS D (DN.vol D L) := by`. Establish `h` using `DN.detId_mul_vol_le D L L'`. Rewrite using `[Submodule.mul_le]`. Introduce `m hm n hn`. Conclude with `Submodule.mul_mem_mul (h hm) hn`.
-/
theorem detId_eq_vol {N : ℕ} {L L' : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} (hL : SD D L) :
    TaylorLogMetric.detId D L L' = DN.vol D L' * CU.cS D (DN.vol D L) := by
  refine le_antisymm ?_ (DN.vol_mul_cS_le D L L' (DN.sd_int D hL))
  have hu : DN.vol D L * CU.cS D (DN.vol D L) = 1 :=
    le_antisymm (DN.vol_mul_cS_le_one D L (DN.sd_int D hL)) (DN.unitDisc D N L hL)
  calc TaylorLogMetric.detId D L L' = TaylorLogMetric.detId D L L' * (DN.vol D L * CU.cS D (DN.vol D L)) := by
        rw [hu, mul_one]
    _ = TaylorLogMetric.detId D L L' * DN.vol D L * CU.cS D (DN.vol D L) := (mul_assoc _ _ _).symm
    _ ≤ DN.vol D L' * CU.cS D (DN.vol D L) := by
        have h := DN.detId_mul_vol_le D L L'
        rw [Submodule.mul_le]
        intro m hm n hn
        exact Submodule.mul_mem_mul (h hm) hn

/- English proof (translation)
Conclude with `le_antisymm (DN.vol_mul_cS_le_one D L (DN.sd_int D hL)) (DN.unitDisc D N L hL)`.
-/
theorem vol_unit {N : ℕ} {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} (hL : SD D L) :
    DN.vol D L * CU.cS D (DN.vol D L) = 1 := by
  exact le_antisymm (DN.vol_mul_cS_le_one D L (DN.sd_int D hL)) (DN.unitDisc D N L hL)

/- English proof (translation)
Introduce `N L L' L'' _ hL hL' hL''`. Rewrite using `[detId_eq_vol D hL, detId_eq_vol D hL, detId_eq_vol D hL']`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[vol_unit D hL', mul_one]`. Use `_ = DN.vol D L' * CU.cS D (DN.vol D L) * (DN.vol D L'' * CU.cS D (DN.vol D L')) := by ring`.
-/
theorem detMul : DetMul D := by
  intro N L L' L'' _ hL hL' hL''
  rw [detId_eq_vol D hL, detId_eq_vol D hL, detId_eq_vol D hL']
  calc DN.vol D L'' * CU.cS D (DN.vol D L)
      = DN.vol D L'' * CU.cS D (DN.vol D L) * (DN.vol D L' * CU.cS D (DN.vol D L')) := by
        rw [vol_unit D hL', mul_one]
    _ = DN.vol D L' * CU.cS D (DN.vol D L) * (DN.vol D L'' * CU.cS D (DN.vol D L')) := by ring

/- English proof (translation)
Introduce `z`. Use `⟨CU.cS D (Submodule.span (𝓞 D.host.E) {(z : D.host.E)}), fun x => Iff.rfl, ?_⟩` and prove the remaining obligations. Rewrite using `[CU.cS_span, Submodule.span_mul_span, Set.singleton_mul_singleton, Submodule.one_eq_span]`. Use `congr 2`. Rewrite using `[← Formalism.BasicNotions.Examples₂.star_eq_conj D.host (z : D.host.E)]`.

Conclude with `z.2.2`.
-/
theorem norm_one_unit_ideal : NormOneUnitIdeal D := by
  intro z
  refine ⟨CU.cS D (Submodule.span (𝓞 D.host.E) {(z : D.host.E)}), fun x => Iff.rfl, ?_⟩
  rw [CU.cS_span, Submodule.span_mul_span, Set.singleton_mul_singleton, Submodule.one_eq_span]
  congr 2
  rw [← Formalism.BasicNotions.Examples₂.star_eq_conj D.host (z : D.host.E)]
  exact z.2.2

/- English proof (translation)
Unfold `SDLat.smulLat`. Rewrite using `[Submodule.mem_map]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨v, hv, rfl⟩ show γ' *ᵥ (γ *ᵥ v) ∈ L`. Rewrite using `[mulVec_mulVec, h1, one_mulVec]` and apply the resulting hypothesis.

Introduce `h`. Use `⟨γ' *ᵥ z, h, ?_⟩` and prove the remaining obligations. Use `show γ *ᵥ (γ' *ᵥ z) = z`. Rewrite using `[mulVec_mulVec, h2, one_mulVec]`.
-/
private theorem smulLat_mem_lemma {N : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (γ γ' : Matrix (Fin N) (Fin N) D.host.E) (h1 : γ' * γ = 1) (h2 : γ * γ' = 1) (z : Fin N → D.host.E) :
    z ∈ SDLat.smulLat γ L ↔ γ' *ᵥ z ∈ L := by
  unfold SDLat.smulLat
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨v, hv, rfl⟩
    show γ' *ᵥ (γ *ᵥ v) ∈ L
    rwa [mulVec_mulVec, h1, one_mulVec]
  · intro h
    refine ⟨γ' *ᵥ z, h, ?_⟩
    show γ *ᵥ (γ' *ᵥ z) = z
    rw [mulVec_mulVec, h2, one_mulVec]

/- English proof (translation)
Introduce `N L₀ L γ _ hL₀ hL`. Use `letI := D.host.cmStar`. Establish `hγ : star (γ : Matrix (Fin N) (Fin N) D.host.E) * γ = 1` using `γ.2.1`. Establish `hγ' : (γ : Matrix (Fin N) (Fin N) D.host.E) * star (γ : Matrix (Fin N) (Fin N) D.host.E) = 1` using `γ.2.2`. Rewrite using `[detId_eq_vol D hL₀, detId_eq_vol D hL₀, ← mul_assoc]`.

Use `congr 1`. Unfold `DN.vol`. Rewrite using `[Submodule.span_mul_span]`. Use `congr 1`. Use extensionality with `x`.

Simplify using `only [Set.mem_setOf_eq, Set.mem_mul, Set.mem_singleton_iff]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨U', hU', rfl⟩`. Use `⟨_, rfl, (star (γ : Matrix (Fin N) (Fin N) D.host.E) * U').det, ⟨star (γ : Matrix (Fin N) (Fin N) D.host.E) * U', fun j => ?_, rfl⟩, ?_⟩` and prove the remaining obligations. Conclude with `(smulLat_mem_lemma D L _ _ hγ hγ' _).mp (hU' j)`.

Rewrite using `[← det_mul, ← mul_assoc, hγ', one_mul]`. Introduce and unpack `⟨_, rfl, _, ⟨U, hU, rfl⟩, rfl⟩`. Use `⟨(γ : Matrix (Fin N) (Fin N) D.host.E) * U, fun j => ?_, (det_mul _ _).symm⟩` and prove the remaining obligations. Rewrite using `[smulLat_mem_lemma D L _ _ hγ hγ']`. Use `show star (γ : Matrix (Fin N) (Fin N) D.host.E) *ᵥ ((γ : Matrix (Fin N) (Fin N) D.host.E) *ᵥ fun i => U i j) ∈ L`.

Rewrite using `[mulVec_mulVec, hγ, one_mulVec]`. Conclude with `hU j`.
-/
theorem detSmul : DetSmul D := by
  intro N L₀ L γ _ hL₀ hL
  letI := D.host.cmStar
  have hγ : star (γ : Matrix (Fin N) (Fin N) D.host.E) * γ = 1 := γ.2.1
  have hγ' : (γ : Matrix (Fin N) (Fin N) D.host.E) * star (γ : Matrix (Fin N) (Fin N) D.host.E) = 1 := γ.2.2
  rw [detId_eq_vol D hL₀, detId_eq_vol D hL₀, ← mul_assoc]
  congr 1
  unfold DN.vol
  rw [Submodule.span_mul_span]
  congr 1
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_mul, Set.mem_singleton_iff]
  constructor
  · rintro ⟨U', hU', rfl⟩
    refine ⟨_, rfl, (star (γ : Matrix (Fin N) (Fin N) D.host.E) * U').det, ⟨star (γ : Matrix (Fin N) (Fin N) D.host.E) * U', fun j => ?_, rfl⟩, ?_⟩
    · exact (smulLat_mem_lemma D L _ _ hγ hγ' _).mp (hU' j)
    · rw [← det_mul, ← mul_assoc, hγ', one_mul]
  · rintro ⟨_, rfl, _, ⟨U, hU, rfl⟩, rfl⟩
    refine ⟨(γ : Matrix (Fin N) (Fin N) D.host.E) * U, fun j => ?_, (det_mul _ _).symm⟩
    rw [smulLat_mem_lemma D L _ _ hγ hγ']
    show star (γ : Matrix (Fin N) (Fin N) D.host.E) *ᵥ ((γ : Matrix (Fin N) (Fin N) D.host.E) *ᵥ fun i => U i j) ∈ L
    rw [mulVec_mulVec, hγ, one_mulVec]
    exact hU j

/- English proof (translation)
Use `letI := D.host.cmStar`. Use `show dotProduct (star (γ *ᵥ a)) (γ *ᵥ b) = dotProduct (star a) b`. Rewrite using `[star_mulVec, dotProduct_mulVec, vecMul_vecMul, ← star_eq_conjTranspose, hu', vecMul_one]`.
-/
theorem stdH_unitary {N : ℕ} (γ : Matrix (Fin N) (Fin N) D.host.E)
    (hu' : (letI := D.host.cmStar; star γ * γ) = 1) (a b : Fin N → D.host.E) :
    (letI := D.host.cmStar; stdH D.host.E N (γ *ᵥ a) (γ *ᵥ b)) = (letI := D.host.cmStar; stdH D.host.E N a b) := by
  letI := D.host.cmStar
  show dotProduct (star (γ *ᵥ a)) (γ *ᵥ b) = dotProduct (star a) b
  rw [star_mulVec, dotProduct_mulVec, vecMul_vecMul, ← star_eq_conjTranspose, hu', vecMul_one]

/- English proof (translation)
Introduce `N L γ hL`. Use `letI := D.host.cmStar`. Establish `hγ : star (γ : Matrix (Fin N) (Fin N) D.host.E) * γ = 1` using `γ.2.1`. Establish `hγ' : (γ : Matrix (Fin N) (Fin N) D.host.E) * star (γ : Matrix (Fin N) (Fin N) D.host.E) = 1` using `γ.2.2`. Establish `hin : ∀ v ∈ L, (γ : Matrix (Fin N) (Fin N) D.host.E) *ᵥ v ∈ SDLat.smulLat (γ : Matrix (Fin N) (Fin N) D.host.E) L` using `fun v hv => by`.

Rewrite using `[smulLat_mem_lemma D L _ _ hγ hγ', mulVec_mulVec, hγ, one_mulVec]`. Conclude with `hv`. Establish `hex : ∀ x ∈ SDLat.smulLat (γ : Matrix (Fin N) (Fin N) D.host.E) L, ∃ v ∈ L, (γ : Matrix (Fin N) (Fin N) D.host.E) *ᵥ v = x` using `fun x hx => ⟨_, (smulLat_mem_lemma D L _ _ hγ hγ' x).mp hx, by rw [mulVec_mulVec, hγ', one_mulVec]⟩`. Unfold `SD Formalism.BasicNotions.IsSDLat at hL`. Take `⟨hfg, hspan, hdual⟩` from `hL`.

Unfold `SD Formalism.BasicNotions.IsSDLat`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Unfold `SDLat.smulLat`. Conclude with `hfg.map _`. Unfold `SDLat.smulLat`.

Rewrite using `[Submodule.map_coe, LinearMap.coe_restrictScalars, Submodule.span_image, hspan, Submodule.map_top, LinearMap.range_eq_top]`. Introduce `y`. Use `⟨star (γ : Matrix (Fin N) (Fin N) D.host.E) *ᵥ y, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.toLin'_apply, mulVec_mulVec, hγ', one_mulVec]`. Introduce `y`.

Establish `key : ∀ v, stdH D.host.E N ((γ : Matrix (Fin N) (Fin N) D.host.E) *ᵥ v) y = stdH D.host.E N v (star (γ : Matrix (Fin N) (Fin N) D.host.E) *ᵥ y)`. Introduce `v`. Establish `hy : y = (γ : Matrix (Fin N) (Fin N) D.host.E) *ᵥ (star (γ : Matrix (Fin N) (Fin N) D.host.E) *ᵥ y)` using `by rw [mulVec_mulVec, hγ', one_mulVec]`. Use `conv_lhs => rw [hy]`. Conclude with `stdH_unitary D (γ : Matrix (Fin N) (Fin N) D.host.E) hγ v _`.

Rewrite using `[smulLat_mem_lemma D L _ _ hγ hγ', hdual]`. Prove the components needed by the constructor for the conclusion. Introduce `h x hx`. Take `⟨v, hv, rfl⟩` from `hex x hx`. Rewrite using `[key v]`.

Conclude with `h v hv`. Introduce `h v hv`. Rewrite using `[← key v]`. Conclude with `h _ (hin v hv)`.
-/
theorem smulSD : SmulSD D := by
  intro N L γ hL
  letI := D.host.cmStar
  have hγ : star (γ : Matrix (Fin N) (Fin N) D.host.E) * γ = 1 := γ.2.1
  have hγ' : (γ : Matrix (Fin N) (Fin N) D.host.E) * star (γ : Matrix (Fin N) (Fin N) D.host.E) = 1 := γ.2.2
  have hin : ∀ v ∈ L, (γ : Matrix (Fin N) (Fin N) D.host.E) *ᵥ v ∈ SDLat.smulLat (γ : Matrix (Fin N) (Fin N) D.host.E) L := fun v hv => by
    rw [smulLat_mem_lemma D L _ _ hγ hγ', mulVec_mulVec, hγ, one_mulVec]
    exact hv
  have hex : ∀ x ∈ SDLat.smulLat (γ : Matrix (Fin N) (Fin N) D.host.E) L, ∃ v ∈ L, (γ : Matrix (Fin N) (Fin N) D.host.E) *ᵥ v = x := fun x hx =>
    ⟨_, (smulLat_mem_lemma D L _ _ hγ hγ' x).mp hx, by rw [mulVec_mulVec, hγ', one_mulVec]⟩
  unfold SD Formalism.BasicNotions.IsSDLat at hL
  obtain ⟨hfg, hspan, hdual⟩ := hL
  unfold SD Formalism.BasicNotions.IsSDLat
  refine ⟨?_, ?_, ?_⟩
  · unfold SDLat.smulLat
    exact hfg.map _
  · unfold SDLat.smulLat
    rw [Submodule.map_coe, LinearMap.coe_restrictScalars, Submodule.span_image, hspan, Submodule.map_top,
      LinearMap.range_eq_top]
    intro y
    refine ⟨star (γ : Matrix (Fin N) (Fin N) D.host.E) *ᵥ y, ?_⟩
    rw [Matrix.toLin'_apply, mulVec_mulVec, hγ', one_mulVec]
  · intro y

    have key : ∀ v, stdH D.host.E N ((γ : Matrix (Fin N) (Fin N) D.host.E) *ᵥ v) y = stdH D.host.E N v (star (γ : Matrix (Fin N) (Fin N) D.host.E) *ᵥ y) := by
      intro v
      have hy : y = (γ : Matrix (Fin N) (Fin N) D.host.E) *ᵥ (star (γ : Matrix (Fin N) (Fin N) D.host.E) *ᵥ y) := by rw [mulVec_mulVec, hγ', one_mulVec]
      conv_lhs => rw [hy]
      exact stdH_unitary D (γ : Matrix (Fin N) (Fin N) D.host.E) hγ v _
    rw [smulLat_mem_lemma D L _ _ hγ hγ', hdual]
    constructor
    · intro h x hx
      obtain ⟨v, hv, rfl⟩ := hex x hx
      rw [key v]
      exact h v hv
    · intro h v hv
      rw [← key v]
      exact h _ (hin v hv)

end Formalism.L2.Ker.Cd.PairingIndexBounds.Eq
