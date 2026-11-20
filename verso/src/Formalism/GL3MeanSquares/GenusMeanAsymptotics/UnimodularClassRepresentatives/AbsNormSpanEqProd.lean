import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.IsUnimodularAtIffVd
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.FinrankRingOfIntegers

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

/- English proof (translation)
Establish `hD` using `LocF.discrIdeal_ne_bot (LocF.aniso_of_totPosDef hd) hL hLi`. Establish `hD' : BrA.discrF F h L ≠ ⊥`. Introduce `e`. Apply `hD` to reduce the goal to its premises. Rewrite using `[BrA.discrIdeal_eq_map hF hs, e, Ideal.map_bot]`.

Rewrite using `[BrA.normD_eq hK hF hs, BrA.absNorm_eq_tprod hD']`. Conclude with `tprod_congr fun 𝔭 => by rw [BrA.vd_eq hF hs]`.
-/
theorem BrA.normD_eq_tprod (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) :
    normD h L = ∏' 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, (Ideal.absNorm 𝔭.1 : ℝ) ^ vd h L 𝔭.1 := by
  have hD := LocF.discrIdeal_ne_bot (LocF.aniso_of_totPosDef hd) hL hLi
  have hD' : BrA.discrF F h L ≠ ⊥ := by
    intro e
    apply hD
    rw [BrA.discrIdeal_eq_map hF hs, e, Ideal.map_bot]
  rw [BrA.normD_eq hK hF hs, BrA.absNorm_eq_tprod hD']
  exact tprod_congr fun 𝔭 => by rw [BrA.vd_eq hF hs]

/- English proof (translation)
Take `⟨hMl, hMg⟩` from `hM`. Establish `key : ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → ∃ g ∈ Formalism.HermitianLatticesTheory.isom h, Formalism.HermitianLatticesTheory.gmap g (locF 𝔭 L) = locF 𝔭 M`. Introduce `𝔭 h𝔭`. Take `⟨P, hP, rfl⟩` from `exists_maximal_over hK hF h𝔭`. Rewrite using `[locF_eq_loc hK hF hP, locF_eq_loc hK hF hP]`.

Conclude with `hMg P hP`. Establish `hMi : Formalism.HermitianLatticesTheory.IsIntegralLat h M`. Introduce `x hx y hy`. Rewrite using `[← LocF.iInf_locF (F := F) (1 : Submodule (𝓞 K) K), Submodule.mem_iInf]`. Introduce `𝔭`.

Take `⟨g, hg, e⟩` from `key 𝔭.1 𝔭.2`. Conclude with `BrA.form_mem_locF hF hLi 𝔭.2.isPrime hg (e ▸ LocF.le_locF 𝔭.1 M hx) (e ▸ LocF.le_locF 𝔭.1 M hy)`. Establish `hvd : ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → vd h M 𝔭 = vd h L 𝔭`. Introduce `𝔭 h𝔭`. Take `⟨g, hg, e⟩` from `key 𝔭 h𝔭`.

Rewrite using `[← localizedQuotients.vd_locF hF h M h𝔭, ← localizedQuotients.vd_locF hF h L h𝔭, ← e]`. Unfold `vd`. Rewrite using `[BrA.discrIdeal_gmap hg]`. Use `⟨hMi, hvd, ?_⟩` and prove the remaining obligations. Rewrite using `[BrA.normD_eq_tprod hK hF hs hd hMl hMi, BrA.normD_eq_tprod hK hF hs hd hL hLi]`.

Conclude with `tprod_congr fun 𝔭 => by rw [hvd 𝔭.1 𝔭.2]`.
-/
theorem integral_of_mem_genus (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {M : Submodule (𝓞 K) V} (hM : M ∈ Formalism.HermitianLatticesTheory.genus h L) :
    Formalism.HermitianLatticesTheory.IsIntegralLat h M ∧ (∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → vd h M 𝔭 = vd h L 𝔭) ∧
      normD h M = normD h L := by
  obtain ⟨hMl, hMg⟩ := hM
  have key : ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal →
      ∃ g ∈ Formalism.HermitianLatticesTheory.isom h, Formalism.HermitianLatticesTheory.gmap g (locF 𝔭 L) = locF 𝔭 M := by
    intro 𝔭 h𝔭
    obtain ⟨P, hP, rfl⟩ := exists_maximal_over hK hF h𝔭
    rw [locF_eq_loc hK hF hP, locF_eq_loc hK hF hP]
    exact hMg P hP
  have hMi : Formalism.HermitianLatticesTheory.IsIntegralLat h M := by
    intro x hx y hy
    rw [← LocF.iInf_locF (F := F) (1 : Submodule (𝓞 K) K), Submodule.mem_iInf]
    intro 𝔭
    obtain ⟨g, hg, e⟩ := key 𝔭.1 𝔭.2
    exact BrA.form_mem_locF hF hLi 𝔭.2.isPrime hg (e ▸ LocF.le_locF 𝔭.1 M hx)
      (e ▸ LocF.le_locF 𝔭.1 M hy)
  have hvd : ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → vd h M 𝔭 = vd h L 𝔭 := by
    intro 𝔭 h𝔭
    obtain ⟨g, hg, e⟩ := key 𝔭 h𝔭
    rw [← localizedQuotients.vd_locF hF h M h𝔭, ← localizedQuotients.vd_locF hF h L h𝔭, ← e]
    unfold vd
    rw [BrA.discrIdeal_gmap hg]
  refine ⟨hMi, hvd, ?_⟩
  rw [BrA.normD_eq_tprod hK hF hs hd hMl hMi, BrA.normD_eq_tprod hK hF hs hd hL hLi]
  exact tprod_congr fun 𝔭 => by rw [hvd 𝔭.1 𝔭.2]

/- English proof (translation)
The claim follows from `BrA.normD_eq_tprod hK hF hs hd hL hLi`.
-/
theorem normD_eq_prod (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) :
    normD h L = ∏' 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, (Ideal.absNorm 𝔭.1 : ℝ) ^ vd h L 𝔭.1 :=
  BrA.normD_eq_tprod hK hF hs hd hL hLi

/- English proof (translation)
Establish `hI : Ideal.span {n} ≠ ⊥`. Rewrite using `[Ne, Ideal.span_singleton_eq_bot]` and apply the resulting hypothesis. Rewrite using `[BrA.absNorm_eq_tprod hI]`. Use `tprod_congr fun 𝔭 => ?_` and prove the remaining obligations. Unfold `vF`.

Simplify using `only [Ideal.span_singleton_le_iff_mem]`.
-/
theorem absNorm_span_eq_prod (n : 𝓞 F) (hn : n ≠ 0) :
    (Ideal.absNorm (Ideal.span {n}) : ℝ) = ∏' 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, (Ideal.absNorm 𝔭.1 : ℝ) ^ vF 𝔭.1 n := by
  have hI : Ideal.span {n} ≠ ⊥ := by
    rwa [Ne, Ideal.span_singleton_eq_bot]
  rw [BrA.absNorm_eq_tprod hI]
  refine tprod_congr fun 𝔭 => ?_
  unfold vF
  simp only [Ideal.span_singleton_le_iff_mem]

end Formalism.HermitianLattices.Ext.L3
