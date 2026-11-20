import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadsHecke
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

namespace GlobalTheory.LevCmp

/- English proof (translation)
Introduce `v hv v' hv'`. Conclude with `HeightOneSpectrum.ext (hv.symm.trans hv')`.
-/
theorem overPl_subsingleton {L : Type} [Field L] (w : HeightOneSpectrum (𝓞 L)) :
    {v : HeightOneSpectrum (𝓞 (maximalRealSubfield L)) | NG.OverPl w v}.Subsingleton := by
  intro v hv v' hv'
  exact HeightOneSpectrum.ext (hv.symm.trans hv')

/- English proof (translation)
Establish `h0 : Ideal.span {((p : ℕ) : 𝓞 E)} ≠ 0`. Rewrite using `[Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]`. Conclude with `hp` after adjusting the coercions. Use `(Ideal.finite_factors h0).subset fun v hv => ?_` and prove the remaining obligations. Use `show v.asIdeal ∣ _`.

Rewrite using `[Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]`. Conclude with `hv`.
-/
theorem placesOver_finite_of_ne_zero (E : Type) [Field E] [NumberField E] (p : ℕ) (hp : p ≠ 0) :
    (placesOver E p).Finite := by
  have h0 : Ideal.span {((p : ℕ) : 𝓞 E)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp
  refine (Ideal.finite_factors h0).subset fun v hv => ?_
  show v.asIdeal ∣ _
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  exact hv

/- English proof (translation)
Introduce `D η`. Establish `hS : (⋃ k : Fin 2, placesOver D.host.E (D.host.g k)).Finite` using `Set.finite_iUnion fun k => placesOver_finite_of_ne_zero _ _ (D.host.g_prime k).ne_zero`. Establish `hR : {w | ¬ η.UnrAt w}.Finite` using `GlobalTheory.Mem.UnrAe.finite_ramified η`. Use `Set.Finite.union ?_ ?_` and prove the remaining obligations. Use `(hS.biUnion fun w _ => (overPl_subsingleton w).finite).subset ?_` and prove the remaining obligations.

Introduce and unpack `v ⟨w, hw, k, hk⟩`. Conclude with `Set.mem_biUnion (Set.mem_iUnion.2 ⟨k, hk⟩) hw`. Use `(hR.biUnion fun w _ => (overPl_subsingleton w).finite).subset ?_` and prove the remaining obligations. Introduce and unpack `v ⟨_, w, hw, hu⟩`. Conclude with `Set.mem_biUnion (x := w) hu hw`.
-/
theorem gPl_union_qPl_finite : ∀ (D : D7) (η : HChar D.host.E), (gPl D ∪ qPl D η).Finite := by
  intro D η
  have hS : (⋃ k : Fin 2, placesOver D.host.E (D.host.g k)).Finite :=
    Set.finite_iUnion fun k => placesOver_finite_of_ne_zero _ _ (D.host.g_prime k).ne_zero
  have hR : {w | ¬ η.UnrAt w}.Finite := GlobalTheory.Mem.UnrAe.finite_ramified η
  refine Set.Finite.union ?_ ?_
  · refine (hS.biUnion fun w _ => (overPl_subsingleton w).finite).subset ?_
    rintro v ⟨w, hw, k, hk⟩
    exact Set.mem_biUnion (Set.mem_iUnion.2 ⟨k, hk⟩) hw
  · refine (hR.biUnion fun w _ => (overPl_subsingleton w).finite).subset ?_
    rintro v ⟨_, w, hw, hu⟩
    exact Set.mem_biUnion (x := w) hu hw

end GlobalTheory.LevCmp
