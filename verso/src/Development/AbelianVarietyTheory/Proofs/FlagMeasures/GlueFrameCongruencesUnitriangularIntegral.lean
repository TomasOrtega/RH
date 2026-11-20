import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.VolPin
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Vanish
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FrameGlue

open IsDedekindDomain

/- English proof (translation)
Use `haveI := P.isPrime`. Set `Rp` to `Localization.AtPrime P.asIdeal`. Use `haveI : IsDiscreteValuationRing Rp := IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain R P.ne_bot Rp`. Establish `hinj : Function.Injective (algebraMap R Rp)` using `IsLocalization.injective Rp P.asIdeal.primeCompl_le_nonZeroDivisors`. Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible Rp`.

Establish `hI : Ideal.map (algebraMap R Rp) (Ideal.span {g}) ≠ ⊥`. Rewrite using `[Ideal.map_span, Set.image_singleton, Ne, Ideal.span_singleton_eq_bot]`. Conclude with `(map_ne_zero_iff _ hinj).2 hg`. Take `⟨n, hn⟩` from `IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hI hϖ`. Use `⟨n, fun x hx => ?_⟩` and prove the remaining obligations.

Establish `hmap : Ideal.map (algebraMap R Rp) (P.asIdeal ^ n) = Ideal.map (algebraMap R Rp) (Ideal.span {g})`. Rewrite using `[Ideal.map_pow, IsLocalization.AtPrime.map_eq_maximalIdeal, hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, hn]`. Establish `hx' : algebraMap R Rp x ∈ Ideal.map (algebraMap R Rp) (Ideal.span {g})` using `hmap ▸ Ideal.mem_map_of_mem _ hx`. Take `⟨⟨a, s⟩, h⟩` from `(IsLocalization.mem_map_algebraMap_iff P.asIdeal.primeCompl Rp).1 hx'`. Use `⟨s, s.2, ?_⟩` and prove the remaining obligations.

Establish `h2 : s.1 * x = a.1` using `hinj (by rw [map_mul, mul_comm]; exact h)`. Rewrite using `[h2]`. Conclude with `a.2`.
-/
theorem exists_pow_sat {R : Type*} [CommRing R] [IsDedekindDomain R] (P : HeightOneSpectrum R)
    {g : R} (hg : g ≠ 0) :
    ∃ e : ℕ, ∀ x ∈ P.asIdeal ^ e, ∃ s : R, s ∉ P.asIdeal ∧ s * x ∈ Ideal.span {g} := by
  classical
  haveI := P.isPrime
  let Rp := Localization.AtPrime P.asIdeal
  haveI : IsDiscreteValuationRing Rp :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain R P.ne_bot Rp
  have hinj : Function.Injective (algebraMap R Rp) :=
    IsLocalization.injective Rp P.asIdeal.primeCompl_le_nonZeroDivisors
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible Rp
  have hI : Ideal.map (algebraMap R Rp) (Ideal.span {g}) ≠ ⊥ := by
    rw [Ideal.map_span, Set.image_singleton, Ne, Ideal.span_singleton_eq_bot]
    exact (map_ne_zero_iff _ hinj).2 hg
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hI hϖ
  refine ⟨n, fun x hx => ?_⟩
  have hmap : Ideal.map (algebraMap R Rp) (P.asIdeal ^ n) =
      Ideal.map (algebraMap R Rp) (Ideal.span {g}) := by
    rw [Ideal.map_pow, IsLocalization.AtPrime.map_eq_maximalIdeal, hϖ.maximalIdeal_eq,
      Ideal.span_singleton_pow, hn]
  have hx' : algebraMap R Rp x ∈ Ideal.map (algebraMap R Rp) (Ideal.span {g}) :=
    hmap ▸ Ideal.mem_map_of_mem _ hx
  obtain ⟨⟨a, s⟩, h⟩ := (IsLocalization.mem_map_algebraMap_iff P.asIdeal.primeCompl Rp).1 hx'
  refine ⟨s, s.2, ?_⟩
  have h2 : s.1 * x = a.1 := hinj (by rw [map_mul, mul_comm]; exact h)
  rw [h2]; exact a.2

end GlobalTheory.FrameGlue

open IsDedekindDomain in
/- English proof (translation)
Introduce `E _ _ _ S r Λ g hg f f' hf hloc`. Establish `hg0 : ((g : 𝓞 E)) ≠ 0` using `by exact_mod_cast hg.ne'`. Establish `hfin : {P : HeightOneSpectrum (𝓞 E) | (g : 𝓞 E) ∈ P.asIdeal}.Finite`. Use `(Ideal.finite_factors (I := Ideal.span {(g : 𝓞 E)}) ?_).subset ?_` and prove the remaining obligations. Rewrite using `[Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]`.

Conclude with `hg0`. Introduce `P hP`. Conclude with `Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hP)`. Use `choose e he using fun P : HeightOneSpectrum (𝓞 E) => GlobalTheory.FrameGlue.exists_pow_sat P hg0`. Set `ξP : HeightOneSpectrum (𝓞 E) → Matrix (Fin (r + 1)) (Fin (r + 1)) (𝓞 E)` to `fun P => if h : (g : 𝓞 E) ∈ P.asIdeal then Classical.choose (hloc P h) else 0`.

Establish `hξP : ∀ P (h : (g : 𝓞 E) ∈ P.asIdeal), ξP P = Classical.choose (hloc P h)`. Introduce `P h`. Simplify using `only [ξP, dif_pos h]`. Establish `hcrt : ∀ a b : Fin (r + 1), ∃ y : 𝓞 E, ∀ P (hP : P ∈ hfin.toFinset), y - ξP P a b ∈ P.asIdeal ^ e P`. Introduce `a b`.

Take `⟨y, hy⟩` from `IsDedekindDomain.exists_forall_sub_mem_ideal (s := hfin.toFinset) (fun P : HeightOneSpectrum (𝓞 E) => P.asIdeal) e (fun P _ => P.prime) (fun P _ Q _ hPQ => fun h => hPQ (HeightOneSpectrum.ext h)) (fun P => ξP P.1 a b)`. Conclude with `⟨y, fun P hP => hy P hP⟩`. Use `choose y hy using hcrt`. Set `ξ : Matrix (Fin (r + 1)) (Fin (r + 1)) (𝓞 E)` to `fun a b => if b < a then 0 else if a = b then 1 else y a b`. Use `⟨ξ, fun a b hab => by simp [ξ, hab], fun a => by simp [ξ], fun b P hP => ?_⟩` and prove the remaining obligations.

Use `haveI := P.isPrime`. Establish `hPs : P ∈ hfin.toFinset` using `by simpa using hP`. Take `⟨hlow, hdiag, hmod⟩` from `Classical.choose_spec (hloc P hP)`. Rewrite `hlow`, `hdiag`, `hmod` using `[← hξP P hP]`. Establish `hdiff : ∀ a, ξP P a b - ξ a b ∈ P.asIdeal ^ e P`.

Introduce `a`. Distinguish the cases in `hba : b < a`. Simplify using `[ξ, hba, hlow a b hba]`. Distinguish the cases in `hab : a = b`. Substitute `hab` using the available equality.

Simplify using `[ξ, hdiag]`. Use `hy a b P hPs` as an intermediate fact. Simplify using `only [ξ, hba, hab, if_false]`. Rewrite using `[← neg_sub]`. Conclude with `(Ideal.neg_mem_iff _).2 this`.

Use `set L := Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Ideal.span {(g : 𝓞 E)} • Λ) with hL`. Establish `key : ∀ (x : 𝓞 E) (v : S.V), ((x : E)) • v = x • v` using `fun x v => algebraMap_smul E x v`. Establish `hterm : ∀ a, ((ξP P a b - ξ a b : 𝓞 E) : E) • f a ∈ L`. Introduce `a`. Take `⟨s, hsP, hs⟩` from `he P _ (hdiff a)`.

Take `⟨t, ht, htf⟩` from `hf P hP a`. Use `⟨s * t, P.asIdeal.primeCompl.mul_mem hsP ht, ?_⟩` and prove the remaining obligations. Establish `: (s * t) • (((ξP P a b - ξ a b : 𝓞 E) : E) • f a) = (s * (ξP P a b - ξ a b)) • (t • f a)`. Rewrite using `[key, smul_smul, smul_smul]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Conclude with `Submodule.smul_mem_smul hs htf`. Establish `hsplit : f' b - frameAct f ξ b = (f' b - frameAct f (ξP P) b) + ∑ a, ((ξP P a b - ξ a b : 𝓞 E) : E) • f a`. Establish `hs : ∑ a, ((ξP P a b - ξ a b : 𝓞 E) : E) • f a = frameAct f (ξP P) b - frameAct f ξ b`.

Simplify using `only [frameAct, ← Finset.sum_sub_distrib]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Use `push_cast`. Rewrite using `[sub_smul]`. Rewrite using `[hs]`.

Normalize the expressions using the abelian group laws. Rewrite using `[hsplit]`. Conclude with `L.add_mem (hmod b) (L.sum_mem fun a _ => hterm a)`.
-/
theorem GlobalTheory.FrameGlue.glue : ∀ {E : Type} [Field E] [NumberField E] [StarRing E] (S : Formalism.BasicNotions.HSpace E) (r : ℕ) (Λ : Submodule (𝓞 E) S.V) (g : ℕ), 0 < g → ∀ (f f' : Fin (r + 1) → S.V), (∀ P : IsDedekindDomain.HeightOneSpectrum (𝓞 E), (g : 𝓞 E) ∈ P.asIdeal → ∀ a, f a ∈ (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal Λ)) → (∀ P : IsDedekindDomain.HeightOneSpectrum (𝓞 E), (g : 𝓞 E) ∈ P.asIdeal → ∃ ξ : Matrix (Fin (r + 1)) (Fin (r + 1)) (𝓞 E), (∀ a b, b < a → ξ a b = 0) ∧ (∀ a, ξ a a = 1) ∧ ∀ b, f' b - frameAct f ξ b ∈ (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Ideal.span {(g : 𝓞 E)} • Λ))) → ∃ ξ : Matrix (Fin (r + 1)) (Fin (r + 1)) (𝓞 E), (∀ a b, b < a → ξ a b = 0) ∧ (∀ a, ξ a a = 1) ∧ ∀ b, ModG S Λ g (f' b - frameAct f ξ b) := by
  intro E _ _ _ S r Λ g hg f f' hf hloc
  classical
  have hg0 : ((g : 𝓞 E)) ≠ 0 := by exact_mod_cast hg.ne'
  have hfin : {P : HeightOneSpectrum (𝓞 E) | (g : 𝓞 E) ∈ P.asIdeal}.Finite := by
    refine (Ideal.finite_factors (I := Ideal.span {(g : 𝓞 E)}) ?_).subset ?_
    · rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hg0
    · intro P hP
      exact Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hP)
  choose e he using fun P : HeightOneSpectrum (𝓞 E) => GlobalTheory.FrameGlue.exists_pow_sat P hg0
  let ξP : HeightOneSpectrum (𝓞 E) → Matrix (Fin (r + 1)) (Fin (r + 1)) (𝓞 E) := fun P =>
    if h : (g : 𝓞 E) ∈ P.asIdeal then Classical.choose (hloc P h) else 0
  have hξP : ∀ P (h : (g : 𝓞 E) ∈ P.asIdeal), ξP P = Classical.choose (hloc P h) := by
    intro P h; simp only [ξP, dif_pos h]
  have hcrt : ∀ a b : Fin (r + 1), ∃ y : 𝓞 E, ∀ P (hP : P ∈ hfin.toFinset),
      y - ξP P a b ∈ P.asIdeal ^ e P := by
    intro a b
    obtain ⟨y, hy⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := hfin.toFinset)
      (fun P : HeightOneSpectrum (𝓞 E) => P.asIdeal) e
      (fun P _ => P.prime) (fun P _ Q _ hPQ => fun h => hPQ (HeightOneSpectrum.ext h))
      (fun P => ξP P.1 a b)
    exact ⟨y, fun P hP => hy P hP⟩
  choose y hy using hcrt
  let ξ : Matrix (Fin (r + 1)) (Fin (r + 1)) (𝓞 E) := fun a b =>
    if b < a then 0 else if a = b then 1 else y a b
  refine ⟨ξ, fun a b hab => by simp [ξ, hab], fun a => by simp [ξ], fun b P hP => ?_⟩
  haveI := P.isPrime
  have hPs : P ∈ hfin.toFinset := by simpa using hP
  obtain ⟨hlow, hdiag, hmod⟩ := Classical.choose_spec (hloc P hP)
  rw [← hξP P hP] at hlow hdiag hmod

  have hdiff : ∀ a, ξP P a b - ξ a b ∈ P.asIdeal ^ e P := by
    intro a
    by_cases hba : b < a
    · simp [ξ, hba, hlow a b hba]
    · by_cases hab : a = b
      · subst hab; simp [ξ, hdiag]
      · have := hy a b P hPs
        simp only [ξ, hba, hab, if_false]
        rw [← neg_sub]; exact (Ideal.neg_mem_iff _).2 this
  set L := Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Ideal.span {(g : 𝓞 E)} • Λ) with hL
  have key : ∀ (x : 𝓞 E) (v : S.V), ((x : E)) • v = x • v := fun x v => algebraMap_smul E x v
  have hterm : ∀ a, ((ξP P a b - ξ a b : 𝓞 E) : E) • f a ∈ L := by
    intro a
    obtain ⟨s, hsP, hs⟩ := he P _ (hdiff a)
    obtain ⟨t, ht, htf⟩ := hf P hP a
    refine ⟨s * t, P.asIdeal.primeCompl.mul_mem hsP ht, ?_⟩
    have : (s * t) • (((ξP P a b - ξ a b : 𝓞 E) : E) • f a) =
        (s * (ξP P a b - ξ a b)) • (t • f a) := by
      rw [key, smul_smul, smul_smul]
      congr 1; ring
    rw [this]
    exact Submodule.smul_mem_smul hs htf
  have hsplit : f' b - frameAct f ξ b =
      (f' b - frameAct f (ξP P) b) + ∑ a, ((ξP P a b - ξ a b : 𝓞 E) : E) • f a := by
    have hs : ∑ a, ((ξP P a b - ξ a b : 𝓞 E) : E) • f a =
        frameAct f (ξP P) b - frameAct f ξ b := by
      simp only [frameAct, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      push_cast; rw [sub_smul]
    rw [hs]; abel
  rw [hsplit]
  exact L.add_mem (hmod b) (L.sum_mem fun a _ => hterm a)
