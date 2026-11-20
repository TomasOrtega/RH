import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.LocDegOneBelow

noncomputable section

namespace MassDataIdxRes

open NumberField IsDedekindDomain Ideal

/- English proof (translation)
Introduce `h`. Apply `hI` to reduce the goal to its premises. Use extensionality with `y`. Prove the components needed by the constructor for the conclusion. Introduce `hy`.

Establish `h1 : f.symm y ∈ I.comap (f : A →+* B)`. Rewrite using `[Ideal.mem_comap]`. Simplify using `using hy`. Rewrite `h1` using `[h, Ideal.mem_bot]`. Simplify using `using h1`.

Introduce `hy`. Rewrite `hy` using `[Ideal.mem_bot]`. Rewrite using `[hy]`. Conclude with `I.zero_mem`.
-/
private theorem comap_ringEquiv_ne_bot {A B : Type} [CommRing A] [CommRing B] (f : A ≃+* B)
    (I : Ideal B) (hI : I ≠ ⊥) : I.comap (f : A →+* B) ≠ ⊥ := by
  intro h
  apply hI
  ext y
  constructor
  · intro hy
    have h1 : f.symm y ∈ I.comap (f : A →+* B) := by
      rw [Ideal.mem_comap]
      simpa using hy
    rw [h, Ideal.mem_bot] at h1
    simpa using h1
  · intro hy
    rw [Ideal.mem_bot] at hy
    rw [hy]
    exact I.zero_mem

/- English proof (translation)
Establish `hrk : Module.finrank ℚ K = Module.finrank ℚ L` using `(e.toRatAlgEquiv.toLinearEquiv).finrank_eq`. Rewrite using `[hrk, ← h]`. Set `g : 𝓞 K ≃+* 𝓞 L` to `NumberField.RingOfIntegers.mapRingEquiv e`. Use `Set.ncard_congr (fun w _ => (⟨w.asIdeal.comap (g.symm : 𝓞 L →+* 𝓞 K), (by haveI := w.isPrime; infer_instance), comap_ringEquiv_ne_bot g.symm w.asIdeal w.ne_bot⟩ : HeightOneSpectrum (𝓞 L))) ?_ ?_ ?_` and prove the remaining obligations. Introduce `w hw`.

Simplify using `only [Set.mem_setOf_eq, Ideal.mem_comap] at hw ⊢`. Simplify using `using hw`. Introduce `a b _ _ hab`. Establish `h1` using `congrArg HeightOneSpectrum.asIdeal hab`. Apply `HeightOneSpectrum.ext` to reduce the goal to its premises.

Use extensionality with `x`. Establish `h2` using `SetLike.ext_iff.mp h1 (g x)`. Simplify `h2` using `[Ideal.mem_comap]`. Introduce `w hw`. Use `⟨⟨w.asIdeal.comap (g : 𝓞 K →+* 𝓞 L), (by haveI := w.isPrime; infer_instance), comap_ringEquiv_ne_bot g w.asIdeal w.ne_bot⟩, ?_, ?_⟩` and prove the remaining obligations.

Simplify using `only [Set.mem_setOf_eq, Ideal.mem_comap] at hw ⊢`. Simplify using `using hw`. Apply `HeightOneSpectrum.ext` to reduce the goal to its premises. Use extensionality with `x`. Rewrite using `[Ideal.mem_comap, Ideal.mem_comap]`.

Simplify using the standard rewrite rules.
-/
theorem split_transport {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] (e : K ≃+* L)
    (l : ℕ) (h : {w : HeightOneSpectrum (𝓞 L) | ((l : ℕ) : 𝓞 L) ∈ w.asIdeal}.ncard = Module.finrank ℚ L) :
    {w : HeightOneSpectrum (𝓞 K) | ((l : ℕ) : 𝓞 K) ∈ w.asIdeal}.ncard = Module.finrank ℚ K := by
  classical
  have hrk : Module.finrank ℚ K = Module.finrank ℚ L :=
    (e.toRatAlgEquiv.toLinearEquiv).finrank_eq
  rw [hrk, ← h]
  let g : 𝓞 K ≃+* 𝓞 L := NumberField.RingOfIntegers.mapRingEquiv e
  refine Set.ncard_congr
    (fun w _ => (⟨w.asIdeal.comap (g.symm : 𝓞 L →+* 𝓞 K),
      (by haveI := w.isPrime; infer_instance),
      comap_ringEquiv_ne_bot g.symm w.asIdeal w.ne_bot⟩ : HeightOneSpectrum (𝓞 L))) ?_ ?_ ?_
  · intro w hw
    simp only [Set.mem_setOf_eq, Ideal.mem_comap] at hw ⊢
    simpa using hw
  · intro a b _ _ hab
    have h1 := congrArg HeightOneSpectrum.asIdeal hab
    apply HeightOneSpectrum.ext
    ext x
    have h2 := SetLike.ext_iff.mp h1 (g x)
    simpa [Ideal.mem_comap] using h2
  · intro w hw
    refine ⟨⟨w.asIdeal.comap (g : 𝓞 K →+* 𝓞 L), (by haveI := w.isPrime; infer_instance),
      comap_ringEquiv_ne_bot g w.asIdeal w.ne_bot⟩, ?_, ?_⟩
    · simp only [Set.mem_setOf_eq, Ideal.mem_comap] at hw ⊢
      simpa using hw
    · apply HeightOneSpectrum.ext
      ext x
      rw [Ideal.mem_comap, Ideal.mem_comap]
      simp

end MassDataIdxRes

namespace MassDataIdxSteps

open NumberField Formalism.L2.SG.TypedSets Formalism.L2.SG.HidaSetting

/- English proof (translation)
Establish `hgp : Fact (gOf p).Prime` using `⟨gOf_prime X p⟩`. Establish `hmem : ((gOf p : ℕ) : 𝓞 X.B.I.F) ∈ p.1.asIdeal`. Establish `hty` using `(mem_typSet X.B.I.F (D.host.g 0) (D.host.g 1) (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero p.1).1 p.2`. Unfold `gOf`. Use `split_ifs with h`.

Conclude with `h`. Conclude with `hty.resolve_left h`. Establish `hsplit : {w : IsDedekindDomain.HeightOneSpectrum (𝓞 X.B.I.E) | ((gOf p : ℕ) : 𝓞 X.B.I.E) ∈ w.asIdeal}.ncard = Module.finrank ℚ X.B.I.E`. Unfold `gOf`. Use `split_ifs`.

Conclude with `MassDataIdxRes.split_transport X.ιE _ (D.nd.g_split 0)`. Conclude with `MassDataIdxRes.split_transport X.ιE _ (D.nd.g_split 1)`. Take `⟨he, hf⟩` from `MassDataIdxRes.locDeg_one_below (F := X.B.I.F) (E := X.B.I.E) (gOf p) hsplit p.1 hmem`. Take `⟨hc, hn⟩` from `MassDataIdxRes.arith_of_loc (gOf p) p.1 hmem he hf`. Conclude with `⟨hc, hmem, hn⟩`.
-/
theorem resArith_holds {D : Formalism.BasicNotions.D7} (X : HidaSetting D) (p : TypX X) : ResArith X p := by
  have hgp : Fact (gOf p).Prime := ⟨gOf_prime X p⟩
  have hmem : ((gOf p : ℕ) : 𝓞 X.B.I.F) ∈ p.1.asIdeal := by
    have hty := (mem_typSet X.B.I.F (D.host.g 0) (D.host.g 1) (D.host.g_prime 0).ne_zero
      (D.host.g_prime 1).ne_zero p.1).1 p.2
    unfold gOf
    split_ifs with h
    · exact h
    · exact hty.resolve_left h
  have hsplit : {w : IsDedekindDomain.HeightOneSpectrum (𝓞 X.B.I.E) |
      ((gOf p : ℕ) : 𝓞 X.B.I.E) ∈ w.asIdeal}.ncard = Module.finrank ℚ X.B.I.E := by
    unfold gOf
    split_ifs
    · exact MassDataIdxRes.split_transport X.ιE _ (D.nd.g_split 0)
    · exact MassDataIdxRes.split_transport X.ιE _ (D.nd.g_split 1)
  obtain ⟨he, hf⟩ := MassDataIdxRes.locDeg_one_below (F := X.B.I.F) (E := X.B.I.E) (gOf p) hsplit p.1 hmem
  obtain ⟨hc, hn⟩ := MassDataIdxRes.arith_of_loc (gOf p) p.1 hmem he hf
  exact ⟨hc, hmem, hn⟩

/- English proof (translation)
The claim follows from `stResZ_of X p (resArith_holds X p)`.
-/
theorem stResZ_holds {D : Formalism.BasicNotions.D7} (X : HidaSetting D) (p : TypX X) : StResZ X p :=
  stResZ_of X p (resArith_holds X p)

end MassDataIdxSteps
