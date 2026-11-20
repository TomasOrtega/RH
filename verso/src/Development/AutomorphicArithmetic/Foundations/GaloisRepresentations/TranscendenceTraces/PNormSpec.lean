import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

/- English proof (translation)
Introduce `hS hCE hCW hMP hPE hPL _`. Unfold `NormSpec`. Introduce `A B _ _ _ _ _ _`. Use `set p := Spec.map (CommRingCat.ofHom (algebraMap A B)) with hp`. Use `haveI : IsFinite p := by`.

Rewrite using `[hp, IsFinite.SpecMap_iff]`. Conclude with `RingHom.finite_algebraMap.mpr inferInstance`. Take `⟨T, π, ι, σ, c, hπi, hπs, hι, hσ, hsym, hgen⟩` from `hS A B`. Use `haveI := hπi`. Use `haveI := hπs`.

Use `haveI := hι`. Establish `hk : ∀ s : ↥(Spec (CommRingCat.of B)), ∃ (Ω : Type) (_ : Field Ω) (_ : IsAlgClosed Ω) (y : gp Ω ⟶ Spec (CommRingCat.of B)), pt y = s` using `fun s => hPE _ s`. Use `choose Ωk fk ak yk hyk using hk`. Set `key : ↥(Spec (CommRingCat.of B)) → ℤ` to `fun s => letI := fk s`. Use `letI := ak s`.

Use `mult p (Ωk s) (yk s)`. Set `m : ι → ℤ` to `fun j => key (c j)`. Establish `hm : ∀ j (Ω : Type) [Field Ω] [IsAlgClosed Ω] (z : gp Ω ⟶ Spec (CommRingCat.of B)), c j = pt z → m j = mult p Ω z`. Introduce `j Ω _ _ z hz`. Use `letI := fk (c j)`.

Use `letI := ak (c j)`. Conclude with `hMP p (Ωk (c j)) Ω (yk (c j)) z ((hyk (c j)).trans hz)`. Establish `hSy : UpperTheory.Gal.TranscendenceTraces.Sym π σ m`. Unfold `UpperTheory.Gal.TranscendenceTraces.Sym`. Introduce `Ω _ _ x x' hxx'`.

Take `⟨e, he⟩` from `hsym Ω x x' hxx'`. Conclude with `⟨e, fun j => ⟨(he j).1, congrArg key (he j).2⟩⟩`. Take `⟨w, hw⟩` from `hCE p π σ m hSy`. Use `⟨w, hCW p π σ m w hσ hw, ?_⟩` and prove the remaining obligations. Introduce `Ω _ _ z hz`.

Take `⟨v, hv⟩` from `π.surjective (pt (z ≫ p))`. Take `⟨x, hx, -⟩` from `hPL π Ω (z ≫ p) v hv`. Establish `hcount` using `hw Ω x z hx.symm`. Establish `hbot : (pt (x ≫ π)).asIdeal = ⊥`. Rewrite using `[hx]`.

Unfold `GenPt at hz`. Establish `h0` using `hz (⟨⊥, Ideal.bot_prime⟩ : PrimeSpectrum A) ((PrimeSpectrum.le_iff_specializes _ _).mp bot_le)`. Rewrite using `[← h0]`. Take `⟨⟨j0, hj0, huniq⟩, hcj⟩` from `hgen Ω x z hx.symm hbot`. Establish `hset : {j | x ≫ σ j = z} = {j0}`.

Use extensionality with `j`. Simplify using `only [Set.mem_setOf_eq, Set.mem_singleton_iff]`. Prove the components needed by the constructor for the conclusion. Conclude with `huniq j`. Introduce and unpack `rfl`.

Conclude with `hj0`. Rewrite using `[hcount, hset, finsum_mem_singleton]`. Conclude with `hm j0 Ω z (hcj j0 hj0)`.
-/
theorem UpperTheory.Gal.TranscendenceTraces.normSpec_of :
    SplitCover → CountEx → CountWt → MultPt → PtEx → PtLift → GenBasic → NormSpec := by
  intro hS hCE hCW hMP hPE hPL _
  unfold NormSpec
  intro A B _ _ _ _ _ _
  set p := Spec.map (CommRingCat.ofHom (algebraMap A B)) with hp
  haveI : IsFinite p := by
    rw [hp, IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.mpr inferInstance
  obtain ⟨T, π, ι, σ, c, hπi, hπs, hι, hσ, hsym, hgen⟩ := hS A B
  haveI := hπi
  haveI := hπs
  haveI := hι
  have hk : ∀ s : ↥(Spec (CommRingCat.of B)), ∃ (Ω : Type) (_ : Field Ω) (_ : IsAlgClosed Ω)
      (y : gp Ω ⟶ Spec (CommRingCat.of B)), pt y = s := fun s => hPE _ s
  choose Ωk fk ak yk hyk using hk
  let key : ↥(Spec (CommRingCat.of B)) → ℤ := fun s => letI := fk s; letI := ak s; mult p (Ωk s) (yk s)
  let m : ι → ℤ := fun j => key (c j)
  have hm : ∀ j (Ω : Type) [Field Ω] [IsAlgClosed Ω] (z : gp Ω ⟶ Spec (CommRingCat.of B)),
      c j = pt z → m j = mult p Ω z := by
    intro j Ω _ _ z hz
    letI := fk (c j)
    letI := ak (c j)
    exact hMP p (Ωk (c j)) Ω (yk (c j)) z ((hyk (c j)).trans hz)
  have hSy : UpperTheory.Gal.TranscendenceTraces.Sym π σ m := by
    unfold UpperTheory.Gal.TranscendenceTraces.Sym
    intro Ω _ _ x x' hxx'
    obtain ⟨e, he⟩ := hsym Ω x x' hxx'
    exact ⟨e, fun j => ⟨(he j).1, congrArg key (he j).2⟩⟩
  obtain ⟨w, hw⟩ := hCE p π σ m hSy
  refine ⟨w, hCW p π σ m w hσ hw, ?_⟩
  intro Ω _ _ z hz
  obtain ⟨v, hv⟩ := π.surjective (pt (z ≫ p))
  obtain ⟨x, hx, -⟩ := hPL π Ω (z ≫ p) v hv
  have hcount := hw Ω x z hx.symm
  have hbot : (pt (x ≫ π)).asIdeal = ⊥ := by
    rw [hx]
    unfold GenPt at hz
    have h0 := hz (⟨⊥, Ideal.bot_prime⟩ : PrimeSpectrum A) ((PrimeSpectrum.le_iff_specializes _ _).mp bot_le)
    rw [← h0]
  obtain ⟨⟨j0, hj0, huniq⟩, hcj⟩ := hgen Ω x z hx.symm hbot
  have hset : {j | x ≫ σ j = z} = {j0} := by
    ext j
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · exact huniq j
    · rintro rfl
      exact hj0
  rw [hcount, hset, finsum_mem_singleton]
  exact hm j0 Ω z (hcj j0 hj0)
