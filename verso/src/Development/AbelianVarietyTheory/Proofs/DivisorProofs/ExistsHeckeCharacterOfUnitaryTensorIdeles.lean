import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TwistedLevelValues
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdeles
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsBaseChangeFiniteAdeleRingEquiv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsArchAdeleTensorEquivComplexCmType
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsCompactAdeleRingModNumberField
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsPosNatMemOpenAdeleSubgroup
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsOpenNsmulAdelicCompletionOfVectorSet

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Pj Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host
open Filter Topology Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HeckeTensorRead

/- English proof (translation)
Use `continuous_of_continuousAt_zero g.toAddMonoidHom ?_` and prove the remaining obligations. Introduce `U hU`. Establish `hU0 : U ∈ 𝓝 (0 : FiniteAdeleRing (𝓞 E) E)` using `by simpa using hU`. Establish `hC` using `GlobalTheory.AdeleCocompact.isCompact_integral E`. Establish `h1` using `hC.eventually_forall_of_forall_eventually (x₀ := (0 : FiniteAdeleRing (𝓞 E) E)) (P := fun x y => x * y ∈ U) (fun y _ => (continuous_mul.tendsto' ((0 : FiniteAdeleRing (𝓞 E) E), y) 0 (zero_mul y)) hU0)`.

Take `⟨n, hn⟩` from `((GlobalTheory.AdelicFactorial.tendsto_factorial_finiteAdele E).eventually h1).exists`. Establish `hn0 : ((n.factorial : ℕ) : F) ≠ 0` using `by exact_mod_cast n.factorial_ne_zero`. Set `m : FiniteAdeleRing (𝓞 F) F` to `algebraMap F _ ((n.factorial : ℕ) : F)⁻¹`. Establish `hm : ((n.factorial : ℕ) : FiniteAdeleRing (𝓞 F) F) * m = 1`. Rewrite using `[← map_natCast (algebraMap F (FiniteAdeleRing (𝓞 F) F)), ← map_mul, mul_inv_cancel₀ hn0, map_one]`.

Establish `hO : IsOpen {a : FiniteAdeleRing (𝓞 F) F | ∀ v, a v ∈ v.adicCompletionIntegers F}` using `RestrictedProduct.isOpen_forall_mem fun v => Valued.isOpen_valuationSubring _`. Establish `h2 : (fun a => m * a) ⁻¹' {a : FiniteAdeleRing (𝓞 F) F | ∀ v, a v ∈ v.adicCompletionIntegers F} ∈ 𝓝 0` using `(hO.preimage (continuous_const.mul continuous_id)).mem_nhds (by`. Introduce `v`. Express the relevant statement in the definitionally equal form `(m * 0) v ∈ _`. Rewrite using `[mul_zero]`.

Conclude with `zero_mem _)`. Use `Filter.mem_map.2 (mem_of_superset h2 fun a ha => ?_)` and prove the remaining obligations. Establish `h3` using `hn _ (hg _ ha)`. Rewrite `h3` using `[← map_natCast g, ← map_mul, ← mul_assoc, hm, one_mul]`. Conclude with `h3`.
-/
theorem continuous_of_map_integral {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    (g : FiniteAdeleRing (𝓞 F) F →+* FiniteAdeleRing (𝓞 E) E)
    (hg : ∀ a : FiniteAdeleRing (𝓞 F) F, (∀ v, a v ∈ v.adicCompletionIntegers F) → ∀ v, g a v ∈ v.adicCompletionIntegers E) :
    Continuous g := by
  refine continuous_of_continuousAt_zero g.toAddMonoidHom ?_
  intro U hU
  have hU0 : U ∈ 𝓝 (0 : FiniteAdeleRing (𝓞 E) E) := by simpa using hU
  have hC := GlobalTheory.AdeleCocompact.isCompact_integral E
  have h1 := hC.eventually_forall_of_forall_eventually (x₀ := (0 : FiniteAdeleRing (𝓞 E) E)) (P := fun x y => x * y ∈ U)
    (fun y _ => (continuous_mul.tendsto' ((0 : FiniteAdeleRing (𝓞 E) E), y) 0 (zero_mul y)) hU0)
  obtain ⟨n, hn⟩ := ((GlobalTheory.AdelicFactorial.tendsto_factorial_finiteAdele E).eventually h1).exists
  have hn0 : ((n.factorial : ℕ) : F) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  let m : FiniteAdeleRing (𝓞 F) F := algebraMap F _ ((n.factorial : ℕ) : F)⁻¹
  have hm : ((n.factorial : ℕ) : FiniteAdeleRing (𝓞 F) F) * m = 1 := by
    rw [← map_natCast (algebraMap F (FiniteAdeleRing (𝓞 F) F)), ← map_mul, mul_inv_cancel₀ hn0, map_one]
  have hO : IsOpen {a : FiniteAdeleRing (𝓞 F) F | ∀ v, a v ∈ v.adicCompletionIntegers F} :=
    RestrictedProduct.isOpen_forall_mem fun v => Valued.isOpen_valuationSubring _
  have h2 : (fun a => m * a) ⁻¹' {a : FiniteAdeleRing (𝓞 F) F | ∀ v, a v ∈ v.adicCompletionIntegers F} ∈ 𝓝 0 :=
    (hO.preimage (continuous_const.mul continuous_id)).mem_nhds (by
      intro v
      change (m * 0) v ∈ _
      rw [mul_zero]
      exact zero_mem _)
  refine Filter.mem_map.2 (mem_of_superset h2 fun a ha => ?_)
  have h3 := hn _ (hg _ ha)
  rw [← map_natCast g, ← map_mul, ← mul_assoc, hm, one_mul] at h3
  exact h3

/- English proof (translation)
Use `haveI : IsModuleTopology (Af D.host.F) (Af D.host.F ⊗[D.host.F] D.host.E) := ⟨rfl⟩`. Use `haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _`. Use `haveI : IsTopologicalRing (Af D.host.F ⊗[D.host.F] D.host.E) := IsModuleTopology.isTopologicalRing (Af D.host.F) _`. Use `haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele D.host.F`. Use `haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele D.host.F`.

Use `haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele D.host.E`. Use `haveI := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField D.host.F`. Use `haveI := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField D.host.E`. Take `⟨e0⟩` from `GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := D.host.F) (E := D.host.E) (Af D.host.F)`. Use `haveI : LocallyCompactSpace (Af D.host.F ⊗[D.host.F] D.host.E) := e0.isClosedEmbedding.locallyCompactSpace`.

Use `haveI : SecondCountableTopology (Af D.host.F ⊗[D.host.F] D.host.E) := e0.secondCountableTopology`. Establish `hc : Continuous ι`. Use `IsModuleTopology.continuous_of_ringHom (R := Af D.host.F) ι.toRingHom ?_` and prove the remaining obligations. Use `continuous_of_map_integral _ fun a ha P => ?_` and prove the remaining obligations. Conclude with `(hint (a ⊗ₜ[D.host.F] (1 : D.host.E))).1 (AddSubgroup.subset_closure ⟨a, ha, 1, rfl⟩) P`.

Establish `ho : IsOpenMap ι` using `AddMonoidHom.isOpenMap_of_sigmaCompact ι.toAddEquiv.toAddMonoidHom ι.surjective hc`. Conclude with `⟨hc, (ι.toEquiv.toHomeomorphOfContinuousOpen hc ho).symm.continuous⟩`.
-/
theorem continuous_finite_equiv (D : D7)
    (ι : (Af D.host.F ⊗[D.host.F] D.host.E) ≃+* FiniteAdeleRing (𝓞 D.host.E) D.host.E)
    (hint : ∀ y, y ∈ intAE D ↔ ∀ P : HeightOneSpectrum (𝓞 D.host.E), Valued.v (ι y P) ≤ 1) :
    Continuous ι ∧ Continuous ι.symm := by
  haveI : IsModuleTopology (Af D.host.F) (Af D.host.F ⊗[D.host.F] D.host.E) := ⟨rfl⟩
  haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI : IsTopologicalRing (Af D.host.F ⊗[D.host.F] D.host.E) := IsModuleTopology.isTopologicalRing (Af D.host.F) _
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele D.host.F
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele D.host.F
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele D.host.E
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField D.host.F
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField D.host.E
  obtain ⟨e0⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := D.host.F) (E := D.host.E) (Af D.host.F)
  haveI : LocallyCompactSpace (Af D.host.F ⊗[D.host.F] D.host.E) := e0.isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (Af D.host.F ⊗[D.host.F] D.host.E) := e0.secondCountableTopology
  have hc : Continuous ι := by
    refine IsModuleTopology.continuous_of_ringHom (R := Af D.host.F) ι.toRingHom ?_
    refine continuous_of_map_integral _ fun a ha P => ?_
    exact (hint (a ⊗ₜ[D.host.F] (1 : D.host.E))).1 (AddSubgroup.subset_closure ⟨a, ha, 1, rfl⟩) P
  have ho : IsOpenMap ι :=
    AddMonoidHom.isOpenMap_of_sigmaCompact ι.toAddEquiv.toAddMonoidHom ι.surjective hc
  exact ⟨hc, (ι.toEquiv.toHomeomorphOfContinuousOpen hc ho).symm.continuous⟩

/- English proof (translation)
Use `haveI := h.1`. Use `haveI := h.2.1`. Use `choose θ h1 h2 using fun w : InfinitePlace E => GlobalTheory.InfAdeleCM.exists_hom (F := F) w.embedding`. Take `⟨e, he, hc, hc', -⟩` from `GlobalTheory.Mem.VolInfIso.exists_infAdele_equiv F E σ (InfinitePlace E) (fun w => w.embedding) θ h (by`. Unfold `GlobalTheory.Mem.Vol.IsCMFam`.

Simplify using `only [InfinitePlace.mk_embedding]`. Conclude with `Function.bijective_id) (fun w => ⟨h1 w, h2 w⟩)`. Set `p : InfiniteAdeleRing E ≃+* (InfinitePlace E → ℂ)` to `RingEquiv.piCongrRight fun w => InfinitePlace.Completion.ringEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)`. Establish `hp : Continuous p` using `continuous_pi fun w => (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp (continuous_apply w)`. Establish `hp' : Continuous p.symm` using `continuous_pi fun w => (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).symm.continuous.comp (continuous_apply w)`.

Use `⟨e.trans p.symm, hp'.comp hc, hc'.comp hp, fun x => ?_⟩` and prove the remaining obligations. Rewrite using `[RingEquiv.trans_apply, RingEquiv.symm_apply_eq]`. Use function extensionality and compare the values at `w`. Rewrite using `[he, h1]`. Conclude with `(InfinitePlace.Completion.extensionEmbedding_coe w (WithAbs.toAbs _ x)).symm`.
-/
theorem exists_infinite_equiv (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (h : IsCMExt F E σ) :
    ∃ j : (Ainf F ⊗[F] E) ≃+* InfiniteAdeleRing E, Continuous j ∧ Continuous j.symm ∧
      ∀ x : E, j ((1 : Ainf F) ⊗ₜ[F] x) = algebraMap E (InfiniteAdeleRing E) x := by
  haveI := h.1
  haveI := h.2.1
  choose θ h1 h2 using fun w : InfinitePlace E => GlobalTheory.InfAdeleCM.exists_hom (F := F) w.embedding
  obtain ⟨e, he, hc, hc', -⟩ := GlobalTheory.Mem.VolInfIso.exists_infAdele_equiv F E σ (InfinitePlace E) (fun w => w.embedding) θ h
    (by
      unfold GlobalTheory.Mem.Vol.IsCMFam
      simp only [InfinitePlace.mk_embedding]
      exact Function.bijective_id) (fun w => ⟨h1 w, h2 w⟩)
  let p : InfiniteAdeleRing E ≃+* (InfinitePlace E → ℂ) :=
    RingEquiv.piCongrRight fun w => InfinitePlace.Completion.ringEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)
  have hp : Continuous p := continuous_pi fun w =>
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp
      (continuous_apply w)
  have hp' : Continuous p.symm := continuous_pi fun w =>
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).symm.continuous.comp
      (continuous_apply w)
  refine ⟨e.trans p.symm, hp'.comp hc, hc'.comp hp, fun x => ?_⟩
  rw [RingEquiv.trans_apply, RingEquiv.symm_apply_eq]
  funext w
  rw [he, h1]
  exact (InfinitePlace.Completion.extensionEmbedding_coe w (WithAbs.toAbs _ x)).symm

/- English proof (translation)
Take `⟨hee, ⟨v, ε, ⟨α, rfl, -, -⟩, hor⟩, hx⟩` from `he`. Establish `hε1 : infPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α)) = 0` using `TensorProduct.zero_tmul _ _`. Establish `hinf : infPart D e = 0`. Break down `hor with ⟨h1, h2⟩ | h` into its components or cases. Establish `: e = e * (e + cA D e)` using `by rw [mul_add, hee, h1, add_zero]`.

Rewrite using `[this, h2, RingHom.map_mul, hε1, mul_zero]`. Rewrite using `[h, hε1]`. Take `⟨f, hf⟩ : ∃ f, f = ι (finPart D e)` from `⟨_, rfl⟩`. Establish `hff : f * f = f` using `by rw [hf, ← map_mul, ← RingHom.map_mul, hee]`. Establish `hf01 : ∀ R, f R ≠ 0 → f R = 1`.

Introduce `R hR`. Establish `: f R * f R = f R * 1` using `by rw [← GlobalTheory.PlaceIdem.mul_ap, hff, mul_one]`. Conclude with `mul_left_cancel₀ hR this`. Establish `key : ∀ x : 𝓞 D.host.E, x ≠ 0 → (x ∈ P.asIdeal ↔ ∃ R, f R ≠ 0 ∧ x ∈ R.asIdeal)`. Introduce `x hx0`.

Establish `h1 : finPart D (incA D ((x : D.host.E)⁻¹)) = (1 : Af D.host.F) ⊗ₜ[D.host.F] ((x : D.host.E)⁻¹)` using `rfl`. Rewrite using `[hx x hx0, hint, RingHom.map_mul, map_mul, ← hf, h1, hι, not_forall]`. Use `exists_congr fun R => ?_` and prove the remaining obligations. Rewrite using `[GlobalTheory.PlaceIdem.mul_ap]`. Distinguish the cases in `hR : f R = 0`.

Simplify using `[hR]`. Rewrite using `[hf01 R hR, one_mul, GlobalTheory.PlaceIdem.val_inv_le_one R hx0]`. Simplify using the standard rewrite rules. Establish `h0 : ∀ Q, Q ≠ P → f Q = 0`. Introduce `Q hQ`.

Assume the negation of the conclusion as `hne`. Use `hQ (HeightOneSpectrum.ext (Q.isMaximal.eq_of_le P.isPrime.ne_top fun x hxQ => ?_))` and prove the remaining obligations. Distinguish the cases in `hx0 : x = 0`. Rewrite using `[hx0]`. Conclude with `zero_mem _`.

Conclude with `(key x hx0).2 ⟨Q, hne, hxQ⟩`. Rewrite using `[← hf]`. Use `⟨hinf, ?_, h0⟩` and prove the remaining obligations. Take `⟨x, hxP, hx0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot P.ne_bot`. Take `⟨R, hR, -⟩` from `(key x hx0).1 hxP`.

Distinguish the cases in `hRP : R = P`. Substitute `hRP` using the available equality. Conclude with `hf01 _ hR`. Conclude with `absurd (h0 R hRP) hR`.
-/
theorem isPlIdem_parts (D : D7)
    (ι : (Af D.host.F ⊗[D.host.F] D.host.E) ≃+* FiniteAdeleRing (𝓞 D.host.E) D.host.E)
    (hι : ∀ x : D.host.E, ι ((1 : Af D.host.F) ⊗ₜ[D.host.F] x) = algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E) x)
    (hint : ∀ y, y ∈ intAE D ↔ ∀ P : HeightOneSpectrum (𝓞 D.host.E), Valued.v (ι y P) ≤ 1)
    {e : AE D} {P : HeightOneSpectrum (𝓞 D.host.E)} (he : IsPlIdem D e P) :
    infPart D e = 0 ∧ ι (finPart D e) P = 1 ∧ ∀ Q, Q ≠ P → ι (finPart D e) Q = 0 := by
  obtain ⟨hee, ⟨v, ε, ⟨α, rfl, -, -⟩, hor⟩, hx⟩ := he
  have hε1 : infPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α)) = 0 :=
    TensorProduct.zero_tmul _ _
  have hinf : infPart D e = 0 := by
    rcases hor with ⟨h1, h2⟩ | h
    · have : e = e * (e + cA D e) := by rw [mul_add, hee, h1, add_zero]
      rw [this, h2, RingHom.map_mul, hε1, mul_zero]
    · rw [h, hε1]
  obtain ⟨f, hf⟩ : ∃ f, f = ι (finPart D e) := ⟨_, rfl⟩
  have hff : f * f = f := by rw [hf, ← map_mul, ← RingHom.map_mul, hee]
  have hf01 : ∀ R, f R ≠ 0 → f R = 1 := by
    intro R hR
    have : f R * f R = f R * 1 := by rw [← GlobalTheory.PlaceIdem.mul_ap, hff, mul_one]
    exact mul_left_cancel₀ hR this
  have key : ∀ x : 𝓞 D.host.E, x ≠ 0 → (x ∈ P.asIdeal ↔ ∃ R, f R ≠ 0 ∧ x ∈ R.asIdeal) := by
    intro x hx0
    have h1 : finPart D (incA D ((x : D.host.E)⁻¹)) = (1 : Af D.host.F) ⊗ₜ[D.host.F] ((x : D.host.E)⁻¹) := rfl
    rw [hx x hx0, hint, RingHom.map_mul, map_mul, ← hf, h1, hι, not_forall]
    refine exists_congr fun R => ?_
    rw [GlobalTheory.PlaceIdem.mul_ap]
    by_cases hR : f R = 0
    · simp [hR]
    · rw [hf01 R hR, one_mul, GlobalTheory.PlaceIdem.val_inv_le_one R hx0]
      simp
  have h0 : ∀ Q, Q ≠ P → f Q = 0 := by
    intro Q hQ
    by_contra hne
    refine hQ (HeightOneSpectrum.ext (Q.isMaximal.eq_of_le P.isPrime.ne_top fun x hxQ => ?_))
    by_cases hx0 : x = 0
    · rw [hx0]; exact zero_mem _
    · exact (key x hx0).2 ⟨Q, hne, hxQ⟩
  rw [← hf]
  refine ⟨hinf, ?_, h0⟩
  obtain ⟨x, hxP, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot P.ne_bot
  obtain ⟨R, hR, -⟩ := (key x hx0).1 hxP
  by_cases hRP : R = P
  · subst hRP
    exact hf01 _ hR
  · exact absurd (h0 R hRP) hR

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem map_loc {R S : Type} [CommRing R] [CommRing S] (q : R →+* S) (e a : R) :
    q (1 + e * (a - 1)) = 1 + q e * (q a - 1) := by
  simp

/- English proof (translation)
Substitute `ha` using the available equality. Use `GlobalTheory.PlaceIdem.adele_ext fun Q => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `1 + f Q * (algebraMap E (Q.adicCompletion E) k - 1) = Function.update (fun w : HeightOneSpectrum (𝓞 E) => (1 : w.adicCompletion E)) P (algebraMap E _ k) Q`. Distinguish the cases in `hQ : Q = P`. Substitute `hQ` using the available equality.

Rewrite using `[h1, Function.update_self]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h0 Q hQ, Function.update_of_ne hQ]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem loc_eq_finSingle {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E))
    (f a : FiniteAdeleRing (𝓞 E) E) (k : E) (ha : a = algebraMap E _ k) (h1 : f P = 1) (h0 : ∀ Q, Q ≠ P → f Q = 0) :
    1 + f * (a - 1) = Neutral.B1.finiteSingle E P (algebraMap E _ k) := by
  subst ha
  refine GlobalTheory.PlaceIdem.adele_ext fun Q => ?_
  classical
  change 1 + f Q * (algebraMap E (Q.adicCompletion E) k - 1) =
    Function.update (fun w : HeightOneSpectrum (𝓞 E) => (1 : w.adicCompletion E)) P (algebraMap E _ k) Q
  by_cases hQ : Q = P
  · subst hQ
    rw [h1, Function.update_self]
    ring
  · rw [h0 Q hQ, Function.update_of_ne hQ]
    ring

/- English proof (translation)
Take `⟨ι, hι, hint, -⟩` from `GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D`. Take `⟨hιc, hιc'⟩` from `continuous_finite_equiv D ι hint`. Take `⟨j, hjc, hjc', hj⟩` from `exists_infinite_equiv D.host.F D.host.E D.sp.cm.sig ⟨D.sp.cm.totReal, D.sp.cm.cmUnram.1, D.sp.cm.deg2, D.sp.cm.cmUnram.2.1⟩`. Take `⟨s, hs, hsc, hsc'⟩` from `GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E`. Set `Φ : AE D ≃+* AdeleRing (𝓞 D.host.E) D.host.E` to `s.trans (j.prodCongr ι)`.

Establish `hΦ : ∀ z, Φ z = (j (infPart D z), ι (finPart D z))` using `fun z => Prod.ext (congrArg j (hs z).1) (congrArg ι (hs z).2)`. Use `⟨Φ, (hjc.prodMap hιc).comp hsc, hsc'.comp (hjc'.prodMap hιc'), fun x => ?_, fun P e he k => ?_⟩` and prove the remaining obligations. Rewrite using `[hΦ]`. Conclude with `Prod.ext (hj x) (hι x)`. Take `⟨h1, h2, h3⟩` from `isPlIdem_parts D ι hι hint he`.

Rewrite using `[hΦ]`. Use `Prod.ext ?_ ?_` and prove the remaining obligations. Establish `h5 : j (infPart D e) = 0` using `by rw [h1]; exact j.map_zero`. Conclude with `(map_loc (j.toRingHom.comp (infPart D)) e _).trans (by`. Express the relevant statement in the definitionally equal form `1 + j (infPart D e) * _ = 1`.

Rewrite using `[h5, zero_mul, add_zero])`. Establish `h4 : ι (finPart D (incA D (k : D.host.E))) = algebraMap D.host.E _ (k : D.host.E)` using `hι k`. Use `(map_loc (ι.toRingHom.comp (finPart D)) e _).trans ?_` and prove the remaining obligations. Conclude with `loc_eq_finSingle P _ _ _ h4 h2 h3`.
-/
theorem exists_adele_tensor_equiv (D : D7) :
    ∃ Φ : AE D ≃+* AdeleRing (𝓞 D.host.E) D.host.E, Continuous Φ ∧ Continuous Φ.symm ∧
      (∀ x : D.host.E, Φ (incA D x) = algebraMap D.host.E (AdeleRing (𝓞 D.host.E) D.host.E) x) ∧
      ∀ (P : HeightOneSpectrum (𝓞 D.host.E)) (e : AE D), IsPlIdem D e P → ∀ k : D.host.Eˣ,
        Φ (locE D e (k : D.host.E)) = ((localIdele D.host.E P (atFin P k) : Ideles D.host.E) : AdeleRing (𝓞 D.host.E) D.host.E) := by
  obtain ⟨ι, hι, hint, -⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  obtain ⟨hιc, hιc'⟩ := continuous_finite_equiv D ι hint
  obtain ⟨j, hjc, hjc', hj⟩ := exists_infinite_equiv D.host.F D.host.E D.sp.cm.sig
    ⟨D.sp.cm.totReal, D.sp.cm.cmUnram.1, D.sp.cm.deg2, D.sp.cm.cmUnram.2.1⟩
  obtain ⟨s, hs, hsc, hsc'⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  let Φ : AE D ≃+* AdeleRing (𝓞 D.host.E) D.host.E := s.trans (j.prodCongr ι)
  have hΦ : ∀ z, Φ z = (j (infPart D z), ι (finPart D z)) := fun z =>
    Prod.ext (congrArg j (hs z).1) (congrArg ι (hs z).2)
  refine ⟨Φ, (hjc.prodMap hιc).comp hsc, hsc'.comp (hjc'.prodMap hιc'), fun x => ?_, fun P e he k => ?_⟩
  · rw [hΦ]
    exact Prod.ext (hj x) (hι x)
  · obtain ⟨h1, h2, h3⟩ := isPlIdem_parts D ι hι hint he
    rw [hΦ]
    refine Prod.ext ?_ ?_
    · have h5 : j (infPart D e) = 0 := by rw [h1]; exact j.map_zero
      exact (map_loc (j.toRingHom.comp (infPart D)) e _).trans (by
        change 1 + j (infPart D e) * _ = 1
        rw [h5, zero_mul, add_zero])
    · have h4 : ι (finPart D (incA D (k : D.host.E))) = algebraMap D.host.E _ (k : D.host.E) := hι k
      refine (map_loc (ι.toRingHom.comp (finPart D)) e _).trans ?_
      exact loc_eq_finSingle P _ _ _ h4 h2 h3

/- English proof (translation)
Introduce `D c hc`. Take `⟨Φ, -, hΦ, h1, h2⟩` from `exists_adele_tensor_equiv D`. Set `u : Ideles D.host.E →* (AE D)ˣ` to `Units.map Φ.symm.toRingHom.toMonoidHom`. Establish `hu : Continuous u` using `Continuous.units_map _ hΦ`. Establish `ht : Continuous (Circle.toUnits : Circle →* ℂˣ)` using `Units.continuous_iff.2 ⟨continuous_subtype_val, by`.

Establish `h : Continuous fun z : Circle => ((z⁻¹ : Circle) : ℂ)` using `continuous_subtype_val.comp continuous_inv`. Use `h.congr fun z => ?_` and prove the remaining obligations. Use the proof step `simp⟩`. Use `⟨⟨Circle.toUnits.comp (c.comp u), ht.comp (hc.1.comp hu), fun k => ?_⟩, hc, fun P e he k x hx => ?_⟩` and prove the remaining obligations. Establish `: u (diagUnits D.host.E k) = Units.map (incA D).toMonoidHom k` using `Units.ext (Φ.symm_apply_eq.2 (h1 k).symm)`.

Express the relevant statement in the definitionally equal form `Circle.toUnits (c (u _)) = 1`. Rewrite using `[this, hc.2, map_one]`. Establish `: x = u (localIdele D.host.E P (atFin P k))` using `Units.ext (Φ.eq_symm_apply.2 (by rw [hx, h2 P e he k]))`. Rewrite using `[this]`. Both sides reduce to the same expression.
-/
theorem exists_hchar_chrEq : ∀ (D : D7) (c : (AE D)ˣ →* Circle), IsHeckeChar D c →
    ∃ χ : Formalism.L2.Host.HChar D.host.E, ChrEq c χ := by
  intro D c hc
  obtain ⟨Φ, -, hΦ, h1, h2⟩ := exists_adele_tensor_equiv D
  let u : Ideles D.host.E →* (AE D)ˣ := Units.map Φ.symm.toRingHom.toMonoidHom
  have hu : Continuous u := Continuous.units_map _ hΦ
  have ht : Continuous (Circle.toUnits : Circle →* ℂˣ) :=
    Units.continuous_iff.2 ⟨continuous_subtype_val, by
      have h : Continuous fun z : Circle => ((z⁻¹ : Circle) : ℂ) := continuous_subtype_val.comp continuous_inv
      refine h.congr fun z => ?_
      simp⟩
  refine ⟨⟨Circle.toUnits.comp (c.comp u), ht.comp (hc.1.comp hu), fun k => ?_⟩, hc, fun P e he k x hx => ?_⟩
  · have : u (diagUnits D.host.E k) = Units.map (incA D).toMonoidHom k :=
      Units.ext (Φ.symm_apply_eq.2 (h1 k).symm)
    change Circle.toUnits (c (u _)) = 1
    rw [this, hc.2, map_one]
  · have : x = u (localIdele D.host.E P (atFin P k)) :=
      Units.ext (Φ.eq_symm_apply.2 (by rw [hx, h2 P e he k]))
    rw [this]
    rfl

end GlobalTheory.HeckeTensorRead
