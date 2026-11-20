import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsHTFrameCpAndNonempty
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagNeZeroOfLinearIndependent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateInclusionRaynaudExtensionAlgebraicPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMapToModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilCharSurjectiveAndMapRangeAl
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.GradedDifferentComparison
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.PadicValNatAbsNormEqZero

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain
open scoped TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.EigenSplit GlobalTheory.Frames GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovHt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CovHt.FrameCmp

section Different

variable {C : Type} [Field C] [IsAlgClosed C] [CharZero C] {v : Valuation C ℝ≥0} {O : Type} [CommRing O] [Algebra O C]
  {E : Type} [Field E] [NumberField E]

omit [IsAlgClosed C] [CharZero C] in

/- English proof (translation)
Use `haveI := Fact.mk hp`. Use `haveI : IsDomain O := hv.hom_inj.isDomain _`. Use `haveI := ValuationRing.of_integers v hv`. Take `⟨δ, hδ, -⟩` from `GlobalTheory.IndefiniteRowSideFullHecke.GradedDifferentComparison.exists_generator_different hv τ`. Use `⟨δ, hδ ▸ Ideal.mem_span_singleton_self δ, ?_⟩` and prove the remaining obligations.

Establish `hd : (discr E).natAbs ≠ 0` using `Int.natAbs_ne_zero.mpr (discr_ne_zero E)`. Take `⟨a, m, hm, hdisc⟩` from `Nat.exists_eq_pow_mul_and_not_dvd hd p hp.ne_one`. Establish `hm0 : m ≠ 0` using `by rintro rfl; exact hm (dvd_zero _)`. Establish `ha : padicValNat p (discr E).natAbs = a`. Rewrite using `[hdisc, padicValNat.mul (pow_ne_zero _ hp.ne_zero) hm0, padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd hm, add_zero]`.

Rewrite using `[ha]`. Use `set σ := embO hv τ`. Use `set P : Ideal (𝓞 E) := (IsLocalRing.maximalIdeal O).comap σ with hP`. Establish `hPp : P.IsPrime` using `Ideal.comap_isPrime σ _`. Establish `hpP : (p : 𝓞 E) ∈ P`.

Rewrite using `[hP, Ideal.mem_comap, map_natCast]`. Conclude with `hO`. Establish `hp0 : (p : 𝓞 E) ≠ 0` using `Nat.cast_ne_zero.2 hp.ne_zero`. Establish `hP0 : P ≠ ⊥` using `fun h => hp0 ((Submodule.mem_bot _).1 (h ▸ hpP))`. Use `haveI : P.IsMaximal := hPp.isMaximal hP0`.

Establish `hexp` using `ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.diffExp E p a m hp hm hdisc P hPp hpP`. Take `⟨Q, hQ, hD⟩` from `Ideal.eq_prime_pow_mul_coprime (differentIdeal_ne_bot (A := ℤ) (B := 𝓞 E)) P`. Take `⟨Q', -, hI⟩` from `Ideal.eq_prime_pow_mul_coprime (I := Ideal.span {(p : 𝓞 E)}) (by rwa [Ne, Ideal.span_singleton_eq_bot]) P`. Establish `hQm : Q.map σ = ⊤`. Assume the negation of the conclusion as `h`.

Establish `h2 : Q ≤ P` using `Ideal.map_le_iff_le_comap.1 (IsLocalRing.le_maximalIdeal h)`. Conclude with `hPp.ne_top (by rw [← hQ, sup_eq_left.2 h2])`. Establish `h1` using `Ideal.le_of_dvd (Dvd.intro _ hI.symm) (Ideal.mem_span_singleton_self _)`. Establish `h2` using `Ideal.mem_map_of_mem σ (Ideal.pow_mem_pow h1 a)`. Rewrite `h2` using `[← pow_mul, mul_comm, ← hexp, pow_mul, Ideal.map_pow, map_pow, map_natCast]`.

Establish `h3` using `congrArg (Ideal.map σ) hD`. Rewrite `h3` using `[Ideal.map_mul, hQm, Ideal.mul_top]`. Rewrite `h2` using `[← h3, hδ, Ideal.span_singleton_pow, Ideal.mem_span_singleton]`. Then use the resulting hypothesis.
-/
theorem exists_delta [IsGalois ℚ E] (hv : v.Integers O) {p : ℕ} (hp : p.Prime) (hO : ¬ IsUnit (p : O)) (τ : E →+* C) :
    ∃ δ ∈ (differentIdeal ℤ (𝓞 E)).map (embO hv τ),
      δ ^ Module.finrank ℚ E ∣ (p : O) ^ padicValNat p (discr E).natAbs := by
  classical
  haveI := Fact.mk hp
  haveI : IsDomain O := hv.hom_inj.isDomain _
  haveI := ValuationRing.of_integers v hv
  obtain ⟨δ, hδ, -⟩ := GlobalTheory.IndefiniteRowSideFullHecke.GradedDifferentComparison.exists_generator_different hv τ
  refine ⟨δ, hδ ▸ Ideal.mem_span_singleton_self δ, ?_⟩
  have hd : (discr E).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (discr_ne_zero E)
  obtain ⟨a, m, hm, hdisc⟩ := Nat.exists_eq_pow_mul_and_not_dvd hd p hp.ne_one
  have hm0 : m ≠ 0 := by rintro rfl; exact hm (dvd_zero _)
  have ha : padicValNat p (discr E).natAbs = a := by
    rw [hdisc, padicValNat.mul (pow_ne_zero _ hp.ne_zero) hm0, padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd hm, add_zero]
  rw [ha]
  set σ := embO hv τ
  set P : Ideal (𝓞 E) := (IsLocalRing.maximalIdeal O).comap σ with hP
  have hPp : P.IsPrime := Ideal.comap_isPrime σ _
  have hpP : (p : 𝓞 E) ∈ P := by
    rw [hP, Ideal.mem_comap, map_natCast]
    exact hO
  have hp0 : (p : 𝓞 E) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have hP0 : P ≠ ⊥ := fun h => hp0 ((Submodule.mem_bot _).1 (h ▸ hpP))
  haveI : P.IsMaximal := hPp.isMaximal hP0
  have hexp := ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.diffExp E p a m hp hm hdisc P hPp hpP
  obtain ⟨Q, hQ, hD⟩ := Ideal.eq_prime_pow_mul_coprime (differentIdeal_ne_bot (A := ℤ) (B := 𝓞 E)) P
  obtain ⟨Q', -, hI⟩ := Ideal.eq_prime_pow_mul_coprime
    (I := Ideal.span {(p : 𝓞 E)}) (by rwa [Ne, Ideal.span_singleton_eq_bot]) P
  have hQm : Q.map σ = ⊤ := by
    by_contra h
    have h2 : Q ≤ P := Ideal.map_le_iff_le_comap.1 (IsLocalRing.le_maximalIdeal h)
    exact hPp.ne_top (by rw [← hQ, sup_eq_left.2 h2])
  have h1 := Ideal.le_of_dvd (Dvd.intro _ hI.symm) (Ideal.mem_span_singleton_self _)
  have h2 := Ideal.mem_map_of_mem σ (Ideal.pow_mem_pow h1 a)
  rw [← pow_mul, mul_comm, ← hexp, pow_mul, Ideal.map_pow, map_pow, map_natCast] at h2
  have h3 := congrArg (Ideal.map σ) hD
  rw [Ideal.map_mul, hQm, Ideal.mul_top] at h3
  rwa [← h3, hδ, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h2

/- English proof (translation)
Set `B` to `integralBasis E`. Establish `hc : ∀ i, ∃ c : 𝓞 E, (c : E) = B.traceDual i * d` using `fun i => by`. Establish `hx : B.traceDual i ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)`. Rewrite using `[FractionalIdeal.mem_dual (by simp)]`. Introduce `a ha`.

Take `⟨y, rfl⟩` from `(FractionalIdeal.mem_one_iff _).1 ha`. Use `⟨(RingOfIntegers.basis E).repr y i, ?_⟩` and prove the remaining obligations. Rewrite using `[← integralBasis_repr_apply]`. Establish `h` using `B.traceDual.traceDual_repr_apply (algebraMap (𝓞 E) E y) i`. Rewrite `h` using `[B.traceDual_traceDual, Algebra.traceForm_apply, mul_comm]`.

Conclude with `h`. Establish `hdd : (d : E) ∈ ((differentIdeal ℤ (𝓞 E) : Ideal (𝓞 E)) : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)` using `(FractionalIdeal.mem_coeIdeal _).2 ⟨d, hd, rfl⟩`. Rewrite `hdd` using `[coeIdeal_differentIdeal ℤ ℚ]`. Establish `hm` using `FractionalIdeal.mul_mem_mul hx hdd`. Rewrite `hm` using `[mul_inv_cancel₀ (FractionalIdeal.dual_ne_zero ℤ ℚ (by simp))]`.

Conclude with `(FractionalIdeal.mem_one_iff _).1 hm`. Use `choose c hc using hc`. Use `⟨_, inferInstance, RingOfIntegers.basis E, c, fun φ ψ => ?_⟩` and prove the remaining obligations. Establish `h1 : (Matrix.of fun i (χ : E →+* C) => χ (B i)) * (Matrix.of fun (χ : E →+* C) i => χ (B.traceDual i)) = 1`. Use extensionality with `i j`.

Establish `h` using `trace_eq_sum_embeddings (K := ℚ) (L := E) C (x := B i * B.traceDual j)`. Rewrite using `[Matrix.mul_apply, Matrix.one_apply]`. Simplify using `only [Matrix.of_apply, ← map_mul]`. Use `(Fintype.sum_equiv (RingHom.equivRatAlgHom E C) _ _ fun _ => rfl).trans (h.symm.trans ?_)` and prove the remaining obligations. Rewrite using `[B.trace_mul_traceDual]`.

Apply the tactic sequence `split_ifs <;> simp`. Establish `h2` using `(Matrix.mul_eq_one_comm_of_card_eq _ _ _ (by rw [NumberField.Embeddings.card, Module.finrank_eq_card_basis B])).1 h1`. Establish `h3` using `congrFun (congrFun h2 ψ) φ`. Rewrite `h3` using `[Matrix.mul_apply, Matrix.one_apply]`. Simplify using `only [Matrix.of_apply] at h3`.

Establish `e : ∀ i, φ (RingOfIntegers.basis E i : 𝓞 E) * ψ (c i) = ψ (B.traceDual i) * φ (B i) * ψ d` using `fun i => by`. Rewrite using `[hc, map_mul, integralBasis_apply]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [e, ← Finset.sum_mul, h3]`. Use `split_ifs with h`.

Rewrite using `[h, one_mul]`. Rewrite using `[zero_mul]`.
-/
theorem exists_sum_eq [DecidableEq (E →+* C)] {d : 𝓞 E} (hd : d ∈ differentIdeal ℤ (𝓞 E)) :
    ∃ (ι : Type) (_ : Fintype ι) (b c : ι → 𝓞 E), ∀ φ ψ : E →+* C,
      ∑ i, φ (b i) * ψ (c i) = if ψ = φ then φ d else 0 := by
  classical
  let B := integralBasis E
  have hc : ∀ i, ∃ c : 𝓞 E, (c : E) = B.traceDual i * d := fun i => by
    have hx : B.traceDual i ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) := by
      rw [FractionalIdeal.mem_dual (by simp)]
      intro a ha
      obtain ⟨y, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 ha
      refine ⟨(RingOfIntegers.basis E).repr y i, ?_⟩
      rw [← integralBasis_repr_apply]
      have h := B.traceDual.traceDual_repr_apply (algebraMap (𝓞 E) E y) i
      rw [B.traceDual_traceDual, Algebra.traceForm_apply, mul_comm] at h
      exact h
    have hdd : (d : E) ∈ ((differentIdeal ℤ (𝓞 E) : Ideal (𝓞 E)) : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) :=
      (FractionalIdeal.mem_coeIdeal _).2 ⟨d, hd, rfl⟩
    rw [coeIdeal_differentIdeal ℤ ℚ] at hdd
    have hm := FractionalIdeal.mul_mem_mul hx hdd
    rw [mul_inv_cancel₀ (FractionalIdeal.dual_ne_zero ℤ ℚ (by simp))] at hm
    exact (FractionalIdeal.mem_one_iff _).1 hm
  choose c hc using hc
  refine ⟨_, inferInstance, RingOfIntegers.basis E, c, fun φ ψ => ?_⟩
  have h1 : (Matrix.of fun i (χ : E →+* C) => χ (B i)) * (Matrix.of fun (χ : E →+* C) i => χ (B.traceDual i)) = 1 := by
    ext i j
    have h := trace_eq_sum_embeddings (K := ℚ) (L := E) C (x := B i * B.traceDual j)
    rw [Matrix.mul_apply, Matrix.one_apply]
    simp only [Matrix.of_apply, ← map_mul]
    refine (Fintype.sum_equiv (RingHom.equivRatAlgHom E C) _ _ fun _ => rfl).trans (h.symm.trans ?_)
    rw [B.trace_mul_traceDual]
    split_ifs <;> simp
  have h2 := (Matrix.mul_eq_one_comm_of_card_eq _ _ _
    (by rw [NumberField.Embeddings.card, Module.finrank_eq_card_basis B])).1 h1
  have h3 := congrFun (congrFun h2 ψ) φ
  rw [Matrix.mul_apply, Matrix.one_apply] at h3
  simp only [Matrix.of_apply] at h3
  have e : ∀ i, φ (RingOfIntegers.basis E i : 𝓞 E) * ψ (c i) = ψ (B.traceDual i) * φ (B i) * ψ d := fun i => by
    rw [hc, map_mul, integralBasis_apply]; ring
  simp only [e, ← Finset.sum_mul, h3]
  split_ifs with h
  · rw [h, one_mul]
  · rw [zero_mul]

/- English proof (translation)
Use `Submodule.span_induction (p := fun δ _ => δ • proj (isSplitting_embO hv) ρ φ x ∈ X) ?_ (by simp) (fun a b _ _ ha hb => by rw [add_smul]; exact X.add_mem ha hb) (fun a b _ hb => by rw [smul_eq_mul, mul_smul]; exact X.smul_mem a hb) hδ` and prove the remaining obligations. Introduce and unpack `_ ⟨d, hd, rfl⟩`. Take `⟨ι, _, b, c, h⟩` from `exists_sum_eq (C := C) hd`. Establish `e : φ d • idem (isSplitting_embO hv) φ = ∑ i, φ (b i) ⊗ₜ[ℤ] c i` using `(isSplitting_embO hv).1 (by`. Use extensionality with `ψ`.

Rewrite using `[map_smul, splitMap_idem, map_sum, Finset.sum_apply]`. Simplify using `only [splitMap_tmul, RingHom.comp_apply, algebraMap_embO, h, Pi.smul_apply, Pi.single_apply]`. Apply the tactic sequence `split_ifs <;> simp)`. Rewrite using `[← algebraMap_smul C, algebraMap_embO, proj, ← LinearMap.smul_apply, ← map_smul, e, map_sum, LinearMap.sum_apply]`. Use `X.sum_mem fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[tensorAction_tmul, ← algebraMap_embO hv, algebraMap_smul]`. Conclude with `X.smul_mem _ (hX _ _ hx)`.
-/
theorem smul_proj_mem [DecidableEq (E →+* C)] (hv : v.Integers O) {U : Type} [AddCommGroup U] [Module C U] [Module O U]
    [IsScalarTower O C U] (ρ : 𝓞 E →+* Module.End C U) {X : Submodule O U} (hX : ∀ a, ∀ x ∈ X, ρ a x ∈ X)
    (φ : E →+* C) {δ : O} (hδ : δ ∈ (differentIdeal ℤ (𝓞 E)).map (embO hv φ)) {x : U} (hx : x ∈ X) :
    δ • proj (isSplitting_embO hv) ρ φ x ∈ X := by
  refine Submodule.span_induction (p := fun δ _ => δ • proj (isSplitting_embO hv) ρ φ x ∈ X) ?_ (by simp)
    (fun a b _ _ ha hb => by rw [add_smul]; exact X.add_mem ha hb)
    (fun a b _ hb => by rw [smul_eq_mul, mul_smul]; exact X.smul_mem a hb) hδ
  rintro _ ⟨d, hd, rfl⟩
  obtain ⟨ι, _, b, c, h⟩ := exists_sum_eq (C := C) hd
  have e : φ d • idem (isSplitting_embO hv) φ = ∑ i, φ (b i) ⊗ₜ[ℤ] c i := (isSplitting_embO hv).1 (by
    ext ψ
    rw [map_smul, splitMap_idem, map_sum, Finset.sum_apply]
    simp only [splitMap_tmul, RingHom.comp_apply, algebraMap_embO, h, Pi.smul_apply, Pi.single_apply]
    split_ifs <;> simp)
  rw [← algebraMap_smul C, algebraMap_embO, proj, ← LinearMap.smul_apply, ← map_smul, e, map_sum, LinearMap.sum_apply]
  refine X.sum_mem fun i _ => ?_
  rw [tensorAction_tmul, ← algebraMap_embO hv, algebraMap_smul]
  exact X.smul_mem _ (hX _ _ hx)

end Different

section Point

variable {p : ℕ} [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C] {v : Valuation C ℝ≥0}
  {O : Type} [CommRing O] [Algebra O C] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C]
  {Λ : Type} [CommRing Λ] [StarRing Λ] (P : Point p v O Λ)

/- English proof (translation)
Proceed by induction on `s using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add x y hx hy => rw [map_add, map_add]`. Conclude with `add_mem hx hy`. Consider the case `tmul c t`.

Take `⟨b, hb⟩` from `(P.mem_latT_iff w).1 hw t`. Establish `: (algebraMap O C c ⊗ₜ t : P.V) = algebraMap O C c • (1 : C) ⊗ₜ t`. Rewrite using `[TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]`. Rewrite using `[P.inclT_tmul, this, map_smul, ← hb]`. Conclude with `⟨c * b, map_mul _ _ _⟩`.
-/
theorem pairV_inclT {w : P.V} (hw : w ∈ P.latT) (s : O ⊗[ℤ_[p]] P.T) :
    P.pairV w (P.inclT s) ∈ (algebraMap O C).range := by
  induction s using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add]; exact add_mem hx hy
  | tmul c t =>
    obtain ⟨b, hb⟩ := (P.mem_latT_iff w).1 hw t
    have : (algebraMap O C c ⊗ₜ t : P.V) = algebraMap O C c • (1 : C) ⊗ₜ t := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
    rw [P.inclT_tmul, this, map_smul, ← hb]
    exact ⟨c * b, map_mul _ _ _⟩

omit [IsAlgClosed C] [CharZero C] in

/- English proof (translation)
Take `⟨s, rfl⟩` from `hx`. Proceed by induction on `s using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add x y hx hy => rw [map_add, map_add]`. Conclude with `add_mem hx hy`.

Consider the case `tmul c t => exact ⟨c ⊗ₜ P.actT a t, by rw [P.inclT_tmul, P.inclT_tmul]; rfl⟩`.
-/
theorem actV_mem (a : Λ) (x : P.V) (hx : x ∈ P.latT) : P.actV a x ∈ P.latT := by
  obtain ⟨s, rfl⟩ := hx
  induction s using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add]; exact add_mem hx hy
  | tmul c t => exact ⟨c ⊗ₜ P.actT a t, by rw [P.inclT_tmul, P.inclT_tmul]; rfl⟩

variable [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O]

/- English proof (translation)
Use `haveI := P.isLocalRing`. Use `haveI : IsDomain O := P.integers.hom_inj.isDomain _`. Take `⟨e₁, h₁, h₂⟩` from `OmegaRank.exists_param P.G (OmegaRank.smoothDim_model P)`. Take `⟨e₂, h₃, h₄⟩` from `OmegaRank.exists_lieEquiv P`. Set `e` to `e₁.trans e₂`.

Establish `hadd : ∀ c d, e (c + d) = lieAdd (e c) (e d)` using `fun c d => Subtype.ext (h₃ _ _ _ (h₁ c d))`. Establish `hsm : ∀ (b : O) c, e (b • c) = AvDefs.lieScale P.Gt b (e c)` using `fun b c => Subtype.ext (h₄ b _ _ (h₂ b c))`. Set `L : (Fin P.A.g → O) →ₗ[O] P.V` to `{ toFun := fun c => P.bLie (e c) map_add' := fun c d => by rw [hadd, P.bLie_add] map_smul' := fun b c => by rw [hsm, P.bLie_scale]; rfl }`. Establish `hL : ∀ y, P.bLie y = ∑ i, e.symm y i • L (Pi.single i 1)` using `fun y => by`. Establish `h : L (e.symm y) = P.bLie y` using `congrArg P.bLie (e.apply_symm_apply y)`.

Simplify using `only [← map_smul, ← map_sum, ← h, ← Pi.single_smul, smul_eq_mul, _root_.mul_one, Finset.univ_sum_single]`. Establish `ht : ∀ i, ∃ s : O ⊗[ℤ_[p]] P.T, ∀ y, P.pairV (P.bLie y) (P.inclT s) = algebraMap O C (a * e.symm y i)` using `fun i => by`. Establish `hf : (fun y => e.symm y i) ∈ omega P.Gt` using `⟨fun y z h => by`. Take `⟨c, rfl⟩` from `e.surjective y`. Take `⟨d, rfl⟩` from `e.surjective z`.

Rewrite using `[show (⟨_, h⟩ : LieG P.Gt) = e (c + d) from (hadd c d).symm]`. Use the proof step `simp, fun b y h => by`. Take `⟨c, rfl⟩` from `e.surjective y`. Rewrite using `[show (⟨_, h⟩ : LieG P.Gt) = e (b • c) from (hsm b c).symm]`. Use the proof step `simp⟩`.

Establish `h2` using `hHT a ha _ hf`. Rewrite `h2` using `[← (weilChar_surjective_and_map_range_al p C v O Λ P).2]`. Take `⟨_, ⟨s, rfl⟩, hs⟩` from `h2`. Use `⟨s, fun y => ?_⟩` and prove the remaining obligations. Rewrite using `[pairV_bLie_eq_evLie, P.alC_inclT, Point.inclOm, TensorProduct.mk_apply, evLie, LinearMap.liftBaseChange_tmul, one_smul]`.

Conclude with `congrArg _ (congrFun hs y)`. Use `choose s hs using ht`. Establish `hinj : Function.Injective P.bLie` using `fun y z h => e.symm.injective (funext fun i => mul_left_cancel₀ ha0 (P.integers.hom_inj (by rw [← hs, ← hs, h])))`. Use `choose o ho using fun i => pairV_inclT P hg (s i)`. Establish `key : P.bLie (e o) = a • ∑ j, g j • P.bLie (x j)`.

Rewrite using `[hL, e.symm_apply_apply]`. Simplify using `only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, hs] at ho`. Simplify using `only [hL (x _), Finset.smul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[← algebraMap_smul C, ho, Finset.sum_smul]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[← algebraMap_smul C a, ← algebraMap_smul C (e.symm _ _), smul_smul, smul_smul, smul_eq_mul, map_mul]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.

Establish `hV : P.bLie (e o) ∈ P.eigV τ`. Rewrite using `[key, ← algebraMap_smul C]`. Conclude with `Submodule.smul_mem _ _ (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (bLie_mem_eigV (hx j)))`. Use `⟨⟨e o, fun b => hinj ?_⟩, key⟩` and prove the remaining obligations. Rewrite using `[P.bLie_act, P.bLie_scale, mem_eigenSub.1 hV b, RingHom.comp_apply, algebraMap_smul]`.
-/
theorem smul_mem_wRec (hHT : HTChar p v P.Gt) {a : O} (ha0 : a ≠ 0) (ha : v (algebraMap O C a) ^ (p - 1) ≤ v (p : C))
    {τ : Λ →+* O} {n : ℕ} {x : Fin n → LieG P.Gt} (hx : ∀ j, AvDefs.IsEig P.Gt P.oGt τ (x j)) (g : Fin n → C)
    (hg : ∑ j, g j • P.bLie (x j) ∈ P.latT) : a • ∑ j, g j • P.bLie (x j) ∈ P.wRec τ := by
  classical
  haveI := P.isLocalRing
  haveI : IsDomain O := P.integers.hom_inj.isDomain _
  obtain ⟨e₁, h₁, h₂⟩ := OmegaRank.exists_param P.G (OmegaRank.smoothDim_model P)
  obtain ⟨e₂, h₃, h₄⟩ := OmegaRank.exists_lieEquiv P
  let e := e₁.trans e₂
  have hadd : ∀ c d, e (c + d) = lieAdd (e c) (e d) := fun c d => Subtype.ext (h₃ _ _ _ (h₁ c d))
  have hsm : ∀ (b : O) c, e (b • c) = AvDefs.lieScale P.Gt b (e c) := fun b c => Subtype.ext (h₄ b _ _ (h₂ b c))
  let L : (Fin P.A.g → O) →ₗ[O] P.V :=
    { toFun := fun c => P.bLie (e c)
      map_add' := fun c d => by rw [hadd, P.bLie_add]
      map_smul' := fun b c => by rw [hsm, P.bLie_scale]; rfl }
  have hL : ∀ y, P.bLie y = ∑ i, e.symm y i • L (Pi.single i 1) := fun y => by
    have h : L (e.symm y) = P.bLie y := congrArg P.bLie (e.apply_symm_apply y)
    simp only [← map_smul, ← map_sum, ← h, ← Pi.single_smul, smul_eq_mul, _root_.mul_one, Finset.univ_sum_single]
  have ht : ∀ i, ∃ s : O ⊗[ℤ_[p]] P.T, ∀ y, P.pairV (P.bLie y) (P.inclT s) = algebraMap O C (a * e.symm y i) := fun i => by
    have hf : (fun y => e.symm y i) ∈ omega P.Gt := ⟨fun y z h => by
        obtain ⟨c, rfl⟩ := e.surjective y
        obtain ⟨d, rfl⟩ := e.surjective z
        rw [show (⟨_, h⟩ : LieG P.Gt) = e (c + d) from (hadd c d).symm]
        simp, fun b y h => by
        obtain ⟨c, rfl⟩ := e.surjective y
        rw [show (⟨_, h⟩ : LieG P.Gt) = e (b • c) from (hsm b c).symm]
        simp⟩
    have h2 := hHT a ha _ hf
    rw [← (weilChar_surjective_and_map_range_al p C v O Λ P).2] at h2
    obtain ⟨_, ⟨s, rfl⟩, hs⟩ := h2
    refine ⟨s, fun y => ?_⟩
    rw [pairV_bLie_eq_evLie, P.alC_inclT, Point.inclOm, TensorProduct.mk_apply, evLie, LinearMap.liftBaseChange_tmul,
      one_smul]
    exact congrArg _ (congrFun hs y)
  choose s hs using ht
  have hinj : Function.Injective P.bLie := fun y z h => e.symm.injective (funext fun i =>
    mul_left_cancel₀ ha0 (P.integers.hom_inj (by rw [← hs, ← hs, h])))
  choose o ho using fun i => pairV_inclT P hg (s i)
  have key : P.bLie (e o) = a • ∑ j, g j • P.bLie (x j) := by
    rw [hL, e.symm_apply_apply]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, hs] at ho
    simp only [hL (x _), Finset.smul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← algebraMap_smul C, ho, Finset.sum_smul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← algebraMap_smul C a, ← algebraMap_smul C (e.symm _ _), smul_smul, smul_smul, smul_eq_mul, map_mul]
    congr 1
    ring
  have hV : P.bLie (e o) ∈ P.eigV τ := by
    rw [key, ← algebraMap_smul C]
    exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (bLie_mem_eigV (hx j)))
  refine ⟨⟨e o, fun b => hinj ?_⟩, key⟩
  rw [P.bLie_act, P.bLie_scale, mem_eigenSub.1 hV b, RingHom.comp_apply, algebraMap_smul]

end Point

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

/- English proof (translation)
Establish `key : ∀ s : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)), ∃ x : Psi H × Fin (Dw.p + Dw.q), |(exOf Dw u 0 (some s) : ℝ)| = |(u x.1 x.2 : ℝ)| ∧ ((x.1.1 = s.1 ∧ (x.2 : ℕ) = s.2 ∧ (s.2 : ℕ) < Dw.p) ∨ (x.1.1 = conjEmb s.1 ∧ (x.2 : ℕ) = Dw.p + (Dw.q - 1 - s.2) ∧ (s.2 : ℕ) < Dw.q))`. Introduce and unpack `⟨τ, i⟩`. Establish `hi` using `i.2`. Distinguish the cases in `h : τ (H.rt : E) = H.rt0`. Establish `hp : (i : ℕ) < Dw.p` using `by simpa [Datum.mult, h] using hi`.

Use `⟨(⟨τ, h⟩, ⟨i, by omega⟩), ?_, .inl ⟨rfl, rfl, hp⟩⟩` and prove the remaining obligations. Rewrite using `[show exOf Dw u 0 (some ⟨τ, i⟩) = _ from wtOf_big u 0 ⟨τ, h⟩ i hp, sub_zero]`. Establish `hq : (i : ℕ) < Dw.q` using `by simpa [Datum.mult, h] using hi`. Use `⟨(⟨conjEmb τ, conj_mem h⟩, ⟨Dw.p + (Dw.q - 1 - i), by omega⟩), ?_, .inr ⟨rfl, rfl, hq⟩⟩` and prove the remaining obligations. Establish `e` using `wtOf_small u 0 ⟨conjEmb τ, conj_mem h⟩ i hq`.

Simplify using `only [conjEmb_conjEmb] at e`. Rewrite using `[show exOf Dw u 0 (some ⟨τ, i⟩) = _ from e, sub_zero, Int.cast_neg, abs_neg]`. Use `choose F hF hR using key`. Establish `hinj : Function.Injective F`. Introduce and unpack `⟨τ, i⟩ ⟨τ', i'⟩ h`.

Establish `h1` using `hR ⟨τ, i⟩`. Establish `h2` using `hR ⟨τ', i'⟩`. Rewrite `h2` using `[← h]`. Simplify using `only at h1 h2`. Choose the witnesses or unpack the hypotheses as in `rfl : τ = τ' := by`.

Apply the tactic sequence `rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2`. Conclude with `h1.1.symm.trans h2.1`. Use linear arithmetic over natural numbers and integers. Use linear arithmetic over natural numbers and integers. Rewrite using `[← conjEmb_conjEmb τ, ← h1.1, h2.1, conjEmb_conjEmb]`.

Take `rfl : i = i'` from `Fin.ext (by omega)`. Both sides reduce to the same expression. Rewrite using `[l1, ← Fintype.sum_prod_type', Finset.sum_congr rfl fun s _ => hF s, ← Finset.sum_image (f := fun x : Psi H × Fin (Dw.p + Dw.q) => |(u x.1 x.2 : ℝ)|) hinj.injOn]`. Conclude with `Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => abs_nonneg _`.
-/
theorem sum_abs_exOf_le (u : AllWt.Weight Dw) :
    ∑ s : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)), |(exOf Dw u 0 (some s) : ℝ)| ≤ l1 u := by
  classical
  have key : ∀ s : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)), ∃ x : Psi H × Fin (Dw.p + Dw.q),
      |(exOf Dw u 0 (some s) : ℝ)| = |(u x.1 x.2 : ℝ)| ∧ ((x.1.1 = s.1 ∧ (x.2 : ℕ) = s.2 ∧ (s.2 : ℕ) < Dw.p) ∨
        (x.1.1 = conjEmb s.1 ∧ (x.2 : ℕ) = Dw.p + (Dw.q - 1 - s.2) ∧ (s.2 : ℕ) < Dw.q)) := by
    rintro ⟨τ, i⟩
    have hi := i.2
    by_cases h : τ (H.rt : E) = H.rt0
    · have hp : (i : ℕ) < Dw.p := by simpa [Datum.mult, h] using hi
      refine ⟨(⟨τ, h⟩, ⟨i, by omega⟩), ?_, .inl ⟨rfl, rfl, hp⟩⟩
      rw [show exOf Dw u 0 (some ⟨τ, i⟩) = _ from wtOf_big u 0 ⟨τ, h⟩ i hp, sub_zero]
    · have hq : (i : ℕ) < Dw.q := by simpa [Datum.mult, h] using hi
      refine ⟨(⟨conjEmb τ, conj_mem h⟩, ⟨Dw.p + (Dw.q - 1 - i), by omega⟩), ?_, .inr ⟨rfl, rfl, hq⟩⟩
      have e := wtOf_small u 0 ⟨conjEmb τ, conj_mem h⟩ i hq
      simp only [conjEmb_conjEmb] at e
      rw [show exOf Dw u 0 (some ⟨τ, i⟩) = _ from e, sub_zero, Int.cast_neg, abs_neg]
  choose F hF hR using key
  have hinj : Function.Injective F := by
    rintro ⟨τ, i⟩ ⟨τ', i'⟩ h
    have h1 := hR ⟨τ, i⟩
    have h2 := hR ⟨τ', i'⟩
    rw [← h] at h2
    dsimp only at h1 h2
    obtain rfl : τ = τ' := by
      rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
      · exact h1.1.symm.trans h2.1
      · omega
      · omega
      · rw [← conjEmb_conjEmb τ, ← h1.1, h2.1, conjEmb_conjEmb]
    obtain rfl : i = i' := Fin.ext (by omega)
    rfl
  rw [l1, ← Fintype.sum_prod_type', Finset.sum_congr rfl fun s _ => hF s,
    ← Finset.sum_image (f := fun x : Psi H × Fin (Dw.p + Dw.q) => |(u x.1 x.2 : ℝ)|) hinj.injOn]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => abs_nonneg _

section Frame

variable {p : ℕ} [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C] {v : Valuation C ℝ≥0}
  {O : Type} [CommRing O] [Algebra O C] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C]
  [Algebra c.F C] [StarRing (𝓞 E)] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O]

omit [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] in

/- English proof (translation)
Unfold `htLat at hw`. Use `split_ifs at hw`. Take `⟨y, hy, rfl⟩` from `hw`. Conclude with `smul_proj_mem P.integers P.actV (actV_mem P) _ hδ hy`. Conclude with `P.latT.smul_mem δ hw.1`.
-/
theorem smul_mem_latT (P : Point p v O (𝓞 E)) (τ : E →+* ℂ) {δ : O}
    (hδ : δ ∈ (differentIdeal ℤ (𝓞 E)).map (embO P.integers (embAt c C τ))) {w : P.V} (hw : w ∈ htLat c P τ) :
    δ • w ∈ P.latT := by
  classical
  unfold htLat at hw
  split_ifs at hw
  · obtain ⟨y, hy, rfl⟩ := hw
    exact smul_proj_mem P.integers P.actV (actV_mem P) _ hδ hy
  · exact P.latT.smul_mem δ hw.1

/- English proof (translation)
The claim follows from `|Real.log (v (t (some s))) / Real.log (v (p : C))| ≤ htEx E p := by letI := io.toAlgebra obtain ⟨-, kO, P, ψ, z, hP, hz, g, a, x, hc, hg, ha, hx, hb⟩ := h have hp : p.Prime := Fact.out have hv := P.integers have hHT := htChar_of_pointOver E H Dw l Xo c p C v O T io y₀ hy k.toRing …`.
-/
theorem exists_frBor [IsGalois ℚ E] {T : CDVR} {io : c.F →+* T.Fr} {y₀ : IntFr Xo c T io} (hy : y₀.IsAlg)
    {k : letI := io.toAlgebra; T.Fr →ₐ[c.F] C} {y : FrPt Xo c C} (h : IsHTFrame p v O y₀ k y) :
    letI := io.toAlgebra
    ∃ (z : FrPt Xo c C) (t : Ix Dw → Cˣ), FrMap k y₀.1 z ∧ FrBor t z y ∧ v (t none) = 1 ∧ ∀ s,
      |Real.log (v (t (some s))) / Real.log (v (p : C))| ≤ htEx E p := by
  letI := io.toAlgebra
  obtain ⟨-, kO, P, ψ, z, hP, hz, g, a, x, hc, hg, ha, hx, hb⟩ := h
  have hp : p.Prime := Fact.out
  have hv := P.integers
  have hHT := htChar_of_pointOver E H Dw l Xo c p C v O T io y₀ hy k.toRingHom kO P ψ hP
  have hd := fun τ => diag_ne_zero_of_linearIndependent (hg τ) (hb τ).1
  have ha0 : a ≠ 0 := by rintro rfl; simp at ha
  let t : Ix Dw → Cˣ := fun i => Option.rec (Units.mk0 a ha0) (fun s => Units.mk0 _ (hd s.1 s.2)) i
  refine ⟨z, t, hz, (frBor_iff_frChg z y t).2 ⟨g, hg, fun _ _ => rfl, hc⟩, ha, ?_⟩
  rintro ⟨τ, i⟩
  change |Real.log (v (g τ i i)) / _| ≤ _
  have h0 : (p : C) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have h1 := lt_one_of_not_isUnit hv (Fact.out : ¬ IsUnit (p : O))
  have hpos : ∀ {b : C}, b ≠ 0 → (0 : ℝ) < v b := fun hb => by simpa [pos_iff_ne_zero] using hb
  have hL : Real.log (v (p : C)) < 0 := Real.log_neg (hpos h0) (by exact_mod_cast h1)
  have heig := fun j => (hx τ j).isEig hP (z.eig τ j)
  have hlow : v 1 ≤ v (g τ i i) := by
    have := IsLatBasis.diag_le hv (g' := 1) (hg τ) (fun i j hij => Matrix.one_apply_ne hij.ne) (hb τ) i (by
      simp only [Matrix.one_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
      exact wRec_le_htLat P τ ⟨⟨x τ i, heig i⟩, rfl⟩)
    rwa [Matrix.one_apply_eq] at this
  have hp1 : 0 < p - 1 := Nat.sub_pos_of_lt hp.one_lt
  obtain ⟨b, hbp⟩ := IsAlgClosed.exists_pow_nat_eq (p : C) hp1
  have hb0 : b ≠ 0 := by rintro rfl; exact h0 (by rw [← hbp, zero_pow hp1.ne'])
  obtain ⟨b, rfl⟩ := hv.exists_of_le_one (r := b)
    ((pow_le_one_iff hp1.ne').1 (by rw [← map_pow, hbp]; exact h1.le))
  obtain ⟨δ, hδ, hδp⟩ := exists_delta hv hp Fact.out (embAt c C τ)
  have hn : 0 < Module.finrank ℚ E := Module.finrank_pos
  have hδv := hv.le_of_dvd hδp
  rw [map_pow, map_pow, map_pow, map_pow, map_natCast] at hδv
  have hδ0 : algebraMap O C δ ≠ 0 := fun (e : algebraMap O C δ = 0) => by
    rw [e, map_zero, zero_pow hn.ne'] at hδv
    exact pow_ne_zero _ ((Valuation.ne_zero_iff v).2 h0) (le_antisymm hδv zero_le)
  have m1 := smul_mem_latT P τ hδ ((hb τ).mem i)
  rw [← algebraMap_smul C, Finset.smul_sum] at m1
  simp only [smul_smul] at m1
  have m2 := smul_mem_wRec P hHT (a := b) (fun e => hb0 (by rw [e, map_zero])) (by rw [← map_pow, hbp]) heig _ m1
  rw [← RecSpan.span_bLie_eq_wRec E H Dw l Xo c p C v O T io y₀ k kO P ψ z hP hz τ (x τ) (hx τ),
    ← algebraMap_smul C, Finset.smul_sum] at m2
  simp only [smul_smul] at m2
  have hli := (alC_surjective_and_linearIndependent_bLie p C v O (𝓞 E) P hHT).2 _ (x τ)
    (linearIndependent_evLie_of_lieTie E H Dw l Xo c p C v O T io y₀ k kO P ψ z hP hz τ (x τ) (hx τ))
  obtain ⟨o, ho⟩ := ((isLatBasis_span hli).sum_mem_iff _).1 m2 i
  have hup := hv.map_le_one o
  rw [ho, map_mul, map_mul] at hup
  have e1 : 0 ≤ Real.log (v (g τ i i)) := Real.log_nonneg (by exact_mod_cast (v.map_one ▸ hlow))
  have e2 : Real.log (v (algebraMap O C b)) + (Real.log (v (algebraMap O C δ)) + Real.log (v (g τ i i))) ≤ 0 := by
    rw [← Real.log_mul (hpos hδ0).ne' (hpos (hd τ i)).ne',
      ← Real.log_mul (hpos hb0).ne' (mul_pos (hpos hδ0) (hpos (hd τ i))).ne']
    exact Real.log_nonpos (by positivity) (by exact_mod_cast hup)
  have hp2 : (0 : ℝ) < (p : ℝ) - 1 := sub_pos.2 (by exact_mod_cast hp.one_lt)
  have e3 : Real.log (v (algebraMap O C b)) = 1 / ((p : ℝ) - 1) * Real.log (v (p : C)) := by
    rw [← hbp, map_pow, NNReal.coe_pow, Real.log_pow, Nat.cast_sub hp.one_lt.le, Nat.cast_one]
    field_simp
  have hn' : (0 : ℝ) < Module.finrank ℚ E := by exact_mod_cast hn
  have e4 : (padicValNat p (discr E).natAbs : ℝ) / (Module.finrank ℚ E : ℝ) * Real.log (v (p : C)) ≤
      Real.log (v (algebraMap O C δ)) := by
    rw [div_mul_eq_mul_div, div_le_iff₀' hn', ← Real.log_pow, ← Real.log_pow]
    exact Real.log_le_log (pow_pos (hpos h0) _) (by exact_mod_cast hδv)
  have e5 : (0 : ℝ) ≤ (padicValNat p (discr E).natAbs : ℝ) / (Module.finrank ℚ E : ℝ) := by positivity
  rw [abs_div, abs_of_nonneg e1, abs_of_neg hL, div_le_iff₀ (neg_pos.2 hL), htEx]
  nlinarith [mul_nonneg e5 (neg_pos.2 hL).le]

/- English proof (translation)
Use `letI := io.toAlgebra`. Take `⟨z, t, hz, ht, h0, hs⟩` from `exists_frBor hy h`. Establish `he : (0 : ℝ) ≤ vLa la (p : c.F)`. Use `vAdd_int_nonneg la (a := (p : 𝓞 c.F)) (by simpa using (Fact.out : p.Prime).ne_zero)` as an intermediate fact. Conclude with `(show (0 : ℤ) ≤ vLa la (p : c.F) by simpa [vLa, Formalism.BasicNotions.vAdd] using this)` after adjusting the coercions.

Rewrite using `[FlagTan.evR_frBor hf ht, FlagTan.evR_frMap hf.1 hz, val_vw_mul, h.val_vw_map ho, add_comm, val_vw_of_ne la p v (Units.ne_zero _)]`. Use `add_le_add le_rfl (EReal.coe_le_coe_iff.2 ?_)` and prove the remaining obligations. Rewrite using `[_root_.mul_assoc]`. Use `mul_le_mul_of_nonneg_left ?_ he` and prove the remaining obligations. Rewrite using `[Units.coe_prod, map_prod, NNReal.coe_prod, Real.log_prod fun i _ => (NNReal.coe_ne_zero.2 ((Valuation.ne_zero_iff v).2 (Units.ne_zero _))), Fintype.sum_option]`.

Simplify using `only [Units.val_zpow_eq_zpow_val, map_zpow₀, NNReal.coe_zpow, Real.log_zpow, h0, NNReal.coe_one, Real.log_one, mul_zero, zero_add, Finset.sum_div]`. Establish `hx : 0 ≤ htEx E p`. Establish `: (1 : ℝ) < p` using `by exact_mod_cast (Fact.out : p.Prime).one_lt`. Conclude with `add_nonneg (div_nonneg zero_le_one (by linarith)) (by positivity)`. Use `le_trans ?_ (mul_le_mul_of_nonneg_left (sum_abs_exOf_le u) hx)` and prove the remaining obligations.

Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_le_sum fun s _ => (le_abs_self _).trans ?_` and prove the remaining obligations. Rewrite using `[mul_div_assoc, abs_mul, mul_comm]`. Conclude with `mul_le_mul_of_nonneg_right (hs s) (abs_nonneg _)`.
-/
theorem val_le [IsGalois ℚ E] {T : CDVR} {io : c.F →+* T.Fr} {y₀ : IntFr Xo c T io} (hy : y₀.IsAlg)
    {k : letI := io.toAlgebra; T.Fr →ₐ[c.F] C} {y : FrPt Xo c C} (h : IsHTFrame p v O y₀ k y)
    {la : HeightOneSpectrum (𝓞 c.F)} {e : ℕ} (ho : OverLa la T.V io e) (u : AllWt.Weight Dw) {f : Rul Xo c}
    (hf : f ∈ secZ Xo c (exOf Dw u 0)) : val_vw la p v (evR Xo c f y) ≤
      nval T.V e (evI y₀ f) + (((vLa la (p : c.F) : ℝ) * htEx E p * l1 u : ℝ) : EReal) := by
  letI := io.toAlgebra
  obtain ⟨z, t, hz, ht, h0, hs⟩ := exists_frBor hy h
  have he : (0 : ℝ) ≤ vLa la (p : c.F) := by
    have := vAdd_int_nonneg la (a := (p : 𝓞 c.F)) (by simpa using (Fact.out : p.Prime).ne_zero)
    exact_mod_cast (show (0 : ℤ) ≤ vLa la (p : c.F) by simpa [vLa, Formalism.BasicNotions.vAdd] using this)
  rw [FlagTan.evR_frBor hf ht, FlagTan.evR_frMap hf.1 hz, val_vw_mul, h.val_vw_map ho, add_comm,
    val_vw_of_ne la p v (Units.ne_zero _)]
  refine add_le_add le_rfl (EReal.coe_le_coe_iff.2 ?_)
  rw [_root_.mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ he
  rw [Units.coe_prod, map_prod, NNReal.coe_prod, Real.log_prod fun i _ => (NNReal.coe_ne_zero.2 ((Valuation.ne_zero_iff v).2 (Units.ne_zero _))),
    Fintype.sum_option]
  simp only [Units.val_zpow_eq_zpow_val, map_zpow₀, NNReal.coe_zpow, Real.log_zpow, h0, NNReal.coe_one, Real.log_one,
    mul_zero, zero_add, Finset.sum_div]
  have hx : 0 ≤ htEx E p := by
    have : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
    exact add_nonneg (div_nonneg zero_le_one (by linarith)) (by positivity)
  refine le_trans ?_ (mul_le_mul_of_nonneg_left (sum_abs_exOf_le u) hx)
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun s _ => (le_abs_self _).trans ?_
  rw [mul_div_assoc, abs_mul, mul_comm]
  exact mul_le_mul_of_nonneg_right (hs s) (abs_nonneg _)

end Frame

attribute [local instance] algPadicInt algPadicField towerPadic factPadic PadicComplexHost.isAdicComplete

/- English proof (translation)
Introduce and unpack `p la hp hla _ ⟨⟨_, T, io, e, ho, y₀, hy, η, -, rfl⟩, rfl⟩`. Take `⟨q, hq, inst, k, y, h⟩` from `exists_isHTFrameCp y₀ hy`. Choose the witnesses or unpack the hypotheses as in `rfl : q = p := by`. Assume the negation of the conclusion as `hne`. Take `⟨a, b, hab⟩ : IsCoprime (q : 𝓞 c.F) (p : 𝓞 c.F)` from `Nat.Coprime.cast ((Nat.coprime_primes hq.out hp).2 hne)`.

Conclude with `la.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (hab ▸ Ideal.add_mem _ (Ideal.mul_mem_left _ _ (h.mem ho)) (Ideal.mul_mem_left _ _ hla)))`. Use `letI := H.starRing`. Conclude with `⟨_, ⟨q, hq, inst, T, io, e, y₀, k, y, ho, hy, h, rfl⟩, fun u f hf => val_le hy h ho u hf⟩`.
-/
theorem htCmp [IsGalois ℚ E] : HTCmp Xo c := by
  rintro p la hp hla _ ⟨⟨_, T, io, e, ho, y₀, hy, η, -, rfl⟩, rfl⟩
  obtain ⟨q, hq, inst, k, y, h⟩ := exists_isHTFrameCp y₀ hy
  obtain rfl : q = p := by
    by_contra hne
    obtain ⟨a, b, hab⟩ : IsCoprime (q : 𝓞 c.F) (p : 𝓞 c.F) := Nat.Coprime.cast ((Nat.coprime_primes hq.out hp).2 hne)
    exact la.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
      (hab ▸ Ideal.add_mem _ (Ideal.mul_mem_left _ _ (h.mem ho)) (Ideal.mul_mem_left _ _ hla)))
  letI := H.starRing
  exact ⟨_, ⟨q, hq, inst, T, io, e, y₀, k, y, ho, hy, h, rfl⟩, fun u f hf => val_le hy h ho u hf⟩

end GlobalTheory.CovHt.FrameCmp

/- English proof (translation)
Introduce `_ _ _ _ _ _ _ _ _ _ _` and use `GlobalTheory.CovHt.FrameCmp.htCmp`.
-/
theorem GlobalTheory.CovHt.htCmp_of_hypotheses : GlobalTheory.CovTop.Hypotheses2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
    [IsGalois ℚ E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l),
    HTCmp Xo c := fun _ _ _ _ _ _ _ _ _ _ _ => GlobalTheory.CovHt.FrameCmp.htCmp
