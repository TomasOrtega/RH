import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LamV
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCompletionEquiv
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FrobOrderSpec
import Formalism.LocalRingCardinality.ConjSqrtMinusD
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.LocalToGlobal.GroupLattices.PerfectRings.ICIntCp
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.WittFractionToCpAlgebraMap
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.FrameFacts
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts

open NumberField IsDedekindDomain IsLocalRing Formalism.UG Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.L2.G GlobalTheory.GO.PlWitt
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.PlaceOrbit

section General

variable {E : Type} [Field E] [NumberField E] {p n : ℕ} [hp : Fact p.Prime]

/- English proof (translation)
Establish `: CharZero K` using `charZero_of_injective_ringHom a.injective`. Set `u : (E ≃ₐ[ℚ] E) → (E →ₐ[ℚ] K)` to `fun τ => a.toRatAlgHom.comp τ`. Establish `hu : Function.Injective u` using `fun s t h => AlgEquiv.ext fun x => a.injective (AlgHom.congr_fun h x)`. Take `⟨τ, hτ⟩` from `(hu.bijective_of_nat_card_le (by`. Rewrite using `[IsGalois.card_aut_eq_finrank]`.

Conclude with `card_algHom_le_finrank ℚ E K)).2 b.toRatAlgHom`. Conclude with `⟨τ, fun x => (AlgHom.congr_fun hτ x).symm⟩`.
-/
theorem exists_aut [IsGalois ℚ E] {K : Type} [Field K] (a b : E →+* K) : ∃ τ : E ≃ₐ[ℚ] E, ∀ x, b x = a (τ x) := by
  have : CharZero K := charZero_of_injective_ringHom a.injective
  let u : (E ≃ₐ[ℚ] E) → (E →ₐ[ℚ] K) := fun τ => a.toRatAlgHom.comp τ
  have hu : Function.Injective u := fun s t h => AlgEquiv.ext fun x => a.injective (AlgHom.congr_fun h x)
  obtain ⟨τ, hτ⟩ := (hu.bijective_of_nat_card_le (by
    rw [IsGalois.card_aut_eq_finrank]; exact card_algHom_le_finrank ℚ E K)).2 b.toRatAlgHom
  exact ⟨τ, fun x => (AlgHom.congr_fun hτ x).symm⟩

/- English proof (translation)
Establish `hpr : (P.under ℤ).IsPrime` using `Ideal.IsPrime.under _ P`. Establish `hcard` using `Ideal.card_inertia_eq_ramificationIdxIn (G := E ≃ₐ[ℚ] E) (P.under ℤ) P`. Rewrite `hcard` using `[Ideal.ramificationIdxIn_eq_ramificationIdx (P.under ℤ) P (E ≃ₐ[ℚ] E)]`. Establish `h1 : Nat.card (P.inertia (E ≃ₐ[ℚ] E)) = 1`. Rewrite using `[Nat.card_eq_one_iff_unique]`.

Use `⟨⟨fun x y => Subtype.ext ?_⟩, ⟨⟨1, one_mem _⟩⟩⟩` and prove the remaining obligations. Rewrite using `[h x.1 (AddSubgroup.mem_inertia.mp x.2), h y.1 (AddSubgroup.mem_inertia.mp y.2)]`. Rewrite `hcard` using `[h1]`. Conclude with `Ideal.ramificationIdx_eq_one_iff.mp hcard.symm`.
-/
theorem unramified_of_inertia [IsGalois ℚ E] (P : Ideal (𝓞 E)) [P.IsPrime]
    (h : ∀ σ : E ≃ₐ[ℚ] E, (∀ x : 𝓞 E, σ • x - x ∈ P) → σ = 1) : Algebra.IsUnramifiedAt ℤ P := by
  have hpr : (P.under ℤ).IsPrime := Ideal.IsPrime.under _ P
  have hcard := Ideal.card_inertia_eq_ramificationIdxIn (G := E ≃ₐ[ℚ] E) (P.under ℤ) P
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx (P.under ℤ) P (E ≃ₐ[ℚ] E)] at hcard
  have h1 : Nat.card (P.inertia (E ≃ₐ[ℚ] E)) = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun x y => Subtype.ext ?_⟩, ⟨⟨1, one_mem _⟩⟩⟩
    rw [h x.1 (AddSubgroup.mem_inertia.mp x.2), h y.1 (AddSubgroup.mem_inertia.mp y.2)]
  rw [h1] at hcard
  exact Ideal.ramificationIdx_eq_one_iff.mp hcard.symm

/- English proof (translation)
Assemble the required witnesses or components as `⟨by have : (Ideal.span {(p : ℤ)}).IsMaximal := Int.ideal_span_isMaximal_of_prime p refine this.eq_of_le (Ideal.comap_ne_top _ Q.isPrime.ne_top) ?_ rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, map_natCast] exact hQ⟩`.
-/
theorem liesOver_of_mem (Q : HeightOneSpectrum (𝓞 E)) (hQ : (p : 𝓞 E) ∈ Q.asIdeal) :
    Q.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) := ⟨by
  have : (Ideal.span {(p : ℤ)}).IsMaximal := Int.ideal_span_isMaximal_of_prime p
  refine this.eq_of_le (Ideal.comap_ne_top _ Q.isPrime.ne_top) ?_
  rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, map_natCast]
  exact hQ⟩

/- English proof (translation)
Rewrite using `[cc_eq_zero, (WittVector.irreducible p).maximalIdeal_eq, Ideal.mem_span_singleton]`.
-/
theorem mem_max (y : Wn p n) : y ∈ maximalIdeal (Wn p n) ↔ WittVector.constantCoeff y = 0 := by
  rw [cc_eq_zero, (WittVector.irreducible p).maximalIdeal_eq, Ideal.mem_span_singleton]

/- English proof (translation)
Rewrite using `[mem_max, cc_eq_zero]`.
-/
theorem p_mem : (p : Wn p n) ∈ maximalIdeal (Wn p n) := by rw [mem_max, cc_eq_zero]

def plc (i : E →+* Qn p n) : HeightOneSpectrum (𝓞 E) := (exists_ov (O := Wn p n) p_mem i).choose

/- English proof (translation)
The claim follows from `(exists_ov (O := Wn p n) p_mem i).choose_spec.1`.
-/
theorem p_mem_plc (i : E →+* Qn p n) : (p : 𝓞 E) ∈ (plc i).asIdeal := (exists_ov (O := Wn p n) p_mem i).choose_spec.1

/- English proof (translation)
The claim follows from `(exists_ov (O := Wn p n) p_mem i).choose_spec.2`.
-/
theorem ov_plc (i : E →+* Qn p n) : Ov (Wn p n) i (plc i) := (exists_ov (O := Wn p n) p_mem i).choose_spec.2

/- English proof (translation)
The claim follows from `ov_plc i x`.
-/
theorem mem_plc (i : E →+* Qn p n) (x : 𝓞 E) :
    x ∈ (plc i).asIdeal ↔ ∃ y ∈ maximalIdeal (Wn p n), algebraMap _ (Qn p n) y = i x := ov_plc i x

/- English proof (translation)
Take `⟨g, hg⟩` from `exists_intHom (O := Wn p n) i`. Use `⟨g, fun x => (hg x).symm, fun a => ?_, fun x => ((ov_iff hg).1 (ov_plc i) x).trans (mem_max _)⟩` and prove the remaining obligations. Take `⟨y, rfl⟩` from `WittVector.constantCoeff_surjective p a`. Take `⟨x, z, hz, e⟩` from `h y`. Use `⟨x, ?_⟩` and prove the remaining obligations.

Simplify using `only`. Rewrite using `[← IsFractionRing.injective (Wn p n) (Qn p n) (e.trans (hg x).symm), map_add, (mem_max z).1 hz, add_zero]`.
-/
theorem good_plc {i : E →+* Qn p n}
    (h : ∀ y : Wn p n, ∃ x : 𝓞 E, ∃ z ∈ maximalIdeal (Wn p n), algebraMap _ (Qn p n) (y + z) = i x) : Good (plc i) i := by
  obtain ⟨g, hg⟩ := exists_intHom (O := Wn p n) i
  refine ⟨g, fun x => (hg x).symm, fun a => ?_, fun x => ((ov_iff hg).1 (ov_plc i) x).trans (mem_max _)⟩
  obtain ⟨y, rfl⟩ := WittVector.constantCoeff_surjective p a
  obtain ⟨x, z, hz, e⟩ := h y
  refine ⟨x, ?_⟩
  simp only
  rw [← IsFractionRing.injective (Wn p n) (Qn p n) (e.trans (hg x).symm), map_add, (mem_max z).1 hz, add_zero]

omit [NumberField E] in
/- English proof (translation)
Take `⟨x, z, e⟩` from `h.dense y 1`. Conclude with `⟨x, _, Ideal.mul_mem_right _ _ (by rw [pow_one]; exact p_mem), e.symm⟩`.
-/
theorem good_approx {Q : HeightOneSpectrum (𝓞 E)} {i : E →+* Qn p n} (h : Good Q i) (y : Wn p n) :
    ∃ x : 𝓞 E, ∃ z ∈ maximalIdeal (Wn p n), algebraMap _ (Qn p n) (y + z) = i x := by
  obtain ⟨x, z, e⟩ := h.dense y 1
  exact ⟨x, _, Ideal.mul_mem_right _ _ (by rw [pow_one]; exact p_mem), e.symm⟩

/- English proof (translation)
The claim follows from `(ov_plc j).eq (h.ov (ι := RingHom.id _) (j := RingHom.id _) p_mem (fun _ => rfl) s e)`.
-/
theorem plc_eq_of_pow {Q : HeightOneSpectrum (𝓞 E)} {i j : E →+* Qn p n} (h : Good Q i) (s : ℕ)
    (e : ∀ x, j x = (Fr p n ^ s) (i x)) : plc j = Q :=
  (ov_plc j).eq (h.ov (ι := RingHom.id _) (j := RingHom.id _) p_mem (fun _ => rfl) s e)

/- English proof (translation)
The claim follows from `good_plc fun y => by obtain ⟨x, z, hz, e'⟩ := good_approx h y refine ⟨τ⁻¹ • x, z, hz, ?_⟩ rw [e', e] exact congrArg i (τ.apply_symm_apply _).symm`.
-/
theorem good_aut {Q : HeightOneSpectrum (𝓞 E)} {i j : E →+* Qn p n} (h : Good Q i) (τ : E ≃ₐ[ℚ] E)
    (e : ∀ x, j x = i (τ x)) : Good (plc j) j :=
  good_plc fun y => by
    obtain ⟨x, z, hz, e'⟩ := good_approx h y
    refine ⟨τ⁻¹ • x, z, hz, ?_⟩
    rw [e', e]
    exact congrArg i (τ.apply_symm_apply _).symm

/- English proof (translation)
Take `⟨g, hg, -, hk⟩` from `h`. Introduce `x`. Establish `hc : Nat.card (ℤ ⧸ Q.asIdeal.under ℤ) = p`. Rewrite using `[← (liesOver_of_mem Q hQ).over, Nat.card_congr (Int.quotientSpanNatEquivZMod p).toEquiv, Nat.card_zmod]`. Take `⟨a, ha, ha'⟩` from `fr_pow 1 (g x)`.

Rewrite `ha`, `ha'` using `[pow_one]`. Establish `h1 : a = g (τ • x)` using `IsFractionRing.injective (Wn p n) (Qn p n) (by rw [← ha, ← hg, ← hg, e]; rfl)`. Rewrite using `[hc, hk, map_sub, map_sub, map_pow, map_pow, ← ha', h1]`. Conclude with `sub_self _`.
-/
theorem isArithFrobAt_of {Q : HeightOneSpectrum (𝓞 E)} {i : E →+* Qn p n} (h : Good Q i) (hQ : (p : 𝓞 E) ∈ Q.asIdeal)
    (τ : E ≃ₐ[ℚ] E) (e : ∀ x, Fr p n (i x) = i (τ x)) : IsArithFrobAt ℤ τ Q.asIdeal := by
  obtain ⟨g, hg, -, hk⟩ := h
  intro x
  have hc : Nat.card (ℤ ⧸ Q.asIdeal.under ℤ) = p := by
    rw [← (liesOver_of_mem Q hQ).over, Nat.card_congr (Int.quotientSpanNatEquivZMod p).toEquiv, Nat.card_zmod]
  obtain ⟨a, ha, ha'⟩ := fr_pow 1 (g x)
  rw [pow_one] at ha ha'
  have h1 : a = g (τ • x) := IsFractionRing.injective (Wn p n) (Qn p n) (by rw [← ha, ← hg, ← hg, e]; rfl)
  rw [hc, hk, map_sub, map_sub, map_pow, map_pow, ← ha', h1]
  exact sub_self _

end General

section Host

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {R : Ranks} {H : Host R} {p n : ℕ} [hp : Fact p.Prime] {h : R.MA}

/- English proof (translation)
Simplify using `only [Host.sigmaOf, map_mul]`. Both sides reduce to the same expression.
-/
theorem sigmaOf_mul (g g' : R.GG) (x : H.E) : H.sigmaOf (g * g') x = H.sigmaOf g (H.sigmaOf g' x) := by
  simp only [Host.sigmaOf, map_mul]
  rfl

/- English proof (translation)
The claim follows from `(H.gal).symm.injective`.
-/
theorem sigmaOf_inj : Function.Injective H.sigmaOf := (H.gal).symm.injective

/- English proof (translation)
The claim follows from `(H.gal).symm.surjective`.
-/
theorem sigmaOf_surj : Function.Surjective H.sigmaOf := (H.gal).symm.surjective

/- English proof (translation)
The claim follows from `e.cc_mul_cc`.
-/
theorem cc_mul_cc (e : Formalism.HC.Frame) : e.cc * e.cc = 1 := e.cc_mul_cc

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => simp`. Consider the case `succ m ih => rcases ih with h | h <;> simp [pow_succ, h, cc_mul_cc]`.
-/
theorem cc_pow (e : Formalism.HC.Frame) (m : ℕ) : e.cc ^ m = 1 ∨ e.cc ^ m = e.cc := by
  induction m with
  | zero => simp
  | succ m ih => rcases ih with h | h <;> simp [pow_succ, h, cc_mul_cc]

/- English proof (translation)
The claim follows from `e.cc_notMem_Psi`.
-/
theorem cc_notMem (e : Formalism.HC.Frame) : e.cc ∉ e.Psi := e.cc_notMem_Psi

/- English proof (translation)
Rewrite using `[zPsi_eq, mul_assoc, cc_mul_cc, mul_one]`.
-/
theorem frob_eq_mul (h : R.MA) : ((c0, h) : R.GG) = (zPsi R.toFrame h : R.GG) * R.cc := by
  rw [zPsi_eq, mul_assoc, cc_mul_cc, mul_one]

variable (H) in

def tw (i : H.E →+* Qn p n) (g : R.GG) : H.E →+* Qn p n := i.comp (H.sigmaOf g : H.E →+* H.E)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem tw_apply (i : H.E →+* Qn p n) (g : R.GG) (x : H.E) : tw H i g x = i (H.sigmaOf g x) := rfl

variable (H) in

def twF (i : H.E →+* Qn p n) (g : R.GG) : H.F →+* Qn p n := (tw H i g).comp (algebraMap H.F H.E)

/- English proof (translation)
Apply the tactic sequence `rcases cc_pow R.toFrame m with e | e <;> rw [e]`. Rewrite using `[mul_one]`. Use `RingHom.ext fun x => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `i (H.sigmaOf (g * R.cc) x) = i (H.sigmaOf g x)`. Rewrite using `[sigmaOf_mul]`.

Conclude with `congrArg (fun y => i (H.sigmaOf g y)) ((H.conjE_mem_hostF_iff x.1).1 x.2)`.
-/
theorem twF_cc_pow (i : H.E →+* Qn p n) (g : R.GG) (m : ℕ) : twF H i (g * R.cc ^ m) = twF H i g := by
  rcases cc_pow R.toFrame m with e | e <;> rw [e]
  · rw [mul_one]
  · refine RingHom.ext fun x => ?_
    change i (H.sigmaOf (g * R.cc) x) = i (H.sigmaOf g x)
    rw [sigmaOf_mul]
    exact congrArg (fun y => i (H.sigmaOf g y)) ((H.conjE_mem_hostF_iff x.1).1 x.2)

/- English proof (translation)
Rewrite using `[mem_plc, mem_plc]`. Both sides reduce to the same expression.
-/
theorem mem_plc_twF (i : H.E →+* Qn p n) (g : R.GG) (x : 𝓞 H.F) :
    x ∈ (plc (twF H i g)).asIdeal ↔ algebraMap (𝓞 H.F) (𝓞 H.E) x ∈ (plc (tw H i g)).asIdeal := by
  rw [mem_plc, mem_plc]
  rfl

/- English proof (translation)
Rewrite using `[mem_plc, mem_plc, tw_apply, sigmaOf_mul]`. Both sides reduce to the same expression.
-/
theorem mem_plc_tw_cc (i : H.E →+* Qn p n) (g : R.GG) (x : 𝓞 H.E) :
    x ∈ (plc (tw H i (g * R.cc))).asIdeal ↔ H.conj • x ∈ (plc (tw H i g)).asIdeal := by
  rw [mem_plc, mem_plc, tw_apply, sigmaOf_mul]
  rfl

/- English proof (translation)
Establish `: H.conj * H.conj = 1`. Unfold `Formalism.HC.HostRaw.conj`. Rewrite using `[← map_mul, cc_mul_cc, map_one]`. Rewrite using `[smul_smul, this, one_smul]`.
-/
theorem conj_conj (x : 𝓞 H.E) : H.conj • H.conj • x = x := by
  have : H.conj * H.conj = 1 := by
    unfold Formalism.HC.HostRaw.conj
    rw [← map_mul, cc_mul_cc, map_one]
  rw [smul_smul, this, one_smul]

/- English proof (translation)
Establish `hm : (x : H.E) ∈ H.F` using `(H.conjE_mem_hostF_iff _).2 (congrArg (fun y : 𝓞 H.E => (y : H.E)) hx)`. Conclude with `⟨⟨⟨x, hm⟩, (isIntegral_algHom_iff (algebraMap H.F H.E).toIntAlgHom (algebraMap H.F H.E).injective).1 x.isIntegral_coe⟩, rfl⟩`.
-/
theorem exists_real (x : 𝓞 H.E) (hx : H.conj • x = x) : ∃ z : 𝓞 H.F, algebraMap (𝓞 H.F) (𝓞 H.E) z = x := by
  have hm : (x : H.E) ∈ H.F := (H.conjE_mem_hostF_iff _).2 (congrArg (fun y : 𝓞 H.E => (y : H.E)) hx)
  exact ⟨⟨⟨x, hm⟩, (isIntegral_algHom_iff (algebraMap H.F H.E).toIntAlgHom (algebraMap H.F H.E).injective).1
    x.isIntegral_coe⟩, rfl⟩

variable (hun : ∀ Q : HeightOneSpectrum (𝓞 H.E), (p : 𝓞 H.E) ∈ Q.asIdeal → Algebra.IsUnramifiedAt ℤ Q.asIdeal)
  (hfr : ∀ Q : HeightOneSpectrum (𝓞 H.E), (p : 𝓞 H.E) ∈ Q.asIdeal → ∀ σ : H.E ≃ₐ[ℚ] H.E, IsArithFrobAt ℤ σ Q.asIdeal →
    σ = H.sigmaOf (c0, h))
  (h2 : 2 ≤ orderOf h) (he : Even (orderOf h))

omit hp in
include he in
/- English proof (translation)
Establish `: orderOf c0 = 2` using `orderOf_eq_prime (by decide) (by decide)`. Rewrite using `[Prod.orderOf_mk, this]`. Conclude with `Nat.lcm_eq_right he.two_dvd`.
-/
theorem orderOf_frob : orderOf ((c0, h) : R.GG) = orderOf h := by
  have : orderOf c0 = 2 := orderOf_eq_prime (by decide) (by decide)
  rw [Prod.orderOf_mk, this]
  exact Nat.lcm_eq_right he.two_dvd

/- English proof (translation)
Take `⟨g, -, -, hk⟩` from `hi`. Rewrite using `[hk, map_natCast, cc_eq_zero]`.
-/
theorem mem_of_good {E : Type} [Field E] {Q : HeightOneSpectrum (𝓞 E)} {i : E →+* Qn p n} (hi : Good Q i) :
    (p : 𝓞 E) ∈ Q.asIdeal := by
  obtain ⟨g, -, -, hk⟩ := hi
  rw [hk, map_natCast, cc_eq_zero]

include hfr in
/- English proof (translation)
Use `H.hostE_isGalois` as an intermediate fact. Take `⟨τ, hτ⟩` from `exists_aut i ((Fr p n).toRingHom.comp i)`. Rewrite using `[← hfr Q (mem_of_good hi) τ (isArithFrobAt_of hi (mem_of_good hi) τ hτ)]`. Conclude with `hτ x`.
-/
theorem fr_apply {Q : HeightOneSpectrum (𝓞 H.E)} {i : H.E →+* Qn p n} (hi : Good Q i) (x : H.E) :
    Fr p n (i x) = i (H.sigmaOf (c0, h) x) := by
  have := H.hostE_isGalois
  obtain ⟨τ, hτ⟩ := exists_aut i ((Fr p n).toRingHom.comp i)
  rw [← hfr Q (mem_of_good hi) τ (isArithFrobAt_of hi (mem_of_good hi) τ hτ)]
  exact hτ x

include hfr in
/- English proof (translation)
Proceed by induction on `s generalizing x with`. Consider the case `zero => simp [Host.sigmaOf]`. Consider the case `succ s ih => rw [pow_succ, pow_succ, RingAut.mul_apply, fr_apply hfr hi, ih, sigmaOf_mul]`.
-/
theorem fr_pow_apply {Q : HeightOneSpectrum (𝓞 H.E)} {i : H.E →+* Qn p n} (hi : Good Q i) (s : ℕ) (x : H.E) :
    (Fr p n ^ s) (i x) = i (H.sigmaOf ((c0, h) ^ s) x) := by
  induction s generalizing x with
  | zero => simp [Host.sigmaOf]
  | succ s ih => rw [pow_succ, pow_succ, RingAut.mul_apply, fr_apply hfr hi, ih, sigmaOf_mul]

include hfr h2 he in

/- English proof (translation)
Establish `h1 : ((c0, h) : R.GG) ^ n = 1` using `sigmaOf_inj (H := H) (AlgEquiv.ext fun x => i.injective (by`. Rewrite using `[← fr_pow_apply hfr hi, GlobalTheory.SqrtUnif.fractionRing_frobenius_pow p hn]`. Simplify using `[Host.sigmaOf]))`. Establish `h3` using `Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (orderOf_dvd_of_pow_eq_one h1)`. Rewrite `h3` using `[orderOf_frob he]`.

Use `(h3.eq_or_lt.resolve_right fun hlt => ?_).symm` and prove the remaining obligations. Use `hi.pow_inj hn hlt (Nat.pos_of_ne_zero hn) fun x => by` as an intermediate fact. Rewrite using `[fr_pow_apply hfr hi, fr_pow_apply hfr hi, ← orderOf_frob he, pow_orderOf_eq_one, pow_zero]`. Use linear arithmetic over natural numbers and integers.
-/
theorem degree_eq {Q : HeightOneSpectrum (𝓞 H.E)} {i : H.E →+* Qn p n} (hi : Good Q i) (hn : n ≠ 0) : n = orderOf h := by
  have h1 : ((c0, h) : R.GG) ^ n = 1 := sigmaOf_inj (H := H) (AlgEquiv.ext fun x => i.injective (by
    rw [← fr_pow_apply hfr hi, GlobalTheory.SqrtUnif.fractionRing_frobenius_pow p hn]
    simp [Host.sigmaOf]))
  have h3 := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (orderOf_dvd_of_pow_eq_one h1)
  rw [orderOf_frob he] at h3
  refine (h3.eq_or_lt.resolve_right fun hlt => ?_).symm
  have := hi.pow_inj hn hlt (Nat.pos_of_ne_zero hn) fun x => by
    rw [fr_pow_apply hfr hi, fr_pow_apply hfr hi, ← orderOf_frob he, pow_orderOf_eq_one, pow_zero]
  omega

variable {Q₀ : HeightOneSpectrum (𝓞 H.E)} {i : H.E →+* Qn p n} (hi : Good Q₀ i) (hn : n ≠ 0)

include hi in
/- English proof (translation)
The claim follows from `good_aut hi _ fun _ => rfl`.
-/
theorem good_tw (g : R.GG) : Good (plc (tw H i g)) (tw H i g) := good_aut hi _ fun _ => rfl

include hun hfr hi hn in

/- English proof (translation)
Use `hun _ (p_mem_plc (tw H i g))` as an intermediate fact. Take `⟨s, -, hs⟩` from `(good_tw hi g).exists_pow (ι := RingHom.id _) (j := RingHom.id _) hn p_mem (fun _ => rfl) (e ▸ ov_plc (tw H i g'))`. Use `⟨s, sigmaOf_inj (H := H) (AlgEquiv.ext fun x => i.injective ?_)⟩` and prove the remaining obligations. Rewrite using `[sigmaOf_mul]`. Conclude with `(hs x).trans (fr_pow_apply hfr (good_tw hi g) s x)`.
-/
theorem exists_pow_of_plc_eq {g g' : R.GG} (e : plc (tw H i g') = plc (tw H i g)) : ∃ s : ℕ, g' = g * (c0, h) ^ s := by
  have := hun _ (p_mem_plc (tw H i g))
  obtain ⟨s, -, hs⟩ := (good_tw hi g).exists_pow (ι := RingHom.id _) (j := RingHom.id _) hn p_mem (fun _ => rfl)
    (e ▸ ov_plc (tw H i g'))
  refine ⟨s, sigmaOf_inj (H := H) (AlgEquiv.ext fun x => i.injective ?_)⟩
  rw [sigmaOf_mul]
  exact (hs x).trans (fr_pow_apply hfr (good_tw hi g) s x)

include hun hfr he hi hn in

/- English proof (translation)
Introduce `e` and use `by obtain ⟨s, hs⟩ := exists_pow_of_plc_eq hun hfr hi hn e have h1 := (R.toFrame.cc_mem_zpowers_iff (c0, h)).1 (by rw [mul_left_cancel hs]; exact Subgroup.npow_mem_zpowers _ s) exact Nat.not_even_iff_odd.2 h1.2 he`.
-/
theorem plc_ne_conj (g : R.GG) : plc (tw H i (g * R.cc)) ≠ plc (tw H i g) := fun e => by
  obtain ⟨s, hs⟩ := exists_pow_of_plc_eq hun hfr hi hn e
  have h1 := (R.toFrame.cc_mem_zpowers_iff (c0, h)).1 (by
    rw [mul_left_cancel hs]; exact Subgroup.npow_mem_zpowers _ s)
  exact Nat.not_even_iff_odd.2 h1.2 he

include hun hfr he hi hn in

/- English proof (translation)
The claim follows from `good_plc fun y => by obtain ⟨x, z, hz, e⟩ := good_approx (good_tw hi g) y have hco : (plc (tw H i g)).asIdeal ⊔ (plc (tw H i (g * R.cc))).asIdeal = ⊤ := (plc _).isMaximal.coprime_of_ne (plc _).isMaximal fun e => plc_ne_conj hun hfr he hi hn g (HeightOneSpectrum.ext e.symm) obtain …`.
-/
theorem good_twF (g : R.GG) : Good (plc (twF H i g)) (twF H i g) :=
  good_plc fun y => by
    obtain ⟨x, z, hz, e⟩ := good_approx (good_tw hi g) y
    have hco : (plc (tw H i g)).asIdeal ⊔ (plc (tw H i (g * R.cc))).asIdeal = ⊤ :=
      (plc _).isMaximal.coprime_of_ne (plc _).isMaximal fun e =>
        plc_ne_conj hun hfr he hi hn g (HeightOneSpectrum.ext e.symm)
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 (hco ▸ Submodule.mem_top : x ∈ _)
    obtain ⟨t, ht⟩ := exists_real (b + H.conj • b) (by rw [smul_add, conj_conj, add_comm])
    obtain ⟨u, hu, eu⟩ := (mem_plc _ _).1 (sub_mem ((mem_plc_tw_cc i g b).1 hb) ha)
    refine ⟨t, z + u, add_mem hz hu, ?_⟩
    rw [← add_assoc, map_add, e, eu, ← map_add]
    have : x + (H.conj • b - a) = algebraMap (𝓞 H.F) (𝓞 H.E) t := by rw [ht, ← hab]; ring
    exact congrArg (fun y : 𝓞 H.E => tw H i g (y : H.E)) this

include hun hfr hi hn in
/- English proof (translation)
Establish `key : ∀ g g' : R.GG, plc (twF H i g') = plc (twF H i g) → ∃ s m : ℕ, g' = g * (zPsi R.toFrame h : R.GG) ^ s * R.cc ^ m`. Introduce `g g' e`. Establish `hsub : ((plc (tw H i g')).asIdeal : Set (𝓞 H.E)) ⊆ (plc (tw H i g)).asIdeal ∪ (plc (tw H i (g * R.cc))).asIdeal` using `fun y hy => by`. Take `⟨t, ht⟩` from `exists_real (y * H.conj • y) (by rw [smul_mul', conj_conj, mul_comm])`. Establish `h1 : t ∈ (plc (twF H i g')).asIdeal`.

Rewrite using `[mem_plc_twF, ht]`. Conclude with `Ideal.mul_mem_right _ _ hy`. Rewrite `h1` using `[e, mem_plc_twF, ht]`. Conclude with `((plc _).isPrime.mem_or_mem h1).imp id (mem_plc_tw_cc i g y).2`. Break down `Ideal.subset_union.1 hsub with hle | hle` into its components or cases.

Take `⟨s, hs⟩` from `exists_pow_of_plc_eq hun hfr hi hn (HeightOneSpectrum.ext ((plc _).isMaximal.eq_of_le (plc _).isPrime.ne_top hle))`. Conclude with `⟨s, s, by rw [hs, frob_eq_mul, mul_pow, mul_assoc]⟩`. Take `⟨s, hs⟩` from `exists_pow_of_plc_eq hun hfr hi hn (HeightOneSpectrum.ext ((plc _).isMaximal.eq_of_le (plc _).isPrime.ne_top hle))`. Conclude with `⟨s, s + 1, by rw [hs, frob_eq_mul, mul_pow, pow_succ (R.cc)]; ac_rfl⟩`. Introduce `v v' e`.

Take `⟨s, m, hs⟩` from `key _ _ e.symm`. Establish `h1 : R.cc ^ m = 1` using `(cc_pow R.toFrame m).resolve_right fun e' => cc_notMem R.toFrame (by`. Rewrite `hs` using `[e']`. Rewrite using `[← inv_mul_eq_of_eq_mul hs]`. Conclude with `mul_mem (inv_mem (mul_mem (orbRep _ v).2 (pow_mem (zPsi R.toFrame h).2 s))) (orbRep _ v').2)`.

Rewrite `hs` using `[h1, mul_one]`. Establish `h3 : orbRep (zPsi R.toFrame h) v' = orbRep (zPsi R.toFrame h) v * zPsi R.toFrame h ^ s` using `Subtype.ext hs`. Apply `(orbEquiv (zPsi R.toFrame h)).injective` to reduce the goal to its premises. Rewrite using `[← orbRep_mk, ← orbRep_mk, h3, QuotientGroup.mk_mul_of_mem _ (Subgroup.npow_mem_zpowers _ s)]`.
-/
theorem place_injective : Function.Injective fun v : Fin (nOrb (zPsi R.toFrame h)) =>
    plc (twF H i (orbRep (zPsi R.toFrame h) v : R.Psi)) := by
  have key : ∀ g g' : R.GG, plc (twF H i g') = plc (twF H i g) → ∃ s m : ℕ, g' = g * (zPsi R.toFrame h : R.GG) ^ s * R.cc ^ m := by
    intro g g' e
    have hsub : ((plc (tw H i g')).asIdeal : Set (𝓞 H.E)) ⊆
        (plc (tw H i g)).asIdeal ∪ (plc (tw H i (g * R.cc))).asIdeal := fun y hy => by
      obtain ⟨t, ht⟩ := exists_real (y * H.conj • y) (by rw [smul_mul', conj_conj, mul_comm])
      have h1 : t ∈ (plc (twF H i g')).asIdeal := by
        rw [mem_plc_twF, ht]; exact Ideal.mul_mem_right _ _ hy
      rw [e, mem_plc_twF, ht] at h1
      exact ((plc _).isPrime.mem_or_mem h1).imp id (mem_plc_tw_cc i g y).2
    rcases Ideal.subset_union.1 hsub with hle | hle
    · obtain ⟨s, hs⟩ := exists_pow_of_plc_eq hun hfr hi hn
        (HeightOneSpectrum.ext ((plc _).isMaximal.eq_of_le (plc _).isPrime.ne_top hle))
      exact ⟨s, s, by rw [hs, frob_eq_mul, mul_pow, mul_assoc]⟩
    · obtain ⟨s, hs⟩ := exists_pow_of_plc_eq hun hfr hi hn
        (HeightOneSpectrum.ext ((plc _).isMaximal.eq_of_le (plc _).isPrime.ne_top hle))
      exact ⟨s, s + 1, by rw [hs, frob_eq_mul, mul_pow, pow_succ (R.cc)]; ac_rfl⟩
  intro v v' e
  obtain ⟨s, m, hs⟩ := key _ _ e.symm
  have h1 : R.cc ^ m = 1 := (cc_pow R.toFrame m).resolve_right fun e' => cc_notMem R.toFrame (by
    rw [e'] at hs
    rw [← inv_mul_eq_of_eq_mul hs]
    exact mul_mem (inv_mem (mul_mem (orbRep _ v).2 (pow_mem (zPsi R.toFrame h).2 s))) (orbRep _ v').2)
  rw [h1, mul_one] at hs
  have h3 : orbRep (zPsi R.toFrame h) v' = orbRep (zPsi R.toFrame h) v * zPsi R.toFrame h ^ s := Subtype.ext hs
  apply (orbEquiv (zPsi R.toFrame h)).injective
  rw [← orbRep_mk, ← orbRep_mk, h3, QuotientGroup.mk_mul_of_mem _ (Subgroup.npow_mem_zpowers _ s)]

include hun hfr h2 he hi hn in
/- English proof (translation)
Use `H.hostE_isGalois` as an intermediate fact. Use `w.isPrime` as an intermediate fact. Take `⟨⟨P, hP, hPl⟩⟩ : Nonempty (w.asIdeal.primesOver (𝓞 H.E))` from `inferInstance`. Establish `hpP : (p : 𝓞 H.E) ∈ P`. Rewrite `hw` using `[hPl.over, Ideal.mem_comap, map_natCast]`.

Conclude with `hw`. Set `Q : HeightOneSpectrum (𝓞 H.E)` to `⟨P, hP, fun e => by`. Rewrite `hpP` using `[e, Ideal.mem_bot]`. Conclude with `hp.out.ne_zero (Nat.cast_eq_zero.1 hpP)⟩`. Use `hun Q hpP` as an intermediate fact.

Take `⟨m, j, hm, hj⟩` from `exists_good Q hpP`. Take `rfl : m = n` from `(degree_eq hfr h2 he hj hm).trans (degree_eq hfr h2 he hi hn).symm`. Take `⟨τ, hτ⟩` from `exists_aut i j`. Take `⟨g, rfl⟩` from `sigmaOf_surj τ`. Establish `hQ : plc (tw H i g) = Q` using `plc_eq_of_pow hj 0 fun x => (hτ x).symm`.

Establish `hwg : plc (twF H i g) = w` using `HeightOneSpectrum.ext (Ideal.ext fun x => by`. Rewrite using `[mem_plc_twF, hQ, hPl.over]`. Use the proof step `rfl)`. Choose the witnesses or unpack the hypotheses as in `⟨g₀, t, rfl⟩ : ∃ (g₀ : R.Psi) (t : ℕ), g = g₀ * R.cc ^ t := by`. Distinguish the cases in `hg : g ∈ R.Psi`.

Conclude with `⟨⟨g, hg⟩, 0, by simp⟩`. Conclude with `⟨⟨g * R.cc, (Subgroup.mul_mem_iff_of_index_two R.toFrame.index_Psi).2 (iff_of_false hg (cc_notMem _))⟩, 1, by rw [pow_one, mul_assoc, cc_mul_cc, mul_one]⟩`. Take `⟨⟨v, s⟩, rfl⟩` from `(posG (zPsi R.toFrame h)).surjective g₀`. Use `⟨v, ?_⟩` and prove the remaining obligations. Rewrite using `[← hwg, twF_cc_pow, ← twF_cc_pow i ((posG (zPsi R.toFrame h) ⟨v, s⟩ : R.Psi) : R.GG) s.val, posG_apply, Subgroup.coe_mul, Subgroup.coe_pow, mul_assoc, ← mul_pow, ← frob_eq_mul]`.

Use `(plc_eq_of_pow (good_twF hun hfr he hi hn _) s fun x => ?_).symm` and prove the remaining obligations. Use `Eq.trans ?_ (fr_pow_apply hfr (good_tw hi _) s _).symm` and prove the remaining obligations. Conclude with `congrArg i (sigmaOf_mul _ _ _)`.
-/
theorem place_surjective (w : HeightOneSpectrum (𝓞 H.F)) (hw : (p : 𝓞 H.F) ∈ w.asIdeal) :
    ∃ v : Fin (nOrb (zPsi R.toFrame h)), plc (twF H i (orbRep (zPsi R.toFrame h) v : R.Psi)) = w := by
  have := H.hostE_isGalois
  have := w.isPrime
  obtain ⟨⟨P, hP, hPl⟩⟩ : Nonempty (w.asIdeal.primesOver (𝓞 H.E)) := inferInstance
  have hpP : (p : 𝓞 H.E) ∈ P := by
    rw [hPl.over, Ideal.mem_comap, map_natCast] at hw
    exact hw
  let Q : HeightOneSpectrum (𝓞 H.E) := ⟨P, hP, fun e => by
    rw [e, Ideal.mem_bot] at hpP
    exact hp.out.ne_zero (Nat.cast_eq_zero.1 hpP)⟩
  have := hun Q hpP
  obtain ⟨m, j, hm, hj⟩ := exists_good Q hpP
  obtain rfl : m = n := (degree_eq hfr h2 he hj hm).trans (degree_eq hfr h2 he hi hn).symm
  obtain ⟨τ, hτ⟩ := exists_aut i j
  obtain ⟨g, rfl⟩ := sigmaOf_surj τ
  have hQ : plc (tw H i g) = Q := plc_eq_of_pow hj 0 fun x => (hτ x).symm
  have hwg : plc (twF H i g) = w := HeightOneSpectrum.ext (Ideal.ext fun x => by
    rw [mem_plc_twF, hQ, hPl.over]; rfl)
  obtain ⟨g₀, t, rfl⟩ : ∃ (g₀ : R.Psi) (t : ℕ), g = g₀ * R.cc ^ t := by
    by_cases hg : g ∈ R.Psi
    · exact ⟨⟨g, hg⟩, 0, by simp⟩
    · exact ⟨⟨g * R.cc, (Subgroup.mul_mem_iff_of_index_two R.toFrame.index_Psi).2 (iff_of_false hg (cc_notMem _))⟩, 1,
        by rw [pow_one, mul_assoc, cc_mul_cc, mul_one]⟩
  obtain ⟨⟨v, s⟩, rfl⟩ := (posG (zPsi R.toFrame h)).surjective g₀
  refine ⟨v, ?_⟩
  rw [← hwg, twF_cc_pow, ← twF_cc_pow i ((posG (zPsi R.toFrame h) ⟨v, s⟩ : R.Psi) : R.GG) s.val, posG_apply, Subgroup.coe_mul, Subgroup.coe_pow, mul_assoc, ← mul_pow,
    ← frob_eq_mul]
  refine (plc_eq_of_pow (good_twF hun hfr he hi hn _) s fun x => ?_).symm
  refine Eq.trans ?_ (fr_pow_apply hfr (good_tw hi _) s _).symm
  exact congrArg i (sigmaOf_mul _ _ _)

end Host

section Assembly

/- English proof (translation)
Use `choose eQ heQ heW using hE`. Establish `hS : ∀ (w : HeightOneSpectrum (𝓞 F)) (_ : ((p : ℕ) : 𝓞 F) ∈ w.asIdeal), ∃ φ : E ⊗[F] w.adicCompletion F ≃+* w.adicCompletion F × w.adicCompletion F, (∀ x, φ (sigR sp.cm.sig (w.adicCompletion F) x) = swapR _ (φ x)) ∧ (∀ a : w.adicCompletion F, φ ((1 : E) ⊗ₜ[F] a) = (a, a)) ∧ ∀ v, …` using `F) (w.adicCompletion F) x)).1 (eQ v (j v x)) := by`. Introduce `w hw`. Take `⟨v, hv⟩` from `pl.surjective ⟨w, hw⟩`. Take `rfl : (pl v).1 = w` from `congrArg Subtype.val hv`.

Take `⟨φ, h1, h3, h4⟩` from `Formalism.MainNotions.Gaps.Loc.exists_spl sp.cm.sig (fun x => star_star x) sp.cm.deg2 b hb0 hb ({ (eQ v).toRingHom.comp (j v) with commutes' := heQ v } : E →ₐ[F] (pl v).1.adicCompletion F)`. Use `⟨φ, h1, h3, fun v' hv' x => ?_⟩` and prove the remaining obligations. Take `rfl : v' = v` from `pl.injective (Subtype.ext hv')`. Conclude with `heq_of_eq (h4 x)`. Use `choose spl hs1 hs2 hs3 using hS`.

Use `choose fr hfr using fun w hw => exists_first_frame w (spl w hw) (hs2 w hw) L.Lb L.Lb_fin L.Lb_span`. Conclude with `⟨⟨pl, eQ, heW, spl, hs1, hs2, fr, hfr⟩, rfl, fun v x => (eQ v).symm_apply_eq.2 (eq_of_heq (hs3 _ (pl v).2 v rfl x))⟩`.
-/
theorem exists_locId_of_completions {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] {sp : Spaces R F E} {gp : Fin 2 → ℕ}
    {ι' : Type} [Fintype ι'] {hc : ι' → HCParam R} {C : ColumnChain R ι' hc} {A : ColumnsAtT R C}
    {clsLat : ∀ i, C.cls i → Submodule (𝓞 E) (sp.X i).V} (L : ColLevel R F E sp gp C A clsLat) {p nV : ℕ} {W Qq : Type}
    [CommRing W] [Field Qq] [Algebra W Qq] (b : E) (hb0 : b ≠ 0) (hb : star b = -b)
    (pl : Fin nV ≃ {v : HeightOneSpectrum (𝓞 F) // ((p : ℕ) : 𝓞 F) ∈ v.asIdeal}) (j : Fin nV → (E →+* Qq))
    (hE : ∀ v, ∃ e : Qq ≃+* (pl v).1.adicCompletion F, (∀ x : F, e (j v (algebraMap F E x)) = algebraMap F _ x) ∧
      ∀ y, y ∈ Set.range (algebraMap W Qq) ↔ e y ∈ (pl v).1.adicCompletionIntegers F) :
    ∃ I : LocId L p nV W Qq, I.pl = pl ∧ ∀ v x, I.iw v x = j v x := by
  choose eQ heQ heW using hE
  have hS : ∀ (w : HeightOneSpectrum (𝓞 F)) (_ : ((p : ℕ) : 𝓞 F) ∈ w.asIdeal),
      ∃ φ : E ⊗[F] w.adicCompletion F ≃+* w.adicCompletion F × w.adicCompletion F,
        (∀ x, φ (sigR sp.cm.sig (w.adicCompletion F) x) = swapR _ (φ x)) ∧
        (∀ a : w.adicCompletion F, φ ((1 : E) ⊗ₜ[F] a) = (a, a)) ∧
        ∀ v, (pl v).1 = w → ∀ x : E, HEq (φ (inclE (F := F) (w.adicCompletion F) x)).1 (eQ v (j v x)) := by
    intro w hw
    obtain ⟨v, hv⟩ := pl.surjective ⟨w, hw⟩
    obtain rfl : (pl v).1 = w := congrArg Subtype.val hv
    obtain ⟨φ, h1, h3, h4⟩ := Formalism.MainNotions.Gaps.Loc.exists_spl sp.cm.sig (fun x => star_star x) sp.cm.deg2 b hb0 hb
      ({ (eQ v).toRingHom.comp (j v) with commutes' := heQ v } : E →ₐ[F] (pl v).1.adicCompletion F)
    refine ⟨φ, h1, h3, fun v' hv' x => ?_⟩
    obtain rfl : v' = v := pl.injective (Subtype.ext hv')
    exact heq_of_eq (h4 x)
  choose spl hs1 hs2 hs3 using hS
  choose fr hfr using fun w hw => exists_first_frame w (spl w hw) (hs2 w hw) L.Lb L.Lb_fin L.Lb_span
  exact ⟨⟨pl, eQ, heW, spl, hs1, hs2, fr, hfr⟩, rfl, fun v x =>
    (eQ v).symm_apply_eq.2 (eq_of_heq (hs3 _ (pl v).2 v rfl x))⟩

attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Use `H.hostE_isGalois` as an intermediate fact. Establish `hn0 : n ≠ 0` using `by omega`. Choose the witnesses or unpack the hypotheses as in `⟨Q₀, i₀, hi₀⟩ : ∃ (Q₀ : HeightOneSpectrum (𝓞 H.E)) (i₀ : H.E →+* Qn p n), Good Q₀ i₀ := by`. Establish `: (Ideal.span {(p : ℤ)}).IsMaximal` using `Int.ideal_span_isMaximal_of_prime p`. Take `⟨⟨P, hP, hPl⟩⟩ : Nonempty ((Ideal.span {(p : ℤ)}).primesOver (𝓞 H.E))` from `inferInstance`.

Establish `hpP : (p : 𝓞 H.E) ∈ P`. Use `Ideal.mem_span_singleton_self (p : ℤ)` as an intermediate fact. Rewrite `this` using `[hPl.over, Ideal.mem_comap, map_natCast]`. Then use the resulting hypothesis. Set `Q : HeightOneSpectrum (𝓞 H.E)` to `⟨P, hP, fun e => by`. Rewrite `hpP` using `[e, Ideal.mem_bot]`.

Conclude with `hp.out.ne_zero (Nat.cast_eq_zero.1 hpP)⟩`. Use `hun Q hpP` as an intermediate fact. Take `⟨m, j, hm, hj⟩` from `exists_good Q hpP`. Take `rfl : m = n` from `(degree_eq hfr h2 he hj hm).trans hn.symm`. Conclude with `⟨Q, j, hj⟩`.

Establish `hmem : ∀ x : H.E, H.φ₀ x ∈ algebraicClosure ℚ ℂ` using `fun x => mem_algebraicClosure_iff.2 ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).algHom H.φ₀.toRatAlgHom)`. Take `⟨γ, hγ⟩` from `exists_aut (κ.comp i₀) (lam.comp (H.φ₀.codRestrict (algebraicClosure ℚ ℂ) hmem))`. Set `i : H.E →+* Qn p n` to `i₀.comp (γ : H.E →+* H.E)`. Establish `hi : Good (plc i) i` using `good_aut hi₀ γ fun _ => rfl`. Establish `hκ : ∀ x, κ (i x) = lamV lam (H.φ₀ x)` using `fun x => by`.

Rewrite using `[lamV, dif_pos (hmem x)]`. Conclude with `(hγ x).symm`. Set `rp : Fin (nOrb (zPsi R.toFrame h)) → R.GG` to `fun v => (orbRep (zPsi R.toFrame h) v : R.Psi)`. Set `pl : Fin (nOrb (zPsi R.toFrame h)) ≃ {v : HeightOneSpectrum (𝓞 H.F) // ((p : ℕ) : 𝓞 H.F) ∈ v.asIdeal}` to `Equiv.ofBijective (fun v => ⟨plc (twF H i (rp v)), p_mem_plc _⟩) ⟨fun v v' e => place_injective hun hfr hi hn0 (congrArg Subtype.val e), fun w => by`. Take `⟨v, hv⟩` from `place_surjective hun hfr h2 he hi hn0 w.1 w.2`.

Conclude with `⟨v, Subtype.ext hv⟩⟩`. Establish `hb0 : H.sqrtMinusD ≠ 0` using `fun e => by`. Use `H.sqrtMinusD_sq` as an intermediate fact. Rewrite `this` using `[e, zero_pow two_ne_zero, eq_comm, neg_eq_zero, Nat.cast_eq_zero]`. Conclude with `H.hyp.2.1.ne_zero this`.

Take `⟨I, -, hI⟩` from `exists_locId_of_completions (W := WQ p n) L H.sqrtMinusD hb0 ((bridge_star_holds R H _).trans H.conj_sqrtMinusD) pl (fun v => tw H i (rp v)) fun v => exists_completion_equiv (good_twF hun hfr he hi hn0 (rp v))`. Use `⟨I, fun v x => ?_, fun v x => ?_⟩` and prove the remaining obligations. Rewrite using `[hI]`. Conclude with `hκ _`. Rewrite using `[hI, hI]`.

Conclude with `fr_apply hfr (good_tw hi _) x`.
-/
theorem exists_locId_host {R : Ranks} {H : Host R} {p : ℕ} [hp : Fact p.Prime] {h : R.MA}
    (hun : ∀ Q : HeightOneSpectrum (𝓞 H.E), (p : 𝓞 H.E) ∈ Q.asIdeal → Algebra.IsUnramifiedAt ℤ Q.asIdeal)
    (hfr : ∀ Q : HeightOneSpectrum (𝓞 H.E), (p : 𝓞 H.E) ∈ Q.asIdeal → ∀ σ : H.E ≃ₐ[ℚ] H.E, IsArithFrobAt ℤ σ Q.asIdeal →
      σ = H.sigmaOf (c0, h))
    (h2 : 2 ≤ orderOf h) (he : Even (orderOf h)) {n : ℕ} (hn : n = orderOf h)
    {sp : Spaces R H.F H.E} {gp : Fin 2 → ℕ} {ι' : Type} [Fintype ι'] {hc : ι' → HCParam R} {C : ColumnChain R ι' hc}
    {A : ColumnsAtT R C} {clsLat : ∀ i, C.cls i → Submodule (𝓞 H.E) (sp.X i).V}
    (L : ColLevel R H.F H.E sp gp C A clsLat) (κ : QQ p n →+* ℂ_[p]) (lam : (algebraicClosure ℚ ℂ) →+* ℂ_[p]) :
    ∃ I : LocId L p (nOrb (zPsi R.toFrame h)) (WQ p n) (QQ p n),
      (∀ v x, κ (I.iw v x) = lamV lam (H.emb ((orbRep (zPsi R.toFrame h) v : R.Psi) : R.GG) x)) ∧
      ∀ v x, sig p n (I.iw v x) = I.iw v (H.sigmaOf ((c0, h) : R.GG) x) := by
  have := H.hostE_isGalois
  have hn0 : n ≠ 0 := by omega

  obtain ⟨Q₀, i₀, hi₀⟩ : ∃ (Q₀ : HeightOneSpectrum (𝓞 H.E)) (i₀ : H.E →+* Qn p n), Good Q₀ i₀ := by
    have : (Ideal.span {(p : ℤ)}).IsMaximal := Int.ideal_span_isMaximal_of_prime p
    obtain ⟨⟨P, hP, hPl⟩⟩ : Nonempty ((Ideal.span {(p : ℤ)}).primesOver (𝓞 H.E)) := inferInstance
    have hpP : (p : 𝓞 H.E) ∈ P := by
      have := Ideal.mem_span_singleton_self (p : ℤ)
      rwa [hPl.over, Ideal.mem_comap, map_natCast] at this
    let Q : HeightOneSpectrum (𝓞 H.E) := ⟨P, hP, fun e => by
      rw [e, Ideal.mem_bot] at hpP
      exact hp.out.ne_zero (Nat.cast_eq_zero.1 hpP)⟩
    have := hun Q hpP
    obtain ⟨m, j, hm, hj⟩ := exists_good Q hpP
    obtain rfl : m = n := (degree_eq hfr h2 he hj hm).trans hn.symm
    exact ⟨Q, j, hj⟩

  have hmem : ∀ x : H.E, H.φ₀ x ∈ algebraicClosure ℚ ℂ := fun x =>
    mem_algebraicClosure_iff.2 ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).algHom H.φ₀.toRatAlgHom)
  obtain ⟨γ, hγ⟩ := exists_aut (κ.comp i₀) (lam.comp (H.φ₀.codRestrict (algebraicClosure ℚ ℂ) hmem))
  let i : H.E →+* Qn p n := i₀.comp (γ : H.E →+* H.E)
  have hi : Good (plc i) i := good_aut hi₀ γ fun _ => rfl
  have hκ : ∀ x, κ (i x) = lamV lam (H.φ₀ x) := fun x => by
    rw [lamV, dif_pos (hmem x)]
    exact (hγ x).symm
  let rp : Fin (nOrb (zPsi R.toFrame h)) → R.GG := fun v => (orbRep (zPsi R.toFrame h) v : R.Psi)
  let pl : Fin (nOrb (zPsi R.toFrame h)) ≃ {v : HeightOneSpectrum (𝓞 H.F) // ((p : ℕ) : 𝓞 H.F) ∈ v.asIdeal} :=
    Equiv.ofBijective (fun v => ⟨plc (twF H i (rp v)), p_mem_plc _⟩)
      ⟨fun v v' e => place_injective hun hfr hi hn0 (congrArg Subtype.val e), fun w => by
        obtain ⟨v, hv⟩ := place_surjective hun hfr h2 he hi hn0 w.1 w.2
        exact ⟨v, Subtype.ext hv⟩⟩
  have hb0 : H.sqrtMinusD ≠ 0 := fun e => by
    have := H.sqrtMinusD_sq
    rw [e, zero_pow two_ne_zero, eq_comm, neg_eq_zero, Nat.cast_eq_zero] at this
    exact H.hyp.2.1.ne_zero this
  obtain ⟨I, -, hI⟩ := exists_locId_of_completions (W := WQ p n) L H.sqrtMinusD hb0
    ((bridge_star_holds R H _).trans H.conj_sqrtMinusD) pl (fun v => tw H i (rp v))
    fun v => exists_completion_equiv (good_twF hun hfr he hi hn0 (rp v))
  refine ⟨I, fun v x => ?_, fun v x => ?_⟩
  · rw [hI]
    exact hκ _
  · rw [hI, hI]
    exact fr_apply hfr (good_tw hi _) x

open GlobalTheory.Mem.LocalPack Formalism.MainNotions Formalism.MainNotions.G

attribute [local instance] Formalism.BasicNotions.factResChar

/- English proof (translation)
Establish `hn : frobOrder D (D.what₂.places.resChar w) = orderOf (D.R.iota (hP D (D.what₂.places.resChar w)))` using `orderOf_zPsi _ _`. Take `⟨h2, hq, hd, -, -⟩` from `Formalism.BasicNotions.Examples₂.LevelValuationRings.of_cls D.host _ hg.2.2.1`. Establish `hN : ¬ D.what₂.places.resChar w ∣ D.host.condN` using `fun hdv => ((D.host.toHostRaw.dvd_condN_iff_small hg.1).1 hdv).elim h2 fun h' => h'.elim hq hd`. Use `D.host.hostE_isGalois` as an intermediate fact. Take `⟨I, h1, h3⟩` from `exists_locId_host (H := D.host) (p := D.what₂.places.resChar w) (h := D.R.iota (hP D (D.what₂.places.resChar w))) (fun Q hQ => by`.

Use `liesOver_of_mem Q hQ` as an intermediate fact. Conclude with `unramified_of_inertia _ fun σ hσ => ((D.host.der.frob _ hN Q.asIdeal).2.2.2 σ).1 hσ)`. Use the proof step `(fun Q hQ σ hσ => by`. Use `liesOver_of_mem Q hQ` as an intermediate fact. Conclude with `((D.host.gal).symm_apply_eq.2 (frob_eq D hg Q.asIdeal σ hσ).symm).symm)`.

Use the proof step `(hn ▸ (frobOrder_spec D hg).1) (hn ▸ (frobOrder_spec D hg).2) hn Lc`. Use the proof step `(iK.comp ((extRec D w (frobOrder D (D.what₂.places.resChar w))).φK.comp (iota _ _))) lam`. Conclude with `⟨I, fun ψ => posCompat_of_base D.host _ _ _ I.iw iK lam h1 h3⟩`.
-/
theorem exists_locId_of_emb (D : D7) (u : D.what₂.Word)
    (Lc : ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u)) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))
    (iK : KfRec D w (frobOrder D (D.what₂.places.resChar w)) →+* ℂ_[(D.what₂.places.resChar w)])
    (lam : (algebraicClosure ℚ ℂ) →+* ℂ_[(D.what₂.places.resChar w)]) :
    ∃ I : LocId Lc (D.what₂.places.resChar w) (nOrb (zH D.R.toFrame (hP D (D.what₂.places.resChar w))))
        (WQ (D.what₂.places.resChar w) (frobOrder D (D.what₂.places.resChar w)))
        (QQ (D.what₂.places.resChar w) (frobOrder D (D.what₂.places.resChar w))),
      ∀ ψ, (pack D u Lc w hg.2.1 (frobOrder_spec D hg).1 (frobOrder_spec D hg).2 I ψ).posOK iK lam := by
  have hn : frobOrder D (D.what₂.places.resChar w) = orderOf (D.R.iota (hP D (D.what₂.places.resChar w))) :=
    orderOf_zPsi _ _
  obtain ⟨h2, hq, hd, -, -⟩ := Formalism.BasicNotions.Examples₂.LevelValuationRings.of_cls D.host _ hg.2.2.1
  have hN : ¬ D.what₂.places.resChar w ∣ D.host.condN := fun hdv =>
    ((D.host.toHostRaw.dvd_condN_iff_small hg.1).1 hdv).elim h2 fun h' => h'.elim hq hd
  have := D.host.hostE_isGalois
  obtain ⟨I, h1, h3⟩ := exists_locId_host (H := D.host) (p := D.what₂.places.resChar w)
    (h := D.R.iota (hP D (D.what₂.places.resChar w)))
    (fun Q hQ => by
      have := liesOver_of_mem Q hQ
      exact unramified_of_inertia _ fun σ hσ => ((D.host.der.frob _ hN Q.asIdeal).2.2.2 σ).1 hσ)
    (fun Q hQ σ hσ => by
      have := liesOver_of_mem Q hQ
      exact ((D.host.gal).symm_apply_eq.2 (frob_eq D hg Q.asIdeal σ hσ).symm).symm)
    (hn ▸ (frobOrder_spec D hg).1) (hn ▸ (frobOrder_spec D hg).2) hn Lc
    (iK.comp ((extRec D w (frobOrder D (D.what₂.places.resChar w))).φK.comp (iota _ _))) lam
  exact ⟨I, fun ψ => posCompat_of_base D.host _ _ _ I.iw iK lam h1 h3⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨(iC (Formalism.L2.G.Pend.k0ToC _)).comp (gL _), fun x => (iC_int_Cp _ (fun y => (Formalism.L2.G.Pend.norm_k0ToC_le_iff _ _).2 ⟨y, rfl⟩) _).symm.trans (Oc_K _ x)⟩`.
-/
theorem exists_emb_norm (D : D7) (w : D.what₂.places.Pl) (n : ℕ) :
    ∃ iK : KfRec D w n →+* ℂ_[(D.what₂.places.resChar w)],
      ∀ x, ‖iK x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap (ORec D w n) (KfRec D w n)) :=
  ⟨(iC (Formalism.L2.G.Pend.k0ToC _)).comp (gL _), fun x =>
    (iC_int_Cp _ (fun y => (Formalism.L2.G.Pend.norm_k0ToC_le_iff _ _).2 ⟨y, rfl⟩) _).symm.trans (Oc_K _ x)⟩

/- English proof (translation)
Introduce `D u Lc w hg`. Take `⟨iK, -⟩` from `exists_emb_norm D w (frobOrder D (D.what₂.places.resChar w))`. Take `⟨lam, hlam⟩` from `GlobalTheory.PadicPlaceExt.exists_lam D.what₂.embLL (iK.comp (embRec D w _))`. Take `⟨I, hI⟩` from `exists_locId_of_emb D u Lc w hg iK lam`. Conclude with `⟨I, iK, lam, hlam, hI⟩`.
-/
theorem exists_locId : ∀ (D : D7) (u : D.what₂.Word)
    (Lc : ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u)) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
    ∃ (I : LocId Lc (D.what₂.places.resChar w) (nOrb (zH D.R.toFrame (hP D (D.what₂.places.resChar w))))
        (WQ (D.what₂.places.resChar w) (frobOrder D (D.what₂.places.resChar w)))
        (QQ (D.what₂.places.resChar w) (frobOrder D (D.what₂.places.resChar w))))
      (iK : KfRec D w (frobOrder D (D.what₂.places.resChar w)) →+* ℂ_[(D.what₂.places.resChar w)])
      (lam : (algebraicClosure ℚ ℂ) →+* ℂ_[(D.what₂.places.resChar w)]),
      (∀ z : D.what₂.LL, iK (embRec D w (frobOrder D (D.what₂.places.resChar w)) z) = lamV lam (D.what₂.embLL z)) ∧
      ∀ ψ, (pack D u Lc w hg.2.1 (frobOrder_spec D hg).1 (frobOrder_spec D hg).2 I ψ).posOK iK lam := by
  intro D u Lc w hg
  obtain ⟨iK, -⟩ := exists_emb_norm D w (frobOrder D (D.what₂.places.resChar w))
  obtain ⟨lam, hlam⟩ := GlobalTheory.PadicPlaceExt.exists_lam D.what₂.embLL (iK.comp (embRec D w _))
  obtain ⟨I, hI⟩ := exists_locId_of_emb D u Lc w hg iK lam
  exact ⟨I, iK, lam, hlam, hI⟩

end Assembly

end GlobalTheory.PlaceOrbit
