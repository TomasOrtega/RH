import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.IsHermForm
import Formalism.LocalToGlobal.ProjectiveLattices.ThClass
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CramerMemAdelicCompletionOfElementSet
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicHermitianFormGaloisMemOfMemCompletion
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsDenominatorPrimesPrescribed
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IdempotentAdelesAndSmallAdelicMatrices
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.StandardHermitianFormHostFieldInhabitant
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.UnitaryClassNumberDecomposition
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUnitaryAdelicDecompositionSplitSupportStatement

open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open scoped TensorProduct Matrix

namespace GlobalTheory.UnRep.FullReps

open GlobalTheory.AdLat.Translate GlobalTheory.UnRep.SmallMat

/- English proof (translation)
Set `s : Setoid (Fin m₀)` to `⟨fun i j => r (f i) (f j), ⟨fun _ => hr.refl _, hr.symm, hr.trans⟩⟩`. Use `haveI : Fintype (Quotient s) := Fintype.ofFinite _`. Set `e` to `Fintype.equivFin (Quotient s)`. Use `⟨_, fun j => (e.symm j).out, fun g i hg => ⟨e (Quotient.mk s i), ?_, fun j hj => ?_⟩⟩` and prove the remaining obligations. Simplify using `only [Equiv.symm_apply_apply]`.

Conclude with `hr.trans hg (hr.symm (Quotient.mk_out (s := s) i))`. Establish `: Quotient.mk s (e.symm j).out = Quotient.mk s i` using `Quotient.sound (hr.trans (hr.symm hj) hg)`. Rewrite using `[← this, Quotient.out_eq, Equiv.apply_symm_apply]`.
-/
theorem exists_subfamily {α : Type} (r : α → α → Prop) (hr : Equivalence r) {m₀ : ℕ} (f : Fin m₀ → α) :
    ∃ (m : ℕ) (ι : Fin m → Fin m₀), ∀ g i, r g (f i) → ∃! j, r g (f (ι j)) := by
  classical
  let s : Setoid (Fin m₀) := ⟨fun i j => r (f i) (f j), ⟨fun _ => hr.refl _, hr.symm, hr.trans⟩⟩
  haveI : Fintype (Quotient s) := Fintype.ofFinite _
  let e := Fintype.equivFin (Quotient s)
  refine ⟨_, fun j => (e.symm j).out, fun g i hg => ⟨e (Quotient.mk s i), ?_, fun j hj => ?_⟩⟩
  · simp only [Equiv.symm_apply_apply]
    exact hr.trans hg (hr.symm (Quotient.mk_out (s := s) i))
  · have : Quotient.mk s (e.symm j).out = Quotient.mk s i := Quotient.sound (hr.trans (hr.symm hj) hg)
    rw [← this, Quotient.out_eq, Equiv.apply_symm_apply]

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}

/- English proof (translation)
The claim follows from `Matrix.map_mul (f := (Algebra.TensorProduct.includeRight : E →ₐ[F] RA F E).toRingHom)`.
-/
theorem fm_mul (A B : Matrix (Fin n) (Fin n) E) : fm F (A * B) = fm F A * fm F B :=
  Matrix.map_mul (f := (Algebra.TensorProduct.includeRight :
    E →ₐ[F] RA F E).toRingHom)

/- English proof (translation)
The claim follows from `Matrix.map_one _ (by simp) rfl`.
-/
theorem fm_one : fm F (1 : Matrix (Fin n) (Fin n) E) = 1 :=
  Matrix.map_one _ (by simp) rfl

variable [NumberField E]

def Rel (c : E ≃ₐ[F] E) (L : Submodule (𝓞 E) (Fin n → E)) (N : ℕ) (g g' : GL (Fin n) (RA F E)) : Prop :=
  ∃ (γ : GL (Fin n) E) (k : GL (Fin n) (RA F E)), IsUnE c 1 γ.1 ∧ (IsUnA c 1 k.1 ∧
    ∀ z ∈ hat F (L : Set (Fin n → E)), ∃ w ∈ hat F (L : Set (Fin n → E)), k.1 *ᵥ z - z = N • w) ∧
    g.1 = fm F γ.1 * g'.1 * k.1

def Bd (L : Submodule (𝓞 E) (Fin n → E)) (a : 𝓞 E) (M : Matrix (Fin n) (Fin n) (RA F E)) : Prop :=
  ∀ z ∈ hat F (L : Set (Fin n → E)),
    ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (a : E) : RA F E) • (M *ᵥ z) ∈ hat F (L : Set (Fin n → E))

omit [NumberField E] in
/- English proof (translation)
Introduce `z hz` and use `by have := hat_smul_ring L b (h z hz) rw [smul_smul, Algebra.TensorProduct.tmul_mul_tmul, one_mul] at this simpa using this`.
-/
theorem Bd.mul {L : Submodule (𝓞 E) (Fin n → E)} {a : 𝓞 E} {M : Matrix (Fin n) (Fin n) (RA F E)}
    (h : Bd L a M) (b : 𝓞 E) : Bd L (b * a) M := fun z hz => by
  have := hat_smul_ring L b (h z hz)
  rw [smul_smul, Algebra.TensorProduct.tmul_mul_tmul, one_mul] at this
  simpa using this

omit [NumberField E] in
/- English proof (translation)
Introduce `z hz` and use `by have := add_mem (h z hz) (hat_smul_ring L a hz) rwa [← smul_add, Matrix.sub_mulVec, Matrix.one_mulVec, sub_add_cancel] at this`.
-/
theorem Bd.of_sub_one {L : Submodule (𝓞 E) (Fin n → E)} {a : 𝓞 E} {M : Matrix (Fin n) (Fin n) (RA F E)}
    (h : Bd L a (M - 1)) : Bd L a M := fun z hz => by
  have := add_mem (h z hz) (hat_smul_ring L a hz)
  rwa [← smul_add, Matrix.sub_mulVec, Matrix.one_mulVec, sub_add_cancel] at this

omit [NumberField E] in
/- English proof (translation)
Establish `: (h⁻¹).1 - 1 = -((h⁻¹).1 * (h.1 - 1))`. Rewrite using `[mul_sub, Units.inv_mul, mul_one, neg_sub]`. Rewrite using `[this, smul_neg, ← Matrix.mul_smul, he]`.
-/
theorem cut_inv (h : GL (Fin n) (RA F E)) (e : RA F E) (he : e • (h.1 - 1) = h.1 - 1) :
    e • ((h⁻¹).1 - 1) = (h⁻¹).1 - 1 := by
  have : (h⁻¹).1 - 1 = -((h⁻¹).1 * (h.1 - 1)) := by
    rw [mul_sub, Units.inv_mul, mul_one, neg_sub]
  rw [this, smul_neg, ← Matrix.mul_smul, he]

/- English proof (translation)
Take `⟨t, ht, h⟩` from `(idempotent_adeles_small_matrices F E n L hL hsp).2.2.2.1 N 1 e (M - 1) one_pos he`. Use `⟨t, ht, Bd.of_sub_one fun z hz => ?_⟩` and prove the remaining obligations. Take `⟨w, hw, h⟩` from `h z hz`. Rewrite `h` using `[hM, one_smul]`. Establish `: ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] ((t : 𝓞 E) : E) : RA F E) = (t : RA F E)`.

Rewrite using `[show ((t : 𝓞 E) : E) = (t : E) from map_natCast (algebraMap (𝓞 E) E) t]`. Conclude with `map_natCast (Algebra.TensorProduct.includeRight : E →ₐ[F] RA F E) t`. Rewrite using `[this, Nat.cast_smul_eq_nsmul, h]`. Conclude with `hw`.
-/
theorem exists_nat_bd (L : Submodule (𝓞 E) (Fin n → E)) (hL : L.FG)
    (hsp : Submodule.span E (L : Set (Fin n → E)) = ⊤) (N : ℕ) (e : FiniteAdeleRing (𝓞 F) F)
    (he : ∀ v : HeightOneSpectrum (𝓞 F), (N : 𝓞 F) ∈ v.asIdeal → e v = 0)
    (M : Matrix (Fin n) (Fin n) (RA F E)) (hM : (e ⊗ₜ[F] (1 : E) : RA F E) • (M - 1) = M - 1) :
    ∃ t : ℕ, t.Coprime N ∧ Bd L (t : 𝓞 E) M := by
  obtain ⟨t, ht, h⟩ := (idempotent_adeles_small_matrices F E n L hL hsp).2.2.2.1 N 1 e (M - 1) one_pos he
  refine ⟨t, ht, Bd.of_sub_one fun z hz => ?_⟩
  obtain ⟨w, hw, h⟩ := h z hz
  rw [hM, one_smul] at h
  have : ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] ((t : 𝓞 E) : E) : RA F E) = (t : RA F E) := by
    rw [show ((t : 𝓞 E) : E) = (t : E) from map_natCast (algebraMap (𝓞 E) E) t]
    exact map_natCast (Algebra.TensorProduct.includeRight : E →ₐ[F] RA F E) t
  rw [this, Nat.cast_smul_eq_nsmul, h]
  exact hw

/- English proof (translation)
Take `⟨d, hd, hb⟩` from `(idempotent_adeles_small_matrices F E n L hL hsp).2.1 (M - 1)`. Establish `hK : (d : F) ≠ 0` using `Nat.cast_ne_zero.2 hd.ne'`. Use `set b : FiniteAdeleRing (𝓞 F) F := algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F)⁻¹ * e with hbdef`. Establish `hbe : e = d • b`. Rewrite using `[hbdef, nsmul_eq_mul, ← mul_assoc, ← map_natCast (algebraMap F (FiniteAdeleRing (𝓞 F) F)), ← map_mul, mul_inv_cancel₀ hK, map_one, one_mul]`.

Establish `hb0 : ∀ v, e v = 0 → b v = 0` using `fun v hv => by`. Express the relevant statement in the definitionally equal form `_ * e v = 0`. Rewrite using `[hv, mul_zero]`. Use `clear_value b`. Take `⟨x, a, ha, hx⟩` from `exists_eq_algebraMap_add_nsmul F 1 one_pos b`.

Rewrite `hx` using `[one_smul]`. Take `⟨s, hs0, hs, hsx⟩` from `exists_denominator_primes_prescribed F (fun P => ∀ v : HeightOneSpectrum (𝓞 F), v.asIdeal = P → e v ≠ 0) Unit (fun _ => x) (by`. Introduce `_ v hv`. Establish `hv' : e v = 0`. Assume the negation of the conclusion as `h`.

Conclude with `hv fun w hw => by rwa [HeightOneSpectrum.ext hw]`. Establish `h1 : algebraMap F (FiniteAdeleRing (𝓞 F) F) x v + a v = 0`. Rewrite using `[← hb0 v hv', hx]`. Both sides reduce to the same expression. Establish `h2 : algebraMap F (FiniteAdeleRing (𝓞 F) F) x v ∈ v.adicCompletionIntegers F`.

Rewrite using `[eq_neg_of_add_eq_zero_left h1]`. Conclude with `neg_mem (ha v)`. Simplify `h2)` using `only [FiniteAdeleRing.algebraMap_apply, HeightOneSpectrum.mem_adicCompletionIntegers, HeightOneSpectrum.valuedAdicCompletion_eq_valuation']`. Take `⟨y, hy⟩` from `hsx ()`. Use `⟨s, hs0, fun v hv => hs _ v.isPrime hv v rfl, Bd.of_sub_one fun z hz => ?_⟩` and prove the remaining obligations.

Establish `hint : ∀ v, (algebraMap F (FiniteAdeleRing (𝓞 F) F) (s : F) * b) v ∈ v.adicCompletionIntegers F`. Introduce `v`. Rewrite using `[hx, mul_add, ← map_mul, hy]`. Conclude with `adele_add_integral F ((mem_range_iff_adele_integral F _).1 ⟨y, rfl⟩ v) (adele_mul_integral F ((mem_range_iff_adele_integral F _).1 ⟨s, rfl⟩ v) (ha v))`. Use `hat_smul_int hint (hb z hz)` as an intermediate fact.

Use `this using 1` and compare the differences between its conclusion and the goal. Use `conv_lhs => rw [← hM, hbe, nsmul_tmul_one, Matrix.smul_mulVec, smul_assoc, ← smul_comm d]`. Rewrite using `[← smul_comm d, smul_smul]`. Use `congr 2`. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one, ← Algebra.smul_def, TensorProduct.smul_tmul, Algebra.smul_def, mul_one]`.

Both sides reduce to the same expression.
-/
theorem exists_supp_bd (L : Submodule (𝓞 E) (Fin n → E)) (hL : L.FG)
    (hsp : Submodule.span E (L : Set (Fin n → E)) = ⊤) (e : FiniteAdeleRing (𝓞 F) F)
    (M : Matrix (Fin n) (Fin n) (RA F E)) (hM : (e ⊗ₜ[F] (1 : E) : RA F E) • (M - 1) = M - 1) :
    ∃ s : 𝓞 F, s ≠ 0 ∧ (∀ v : HeightOneSpectrum (𝓞 F), s ∈ v.asIdeal → e v ≠ 0) ∧
      Bd L (algebraMap (𝓞 F) (𝓞 E) s) M := by
  obtain ⟨d, hd, hb⟩ := (idempotent_adeles_small_matrices F E n L hL hsp).2.1 (M - 1)
  have hK : (d : F) ≠ 0 := Nat.cast_ne_zero.2 hd.ne'
  set b : FiniteAdeleRing (𝓞 F) F := algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F)⁻¹ * e with hbdef
  have hbe : e = d • b := by
    rw [hbdef, nsmul_eq_mul, ← mul_assoc, ← map_natCast (algebraMap F (FiniteAdeleRing (𝓞 F) F)),
      ← map_mul, mul_inv_cancel₀ hK, map_one, one_mul]
  have hb0 : ∀ v, e v = 0 → b v = 0 := fun v hv => by
    change _ * e v = 0
    rw [hv, mul_zero]
  clear_value b
  obtain ⟨x, a, ha, hx⟩ := exists_eq_algebraMap_add_nsmul F 1 one_pos b
  rw [one_smul] at hx
  obtain ⟨s, hs0, hs, hsx⟩ := exists_denominator_primes_prescribed F
    (fun P => ∀ v : HeightOneSpectrum (𝓞 F), v.asIdeal = P → e v ≠ 0) Unit (fun _ => x) (by
      intro _ v hv
      have hv' : e v = 0 := by
        by_contra h
        exact hv fun w hw => by rwa [HeightOneSpectrum.ext hw]
      have h1 : algebraMap F (FiniteAdeleRing (𝓞 F) F) x v + a v = 0 := by
        rw [← hb0 v hv', hx]; rfl
      have h2 : algebraMap F (FiniteAdeleRing (𝓞 F) F) x v ∈ v.adicCompletionIntegers F := by
        rw [eq_neg_of_add_eq_zero_left h1]; exact neg_mem (ha v)
      simpa only [FiniteAdeleRing.algebraMap_apply, HeightOneSpectrum.mem_adicCompletionIntegers,
        HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] using h2)
  obtain ⟨y, hy⟩ := hsx ()
  refine ⟨s, hs0, fun v hv => hs _ v.isPrime hv v rfl, Bd.of_sub_one fun z hz => ?_⟩
  have hint : ∀ v, (algebraMap F (FiniteAdeleRing (𝓞 F) F) (s : F) * b) v ∈ v.adicCompletionIntegers F := by
    intro v
    rw [hx, mul_add, ← map_mul, hy]
    exact adele_add_integral F ((mem_range_iff_adele_integral F _).1 ⟨y, rfl⟩ v)
      (adele_mul_integral F ((mem_range_iff_adele_integral F _).1 ⟨s, rfl⟩ v) (ha v))
  have := hat_smul_int hint (hb z hz)
  convert this using 1
  conv_lhs => rw [← hM, hbe, nsmul_tmul_one, Matrix.smul_mulVec, smul_assoc, ← smul_comm d]
  rw [← smul_comm d, smul_smul]
  congr 2
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one, ← Algebra.smul_def, TensorProduct.smul_tmul,
    Algebra.smul_def, mul_one]
  rfl

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `v hv`. Take `⟨z, hz, e⟩ : v ∈ latOf F h.1 L` from `hΛ ▸ hv`. Rewrite using `[← (hat_rational_points_and_approx F E n L hL hsp).1]`. Establish `: a • v = (a : E) • v` using `rfl`.

Rewrite using `[this, fv_smul, ← e]`. Conclude with `h1 z hz`. Introduce `v hv`. Establish `: a • v ∈ latOf F h.1 L`. Use `⟨_, h2 _ (fv_mem_hat hv), ?_⟩` and prove the remaining obligations.

Establish `: a • v = (a : E) • v` using `rfl`. Rewrite using `[this, fv_smul, Matrix.mulVec_smul, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]`. Rewrite `this` using `[← hΛ]`. Then use the resulting hypothesis.
-/
theorem smul_mem_of_bd {L Λ : Submodule (𝓞 E) (Fin n → E)} (hL : L.FG)
    (hsp : Submodule.span E (L : Set (Fin n → E)) = ⊤) {h : GL (Fin n) (RA F E)}
    (hΛ : (Λ : Set (Fin n → E)) = latOf F h.1 L) {a : 𝓞 E} (h1 : Bd L a h.1) (h2 : Bd L a (h⁻¹).1) :
    (∀ v ∈ Λ, a • v ∈ L) ∧ ∀ v ∈ L, a • v ∈ Λ := by
  constructor
  · intro v hv
    obtain ⟨z, hz, e⟩ : v ∈ latOf F h.1 L := hΛ ▸ hv
    rw [← (hat_rational_points_and_approx F E n L hL hsp).1]
    have : a • v = (a : E) • v := rfl
    rw [this, fv_smul, ← e]
    exact h1 z hz
  · intro v hv
    have : a • v ∈ latOf F h.1 L := by
      refine ⟨_, h2 _ (fv_mem_hat hv), ?_⟩
      have : a • v = (a : E) • v := rfl
      rw [this, fv_smul, Matrix.mulVec_smul, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
    rwa [← hΛ] at this

end General

section CM

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

noncomputable def conjLat (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Λ : Submodule (𝓞 E) (Fin n → E)) : GenLat E n :=
  ⟨{ carrier := {v | (fun j => IsCMField.complexConj E (v j)) ∈ Λ}
     add_mem' := fun {x y} hx hy => by
       have := Λ.add_mem hx hy
       simp only [Set.mem_setOf_eq, Pi.add_apply, map_add]
       exact this
     zero_mem' := by
       simp only [Set.mem_setOf_eq, Pi.zero_apply, map_zero]
       exact Λ.zero_mem
     smul_mem' := fun a x hx => by
       have := Λ.smul_mem (H.bar a) hx
       simp only [Set.mem_setOf_eq]
       convert this using 1
       funext j
       change IsCMField.complexConj E ((a : E) * x j) = ((H.bar a : 𝓞 E) : E) * _
       rw [map_mul, H.bar_eq] }⟩

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_conjLat (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Λ : Submodule (𝓞 E) (Fin n → E)) (v : Fin n → E) :
    v ∈ (conjLat H Λ).La ↔ (fun j => IsCMField.complexConj E (v j)) ∈ Λ := Iff.rfl

/- English proof (translation)
Take `⟨a, rfl⟩` from `Submodule.mem_one.1 hx`. Conclude with `Submodule.mem_one.2 ⟨H.bar a, H.bar_eq a⟩`.
-/
theorem conj_mem_range (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) {x : E} (hx : x ∈ (1 : Submodule (𝓞 E) E)) :
    IsCMField.complexConj E x ∈ (1 : Submodule (𝓞 E) E) := by
  obtain ⟨a, rfl⟩ := Submodule.mem_one.1 hx
  exact Submodule.mem_one.2 ⟨H.bar a, H.bar_eq a⟩

/- English proof (translation)
Introduce `j _` and use `conj_mem_range H (hv j trivial)`.
-/
theorem conj_mem_std (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) {v : Fin n → E} (hv : v ∈ stdLat E n) :
    (fun j => IsCMField.complexConj E (v j)) ∈ stdLat E n := fun j _ => conj_mem_range H (hv j trivial)

/- English proof (translation)
Simplify using `only [Submodule.ideal_span_singleton_smul]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `_ ⟨v, hv, rfl⟩`. Use `conj_mem_std H (h.1 _ hv)` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal.

Use function extensionality and compare the values at `j`. Express the relevant statement in the definitionally equal form `(a : E) * v j = IsCMField.complexConj E ((a : E) * IsCMField.complexConj E (v j))`. Rewrite using `[map_mul, ha, IsCMField.complexConj_apply_apply]`. Introduce and unpack `_ ⟨v, hv, rfl⟩`. Use `h.2 _ (conj_mem_std H hv)` as an intermediate fact.

Rewrite using `[mem_conjLat]`. Use `this using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `j`. Express the relevant statement in the definitionally equal form `IsCMField.complexConj E ((a : E) * v j) = (a : E) * IsCMField.complexConj E (v j)`. Rewrite using `[map_mul, ha]`.
-/
theorem conjLat_le (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) {Λ : Submodule (𝓞 E) (Fin n → E)} {a : 𝓞 E}
    (ha : IsCMField.complexConj E (a : E) = a)
    (h : (∀ v ∈ Λ, a • v ∈ stdLat E n) ∧ ∀ v ∈ stdLat E n, a • v ∈ Λ) :
    Ideal.span {a} • (conjLat H Λ).La ≤ stdLat E n ∧ Ideal.span {a} • stdLat E n ≤ (conjLat H Λ).La := by
  simp only [Submodule.ideal_span_singleton_smul]
  constructor
  · rintro _ ⟨v, hv, rfl⟩
    have := conj_mem_std H (h.1 _ hv)
    convert this using 1
    funext j
    change (a : E) * v j = IsCMField.complexConj E ((a : E) * IsCMField.complexConj E (v j))
    rw [map_mul, ha, IsCMField.complexConj_apply_apply]
  · rintro _ ⟨v, hv, rfl⟩
    have := h.2 _ (conj_mem_std H hv)
    rw [mem_conjLat]
    convert this using 1
    funext j
    change IsCMField.complexConj E ((a : E) * v j) = (a : E) * IsCMField.complexConj E (v j)
    rw [map_mul, ha]

/- English proof (translation)
The claim follows from `StdInhab.hermE_one _ x y`.
-/
theorem sum_one (x y : Fin n → E) :
    ∑ a, ∑ b, x a * (1 : Matrix (Fin n) (Fin n) E) a b * IsCMField.complexConj E (y b) =
      ∑ a, x a * IsCMField.complexConj E (y a) := StdInhab.hermE_one _ x y

/- English proof (translation)
Take `⟨⟨h1, -, h2, h3⟩, -, hfg, hsp, -⟩` from `StdInhab.main E H n`. Establish `key` using `latOf_selfDual (maximalRealSubfield E) E n (stdLat E n) (IsCMField.complexConj E) 1 1 h hfg hsp h1 h2 h3 one_ne_zero (fun v => by`. Simplify using `only [sum_one]`. Prove the components needed by the constructor for the conclusion. Introduce `hv j _`.

Use `hv _ (StdInhab.single_mem n j)` as an intermediate fact. Establish `e : ∑ a, v a * IsCMField.complexConj E ((Pi.single j (1 : E) : Fin n → E) a) = v j`. Simplify using `[Pi.single_apply, apply_ite]`. Rewrite `this` using `[e]`. Conclude with `Submodule.mem_one.2 ((FractionalIdeal.mem_one_iff _).1 this)`.

Introduce `hv y hy`. Use `(FractionalIdeal.mem_one_iff _).2 (Submodule.mem_one.1 ?_)` and prove the remaining obligations. Use `Submodule.sum_mem _ fun a _ => ?_` and prove the remaining obligations. Use `Submodule.mul_mem_mul (hv a trivial) (conj_mem_range H (hy a trivial))` as an intermediate fact. Rewrite using `[mul_one] at this) hh` and apply the resulting hypothesis.

Introduce `v`. Rewrite using `[mem_conjLat, ← SetLike.mem_coe, hΛ, ← key, ← hΛ]`. Simplify using `only [sum_one]`. Prove the components needed by the constructor for the conclusion. Introduce `hv w hw`.

Use `hv _ hw` as an intermediate fact. Simplify using `only [IsCMField.complexConj_apply_apply] at this`. Conclude with `(FractionalIdeal.mem_one_iff _).1 this`. Introduce `hv y hy`. Use `(FractionalIdeal.mem_one_iff _).2 (hv (fun j => IsCMField.complexConj E (y j)) ?_)` and prove the remaining obligations.

Rewrite using `[mem_conjLat]`. Simplify using `only [IsCMField.complexConj_apply_apply]`. Conclude with `hy`.
-/
theorem conjLat_unimod (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) {Λ : Submodule (𝓞 E) (Fin n → E)}
    {h : GL (Fin n) (RA (maximalRealSubfield E) E)} (hh : IsUnA (IsCMField.complexConj E) 1 h.1)
    (hΛ : (Λ : Set (Fin n → E)) = latOf (maximalRealSubfield E) h.1 (stdLat E n)) : (conjLat H Λ).Unimod := by
  obtain ⟨⟨h1, -, h2, h3⟩, -, hfg, hsp, -⟩ := StdInhab.main E H n
  have key := latOf_selfDual (maximalRealSubfield E) E n (stdLat E n) (IsCMField.complexConj E) 1 1 h hfg hsp h1 h2 h3
    one_ne_zero (fun v => by
      simp only [sum_one]
      constructor
      · intro hv j _
        have := hv _ (StdInhab.single_mem n j)
        have e : ∑ a, v a * IsCMField.complexConj E ((Pi.single j (1 : E) : Fin n → E) a) = v j := by
          simp [Pi.single_apply, apply_ite]
        rw [e] at this
        exact Submodule.mem_one.2 ((FractionalIdeal.mem_one_iff _).1 this)
      · intro hv y hy
        refine (FractionalIdeal.mem_one_iff _).2 (Submodule.mem_one.1 ?_)
        refine Submodule.sum_mem _ fun a _ => ?_
        have := Submodule.mul_mem_mul (hv a trivial) (conj_mem_range H (hy a trivial))
        rwa [mul_one] at this) hh
  intro v
  rw [mem_conjLat, ← SetLike.mem_coe, hΛ, ← key, ← hΛ]
  simp only [sum_one]
  constructor
  · intro hv w hw
    have := hv _ hw
    simp only [IsCMField.complexConj_apply_apply] at this
    exact (FractionalIdeal.mem_one_iff _).1 this
  · intro hv y hy
    refine (FractionalIdeal.mem_one_iff _).2 (hv (fun j => IsCMField.complexConj E (y j)) ?_)
    rw [mem_conjLat]
    simp only [IsCMField.complexConj_apply_apply]
    exact hy

/- English proof (translation)
Take `⟨Q, hQ, hQv, hm⟩` from `hv`. Assume the negation of the conclusion as `hn`. Establish `key : ∀ a ∈ P, H.bar a ∈ P`. Introduce `a ha`. Assume the negation of the conclusion as `hb`.

Conclude with `hn ⟨a, ha, H.bar a, H.bar_eq a, hb⟩`. Establish `hle : Q ≤ P`. Introduce `a ha`. Establish `hfix : IsCMField.complexConj E ((a * H.bar a : 𝓞 E) : E) = ((a * H.bar a : 𝓞 E) : E)`. Rewrite using `[← H.bar_eq, map_mul, StdInhab.bar_bar, mul_comm]`.

Establish `hmem` using `(IsCMField.complexConj_eq_self_iff E _).1 hfix`. Establish `hint : IsIntegral ℤ (⟨_, hmem⟩ : maximalRealSubfield E)` using `(isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ (maximalRealSubfield E) E) (algebraMap (maximalRealSubfield E) E).injective).1 (a * H.bar a).2`. Take `⟨x, e⟩ : ∃ x : 𝓞 (maximalRealSubfield E), algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) x = a * H.bar a` from `⟨⟨_, hint⟩, rfl⟩`. Establish `h1 : x ∈ v.asIdeal`. Rewrite using `[← hQv, Ideal.mem_comap, e]`.

Conclude with `Q.mul_mem_right _ ha`. Rewrite `h1` using `[← hPv, Ideal.mem_comap, e]`. Break down `hP.mem_or_mem h1 with h | h` into its components or cases. Conclude with `h`. Rewrite using `[← StdInhab.bar_bar H a]`.

Conclude with `key _ h`. Establish `hQ0 : Q ≠ ⊥`. Introduce and unpack `rfl`. Apply `v.ne_bot` to reduce the goal to its premises. Rewrite using `[← hQv]`.

Conclude with `Ideal.comap_bot_of_injective _ (RingOfIntegers.algebraMap.injective _ _)`. Conclude with `hn ((hQ.isMaximal hQ0).eq_of_le hP.ne_top hle ▸ hm)`.
-/
theorem moved_of_splitPl (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)))
    (hv : SplitPl (IsCMField.complexConj E) v) (P : Ideal (𝓞 E)) (hP : P.IsPrime)
    (hPv : P.comap (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) = v.asIdeal) :
    Moved (IsCMField.complexConj E) P := by
  obtain ⟨Q, hQ, hQv, hm⟩ := hv
  by_contra hn
  have key : ∀ a ∈ P, H.bar a ∈ P := by
    intro a ha
    by_contra hb
    exact hn ⟨a, ha, H.bar a, H.bar_eq a, hb⟩
  have hle : Q ≤ P := by
    intro a ha
    have hfix : IsCMField.complexConj E ((a * H.bar a : 𝓞 E) : E) = ((a * H.bar a : 𝓞 E) : E) := by
      rw [← H.bar_eq, map_mul, StdInhab.bar_bar, mul_comm]
    have hmem := (IsCMField.complexConj_eq_self_iff E _).1 hfix
    have hint : IsIntegral ℤ (⟨_, hmem⟩ : maximalRealSubfield E) :=
      (isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ (maximalRealSubfield E) E)
        (algebraMap (maximalRealSubfield E) E).injective).1 (a * H.bar a).2
    obtain ⟨x, e⟩ : ∃ x : 𝓞 (maximalRealSubfield E),
        algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) x = a * H.bar a := ⟨⟨_, hint⟩, rfl⟩
    have h1 : x ∈ v.asIdeal := by
      rw [← hQv, Ideal.mem_comap, e]
      exact Q.mul_mem_right _ ha
    rw [← hPv, Ideal.mem_comap, e] at h1
    rcases hP.mem_or_mem h1 with h | h
    · exact h
    · rw [← StdInhab.bar_bar H a]; exact key _ h
  have hQ0 : Q ≠ ⊥ := by
    rintro rfl
    apply v.ne_bot
    rw [← hQv]
    exact Ideal.comap_bot_of_injective _ (RingOfIntegers.algebraMap.injective _ _)
  exact hn ((hQ.isMaximal hQ0).eq_of_le hP.ne_top hle ▸ hm)

/- English proof (translation)
Take `⟨-, -, hfg, hsp, -⟩` from `StdInhab.main E H n`. Take `⟨Λ, hΛ, -⟩` from `exists_lattice_latOf (maximalRealSubfield E) E n (stdLat E n) h hfg hsp`. Take `⟨e, -, -, he, hcut⟩` from `hs`. Establish `hcut'` using `cut_inv h _ hcut`. Establish `he' : ∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)), ((bad * l.M : ℕ) : 𝓞 (maximalRealSubfield E)) ∈ v.asIdeal → e v = 0` using `fun v hv => by`.

Assume the negation of the conclusion as `h0`. Conclude with `(he v h0).2 hv`. Take `⟨t, ht, hb⟩` from `exists_nat_bd _ hfg hsp _ e he' _ hcut`. Take `⟨t', ht', hb'⟩` from `exists_nat_bd _ hfg hsp _ e he' _ hcut'`. Take `⟨s, hs0, hs, hc⟩` from `exists_supp_bd _ hfg hsp e _ hcut`.

Take `⟨s', hs0', hs', hc'⟩` from `exists_supp_bd _ hfg hsp e _ hcut'`. Establish `hk : (t' * t).Coprime (bad * l.M)` using `Nat.Coprime.mul_left ht' ht`. Establish `hnat : ∀ u : ℕ, Ideal.span {((u * (t' * t) : ℕ) : 𝓞 E)} • (conjLat H Λ).La ≤ stdLat E n ∧ Ideal.span {((u * (t' * t) : ℕ) : 𝓞 E)} • stdLat E n ≤ (conjLat H Λ).La` using `fun u => by`. Use `conjLat_le H (by rw [← H.bar_eq, map_natCast]) (smul_mem_of_bd hfg hsp hΛ ?_ ?_)` and prove the remaining obligations. Use `hb.mul ((u * t' : ℕ) : 𝓞 E)` as an intermediate fact.

Rewrite `this` using `[← Nat.cast_mul, mul_assoc]`. Then use the resulting hypothesis. Use `hb'.mul ((u * t : ℕ) : 𝓞 E)` as an intermediate fact. Rewrite `this` using `[← Nat.cast_mul, mul_assoc, mul_comm t]`. Then use the resulting hypothesis. Establish `h1` using `hnat 1`. Rewrite `h1` using `[one_mul]`.

Use `⟨Λ, l.M * (t' * t), hΛ, conjLat_unimod H hh hΛ, ⟨_, hk.coprime_mul_right_right, h1⟩, ⟨_, hk.coprime_mul_left_right, h1⟩, ⟨l.odd.mul ?_, dvd_mul_right _ _, le_inf (hnat _).2 Submodule.smul_le_right⟩, algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) (s' * s), ?_, ?_⟩` and prove the remaining obligations. Conclude with `Nat.Coprime.odd_of_right (hk.coprime_mul_right_right.coprime_dvd_right h2)`. Conclude with `(map_ne_zero_iff _ (RingOfIntegers.algebraMap.injective _ _)).2 (mul_ne_zero hs0' hs0)`. Rewrite using `[← and_assoc]`. Use `⟨conjLat_le H ?_ (smul_mem_of_bd hfg hsp hΛ ?_ ?_), fun P hP hm => ?_⟩` and prove the remaining obligations.

Conclude with `(IsCMField.complexConj E).commutes ((s' * s : 𝓞 (maximalRealSubfield E)) : maximalRealSubfield E)`. Rewrite using `[map_mul]`. Conclude with `hc.mul _`. Rewrite using `[mul_comm, map_mul]`. Conclude with `hc'.mul _`.

Rewrite using `[← StdInhab.moved_iff]`. Set `v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))` to `⟨P.comap (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)), Ideal.comap_isPrime _ _, fun h0 => mul_ne_zero hs0' hs0 (by rw [← Ideal.mem_bot, ← h0]; exact hm)⟩`. Establish `hv : e v ≠ 0` using `(v.isPrime.mem_or_mem (show s' * s ∈ v.asIdeal from hm)).elim (hs' v) (hs v)`. Conclude with `moved_of_splitPl H v (he v hv).1 P hP rfl`.
-/
theorem exists_lat (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (bad : ℕ) (h2 : 2 ∣ bad)
    (h : GL (Fin n) (RA (maximalRealSubfield E) E)) (hh : IsUnA (IsCMField.complexConj E) 1 h.1)
    (hs : SuppSplit (IsCMField.complexConj E) (bad * l.M) h.1) :
    ∃ (Λ : Submodule (𝓞 E) (Fin n → E)) (N : ℕ),
      (Λ : Set (Fin n → E)) = latOf (maximalRealSubfield E) h.1 (stdLat E n) ∧ (conjLat H Λ).Unimod ∧
      (conjLat H Λ).TrivAt bad ∧ (conjLat H Λ).TrivAt l.M ∧ (conjLat H Λ).LevOK N l.M ∧
      GenLat.SplitSupp H (conjLat H Λ) := by
  obtain ⟨-, -, hfg, hsp, -⟩ := StdInhab.main E H n
  obtain ⟨Λ, hΛ, -⟩ := exists_lattice_latOf (maximalRealSubfield E) E n (stdLat E n) h hfg hsp
  obtain ⟨e, -, -, he, hcut⟩ := hs
  have hcut' := cut_inv h _ hcut
  have he' : ∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)),
      ((bad * l.M : ℕ) : 𝓞 (maximalRealSubfield E)) ∈ v.asIdeal → e v = 0 := fun v hv => by
    by_contra h0
    exact (he v h0).2 hv
  obtain ⟨t, ht, hb⟩ := exists_nat_bd _ hfg hsp _ e he' _ hcut
  obtain ⟨t', ht', hb'⟩ := exists_nat_bd _ hfg hsp _ e he' _ hcut'
  obtain ⟨s, hs0, hs, hc⟩ := exists_supp_bd _ hfg hsp e _ hcut
  obtain ⟨s', hs0', hs', hc'⟩ := exists_supp_bd _ hfg hsp e _ hcut'
  have hk : (t' * t).Coprime (bad * l.M) := Nat.Coprime.mul_left ht' ht
  have hnat : ∀ u : ℕ, Ideal.span {((u * (t' * t) : ℕ) : 𝓞 E)} • (conjLat H Λ).La ≤ stdLat E n ∧
      Ideal.span {((u * (t' * t) : ℕ) : 𝓞 E)} • stdLat E n ≤ (conjLat H Λ).La := fun u => by
    refine conjLat_le H (by rw [← H.bar_eq, map_natCast]) (smul_mem_of_bd hfg hsp hΛ ?_ ?_)
    · have := hb.mul ((u * t' : ℕ) : 𝓞 E)
      rwa [← Nat.cast_mul, mul_assoc] at this
    · have := hb'.mul ((u * t : ℕ) : 𝓞 E)
      rwa [← Nat.cast_mul, mul_assoc, mul_comm t] at this
  have h1 := hnat 1
  rw [one_mul] at h1
  refine ⟨Λ, l.M * (t' * t), hΛ, conjLat_unimod H hh hΛ, ⟨_, hk.coprime_mul_right_right, h1⟩,
    ⟨_, hk.coprime_mul_left_right, h1⟩, ⟨l.odd.mul ?_, dvd_mul_right _ _, le_inf (hnat _).2 Submodule.smul_le_right⟩,
    algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) (s' * s), ?_, ?_⟩
  · exact Nat.Coprime.odd_of_right (hk.coprime_mul_right_right.coprime_dvd_right h2)
  · exact (map_ne_zero_iff _ (RingOfIntegers.algebraMap.injective _ _)).2 (mul_ne_zero hs0' hs0)
  · rw [← and_assoc]
    refine ⟨conjLat_le H ?_ (smul_mem_of_bd hfg hsp hΛ ?_ ?_), fun P hP hm => ?_⟩
    · exact (IsCMField.complexConj E).commutes ((s' * s : 𝓞 (maximalRealSubfield E)) : maximalRealSubfield E)
    · rw [map_mul]; exact hc.mul _
    · rw [mul_comm, map_mul]; exact hc'.mul _
    · rw [← StdInhab.moved_iff]
      let v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)) :=
        ⟨P.comap (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)), Ideal.comap_isPrime _ _, fun h0 =>
          mul_ne_zero hs0' hs0 (by rw [← Ideal.mem_bot, ← h0]; exact hm)⟩
      have hv : e v ≠ 0 := (v.isPrime.mem_or_mem (show s' * s ∈ v.asIdeal from hm)).elim (hs' v) (hs v)
      exact moved_of_splitPl H v (he v hv).1 P hP rfl

end CM

end GlobalTheory.UnRep.FullReps
