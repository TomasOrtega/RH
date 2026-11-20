import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsBaseClassLevelAdapted
import Formalism.LocalToGlobal.ProjectiveLattices.CuspFree
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.AnChartAsm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.CmHostUnitAddConjEqOne
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HalvesFreeAndAdjoint
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.GeneralLinearGroupCharEqOneOfDetEqOne
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelStructureProperties

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.LevelTied

open GlobalTheory.SW.Lev GlobalTheory.HalfPairing

section Alg

variable {R Q : Type} [CommRing R] [AddCommGroup Q] [Module R Q] {I : Ideal R} {r : ℕ}

/- English proof (translation)
Simplify using `only [← map_smul, ← map_sum]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Simplify using `[Finset.sum_apply, Pi.single_apply, Algebra.smul_def]`.
-/
theorem equiv_col (e : (Fin r → R ⧸ I) ≃ₗ[R] Q) (c : Fin r → R) :
    e (fun j => Ideal.Quotient.mk I (c j)) = ∑ j, c j • e (Pi.single j 1) := by
  simp only [← map_smul, ← map_sum]
  congr 1
  funext i
  simp [Finset.sum_apply, Pi.single_apply, Algebra.smul_def]

noncomputable def rho (e : (Fin r → R ⧸ I) ≃ₗ[R] Q) : GL (Fin r) (R ⧸ I) →* (Q ≃ₗ[R] Q) :=
  MonoidHom.mk' (fun k => e.symm ≪≫ₗ
    ((Matrix.GeneralLinearGroup.toLin k).toLinearEquiv.restrictScalars R) ≪≫ₗ e) (fun k k' => by
      ext q
      simp)

/- English proof (translation)
Rewrite using `[← equiv_col]`. Express the relevant statement in the definitionally equal form `e ((k : Matrix (Fin r) (Fin r) (R ⧸ I)) *ᵥ (e.symm (e (Pi.single i 1)))) = _`. Rewrite using `[e.symm_apply_apply, ← ha]`. Use `congr 1`. Use function extensionality and compare the values at `j`.

Simplify using the standard rewrite rules.
-/
theorem rho_apply (e : (Fin r → R ⧸ I) ≃ₗ[R] Q) (k : GL (Fin r) (R ⧸ I)) (a : Matrix (Fin r) (Fin r) R)
    (ha : a.map (Ideal.Quotient.mk I) = k) (i : Fin r) :
    rho e k (e (Pi.single i 1)) = ∑ j, a j i • e (Pi.single j 1) := by
  rw [← equiv_col]
  change e ((k : Matrix (Fin r) (Fin r) (R ⧸ I)) *ᵥ (e.symm (e (Pi.single i 1)))) = _
  rw [e.symm_apply_apply, ← ha]
  congr 1
  funext j
  simp

/- English proof (translation)
Rewrite using `[cop_iff]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, m, hm, h⟩`. Use `IsUnit.of_mul_eq_one_right (Ideal.Quotient.mk I a) ?_` and prove the remaining obligations. Rewrite using `[← map_mul, ← map_one (Ideal.Quotient.mk I), Ideal.Quotient.eq, ← h]`.

Simplify using `using hm`. Introduce `h`. Take `⟨b, hb⟩` from `h.exists_left_inv`. Take `⟨a, rfl⟩` from `Ideal.Quotient.mk_surjective b`. Rewrite `hb` using `[← map_mul, ← map_one (Ideal.Quotient.mk I), eq_comm, Ideal.Quotient.eq]`.

Conclude with `⟨a, _, hb, by ring⟩`.
-/
theorem cop_iff_isUnit {s : R} : IsCoprime (Ideal.span {s}) I ↔ IsUnit (Ideal.Quotient.mk I s) := by
  rw [cop_iff]
  constructor
  · rintro ⟨a, m, hm, h⟩
    refine IsUnit.of_mul_eq_one_right (Ideal.Quotient.mk I a) ?_
    rw [← map_mul, ← map_one (Ideal.Quotient.mk I), Ideal.Quotient.eq, ← h]
    simpa using hm
  · intro h
    obtain ⟨b, hb⟩ := h.exists_left_inv
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
    rw [← map_mul, ← map_one (Ideal.Quotient.mk I), eq_comm, Ideal.Quotient.eq] at hb
    exact ⟨a, _, hb, by ring⟩

/- English proof (translation)
Take `⟨ez, hez⟩` from `exists_equiv_of_span I r e z hz`. Take `⟨ex, hex⟩` from `exists_equiv_of_span I r e x hx`. Use `choose a ha using fun j i => Ideal.Quotient.mk_surjective (ez.symm (x i) j)`. Use `choose b hb using fun j i => Ideal.Quotient.mk_surjective (ex.symm (z i) j)`. Establish `h1 : ∀ i, x i = ∑ j, a j i • z j` using `fun i => by`.

Simplify using `only [← hez, ← equiv_col, ha]`. Conclude with `(ez.apply_symm_apply _).symm`. Establish `h2 : ∀ i, z i = ∑ j, b j i • x j` using `fun i => by`. Simplify using `only [← hex, ← equiv_col, hb]`. Conclude with `(ex.apply_symm_apply _).symm`.

Use `⟨Matrix.of a, cop_iff_isUnit.2 ?_, h1⟩` and prove the remaining obligations. Establish `h3 : (Ideal.Quotient.mk I).mapMatrix (Matrix.of a * Matrix.of b) = 1`. Use extensionality with `j i`. Establish `: ez (fun j => Ideal.Quotient.mk I ((Matrix.of a * Matrix.of b) j i)) = ez (Pi.single i 1)`. Rewrite using `[equiv_col]`.

Simplify using `only [hez]`. Rewrite using `[h2 i]`. Simplify using `only [h1, Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, smul_smul, mul_comm, Matrix.of_apply]`. Conclude with `Finset.sum_comm`. Use `congrFun (ez.injective this) j` as an intermediate fact.

Simplify `this` using `[Pi.single_apply, Matrix.one_apply]`. Establish `h4` using `congrArg Matrix.det h3`. Rewrite `h4` using `[← RingHom.map_det, Matrix.det_mul, map_mul, Matrix.det_one]`. Conclude with `IsUnit.of_mul_eq_one _ h4`.
-/
theorem exists_matrix (e : Q ≃ₗ[R] (Fin r → R ⧸ I)) (z x : Fin r → Q)
    (hz : Submodule.span R (Set.range z) = ⊤) (hx : Submodule.span R (Set.range x) = ⊤) :
    ∃ a : Matrix (Fin r) (Fin r) R, IsCoprime (Ideal.span {a.det}) I ∧ ∀ i, x i = ∑ j, a j i • z j := by
  obtain ⟨ez, hez⟩ := exists_equiv_of_span I r e z hz
  obtain ⟨ex, hex⟩ := exists_equiv_of_span I r e x hx
  choose a ha using fun j i => Ideal.Quotient.mk_surjective (ez.symm (x i) j)
  choose b hb using fun j i => Ideal.Quotient.mk_surjective (ex.symm (z i) j)
  have h1 : ∀ i, x i = ∑ j, a j i • z j := fun i => by
    simp only [← hez, ← equiv_col, ha]
    exact (ez.apply_symm_apply _).symm
  have h2 : ∀ i, z i = ∑ j, b j i • x j := fun i => by
    simp only [← hex, ← equiv_col, hb]
    exact (ex.apply_symm_apply _).symm
  refine ⟨Matrix.of a, cop_iff_isUnit.2 ?_, h1⟩
  have h3 : (Ideal.Quotient.mk I).mapMatrix (Matrix.of a * Matrix.of b) = 1 := by
    ext j i
    have : ez (fun j => Ideal.Quotient.mk I ((Matrix.of a * Matrix.of b) j i)) = ez (Pi.single i 1) := by
      rw [equiv_col]
      simp only [hez]
      rw [h2 i]
      simp only [h1, Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, smul_smul, mul_comm, Matrix.of_apply]
      exact Finset.sum_comm
    have := congrFun (ez.injective this) j
    simpa [Pi.single_apply, Matrix.one_apply] using this
  have h4 := congrArg Matrix.det h3
  rw [← RingHom.map_det, Matrix.det_mul, map_mul, Matrix.det_one] at h4
  exact IsUnit.of_mul_eq_one _ h4

/- English proof (translation)
Use `haveI : Nontrivial (S ⧸ 𝔪) := Ideal.Quotient.nontrivial_iff.2 h.ne_top`. Use `haveI : Finite (S ⧸ 𝔪) := Finite.of_surjective _ Ideal.Quotient.mk_surjective`. Use `haveI : Fintype (S ⧸ 𝔪) := Fintype.ofFinite _`. Establish `h1 : 1 < Nat.card (S ⧸ 𝔪)` using `Finite.one_lt_card`. Establish `h0 : ((Nat.card (S ⧸ 𝔪) : ℕ) : S ⧸ 𝔪) = 0`.

Rewrite using `[Nat.card_eq_fintype_card]`. Conclude with `Nat.cast_card_eq_zero _`. Establish `hN' : (N : S ⧸ 𝔪) = 0` using `by rw [← map_natCast (Ideal.Quotient.mk 𝔪), hN, map_zero]`. Assume the negation of the conclusion as `hlt`. Establish `hc : Nat.Coprime (Nat.card (S ⧸ 𝔪)) N`.

Establish `: Nat.card (S ⧸ 𝔪) = 2 ∨ Nat.card (S ⧸ 𝔪) = 3` using `by omega`. Apply the tactic sequence `rcases this with h | h <;> rw [h]`. Conclude with `Nat.coprime_two_left.2 h2`. Conclude with `(Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3`. Use `hc.cast (R := S ⧸ 𝔪)` as an intermediate fact.

Rewrite `this` using `[h0, hN']`. Conclude with `not_isCoprime_zero_zero this`.
-/
theorem four_le_card {S : Type} [CommRing S] [Finite S] (N : ℕ) (h2 : Odd N) (h3 : ¬ 3 ∣ N) (hN : (N : S) = 0)
    (𝔪 : Ideal S) (h : 𝔪.IsMaximal) : 4 ≤ Nat.card (S ⧸ 𝔪) := by
  haveI : Nontrivial (S ⧸ 𝔪) := Ideal.Quotient.nontrivial_iff.2 h.ne_top
  haveI : Finite (S ⧸ 𝔪) := Finite.of_surjective _ Ideal.Quotient.mk_surjective
  haveI : Fintype (S ⧸ 𝔪) := Fintype.ofFinite _
  have h1 : 1 < Nat.card (S ⧸ 𝔪) := Finite.one_lt_card
  have h0 : ((Nat.card (S ⧸ 𝔪) : ℕ) : S ⧸ 𝔪) = 0 := by
    rw [Nat.card_eq_fintype_card]; exact Nat.cast_card_eq_zero _
  have hN' : (N : S ⧸ 𝔪) = 0 := by rw [← map_natCast (Ideal.Quotient.mk 𝔪), hN, map_zero]
  by_contra hlt
  have hc : Nat.Coprime (Nat.card (S ⧸ 𝔪)) N := by
    have : Nat.card (S ⧸ 𝔪) = 2 ∨ Nat.card (S ⧸ 𝔪) = 3 := by omega
    rcases this with h | h <;> rw [h]
    · exact Nat.coprime_two_left.2 h2
    · exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3
  have := hc.cast (R := S ⧸ 𝔪)
  rw [h0, hN'] at this
  exact not_isCoprime_zero_zero this

end Alg

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r}

/- English proof (translation)
Use `haveI : Finite (𝓞 E ⧸ I) := Ideal.finiteQuotientOfFreeOfNeBot _ hI`. Use `haveI : Module.Finite (𝓞 E) X.Λ := Module.Finite.iff_fg.2 X.Λ_fg`. Use `haveI : Module.FinitePresentation (𝓞 E) X.Λ := Module.finitePresentation_of_finite _ _`. Use `haveI : Module.Projective (𝓞 E) X.Λ := Module.Flat.projective_of_finitePresentation`. Use `nonempty_equiv_quot I r ?_` and prove the remaining obligations.

Establish `h` using `(X.Λ.tensorEquivSpan E).finrank_eq`. Rewrite `h` using `[IsLocalization.finrank_eq E (nonZeroDivisors (𝓞 E)) le_rfl, IsLocalizedModule.finrank_eq (nonZeroDivisors (𝓞 E)) (TensorProduct.mk (𝓞 E) E X.Λ 1) le_rfl, X.Λ_span]`. Simplify using `using h`.
-/
theorem nonempty_equiv_lat (X : Data E r) (I : Ideal (𝓞 E)) (hI : I ≠ ⊥) :
    Nonempty ((X.Λ ⧸ (I • ⊤ : Submodule (𝓞 E) X.Λ)) ≃ₗ[𝓞 E] (Fin r → 𝓞 E ⧸ I)) := by
  haveI : Finite (𝓞 E ⧸ I) := Ideal.finiteQuotientOfFreeOfNeBot _ hI
  haveI : Module.Finite (𝓞 E) X.Λ := Module.Finite.iff_fg.2 X.Λ_fg
  haveI : Module.FinitePresentation (𝓞 E) X.Λ := Module.finitePresentation_of_finite _ _
  haveI : Module.Projective (𝓞 E) X.Λ := Module.Flat.projective_of_finitePresentation
  refine nonempty_equiv_quot I r ?_
  have h := (X.Λ.tensorEquivSpan E).finrank_eq
  rw [IsLocalization.finrank_eq E (nonZeroDivisors (𝓞 E)) le_rfl,
    IsLocalizedModule.finrank_eq (nonZeroDivisors (𝓞 E)) (TensorProduct.mk (𝓞 E) E X.Λ 1) le_rfl, X.Λ_span] at h
  simpa using h

/- English proof (translation)
The claim follows from `Submodule.mem_smul_top_iff I L v`.
-/
theorem mem_smul_top {L : Lt E r} {I : Ideal (𝓞 E)} {v : L} :
    v ∈ (I • ⊤ : Submodule (𝓞 E) L) ↔ (v : Fin r → E) ∈ I • L := Submodule.mem_smul_top_iff I L v

/- English proof (translation)
Take `⟨e⟩` from `nonempty_equiv_lat X I hI`. Take `⟨x, hx⟩` from `exists_span I r e`. Use `choose b hb using fun i => Submodule.Quotient.mk_surjective _ (x i)`. Use `⟨fun i => b i, fun i => (b i).2, fun v hv => ?_⟩` and prove the remaining obligations. Take `⟨c, hc⟩` from `(Submodule.mem_span_range_iff_exists_fun (𝓞 E)).1 (hx ▸ Submodule.mem_top : Submodule.Quotient.mk (⟨v, hv⟩ : X.Λ) ∈ Submodule.span (𝓞 E) (Set.range x))`.

Establish `: Submodule.Quotient.mk (⟨v, hv⟩ : X.Λ) = (Submodule.Quotient.mk (∑ i, c i • b i) : X.Λ ⧸ (I • ⊤ : Submodule (𝓞 E) X.Λ))`. Rewrite using `[← hc]`. Simplify using `only [← hb, ← Submodule.mkQ_apply, map_sum, map_smul]`. Establish `h2` using `mem_smul_top.1 ((Submodule.Quotient.eq _).1 this)`. Establish `h3 : v = ∑ i, c i • (b i : Fin r → E) + ((⟨v, hv⟩ - ∑ i, c i • b i : X.Λ) : Fin r → E)` using `by simp`.

Rewrite using `[h3]`. Conclude with `Submodule.add_mem_sup (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)) h2`.
-/
theorem exists_frame (X : Data E r) (I : Ideal (𝓞 E)) (hI : I ≠ ⊥) : ∃ β : Fin r → Fin r → E,
    (∀ i, β i ∈ X.Λ) ∧ X.Λ ≤ Submodule.span (𝓞 E) (Set.range β) ⊔ I • X.Λ := by
  obtain ⟨e⟩ := nonempty_equiv_lat X I hI
  obtain ⟨x, hx⟩ := exists_span I r e
  choose b hb using fun i => Submodule.Quotient.mk_surjective _ (x i)
  refine ⟨fun i => b i, fun i => (b i).2, fun v hv => ?_⟩
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 E)).1
    (hx ▸ Submodule.mem_top : Submodule.Quotient.mk (⟨v, hv⟩ : X.Λ) ∈ Submodule.span (𝓞 E) (Set.range x))
  have : Submodule.Quotient.mk (⟨v, hv⟩ : X.Λ) = (Submodule.Quotient.mk (∑ i, c i • b i) :
      X.Λ ⧸ (I • ⊤ : Submodule (𝓞 E) X.Λ)) := by
    rw [← hc]
    simp only [← hb, ← Submodule.mkQ_apply, map_sum, map_smul]
  have h2 := mem_smul_top.1 ((Submodule.Quotient.eq _).1 this)
  have h3 : v = ∑ i, c i • (b i : Fin r → E) + ((⟨v, hv⟩ - ∑ i, c i • b i : X.Λ) : Fin r → E) := by simp
  rw [h3]
  exact Submodule.add_mem_sup (Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)) h2

/- English proof (translation)
Take `⟨s, hs, H⟩` from `H`. Take `⟨a, m, hm, e⟩` from `cop_iff.1 hs`. Conclude with `⟨s, cop_iff.2 ⟨a, m, h hm, e⟩, Submodule.smul_mono_left h H⟩`.
-/
theorem cong_mono {𝔞 𝔟 : Ideal (𝓞 E)} (h : 𝔞 ≤ 𝔟) {u v : Fin r → E} (H : Cong X 𝔞 u v) : Cong X 𝔟 u v := by
  obtain ⟨s, hs, H⟩ := H
  obtain ⟨a, m, hm, e⟩ := cop_iff.1 hs
  exact ⟨s, cop_iff.2 ⟨a, m, h hm, e⟩, Submodule.smul_mono_left h H⟩

/- English proof (translation)
Take `⟨s, hs, H⟩` from `H`. Take `⟨t, ht, H'⟩` from `H'`. Take `⟨m, hm, m', hm', e⟩` from `Ideal.isCoprime_iff_exists.1 h`. Take `⟨a, x, hx, e1⟩` from `cop_iff.1 hs`. Take `⟨b, y, hy, e2⟩` from `cop_iff.1 ht`.

Use `⟨m' * s + m * t, IsCoprime.mul_right (cop_iff.2 ⟨a, x + a * m * (s - t), ?_, ?_⟩) (cop_iff.2 ⟨b, y + b * m' * (t - s), ?_, ?_⟩), ?_⟩` and prove the remaining obligations. Conclude with `add_mem hx (Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ hm))`. Take the linear combination `e1 + a * s * e`. Conclude with `add_mem hy (Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ hm'))`. Take the linear combination `e2 + b * t * e`.

Rewrite using `[add_smul, mul_smul m', mul_smul m]`. Use `add_mem ?_ ?_` and prove the remaining obligations. Rewrite using `[mul_comm, Submodule.mul_smul]`. Conclude with `Submodule.smul_mem_smul hm' H`. Rewrite using `[Submodule.mul_smul]`.

Conclude with `Submodule.smul_mem_smul hm H'`.
-/
theorem cong_glue {𝔞 𝔟 : Ideal (𝓞 E)} (h : IsCoprime 𝔞 𝔟) {u v : Fin r → E} (H : Cong X 𝔞 u v)
    (H' : Cong X 𝔟 u v) : Cong X (𝔞 * 𝔟) u v := by
  obtain ⟨s, hs, H⟩ := H
  obtain ⟨t, ht, H'⟩ := H'
  obtain ⟨m, hm, m', hm', e⟩ := Ideal.isCoprime_iff_exists.1 h
  obtain ⟨a, x, hx, e1⟩ := cop_iff.1 hs
  obtain ⟨b, y, hy, e2⟩ := cop_iff.1 ht
  refine ⟨m' * s + m * t, IsCoprime.mul_right (cop_iff.2 ⟨a, x + a * m * (s - t), ?_, ?_⟩)
    (cop_iff.2 ⟨b, y + b * m' * (t - s), ?_, ?_⟩), ?_⟩
  · exact add_mem hx (Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ hm))
  · linear_combination e1 + a * s * e
  · exact add_mem hy (Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ hm'))
  · linear_combination e2 + b * t * e
  · rw [add_smul, mul_smul m', mul_smul m]
    refine add_mem ?_ ?_
    · rw [mul_comm, Submodule.mul_smul]; exact Submodule.smul_mem_smul hm' H
    · rw [Submodule.mul_smul]; exact Submodule.smul_mem_smul hm H'

/- English proof (translation)
Rewrite using `[cong_iff, ← Finset.sum_sub_distrib]`. Conclude with `le_loc _ (Submodule.sum_mem _ fun j _ => sub_smul (c j) (d j) (β j) ▸ Submodule.smul_mem_smul (h j) (hβ j))`.
-/
theorem cong_coeff' {𝔞 : Ideal (𝓞 E)} {β : Fin r → Fin r → E} (hβ : ∀ i, β i ∈ X.Λ) {c d : Fin r → 𝓞 E}
    (h : ∀ j, c j - d j ∈ 𝔞) : Cong X 𝔞 (∑ j, c j • β j) (∑ j, d j • β j) := by
  rw [cong_iff, ← Finset.sum_sub_distrib]
  exact le_loc _ (Submodule.sum_mem _ fun j _ =>
    sub_smul (c j) (d j) (β j) ▸ Submodule.smul_mem_smul (h j) (hβ j))

variable {La : Type} [AddCommGroup La] [Module (𝓞 E) La]

/- English proof (translation)
Take `⟨e'⟩` from `nonempty_equiv_lat X J hJ`. Set `f : La →ₗ[𝓞 E] X.Λ` to `LinearMap.codRestrict X.Λ (s • δ) fun a => h1 _ (hδ a)`. Set `g` to `Submodule.mapQ (J • ⊤ : Submodule (𝓞 E) La) (J • ⊤ : Submodule (𝓞 E) X.Λ) f (Submodule.smul_le.2 fun m hm x _ => by`. Rewrite using `[Submodule.mem_comap, map_smul]`. Conclude with `Submodule.smul_mem_smul hm trivial)`.

Establish `hsurj : Function.Surjective g`. Introduce `q`. Take `⟨⟨v, hv⟩, rfl⟩` from `Submodule.Quotient.mk_surjective _ q`. Take `⟨c, m, hm, ec⟩` from `cop_iff.1 (cop_mul hs hs)`. Take `⟨_, ⟨a, rfl⟩, w, hw, hvw⟩` from `Submodule.mem_sup.1 (hL (h2 v hv))`.

Use `⟨Submodule.Quotient.mk (c • a), (Submodule.Quotient.eq _).2 (mem_smul_top.2 ?_)⟩` and prove the remaining obligations. Establish `hw' : s • w ∈ J • X.Λ` using `smul_map_mem LinearMap.id h1 hw`. Establish `: s • δ (c • a) - v = -(c • s • w) - m • v`. Rewrite using `[map_smul, eq_sub_of_add_eq hvw]`. Establish `: v = (c * (s * s) + m) • v` using `by rw [ec, one_smul]`.

Take the linear combination `(norm := module) -this`. Express the relevant statement in the definitionally equal form `s • δ (c • a) - v ∈ _`. Rewrite using `[this]`. Conclude with `sub_mem (neg_mem (Submodule.smul_mem _ _ hw')) (Submodule.smul_mem_smul hm hv)`. Establish `hinj : Function.Injective (e'.toLinearMap ∘ₗ g ∘ₗ e.symm.toLinearMap)` using `OrzechProperty.injective_of_surjective_endomorphism _ (e'.surjective.comp (hsurj.comp e.symm.surjective))`.

Establish `hg : Function.Injective g` using `fun x y hxy => e.injective (hinj (by simp [hxy]))`. Take `⟨t, ht, h⟩` from `h`. Rewrite using `[Submodule.Quotient.eq]`. Use `mem_of_loc (L := ⊤) trivial le_rfl ⟨t, ht, ?_⟩` and prove the remaining obligations. Rewrite using `[← Submodule.Quotient.mk_eq_zero]`.

Apply `hg` to reduce the goal to its premises. Rewrite using `[map_zero]`. Use `(Submodule.Quotient.mk_eq_zero _).2 (mem_smul_top.2 ?_)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `s • δ (t • (a - b)) ∈ _`. Rewrite using `[map_smul, map_sub]`.

Conclude with `Submodule.smul_mem _ _ h`.
-/
theorem mem_of_cong {J : Ideal (𝓞 E)} (hJ : J ≠ ⊥)
    (e : (La ⧸ (J • ⊤ : Submodule (𝓞 E) La)) ≃ₗ[𝓞 E] (Fin r → 𝓞 E ⧸ J)) {L : Lt E r} {s : 𝓞 E}
    (hs : IsCoprime (Ideal.span {s}) J) (h1 : ∀ v ∈ L, s • v ∈ X.Λ) (h2 : ∀ v ∈ X.Λ, s • v ∈ L)
    (δ : La →ₗ[𝓞 E] (Fin r → E)) (hδ : ∀ a, δ a ∈ L) (hL : L ≤ LinearMap.range δ ⊔ J • L) {a b : La}
    (h : Cong X J (δ a) (δ b)) :
    (Submodule.Quotient.mk a : La ⧸ (J • ⊤ : Submodule (𝓞 E) La)) = Submodule.Quotient.mk b := by
  obtain ⟨e'⟩ := nonempty_equiv_lat X J hJ
  let f : La →ₗ[𝓞 E] X.Λ := LinearMap.codRestrict X.Λ (s • δ) fun a => h1 _ (hδ a)
  let g := Submodule.mapQ (J • ⊤ : Submodule (𝓞 E) La) (J • ⊤ : Submodule (𝓞 E) X.Λ) f
    (Submodule.smul_le.2 fun m hm x _ => by
      rw [Submodule.mem_comap, map_smul]; exact Submodule.smul_mem_smul hm trivial)
  have hsurj : Function.Surjective g := by
    intro q
    obtain ⟨⟨v, hv⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    obtain ⟨c, m, hm, ec⟩ := cop_iff.1 (cop_mul hs hs)
    obtain ⟨_, ⟨a, rfl⟩, w, hw, hvw⟩ := Submodule.mem_sup.1 (hL (h2 v hv))
    refine ⟨Submodule.Quotient.mk (c • a), (Submodule.Quotient.eq _).2 (mem_smul_top.2 ?_)⟩
    have hw' : s • w ∈ J • X.Λ := smul_map_mem LinearMap.id h1 hw
    have : s • δ (c • a) - v = -(c • s • w) - m • v := by
      rw [map_smul, eq_sub_of_add_eq hvw]
      have : v = (c * (s * s) + m) • v := by rw [ec, one_smul]
      linear_combination (norm := module) -this
    change s • δ (c • a) - v ∈ _
    rw [this]
    exact sub_mem (neg_mem (Submodule.smul_mem _ _ hw')) (Submodule.smul_mem_smul hm hv)
  have hinj : Function.Injective (e'.toLinearMap ∘ₗ g ∘ₗ e.symm.toLinearMap) :=
    OrzechProperty.injective_of_surjective_endomorphism _ (e'.surjective.comp (hsurj.comp e.symm.surjective))
  have hg : Function.Injective g := fun x y hxy => e.injective (hinj (by simp [hxy]))
  obtain ⟨t, ht, h⟩ := h
  rw [Submodule.Quotient.eq]
  refine mem_of_loc (L := ⊤) trivial le_rfl ⟨t, ht, ?_⟩
  rw [← Submodule.Quotient.mk_eq_zero]
  apply hg
  rw [map_zero]
  refine (Submodule.Quotient.mk_eq_zero _).2 (mem_smul_top.2 ?_)
  change s • δ (t • (a - b)) ∈ _
  rw [map_smul, map_sub]
  exact Submodule.smul_mem _ _ h

/- English proof (translation)
Simplify using `only [← Submodule.mkQ_apply, map_sum, map_smul]`.
-/
theorem mk_comb {K : Submodule (𝓞 E) La} (c : Fin r → 𝓞 E) (z : Fin r → La) :
    (Submodule.Quotient.mk (∑ j, c j • z j) : La ⧸ K) = ∑ j, c j • Submodule.Quotient.mk (z j) := by
  simp only [← Submodule.mkQ_apply, map_sum, map_smul]

/- English proof (translation)
Establish `hle : D.𝔪 ≤ J` using `hprod ▸ Ideal.mul_le_right`. Establish `hJ : J ≠ ⊥` using `fun h => D.ne_bot (le_bot_iff.1 (h ▸ hle))`. Take `⟨-, s, hs, h1, h2⟩` from `hLl`. Establish `hs' : IsCoprime (Ideal.span {s}) J` using `(hprod ▸ hs.of_mul_right_left).of_mul_right_right`. Establish `inj` using `fun a b => mem_of_cong (a := a) (b := b) hJ e hs' h1 h2 δ hδ hL`.

Take `⟨c, m, hm, ec⟩` from `cop_iff.1 hs'`. Establish `hz : ∀ i, ∃ z, Cong X J (δ z) (D.β i)` using `fun i => by`. Take `⟨_, ⟨a, rfl⟩, w, hw, hvw⟩` from `Submodule.mem_sup.1 (hL (h2 _ (D.β_mem i)))`. Use `⟨c • a, s, hs', ?_⟩` and prove the remaining obligations. Establish `hw' : s • w ∈ J • X.Λ` using `smul_map_mem LinearMap.id h1 hw`.

Establish `: s • (δ (c • a) - D.β i) = -(c • s • w) - s • m • D.β i`. Rewrite using `[map_smul, eq_sub_of_add_eq hvw]`. Establish `: s • D.β i = s • (c * s + m) • D.β i` using `by rw [ec, one_smul]`. Take the linear combination `(norm := module) -this`. Rewrite using `[this]`.

Conclude with `sub_mem (neg_mem (Submodule.smul_mem _ _ hw')) (Submodule.smul_mem _ _ (Submodule.smul_mem_smul hm (D.β_mem i)))`. Use `choose z hz using hz`. Establish `hcomb : ∀ a : Fin r → 𝓞 E, Cong X J (δ (∑ j, a j • z j)) (∑ j, a j • D.β j)` using `fun a => by`. Simplify `cong_sum hz a` using `only [map_sum, map_smul]`. Establish `hsp : Submodule.span (𝓞 E) (Set.range fun i => (Submodule.Quotient.mk (z i) : La ⧸ (J • ⊤ : Submodule (𝓞 E) La))) = ⊤`.

Use `eq_top_iff.2 fun q _ => ?_` and prove the remaining obligations. Take `⟨a, rfl⟩` from `Submodule.Quotient.mk_surjective _ q`. Take `⟨u, hu, w, hw, huw⟩` from `Submodule.mem_sup.1 (D.β_span (X.Λ.smul_mem c (h1 _ (hδ a))))`. Take `⟨b, rfl⟩` from `(Submodule.mem_span_range_iff_exists_fun (𝓞 E)).1 hu`. Establish `h3 : Cong X J (δ a) (∑ j, b j • D.β j)`.

Use `⟨s, hs', ?_⟩` and prove the remaining obligations. Establish `: s • (δ a - ∑ j, b j • D.β j) = m • s • δ a + s • w`. Rewrite using `[eq_sub_of_add_eq huw]`. Establish `: s • δ a = s • (c * s + m) • δ a` using `by rw [ec, one_smul]`. Take the linear combination `(norm := module) this`.

Rewrite using `[this]`. Conclude with `add_mem (Submodule.smul_mem_smul hm (h1 _ (hδ a))) (Submodule.smul_mem _ _ (Submodule.smul_mono_left hle hw))`. Rewrite using `[inj _ _ (cong_trans h3 (cong_symm (hcomb b))), mk_comb]`. Conclude with `Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)`. Use `⟨_, hf1 _ hsp, fun xs y hy hy' => ?_⟩` and prove the remaining obligations.

Unfold `datF`. Use `split_ifs with h`. Take `⟨a, ha, hr⟩` from `h.1.choose_spec`. Rewrite using `[← hf2 _ hsp _ a ha]`. Use `congr 1`.

Use function extensionality and compare the values at `i`. Rewrite using `[← mk_comb]`. Conclude with `inj _ _ (cong_trans (cong_symm (hy i).1) (cong_trans (cong_mono hle (hr i)) (cong_symm (hcomb _))))`. Rewrite using `[mul_zero]`. Assume the negation of the conclusion as `h0`.

Take `⟨a, hdet, ha⟩` from `exists_matrix e _ _ hsp (hf0 _ h0)`. Take `⟨p, hp, q, hq, epq⟩` from `Ideal.isCoprime_iff_exists.1 hcop`. Set `a' : Matrix (Fin r) (Fin r) (𝓞 E)` to `p • a + q • 1`. Establish `e1 : ∀ j i, a' j i - a j i ∈ J` using `fun j i => by`. Establish `: a' j i - a j i = q * ((1 : Matrix (Fin r) (Fin r) (𝓞 E)) j i - a j i)`.

Simplify using `only [a', Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]`. Take the linear combination `a j i * epq`. Rewrite using `[this]`. Conclude with `Ideal.mul_mem_right _ _ hq`. Establish `e2 : ∀ j i, a' j i - (1 : Matrix (Fin r) (Fin r) (𝓞 E)) j i ∈ 𝔐` using `fun j i => by`.

Establish `: a' j i - (1 : Matrix (Fin r) (Fin r) (𝓞 E)) j i = p * (a j i - (1 : Matrix (Fin r) (Fin r) (𝓞 E)) j i)`. Simplify using `only [a', Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]`. Take the linear combination `(1 : Matrix (Fin r) (Fin r) (𝓞 E)) j i * epq`. Rewrite using `[this]`. Conclude with `Ideal.mul_mem_right _ _ hp`.

Establish `hd : ∀ (I : Ideal (𝓞 E)) (b : Matrix (Fin r) (Fin r) (𝓞 E)), (∀ j i, a' j i - b j i ∈ I) → IsCoprime (Ideal.span {b.det}) I → IsCoprime (Ideal.span {a'.det}) I` using `fun I b hb hI => by`. Rewrite `hI`, the goal using `[cop_iff_isUnit, RingHom.map_det]`. Use `hI using 2` and compare the differences between its conclusion and the goal. Use extensionality with `j i`. Conclude with `Ideal.Quotient.eq.2 (hb j i)`.

Establish `hu : IsUnit (a'.map (Ideal.Quotient.mk D.𝔪))`. Rewrite using `[Matrix.isUnit_iff_isUnit_det]`. Establish `: IsCoprime (Ideal.span {a'.det}) D.𝔪` using `hprod ▸ IsCoprime.mul_right (hd _ 1 e2 (by rw [Matrix.det_one]; exact cop_one)) (hd _ a e1 hdet)`. Rewrite `this` using `[cop_iff_isUnit, RingHom.map_det]`. Then use the resulting hypothesis. Use `h ⟨⟨⟨hu.unit, hgrp _ fun i j => ⟨_, e2 i j, ?_⟩⟩, a', rfl, fun i => ?_⟩, hy'⟩` and prove the remaining obligations.

Simplify using `[Matrix.one_apply]`. Rewrite using `[hprod]`. Use `cong_glue hcop (cong_trans (hy i).2 (cong_symm ?_)) (cong_trans (hy i).1 ?_)` and prove the remaining obligations. Simplify `cong_coeff' D.β_mem fun j => e2 j i` using `[Matrix.one_apply]`. Use `cong_trans ?_ (cong_trans (hcomb fun j => a j i) (cong_symm (cong_coeff' D.β_mem fun j => e1 j i)))` and prove the remaining obligations.

Use `(Submodule.Quotient.eq _).1 ((ha i).trans (mk_comb _ _).symm)` as an intermediate fact. Use `⟨s, hs', ?_⟩` and prove the remaining obligations. Rewrite using `[← map_sub]`. Use `Submodule.smul_induction_on this (fun m hm x _ => ?_) fun x y hx hy => ?_` and prove the remaining obligations. Rewrite using `[map_smul, smul_comm]`.

Conclude with `Submodule.smul_mem_smul hm (h1 _ (hδ x))`. Rewrite using `[map_add, smul_add]`. Conclude with `add_mem hx hy`.
-/
theorem tie_core (D : SW.Level X) {𝔐 J : Ideal (𝓞 E)} (hprod : D.𝔪 = 𝔐 * J) (hcop : IsCoprime 𝔐 J)
    (hgrp : ∀ k : GL (Fin r) (𝓞 E ⧸ D.𝔪), (∀ i j, ∃ a ∈ 𝔐,
      (k : Matrix (Fin r) (Fin r) (𝓞 E ⧸ D.𝔪)) i j - (1 : Matrix (Fin r) (Fin r) (𝓞 E ⧸ D.𝔪)) i j =
        Ideal.Quotient.mk D.𝔪 a) → k ∈ D.J)
    (e : (La ⧸ (J • ⊤ : Submodule (𝓞 E) La)) ≃ₗ[𝓞 E] (Fin r → 𝓞 E ⧸ J))
    (f : (Fin r → La ⧸ (J • ⊤ : Submodule (𝓞 E) La)) → ℂ)
    (hf0 : ∀ x, f x ≠ 0 → Submodule.span (𝓞 E) (Set.range x) = ⊤)
    (hf1 : ∀ z, Submodule.span (𝓞 E) (Set.range z) = ⊤ → ‖f z‖ = 1)
    (hf2 : ∀ z, Submodule.span (𝓞 E) (Set.range z) = ⊤ → ∀ (k : D.J) (a : Matrix (Fin r) (Fin r) (𝓞 E)),
      a.map (Ideal.Quotient.mk D.𝔪) = (k : GL (Fin r) (𝓞 E ⧸ D.𝔪)) →
        f (fun i => ∑ j, a j i • z j) = f z * (D.lam k : ℂˣ))
    {L : Lt E r} (hLl : L ∈ D.lats) (δ : La →ₗ[𝓞 E] (Fin r → E)) (hδ : ∀ a, δ a ∈ L)
    (hL : L ≤ LinearMap.range δ ⊔ J • L) {n : ℕ} (hn : r ≤ n) :
    ∃ t : ℂ, ‖t‖ = 1 ∧ ∀ (xs : Fin r → La) (y : Matrix (Fin n) (Fin r) E),
      (∀ i : Fin r, Cong X J (y (Fin.castLE hn i)) (δ (xs i)) ∧ Cong X 𝔐 (y (Fin.castLE hn i)) (D.β i)) →
      (∀ k : Fin n, r ≤ (k : ℕ) → Cong X 𝔐 (y k) 0) →
      f (fun b => Submodule.Quotient.mk (xs b)) = t * datF D 𝔐 hn y := by
  have hle : D.𝔪 ≤ J := hprod ▸ Ideal.mul_le_right
  have hJ : J ≠ ⊥ := fun h => D.ne_bot (le_bot_iff.1 (h ▸ hle))
  obtain ⟨-, s, hs, h1, h2⟩ := hLl
  have hs' : IsCoprime (Ideal.span {s}) J := (hprod ▸ hs.of_mul_right_left).of_mul_right_right
  have inj := fun a b => mem_of_cong (a := a) (b := b) hJ e hs' h1 h2 δ hδ hL
  obtain ⟨c, m, hm, ec⟩ := cop_iff.1 hs'
  have hz : ∀ i, ∃ z, Cong X J (δ z) (D.β i) := fun i => by
    obtain ⟨_, ⟨a, rfl⟩, w, hw, hvw⟩ := Submodule.mem_sup.1 (hL (h2 _ (D.β_mem i)))
    refine ⟨c • a, s, hs', ?_⟩
    have hw' : s • w ∈ J • X.Λ := smul_map_mem LinearMap.id h1 hw
    have : s • (δ (c • a) - D.β i) = -(c • s • w) - s • m • D.β i := by
      rw [map_smul, eq_sub_of_add_eq hvw]
      have : s • D.β i = s • (c * s + m) • D.β i := by rw [ec, one_smul]
      linear_combination (norm := module) -this
    rw [this]
    exact sub_mem (neg_mem (Submodule.smul_mem _ _ hw'))
      (Submodule.smul_mem _ _ (Submodule.smul_mem_smul hm (D.β_mem i)))
  choose z hz using hz
  have hcomb : ∀ a : Fin r → 𝓞 E, Cong X J (δ (∑ j, a j • z j)) (∑ j, a j • D.β j) := fun a => by
    simpa only [map_sum, map_smul] using cong_sum hz a
  have hsp : Submodule.span (𝓞 E) (Set.range fun i =>
      (Submodule.Quotient.mk (z i) : La ⧸ (J • ⊤ : Submodule (𝓞 E) La))) = ⊤ := by
    refine eq_top_iff.2 fun q _ => ?_
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    obtain ⟨u, hu, w, hw, huw⟩ := Submodule.mem_sup.1 (D.β_span (X.Λ.smul_mem c (h1 _ (hδ a))))
    obtain ⟨b, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 E)).1 hu
    have h3 : Cong X J (δ a) (∑ j, b j • D.β j) := by
      refine ⟨s, hs', ?_⟩
      have : s • (δ a - ∑ j, b j • D.β j) = m • s • δ a + s • w := by
        rw [eq_sub_of_add_eq huw]
        have : s • δ a = s • (c * s + m) • δ a := by rw [ec, one_smul]
        linear_combination (norm := module) this
      rw [this]
      exact add_mem (Submodule.smul_mem_smul hm (h1 _ (hδ a)))
        (Submodule.smul_mem _ _ (Submodule.smul_mono_left hle hw))
    rw [inj _ _ (cong_trans h3 (cong_symm (hcomb b))), mk_comb]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  refine ⟨_, hf1 _ hsp, fun xs y hy hy' => ?_⟩
  unfold datF
  split_ifs with h
  · obtain ⟨a, ha, hr⟩ := h.1.choose_spec
    rw [← hf2 _ hsp _ a ha]
    congr 1
    funext i
    rw [← mk_comb]
    exact inj _ _ (cong_trans (cong_symm (hy i).1) (cong_trans (cong_mono hle (hr i)) (cong_symm (hcomb _))))
  · rw [mul_zero]
    by_contra h0
    obtain ⟨a, hdet, ha⟩ := exists_matrix e _ _ hsp (hf0 _ h0)
    obtain ⟨p, hp, q, hq, epq⟩ := Ideal.isCoprime_iff_exists.1 hcop
    let a' : Matrix (Fin r) (Fin r) (𝓞 E) := p • a + q • 1
    have e1 : ∀ j i, a' j i - a j i ∈ J := fun j i => by
      have : a' j i - a j i = q * ((1 : Matrix (Fin r) (Fin r) (𝓞 E)) j i - a j i) := by
        simp only [a', Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
        linear_combination a j i * epq
      rw [this]; exact Ideal.mul_mem_right _ _ hq
    have e2 : ∀ j i, a' j i - (1 : Matrix (Fin r) (Fin r) (𝓞 E)) j i ∈ 𝔐 := fun j i => by
      have : a' j i - (1 : Matrix (Fin r) (Fin r) (𝓞 E)) j i =
          p * (a j i - (1 : Matrix (Fin r) (Fin r) (𝓞 E)) j i) := by
        simp only [a', Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
        linear_combination (1 : Matrix (Fin r) (Fin r) (𝓞 E)) j i * epq
      rw [this]; exact Ideal.mul_mem_right _ _ hp
    have hd : ∀ (I : Ideal (𝓞 E)) (b : Matrix (Fin r) (Fin r) (𝓞 E)), (∀ j i, a' j i - b j i ∈ I) →
        IsCoprime (Ideal.span {b.det}) I → IsCoprime (Ideal.span {a'.det}) I := fun I b hb hI => by
      rw [cop_iff_isUnit, RingHom.map_det] at hI ⊢
      convert hI using 2
      ext j i
      exact Ideal.Quotient.eq.2 (hb j i)
    have hu : IsUnit (a'.map (Ideal.Quotient.mk D.𝔪)) := by
      rw [Matrix.isUnit_iff_isUnit_det]
      have : IsCoprime (Ideal.span {a'.det}) D.𝔪 := hprod ▸ IsCoprime.mul_right
        (hd _ 1 e2 (by rw [Matrix.det_one]; exact cop_one)) (hd _ a e1 hdet)
      rwa [cop_iff_isUnit, RingHom.map_det] at this
    refine h ⟨⟨⟨hu.unit, hgrp _ fun i j => ⟨_, e2 i j, ?_⟩⟩, a', rfl, fun i => ?_⟩, hy'⟩
    · simp [Matrix.one_apply]
    · rw [hprod]
      refine cong_glue hcop (cong_trans (hy i).2 (cong_symm ?_)) (cong_trans (hy i).1 ?_)
      · simpa [Matrix.one_apply] using cong_coeff' D.β_mem fun j => e2 j i
      · refine cong_trans ?_ (cong_trans (hcomb fun j => a j i) (cong_symm (cong_coeff' D.β_mem fun j => e1 j i)))
        have := (Submodule.Quotient.eq _).1 ((ha i).trans (mk_comb _ _).symm)
        refine ⟨s, hs', ?_⟩
        rw [← map_sub]
        refine Submodule.smul_induction_on this (fun m hm x _ => ?_) fun x y hx hy => ?_
        · rw [map_smul, smul_comm]; exact Submodule.smul_mem_smul hm (h1 _ (hδ x))
        · rw [map_add, smul_add]; exact add_mem hx hy

/- English proof (translation)
Use extensionality with `q`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨b, hb, rfl⟩`. Conclude with `⟨⟨b, hb⟩, rfl⟩`. Introduce and unpack `⟨i, rfl⟩`.

Conclude with `⟨_, i.2, rfl⟩`.
-/
theorem image_lt_eq_range {Q : Type} {n : ℕ} (hn : r ≤ n) (x : Fin n → Q) :
    x '' {b | b.val < r} = Set.range fun i => x (Fin.castLE hn i) := by
  ext q
  constructor
  · rintro ⟨b, hb, rfl⟩
    exact ⟨⟨b, hb⟩, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨_, i.2, rfl⟩

/- English proof (translation)
Use extensionality with `a`. Establish `hb : bar a = H.bar a` using `RingOfIntegers.ext ((coe_bar a).trans (H.bar_eq a).symm)`. Rewrite using `[mem_conjI, hb]`. Use `⟨fun h => ?_, fun h => Ideal.mem_map_of_mem (H.bar : 𝓞 E →+* 𝓞 E) h⟩` and prove the remaining obligations. Use `bar_mem h` as an intermediate fact.

Rewrite `this` using `[LevelPairing.bar_bar]`. Then use the resulting hypothesis.
-/
theorem conjI_Mfr {H : Host E} (l : Geo.Tor.Level H) : conjI (Mfr l) = l.Mb := by
  ext a
  have hb : bar a = H.bar a := RingOfIntegers.ext ((coe_bar a).trans (H.bar_eq a).symm)
  rw [mem_conjI, hb]
  refine ⟨fun h => ?_, fun h => Ideal.mem_map_of_mem (H.bar : 𝓞 E →+* 𝓞 E) h⟩
  have := bar_mem h
  rwa [LevelPairing.bar_bar] at this

/- English proof (translation)
The claim follows from `(l.prod ▸ Ideal.mul_le_right : Ideal.span {(l.M : 𝓞 E)} ≤ Mfr l) (Ideal.mem_span_singleton_self _)`.
-/
theorem natCast_mem_Mfr {H : Host E} (l : Geo.Tor.Level H) : (l.M : 𝓞 E) ∈ Mfr l :=
  (l.prod ▸ Ideal.mul_le_right : Ideal.span {(l.M : 𝓞 E)} ≤ Mfr l) (Ideal.mem_span_singleton_self _)

/- English proof (translation)
Introduce `h`. Establish `h1 : l.Mb = ⊤`. Rewrite using `[← conjI_Mfr, h, eq_top_iff]`. Conclude with `fun a _ => mem_conjI.2 trivial`. Establish `h2` using `l.prod`.

Rewrite `h2` using `[h1, Ideal.map_top, Ideal.mul_top, eq_comm, Ideal.span_singleton_eq_top]`. Establish `h3 : IsUnit (algebraMap ℤ (𝓞 E) (l.M : ℤ))` using `by simpa using h2`. Establish `h4` using `Int.isUnit_iff.1 (isUnit_of_map_unit _ _ h3)`. Use `l.three_le` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem Mfr_ne_top {H : Host E} (l : Geo.Tor.Level H) : Mfr l ≠ ⊤ := by
  intro h
  have h1 : l.Mb = ⊤ := by
    rw [← conjI_Mfr, h, eq_top_iff]; exact fun a _ => mem_conjI.2 trivial
  have h2 := l.prod
  rw [h1, Ideal.map_top, Ideal.mul_top, eq_comm, Ideal.span_singleton_eq_top] at h2
  have h3 : IsUnit (algebraMap ℤ (𝓞 E) (l.M : ℤ)) := by simpa using h2
  have h4 := Int.isUnit_iff.1 (isUnit_of_map_unit _ _ h3)
  have := l.three_le
  omega

/- English proof (translation)
Take `⟨u, v, e⟩` from `h.cast (R := R)`. Conclude with `Ideal.isCoprime_iff_exists.2 ⟨_, I.mul_mem_left u ha, _, J.mul_mem_left v hb, e⟩`.
-/
theorem cop_of_nat {R : Type} [CommRing R] {I J : Ideal R} {a b : ℕ} (h : Nat.Coprime a b) (ha : (a : R) ∈ I)
    (hb : (b : R) ∈ J) : IsCoprime I J := by
  obtain ⟨u, v, e⟩ := h.cast (R := R)
  exact Ideal.isCoprime_iff_exists.2 ⟨_, I.mul_mem_left u ha, _, J.mul_mem_left v hb, e⟩

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c n d σ r X hn hr _ hd h3 ph ψ x₀ hph`. Substitute `hr` using the available equality. Take `⟨-, huniq, adj, hadj, hadj'⟩` from `halves_free_and_adjoint E H Dw l Xo c n d hd`. Take `⟨-, hM, hcM, hMb, hI, -⟩` from `hd`. Take `⟨pa, pb, pc, pd, px, -⟩` from `hph`.

Establish `hM0 : l.M ≠ 0` using `by have := l.three_le; omega`. Establish `hM2 : d.l₂.M ≠ 0` using `by have := d.l₂.three_le; omega`. Establish `hp : d.I * Jd d = Ideal.span {(d.pd : 𝓞 E)}`. Establish `h2` using `d.l₂.prod`. Rewrite `h2` using `[hMb, hM, Ideal.map_mul, _root_.mul_mul_mul_comm, l.prod, Nat.cast_mul, ← Ideal.span_singleton_mul_span_singleton]`.

Use `mul_left_cancel₀ ?_ h2` and prove the remaining obligations. Rewrite using `[Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]`. Conclude with `hM0` after adjusting the coercions. Establish `hpJ : (d.pd : 𝓞 E) ∈ Jd d` using `(hp ▸ Ideal.mul_le_right : Ideal.span {(d.pd : 𝓞 E)} ≤ Jd d) (Ideal.mem_span_singleton_self _)`. Establish `hprod : Mfr d.l₂ = Mfr l * Jd d`.

Rewrite using `[Mfr, hMb, Ideal.map_mul]`. Both sides reduce to the same expression. Establish `hcop : IsCoprime (Mfr l) (Jd d)` using `cop_of_nat hcM.symm (natCast_mem_Mfr l) hpJ`. Establish `hbot : Mfr d.l₂ ≠ ⊥` using `fun h => by`. Use `natCast_mem_Mfr d.l₂` as an intermediate fact.

Rewrite `this` using `[h, Ideal.mem_bot]`. Conclude with `hM2 (by exact_mod_cast this)`. Establish `hle : Mfr d.l₂ ≤ Jd d` using `hprod ▸ Ideal.mul_le_right`. Establish `hle' : Mfr d.l₂ ≤ Mfr l` using `hprod ▸ Ideal.mul_le_left`. Establish `hJ : Jd d ≠ ⊥` using `fun h => hbot (le_bot_iff.1 (h ▸ hle))`.

Use `haveI : Finite (𝓞 E ⧸ Jd d) := Ideal.finiteQuotientOfFreeOfNeBot _ hJ`. Use `haveI := Dw.fin`. Use `haveI := Dw.proj`. Take `⟨e⟩ : Nonempty (LaJ Xo c d ≃ₗ[𝓞 E] (Fin (Dw.p + Dw.q) → 𝓞 E ⧸ Jd d))` from `nonempty_equiv_quot (N := Dw.La) (Jd d) _ Dw.rank`. Rewrite `px` using `[image_lt_eq_range hn]`.

Take `⟨e₀, he₀⟩` from `exists_equiv_of_span _ _ e _ px`. Set `χ : (LaJ Xo c d ≃ₗ[𝓞 E] LaJ Xo c d) →* ℂˣ` to `(Units.map (σ : c.F →* ℂ)).comp (MonoidHom.mk' (fun g => (ψ (adj g))⁻¹) fun g g' => by rw [hadj, map_mul, mul_inv, mul_comm])`. Set `ext : (Fin (Dw.p + Dw.q) → LaJ Xo c d) → Fin n → LaJ Xo c d` to `fun x b => if h : b.val < Dw.p + Dw.q then x ⟨b, h⟩ else 0`. Establish `hext : ∀ x i, ext x (Fin.castLE hn i) = x i` using `fun x i => dif_pos i.2`. Set `f : (Fin (Dw.p + Dw.q) → LaJ Xo c d) → ℂ` to `fun x => σ (ph (ext x))`.

Establish `hf : ∀ x, σ (ph x) = f fun i => x (Fin.castLE hn i)` using `fun x => congrArg σ (pa _ _ fun b hb => (hext (fun i => x (Fin.castLE hn i)) ⟨b, hb⟩).symm)`. Establish `hfg : ∀ g : LaJ Xo c d ≃ₗ[𝓞 E] LaJ Xo c d, f (fun i => g (x₀ (Fin.castLE hn i))) = (χ g : ℂˣ)` using `fun g => by`. Rewrite using `[← hf fun b => g (x₀ b), pc (adj g) g ((hadj' _ _).2 rfl), pd, _root_.mul_one]`. Both sides reduce to the same expression. Establish `hchar : ∀ g : GL (Fin (Dw.p + Dw.q)) (𝓞 E ⧸ Jd d), (g : Matrix (Fin (Dw.p + Dw.q)) (Fin (Dw.p + Dw.q)) (𝓞 E ⧸ Jd d)).det = 1 → χ (rho e₀ g) = 1` using `generalLinearGroup_char_eq_one_of_det_eq_one _ _ _ (χ.comp (rho e₀)) (four_le_card d.pd (Nat.odd_mul.1 (hM ▸ d.l₂.odd)).2 h3 (by rw [← map_natCast (Ideal.Quotient.mk (Jd d)), Ideal.Quotient.eq_zero_iff_mem]; exact hpJ))`.

Take `⟨β, hβ, hβ'⟩` from `exists_frame X (Mfr d.l₂) hbot`. Set `G` to `(Matrix.GeneralLinearGroup.map (n := Fin (Dw.p + Dw.q)) (Ideal.Quotient.factor hle')).ker`. Set `D : SW.Level X` to `{ 𝔪 := Mfr d.l₂ proper := Mfr_ne_top _ ne_bot := hbot cop := by`. Rewrite using `[conjI_Mfr, Ideal.isCoprime_iff_sup_eq, sup_comm]`. Conclude with `d.l₂.coprime`.

Use `odd := cop_of_nat (Nat.coprime_two_right.2 d.l₂.odd) (natCast_mem_Mfr _) (Ideal.mem_span_singleton_self _)`. Use `β := β`. Use `β_mem := hβ`. Use `β_span := hβ'`. Use `J := G`.

Use `lam := (χ.comp ((rho e₀).comp (Matrix.GeneralLinearGroup.map (Ideal.Quotient.factor hle)))).comp G.subtype`. Use `w := H.w0`. Use `w_int := H.w0.2`. Use `w_tr := by`. Use `congrArg (fun a : 𝓞 E => (a : E)) (PullbackSections.CVA.cmHostUnit_add_conj_eq_one H)` as an intermediate fact.

Simplify `this }` using `[H.bar_eq, cc]`. Establish `hG : ∀ k : GL (Fin (Dw.p + Dw.q)) (𝓞 E ⧸ Mfr d.l₂), k ∈ G ↔ ∀ i j, ∃ a ∈ Mfr l, (k : Matrix (Fin (Dw.p + Dw.q)) (Fin (Dw.p + Dw.q)) (𝓞 E ⧸ Mfr d.l₂)) i j - (1 : Matrix (Fin (Dw.p + Dw.q)) (Fin (Dw.p + Dw.q)) (𝓞 E ⧸ Mfr d.l₂)) i j = Ideal.Quotient.mk (Mfr d.l₂) a` using `fun k => by`. Rewrite using `[MonoidHom.mem_ker, Matrix.GeneralLinearGroup.ext_iff]`. Use `forall₂_congr fun i j => ?_` and prove the remaining obligations. Establish `key : ∀ u : 𝓞 E ⧸ Mfr d.l₂, Ideal.Quotient.factor hle' u = 0 ↔ ∃ a ∈ Mfr l, u = Ideal.Quotient.mk (Mfr d.l₂) a` using `fun u => by`.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Take `⟨a, rfl⟩` from `Ideal.Quotient.mk_surjective u`. Conclude with `⟨a, Ideal.Quotient.eq_zero_iff_mem.1 h, rfl⟩`. Introduce and unpack `⟨a, ha, rfl⟩`.

Conclude with `Ideal.Quotient.eq_zero_iff_mem.2 ha`. Rewrite using `[← key, map_sub, sub_eq_zero]`. Establish `h1 : Ideal.Quotient.factor hle' ((1 : Matrix (Fin (Dw.p + Dw.q)) (Fin (Dw.p + Dw.q)) (𝓞 E ⧸ Mfr d.l₂)) i j) = (1 : Matrix (Fin (Dw.p + Dw.q)) (Fin (Dw.p + Dw.q)) (𝓞 E ⧸ Mfr l)) i j`. Simplify using `only [Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> simp`.

Rewrite using `[h1]`. Both sides reduce to the same expression. Use `⟨D, rfl, hprod, hcop, rfl, hG, fun k hk => hchar _ ?_, fun L hL δ hδ hLδ => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `((Ideal.Quotient.factor hle).mapMatrix _).det = 1`. Rewrite using `[← RingHom.map_det]`.

Conclude with `(congrArg _ hk).trans (map_one _)`. Use `haveI : Finite (LaJ Xo c d) := Finite.of_equiv _ e.symm.toEquiv haveI : Finite (LaJ Xo c d ≃ₗ[𝓞 E] LaJ Xo c d) := Finite.of_injective (fun g => (g : LaJ Xo c d → LaJ Xo c d)) DFunLike.coe_injective`. Take `⟨t, ht, H⟩` from `tie_core D hprod hcop (fun k => (hG k).2) e f (fun x hx => by`. Use `pb (ext x) fun h => hx (by simp only [f, h, map_zero])` as an intermediate fact. Rewrite using `[image_lt_eq_range hn, funext (hext x)] at this)` and apply the resulting hypothesis.

Use the proof step `(fun z hz => by`. Take `⟨g, hg, -⟩` from `huniq _ z px hz`. Rewrite using `[← funext hg, hfg]`. Use `Complex.norm_eq_one_of_pow_eq_one (n := Nat.card (LaJ Xo c d ≃ₗ[𝓞 E] LaJ Xo c d)) ?_ Nat.card_pos.ne'` and prove the remaining obligations. Rewrite using `[← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one', map_one, Units.val_one])`.

Use the proof step `(fun z hz k a ha => by`. Take `⟨g, hg, -⟩` from `huniq _ z px hz`. Establish `h1` using `rho_apply e₀ (Matrix.GeneralLinearGroup.map (Ideal.Quotient.factor hle) k.1) a (by`. Express the relevant statement in the definitionally equal form `_ = (k.1.1).map _`. Rewrite using `[← ha, Matrix.map_map]`.

Use the proof step `rfl)`. Simplify using `only [he₀] at h1`. Establish `h2` using `hfg (g * rho e₀ (Matrix.GeneralLinearGroup.map (Ideal.Quotient.factor hle) k.1))`. Simplify using `only [LinearEquiv.mul_apply, h1, map_sum, map_smul] at h2`. Rewrite using `[← funext hg, hfg]`.

Conclude with `h2.trans (by rw [map_mul, Units.val_mul]; rfl)) hL δ hδ hLδ hn`. Conclude with `⟨t, ht, fun xs y h1 h2 => (hf _).trans (H _ y h1 h2)⟩`.
-/
theorem exists_levTie : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n) (σ : c.F →+* ℂ) (r : ℕ) (X : Data E r) (hn : r ≤ n), r = Dw.p + Dw.q → SelfD X X.Λ → d.IsLev → ¬ 3 ∣ d.pd → ∀ (ph : (Fin n → LaJ Xo c d) → c.F) (ψ : (LaI Xo c d ≃ₗ[𝓞 E] LaI Xo c d) →* c.Fˣ) (x₀ : Fin n → LaJ Xo c d), d.PhiPin ph ψ x₀ → ∃ D : SW.Level X, LevTie d σ ph D hn := by
  intro E _ _ _ H Dw l Xo c n d σ r X hn hr _ hd h3 ph ψ x₀ hph
  subst hr
  obtain ⟨-, huniq, adj, hadj, hadj'⟩ := halves_free_and_adjoint E H Dw l Xo c n d hd
  obtain ⟨-, hM, hcM, hMb, hI, -⟩ := hd
  obtain ⟨pa, pb, pc, pd, px, -⟩ := hph
  have hM0 : l.M ≠ 0 := by have := l.three_le; omega
  have hM2 : d.l₂.M ≠ 0 := by have := d.l₂.three_le; omega
  have hp : d.I * Jd d = Ideal.span {(d.pd : 𝓞 E)} := by
    have h2 := d.l₂.prod
    rw [hMb, hM, Ideal.map_mul, _root_.mul_mul_mul_comm, l.prod, Nat.cast_mul, ← Ideal.span_singleton_mul_span_singleton] at h2
    refine mul_left_cancel₀ ?_ h2
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hM0
  have hpJ : (d.pd : 𝓞 E) ∈ Jd d :=
    (hp ▸ Ideal.mul_le_right : Ideal.span {(d.pd : 𝓞 E)} ≤ Jd d) (Ideal.mem_span_singleton_self _)
  have hprod : Mfr d.l₂ = Mfr l * Jd d := by
    rw [Mfr, hMb, Ideal.map_mul]; rfl
  have hcop : IsCoprime (Mfr l) (Jd d) := cop_of_nat hcM.symm (natCast_mem_Mfr l) hpJ
  have hbot : Mfr d.l₂ ≠ ⊥ := fun h => by
    have := natCast_mem_Mfr d.l₂
    rw [h, Ideal.mem_bot] at this
    exact hM2 (by exact_mod_cast this)
  have hle : Mfr d.l₂ ≤ Jd d := hprod ▸ Ideal.mul_le_right
  have hle' : Mfr d.l₂ ≤ Mfr l := hprod ▸ Ideal.mul_le_left
  have hJ : Jd d ≠ ⊥ := fun h => hbot (le_bot_iff.1 (h ▸ hle))
  haveI : Finite (𝓞 E ⧸ Jd d) := Ideal.finiteQuotientOfFreeOfNeBot _ hJ
  haveI := Dw.fin
  haveI := Dw.proj
  obtain ⟨e⟩ : Nonempty (LaJ Xo c d ≃ₗ[𝓞 E] (Fin (Dw.p + Dw.q) → 𝓞 E ⧸ Jd d)) :=
    nonempty_equiv_quot (N := Dw.La) (Jd d) _ Dw.rank
  rw [image_lt_eq_range hn] at px
  obtain ⟨e₀, he₀⟩ := exists_equiv_of_span _ _ e _ px
  let χ : (LaJ Xo c d ≃ₗ[𝓞 E] LaJ Xo c d) →* ℂˣ := (Units.map (σ : c.F →* ℂ)).comp
    (MonoidHom.mk' (fun g => (ψ (adj g))⁻¹) fun g g' => by rw [hadj, map_mul, mul_inv, mul_comm])
  let ext : (Fin (Dw.p + Dw.q) → LaJ Xo c d) → Fin n → LaJ Xo c d := fun x b =>
    if h : b.val < Dw.p + Dw.q then x ⟨b, h⟩ else 0
  have hext : ∀ x i, ext x (Fin.castLE hn i) = x i := fun x i => dif_pos i.2
  let f : (Fin (Dw.p + Dw.q) → LaJ Xo c d) → ℂ := fun x => σ (ph (ext x))
  have hf : ∀ x, σ (ph x) = f fun i => x (Fin.castLE hn i) := fun x =>
    congrArg σ (pa _ _ fun b hb => (hext (fun i => x (Fin.castLE hn i)) ⟨b, hb⟩).symm)
  have hfg : ∀ g : LaJ Xo c d ≃ₗ[𝓞 E] LaJ Xo c d,
      f (fun i => g (x₀ (Fin.castLE hn i))) = (χ g : ℂˣ) := fun g => by
    rw [← hf fun b => g (x₀ b), pc (adj g) g ((hadj' _ _).2 rfl), pd, _root_.mul_one]
    rfl
  have hchar : ∀ g : GL (Fin (Dw.p + Dw.q)) (𝓞 E ⧸ Jd d),
      (g : Matrix (Fin (Dw.p + Dw.q)) (Fin (Dw.p + Dw.q)) (𝓞 E ⧸ Jd d)).det = 1 → χ (rho e₀ g) = 1 :=
    generalLinearGroup_char_eq_one_of_det_eq_one _ _ _ (χ.comp (rho e₀)) (four_le_card d.pd
      (Nat.odd_mul.1 (hM ▸ d.l₂.odd)).2 h3
      (by rw [← map_natCast (Ideal.Quotient.mk (Jd d)), Ideal.Quotient.eq_zero_iff_mem]; exact hpJ))
  obtain ⟨β, hβ, hβ'⟩ := exists_frame X (Mfr d.l₂) hbot
  let G := (Matrix.GeneralLinearGroup.map (n := Fin (Dw.p + Dw.q)) (Ideal.Quotient.factor hle')).ker
  let D : SW.Level X :=
    { 𝔪 := Mfr d.l₂
      proper := Mfr_ne_top _
      ne_bot := hbot
      cop := by
        rw [conjI_Mfr, Ideal.isCoprime_iff_sup_eq, sup_comm]; exact d.l₂.coprime
      odd := cop_of_nat (Nat.coprime_two_right.2 d.l₂.odd) (natCast_mem_Mfr _) (Ideal.mem_span_singleton_self _)
      β := β
      β_mem := hβ
      β_span := hβ'
      J := G
      lam := (χ.comp ((rho e₀).comp (Matrix.GeneralLinearGroup.map (Ideal.Quotient.factor hle)))).comp G.subtype
      w := H.w0
      w_int := H.w0.2
      w_tr := by
        have := congrArg (fun a : 𝓞 E => (a : E)) (PullbackSections.CVA.cmHostUnit_add_conj_eq_one H)
        simpa [H.bar_eq, cc] using this }
  have hG : ∀ k : GL (Fin (Dw.p + Dw.q)) (𝓞 E ⧸ Mfr d.l₂), k ∈ G ↔ ∀ i j, ∃ a ∈ Mfr l,
      (k : Matrix (Fin (Dw.p + Dw.q)) (Fin (Dw.p + Dw.q)) (𝓞 E ⧸ Mfr d.l₂)) i j - (1 : Matrix (Fin (Dw.p + Dw.q)) (Fin (Dw.p + Dw.q)) (𝓞 E ⧸ Mfr d.l₂)) i j =
        Ideal.Quotient.mk (Mfr d.l₂) a := fun k => by
    rw [MonoidHom.mem_ker, Matrix.GeneralLinearGroup.ext_iff]
    refine forall₂_congr fun i j => ?_
    have key : ∀ u : 𝓞 E ⧸ Mfr d.l₂, Ideal.Quotient.factor hle' u = 0 ↔
        ∃ a ∈ Mfr l, u = Ideal.Quotient.mk (Mfr d.l₂) a := fun u => by
      constructor
      · intro h
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective u
        exact ⟨a, Ideal.Quotient.eq_zero_iff_mem.1 h, rfl⟩
      · rintro ⟨a, ha, rfl⟩
        exact Ideal.Quotient.eq_zero_iff_mem.2 ha
    rw [← key, map_sub, sub_eq_zero]
    have h1 : Ideal.Quotient.factor hle'
        ((1 : Matrix (Fin (Dw.p + Dw.q)) (Fin (Dw.p + Dw.q)) (𝓞 E ⧸ Mfr d.l₂)) i j) =
        (1 : Matrix (Fin (Dw.p + Dw.q)) (Fin (Dw.p + Dw.q)) (𝓞 E ⧸ Mfr l)) i j := by
      simp only [Matrix.one_apply]
      split_ifs <;> simp
    rw [h1]
    rfl
  refine ⟨D, rfl, hprod, hcop, rfl, hG, fun k hk => hchar _ ?_, fun L hL δ hδ hLδ => ?_⟩
  · change ((Ideal.Quotient.factor hle).mapMatrix _).det = 1
    rw [← RingHom.map_det]
    exact (congrArg _ hk).trans (map_one _)
  · haveI : Finite (LaJ Xo c d) := Finite.of_equiv _ e.symm.toEquiv
    haveI : Finite (LaJ Xo c d ≃ₗ[𝓞 E] LaJ Xo c d) :=
      Finite.of_injective (fun g => (g : LaJ Xo c d → LaJ Xo c d)) DFunLike.coe_injective
    obtain ⟨t, ht, H⟩ := tie_core D hprod hcop (fun k => (hG k).2) e f
      (fun x hx => by
        have := pb (ext x) fun h => hx (by simp only [f, h, map_zero])
        rwa [image_lt_eq_range hn, funext (hext x)] at this)
      (fun z hz => by
        obtain ⟨g, hg, -⟩ := huniq _ z px hz
        rw [← funext hg, hfg]
        refine Complex.norm_eq_one_of_pow_eq_one (n := Nat.card (LaJ Xo c d ≃ₗ[𝓞 E] LaJ Xo c d)) ?_ Nat.card_pos.ne'
        rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one', map_one, Units.val_one])
      (fun z hz k a ha => by
        obtain ⟨g, hg, -⟩ := huniq _ z px hz
        have h1 := rho_apply e₀ (Matrix.GeneralLinearGroup.map (Ideal.Quotient.factor hle) k.1) a (by
          change _ = (k.1.1).map _
          rw [← ha, Matrix.map_map]; rfl)
        simp only [he₀] at h1
        have h2 := hfg (g * rho e₀ (Matrix.GeneralLinearGroup.map (Ideal.Quotient.factor hle) k.1))
        simp only [LinearEquiv.mul_apply, h1, map_sum, map_smul] at h2
        rw [← funext hg, hfg]
        exact h2.trans (by rw [map_mul, Units.val_mul]; rfl)) hL δ hδ hLδ hn
    exact ⟨t, ht, fun xs y h1 h2 => (hf _).trans (H _ y h1 h2)⟩

end GlobalTheory.LevelTied
