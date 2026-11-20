import Formalism.SharpRestriction.GlobalSchurBounds.ProductFirstZerothParts
import Formalism.SharpRestriction.GlobalSchurBounds.TaylorLogMetric
import Formalism.SharpRestriction.GlobalSchurBounds.FlipTwoThree
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
import Formalism.SharpRestriction.GlobalSchurBounds.CMFieldLemmas
import Formalism.SharpRestriction.GlobalSchurBounds.ShortIntervalPrimes
import Formalism.SharpRestriction.GlobalSchurBounds.LocalCountingBounds
import Formalism.SharpRestriction.GlobalSchurBounds.ZetaZeroFreeRegion
import Formalism.FrobeniusOrbits.HostCorollaries
import Formalism.LocalRingCardinality.DataLevelD
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Formalism.SizeWindowBrackets.ChainSlopeWindows.GaloisMapComplexConjugation
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.FrameFacts
import Development.AutomorphicArithmetic.PrimeDiscriminants.RamDiscr
import Development.AutomorphicArithmetic.ConductorsKronecker.dataField
import Development.AutomorphicArithmetic.ConductorsKronecker.Imports

noncomputable section

namespace Formalism.MainNotions.GlobalTheoryTheory

open NumberField Formalism.FrobeniusOrbits Formalism.BasicNotions
open scoped Pointwise

/- English proof (translation)
Take `⟨h1, h2, h3, h4, h5, h6⟩` from `h`. Use `⟨⟨?_, h1⟩, h3, fun t h => h4 h t, fun ψ => h5 ψ, ?_⟩` and prove the remaining obligations. Use extensionality with `φ`. Prove the components needed by the constructor for the conclusion. Introduce `hφ show φ D.host.sqd = _`.

Rewrite using `[h2 φ hφ _ D.host.sqd_mem_K]`. Conclude with `D.host.φ₀_mem`. Introduce `hφ`. Assume the negation of the conclusion as `hn`. Establish `hc : (starRingEnd ℂ).comp φ ∈ PhiEmb D`.

Assume the negation of the conclusion as `hc'`. Conclude with `hn ((h1 φ).mpr hc')`. Establish `e1` using `h2 _ hc _ D.host.sqd_mem_K`. Establish `e2 : φ (D.host.sqd) = Complex.I * (Real.sqrt D.host.d : ℂ)` using `hφ`. Establish `e3 : D.host.φ₀ (D.host.sqd) = Complex.I * (Real.sqrt D.host.d : ℂ)` using `D.host.φ₀_mem`.

Simplify using `only [RingHom.coe_comp, Function.comp_apply] at e1`. Rewrite `e1` using `[e2, e3]`. Establish `hd : (0 : ℝ) < Real.sqrt D.host.d` using `Real.sqrt_pos.mpr (by exact_mod_cast D.host.hyp.2.1.pos)`. Use `congrArg Complex.im e1` as an intermediate fact. Simplify using `at this`.

Combine the linear equalities and inequalities to obtain the conclusion. Introduce `g`. Use `congrArg (fun r : ℚ => (r : ℝ)) (h6 g)` as an intermediate fact. Apply the tactic sequence `rcases Int.units_eq_one_or (D.R.chD g) with hc | hc <;>`. Apply the tactic sequence `rcases Int.units_eq_one_or (D.R.chQ g) with hp | hp <;>`.

Apply the tactic sequence `simp only [hc, hp] at this ⊢ <;> split_ifs at this ⊢ <;> push_cast at this ⊢ <;> linarith`.
-/
theorem _root_.Formalism.MainNotions.ZetaZeroFreeRegion.second_hypothesis_of_lifting (D : D7) (h : Formalism.MainNotions.UnusedSlot33.Conclusion2 D) : Formalism.MainNotions.ZetaZeroFreeRegion.adm2 D := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨⟨?_, h1⟩, h3, fun t h => h4 h t, fun ψ => h5 ψ, ?_⟩
  · ext φ
    constructor
    · intro hφ
      show φ D.host.sqd = _
      rw [h2 φ hφ _ D.host.sqd_mem_K]
      exact D.host.φ₀_mem
    · intro hφ
      by_contra hn
      have hc : (starRingEnd ℂ).comp φ ∈ PhiEmb D := by
        by_contra hc'
        exact hn ((h1 φ).mpr hc')
      have e1 := h2 _ hc _ D.host.sqd_mem_K
      have e2 : φ (D.host.sqd) = Complex.I * (Real.sqrt D.host.d : ℂ) := hφ
      have e3 : D.host.φ₀ (D.host.sqd) = Complex.I * (Real.sqrt D.host.d : ℂ) :=
        D.host.φ₀_mem
      simp only [RingHom.coe_comp, Function.comp_apply] at e1
      rw [e2, e3] at e1
      have hd : (0 : ℝ) < Real.sqrt D.host.d := Real.sqrt_pos.mpr (by exact_mod_cast D.host.hyp.2.1.pos)
      have := congrArg Complex.im e1
      simp at this
      linarith
  · intro g
    have := congrArg (fun r : ℚ => (r : ℝ)) (h6 g)
    rcases Int.units_eq_one_or (D.R.chD g) with hc | hc <;>
      rcases Int.units_eq_one_or (D.R.chQ g) with hp | hp <;>
      simp only [hc, hp] at this ⊢ <;> split_ifs at this ⊢ <;> push_cast at this ⊢ <;> linarith

/- English proof (translation)
Establish `hne : (1 : (𝓞 E)ˣ) ≠ -1`. Introduce `h`. Establish `h1` using `congrArg (fun v : (𝓞 E)ˣ => ((v : 𝓞 E) : E)) h`. Move the coercions through the operations in `at h1`. Establish `h2 : (2 : E) = 0` using `by linear_combination h1`.

Conclude with `two_ne_zero h2`. Establish `hset : ((NumberField.Units.torsion E : Subgroup (𝓞 E)ˣ) : Set (𝓞 E)ˣ) = {1, -1}`. Use extensionality with `u`. Simplify using `only [SetLike.mem_coe, Set.mem_insert_iff, Set.mem_singleton_iff]`. Rewrite using `[NumberField.Units.torsion, CommGroup.mem_torsion]`.

Prove the components needed by the constructor for the conclusion. Introduce `hu`. Take `⟨m, hm, hum⟩` from `hu.exists_pow_eq_one`. Establish `h1 : ((u : 𝓞 E) : E) ^ m = 1`. Use `congrArg (fun v : (𝓞 E)ˣ => ((v : 𝓞 E) : E)) hum` as an intermediate fact.

Simplify using `using this`. Break down `(hμ _).mp ⟨m, hm, h1⟩ with h2 | h2` into its components or cases. Use `left`. Use `ext`. Simplify using `using h2`.

Use `right`. Use `ext`. Simplify using `using h2`. Introduce and unpack `(rfl | rfl)`. Conclude with `isOfFinOrder_iff_pow_eq_one.mpr ⟨1, by norm_num, by simp⟩`.

Conclude with `isOfFinOrder_iff_pow_eq_one.mpr ⟨2, by norm_num, by simp⟩`. Unfold `NumberField.Units.torsionOrder`. Establish `: Nat.card (NumberField.Units.torsion E) = Nat.card (({1, -1} : Set (𝓞 E)ˣ))`. Rewrite using `[← hset]`. Both sides reduce to the same expression.

Rewrite using `[this, Nat.card_coe_set_eq, Set.ncard_pair hne]`.
-/
theorem jnt_torsionOrder_two (E : Type*) [Field E] [NumberField E]
    (hμ : ∀ x : E, (∃ m : ℕ, 0 < m ∧ x ^ m = 1) ↔ (x = 1 ∨ x = -1)) :
    NumberField.Units.torsionOrder E = 2 := by
  have hne : (1 : (𝓞 E)ˣ) ≠ -1 := by
    intro h
    have h1 := congrArg (fun v : (𝓞 E)ˣ => ((v : 𝓞 E) : E)) h
    push_cast at h1
    have h2 : (2 : E) = 0 := by linear_combination h1
    exact two_ne_zero h2
  have hset : ((NumberField.Units.torsion E : Subgroup (𝓞 E)ˣ) : Set (𝓞 E)ˣ) = {1, -1} := by
    ext u
    simp only [SetLike.mem_coe, Set.mem_insert_iff, Set.mem_singleton_iff]
    rw [NumberField.Units.torsion, CommGroup.mem_torsion]
    constructor
    · intro hu
      obtain ⟨m, hm, hum⟩ := hu.exists_pow_eq_one
      have h1 : ((u : 𝓞 E) : E) ^ m = 1 := by
        have := congrArg (fun v : (𝓞 E)ˣ => ((v : 𝓞 E) : E)) hum
        simpa using this
      rcases (hμ _).mp ⟨m, hm, h1⟩ with h2 | h2
      · left; ext; simpa using h2
      · right; ext; simpa using h2
    · rintro (rfl | rfl)
      · exact isOfFinOrder_iff_pow_eq_one.mpr ⟨1, by norm_num, by simp⟩
      · exact isOfFinOrder_iff_pow_eq_one.mpr ⟨2, by norm_num, by simp⟩
  unfold NumberField.Units.torsionOrder
  have : Nat.card (NumberField.Units.torsion E) = Nat.card (({1, -1} : Set (𝓞 E)ˣ)) := by
    rw [← hset]; rfl
  rw [this, Nat.card_coe_set_eq, Set.ncard_pair hne]

/- English proof (translation)
Establish `: IsGalois ℚ D.host.E` using `D.host.galois`. Establish `hpZ : Prime (p : ℤ)` using `Nat.prime_iff_prime_int.mp hp`. Establish `: (Ideal.span {(p : ℤ)}).IsPrime` using `(Ideal.span_singleton_prime hpZ.ne_zero).mpr hpZ`. Establish `hne` using `Ideal.ramificationIdxIn_ne_zero (B := 𝓞 D.host.E) (D.host.E ≃ₐ[ℚ] D.host.E) (p := Ideal.span {(p : ℤ)})`. Rewrite using `[← not_iff_not, NumberField.not_dvd_discr_iff_isUnramifiedIn D.host.E (𝓞 D.host.E) hpZ, Algebra.isUnramifiedIn_iff_forall_ramificationIdx_eq_one]`.

Prove the components needed by the constructor for the conclusion. Introduce `H`. Take `⟨P, hP⟩` from `(inferInstance : Nonempty (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 D.host.E)))`. Use `hP.1` as an intermediate fact. Use `hP.2` as an intermediate fact.

Rewrite using `[Ideal.ramificationIdxIn_eq_ramificationIdx (Ideal.span {(p : ℤ)}) P (D.host.E ≃ₐ[ℚ] D.host.E), H P hP.2]`. Use linear arithmetic over natural numbers and integers. Introduce `H P _ hlo`. Rewrite `H`, `hne` using `[Ideal.ramificationIdxIn_eq_ramificationIdx (Ideal.span {(p : ℤ)}) P (D.host.E ≃ₐ[ℚ] D.host.E)]`. Use linear arithmetic over natural numbers and integers.
-/
theorem jnt_dvd_discr_iff_ram (D : D7) (p : ℕ) (hp : p.Prime) :
    ((p : ℤ) ∣ discr D.host.E) ↔ 1 < (Ideal.span {(p : ℤ)}).ramificationIdxIn (𝓞 D.host.E) := by
  have : IsGalois ℚ D.host.E := D.host.galois
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have : (Ideal.span {(p : ℤ)}).IsPrime := (Ideal.span_singleton_prime hpZ.ne_zero).mpr hpZ
  have hne := Ideal.ramificationIdxIn_ne_zero (B := 𝓞 D.host.E) (D.host.E ≃ₐ[ℚ] D.host.E)
    (p := Ideal.span {(p : ℤ)})
  rw [← not_iff_not, NumberField.not_dvd_discr_iff_isUnramifiedIn D.host.E (𝓞 D.host.E) hpZ,
    Algebra.isUnramifiedIn_iff_forall_ramificationIdx_eq_one]
  constructor
  · intro H
    obtain ⟨P, hP⟩ := (inferInstance : Nonempty (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 D.host.E)))
    have := hP.1; have := hP.2
    rw [Ideal.ramificationIdxIn_eq_ramificationIdx (Ideal.span {(p : ℤ)}) P (D.host.E ≃ₐ[ℚ] D.host.E),
      H P hP.2]
    omega
  · intro H P _ hlo
    rw [Ideal.ramificationIdxIn_eq_ramificationIdx (Ideal.span {(p : ℤ)}) P
      (D.host.E ≃ₐ[ℚ] D.host.E)] at H hne
    omega

/- English proof (translation)
Take `⟨hCM, hdeg, hram, -, -, -, hrd⟩` from `h`. Conclude with `⟨hCM, hdeg, fun p hp => (jnt_dvd_discr_iff_ram D p hp).trans (hram p hp), D.host.der.norm_mu, D.host.der.unramEF, fun p hp hd P hP hl h => D.host.der.decompConj p hp hd P h, hrd.symm⟩`.
-/
theorem _root_.Formalism.MainNotions.ZetaZeroFreeRegion.first_hypothesis_of_lifting (D : D7) (h : Formalism.MainNotions.UnusedSlot33.Conclusion1 D) : Formalism.MainNotions.ZetaZeroFreeRegion.adm1 D := by
  obtain ⟨hCM, hdeg, hram, -, -, -, hrd⟩ := h
  exact ⟨hCM, hdeg, fun p hp => (jnt_dvd_discr_iff_ram D p hp).trans (hram p hp),
    D.host.der.norm_mu, D.host.der.unramEF,
    fun p hp hd P hP hl h => D.host.der.decompConj p hp hd P h, hrd.symm⟩

/- English proof (translation)
Conclude with `Nat.Coprime.pow_right e ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr (by omega)).symm`.
-/
theorem jnt_coprime_pow {q : ℕ} (hq : q % 8 = 3) (e : ℕ) : Nat.Coprime q (2 ^ e) := by
  exact Nat.Coprime.pow_right e ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr (by omega)).symm

/- English proof (translation)
Conclude with `Nat.Coprime.pow_right e ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr (by omega)).symm`.
-/
theorem jnt_coprime_pow' {d : ℕ} (hd : d % 16 = 7) (e : ℕ) : Nat.Coprime d (2 ^ e) := by
  exact Nat.Coprime.pow_right e ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr (by omega)).symm

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem jnt_iner_eq (D : D7) : Formalism.MainNotions.ZetaZeroFreeRegion.iner D = (((1 : ℤˣ), (-1 : ℤˣ)), 1) := by
  rfl

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun p hp hd P hP hl σ hσ => D.host.der.decomp_typeI p hp hd P σ hσ, fun P hP hl σ => by rw [jnt_iner_eq]; exact D.host.der.inertia_d P σ⟩`.
-/
theorem _root_.Formalism.MainNotions.ZetaZeroFreeRegion.subgroup_admissible_holds (D : D7) : Formalism.MainNotions.ZetaZeroFreeRegion.adm3 D :=
  ⟨fun p hp hd P hP hl σ hσ => D.host.der.decomp_typeI p hp hd P σ hσ,
    fun P hP hl σ => by rw [jnt_iner_eq]; exact D.host.der.inertia_d P σ⟩

/- English proof (translation)
Conclude with `Formalism.MainNotions.ZetaZeroFreeRegion.subgroup_admissible_holds D`.
-/
theorem _root_.Formalism.MainNotions.ZetaZeroFreeRegion.integrality_of_commutation (D : D7)
    (_h : Formalism.MainNotions.UnusedSlot33.Conclusion1 D ∧ Formalism.MainNotions.UnusedSlot33.Conclusion2 D ∧ Formalism.MainNotions.UnusedSlot33.PointsLemma D) : Formalism.MainNotions.ZetaZeroFreeRegion.adm3 D := by
  exact Formalism.MainNotions.ZetaZeroFreeRegion.subgroup_admissible_holds D

open IsDedekindDomain TensorProduct Formalism.MainNotions.UnusedSlot33 in

def StabLink (D : D7) (u : D.what₂.Word) : Prop :=
  ∀ c : (D.mem u).C.cls 0,
  ∃ σ : D.host.E →ₐ[D.host.F] D.host.E, (∀ x, σ x = D.host.conj x) ∧
  ∃ J : Matrix (Fin D.R.k) (Fin D.R.k) D.host.E, IsHerm (σ : D.host.E →+* D.host.E) J ∧ IsDef σ J ∧
  ∃ g : ℕ, g.Prime ∧ 2 * D.R.f * D.R.k < g - 1 ∧
  ∃ v : HeightOneSpectrum (𝓞 D.host.F), ((g : 𝓞 D.host.F) ∈ v.asIdeal) ∧
  letI := tensTop (F := D.host.F) (E := D.host.E) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)
  letI := tensTop (F := D.host.F) (E := D.host.E) (v.adicCompletion D.host.F)
  ∃ U : Subgroup (GL (Fin D.R.k) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)),
    U ≤ UPts σ J (FiniteAdeleRing (𝓞 D.host.F) D.host.F) ∧
    IsCompact (U : Set (GL (Fin D.R.k) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F))) ∧
    IsOpen {x : UPts σ J (FiniteAdeleRing (𝓞 D.host.F) D.host.F) | (x : GL _ _) ∈ U} ∧
  ∃ Uw : Subgroup (GL (Fin D.R.k) (D.host.E ⊗[D.host.F] v.adicCompletion D.host.F)),
    IsProG g Uw ∧ (∀ w ∈ U, bc (prV v) w ∈ Uw) ∧
  ∃ y ∈ UPts σ J (FiniteAdeleRing (𝓞 D.host.F) D.host.F),
  ∃ ι : (D.mem u).C.stab 0 c →*
      ↥(ratPts σ J (FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊓ U.map (MulAut.conj y).toMonoidHom),
    Function.Injective ι

open IsDedekindDomain in

/- English proof (translation)
Introduce `c`. Take `⟨σ, hσ, J, hJ, hdef, g, hg, hgk, v, hv, U, hU, hUc, hUo, Uw, hUw, hUv, y, hy, ι, hι⟩` from `hl c`. Establish `hbot` using `h σ hσ J hJ hdef g hg hgk v hv U hU hUc hUo Uw hUw hUv y hy`. Establish `hsub : Subsingleton ↥(Formalism.MainNotions.UnusedSlot33.ratPts σ J (FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊓ U.map (MulAut.conj y).toMonoidHom)`. Rewrite using `[hbot]`.

Use `infer_instance`. Conclude with `⟨fun a b => hι (Subsingleton.elim _ _)⟩`.
-/
theorem stabZero_of (D : D7) (u : D.what₂.Word) (h : Formalism.MainNotions.UnusedSlot33.division_rows_rational_lattice D) (hl : StabLink D u) :
    (D.mem u).C.StabZero := by
  intro c
  obtain ⟨σ, hσ, J, hJ, hdef, g, hg, hgk, v, hv, U, hU, hUc, hUo, Uw, hUw, hUv, y, hy, ι, hι⟩ := hl c
  have hbot := h σ hσ J hJ hdef g hg hgk v hv U hU hUc hUo Uw hUw hUv y hy
  have hsub : Subsingleton ↥(Formalism.MainNotions.UnusedSlot33.ratPts σ J (FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊓
      U.map (MulAut.conj y).toMonoidHom) := by
    rw [hbot]; infer_instance
  exact ⟨fun a b => hι (Subsingleton.elim _ _)⟩

section DlogL

open DirichletCharacter
open scoped ComplexConjugate

/- English proof (translation)
Establish `ha0 : a ≠ 0`. Introduce and unpack `rfl`. Rewrite `ha` using `[Nat.coprime_zero_left]`. Conclude with `hdp.one_lt.ne' ha`. Establish `hdodd : _root_.Odd d` using `Nat.odd_iff.mpr (by omega)`.

Establish `hkron2 : kron2 (-(d : ℤ)) = 1`. Unfold `kron2`. Establish `h1 : (-(d : ℤ)) % 2 = 1` using `by omega`. Establish `h2 : (-(d : ℤ)) % 8 = 1` using `by omega`. Simplify using `[h1, h2]`.

Unfold `kronSym`. Rewrite using `[hkron2, one_pow, mul_one]`. Establish `hsplit : 2 ^ a.factorization 2 * (a / 2 ^ a.factorization 2) = a` using `Nat.ordProj_mul_ordCompl_eq_self a 2`. Establish `hodd : _root_.Odd (a / 2 ^ a.factorization 2)` using `Nat.coprime_two_left.mp (Nat.coprime_ordCompl Nat.prime_two ha0)`. Generalize the expression as in `a / 2 ^ a.factorization 2 = a' at hsplit hodd ⊢`.

Generalize the expression as in `a.factorization 2 = v at hsplit`. Substitute `hsplit` using the available equality. Establish `h2 : jacobiSym 2 d = 1`. Rewrite using `[jacobiSym.at_two hdodd, ZMod.χ₈_nat_eq_if_mod_eight]`. Establish `: d % 2 = 1` using `by omega`.

Establish `: d % 8 = 7` using `by omega`. Simplify using `[*]`. Use `push_cast`. Rewrite using `[jacobiSym.mul_left, jacobiSym.pow_left, h2, one_pow, one_mul, neg_eq_neg_one_mul, jacobiSym.mul_left, jacobiSym.at_neg_one hodd]`. Break down `Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hodd) with h1 | h3` into its components or cases.

Rewrite using `[ZMod.χ₄_nat_one_mod_four h1, jacobiSym.quadratic_reciprocity_one_mod_four' hdodd h1]`. Simplify using the standard rewrite rules. Rewrite using `[ZMod.χ₄_nat_three_mod_four h3, jacobiSym.quadratic_reciprocity_three_mod_four (by omega : d % 4 = 3) h3]`. Simplify using the standard rewrite rules.
-/
theorem jnt_kron_eq (d a : ℕ) (hdp : d.Prime) (hd : d % 16 = 7) (ha : a.Coprime d) :
    kronSym (-(d : ℤ)) a = jacobiSym (a : ℤ) d := by
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [Nat.coprime_zero_left] at ha
    exact hdp.one_lt.ne' ha
  have hdodd : _root_.Odd d := Nat.odd_iff.mpr (by omega)
  have hkron2 : kron2 (-(d : ℤ)) = 1 := by
    unfold kron2
    have h1 : (-(d : ℤ)) % 2 = 1 := by omega
    have h2 : (-(d : ℤ)) % 8 = 1 := by omega
    simp [h1, h2]
  unfold kronSym
  rw [hkron2, one_pow, mul_one]
  have hsplit : 2 ^ a.factorization 2 * (a / 2 ^ a.factorization 2) = a :=
    Nat.ordProj_mul_ordCompl_eq_self a 2
  have hodd : _root_.Odd (a / 2 ^ a.factorization 2) :=
    Nat.coprime_two_left.mp (Nat.coprime_ordCompl Nat.prime_two ha0)
  generalize a / 2 ^ a.factorization 2 = a' at hsplit hodd ⊢
  generalize a.factorization 2 = v at hsplit
  subst hsplit
  have h2 : jacobiSym 2 d = 1 := by
    rw [jacobiSym.at_two hdodd, ZMod.χ₈_nat_eq_if_mod_eight]
    have : d % 2 = 1 := by omega
    have : d % 8 = 7 := by omega
    simp [*]
  push_cast
  rw [jacobiSym.mul_left, jacobiSym.pow_left, h2, one_pow, one_mul,
    neg_eq_neg_one_mul, jacobiSym.mul_left, jacobiSym.at_neg_one hodd]
  rcases Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hodd) with h1 | h3
  · rw [ZMod.χ₄_nat_one_mod_four h1, jacobiSym.quadratic_reciprocity_one_mod_four' hdodd h1]
    simp
  · rw [ZMod.χ₄_nat_three_mod_four h3,
      jacobiSym.quadratic_reciprocity_three_mod_four (by omega : d % 4 = 3) h3]
    simp

/- English proof (translation)
Establish `: Fact D.host.d.Prime` using `⟨D.host.hyp.2.1⟩`. Unfold `chDir kron chiK`. Rewrite using `[MulChar.ringHomComp_apply, jnt_kron_eq _ _ D.host.hyp.2.1 D.host.hyp.2.2.2.1 ha, ← jacobiSym.legendreSym.to_jacobiSym]`. Simplify using `[legendreSym]`.
-/
theorem jnt_chDir_eq_chiK (D : D7) (a : ℕ) (ha : a.Coprime D.host.d) :
    chDir D.host.d a = chiK D (a : ZMod D.host.d) := by
  have : Fact D.host.d.Prime := ⟨D.host.hyp.2.1⟩
  unfold chDir kron chiK
  rw [MulChar.ringHomComp_apply, jnt_kron_eq _ _ D.host.hyp.2.1 D.host.hyp.2.2.2.1 ha,
    ← jacobiSym.legendreSym.to_jacobiSym]
  simp [legendreSym]

/- English proof (translation)
Establish `: Fact D.host.d.Prime` using `⟨D.host.hyp.2.1⟩`. Introduce `h`. Establish `hd2 : D.host.d ≠ 2` using `by have := D.host.hyp.2.2.2.1; omega`. Take `⟨a, ha⟩` from `quadraticChar_exists_neg_one (F := ZMod D.host.d) (by rw [ZMod.ringChar_zmod_n]; exact hd2)`. Establish `ha0 : a ≠ 0` using `by rintro rfl; simp at ha`.

Use `congrArg (fun χ : DirichletCharacter ℂ D.host.d => χ a) h` as an intermediate fact. Simplify using `only [chiK, MulChar.ringHomComp_apply, ha, MulChar.one_apply (Ne.isUnit ha0)] at this`. Evaluate the numerical expressions using `at this`.
-/
theorem jnt_chiK_ne_one (D : D7) : chiK D ≠ 1 := by
  have : Fact D.host.d.Prime := ⟨D.host.hyp.2.1⟩
  intro h
  have hd2 : D.host.d ≠ 2 := by have := D.host.hyp.2.2.2.1; omega
  obtain ⟨a, ha⟩ := quadraticChar_exists_neg_one (F := ZMod D.host.d)
    (by rw [ZMod.ringChar_zmod_n]; exact hd2)
  have ha0 : a ≠ 0 := by rintro rfl; simp at ha
  have := congrArg (fun χ : DirichletCharacter ℂ D.host.d => χ a) h
  simp only [chiK, MulChar.ringHomComp_apply, ha, MulChar.one_apply (Ne.isUnit ha0)] at this
  norm_num at this

/- English proof (translation)
Establish `: NeZero D.host.d` using `⟨D.host.hyp.2.1.ne_zero⟩`. Rewrite using `[isPrimitive_def]`. Break down `(Nat.Prime.eq_one_or_self_of_dvd D.host.hyp.2.1 _ (conductor_dvd_level (chiK D))) with h | h` into its components or cases. Conclude with `absurd (eq_one_iff_conductor_eq_one.mpr h) (jnt_chiK_ne_one D)`. Conclude with `h`.
-/
theorem jnt_chiK_prim (D : D7) : (chiK D).IsPrimitive := by
  have : NeZero D.host.d := ⟨D.host.hyp.2.1.ne_zero⟩
  rw [isPrimitive_def]
  rcases (Nat.Prime.eq_one_or_self_of_dvd D.host.hyp.2.1 _ (conductor_dvd_level (chiK D))) with h | h
  · exact absurd (eq_one_iff_conductor_eq_one.mpr h) (jnt_chiK_ne_one D)
  · exact h

/- English proof (translation)
Simplify using `[chiK, MulChar.ringHomComp_apply]`.
-/
theorem jnt_chiK_real (D : D7) (a : ZMod D.host.d) : conj (chiK D a) = chiK D a := by
  simp [chiK, MulChar.ringHomComp_apply]

/- English proof (translation)
Establish `hf : Differentiable ℂ (LFunction χ)` using `differentiable_LFunction hχ`. Set `g : ℂ → ℂ` to `conj ∘ LFunction χ ∘ conj`. Establish `hg : Differentiable ℂ g` using `fun z => by`. Use `(hf (conj z)).conj_conj` as an intermediate fact. Simplify `this` using `[g]`.

Establish `hreal : ∀ t : ℝ, 1 < t → LFunction χ t = g t`. Introduce `t ht`. Simplify using `only [g, Function.comp, Complex.conj_ofReal]`. Rewrite using `[LFunction_eq_LSeries χ (by simpa using ht)]`. Unfold `LSeries`.

Rewrite using `[Complex.conj_tsum]`. Use `congr 1`. Use function extensionality and compare the values at `n`. Unfold `LSeries.term`. Use `split_ifs`.

Simplify using the standard rewrite rules. Rewrite using `[map_div₀, hr, ← Complex.ofReal_natCast, ← Complex.ofReal_cpow (Nat.cast_nonneg _), Complex.conj_ofReal]`. Establish `heq : Set.EqOn (LFunction χ) g Set.univ`. Apply `AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq (z₀ := 2) (fun z _ => hf.analyticAt z) (fun z _ => hg.analyticAt z) isPreconnected_univ (Set.mem_univ _)` to reduce the goal to its premises. Set `u : ℕ → ℂ` to `fun n => ((2 + 1 / ((n : ℝ) + 1) : ℝ) : ℂ)`.

Establish `hpos : ∀ n : ℕ, (0 : ℝ) < 1 / ((n : ℝ) + 1)` using `fun n => by positivity`. Establish `hu : Filter.Tendsto u Filter.atTop (nhdsWithin 2 {2}ᶜ)`. Rewrite using `[tendsto_nhdsWithin_iff]`. Prove the components needed by the constructor for the conclusion. Establish `h0 : Filter.Tendsto (fun n : ℕ => (2 : ℝ) + 1 / ((n : ℝ) + 1)) Filter.atTop (nhds (2 + 0))` using `tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat`.

Rewrite `h0` using `[add_zero]`. Establish `h1` using `(Complex.continuous_ofReal.tendsto 2).comp h0`. Establish `h2 : ((2 : ℝ) : ℂ) = 2` using `by norm_num`. Rewrite `h1` using `[h2]`. Conclude with `h1`.

Use `Filter.Eventually.of_forall (fun n => ?_)` and prove the remaining obligations. Simplify using `only [u, Set.mem_compl_iff, Set.mem_singleton_iff]`. Introduce `h2`. Establish `h3` using `congrArg Complex.re h2`. Simplify using `only [Complex.ofReal_re, Complex.re_ofNat] at h3`.

Combine the linear relations using `[hpos n]`. Apply `hu.frequently` to reduce the goal to its premises. Use `Filter.Eventually.frequently (Filter.Eventually.of_forall (fun n => ?_))` and prove the remaining obligations. Conclude with `hreal _ (by linarith [hpos n])`. Use `heq (Set.mem_univ (conj s))` as an intermediate fact.

Simplify `this` using `[g]`.
-/
theorem jnt_LFunction_conj {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (hr : ∀ a, conj (χ a) = χ a) (s : ℂ) :
    LFunction χ (conj s) = conj (LFunction χ s) := by
  have hf : Differentiable ℂ (LFunction χ) := differentiable_LFunction hχ
  let g : ℂ → ℂ := conj ∘ LFunction χ ∘ conj
  have hg : Differentiable ℂ g := fun z => by
    have := (hf (conj z)).conj_conj
    simpa [g] using this
  have hreal : ∀ t : ℝ, 1 < t → LFunction χ t = g t := by
    intro t ht
    simp only [g, Function.comp, Complex.conj_ofReal]
    rw [LFunction_eq_LSeries χ (by simpa using ht)]
    unfold LSeries
    rw [Complex.conj_tsum]
    congr 1
    funext n
    unfold LSeries.term
    split_ifs
    · simp
    · rw [map_div₀, hr, ← Complex.ofReal_natCast, ← Complex.ofReal_cpow (Nat.cast_nonneg _),
        Complex.conj_ofReal]
  have heq : Set.EqOn (LFunction χ) g Set.univ := by
    apply AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq (z₀ := 2)
      (fun z _ => hf.analyticAt z) (fun z _ => hg.analyticAt z) isPreconnected_univ (Set.mem_univ _)
    let u : ℕ → ℂ := fun n => ((2 + 1 / ((n : ℝ) + 1) : ℝ) : ℂ)
    have hpos : ∀ n : ℕ, (0 : ℝ) < 1 / ((n : ℝ) + 1) := fun n => by positivity
    have hu : Filter.Tendsto u Filter.atTop (nhdsWithin 2 {2}ᶜ) := by
      rw [tendsto_nhdsWithin_iff]
      constructor
      · have h0 : Filter.Tendsto (fun n : ℕ => (2 : ℝ) + 1 / ((n : ℝ) + 1)) Filter.atTop
            (nhds (2 + 0)) := tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat
        rw [add_zero] at h0
        have h1 := (Complex.continuous_ofReal.tendsto 2).comp h0
        have h2 : ((2 : ℝ) : ℂ) = 2 := by norm_num
        rw [h2] at h1
        exact h1
      · refine Filter.Eventually.of_forall (fun n => ?_)
        simp only [u, Set.mem_compl_iff, Set.mem_singleton_iff]
        intro h2
        have h3 := congrArg Complex.re h2
        simp only [Complex.ofReal_re, Complex.re_ofNat] at h3
        linarith [hpos n]
    apply hu.frequently
    refine Filter.Eventually.frequently (Filter.Eventually.of_forall (fun n => ?_))
    exact hreal _ (by linarith [hpos n])
  have := heq (Set.mem_univ (conj s))
  simpa [g] using this

/- English proof (translation)
Establish `hc` using `jnt_LFunction_conj χ hχ hr`. Establish `hfun : (conj ∘ LFunction χ ∘ conj) = LFunction χ` using `funext fun s => by simp [hc]`. Establish `hd : HasDerivAt (LFunction χ) (deriv (LFunction χ) 1) 1` using `(differentiable_LFunction hχ 1).hasDerivAt`. Establish `hd2` using `hd.conj_conj`. Rewrite `hd2` using `[hfun, map_one]`.

Establish `hde : deriv (LFunction χ) 1 = conj (deriv (LFunction χ) 1)` using `hd.unique hd2`. Establish `hL1 : LFunction χ 1 = conj (LFunction χ 1)` using `by simpa using hc 1`. Establish `hz : conj (logDerivativeAtOne χ) = logDerivativeAtOne χ`. Unfold `logDerivativeAtOne`. Rewrite using `[map_div₀, ← hde, ← hL1]`.

Conclude with `Complex.conj_eq_iff_im.mp hz`.
-/
theorem log_deriv_L_one_real_im_eq_zero {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (hr : ∀ a, conj (χ a) = χ a) : (logDerivativeAtOne χ).im = 0 := by
  have hc := jnt_LFunction_conj χ hχ hr
  have hfun : (conj ∘ LFunction χ ∘ conj) = LFunction χ := funext fun s => by simp [hc]
  have hd : HasDerivAt (LFunction χ) (deriv (LFunction χ) 1) 1 :=
    (differentiable_LFunction hχ 1).hasDerivAt
  have hd2 := hd.conj_conj
  rw [hfun, map_one] at hd2
  have hde : deriv (LFunction χ) 1 = conj (deriv (LFunction χ) 1) := hd.unique hd2
  have hL1 : LFunction χ 1 = conj (LFunction χ 1) := by simpa using hc 1
  have hz : conj (logDerivativeAtOne χ) = logDerivativeAtOne χ := by
    unfold logDerivativeAtOne
    rw [map_div₀, ← hde, ← hL1]
  exact Complex.conj_eq_iff_im.mp hz

/- English proof (translation)
Establish `: Fact D.host.d.Prime` using `⟨D.host.hyp.2.1⟩`. Establish `: NeZero D.host.d` using `⟨D.host.hyp.2.1.ne_zero⟩`. Establish `: NeZero (N * (M * D.host.d))` using `⟨mul_ne_zero (NeZero.ne N) (mul_ne_zero hM (NeZero.ne _))⟩`. Establish `hN1 : N ∣ N * (M * D.host.d)` using `Dvd.intro _ rfl`. Establish `hd1 : D.host.d ∣ N * (M * D.host.d)` using `Dvd.dvd.mul_left (Dvd.intro_left M rfl) N`.

Establish `hM1 : M ∣ N * (M * D.host.d)` using `Dvd.dvd.mul_left (Dvd.intro _ rfl) N`. Establish `hch : changeLevel hN1 χ = changeLevel hd1 (chiK D)`. Use extensionality with `u`. Establish `hcop : Nat.Coprime (u : ZMod (N * (M * D.host.d))).val (N * (M * D.host.d))` using `ZMod.val_coe_unit_coprime u`. Establish `hu : (((u : ZMod (N * (M * D.host.d))).val : ℤ) : ZMod (N * (M * D.host.d))) = u`.

Simplify using the standard rewrite rules. Establish `hic : IsCoprime ((u : ZMod (N * (M * D.host.d))).val : ℤ) (N * (M * D.host.d) : ℕ)` using `Nat.isCoprime_iff_coprime.mpr hcop`. Rewrite using `[← hu, changeLevel_eq_cast_of_dvd' _ _ hic, changeLevel_eq_cast_of_dvd' _ _ hic]`. Simplify using `only [Int.cast_natCast]`. Rewrite using `[h.2 _ (Nat.Coprime.coprime_dvd_right hM1 hcop), jnt_chDir_eq_chiK D _ (Nat.Coprime.coprime_dvd_right hd1 hcop)]`.

Establish `hc` using `congrArg conductor hch`. Rewrite `hc` using `[conductor_changeLevel, conductor_changeLevel]`. Establish `hN : N = D.host.d`. Rewrite using `[← (show χ.conductor = N from h.1), hc, (show (chiK D).conductor = D.host.d from jnt_chiK_prim D)]`. Substitute `hN` using the available equality.

Establish `hχ : χ = chiK D` using `changeLevel_injective hd1 hch`. Substitute `hχ` using the available equality. Apply `Complex.ext` to reduce the goal to its premises. Simplify using `[dlogL]`. Both sides reduce to the same expression.

Simplify using `only [Complex.ofReal_im]`. Conclude with `log_deriv_L_one_real_im_eq_zero _ (jnt_chiK_ne_one D) (jnt_chiK_real D)`.
-/
theorem log_deriv_L_one_eq_of_induces (D : D7) (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (M : ℕ)
    (hM : M ≠ 0) (h : Induces χ (chDir D.host.d) M) :
    logDerivativeAtOne χ = ((dlogL D 1 : ℝ) : ℂ) := by
  have : Fact D.host.d.Prime := ⟨D.host.hyp.2.1⟩
  have : NeZero D.host.d := ⟨D.host.hyp.2.1.ne_zero⟩
  have : NeZero (N * (M * D.host.d)) := ⟨mul_ne_zero (NeZero.ne N) (mul_ne_zero hM (NeZero.ne _))⟩
  have hN1 : N ∣ N * (M * D.host.d) := Dvd.intro _ rfl
  have hd1 : D.host.d ∣ N * (M * D.host.d) := Dvd.dvd.mul_left (Dvd.intro_left M rfl) N
  have hM1 : M ∣ N * (M * D.host.d) := Dvd.dvd.mul_left (Dvd.intro _ rfl) N
  have hch : changeLevel hN1 χ = changeLevel hd1 (chiK D) := by
    ext u
    have hcop : Nat.Coprime (u : ZMod (N * (M * D.host.d))).val (N * (M * D.host.d)) :=
      ZMod.val_coe_unit_coprime u
    have hu : (((u : ZMod (N * (M * D.host.d))).val : ℤ) : ZMod (N * (M * D.host.d))) = u := by
      simp
    have hic : IsCoprime ((u : ZMod (N * (M * D.host.d))).val : ℤ) (N * (M * D.host.d) : ℕ) :=
      Nat.isCoprime_iff_coprime.mpr hcop
    rw [← hu, changeLevel_eq_cast_of_dvd' _ _ hic, changeLevel_eq_cast_of_dvd' _ _ hic]
    simp only [Int.cast_natCast]
    rw [h.2 _ (Nat.Coprime.coprime_dvd_right hM1 hcop),
      jnt_chDir_eq_chiK D _ (Nat.Coprime.coprime_dvd_right hd1 hcop)]
  have hc := congrArg conductor hch
  rw [conductor_changeLevel, conductor_changeLevel] at hc
  have hN : N = D.host.d := by
    rw [← (show χ.conductor = N from h.1), hc, (show (chiK D).conductor = D.host.d from jnt_chiK_prim D)]
  subst hN
  have hχ : χ = chiK D := changeLevel_injective hd1 hch
  subst hχ
  apply Complex.ext
  · simp [dlogL]; rfl
  · simp only [Complex.ofReal_im]
    exact log_deriv_L_one_real_im_eq_zero _ (jnt_chiK_ne_one D) (jnt_chiK_real D)

/- English proof (translation)
Establish `h2 : 2 ∣ D.host.QS` using `(dvd_pow_self 2 (by omega)).trans D.host.tower_dvd`. Establish `hqd : D.host.q * D.host.d ≠ 0`. Introduce `h0`. Establish `hc` using `D.host.QS_coprime`. Rewrite `hc` using `[h0, Nat.coprime_zero_right]`.

Rewrite `h2` using `[hc]`. Use linear arithmetic over natural numbers and integers. Conclude with `log_deriv_L_one_eq_of_induces D N χ (2 * D.host.d) (Nat.mul_ne_zero (by norm_num) (right_ne_zero_of_mul hqd)) h`.
-/
theorem log_deriv_L_one_eq_quadratic (D : D7) (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N)
    (h : Induces χ (chDir D.host.d) (2 * D.host.d)) :
    logDerivativeAtOne χ = ((dlogL D 1 : ℝ) : ℂ) := by
  have h2 : 2 ∣ D.host.QS := (dvd_pow_self 2 (by omega)).trans D.host.tower_dvd
  have hqd : D.host.q * D.host.d ≠ 0 := by
    intro h0
    have hc := D.host.QS_coprime
    rw [h0, Nat.coprime_zero_right] at hc
    rw [hc] at h2
    omega
  exact log_deriv_L_one_eq_of_induces D N χ (2 * D.host.d) (Nat.mul_ne_zero (by norm_num) (right_ne_zero_of_mul hqd)) h

/- English proof (translation)
Rewrite using `[L.logDerivative_at_one_eq]`. Conclude with `log_deriv_L_one_eq_quadratic D N χ h`.
-/
theorem logDerivativeAtOne_eq_of_induces (D : D7) (L : SizeData₂ D) (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N)
    (h : Induces χ (chDir D.host.d) (2 * D.host.d)) :
    logDerivativeAtOne χ = ((L.logDerivativeAtOne : ℝ) : ℂ) := by
  rw [L.logDerivative_at_one_eq]
  exact log_deriv_L_one_eq_quadratic D N χ h

end DlogL

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem log_deriv_L_one_theta_eq (D : D7) : TaylorLogMetric.logDerivativeAtOne D = dlogL D 1 := rfl

/- English proof (translation)
Introduce `u`. Establish `hlow` using `(h Δ w hB u).1`. Take `⟨hv, -, -, hmk, -, hg, hΔ, -, -, -, -, -, hw, hwb, hb0, -⟩` from `hB`. Establish `hx` using `sc.one_lt_alt`. Establish `hk : (1 : ℝ) ≤ D.R.k`.

Use `D.R.m_add_three_le_k` as an intermediate fact. Conclude with `(by omega : 1 ≤ D.R.k)` after adjusting the coercions. Establish `hbpos : 0 < sc.b` using `Real.exp_pos _`. Establish `hXu : Real.log (D.mem u).A.Xu = StandardLattice.logXuD D u`. Unfold `ColumnsAtT.Xu StandardLattice.logXuD StandardLattice.logXu`.

Rewrite using `[Real.log_rpow (div_pos (D.mem u).A.Dstar_pos (by exact_mod_cast (D.mem u).A.duStar_pos)), D.Dstar_eq u, hDs, hDu u]`. Establish `hb : ∀ ρ j, j < D.R.m → 4 ≤ StandardLattice.bN D ρ j`. Introduce `ρ j`. Proceed by induction on `j with`. Consider the case `zero`.

Introduce `_`. Establish `h1` using `(hb0 ρ).1`. Rewrite `h1` using `[le_div_iff₀ (by linarith)]`. Establish `hΔ' : (1 : ℝ) ≤ Δ` using `hΔ`. Establish `h4 : (4 : ℝ) ≤ (D.R.k : ℝ) * (4 * Δ)` using `by nlinarith`.

Establish `h5 : (4 : ℝ) * 1 ≤ (D.R.k : ℝ) * (4 * Δ) * sc.x` using `mul_le_mul h4 hx.le zero_le_one (by linarith)`. Combine the linear equalities and inequalities to obtain the conclusion. Consider the case `succ j ih`. Introduce `hj`. Establish `h1` using `ih (by omega)`.

Establish `h2` using `(hw ρ j (by omega)).2.1`. Establish `h3` using `hwb ρ j hj`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `ht1 : 0 ≤ ∑ j ∈ Finset.range D.R.m, (1 / (D.R.f : ℝ)) * ∑ ρ, Real.log (w j ρ * D.host.v / Real.pi)`. Apply `Finset.sum_nonneg` to reduce the goal to its premises.

Introduce `j hj`. Apply `mul_nonneg (by positivity)` to reduce the goal to its premises. Apply `Finset.sum_nonneg` to reduce the goal to its premises. Introduce `ρ _`. Apply `Real.log_nonneg` to reduce the goal to its premises.

Rewrite using `[le_div_iff₀ Real.pi_pos]`. Establish `h1` using `(hw ρ j (Finset.mem_range.mp hj)).2.1`. Establish `h2` using `hb ρ j (Finset.mem_range.mp hj)`. Conclude with `mul_le_mul (by linarith) hv Real.pi_pos.le (by linarith)`. Establish `hgi : ∀ i, 8 * sc.L ≤ Real.log (D.host.g i)`.

Introduce `i`. Establish `h1` using `(hg i).1`. Establish `hkb : sc.b ≤ (D.R.k : ℝ) * sc.b` using `by nlinarith`. Establish `h2 : Real.log (((D.R.k : ℝ) * sc.b) ^ 8) ≤ Real.log (D.host.g i)` using `Real.log_le_log (pow_pos (mul_pos (by linarith) hbpos) 8) h1`. Rewrite `h2` using `[Real.log_pow]`.

Establish `h3 : sc.L ≤ Real.log ((D.R.k : ℝ) * sc.b)`. Use `Real.log_le_log hbpos hkb` as an intermediate fact. Rewrite `this` using `[show sc.b = Real.exp sc.L from rfl, Real.log_exp]`. Then use the resulting hypothesis. Move the coercions through the operations in `at h2`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hLpos : 0 < sc.L` using `Real.rpow_pos_of_pos (by linarith) _`. Establish `hm0 : 0 ≤ (D.R.m : ℝ)` using `Nat.cast_nonneg _`. Establish `ht3 : C * (sc.L + (D.R.m : ℝ) ^ 2 * sc.L / D.R.k) ≤ 31 / 2 * D.R.m * sc.L`. Establish `h1 : (D.R.m : ℝ) ^ 2 * sc.L / D.R.k ≤ 1`. Rewrite using `[div_le_one (by linarith)]; exact hmk`.

Establish `h0 : 0 ≤ (D.R.m : ℝ) ^ 2 * sc.L / D.R.k` using `by positivity`. Break down `le_total 0 C with hC0 | hC0` into its components or cases. Conclude with `(mul_le_mul_of_nonneg_left (by linarith) hC0).trans hC`. Conclude with `(mul_nonpos_of_nonpos_of_nonneg hC0 (by linarith)).trans (by positivity)`. Unfold `StandardLattice.lowB at hlow`.

Rewrite `hlow` using `[Fin.sum_univ_two]`. Rewrite using `[hXu]`. Establish `hL : sc.x ^ sc.eps = sc.L` using `rfl`. Rewrite using `[hL]`. Establish `hm : 0 ≤ (D.R.m : ℝ)` using `Nat.cast_nonneg _`.

Establish `h6` using `mul_le_mul_of_nonneg_left (add_le_add (hgi 0) (hgi 1)) hm`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem _root_.Formalism.MainNotions.ShortIntervalPrimes.crystalline_lift_of_theorem_c (D : D7) (sc : Scale) (C0 C : ℝ)
    (h : StandardLattice.Conclusion5 D sc C0 C) (Δ : ℝ) (w : ℕ → D.what₂.Tau → ℝ) (hB : StandardLattice.DataB D sc C0 Δ w)
    (hDu : StandardLattice.FactDuStar D) (hDs : StandardLattice.FactDstar D)
    (hC : C * (sc.L + 1) ≤ 31 / 2 * D.R.m * sc.L) :
    ShortIntervalPrimes.adm9 D sc.x sc.eps := by
  intro u
  have hlow := (h Δ w hB u).1
  obtain ⟨hv, -, -, hmk, -, hg, hΔ, -, -, -, -, -, hw, hwb, hb0, -⟩ := hB
  have hx := sc.one_lt_alt
  have hk : (1 : ℝ) ≤ D.R.k := by
    have := D.R.m_add_three_le_k
    exact_mod_cast (by omega : 1 ≤ D.R.k)
  have hbpos : 0 < sc.b := Real.exp_pos _
  have hXu : Real.log (D.mem u).A.Xu = StandardLattice.logXuD D u := by
    unfold ColumnsAtT.Xu StandardLattice.logXuD StandardLattice.logXu
    rw [Real.log_rpow (div_pos (D.mem u).A.Dstar_pos (by exact_mod_cast (D.mem u).A.duStar_pos)),
      D.Dstar_eq u, hDs, hDu u]
  have hb : ∀ ρ j, j < D.R.m → 4 ≤ StandardLattice.bN D ρ j := by
    intro ρ j
    induction j with
    | zero =>
      intro _
      have h1 := (hb0 ρ).1
      rw [le_div_iff₀ (by linarith)] at h1
      have hΔ' : (1 : ℝ) ≤ Δ := hΔ
      have h4 : (4 : ℝ) ≤ (D.R.k : ℝ) * (4 * Δ) := by nlinarith
      have h5 : (4 : ℝ) * 1 ≤ (D.R.k : ℝ) * (4 * Δ) * sc.x :=
        mul_le_mul h4 hx.le zero_le_one (by linarith)
      linarith
    | succ j ih =>
      intro hj
      have h1 := ih (by omega)
      have h2 := (hw ρ j (by omega)).2.1
      have h3 := hwb ρ j hj
      linarith
  have ht1 : 0 ≤ ∑ j ∈ Finset.range D.R.m,
      (1 / (D.R.f : ℝ)) * ∑ ρ, Real.log (w j ρ * D.host.v / Real.pi) := by
    apply Finset.sum_nonneg
    intro j hj
    apply mul_nonneg (by positivity)
    apply Finset.sum_nonneg
    intro ρ _
    apply Real.log_nonneg
    rw [le_div_iff₀ Real.pi_pos]
    have h1 := (hw ρ j (Finset.mem_range.mp hj)).2.1
    have h2 := hb ρ j (Finset.mem_range.mp hj)
    exact mul_le_mul (by linarith) hv Real.pi_pos.le (by linarith)
  have hgi : ∀ i, 8 * sc.L ≤ Real.log (D.host.g i) := by
    intro i
    have h1 := (hg i).1
    have hkb : sc.b ≤ (D.R.k : ℝ) * sc.b := by nlinarith
    have h2 : Real.log (((D.R.k : ℝ) * sc.b) ^ 8) ≤ Real.log (D.host.g i) :=
      Real.log_le_log (pow_pos (mul_pos (by linarith) hbpos) 8) h1
    rw [Real.log_pow] at h2
    have h3 : sc.L ≤ Real.log ((D.R.k : ℝ) * sc.b) := by
      have := Real.log_le_log hbpos hkb
      rwa [show sc.b = Real.exp sc.L from rfl, Real.log_exp] at this
    push_cast at h2
    linarith
  have hLpos : 0 < sc.L := Real.rpow_pos_of_pos (by linarith) _
  have hm0 : 0 ≤ (D.R.m : ℝ) := Nat.cast_nonneg _
  have ht3 : C * (sc.L + (D.R.m : ℝ) ^ 2 * sc.L / D.R.k) ≤ 31 / 2 * D.R.m * sc.L := by
    have h1 : (D.R.m : ℝ) ^ 2 * sc.L / D.R.k ≤ 1 := by
      rw [div_le_one (by linarith)]; exact hmk
    have h0 : 0 ≤ (D.R.m : ℝ) ^ 2 * sc.L / D.R.k := by positivity
    rcases le_total 0 C with hC0 | hC0
    · exact (mul_le_mul_of_nonneg_left (by linarith) hC0).trans hC
    · exact (mul_nonpos_of_nonpos_of_nonneg hC0 (by linarith)).trans (by positivity)
  unfold StandardLattice.lowB at hlow
  rw [Fin.sum_univ_two] at hlow
  rw [hXu]
  have hL : sc.x ^ sc.eps = sc.L := rfl
  rw [hL]
  have hm : 0 ≤ (D.R.m : ℝ) := Nat.cast_nonneg _
  have h6 := mul_le_mul_of_nonneg_left (add_le_add (hgi 0) (hgi 1)) hm
  linarith

/- English proof (translation)
Set `f : 𝓞 K₁ ≃+* 𝓞 K₂` to `NumberField.RingOfIntegers.mapRingEquiv e`. Establish `himg : (fun P : Ideal (𝓞 K₁) => P.map f) '' (Ideal.primesOver (Ideal.span {p}) (𝓞 K₁)) = Ideal.primesOver (Ideal.span {p}) (𝓞 K₂)`. Use extensionality with `Q`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨P, ⟨hP, hlo⟩, rfl⟩`.

Establish `hPm : (P.map f).IsPrime` using `Ideal.map_isPrime_of_equiv f`. Use `⟨hPm, (Ideal.liesOver_span_iff hPm.ne_top hp).mpr ?_⟩` and prove the remaining obligations. Establish `h1 : ((p : ℤ) : 𝓞 K₁) ∈ P` using `(Ideal.liesOver_span_iff hP.ne_top hp).mp hlo`. Establish `h2` using `Ideal.mem_map_of_mem f h1`. Simplify using `using h2`.

Introduce and unpack `⟨hQ, hlo⟩`. Establish `h1 : ((p : ℤ) : 𝓞 K₂) ∈ Q` using `(Ideal.liesOver_span_iff hQ.ne_top hp).mp hlo`. Establish `hc : (Q.comap f).IsPrime` using `Ideal.comap_isPrime f Q`. Use `⟨Q.comap f, ⟨hc, (Ideal.liesOver_span_iff hc.ne_top hp).mpr ?_⟩, Ideal.map_comap_of_surjective f f.surjective Q⟩` and prove the remaining obligations. Rewrite using `[Ideal.mem_comap]`.

Simplify using `using h1`. Rewrite using `[← himg]`. Conclude with `(Set.ncard_image_of_injective _ (Function.LeftInverse.injective (g := Ideal.comap f) (fun P => Ideal.comap_map_of_bijective f f.bijective))).symm`.
-/
theorem jnt_ncard_primesOver_equiv {K₁ K₂ : Type*} [Field K₁] [NumberField K₁] [Field K₂]
    [NumberField K₂] (e : K₁ ≃+* K₂) (p : ℤ) (hp : Prime p) :
    (Ideal.primesOver (Ideal.span {p}) (𝓞 K₁)).ncard =
      (Ideal.primesOver (Ideal.span {p}) (𝓞 K₂)).ncard := by
  let f : 𝓞 K₁ ≃+* 𝓞 K₂ := NumberField.RingOfIntegers.mapRingEquiv e
  have himg : (fun P : Ideal (𝓞 K₁) => P.map f) '' (Ideal.primesOver (Ideal.span {p}) (𝓞 K₁)) =
      Ideal.primesOver (Ideal.span {p}) (𝓞 K₂) := by
    ext Q
    constructor
    · rintro ⟨P, ⟨hP, hlo⟩, rfl⟩
      have hPm : (P.map f).IsPrime := Ideal.map_isPrime_of_equiv f
      refine ⟨hPm, (Ideal.liesOver_span_iff hPm.ne_top hp).mpr ?_⟩
      have h1 : ((p : ℤ) : 𝓞 K₁) ∈ P := (Ideal.liesOver_span_iff hP.ne_top hp).mp hlo
      have h2 := Ideal.mem_map_of_mem f h1
      simpa using h2
    · rintro ⟨hQ, hlo⟩
      have h1 : ((p : ℤ) : 𝓞 K₂) ∈ Q := (Ideal.liesOver_span_iff hQ.ne_top hp).mp hlo
      have hc : (Q.comap f).IsPrime := Ideal.comap_isPrime f Q
      refine ⟨Q.comap f, ⟨hc, (Ideal.liesOver_span_iff hc.ne_top hp).mpr ?_⟩,
        Ideal.map_comap_of_surjective f f.surjective Q⟩
      rw [Ideal.mem_comap]
      simpa using h1
  rw [← himg]
  exact (Set.ncard_image_of_injective _ (Function.LeftInverse.injective (g := Ideal.comap f)
    (fun P => Ideal.comap_map_of_bijective f f.bijective))).symm

def jnt_KEquiv (D : D7) : D.host.K ≃ₐ[ℚ] Kd (D.host.cycEmb D.host.sqd) :=
  (IntermediateField.equivMap D.host.K D.host.cycEmb).trans
    (IntermediateField.equivOfEq (by
      unfold Formalism.HC.HostRaw.K Kd
      rw [IntermediateField.adjoin_map]
      simp))

/- English proof (translation)
The claim follows from `D.host.splitK_of_dvd hp hd`.
-/
theorem jnt_splitK (D : D7) (p : ℕ) (hp : p.Prime) (hd : p ∣ D.host.QS * D.host.q) :
    (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 D.host.K)).ncard = 2 :=
  D.host.splitK_of_dvd hp hd

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra in
/- English proof (translation)
Establish `hex : ∃ P : Ideal (𝓞 D.host.E), P.IsPrime ∧ P.LiesOver 𝔭`. Assume the negation of the conclusion as `hn`. Rewrite `hr` using `[Ideal.ramificationIdxIn, dif_neg hn]`. Use linear arithmetic over natural numbers and integers. Rewrite `hr` using `[Ideal.ramificationIdxIn, dif_pos hex]`.

Take `⟨hP, hlo⟩` from `hex.choose_spec`. Generalize the expression as in `hex.choose = P at hr hP hlo`. Establish `hdvd : P ∣ differentIdeal (𝓞 D.host.K) (𝓞 D.host.E)`. Assume the negation of the conclusion as `hnd`. Establish `hun` using `not_dvd_differentIdeal_iff.mp hnd`.

Use `Ideal.ramificationIdx_eq_one_iff.mpr hun` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Rewrite using `[Ideal.mem_of_liesOver P 𝔭, map_natCast]`. Conclude with `D.host.der.diffSupport P hP hdvd`.
-/
theorem jnt_ramEK (D : D7) (𝔭 : Ideal (𝓞 D.host.K)) (h𝔭 : 𝔭.IsPrime)
    (hr : 1 < 𝔭.ramificationIdxIn (𝓞 D.host.E)) :
    ((D.host.QS * D.host.q : ℕ) : 𝓞 D.host.K) ∈ 𝔭 := by
  have hex : ∃ P : Ideal (𝓞 D.host.E), P.IsPrime ∧ P.LiesOver 𝔭 := by
    by_contra hn
    rw [Ideal.ramificationIdxIn, dif_neg hn] at hr
    omega
  rw [Ideal.ramificationIdxIn, dif_pos hex] at hr
  obtain ⟨hP, hlo⟩ := hex.choose_spec
  generalize hex.choose = P at hr hP hlo
  have hdvd : P ∣ differentIdeal (𝓞 D.host.K) (𝓞 D.host.E) := by
    by_contra hnd
    have hun := not_dvd_differentIdeal_iff.mp hnd
    have := Ideal.ramificationIdx_eq_one_iff.mpr hun
    omega
  rw [Ideal.mem_of_liesOver P 𝔭, map_natCast]
  exact D.host.der.diffSupport P hP hdvd

/- English proof (translation)
Establish `hlo : P.LiesOver (Ideal.span {(D.host.d : ℤ)})` using `(Ideal.liesOver_span_iff hP.ne_top (Nat.prime_iff_prime_int.mp D.host.hyp.2.1)).mpr (by simpa using hd)`. Use `Iff.trans ?_ (D.host.der.inertia_d P σ)` and prove the remaining obligations. Prove the components needed by the constructor for the conclusion. Introduce `h x`. Take `⟨y, hy, hyx⟩` from `h x`.

Establish `: σ • x - x = y`. Apply `NumberField.RingOfIntegers.ext` to reduce the goal to its premises. Rewrite using `[hyx]`. Both sides reduce to the same expression. Rewrite using `[this]`.

Conclude with `hy`. Introduce `h x`. Conclude with `⟨σ • x - x, h x, rfl⟩`.
-/
theorem jnt_inertiaD (D : D7) (P : Ideal (𝓞 D.host.E)) (hP : P.IsPrime)
    (hd : (D.host.d : 𝓞 D.host.E) ∈ P) (σ : D.host.E ≃ₐ[ℚ] D.host.E) :
    ((∀ x : 𝓞 D.host.E, ∃ y ∈ P, (y : D.host.E) = σ (x : D.host.E) - (x : D.host.E)) ↔
      (D.host.galE σ = 1 ∨
        D.host.galE σ = ((1, -1), 1))) := by
  have hlo : P.LiesOver (Ideal.span {(D.host.d : ℤ)}) :=
    (Ideal.liesOver_span_iff hP.ne_top (Nat.prime_iff_prime_int.mp D.host.hyp.2.1)).mpr
      (by simpa using hd)
  refine Iff.trans ?_ (D.host.der.inertia_d P σ)
  constructor
  · intro h x
    obtain ⟨y, hy, hyx⟩ := h x
    have : σ • x - x = y := by
      apply NumberField.RingOfIntegers.ext
      rw [hyx]
      rfl
    rw [this]
    exact hy
  · intro h x
    exact ⟨σ • x - x, h x, rfl⟩

/- English proof (translation)
Take `⟨-, -, -, -, hun, hsp, -⟩` from `h`. Conclude with `⟨hun, D.host.der.norm_mu, hsp, jnt_splitK D, fun 𝔭 h𝔭 _ hr => jnt_ramEK D 𝔭 h𝔭 hr, fun P hP hd σ => jnt_inertiaD D P hP hd σ⟩`.
-/
theorem _root_.Formalism.MainNotions.TaylorLogMetric.first_hypothesis_of_lifting (D : D7) (h : Formalism.MainNotions.UnusedSlot33.Conclusion1 D) : Formalism.MainNotions.TaylorLogMetric.adm1 D := by
  obtain ⟨-, -, -, -, hun, hsp, -⟩ := h
  exact ⟨hun, D.host.der.norm_mu, hsp, jnt_splitK D, fun 𝔭 h𝔭 _ hr => jnt_ramEK D 𝔭 h𝔭 hr,
    fun P hP hd σ => jnt_inertiaD D P hP hd σ⟩

/- English proof (translation)
Introduce `u c`. Conclude with `stabZero_of D u h (hl u) c`.
-/
theorem _root_.Formalism.MainNotions.flipTwoThree.integrality_of_commutation (D : D7) (h : Formalism.MainNotions.UnusedSlot33.division_rows_rational_lattice D) (hl : ∀ u, StabLink D u) :
    Formalism.MainNotions.flipTwoThree.adm3 D := by
  intro u c
  exact stabZero_of D u h (hl u) c

/- English proof (translation)
Establish `h1 : (4 * D.R.ord : ℝ) ≤ D.host.rdE ^ 2` using `D.host.der.rd_sq_ge`. Establish `h2 : (1 : ℝ) ≤ D.R.ord` using `by exact_mod_cast D.R.ord_pos`. Establish `h3 : 0 ≤ D.host.rdE` using `Real.rpow_nonneg (abs_nonneg _) _`. Establish `h4 : 2 ≤ D.host.rdE`. Assume the negation of the conclusion as `hlt`.

Use `push Not at hlt`. Use the polynomial consequences of the given equalities and inequalities. Unfold `Host.v`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem jnt_one_le_v (D : D7) (_h : Formalism.MainNotions.UnusedSlot33.Conclusion1 D) : 1 ≤ D.host.v := by
  have h1 : (4 * D.R.ord : ℝ) ≤ D.host.rdE ^ 2 := D.host.der.rd_sq_ge
  have h2 : (1 : ℝ) ≤ D.R.ord := by exact_mod_cast D.R.ord_pos
  have h3 : 0 ≤ D.host.rdE := Real.rpow_nonneg (abs_nonneg _) _
  have h4 : 2 ≤ D.host.rdE := by
    by_contra hlt
    push Not at hlt
    nlinarith
  unfold Host.v
  linarith

/- English proof (translation)
Take `⟨hb, hL, _, _, _, hb', hSc, heta, hsum, _, _, _, hdl, hx2, hv1, _⟩` from `h`. Establish `hx0 : (0:ℝ) < x` using `by linarith`. Establish `hmt : (0:ℝ) ≤ D.R.m * D.R.t` using `by positivity`. Establish `h2 : 2 ≤ b' / x` using `by linarith`. Establish `hb'2 : 2 * x ≤ b'` using `(le_div_iff₀ hx0).mp h2`.

Rewrite `hb'` using `[mul_div_cancel_left₀ b hx0.ne']`. Establish `hb1 : 1 ≤ b` using `by linarith`. Establish `hv0 : (0:ℝ) < D.host.v` using `by linarith`. Establish `hlog : Real.log (x * b * D.host.v) = Real.log x + Real.log b + Real.log D.host.v`. Rewrite using `[Real.log_mul (mul_pos hx0 hb).ne' hv0.ne', Real.log_mul hx0.ne' hb.ne']`.

Establish `hlb : 0 ≤ Real.log b` using `Real.log_nonneg hb1`. Establish `hlv : 0 ≤ Real.log D.host.v` using `Real.log_nonneg hv1`. Establish `hlx : 0 ≤ Real.log x` using `Real.log_nonneg (by linarith)`. Establish `hl2 : Real.log 2 ≤ Real.log x` using `Real.log_le_log (by norm_num) hx2`. Conclude with `⟨by linarith, by linarith, by linarith⟩`.
-/
theorem jnt_nums (D : D7) (T g1 g2 : ℕ) (Cn x b Lr b' Sc eta : ℝ) (hx : 1 ≤ x) (hv : 1 ≤ D.host.v)
    (h : Formalism.MainNotions.flipTwoThree.Nums D T g1 g2 Cn x b Lr b' Sc eta) :
    Real.log 2 ≤ Lr ∧ Real.log x ≤ Lr ∧ Real.log D.host.v ≤ Lr := by
  obtain ⟨hb, hL, _, _, _, hb', hSc, heta, hsum, _, _, _, hdl, hx2, hv1, _⟩ := h
  have hx0 : (0:ℝ) < x := by linarith
  have hmt : (0:ℝ) ≤ D.R.m * D.R.t := by positivity
  have h2 : 2 ≤ b' / x := by linarith
  have hb'2 : 2 * x ≤ b' := (le_div_iff₀ hx0).mp h2
  rw [mul_div_cancel_left₀ b hx0.ne'] at hb'
  have hb1 : 1 ≤ b := by linarith
  have hv0 : (0:ℝ) < D.host.v := by linarith
  have hlog : Real.log (x * b * D.host.v) = Real.log x + Real.log b + Real.log D.host.v := by
    rw [Real.log_mul (mul_pos hx0 hb).ne' hv0.ne', Real.log_mul hx0.ne' hb.ne']
  have hlb : 0 ≤ Real.log b := Real.log_nonneg hb1
  have hlv : 0 ≤ Real.log D.host.v := Real.log_nonneg hv1
  have hlx : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hl2 : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx2
  exact ⟨by linarith, by linarith, by linarith⟩

def OmLink (D : D7) (T : Formalism.MainNotions.TaylorLogMetric.Tor D) : Prop :=
  ∃ (M : IntermediateField ℚ ℂ) (_ : NumberField M), Formalism.MainNotions.TaylorLogMetric.DataIn D T M ∧
    ∀ τ, D.gx.logOmMean τ = Formalism.MainNotions.TaylorLogMetric.meanLogOm D T.abelian₂ M τ

/- English proof (translation)
Take `⟨M, hM, hd, h⟩` from `hl`. Rewrite using `[Formalism.MainNotions.flipTwoThree.logOm, h τ]`. Conclude with `hper M hd τ`.
-/
theorem jnt_logOm_eq (D : D7) (T : Formalism.MainNotions.TaylorLogMetric.Tor D) (hper : Formalism.MainNotions.TaylorLogMetric.per22 D T)
    (hl : OmLink D T) (τ : D.what₂.Tau) : Formalism.MainNotions.flipTwoThree.logOm D τ = Formalism.MainNotions.TaylorLogMetric.logOmVal D := by
  obtain ⟨M, hM, hd, h⟩ := hl
  rw [Formalism.MainNotions.flipTwoThree.logOm, h τ]
  exact hper M hd τ

/- English proof (translation)
Introduce `τ` and use `jnt_logOm_eq D T hper hl τ`.
-/
theorem omValue_of (D : D7) (T : Formalism.MainNotions.TaylorLogMetric.Tor D) (hper : Formalism.MainNotions.TaylorLogMetric.per22 D T)
    (hl : OmLink D T) : D.gx.OmValue D.host.v (Formalism.MainNotions.TaylorLogMetric.logDerivativeAtOne D) :=
  fun τ => jnt_logOm_eq D T hper hl τ

/- English proof (translation)
The claim follows from `|Formalism.MainNotions.TaylorLogMetric.logDerivativeAtOne D| ≤ Cn * Lr ∧ 1 ≤ D.host.v := by obtain ⟨hb, hL, _, _, _, hb', hSc, heta, hsum, _, _, _, hdl, hx2, hv1, _⟩ := h have hx0 : (0:ℝ) < x := by linarith have hmt : (0:ℝ) ≤ D.R.m * D.R.t := by positivity have h2 : 2 ≤ b' / x := …`.
-/
theorem jnt_nums' (D : D7) (T g1 g2 : ℕ) (Cn x b Lr b' Sc eta : ℝ)
    (h : Formalism.MainNotions.flipTwoThree.Nums D T g1 g2 Cn x b Lr b' Sc eta) :
    Real.log 2 ≤ Lr ∧ Real.log x ≤ Lr ∧ Real.log D.host.v ≤ Lr ∧
      |Formalism.MainNotions.TaylorLogMetric.logDerivativeAtOne D| ≤ Cn * Lr ∧ 1 ≤ D.host.v := by
  obtain ⟨hb, hL, _, _, _, hb', hSc, heta, hsum, _, _, _, hdl, hx2, hv1, _⟩ := h
  have hx0 : (0:ℝ) < x := by linarith
  have hmt : (0:ℝ) ≤ D.R.m * D.R.t := by positivity
  have h2 : 2 ≤ b' / x := by linarith
  have hb'2 : 2 * x ≤ b' := (le_div_iff₀ hx0).mp h2
  rw [mul_div_cancel_left₀ b hx0.ne'] at hb'
  have hb1 : 1 ≤ b := by linarith
  have hv0 : (0:ℝ) < D.host.v := by linarith
  have hlog : Real.log (x * b * D.host.v) = Real.log x + Real.log b + Real.log D.host.v := by
    rw [Real.log_mul (mul_pos hx0 hb).ne' hv0.ne', Real.log_mul hx0.ne' hb.ne']
  have hlb : 0 ≤ Real.log b := Real.log_nonneg hb1
  have hlv : 0 ≤ Real.log D.host.v := Real.log_nonneg hv1
  have hlx : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hl2 : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx2
  exact ⟨by linarith, by linarith, by linarith, hdl, hv1⟩

/- English proof (translation)
Use `⟨fun τ τ' => by rw [jnt_logOm_eq D T hper hl, jnt_logOm_eq D T hper hl], ?_⟩` and prove the remaining obligations. Introduce `u b Lr b' Sc eta hN τ`. Take `⟨h2, hlx, hlv, hd1, hv⟩` from `jnt_nums' D _ _ _ Cn x b Lr b' Sc eta hN`. Rewrite using `[jnt_logOm_eq D T hper hl, Formalism.MainNotions.TaylorLogMetric.logOmVal, Real.log_div Real.pi_ne_zero (by linarith : D.host.v ≠ 0)]`. Establish `hg0` using `Real.one_half_lt_eulerMascheroniConstant`.

Establish `hg1` using `Real.eulerMascheroniConstant_lt_two_thirds`. Establish `hl2` using `Real.log_two_gt_d9`. Establish `hpi0 : 0 ≤ Real.log Real.pi` using `Real.log_nonneg (by linarith [Real.pi_gt_three])`. Establish `hpi1 : Real.log Real.pi ≤ 2 * Real.log 2`. Establish `h4 : Real.log 4 = 2 * Real.log 2`.

Rewrite using `[show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num`. Rewrite using `[← h4]`. Conclude with `Real.log_le_log Real.pi_pos Real.pi_le_four`. Establish `hv0 : 0 ≤ Real.log D.host.v` using `Real.log_nonneg hv`. Take `⟨hda, hdb⟩` from `abs_le.mp hd1`.

Rewrite using `[abs_le]`. Apply the tactic sequence `constructor <;> nlinarith`.
-/
theorem _root_.Formalism.MainNotions.flipTwoThree.first_hypothesis_of_lifting (D : D7) (Cn x : ℝ)
    (T : Formalism.MainNotions.TaylorLogMetric.Tor D) (hper : Formalism.MainNotions.TaylorLogMetric.per22 D T) (hl : OmLink D T) :
    Formalism.MainNotions.flipTwoThree.adm1 D Cn (Cn + 4) x := by
  refine ⟨fun τ τ' => by rw [jnt_logOm_eq D T hper hl, jnt_logOm_eq D T hper hl], ?_⟩
  intro u b Lr b' Sc eta hN τ
  obtain ⟨h2, hlx, hlv, hd1, hv⟩ := jnt_nums' D _ _ _ Cn x b Lr b' Sc eta hN
  rw [jnt_logOm_eq D T hper hl, Formalism.MainNotions.TaylorLogMetric.logOmVal,
    Real.log_div Real.pi_ne_zero (by linarith : D.host.v ≠ 0)]
  have hg0 := Real.one_half_lt_eulerMascheroniConstant
  have hg1 := Real.eulerMascheroniConstant_lt_two_thirds
  have hl2 := Real.log_two_gt_d9
  have hpi0 : 0 ≤ Real.log Real.pi := Real.log_nonneg (by linarith [Real.pi_gt_three])
  have hpi1 : Real.log Real.pi ≤ 2 * Real.log 2 := by
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    rw [← h4]
    exact Real.log_le_log Real.pi_pos Real.pi_le_four
  have hv0 : 0 ≤ Real.log D.host.v := Real.log_nonneg hv
  obtain ⟨hda, hdb⟩ := abs_le.mp hd1
  rw [abs_le]
  constructor <;> nlinarith

/- English proof (translation)
The claim follows from `Formalism.MainNotions.flipTwoThree.first_hypothesis_of_lifting D Cn x _ (h22 cc hcc δ hδ).1 hl`.
-/
theorem _root_.Formalism.MainNotions.flipTwoThree.theta_norm_condition_of_theorem (D : D7) (Cn x C : ℝ)
    (h22 : Formalism.MainNotions.TaylorLogMetric.aux₃ D C) (cc : Ideal (𝓞 D.host.K))
    (hcc : Formalism.MainNotions.TaylorLogMetric.IsCurveIdeal D cc) (δ : ℂ) (hδ : Formalism.MainNotions.TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ)
    (hl : OmLink D (Formalism.MainNotions.TaylorLogMetric.tor0 D cc δ)) :
    Formalism.MainNotions.flipTwoThree.adm1 D Cn (Cn + 4) x :=
  Formalism.MainNotions.flipTwoThree.first_hypothesis_of_lifting D Cn x _ (h22 cc hcc δ hδ).1 hl

def ThFree (D : D7) : Prop :=
  ∀ (u : D.what₂.Word) (i : ℕ), i < D.R.m →
    ∀ (s : D.what₂.LL →+* ℂ) (L₁ : (D.mem u).C.cls i) (L₁' : (D.mem u).C.cls (i + 1)),
      (D.fm u).thFree i s L₁ L₁' = Formalism.MainNotions.flipTwoThree.thetaLocalFactorAtIndex D u i s

def ThLink (D : D7) (T : Formalism.MainNotions.TaylorLogMetric.Tor D) (e : Formalism.MainNotions.TaylorLogMetric.FamE D) : Prop :=
  ∀ (u : D.what₂.Word) (i : ℕ), i < D.R.m →
    ∃ (L : Submodule (𝓞 D.host.E) (Fin (D.R.N i) → D.host.E))
      (L' : Submodule (𝓞 D.host.E) (Fin (D.R.N (i + 1)) → D.host.E)),
      Formalism.MainNotions.TaylorLogMetric.admitted D (D.R.N i) (D.R.N (i + 1)) L L' ∧
      ∃ (M : IntermediateField ℚ ℂ) (_ : FiniteDimensional ℚ M), Formalism.MainNotions.TaylorLogMetric.DataIn D T M ∧
        Formalism.MainNotions.TaylorLogMetric.CoefIn D (e (D.R.N i) (D.R.N (i + 1)) L L') M ∧
        (∑ s : D.what₂.LL →+* ℂ, Real.log (Formalism.MainNotions.flipTwoThree.thetaLocalFactorAtIndex D u i s ^ 2)) /
            (Fintype.card (D.what₂.LL →+* ℂ) : ℝ) =
          Formalism.MainNotions.TaylorLogMetric.meanLogNormSq D T L L' M (e (D.R.N i) (D.R.N (i + 1)) L L')

def ThLinkLe (D : D7) (T : Formalism.MainNotions.TaylorLogMetric.Tor D) (e : Formalism.MainNotions.TaylorLogMetric.FamE D) : Prop :=
  ∀ (u : D.what₂.Word) (i : ℕ), i < D.R.m →
    ∃ (L : Submodule (𝓞 D.host.E) (Fin (D.R.N i) → D.host.E))
      (L' : Submodule (𝓞 D.host.E) (Fin (D.R.N (i + 1)) → D.host.E)),
      Formalism.MainNotions.TaylorLogMetric.admitted D (D.R.N i) (D.R.N (i + 1)) L L' ∧
      ∃ (M : IntermediateField ℚ ℂ) (_ : FiniteDimensional ℚ M), Formalism.MainNotions.TaylorLogMetric.DataIn D T M ∧
        Formalism.MainNotions.TaylorLogMetric.CoefIn D (e (D.R.N i) (D.R.N (i + 1)) L L') M ∧
        (∑ s : D.what₂.LL →+* ℂ, Real.log (Formalism.MainNotions.flipTwoThree.thetaLocalFactorAtIndex D u i s ^ 2)) /
            (Fintype.card (D.what₂.LL →+* ℂ) : ℝ) ≤
          Formalism.MainNotions.TaylorLogMetric.meanLogNormSq D T L L' M (e (D.R.N i) (D.R.N (i + 1)) L L')

/- English proof (translation)
Introduce `u i hi`. Take `⟨L, L', hA, M, hM, hD, hC, heq⟩` from `h u i hi`. Conclude with `⟨L, L', hA, M, hM, hD, hC, heq.le⟩`.
-/
theorem ThLink.le {D : D7} {T : Formalism.MainNotions.TaylorLogMetric.Tor D} {e : Formalism.MainNotions.TaylorLogMetric.FamE D} (h : ThLink D T e) :
    ThLinkLe D T e := by
  intro u i hi
  obtain ⟨L, L', hA, M, hM, hD, hC, heq⟩ := h u i hi
  exact ⟨L, L', hA, M, hM, hD, hC, heq.le⟩

/- English proof (translation)
Introduce `u b Lr b' Sc eta hN i hi`. Take `⟨-, hlx, hlv, hd1, -⟩` from `jnt_nums' D _ _ _ Cn x b Lr b' Sc eta hN`. Use `⟨hfree u i hi, ?_⟩` and prove the remaining obligations. Take `⟨L, L', hAdm, M, hM, hD, hC, hle⟩` from `hl u i hi`. Use `le_trans hle ?_` and prove the remaining obligations.

Establish `h1` using `hth.2.1 ((1 + Cn) * Lr) (by linarith) (D.R.N i) (D.R.N (i + 1)) L L' hAdm M hD hC`. Combine the equalities or inequalities in the displayed calculation. Unfold `Formalism.MainNotions.TaylorLogMetric.fF`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem _root_.Formalism.MainNotions.flipTwoThree.second_hypothesis_of_lifting (D : D7) (Cn C x : ℝ)
    (T : Formalism.MainNotions.TaylorLogMetric.Tor D) (e : Formalism.MainNotions.TaylorLogMetric.FamE D) (hth : Formalism.MainNotions.TaylorLogMetric.th22 D T C e)
    (hfree : ThFree D) (hl : ThLinkLe D T e) :
    Formalism.MainNotions.flipTwoThree.adm2 D Cn (C * (1 + Cn)) x := by
  intro u b Lr b' Sc eta hN i hi
  obtain ⟨-, hlx, hlv, hd1, -⟩ := jnt_nums' D _ _ _ Cn x b Lr b' Sc eta hN
  refine ⟨hfree u i hi, ?_⟩
  obtain ⟨L, L', hAdm, M, hM, hD, hC, hle⟩ := hl u i hi
  refine le_trans hle ?_
  have h1 := hth.2.1 ((1 + Cn) * Lr) (by linarith) (D.R.N i) (D.R.N (i + 1)) L L' hAdm M hD hC
  calc _ ≤ C * (Formalism.MainNotions.TaylorLogMetric.fF D : ℝ) * (D.R.N i : ℝ) * (D.R.N (i + 1) : ℝ) * ((1 + Cn) * Lr) := h1
    _ = C * (1 + Cn) * D.R.f * (D.R.N i : ℝ) * (D.R.N (i + 1) : ℝ) * Lr := by
      unfold Formalism.MainNotions.TaylorLogMetric.fF; ring

def Cl22 (D : D7) (C : ℝ) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (χ : Formalism.MainNotions.TaylorLogMetric.IdE D → ℂ)
    (e : Formalism.MainNotions.TaylorLogMetric.FamE D) : Prop :=
  Formalism.MainNotions.TaylorLogMetric.vec22 D (Formalism.MainNotions.TaylorLogMetric.tor0 D cc δ) e ∧ Formalism.MainNotions.TaylorLogMetric.th22 D (Formalism.MainNotions.TaylorLogMetric.tor0 D cc δ) C e ∧
    Formalism.MainNotions.TaylorLogMetric.eq22 D (Formalism.MainNotions.TaylorLogMetric.tor0 D cc δ) χ e ∧ Formalism.MainNotions.TaylorLogMetric.int22 D (Formalism.MainNotions.TaylorLogMetric.tor0 D cc δ) e ∧
    Formalism.MainNotions.TaylorLogMetric.mom22 D cc δ e ∧ Formalism.MainNotions.TaylorLogMetric.LargerSupportMomentCondition D cc δ e ∧ Formalism.MainNotions.TaylorLogMetric.str22 D (Formalism.MainNotions.TaylorLogMetric.tor0 D cc δ) e

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem theta_theorem_iff_clauses (D : D7) (C : ℝ) : Formalism.MainNotions.TaylorLogMetric.aux₃ D C ↔
    ∀ cc : Ideal (𝓞 D.host.K), Formalism.MainNotions.TaylorLogMetric.IsCurveIdeal D cc → ∀ δ : ℂ, Formalism.MainNotions.TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
      Formalism.MainNotions.TaylorLogMetric.per22 D (Formalism.MainNotions.TaylorLogMetric.tor0 D cc δ) ∧ (∃ χ, Formalism.MainNotions.TaylorLogMetric.IsChi D χ) ∧
      ∀ χ, Formalism.MainNotions.TaylorLogMetric.IsChi D χ → ∃ e, Cl22 D C cc δ χ e := Iff.rfl

def ExistsTwelfthRootCharacterThetaFamily (D : D7) (C : ℝ) : Prop :=
  ∃ δ : ℂ, Formalism.MainNotions.TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D D.host.ccK δ ∧ ∃ χ, Formalism.MainNotions.TaylorLogMetric.IsChi D χ ∧
    ∃ e, Cl22 D C D.host.ccK δ χ e ∧ ThLinkLe D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) e

/- English proof (translation)
Take `⟨δ, hδ, χ, hχ, e, hcl, hl⟩` from `h`. Conclude with `Formalism.MainNotions.flipTwoThree.second_hypothesis_of_lifting D Cn C x _ e hcl.2.1 hfree hl`.
-/
theorem _root_.Formalism.MainNotions.flipTwoThree.theta_condition_of_linked_family (D : D7) (Cn C x : ℝ) (hfree : ThFree D) (h : ExistsTwelfthRootCharacterThetaFamily D C) :
    Formalism.MainNotions.flipTwoThree.adm2 D Cn (C * (1 + Cn)) x := by
  obtain ⟨δ, hδ, χ, hχ, e, hcl, hl⟩ := h
  exact Formalism.MainNotions.flipTwoThree.second_hypothesis_of_lifting D Cn C x _ e hcl.2.1 hfree hl

/- English proof (translation)
Assemble the required witnesses or components as `⟨D.host.ccK_ne_bot, Nat.Coprime.mul_right (D.host.ccK_coprime 2 (by simp)) (D.host.ccK_coprime D.host.d (by simp))⟩`.
-/
theorem jnt_ccK_curve (D : D7) : Formalism.MainNotions.TaylorLogMetric.IsCurveIdeal D D.host.ccK :=
  ⟨D.host.ccK_ne_bot, Nat.Coprime.mul_right (D.host.ccK_coprime 2 (by simp))
    (D.host.ccK_coprime D.host.d (by simp))⟩

section Level

open IsDedekindDomain
open scoped TensorProduct

/- English proof (translation)
Use `letI := D.host.cmStar`. Use `haveI : IsCMField D.host.E := D.host.isCMField_hostE`. Apply `D.host.φ₀.injective` to reduce the goal to its premises. Establish `h1 : D.host.φ₀ (D.host.conj x) = starRingEnd ℂ (D.host.φ₀ x)` using `D.host.conjE_apply D.host.φ₀ x`. Rewrite using `[h1]`.

Conclude with `IsCMField.complexEmbedding_complexConj D.host.E D.host.φ₀ x`.
-/
theorem jnt_sig_eq_conj (D : D7) (x : D.host.E) :
    letI := D.host.cmStar
    D.sp.cm.sig x = D.host.conj x := by
  letI := D.host.cmStar
  haveI : IsCMField D.host.E := D.host.isCMField_hostE
  apply D.host.φ₀.injective
  have h1 : D.host.φ₀ (D.host.conj x) = starRingEnd ℂ (D.host.φ₀ x) :=
    D.host.conjE_apply D.host.φ₀ x
  rw [h1]
  exact IsCMField.complexEmbedding_complexConj D.host.E D.host.φ₀ x

/- English proof (translation)
Establish `hgZ : Prime (g : ℤ)` using `Nat.prime_iff_prime_int.mp hg`. Establish `: (Ideal.span {(g : ℤ)}).IsPrime` using `(Ideal.span_singleton_prime hgZ.ne_zero).mpr hgZ`. Take `⟨P, hP, hlo⟩` from `(inferInstance : Nonempty (Ideal.primesOver (Ideal.span {(g : ℤ)}) (𝓞 D.host.F)))`. Establish `hmem : ((g : ℤ) : 𝓞 D.host.F) ∈ P` using `(Ideal.liesOver_span_iff hP.ne_top hgZ).mp hlo`. Establish `hmem' : (g : 𝓞 D.host.F) ∈ P` using `by simpa using hmem`.

Use `⟨⟨P, hP, ?_⟩, hmem'⟩` and prove the remaining obligations. Introduce and unpack `rfl`. Conclude with `hg.ne_zero (by exact_mod_cast (Ideal.mem_bot.mp hmem'))`.
-/
theorem jnt_exists_place (D : D7) (g : ℕ) (hg : g.Prime) :
    ∃ v : HeightOneSpectrum (𝓞 D.host.F), (g : 𝓞 D.host.F) ∈ v.asIdeal := by
  have hgZ : Prime (g : ℤ) := Nat.prime_iff_prime_int.mp hg
  have : (Ideal.span {(g : ℤ)}).IsPrime := (Ideal.span_singleton_prime hgZ.ne_zero).mpr hgZ
  obtain ⟨P, hP, hlo⟩ :=
    (inferInstance : Nonempty (Ideal.primesOver (Ideal.span {(g : ℤ)}) (𝓞 D.host.F)))
  have hmem : ((g : ℤ) : 𝓞 D.host.F) ∈ P := (Ideal.liesOver_span_iff hP.ne_top hgZ).mp hlo
  have hmem' : (g : 𝓞 D.host.F) ∈ P := by simpa using hmem
  refine ⟨⟨P, hP, ?_⟩, hmem'⟩
  rintro rfl
  exact hg.ne_zero (by exact_mod_cast (Ideal.mem_bot.mp hmem'))

/- English proof (translation)
Use `letI := D.host.cmStar`. Introduce and unpack `⟨i, hgk⟩ u hP c`. Take `⟨v, hv⟩` from `jnt_exists_place D (D.host.g i) (D.host.g_prime i)`. Conclude with `h D.sp.cm.sig (jnt_sig_eq_conj D) D.sp.gram0 D.sp.baseGram_isHermitian hD (D.host.g i) (D.host.g_prime i) hgk v hv (Lv u).U (fun x hx => (((Lv u).U_eq x).1 hx).1) (Lv u).U_compact (Lv u).U_open ((Lv u).Uloc v) (hP i v hv) (fun x hx => (((Lv u).U_eq x).1 hx).2 v) _ ((Lv u).y c).2`.
-/
theorem _root_.Formalism.MainNotions.StandardLattice.column_lemma_of_definite_form (D : D7) (Lv : LevelData D) (h : Formalism.MainNotions.UnusedSlot33.division_rows_rational_lattice D)
    (hD : letI := D.host.cmStar; Formalism.MainNotions.UnusedSlot33.IsDef D.sp.cm.sig D.sp.gram0) : Formalism.MainNotions.StandardLattice.adm17 D Lv := by
  letI := D.host.cmStar
  rintro ⟨i, hgk⟩ u hP c
  obtain ⟨v, hv⟩ := jnt_exists_place D (D.host.g i) (D.host.g_prime i)
  exact h D.sp.cm.sig (jnt_sig_eq_conj D) D.sp.gram0 D.sp.baseGram_isHermitian hD (D.host.g i)
    (D.host.g_prime i) hgk v hv (Lv u).U (fun x hx => (((Lv u).U_eq x).1 hx).1) (Lv u).U_compact
    (Lv u).U_open ((Lv u).Uloc v) (hP i v hv) (fun x hx => (((Lv u).U_eq x).1 hx).2 v)
    _ ((Lv u).y c).2

/- English proof (translation)
Use `letI := D.host.cmStar`. Introduce `c`. Establish `hbot` using `h hgk u hP c`. Establish `h1 : ∀ γ : (D.mem u).C.stab 0 c, Formalism.UG.bc (Formalism.UG.inclE (F` using `D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) ((Lv u).stabI c γ : GL (Fin D.R.k) D.host.E) = 1 := by`. Introduce `γ`.

Establish `hm : Formalism.UG.bc (Formalism.UG.inclE (F` using `D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) ((Lv u).stabI c γ : GL (Fin D.R.k) D.host.E) ∈ Formalism.UG.ratPts D.sp.cm.sig D.sp.gram0 (FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊓ (Lv u).U.map (MulAut.conj ((Lv u).y c : GL (Fin D.R.k) _)).toMonoidHom := ⟨⟨((Lv u).stabI c γ : G …`. Rewrite `hm` using `[hbot]`. Conclude with `Subgroup.mem_bot.mp hm`. Use `⟨fun a b => (Lv u).stabI_inj c (Subtype.ext ?_)⟩` and prove the remaining obligations. Conclude with `Formalism.UG.Final.InclInj D.host.F D.host.E (Fin D.R.k) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (Formalism.UG.evalV D.host.F (Lv u).w1).toRingHom.domain_nontrivial ((h1 a).trans (h1 b).symm)`.
-/
theorem stabilisers_trivial_of_adm17 (D : D7) (Lv : LevelData D) (u : D.what₂.Word) (h : Formalism.MainNotions.StandardLattice.adm17 D Lv)
    (hP : letI := D.host.cmStar; (Lv u).ProG) (hgk : StandardLattice.GBig D) : (D.mem u).C.StabZero := by
  letI := D.host.cmStar
  intro c
  have hbot := h hgk u hP c
  have h1 : ∀ γ : (D.mem u).C.stab 0 c,
      Formalism.UG.bc (Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
        ((Lv u).stabI c γ : GL (Fin D.R.k) D.host.E) = 1 := by
    intro γ
    have hm : Formalism.UG.bc (Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
        ((Lv u).stabI c γ : GL (Fin D.R.k) D.host.E) ∈
        Formalism.UG.ratPts D.sp.cm.sig D.sp.gram0 (FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊓
          (Lv u).U.map (MulAut.conj ((Lv u).y c : GL (Fin D.R.k) _)).toMonoidHom :=
      ⟨⟨((Lv u).stabI c γ : GL (Fin D.R.k) D.host.E), ((Lv u).stabI c γ).2, rfl⟩,
        ((Lv u).stabI_range c _ ((Lv u).stabI c γ).2).1 ⟨γ, rfl⟩⟩
    rw [hbot] at hm
    exact Subgroup.mem_bot.mp hm
  refine ⟨fun a b => (Lv u).stabI_inj c (Subtype.ext ?_)⟩
  exact Formalism.UG.Final.InclInj D.host.F D.host.E (Fin D.R.k)
    (FiniteAdeleRing (𝓞 D.host.F) D.host.F)
    (Formalism.UG.evalV D.host.F (Lv u).w1).toRingHom.domain_nontrivial ((h1 a).trans (h1 b).symm)

/- English proof (translation)
Conclude with `stabilisers_trivial_of_adm17 D Lv u (Formalism.MainNotions.StandardLattice.column_lemma_of_definite_form D Lv h hD) hP hgk`.
-/
theorem stabZero_of_level (D : D7) (Lv : LevelData D) (u : D.what₂.Word) (h : Formalism.MainNotions.UnusedSlot33.division_rows_rational_lattice D)
    (hD : letI := D.host.cmStar; Formalism.MainNotions.UnusedSlot33.IsDef D.sp.cm.sig D.sp.gram0)
    (hP : letI := D.host.cmStar; (Lv u).ProG)
    (hgk : StandardLattice.GBig D) : (D.mem u).C.StabZero := by
  exact stabilisers_trivial_of_adm17 D Lv u (Formalism.MainNotions.StandardLattice.column_lemma_of_definite_form D Lv h hD) hP hgk

/- English proof (translation)
Introduce `u c`. Conclude with `stabZero_of_level D Lv u h hD (hP u) hgk c`.
-/
theorem _root_.Formalism.MainNotions.flipTwoThree.stabiliser_condition_of_level (D : D7) (Lv : LevelData D) (h : Formalism.MainNotions.UnusedSlot33.division_rows_rational_lattice D)
    (hD : letI := D.host.cmStar; Formalism.MainNotions.UnusedSlot33.IsDef D.sp.cm.sig D.sp.gram0)
    (hP : letI := D.host.cmStar; ∀ u, (Lv u).ProG)
    (hgk : StandardLattice.GBig D) : Formalism.MainNotions.flipTwoThree.adm3 D := by
  intro u c
  exact stabZero_of_level D Lv u h hD (hP u) hgk c

end Level

namespace ConductorDivisibility

/- English proof (translation)
Establish `h2 : n.factorization 2 = 0` using `Nat.factorization_eq_zero_of_not_dvd (by omega)`. Simplify using `[kronSym, h2]`.
-/
theorem jnt_kronSym_odd (Dd : ℤ) (n : ℕ) (hn : n % 2 = 1) : kronSym Dd n = jacobiSym Dd n := by
  have h2 : n.factorization 2 = 0 := Nat.factorization_eq_zero_of_not_dvd (by omega)
  simp [kronSym, h2]

/- English proof (translation)
Establish `hao : Odd a` using `Nat.odd_iff.mpr ha`. Establish `hmo : Odd m` using `Nat.odd_iff.mpr (by omega)`. Rewrite using `[jacobiSym.neg _ hao]`. Break down `(by omega : a % 4 = 1 ∨ a % 4 = 3) with h1 | h3` into its components or cases. Rewrite using `[ZMod.χ₄_nat_one_mod_four h1, one_mul, jacobiSym.quadratic_reciprocity_one_mod_four h1 hmo]`.

Rewrite using `[ZMod.χ₄_nat_three_mod_four h3, jacobiSym.quadratic_reciprocity_three_mod_four h3 hm]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem jnt_recip (m a : ℕ) (hm : m % 4 = 3) (ha : a % 2 = 1) :
    jacobiSym (-(m : ℤ)) a = jacobiSym a m := by
  have hao : Odd a := Nat.odd_iff.mpr ha
  have hmo : Odd m := Nat.odd_iff.mpr (by omega)
  rw [jacobiSym.neg _ hao]
  rcases (by omega : a % 4 = 1 ∨ a % 4 = 3) with h1 | h3
  · rw [ZMod.χ₄_nat_one_mod_four h1, one_mul, jacobiSym.quadratic_reciprocity_one_mod_four h1 hmo]
  · rw [ZMod.χ₄_nat_three_mod_four h3, jacobiSym.quadratic_reciprocity_three_mod_four h3 hm]
    ring

/- English proof (translation)
Apply `jacobiSym.eq_one_or_neg_one` to reduce the goal to its premises. Simplify `h.symm` using `[Int.gcd]`.
-/
theorem jnt_J_pm (m a : ℕ) (h : a.Coprime m) :
    jacobiSym (-(m : ℤ)) a = 1 ∨ jacobiSym (-(m : ℤ)) a = -1 := by
  apply jacobiSym.eq_one_or_neg_one
  simpa [Int.gcd] using h.symm

def sU (z : ℤ) : ℤˣ := if z = -1 then -1 else 1

/- English proof (translation)
Unfold `sU`. Apply the tactic sequence `rcases h with rfl | rfl <;> simp`.
-/
theorem sU_val {z : ℤ} (h : z = 1 ∨ z = -1) : ((sU z : ℤˣ) : ℤ) = z := by
  unfold sU
  rcases h with rfl | rfl <;> simp

/- English proof (translation)
Apply the tactic sequence `rcases hz with rfl | rfl <;> rcases hw with rfl | rfl <;> first | decide | (unfold sU; simp)`.
-/
theorem sU_mul {z w : ℤ} (hz : z = 1 ∨ z = -1) (hw : w = 1 ∨ w = -1) :
    sU (z * w) = sU z * sU w := by
  rcases hz with rfl | rfl <;> rcases hw with rfl | rfl <;> first | decide | (unfold sU; simp)

/- English proof (translation)
Unfold `sU`. Apply the tactic sequence `rcases Int.units_eq_one_or s with rfl | rfl <;> simp`.
-/
theorem sU_coe (s : ℤˣ) : sU (s : ℤ) = s := by
  unfold sU
  rcases Int.units_eq_one_or s with rfl | rfl <;> simp

def hN (e a : ℕ) : HGrp e :=
  if h : Nat.Coprime a 2 then hcl e (ZMod.unitOfCoprime a (Nat.Coprime.pow_right (e + 2) h)) else 1

def Phi (D : D7) (a : ℕ) : D.R.GG :=
  if h : a.Coprime D.host.condN then D.host.art (ZMod.unitOfCoprime a h) else 1

def MM (D : D7) : ℕ := D.host.QS * D.host.q * D.host.d

/- English proof (translation)
Rewrite using `[Phi, dif_pos h]`.
-/
theorem Phi_of_coprime (D : D7) {a : ℕ} (h : a.Coprime D.host.condN) :
    Phi D a = D.host.art (ZMod.unitOfCoprime a h) := by
  rw [Phi, dif_pos h]

/- English proof (translation)
Establish `h2 : 2 ∣ MM D`. Unfold `MM`. Conclude with `Dvd.dvd.mul_right (Dvd.dvd.mul_right ((dvd_pow_self 2 (by omega)).trans D.host.tower_dvd) _) _`. Conclude with `Nat.Coprime.coprime_dvd_right h2 h`.
-/
theorem cop2 {D : D7} {a : ℕ} (h : a.Coprime (MM D)) : a.Coprime 2 := by
  have h2 : 2 ∣ MM D := by
    unfold MM
    exact Dvd.dvd.mul_right (Dvd.dvd.mul_right ((dvd_pow_self 2 (by omega)).trans D.host.tower_dvd) _) _
  exact Nat.Coprime.coprime_dvd_right h2 h
/- English proof (translation)
Conclude with `Nat.Coprime.coprime_dvd_right (by unfold MM; exact (dvd_mul_left _ _).mul_right _) h`.
-/
theorem copq {D : D7} {a : ℕ} (h : a.Coprime (MM D)) : a.Coprime D.host.q := by
  exact Nat.Coprime.coprime_dvd_right (by unfold MM; exact (dvd_mul_left _ _).mul_right _) h
/- English proof (translation)
Conclude with `Nat.Coprime.coprime_dvd_right (by unfold MM; exact dvd_mul_left _ _) h`.
-/
theorem copd {D : D7} {a : ℕ} (h : a.Coprime (MM D)) : a.Coprime D.host.d := by
  exact Nat.Coprime.coprime_dvd_right (by unfold MM; exact dvd_mul_left _ _) h
/- English proof (translation)
Introduce and unpack `rfl`. Establish `h2` using `cop2 h`. Rewrite `h2` using `[Nat.coprime_zero_left]`. Use linear arithmetic over natural numbers and integers.
-/
theorem cop_ne_zero {D : D7} {a : ℕ} (h : a.Coprime (MM D)) : a ≠ 0 := by
  rintro rfl
  have h2 := cop2 h
  rw [Nat.coprime_zero_left] at h2
  omega
/- English proof (translation)
Establish `h2` using `cop2 h`. Assume the negation of the conclusion as `hne`. Establish `hd : 2 ∣ Nat.gcd a 2` using `Nat.dvd_gcd (by omega) dvd_rfl`. Rewrite `hd` using `[h2.gcd_eq_one]`. Use linear arithmetic over natural numbers and integers.
-/
theorem cop_odd {D : D7} {a : ℕ} (h : a.Coprime (MM D)) : a % 2 = 1 := by
  have h2 := cop2 h
  by_contra hne
  have hd : 2 ∣ Nat.gcd a 2 := Nat.dvd_gcd (by omega) dvd_rfl
  rw [h2.gcd_eq_one] at hd
  omega

/- English proof (translation)
Unfold `hN hcl`. Rewrite using `[dif_pos (Nat.Coprime.mul ha hb), dif_pos ha, dif_pos hb]`. Establish `hu : ZMod.unitOfCoprime (a * b) (Nat.Coprime.pow_right (e + 2) (Nat.Coprime.mul ha hb)) = ZMod.unitOfCoprime a (Nat.Coprime.pow_right (e + 2) ha) * ZMod.unitOfCoprime b (Nat.Coprime.pow_right (e + 2) hb)` using `Units.ext (by simp)`. Rewrite using `[hu]`. Apply the tactic sequence `first | rfl | exact QuotientGroup.mk_mul _ _`.
-/
theorem hN_mul (e : ℕ) {a b : ℕ} (ha : a.Coprime 2) (hb : b.Coprime 2) :
    hN e (a * b) = hN e a * hN e b := by
  unfold hN hcl
  rw [dif_pos (Nat.Coprime.mul ha hb), dif_pos ha, dif_pos hb]
  have hu : ZMod.unitOfCoprime (a * b) (Nat.Coprime.pow_right (e + 2) (Nat.Coprime.mul ha hb)) =
      ZMod.unitOfCoprime a (Nat.Coprime.pow_right (e + 2) ha) * ZMod.unitOfCoprime b (Nat.Coprime.pow_right (e + 2) hb) :=
    Units.ext (by simp)
  rw [hu]
  first | rfl | exact QuotientGroup.mk_mul _ _

/- English proof (translation)
Unfold `hN hcl`. Rewrite using `[dif_pos (Nat.coprime_one_left 2)]`. Establish `h1 : ZMod.unitOfCoprime 1 (Nat.Coprime.pow_right (e + 2) (Nat.coprime_one_left 2)) = 1` using `Units.ext (by simp)`. Rewrite using `[h1]`. Apply the tactic sequence `first | rfl | simp | exact QuotientGroup.mk_one _`.
-/
theorem hN_one (e : ℕ) : hN e 1 = 1 := by
  unfold hN hcl
  rw [dif_pos (Nat.coprime_one_left 2)]
  have h1 : ZMod.unitOfCoprime 1 (Nat.Coprime.pow_right (e + 2) (Nat.coprime_one_left 2)) = 1 := Units.ext (by simp)
  rw [h1]
  first | rfl | simp | exact QuotientGroup.mk_one _

/- English proof (translation)
Rewrite using `[Phi, dif_pos (Nat.coprime_one_left _)]`. Establish `h1 : ZMod.unitOfCoprime 1 (Nat.coprime_one_left D.host.condN) = 1` using `Units.ext (by simp)`. Rewrite using `[h1, map_one]`.
-/
theorem Phi_one (D : D7) : Phi D 1 = 1 := by
  rw [Phi, dif_pos (Nat.coprime_one_left _)]
  have h1 : ZMod.unitOfCoprime 1 (Nat.coprime_one_left D.host.condN) = 1 := Units.ext (by simp)
  rw [h1, map_one]

/- English proof (translation)
Establish `ha' : a.Coprime D.host.condN` using `ha`. Establish `hb' : b.Coprime D.host.condN` using `hb`. Rewrite using `[Phi_of_coprime D ha', Phi_of_coprime D hb', Phi_of_coprime D (Nat.Coprime.mul_left ha' hb'), ← map_mul]`. Use `congr 1`. Conclude with `Units.ext (by simp)`.
-/
theorem Phi_mul (D : D7) {a b : ℕ} (ha : a.Coprime (MM D)) (hb : b.Coprime (MM D)) :
    Phi D (a * b) = Phi D a * Phi D b := by
  have ha' : a.Coprime D.host.condN := ha
  have hb' : b.Coprime D.host.condN := hb
  rw [Phi_of_coprime D ha', Phi_of_coprime D hb', Phi_of_coprime D (Nat.Coprime.mul_left ha' hb'), ← map_mul]
  congr 1
  exact Units.ext (by simp)

/- English proof (translation)
Assemble the required witnesses or components as `⟨hp, fun hd => h (D.host.der.discr_primes.1 p hp hd)⟩`.
-/
theorem jnt_unram (D : D7) (p : ℕ) (hp : p.Prime) (h : ¬ p ∣ D.host.condN) : ZetaZeroFreeRegion.Unram D p :=
  ⟨hp, fun hd => h (D.host.der.discr_primes.1 p hp hd)⟩

/- English proof (translation)
Establish `: Fact p.Prime` using `⟨hp⟩`. Establish `hc : p.Coprime D.host.condN` using `hp.coprime_iff_not_dvd.2 h`. Establish `hpZ : Prime (p : ℤ)` using `Nat.prime_iff_prime_int.mp hp`. Establish `: (Ideal.span {(p : ℤ)}).IsPrime` using `(Ideal.span_singleton_prime hpZ.ne_zero).mpr hpZ`. Take `⟨P, hP⟩` from `(inferInstance : Nonempty (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 D.host.E)))`.

Establish `hex : ∃ σ : D.host.E ≃ₐ[ℚ] D.host.E, ∃ P : Ideal (𝓞 D.host.E), P.IsPrime ∧ P.LiesOver (Ideal.span {(p : ℤ)}) ∧ IsArithFrobAt ℤ σ P`. Use `hP.1` as an intermediate fact. Use `hP.2` as an intermediate fact. Take `⟨σ, hσ⟩` from `(D.host.der.frob p h P).1`. Conclude with `⟨σ, P, hP.1, hP.2, hσ⟩`.

Unfold `frob`. Rewrite using `[dif_pos hex, Phi_of_coprime D hc]`. Take `⟨P', hP'1, hP'2, hfr⟩` from `hex.choose_spec`. Conclude with `(D.host.frob_iff p hc P' _).1 hfr`.
-/
theorem jnt_frob_eq (D : D7) (p : ℕ) (hp : p.Prime) (h : ¬ p ∣ D.host.condN) : frob D p = Phi D p := by
  have : Fact p.Prime := ⟨hp⟩
  have hc : p.Coprime D.host.condN := hp.coprime_iff_not_dvd.2 h
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have : (Ideal.span {(p : ℤ)}).IsPrime := (Ideal.span_singleton_prime hpZ.ne_zero).mpr hpZ
  obtain ⟨P, hP⟩ := (inferInstance : Nonempty (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 D.host.E)))
  have hex : ∃ σ : D.host.E ≃ₐ[ℚ] D.host.E, ∃ P : Ideal (𝓞 D.host.E),
      P.IsPrime ∧ P.LiesOver (Ideal.span {(p : ℤ)}) ∧ IsArithFrobAt ℤ σ P := by
    have := hP.1
    have := hP.2
    obtain ⟨σ, hσ⟩ := (D.host.der.frob p h P).1
    exact ⟨σ, P, hP.1, hP.2, hσ⟩
  unfold frob
  rw [dif_pos hex, Phi_of_coprime D hc]
  obtain ⟨P', hP'1, hP'2, hfr⟩ := hex.choose_spec
  exact (D.host.frob_iff p hc P' _).1 hfr

/- English proof (translation)
Proceed by induction on `a using Nat.recOnMul with`. Consider the case `zero => exact absurd rfl (cop_ne_zero ha)`. Consider the case `one => simp [Phi_one]`. Consider the case `prime p hp`. Establish `hN : ¬ p ∣ D.host.condN` using `hp.coprime_iff_not_dvd.1 ha`.

Rewrite using `[h.2 p (jnt_unram D p hp hN), jnt_frob_eq D p hp hN]`. Consider the case `mul a b iha ihb`. Establish `ha' : a.Coprime (MM D)` using `Nat.Coprime.coprime_mul_right ha`. Establish `hb' : b.Coprime (MM D)` using `Nat.Coprime.coprime_mul_left ha`. Rewrite using `[Nat.cast_mul, map_mul, iha ha', ihb hb', Phi_mul D ha' hb', map_mul]`.

Use `push_cast`. Both sides reduce to the same expression.
-/
theorem jnt_reads_apply (D : D7) (ψ : ZetaZeroFreeRegion.Chr D) (χ : Σ N : ℕ+, DirichletCharacter ℂ N)
    (h : ZetaZeroFreeRegion.Reads D ψ χ) (a : ℕ) (ha : a.Coprime (MM D)) :
    χ.2 (a : ZMod χ.1) = ((ψ (Phi D a) : ℂˣ) : ℂ) := by
  induction a using Nat.recOnMul with
  | zero => exact absurd rfl (cop_ne_zero ha)
  | one => simp [Phi_one]
  | prime p hp =>
    have hN : ¬ p ∣ D.host.condN := hp.coprime_iff_not_dvd.1 ha
    rw [h.2 p (jnt_unram D p hp hN), jnt_frob_eq D p hp hN]
  | mul a b iha ihb =>
    have ha' : a.Coprime (MM D) := Nat.Coprime.coprime_mul_right ha
    have hb' : b.Coprime (MM D) := Nat.Coprime.coprime_mul_left ha
    rw [Nat.cast_mul, map_mul, iha ha', ihb hb', Phi_mul D ha' hb', map_mul]
    push_cast
    rfl

/- English proof (translation)
Establish `h2 : 2 ∣ D.host.QS` using `(dvd_pow_self 2 (by omega)).trans D.host.tower_dvd`. Establish `hqd : D.host.q * D.host.d ≠ 0`. Introduce `h0`. Establish `hc` using `D.host.QS_coprime`. Rewrite `hc` using `[h0, Nat.coprime_zero_right]`.

Rewrite `h2` using `[hc]`. Use linear arithmetic over natural numbers and integers. Establish `hQ` using `D.host.QS_pos`. Unfold `MM`. Rewrite using `[mul_assoc]`.

Conclude with `Nat.mul_ne_zero (by omega) hqd`.
-/
theorem MM_ne_zero (D : D7) : MM D ≠ 0 := by
  have h2 : 2 ∣ D.host.QS := (dvd_pow_self 2 (by omega)).trans D.host.tower_dvd
  have hqd : D.host.q * D.host.d ≠ 0 := by
    intro h0
    have hc := D.host.QS_coprime
    rw [h0, Nat.coprime_zero_right] at hc
    rw [hc] at h2
    omega
  have hQ := D.host.QS_pos
  unfold MM
  rw [mul_assoc]
  exact Nat.mul_ne_zero (by omega) hqd

open DirichletCharacter in
/- English proof (translation)
Establish `: NeZero (N1 * N2 * M)` using `⟨mul_ne_zero (mul_ne_zero (NeZero.ne N1) (NeZero.ne N2)) hM⟩`. Establish `hd1 : N1 ∣ N1 * N2 * M` using `⟨N2 * M, by ring⟩`. Establish `hd2 : N2 ∣ N1 * N2 * M` using `⟨N1 * M, by ring⟩`. Establish `hdM : M ∣ N1 * N2 * M` using `Dvd.intro_left _ rfl`. Establish `hch : changeLevel hd1 χ1 = changeLevel hd2 χ2`.

Use extensionality with `u`. Establish `hcop : Nat.Coprime (u : ZMod (N1 * N2 * M)).val (N1 * N2 * M)` using `ZMod.val_coe_unit_coprime u`. Establish `hu : (((u : ZMod (N1 * N2 * M)).val : ℤ) : ZMod (N1 * N2 * M)) = u` using `by simp`. Establish `hic : IsCoprime ((u : ZMod (N1 * N2 * M)).val : ℤ) (N1 * N2 * M : ℕ)` using `Nat.isCoprime_iff_coprime.mpr hcop`. Rewrite using `[← hu, changeLevel_eq_cast_of_dvd' _ _ hic, changeLevel_eq_cast_of_dvd' _ _ hic]`.

Simplify using `only [Int.cast_natCast]`. Conclude with `h _ (Nat.Coprime.coprime_dvd_right hdM hcop)`. Establish `hc` using `congrArg conductor hch`. Rewrite `hc` using `[conductor_changeLevel, conductor_changeLevel]`. Establish `hN : N1 = N2` using `(((isPrimitive_def χ1).mp h1).symm.trans hc).trans ((isPrimitive_def χ2).mp h2)`.

Substitute `hN` using the available equality. Rewrite using `[changeLevel_injective hd1 hch]`.
-/
theorem _root_.Formalism.MainNotions.GlobalTheoryTheory.ConductorLiftingHypotheses.prim_unique {N1 N2 : ℕ} [NeZero N1] [NeZero N2] (χ1 : DirichletCharacter ℂ N1)
    (χ2 : DirichletCharacter ℂ N2) (h1 : χ1.IsPrimitive) (h2 : χ2.IsPrimitive) (M : ℕ) (hM : M ≠ 0)
    (h : ∀ a : ℕ, a.Coprime M → χ1 (a : ZMod N1) = χ2 (a : ZMod N2)) (n : ℕ) :
    χ1 (n : ZMod N1) = χ2 (n : ZMod N2) := by
  have : NeZero (N1 * N2 * M) := ⟨mul_ne_zero (mul_ne_zero (NeZero.ne N1) (NeZero.ne N2)) hM⟩
  have hd1 : N1 ∣ N1 * N2 * M := ⟨N2 * M, by ring⟩
  have hd2 : N2 ∣ N1 * N2 * M := ⟨N1 * M, by ring⟩
  have hdM : M ∣ N1 * N2 * M := Dvd.intro_left _ rfl
  have hch : changeLevel hd1 χ1 = changeLevel hd2 χ2 := by
    ext u
    have hcop : Nat.Coprime (u : ZMod (N1 * N2 * M)).val (N1 * N2 * M) := ZMod.val_coe_unit_coprime u
    have hu : (((u : ZMod (N1 * N2 * M)).val : ℤ) : ZMod (N1 * N2 * M)) = u := by simp
    have hic : IsCoprime ((u : ZMod (N1 * N2 * M)).val : ℤ) (N1 * N2 * M : ℕ) :=
      Nat.isCoprime_iff_coprime.mpr hcop
    rw [← hu, changeLevel_eq_cast_of_dvd' _ _ hic, changeLevel_eq_cast_of_dvd' _ _ hic]
    simp only [Int.cast_natCast]
    exact h _ (Nat.Coprime.coprime_dvd_right hdM hcop)
  have hc := congrArg conductor hch
  rw [conductor_changeLevel, conductor_changeLevel] at hc
  have hN : N1 = N2 := (((isPrimitive_def χ1).mp h1).symm.trans hc).trans ((isPrimitive_def χ2).mp h2)
  subst hN
  rw [changeLevel_injective hd1 hch]

/- English proof (translation)
Rewrite using `[jnt_recip p a hp ha, ← jacobiSym.legendreSym.to_jacobiSym p]`. Simplify using `only [legendreSym, Int.cast_natCast, hr]`.
-/
theorem jnt_J_of_cast (p a : ℕ) [Fact p.Prime] (hp : p % 4 = 3) (ha : a % 2 = 1) (r : ZMod p)
    (hr : (a : ZMod p) = r) : jacobiSym (-(p : ℤ)) a = quadraticChar (ZMod p) r := by
  rw [jnt_recip p a hp ha, ← jacobiSym.legendreSym.to_jacobiSym p]
  simp only [legendreSym, Int.cast_natCast, hr]

/- English proof (translation)
The claim follows from `Nat.Coprime.mul_right (Nat.Coprime.mul_right (Nat.Coprime.pow_right 3 (cop2 h)) (copq h)) (copd h)`.
-/
theorem cop8 {D : D7} {a : ℕ} (h : a.Coprime (MM D)) : a.Coprime (8 * D.host.q * D.host.d) :=
  Nat.Coprime.mul_right (Nat.Coprime.mul_right (Nat.Coprime.pow_right 3 (cop2 h)) (copq h)) (copd h)

/- English proof (translation)
Establish `: NeZero χ₁.conductor` using `⟨DirichletCharacter.conductor_ne_zero χ₁⟩`. Establish `h3 : ∀ a : ℕ, a.Coprime M₁ → χ₁.primitiveCharacter (a : ZMod χ₁.conductor) = f a`. Introduce `a ha`. Establish `e1` using `DirichletCharacter.primitiveCharacter_apply_of_isCoprime χ₁ (Nat.isCoprime_iff_coprime.mpr ha)`. Simplify using `only [Int.cast_natCast] at e1`.

Rewrite using `[e1, h1 a ha]`. Use `⟨hχ, fun a ha => ?_⟩` and prove the remaining obligations. Rewrite using `[ConductorLiftingHypotheses.prim_unique χ χ₁.primitiveCharacter hχ (DirichletCharacter.primitiveCharacter_isPrimitive χ₁) (M * M₁) (mul_ne_zero hM (NeZero.ne _)) (fun b hb => by`. Rewrite using `[h2 b (Nat.Coprime.coprime_mul_right_right hb), h3 b (Nat.Coprime.coprime_mul_left_right hb)]) a, h3 a ha]`.
-/
theorem jnt_induces_of {N M₁ : ℕ} [NeZero N] [NeZero M₁] (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive)
    (χ₁ : DirichletCharacter ℂ M₁) (f : ℕ → ℂ) (h1 : ∀ a : ℕ, a.Coprime M₁ → χ₁ (a : ZMod M₁) = f a)
    (M : ℕ) (hM : M ≠ 0) (h2 : ∀ a : ℕ, a.Coprime M → χ (a : ZMod N) = f a) : Induces χ f M₁ := by
  have : NeZero χ₁.conductor := ⟨DirichletCharacter.conductor_ne_zero χ₁⟩
  have h3 : ∀ a : ℕ, a.Coprime M₁ → χ₁.primitiveCharacter (a : ZMod χ₁.conductor) = f a := by
    intro a ha
    have e1 := DirichletCharacter.primitiveCharacter_apply_of_isCoprime χ₁ (Nat.isCoprime_iff_coprime.mpr ha)
    simp only [Int.cast_natCast] at e1
    rw [e1, h1 a ha]
  refine ⟨hχ, fun a ha => ?_⟩
  rw [ConductorLiftingHypotheses.prim_unique χ χ₁.primitiveCharacter hχ (DirichletCharacter.primitiveCharacter_isPrimitive χ₁) (M * M₁)
    (mul_ne_zero hM (NeZero.ne _)) (fun b hb => by
      rw [h2 b (Nat.Coprime.coprime_mul_right_right hb), h3 b (Nat.Coprime.coprime_mul_left_right hb)]) a, h3 a ha]

/- English proof (translation)
Establish `: Fact r.Prime` using `⟨hr⟩`. Use `⟨DirichletCharacter.changeLevel hd ((quadraticChar (ZMod r)).ringHomComp (Int.castRingHom ℂ)), fun a ha => ?_⟩` and prove the remaining obligations. Establish `hodd : a % 2 = 1` using `Nat.odd_iff.mp (Nat.coprime_two_right.mp (Nat.Coprime.coprime_dvd_right h2 ha))`. Establish `e1` using `DirichletCharacter.changeLevel_eq_cast_of_dvd' ((quadraticChar (ZMod r)).ringHomComp (Int.castRingHom ℂ)) hd (Nat.isCoprime_iff_coprime.mpr ha)`. Simplify using `only [Int.cast_natCast] at e1`.

Rewrite using `[e1, MulChar.ringHomComp_apply]`. Unfold `kron`. Rewrite using `[jnt_kronSym_odd _ _ hodd, jnt_J_of_cast r a h4 hodd _ rfl]`. Both sides reduce to the same expression.
-/
theorem jnt_exists_kron (r M₁ : ℕ) [NeZero M₁] (hr : r.Prime) (h4 : r % 4 = 3) (hd : r ∣ M₁) (h2 : 2 ∣ M₁) :
    ∃ χ₁ : DirichletCharacter ℂ M₁, ∀ a : ℕ, a.Coprime M₁ → χ₁ (a : ZMod M₁) = kron (-(r : ℤ)) a := by
  have : Fact r.Prime := ⟨hr⟩
  refine ⟨DirichletCharacter.changeLevel hd ((quadraticChar (ZMod r)).ringHomComp (Int.castRingHom ℂ)),
    fun a ha => ?_⟩
  have hodd : a % 2 = 1 := Nat.odd_iff.mp (Nat.coprime_two_right.mp (Nat.Coprime.coprime_dvd_right h2 ha))
  have e1 := DirichletCharacter.changeLevel_eq_cast_of_dvd'
    ((quadraticChar (ZMod r)).ringHomComp (Int.castRingHom ℂ)) hd (Nat.isCoprime_iff_coprime.mpr ha)
  simp only [Int.cast_natCast] at e1
  rw [e1, MulChar.ringHomComp_apply]
  unfold kron
  rw [jnt_kronSym_odd _ _ hodd, jnt_J_of_cast r a h4 hodd _ rfl]
  rfl

/- English proof (translation)
Unfold `psDir kron`. Rewrite using `[jnt_kronSym_odd _ _ (cop_odd ha), ← D.host.flPS.psAt_eq ha, D.host.psAt_of_coprime ha, Phi_of_coprime D ha]`. Both sides reduce to the same expression.
-/
theorem jnt_psC_Phi (D : D7) {a : ℕ} (ha : a.Coprime (MM D)) :
    ((ZetaZeroFreeRegion.psC D (Phi D a) : ℂˣ) : ℂ) = psDir D.host.q a := by
  unfold psDir kron
  rw [jnt_kronSym_odd _ _ (cop_odd ha), ← D.host.flPS.psAt_eq ha, D.host.psAt_of_coprime ha, Phi_of_coprime D ha]
  rfl

/- English proof (translation)
Establish `hd : (((D.host.art (ZMod.unitOfCoprime a ha)).1.2 : ℤˣ) : ℤ) = jacobiSym (-(D.host.d : ℤ)) a`. Rewrite using `[D.host.der.art_ch, Formalism.HC.jacobi_neg_recip D.host.d_mod_four (cop_odd ha)]`. Conclude with `Formalism.HC.jacobi_congr ((D.host.val_unitOfCoprime ha).of_dvd D.host.d_dvd_condN)`. Unfold `chDir kron`. Rewrite using `[jnt_kronSym_odd _ _ (cop_odd ha), ← hd, Phi_of_coprime D ha]`.

Both sides reduce to the same expression.
-/
theorem jnt_chC_Phi (D : D7) {a : ℕ} (ha : a.Coprime (MM D)) :
    ((ZetaZeroFreeRegion.chC D (Phi D a) : ℂˣ) : ℂ) = chDir D.host.d a := by
  have hd : (((D.host.art (ZMod.unitOfCoprime a ha)).1.2 : ℤˣ) : ℤ) = jacobiSym (-(D.host.d : ℤ)) a := by
    rw [D.host.der.art_ch, Formalism.HC.jacobi_neg_recip D.host.d_mod_four (cop_odd ha)]
    exact Formalism.HC.jacobi_congr ((D.host.val_unitOfCoprime ha).of_dvd D.host.d_dvd_condN)
  unfold chDir kron
  rw [jnt_kronSym_odd _ _ (cop_odd ha), ← hd, Phi_of_coprime D ha]
  rfl

/- English proof (translation)
Unfold `ZetaZeroFreeRegion.prim`. Rewrite using `[dif_pos h]`. Conclude with `h.choose_spec`.
-/
theorem jnt_prim_reads (D : D7) (ψ : ZetaZeroFreeRegion.Chr D) (h : ∃ χ, ZetaZeroFreeRegion.Reads D ψ χ) :
    ZetaZeroFreeRegion.Reads D ψ (ZetaZeroFreeRegion.prim D ψ) := by
  unfold ZetaZeroFreeRegion.prim
  rw [dif_pos h]
  exact h.choose_spec

/- English proof (translation)
Assemble the required witnesses or components as `⟨mul_ne_zero (mul_ne_zero (by norm_num) D.host.q_prime.ne_zero) D.host.d_prime.ne_zero⟩`.
-/
theorem jnt_eight_ne (D : D7) : NeZero (8 * D.host.q * D.host.d) :=
  ⟨mul_ne_zero (mul_ne_zero (by norm_num) D.host.q_prime.ne_zero) D.host.d_prime.ne_zero⟩

/- English proof (translation)
The claim follows from `haveI := jnt_eight_ne D jnt_exists_kron _ _ D.host.q_prime D.host.q_mod_four ⟨8 * D.host.d, by ring⟩ ⟨4 * D.host.q * D.host.d, by ring⟩`.
-/
theorem jnt_exists_ps (D : D7) : ∃ χ₁ : DirichletCharacter ℂ (8 * D.host.q * D.host.d),
    ∀ a : ℕ, a.Coprime (8 * D.host.q * D.host.d) → χ₁ (a : ZMod _) = psDir D.host.q a :=
  haveI := jnt_eight_ne D
  jnt_exists_kron _ _ D.host.q_prime D.host.q_mod_four ⟨8 * D.host.d, by ring⟩ ⟨4 * D.host.q * D.host.d, by ring⟩

/- English proof (translation)
The claim follows from `haveI := jnt_eight_ne D jnt_exists_kron _ _ D.host.d_prime D.host.d_mod_four (dvd_mul_left _ _) ⟨4 * D.host.q * D.host.d, by ring⟩`.
-/
theorem jnt_exists_ch (D : D7) : ∃ χ₁ : DirichletCharacter ℂ (8 * D.host.q * D.host.d),
    ∀ a : ℕ, a.Coprime (8 * D.host.q * D.host.d) → χ₁ (a : ZMod _) = chDir D.host.d a :=
  haveI := jnt_eight_ne D
  jnt_exists_kron _ _ D.host.d_prime D.host.d_mod_four (dvd_mul_left _ _) ⟨4 * D.host.q * D.host.d, by ring⟩

/- English proof (translation)
Use `jnt_eight_ne D` as an intermediate fact. Take `⟨χ₁, h1⟩` from `jnt_exists_ps D`. Conclude with `jnt_induces_of χ.2 h.1 χ₁ _ h1 (MM D) (MM_ne_zero D) (fun a ha => by rw [jnt_reads_apply D _ χ h a ha, jnt_psC_Phi D ha])`.
-/
theorem jnt_induces_ps (D : D7) (χ : Σ N : ℕ+, DirichletCharacter ℂ N)
    (h : ZetaZeroFreeRegion.Reads D (ZetaZeroFreeRegion.psC D) χ) :
    Induces χ.2 (psDir D.host.q) (8 * D.host.q * D.host.d) := by
  have := jnt_eight_ne D
  obtain ⟨χ₁, h1⟩ := jnt_exists_ps D
  exact jnt_induces_of χ.2 h.1 χ₁ _ h1 (MM D) (MM_ne_zero D)
    (fun a ha => by rw [jnt_reads_apply D _ χ h a ha, jnt_psC_Phi D ha])

/- English proof (translation)
Use `jnt_eight_ne D` as an intermediate fact. Take `⟨χ₁, h1⟩` from `jnt_exists_ch D`. Conclude with `jnt_induces_of χ.2 h.1 χ₁ _ h1 (MM D) (MM_ne_zero D) (fun a ha => by rw [jnt_reads_apply D _ χ h a ha, jnt_chC_Phi D ha])`.
-/
theorem jnt_induces_ch (D : D7) (χ : Σ N : ℕ+, DirichletCharacter ℂ N)
    (h : ZetaZeroFreeRegion.Reads D (ZetaZeroFreeRegion.chC D) χ) :
    Induces χ.2 (chDir D.host.d) (8 * D.host.q * D.host.d) := by
  have := jnt_eight_ne D
  obtain ⟨χ₁, h1⟩ := jnt_exists_ch D
  exact jnt_induces_of χ.2 h.1 χ₁ _ h1 (MM D) (MM_ne_zero D)
    (fun a ha => by rw [jnt_reads_apply D _ χ h a ha, jnt_chC_Phi D ha])

/- English proof (translation)
Use `jnt_eight_ne D` as an intermediate fact. Take `⟨χ₁, h1⟩` from `jnt_exists_ch D`. Take `⟨χ₂, h2⟩` from `jnt_exists_ps D`. Conclude with `jnt_induces_of χ.2 h.1 (χ₁ * χ₂) _ (fun a ha => by rw [MulChar.mul_apply, h1 a ha, h2 a ha]) (MM D) (MM_ne_zero D) (fun a ha => by`. Rewrite using `[jnt_reads_apply D _ χ h a ha, MonoidHom.mul_apply, Units.val_mul, jnt_chC_Phi D ha, jnt_psC_Phi D ha])`.
-/
theorem jnt_induces_chps (D : D7) (χ : Σ N : ℕ+, DirichletCharacter ℂ N)
    (h : ZetaZeroFreeRegion.Reads D (ZetaZeroFreeRegion.chC D * ZetaZeroFreeRegion.psC D) χ) :
    Induces χ.2 (fun a => chDir D.host.d a * psDir D.host.q a) (8 * D.host.q * D.host.d) := by
  have := jnt_eight_ne D
  obtain ⟨χ₁, h1⟩ := jnt_exists_ch D
  obtain ⟨χ₂, h2⟩ := jnt_exists_ps D
  exact jnt_induces_of χ.2 h.1 (χ₁ * χ₂) _
    (fun a ha => by rw [MulChar.mul_apply, h1 a ha, h2 a ha]) (MM D) (MM_ne_zero D)
    (fun a ha => by
      rw [jnt_reads_apply D _ χ h a ha, MonoidHom.mul_apply, Units.val_mul,
        jnt_chC_Phi D ha, jnt_psC_Phi D ha])

/- English proof (translation)
Take `⟨-, -, B1, B2, B3⟩` from `h`. Introduce `ψ hψ`. Simplify using `only [Finset.mem_insert, Finset.mem_singleton] at hψ`. Break down `hψ with rfl | rfl | rfl` into its components or cases. Conclude with `B1 _ _ (jnt_induces_ps D _ (jnt_prim_reads D _ (h10 _)))`.

Conclude with `B2 _ _ (jnt_induces_ch D _ (jnt_prim_reads D _ (h10 _)))`. Conclude with `B3 _ _ (jnt_induces_chps D _ (jnt_prim_reads D _ (h10 _)))`.
-/
theorem character_bounds_of_proposition_five (D : D7) (s : Scale) (C : ℝ) (h10 : ZetaZeroFreeRegion.adm10 D)
    (h : ShortIntervalPrimes.PrimesAsPropTwoFive D s.x s.eps C) : ZetaZeroFreeRegion.adm6 D s C := by
  obtain ⟨-, -, B1, B2, B3⟩ := h
  intro ψ hψ
  simp only [Finset.mem_insert, Finset.mem_singleton] at hψ
  rcases hψ with rfl | rfl | rfl
  · exact B1 _ _ (jnt_induces_ps D _ (jnt_prim_reads D _ (h10 _)))
  · exact B2 _ _ (jnt_induces_ch D _ (jnt_prim_reads D _ (h10 _)))
  · exact B3 _ _ (jnt_induces_chps D _ (jnt_prim_reads D _ (h10 _)))

/- English proof (translation)
Establish `h2 : ((θ (-1) : ℂˣ) : ℂ) * ((θ (-1) : ℂˣ) : ℂ) = 1`. Rewrite using `[← Units.val_mul, ← map_mul]`. Simplify using the standard rewrite rules. Break down `mul_self_eq_one_iff.mp h2 with h | h` into its components or cases. Use `left`.

Introduce `s`. Break down `Int.units_eq_one_or s with rfl | rfl` into its components or cases. Simplify using the standard rewrite rules. Conclude with `h`. Use `right`.

Introduce `s`. Break down `Int.units_eq_one_or s with rfl | rfl` into its components or cases. Simplify using the standard rewrite rules. Rewrite using `[h]`. Simplify using the standard rewrite rules.
-/
theorem jnt_sign_hom (θ : ℤˣ →* ℂˣ) :
    (∀ s, ((θ s : ℂˣ) : ℂ) = 1) ∨ (∀ s : ℤˣ, ((θ s : ℂˣ) : ℂ) = (((s : ℤˣ) : ℤ) : ℂ)) := by
  have h2 : ((θ (-1) : ℂˣ) : ℂ) * ((θ (-1) : ℂˣ) : ℂ) = 1 := by
    rw [← Units.val_mul, ← map_mul]
    simp
  rcases mul_self_eq_one_iff.mp h2 with h | h
  · left
    intro s
    rcases Int.units_eq_one_or s with rfl | rfl
    · simp
    · exact h
  · right
    intro s
    rcases Int.units_eq_one_or s with rfl | rfl
    · simp
    · rw [h]
      simp

/- English proof (translation)
Rewrite using `[pow_add, mul_comm]`. Conclude with `Nat.mul_dvd_mul_left 4 D.R.two_pow_dvd_ord`.
-/
theorem tower_dvd_four_n (D : D7) : 2 ^ (D.R.e + 2) ∣ 4 * D.R.n := by
  rw [pow_add, mul_comm]
  exact Nat.mul_dvd_mul_left 4 D.R.two_pow_dvd_ord

def xiOf (D : D7) (ψ : ZetaZeroFreeRegion.Chr D) : DirichletCharacter ℂ D.host.condN :=
  MulChar.ofUnitHom ((ψ.comp (MonoidHom.inr G0 (D.R.MA))).comp
    ((MonoidHom.snd G0 D.R.MA).comp D.host.art))

/- English proof (translation)
Use `show xiOf D ψ (-1) = 1`. Establish `h1 : (-1 : ZMod D.host.condN) = (((-1 : (ZMod D.host.condN)ˣ)) : ZMod D.host.condN)` using `by simp`. Unfold `xiOf`. Rewrite using `[h1, MulChar.ofUnitHom_coe]`. Simplify using `only [MonoidHom.comp_apply]`.

Rewrite using `[D.host.art_neg_one]`. Use `show ((ψ 1 : ℂˣ) : ℂ) = 1`. Simplify using the standard rewrite rules.
-/
theorem xiOf_even (D : D7) (ψ : ZetaZeroFreeRegion.Chr D) : (xiOf D ψ).Even := by
  show xiOf D ψ (-1) = 1
  have h1 : (-1 : ZMod D.host.condN) = (((-1 : (ZMod D.host.condN)ˣ)) : ZMod D.host.condN) := by simp
  unfold xiOf
  rw [h1, MulChar.ofUnitHom_coe]
  simp only [MonoidHom.comp_apply]
  rw [D.host.art_neg_one]
  show ((ψ 1 : ℂˣ) : ℂ) = 1
  simp

/- English proof (translation)
Unfold `xiOf`. Rewrite using `[Phi_of_coprime D ha, ← ZMod.coe_unitOfCoprime a (show a.Coprime D.host.condN from ha), MulChar.ofUnitHom_coe]`. Both sides reduce to the same expression.
-/
theorem xiOf_apply (D : D7) (ψ : ZetaZeroFreeRegion.Chr D) {a : ℕ} (ha : a.Coprime (MM D)) :
    xiOf D ψ (a : ZMod D.host.condN) = ((ψ ((1 : G0), (Phi D a).2) : ℂˣ) : ℂ) := by
  unfold xiOf
  rw [Phi_of_coprime D ha, ← ZMod.coe_unitOfCoprime a (show a.Coprime D.host.condN from ha), MulChar.ofUnitHom_coe]
  rfl

/- English proof (translation)
Unfold `MM`. Conclude with `h`.
-/
theorem cop4n {D : D7} {a : ℕ} (h : a.Coprime (D.host.QS * D.host.q * D.host.d)) :
    a.Coprime (MM D) := by
  unfold MM
  exact h

/- English proof (translation)
Assemble the required witnesses or components as `⟨h.1, ψ, fun a ha => by rw [jnt_reads_apply D ψ χ h a ha, Phi_of_coprime D ha]⟩`.
-/
theorem jnt_isCharED_of_reads (D : D7) (ψ : ZetaZeroFreeRegion.Chr D) (χ : Σ N : ℕ+, DirichletCharacter ℂ N)
    (h : ZetaZeroFreeRegion.Reads D ψ χ) : IsCharED D χ.2 :=
  ⟨h.1, ψ, fun a ha => by rw [jnt_reads_apply D ψ χ h a ha, Phi_of_coprime D ha]⟩

/- English proof (translation)
Use `⟨DirichletCharacter.isPrimitive_one_level_one, 1, fun a ha => ?_⟩` and prove the remaining obligations. Establish `: Subsingleton (ZMod ((1 : ℕ+) : ℕ))` using `(inferInstance : Subsingleton (ZMod 1))`. Rewrite using `[MulChar.one_apply (isUnit_of_subsingleton _)]`. Simplify using the standard rewrite rules.
-/
theorem jnt_isCharED_one (D : D7) : IsCharED D (1 : DirichletCharacter ℂ ((1 : ℕ+) : ℕ)) := by
  refine ⟨DirichletCharacter.isPrimitive_one_level_one, 1, fun a ha => ?_⟩
  have : Subsingleton (ZMod ((1 : ℕ+) : ℕ)) := (inferInstance : Subsingleton (ZMod 1))
  rw [MulChar.one_apply (isUnit_of_subsingleton _)]
  simp

/- English proof (translation)
Distinguish the cases in `h : ∃ χ, ZetaZeroFreeRegion.Reads D ψ χ`. Conclude with `jnt_isCharED_of_reads D ψ _ (jnt_prim_reads D ψ h)`. Establish `key : ZetaZeroFreeRegion.prim D ψ = ⟨1, 1⟩` using `dif_neg h`. Rewrite using `[key]`. Conclude with `jnt_isCharED_one D`.
-/
theorem jnt_prim_isCharED (D : D7) (ψ : ZetaZeroFreeRegion.Chr D) : IsCharED D (ZetaZeroFreeRegion.prim D ψ).2 := by
  by_cases h : ∃ χ, ZetaZeroFreeRegion.Reads D ψ χ
  · exact jnt_isCharED_of_reads D ψ _ (jnt_prim_reads D ψ h)
  · have key : ZetaZeroFreeRegion.prim D ψ = ⟨1, 1⟩ := dif_neg h
    rw [key]
    exact jnt_isCharED_one D

/- English proof (translation)
Introduce `ψ y hy`. Conclude with `h ⟨C5, h5⟩ _ _ (jnt_prim_isCharED D ψ) y hy`.
-/
theorem _root_.Formalism.MainNotions.ZetaZeroFreeRegion.sizes_bound_of_log_estimates (D : D7) (s : Scale) (c C5 : ℝ) (h5 : ShortIntervalPrimes.PrimesAsPropTwoFive D s.x s.eps C5)
    (h : ShortIntervalPrimes.Conclusion6 D s.x s.eps c) : ZetaZeroFreeRegion.adm5 D s c := by
  intro ψ y hy
  exact h ⟨C5, h5⟩ _ _ (jnt_prim_isCharED D ψ) y hy

/- English proof (translation)
Establish `: NeZero ((χ.1 : ℕ) * MM D)` using `⟨mul_ne_zero χ.1.ne_zero (MM_ne_zero D)⟩`. Establish `hN1 : (χ.1 : ℕ) ∣ (χ.1 : ℕ) * MM D` using `Dvd.intro _ rfl`. Establish `hch : DirichletCharacter.changeLevel hN1 χ.2 = 1`. Use extensionality with `u`. Establish `hcop : Nat.Coprime (u : ZMod ((χ.1 : ℕ) * MM D)).val ((χ.1 : ℕ) * MM D)` using `ZMod.val_coe_unit_coprime u`.

Establish `hu : (((u : ZMod ((χ.1 : ℕ) * MM D)).val : ℤ) : ZMod ((χ.1 : ℕ) * MM D)) = u` using `by simp`. Establish `hic : IsCoprime ((u : ZMod ((χ.1 : ℕ) * MM D)).val : ℤ) (((χ.1 : ℕ) * MM D : ℕ) : ℤ)` using `Nat.isCoprime_iff_coprime.mpr hcop`. Rewrite using `[MulChar.one_apply_coe, ← hu, DirichletCharacter.changeLevel_eq_cast_of_dvd' _ _ hic]`. Simplify using `only [Int.cast_natCast]`. Rewrite using `[jnt_reads_apply D 1 χ h _ (Nat.Coprime.coprime_dvd_right (Dvd.intro_left _ rfl) hcop)]`.

Simplify using the standard rewrite rules. Conclude with `(DirichletCharacter.changeLevel_eq_one_iff hN1).mp hch`.
-/
theorem jnt_reads_one (D : D7) (χ : Σ N : ℕ+, DirichletCharacter ℂ N)
    (h : ZetaZeroFreeRegion.Reads D 1 χ) : χ.2 = 1 := by
  have : NeZero ((χ.1 : ℕ) * MM D) := ⟨mul_ne_zero χ.1.ne_zero (MM_ne_zero D)⟩
  have hN1 : (χ.1 : ℕ) ∣ (χ.1 : ℕ) * MM D := Dvd.intro _ rfl
  have hch : DirichletCharacter.changeLevel hN1 χ.2 = 1 := by
    ext u
    have hcop : Nat.Coprime (u : ZMod ((χ.1 : ℕ) * MM D)).val ((χ.1 : ℕ) * MM D) :=
      ZMod.val_coe_unit_coprime u
    have hu : (((u : ZMod ((χ.1 : ℕ) * MM D)).val : ℤ) : ZMod ((χ.1 : ℕ) * MM D)) = u := by simp
    have hic : IsCoprime ((u : ZMod ((χ.1 : ℕ) * MM D)).val : ℤ) (((χ.1 : ℕ) * MM D : ℕ) : ℤ) :=
      Nat.isCoprime_iff_coprime.mpr hcop
    rw [MulChar.one_apply_coe, ← hu, DirichletCharacter.changeLevel_eq_cast_of_dvd' _ _ hic]
    simp only [Int.cast_natCast]
    rw [jnt_reads_apply D 1 χ h _ (Nat.Coprime.coprime_dvd_right (Dvd.intro_left _ rfl) hcop)]
    simp
  exact (DirichletCharacter.changeLevel_eq_one_iff hN1).mp hch

/- English proof (translation)
Break down `Int.units_eq_one_or s with rfl | rfl` into its components or cases. Conclude with `⟨1, by simp⟩`. Take `⟨a, ha⟩` from `quadraticChar_exists_neg_one (F := ZMod p) (by rw [ZMod.ringChar_zmod_n]; exact hp)`. Conclude with `⟨a, by rw [ha]; simp⟩`.
-/
theorem jnt_exists_qc (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (s : ℤˣ) :
    ∃ r : ZMod p, quadraticChar (ZMod p) r = (s : ℤ) := by
  rcases Int.units_eq_one_or s with rfl | rfl
  · exact ⟨1, by simp⟩
  · obtain ⟨a, ha⟩ := quadraticChar_exists_neg_one (F := ZMod p) (by rw [ZMod.ringChar_zmod_n]; exact hp)
    exact ⟨a, by rw [ha]; simp⟩

/- English proof (translation)
Take `⟨u, rfl⟩` from `D.host.der.art_surj g`. Establish `hc : (u : ZMod D.host.condN).val.Coprime D.host.condN` using `ZMod.val_coe_unit_coprime u`. Use `⟨_, hc, ?_⟩` and prove the remaining obligations. Rewrite using `[Phi_of_coprime D hc]`. Use `congr 1`.

Conclude with `Units.ext (by simp)`.
-/
theorem Phi_surj (D : D7) (g : D.R.GG) : ∃ a : ℕ, a.Coprime (MM D) ∧ Phi D a = g := by
  obtain ⟨u, rfl⟩ := D.host.der.art_surj g
  have hc : (u : ZMod D.host.condN).val.Coprime D.host.condN := ZMod.val_coe_unit_coprime u
  refine ⟨_, hc, ?_⟩
  rw [Phi_of_coprime D hc]
  congr 1
  exact Units.ext (by simp)

/- English proof (translation)
Introduce `h1`. Apply `hψ` to reduce the goal to its premises. Establish `hN : (χ.1 : ℕ) = 1`. Establish `h2 : χ.2.conductor = χ.1` using `h.1`. Rewrite `h2` using `[h1, DirichletCharacter.conductor_one]`.

Conclude with `h2.symm`. Use extensionality with `g`. Take `⟨a, ha, rfl⟩` from `Phi_surj D g`. Rewrite using `[← jnt_reads_apply D ψ χ h a ha, h1, MulChar.one_apply ((ZMod.isUnit_iff_coprime a _).mpr (by rw [hN]; exact Nat.coprime_one_right a))]`. Simplify using the standard rewrite rules.
-/
theorem jnt_reads_ne_one (D : D7) (ψ : ZetaZeroFreeRegion.Chr D) (χ : Σ N : ℕ+, DirichletCharacter ℂ N)
    (h : ZetaZeroFreeRegion.Reads D ψ χ) (hψ : ψ ≠ 1) : χ.2 ≠ 1 := by
  intro h1
  apply hψ
  have hN : (χ.1 : ℕ) = 1 := by
    have h2 : χ.2.conductor = χ.1 := h.1
    rw [h1, DirichletCharacter.conductor_one] at h2
    exact h2.symm
  ext g
  obtain ⟨a, ha, rfl⟩ := Phi_surj D g
  rw [← jnt_reads_apply D ψ χ h a ha, h1,
    MulChar.one_apply ((ZMod.isUnit_iff_coprime a _).mpr (by rw [hN]; exact Nat.coprime_one_right a))]
  simp

section Analysis

open MeasureTheory Set Filter Topology

/- English proof (translation)
Establish `hs : (Set.range (fun n : ℕ => (n : ℝ))).Countable` using `Set.countable_range _`. Establish `Hd : ∀ x ∈ Ioo a b \ Set.range (fun n : ℕ => (n : ℝ)), HasDerivAt f (deriv f x) x`. Introduce `x hx`. Conclude with `(hd x hx.1 (fun n hn => hx.2 ⟨n, hn.symm⟩)).hasDerivAt`. Establish `Hi : IntervalIntegrable (deriv f) volume a b`.

Use `IntervalIntegrable.mono_fun' (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => B) volume a b) (measurable_deriv f).aestronglyMeasurable ?_` and prove the remaining obligations. Use `filter_upwards [ae_restrict_mem measurableSet_uIoc] with x hx`. Rewrite `hx` using `[uIoc_of_le hab]`. Conclude with `hB x (Ioc_subset_Icc_self hx)`. Rewrite using `[← integral_eq_of_hasDerivAt_off_countable_of_le f (deriv f) hab hs hc Hd Hi]`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem jnt_lip {f : ℝ → ℂ} {a b B : ℝ} (hab : a ≤ b) (hc : ContinuousOn f (Icc a b))
    (hd : ∀ x ∈ Ioo a b, (∀ n : ℕ, x ≠ n) → DifferentiableAt ℝ f x)
    (hB : ∀ x ∈ Icc a b, ‖deriv f x‖ ≤ B) : ‖f b - f a‖ ≤ B * (b - a) := by
  have hs : (Set.range (fun n : ℕ => (n : ℝ))).Countable := Set.countable_range _
  have Hd : ∀ x ∈ Ioo a b \ Set.range (fun n : ℕ => (n : ℝ)), HasDerivAt f (deriv f x) x := by
    intro x hx
    exact (hd x hx.1 (fun n hn => hx.2 ⟨n, hn.symm⟩)).hasDerivAt
  have Hi : IntervalIntegrable (deriv f) volume a b := by
    refine IntervalIntegrable.mono_fun'
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => B) volume a b)
      (measurable_deriv f).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with x hx
    rw [uIoc_of_le hab] at hx
    exact hB x (Ioc_subset_Icc_self hx)
  rw [← integral_eq_of_hasDerivAt_off_countable_of_le f (deriv f) hab hs hc Hd Hi]
  calc ‖∫ x in a..b, deriv f x‖ ≤ B * |b - a| :=
        intervalIntegral.norm_integral_le_of_norm_le_const
          (fun x hx => hB x (Ioc_subset_Icc_self (by rwa [uIoc_of_le hab] at hx)))
    _ = B * (b - a) := by rw [abs_of_nonneg (by linarith)]

def tM {N : ℕ} (χ : DirichletCharacter ℂ N) (M : ℕ) (t : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 M, (abelian₂ n : ℂ) * χ (n : ZMod N) * ((max (t / n - 1) 0 : ℝ) : ℂ)

/- English proof (translation)
Establish `hf : ⌊t⌋₊ ≤ M`. Simplify using `using Nat.floor_mono ht`. Unfold `tM sumLamChi`. Apply `Finset.sum_subset` to reduce the goal to its premises. Introduce `n hn`.

Simplify using `only [Finset.mem_Icc] at hn ⊢`. Use linear arithmetic over natural numbers and integers. Introduce `n hn hn'`. Simplify using `only [Finset.mem_Icc, not_and, not_le] at hn hn'`. Establish `hlt : ⌊t⌋₊ < n` using `hn' hn.1`.

Establish `ht' : t < n` using `Nat.lt_of_floor_lt hlt`. Establish `hpos : (0:ℝ) < n` using `by exact_mod_cast (by omega : 0 < n)`. Establish `h2 : t / n - 1 ≤ 0`. Rewrite using `[sub_nonpos, div_le_one hpos]`. Conclude with `ht'.le`.

Rewrite using `[max_eq_right h2]`. Simplify using the standard rewrite rules.
-/
theorem sumLamChi_eq_tM {N : ℕ} (χ : DirichletCharacter ℂ N) (M : ℕ) (t : ℝ) (ht : t ≤ M) :
    sumLamChi χ t = tM χ M t := by
  have hf : ⌊t⌋₊ ≤ M := by
    simpa using Nat.floor_mono ht
  unfold tM sumLamChi
  apply Finset.sum_subset
  · intro n hn
    simp only [Finset.mem_Icc] at hn ⊢
    omega
  · intro n hn hn'
    simp only [Finset.mem_Icc, not_and, not_le] at hn hn'
    have hlt : ⌊t⌋₊ < n := hn' hn.1
    have ht' : t < n := Nat.lt_of_floor_lt hlt
    have hpos : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have h2 : t / n - 1 ≤ 0 := by
      rw [sub_nonpos, div_le_one hpos]
      exact ht'.le
    rw [max_eq_right h2]
    simp

/- English proof (translation)
Unfold `tM`. Apply `continuous_finset_sum` to reduce the goal to its premises. Introduce `n _`. Establish `hc : Continuous (fun t : ℝ => max (t / n - 1) 0)` using `Continuous.max (by fun_prop) continuous_const`. Conclude with `continuous_const.mul (Complex.continuous_ofReal.comp hc)`.
-/
theorem tM_continuous {N : ℕ} (χ : DirichletCharacter ℂ N) (M : ℕ) : Continuous (tM χ M) := by
  unfold tM
  apply continuous_finset_sum
  intro n _
  have hc : Continuous (fun t : ℝ => max (t / n - 1) 0) := Continuous.max (by fun_prop) continuous_const
  exact continuous_const.mul (Complex.continuous_ofReal.comp hc)

/- English proof (translation)
Establish `hn' : (0:ℝ) < n` using `by exact_mod_cast hn`. Break down `lt_or_gt_of_ne hx with h | h` into its components or cases. Establish `he : (fun t : ℝ => ((max (t / n - 1) 0 : ℝ) : ℂ)) =ᶠ[nhds x] fun _ => (0:ℂ)` using `by filter_upwards [Iio_mem_nhds h] with t ht`. Establish `h2 : t / n - 1 ≤ 0`. Rewrite using `[sub_nonpos, div_le_one hn']`.

Conclude with `(Set.mem_Iio.mp ht).le`. Simplify using `[max_eq_right h2]`. Conclude with `(differentiableAt_const (0:ℂ)).congr_of_eventuallyEq he`. Establish `he : (fun t : ℝ => ((max (t / n - 1) 0 : ℝ) : ℂ)) =ᶠ[nhds x] fun t => ((t / n - 1 : ℝ) : ℂ)` using `by filter_upwards [Ioi_mem_nhds h] with t ht`. Establish `h2 : 0 ≤ t / n - 1`.

Rewrite using `[sub_nonneg, one_le_div hn']`. Conclude with `(Set.mem_Ioi.mp ht).le`. Rewrite using `[max_eq_left h2]`. Conclude with `(((hasDerivAt_id' x).div_const (n:ℝ)).sub_const 1).ofReal_comp.differentiableAt.congr_of_eventuallyEq he`.
-/
theorem jnt_diff_max (n : ℕ) (hn : 1 ≤ n) (x : ℝ) (hx : x ≠ n) :
    DifferentiableAt ℝ (fun t : ℝ => ((max (t / n - 1) 0 : ℝ) : ℂ)) x := by
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  rcases lt_or_gt_of_ne hx with h | h
  · have he : (fun t : ℝ => ((max (t / n - 1) 0 : ℝ) : ℂ)) =ᶠ[nhds x] fun _ => (0:ℂ) := by
      filter_upwards [Iio_mem_nhds h] with t ht
      have h2 : t / n - 1 ≤ 0 := by
        rw [sub_nonpos, div_le_one hn']
        exact (Set.mem_Iio.mp ht).le
      simp [max_eq_right h2]
    exact (differentiableAt_const (0:ℂ)).congr_of_eventuallyEq he
  · have he : (fun t : ℝ => ((max (t / n - 1) 0 : ℝ) : ℂ)) =ᶠ[nhds x] fun t => ((t / n - 1 : ℝ) : ℂ) := by
      filter_upwards [Ioi_mem_nhds h] with t ht
      have h2 : 0 ≤ t / n - 1 := by
        rw [sub_nonneg, one_le_div hn']
        exact (Set.mem_Ioi.mp ht).le
      rw [max_eq_left h2]
    exact (((hasDerivAt_id' x).div_const (n:ℝ)).sub_const 1).ofReal_comp.differentiableAt.congr_of_eventuallyEq he

/- English proof (translation)
Unfold `tM`. Establish `hd : ∀ n ∈ Finset.Icc 1 M, DifferentiableAt ℝ (fun t : ℝ => (abelian₂ n : ℂ) * χ (n : ZMod N) * ((max (t / n - 1) 0 : ℝ) : ℂ)) x`. Introduce `n hn`. Conclude with `(differentiableAt_const _).mul (jnt_diff_max n (Finset.mem_Icc.mp hn).1 x (hx n))`. Use `first`.

Consider the case `exact DifferentiableAt.fun_sum hd`. Consider the case `exact DifferentiableAt.sum hd`. Consider the case `(convert DifferentiableAt.sum hd using 1; ext t; simp [Finset.sum_apply])`.
-/
theorem tM_differentiableAt {N : ℕ} (χ : DirichletCharacter ℂ N) (M : ℕ) (x : ℝ)
    (hx : ∀ n : ℕ, x ≠ n) : DifferentiableAt ℝ (tM χ M) x := by
  unfold tM
  have hd : ∀ n ∈ Finset.Icc 1 M, DifferentiableAt ℝ
      (fun t : ℝ => (abelian₂ n : ℂ) * χ (n : ZMod N) * ((max (t / n - 1) 0 : ℝ) : ℂ)) x := by
    intro n hn
    exact (differentiableAt_const _).mul (jnt_diff_max n (Finset.mem_Icc.mp hn).1 x (hx n))
  first
    | exact DifferentiableAt.fun_sum hd
    | exact DifferentiableAt.sum hd
    | (convert DifferentiableAt.sum hd using 1; ext t; simp [Finset.sum_apply])

/- English proof (translation)
Establish `hbM : b ≤ (⌈b⌉₊ : ℝ)` using `Nat.le_ceil b`. Establish `heq : ∀ t ∈ Icc a b, sumLamChi χ t + h t = tM χ ⌈b⌉₊ t + h t`. Introduce `t ht`. Rewrite using `[sumLamChi_eq_tM χ ⌈b⌉₊ t (ht.2.trans hbM)]`. Use `jnt_lip (f := fun t => sumLamChi χ t + h t) hab ?_ ?_ hB` and prove the remaining obligations.

Conclude with `((tM_continuous χ ⌈b⌉₊).continuousOn.add hc).congr heq`. Introduce `x hx hxn`. Establish `hev : (fun t => sumLamChi χ t + h t) =ᶠ[nhds x] fun t => tM χ ⌈b⌉₊ t + h t` using `by filter_upwards [Iio_mem_nhds (hx.2.trans_le hbM)] with t ht`. Rewrite using `[sumLamChi_eq_tM χ ⌈b⌉₊ t (Set.mem_Iio.mp ht).le]`. Conclude with `((tM_differentiableAt χ ⌈b⌉₊ x hxn).add (hd x hx)).congr_of_eventuallyEq hev`.
-/
theorem jnt_lip_sum {N : ℕ} (χ : DirichletCharacter ℂ N) (h : ℝ → ℂ) {a b B : ℝ} (hab : a ≤ b)
    (hc : ContinuousOn h (Icc a b)) (hd : ∀ x ∈ Ioo a b, DifferentiableAt ℝ h x)
    (hB : ∀ x ∈ Icc a b, ‖deriv (fun t => sumLamChi χ t + h t) x‖ ≤ B) :
    ‖(sumLamChi χ b + h b) - (sumLamChi χ a + h a)‖ ≤ B * (b - a) := by
  have hbM : b ≤ (⌈b⌉₊ : ℝ) := Nat.le_ceil b
  have heq : ∀ t ∈ Icc a b, sumLamChi χ t + h t = tM χ ⌈b⌉₊ t + h t := by
    intro t ht
    rw [sumLamChi_eq_tM χ ⌈b⌉₊ t (ht.2.trans hbM)]
  refine jnt_lip (f := fun t => sumLamChi χ t + h t) hab ?_ ?_ hB
  · exact ((tM_continuous χ ⌈b⌉₊).continuousOn.add hc).congr heq
  · intro x hx hxn
    have hev : (fun t => sumLamChi χ t + h t) =ᶠ[nhds x] fun t => tM χ ⌈b⌉₊ t + h t := by
      filter_upwards [Iio_mem_nhds (hx.2.trans_le hbM)] with t ht
      rw [sumLamChi_eq_tM χ ⌈b⌉₊ t (Set.mem_Iio.mp ht).le]
    exact ((tM_differentiableAt χ ⌈b⌉₊ x hxn).add (hd x hx)).congr_of_eventuallyEq hev

/- English proof (translation)
Use function extensionality and compare the values at `t`. Unfold `gChi`. Rewrite using `[if_neg hχ]`.
-/
theorem gChi_eq_of_ne_one {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) :
    (fun t : ℝ => gChi χ t) = fun t => sumLamChi χ t + (t : ℂ) * logDerivativeAtOne χ := by
  funext t
  unfold gChi
  rw [if_neg hχ]

/- English proof (translation)
Use function extensionality and compare the values at `t`. Unfold `gChi`. Rewrite using `[if_pos hχ]`.
-/
theorem gChi_one {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ = 1) :
    (fun t : ℝ => gChi χ t) = fun t => ((G t : ℝ) : ℂ) := by
  funext t
  unfold gChi
  rw [if_pos hχ]

/- English proof (translation)
Unfold `G sumLamChi`. Establish `h1 : ∀ n : ℕ, (1 : DirichletCharacter ℂ 1) (n : ZMod 1) = 1`. Introduce `n`. Establish `hu : IsUnit (n : ZMod 1)`. Establish `h2` using `(ZMod.unitOfCoprime n (Nat.coprime_one_right n)).isUnit`.

Rewrite `h2` using `[ZMod.coe_unitOfCoprime]`. Then use the resulting hypothesis. Conclude with `MulChar.one_apply hu`. Simplify using `only [h1, mul_one]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem G_cast (t : ℝ) : ((G t : ℝ) : ℂ) = sumLamChi (1 : DirichletCharacter ℂ 1) t +
    (-((t * (Real.log t - 1 - Real.eulerMascheroniConstant) : ℝ) : ℂ)) := by
  unfold G sumLamChi
  have h1 : ∀ n : ℕ, (1 : DirichletCharacter ℂ 1) (n : ZMod 1) = 1 := by
    intro n
    have hu : IsUnit (n : ZMod 1) := by
      have h2 := (ZMod.unitOfCoprime n (Nat.coprime_one_right n)).isUnit
      rwa [ZMod.coe_unitOfCoprime] at h2
    exact MulChar.one_apply hu
  simp only [h1, mul_one]
  push_cast
  ring

/- English proof (translation)
Establish `hg` using `gChi_eq_of_ne_one χ hχ`. Establish `hdl : ∀ x : ℝ, DifferentiableAt ℝ (fun t : ℝ => (t : ℂ) * logDerivativeAtOne χ) x` using `fun x => ((hasDerivAt_id' x).ofReal_comp.mul_const (logDerivativeAtOne χ)).differentiableAt`. Establish `key` using `jnt_lip_sum χ (fun t : ℝ => (t : ℂ) * logDerivativeAtOne χ) (B := Real.log y₂ + C + ‖logDerivativeAtOne χ‖) h12 (fun x _ => (hdl x).continuousAt.continuousWithinAt) (fun x _ => hdl x) (fun x hx => by`. Establish `hx1` using `hc x (h1.trans hx.1)`. Rewrite `hx1` using `[hg]`.

Use `hx1.trans ?_` and prove the remaining obligations. Establish `hlog : Real.log x ≤ Real.log y₂` using `Real.log_le_log (by linarith [hx.1]) hx.2`. Use the proof step `linarith)`. Establish `e1 : gChi χ y₂ = sumLamChi χ y₂ + (y₂ : ℂ) * logDerivativeAtOne χ` using `congrFun hg y₂`. Establish `e2 : gChi χ y₁ = sumLamChi χ y₁ + (y₁ : ℂ) * logDerivativeAtOne χ` using `congrFun hg y₁`.

Rewrite using `[e1, e2]`. Conclude with `key`.
-/
theorem jnt_c_int_ne {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (C : ℝ)
    (hc : ∀ y : ℝ, 1 ≤ y → ‖deriv (fun t : ℝ => gChi χ t) y‖ ≤ Real.log y + C + ‖logDerivativeAtOne χ‖)
    (y₁ y₂ : ℝ) (h1 : 1 ≤ y₁) (h12 : y₁ ≤ y₂) :
    ‖gChi χ y₂ - gChi χ y₁‖ ≤ (Real.log y₂ + C + ‖logDerivativeAtOne χ‖) * (y₂ - y₁) := by
  have hg := gChi_eq_of_ne_one χ hχ
  have hdl : ∀ x : ℝ, DifferentiableAt ℝ (fun t : ℝ => (t : ℂ) * logDerivativeAtOne χ) x :=
    fun x => ((hasDerivAt_id' x).ofReal_comp.mul_const (logDerivativeAtOne χ)).differentiableAt
  have key := jnt_lip_sum χ (fun t : ℝ => (t : ℂ) * logDerivativeAtOne χ) (B := Real.log y₂ + C + ‖logDerivativeAtOne χ‖) h12
    (fun x _ => (hdl x).continuousAt.continuousWithinAt) (fun x _ => hdl x)
    (fun x hx => by
      have hx1 := hc x (h1.trans hx.1)
      rw [hg] at hx1
      refine hx1.trans ?_
      have hlog : Real.log x ≤ Real.log y₂ := Real.log_le_log (by linarith [hx.1]) hx.2
      linarith)
  have e1 : gChi χ y₂ = sumLamChi χ y₂ + (y₂ : ℂ) * logDerivativeAtOne χ := congrFun hg y₂
  have e2 : gChi χ y₁ = sumLamChi χ y₁ + (y₁ : ℂ) * logDerivativeAtOne χ := congrFun hg y₁
  rw [e1, e2]
  exact key

/- English proof (translation)
Distinguish the cases in `hg : DifferentiableAt ℝ g y`. Conclude with `hg.hasDerivAt.ofReal_comp.deriv`. Rewrite using `[deriv_zero_of_not_differentiableAt hg, deriv_zero_of_not_differentiableAt]`. Simplify using the standard rewrite rules. Introduce `h`.

Apply `hg` to reduce the goal to its premises. Establish `h2` using `Complex.reCLM.differentiableAt.comp y h`. Simplify `h2` using `[Function.comp_def]`.
-/
theorem jnt_deriv_ofReal (g : ℝ → ℝ) (y : ℝ) :
    deriv (fun t : ℝ => ((g t : ℝ) : ℂ)) y = ((deriv g y : ℝ) : ℂ) := by
  by_cases hg : DifferentiableAt ℝ g y
  · exact hg.hasDerivAt.ofReal_comp.deriv
  · rw [deriv_zero_of_not_differentiableAt hg, deriv_zero_of_not_differentiableAt]
    · simp
    · intro h
      apply hg
      have h2 := Complex.reCLM.differentiableAt.comp y h
      simpa [Function.comp_def] using h2

/- English proof (translation)
Establish `hdh : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ (fun t : ℝ => (-((t * (Real.log t - 1 - Real.eulerMascheroniConstant) : ℝ) : ℂ))) x`. Introduce `x hx`. Conclude with `((((hasDerivAt_id' x).mul (((Real.hasDerivAt_log hx.ne').sub_const 1).sub_const Real.eulerMascheroniConstant)).ofReal_comp).neg).differentiableAt`. Establish `hfun : (fun t : ℝ => sumLamChi (1 : DirichletCharacter ℂ 1) t + (-((t * (Real.log t - 1 - Real.eulerMascheroniConstant) : ℝ) : ℂ))) = fun t => ((G t : ℝ) : ℂ)`. Use function extensionality and compare the values at `t`.

Rewrite using `[G_cast]`. Establish `key` using `jnt_lip_sum (1 : DirichletCharacter ℂ 1) (fun t : ℝ => (-((t * (Real.log t - 1 - Real.eulerMascheroniConstant) : ℝ) : ℂ))) (B := C) h12 (fun x hx => (hdh x (by linarith [hx.1])).continuousAt.continuousWithinAt) (fun x hx => hdh x (by linarith [hx.1])) (fun x hx => by`. Establish `hd1 : deriv (fun t : ℝ => sumLamChi (1 : DirichletCharacter ℂ 1) t + (-((t * (Real.log t - 1 - Real.eulerMascheroniConstant) : ℝ) : ℂ))) x = ((deriv G x : ℝ) : ℂ)`. Rewrite using `[hfun, jnt_deriv_ofReal]`. Use `show ‖deriv (fun t : ℝ => sumLamChi (1 : DirichletCharacter ℂ 1) t + (-((t * (Real.log t - 1 - Real.eulerMascheroniConstant) : ℝ) : ℂ))) x‖ ≤ C`.

Rewrite using `[hd1]`. Simplify using `using hc x (h1.trans hx.1))`. Rewrite using `[G_cast y₂, G_cast y₁]`. Conclude with `key`.
-/
theorem jnt_c_int_one (C : ℝ) (hc : ∀ y : ℝ, 1 ≤ y → |deriv G y| ≤ C)
    (y₁ y₂ : ℝ) (h1 : 1 ≤ y₁) (h12 : y₁ ≤ y₂) :
    ‖((G y₂ : ℝ) : ℂ) - ((G y₁ : ℝ) : ℂ)‖ ≤ C * (y₂ - y₁) := by
  have hdh : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ
      (fun t : ℝ => (-((t * (Real.log t - 1 - Real.eulerMascheroniConstant) : ℝ) : ℂ))) x := by
    intro x hx
    exact ((((hasDerivAt_id' x).mul (((Real.hasDerivAt_log hx.ne').sub_const 1).sub_const
      Real.eulerMascheroniConstant)).ofReal_comp).neg).differentiableAt
  have hfun : (fun t : ℝ => sumLamChi (1 : DirichletCharacter ℂ 1) t +
      (-((t * (Real.log t - 1 - Real.eulerMascheroniConstant) : ℝ) : ℂ))) = fun t => ((G t : ℝ) : ℂ) := by
    funext t
    rw [G_cast]
  have key := jnt_lip_sum (1 : DirichletCharacter ℂ 1)
    (fun t : ℝ => (-((t * (Real.log t - 1 - Real.eulerMascheroniConstant) : ℝ) : ℂ))) (B := C) h12
    (fun x hx => (hdh x (by linarith [hx.1])).continuousAt.continuousWithinAt)
    (fun x hx => hdh x (by linarith [hx.1]))
    (fun x hx => by
      have hd1 : deriv (fun t : ℝ => sumLamChi (1 : DirichletCharacter ℂ 1) t +
          (-((t * (Real.log t - 1 - Real.eulerMascheroniConstant) : ℝ) : ℂ))) x = ((deriv G x : ℝ) : ℂ) := by
        rw [hfun, jnt_deriv_ofReal]
      show ‖deriv (fun t : ℝ => sumLamChi (1 : DirichletCharacter ℂ 1) t +
          (-((t * (Real.log t - 1 - Real.eulerMascheroniConstant) : ℝ) : ℂ))) x‖ ≤ C
      rw [hd1]
      simpa using hc x (h1.trans hx.1))
  rw [G_cast y₂, G_cast y₁]
  exact key

/- English proof (translation)
Unfold `sumLamChi`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `n hn`. Rewrite `hn` using `[Finset.mem_Icc]`. Establish `h1 : (1:ℝ) ≤ n` using `by exact_mod_cast hn.1`.

Establish `h2 : y / n - 1 ≤ 0`. Rewrite using `[sub_nonpos, div_le_one (by linarith)]`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[max_eq_right h2]`. Simplify using the standard rewrite rules.
-/
theorem sumLamChi_eq_zero_of_le_one {N : ℕ} (χ : DirichletCharacter ℂ N) {y : ℝ} (hy : y ≤ 1) :
    sumLamChi χ y = 0 := by
  unfold sumLamChi
  apply Finset.sum_eq_zero
  intro n hn
  rw [Finset.mem_Icc] at hn
  have h1 : (1:ℝ) ≤ n := by exact_mod_cast hn.1
  have h2 : y / n - 1 ≤ 0 := by
    rw [sub_nonpos, div_le_one (by linarith)]
    linarith
  rw [max_eq_right h2]
  simp

/- English proof (translation)
Unfold `G`. Establish `hs : ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, abelian₂ n * max (y / n - 1) 0 = 0`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `n hn`. Rewrite `hn` using `[Finset.mem_Icc]`.

Establish `h1 : (1:ℝ) ≤ n` using `by exact_mod_cast hn.1`. Establish `h2 : y / n - 1 ≤ 0`. Rewrite using `[sub_nonpos, div_le_one (by linarith)]`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[max_eq_right h2, mul_zero]`.

Rewrite using `[hs, zero_sub]`.
-/
theorem G_eq_of_le_one {y : ℝ} (hy : y ≤ 1) :
    G y = -(y * (Real.log y - 1 - Real.eulerMascheroniConstant)) := by
  unfold G
  have hs : ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, abelian₂ n * max (y / n - 1) 0 = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    rw [Finset.mem_Icc] at hn
    have h1 : (1:ℝ) ≤ n := by exact_mod_cast hn.1
    have h2 : y / n - 1 ≤ 0 := by
      rw [sub_nonpos, div_le_one (by linarith)]
      linarith
    rw [max_eq_right h2, mul_zero]
  rw [hs, zero_sub]

/- English proof (translation)
Establish `hw1 : 0 < w1` using `lt_of_lt_of_le ha h1`. Establish `hw2 : 0 < w2` using `lt_of_lt_of_le hw1 h12`. Establish `hy1 : a / w1 ≤ 1` using `(div_le_one hw1).mpr h1`. Establish `hy2 : a / w2 ≤ 1` using `(div_le_one hw2).mpr (h1.trans h12)`. Establish `hlog : 0 ≤ Real.log (w2 / w1)` using `Real.log_nonneg ((one_le_div hw1).mpr h12)`.

Distinguish the cases in `hχ : χ = 1`. Unfold `gChi`. Rewrite using `[if_pos hχ, if_pos hχ]`. Establish `er : w2 * G (a / w2) - w1 * G (a / w1) = a * Real.log (w2 / w1)`. Rewrite using `[G_eq_of_le_one hy1, G_eq_of_le_one hy2, Real.log_div ha.ne' hw1.ne', Real.log_div ha.ne' hw2.ne', Real.log_div hw2.ne' hw1.ne']`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_sub, er, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg ha.le hlog)]`. Use polynomial arithmetic with `[mul_nonneg ha.le hlog]`. Unfold `gChi`.

Rewrite using `[if_neg hχ, if_neg hχ, sumLamChi_eq_zero_of_le_one χ hy1, sumLamChi_eq_zero_of_le_one χ hy2]`. Establish `e0 : (w2 : ℂ) * (0 + ((a / w2 : ℝ) : ℂ) * logDerivativeAtOne χ) - (w1 : ℂ) * (0 + ((a / w1 : ℝ) : ℂ) * logDerivativeAtOne χ) = 0`. Establish `c1 : (w1 : ℂ) ≠ 0` using `by exact_mod_cast hw1.ne'`. Establish `c2 : (w2 : ℂ) ≠ 0` using `by exact_mod_cast hw2.ne'`. Use `push_cast`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e0, norm_zero]`. Conclude with `mul_nonneg (by linarith) hlog`.
-/
theorem jnt_d_large {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {a w1 w2 : ℝ} (ha : 0 < a)
    (h1 : a ≤ w1) (h12 : w1 ≤ w2) :
    ‖(w2 : ℂ) * gChi χ (a / w2) - (w1 : ℂ) * gChi χ (a / w1)‖ ≤ 3 * a * Real.log (w2 / w1) := by
  have hw1 : 0 < w1 := lt_of_lt_of_le ha h1
  have hw2 : 0 < w2 := lt_of_lt_of_le hw1 h12
  have hy1 : a / w1 ≤ 1 := (div_le_one hw1).mpr h1
  have hy2 : a / w2 ≤ 1 := (div_le_one hw2).mpr (h1.trans h12)
  have hlog : 0 ≤ Real.log (w2 / w1) := Real.log_nonneg ((one_le_div hw1).mpr h12)
  by_cases hχ : χ = 1
  · unfold gChi
    rw [if_pos hχ, if_pos hχ]
    have er : w2 * G (a / w2) - w1 * G (a / w1) = a * Real.log (w2 / w1) := by
      rw [G_eq_of_le_one hy1, G_eq_of_le_one hy2, Real.log_div ha.ne' hw1.ne', Real.log_div ha.ne' hw2.ne',
        Real.log_div hw2.ne' hw1.ne']
      field_simp
      ring
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_sub, er, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (mul_nonneg ha.le hlog)]
    nlinarith [mul_nonneg ha.le hlog]
  · unfold gChi
    rw [if_neg hχ, if_neg hχ, sumLamChi_eq_zero_of_le_one χ hy1, sumLamChi_eq_zero_of_le_one χ hy2]
    have e0 : (w2 : ℂ) * (0 + ((a / w2 : ℝ) : ℂ) * logDerivativeAtOne χ) -
        (w1 : ℂ) * (0 + ((a / w1 : ℝ) : ℂ) * logDerivativeAtOne χ) = 0 := by
      have c1 : (w1 : ℂ) ≠ 0 := by exact_mod_cast hw1.ne'
      have c2 : (w2 : ℂ) ≠ 0 := by exact_mod_cast hw2.ne'
      push_cast
      field_simp
      ring
    rw [e0, norm_zero]
    exact mul_nonneg (by linarith) hlog

end Analysis

/- English proof (translation)
The claim follows from `(jnt_prim_isCharED D ψ).1`.
-/
theorem jnt_prim_isPrimitive (D : D7) (ψ : ZetaZeroFreeRegion.Chr D) : (ZetaZeroFreeRegion.prim D ψ).2.IsPrimitive :=
  (jnt_prim_isCharED D ψ).1

/- English proof (translation)
Introduce `ψ`. Establish `hR` using `jnt_prim_reads D ψ (h10 ψ)`. Take `⟨ha, hb, hc, hc1, hci, hci1, hd⟩` from `h _ (ZetaZeroFreeRegion.prim D ψ).2 (jnt_prim_isPrimitive D ψ)`. Establish `hne : ψ ≠ 1 → (ZetaZeroFreeRegion.prim D ψ).2 ≠ 1` using `jnt_reads_ne_one D ψ _ hR`. Establish `heq : ψ = 1 → (ZetaZeroFreeRegion.prim D ψ).2 = 1`.

Introduce `h1`. Substitute `h1` using the available equality. Conclude with `jnt_reads_one D _ hR`. Simplify using `only [ZetaZeroFreeRegion.Gc, ZetaZeroFreeRegion.Lp]`. Use `⟨fun y hy => (ha y hy).2, fun hψ => hb (hne hψ) s.x s.one_lt_alt.le, fun y hy hψ => hc (hne hψ) y hy, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Introduce `y hy hψ`. Rewrite using `[gChi_one _ (heq hψ), jnt_deriv_ofReal, Complex.norm_real, Real.norm_eq_abs]`. Conclude with `hc1 y hy`. Introduce `y₁ y₂ h1 h2 hψ`. Conclude with `hci (hne hψ) y₁ y₂ h1 h2`.

Introduce `y₁ y₂ h1 h2 hψ`. Establish `e : ∀ t : ℝ, gChi (ZetaZeroFreeRegion.prim D ψ).2 t = ((G t : ℝ) : ℂ)` using `fun t => congrFun (gChi_one _ (heq hψ)) t`. Rewrite using `[e, e, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]`. Conclude with `hci1 y₁ y₂ h1 h2`. Introduce `a w₁ w₂ ha0 hw1 h12`.

Conclude with `hd a ha0 w₁ w₂ hw1 h12`.
-/
theorem chebyshev_condition_of_primitive_reading (D : D7) (s : Scale) (C : ℝ) (h10 : ZetaZeroFreeRegion.adm10 D) (h : ShortIntervalPrimes.Conclusion1 D C) :
    ZetaZeroFreeRegion.ArchimedeanSignatureMatching D s C := by
  intro ψ
  have hR := jnt_prim_reads D ψ (h10 ψ)
  obtain ⟨ha, hb, hc, hc1, hci, hci1, hd⟩ := h _ (ZetaZeroFreeRegion.prim D ψ).2 (jnt_prim_isPrimitive D ψ)
  have hne : ψ ≠ 1 → (ZetaZeroFreeRegion.prim D ψ).2 ≠ 1 := jnt_reads_ne_one D ψ _ hR
  have heq : ψ = 1 → (ZetaZeroFreeRegion.prim D ψ).2 = 1 := by
    intro h1
    subst h1
    exact jnt_reads_one D _ hR
  simp only [ZetaZeroFreeRegion.Gc, ZetaZeroFreeRegion.Lp]
  refine ⟨fun y hy => (ha y hy).2, fun hψ => hb (hne hψ) s.x s.one_lt_alt.le,
    fun y hy hψ => hc (hne hψ) y hy, ?_, ?_, ?_, ?_⟩
  · intro y hy hψ
    rw [gChi_one _ (heq hψ), jnt_deriv_ofReal, Complex.norm_real, Real.norm_eq_abs]
    exact hc1 y hy
  · intro y₁ y₂ h1 h2 hψ
    exact hci (hne hψ) y₁ y₂ h1 h2
  · intro y₁ y₂ h1 h2 hψ
    have e : ∀ t : ℝ, gChi (ZetaZeroFreeRegion.prim D ψ).2 t = ((G t : ℝ) : ℂ) :=
      fun t => congrFun (gChi_one _ (heq hψ)) t
    rw [e, e, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    exact hci1 y₁ y₂ h1 h2
  · intro a w₁ w₂ ha0 hw1 h12
    exact hd a ha0 w₁ w₂ hw1 h12

def LL (D : D7) : ℕ := D.host.QS * D.host.q * D.host.d

/- English proof (translation)
Conclude with `MM_ne_zero D`.
-/
theorem LL_ne_zero (D : D7) : LL D ≠ 0 := by
  exact MM_ne_zero D

instance (D : D7) : NeZero (LL D) := ⟨LL_ne_zero D⟩

/- English proof (translation)
Unfold `LL`. Conclude with `(D.host.tower_dvd.mul_right _).mul_right _`.
-/
theorem tower_dvd_conductor (D : D7) : 2 ^ (D.R.e + 2) ∣ LL D := by
  unfold LL
  exact (D.host.tower_dvd.mul_right _).mul_right _
/- English proof (translation)
Conclude with `⟨D.host.QS * D.host.d, by unfold LL; ring⟩`.
-/
theorem LL_dvdq (D : D7) : D.host.q ∣ LL D := by
  exact ⟨D.host.QS * D.host.d, by unfold LL; ring⟩
/- English proof (translation)
Unfold `LL`. Conclude with `dvd_mul_left _ _`.
-/
theorem LL_dvdd (D : D7) : D.host.d ∣ LL D := by
  unfold LL
  exact dvd_mul_left _ _
/- English proof (translation)
Unfold `MM LL`. Conclude with `dvd_rfl`.
-/
theorem MM_dvd_LL (D : D7) : MM D ∣ LL D := by
  unfold MM LL
  exact dvd_rfl

/- English proof (translation)
Rewrite using `[Phi_of_coprime D ha, Phi_of_coprime D hb]`. Use `congr 1`. Conclude with `Units.ext h`.
-/
theorem Phi_congr (D : D7) {a b : ℕ} (ha : a.Coprime (MM D)) (hb : b.Coprime (MM D))
    (h : (a : ZMod (LL D)) = b) : Phi D a = Phi D b := by
  rw [Phi_of_coprime D ha, Phi_of_coprime D hb]
  congr 1
  exact Units.ext h

/- English proof (translation)
Conclude with `Phi_congr D hx ha (by rw [ZMod.natCast_zmod_val]; exact h)`.
-/
theorem Phi_val (D : D7) (x : ZMod (LL D)) (a : ℕ) (hx : x.val.Coprime (MM D))
    (ha : a.Coprime (MM D)) (h : x = (a : ZMod (LL D))) : Phi D x.val = Phi D a := by
  exact Phi_congr D hx ha (by rw [ZMod.natCast_zmod_val]; exact h)

/- English proof (translation)
The claim follows from `Nat.Coprime.coprime_dvd_right (MM_dvd_LL D) (ZMod.val_coe_unit_coprime u)`.
-/
theorem unit_cop (D : D7) (u : (ZMod (LL D))ˣ) : (u : ZMod (LL D)).val.Coprime (MM D) :=
  Nat.Coprime.coprime_dvd_right (MM_dvd_LL D) (ZMod.val_coe_unit_coprime u)

def Theta (D : D7) : (ZMod (LL D))ˣ →* D.R.GG where
  toFun u := Phi D (u : ZMod (LL D)).val
  map_one' := by
    rw [← Phi_one D]
    exact Phi_val D _ 1 (unit_cop D 1) (Nat.coprime_one_left _) (by simp)
  map_mul' u v := by
    rw [← Phi_mul D (unit_cop D u) (unit_cop D v)]
    exact Phi_val D _ _ (unit_cop D (u * v)) (Nat.Coprime.mul_left (unit_cop D u) (unit_cop D v))
      (by push_cast; simp)

/- English proof (translation)
Introduce `hd` and use `h.2 ((D.host.dvd_discr_iff_dvd_condN h.1).2 hd)`.
-/
theorem not_dvd_condN_of_unram' (D : D7) (p : ℕ) (h : ZetaZeroFreeRegion.Unram D p) : ¬ p ∣ D.host.condN :=
  fun hd => h.2 ((D.host.dvd_discr_iff_dvd_condN h.1).2 hd)

/- English proof (translation)
Introduce `ψ`. Set `χ₀ : DirichletCharacter ℂ (LL D)` to `MulChar.ofUnitHom (ψ.comp (Theta D))`. Establish `hc0 : 0 < χ₀.conductor` using `Nat.pos_of_ne_zero (DirichletCharacter.conductor_ne_zero χ₀)`. Use `⟨⟨⟨χ₀.conductor, hc0⟩, χ₀.primitiveCharacter⟩, DirichletCharacter.primitiveCharacter_isPrimitive χ₀, ?_⟩` and prove the remaining obligations. Introduce `p hp`.

Establish `hN` using `not_dvd_condN_of_unram' D p hp`. Establish `hpp` using `hp.1`. Establish `cL : p.Coprime (LL D)` using `hpp.coprime_iff_not_dvd.2 hN`. Establish `cM : p.Coprime (MM D)` using `Nat.Coprime.coprime_dvd_right (MM_dvd_LL D) cL`. Establish `hic : IsCoprime (p : ℤ) ((LL D : ℕ) : ℤ)` using `Nat.isCoprime_iff_coprime.mpr cL`.

Establish `e1` using `DirichletCharacter.primitiveCharacter_apply_of_isCoprime χ₀ hic`. Simplify using `only [Int.cast_natCast] at e1`. Use `show χ₀.primitiveCharacter (p : ZMod χ₀.conductor) = _`. Rewrite using `[e1, jnt_frob_eq D p hpp hN, ← ZMod.coe_unitOfCoprime p cL, MulChar.ofUnitHom_coe]`. Establish `e2 : Theta D (ZMod.unitOfCoprime p cL) = Phi D p` using `Phi_val D _ p (unit_cop D _) cM (ZMod.coe_unitOfCoprime p cL)`.

Rewrite using `[MonoidHom.comp_apply, e2]`.
-/
theorem _root_.Formalism.MainNotions.ZetaZeroFreeRegion.primitive_reading_holds (D : D7) : ZetaZeroFreeRegion.adm10 D := by
  intro ψ
  let χ₀ : DirichletCharacter ℂ (LL D) := MulChar.ofUnitHom (ψ.comp (Theta D))
  have hc0 : 0 < χ₀.conductor := Nat.pos_of_ne_zero (DirichletCharacter.conductor_ne_zero χ₀)
  refine ⟨⟨⟨χ₀.conductor, hc0⟩, χ₀.primitiveCharacter⟩,
    DirichletCharacter.primitiveCharacter_isPrimitive χ₀, ?_⟩
  intro p hp
  have hN := not_dvd_condN_of_unram' D p hp
  have hpp := hp.1
  have cL : p.Coprime (LL D) := hpp.coprime_iff_not_dvd.2 hN
  have cM : p.Coprime (MM D) := Nat.Coprime.coprime_dvd_right (MM_dvd_LL D) cL
  have hic : IsCoprime (p : ℤ) ((LL D : ℕ) : ℤ) := Nat.isCoprime_iff_coprime.mpr cL
  have e1 := DirichletCharacter.primitiveCharacter_apply_of_isCoprime χ₀ hic
  simp only [Int.cast_natCast] at e1
  show χ₀.primitiveCharacter (p : ZMod χ₀.conductor) = _
  rw [e1, jnt_frob_eq D p hpp hN, ← ZMod.coe_unitOfCoprime p cL, MulChar.ofUnitHom_coe]
  have e2 : Theta D (ZMod.unitOfCoprime p cL) = Phi D p :=
    Phi_val D _ p (unit_cop D _) cM (ZMod.coe_unitOfCoprime p cL)
  rw [MonoidHom.comp_apply, e2]

/- English proof (translation)
Conclude with `chebyshev_condition_of_primitive_reading D s C (Formalism.MainNotions.ZetaZeroFreeRegion.primitive_reading_holds D) h`.
-/
theorem _root_.Formalism.MainNotions.ZetaZeroFreeRegion.fourth_hypothesis_of_lifting (D : D7) (s : Scale) (C : ℝ) (h : ShortIntervalPrimes.Conclusion1 D C) : ZetaZeroFreeRegion.ArchimedeanSignatureMatching D s C := by
  exact chebyshev_condition_of_primitive_reading D s C (Formalism.MainNotions.ZetaZeroFreeRegion.primitive_reading_holds D) h

/- English proof (translation)
Conclude with `character_bounds_of_proposition_five D s C (Formalism.MainNotions.ZetaZeroFreeRegion.primitive_reading_holds D) h`.
-/
theorem _root_.Formalism.MainNotions.ZetaZeroFreeRegion.restriction_dimension_of_division (D : D7) (s : Scale) (C : ℝ) (h : ShortIntervalPrimes.PrimesAsPropTwoFive D s.x s.eps C) : ZetaZeroFreeRegion.adm6 D s C := by
  exact character_bounds_of_proposition_five D s C (Formalism.MainNotions.ZetaZeroFreeRegion.primitive_reading_holds D) h

/- English proof (translation)
The claim follows from `log_deriv_L_one_eq_of_induces D _ _ (8 * D.host.q * D.host.d) (mul_ne_zero (mul_ne_zero (by norm_num) D.host.hyp.1.ne_zero) D.host.hyp.2.1.ne_zero) (jnt_induces_ch D _ (jnt_prim_reads D _ (ZetaZeroFreeRegion.primitive_reading_holds D _)))`.
-/
theorem _root_.Formalism.MainNotions.ZetaZeroFreeRegion.Lp_chC_eq (D : D7) : ZetaZeroFreeRegion.Lp D (ZetaZeroFreeRegion.chC D) = ((dlogL D 1 : ℝ) : ℂ) :=
  log_deriv_L_one_eq_of_induces D _ _ (8 * D.host.q * D.host.d)
    (mul_ne_zero (mul_ne_zero (by norm_num) D.host.hyp.1.ne_zero) D.host.hyp.2.1.ne_zero)
    (jnt_induces_ch D _ (jnt_prim_reads D _ (ZetaZeroFreeRegion.primitive_reading_holds D _)))

end ConductorDivisibility

namespace ConductorLiftingHypotheses

section

open ConductorDivisibility

/- English proof (translation)
Assemble the required witnesses or components as `⟨D.host.hyp.1⟩`.
-/
theorem factQ (D : D7) : Fact D.host.q.Prime := ⟨D.host.hyp.1⟩
/- English proof (translation)
Assemble the required witnesses or components as `⟨D.host.hyp.2.1⟩`.
-/
theorem factD (D : D7) : Fact D.host.d.Prime := ⟨D.host.hyp.2.1⟩

attribute [local instance] factQ factD

abbrev Md (D : D7) : Formalism.LFunctionChainParameters.characterSumData.ArithData D.R.A := UpperTheory.Comparison₂.arith D.host.toHostRaw

def Teq (e : Formalism.HC.Frame) : e.GG ≃ Formalism.D5.E0 × e.A :=
  Equiv.ofBijective (fun g => (UpperTheory.Comparison₂.toE e g).toAdd)
    (Multiplicative.toAdd.bijective.comp (UpperTheory.Comparison₂.toE_bij e).1)

/- English proof (translation)
Simplify using `only [Teq, Equiv.ofBijective_apply, map_mul, toAdd_mul]`.
-/
theorem Teq_mul (e : Formalism.HC.Frame) (g g' : e.GG) : Teq e (g * g') = Teq e g + Teq e g' := by
  simp only [Teq, Equiv.ofBijective_apply, map_mul, toAdd_mul]

/- English proof (translation)
Simplify using `only [Teq, Equiv.ofBijective_apply, map_one, toAdd_one]`.
-/
theorem Teq_one (e : Formalism.HC.Frame) : Teq e 1 = 0 := by
  simp only [Teq, Equiv.ofBijective_apply, map_one, toAdd_one]

/- English proof (translation)
Simplify using `only [Teq, Equiv.ofBijective_apply, map_pow, toAdd_pow]`.
-/
theorem Teq_pow (e : Formalism.HC.Frame) (g : e.GG) (i : ℕ) : Teq e (g ^ i) = i • Teq e g := by
  simp only [Teq, Equiv.ofBijective_apply, map_pow, toAdd_pow]

/- English proof (translation)
Apply `(Teq e).injective` to reduce the goal to its premises. Rewrite using `[Teq_mul, Equiv.apply_symm_apply, Equiv.apply_symm_apply, Equiv.apply_symm_apply]`.
-/
theorem Teq_symm_add (e : Formalism.HC.Frame) (x y : Formalism.D5.E0 × e.A) :
    (Teq e).symm (x + y) = (Teq e).symm x * (Teq e).symm y := by
  apply (Teq e).injective
  rw [Teq_mul, Equiv.apply_symm_apply, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

def psiA (D : D7) (ψ : ZetaZeroFreeRegion.Chr D) : AddChar (Formalism.D5.E0 × D.R.A) ℂ where
  toFun x := ((ψ ((Teq D.R.toFrame).symm x) : ℂˣ) : ℂ)
  map_zero_eq_one' := by
    have h : (Teq D.R.toFrame).symm 0 = 1 := by rw [Equiv.symm_apply_eq, Teq_one]
    simp [h]
  map_add_eq_mul' x y := by
    rw [Teq_symm_add, map_mul, Units.val_mul]

/- English proof (translation)
Use `show ((ψ ((Teq D.R.toFrame).symm (Teq D.R.toFrame g)) : ℂˣ) : ℂ) = _`. Rewrite using `[Equiv.symm_apply_apply]`.
-/
theorem psiA_Teq_eq_chr (D : D7) (ψ : ZetaZeroFreeRegion.Chr D) (g : D.R.GG) :
    psiA D ψ (Teq D.R.toFrame g) = ((ψ g : ℂˣ) : ℂ) := by
  show ((ψ ((Teq D.R.toFrame).symm (Teq D.R.toFrame g)) : ℂˣ) : ℂ) = _
  rw [Equiv.symm_apply_apply]

/- English proof (translation)
The claim follows from `(D.host.gal).apply_symm_apply g`.
-/
theorem galE_sigmaOf (D : D7) (g : D.R.GG) :
    D.host.galE (D.host.sigmaOf g) = g :=
  (D.host.gal).apply_symm_apply g

/- English proof (translation)
The claim follows from `UpperTheory.GL.dataField D.host.toHostAx p P σ`.
-/
theorem fld (D : D7) (p : ℕ) [Fact p.Prime] (P : Ideal (𝓞 D.host.E)) [P.IsPrime]
    [P.LiesOver (Ideal.span {(p : ℤ)})] (σ : D.host.E ≃ₐ[ℚ] D.host.E) :
    ((∀ x : 𝓞 D.host.E, σ • x - x ∈ P) ↔
      Teq D.R.toFrame (D.host.galE σ) ∈ (Md D).inertia p) ∧
    (IsArithFrobAt ℤ σ P ↔
      Teq D.R.toFrame (D.host.galE σ) - (Md D).frob p ∈ (Md D).inertia p) :=
  UpperTheory.GL.dataField D.host.toHostAx p P σ

/- English proof (translation)
Unfold `ZetaZeroFreeRegion.inerP`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨σ, rfl, hσ⟩`. Conclude with `((fld D p P σ).1).mp hσ`.

Introduce `h`. Use `⟨D.host.sigmaOf g, galE_sigmaOf D g, ((fld D p P _).1).mpr ?_⟩` and prove the remaining obligations. Rewrite using `[galE_sigmaOf]` and apply the resulting hypothesis.
-/
theorem mem_inerP (D : D7) (p : ℕ) [Fact p.Prime] (P : Ideal (𝓞 D.host.E)) [P.IsPrime]
    [P.LiesOver (Ideal.span {(p : ℤ)})] (g : D.R.GG) :
    g ∈ ZetaZeroFreeRegion.inerP D P ↔ Teq D.R.toFrame g ∈ (Md D).inertia p := by
  unfold ZetaZeroFreeRegion.inerP
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨σ, rfl, hσ⟩
    exact ((fld D p P σ).1).mp hσ
  · intro h
    refine ⟨D.host.sigmaOf g, galE_sigmaOf D g, ((fld D p P _).1).mpr ?_⟩
    rwa [galE_sigmaOf]

/- English proof (translation)
Establish `hex : ∃ σ : D.host.E ≃ₐ[ℚ] D.host.E, ∃ P : Ideal (𝓞 D.host.E), P.IsPrime ∧ P.LiesOver (Ideal.span {(p : ℤ)}) ∧ IsArithFrobAt ℤ σ P`. Use `⟨D.host.sigmaOf ((Teq D.R.toFrame).symm ((Md D).frob p)), P, hP, hlo, ((fld D p P _).2).mpr ?_⟩` and prove the remaining obligations. Rewrite using `[galE_sigmaOf, Equiv.apply_symm_apply, sub_self]`. Conclude with `zero_mem _`. Unfold `frob`.

Rewrite using `[dif_pos hex]`. Take `⟨P', hP', hlo', hfr⟩` from `hex.choose_spec`. Conclude with `((fld D p P' hex.choose).2).mp hfr`.
-/
theorem frob_mem (D : D7) (p : ℕ) [Fact p.Prime] (P : Ideal (𝓞 D.host.E)) [hP : P.IsPrime]
    [hlo : P.LiesOver (Ideal.span {(p : ℤ)})] :
    Teq D.R.toFrame (frob D p) - (Md D).frob p ∈ (Md D).inertia p := by
  have hex : ∃ σ : D.host.E ≃ₐ[ℚ] D.host.E, ∃ P : Ideal (𝓞 D.host.E),
      P.IsPrime ∧ P.LiesOver (Ideal.span {(p : ℤ)}) ∧ IsArithFrobAt ℤ σ P := by
    refine ⟨D.host.sigmaOf ((Teq D.R.toFrame).symm ((Md D).frob p)), P, hP, hlo, ((fld D p P _).2).mpr ?_⟩
    rw [galE_sigmaOf, Equiv.apply_symm_apply, sub_self]
    exact zero_mem _
  unfold frob
  rw [dif_pos hex]
  obtain ⟨P', hP', hlo', hfr⟩ := hex.choose_spec
  exact ((fld D p P' hex.choose).2).mp hfr

/- English proof (translation)
Unfold `Formalism.LFunctionChainParameters.characterSumData.cosetMean`. Establish `hs' : Finset.univ.filter (fun x => x ∈ I) = s`. Use extensionality with `x`. Simplify using `[hs]`. Simplify using `only [hs']`.
-/
theorem cosetMean_of {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
    (I : AddSubgroup (Formalism.D5.E0 × H)) (h : Formalism.D5.E0 × H) (ψ : AddChar (Formalism.D5.E0 × H) ℂ)
    (s : Finset (Formalism.D5.E0 × H)) (hs : ∀ x, x ∈ s ↔ x ∈ I) :
    Formalism.LFunctionChainParameters.characterSumData.cosetMean I h ψ = (∑ x ∈ s, ψ (h + x)) / (s.card : ℂ) := by
  classical
  unfold Formalism.LFunctionChainParameters.characterSumData.cosetMean
  have hs' : Finset.univ.filter (fun x => x ∈ I) = s := by
    ext x
    simp [hs]
  simp only [hs']

/- English proof (translation)
Establish `hs : ∀ x, x ∈ (ZetaZeroFreeRegion.inerP D P).map (Teq D.R.toFrame).toEmbedding ↔ x ∈ (Md D).inertia p`. Introduce `x`. Simplify using `only [Finset.mem_map, Equiv.coe_toEmbedding]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨g, hg, rfl⟩`.

Conclude with `(mem_inerP D p P g).mp hg`. Introduce `hx`. Use `⟨(Teq D.R.toFrame).symm x, (mem_inerP D p P _).mpr ?_, Equiv.apply_symm_apply _ _⟩` and prove the remaining obligations. Rewrite using `[Equiv.apply_symm_apply]` and apply the resulting hypothesis. Rewrite using `[cosetMean_of _ _ _ _ hs, Finset.card_map, Finset.sum_map, Finset.sum_image (fun a _ b _ hab => mul_left_cancel hab), div_eq_mul_inv, one_div, mul_comm]`.

Use `congr 1`. Establish `hy` using `frob_mem D p P`. Use `set y := Teq D.R.toFrame (frob D p) - (Md D).frob p with hydef`. Establish `hTφ : Teq D.R.toFrame (frob D p) = (Md D).frob p + y` using `by rw [hydef]; abel`. Use `set g0 : D.R.GG := (Teq D.R.toFrame).symm (i • y) with hg0`.

Establish `hTg0 : Teq D.R.toFrame g0 = i • y` using `Equiv.apply_symm_apply _ _`. Establish `hiy : i • y ∈ (Md D).inertia p` using `nsmul_mem hy i`. Use `symm`. Use `Finset.sum_equiv (Equiv.mulLeft g0) ?_ ?_` and prove the remaining obligations. Introduce `g`.

Rewrite using `[mem_inerP D p P, mem_inerP D p P, Equiv.coe_mulLeft, Teq_mul, hTg0]`. Conclude with `((Md D).inertia p).add_mem_cancel_left hiy |>.symm`. Introduce `g _`. Rewrite using `[← psiA_Teq_eq_chr, Teq_mul, Teq_pow, hTφ, Equiv.coe_mulLeft, Equiv.coe_toEmbedding, Teq_mul, hTg0, nsmul_add]`. Use `congr 1`.

Normalize the expressions using the abelian group laws.
-/
theorem mean_eq (D : D7) (ψ : ZetaZeroFreeRegion.Chr D) (p : ℕ) [Fact p.Prime] (P : Ideal (𝓞 D.host.E)) [P.IsPrime]
    [P.LiesOver (Ideal.span {(p : ℤ)})] (i : ℕ) :
    Formalism.LFunctionChainParameters.characterSumData.cosetMean ((Md D).inertia p) (i • (Md D).frob p) (psiA D ψ) =
      (1 / ((ZetaZeroFreeRegion.inerP D P).card : ℂ)) *
        ∑ g ∈ (ZetaZeroFreeRegion.inerP D P).image (fun g => frob D p ^ i * g), ((ψ g : ℂˣ) : ℂ) := by
  classical
  have hs : ∀ x, x ∈ (ZetaZeroFreeRegion.inerP D P).map (Teq D.R.toFrame).toEmbedding ↔ x ∈ (Md D).inertia p := by
    intro x
    simp only [Finset.mem_map, Equiv.coe_toEmbedding]
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact (mem_inerP D p P g).mp hg
    · intro hx
      refine ⟨(Teq D.R.toFrame).symm x, (mem_inerP D p P _).mpr ?_, Equiv.apply_symm_apply _ _⟩
      rwa [Equiv.apply_symm_apply]
  rw [cosetMean_of _ _ _ _ hs, Finset.card_map, Finset.sum_map,
    Finset.sum_image (fun a _ b _ hab => mul_left_cancel hab), div_eq_mul_inv, one_div, mul_comm]
  congr 1

  have hy := frob_mem D p P
  set y := Teq D.R.toFrame (frob D p) - (Md D).frob p with hydef
  have hTφ : Teq D.R.toFrame (frob D p) = (Md D).frob p + y := by rw [hydef]; abel
  set g0 : D.R.GG := (Teq D.R.toFrame).symm (i • y) with hg0
  have hTg0 : Teq D.R.toFrame g0 = i • y := Equiv.apply_symm_apply _ _
  have hiy : i • y ∈ (Md D).inertia p := nsmul_mem hy i
  symm
  refine Finset.sum_equiv (Equiv.mulLeft g0) ?_ ?_
  · intro g
    rw [mem_inerP D p P, mem_inerP D p P, Equiv.coe_mulLeft, Teq_mul, hTg0]
    exact ((Md D).inertia p).add_mem_cancel_left hiy |>.symm
  · intro g _
    rw [← psiA_Teq_eq_chr, Teq_mul, Teq_pow, hTφ, Equiv.coe_mulLeft, Equiv.coe_toEmbedding, Teq_mul, hTg0,
      nsmul_add]
    congr 1
    abel

/- English proof (translation)
Conclude with `ConductorDivisibility.MM_ne_zero D`.
-/
theorem hostN_ne (D : D7) : D.host.condN ≠ 0 := by
  exact ConductorDivisibility.MM_ne_zero D

def chi0 (D : D7) (ψ : ZetaZeroFreeRegion.Chr D) : DirichletCharacter ℂ D.host.condN :=
  Formalism.LFunctionChainParameters.LHost.dirChar (UpperTheory.Comparison₂.recH D.host.toHostRaw) (psiA D ψ)

/- English proof (translation)
Use `haveI : NeZero D.host.condN := ⟨hostN_ne D⟩`. Use `first`. Consider the case `exact Nat.pos_of_ne_zero (DirichletCharacter.conductor_ne_zero _ (hostN_ne D))`. Consider the case `exact Nat.pos_of_ne_zero (DirichletCharacter.conductor_ne_zero _)`.
-/
theorem induced_character_conductor_pos (D : D7) (ψ : ZetaZeroFreeRegion.Chr D) : 0 < (chi0 D ψ).conductor := by
  haveI : NeZero D.host.condN := ⟨hostN_ne D⟩
  first
    | exact Nat.pos_of_ne_zero (DirichletCharacter.conductor_ne_zero _ (hostN_ne D))
    | exact Nat.pos_of_ne_zero (DirichletCharacter.conductor_ne_zero _)

def chiM (D : D7) (ψ : ZetaZeroFreeRegion.Chr D) : Σ N : ℕ+, DirichletCharacter ℂ N :=
  ⟨⟨(chi0 D ψ).conductor, induced_character_conductor_pos D ψ⟩, (chi0 D ψ).primitiveCharacter⟩

/- English proof (translation)
Rewrite using `[← Formalism.LFunctionChainParameters.characterSumData.primitive_value_pow (Md D) (psiA D ψ) p i hp hi]`. Conclude with `(Formalism.LFunctionChainParameters.LHost.primitive_value_primitive D.host.condN D.host.q D.host.d (UpperTheory.Comparison₂.recH D.host.toHostRaw) (psiA D ψ) (p ^ i) (hostN_ne D) (pow_ne_zero _ hp.ne_zero)).symm`.
-/
theorem chiM_apply (D : D7) (ψ : ZetaZeroFreeRegion.Chr D) (p i : ℕ) (hp : p.Prime) (hi : 1 ≤ i) :
    (chiM D ψ).2 ((p ^ i : ℕ) : ZMod (chiM D ψ).1) =
      Formalism.LFunctionChainParameters.characterSumData.cosetMean ((Md D).inertia p) (i • (Md D).frob p) (psiA D ψ) := by
  rw [← Formalism.LFunctionChainParameters.characterSumData.primitive_value_pow (Md D) (psiA D ψ) p i hp hi]
  exact (Formalism.LFunctionChainParameters.LHost.primitive_value_primitive D.host.condN
    D.host.q D.host.d (UpperTheory.Comparison₂.recH D.host.toHostRaw) (psiA D ψ) (p ^ i)
    (hostN_ne D) (pow_ne_zero _ hp.ne_zero)).symm

/- English proof (translation)
Use `⟨DirichletCharacter.primitiveCharacter_isPrimitive _, ?_⟩` and prove the remaining obligations. Introduce `p hp`. Establish `hN` using `not_dvd_condN_of_unram' D p hp`. Establish `hpp` using `hp.1`. Establish `: Fact p.Prime` using `⟨hpp⟩`.

Establish `hpZ : Prime (p : ℤ)` using `Nat.prime_iff_prime_int.mp hpp`. Establish `: (Ideal.span {(p : ℤ)}).IsPrime` using `(Ideal.span_singleton_prime hpZ.ne_zero).mpr hpZ`. Take `⟨P, hP⟩` from `(inferInstance : Nonempty (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 D.host.E)))`. Use `hP.1` as an intermediate fact. Use `hP.2` as an intermediate fact.

Establish `h1` using `chiM_apply D ψ p 1 hpp le_rfl`. Rewrite `h1` using `[pow_one, one_nsmul]`. Rewrite using `[h1]`. Establish `hbot : (Md D).inertia p = ⊥` using `(UpperTheory.GL.unram D.host.toHostRaw p (hpp.coprime_iff_not_dvd.2 hN) hpp).1`. Establish `hfr` using `frob_mem D p P`.

Rewrite `hfr` using `[hbot, AddSubgroup.mem_bot, sub_eq_zero]`. Rewrite using `[hbot, cosetMean_of ⊥ _ _ {0} (by intro x; simp [AddSubgroup.mem_bot]), ← hfr]`. Simplify using `[psiA_Teq_eq_chr]`.
-/
theorem reads_model (D : D7) (ψ : ZetaZeroFreeRegion.Chr D) : ZetaZeroFreeRegion.Reads D ψ (chiM D ψ) := by
  refine ⟨DirichletCharacter.primitiveCharacter_isPrimitive _, ?_⟩
  intro p hp
  have hN := not_dvd_condN_of_unram' D p hp
  have hpp := hp.1
  have : Fact p.Prime := ⟨hpp⟩
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hpp
  have : (Ideal.span {(p : ℤ)}).IsPrime := (Ideal.span_singleton_prime hpZ.ne_zero).mpr hpZ
  obtain ⟨P, hP⟩ := (inferInstance : Nonempty (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 D.host.E)))
  have := hP.1
  have := hP.2
  have h1 := chiM_apply D ψ p 1 hpp le_rfl
  rw [pow_one, one_nsmul] at h1
  rw [h1]
  have hbot : (Md D).inertia p = ⊥ :=
    (UpperTheory.GL.unram D.host.toHostRaw p (hpp.coprime_iff_not_dvd.2 hN) hpp).1
  have hfr := frob_mem D p P
  rw [hbot, AddSubgroup.mem_bot, sub_eq_zero] at hfr
  rw [hbot, cosetMean_of ⊥ _ _ {0} (by intro x; simp [AddSubgroup.mem_bot]), ← hfr]
  simp [psiA_Teq_eq_chr]

/- English proof (translation)
Introduce `p hpp _ P hP hlo i hi ψ`. Establish `: Fact p.Prime` using `⟨hpp⟩`. Establish `hr1` using `jnt_prim_reads D ψ (ZetaZeroFreeRegion.primitive_reading_holds D ψ)`. Establish `hr2` using `reads_model D ψ`. Establish `hM : MM D ≠ 0` using `MM_ne_zero D`.

Rewrite using `[prim_unique (ZetaZeroFreeRegion.prim D ψ).2 (chiM D ψ).2 hr1.1 hr2.1 (MM D) hM (fun a ha => (jnt_reads_apply D ψ _ hr1 a ha).trans (jnt_reads_apply D ψ _ hr2 a ha).symm) (p ^ i), chiM_apply D ψ p i hpp hi, mean_eq D ψ p P i]`.
-/
theorem _root_.Formalism.MainNotions.ZetaZeroFreeRegion.zero_window_bound_holds (D : D7) : ZetaZeroFreeRegion.adm11 D := by
  intro p hpp _ P hP hlo i hi ψ
  have : Fact p.Prime := ⟨hpp⟩
  have hr1 := jnt_prim_reads D ψ (ZetaZeroFreeRegion.primitive_reading_holds D ψ)
  have hr2 := reads_model D ψ
  have hM : MM D ≠ 0 := MM_ne_zero D
  rw [prim_unique (ZetaZeroFreeRegion.prim D ψ).2 (chiM D ψ).2 hr1.1 hr2.1 (MM D) hM
    (fun a ha => (jnt_reads_apply D ψ _ hr1 a ha).trans (jnt_reads_apply D ψ _ hr2 a ha).symm) (p ^ i),
    chiM_apply D ψ p i hpp hi, mean_eq D ψ p P i]

end

end ConductorLiftingHypotheses

/- English proof (translation)
Introduce `u` and use `(h u).1`.
-/
theorem _root_.Formalism.MainNotions.flipTwoThree.fourth_hypothesis_of_lifting (D : D7) (h : ∀ u, product_first_zeroth_parts.Conclusion6 D u) : flipTwoThree.ArchimedeanSignatureMatching D := fun u => (h u).1

/- English proof (translation)
Introduce `u` and use `by obtain ⟨-, -, -, ⟨hR, -, hb⟩, -⟩ := h u exact ⟨hR, hb⟩`.
-/
theorem _root_.Formalism.MainNotions.flipTwoThree.restriction_dimension_of_division (D : D7) (h : ∀ u, product_first_zeroth_parts.Conclusion6 D u) : flipTwoThree.adm6 D := fun u => by
  obtain ⟨-, -, -, ⟨hR, -, hb⟩, -⟩ := h u
  exact ⟨hR, hb⟩

/- English proof (translation)
The claim follows from `stabZero_of_level D Lv u h hD hP hgk`.
-/
theorem _root_.Formalism.MainNotions.product_first_zeroth_parts.stabiliser_admissible_of_level (D : D7) (Lv : LevelData D) (u : D.what₂.Word) (h : UnusedSlot33.division_rows_rational_lattice D)
    (hD : letI := D.host.cmStar; UnusedSlot33.IsDef D.sp.cm.sig D.sp.gram0)
    (hP : letI := D.host.cmStar; (Lv u).ProG) (hgk : StandardLattice.GBig D) : product_first_zeroth_parts.admS D u :=
  stabZero_of_level D Lv u h hD hP hgk

/- English proof (translation)
Take `⟨δ, hδ⟩` from `IsAlgClosed.exists_pow_nat_eq (TaylorLogMetric.discr (TaylorLogMetric.lamOf D D.host.ccK 1)) (by norm_num : 0 < 12)`. Take `⟨-, ⟨χ, hχ⟩, hall⟩` from `h D.host.ccK (jnt_ccK_curve D) δ hδ`. Take `⟨e, hv, -, he, hi, hm, -⟩` from `hall χ hχ`. Conclude with `⟨⟨D.host.ccK, δ, χ, e, jnt_ccK_curve D, hδ, hχ⟩, ⟨hv, he⟩, hi, hm⟩`.
-/
theorem _root_.Formalism.MainNotions.product_first_zeroth_parts.theta_conditions_of_theta_theorem (D : D7) (C : ℝ) (h : TaylorLogMetric.aux₃ D C) :
    ∃ G : product_first_zeroth_parts.Th22 D, product_first_zeroth_parts.adm1 G ∧ product_first_zeroth_parts.adm2 G ∧ product_first_zeroth_parts.adm3 G := by
  obtain ⟨δ, hδ⟩ := IsAlgClosed.exists_pow_nat_eq (TaylorLogMetric.discr (TaylorLogMetric.lamOf D D.host.ccK 1))
    (by norm_num : 0 < 12)
  obtain ⟨-, ⟨χ, hχ⟩, hall⟩ := h D.host.ccK (jnt_ccK_curve D) δ hδ
  obtain ⟨e, hv, -, he, hi, hm, -⟩ := hall χ hχ
  exact ⟨⟨D.host.ccK, δ, χ, e, jnt_ccK_curve D, hδ, hχ⟩, ⟨hv, he⟩, hi, hm⟩

namespace JSW

section

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain
open scoped TensorProduct ENNReal

/- English proof (translation)
Unfold `AllSome`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2⟩`. Conclude with `⟨h1, fun a ha => (h a ha).mp (h2 a ha)⟩`. Introduce and unpack `⟨h1, h2⟩`.

Conclude with `⟨h1, fun a ha => (h a ha).mpr (h2 a ha)⟩`.
-/
theorem as_congr {α : Sort*} {P Q Q' : α → Prop} (h : ∀ a, P a → (Q a ↔ Q' a)) :
    AllSome P Q ↔ AllSome P Q' := by
  unfold AllSome
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun a ha => (h a ha).mp (h2 a ha)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun a ha => (h a ha).mpr (h2 a ha)⟩

/- English proof (translation)
Unfold `AllSome`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨a, ha⟩, h2⟩`. Conclude with `⟨⟨a, (h a).mp ha⟩, fun b hb => h2 b ((h b).mpr hb)⟩`. Introduce and unpack `⟨⟨a, ha⟩, h2⟩`.

Conclude with `⟨⟨a, (h a).mpr ha⟩, fun b hb => h2 b ((h b).mp hb)⟩`.
-/
theorem as_congrP {α : Sort*} {P P' Q : α → Prop} (h : ∀ a, P a ↔ P' a) :
    AllSome P Q ↔ AllSome P' Q := by
  unfold AllSome
  constructor
  · rintro ⟨⟨a, ha⟩, h2⟩
    exact ⟨⟨a, (h a).mp ha⟩, fun b hb => h2 b ((h b).mpr hb)⟩
  · rintro ⟨⟨a, ha⟩, h2⟩
    exact ⟨⟨a, (h a).mpr ha⟩, fun b hb => h2 b ((h b).mp hb)⟩

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨a, ha⟩, h⟩`. Conclude with `⟨(h a ha).1, fun b hb => ⟨⟨a, ha⟩, fun a' ha' => (h a' ha').2 b hb⟩⟩`. Introduce and unpack `⟨⟨b, hb⟩, h⟩`. Conclude with `⟨(h b hb).1, fun a ha => ⟨⟨b, hb⟩, fun b' hb' => (h b' hb').2 a ha⟩⟩`.
-/
theorem as_swap {α β : Sort*} {P : α → Prop} {Q : β → Prop} {R : α → β → Prop} :
    AllSome P (fun a => AllSome Q (fun b => R a b)) ↔
      AllSome Q (fun b => AllSome P (fun a => R a b)) := by
  constructor
  · rintro ⟨⟨a, ha⟩, h⟩
    exact ⟨(h a ha).1, fun b hb => ⟨⟨a, ha⟩, fun a' ha' => (h a' ha').2 b hb⟩⟩
  · rintro ⟨⟨b, hb⟩, h⟩
    exact ⟨(h b hb).1, fun a ha => ⟨⟨b, hb⟩, fun b' hb' => (h b' hb').2 a ha⟩⟩

/- English proof (translation)
Unfold `AllSome`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨ha, hb, h⟩`. Conclude with `⟨ha, fun a ha' => ⟨hb, fun b hb' => h a b ha' hb'⟩⟩`. Introduce and unpack `⟨⟨a, ha⟩, h⟩`.

Conclude with `⟨⟨a, ha⟩, (h a ha).1, fun a' b ha' hb' => (h a' ha').2 b hb'⟩`.
-/
theorem as_two {α β : Sort*} {A : α → Prop} {B : β → Prop} {Q : α → β → Prop} :
    ((∃ a, A a) ∧ (∃ b, B b) ∧ ∀ a b, A a → B b → Q a b) ↔
      AllSome A fun a => AllSome B fun b => Q a b := by
  unfold AllSome
  constructor
  · rintro ⟨ha, hb, h⟩
    exact ⟨ha, fun a ha' => ⟨hb, fun b hb' => h a b ha' hb'⟩⟩
  · rintro ⟨⟨a, ha⟩, h⟩
    exact ⟨⟨a, ha⟩, (h a ha).1, fun a' b ha' hb' => (h a' ha').2 b hb'⟩

/- English proof (translation)
Unfold `AllSome`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨ha, hb, hc, hd, h⟩`. Conclude with `⟨ha, fun a ha' => ⟨hb, fun b hb' => ⟨hc, fun c hc' => ⟨hd, fun d hd' => h a b c d ha' hb' hc' hd'⟩⟩⟩⟩`. Introduce and unpack `⟨⟨a, ha⟩, h⟩`.

Take `⟨⟨b, hb⟩, h2⟩` from `h a ha`. Take `⟨⟨c, hc⟩, h3⟩` from `h2 b hb`. Conclude with `⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩, (h3 c hc).1, fun a' b' c' d' ha' hb' hc' hd' => (((h a' ha').2 b' hb').2 c' hc').2 d' hd'⟩`.
-/
theorem as_four {α β γ δ : Sort*} {A : α → Prop} {B : β → Prop} {C : γ → Prop} {Dd : δ → Prop}
    {Q : α → β → γ → δ → Prop} :
    ((∃ a, A a) ∧ (∃ b, B b) ∧ (∃ c, C c) ∧ (∃ d, Dd d) ∧
        ∀ a b c d, A a → B b → C c → Dd d → Q a b c d) ↔
      AllSome A fun a => AllSome B fun b => AllSome C fun c => AllSome Dd fun d => Q a b c d := by
  unfold AllSome
  constructor
  · rintro ⟨ha, hb, hc, hd, h⟩
    exact ⟨ha, fun a ha' => ⟨hb, fun b hb' => ⟨hc, fun c hc' => ⟨hd, fun d hd' => h a b c d ha' hb' hc' hd'⟩⟩⟩⟩
  · rintro ⟨⟨a, ha⟩, h⟩
    obtain ⟨⟨b, hb⟩, h2⟩ := h a ha
    obtain ⟨⟨c, hc⟩, h3⟩ := h2 b hb
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩, (h3 c hc).1,
      fun a' b' c' d' ha' hb' hc' hd' => (((h a' ha').2 b' hb').2 c' hc').2 d' hd'⟩

section SW
variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E)

/- English proof (translation)
The claim follows from `as_congr (P := IsHaarH F E σ M J) fun μ _ => as_congr (P := IsFDH F E σ M J μ) fun 𝓕 _ => h μ 𝓕`.
-/
theorem onH_congr {P P' : Measure (HA (AF F) σ J) → Set (HA (AF F) σ J) → Prop}
    (h : ∀ μ 𝓕, P μ 𝓕 ↔ P' μ 𝓕) : StandardLattice.OnH F E σ M J P ↔ StandardLattice.OnH F E σ M J P' :=
  as_congr (P := IsHaarH F E σ M J) fun μ _ => as_congr (P := IsFDH F E σ M J μ) fun 𝓕 _ => h μ 𝓕

/- English proof (translation)
The claim follows from `(as_swap (Q := IsHaarH F E σ M J) (R := fun ψ μ => AllSome (IsFDH F E σ M J μ) (R ψ μ))).trans (as_congr fun _ _ => as_swap)`.
-/
theorem onH_swap {γ : Sort*} {Pψ : γ → Prop}
    {R : γ → Measure (HA (AF F) σ J) → Set (HA (AF F) σ J) → Prop} :
    AllSome Pψ (fun ψ => StandardLattice.OnH F E σ M J (R ψ)) ↔
      AllSome (IsHaarH F E σ M J) fun μ => AllSome (IsFDH F E σ M J μ) fun 𝓕 =>
        AllSome Pψ fun ψ => R ψ μ 𝓕 :=
  (as_swap (Q := IsHaarH F E σ M J)
    (R := fun ψ μ => AllSome (IsFDH F E σ M J μ) (R ψ μ))).trans (as_congr fun _ _ => as_swap)

/- English proof (translation)
The claim follows from `as_four`.
-/
theorem onSD_iff (ψ : AddChar (AF F) ℂ) (n : ℕ) (Yi : Type) [AddCommGroup Yi] [TopologicalSpace Yi]
    [MeasurableSpace Yi] (Yv : HeightOneSpectrum (𝓞 F) → Type) [∀ v, AddCommGroup (Yv v)]
    [∀ v, TopologicalSpace (Yv v)] [∀ v, MeasurableSpace (Yv v)]
    (χi : Yi → Yi → ℂ) (χv : ∀ v, Yv v → Yv v → ℂ)
    (Q : Measure (Fin n → Fin M → Ainf F ⊗[F] E) → Measure Yi →
      (∀ v, Measure (Fin n → Fin M → Fv F v ⊗[F] E)) → (∀ v, Measure (Yv v)) → Prop) :
    StandardLattice.OnSD F E σ M J ψ n Yi Yv χi χv Q ↔
      AllSome (SdW F E σ M J (Ainf F) (psiInf F ψ) n) fun μi =>
      AllSome (fun νi : Measure Yi => SelfDual νi χi) fun νi =>
      AllSome (fun μv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fin M → Fv F v ⊗[F] E) =>
        ∀ v, SdW F E σ M J (Fv F v) (psiV F ψ v) n (μv v)) fun μv =>
      AllSome (fun νv : ∀ v, Measure (Yv v) => ∀ v, SelfDual (νv v) (χv v)) fun νv =>
        Q μi νi μv νv :=
  as_four

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem sw1a1_iff_swa1 : StandardLattice.SW1a1 F E σ M J ↔ UnusedSlot34.SWa1 F E σ M J := Iff.rfl

/- English proof (translation)
Unfold `StandardLattice.SW1a2 UnusedSlot34.SWa2`. Simplify using `only [ofReal_norm]`. Conclude with `Iff.rfl`.
-/
theorem sw1a2_iff_swa2 : StandardLattice.SW1a2 F E σ M J ↔ UnusedSlot34.SWa2 F E σ M J := by
  unfold StandardLattice.SW1a2 UnusedSlot34.SWa2
  simp only [ofReal_norm]
  exact Iff.rfl

/- English proof (translation)
Unfold `StandardLattice.SW1b1 UnusedSlot34.SWb1`. Use `imp_congr_right fun _ => forall_congr' fun β => forall_congr' fun d => forall_congr' fun b => forall_congr' fun Φ => forall_congr' fun Φi => forall_congr' fun Φf => forall_congr' fun Φv => imp_congr_right fun _ => imp_congr_right fun _ => imp_congr_right fun _ => imp_congr_right …` and prove the remaining obligations. Use `Iff.trans (as_congr fun ψ _ => onH_congr F E σ M J fun μ 𝓕 => onSD_iff F E σ M J ψ 1 _ _ _ _ _) ?_` and prove the remaining obligations. Conclude with `onH_swap F E σ M J`.
-/
theorem sw1b1_iff_swb1 : StandardLattice.SW1b1 F E σ M J ↔ UnusedSlot34.SWb1 F E σ M J := by
  unfold StandardLattice.SW1b1 UnusedSlot34.SWb1
  refine imp_congr_right fun _ => forall_congr' fun β => forall_congr' fun d => forall_congr' fun b =>
    forall_congr' fun Φ => forall_congr' fun Φi => forall_congr' fun Φf => forall_congr' fun Φv =>
    imp_congr_right fun _ => imp_congr_right fun _ => imp_congr_right fun _ =>
    imp_congr_right fun _ => ?_
  refine Iff.trans (as_congr fun ψ _ => onH_congr F E σ M J fun μ 𝓕 => onSD_iff F E σ M J ψ 1 _ _ _ _ _) ?_
  exact onH_swap F E σ M J

/- English proof (translation)
Unfold `StandardLattice.SW1c1 UnusedSlot34.SWc1`. Use `forall_congr' fun n => imp_congr_right fun _ => forall_congr' fun T => forall_congr' fun hT => imp_congr_right fun _ => forall_congr' fun d => forall_congr' fun b => forall_congr' fun Φ => forall_congr' fun Φi => forall_congr' fun Φf => forall_congr' fun Φv => imp_congr_right fun …` and prove the remaining obligations. Use `Iff.trans (as_congr fun ψ _ => onH_congr F E σ M J fun μ 𝓕 => onSD_iff F E σ M J ψ n _ _ _ _ _) ?_` and prove the remaining obligations. Conclude with `onH_swap F E σ M J`.
-/
theorem shintani_weight_c1_iff : StandardLattice.SW1c1 F E σ M J ↔ UnusedSlot34.SWc1 F E σ M J := by
  unfold StandardLattice.SW1c1 UnusedSlot34.SWc1
  refine forall_congr' fun n => imp_congr_right fun _ => forall_congr' fun T => forall_congr' fun hT =>
    imp_congr_right fun _ => forall_congr' fun d => forall_congr' fun b =>
    forall_congr' fun Φ => forall_congr' fun Φi => forall_congr' fun Φf => forall_congr' fun Φv =>
    imp_congr_right fun _ => imp_congr_right fun _ => imp_congr_right fun _ =>
    imp_congr_right fun _ => ?_
  refine Iff.trans (as_congr fun ψ _ => onH_congr F E σ M J fun μ 𝓕 => onSD_iff F E σ M J ψ n _ _ _ _ _) ?_
  exact onH_swap F E σ M J

/- English proof (translation)
Unfold `StandardLattice.SW1c2 UnusedSlot34.SWc2`. Use `forall_congr' fun p => imp_congr_right fun _ => forall_congr' fun d => forall_congr' fun b => forall_congr' fun Φ => forall_congr' fun Φi => forall_congr' fun Φf => forall_congr' fun Φv => imp_congr_right fun _ => imp_congr_right fun _ => imp_congr_right fun _ => imp_congr_right …` and prove the remaining obligations. Use `Iff.trans (as_congr fun ψ _ => onH_congr F E σ M J fun μ 𝓕 => (onSD_iff F E σ M J ψ p _ _ _ _ _).trans (as_congr fun _ _ => as_congr fun _ _ => as_congr fun _ _ => as_congr fun _ _ => as_two)) ?_` and prove the remaining obligations. Conclude with `onH_swap F E σ M J`.
-/
theorem shintani_weight_c2_iff : StandardLattice.SW1c2 F E σ M J ↔ UnusedSlot34.SWc2 F E σ M J := by
  unfold StandardLattice.SW1c2 UnusedSlot34.SWc2
  refine forall_congr' fun p => imp_congr_right fun _ => forall_congr' fun d => forall_congr' fun b =>
    forall_congr' fun Φ => forall_congr' fun Φi => forall_congr' fun Φf => forall_congr' fun Φv =>
    imp_congr_right fun _ => imp_congr_right fun _ => imp_congr_right fun _ =>
    imp_congr_right fun _ => ?_
  refine Iff.trans (as_congr fun ψ _ => onH_congr F E σ M J fun μ 𝓕 =>
    (onSD_iff F E σ M J ψ p _ _ _ _ _).trans (as_congr fun _ _ => as_congr fun _ _ =>
      as_congr fun _ _ => as_congr fun _ _ => as_two)) ?_
  exact onH_swap F E σ M J

/- English proof (translation)
The claim follows from `and_congr_right fun _ => (onSD_iff F E σ M J ψ 1 _ _ _ _ _).trans (as_congr fun _ _ => as_congr fun _ _ => as_congr fun _ _ => as_congr fun _ _ => as_two)`.
-/
theorem isDxDq_iff (ψ : AddChar (AF F) ℂ) (β : F) (ν : Measure (Fin 1 → Fin M → AF F ⊗[F] E)) :
    StandardLattice.IsDxDq F E σ M J ψ β ν ↔ IsXbetaMeasure F E σ M J ψ β ν :=
  and_congr_right fun _ => (onSD_iff F E σ M J ψ 1 _ _ _ _ _).trans
    (as_congr fun _ _ => as_congr fun _ _ => as_congr fun _ _ => as_congr fun _ _ => as_two)

/- English proof (translation)
Unfold `StandardLattice.SW1c3 UnusedSlot34.SWc3`. Use `imp_congr_right fun _ => forall_congr' fun x => forall_congr' fun β => imp_congr_right fun _ => imp_congr_right fun _ => imp_congr_right fun _ => ?_` and prove the remaining obligations. Use `as_congr fun ψ _ => as_congr (P := IsHaarH F E σ M J) fun μ _ => ?_` and prove the remaining obligations. Use `Iff.trans as_swap ?_` and prove the remaining obligations. Use `Iff.trans (as_congrP fun ν => isDxDq_iff F E σ M J ψ β ν) ?_` and prove the remaining obligations.

Conclude with `as_congr fun ν _ => as_swap`.
-/
theorem shintani_weight_c3_iff : StandardLattice.SW1c3 F E σ M J ↔ UnusedSlot34.SWc3 F E σ M J := by
  unfold StandardLattice.SW1c3 UnusedSlot34.SWc3
  refine imp_congr_right fun _ => forall_congr' fun x => forall_congr' fun β =>
    imp_congr_right fun _ => imp_congr_right fun _ => imp_congr_right fun _ => ?_
  refine as_congr fun ψ _ => as_congr (P := IsHaarH F E σ M J) fun μ _ => ?_
  refine Iff.trans as_swap ?_
  refine Iff.trans (as_congrP fun ν => isDxDq_iff F E σ M J ψ β ν) ?_
  exact as_congr fun ν _ => as_swap

/- English proof (translation)
Introduce `hM β hβ d b Φ Φinf Φf Φv hmeas hpos hpure hposv hprod`. Establish `h1` using `h hM β hβ d b (fun X => ENNReal.ofReal (Φ X).re) (fun X => ENNReal.ofReal (Φinf X).re) Φf Φv (Complex.measurable_re.comp hmeas).ennreal_ofReal hpure hposv (fun X => by`. Rewrite using `[hprod X, Complex.mul_re, (hpos _).2, zero_mul, sub_zero, ENNReal.ofReal_mul (hpos _).1])`. Conclude with `((as_congr fun ψ _ => onH_congr F E σ M J fun μ 𝓕 => (onSD_iff F E σ M J ψ 1 _ _ _ _ _).trans (as_congr fun _ _ => as_congr fun _ _ => as_congr fun _ _ => as_congr fun _ _ => as_two)).trans (onH_swap F E σ M J)).mp h1`.
-/
theorem shintani_weight_b2_of_extended (h : StandardLattice.SW1b2 F E σ M J) : UnusedSlot34.SWb2 F E σ M J := by
  intro hM β hβ d b Φ Φinf Φf Φv hmeas hpos hpure hposv hprod
  have h1 := h hM β hβ d b (fun X => ENNReal.ofReal (Φ X).re) (fun X => ENNReal.ofReal (Φinf X).re)
    Φf Φv (Complex.measurable_re.comp hmeas).ennreal_ofReal hpure hposv (fun X => by
      rw [hprod X, Complex.mul_re, (hpos _).2, zero_mul, sub_zero, ENNReal.ofReal_mul (hpos _).1])
  exact ((as_congr fun ψ _ => onH_congr F E σ M J fun μ 𝓕 =>
    (onSD_iff F E σ M J ψ 1 _ _ _ _ _).trans (as_congr fun _ _ => as_congr fun _ _ =>
      as_congr fun _ _ => as_congr fun _ _ => as_two)).trans (onH_swap F E σ M J)).mp h1

def SchurWeightFiniteness : Prop :=
  3 ≤ M → ∀ (β : F), β ≠ 0 → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E)
    (Φ : (Fin 1 → Fin M → AF F ⊗[F] E) → ℝ≥0∞) (Φi : (Fin 1 → Fin M → Ainf F ⊗[F] E) → ℝ≥0∞)
    (Φf : (Fin 1 → Fin M → Af F ⊗[F] E) → ℂ)
    (Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin 1 → Fin M → Fv F v ⊗[F] E) → ℂ),
    Measurable Φi → (∀ X, Φi X ≠ ⊤) → IsPureFin b Φf Φv → (∀ v Y, 0 ≤ (Φv v Y).re ∧ (Φv v Y).im = 0) →
    (∀ X, Φ X = Φi (projInf X) * ENNReal.ofReal (Φf (projFin X)).re) →
    AllSome (IsCharAF F) fun ψ =>
    StandardLattice.OnH F E σ M J fun μ 𝓕 =>
    StandardLattice.OnSD F E σ M J ψ 1 (Ainf F) (Fv F) (fun s t => psiInf F ψ (s * t)) (fun v s t => psiV F ψ v (s * t))
      fun μi νi μv νv =>
      (∃ fi : Ainf F → Measure (Fin 1 → Fin M → Ainf F ⊗[F] E),
        IsFibreFamily μi (fun X => qR (Ainf F) σ J (X 0)) id Set.univ νi {c | ∀ w, c w ≠ 0} fi) ∧
      (∃ fv : ∀ v, Fv F v → Measure (Fin 1 → Fin M → Fv F v ⊗[F] E),
        ∀ v, IsFibreFamily (μv v) (fun X => qR (Fv F v) σ J (X 0)) id Set.univ (νv v) {c | c ≠ 0}
          (fv v)) ∧
      ∀ (fi : Ainf F → Measure (Fin 1 → Fin M → Ainf F ⊗[F] E))
        (fv : ∀ v, Fv F v → Measure (Fin 1 → Fin M → Fv F v ⊗[F] E)),
        IsFibreFamily μi (fun X => qR (Ainf F) σ J (X 0)) id Set.univ νi {c | ∀ w, c w ≠ 0} fi →
        (∀ v, IsFibreFamily (μv v) (fun X => qR (Fv F v) σ J (X 0)) id Set.univ (νv v) {c | c ≠ 0}
          (fv v)) →
        Multipliable (fun v => ∫⁻ X, ENNReal.ofReal (Φv v X).re ∂(fv v (algebraMap F (Fv F v) β))) ∧
        meanL μ 𝓕 (fun h => ∑' x : {x : Fin 1 → Fin M → E | x 0 ≠ 0 ∧
            hE σ J (x 0) (x 0) = algebraMap F E β},
          Φ (h⁻¹ • ratTup (F := F) (AF F) (x : Fin 1 → Fin M → E))) =
        (∫⁻ X, Φi X ∂(fi (algebraMap F (Ainf F) β))) *
          ∏' v, ∫⁻ X, ENNReal.ofReal (Φv v X).re ∂(fv v (algebraMap F (Fv F v) β))

/- English proof (translation)
Apply `finprod_induction (p := fun z : ℂ => 0 ≤ z.re ∧ z.im = 0)` to reduce the goal to its premises. Simplify using the standard rewrite rules. Introduce and unpack `x y ⟨hx1, hx2⟩ ⟨hy1, hy2⟩`. Simplify using `only [Complex.mul_re, Complex.mul_im, hx2, hy2]`. Conclude with `⟨by simpa using mul_nonneg hx1 hy1, by ring⟩`.

Conclude with `h`.
-/
theorem jnt_finprod_real {ι : Type*} (f : ι → ℂ) (h : ∀ i, 0 ≤ (f i).re ∧ (f i).im = 0) :
    0 ≤ (∏ᶠ i, f i).re ∧ (∏ᶠ i, f i).im = 0 := by
  apply finprod_induction (p := fun z : ℂ => 0 ≤ z.re ∧ z.im = 0)
  · simp
  · rintro x y ⟨hx1, hx2⟩ ⟨hy1, hy2⟩
    simp only [Complex.mul_re, Complex.mul_im, hx2, hy2]
    exact ⟨by simpa using mul_nonneg hx1 hy1, by ring⟩
  · exact h

/- English proof (translation)
Introduce `hM β hβ d b Φ Φi Φf Φv hmeas hfin hpure hposv hprod`. Establish `hf : ∀ Y, 0 ≤ (Φf Y).re ∧ (Φf Y).im = 0` using `fun Y => by`. Rewrite using `[hpure.2.2 Y]`. Conclude with `jnt_finprod_real _ fun v => hposv v _`. Establish `hΦfin : ∀ X, Φ X ≠ ⊤` using `fun X => by`.

Rewrite using `[hprod X]`. Conclude with `ENNReal.mul_ne_top (hfin _) ENNReal.ofReal_ne_top`. Establish `e1 : ∀ X, ENNReal.ofReal ((((Φ X).toReal : ℝ) : ℂ)).re = Φ X` using `fun X => by`. Rewrite using `[Complex.ofReal_re, ENNReal.ofReal_toReal (hΦfin X)]`. Establish `e2 : ∀ X, ENNReal.ofReal ((((Φi X).toReal : ℝ) : ℂ)).re = Φi X` using `fun X => by`.

Rewrite using `[Complex.ofReal_re, ENNReal.ofReal_toReal (hfin X)]`. Establish `h1` using `h hM β hβ d b (fun X => (((Φ X).toReal : ℝ) : ℂ)) (fun X => (((Φi X).toReal : ℝ) : ℂ)) Φf Φv (Complex.measurable_ofReal.comp hmeas.ennreal_toReal) (fun X => ⟨by simp, by simp⟩) hpure hposv (fun X => by show (((Φ X).toReal : ℝ) : ℂ) = (((Φi (projInf X)).toReal : ℝ) : ℂ) * Φf (proj …`. Rewrite using `[hprod X, ENNReal.toReal_mul, ENNReal.toReal_ofReal (hf _).1, Complex.ofReal_mul]`. Use `congr 1`. Conclude with `Complex.ext (by simp) (by simp [(hf (projFin X)).2]))`.

Simplify using `only [e1, e2] at h1`. Conclude with `((as_congr fun ψ _ => onH_congr F E σ M J fun μ 𝓕 => (onSD_iff F E σ M J ψ 1 _ _ _ _ _).trans (as_congr fun _ _ => as_congr fun _ _ => as_congr fun _ _ => as_congr fun _ _ => as_two)).trans (onH_swap F E σ M J)).mpr h1`.
-/
theorem schur_weight_finiteness_of_swb2 (h : UnusedSlot34.SWb2 F E σ M J) : SchurWeightFiniteness F E σ M J := by
  intro hM β hβ d b Φ Φi Φf Φv hmeas hfin hpure hposv hprod
  have hf : ∀ Y, 0 ≤ (Φf Y).re ∧ (Φf Y).im = 0 := fun Y => by
    rw [hpure.2.2 Y]; exact jnt_finprod_real _ fun v => hposv v _
  have hΦfin : ∀ X, Φ X ≠ ⊤ := fun X => by
    rw [hprod X]; exact ENNReal.mul_ne_top (hfin _) ENNReal.ofReal_ne_top
  have e1 : ∀ X, ENNReal.ofReal ((((Φ X).toReal : ℝ) : ℂ)).re = Φ X := fun X => by
    rw [Complex.ofReal_re, ENNReal.ofReal_toReal (hΦfin X)]
  have e2 : ∀ X, ENNReal.ofReal ((((Φi X).toReal : ℝ) : ℂ)).re = Φi X := fun X => by
    rw [Complex.ofReal_re, ENNReal.ofReal_toReal (hfin X)]
  have h1 := h hM β hβ d b (fun X => (((Φ X).toReal : ℝ) : ℂ)) (fun X => (((Φi X).toReal : ℝ) : ℂ))
    Φf Φv (Complex.measurable_ofReal.comp hmeas.ennreal_toReal)
    (fun X => ⟨by simp, by simp⟩) hpure hposv (fun X => by
      show (((Φ X).toReal : ℝ) : ℂ) = (((Φi (projInf X)).toReal : ℝ) : ℂ) * Φf (projFin X)
      rw [hprod X, ENNReal.toReal_mul, ENNReal.toReal_ofReal (hf _).1, Complex.ofReal_mul]
      congr 1
      exact Complex.ext (by simp) (by simp [(hf (projFin X)).2]))
  simp only [e1, e2] at h1
  exact ((as_congr fun ψ _ => onH_congr F E σ M J fun μ 𝓕 =>
    (onSD_iff F E σ M J ψ 1 _ _ _ _ _).trans (as_congr fun _ _ => as_congr fun _ _ =>
      as_congr fun _ _ => as_congr fun _ _ => as_two)).trans (onH_swap F E σ M J)).mpr h1

end SW

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun F E _ _ _ _ _ σ hσ M J hJ => (sw1a1_iff_swa1 F E σ M J).mp (h F E σ hσ M J hJ).1, fun F E _ _ _ _ _ σ hσ M J hJ => (sw1a2_iff_swa2 F E σ M J).mp (h F E σ hσ M J hJ).2.1, fun F E _ _ _ _ _ σ hσ M J hJ => (sw1b1_iff_swb1 F E σ M J).mp (h F E σ hσ M J hJ).2.2.1, fun F E _ _ _ _ …`.
-/
theorem _root_.Formalism.MainNotions.UnusedSlot34.conclusion_of_standardLattice (D : D7) (h : StandardLattice.Conclusion1 D) : UnusedSlot34.Conclusion₂ :=
  ⟨fun F E _ _ _ _ _ σ hσ M J hJ => (sw1a1_iff_swa1 F E σ M J).mp (h F E σ hσ M J hJ).1,
   fun F E _ _ _ _ _ σ hσ M J hJ => (sw1a2_iff_swa2 F E σ M J).mp (h F E σ hσ M J hJ).2.1,
   fun F E _ _ _ _ _ σ hσ M J hJ => (sw1b1_iff_swb1 F E σ M J).mp (h F E σ hσ M J hJ).2.2.1,
   fun F E _ _ _ _ _ σ hσ M J hJ => shintani_weight_b2_of_extended F E σ M J (h F E σ hσ M J hJ).2.2.2.1,
   fun F E _ _ _ _ _ σ hσ M J hJ => (shintani_weight_c1_iff F E σ M J).mp (h F E σ hσ M J hJ).2.2.2.2.1,
   fun F E _ _ _ _ _ σ hσ M J hJ => (shintani_weight_c2_iff F E σ M J).mp (h F E σ hσ M J hJ).2.2.2.2.2.1,
   fun F E _ _ _ _ _ σ hσ M J hJ => (shintani_weight_c3_iff F E σ M J).mp (h F E σ hσ M J hJ).2.2.2.2.2.2⟩

/- English proof (translation)
Take `⟨h1, h2, h3, -, h5, h6, h7⟩` from `h`. Introduce `F E _ _ _ _ _ σ hσ M J hJ`. Conclude with `⟨(sw1a1_iff_swa1 F E σ M J).mpr (h1 F E σ hσ M J hJ), (sw1a2_iff_swa2 F E σ M J).mpr (h2 F E σ hσ M J hJ), (sw1b1_iff_swb1 F E σ M J).mpr (h3 F E σ hσ M J hJ), hb2 F E σ hσ M J hJ, (shintani_weight_c1_iff F E σ M J).mpr (h5 F E σ hσ M J hJ), (shintani_weight_c2_iff F E σ M J).mpr …`.
-/
theorem _root_.Formalism.MainNotions.StandardLattice.baseChange_preserves_unitary_of (D : D7) (h : UnusedSlot34.Conclusion₂)
    (hb2 : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
      (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
        StandardLattice.SW1b2 F E σ M J) : StandardLattice.Conclusion1 D := by
  obtain ⟨h1, h2, h3, -, h5, h6, h7⟩ := h
  intro F E _ _ _ _ _ σ hσ M J hJ
  exact ⟨(sw1a1_iff_swa1 F E σ M J).mpr (h1 F E σ hσ M J hJ), (sw1a2_iff_swa2 F E σ M J).mpr (h2 F E σ hσ M J hJ),
    (sw1b1_iff_swb1 F E σ M J).mpr (h3 F E σ hσ M J hJ), hb2 F E σ hσ M J hJ,
    (shintani_weight_c1_iff F E σ M J).mpr (h5 F E σ hσ M J hJ), (shintani_weight_c2_iff F E σ M J).mpr (h6 F E σ hσ M J hJ),
    (shintani_weight_c3_iff F E σ M J).mpr (h7 F E σ hσ M J hJ)⟩

end

end JSW

def JointsOpen : List String := []

end Formalism.MainNotions.GlobalTheoryTheory

end
