import Formalism.SizeWindowBrackets.GaloisToProductIsIso
import Formalism.SizeWindowBrackets.ChainSlopeWindows.StronglyIrreducible
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.CoprimeTwoPow
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.Galois
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.FrobMulInertia
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.Inertia
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.Decomp

open Finset

noncomputable section

namespace Formalism.LFunctionChainParameters.LHost

open Formalism Formalism.D5 Formalism.LFunctionChainParameters.characterSumData

/- English proof (authored)
Represent the residue x by its canonical natural representative. Its reduction modulo c equals the residue of k exactly when those two representatives are congruent modulo c.
-/
lemma cast_eq_natCast_iff {N : ℕ} [NeZero N] (x : ZMod N) (c k : ℕ) :
    (x.cast : ZMod c) = (k : ZMod c) ↔ x.val ≡ k [MOD c] := by
  rw [← ZMod.natCast_val, ZMod.natCast_eq_natCast_iff]

/- English proof (authored)
Apply the residue comparison with the natural representative 1.
-/
lemma cast_eq_one_iff {N : ℕ} [NeZero N] (x : ZMod N) (c : ℕ) :
    (x.cast : ZMod c) = 1 ↔ x.val ≡ 1 [MOD c] := by
  rw [← cast_eq_natCast_iff, Nat.cast_one]

/- English proof (authored)
Equality of units is equality of their underlying residues. The reduction of the unit has the reduced underlying residue, so the general comparison with one gives the congruence.
-/
lemma unitsMap_eq_one_iff {N c : ℕ} [NeZero N] (h : c ∣ N) (u : (ZMod N)ˣ) :
    ZMod.unitsMap h u = 1 ↔ (u : ZMod N).val ≡ 1 [MOD c] := by
  rw [Units.ext_iff, ZMod.unitsMap_val, Units.val_one, cast_eq_one_iff]

/- English proof (authored)
The unit represented by k has underlying residue k. Compare the underlying residues after reduction modulo c, which is equivalent to the asserted congruence.
-/
lemma unitsMap_eq_unitOfCoprime_iff {N c k : ℕ} [NeZero N] (h : c ∣ N) (hk : k.Coprime c) (u : (ZMod N)ˣ) :
    ZMod.unitsMap h u = ZMod.unitOfCoprime k hk ↔ (u : ZMod N).val ≡ k [MOD c] := by
  rw [Units.ext_iff, ZMod.unitsMap_val, ZMod.coe_unitOfCoprime, cast_eq_natCast_iff]

/- English proof (authored)
The local subgroup is the kernel of reduction to the part of the modulus coprime to p. Kernel membership means that the unit reduces to one, which is the displayed congruence on its representative.
-/
lemma mem_localUnits_iff {N : ℕ} [NeZero N] (p : ℕ) (u : (ZMod N)ˣ) :
    u ∈ localUnits N p ↔ (u : ZMod N).val ≡ 1 [MOD ordCompl[p] N] := by
  unfold localUnits
  rw [MonoidHom.mem_ker, unitsMap_eq_one_iff]

/- English proof (authored)
The two defining residue conditions specify p on the part coprime to p and one on the p-power part. Translate each residue equality into a congruence of natural representatives.
-/
lemma isFrobUnit_iff {N : ℕ} [NeZero N] (p : ℕ) (w : (ZMod N)ˣ) :
    IsFrobUnit N p w ↔ (w : ZMod N).val ≡ p [MOD ordCompl[p] N] ∧ (w : ZMod N).val ≡ 1 [MOD ordProj[p] N] := by
  unfold IsFrobUnit
  rw [cast_eq_natCast_iff, cast_eq_one_iff]

/- English proof (authored)
The congruence modulo N identifies the residues of the two canonical representatives. These are the underlying residues of the original units, so the units agree.
-/
lemma units_ext_modEq {N : ℕ} [NeZero N] {u v : (ZMod N)ˣ} (h : (u : ZMod N).val ≡ (v : ZMod N).val [MOD N]) :
    u = v := by
  apply Units.ext
  have := (ZMod.natCast_eq_natCast_iff _ _ N).2 h
  simpa using this

/- English proof (authored)
The Chinese remainder isomorphism for the coprime factors identifies the residue ring modulo their product with the two residue rings. The pair of units is a unit of the product ring. Its inverse image is a unit whose two reductions are the prescribed units.
-/
lemma exists_unit_crt {N a b : ℕ} (hN : N = a * b) (hab : a.Coprime b) (ha : a ∣ N) (hb : b ∣ N)
    (x : (ZMod a)ˣ) (y : (ZMod b)ˣ) :
    ∃ u : (ZMod N)ˣ, ZMod.unitsMap ha u = x ∧ ZMod.unitsMap hb u = y := by
  subst hN
  let E := ZMod.chineseRemainder hab
  refine ⟨Units.map E.symm.toMonoidHom (MulEquiv.prodUnits.symm (x, y)), ?_, ?_⟩
  · apply Units.ext
    change ((E.symm ((x : ZMod a), (y : ZMod b))).cast : ZMod a) = x
    have h3 : ∀ z : ZMod (a * b), (E z).1 = (z.cast : ZMod a) := fun z => Prod.fst_zmod_cast z
    rw [← h3, E.apply_symm_apply]
  · apply Units.ext
    change ((E.symm ((x : ZMod a), (y : ZMod b))).cast : ZMod b) = y
    have h3 : ∀ z : ZMod (a * b), (E z).2 = (z.cast : ZMod b) := fun z => Prod.snd_zmod_cast z
    rw [← h3, E.apply_symm_apply]

/- English proof (authored)
The p-power part and the part coprime to p are coprime factors of the modulus. Choose the residue one on the first and the unit represented by p on the second. The Chinese remainder construction gives a Frobenius unit with these residues, so the chosen Frobenius unit satisfies them. Any two such units have representatives congruent modulo both coprime factors, hence modulo the whole modulus. Their underlying residues are therefore equal.
-/
theorem frobenius_unit_spec : FrobUnitSpec := by
  intro N p hN hp
  have : NeZero N := ⟨hN⟩
  have hcop : (ordProj[p] N).Coprime (ordCompl[p] N) := (Nat.coprime_ordCompl hp hN).pow_left _
  have hex : ∃ w, IsFrobUnit N p w := by
    obtain ⟨u, hu1, hu2⟩ := exists_unit_crt (Nat.ordProj_mul_ordCompl_eq_self N p).symm hcop
      (Nat.ordProj_dvd N p) (Nat.ordCompl_dvd N p) 1 (ZMod.unitOfCoprime p (Nat.coprime_ordCompl hp hN))
    refine ⟨u, (isFrobUnit_iff p u).2 ⟨?_, ?_⟩⟩
    · exact (unitsMap_eq_unitOfCoprime_iff _ _ u).1 hu2
    · exact (unitsMap_eq_one_iff _ u).1 hu1
  have hspec : IsFrobUnit N p (frobUnit N p) := by
    unfold frobUnit
    rw [dif_pos hex]
    exact hex.choose_spec
  refine ⟨hspec, fun w hw => ?_⟩
  rw [isFrobUnit_iff] at hspec hw
  apply units_ext_modEq
  have h1 := hw.1.trans hspec.1.symm
  have h2 := hw.2.trans hspec.2.symm
  have := (Nat.modEq_and_modEq_iff_modEq_mul hcop).1 ⟨h2, h1⟩
  rwa [Nat.ordProj_mul_ordCompl_eq_self] at this

/- English proof (authored)
Apply the specification of the chosen Frobenius unit and translate its two residue conditions into congruences.
-/
lemma frobUnit_modEq {N p : ℕ} [NeZero N] (hp : p.Prime) :
    ((frobUnit N p : (ZMod N)ˣ) : ZMod N).val ≡ p [MOD ordCompl[p] N] ∧
      ((frobUnit N p : (ZMod N)ˣ) : ZMod N).val ≡ 1 [MOD ordProj[p] N] :=
  (isFrobUnit_iff p _).1 (frobenius_unit_spec N p (NeZero.ne N) hp).1

/- English proof (authored)
If p does not divide the modulus, the part coprime to p is the whole modulus. The local subgroup is then the kernel of reduction to the same modulus and is trivial. The first Frobenius congruence now says its underlying residue is p in that ring.
-/
theorem unramified_spec : UnramSpec := by
  intro N p hN hp hpN
  have : NeZero N := ⟨hN⟩
  have hM : ordCompl[p] N = N := (Nat.ordCompl_eq_self_iff_zero_or_not_dvd N hp).2 (Or.inr hpN)
  constructor
  · rw [eq_bot_iff]
    intro u hu
    rw [mem_localUnits_iff, hM] at hu
    rw [Subgroup.mem_bot]
    apply units_ext_modEq
    refine hu.trans ?_
    have : ((1 : (ZMod N)ˣ) : ZMod N).val ≡ 1 [MOD N] := by
      rw [← cast_eq_one_iff]; simp
    exact this.symm
  · have h := (frobUnit_modEq (N := N) hp).1
    rw [hM] at h
    have := (ZMod.natCast_eq_natCast_iff _ _ N).2 h
    simpa using this

section
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]

/- English proof (authored)
On units the induced Dirichlet character is the given character composed with the reciprocity map. Its extension to the residue ring assigns zero to every nonunit.
-/
theorem dirichlet_character_spec : DirCharSpec H := by
  intro N r ψ
  refine ⟨fun u => ?_, fun x hx => MulChar.map_nonunit _ hx⟩
  unfold dirChar
  rw [MulChar.ofUnitHom_coe, MonoidHom.coe_toHomUnits]
  rfl

/- English proof (authored)
At a unit, the definition of the induced Dirichlet character is exactly evaluation of the original character on the unit's reciprocity image.
-/
lemma dirChar_unit {N : ℕ} (r : (ZMod N)ˣ →* Multiplicative (E0 × H)) (ψ : AddChar (E0 × H) ℂ) (u : (ZMod N)ˣ) :
    dirChar r ψ (u : ZMod N) = ψ (Multiplicative.toAdd (r u)) := (dirichlet_character_spec N r ψ).1 u

/- English proof (authored)
The inertia subgroup is the image of the local unit subgroup. Membership in that image means there is a local unit whose reciprocity value is the given group element.
-/
lemma mem_inertia_iff {N : ℕ} (q1 d : ℕ) (r : (ZMod N)ˣ →* Multiplicative (E0 × H)) (p : ℕ) (x : E0 × H) :
    x ∈ (cftData q1 d r).inertia p ↔ ∃ u ∈ localUnits N p, Multiplicative.toAdd (r u) = x := by
  change Multiplicative.ofAdd x ∈ (localUnits N p).map r ↔ _
  rw [Subgroup.mem_map]
  rfl

/- English proof (authored)
A character's conductor divides the complementary modulus exactly when the character factors through the reduction to that modulus. This is equivalent to the induced unit character being trivial on the kernel of reduction. That kernel is the local subgroup, whose reciprocity image is the inertia subgroup. Evaluating the two characters on corresponding units identifies the two triviality conditions.
-/
lemma trivial_on_inertia_iff {N : ℕ} [NeZero N] (q1 d : ℕ) (r : (ZMod N)ˣ →* Multiplicative (E0 × H))
    (ψ : AddChar (E0 × H) ℂ) (p : ℕ) :
    (∀ x ∈ (cftData q1 d r).inertia p, ψ x = 1) ↔ (dirChar r ψ).conductor ∣ ordCompl[p] N := by
  rw [← DirichletCharacter.mem_conductorSet_iff_conductor_dvd _ (Nat.ordCompl_dvd N p),
    DirichletCharacter.mem_conductorSet_iff,
    DirichletCharacter.factorsThrough_iff_ker_unitsMap (Nat.ordCompl_dvd N p)]
  constructor
  · intro h u hu
    rw [MonoidHom.mem_ker, Units.ext_iff, MulChar.coe_toUnitHom, dirChar_unit, Units.val_one]
    exact h _ ((mem_inertia_iff q1 d r p _).2 ⟨u, hu, rfl⟩)
  · intro h x hx
    obtain ⟨u, hu, rfl⟩ := (mem_inertia_iff q1 d r p _).1 hx
    have := h hu
    rw [MonoidHom.mem_ker, Units.ext_iff, MulChar.coe_toUnitHom, dirChar_unit, Units.val_one] at this
    exact this

/- English proof (authored)
Triviality on inertia is equivalent to the conductor dividing the part of the modulus coprime to p. If it does, p cannot divide the conductor. Conversely, the conductor divides the full modulus, so if p does not divide it then it divides the complementary part.
-/
theorem inertia_conductor : InertiaConductor H := by
  intro N q1 d r ψ p hN hp
  have : NeZero N := ⟨hN⟩
  rw [trivial_on_inertia_iff]
  constructor
  · intro h hpc
    exact Nat.not_dvd_ordCompl hp hN (hpc.trans h)
  · intro h
    exact Nat.dvd_ordCompl_of_dvd_not_dvd (DirichletCharacter.conductor_dvd_level _) h

/- English proof (authored)
For each subgroup element x, the value at h + x is the value at h times the value at x. The latter equals one, so all terms equal the value at h. The subgroup contains zero, and its positive cardinality cancels in the average.
-/
lemma cosetMean_of_trivial (I : AddSubgroup (E0 × H)) (h : E0 × H) (ψ : AddChar (E0 × H) ℂ)
    (hI : ∀ x ∈ I, ψ x = 1) : cosetMean I h ψ = ψ h := by
  classical
  unfold cosetMean
  have h0 : ((univ.filter (fun x => x ∈ I)).card : ℂ) ≠ 0 := by
    have : (0 : E0 × H) ∈ univ.filter (fun x => x ∈ I) := by simp [I.zero_mem]
    exact_mod_cast (Finset.card_pos.2 ⟨_, this⟩).ne'
  rw [div_eq_iff h0, Finset.sum_congr rfl (g := fun _ => ψ h)]
  · rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
  · intro x hx
    rw [AddChar.map_add_eq_mul, hI x (by simpa using hx), mul_one]

/- English proof (authored)
Choose a subgroup element whose character value is different from one. Translation by this element permutes the subgroup. Reindexing the coset sum by that translation multiplies the sum by its character value while preserving the sum. Since this multiplier is different from one, the sum is zero, hence so is the mean.
-/
lemma cosetMean_of_nontrivial (I : AddSubgroup (E0 × H)) (h : E0 × H) (ψ : AddChar (E0 × H) ℂ)
    (hI : ¬ ∀ x ∈ I, ψ x = 1) : cosetMean I h ψ = 0 := by
  classical
  unfold cosetMean
  push Not at hI
  obtain ⟨y, hy, hy1⟩ := hI
  have key : ∑ x ∈ univ.filter (fun x => x ∈ I), ψ (h + x) = 0 := by
    have h1 : ∑ x ∈ univ.filter (fun x => x ∈ I), ψ (h + x)
        = ∑ x ∈ univ.filter (fun x => x ∈ I), ψ (h + (y + x)) := by
      symm
      apply Finset.sum_bij (fun x _ => y + x)
      · intro x hx
        simp only [mem_filter, mem_univ, true_and] at hx ⊢
        exact I.add_mem hy hx
      · intro a _ b _ hab
        exact add_left_cancel hab
      · intro b hb
        simp only [mem_filter, mem_univ, true_and] at hb
        exact ⟨-y + b, by simpa using I.add_mem (I.neg_mem hy) hb, by simp⟩
      · intro x _
        rfl
    have h2 : ∑ x ∈ univ.filter (fun x => x ∈ I), ψ (h + (y + x))
        = ψ y * ∑ x ∈ univ.filter (fun x => x ∈ I), ψ (h + x) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      rw [AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul]
      ring
    rw [h2] at h1
    have h3 : (1 - ψ y) * ∑ x ∈ univ.filter (fun x => x ∈ I), ψ (h + x) = 0 := by
      rw [sub_mul, one_mul, ← h1, sub_self]
    rcases mul_eq_zero.1 h3 with h4 | h4
    · exact absurd (sub_eq_zero.1 h4).symm hy1
    · exact h4
  rw [key, zero_div]

/- English proof (authored)
At a positive prime power the primitive value is one inertia-coset mean. If the character is trivial on inertia, the mean equals the value at the Frobenius multiple, which is the corresponding power. Otherwise the coset mean is zero.
-/
theorem primitive_value_ramified : PrimValRamified H := by
  intro N q1 d r ψ p i hp hi
  rw [primitive_value_pow (cftData q1 d r) ψ p i hp hi]
  refine ⟨fun h => ?_, fun h => cosetMean_of_nontrivial _ _ _ h⟩
  rw [cosetMean_of_trivial _ _ _ h, AddChar.map_nsmul_eq_pow]

/- English proof (authored)
If the character is trivial on inertia, the mean is the i-th power of its value on the Frobenius unit. The conductor divides the part coprime to p. After descent to the primitive character at that conductor, the Frobenius congruence reduces its input to p. If the character is nontrivial on inertia, the mean is zero and p divides the conductor. The residue p is then a nonunit for the primitive character, so its value and its positive power are zero as well.
-/
lemma cosetMean_eq_primitive {N : ℕ} [NeZero N] (q1 d : ℕ) (r : (ZMod N)ˣ →* Multiplicative (E0 × H))
    (ψ : AddChar (E0 × H) ℂ) (p i : ℕ) (hp : p.Prime) (hi : i ≠ 0) :
    cosetMean ((cftData q1 d r).inertia p) (i • (cftData q1 d r).frob p) ψ
      = (dirChar r ψ).primitiveCharacter (p : ZMod (dirChar r ψ).conductor) ^ i := by
  by_cases h : ∀ x ∈ (cftData q1 d r).inertia p, ψ x = 1
  · rw [cosetMean_of_trivial _ _ _ h, AddChar.map_nsmul_eq_pow]
    congr 1
    have hc : (dirChar r ψ).conductor ∣ ordCompl[p] N := (trivial_on_inertia_iff q1 d r ψ p).1 h
    change ψ (Multiplicative.toAdd (r (frobUnit N p))) = _
    rw [← dirChar_unit]
    conv_lhs => rw [← DirichletCharacter.changeLevel_primitiveCharacter (dirChar r ψ)]
    rw [DirichletCharacter.changeLevel_eq_cast_of_dvd]
    congr 1
    rw [cast_eq_natCast_iff]
    exact (frobUnit_modEq hp).1.of_dvd hc
  · rw [cosetMean_of_nontrivial _ _ _ h]
    have hpc : p ∣ (dirChar r ψ).conductor := by
      by_contra hpc
      exact h ((inertia_conductor N q1 d r ψ p (NeZero.ne N) hp).2 hpc)
    rw [MulChar.map_nonunit, zero_pow hi]
    rw [ZMod.isUnit_iff_coprime]
    intro hcop
    exact hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hcop hpc)

/- English proof (authored)
Factor n into positive prime powers and use multiplicativity of the primitive character to express its value as a product of the corresponding powers. The coset mean formula identifies each factor with the local factor in the primitive value. The two products are over the same prime support.
-/
theorem primitive_value_primitive : PrimValPrimitive H := by
  intro N q1 d r ψ n hN hn
  have : NeZero N := ⟨hN⟩
  unfold primVal
  conv_rhs => rw [← Nat.prod_factorization_pow_eq_self hn]
  rw [Nat.prod_factorization_eq_prod_primeFactors, Nat.cast_prod, map_prod]
  apply Finset.prod_congr rfl
  intro p hp
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hi : n.factorization p ≠ 0 := by
    have := (Nat.support_factorization n ▸ hp : p ∈ n.factorization.support)
    exact Finsupp.mem_support_iff.1 this
  rw [cosetMean_eq_primitive q1 d r ψ p _ hpp hi, Nat.cast_pow, map_pow]

end

open Formalism.FrobeniusOrbits (HostHyp HGrp hcl)

/- English proof (authored)
The host modulus is a power of two times two primes. All three factors are nonzero, so their product is nonzero.
-/
lemma hostN_ne_zero (e : ℕ) {q d : ℕ} (h : HostHyp q d) : hostN e q d ≠ 0 :=
  Nat.mul_ne_zero (Nat.mul_ne_zero (pow_ne_zero _ two_ne_zero) h.1.ne_zero) h.2.1.ne_zero

/- English proof (authored)
The factor m is coprime to p, so removing the full p-power part from the modulus leaves m. The product of the p-power part and m is the modulus, which is also p to the power k times m. Cancelling nonzero m gives the stated p-power part.
-/
lemma parts_of_eq {N p k m : ℕ} (hp : p.Prime) (hN : N = p ^ k * m) (hm : ¬ p ∣ m) (hm0 : m ≠ 0) :
    ordProj[p] N = p ^ k ∧ ordCompl[p] N = m := by
  subst hN
  have h2 := Nat.ordCompl_pow_mul_of_not_dvd k hp hm
  have h1 := Nat.ordProj_mul_ordCompl_eq_self (p ^ k * m) p
  rw [h2] at h1
  exact ⟨Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hm0) h1, h2⟩

/- English proof (authored)
The first prime is congruent to three modulo eight and the second to seven modulo eight. Neither equals two, and their residues differ, so the primes are distinct.
-/
lemma HostHyp_ne {q d : ℕ} (h : HostHyp q d) : q ≠ 2 ∧ d ≠ 2 ∧ q ≠ d := by
  obtain ⟨_, _, h3, h4, _⟩ := h
  refine ⟨?_, ?_, ?_⟩ <;> omega

/- English proof (authored)
Factor the modulus as its power of two times q and d. The primes q and d are distinct and odd. For each of 2, q and d, its displayed factor is the full prime-power part because the product of the other two factors is coprime to it. The complementary part is therefore that other product.
-/
theorem extension_local_parts : HostLocalParts := by
  intro e q d h
  obtain ⟨hq2, hd2, hqd⟩ := HostHyp_ne h
  have hq := h.1
  have hd := h.2.1
  have h2q : ¬ 2 ∣ q := fun hh => hq2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hq).1 hh).symm
  have h2d : ¬ 2 ∣ d := fun hh => hd2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hd).1 hh).symm
  have hq2' : ¬ q ∣ 2 ^ (e + 2) := fun hh =>
    hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 (hq.dvd_of_dvd_pow hh))
  have hd2' : ¬ d ∣ 2 ^ (e + 2) := fun hh =>
    hd2 ((Nat.prime_dvd_prime_iff_eq hd Nat.prime_two).1 (hd.dvd_of_dvd_pow hh))
  have hqd' : ¬ q ∣ d := fun hh => hqd ((Nat.prime_dvd_prime_iff_eq hq hd).1 hh)
  have hdq' : ¬ d ∣ q := fun hh => hqd ((Nat.prime_dvd_prime_iff_eq hd hq).1 hh).symm
  have hp0 : (2 : ℕ) ^ (e + 2) ≠ 0 := pow_ne_zero _ two_ne_zero
  refine ⟨?_, ?_, ?_⟩
  · exact parts_of_eq Nat.prime_two (by unfold hostN; ring)
      (fun hh => (Nat.prime_two.dvd_mul.1 hh).elim h2q h2d) (Nat.mul_ne_zero hq.ne_zero hd.ne_zero)
  · have := parts_of_eq (N := hostN e q d) (k := 1) (m := 2 ^ (e + 2) * d) hq (by unfold hostN; ring)
      (fun hh => (hq.dvd_mul.1 hh).elim hq2' hqd') (Nat.mul_ne_zero hp0 hd.ne_zero)
    rwa [pow_one] at this
  · have := parts_of_eq (N := hostN e q d) (k := 1) (m := 2 ^ (e + 2) * q) hd (by unfold hostN; ring)
      (fun hh => (hd.dvd_mul.1 hh).elim hd2' hdq') (Nat.mul_ne_zero hp0 hq.ne_zero)
    rwa [pow_one] at this

/- English proof (authored)
The supplementary law for the Jacobi symbol at two gives the sign of the residue class of d modulo eight. The residue is seven, so the sign is one.
-/
lemma jac_two_d {q d : ℕ} (h : HostHyp q d) : jacobiSym ((2 : ℕ) : ℤ) d = 1 := by
  have h8 : d % 8 = 7 := by have := h.2.2.2.1; omega
  have hodd : Odd d := Nat.odd_iff.2 (by omega)
  rw [Nat.cast_ofNat, jacobiSym.at_two hodd, ZMod.χ₈_nat_mod_eight, h8]
  rfl

/- English proof (authored)
The supplementary law at two gives minus one for a denominator congruent to three modulo eight. This applies to q.
-/
lemma jac_two_q {q d : ℕ} (h : HostHyp q d) : jacobiSym ((2 : ℕ) : ℤ) q = -1 := by
  have h8 : q % 8 = 3 := h.2.2.1
  have hodd : Odd q := Nat.odd_iff.2 (by omega)
  rw [Nat.cast_ofNat, jacobiSym.at_two hodd, ZMod.χ₈_nat_mod_eight, h8]
  rfl

/- English proof (authored)
The reciprocity relation for the two host primes gives the value of the symbol with numerator −q and denominator d. Since d is congruent to three modulo four, multiplying the numerator by −1 flips the sign. This gives the value one for numerator q.
-/
lemma jac_q_d {q d : ℕ} (h : HostHyp q d) : jacobiSym (q : ℤ) d = 1 := by
  have h4 : d % 4 = 3 := by have := h.2.2.2.1; omega
  have hodd : Odd d := Nat.odd_iff.2 (by omega)
  have h1 := FrobeniusOrbits.hostRecip q d h
  rw [jacobiSym.neg _ hodd, ZMod.χ₄_nat_three_mod_four h4] at h1
  linarith

/- English proof (authored)
The host condition gives the symbol for −d modulo q equal to one. Since q is congruent to three modulo four, the symbol of −1 modulo q is minus one. Multiplicativity therefore gives minus one for numerator d.
-/
lemma jac_d_q {q d : ℕ} (h : HostHyp q d) : jacobiSym (d : ℤ) q = -1 := by
  have h4 : q % 4 = 3 := by have := h.2.2.1; omega
  have hodd : Odd q := Nat.odd_iff.2 (by omega)
  have h1 := h.2.2.2.2
  rw [jacobiSym.neg _ hodd, ZMod.χ₄_nat_three_mod_four h4] at h1
  linarith

/- English proof (authored)
The supplementary law for −1 expresses the symbol of −l modulo m as the symbol of l modulo m times the sign determined by m modulo four. Quadratic reciprocity has exactly the same sign when the denominator l is three modulo four. If m is one modulo four both signs are positive, and if m is three modulo four both are negative. The expressions thus agree.
-/
lemma jac_flip {l m : ℕ} (hl : l % 4 = 3) (hm : Odd m) : jacobiSym (m : ℤ) l = jacobiSym (-(l : ℤ)) m := by
  rw [jacobiSym.neg _ hm]
  have hl' : Odd l := Nat.odd_iff.2 (by omega)
  rcases Nat.odd_mod_four_iff.1 (Nat.odd_iff.1 hm) with h1 | h3
  · rw [ZMod.χ₄_nat_one_mod_four h1, one_mul, jacobiSym.quadratic_reciprocity_one_mod_four h1 hl']
  · rw [ZMod.χ₄_nat_three_mod_four h3, jacobiSym.quadratic_reciprocity_three_mod_four h3 hl]
    ring

/- English proof (authored)
The sign map takes the positive unit to zero and the negative unit to one in additive notation. A unit is positive one exactly when its underlying integer is one.
-/
lemma sgn2_toAdd_eq_ite (s : ℤˣ) : Multiplicative.toAdd (sgn2 s) = if (s : ℤ) = 1 then 0 else 1 := by
  change (if s = 1 then (0 : ZMod 2) else 1) = _
  have : s = 1 ↔ (s : ℤ) = 1 := by rw [Units.ext_iff, Units.val_one]
  simp only [this]

/- English proof (authored)
Reduce the unit modulo the prime l. The congruence identifies its residue with that of k. The quadratic character at this residue is the Legendre symbol, which agrees with the Jacobi symbol for prime denominator.
-/
lemma legU_of_modEq {N l : ℕ} [NeZero N] [Fact l.Prime] (h : l ∣ N) (u : (ZMod N)ˣ) (k : ℕ)
    (hk : (u : ZMod N).val ≡ k [MOD l]) : ((legU N l h u : ℤˣ) : ℤ) = jacobiSym (k : ℤ) l := by
  unfold legU
  rw [MonoidHom.comp_apply, MulChar.coe_toUnitHom, ZMod.unitsMap_val, (cast_eq_natCast_iff _ _ _).2 hk,
    ← jacobiSym.legendreSym.to_jacobiSym, legendreSym, Int.cast_natCast]

/- English proof (authored)
The host reciprocity map has two quadratic-sign components and the class of the reduction at the power of two. The congruences at d and q identify the two signed values by the quadratic-symbol formula. The third congruence identifies the reduced unit with the one represented by the indicated coprime integer. Substituting these three components gives the formula.
-/
lemma recMap_of_modEq {e q d : ℕ} [Fact q.Prime] [Fact d.Prime] [NeZero (hostN e q d)] (u : (ZMod (hostN e q d))ˣ)
    (kd kq k2 : ℕ) (hk2 : k2.Coprime (2 ^ (e + 2)))
    (h1 : (u : ZMod (hostN e q d)).val ≡ kd [MOD d]) (h2 : (u : ZMod (hostN e q d)).val ≡ kq [MOD q])
    (h3 : (u : ZMod (hostN e q d)).val ≡ k2 [MOD 2 ^ (e + 2)]) :
    Multiplicative.toAdd (recMap e q d u)
      = ((if jacobiSym (kd : ℤ) d = 1 then 0 else 1, if jacobiSym (kq : ℤ) q = 1 then 0 else 1),
        Additive.ofMul (hcl e (ZMod.unitOfCoprime k2 hk2))) := by
  change ((Multiplicative.toAdd (sgn2 (legU _ d (d_dvd_hostN e q d) u)),
      Multiplicative.toAdd (sgn2 (legU _ q (q_dvd_hostN e q d) u))),
      Additive.ofMul (hcl e (ZMod.unitsMap (two_dvd_hostN e q d) u))) = _
  rw [sgn2_toAdd_eq_ite, sgn2_toAdd_eq_ite, legU_of_modEq _ u kd h1, legU_of_modEq _ u kq h2,
    (unitsMap_eq_unitOfCoprime_iff _ hk2 u).2 h3]

/- English proof (authored)
The unit has underlying residue of m modulo N. Its canonical representative is congruent to m modulo N and therefore modulo every divisor c of N.
-/
lemma unitOfCoprime_modEq {N m c : ℕ} [NeZero N] (hm : m.Coprime N) (hc : c ∣ N) :
    ((ZMod.unitOfCoprime m hm : (ZMod N)ˣ) : ZMod N).val ≡ m [MOD c] := by
  rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast]
  exact (Nat.mod_modEq m N).of_dvd hc

/- English proof (authored)
If the sign is one the map returns zero, and if the sign is minus one the map returns one. These two cases give both equivalences because zero and one are distinct modulo two.
-/
lemma ite_zmod2 (J : ℤ) (hJ : J = 1 ∨ J = -1) :
    (((if J = 1 then (0 : ZMod 2) else 1) = 0 ↔ J = 1) ∧ ((if J = 1 then (0 : ZMod 2) else 1) = 1 ↔ J = -1)) := by
  rcases hJ with rfl | rfl
  · simp
  · simp

/- English proof (authored)
The coprime integer m is odd, and its unit reduces to m at each component modulus. Apply the component formula. Since q and d are both congruent to three modulo four, reciprocity changes the two symbols to those of −q and −d modulo m. Coprimality makes each symbol a sign, so the binary equivalences follow from the sign map. The power-of-two component is its specified quotient class.
-/
theorem reciprocity_kronecker : RecKronecker := by
  intro e q d _ _ h m hm hm2
  have : NeZero (hostN e q d) := ⟨hostN_ne_zero e h⟩
  have hodd : Odd m := by
    have : m.Coprime 2 := Nat.Coprime.coprime_dvd_right (dvd_pow_self 2 (by omega)) hm2
    exact Nat.Coprime.odd_of_right this
  have hd4 : d % 4 = 3 := by have := h.2.2.2.1; omega
  have hq4 : q % 4 = 3 := by have := h.2.2.1; omega
  rw [recMap_of_modEq _ m m m hm2 (unitOfCoprime_modEq hm (d_dvd_hostN e q d))
    (unitOfCoprime_modEq hm (q_dvd_hostN e q d)) (unitOfCoprime_modEq hm (two_dvd_hostN e q d)),
    jac_flip hd4 hodd, jac_flip hq4 hodd]
  have hJd : jacobiSym (-(d : ℤ)) m = 1 ∨ jacobiSym (-(d : ℤ)) m = -1 := by
    apply jacobiSym.eq_one_or_neg_one
    rw [Int.neg_gcd, Int.gcd_natCast_natCast]
    exact (Nat.Coprime.coprime_dvd_right (d_dvd_hostN e q d) hm).symm
  have hJq : jacobiSym (-(q : ℤ)) m = 1 ∨ jacobiSym (-(q : ℤ)) m = -1 := by
    apply jacobiSym.eq_one_or_neg_one
    rw [Int.neg_gcd, Int.gcd_natCast_natCast]
    exact (Nat.Coprime.coprime_dvd_right (q_dvd_hostN e q d) hm).symm
  exact ⟨(ite_zmod2 _ hJd).1, (ite_zmod2 _ hJd).2, (ite_zmod2 _ hJq).1, (ite_zmod2 _ hJq).2, rfl⟩

def sQ (l : ℕ) [Fact l.Prime] (x : (ZMod l)ˣ) : ZMod 2 :=
  Multiplicative.toAdd (sgn2 ((quadraticChar (ZMod l)).toUnitHom x))

/- English proof (authored)
The quadratic character sends the identity to one. Passing to its additive sign sends that value to zero.
-/
lemma sQ_one (l : ℕ) [Fact l.Prime] : sQ l 1 = 0 := by
  unfold sQ
  rw [map_one, map_one]
  rfl

/- English proof (authored)
The residue field has odd characteristic, so it has a nonzero quadratic nonresidue. Its quadratic character is minus one, whose additive sign is one.
-/
lemma exists_sQ_eq_one (l : ℕ) [Fact l.Prime] (hl : l ≠ 2) : ∃ x : (ZMod l)ˣ, sQ l x = 1 := by
  obtain ⟨x, hx⟩ := quadraticChar_exists_neg_one' (F := ZMod l) (by rwa [ZMod.ringChar_zmod_n])
  refine ⟨x, ?_⟩
  unfold sQ
  rw [sgn2_toAdd_eq_ite, MulChar.coe_toUnitHom, hx]
  simp

/- English proof (authored)
The only residues modulo two are zero and one.
-/
lemma zmod_two_eq_zero_or_eq_one (a : ZMod 2) : a = 0 ∨ a = 1 := by revert a; decide

/- English proof (authored)
A desired binary value is either zero or one. For zero choose the identity unit. For one choose a quadratic nonresidue, which exists in the odd prime residue field.
-/
lemma exists_sQ_eq (l : ℕ) [Fact l.Prime] (hl : l ≠ 2) (a : ZMod 2) : ∃ x : (ZMod l)ˣ, sQ l x = a := by
  rcases zmod_two_eq_zero_or_eq_one a with rfl | rfl
  · exact ⟨1, sQ_one l⟩
  · exact exists_sQ_eq_one l hl

/- English proof (authored)
By definition the reciprocity map reduces the unit modulo d and q for the two sign components and modulo the power of two for the quotient component. Writing these values additively gives the displayed product coordinates.
-/
lemma recMap_apply (e q d : ℕ) [Fact q.Prime] [Fact d.Prime] (u : (ZMod (hostN e q d))ˣ) :
    Multiplicative.toAdd (recMap e q d u)
      = ((sQ d (ZMod.unitsMap (d_dvd_hostN e q d) u), sQ q (ZMod.unitsMap (q_dvd_hostN e q d) u)),
        Additive.ofMul (hcl e (ZMod.unitsMap (two_dvd_hostN e q d) u))) := rfl

/- English proof (authored)
The power of two and the distinct odd primes q and d are pairwise coprime. First lift the prescribed units modulo the power of two and q to their product. Then lift that unit together with the prescribed unit modulo d. Composing reductions gives the two original reductions as well as the one modulo d.
-/
lemma host_crt (e : ℕ) {q d : ℕ} (h : HostHyp q d) (x2 : (ZMod (2 ^ (e + 2)))ˣ) (xq : (ZMod q)ˣ) (xd : (ZMod d)ˣ) :
    ∃ u : (ZMod (hostN e q d))ˣ, ZMod.unitsMap (two_dvd_hostN e q d) u = x2 ∧
      ZMod.unitsMap (q_dvd_hostN e q d) u = xq ∧ ZMod.unitsMap (d_dvd_hostN e q d) u = xd := by
  obtain ⟨hq2, hd2, hqd⟩ := HostHyp_ne h
  have c2q : (2 ^ (e + 2)).Coprime q :=
    Nat.Coprime.pow_left _ ((Nat.coprime_primes Nat.prime_two h.1).2 hq2.symm)
  have c2d : (2 ^ (e + 2)).Coprime d :=
    Nat.Coprime.pow_left _ ((Nat.coprime_primes Nat.prime_two h.2.1).2 hd2.symm)
  have cqd : q.Coprime d := (Nat.coprime_primes h.1 h.2.1).2 hqd
  obtain ⟨v, hv1, hv2⟩ := exists_unit_crt (N := 2 ^ (e + 2) * q) rfl c2q (dvd_mul_right _ _) (dvd_mul_left _ _) x2 xq
  have hA : 2 ^ (e + 2) * q ∣ hostN e q d := Dvd.intro _ rfl
  obtain ⟨u, hu1, hu2⟩ := exists_unit_crt (N := hostN e q d) (a := 2 ^ (e + 2) * q) (b := d) rfl
    (Nat.Coprime.mul_left c2d cqd) hA (d_dvd_hostN e q d) v xd
  refine ⟨u, ?_, ?_, hu2⟩
  · rw [← hv1, ← hu1, ← MonoidHom.comp_apply, ZMod.unitsMap_comp]
  · rw [← hv2, ← hu1, ← MonoidHom.comp_apply, ZMod.unitsMap_comp]

/- English proof (authored)
The quotient group map is surjective. Choose a unit representing the multiplicative class corresponding to the desired additive element.
-/
lemma exists_hcl (e : ℕ) (t : HA e) : ∃ x2 : (ZMod (2 ^ (e + 2)))ˣ, Additive.ofMul (hcl e x2) = t := by
  obtain ⟨x2, hx2⟩ := QuotientGroup.mk_surjective (Additive.toMul t)
  exact ⟨x2, by unfold FrobeniusOrbits.hcl; rw [hx2]; rfl⟩

/- English proof (authored)
Choose units modulo d and q with the two prescribed signs, and choose a unit modulo the power of two representing the prescribed quotient class. Use the Chinese remainder construction to lift them to one unit of the host modulus. Its reciprocity image has exactly the specified components.
-/
theorem recSurjective_valid : RecSurjective := by
  intro e q d _ _ h y
  obtain ⟨hq2, hd2, -⟩ := HostHyp_ne h
  obtain ⟨xd, hxd⟩ := exists_sQ_eq d hd2 (Multiplicative.toAdd y).1.1
  obtain ⟨xq, hxq⟩ := exists_sQ_eq q hq2 (Multiplicative.toAdd y).1.2
  obtain ⟨x2, hx2⟩ := exists_hcl e (Multiplicative.toAdd y).2
  obtain ⟨u, h1, h2, h3⟩ := host_crt e h x2 xq xd
  refine ⟨u, ?_⟩
  apply Multiplicative.toAdd.injective
  rw [recMap_apply, h1, h2, h3, hxd, hxq, hx2]

section
variable {e q d : ℕ} [Fact q.Prime] [Fact d.Prime]

/- English proof (authored)
Specialize the general inertia-image description to the host modulus and the host reciprocity map.
-/
lemma mem_host_inertia_iff (p : ℕ) (x : E0 × HA e) :
    x ∈ (hostData e q d).inertia p ↔ ∃ u ∈ localUnits (hostN e q d) p, Multiplicative.toAdd (recMap e q d u) = x :=
  mem_inertia_iff q d (recMap e q d) p x

/- English proof (authored)
The quotient class of the identity unit is the identity class, written as zero in the additive quotient.
-/
lemma hcl_one (e : ℕ) : Additive.ofMul (hcl e 1) = (0 : HA e) := rfl

/- English proof (authored)
Coprimality implies the prime does not divide the host modulus. The unramified unit calculation gives a trivial local subgroup and identifies the Frobenius residue with p. Its reciprocity image is therefore the stated Frobenius element, and the image of the trivial subgroup is trivial inertia.
-/
lemma host_unram (h : HostHyp q d) (p : ℕ) (hp : p.Coprime (hostN e q d)) (hpp : p.Prime) :
    (hostData e q d).inertia p = ⊥ ∧
      (hostData e q d).frob p = Multiplicative.toAdd (recMap e q d (ZMod.unitOfCoprime p hp)) := by
  have hN := hostN_ne_zero e h
  have hpN : ¬ p ∣ hostN e q d := fun hh => hpp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hp hh)
  obtain ⟨h1, h2⟩ := unramified_spec (hostN e q d) p hN hpp hpN
  constructor
  · rw [eq_bot_iff]
    intro x hx
    obtain ⟨u, hu, rfl⟩ := (mem_host_inertia_iff p x).1 hx
    rw [h1, Subgroup.mem_bot] at hu
    rw [hu, map_one]
    exact AddSubgroup.zero_mem _
  · change Multiplicative.toAdd (recMap e q d (frobUnit (hostN e q d) p)) = _
    congr 2
    apply Units.ext
    rw [h2, ZMod.coe_unitOfCoprime]

/- English proof (authored)
The complementary modulus at two is qd, so local units reduce to one at both odd primes. Their binary signs are both zero. Conversely any quotient class at the power of two can be represented by a unit there. Lift it together with identity units at q and d. That lift belongs to the local subgroup and realizes the desired element with zero sign coordinates.
-/
lemma host_inertia_two (h : HostHyp q d) (x : E0 × HA e) : x ∈ (hostData e q d).inertia 2 ↔ x.1 = 0 := by
  have : NeZero (hostN e q d) := ⟨hostN_ne_zero e h⟩
  have hM := (extension_local_parts e q d h).1.2
  rw [mem_host_inertia_iff]
  constructor
  · rintro ⟨u, hu, rfl⟩
    rw [mem_localUnits_iff, hM] at hu
    rw [recMap_apply, (unitsMap_eq_one_iff _ u).2 (hu.of_dvd (dvd_mul_left d q)),
      (unitsMap_eq_one_iff _ u).2 (hu.of_dvd (dvd_mul_right q d)), sQ_one, sQ_one]
    rfl
  · intro hx
    obtain ⟨x2, hx2⟩ := exists_hcl e x.2
    obtain ⟨u, h1, h2, h3⟩ := host_crt e h x2 1 1
    refine ⟨u, ?_, ?_⟩
    · rw [mem_localUnits_iff, hM]
      exact (Nat.modEq_and_modEq_iff_modEq_mul ((Nat.coprime_primes h.1 h.2.1).2 (HostHyp_ne h).2.2)).1
        ⟨(unitsMap_eq_one_iff _ u).1 h2, (unitsMap_eq_one_iff _ u).1 h3⟩
    · rw [recMap_apply, h1, h2, h3, sQ_one, sQ_one, hx2]
      exact Prod.ext hx.symm rfl

/- English proof (authored)
Local units at q reduce to one modulo d and the power of two, so only the q-sign can vary. It is either zero or one, yielding the two listed elements. The identity realizes zero. To realize the other, lift a quadratic nonresidue at q together with identities at the other coprime factors.
-/
lemma host_inertia_q (h : HostHyp q d) (x : E0 × HA e) : x ∈ (hostData e q d).inertia q ↔ x = 0 ∨ x = sg := by
  have : NeZero (hostN e q d) := ⟨hostN_ne_zero e h⟩
  have hM := (extension_local_parts e q d h).2.1.2
  obtain ⟨hq2, hd2, hqd⟩ := HostHyp_ne h
  have c2d : (2 ^ (e + 2)).Coprime d :=
    Nat.Coprime.pow_left _ ((Nat.coprime_primes Nat.prime_two h.2.1).2 hd2.symm)
  rw [mem_host_inertia_iff]
  constructor
  · rintro ⟨u, hu, rfl⟩
    rw [mem_localUnits_iff, hM] at hu
    rw [recMap_apply, (unitsMap_eq_one_iff _ u).2 (hu.of_dvd (dvd_mul_left d _)),
      (unitsMap_eq_one_iff (two_dvd_hostN e q d) u).2 (hu.of_dvd (dvd_mul_right _ d)), sQ_one, hcl_one]
    rcases zmod_two_eq_zero_or_eq_one (sQ q (ZMod.unitsMap (q_dvd_hostN e q d) u)) with h0 | h0 <;> rw [h0]
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨1, Subgroup.one_mem _, by rw [map_one]; rfl⟩
    · obtain ⟨xq, hxq⟩ := exists_sQ_eq_one q hq2
      obtain ⟨u, h1, h2, h3⟩ := host_crt e h 1 xq 1
      refine ⟨u, ?_, ?_⟩
      · rw [mem_localUnits_iff, hM]
        exact (Nat.modEq_and_modEq_iff_modEq_mul c2d).1
          ⟨(unitsMap_eq_one_iff _ u).1 h1, (unitsMap_eq_one_iff _ u).1 h3⟩
      · rw [recMap_apply, h1, h2, h3, sQ_one, hxq, hcl_one]
        rfl

/- English proof (authored)
Local units at d reduce to one modulo q and the power of two, so only the d-sign can vary. Its two values give zero and the indicated nontrivial element. Choose the identity for zero, and lift a quadratic nonresidue at d with identities at the other factors for the nontrivial value.
-/
lemma host_inertia_d (h : HostHyp q d) (x : E0 × HA e) : x ∈ (hostData e q d).inertia d ↔ x = 0 ∨ x = sgc0 := by
  have : NeZero (hostN e q d) := ⟨hostN_ne_zero e h⟩
  have hM := (extension_local_parts e q d h).2.2.2
  obtain ⟨hq2, hd2, hqd⟩ := HostHyp_ne h
  have c2q : (2 ^ (e + 2)).Coprime q :=
    Nat.Coprime.pow_left _ ((Nat.coprime_primes Nat.prime_two h.1).2 hq2.symm)
  rw [mem_host_inertia_iff]
  constructor
  · rintro ⟨u, hu, rfl⟩
    rw [mem_localUnits_iff, hM] at hu
    rw [recMap_apply, (unitsMap_eq_one_iff _ u).2 (hu.of_dvd (dvd_mul_left q _)),
      (unitsMap_eq_one_iff (two_dvd_hostN e q d) u).2 (hu.of_dvd (dvd_mul_right _ q)), sQ_one, hcl_one]
    rcases zmod_two_eq_zero_or_eq_one (sQ d (ZMod.unitsMap (d_dvd_hostN e q d) u)) with h0 | h0 <;> rw [h0]
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨1, Subgroup.one_mem _, by rw [map_one]; rfl⟩
    · obtain ⟨xd, hxd⟩ := exists_sQ_eq_one d hd2
      obtain ⟨u, h1, h2, h3⟩ := host_crt e h 1 1 xd
      refine ⟨u, ?_, ?_⟩
      · rw [mem_localUnits_iff, hM]
        exact (Nat.modEq_and_modEq_iff_modEq_mul c2q).1
          ⟨(unitsMap_eq_one_iff _ u).1 h1, (unitsMap_eq_one_iff _ u).1 h2⟩
      · rw [recMap_apply, h1, h2, h3, sQ_one, hxd, hcl_one]
        rfl

/- English proof (authored)
Both units have underlying residue one. Equality of their underlying residues gives equality of units.
-/
lemma unitOfCoprime_one (c : ℕ) (h : (1 : ℕ).Coprime c) : ZMod.unitOfCoprime 1 h = 1 := by
  apply Units.ext
  simp

/- English proof (authored)
At two the Frobenius unit reduces to two at q and d and to one on the power-of-two part. The supplementary symbol values are minus one at q and one at d. The last component is the identity class. These are the coordinates of the stated element.
-/
lemma host_frob_two (h : HostHyp q d) : (hostData e q d).frob 2 = sg := by
  have : NeZero (hostN e q d) := ⟨hostN_ne_zero e h⟩
  obtain ⟨hP, hM⟩ := (extension_local_parts e q d h).1
  obtain ⟨w1, w2⟩ := frobUnit_modEq (N := hostN e q d) Nat.prime_two
  rw [hM] at w1
  rw [hP] at w2
  change Multiplicative.toAdd (recMap e q d (frobUnit (hostN e q d) 2)) = _
  rw [recMap_of_modEq _ 2 2 1 (Nat.coprime_one_left _) (w1.of_dvd (dvd_mul_left d q)) (w1.of_dvd (dvd_mul_right q d)) w2,
    jac_two_d h, jac_two_q h, unitOfCoprime_one, hcl_one]
  rfl

/- English proof (authored)
At q the Frobenius unit reduces to one modulo q and to q at the other components. The symbol of q modulo d is one and the symbol of one modulo q is one, so both binary signs vanish. The remaining component is the class of q at the power of two.
-/
lemma host_frob_q (h : HostHyp q d) (hq : q.Coprime (2 ^ (e + 2))) :
    (hostData e q d).frob q = ((0, 0), Additive.ofMul (hcl e (ZMod.unitOfCoprime q hq))) := by
  have : NeZero (hostN e q d) := ⟨hostN_ne_zero e h⟩
  obtain ⟨hP, hM⟩ := (extension_local_parts e q d h).2.1
  obtain ⟨w1, w2⟩ := frobUnit_modEq (N := hostN e q d) h.1
  rw [hM] at w1
  rw [hP] at w2
  change Multiplicative.toAdd (recMap e q d (frobUnit (hostN e q d) q)) = _
  rw [recMap_of_modEq _ q 1 q hq (w1.of_dvd (dvd_mul_left d _)) w2 (w1.of_dvd (dvd_mul_right _ d)),
    jac_q_d h, Nat.cast_one, jacobiSym.one_left]
  rfl

/- English proof (authored)
At d the Frobenius unit reduces to one modulo d and to d at the other components. Its first binary coordinate is zero, and the symbol of d modulo q is minus one, which gives second coordinate one. The quotient component is the class of d at the power of two.
-/
lemma host_frob_d (h : HostHyp q d) (hd : d.Coprime (2 ^ (e + 2))) :
    (hostData e q d).frob d = ((0, 1), Additive.ofMul (hcl e (ZMod.unitOfCoprime d hd))) := by
  have : NeZero (hostN e q d) := ⟨hostN_ne_zero e h⟩
  obtain ⟨hP, hM⟩ := (extension_local_parts e q d h).2.2
  obtain ⟨w1, w2⟩ := frobUnit_modEq (N := hostN e q d) h.2.1
  rw [hM] at w1
  rw [hP] at w2
  change Multiplicative.toAdd (recMap e q d (frobUnit (hostN e q d) d)) = _
  rw [recMap_of_modEq _ 1 d d hd w2 (w1.of_dvd (dvd_mul_left q _)) (w1.of_dvd (dvd_mul_right _ q)),
    jac_d_q h, Nat.cast_one, jacobiSym.one_left]
  rfl

end

/- English proof (authored)
Combine the unramified formula with the inertia and Frobenius calculations at two, q and d. Together they give each local assertion.
-/
theorem extension_local : HostLocal := by
  intro e q d _ _ h
  exact ⟨fun p hp hpp => host_unram h p hp hpp, ⟨host_inertia_two h, host_frob_two h⟩,
    ⟨host_inertia_q h, host_frob_q h⟩, ⟨host_inertia_d h, host_frob_d h⟩⟩

/- English proof (authored)
The prime p differs from all three primes dividing the host modulus. It is therefore coprime to their respective powers and to the product.
-/
lemma coprime_hostN (e : ℕ) {q d p : ℕ} (h : HostHyp q d) (hp : p.Prime) (h2 : p ≠ 2) (hq : p ≠ q) (hd : p ≠ d) :
    p.Coprime (hostN e q d) := by
  unfold hostN
  exact Nat.Coprime.mul_right (Nat.Coprime.mul_right
    (Nat.Coprime.pow_right _ ((Nat.coprime_primes hp Nat.prime_two).2 h2))
    ((Nat.coprime_primes hp h.1).2 hq)) ((Nat.coprime_primes hp h.2.1).2 hd)

/- English proof (authored)
The host conditions supply the prime and distinctness facts. Away from two, q and d the coprimality result gives trivial inertia. At the two split primes the explicit inertia and Frobenius descriptions have zero first binary coordinate. The distinguished prime has exactly the asserted two inertia elements.
-/
theorem extension_facts : HostFactsHost := by
  intro e q d _ _ h
  obtain ⟨hq2, hd2, hqd⟩ := HostHyp_ne h
  have cq : q.Coprime (2 ^ (e + 2)) := Nat.Coprime.pow_right _ ((Nat.coprime_primes h.1 Nat.prime_two).2 hq2)
  refine ⟨h.1, h.2.1, hq2, hd2, hqd, ?_, ?_, ?_, host_inertia_d h⟩
  · intro p hp h2 hq hd
    exact (host_unram h p (coprime_hostN e h hp h2 hq hd) hp).1
  · rintro p (rfl | hp) x hx
    · have := (host_inertia_two h x).1 hx
      change x.1.1 = 0
      rw [this]
      rfl
    · have hp' : p = q := hp
      rw [hp'] at hx
      rcases (host_inertia_q h x).1 hx with rfl | rfl <;> rfl
  · rintro p (rfl | hp)
    · rw [host_frob_two h]
      rfl
    · have hp' : p = q := hp
      rw [hp', host_frob_q h cq]
      rfl

/- English proof (authored)
The calculated host facts are precisely the arithmetic hypotheses of the character balance theorem. Apply that theorem to the host data and the given positive weights and cutoff.
-/
theorem balance_for_extension : BalanceHost := by
  intro e q d _ _ h ell a t w ha hw N hN
  exact colour_balance (hostData e q d) (extension_facts e q d h) ell a t w ha hw N hN

/- English proof (authored)
The sign character reads the first binary coordinate and returns one at zero and minus one at one.
-/
lemma chC_val {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] (g : E0 × H) :
    (chC : AddChar (E0 × H) ℂ) g = if g.1.1 = 0 then 1 else -1 := rfl

section
variable {e q d : ℕ} [Fact q.Prime] [Fact d.Prime]

/- English proof (authored)
At two the entire sign component of inertia is zero. The first binary coordinate is zero, so the sign character is one there.
-/
lemma chC_trivial_two (h : HostHyp q d) : ∀ x ∈ (hostData e q d).inertia 2, (chC : AddChar (E0 × HA e) ℂ) x = 1 := by
  intro x hx
  rw [chC_val, (host_inertia_two h x).1 hx]
  simp

/- English proof (authored)
The inertia elements at q are zero and the element changing only the second binary coordinate. The first coordinate is zero in both cases, so the character is trivial on this subgroup.
-/
lemma chC_trivial_q (h : HostHyp q d) : ∀ x ∈ (hostData e q d).inertia q, (chC : AddChar (E0 × HA e) ℂ) x = 1 := by
  intro x hx
  rw [chC_val]
  rcases (host_inertia_q h x).1 hx with rfl | rfl <;> simp [sg]

/- English proof (authored)
The nontrivial inertia element at d has first binary coordinate one. The sign character is minus one at this element, so the restriction is nontrivial.
-/
lemma chC_nontrivial_d (h : HostHyp q d) :
    ¬ ∀ x ∈ (hostData e q d).inertia d, (chC : AddChar (E0 × HA e) ℂ) x = 1 := by
  intro hh
  have h1 := hh sgc0 ((host_inertia_d h _).2 (Or.inr rfl))
  rw [chC_val] at h1
  simp [sgc0] at h1
  norm_num at h1

/- English proof (authored)
Reduce the numerator d modulo d to zero. The Jacobi symbol with numerator zero and denominator greater than one is zero.
-/
lemma jac_self (d : ℕ) (hd : 1 < d) : jacobiSym (d : ℤ) d = 0 := by
  rw [jacobiSym.mod_left, Int.emod_self, jacobiSym.zero_left hd]

/- English proof (authored)
At d the mean vanishes because the sign character is nontrivial on inertia. The Jacobi symbol also vanishes, and its exponent is positive. At two and q the character is trivial on inertia, and the explicit Frobenius elements have first coordinate zero. Their sign is one, which matches the corresponding Jacobi values. At any other prime the inertia is trivial, and the first coordinate of the unramified Frobenius records the sign of the Jacobi symbol modulo d. Raising that common value to the positive exponent gives the claimed equality.
-/
lemma cosetMean_chC (h : HostHyp q d) (p i : ℕ) (hp : p.Prime) (hi : i ≠ 0) :
    cosetMean ((hostData e q d).inertia p) (i • (hostData e q d).frob p) chC
      = (((jacobiSym (p : ℤ) d) ^ i : ℤ) : ℂ) := by
  have : NeZero (hostN e q d) := ⟨hostN_ne_zero e h⟩
  obtain ⟨hq2, hd2, hqd⟩ := HostHyp_ne h
  by_cases hpd : p = d
  · subst hpd
    rw [cosetMean_of_nontrivial _ _ _ (chC_nontrivial_d h), jac_self p hp.one_lt, zero_pow hi]
    simp
  by_cases hp2 : p = 2
  · subst hp2
    rw [cosetMean_of_trivial _ _ _ (chC_trivial_two h), AddChar.map_nsmul_eq_pow, host_frob_two h, jac_two_d h, chC_val]
    simp [sg]
  by_cases hpq : p = q
  · subst hpq
    have cq : p.Coprime (2 ^ (e + 2)) := Nat.Coprime.pow_right _ ((Nat.coprime_primes h.1 Nat.prime_two).2 hq2)
    rw [cosetMean_of_trivial _ _ _ (chC_trivial_q h), AddChar.map_nsmul_eq_pow, host_frob_q h cq, jac_q_d h, chC_val]
    simp
  have hcop := coprime_hostN e h hp hp2 hpq hpd
  obtain ⟨h1, h2⟩ := host_unram (e := e) h p hcop hp
  have c2 : p.Coprime (2 ^ (e + 2)) := Nat.Coprime.pow_right _ ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
  rw [cosetMean_of_trivial _ _ _ (by
      intro x hx
      rw [h1, AddSubgroup.mem_bot] at hx
      rw [hx, AddChar.map_zero_eq_one]), AddChar.map_nsmul_eq_pow, h2,
    recMap_of_modEq _ p p p c2 (unitOfCoprime_modEq hcop (d_dvd_hostN e q d))
      (unitOfCoprime_modEq hcop (q_dvd_hostN e q d)) (unitOfCoprime_modEq hcop (two_dvd_hostN e q d)), chC_val]
  have hJ : jacobiSym (p : ℤ) d = 1 ∨ jacobiSym (p : ℤ) d = -1 := by
    apply jacobiSym.eq_one_or_neg_one
    rw [Int.gcd_natCast_natCast]
    exact (Nat.coprime_primes hp h.2.1).2 hpd
  rcases hJ with hJ | hJ <;> rw [hJ] <;> simp

end

/- English proof (authored)
The inertia criterion excludes two and q from the conductor because the character is trivial there. It forces d into the conductor because the character is nontrivial there. The conductor divides the host modulus, which contains d to the first power, so it is exactly d. For the value formula, factor the input into prime powers and use multiplicativity of the Jacobi symbol in its numerator. The coset mean calculation identifies each resulting prime-power factor with the factor defining the primitive value.
-/
theorem character_conductor : ChConductor := by
  intro e q d _ _ h
  have hN := hostN_ne_zero e h
  constructor
  · have i2 := (inertia_conductor (H := HA e) (hostN e q d) q d (recMap e q d) chC 2 hN Nat.prime_two).1
      (chC_trivial_two h)
    have iq := (inertia_conductor (H := HA e) (hostN e q d) q d (recMap e q d) chC q hN h.1).1
      (chC_trivial_q h)
    have id : d ∣ (dirChar (recMap e q d) chC).conductor := by
      by_contra hh
      exact chC_nontrivial_d h
        ((inertia_conductor (H := HA e) (hostN e q d) q d (recMap e q d) chC d hN h.2.1).2 hh)
    have hdvd : (dirChar (recMap e q d) chC).conductor ∣ 2 ^ (e + 2) * q * d :=
      DirichletCharacter.conductor_dvd_level _
    have c2 : ((dirChar (recMap e q d) chC).conductor).Coprime (2 ^ (e + 2)) :=
      Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 i2).symm
    have cq : ((dirChar (recMap e q d) chC).conductor).Coprime q :=
      ((Nat.Prime.coprime_iff_not_dvd h.1).2 iq).symm
    exact Nat.dvd_antisymm (Nat.Coprime.dvd_of_dvd_mul_left (Nat.Coprime.mul_right c2 cq) hdvd) id
  · intro n hn
    let φ : ℤ →* ℤ :=
      { toFun := fun a => jacobiSym a d
        map_one' := jacobiSym.one_left d
        map_mul' := fun a b => jacobiSym.mul_left a b d }
    have hφ : jacobiSym (n : ℤ) d = ∏ p ∈ n.primeFactors, (jacobiSym (p : ℤ) d) ^ n.factorization p := by
      conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hn]
      rw [Nat.prod_factorization_eq_prod_primeFactors, Nat.cast_prod]
      change φ _ = _
      rw [map_prod]
      apply Finset.prod_congr rfl
      intro p _
      rw [Nat.cast_pow, map_pow]
      rfl
    rw [hφ, Int.cast_prod]
    unfold primVal
    apply Finset.prod_congr rfl
    intro p hp
    have hi : n.factorization p ≠ 0 := by
      have := (Nat.support_factorization n ▸ hp : p ∈ n.factorization.support)
      exact Finsupp.mem_support_iff.1 this
    exact cosetMean_chC h p _ (Nat.prime_of_mem_primeFactors hp) hi

/- English proof (authored)
For any target group element choose a unit mapping to it by surjectivity of reciprocity. Equality of the induced Dirichlet characters at that unit gives equality of the original character values at the group element. Thus the original characters agree at all inputs.
-/
theorem dirichlet_character_injective : DirCharInjective := by
  intro e q d _ _ h ψ ψ' hψ
  apply DFunLike.ext
  intro x
  obtain ⟨u, hu⟩ := recSurjective_valid e q d h (Multiplicative.ofAdd x)
  have h1 := dirChar_unit (recMap e q d) ψ u
  have h2 := dirChar_unit (recMap e q d) ψ' u
  rw [hu] at h1 h2
  have h3 : dirChar (recMap e q d) ψ (u : ZMod (hostN e q d)) = dirChar (recMap e q d) ψ' (u : ZMod (hostN e q d)) := by
    rw [hψ]
  rw [h1, h2] at h3
  exact h3

/- English proof (authored)
The integer units are one and minus one. The binary sign sends them to the two distinct residues zero and one, so equal binary signs imply equal units.
-/
lemma sign_injective : ∀ s s' : ℤˣ, Multiplicative.toAdd (sgn2 s) = Multiplicative.toAdd (sgn2 s') → s = s' := by decide

/- English proof (authored)
The unit one maps to zero and minus one maps to one. These are all residues in the target.
-/
lemma sgn2_toAdd_surjective : ∀ x : ZMod 2, ∃ s : ℤˣ, Multiplicative.toAdd (sgn2 s) = x := by decide

/- English proof (authored)
The map reorders the two sign coordinates and writes the signs and quotient component additively. Each of these coordinate operations carries multiplication to addition, so the result holds on all coordinates.
-/
lemma galois_map_mul (e : ℕ) (g g' : FrobeniusOrbits.GG e) : galoisToProduct e (g * g') = galoisToProduct e g + galoisToProduct e g' := by
  unfold galoisToProduct
  simp only [Prod.fst_mul, Prod.snd_mul, map_mul]
  rfl

/- English proof (authored)
The two identity signs map to zero, and the identity class becomes zero in the additive quotient. These are the coordinates of the additive identity.
-/
lemma galois_map_one (e : ℕ) : galoisToProduct e 1 = 0 := by
  unfold galoisToProduct
  simp only [Prod.fst_one, Prod.snd_one, map_one]
  rfl

/- English proof (authored)
Equality of images gives equality of both binary signs and of the additive quotient coordinate. Injectivity of the sign map recovers the original signs, and converting the quotient coordinate back to multiplicative notation recovers its original value. Thus the original group elements are equal.
-/
lemma galois_map_injective (e : ℕ) : Function.Injective (galoisToProduct e) := by
  intro g g' hg
  unfold galoisToProduct at hg
  simp only [Prod.mk.injEq] at hg
  obtain ⟨⟨h1, h2⟩, h3⟩ := hg
  exact Prod.ext (Prod.ext (sign_injective _ _ h2) (sign_injective _ _ h1)) (Additive.ofMul.injective h3)

/- English proof (authored)
The map is injective and carries products to sums. For surjectivity, lift the two binary coordinates to integer signs in the reversed order, and interpret the additive quotient coordinate multiplicatively. The resulting element maps to the chosen target.
-/
theorem galois_map_iso : GaloisToProductIsIso := by
  intro e
  refine ⟨⟨galois_map_injective e, ?_⟩, galois_map_mul e⟩
  rintro ⟨⟨x, y⟩, t⟩
  obtain ⟨s, hs⟩ := sgn2_toAdd_surjective x
  obtain ⟨s', hs'⟩ := sgn2_toAdd_surjective y
  exact ⟨((s', s), Additive.toMul t), by unfold galoisToProduct; simp only [hs, hs']; rfl⟩

/- English proof (authored)
Evaluate each of the two sign coordinates by the binary rule for an integer unit, taking them in the order specified by the map. The quotient component is the original quotient class in additive notation.
-/
lemma galois_map_apply (e : ℕ) (g : FrobeniusOrbits.GG e) :
    galoisToProduct e g = ((if ((g.1.2 : ℤˣ) : ℤ) = 1 then 0 else 1, if ((g.1.1 : ℤˣ) : ℤ) = 1 then 0 else 1),
      Additive.ofMul g.2) := by
  unfold galoisToProduct
  rw [sgn2_toAdd_eq_ite, sgn2_toAdd_eq_ite]

section Field

open NumberField Ideal
open Formalism.FrobeniusOrbits (hostE galE aE bE hostGalois hostGalSpec hostInertia hostDecomp hostFrob_of)
open Formalism.TwoAdicCyclotomicDecomposition (IsLayer galMap layerGalois odd_cyc_frob odd_frob_sgn odd_card_under odd_intCast_mem_iff)

variable {e q d : ℕ} {L : Type} [Field L] [NumberField L] {ζ a b : L}

/- English proof (authored)
The host Galois-group description identifies the map on automorphisms as multiplicative. Apply its product identity to the two automorphisms.
-/
lemma galE_mul' (h : HostHyp q d) (hL : IsLayer (e + 2) q d ζ a b) (σ τ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) :
    galE e ζ a b (σ * τ) = galE e ζ a b σ * galE e ζ a b τ :=
  (hostGalois e q d h.toHypOdd L ζ a b hL).2.2.1 σ τ

/- English proof (authored)
Multiplicativity says the image of the identity is equal to its square. In a group, cancelling this element from that equality makes it the identity.
-/
lemma galE_one' (h : HostHyp q d) (hL : IsLayer (e + 2) q d ζ a b) :
    galE e ζ a b (1 : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) = 1 := by
  have := galE_mul' h hL 1 1
  rw [mul_one] at this
  exact mul_eq_left.mp this.symm

/- English proof (authored)
Multiply the product of the first automorphism and the inverse of the second by the second, which recovers the first automorphism. After applying the multiplicative description and its additive form, this becomes the desired difference identity after subtracting the second image.
-/
lemma galois_map_mul_inv (h : HostHyp q d) (hL : IsLayer (e + 2) q d ζ a b)
    (σ τ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) :
    galoisToProduct e (galE e ζ a b (σ * τ⁻¹)) = galoisToProduct e (galE e ζ a b σ) - galoisToProduct e (galE e ζ a b τ) := by
  rw [eq_sub_iff_add_eq, ← galois_map_mul, ← galE_mul' h hL, inv_mul_cancel_right]

/- English proof (authored)
Under the binary sign rule, one maps to zero and minus one maps to the distinct residue one. Since these are the only units, the zero sign characterizes the positive unit.
-/
lemma sgn2_toAdd_eq_zero_iff : ∀ s : ℤˣ, Multiplicative.toAdd (sgn2 s) = 0 ↔ s = 1 := by decide

/- English proof (authored)
The first factor is the pair of binary signs of the two original units. It is zero exactly when both signs are zero, which is equivalent to both original units being one.
-/
lemma galois_map_first_eq_zero_iff (g : FrobeniusOrbits.GG e) : (galoisToProduct e g).1 = 0 ↔ g.1 = 1 := by
  change ((Multiplicative.toAdd (sgn2 g.1.2), Multiplicative.toAdd (sgn2 g.1.1)) : E0) = 0 ↔ _
  rw [Prod.ext_iff, Prod.ext_iff]
  change (Multiplicative.toAdd (sgn2 g.1.2) = 0 ∧ Multiplicative.toAdd (sgn2 g.1.1) = 0) ↔ (g.1.1 = 1 ∧ g.1.2 = 1)
  rw [sgn2_toAdd_eq_zero_iff, sgn2_toAdd_eq_zero_iff, and_comm]

/- English proof (authored)
The distinguished sign element has first sign −1, second sign 1 and trivial quotient component. In the reversed binary order these give coordinates zero and one, with zero quotient component, as asserted.
-/
lemma galois_map_sign : galoisToProduct e (FrobeniusOrbits.sg e) = sg := by
  rw [galois_map_apply]
  simp [FrobeniusOrbits.sg, sg]

/- English proof (authored)
The specified element has first sign 1 and second sign −1. Their reversed binary coordinates are one and zero. Its quotient class is trivial, which gives the claimed conjugation element.
-/
lemma galois_map_complex_conjugation : galoisToProduct e (((1, -1), 1) : FrobeniusOrbits.GG e) = sgc0 := by
  rw [galois_map_apply]
  simp [sgc0]

variable [Fact q.Prime] [Fact d.Prime]

/- English proof (authored)
At two, the field inertia condition fixes both original signs, which is equivalent to zero sign pair under the additive map. At q and d the field inertia descriptions give the identity and the respective sign element. Their additive images are exactly the two computed local inertia elements, and injectivity gives the converse. At any other prime the field inertia condition forces the identity automorphism, and the computed local inertia is trivial. The injective Galois and additive maps identify those two identity conditions.
-/
lemma field_inertia (h : HostHyp q d) (hL : IsLayer (e + 2) q d ζ a b) (p : ℕ) [Fact p.Prime]
    (P : Ideal (𝓞 (hostE ζ a b))) [P.IsPrime] [hPl : P.LiesOver (span {(p : ℤ)})]
    (σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) :
    (∀ x : 𝓞 (hostE ζ a b), σ • x - x ∈ P) ↔ galoisToProduct e (galE e ζ a b σ) ∈ (hostData e q d).inertia p := by
  have hI := hostInertia e q d h L ζ a b hL σ
  have hinj := galois_map_injective e
  by_cases hp2 : p = 2
  · subst hp2
    have : P.LiesOver (span {(2 : ℤ)}) := by simpa using hPl
    rw [hI.1 P, host_inertia_two h, galois_map_first_eq_zero_iff]
  by_cases hpq : p = q
  · subst hpq
    rw [hI.2.1 P, host_inertia_q h, ← galois_map_one e, ← galois_map_sign, hinj.eq_iff, hinj.eq_iff]
  by_cases hpd : p = d
  · subst hpd
    rw [hI.2.2 P, host_inertia_d h, ← galois_map_one e, ← galois_map_complex_conjugation, hinj.eq_iff, hinj.eq_iff]
  have hp : p.Prime := Fact.out
  rw [(hostFrob_of hostGalois hostGalSpec e q d h.toHypOdd L ζ a b hL p hp2 hpq hpd P).2.2 σ,
    (host_unram h p (coprime_hostN e h hp hp2 hpq hpd) hp).1, AddSubgroup.mem_bot, ← galois_map_one e, hinj.eq_iff,
    ← galE_one' h hL, (hostGalois e q d h.toHypOdd L ζ a b hL).2.2.2.1.eq_iff]

/- English proof (authored)
Two arithmetic Frobenius representatives differ by inertia. If the given automorphism is Frobenius, compare it with the reference representative and use the field inertia identification to place the difference of their images in the arithmetic inertia subgroup. Adding the reference representative's known difference from the designated element gives the desired coset condition. Conversely subtract the reference difference from the assumed condition. The difference corresponds to the product with the inverse reference automorphism, so that product is in field inertia. Multiplying the reference Frobenius by it gives the original automorphism as Frobenius.
-/
lemma field_frob_of (h : HostHyp q d) (hL : IsLayer (e + 2) q d ζ a b) (p : ℕ) [Fact p.Prime]
    (P : Ideal (𝓞 (hostE ζ a b))) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})]
    (σ₀ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) (h₀ : IsArithFrobAt ℤ σ₀ P)
    (h1 : galoisToProduct e (galE e ζ a b σ₀) - (hostData e q d).frob p ∈ (hostData e q d).inertia p)
    (σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) :
    IsArithFrobAt ℤ σ P ↔
      galoisToProduct e (galE e ζ a b σ) - (hostData e q d).frob p ∈ (hostData e q d).inertia p := by
  constructor
  · intro hσ
    have h2 : ∀ x : 𝓞 (hostE ζ a b), (σ * σ₀⁻¹) • x - x ∈ P :=
      AddSubgroup.mem_inertia.mp (hσ.mul_inv_mem_inertia h₀)
    rw [field_inertia h hL p P, galois_map_mul_inv h hL] at h2
    have := AddSubgroup.add_mem _ h2 h1
    rwa [sub_add_sub_cancel] at this
  · intro hσ
    have h2 := AddSubgroup.sub_mem _ hσ h1
    rw [sub_sub_sub_cancel_right, ← galois_map_mul_inv h hL, ← field_inertia h hL p P] at h2
    have := FrobeniusOrbits.Frob.frob_mul_inertia P (σ * σ₀⁻¹) σ₀ (AddSubgroup.mem_inertia.mpr h2) h₀
    rwa [inv_mul_cancel_right] at this

omit [Fact q.Prime] [Fact d.Prime] in

/- English proof (authored)
Choose a prime of the Galois layer above the given host prime. Its residue ring is finite since it lies above a nonzero rational prime ideal. Choose an arithmetic Frobenius there and restrict it to the normal host field. The congruence descends because the upper prime contracts to the given prime and both use the same rational exponent p. The odd-prime Frobenius formula on the cyclotomic part gives the quotient class of p modulo the power of two. On each quadratic root away from its own prime, the Frobenius sign is the symbol of its squared value modulo p. The squared root values are −q and −d, giving the two stated signs.
-/
lemma exists_frob_odd (h : HostHyp q d) (hL : IsLayer (e + 2) q d ζ a b) (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (P : Ideal (𝓞 (hostE ζ a b))) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})] :
    ∃ σ₀ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b, IsArithFrobAt ℤ σ₀ P ∧
      (∀ hp : p.Coprime (2 ^ (e + 2)), (galE e ζ a b σ₀).2 = hcl e (ZMod.unitOfCoprime p hp)) ∧
      (p ≠ q → (((galE e ζ a b σ₀).1.1 : ℤˣ) : ℤ) = jacobiSym (-(q : ℤ)) p) ∧
      (p ≠ d → (((galE e ζ a b σ₀).1.2 : ℤˣ) : ℤ) = jacobiSym (-(d : ℤ)) p) := by
  have hqd := h.toHypOdd
  have hp : p.Prime := Fact.out
  obtain ⟨hEgal, -, -, -⟩ := hostGalois e q d hqd L ζ a b hL
  obtain ⟨hLgal, -, -, -⟩ := layerGalois (e + 2) q d (by omega) hqd L ζ a b hL
  have := hEgal
  have := hLgal
  obtain ⟨⟨Q, hQp, hQl⟩⟩ : Nonempty (P.primesOver (𝓞 L)) := inferInstance
  have : Q.LiesOver (span {(p : ℤ)}) := Ideal.LiesOver.trans Q P (span {(p : ℤ)})
  have : Finite (𝓞 L ⧸ Q) := by
    have hpb : span {(p : ℤ)} ≠ ⊥ := by
      rw [Ne, Ideal.span_singleton_eq_bot]
      exact_mod_cast hp.ne_zero
    exact Ring.HasFiniteQuotients.finiteQuotient (Ideal.ne_bot_of_liesOver_of_ne_bot hpb Q)
  obtain ⟨τ, hτ⟩ := IsArithFrobAt.exists_of_isInvariant ℤ Gal(L/ℚ) Q
  let σ₀ : Gal(hostE ζ a b/ℚ) := τ.restrictNormal (hostE ζ a b)
  have hσ₀ : ∀ x : hostE ζ a b, ((σ₀ x : hostE ζ a b) : L) = τ x :=
    fun x => AlgEquiv.restrictNormal_commutes τ (hostE ζ a b) x
  have hσ₀F : IsArithFrobAt ℤ σ₀ P := by
    intro x
    have hx := hτ (algebraMap (𝓞 (hostE ζ a b)) (𝓞 L) x)
    rw [odd_card_under p Q] at hx
    rw [odd_card_under p P]
    rw [Ideal.over_def Q P, Ideal.under_def, Ideal.mem_comap]
    convert hx using 1
    apply RingOfIntegers.coe_injective
    simp only [map_sub, map_pow, MulSemiringAction.toAlgHom_apply]
    congr 1
    show (((σ₀ • x : 𝓞 (hostE ζ a b)) : hostE ζ a b) : L) =
      τ (((x : 𝓞 (hostE ζ a b)) : hostE ζ a b) : L)
    exact hσ₀ x
  have hval := (hostGalSpec e q d hqd L ζ a b hL σ₀).2.2.2 τ hσ₀
  have ha : a ^ 2 = ((-(q : ℤ) : ℤ) : L) := by rw [hL.2.1]; push_cast; rfl
  have hb : b ^ 2 = ((-(d : ℤ) : ℤ) : L) := by rw [hL.2.2.1]; push_cast; rfl
  refine ⟨σ₀, hσ₀F, fun hc => ?_, fun hpq => ?_, fun hpd => ?_⟩
  · rw [hval]
    change hcl e (galMap hL.1 a b τ).1 = _
    congr 1
    apply Units.ext
    rw [ZMod.coe_unitOfCoprime]
    exact odd_cyc_frob hL.1 p hp2 Q τ hτ
  · rw [hval]
    refine odd_frob_sgn p hp2 Q τ hτ a _ ha ?_
    rw [dvd_neg]
    intro hd'
    exact hpq ((Nat.prime_dvd_prime_iff_eq hp hqd.1).mp (by exact_mod_cast hd'))
  · rw [hval]
    refine odd_frob_sgn p hp2 Q τ hτ b _ hb ?_
    rw [dvd_neg]
    intro hd'
    exact hpd ((Nat.prime_dvd_prime_iff_eq hp hqd.2.1).mp (by exact_mod_cast hd'))

omit [Fact q.Prime] [Fact d.Prime] in

/- English proof (authored)
The residue ring at the given prime is finite, and the host field is Galois, so choose an arithmetic Frobenius. Its decomposition condition forces the second sign to be one. If the first sign were also one, the inertia description would make the automorphism act trivially modulo the prime. Let a be the quadratic generator with a² = −q and take the algebraic integer W = (1 + a)/2. Frobenius acts as squaring modulo the prime over two. Triviality would then give W² − W congruent to zero. But W² − W equals the integer −(q + 1)/4, which is odd because q is three modulo eight. It cannot lie in a prime above two. The first sign is therefore minus one.
-/
lemma exists_frob_two (h : HostHyp q d) (hL : IsLayer (e + 2) q d ζ a b)
    (P : Ideal (𝓞 (hostE ζ a b))) [P.IsPrime] [hPl : P.LiesOver (span {((2 : ℕ) : ℤ)})] :
    ∃ σ₀ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b, IsArithFrobAt ℤ σ₀ P ∧ (galE e ζ a b σ₀).1 = (-1, 1) := by
  have hqd := h.toHypOdd
  obtain ⟨hq2, hd2, -⟩ := HostHyp_ne h
  obtain ⟨hEgal, -, -, -⟩ := hostGalois e q d hqd L ζ a b hL
  have := hEgal
  have : P.LiesOver (span {(2 : ℤ)}) := by simpa using hPl
  have : Finite (𝓞 (hostE ζ a b) ⧸ P) := by
    have hpb : span {(2 : ℤ)} ≠ ⊥ := by
      rw [Ne, Ideal.span_singleton_eq_bot]
      norm_num
    exact Ring.HasFiniteQuotients.finiteQuotient (Ideal.ne_bot_of_liesOver_of_ne_bot hpb P)
  obtain ⟨σ₀, h₀⟩ := IsArithFrobAt.exists_of_isInvariant ℤ Gal(hostE ζ a b/ℚ) P
  have cq : q.Coprime (2 ^ (e + 2)) := Nat.Coprime.pow_right _ ((Nat.coprime_primes h.1 Nat.prime_two).2 hq2)
  have cd : d.Coprime (2 ^ (e + 2)) := Nat.Coprime.pow_right _ ((Nat.coprime_primes h.2.1 Nat.prime_two).2 hd2)
  have hD := (hostDecomp e q d h L ζ a b hL (ZMod.unitOfCoprime q cq) (ZMod.unitOfCoprime d cd)
    (ZMod.coe_unitOfCoprime q cq) (ZMod.coe_unitOfCoprime d cd) σ₀).1 P
  have hb1 : (galE e ζ a b σ₀).1.2 = 1 := (FrobeniusOrbits.mem_Psi_iff _).1 (hD.1 h₀.mem_stabilizer)
  have ha1 : (galE e ζ a b σ₀).1.1 = -1 := by
    rcases Int.units_eq_one_or (galE e ζ a b σ₀).1.1 with h1 | h1
    · exfalso
      have hin : ∀ x : 𝓞 (hostE ζ a b), σ₀ • x - x ∈ P :=
        ((hostInertia e q d h L ζ a b hL σ₀).1 P).2 (Prod.ext h1 hb1)
      have hq8 : q % 8 = 3 := h.2.2.1
      have hq4 : q % 4 = 3 := by omega
      have haE : (aE ζ a b) ^ 2 = -(q : hostE ζ a b) := by
        apply Subtype.ext
        push_cast
        exact hL.2.1
      let W : 𝓞 (hostE ζ a b) := ⟨(1 + aE ζ a b) / 2, FrobeniusOrbits.Inertia.omega_integral hq4 haE⟩
      have hF := h₀ W
      rw [odd_card_under 2 P, MulSemiringAction.toAlgHom_apply] at hF
      have h3 : W ^ 2 - W ∈ P := by
        have := P.sub_mem (hin W) hF
        convert this using 1
        ring
      set c : ℤ := ((q : ℤ) + 1) / 4 with hc
      have h4 : 4 * c = (q : ℤ) + 1 := by omega
      have h4E : 4 * (c : hostE ζ a b) = (q : hostE ζ a b) + 1 := by exact_mod_cast h4
      have hW : W ^ 2 - W = ((-c : ℤ) : 𝓞 (hostE ζ a b)) := by
        apply RingOfIntegers.coe_injective
        simp only [map_sub, map_pow, map_intCast]
        change ((1 + aE ζ a b) / 2) ^ 2 - (1 + aE ζ a b) / 2 = ((-c : ℤ) : hostE ζ a b)
        push_cast
        linear_combination (1 / 4 : hostE ζ a b) * haE + (1 / 4 : hostE ζ a b) * h4E
      rw [hW, odd_intCast_mem_iff 2 P] at h3
      omega
    · exact h1
  exact ⟨σ₀, h₀, Prod.ext ha1 hb1⟩

/- English proof (authored)
The first assertion is the inertia identification. For Frobenius, choose a representative with the calculated signs. At two the two signs match the computed Frobenius, so their difference lies in inertia regardless of the quotient coordinate. At q or d, the quotient coordinate and the sign away from that prime agree by the respective symbol formula. Any remaining sign difference is the generator of the computed inertia subgroup at that prime. Away from the three exceptional primes, reciprocity identifies both quadratic signs with those in the unramified formula and the quotient classes agree, so the difference is zero. In every case the reference representative lies in the required coset. Apply the coset comparison to all automorphisms.
-/
theorem extension_data_field : HostDataField := by
  intro e q d _ _ h L _ _ ζ a b hL p _ P _ _ σ
  refine ⟨field_inertia h hL p P σ, ?_⟩
  have hp : p.Prime := Fact.out
  obtain ⟨hq2, hd2, hqd⟩ := HostHyp_ne h
  by_cases hp2 : p = 2
  · subst hp2
    obtain ⟨σ₀, h₀, h1⟩ := exists_frob_two h hL P
    refine field_frob_of h hL 2 P σ₀ h₀ ?_ σ
    rw [host_inertia_two h, host_frob_two h, galois_map_apply, h1]
    simp [sg]
  obtain ⟨σ₀, h₀, hH, ha, hb⟩ := exists_frob_odd h hL p hp2 P
  have c2 : p.Coprime (2 ^ (e + 2)) := Nat.Coprime.pow_right _ ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
  refine field_frob_of h hL p P σ₀ h₀ ?_ σ
  rw [galois_map_apply, hH c2]
  by_cases hpq : p = q
  · subst hpq
    rw [hb hqd, h.2.2.2.2, host_frob_q h c2, host_inertia_q h]
    by_cases hs : (((galE e ζ a b σ₀).1.1 : ℤˣ) : ℤ) = 1 <;> simp [hs, sg]
  by_cases hpd : p = d
  · subst hpd
    rw [ha hqd.symm, FrobeniusOrbits.hostRecip q p h, host_frob_d h c2, host_inertia_d h]
    by_cases hs : (((galE e ζ a b σ₀).1.2 : ℤˣ) : ℤ) = 1 <;> simp [hs, sgc0]
  have : NeZero (hostN e q d) := ⟨hostN_ne_zero e h⟩
  have hcop := coprime_hostN e h hp hp2 hpq hpd
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hd4 : d % 4 = 3 := by have := h.2.2.2.1; omega
  have hq4 : q % 4 = 3 := by have := h.2.2.1; omega
  rw [ha hpq, hb hpd, (host_unram h p hcop hp).2,
    recMap_of_modEq _ p p p c2 (unitOfCoprime_modEq hcop (d_dvd_hostN e q d))
      (unitOfCoprime_modEq hcop (q_dvd_hostN e q d)) (unitOfCoprime_modEq hcop (two_dvd_hostN e q d)),
    jac_flip hd4 hodd, jac_flip hq4 hodd, sub_self]
  exact AddSubgroup.zero_mem _

end Field

end Formalism.LFunctionChainParameters.LHost
