import Mathlib
import GroundTheory.GlobalFields.AnalyticClassNumber.DirichletHecke
set_option maxSynthPendingDepth 1

namespace GroundTheory.Global

open IsDedekindDomain NumberField IdeleGroup Topology Filter
open scoped GroundTheory.LocalField.Abstract

noncomputable section

namespace DirichletHecke

open _root_.GroundTheory.Global.Cyclotomic GroundTheory.LocalField.Abstract RationalSymbol

section Level

variable {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)

abbrev frobClass (v : HeightOneSpectrum (𝓞 ℚ)) : IdeleClassGroup ℚ :=
  IdeleClassGroup.mk ℚ (finiteEmbedding v (uniformizer v))

/- English proof (translation)
Take `⟨p, -, hp, hpb⟩` from `Nat.forall_exists_prime_gt_and_eq_mod b.isUnit 0`. Use `⟨placeOf (⟨p, hp⟩ : Nat.Primes), fun hdvd ↦ ?_, by` and prove the remaining obligations. Rewrite using `[prime_placeOf (⟨p, hp⟩ : Nat.Primes)]`. Conclude with `hpb⟩`. Rewrite `hdvd` using `[prime_placeOf (⟨p, hp⟩ : Nat.Primes)]`.

Establish `hu : IsUnit (p : ZMod N)` using `hpb ▸ b.isUnit`. Rewrite `hu` using `[ZMod.isUnit_iff_coprime]`. Conclude with `(Nat.Prime.coprime_iff_not_dvd hp).1 hu hdvd`.
-/
theorem exists_frobClass (b : (ZMod N)ˣ) :
    ∃ v : HeightOneSpectrum (𝓞 ℚ), ¬ prime v ∣ N ∧ (prime v : ZMod N) = b := by
  obtain ⟨p, -, hp, hpb⟩ := Nat.forall_exists_prime_gt_and_eq_mod b.isUnit 0
  refine ⟨placeOf (⟨p, hp⟩ : Nat.Primes), fun hdvd ↦ ?_, by
    rw [prime_placeOf (⟨p, hp⟩ : Nat.Primes)]; exact hpb⟩
  rw [prime_placeOf (⟨p, hp⟩ : Nat.Primes)] at hdvd
  have hu : IsUnit (p : ZMod N) := hpb ▸ b.isUnit
  rw [ZMod.isUnit_iff_coprime] at hu
  exact (Nat.Prime.coprime_iff_not_dvd hp).1 hu hdvd

/- English proof (translation)
Introduce `χ ψ h`. Use `MulChar.ext fun b ↦ ?_` and prove the remaining obligations. Take `⟨v, hv, hvb⟩` from `exists_frobClass b`. Use `congrArg (fun ω : HeckeCharacter ℚ ↦ (ω (frobClass v) : ℂ)) h` as an intermediate fact. Simplify using `only [frobClass, coe_heckeCharacter_uniformizer _ hv] at this`.

Rewrite using `[← hvb]`. Conclude with `this`.
-/
theorem heckeCharacter_injective :
    Function.Injective (heckeCharacter : DirichletCharacter ℂ N → HeckeCharacter ℚ) := by
  intro χ ψ h
  refine MulChar.ext fun b ↦ ?_
  obtain ⟨v, hv, hvb⟩ := exists_frobClass b
  have := congrArg (fun ω : HeckeCharacter ℚ ↦ (ω (frobClass v) : ℂ)) h
  simp only [frobClass, coe_heckeCharacter_uniformizer _ hv] at this
  rw [← hvb]
  exact this

/- English proof (translation)
The claim follows from `Units.ext (ProfiniteInteger.castHom_proj (m := modulus N) (n := modulus M) h (w : ℤ̂))`.
-/
theorem unitsMap_unitsMod {M : ℕ} [NeZero M] (h : N ∣ M) (w : ℤ̂ˣ) :
    ZMod.unitsMap h (unitsMod M w) = unitsMod N w :=
  Units.ext (ProfiniteInteger.castHom_proj (m := modulus N) (n := modulus M) h (w : ℤ̂))

/- English proof (translation)
Use extensionality with `x`. Rewrite using `[coe_heckeCharacter_apply, coe_heckeCharacter_apply, ← coe_unitsMod, ← coe_unitsMod, ← MulChar.coe_toUnitHom, ← MulChar.coe_toUnitHom, DirichletCharacter.changeLevel_toUnitHom, MonoidHom.comp_apply, unitsMap_unitsMod]`.
-/
theorem heckeCharacter_changeLevel {M : ℕ} [NeZero M] (h : N ∣ M) :
    heckeCharacter (DirichletCharacter.changeLevel h χ) = heckeCharacter χ := by
  ext x
  rw [coe_heckeCharacter_apply, coe_heckeCharacter_apply, ← coe_unitsMod, ← coe_unitsMod,
    ← MulChar.coe_toUnitHom, ← MulChar.coe_toUnitHom, DirichletCharacter.changeLevel_toUnitHom,
    MonoidHom.comp_apply, unitsMap_unitsMod]

/- English proof (translation)
Assemble the required witnesses or components as `⟨χ.conductor_ne_zero⟩ heckeCharacter χ.primitiveCharacter = heckeCharacter χ := by have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩ conv_rhs => rw [← χ.changeLevel_primitiveCharacter] exact (heckeCharacter_changeLevel _ _).symm`.
-/
theorem heckeCharacter_primitiveCharacter :
    haveI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
    heckeCharacter χ.primitiveCharacter = heckeCharacter χ := by
  have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  conv_rhs => rw [← χ.changeLevel_primitiveCharacter]
  exact (heckeCharacter_changeLevel _ _).symm

/- English proof (translation)
Use extensionality with `x`. Rewrite using `[ContinuousMonoidHom.pow_apply, heckeCharacter_apply, galoisCharacter, MonoidHom.comp_apply, ← map_pow, pow_card_eq_one, map_one]`. Both sides reduce to the same expression.
-/
theorem heckeCharacter_pow_card : heckeCharacter χ ^ Fintype.card (ZMod N)ˣ = 1 := by
  ext x
  rw [ContinuousMonoidHom.pow_apply, heckeCharacter_apply, galoisCharacter, MonoidHom.comp_apply,
    ← map_pow, pow_card_eq_one, map_one]
  rfl

/- English proof (translation)
The claim follows from `isOfFinOrder_iff_pow_eq_one.2 ⟨_, Fintype.card_pos, heckeCharacter_pow_card χ⟩`.
-/
theorem isOfFinOrder_heckeCharacter : IsOfFinOrder (heckeCharacter χ) :=
  isOfFinOrder_iff_pow_eq_one.2 ⟨_, Fintype.card_pos, heckeCharacter_pow_card χ⟩

end Level

/- English proof (translation)
Establish `hNM : (DirichletCharacter.changeLevel (Nat.dvd_mul_right N M) χ) = DirichletCharacter.changeLevel (Nat.dvd_mul_left M N) ψ` using `heckeCharacter_injective (by rw [heckeCharacter_changeLevel, heckeCharacter_changeLevel, h])`. Establish `h1 : N ∣ M`. Establish `hf` using `χ.factorsThrough_gcd ψ hNM`. Use `χ.conductor_dvd_of_mem_conductorSet hf` as an intermediate fact. Rewrite `this` using `[hχ]`.

Conclude with `this.trans (Nat.gcd_dvd_right N M)`. Establish `h2 : M ∣ N`. Establish `hMN : DirichletCharacter.changeLevel (Nat.dvd_mul_right M N) ψ = DirichletCharacter.changeLevel (Nat.dvd_mul_left N M) χ` using `heckeCharacter_injective (by rw [heckeCharacter_changeLevel, heckeCharacter_changeLevel, h])`. Establish `hf` using `ψ.factorsThrough_gcd χ hMN`. Use `ψ.conductor_dvd_of_mem_conductorSet hf` as an intermediate fact.

Rewrite `this` using `[hψ]`. Conclude with `this.trans (Nat.gcd_dvd_right M N)`. Take `rfl` from `Nat.dvd_antisymm h1 h2`. Conclude with `⟨rfl, heq_of_eq (heckeCharacter_injective h)⟩`.
-/
theorem eq_of_heckeCharacter_eq {N M : ℕ} [NeZero N] [NeZero M] {χ : DirichletCharacter ℂ N}
    {ψ : DirichletCharacter ℂ M} (hχ : χ.IsPrimitive) (hψ : ψ.IsPrimitive)
    (h : heckeCharacter χ = heckeCharacter ψ) : N = M ∧ HEq χ ψ := by
  have hNM : (DirichletCharacter.changeLevel (Nat.dvd_mul_right N M) χ) =
      DirichletCharacter.changeLevel (Nat.dvd_mul_left M N) ψ :=
    heckeCharacter_injective (by rw [heckeCharacter_changeLevel, heckeCharacter_changeLevel, h])
  have h1 : N ∣ M := by
    have hf := χ.factorsThrough_gcd ψ hNM
    have := χ.conductor_dvd_of_mem_conductorSet hf
    rw [hχ] at this
    exact this.trans (Nat.gcd_dvd_right N M)
  have h2 : M ∣ N := by
    have hMN : DirichletCharacter.changeLevel (Nat.dvd_mul_right M N) ψ =
        DirichletCharacter.changeLevel (Nat.dvd_mul_left N M) χ :=
      heckeCharacter_injective (by rw [heckeCharacter_changeLevel, heckeCharacter_changeLevel, h])
    have hf := ψ.factorsThrough_gcd χ hMN
    have := ψ.conductor_dvd_of_mem_conductorSet hf
    rw [hψ] at this
    exact this.trans (Nat.gcd_dvd_right M N)
  obtain rfl := Nat.dvd_antisymm h1 h2
  exact ⟨rfl, heq_of_eq (heckeCharacter_injective h)⟩

/- English proof (translation)
Take `⟨r, rfl⟩` from `(mem_positiveRealFactor_iff_exists x).1 hx`. Establish `hn : 0 < orderOf ω` using `hω.orderOf_pos`. Establish `hr : 0 < ((r : ℝˣ) : ℝ)` using `(Units.mem_posSubgroup _).1 r.2`. Establish `hr0 : 0 < ((r : ℝˣ) : ℝ) ^ ((orderOf ω : ℝ)⁻¹)` using `Real.rpow_pos_of_pos hr _`. Set `r' : Units.posSubgroup ℝ` to `⟨Units.mk0 _ hr0.ne', (Units.mem_posSubgroup _).2 hr0⟩`.

Establish `hr' : r' ^ orderOf ω = r` using `Subtype.ext (Units.ext (by`. Simplify using `only [r', SubgroupClass.coe_pow, Units.val_pow_eq_pow_val, Units.val_mk0]`. Conclude with `Real.rpow_inv_natCast_pow hr.le hn.ne'))`. Establish `h : RationalIdeles.ideleClassGroupEquiv.symm (r, 1) = RationalIdeles.ideleClassGroupEquiv.symm (r', 1) ^ orderOf ω`. Rewrite using `[← map_pow, Prod.pow_mk, one_pow, hr']`.

Rewrite using `[h, map_pow, ← ContinuousMonoidHom.pow_apply, pow_orderOf_eq_one]`. Both sides reduce to the same expression.
-/
theorem eq_one_of_mem_positiveRealFactor {ω : HeckeCharacter ℚ} (hω : IsOfFinOrder ω)
    {x : IdeleClassGroup ℚ} (hx : x ∈ positiveRealFactor) : ω x = 1 := by
  obtain ⟨r, rfl⟩ := (mem_positiveRealFactor_iff_exists x).1 hx
  have hn : 0 < orderOf ω := hω.orderOf_pos
  have hr : 0 < ((r : ℝˣ) : ℝ) := (Units.mem_posSubgroup _).1 r.2
  have hr0 : 0 < ((r : ℝˣ) : ℝ) ^ ((orderOf ω : ℝ)⁻¹) := Real.rpow_pos_of_pos hr _
  let r' : Units.posSubgroup ℝ := ⟨Units.mk0 _ hr0.ne', (Units.mem_posSubgroup _).2 hr0⟩
  have hr' : r' ^ orderOf ω = r := Subtype.ext (Units.ext (by
    simp only [r', SubgroupClass.coe_pow, Units.val_pow_eq_pow_val, Units.val_mk0]
    exact Real.rpow_inv_natCast_pow hr.le hn.ne'))
  have h : RationalIdeles.ideleClassGroupEquiv.symm (r, 1) =
      RationalIdeles.ideleClassGroupEquiv.symm (r', 1) ^ orderOf ω := by
    rw [← map_pow, Prod.pow_mk, one_pow, hr']
  rw [h, map_pow, ← ContinuousMonoidHom.pow_apply, pow_orderOf_eq_one]
  rfl

def unitSection : ℤ̂ˣ →* IdeleClassGroup ℚ :=
  RationalIdeles.ideleClassGroupEquiv.symm.toMulEquiv.toMonoidHom.comp
    ((MonoidHom.inr _ _).comp unitsPadicHomeomorph.symm.toMulEquiv.toMonoidHom)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem unitSection_apply (w : ℤ̂ˣ) :
    unitSection w = RationalIdeles.ideleClassGroupEquiv.symm (1, unitsPadicHomeomorph.symm w) :=
  rfl

/- English proof (translation)
Establish `h : (unitSection : ℤ̂ˣ → IdeleClassGroup ℚ) = fun w ↦ RationalIdeles.ideleClassGroupEquiv.symm (1, unitsPadicHomeomorph.symm w)`. Use function extensionality and compare the values at `unitSection_apply`. Rewrite using `[h]`. Conclude with `RationalIdeles.ideleClassGroupEquiv.symm.continuous.comp (continuous_const.prodMk unitsPadicHomeomorph.symm.continuous)`.
-/
theorem continuous_unitSection : Continuous unitSection := by
  have h : (unitSection : ℤ̂ˣ → IdeleClassGroup ℚ) =
      fun w ↦ RationalIdeles.ideleClassGroupEquiv.symm (1, unitsPadicHomeomorph.symm w) :=
    funext unitSection_apply
  rw [h]
  exact RationalIdeles.ideleClassGroupEquiv.symm.continuous.comp
    (continuous_const.prodMk unitsPadicHomeomorph.symm.continuous)

/- English proof (translation)
Rewrite using `[mem_positiveRealFactor_iff, map_mul, map_inv, unitSection_apply, ContinuousMulEquiv.apply_symm_apply, unitPart_eq, ContinuousMulEquiv.symm_apply_apply]`. Conclude with `mul_inv_cancel _`.
-/
theorem mul_inv_unitSection_mem (x : IdeleClassGroup ℚ) :
    x * (unitSection (unitPart x))⁻¹ ∈ positiveRealFactor := by
  rw [mem_positiveRealFactor_iff, map_mul, map_inv, unitSection_apply,
    ContinuousMulEquiv.apply_symm_apply, unitPart_eq, ContinuousMulEquiv.symm_apply_apply]
  exact mul_inv_cancel _

/- English proof (translation)
Establish `h` using `eq_one_of_mem_positiveRealFactor hω (mul_inv_unitSection_mem x)`. Rewrite `h` using `[map_mul, map_inv, mul_inv_eq_one]`. Then use the resulting hypothesis.
-/
theorem apply_eq_unitSection {ω : HeckeCharacter ℚ} (hω : IsOfFinOrder ω) (x : IdeleClassGroup ℚ) :
    ω x = ω (unitSection (unitPart x)) := by
  have h := eq_one_of_mem_positiveRealFactor hω (mul_inv_unitSection_mem x)
  rwa [map_mul, map_inv, mul_inv_eq_one] at h

/- English proof (translation)
Establish `hF : {z : Circle | z ^ n = 1 ∧ z ≠ 1}.Finite`. Use `Set.Finite.subset (Set.Finite.preimage Circle.coe_injective.injOn (Finset.finite_toSet (Polynomial.nthRoots n (1 : ℂ)).toFinset)) fun z hz ↦ ?_` and prove the remaining obligations. Establish `h` using `congrArg (fun w : Circle ↦ (w : ℂ)) hz.1`. Simplify using `only [Circle.coe_one] at h`. Simplify using `only [Set.mem_preimage, Finset.mem_coe, Multiset.mem_toFinset]`.

Conclude with `(Polynomial.mem_nthRoots hn).2 h`. Establish `h : (φ.ker : Set G) = φ ⁻¹' {z : Circle | z ^ n = 1 ∧ z ≠ 1}ᶜ`. Use extensionality with `g`. Simplify using `only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_preimage, Set.mem_compl_iff, Set.mem_ofPred_eq, not_and, not_not]`. Conclude with `⟨fun h _ ↦ h, fun h ↦ h (hpow g)⟩`.

Rewrite using `[h]`. Conclude with `hF.isClosed.isOpen_compl.preimage hφ`.
-/
theorem isOpen_ker_of_pow_eq_one {G : Type*} [TopologicalSpace G] [Group G] (φ : G →* Circle)
    (hφ : Continuous φ) {n : ℕ} (hn : 0 < n) (hpow : ∀ g, φ g ^ n = 1) :
    IsOpen (φ.ker : Set G) := by
  have hF : {z : Circle | z ^ n = 1 ∧ z ≠ 1}.Finite := by
    refine Set.Finite.subset (Set.Finite.preimage Circle.coe_injective.injOn
      (Finset.finite_toSet (Polynomial.nthRoots n (1 : ℂ)).toFinset)) fun z hz ↦ ?_
    have h := congrArg (fun w : Circle ↦ (w : ℂ)) hz.1
    simp only [Circle.coe_one] at h
    simp only [Set.mem_preimage, Finset.mem_coe, Multiset.mem_toFinset]
    exact (Polynomial.mem_nthRoots hn).2 h
  have h : (φ.ker : Set G) = φ ⁻¹' {z : Circle | z ^ n = 1 ∧ z ≠ 1}ᶜ := by
    ext g
    simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_preimage, Set.mem_compl_iff,
      Set.mem_ofPred_eq, not_and, not_not]
    exact ⟨fun h _ ↦ h, fun h ↦ h (hpow g)⟩
  rw [h]
  exact hF.isClosed.isOpen_compl.preimage hφ

/- English proof (translation)
Rewrite `ht` using `[nhds_subtype, Filter.mem_comap]`. Take `⟨s, hs, hst⟩` from `ht`. Rewrite `hs` using `[nhds_pi, Filter.mem_pi]`. Take `⟨I, hI, u, hu, hIu⟩` from `hs`. Use `⟨⟨∏ n ∈ hI.toFinset, (n : ℕ), Finset.prod_pos fun n _ ↦ n.pos⟩, fun z hz ↦ hst (hIu fun n hn ↦ ?_)⟩` and prove the remaining obligations.

Establish `hdvd : (n : ℕ) ∣ ∏ m ∈ hI.toFinset, (m : ℕ)` using `Finset.dvd_prod_of_mem _ (hI.mem_toFinset.2 hn)`. Establish `h1` using `ProfiniteInteger.castHom_proj (m := n) (n := ⟨∏ n ∈ hI.toFinset, (n : ℕ), Finset.prod_pos fun n _ ↦ n.pos⟩) hdvd z`. Establish `h2` using `ProfiniteInteger.castHom_proj (m := n) (n := ⟨∏ n ∈ hI.toFinset, (n : ℕ), Finset.prod_pos fun n _ ↦ n.pos⟩) hdvd z₀`. Rewrite `h1` using `[hz, h2]`. Establish `h3 : (z : ∀ k : ℕ+, ZMod k) n = (z₀ : ∀ k : ℕ+, ZMod k) n`.

Rewrite using `[← ProfiniteInteger.proj_apply, ← ProfiniteInteger.proj_apply, h1]`. Use `show (z : ∀ k : ℕ+, ZMod k) n ∈ u n`. Rewrite using `[h3]`. Conclude with `mem_of_mem_nhds (hu n)`.
-/
theorem exists_proj_eq_mem {z₀ : ℤ̂} {t : Set ℤ̂} (ht : t ∈ 𝓝 z₀) :
    ∃ M : ℕ+, ∀ z : ℤ̂, ProfiniteInteger.proj M z = ProfiniteInteger.proj M z₀ → z ∈ t := by
  rw [nhds_subtype, Filter.mem_comap] at ht
  obtain ⟨s, hs, hst⟩ := ht
  rw [nhds_pi, Filter.mem_pi] at hs
  obtain ⟨I, hI, u, hu, hIu⟩ := hs
  refine ⟨⟨∏ n ∈ hI.toFinset, (n : ℕ), Finset.prod_pos fun n _ ↦ n.pos⟩,
    fun z hz ↦ hst (hIu fun n hn ↦ ?_)⟩
  have hdvd : (n : ℕ) ∣ ∏ m ∈ hI.toFinset, (m : ℕ) := Finset.dvd_prod_of_mem _ (hI.mem_toFinset.2 hn)
  have h1 := ProfiniteInteger.castHom_proj (m := n)
    (n := ⟨∏ n ∈ hI.toFinset, (n : ℕ), Finset.prod_pos fun n _ ↦ n.pos⟩) hdvd z
  have h2 := ProfiniteInteger.castHom_proj (m := n)
    (n := ⟨∏ n ∈ hI.toFinset, (n : ℕ), Finset.prod_pos fun n _ ↦ n.pos⟩) hdvd z₀
  rw [hz, h2] at h1
  have h3 : (z : ∀ k : ℕ+, ZMod k) n = (z₀ : ∀ k : ℕ+, ZMod k) n := by
    rw [← ProfiniteInteger.proj_apply, ← ProfiniteInteger.proj_apply, h1]
  show (z : ∀ k : ℕ+, ZMod k) n ∈ u n
  rw [h3]
  exact mem_of_mem_nhds (hu n)

/- English proof (translation)
Establish `h1 : (H : Set ℤ̂ˣ) ∈ 𝓝 (1 : ℤ̂ˣ)` using `hH.mem_nhds H.one_mem`. Rewrite `h1` using `[Units.isEmbedding_embedProduct.isInducing.nhds_eq_comap, Filter.mem_comap]`. Take `⟨t, ht, hsub⟩` from `h1`. Rewrite `ht` using `[map_one, Prod.one_eq_mk, nhds_prod_eq, Filter.mem_prod_iff]`. Take `⟨t1, ht1, t2, ht2, ht12⟩` from `ht`.

Establish `ht2' : (MulOpposite.op ⁻¹' t2 : Set ℤ̂) ∈ 𝓝 (1 : ℤ̂)` using `MulOpposite.continuous_op.continuousAt.preimage_mem_nhds (by rwa [MulOpposite.op_one])`. Take `⟨M1, hM1⟩` from `exists_proj_eq_mem ht1`. Take `⟨M2, hM2⟩` from `exists_proj_eq_mem ht2'`. Establish `hd1 : (M1 : ℕ) ∣ ((M1 * M2 : ℕ+) : ℕ)` using `by rw [PNat.mul_coe]; exact dvd_mul_right _ _`. Establish `hd2 : (M2 : ℕ) ∣ ((M1 * M2 : ℕ+) : ℕ)` using `by rw [PNat.mul_coe]; exact dvd_mul_left _ _`.

Use `⟨M1 * M2, fun w hw ↦ hsub (ht12 ⟨?_, ?_⟩)⟩` and prove the remaining obligations. Use `show (w : ℤ̂) ∈ t1`. Use `hM1 _ ?_` and prove the remaining obligations. Rewrite using `[map_one, ← ProfiniteInteger.castHom_proj hd1, hw, map_one]`. Use `show (((w⁻¹ : ℤ̂ˣ) : ℤ̂)) ∈ MulOpposite.op ⁻¹' t2`.

Use `hM2 _ ?_` and prove the remaining obligations. Establish `hinv : ProfiniteInteger.proj (M1 * M2) ((w⁻¹ : ℤ̂ˣ) : ℤ̂) = 1`. Use `congrArg (ProfiniteInteger.proj (M1 * M2)) (Units.inv_mul w)` as an intermediate fact. Rewrite `this` using `[map_mul, hw, mul_one, map_one]`. Then use the resulting hypothesis. Rewrite using `[map_one, ← ProfiniteInteger.castHom_proj hd2, hinv, map_one]`.
-/
theorem exists_forall_proj_eq_one_mem {H : Subgroup ℤ̂ˣ} (hH : IsOpen (H : Set ℤ̂ˣ)) :
    ∃ M : ℕ+, ∀ w : ℤ̂ˣ, ProfiniteInteger.proj M (w : ℤ̂) = 1 → w ∈ H := by
  have h1 : (H : Set ℤ̂ˣ) ∈ 𝓝 (1 : ℤ̂ˣ) := hH.mem_nhds H.one_mem
  rw [Units.isEmbedding_embedProduct.isInducing.nhds_eq_comap, Filter.mem_comap] at h1
  obtain ⟨t, ht, hsub⟩ := h1
  rw [map_one, Prod.one_eq_mk, nhds_prod_eq, Filter.mem_prod_iff] at ht
  obtain ⟨t1, ht1, t2, ht2, ht12⟩ := ht
  have ht2' : (MulOpposite.op ⁻¹' t2 : Set ℤ̂) ∈ 𝓝 (1 : ℤ̂) :=
    MulOpposite.continuous_op.continuousAt.preimage_mem_nhds (by rwa [MulOpposite.op_one])
  obtain ⟨M1, hM1⟩ := exists_proj_eq_mem ht1
  obtain ⟨M2, hM2⟩ := exists_proj_eq_mem ht2'
  have hd1 : (M1 : ℕ) ∣ ((M1 * M2 : ℕ+) : ℕ) := by rw [PNat.mul_coe]; exact dvd_mul_right _ _
  have hd2 : (M2 : ℕ) ∣ ((M1 * M2 : ℕ+) : ℕ) := by rw [PNat.mul_coe]; exact dvd_mul_left _ _
  refine ⟨M1 * M2, fun w hw ↦ hsub (ht12 ⟨?_, ?_⟩)⟩
  · show (w : ℤ̂) ∈ t1
    refine hM1 _ ?_
    rw [map_one, ← ProfiniteInteger.castHom_proj hd1, hw, map_one]
  · show (((w⁻¹ : ℤ̂ˣ) : ℤ̂)) ∈ MulOpposite.op ⁻¹' t2
    refine hM2 _ ?_
    have hinv : ProfiniteInteger.proj (M1 * M2) ((w⁻¹ : ℤ̂ˣ) : ℤ̂) = 1 := by
      have := congrArg (ProfiniteInteger.proj (M1 * M2)) (Units.inv_mul w)
      rwa [map_mul, hw, mul_one, map_one] at this
    rw [map_one, ← ProfiniteInteger.castHom_proj hd2, hinv, map_one]

/- English proof (translation)
Set `φ : ℤ̂ˣ →* Circle` to `(ω : IdeleClassGroup ℚ →* Circle).comp unitSection`. Establish `hφc : Continuous φ` using `ω.continuous.comp continuous_unitSection`. Establish `hn : 0 < orderOf ω` using `hω.orderOf_pos`. Establish `hpow : ∀ w, φ w ^ orderOf ω = 1` using `fun w ↦ by`. Express the relevant statement in the definitionally equal form `ω (unitSection w) ^ orderOf ω = 1`.

Rewrite using `[← ContinuousMonoidHom.pow_apply, pow_orderOf_eq_one]`. Both sides reduce to the same expression. Take `⟨M, hM⟩` from `exists_forall_proj_eq_one_mem (isOpen_ker_of_pow_eq_one φ hφc hn hpow)`. Establish `: NeZero (M : ℕ)` using `⟨M.ne_zero⟩`. Establish `hsurj : Function.Surjective (unitsMod (M : ℕ))` using `fun b ↦ by`.

Take `⟨v, hv, hvb⟩` from `exists_frobClass b`. Conclude with `⟨(unitPart (frobClass v))⁻¹, Units.ext (by`. Rewrite using `[coe_unitsMod, proj_unitPart_inv_uniformizer hv, hvb])⟩`. Set `ρ : ℤ̂ˣ →* ℂˣ` to `Circle.toUnits.comp φ⁻¹`. Establish `hker : (unitsMod (M : ℕ)).ker ≤ ρ.ker` using `fun w hw ↦ by`.

Establish `hw' : w ∈ φ.ker` using `hM w (congrArg Units.val hw)`. Rewrite `hw'`, the goal using `[MonoidHom.mem_ker]`. Simplify using `only [ρ, MonoidHom.comp_apply, MonoidHom.inv_apply, hw', inv_one, map_one]`. Set `E : (ZMod (M : ℕ))ˣ →* ℂˣ` to `(unitsMod (M : ℕ)).liftOfSurjective hsurj ⟨ρ, hker⟩`. Establish `hE : ∀ w, E (unitsMod (M : ℕ) w) = ρ w` using `fun w ↦ (unitsMod (M : ℕ)).liftOfRightInverse_comp_apply _ _ ⟨ρ, hker⟩ w`.

Set `χ : DirichletCharacter ℂ (M : ℕ)` to `MulChar.ofUnitHom E`. Establish `hχω : heckeCharacter χ = ω`. Use extensionality with `x`. Rewrite using `[coe_heckeCharacter_apply, ← coe_unitsMod, MulChar.ofUnitHom_coe, hE, apply_eq_unitSection hω x]`. Simplify using `only [ρ, MonoidHom.comp_apply, MonoidHom.inv_apply, map_inv, Circle.toUnits_apply, Units.val_mk0, inv_inv, φ]`.

Both sides reduce to the same expression. Establish `: NeZero χ.conductor` using `⟨χ.conductor_ne_zero⟩`. Conclude with `⟨χ.conductor, this, χ.primitiveCharacter, χ.primitiveCharacter_isPrimitive, (heckeCharacter_primitiveCharacter χ).trans hχω⟩`.
-/
theorem exists_heckeCharacter_eq {ω : HeckeCharacter ℚ} (hω : IsOfFinOrder ω) :
    ∃ (N : ℕ) (_ : NeZero N) (χ : DirichletCharacter ℂ N), χ.IsPrimitive ∧ heckeCharacter χ = ω := by
  let φ : ℤ̂ˣ →* Circle := (ω : IdeleClassGroup ℚ →* Circle).comp unitSection
  have hφc : Continuous φ := ω.continuous.comp continuous_unitSection
  have hn : 0 < orderOf ω := hω.orderOf_pos
  have hpow : ∀ w, φ w ^ orderOf ω = 1 := fun w ↦ by
    change ω (unitSection w) ^ orderOf ω = 1
    rw [← ContinuousMonoidHom.pow_apply, pow_orderOf_eq_one]
    rfl
  obtain ⟨M, hM⟩ := exists_forall_proj_eq_one_mem (isOpen_ker_of_pow_eq_one φ hφc hn hpow)
  have : NeZero (M : ℕ) := ⟨M.ne_zero⟩
  have hsurj : Function.Surjective (unitsMod (M : ℕ)) := fun b ↦ by
    obtain ⟨v, hv, hvb⟩ := exists_frobClass b
    exact ⟨(unitPart (frobClass v))⁻¹, Units.ext (by
      rw [coe_unitsMod, proj_unitPart_inv_uniformizer hv, hvb])⟩
  let ρ : ℤ̂ˣ →* ℂˣ := Circle.toUnits.comp φ⁻¹
  have hker : (unitsMod (M : ℕ)).ker ≤ ρ.ker := fun w hw ↦ by
    have hw' : w ∈ φ.ker := hM w (congrArg Units.val hw)
    rw [MonoidHom.mem_ker] at hw' ⊢
    simp only [ρ, MonoidHom.comp_apply, MonoidHom.inv_apply, hw', inv_one, map_one]
  let E : (ZMod (M : ℕ))ˣ →* ℂˣ := (unitsMod (M : ℕ)).liftOfSurjective hsurj ⟨ρ, hker⟩
  have hE : ∀ w, E (unitsMod (M : ℕ) w) = ρ w := fun w ↦
    (unitsMod (M : ℕ)).liftOfRightInverse_comp_apply _ _ ⟨ρ, hker⟩ w
  let χ : DirichletCharacter ℂ (M : ℕ) := MulChar.ofUnitHom E
  have hχω : heckeCharacter χ = ω := by
    ext x
    rw [coe_heckeCharacter_apply, ← coe_unitsMod, MulChar.ofUnitHom_coe, hE, apply_eq_unitSection hω x]
    simp only [ρ, MonoidHom.comp_apply, MonoidHom.inv_apply, map_inv, Circle.toUnits_apply,
      Units.val_mk0, inv_inv, φ]
    rfl
  have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  exact ⟨χ.conductor, this, χ.primitiveCharacter, χ.primitiveCharacter_isPrimitive,
    (heckeCharacter_primitiveCharacter χ).trans hχω⟩

def PrimitiveDirichletCharacter : Type :=
  Σ N : ℕ+, {χ : DirichletCharacter ℂ N // χ.IsPrimitive}

def toFiniteOrder (χ : PrimitiveDirichletCharacter) : {ω : HeckeCharacter ℚ // IsOfFinOrder ω} :=
  ⟨heckeCharacter χ.2.1, isOfFinOrder_heckeCharacter χ.2.1⟩

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨N, χ, hχ⟩ ⟨M, ψ, hψ⟩ h`. Establish `h' : heckeCharacter χ = heckeCharacter ψ` using `congrArg Subtype.val h`. Take `⟨hNM, hχψ⟩` from `eq_of_heckeCharacter_eq hχ hψ h'`. Take `rfl : N = M` from `PNat.coe_injective hNM`.

Take `rfl` from `eq_of_heq hχψ`. Both sides reduce to the same expression. Introduce and unpack `⟨ω, hω⟩`. Take `⟨N, hN, χ, hχ, h⟩` from `exists_heckeCharacter_eq hω`. Conclude with `⟨⟨⟨N, Nat.pos_of_ne_zero hN.out⟩, χ, hχ⟩, Subtype.ext h⟩`.
-/
theorem bijective_toFiniteOrder : Function.Bijective toFiniteOrder := by
  constructor
  · rintro ⟨N, χ, hχ⟩ ⟨M, ψ, hψ⟩ h
    have h' : heckeCharacter χ = heckeCharacter ψ := congrArg Subtype.val h
    obtain ⟨hNM, hχψ⟩ := eq_of_heckeCharacter_eq hχ hψ h'
    obtain rfl : N = M := PNat.coe_injective hNM
    obtain rfl := eq_of_heq hχψ
    rfl
  · rintro ⟨ω, hω⟩
    obtain ⟨N, hN, χ, hχ, h⟩ := exists_heckeCharacter_eq hω
    exact ⟨⟨⟨N, Nat.pos_of_ne_zero hN.out⟩, χ, hχ⟩, Subtype.ext h⟩

def finiteOrderEquiv : PrimitiveDirichletCharacter ≃ {ω : HeckeCharacter ℚ // IsOfFinOrder ω} :=
  Equiv.ofBijective toFiniteOrder bijective_toFiniteOrder

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coe_finiteOrderEquiv_apply (χ : PrimitiveDirichletCharacter) :
    (finiteOrderEquiv χ : HeckeCharacter ℚ) = heckeCharacter χ.2.1 :=
  rfl

end DirichletHecke

end

end GroundTheory.Global
