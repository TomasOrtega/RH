import Mathlib
import ReciprocityTheory.ClassFieldTheory.LocalClassField.RecPairDefs
import ReciprocityTheory.ClassFieldTheory.LocalClassField.PairKEqZeroOfMemNormGrp
import ReciprocityTheory.ClassFieldTheory.LocalClassField.NormLimit
import ReciprocityTheory.ClassFieldTheory.LocalClassField.NormOpen
import ReciprocityTheory.ClassFieldTheory.LocalClassField.Kummer
import ReciprocityTheory.ClassFieldTheory.LocalClassField.BaseCase
import ReciprocityTheory.ClassFieldTheory.LocalClassField.ExistenceA
import ReciprocityTheory.ClassFieldTheory.LocalClassField.ExistenceB

namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ReciprocityTheory.Coh Function

variable (p : ℕ) [Fact p.Prime] (K L : IntermediateField ℚ_[p] (PadicAlgCl p))

variable {p K L}

/- English proof (translation)
The claim follows from `card_character_n_torsion hn hμ`.
-/
theorem card_char_torsion {n : ℕ} (hn : 0 < n) (hμ : ∀ ζ : PadicAlgCl p, ζ ^ n = 1 → ζ ∈ K) :
    Nat.card {χ : charGrp (GK p K) // n • χ = 0} = (powMonoidHom n : Kˣ →* Kˣ).range.index :=
  card_character_n_torsion hn hμ

/- English proof (translation)
The claim follows from `exists_maximal_exponent_abelian_extension hK hfin`.
-/
theorem exists_maxExp (hK : FiniteDimensional ℚ_[p] K) {n : ℕ} (hn : 0 < n) (hfin : Finite {χ : charGrp (GK p K) // n • χ = 0}) :
    ∃ L : IntermediateField ℚ_[p] (PadicAlgCl p), IsAbLK p K L ∧ ∀ χ : charGrp (GK p K), TrivOn p K L χ ↔ n • χ = 0 :=
  exists_maximal_exponent_abelian_extension hK hfin

/- English proof (translation)
The claim follows from `maximal_exponent_extension_stable h₀ hK₀ hL hL' σ x hx`.
-/
theorem maxExp_stable {K₀ : IntermediateField ℚ_[p] (PadicAlgCl p)} (h₀ : K₀ ≤ K) (hK₀ : ∀ (σ : GK p K₀), ∀ x ∈ K, σ x ∈ K) {n : ℕ}
    (hL : IsAbLK p K L) (hL' : ∀ χ : charGrp (GK p K), TrivOn p K L χ ↔ n • χ = 0) (σ : GK p K₀) (x : PadicAlgCl p)
    (hx : x ∈ L) : σ x ∈ L := maximal_exponent_extension_stable h₀ hK₀ hL hL' σ x hx

/- English proof (translation)
Establish `hle : (powMonoidHom n : Kˣ →* Kˣ).range ≤ normGrp p K L`. Introduce and unpack `_ ⟨a, rfl⟩`. Establish `h1 : IsRecip p K L (a ^ n) 1`. Introduce `χ hχ`. Rewrite using `[pairK_pow, ← pairK_nsmul, (hL' χ).1 hχ, pairK_zero]`.

Conclude with `map_zero χ.1`. Conclude with `(h1.mem_subG_iff hK hL).1 (subG p K L).one_mem`. Establish `hidx : (normGrp p K L).index = (powMonoidHom n : Kˣ →* Kˣ).range.index`. Rewrite using `[index_normGrp hK hL, ← card_trivOn hL, ← card_char_torsion hn hμ]`. Conclude with `Nat.card_congr (Equiv.subtypeEquivRight hL')`.

Establish `hfi` using `finiteIndex_range_pow hK hn`. Establish `h2` using `Subgroup.relIndex_mul_index hle`. Rewrite `h2` using `[hidx]`. Establish `h3 : (powMonoidHom n : Kˣ →* Kˣ).range.relIndex (normGrp p K L) = 1` using `Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hfi.index_ne_zero) (by rw [h2, one_mul])`. Conclude with `le_antisymm (Subgroup.relIndex_eq_one.1 h3) hle`.
-/
theorem normGrp_maxExp (hK : FiniteDimensional ℚ_[p] K) {n : ℕ} (hn : 0 < n) (hμ : ∀ ζ : PadicAlgCl p, ζ ^ n = 1 → ζ ∈ K)
    (hL : IsAbLK p K L) (hL' : ∀ χ : charGrp (GK p K), TrivOn p K L χ ↔ n • χ = 0) :
    normGrp p K L = (powMonoidHom n : Kˣ →* Kˣ).range := by
  have hle : (powMonoidHom n : Kˣ →* Kˣ).range ≤ normGrp p K L := by
    rintro _ ⟨a, rfl⟩
    have h1 : IsRecip p K L (a ^ n) 1 := by
      intro χ hχ
      rw [pairK_pow, ← pairK_nsmul, (hL' χ).1 hχ, pairK_zero]
      exact map_zero χ.1
    exact (h1.mem_subG_iff hK hL).1 (subG p K L).one_mem
  have hidx : (normGrp p K L).index = (powMonoidHom n : Kˣ →* Kˣ).range.index := by
    rw [index_normGrp hK hL, ← card_trivOn hL, ← card_char_torsion hn hμ]
    exact Nat.card_congr (Equiv.subtypeEquivRight hL')
  have hfi := finiteIndex_range_pow hK hn
  have h2 := Subgroup.relIndex_mul_index hle
  rw [hidx] at h2
  have h3 : (powMonoidHom n : Kˣ →* Kˣ).range.relIndex (normGrp p K L) = 1 :=
    Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hfi.index_ne_zero) (by rw [h2, one_mul])
  exact le_antisymm (Subgroup.relIndex_eq_one.1 h3) hle

/- English proof (translation)
The claim follows from `isAbelian_cyclotomic_extension hK hn`.
-/
theorem isAbLK_cyclotomic (hK : FiniteDimensional ℚ_[p] K) {n : ℕ} (hn : 0 < n) :
    IsAbLK p K (K ⊔ IntermediateField.adjoin ℚ_[p] {ζ : PadicAlgCl p | ζ ^ n = 1}) := isAbelian_cyclotomic_extension hK hn

/- English proof (translation)
The claim follows from `isSolvable_of_abelian_tower hM hL`.
-/
theorem isSolvable_of_ab_of_ab {M : IntermediateField ℚ_[p] (PadicAlgCl p)} (hM : IsAbLK p K M) (hL : IsAbLK p M L) [(subG p K L).Normal] :
    Group.IsSolvable (GalLK p K L) := isSolvable_of_abelian_tower hM hL

/- English proof (translation)
Assemble the required witnesses or components as `⟨unitOf p K ⟨x, hx⟩, Units.ext rfl⟩`.
-/
theorem exists_unit_ofK (x : KbarMult p) (hx : x ∈ multOf p K) : ∃ u : Kˣ, ofK p K (Additive.ofMul u) = x :=
  ⟨unitOf p K ⟨x, hx⟩, Units.ext rfl⟩

/- English proof (translation)
Introduce `a b hab`. Establish `h1 : Units.map (algebraMap K (PadicAlgCl p) : K →* PadicAlgCl p) a.toMul = Units.map (algebraMap K (PadicAlgCl p) : K →* PadicAlgCl p) b.toMul` using `hab`. Conclude with `Units.map_injective (algebraMap K (PadicAlgCl p)).injective h1`.
-/
theorem ofK_injective' : Injective (ofK p K) := by
  intro a b hab
  have h1 : Units.map (algebraMap K (PadicAlgCl p) : K →* PadicAlgCl p) a.toMul =
      Units.map (algebraMap K (PadicAlgCl p) : K →* PadicAlgCl p) b.toMul := hab
  exact Units.map_injective (algebraMap K (PadicAlgCl p)).injective h1

/- English proof (translation)
Take `⟨M, hMdef⟩ : ∃ M, M = K ⊔ IntermediateField.adjoin ℚ_[p] {ζ : PadicAlgCl p | ζ ^ n = 1}` from `⟨_, rfl⟩`. Establish `hM : IsAbLK p K M` using `hMdef ▸ isAbLK_cyclotomic hK hn`. Establish `hμ : ∀ ζ : PadicAlgCl p, ζ ^ n = 1 → ζ ∈ M` using `fun ζ hζ => by`. Rewrite using `[hMdef]`. Conclude with `(le_sup_right : _ ≤ K ⊔ _) (IntermediateField.subset_adjoin _ _ hζ)`.

Establish `hfinM` using `hM.fin`. Establish `hfin : Finite {χ : charGrp (GK p M) // n • χ = 0}`. Apply `Nat.finite_of_card_ne_zero` to reduce the goal to its premises. Rewrite using `[card_char_torsion hn hμ]`. Conclude with `(finiteIndex_range_pow hfinM hn).index_ne_zero`.

Take `⟨L, hL, hL'⟩` from `exists_maxExp hfinM hn hfin`. Establish `hMst : ∀ (σ : GK p K), ∀ x ∈ M, σ x ∈ M` using `(subG_normal_iff hM.le).1 hM.normal`. Establish `hst : ∀ (σ : GK p K), ∀ x ∈ L, σ x ∈ L` using `fun σ x hx => maxExp_stable hM.le hMst hL hL' σ x hx`. Establish `: (subG p K L).Normal` using `subG_normal_of_stable hst`. Establish `hKL : K ≤ L` using `hM.le.trans hL.le`.

Establish `hsol` using `isSolvable_of_ab_of_ab hM hL`. Take `⟨E, hE, hEL, hE'⟩` from `exists_maxAb hL.fin hKL`. Use `⟨E, hE, ?_⟩` and prove the remaining obligations. Rewrite using `[← normGrp_eq_of_soluble hK hL.fin hKL hsol hE hEL hE']`. Introduce `x hx`.

Take `⟨y, hy, hxy⟩` from `(mem_normGrp_iff p K L x).1 hx`. Rewrite `hxy` using `[← normHom_trans hL.fin hM.le hL.le y hy]`. Take `⟨z, hz⟩` from `exists_unit_ofK _ (normHom_mem hL.fin hL.le y hy)`. Establish `hzN : z ∈ normGrp p M L` using `(mem_normGrp_iff p M L z).2 ⟨y, hy, hz.symm⟩`. Rewrite `hzN` using `[normGrp_maxExp hfinM hn hμ hL hL']`.

Take `⟨w, rfl⟩` from `hzN`. Take `⟨u, hu⟩` from `exists_unit_ofK (K := K) _ (normHom_mem hfinM hM.le _ (ofK_mem p M (Additive.ofMul w)))`. Use `⟨u, ?_⟩` and prove the remaining obligations. Apply `Additive.ofMul.injective` to reduce the goal to its premises. Apply `ofK_injective' (K := K)` to reduce the goal to its premises.

Rewrite using `[← hxy, ← hz]`. Use `show ofK p K (n • Additive.ofMul u) = normHom p K M (ofK p M (n • Additive.ofMul w))`. Rewrite using `[map_nsmul, map_nsmul, map_nsmul, hu]`.
-/
theorem exists_normGrp_le_pow (hK : FiniteDimensional ℚ_[p] K) {n : ℕ} (hn : 0 < n) :
    ∃ E : IntermediateField ℚ_[p] (PadicAlgCl p), IsAbLK p K E ∧ normGrp p K E ≤ (powMonoidHom n : Kˣ →* Kˣ).range := by
  obtain ⟨M, hMdef⟩ : ∃ M, M = K ⊔ IntermediateField.adjoin ℚ_[p] {ζ : PadicAlgCl p | ζ ^ n = 1} := ⟨_, rfl⟩
  have hM : IsAbLK p K M := hMdef ▸ isAbLK_cyclotomic hK hn
  have hμ : ∀ ζ : PadicAlgCl p, ζ ^ n = 1 → ζ ∈ M := fun ζ hζ => by
    rw [hMdef]
    exact (le_sup_right : _ ≤ K ⊔ _) (IntermediateField.subset_adjoin _ _ hζ)
  have hfinM := hM.fin
  have hfin : Finite {χ : charGrp (GK p M) // n • χ = 0} := by
    apply Nat.finite_of_card_ne_zero
    rw [card_char_torsion hn hμ]
    exact (finiteIndex_range_pow hfinM hn).index_ne_zero
  obtain ⟨L, hL, hL'⟩ := exists_maxExp hfinM hn hfin
  have hMst : ∀ (σ : GK p K), ∀ x ∈ M, σ x ∈ M := (subG_normal_iff hM.le).1 hM.normal
  have hst : ∀ (σ : GK p K), ∀ x ∈ L, σ x ∈ L := fun σ x hx => maxExp_stable hM.le hMst hL hL' σ x hx
  have : (subG p K L).Normal := subG_normal_of_stable hst
  have hKL : K ≤ L := hM.le.trans hL.le
  have hsol := isSolvable_of_ab_of_ab hM hL
  obtain ⟨E, hE, hEL, hE'⟩ := exists_maxAb hL.fin hKL
  refine ⟨E, hE, ?_⟩
  rw [← normGrp_eq_of_soluble hK hL.fin hKL hsol hE hEL hE']
  intro x hx
  obtain ⟨y, hy, hxy⟩ := (mem_normGrp_iff p K L x).1 hx
  rw [← normHom_trans hL.fin hM.le hL.le y hy] at hxy
  obtain ⟨z, hz⟩ := exists_unit_ofK _ (normHom_mem hL.fin hL.le y hy)
  have hzN : z ∈ normGrp p M L := (mem_normGrp_iff p M L z).2 ⟨y, hy, hz.symm⟩
  rw [normGrp_maxExp hfinM hn hμ hL hL'] at hzN
  obtain ⟨w, rfl⟩ := hzN
  obtain ⟨u, hu⟩ := exists_unit_ofK (K := K) _ (normHom_mem hfinM hM.le _ (ofK_mem p M (Additive.ofMul w)))
  refine ⟨u, ?_⟩
  apply Additive.ofMul.injective
  apply ofK_injective' (K := K)
  rw [← hxy, ← hz]
  show ofK p K (n • Additive.ofMul u) = normHom p K M (ofK p M (n • Additive.ofMul w))
  rw [map_nsmul, map_nsmul, map_nsmul, hu]

/- English proof (translation)
Take `⟨E, hE, hEle⟩` from `exists_normGrp_le_pow hK (n := H.index) (Nat.pos_of_ne_zero hH.index_ne_zero)`. Take `⟨L₀, h1, -, h2⟩` from `exists_normGrp_eq_of_le hK hE H (hEle.trans (by`. Introduce and unpack `_ ⟨a, rfl⟩`. Conclude with `Subgroup.pow_index_mem H a))`. Conclude with `⟨L₀, h1, h2⟩`.
-/
theorem existence (hK : FiniteDimensional ℚ_[p] K) (H : Subgroup Kˣ) (hH : H.FiniteIndex) :
    ∃ L : IntermediateField ℚ_[p] (PadicAlgCl p), IsAbLK p K L ∧ normGrp p K L = H := by
  obtain ⟨E, hE, hEle⟩ := exists_normGrp_le_pow hK (n := H.index) (Nat.pos_of_ne_zero hH.index_ne_zero)
  obtain ⟨L₀, h1, -, h2⟩ := exists_normGrp_eq_of_le hK hE H (hEle.trans (by
    rintro _ ⟨a, rfl⟩; exact Subgroup.pow_index_mem H a))
  exact ⟨L₀, h1, h2⟩

/- English proof (translation)
Establish `hε : 0 < ‖((a : K) : PadicAlgCl p) - 1‖`. Rewrite using `[norm_pos_iff, sub_ne_zero]`. Introduce `h`. Conclude with `ha (Units.ext (Subtype.ext h))`. Establish `he : (0 : ℝ) < eK p K` using `by exact_mod_cast eK_pos p K hK`.

Establish `hp1 : (1 : ℝ) < p` using `by exact_mod_cast (Fact.out : p.Prime).one_lt`. Establish `hp0 : (0 : ℝ) < p` using `zero_lt_one.trans hp1`. Establish `hq1 : (p : ℝ) ^ (- 1 / (eK p K : ℝ)) < 1` using `Real.rpow_lt_one_of_one_lt_of_neg hp1 (div_neg_of_neg_of_pos (by norm_num) he)`. Take `⟨i, hi⟩` from `exists_pow_lt_of_lt_one hε hq1`. Use `⟨i, fun hx => absurd (lt_of_le_of_lt ((mem_UKi_iff p K i a).1 hx).2 ?_) (lt_irrefl _)⟩` and prove the remaining obligations.

Rewrite `hi` using `[← Real.rpow_natCast, ← Real.rpow_mul hp0.le]`. Use `hi using 2` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_not_mem_UKi (hK : FiniteDimensional ℚ_[p] K) (a : Kˣ) (ha : a ≠ 1) : ∃ i, a ∉ UKi p K i := by
  have hε : 0 < ‖((a : K) : PadicAlgCl p) - 1‖ := by
    rw [norm_pos_iff, sub_ne_zero]
    intro h
    exact ha (Units.ext (Subtype.ext h))
  have he : (0 : ℝ) < eK p K := by exact_mod_cast eK_pos p K hK
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hp0 : (0 : ℝ) < p := zero_lt_one.trans hp1
  have hq1 : (p : ℝ) ^ (- 1 / (eK p K : ℝ)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg hp1 (div_neg_of_neg_of_pos (by norm_num) he)
  obtain ⟨i, hi⟩ := exists_pow_lt_of_lt_one hε hq1
  refine ⟨i, fun hx => absurd (lt_of_le_of_lt ((mem_UKi_iff p K i a).1 hx).2 ?_) (lt_irrefl _)⟩
  rw [← Real.rpow_natCast, ← Real.rpow_mul hp0.le] at hi
  convert hi using 2
  ring

/- English proof (translation)
Assume the negation of the conclusion as `ha`. Take `⟨π, hπ⟩` from `exists_vK_eq_one p K hK`. Take `⟨i, hi⟩` from `exists_not_mem_UKi hK a ha`. Take `⟨m, hm⟩ : ∃ m : ℕ, m = (vK p K a).natAbs + 1` from `⟨_, rfl⟩`. Establish `hopen : IsOpen ((UKi p K i ⊔ Subgroup.zpowers (π ^ m) : Subgroup Kˣ) : Set Kˣ)` using `Subgroup.isOpen_mono le_sup_left (isOpen_UKi i)`.

Establish `hfi : (UKi p K i ⊔ Subgroup.zpowers (π ^ m)).FiniteIndex` using `finiteIndex_of_isOpen_of_vK hK _ hopen (x := π ^ m) ((le_sup_right : _ ≤ UKi p K i ⊔ _) (Subgroup.mem_zpowers _)) (by rw [vK_pow, hπ, hm]; positivity)`. Take `⟨L, hL, hLH⟩` from `existence hK _ hfi`. Establish `haH : a ∈ UKi p K i ⊔ Subgroup.zpowers (π ^ m)` using `hLH ▸ h L hL`. Take `⟨u, hu, w, hw, rfl⟩` from `Subgroup.mem_sup.1 haH`. Take `⟨k, rfl⟩` from `Subgroup.mem_zpowers_iff.1 hw`.

Establish `hu0 : vK p K u = 0` using `(mem_UK_iff p K hK u).1 ((mem_UKi_iff p K i u).1 hu).1`. Establish `hv : vK p K (u * (π ^ m) ^ k) = k * m`. Rewrite using `[vK_mul, hu0, vK_zpow, vK_pow, hπ]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `hm` using `[hv]`.

Establish `hk : k = 0`. Assume the negation of the conclusion as `hk`. Establish `h1 : 1 ≤ k.natAbs` using `Int.natAbs_pos.2 hk`. Rewrite `hm` using `[Int.natAbs_mul, Int.natAbs_natCast]`. Use the polynomial consequences of the given equalities and inequalities.

Rewrite `hi` using `[hk, zpow_zero, mul_one]`. Conclude with `hi hu`.
-/
theorem eq_one_of_forall_mem_normGrp (hK : FiniteDimensional ℚ_[p] K) (a : Kˣ) (h : ∀ L, IsAbLK p K L → a ∈ normGrp p K L) : a = 1 := by
  by_contra ha
  obtain ⟨π, hπ⟩ := exists_vK_eq_one p K hK
  obtain ⟨i, hi⟩ := exists_not_mem_UKi hK a ha
  obtain ⟨m, hm⟩ : ∃ m : ℕ, m = (vK p K a).natAbs + 1 := ⟨_, rfl⟩
  have hopen : IsOpen ((UKi p K i ⊔ Subgroup.zpowers (π ^ m) : Subgroup Kˣ) : Set Kˣ) :=
    Subgroup.isOpen_mono le_sup_left (isOpen_UKi i)
  have hfi : (UKi p K i ⊔ Subgroup.zpowers (π ^ m)).FiniteIndex :=
    finiteIndex_of_isOpen_of_vK hK _ hopen (x := π ^ m)
      ((le_sup_right : _ ≤ UKi p K i ⊔ _) (Subgroup.mem_zpowers _)) (by rw [vK_pow, hπ, hm]; positivity)
  obtain ⟨L, hL, hLH⟩ := existence hK _ hfi
  have haH : a ∈ UKi p K i ⊔ Subgroup.zpowers (π ^ m) := hLH ▸ h L hL
  obtain ⟨u, hu, w, hw, rfl⟩ := Subgroup.mem_sup.1 haH
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hw
  have hu0 : vK p K u = 0 := (mem_UK_iff p K hK u).1 ((mem_UKi_iff p K i u).1 hu).1
  have hv : vK p K (u * (π ^ m) ^ k) = k * m := by
    rw [vK_mul, hu0, vK_zpow, vK_pow, hπ]; ring
  rw [hv] at hm
  have hk : k = 0 := by
    by_contra hk
    have h1 : 1 ≤ k.natAbs := Int.natAbs_pos.2 hk
    rw [Int.natAbs_mul, Int.natAbs_natCast] at hm
    nlinarith
  rw [hk, zpow_zero, mul_one] at hi
  exact hi hu

end ReciprocityTheory.DiscreteGroups.LocalClassField
