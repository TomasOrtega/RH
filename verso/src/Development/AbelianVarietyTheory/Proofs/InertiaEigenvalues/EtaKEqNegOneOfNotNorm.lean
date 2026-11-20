import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitting
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuadraticStarStructure
import GroundTheory.LocalFields.UnramifiedNormSurj
import GroundTheory.LocalFields.UnramifiedGalois
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.NonNorm

open ValuativeRel GroundTheory.LocalField IntermediateField

/- English proof (translation)
Use `haveI : FiniteDimensional K L := Module.finite_of_finrank_pos (by omega)`. Take `⟨vK, tK, hK, eK⟩` from `exists_isNonarchimedeanLocalField_valuativeExtension F K`. Take `⟨vL, tL, hL, eL⟩` from `exists_isNonarchimedeanLocalField_valuativeExtension K L`. Establish `hm : ((Nat.card 𝓀[F] ^ 2 - 1 : ℕ) : 𝓀[K]) ≠ 0` using `natCast_residueField_ne_zero K (natCast_card_pow_sub_one_ne_zero (K := F) two_ne_zero)`. Use `haveI : IsUnramified K L := ⟨ramificationIndex_eq_one_of_adjoin_eq_top hζ hm htop⟩`.

Establish `hodd : ¬ (2 : ℤ) ∣ ord s`. Introduce `hd`. Establish `h` using `(mem_range_normUnits_iff (K := K) (L := L) (Units.mk0 s hs0)).2 (by rw [h2]; exact hd)`. Take `⟨y, hy⟩` from `h`. Conclude with `hs ⟨y, congrArg Units.val hy⟩`.

Establish `hf : ¬ 2 ∣ residueDegree F K`. Introduce and unpack `⟨j, hj⟩`. Establish `hcard : Nat.card 𝓀[K] = Nat.card 𝓀[F] ^ residueDegree F K`. Rewrite using `[residueDegree_eq_finrank]`. Conclude with `Module.natCard_eq_pow_finrank`.

Take `⟨z, hz⟩` from `exists_isPrimitiveRoot_card_residueField_sub_one (L := K)`. Establish `hz1 : IsPrimitiveRoot (z : K) (Nat.card 𝓀[K] - 1)` using `hz.map_of_injective (f := (𝒪[K]).subtype) Subtype.val_injective`. Establish `hz2 : IsPrimitiveRoot (algebraMap K L z) (Nat.card 𝓀[K] - 1)` using `hz1.map_of_injective (algebraMap K L).injective`. Use `haveI : NeZero (Nat.card 𝓀[K] - 1) := ⟨by have := one_lt_card_residueField K; omega⟩`. Establish `hdvd : Nat.card 𝓀[F] ^ 2 - 1 ∣ Nat.card 𝓀[K] - 1`.

Rewrite using `[hcard, hj, pow_mul]`. Conclude with `Nat.sub_one_dvd_pow_sub_one _ _`. Take `⟨i, -, hi⟩` from `hz2.eq_pow_of_pow_eq_one ((hζ.pow_eq_one_iff_dvd _).2 hdvd)`. Establish `hbot : K⟮ζ⟯ = ⊥`. Rewrite using `[adjoin_simple_eq_bot_iff, ← hi, ← map_pow]`.

Conclude with `IntermediateField.algebraMap_mem _ _`. Establish `h1 : Module.finrank K L = 1`. Rewrite using `[← finrank_top', ← htop, hbot, IntermediateField.finrank_bot]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[ord_norm]`.

Introduce `hd`. Break down `(Int.prime_two.dvd_or_dvd hd) with h | h` into its components or cases. Conclude with `hf (by exact_mod_cast h)`. Conclude with `hodd h`.
-/
theorem not_two_dvd_ord_norm (F K L : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [Field K] [Algebra F K] [FiniteDimensional F K]
    [Field L] [Algebra K L] (h2 : Module.finrank K L = 2) (ζ : L)
    (hζ : IsPrimitiveRoot ζ (Nat.card 𝓀[F] ^ 2 - 1)) (htop : K⟮ζ⟯ = ⊤) (s : K) (hs0 : s ≠ 0)
    (hs : ¬ ∃ y : L, Algebra.norm K y = s) : ¬ (2 : ℤ) ∣ ord (Algebra.norm F s) := by
  haveI : FiniteDimensional K L := Module.finite_of_finrank_pos (by omega)
  obtain ⟨vK, tK, hK, eK⟩ := exists_isNonarchimedeanLocalField_valuativeExtension F K
  obtain ⟨vL, tL, hL, eL⟩ := exists_isNonarchimedeanLocalField_valuativeExtension K L
  have hm : ((Nat.card 𝓀[F] ^ 2 - 1 : ℕ) : 𝓀[K]) ≠ 0 :=
    natCast_residueField_ne_zero K (natCast_card_pow_sub_one_ne_zero (K := F) two_ne_zero)
  haveI : IsUnramified K L := ⟨ramificationIndex_eq_one_of_adjoin_eq_top hζ hm htop⟩
  have hodd : ¬ (2 : ℤ) ∣ ord s := by
    intro hd
    have h := (mem_range_normUnits_iff (K := K) (L := L) (Units.mk0 s hs0)).2 (by rw [h2]; exact hd)
    obtain ⟨y, hy⟩ := h
    exact hs ⟨y, congrArg Units.val hy⟩
  have hf : ¬ 2 ∣ residueDegree F K := by
    rintro ⟨j, hj⟩
    have hcard : Nat.card 𝓀[K] = Nat.card 𝓀[F] ^ residueDegree F K := by
      rw [residueDegree_eq_finrank]
      exact Module.natCard_eq_pow_finrank
    obtain ⟨z, hz⟩ := exists_isPrimitiveRoot_card_residueField_sub_one (L := K)
    have hz1 : IsPrimitiveRoot (z : K) (Nat.card 𝓀[K] - 1) :=
      hz.map_of_injective (f := (𝒪[K]).subtype) Subtype.val_injective
    have hz2 : IsPrimitiveRoot (algebraMap K L z) (Nat.card 𝓀[K] - 1) :=
      hz1.map_of_injective (algebraMap K L).injective
    haveI : NeZero (Nat.card 𝓀[K] - 1) := ⟨by have := one_lt_card_residueField K; omega⟩
    have hdvd : Nat.card 𝓀[F] ^ 2 - 1 ∣ Nat.card 𝓀[K] - 1 := by
      rw [hcard, hj, pow_mul]
      exact Nat.sub_one_dvd_pow_sub_one _ _
    obtain ⟨i, -, hi⟩ := hz2.eq_pow_of_pow_eq_one ((hζ.pow_eq_one_iff_dvd _).2 hdvd)
    have hbot : K⟮ζ⟯ = ⊥ := by
      rw [adjoin_simple_eq_bot_iff, ← hi, ← map_pow]
      exact IntermediateField.algebraMap_mem _ _
    have h1 : Module.finrank K L = 1 := by
      rw [← finrank_top', ← htop, hbot, IntermediateField.finrank_bot]
    omega
  rw [ord_norm]
  intro hd
  rcases (Int.prime_two.dvd_or_dvd hd) with h | h
  · exact hf (by exact_mod_cast h)
  · exact hodd h

@[reducible] noncomputable def normRel (F : Type) [NormedField F] [IsUltrametricDist F] : ValuativeRel F :=
  ValuativeRel.ofValuation (NormedField.valuation (K := F))

/- English proof (translation)
Use `letI := normRel F`. Establish `hc : (NormedField.valuation (K` using `F)).Compatible := Valuation.Compatible.ofValuation _`. Use `{ toIsValuativeTopology := ?_, toLocallyCompactSpace := inferInstance, toIsNontrivial := ?_ }` and prove the remaining obligations. Conclude with `IsValuativeTopology.of_mem_nhds_zero_iff_vle (NormedField.valuation (K := F)) (fun {s} => (NormedField.toValued (K := F)).is_topological_valuation s)`. Rewrite using `[isNontrivial_iff_isNontrivial (NormedField.valuation (K := F))] infer_instance`.
-/
theorem isLocalField (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] [LocallyCompactSpace F] :
    letI := normRel F
    IsNonarchimedeanLocalField F := by
  letI := normRel F
  have hc : (NormedField.valuation (K := F)).Compatible := Valuation.Compatible.ofValuation _
  refine { toIsValuativeTopology := ?_, toLocallyCompactSpace := inferInstance, toIsNontrivial := ?_ }
  · exact IsValuativeTopology.of_mem_nhds_zero_iff_vle (NormedField.valuation (K := F))
      (fun {s} => (NormedField.toValued (K := F)).is_topological_valuation s)
  · rw [isNontrivial_iff_isNontrivial (NormedField.valuation (K := F))]
    infer_instance

/- English proof (translation)
The claim follows from `isLocalField F ord x = ord y := by letI := normRel F haveI := isLocalField F have h1 : x ≤ᵥ y := h.le have h2 : y ≤ᵥ x := h.ge rw [(valuation F).vle_iff_le] at h1 h2 unfold ord rw [normalizedValuation_eq_iff.2 (le_antisymm h1 h2)]`.
-/
theorem ord_eq_of_norm_eq (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] [LocallyCompactSpace F]
    (x y : F) (h : ‖x‖ = ‖y‖) :
    letI := normRel F
    haveI := isLocalField F
    ord x = ord y := by
  letI := normRel F
  haveI := isLocalField F
  have h1 : x ≤ᵥ y := h.le
  have h2 : y ≤ᵥ x := h.ge
  rw [(valuation F).vle_iff_le] at h1 h2
  unfold ord
  rw [normalizedValuation_eq_iff.2 (le_antisymm h1 h2)]

/- English proof (translation)
Introduce `F E _ _ _ _ hU A hK hL s hs`. Use `haveI := hU.ultraF`. Use `haveI := hU.ultraE`. Use `haveI := hU.lcF`. Use `haveI := hU.lcE`.

Use `letI := normRel F`. Use `letI := normRel E`. Use `haveI := isLocalField F`. Use `haveI := isLocalField E`. Use `haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hU.finrank_eq]; norm_num)`.

Use `haveI : ValuativeExtension F E := ⟨fun a b => by`. Express the relevant statement in the definitionally equal form `‖algebraMap F E a‖ ≤ ‖algebraMap F E b‖ ↔ ‖a‖ ≤ ‖b‖`. Rewrite using `[norm_algebraMap', norm_algebraMap']⟩`. Establish `he : ramificationIndex F E = 1`. Take `⟨π, hπ⟩` from `IsDiscreteValuationRing.exists_irreducible 𝒪[E]`.

Take `⟨x, hx⟩` from `hU.unram (π : E)`. Establish `h1` using `ord_eq_of_norm_eq E (π : E) (algebraMap F E x) (by rw [norm_algebraMap', hx])`. Rewrite `h1` using `[ord_uniformizer hπ, ord_algebraMap]`. Establish `h2 : (ramificationIndex F E : ℤ) ∣ 1` using `⟨_, h1⟩`. Conclude with `Nat.dvd_one.1 (by exact_mod_cast h2)`.

Take `⟨ζ, hζ, htop⟩` from `exists_isPrimitiveRoot_adjoin_eq_top_of_unramified F E he`. Establish `hcard : Nat.card 𝓀[E] = Nat.card 𝓀[F] ^ 2`. Rewrite using `[← hU.finrank_eq, ← residueDegree_eq_finrank_of_unramified F E he, residueDegree_eq_finrank]`. Conclude with `Module.natCard_eq_pow_finrank`. Rewrite `hζ` using `[hcard]`.

Take `⟨⟨b⟩, -⟩` from `Et.quadratic_structure F E A`. Use `letI : Field A.K := hK.toField`. Use `letI : Field A.L := hL.toField`. Establish `h2 : Module.finrank A.K A.L = 2` using `by simpa using Module.finrank_eq_card_basis b`. Establish `hζ' : IsPrimitiveRoot (algebraMap E A.L ζ) (Nat.card 𝓀[F] ^ 2 - 1)` using `hζ.map_of_injective (algebraMap E A.L).injective`.

Establish `hE : ∀ e : E, algebraMap E A.L e ∈ A.K⟮algebraMap E A.L ζ⟯`. Introduce `e`. Establish `he' : e ∈ F⟮ζ⟯` using `by rw [htop]; trivial`. Proceed by induction on `he' using IntermediateField.adjoin_induction with`. Consider the case `mem x hx`.

Rewrite using `[Set.mem_singleton_iff.1 hx]`. Conclude with `mem_adjoin_simple_self _ _`. Consider the case `algebraMap x`. Rewrite using `[← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply F A.K A.L]`. Conclude with `IntermediateField.algebraMap_mem _ _`.

Consider the case `add x y _ _ hx hy => rw [map_add]`. Conclude with `add_mem hx hy`. Consider the case `inv x _ hx => rw [map_inv₀]`. Conclude with `inv_mem hx`. Consider the case `mul x y _ _ hx hy => rw [map_mul]`.

Conclude with `mul_mem hx hy`. Establish `htop' : A.K⟮algebraMap E A.L ζ⟯ = ⊤`. Rewrite using `[eq_top_iff]`. Introduce `y _`. Establish `hbc` using `A.push.symm.out`.

Proceed by induction on `y using hbc.inductionOn with`. Consider the case `zero => exact zero_mem _`. Consider the case `tmul e => exact hE e`. Consider the case `smul k y hy => exact IntermediateField.smul_mem _ (hy trivial)`. Consider the case `add y z hy hz => exact add_mem (hy trivial) (hz trivial)`.

Establish `hodd` using `not_two_dvd_ord_norm F A.K A.L h2 _ hζ' htop' s s.ne_zero hs`. Unfold `Et.etaK eta`. Rewrite using `[if_neg]`. Introduce and unpack `⟨y, hy⟩`. Apply `hodd` to reduce the goal to its premises.

Establish `hy0 : y ≠ 0`. Introduce and unpack `rfl`. Establish `h0 : Algebra.norm F (s : A.K) = 0` using `norm_eq_zero.1 (by simpa using hy)`. Conclude with `s.ne_zero (Algebra.norm_eq_zero_iff.1 h0)`. Establish `h3` using `ord_eq_of_norm_eq F (Algebra.norm F (s : A.K)) (y ^ 2) (by rw [norm_pow, hy])`.

Rewrite `h3` using `[ord_pow hy0]`. Conclude with `⟨ord y, by exact_mod_cast h3⟩`.
-/
theorem etaK_eq_neg_one : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E), IsField A.K → IsField A.L → ∀ s : A.Kˣ, (¬ ∃ y : A.L, A.NL y = s) → A.etaK s = -1 := by
  intro F E _ _ _ _ hU A hK hL s hs
  haveI := hU.ultraF
  haveI := hU.ultraE
  haveI := hU.lcF
  haveI := hU.lcE
  letI := normRel F
  letI := normRel E
  haveI := isLocalField F
  haveI := isLocalField E
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hU.finrank_eq]; norm_num)
  haveI : ValuativeExtension F E := ⟨fun a b => by
    change ‖algebraMap F E a‖ ≤ ‖algebraMap F E b‖ ↔ ‖a‖ ≤ ‖b‖
    rw [norm_algebraMap', norm_algebraMap']⟩
  have he : ramificationIndex F E = 1 := by
    obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[E]
    obtain ⟨x, hx⟩ := hU.unram (π : E)
    have h1 := ord_eq_of_norm_eq E (π : E) (algebraMap F E x) (by rw [norm_algebraMap', hx])
    rw [ord_uniformizer hπ, ord_algebraMap] at h1
    have h2 : (ramificationIndex F E : ℤ) ∣ 1 := ⟨_, h1⟩
    exact Nat.dvd_one.1 (by exact_mod_cast h2)
  obtain ⟨ζ, hζ, htop⟩ := exists_isPrimitiveRoot_adjoin_eq_top_of_unramified F E he
  have hcard : Nat.card 𝓀[E] = Nat.card 𝓀[F] ^ 2 := by
    rw [← hU.finrank_eq, ← residueDegree_eq_finrank_of_unramified F E he, residueDegree_eq_finrank]
    exact Module.natCard_eq_pow_finrank
  rw [hcard] at hζ
  obtain ⟨⟨b⟩, -⟩ := Et.quadratic_structure F E A
  letI : Field A.K := hK.toField
  letI : Field A.L := hL.toField
  have h2 : Module.finrank A.K A.L = 2 := by simpa using Module.finrank_eq_card_basis b
  have hζ' : IsPrimitiveRoot (algebraMap E A.L ζ) (Nat.card 𝓀[F] ^ 2 - 1) :=
    hζ.map_of_injective (algebraMap E A.L).injective
  have hE : ∀ e : E, algebraMap E A.L e ∈ A.K⟮algebraMap E A.L ζ⟯ := by
    intro e
    have he' : e ∈ F⟮ζ⟯ := by rw [htop]; trivial
    induction he' using IntermediateField.adjoin_induction with
    | mem x hx =>
      rw [Set.mem_singleton_iff.1 hx]
      exact mem_adjoin_simple_self _ _
    | algebraMap x =>
      rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply F A.K A.L]
      exact IntermediateField.algebraMap_mem _ _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | inv x _ hx => rw [map_inv₀]; exact inv_mem hx
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  have htop' : A.K⟮algebraMap E A.L ζ⟯ = ⊤ := by
    rw [eq_top_iff]
    intro y _
    have hbc := A.push.symm.out
    induction y using hbc.inductionOn with
    | zero => exact zero_mem _
    | tmul e => exact hE e
    | smul k y hy => exact IntermediateField.smul_mem _ (hy trivial)
    | add y z hy hz => exact add_mem (hy trivial) (hz trivial)
  have hodd := not_two_dvd_ord_norm F A.K A.L h2 _ hζ' htop' s s.ne_zero hs
  unfold Et.etaK eta
  rw [if_neg]
  rintro ⟨y, hy⟩
  apply hodd
  have hy0 : y ≠ 0 := by
    rintro rfl
    have h0 : Algebra.norm F (s : A.K) = 0 := norm_eq_zero.1 (by simpa using hy)
    exact s.ne_zero (Algebra.norm_eq_zero_iff.1 h0)
  have h3 := ord_eq_of_norm_eq F (Algebra.norm F (s : A.K)) (y ^ 2) (by rw [norm_pow, hy])
  rw [ord_pow hy0] at h3
  exact ⟨ord y, by exact_mod_cast h3⟩

end GlobalTheory.JR.NonNorm
