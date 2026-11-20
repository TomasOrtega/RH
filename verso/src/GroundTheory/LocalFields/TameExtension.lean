import Mathlib
import GroundTheory.LocalFields.ExtensionsOfDegree
import GroundTheory.LocalFields.RamificationTameStructure
import GroundTheory.LocalFields.MaximalUnramified
import GroundTheory.LocalFields.SeparableClosure
import GroundTheory.LocalFields.UnramifiedExistence
import GroundTheory.LocalFields.Unramified

noncomputable section

open Polynomial IntermediateField ValuativeRel

namespace GroundTheory.LocalField

section Definition

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [Algebra K Ω]

def IsTameSubextension (E : IntermediateField K Ω) : Prop :=
  FiniteDimensional K E ∧
    ∀ (_ : ValuativeRel E) (_ : TopologicalSpace E) (_ : IsNonarchimedeanLocalField E)
      (_ : ValuativeExtension K E), Nat.Coprime (ramificationIndex K E) (ringChar 𝓀[K])

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hfin, h⟩`. Conclude with `⟨hfin, (finiteExtensionStructure K E).rel, (finiteExtensionStructure K E).top, finiteExtensionStructure_isNonarchimedeanLocalField K E, finiteExtensionStructure_valuativeExtension K E, h (finiteExtensionStructure K E).rel (finiteExtensionStructure K E).top (finiteExtensionStructu …`. Introduce and unpack `⟨hfin, v₁, t₁, h₁, e₁, h⟩`. Use `⟨hfin, fun v₂ t₂ h₂ e₂ ↦ ?_⟩` and prove the remaining obligations.

Take `rfl` from `valuativeRel_unique K h₁ h₂ e₁ e₂`. Conclude with `h`.
-/
theorem isTameSubextension_iff_exists (E : IntermediateField K Ω) :
    IsTameSubextension E ↔ FiniteDimensional K E ∧
      ∃ (_ : ValuativeRel E) (_ : TopologicalSpace E) (_ : IsNonarchimedeanLocalField E)
        (_ : ValuativeExtension K E), Nat.Coprime (ramificationIndex K E) (ringChar 𝓀[K]) := by
  constructor
  · rintro ⟨hfin, h⟩
    exact ⟨hfin, (finiteExtensionStructure K E).rel, (finiteExtensionStructure K E).top,
      finiteExtensionStructure_isNonarchimedeanLocalField K E,
      finiteExtensionStructure_valuativeExtension K E,
      h (finiteExtensionStructure K E).rel (finiteExtensionStructure K E).top
        (finiteExtensionStructure_isNonarchimedeanLocalField K E)
        (finiteExtensionStructure_valuativeExtension K E)⟩
  · rintro ⟨hfin, v₁, t₁, h₁, e₁, h⟩
    refine ⟨hfin, fun v₂ t₂ h₂ e₂ ↦ ?_⟩
    obtain rfl := valuativeRel_unique K h₁ h₂ e₁ e₂
    exact h

/- English proof (translation)
The claim follows from `hE.2 inferInstance inferInstance inferInstance inferInstance`.
-/
theorem IsTameSubextension.coprime {E : IntermediateField K Ω} (hE : IsTameSubextension E)
    [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] [ValuativeExtension K E] :
    Nat.Coprime (ramificationIndex K E) (ringChar 𝓀[K]) :=
  hE.2 inferInstance inferInstance inferInstance inferInstance

/- English proof (translation)
Assemble the required witnesses or components as `⟨hE.1, fun _ _ _ _ ↦ by rw [hE.ramificationIndex_eq_one]; exact Nat.coprime_one_left _⟩`.
-/
theorem IsUnramifiedSubextension.isTameSubextension {E : IntermediateField K Ω}
    (hE : IsUnramifiedSubextension E) : IsTameSubextension E :=
  ⟨hE.1, fun _ _ _ _ ↦ by rw [hE.ramificationIndex_eq_one]; exact Nat.coprime_one_left _⟩

variable (K Ω) in

def tameExtension : IntermediateField K Ω :=
  ⨆ E : {E : IntermediateField K Ω // IsTameSubextension E}, E.1

/- English proof (translation)
The claim follows from `le_iSup (fun E : {E : IntermediateField K Ω // IsTameSubextension E} ↦ E.1) ⟨E, hE⟩`.
-/
theorem IsTameSubextension.le_tameExtension {E : IntermediateField K Ω}
    (hE : IsTameSubextension E) : E ≤ tameExtension K Ω :=
  le_iSup (fun E : {E : IntermediateField K Ω // IsTameSubextension E} ↦ E.1) ⟨E, hE⟩

variable (K Ω) in

/- English proof (translation)
The claim follows from `iSup_le fun E ↦ E.2.isTameSubextension.le_tameExtension`.
-/
theorem maximalUnramifiedExtension_le_tameExtension :
    maximalUnramifiedExtension K Ω ≤ tameExtension K Ω :=
  iSup_le fun E ↦ E.2.isTameSubextension.le_tameExtension

end Definition

/- English proof (translation)
The claim follows from `Module.Finite.of_injective (IntermediateField.inclusion h).toLinearMap (IntermediateField.inclusion_injective h)`.
-/
theorem finiteDimensional_of_le {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]
    {E F : IntermediateField K Ω} [FiniteDimensional K F] (h : E ≤ F) : FiniteDimensional K E :=
  Module.Finite.of_injective (IntermediateField.inclusion h).toLinearMap
    (IntermediateField.inclusion_injective h)

section Valued

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω]

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun h ↦ h.coprime, fun h ↦ (isTameSubextension_iff_exists E).2 ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, h⟩⟩`.
-/
theorem isTameSubextension_iff (E : IntermediateField K Ω) [FiniteDimensional K E] :
    IsTameSubextension E ↔ Nat.Coprime (ramificationIndex K E) (ringChar 𝓀[K]) :=
  ⟨fun h ↦ h.coprime, fun h ↦ (isTameSubextension_iff_exists E).2
    ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, h⟩⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun h ↦ h.ramificationIndex_eq_one, fun h ↦ (isUnramifiedSubextension_iff_exists E).2 ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, h⟩⟩`.
-/
theorem isUnramifiedSubextension_iff' (E : IntermediateField K Ω) [FiniteDimensional K E] :
    IsUnramifiedSubextension E ↔ ramificationIndex K E = 1 :=
  ⟨fun h ↦ h.ramificationIndex_eq_one, fun h ↦ (isUnramifiedSubextension_iff_exists E).2
    ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, h⟩⟩

/- English proof (translation)
Establish `: FiniteDimensional K F` using `Module.Finite.trans T F`. Establish `: FiniteDimensional K (F.restrictScalars K)` using `this`. Establish `h1 : Nat.card 𝓀[F.restrictScalars K] = Nat.card 𝓀[K] ^ residueDegree K (F.restrictScalars K)` using `card_residueField_eq_pow_residueDegree K _`. Establish `h2 : Nat.card 𝓀[F] = Nat.card 𝓀[T] ^ residueDegree T F` using `card_residueField_eq_pow_residueDegree T F`. Establish `h3 : Nat.card 𝓀[T] = Nat.card 𝓀[K] ^ residueDegree K T` using `card_residueField_eq_pow_residueDegree K T`.

Establish `h4 : Nat.card 𝓀[F.restrictScalars K] = Nat.card 𝓀[F]` using `rfl`. Rewrite `h1` using `[h4, h2, h3, ← pow_mul]`. Conclude with `(Nat.pow_right_injective (one_lt_card_residueField K) h1).symm`.
-/
theorem residueDegree_restrictScalars (T : IntermediateField K Ω) [FiniteDimensional K T]
    (F : IntermediateField T Ω) [FiniteDimensional T F] :
    residueDegree K (F.restrictScalars K) = residueDegree K T * residueDegree T F := by
  have : FiniteDimensional K F := Module.Finite.trans T F
  have : FiniteDimensional K (F.restrictScalars K) := this
  have h1 : Nat.card 𝓀[F.restrictScalars K] = Nat.card 𝓀[K] ^ residueDegree K (F.restrictScalars K) :=
    card_residueField_eq_pow_residueDegree K _
  have h2 : Nat.card 𝓀[F] = Nat.card 𝓀[T] ^ residueDegree T F :=
    card_residueField_eq_pow_residueDegree T F
  have h3 : Nat.card 𝓀[T] = Nat.card 𝓀[K] ^ residueDegree K T :=
    card_residueField_eq_pow_residueDegree K T
  have h4 : Nat.card 𝓀[F.restrictScalars K] = Nat.card 𝓀[F] := rfl
  rw [h4, h2, h3, ← pow_mul] at h1
  exact (Nat.pow_right_injective (one_lt_card_residueField K) h1).symm

/- English proof (translation)
Establish `: FiniteDimensional K F` using `Module.Finite.trans T F`. Establish `: FiniteDimensional K (F.restrictScalars K)` using `this`. Establish `hf` using `residueDegree_restrictScalars T F`. Establish `h1` using `ramificationIndex_mul_residueDegree K (F.restrictScalars K)`. Establish `h2` using `ramificationIndex_mul_residueDegree K T`.

Establish `h3` using `ramificationIndex_mul_residueDegree T F`. Establish `h4 : Module.finrank K (F.restrictScalars K) = Module.finrank K T * Module.finrank T F` using `(Module.finrank_mul_finrank K T F).symm`. Rewrite `h1` using `[h4, ← h2, ← h3, hf]`. Establish `hpos : 0 < residueDegree K T * residueDegree T F` using `Nat.mul_pos (residueDegree_pos K T) (residueDegree_pos T F)`. Conclude with `Nat.eq_of_mul_eq_mul_right hpos (by rw [h1]; ring)`.
-/
theorem ramificationIndex_restrictScalars (T : IntermediateField K Ω) [FiniteDimensional K T]
    (F : IntermediateField T Ω) [FiniteDimensional T F] :
    ramificationIndex K (F.restrictScalars K) = ramificationIndex K T * ramificationIndex T F := by
  have : FiniteDimensional K F := Module.Finite.trans T F
  have : FiniteDimensional K (F.restrictScalars K) := this
  have hf := residueDegree_restrictScalars T F
  have h1 := ramificationIndex_mul_residueDegree K (F.restrictScalars K)
  have h2 := ramificationIndex_mul_residueDegree K T
  have h3 := ramificationIndex_mul_residueDegree T F
  have h4 : Module.finrank K (F.restrictScalars K) = Module.finrank K T * Module.finrank T F :=
    (Module.finrank_mul_finrank K T F).symm
  rw [h4, ← h2, ← h3, hf] at h1
  have hpos : 0 < residueDegree K T * residueDegree T F :=
    Nat.mul_pos (residueDegree_pos K T) (residueDegree_pos T F)
  exact Nat.eq_of_mul_eq_mul_right hpos (by rw [h1]; ring)

/- English proof (translation)
Use `hF.1` as an intermediate fact. Establish `: FiniteDimensional K E` using `finiteDimensional_of_le h`. Use `set F' := extendScalars h`. Establish `: FiniteDimensional K F'` using `(inferInstance : FiniteDimensional K F)`. Establish `: FiniteDimensional E F'` using `Module.Finite.of_restrictScalars_finite K E F'`.

Rewrite using `[isTameSubextension_iff]`. Establish `he : ramificationIndex K F = ramificationIndex K E * ramificationIndex E F'` using `ramificationIndex_restrictScalars E F'`. Conclude with `Nat.Coprime.coprime_dvd_left (Dvd.intro _ he.symm) hF.coprime`.
-/
theorem IsTameSubextension.of_le {E F : IntermediateField K Ω} (hF : IsTameSubextension F)
    (h : E ≤ F) : IsTameSubextension E := by
  have := hF.1
  have : FiniteDimensional K E := finiteDimensional_of_le h
  set F' := extendScalars h
  have : FiniteDimensional K F' := (inferInstance : FiniteDimensional K F)
  have : FiniteDimensional E F' := Module.Finite.of_restrictScalars_finite K E F'
  rw [isTameSubextension_iff]
  have he : ramificationIndex K F = ramificationIndex K E * ramificationIndex E F' :=
    ramificationIndex_restrictScalars E F'
  exact Nat.Coprime.coprime_dvd_left (Dvd.intro _ he.symm) hF.coprime

end Valued

section SlopeTestRemainingChoices

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/- English proof (translation)
Rewrite using `[Ne, CharP.cast_eq_zero_iff 𝓀[K] (ringChar 𝓀[K])]`. Introduce `hd`. Establish `h1` using `Nat.Coprime.eq_one_of_dvd hm.symm hd`. Conclude with `Nat.not_prime_one (h1 ▸ CharP.char_is_prime 𝓀[K] (ringChar 𝓀[K]))`.
-/
theorem natCast_residueField_ne_zero_of_coprime {m : ℕ} (hm : Nat.Coprime m (ringChar 𝓀[K])) :
    (m : 𝓀[K]) ≠ 0 := by
  rw [Ne, CharP.cast_eq_zero_iff 𝓀[K] (ringChar 𝓀[K])]
  intro hd
  have h1 := Nat.Coprime.eq_one_of_dvd hm.symm hd
  exact Nat.not_prime_one (h1 ▸ CharP.char_is_prime 𝓀[K] (ringChar 𝓀[K]))

/- English proof (translation)
Introduce and unpack `rfl`. Conclude with `natCast_residueField_ne_zero_of_coprime (K := K) hm Nat.cast_zero`.
-/
theorem ne_zero_of_coprime_ringChar {m : ℕ} (hm : Nat.Coprime m (ringChar 𝓀[K])) : m ≠ 0 := by
  rintro rfl
  exact natCast_residueField_ne_zero_of_coprime (K := K) hm Nat.cast_zero

/- English proof (translation)
Establish `hu : IsUnramified K L` using `(isUnramified_iff K L).2 h`. Establish `hmap` using `(map_maximalIdeal_eq_iff K L).2 hu`. Rewrite `hπ`, the goal using `[IsDiscreteValuationRing.irreducible_iff_uniformizer]`. Rewrite using `[← hmap, hπ, Ideal.map_span, Set.image_singleton]`.
-/
theorem irreducible_algebraMap_of_ramificationIndex_eq_one {L : Type*} [Field L] [ValuativeRel L]
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L]
    [FiniteDimensional K L] (h : ramificationIndex K L = 1) {π : 𝒪[K]} (hπ : Irreducible π) :
    Irreducible (algebraMap 𝒪[K] 𝒪[L] π) := by
  have hu : IsUnramified K L := (isUnramified_iff K L).2 h
  have hmap := (map_maximalIdeal_eq_iff K L).2 hu
  rw [IsDiscreteValuationRing.irreducible_iff_uniformizer] at hπ ⊢
  rw [← hmap, hπ, Ideal.map_span, Set.image_singleton]

/- English proof (translation)
Break down `subsingleton_or_nontrivial R with hR | hR` into its components or cases. Conclude with `absurd (Subsingleton.elim P ⊤) hP`. Use `⟨?_, fun {n} hn ↦ ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[(monic_X_pow_sub_C a hm.ne').leadingCoeff]`. Conclude with `fun h ↦ hP ((Ideal.eq_top_iff_one _).2 h)`.

Rewrite `hn` using `[natDegree_X_pow_sub_C]`. Rewrite using `[coeff_sub, coeff_X_pow, if_neg hn.ne, coeff_C, zero_sub]`. Use `split_ifs`. Conclude with `P.neg_mem ha`. Rewrite using `[neg_zero]`.

Conclude with `P.zero_mem`. Rewrite using `[coeff_sub, coeff_X_pow, if_neg hm.ne, coeff_C, if_pos rfl, zero_sub]`. Conclude with `fun h ↦ ha2 ((P ^ 2).neg_mem_iff.1 h)`.
-/
theorem isEisensteinAt_X_pow_sub_C {R : Type*} [CommRing R] {P : Ideal R} (hP : P ≠ ⊤) {m : ℕ}
    (hm : 0 < m) {a : R} (ha : a ∈ P) (ha2 : a ∉ P ^ 2) : (X ^ m - C a).IsEisensteinAt P := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact absurd (Subsingleton.elim P ⊤) hP
  refine ⟨?_, fun {n} hn ↦ ?_, ?_⟩
  · rw [(monic_X_pow_sub_C a hm.ne').leadingCoeff]
    exact fun h ↦ hP ((Ideal.eq_top_iff_one _).2 h)
  · rw [natDegree_X_pow_sub_C] at hn
    rw [coeff_sub, coeff_X_pow, if_neg hn.ne, coeff_C, zero_sub]
    split_ifs
    · exact P.neg_mem ha
    · rw [neg_zero]
      exact P.zero_mem
  · rw [coeff_sub, coeff_X_pow, if_neg hm.ne, coeff_C, if_pos rfl, zero_sub]
    exact fun h ↦ ha2 ((P ^ 2).neg_mem_iff.1 h)

variable {Ω : Type*} [Field Ω] [Algebra K Ω]

/- English proof (translation)
Use `choose n hn0 hn using hS`. Use `set k := ∏ x ∈ S.attach, n x.1 x.2 with hk_def`. Establish `hk : k ≠ 0` using `Finset.prod_ne_zero_iff.2 fun x _ ↦ hn0 x.1 x.2`. Take `⟨ζ, hζ⟩` from `HasUnramifiedRoots.exists_isPrimitiveRoot (K := K) (Ω := Ω) k hk`. Use `⟨k, hk, ζ, hζ, fun x hx ↦ ?_⟩` and prove the remaining obligations.

Establish `hdvd : n x hx ∣ k` using `Finset.dvd_prod_of_mem (fun y : S ↦ n y.1 y.2) (Finset.mem_attach S ⟨x, hx⟩)`. Establish `hx1 : x ^ (Nat.card 𝓀[K] ^ k - 1) = 1`. Take `⟨c, hc⟩` from `pow_sub_one_dvd_pow_sub_one (Nat.card 𝓀[K]) hdvd`. Rewrite using `[hc, pow_mul, hn x hx, one_pow]`. Establish `: NeZero (Nat.card 𝓀[K] ^ k - 1)` using `⟨by have := one_lt_card_residueField_pow (K := K) hk; omega⟩`.

Take `⟨i, -, rfl⟩` from `hζ.eq_pow_of_pow_eq_one hx1`. Conclude with `pow_mem (mem_adjoin_simple_self K ζ) i`.
-/
theorem exists_isPrimitiveRoot_forall_mem_adjoin [HasUnramifiedRoots K Ω] (S : Finset Ω)
    (hS : ∀ x ∈ S, x ∈ unramifiedRoots K Ω) :
    ∃ k : ℕ, k ≠ 0 ∧ ∃ ζ : Ω, IsPrimitiveRoot ζ (Nat.card 𝓀[K] ^ k - 1) ∧ ∀ x ∈ S, x ∈ K⟮ζ⟯ := by
  classical
  choose n hn0 hn using hS
  set k := ∏ x ∈ S.attach, n x.1 x.2 with hk_def
  have hk : k ≠ 0 := Finset.prod_ne_zero_iff.2 fun x _ ↦ hn0 x.1 x.2
  obtain ⟨ζ, hζ⟩ := HasUnramifiedRoots.exists_isPrimitiveRoot (K := K) (Ω := Ω) k hk
  refine ⟨k, hk, ζ, hζ, fun x hx ↦ ?_⟩
  have hdvd : n x hx ∣ k := Finset.dvd_prod_of_mem (fun y : S ↦ n y.1 y.2) (Finset.mem_attach S ⟨x, hx⟩)
  have hx1 : x ^ (Nat.card 𝓀[K] ^ k - 1) = 1 := by
    obtain ⟨c, hc⟩ := pow_sub_one_dvd_pow_sub_one (Nat.card 𝓀[K]) hdvd
    rw [hc, pow_mul, hn x hx, one_pow]
  have : NeZero (Nat.card 𝓀[K] ^ k - 1) :=
    ⟨by have := one_lt_card_residueField_pow (K := K) hk; omega⟩
  obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hx1
  exact pow_mem (mem_adjoin_simple_self K ζ) i

end SlopeTestRemainingChoices

section Valued

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω]

/- English proof (translation)
Establish `hm0 : 0 < m` using `Nat.pos_of_ne_zero (ne_zero_of_coprime_ringChar hm)`. Take `⟨hT, -⟩` from `isUnramifiedSubextension_adjoin hk hζ`. Use `set T := K⟮ζ⟯ with hT_def`. Use `hT.1` as an intermediate fact. Establish `heT : ramificationIndex K T = 1` using `hT.ramificationIndex_eq_one`.

Use `set πT : 𝒪[T] := algebraMap 𝒪[K] 𝒪[T] π with hπT_def`. Establish `hπT : Irreducible πT` using `irreducible_algebraMap_of_ramificationIndex_eq_one heT hπ`. Use `set g : 𝒪[T][X] := X ^ m - C πT with hg_def`. Establish `hgE : g.IsEisensteinAt 𝓂[T]`. Use `isEisensteinAt_X_pow_sub_C (IsLocalRing.maximalIdeal.isMaximal _).ne_top hm0 (uniformizer_mem_maximalIdeal hπT) ?_` and prove the remaining obligations.

Rewrite using `[(IsDiscreteValuationRing.irreducible_iff_uniformizer _).1 hπT, Ideal.span_singleton_pow, Ideal.mem_span_singleton]`. Introduce `hd`. Use `(_root_.pow_dvd_pow_iff hπT.ne_zero hπT.not_isUnit).1 (by rwa [pow_one] : πT ^ 2 ∣ πT ^ 1)` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hgdeg : g.natDegree = m` using `natDegree_X_pow_sub_C`.

Establish `hπΩ : algebraMap T Ω ((πT : 𝒪[T]) : T) = algebraMap K Ω π`. Rewrite using `[hπT_def, coe_algebraMap_integer, ← IsScalarTower.algebraMap_apply]`. Establish `hγT : aeval γ (g.map (algebraMap 𝒪[T] T)) = 0`. Rewrite using `[hg_def, Polynomial.map_sub, Polynomial.map_pow, map_X, map_C, map_sub, map_pow, aeval_X, aeval_C, sub_eq_zero, hγ]`. Conclude with `hπΩ.symm`.

Establish `hγint : IsIntegral T γ` using `⟨g.map (algebraMap 𝒪[T] T), (monic_X_pow_sub_C _ hm0.ne').map _, by rwa [← aeval_def]⟩`. Establish `: FiniteDimensional T T⟮γ⟯` using `adjoin.finiteDimensional hγint`. Use `set α := AdjoinSimple.gen T γ`. Establish `hα : aeval α g = 0`. Apply `(algebraMap T⟮γ⟯ Ω).injective` to reduce the goal to its premises.

Rewrite using `[← aeval_algebraMap_apply, IntermediateField.algebraMap_apply, AdjoinSimple.coe_gen, map_zero, ← aeval_map_algebraMap T]`. Conclude with `hγT`. Establish `he : ramificationIndex T T⟮γ⟯ = m`. Rewrite using `[← hgdeg]`. Conclude with `ramificationIndex_eq_natDegree_of_isEisensteinAt hgE (by rw [hgdeg]; exact hm0) hα (adjoin_gen_eq_top γ)`.

Establish `hadj : T⟮γ⟯.restrictScalars K = adjoin K {ζ, γ}` using `adjoin_simple_adjoin_simple K ζ γ`. Establish `: FiniteDimensional K T⟮γ⟯` using `Module.Finite.trans T T⟮γ⟯`. Establish `hfin : FiniteDimensional K (T⟮γ⟯.restrictScalars K)` using `this`. Rewrite `hfin` using `[hadj]`. Use `⟨hfin, ?_⟩` and prove the remaining obligations.

Use `ramificationIndex_restrictScalars T T⟮γ⟯` as an intermediate fact. Rewrite `this` using `[heT, one_mul, he]`. Rewrite using `[← hadj]`. Conclude with `this`.
-/
theorem finiteDimensional_adjoin_pair_and_ramificationIndex {k : ℕ} (hk : k ≠ 0) {ζ : Ω}
    (hζ : IsPrimitiveRoot ζ (Nat.card 𝓀[K] ^ k - 1)) {π : 𝒪[K]} (hπ : Irreducible π) {m : ℕ}
    (hm : Nat.Coprime m (ringChar 𝓀[K])) {γ : Ω} (hγ : γ ^ m = algebraMap K Ω π) :
    ∃ _ : FiniteDimensional K (adjoin K {ζ, γ}), ramificationIndex K (adjoin K {ζ, γ}) = m := by
  have hm0 : 0 < m := Nat.pos_of_ne_zero (ne_zero_of_coprime_ringChar hm)
  obtain ⟨hT, -⟩ := isUnramifiedSubextension_adjoin hk hζ
  set T := K⟮ζ⟯ with hT_def
  have := hT.1
  have heT : ramificationIndex K T = 1 := hT.ramificationIndex_eq_one
  set πT : 𝒪[T] := algebraMap 𝒪[K] 𝒪[T] π with hπT_def
  have hπT : Irreducible πT := irreducible_algebraMap_of_ramificationIndex_eq_one heT hπ
  set g : 𝒪[T][X] := X ^ m - C πT with hg_def
  have hgE : g.IsEisensteinAt 𝓂[T] := by
    refine isEisensteinAt_X_pow_sub_C (IsLocalRing.maximalIdeal.isMaximal _).ne_top hm0
      (uniformizer_mem_maximalIdeal hπT) ?_
    rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer _).1 hπT, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton]
    intro hd
    have := (_root_.pow_dvd_pow_iff hπT.ne_zero hπT.not_isUnit).1 (by rwa [pow_one] : πT ^ 2 ∣ πT ^ 1)
    omega
  have hgdeg : g.natDegree = m := natDegree_X_pow_sub_C
  have hπΩ : algebraMap T Ω ((πT : 𝒪[T]) : T) = algebraMap K Ω π := by
    rw [hπT_def, coe_algebraMap_integer, ← IsScalarTower.algebraMap_apply]
  have hγT : aeval γ (g.map (algebraMap 𝒪[T] T)) = 0 := by
    rw [hg_def, Polynomial.map_sub, Polynomial.map_pow, map_X, map_C, map_sub, map_pow, aeval_X,
      aeval_C, sub_eq_zero, hγ]
    exact hπΩ.symm
  have hγint : IsIntegral T γ :=
    ⟨g.map (algebraMap 𝒪[T] T), (monic_X_pow_sub_C _ hm0.ne').map _, by rwa [← aeval_def]⟩
  have : FiniteDimensional T T⟮γ⟯ := adjoin.finiteDimensional hγint
  set α := AdjoinSimple.gen T γ
  have hα : aeval α g = 0 := by
    apply (algebraMap T⟮γ⟯ Ω).injective
    rw [← aeval_algebraMap_apply, IntermediateField.algebraMap_apply, AdjoinSimple.coe_gen, map_zero,
      ← aeval_map_algebraMap T]
    exact hγT
  have he : ramificationIndex T T⟮γ⟯ = m := by
    rw [← hgdeg]
    exact ramificationIndex_eq_natDegree_of_isEisensteinAt hgE (by rw [hgdeg]; exact hm0) hα
      (adjoin_gen_eq_top γ)
  have hadj : T⟮γ⟯.restrictScalars K = adjoin K {ζ, γ} := adjoin_simple_adjoin_simple K ζ γ
  have : FiniteDimensional K T⟮γ⟯ := Module.Finite.trans T T⟮γ⟯
  have hfin : FiniteDimensional K (T⟮γ⟯.restrictScalars K) := this
  rw [hadj] at hfin
  refine ⟨hfin, ?_⟩
  have := ramificationIndex_restrictScalars T T⟮γ⟯
  rw [heT, one_mul, he] at this
  rw [← hadj]
  exact this

end Valued

section Structure

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in

/- English proof (translation)
Establish `ht : t ∈ K⟮z⟯` using `by rw [hgen]; trivial`. Establish `: ι t ∈ (K⟮z⟯).map ι` using `(IntermediateField.mem_map _).2 ⟨t, ht, rfl⟩`. Rewrite `this` using `[adjoin_map, Set.image_singleton]`. Then use the resulting hypothesis.
-/
theorem apply_mem_adjoin_of_adjoin_eq_top {A Ω : Type*} [Field A] [Algebra K A] [Field Ω]
    [Algebra K Ω] (ι : A →ₐ[K] Ω) {z : A} (hgen : K⟮z⟯ = ⊤) (t : A) : ι t ∈ K⟮ι z⟯ := by
  have ht : t ∈ K⟮z⟯ := by rw [hgen]; trivial
  have : ι t ∈ (K⟮z⟯).map ι := (IntermediateField.mem_map _).2 ⟨t, ht, rfl⟩
  rwa [adjoin_map, Set.image_singleton] at this

variable {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω]

/- English proof (translation)
Use `hE.1` as an intermediate fact. Use `set e := ramificationIndex K E with he_def`. Establish `he : Nat.Coprime e (ringChar 𝓀[K])` using `hE.coprime`. Take `⟨T₀, hT₀un, -, -, -, -, π₀, hπ₀, α, -, hαpow, hαgen⟩` from `exists_tame_structure K E he`. Establish `heT₀ : ramificationIndex K T₀ = 1` using `(isUnramified_iff K T₀).1 hT₀un`.

Take `⟨ζ₀, hζ₀, hζ₀gen⟩` from `exists_isPrimitiveRoot_adjoin_eq_top_of_unramified K T₀ heT₀`. Establish `hπT₀ : Irreducible (algebraMap 𝒪[K] 𝒪[T₀] π)` using `irreducible_algebraMap_of_ramificationIndex_eq_one heT₀ hπ`. Take `⟨u, hu⟩` from `IsDiscreteValuationRing.associated_of_irreducible 𝒪[T₀] hπT₀ hπ₀`. Use `set t : 𝒪[T₀]ˣ := teichmuller T₀ (unitsToResidue T₀ u) with ht_def`. Establish `ht : t ^ (Nat.card 𝓀[T₀] - 1) = 1` using `teichmuller_pow_card_sub_one _`.

Establish `hw : u * t⁻¹ ∈ unitFiltration T₀ 1` using `unitsMulInvTeichmuller_mem u`. Establish `heK : (e : 𝓀[K]) ≠ 0` using `natCast_residueField_ne_zero_of_coprime he`. Establish `heT₀' : (e : 𝓀[T₀]) ≠ 0` using `natCast_residueField_ne_zero T₀ heK`. Take `⟨w₀, hw₀⟩` from `unitFiltration_one_le_range_pow heT₀' hw`. Establish `hw₀' : w₀ ^ e * t = u`.

Establish `: w₀ ^ e = u * t⁻¹` using `hw₀`. Rewrite using `[this, inv_mul_cancel_right]`. Set `ι : T₀ →ₐ[K] Ω` to `E.val.comp T₀.val`. Establish `hιT₀ : ∀ x : T₀, ι x = ((x : E) : Ω)` using `fun x ↦ rfl`. Take `⟨t', ht'_def⟩ : ∃ x : Ω, x = ι ((t : 𝒪[T₀]) : T₀)` from `⟨_, rfl⟩`.

Take `⟨w', hw'_def⟩ : ∃ x : Ω, x = ι ((w₀ : 𝒪[T₀]) : T₀)` from `⟨_, rfl⟩`. Take `⟨α', hα'_def⟩ : ∃ x : Ω, x = (((α : 𝒪[E]) : E) : Ω)` from `⟨_, rfl⟩`. Establish `he0 : (e : Ω) ≠ 0`. Rewrite using `[← map_natCast (algebraMap K Ω)]`. Conclude with `(map_ne_zero_iff _ (algebraMap K Ω).injective).2 (natCast_ne_zero_of_residueField heK)`.

Establish `: NeZero (e : Ω)` using `⟨he0⟩`. Take `⟨ξ, hξ⟩` from `IsSepClosed.exists_pow_nat_eq t' e`. Establish `ht'0 : t' ≠ 0`. Rewrite using `[ht'_def]`. Conclude with `(map_ne_zero_iff _ ι.injective).2 (by simp)`.

Establish `hw'0 : w' ≠ 0`. Rewrite using `[hw'_def]`. Conclude with `(map_ne_zero_iff _ ι.injective).2 (by simp)`. Establish `hξ0 : ξ ≠ 0`. Introduce and unpack `rfl`.

Rewrite `hξ` using `[zero_pow (ne_zero_of_coprime_ringChar he)]`. Conclude with `ht'0 hξ.symm`. Establish `hα'pow : α' ^ e = algebraMap K Ω π * w' ^ e * t'`. Establish `h1 : α' ^ e = ι ((π₀ : 𝒪[T₀]) : T₀)`. Combine the equalities or inequalities in the displayed calculation.

Establish `h2 : ((π₀ : 𝒪[T₀]) : T₀) = algebraMap K T₀ π * ((w₀ : 𝒪[T₀]) : T₀) ^ e * ((t : 𝒪[T₀]) : T₀)`. Rewrite using `[← hu, ← hw₀']`. Move the coercions through the operations in `[coe_algebraMap_integer]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h1, h2, map_mul, map_mul, map_pow, AlgHom.commutes, ht'_def, hw'_def]`.

Take `⟨γ, hγ_def⟩ : ∃ x : Ω, x = α' / (ξ * w')` from `⟨_, rfl⟩`. Establish `hγ : γ ^ e = algebraMap K Ω π`. Rewrite using `[hγ_def, div_pow, mul_pow, hξ, hα'pow]`. Clear the denominators using the available nonvanishing facts. Establish `hf₀ : residueDegree K T₀ ≠ 0` using `(residueDegree_pos K T₀).ne'`.

Establish `hcard : Nat.card 𝓀[T₀] = Nat.card 𝓀[K] ^ residueDegree K T₀` using `card_residueField_eq_pow_residueDegree K T₀`. Establish `htT : ((t : 𝒪[T₀]) : T₀) ^ (Nat.card 𝓀[T₀] - 1) = 1`. Use `congrArg (fun x : 𝒪[T₀]ˣ ↦ (((x : 𝒪[T₀]) : T₀))) ht` as an intermediate fact. Simplify using `using this`. Establish `hξroot : ξ ^ (e * (Nat.card 𝓀[T₀] - 1)) = 1`.

Rewrite using `[pow_mul, hξ, ht'_def, ← map_pow, htT, map_one]`. Establish `hζ₀root : ι ζ₀ ^ (Nat.card 𝓀[T₀] - 1) = 1`. Rewrite using `[← map_pow, hζ₀.pow_eq_one, map_one]`. Establish `hcK : ((Nat.card 𝓀[T₀] - 1 : ℕ) : 𝓀[K]) ≠ 0`. Rewrite using `[hcard]`.

Conclude with `natCast_card_pow_sub_one_ne_zero hf₀`. Take `⟨k, hk, ζ, hζ, hmem⟩` from `exists_isPrimitiveRoot_forall_mem_adjoin (K := K) {ξ, ι ζ₀} (by`. Introduce `x hx`. Rewrite `hx` using `[Finset.mem_insert, Finset.mem_singleton]`. Break down `hx with rfl | rfl` into its components or cases.

Conclude with `mem_unramifiedRoots_iff.2 ⟨_, by rw [Nat.cast_mul]; exact mul_ne_zero heK hcK, hξroot⟩`. Conclude with `mem_unramifiedRoots_iff.2 ⟨_, hcK, hζ₀root⟩)`. Use `⟨k, hk, ζ, hζ, e, he, γ, hγ, ?_⟩` and prove the remaining obligations. Establish `hζA : K⟮ζ⟯ ≤ adjoin K {ζ, γ}` using `adjoin_simple_le_iff.2 (subset_adjoin K _ (by simp))`. Establish `hγA : γ ∈ adjoin K {ζ, γ}` using `subset_adjoin K _ (by simp)`.

Establish `hT₀A : ∀ x : T₀, ι x ∈ adjoin K {ζ, γ}` using `fun x ↦ hζA (adjoin_simple_le_iff.2 (hmem (ι ζ₀) (by simp)) (apply_mem_adjoin_of_adjoin_eq_top ι hζ₀gen x))`. Establish `hξA : ξ ∈ adjoin K {ζ, γ}` using `hζA (hmem ξ (by simp))`. Establish `hα'A : α' ∈ adjoin K {ζ, γ}`. Establish `: α' = γ * (ξ * w')`. Rewrite using `[hγ_def, div_mul_cancel₀ _ (mul_ne_zero hξ0 hw'0)]`.

Rewrite using `[this]`. Conclude with `mul_mem hγA (mul_mem hξA (hw'_def ▸ hT₀A _))`. Establish `htop : (⊤ : IntermediateField K E) = adjoin K ((T₀ : Set E) ∪ {((α : 𝒪[E]) : E)})`. Rewrite using `[← restrictScalars_adjoin, hαgen, restrictScalars_top]`. Introduce `x hx`.

Establish `hx' : (⟨x, hx⟩ : E) ∈ adjoin K ((T₀ : Set E) ∪ {((α : 𝒪[E]) : E)})`. Rewrite using `[← htop]`. Discharge the goal by the elementary cases of `trivial`. Establish `hxm : E.val ⟨x, hx⟩ ∈ (adjoin K ((T₀ : Set E) ∪ {((α : 𝒪[E]) : E)})).map E.val` using `(IntermediateField.mem_map _).2 ⟨_, hx', rfl⟩`. Rewrite `hxm` using `[adjoin_map]`.

Use `(adjoin_le_iff.2 ?_) hxm` and prove the remaining obligations. Introduce and unpack `_ ⟨y, hy, rfl⟩`. Break down `hy with hy | hy` into its components or cases. Conclude with `hT₀A ⟨y, hy⟩`. Rewrite `hy` using `[Set.mem_singleton_iff]`.

Substitute `hy` using the available equality. Rewrite `hα'A` using `[hα'_def]`. Conclude with `hα'A`.
-/
theorem IsTameSubextension.exists_le_adjoin_pair [IsSepClosed Ω] {E : IntermediateField K Ω}
    (hE : IsTameSubextension E) {π : 𝒪[K]} (hπ : Irreducible π) :
    ∃ k : ℕ, k ≠ 0 ∧ ∃ ζ : Ω, IsPrimitiveRoot ζ (Nat.card 𝓀[K] ^ k - 1) ∧
      ∃ m : ℕ, Nat.Coprime m (ringChar 𝓀[K]) ∧ ∃ γ : Ω, γ ^ m = algebraMap K Ω π ∧
        E ≤ adjoin K {ζ, γ} := by
  have := hE.1
  set e := ramificationIndex K E with he_def
  have he : Nat.Coprime e (ringChar 𝓀[K]) := hE.coprime
  obtain ⟨T₀, hT₀un, -, -, -, -, π₀, hπ₀, α, -, hαpow, hαgen⟩ := exists_tame_structure K E he
  have heT₀ : ramificationIndex K T₀ = 1 := (isUnramified_iff K T₀).1 hT₀un
  obtain ⟨ζ₀, hζ₀, hζ₀gen⟩ := exists_isPrimitiveRoot_adjoin_eq_top_of_unramified K T₀ heT₀
  have hπT₀ : Irreducible (algebraMap 𝒪[K] 𝒪[T₀] π) :=
    irreducible_algebraMap_of_ramificationIndex_eq_one heT₀ hπ
  obtain ⟨u, hu⟩ := IsDiscreteValuationRing.associated_of_irreducible 𝒪[T₀] hπT₀ hπ₀
  set t : 𝒪[T₀]ˣ := teichmuller T₀ (unitsToResidue T₀ u) with ht_def
  have ht : t ^ (Nat.card 𝓀[T₀] - 1) = 1 := teichmuller_pow_card_sub_one _
  have hw : u * t⁻¹ ∈ unitFiltration T₀ 1 := unitsMulInvTeichmuller_mem u
  have heK : (e : 𝓀[K]) ≠ 0 := natCast_residueField_ne_zero_of_coprime he
  have heT₀' : (e : 𝓀[T₀]) ≠ 0 := natCast_residueField_ne_zero T₀ heK
  obtain ⟨w₀, hw₀⟩ := unitFiltration_one_le_range_pow heT₀' hw
  have hw₀' : w₀ ^ e * t = u := by
    have : w₀ ^ e = u * t⁻¹ := hw₀
    rw [this, inv_mul_cancel_right]

  let ι : T₀ →ₐ[K] Ω := E.val.comp T₀.val
  have hιT₀ : ∀ x : T₀, ι x = ((x : E) : Ω) := fun x ↦ rfl
  obtain ⟨t', ht'_def⟩ : ∃ x : Ω, x = ι ((t : 𝒪[T₀]) : T₀) := ⟨_, rfl⟩
  obtain ⟨w', hw'_def⟩ : ∃ x : Ω, x = ι ((w₀ : 𝒪[T₀]) : T₀) := ⟨_, rfl⟩
  obtain ⟨α', hα'_def⟩ : ∃ x : Ω, x = (((α : 𝒪[E]) : E) : Ω) := ⟨_, rfl⟩
  have he0 : (e : Ω) ≠ 0 := by
    rw [← map_natCast (algebraMap K Ω)]
    exact (map_ne_zero_iff _ (algebraMap K Ω).injective).2
      (natCast_ne_zero_of_residueField heK)
  have : NeZero (e : Ω) := ⟨he0⟩
  obtain ⟨ξ, hξ⟩ := IsSepClosed.exists_pow_nat_eq t' e
  have ht'0 : t' ≠ 0 := by
    rw [ht'_def]
    exact (map_ne_zero_iff _ ι.injective).2 (by simp)
  have hw'0 : w' ≠ 0 := by
    rw [hw'_def]
    exact (map_ne_zero_iff _ ι.injective).2 (by simp)
  have hξ0 : ξ ≠ 0 := by
    rintro rfl
    rw [zero_pow (ne_zero_of_coprime_ringChar he)] at hξ
    exact ht'0 hξ.symm

  have hα'pow : α' ^ e = algebraMap K Ω π * w' ^ e * t' := by
    have h1 : α' ^ e = ι ((π₀ : 𝒪[T₀]) : T₀) := by
      calc α' ^ e = (((α ^ e : 𝒪[E]) : E) : Ω) := by rw [hα'_def]; simp
        _ = ι ((π₀ : 𝒪[T₀]) : T₀) := by rw [hαpow, coe_algebraMap_integer]; rfl
    have h2 : ((π₀ : 𝒪[T₀]) : T₀) =
        algebraMap K T₀ π * ((w₀ : 𝒪[T₀]) : T₀) ^ e * ((t : 𝒪[T₀]) : T₀) := by
      rw [← hu, ← hw₀']
      push_cast [coe_algebraMap_integer]
      ring
    rw [h1, h2, map_mul, map_mul, map_pow, AlgHom.commutes, ht'_def, hw'_def]
  obtain ⟨γ, hγ_def⟩ : ∃ x : Ω, x = α' / (ξ * w') := ⟨_, rfl⟩
  have hγ : γ ^ e = algebraMap K Ω π := by
    rw [hγ_def, div_pow, mul_pow, hξ, hα'pow]
    field_simp

  have hf₀ : residueDegree K T₀ ≠ 0 := (residueDegree_pos K T₀).ne'
  have hcard : Nat.card 𝓀[T₀] = Nat.card 𝓀[K] ^ residueDegree K T₀ :=
    card_residueField_eq_pow_residueDegree K T₀
  have htT : ((t : 𝒪[T₀]) : T₀) ^ (Nat.card 𝓀[T₀] - 1) = 1 := by
    have := congrArg (fun x : 𝒪[T₀]ˣ ↦ (((x : 𝒪[T₀]) : T₀))) ht
    simpa using this
  have hξroot : ξ ^ (e * (Nat.card 𝓀[T₀] - 1)) = 1 := by
    rw [pow_mul, hξ, ht'_def, ← map_pow, htT, map_one]
  have hζ₀root : ι ζ₀ ^ (Nat.card 𝓀[T₀] - 1) = 1 := by
    rw [← map_pow, hζ₀.pow_eq_one, map_one]
  have hcK : ((Nat.card 𝓀[T₀] - 1 : ℕ) : 𝓀[K]) ≠ 0 := by
    rw [hcard]
    exact natCast_card_pow_sub_one_ne_zero hf₀
  classical
  obtain ⟨k, hk, ζ, hζ, hmem⟩ := exists_isPrimitiveRoot_forall_mem_adjoin (K := K) {ξ, ι ζ₀} (by
    intro x hx
    rw [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact mem_unramifiedRoots_iff.2 ⟨_, by rw [Nat.cast_mul]; exact mul_ne_zero heK hcK, hξroot⟩
    · exact mem_unramifiedRoots_iff.2 ⟨_, hcK, hζ₀root⟩)
  refine ⟨k, hk, ζ, hζ, e, he, γ, hγ, ?_⟩

  have hζA : K⟮ζ⟯ ≤ adjoin K {ζ, γ} := adjoin_simple_le_iff.2 (subset_adjoin K _ (by simp))
  have hγA : γ ∈ adjoin K {ζ, γ} := subset_adjoin K _ (by simp)
  have hT₀A : ∀ x : T₀, ι x ∈ adjoin K {ζ, γ} := fun x ↦
    hζA (adjoin_simple_le_iff.2 (hmem (ι ζ₀) (by simp))
      (apply_mem_adjoin_of_adjoin_eq_top ι hζ₀gen x))
  have hξA : ξ ∈ adjoin K {ζ, γ} := hζA (hmem ξ (by simp))
  have hα'A : α' ∈ adjoin K {ζ, γ} := by
    have : α' = γ * (ξ * w') := by
      rw [hγ_def, div_mul_cancel₀ _ (mul_ne_zero hξ0 hw'0)]
    rw [this]
    exact mul_mem hγA (mul_mem hξA (hw'_def ▸ hT₀A _))
  have htop : (⊤ : IntermediateField K E) = adjoin K ((T₀ : Set E) ∪ {((α : 𝒪[E]) : E)}) := by
    rw [← restrictScalars_adjoin, hαgen, restrictScalars_top]
  intro x hx
  have hx' : (⟨x, hx⟩ : E) ∈ adjoin K ((T₀ : Set E) ∪ {((α : 𝒪[E]) : E)}) := by
    rw [← htop]
    trivial
  have hxm : E.val ⟨x, hx⟩ ∈ (adjoin K ((T₀ : Set E) ∪ {((α : 𝒪[E]) : E)})).map E.val :=
    (IntermediateField.mem_map _).2 ⟨_, hx', rfl⟩
  rw [adjoin_map] at hxm
  refine (adjoin_le_iff.2 ?_) hxm
  rintro _ ⟨y, hy, rfl⟩
  rcases hy with hy | hy
  · exact hT₀A ⟨y, hy⟩
  · rw [Set.mem_singleton_iff] at hy
    subst hy
    rw [hα'_def] at hα'A
    exact hα'A

end Structure

section Union

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω]

/- English proof (translation)
Take `⟨hfin, he⟩` from `finiteDimensional_adjoin_pair_and_ramificationIndex hk hζ hπ hm hγ`. Rewrite using `[isTameSubextension_iff, he]`. Conclude with `hm`.
-/
theorem isTameSubextension_adjoin_pair {k : ℕ} (hk : k ≠ 0) {ζ : Ω}
    (hζ : IsPrimitiveRoot ζ (Nat.card 𝓀[K] ^ k - 1)) {π : 𝒪[K]} (hπ : Irreducible π) {m : ℕ}
    (hm : Nat.Coprime m (ringChar 𝓀[K])) {γ : Ω} (hγ : γ ^ m = algebraMap K Ω π) :
    IsTameSubextension (adjoin K {ζ, γ}) := by
  obtain ⟨hfin, he⟩ := finiteDimensional_adjoin_pair_and_ramificationIndex hk hζ hπ hm hγ
  rw [isTameSubextension_iff, he]
  exact hm

variable [IsSepClosed Ω]

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Use `iSup_le fun E ↦ ?_` and prove the remaining obligations. Take `⟨k, hk, ζ, hζ, m, hm, γ, hγ, hE⟩` from `E.2.exists_le_adjoin_pair hπ`. Use `hE.trans ((adjoin_le_iff).2 ?_)` and prove the remaining obligations. Introduce `x hx`.

Simplify using `only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx`. Break down `hx with rfl | rfl` into its components or cases. Conclude with `le_sup_left (a := maximalUnramifiedExtension K Ω) (unramifiedRoots_subset_maximalUnramifiedExtension ⟨k, hk, hζ.pow_eq_one⟩)`. Conclude with `le_sup_right (a := maximalUnramifiedExtension K Ω) (subset_adjoin K _ ⟨m, hm, hγ⟩)`. Use `sup_le (maximalUnramifiedExtension_le_tameExtension K Ω) ((adjoin_le_iff).2 ?_)` and prove the remaining obligations.

Introduce and unpack `γ ⟨m, hm, hγ⟩`. Take `⟨ζ, hζ⟩` from `exists_isPrimitiveRoot_card_pow_sub_one (K := K) (Ksep := Ω) one_ne_zero`. Conclude with `(isTameSubextension_adjoin_pair one_ne_zero hζ hπ hm hγ).le_tameExtension (subset_adjoin K _ (by simp))`.
-/
theorem tameExtension_eq_sup {π : 𝒪[K]} (hπ : Irreducible π) :
    tameExtension K Ω = maximalUnramifiedExtension K Ω ⊔
      adjoin K {γ : Ω | ∃ m : ℕ, Nat.Coprime m (ringChar 𝓀[K]) ∧ γ ^ m = algebraMap K Ω π} := by
  apply le_antisymm
  · refine iSup_le fun E ↦ ?_
    obtain ⟨k, hk, ζ, hζ, m, hm, γ, hγ, hE⟩ := E.2.exists_le_adjoin_pair hπ
    refine hE.trans ((adjoin_le_iff).2 ?_)
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact le_sup_left (a := maximalUnramifiedExtension K Ω)
        (unramifiedRoots_subset_maximalUnramifiedExtension ⟨k, hk, hζ.pow_eq_one⟩)
    · exact le_sup_right (a := maximalUnramifiedExtension K Ω) (subset_adjoin K _ ⟨m, hm, hγ⟩)
  · refine sup_le (maximalUnramifiedExtension_le_tameExtension K Ω) ((adjoin_le_iff).2 ?_)
    rintro γ ⟨m, hm, hγ⟩
    obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_card_pow_sub_one (K := K) (Ksep := Ω) one_ne_zero
    exact (isTameSubextension_adjoin_pair one_ne_zero hζ hπ hm hγ).le_tameExtension
      (subset_adjoin K _ (by simp))

/- English proof (translation)
Rewrite using `[tameExtension_eq_sup hπ, maximalUnramifiedExtension_eq_adjoin, adjoin_union]`.
-/
theorem tameExtension_eq_adjoin {π : 𝒪[K]} (hπ : Irreducible π) :
    tameExtension K Ω = adjoin K (unramifiedRoots K Ω ∪
      {γ : Ω | ∃ m : ℕ, Nat.Coprime m (ringChar 𝓀[K]) ∧ γ ^ m = algebraMap K Ω π}) := by
  rw [tameExtension_eq_sup hπ, maximalUnramifiedExtension_eq_adjoin, adjoin_union]

end Union

section Galois

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω] [IsSepClosed Ω]

omit [Algebra.IsAlgebraic K Ω] in

/- English proof (translation)
Take `⟨π, hπ⟩` from `IsDiscreteValuationRing.exists_irreducible 𝒪[K]`. Rewrite using `[normal_iff_forall_map_le']`. Introduce `σ`. Rewrite using `[tameExtension_eq_adjoin hπ, adjoin_map]`. Use `adjoin_le_iff.2 fun y hy ↦ subset_adjoin K _ ?_` and prove the remaining obligations.

Take `⟨x, hx, rfl⟩` from `hy`. Break down `hx with ⟨n, hn, hx⟩ | ⟨m, hm, hx⟩` into its components or cases. Conclude with `Or.inl ⟨n, hn, by rw [AlgEquiv.coe_toAlgHom, ← map_pow, hx, map_one]⟩`. Conclude with `Or.inr ⟨m, hm, by rw [AlgEquiv.coe_toAlgHom, ← map_pow, hx, AlgEquiv.commutes]⟩`.
-/
theorem normal_tameExtension [Normal K Ω] : Normal K (tameExtension K Ω) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  rw [normal_iff_forall_map_le']
  intro σ
  rw [tameExtension_eq_adjoin hπ, adjoin_map]
  refine adjoin_le_iff.2 fun y hy ↦ subset_adjoin K _ ?_
  obtain ⟨x, hx, rfl⟩ := hy
  rcases hx with ⟨n, hn, hx⟩ | ⟨m, hm, hx⟩
  · exact Or.inl ⟨n, hn, by rw [AlgEquiv.coe_toAlgHom, ← map_pow, hx, map_one]⟩
  · exact Or.inr ⟨m, hm, by rw [AlgEquiv.coe_toAlgHom, ← map_pow, hx, AlgEquiv.commutes]⟩

omit [Algebra.IsAlgebraic K Ω] in

/- English proof (translation)
The claim follows from `have := Algebra.isSeparable_tower_bot_of_isSeparable K (tameExtension K Ω) Ω have := normal_tameExtension (K := K) (Ω := Ω) isGalois_iff.2 ⟨inferInstance, inferInstance⟩`.
-/
theorem isGalois_tameExtension_of_valued [IsGalois K Ω] : IsGalois K (tameExtension K Ω) :=
  have := Algebra.isSeparable_tower_bot_of_isSeparable K (tameExtension K Ω) Ω
  have := normal_tameExtension (K := K) (Ω := Ω)
  isGalois_iff.2 ⟨inferInstance, inferInstance⟩

end Galois

section SeparableClosure

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

instance isGalois_tameExtension : IsGalois K (tameExtension K Ω) := by
  let := algebraicValuativeRel K Ω
  let := algebraicTopology K Ω
  have := algebraicValuativeRel_valuativeExtension K Ω
  have := algebraicTopology_isValuativeTopology K Ω
  have : IsSepClosed Ω := IsSepClosure.sep_closed K
  exact isGalois_tameExtension_of_valued

end SeparableClosure

end GroundTheory.LocalField
