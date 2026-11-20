import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.GLVolumeIndex

noncomputable section

namespace GlobalTheory.IndexVolume

open MeasureTheory Matrix Finset ValuativeRel
open Formalism.MainNotions.ZetaProductPairs (qE zetaProd idxPar Lpair)
open GlobalTheory.IndefiniteRowSideFullHecke.GLVolumeIndex
open scoped Classical

/- English proof (translation)
Use `Fintype.ofFinite k` as an intermediate fact. Establish `e : GL n k ≃ GL (Fin (Fintype.card n)) k` using `(Units.mapEquiv (Matrix.reindexAlgEquiv k k (Fintype.equivFin n)).toMulEquiv).toEquiv`. Rewrite using `[Nat.card_congr e, Matrix.card_GL_field, ← Nat.card_eq_fintype_card (α := k)]`. Generalize the expression as in `Fintype.card n = N`. Establish `hq : 0 < Nat.card k` using `Nat.card_pos`.

Generalize the expression as in `Nat.card k = q at hq`. Establish `hq' : (0 : ℝ) < q` using `by exact_mod_cast hq`. Rewrite using `[Nat.cast_prod]`. Establish `h1 : ∀ i : Fin N, ((q ^ N - q ^ (i : ℕ) : ℕ) : ℝ) = (q : ℝ) ^ N * (1 - (q : ℝ) ^ (-((N - 1 - i + 1 : ℕ) : ℤ)))`. Introduce `i`.

Rewrite using `[Nat.cast_sub (Nat.pow_le_pow_right hq i.2.le), _root_.zpow_neg, _root_.zpow_natCast]`. Establish `: N = i + (N - 1 - i + 1)` using `by have := i.2; omega`. Generalize the expression as in `N - 1 - i + 1 = l at this ⊢`. Establish `h2 : (q : ℝ) ^ N = q ^ (i : ℕ) * q ^ l` using `by rw [← pow_add, ← this]`. Use `push_cast`.

Rewrite using `[h2]`. Clear the denominators using the available nonvanishing facts. Simplify using `only [h1]`. Rewrite using `[Fin.prod_univ_eq_prod_range (fun i => (q : ℝ) ^ N * (1 - (q : ℝ) ^ (-((N - 1 - i + 1 : ℕ) : ℤ)))) N, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, ← pow_mul, Finset.prod_range_reflect (fun i => 1 - (q : ℝ) ^ (-((i + 1 : ℕ) : ℤ))) N, qE, ← Finset.Ico_add_one_righ …`. Simplify using `[add_comm]`.
-/
theorem card_GL_real (k : Type) [Field k] [Finite k] (n : Type) [Fintype n] [DecidableEq n] :
    (Nat.card (GL n k) : ℝ) =
      (Nat.card k : ℝ) ^ (Fintype.card n * Fintype.card n) * qE (Nat.card k) 1 (Fintype.card n) := by
  have := Fintype.ofFinite k
  have e : GL n k ≃ GL (Fin (Fintype.card n)) k :=
    (Units.mapEquiv (Matrix.reindexAlgEquiv k k (Fintype.equivFin n)).toMulEquiv).toEquiv
  rw [Nat.card_congr e, Matrix.card_GL_field, ← Nat.card_eq_fintype_card (α := k)]
  generalize Fintype.card n = N
  have hq : 0 < Nat.card k := Nat.card_pos
  generalize Nat.card k = q at hq
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  rw [Nat.cast_prod]
  have h1 : ∀ i : Fin N, ((q ^ N - q ^ (i : ℕ) : ℕ) : ℝ) =
      (q : ℝ) ^ N * (1 - (q : ℝ) ^ (-((N - 1 - i + 1 : ℕ) : ℤ))) := by
    intro i
    rw [Nat.cast_sub (Nat.pow_le_pow_right hq i.2.le), _root_.zpow_neg, _root_.zpow_natCast]
    have : N = i + (N - 1 - i + 1) := by have := i.2; omega
    generalize N - 1 - i + 1 = l at this ⊢
    have h2 : (q : ℝ) ^ N = q ^ (i : ℕ) * q ^ l := by rw [← pow_add, ← this]
    push_cast
    rw [h2]
    field_simp
  simp only [h1]
  rw [Fin.prod_univ_eq_prod_range
    (fun i => (q : ℝ) ^ N * (1 - (q : ℝ) ^ (-((N - 1 - i + 1 : ℕ) : ℤ)))) N,
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, ← pow_mul,
    Finset.prod_range_reflect (fun i => 1 - (q : ℝ) ^ (-((i + 1 : ℕ) : ℤ))) N, qE,
    ← Finset.Ico_add_one_right_eq_Icc, Finset.prod_Ico_eq_prod_range]
  simp [add_comm]

section Levels

variable {O : Type} [CommRing O] [IsLocalRing O]

def bar {n : Type} [Fintype n] [DecidableEq n] (H : Subgroup (GL n O)) :
    Set (Matrix n n (IsLocalRing.ResidueField O)) := {B | ∃ h ∈ H, red h.val = B}

/- English proof (translation)
Use `choose A hA using fun i j => IsLocalRing.residue_surjective (B i j)`. Conclude with `⟨Matrix.of A, by ext i j; exact hA i j⟩`.
-/
theorem exists_red {m n : Type} (B : Matrix m n (IsLocalRing.ResidueField O)) :
    ∃ A : Matrix m n O, red A = B := by
  choose A hA using fun i j => IsLocalRing.residue_surjective (B i j)
  exact ⟨Matrix.of A, by ext i j; exact hA i j⟩

/- English proof (translation)
Introduce `B`. Take `⟨A, hA⟩` from `exists_red B.val`. Take `⟨u, hu⟩` from `isUnit_of_red A (hA ▸ B.isUnit)`. Use `⟨u, Units.ext ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `red u.val = B.val`.

Rewrite using `[hu, hA]`.
-/
theorem map_surjective (n : Type) [Fintype n] [DecidableEq n] :
    Function.Surjective (Matrix.GeneralLinearGroup.map (n := n) (IsLocalRing.residue O)) := by
  intro B
  obtain ⟨A, hA⟩ := exists_red B.val
  obtain ⟨u, hu⟩ := isUnit_of_red A (hA ▸ B.isUnit)
  refine ⟨u, Units.ext ?_⟩
  change red u.val = B.val
  rw [hu, hA]

/- English proof (translation)
Establish `e : bar H = Units.val '' ((H.map (Matrix.GeneralLinearGroup.map (n` using `n) (IsLocalRing.residue O)) : Subgroup (GL n (IsLocalRing.ResidueField O))) : Set (GL n (IsLocalRing.ResidueField O))) := by`. Use extensionality with `B`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h, hh, rfl⟩`. Conclude with `⟨_, ⟨h, hh, rfl⟩, rfl⟩`.

Introduce and unpack `⟨_, ⟨h, hh, rfl⟩, rfl⟩`. Conclude with `⟨h, hh, rfl⟩`. Rewrite using `[e, Nat.card_image_of_injective Units.val_injective, ← Subgroup.index_map_eq H (map_surjective n) hH]`. Conclude with `Subgroup.index_mul_card _`.
-/
theorem index_mul_card_bar {n : Type} [Fintype n] [DecidableEq n] {H : Subgroup (GL n O)}
    (hH : princ O n ≤ H) :
    H.index * Nat.card (bar H) = Nat.card (GL n (IsLocalRing.ResidueField O)) := by
  have e : bar H = Units.val ''
      ((H.map (Matrix.GeneralLinearGroup.map (n := n) (IsLocalRing.residue O)) :
        Subgroup (GL n (IsLocalRing.ResidueField O))) : Set (GL n (IsLocalRing.ResidueField O))) := by
    ext B
    constructor
    · rintro ⟨h, hh, rfl⟩
      exact ⟨_, ⟨h, hh, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨h, hh, rfl⟩, rfl⟩
      exact ⟨h, hh, rfl⟩
  rw [e, Nat.card_image_of_injective Units.val_injective,
    ← Subgroup.index_map_eq H (map_surjective n) hH]
  exact Subgroup.index_mul_card _

end Levels

section Local

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

/- English proof (translation)
Use `letI := IsTopologicalAddGroup.rightUniformSpace k`. Use `haveI := isUniformAddGroup_of_addCommGroup (G := k)`. Use `letI : (Valued.v (R := k)).RankOne :=`. Use the proof step `{ hom' := IsRankLeOne.nonempty.some.emb (R := k).comp MonoidWithZeroHom.ValueGroup₀.embedding strictMono' := IsRankLeOne.nonempty.some.strictMono.comp MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }`. Use `open scoped Valued in`.

Use `haveI : ProperSpace k := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace k`. Conclude with `secondCountable_of_proper`.
-/
theorem secondCountable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] : SecondCountableTopology k := by
  letI := IsTopologicalAddGroup.rightUniformSpace k
  haveI := isUniformAddGroup_of_addCommGroup (G := k)
  letI : (Valued.v (R := k)).RankOne :=
  { hom' := IsRankLeOne.nonempty.some.emb (R := k).comp MonoidWithZeroHom.ValueGroup₀.embedding
    strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  open scoped Valued in
  haveI : ProperSpace k := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace k
  exact secondCountable_of_proper

/- English proof (translation)
Establish `: 1 < Nat.card 𝓀[F]` using `Finite.one_lt_card`. Unfold `resCard`. Conclude with `this` after adjusting the coercions.
-/
theorem one_lt_resCard : 1 < resCard F := by
  have : 1 < Nat.card 𝓀[F] := Finite.one_lt_card
  unfold resCard
  exact_mod_cast this

def cell (c : 𝓀[F]) : Set F := {x | ∃ y : 𝒪[F], (y : F) = x ∧ IsLocalRing.residue 𝒪[F] y = c}

def pre {m n : Type} (S : Set (Matrix m n 𝓀[F])) : Set (m → n → F) :=
  {x | ∃ A : Matrix m n 𝒪[F], entries A = x ∧ red A ∈ S}

/- English proof (translation)
Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨z, rfl, hz⟩`. Conclude with `⟨z - y, by simp [sub_eq_add_neg], by rw [map_sub, hz, sub_self]⟩`. Introduce and unpack `⟨z, hz, h0⟩`.

Use `⟨z + y, ?_, by rw [map_add, h0, zero_add]⟩` and prove the remaining obligations. Use `push_cast`. Rewrite using `[hz]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem cell_eq (y : 𝒪[F]) :
    cell (IsLocalRing.residue 𝒪[F] y) = (fun x => x + (-(y : F))) ⁻¹' cell (0 : 𝓀[F]) := by
  ext x
  constructor
  · rintro ⟨z, rfl, hz⟩
    exact ⟨z - y, by simp [sub_eq_add_neg], by rw [map_sub, hz, sub_self]⟩
  · rintro ⟨z, hz, h0⟩
    refine ⟨z + y, ?_, by rw [map_add, h0, zero_add]⟩
    push_cast
    rw [hz]; ring

/- English proof (translation)
Take `⟨y, rfl⟩` from `IsLocalRing.residue_surjective c`. Rewrite using `[cell_eq]`. Use `IsClosed.preimage (by fun_prop) ?_` and prove the remaining obligations. Establish `: cell (0 : 𝓀[F]) = Subtype.val '' (𝓂[F] : Set 𝒪[F])`. Use extensionality with `x`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨z, rfl, hz⟩`. Conclude with `⟨z, (IsLocalRing.residue_eq_zero_iff _).1 hz, rfl⟩`. Introduce and unpack `⟨z, hz, rfl⟩`. Conclude with `⟨z, rfl, (IsLocalRing.residue_eq_zero_iff _).2 hz⟩`.

Rewrite using `[this]`. Establish `: T2Space F`. Use `letI := IsTopologicalAddGroup.rightUniformSpace F`. Use `haveI := isUniformAddGroup_of_addCommGroup (G := F)`. Use `infer_instance`.

Conclude with `((IsNoetherianRing.isClosed_ideal 𝓂[F]).isCompact.image continuous_subtype_val).isClosed`.
-/
theorem isClosed_cell (c : 𝓀[F]) : IsClosed (cell c) := by
  obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective c
  rw [cell_eq]
  refine IsClosed.preimage (by fun_prop) ?_
  have : cell (0 : 𝓀[F]) = Subtype.val '' (𝓂[F] : Set 𝒪[F]) := by
    ext x
    constructor
    · rintro ⟨z, rfl, hz⟩
      exact ⟨z, (IsLocalRing.residue_eq_zero_iff _).1 hz, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z, rfl, (IsLocalRing.residue_eq_zero_iff _).2 hz⟩
  rw [this]
  have : T2Space F := by
    letI := IsTopologicalAddGroup.rightUniformSpace F
    haveI := isUniformAddGroup_of_addCommGroup (G := F)
    infer_instance
  exact ((IsNoetherianRing.isClosed_ideal 𝓂[F]).isCompact.image continuous_subtype_val).isClosed

/- English proof (translation)
Introduce `A B h` and use `by ext i j exact congrFun (congrFun h i) j`.
-/
theorem entries_injective {m n : Type} :
    Function.Injective (entries : Matrix m n 𝒪[F] → m → n → F) := fun A B h => by
  ext i j
  exact congrFun (congrFun h i) j

/- English proof (translation)
Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨A, rfl, rfl⟩ i _ j _`. Conclude with `⟨A i j, rfl, rfl⟩`. Introduce `h choose A hA hB using fun i j => h i trivial j trivial`.

Conclude with `⟨Matrix.of A, funext fun i => funext fun j => hA i j, by ext i j; exact hB i j⟩`.
-/
theorem pre_singleton {m n : Type} (B : Matrix m n 𝓀[F]) :
    pre {B} = Set.univ.pi fun i => Set.univ.pi fun j => cell (B i j) := by
  ext x
  constructor
  · rintro ⟨A, rfl, rfl⟩ i _ j _
    exact ⟨A i j, rfl, rfl⟩
  · intro h
    choose A hA hB using fun i j => h i trivial j trivial
    exact ⟨Matrix.of A, funext fun i => funext fun j => hA i j, by ext i j; exact hB i j⟩

/- English proof (translation)
Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨k, hk, rfl⟩`. Conclude with `⟨k.val, rfl, k, hk, rfl⟩`. Introduce and unpack `⟨A, rfl, k, hk, h⟩`.

Take `⟨k', hk', e⟩` from `exists_mem_of_red hH hk h.symm`. Conclude with `⟨k', hk', by rw [e]⟩`.
-/
theorem groupSet_eq {n : Type} [Fintype n] [DecidableEq n] {H : Subgroup (GL n 𝒪[F])}
    (hH : princ 𝒪[F] n ≤ H) : groupSet H = pre (bar H) := by
  ext x
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k.val, rfl, k, hk, rfl⟩
  · rintro ⟨A, rfl, k, hk, h⟩
    obtain ⟨k', hk', e⟩ := exists_mem_of_red hH hk h.symm
    exact ⟨k', hk', by rw [e]⟩

variable [MeasurableSpace F] [BorelSpace F] (ν : Measure F) [ν.IsAddHaarMeasure]

/- English proof (translation)
Establish `hv : ∀ c : 𝓀[F], ν (cell c) = ν (cell (0 : 𝓀[F]))` using `fun c => by`. Take `⟨y, rfl⟩` from `IsLocalRing.residue_surjective c`. Rewrite using `[cell_eq, measure_preimage_add_right]`. Establish `hU : (𝒪[F] : Set F) = ⋃ c : 𝓀[F], cell c`. Use extensionality with `x`.

Simplify using `only [Set.mem_iUnion]`. Conclude with `⟨fun h => ⟨_, ⟨x, h⟩, rfl, rfl⟩, fun ⟨_, y, hy, _⟩ => hy ▸ y.2⟩`. Use `Fintype.ofFinite 𝓀[F]` as an intermediate fact. Rewrite `hν` using `[hU, measure_iUnion (fun u u' h => Set.disjoint_left.2 ?_) (fun u => (isClosed_cell u).measurableSet)]`. Simplify using `only [hv, tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card] at hν`.

Rewrite using `[hv]`. Conclude with `ENNReal.eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact hν)`. Introduce and unpack `_ ⟨y, rfl, rfl⟩ ⟨z, hz, rfl⟩`. Conclude with `h (by rw [Subtype.ext hz])`.
-/
theorem measure_cell (hν : ν (𝒪[F] : Set F) = 1) (c : 𝓀[F]) :
    ν (cell c) = (Nat.card 𝓀[F] : ENNReal)⁻¹ := by
  have hv : ∀ c : 𝓀[F], ν (cell c) = ν (cell (0 : 𝓀[F])) := fun c => by
    obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective c
    rw [cell_eq, measure_preimage_add_right]
  have hU : (𝒪[F] : Set F) = ⋃ c : 𝓀[F], cell c := by
    ext x
    simp only [Set.mem_iUnion]
    exact ⟨fun h => ⟨_, ⟨x, h⟩, rfl, rfl⟩, fun ⟨_, y, hy, _⟩ => hy ▸ y.2⟩
  have := Fintype.ofFinite 𝓀[F]
  rw [hU, measure_iUnion (fun u u' h => Set.disjoint_left.2 ?_)
    (fun u => (isClosed_cell u).measurableSet)] at hν
  · simp only [hv, tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      ← Nat.card_eq_fintype_card] at hν
    rw [hv]
    exact ENNReal.eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact hν)
  · rintro _ ⟨y, rfl, rfl⟩ ⟨z, hz, rfl⟩
    exact h (by rw [Subtype.ext hz])

omit [ν.IsAddHaarMeasure] in
/- English proof (translation)
Rewrite using `[pre_singleton]`. Conclude with `MeasurableSet.univ_pi fun i => MeasurableSet.univ_pi fun j => (isClosed_cell _).measurableSet`.
-/
theorem measurableSet_pre_singleton {m n : Type} [Fintype m] [Fintype n] (B : Matrix m n 𝓀[F]) :
    MeasurableSet (pre {B}) := by
  rw [pre_singleton]
  exact MeasurableSet.univ_pi fun i => MeasurableSet.univ_pi fun j => (isClosed_cell _).measurableSet

/- English proof (translation)
Use extensionality with `x`. Simplify using `only [Set.mem_iUnion]`. Conclude with `⟨fun ⟨A, h1, h2⟩ => ⟨⟨_, h2⟩, A, h1, rfl⟩, fun ⟨B, A, h1, h2⟩ => ⟨A, h1, by`. Rewrite using `[Set.mem_singleton_iff.1 h2]`. Conclude with `B.2⟩⟩`.
-/
theorem pre_eq_iUnion {m n : Type} (S : Set (Matrix m n 𝓀[F])) :
    pre S = ⋃ B : S, pre {B.val} := by
  ext x
  simp only [Set.mem_iUnion]
  exact ⟨fun ⟨A, h1, h2⟩ => ⟨⟨_, h2⟩, A, h1, rfl⟩, fun ⟨B, A, h1, h2⟩ => ⟨A, h1, by
    rw [Set.mem_singleton_iff.1 h2]; exact B.2⟩⟩

/- English proof (translation)
Establish `: Finite (Matrix m n 𝓀[F])` using `inferInstanceAs (Finite (m → n → 𝓀[F]))`. Rewrite using `[pre_eq_iUnion]`. Conclude with `MeasurableSet.iUnion fun B => measurableSet_pre_singleton _`.
-/
theorem measurableSet_pre {m n : Type} [Fintype m] [Fintype n] (S : Set (Matrix m n 𝓀[F])) :
    MeasurableSet (pre S) := by
  have : Finite (Matrix m n 𝓀[F]) := inferInstanceAs (Finite (m → n → 𝓀[F]))
  rw [pre_eq_iUnion]
  exact MeasurableSet.iUnion fun B => measurableSet_pre_singleton _

/- English proof (translation)
Establish `: Finite (Matrix m n 𝓀[F])` using `inferInstanceAs (Finite (m → n → 𝓀[F]))`. Use `secondCountable F` as an intermediate fact. Use `Fintype.ofFinite S` as an intermediate fact. Establish `h1 : ∀ B : Matrix m n 𝓀[F], volAdd ν m n (pre {B}) = (Nat.card 𝓀[F] : ENNReal)⁻¹ ^ (Fintype.card m * Fintype.card n)` using `fun B => by`. Rewrite using `[pre_singleton, volAdd, Measure.pi_pi]`.

Simplify using `only [Measure.pi_pi, measure_cell ν hν, Finset.prod_const, Finset.card_univ]`. Rewrite using `[← pow_mul, mul_comm]`. Rewrite using `[pre_eq_iUnion, measure_iUnion (fun u u' h => Set.disjoint_left.2 ?_) (fun u => measurableSet_pre_singleton _)]`. Simplify using `only [h1, tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card]`. Introduce and unpack `_ ⟨A, rfl, hA⟩ ⟨B, hB, hB'⟩`.

Rewrite `hB'` using `[entries_injective hB]`. Conclude with `h (Subtype.ext ((Set.mem_singleton_iff.1 hA).symm.trans hB'))`.
-/
theorem measure_pre (hν : ν (𝒪[F] : Set F) = 1) {m n : Type} [Fintype m] [Fintype n]
    (S : Set (Matrix m n 𝓀[F])) :
    volAdd ν m n (pre S) =
      Nat.card S * (Nat.card 𝓀[F] : ENNReal)⁻¹ ^ (Fintype.card m * Fintype.card n) := by
  have : Finite (Matrix m n 𝓀[F]) := inferInstanceAs (Finite (m → n → 𝓀[F]))
  have := secondCountable F
  have := Fintype.ofFinite S
  have h1 : ∀ B : Matrix m n 𝓀[F], volAdd ν m n (pre {B}) =
      (Nat.card 𝓀[F] : ENNReal)⁻¹ ^ (Fintype.card m * Fintype.card n) := fun B => by
    rw [pre_singleton, volAdd, Measure.pi_pi]
    simp only [Measure.pi_pi, measure_cell ν hν, Finset.prod_const, Finset.card_univ]
    rw [← pow_mul, mul_comm]
  rw [pre_eq_iUnion, measure_iUnion (fun u u' h => Set.disjoint_left.2 ?_)
    (fun u => measurableSet_pre_singleton _)]
  · simp only [h1, tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      ← Nat.card_eq_fintype_card]
  · rintro _ ⟨A, rfl, hA⟩ ⟨B, hB, hB'⟩
    rw [entries_injective hB] at hB'
    exact h (Subtype.ext ((Set.mem_singleton_iff.1 hA).symm.trans hB'))

/- English proof (translation)
Rewrite using `[Measure.real, measure_pre ν hν]`. Simplify using `[resCard, div_eq_mul_inv]`.
-/
theorem measureReal_pre (hν : ν (𝒪[F] : Set F) = 1) {m n : Type} [Fintype m] [Fintype n]
    (S : Set (Matrix m n 𝓀[F])) :
    (volAdd ν m n).real (pre S) = Nat.card S / resCard F ^ (Fintype.card m * Fintype.card n) := by
  rw [Measure.real, measure_pre ν hν]
  simp [resCard, div_eq_mul_inv]

/- English proof (translation)
Rewrite using `[volGroup, groupSet_eq hH, measureReal_pre ν hν]`.
-/
theorem volGroup_eq (hν : ν (𝒪[F] : Set F) = 1) {n : Type} [Fintype n] [DecidableEq n]
    {H : Subgroup (GL n 𝒪[F])} (hH : princ 𝒪[F] n ≤ H) :
    volGroup ν H = Nat.card (bar H) / resCard F ^ (Fintype.card n * Fintype.card n) := by
  rw [volGroup, groupSet_eq hH, measureReal_pre ν hν]

/- English proof (translation)
Establish `h` using `congrArg (Nat.cast : ℕ → ℝ) (index_mul_card_bar hH)`. Rewrite `h` using `[card_GL_real, Nat.cast_mul]`. Establish `hq : 0 < resCard F` using `lt_trans one_pos one_lt_resCard`. Rewrite using `[volGroup_eq ν hν hH, ← mul_div_assoc, h]`. Express the relevant statement in the definitionally equal form `resCard F ^ _ * qE (resCard F) _ _ / _ = _`.

Clear the denominators using the available nonvanishing facts.
-/
theorem index_mul_volGroup (hν : ν (𝒪[F] : Set F) = 1) {n : Type} [Fintype n] [DecidableEq n]
    {H : Subgroup (GL n 𝒪[F])} (hH : princ 𝒪[F] n ≤ H) :
    (H.index : ℝ) * volGroup ν H = qE (resCard F) 1 (Fintype.card n) := by
  have h := congrArg (Nat.cast : ℕ → ℝ) (index_mul_card_bar hH)
  rw [card_GL_real, Nat.cast_mul] at h
  have hq : 0 < resCard F := lt_trans one_pos one_lt_resCard
  rw [volGroup_eq ν hν hH, ← mul_div_assoc, h]
  change resCard F ^ _ * qE (resCard F) _ _ / _ = _
  field_simp

/- English proof (translation)
Introduce `n _ _`. Use `index_mul_volGroup ν hν (le_top : princ 𝒪[F] n ≤ ⊤)` as an intermediate fact. Simplify using `using this`.
-/
theorem volumeOfGL (hν : ν (𝒪[F] : Set F) = 1) : VolumeOfGL ν := by
  intro n _ _
  have := index_mul_volGroup ν hν (le_top : princ 𝒪[F] n ≤ ⊤)
  simpa using this

end Local

end GlobalTheory.IndexVolume
