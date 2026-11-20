import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardEqPowAndIndexGe
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDoubleCosetTermBasicFacts
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermExponentsNonnegAndDefectGroupBoundStatement

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.LevelFamilies

/- English proof (translation)
Establish `h` using `AddSubgroup.relIndex_ker A.toAddSubgroup M.mkQ.toAddMonoidHom`. Establish `hk : M.mkQ.toAddMonoidHom.ker = M.toAddSubgroup`. Use extensionality with `x`. Simplify using `[AddMonoidHom.mem_ker]`. Rewrite `h` using `[hk]`.

Rewrite using `[h]`. Both sides reduce to the same expression.
-/
theorem relIndex_eq_card_map {O V : Type} [Ring O] [AddCommGroup V] [Module O V]
    (M A : Submodule O V) :
    M.toAddSubgroup.relIndex A.toAddSubgroup = Nat.card (A.map M.mkQ) := by
  have h := AddSubgroup.relIndex_ker A.toAddSubgroup M.mkQ.toAddMonoidHom
  have hk : M.mkQ.toAddMonoidHom.ker = M.toAddSubgroup := by
    ext x
    simp [AddMonoidHom.mem_ker]
  rw [hk] at h
  rw [h]
  rfl

/- English proof (translation)
Establish `hinj : Function.Injective (fun c : V ⧸ M => (M.mkQ ⁻¹' {c} : Set V))`. Introduce `c c' h`. Take `⟨v, rfl⟩` from `M.mkQ_surjective c`. Establish `: v ∈ (M.mkQ ⁻¹' {c'} : Set V)`. Establish `h' : (M.mkQ ⁻¹' {M.mkQ v} : Set V) = M.mkQ ⁻¹' {c'}` using `h`.

Rewrite using `[← h']`. Simplify using the standard rewrite rules. Simplify using `using this`. Establish `hpre : ∀ y : V, (M.mkQ ⁻¹' {M.mkQ y} : Set V) = {x | x - y ∈ M}`. Introduce `y`.

Use extensionality with `x`. Simplify using `[Submodule.Quotient.eq]`. Establish `hmem : ∀ y : V, M.mkQ y ∈ B.map M.mkQ ↔ y ∈ B`. Introduce `y`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨b, hb, hby⟩`. Establish `h1 : b - y ∈ M` using `by simpa [Submodule.Quotient.eq] using hby`. Establish `h2 : y = b - (b - y)` using `by abel`. Rewrite using `[h2]`. Conclude with `B.sub_mem hb (hMB h1)`.

Introduce `hy`. Conclude with `⟨y, hy, rfl⟩`. Establish `hset : {C : Set V | ∃ y ∈ A, y ∉ B ∧ C = {x | x - y ∈ M}} = (fun c : V ⧸ M => (M.mkQ ⁻¹' {c} : Set V)) '' ((A.map M.mkQ : Set (V ⧸ M)) \ (B.map M.mkQ : Set (V ⧸ M)))`. Use extensionality with `C`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨y, hyA, hyB, rfl⟩`. Conclude with `⟨M.mkQ y, ⟨⟨y, hyA, rfl⟩, fun h => hyB ((hmem y).1 h)⟩, hpre y⟩`. Introduce and unpack `⟨c, ⟨⟨y, hyA, rfl⟩, hc⟩, rfl⟩`. Conclude with `⟨y, hyA, fun h => hc ((hmem y).2 h), hpre y⟩`. Establish `hsub : (B.map M.mkQ : Set (V ⧸ M)) ⊆ (A.map M.mkQ : Set (V ⧸ M))` using `Submodule.map_mono hBA`.

Establish `hfin : (A.map M.mkQ : Set (V ⧸ M)).Finite` using `Set.toFinite _`. Rewrite using `[hset, Set.ncard_image_of_injective _ hinj, Set.ncard_diff hsub (hfin.subset hsub)]`. Both sides reduce to the same expression.
-/
theorem ncard_classes {O V : Type} [Ring O] [AddCommGroup V] [Module O V]
    (M B A : Submodule O V) (hMB : M ≤ B) (hBA : B ≤ A) [Finite (A.map M.mkQ)] :
    Set.ncard {C : Set V | ∃ y ∈ A, y ∉ B ∧ C = {x | x - y ∈ M}} =
      Nat.card (A.map M.mkQ) - Nat.card (B.map M.mkQ) := by
  have hinj : Function.Injective (fun c : V ⧸ M => (M.mkQ ⁻¹' {c} : Set V)) := by
    intro c c' h
    obtain ⟨v, rfl⟩ := M.mkQ_surjective c
    have : v ∈ (M.mkQ ⁻¹' {c'} : Set V) := by
      have h' : (M.mkQ ⁻¹' {M.mkQ v} : Set V) = M.mkQ ⁻¹' {c'} := h
      rw [← h']; simp
    simpa using this
  have hpre : ∀ y : V, (M.mkQ ⁻¹' {M.mkQ y} : Set V) = {x | x - y ∈ M} := by
    intro y
    ext x
    simp [Submodule.Quotient.eq]
  have hmem : ∀ y : V, M.mkQ y ∈ B.map M.mkQ ↔ y ∈ B := by
    intro y
    constructor
    · rintro ⟨b, hb, hby⟩
      have h1 : b - y ∈ M := by simpa [Submodule.Quotient.eq] using hby
      have h2 : y = b - (b - y) := by abel
      rw [h2]
      exact B.sub_mem hb (hMB h1)
    · intro hy
      exact ⟨y, hy, rfl⟩
  have hset : {C : Set V | ∃ y ∈ A, y ∉ B ∧ C = {x | x - y ∈ M}} =
      (fun c : V ⧸ M => (M.mkQ ⁻¹' {c} : Set V)) ''
        ((A.map M.mkQ : Set (V ⧸ M)) \ (B.map M.mkQ : Set (V ⧸ M))) := by
    ext C
    constructor
    · rintro ⟨y, hyA, hyB, rfl⟩
      exact ⟨M.mkQ y, ⟨⟨y, hyA, rfl⟩, fun h => hyB ((hmem y).1 h)⟩, hpre y⟩
    · rintro ⟨c, ⟨⟨y, hyA, rfl⟩, hc⟩, rfl⟩
      exact ⟨y, hyA, fun h => hc ((hmem y).2 h), hpre y⟩
  have hsub : (B.map M.mkQ : Set (V ⧸ M)) ⊆ (A.map M.mkQ : Set (V ⧸ M)) :=
    Submodule.map_mono hBA
  have hfin : (A.map M.mkQ : Set (V ⧸ M)).Finite := Set.toFinite _
  rw [hset, Set.ncard_image_of_injective _ hinj, Set.ncard_diff hsub (hfin.subset hsub)]
  rfl

/- English proof (translation)
Establish `h : Ideal.span {ϖ} = IsLocalRing.maximalIdeal 𝒪[F]` using `hϖ.maximalIdeal_eq.symm`. Establish `h1 : resQ ϖ = Nat.card (IsLocalRing.ResidueField 𝒪[F])`. Unfold `resQ`. Rewrite using `[h]`. Both sides reduce to the same expression.

Rewrite using `[h1]`. Conclude with `Finite.one_lt_card`.
-/
theorem two_le_resQ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (ϖ : 𝒪[F]) (hϖ : Irreducible ϖ) : 2 ≤ resQ ϖ := by
  have h : Ideal.span {ϖ} = IsLocalRing.maximalIdeal 𝒪[F] := hϖ.maximalIdeal_eq.symm
  have h1 : resQ ϖ = Nat.card (IsLocalRing.ResidueField 𝒪[F]) := by
    unfold resQ
    rw [h]
    rfl
  rw [h1]
  exact Finite.one_lt_card

/- English proof (translation)
Introduce `F _ _ _ _ _ E _ _ _ L r k S d Λ hT hB`. Take `⟨-, -, -, -, -, ⟨i, hia, hbe⟩, -, -, -, hlev0, hlev⟩` from `GlobalTheory.T.term_exponents_nonneg_and_defect_group_bound L r k S d Λ hT`. Establish `hMA : S.M d Λ ≤ S.sat Λ` using `(GlobalTheory.HL.TermBasic.term_basic L r k S d Λ hT).2.2.1`. Establish `hq : 2 ≤ S.q` using `two_le_resQ S.ϖ S.ϖ_irr`. Establish `hcard : Nat.card ((S.sat Λ).map (S.M d Λ).mkQ) = S.q ^ i`.

Rewrite using `[← hbe, ← relIndex_eq_card_map]`. Both sides reduce to the same expression. Use `haveI hfin : Finite ((S.sat Λ).map (S.M d Λ).mkQ) := by`. Apply `Nat.finite_of_card_ne_zero` to reduce the goal to its premises. Rewrite using `[hcard]`.

Check the signs of the components of the expression. Set `P : ℕ → Prop` to `fun j => ∃ y ∈ S.sat Λ, S.levC d Λ y = j`. Choose the witnesses or unpack the hypotheses as in `⟨y0, hy0A, hy0M⟩ : ∃ y ∈ S.sat Λ, y ∉ S.M d Λ := by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`.

Conclude with `hB.1 (le_antisymm hMA h)`. Set `J` to `Nat.findGreatest P r`. Establish `hle : ∀ y ∈ S.sat Λ, S.levC d Λ y ≤ J` using `fun y hy => Nat.le_findGreatest (hB.2.1 y hy) ⟨y, hy, rfl⟩`. Establish `hPJ : P J` using `Nat.findGreatest_spec (hB.2.1 y0 hy0A) ⟨y0, hy0A, rfl⟩`. Establish `hJr : J ≤ r` using `Nat.findGreatest_le r`.

Establish `hJ1 : 1 ≤ J`. Establish `h1 : S.levC d Λ y0 ≠ 0` using `fun h => hy0M ((hlev0 y0 hy0A).1 h)`. Use `hle y0 hy0A` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Set `B : Submodule L.O S.V` to `S.sat Λ ⊓ ((S.spanTo S.f (J - 1) ⊔ S.spanTo S.f' (J - 1)).restrictScalars L.O ⊔ S.M d Λ)`.

Establish `hBmem : ∀ y ∈ S.sat Λ, y ∈ B ↔ S.levC d Λ y ≤ J - 1`. Introduce `y hy`. Rewrite using `[hlev y hy]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨-, h⟩`.

Take `⟨u, hu, m, hm, rfl⟩` from `Submodule.mem_sup.1 h`. Conclude with `⟨u, hu, by simpa using hm⟩`. Introduce and unpack `⟨u, hu, hm⟩`. Conclude with `⟨hy, Submodule.mem_sup.2 ⟨u, hu, y - u, hm, by abel⟩⟩`. Establish `hMB : S.M d Λ ≤ B` using `le_inf hMA le_sup_right`.

Establish `hBA : B ≤ S.sat Λ` using `inf_le_left`. Establish `hle' : B.map (S.M d Λ).mkQ ≤ (S.sat Λ).map (S.M d Λ).mkQ` using `Submodule.map_mono hBA`. Use `haveI hfinB : Finite (B.map (S.M d Λ).mkQ) := Finite.of_injective _ (Submodule.inclusion_injective hle')`. Take `⟨i', hi'⟩` from `(GlobalTheory.FiniteModuleOrder.card_eq_pow_and_index_ge L S.ϖ S.ϖ_irr (B.map (S.M d Λ).mkQ)).1`. Establish `hi'q : Nat.card (B.map (S.M d Λ).mkQ) = S.q ^ i'` using `hi'`.

Establish `hn : S.nLev d Λ J = S.q ^ i - S.q ^ i'`. Rewrite using `[← hcard, ← hi'q, ← ncard_classes _ _ _ hMB hBA]`. Unfold `Frames.nLev`. Use `congr 1`. Use extensionality with `C`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, hl, rfl⟩`. Use `⟨y, hy, fun h => ?_, rfl⟩` and prove the remaining obligations. Use `(hBmem y hy).1 h` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Introduce and unpack `⟨y, hy, hl, rfl⟩`. Use `⟨y, hy, ?_, rfl⟩` and prove the remaining obligations. Establish `h1` using `hle y hy`. Establish `h2 : ¬ S.levC d Λ y ≤ J - 1` using `fun h => hl ((hBmem y hy).2 h)`. Use linear arithmetic over natural numbers and integers.

Establish `hlt : S.q ^ i' < S.q ^ i`. Rewrite using `[← hcard, ← hi'q]`. Take `⟨y, hy, hl⟩` from `hPJ`. Establish `hss : (B.map (S.M d Λ).mkQ : Set (S.V ⧸ S.M d Λ)) ⊂ ((S.sat Λ).map (S.M d Λ).mkQ : Set (S.V ⧸ S.M d Λ))`. Use `⟨hle', fun h => ?_⟩` and prove the remaining obligations.

Take `⟨b, hb, hby⟩` from `h (⟨y, hy, rfl⟩ : (S.M d Λ).mkQ y ∈ (S.sat Λ).map (S.M d Λ).mkQ)`. Establish `h1 : b - y ∈ S.M d Λ` using `by simpa [Submodule.Quotient.eq] using hby`. Establish `h2 : y ∈ B`. Establish `h3 : y = b - (b - y)` using `by abel`. Rewrite using `[h3]`.

Conclude with `B.sub_mem hb (hMB h1)`. Use `(hBmem y hy).1 h2` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Conclude with `Set.ncard_lt_ncard hss (Set.toFinite _)`. Establish `hii : i' < i` using `(Nat.pow_lt_pow_iff_right (by omega)).1 hlt`.

Conclude with `⟨i, J, i', by omega, hia, hJ1, hJr, hii, hB, hbe, hle, hPJ, hn⟩`.
-/
theorem exists_family : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → S.TypeBe d Λ → ∃ i J i' : ℕ, 1 ≤ i ∧ (i : ℤ) ≤ S.a ∧ 1 ≤ J ∧ J ≤ r ∧ i' < i ∧ S.InFF (S.q ^ i) J (S.q ^ i - S.q ^ i') d Λ := by
  intro F _ _ _ _ _ E _ _ _ L r k S d Λ hT hB
  obtain ⟨-, -, -, -, -, ⟨i, hia, hbe⟩, -, -, -, hlev0, hlev⟩ := GlobalTheory.T.term_exponents_nonneg_and_defect_group_bound L r k S d Λ hT
  have hMA : S.M d Λ ≤ S.sat Λ := (GlobalTheory.HL.TermBasic.term_basic L r k S d Λ hT).2.2.1
  have hq : 2 ≤ S.q := two_le_resQ S.ϖ S.ϖ_irr
  have hcard : Nat.card ((S.sat Λ).map (S.M d Λ).mkQ) = S.q ^ i := by
    rw [← hbe, ← relIndex_eq_card_map]; rfl
  haveI hfin : Finite ((S.sat Λ).map (S.M d Λ).mkQ) := by
    apply Nat.finite_of_card_ne_zero
    rw [hcard]
    positivity

  let P : ℕ → Prop := fun j => ∃ y ∈ S.sat Λ, S.levC d Λ y = j
  obtain ⟨y0, hy0A, hy0M⟩ : ∃ y ∈ S.sat Λ, y ∉ S.M d Λ := by
    by_contra h
    push_neg at h
    exact hB.1 (le_antisymm hMA h)
  let J := Nat.findGreatest P r
  have hle : ∀ y ∈ S.sat Λ, S.levC d Λ y ≤ J := fun y hy =>
    Nat.le_findGreatest (hB.2.1 y hy) ⟨y, hy, rfl⟩
  have hPJ : P J := Nat.findGreatest_spec (hB.2.1 y0 hy0A) ⟨y0, hy0A, rfl⟩
  have hJr : J ≤ r := Nat.findGreatest_le r
  have hJ1 : 1 ≤ J := by
    have h1 : S.levC d Λ y0 ≠ 0 := fun h => hy0M ((hlev0 y0 hy0A).1 h)
    have := hle y0 hy0A
    omega

  let B : Submodule L.O S.V := S.sat Λ ⊓
    ((S.spanTo S.f (J - 1) ⊔ S.spanTo S.f' (J - 1)).restrictScalars L.O ⊔ S.M d Λ)
  have hBmem : ∀ y ∈ S.sat Λ, y ∈ B ↔ S.levC d Λ y ≤ J - 1 := by
    intro y hy
    rw [hlev y hy]
    constructor
    · rintro ⟨-, h⟩
      obtain ⟨u, hu, m, hm, rfl⟩ := Submodule.mem_sup.1 h
      exact ⟨u, hu, by simpa using hm⟩
    · rintro ⟨u, hu, hm⟩
      exact ⟨hy, Submodule.mem_sup.2 ⟨u, hu, y - u, hm, by abel⟩⟩
  have hMB : S.M d Λ ≤ B := le_inf hMA le_sup_right
  have hBA : B ≤ S.sat Λ := inf_le_left
  have hle' : B.map (S.M d Λ).mkQ ≤ (S.sat Λ).map (S.M d Λ).mkQ := Submodule.map_mono hBA
  haveI hfinB : Finite (B.map (S.M d Λ).mkQ) :=
    Finite.of_injective _ (Submodule.inclusion_injective hle')
  obtain ⟨i', hi'⟩ := (GlobalTheory.FiniteModuleOrder.card_eq_pow_and_index_ge L S.ϖ S.ϖ_irr
    (B.map (S.M d Λ).mkQ)).1
  have hi'q : Nat.card (B.map (S.M d Λ).mkQ) = S.q ^ i' := hi'
  have hn : S.nLev d Λ J = S.q ^ i - S.q ^ i' := by
    rw [← hcard, ← hi'q, ← ncard_classes _ _ _ hMB hBA]
    unfold Frames.nLev
    congr 1
    ext C
    constructor
    · rintro ⟨y, hy, hl, rfl⟩
      refine ⟨y, hy, fun h => ?_, rfl⟩
      have := (hBmem y hy).1 h
      omega
    · rintro ⟨y, hy, hl, rfl⟩
      refine ⟨y, hy, ?_, rfl⟩
      have h1 := hle y hy
      have h2 : ¬ S.levC d Λ y ≤ J - 1 := fun h => hl ((hBmem y hy).2 h)
      omega
  have hlt : S.q ^ i' < S.q ^ i := by
    rw [← hcard, ← hi'q]
    obtain ⟨y, hy, hl⟩ := hPJ
    have hss : (B.map (S.M d Λ).mkQ : Set (S.V ⧸ S.M d Λ)) ⊂
        ((S.sat Λ).map (S.M d Λ).mkQ : Set (S.V ⧸ S.M d Λ)) := by
      refine ⟨hle', fun h => ?_⟩
      obtain ⟨b, hb, hby⟩ := h (⟨y, hy, rfl⟩ : (S.M d Λ).mkQ y ∈ (S.sat Λ).map (S.M d Λ).mkQ)
      have h1 : b - y ∈ S.M d Λ := by simpa [Submodule.Quotient.eq] using hby
      have h2 : y ∈ B := by
        have h3 : y = b - (b - y) := by abel
        rw [h3]
        exact B.sub_mem hb (hMB h1)
      have := (hBmem y hy).1 h2
      omega
    exact Set.ncard_lt_ncard hss (Set.toFinite _)
  have hii : i' < i := (Nat.pow_lt_pow_iff_right (by omega)).1 hlt
  exact ⟨i, J, i', by omega, hia, hJ1, hJr, hii, hB, hbe, hle, hPJ, hn⟩

end GlobalTheory.HL.LevelFamilies
