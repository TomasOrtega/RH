import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPrincipalIdealRingOfHenselian
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsEqZpowMulUnit
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardEqPowAndIndexGe
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.EichlerIsometry
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BasisOfIsCompl
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SpanToLePerp
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemPerpSpan
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDoubleCosetTermBasicFacts
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DetUpdateRowLastSingle
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardCokernelUnramifiedOrderMatrixOfDetBaseStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDoubleCosetFramesLevelLeIffCongrFlagSteStatement
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.Defect
open GlobalTheory.HL.Eichler GlobalTheory.HL.StdLat GlobalTheory.UnramOrder Matrix

/- English proof (translation)
Establish `: Finite (P ⧸ Q)` using `Nat.finite_of_card_ne_zero hQ`. Set `` to `Fintype.ofFinite (P ⧸ Q)`. Set `f : N ⧸ M → AddChar (P ⧸ Q) ℂ` to `fun x => { toFun := fun t => χ x.out t.out map_zero_eq_one' := h1 _ _ (by`. Rewrite using `[← QuotientAddGroup.eq_zero_iff, QuotientAddGroup.out_eq'])`. Use the proof step `map_add_eq_mul' := fun a b => by`.

Establish `h : (a + b).out - (a.out + b.out) ∈ Q`. Rewrite using `[← QuotientAddGroup.eq_iff_sub_mem]`. Simplify using the standard rewrite rules. Use `h1 x.out _ h` as an intermediate fact. Rewrite using `[← AddChar.map_add_eq_mul, ← sub_add_cancel (a + b).out (a.out + b.out), AddChar.map_add_eq_mul, this, one_mul] }`.

Establish `hf : ∀ x (p : P), f x (p : P ⧸ Q) = χ x.out p` using `fun x p => by`. Establish `h : (p : P ⧸ Q).out - p ∈ Q`. Rewrite using `[← QuotientAddGroup.eq_iff_sub_mem]`. Simplify using the standard rewrite rules. Express the relevant statement in the definitionally equal form `χ x.out (p : P ⧸ Q).out = _`.

Rewrite using `[← sub_add_cancel (p : P ⧸ Q).out p, AddChar.map_add_eq_mul, h1 _ _ h, one_mul]`. Establish `hinj : Function.Injective f` using `fun x x' h => by`. Establish `: χ x.out = χ x'.out`. Use extensionality with `p`. Rewrite using `[← hf, ← hf, h]`.

Establish `h3` using `QuotientAddGroup.eq_iff_sub_mem.2 (h2 _ _ this)`. Simplify using `using h3`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[AddSubgroup.index, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]`. Conclude with `AddChar.card_addChar_le _ _`.
-/
theorem index_le_of_chars {N P : Type} [AddCommGroup N] [AddCommGroup P] (M : AddSubgroup N)
    (Q : AddSubgroup P) (hQ : Q.index ≠ 0) (χ : N → AddChar P ℂ) (h1 : ∀ y, ∀ p ∈ Q, χ y p = 1)
    (h2 : ∀ y y', χ y = χ y' → y - y' ∈ M) : M.index ≤ Q.index := by
  have : Finite (P ⧸ Q) := Nat.finite_of_card_ne_zero hQ
  let := Fintype.ofFinite (P ⧸ Q)
  let f : N ⧸ M → AddChar (P ⧸ Q) ℂ := fun x =>
    { toFun := fun t => χ x.out t.out
      map_zero_eq_one' := h1 _ _ (by
        rw [← QuotientAddGroup.eq_zero_iff, QuotientAddGroup.out_eq'])
      map_add_eq_mul' := fun a b => by
        have h : (a + b).out - (a.out + b.out) ∈ Q := by
          rw [← QuotientAddGroup.eq_iff_sub_mem]; simp
        have := h1 x.out _ h
        rw [← AddChar.map_add_eq_mul, ← sub_add_cancel (a + b).out (a.out + b.out),
          AddChar.map_add_eq_mul, this, one_mul] }
  have hf : ∀ x (p : P), f x (p : P ⧸ Q) = χ x.out p := fun x p => by
    have h : (p : P ⧸ Q).out - p ∈ Q := by
      rw [← QuotientAddGroup.eq_iff_sub_mem]; simp
    change χ x.out (p : P ⧸ Q).out = _
    rw [← sub_add_cancel (p : P ⧸ Q).out p, AddChar.map_add_eq_mul, h1 _ _ h, one_mul]
  have hinj : Function.Injective f := fun x x' h => by
    have : χ x.out = χ x'.out := by
      ext p; rw [← hf, ← hf, h]
    have h3 := QuotientAddGroup.eq_iff_sub_mem.2 (h2 _ _ this)
    simpa using h3
  calc M.index ≤ Nat.card (AddChar (P ⧸ Q) ℂ) := Nat.card_le_card_of_injective f hinj
    _ ≤ Q.index := by
      rw [AddSubgroup.index, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
      exact AddChar.card_addChar_le _ _

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

/- English proof (translation)
Simplify using `only [hf_sum_l, hf_smul_l]`.
-/
theorem hf_comb (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) {ι : Type} [Fintype ι]
    (b : ι → Fin n → E) (c : ι → E) (y : Fin n → E) :
    hf L Hm (∑ i, c i • b i) y = ∑ i, c i * hf L Hm (b i) y := by
  simp only [hf_sum_l, hf_smul_l]

/- English proof (translation)
Simplify using `only [hf_sum_r, hf_smul_r]`.
-/
theorem hf_comb_r (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) {ι : Type} [Fintype ι]
    (b : ι → Fin n → E) (c : ι → E) (y : Fin n → E) :
    hf L Hm y (∑ i, c i • b i) = ∑ i, L.cj (c i) * hf L Hm y (b i) := by
  simp only [hf_sum_r, hf_smul_r]

/- English proof (translation)
The claim follows from `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ (⟨c i, hc i⟩ : L.O) (Submodule.subset_span ⟨i, rfl⟩)`.
-/
theorem comb_mem (L : LocE F E) {n : ℕ} {ι : Type} [Fintype ι] (b : ι → Fin n → E) (c : ι → E)
    (hc : ∀ i, c i ∈ L.O) : ∑ i, c i • b i ∈ Submodule.span L.O (Set.range b) :=
  Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ (⟨c i, hc i⟩ : L.O) (Submodule.subset_span ⟨i, rfl⟩)

/- English proof (translation)
Establish `hb : ∀ i, b i ∈ N` using `fun i => hMN (Submodule.subset_span ⟨i, rfl⟩)`. Use `set G : Matrix ι ι E := Matrix.of fun i j => hf L Hm (b i) (b j) with hG`. Set `A : Matrix ι ι L.O` to `Matrix.of fun i j => ⟨hf L Hm (b j) (b i), hint _ (hb j) _ (hb i)⟩`. Establish `hAG : A.map L.O.subtype = Gᵀ` using `rfl`. Establish `hAdet : ((A.det : L.O) : E) = G.det`.

Rewrite using `[← Matrix.det_transpose G, ← hAG]`. Conclude with `RingHom.map_det L.O.subtype A`. Establish `hϖ0 : (ϖ : F) ≠ 0` using `fun h => hϖ.ne_zero (Subtype.ext h)`. Establish `hu0 : ((u : 𝒪[F]) : F) ≠ 0` using `fun h => u.ne_zero (Subtype.ext h)`. Establish `hGu : IsUnit G.det`.

Rewrite using `[hdet]`. Conclude with `(IsUnit.mk0 _ (mul_ne_zero (pow_ne_zero _ hϖ0) hu0)).map _`. Use `choose co hco using fun y : N => (Submodule.mem_span_range_iff_exists_fun E).1 (hN y y.2)`. Establish `hpair : ∀ (c : ι → E) j, hf L Hm (∑ i, c i • b i) (b j) = (Gᵀ *ᵥ c) j` using `fun c j => by`. Rewrite using `[hf_comb]`.

Simplify using `only [Matrix.mulVec, dotProduct, hG, Matrix.transpose_apply, Matrix.of_apply, mul_comm]`. Set `φ : N →+ (ι → L.O)` to `{ toFun := fun y j => ⟨hf L Hm y (b j), hint _ y.2 _ (hb j)⟩ map_zero' := by funext j; exact Subtype.ext (hf_zero_l _ _ _) map_add' := fun x y => by funext j; exact Subtype.ext (hf_add_l _ _ _ _ _) }`. Establish `hφ : ∀ y j, ((φ y j : L.O) : E) = (Gᵀ *ᵥ co y) j` using `fun y j => by`. Rewrite using `[← hpair, hco]`. Both sides reduce to the same expression.

Establish `hA : ∀ (c : ι → L.O) j, (((A *ᵥ c) j : L.O) : E) = (Gᵀ *ᵥ fun i => (c i : E)) j` using `fun c j => RingHom.map_mulVec L.O.subtype A c j`. Use `⟨fun y hy => ?_, ?_⟩` and prove the remaining obligations. Establish `h1 : ∀ i, G.det * co ⟨y, hy⟩ i ∈ L.O` using `fun i => by`. Establish `h2 : Gᵀ.adjugate *ᵥ (Gᵀ *ᵥ co ⟨y, hy⟩) = G.det • co ⟨y, hy⟩`. Rewrite using `[Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec, Matrix.det_transpose]`.

Establish `h3` using `RingHom.map_mulVec L.O.subtype A.adjugate (φ ⟨y, hy⟩) i`. Establish `h4 : A.adjugate.map L.O.subtype = Gᵀ.adjugate` using `RingHom.map_adjugate L.O.subtype A`. Establish `h5 : L.O.subtype ∘ φ ⟨y, hy⟩ = Gᵀ *ᵥ co ⟨y, hy⟩` using `funext (hφ _)`. Rewrite `h3` using `[h4, h5, h2]`. Establish `h6 : L.O.subtype ((A.adjugate *ᵥ φ ⟨y, hy⟩) i) ∈ L.O` using `Subtype.property _`.

Rewrite `h6` using `[h3]`. Then use the resulting hypothesis. Establish `h6 : y = ∑ i, co ⟨y, hy⟩ i • b i` using `(hco ⟨y, hy⟩).symm`. Rewrite using `[h6, Finset.smul_sum]`. Simplify using `only [smul_smul]`. Use `comb_mem L b _ fun i => ?_` and prove the remaining obligations.

Establish `h7` using `L.O.mul_mem ((algebraMap_mem_iff L _).2 (u⁻¹ : (𝒪[F])ˣ).1.2) (h1 i)`. Establish `h8 : (((u⁻¹ : (𝒪[F])ˣ) : 𝒪[F]) : F) * ((ϖ : F) ^ a * ((u : 𝒪[F]) : F)) = (ϖ : F) ^ a`. Rewrite using `[mul_left_comm, ← Subring.coe_mul, Units.inv_mul]`. Simplify using the standard rewrite rules. Rewrite `h7` using `[hdet, ← mul_assoc, ← map_mul, h8]`. Then use the resulting hypothesis.

Use `set M := Submodule.span L.O (Set.range b) with hM`. Set `K : AddSubgroup (ι → L.O)` to `(LinearMap.range A.mulVecLin).toAddSubgroup`. Establish `hK : K.index = resQ ϖ ^ (2 * a)` using `GlobalTheory.T.card_cokernel_unramifiedOrder_matrix_of_det_base L ϖ hϖ ι A a u (hAdet.trans hdet)`. Establish `hq : 2 ≤ resQ ϖ` using `(order_facts L ϖ hϖ).2.2.2.2.2.2.1`. Establish `hinj : Function.Injective Gᵀ.mulVec` using `Matrix.mulVec_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det _).2 (by rwa [Matrix.det_transpose]))`.

Establish `hcomap : K.comap φ = M.toAddSubgroup.addSubgroupOf N.toAddSubgroup`. Use extensionality with `y`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨c, hc⟩`. Establish `h1 : (fun i => (c i : E)) = co y` using `hinj (funext fun j => by`.

Rewrite using `[← hA, ← hφ, ← hc]`. Use the proof step `rfl)`. Express the relevant statement in the definitionally equal form `(y : Fin n → E) ∈ M`. Rewrite using `[← hco y, ← h1]`. Conclude with `comb_mem L b _ fun i => (c i).2`.

Introduce `hy`. Take `⟨c, hc⟩` from `(Submodule.mem_span_range_iff_exists_fun L.O).1 (show (y : Fin n → E) ∈ M from hy)`. Use `⟨c, funext fun j => Subtype.ext ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.mulVecLin_apply, hA, ← hpair]`. Conclude with `congrArg (fun v => hf L Hm v (b j)) hc`.

Establish `hle : K ≤ φ.range`. Introduce and unpack `_ ⟨c, rfl⟩`. Use `⟨⟨∑ i, (c i : E) • b i, hMN (comb_mem L b _ fun i => (c i).2)⟩,` and prove the remaining obligations. Use function extensionality and compare the values at `fun j => Subtype.ext ?_⟩`. Rewrite using `[Matrix.mulVecLin_apply, hA, ← hpair]`.

Both sides reduce to the same expression. Establish `hmul` using `AddSubgroup.relIndex_mul_index hle`. Rewrite `hmul` using `[← AddSubgroup.index_comap, hcomap, hK]`. Establish `hne : resQ ϖ ^ (2 * a) ≠ 0` using `pow_ne_zero _ (by omega)`. Set `β : N → (ι → L.O) →+ E` to `fun y => { toFun := fun p => ∑ i, L.cj (co y i) * (p i : E) map_zero' := by simp map_add' := fun p p' => by simp [mul_add, Finset.sum_add_distrib] }`.

Establish `hO : ∀ x ∈ L.O, L.psi0 x = 1` using `fun x hx => by`. Simplify using `using (L.additive_character_dual_ring x).2 hx 1 L.O.one_mem`. Establish `hidx` using `index_le_of_chars (M.toAddSubgroup.addSubgroupOf N.toAddSubgroup) φ.range (fun h => hne (by rw [← hmul, h, mul_zero])) (fun y => L.psi0.compAddMonoidHom (β y)) (by`. Introduce and unpack `y _ ⟨x, rfl⟩`. Apply `hO` to reduce the goal to its premises.

Use `hint _ x.2 _ y.2` as an intermediate fact. Rewrite using `[← hco y, hf_comb_r] at this)` and apply the resulting hypothesis. Use the proof step `(by`. Introduce `y y' h`. Express the relevant statement in the definitionally equal form `((y : Fin n → E) - y') ∈ M`.

Rewrite using `[← hco y, ← hco y', ← Finset.sum_sub_distrib]`. Simplify using `only [← sub_smul]`. Use `comb_mem L b _ fun i => ?_` and prove the remaining obligations. Rewrite using `[← L.cj_cj (co y i - co y' i)]`. Use `cj_mem L ((L.additive_character_dual_ring _).1 fun t ht => ?_)` and prove the remaining obligations.

Establish `h1` using `DFunLike.congr_fun h (Pi.single i ⟨t, ht⟩)`. Establish `h2 : ∀ z, β z (Pi.single i ⟨t, ht⟩) = L.cj (co z i) * t` using `fun z => by`. Express the relevant statement in the definitionally equal form `∑ j, _ = _`. Rewrite using `[Finset.sum_eq_single i (fun j _ hj => by simp [hj]) (by simp)]`. Simplify using the standard rewrite rules.

Simplify using `only [AddChar.compAddMonoidHom_apply, h2] at h1`. Establish `h3` using `L.psi0.map_add_eq_mul (L.cj (co y' i) * t) (-(L.cj (co y' i) * t))`. Rewrite using `[map_sub, sub_mul, sub_eq_add_neg, AddChar.map_add_eq_mul, h1, ← h3]`. Use the proof step `simp)`. Establish `hfin : Finite (N ⧸ M.comap N.subtype)` using `Nat.finite_of_card_ne_zero (fun h => hne (by`.

Rewrite using `[← hmul]`. Conclude with `mul_eq_zero_of_left h _))`. Take `⟨i, hi⟩` from `(GlobalTheory.FiniteModuleOrder.card_eq_pow_and_index_ge L ϖ hϖ (N ⧸ M.comap N.subtype)).1`. Establish `hi' : (M.toAddSubgroup.addSubgroupOf N.toAddSubgroup).index = resQ ϖ ^ i` using `hi`. Use `⟨i, ?_, hi'⟩` and prove the remaining obligations.

Rewrite `hmul`, `hidx` using `[hi']`. Establish `h9 : resQ ϖ ^ (2 * i) ≤ resQ ϖ ^ (2 * a)`. Rewrite using `[← hmul, two_mul, pow_add]`. Conclude with `Nat.mul_le_mul_left _ hidx`. Use `(Nat.pow_le_pow_iff_right (by omega)).1 h9` as an intermediate fact.

Use linear arithmetic over natural numbers and integers.
-/
theorem defect [IsNonarchimedeanLocalField F] [CharZero F] (L : LocE F E) (ϖ : 𝒪[F])
    (hϖ : Irreducible ϖ) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) {ι : Type} [Fintype ι]
    [DecidableEq ι] (b : ι → Fin n → E) (a : ℕ) (u : (𝒪[F])ˣ)
    (hdet : (Matrix.of fun i j => hf L Hm (b i) (b j)).det =
      algebraMap F E ((ϖ : F) ^ a * ((u : 𝒪[F]) : F)))
    (N : Submodule L.O (Fin n → E)) (hMN : Submodule.span L.O (Set.range b) ≤ N)
    (hN : ∀ y ∈ N, y ∈ Submodule.span E (Set.range b))
    (hint : ∀ x ∈ N, ∀ y ∈ N, hf L Hm x y ∈ L.O) :
    (∀ y ∈ N, algebraMap F E ((ϖ : F) ^ a) • y ∈ Submodule.span L.O (Set.range b)) ∧
    ∃ i ≤ a, (Submodule.span L.O (Set.range b)).toAddSubgroup.relIndex N.toAddSubgroup =
      resQ ϖ ^ i := by
  have hb : ∀ i, b i ∈ N := fun i => hMN (Submodule.subset_span ⟨i, rfl⟩)
  set G : Matrix ι ι E := Matrix.of fun i j => hf L Hm (b i) (b j) with hG
  let A : Matrix ι ι L.O := Matrix.of fun i j => ⟨hf L Hm (b j) (b i), hint _ (hb j) _ (hb i)⟩
  have hAG : A.map L.O.subtype = Gᵀ := rfl
  have hAdet : ((A.det : L.O) : E) = G.det := by
    rw [← Matrix.det_transpose G, ← hAG]
    exact RingHom.map_det L.O.subtype A
  have hϖ0 : (ϖ : F) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
  have hu0 : ((u : 𝒪[F]) : F) ≠ 0 := fun h => u.ne_zero (Subtype.ext h)
  have hGu : IsUnit G.det := by
    rw [hdet]; exact (IsUnit.mk0 _ (mul_ne_zero (pow_ne_zero _ hϖ0) hu0)).map _
  choose co hco using fun y : N => (Submodule.mem_span_range_iff_exists_fun E).1 (hN y y.2)
  have hpair : ∀ (c : ι → E) j, hf L Hm (∑ i, c i • b i) (b j) = (Gᵀ *ᵥ c) j := fun c j => by
    rw [hf_comb]
    simp only [Matrix.mulVec, dotProduct, hG, Matrix.transpose_apply, Matrix.of_apply, mul_comm]
  let φ : N →+ (ι → L.O) :=
    { toFun := fun y j => ⟨hf L Hm y (b j), hint _ y.2 _ (hb j)⟩
      map_zero' := by funext j; exact Subtype.ext (hf_zero_l _ _ _)
      map_add' := fun x y => by funext j; exact Subtype.ext (hf_add_l _ _ _ _ _) }
  have hφ : ∀ y j, ((φ y j : L.O) : E) = (Gᵀ *ᵥ co y) j := fun y j => by
    rw [← hpair, hco]; rfl
  have hA : ∀ (c : ι → L.O) j, (((A *ᵥ c) j : L.O) : E) = (Gᵀ *ᵥ fun i => (c i : E)) j :=
    fun c j => RingHom.map_mulVec L.O.subtype A c j
  refine ⟨fun y hy => ?_, ?_⟩
  · have h1 : ∀ i, G.det * co ⟨y, hy⟩ i ∈ L.O := fun i => by
      have h2 : Gᵀ.adjugate *ᵥ (Gᵀ *ᵥ co ⟨y, hy⟩) = G.det • co ⟨y, hy⟩ := by
        rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec,
          Matrix.det_transpose]
      have h3 := RingHom.map_mulVec L.O.subtype A.adjugate (φ ⟨y, hy⟩) i
      have h4 : A.adjugate.map L.O.subtype = Gᵀ.adjugate := RingHom.map_adjugate L.O.subtype A
      have h5 : L.O.subtype ∘ φ ⟨y, hy⟩ = Gᵀ *ᵥ co ⟨y, hy⟩ := funext (hφ _)
      rw [h4, h5, h2] at h3
      have h6 : L.O.subtype ((A.adjugate *ᵥ φ ⟨y, hy⟩) i) ∈ L.O := Subtype.property _
      rwa [h3] at h6
    have h6 : y = ∑ i, co ⟨y, hy⟩ i • b i := (hco ⟨y, hy⟩).symm
    rw [h6, Finset.smul_sum]
    simp only [smul_smul]
    refine comb_mem L b _ fun i => ?_
    have h7 := L.O.mul_mem ((algebraMap_mem_iff L _).2 (u⁻¹ : (𝒪[F])ˣ).1.2) (h1 i)
    have h8 : (((u⁻¹ : (𝒪[F])ˣ) : 𝒪[F]) : F) * ((ϖ : F) ^ a * ((u : 𝒪[F]) : F)) = (ϖ : F) ^ a := by
      rw [mul_left_comm, ← Subring.coe_mul, Units.inv_mul]; simp
    rwa [hdet, ← mul_assoc, ← map_mul, h8] at h7
  · set M := Submodule.span L.O (Set.range b) with hM
    let K : AddSubgroup (ι → L.O) := (LinearMap.range A.mulVecLin).toAddSubgroup
    have hK : K.index = resQ ϖ ^ (2 * a) := GlobalTheory.T.card_cokernel_unramifiedOrder_matrix_of_det_base L ϖ hϖ ι A a u (hAdet.trans hdet)
    have hq : 2 ≤ resQ ϖ := (order_facts L ϖ hϖ).2.2.2.2.2.2.1
    have hinj : Function.Injective Gᵀ.mulVec :=
      Matrix.mulVec_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det _).2
        (by rwa [Matrix.det_transpose]))
    have hcomap : K.comap φ = M.toAddSubgroup.addSubgroupOf N.toAddSubgroup := by
      ext y
      constructor
      · rintro ⟨c, hc⟩
        have h1 : (fun i => (c i : E)) = co y := hinj (funext fun j => by
          rw [← hA, ← hφ, ← hc]; rfl)
        change (y : Fin n → E) ∈ M
        rw [← hco y, ← h1]
        exact comb_mem L b _ fun i => (c i).2
      · intro hy
        obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun L.O).1 (show (y : Fin n → E) ∈ M from hy)
        refine ⟨c, funext fun j => Subtype.ext ?_⟩
        rw [Matrix.mulVecLin_apply, hA, ← hpair]
        exact congrArg (fun v => hf L Hm v (b j)) hc
    have hle : K ≤ φ.range := by
      rintro _ ⟨c, rfl⟩
      refine ⟨⟨∑ i, (c i : E) • b i, hMN (comb_mem L b _ fun i => (c i).2)⟩,
        funext fun j => Subtype.ext ?_⟩
      rw [Matrix.mulVecLin_apply, hA, ← hpair]; rfl
    have hmul := AddSubgroup.relIndex_mul_index hle
    rw [← AddSubgroup.index_comap, hcomap, hK] at hmul
    have hne : resQ ϖ ^ (2 * a) ≠ 0 := pow_ne_zero _ (by omega)
    let β : N → (ι → L.O) →+ E := fun y =>
      { toFun := fun p => ∑ i, L.cj (co y i) * (p i : E)
        map_zero' := by simp
        map_add' := fun p p' => by simp [mul_add, Finset.sum_add_distrib] }
    have hO : ∀ x ∈ L.O, L.psi0 x = 1 := fun x hx => by
      simpa using (L.additive_character_dual_ring x).2 hx 1 L.O.one_mem
    have hidx := index_le_of_chars (M.toAddSubgroup.addSubgroupOf N.toAddSubgroup) φ.range
      (fun h => hne (by rw [← hmul, h, mul_zero])) (fun y => L.psi0.compAddMonoidHom (β y))
      (by
        rintro y _ ⟨x, rfl⟩
        apply hO
        have := hint _ x.2 _ y.2
        rwa [← hco y, hf_comb_r] at this)
      (by
        intro y y' h
        change ((y : Fin n → E) - y') ∈ M
        rw [← hco y, ← hco y', ← Finset.sum_sub_distrib]
        simp only [← sub_smul]
        refine comb_mem L b _ fun i => ?_
        rw [← L.cj_cj (co y i - co y' i)]
        refine cj_mem L ((L.additive_character_dual_ring _).1 fun t ht => ?_)
        have h1 := DFunLike.congr_fun h (Pi.single i ⟨t, ht⟩)
        have h2 : ∀ z, β z (Pi.single i ⟨t, ht⟩) = L.cj (co z i) * t := fun z => by
          change ∑ j, _ = _
          rw [Finset.sum_eq_single i (fun j _ hj => by simp [hj]) (by simp)]
          simp
        simp only [AddChar.compAddMonoidHom_apply, h2] at h1
        have h3 := L.psi0.map_add_eq_mul (L.cj (co y' i) * t) (-(L.cj (co y' i) * t))
        rw [map_sub, sub_mul, sub_eq_add_neg, AddChar.map_add_eq_mul, h1, ← h3]
        simp)
    have hfin : Finite (N ⧸ M.comap N.subtype) := Nat.finite_of_card_ne_zero (fun h => hne (by
      rw [← hmul]; exact mul_eq_zero_of_left h _))
    obtain ⟨i, hi⟩ := (GlobalTheory.FiniteModuleOrder.card_eq_pow_and_index_ge L ϖ hϖ
      (N ⧸ M.comap N.subtype)).1
    have hi' : (M.toAddSubgroup.addSubgroupOf N.toAddSubgroup).index = resQ ϖ ^ i := hi
    refine ⟨i, ?_, hi'⟩
    rw [hi'] at hmul hidx
    have h9 : resQ ϖ ^ (2 * i) ≤ resQ ϖ ^ (2 * a) := by
      rw [← hmul, two_mul, pow_add]; exact Nat.mul_le_mul_left _ hidx
    have := (Nat.pow_le_pow_iff_right (by omega)).1 h9
    omega

omit [TopologicalSpace E] in
/- English proof (translation)
Use extensionality with `a b`. Simplify using `only [Matrix.submatrix_apply, Matrix.mul_apply]`. Use `(Fintype.sum_of_injective (Fin.castLE hl) (Fin.castLE_injective hl) _ _ (fun i hi => ?_) fun _ => rfl).symm` and prove the remaining obligations. Use `h a b i (not_lt.1 fun h' => hi ⟨⟨i, h'⟩, rfl⟩)` and prove the remaining obligations.
-/
theorem submatrix_mul_of_zero {N l : ℕ} (hl : l ≤ N) (A B : Matrix (Fin N) (Fin N) E)
    (h : ∀ (a b : Fin l) (i : Fin N), l ≤ (i : ℕ) → A (Fin.castLE hl a) i * B i (Fin.castLE hl b) = 0) :
    (A * B).submatrix (Fin.castLE hl) (Fin.castLE hl) =
      A.submatrix (Fin.castLE hl) (Fin.castLE hl) * B.submatrix (Fin.castLE hl) (Fin.castLE hl) := by
  ext a b
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  refine (Fintype.sum_of_injective (Fin.castLE hl) (Fin.castLE_injective hl) _ _ (fun i hi => ?_)
    fun _ => rfl).symm
  refine h a b i (not_lt.1 fun h' => hi ⟨⟨i, h'⟩, rfl⟩)

omit [TopologicalSpace E] in
/- English proof (translation)
Establish `hl` using `Nat.lt_succ_iff.mp l.2`. Establish `hd : (s.submatrix (Fin.castLE hl) (Fin.castLE hl)).det = 1`. Rewrite using `[Matrix.det_of_isUpperTriangular (M := s.submatrix (Fin.castLE hl) (Fin.castLE hl)) (fun i j h => hs.1 _ _ h)]`. Simplify using `[hs.2]`. Establish `h0 : ∀ (b : Fin l) (i : Fin N), (l : ℕ) ≤ i → s i (Fin.castLE hl b) = 0` using `fun b i h => hs.1 _ _ (show (b : ℕ) < (i : ℕ) from lt_of_lt_of_le b.2 h)`.

Prove the components needed by the constructor for the conclusion. Unfold `lead`. Rewrite using `[submatrix_mul_of_zero hl _ _ fun a b i h => by rw [h0 b i h, mul_zero], Matrix.det_mul, hd, mul_one]`. Unfold `lead`. Rewrite using `[submatrix_mul_of_zero hl _ _ fun a b i h => by`.

Rewrite using `[Matrix.transpose_apply, h0 a i h, zero_mul], Matrix.det_mul,`. Use the proof step `← Matrix.transpose_submatrix, Matrix.det_transpose, hd, one_mul]`.
-/
theorem lead_mul_tri {N : ℕ} (Z s : Matrix (Fin N) (Fin N) E)
    (hs : (∀ i j, j < i → s i j = 0) ∧ (∀ i, s i i = 1)) (l : Fin (N + 1)) :
    lead (Z * s) l = lead Z l ∧ lead (sᵀ * Z) l = lead Z l := by
  have hl := Nat.lt_succ_iff.mp l.2
  have hd : (s.submatrix (Fin.castLE hl) (Fin.castLE hl)).det = 1 := by
    rw [Matrix.det_of_isUpperTriangular (M := s.submatrix (Fin.castLE hl) (Fin.castLE hl))
      (fun i j h => hs.1 _ _ h)]
    simp [hs.2]
  have h0 : ∀ (b : Fin l) (i : Fin N), (l : ℕ) ≤ i → s i (Fin.castLE hl b) = 0 := fun b i h =>
    hs.1 _ _ (show (b : ℕ) < (i : ℕ) from lt_of_lt_of_le b.2 h)
  constructor
  · unfold lead
    rw [submatrix_mul_of_zero hl _ _ fun a b i h => by rw [h0 b i h, mul_zero], Matrix.det_mul, hd,
      mul_one]
  · unfold lead
    rw [submatrix_mul_of_zero hl _ _ fun a b i h => by
      rw [Matrix.transpose_apply, h0 a i h, zero_mul], Matrix.det_mul,
      ← Matrix.transpose_submatrix, Matrix.det_transpose, hd, one_mul]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [Matrix.of_apply, hb, hb', hf_comb_r, hf_comb, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply]`. Conclude with `Finset.sum_congr rfl fun _ _ => mul_comm _ _`.
-/
theorem gram_change (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) {ι : Type} [Fintype ι]
    (e e' b b' : ι → Fin n → E) (P P' : Matrix ι ι E) (hb : ∀ i, b i = ∑ k, P k i • e k)
    (hb' : ∀ i, b' i = ∑ k, P' k i • e' k) :
    (Matrix.of fun i j => hf L Hm (b i) (b' j)) =
      Pᵀ * (Matrix.of fun i j => hf L Hm (e i) (e' j)) * P'.map L.cj := by
  ext i j
  simp only [Matrix.of_apply, hb, hb', hf_comb_r, hf_comb, Matrix.mul_apply,
    Matrix.transpose_apply, Matrix.map_apply]
  exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨i, hi, rfl⟩`. Rewrite using `[hg]`. Use `Submodule.sum_mem _ fun a _ => ?_` and prove the remaining obligations.

Distinguish the cases in `h : i < a`. Simplify using `[hs.1 _ _ h]`. Conclude with `Submodule.smul_mem _ _ (FrameOnto.mem_spanTo S g (lt_of_le_of_lt (not_lt.1 h) hi))`. Establish `key : ∀ m : ℕ, ∀ i : Fin (r + 1), (i : ℕ) = m → (i : ℕ) < j → g i ∈ S.spanTo g₁ j`. Introduce `m`.

Proceed by induction on `m using Nat.strong_induction_on with`. Consider the case `_ m ih`. Introduce `i him hi`. Establish `h1 : g i = g₁ i - ∑ a ∈ Finset.univ.erase i, s a i • g a`. Rewrite using `[hg, ← Finset.add_sum_erase _ _ (Finset.mem_univ i), hs.2]`.

Simplify using the standard rewrite rules. Rewrite using `[h1]`. Use `Submodule.sub_mem _ (FrameOnto.mem_spanTo S g₁ hi) (Submodule.sum_mem _ fun a ha => ?_)` and prove the remaining obligations. Break down `lt_or_gt_of_ne (Finset.ne_of_mem_erase ha) with h | h` into its components or cases. Conclude with `Submodule.smul_mem _ _ (ih a (him ▸ h) a rfl (lt_trans h hi))`.

Simplify using `[hs.1 _ _ h]`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨i, hi, rfl⟩`. Conclude with `key i i rfl hi`.
-/
theorem spanTo_eq (g g₁ : Fin (r + 1) → S.V) (s : Matrix (Fin (r + 1)) (Fin (r + 1)) E)
    (hs : (∀ i j, j < i → s i j = 0) ∧ (∀ i, s i i = 1)) (hg : ∀ j, g₁ j = ∑ i, s i j • g i)
    (j : ℕ) : S.spanTo g₁ j = S.spanTo g j := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨i, hi, rfl⟩
    rw [hg]
    refine Submodule.sum_mem _ fun a _ => ?_
    by_cases h : i < a
    · simp [hs.1 _ _ h]
    · exact Submodule.smul_mem _ _ (FrameOnto.mem_spanTo S g (lt_of_le_of_lt (not_lt.1 h) hi))
  · have key : ∀ m : ℕ, ∀ i : Fin (r + 1), (i : ℕ) = m → (i : ℕ) < j → g i ∈ S.spanTo g₁ j := by
      intro m
      induction m using Nat.strong_induction_on with
      | _ m ih =>
        intro i him hi
        have h1 : g i = g₁ i - ∑ a ∈ Finset.univ.erase i, s a i • g a := by
          rw [hg, ← Finset.add_sum_erase _ _ (Finset.mem_univ i), hs.2]; simp
        rw [h1]
        refine Submodule.sub_mem _ (FrameOnto.mem_spanTo S g₁ hi) (Submodule.sum_mem _ fun a ha => ?_)
        rcases lt_or_gt_of_ne (Finset.ne_of_mem_erase ha) with h | h
        · exact Submodule.smul_mem _ _ (ih a (him ▸ h) a rfl (lt_trans h hi))
        · simp [hs.1 _ _ h]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨i, hi, rfl⟩
    exact key i i rfl hi

noncomputable def gens (g g' : Fin (r + 1) → S.V) : Fin (r + 1) ⊕ Fin (r + 1) → S.V :=
  Sum.elim g fun b => algebraMap F E S.th⁻¹ • (g' b - g b)

/- English proof (translation)
Rewrite using `[gens, Set.Sum.elim_range]`. Both sides reduce to the same expression.
-/
theorem Mof_eq (g g' : Fin (r + 1) → S.V) :
    S.Mof g g' = Submodule.span L.O (Set.range (gens S g g')) := by
  rw [gens, Set.Sum.elim_range]; rfl

/- English proof (translation)
Take `⟨s, hs, h⟩` from `FrameOnto.exists_matrix S S.f S.T S.gram n hn`. Take `⟨s', hs', h'⟩` from `FrameOnto.exists_matrix S S.f' S.T' S.gram' n' hn'`. Establish `h1` using `congrArg Matrix.transpose (gram_change L S.Hm S.f' S.f _ _ s' s h' h)`. Establish `h2 : (Matrix.of fun a b => hf L S.Hm (n' (S.f' b)) (n (S.f a))) = (s.map L.cj)ᵀ * (S.Zh * s')`. Rewrite `h1` using `[Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose]`.

Conclude with `h1`. Rewrite using `[h2, (lead_mul_tri _ (s.map L.cj) ⟨fun i j h => by simp [hs.1 i j h], fun i => by simp [hs.2]⟩ l).2, (lead_mul_tri _ s' hs' l).1]`. Both sides reduce to the same expression.
-/
theorem lead_translate {n n' : S.GLV} (hn : n ∈ S.N) (hn' : n' ∈ S.N') (l : Fin (r + 2)) :
    lead (Matrix.of fun a b => hf L S.Hm (n' (S.f' b)) (n (S.f a))) l = S.D l := by
  obtain ⟨s, hs, h⟩ := FrameOnto.exists_matrix S S.f S.T S.gram n hn
  obtain ⟨s', hs', h'⟩ := FrameOnto.exists_matrix S S.f' S.T' S.gram' n' hn'
  have h1 := congrArg Matrix.transpose (gram_change L S.Hm S.f' S.f _ _ s' s h' h)
  have h2 : (Matrix.of fun a b => hf L S.Hm (n' (S.f' b)) (n (S.f a))) =
      (s.map L.cj)ᵀ * (S.Zh * s') := by
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose] at h1
    exact h1
  rw [h2, (lead_mul_tri _ (s.map L.cj) ⟨fun i j h => by simp [hs.1 i j h], fun i => by simp [hs.2]⟩ l).2,
    (lead_mul_tri _ s' hs' l).1]
  rfl

/- English proof (translation)
Use `set t := algebraMap F E S.th⁻¹ with ht`. Set `e : Fin (r + 1) ⊕ Fin (r + 1) → S.V` to `Sum.elim (fun b => n (S.f b)) (fun b => n' (S.f' b))`. Set `P : Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) E` to `Matrix.fromBlocks 1 (-(t • 1)) 0 (t • 1)`. Establish `hP : ∀ i, gens S (fun b => n (S.f b)) (fun b => n' (S.f' b)) i = ∑ k, P k i • e k`. Introduce and unpack `(i | i)`.

Simplify using `[gens, P, e, Fintype.sum_sum_type, Matrix.one_apply, ite_smul]`. Simplify using `[gens, P, e, Fintype.sum_sum_type, Matrix.one_apply, ite_smul, ← ht, sub_eq_neg_add]`. Establish `hPd : P.det = t ^ (r + 1)`. Simplify using `[P, Matrix.det_fromBlocks_zero₂₁]`. Establish `hdet : ∀ {m : Type} [Fintype m] [DecidableEq m] (A : Matrix m m E), (A.map L.cj).det = L.cj A.det` using `fun A => (AlgEquiv.map_det L.cj A).symm`.

Use `set Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E := Matrix.of fun a b => hf L S.Hm (n' (S.f' b)) (n (S.f a)) with hZ`. Establish `he : (Matrix.of fun i j => hf L S.Hm (e i) (e j)) = Matrix.fromBlocks (Matrix.diagonal fun i => if i = Fin.last r then -algebraMap F E S.T else 0) (Z.map L.cj) Zᵀ (Matrix.diagonal fun i => if i = Fin.last r then -algebraMap F E S.T' else 0)`. Establish `i1 : n ∈ isomG L S.Hm` using `hn.1.1`. Establish `i2 : n' ∈ isomG L S.Hm` using `hn'.1.1`. Use extensionality with `(i | i) (j | j)`.

Simplify using `only [e, Matrix.of_apply, Sum.elim_inl, Matrix.fromBlocks_apply₁₁, i1 _ _, S.gram, Matrix.diagonal_apply]`. Distinguish the cases in `h : i = j`. Simplify using `[h]`. Rewrite using `[if_neg h, if_neg]`. Introduce and unpack `⟨rfl, rfl⟩`.

Conclude with `h rfl`. Conclude with `(hf_cj L S.herm.1 _ _).symm`. Both sides reduce to the same expression. Simplify using `only [e, Matrix.of_apply, Sum.elim_inr, Matrix.fromBlocks_apply₂₂, i2 _ _, S.gram', Matrix.diagonal_apply]`. Distinguish the cases in `h : i = j`.

Simplify using `[h]`. Rewrite using `[if_neg h, if_neg]`. Introduce and unpack `⟨rfl, rfl⟩`. Conclude with `h rfl`. Establish `hD1 : Z.det = S.D (Fin.last (r + 1))` using `lead_translate S hn hn' (Fin.last (r + 1))`.

Establish `hD0 : (Z.submatrix Fin.castSucc Fin.castSucc).det = S.D (Fin.last r).castSucc` using `lead_translate S hn hn' (Fin.last r).castSucc`. Rewrite using `[gram_change L S.Hm e e _ _ P P hP hP, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hdet, hPd, he, GlobalTheory.det_gram_two_frames, Matrix.det_transpose, hdet, hD1, ← Matrix.transpose_submatrix, Matrix.det_transpose, Matrix.submatrix_map, hdet, hD0, map_pow, ht, AlgEqui …`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem det_gens {n n' : S.GLV} (hn : n ∈ S.N) (hn' : n' ∈ S.N') :
    (Matrix.of fun i j => hf L S.Hm (gens S (fun b => n (S.f b)) (fun b => n' (S.f' b)) i)
      (gens S (fun b => n (S.f b)) (fun b => n' (S.f' b)) j)).det =
      (-1) ^ (r + 1) * algebraMap F E S.th⁻¹ ^ (2 * (r + 1)) * S.G := by
  set t := algebraMap F E S.th⁻¹ with ht
  let e : Fin (r + 1) ⊕ Fin (r + 1) → S.V := Sum.elim (fun b => n (S.f b)) (fun b => n' (S.f' b))
  let P : Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) E :=
    Matrix.fromBlocks 1 (-(t • 1)) 0 (t • 1)
  have hP : ∀ i, gens S (fun b => n (S.f b)) (fun b => n' (S.f' b)) i = ∑ k, P k i • e k := by
    rintro (i | i)
    · simp [gens, P, e, Fintype.sum_sum_type, Matrix.one_apply, ite_smul]
    · simp [gens, P, e, Fintype.sum_sum_type, Matrix.one_apply, ite_smul, ← ht,
        sub_eq_neg_add]
  have hPd : P.det = t ^ (r + 1) := by
    simp [P, Matrix.det_fromBlocks_zero₂₁]
  have hdet : ∀ {m : Type} [Fintype m] [DecidableEq m] (A : Matrix m m E),
      (A.map L.cj).det = L.cj A.det := fun A => (AlgEquiv.map_det L.cj A).symm
  set Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E :=
    Matrix.of fun a b => hf L S.Hm (n' (S.f' b)) (n (S.f a)) with hZ
  have he : (Matrix.of fun i j => hf L S.Hm (e i) (e j)) = Matrix.fromBlocks
      (Matrix.diagonal fun i => if i = Fin.last r then -algebraMap F E S.T else 0) (Z.map L.cj) Zᵀ
      (Matrix.diagonal fun i => if i = Fin.last r then -algebraMap F E S.T' else 0) := by
    have i1 : n ∈ isomG L S.Hm := hn.1.1
    have i2 : n' ∈ isomG L S.Hm := hn'.1.1
    ext (i | i) (j | j)
    · simp only [e, Matrix.of_apply, Sum.elim_inl, Matrix.fromBlocks_apply₁₁, i1 _ _, S.gram,
        Matrix.diagonal_apply]
      by_cases h : i = j
      · simp [h]
      · rw [if_neg h, if_neg]; rintro ⟨rfl, rfl⟩; exact h rfl
    · exact (hf_cj L S.herm.1 _ _).symm
    · rfl
    · simp only [e, Matrix.of_apply, Sum.elim_inr, Matrix.fromBlocks_apply₂₂, i2 _ _, S.gram',
        Matrix.diagonal_apply]
      by_cases h : i = j
      · simp [h]
      · rw [if_neg h, if_neg]; rintro ⟨rfl, rfl⟩; exact h rfl
  have hD1 : Z.det = S.D (Fin.last (r + 1)) := lead_translate S hn hn' (Fin.last (r + 1))
  have hD0 : (Z.submatrix Fin.castSucc Fin.castSucc).det = S.D (Fin.last r).castSucc :=
    lead_translate S hn hn' (Fin.last r).castSucc
  rw [gram_change L S.Hm e e _ _ P P hP hP, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
    hdet, hPd, he, GlobalTheory.det_gram_two_frames, Matrix.det_transpose, hdet, hD1,
    ← Matrix.transpose_submatrix, Matrix.det_transpose, Matrix.submatrix_map, hdet, hD0, map_pow,
    ht, AlgEquiv.commutes, Frames.G, map_mul]
  ring

/- English proof (translation)
Establish `h1` using `RingHom.map_det L.O.subtype (Matrix.of fun i j => (⟨A i j, h i j⟩ : L.O))`. Establish `h2 : L.O.subtype (Matrix.of fun i j => (⟨A i j, h i j⟩ : L.O)).det ∈ L.O` using `Subtype.property _`. Rewrite `h2` using `[h1]`. Then use the resulting hypothesis.
-/
theorem det_mem {ι : Type} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι E) (h : ∀ i j, A i j ∈ L.O) :
    A.det ∈ L.O := by
  have h1 := RingHom.map_det L.O.subtype (Matrix.of fun i j => (⟨A i j, h i j⟩ : L.O))
  have h2 : L.O.subtype (Matrix.of fun i j => (⟨A i j, h i j⟩ : L.O)).det ∈ L.O := Subtype.property _
  rwa [h1] at h2

/- English proof (translation)
Take `⟨h1, h2, h3, -⟩` from `GlobalTheory.UnramVal.vE_valuation L ϖ hϖ`. Establish `hϖ0 : (ϖ : F) ≠ 0` using `fun h => hϖ.ne_zero (Subtype.ext h)`. Establish `hu0 : ∀ u : (𝒪[F])ˣ, ((u : 𝒪[F]) : F) ≠ 0` using `fun u h => u.ne_zero (Subtype.ext h)`. Proceed by induction on `m with`. Consider the case `zero`.

Establish `e1` using `h1 1 1 one_ne_zero one_ne_zero`. Establish `e2` using `h1 _ _ (hu0 u) (hu0 u⁻¹)`. Establish `e3` using `(h3 _ (hu0 u)).2 (Subtype.property _)`. Establish `e4` using `(h3 _ (hu0 u⁻¹)).2 (Subtype.property _)`. Rewrite `e2` using `[← Subring.coe_mul, Units.mul_inv, OneMemClass.coe_one]`.

Rewrite `e1` using `[mul_one]`. Rewrite using `[pow_zero, one_mul]`. Use linear arithmetic over natural numbers and integers. Consider the case `succ m ih`. Rewrite using `[pow_succ', mul_assoc, h1 _ _ hϖ0 (mul_ne_zero (pow_ne_zero _ hϖ0) (hu0 u)), h2, ih]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem vE_pow_mul [IsNonarchimedeanLocalField F] [CharZero F] (ϖ : 𝒪[F]) (hϖ : Irreducible ϖ)
    (m : ℕ) (u : (𝒪[F])ˣ) : vE L ϖ (algebraMap F E ((ϖ : F) ^ m * ((u : 𝒪[F]) : F))) = m := by
  obtain ⟨h1, h2, h3, -⟩ := GlobalTheory.UnramVal.vE_valuation L ϖ hϖ
  have hϖ0 : (ϖ : F) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
  have hu0 : ∀ u : (𝒪[F])ˣ, ((u : 𝒪[F]) : F) ≠ 0 := fun u h => u.ne_zero (Subtype.ext h)
  induction m with
  | zero =>
    have e1 := h1 1 1 one_ne_zero one_ne_zero
    have e2 := h1 _ _ (hu0 u) (hu0 u⁻¹)
    have e3 := (h3 _ (hu0 u)).2 (Subtype.property _)
    have e4 := (h3 _ (hu0 u⁻¹)).2 (Subtype.property _)
    rw [← Subring.coe_mul, Units.mul_inv, OneMemClass.coe_one] at e2
    rw [mul_one] at e1
    rw [pow_zero, one_mul]
    omega
  | succ m ih =>
    rw [pow_succ', mul_assoc, h1 _ _ hϖ0 (mul_ne_zero (pow_ne_zero _ hϖ0) (hu0 u)), h2, ih]
    push_cast; ring

/- English proof (translation)
Introduce `F _ _ _ _ _ E _ _ _ L r k S d Λ hT`. Take `⟨hSD, hW, hM, -, hfr', -⟩` from `GlobalTheory.HL.TermBasic.term_basic L r k S d Λ hT`. Take `⟨-, -, ⟨c, hc0, hc⟩, -, hDu, hth0, -⟩` from `GlobalTheory.FrameBasic.main L r k S`. Take `⟨-, -, hv, hvu⟩` from `GlobalTheory.UnramVal.vE_valuation L S.ϖ S.ϖ_irr`. Establish `hn : (S.wit d Λ).1 ∈ S.N` using `hW.2.2.1`.

Establish `hn' : (S.wit d Λ).2 ∈ S.N'` using `hW.2.2.2.1`. Establish `hint : ∀ x ∈ Λ, ∀ y ∈ Λ, hf L S.Hm x y ∈ L.O` using `fun x hx y hy => (hSD.2 y).2 hy x hx`. Establish `hMe : S.M d Λ = Submodule.span L.O (Set.range (gens S (S.fr d Λ) (S.fr' d Λ)))` using `Mof_eq S _ _`. Establish `hg : ∀ i, gens S (S.fr d Λ) (S.fr' d Λ) i ∈ Λ` using `fun i => (hM (hMe ▸ Submodule.subset_span ⟨i, rfl⟩)).1`. Establish `hf1 : ∀ b, S.fr d Λ b ∈ Λ` using `fun b => hg (Sum.inl b)`.

Establish `hf2 : ∀ b, S.fr' d Λ b ∈ Λ` using `fun b => ((hfr' (r + 1) le_rfl _).2 (Submodule.subset_span ⟨b, b.2, rfl⟩)).1`. Establish `hD : ∀ l, S.D l ∈ L.O` using `fun l => by`. Rewrite using `[← lead_translate S hn hn' l]`. Conclude with `det_mem _ fun i j => hint _ (hf2 _) _ (hf1 _)`. Establish `hsp : ∀ j, S.spanTo (S.fr d Λ) j = S.spanTo S.f j`.

Take `⟨s, hs, h⟩` from `FrameOnto.exists_matrix S S.f S.T S.gram _ hn`. Conclude with `spanTo_eq S _ _ s hs h`. Establish `hsp' : ∀ j, S.spanTo (S.fr' d Λ) j = S.spanTo S.f' j`. Take `⟨s, hs, h⟩` from `FrameOnto.exists_matrix S S.f' S.T' S.gram' _ hn'`. Conclude with `spanTo_eq S _ _ s hs h`.

Establish `hdet : (Matrix.of fun i j => hf L S.Hm (gens S (S.fr d Λ) (S.fr' d Λ) i) (gens S (S.fr d Λ) (S.fr' d Λ) j)).det = algebraMap F E ((-1) ^ (r + 1) * S.th⁻¹ ^ (2 * (r + 1)) * c)`. Use `(det_gens S hn hn').trans ?_` and prove the remaining obligations. Rewrite using `[hc]`. Simplify using `only [map_mul, map_pow, map_neg, map_one]`. Establish `hc' : ((-1) ^ (r + 1) * S.th⁻¹ ^ (2 * (r + 1)) * c : F) ≠ 0`.

Simplify using `[hc0, hth0]`. Establish `hmem : ((-1) ^ (r + 1) * S.th⁻¹ ^ (2 * (r + 1)) * c : F) ∈ 𝒪[F]`. Rewrite using `[← algebraMap_mem_iff L, ← hdet]`. Conclude with `det_mem _ fun i j => hint _ (hg i) _ (hg j)`. Take `⟨u, hu⟩` from `hvu _ hc'`.

Take `⟨m, hm⟩` from `Int.eq_ofNat_of_zero_le ((hv _ hc').2 hmem)`. Rewrite `hu` using `[hm, zpow_natCast]`. Establish `ha : S.a = m`. Establish `e1 : c = S.th ^ (2 * (r + 1)) * ((S.ϖ : F) ^ m * ((((-1) ^ (r + 1) * u : (𝒪[F])ˣ) : 𝒪[F]) : F))`. Establish `e2 : ((((-1) ^ (r + 1) * u : (𝒪[F])ˣ) : 𝒪[F]) : F) = (-1) ^ (r + 1) * ((u : 𝒪[F]) : F)`.

Simplify using the standard rewrite rules. Rewrite using `[e2, mul_left_comm ((S.ϖ : F) ^ m), ← hu, ← mul_assoc ((-1 : F) ^ _), ← mul_assoc ((-1 : F) ^ _), ← mul_pow, inv_pow]`. Clear the denominators using the available nonvanishing facts. Simplify using the standard rewrite rules. Unfold `Frames.a Frames.vth`.

Unfold `Frames.th at e1`. Rewrite using `[hc, e1]`. Use `split_ifs`. Rewrite using `[← mul_assoc, ← pow_add, vE_pow_mul _ S.ϖ_irr]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[one_pow, one_mul, vE_pow_mul _ S.ϖ_irr]`. Expand and normalize the polynomial expressions, which then agree. Establish `hvD : 0 ≤ S.vD`. Use `Finset.sum_nonneg fun l _ => ?_` and prove the remaining obligations.

Use `split_ifs with h`. Take `⟨e, he⟩` from `exists_norm L (hD l)`. Rewrite using `[he]`. Use `(hv _ fun h0 => ?_).2 e.2` and prove the remaining obligations. Rewrite `he` using `[h0, map_zero]`.

Apply `h.2` to reduce the goal to its premises. Rewrite using `[← L.cj_cj (S.D l), (hDu l h.2).mul_right_eq_zero.1 he, map_zero]`. Conclude with `le_rfl`. Establish `hq : 2 ≤ S.q` using `(order_facts L S.ϖ S.ϖ_irr).2.2.2.2.2.2.1`. Establish `hq1 : (1 : ℝ) ≤ S.q` using `by exact_mod_cast (by omega : 1 ≤ S.q)`.

Apply the tactic sequence `have hvth : 0 ≤ S.vth := by unfold Frames.vth; split_ifs <;> norm_num`. Establish `hHp : (S.q : ℝ) ^ S.a ≤ S.Hp` using `zpow_le_zpow_right₀ hq1 (by omega)`. Establish `hsat : ∀ y ∈ S.sat Λ, y ∈ S.spanTo (S.fr d Λ) (r + 1) ⊔ S.spanTo (S.fr' d Λ) (r + 1)` using `fun y hy => by rw [hsp, hsp']; exact hy.2`. Take `⟨hk, i, hi, hbe⟩` from `defect L S.ϖ S.ϖ_irr S.Hm (gens S (S.fr d Λ) (S.fr' d Λ)) m u (hdet.trans (congrArg _ hu)) (S.sat Λ) (hMe ▸ hM) (fun y hy => by`. Establish `h1 : ∀ b, S.fr d Λ b ∈ Submodule.span E (Set.range (gens S (S.fr d Λ) (S.fr' d Λ)))` using `fun b => Submodule.subset_span ⟨Sum.inl b, rfl⟩`.

Use `(sup_le (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_) : _ ≤ Submodule.span E (Set.range (gens S (S.fr d Λ) (S.fr' d Λ)))) (hsat y hy)` and prove the remaining obligations. Introduce and unpack `_ ⟨b, -, rfl⟩`. Conclude with `h1 b`. Introduce and unpack `_ ⟨b, -, rfl⟩`. Establish `h2 : S.fr' d Λ b = S.fr d Λ b + algebraMap F E S.th • gens S (S.fr d Λ) (S.fr' d Λ) (Sum.inr b)`.

Simplify using `only [gens, Sum.elim_inr, smul_smul, ← map_mul, mul_inv_cancel₀ hth0, map_one, one_smul]`. Normalize the expressions using the abelian group laws. Rewrite using `[h2]`. Conclude with `Submodule.add_mem _ (h1 b) (Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inr b, rfl⟩)))`. Use the proof step `(fun x hx y hy => hint x hx.1 y hy.1)`.

Rewrite `hk`, `hbe` using `[← hMe]`. Establish `hbe' : S.be d Λ = S.q ^ i` using `hbe`. Establish `hBB : S.BBzero d Λ ↔ S.be d Λ = 1`. Unfold `Frames.BBzero Frames.be`. Rewrite using `[AddSubgroup.relIndex_eq_one]`.

Conclude with `⟨fun h => by rw [h], fun h => le_antisymm hM h⟩`. Establish `hlev : ∀ y ∈ S.sat Λ, ∀ j, S.levC d Λ y ≤ j ↔ ∃ y₁ ∈ S.spanTo S.f j ⊔ S.spanTo S.f' j, y - y₁ ∈ S.M d Λ` using `fun y hy j => by`. Rewrite using `[← hsp, ← hsp']`. Conclude with `GlobalTheory.T.hermitianDoubleCosetFrames_level_le_iff_congr_flagSteps L r k S _ _ y (hsat y hy) j`. Use `⟨by omega, hvD, hD, hHp, le_trans (one_le_zpow₀ hq1 (by omega)) hHp, ⟨i, by omega, hbe'⟩, hBB, fun h => ?_, fun y hy => ?_, fun y hy => ?_, hlev⟩` and prove the remaining obligations.

Establish `hi0 : i ≠ 0`. Introduce and unpack `rfl`. Conclude with `h (hBB.2 (by simpa using hbe'))`. Use `le_trans ?_ hHp` and prove the remaining obligations. Simplify using `using zpow_le_zpow_right₀ hq1 (show (1 : ℤ) ≤ S.a by omega)`.

Rewrite using `[ha, zpow_natCast]`. Conclude with `hk y hy`. Rewrite using `[← Nat.le_zero, hlev y hy 0]`. Simplify using `[Frames.spanTo]`.
-/
theorem exponents_and_defect : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → 0 ≤ S.a ∧ 0 ≤ S.vD ∧ (∀ l, S.D l ∈ L.O) ∧ (S.q : ℝ) ^ S.a ≤ S.Hp ∧ 1 ≤ S.Hp ∧ (∃ i : ℕ, (i : ℤ) ≤ S.a ∧ S.be d Λ = S.q ^ i) ∧ (S.BBzero d Λ ↔ S.be d Λ = 1) ∧ (¬ S.BBzero d Λ → (S.q : ℝ) ≤ S.Hp) ∧ (∀ y ∈ S.sat Λ, algebraMap F E ((S.ϖ : F) ^ S.a) • y ∈ S.M d Λ) ∧ (∀ y ∈ S.sat Λ, S.levC d Λ y = 0 ↔ y ∈ S.M d Λ) ∧ ∀ y ∈ S.sat Λ, ∀ j, S.levC d Λ y ≤ j ↔ ∃ y₁ ∈ S.spanTo S.f j ⊔ S.spanTo S.f' j, y - y₁ ∈ S.M d Λ := by
  intro F _ _ _ _ _ E _ _ _ L r k S d Λ hT
  obtain ⟨hSD, hW, hM, -, hfr', -⟩ := GlobalTheory.HL.TermBasic.term_basic L r k S d Λ hT
  obtain ⟨-, -, ⟨c, hc0, hc⟩, -, hDu, hth0, -⟩ := GlobalTheory.FrameBasic.main L r k S
  obtain ⟨-, -, hv, hvu⟩ := GlobalTheory.UnramVal.vE_valuation L S.ϖ S.ϖ_irr
  have hn : (S.wit d Λ).1 ∈ S.N := hW.2.2.1
  have hn' : (S.wit d Λ).2 ∈ S.N' := hW.2.2.2.1
  have hint : ∀ x ∈ Λ, ∀ y ∈ Λ, hf L S.Hm x y ∈ L.O := fun x hx y hy => (hSD.2 y).2 hy x hx
  have hMe : S.M d Λ = Submodule.span L.O (Set.range (gens S (S.fr d Λ) (S.fr' d Λ))) := Mof_eq S _ _
  have hg : ∀ i, gens S (S.fr d Λ) (S.fr' d Λ) i ∈ Λ := fun i =>
    (hM (hMe ▸ Submodule.subset_span ⟨i, rfl⟩)).1
  have hf1 : ∀ b, S.fr d Λ b ∈ Λ := fun b => hg (Sum.inl b)
  have hf2 : ∀ b, S.fr' d Λ b ∈ Λ := fun b =>
    ((hfr' (r + 1) le_rfl _).2 (Submodule.subset_span ⟨b, b.2, rfl⟩)).1
  have hD : ∀ l, S.D l ∈ L.O := fun l => by
    rw [← lead_translate S hn hn' l]
    exact det_mem _ fun i j => hint _ (hf2 _) _ (hf1 _)
  have hsp : ∀ j, S.spanTo (S.fr d Λ) j = S.spanTo S.f j := by
    obtain ⟨s, hs, h⟩ := FrameOnto.exists_matrix S S.f S.T S.gram _ hn
    exact spanTo_eq S _ _ s hs h
  have hsp' : ∀ j, S.spanTo (S.fr' d Λ) j = S.spanTo S.f' j := by
    obtain ⟨s, hs, h⟩ := FrameOnto.exists_matrix S S.f' S.T' S.gram' _ hn'
    exact spanTo_eq S _ _ s hs h
  have hdet : (Matrix.of fun i j => hf L S.Hm (gens S (S.fr d Λ) (S.fr' d Λ) i)
      (gens S (S.fr d Λ) (S.fr' d Λ) j)).det =
      algebraMap F E ((-1) ^ (r + 1) * S.th⁻¹ ^ (2 * (r + 1)) * c) := by
    refine (det_gens S hn hn').trans ?_
    rw [hc]; simp only [map_mul, map_pow, map_neg, map_one]
  have hc' : ((-1) ^ (r + 1) * S.th⁻¹ ^ (2 * (r + 1)) * c : F) ≠ 0 := by
    simp [hc0, hth0]
  have hmem : ((-1) ^ (r + 1) * S.th⁻¹ ^ (2 * (r + 1)) * c : F) ∈ 𝒪[F] := by
    rw [← algebraMap_mem_iff L, ← hdet]
    exact det_mem _ fun i j => hint _ (hg i) _ (hg j)
  obtain ⟨u, hu⟩ := hvu _ hc'
  obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le ((hv _ hc').2 hmem)
  rw [hm, zpow_natCast] at hu
  have ha : S.a = m := by
    have e1 : c = S.th ^ (2 * (r + 1)) * ((S.ϖ : F) ^ m *
        ((((-1) ^ (r + 1) * u : (𝒪[F])ˣ) : 𝒪[F]) : F)) := by
      have e2 : ((((-1) ^ (r + 1) * u : (𝒪[F])ˣ) : 𝒪[F]) : F) = (-1) ^ (r + 1) * ((u : 𝒪[F]) : F) := by
        simp
      rw [e2, mul_left_comm ((S.ϖ : F) ^ m), ← hu, ← mul_assoc ((-1 : F) ^ _), ← mul_assoc ((-1 : F) ^ _),
        ← mul_pow, inv_pow]
      field_simp
      simp
    unfold Frames.a Frames.vth
    unfold Frames.th at e1
    rw [hc, e1]
    split_ifs
    · rw [← mul_assoc, ← pow_add, vE_pow_mul _ S.ϖ_irr]; push_cast; ring
    · rw [one_pow, one_mul, vE_pow_mul _ S.ϖ_irr]; ring
  have hvD : 0 ≤ S.vD := by
    refine Finset.sum_nonneg fun l _ => ?_
    split_ifs with h
    · obtain ⟨e, he⟩ := exists_norm L (hD l)
      rw [he]
      refine (hv _ fun h0 => ?_).2 e.2
      rw [h0, map_zero] at he
      apply h.2
      rw [← L.cj_cj (S.D l), (hDu l h.2).mul_right_eq_zero.1 he, map_zero]
    · exact le_rfl
  have hq : 2 ≤ S.q := (order_facts L S.ϖ S.ϖ_irr).2.2.2.2.2.2.1
  have hq1 : (1 : ℝ) ≤ S.q := by exact_mod_cast (by omega : 1 ≤ S.q)
  have hvth : 0 ≤ S.vth := by unfold Frames.vth; split_ifs <;> norm_num
  have hHp : (S.q : ℝ) ^ S.a ≤ S.Hp := zpow_le_zpow_right₀ hq1 (by omega)
  have hsat : ∀ y ∈ S.sat Λ, y ∈ S.spanTo (S.fr d Λ) (r + 1) ⊔ S.spanTo (S.fr' d Λ) (r + 1) :=
    fun y hy => by rw [hsp, hsp']; exact hy.2
  obtain ⟨hk, i, hi, hbe⟩ := defect L S.ϖ S.ϖ_irr S.Hm (gens S (S.fr d Λ) (S.fr' d Λ)) m u
    (hdet.trans (congrArg _ hu)) (S.sat Λ) (hMe ▸ hM)
    (fun y hy => by
      have h1 : ∀ b, S.fr d Λ b ∈ Submodule.span E (Set.range (gens S (S.fr d Λ) (S.fr' d Λ))) :=
        fun b => Submodule.subset_span ⟨Sum.inl b, rfl⟩
      refine (sup_le (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_) :
        _ ≤ Submodule.span E (Set.range (gens S (S.fr d Λ) (S.fr' d Λ)))) (hsat y hy)
      · rintro _ ⟨b, -, rfl⟩
        exact h1 b
      · rintro _ ⟨b, -, rfl⟩
        have h2 : S.fr' d Λ b = S.fr d Λ b +
            algebraMap F E S.th • gens S (S.fr d Λ) (S.fr' d Λ) (Sum.inr b) := by
          simp only [gens, Sum.elim_inr, smul_smul, ← map_mul, mul_inv_cancel₀ hth0, map_one, one_smul]
          abel
        rw [h2]
        exact Submodule.add_mem _ (h1 b)
          (Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inr b, rfl⟩)))
    (fun x hx y hy => hint x hx.1 y hy.1)
  rw [← hMe] at hk hbe
  have hbe' : S.be d Λ = S.q ^ i := hbe
  have hBB : S.BBzero d Λ ↔ S.be d Λ = 1 := by
    unfold Frames.BBzero Frames.be
    rw [AddSubgroup.relIndex_eq_one]
    exact ⟨fun h => by rw [h], fun h => le_antisymm hM h⟩
  have hlev : ∀ y ∈ S.sat Λ, ∀ j, S.levC d Λ y ≤ j ↔
      ∃ y₁ ∈ S.spanTo S.f j ⊔ S.spanTo S.f' j, y - y₁ ∈ S.M d Λ := fun y hy j => by
    rw [← hsp, ← hsp']
    exact GlobalTheory.T.hermitianDoubleCosetFrames_level_le_iff_congr_flagSteps L r k S _ _ y (hsat y hy) j
  refine ⟨by omega, hvD, hD, hHp, le_trans (one_le_zpow₀ hq1 (by omega)) hHp,
    ⟨i, by omega, hbe'⟩, hBB, fun h => ?_, fun y hy => ?_, fun y hy => ?_, hlev⟩
  · have hi0 : i ≠ 0 := by
      rintro rfl
      exact h (hBB.2 (by simpa using hbe'))
    refine le_trans ?_ hHp
    simpa using zpow_le_zpow_right₀ hq1 (show (1 : ℤ) ≤ S.a by omega)
  · rw [ha, zpow_natCast]; exact hk y hy
  · rw [← Nat.le_zero, hlev y hy 0]
    simp [Frames.spanTo]

end GlobalTheory.HL.Defect
