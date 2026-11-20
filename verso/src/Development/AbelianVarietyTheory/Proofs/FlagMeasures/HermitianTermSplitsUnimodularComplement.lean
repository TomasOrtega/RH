import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GFrames
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsEqZpowMulUnit
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrthonormalBasisAndOneOrbit
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsEquivOfRetractions
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BasisOfIsCompl
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FramesCommonStabiliserEqPairingMatrixStabiliser
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SelfDualLatticeUnipotentTranslateStandard
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDoubleCosetTermBasicFacts
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermInvariantsIndependentOfWitnesses
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramesStabilizerActsOnTerms
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramesComplementUnitaryActsOnTerms
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermExponentsNonnegAndDefectGroupBound
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsGluingHomomorphismDefectGroup
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitEntries
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralOfMulVec
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HmUnit
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalExtend
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsIntegralOfQuad
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.HL.StdPlace NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

noncomputable section

namespace GlobalTheory.HL.UnimodSplit

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

omit [IsNonarchimedeanLocalField F] [CharZero F] in

/- English proof (translation)
Establish `h1 : Matrix.vecMul z Hm = 0`. Use function extensionality and compare the values at `j`. Use `hz (Pi.single j 1)` as an intermediate fact. Simplify using `only [hf, Pi.single_apply, apply_ite (⇑L.cj), map_one, map_zero, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at this`. Simplify `this` using `[Matrix.vecMul, dotProduct]`.

Use `congrArg (fun u => Matrix.vecMul u Hm⁻¹) h1` as an intermediate fact. Simplify `this` using `[Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hd]`.
-/
theorem eq_zero_of_forall_hf (L : LocE F E) {n : ℕ} {Hm : Matrix (Fin n) (Fin n) E}
    (hd : IsUnit Hm.det) {z : Fin n → E} (hz : ∀ v, hf L Hm z v = 0) : z = 0 := by
  have h1 : Matrix.vecMul z Hm = 0 := by
    funext j
    have := hz (Pi.single j 1)
    simp only [hf, Pi.single_apply, apply_ite (⇑L.cj), map_one, map_zero, mul_ite, mul_one,
      mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at this
    simpa [Matrix.vecMul, dotProduct] using this
  have := congrArg (fun u => Matrix.vecMul u Hm⁻¹) h1
  simpa [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hd] using this

omit [IsNonarchimedeanLocalField F] [CharZero F] in

/- English proof (translation)
Rewrite `hx`, the goal using `[L.O_def]`. Conclude with `hx.map ((L.cj : E →ₐ[F] E).restrictScalars 𝒪[F])`.
-/
theorem cj_mem (L : LocE F E) {x : E} (hx : x ∈ L.O) : L.cj x ∈ L.O := by
  rw [L.O_def] at hx ⊢
  exact hx.map ((L.cj : E →ₐ[F] E).restrictScalars 𝒪[F])

omit [IsNonarchimedeanLocalField F] [CharZero F] in
/- English proof (translation)
Simplify using `[hf, add_mul, Finset.sum_add_distrib]`.
-/
theorem hf_add_left (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (x x' y : Fin n → E) :
    hf L Hm (x + x') y = hf L Hm x y + hf L Hm x' y := by
  simp [hf, add_mul, Finset.sum_add_distrib]

omit [IsNonarchimedeanLocalField F] [CharZero F] in
/- English proof (translation)
Simplify using `[hf, mul_add, Finset.sum_add_distrib]`.
-/
theorem hf_add_right (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (x y y' : Fin n → E) :
    hf L Hm x (y + y') = hf L Hm x y + hf L Hm x y' := by
  simp [hf, mul_add, Finset.sum_add_distrib]

omit [IsNonarchimedeanLocalField F] [CharZero F] in
/- English proof (translation)
Rewrite using `[FrameBasic.hf_conj L S.herm.1 x, UnimodTerm.hf_sum_left S, map_sum]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, ← FrameBasic.hf_conj L S.herm.1 x (g l)]`.
-/
theorem hf_sum_right {L : LocE F E} {r k : ℕ} (S : Frames L r k) {ι : Type} [Fintype ι] (x : S.V)
    (c : ι → E) (g : ι → S.V) :
    hf L S.Hm x (∑ l, c l • g l) = ∑ l, hf L S.Hm x (g l) * L.cj (c l) := by
  rw [FrameBasic.hf_conj L S.herm.1 x, UnimodTerm.hf_sum_left S, map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [map_mul, ← FrameBasic.hf_conj L S.herm.1 x (g l)]

/- English proof (translation)
Introduce `F _ _ _ _ _ E _ _ _ L r k S d Λ hT ha`. Take `⟨hSD, hW, hM, -⟩` from `TermBasic.term_basic L r k S d Λ hT`. Take `⟨-, hc, -⟩` from `FrameBasic.main L r k S`. Take `⟨-, -, -, hW0, -, b, hbli, hb⟩` from `Gluing.main L r k S d Λ hT`. Establish `hMΛ : ∀ m ∈ S.M d Λ, m ∈ Λ` using `fun m h => (hM h).1`.

Establish `hMME : ∀ m ∈ S.M d Λ, m ∈ S.ME` using `fun m h => (hM h).2`. Establish `hbL : ∀ w, w ∈ Submodule.span L.O (Set.range b) ↔ w ∈ S.complementLatticeOfDatum d` using `fun w => by`. Rewrite using `[hb]`. Both sides reduce to the same expression. Establish `hbW : ∀ i, b i ∈ S.W0` using `fun i => ((hbL _).1 (Submodule.subset_span ⟨i, rfl⟩)).1`.

Establish `hspan : ∀ w ∈ S.W0, (w ∈ Λ ↔ w ∈ Submodule.span L.O (Set.range b))`. Introduce `w hw`. Rewrite using `[hbL]`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Conclude with `((hW0 w hw).1 h).1`. Introduce `h`. Conclude with `(UnimodTerm.mem_iff_graph S hT ha hw).2 h.2.2.2`. Establish `hdec : ∀ x, ∃ m ∈ S.ME, ∃ w ∈ S.W0, x = m + w`. Introduce `x`.

Establish `hx : x ∈ S.ME ⊔ S.W0` using `by rw [hc.sup_eq_top]; trivial`. Take `⟨m, hm, w, hw, h⟩` from `Submodule.mem_sup.1 hx`. Conclude with `⟨m, hm, w, hw, h.symm⟩`. Establish `hΛ : Λ = S.M d Λ ⊔ Submodule.span L.O (Set.range b)`. Apply `le_antisymm` to reduce the goal to its premises.

Introduce `x hx`. Take `⟨m, hm, w, hw, rfl⟩` from `hdec x`. Establish `h1 : m ∈ S.M d Λ` using `UnimodTerm.proj_mem S hT ha hx hm (by simpa using hw)`. Establish `h2 : w ∈ Λ` using `by simpa using Λ.sub_mem hx (hMΛ m h1)`. Conclude with `Submodule.mem_sup.2 ⟨m, h1, w, (hspan w hw).1 h2, rfl⟩`.

Use `sup_le (fun m h => hMΛ m h) (fun w h => ?_)` and prove the remaining obligations. Conclude with `(hspan w ((hbL w).1 h).1).2 h`. Establish `hbΛ : ∀ i, b i ∈ Λ` using `fun i => (hspan _ (hbW i)).2 (Submodule.subset_span ⟨i, rfl⟩)`. Establish `hG : ∀ i j, hf L S.Hm (b i) (b j) ∈ L.O` using `fun i j => (hSD.2 (b j)).2 (hbΛ j) (b i) (hbΛ i)`. Establish `hYW : Submodule.span E (Set.range b) ≤ S.W0` using `Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hbW i)`.

Establish `hOY : ∀ w ∈ Submodule.span L.O (Set.range b), w ∈ Submodule.span E (Set.range b)` using `fun w h => Submodule.span_le_restrictScalars L.O E (Set.range b) h`. Establish `hWY : S.W0 ≤ Submodule.span E (Set.range b)`. Establish `htop : (⊤ : Submodule E S.V) ≤ S.ME ⊔ Submodule.span E (Set.range b)`. Rewrite using `[← hSD.1.2, Submodule.span_le]`. Introduce `x hx`.

Establish `hx' : x ∈ S.M d Λ ⊔ Submodule.span L.O (Set.range b)` using `by rw [← hΛ]; exact hx`. Take `⟨m, hm, w, hw, rfl⟩` from `Submodule.mem_sup.1 hx'`. Conclude with `Submodule.mem_sup.2 ⟨m, hMME m hm, w, hOY w hw, rfl⟩`. Introduce `w hw`. Take `⟨m, hm, y, hy, rfl⟩` from `Submodule.mem_sup.1 (htop (Submodule.mem_top (x := w)))`.

Establish `hm0 : m ∈ S.ME ⊓ S.W0` using `⟨hm, by simpa using S.W0.sub_mem hw (hYW hy)⟩`. Rewrite `hm0` using `[hc.inf_eq_bot, Submodule.mem_bot]`. Rewrite using `[hm0, zero_add]`. Conclude with `hy`. Establish `hzero : ∀ z ∈ S.W0, (∀ j, hf L S.Hm z (b j) = 0) → z = 0`.

Introduce `z hz hzb`. Apply `eq_zero_of_forall_hf L S.herm.2` to reduce the goal to its premises. Introduce `v`. Take `⟨m, hm, w, hw, rfl⟩` from `hdec v`. Establish `e1 : hf L S.Hm z m = 0` using `hz m hm`.

Establish `e2 : hf L S.Hm z w = 0`. Take `⟨c, rfl⟩` from `(Submodule.mem_span_range_iff_exists_fun E).1 (hWY hw)`. Rewrite using `[hf_sum_right S]`. Simplify using `[hzb]`. Rewrite using `[hf_add_right, e1, e2, add_zero]`.

Use `set Gb : Matrix (Fin (k - 1)) (Fin (k - 1)) E := Matrix.of fun i j => hf L S.Hm (b i) (b j) with hGb`. Establish `: Module.Finite F E` using `Module.finite_of_finrank_pos (by rw [L.rank]; norm_num)`. Establish `: IsArtinianRing E` using `IsArtinianRing.of_finite F E`. Establish `hunit : IsUnit Gb`. Rewrite using `[← Matrix.vecMul_surjective_iff_isUnit]`.

Establish `hinj : Function.Injective Gb.vecMulLinear`. Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce `c hc`. Establish `hz : ∑ i, c i • b i = 0`. Apply `hzero _ (S.W0.sum_mem fun i _ => S.W0.smul_mem _ (hbW i))` to reduce the goal to its premises.

Introduce `j`. Use `congrFun hc j` as an intermediate fact. Simplify using `only [Matrix.vecMulLinear_apply, Matrix.vecMul, dotProduct, Pi.zero_apply, hGb, Matrix.of_apply] at this`. Rewrite using `[UnimodTerm.hf_sum_left S, ← this]`. Conclude with `Finset.sum_congr rfl fun i _ => mul_comm _ _`.

Use function extensionality and compare the values at `i`. Conclude with `Fintype.linearIndependent_iff.1 hbli c hz i`. Conclude with `IsArtinian.surjective_of_injective_endomorphism Gb.vecMulLinear hinj`. Establish `hdet` using `(Matrix.isUnit_iff_isUnit_det Gb).1 hunit`. Establish `hGP : Gb * Gb⁻¹ = 1` using `Matrix.mul_nonsing_inv Gb hdet`.

Use `⟨b, hbW, hΛ, hG, Gb⁻¹, ?_, hGP⟩` and prove the remaining obligations. Introduce `l j`. Use `set y : S.V := ∑ l', L.cj (Gb⁻¹ l' j) • b l' with hy`. Establish `hyb : ∀ i, hf L S.Hm (b i) y = if i = j then 1 else 0`. Introduce `i`.

Rewrite using `[hy, hf_sum_right S]`. Use `congrFun (congrFun hGP i) j` as an intermediate fact. Simplify using `only [Matrix.mul_apply, Matrix.one_apply, hGb, Matrix.of_apply] at this`. Rewrite using `[← this]`. Conclude with `Finset.sum_congr rfl fun l' _ => by rw [L.cj_cj]`.

Establish `hyW : y ∈ S.W0` using `S.W0.sum_mem fun l' _ => S.W0.smul_mem _ (hbW l')`. Establish `hyΛ : y ∈ Λ`. Use `(hSD.2 y).1 fun x hx => ?_` and prove the remaining obligations. Establish `hx' : x ∈ S.M d Λ ⊔ Submodule.span L.O (Set.range b)` using `by rw [← hΛ]; exact hx`. Take `⟨m, hm, w, hw, rfl⟩` from `Submodule.mem_sup.1 hx'`.

Take `⟨o, rfl⟩` from `(Submodule.mem_span_range_iff_exists_fun L.O).1 hw`. Establish `e1 : hf L S.Hm m y = 0`. Rewrite using `[FrameBasic.hf_conj L S.herm.1 m y, hyW m (hMME m hm), map_zero]`. Establish `e2 : ∑ i, o i • b i = ∑ i, (o i : E) • b i` using `rfl`. Rewrite using `[hf_add_left, e1, zero_add, e2, UnimodTerm.hf_sum_left S]`.

Simplify using `only [hyb, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]`. Conclude with `(o j).2`. Take `⟨Q, hQ⟩` from `(Submodule.mem_span_range_iff_exists_fun L.O).1 ((hspan y hyW).1 hyΛ)`. Establish `hQ' : ∑ i, (Q i : E) • b i = y` using `hQ`. Establish `hcoef : L.cj (Gb⁻¹ l j) = (Q l : E)`.

Establish `h0` using `Fintype.linearIndependent_iff.1 hbli (fun l' => L.cj (Gb⁻¹ l' j) - (Q l' : E)) (by`. Simplify using `only [sub_smul, Finset.sum_sub_distrib]`. Rewrite using `[← hy, hQ', sub_self])`. Conclude with `sub_eq_zero.1 (h0 l)`. Establish `h1` using `cj_mem L (Q l).2`.

Rewrite `h1` using `[← hcoef, L.cj_cj]`. Conclude with `h1`.
-/
theorem main : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → S.a = 0 → ∃ b : Fin (k - 1) → S.V, (∀ i, b i ∈ S.W0) ∧ Λ = S.M d Λ ⊔ Submodule.span L.O (Set.range b) ∧ (∀ i j, hf L S.Hm (b i) (b j) ∈ L.O) ∧ ∃ P : Matrix (Fin (k - 1)) (Fin (k - 1)) E, IsIntM L P ∧ (Matrix.of fun i j => hf L S.Hm (b i) (b j)) * P = 1 := by
  intro F _ _ _ _ _ E _ _ _ L r k S d Λ hT ha
  obtain ⟨hSD, hW, hM, -⟩ := TermBasic.term_basic L r k S d Λ hT
  obtain ⟨-, hc, -⟩ := FrameBasic.main L r k S
  obtain ⟨-, -, -, hW0, -, b, hbli, hb⟩ := Gluing.main L r k S d Λ hT
  have hMΛ : ∀ m ∈ S.M d Λ, m ∈ Λ := fun m h => (hM h).1
  have hMME : ∀ m ∈ S.M d Λ, m ∈ S.ME := fun m h => (hM h).2
  have hbL : ∀ w, w ∈ Submodule.span L.O (Set.range b) ↔ w ∈ S.complementLatticeOfDatum d := fun w => by
    rw [hb]; rfl
  have hbW : ∀ i, b i ∈ S.W0 := fun i => ((hbL _).1 (Submodule.subset_span ⟨i, rfl⟩)).1
  have hspan : ∀ w ∈ S.W0, (w ∈ Λ ↔ w ∈ Submodule.span L.O (Set.range b)) := by
    intro w hw
    rw [hbL]
    constructor
    · intro h; exact ((hW0 w hw).1 h).1
    · intro h; exact (UnimodTerm.mem_iff_graph S hT ha hw).2 h.2.2.2
  have hdec : ∀ x, ∃ m ∈ S.ME, ∃ w ∈ S.W0, x = m + w := by
    intro x
    have hx : x ∈ S.ME ⊔ S.W0 := by rw [hc.sup_eq_top]; trivial
    obtain ⟨m, hm, w, hw, h⟩ := Submodule.mem_sup.1 hx
    exact ⟨m, hm, w, hw, h.symm⟩
  have hΛ : Λ = S.M d Λ ⊔ Submodule.span L.O (Set.range b) := by
    apply le_antisymm
    · intro x hx
      obtain ⟨m, hm, w, hw, rfl⟩ := hdec x
      have h1 : m ∈ S.M d Λ := UnimodTerm.proj_mem S hT ha hx hm (by simpa using hw)
      have h2 : w ∈ Λ := by simpa using Λ.sub_mem hx (hMΛ m h1)
      exact Submodule.mem_sup.2 ⟨m, h1, w, (hspan w hw).1 h2, rfl⟩
    · refine sup_le (fun m h => hMΛ m h) (fun w h => ?_)
      exact (hspan w ((hbL w).1 h).1).2 h
  have hbΛ : ∀ i, b i ∈ Λ := fun i => (hspan _ (hbW i)).2 (Submodule.subset_span ⟨i, rfl⟩)
  have hG : ∀ i j, hf L S.Hm (b i) (b j) ∈ L.O := fun i j => (hSD.2 (b j)).2 (hbΛ j) (b i) (hbΛ i)
  have hYW : Submodule.span E (Set.range b) ≤ S.W0 :=
    Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hbW i)
  have hOY : ∀ w ∈ Submodule.span L.O (Set.range b), w ∈ Submodule.span E (Set.range b) :=
    fun w h => Submodule.span_le_restrictScalars L.O E (Set.range b) h
  have hWY : S.W0 ≤ Submodule.span E (Set.range b) := by
    have htop : (⊤ : Submodule E S.V) ≤ S.ME ⊔ Submodule.span E (Set.range b) := by
      rw [← hSD.1.2, Submodule.span_le]
      intro x hx
      have hx' : x ∈ S.M d Λ ⊔ Submodule.span L.O (Set.range b) := by rw [← hΛ]; exact hx
      obtain ⟨m, hm, w, hw, rfl⟩ := Submodule.mem_sup.1 hx'
      exact Submodule.mem_sup.2 ⟨m, hMME m hm, w, hOY w hw, rfl⟩
    intro w hw
    obtain ⟨m, hm, y, hy, rfl⟩ := Submodule.mem_sup.1 (htop (Submodule.mem_top (x := w)))
    have hm0 : m ∈ S.ME ⊓ S.W0 := ⟨hm, by simpa using S.W0.sub_mem hw (hYW hy)⟩
    rw [hc.inf_eq_bot, Submodule.mem_bot] at hm0
    rw [hm0, zero_add]; exact hy
  have hzero : ∀ z ∈ S.W0, (∀ j, hf L S.Hm z (b j) = 0) → z = 0 := by
    intro z hz hzb
    apply eq_zero_of_forall_hf L S.herm.2
    intro v
    obtain ⟨m, hm, w, hw, rfl⟩ := hdec v
    have e1 : hf L S.Hm z m = 0 := hz m hm
    have e2 : hf L S.Hm z w = 0 := by
      obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 (hWY hw)
      rw [hf_sum_right S]
      simp [hzb]
    rw [hf_add_right, e1, e2, add_zero]
  set Gb : Matrix (Fin (k - 1)) (Fin (k - 1)) E := Matrix.of fun i j => hf L S.Hm (b i) (b j) with hGb
  have : Module.Finite F E := Module.finite_of_finrank_pos (by rw [L.rank]; norm_num)
  have : IsArtinianRing E := IsArtinianRing.of_finite F E
  have hunit : IsUnit Gb := by
    rw [← Matrix.vecMul_surjective_iff_isUnit]
    have hinj : Function.Injective Gb.vecMulLinear := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro c hc
      have hz : ∑ i, c i • b i = 0 := by
        apply hzero _ (S.W0.sum_mem fun i _ => S.W0.smul_mem _ (hbW i))
        intro j
        have := congrFun hc j
        simp only [Matrix.vecMulLinear_apply, Matrix.vecMul, dotProduct, Pi.zero_apply, hGb,
          Matrix.of_apply] at this
        rw [UnimodTerm.hf_sum_left S, ← this]
        exact Finset.sum_congr rfl fun i _ => mul_comm _ _
      funext i
      exact Fintype.linearIndependent_iff.1 hbli c hz i
    exact IsArtinian.surjective_of_injective_endomorphism Gb.vecMulLinear hinj
  have hdet := (Matrix.isUnit_iff_isUnit_det Gb).1 hunit
  have hGP : Gb * Gb⁻¹ = 1 := Matrix.mul_nonsing_inv Gb hdet
  refine ⟨b, hbW, hΛ, hG, Gb⁻¹, ?_, hGP⟩
  intro l j
  set y : S.V := ∑ l', L.cj (Gb⁻¹ l' j) • b l' with hy
  have hyb : ∀ i, hf L S.Hm (b i) y = if i = j then 1 else 0 := by
    intro i
    rw [hy, hf_sum_right S]
    have := congrFun (congrFun hGP i) j
    simp only [Matrix.mul_apply, Matrix.one_apply, hGb, Matrix.of_apply] at this
    rw [← this]
    exact Finset.sum_congr rfl fun l' _ => by rw [L.cj_cj]
  have hyW : y ∈ S.W0 := S.W0.sum_mem fun l' _ => S.W0.smul_mem _ (hbW l')
  have hyΛ : y ∈ Λ := by
    refine (hSD.2 y).1 fun x hx => ?_
    have hx' : x ∈ S.M d Λ ⊔ Submodule.span L.O (Set.range b) := by rw [← hΛ]; exact hx
    obtain ⟨m, hm, w, hw, rfl⟩ := Submodule.mem_sup.1 hx'
    obtain ⟨o, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun L.O).1 hw
    have e1 : hf L S.Hm m y = 0 := by
      rw [FrameBasic.hf_conj L S.herm.1 m y, hyW m (hMME m hm), map_zero]
    have e2 : ∑ i, o i • b i = ∑ i, (o i : E) • b i := rfl
    rw [hf_add_left, e1, zero_add, e2, UnimodTerm.hf_sum_left S]
    simp only [hyb, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    exact (o j).2
  obtain ⟨Q, hQ⟩ := (Submodule.mem_span_range_iff_exists_fun L.O).1 ((hspan y hyW).1 hyΛ)
  have hQ' : ∑ i, (Q i : E) • b i = y := hQ
  have hcoef : L.cj (Gb⁻¹ l j) = (Q l : E) := by
    have h0 := Fintype.linearIndependent_iff.1 hbli (fun l' => L.cj (Gb⁻¹ l' j) - (Q l' : E)) (by
      simp only [sub_smul, Finset.sum_sub_distrib]
      rw [← hy, hQ', sub_self])
    exact sub_eq_zero.1 (h0 l)
  have h1 := cj_mem L (Q l).2
  rw [← hcoef, L.cj_cj] at h1
  exact h1

end GlobalTheory.HL.UnimodSplit
