import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TwTransAlt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DecoStabTrivial
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnSpacesStandardInFrameCoords
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPointOfLastCoordinateDilationOnePrime
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FiniteAdeleIdempotentOfFMulSelf
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryClassRepresentativesBijective
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFiniteAdeleProjectionIntegralReduction
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StandardPairFrameCoordinatesIntegralAndFunctiona
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdForm.RowModPrime

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Take `⟨e, he⟩` from `Q.exists_hasVal_one`. Take `⟨y₀, -, sc, hsc, h1⟩` from `(hQ e 1).1 he`. Establish `hsc0 : residue 𝒪[k] sc ≠ 0`. Introduce `h`. Rewrite `h1` using `[map_mul, h, zero_mul]`.

Conclude with `one_ne_zero h1`. Set `y : Fin n → 𝒪[k]` to `Pi.single m 1`. Establish `hbx : b *ᵥ (b' *ᵥ Pi.single m 1) = Pi.single m 1`. Rewrite using `[Matrix.mulVec_mulVec, hbb', Matrix.one_mulVec]`. Establish `hx : Q.HasVal (b' *ᵥ Pi.single m 1) (residue 𝒪[k] (sc * y r₀))`.

Use `(hQ _ _).2 ⟨y, fun r => ?_, sc, hsc, rfl⟩` and prove the remaining obligations. Rewrite using `[hbx]`. Simplify using `only [y, Pi.single_apply]`. Apply the tactic sequence `split_ifs <;> simp`. Establish `hx2 : (g • Q).HasVal (b' *ᵥ Pi.single m 1) ((s : 𝓀[k]) * residue 𝒪[k] (sc * y r₀))`.

Rewrite using `[hg, GlobalTheory.LatPair.Pair.dia_hasVal, Units.inv_mul_cancel_left]`. Conclude with `hx`. Establish `hx3` using `GlobalTheory.LatPair.Pair.smul_hasVal.1 hx2`. Take `⟨y', hy', sc', hsc', h3⟩` from `(hQ _ _).1 hx3`. Establish `hss : sc' = sc` using `Subtype.ext (hsc'.trans hsc.symm)`.

Rewrite `h3` using `[hss]`. Establish `hM : (b *ᵥ (g⁻¹ • (b' *ᵥ Pi.single m 1))) r₀ = (b * (g⁻¹).val * b') r₀ m`. Express the relevant statement in the definitionally equal form `(b *ᵥ ((g⁻¹).val *ᵥ (b' *ᵥ Pi.single m 1))) r₀ = _`. Rewrite using `[Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_single_one]`. Both sides reduce to the same expression.

Use `⟨y' r₀, (hy' r₀).trans hM, ?_⟩` and prove the remaining obligations. Rewrite `h3` using `[map_mul, map_mul]`. Establish `h4 : residue 𝒪[k] sc * residue 𝒪[k] (y' r₀) = residue 𝒪[k] sc * ((s : 𝓀[k]) * residue 𝒪[k] (y r₀))`. Rewrite using `[← h3]`. Expand and normalize the polynomial expressions, which then agree.

Establish `h5` using `mul_left_cancel₀ hsc0 h4`. Rewrite using `[h5]`. Simplify using `only [y, Pi.single_apply]`. Distinguish the cases in `h : m = r₀`. Substitute `h` using the available equality.

Simplify using the standard rewrite rules. Rewrite using `[if_neg (Ne.symm h), if_neg h]`. Simplify using the standard rewrite rules.
-/
theorem row_of_smul_eq {n : ℕ} (Q : GlobalTheory.LatPair.Pair k (Fin n)) (b b' : Matrix (Fin n) (Fin n) k) (hbb' : b * b' = 1)
    (c : k) (r₀ : Fin n)
    (hQ : ∀ (x : Fin n → k) (a : 𝓀[k]), Q.HasVal x a ↔ ∃ y : Fin n → 𝒪[k], (∀ r, (y r : k) = (b *ᵥ x) r) ∧
      ∃ s : 𝒪[k], (s : k) = c ∧ a = residue 𝒪[k] (s * y r₀))
    (g : GL (Fin n) k) (s : 𝓀[k]ˣ) (hg : g • Q = s • Q) (m : Fin n) :
    ∃ t : 𝒪[k], (t : k) = (b * (g⁻¹).val * b') r₀ m ∧ residue 𝒪[k] t = if m = r₀ then (s : 𝓀[k]) else 0 := by
  obtain ⟨e, he⟩ := Q.exists_hasVal_one
  obtain ⟨y₀, -, sc, hsc, h1⟩ := (hQ e 1).1 he
  have hsc0 : residue 𝒪[k] sc ≠ 0 := by
    intro h
    rw [map_mul, h, zero_mul] at h1
    exact one_ne_zero h1
  let y : Fin n → 𝒪[k] := Pi.single m 1
  have hbx : b *ᵥ (b' *ᵥ Pi.single m 1) = Pi.single m 1 := by
    rw [Matrix.mulVec_mulVec, hbb', Matrix.one_mulVec]
  have hx : Q.HasVal (b' *ᵥ Pi.single m 1) (residue 𝒪[k] (sc * y r₀)) := by
    refine (hQ _ _).2 ⟨y, fun r => ?_, sc, hsc, rfl⟩
    rw [hbx]
    simp only [y, Pi.single_apply]
    split_ifs <;> simp
  have hx2 : (g • Q).HasVal (b' *ᵥ Pi.single m 1) ((s : 𝓀[k]) * residue 𝒪[k] (sc * y r₀)) := by
    rw [hg, GlobalTheory.LatPair.Pair.dia_hasVal, Units.inv_mul_cancel_left]
    exact hx
  have hx3 := GlobalTheory.LatPair.Pair.smul_hasVal.1 hx2
  obtain ⟨y', hy', sc', hsc', h3⟩ := (hQ _ _).1 hx3
  have hss : sc' = sc := Subtype.ext (hsc'.trans hsc.symm)
  rw [hss] at h3
  have hM : (b *ᵥ (g⁻¹ • (b' *ᵥ Pi.single m 1))) r₀ = (b * (g⁻¹).val * b') r₀ m := by
    change (b *ᵥ ((g⁻¹).val *ᵥ (b' *ᵥ Pi.single m 1))) r₀ = _
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_single_one]
    rfl
  refine ⟨y' r₀, (hy' r₀).trans hM, ?_⟩
  rw [map_mul, map_mul] at h3
  have h4 : residue 𝒪[k] sc * residue 𝒪[k] (y' r₀) = residue 𝒪[k] sc * ((s : 𝓀[k]) * residue 𝒪[k] (y r₀)) := by
    rw [← h3]; ring
  have h5 := mul_left_cancel₀ hsc0 h4
  rw [h5]
  simp only [y, Pi.single_apply]
  by_cases h : m = r₀
  · subst h
    simp
  · rw [if_neg (Ne.symm h), if_neg h]
    simp

end GlobalTheory.AdForm.RowModPrime

namespace GlobalTheory.AdForm.RowModPrime

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Take `⟨x, hx0⟩` from `GlobalTheory.FunObj.Comparison₂.exists_approx (D := D) P.ne_bot a`. Establish `hx : a - Formalism.L2.DIV.oToS D.host.F D.host.E x ∈ Formalism.L2.DIV.idS D.host.F P.asIdeal` using `hx0`. Establish `h1 : Formalism.L2.DIV.resS D.host.F P a = Ideal.Quotient.mk P.asIdeal x`. Rewrite using `[← Formalism.L2.DIV.resS_oToS (F := D.host.F) P x, ← sub_eq_zero, ← map_sub]`. Conclude with `GlobalTheory.FinPl.SplitPt.resS_eq_zero_of_mem hx`.

Establish `h2` using `q.val_lt_of_mem_idS he hx`. Establish `e1 : ((Formalism.L2.DIV.oToS D.host.F D.host.E x : Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) = toEAf D (incA D (x : D.host.E))` using `rfl`. Establish `e2 : ((a - Formalism.L2.DIV.oToS D.host.F D.host.E x : Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) = (a : EAf D) - ((Formalism.L2.DIV.oToS D.host.F D.host.E x : Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D)` using `rfl`. Rewrite `h2` using `[e2, map_sub, e1, GlobalTheory.FinPl.SplitPt.prF_toEAf, ← ht]`. Establish `hw : q.pr (incA D (x : D.host.E)) ∈ 𝒪[k]`.

Establish `ht1 : valuation k (t : k) ≤ 1` using `(Valuation.mem_integer_iff _ _).1 t.2`. Establish `e3 : q.pr (incA D (x : D.host.E)) = (t : k) - ((t : k) - q.pr (incA D (x : D.host.E)))` using `by ring`. Rewrite using `[Valuation.mem_integer_iff, e3]`. Conclude with `(Valuation.map_sub _ _ _).trans (max_le ht1 h2.le)`. Set `tw : 𝒪[k]` to `⟨_, hw⟩`.

Establish `h3 : residue 𝒪[k] t = residue 𝒪[k] tw`. Rewrite using `[← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]`. Conclude with `(IsLocalRing.mem_maximalIdeal _).2 (Valuation.Integer.not_isUnit_iff_valuation_lt_one.2 (by simpa [tw] using h2))`. Rewrite using `[h1, h3, hρ x tw rfl]`.
-/
theorem resS_eq_rho {D : D7} (q : GlobalTheory.FinPl.SplitPt D k) {P : HeightOneSpectrum (𝓞 D.host.E)}
    (he : Formalism.L2.NTheta.IsIdemAt q.e P) (ρ : 𝓀[k] ≃+* (𝓞 D.host.E ⧸ P.asIdeal))
    (hρ : ∀ (x : 𝓞 D.host.E) (t : 𝒪[k]), (t : k) = q.pr (incA D (x : D.host.E)) →
      ρ (residue 𝒪[k] t) = Ideal.Quotient.mk P.asIdeal x)
    (a : Formalism.L2.Herm.intAf D.host.F D.host.E) (t : 𝒪[k]) (ht : (t : k) = q.prF he a.1) :
    Formalism.L2.DIV.resS D.host.F P a = ρ (residue 𝒪[k] t) := by
  obtain ⟨x, hx0⟩ := GlobalTheory.FunObj.Comparison₂.exists_approx (D := D) P.ne_bot a
  have hx : a - Formalism.L2.DIV.oToS D.host.F D.host.E x ∈ Formalism.L2.DIV.idS D.host.F P.asIdeal := hx0
  have h1 : Formalism.L2.DIV.resS D.host.F P a = Ideal.Quotient.mk P.asIdeal x := by
    rw [← Formalism.L2.DIV.resS_oToS (F := D.host.F) P x, ← sub_eq_zero, ← map_sub]
    exact GlobalTheory.FinPl.SplitPt.resS_eq_zero_of_mem hx
  have h2 := q.val_lt_of_mem_idS he hx
  have e1 : ((Formalism.L2.DIV.oToS D.host.F D.host.E x : Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) =
      toEAf D (incA D (x : D.host.E)) := rfl
  have e2 : ((a - Formalism.L2.DIV.oToS D.host.F D.host.E x : Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) =
      (a : EAf D) - ((Formalism.L2.DIV.oToS D.host.F D.host.E x : Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) := rfl
  rw [e2, map_sub, e1, GlobalTheory.FinPl.SplitPt.prF_toEAf, ← ht] at h2
  have hw : q.pr (incA D (x : D.host.E)) ∈ 𝒪[k] := by
    have ht1 : valuation k (t : k) ≤ 1 := (Valuation.mem_integer_iff _ _).1 t.2
    have e3 : q.pr (incA D (x : D.host.E)) = (t : k) - ((t : k) - q.pr (incA D (x : D.host.E))) := by ring
    rw [Valuation.mem_integer_iff, e3]
    exact (Valuation.map_sub _ _ _).trans (max_le ht1 h2.le)
  let tw : 𝒪[k] := ⟨_, hw⟩
  have h3 : residue 𝒪[k] t = residue 𝒪[k] tw := by
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
    exact (IsLocalRing.mem_maximalIdeal _).2 (Valuation.Integer.not_isUnit_iff_valuation_lt_one.2 (by simpa [tw] using h2))
  rw [h1, h3, hρ x tw rfl]

end GlobalTheory.AdForm.RowModPrime

open GlobalTheory.AdForm.RowModPrime in

/- English proof (translation)
Introduce `B X I hOk hP l Z u a k _ _ _ _ ι p β Q L hStd j hj i v hId ρ hρ g s hg δ hδ hint r r' hr`. Establish `hn : ((I.rec7 l Z).sp.X j).rank = B.R.N j` using `rankN (I.rec7 l Z) j hj`. Set `e : Fin ((I.rec7 l Z).sp.X j).rank ≃ Fin (B.R.N j)` to `finCongr hn`. Set `f : Matrix (Fin (B.R.N j)) (Fin (B.R.N j)) (EAf (I.rec7 l Z)) →+* Matrix (Fin (B.R.N j)) (Fin (B.R.N j)) k` to `((p i).prF hId).mapMatrix`. Establish `hδm : f δ.1 = Matrix.reindex e e ((β j i).b * g.val * (β j i).b')`.

Rewrite using `[hδ, ← (β j i).gl_mat g]`. Use extensionality with `x y`. Conclude with `GlobalTheory.FinPl.SplitPt.prF_toEAf (p i) hId _`. Establish `hY : Matrix.reindex e e ((β j i).b * g.val * (β j i).b') * Matrix.reindex e e ((β j i).b * (g⁻¹).val * (β j i).b') = 1`. Rewrite using `[Matrix.reindex_apply, Matrix.reindex_apply, Matrix.submatrix_mul_equiv]`.

Establish `: (β j i).b * g.val * (β j i).b' * ((β j i).b * (g⁻¹).val * (β j i).b') = 1`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[this, Matrix.submatrix_one_equiv]`. Establish `h1 : ((δ⁻¹).1 : Matrix (Fin (B.R.N j)) (Fin (B.R.N j)) (EAf (I.rec7 l Z))) * δ.1 = 1`. Rewrite using `[← Units.val_mul, inv_mul_cancel, Units.val_one]`.

Establish `hX : f (δ⁻¹).1 * f δ.1 = 1` using `(map_mul f _ _).symm.trans ((congrArg f h1).trans (map_one f))`. Establish `hA : f (δ⁻¹).1 = Matrix.reindex e e ((β j i).b * (g⁻¹).val * (β j i).b')`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hδm, hY, Matrix.mul_one]`. Use `_ = _ := by rw [← Matrix.mul_assoc, hX, Matrix.one_mul]`.

Establish `hA' : (p i).prF hId ((δ⁻¹).1 r r') = ((β j i).b * (g⁻¹).val * (β j i).b') (e.symm r) (e.symm r')` using `congrFun (congrFun hA r) r'`. Establish `hr0 : (e.symm r).1 + 1 = ((I.rec7 l Z).sp.X j).rank` using `by show r.1 + 1 = _`. Rewrite using `[hr]`. Conclude with `hn.symm`. Establish `hQ` using `GlobalTheory.AdForm.stdT_pair_coords I l Z u k ι p β Q L hStd j hj i (e.symm r) hr0`.

Take `⟨t, ht, hres⟩` from `row_of_smul_eq (Q j i) (β j i).b (β j i).b' (β j i).bb' _ (e.symm r) hQ g s hg (e.symm r')`. Establish `hmem` using `hint r r'`. Establish `h` using `GlobalTheory.Mem.Col2.PtExist.hasRes_redA v.1 hmem`. Establish `hr1 : Formalism.L2.Col.redA v.1 ((δ⁻¹).1 r r') = ρ (residue 𝒪[k] t)` using `(Formalism.L2.Col.redA_int v.1 hmem).trans (resS_eq_rho (p i) hId ρ hρ ⟨_, hmem⟩ t (ht.trans hA'.symm))`. Rewrite `h` using `[hr1, hres]`.

Use `h using 2` and compare the differences between its conclusion and the goal. Distinguish the cases in `h' : r' = r`. Substitute `h'` using the available equality. Simplify using the standard rewrite rules. Rewrite using `[if_neg h', if_neg (fun h'' => h' (e.symm.injective h'')), map_zero]`.
-/
theorem GlobalTheory.AdForm.lastRow_inv_frame : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type)
    (p : ι → SplitPt (I.rec7 l Z) k) (β : ∀ j i, Frame (p i) ((I.rec7 l Z).sp.X j) (Fin ((I.rec7 l Z).sp.X j).rank))
    (Q : ∀ j, ι → Pair k (Fin ((I.rec7 l Z).sp.X j).rank)) (L : ∀ j, Lat ((I.rec7 l Z).sp.X j)),
    StdT I l Z u p β Q L → ∀ j (hj : j ≤ B.R.m) (i : ι) (v : (I.atT l u a).vT), Formalism.L2.NTheta.IsIdemAt (p i).e v.1 → ∀ (ρ : 𝓀[k] ≃+* (𝓞 B.fields.E ⧸ v.1.asIdeal)), (∀ (x : 𝓞 B.fields.E) (t : 𝒪[k]), (t : k) = (p i).pr (incA (I.rec7 l Z) (x : B.fields.E)) → ρ (residue 𝒪[k] t) = Ideal.Quotient.mk v.1.asIdeal x) →
    ∀ (g : GL (Fin ((I.rec7 l Z).sp.X j).rank) k) (s : 𝓀[k]ˣ), g • Q j i = s • Q j i → ∀ δ : TC.GA B (B.R.N j), δ.1 = finM _ (rankN (I.rec7 l Z) j hj) ((β j i).gl g) →
      (∀ r r', (δ⁻¹).1 r r' ∈ Formalism.L2.DIV.RInt B.host.F B.host.E) →
      ∀ r r' : Fin (B.R.N j), r.1 + 1 = B.R.N j → HasRes v.1 (adAt B.host.F v.1 ((δ⁻¹).1 r r')) (if r' = r then ρ (s : 𝓀[k]) else 0) := by
  intro B X I hOk hP l Z u a k _ _ _ _ ι p β Q L hStd j hj i v hId ρ hρ g s hg δ hδ hint r r' hr
  have hn : ((I.rec7 l Z).sp.X j).rank = B.R.N j := rankN (I.rec7 l Z) j hj
  let e : Fin ((I.rec7 l Z).sp.X j).rank ≃ Fin (B.R.N j) := finCongr hn
  let f : Matrix (Fin (B.R.N j)) (Fin (B.R.N j)) (EAf (I.rec7 l Z)) →+* Matrix (Fin (B.R.N j)) (Fin (B.R.N j)) k :=
    ((p i).prF hId).mapMatrix
  have hδm : f δ.1 = Matrix.reindex e e ((β j i).b * g.val * (β j i).b') := by
    rw [hδ, ← (β j i).gl_mat g]
    ext x y
    exact GlobalTheory.FinPl.SplitPt.prF_toEAf (p i) hId _
  have hY : Matrix.reindex e e ((β j i).b * g.val * (β j i).b') * Matrix.reindex e e ((β j i).b * (g⁻¹).val * (β j i).b') = 1 := by
    rw [Matrix.reindex_apply, Matrix.reindex_apply, Matrix.submatrix_mul_equiv]
    have : (β j i).b * g.val * (β j i).b' * ((β j i).b * (g⁻¹).val * (β j i).b') = 1 := by
      calc (β j i).b * g.val * (β j i).b' * ((β j i).b * (g⁻¹).val * (β j i).b')
          = (β j i).b * (g.val * ((β j i).b' * (β j i).b) * (g⁻¹).val) * (β j i).b' := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [(β j i).b'b, Matrix.mul_one, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one, (β j i).bb']
    rw [this, Matrix.submatrix_one_equiv]
  have h1 : ((δ⁻¹).1 : Matrix (Fin (B.R.N j)) (Fin (B.R.N j)) (EAf (I.rec7 l Z))) * δ.1 = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hX : f (δ⁻¹).1 * f δ.1 = 1 :=
    (map_mul f _ _).symm.trans ((congrArg f h1).trans (map_one f))
  have hA : f (δ⁻¹).1 = Matrix.reindex e e ((β j i).b * (g⁻¹).val * (β j i).b') := by
    calc f (δ⁻¹).1 = f (δ⁻¹).1 * (f δ.1 * Matrix.reindex e e ((β j i).b * (g⁻¹).val * (β j i).b')) := by
          rw [hδm, hY, Matrix.mul_one]
      _ = _ := by rw [← Matrix.mul_assoc, hX, Matrix.one_mul]
  have hA' : (p i).prF hId ((δ⁻¹).1 r r') = ((β j i).b * (g⁻¹).val * (β j i).b') (e.symm r) (e.symm r') :=
    congrFun (congrFun hA r) r'
  have hr0 : (e.symm r).1 + 1 = ((I.rec7 l Z).sp.X j).rank := by
    show r.1 + 1 = _
    rw [hr]
    exact hn.symm
  have hQ := GlobalTheory.AdForm.stdT_pair_coords I l Z u k ι p β Q L hStd j hj i (e.symm r) hr0
  obtain ⟨t, ht, hres⟩ := row_of_smul_eq (Q j i) (β j i).b (β j i).b' (β j i).bb' _ (e.symm r) hQ g s hg (e.symm r')
  have hmem := hint r r'
  have h := GlobalTheory.Mem.Col2.PtExist.hasRes_redA v.1 hmem
  have hr1 : Formalism.L2.Col.redA v.1 ((δ⁻¹).1 r r') = ρ (residue 𝒪[k] t) :=
    (Formalism.L2.Col.redA_int v.1 hmem).trans (resS_eq_rho (p i) hId ρ hρ ⟨_, hmem⟩ t (ht.trans hA'.symm))
  rw [hr1, hres] at h
  convert h using 2
  by_cases h' : r' = r
  · subst h'; simp
  · rw [if_neg h', if_neg (fun h'' => h' (e.symm.injective h'')), map_zero]

end
