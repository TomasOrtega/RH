import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FockSpaces.ContinuousLoc
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKrdPlace

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KFock
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
def cmpW_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (w : InfinitePlace F) : AddSubgroup (Mx F E d.m d.n) where
  carrier := {X | d.cw w X = 0}
  zero_mem' := by
    show d.cw w 0 = 0
    exact Matrix.map_zero _ (map_zero _)
  add_mem' := by
    intro X Z hX hZ
    show d.cw w (X + Z) = 0
    have e : d.cw w (X + Z) = d.cw w X + d.cw w Z := Matrix.map_add _ (map_add _) X Z
    rw [e, show d.cw w X = 0 from hX, show d.cw w Z = 0 from hZ, add_zero]
  neg_mem' := by
    intro X hX
    show d.cw w (-X) = 0
    have e : d.cw w (-X) = -d.cw w X := Matrix.map_neg _ (map_neg _) X
    rw [e, show d.cw w X = 0 from hX, neg_zero]
def IntFact_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
  (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) (ν : Measure (Mx F E d.m d.n)), d.IsCov ν →
  ∃ (C : ℝ) (μ' : Measure (_root_.PositivityTheory.SiegelWeilFormula.KFock.cmpW_k d w)), 0 < C ∧ μ'.IsAddHaarMeasure ∧
    ∀ (f : (Fin d.m → Fin d.n → ℂ) → ℂ) (Ψ : Mx F E d.m d.n → ℂ),
      (∀ X Z, (∀ w', w' ≠ w → d.cw w' Z = 0) → finOne F • Z = 0 → Ψ (X + Z) = Ψ X) →
      ∫ X, R.tens w f Ψ X ∂ν = C * (∫ u, f u) * ∫ Z, Ψ Z.1 ∂μ'
section Split
variable (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F)
/- English proof (translation)
The claim follows from `Matrix.map_add _ (map_add _) X Z`.
-/
theorem cw_add'_k (X Z : Mx F E d.m d.n) : d.cw w (X + Z) = d.cw w X + d.cw w Z := Matrix.map_add _ (map_add _) X Z
/- English proof (translation)
The claim follows from `Matrix.map_sub _ (map_sub _) X Z`.
-/
theorem cw_sub'_k (X Z : Mx F E d.m d.n) : d.cw w (X - Z) = d.cw w X - d.cw w Z := Matrix.map_sub _ (map_sub _) X Z
/- English proof (translation)
Unfold `_root_.PositivityTheory.SiegelWeilFormula.RD_k.loc`. Rewrite using `[_root_.PositivityTheory.SiegelWeilFormula.KFock.cw_add'_k, Matrix.mul_add]`. Conclude with `Matrix.map_add _ (fun a b => star_add a b) _ _`.
-/
theorem loc_add'_k (X Z : Mx F E d.m d.n) : R.loc w (X + Z) = R.loc w X + R.loc w Z := by
  unfold _root_.PositivityTheory.SiegelWeilFormula.RD_k.loc
  rw [_root_.PositivityTheory.SiegelWeilFormula.KFock.cw_add'_k, Matrix.mul_add]
  exact Matrix.map_add _ (fun a b => star_add a b) _ _
/- English proof (translation)
Establish `h : d.cw w b = 0` using `hb`. Unfold `_root_.PositivityTheory.SiegelWeilFormula.RD_k.loc`. Rewrite using `[h, Matrix.mul_zero]`. Conclude with `Matrix.map_zero _ (star_zero _)`.
-/
theorem loc_of_mem_k {b : Mx F E d.m d.n} (hb : b ∈ _root_.PositivityTheory.SiegelWeilFormula.KFock.cmpW_k d w) : R.loc w b = 0 := by
  have h : d.cw w b = 0 := hb
  unfold _root_.PositivityTheory.SiegelWeilFormula.RD_k.loc
  rw [h, Matrix.mul_zero]
  exact Matrix.map_zero _ (star_zero _)
/- English proof (translation)
Unfold `_root_.PositivityTheory.SiegelWeilFormula.RD_k.loc`. Conclude with `(continuous_const.matrix_mul (_root_.PositivityTheory.SiegelWeilFormula.Place.continuous_cw_k d w)).matrix_map continuous_star`.
-/
theorem continuous_loc_k : Continuous (R.loc w) := by
  unfold _root_.PositivityTheory.SiegelWeilFormula.RD_k.loc
  exact (continuous_const.matrix_mul (_root_.PositivityTheory.SiegelWeilFormula.Place.continuous_cw_k d w)).matrix_map continuous_star
end Split
/- English proof (translation)
Introduce `F E _ _ _ _ _ σ d R w ν hν`. Use `haveI := hν.1`. Take `⟨i1, i2, i3, i4⟩` from `(PositivityTheory.ThKCT.ideleTop F E).1`. Use `haveI : BorelSpace (AE F E) := ⟨rfl⟩`. Use `haveI : IsTopologicalAddGroup (Mx F E d.m d.n) := inferInstanceAs (IsTopologicalAddGroup (Fin d.m → Fin d.n → AE F E))`.

Use `haveI : LocallyCompactSpace (Mx F E d.m d.n) := inferInstanceAs (LocallyCompactSpace (Fin d.m → Fin d.n → AE F E))`. Use `haveI : SecondCountableTopology (Mx F E d.m d.n) := inferInstanceAs (SecondCountableTopology (Fin d.m → Fin d.n → AE F E))`. Use `haveI : BorelSpace (Mx F E d.m d.n) := inferInstanceAs (BorelSpace (Fin d.m → Fin d.n → AE F E))`. Establish `hcl : IsClosed ((_root_.PositivityTheory.SiegelWeilFormula.KFock.cmpW_k d w : AddSubgroup (Mx F E d.m d.n)) : Set (Mx F E d.m d.n))` using `isClosed_eq (_root_.PositivityTheory.SiegelWeilFormula.Place.continuous_cw_k d w) continuous_const`. Use `haveI : LocallyCompactSpace (_root_.PositivityTheory.SiegelWeilFormula.KFock.cmpW_k d w) := hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace`.

Use `haveI : SecondCountableTopology (_root_.PositivityTheory.SiegelWeilFormula.KFock.cmpW_k d w) := TopologicalSpace.Subtype.secondCountableTopology ((_root_.PositivityTheory.SiegelWeilFormula.KFock.cmpW_k d w : AddSubgroup (Mx F E d.m d.n)) : Set (Mx F E d.m d.n))`. Use `haveI : BorelSpace (_root_.PositivityTheory.SiegelWeilFormula.KFock.cmpW_k d w) := Subtype.borelSpace ((_root_.PositivityTheory.SiegelWeilFormula.KFock.cmpW_k d w : AddSubgroup (Mx F E d.m d.n)) : Set (Mx F E d.m d.n))`. Use `haveI := volume_isAddHaar d.m d.n`. Take `⟨s, hsc, hs1, hs2, hsa, -⟩` from `Place.exists_sec d.cm d.B.emb`. Use `set fr : Matrix (Fin d.m) (Fin d.m) ℂ := (R.fr w).1 with hfr`.

Set `U : (Fin d.m → Fin d.n → ℂ) → Matrix (Fin d.m) (Fin d.n) ℂ` to `fun u => fr * Matrix.of fun b j => star (u b j)`. Set `sW : (Fin d.m → Fin d.n → ℂ) → Mx F E d.m d.n` to `fun u i j => s fun w' => if w' = w then U u i j else 0`. Establish `cw_sW : ∀ u, d.cw w (sW u) = U u` using `fun u => by`. Use extensionality with `i j`. Use `show piInf (d.B.emb w) (s _) = U u i j`.

Rewrite using `[hs1, if_pos rfl]`. Establish `cw_sW' : ∀ u w', w' ≠ w → d.cw w' (sW u) = 0` using `fun u w' h => by`. Use extensionality with `i j`. Use `show piInf (d.B.emb w') (s _) = 0`. Rewrite using `[hs1, if_neg h]`.

Establish `fin_sW : ∀ u, finOne F • sW u = 0` using `fun u => by`. Use extensionality with `i j`. Use `show finOne F • s _ = 0`. Conclude with `hs2 _`. Establish `inv_fr : ((R.fr w)⁻¹).1 * fr = 1` using `Units.inv_mul (R.fr w)`.

Establish `fr_inv : fr * ((R.fr w)⁻¹).1 = 1` using `Units.mul_inv (R.fr w)`. Establish `loc_sW : ∀ u, R.loc w (sW u) = u` using `fun u => by`. Unfold `_root_.PositivityTheory.SiegelWeilFormula.RD_k.loc`. Rewrite using `[cw_sW, ← Matrix.mul_assoc, inv_fr, Matrix.one_mul]`. Use extensionality with `a j`.

Simplify using the standard rewrite rules. Establish `U_loc : ∀ X, U (R.loc w X) = d.cw w X` using `fun X => by`. Simplify using `only [U, _root_.PositivityTheory.SiegelWeilFormula.RD_k.loc]`. Establish `: (Matrix.of fun b j => star ((((R.fr w)⁻¹).1 * d.cw w X).map star b j)) = ((R.fr w)⁻¹).1 * d.cw w X`. Use extensionality with `b j`.

Simplify using the standard rewrite rules. Rewrite using `[this, ← Matrix.mul_assoc, fr_inv, Matrix.one_mul]`. Establish `U_add : ∀ u v, U (u + v) = U u + U v` using `fun u v => by`. Simplify using `only [U]`. Rewrite using `[← Matrix.mul_add]`.

Use `congr 1`. Use extensionality with `b j`. Simplify using `[star_add]`. Establish `sW_add : ∀ u v, sW (u + v) = sW u + sW v` using `fun u v => by`. Use extensionality with `i j`.

Use `show s _ = s _ + s _`. Rewrite using `[← hsa]`. Use `congr 1`. Use function extensionality and compare the values at `w'`. Use `show _ = (if w' = w then U u i j else 0) + (if w' = w then U v i j else 0)`.

Distinguish the cases in `h : w' = w`. Rewrite using `[if_pos h, if_pos h, if_pos h, U_add]`. Both sides reduce to the same expression. Rewrite using `[if_neg h, if_neg h, if_neg h, add_zero]`. Establish `hU : Continuous U`.

Simplify using `only [U]`. Conclude with `continuous_const.matrix_mul (continuous_pi fun b => continuous_pi fun j => continuous_star.comp ((continuous_apply j).comp (continuous_apply b)))`. Establish `hsW : Continuous sW`. Use `continuous_pi fun i => continuous_pi fun j => hsc.comp (continuous_pi fun w' => ?_)` and prove the remaining obligations. Use `split_ifs`.

Conclude with `(continuous_apply j).comp ((continuous_apply i).comp hU)`. Conclude with `continuous_const`. Establish `mem : ∀ X, X - sW (R.loc w X) ∈ _root_.PositivityTheory.SiegelWeilFormula.KFock.cmpW_k d w` using `fun X => by show d.cw w (X - sW (R.loc w X)) = 0`. Rewrite using `[_root_.PositivityTheory.SiegelWeilFormula.KFock.cw_sub'_k, cw_sW, U_loc, sub_self]`. Set `Φ : (Fin d.m → Fin d.n → ℂ) × _root_.PositivityTheory.SiegelWeilFormula.KFock.cmpW_k d w ≃ₜ+ Mx F E d.m d.n` to `{ toFun := fun p => sW p.1 + p.2.1 invFun := fun X => (R.loc w X, ⟨X - sW (R.loc w X), mem X⟩) left_inv := fun p => by`.

Take `⟨u, b, hb⟩` from `p`. Establish `e1 : R.loc w (sW u + b) = u` using `by rw [_root_.PositivityTheory.SiegelWeilFormula.KFock.loc_add'_k, loc_sW, _root_.PositivityTheory.SiegelWeilFormula.KFock.loc_of_mem_k d R w hb, add_zero]`. Use `Prod.ext e1 (Subtype.ext ?_)` and prove the remaining obligations. Use `show sW u + b - sW (R.loc w (sW u + b)) = b`. Rewrite using `[e1, add_sub_cancel_left]`.

Use `right_inv := fun X => by show sW (R.loc w X) + (X - sW (R.loc w X)) = X`. Rewrite using `[add_sub_cancel]`. Use the proof step `map_add' := fun p q => by show sW (p.1 + q.1) + (p.2.1 + q.2.1) = sW p.1 + p.2.1 + (sW q.1 + q.2.1)`. Rewrite using `[sW_add]`. Normalize the expressions using the abelian group laws.

Use `continuous_toFun := (hsW.comp continuous_fst).add (continuous_subtype_val.comp continuous_snd)`. Use `continuous_invFun := (_root_.PositivityTheory.SiegelWeilFormula.KFock.continuous_loc_k d R w).prodMk ((continuous_id.sub (hsW.comp (_root_.PositivityTheory.SiegelWeilFormula.KFock.continuous_loc_k d R w))).subtype_mk _) }`. Take `⟨C, hC, hg⟩` from `integral_split ν (volume : Measure (Fin d.m → Fin d.n → ℂ)) (Measure.addHaar : Measure (_root_.PositivityTheory.SiegelWeilFormula.KFock.cmpW_k d w)) Φ`. Use `⟨C, Measure.addHaar, hC, inferInstance, fun f Ψ hΨ => ?_⟩` and prove the remaining obligations. Rewrite using `[hg]`.

Establish `e : ∀ p : (Fin d.m → Fin d.n → ℂ) × _root_.PositivityTheory.SiegelWeilFormula.KFock.cmpW_k d w, R.tens w f Ψ (Φ p) = f p.1 * Ψ p.2.1` using `fun p => by`. Take `⟨u, b, hb⟩` from `p`. Use `show f (R.loc w (sW u + b)) * Ψ (sW u + b) = f u * Ψ b`. Rewrite using `[_root_.PositivityTheory.SiegelWeilFormula.KFock.loc_add'_k, loc_sW, _root_.PositivityTheory.SiegelWeilFormula.KFock.loc_of_mem_k d R w hb, add_zero, add_comm, hΨ b (sW u) (cw_sW' u) (fin_sW u)]`. Repeatedly rewrite using `[e]`.

Establish `hp` using `integral_prod_mul (μ := (volume : Measure (Fin d.m → Fin d.n → ℂ))) (ν := (Measure.addHaar : Measure (_root_.PositivityTheory.SiegelWeilFormula.KFock.cmpW_k d w))) f (fun Z : _root_.PositivityTheory.SiegelWeilFormula.KFock.cmpW_k d w => Ψ Z.1)`. Rewrite using `[hp, mul_assoc]`.
-/
theorem intFact_k : _root_.PositivityTheory.SiegelWeilFormula.KFock.IntFact_k := by
  intro F E _ _ _ _ _ σ d R w ν hν
  haveI := hν.1
  obtain ⟨i1, i2, i3, i4⟩ := (PositivityTheory.ThKCT.ideleTop F E).1
  haveI : BorelSpace (AE F E) := ⟨rfl⟩
  haveI : IsTopologicalAddGroup (Mx F E d.m d.n) := inferInstanceAs (IsTopologicalAddGroup (Fin d.m → Fin d.n → AE F E))
  haveI : LocallyCompactSpace (Mx F E d.m d.n) := inferInstanceAs (LocallyCompactSpace (Fin d.m → Fin d.n → AE F E))
  haveI : SecondCountableTopology (Mx F E d.m d.n) :=
    inferInstanceAs (SecondCountableTopology (Fin d.m → Fin d.n → AE F E))
  haveI : BorelSpace (Mx F E d.m d.n) := inferInstanceAs (BorelSpace (Fin d.m → Fin d.n → AE F E))
  have hcl : IsClosed ((_root_.PositivityTheory.SiegelWeilFormula.KFock.cmpW_k d w : AddSubgroup (Mx F E d.m d.n)) : Set (Mx F E d.m d.n)) :=
    isClosed_eq (_root_.PositivityTheory.SiegelWeilFormula.Place.continuous_cw_k d w) continuous_const
  haveI : LocallyCompactSpace (_root_.PositivityTheory.SiegelWeilFormula.KFock.cmpW_k d w) := hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology (_root_.PositivityTheory.SiegelWeilFormula.KFock.cmpW_k d w) :=
    TopologicalSpace.Subtype.secondCountableTopology ((_root_.PositivityTheory.SiegelWeilFormula.KFock.cmpW_k d w : AddSubgroup (Mx F E d.m d.n)) : Set (Mx F E d.m d.n))
  haveI : BorelSpace (_root_.PositivityTheory.SiegelWeilFormula.KFock.cmpW_k d w) := Subtype.borelSpace ((_root_.PositivityTheory.SiegelWeilFormula.KFock.cmpW_k d w : AddSubgroup (Mx F E d.m d.n)) : Set (Mx F E d.m d.n))
  haveI := volume_isAddHaar d.m d.n
  obtain ⟨s, hsc, hs1, hs2, hsa, -⟩ := Place.exists_sec d.cm d.B.emb
  set fr : Matrix (Fin d.m) (Fin d.m) ℂ := (R.fr w).1 with hfr
  let U : (Fin d.m → Fin d.n → ℂ) → Matrix (Fin d.m) (Fin d.n) ℂ := fun u => fr * Matrix.of fun b j => star (u b j)
  let sW : (Fin d.m → Fin d.n → ℂ) → Mx F E d.m d.n := fun u i j => s fun w' => if w' = w then U u i j else 0
  have cw_sW : ∀ u, d.cw w (sW u) = U u := fun u => by
    ext i j
    show piInf (d.B.emb w) (s _) = U u i j
    rw [hs1, if_pos rfl]
  have cw_sW' : ∀ u w', w' ≠ w → d.cw w' (sW u) = 0 := fun u w' h => by
    ext i j
    show piInf (d.B.emb w') (s _) = 0
    rw [hs1, if_neg h]
  have fin_sW : ∀ u, finOne F • sW u = 0 := fun u => by
    ext i j
    show finOne F • s _ = 0
    exact hs2 _
  have inv_fr : ((R.fr w)⁻¹).1 * fr = 1 := Units.inv_mul (R.fr w)
  have fr_inv : fr * ((R.fr w)⁻¹).1 = 1 := Units.mul_inv (R.fr w)
  have loc_sW : ∀ u, R.loc w (sW u) = u := fun u => by
    unfold _root_.PositivityTheory.SiegelWeilFormula.RD_k.loc
    rw [cw_sW, ← Matrix.mul_assoc, inv_fr, Matrix.one_mul]
    ext a j
    simp
  have U_loc : ∀ X, U (R.loc w X) = d.cw w X := fun X => by
    simp only [U, _root_.PositivityTheory.SiegelWeilFormula.RD_k.loc]
    have : (Matrix.of fun b j => star ((((R.fr w)⁻¹).1 * d.cw w X).map star b j)) = ((R.fr w)⁻¹).1 * d.cw w X := by
      ext b j; simp
    rw [this, ← Matrix.mul_assoc, fr_inv, Matrix.one_mul]
  have U_add : ∀ u v, U (u + v) = U u + U v := fun u v => by
    simp only [U]
    rw [← Matrix.mul_add]
    congr 1
    ext b j
    simp [star_add]
  have sW_add : ∀ u v, sW (u + v) = sW u + sW v := fun u v => by
    ext i j
    show s _ = s _ + s _
    rw [← hsa]
    congr 1
    funext w'
    show _ = (if w' = w then U u i j else 0) + (if w' = w then U v i j else 0)
    by_cases h : w' = w
    · rw [if_pos h, if_pos h, if_pos h, U_add]; rfl
    · rw [if_neg h, if_neg h, if_neg h, add_zero]
  have hU : Continuous U := by
    simp only [U]
    exact continuous_const.matrix_mul (continuous_pi fun b => continuous_pi fun j =>
      continuous_star.comp ((continuous_apply j).comp (continuous_apply b)))
  have hsW : Continuous sW := by
    refine continuous_pi fun i => continuous_pi fun j => hsc.comp (continuous_pi fun w' => ?_)
    split_ifs
    · exact (continuous_apply j).comp ((continuous_apply i).comp hU)
    · exact continuous_const
  have mem : ∀ X, X - sW (R.loc w X) ∈ _root_.PositivityTheory.SiegelWeilFormula.KFock.cmpW_k d w := fun X => by
    show d.cw w (X - sW (R.loc w X)) = 0
    rw [_root_.PositivityTheory.SiegelWeilFormula.KFock.cw_sub'_k, cw_sW, U_loc, sub_self]
  let Φ : (Fin d.m → Fin d.n → ℂ) × _root_.PositivityTheory.SiegelWeilFormula.KFock.cmpW_k d w ≃ₜ+ Mx F E d.m d.n :=
    { toFun := fun p => sW p.1 + p.2.1
      invFun := fun X => (R.loc w X, ⟨X - sW (R.loc w X), mem X⟩)
      left_inv := fun p => by
        obtain ⟨u, b, hb⟩ := p
        have e1 : R.loc w (sW u + b) = u := by rw [_root_.PositivityTheory.SiegelWeilFormula.KFock.loc_add'_k, loc_sW, _root_.PositivityTheory.SiegelWeilFormula.KFock.loc_of_mem_k d R w hb, add_zero]
        refine Prod.ext e1 (Subtype.ext ?_)
        show sW u + b - sW (R.loc w (sW u + b)) = b
        rw [e1, add_sub_cancel_left]
      right_inv := fun X => by
        show sW (R.loc w X) + (X - sW (R.loc w X)) = X
        rw [add_sub_cancel]
      map_add' := fun p q => by
        show sW (p.1 + q.1) + (p.2.1 + q.2.1) = sW p.1 + p.2.1 + (sW q.1 + q.2.1)
        rw [sW_add]; abel
      continuous_toFun := (hsW.comp continuous_fst).add (continuous_subtype_val.comp continuous_snd)
      continuous_invFun := (_root_.PositivityTheory.SiegelWeilFormula.KFock.continuous_loc_k d R w).prodMk
        ((continuous_id.sub (hsW.comp (_root_.PositivityTheory.SiegelWeilFormula.KFock.continuous_loc_k d R w))).subtype_mk _) }
  obtain ⟨C, hC, hg⟩ := integral_split ν (volume : Measure (Fin d.m → Fin d.n → ℂ)) (Measure.addHaar : Measure (_root_.PositivityTheory.SiegelWeilFormula.KFock.cmpW_k d w)) Φ
  refine ⟨C, Measure.addHaar, hC, inferInstance, fun f Ψ hΨ => ?_⟩
  rw [hg]
  have e : ∀ p : (Fin d.m → Fin d.n → ℂ) × _root_.PositivityTheory.SiegelWeilFormula.KFock.cmpW_k d w, R.tens w f Ψ (Φ p) = f p.1 * Ψ p.2.1 := fun p => by
    obtain ⟨u, b, hb⟩ := p
    show f (R.loc w (sW u + b)) * Ψ (sW u + b) = f u * Ψ b
    rw [_root_.PositivityTheory.SiegelWeilFormula.KFock.loc_add'_k, loc_sW, _root_.PositivityTheory.SiegelWeilFormula.KFock.loc_of_mem_k d R w hb, add_zero, add_comm, hΨ b (sW u) (cw_sW' u) (fin_sW u)]
  simp_rw [e]
  have hp := integral_prod_mul (μ := (volume : Measure (Fin d.m → Fin d.n → ℂ))) (ν := (Measure.addHaar : Measure (_root_.PositivityTheory.SiegelWeilFormula.KFock.cmpW_k d w)))
    f (fun Z : _root_.PositivityTheory.SiegelWeilFormula.KFock.cmpW_k d w => Ψ Z.1)
  rw [hp, mul_assoc]
end PositivityTheory.SiegelWeilFormula.KFock
end
end
