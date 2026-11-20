import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.EStar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalComponentDefiniteUnitaryFinitePartEqLocalPo
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SatakeMatchBaseChange

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil Formalism.BasicNotions Matrix
open UpperTheory.V UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob
open UpperTheory.V.W (Plc Lp)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open Formalism.UG GlobalTheory.BCT.FinPtLoc in
/- English proof (translation)
Express the relevant statement in the definitionally equal form `((1 : Matrix (Fin n) (Fin n) (InfiniteAdeleRing L × Af L)) i j - ((0 : InfiniteAdeleRing L), (1 : Matrix (Fin n) (Fin n) (Af L)) i j) + ((0 : InfiniteAdeleRing L), g.val i j)).1 = _`. Apply the tactic sequence `by_cases h : i = j <;> simp [Matrix.one_apply, h]`.
-/
private theorem fin_fst {L : Type} [Field L] [NumberField L] {n : ℕ} (g : GL (Fin n) (Af L)) (i j : Fin n) :
    fstA L ((finGL L n g).val i j) = (1 : Matrix (Fin n) (Fin n) (InfiniteAdeleRing L)) i j := by
  change ((1 : Matrix (Fin n) (Fin n) (InfiniteAdeleRing L × Af L)) i j -
      ((0 : InfiniteAdeleRing L), (1 : Matrix (Fin n) (Fin n) (Af L)) i j) +
      ((0 : InfiniteAdeleRing L), g.val i j)).1 = _
  by_cases h : i = j <;> simp [Matrix.one_apply, h]

open Formalism.UG GlobalTheory.BCT.FinPtLoc in
/- English proof (translation)
Express the relevant statement in the definitionally equal form `((1 : Matrix (Fin n) (Fin n) (InfiniteAdeleRing L × Af L)) i j - ((0 : InfiniteAdeleRing L), (1 : Matrix (Fin n) (Fin n) (Af L)) i j) + ((0 : InfiniteAdeleRing L), g.val i j)).2 = _`. Apply the tactic sequence `by_cases h : i = j <;> simp [Matrix.one_apply, h]`.
-/
private theorem fin_snd {L : Type} [Field L] [NumberField L] {n : ℕ} (g : GL (Fin n) (Af L)) (i j : Fin n) :
    pFin L ((finGL L n g).val i j) = g.val i j := by
  change ((1 : Matrix (Fin n) (Fin n) (InfiniteAdeleRing L × Af L)) i j -
      ((0 : InfiniteAdeleRing L), (1 : Matrix (Fin n) (Fin n) (Af L)) i j) +
      ((0 : InfiniteAdeleRing L), g.val i j)).2 = _
  by_cases h : i = j <;> simp [Matrix.one_apply, h]

open Formalism.UG GlobalTheory.BCT.FinPtLoc in

/- English proof (translation)
Use `show cT (conjAd L) (finGL L n g).val * 1 * (finGL L n g).val = 1`. Establish `hf : (finGL L n g).val.map (fstA L) = 1`. Use extensionality with `i j`. Rewrite using `[Matrix.map_apply, fin_fst]`. Establish `hs : (finGL L n g).val.map (pFin L) = g.val`.

Use extensionality with `i j`. Rewrite using `[Matrix.map_apply, fin_snd]`. Apply `ext_ad` to reduce the goal to its premises. Rewrite using `[Matrix.map_mul, Matrix.map_mul, map_cT (fstA L) (conjAd L) ((infEq L).toRingHom.comp ((starRingEnd (Cinf L)).comp (infEq L).symm.toRingHom)) (fun x => rfl), hf, Matrix.map_one _ (map_zero _) (map_one _)]`. Use extensionality with `i j`.

Simplify using `[cT, Matrix.one_apply]`. Rewrite using `[Matrix.map_mul, Matrix.map_mul, map_cT (pFin L) (conjAd L) (cjF (L := L)) (fun x => rfl), hs, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one, hg]`.
-/
private theorem fin_mem {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} (g : GL (Fin n) (Af L))
    (hg : cT (cjF (L := L)) g.val * g.val = 1) : finGL L n g ∈ UA L n := by
  show cT (conjAd L) (finGL L n g).val * 1 * (finGL L n g).val = 1
  have hf : (finGL L n g).val.map (fstA L) = 1 := by
    ext i j; rw [Matrix.map_apply, fin_fst]
  have hs : (finGL L n g).val.map (pFin L) = g.val := by
    ext i j; rw [Matrix.map_apply, fin_snd]
  apply ext_ad
  · rw [Matrix.map_mul, Matrix.map_mul, map_cT (fstA L) (conjAd L) ((infEq L).toRingHom.comp ((starRingEnd (Cinf L)).comp (infEq L).symm.toRingHom)) (fun x => rfl), hf, Matrix.map_one _ (map_zero _) (map_one _)]
    ext i j; simp [cT, Matrix.one_apply]
  · rw [Matrix.map_mul, Matrix.map_mul, map_cT (pFin L) (conjAd L) (cjF (L := L)) (fun x => rfl), hs,
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one, hg]

open Formalism.UG GlobalTheory.BCT.FinPtLoc in
/- English proof (translation)
Use `show cInf (⟨_, h⟩ : UA L n) = 1`. Apply `Units.ext` to reduce the goal to its premises. Use `Matrix.ext fun i j => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(infEq L).symm (fstA L ((finGL L n g).val i j)) = (1 : Matrix (Fin n) (Fin n) (Cinf L)) i j`. Rewrite using `[fin_fst]`.

Apply the tactic sequence `by_cases h : i = j <;> simp [Matrix.one_apply, h]`.
-/
private theorem fin_ker {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} (g : GL (Fin n) (Af L))
    (h : finGL L n g ∈ UA L n) : (⟨_, h⟩ : UA L n) ∈ finU L n := by
  show cInf (⟨_, h⟩ : UA L n) = 1
  apply Units.ext
  refine Matrix.ext fun i j => ?_
  change (infEq L).symm (fstA L ((finGL L n g).val i j)) = (1 : Matrix (Fin n) (Fin n) (Cinf L)) i j
  rw [fin_fst]
  by_cases h : i = j <;> simp [Matrix.one_apply, h]

/- English proof (translation)
Introduce `L _ _ _ R n x hx hint`. Establish `ev : ∀ i j, ∀ᶠ w : Plc L in Filter.cofinite, R.ρ _ w rfl (x (un w) i j) ∈ w.adicCompletionIntegers L` using `fun i j => ((GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.tendsto_under (Lp L) L).eventually hint).mono fun w h => (R.ρ_int (un w) _).1 (h i j) w rfl`. Set `a : Fin n → Fin n → Af L` to `fun i j => ⟨fun w => R.ρ _ w rfl (x (un w) i j), ev i j⟩`. Establish `ha : ∀ i j (w : Plc L), pLoc L w (a i j) = R.ρ _ w rfl (x (un w) i j)` using `fun _ _ _ => rfl`. Establish `hv : ∀ i j (v : Pl (Lp L)) (w : Plc L) (h : un w = v), R.ρ v w h (x v i j) = pLoc L w (a i j)`.

Introduce and unpack `i j _ w rfl`. Both sides reduce to the same expression. Establish `hc : ∀ i j (w : Plc L), pLoc L w (cjF (a i j)) = R.ρ _ w rfl (star (x (un w) i j))` using `fun i j w => (R.ρ_star (un w) (x (un w) i j) (a i j) (hv i j (un w)) w rfl).symm`. Set `M : Matrix (Fin n) (Fin n) (Af L)` to `Matrix.of a`. Establish `hM : Formalism.UG.cT (cjF (L` using `L)) M * M = 1 := by`.

Use `Matrix.ext fun i j => Subtype.ext (funext fun w => ?_)` and prove the remaining obligations. Establish `h1` using `congrArg (R.ρ _ w rfl) (congrFun (congrFun (hx (un w)) i) j)`. Rewrite `h1` using `[Matrix.mul_apply, map_sum]`. Express the relevant statement in the definitionally equal form `pLoc L w _ = pLoc L w _`. Rewrite using `[Matrix.mul_apply, map_sum]`.

Establish `h2 : pLoc L w ((1 : Matrix (Fin n) (Fin n) (Af L)) i j) = R.ρ _ w rfl ((1 : Matrix (Fin n) (Fin n) _) i j)`. Apply the tactic sequence `by_cases h : i = j <;> simp [Matrix.one_apply, h]`. Rewrite using `[h2, ← h1]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, map_mul]`.

Simplify using `only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply, Matrix.star_apply]`. Conclude with `congrArg₂ _ (hc k i w) (ha k j w)`. Set `g : GL (Fin n) (Af L)` to `⟨M, Formalism.UG.cT (cjF (L := L)) M, mul_eq_one_comm.1 hM, hM⟩`. Establish `hm` using `fin_mem g hM`. Use `⟨⟨_, hm⟩, fin_ker g hm, fun w => ?_⟩` and prove the remaining obligations.

Use `Matrix.ext fun i j => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `pLoc L w (pFin L ((finGL L n g).val i j)) = _`. Rewrite using `[fin_snd]`. Both sides reduce to the same expression.
-/
theorem UpperTheory.V.Z.Sym.Dict.Br.adEx :
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (R : RingBr L) (n : ℕ) (x : ∀ v : Pl (Lp L), Matrix (Fin n) (Fin n) (Lsq (Kv v) (cv v R.Δ))), (∀ v, star (x v) * x v = 1) → (∀ᶠ v in Filter.cofinite, ∀ i j, IsIntegral (Ov v) (x v i j)) → ∃ g ∈ finU L n, ∀ w, mL w g = (x (un w)).map (R.ρ _ w rfl) := by
  intro L _ _ _ R n x hx hint
  have ev : ∀ i j, ∀ᶠ w : Plc L in Filter.cofinite, R.ρ _ w rfl (x (un w) i j) ∈ w.adicCompletionIntegers L :=
    fun i j => ((GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.tendsto_under (Lp L) L).eventually hint).mono
      fun w h => (R.ρ_int (un w) _).1 (h i j) w rfl
  let a : Fin n → Fin n → Af L := fun i j => ⟨fun w => R.ρ _ w rfl (x (un w) i j), ev i j⟩
  have ha : ∀ i j (w : Plc L), pLoc L w (a i j) = R.ρ _ w rfl (x (un w) i j) := fun _ _ _ => rfl
  have hv : ∀ i j (v : Pl (Lp L)) (w : Plc L) (h : un w = v), R.ρ v w h (x v i j) = pLoc L w (a i j) := by
    rintro i j _ w rfl; rfl
  have hc : ∀ i j (w : Plc L), pLoc L w (cjF (a i j)) = R.ρ _ w rfl (star (x (un w) i j)) := fun i j w =>
    (R.ρ_star (un w) (x (un w) i j) (a i j) (hv i j (un w)) w rfl).symm
  let M : Matrix (Fin n) (Fin n) (Af L) := Matrix.of a
  have hM : Formalism.UG.cT (cjF (L := L)) M * M = 1 := by
    refine Matrix.ext fun i j => Subtype.ext (funext fun w => ?_)
    have h1 := congrArg (R.ρ _ w rfl) (congrFun (congrFun (hx (un w)) i) j)
    rw [Matrix.mul_apply, map_sum] at h1
    change pLoc L w _ = pLoc L w _
    rw [Matrix.mul_apply, map_sum]
    have h2 : pLoc L w ((1 : Matrix (Fin n) (Fin n) (Af L)) i j) = R.ρ _ w rfl ((1 : Matrix (Fin n) (Fin n) _) i j) := by
      by_cases h : i = j <;> simp [Matrix.one_apply, h]
    rw [h2, ← h1]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, map_mul]
    simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply, Matrix.star_apply]
    exact congrArg₂ _ (hc k i w) (ha k j w)
  let g : GL (Fin n) (Af L) := ⟨M, Formalism.UG.cT (cjF (L := L)) M, mul_eq_one_comm.1 hM, hM⟩
  have hm := fin_mem g hM
  refine ⟨⟨_, hm⟩, fin_ker g hm, fun w => ?_⟩
  refine Matrix.ext fun i j => ?_
  change pLoc L w (pFin L ((finGL L n g).val i j)) = _
  rw [fin_snd]
  rfl
