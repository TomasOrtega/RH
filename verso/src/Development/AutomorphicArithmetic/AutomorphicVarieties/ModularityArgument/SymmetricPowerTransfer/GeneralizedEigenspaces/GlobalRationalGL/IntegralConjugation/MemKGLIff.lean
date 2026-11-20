import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.EStar
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.IntegralConjugation.IntsOv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmallOpenCompactNormal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeDEqSumOfAgree

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil Formalism.BasicNotions Matrix
open UpperTheory.V UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob
open UpperTheory.V.W (Plc Lp)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

/- English proof (translation)
Rewrite using `[← GlobalTheory.HeckeEigConj.KO_eq_KGL, GlobalTheory.SplitFlip.mem_KO_iff]`. Establish `h : ∀ y : Kw w, y ∈ 𝒪[Kw w] ↔ y ∈ w.adicCompletionIntegers L` using `fun y => ((intsOv L w).2 y).symm`. Simplify using `only [h]`.
-/
private theorem mem_KGL_iff {L : Type} [Field L] [NumberField L] [IsCMField L] (w : Plc L) {n : ℕ}
    (x : GL (Fin n) (Kw w)) : x ∈ GlobalTheory.LFun.KGL w n ↔
      (∀ i j, (x : Matrix (Fin n) (Fin n) (Kw w)) i j ∈ w.adicCompletionIntegers L) ∧
      ∀ i j, ((x⁻¹ : GL (Fin n) (Kw w)) : Matrix (Fin n) (Fin n) (Kw w)) i j ∈ w.adicCompletionIntegers L := by
  rw [← GlobalTheory.HeckeEigConj.KO_eq_KGL, GlobalTheory.SplitFlip.mem_KO_iff]
  have h : ∀ y : Kw w, y ∈ 𝒪[Kw w] ↔ y ∈ w.adicCompletionIntegers L := fun y => ((intsOv L w).2 y).symm
  simp only [h]

/- English proof (translation)
Introduce `L _ _ _ B`. Establish `hm : ∀ (g : GA B.Δ) (w : Plc L) (i j : Fin 3), (cLoc w (B.bG g : UA L 3) : Matrix (Fin 3) (Fin 3) (Kw w)) i j = B.ρ _ w rfl ((g.1 (un w) : Matrix (Fin 3) (Fin 3) _) i j)` using `fun g w i j => congrFun (congrFun (B.bG_loc g w) i) j`. Establish `hi : ∀ (g : GA B.Δ) (w : Plc L) (i j : Fin 3), (((cLoc w (B.bG g : UA L 3))⁻¹ : GL (Fin 3) (Kw w)) : Matrix (Fin 3) (Fin 3) (Kw w)) i j = B.ρ _ w rfl (star ((g.1 (un w) : Matrix (Fin 3) (Fin 3) _) j i))`. Introduce `g w i j`. Establish `h` using `hm g⁻¹ w i j`.

Rewrite `h` using `[map_inv, InvMemClass.coe_inv, map_inv]`. Conclude with `h`. Use `⟨fun g v => ?_, fun g v => ?_, fun w S g => ?_⟩` and prove the remaining obligations. Prove the components needed by the constructor for the conclusion. Introduce `hK w h`.

Substitute `h` using the available equality. Rewrite using `[mem_KGL_iff]`. Use `⟨fun i j => ?_, fun i j => ?_⟩` and prove the remaining obligations. Rewrite using `[hm]`. Conclude with `(B.ρ_int _ _).1 (hK i j).1 w rfl`.

Rewrite using `[hi]`. Conclude with `(B.ρ_int _ _).1 (hK j i).2 w rfl`. Introduce `H i j`. Use `⟨(B.ρ_int _ _).2 fun w h => ?_, (B.ρ_int _ _).2 fun w h => ?_⟩` and prove the remaining obligations. Substitute `h` using the available equality.

Use `((mem_KGL_iff _ _).1 (H w rfl)).1 i j` as an intermediate fact. Rewrite `this` using `[hm]`. Then use the resulting hypothesis. Substitute `h` using the available equality. Use `((mem_KGL_iff _ _).1 (H w rfl)).2 j i` as an intermediate fact. Rewrite `this` using `[hi]`. Then use the resulting hypothesis.

Prove the components needed by the constructor for the conclusion. Introduce `h1 w h`. Substitute `h` using the available equality. Apply `Units.ext` to reduce the goal to its premises. Use `B.bG_loc g w` as an intermediate fact.

Rewrite `this` using `[h1]`. Use `this.trans ?_` and prove the remaining obligations. Conclude with `Matrix.map_one _ (map_zero _) (map_one _)`. Introduce `H`. Apply `Subtype.ext` to reduce the goal to its premises.

Use `Matrix.ext fun i j => ?_` and prove the remaining obligations. Apply `sub_eq_zero.1` to reduce the goal to its premises. Apply `B.ρ_inj` to reduce the goal to its premises. Introduce `w h`. Consider the cases of `h`.

Establish `e2` using `hm g w i j`. Rewrite `e2` using `[H w rfl, Units.val_one]`. Establish `e3 : B.ρ _ w rfl ((1 : Matrix (Fin 3) (Fin 3) (Lsq (Kv (un w)) (cv (un w) B.Δ))) i j) = (1 : Matrix (Fin 3) (Fin 3) (Kw w)) i j` using `congrFun (congrFun (Matrix.map_one (B.ρ _ w rfl) (map_zero _) (map_one _)) i) j`. Rewrite using `[map_sub, ← e2]`. Conclude with `sub_eq_zero.2 e3.symm`.

Apply `Units.ext` to reduce the goal to its premises. Use `(B.bG_loc g w).trans ?_` and prove the remaining obligations. Use `Matrix.ext fun i j => ?_` and prove the remaining obligations. Conclude with `S.ρ_eq _`.
-/
theorem UpperTheory.V.Z.Sym.Dict.Br.okG :
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (B : Bridge L), (∀ (g : GA B.Δ) v, g.1 v ∈ KU (Ov v) _ ↔ ∀ w, un w = v → cLoc w (B.bG g : UA L 3) ∈ GlobalTheory.LFun.KGL w 3) ∧ (∀ (g : GA B.Δ) v, g.1 v = 1 ↔ ∀ w, un w = v → cLoc w (B.bG g : UA L 3) = 1) ∧ ∀ w (S : B.toRingBr.Split w) (g : GA B.Δ), cLoc w (B.bG g : UA L 3) = GeneralLinearGroup.map (S.i : Kv (un w) →+* Kw w) (Sig.eU S.hs (g.1 (un w))) := by
  intro L _ _ _ B
  have hm : ∀ (g : GA B.Δ) (w : Plc L) (i j : Fin 3),
      (cLoc w (B.bG g : UA L 3) : Matrix (Fin 3) (Fin 3) (Kw w)) i j
        = B.ρ _ w rfl ((g.1 (un w) : Matrix (Fin 3) (Fin 3) _) i j) :=
    fun g w i j => congrFun (congrFun (B.bG_loc g w) i) j
  have hi : ∀ (g : GA B.Δ) (w : Plc L) (i j : Fin 3),
      (((cLoc w (B.bG g : UA L 3))⁻¹ : GL (Fin 3) (Kw w)) : Matrix (Fin 3) (Fin 3) (Kw w)) i j
        = B.ρ _ w rfl (star ((g.1 (un w) : Matrix (Fin 3) (Fin 3) _) j i)) := by
    intro g w i j
    have h := hm g⁻¹ w i j
    rw [map_inv, InvMemClass.coe_inv, map_inv] at h
    exact h
  refine ⟨fun g v => ?_, fun g v => ?_, fun w S g => ?_⟩
  · constructor
    · intro hK w h
      subst h
      rw [mem_KGL_iff]
      refine ⟨fun i j => ?_, fun i j => ?_⟩
      · rw [hm]
        exact (B.ρ_int _ _).1 (hK i j).1 w rfl
      · rw [hi]
        exact (B.ρ_int _ _).1 (hK j i).2 w rfl
    · intro H i j
      refine ⟨(B.ρ_int _ _).2 fun w h => ?_, (B.ρ_int _ _).2 fun w h => ?_⟩
      · subst h
        have := ((mem_KGL_iff _ _).1 (H w rfl)).1 i j
        rwa [hm] at this
      · subst h
        have := ((mem_KGL_iff _ _).1 (H w rfl)).2 j i
        rwa [hi] at this
  · constructor
    · intro h1 w h
      subst h
      apply Units.ext
      have := B.bG_loc g w
      rw [h1] at this
      refine this.trans ?_
      exact Matrix.map_one _ (map_zero _) (map_one _)
    · intro H
      apply Subtype.ext
      refine Matrix.ext fun i j => ?_
      apply sub_eq_zero.1
      apply B.ρ_inj
      intro w h
      cases h
      have e2 := hm g w i j
      rw [H w rfl, Units.val_one] at e2
      have e3 : B.ρ _ w rfl ((1 : Matrix (Fin 3) (Fin 3) (Lsq (Kv (un w)) (cv (un w) B.Δ))) i j) = (1 : Matrix (Fin 3) (Fin 3) (Kw w)) i j :=
        congrFun (congrFun (Matrix.map_one (B.ρ _ w rfl) (map_zero _) (map_one _)) i) j
      rw [map_sub, ← e2]
      exact sub_eq_zero.2 e3.symm
  · apply Units.ext
    refine (B.bG_loc g w).trans ?_
    refine Matrix.ext fun i j => ?_
    exact S.ρ_eq _
