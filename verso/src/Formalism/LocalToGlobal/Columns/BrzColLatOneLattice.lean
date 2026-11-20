import Mathlib
import Formalism.LocalToGlobal.Columns.SummandSlopeAtDecoratedLattice
import Formalism.LocalToGlobal.Columns.ToHLatLemmas
import Formalism.LocalToGlobal.Columns.CoefficientsModP
import Formalism.LocalToGlobal.GlobalTheory.HLatOpsP

open NumberField IsDedekindDomain Module
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.GlobalTheoryTheory.HLatOps Formalism.HermitianLattices.TraceIntegrality

section Forms

variable {K : Type} [Field K] [NumberField K] [StarRing K] {V ι : Type} [AddCommGroup V] [Module K V] [Fintype ι]
  (b : Basis ι K V) (P : V →ₗ⋆[K] V →ₗ[K] K)

/- English proof (translation)
Introduce `v`. Use `⟨fun x x' y => ?_, fun x y y' => ?_, fun a x y => ?_, fun a x y => ?_⟩` and prove the remaining obligations. Simplify using `only [formAt, map_add, Finsupp.add_apply, add_mul, Finset.sum_add_distrib]`. Simplify using `only [formAt, map_add, Finsupp.add_apply, mul_add, Finset.sum_add_distrib]`. Simplify using `only [formAt, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum, mul_assoc]`.

Simplify using `only [formAt, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem isSesq_formAt : IsSesq (formAt b P) := by
  intro v
  refine ⟨fun x x' y => ?_, fun x y y' => ?_, fun a x y => ?_, fun a x y => ?_⟩
  · simp only [formAt, map_add, Finsupp.add_apply, add_mul, Finset.sum_add_distrib]
  · simp only [formAt, map_add, Finsupp.add_apply, mul_add, Finset.sum_add_distrib]
  · simp only [formAt, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum, mul_assoc]
  · simp only [formAt, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [gramOf, Matrix.of_apply, formAt, Basis.repr_self, Finsupp.single_apply]`. Rewrite using `[Finset.sum_eq_single i, Finset.sum_eq_single j]`. Simplify using the standard rewrite rules. Introduce `j' _ hj`.

Simplify using `[Ne.symm hj]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`. Introduce `i' _ hi`. Simplify using `[Ne.symm hi]`.

Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`.
-/
theorem gramOf_formAt [DecidableEq ι] (v : InfinitePlace K) :
    gramOf b (formAt b P v) = Matrix.of fun i j => v.embedding (P (b i) (b j)) := by
  ext i j
  simp only [gramOf, Matrix.of_apply, formAt, Basis.repr_self, Finsupp.single_apply]
  rw [Finset.sum_eq_single i, Finset.sum_eq_single j]
  · simp
  · intro j' _ hj
    simp [Ne.symm hj]
  · intro h; exact absurd (Finset.mem_univ _) h
  · intro i' _ hi
    simp [Ne.symm hi]
  · intro h; exact absurd (Finset.mem_univ _) h

/- English proof (translation)
Introduce `v` and use `by rw [gramOf_formAt]; exact hpos v`.
-/
theorem posAt_formAt [DecidableEq ι] (hpos : ∀ v : InfinitePlace K, (Matrix.of fun i j => v.embedding (P (b i) (b j))).PosDef) :
    PosAt b (formAt b P) := fun v => by rw [gramOf_formAt]; exact hpos v

variable [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [DecidableEq ι]

/- English proof (translation)
The claim follows from `of_form_spec K V ι b L (formAt b P) (isSesq_formAt b P) (posAt_formAt b P hpos)`.
-/
theorem formH_spec (hpos : ∀ v : InfinitePlace K, (Matrix.of fun i j => v.embedding (P (b i) (b j))).PosDef)
    (L : Submodule (𝓞 K) V) :
    FrameOK (ofFormB b L (formAt b P)) ∧
    (∀ v (x y : V), Formalism.HermitianLatticesTheory.majAt (ofFormB b L (formAt b P)).b (ofFormB b L (formAt b P)).X v x y = formAt b P v x y) ∧
    (∀ v (x : V), Formalism.HermitianLatticesTheory.normAt (ofFormB b L (formAt b P)).b (ofFormB b L (formAt b P)).X v x =
      Real.sqrt (formAt b P v x x).re) :=
  of_form_spec K V ι b L (formAt b P) (isSesq_formAt b P) (posAt_formAt b P hpos)

/- English proof (translation)
Assemble the required witnesses or components as `⟨(formH_spec b P hpos L).1, hL.fg, hL.span_eq_top⟩`.
-/
theorem formH_good (hpos : ∀ v : InfinitePlace K, (Matrix.of fun i j => v.embedding (P (b i) (b j))).PosDef)
    {L : Submodule (𝓞 K) V} (hL : Submodule.IsLattice K L) : (ofFormB b L (formAt b P)).Good :=
  ⟨(formH_spec b P hpos L).1, hL.fg, hL.span_eq_top⟩

end Forms

/- English proof (translation)
Establish `h1` using `(Formalism.HN.plLat K A.V A.ι A.b A.X hX A.L hL).1`. Establish `h2` using `(Formalism.HN.muChar (𝓞 K) A.V _ (Formalism.HermitianLatticesTheory.realize A.b A.X) A.L h1 hne).2.2.2.2`. Unfold `HLat.mu HLat.muMax Formalism.HN.muDef Formalism.HN.muMaxDef`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem hlat_mu_le_muMax {K : Type} [Field K] [NumberField K] [StarRing K] (A : HLat K) (hX : FrameOK A) (hL : A.L.FG)
    (hne : A.L ≠ ⊥) : A.mu ≤ A.muMax := by
  have h1 := (Formalism.HN.plLat K A.V A.ι A.b A.X hX A.L hL).1
  have h2 := (Formalism.HN.muChar (𝓞 K) A.V _ (Formalism.HermitianLatticesTheory.realize A.b A.X) A.L h1 hne).2.2.2.2
  unfold HLat.mu HLat.muMax Formalism.HN.muDef Formalism.HN.muMaxDef
  linarith

/- English proof (translation)
Introduce `h`. Establish `h2` using `hL.span_eq_top`. Rewrite `h2` using `[h, Submodule.bot_coe, Submodule.span_zero_singleton]`. Conclude with `bot_ne_top h2`.
-/
theorem isLattice_ne_bot {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] [Nontrivial V] {L : Submodule (𝓞 K) V} (hL : Submodule.IsLattice K L) : L ≠ ⊥ := by
  intro h
  have h2 := hL.span_eq_top
  rw [h, Submodule.bot_coe, Submodule.span_zero_singleton] at h2
  exact bot_ne_top h2

section Val

variable {K : Type} [Field K] [NumberField K] [StarRing K] {S : GSD K}

/- English proof (translation)
The claim follows from `R.pos v`.
-/
theorem GSD.Rat.pos' (R : S.Rat) (v : InfinitePlace K) :
    (Matrix.of fun i j => v.embedding (S.pair (S.bV i) (S.bV j))).PosDef := R.pos v

/- English proof (translation)
The claim follows from `formH_spec S.bV S.pair R.pos' (S.Del d)`.
-/
theorem GSD.valH_spec (R : S.Rat) (d : S.D) :
    FrameOK (S.valH d) ∧
    (∀ v (x y : S.V), Formalism.HermitianLatticesTheory.majAt (S.valH d).b (S.valH d).X v x y = S.pairAt v x y) ∧
    (∀ v (x : S.V), Formalism.HermitianLatticesTheory.normAt (S.valH d).b (S.valH d).X v x = Real.sqrt (S.pairAt v x x).re) :=
  formH_spec S.bV S.pair R.pos' (S.Del d)

/- English proof (translation)
The claim follows from `formH_good S.bV S.pair R.pos' hD`.
-/
theorem GSD.valH_good (R : S.Rat) (d : S.D) (hD : Submodule.IsLattice K (S.Del d)) : (S.valH d).Good :=
  formH_good S.bV S.pair R.pos' hD

/- English proof (translation)
The claim follows from `formH_good S.bV S.pair R.pos' hD`.
-/
theorem GSD.valNabH_good (R : S.Rat) (d : S.D) (hD : Submodule.IsLattice K (S.Nab d)) : (S.valNabH d).Good :=
  formH_good S.bV S.pair R.pos' hD

end Val

section Std

variable (K : Type) [Field K] [NumberField K] [StarRing K] {n : ℕ} (lam : DomWeight n)

/- English proof (translation)
The claim follows from `pairPos K Unit n (oneW lam) _ v.embedding fun _ => by rw [Matrix.map_one _ (map_zero _) (map_one _)] exact Matrix.PosDef.one`.
-/
theorem stdPair_pos (v : InfinitePlace K) :
    (Matrix.of fun i j => v.embedding (stdPair K lam (bVV K (oneW lam) i) (bVV K (oneW lam) j))).PosDef :=
  pairPos K Unit n (oneW lam) _ v.embedding fun _ => by
    rw [Matrix.map_one _ (map_zero _) (map_one _)]
    exact Matrix.PosDef.one

/- English proof (translation)
Unfold `stdNabL nabK`. Establish `h` using `(nabDelFree K Unit n (oneW lam) 1).1`. Establish `h1 : (nabStd K (oneW lam)).map ((actP (oneW lam) (1 : Unit → GL (Fin n) K)).restrictScalars (𝓞 K)) = nabStd K (oneW lam)`. Use extensionality with `F`. Simplify using `[polyAction_one₂]`.

Rewrite `h` using `[h1]`. Rewrite using `[← h]`. Both sides reduce to the same expression.
-/
theorem stdNabL_eq : stdNabL K lam = nabK (oneW lam) fun _ => colLat (1 : GL (Fin n) K) := by
  unfold stdNabL nabK
  have h := (nabDelFree K Unit n (oneW lam) 1).1
  have h1 : (nabStd K (oneW lam)).map ((actP (oneW lam) (1 : Unit → GL (Fin n) K)).restrictScalars (𝓞 K)) = nabStd K (oneW lam) := by
    ext F
    simp [polyAction_one₂]
  rw [h1] at h
  rw [← h]
  rfl

/- English proof (translation)
Unfold `stdDelL delK`. Establish `h` using `(nabDelFree K Unit n (oneW lam) 1).2`. Establish `h1 : (delStd K (oneW lam)).map ((actP (oneW lam) (1 : Unit → GL (Fin n) K)).restrictScalars (𝓞 K)) = delStd K (oneW lam)`. Use extensionality with `F`. Simplify using `[polyAction_one₂]`.

Rewrite `h` using `[h1]`. Rewrite using `[← h]`. Both sides reduce to the same expression.
-/
theorem stdDelL_eq : stdDelL K lam = delK (oneW lam) fun _ => colLat (1 : GL (Fin n) K) := by
  unfold stdDelL delK
  have h := (nabDelFree K Unit n (oneW lam) 1).2
  have h1 : (delStd K (oneW lam)).map ((actP (oneW lam) (1 : Unit → GL (Fin n) K)).restrictScalars (𝓞 K)) = delStd K (oneW lam) := by
    ext F
    simp [polyAction_one₂]
  rw [h1] at h
  rw [← h]
  rfl

/- English proof (translation)
Establish `e : colLat (1 : GL (Fin n) K) = stdLat K n`. Use extensionality with `x`. Rewrite using `[lc_mem_colLat_one]`. Simplify using `only [stdLat, Submodule.mem_pi, Set.mem_univ, true_imp_iff]`. Rewrite using `[e]`.

Conclude with `stdLat_lattice`.
-/
theorem brz_colLat_one_lattice : Submodule.IsLattice K (colLat (1 : GL (Fin n) K)) := by
  have e : colLat (1 : GL (Fin n) K) = stdLat K n := by
    ext x
    rw [lc_mem_colLat_one]
    simp only [stdLat, Submodule.mem_pi, Set.mem_univ, true_imp_iff]
  rw [e]
  exact stdLat_lattice

/- English proof (translation)
Rewrite using `[stdNabL_eq]`. Conclude with `(nabDelLattice K Unit n (oneW lam) _ fun _ => brz_colLat_one_lattice K).1`.
-/
theorem stdNabL_isLattice : Submodule.IsLattice K (stdNabL K lam) := by
  rw [stdNabL_eq]
  exact (nabDelLattice K Unit n (oneW lam) _ fun _ => brz_colLat_one_lattice K).1

/- English proof (translation)
Rewrite using `[stdDelL_eq]`. Conclude with `(nabDelLattice K Unit n (oneW lam) _ fun _ => brz_colLat_one_lattice K).2`.
-/
theorem stdDelL_isLattice : Submodule.IsLattice K (stdDelL K lam) := by
  rw [stdDelL_eq]
  exact (nabDelLattice K Unit n (oneW lam) _ fun _ => brz_colLat_one_lattice K).2

/- English proof (translation)
The claim follows from `formH_good _ _ (stdPair_pos K lam) (stdNabL_isLattice K lam)`.
-/
theorem stdNabH_good : (stdNabH K lam).Good := formH_good _ _ (stdPair_pos K lam) (stdNabL_isLattice K lam)

/- English proof (translation)
The claim follows from `formH_good _ _ (stdPair_pos K lam) (stdDelL_isLattice K lam)`.
-/
theorem stdDelH_good : (stdDelH K lam).Good := formH_good _ _ (stdPair_pos K lam) (stdDelL_isLattice K lam)

/- English proof (translation)
Conclude with `isLattice_ne_bot (stdNabL_isLattice K lam)`.
-/
theorem stdNabL_ne_bot : stdNabL K lam ≠ ⊥ := by
  exact isLattice_ne_bot (stdNabL_isLattice K lam)

/- English proof (translation)
Conclude with `isLattice_ne_bot (stdDelL_isLattice K lam)`.
-/
theorem stdDelL_ne_bot : stdDelL K lam ≠ ⊥ := by
  exact isLattice_ne_bot (stdDelL_isLattice K lam)

/- English proof (translation)
The claim follows from `Submodule.comap_mono (delStd_le_nabStd K (oneW lam))`.
-/
theorem stdDelL_le : stdDelL K lam ≤ stdNabL K lam :=
  Submodule.comap_mono (delStd_le_nabStd K (oneW lam))

/- English proof (translation)
The claim follows from `hlat_mu_le_muMax (stdNabH K lam) (stdNabH_good K lam).1 (stdNabH_good K lam).2.1 (stdNabL_ne_bot K lam)`.
-/
theorem slopeLeMax : SlopeLeMax K lam :=
  hlat_mu_le_muMax (stdNabH K lam) (stdNabH_good K lam).1 (stdNabH_good K lam).2.1 (stdNabL_ne_bot K lam)

end Std

section Cols

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)

/- English proof (translation)
The claim follows from `GSD.valH_good (colRat W Ch hX u j) d (thl_colDel_isLattice W Ch u j d)`.
-/
theorem colValH_good (hX : X.Ok) (u : Pr.Word) (j : ℕ) (d : (colGSD W Ch u j).D) : ((colGSD W Ch u j).valH d).Good :=
  GSD.valH_good (colRat W Ch hX u j) d (thl_colDel_isLattice W Ch u j d)

end Cols

end Formalism.L2.Col
