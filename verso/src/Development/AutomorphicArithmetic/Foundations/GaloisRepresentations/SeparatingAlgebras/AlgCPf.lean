import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.GroupDetAlt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.StGlob

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open MeasureTheory GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

/- English proof (translation)
Introduce `hA l _ ι H _ _ hp P hP hcard`. Set `P' : Submodule (Qbar l) (H → Qbar l)` to `{ carrier := {f | (fun h => ι (f h)) ∈ P} zero_mem' := by show (fun h => ι ((0 : H → Qbar l) h)) ∈ P`. Use `P.zero_mem using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `h`. Simplify using the standard rewrite rules.

Use the proof step `add_mem' := by`. Introduce `a b ha hb`. Use `show (fun h => ι ((a + b) h)) ∈ P`. Use `P.add_mem ha hb using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `h`.

Simplify using the standard rewrite rules. Use the proof step `smul_mem' := by`. Introduce `r a ha`. Use `show (fun h => ι ((r • a) h)) ∈ P`. Use `P.smul_mem (ι r) ha using 1` and compare the differences between its conclusion and the goal.

Use function extensionality and compare the values at `h`. Simplify using `}`. Set `j : P ≃+ P'` to `{ toFun := fun c => ⟨fun h => ι.symm (c.1 h), by show (fun h => ι (ι.symm (c.1 h))) ∈ P`. Simplify using `using c.2⟩`. Use `invFun := fun f => ⟨fun h => ι (f.1 h), f.2⟩`.

Use `left_inv := by`. Introduce `c`. Use extensionality with `h`. Simplify using the standard rewrite rules. Use `right_inv := by`.

Introduce `f`. Use extensionality with `h`. Simplify using the standard rewrite rules. Use the proof step `map_add' := by`. Introduce `a b`.

Use extensionality with `h`. Simplify using `}`. Establish `hrank : Module.rank ℂ P = Module.rank (Qbar l) P'`. Use `rank_eq_of_equiv_equiv (fun z => ι.symm z) j ι.symm.bijective ?_` and prove the remaining obligations. Introduce `r m`.

Use extensionality with `h`. Simplify using `[j, smul_eq_mul, map_mul]`. Establish `hfin : Module.finrank ℂ P = Module.finrank (Qbar l) P'`. Unfold `Module.finrank`. Rewrite using `[hrank]`.

Establish `hinv : ∀ c ∈ P', ∀ g : H, (fun h => c (h * g)) ∈ P'`. Introduce `c hc g`. Conclude with `hP _ hc g`. Take `⟨c, hc, hbound⟩` from `hA (Qbar l) l H hp P' hinv (hfin ▸ hcard)`. Use `⟨fun h => ι (c h), hc, ?_⟩` and prove the remaining obligations.

Introduce `h`. Simplify using `using hbound h`.
-/
theorem UpperTheory.Gal.Gen.algC_pf :
    UpperTheory.Gal.Gen.Alg → UpperTheory.Gal.Gen.AlgC := by
  intro hA l _ ι H _ _ hp P hP hcard
  let P' : Submodule (Qbar l) (H → Qbar l) :=
    { carrier := {f | (fun h => ι (f h)) ∈ P}
      zero_mem' := by
        show (fun h => ι ((0 : H → Qbar l) h)) ∈ P
        convert P.zero_mem using 1
        funext h
        simp
      add_mem' := by
        intro a b ha hb
        show (fun h => ι ((a + b) h)) ∈ P
        convert P.add_mem ha hb using 1
        funext h
        simp
      smul_mem' := by
        intro r a ha
        show (fun h => ι ((r • a) h)) ∈ P
        convert P.smul_mem (ι r) ha using 1
        funext h
        simp }
  let j : P ≃+ P' :=
    { toFun := fun c => ⟨fun h => ι.symm (c.1 h), by
        show (fun h => ι (ι.symm (c.1 h))) ∈ P
        simpa using c.2⟩
      invFun := fun f => ⟨fun h => ι (f.1 h), f.2⟩
      left_inv := by
        intro c
        ext h
        simp
      right_inv := by
        intro f
        ext h
        simp
      map_add' := by
        intro a b
        ext h
        simp }
  have hrank : Module.rank ℂ P = Module.rank (Qbar l) P' := by
    refine rank_eq_of_equiv_equiv (fun z => ι.symm z) j ι.symm.bijective ?_
    intro r m
    ext h
    simp [j, smul_eq_mul, map_mul]
  have hfin : Module.finrank ℂ P = Module.finrank (Qbar l) P' := by
    unfold Module.finrank
    rw [hrank]
  have hinv : ∀ c ∈ P', ∀ g : H, (fun h => c (h * g)) ∈ P' := by
    intro c hc g
    exact hP _ hc g
  obtain ⟨c, hc, hbound⟩ := hA (Qbar l) l H hp P' hinv (hfin ▸ hcard)
  refine ⟨fun h => ι (c h), hc, ?_⟩
  intro h
  simpa using hbound h
