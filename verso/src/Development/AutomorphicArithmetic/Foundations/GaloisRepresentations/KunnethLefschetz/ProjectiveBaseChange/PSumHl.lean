import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.ProjectiveBaseChange.AdicTopOf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace CrystallineSemistableComparison ReciprocityTheory.ChartRestriction.G.Geo.Tor UpperTheory.Gal.KunnethLefschetz
open scoped TensorProduct DirectSum

/- English proof (translation)
Unfold `UpperTheory.Gal.KunnethLefschetz.SumHl`. Introduce `hS l _ X r Y j hj n`. Establish `hb : ∀ k : ℕ, Function.Bijective fun (x : Ht (l ^ k) (sch.obj X) n 0) (s : Fin r) => pull (ZMod (l ^ k)) (sch.map (j s)) (tw (l ^ k) 0) n x` using `fun k => hS (ZMod (l ^ k)) (tw (l ^ k) 0) j hj n`. Prove the components needed by the constructor for the conclusion. Introduce `x y h`.

Use `Subtype.ext (funext fun k => (hb k).1 (funext fun s => ?_))` and prove the remaining obligations. Conclude with `congrArg (fun z : Hl l (sch.obj (Y s)) n 0 => z.1 k) (congrFun h s)`. Introduce `y choose x hx using fun k : ℕ => (hb k).2 (fun s => (y s).1 k)`. Use `⟨⟨x, fun k => (hb k).1 (funext fun s => ?_)⟩,` and prove the remaining obligations. Use function extensionality and compare the values at `fun s => Subtype.ext (funext fun k => congrFun (hx k) s)⟩`.

Conclude with `(pull_red _ _ (sch.map (j s)) n 0 (x (k + 1))).trans ((congrArg (red (l ^ (k + 1)) (l ^ k) (sch.obj (Y s)) n 0) (congrFun (hx (k + 1)) s)).trans (((y s).2 k).trans (congrFun (hx k) s).symm))`.
-/
theorem UpperTheory.Gal.KunnethLefschetz.sumHl_holds :
    UpperTheory.Gal.KunnethLefschetz.SumHl := by
  unfold UpperTheory.Gal.KunnethLefschetz.SumHl
  intro hS l _ X r Y j hj n
  have hb : ∀ k : ℕ, Function.Bijective fun (x : Ht (l ^ k) (sch.obj X) n 0) (s : Fin r) =>
      pull (ZMod (l ^ k)) (sch.map (j s)) (tw (l ^ k) 0) n x :=
    fun k => hS (ZMod (l ^ k)) (tw (l ^ k) 0) j hj n
  constructor
  · intro x y h
    refine Subtype.ext (funext fun k => (hb k).1 (funext fun s => ?_))
    exact congrArg (fun z : Hl l (sch.obj (Y s)) n 0 => z.1 k) (congrFun h s)
  · intro y
    choose x hx using fun k : ℕ => (hb k).2 (fun s => (y s).1 k)
    refine ⟨⟨x, fun k => (hb k).1 (funext fun s => ?_)⟩,
      funext fun s => Subtype.ext (funext fun k => congrFun (hx k) s)⟩
    exact (pull_red _ _ (sch.map (j s)) n 0 (x (k + 1))).trans
      ((congrArg (red (l ^ (k + 1)) (l ^ k) (sch.obj (Y s)) n 0) (congrFun (hx (k + 1)) s)).trans
        (((y s).2 k).trans (congrFun (hx k) s).symm))
