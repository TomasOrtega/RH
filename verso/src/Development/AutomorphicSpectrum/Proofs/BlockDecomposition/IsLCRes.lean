import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.FirstChernCompatibleSystem

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.KapSpecProof

variable {R : Type} [CommRing R]

/- English proof (translation)
Use `delta GlobalTheory.EtC.Sec.res`. Rewrite using `[op_comp, Functor.map_comp]`. Both sides reduce to the same expression.
-/
theorem res_comp {G : Shv R} {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (x : Sec G U) :
    Sec.res (k ≫ g) x = Sec.res k (Sec.res g x) := by
  delta GlobalTheory.EtC.Sec.res
  rw [op_comp, Functor.map_comp]
  rfl

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Use `delta CrystallineSemistableComparison.E.primRes`. Both sides reduce to the same expression.
-/
theorem primRes_comp {q : ℕ} {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (ζ : Prim q Γ(U, ⊤)) :
    primRes (k ≫ g) ζ = primRes k (primRes g ζ) := by
  apply Subtype.ext
  delta CrystallineSemistableComparison.E.primRes
  rfl

/- English proof (translation)
Set `f0 : LocallyConstant U Empty` to `⟨fun u => isEmptyElim u, fun s => by`. Use `isOpen_empty` and compare the differences between its conclusion and the goal. Use extensionality with `u`. Conclude with `isEmptyElim u⟩`. Take `⟨W, j, -, -, -, hglue⟩` from `hL U Empty f0`.

Take `⟨z, -, hz⟩` from `hglue R G (fun a => a.elim)`. Conclude with `⟨fun x x' => (hz x (fun a => a.elim)).trans (hz x' (fun a => a.elim)).symm⟩`.
-/
theorem sec_subsingleton (hL : LcCover) {U : Scheme.{0}} [IsEmpty U] (G : Shv R) :
    Subsingleton (Sec G U) := by
  let f0 : LocallyConstant U Empty :=
    ⟨fun u => isEmptyElim u, fun s => by
      convert isOpen_empty
      ext u
      exact isEmptyElim u⟩
  obtain ⟨W, j, -, -, -, hglue⟩ := hL U Empty f0
  obtain ⟨z, -, hz⟩ := hglue R G (fun a => a.elim)
  exact ⟨fun x x' => (hz x (fun a => a.elim)).trans (hz x' (fun a => a.elim)).symm⟩

/- English proof (translation)
Take `⟨W, j, hWf, -, -, hglue⟩` from `hL U ι f`. Take `⟨z, -, hz⟩` from `hglue R G (fun a => Sec.res (j a) x)`. Conclude with `(hz x (fun a => rfl)).trans (hz y (fun a => (h (W a) (j a) a (hWf a)).symm)).symm`.
-/
theorem sec_ext (hL : LcCover) {ι : Type} {U : Scheme.{0}} (f : LocallyConstant U ι) (G : Shv R)
    (x y : Sec G U)
    (h : ∀ (V : Scheme.{0}) (g : V ⟶ U) (a : ι), (∀ v : V, f (g v) = a) → Sec.res g x = Sec.res g y) :
    x = y := by
  obtain ⟨W, j, hWf, -, -, hglue⟩ := hL U ι f
  obtain ⟨z, -, hz⟩ := hglue R G (fun a => Sec.res (j a) x)
  exact (hz x (fun a => rfl)).trans (hz y (fun a => (h (W a) (j a) a (hWf a)).symm)).symm

variable {q : ℕ} {i : ℤ}

/- English proof (translation)
Use `sec_ext hL f _ x y fun V g a hga => ?_` and prove the remaining obligations. Use `delta CrystallineSemistableComparison.E.IsLC at hx hy`. Rewrite using `[hx V g a hga, hy V g a hga]`.
-/
theorem isLC_unique (hL : LcCover) {U : Scheme.{0}} {ζ : Prim q Γ(U, ⊤)}
    {f : LocallyConstant U (ZMod q)} {x y : Sec (tw q i) U} (hx : IsLC i ζ f x) (hy : IsLC i ζ f y) :
    x = y := by
  refine sec_ext hL f _ x y fun V g a hga => ?_
  delta CrystallineSemistableComparison.E.IsLC at hx hy
  rw [hx V g a hga, hy V g a hga]

/- English proof (translation)
Use `delta CrystallineSemistableComparison.E.IsLC`. Establish `hres_smul : ∀ {V W : Scheme.{0}} (g : V ⟶ W) (c : ULift (ZMod q)) (y : Sec (tw q i) W), Sec.res g (c • y) = c • Sec.res g y` using `fun g c y => by delta GlobalTheory.EtC.Sec.res`. Conclude with `map_smul _ c y`. Take `⟨W, j, -, hfac, -, hglue⟩` from `hL U (ZMod q) f`. Take `⟨x, hx, -⟩` from `hglue (ZMod q) (tw q i) (fun a => (⟨a⟩ : ULift (ZMod q)) • twGen i (primRes (j a) ζ))`.

Use `⟨x, fun V g a ha => ?_⟩` and prove the remaining obligations. Take `⟨k, rfl⟩` from `hfac V g a ha`. Rewrite using `[res_comp, hx a, hres_smul, ((hR q i (W a) (primRes (j a) ζ)).1 V k).1, ← primRes_comp]`.
-/
theorem isLC_exists (hL : LcCover) (hR : RepRoot) {U : Scheme.{0}} (ζ : Prim q Γ(U, ⊤))
    (f : LocallyConstant U (ZMod q)) : ∃ x : Sec (tw q i) U, IsLC i ζ f x := by
  delta CrystallineSemistableComparison.E.IsLC
  have hres_smul : ∀ {V W : Scheme.{0}} (g : V ⟶ W) (c : ULift (ZMod q)) (y : Sec (tw q i) W),
      Sec.res g (c • y) = c • Sec.res g y := fun g c y => by
    delta GlobalTheory.EtC.Sec.res
    exact map_smul _ c y
  obtain ⟨W, j, -, hfac, -, hglue⟩ := hL U (ZMod q) f
  obtain ⟨x, hx, -⟩ := hglue (ZMod q) (tw q i)
    (fun a => (⟨a⟩ : ULift (ZMod q)) • twGen i (primRes (j a) ζ))
  refine ⟨x, fun V g a ha => ?_⟩
  obtain ⟨k, rfl⟩ := hfac V g a ha
  rw [res_comp, hx a, hres_smul, ((hR q i (W a) (primRes (j a) ζ)).1 V k).1, ← primRes_comp]

/- English proof (translation)
Use `delta CrystallineSemistableComparison.E.IsLC at hx hx' ⊢`. Introduce `V g a ha`. Establish `hres_smul : ∀ {V W : Scheme.{0}} (g : V ⟶ W) (c : ULift (ZMod q)) (y : Sec (tw q i) W), Sec.res g (c • y) = c • Sec.res g y` using `fun g c y => by delta GlobalTheory.EtC.Sec.res`. Conclude with `map_smul _ c y`. Establish `hcont : Continuous (fun v : V => g v)` using `g.continuous`.

Set `F2 : LocallyConstant V (ZMod q × ZMod q)` to `⟨fun v => (f (g v), f' (g v)), IsLocallyConstant.comp₂ (f.isLocallyConstant.comp_continuous hcont) (f'.isLocallyConstant.comp_continuous hcont) Prod.mk⟩`. Use `sec_ext hL F2 _ _ _ fun V' g' b hb => ?_` and prove the remaining obligations. Break down `isEmpty_or_nonempty V' with hV | ⟨⟨v⟩⟩` into its components or cases. Use `haveI := sec_subsingleton hL (U := V') (tw q i)`. Conclude with `Subsingleton.elim _ _`.

Establish `hb1 : ∀ v, f ((g' ≫ g) v) = b.1` using `fun v => congrArg Prod.fst (hb v)`. Establish `hb2 : ∀ v, f' ((g' ≫ g) v) = b.2` using `fun v => congrArg Prod.snd (hb v)`. Establish `hres_add : ∀ (y y' : Sec (tw q i) U), Sec.res (g' ≫ g) (y + y') = Sec.res (g' ≫ g) y + Sec.res (g' ≫ g) y'` using `fun y y' => by delta GlobalTheory.EtC.Sec.res`. Conclude with `map_add _ y y'`. Establish `hab : a = b.1 + b.2`.

Rewrite using `[← ha (g' v), ← hb1 v, ← hb2 v]`. Both sides reduce to the same expression. Rewrite using `[← res_comp, hres_add, hx V' (g' ≫ g) b.1 hb1, hx' V' (g' ≫ g) b.2 hb2, ← add_smul, hres_smul, ((hR q i V (primRes g ζ)).1 V' g').1, ← primRes_comp, hab]`. Both sides reduce to the same expression.
-/
theorem isLC_add (hL : LcCover) (hR : RepRoot) {U : Scheme.{0}} {ζ : Prim q Γ(U, ⊤)}
    {f f' : LocallyConstant U (ZMod q)} {x x' : Sec (tw q i) U} (hx : IsLC i ζ f x)
    (hx' : IsLC i ζ f' x') : IsLC i ζ (f + f') (x + x') := by
  delta CrystallineSemistableComparison.E.IsLC at hx hx' ⊢
  intro V g a ha
  have hres_smul : ∀ {V W : Scheme.{0}} (g : V ⟶ W) (c : ULift (ZMod q)) (y : Sec (tw q i) W),
      Sec.res g (c • y) = c • Sec.res g y := fun g c y => by
    delta GlobalTheory.EtC.Sec.res
    exact map_smul _ c y
  have hcont : Continuous (fun v : V => g v) := g.continuous
  let F2 : LocallyConstant V (ZMod q × ZMod q) :=
    ⟨fun v => (f (g v), f' (g v)), IsLocallyConstant.comp₂ (f.isLocallyConstant.comp_continuous hcont)
      (f'.isLocallyConstant.comp_continuous hcont) Prod.mk⟩
  refine sec_ext hL F2 _ _ _ fun V' g' b hb => ?_
  rcases isEmpty_or_nonempty V' with hV | ⟨⟨v⟩⟩
  · haveI := sec_subsingleton hL (U := V') (tw q i)
    exact Subsingleton.elim _ _
  have hb1 : ∀ v, f ((g' ≫ g) v) = b.1 := fun v => congrArg Prod.fst (hb v)
  have hb2 : ∀ v, f' ((g' ≫ g) v) = b.2 := fun v => congrArg Prod.snd (hb v)
  have hres_add : ∀ (y y' : Sec (tw q i) U),
      Sec.res (g' ≫ g) (y + y') = Sec.res (g' ≫ g) y + Sec.res (g' ≫ g) y' := fun y y' => by
    delta GlobalTheory.EtC.Sec.res
    exact map_add _ y y'
  have hab : a = b.1 + b.2 := by
    rw [← ha (g' v), ← hb1 v, ← hb2 v]
    rfl
  rw [← res_comp, hres_add, hx V' (g' ≫ g) b.1 hb1, hx' V' (g' ≫ g) b.2 hb2, ← add_smul, hres_smul,
    ((hR q i V (primRes g ζ)).1 V' g').1, ← primRes_comp, hab]
  rfl

/- English proof (translation)
Use `delta CrystallineSemistableComparison.E.IsLC at hx ⊢`. Introduce `W h a ha`. Rewrite using `[← res_comp, hx W (h ≫ g) a ?_, primRes_comp]`. Introduce `w`. Conclude with `ha w`.
-/
theorem isLC_res {U V : Scheme.{0}} {ζ : Prim q Γ(U, ⊤)}
    {f : LocallyConstant U (ZMod q)} {x : Sec (tw q i) U} (hx : IsLC i ζ f x) (g : V ⟶ U) :
    IsLC i (primRes g ζ) (lcRes q g f) (Sec.res g x) := by
  delta CrystallineSemistableComparison.E.IsLC at hx ⊢
  intro W h a ha
  rw [← res_comp, hx W (h ≫ g) a ?_, primRes_comp]
  intro w
  exact ha w

/- English proof (translation)
Introduce `hL hR q i U ζ f`. Establish `hk : ∀ {U' : Scheme.{0}} (ζ' : Prim q Γ(U', ⊤)) (f' : LocallyConstant U' (ZMod q)), IsLC i ζ' f' (kap i ζ' f')`. Introduce `U' ζ' f'`. Establish `hex : ∃ κ : LocallyConstant U' (ZMod q) →+ Sec (tw q i) U', ∀ f'', IsLC i ζ' f'' (κ f'')` using `by choose c hc using fun f'' : LocallyConstant U' (ZMod q) => isLC_exists hL hR (i := i) ζ' f''`. Use `⟨{ toFun := c, map_zero' := ?_, map_add' := fun a b => ?_ }, hc⟩` and prove the remaining obligations.

Establish `h` using `isLC_unique hL (hc (0 + 0)) (isLC_add hL hR (hc 0) (hc 0))`. Simplify using `using h`. Conclude with `isLC_unique hL (hc (a + b)) (isLC_add hL hR (hc a) (hc b))`. Use `delta CrystallineSemistableComparison.E.kap`. Conclude with `GlobalTheory.EtC.pick_spec hex f'`.

Use `⟨hk ζ f, fun x hx => isLC_unique hL hx (hk ζ f), fun V g => ?_⟩` and prove the remaining obligations. Conclude with `isLC_unique hL (isLC_res (hk ζ f) g) (hk _ _)`.
-/
theorem kapSpec : LcCover → RepRoot → KapSpec := by
  intro hL hR q i U ζ f
  have hk : ∀ {U' : Scheme.{0}} (ζ' : Prim q Γ(U', ⊤)) (f' : LocallyConstant U' (ZMod q)),
      IsLC i ζ' f' (kap i ζ' f') := by
    intro U' ζ' f'
    have hex : ∃ κ : LocallyConstant U' (ZMod q) →+ Sec (tw q i) U', ∀ f'', IsLC i ζ' f'' (κ f'') := by
      choose c hc using fun f'' : LocallyConstant U' (ZMod q) => isLC_exists hL hR (i := i) ζ' f''
      refine ⟨{ toFun := c, map_zero' := ?_, map_add' := fun a b => ?_ }, hc⟩
      · have h := isLC_unique hL (hc (0 + 0)) (isLC_add hL hR (hc 0) (hc 0))
        simpa using h
      · exact isLC_unique hL (hc (a + b)) (isLC_add hL hR (hc a) (hc b))
    delta CrystallineSemistableComparison.E.kap
    exact GlobalTheory.EtC.pick_spec hex f'
  refine ⟨hk ζ f, fun x hx => isLC_unique hL hx (hk ζ f), fun V g => ?_⟩
  exact isLC_unique hL (isLC_res (hk ζ f) g) (hk _ _)

end GlobalTheory.CompanionTheory.KapSpecProof
