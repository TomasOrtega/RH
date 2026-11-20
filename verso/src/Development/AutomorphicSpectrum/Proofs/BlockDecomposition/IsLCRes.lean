import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.FirstChernCompatibleSystem

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.KapSpecProof

variable {R : Type} [CommRing R]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem res_comp {G : Shv R} {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (x : Sec G U) :
    Sec.res (k ≫ g) x = Sec.res k (Sec.res g x) := by
  delta GlobalTheory.EtC.Sec.res
  rw [op_comp, Functor.map_comp]
  rfl

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem primRes_comp {q : ℕ} {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (ζ : Prim q Γ(U, ⊤)) :
    primRes (k ≫ g) ζ = primRes k (primRes g ζ) := by
  apply Subtype.ext
  delta CrystallineSemistableComparison.E.primRes
  rfl

/- English proof (translation)
Introduce a local definition for the expression. Apply an available result and prove the equalities needed to match it to the conclusion. By extensionality, compare the relevant components. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Supply the required witnesses or components. A detailed English derivation is pending.
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
Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. A detailed English derivation is pending.
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
Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem isLC_unique (hL : LcCover) {U : Scheme.{0}} {ζ : Prim q Γ(U, ⊤)}
    {f : LocallyConstant U (ZMod q)} {x y : Sec (tw q i) U} (hx : IsLC i ζ f x) (hy : IsLC i ζ f y) :
    x = y := by
  refine sec_ext hL f _ x y fun V g a hga => ?_
  delta CrystallineSemistableComparison.E.IsLC at hx hy
  rw [hx V g a hga, hy V g a hga]

/- English proof (translation)
Establish an intermediate fact. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
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
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Introduce a local definition for the expression. Reduce the conclusion to the remaining proof obligations.

Separate the alternatives or extract the components of the hypothesis. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. A detailed English derivation is pending.
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
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
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
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
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
