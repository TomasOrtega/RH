import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SupEq

section Iso

variable {LL Ks Ks' WL WL' G G' : Type} [Field LL] [NumberField LL] [Field Ks] [NumberField Ks] [Algebra Ks LL]
  [Field Ks'] [NumberField Ks'] [Algebra Ks' LL]
  [AddCommGroup WL] [Module LL WL] [Module Ks WL] [IsScalarTower Ks LL WL] [Module (𝓞 LL) WL] [IsScalarTower (𝓞 LL) LL WL]
  [Module (𝓞 Ks) WL] [IsScalarTower (𝓞 Ks) Ks WL]
  [AddCommGroup WL'] [Module LL WL'] [Module Ks' WL'] [IsScalarTower Ks' LL WL'] [Module (𝓞 LL) WL']
  [IsScalarTower (𝓞 LL) LL WL'] [Module (𝓞 Ks') WL'] [IsScalarTower (𝓞 Ks') Ks' WL']
  {W W' : (LL →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)]
  [∀ σ, NormedAddCommGroup (W' σ)] [∀ σ, InnerProductSpace ℂ (W' σ)] [Group G] [Group G']
  {A : Arith.FormsL LL Ks WL W G} {A' : Arith.FormsL LL Ks' WL' W' G'}

/- English proof (translation)
Rewrite using `[← algebraMap_smul LL c w, map_smul, ← Y.eK_LL, algebraMap_smul]`.
-/
theorem iso_smul (Y : NX.FormsIso A A') (c : Ks) (w : WL) : Y.e (c • w) = Y.eK c • Y.e w := by
  rw [← algebraMap_smul LL c w, map_smul, ← Y.eK_LL, algebraMap_smul]

/- English proof (translation)
Apply `Y.e.injective` to reduce the goal to its premises. Rewrite using `[iso_smul]`. Simplify using the standard rewrite rules.
-/
theorem iso_symm_smul (Y : NX.FormsIso A A') (c : Ks') (y : WL') : Y.e.symm (c • y) = Y.eK.symm c • Y.e.symm y := by
  apply Y.e.injective
  rw [iso_smul]
  simp

/- English proof (translation)
Rewrite using `[← algebraMap_smul Ks' c y, ← algebraMap_smul Ks _ (Y.e.symm y), iso_symm_smul]`. Both sides reduce to the same expression.
-/
theorem iso_symm_smul_int (Y : NX.FormsIso A A') (c : 𝓞 Ks') (y : WL') :
    Y.e.symm (c • y) = RingOfIntegers.mapRingEquiv Y.eK.symm c • Y.e.symm y := by
  rw [← algebraMap_smul Ks' c y, ← algebraMap_smul Ks _ (Y.e.symm y), iso_symm_smul]
  rfl

/- English proof (translation)
Take `⟨⟨T, hT⟩, hS⟩` from `h`. Use `⟨⟨T.image Y.e.symm, ?_⟩, ?_⟩` and prove the remaining obligations. Apply `le_antisymm` to reduce the goal to its premises. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce `x hx`.

Simplify using `only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hx`. Take `⟨t, ht, rfl⟩` from `hx`. Establish `: t ∈ A'.MK` using `hT ▸ Submodule.subset_span ht`. Conclude with `(Y.mkK _).2 (by simpa using this)`. Introduce `x hx`.

Establish `h1 : Y.e x ∈ Submodule.span (𝓞 Ks') (T : Set WL')` using `hT ▸ (Y.mkK x).1 hx`. Establish `h2 : ∀ y ∈ Submodule.span (𝓞 Ks') (T : Set WL'), Y.e.symm y ∈ Submodule.span (𝓞 Ks) ((T.image Y.e.symm : Finset WL) : Set WL)`. Introduce `y hy`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem y hy => exact Submodule.subset_span (by rw [Finset.coe_image]; exact Set.mem_image_of_mem _ hy)`.

Consider the case `zero => simp`. Consider the case `add a b _ _ ha hb => rw [map_add]`. Conclude with `Submodule.add_mem _ ha hb`. Consider the case `smul c a _ ha => rw [iso_symm_smul_int]`. Conclude with `Submodule.smul_mem _ _ ha`.

Simplify using `using h2 _ h1`. Apply `le_antisymm` to reduce the goal to its premises. Conclude with `Submodule.span_le.2 fun x hx => by obtain ⟨h, -⟩ := hx; exact h`. Introduce `x hx`. Establish `h1 : Y.e x ∈ Submodule.span Ks' (A'.MK : Set WL')` using `hS ▸ (Y.wk x).1 hx`.

Establish `h2 : ∀ y ∈ Submodule.span Ks' (A'.MK : Set WL'), Y.e.symm y ∈ Submodule.span Ks (A.MK : Set WL)`. Introduce `y hy`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem y hy => exact Submodule.subset_span ((Y.mkK _).2 (by simpa using hy))`. Consider the case `zero => simp`.

Consider the case `add a b _ _ ha hb => rw [map_add]`. Conclude with `Submodule.add_mem _ ha hb`. Consider the case `smul c a _ ha => rw [iso_symm_smul]`. Conclude with `Submodule.smul_mem _ _ ha`. Simplify using `using h2 _ h1`.
-/
theorem iso_MKFull (Y : NX.FormsIso A A') (h : A'.MKFull) : A.MKFull := by
  classical
  obtain ⟨⟨T, hT⟩, hS⟩ := h
  refine ⟨⟨T.image Y.e.symm, ?_⟩, ?_⟩
  · apply le_antisymm
    · refine Submodule.span_le.2 ?_
      intro x hx
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hx
      obtain ⟨t, ht, rfl⟩ := hx
      have : t ∈ A'.MK := hT ▸ Submodule.subset_span ht
      exact (Y.mkK _).2 (by simpa using this)
    · intro x hx
      have h1 : Y.e x ∈ Submodule.span (𝓞 Ks') (T : Set WL') := hT ▸ (Y.mkK x).1 hx
      have h2 : ∀ y ∈ Submodule.span (𝓞 Ks') (T : Set WL'),
          Y.e.symm y ∈ Submodule.span (𝓞 Ks) ((T.image Y.e.symm : Finset WL) : Set WL) := by
        intro y hy
        induction hy using Submodule.span_induction with
        | mem y hy => exact Submodule.subset_span (by rw [Finset.coe_image]; exact Set.mem_image_of_mem _ hy)
        | zero => simp
        | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
        | smul c a _ ha => rw [iso_symm_smul_int]; exact Submodule.smul_mem _ _ ha
      simpa using h2 _ h1
  · apply le_antisymm
    · exact Submodule.span_le.2 fun x hx => by obtain ⟨h, -⟩ := hx; exact h
    · intro x hx
      have h1 : Y.e x ∈ Submodule.span Ks' (A'.MK : Set WL') := hS ▸ (Y.wk x).1 hx
      have h2 : ∀ y ∈ Submodule.span Ks' (A'.MK : Set WL'),
          Y.e.symm y ∈ Submodule.span Ks (A.MK : Set WL) := by
        intro y hy
        induction hy using Submodule.span_induction with
        | mem y hy => exact Submodule.subset_span ((Y.mkK _).2 (by simpa using hy))
        | zero => simp
        | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
        | smul c a _ ha => rw [iso_symm_smul]; exact Submodule.smul_mem _ _ ha
      simpa using h2 _ h1

/- English proof (translation)
Introduce `g f`. Use `⟨fun hf => (Y.wk _).2 ?_, fun hf => (Y.mkK _).2 ?_⟩` and prove the remaining obligations. Rewrite using `[Y.rho]`. Conclude with `(h _ _).1 ((Y.wk _).1 hf)`. Rewrite using `[Y.rho]`.

Conclude with `(h _ _).2 ((Y.mkK _).1 hf)`.
-/
theorem iso_MKStable (Y : NX.FormsIso A A') (h : A'.MKStable) : A.MKStable := by
  intro g f
  refine ⟨fun hf => (Y.wk _).2 ?_, fun hf => (Y.mkK _).2 ?_⟩
  · rw [Y.rho]; exact (h _ _).1 ((Y.wk _).1 hf)
  · rw [Y.rho]; exact (h _ _).2 ((Y.mkK _).1 hf)

end Iso

section Base

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} [NumberField what₂.LL] [StarRing what₂.LL]
  {LL0 : IntermediateField ℚ what₂.LL} {N : NData R H what₂} {tw : NTw R H what₂ LL0 N} (S : NX.RatDat tw)

open NX

/- English proof (translation)
Set `f : S.Ks →+* FractionRing (tw.O i)` to `ιK S i b`. Establish `h : IsIntegral (tw.O i) (f (a : S.Ks))` using `(RingOfIntegers.isIntegral_coe a).map_of_comp_eq (Int.castRingHom (tw.O i)) f (RingHom.ext_int _ _)`. Conclude with `IsIntegrallyClosed.isIntegral_iff.1 h`.
-/
theorem exists_int_read (i : tw.Tw) (b : Bool) (a : 𝓞 S.Ks) :
    ∃ o : tw.O i, algebraMap (tw.O i) (FractionRing (tw.O i)) o = (ιK S i b (a : S.Ks) : KB S i b) := by
  let f : S.Ks →+* FractionRing (tw.O i) := ιK S i b
  have h : IsIntegral (tw.O i) (f (a : S.Ks)) :=
    (RingOfIntegers.isIntegral_coe a).map_of_comp_eq (Int.castRingHom (tw.O i)) f (RingHom.ext_int _ _)
  exact IsIntegrallyClosed.isIntegral_iff.1 h

/- English proof (translation)
Establish `hn : 0 < orderOf g` using `orderOf_pos g`. Establish `h1 : chiL S j hχ g ^ orderOf g = 1`. Apply `Subtype.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `(((S.A j).chi g : what₂.LLˣ) : what₂.LL) ^ orderOf g = 1`. Rewrite using `[← Units.val_pow_eq_pow_val, ← map_pow, pow_orderOf_eq_one, map_one, Units.val_one]`.

Set `x : FractionRing (tw.O i)` to `((readLL0 S i b (chiL S j hχ g))⁻¹ : KB S i b)`. Establish `h2 : x ^ orderOf g = 1`. Express the relevant statement in the definitionally equal form `((readLL0 S i b (chiL S j hχ g))⁻¹ : KB S i b) ^ orderOf g = 1`. Rewrite using `[inv_pow, ← map_pow, h1, map_one, inv_one]`. Establish `h3 : IsIntegral (tw.O i) x` using `IsIntegral.of_pow hn (by rw [h2]; exact isIntegral_one)`.

Conclude with `IsIntegrallyClosed.isIntegral_iff.1 h3`.
-/
theorem exists_chi_read [Finite S.G] (i : tw.Tw) (b : Bool) (j : ℕ) (hχ : ChiInLL0 S j) (g : S.G) :
    ∃ o : tw.O i, algebraMap (tw.O i) (FractionRing (tw.O i)) o = ((readLL0 S i b (chiL S j hχ g))⁻¹ : KB S i b) := by
  have hn : 0 < orderOf g := orderOf_pos g
  have h1 : chiL S j hχ g ^ orderOf g = 1 := by
    apply Subtype.ext
    change (((S.A j).chi g : what₂.LLˣ) : what₂.LL) ^ orderOf g = 1
    rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_orderOf_eq_one, map_one, Units.val_one]
  let x : FractionRing (tw.O i) := ((readLL0 S i b (chiL S j hχ g))⁻¹ : KB S i b)
  have h2 : x ^ orderOf g = 1 := by
    change ((readLL0 S i b (chiL S j hχ g))⁻¹ : KB S i b) ^ orderOf g = 1
    rw [inv_pow, ← map_pow, h1, map_one, inv_one]
  have h3 : IsIntegral (tw.O i) x := IsIntegral.of_pow hn (by rw [h2]; exact isIntegral_one)
  exact IsIntegrallyClosed.isIntegral_iff.1 h3

variable (i : tw.Tw) (j : ℕ) (b : Bool)

def mkF (y : S.WL j) (h : y ∈ (S.A j).WK) : FmK S j := ⟨y, h⟩

def rdF (c : S.Ks) : FractionRing (tw.O i) := ιK S i b c

def rdK (a : KB S i b) : FractionRing (tw.O i) := a

def oneT (x : FmK S j) : Fm S i j b := ((1 : KB S i b) ⊗ₜ[S.Ks] x : KB S i b ⊗[S.Ks] FmK S j)

/- English proof (translation)
The claim follows from `TensorProduct.tmul_zero _ _`.
-/
theorem oneT_zero : oneT S i j b 0 = 0 := TensorProduct.tmul_zero _ _

/- English proof (translation)
The claim follows from `TensorProduct.tmul_add _ _ _`.
-/
theorem oneT_add (x y : FmK S j) : oneT S i j b (x + y) = oneT S i j b x + oneT S i j b y :=
  TensorProduct.tmul_add _ _ _

/- English proof (translation)
Express the relevant statement in the definitionally equal form `(1 : KB S i b) ⊗ₜ[S.Ks] (c • x) = (ιK S i b c : KB S i b) • ((1 : KB S i b) ⊗ₜ[S.Ks] x)`. Rewrite using `[← TensorProduct.smul_tmul, TensorProduct.smul_tmul']`. Use `congr 1`.
-/
theorem oneT_smul (c : S.Ks) (x : FmK S j) :
    oneT S i j b (c • x) = (rdF S i b c) • oneT S i j b x := by
  change (1 : KB S i b) ⊗ₜ[S.Ks] (c • x) = (ιK S i b c : KB S i b) • ((1 : KB S i b) ⊗ₜ[S.Ks] x)
  rw [← TensorProduct.smul_tmul, TensorProduct.smul_tmul']
  congr 1

/- English proof (translation)
Establish `h1 : (mkF S j (c • y) h') = (c : S.Ks) • (mkF S j y h)` using `Subtype.ext (algebraMap_smul S.Ks c y).symm`. Establish `ho' : algebraMap (tw.O i) (FractionRing (tw.O i)) o = rdF S i b (c : S.Ks)` using `ho`. Rewrite using `[h1, oneT_smul, ← ho', algebraMap_smul]`.
-/
theorem oneT_smul_int (c : 𝓞 S.Ks) (y : S.WL j) (h : y ∈ (S.A j).WK) (h' : c • y ∈ (S.A j).WK) (o : tw.O i)
    (ho : algebraMap (tw.O i) (FractionRing (tw.O i)) o = (ιK S i b (c : S.Ks) : KB S i b)) :
    oneT S i j b (mkF S j (c • y) h') = o • oneT S i j b (mkF S j y h) := by
  have h1 : (mkF S j (c • y) h') = (c : S.Ks) • (mkF S j y h) :=
    Subtype.ext (algebraMap_smul S.Ks c y).symm
  have ho' : algebraMap (tw.O i) (FractionRing (tw.O i)) o = rdF S i b (c : S.Ks) := ho
  rw [h1, oneT_smul, ← ho', algebraMap_smul]

/- English proof (translation)
Take `⟨⟨T, hT⟩, -⟩` from `hF`. Establish `hTW : ∀ t ∈ (T : Set (S.WL j)), t ∈ (S.A j).MK` using `fun t ht => hT ▸ Submodule.subset_span ht`. Set `val : FmK S j → S.WL j` to `fun x => (show ↥(S.A j).WK from x).1`. Establish `hval : Function.Injective val` using `Subtype.val_injective`. Set `gens : Set (Fm S i j b)` to `oneT S i j b '' (val ⁻¹' (T : Set (S.WL j)))`.

Establish `hfin : gens.Finite` using `((T.finite_toSet).preimage hval.injOn).image _`. Establish `aux : ∀ y ∈ Submodule.span (𝓞 S.Ks) (T : Set (S.WL j)), ∃ h : y ∈ (S.A j).WK, oneT S i j b (mkF S j y h) ∈ Submodule.span (tw.O i) gens`. Introduce `y hy`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem y hy`.

Take `⟨h, -⟩` from `hTW y hy`. Conclude with `⟨h, Submodule.subset_span ⟨mkF S j y h, hy, rfl⟩⟩`. Consider the case `zero`. Use `⟨(S.A j).WK.zero_mem, ?_⟩` and prove the remaining obligations. Establish `: oneT S i j b (mkF S j 0 (S.A j).WK.zero_mem) = 0` using `oneT_zero S i j b`.

Rewrite using `[this]`. Conclude with `Submodule.zero_mem _`. Consider the case `add x y _ _ hx hy`. Take `⟨h1, h2⟩` from `hx`. Take `⟨h3, h4⟩` from `hy`.

Use `⟨(S.A j).WK.add_mem h1 h3, ?_⟩` and prove the remaining obligations. Establish `: oneT S i j b (mkF S j (x + y) ((S.A j).WK.add_mem h1 h3)) = oneT S i j b (mkF S j x h1) + oneT S i j b (mkF S j y h3)` using `oneT_add S i j b (mkF S j x h1) (mkF S j y h3)`. Rewrite using `[this]`. Conclude with `Submodule.add_mem _ h2 h4`. Consider the case `smul c x _ hx`.

Take `⟨h1, h2⟩` from `hx`. Establish `h3 : c • x ∈ (S.A j).WK`. Rewrite using `[← algebraMap_smul S.Ks c x]`. Conclude with `(S.A j).WK.smul_mem _ h1`. Take `⟨o, ho⟩` from `exists_int_read S i b c`.

Use `⟨h3, ?_⟩` and prove the remaining obligations. Rewrite using `[oneT_smul_int S i j b c x h1 h3 o ho]`. Conclude with `Submodule.smul_mem _ _ h2`. Use `Submodule.fg_def.2 ⟨gens, hfin, le_antisymm ?_ ?_⟩` and prove the remaining obligations. Use `Submodule.span_le.2 ?_` and prove the remaining obligations.

Introduce and unpack `_ ⟨t, ht, rfl⟩`. Conclude with `Submodule.subset_span ⟨t, hTW _ ht, rfl⟩`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Rewrite `hx` using `[show (S.A j).MK = Submodule.span (𝓞 S.Ks) (T : Set (S.WL j)) from hT.symm]`.

Take `⟨h, h'⟩` from `aux _ hx`. Conclude with `h'`.
-/
theorem Bsup_fg (hF : (S.A j).MKFull) : (Bsup S i j b).FG := by
  obtain ⟨⟨T, hT⟩, -⟩ := hF
  have hTW : ∀ t ∈ (T : Set (S.WL j)), t ∈ (S.A j).MK := fun t ht => hT ▸ Submodule.subset_span ht
  let val : FmK S j → S.WL j := fun x => (show ↥(S.A j).WK from x).1
  have hval : Function.Injective val := Subtype.val_injective
  let gens : Set (Fm S i j b) := oneT S i j b '' (val ⁻¹' (T : Set (S.WL j)))
  have hfin : gens.Finite := ((T.finite_toSet).preimage hval.injOn).image _
  have aux : ∀ y ∈ Submodule.span (𝓞 S.Ks) (T : Set (S.WL j)), ∃ h : y ∈ (S.A j).WK,
      oneT S i j b (mkF S j y h) ∈ Submodule.span (tw.O i) gens := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨h, -⟩ := hTW y hy
      exact ⟨h, Submodule.subset_span ⟨mkF S j y h, hy, rfl⟩⟩
    | zero =>
      refine ⟨(S.A j).WK.zero_mem, ?_⟩
      have : oneT S i j b (mkF S j 0 (S.A j).WK.zero_mem) = 0 := oneT_zero S i j b
      rw [this]
      exact Submodule.zero_mem _
    | add x y _ _ hx hy =>
      obtain ⟨h1, h2⟩ := hx
      obtain ⟨h3, h4⟩ := hy
      refine ⟨(S.A j).WK.add_mem h1 h3, ?_⟩
      have : oneT S i j b (mkF S j (x + y) ((S.A j).WK.add_mem h1 h3)) =
          oneT S i j b (mkF S j x h1) + oneT S i j b (mkF S j y h3) :=
        oneT_add S i j b (mkF S j x h1) (mkF S j y h3)
      rw [this]
      exact Submodule.add_mem _ h2 h4
    | smul c x _ hx =>
      obtain ⟨h1, h2⟩ := hx
      have h3 : c • x ∈ (S.A j).WK := by
        rw [← algebraMap_smul S.Ks c x]
        exact (S.A j).WK.smul_mem _ h1
      obtain ⟨o, ho⟩ := exists_int_read S i b c
      refine ⟨h3, ?_⟩
      rw [oneT_smul_int S i j b c x h1 h3 o ho]
      exact Submodule.smul_mem _ _ h2
  refine Submodule.fg_def.2 ⟨gens, hfin, le_antisymm ?_ ?_⟩
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨t, ht, rfl⟩
    exact Submodule.subset_span ⟨t, hTW _ ht, rfl⟩
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨x, hx, rfl⟩
    rw [show (S.A j).MK = Submodule.span (𝓞 S.Ks) (T : Set (S.WL j)) from hT.symm] at hx
    obtain ⟨h, h'⟩ := aux _ hx
    exact h'

/- English proof (translation)
Take `⟨-, hS⟩` from `hF`. Set `B` to `Submodule.span (FractionRing (tw.O i)) (Bsup S i j b : Set (Fm S i j b))`. Establish `aux : ∀ y ∈ Submodule.span S.Ks ((S.A j).MK : Set (S.WL j)), ∃ h : y ∈ (S.A j).WK, oneT S i j b (mkF S j y h) ∈ B`. Introduce `y hy`. Proceed by induction on `hy using Submodule.span_induction with`.

Consider the case `mem y hy`. Take `⟨h, h'⟩` from `id hy`. Conclude with `⟨h, Submodule.subset_span (Submodule.subset_span ⟨mkF S j y h, hy, rfl⟩)⟩`. Consider the case `zero`. Use `⟨(S.A j).WK.zero_mem, ?_⟩` and prove the remaining obligations.

Establish `: oneT S i j b (mkF S j 0 (S.A j).WK.zero_mem) = 0` using `oneT_zero S i j b`. Rewrite using `[this]`. Conclude with `Submodule.zero_mem _`. Consider the case `add x y _ _ hx hy`. Take `⟨h1, h2⟩` from `hx`.

Take `⟨h3, h4⟩` from `hy`. Use `⟨(S.A j).WK.add_mem h1 h3, ?_⟩` and prove the remaining obligations. Establish `: oneT S i j b (mkF S j (x + y) ((S.A j).WK.add_mem h1 h3)) = oneT S i j b (mkF S j x h1) + oneT S i j b (mkF S j y h3)` using `oneT_add S i j b (mkF S j x h1) (mkF S j y h3)`. Rewrite using `[this]`. Conclude with `Submodule.add_mem _ h2 h4`.

Consider the case `smul c x _ hx`. Take `⟨h1, h2⟩` from `hx`. Use `⟨(S.A j).WK.smul_mem c h1, ?_⟩` and prove the remaining obligations. Establish `: oneT S i j b (mkF S j (c • x) ((S.A j).WK.smul_mem c h1)) = (rdF S i b c) • oneT S i j b (mkF S j x h1)` using `oneT_smul S i j b c (mkF S j x h1)`. Rewrite using `[this]`.

Conclude with `Submodule.smul_mem _ _ h2`. Establish `hall : ∀ (a : KB S i b) (x : FmK S j), ((a ⊗ₜ[S.Ks] x : KB S i b ⊗[S.Ks] FmK S j) : Fm S i j b) ∈ B`. Introduce `a x`. Establish `hx : (show ↥(S.A j).WK from x).1 ∈ Submodule.span S.Ks ((S.A j).MK : Set (S.WL j))`. Rewrite using `[hS]`.

Conclude with `(show ↥(S.A j).WK from x).2`. Take `⟨h, h'⟩` from `aux _ hx`. Establish `e : ((a ⊗ₜ[S.Ks] x : KB S i b ⊗[S.Ks] FmK S j) : Fm S i j b) = (rdK S i b a) • oneT S i j b x`. Express the relevant statement in the definitionally equal form `a ⊗ₜ[S.Ks] x = a • ((1 : KB S i b) ⊗ₜ[S.Ks] x)`. Rewrite using `[TensorProduct.smul_tmul', smul_eq_mul, mul_one]`.

Rewrite using `[e]`. Conclude with `Submodule.smul_mem _ _ h'`. Use `eq_top_iff.2 fun t _ => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `t ∈ B`. Proceed by induction on `(show KB S i b ⊗[S.Ks] FmK S j from t) using TensorProduct.induction_on with`.

Consider the case `zero => exact Submodule.zero_mem _`. Consider the case `tmul a x => exact hall a x`. Consider the case `add x y hx hy => exact Submodule.add_mem _ hx hy`.
-/
theorem Bsup_span (hF : (S.A j).MKFull) :
    Submodule.span (FractionRing (tw.O i)) (Bsup S i j b : Set (Fm S i j b)) = ⊤ := by
  obtain ⟨-, hS⟩ := hF
  let B := Submodule.span (FractionRing (tw.O i)) (Bsup S i j b : Set (Fm S i j b))
  have aux : ∀ y ∈ Submodule.span S.Ks ((S.A j).MK : Set (S.WL j)), ∃ h : y ∈ (S.A j).WK,
      oneT S i j b (mkF S j y h) ∈ B := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨h, h'⟩ := id hy
      exact ⟨h, Submodule.subset_span (Submodule.subset_span ⟨mkF S j y h, hy, rfl⟩)⟩
    | zero =>
      refine ⟨(S.A j).WK.zero_mem, ?_⟩
      have : oneT S i j b (mkF S j 0 (S.A j).WK.zero_mem) = 0 := oneT_zero S i j b
      rw [this]
      exact Submodule.zero_mem _
    | add x y _ _ hx hy =>
      obtain ⟨h1, h2⟩ := hx
      obtain ⟨h3, h4⟩ := hy
      refine ⟨(S.A j).WK.add_mem h1 h3, ?_⟩
      have : oneT S i j b (mkF S j (x + y) ((S.A j).WK.add_mem h1 h3)) =
          oneT S i j b (mkF S j x h1) + oneT S i j b (mkF S j y h3) :=
        oneT_add S i j b (mkF S j x h1) (mkF S j y h3)
      rw [this]
      exact Submodule.add_mem _ h2 h4
    | smul c x _ hx =>
      obtain ⟨h1, h2⟩ := hx
      refine ⟨(S.A j).WK.smul_mem c h1, ?_⟩
      have : oneT S i j b (mkF S j (c • x) ((S.A j).WK.smul_mem c h1)) =
          (rdF S i b c) • oneT S i j b (mkF S j x h1) :=
        oneT_smul S i j b c (mkF S j x h1)
      rw [this]
      exact Submodule.smul_mem _ _ h2
  have hall : ∀ (a : KB S i b) (x : FmK S j),
      ((a ⊗ₜ[S.Ks] x : KB S i b ⊗[S.Ks] FmK S j) : Fm S i j b) ∈ B := by
    intro a x
    have hx : (show ↥(S.A j).WK from x).1 ∈ Submodule.span S.Ks ((S.A j).MK : Set (S.WL j)) := by
      rw [hS]; exact (show ↥(S.A j).WK from x).2
    obtain ⟨h, h'⟩ := aux _ hx
    have e : ((a ⊗ₜ[S.Ks] x : KB S i b ⊗[S.Ks] FmK S j) : Fm S i j b) =
        (rdK S i b a) • oneT S i j b x := by
      change a ⊗ₜ[S.Ks] x = a • ((1 : KB S i b) ⊗ₜ[S.Ks] x)
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [e]
    exact Submodule.smul_mem _ _ h'
  refine eq_top_iff.2 fun t _ => ?_
  change t ∈ B
  induction (show KB S i b ⊗[S.Ks] FmK S j from t) using TensorProduct.induction_on with
  | zero => exact Submodule.zero_mem _
  | tmul a x => exact hall a x
  | add x y hx hy => exact Submodule.add_mem _ hx hy

/- English proof (translation)
Take `⟨o, ho⟩` from `exists_chi_read S i b j hχ (S.eG.symm g)`. Proceed by induction on `hf using Submodule.span_induction with`. Consider the case `mem f hf`. Take `⟨x, hx, rfl⟩` from `hf`. Establish `e : actG S i j b hst hχ g ((1 : KB S i b) ⊗ₜ[S.Ks] x : KB S i b ⊗[S.Ks] FmK S j) = o • oneT S i j b (rhoKG S j hst (S.eG.symm g) x)`.

Rewrite using `[← algebraMap_smul (FractionRing (tw.O i)) o, ho]`. Express the relevant statement in the definitionally equal form `((readLL0 S i b (chiL S j hχ (S.eG.symm g)))⁻¹ • Module.End.baseChangeHom S.Ks (KB S i b) (FmK S j) (rhoKG S j hst (S.eG.symm g))) ((1 : KB S i b) ⊗ₜ[S.Ks] x) = _`. Rewrite using `[LinearMap.smul_apply]`. Both sides reduce to the same expression. Rewrite using `[e]`.

Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, hM _ _ hx, rfl⟩)`. Consider the case `zero => rw [map_zero]`. Conclude with `Submodule.zero_mem _`. Consider the case `add x y _ _ hx hy => rw [map_add]`. Conclude with `Submodule.add_mem _ hx hy`.

Consider the case `smul c x _ hx`. Rewrite using `[← algebraMap_smul (FractionRing (tw.O i)) c x, map_smul, algebraMap_smul]`. Conclude with `Submodule.smul_mem _ _ hx`.
-/
theorem actG_Bsup [Finite S.G] (hst : RhoStab S j) (hχ : ChiInLL0 S j)
    (hM : ∀ g x, x ∈ (S.A j).MK → (S.A j).ρ g x ∈ (S.A j).MK) (g : G0g N) (f : Fm S i j b)
    (hf : f ∈ Bsup S i j b) : actG S i j b hst hχ g f ∈ Bsup S i j b := by
  obtain ⟨o, ho⟩ := exists_chi_read S i b j hχ (S.eG.symm g)
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨x, hx, rfl⟩ := hf
    have e : actG S i j b hst hχ g ((1 : KB S i b) ⊗ₜ[S.Ks] x : KB S i b ⊗[S.Ks] FmK S j) =
        o • oneT S i j b (rhoKG S j hst (S.eG.symm g) x) := by
      rw [← algebraMap_smul (FractionRing (tw.O i)) o, ho]
      change ((readLL0 S i b (chiL S j hχ (S.eG.symm g)))⁻¹ •
        Module.End.baseChangeHom S.Ks (KB S i b) (FmK S j) (rhoKG S j hst (S.eG.symm g)))
          ((1 : KB S i b) ⊗ₜ[S.Ks] x) = _
      rw [LinearMap.smul_apply]
      rfl
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, hM _ _ hx, rfl⟩)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
    rw [← algebraMap_smul (FractionRing (tw.O i)) c x, map_smul, algebraMap_smul]
    exact Submodule.smul_mem _ _ hx

end Base

section Tied

open Formalism.IndefR.Links NX

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
  {A3 : Formalism.L2.DIV.FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

set_option synthInstance.maxHeartbeats 400000 in

/- English proof (translation)
Establish `key : ∀ j, j ∈ Finset.Icc 1 D.R.m → ∃ k : Fin D.R.m, j = (k : ℕ) + 1`. Introduce `j hj`. Take `⟨h1, h2⟩` from `Finset.mem_Icc.1 hj`. Conclude with `⟨⟨j - 1, by omega⟩, by simp only; omega⟩`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Introduce `i _ j hj b g f hf`. Take `⟨h1, h2⟩` from `Finset.mem_Icc.1 hj`. Take `⟨k, rfl⟩` from `key j hj`. Use `haveI : Finite S.G := Finite.of_equiv G (Y.fi k).eG.symm.toEquiv`. Establish `hst` using `iso_MKStable (Y.fi k) (hI k).2.2`.

Rewrite using `[hEq i _ b h1 h2, Y.act]`. Conclude with `actG_Bsup S i _ b (Y.rho _ h1 h2) (Y.chi _ h1 h2) (fun g x hx => (hst g x).2 hx) g _ ((hEq i _ b h1 h2 f).1 hf)`. Introduce `i _ j hj b`. Take `⟨h1, h2⟩` from `Finset.mem_Icc.1 hj`. Take `⟨k, rfl⟩` from `key j hj`.

Establish `hF` using `iso_MKFull (Y.fi k) (hI k).2.1`. Set `e` to `Y.eF i _ b h1 h2`. Set `eO` to `e.restrictScalars (D.ntw.O i)`. Establish `hB : D.nexp.Bsup i _ b = (Bsup S i _ b).map eO.symm.toLinearMap`. Use extensionality with `x`.

Rewrite using `[Submodule.mem_map_equiv]`. Conclude with `hEq i _ b h1 h2 x`. Use `⟨hB ▸ (Bsup_fg S i _ b hF).map _, ?_⟩` and prove the remaining obligations. Establish `hC : (D.nexp.Bsup i ((k : ℕ) + 1) b : Set (D.nexp.Fm i ((k : ℕ) + 1) b)) = e.symm.toLinearMap '' (Bsup S i ((k : ℕ) + 1) b : Set (Fm S i ((k : ℕ) + 1) b))`. Rewrite using `[hB]`.

Both sides reduce to the same expression. Rewrite using `[hC, ← Submodule.map_span, Bsup_span S i _ b hF, Submodule.map_top]`. Conclude with `LinearEquiv.range e.symm`.
-/
theorem sup_of_tied (Rl : RealDat3 D A3 Ks) (cG : Formalism.L2.DIV.G0 Rl.Pg D.R.r ≃* G0g D.nd) (S : RatDat D.ntw)
    (Y : NExpRealS Rl cG S)
    (hEq : ∀ i j b (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (x : D.nexp.Fm i j b), x ∈ D.nexp.Bsup i j b ↔ Y.eF i j b h1 h2 x ∈ Bsup S i j b)
    (hI : RealDat.LIntegral Rl.toRealDat) : SupG D ∧ SupFull D := by
  have key : ∀ j, j ∈ Finset.Icc 1 D.R.m → ∃ k : Fin D.R.m, j = (k : ℕ) + 1 := by
    intro j hj
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hj
    exact ⟨⟨j - 1, by omega⟩, by simp only; omega⟩
  refine ⟨?_, ?_⟩
  · intro i _ j hj b g f hf
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hj
    obtain ⟨k, rfl⟩ := key j hj
    haveI : Finite S.G := Finite.of_equiv G (Y.fi k).eG.symm.toEquiv
    have hst := iso_MKStable (Y.fi k) (hI k).2.2
    rw [hEq i _ b h1 h2, Y.act]
    exact actG_Bsup S i _ b (Y.rho _ h1 h2) (Y.chi _ h1 h2) (fun g x hx => (hst g x).2 hx) g _
      ((hEq i _ b h1 h2 f).1 hf)
  · intro i _ j hj b
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hj
    obtain ⟨k, rfl⟩ := key j hj
    have hF := iso_MKFull (Y.fi k) (hI k).2.1
    let e := Y.eF i _ b h1 h2
    let eO := e.restrictScalars (D.ntw.O i)
    have hB : D.nexp.Bsup i _ b = (Bsup S i _ b).map eO.symm.toLinearMap := by
      ext x
      rw [Submodule.mem_map_equiv]
      exact hEq i _ b h1 h2 x
    refine ⟨hB ▸ (Bsup_fg S i _ b hF).map _, ?_⟩
    have hC : (D.nexp.Bsup i ((k : ℕ) + 1) b : Set (D.nexp.Fm i ((k : ℕ) + 1) b)) = e.symm.toLinearMap '' (Bsup S i ((k : ℕ) + 1) b : Set (Fm S i ((k : ℕ) + 1) b)) := by
      rw [hB]
      rfl
    rw [hC, ← Submodule.map_span, Bsup_span S i _ b hF, Submodule.map_top]
    exact LinearEquiv.range e.symm

end Tied

/- English proof (translation)
Introduce `D G _ _ Pl0 I0 T A3 Ks _ _ _ R cG S YS hEq hI`. Conclude with `sup_of_tied R cG S YS hEq hI`.
-/
theorem supG_supFull_of_eq : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS R cG S), (∀ i j b (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (x : D.nexp.Fm i j b), x ∈ D.nexp.Bsup i j b ↔ YS.eF i j b h1 h2 x ∈ NX.Bsup S i j b) → R.toRealDat.LIntegral → SupG D ∧ SupFull D := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R cG S YS hEq hI
  exact sup_of_tied R cG S YS hEq hI

end GlobalTheory.SupEq
