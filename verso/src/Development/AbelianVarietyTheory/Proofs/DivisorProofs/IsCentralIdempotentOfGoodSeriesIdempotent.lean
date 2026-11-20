import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.CuspLatticeAnyLevel
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnipotentLatticeMembership
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompletelySplitPrimeHostPlaceProperties
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTypesIdempotentCoefficients

noncomputable section

namespace GlobalTheory.GoodLatCompare

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.IndefR.Arith Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.GoodBasisCentralIdempotents GlobalTheory.IndefiniteRowSideFullHecke.UnipotentLatticeMembership

section Clause

variable {LL Ks : Type} [Field LL] [NumberField LL] [Field Ks] [NumberField Ks] [Algebra Ks LL]
variable {WL : Type} [AddCommGroup WL] [Module LL WL] [Module Ks WL] [IsScalarTower Ks LL WL]
  [Module (𝓞 LL) WL] [IsScalarTower (𝓞 LL) LL WL] [Module (𝓞 Ks) WL] [IsScalarTower (𝓞 Ks) Ks WL]
variable {W : (LL →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)]
variable {G G' : Type} [Group G] [Fintype G] [Group G'] [Fintype G']

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem isGoodBasis_iff (A : FormsL LL Ks WL W G) (J0 : Subgroup G) (lam0 : J0 →* LLˣ) (eC : G → LL) {d : ℕ}
    (b : Fin d → WL) : IsGoodBasis A J0 lam0 eC b ↔ IsCoord A J0 lam0 eC b := Iff.rfl

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2⟩`. Take `⟨b, hb⟩` from `exists_isGoodBasis A J0 lam0 eC`. Conclude with `⟨⟨_, b, hb⟩, fun d b hb => ⟨hb, h2 d b hb⟩⟩`. Introduce and unpack `⟨⟨d, b, hb⟩, h2⟩`.

Use `⟨?_, fun d b hb => (h2 d b hb).2⟩` and prove the remaining obligations. Rewrite using `[← hb.2]`. Conclude with `FiniteDimensional.span_of_finite LL (Set.finite_range b)`.
-/
theorem mjFull_iff (A : FormsL LL Ks WL W G) (J0 : Subgroup G) (lam0 : J0 →* LLˣ) (eC : G → LL) :
    MjFull A J0 lam0 eC ↔ MjLattice A J0 lam0 eC := by
  constructor
  · rintro ⟨h1, h2⟩
    obtain ⟨b, hb⟩ := exists_isGoodBasis A J0 lam0 eC
    exact ⟨⟨_, b, hb⟩, fun d b hb => ⟨hb, h2 d b hb⟩⟩
  · rintro ⟨⟨d, b, hb⟩, h2⟩
    refine ⟨?_, fun d b hb => (h2 d b hb).2⟩
    rw [← hb.2]
    exact FiniteDimensional.span_of_finite LL (Set.finite_range b)

/- English proof (translation)
Establish `hT : A'.typeP J0' lam0' = A.typeP J0 lam0`. Use extensionality with `F`. Rewrite using `[FormsL.mem_typeP, FormsL.mem_typeP]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `h ⟨p, hp⟩`.

Take `⟨q, rfl⟩` from `e.surjective p`. Use `h ⟨q, (hJ q).2 hp⟩` as an intermediate fact. Rewrite `this` using `[hρ, hχ, hl _ _ hp]`. Then use the resulting hypothesis. Introduce and unpack `h ⟨q, hq⟩`. Use `h ⟨e q, (hJ q).1 hq⟩` as an intermediate fact.

Rewrite using `[hρ, hχ, hl _ _ ((hJ q).1 hq)]`. Conclude with `this`. Establish `hE : A'.eOp eC' = A.eOp eC`. Unfold `FormsL.eOp`. Conclude with `Fintype.sum_equiv e.toEquiv _ _ fun g => by rw [he, hρ, hχ]; rfl`.

Establish `hG : A'.good eC' = A.good eC` using `by unfold FormsL.good; rw [hE]`. Establish `hW : A'.Wgood J0' lam0' eC' = A.Wgood J0 lam0 eC` using `by unfold FormsL.Wgood; rw [hT, hG]`. Establish `hMj : A'.Mj J0' lam0' eC' = A.Mj J0 lam0 eC` using `by unfold FormsL.Mj FormsL.Mall; rw [hT, hG, hM]`. Unfold `MjLattice MjLatticeIn IsCoord FormsL.Mcoord`. Rewrite using `[hW, hMj]`.
-/
theorem mjLattice_congr (A : FormsL LL Ks WL W G) (A' : FormsL LL Ks WL W G') (e : G' ≃* G)
    (hM : A'.MK = A.MK) (hρ : ∀ g, A'.ρ g = A.ρ (e g)) (hχ : ∀ g, A'.chi g = A.chi (e g))
    (J0 : Subgroup G) (lam0 : J0 →* LLˣ) (J0' : Subgroup G') (lam0' : J0' →* LLˣ)
    (hJ : ∀ g, g ∈ J0' ↔ e g ∈ J0) (hl : ∀ g (h' : g ∈ J0') (h : e g ∈ J0), lam0' ⟨g, h'⟩ = lam0 ⟨e g, h⟩)
    (eC : G → LL) (eC' : G' → LL) (he : ∀ g, eC' g = eC (e g)) :
    MjLattice A' J0' lam0' eC' ↔ MjLattice A J0 lam0 eC := by
  have hT : A'.typeP J0' lam0' = A.typeP J0 lam0 := by
    ext F
    rw [FormsL.mem_typeP, FormsL.mem_typeP]
    constructor
    · rintro h ⟨p, hp⟩
      obtain ⟨q, rfl⟩ := e.surjective p
      have := h ⟨q, (hJ q).2 hp⟩
      rwa [hρ, hχ, hl _ _ hp] at this
    · rintro h ⟨q, hq⟩
      have := h ⟨e q, (hJ q).1 hq⟩
      rw [hρ, hχ, hl _ _ ((hJ q).1 hq)]
      exact this
  have hE : A'.eOp eC' = A.eOp eC := by
    unfold FormsL.eOp
    exact Fintype.sum_equiv e.toEquiv _ _ fun g => by rw [he, hρ, hχ]; rfl
  have hG : A'.good eC' = A.good eC := by unfold FormsL.good; rw [hE]
  have hW : A'.Wgood J0' lam0' eC' = A.Wgood J0 lam0 eC := by unfold FormsL.Wgood; rw [hT, hG]
  have hMj : A'.Mj J0' lam0' eC' = A.Mj J0 lam0 eC := by unfold FormsL.Mj FormsL.Mall; rw [hT, hG, hM]
  unfold MjLattice MjLatticeIn IsCoord FormsL.Mcoord
  rw [hW, hMj]

omit [NumberField LL] in

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun g x => by simpa using h.1 (e g) (e x), fun g => by refine Eq.trans ?_ (h.2 (e g)) exact Fintype.sum_equiv e.toEquiv _ _ fun x => by simp⟩`.
-/
theorem isCentralIdem_comp (e : G' ≃* G) {eC : G → LL} (h : IsCentralIdem eC) : IsCentralIdem (fun g => eC (e g)) :=
  ⟨fun g x => by simpa using h.1 (e g) (e x), fun g => by
    refine Eq.trans ?_ (h.2 (e g))
    exact Fintype.sum_equiv e.toEquiv _ _ fun x => by simp⟩

end Clause

section Forms

variable {D : D7} (T : Core D) (j : ℕ) (w : WeightFamilies.Wt D j)
variable {LL : Type} [Field LL] [NumberField LL] [Algebra T.Q.c.F LL]
variable {WL : Type} [AddCommGroup WL] [Module LL WL] [Module T.Q.c.F WL] [IsScalarTower T.Q.c.F LL WL]
  [Module (𝓞 T.Q.c.F) WL] [IsScalarTower (𝓞 T.Q.c.F) T.Q.c.F WL]
variable {W : (LL →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)]
variable {G : Type} [Group G]

/- English proof (translation)
Use `⟨h.1, h.2.1, fun f => ?_⟩` and prove the remaining obligations. Establish `hf : ι f ∈ A.WK` using `h.2.1 ▸ LinearMap.mem_range_self ι f`. Conclude with `⟨fun ⟨h', hh⟩ lp => (h.2.2 lp f h').1 (hh lp), fun hh => ⟨hf, fun lp => (h.2.2 lp f hf).2 (hh lp)⟩⟩`.
-/
theorem isFormsOf_of_carriesCusp {A : FormsL LL T.Q.c.F WL W G} {ι : Cusp T j w →ₗ[T.Q.c.F] WL}
    (h : CarriesCusp T j w A ι) : IsFormsOf T j (wtA w) w.n A ι := by
  refine ⟨h.1, h.2.1, fun f => ?_⟩
  have hf : ι f ∈ A.WK := h.2.1 ▸ LinearMap.mem_range_self ι f
  exact ⟨fun ⟨h', hh⟩ lp => (h.2.2 lp f h').1 (hh lp), fun hh => ⟨hf, fun lp => (h.2.2 lp f hf).2 (hh lp)⟩⟩

/- English proof (translation)
Introduce `x y hxy`. Apply `incl_injective (K := K) (L := L) (M := M)` to reduce the goal to its premises. Apply `h.equiv.injective` to reduce the goal to its premises. Use `show h.equiv (1 ⊗ₜ x) = h.equiv (1 ⊗ₜ y)`. Rewrite using `[h.equiv_tmul, h.equiv_tmul, hxy]`.
-/
theorem injective_of_baseChange {K L M N : Type} [Field K] [Field L] [Algebra K L] [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] [Module L N] [IsScalarTower K L N] {ι : M →ₗ[K] N} (h : IsBaseChange L ι) :
    Function.Injective ι := by
  intro x y hxy
  apply incl_injective (K := K) (L := L) (M := M)
  apply h.equiv.injective
  show h.equiv (1 ⊗ₜ x) = h.equiv (1 ⊗ₜ y)
  rw [h.equiv_tmul, h.equiv_tmul, hxy]

/- English proof (translation)
Establish `hi` using `injective_of_baseChange h.1`. Set `u` to `(LinearEquiv.ofInjective ι hi).symm`. Establish `hu : ∀ f hf, u ⟨ι f, hf⟩ = f` using `fun f hf => by rw [LinearEquiv.symm_apply_eq]; rfl`. Set `A' : FormsL LL T.Q.c.F WL W G` to `{ WK := LinearMap.range ι Pt := T.PtM j nrm := fun lp y x => T.nrmM j lp y (u x : T.R j) nrm_nonneg := fun lp y x => (nrmM_laws T j lp y).1 _ nrm_zero := fun lp y => by rw [map_zero]; exact (nrmM_laws T j lp y).2.1 nrm_add := fun lp y x x' => by rw [map_add]; exact (nrmM_laws T j …`. Establish `hc : CarriesCusp T j w A' ι` using `⟨h.1, rfl, fun lp f hf => forall_congr' fun y => by show T.nrmM j lp y (u ⟨ι f, hf⟩ : T.R j) ≤ 1 ↔ _`.

Rewrite using `[hu]⟩`. Use `⟨A', hc, ?_, rfl, rfl⟩` and prove the remaining obligations. Establish `h'` using `isFormsOf_of_carriesCusp T j w hc`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion.

Introduce `hx`. Take `⟨f, rfl⟩ : x ∈ LinearMap.range ι` from `hx.1`. Conclude with `(h.2.2 f).2 ((h'.2.2 f).1 hx)`. Introduce `hx`. Take `⟨f, rfl⟩ : x ∈ LinearMap.range ι` from `h.2.1 ▸ hx.1`.

Conclude with `(h'.2.2 f).2 ((h.2.2 f).1 hx)`.
-/
theorem exists_carriesCusp {A : FormsL LL T.Q.c.F WL W G} {ι : Cusp T j w →ₗ[T.Q.c.F] WL}
    (h : IsFormsOf T j (wtA w) w.n A ι) :
    ∃ A' : FormsL LL T.Q.c.F WL W G, CarriesCusp T j w A' ι ∧ A'.MK = A.MK ∧ A'.ρ = A.ρ ∧ A'.chi = A.chi := by
  have hi := injective_of_baseChange h.1
  let u := (LinearEquiv.ofInjective ι hi).symm
  have hu : ∀ f hf, u ⟨ι f, hf⟩ = f := fun f hf => by rw [LinearEquiv.symm_apply_eq]; rfl
  let A' : FormsL LL T.Q.c.F WL W G :=
    { WK := LinearMap.range ι
      Pt := T.PtM j
      nrm := fun lp y x => T.nrmM j lp y (u x : T.R j)
      nrm_nonneg := fun lp y x => (nrmM_laws T j lp y).1 _
      nrm_zero := fun lp y => by rw [map_zero]; exact (nrmM_laws T j lp y).2.1
      nrm_add := fun lp y x x' => by rw [map_add]; exact (nrmM_laws T j lp y).2.2.1 _ _
      nrm_smul := fun lp y a x => by rw [u.map_smul]; exact (nrmM_laws T j lp y).2.2.2 _ _
      towKs := A.towKs, ρ := A.ρ, chi := A.chi, j := A.j }
  have hc : CarriesCusp T j w A' ι := ⟨h.1, rfl, fun lp f hf => forall_congr' fun y => by
    show T.nrmM j lp y (u ⟨ι f, hf⟩ : T.R j) ≤ 1 ↔ _
    rw [hu]⟩
  refine ⟨A', hc, ?_, rfl, rfl⟩
  have h' := isFormsOf_of_carriesCusp T j w hc
  ext x
  constructor
  · intro hx
    obtain ⟨f, rfl⟩ : x ∈ LinearMap.range ι := hx.1
    exact (h.2.2 f).2 ((h'.2.2 f).1 hx)
  · intro hx
    obtain ⟨f, rfl⟩ : x ∈ LinearMap.range ι := h.2.1 ▸ hx.1
    exact (h'.2.2 f).2 ((h.2.2 f).1 hx)

end Forms

section Local

variable {κ κ' : Type} [CommRing κ] [CommRing κ'] {r : ℕ}

def glEquiv (i : κ ≃+* κ') (r : ℕ) : GL (Fin r) κ ≃ GL (Fin r) κ' where
  toFun := Matrix.GeneralLinearGroup.map (i : κ →+* κ')
  invFun := Matrix.GeneralLinearGroup.map (i.symm : κ' →+* κ)
  left_inv g := by ext a b; simp
  right_inv g := by ext a b; simp

/- English proof (translation)
Use `and_congr (forall_congr' fun a => forall_congr' fun b => imp_congr_right fun _ => ?_) (forall_congr' fun a => ?_)` and prove the remaining obligations. Conclude with `map_eq_zero_iff i i.injective`. Conclude with `map_eq_one_iff i i.injective`.
-/
theorem map_mem_unip (i : κ ≃+* κ') (g : GL (Fin r) κ) :
    Matrix.GeneralLinearGroup.map (i : κ →+* κ') g ∈ unip κ' r ↔ g ∈ unip κ r := by
  refine and_congr (forall_congr' fun a => forall_congr' fun b => imp_congr_right fun _ => ?_)
    (forall_congr' fun a => ?_)
  · exact map_eq_zero_iff i i.injective
  · exact map_eq_one_iff i i.injective

/- English proof (translation)
Unfold `edgeSum`. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations.

Use `split_ifs`. Both sides reduce to the same expression. Rewrite using `[map_zero]`.
-/
theorem edgeSum_map (i : κ ≃+* κ') (g : GL (Fin r) κ) :
    edgeSum supEdge (Matrix.GeneralLinearGroup.map (i : κ →+* κ') g) = i (edgeSum supEdge g) := by
  unfold edgeSum
  rw [map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  split_ifs
  · rfl
  · rw [map_zero]

end Local

structure PlaceIso (D : D7) (Pg : Finset (Pl D.host.E)) where
  pl : TypePl D ≃ ↥Pg
  iso : ∀ v : TypePl D, ZMod (D.host.g v.1) ≃+* kP (pl v).1

namespace PlaceIso

variable {D : D7} {Pg : Finset (Pl D.host.E)} (P : PlaceIso D Pg) {LL : Type} [Field LL]

def grp : G0g D.nd ≃* G0 Pg D.R.r where
  toEquiv := (Equiv.piCongrRight fun v => glEquiv (P.iso v) D.R.r).trans
    (Equiv.piCongrLeft (fun PP : ↥Pg => GL (Fin D.R.r) (kP PP.1)) P.pl)
  map_mul' x y := by
    funext PP
    obtain ⟨v, rfl⟩ := P.pl.surjective PP
    simp [glEquiv]

/- English proof (translation)
Simplify using `[grp, glEquiv]`.
-/
theorem grp_apply (g : G0g D.nd) (v : TypePl D) :
    P.grp g (P.pl v) = Matrix.GeneralLinearGroup.map (P.iso v : ZMod (D.host.g v.1) →+* kP (P.pl v).1) (g v) := by
  simp [grp, glEquiv]

def pullChi (χ : ∀ PP : ↥Pg, (kP PP.1)ˣ →* LLˣ) (v : TypePl D) : (ZMod (D.host.g v.1))ˣ →* LLˣ :=
  (χ (P.pl v)).comp (Units.map (P.iso v : ZMod (D.host.g v.1) →+* kP (P.pl v).1).toMonoidHom)

def pullPsi (ψ : ∀ PP : Pl D.host.E, AddChar (kP PP) LL) (v : TypePl D) : AddChar (ZMod (D.host.g v.1)) LL :=
  (ψ (P.pl v).1).compAddMonoidHom (P.iso v).toAddMonoidHom

/- English proof (translation)
Use `⟨Equiv.piCongrLeft (fun PP : ↥Pg => (kP PP.1)ˣ →* LLˣ) P.pl fun v => (χ' v).comp (Units.map ((P.iso v).symm : kP (P.pl v).1 →+* ZMod (D.host.g v.1)).toMonoidHom), ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `v`. Unfold `pullChi`. Rewrite using `[Equiv.piCongrLeft_apply_apply]`. Use `MonoidHom.ext fun x => congrArg (χ' v) (Units.ext ?_)` and prove the remaining obligations.

Simplify using the standard rewrite rules.
-/
theorem pullChi_surj (χ' : ∀ v : TypePl D, (ZMod (D.host.g v.1))ˣ →* LLˣ) : ∃ χ, P.pullChi χ = χ' := by
  refine ⟨Equiv.piCongrLeft (fun PP : ↥Pg => (kP PP.1)ˣ →* LLˣ) P.pl fun v =>
    (χ' v).comp (Units.map ((P.iso v).symm : kP (P.pl v).1 →+* ZMod (D.host.g v.1)).toMonoidHom), ?_⟩
  funext v
  unfold pullChi
  rw [Equiv.piCongrLeft_apply_apply]
  refine MonoidHom.ext fun x => congrArg (χ' v) (Units.ext ?_)
  simp

/- English proof (translation)
Set `ψ0` to `Equiv.piCongrLeft (fun PP : ↥Pg => AddChar (kP PP.1) LL) P.pl fun v => (ψ' v).compAddMonoidHom (P.iso v).symm.toAddMonoidHom`. Use `⟨fun PP => if h : PP ∈ Pg then ψ0 ⟨PP, h⟩ else 1, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `v`. Unfold `pullPsi`. Simplify using `only [dif_pos (P.pl v).2, Subtype.coe_eta, ψ0]`.

Rewrite using `[Equiv.piCongrLeft_apply_apply]`. Use extensionality with `x`. Simplify using the standard rewrite rules.
-/
theorem pullPsi_surj (ψ' : ∀ v : TypePl D, AddChar (ZMod (D.host.g v.1)) LL) : ∃ ψ, P.pullPsi ψ = ψ' := by
  classical
  let ψ0 := Equiv.piCongrLeft (fun PP : ↥Pg => AddChar (kP PP.1) LL) P.pl fun v =>
    (ψ' v).compAddMonoidHom (P.iso v).symm.toAddMonoidHom
  refine ⟨fun PP => if h : PP ∈ Pg then ψ0 ⟨PP, h⟩ else 1, ?_⟩
  funext v
  unfold pullPsi
  simp only [dif_pos (P.pl v).2, Subtype.coe_eta, ψ0]
  rw [Equiv.piCongrLeft_apply_apply]
  ext x
  simp

/- English proof (translation)
Establish `key : ∀ v, P.pullPsi ψ v = 1 ↔ ψ (P.pl v).1 = 1` using `fun v => ⟨fun h => AddChar.ext _ _ fun x => by`. Take `⟨y, rfl⟩` from `(P.iso v).surjective x`. Conclude with `DFunLike.congr_fun h y, fun h => by unfold pullPsi; rw [h]; rfl⟩`. Prove the components needed by the constructor for the conclusion. Conclude with `fun h v hv => h _ (P.pl v).2 ((key v).1 hv)`.

Introduce `h PP hP h1`. Take `⟨v, hv⟩` from `P.pl.surjective ⟨PP, hP⟩`. Take `rfl : (P.pl v).1 = PP` from `congrArg Subtype.val hv`. Conclude with `h v ((key v).2 h1)`.
-/
theorem generic_iff (ψ : ∀ PP : Pl D.host.E, AddChar (kP PP) LL) : IsGenericPsi Pg ψ ↔ ∀ v, P.pullPsi ψ v ≠ 1 := by
  have key : ∀ v, P.pullPsi ψ v = 1 ↔ ψ (P.pl v).1 = 1 := fun v =>
    ⟨fun h => AddChar.ext _ _ fun x => by
      obtain ⟨y, rfl⟩ := (P.iso v).surjective x
      exact DFunLike.congr_fun h y, fun h => by unfold pullPsi; rw [h]; rfl⟩
  constructor
  · exact fun h v hv => h _ (P.pl v).2 ((key v).1 hv)
  · intro h PP hP h1
    obtain ⟨v, hv⟩ := P.pl.surjective ⟨PP, hP⟩
    obtain rfl : (P.pl v).1 = PP := congrArg Subtype.val hv
    exact h v ((key v).2 h1)

/- English proof (translation)
Rewrite using `[chiDetG, MonoidHom.finsetProd_apply]`. Use `Fintype.prod_equiv P.pl _ _ fun v => ?_` and prove the remaining obligations. Rewrite using `[grp_apply, Matrix.GeneralLinearGroup.map_det]`. Both sides reduce to the same expression.
-/
theorem chiDetG_pull (χ : ∀ PP : ↥Pg, (kP PP.1)ˣ →* LLˣ) (g : G0g D.nd) :
    chiDetG D (P.pullChi χ) g = ∏ PP : ↥Pg, χ PP (Matrix.GeneralLinearGroup.det (P.grp g PP)) := by
  rw [chiDetG, MonoidHom.finsetProd_apply]
  refine Fintype.prod_equiv P.pl _ _ fun v => ?_
  rw [grp_apply, Matrix.GeneralLinearGroup.map_det]
  rfl

/- English proof (translation)
Use `show (∀ v ∈ Set.univ, g v ∈ unip _ D.R.r) ↔ ∀ PP ∈ Set.univ, P.grp g PP ∈ unip (kP PP.1) D.R.r`. Simplify using `only [Set.mem_univ, forall_true_left]`. Rewrite using `[P.pl.surjective.forall]`. Conclude with `forall_congr' fun v => by rw [grp_apply, map_mem_unip]`.
-/
theorem mem_unipG (ψ : ∀ PP : Pl D.host.E, AddChar (kP PP) LL) (g : G0g D.nd) :
    g ∈ unipG D ↔ P.grp g ∈ (P0 Pg D.R.r ψ).conj.H := by
  show (∀ v ∈ Set.univ, g v ∈ unip _ D.R.r) ↔ ∀ PP ∈ Set.univ, P.grp g PP ∈ unip (kP PP.1) D.R.r
  simp only [Set.mem_univ, forall_true_left]
  rw [P.pl.surjective.forall]
  exact forall_congr' fun v => by rw [grp_apply, map_mem_unip]

/- English proof (translation)
Unfold `unipotentCharacterOfAddChars LevelP.conj P0 LevelP.ofLocal`. Simplify using `only [MonoidHom.inv_apply, MonoidHom.finsetProd_apply]`. Use `congr 1`. Use `Fintype.prod_equiv P.pl _ _ fun v => Units.ext ?_` and prove the remaining obligations. Use `show ψ (P.pl v).1 (P.iso v (edgeSum supEdge (g v))) = ψ (P.pl v).1 (edgeSum supEdge (P.grp g (P.pl v)))`.

Rewrite using `[grp_apply, edgeSum_map]`.
-/
theorem lamP0_pull_psi (ψ : ∀ PP : Pl D.host.E, AddChar (kP PP) LL) (g : G0g D.nd) (h' : g ∈ unipG D)
    (h : P.grp g ∈ (P0 Pg D.R.r ψ).conj.H) :
    unipotentCharacterOfAddChars D (P.pullPsi ψ) ⟨g, h'⟩ = (P0 Pg D.R.r ψ).conj.chi ⟨P.grp g, h⟩ := by
  unfold unipotentCharacterOfAddChars LevelP.conj P0 LevelP.ofLocal
  simp only [MonoidHom.inv_apply, MonoidHom.finsetProd_apply]
  congr 1
  refine Fintype.prod_equiv P.pl _ _ fun v => Units.ext ?_
  show ψ (P.pl v).1 (P.iso v (edgeSum supEdge (g v))) = ψ (P.pl v).1 (edgeSum supEdge (P.grp g (P.pl v)))
  rw [grp_apply, edgeSum_map]

end PlaceIso

section Places

open scoped Pointwise

variable {D : D7}

/- English proof (translation)
Rewrite using `[Ideal.map_le_iff_le_comap]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Conclude with `HeightOneSpectrum.ext (Q.isMaximal.eq_of_le (PP.under (𝓞 D.host.K)).isPrime.ne_top h).symm`. Introduce and unpack `rfl`.

Conclude with `le_rfl`.
-/
theorem map_le_iff_under (Q : HeightOneSpectrum (𝓞 D.host.K)) (PP : Pl D.host.E) :
    Q.asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) ≤ PP.asIdeal ↔ PP.under (𝓞 D.host.K) = Q := by
  rw [Ideal.map_le_iff_le_comap]
  constructor
  · intro h
    exact HeightOneSpectrum.ext (Q.isMaximal.eq_of_le (PP.under (𝓞 D.host.K)).isPrime.ne_top h).symm
  · rintro rfl
    exact le_rfl

/- English proof (translation)
Substitute `h` using the available equality. Establish `: algebraMap (𝓞 D.host.K) (𝓞 D.host.E) ((D.host.g k : ℕ) : 𝓞 D.host.K) ∈ PP.asIdeal` using `hQ`. Rewrite `this` using `[map_natCast]`. Then use the resulting hypothesis.
-/
theorem over_of_under {k : Fin 2} {Q : HeightOneSpectrum (𝓞 D.host.K)}
    (hQ : ((D.host.g k : ℕ) : 𝓞 D.host.K) ∈ Q.asIdeal) {PP : Pl D.host.E} (h : PP.under (𝓞 D.host.K) = Q) :
    ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
  subst h
  have : algebraMap (𝓞 D.host.K) (𝓞 D.host.E) ((D.host.g k : ℕ) : 𝓞 D.host.K) ∈ PP.asIdeal := hQ
  rwa [map_natCast] at this

/- English proof (translation)
The claim follows from `Set.finite_of_ncard_ne_zero (by rw [D.nd.g_split k]; exact Module.finrank_pos.ne')`.
-/
theorem finite_over (k : Fin 2) : (placesOver D.host.E (D.host.g k)).Finite :=
  Set.finite_of_ncard_ne_zero (by rw [D.nd.g_split k]; exact Module.finrank_pos.ne')

/- English proof (translation)
Establish `hE : Module.finrank ℚ D.host.E = 2 * D.R.f`. Establish `h : (Module.finrank ℚ D.host.E : ℝ) = 2 * (D.R.f : ℝ)`. Rewrite using `[D.host.finrank_cmField]`. Unfold `Ranks.f Ranks.n`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Conclude with `h` after adjusting the coercions. Set `c : Pl D.host.E → Pl D.host.E` to `fun w => ⟨D.host.conj • w.asIdeal, haveI := w.isPrime; inferInstance, by`. Introduce `h0`. Apply `w.ne_bot` to reduce the goal to its premises.

Use `congrArg (fun I : Ideal (𝓞 D.host.E) => D.host.conj⁻¹ • I) h0` as an intermediate fact. Simplify using `using this⟩`. Establish `hci : Function.Injective c` using `fun a b h => HeightOneSpectrum.ext (MulAction.injective D.host.conj (congrArg HeightOneSpectrum.asIdeal h))`. Establish `hm` using `fun w hw => (GlobalTheory.Mem.Chr.splitsC_main D.R D.host (D.host.g k) (D.host.g_prime k) (D.nd.g_split k) w hw).2.2.2 Q hQ (c w) ((GlobalTheory.Mem.Chr.conjPl_iff_smul D.host.conj w (c w)).2 rfl)`. Use `set S := {PP : Pl D.host.E | PP.under (𝓞 D.host.K) = Q}`.

Use `set X := placesOver D.host.E (D.host.g k)`. Establish `hX : X.Finite` using `finite_over k`. Establish `hS : S ⊆ X` using `fun w hw => over_of_under hQ hw`. Establish `h1 : S.ncard ≤ (X \ S).ncard` using `Set.ncard_le_ncard_of_injOn c (fun w hw => ⟨(hm w (hS hw)).1, (hm w (hS hw)).2.1 hw⟩) hci.injOn hX.diff`. Establish `h2 : (X \ S).ncard ≤ S.ncard` using `Set.ncard_le_ncard_of_injOn c (fun w hw => not_not.1 fun h => hw.2 ((hm w hw.1).2.2 h)) hci.injOn (hX.subset hS)`.

Establish `h3` using `Set.ncard_diff_add_ncard_of_subset hS hX`. Establish `h4 : X.ncard = 2 * D.R.f` using `(D.nd.g_split k).trans hE`. Use linear arithmetic over natural numbers and integers.
-/
theorem ncard_under {k : Fin 2} {Q : HeightOneSpectrum (𝓞 D.host.K)}
    (hQ : ((D.host.g k : ℕ) : 𝓞 D.host.K) ∈ Q.asIdeal) :
    {PP : Pl D.host.E | PP.under (𝓞 D.host.K) = Q}.ncard = D.R.f := by
  have hE : Module.finrank ℚ D.host.E = 2 * D.R.f := by
    have h : (Module.finrank ℚ D.host.E : ℝ) = 2 * (D.R.f : ℝ) := by
      rw [D.host.finrank_cmField]
      unfold Ranks.f Ranks.n
      push_cast
      ring
    exact_mod_cast h
  let c : Pl D.host.E → Pl D.host.E := fun w => ⟨D.host.conj • w.asIdeal, haveI := w.isPrime; inferInstance, by
    intro h0
    apply w.ne_bot
    have := congrArg (fun I : Ideal (𝓞 D.host.E) => D.host.conj⁻¹ • I) h0
    simpa using this⟩
  have hci : Function.Injective c := fun a b h => HeightOneSpectrum.ext
    (MulAction.injective D.host.conj (congrArg HeightOneSpectrum.asIdeal h))
  have hm := fun w hw => (GlobalTheory.Mem.Chr.splitsC_main D.R D.host (D.host.g k) (D.host.g_prime k) (D.nd.g_split k)
    w hw).2.2.2 Q hQ (c w) ((GlobalTheory.Mem.Chr.conjPl_iff_smul D.host.conj w (c w)).2 rfl)
  set S := {PP : Pl D.host.E | PP.under (𝓞 D.host.K) = Q}
  set X := placesOver D.host.E (D.host.g k)
  have hX : X.Finite := finite_over k
  have hS : S ⊆ X := fun w hw => over_of_under hQ hw
  have h1 : S.ncard ≤ (X \ S).ncard :=
    Set.ncard_le_ncard_of_injOn c (fun w hw => ⟨(hm w (hS hw)).1, (hm w (hS hw)).2.1 hw⟩) hci.injOn hX.diff
  have h2 : (X \ S).ncard ≤ S.ncard :=
    Set.ncard_le_ncard_of_injOn c (fun w hw => not_not.1 fun h => hw.2 ((hm w hw.1).2.2 h)) hci.injOn (hX.subset hS)
  have h3 := Set.ncard_diff_add_ncard_of_subset hS hX
  have h4 : X.ncard = 2 * D.R.f := (D.nd.g_split k).trans hE
  omega

variable {T : Core D} (hb : ∀ k, ((D.host.g k : ℕ) : 𝓞 D.host.K) ∈ (T.pb k).asIdeal)
include hb

/- English proof (translation)
Establish `hf : {PP : Pl D.host.E | ∃ k, PP.under (𝓞 D.host.K) = T.pb k}.Finite` using `(Set.finite_iUnion fun k => finite_over (D := D) k).subset fun PP ⟨k, hk⟩ => Set.mem_iUnion.2 ⟨k, over_of_under (hb k) hk⟩`. Use `⟨hf.toFinset, fun PP => ?_⟩` and prove the remaining obligations. Simplify using `only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, map_le_iff_under]`.
-/
theorem exists_isTypeSet : ∃ Pg, IsTypeSet T Pg := by
  have hf : {PP : Pl D.host.E | ∃ k, PP.under (𝓞 D.host.K) = T.pb k}.Finite :=
    (Set.finite_iUnion fun k => finite_over (D := D) k).subset fun PP ⟨k, hk⟩ =>
      Set.mem_iUnion.2 ⟨k, over_of_under (hb k) hk⟩
  refine ⟨hf.toFinset, fun PP => ?_⟩
  simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, map_le_iff_under]

/- English proof (translation)
Establish `he : ∀ k, Nonempty (D.nd.PlG k ≃ {PP : Pl D.host.E | PP.under (𝓞 D.host.K) = T.pb k})`. Introduce `k`. Use `haveI : Finite {PP : Pl D.host.E | PP.under (𝓞 D.host.K) = T.pb k} := (finite_over k).subset fun w hw => over_of_under (hb k) hw`. Rewrite using `[← Finite.card_eq, Nat.card_coe_set_eq, ncard_under (hb k), Nat.card_eq_fintype_card, D.nd.card_PlG]`. Set `e` to `fun k => (he k).some`.

Set `p : TypePl D → ↥Pg` to `fun v => ⟨(e v.1 v.2).1, (h _).2 ⟨v.1, (map_le_iff_under _ _).2 (e v.1 v.2).2⟩⟩`. Establish `hov : ∀ v, ((D.host.g v.1 : ℕ) : 𝓞 D.host.E) ∈ (p v).1.asIdeal` using `fun v => over_of_under (hb v.1) (e v.1 v.2).2`. Establish `hN : ∀ v, Ideal.absNorm (p v).1.asIdeal = D.host.g v.1` using `fun v => (GlobalTheory.Mem.Chr.splitsC_main D.R D.host _ (D.host.g_prime v.1) (D.nd.g_split v.1) _ (hov v)).1`. Establish `hp : Function.Bijective p`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨k, a⟩ ⟨k', a'⟩ hh`. Establish `hg : D.host.g k = D.host.g k'` using `(hN ⟨k, a⟩).symm.trans (hh ▸ hN ⟨k', a'⟩)`. Choose the witnesses or unpack the hypotheses as in `rfl : k = k' := by`. Use `D.host.g_ne` as an intermediate fact. Apply the tactic sequence `fin_cases k <;> fin_cases k' <;> first | rfl | exact absurd hg this | exact absurd hg.symm this`.

Take `rfl : a = a'` from `(e k).injective (Subtype.ext (congrArg (fun x : ↥Pg => x.1) hh))`. Both sides reduce to the same expression. Introduce and unpack `⟨PP, hP⟩`. Take `⟨k, hk⟩` from `(h PP).1 hP`. Conclude with `⟨⟨k, (e k).symm ⟨PP, (map_le_iff_under _ _).1 hk⟩⟩, Subtype.ext (by simp [p])⟩`.

Use `⟨⟨Equiv.ofBijective p hp, fun v => ?_⟩⟩` and prove the remaining obligations. Establish `hc : Nat.card (kP (p v).1) = D.host.g v.1`. Rewrite using `[← hN v, Ideal.absNorm_apply, Submodule.cardQuot_apply]`. Use `haveI : Finite (kP (p v).1) := Nat.finite_of_card_ne_zero (hc ▸ (D.host.g_prime v.1).ne_zero)`. Use `haveI := Fintype.ofFinite (kP (p v).1)`.

Conclude with `ZMod.ringEquivOfPrime (kP (p v).1) (D.host.g_prime v.1) (Nat.card_eq_fintype_card.symm.trans hc)`.
-/
theorem nonempty_placeIso {Pg : Finset (Pl D.host.E)} (h : IsTypeSet T Pg) : Nonempty (PlaceIso D Pg) := by
  have he : ∀ k, Nonempty (D.nd.PlG k ≃ {PP : Pl D.host.E | PP.under (𝓞 D.host.K) = T.pb k}) := by
    intro k
    haveI : Finite {PP : Pl D.host.E | PP.under (𝓞 D.host.K) = T.pb k} :=
      (finite_over k).subset fun w hw => over_of_under (hb k) hw
    rw [← Finite.card_eq, Nat.card_coe_set_eq, ncard_under (hb k), Nat.card_eq_fintype_card, D.nd.card_PlG]
  let e := fun k => (he k).some
  let p : TypePl D → ↥Pg := fun v => ⟨(e v.1 v.2).1, (h _).2 ⟨v.1, (map_le_iff_under _ _).2 (e v.1 v.2).2⟩⟩
  have hov : ∀ v, ((D.host.g v.1 : ℕ) : 𝓞 D.host.E) ∈ (p v).1.asIdeal := fun v => over_of_under (hb v.1) (e v.1 v.2).2
  have hN : ∀ v, Ideal.absNorm (p v).1.asIdeal = D.host.g v.1 := fun v =>
    (GlobalTheory.Mem.Chr.splitsC_main D.R D.host _ (D.host.g_prime v.1) (D.nd.g_split v.1) _ (hov v)).1
  have hp : Function.Bijective p := by
    constructor
    · rintro ⟨k, a⟩ ⟨k', a'⟩ hh
      have hg : D.host.g k = D.host.g k' := (hN ⟨k, a⟩).symm.trans (hh ▸ hN ⟨k', a'⟩)
      obtain rfl : k = k' := by
        have := D.host.g_ne
        fin_cases k <;> fin_cases k' <;> first | rfl | exact absurd hg this | exact absurd hg.symm this
      obtain rfl : a = a' := (e k).injective (Subtype.ext (congrArg (fun x : ↥Pg => x.1) hh))
      rfl
    · rintro ⟨PP, hP⟩
      obtain ⟨k, hk⟩ := (h PP).1 hP
      exact ⟨⟨k, (e k).symm ⟨PP, (map_le_iff_under _ _).1 hk⟩⟩, Subtype.ext (by simp [p])⟩
  refine ⟨⟨Equiv.ofBijective p hp, fun v => ?_⟩⟩
  have hc : Nat.card (kP (p v).1) = D.host.g v.1 := by
    rw [← hN v, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  haveI : Finite (kP (p v).1) := Nat.finite_of_card_ne_zero (hc ▸ (D.host.g_prime v.1).ne_zero)
  haveI := Fintype.ofFinite (kP (p v).1)
  exact ZMod.ringEquivOfPrime (kP (p v).1) (D.host.g_prime v.1) (Nat.card_eq_fintype_card.symm.trans hc)

end Places

open GlobalTheory.MemN.TypesInhab in

/- English proof (translation)
Use `haveI : ∀ k, NeZero (D.host.g k) := fun k => ⟨(D.host.g_prime k).ne_zero⟩`. Use `haveI : ∀ k, Fact (D.host.g k).Prime := fun k => ⟨D.host.g_prime k⟩`. Take `⟨hc, hm⟩` from `good_sum (I := TypePl D) (P := fun v => Fin D.R.r → ZMod (D.host.g v.1)) (fun v p => D.ntypes.eSer v.1 (Formalism.CyclotomicNorms.monicOf p)) (fun a => D.ntypes.goodTuple (fun k v => Formalism.CyclotomicNorms.monicOf (a ⟨k, v⟩))) D.ntypes.e0 (fun g => rfl) (fun _ _ => D.ntypes.eS …`. Rewrite using `[← Formalism.CyclotomicNorms.Sqf.coeff_monicOf_lt p i, h, Formalism.CyclotomicNorms.Sqf.coeff_monicOf_lt]))`. Use `⟨hc, ?_⟩` and prove the remaining obligations.

Establish `h : D.ntypes.e0 = ∑ a : ∀ v : TypePl D, Fin D.R.r → ZMod (D.host.g v.1), if D.ntypes.goodTuple (fun k v => Formalism.CyclotomicNorms.monicOf (a ⟨k, v⟩)) then ten (fun v => D.ntypes.eSer v.1 (Formalism.CyclotomicNorms.monicOf (a v))) else 0`. Use extensionality with `g`. Rewrite using `[MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]`. Use `(finsum_eq_sum_of_fintype _).trans (Finset.sum_congr rfl fun a _ => ?_)` and prove the remaining obligations. Apply the tactic sequence `split_ifs <;> rfl`.

Use `conv_lhs => rhs`. Rewrite using `[h]`. Rewrite using `[Finset.mul_sum]`. Use `conv_rhs => rw [h]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations.

Use `split_ifs with ha`. Rewrite using `[hm, if_pos ha]`. Rewrite using `[mul_zero]`.
-/
theorem goodSeriesIdempotent_central_idempotent (D : D7) :
    D.ntypes.e0 ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd)) ∧ D.ntypes.e0 * D.ntypes.e0 = D.ntypes.e0 := by
  classical
  haveI : ∀ k, NeZero (D.host.g k) := fun k => ⟨(D.host.g_prime k).ne_zero⟩
  haveI : ∀ k, Fact (D.host.g k).Prime := fun k => ⟨D.host.g_prime k⟩
  obtain ⟨hc, hm⟩ := good_sum (I := TypePl D) (P := fun v => Fin D.R.r → ZMod (D.host.g v.1))
    (fun v p => D.ntypes.eSer v.1 (Formalism.CyclotomicNorms.monicOf p))
    (fun a => D.ntypes.goodTuple (fun k v => Formalism.CyclotomicNorms.monicOf (a ⟨k, v⟩))) D.ntypes.e0 (fun g => rfl)
    (fun _ _ => D.ntypes.eSer_idem _ _) (fun _ _ => D.ntypes.eSer_central _ _)
    (fun _ p q hpq => D.ntypes.eSer_orth _ _ _ fun h => hpq (funext fun i => by
      rw [← Formalism.CyclotomicNorms.Sqf.coeff_monicOf_lt p i, h, Formalism.CyclotomicNorms.Sqf.coeff_monicOf_lt]))
  refine ⟨hc, ?_⟩
  have h : D.ntypes.e0 = ∑ a : ∀ v : TypePl D, Fin D.R.r → ZMod (D.host.g v.1),
      if D.ntypes.goodTuple (fun k v => Formalism.CyclotomicNorms.monicOf (a ⟨k, v⟩)) then
        ten (fun v => D.ntypes.eSer v.1 (Formalism.CyclotomicNorms.monicOf (a v))) else 0 := by
    ext g
    rw [MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
    refine (finsum_eq_sum_of_fintype _).trans (Finset.sum_congr rfl fun a _ => ?_)
    split_ifs <;> rfl
  conv_lhs => rhs; rw [h]
  rw [Finset.mul_sum]
  conv_rhs => rw [h]
  refine Finset.sum_congr rfl fun a _ => ?_
  split_ifs with ha
  · rw [hm, if_pos ha]
  · rw [mul_zero]

/- English proof (translation)
Take `⟨hc, hi⟩` from `goodSeriesIdempotent_central_idempotent D`. Use `⟨fun g x => σ₀.injective ?_, fun g => σ₀.injective ?_⟩` and prove the remaining obligations. Use `congrArg (fun z => z.coeff (x * g)) (Subalgebra.mem_center_iff.1 hc (MonoidAlgebra.single x (1 : ℂ)))` as an intermediate fact. Simplify using `only [MonoidAlgebra.coeff_single_mul_apply, MonoidAlgebra.coeff_mul_single_apply, inv_mul_cancel_left, one_mul, mul_one] at this`. Rewrite using `[h, h, this]`.

Rewrite using `[map_sum, h, ← hi, GlobalTheory.MemN.TypesInhab.coeff_mul_sum]`. Conclude with `Finset.sum_congr rfl fun x _ => by rw [map_mul, h, h]`.
-/
theorem isCentralIdempotent_of_goodSeriesIdempotent {D : D7} {LL : Type} [Field LL] (σ₀ : LL →+* ℂ) {eC : G0g D.nd → LL}
    (h : ∀ g, σ₀ (eC g) = D.ntypes.e0.coeff g) : IsCentralIdem eC := by
  obtain ⟨hc, hi⟩ := goodSeriesIdempotent_central_idempotent D
  refine ⟨fun g x => σ₀.injective ?_, fun g => σ₀.injective ?_⟩
  · have := congrArg (fun z => z.coeff (x * g))
      (Subalgebra.mem_center_iff.1 hc (MonoidAlgebra.single x (1 : ℂ)))
    simp only [MonoidAlgebra.coeff_single_mul_apply, MonoidAlgebra.coeff_mul_single_apply, inv_mul_cancel_left, one_mul, mul_one] at this
    rw [h, h, this]
  · rw [map_sum, h, ← hi, GlobalTheory.MemN.TypesInhab.coeff_mul_sum]
    exact Finset.sum_congr rfl fun x _ => by rw [map_mul, h, h]

/- English proof (translation)
Take `⟨aP, aM, _, _, n, _⟩` from `w`. Take `⟨aP', aM', _, _, n', _⟩` from `w'`. Take `rfl : n = n'` from `h.1.trans h'.1.symm`. Take `rfl : aP = aP'` from `funext fun τ => funext fun i => by`. Conclude with `((h.2 τ).1 i).trans ((h'.2 τ).1 i).symm` after adjusting the coercions.

Take `rfl : aM = aM'` from `funext fun τ => funext fun i => by`. Use `((h.2 τ).2 i.rev).trans ((h'.2 τ).2 i.rev).symm` as an intermediate fact. Rewrite `this` using `[Fin.rev_rev]`. Conclude with `this` after adjusting the coercions. Both sides reduce to the same expression.
-/
theorem isKappa_unique {D : D7} {j : ℕ} {w w' : WeightFamilies.Wt D j} (h : IsKappa D j w) (h' : IsKappa D j w') : w = w' := by
  obtain ⟨aP, aM, _, _, n, _⟩ := w
  obtain ⟨aP', aM', _, _, n', _⟩ := w'
  obtain rfl : n = n' := h.1.trans h'.1.symm
  obtain rfl : aP = aP' := funext fun τ => funext fun i => by
    exact_mod_cast ((h.2 τ).1 i).trans ((h'.2 τ).1 i).symm
  obtain rfl : aM = aM' := funext fun τ => funext fun i => by
    have := ((h.2 τ).2 i.rev).trans ((h'.2 τ).2 i.rev).symm
    rw [Fin.rev_rev] at this
    exact_mod_cast this
  rfl

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun h => isKappa_unique h (isKappa_kaWt hK hn hj), fun h => h ▸ isKappa_kaWt hK hn hj⟩`.
-/
theorem isKappa_iff {D : D7} (hK : DV.KapDef D) (hn : Even D.R.nV) {j : ℕ} (hj : InR D j) (w : WeightFamilies.Wt D j) :
    IsKappa D j w ↔ w = DIV.Cons.kaWt D hK hn j :=
  ⟨fun h => isKappa_unique h (isKappa_kaWt hK hn hj), fun h => h ▸ isKappa_kaWt hK hn hj⟩

section Sides

variable {D : D7} (T : Core D) (j : ℕ) (w : WeightFamilies.Wt D j)
  (LL : Type) [Field LL] [NumberField LL] [Algebra T.Q.c.F LL]

def SideA (Pe : ∀ (G : Type) [Group G] [Fintype G] (Pg : Finset (Pl D.host.E)), (G ≃* G0 Pg D.R.r) → (G → LL) → Prop) :
    Prop :=
  ∀ (WL : Type) [AddCommGroup WL] [Module LL WL] [Module T.Q.c.F WL] [IsScalarTower T.Q.c.F LL WL]
    [Module (𝓞 LL) WL] [IsScalarTower (𝓞 LL) LL WL] [Module (𝓞 T.Q.c.F) WL]
    [IsScalarTower (𝓞 T.Q.c.F) T.Q.c.F WL]
    (W : (LL →+* ℂ) → Type) [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)]
    (G : Type) [Group G] [Fintype G]
    (A : FormsL LL T.Q.c.F WL W G) (ι : Cusp T j w →ₗ[T.Q.c.F] WL), CarriesCusp T j w A ι →
  ∀ (Pg : Finset (Pl D.host.E)), IsTypeSet T Pg →
  ∀ (φ : G ≃* G0 Pg D.R.r), IsDetChar φ A.chi →
  ∀ (ψ : ∀ PP : Pl D.host.E, AddChar (kP PP) LL), IsGenericPsi Pg ψ →
  ∀ eC : G → LL, Pe G Pg φ eC →
    MjFull A (levJ φ (P0 Pg D.R.r ψ).conj) (levLam φ (P0 Pg D.R.r ψ).conj) eC

def SideB (Pe : (G0g D.nd → LL) → Prop) : Prop :=
  ∀ (WL : Type) [AddCommGroup WL] [Module LL WL] [Module T.Q.c.F WL] [IsScalarTower T.Q.c.F LL WL]
    [Module (𝓞 LL) WL] [IsScalarTower (𝓞 LL) LL WL] [Module (𝓞 T.Q.c.F) WL]
    [IsScalarTower (𝓞 T.Q.c.F) T.Q.c.F WL]
    (W : (LL →+* ℂ) → Type) [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)]
    (A : FormsL LL T.Q.c.F WL W (G0g D.nd)) (ι : T.cuspA j (wtA w) w.n →ₗ[T.Q.c.F] WL),
    IsFormsOf T j (wtA w) w.n A ι →
  ∀ (χ : ∀ v : TypePl D, (ZMod (D.host.g v.1))ˣ →* LLˣ), A.chi = chiDetG D χ →
  ∀ (ψ : ∀ v : TypePl D, AddChar (ZMod (D.host.g v.1)) LL), (∀ v, ψ v ≠ 1) →
  ∀ (eC : G0g D.nd → LL), Pe eC → MjLattice A (unipG D) (unipotentCharacterOfAddChars D ψ) eC

def ReadAt {LL : Type} (Pe : (G0g D.nd → LL) → Prop) (G : Type) [Group G] [Fintype G] (Pg : Finset (Pl D.host.E))
    (φ : G ≃* G0 Pg D.R.r) (eC : G → LL) : Prop :=
  ∃ P : PlaceIso D Pg, Pe fun g => eC (φ.symm (P.grp g))

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h WL _ _ _ _ _ _ _ _ W _ _ A ι hA χ' hχ ψ' hψ eC he`. Take `⟨A', hA', hM, hρ, hc⟩` from `exists_carriesCusp T j w hA`. Take `⟨Pg, hPg⟩` from `exists_isTypeSet hb`. Take `⟨P⟩` from `nonempty_placeIso hb hPg`.

Take `⟨χ, rfl⟩` from `P.pullChi_surj χ'`. Take `⟨ψ, rfl⟩` from `P.pullPsi_surj ψ'`. Establish `h1` using `h WL W (G0g D.nd) A' ι hA' Pg hPg P.grp ⟨χ, fun g => by rw [hc, hχ, P.chiDetG_pull]⟩ ψ ((P.generic_iff ψ).2 hψ) eC ⟨P, by simpa using he⟩`. Conclude with `(mjLattice_congr A' A (MulEquiv.refl _) hM.symm (fun g => by rw [hρ]; rfl) (fun g => by rw [hc]; rfl) _ _ _ _ (P.mem_unipG ψ) (P.lamP0_pull_psi ψ) eC eC fun _ => rfl).2 ((mjFull_iff _ _ _ _).1 h1)`. Introduce and unpack `h WL _ _ _ _ _ _ _ _ W _ _ G _ _ A ι hA Pg - φ ⟨χ, hχ⟩ ψ hψ eC ⟨P, he⟩`.

Set `e : G0g D.nd ≃* G` to `P.grp.trans φ.symm`. Establish `hφ : ∀ g, φ (e g) = P.grp g` using `fun g => φ.apply_symm_apply _`. Set `A' : FormsL LL T.Q.c.F WL W (G0g D.nd)` to `{ A with ρ := A.ρ.comp e.toMonoidHom, chi := A.chi.comp e.toMonoidHom }`. Establish `h1` using `h WL W A' ι (isFormsOf_of_carriesCusp T j w (A := A') hA) (P.pullChi χ) (MonoidHom.ext fun g => by rw [P.chiDetG_pull, ← hφ, ← hχ]; rfl) (P.pullPsi ψ) ((P.generic_iff ψ).1 hψ) _ he`. Use `(mjFull_iff _ _ _ _).2 ((mjLattice_congr A A' e rfl (fun _ => rfl) (fun _ => rfl) _ _ _ _ (fun g => ?_) (fun g h' hg => ?_) eC _ fun _ => rfl).1 h1)` and prove the remaining obligations.

Rewrite using `[P.mem_unipG ψ, ← hφ]`. Both sides reduce to the same expression. Rewrite using `[P.lamP0_pull_psi ψ g h' ((P.mem_unipG ψ g).1 h')]`. Conclude with `congrArg _ (Subtype.ext (hφ g).symm)`.
-/
theorem sideA_iff_sideB (hb : ∀ k, ((D.host.g k : ℕ) : 𝓞 D.host.K) ∈ (T.pb k).asIdeal)
    (Pe : (G0g D.nd → LL) → Prop) : SideA T j w LL (ReadAt Pe) ↔ SideB T j w LL Pe := by
  constructor
  · intro h WL _ _ _ _ _ _ _ _ W _ _ A ι hA χ' hχ ψ' hψ eC he
    obtain ⟨A', hA', hM, hρ, hc⟩ := exists_carriesCusp T j w hA
    obtain ⟨Pg, hPg⟩ := exists_isTypeSet hb
    obtain ⟨P⟩ := nonempty_placeIso hb hPg
    obtain ⟨χ, rfl⟩ := P.pullChi_surj χ'
    obtain ⟨ψ, rfl⟩ := P.pullPsi_surj ψ'
    have h1 := h WL W (G0g D.nd) A' ι hA' Pg hPg P.grp ⟨χ, fun g => by rw [hc, hχ, P.chiDetG_pull]⟩ ψ
      ((P.generic_iff ψ).2 hψ) eC ⟨P, by simpa using he⟩
    exact (mjLattice_congr A' A (MulEquiv.refl _) hM.symm (fun g => by rw [hρ]; rfl) (fun g => by rw [hc]; rfl)
      _ _ _ _ (P.mem_unipG ψ) (P.lamP0_pull_psi ψ) eC eC fun _ => rfl).2 ((mjFull_iff _ _ _ _).1 h1)
  · rintro h WL _ _ _ _ _ _ _ _ W _ _ G _ _ A ι hA Pg - φ ⟨χ, hχ⟩ ψ hψ eC ⟨P, he⟩
    let e : G0g D.nd ≃* G := P.grp.trans φ.symm
    have hφ : ∀ g, φ (e g) = P.grp g := fun g => φ.apply_symm_apply _
    let A' : FormsL LL T.Q.c.F WL W (G0g D.nd) :=
      { A with ρ := A.ρ.comp e.toMonoidHom, chi := A.chi.comp e.toMonoidHom }
    have h1 := h WL W A' ι (isFormsOf_of_carriesCusp T j w (A := A') hA) (P.pullChi χ)
      (MonoidHom.ext fun g => by rw [P.chiDetG_pull, ← hφ, ← hχ]; rfl) (P.pullPsi ψ) ((P.generic_iff ψ).1 hψ) _ he
    refine (mjFull_iff _ _ _ _).2 ((mjLattice_congr A A' e rfl (fun _ => rfl) (fun _ => rfl) _ _ _ _
      (fun g => ?_) (fun g h' hg => ?_) eC _ fun _ => rfl).1 h1)
    · rw [P.mem_unipG ψ, ← hφ]; rfl
    · rw [P.lamP0_pull_psi ψ g h' ((P.mem_unipG ψ g).1 h')]
      exact congrArg _ (Subtype.ext (hφ g).symm)

/- English proof (translation)
Rewrite using `[← sideA_iff_sideB T j w LL hb]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `h WL _ _ _ _ _ _ _ _ W _ _ G _ _ A ι hA Pg hPg φ hχ ψ hψ eC ⟨P, he⟩`. Use `h WL W G A ι hA Pg hPg φ hχ ψ hψ eC ?_` and prove the remaining obligations. Simplify using `using isCentralIdem_comp (φ.trans P.grp.symm) he`.

Introduce `h WL _ _ _ _ _ _ _ _ W _ _ G _ _ A ι hA Pg hPg φ hχ ψ hψ eC he`. Take `⟨P⟩` from `nonempty_placeIso hb hPg`. Conclude with `h WL W G A ι hA Pg hPg φ hχ ψ hψ eC ⟨P, isCentralIdem_comp (P.grp.trans φ.symm) he⟩`.
-/
theorem sideA_idem_iff (hb : ∀ k, ((D.host.g k : ℕ) : 𝓞 D.host.K) ∈ (T.pb k).asIdeal) :
    SideA T j w LL (fun _ _ _ _ _ eC => IsCentralIdem eC) ↔ SideB T j w LL IsCentralIdem := by
  rw [← sideA_iff_sideB T j w LL hb]
  constructor
  · rintro h WL _ _ _ _ _ _ _ _ W _ _ G _ _ A ι hA Pg hPg φ hχ ψ hψ eC ⟨P, he⟩
    refine h WL W G A ι hA Pg hPg φ hχ ψ hψ eC ?_
    simpa using isCentralIdem_comp (φ.trans P.grp.symm) he
  · intro h WL _ _ _ _ _ _ _ _ W _ _ G _ _ A ι hA Pg hPg φ hχ ψ hψ eC he
    obtain ⟨P⟩ := nonempty_placeIso hb hPg
    exact h WL W G A ι hA Pg hPg φ hχ ψ hψ eC ⟨P, isCentralIdem_comp (P.grp.trans φ.symm) he⟩

end Sides

def WideB : Prop :=
  ∀ (D : D7) (T : Core D), LawsM T → ∀ j, InR D j → ∀ w : WeightFamilies.Wt D j, IsKappa D j w →
  ∀ (LL : Type) [Field LL] [NumberField LL] [Algebra T.Q.c.F LL], SideB T j w LL IsCentralIdem

def NarrowA (D : D7) : Prop :=
  ∀ (T : CoreJ D), LawsJ T → DV.KapDef D → Even D.R.nV → ∀ j, InR D j → ∀ w : WeightFamilies.Wt D j, IsKappa D j w →
  ∀ (LL : Type) [Field LL] [NumberField LL] [Algebra T.Q.c.F LL] (σ₀ : LL →+* ℂ), BaseEmbeddingInclusion T.Q.c.F σ₀ →
    SideA T.toCore j w LL (ReadAt fun eC => ∀ g, σ₀ (eC g) = D.ntypes.e0.coeff g)

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun h D T hT j hj w hw LL _ _ _ => (sideA_idem_iff T j w LL hT.half.1).1 (h D T hT j hj w hw LL), fun h D T hT j hj w hw LL _ _ _ => (sideA_idem_iff T j w LL hT.half.1).2 (h D T hT j hj w hw LL)⟩`.
-/
theorem mLat_iff_wideB : MLat ↔ WideB :=
  ⟨fun h D T hT j hj w hw LL _ _ _ => (sideA_idem_iff T j w LL hT.half.1).1 (h D T hT j hj w hw LL),
    fun h D T hT j hj w hw LL _ _ _ => (sideA_idem_iff T j w LL hT.half.1).2 (h D T hT j hj w hw LL)⟩

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h T hT hK hn j hj LL _ _ _ σ₀ hσ`. Conclude with `(sideA_iff_sideB T.toCore j _ LL hT.half.1 _).1 (h T hT hK hn j hj _ (isKappa_kaWt hK hn hj) LL σ₀ hσ)`. Introduce `h T hT hK hn j hj w hw LL _ _ _ σ₀ hσ`. Take `rfl` from `(isKappa_iff hK hn hj w).1 hw`.

Conclude with `(sideA_iff_sideB T.toCore j _ LL hT.half.1 _).2 (h T hT hK hn j hj LL σ₀ hσ)`.
-/
theorem narrowA_iff (D : D7) : NarrowA D ↔ MjLatticeRec D := by
  constructor
  · intro h T hT hK hn j hj LL _ _ _ σ₀ hσ
    exact (sideA_iff_sideB T.toCore j _ LL hT.half.1 _).1
      (h T hT hK hn j hj _ (isKappa_kaWt hK hn hj) LL σ₀ hσ)
  · intro h T hT hK hn j hj w hw LL _ _ _ σ₀ hσ
    obtain rfl := (isKappa_iff hK hn hj w).1 hw
    exact (sideA_iff_sideB T.toCore j _ LL hT.half.1 _).2 (h T hT hK hn j hj LL σ₀ hσ)

/- English proof (translation)
Introduce `T hT hK hn j hj LL _ _ _ σ₀ _ WL _ _ _ _ _ _ _ _ W _ _ A ι hA χ hχ ψ hψ eC he`. Conclude with `mLat_iff_wideB.1 h D T.toCore hT.toLawsM j hj _ (isKappa_kaWt hK hn hj) LL WL W A ι hA χ hχ ψ hψ eC (isCentralIdempotent_of_goodSeriesIdempotent σ₀ he)`.
-/
theorem mjLatticeRec_of_mLat (h : MLat) (D : D7) : MjLatticeRec D := by
  intro T hT hK hn j hj LL _ _ _ σ₀ _ WL _ _ _ _ _ _ _ _ W _ _ A ι hA χ hχ ψ hψ eC he
  exact mLat_iff_wideB.1 h D T.toCore hT.toLawsM j hj _ (isKappa_kaWt hK hn hj) LL WL W A ι hA χ hχ ψ hψ eC
    (isCentralIdempotent_of_goodSeriesIdempotent σ₀ he)

/- English proof (translation)
Assemble the required witnesses or components as `⟨mLat_iff_wideB, narrowA_iff, mjLatticeRec_of_mLat⟩`.
-/
theorem compare :
    (MLat ↔ WideB) ∧ (∀ D, NarrowA D ↔ MjLatticeRec D) ∧ (MLat → ∀ D, MjLatticeRec D) :=
  ⟨mLat_iff_wideB, narrowA_iff, mjLatticeRec_of_mLat⟩

end GlobalTheory.GoodLatCompare
