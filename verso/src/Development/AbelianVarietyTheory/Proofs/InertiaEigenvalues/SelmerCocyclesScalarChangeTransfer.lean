import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.VecPairApply
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemilinearCoefficientMapCocycles

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate
open GlobalTheory.ResSel.CoefMap

namespace GlobalTheory.NewPrime.ScalarChange

section General

variable {R R' : Type} [CommRing R] [CommRing R'] (σ : R →+* R') {Γ : Type} [Group Γ] [TopologicalSpace Γ]
  {M : Type} [AddCommGroup M] [Module R M] [Module R' M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [ContinuousConstSMul R M] [ContinuousConstSMul R' M]
  (hs : ∀ (a : R) (m : M), a • m = σ a • m)
  (rho : Representation R Γ M) (rho' : Representation R' Γ M) (he : ∀ g m, rho g m = rho' g m)

def idSl : M →ₛₗ[σ] M where
  toFun m := m
  map_add' _ _ := rfl
  map_smul' c m := hs c m

def tr : H1 rho →ₛₗ[σ] H1 rho' :=
  slH1 rho rho' (idSl σ hs) continuous_id he

def back (z : Z1 rho') : Z1 rho :=
  ⟨z.1, z.2.1, fun g h => by rw [z.2.2, he]⟩

/- English proof (translation)
The claim follows from `congrArg Submodule.Quotient.mk (Subtype.ext rfl)`.
-/
theorem tr_back (z : Z1 rho') :
    tr σ hs rho rho' he (Submodule.Quotient.mk (back rho rho' he z)) = Submodule.Quotient.mk z :=
  congrArg Submodule.Quotient.mk (Subtype.ext rfl)

/- English proof (translation)
Rewrite using `[injective_iff_map_eq_zero]`. Introduce `x hx`. Proceed by induction on `x using Submodule.Quotient.induction_on with`. Consider the case `H z`. Establish `h1 : (Submodule.Quotient.mk (semilinearCoefficientMapCocycles rho rho' (idSl σ hs) continuous_id he z) : H1 rho') = 0` using `hx`.

Rewrite `h1`, the goal using `[Submodule.Quotient.mk_eq_zero]`. Take `⟨m, hm⟩` from `(mem_coboundaries1 _ _).1 h1`. Use `(mem_coboundaries1 _ _).2 ⟨m, fun g => ?_⟩` and prove the remaining obligations. Rewrite using `[he]`. Conclude with `hm g`.
-/
theorem tr_injective : Function.Injective (tr σ hs rho rho' he) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  induction x using Submodule.Quotient.induction_on with
  | H z =>
    have h1 : (Submodule.Quotient.mk (semilinearCoefficientMapCocycles rho rho' (idSl σ hs) continuous_id he z) : H1 rho') = 0 := hx
    rw [Submodule.Quotient.mk_eq_zero] at h1 ⊢
    obtain ⟨m, hm⟩ := (mem_coboundaries1 _ _).1 h1
    refine (mem_coboundaries1 _ _).2 ⟨m, fun g => ?_⟩
    rw [he]
    exact hm g

/- English proof (translation)
The claim follows from `res_slH1 rho rho' (idSl σ hs) continuous_id he phi hphi x`.
-/
theorem res_tr {H : Type} [Group H] [TopologicalSpace H] (phi : H →* Γ) (hphi : Continuous phi) (x : H1 rho) :
    resH1 rho' phi hphi (tr σ hs rho rho' he x) =
      tr σ hs (rho.comp phi) (rho'.comp phi) (fun g m => he (phi g) m) (resH1 rho phi hphi x) :=
  res_slH1 rho rho' (idSl σ hs) continuous_id he phi hphi x

/- English proof (translation)
Establish `h0 : resH1 rho' J.subtype continuous_subtype_val (tr σ hs rho rho' he x) = 0` using `hx`. Establish `h1` using `res_tr σ hs rho rho' he J.subtype continuous_subtype_val x`. Conclude with `tr_injective σ hs (rho.comp J.subtype) (rho'.comp J.subtype) (fun g m => he g.1 m) (h1.symm.trans (h0.trans (map_zero _).symm))`.
-/
theorem of_tr_mem_ur (J : Subgroup Γ) (x : H1 rho) (hx : tr σ hs rho rho' he x ∈ H1ur rho' J) : x ∈ H1ur rho J := by
  have h0 : resH1 rho' J.subtype continuous_subtype_val (tr σ hs rho rho' he x) = 0 := hx
  have h1 := res_tr σ hs rho rho' he J.subtype continuous_subtype_val x
  exact tr_injective σ hs (rho.comp J.subtype) (rho'.comp J.subtype) (fun g m => he g.1 m)
    (h1.symm.trans (h0.trans (map_zero _).symm))

end General

section Coef

variable {O Λ Λ' : Type} [CommRing O] [CommRing Λ] [Algebra O Λ] [CommRing Λ'] [Algebra O Λ'] (φ : Λ →ₐ[O] Λ')
  {Y : Type} [AddCommGroup Y] [Module Λ Y] [Module Λ' Y] (hY : ∀ (a : Λ) (y : Y), a • y = φ a • y)

include hY in
/- English proof (translation)
Rewrite using `[hY, φ.commutes]`.
-/
theorem algebraMap_smul (c : O) (y : Y) : algebraMap O Λ c • y = algebraMap O Λ' c • y := by
  rw [hY, φ.commutes]

include hY in
/- English proof (translation)
The claim follows from `funext fun c => hY a (m c)`.
-/
theorem vec_smul {r : ℕ} (a : Λ) (m : Fin r → Y) : a • m = φ a • m :=
  funext fun c => hY a (m c)

include hY in
/- English proof (translation)
Use function extensionality and compare the values at `a`. Express the relevant statement in the definitionally equal form `((κ g : Λˣ) : Λ) • ∑ j, algebraMap O Λ ((ρ g : Matrix (Fin r) (Fin r) O) a j) • m j = ((κ' g : Λ'ˣ) : Λ') • ∑ j, algebraMap O Λ' ((ρ g : Matrix (Fin r) (Fin r) O) a j) • m j`. Simplify using `only [algebraMap_smul φ hY]`. Rewrite using `[hY, hκ]`.
-/
theorem repOn_eq_repOn {Γ : Type} [Group Γ] {r : ℕ} (ρ : Γ →* GL (Fin r) O) (κ : Γ →* Λˣ) (κ' : Γ →* Λ'ˣ)
    (hκ : ∀ g, ((κ' g : Λ'ˣ) : Λ') = φ (κ g : Λˣ)) (g : Γ) (m : Fin r → Y) :
    repOn ρ κ Y g m = repOn ρ κ' Y g m := by
  funext a
  change ((κ g : Λˣ) : Λ) • ∑ j, algebraMap O Λ ((ρ g : Matrix (Fin r) (Fin r) O) a j) • m j =
    ((κ' g : Λ'ˣ) : Λ') • ∑ j, algebraMap O Λ' ((ρ g : Matrix (Fin r) (Fin r) O) a j) • m j
  simp only [algebraMap_smul φ hY]
  rw [hY, hκ]

end Coef

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} (bkP : BKPh X)
  (i : X.Tw) {r : ℕ} (ρ : GE N →* GL (Fin r) (X.O0 i))
  {Λ Λ' : Type} [CommRing Λ] [Algebra (X.O0 i) Λ] [CommRing Λ'] [Algebra (X.O0 i) Λ']
  (φ : Λ →ₐ[X.O0 i] Λ') (κ : GE N →* Λˣ) (κ' : GE N →* Λ'ˣ) (hκ : ∀ g, ((κ' g : Λ'ˣ) : Λ') = φ (κ g : Λˣ))
  {Y : Type} [AddCommGroup Y] [Module Λ Y] [Module Λ' Y] [TopologicalSpace Y] [DiscreteTopology Y]
  (hY : ∀ (a : Λ) (y : Y), a • y = φ a • y)

abbrev trG : H1 (repOn ρ κ Y) →ₛₗ[(φ : Λ →+* Λ')] H1 (repOn ρ κ' Y) :=
  tr (φ : Λ →+* Λ') (vec_smul φ hY) (repOn ρ κ Y) (repOn ρ κ' Y) (repOn_eq_repOn φ hY ρ κ κ' hκ)

abbrev trL (v : PlE D.host) :
    H1 ((repOn ρ κ Y).comp (DecV N v).subtype) →ₛₗ[(φ : Λ →+* Λ')] H1 ((repOn ρ κ' Y).comp (DecV N v).subtype) :=
  tr (φ : Λ →+* Λ') (vec_smul φ hY) ((repOn ρ κ Y).comp (DecV N v).subtype) ((repOn ρ κ' Y).comp (DecV N v).subtype)
    (fun g m => repOn_eq_repOn φ hY ρ κ κ' hκ g.1 m)

/- English proof (translation)
Unfold `bkOn at hx ⊢`. Use `split_ifs at hx ⊢ with hv`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨z, c, y, b, hc, hy, hz, rfl⟩` from `hx`.

Use `Submodule.subset_span ⟨semilinearCoefficientMapCocycles _ _ (idSl (φ : Λ →+* Λ') (vec_smul φ hY)) continuous_id (fun g m => repOn_eq_repOn φ hY ρ κ κ' hκ g.1 m) z, c, y, b, hc, hy, fun g a => ?_, rfl⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `((z : ↥(DecV N v) → Fin r → Y) g a) = _`. Rewrite using `[hz, algebraMap_smul φ hY]`. Consider the case `zero => rw [map_zero]`. Conclude with `Submodule.zero_mem _`.

Consider the case `add x y _ _ hx hy => rw [map_add]`. Conclude with `Submodule.add_mem _ hx hy`. Consider the case `smul a x _ hx => rw [map_smulₛₗ]`. Conclude with `Submodule.smul_mem _ _ hx`. Rewrite `hx`, the goal using `[Submodule.mem_bot]`.

Rewrite using `[hx, map_zero]`.
-/
theorem trL_mem_bkOn (v : PlE D.host) (x : H1 ((repOn ρ κ Y).comp (DecV N v).subtype))
    (hx : x ∈ bkOn bkP i ρ κ Y v) : trL i ρ φ κ κ' hκ hY v x ∈ bkOn bkP i ρ κ' Y v := by
  unfold bkOn at hx ⊢
  split_ifs at hx ⊢ with hv
  · induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨z, c, y, b, hc, hy, hz, rfl⟩ := hx
      refine Submodule.subset_span ⟨semilinearCoefficientMapCocycles _ _ (idSl (φ : Λ →+* Λ') (vec_smul φ hY)) continuous_id
        (fun g m => repOn_eq_repOn φ hY ρ κ κ' hκ g.1 m) z, c, y, b, hc, hy, fun g a => ?_, rfl⟩
      change ((z : ↥(DecV N v) → Fin r → Y) g a) = _
      rw [hz, algebraMap_smul φ hY]
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx => rw [map_smulₛₗ]; exact Submodule.smul_mem _ _ hx
  · rw [Submodule.mem_bot] at hx ⊢
    rw [hx, map_zero]

/- English proof (translation)
Distinguish the cases in `hv : v ∈ placesOver D.host.E (X.l i)`. Establish `H : ∀ a : Λ', ∃ w ∈ bkOn bkP i ρ κ Y v, trL i ρ φ κ κ' hκ hY v w = a • x'`. Unfold `bkOn at hx`. Rewrite `hx` using `[dif_pos hv]`. Proceed by induction on `hx using Submodule.span_induction with`.

Consider the case `mem x hx`. Introduce `a`. Take `⟨z, c, y, b, hc, hy, hz, rfl⟩` from `hx`. Use `⟨Submodule.Quotient.mk (back ((repOn ρ κ Y).comp (DecV N v).subtype) ((repOn ρ κ' Y).comp (DecV N v).subtype) (fun g m => repOn_eq_repOn φ hY ρ κ κ' hκ g.1 m) (a • z)), ?_, tr_back _ _ _ _ _ _⟩` and prove the remaining obligations. Unfold `bkOn`.

Rewrite using `[dif_pos hv]`. Use `Submodule.subset_span ⟨back ((repOn ρ κ Y).comp (DecV N v).subtype) ((repOn ρ κ' Y).comp (DecV N v).subtype) (fun g m => repOn_eq_repOn φ hY ρ κ κ' hκ g.1 m) (a • z), c, y, a • b, hc, hy, fun g e => ?_, rfl⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `a • ((z : ↥(DecV N v) → Fin r → Y) g e) = _`. Rewrite using `[hz, algebraMap_smul φ hY, smul_comm]`. Consider the case `zero => exact fun a => ⟨0, Submodule.zero_mem _, by rw [map_zero, smul_zero]⟩`.

Consider the case `add x y _ _ hx hy`. Introduce `a`. Take `⟨w, hw, e⟩` from `hx a`. Take `⟨w', hw', e'⟩` from `hy a`. Conclude with `⟨w + w', Submodule.add_mem _ hw hw', by rw [map_add, e, e', smul_add]⟩`.

Consider the case `smul c x _ hx`. Introduce `a`. Take `⟨w, hw, e⟩` from `hx (a * c)`. Conclude with `⟨w, hw, by rw [e, mul_smul]⟩`. Simplify using `using H 1`.

Unfold `bkOn at hx`. Rewrite `hx` using `[dif_neg hv, Submodule.mem_bot]`. Conclude with `⟨0, Submodule.zero_mem _, by rw [map_zero, hx]⟩`.
-/
theorem exists_mem_bkOn (v : PlE D.host) (x' : H1 ((repOn ρ κ' Y).comp (DecV N v).subtype))
    (hx : x' ∈ bkOn bkP i ρ κ' Y v) : ∃ w ∈ bkOn bkP i ρ κ Y v, trL i ρ φ κ κ' hκ hY v w = x' := by
  by_cases hv : v ∈ placesOver D.host.E (X.l i)
  · have H : ∀ a : Λ', ∃ w ∈ bkOn bkP i ρ κ Y v, trL i ρ φ κ κ' hκ hY v w = a • x' := by
      unfold bkOn at hx
      rw [dif_pos hv] at hx
      induction hx using Submodule.span_induction with
      | mem x hx =>
        intro a
        obtain ⟨z, c, y, b, hc, hy, hz, rfl⟩ := hx
        refine ⟨Submodule.Quotient.mk (back ((repOn ρ κ Y).comp (DecV N v).subtype) ((repOn ρ κ' Y).comp (DecV N v).subtype)
          (fun g m => repOn_eq_repOn φ hY ρ κ κ' hκ g.1 m) (a • z)), ?_,
          tr_back _ _ _ _ _ _⟩
        unfold bkOn
        rw [dif_pos hv]
        refine Submodule.subset_span ⟨back ((repOn ρ κ Y).comp (DecV N v).subtype) ((repOn ρ κ' Y).comp (DecV N v).subtype)
          (fun g m => repOn_eq_repOn φ hY ρ κ κ' hκ g.1 m) (a • z), c, y, a • b, hc, hy,
            fun g e => ?_, rfl⟩
        change a • ((z : ↥(DecV N v) → Fin r → Y) g e) = _
        rw [hz, algebraMap_smul φ hY, smul_comm]
      | zero => exact fun a => ⟨0, Submodule.zero_mem _, by rw [map_zero, smul_zero]⟩
      | add x y _ _ hx hy =>
        intro a
        obtain ⟨w, hw, e⟩ := hx a
        obtain ⟨w', hw', e'⟩ := hy a
        exact ⟨w + w', Submodule.add_mem _ hw hw', by rw [map_add, e, e', smul_add]⟩
      | smul c x _ hx =>
        intro a
        obtain ⟨w, hw, e⟩ := hx (a * c)
        exact ⟨w, hw, by rw [e, mul_smul]⟩
    simpa using H 1
  · unfold bkOn at hx
    rw [dif_neg hv, Submodule.mem_bot] at hx
    exact ⟨0, Submodule.zero_mem _, by rw [map_zero, hx]⟩

/- English proof (translation)
Use `(mem_Sel _ _ _ _ _).2 fun v => ?_` and prove the remaining obligations. Establish `hv` using `(mem_Sel _ _ _ _ _).1 hx v`. Use `(res_tr (φ : Λ →+* Λ') (vec_smul φ hY) (repOn ρ κ Y) (repOn ρ κ' Y) (repOn_eq_repOn φ hY ρ κ κ' hκ) (Dec (F := D.host.E) (N.plOm.1 v)).subtype continuous_subtype_val x) ▸ ?_` and prove the remaining obligations. Unfold `Formalism.GaloisCohomology.bkCond at hv ⊢`. Use `split_ifs at hv ⊢ with h1 h2`.

Conclude with `trL_mem_bkOn bkP i ρ φ κ κ' hκ hY v _ hv`. Conclude with `Submodule.mem_top`. Conclude with `slH1_ur _ _ _ _ _ _ _ hv`.
-/
theorem trG_mem_selOn (Q : Finset (PlE D.host)) (x : H1 (repOn ρ κ Y)) (hx : x ∈ selOn bkP i ρ κ Y Q) :
    trG i ρ φ κ κ' hκ hY x ∈ selOn bkP i ρ κ' Y Q := by
  refine (mem_Sel _ _ _ _ _).2 fun v => ?_
  have hv := (mem_Sel _ _ _ _ _).1 hx v
  refine (res_tr (φ : Λ →+* Λ') (vec_smul φ hY) (repOn ρ κ Y) (repOn ρ κ' Y) (repOn_eq_repOn φ hY ρ κ κ' hκ)
    (Dec (F := D.host.E) (N.plOm.1 v)).subtype continuous_subtype_val x) ▸ ?_
  unfold Formalism.GaloisCohomology.bkCond at hv ⊢
  split_ifs at hv ⊢ with h1 h2
  · exact trL_mem_bkOn bkP i ρ φ κ κ' hκ hY v _ hv
  · exact Submodule.mem_top
  · exact slH1_ur _ _ _ _ _ _ _ hv

/- English proof (translation)
Use `(mem_Sel _ _ _ _ _).2 fun v => ?_` and prove the remaining obligations. Establish `hv` using `(mem_Sel _ _ _ _ _).1 hx v`. Establish `e` using `res_tr (φ : Λ →+* Λ') (vec_smul φ hY) (repOn ρ κ Y) (repOn ρ κ' Y) (repOn_eq_repOn φ hY ρ κ κ' hκ) (Dec (F := D.host.E) (N.plOm.1 v)).subtype continuous_subtype_val x`. Establish `hv' : trL i ρ φ κ κ' hκ hY v (resH1 (repOn ρ κ Y) (Dec (F` using `D.host.E) (N.plOm.1 v)).subtype continuous_subtype_val x) ∈ Formalism.GaloisCohomology.bkCond (repOn ρ κ' Y) N.plOm (X.l i) (Spl i ∪ ↑Q) (bkOn bkP i ρ κ' Y) v := e ▸ hv`. Unfold `Formalism.GaloisCohomology.bkCond at hv' ⊢`.

Use `split_ifs at hv' ⊢ with h1 h2`. Take `⟨w, hw, e'⟩` from `exists_mem_bkOn bkP i ρ φ κ κ' hκ hY v _ hv'`. Rewrite using `[← tr_injective _ _ _ _ _ e']` and apply the resulting hypothesis. Conclude with `Submodule.mem_top`. Conclude with `of_tr_mem_ur _ _ _ _ _ _ _ hv'`.
-/
theorem of_trG_mem_selOn (Q : Finset (PlE D.host)) (x : H1 (repOn ρ κ Y))
    (hx : trG i ρ φ κ κ' hκ hY x ∈ selOn bkP i ρ κ' Y Q) : x ∈ selOn bkP i ρ κ Y Q := by
  refine (mem_Sel _ _ _ _ _).2 fun v => ?_
  have hv := (mem_Sel _ _ _ _ _).1 hx v
  have e := res_tr (φ : Λ →+* Λ') (vec_smul φ hY) (repOn ρ κ Y) (repOn ρ κ' Y) (repOn_eq_repOn φ hY ρ κ κ' hκ)
    (Dec (F := D.host.E) (N.plOm.1 v)).subtype continuous_subtype_val x
  have hv' : trL i ρ φ κ κ' hκ hY v (resH1 (repOn ρ κ Y) (Dec (F := D.host.E) (N.plOm.1 v)).subtype continuous_subtype_val x) ∈
      Formalism.GaloisCohomology.bkCond (repOn ρ κ' Y) N.plOm (X.l i) (Spl i ∪ ↑Q) (bkOn bkP i ρ κ' Y) v := e ▸ hv
  unfold Formalism.GaloisCohomology.bkCond at hv' ⊢
  split_ifs at hv' ⊢ with h1 h2
  · obtain ⟨w, hw, e'⟩ := exists_mem_bkOn bkP i ρ φ κ κ' hκ hY v _ hv'
    rwa [← tr_injective _ _ _ _ _ e']
  · exact Submodule.mem_top
  · exact of_tr_mem_ur _ _ _ _ _ _ _ hv'

/- English proof (translation)
Introduce `D N X bkP i s Λ _ _ Λ' _ _ φ κ κ' hκ Y _ _ _ _ _ hY`. Use `⟨repOn_eq_repOn φ hY (Tgl i s) κ κ' hκ, fun Q f => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Introduce and unpack `⟨z, rfl, hz⟩`. Conclude with `⟨semilinearCoefficientMapCocycles _ _ (idSl (φ : Λ →+* Λ') (vec_smul φ hY)) continuous_id (repOn_eq_repOn φ hY (Tgl i s) κ κ' hκ) z, rfl, trG_mem_selOn bkP i (Tgl i s) φ κ κ' hκ hY Q _ hz⟩`. Introduce and unpack `⟨z, rfl, hz⟩`.

Use `⟨back _ _ (repOn_eq_repOn φ hY (Tgl i s) κ κ' hκ) z, rfl, of_trG_mem_selOn bkP i (Tgl i s) φ κ κ' hκ hY Q _ ?_⟩` and prove the remaining obligations. Establish `e` using `tr_back (φ : Λ →+* Λ') (vec_smul φ hY) (repOn (Tgl i s) κ Y) (repOn (Tgl i s) κ' Y) (repOn_eq_repOn φ hY (Tgl i s) κ κ' hκ) z`. Conclude with `e ▸ hz`.
-/
theorem selC_transfer : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), ∀ (Λ : Type) [CommRing Λ] [Algebra (X.O0 i) Λ] (Λ' : Type) [CommRing Λ'] [Algebra (X.O0 i) Λ'] (φ : Λ →ₐ[X.O0 i] Λ') (κ : GE N →* Λˣ) (κ' : GE N →* Λ'ˣ), (∀ g, ((κ' g : Λ'ˣ) : Λ') = φ (κ g : Λˣ)) → ∀ (Y : Type) [AddCommGroup Y] [Module Λ Y] [Module Λ' Y] [TopologicalSpace Y] [DiscreteTopology Y], (∀ (a : Λ) (y : Y), a • y = φ a • y) → (∀ g m, repOn (Tgl i s) κ Y g m = repOn (Tgl i s) κ' Y g m) ∧ ∀ Q f, SelC bkP i s κ Y Q f ↔ SelC bkP i s κ' Y Q f := by
  intro D N X bkP i s Λ _ _ Λ' _ _ φ κ κ' hκ Y _ _ _ _ _ hY
  refine ⟨repOn_eq_repOn φ hY (Tgl i s) κ κ' hκ, fun Q f => ⟨?_, ?_⟩⟩
  · rintro ⟨z, rfl, hz⟩
    exact ⟨semilinearCoefficientMapCocycles _ _ (idSl (φ : Λ →+* Λ') (vec_smul φ hY)) continuous_id (repOn_eq_repOn φ hY (Tgl i s) κ κ' hκ) z, rfl,
      trG_mem_selOn bkP i (Tgl i s) φ κ κ' hκ hY Q _ hz⟩
  · rintro ⟨z, rfl, hz⟩
    refine ⟨back _ _ (repOn_eq_repOn φ hY (Tgl i s) κ κ' hκ) z, rfl,
      of_trG_mem_selOn bkP i (Tgl i s) φ κ κ' hκ hY Q _ ?_⟩
    have e := tr_back (φ : Λ →+* Λ') (vec_smul φ hY) (repOn (Tgl i s) κ Y) (repOn (Tgl i s) κ' Y)
      (repOn_eq_repOn φ hY (Tgl i s) κ κ' hκ) z
    exact e ▸ hz

end GlobalTheory.NewPrime.ScalarChange

end
