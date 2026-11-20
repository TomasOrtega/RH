import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualMapCompDualMap
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechKS
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CechKS

variable {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A]

/- English proof (translation)
The claim follows from `(congrArg (P.x ≫ ·) (Category.comp_id _)).symm.trans P.w`.
-/
theorem cechPt_over (P : GPt A) : P.x ≫ A.hom = spMap (algebraMap K P.B) :=
  (congrArg (P.x ≫ ·) (Category.comp_id _)).symm.trans P.w

@[reducible] def Pt.cst (P : GPt A) : GPt A where
  B := DualNumber P.B
  x := spMap (algebraMap P.B (DualNumber P.B)) ≫ P.x
  w := (congrArg (_ ≫ ·) (Category.comp_id A.hom)).trans (by
    rw [Category.assoc, cechPt_over, ← Cris.spMap_comp, ← IsScalarTower.algebraMap_eq])

/- English proof (translation)
The claim follows from `fun _ _ ↦ h (Set.mem_univ _)`.
-/
theorem Pt.In.cst {P : GPt A} {U : A.left.Opens} (h : P.In U) : P.cst.In U :=
  fun _ _ ↦ h (Set.mem_univ _)

/- English proof (translation)
Apply the tactic sequence `ext r <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.algebraMap_eq_inl']`.
-/
theorem cst_base (P : GPt A) :
    (dualMap (algebraMap K P.B)).comp (algebraMap K (DualNumber K)) = algebraMap K (DualNumber P.B) := by
  ext r <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.algebraMap_eq_inl']

/- English proof (translation)
Use extensionality with `r`. Simplify using `[TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.algebraMap_eq_inl']`.
-/
theorem fst_comp_dualMap (P : GPt A) :
    (TrivSqZeroExt.fstHom K P.B P.B : DualNumber P.B →+* P.B).comp (algebraMap K (DualNumber P.B)) = algebraMap K P.B := by
  ext r; simp [TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.algebraMap_eq_inl']

/- English proof (translation)
Use extensionality with `r`. Simplify using `[TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.algebraMap_eq_inl']`.
-/
theorem fst_comp_inl (P : GPt A) :
    (TrivSqZeroExt.fstHom K P.B P.B : DualNumber P.B →+* P.B).comp (algebraMap P.B (DualNumber P.B)) = RingHom.id _ := by
  ext r; simp [TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.algebraMap_eq_inl']

/- English proof (translation)
Use `show _ ≫ spMap _ ≫ P.x = P.x`. Rewrite using `[← Category.assoc, ← Cris.spMap_comp, fst_comp_inl, Cris.spMap_id, Category.id_comp]`.
-/
theorem cst_red (P : GPt A) :
    spMap (TrivSqZeroExt.fstHom K P.B P.B : DualNumber P.B →+* P.B) ≫ P.cst.x = P.x := by
  show _ ≫ spMap _ ≫ P.x = P.x
  rw [← Category.assoc, ← Cris.spMap_comp, fst_comp_inl, Cris.spMap_id, Category.id_comp]

/- English proof (translation)
Use `show TrivSqZeroExt.fst (valR (spMap _ ≫ P.x) U g) = _`. Rewrite using `[GlobalTheory.Points.valR_spMap_comp _ _ _ hU]`. Simplify using `[TrivSqZeroExt.algebraMap_eq_inl]`.
-/
theorem cst_val (P : GPt A) {U : A.left.Opens} (hU : P.In U) (g : Γ(A.left, U)) :
    TrivSqZeroExt.fst (valR P.cst.x U g) = valR P.x U g := by
  show TrivSqZeroExt.fst (valR (spMap _ ≫ P.x) U g) = _
  rw [GlobalTheory.Points.valR_spMap_comp _ _ _ hU]
  simp [TrivSqZeroExt.algebraMap_eq_inl]

/- English proof (translation)
Establish `hin : ⊤ ≤ P.cst.trx v ⁻¹ᵁ U` using `hU.cst.tr hv`. Establish `hm` using `(P.cst.isTransl_trx v).map (TrivSqZeroExt.fstHom K P.B P.B : DualNumber P.B →+* P.B)`. Establish `e1 : (TrivSqZeroExt.fstHom K P.B P.B : DualNumber P.B →+* P.B).comp (algebraMap K P.cst.B) = algebraMap K P.B` using `fst_comp_dualMap P`. Rewrite `hm` using `[e1, cst_red]`. Rewrite using `[← hm.unique (P.isTransl_trx v), GlobalTheory.Points.valR_spMap_comp _ _ _ hin]`.

Simplify using `[dualMap]`.
-/
theorem cst_trx_val (P : GPt A) {v : epsR K ⟶ A} (hv : IsTangent v) {U : A.left.Opens} (hU : P.In U)
    (g : Γ(A.left, U)) : TrivSqZeroExt.fst (valR (P.cst.trx v) U g).snd = (valR (P.trx v) U g).snd := by
  have hin : ⊤ ≤ P.cst.trx v ⁻¹ᵁ U := hU.cst.tr hv
  have hm := (P.cst.isTransl_trx v).map (TrivSqZeroExt.fstHom K P.B P.B : DualNumber P.B →+* P.B)
  have e1 : (TrivSqZeroExt.fstHom K P.B P.B : DualNumber P.B →+* P.B).comp (algebraMap K P.cst.B) = algebraMap K P.B :=
    fst_comp_dualMap P
  rw [e1, cst_red] at hm
  rw [← hm.unique (P.isTransl_trx v), GlobalTheory.Points.valR_spMap_comp _ _ _ hin]
  simp [dualMap]

/- English proof (translation)
Apply the tactic sequence `ext <;> simp [dualMap, RingHom.algebraMap_toAlgebra]`.
-/
theorem eps_eq (P : GPt A) :
    letI : Algebra (DualNumber K) (DualNumber P.B) := (dualMap (algebraMap K P.B)).toAlgebra
    algebraMap (DualNumber K) (DualNumber P.B) DualNumber.eps = TrivSqZeroExt.inr 1 := by
  ext <;> simp [dualMap, RingHom.algebraMap_toAlgebra]

/- English proof (translation)
Introduce `K _ A _ A' _ i L n u θ hu h`. Take `⟨J, W, c, lam, hcov, hWc, hlift, hdiff⟩` from `h`. Establish `hx : ∀ P : GPt A, letI : Algebra (DualNumber K) (DualNumber P.B)` using `(dualMap (algebraMap K P.B)).toAlgebra P.cst.x ≫ A.hom = spMap ((algebraMap (DualNumber K) (DualNumber P.B)).comp (algebraMap K (DualNumber K))) := fun P ↦ (cechPt_over P.cst).trans (congrArg spMap (cst_base P).symm)`. Use `⟨J, W, c, fun k P ↦ @lam k (DualNumber P.B) _ (dualMap (algebraMap K P.B)).toAlgebra P.cst.x, hcov, hWc, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `k P hP`.

Use `letI : Algebra (DualNumber K) (DualNumber P.B) := (dualMap (algebraMap K P.B)).toAlgebra`. Take `⟨h1, h2, -⟩` from `hlift k (DualNumber P.B) P.cst.x (hx P) hP.cst`. Use `⟨(congrArg (_ ≫ ·) (Category.comp_id _)).trans h1, ?_⟩` and prove the remaining obligations. Set `I` to `Ideal.span {algebraMap (DualNumber K) (DualNumber P.B) DualNumber.eps}`. Establish `hI : ∀ a ∈ I, (TrivSqZeroExt.fstHom K P.B P.B : DualNumber P.B →+* P.B) a = 0`.

Introduce `a ha`. Take `⟨b, rfl⟩` from `Ideal.mem_span_singleton'.mp ha`. Rewrite using `[eps_eq P]`. Simplify using the standard rewrite rules. Establish `hq : (Ideal.Quotient.lift I _ hI).comp (Ideal.Quotient.mk I) = (TrivSqZeroExt.fstHom K P.B P.B : DualNumber P.B →+* P.B)` using `RingHom.ext fun _ ↦ rfl`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Category.assoc, ← Cris.spMap_comp, hq]`. Use `_ = spMap (Ideal.Quotient.lift I _ hI) ≫ spMap (Ideal.Quotient.mk I) ≫ P.cst.x ≫ i := by rw [h2]`. Use `_ = (spMap (TrivSqZeroExt.fstHom K P.B P.B : DualNumber P.B →+* P.B) ≫ P.cst.x) ≫ i := by`. Rewrite using `[← Category.assoc, ← Category.assoc, ← Cris.spMap_comp, hq, Category.assoc]`.

Use `_ = P.x ≫ i := by rw [cst_red]`. Introduce `k P Q φ hP`. Use `letI : Algebra (DualNumber K) (DualNumber P.B) := (dualMap (algebraMap K P.B)).toAlgebra`. Use `letI : Algebra (DualNumber K) (DualNumber Q.B) := (dualMap (algebraMap K Q.B)).toAlgebra`. Set `ρ : DualNumber P.B →ₐ[DualNumber K] DualNumber Q.B` to `{ dualMap (φ.ρ : P.B →+* Q.B) with commutes' := fun r ↦ by`.

Apply the tactic sequence `ext <;> simp [dualMap, RingHom.algebraMap_toAlgebra] }`. Establish `h3` using `(hlift k (DualNumber P.B) P.cst.x (hx P) hP.cst).2.2 (DualNumber Q.B) ρ`. Establish `hc : spMap (dualMap (φ.ρ : P.B →+* Q.B)) ≫ P.cst.x = Q.cst.x` using `by show spMap _ ≫ spMap _ ≫ P.x = spMap _ ≫ Q.x`. Rewrite using `[← φ.pt, ← Category.assoc, ← Category.assoc, ← Cris.spMap_comp, ← Cris.spMap_comp, dualMap_comp_algebraMap]`. Conclude with `h3.trans (congrArg _ hc)`.

Introduce `k k' P U f hk hk' hU`. Use `letI : Algebra (DualNumber K) (DualNumber P.B) := (dualMap (algebraMap K P.B)).toAlgebra`. Establish `ht : ∀ a, IsTransl ((algebraMap (DualNumber K) (DualNumber P.B)).comp (algebraMap K (DualNumber K))) P.cst.x (u a) (P.cst.trx (u a))` using `fun a ↦ by`. Rewrite using `[show (algebraMap (DualNumber K) (DualNumber P.B)).comp (algebraMap K (DualNumber K)) = algebraMap K P.cst.B from cst_base P]`. Conclude with `P.cst.isTransl_trx (u a)`.

Establish `hd` using `hdiff k k' (DualNumber P.B) P.cst.x U f (fun a ↦ P.cst.trx (u a)) (hx P) (hk.cst.inf hk'.cst) hU.cst ht`. Use `hd.trans ?_` and prove the remaining obligations. Establish `hg : P.In (L.U (c k) ⊓ L.U (c k'))` using `(hk.mono (hWc k)).inf (hk'.mono (hWc k'))`. Establish `e1 : ∀ a, TrivSqZeroExt.fst (valR (P.cst.trx (u a)) _ (L.g (c k) (c k')).val).snd = (valR (P.trx (u a)) _ (L.g (c k) (c k')).val).snd` using `fun a ↦ cst_trx_val P (hu a) hg _`. Establish `e2 : ∀ a, TrivSqZeroExt.fst (valR (P.cst.trx (u a)) (i ⁻¹ᵁ U) ((i.app U).hom f)).snd = (valR (P.trx (u a)) (i ⁻¹ᵁ U) ((i.app U).hom f)).snd` using `fun a ↦ cst_trx_val P (hu a) hU _`.

Establish `e3 : TrivSqZeroExt.fst (valR P.cst.x _ (L.g (c k) (c k'))⁻¹.val) = valR P.x _ (L.g (c k) (c k'))⁻¹.val` using `cst_val P hg _`. Establish `e4 : ∀ r : K, TrivSqZeroExt.fst (((algebraMap (DualNumber K) (DualNumber P.B)).comp (algebraMap K (DualNumber K))) r) = algebraMap K P.B r`. Introduce `r`. Rewrite using `[show (algebraMap (DualNumber K) (DualNumber P.B)).comp (algebraMap K (DualNumber K)) = algebraMap K P.cst.B from cst_base P]`. Simplify using `[TrivSqZeroExt.algebraMap_eq_inl']`.

Rewrite using `[eps_eq P]`. Establish `hS : ∀ S : DualNumber P.B, TrivSqZeroExt.inr (1 : P.B) * S = TrivSqZeroExt.inr S.fst` using `fun S ↦ by`. Apply the tactic sequence `ext <;> simp`. Rewrite using `[hS]`. Use `congr 1`.

Express the relevant statement in the definitionally equal form `(TrivSqZeroExt.fstHom K P.B P.B) _ = _`. Simplify using `only [map_sum, map_mul, TrivSqZeroExt.fstHom_apply]`. Simplify using `only [e1, e2, e3, e4, dlog, Finset.sum_mul]`.
-/
theorem cechKS_lifts : ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A] (A' : Over (Sp (DualNumber K))) [GrpObj A'] (i : A.left ⟶ A'.left) (L : LB A.left) (n : ℕ) (u : Fin n → (epsR K ⟶ A)) (θ : Matrix (Fin n) (Fin n) K), (∀ a, IsTangent (u a)) → IsCechKS A A' i L u θ → ∃ (J : Type) (W : J → A.left.Opens) (c : J → L.ι) (y : J → ∀ P : GPt A, Sp (DualNumber P.B) ⟶ A'.left), ⨆ k, W k = ⊤ ∧ (∀ k, W k ≤ L.U (c k)) ∧ (∀ (k : J) (P : GPt A), P.In (W k) → IsLift i P (y k P)) ∧ (∀ (k : J) (P Q : GPt A) (φ : P.Hom Q), P.In (W k) → spMap (dualMap (φ.ρ : P.B →+* Q.B)) ≫ y k P = y k Q) ∧ ∀ (k k' : J) (P : GPt A) (U : A'.left.Opens) (f : Γ(A'.left, U)), P.In (W k) → P.In (W k') → P.In (i ⁻¹ᵁ U) → valR (y k P) U f - valR (y k' P) U f = (TrivSqZeroExt.inr (∑ a, (∑ b, algebraMap K P.B (θ a b) * dlog L (u b) (c k) (c k') P) * (valR (P.trx (u a)) (i ⁻¹ᵁ U) ((i.app U).hom f)).snd) : DualNumber P.B) := by
  intro K _ A _ A' _ i L n u θ hu h
  obtain ⟨J, W, c, lam, hcov, hWc, hlift, hdiff⟩ := h
  have hx : ∀ P : GPt A, letI : Algebra (DualNumber K) (DualNumber P.B) := (dualMap (algebraMap K P.B)).toAlgebra
      P.cst.x ≫ A.hom = spMap ((algebraMap (DualNumber K) (DualNumber P.B)).comp (algebraMap K (DualNumber K))) :=
    fun P ↦ (cechPt_over P.cst).trans (congrArg spMap (cst_base P).symm)
  refine ⟨J, W, c, fun k P ↦ @lam k (DualNumber P.B) _ (dualMap (algebraMap K P.B)).toAlgebra P.cst.x,
    hcov, hWc, ?_, ?_, ?_⟩
  · intro k P hP
    letI : Algebra (DualNumber K) (DualNumber P.B) := (dualMap (algebraMap K P.B)).toAlgebra
    obtain ⟨h1, h2, -⟩ := hlift k (DualNumber P.B) P.cst.x (hx P) hP.cst
    refine ⟨(congrArg (_ ≫ ·) (Category.comp_id _)).trans h1, ?_⟩
    let I := Ideal.span {algebraMap (DualNumber K) (DualNumber P.B) DualNumber.eps}
    have hI : ∀ a ∈ I, (TrivSqZeroExt.fstHom K P.B P.B : DualNumber P.B →+* P.B) a = 0 := by
      intro a ha
      obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
      rw [eps_eq P]
      simp
    have hq : (Ideal.Quotient.lift I _ hI).comp (Ideal.Quotient.mk I) =
        (TrivSqZeroExt.fstHom K P.B P.B : DualNumber P.B →+* P.B) := RingHom.ext fun _ ↦ rfl
    calc spMap (TrivSqZeroExt.fstHom K P.B P.B : DualNumber P.B →+* P.B) ≫ _
        = spMap (Ideal.Quotient.lift I _ hI) ≫ spMap (Ideal.Quotient.mk I) ≫ lam k (DualNumber P.B) P.cst.x := by
          rw [← Category.assoc, ← Cris.spMap_comp, hq]
      _ = spMap (Ideal.Quotient.lift I _ hI) ≫ spMap (Ideal.Quotient.mk I) ≫ P.cst.x ≫ i := by rw [h2]
      _ = (spMap (TrivSqZeroExt.fstHom K P.B P.B : DualNumber P.B →+* P.B) ≫ P.cst.x) ≫ i := by
          rw [← Category.assoc, ← Category.assoc, ← Cris.spMap_comp, hq, Category.assoc]
      _ = P.x ≫ i := by rw [cst_red]
  · intro k P Q φ hP
    letI : Algebra (DualNumber K) (DualNumber P.B) := (dualMap (algebraMap K P.B)).toAlgebra
    letI : Algebra (DualNumber K) (DualNumber Q.B) := (dualMap (algebraMap K Q.B)).toAlgebra
    let ρ : DualNumber P.B →ₐ[DualNumber K] DualNumber Q.B :=
      { dualMap (φ.ρ : P.B →+* Q.B) with
        commutes' := fun r ↦ by
          ext <;> simp [dualMap, RingHom.algebraMap_toAlgebra] }
    have h3 := (hlift k (DualNumber P.B) P.cst.x (hx P) hP.cst).2.2 (DualNumber Q.B) ρ
    have hc : spMap (dualMap (φ.ρ : P.B →+* Q.B)) ≫ P.cst.x = Q.cst.x := by
      show spMap _ ≫ spMap _ ≫ P.x = spMap _ ≫ Q.x
      rw [← φ.pt, ← Category.assoc, ← Category.assoc, ← Cris.spMap_comp, ← Cris.spMap_comp, dualMap_comp_algebraMap]
    exact h3.trans (congrArg _ hc)
  · intro k k' P U f hk hk' hU
    letI : Algebra (DualNumber K) (DualNumber P.B) := (dualMap (algebraMap K P.B)).toAlgebra
    have ht : ∀ a, IsTransl ((algebraMap (DualNumber K) (DualNumber P.B)).comp (algebraMap K (DualNumber K)))
        P.cst.x (u a) (P.cst.trx (u a)) := fun a ↦ by
      rw [show (algebraMap (DualNumber K) (DualNumber P.B)).comp (algebraMap K (DualNumber K)) =
        algebraMap K P.cst.B from cst_base P]
      exact P.cst.isTransl_trx (u a)
    have hd := hdiff k k' (DualNumber P.B) P.cst.x U f (fun a ↦ P.cst.trx (u a)) (hx P) (hk.cst.inf hk'.cst)
      hU.cst ht
    refine hd.trans ?_
    have hg : P.In (L.U (c k) ⊓ L.U (c k')) := (hk.mono (hWc k)).inf (hk'.mono (hWc k'))
    have e1 : ∀ a, TrivSqZeroExt.fst (valR (P.cst.trx (u a)) _ (L.g (c k) (c k')).val).snd =
        (valR (P.trx (u a)) _ (L.g (c k) (c k')).val).snd := fun a ↦ cst_trx_val P (hu a) hg _
    have e2 : ∀ a, TrivSqZeroExt.fst (valR (P.cst.trx (u a)) (i ⁻¹ᵁ U) ((i.app U).hom f)).snd =
        (valR (P.trx (u a)) (i ⁻¹ᵁ U) ((i.app U).hom f)).snd := fun a ↦ cst_trx_val P (hu a) hU _
    have e3 : TrivSqZeroExt.fst (valR P.cst.x _ (L.g (c k) (c k'))⁻¹.val) = valR P.x _ (L.g (c k) (c k'))⁻¹.val :=
      cst_val P hg _
    have e4 : ∀ r : K, TrivSqZeroExt.fst
        (((algebraMap (DualNumber K) (DualNumber P.B)).comp (algebraMap K (DualNumber K))) r) = algebraMap K P.B r := by
      intro r
      rw [show (algebraMap (DualNumber K) (DualNumber P.B)).comp (algebraMap K (DualNumber K)) =
        algebraMap K P.cst.B from cst_base P]
      simp [TrivSqZeroExt.algebraMap_eq_inl']
    rw [eps_eq P]
    have hS : ∀ S : DualNumber P.B, TrivSqZeroExt.inr (1 : P.B) * S = TrivSqZeroExt.inr S.fst := fun S ↦ by
      ext <;> simp
    rw [hS]
    congr 1
    change (TrivSqZeroExt.fstHom K P.B P.B) _ = _
    simp only [map_sum, map_mul, TrivSqZeroExt.fstHom_apply]
    simp only [e1, e2, e3, e4, dlog, Finset.sum_mul]

end GlobalTheory.CechKS
