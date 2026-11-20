import Mathlib
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.ReesScheme
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory Limits Opposite

universe u

noncomputable section

variable {A : Type u} [CommRing A] {I : Ideal A} {X : Scheme.{u}} [X.Over (Spec (.of A))]
  {V : X.Opens} (hV : IsAffineOpen V)

abbrev polyRing (I : Ideal A) (V : X.Opens) : CommRingCat.{u} :=
  Γ(reesPolyScheme I X, reesPolyMap I X ⁻¹ᵁ (reesPr I X ⁻¹ᵁ V))

abbrev polyInl (I : Ideal A) (V : X.Opens) : Γ(X, V) ⟶ polyRing I V :=
  (reesPr I X).app V ≫ (reesPolyMap I X).app _

/- English proof (translation)
Use extensionality with `a`. Simplify using the standard rewrite rules.
-/
lemma polyDesc_w : CommRingCat.ofHom (algV X V) ≫ CommRingCat.ofHom Polynomial.C =
    CommRingCat.ofHom (Polynomial.C (R := A)) ≫
      CommRingCat.ofHom (Polynomial.mapRingHom (algV X V)) := by
  ext a
  simp

def polyRingHom : polyRing I V →+* Polynomial Γ(X, V) :=
  ((isPushout_reesPoly (I := I) hV).desc (CommRingCat.ofHom Polynomial.C)
    (CommRingCat.ofHom (Polynomial.mapRingHom (algV X V))) polyDesc_w).hom

/- English proof (translation)
Use `congrArg (fun f : Γ(X, V) ⟶ CommRingCat.of (Polynomial Γ(X, V)) => f.hom c) (IsPushout.inl_desc (isPushout_reesPoly (I := I) hV) _ _ polyDesc_w)` as an intermediate fact. Conclude with `this`.
-/
lemma polyRingHom_inl (c : Γ(X, V)) : polyRingHom hV (polyInl I V c) = Polynomial.C c := by
  have := congrArg (fun f : Γ(X, V) ⟶ CommRingCat.of (Polynomial Γ(X, V)) => f.hom c)
    (IsPushout.inl_desc (isPushout_reesPoly (I := I) hV) _ _ polyDesc_w)
  exact this

/- English proof (translation)
Use `congrArg (fun f : CommRingCat.of (Polynomial A) ⟶ CommRingCat.of (Polynomial Γ(X, V)) => f.hom p) (IsPushout.inr_desc (isPushout_reesPoly (I := I) hV) _ _ polyDesc_w)` as an intermediate fact. Conclude with `this`.
-/
lemma polyRingHom_inr (p : Polynomial A) :
    polyRingHom hV (polyInr I V p) = p.map (algV X V) := by
  have := congrArg
    (fun f : CommRingCat.of (Polynomial A) ⟶ CommRingCat.of (Polynomial Γ(X, V)) => f.hom p)
    (IsPushout.inr_desc (isPushout_reesPoly (I := I) hV) _ _ polyDesc_w)
  exact this

def polyRingInv : Polynomial Γ(X, V) →+* polyRing I V :=
  Polynomial.eval₂RingHom (polyInl I V).hom (polyInr I V Polynomial.X)

include hV in
/- English proof (translation)
Establish `hw` using `(isPushout_reesPoly (I := I) hV).w`. Establish `h : (polyInr I V).hom = Polynomial.eval₂RingHom ((polyInl I V).hom.comp (algV X V)) (polyInr I V Polynomial.X)`. Apply `Polynomial.ringHom_ext` to reduce the goal to its premises. Introduce `a`. Use `congrArg (fun f => f.hom a) hw` as an intermediate fact.

Simplify using `using this.symm`. Simplify using the standard rewrite rules. Conclude with `congrArg (fun f => f p) h`.
-/
lemma polyInr_eq_eval₂ (p : Polynomial A) :
    polyInr I V p = p.eval₂ ((polyInl I V).hom.comp (algV X V)) (polyInr I V Polynomial.X) := by
  have hw := (isPushout_reesPoly (I := I) hV).w
  have h : (polyInr I V).hom = Polynomial.eval₂RingHom ((polyInl I V).hom.comp (algV X V))
      (polyInr I V Polynomial.X) := by
    apply Polynomial.ringHom_ext
    · intro a
      have := congrArg (fun f => f.hom a) hw
      simpa using this.symm
    · simp
  exact congrArg (fun f => f p) h

def polyRingEquiv : polyRing I V ≃+* Polynomial Γ(X, V) :=
  RingEquiv.ofRingHom (polyRingHom hV) (polyRingInv (I := I) (V := V))
    (by
      apply Polynomial.ringHom_ext
      · intro c
        change polyRingHom hV ((polyRingInv (I := I) (V := V)) (Polynomial.C c)) = Polynomial.C c
        rw [polyRingInv, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
        exact polyRingHom_inl hV c
      · change polyRingHom hV ((polyRingInv (I := I) (V := V)) Polynomial.X) = Polynomial.X
        rw [polyRingInv, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, polyRingHom_inr,
          Polynomial.map_X])
    (by
      have h := (isPushout_reesPoly (I := I) hV).hom_ext
        (k := CommRingCat.ofHom ((polyRingInv (I := I) (V := V)).comp (polyRingHom hV)))
        (l := 𝟙 _) (by
          ext c
          change (polyRingInv (I := I) (V := V)) (polyRingHom hV (polyInl I V c)) = polyInl I V c
          rw [polyRingHom_inl, polyRingInv, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]) (by
          refine CommRingCat.hom_ext (RingHom.ext fun p => ?_)
          change (polyRingInv (I := I) (V := V)) (polyRingHom hV (polyInr I V p)) = polyInr I V p
          rw [polyRingHom_inr, polyRingInv, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_map]
          exact (polyInr_eq_eval₂ hV p).symm)
      exact congrArg CommRingCat.Hom.hom h)

include hV in

/- English proof (translation)
Establish `hw` using `(isPushout_app_of_isPullback (isPullback_reesPoly I X) (hV.preimage (reesPr I X))).w`. Rewrite using `[reesInr, polyInr, Category.assoc, hw, ← Category.assoc, ← Category.assoc, Scheme.ΓSpecIso_inv_naturality]`.
-/
lemma reesInr_comp :
    reesInr I V ≫ (reesPolyMap I X).app _ =
      CommRingCat.ofHom (algebraMap (reesAlgebra I) (Polynomial A)) ≫ polyInr I V := by
  have hw := (isPushout_app_of_isPullback (isPullback_reesPoly I X) (hV.preimage (reesPr I X))).w
  rw [reesInr, polyInr, Category.assoc, hw, ← Category.assoc, ← Category.assoc,
    Scheme.ΓSpecIso_inv_naturality]

def reesRingHom : Γ(reesScheme I X, reesPr I X ⁻¹ᵁ V) →+* Polynomial Γ(X, V) :=
  (polyRingHom hV).comp ((reesPolyMap I X).app (reesPr I X ⁻¹ᵁ V)).hom

/- English proof (translation)
The claim follows from `polyRingHom_inl hV c`.
-/
lemma reesRingHom_inl (c : Γ(X, V)) : reesRingHom hV ((reesPr I X).app V c) = Polynomial.C c :=
  polyRingHom_inl hV c

/- English proof (translation)
Use `congrArg (fun f : CommRingCat.of (reesAlgebra I) ⟶ polyRing I V => f.hom r) (reesInr_comp (I := I) hV)` as an intermediate fact. Express the relevant statement in the definitionally equal form `polyRingHom hV (((reesInr I V ≫ (reesPolyMap I X).app _)).hom r) = _`. Rewrite using `[this]`. Conclude with `polyRingHom_inr hV _`.
-/
lemma reesRingHom_inr (r : reesAlgebra I) :
    reesRingHom hV (reesInr I V r) = (r : Polynomial A).map (algV X V) := by
  have := congrArg (fun f : CommRingCat.of (reesAlgebra I) ⟶ polyRing I V => f.hom r)
    (reesInr_comp (I := I) hV)
  change polyRingHom hV (((reesInr I V ≫ (reesPolyMap I X).app _)).hom r) = _
  rw [this]
  exact polyRingHom_inr hV _

variable (I X V) in

def reesCoeffRing : Subring (Polynomial Γ(X, V)) where
  carrier := {p | ∀ n, p.coeff n ∈ (I.map (algV X V)) ^ n}
  one_mem' n := by
    change Polynomial.coeff 1 n ∈ _
    rw [Polynomial.coeff_one]
    split_ifs with h
    · subst h
      simp
    · exact zero_mem _
  mul_mem' {p q} hp hq n := by
    change (p * q).coeff n ∈ _
    rw [Polynomial.coeff_mul]
    refine Ideal.sum_mem _ fun x hx => ?_
    have hx : x.1 + x.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.1 hx
    rw [← hx, pow_add]
    exact Ideal.mul_mem_mul (hp x.1) (hq x.2)
  zero_mem' n := by simp
  add_mem' {p q} hp hq n := by
    change (p + q).coeff n ∈ _
    rw [Polynomial.coeff_add]
    exact add_mem (hp n) (hq n)
  neg_mem' {p} hp n := by
    change (-p).coeff n ∈ _
    rw [Polynomial.coeff_neg]
    exact neg_mem (hp n)

/- English proof (translation)
Introduce `n`. Rewrite using `[Polynomial.coeff_C]`. Use `split_ifs with h`. Substitute `h` using the available equality. Simplify using the standard rewrite rules.

Conclude with `zero_mem _`.
-/
lemma C_mem_reesCoeffRing (c : Γ(X, V)) : Polynomial.C c ∈ reesCoeffRing I X V := by
  intro n
  rw [Polynomial.coeff_C]
  split_ifs with h
  · subst h
    simp
  · exact zero_mem _

/- English proof (translation)
Introduce `n`. Rewrite using `[Polynomial.coeff_map, ← Ideal.map_pow]`. Conclude with `Ideal.mem_map_of_mem _ ((mem_reesAlgebra_iff I _).1 r.2 n)`.
-/
lemma map_mem_reesCoeffRing (r : reesAlgebra I) :
    (r : Polynomial A).map (algV X V) ∈ reesCoeffRing I X V := by
  intro n
  rw [Polynomial.coeff_map, ← Ideal.map_pow]
  exact Ideal.mem_map_of_mem _ ((mem_reesAlgebra_iff I _).1 r.2 n)

/- English proof (translation)
Set `l : Γ(X, V) ⟶ CommRingCat.of (reesCoeffRing I X V)` to `CommRingCat.ofHom ((Polynomial.C).codRestrict (reesCoeffRing I X V) C_mem_reesCoeffRing)`. Set `r : CommRingCat.of (reesAlgebra I) ⟶ CommRingCat.of (reesCoeffRing I X V)` to `CommRingCat.ofHom (((Polynomial.mapRingHom (algV X V)).comp (reesAlgebra I).val.toRingHom) |>.codRestrict (reesCoeffRing I X V) map_mem_reesCoeffRing)`. Establish `hw' : CommRingCat.ofHom (algV X V) ≫ l = CommRingCat.ofHom (algebraMap A (reesAlgebra I)) ≫ r`. Use `CommRingCat.hom_ext (RingHom.ext fun a => Subtype.ext ?_)` and prove the remaining obligations. Simplify using `[l, r]`.

Set `d` to `(isPushout_rees (I := I) hV).desc l r hw'`. Establish `h : (CommRingCat.ofHom (reesRingHom hV) : Γ(reesScheme I X, reesPr I X ⁻¹ᵁ V) ⟶ CommRingCat.of (Polynomial Γ(X, V))) = d ≫ CommRingCat.ofHom (reesCoeffRing I X V).subtype`. Apply `(isPushout_rees (I := I) hV).hom_ext` to reduce the goal to its premises. Use `CommRingCat.hom_ext (RingHom.ext fun c => ?_)` and prove the remaining obligations. Use `congrArg (fun f : Γ(X, V) ⟶ CommRingCat.of (reesCoeffRing I X V) => (f.hom c : Polynomial Γ(X, V))) (IsPushout.inl_desc (isPushout_rees (I := I) hV) l r hw')` as an intermediate fact.

Conclude with `(reesRingHom_inl hV c).trans this.symm`. Use `CommRingCat.hom_ext (RingHom.ext fun x => ?_)` and prove the remaining obligations. Use `congrArg (fun f : CommRingCat.of (reesAlgebra I) ⟶ CommRingCat.of (reesCoeffRing I X V) => (f.hom x : Polynomial Γ(X, V))) (IsPushout.inr_desc (isPushout_rees (I := I) hV) l r hw')` as an intermediate fact. Conclude with `(reesRingHom_inr hV x).trans this.symm`. Use `congrArg (fun f : Γ(reesScheme I X, reesPr I X ⁻¹ᵁ V) ⟶ CommRingCat.of (Polynomial Γ(X, V)) => f.hom s) h` as an intermediate fact.

Express the relevant statement in the definitionally equal form `reesRingHom hV s ∈ _`. Rewrite using `[show reesRingHom hV s = ((d.hom s : reesCoeffRing I X V) : Polynomial Γ(X, V)) from this]`. Conclude with `(d.hom s).2`.
-/
theorem reesRingHom_mem (s : Γ(reesScheme I X, reesPr I X ⁻¹ᵁ V)) :
    reesRingHom hV s ∈ reesCoeffRing I X V := by
  let l : Γ(X, V) ⟶ CommRingCat.of (reesCoeffRing I X V) :=
    CommRingCat.ofHom ((Polynomial.C).codRestrict (reesCoeffRing I X V) C_mem_reesCoeffRing)
  let r : CommRingCat.of (reesAlgebra I) ⟶ CommRingCat.of (reesCoeffRing I X V) :=
    CommRingCat.ofHom (((Polynomial.mapRingHom (algV X V)).comp (reesAlgebra I).val.toRingHom)
      |>.codRestrict (reesCoeffRing I X V) map_mem_reesCoeffRing)
  have hw' : CommRingCat.ofHom (algV X V) ≫ l =
      CommRingCat.ofHom (algebraMap A (reesAlgebra I)) ≫ r := by
    refine CommRingCat.hom_ext (RingHom.ext fun a => Subtype.ext ?_)
    simp [l, r]
  let d := (isPushout_rees (I := I) hV).desc l r hw'
  have h : (CommRingCat.ofHom (reesRingHom hV) :
      Γ(reesScheme I X, reesPr I X ⁻¹ᵁ V) ⟶ CommRingCat.of (Polynomial Γ(X, V))) =
      d ≫ CommRingCat.ofHom (reesCoeffRing I X V).subtype := by
    apply (isPushout_rees (I := I) hV).hom_ext
    · refine CommRingCat.hom_ext (RingHom.ext fun c => ?_)
      have := congrArg (fun f : Γ(X, V) ⟶ CommRingCat.of (reesCoeffRing I X V) =>
        (f.hom c : Polynomial Γ(X, V))) (IsPushout.inl_desc (isPushout_rees (I := I) hV) l r hw')
      exact (reesRingHom_inl hV c).trans this.symm
    · refine CommRingCat.hom_ext (RingHom.ext fun x => ?_)
      have := congrArg (fun f : CommRingCat.of (reesAlgebra I) ⟶ CommRingCat.of (reesCoeffRing I X V) =>
        (f.hom x : Polynomial Γ(X, V))) (IsPushout.inr_desc (isPushout_rees (I := I) hV) l r hw')
      exact (reesRingHom_inr hV x).trans this.symm
  have := congrArg (fun f : Γ(reesScheme I X, reesPr I X ⁻¹ᵁ V) ⟶
    CommRingCat.of (Polynomial Γ(X, V)) => f.hom s) h
  change reesRingHom hV s ∈ _
  rw [show reesRingHom hV s = ((d.hom s : reesCoeffRing I X V) : Polynomial Γ(X, V)) from this]
  exact (d.hom s).2

end

end GroundTheory.Arith.SchemeCoh
