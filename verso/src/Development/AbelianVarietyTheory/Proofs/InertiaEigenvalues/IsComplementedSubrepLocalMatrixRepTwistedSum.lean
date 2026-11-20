import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSummandTw
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition GlobalTheory.Pass.LocDual

noncomputable section
namespace GlobalTheory.Pass.LocDual.Summand

/- English proof (translation)
Set `e` to `LinearEquiv.ofInjective j hinj`. Set `P` to `Submodule.linearProjOfIsCompl (LinearMap.range j) W' hc`. Establish `hjB : ∀ v, j ((e.symm.toLinearMap ∘ₗ P) v) = (P v : Fin n → K)`. Introduce `v`. Use `congrArg Subtype.val (e.apply_symm_apply (P v))` as an intermediate fact.

Simplify `this` using `[e, LinearEquiv.ofInjective_apply]`. Establish `hP : ∀ v, ∀ a ∈ LinearMap.range j, ∀ b ∈ W', v = a + b → (P v : Fin n → K) = a`. Introduce `v a ha b hb hv`. Substitute `hv` using the available equality. Establish `h1 : P a = ⟨a, ha⟩` using `Submodule.linearProjOfIsCompl_apply_left hc ⟨a, ha⟩`.

Establish `h2 : P b = 0` using `Submodule.linearProjOfIsCompl_apply_right hc ⟨b, hb⟩`. Rewrite using `[map_add, Submodule.coe_add, h1, h2]`. Simplify using the standard rewrite rules. Use `⟨e.symm.toLinearMap ∘ₗ P, ?_, ?_⟩` and prove the remaining obligations. Introduce `u`.

Apply `hinj` to reduce the goal to its premises. Rewrite using `[hjB]`. Conclude with `hP _ _ ⟨u, rfl⟩ 0 W'.zero_mem (by simp)`. Introduce `g v`. Establish `hv : v ∈ LinearMap.range j ⊔ W'` using `by rw [hc.sup_eq_top]; trivial`.

Take `⟨a, ha, b, hb, rfl⟩` from `Submodule.mem_sup.mp hv`. Rewrite using `[hjB, hjB, hP (a + b) a ha b hb rfl, hP _ _ (hW g a ha) _ (hW' g b hb) (Matrix.mulVec_add _ _ _)]`.
-/
theorem exists_left_inv {K : Type} [Field K] {Γ : Type} [Group Γ] {n k : ℕ}
    (A : Γ → Matrix (Fin n) (Fin n) K) (j : (Fin k → K) →ₗ[K] (Fin n → K)) (hinj : Function.Injective j)
    (W' : Submodule K (Fin n → K)) (hc : IsCompl (LinearMap.range j) W')
    (hW : ∀ g, ∀ v ∈ LinearMap.range j, (A g).mulVec v ∈ LinearMap.range j)
    (hW' : ∀ g, ∀ v ∈ W', (A g).mulVec v ∈ W') :
    ∃ Bl : (Fin n → K) →ₗ[K] (Fin k → K), (∀ u, Bl (j u) = u) ∧
      ∀ g v, j (Bl ((A g).mulVec v)) = (A g).mulVec (j (Bl v)) := by
  let e := LinearEquiv.ofInjective j hinj
  let P := Submodule.linearProjOfIsCompl (LinearMap.range j) W' hc
  have hjB : ∀ v, j ((e.symm.toLinearMap ∘ₗ P) v) = (P v : Fin n → K) := by
    intro v
    have := congrArg Subtype.val (e.apply_symm_apply (P v))
    simpa [e, LinearEquiv.ofInjective_apply] using this
  have hP : ∀ v, ∀ a ∈ LinearMap.range j, ∀ b ∈ W', v = a + b → (P v : Fin n → K) = a := by
    intro v a ha b hb hv
    subst hv
    have h1 : P a = ⟨a, ha⟩ := Submodule.linearProjOfIsCompl_apply_left hc ⟨a, ha⟩
    have h2 : P b = 0 := Submodule.linearProjOfIsCompl_apply_right hc ⟨b, hb⟩
    rw [map_add, Submodule.coe_add, h1, h2]
    simp
  refine ⟨e.symm.toLinearMap ∘ₗ P, ?_, ?_⟩
  · intro u
    apply hinj
    rw [hjB]
    exact hP _ _ ⟨u, rfl⟩ 0 W'.zero_mem (by simp)
  · intro g v
    have hv : v ∈ LinearMap.range j ⊔ W' := by rw [hc.sup_eq_top]; trivial
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hv
    rw [hjB, hjB, hP (a + b) a ha b hb rfl, hP _ _ (hW g a ha) _ (hW' g b hb) (Matrix.mulVec_add _ _ _)]

/- English proof (translation)
Use `Matrix.ext fun a b => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(D.nbr i w hw).toLL (M (decS D.nd w (Br.iota D.nbr i w hw g)) a b) = Br.toLLK (D.nbr i w hw) (toK D.nd i (M (decS D.nd w (Br.iota D.nbr i w hw g)) a b))`. Rewrite using `[Br.toLLK_alg]`. Both sides reduce to the same expression.
-/
theorem loc_eq (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : w ∈ placesOver D.host.E (D.nd.l i)) {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i))
    (g : Br.G D.nbr i w hw) :
    Br.loc D.nbr i w hw M g =
      (mapM (toK D.nd i) M (decS D.nd w (Br.iota D.nbr i w hw g))).map (Br.toLLK (D.nbr i w hw)) := by
  refine Matrix.ext fun a b => ?_
  change (D.nbr i w hw).toLL (M (decS D.nd w (Br.iota D.nbr i w hw g)) a b) =
    Br.toLLK (D.nbr i w hw) (toK D.nd i (M (decS D.nd w (Br.iota D.nbr i w hw g)) a b))
  rw [Br.toLLK_alg]
  rfl

/- English proof (translation)
Use `Matrix.ext fun a b => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `toK D.nd i (((((chiU D.nd i 1)⁻¹ g : (D.nd.O i)ˣ)) : D.nd.O i) * ((r x g : GL _ _) : Matrix _ _ _) a b) = toK D.nd i ((((chiU D.nd i 1)⁻¹ g : (D.nd.O i)ˣ)) : D.nd.O i) * toK D.nd i (((r x g : GL _ _) : Matrix _ _ _) a b)`. Conclude with `map_mul _ _ _`.
-/
theorem twist_eq (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (x : D.nd.X i) (g : GE D.nd) :
    mapM (toK D.nd i) (rTwO D.nd i r x) g =
      toK D.nd i ((((chiU D.nd i 1)⁻¹ g : (D.nd.O i)ˣ)) : D.nd.O i) •
        ((mapRep (algebraMap (D.nd.O i) (FractionRing (D.nd.O i))) (r x) g : GL (Fin D.R.nV) (FractionRing (D.nd.O i))) :
          Matrix (Fin D.R.nV) (Fin D.R.nV) (FractionRing (D.nd.O i))) := by
  refine Matrix.ext fun a b => ?_
  change toK D.nd i (((((chiU D.nd i 1)⁻¹ g : (D.nd.O i)ˣ)) : D.nd.O i) * ((r x g : GL _ _) : Matrix _ _ _) a b) =
    toK D.nd i ((((chiU D.nd i 1)⁻¹ g : (D.nd.O i)ˣ)) : D.nd.O i) * toK D.nd i (((r x g : GL _ _) : Matrix _ _ _) a b)
  exact map_mul _ _ _

end GlobalTheory.Pass.LocDual.Summand

open GlobalTheory.Pass.LocDual.Summand in
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in

/- English proof (translation)
Introduce `D i r hr Xs w hw k M hSub`. Take `⟨x, hx, j, hinj, hj⟩` from `hSub.2`. Set `K` to `FractionRing (D.nd.O i)`. Set `A : GE D.nd → Matrix (Fin D.R.nV) (Fin D.R.nV) K` to `fun g => mapM (toK D.nd i) (rTwO D.nd i r x) g`. Set `Rm : GE D.nd → Matrix (Fin D.R.nV) (Fin D.R.nV) K` to `fun g => ((mapRep (algebraMap (D.nd.O i) K) (r x) g : GL (Fin D.R.nV) K) : Matrix (Fin D.R.nV) (Fin D.R.nV) K)`.

Set `c : GE D.nd → Kˣ` to `fun g => Units.map (toK D.nd i).toMonoidHom ((chiU D.nd i 1)⁻¹ g)`. Establish `hA : ∀ g, A g = ((c g : Kˣ) : K) • Rm g` using `fun g => twist_eq D i r x g`. Establish `hR : ∀ g v, (Rm g).mulVec v = (((c g)⁻¹ : Kˣ) : K) • (A g).mulVec v`. Introduce `g v`. Rewrite using `[hA, Matrix.smul_mulVec, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]`.

Establish `hWinv : IsInv (mapRep (algebraMap (D.nd.O i) K) (r x)) (LinearMap.range j)`. Introduce and unpack `g _ ⟨u, rfl⟩`. Express the relevant statement in the definitionally equal form `(Rm g).mulVec (j u) ∈ LinearMap.range j`. Rewrite using `[hR, ← hj]`. Conclude with `⟨(((c g)⁻¹ : Kˣ) : K) • (mapM (toK D.nd i) M g).mulVec u, by rw [map_smul]⟩`.

Take `⟨W', hW'inv, hcompl⟩` from `(hr x).2.1 (LinearMap.range j) hWinv`. Establish `hW : ∀ g, ∀ v ∈ LinearMap.range j, (A g).mulVec v ∈ LinearMap.range j`. Introduce and unpack `g _ ⟨u, rfl⟩`. Conclude with `⟨_, hj g u⟩`. Establish `hW' : ∀ g, ∀ v ∈ W', (A g).mulVec v ∈ W'`.

Introduce `g v hv`. Rewrite using `[hA, Matrix.smul_mulVec]`. Conclude with `W'.smul_mem _ (hW'inv g v hv)`. Take `⟨Bl, hBj, hcomm⟩` from `exists_left_inv A j hinj W' hcompl hW hW'`. Set `J : Matrix (Fin D.R.nV) (Fin k) K` to `LinearMap.toMatrix' j`.

Set `B : Matrix (Fin k) (Fin D.R.nV) K` to `LinearMap.toMatrix' Bl`. Establish `hJv : ∀ v, J.mulVec v = j v` using `fun v => LinearMap.toMatrix'_mulVec j v`. Establish `hBv : ∀ v, B.mulVec v = Bl v` using `fun v => LinearMap.toMatrix'_mulVec Bl v`. Establish `hBJ : B * J = 1`. Apply `Matrix.toLin'.injective` to reduce the goal to its premises.

Use `LinearMap.ext fun v => ?_` and prove the remaining obligations. Rewrite using `[Matrix.toLin'_mul, LinearMap.comp_apply, Matrix.toLin'_apply, Matrix.toLin'_apply, hJv, hBv, hBj, Matrix.toLin'_one, LinearMap.id_apply]`. Establish `hPA : ∀ g, J * B * A g = A g * (J * B)`. Introduce `g`. Apply `Matrix.toLin'.injective` to reduce the goal to its premises.

Use `LinearMap.ext fun v => ?_` and prove the remaining obligations. Simplify using `only [Matrix.toLin'_mul, LinearMap.comp_apply, Matrix.toLin'_apply, hJv, hBv, hcomm]`. Establish `hJM : ∀ g, J * mapM (toK D.nd i) M g = A g * J`. Introduce `g`. Apply `Matrix.toLin'.injective` to reduce the goal to its premises.

Use `LinearMap.ext fun v => ?_` and prove the remaining obligations. Simplify using `only [Matrix.toLin'_mul, LinearMap.comp_apply, Matrix.toLin'_apply, hJv]`. Conclude with `hj g v`. Set `f` to `Br.toLLK (D.nbr i w hw)`. Set `JL : Matrix (Fin D.R.nV) (Fin k) (Br.LL D.nbr i w hw)` to `J.map f`.

Set `BL : Matrix (Fin k) (Fin D.R.nV) (Br.LL D.nbr i w hw)` to `B.map f`. Set `PL : Matrix (Fin D.R.nV) (Fin D.R.nV) (Br.LL D.nbr i w hw)` to `JL * BL`. Establish `hBJL : BL * JL = 1`. Express the relevant statement in the definitionally equal form `B.map f * J.map f = 1`. Rewrite using `[← Matrix.map_mul, hBJ, Matrix.map_one f (map_zero f) (map_one f)]`.

Establish `hPJ : PL * JL = JL`. Express the relevant statement in the definitionally equal form `JL * BL * JL = JL`. Rewrite using `[Matrix.mul_assoc, hBJL, Matrix.mul_one]`. Establish `hloc : ∀ g, Br.loc D.nbr i w hw (rTwO D.nd i r x) g = (A (decS D.nd w (Br.iota D.nbr i w hw g))).map f` using `fun g => loc_eq D i w hw _ g`. Establish `hPL : ∀ g, PL * Br.loc D.nbr i w hw (rTwO D.nd i r x) g = Br.loc D.nbr i w hw (rTwO D.nd i r x) g * PL`.

Introduce `g`. Rewrite using `[hloc]`. Use `congrArg (fun Z => Z.map f) (hPA (decS D.nd w (Br.iota D.nbr i w hw g)))` as an intermediate fact. Simplify using `only [Matrix.map_mul] at this`. Conclude with `this`.

Use `⟨1, fun _ => ⟨x, hx⟩, (LinearMap.pi fun _ => Matrix.mulVecLin JL : (Fin k → Br.LL D.nbr i w hw) →ₗ[Br.LL D.nbr i w hw] (Fin 1 → Fin D.R.nV → Br.LL D.nbr i w hw)), ?_, ?_, ?_⟩` and prove the remaining obligations. Use `show Function.Injective (fun (v : Fin k → Br.LL D.nbr i w hw) (_ : Fin 1) => JL.mulVec v)`. Introduce `v v' h`. Establish `h1` using `congrArg (fun z => BL.mulVec (z 0)) h`. Express the relevant statement in the definitionally equal form `BL.mulVec (JL.mulVec v) = BL.mulVec (JL.mulVec v') at h1`.

Simplify using `only [Matrix.mulVec_mulVec, hBJL, Matrix.one_mulVec] at h1`. Conclude with `h1`. Use `show ∀ (g : Br.G D.nbr i w hw) (v : Fin k → Br.LL D.nbr i w hw), (fun (_ : Fin 1) => JL.mulVec ((Br.loc D.nbr i w hw M g).mulVec v)) = fun (_ : Fin 1) => (Br.loc D.nbr i w hw (rTwO D.nd i r x) g).mulVec (JL.mulVec v)`. Introduce `g v`. Use function extensionality and compare the values at `b`.

Express the relevant statement in the definitionally equal form `JL.mulVec ((Br.loc D.nbr i w hw M g).mulVec v) = (Br.loc D.nbr i w hw (rTwO D.nd i r x) g).mulVec (JL.mulVec v)`. Simplify using `only [Matrix.mulVec_mulVec]`. Rewrite using `[hloc, loc_eq]`. Express the relevant statement in the definitionally equal form `Matrix.mulVec (J.map f * (mapM (toK D.nd i) M (decS D.nd w (Br.iota D.nbr i w hw g))).map f) v = _`. Rewrite using `[← Matrix.map_mul, hJM, Matrix.map_mul]`.

Use `⟨LinearMap.ker (LinearMap.pi fun b => (Matrix.mulVecLin PL).comp (LinearMap.proj b)), ?_, ?_⟩` and prove the remaining obligations. Introduce `g u hu`. Establish `hu' : ∀ b, PL.mulVec (u b) = 0` using `fun b => congrFun (LinearMap.mem_ker.mp hu) b`. Use `LinearMap.mem_ker.mpr (funext fun b => ?_)` and prove the remaining obligations. Simplify using `only [LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply, Matrix.mulVecLin_apply, Pi.zero_apply]`.

Express the relevant statement in the definitionally equal form `PL.mulVec ((Br.loc D.nbr i w hw (rTwO D.nd i r x) g).mulVec (u b)) = 0`. Rewrite using `[Matrix.mulVec_mulVec, hPL, ← Matrix.mulVec_mulVec, hu', Matrix.mulVec_zero]`. Prove the components needed by the constructor for the conclusion. Rewrite using `[Submodule.disjoint_def]`. Introduce and unpack `u ⟨(v : Fin k → Br.LL D.nbr i w hw), rfl⟩ hu`.

Establish `hu' : ∀ b, PL.mulVec (JL.mulVec v) = 0` using `fun b => congrFun (LinearMap.mem_ker.mp hu) b`. Use function extensionality and compare the values at `b`. Express the relevant statement in the definitionally equal form `JL.mulVec v = 0`. Rewrite using `[← hPJ, ← Matrix.mulVec_mulVec]`. Conclude with `hu' b`.

Rewrite using `[codisjoint_iff, eq_top_iff]`. Introduce `u _`. Use `Submodule.mem_sup.mpr ⟨fun _ => PL.mulVec (u 0), ⟨BL.mulVec (u 0), ?_⟩, fun b => u b - PL.mulVec (u 0), ?_, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `b`. Express the relevant statement in the definitionally equal form `JL.mulVec (BL.mulVec (u 0)) = (JL * BL).mulVec (u 0)`.

Conclude with `Matrix.mulVec_mulVec _ _ _`. Use `LinearMap.mem_ker.mpr (funext fun b => ?_)` and prove the remaining obligations. Simplify using `only [LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply, Matrix.mulVecLin_apply, Pi.zero_apply]`. Rewrite using `[Matrix.mulVec_sub, Matrix.mulVec_mulVec, Subsingleton.elim b 0]`. Express the relevant statement in the definitionally equal form `(JL * BL).mulVec (u 0) - (JL * BL * (JL * BL)).mulVec (u 0) = 0`.

Rewrite using `[Matrix.mul_assoc JL BL, ← Matrix.mul_assoc BL, hBJL, Matrix.one_mul, sub_self]`. Use function extensionality and compare the values at `b`. Express the relevant statement in the definitionally equal form `PL.mulVec (u 0) + (u b - PL.mulVec (u 0)) = u b`. Conclude with `add_sub_cancel _ _`.
-/
theorem GlobalTheory.Pass.LocDual.isSummandTw_locU : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))), GoodR D.nd i r →
    ∀ (Xs : Set (D.nd.X i)) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (k : ℕ) (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (hSub : SubTw i r Xs M),
      IsSummandTw i w hw r Xs (locU i w hw M hSub.1) := by
  intro D i r hr Xs w hw k M hSub
  obtain ⟨x, hx, j, hinj, hj⟩ := hSub.2
  let K := FractionRing (D.nd.O i)
  let A : GE D.nd → Matrix (Fin D.R.nV) (Fin D.R.nV) K := fun g => mapM (toK D.nd i) (rTwO D.nd i r x) g
  let Rm : GE D.nd → Matrix (Fin D.R.nV) (Fin D.R.nV) K := fun g =>
    ((mapRep (algebraMap (D.nd.O i) K) (r x) g : GL (Fin D.R.nV) K) : Matrix (Fin D.R.nV) (Fin D.R.nV) K)
  let c : GE D.nd → Kˣ := fun g => Units.map (toK D.nd i).toMonoidHom ((chiU D.nd i 1)⁻¹ g)
  have hA : ∀ g, A g = ((c g : Kˣ) : K) • Rm g := fun g => twist_eq D i r x g
  have hR : ∀ g v, (Rm g).mulVec v = (((c g)⁻¹ : Kˣ) : K) • (A g).mulVec v := by
    intro g v
    rw [hA, Matrix.smul_mulVec, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]
  have hWinv : IsInv (mapRep (algebraMap (D.nd.O i) K) (r x)) (LinearMap.range j) := by
    rintro g _ ⟨u, rfl⟩
    change (Rm g).mulVec (j u) ∈ LinearMap.range j
    rw [hR, ← hj]
    exact ⟨(((c g)⁻¹ : Kˣ) : K) • (mapM (toK D.nd i) M g).mulVec u, by rw [map_smul]⟩
  obtain ⟨W', hW'inv, hcompl⟩ := (hr x).2.1 (LinearMap.range j) hWinv
  have hW : ∀ g, ∀ v ∈ LinearMap.range j, (A g).mulVec v ∈ LinearMap.range j := by
    rintro g _ ⟨u, rfl⟩
    exact ⟨_, hj g u⟩
  have hW' : ∀ g, ∀ v ∈ W', (A g).mulVec v ∈ W' := by
    intro g v hv
    rw [hA, Matrix.smul_mulVec]
    exact W'.smul_mem _ (hW'inv g v hv)
  obtain ⟨Bl, hBj, hcomm⟩ := exists_left_inv A j hinj W' hcompl hW hW'

  let J : Matrix (Fin D.R.nV) (Fin k) K := LinearMap.toMatrix' j
  let B : Matrix (Fin k) (Fin D.R.nV) K := LinearMap.toMatrix' Bl
  have hJv : ∀ v, J.mulVec v = j v := fun v => LinearMap.toMatrix'_mulVec j v
  have hBv : ∀ v, B.mulVec v = Bl v := fun v => LinearMap.toMatrix'_mulVec Bl v
  have hBJ : B * J = 1 := by
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun v => ?_
    rw [Matrix.toLin'_mul, LinearMap.comp_apply, Matrix.toLin'_apply, Matrix.toLin'_apply, hJv, hBv, hBj,
      Matrix.toLin'_one, LinearMap.id_apply]
  have hPA : ∀ g, J * B * A g = A g * (J * B) := by
    intro g
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun v => ?_
    simp only [Matrix.toLin'_mul, LinearMap.comp_apply, Matrix.toLin'_apply, hJv, hBv, hcomm]
  have hJM : ∀ g, J * mapM (toK D.nd i) M g = A g * J := by
    intro g
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun v => ?_
    simp only [Matrix.toLin'_mul, LinearMap.comp_apply, Matrix.toLin'_apply, hJv]
    exact hj g v
  let f := Br.toLLK (D.nbr i w hw)
  let JL : Matrix (Fin D.R.nV) (Fin k) (Br.LL D.nbr i w hw) := J.map f
  let BL : Matrix (Fin k) (Fin D.R.nV) (Br.LL D.nbr i w hw) := B.map f
  let PL : Matrix (Fin D.R.nV) (Fin D.R.nV) (Br.LL D.nbr i w hw) := JL * BL
  have hBJL : BL * JL = 1 := by
    change B.map f * J.map f = 1
    rw [← Matrix.map_mul, hBJ, Matrix.map_one f (map_zero f) (map_one f)]
  have hPJ : PL * JL = JL := by
    change JL * BL * JL = JL
    rw [Matrix.mul_assoc, hBJL, Matrix.mul_one]
  have hloc : ∀ g, Br.loc D.nbr i w hw (rTwO D.nd i r x) g = (A (decS D.nd w (Br.iota D.nbr i w hw g))).map f :=
    fun g => loc_eq D i w hw _ g
  have hPL : ∀ g, PL * Br.loc D.nbr i w hw (rTwO D.nd i r x) g = Br.loc D.nbr i w hw (rTwO D.nd i r x) g * PL := by
    intro g
    rw [hloc]
    have := congrArg (fun Z => Z.map f) (hPA (decS D.nd w (Br.iota D.nbr i w hw g)))
    simp only [Matrix.map_mul] at this
    exact this
  refine ⟨1, fun _ => ⟨x, hx⟩, (LinearMap.pi fun _ => Matrix.mulVecLin JL : (Fin k → Br.LL D.nbr i w hw) →ₗ[Br.LL D.nbr i w hw] (Fin 1 → Fin D.R.nV → Br.LL D.nbr i w hw)), ?_, ?_, ?_⟩
  · show Function.Injective (fun (v : Fin k → Br.LL D.nbr i w hw) (_ : Fin 1) => JL.mulVec v)
    intro v v' h
    have h1 := congrArg (fun z => BL.mulVec (z 0)) h
    change BL.mulVec (JL.mulVec v) = BL.mulVec (JL.mulVec v') at h1
    simp only [Matrix.mulVec_mulVec, hBJL, Matrix.one_mulVec] at h1
    exact h1
  · show ∀ (g : Br.G D.nbr i w hw) (v : Fin k → Br.LL D.nbr i w hw), (fun (_ : Fin 1) => JL.mulVec ((Br.loc D.nbr i w hw M g).mulVec v)) =
      fun (_ : Fin 1) => (Br.loc D.nbr i w hw (rTwO D.nd i r x) g).mulVec (JL.mulVec v)
    intro g v
    funext b
    change JL.mulVec ((Br.loc D.nbr i w hw M g).mulVec v) = (Br.loc D.nbr i w hw (rTwO D.nd i r x) g).mulVec (JL.mulVec v)
    simp only [Matrix.mulVec_mulVec]
    rw [hloc, loc_eq]
    change Matrix.mulVec (J.map f * (mapM (toK D.nd i) M (decS D.nd w (Br.iota D.nbr i w hw g))).map f) v = _
    rw [← Matrix.map_mul, hJM, Matrix.map_mul]
  · refine ⟨LinearMap.ker (LinearMap.pi fun b => (Matrix.mulVecLin PL).comp (LinearMap.proj b)), ?_, ?_⟩
    · intro g u hu
      have hu' : ∀ b, PL.mulVec (u b) = 0 := fun b => congrFun (LinearMap.mem_ker.mp hu) b
      refine LinearMap.mem_ker.mpr (funext fun b => ?_)
      simp only [LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply, Matrix.mulVecLin_apply, Pi.zero_apply]
      change PL.mulVec ((Br.loc D.nbr i w hw (rTwO D.nd i r x) g).mulVec (u b)) = 0
      rw [Matrix.mulVec_mulVec, hPL, ← Matrix.mulVec_mulVec, hu', Matrix.mulVec_zero]
    · constructor
      · rw [Submodule.disjoint_def]
        rintro u ⟨(v : Fin k → Br.LL D.nbr i w hw), rfl⟩ hu
        have hu' : ∀ b, PL.mulVec (JL.mulVec v) = 0 := fun b => congrFun (LinearMap.mem_ker.mp hu) b
        funext b
        change JL.mulVec v = 0
        rw [← hPJ, ← Matrix.mulVec_mulVec]
        exact hu' b
      · rw [codisjoint_iff, eq_top_iff]
        intro u _
        refine Submodule.mem_sup.mpr ⟨fun _ => PL.mulVec (u 0), ⟨BL.mulVec (u 0), ?_⟩, fun b => u b - PL.mulVec (u 0), ?_, ?_⟩
        · funext b
          change JL.mulVec (BL.mulVec (u 0)) = (JL * BL).mulVec (u 0)
          exact Matrix.mulVec_mulVec _ _ _
        · refine LinearMap.mem_ker.mpr (funext fun b => ?_)
          simp only [LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply, Matrix.mulVecLin_apply, Pi.zero_apply]
          rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, Subsingleton.elim b 0]
          change (JL * BL).mulVec (u 0) - (JL * BL * (JL * BL)).mulVec (u 0) = 0
          rw [Matrix.mul_assoc JL BL, ← Matrix.mul_assoc BL, hBJL, Matrix.one_mul, sub_self]
        · funext b
          change PL.mulVec (u 0) + (u b - PL.mulVec (u 0)) = u b
          exact add_sub_cancel _ _
