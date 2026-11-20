import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EvalAtOneExtremalMul
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SqRepTopVecOfUnitriangular
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FockSubstitutionIdentitiesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeylDeterminantTwistTensorFiniteDimensionalStablStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EquivariantHomMultiplicityFreeIrreducibleStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeylDeterminantTwistTensorUnitIndexIrreducibleUnStatement

noncomputable section

open MvPolynomial Formalism.BasicNotions Formalism.L2.Forms Formalism.L2.Ker GlobalTheory.KJInf GlobalTheory.GLDuality
open scoped Matrix Kronecker

namespace GlobalTheory.HoweOne

def ren (a b : ℕ) : FP Unit a b →ₐ[ℂ] MvPolynomial (Fin b × Fin a) ℂ :=
  rename Prod.snd

/- English proof (translation)
Simplify using `[ren]`.
-/
theorem ren_X {a b : ℕ} (v : Unit × Fin b × Fin a) : ren a b (X v) = X v.2 := by
  simp [ren]

/- English proof (translation)
The claim follows from `rename_injective _ fun u v h => Prod.ext (Subsingleton.elim _ _) h`.
-/
theorem ren_injective (a b : ℕ) : Function.Injective (ren a b) :=
  rename_injective _ fun u v h => Prod.ext (Subsingleton.elim _ _) h

/- English proof (translation)
Rewrite using `[matRep_apply]`. Establish `e : (Formalism.GradedWeylDivisibility.sub ((h : Matrix (Fin b) (Fin b) ℂ) ⊗ₖ (g : Matrix (Fin a) (Fin a) ℂ))ᵀ).comp (ren a b) = (ren a b).comp (mvZ (fun _ => (g : Matrix (Fin a) (Fin a) ℂ)ᵀ) (fun _ => (h : Matrix (Fin b) (Fin b) ℂ)))`. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce and unpack `⟨u, i, j⟩`. Rewrite using `[AlgHom.comp_apply, AlgHom.comp_apply, ren_X, ← matRep_apply, matRep_X]`.

Simplify using `[mvZ, map_sum, ren_X, Matrix.transpose_apply]`. Conclude with `congrArg (fun φ => φ P) e`.
-/
theorem matRep_ren {a b : ℕ} (g : GL (Fin a) ℂ) (h : GL (Fin b) ℂ) (P : FP Unit a b) :
    matRep a b (g, h) (ren a b P) =
      ren a b (mvZ (fun _ => (g : Matrix (Fin a) (Fin a) ℂ)ᵀ) (fun _ => (h : Matrix (Fin b) (Fin b) ℂ)) P) := by
  rw [matRep_apply]
  have e : (Formalism.GradedWeylDivisibility.sub ((h : Matrix (Fin b) (Fin b) ℂ) ⊗ₖ (g : Matrix (Fin a) (Fin a) ℂ))ᵀ).comp (ren a b) =
      (ren a b).comp
        (mvZ (fun _ => (g : Matrix (Fin a) (Fin a) ℂ)ᵀ) (fun _ => (h : Matrix (Fin b) (Fin b) ℂ))) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨u, i, j⟩
    rw [AlgHom.comp_apply, AlgHom.comp_apply, ren_X, ← matRep_apply, matRep_X]
    simp [mvZ, map_sum, ren_X, Matrix.transpose_apply]
  exact congrArg (fun φ => φ P) e

/- English proof (translation)
Establish `e : subY (ι` using `Unit) hab (fun _ => (1 : Matrix (Fin b) (Fin b) ℂ)) = rename fun v : Unit × Fin a × Fin a => (v.1, Fin.castLE hab v.2.2, v.2.1) := by`. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce and unpack `⟨u, i, j⟩`. Simplify using `[subY, Matrix.one_apply, apply_ite C]`. Rewrite using `[e]`.

Apply `rename_injective` to reduce the goal to its premises. Introduce and unpack `⟨u, i, j⟩ ⟨u', i', j'⟩ h`. Simplify using `only [Prod.mk.injEq] at h`. Take `⟨-, h2, rfl⟩` from `h`. Rewrite using `[Fin.castLE_injective hab h2]`.
-/
theorem subY_one_injective {a b : ℕ} (hab : a ≤ b) :
    Function.Injective (subY (ι := Unit) hab (fun _ => (1 : Matrix (Fin b) (Fin b) ℂ))) := by
  have e : subY (ι := Unit) hab (fun _ => (1 : Matrix (Fin b) (Fin b) ℂ)) =
      rename fun v : Unit × Fin a × Fin a => (v.1, Fin.castLE hab v.2.2, v.2.1) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨u, i, j⟩
    simp [subY, Matrix.one_apply, apply_ite C]
  rw [e]
  apply rename_injective
  rintro ⟨u, i, j⟩ ⟨u', i', j'⟩ h
  simp only [Prod.mk.injEq] at h
  obtain ⟨-, h2, rfl⟩ := h
  rw [Fin.castLE_injective hab h2]

end GlobalTheory.HoweOne

namespace GlobalTheory.HoweOne

open GlobalTheory.Branching

/- English proof (translation)
The claim follows from `(GlobalTheory.T.weylDeterminantTwistTensor_finiteDimensional_stable Unit a lam n).2 g`.
-/
theorem vn_stable {a : ℕ} (lam : Unit → DomWeight a) (n : Unit → ℕ) (g : Unit → Matrix (Fin a) (Fin a) ℂ) :
    ∀ F ∈ Vn lam n, lft g F ∈ Vn lam n := (GlobalTheory.T.weylDeterminantTwistTensor_finiteDimensional_stable Unit a lam n).2 g

def vnMap {a : ℕ} (lam : Unit → DomWeight a) (n : Unit → ℕ) (g : Unit → Matrix (Fin a) (Fin a) ℂ) :
    Vn lam n →ₗ[ℂ] Vn lam n :=
  LinearMap.restrict (p := Vn lam n) (q := Vn lam n) (lft g).toLinearMap (vn_stable lam n g)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem vnMap_apply {a : ℕ} (lam : Unit → DomWeight a) (n : Unit → ℕ) (g : Unit → Matrix (Fin a) (Fin a) ℂ)
    (F : Vn lam n) : (vnMap lam n g F : PY Unit a) = lft g F := rfl

/- English proof (translation)
The claim follows from `Matrix.transpose_mem_unitaryGroup_iff.2 k.2`.
-/
theorem transpose_uni {a : ℕ} (k : Matrix.unitaryGroup (Fin a) ℂ) :
    (k : Matrix (Fin a) (Fin a) ℂ)ᵀ ∈ Matrix.unitaryGroup (Fin a) ℂ :=
  Matrix.transpose_mem_unitaryGroup_iff.2 k.2

def vnRep {a : ℕ} (lam : Unit → DomWeight a) (n : Unit → ℕ) :
    Representation ℂ (Matrix.unitaryGroup (Fin a) ℂ) (Vn lam n) where
  toFun k := vnMap lam n (fun _ => (k : Matrix (Fin a) (Fin a) ℂ)ᵀ)
  map_one' := by
    refine LinearMap.ext fun F => Subtype.ext ?_
    rw [vnMap_apply, Module.End.one_apply]
    have : (fun _ : Unit => ((1 : Matrix.unitaryGroup (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ)ᵀ) = fun _ => 1 := by
      exact funext fun _ => Matrix.transpose_one
    rw [this, (GlobalTheory.T.fockSubstitution_identities Unit a a le_rfl).2.2.2.2.1]
  map_mul' k k' := by
    refine LinearMap.ext fun F => Subtype.ext ?_
    rw [Module.End.mul_apply, vnMap_apply, vnMap_apply, vnMap_apply, (GlobalTheory.T.fockSubstitution_identities Unit a a le_rfl).2.2.2.1]
    congr 2
    refine funext fun _ => ?_
    first | exact (Matrix.transpose_mul _ _).symm | exact Matrix.transpose_mul _ _

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem vnRep_apply {a : ℕ} (lam : Unit → DomWeight a) (n : Unit → ℕ) (k : Matrix.unitaryGroup (Fin a) ℂ)
    (F : Vn lam n) : (vnRep lam n k F : PY Unit a) = lft (fun _ => (k : Matrix (Fin a) (Fin a) ℂ)ᵀ) F := rfl

/- English proof (translation)
Take `⟨hne, hirr⟩` from `GlobalTheory.T.weylDeterminantTwistTensor_unitIndex_irreducible_unitary a ha lam n`. Take `⟨F₀, hF₀, hF₀0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hne`. Use `{ exists_pair_ne := ⟨⊥, ⊤, fun e => ?_⟩, eq_bot_or_eq_top := fun S => ?_ }` and prove the remaining obligations. Establish `e'` using `congrArg Subrepresentation.toSubmodule e`. Establish `: (⟨F₀, hF₀⟩ : Vn lam n) ∈ (⊤ : Subrepresentation (vnRep lam n)).toSubmodule` using `Submodule.mem_top`.

Rewrite `this` using `[← e']`. Conclude with `hF₀0 (congrArg Subtype.val ((Submodule.mem_bot ℂ).1 this))`. Set `U : Submodule ℂ (PY Unit a)` to `S.toSubmodule.map (Vn lam n).subtype`. Establish `hU : U ≤ Vn lam n`. Introduce and unpack `_ ⟨x, -, rfl⟩`.

Conclude with `x.2`. Establish `hst : ∀ k, IsUni k → ∀ F ∈ U, lft k F ∈ U`. Introduce and unpack `k hk _ ⟨x, hx, rfl⟩`. Set `u : Matrix.unitaryGroup (Fin a) ℂ` to `⟨(k ())ᵀ, Matrix.transpose_mem_unitaryGroup_iff.2 (hk ())⟩`. Use `⟨vnRep lam n u x, S.apply_mem_toSubmodule u hx, ?_⟩` and prove the remaining obligations.

Establish `hk' : (fun _ : Unit => (u : Matrix (Fin a) (Fin a) ℂ)ᵀ) = k`. Use function extensionality and compare the values at `t`. Simplify using `[u]`. Simplify using `only [Submodule.subtype_apply, vnRep_apply, hk']`. Break down `hirr U hU hst with h | h` into its components or cases.

Use `left`. Use `Subrepresentation.ext ((Submodule.eq_bot_iff _).2 fun x hx => ?_)` and prove the remaining obligations. Establish `: (x : PY Unit a) ∈ U` using `⟨x, hx, rfl⟩`. Rewrite `this` using `[h]`. Conclude with `Subtype.ext ((Submodule.mem_bot ℂ).1 this)`.

Use `right`. Use `Subrepresentation.ext (Submodule.eq_top_iff'.2 fun x => ?_)` and prove the remaining obligations. Establish `: (x : PY Unit a) ∈ U` using `by rw [h]; exact x.2`. Take `⟨y, hy, hyx⟩` from `this`. Rewrite `hy` using `[Subtype.ext hyx]`. Then use the resulting hypothesis.
-/
theorem vnRep_irreducible {a : ℕ} (ha : 0 < a) (lam : Unit → DomWeight a) (n : Unit → ℕ) :
    (vnRep lam n).IsIrreducible := by
  obtain ⟨hne, hirr⟩ := GlobalTheory.T.weylDeterminantTwistTensor_unitIndex_irreducible_unitary a ha lam n
  obtain ⟨F₀, hF₀, hF₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  refine { exists_pair_ne := ⟨⊥, ⊤, fun e => ?_⟩, eq_bot_or_eq_top := fun S => ?_ }
  · have e' := congrArg Subrepresentation.toSubmodule e
    have : (⟨F₀, hF₀⟩ : Vn lam n) ∈ (⊤ : Subrepresentation (vnRep lam n)).toSubmodule := Submodule.mem_top
    rw [← e'] at this
    exact hF₀0 (congrArg Subtype.val ((Submodule.mem_bot ℂ).1 this))
  · let U : Submodule ℂ (PY Unit a) := S.toSubmodule.map (Vn lam n).subtype
    have hU : U ≤ Vn lam n := by
      rintro _ ⟨x, -, rfl⟩
      exact x.2
    have hst : ∀ k, IsUni k → ∀ F ∈ U, lft k F ∈ U := by
      rintro k hk _ ⟨x, hx, rfl⟩
      let u : Matrix.unitaryGroup (Fin a) ℂ := ⟨(k ())ᵀ, Matrix.transpose_mem_unitaryGroup_iff.2 (hk ())⟩
      refine ⟨vnRep lam n u x, S.apply_mem_toSubmodule u hx, ?_⟩
      have hk' : (fun _ : Unit => (u : Matrix (Fin a) (Fin a) ℂ)ᵀ) = k := by
        funext t; simp [u]
      simp only [Submodule.subtype_apply, vnRep_apply, hk']
    rcases hirr U hU hst with h | h
    · left
      refine Subrepresentation.ext ((Submodule.eq_bot_iff _).2 fun x hx => ?_)
      have : (x : PY Unit a) ∈ U := ⟨x, hx, rfl⟩
      rw [h] at this
      exact Subtype.ext ((Submodule.mem_bot ℂ).1 this)
    · right
      refine Subrepresentation.ext (Submodule.eq_top_iff'.2 fun x => ?_)
      have : (x : PY Unit a) ∈ U := by rw [h]; exact x.2
      obtain ⟨y, hy, hyx⟩ := this
      rwa [Subtype.ext hyx] at hy

/- English proof (translation)
Take `⟨⟨e⟩, -, -⟩` from `(GlobalTheory.Published.glHoweDuality_holds a b ha hb).1`. Conclude with `⟨Representation.Equiv.mk e.toLinearEquiv fun u => e.isIntertwining' (unitaryIncl a u.1, u.2)⟩`.
-/
theorem equiv_unitary_gl {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    Nonempty ((Representation.directSum fun j : Part (min a b) =>
      Representation.tprod ((smallRep (unitaryIncl a) (pad a j)).comp
          (MonoidHom.fst (Matrix.unitaryGroup (Fin a) ℂ) (GL (Fin b) ℂ)))
        ((smallRep (MonoidHom.id (GL (Fin b) ℂ)) (pad b j)).comp
          (MonoidHom.snd (Matrix.unitaryGroup (Fin a) ℂ) (GL (Fin b) ℂ)))).Equiv
      (polyRep (unitaryIncl a) (MonoidHom.id (GL (Fin b) ℂ)))) := by
  obtain ⟨⟨e⟩, -, -⟩ := (GlobalTheory.Published.glHoweDuality_holds a b ha hb).1
  exact ⟨Representation.Equiv.mk e.toLinearEquiv fun u => e.isIntertwining' (unitaryIncl a u.1, u.2)⟩

end GlobalTheory.HoweOne

namespace GlobalTheory.HoweOne

open GlobalTheory.Branching

def subMap {a b : ℕ} (hab : a ≤ b) (lam : Unit → DomWeight a) (n : Unit → ℕ)
    (y' : Unit → Matrix (Fin b) (Fin b) ℂ) : Vn lam n →ₗ[ℂ] MvPolynomial (Fin b × Fin a) ℂ :=
  (ren a b).toLinearMap ∘ₗ (subY hab y').toLinearMap ∘ₗ (Vn lam n).subtype

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem subMap_apply {a b : ℕ} (hab : a ≤ b) (lam : Unit → DomWeight a) (n : Unit → ℕ)
    (y' : Unit → Matrix (Fin b) (Fin b) ℂ) (F : Vn lam n) :
    subMap hab lam n y' F = ren a b (subY hab y' F) := rfl

def subSet {a b : ℕ} (hab : a ≤ b) (lam : Unit → DomWeight a) (n : Unit → ℕ) :
    Set (Vn lam n →ₗ[ℂ] MvPolynomial (Fin b × Fin a) ℂ) :=
  {T | ∃ y', IsInv y' ∧ T = subMap hab lam n y'}

/- English proof (translation)
The claim follows from `matRep_ren (unitaryIncl a k) h P`.
-/
theorem polyRep_apply {a b : ℕ} (k : Matrix.unitaryGroup (Fin a) ℂ) (h : GL (Fin b) ℂ) (P : FP Unit a b) :
    polyRep (unitaryIncl a) (MonoidHom.id (GL (Fin b) ℂ)) (k, h) (ren a b P) =
      ren a b (mvZ (fun _ => (k : Matrix (Fin a) (Fin a) ℂ)ᵀ) (fun _ => (h : Matrix (Fin b) (Fin b) ℂ)) P) :=
  matRep_ren (unitaryIncl a k) h P

/- English proof (translation)
Rewrite using `[subMap_apply, subMap_apply, polyRep_apply, (GlobalTheory.T.fockSubstitution_identities Unit a b hab).1, vnRep_apply]`. Simplify using `only [Units.val_one, one_mul]`.
-/
theorem subMap_intertwines {a b : ℕ} (hab : a ≤ b) (lam : Unit → DomWeight a) (n : Unit → ℕ)
    (y' : Unit → Matrix (Fin b) (Fin b) ℂ) (k : Matrix.unitaryGroup (Fin a) ℂ) (F : Vn lam n) :
    subMap hab lam n y' (vnRep lam n k F) =
      polyRep (unitaryIncl a) (MonoidHom.id (GL (Fin b) ℂ)) (k, 1) (subMap hab lam n y' F) := by
  rw [subMap_apply, subMap_apply, polyRep_apply, (GlobalTheory.T.fockSubstitution_identities Unit a b hab).1, vnRep_apply]
  simp only [Units.val_one, one_mul]

/- English proof (translation)
Use `LinearMap.ext fun F => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.comp_apply, subMap_apply, subMap_apply, polyRep_apply, (GlobalTheory.T.fockSubstitution_identities Unit a b hab).1]`. Establish `: (fun _ : Unit => ((1 : Matrix.unitaryGroup (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ)ᵀ) = fun _ => 1`. Use function extensionality and compare the values at `fun _ => Matrix.transpose_one`. Rewrite using `[this, (GlobalTheory.T.fockSubstitution_identities Unit a a le_rfl).2.2.2.2.1]`.
-/
theorem comp_subMap {a b : ℕ} (hab : a ≤ b) (lam : Unit → DomWeight a) (n : Unit → ℕ)
    (y' : Unit → Matrix (Fin b) (Fin b) ℂ) (h : GL (Fin b) ℂ) :
    polyRep (unitaryIncl a) (MonoidHom.id (GL (Fin b) ℂ)) (1, h) ∘ₗ subMap hab lam n y' =
      subMap hab lam n (fun τ => (h : Matrix (Fin b) (Fin b) ℂ) * y' τ) := by
  refine LinearMap.ext fun F => ?_
  rw [LinearMap.comp_apply, subMap_apply, subMap_apply, polyRep_apply, (GlobalTheory.T.fockSubstitution_identities Unit a b hab).1]
  have : (fun _ : Unit => ((1 : Matrix.unitaryGroup (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ)ᵀ) = fun _ => 1 :=
    funext fun _ => Matrix.transpose_one
  rw [this, (GlobalTheory.T.fockSubstitution_identities Unit a a le_rfl).2.2.2.2.1]

/- English proof (translation)
Introduce `a b hab ha lam n Q hQ`. Use `haveI : FiniteDimensional ℂ (Vn lam n) := (GlobalTheory.T.weylDeterminantTwistTensor_finiteDimensional_stable Unit a lam n).1`. Establish `hb : 1 ≤ b` using `le_trans ha hab`. Set `S` to `Submodule.span ℂ (subSet hab lam n)`. Establish `h1 : ∀ T ∈ S, ∀ k F, T (vnRep lam n k F) = polyRep (unitaryIncl a) (MonoidHom.id (GL (Fin b) ℂ)) (k, 1) (T F)`.

Introduce `T hT`. Proceed by induction on `hT using Submodule.span_induction with`. Consider the case `mem T hT`. Take `⟨y', -, rfl⟩` from `hT`. Conclude with `subMap_intertwines hab lam n y'`.

Consider the case `zero => intro k F`. Simplify using the standard rewrite rules. Consider the case `add T T' _ _ hT hT' => intro k F`. Simplify using `[hT k F, hT' k F]`. Consider the case `smul c T _ hT => intro k F`.

Simplify using `[hT k F]`. Establish `h2 : ∀ T ∈ S, ∀ h, polyRep (unitaryIncl a) (MonoidHom.id (GL (Fin b) ℂ)) (1, h) ∘ₗ T ∈ S`. Introduce `T hT h`. Proceed by induction on `hT using Submodule.span_induction with`. Consider the case `mem T hT`.

Take `⟨y', hy', rfl⟩` from `hT`. Rewrite using `[comp_subMap]`. Use `Submodule.subset_span ⟨_, fun τ => ?_, rfl⟩` and prove the remaining obligations. Rewrite using `[Matrix.det_mul]`. Conclude with `(Matrix.isUnits_det_units h).mul (hy' τ)`.

Consider the case `zero => simp`. Consider the case `add T T' _ _ hT hT' => rw [LinearMap.comp_add]`. Conclude with `S.add_mem hT hT'`. Consider the case `smul c T _ hT => rw [LinearMap.comp_smul]`. Conclude with `S.smul_mem c hT`.

Establish `h3 : S ≠ ⊥`. Take `⟨F₀, hF₀, hF₀0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot (GlobalTheory.T.weylDeterminantTwistTensor_unitIndex_irreducible_unitary a ha lam n).1`. Establish `hmem : subMap hab lam n (fun _ => 1) ∈ S` using `Submodule.subset_span ⟨_, fun _ => by simp, rfl⟩`. Introduce `hS`. Rewrite `hmem` using `[hS, Submodule.mem_bot]`.

Use `LinearMap.congr_fun hmem ⟨F₀, hF₀⟩` as an intermediate fact. Rewrite `this` using `[subMap_apply, LinearMap.zero_apply]`. Conclude with `hF₀0 (subY_one_injective hab ((map_eq_zero_iff _ (ren_injective a b)).1 this |>.trans (map_zero _).symm))`. Set `Q' : Vn lam n →ₗ[ℂ] MvPolynomial (Fin b × Fin a) ℂ` to `(ren a b).toLinearMap ∘ₗ Q ∘ₗ (Vn lam n).subtype`. Establish `hQ' : ∀ k F, Q' (vnRep lam n k F) = polyRep (unitaryIncl a) (MonoidHom.id (GL (Fin b) ℂ)) (k, 1) (Q' F)`.

Introduce `k F`. Simplify using `only [Q', LinearMap.comp_apply, Submodule.subtype_apply, AlgHom.toLinearMap_apply]`. Rewrite using `[vnRep_apply, polyRep_apply, hQ _ (fun _ => transpose_uni k) F F.2]`. Both sides reduce to the same expression. Establish `key` using `GlobalTheory.T.equivariantHom_multiplicityFree_irreducible (Matrix.unitaryGroup (Fin a) ℂ) (GL (Fin b) ℂ) (Part (min a b)) (fun j => nablaSq ℂ a (pad a j)) (fun j => nablaSq ℂ b (pad b j)) (fun j => smallRep (unitaryIncl a) (pad a j)) (fun j => smallRep (MonoidHom.id (GL (Fin b) …`.

Take `⟨m, c, T, hT⟩` from `Submodule.mem_span_set'.1 key`. Use `choose y' hy' hyT using fun i => (T i).2`. Use `⟨m, y', c, hy', fun F hF => ren_injective a b ?_⟩` and prove the remaining obligations. Use `LinearMap.congr_fun hT ⟨F, hF⟩` as an intermediate fact. Rewrite `this` using `[LinearMap.sum_apply]`.

Simplify using `only [LinearMap.smul_apply, hyT, subMap_apply] at this`. Simplify using `only [map_sum, map_smul]`. Conclude with `this.symm`.
-/
theorem howeSpan_unit : HoweSpan Unit := by
  intro a b hab ha lam n Q hQ
  haveI : FiniteDimensional ℂ (Vn lam n) := (GlobalTheory.T.weylDeterminantTwistTensor_finiteDimensional_stable Unit a lam n).1
  have hb : 1 ≤ b := le_trans ha hab
  let S := Submodule.span ℂ (subSet hab lam n)
  have h1 : ∀ T ∈ S, ∀ k F, T (vnRep lam n k F) =
      polyRep (unitaryIncl a) (MonoidHom.id (GL (Fin b) ℂ)) (k, 1) (T F) := by
    intro T hT
    induction hT using Submodule.span_induction with
    | mem T hT =>
      obtain ⟨y', -, rfl⟩ := hT
      exact subMap_intertwines hab lam n y'
    | zero => intro k F; simp
    | add T T' _ _ hT hT' => intro k F; simp [hT k F, hT' k F]
    | smul c T _ hT => intro k F; simp [hT k F]
  have h2 : ∀ T ∈ S, ∀ h, polyRep (unitaryIncl a) (MonoidHom.id (GL (Fin b) ℂ)) (1, h) ∘ₗ T ∈ S := by
    intro T hT h
    induction hT using Submodule.span_induction with
    | mem T hT =>
      obtain ⟨y', hy', rfl⟩ := hT
      rw [comp_subMap]
      refine Submodule.subset_span ⟨_, fun τ => ?_, rfl⟩
      rw [Matrix.det_mul]
      exact (Matrix.isUnits_det_units h).mul (hy' τ)
    | zero => simp
    | add T T' _ _ hT hT' => rw [LinearMap.comp_add]; exact S.add_mem hT hT'
    | smul c T _ hT => rw [LinearMap.comp_smul]; exact S.smul_mem c hT
  have h3 : S ≠ ⊥ := by
    obtain ⟨F₀, hF₀, hF₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (GlobalTheory.T.weylDeterminantTwistTensor_unitIndex_irreducible_unitary a ha lam n).1
    have hmem : subMap hab lam n (fun _ => 1) ∈ S :=
      Submodule.subset_span ⟨_, fun _ => by simp, rfl⟩
    intro hS
    rw [hS, Submodule.mem_bot] at hmem
    have := LinearMap.congr_fun hmem ⟨F₀, hF₀⟩
    rw [subMap_apply, LinearMap.zero_apply] at this
    exact hF₀0 (subY_one_injective hab ((map_eq_zero_iff _ (ren_injective a b)).1 this |>.trans
      (map_zero _).symm))
  let Q' : Vn lam n →ₗ[ℂ] MvPolynomial (Fin b × Fin a) ℂ := (ren a b).toLinearMap ∘ₗ Q ∘ₗ (Vn lam n).subtype
  have hQ' : ∀ k F, Q' (vnRep lam n k F) = polyRep (unitaryIncl a) (MonoidHom.id (GL (Fin b) ℂ)) (k, 1) (Q' F) := by
    intro k F
    simp only [Q', LinearMap.comp_apply, Submodule.subtype_apply, AlgHom.toLinearMap_apply]
    rw [vnRep_apply, polyRep_apply, hQ _ (fun _ => transpose_uni k) F F.2]
    rfl
  have key := GlobalTheory.T.equivariantHom_multiplicityFree_irreducible (Matrix.unitaryGroup (Fin a) ℂ) (GL (Fin b) ℂ) (Part (min a b))
    (fun j => nablaSq ℂ a (pad a j)) (fun j => nablaSq ℂ b (pad b j))
    (fun j => smallRep (unitaryIncl a) (pad a j)) (fun j => smallRep (MonoidHom.id (GL (Fin b) ℂ)) (pad b j))
    (irreducibleDistinct_unitary (min_le_left a b)).1 (irreducibleDistinct_gl (min_le_right a b)).1
    (irreducibleDistinct_unitary (min_le_left a b)).2
    (MvPolynomial (Fin b × Fin a) ℂ) (polyRep (unitaryIncl a) (MonoidHom.id (GL (Fin b) ℂ)))
    (equiv_unitary_gl ha hb) (Vn lam n) (vnRep lam n) (vnRep_irreducible ha lam n) S h1 h2 h3 Q' hQ'
  obtain ⟨m, c, T, hT⟩ := Submodule.mem_span_set'.1 key
  choose y' hy' hyT using fun i => (T i).2
  refine ⟨m, y', c, hy', fun F hF => ren_injective a b ?_⟩
  have := LinearMap.congr_fun hT ⟨F, hF⟩
  rw [LinearMap.sum_apply] at this
  simp only [LinearMap.smul_apply, hyT, subMap_apply] at this
  simp only [map_sum, map_smul]
  exact this.symm

end GlobalTheory.HoweOne
