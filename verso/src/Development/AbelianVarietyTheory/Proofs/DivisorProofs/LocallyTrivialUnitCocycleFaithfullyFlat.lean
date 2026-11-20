import Mathlib
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueBaseChangeEqOfMem

open CategoryTheory CategoryTheory.Limits TensorProduct

namespace GlobalTheory

namespace UnitCocycle

section Tensor

variable {R B : Type} [CommRing R] [CommRing B] [Algebra R B]

variable (R B) in

noncomputable def m₁₂ : B ⊗[R] B →ₐ[R] B ⊗[R] (B ⊗[R] B) :=
  Algebra.TensorProduct.map (AlgHom.id R B) Algebra.TensorProduct.includeLeft

variable (R B) in

noncomputable def m₁₃ : B ⊗[R] B →ₐ[R] B ⊗[R] (B ⊗[R] B) :=
  Algebra.TensorProduct.map (AlgHom.id R B) Algebra.TensorProduct.includeRight

variable (R B) in

noncomputable def m₂₃ : B ⊗[R] B →ₐ[R] B ⊗[R] (B ⊗[R] B) :=
  Algebra.TensorProduct.includeRight

noncomputable def datum (c : B ⊗[R] B) : B →ₗ[B] B ⊗[R] B :=
  LinearMap.toSpanSingleton B _ c

/- English proof (translation)
Rewrite using `[datum, LinearMap.toSpanSingleton_apply, Algebra.smul_def, mul_comm]`. Both sides reduce to the same expression.
-/
theorem datum_apply (c : B ⊗[R] B) (x : B) : datum c x = c * (x ⊗ₜ[R] (1 : B)) := by
  rw [datum, LinearMap.toSpanSingleton_apply, Algebra.smul_def, mul_comm]
  rfl

/- English proof (translation)
Set `μ : B ⊗[R] B →ₐ[R] B` to `Algebra.TensorProduct.lmul' R`. Set `ν : B ⊗[R] (B ⊗[R] B) →ₐ[R] B` to `μ.comp (Algebra.TensorProduct.map (AlgHom.id R B) μ)`. Apply the tactic sequence `have h12 : ν.comp (m₁₂ R B) = μ := by ext <;> simp [ν, μ, m₁₂, Algebra.TensorProduct.one_def]`. Apply the tactic sequence `have h13 : ν.comp (m₁₃ R B) = μ := by ext <;> simp [ν, μ, m₁₃, Algebra.TensorProduct.one_def]`. Apply the tactic sequence `have h23 : ν.comp (m₂₃ R B) = μ := by ext <;> simp [ν, μ, m₂₃, Algebra.TensorProduct.one_def]`.

Establish `h'` using `congrArg ν h`. Rewrite `h'` using `[map_mul, ← AlgHom.comp_apply, ← AlgHom.comp_apply, ← AlgHom.comp_apply, h12, h13, h23]`. Conclude with `(hu.map μ).mul_left_cancel (by rw [mul_one]; exact h'.symm)`.
-/
theorem lmul'_eq_one {c : B ⊗[R] B} (hu : IsUnit c)
    (h : m₁₃ R B c = m₁₂ R B c * m₂₃ R B c) : Algebra.TensorProduct.lmul' R c = (1 : B) := by
  let μ : B ⊗[R] B →ₐ[R] B := Algebra.TensorProduct.lmul' R
  let ν : B ⊗[R] (B ⊗[R] B) →ₐ[R] B :=
    μ.comp (Algebra.TensorProduct.map (AlgHom.id R B) μ)
  have h12 : ν.comp (m₁₂ R B) = μ := by ext <;> simp [ν, μ, m₁₂, Algebra.TensorProduct.one_def]
  have h13 : ν.comp (m₁₃ R B) = μ := by ext <;> simp [ν, μ, m₁₃, Algebra.TensorProduct.one_def]
  have h23 : ν.comp (m₂₃ R B) = μ := by ext <;> simp [ν, μ, m₂₃, Algebra.TensorProduct.one_def]
  have h' := congrArg ν h
  rw [map_mul, ← AlgHom.comp_apply, ← AlgHom.comp_apply, ← AlgHom.comp_apply, h12, h13, h23] at h'
  exact (hu.map μ).mul_left_cancel (by rw [mul_one]; exact h'.symm)

/- English proof (translation)
Establish `ha : ∀ z : B ⊗[R] B, FlatDescent.act R B B z = Algebra.TensorProduct.lmul' R z`. Introduce `z`. Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`.

Consider the case `tmul b m => simp`. Establish `h1 : ∀ z : B ⊗[R] B, ((datum c).restrictScalars R).lTensor B z = m₁₂ R B z * m₂₃ R B c`. Introduce `z`. Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`.

Consider the case `add x y hx hy => simp only [map_add, hx, hy, add_mul]`. Consider the case `tmul b m => simp [datum_apply, m₁₂, m₂₃, mul_comm]`. Establish `h2 : ∀ z : B ⊗[R] B, (TensorProduct.mk R B B 1).lTensor B z = m₁₃ R B z`. Introduce `z`. Proceed by induction on `z using TensorProduct.induction_on with`.

Consider the case `zero => simp`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`. Consider the case `tmul b m => simp [m₁₃]`. Prove the components needed by the constructor for the conclusion. Introduce `n`.

Rewrite using `[ha, datum_apply, map_mul, lmul'_eq_one hu h]`. Simplify using the standard rewrite rules. Introduce `n`. Rewrite using `[h1, h2, datum_apply, map_mul, map_mul, h, mul_right_comm]`. Use `congr 1`.
-/
theorem isDescentDatum {c : B ⊗[R] B} (hu : IsUnit c)
    (h : m₁₃ R B c = m₁₂ R B c * m₂₃ R B c) : FlatDescent.IsDescentDatum (datum c) := by
  have ha : ∀ z : B ⊗[R] B, FlatDescent.act R B B z = Algebra.TensorProduct.lmul' R z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul b m => simp
  have h1 : ∀ z : B ⊗[R] B,
      ((datum c).restrictScalars R).lTensor B z = m₁₂ R B z * m₂₃ R B c := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy, add_mul]
    | tmul b m => simp [datum_apply, m₁₂, m₂₃, mul_comm]
  have h2 : ∀ z : B ⊗[R] B, (TensorProduct.mk R B B 1).lTensor B z = m₁₃ R B z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul b m => simp [m₁₃]
  constructor
  · intro n
    rw [ha, datum_apply, map_mul, lmul'_eq_one hu h]
    simp
  · intro n
    rw [h1, h2, datum_apply, map_mul, map_mul, h, mul_right_comm]
    congr 1

/- English proof (translation)
Establish `hd` using `isDescentDatum hu h`. Establish `hI` using `hd.invertible_invariants`. Set `I` to `FlatDescent.invariants (datum c)`. Choose the witnesses or unpack the hypotheses as in `⟨φ, m, hm⟩ : ∃ (φ : Module.Dual R I) (m : I), φ m ∉ P := by`. Assume the negation of the conclusion as `hcon`.

Use `push_neg at hcon`. Apply `hP` to reduce the goal to its premises. Rewrite using `[Ideal.eq_top_iff_one]`. Take `⟨z, hz⟩` from `hI.bijective.2 1`. Rewrite using `[← hz]`.

Use `clear hz`. Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add x y hx hy => rw [map_add]`. Conclude with `P.add_mem hx hy`.

Consider the case `tmul b m => simpa using hcon b m`. Set `e` to `LinearEquiv.ofBijective _ hd.bijective_extend`. Set `Φ : B →ₗ[B] B` to `(AlgebraTensorModule.rid R B B).toLinearMap ∘ₗ LinearMap.baseChange B φ ∘ₗ e.symm.toLinearMap`. Establish `h1 : e.symm (m : B) = 1 ⊗ₜ m`. Rewrite using `[LinearEquiv.symm_apply_eq]`.

Simplify using `[e]`. Use `⟨φ m, hm, m, Φ 1, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← smul_eq_mul, ← map_smul, smul_eq_mul, mul_one]`. Simplify using `[Φ, h1, Algebra.algebraMap_eq_smul_one]`. Rewrite using `[← datum_apply]`.

Conclude with `(FlatDescent.mem_invariants.1 m.2).symm`.
-/
theorem exists_local_tensor [Module.FaithfullyFlat R B] {c : B ⊗[R] B} (hu : IsUnit c)
    (h : m₁₃ R B c = m₁₂ R B c * m₂₃ R B c) (P : Ideal R) (hP : P ≠ ⊤) :
    ∃ s : R, s ∉ P ∧ ∃ x y : B, x * y = algebraMap R B s ∧
      (1 : B) ⊗ₜ[R] x = c * (x ⊗ₜ[R] (1 : B)) := by
  have hd := isDescentDatum hu h
  have hI := hd.invertible_invariants
  let I := FlatDescent.invariants (datum c)
  obtain ⟨φ, m, hm⟩ : ∃ (φ : Module.Dual R I) (m : I), φ m ∉ P := by
    by_contra hcon
    push_neg at hcon
    apply hP
    rw [Ideal.eq_top_iff_one]
    obtain ⟨z, hz⟩ := hI.bijective.2 1
    rw [← hz]
    clear hz
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [map_add]; exact P.add_mem hx hy
    | tmul b m => simpa using hcon b m
  let e := LinearEquiv.ofBijective _ hd.bijective_extend
  let Φ : B →ₗ[B] B :=
    (AlgebraTensorModule.rid R B B).toLinearMap ∘ₗ LinearMap.baseChange B φ ∘ₗ e.symm.toLinearMap
  have h1 : e.symm (m : B) = 1 ⊗ₜ m := by
    rw [LinearEquiv.symm_apply_eq]
    simp [e]
  refine ⟨φ m, hm, m, Φ 1, ?_, ?_⟩
  · rw [← smul_eq_mul, ← map_smul, smul_eq_mul, mul_one]
    simp [Φ, h1, Algebra.algebraMap_eq_smul_one]
  · rw [← datum_apply]
    exact (FlatDescent.mem_invariants.1 m.2).symm

end Tensor

/- English proof (translation)
Use `letI : Algebra R B := f.hom.toAlgebra`. Use `haveI : Module.FaithfullyFlat R B := hf`. Establish `hT` using `CommRingCat.isPushout_tensorProduct R B B`. Set `e : C ≅ CommRingCat.of (B ⊗[R] B)` to `hC.isoIsPushout _ _ hT`. Establish `e1 : j₁ ≫ e.hom = _` using `hC.inl_isoIsPushout_hom _ _ hT`.

Establish `e2 : j₂ ≫ e.hom = _` using `hC.inr_isoIsPushout_hom _ _ hT`. Establish `e1' : ∀ x : B, e.hom.hom (j₁.hom x) = x ⊗ₜ[R] (1 : B)` using `fun x => congrArg (fun q => q.hom x) e1`. Establish `e2' : ∀ x : B, e.hom.hom (j₂.hom x) = (1 : B) ⊗ₜ[R] x` using `fun x => congrArg (fun q => q.hom x) e2`. Set `n₁₂ : C ⟶ CommRingCat.of (B ⊗[R] (B ⊗[R] B))` to `e.hom ≫ CommRingCat.ofHom (m₁₂ R B).toRingHom`. Set `n₁₃ : C ⟶ CommRingCat.of (B ⊗[R] (B ⊗[R] B))` to `e.hom ≫ CommRingCat.ofHom (m₁₃ R B).toRingHom`.

Set `n₂₃ : C ⟶ CommRingCat.of (B ⊗[R] (B ⊗[R] B))` to `e.hom ≫ CommRingCat.ofHom (m₂₃ R B).toRingHom`. Establish `w : j₂ ≫ n₁₂ = j₁ ≫ n₂₃`. Use extensionality with `x`. Express the relevant statement in the definitionally equal form `m₁₂ R B (e.hom.hom (j₂.hom x)) = m₂₃ R B (e.hom.hom (j₁.hom x))`. Rewrite using `[e1', e2']`.

Simplify using `[m₁₂, m₂₃]`. Set `ψ` to `hD.desc n₁₂ n₂₃ w`. Establish `p12 : d₁₂ ≫ ψ = n₁₂` using `hD.inl_desc _ _ _`. Establish `p23 : d₂₃ ≫ ψ = n₂₃` using `hD.inr_desc _ _ _`. Establish `p13 : d₁₃ ≫ ψ = n₁₃`.

Apply `hC.hom_ext` to reduce the goal to its premises. Rewrite using `[← Category.assoc, h₁, Category.assoc, p12]`. Use extensionality with `x`. Express the relevant statement in the definitionally equal form `m₁₂ R B (e.hom.hom (j₁.hom x)) = m₁₃ R B (e.hom.hom (j₁.hom x))`. Rewrite using `[e1']`.

Simplify using `[m₁₂, m₁₃, Algebra.TensorProduct.one_def]`. Rewrite using `[← Category.assoc, h₂, Category.assoc, p23]`. Use extensionality with `x`. Express the relevant statement in the definitionally equal form `m₂₃ R B (e.hom.hom (j₂.hom x)) = m₁₃ R B (e.hom.hom (j₂.hom x))`. Rewrite using `[e2']`.

Simplify using `[m₂₃, m₁₃]`. Establish `hco : m₁₃ R B (e.hom.hom c) = m₁₂ R B (e.hom.hom c) * m₂₃ R B (e.hom.hom c)`. Establish `h'` using `congrArg ψ.hom hc`. Rewrite `h'` using `[map_mul]`. Establish `q12 : ψ.hom (d₁₂.hom c) = m₁₂ R B (e.hom.hom c)` using `congrArg (fun q => q.hom (c : C)) p12`.

Establish `q13 : ψ.hom (d₁₃.hom c) = m₁₃ R B (e.hom.hom c)` using `congrArg (fun q => q.hom (c : C)) p13`. Establish `q23 : ψ.hom (d₂₃.hom c) = m₂₃ R B (e.hom.hom c)` using `congrArg (fun q => q.hom (c : C)) p23`. Rewrite `h'` using `[q12, q13, q23]`. Then use the resulting hypothesis. Take `⟨s, hs, x, y, hxy, hx⟩` from `exists_local_tensor (c.isUnit.map e.hom.hom) hco P hP.ne_top`. Use `⟨s, hs, x, y, hxy, ?_⟩` and prove the remaining obligations.

Apply `e.commRingCatIsoToRingEquiv.injective` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `e.hom.hom _ = e.hom.hom _`. Rewrite using `[map_mul, e1', e2']`. Conclude with `hx`.
-/
theorem exists_local (R B C D : CommRingCat.{0}) (f : R ⟶ B) (j₁ j₂ : B ⟶ C) (d₁₂ d₂₃ d₁₃ : C ⟶ D)
    (hC : IsPushout f f j₁ j₂) (hD : IsPushout j₂ j₁ d₁₂ d₂₃) (h₁ : j₁ ≫ d₁₃ = j₁ ≫ d₁₂)
    (h₂ : j₂ ≫ d₁₃ = j₂ ≫ d₂₃) (hf : f.hom.FaithfullyFlat) (c : Cˣ)
    (hc : d₁₃.hom (c : C) = d₁₂.hom (c : C) * d₂₃.hom (c : C)) (P : Ideal R) (hP : P.IsPrime) :
    ∃ s : R, s ∉ P ∧ ∃ x y : B, x * y = f.hom s ∧ j₂.hom x = (c : C) * j₁.hom x := by
  letI : Algebra R B := f.hom.toAlgebra
  haveI : Module.FaithfullyFlat R B := hf
  have hT := CommRingCat.isPushout_tensorProduct R B B
  let e : C ≅ CommRingCat.of (B ⊗[R] B) := hC.isoIsPushout _ _ hT
  have e1 : j₁ ≫ e.hom = _ := hC.inl_isoIsPushout_hom _ _ hT
  have e2 : j₂ ≫ e.hom = _ := hC.inr_isoIsPushout_hom _ _ hT
  have e1' : ∀ x : B, e.hom.hom (j₁.hom x) = x ⊗ₜ[R] (1 : B) := fun x =>
    congrArg (fun q => q.hom x) e1
  have e2' : ∀ x : B, e.hom.hom (j₂.hom x) = (1 : B) ⊗ₜ[R] x := fun x =>
    congrArg (fun q => q.hom x) e2
  let n₁₂ : C ⟶ CommRingCat.of (B ⊗[R] (B ⊗[R] B)) := e.hom ≫ CommRingCat.ofHom (m₁₂ R B).toRingHom
  let n₁₃ : C ⟶ CommRingCat.of (B ⊗[R] (B ⊗[R] B)) := e.hom ≫ CommRingCat.ofHom (m₁₃ R B).toRingHom
  let n₂₃ : C ⟶ CommRingCat.of (B ⊗[R] (B ⊗[R] B)) := e.hom ≫ CommRingCat.ofHom (m₂₃ R B).toRingHom
  have w : j₂ ≫ n₁₂ = j₁ ≫ n₂₃ := by
    ext x
    change m₁₂ R B (e.hom.hom (j₂.hom x)) = m₂₃ R B (e.hom.hom (j₁.hom x))
    rw [e1', e2']
    simp [m₁₂, m₂₃]
  let ψ := hD.desc n₁₂ n₂₃ w
  have p12 : d₁₂ ≫ ψ = n₁₂ := hD.inl_desc _ _ _
  have p23 : d₂₃ ≫ ψ = n₂₃ := hD.inr_desc _ _ _
  have p13 : d₁₃ ≫ ψ = n₁₃ := by
    apply hC.hom_ext
    · rw [← Category.assoc, h₁, Category.assoc, p12]
      ext x
      change m₁₂ R B (e.hom.hom (j₁.hom x)) = m₁₃ R B (e.hom.hom (j₁.hom x))
      rw [e1']
      simp [m₁₂, m₁₃, Algebra.TensorProduct.one_def]
    · rw [← Category.assoc, h₂, Category.assoc, p23]
      ext x
      change m₂₃ R B (e.hom.hom (j₂.hom x)) = m₁₃ R B (e.hom.hom (j₂.hom x))
      rw [e2']
      simp [m₂₃, m₁₃]
  have hco : m₁₃ R B (e.hom.hom c) = m₁₂ R B (e.hom.hom c) * m₂₃ R B (e.hom.hom c) := by
    have h' := congrArg ψ.hom hc
    rw [map_mul] at h'
    have q12 : ψ.hom (d₁₂.hom c) = m₁₂ R B (e.hom.hom c) := congrArg (fun q => q.hom (c : C)) p12
    have q13 : ψ.hom (d₁₃.hom c) = m₁₃ R B (e.hom.hom c) := congrArg (fun q => q.hom (c : C)) p13
    have q23 : ψ.hom (d₂₃.hom c) = m₂₃ R B (e.hom.hom c) := congrArg (fun q => q.hom (c : C)) p23
    rwa [q12, q13, q23] at h'
  obtain ⟨s, hs, x, y, hxy, hx⟩ :=
    exists_local_tensor (c.isUnit.map e.hom.hom) hco P hP.ne_top
  refine ⟨s, hs, x, y, hxy, ?_⟩
  apply e.commRingCatIsoToRingEquiv.injective
  change e.hom.hom _ = e.hom.hom _
  rw [map_mul, e1', e2']
  exact hx

end UnitCocycle

end GlobalTheory
