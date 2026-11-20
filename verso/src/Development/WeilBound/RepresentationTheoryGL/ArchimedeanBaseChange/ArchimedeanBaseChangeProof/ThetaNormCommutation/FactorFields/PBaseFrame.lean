import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.FactorFields.TensorCompl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTwistedClassesCharpoly
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.G3
open scoped Classical TensorProduct

namespace PositivityTheory.Rg.BcB.G3.BaseFrameP

/- English proof (translation)
Use extensionality with `i k`. Simplify using `only [Matrix.map_apply, GlobalTheory.Tw.Phi, Matrix.of_apply]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem phi_map {R S : Type} [CommRing R] [CommRing S] (p : R →+* S) (n : ℕ) :
    (GlobalTheory.Tw.Phi n R).map p = GlobalTheory.Tw.Phi n S := by
  ext i k
  simp only [Matrix.map_apply, GlobalTheory.Tw.Phi, Matrix.of_apply]
  split_ifs <;> simp

end PositivityTheory.Rg.BcB.G3.BaseFrameP

open PositivityTheory.Rg.BcB.G3.BaseFrameP in
/- English proof (translation)
Introduce `F E F' E' _ _ _ _ _ _ _ p j c c' s d hj hc hcj hs0 hcs hspE hspE' n δ hsep B _ _ ρ hfr`. Establish `hps0 : p s ≠ 0` using `(map_ne_zero p).2 hs0`. Establish `hcps : c' (p s) = - p s` using `by rw [hc, hcs, map_neg]`. Establish `indep' : ∀ u v : F', j u + p s * j v = 0 → u = 0 ∧ v = 0`. Introduce `u v h`.

Establish `h2` using `congrArg c' h`. Simplify using `only [map_add, map_mul, hcj, hcps, map_zero] at h2`. Establish `hu : j u = 0`. Establish `h3 : (2 : E') * j u = 0` using `by linear_combination h + h2`. Conclude with `(mul_eq_zero.1 h3).resolve_left two_ne_zero`.

Establish `hv : j v = 0`. Rewrite `h` using `[hu, zero_add]`. Conclude with `(mul_eq_zero.1 h).resolve_left hps0`. Conclude with `⟨(map_eq_zero j).1 hu, (map_eq_zero j).1 hv⟩`. Establish `indepE : ∀ a b : F, algebraMap F E a + s * algebraMap F E b = 0 → a = 0 ∧ b = 0`.

Introduce `a b h`. Establish `h1` using `congrArg p h`. Simplify using `only [map_add, map_mul, ← hj, map_zero] at h1`. Take `⟨h2, h3⟩` from `indep' _ _ h1`. Conclude with `⟨(map_eq_zero (algebraMap F F')).1 h2, (map_eq_zero (algebraMap F F')).1 h3⟩`.

Establish `hli : LinearIndependent F ![(1 : E), s]`. Rewrite using `[LinearIndependent.pair_iff]`. Introduce `a b h`. Apply `indepE a b` to reduce the goal to its premises. Simplify using `only [Algebra.smul_def] at h`.

Take the linear combination `h`. Establish `hsp : ⊤ ≤ Submodule.span F (Set.range ![(1 : E), s])`. Introduce `z _`. Take `⟨a, b, rfl⟩` from `hspE z`. Establish `h1 : (1 : E) ∈ Submodule.span F (Set.range ![(1 : E), s])` using `Submodule.subset_span ⟨0, rfl⟩`.

Establish `h2 : s ∈ Submodule.span F (Set.range ![(1 : E), s])` using `Submodule.subset_span ⟨1, rfl⟩`. Establish `h3` using `Submodule.add_mem _ (Submodule.smul_mem _ a h1) (Submodule.smul_mem _ b h2)`. Use `h3 using 1` and compare the differences between its conclusion and the goal. Rewrite using `[Algebra.smul_def, Algebra.smul_def]`. Expand and normalize the polynomial expressions, which then agree.

Take `⟨bE, hb0, hb1⟩ : ∃ bE : Module.Basis (Fin 2) F E, bE 0 = 1 ∧ bE 1 = s` from `⟨Module.Basis.mk hli hsp, by simp, by simp⟩`. Establish `hdec : ∀ e : E, e = algebraMap F E (bE.repr e 0) + s * algebraMap F E (bE.repr e 1)`. Introduce `e`. Use `conv_lhs => rw [← bE.sum_repr e]`. Rewrite using `[Fin.sum_univ_two, hb0, hb1, Algebra.smul_def, Algebra.smul_def]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hsq : ρ (algebraMap F B d) = s ^ 2 • (1 : Matrix (Fin n) (Fin n) E)` using `hfr.sq`. Establish `hadj : ∀ a, ρ a * (δ.val * GlobalTheory.Tw.Phi n E) = δ.val * GlobalTheory.Tw.Phi n E * ((ρ a).map c)ᵀ` using `hfr.adj`. Establish `hcm : ∀ a, ρ a * (δ * thetaGL n c δ).val = (δ * thetaGL n c δ).val * ρ a` using `hfr.comm`. Choose the witnesses or unpack the hypotheses as in `⟨ρ', hρt⟩ : ∃ ρ' : F' ⊗[F] B →+* Matrix (Fin n) (Fin n) E', ∀ x b, ρ' (x ⊗ₜ b) = j x • (ρ b).map p := by`.

Set `_ : Algebra F E'` to `(p.comp (algebraMap F E)).toAlgebra`. Set `pA : E →ₐ[F] E'` to `{ p with commutes' := fun _ => rfl }`. Set `fA : F' →ₐ[F] Matrix (Fin n) (Fin n) E'` to `{ (Matrix.scalar (Fin n) : E' →+* Matrix (Fin n) (Fin n) E').comp j with commutes' := fun x => by show Matrix.scalar (Fin n) (j (algebraMap F F' x)) = _`. Rewrite using `[hj, Matrix.algebraMap_eq_diagonal, Matrix.scalar_apply]`. Use `rfl }`.

Set `gA : B →ₐ[F] Matrix (Fin n) (Fin n) E'` to `pA.mapMatrix.comp ρ`. Establish `hcomm : ∀ x y, Commute (fA x) (gA y)` using `fun x y => by show Commute (Matrix.scalar (Fin n) (j x)) _`. Conclude with `Matrix.scalar_commute _ (fun _ => Commute.all _ _) _`. Use `⟨(Algebra.TensorProduct.lift fA gA hcomm).toRingHom, fun x b => ?_⟩` and prove the remaining obligations. Rewrite using `[AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.lift_tmul]`.

Use `show Matrix.scalar (Fin n) (j x) * (ρ b).map p = _`. Rewrite using `[Matrix.scalar_apply, Matrix.smul_eq_diagonal_mul]`. Establish `hρ1 : ∀ a, ρ' (1 ⊗ₜ a) = (ρ a).map p`. Introduce `a`. Rewrite using `[hρt, map_one, one_smul]`.

Establish `hρu : ∀ u : F', ρ' (u ⊗ₜ (1 : B)) = j u • (1 : Matrix (Fin n) (Fin n) E')`. Introduce `u`. Rewrite using `[hρt, map_one ρ, Matrix.map_one _ (map_zero p) (map_one p)]`. Establish `hD : ρ' ((1 : F') ⊗ₜ algebraMap F B d) = (p s) ^ 2 • (1 : Matrix (Fin n) (Fin n) E')`. Rewrite using `[hρ1, hsq]`.

Use extensionality with `i k`. Apply the tactic sequence `by_cases h : i = k <;> simp [h, Matrix.one_apply]`. Establish `hN' : (GeneralLinearGroup.map p δ * thetaGL n c' (GeneralLinearGroup.map p δ)).val = (δ * thetaGL n c δ).val.map p`. Rewrite using `[← GlobalTheory.ThetaPull.map_thetaGL p c c' (fun x => (hc x).symm) δ, ← map_mul]`. Both sides reduce to the same expression.

Use `⟨ρ', hρ1, ⟨?_, hD, ?_, ?_, ?_⟩⟩` and prove the remaining obligations. Take `⟨φ, hφdef⟩ : ∃ φ : B →ₗ[F] (Fin n × Fin n × Fin 2 → F), ∀ b i, φ b i = bE.repr (ρ b i.1 i.2.1) i.2.2` from `⟨{ toFun := fun b i => bE.repr (ρ b i.1 i.2.1) i.2.2 map_add' := fun a b => by funext i; simp [map_add] map_smul' := fun r b => by funext i; simp [map_smul] }, fun _ _ => rfl⟩`. Establish `hφ : Function.Injective φ`. Use `(injective_iff_map_eq_zero φ).2 fun b hb => ?_` and prove the remaining obligations. Establish `h1 : ρ b = 0`.

Use extensionality with `i k`. Establish `h2 : bE.repr (ρ b i k) = 0`. Use extensionality with `t`. Use `congrFun hb (i, k, t)` as an intermediate fact. Rewrite `this` using `[hφdef]`.

Simplify using `using this`. Simplify using `using h2`. Conclude with `(injective_iff_map_eq_zero ρ.toRingHom).1 hfr.inj b h1`. Establish `hL : Function.Injective (φ.lTensor F')` using `Module.Flat.lTensor_preserves_injective_linearMap φ hφ`. Establish `hkey : ∀ X : F' ⊗[F] B, ∀ i k, ρ' X i k = j (TensorProduct.piScalarRight F F F' (Fin n × Fin n × Fin 2) (φ.lTensor F' X) (i, k, 0)) + p s * j (TensorProduct.piScalarRight F F F' (Fin n × Fin n × Fin 2) (φ.lTensor F' X) (i, k, 1))`.

Introduce `X i k`. Proceed by induction on `X using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul x b`. Rewrite using `[hρt]`.

Simplify using `only [LinearMap.lTensor_tmul, TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul, hφdef, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, Algebra.smul_def, map_mul]`. Use `conv_lhs => rw [hdec (ρ b i k)]`. Simplify using `only [map_add, map_mul, ← hj]`. Expand and normalize the polynomial expressions, which then agree. Consider the case `add X Y hX hY`.

Simplify using `only [map_add, Matrix.add_apply, hX, hY, Pi.add_apply]`. Expand and normalize the polynomial expressions, which then agree. Use `(injective_iff_map_eq_zero ρ').2 fun X hX => ?_` and prove the remaining obligations. Establish `hW : TensorProduct.piScalarRight F F F' (Fin n × Fin n × Fin 2) (φ.lTensor F' X) = 0`. Use function extensionality and compare the values at `⟨i, k, t⟩`.

Establish `h` using `hkey X i k`. Rewrite `h` using `[hX, Matrix.zero_apply]`. Take `⟨h0, h1⟩` from `indep' _ _ h.symm`. Apply the tactic sequence `have ht : t = 0 ∨ t = 1 := by fin_cases t <;> simp`. Break down `ht with rfl | rfl` into its components or cases.

Conclude with `h0`. Conclude with `h1`. Establish `h0 : φ.lTensor F' X = 0` using `(TensorProduct.piScalarRight F F F' (Fin n × Fin n × Fin 2)).injective (hW.trans (map_zero _).symm)`. Conclude with `hL (by rw [h0, map_zero])`. Introduce `X`.

Rewrite using `[show (GeneralLinearGroup.map p δ).val = δ.val.map p from rfl, ← phi_map p n, ← Matrix.map_mul]`. Proceed by induction on `X using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul x b`. Rewrite using `[hρt]`.

Establish `e1 : ((j x • (ρ b).map p).map c') = j x • (((ρ b).map c).map p)`. Use extensionality with `i k`. Simplify using `[hcj, hc]`. Rewrite using `[e1, Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul]`. Use `congr 1`.

Rewrite using `[← Matrix.map_mul, hadj, ← Matrix.transpose_map, Matrix.map_mul, Matrix.transpose_map, Matrix.transpose_map]`. Consider the case `add X Y hX hY`. Rewrite using `[map_add, add_mul, hX, hY, Matrix.map_add _ (map_add c'), Matrix.transpose_add, mul_add]`. Introduce `X`. Rewrite using `[hN']`.

Proceed by induction on `X using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul x b`. Rewrite using `[hρt, Matrix.smul_mul, Matrix.mul_smul, ← Matrix.map_mul, ← Matrix.map_mul, hcm]`. Consider the case `add X Y hX hY`.

Rewrite using `[map_add, add_mul, mul_add, hX, hY]`. Introduce `x hx`. Rewrite `hx` using `[hN']`. Establish `hsepN' : ((δ * thetaGL n c δ).val.map p).charpoly.Separable`. Rewrite using `[Matrix.charpoly_map]`.

Conclude with `hsep.map`. Take `⟨q, rfl⟩` from `GlobalTheory.BCT.ClsFin.exists_aeval_of_comm _ x hsepN' hx.symm`. Establish `hTadd : ∀ y z : Matrix (Fin n) (Fin n) E', (∃ a b, y = ρ' a + p s • ρ' b) → (∃ a b, z = ρ' a + p s • ρ' b) → ∃ a b, y + z = ρ' a + p s • ρ' b`. Introduce and unpack `y z ⟨a, b, rfl⟩ ⟨a', b', rfl⟩`. Conclude with `⟨a + a', b + b', by rw [map_add, map_add, smul_add]; abel⟩`.

Establish `hT0 : ∃ a b, (0 : Matrix (Fin n) (Fin n) E') = ρ' a + p s • ρ' b` using `⟨0, 0, by simp⟩`. Establish `hTsmul : ∀ (e : E') (y : Matrix (Fin n) (Fin n) E'), (∃ a b, y = ρ' a + p s • ρ' b) → ∃ a b, e • y = ρ' a + p s • ρ' b`. Introduce and unpack `e y ⟨a, b, rfl⟩`. Take `⟨u, v, rfl⟩` from `hspE' e`. Use `⟨(u ⊗ₜ (1 : B)) * a + ((1 : F') ⊗ₜ algebraMap F B d) * ((v ⊗ₜ (1 : B)) * b), (u ⊗ₜ (1 : B)) * b + (v ⊗ₜ (1 : B)) * a, ?_⟩` and prove the remaining obligations.

Simplify using `only [map_add, map_mul, hρu, hD, Matrix.smul_mul, one_mul]`. Use `module`. Establish `hTpow : ∀ k : ℕ, ∃ a b, ((δ * thetaGL n c δ).val.map p) ^ k = ρ' a + p s • ρ' b`. Introduce `k`. Take `⟨a, b, hab⟩` from `hfr.span ((δ * thetaGL n c δ).val ^ k) (Commute.self_pow (δ * thetaGL n c δ).val k).eq.symm`.

Use `⟨1 ⊗ₜ a, 1 ⊗ₜ b, ?_⟩` and prove the remaining obligations. Establish `hpw : ((δ * thetaGL n c δ).val.map p) ^ k = ((δ * thetaGL n c δ).val ^ k).map p` using `(map_pow p.mapMatrix _ k).symm`. Rewrite using `[hpw, hρ1, hρ1, hab]`. Use extensionality with `i k`. Simplify using the standard rewrite rules.

Rewrite using `[aeval_eq_sum_range]`. Conclude with `Finset.sum_induction _ (fun y => ∃ a b, y = ρ' a + p s • ρ' b) hTadd hT0 (fun i _ => hTsmul _ _ (hTpow i))`.
-/
theorem PositivityTheory.Rg.BcB.G3.baseFrame_pf : BaseFrame := by
  intro F E F' E' _ _ _ _ _ _ _ p j c c' s d hj hc hcj hs0 hcs hspE hspE' n δ hsep B _ _ ρ hfr
  have hps0 : p s ≠ 0 := (map_ne_zero p).2 hs0
  have hcps : c' (p s) = - p s := by rw [hc, hcs, map_neg]
  have indep' : ∀ u v : F', j u + p s * j v = 0 → u = 0 ∧ v = 0 := by
    intro u v h
    have h2 := congrArg c' h
    simp only [map_add, map_mul, hcj, hcps, map_zero] at h2
    have hu : j u = 0 := by
      have h3 : (2 : E') * j u = 0 := by linear_combination h + h2
      exact (mul_eq_zero.1 h3).resolve_left two_ne_zero
    have hv : j v = 0 := by
      rw [hu, zero_add] at h
      exact (mul_eq_zero.1 h).resolve_left hps0
    exact ⟨(map_eq_zero j).1 hu, (map_eq_zero j).1 hv⟩
  have indepE : ∀ a b : F, algebraMap F E a + s * algebraMap F E b = 0 → a = 0 ∧ b = 0 := by
    intro a b h
    have h1 := congrArg p h
    simp only [map_add, map_mul, ← hj, map_zero] at h1
    obtain ⟨h2, h3⟩ := indep' _ _ h1
    exact ⟨(map_eq_zero (algebraMap F F')).1 h2, (map_eq_zero (algebraMap F F')).1 h3⟩
  have hli : LinearIndependent F ![(1 : E), s] := by
    rw [LinearIndependent.pair_iff]
    intro a b h
    apply indepE a b
    simp only [Algebra.smul_def] at h
    linear_combination h
  have hsp : ⊤ ≤ Submodule.span F (Set.range ![(1 : E), s]) := by
    intro z _
    obtain ⟨a, b, rfl⟩ := hspE z
    have h1 : (1 : E) ∈ Submodule.span F (Set.range ![(1 : E), s]) := Submodule.subset_span ⟨0, rfl⟩
    have h2 : s ∈ Submodule.span F (Set.range ![(1 : E), s]) := Submodule.subset_span ⟨1, rfl⟩
    have h3 := Submodule.add_mem _ (Submodule.smul_mem _ a h1) (Submodule.smul_mem _ b h2)
    convert h3 using 1
    rw [Algebra.smul_def, Algebra.smul_def]
    ring
  obtain ⟨bE, hb0, hb1⟩ : ∃ bE : Module.Basis (Fin 2) F E, bE 0 = 1 ∧ bE 1 = s :=
    ⟨Module.Basis.mk hli hsp, by simp, by simp⟩
  have hdec : ∀ e : E, e = algebraMap F E (bE.repr e 0) + s * algebraMap F E (bE.repr e 1) := by
    intro e
    conv_lhs => rw [← bE.sum_repr e]
    rw [Fin.sum_univ_two, hb0, hb1, Algebra.smul_def, Algebra.smul_def]
    ring
  have hsq : ρ (algebraMap F B d) = s ^ 2 • (1 : Matrix (Fin n) (Fin n) E) := hfr.sq
  have hadj : ∀ a, ρ a * (δ.val * GlobalTheory.Tw.Phi n E) = δ.val * GlobalTheory.Tw.Phi n E * ((ρ a).map c)ᵀ := hfr.adj
  have hcm : ∀ a, ρ a * (δ * thetaGL n c δ).val = (δ * thetaGL n c δ).val * ρ a := hfr.comm

  obtain ⟨ρ', hρt⟩ : ∃ ρ' : F' ⊗[F] B →+* Matrix (Fin n) (Fin n) E',
      ∀ x b, ρ' (x ⊗ₜ b) = j x • (ρ b).map p := by
    let _ : Algebra F E' := (p.comp (algebraMap F E)).toAlgebra
    let pA : E →ₐ[F] E' := { p with commutes' := fun _ => rfl }
    let fA : F' →ₐ[F] Matrix (Fin n) (Fin n) E' :=
      { (Matrix.scalar (Fin n) : E' →+* Matrix (Fin n) (Fin n) E').comp j with
        commutes' := fun x => by
          show Matrix.scalar (Fin n) (j (algebraMap F F' x)) = _
          rw [hj, Matrix.algebraMap_eq_diagonal, Matrix.scalar_apply]
          rfl }
    let gA : B →ₐ[F] Matrix (Fin n) (Fin n) E' := pA.mapMatrix.comp ρ
    have hcomm : ∀ x y, Commute (fA x) (gA y) := fun x y => by
      show Commute (Matrix.scalar (Fin n) (j x)) _
      exact Matrix.scalar_commute _ (fun _ => Commute.all _ _) _
    refine ⟨(Algebra.TensorProduct.lift fA gA hcomm).toRingHom, fun x b => ?_⟩
    rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.lift_tmul]
    show Matrix.scalar (Fin n) (j x) * (ρ b).map p = _
    rw [Matrix.scalar_apply, Matrix.smul_eq_diagonal_mul]
  have hρ1 : ∀ a, ρ' (1 ⊗ₜ a) = (ρ a).map p := by
    intro a; rw [hρt, map_one, one_smul]
  have hρu : ∀ u : F', ρ' (u ⊗ₜ (1 : B)) = j u • (1 : Matrix (Fin n) (Fin n) E') := by
    intro u; rw [hρt, map_one ρ, Matrix.map_one _ (map_zero p) (map_one p)]
  have hD : ρ' ((1 : F') ⊗ₜ algebraMap F B d) = (p s) ^ 2 • (1 : Matrix (Fin n) (Fin n) E') := by
    rw [hρ1, hsq]
    ext i k
    by_cases h : i = k <;> simp [h, Matrix.one_apply]
  have hN' : (GeneralLinearGroup.map p δ * thetaGL n c' (GeneralLinearGroup.map p δ)).val =
      (δ * thetaGL n c δ).val.map p := by
    rw [← GlobalTheory.ThetaPull.map_thetaGL p c c' (fun x => (hc x).symm) δ, ← map_mul]
    rfl
  refine ⟨ρ', hρ1, ⟨?_, hD, ?_, ?_, ?_⟩⟩
  ·
    obtain ⟨φ, hφdef⟩ : ∃ φ : B →ₗ[F] (Fin n × Fin n × Fin 2 → F),
        ∀ b i, φ b i = bE.repr (ρ b i.1 i.2.1) i.2.2 :=
      ⟨{ toFun := fun b i => bE.repr (ρ b i.1 i.2.1) i.2.2
         map_add' := fun a b => by funext i; simp [map_add]
         map_smul' := fun r b => by funext i; simp [map_smul] }, fun _ _ => rfl⟩
    have hφ : Function.Injective φ := by
      refine (injective_iff_map_eq_zero φ).2 fun b hb => ?_
      have h1 : ρ b = 0 := by
        ext i k
        have h2 : bE.repr (ρ b i k) = 0 := by
          ext t
          have := congrFun hb (i, k, t)
          rw [hφdef] at this
          simpa using this
        simpa using h2
      exact (injective_iff_map_eq_zero ρ.toRingHom).1 hfr.inj b h1
    have hL : Function.Injective (φ.lTensor F') := Module.Flat.lTensor_preserves_injective_linearMap φ hφ
    have hkey : ∀ X : F' ⊗[F] B, ∀ i k, ρ' X i k =
        j (TensorProduct.piScalarRight F F F' (Fin n × Fin n × Fin 2) (φ.lTensor F' X) (i, k, 0)) +
        p s * j (TensorProduct.piScalarRight F F F' (Fin n × Fin n × Fin 2) (φ.lTensor F' X) (i, k, 1)) := by
      intro X i k
      induction X using TensorProduct.induction_on with
      | zero => simp
      | tmul x b =>
        rw [hρt]
        simp only [LinearMap.lTensor_tmul, TensorProduct.piScalarRight_apply,
          TensorProduct.piScalarRightHom_tmul, hφdef, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul,
          Algebra.smul_def, map_mul]
        conv_lhs => rw [hdec (ρ b i k)]
        simp only [map_add, map_mul, ← hj]
        ring
      | add X Y hX hY =>
        simp only [map_add, Matrix.add_apply, hX, hY, Pi.add_apply]
        ring
    refine (injective_iff_map_eq_zero ρ').2 fun X hX => ?_
    have hW : TensorProduct.piScalarRight F F F' (Fin n × Fin n × Fin 2) (φ.lTensor F' X) = 0 := by
      funext ⟨i, k, t⟩
      have h := hkey X i k
      rw [hX, Matrix.zero_apply] at h
      obtain ⟨h0, h1⟩ := indep' _ _ h.symm
      have ht : t = 0 ∨ t = 1 := by fin_cases t <;> simp
      rcases ht with rfl | rfl
      · exact h0
      · exact h1
    have h0 : φ.lTensor F' X = 0 :=
      (TensorProduct.piScalarRight F F F' (Fin n × Fin n × Fin 2)).injective (hW.trans (map_zero _).symm)
    exact hL (by rw [h0, map_zero])
  ·
    intro X
    rw [show (GeneralLinearGroup.map p δ).val = δ.val.map p from rfl, ← phi_map p n, ← Matrix.map_mul]
    induction X using TensorProduct.induction_on with
    | zero => simp
    | tmul x b =>
      rw [hρt]
      have e1 : ((j x • (ρ b).map p).map c') = j x • (((ρ b).map c).map p) := by
        ext i k; simp [hcj, hc]
      rw [e1, Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul]
      congr 1
      rw [← Matrix.map_mul, hadj, ← Matrix.transpose_map, Matrix.map_mul, Matrix.transpose_map, Matrix.transpose_map]
    | add X Y hX hY =>
      rw [map_add, add_mul, hX, hY, Matrix.map_add _ (map_add c'), Matrix.transpose_add, mul_add]
  ·
    intro X
    rw [hN']
    induction X using TensorProduct.induction_on with
    | zero => simp
    | tmul x b =>
      rw [hρt, Matrix.smul_mul, Matrix.mul_smul, ← Matrix.map_mul, ← Matrix.map_mul, hcm]
    | add X Y hX hY =>
      rw [map_add, add_mul, mul_add, hX, hY]
  ·
    intro x hx
    rw [hN'] at hx
    have hsepN' : ((δ * thetaGL n c δ).val.map p).charpoly.Separable := by
      rw [Matrix.charpoly_map]; exact hsep.map
    obtain ⟨q, rfl⟩ := GlobalTheory.BCT.ClsFin.exists_aeval_of_comm _ x hsepN' hx.symm
    have hTadd : ∀ y z : Matrix (Fin n) (Fin n) E', (∃ a b, y = ρ' a + p s • ρ' b) →
        (∃ a b, z = ρ' a + p s • ρ' b) → ∃ a b, y + z = ρ' a + p s • ρ' b := by
      rintro y z ⟨a, b, rfl⟩ ⟨a', b', rfl⟩
      exact ⟨a + a', b + b', by rw [map_add, map_add, smul_add]; abel⟩
    have hT0 : ∃ a b, (0 : Matrix (Fin n) (Fin n) E') = ρ' a + p s • ρ' b := ⟨0, 0, by simp⟩
    have hTsmul : ∀ (e : E') (y : Matrix (Fin n) (Fin n) E'), (∃ a b, y = ρ' a + p s • ρ' b) →
        ∃ a b, e • y = ρ' a + p s • ρ' b := by
      rintro e y ⟨a, b, rfl⟩
      obtain ⟨u, v, rfl⟩ := hspE' e
      refine ⟨(u ⊗ₜ (1 : B)) * a + ((1 : F') ⊗ₜ algebraMap F B d) * ((v ⊗ₜ (1 : B)) * b),
        (u ⊗ₜ (1 : B)) * b + (v ⊗ₜ (1 : B)) * a, ?_⟩
      simp only [map_add, map_mul, hρu, hD, Matrix.smul_mul, one_mul]
      module
    have hTpow : ∀ k : ℕ, ∃ a b, ((δ * thetaGL n c δ).val.map p) ^ k = ρ' a + p s • ρ' b := by
      intro k
      obtain ⟨a, b, hab⟩ := hfr.span ((δ * thetaGL n c δ).val ^ k)
        (Commute.self_pow (δ * thetaGL n c δ).val k).eq.symm
      refine ⟨1 ⊗ₜ a, 1 ⊗ₜ b, ?_⟩
      have hpw : ((δ * thetaGL n c δ).val.map p) ^ k = ((δ * thetaGL n c δ).val ^ k).map p :=
        (map_pow p.mapMatrix _ k).symm
      rw [hpw, hρ1, hρ1, hab]
      ext i k
      simp
    rw [aeval_eq_sum_range]
    exact Finset.sum_induction _ (fun y => ∃ a b, y = ρ' a + p s • ρ' b) hTadd hT0
      (fun i _ => hTsmul _ _ (hTpow i))
