import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjRelEquiv
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeftMulMatrixTransfer
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ReducedFreeAlgebraTraceFormPerfect

noncomputable section

open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat
open scoped Classical

namespace GlobalTheory.KapLat.ExModel

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

section Herm

variable (w : Pl E) {n : ℕ}

/- English proof (translation)
Simplify using `[stdH, add_mul, Finset.sum_add_distrib]`.
-/
theorem stdH_add_left (a b c : Fin n → w.adicCompletion E) :
    stdH w (a + b) c = stdH w a c + stdH w b c := by
  simp [stdH, add_mul, Finset.sum_add_distrib]

/- English proof (translation)
Simplify using `[stdH, mul_add, Finset.sum_add_distrib]`.
-/
theorem stdH_add_right (a b c : Fin n → w.adicCompletion E) :
    stdH w a (b + c) = stdH w a b + stdH w a c := by
  simp [stdH, mul_add, Finset.sum_add_distrib]

/- English proof (translation)
Simplify using `[stdH, Finset.mul_sum, mul_assoc]`.
-/
theorem stdH_smul_left (r : w.adicCompletion E) (a b : Fin n → w.adicCompletion E) :
    stdH w (r • a) b = r * stdH w a b := by
  simp [stdH, Finset.mul_sum, mul_assoc]

/- English proof (translation)
Simplify using `only [stdH, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun k _ => by ring`.
-/
theorem stdH_smul_right (r : w.adicCompletion E) (a b : Fin n → w.adicCompletion E) :
    stdH w a (r • b) = cj w r * stdH w a b := by
  simp only [stdH, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

/- English proof (translation)
Simplify using `[stdH, Pi.single_apply, apply_ite (cj w)]`.
-/
theorem stdH_single (a : Fin n → w.adicCompletion E) (k : Fin n) :
    stdH w a (Pi.single k 1) = a k := by
  simp [stdH, Pi.single_apply, apply_ite (cj w)]

/- English proof (translation)
Take `⟨x, rfl⟩` from `e.surjective z`. Rewrite using `[← hB.1, ← hB.1, K.c_c]`.
-/
theorem cj_cj {K : GlobalTheory.UnitLemma.UQ} {e : K.E ≃+* w.adicCompletion E} (hB : Bridge w K e)
    (z : w.adicCompletion E) : cj w (cj w z) = z := by
  obtain ⟨x, rfl⟩ := e.surjective z
  rw [← hB.1, ← hB.1, K.c_c]

/- English proof (translation)
Simplify using `only [stdH, map_sum, map_mul, cj_cj w hB]`. Conclude with `Finset.sum_congr rfl fun k _ => mul_comm _ _`.
-/
theorem stdH_symm {K : GlobalTheory.UnitLemma.UQ} {e : K.E ≃+* w.adicCompletion E} (hB : Bridge w K e)
    (a b : Fin n → w.adicCompletion E) : stdH w b a = cj w (stdH w a b) := by
  simp only [stdH, map_sum, map_mul, cj_cj w hB]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

/- English proof (translation)
Establish `h1 : γ.valᵀ * γ.val.map (cj w) = 1`. Establish `h0 : (γ.val.map (cj w))ᵀ * γ.val = 1` using `by simpa [cT] using hγ`. Establish `h2 : γ.val * (γ.val.map (cj w))ᵀ = 1` using `mul_eq_one_comm.mp h0`. Establish `h3 : γ.val.map (cj w) * γ.valᵀ = 1`. Use `congrArg Matrix.transpose h2` as an intermediate fact.

Simplify `this` using `[Matrix.transpose_mul]`. Conclude with `mul_eq_one_comm.mp h3`. Establish `hc : ∀ z : Fin n → w.adicCompletion E, (fun k => cj w ((γ.val *ᵥ z) k)) = γ.val.map (cj w) *ᵥ (fun k => cj w (z k))`. Introduce `z`. Use function extensionality and compare the values at `k`.

Conclude with `RingHom.map_mulVec (cj w) γ.val z k`. Establish `hs : ∀ a b : Fin n → w.adicCompletion E, stdH w a b = a ⬝ᵥ (fun k => cj w (b k))` using `fun a b => rfl`. Rewrite using `[hs, hs, hc, Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose, Matrix.vecMul_vecMul, h1, Matrix.vecMul_one]`.
-/
theorem stdH_unitary (γ : GLw n w) (hγ : cT (cj w) γ.val * 1 * γ.val = 1)
    (a b : Fin n → w.adicCompletion E) : stdH w (γ.val *ᵥ a) (γ.val *ᵥ b) = stdH w a b := by
  have h1 : γ.valᵀ * γ.val.map (cj w) = 1 := by
    have h0 : (γ.val.map (cj w))ᵀ * γ.val = 1 := by simpa [cT] using hγ
    have h2 : γ.val * (γ.val.map (cj w))ᵀ = 1 := mul_eq_one_comm.mp h0
    have h3 : γ.val.map (cj w) * γ.valᵀ = 1 := by
      have := congrArg Matrix.transpose h2
      simpa [Matrix.transpose_mul] using this
    exact mul_eq_one_comm.mp h3
  have hc : ∀ z : Fin n → w.adicCompletion E,
      (fun k => cj w ((γ.val *ᵥ z) k)) = γ.val.map (cj w) *ᵥ (fun k => cj w (z k)) := by
    intro z; funext k; exact RingHom.map_mulVec (cj w) γ.val z k
  have hs : ∀ a b : Fin n → w.adicCompletion E, stdH w a b = a ⬝ᵥ (fun k => cj w (b k)) :=
    fun a b => rfl
  rw [hs, hs, hc, Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose, Matrix.vecMul_vecMul, h1,
    Matrix.vecMul_one]

end Herm

section Alg

variable {K : GlobalTheory.UnitLemma.UQ} {B : GlobalTheory.UnitLemma.InvAlg K} {n : ℕ}

/- English proof (translation)
Distinguish the cases in `h0 : p = 0`. Simplify using `[h0]`. Rewrite using `[aeval_eq_sum_range' ((natDegree_lt_iff_degree_lt h0).mpr hp) x, ← Fin.sum_univ_eq_sum_range (fun i => p.coeff i • x ^ i)]`.
-/
theorem aeval_eq_sum_fin {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A] (x : A) (p : R[X])
    (hp : p.degree < n) : aeval x p = ∑ i : Fin n, p.coeff i • x ^ (i : ℕ) := by
  by_cases h0 : p = 0
  · simp [h0]
  rw [aeval_eq_sum_range' ((natDegree_lt_iff_degree_lt h0).mpr hp) x,
    ← Fin.sum_univ_eq_sum_range (fun i => p.coeff i • x ^ i)]

variable {u : B.A} {Q' : K.E[X]}

/- English proof (translation)
Establish `hy : y ∈ Algebra.adjoin K.E {u}` using `hadj ▸ Algebra.mem_top`. Rewrite `hy` using `[Algebra.adjoin_singleton_eq_range_aeval]`. Take `⟨p, rfl⟩` from `hy`. Use `⟨p %ₘ Q', ?_, aeval_modByMonic_eq_self_of_root hroot⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.
-/
theorem exists_aeval_lt (hQm : Q'.Monic) (hdeg : Q'.natDegree = n)
    (hadj : Algebra.adjoin K.E {u} = ⊤) (hroot : aeval u Q' = 0) (y : B.A) :
    ∃ p : K.E[X], p.degree < n ∧ aeval u p = y := by
  have hy : y ∈ Algebra.adjoin K.E {u} := hadj ▸ Algebra.mem_top
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hy
  obtain ⟨p, rfl⟩ := hy
  refine ⟨p %ₘ Q', ?_, aeval_modByMonic_eq_self_of_root hroot⟩
  calc (p %ₘ Q').degree < Q'.degree := degree_modByMonic_lt p hQm
    _ = n := by rw [degree_eq_natDegree hQm.ne_zero, hdeg]

/- English proof (translation)
Introduce `y _`. Take `⟨p, hp, rfl⟩` from `exists_aeval_lt hQm hdeg hadj hroot y`. Rewrite using `[aeval_eq_sum_fin u p hp]`. Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`.
-/
theorem span_pow (hQm : Q'.Monic) (hdeg : Q'.natDegree = n)
    (hadj : Algebra.adjoin K.E {u} = ⊤) (hroot : aeval u Q' = 0) :
    ⊤ ≤ Submodule.span K.E (Set.range fun i : Fin n => u ^ (i : ℕ)) := by
  intro y _
  obtain ⟨p, hp, rfl⟩ := exists_aeval_lt hQm hdeg hadj hroot y
  rw [aeval_eq_sum_fin u p hp]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/- English proof (translation)
Rewrite using `[← modByMonic_eq_zero_iff_dvd hQm]`. Establish `hr : (p %ₘ Q').degree < n` using `(degree_modByMonic_lt p hQm).trans_eq (by rw [degree_eq_natDegree hQm.ne_zero, hdeg])`. Establish `h0 : ∑ i : Fin n, (p %ₘ Q').coeff i • u ^ (i : ℕ) = 0`. Rewrite using `[← aeval_eq_sum_fin u _ hr, aeval_modByMonic_eq_self_of_root hroot, hp]`. Establish `hc` using `Fintype.linearIndependent_iff.mp hli _ h0`.

Use extensionality with `k`. Rewrite using `[coeff_zero]`. Distinguish the cases in `hk : k < n`. Conclude with `hc ⟨k, hk⟩`. Conclude with `coeff_eq_zero_of_degree_lt (hr.trans_le (by exact_mod_cast not_lt.mp hk))`.
-/
theorem dvd_of_aeval_eq_zero (hli : LinearIndependent K.E (fun i : Fin n => u ^ (i : ℕ)))
    (hQm : Q'.Monic) (hdeg : Q'.natDegree = n) (hroot : aeval u Q' = 0) (p : K.E[X])
    (hp : aeval u p = 0) : Q' ∣ p := by
  rw [← modByMonic_eq_zero_iff_dvd hQm]
  have hr : (p %ₘ Q').degree < n :=
    (degree_modByMonic_lt p hQm).trans_eq (by rw [degree_eq_natDegree hQm.ne_zero, hdeg])
  have h0 : ∑ i : Fin n, (p %ₘ Q').coeff i • u ^ (i : ℕ) = 0 := by
    rw [← aeval_eq_sum_fin u _ hr, aeval_modByMonic_eq_self_of_root hroot, hp]
  have hc := Fintype.linearIndependent_iff.mp hli _ h0
  ext k
  rw [coeff_zero]
  by_cases hk : k < n
  · exact hc ⟨k, hk⟩
  · exact coeff_eq_zero_of_degree_lt (hr.trans_le (by exact_mod_cast not_lt.mp hk))

/- English proof (translation)
Use `⟨fun a ⟨k, hk⟩ => ?_⟩` and prove the remaining obligations. Take `⟨p, -, rfl⟩` from `exists_aeval_lt hQm hdeg hadj hroot a`. Establish `hd : Q' ∣ p ^ k` using `dvd_of_aeval_eq_zero hli hQm hdeg hroot (p ^ k) (by rw [map_pow]; exact hk)`. Take `⟨r, rfl⟩` from `hsep.squarefree.isRadical k p hd`. Simplify using `[hroot]`.
-/
theorem isReduced_of (hli : LinearIndependent K.E (fun i : Fin n => u ^ (i : ℕ)))
    (hQm : Q'.Monic) (hdeg : Q'.natDegree = n) (hadj : Algebra.adjoin K.E {u} = ⊤)
    (hroot : aeval u Q' = 0) (hsep : Q'.Separable) : IsReduced B.A := by
  refine ⟨fun a ⟨k, hk⟩ => ?_⟩
  obtain ⟨p, -, rfl⟩ := exists_aeval_lt hQm hdeg hadj hroot a
  have hd : Q' ∣ p ^ k := dvd_of_aeval_eq_zero hli hQm hdeg hroot (p ^ k) (by rw [map_pow]; exact hk)
  obtain ⟨r, rfl⟩ := hsep.squarefree.isRadical k p hd
  simp [hroot]

end Alg

end GlobalTheory.KapLat.ExModel

namespace GlobalTheory.KapLat.ExModel

/- English proof (translation)
Introduce `E _ _ _ w hsplit K e hB n Q B u hsep hF γ hγU hQ`. Take `⟨hadj, hroot, hrank, huσ⟩` from `hF`. Substitute `hQ` using the available equality. Establish `hU : cT (cj w) γ.val * 1 * γ.val = 1`. Establish `h` using `hγU`.

Simplify using `only [UL, hsplit, if_false] at h`. Conclude with `h`. Use `set Q' : K.E[X] := (γ.val.charpoly).map e.symm.toRingHom with hQ'`. Establish `hQm : Q'.Monic` using `(charpoly_monic _).map _`. Establish `hdeg : Q'.natDegree = n`.

Rewrite using `[hQ', natDegree_map, charpoly_natDegree_eq_dim, Fintype.card_fin]`. Establish `hrank' : Module.finrank K.E B.A = n`. Rewrite using `[hrank, charpoly_natDegree_eq_dim, Fintype.card_fin]`. Establish `hsep' : Q'.Separable` using `hsep.map`. Establish `hspan` using `span_pow hQm hdeg hadj hroot`.

Establish `hli : LinearIndependent K.E (fun i : Fin n => u ^ (i : ℕ))` using `linearIndependent_of_top_le_span_of_card_eq_finrank hspan (by simp [hrank'])`. Set `bA : Module.Basis (Fin n) K.E B.A` to `Module.Basis.mk hli hspan`. Establish `hbA : ∀ i, bA i = u ^ (i : ℕ)` using `fun i => Module.Basis.mk_apply hli hspan i`. Take `⟨v, hv⟩` from `GlobalTheory.ClassParam.exists_cyclic_field γ.val hsep`. Establish `hliV : LinearIndependent (w.adicCompletion E) (fun j : Fin n => (γ.val ^ (j : ℕ)) *ᵥ v)`.

Use `Matrix.linearIndependent_cols_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hv))` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `j i`. Both sides reduce to the same expression. Set `bV : Module.Basis (Fin n) (w.adicCompletion E) (Fin n → w.adicCompletion E)` to `basisOfLinearIndependentOfCardEqFinrank' _ hliV (by simp)`.

Establish `hbV : ∀ j, bV j = (γ.val ^ (j : ℕ)) *ᵥ v` using `fun j => by simp [bV]`. Set `ψ : B.A ≃+ (Fin n → w.adicCompletion E)` to `bA.equivFun.toAddEquiv.trans ((AddEquiv.piCongrRight fun _ : Fin n => e.toAddEquiv).trans bV.equivFun.symm.toAddEquiv)`. Establish `hψ : ∀ y, ψ y = bV.equivFun.symm (fun i => e (bA.equivFun y i))` using `fun y => rfl`. Establish `hψs : ∀ (c : K.E) (y : B.A), ψ (c • y) = e c • ψ y`. Introduce `c y`.

Rewrite using `[hψ, hψ, ← map_smul]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Simplify using the standard rewrite rules. Establish `hP1 : ∀ p : K.E[X], p.degree < n → ψ (aeval u p) = aeval γ.val (p.map e.toRingHom) *ᵥ v`.

Introduce `p hp`. Establish `h1 : aeval u p = bA.equivFun.symm (fun i => p.coeff i)`. Rewrite using `[aeval_eq_sum_fin u p hp, Module.Basis.equivFun_symm_apply]`. Simplify using `[hbA]`. Establish `hp' : (p.map e.toRingHom).degree < n` using `(degree_map_le).trans_lt hp`.

Rewrite using `[hψ, h1, LinearEquiv.apply_symm_apply, Module.Basis.equivFun_symm_apply, aeval_eq_sum_fin γ.val _ hp', Matrix.sum_mulVec]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[hbV, coeff_map, Matrix.smul_mulVec]`. Both sides reduce to the same expression. Establish `hmapQ : Q'.map e.toRingHom = γ.val.charpoly`.

Use extensionality with `i`. Simplify using `[hQ']`. Establish `hP2 : ∀ p : K.E[X], ψ (aeval u p) = aeval γ.val (p.map e.toRingHom) *ᵥ v`. Introduce `p`. Establish `hr : (p %ₘ Q').degree < n` using `(degree_modByMonic_lt p hQm).trans_eq (by rw [degree_eq_natDegree hQm.ne_zero, hdeg])`.

Rewrite using `[← aeval_modByMonic_eq_self_of_root hroot, hP1 _ hr, map_modByMonic _ hQm, hmapQ, aeval_modByMonic_eq_self_of_root (aeval_self_charpoly γ.val)]`. Establish `hψ1 : ψ 1 = v`. Simplify using `using hP2 1`. Establish `hmul : ∀ y, ψ (u * y) = γ.val *ᵥ ψ y`. Introduce `y`.

Take `⟨p, -, rfl⟩` from `exists_aeval_lt hQm hdeg hadj hroot y`. Establish `: u * aeval u p = aeval u (X * p)` using `by rw [map_mul, aeval_X]`. Rewrite using `[this, hP2, hP2, Polynomial.map_mul, map_X, map_mul, aeval_X, Matrix.mulVec_mulVec]`. Establish `hadjP : ∀ a y z, stdH w (ψ (a * y)) (ψ z) = stdH w (ψ y) (ψ (B.σ a * z))`. Introduce `a`.

Establish `ha : a ∈ Algebra.adjoin K.E {u}` using `hadj ▸ Algebra.mem_top`. Proceed by induction on `ha using Algebra.adjoin_induction with`. Consider the case `mem x hx`. Rewrite `hx` using `[Set.mem_singleton_iff]`. Rewrite using `[hx]`.

Introduce `y z`. Establish `h1 : ψ z = γ.val *ᵥ ψ (B.σ u * z)` using `by rw [← hmul, ← mul_assoc, huσ, one_mul]`. Rewrite using `[hmul, h1, stdH_unitary w γ hU]`. Consider the case `algebraMap r`. Introduce `y z`.

Rewrite using `[B.σ_alg, ← Algebra.smul_def, ← Algebra.smul_def, hψs, hψs, stdH_smul_left, stdH_smul_right, hB.1, cj_cj w hB]`. Consider the case `add a b _ _ ha hb`. Introduce `y z`. Rewrite using `[add_mul, map_add ψ, stdH_add_left, ha, hb, map_add B.σ, add_mul, map_add ψ, stdH_add_right]`. Consider the case `mul a b _ _ ha hb`.

Introduce `y z`. Rewrite using `[mul_assoc, ha, hb, map_mul B.σ]`. Use `congr 2`. Expand and normalize the polynomial expressions, which then agree. Set `lam : B.A →ₗ[K.E] K.E` to `{ toFun := fun a => e.symm (stdH w (ψ a) v) map_add' := by intro a b; rw [map_add, stdH_add_left, map_add] map_smul' := by`.

Introduce `r a`. Rewrite using `[hψs, stdH_smul_left, map_mul, RingEquiv.symm_apply_apply]`. Use `rfl }`. Use `haveI := isReduced_of hli hQm hdeg hadj hroot hsep'`. Establish `hnd : ∀ a : B.A, (∀ y, Algebra.trace K.E B.A (a * y) = 0) → a = 0` using `fun a ha => GlobalTheory.RegSS.eq_zero_of_trace_mul_eq_zero a ha`.

Establish `hinj : Function.Injective (Algebra.traceForm K.E B.A)`. Introduce `a b hab`. Rewrite using `[← sub_eq_zero]`. Apply `hnd` to reduce the goal to its premises. Introduce `y`.

Use `LinearMap.congr_fun hab y` as an intermediate fact. Simplify using `only [Algebra.traceForm_apply] at this`. Rewrite using `[sub_mul, map_sub, this, sub_self]`. Establish `hsurj : Function.Surjective (Algebra.traceForm K.E B.A)` using `(LinearMap.injective_iff_surjective_of_finrank_eq_finrank Subspace.dual_finrank_eq.symm).mp hinj`. Take `⟨x, hx⟩` from `hsurj lam`.

Establish `hxa : ∀ a, Algebra.trace K.E B.A (x * a) = e.symm (stdH w (ψ a) v)` using `fun a => by`. Use `LinearMap.congr_fun hx a` as an intermediate fact. Simplify `this` using `[Algebra.traceForm_apply, lam]`. Establish `hform : ∀ y z, stdH w (ψ y) (ψ z) = e (B.herm x y z)`. Introduce `y z`.

Establish `h1` using `hadjP (B.σ z) y 1`. Rewrite `h1` using `[B.σ_σ, mul_one]`. Rewrite using `[← h1, hψ1, GlobalTheory.UnitLemma.InvAlg.herm, show x * y * B.σ z = x * (B.σ z * y) by ring, hxa, RingEquiv.apply_symm_apply]`. Establish `htr : ∀ a, Algebra.trace K.E B.A (x * B.σ a) = K.c (Algebra.trace K.E B.A (x * a))`. Introduce `a`.

Apply `e.injective` to reduce the goal to its premises. Establish `e1 : B.herm x 1 a = Algebra.trace K.E B.A (x * B.σ a)`. Simplify using `[GlobalTheory.UnitLemma.InvAlg.herm]`. Establish `e2 : B.herm x a 1 = Algebra.trace K.E B.A (x * a)`. Simplify using `[GlobalTheory.UnitLemma.InvAlg.herm]`.

Rewrite using `[← e1, ← e2, ← hform, hB.1, ← hform]`. Conclude with `stdH_symm w hB _ _`. Establish `htrσ : ∀ a : B.A, Algebra.trace K.E B.A (B.σ a) = K.c (Algebra.trace K.E B.A a)`. Introduce `a`. Establish `h` using `Algebra.trace_eq_of_equiv_equiv K.c B.σ (by ext r; simp [B.σ_alg]) a`.

Rewrite using `[h, RingEquiv.apply_symm_apply]`. Establish `hσx : B.σ x = x`. Rewrite using `[← sub_eq_zero]`. Apply `hnd` to reduce the goal to its premises. Introduce `a`.

Rewrite using `[sub_mul, map_sub, sub_eq_zero]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[map_mul B.σ, B.σ_σ]`. Use `_ = K.c (Algebra.trace K.E B.A (x * B.σ a)) := htrσ _`. Use `_ = K.c (K.c (Algebra.trace K.E B.A (x * a))) := by rw [htr]`.

Use `_ = Algebra.trace K.E B.A (x * a) := K.c_c _`. Establish `hxinj : Function.Injective (LinearMap.mulLeft K.E x)`. Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce `a ha`. Simplify using `only [LinearMap.mulLeft_apply] at ha`.

Establish `h0 : ψ a = 0`. Use function extensionality and compare the values at `k`. Take `⟨z, hz⟩` from `ψ.surjective (Pi.single k 1)`. Use `hform a z` as an intermediate fact. Rewrite `this` using `[hz, stdH_single]`.

Rewrite using `[this, GlobalTheory.UnitLemma.InvAlg.herm, ha, zero_mul, map_zero, map_zero]`. Both sides reduce to the same expression. Conclude with `ψ.injective (h0.trans (map_zero ψ).symm)`. Take `⟨y, hy⟩` from `(LinearMap.injective_iff_surjective.mp hxinj) 1`. Conclude with `⟨x, hσx, ⟨⟨x, y, hy, by rw [mul_comm]; exact hy⟩, rfl⟩, ψ, hψs, hmul, hform⟩`.
-/
theorem exists_isModel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E), ¬ IsSplitAt w →
    ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), Bridge w K e → ∀ (n : ℕ)
    (Q : (w.adicCompletion E)[X]) (B : GlobalTheory.UnitLemma.InvAlg K) (u : B.A), Q.Separable → Fits w e B Q u →
    ∀ γ : GLw n w, γ ∈ UL n w → γ.val.charpoly = Q → ∃ x : B.A, B.σ x = x ∧ IsUnit x ∧ IsModel w e B u x γ := by
  intro E _ _ _ w hsplit K e hB n Q B u hsep hF γ hγU hQ
  obtain ⟨hadj, hroot, hrank, huσ⟩ := hF
  subst hQ
  have hU : cT (cj w) γ.val * 1 * γ.val = 1 := by
    have h := hγU
    simp only [UL, hsplit, if_false] at h
    exact h
  set Q' : K.E[X] := (γ.val.charpoly).map e.symm.toRingHom with hQ'
  have hQm : Q'.Monic := (charpoly_monic _).map _
  have hdeg : Q'.natDegree = n := by
    rw [hQ', natDegree_map, charpoly_natDegree_eq_dim, Fintype.card_fin]
  have hrank' : Module.finrank K.E B.A = n := by
    rw [hrank, charpoly_natDegree_eq_dim, Fintype.card_fin]
  have hsep' : Q'.Separable := hsep.map
  have hspan := span_pow hQm hdeg hadj hroot
  have hli : LinearIndependent K.E (fun i : Fin n => u ^ (i : ℕ)) :=
    linearIndependent_of_top_le_span_of_card_eq_finrank hspan (by simp [hrank'])
  let bA : Module.Basis (Fin n) K.E B.A := Module.Basis.mk hli hspan
  have hbA : ∀ i, bA i = u ^ (i : ℕ) := fun i => Module.Basis.mk_apply hli hspan i

  obtain ⟨v, hv⟩ := GlobalTheory.ClassParam.exists_cyclic_field γ.val hsep
  have hliV : LinearIndependent (w.adicCompletion E) (fun j : Fin n => (γ.val ^ (j : ℕ)) *ᵥ v) := by
    have := Matrix.linearIndependent_cols_iff_isUnit.mpr
      ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hv))
    convert this using 1
    funext j i
    rfl
  let bV : Module.Basis (Fin n) (w.adicCompletion E) (Fin n → w.adicCompletion E) :=
    basisOfLinearIndependentOfCardEqFinrank' _ hliV (by simp)
  have hbV : ∀ j, bV j = (γ.val ^ (j : ℕ)) *ᵥ v := fun j => by simp [bV]
  let ψ : B.A ≃+ (Fin n → w.adicCompletion E) :=
    bA.equivFun.toAddEquiv.trans
      ((AddEquiv.piCongrRight fun _ : Fin n => e.toAddEquiv).trans bV.equivFun.symm.toAddEquiv)
  have hψ : ∀ y, ψ y = bV.equivFun.symm (fun i => e (bA.equivFun y i)) := fun y => rfl
  have hψs : ∀ (c : K.E) (y : B.A), ψ (c • y) = e c • ψ y := by
    intro c y
    rw [hψ, hψ, ← map_smul]
    congr 1
    funext i
    simp

  have hP1 : ∀ p : K.E[X], p.degree < n → ψ (aeval u p) = aeval γ.val (p.map e.toRingHom) *ᵥ v := by
    intro p hp
    have h1 : aeval u p = bA.equivFun.symm (fun i => p.coeff i) := by
      rw [aeval_eq_sum_fin u p hp, Module.Basis.equivFun_symm_apply]
      simp [hbA]
    have hp' : (p.map e.toRingHom).degree < n := (degree_map_le).trans_lt hp
    rw [hψ, h1, LinearEquiv.apply_symm_apply, Module.Basis.equivFun_symm_apply,
      aeval_eq_sum_fin γ.val _ hp', Matrix.sum_mulVec]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hbV, coeff_map, Matrix.smul_mulVec]
    rfl
  have hmapQ : Q'.map e.toRingHom = γ.val.charpoly := by
    ext i; simp [hQ']
  have hP2 : ∀ p : K.E[X], ψ (aeval u p) = aeval γ.val (p.map e.toRingHom) *ᵥ v := by
    intro p
    have hr : (p %ₘ Q').degree < n :=
      (degree_modByMonic_lt p hQm).trans_eq (by rw [degree_eq_natDegree hQm.ne_zero, hdeg])
    rw [← aeval_modByMonic_eq_self_of_root hroot, hP1 _ hr, map_modByMonic _ hQm, hmapQ,
      aeval_modByMonic_eq_self_of_root (aeval_self_charpoly γ.val)]
  have hψ1 : ψ 1 = v := by
    simpa using hP2 1
  have hmul : ∀ y, ψ (u * y) = γ.val *ᵥ ψ y := by
    intro y
    obtain ⟨p, -, rfl⟩ := exists_aeval_lt hQm hdeg hadj hroot y
    have : u * aeval u p = aeval u (X * p) := by rw [map_mul, aeval_X]
    rw [this, hP2, hP2, Polynomial.map_mul, map_X, map_mul, aeval_X, Matrix.mulVec_mulVec]

  have hadjP : ∀ a y z, stdH w (ψ (a * y)) (ψ z) = stdH w (ψ y) (ψ (B.σ a * z)) := by
    intro a
    have ha : a ∈ Algebra.adjoin K.E {u} := hadj ▸ Algebra.mem_top
    induction ha using Algebra.adjoin_induction with
    | mem x hx =>
      rw [Set.mem_singleton_iff] at hx
      rw [hx]
      intro y z
      have h1 : ψ z = γ.val *ᵥ ψ (B.σ u * z) := by rw [← hmul, ← mul_assoc, huσ, one_mul]
      rw [hmul, h1, stdH_unitary w γ hU]
    | algebraMap r =>
      intro y z
      rw [B.σ_alg, ← Algebra.smul_def, ← Algebra.smul_def, hψs, hψs, stdH_smul_left, stdH_smul_right,
        hB.1, cj_cj w hB]
    | add a b _ _ ha hb =>
      intro y z
      rw [add_mul, map_add ψ, stdH_add_left, ha, hb, map_add B.σ, add_mul, map_add ψ, stdH_add_right]
    | mul a b _ _ ha hb =>
      intro y z
      rw [mul_assoc, ha, hb, map_mul B.σ]
      congr 2
      ring

  let lam : B.A →ₗ[K.E] K.E :=
    { toFun := fun a => e.symm (stdH w (ψ a) v)
      map_add' := by intro a b; rw [map_add, stdH_add_left, map_add]
      map_smul' := by
        intro r a
        rw [hψs, stdH_smul_left, map_mul, RingEquiv.symm_apply_apply]
        rfl }
  haveI := isReduced_of hli hQm hdeg hadj hroot hsep'
  have hnd : ∀ a : B.A, (∀ y, Algebra.trace K.E B.A (a * y) = 0) → a = 0 := fun a ha =>
    GlobalTheory.RegSS.eq_zero_of_trace_mul_eq_zero a ha
  have hinj : Function.Injective (Algebra.traceForm K.E B.A) := by
    intro a b hab
    rw [← sub_eq_zero]
    apply hnd
    intro y
    have := LinearMap.congr_fun hab y
    simp only [Algebra.traceForm_apply] at this
    rw [sub_mul, map_sub, this, sub_self]
  have hsurj : Function.Surjective (Algebra.traceForm K.E B.A) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank Subspace.dual_finrank_eq.symm).mp hinj
  obtain ⟨x, hx⟩ := hsurj lam
  have hxa : ∀ a, Algebra.trace K.E B.A (x * a) = e.symm (stdH w (ψ a) v) := fun a => by
    have := LinearMap.congr_fun hx a
    simpa [Algebra.traceForm_apply, lam] using this
  have hform : ∀ y z, stdH w (ψ y) (ψ z) = e (B.herm x y z) := by
    intro y z
    have h1 := hadjP (B.σ z) y 1
    rw [B.σ_σ, mul_one] at h1
    rw [← h1, hψ1, GlobalTheory.UnitLemma.InvAlg.herm, show x * y * B.σ z = x * (B.σ z * y) by ring, hxa,
      RingEquiv.apply_symm_apply]
  have htr : ∀ a, Algebra.trace K.E B.A (x * B.σ a) = K.c (Algebra.trace K.E B.A (x * a)) := by
    intro a
    apply e.injective
    have e1 : B.herm x 1 a = Algebra.trace K.E B.A (x * B.σ a) := by
      simp [GlobalTheory.UnitLemma.InvAlg.herm]
    have e2 : B.herm x a 1 = Algebra.trace K.E B.A (x * a) := by
      simp [GlobalTheory.UnitLemma.InvAlg.herm]
    rw [← e1, ← e2, ← hform, hB.1, ← hform]
    exact stdH_symm w hB _ _
  have htrσ : ∀ a : B.A, Algebra.trace K.E B.A (B.σ a) = K.c (Algebra.trace K.E B.A a) := by
    intro a
    have h := Algebra.trace_eq_of_equiv_equiv K.c B.σ (by ext r; simp [B.σ_alg]) a
    rw [h, RingEquiv.apply_symm_apply]
  have hσx : B.σ x = x := by
    rw [← sub_eq_zero]
    apply hnd
    intro a
    rw [sub_mul, map_sub, sub_eq_zero]
    calc Algebra.trace K.E B.A (B.σ x * a) = Algebra.trace K.E B.A (B.σ (x * B.σ a)) := by
          rw [map_mul B.σ, B.σ_σ]
      _ = K.c (Algebra.trace K.E B.A (x * B.σ a)) := htrσ _
      _ = K.c (K.c (Algebra.trace K.E B.A (x * a))) := by rw [htr]
      _ = Algebra.trace K.E B.A (x * a) := K.c_c _
  have hxinj : Function.Injective (LinearMap.mulLeft K.E x) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro a ha
    simp only [LinearMap.mulLeft_apply] at ha
    have h0 : ψ a = 0 := by
      funext k
      obtain ⟨z, hz⟩ := ψ.surjective (Pi.single k 1)
      have := hform a z
      rw [hz, stdH_single] at this
      rw [this, GlobalTheory.UnitLemma.InvAlg.herm, ha, zero_mul, map_zero, map_zero]
      rfl
    exact ψ.injective (h0.trans (map_zero ψ).symm)
  obtain ⟨y, hy⟩ := (LinearMap.injective_iff_surjective.mp hxinj) 1
  exact ⟨x, hσx, ⟨⟨x, y, hy, by rw [mul_comm]; exact hy⟩, rfl⟩, ψ, hψs, hmul, hform⟩

end GlobalTheory.KapLat.ExModel
