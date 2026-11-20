import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.HighestVectorsRegularLine
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WtRInjective
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SumMemOfStable
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryEuclideanModelStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InvariantIntertwinesDualStatement

noncomputable section

open Matrix Finset
open scoped InnerProductSpace

open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount GlobalTheory.CompanionTheory.RealCountG
open GlobalTheory.CompanionTheory.RealCount.InjHw

namespace GlobalTheory.CompanionTheory.RealCountG.InjG

variable {n : ℕ}

section Dual

variable {E : KMod n} {G : Fin n → Fin n → Module.End ℂ (E.V →L[ℂ] ℂ)}

/- English proof (translation)
Establish `hd` using `hG.2 X (expU X hX) hX (fun _ => rfl) ξ`. Establish `hcl : IsClosed (R : Set (E.V →L[ℂ] ℂ))` using `Submodule.closed_of_finiteDimensional R`. Establish `ht` using `hasDerivAt_iff_tendsto_slope_zero.1 hd`. Use `hcl.mem_of_tendsto ht (Filter.Eventually.of_forall fun s => ?_)` and prove the remaining obligations. Establish `: s⁻¹ • (ξ ∘L E.ρ (expU X hX (0 + s))⁻¹ - ξ ∘L E.ρ (expU X hX 0)⁻¹) ∈ R.restrictScalars ℝ` using `Submodule.smul_mem _ _ (sub_mem (hR _ _ hξ) (hR _ _ hξ))`.

Conclude with `this`.
-/
theorem dual_sum_mem (hG : IsDualFam E G) (R : Submodule ℂ (E.V →L[ℂ] ℂ))
    (hR : ∀ k, ∀ ξ ∈ R, ξ ∘L E.ρ k⁻¹ ∈ R) (X : Matrix (Fin n) (Fin n) ℂ) (hX : Xᴴ = -X)
    {ξ : E.V →L[ℂ] ℂ} (hξ : ξ ∈ R) : ∑ a, ∑ b, X a b • G a b ξ ∈ R := by
  have hd := hG.2 X (expU X hX) hX (fun _ => rfl) ξ
  have hcl : IsClosed (R : Set (E.V →L[ℂ] ℂ)) := Submodule.closed_of_finiteDimensional R
  have ht := hasDerivAt_iff_tendsto_slope_zero.1 hd
  refine hcl.mem_of_tendsto ht (Filter.Eventually.of_forall fun s => ?_)
  have : s⁻¹ • (ξ ∘L E.ρ (expU X hX (0 + s))⁻¹ - ξ ∘L E.ρ (expU X hX 0)⁻¹) ∈ R.restrictScalars ℝ :=
    Submodule.smul_mem _ _ (sub_mem (hR _ _ hξ) (hR _ _ hξ))
  exact this

/- English proof (translation)
Rewrite using `[Finset.sum_eq_single a, Finset.sum_eq_single b]`. Simplify using the standard rewrite rules. Introduce `y _ hy`. Rewrite using `[Matrix.single_apply, if_neg (fun hh => hy hh.2.symm), zero_smul]`. Simplify using the standard rewrite rules.

Introduce `x _ hx`. Use `Finset.sum_eq_zero fun y _ => ?_` and prove the remaining obligations. Rewrite using `[Matrix.single_apply, if_neg (fun hh => hx hh.1.symm), zero_smul]`. Simplify using the standard rewrite rules.
-/
theorem sum_single_dual (w : E.V →L[ℂ] ℂ) (a b : Fin n) (c : ℂ) :
    ∑ x, ∑ y, (Matrix.single a b c : Matrix (Fin n) (Fin n) ℂ) x y • G x y w = c • G a b w := by
  rw [Finset.sum_eq_single a, Finset.sum_eq_single b]
  · simp
  · intro y _ hy
    rw [Matrix.single_apply, if_neg (fun hh => hy hh.2.symm), zero_smul]
  · simp
  · intro x _ hx
    refine Finset.sum_eq_zero fun y _ => ?_
    rw [Matrix.single_apply, if_neg (fun hh => hx hh.1.symm), zero_smul]
  · simp

/- English proof (translation)
Establish `h1 : (Matrix.single a b (1 : ℂ) - Matrix.single b a 1)ᴴ = -(Matrix.single a b (1 : ℂ) - Matrix.single b a 1)`. Rewrite using `[conjTranspose_sub, single_conjT, single_conjT, star_one, neg_sub]`. Establish `h2 : (Matrix.single a b Complex.I + Matrix.single b a Complex.I)ᴴ = -(Matrix.single a b Complex.I + Matrix.single b a Complex.I)`. Rewrite using `[conjTranspose_add, single_conjT, single_conjT, Complex.star_def, Complex.conj_I, single_negI, single_negI, neg_add, add_comm]`. Establish `m1` using `dual_sum_mem hG R hR _ h1 hw`.

Establish `m2` using `dual_sum_mem hG R hR _ h2 hw`. Establish `e1 : ∑ x, ∑ y, (Matrix.single a b (1 : ℂ) - Matrix.single b a 1 : Matrix (Fin n) (Fin n) ℂ) x y • G x y w = G a b w - G b a w`. Simplify using `only [Matrix.sub_apply, sub_smul, Finset.sum_sub_distrib, sum_single_dual, one_smul]`. Establish `e2 : ∑ x, ∑ y, (Matrix.single a b Complex.I + Matrix.single b a Complex.I : Matrix (Fin n) (Fin n) ℂ) x y • G x y w = Complex.I • G a b w + Complex.I • G b a w`. Simplify using `only [Matrix.add_apply, add_smul, Finset.sum_add_distrib, sum_single_dual]`.

Rewrite `m1` using `[e1]`. Rewrite `m2` using `[e2]`. Establish `m3` using `R.smul_mem (-Complex.I) m2`. Establish `m4` using `R.smul_mem (1 / 2 : ℂ) (R.add_mem m1 m3)`. Establish `e3 : (1 / 2 : ℂ) • (G a b w - G b a w + -Complex.I • (Complex.I • G a b w + Complex.I • G b a w)) = G a b w`.

Rewrite using `[smul_add (-Complex.I), smul_smul, smul_smul]`. Establish `: -Complex.I * Complex.I = 1` using `by simp`. Rewrite using `[this, one_smul, one_smul, sub_add_add_cancel, ← two_smul ℂ, smul_smul]`. Evaluate the numerical expressions. Rewrite `m4` using `[e3]`. Then use the resulting hypothesis.
-/
theorem dual_entry_mem (hG : IsDualFam E G) (R : Submodule ℂ (E.V →L[ℂ] ℂ))
    (hR : ∀ k, ∀ ξ ∈ R, ξ ∘L E.ρ k⁻¹ ∈ R) (a b : Fin n) {w : E.V →L[ℂ] ℂ} (hw : w ∈ R) : G a b w ∈ R := by
  have h1 : (Matrix.single a b (1 : ℂ) - Matrix.single b a 1)ᴴ = -(Matrix.single a b (1 : ℂ) - Matrix.single b a 1) := by
    rw [conjTranspose_sub, single_conjT, single_conjT, star_one, neg_sub]
  have h2 : (Matrix.single a b Complex.I + Matrix.single b a Complex.I)ᴴ =
      -(Matrix.single a b Complex.I + Matrix.single b a Complex.I) := by
    rw [conjTranspose_add, single_conjT, single_conjT, Complex.star_def, Complex.conj_I, single_negI, single_negI, neg_add,
      add_comm]
  have m1 := dual_sum_mem hG R hR _ h1 hw
  have m2 := dual_sum_mem hG R hR _ h2 hw
  have e1 : ∑ x, ∑ y, (Matrix.single a b (1 : ℂ) - Matrix.single b a 1 : Matrix (Fin n) (Fin n) ℂ) x y • G x y w =
      G a b w - G b a w := by
    simp only [Matrix.sub_apply, sub_smul, Finset.sum_sub_distrib, sum_single_dual, one_smul]
  have e2 : ∑ x, ∑ y, (Matrix.single a b Complex.I + Matrix.single b a Complex.I : Matrix (Fin n) (Fin n) ℂ) x y • G x y w =
      Complex.I • G a b w + Complex.I • G b a w := by
    simp only [Matrix.add_apply, add_smul, Finset.sum_add_distrib, sum_single_dual]
  rw [e1] at m1
  rw [e2] at m2
  have m3 := R.smul_mem (-Complex.I) m2
  have m4 := R.smul_mem (1 / 2 : ℂ) (R.add_mem m1 m3)
  have e3 : (1 / 2 : ℂ) • (G a b w - G b a w + -Complex.I • (Complex.I • G a b w + Complex.I • G b a w)) = G a b w := by
    rw [smul_add (-Complex.I), smul_smul, smul_smul]
    have : -Complex.I * Complex.I = 1 := by simp
    rw [this, one_smul, one_smul, sub_add_add_cancel, ← two_smul ℂ, smul_smul]
    norm_num
  rwa [e3] at m4

/- English proof (translation)
Establish `hX : (Matrix.single a a Complex.I)ᴴ = -(Matrix.single a a Complex.I)`. Rewrite using `[single_conjT, Complex.star_def, Complex.conj_I, single_negI]`. Establish `hd` using `hG.2 _ (expU _ hX) hX (fun _ => rfl) v`. Rewrite `hd` using `[sum_single_dual]`. Establish `hk : ∀ s : ℝ, (expU _ hX s).1 = diagonal (fun c => if c = a then Complex.exp (s * Complex.I) else 1)`.

Introduce `s`. Establish `e : (s : ℂ) • (Matrix.single a a Complex.I : Matrix (Fin n) (Fin n) ℂ) = diagonal (fun c => if c = a then (s : ℂ) * Complex.I else 0)`. Use extensionality with `i j`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality.

Distinguish the cases in `hc : i = a`. Substitute `hc` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Matrix.single_apply, hc, Ne.symm hc]`. Rewrite using `[Matrix.diagonal_apply_ne _ hij, Matrix.smul_apply, Matrix.single_apply, if_neg (fun hh => hij (hh.1.symm.trans hh.2)), smul_zero]`.

Use `show NormedSpace.exp _ = _`. Rewrite using `[e, Matrix.exp_diagonal]`. Use `congr 1`. Use function extensionality and compare the values at `c`. Apply the tactic sequence `split_ifs with hc <;> simp [hc, Complex.exp_eq_exp_ℂ]`.

Establish `hf : (fun s : ℝ => v ∘L E.ρ (expU _ hX s)⁻¹) = fun s : ℝ => Complex.exp ((s : ℂ) * (Complex.I * ((μ a : ℝ) : ℂ))) • v`. Use function extensionality and compare the values at `s`. Rewrite using `[hv _ _ (hk s), Finset.prod_eq_single a]`. Simplify using `only [if_true]`. Rewrite using `[← Complex.exp_int_mul]`.

Use `congr 2`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Introduce `c _ hc`. Simplify using `[hc]`.

Simplify using the standard rewrite rules. Rewrite `hd` using `[hf]`. Establish `h2 : HasDerivAt (fun s : ℝ => Complex.exp ((s : ℂ) * (Complex.I * ((μ a : ℝ) : ℂ))) • v) ((Complex.I * ((μ a : ℝ) : ℂ)) • v) 0`. Establish `h3 : HasDerivAt (fun y : ℂ => Complex.exp (y * (Complex.I * ((μ a : ℝ) : ℂ)))) (Complex.exp ((0 : ℂ) * (Complex.I * ((μ a : ℝ) : ℂ))) * (1 * (Complex.I * ((μ a : ℝ) : ℂ)))) 0` using `((hasDerivAt_id (0 : ℂ)).mul_const _).cexp`. Establish `h4` using `(h3.comp_ofReal).smul_const v`.

Simplify using `using h4`. Establish `e` using `hd.unique h2`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem dual_weight (hG : IsDualFam E G) (μ : Fin n → ℤ) {v : E.V →L[ℂ] ℂ} (hv : v ∈ wtDual E μ) (a : Fin n) :
    G a a v = ((μ a : ℝ) : ℂ) • v := by
  have hX : (Matrix.single a a Complex.I)ᴴ = -(Matrix.single a a Complex.I) := by
    rw [single_conjT, Complex.star_def, Complex.conj_I, single_negI]
  have hd := hG.2 _ (expU _ hX) hX (fun _ => rfl) v
  rw [sum_single_dual] at hd
  have hk : ∀ s : ℝ, (expU _ hX s).1 = diagonal (fun c => if c = a then Complex.exp (s * Complex.I) else 1) := by
    intro s
    have e : (s : ℂ) • (Matrix.single a a Complex.I : Matrix (Fin n) (Fin n) ℂ) =
        diagonal (fun c => if c = a then (s : ℂ) * Complex.I else 0) := by
      ext i j
      by_cases hij : i = j
      · subst hij
        by_cases hc : i = a
        · subst hc
          simp
        · simp [Matrix.single_apply, hc, Ne.symm hc]
      · rw [Matrix.diagonal_apply_ne _ hij, Matrix.smul_apply, Matrix.single_apply,
          if_neg (fun hh => hij (hh.1.symm.trans hh.2)), smul_zero]
    show NormedSpace.exp _ = _
    rw [e, Matrix.exp_diagonal]
    congr 1
    funext c
    split_ifs with hc <;> simp [hc, Complex.exp_eq_exp_ℂ]
  have hf : (fun s : ℝ => v ∘L E.ρ (expU _ hX s)⁻¹) =
      fun s : ℝ => Complex.exp ((s : ℂ) * (Complex.I * ((μ a : ℝ) : ℂ))) • v := by
    funext s
    rw [hv _ _ (hk s), Finset.prod_eq_single a]
    · simp only [if_true]
      rw [← Complex.exp_int_mul]
      congr 2
      push_cast
      ring
    · intro c _ hc
      simp [hc]
    · simp
  rw [hf] at hd
  have h2 : HasDerivAt (fun s : ℝ => Complex.exp ((s : ℂ) * (Complex.I * ((μ a : ℝ) : ℂ))) • v)
      ((Complex.I * ((μ a : ℝ) : ℂ)) • v) 0 := by
    have h3 : HasDerivAt (fun y : ℂ => Complex.exp (y * (Complex.I * ((μ a : ℝ) : ℂ))))
        (Complex.exp ((0 : ℂ) * (Complex.I * ((μ a : ℝ) : ℂ))) * (1 * (Complex.I * ((μ a : ℝ) : ℂ)))) 0 :=
      ((hasDerivAt_id (0 : ℂ)).mul_const _).cexp
    have h4 := (h3.comp_ofReal).smul_const v
    simpa using h4
  have e := hd.unique h2
  calc G a a v = (-Complex.I) • (Complex.I • G a a v) := by rw [smul_smul]; simp
    _ = ((μ a : ℝ) : ℂ) • v := by rw [e, smul_smul, ← mul_assoc]; simp

/- English proof (translation)
Take `⟨e, ρ', -, hi, he⟩` from `GlobalTheory.T.unitary_euclidean_model E`. Establish `hin : ∀ k x y, ⟪ρ' k x, ρ' k y⟫_ℂ = ⟪x, y⟫_ℂ` using `fun k x y => (LinearIsometry.mk (ρ' k).toLinearMap (hi k)).inner_map_map x y`. Set `Ke` to `K.map e.toLinearMap`. Use `⟨Keᗮ.comap e.toLinearMap, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `k ξ hξ`.

Use `(Submodule.mem_orthogonal _ _).2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨η, hη, rfl⟩`. Establish `hξ' : e ξ ∈ Keᗮ` using `hξ`. Establish `h1 : e (ξ ∘L E.ρ k⁻¹) = ρ' k (e ξ)` using `he k ξ`. Establish `h2 : e η = ρ' k (e (η ∘L E.ρ k⁻¹⁻¹))`.

Rewrite using `[he k⁻¹ η, ← ContinuousLinearMap.mul_apply, ← map_mul, mul_inv_cancel, map_one]`. Both sides reduce to the same expression. Use `show ⟪e η, e (ξ ∘L E.ρ k⁻¹)⟫_ℂ = 0`. Rewrite using `[h1, h2, hin]`. Conclude with `(Submodule.mem_orthogonal _ _).1 hξ' _ ⟨_, hK k⁻¹ η hη, rfl⟩`.

Introduce `x hx hx'`. Establish `h1 : e x ∈ Keᗮ` using `hx'`. Establish `h2` using `(Submodule.mem_orthogonal _ _).1 h1 (e x) ⟨x, hx, rfl⟩`. Establish `h3 : e x = 0` using `inner_self_eq_zero.1 h2`. Simplify using `using h3`.

Introduce `ξ`. Take `⟨p, ⟨x, hx, hxp⟩, q, hq, hpq⟩` from `Ke.exists_add_mem_mem_orthogonal (e ξ)`. Use `⟨x, hx, e.symm q, ?_, ?_⟩` and prove the remaining obligations. Use `show e (e.symm q) ∈ Keᗮ`. Simplify using `using hq`.

Apply `e.injective` to reduce the goal to its premises. Rewrite using `[map_add, e.apply_symm_apply, hpq, ← hxp]`. Both sides reduce to the same expression.
-/
theorem exists_stable_compl (E : KMod n) (K : Submodule ℂ (E.V →L[ℂ] ℂ)) (hK : ∀ k, ∀ ξ ∈ K, ξ ∘L E.ρ k⁻¹ ∈ K) :
    ∃ N : Submodule ℂ (E.V →L[ℂ] ℂ), (∀ k, ∀ ξ ∈ N, ξ ∘L E.ρ k⁻¹ ∈ N) ∧ (∀ x ∈ K, x ∈ N → x = 0) ∧
      ∀ ξ, ∃ x ∈ K, ∃ y ∈ N, ξ = x + y := by
  obtain ⟨e, ρ', -, hi, he⟩ := GlobalTheory.T.unitary_euclidean_model E
  have hin : ∀ k x y, ⟪ρ' k x, ρ' k y⟫_ℂ = ⟪x, y⟫_ℂ := fun k x y =>
    (LinearIsometry.mk (ρ' k).toLinearMap (hi k)).inner_map_map x y
  let Ke := K.map e.toLinearMap
  refine ⟨Keᗮ.comap e.toLinearMap, ?_, ?_, ?_⟩
  · intro k ξ hξ
    refine (Submodule.mem_orthogonal _ _).2 ?_
    rintro _ ⟨η, hη, rfl⟩
    have hξ' : e ξ ∈ Keᗮ := hξ
    have h1 : e (ξ ∘L E.ρ k⁻¹) = ρ' k (e ξ) := he k ξ
    have h2 : e η = ρ' k (e (η ∘L E.ρ k⁻¹⁻¹)) := by
      rw [he k⁻¹ η, ← ContinuousLinearMap.mul_apply, ← map_mul, mul_inv_cancel, map_one]
      rfl
    show ⟪e η, e (ξ ∘L E.ρ k⁻¹)⟫_ℂ = 0
    rw [h1, h2, hin]
    exact (Submodule.mem_orthogonal _ _).1 hξ' _ ⟨_, hK k⁻¹ η hη, rfl⟩
  · intro x hx hx'
    have h1 : e x ∈ Keᗮ := hx'
    have h2 := (Submodule.mem_orthogonal _ _).1 h1 (e x) ⟨x, hx, rfl⟩
    have h3 : e x = 0 := inner_self_eq_zero.1 h2
    simpa using h3
  · intro ξ
    obtain ⟨p, ⟨x, hx, hxp⟩, q, hq, hpq⟩ := Ke.exists_add_mem_mem_orthogonal (e ξ)
    refine ⟨x, hx, e.symm q, ?_, ?_⟩
    · show e (e.symm q) ∈ Keᗮ
      simpa using hq
    · apply e.injective
      rw [map_add, e.apply_symm_apply, hpq, ← hxp]
      rfl

end Dual

section Main

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/- English proof (translation)
Establish `hg` using `gl_kF hP`. Establish `hfd : FiniteDimensional ℂ (LinearMap.range t)` using `inferInstance`. Establish `hσ : ∀ k, ∀ w ∈ LinearMap.range t, σ k w ∈ LinearMap.range t`. Introduce and unpack `k _ ⟨ξ, rfl⟩`. Conclude with `⟨_, ht k ξ⟩`.

Establish `hst : ∀ a b, ∀ w ∈ LinearMap.range t, kF E1 E2 a b w ∈ LinearMap.range t` using `fun a b w hw => entry_mem hK _ hσ a b hw`. Establish `hwt : ∀ μ, ∀ ξ ∈ wtDual E μ, ∀ a, kF E1 E2 a a (t ξ) = ((μ a : ℝ) : ℂ) • t ξ`. Introduce `μ ξ hξ a`. Use `weight_of_torus hK μ (fun k z hk => ?_) a` and prove the remaining obligations. Rewrite using `[← ht k ξ, hξ k z hk, map_smul]`.

Set `W : Set (Fin n → ℤ)` to `{μ | ∃ ξ ∈ wtDual E μ, t ξ ≠ 0}`. Establish `hWfin : W.Finite`. Establish `hfa : ∀ a, Set.Finite {m : ℤ | Module.End.HasEigenvalue (((kF E1 E2 a a).restrict (hst a a) : Module.End ℂ (LinearMap.range t))) ((m : ℝ) : ℂ)}` using `fun a => (Module.End.finite_hasEigenvalue _).preimage (Function.Injective.injOn (fun x y h => by simpa using h))`. Use `(Set.Finite.pi' hfa).subset ?_` and prove the remaining obligations. Introduce and unpack `μ ⟨ξ, hξ, h0⟩ a`.

Conclude with `Module.End.hasEigenvalue_of_hasEigenvector (x := ⟨t ξ, ⟨ξ, rfl⟩⟩) ⟨Module.End.mem_eigenspace_iff.2 (Subtype.ext (hwt μ ξ hξ a)), fun h => h0 (congrArg Subtype.val h)⟩`. Establish `hWne : W.Nonempty`. Assume the negation of the conclusion as `hne`. Apply `ht0` to reduce the goal to its premises. Establish `hall : ∀ μ, wtDual E μ ≤ LinearMap.ker t`.

Introduce `μ ξ hξ`. Assume the negation of the conclusion as `h`. Conclude with `hne ⟨μ, ξ, hξ, h⟩`. Conclude with `LinearMap.ker_eq_top.1 (top_le_iff.1 (htop ▸ iSup_le hall))`. Take `⟨μ, hμ, hmax⟩` from `hWfin.toFinset.exists_max_image (fun ν => toLex ν) (by simpa using hWne)`.

Take `⟨ξ, hξ, hv⟩` from `hWfin.mem_toFinset.1 hμ`. Establish `key : ∀ a b : Fin n, a < b → kF E1 E2 a b (t ξ) = 0`. Introduce `a b hab`. Set `μ' : Fin n → ℤ` to `fun c => μ c + (if c = a then 1 else 0) - (if c = b then 1 else 0)`. Establish `hlt : toLex μ < toLex μ'`.

Use `⟨a, fun j hj => ?_, ?_⟩` and prove the remaining obligations. Establish `h1 : j ≠ a` using `ne_of_lt hj`. Establish `h2 : j ≠ b` using `ne_of_lt (lt_trans hj hab)`. Use `show μ j = μ j + (if j = a then 1 else 0) - (if j = b then 1 else 0)`. Simplify using `[h1, h2]`.

Use `show μ a < μ a + (if a = a then 1 else 0) - (if a = b then 1 else 0)`. Simplify using `[ne_of_lt hab]`. Establish `hnot : μ' ∉ W` using `fun h => not_le.2 hlt (hmax μ' (hWfin.mem_toFinset.2 h))`. Establish `hw' : kF E1 E2 a b (t ξ) ∈ jt (kF E1 E2) (wtC μ')` using `mem_jt fun c => weight_shift hg μ (hwt μ ξ hξ) (ne_of_lt hab) c`. Establish `hR : LinearMap.range t ≤ ⨆ (j) (_ : j ≠ wtC μ'), jt (kF E1 E2) j`.

Rewrite using `[LinearMap.range_eq_map, ← htop, Submodule.map_iSup]`. Use `iSup_le fun ν => ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨ζ, hζ, rfl⟩`. Distinguish the cases in `hν : ν = μ'`. Establish `h0 : t ζ = 0`.

Assume the negation of the conclusion as `h`. Conclude with `hnot ⟨ζ, hν ▸ hζ, h⟩`. Rewrite using `[h0]`. Conclude with `zero_mem _`. Conclude with `Submodule.mem_iSup_of_mem (wtC ν) (Submodule.mem_iSup_of_mem (fun h => hν (wtC_injective h)) (mem_jt fun c => hwt ν ζ hζ c))`.

Conclude with `Submodule.disjoint_def.1 (jt_indep hg (wtC μ')) _ hw' (hR (hst a b _ ⟨ξ, rfl⟩))`. Conclude with `⟨μ, ξ, hξ, hv, fun a => hwt μ ξ hξ a, fun a b hab _ => key a b hab⟩`.
-/
theorem exists_hw_image (E1 E2 : Fin n → Fin n → Module.End ℂ V)
    (σ : Matrix.unitaryGroup (Fin n) ℂ →* (V →ₗ[ℂ] V)) (hP : IsPair E1 E2) (hK : IsDerivK σ (kF E1 E2))
    (E : KMod n) (htop : (⨆ μ, wtDual E μ) = ⊤) (t : (E.V →L[ℂ] ℂ) →ₗ[ℂ] V) (ht : t ∈ invA σ E) (ht0 : t ≠ 0) :
    ∃ (μ : Fin n → ℤ) (ξ : E.V →L[ℂ] ℂ), ξ ∈ wtDual E μ ∧ t ξ ≠ 0 ∧ t ξ ∈ hwSp E1 E2 (wtR μ) := by
  have hg := gl_kF hP
  have hfd : FiniteDimensional ℂ (LinearMap.range t) := inferInstance
  have hσ : ∀ k, ∀ w ∈ LinearMap.range t, σ k w ∈ LinearMap.range t := by
    rintro k _ ⟨ξ, rfl⟩
    exact ⟨_, ht k ξ⟩
  have hst : ∀ a b, ∀ w ∈ LinearMap.range t, kF E1 E2 a b w ∈ LinearMap.range t :=
    fun a b w hw => entry_mem hK _ hσ a b hw
  have hwt : ∀ μ, ∀ ξ ∈ wtDual E μ, ∀ a, kF E1 E2 a a (t ξ) = ((μ a : ℝ) : ℂ) • t ξ := by
    intro μ ξ hξ a
    refine weight_of_torus hK μ (fun k z hk => ?_) a
    rw [← ht k ξ, hξ k z hk, map_smul]
  let W : Set (Fin n → ℤ) := {μ | ∃ ξ ∈ wtDual E μ, t ξ ≠ 0}
  have hWfin : W.Finite := by
    have hfa : ∀ a, Set.Finite {m : ℤ |
        Module.End.HasEigenvalue (((kF E1 E2 a a).restrict (hst a a) : Module.End ℂ (LinearMap.range t)))
          ((m : ℝ) : ℂ)} := fun a =>
      (Module.End.finite_hasEigenvalue _).preimage
        (Function.Injective.injOn (fun x y h => by simpa using h))
    refine (Set.Finite.pi' hfa).subset ?_
    rintro μ ⟨ξ, hξ, h0⟩ a
    exact Module.End.hasEigenvalue_of_hasEigenvector (x := ⟨t ξ, ⟨ξ, rfl⟩⟩)
      ⟨Module.End.mem_eigenspace_iff.2 (Subtype.ext (hwt μ ξ hξ a)), fun h => h0 (congrArg Subtype.val h)⟩
  have hWne : W.Nonempty := by
    by_contra hne
    apply ht0
    have hall : ∀ μ, wtDual E μ ≤ LinearMap.ker t := by
      intro μ ξ hξ
      by_contra h
      exact hne ⟨μ, ξ, hξ, h⟩
    exact LinearMap.ker_eq_top.1 (top_le_iff.1 (htop ▸ iSup_le hall))
  obtain ⟨μ, hμ, hmax⟩ := hWfin.toFinset.exists_max_image (fun ν => toLex ν) (by simpa using hWne)
  obtain ⟨ξ, hξ, hv⟩ := hWfin.mem_toFinset.1 hμ
  have key : ∀ a b : Fin n, a < b → kF E1 E2 a b (t ξ) = 0 := by
    intro a b hab
    let μ' : Fin n → ℤ := fun c => μ c + (if c = a then 1 else 0) - (if c = b then 1 else 0)
    have hlt : toLex μ < toLex μ' := by
      refine ⟨a, fun j hj => ?_, ?_⟩
      · have h1 : j ≠ a := ne_of_lt hj
        have h2 : j ≠ b := ne_of_lt (lt_trans hj hab)
        show μ j = μ j + (if j = a then 1 else 0) - (if j = b then 1 else 0)
        simp [h1, h2]
      · show μ a < μ a + (if a = a then 1 else 0) - (if a = b then 1 else 0)
        simp [ne_of_lt hab]
    have hnot : μ' ∉ W := fun h => not_le.2 hlt (hmax μ' (hWfin.mem_toFinset.2 h))
    have hw' : kF E1 E2 a b (t ξ) ∈ jt (kF E1 E2) (wtC μ') :=
      mem_jt fun c => weight_shift hg μ (hwt μ ξ hξ) (ne_of_lt hab) c
    have hR : LinearMap.range t ≤ ⨆ (j) (_ : j ≠ wtC μ'), jt (kF E1 E2) j := by
      rw [LinearMap.range_eq_map, ← htop, Submodule.map_iSup]
      refine iSup_le fun ν => ?_
      rintro _ ⟨ζ, hζ, rfl⟩
      by_cases hν : ν = μ'
      · have h0 : t ζ = 0 := by
          by_contra h
          exact hnot ⟨ζ, hν ▸ hζ, h⟩
        rw [h0]
        exact zero_mem _
      · exact Submodule.mem_iSup_of_mem (wtC ν) (Submodule.mem_iSup_of_mem
          (fun h => hν (wtC_injective h)) (mem_jt fun c => hwt ν ζ hζ c))
    exact Submodule.disjoint_def.1 (jt_indep hg (wtC μ')) _ hw' (hR (hst a b _ ⟨ξ, rfl⟩))
  exact ⟨μ, ξ, hξ, hv, fun a => hwt μ ξ hξ a, fun a b hab _ => key a b hab⟩

/- English proof (translation)
Introduce `n V _ _ E1 E2 σ hP hK E G hG htop M hM t ht hzero`. Assume the negation of the conclusion as `ht0`. Take `⟨μ, ξ, hξ, hv, hhw⟩` from `exists_hw_image E1 E2 σ hP hK E htop t ht ht0`. Establish `hKs : ∀ k, ∀ η ∈ LinearMap.ker t, η ∘L E.ρ k⁻¹ ∈ LinearMap.ker t`. Introduce `k η hη`.

Rewrite `hη`, the goal using `[LinearMap.mem_ker]`. Rewrite using `[ht k η, hη, map_zero]`. Take `⟨N, hNs, hdisj, hsum⟩` from `exists_stable_compl E (LinearMap.ker t) hKs`. Take `⟨x, hx, y, hy, hxy⟩` from `hsum ξ`. Establish `hty : t y = t ξ`.

Rewrite using `[hxy, map_add, LinearMap.mem_ker.1 hx, zero_add]`. Establish `hyw : y ∈ wtDual E μ`. Introduce `k z hk`. Establish `h1` using `hξ k z hk`. Rewrite `h1` using `[hxy, ContinuousLinearMap.add_comp, smul_add]`.

Use `set c : ℂ := ∏ a, z a ^ μ a`. Establish `hx1 : x ∘L E.ρ k⁻¹ - c • x ∈ LinearMap.ker t` using `sub_mem (hKs k x hx) (Submodule.smul_mem _ _ hx)`. Establish `hy1 : y ∘L E.ρ k⁻¹ - c • y ∈ N` using `sub_mem (hNs k y hy) (Submodule.smul_mem _ _ hy)`. Establish `e : y ∘L E.ρ k⁻¹ - c • y = -(x ∘L E.ρ k⁻¹ - c • x)`. Rewrite using `[neg_sub, sub_eq_sub_iff_add_eq_add, add_comm, h1, add_comm]`.

Establish `h0` using `hdisj _ (by rw [e]; exact neg_mem hx1) hy1`. Conclude with `sub_eq_zero.1 h0`. Establish `hyh : y ∈ hwOf G (wtR μ)`. Use `⟨fun a => dual_weight hG μ hyw a, fun a b hab _ => ?_⟩` and prove the remaining obligations. Use `hdisj _ ?_ (dual_entry_mem hG N hNs a b hy)` and prove the remaining obligations.

Rewrite using `[LinearMap.mem_ker, GlobalTheory.T.invariant_intertwines_dual V σ (kF E1 E2) hK E G hG t ht a b y, hty]`. Conclude with `hhw.2 a b hab rfl`. Establish `hne : wtDual E μ ≠ ⊥`. Introduce `h`. Establish `h0 : y = 0` using `(Submodule.mem_bot ℂ).1 (h ▸ hyw)`.

Conclude with `hv (by rw [← hty, h0, map_zero])`. Conclude with `hv (by rw [← hty]; exact hzero μ (hM μ (t ξ) hv hhw hne) y hyh)`.
-/
theorem eq_zero_of_hw : ∀ {n : ℕ} (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (E1 E2 : Fin n → Fin n → Module.End ℂ V) (σ : Matrix.unitaryGroup (Fin n) ℂ →* (V →ₗ[ℂ] V)), IsPair E1 E2 →
    IsDerivK σ (kF E1 E2) → ∀ (E : KMod n) (G : Fin n → Fin n → Module.End ℂ (E.V →L[ℂ] ℂ)), IsDualFam E G →
    (⨆ μ, wtDual E μ) = ⊤ → ∀ M : Finset (Fin n → ℤ),
    (∀ (ν : Fin n → ℤ) (v : V), v ≠ 0 → v ∈ hwSp E1 E2 (wtR ν) → wtDual E ν ≠ ⊥ → ν ∈ M) →
    ∀ t ∈ invA σ E, (∀ μ ∈ M, ∀ ξ ∈ hwOf G (wtR μ), t ξ = 0) → t = 0 := by
  intro n V _ _ E1 E2 σ hP hK E G hG htop M hM t ht hzero
  by_contra ht0
  obtain ⟨μ, ξ, hξ, hv, hhw⟩ := exists_hw_image E1 E2 σ hP hK E htop t ht ht0
  have hKs : ∀ k, ∀ η ∈ LinearMap.ker t, η ∘L E.ρ k⁻¹ ∈ LinearMap.ker t := by
    intro k η hη
    rw [LinearMap.mem_ker] at hη ⊢
    rw [ht k η, hη, map_zero]
  obtain ⟨N, hNs, hdisj, hsum⟩ := exists_stable_compl E (LinearMap.ker t) hKs
  obtain ⟨x, hx, y, hy, hxy⟩ := hsum ξ
  have hty : t y = t ξ := by
    rw [hxy, map_add, LinearMap.mem_ker.1 hx, zero_add]
  have hyw : y ∈ wtDual E μ := by
    intro k z hk
    have h1 := hξ k z hk
    rw [hxy, ContinuousLinearMap.add_comp, smul_add] at h1
    set c : ℂ := ∏ a, z a ^ μ a
    have hx1 : x ∘L E.ρ k⁻¹ - c • x ∈ LinearMap.ker t := sub_mem (hKs k x hx) (Submodule.smul_mem _ _ hx)
    have hy1 : y ∘L E.ρ k⁻¹ - c • y ∈ N := sub_mem (hNs k y hy) (Submodule.smul_mem _ _ hy)
    have e : y ∘L E.ρ k⁻¹ - c • y = -(x ∘L E.ρ k⁻¹ - c • x) := by
      rw [neg_sub, sub_eq_sub_iff_add_eq_add, add_comm, h1, add_comm]
    have h0 := hdisj _ (by rw [e]; exact neg_mem hx1) hy1
    exact sub_eq_zero.1 h0
  have hyh : y ∈ hwOf G (wtR μ) := by
    refine ⟨fun a => dual_weight hG μ hyw a, fun a b hab _ => ?_⟩
    refine hdisj _ ?_ (dual_entry_mem hG N hNs a b hy)
    rw [LinearMap.mem_ker, GlobalTheory.T.invariant_intertwines_dual V σ (kF E1 E2) hK E G hG t ht a b y, hty]
    exact hhw.2 a b hab rfl
  have hne : wtDual E μ ≠ ⊥ := by
    intro h
    have h0 : y = 0 := (Submodule.mem_bot ℂ).1 (h ▸ hyw)
    exact hv (by rw [← hty, h0, map_zero])
  exact hv (by rw [← hty]; exact hzero μ (hM μ (t ξ) hv hhw hne) y hyh)

end Main

end GlobalTheory.CompanionTheory.RealCountG.InjG
