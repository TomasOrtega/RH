import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.DvdTraceOfBalancedTensor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormEigenvalueLeOneOfIntegralMatrixUltrametricStatement

open MvPolynomial Matrix

namespace GlobalTheory.MaxIdealJointEigen

/- English proof (translation)
Establish `stab : ∀ (s : Finset (I → K)) (i : I), ∀ u ∈ ⨆ y ∈ s, V y, h i u ∈ ⨆ y ∈ s, V y`. Introduce `s i`. Establish `: (⨆ y ∈ s, V y) ≤ (⨆ y ∈ s, V y).comap (h i)`. Use `iSup₂_le fun y hy v hv => ?_` and prove the remaining obligations. Rewrite using `[Submodule.mem_comap, hV y v hv i]`.

Conclude with `Submodule.smul_mem _ _ ((le_iSup₂_of_le (f := fun y (_ : y ∈ s) => V y) y hy le_rfl) hv)`. Conclude with `fun u hu => this hu`. Establish `key : ∀ (x : I → K) (s : Finset (I → K)), x ∉ s → ∀ v ∈ V x, v ∈ (⨆ y ∈ s, V y) → v = 0`. Introduce `x s`. Proceed by induction on `s using Finset.induction_on with`.

Consider the case `empty => intro _ v _ hv`. Simplify using `using hv`. Consider the case `insert y s hy ih`. Introduce `hx v hvx hv`. Rewrite `hx` using `[Finset.mem_insert, not_or]`.

Rewrite `hv` using `[Finset.iSup_insert, Submodule.mem_sup]`. Take `⟨w, hw, u, hu, hsum⟩` from `hv`. Take `⟨i, hi⟩` from `Function.ne_iff.mp hx.1`. Establish `e : (x i - y i) • v = h i u - y i • u`. Rewrite using `[sub_smul, ← hV x v hvx i, ← hsum, map_add, hV y w hw i, smul_add]`.

Normalize the expressions using the abelian group laws. Establish `h0` using `ih hx.2 ((x i - y i) • v) (Submodule.smul_mem _ _ hvx) (e ▸ Submodule.sub_mem _ (stab s i u hu) (Submodule.smul_mem _ _ hu))`. Conclude with `(smul_eq_zero.mp h0).resolve_left (sub_ne_zero.mpr hi)`. Introduce `x`. Rewrite using `[Submodule.disjoint_def]`.

Introduce `v hvx hv`. Use `replace hv : v ∈ ⨆ y : {y : I → K // y ≠ x}, V y.1 := by rwa [iSup_subtype]`. Take `⟨s, hs⟩` from `Submodule.mem_iSup_iff_exists_finset.mp hv`. Use `key x (s.image Subtype.val) ?_ v hvx ?_` and prove the remaining obligations. Introduce `hx`.

Take `⟨⟨y, hy⟩, -, e⟩` from `Finset.mem_image.mp hx`. Conclude with `hy e`. Use `(iSup₂_le fun y hy => ?_ : (⨆ y ∈ s, V y.1) ≤ _) hs` and prove the remaining obligations. Conclude with `le_iSup₂_of_le (f := fun y (_ : y ∈ s.image Subtype.val) => V y) y.1 (Finset.mem_image_of_mem _ hy) le_rfl`.
-/
theorem iSupIndep_of_joint_eigen {K E I : Type} [Field K] [AddCommGroup E] [Module K E]
    (h : I → Module.End K E) (V : (I → K) → Submodule K E)
    (hV : ∀ x, ∀ v ∈ V x, ∀ i, h i v = x i • v) : iSupIndep V := by
  classical
  have stab : ∀ (s : Finset (I → K)) (i : I), ∀ u ∈ ⨆ y ∈ s, V y, h i u ∈ ⨆ y ∈ s, V y := by
    intro s i
    have : (⨆ y ∈ s, V y) ≤ (⨆ y ∈ s, V y).comap (h i) := by
      refine iSup₂_le fun y hy v hv => ?_
      rw [Submodule.mem_comap, hV y v hv i]
      exact Submodule.smul_mem _ _ ((le_iSup₂_of_le (f := fun y (_ : y ∈ s) => V y) y hy le_rfl) hv)
    exact fun u hu => this hu
  have key : ∀ (x : I → K) (s : Finset (I → K)), x ∉ s → ∀ v ∈ V x, v ∈ (⨆ y ∈ s, V y) → v = 0 := by
    intro x s
    induction s using Finset.induction_on with
    | empty => intro _ v _ hv; simpa using hv
    | insert y s hy ih =>
      intro hx v hvx hv
      rw [Finset.mem_insert, not_or] at hx
      rw [Finset.iSup_insert, Submodule.mem_sup] at hv
      obtain ⟨w, hw, u, hu, hsum⟩ := hv
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hx.1
      have e : (x i - y i) • v = h i u - y i • u := by
        rw [sub_smul, ← hV x v hvx i, ← hsum, map_add, hV y w hw i, smul_add]; abel
      have h0 := ih hx.2 ((x i - y i) • v) (Submodule.smul_mem _ _ hvx)
        (e ▸ Submodule.sub_mem _ (stab s i u hu) (Submodule.smul_mem _ _ hu))
      exact (smul_eq_zero.mp h0).resolve_left (sub_ne_zero.mpr hi)
  intro x
  rw [Submodule.disjoint_def]
  intro v hvx hv
  replace hv : v ∈ ⨆ y : {y : I → K // y ≠ x}, V y.1 := by rwa [iSup_subtype]
  obtain ⟨s, hs⟩ := Submodule.mem_iSup_iff_exists_finset.mp hv
  refine key x (s.image Subtype.val) ?_ v hvx ?_
  · intro hx
    obtain ⟨⟨y, hy⟩, -, e⟩ := Finset.mem_image.mp hx
    exact hy e
  · refine (iSup₂_le fun y hy => ?_ : (⨆ y ∈ s, V y.1) ≤ _) hs
    exact le_iSup₂_of_le (f := fun y (_ : y ∈ s.image Subtype.val) => V y) y.1
      (Finset.mem_image_of_mem _ hy) le_rfl

/- English proof (translation)
Set `V : (I → K) → Submodule K (Fin n → K)` to `fun θ => ⨅ i, Module.End.eigenspace (Matrix.toLin' (T i)) (θ i)`. Establish `hV : ∀ x, ∀ v ∈ V x, ∀ i, Matrix.toLin' (T i) v = x i • v`. Introduce `x v hv i`. Use `(Submodule.mem_iInf _).mp hv i` as an intermediate fact. Conclude with `Module.End.mem_eigenspace_iff.mp this`.

Establish `hind` using `iSupIndep_of_joint_eigen (fun i => Matrix.toLin' (T i)) V hV`. Establish `hfin : Finite {θ // V θ ≠ ⊥}` using `by haveI := hind.fintypeNeBotOfFiniteDimensional infer_instance`. Use `(Set.finite_coe_iff.mp hfin).subset ?_` and prove the remaining obligations. Introduce and unpack `θ ⟨c, hc0, hc⟩`. Use `show V θ ≠ ⊥`.

Rewrite using `[Submodule.ne_bot_iff]`. Use `⟨c, (Submodule.mem_iInf _).mpr fun i => ?_, hc0⟩` and prove the remaining obligations. Rewrite using `[Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]`. Conclude with `hc i`.
-/
theorem finite_joint_eigen {K I : Type} [Field K] {n : ℕ} (T : I → Matrix (Fin n) (Fin n) K) :
    {θ : I → K | ∃ c : Fin n → K, c ≠ 0 ∧ ∀ i, (T i).mulVec c = θ i • c}.Finite := by
  classical
  let V : (I → K) → Submodule K (Fin n → K) := fun θ =>
    ⨅ i, Module.End.eigenspace (Matrix.toLin' (T i)) (θ i)
  have hV : ∀ x, ∀ v ∈ V x, ∀ i, Matrix.toLin' (T i) v = x i • v := by
    intro x v hv i
    have := (Submodule.mem_iInf _).mp hv i
    exact Module.End.mem_eigenspace_iff.mp this
  have hind := iSupIndep_of_joint_eigen (fun i => Matrix.toLin' (T i)) V hV
  have hfin : Finite {θ // V θ ≠ ⊥} := by
    haveI := hind.fintypeNeBotOfFiniteDimensional
    infer_instance
  refine (Set.finite_coe_iff.mp hfin).subset ?_
  rintro θ ⟨c, hc0, hc⟩
  show V θ ≠ ⊥
  rw [Submodule.ne_bot_iff]
  refine ⟨c, (Submodule.mem_iInf _).mpr fun i => ?_, hc0⟩
  rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
  exact hc i

/- English proof (translation)
Proceed by induction on `p using MvPolynomial.induction_on with`. Consider the case `C a`. Rewrite using `[← MvPolynomial.algebraMap_eq, AlgHom.commutes, Matrix.algebraMap_eq_diagonal]`. Use extensionality with `j`. Simplify using `[Matrix.mulVec_diagonal]`.

Consider the case `add p q hp hq`. Rewrite using `[map_add, Matrix.map_add _ (map_add emb), Matrix.add_mulVec, hp, hq, eval₂_add, add_smul]`. Consider the case `mul_X p i hp`. Rewrite using `[map_mul, Matrix.map_mul, ← Matrix.mulVec_mulVec, hc, Matrix.mulVec_smul, hp, eval₂_mul, eval₂_X, smul_smul, mul_comm]`.
-/
theorem mulVec_eval₂ {O K I : Type} [CommRing O] [Field K] (emb : O →+* K) {n : ℕ}
    (ρ : MvPolynomial I O →ₐ[O] Matrix (Fin n) (Fin n) O) (θ : I → K) (c : Fin n → K)
    (hc : ∀ i, ((ρ (X i)).map emb).mulVec c = θ i • c) (p : MvPolynomial I O) :
    ((ρ p).map emb).mulVec c = eval₂ emb θ p • c := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes, Matrix.algebraMap_eq_diagonal]
    ext j
    simp [Matrix.mulVec_diagonal]
  | add p q hp hq =>
    rw [map_add, Matrix.map_add _ (map_add emb), Matrix.add_mulVec, hp, hq, eval₂_add, add_smul]
  | mul_X p i hp =>
    rw [map_mul, Matrix.map_mul, ← Matrix.mulVec_mulVec, hc, Matrix.mulVec_smul, hp, eval₂_mul,
      eval₂_X, smul_smul, mul_comm]

end GlobalTheory.MaxIdealJointEigen

namespace GlobalTheory

open MvPolynomial Matrix GlobalTheory.MaxIdealJointEigen

/- English proof (translation)
Introduce `l _ O _ emb h1 hu I n ρ m hm hker`. Use `set K := PadicAlgCl l`. Set `T : I → Matrix (Fin n) (Fin n) K` to `fun i => (ρ (X i)).map emb`. Set `Θ : Set (I → K)` to `{θ | ∃ c : Fin n → K, c ≠ 0 ∧ ∀ i, (T i).mulVec c = θ i • c}`. Establish `hfin : Θ.Finite` using `finite_joint_eigen T`.

Establish `hint : ∀ θ ∈ Θ, ∀ p, ‖eval₂ emb θ p‖ ≤ 1`. Introduce and unpack `θ ⟨c, hc0, hc⟩ p`. Conclude with `GlobalTheory.T.norm_eigenvalue_le_one_of_integral_matrix_ultrametric O K emb h1 n (ρ p) _ c hc0 (mulVec_eval₂ emb ρ θ c hc p)`. Set `J : (I → K) → Ideal (MvPolynomial I O)` to `fun θ => { carrier := {p | ∀ r, ‖eval₂ emb θ (r * p)‖ < 1} add_mem' := by`. Introduce `a b ha hb r`.

Simplify using `only [Set.mem_setOf_eq, mul_add, eval₂_add] at *`. Conclude with `lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt (ha r) (hb r))`. Use the proof step `zero_mem' := by intro r; simp`. Use the proof step `smul_mem' := by`. Introduce `a b hb r`.

Simplify using `only [Set.mem_setOf_eq, smul_eq_mul, ← mul_assoc] at *`. Conclude with `hb (r * a) }`. Establish `hJmem : ∀ θ ∈ Θ, ∀ p, p ∈ J θ ↔ ‖eval₂ emb θ p‖ < 1`. Introduce `θ hθ p`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Simplify using `using h 1`. Introduce `h r show ‖eval₂ emb θ (r * p)‖ < 1`. Rewrite using `[eval₂_mul, norm_mul]`. Conclude with `lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) (hint θ hθ r)) h`.

Establish `hJprime : ∀ θ ∈ Θ, (J θ).IsPrime`. Introduce `θ hθ`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `htop`. Use `(hJmem θ hθ 1).mp (htop ▸ Submodule.mem_top)` as an intermediate fact.

Simplify using `at this`. Introduce `a b hab`. Rewrite `hab` using `[hJmem θ hθ, eval₂_mul, norm_mul]`. Rewrite using `[hJmem θ hθ, hJmem θ hθ]`. Assume the negation of the conclusion as `hc`.

Use `push_neg at hc`. Use `mul_le_mul hc.1 hc.2 zero_le_one (norm_nonneg _)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Distinguish the cases in `hex : ∃ θ ∈ Θ, m ≤ J θ`. Take `⟨θ, hθ, hle⟩` from `hex`.

Establish `heq : m = J θ` using `hm.eq_of_le (hJprime θ hθ).ne_top hle`. Take `⟨c, hc0, hc⟩` from `hθ`. Use `⟨θ, fun i => ?_, fun p => ?_, c, hc0, hc⟩` and prove the remaining obligations. Simplify using `using hint θ ⟨c, hc0, hc⟩ (X i)`. Rewrite using `[heq]`.

Conclude with `hJmem θ ⟨c, hc0, hc⟩ p`. Use `exfalso push_neg at hex`. Establish `hnot : ¬ ((m : Set (MvPolynomial I O)) ⊆ ⋃ θ ∈ (hfin.toFinset : Set (I → K)), (J θ : Set _))`. Rewrite using `[Ideal.subset_union_prime (0 : I → K) (0 : I → K) (fun θ hθ _ _ => hJprime θ (by simpa using hθ))]`. Introduce and unpack `⟨θ, hθ, hle⟩`.

Conclude with `hex θ (by simpa using hθ) hle`. Take `⟨q, hqm, hq⟩` from `Set.not_subset.mp hnot`. Establish `hq1 : ∀ θ ∈ Θ, ‖eval₂ emb θ q‖ = 1`. Introduce `θ hθ`. Use `le_antisymm (hint θ hθ q) (not_lt.mp fun h => hq ?_)` and prove the remaining obligations.

Conclude with `Set.mem_biUnion (x := θ) (by simpa using hθ) ((hJmem θ hθ q).mpr h)`. Set `B : Matrix (Fin n) (Fin n) K` to `(ρ q).map emb`. Establish `hcomm : ∀ p p', ((ρ p).map emb) * ((ρ p').map emb) = ((ρ p').map emb) * ((ρ p).map emb)`. Introduce `p p'`. Rewrite using `[← Matrix.map_mul, ← Matrix.map_mul, ← map_mul, ← map_mul, mul_comm]`.

Establish `hroot : ∀ μ ∈ B.charpoly.roots, ‖μ‖ = 1`. Introduce `μ hμ`. Establish `hdet0 : (Matrix.scalar (Fin n) μ - B).det = 0`. Rewrite using `[← Matrix.eval_charpoly]`. Conclude with `(Polynomial.mem_roots'.mp hμ).2`.

Take `⟨v, hv0, hv⟩` from `Matrix.exists_mulVec_eq_zero_iff.mpr hdet0`. Establish `hsc : ∀ w : Fin n → K, (Matrix.scalar (Fin n) μ) *ᵥ w = μ • w`. Introduce `w`. Use extensionality with `j`. Simplify using `[Matrix.scalar_apply, Matrix.mulVec_diagonal]`.

Establish `hBv : B *ᵥ v = μ • v`. Rewrite `hv` using `[Matrix.sub_mulVec, sub_eq_zero, hsc]`. Conclude with `hv.symm`. Set `W : Submodule K (Fin n → K)` to `Module.End.eigenspace (Matrix.toLin' B) μ`. Establish `hW0 : W ≠ ⊥`.

Rewrite using `[Submodule.ne_bot_iff]`. Use `⟨v, ?_, hv0⟩` and prove the remaining obligations. Rewrite using `[Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]`. Conclude with `hBv`. Establish `hWs : ∀ i, ∀ w ∈ W, Matrix.toLin' (T i) w ∈ W`.

Introduce `i w hw`. Rewrite `hw`, the goal using `[Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]`. Rewrite using `[Matrix.toLin'_apply, Matrix.mulVec_mulVec]`. Express the relevant statement in the definitionally equal form `((ρ q).map emb * (ρ (X i)).map emb) *ᵥ w = μ • ((ρ (X i)).map emb *ᵥ w)`. Rewrite using `[hcomm, ← Matrix.mulVec_mulVec]`.

Express the relevant statement in the definitionally equal form `(ρ (X i)).map emb *ᵥ (B *ᵥ w) = _`. Rewrite using `[hw, Matrix.mulVec_smul]`. Take `⟨c, hcW, hc0, hc⟩` from `GlobalTheory.exists_common_eigenvector_mem (fun i => Matrix.toLin' (T i)) (fun i j w => by`. Simplify using `only [Matrix.toLin'_apply, Matrix.mulVec_mulVec]`. Conclude with `congrArg (· *ᵥ w) (hcomm (X i) (X j))) W hW0 hWs`.

Use `choose θ hθ using hc`. Establish `hθ' : ∀ i, (T i) *ᵥ c = θ i • c` using `fun i => by simpa [Matrix.toLin'_apply] using hθ i`. Establish `hθΘ : θ ∈ Θ` using `⟨c, hc0, hθ'⟩`. Establish `h2` using `mulVec_eval₂ emb ρ θ c hθ' q`. Establish `h3 : B *ᵥ c = μ • c`.

Use `Module.End.mem_eigenspace_iff.mp hcW` as an intermediate fact. Rewrite `this` using `[Matrix.toLin'_apply]`. Then use the resulting hypothesis. Establish `hμ : μ = eval₂ emb θ q`. Establish `e : (μ - eval₂ emb θ q) • c = 0`. Rewrite using `[sub_smul, ← h3, ← h2]`.

Conclude with `sub_self _`. Conclude with `sub_eq_zero.mp ((smul_eq_zero.mp e).resolve_right hc0)`. Rewrite using `[hμ]`. Conclude with `hq1 θ hθΘ`. Establish `hdetB : ‖emb (ρ q).det‖ = 1`.

Rewrite using `[RingHom.map_det, RingHom.mapMatrix_apply, Matrix.det_eq_prod_roots_charpoly]`. Conclude with `Multiset.prod_induction (fun x => ‖x‖ = 1) _ (fun a b ha hb => by rw [norm_mul, ha, hb, one_mul]) norm_one hroot`. Establish `hunit : IsUnit (ρ q).det` using `hu _ hdetB`. Use `set P := (ρ q).charpoly with hPdef`. Establish `hP : Polynomial.aeval q P ∈ m`.

Apply `hker` to reduce the goal to its premises. Rewrite using `[RingHom.mem_ker]`. Rewrite using `[← Polynomial.aeval_algHom_apply, Matrix.aeval_self_charpoly]`. Establish `hC : MvPolynomial.C (P.coeff 0) ∈ m`. Rewrite `hP`, the goal using `[← Ideal.Quotient.eq_zero_iff_mem]`.

Establish `hq0 : Ideal.Quotient.mkₐ O m q = 0`. Rewrite using `[Ideal.Quotient.mkₐ_eq_mk]`. Conclude with `Ideal.Quotient.eq_zero_iff_mem.mpr hqm`. Establish `e` using `Polynomial.aeval_algHom_apply (Ideal.Quotient.mkₐ O m) q P`. Rewrite `e` using `[hq0, ← Polynomial.coeff_zero_eq_aeval_zero']`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← MvPolynomial.algebraMap_eq]`. Use `first`. Consider the case `exact Ideal.Quotient.mk_algebraMap _ _ _`. Consider the case `rfl`.

Use `_ = Ideal.Quotient.mkₐ O m (Polynomial.aeval q P) := e`. Use `_ = 0 := by rw [Ideal.Quotient.mkₐ_eq_mk]; exact hP`. Establish `hu0 : IsUnit (P.coeff 0)`. Rewrite `hunit` using `[Matrix.det_eq_sign_charpoly_coeff]`. Conclude with `isUnit_of_mul_isUnit_right hunit`.

Conclude with `hm.ne_top (Ideal.eq_top_of_isUnit_mem _ hC (hu0.map MvPolynomial.C))`.
-/
theorem maximal_ideal_eq_joint_eigen : ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O]
    (emb : O →+* PadicAlgCl l), (∀ c, ‖emb c‖ ≤ 1) → (∀ c, ‖emb c‖ = 1 → IsUnit c) →
    ∀ (I : Type) (n : ℕ) (ρ : MvPolynomial I O →ₐ[O] Matrix (Fin n) (Fin n) O)
    (m : Ideal (MvPolynomial I O)), m.IsMaximal → RingHom.ker ρ ≤ m →
    ∃ θ : I → PadicAlgCl l, (∀ i, ‖θ i‖ ≤ 1) ∧ (∀ p, p ∈ m ↔ ‖MvPolynomial.eval₂ emb θ p‖ < 1) ∧
      ∃ c : Fin n → PadicAlgCl l, c ≠ 0 ∧
        ∀ i, ((ρ (MvPolynomial.X i)).map emb).mulVec c = θ i • c := by
  intro l _ O _ emb h1 hu I n ρ m hm hker
  classical
  set K := PadicAlgCl l
  let T : I → Matrix (Fin n) (Fin n) K := fun i => (ρ (X i)).map emb
  let Θ : Set (I → K) := {θ | ∃ c : Fin n → K, c ≠ 0 ∧ ∀ i, (T i).mulVec c = θ i • c}
  have hfin : Θ.Finite := finite_joint_eigen T
  have hint : ∀ θ ∈ Θ, ∀ p, ‖eval₂ emb θ p‖ ≤ 1 := by
    rintro θ ⟨c, hc0, hc⟩ p
    exact GlobalTheory.T.norm_eigenvalue_le_one_of_integral_matrix_ultrametric O K emb h1 n (ρ p) _ c hc0 (mulVec_eval₂ emb ρ θ c hc p)

  let J : (I → K) → Ideal (MvPolynomial I O) := fun θ =>
    { carrier := {p | ∀ r, ‖eval₂ emb θ (r * p)‖ < 1}
      add_mem' := by
        intro a b ha hb r
        simp only [Set.mem_setOf_eq, mul_add, eval₂_add] at *
        exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt (ha r) (hb r))
      zero_mem' := by intro r; simp
      smul_mem' := by
        intro a b hb r
        simp only [Set.mem_setOf_eq, smul_eq_mul, ← mul_assoc] at *
        exact hb (r * a) }
  have hJmem : ∀ θ ∈ Θ, ∀ p, p ∈ J θ ↔ ‖eval₂ emb θ p‖ < 1 := by
    intro θ hθ p
    constructor
    · intro h; simpa using h 1
    · intro h r
      show ‖eval₂ emb θ (r * p)‖ < 1
      rw [eval₂_mul, norm_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) (hint θ hθ r)) h
  have hJprime : ∀ θ ∈ Θ, (J θ).IsPrime := by
    intro θ hθ
    refine ⟨?_, ?_⟩
    · intro htop
      have := (hJmem θ hθ 1).mp (htop ▸ Submodule.mem_top)
      simp at this
    · intro a b hab
      rw [hJmem θ hθ, eval₂_mul, norm_mul] at hab
      rw [hJmem θ hθ, hJmem θ hθ]
      by_contra hc
      push_neg at hc
      have := mul_le_mul hc.1 hc.2 zero_le_one (norm_nonneg _)
      linarith
  by_cases hex : ∃ θ ∈ Θ, m ≤ J θ
  · obtain ⟨θ, hθ, hle⟩ := hex
    have heq : m = J θ := hm.eq_of_le (hJprime θ hθ).ne_top hle
    obtain ⟨c, hc0, hc⟩ := hθ
    refine ⟨θ, fun i => ?_, fun p => ?_, c, hc0, hc⟩
    · simpa using hint θ ⟨c, hc0, hc⟩ (X i)
    · rw [heq]; exact hJmem θ ⟨c, hc0, hc⟩ p
  · exfalso
    push_neg at hex
    have hnot : ¬ ((m : Set (MvPolynomial I O)) ⊆ ⋃ θ ∈ (hfin.toFinset : Set (I → K)), (J θ : Set _)) := by
      rw [Ideal.subset_union_prime (0 : I → K) (0 : I → K)
        (fun θ hθ _ _ => hJprime θ (by simpa using hθ))]
      rintro ⟨θ, hθ, hle⟩
      exact hex θ (by simpa using hθ) hle
    obtain ⟨q, hqm, hq⟩ := Set.not_subset.mp hnot
    have hq1 : ∀ θ ∈ Θ, ‖eval₂ emb θ q‖ = 1 := by
      intro θ hθ
      refine le_antisymm (hint θ hθ q) (not_lt.mp fun h => hq ?_)
      exact Set.mem_biUnion (x := θ) (by simpa using hθ) ((hJmem θ hθ q).mpr h)
    let B : Matrix (Fin n) (Fin n) K := (ρ q).map emb
    have hcomm : ∀ p p', ((ρ p).map emb) * ((ρ p').map emb) = ((ρ p').map emb) * ((ρ p).map emb) := by
      intro p p'
      rw [← Matrix.map_mul, ← Matrix.map_mul, ← map_mul, ← map_mul, mul_comm]
    have hroot : ∀ μ ∈ B.charpoly.roots, ‖μ‖ = 1 := by
      intro μ hμ
      have hdet0 : (Matrix.scalar (Fin n) μ - B).det = 0 := by
        rw [← Matrix.eval_charpoly]
        exact (Polynomial.mem_roots'.mp hμ).2
      obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet0
      have hsc : ∀ w : Fin n → K, (Matrix.scalar (Fin n) μ) *ᵥ w = μ • w := by
        intro w; ext j; simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]
      have hBv : B *ᵥ v = μ • v := by
        rw [Matrix.sub_mulVec, sub_eq_zero, hsc] at hv
        exact hv.symm
      let W : Submodule K (Fin n → K) := Module.End.eigenspace (Matrix.toLin' B) μ
      have hW0 : W ≠ ⊥ := by
        rw [Submodule.ne_bot_iff]
        refine ⟨v, ?_, hv0⟩
        rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
        exact hBv
      have hWs : ∀ i, ∀ w ∈ W, Matrix.toLin' (T i) w ∈ W := by
        intro i w hw
        rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply] at hw ⊢
        rw [Matrix.toLin'_apply, Matrix.mulVec_mulVec]
        change ((ρ q).map emb * (ρ (X i)).map emb) *ᵥ w = μ • ((ρ (X i)).map emb *ᵥ w)
        rw [hcomm, ← Matrix.mulVec_mulVec]
        change (ρ (X i)).map emb *ᵥ (B *ᵥ w) = _
        rw [hw, Matrix.mulVec_smul]
      obtain ⟨c, hcW, hc0, hc⟩ := GlobalTheory.exists_common_eigenvector_mem
        (fun i => Matrix.toLin' (T i))
        (fun i j w => by
          simp only [Matrix.toLin'_apply, Matrix.mulVec_mulVec]
          exact congrArg (· *ᵥ w) (hcomm (X i) (X j))) W hW0 hWs
      choose θ hθ using hc
      have hθ' : ∀ i, (T i) *ᵥ c = θ i • c := fun i => by simpa [Matrix.toLin'_apply] using hθ i
      have hθΘ : θ ∈ Θ := ⟨c, hc0, hθ'⟩
      have h2 := mulVec_eval₂ emb ρ θ c hθ' q
      have h3 : B *ᵥ c = μ • c := by
        have := Module.End.mem_eigenspace_iff.mp hcW
        rwa [Matrix.toLin'_apply] at this
      have hμ : μ = eval₂ emb θ q := by
        have e : (μ - eval₂ emb θ q) • c = 0 := by
          rw [sub_smul, ← h3, ← h2]
          exact sub_self _
        exact sub_eq_zero.mp ((smul_eq_zero.mp e).resolve_right hc0)
      rw [hμ]
      exact hq1 θ hθΘ
    have hdetB : ‖emb (ρ q).det‖ = 1 := by
      rw [RingHom.map_det, RingHom.mapMatrix_apply, Matrix.det_eq_prod_roots_charpoly]
      exact Multiset.prod_induction (fun x => ‖x‖ = 1) _
        (fun a b ha hb => by rw [norm_mul, ha, hb, one_mul]) norm_one hroot
    have hunit : IsUnit (ρ q).det := hu _ hdetB
    set P := (ρ q).charpoly with hPdef
    have hP : Polynomial.aeval q P ∈ m := by
      apply hker
      rw [RingHom.mem_ker]
      rw [← Polynomial.aeval_algHom_apply, Matrix.aeval_self_charpoly]
    have hC : MvPolynomial.C (P.coeff 0) ∈ m := by
      rw [← Ideal.Quotient.eq_zero_iff_mem] at hP ⊢
      have hq0 : Ideal.Quotient.mkₐ O m q = 0 := by
        rw [Ideal.Quotient.mkₐ_eq_mk]; exact Ideal.Quotient.eq_zero_iff_mem.mpr hqm
      have e := Polynomial.aeval_algHom_apply (Ideal.Quotient.mkₐ O m) q P
      rw [hq0, ← Polynomial.coeff_zero_eq_aeval_zero'] at e
      calc Ideal.Quotient.mk m (C (P.coeff 0))
          = algebraMap O (MvPolynomial I O ⧸ m) (P.coeff 0) := by
            rw [← MvPolynomial.algebraMap_eq]
            first
              | exact Ideal.Quotient.mk_algebraMap _ _ _
              | rfl
        _ = Ideal.Quotient.mkₐ O m (Polynomial.aeval q P) := e
        _ = 0 := by rw [Ideal.Quotient.mkₐ_eq_mk]; exact hP
    have hu0 : IsUnit (P.coeff 0) := by
      rw [Matrix.det_eq_sign_charpoly_coeff] at hunit
      exact isUnit_of_mul_isUnit_right hunit
    exact hm.ne_top (Ideal.eq_top_of_isUnit_mem _ hC (hu0.map MvPolynomial.C))

end GlobalTheory
