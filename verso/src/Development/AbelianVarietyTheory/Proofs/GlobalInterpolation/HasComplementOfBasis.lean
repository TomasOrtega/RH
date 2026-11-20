import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.UnitVectorOrthogonal
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnramifiedOfIsCMUnram
import Formalism.LocalRingCardinality.SpanPowerMembership.Spaces
import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.LandherrStIffLandherr

noncomputable section

open NumberField Formalism.BasicNotions Formalism.BasicNotions.Examples₂ GlobalTheory.IndefiniteRowSideFullHecke.UnitVectorOrthogonal
open scoped Matrix

namespace GlobalTheory.UnitPerp

def negFrom (N p : ℕ) : Fin N → Bool := fun i => decide (p ≤ (i : ℕ))

/- English proof (translation)
Substitute `h` using the available equality. Establish `hJ : Formalism.UG.Jpq p q = Matrix.diagonal (Sum.elim (fun _ => 1) (fun _ => -1))`. Rewrite using `[← Matrix.fromBlocks_diagonal, Formalism.UG.Jpq, Matrix.diagonal_one, ← Matrix.diagonal_neg, Matrix.diagonal_one]`. Rewrite using `[hJ, Matrix.submatrix_diagonal_equiv]`. Use `congr 1`.

Use function extensionality and compare the values at `a`. Take `⟨s, rfl⟩` from `finSumFinEquiv.surjective a`. Break down `s with s | s` into its components or cases. Establish `: ¬ p ≤ (s : ℕ)` using `not_le.2 s.2`. Simplify using `[negFrom, sgn, this]`.

Simplify using `[negFrom, sgn]`.
-/
theorem jpq_submatrix {r p q : ℕ} (h : r = p + q) :
    (Formalism.UG.Jpq p q).submatrix ((finCongr h).trans finSumFinEquiv.symm)
      ((finCongr h).trans finSumFinEquiv.symm) =
      Matrix.diagonal fun a : Fin r => (sgn (negFrom r p a) : ℂ) := by
  subst h
  have hJ : Formalism.UG.Jpq p q = Matrix.diagonal (Sum.elim (fun _ => 1) (fun _ => -1)) := by
    rw [← Matrix.fromBlocks_diagonal, Formalism.UG.Jpq, Matrix.diagonal_one, ← Matrix.diagonal_neg,
      Matrix.diagonal_one]
  rw [hJ, Matrix.submatrix_diagonal_equiv]
  congr 1
  funext a
  obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective a
  rcases s with s | s
  · have : ¬ p ≤ (s : ℕ) := not_le.2 s.2
    simp [negFrom, sgn, this]
  · simp [negFrom, sgn]

/- English proof (translation)
Rewrite using `[← jpq_submatrix h]`. Use `⟨(finCongr h).trans finSumFinEquiv.symm, 1, ?_⟩` and prove the remaining obligations. Simplify using `only [Units.val_one, Formalism.UG.cT_one, Matrix.one_mul, Matrix.mul_one]`. Use extensionality with `i j`. Simplify using `only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.apply_symm_apply]`.
-/
theorem hasSignature_diagonal {n p q : ℕ} (h : n = p + q) : Formalism.UG.HasSignature
    (Matrix.diagonal fun a : Fin n => (sgn (negFrom n p a) : ℂ)) p q := by
  rw [← jpq_submatrix h]
  refine ⟨(finCongr h).trans finSumFinEquiv.symm, 1, ?_⟩
  simp only [Units.val_one, Formalism.UG.cT_one, Matrix.one_mul, Matrix.mul_one]
  ext i j
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.apply_symm_apply]

section Generic

variable {E : Type} [Field E] [NumberField E] [StarRing E]

/- English proof (translation)
Use `⟨rfl, fun τ => ?_, fun _ => rfl⟩` and prove the remaining obligations. Establish `hg : (stdSpace (E` using `E) star_isIntegral n (negFrom n p) p q).gram.map τ = Matrix.diagonal fun i : Fin n => (sgn (negFrom n p i) : ℂ) := by`. Use extensionality with `i j`. Rewrite using `[Matrix.map_apply]`. Use `(congrArg τ (stdSpace_gram_apply star_isIntegral n (negFrom n p) p q i j)).trans ?_` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `τ (if i = j then (sgn (negFrom n p i) : E) else 0) = if i = j then (sgn (negFrom n p i) : ℂ) else 0`. Apply the tactic sequence `by_cases h : i = j <;> simp [h, map_sgn]`. Rewrite using `[hg]`. Conclude with `hasSignature_diagonal h`.
-/
theorem ofKind_stdSpace {n p q : ℕ} (h : n = p + q) :
    OfKind (stdSpace (E := E) star_isIntegral n (negFrom n p) p q) n p q := by
  refine ⟨rfl, fun τ => ?_, fun _ => rfl⟩
  have hg : (stdSpace (E := E) star_isIntegral n (negFrom n p) p q).gram.map τ =
      Matrix.diagonal fun i : Fin n => (sgn (negFrom n p i) : ℂ) := by
    ext i j
    rw [Matrix.map_apply]
    refine (congrArg τ (stdSpace_gram_apply star_isIntegral n (negFrom n p) p q i j)).trans ?_
    change τ (if i = j then (sgn (negFrom n p i) : E) else 0) =
      if i = j then (sgn (negFrom n p i) : ℂ) else 0
    by_cases h : i = j <;> simp [h, map_sgn]
  rw [hg]
  exact hasSignature_diagonal h

/- English proof (translation)
Take `⟨τ⟩ : Nonempty (E →+* ℂ)` from `inferInstance`. Establish `h0` using `h.2.1 τ`. Rewrite `h0` using `[h.2.2 τ]`. Take `⟨e, -⟩` from `h0`. Use `Fintype.card_congr e` as an intermediate fact.

Simplify `this` using `[h.1]`.
-/
theorem rank_eq_add {W : HSpace E} {M P Q : ℕ} (h : OfKind W M P Q) : M = P + Q := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have h0 := h.2.1 τ
  rw [h.2.2 τ] at h0
  obtain ⟨e, -⟩ := h0
  have := Fintype.card_congr e
  simpa [h.1] using this

/- English proof (translation)
Establish `key : ∀ i v, W.hT (b i) v = sgn (neg i) * b.repr v i`. Introduce `i v`. Use `conv_lhs => rw [← b.sum_repr v]`. Rewrite using `[map_sum, Finset.sum_eq_single i (fun j _ hj => by rw [map_smul, hb, if_neg hj.symm, smul_zero]) (by simp), map_smul, hb, if_pos rfl, smul_eq_mul, mul_comm]`. Establish `hperp : ∀ v, v ∈ perp W (b k) ↔ b.repr v k = 0`.

Introduce `v`. Express the relevant statement in the definitionally equal form `W.hT (b k) v = 0 ↔ _`. Rewrite using `[key, mul_eq_zero, or_iff_right (sgn_ne_zero _)]`. Set `L : Submodule (𝓞 E) W.V` to `Submodule.span (𝓞 E) (Set.range b)`. Establish `hL : ∀ v, v ∈ L ↔ ∀ i, b.repr v i ∈ Set.range (algebraMap (𝓞 E) E)` using `fun v => b.mem_span_iff_repr_mem (𝓞 E) v`.

Establish `hS : ∀ y : Fin n → E, y ∈ stdLat (E` using `E) n ↔ ∀ i, y i ∈ Set.range (algebraMap (𝓞 E) E) := fun y => (Pi.basisFun E (Fin n)).mem_span_iff_repr_mem (𝓞 E) y`. Set `ι : (Fin n → E) →ₗ[E] W.V` to `Fintype.linearCombination E fun i => b (k.succAbove i)`. Establish `hι : ∀ y, ι y = ∑ i, y i • b (k.succAbove i)` using `fun y => Fintype.linearCombination_apply _ _ _`. Establish `hιk : ∀ y, b.repr (ι y) k = 0`. Introduce `y`.

Simplify using `[hι]`. Establish `hιs : ∀ y i, b.repr (ι y) (k.succAbove i) = y i`. Introduce `y i`. Simplify using `[hι, Finsupp.single_apply]`. Establish `hsur : ∀ v, b.repr v k = 0 → ι (fun i => b.repr v (k.succAbove i)) = v`.

Introduce `v hv`. Use `conv_rhs => rw [← b.sum_repr v, Fin.sum_univ_succAbove _ k, hv, zero_smul, zero_add]`. Conclude with `hι _`. Establish `hx : b k ∈ L` using `Submodule.subset_span ⟨k, rfl⟩`. Use `⟨L, ⟨⟨Submodule.fg_span (Set.finite_range _), ?_⟩, ?_⟩, hx, ?_, stdSpace star_isIntegral n (fun i => neg (k.succAbove i)) p q, ι, hk, ?_, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[Submodule.span_span_of_tower]`. Conclude with `b.span_eq`. Establish `h` using `(Formalism.E.hermDual (𝓞 E) E W.V (Fin (n + 1)) W.hT b (IsFractionRing.injective (𝓞 E) E) (star_integral star_isIntegral)).2 (Matrix.diagonal fun i => (sgn (neg i) : 𝓞 E)) (by`. Introduce `i j`. Rewrite using `[hb]`.

Distinguish the cases in `h : i = j`. Substitute `h` using the available equality. Simplify using `[map_sgn]`. Simplify using `[h]) (by`. Rewrite using `[Matrix.det_diagonal]`.

Conclude with `Finset.prod_ne_zero_iff.2 fun i _ => sgn_ne_zero (neg i))`. Conclude with `h.2.2 (by`. Rewrite using `[Matrix.det_diagonal]`. Use `isUnit_iff_exists_inv.2 ⟨∏ i, (sgn (neg i) : 𝓞 E), ?_⟩` and prove the remaining obligations. Rewrite using `[← Finset.prod_mul_distrib]`.

Simplify using `[sgn_mul_self])`. Use `le_antisymm (Submodule.span_le.2 ?_) (sup_le (Submodule.span_le.2 (Set.singleton_subset_iff.2 hx)) inf_le_left)` and prove the remaining obligations. Introduce and unpack `_ ⟨i, rfl⟩`. Distinguish the cases in `h : i = k`. Substitute `h` using the available equality.

Conclude with `Submodule.mem_sup_left (Submodule.mem_span_singleton_self _)`. Use `Submodule.mem_sup_right ⟨Submodule.subset_span ⟨i, rfl⟩, (hperp _).2 ?_⟩` and prove the remaining obligations. Simplify using `[h]`. Express the relevant statement in the definitionally equal form `∀ x y : Fin n → E, W.hT (ι x) (ι y) = diagForm n (fun i => neg (k.succAbove i)) x y`. Introduce `x y`.

Use `conv_lhs => rw [hι x]`. Rewrite using `[diagForm_apply, map_sum, LinearMap.sum_apply]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.map_smulₛₗ, LinearMap.smul_apply, key, hιs, smul_eq_mul, mul_assoc]`. Both sides reduce to the same expression.

Use extensionality with `v`. Rewrite using `[hperp]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, rfl⟩`. Conclude with `hιk y`.

Conclude with `fun hv => ⟨_, hsur v hv⟩`. Use extensionality with `v`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, rfl⟩`. Use `⟨(hL (ι y)).2 fun i => ?_, (hperp (ι y)).2 (hιk y)⟩` and prove the remaining obligations.

Break down `eq_or_ne i k with rfl | h` into its components or cases. Conclude with `⟨0, (map_zero _).trans (hιk y).symm⟩`. Take `⟨j, rfl⟩` from `Fin.exists_succAbove_eq h`. Conclude with `(hιs y j).symm ▸ (hS y).1 hy j`. Introduce and unpack `⟨h1, h2⟩`.

Conclude with `⟨fun i => b.repr v (k.succAbove i), (hS _).2 fun i => (hL v).1 h1 _, hsur v ((hperp v).1 h2)⟩`.
-/
theorem hasComplement_of_basis (W : HSpace E) {n : ℕ} (b : Module.Basis (Fin (n + 1)) E W.V)
    (neg : Fin (n + 1) → Bool)
    (hb : ∀ i j, W.hT (b i) (b j) = if i = j then sgn (neg i) else 0) (k : Fin (n + 1)) {p q : ℕ}
    (hk : OfKind (stdSpace (E := E) star_isIntegral n (fun i => neg (k.succAbove i)) p q) n p q) :
    HasComplement W (b k) n p q := by
  have key : ∀ i v, W.hT (b i) v = sgn (neg i) * b.repr v i := by
    intro i v
    conv_lhs => rw [← b.sum_repr v]
    rw [map_sum, Finset.sum_eq_single i (fun j _ hj => by rw [map_smul, hb, if_neg hj.symm, smul_zero])
      (by simp), map_smul, hb, if_pos rfl, smul_eq_mul, mul_comm]
  have hperp : ∀ v, v ∈ perp W (b k) ↔ b.repr v k = 0 := by
    intro v
    change W.hT (b k) v = 0 ↔ _
    rw [key, mul_eq_zero, or_iff_right (sgn_ne_zero _)]
  let L : Submodule (𝓞 E) W.V := Submodule.span (𝓞 E) (Set.range b)
  have hL : ∀ v, v ∈ L ↔ ∀ i, b.repr v i ∈ Set.range (algebraMap (𝓞 E) E) :=
    fun v => b.mem_span_iff_repr_mem (𝓞 E) v
  have hS : ∀ y : Fin n → E, y ∈ stdLat (E := E) n ↔ ∀ i, y i ∈ Set.range (algebraMap (𝓞 E) E) :=
    fun y => (Pi.basisFun E (Fin n)).mem_span_iff_repr_mem (𝓞 E) y
  let ι : (Fin n → E) →ₗ[E] W.V := Fintype.linearCombination E fun i => b (k.succAbove i)
  have hι : ∀ y, ι y = ∑ i, y i • b (k.succAbove i) := fun y => Fintype.linearCombination_apply _ _ _
  have hιk : ∀ y, b.repr (ι y) k = 0 := by
    intro y
    simp [hι]
  have hιs : ∀ y i, b.repr (ι y) (k.succAbove i) = y i := by
    intro y i
    simp [hι, Finsupp.single_apply]
  have hsur : ∀ v, b.repr v k = 0 → ι (fun i => b.repr v (k.succAbove i)) = v := by
    intro v hv
    conv_rhs => rw [← b.sum_repr v, Fin.sum_univ_succAbove _ k, hv, zero_smul, zero_add]
    exact hι _
  have hx : b k ∈ L := Submodule.subset_span ⟨k, rfl⟩
  refine ⟨L, ⟨⟨Submodule.fg_span (Set.finite_range _), ?_⟩, ?_⟩, hx, ?_,
    stdSpace star_isIntegral n (fun i => neg (k.succAbove i)) p q, ι, hk, ?_, ?_, ?_⟩
  · rw [Submodule.span_span_of_tower]
    exact b.span_eq
  · have h := (Formalism.E.hermDual (𝓞 E) E W.V (Fin (n + 1)) W.hT b
      (IsFractionRing.injective (𝓞 E) E) (star_integral star_isIntegral)).2
      (Matrix.diagonal fun i => (sgn (neg i) : 𝓞 E)) (by
        intro i j
        rw [hb]
        by_cases h : i = j
        · subst h; simp [map_sgn]
        · simp [h]) (by
        rw [Matrix.det_diagonal]
        exact Finset.prod_ne_zero_iff.2 fun i _ => sgn_ne_zero (neg i))
    exact h.2.2 (by
      rw [Matrix.det_diagonal]
      refine isUnit_iff_exists_inv.2 ⟨∏ i, (sgn (neg i) : 𝓞 E), ?_⟩
      rw [← Finset.prod_mul_distrib]
      simp [sgn_mul_self])
  · refine le_antisymm (Submodule.span_le.2 ?_)
      (sup_le (Submodule.span_le.2 (Set.singleton_subset_iff.2 hx)) inf_le_left)
    rintro _ ⟨i, rfl⟩
    by_cases h : i = k
    · subst h
      exact Submodule.mem_sup_left (Submodule.mem_span_singleton_self _)
    · refine Submodule.mem_sup_right ⟨Submodule.subset_span ⟨i, rfl⟩, (hperp _).2 ?_⟩
      simp [h]
  · change ∀ x y : Fin n → E, W.hT (ι x) (ι y) = diagForm n (fun i => neg (k.succAbove i)) x y
    intro x y
    conv_lhs => rw [hι x]
    rw [diagForm_apply, map_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, key, hιs, smul_eq_mul, mul_assoc]
    rfl
  · ext v
    rw [hperp]
    constructor
    · rintro ⟨y, rfl⟩
      exact hιk y
    · exact fun hv => ⟨_, hsur v hv⟩
  · ext v
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨(hL (ι y)).2 fun i => ?_, (hperp (ι y)).2 (hιk y)⟩
      rcases eq_or_ne i k with rfl | h
      · exact ⟨0, (map_zero _).trans (hιk y).symm⟩
      · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq h
        exact (hιs y j).symm ▸ (hS y).1 hy j
    · rintro ⟨h1, h2⟩
      exact ⟨fun i => b.repr v (k.succAbove i), (hS _).2 fun i => (hL v).1 h1 _,
        hsur v ((hperp v).1 h2)⟩

/- English proof (translation)
Introduce `W M P Q hW hM`. Establish `hPQ` using `rank_eq_add hW`. Take `⟨b, hb⟩` from `H W M P Q hW`. Take `⟨n, rfl⟩ : ∃ n, M = n + 1` from `⟨M - 1, by omega⟩`. Use `⟨fun hP => ⟨b 0, ?_, ?_⟩, fun hQ => ⟨b (Fin.last n), ?_, ?_⟩⟩` and prove the remaining obligations.

Establish `: ¬ P ≤ 0` using `by omega`. Simplify using `[HSpace.hD, hb, negFrom, sgn, this]`. Use `hasComplement_of_basis W b _ hb 0 ?_` and prove the remaining obligations. Establish `: (fun i : Fin n => negFrom (n + 1) P ((0 : Fin (n + 1)).succAbove i)) = negFrom n (P - 1)`. Use function extensionality and compare the values at `i`.

Conclude with `decide_eq_decide.2 (by`. Express the relevant statement in the definitionally equal form `P ≤ (i : ℕ) + 1 ↔ P - 1 ≤ (i : ℕ)`. Use the proof step `omega)`. Rewrite using `[this]`. Conclude with `ofKind_stdSpace (by omega)`.

Establish `: P ≤ n` using `by omega`. Simplify using `[HSpace.hD, hb, negFrom, sgn, this]`. Use `hasComplement_of_basis W b _ hb (Fin.last n) ?_` and prove the remaining obligations. Establish `: (fun i : Fin n => negFrom (n + 1) P ((Fin.last n).succAbove i)) = negFrom n P`. Use function extensionality and compare the values at `i`.

Simplify using `[negFrom]`. Rewrite using `[this]`. Conclude with `ofKind_stdSpace (by omega)`.
-/
theorem over_of_bases
    (H : ∀ (W : HSpace E) (M P Q : ℕ), OfKind W M P Q → ∃ b : Module.Basis (Fin M) E W.V,
      ∀ i j, W.hT (b i) (b j) = if i = j then sgn (negFrom M P i) else 0) :
    UnitVectorPerpOver E := by
  intro W M P Q hW hM
  have hPQ := rank_eq_add hW
  obtain ⟨b, hb⟩ := H W M P Q hW
  obtain ⟨n, rfl⟩ : ∃ n, M = n + 1 := ⟨M - 1, by omega⟩
  refine ⟨fun hP => ⟨b 0, ?_, ?_⟩, fun hQ => ⟨b (Fin.last n), ?_, ?_⟩⟩
  · have : ¬ P ≤ 0 := by omega
    simp [HSpace.hD, hb, negFrom, sgn, this]
  · refine hasComplement_of_basis W b _ hb 0 ?_
    have : (fun i : Fin n => negFrom (n + 1) P ((0 : Fin (n + 1)).succAbove i)) =
        negFrom n (P - 1) := by
      funext i
      exact decide_eq_decide.2 (by
        change P ≤ (i : ℕ) + 1 ↔ P - 1 ≤ (i : ℕ)
        omega)
    rw [this]
    exact ofKind_stdSpace (by omega)
  · have : P ≤ n := by omega
    simp [HSpace.hD, hb, negFrom, sgn, this]
  · refine hasComplement_of_basis W b _ hb (Fin.last n) ?_
    have : (fun i : Fin n => negFrom (n + 1) P ((Fin.last n).succAbove i)) = negFrom n P := by
      funext i
      simp [negFrom]
    rw [this]
    exact ofKind_stdSpace (by omega)

end Generic

section CM

open ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.SelfDualGenus GlobalTheory.LocalConjugacy

variable {E : Type} [Field E] [NumberField E] [IsCMField E]
attribute [local instance] IsCMField.starRing

/- English proof (translation)
Use `GlobalTheory.DefiniteMass.unramified_of_isCMUnram hc` as an intermediate fact. Establish `hr` using `rank_eq_add hW`. Take `⟨-, hs, hp⟩` from `hW`. Establish `hG : ∀ a b, cc (W.gramᵀ a b) = W.gramᵀ b a` using `fun a b => W.herm.eq (W.frame b) (W.frame a)`. Establish `hd : W.gramᵀ.det ≠ 0`.

Rewrite using `[Matrix.det_transpose]`. Conclude with `(GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.gram_det_isUnit W).ne_zero`. Take `⟨P, hP0, hP⟩` from `congr_signMatrix (GlobalTheory.LocalQuad.landherr_of_hasseNormSt GlobalTheory.QNorm.hasseNormSt) GlobalTheory.QNorm.hasseNormSt hG hd (isLattice_coordLat W W.L0 W.standardTuple_isLattice) (selfDual_coordLat W W.L0 W.baseLattice_isUnimodular) Set.univ (fun _ => Or.inl trivial) p f …`. Establish `h0` using `hs τ`. Rewrite `h0` using `[hp τ]`.

Take `⟨e, Q, hQ⟩` from `h0`. Establish `hJ` using `jpq_submatrix hr`. Use `set f := (finCongr hr).trans (finSumFinEquiv (m := p) (n := q)).symm`. Establish `h1` using `congrArg (fun M => (Matrix.submatrix M f f)ᵀ) hQ`. Simplify using `only [hJ, Matrix.diagonal_transpose] at h1`.

Rewrite `h1` using `[← Matrix.submatrix_mul_equiv _ _ f e f, ← Matrix.submatrix_mul_equiv _ _ f e e, Matrix.transpose_mul, Matrix.transpose_mul, ← Matrix.mul_assoc]`. Establish `h2 : gram τ W.gramᵀ (Q.1.submatrix e f) = Matrix.diagonal fun a : Fin W.rank => (Examples₂.sgn (negFrom W.rank p a) : ℂ)`. Rewrite using `[Published.gram_eq]`. Use `h1 using 1` and compare the differences between its conclusion and the goal. Use `congr 2`.

Use extensionality with `i j`. Simplify using the standard rewrite rules. Use `⟨Q.1.submatrix e f, fun h0 => ?_, h2.trans ?_⟩` and prove the remaining obligations. Establish `h3` using `congrArg Matrix.det h2`. Rewrite `h3` using `[Published.gram_eq, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, h0, zero_mul, zero_mul, Matrix.det_diagonal]`.

Conclude with `Finset.prod_ne_zero_iff.2 (fun a _ => sgn_ne_zero _) h3.symm`. Use `congr 1`. Use function extensionality and compare the values at `a`. Distinguish the cases in `h : (a : ℕ) < p`. Simplify using `[negFrom, Examples₂.sgn, ReciprocityTheory.ChartRestriction.G.FD.sgn, h, not_le.2 h]`.

Simplify using `[negFrom, Examples₂.sgn, ReciprocityTheory.ChartRestriction.G.FD.sgn, h, not_lt.1 h]`. Establish `h1 : signMatrix E W.rank p = Matrix.diagonal fun a => (Examples₂.sgn (negFrom W.rank p a) : E)`. Unfold `signMatrix`. Use `congr 1`. Use function extensionality and compare the values at `a`.

Distinguish the cases in `h : (a : ℕ) < p`. Simplify using `[negFrom, Examples₂.sgn, h, not_le.2 h]`. Simplify using `[negFrom, Examples₂.sgn, h, not_lt.1 h]`. Rewrite `hP` using `[h1]`. Use `⟨W.frame.equivFun.trans (Matrix.toLinearEquiv' P (Matrix.invertibleOfIsUnitDet P hP0.isUnit)), fun x y => ?_⟩` and prove the remaining obligations.

Rewrite using `[← herm_coord, hP, ← Published.LandherrSt.herm_mulVec]`. Express the relevant statement in the definitionally equal form `∑ i, cc ((P *ᵥ W.frame.equivFun x) i) * Examples₂.sgn (negFrom W.rank p i) * (P *ᵥ W.frame.equivFun y) i = _`. Rewrite using `[Published.LandherrSt.herm_eq]`. Simplify using `only [dotProduct, Matrix.mulVec_diagonal]`. Conclude with `Finset.sum_congr rfl fun i _ => by ring`.
-/
theorem exists_isometry (hc : Formalism.HermitianLatticesTheory.IsCMUnram E) (W : Formalism.BasicNotions.HSpace E) {p q : ℕ}
    (hW : OfKind W W.rank p q) :
    ∃ e : W.V ≃ₗ[E] (Fin W.rank → E),
      ∀ x y, diagForm W.rank (negFrom W.rank p) (e x) (e y) = W.hT x y := by
  have := GlobalTheory.DefiniteMass.unramified_of_isCMUnram hc
  have hr := rank_eq_add hW
  obtain ⟨-, hs, hp⟩ := hW
  have hG : ∀ a b, cc (W.gramᵀ a b) = W.gramᵀ b a := fun a b => W.herm.eq (W.frame b) (W.frame a)
  have hd : W.gramᵀ.det ≠ 0 := by
    rw [Matrix.det_transpose]; exact (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.gram_det_isUnit W).ne_zero
  obtain ⟨P, hP0, hP⟩ := congr_signMatrix
    (GlobalTheory.LocalQuad.landherr_of_hasseNormSt GlobalTheory.QNorm.hasseNormSt)
    GlobalTheory.QNorm.hasseNormSt hG hd (isLattice_coordLat W W.L0 W.standardTuple_isLattice)
    (selfDual_coordLat W W.L0 W.baseLattice_isUnimodular)
    Set.univ (fun _ => Or.inl trivial) p fun τ _ => by
      have h0 := hs τ
      rw [hp τ] at h0
      obtain ⟨e, Q, hQ⟩ := h0
      have hJ := jpq_submatrix hr
      set f := (finCongr hr).trans (finSumFinEquiv (m := p) (n := q)).symm
      have h1 := congrArg (fun M => (Matrix.submatrix M f f)ᵀ) hQ
      simp only [hJ, Matrix.diagonal_transpose] at h1
      rw [← Matrix.submatrix_mul_equiv _ _ f e f, ← Matrix.submatrix_mul_equiv _ _ f e e,
        Matrix.transpose_mul, Matrix.transpose_mul, ← Matrix.mul_assoc] at h1
      have h2 : gram τ W.gramᵀ (Q.1.submatrix e f) =
          Matrix.diagonal fun a : Fin W.rank => (Examples₂.sgn (negFrom W.rank p a) : ℂ) := by
        rw [Published.gram_eq]
        convert h1 using 1
        congr 2
        ext i j
        simp
      refine ⟨Q.1.submatrix e f, fun h0 => ?_, h2.trans ?_⟩
      · have h3 := congrArg Matrix.det h2
        rw [Published.gram_eq, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, h0, zero_mul,
          zero_mul, Matrix.det_diagonal] at h3
        exact Finset.prod_ne_zero_iff.2 (fun a _ => sgn_ne_zero _) h3.symm
      · congr 1
        funext a
        by_cases h : (a : ℕ) < p
        · simp [negFrom, Examples₂.sgn, ReciprocityTheory.ChartRestriction.G.FD.sgn, h, not_le.2 h]
        · simp [negFrom, Examples₂.sgn, ReciprocityTheory.ChartRestriction.G.FD.sgn, h, not_lt.1 h]
  have h1 : signMatrix E W.rank p =
      Matrix.diagonal fun a => (Examples₂.sgn (negFrom W.rank p a) : E) := by
    unfold signMatrix
    congr 1
    funext a
    by_cases h : (a : ℕ) < p
    · simp [negFrom, Examples₂.sgn, h, not_le.2 h]
    · simp [negFrom, Examples₂.sgn, h, not_lt.1 h]
  rw [h1] at hP
  refine ⟨W.frame.equivFun.trans
    (Matrix.toLinearEquiv' P (Matrix.invertibleOfIsUnitDet P hP0.isUnit)), fun x y => ?_⟩
  rw [← herm_coord, hP, ← Published.LandherrSt.herm_mulVec]
  change ∑ i, cc ((P *ᵥ W.frame.equivFun x) i) * Examples₂.sgn (negFrom W.rank p i) *
    (P *ᵥ W.frame.equivFun y) i = _
  rw [Published.LandherrSt.herm_eq]
  simp only [dotProduct, Matrix.mulVec_diagonal]
  exact Finset.sum_congr rfl fun i _ => by ring

/- English proof (translation)
Use `over_of_bases fun W M P Q hW => ?_` and prove the remaining obligations. Take `rfl` from `hW.1`. Apply the tactic sequence `obtain ⟨e, he⟩ := exists_isometry hc W hW`. Use `⟨(Pi.basisFun E (Fin W.rank)).map e.symm, fun i j => ?_⟩` and prove the remaining obligations. Rewrite using `[← he]`.

Simplify using `only [Module.Basis.map_apply, LinearEquiv.apply_symm_apply, Pi.basisFun_apply]`. Conclude with `diagForm_single _ _ i j`.
-/
theorem unitVectorPerpOver (hc : Formalism.HermitianLatticesTheory.IsCMUnram E) : UnitVectorPerpOver E := by
  refine over_of_bases fun W M P Q hW => ?_
  obtain rfl := hW.1
  obtain ⟨e, he⟩ := exists_isometry hc W hW
  refine ⟨(Pi.basisFun E (Fin W.rank)).map e.symm, fun i j => ?_⟩
  rw [← he]
  simp only [Module.Basis.map_apply, LinearEquiv.apply_symm_apply, Pi.basisFun_apply]
  exact diagForm_single _ _ i j

end CM

/- English proof (translation)
The claim follows from `haveI : IsCMField D.host.E := D.host.isCMField_hostE unitVectorPerpOver (E := D.host.E) D.sp.cm.cmUnram`.
-/
theorem unitVectorPerp (D : D7) : UnitVectorPerp D :=
  haveI : IsCMField D.host.E := D.host.isCMField_hostE
  unitVectorPerpOver (E := D.host.E) D.sp.cm.cmUnram

end GlobalTheory.UnitPerp

end
