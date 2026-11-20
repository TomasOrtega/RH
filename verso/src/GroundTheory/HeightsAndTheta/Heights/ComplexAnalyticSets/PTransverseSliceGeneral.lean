import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StTransverseSliceGeneral
import GroundTheory.HeightsAndTheta.Heights.Intersections.JacMinorC
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsExpansion
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Matrix ComplexSets Filter Topology

noncomputable section

namespace TransverseSliceGeneral

variable {n d : ℕ}

def gradAt (q : Fin n → ℂ) : MvPolynomial (Fin n) ℂ →ₗ[ℂ] (Fin n → ℂ) :=
  LinearMap.pi fun j => (aeval q).toLinearMap ∘ₗ (pderiv j).toLinearMap

/- English proof (translation)
Simplify using `[gradAt]`.
-/
theorem gradAt_apply (q : Fin n → ℂ) (g : MvPolynomial (Fin n) ℂ) (j : Fin n) :
    gradAt q g j = eval q (pderiv j g) := by
  simp [gradAt]

/- English proof (translation)
Use extensionality with `j`. Simplify using `[gradAt_apply, Derivation.leibniz, hg]`.
-/
theorem gradAt_mul_of_eval_eq_zero (q : Fin n → ℂ) (s g : MvPolynomial (Fin n) ℂ) (hg : eval q g = 0) :
    gradAt q (s * g) = eval q s • gradAt q g := by
  ext j
  simp [gradAt_apply, Derivation.leibniz, hg]

/- English proof (translation)
Use extensionality with `j`. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality. Simplify using `[gradAt_apply, pderiv_X]`. Simplify using `[gradAt_apply, pderiv_X, h, Ne.symm h]`.
-/
theorem gradAt_X_sub_C (q : Fin n → ℂ) (i : Fin n) (c : ℂ) :
    gradAt q (X i - C c) = Pi.single i 1 := by
  ext j
  by_cases h : i = j
  · subst h; simp [gradAt_apply, pderiv_X]
  · simp [gradAt_apply, pderiv_X, h, Ne.symm h]

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.Qn12.exists_expansion q p`.
-/
theorem exists_expansion (q : Fin n → ℂ) (p : MvPolynomial (Fin n) ℂ) :
    ∃ c : Fin n → MvPolynomial (Fin n) ℂ, p = C (eval q p) + ∑ i, c i * (X i - C (q i)) :=
  _root_.UpperTheory.Reformulated.B.Qn12.exists_expansion q p

/- English proof (translation)
Take `⟨c, hc⟩` from `exists_expansion q p`. Rewrite `hc` using `[hp, map_zero, zero_add]`. Establish `hgrad : gradAt q p = ∑ i, eval q (c i) • (Pi.single i 1 : Fin n → ℂ)`. Rewrite using `[hc, map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[gradAt_mul_of_eval_eq_zero q _ _ (by simp), gradAt_X_sub_C]`. Establish `hcj : ∀ j, eval q (c j) = 0`. Introduce `j`. Use `congr_fun (hgrad.symm.trans hg) j` as an intermediate fact. Simplify `this` using `[Finset.sum_apply, Pi.single_apply]`.

Rewrite using `[hc, sq]`. Conclude with `Ideal.sum_mem _ fun i _ => Ideal.mul_mem_mul (RingHom.mem_ker.2 (hcj i)) (by simp [RingHom.mem_ker])`.
-/
theorem mem_sq_of_gradAt_eq_zero (q : Fin n → ℂ) (p : MvPolynomial (Fin n) ℂ) (hp : eval q p = 0)
    (hg : gradAt q p = 0) : p ∈ RingHom.ker (eval q) ^ 2 := by
  obtain ⟨c, hc⟩ := exists_expansion q p
  rw [hp, map_zero, zero_add] at hc
  have hgrad : gradAt q p = ∑ i, eval q (c i) • (Pi.single i 1 : Fin n → ℂ) := by
    rw [hc, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [gradAt_mul_of_eval_eq_zero q _ _ (by simp), gradAt_X_sub_C]
  have hcj : ∀ j, eval q (c j) = 0 := by
    intro j
    have := congr_fun (hgrad.symm.trans hg) j
    simpa [Finset.sum_apply, Pi.single_apply] using this
  rw [hc, sq]
  exact Ideal.sum_mem _ fun i _ =>
    Ideal.mul_mem_mul (RingHom.mem_ker.2 (hcj i)) (by simp [RingHom.mem_ker])

/- English proof (translation)
Use `set m := RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ)`. Establish `hle : Submodule.map I.mkQ m ≤ m • Submodule.map I.mkQ m`. Rewrite using `[Submodule.map_le_iff_le_comap]`. Introduce `x hx`. Take `⟨i, hi, y, hy, rfl⟩` from `Submodule.mem_sup.1 (h hx)`.

Rewrite using `[Submodule.mem_comap, map_add, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero I).2 hi, zero_add, ← Submodule.map_smul'']`. Rewrite `hy` using `[sq, ← Ideal.smul_eq_mul]`. Conclude with `Submodule.mem_map_of_mem hy`. Take `⟨r, hr1, hr⟩` from `Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul m _ ((IsNoetherian.noetherian m).map I.mkQ) hle`. Use `⟨r, ?_, ?_⟩` and prove the remaining obligations.

Establish `h1 : eval q (r - 1) = 0` using `hr1`. Rewrite `h1` using `[map_sub, map_one, sub_eq_zero]`. Rewrite using `[h1]`. Conclude with `one_ne_zero`. Establish `h2` using `hr _ (Submodule.mem_map_of_mem (f := I.mkQ) (show g ∈ m from hg))`.

Rewrite `h2` using `[← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, smul_eq_mul]`. Conclude with `h2`.
-/
theorem exists_mul_mem_of_le_sup_sq (q : Fin n → ℂ) (I : Ideal (MvPolynomial (Fin n) ℂ))
    (h : RingHom.ker (eval q) ≤ I ⊔ RingHom.ker (eval q) ^ 2) (g : MvPolynomial (Fin n) ℂ)
    (hg : eval q g = 0) : ∃ s, eval q s ≠ 0 ∧ s * g ∈ I := by
  set m := RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ)
  have hle : Submodule.map I.mkQ m ≤ m • Submodule.map I.mkQ m := by
    rw [Submodule.map_le_iff_le_comap]
    intro x hx
    obtain ⟨i, hi, y, hy, rfl⟩ := Submodule.mem_sup.1 (h hx)
    rw [Submodule.mem_comap, map_add, Submodule.mkQ_apply,
      (Submodule.Quotient.mk_eq_zero I).2 hi, zero_add, ← Submodule.map_smul'']
    rw [sq, ← Ideal.smul_eq_mul] at hy
    exact Submodule.mem_map_of_mem hy
  obtain ⟨r, hr1, hr⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul m _
    ((IsNoetherian.noetherian m).map I.mkQ) hle
  refine ⟨r, ?_, ?_⟩
  · have h1 : eval q (r - 1) = 0 := hr1
    rw [map_sub, map_one, sub_eq_zero] at h1
    rw [h1]
    exact one_ne_zero
  · have h2 := hr _ (Submodule.mem_map_of_mem (f := I.mkQ) (show g ∈ m from hg))
    rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, smul_eq_mul] at h2
    exact h2

def gradSpace (W : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ) : Submodule ℂ (Fin n → ℂ) :=
  (Submodule.restrictScalars ℂ W).map (gradAt q)

/- English proof (translation)
Use extensionality with `j`. Simplify using `[gradAt_apply, linPoly, pderiv_X, Pi.single_apply]`.
-/
theorem gradAt_linPoly_sub (q : Fin n → ℂ) (L : Matrix (Fin d) (Fin n) ℂ) (i : Fin d) :
    gradAt q (linPoly L i - C ((L *ᵥ q) i)) = L i := by
  ext j
  simp [gradAt_apply, linPoly, pderiv_X, Pi.single_apply]

/- English proof (translation)
Use `le_antisymm ?_ (sup_le ?_ ?_)` and prove the remaining obligations. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Take `⟨w, hw, y, hy, rfl⟩` from `Submodule.mem_sup.1 hx`. Rewrite using `[map_add]`. Use `Submodule.add_mem_sup ⟨w, hw, rfl⟩ ?_` and prove the remaining obligations.

Take `⟨c, rfl⟩` from `Ideal.mem_span_range_iff_exists_fun.1 hy`. Rewrite using `[map_sum]`. Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Rewrite using `[gradAt_mul_of_eval_eq_zero q _ _ (by rw [map_sub, eval_linPoly, eval_C, sub_self]), gradAt_linPoly_sub]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`.

Introduce and unpack `_ ⟨x, hx, rfl⟩`. Conclude with `⟨x, Ideal.mem_sup_left hx, rfl⟩`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Conclude with `⟨_, Ideal.mem_sup_right (Ideal.subset_span ⟨i, rfl⟩), gradAt_linPoly_sub q L i⟩`.
-/
theorem gradSpace_sliceIdeal (W : Ideal (MvPolynomial (Fin n) ℂ)) (L : Matrix (Fin d) (Fin n) ℂ)
    (q : Fin n → ℂ) :
    gradSpace (sliceIdeal W L q) q = gradSpace W q ⊔ Submodule.span ℂ (Set.range fun i => L i) := by
  refine le_antisymm ?_ (sup_le ?_ ?_)
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨w, hw, y, hy, rfl⟩ := Submodule.mem_sup.1 hx
    rw [map_add]
    refine Submodule.add_mem_sup ⟨w, hw, rfl⟩ ?_
    obtain ⟨c, rfl⟩ := Ideal.mem_span_range_iff_exists_fun.1 hy
    rw [map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [gradAt_mul_of_eval_eq_zero q _ _ (by rw [map_sub, eval_linPoly, eval_C, sub_self]),
      gradAt_linPoly_sub]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · rintro _ ⟨x, hx, rfl⟩
    exact ⟨x, Ideal.mem_sup_left hx, rfl⟩
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨_, Ideal.mem_sup_right (Ideal.subset_span ⟨i, rfl⟩), gradAt_linPoly_sub q L i⟩

/- English proof (translation)
Rewrite using `[← gradSpace_sliceIdeal W L q]`. Establish `hq' : q ∈ zeroSet (sliceIdeal W L q)`. Rewrite using `[zeroSet_sliceIdeal]`. Conclude with `⟨hq, rfl⟩`. Use `set I := sliceIdeal W L q`.

Prove the components needed by the constructor for the conclusion. Introduce `hT`. Rewrite using `[eq_top_iff, ← (Pi.basisFun ℂ (Fin n)).span_eq, Submodule.span_le]`. Introduce and unpack `_ ⟨j, rfl⟩`. Take `⟨s, hs, hsI⟩` from `hT (X j - C (q j)) (by simp)`.

Use `⟨C (eval q s)⁻¹ * (s * (X j - C (q j))), I.mul_mem_left _ hsI, ?_⟩` and prove the remaining obligations. Rewrite using `[gradAt_mul_of_eval_eq_zero q _ _ (by simp), gradAt_mul_of_eval_eq_zero q _ _ (by simp), gradAt_X_sub_C, smul_smul, eval_C, inv_mul_cancel₀ hs, one_smul, Pi.basisFun_apply]`. Introduce `hG g hg`. Use `exists_mul_mem_of_le_sup_sq q I (fun x hx => ?_) g hg` and prove the remaining obligations. Take `⟨c, hc⟩` from `exists_expansion q x`.

Rewrite `hc` using `[RingHom.mem_ker.1 hx, map_zero, zero_add]`. Rewrite using `[hc]`. Use `Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ ?_` and prove the remaining obligations. Take `⟨h, hh, hgh⟩ : (Pi.single i 1 : Fin n → ℂ) ∈ gradSpace I q` from `hG ▸ Submodule.mem_top`. Establish `hmem : X i - C (q i) - h ∈ RingHom.ker (eval q) ^ 2` using `mem_sq_of_gradAt_eq_zero q _ (by rw [map_sub, hq' h hh]; simp) (by rw [map_sub, hgh, gradAt_X_sub_C, sub_self])`.

Establish `hsplit : X i - C (q i) = h + (X i - C (q i) - h)` using `by ring`. Rewrite using `[hsplit]`. Conclude with `Submodule.add_mem_sup hh hmem`.
-/
theorem isTransverseSliceAt_iff (W : Ideal (MvPolynomial (Fin n) ℂ)) (L : Matrix (Fin d) (Fin n) ℂ)
    (q : Fin n → ℂ) (hq : q ∈ zeroSet W) :
    IsTransverseSliceAt W L q ↔ gradSpace W q ⊔ Submodule.span ℂ (Set.range fun i => L i) = ⊤ := by
  rw [← gradSpace_sliceIdeal W L q]
  have hq' : q ∈ zeroSet (sliceIdeal W L q) := by
    rw [zeroSet_sliceIdeal]
    exact ⟨hq, rfl⟩
  set I := sliceIdeal W L q
  constructor
  · intro hT
    rw [eq_top_iff, ← (Pi.basisFun ℂ (Fin n)).span_eq, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    obtain ⟨s, hs, hsI⟩ := hT (X j - C (q j)) (by simp)
    refine ⟨C (eval q s)⁻¹ * (s * (X j - C (q j))), I.mul_mem_left _ hsI, ?_⟩
    rw [gradAt_mul_of_eval_eq_zero q _ _ (by simp), gradAt_mul_of_eval_eq_zero q _ _ (by simp),
      gradAt_X_sub_C, smul_smul, eval_C, inv_mul_cancel₀ hs, one_smul, Pi.basisFun_apply]
  · intro hG g hg
    refine exists_mul_mem_of_le_sup_sq q I (fun x hx => ?_) g hg
    obtain ⟨c, hc⟩ := exists_expansion q x
    rw [RingHom.mem_ker.1 hx, map_zero, zero_add] at hc
    rw [hc]
    refine Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ ?_
    obtain ⟨h, hh, hgh⟩ : (Pi.single i 1 : Fin n → ℂ) ∈ gradSpace I q := hG ▸ Submodule.mem_top
    have hmem : X i - C (q i) - h ∈ RingHom.ker (eval q) ^ 2 :=
      mem_sq_of_gradAt_eq_zero q _ (by rw [map_sub, hq' h hh]; simp)
        (by rw [map_sub, hgh, gradAt_X_sub_C, sub_self])
    have hsplit : X i - C (q i) = h + (X i - C (q i) - h) := by ring
    rw [hsplit]
    exact Submodule.add_mem_sup hh hmem

/- English proof (translation)
Introduce `f₀`. Set `ι : Fin m → Fin d` to `Fin.castLE h`. Set `g : Fin m → Fin d → ℂ` to `fun k => Pi.single (ι k) 1`. Set `A : Matrix (Fin m) (Fin m) ℂ` to `Matrix.of fun k l => f₀ k (ι l)`. Establish `hfin : {t : ℂ | (A + t • (1 : Matrix (Fin m) (Fin m) ℂ)).det = 0}.Finite`.

Use `(Polynomial.finite_setOfPred_isRoot (-A).charpoly_monic.ne_zero).subset fun t ht => ?_` and prove the remaining obligations. Simplify using `only [Set.mem_ofPred_eq, Polynomial.IsRoot, Matrix.eval_charpoly] at ht ⊢`. Rewrite using `[show scalar (Fin m) t - -A = A + t • (1 : Matrix (Fin m) (Fin m) ℂ) by` and apply the resulting hypothesis. Rewrite using `[sub_neg_eq_add, add_comm, scalar_apply, smul_one_eq_diagonal]]`. Establish `hLI : ∀ t ∉ {t : ℂ | (A + t • (1 : Matrix (Fin m) (Fin m) ℂ)).det = 0}, LinearIndependent ℂ (f₀ + t • g)`.

Introduce `t ht`. Establish `hU : IsUnit (A + t • (1 : Matrix (Fin m) (Fin m) ℂ))` using `(Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 ht)`. Use `LinearIndependent.of_comp (LinearMap.funLeft ℂ ℂ ι) ?_` and prove the remaining obligations. Establish `hfun : (⇑(LinearMap.funLeft ℂ ℂ ι) ∘ (f₀ + t • g)) = fun k => (A + t • (1 : Matrix (Fin m) (Fin m) ℂ)) k`. Use extensionality with `k l`.

Distinguish the cases in `hkl : k = l`. Substitute `hkl` using the available equality. Simplify using `[A, g, LinearMap.funLeft_apply]`. Establish `: ι l ≠ ι k` using `fun e => hkl (Fin.castLE_injective h e).symm`. Simplify using `[A, g, LinearMap.funLeft_apply, Matrix.one_apply, hkl, Pi.single_apply, this]`.

Rewrite using `[hfun]`. Conclude with `Matrix.linearIndependent_rows_iff_isUnit.2 hU`. Establish `hT : Tendsto (fun t : ℂ => f₀ + t • g) (𝓝[≠] 0) (𝓝 f₀)`. Establish `hc : Continuous fun t : ℂ => f₀ + t • g` using `continuous_const.add (continuous_id.smul continuous_const)`. Simplify using `using (hc.tendsto 0).mono_left nhdsWithin_le_nhds`.

Use `mem_closure_of_tendsto hT ?_` and prove the remaining obligations. Establish `hcl : IsClosed ({t : ℂ | (A + t • (1 : Matrix (Fin m) (Fin m) ℂ)).det = 0} \ {0})` using `(hfin.subset Set.sdiff_subset).isClosed`. Use `filter_upwards [nhdsWithin_le_nhds (hcl.isOpen_compl.mem_nhds (by simp)), self_mem_nhdsWithin] with t h1 h2`. Conclude with `hLI t fun h3 => h1 ⟨h3, h2⟩`.
-/
theorem dense_linearIndependent {m d : ℕ} (h : m ≤ d) :
    Dense {f : Fin m → Fin d → ℂ | LinearIndependent ℂ f} := by
  intro f₀
  let ι : Fin m → Fin d := Fin.castLE h
  let g : Fin m → Fin d → ℂ := fun k => Pi.single (ι k) 1
  let A : Matrix (Fin m) (Fin m) ℂ := Matrix.of fun k l => f₀ k (ι l)
  have hfin : {t : ℂ | (A + t • (1 : Matrix (Fin m) (Fin m) ℂ)).det = 0}.Finite := by
    refine (Polynomial.finite_setOfPred_isRoot (-A).charpoly_monic.ne_zero).subset fun t ht => ?_
    simp only [Set.mem_ofPred_eq, Polynomial.IsRoot, Matrix.eval_charpoly] at ht ⊢
    rwa [show scalar (Fin m) t - -A = A + t • (1 : Matrix (Fin m) (Fin m) ℂ) by
      rw [sub_neg_eq_add, add_comm, scalar_apply, smul_one_eq_diagonal]]
  have hLI : ∀ t ∉ {t : ℂ | (A + t • (1 : Matrix (Fin m) (Fin m) ℂ)).det = 0},
      LinearIndependent ℂ (f₀ + t • g) := by
    intro t ht
    have hU : IsUnit (A + t • (1 : Matrix (Fin m) (Fin m) ℂ)) :=
      (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 ht)
    refine LinearIndependent.of_comp (LinearMap.funLeft ℂ ℂ ι) ?_
    have hfun : (⇑(LinearMap.funLeft ℂ ℂ ι) ∘ (f₀ + t • g)) =
        fun k => (A + t • (1 : Matrix (Fin m) (Fin m) ℂ)) k := by
      ext k l
      by_cases hkl : k = l
      · subst hkl
        simp [A, g, LinearMap.funLeft_apply]
      · have : ι l ≠ ι k := fun e => hkl (Fin.castLE_injective h e).symm
        simp [A, g, LinearMap.funLeft_apply, Matrix.one_apply, hkl, Pi.single_apply, this]
    rw [hfun]
    exact Matrix.linearIndependent_rows_iff_isUnit.2 hU
  have hT : Tendsto (fun t : ℂ => f₀ + t • g) (𝓝[≠] 0) (𝓝 f₀) := by
    have hc : Continuous fun t : ℂ => f₀ + t • g := continuous_const.add (continuous_id.smul continuous_const)
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  refine mem_closure_of_tendsto hT ?_
  have hcl : IsClosed ({t : ℂ | (A + t • (1 : Matrix (Fin m) (Fin m) ℂ)).det = 0} \ {0}) :=
    (hfin.subset Set.sdiff_subset).isClosed
  filter_upwards [nhdsWithin_le_nhds (hcl.isOpen_compl.mem_nhds (by simp)), self_mem_nhdsWithin]
    with t h1 h2
  exact hLI t fun h3 => h1 ⟨h3, h2⟩

/- English proof (translation)
Use `set m := Module.finrank ℂ ((Fin n → ℂ) ⧸ V)`. Establish `hm : m ≤ d`. Use `Submodule.finrank_quotient_add_finrank V` as an intermediate fact. Simplify using `only [Module.finrank_fin_fun] at this`. Use linear arithmetic over natural numbers and integers.

Set `Ψ : (Fin n → ℂ) →ₗ[ℂ] (Fin m → ℂ)` to `(Module.finBasis ℂ ((Fin n → ℂ) ⧸ V)).equivFun.toLinearMap ∘ₗ V.mkQ`. Establish `hΨs : Function.Surjective Ψ` using `(Module.finBasis ℂ ((Fin n → ℂ) ⧸ V)).equivFun.surjective.comp V.mkQ_surjective`. Establish `hΨk : LinearMap.ker Ψ = V`. Simplify using `[Ψ, LinearEquiv.ker_comp]`. Set `Φ : Matrix (Fin d) (Fin n) ℂ →ₗ[ℂ] (Fin m → Fin d → ℂ)` to `{ toFun := fun L k i => Ψ (L i) k map_add' := fun L L' => by`.

Use extensionality with `k i`. Use `show Ψ (L i + L' i) k = Ψ (L i) k + Ψ (L' i) k`. Rewrite using `[map_add]`. Both sides reduce to the same expression. Use the proof step `map_smul' := fun c L => by`.

Use extensionality with `k i`. Use `show Ψ (c • L i) k = c * Ψ (L i) k`. Rewrite using `[map_smul]`. Use `rfl }`. Establish `hΦs : Function.Surjective Φ`.

Introduce `F`. Use `⟨Matrix.of fun i => Function.surjInv hΨs (fun k => F k i), ?_⟩` and prove the remaining obligations. Use extensionality with `k i`. Use `show Ψ (Function.surjInv hΨs (fun k => F k i)) k = F k i`. Rewrite using `[Function.surjInv_eq hΨs]`.

Establish `hset : {L : Matrix (Fin d) (Fin n) ℂ | V ⊔ Submodule.span ℂ (Set.range fun i => L i) = ⊤} = Φ ⁻¹' {f | LinearIndependent ℂ f}`. Use extensionality with `L`. Simplify using `only [Set.mem_ofPred_eq, Set.mem_preimage]`. Set `N : Matrix (Fin d) (Fin m) ℂ` to `Matrix.of fun i k => Ψ (L i) k`. Establish `h1 : V ⊔ Submodule.span ℂ (Set.range fun i => L i) = ⊤ ↔ Submodule.span ℂ (Set.range N.row) = ⊤`.

Establish `hc : Submodule.comap Ψ (Submodule.span ℂ (Set.range N.row)) = V ⊔ Submodule.span ℂ (Set.range fun i => L i)`. Establish `: Submodule.span ℂ (Set.range N.row) = (Submodule.span ℂ (Set.range fun i => L i)).map Ψ`. Rewrite using `[Submodule.map_span, ← Set.range_comp]`. Both sides reduce to the same expression. Rewrite using `[this, Submodule.comap_map_eq, hΨk, sup_comm]`.

Rewrite using `[← hc]`. Prove the components needed by the constructor for the conclusion. Introduce `htop`. Rewrite using `[← Submodule.map_comap_eq_of_surjective hΨs (Submodule.span ℂ (Set.range N.row)), htop, Submodule.map_top, LinearMap.range_eq_top.2 hΨs]`. Introduce `htop`.

Rewrite using `[htop, Submodule.comap_top]`. Establish `h2 : Submodule.span ℂ (Set.range N.row) = ⊤ ↔ N.rank = m`. Rewrite using `[Matrix.rank_eq_finrank_span_row]`. Prove the components needed by the constructor for the conclusion. Introduce `htop`.

Rewrite using `[htop, finrank_top, Module.finrank_fin_fun]`. Introduce `hr`. Conclude with `Submodule.eq_top_of_finrank_eq (by rw [hr, Module.finrank_fin_fun])`. Establish `h3 : LinearIndependent ℂ (Φ L) ↔ N.rank = m`. Rewrite using `[linearIndependent_iff_card_eq_finrank_span, Fintype.card_fin, ← Matrix.rank_transpose N, Matrix.rank_eq_finrank_span_row, eq_comm]`.

Both sides reduce to the same expression. Rewrite using `[h1, h2, h3]`. Rewrite using `[hset]`. Conclude with `⟨isOpen_setOfPred_linearIndependent.preimage (LinearMap.continuous_of_finiteDimensional Φ), (dense_linearIndependent hm).preimage (LinearMap.isOpenMap_of_finiteDimensional Φ hΦs)⟩`.
-/
theorem isOpen_dense_sup_span_rows (V : Submodule ℂ (Fin n → ℂ)) (hV : n ≤ Module.finrank ℂ V + d) :
    IsOpen {L : Matrix (Fin d) (Fin n) ℂ | V ⊔ Submodule.span ℂ (Set.range fun i => L i) = ⊤} ∧
      Dense {L : Matrix (Fin d) (Fin n) ℂ | V ⊔ Submodule.span ℂ (Set.range fun i => L i) = ⊤} := by
  set m := Module.finrank ℂ ((Fin n → ℂ) ⧸ V)
  have hm : m ≤ d := by
    have := Submodule.finrank_quotient_add_finrank V
    simp only [Module.finrank_fin_fun] at this
    omega
  let Ψ : (Fin n → ℂ) →ₗ[ℂ] (Fin m → ℂ) :=
    (Module.finBasis ℂ ((Fin n → ℂ) ⧸ V)).equivFun.toLinearMap ∘ₗ V.mkQ
  have hΨs : Function.Surjective Ψ :=
    (Module.finBasis ℂ ((Fin n → ℂ) ⧸ V)).equivFun.surjective.comp V.mkQ_surjective
  have hΨk : LinearMap.ker Ψ = V := by
    simp [Ψ, LinearEquiv.ker_comp]
  let Φ : Matrix (Fin d) (Fin n) ℂ →ₗ[ℂ] (Fin m → Fin d → ℂ) :=
    { toFun := fun L k i => Ψ (L i) k
      map_add' := fun L L' => by
        ext k i
        show Ψ (L i + L' i) k = Ψ (L i) k + Ψ (L' i) k
        rw [map_add]
        rfl
      map_smul' := fun c L => by
        ext k i
        show Ψ (c • L i) k = c * Ψ (L i) k
        rw [map_smul]
        rfl }
  have hΦs : Function.Surjective Φ := by
    intro F
    refine ⟨Matrix.of fun i => Function.surjInv hΨs (fun k => F k i), ?_⟩
    ext k i
    show Ψ (Function.surjInv hΨs (fun k => F k i)) k = F k i
    rw [Function.surjInv_eq hΨs]
  have hset : {L : Matrix (Fin d) (Fin n) ℂ | V ⊔ Submodule.span ℂ (Set.range fun i => L i) = ⊤} =
      Φ ⁻¹' {f | LinearIndependent ℂ f} := by
    ext L
    simp only [Set.mem_ofPred_eq, Set.mem_preimage]
    let N : Matrix (Fin d) (Fin m) ℂ := Matrix.of fun i k => Ψ (L i) k
    have h1 : V ⊔ Submodule.span ℂ (Set.range fun i => L i) = ⊤ ↔
        Submodule.span ℂ (Set.range N.row) = ⊤ := by
      have hc : Submodule.comap Ψ (Submodule.span ℂ (Set.range N.row)) =
          V ⊔ Submodule.span ℂ (Set.range fun i => L i) := by
        have : Submodule.span ℂ (Set.range N.row) =
            (Submodule.span ℂ (Set.range fun i => L i)).map Ψ := by
          rw [Submodule.map_span, ← Set.range_comp]
          rfl
        rw [this, Submodule.comap_map_eq, hΨk, sup_comm]
      rw [← hc]
      constructor
      · intro htop
        rw [← Submodule.map_comap_eq_of_surjective hΨs (Submodule.span ℂ (Set.range N.row)),
          htop, Submodule.map_top, LinearMap.range_eq_top.2 hΨs]
      · intro htop
        rw [htop, Submodule.comap_top]
    have h2 : Submodule.span ℂ (Set.range N.row) = ⊤ ↔ N.rank = m := by
      rw [Matrix.rank_eq_finrank_span_row]
      constructor
      · intro htop
        rw [htop, finrank_top, Module.finrank_fin_fun]
      · intro hr
        exact Submodule.eq_top_of_finrank_eq (by rw [hr, Module.finrank_fin_fun])
    have h3 : LinearIndependent ℂ (Φ L) ↔ N.rank = m := by
      rw [linearIndependent_iff_card_eq_finrank_span, Fintype.card_fin, ← Matrix.rank_transpose N,
        Matrix.rank_eq_finrank_span_row, eq_comm]
      rfl
    rw [h1, h2, h3]
  rw [hset]
  exact ⟨isOpen_setOfPred_linearIndependent.preimage (LinearMap.continuous_of_finiteDimensional Φ),
    (dense_linearIndependent hm).preimage (LinearMap.isOpenMap_of_finiteDimensional Φ hΦs)⟩

/- English proof (translation)
Introduce `n d W hW hdim`. Use `hW` as an intermediate fact. Take `⟨t, G, hG⟩` from `Submodule.fg_iff_exists_fin_generating_family.1 (IsNoetherian.noetherian W)`. Take `⟨a, b, hab⟩` from `IndefiniteRowSideFullHecke.Inter.exists_jacobian_minor_not_mem_charZero W G hG d hdim`. Use `⟨_, hab, fun q hq hfq => ?_⟩` and prove the remaining obligations.

Establish `hV : n ≤ Module.finrank ℂ (gradSpace W q) + d`. Set `w : Fin (Fintype.card (Fin n) - d) → Fin n → ℂ` to `fun i => gradAt q (G (a i))`. Establish `hw : LinearIndependent ℂ w`. Use `LinearIndependent.of_comp (LinearMap.funLeft ℂ ℂ b) ?_` and prove the remaining obligations. Establish `hdet : IsUnit (Matrix.of fun i j => eval q (pderiv (b j) (G (a i))))`.

Rewrite using `[Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]`. Rewrite `hfq` using `[RingHom.map_det]`. Conclude with `hfq`. Establish `hfun : (⇑(LinearMap.funLeft ℂ ℂ b) ∘ w) = fun i => (Matrix.of fun i j => eval q (pderiv (b j) (G (a i)))) i`. Use extensionality with `i j`.

Simplify using `[w, gradAt_apply, LinearMap.funLeft_apply]`. Rewrite using `[hfun]`. Conclude with `Matrix.linearIndependent_rows_iff_isUnit.2 hdet`. Establish `hle : Submodule.span ℂ (Set.range w) ≤ gradSpace W q`. Rewrite using `[Submodule.span_le]`.

Introduce and unpack `_ ⟨i, rfl⟩`. Conclude with `⟨G (a i), hG ▸ Ideal.subset_span ⟨a i, rfl⟩, rfl⟩`. Use `Submodule.finrank_mono hle` as an intermediate fact. Rewrite `this` using `[finrank_span_eq_card hw, Fintype.card_fin, Fintype.card_fin]`. Use linear arithmetic over natural numbers and integers.

Establish `hset : {L : Matrix (Fin d) (Fin n) ℂ | IsTransverseSliceAt W L q} = {L | gradSpace W q ⊔ Submodule.span ℂ (Set.range fun i => L i) = ⊤}` using `Set.ext fun L => isTransverseSliceAt_iff W L q hq`. Rewrite using `[hset]`. Conclude with `isOpen_dense_sup_span_rows _ hV`.
-/
theorem proof : TransverseSliceGeneral.Statement := by
  intro n d W hW hdim
  have := hW
  obtain ⟨t, G, hG⟩ := Submodule.fg_iff_exists_fin_generating_family.1 (IsNoetherian.noetherian W)
  obtain ⟨a, b, hab⟩ := IndefiniteRowSideFullHecke.Inter.exists_jacobian_minor_not_mem_charZero W G hG d hdim
  refine ⟨_, hab, fun q hq hfq => ?_⟩
  have hV : n ≤ Module.finrank ℂ (gradSpace W q) + d := by
    let w : Fin (Fintype.card (Fin n) - d) → Fin n → ℂ := fun i => gradAt q (G (a i))
    have hw : LinearIndependent ℂ w := by
      refine LinearIndependent.of_comp (LinearMap.funLeft ℂ ℂ b) ?_
      have hdet : IsUnit (Matrix.of fun i j => eval q (pderiv (b j) (G (a i)))) := by
        rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
        rw [RingHom.map_det] at hfq
        exact hfq
      have hfun : (⇑(LinearMap.funLeft ℂ ℂ b) ∘ w) =
          fun i => (Matrix.of fun i j => eval q (pderiv (b j) (G (a i)))) i := by
        ext i j
        simp [w, gradAt_apply, LinearMap.funLeft_apply]
      rw [hfun]
      exact Matrix.linearIndependent_rows_iff_isUnit.2 hdet
    have hle : Submodule.span ℂ (Set.range w) ≤ gradSpace W q := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact ⟨G (a i), hG ▸ Ideal.subset_span ⟨a i, rfl⟩, rfl⟩
    have := Submodule.finrank_mono hle
    rw [finrank_span_eq_card hw, Fintype.card_fin, Fintype.card_fin] at this
    omega
  have hset : {L : Matrix (Fin d) (Fin n) ℂ | IsTransverseSliceAt W L q} =
      {L | gradSpace W q ⊔ Submodule.span ℂ (Set.range fun i => L i) = ⊤} :=
    Set.ext fun L => isTransverseSliceAt_iff W L q hq
  rw [hset]
  exact isOpen_dense_sup_span_rows _ hV

end TransverseSliceGeneral

end

end GroundTheory.Heights₂.Heights
