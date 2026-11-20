import ReciprocityTheory.DualLattices.BlockOneMulMulBlockOne
import ReciprocityTheory.DualLattices.ProdDvdOfIso
import ReciprocityTheory.DualLattices.ExistsSmulMemOfMemSpan

noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up.ED

variable {C : Type} [Field C] {v : Valuation C NNReal} {R : Type} [CommRing R] [Algebra R C]

/- English proof (translation)
Use `conv_rhs => rw [← Finset.univ_sum_single x]`. Rewrite using `[map_sum, dotProduct]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Establish `hk : (Pi.single k (x k) : ι → R) = x k • (Pi.single k (1 : R) : ι → R)`. Use extensionality with `i`.

Distinguish the cases in `hi : i = k`. Substitute `hi` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Pi.single_apply, hi]`. Rewrite using `[hk, map_smul, smul_eq_mul, mul_comm]`.
-/
theorem dot_single {ι : Type} [Fintype ι] [DecidableEq ι] (f : (ι → R) →ₗ[R] R) (x : ι → R) :
    (fun k => f (Pi.single k 1)) ⬝ᵥ x = f x := by
  conv_rhs => rw [← Finset.univ_sum_single x]
  rw [map_sum, dotProduct]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hk : (Pi.single k (x k) : ι → R) = x k • (Pi.single k (1 : R) : ι → R) := by
    ext i
    by_cases hi : i = k
    · subst hi; simp
    · simp [Pi.single_apply, hi]
  rw [hk, map_smul, smul_eq_mul, mul_comm]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `using h (Pi.single i 1)`.
-/
theorem eq_of_dot {ι : Type} [Fintype ι] [DecidableEq ι] {w w' : ι → R}
    (h : ∀ x, w ⬝ᵥ x = w' ⬝ᵥ x) : w = w' := by
  funext i
  simpa using h (Pi.single i 1)

/- English proof (translation)
Establish `: IsDomain R` using `hv.hom_inj.isDomain`. Use `ValuationRing.of_integers v hv` as an intermediate fact. Use `set T := LinearMap.range (Matrix.mulVecLin ε) with hT`. Establish `hQeq : Qs = LinearMap.range (Matrix.mulVecLin Pq)` using `le_antisymm (fun w hw => ⟨w, hPqid w hw⟩) (by rintro _ ⟨w, rfl⟩; exact hPqmem w)`. Establish `hTfg : T.FG` using `by rw [hT, LinearMap.range_eq_map]; exact Module.Finite.fg_top.map _`.

Establish `hQfg : Qs.FG` using `by rw [hQeq, LinearMap.range_eq_map]; exact Module.Finite.fg_top.map _`. Establish `htf : ∀ {α : Type} (S : Submodule R (α → R)) (r : R) (x : S), r ≠ 0 → r • x = 0 → x = 0`. Introduce and unpack `α S r ⟨x, hx⟩ hr h`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `i`.

Use `congrFun (congrArg Subtype.val h) i` as an intermediate fact. Simplify using `only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, Submodule.coe_zero, Pi.zero_apply] at this`. Conclude with `(mul_eq_zero.1 this).resolve_left hr`. Establish `: Module.Finite R T` using `Module.Finite.iff_fg.2 hTfg`. Establish `: Module.Finite R Qs` using `Module.Finite.iff_fg.2 hQfg`.

Establish `: Module.Free R T` using `L2.SecondCohomologyLattice.free_of_finite_torsionFree T (htf T)`. Establish `: Module.Free R Qs` using `L2.SecondCohomologyLattice.free_of_finite_torsionFree Qs (htf Qs)`. Use `set β := Module.finBasisOfFinrankEq R T hnT with hβ`. Use `set γ := Module.finBasisOfFinrankEq R Qs hnQ with hγ`. Establish `hεT : ∀ t ∈ T, ε *ᵥ t = t`.

Introduce and unpack `_ ⟨x, rfl⟩`. Use `show ε *ᵥ (ε *ᵥ x) = ε *ᵥ x`. Rewrite using `[mulVec_mulVec, hε]`. Establish `hΦT : ∀ t : T, Φ *ᵥ (t : ι → R) ∈ Qs`. Introduce and unpack `⟨_, x, rfl⟩`.

Use `show Φ *ᵥ (ε *ᵥ x) ∈ Qs`. Rewrite using `[mulVec_mulVec, hcomm, ← mulVec_mulVec]`. Conclude with `hPqmem _`. Use `set Φi : T →ₗ[R] Qs := LinearMap.codRestrict Qs ((Matrix.mulVecLin Φ).comp T.subtype) hΦT with hΦi`. Establish `hΦiapp : ∀ t : T, ((Φi t : Qs) : κ' → R) = Φ *ᵥ (t : ι → R)` using `fun _ => rfl`.

Use `set M := LinearMap.toMatrix β γ Φi with hM`. Establish `hrange : ((T.map (Matrix.mulVecLin Φ)).comap Qs.subtype) = LinearMap.range Φi`. Use extensionality with `q`. Simplify using `only [Submodule.mem_comap, Submodule.mem_map, LinearMap.mem_range]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨t, ht, htq⟩`. Conclude with `⟨⟨t, ht⟩, Subtype.ext htq⟩`. Introduce and unpack `⟨t, rfl⟩`. Conclude with `⟨t, t.2, rfl⟩`. Establish `hkey : ∀ t : T, γ.equivFun (Φi t) = M *ᵥ β.equivFun t`.

Introduce `t`. Simplify using `only [Module.Basis.equivFun_apply]`. Rewrite using `[hM, LinearMap.toMatrix_mulVec_repr]`. Establish `hmapM : (LinearMap.range Φi).map γ.equivFun.toLinearMap = LinearMap.range (Matrix.mulVecLin M)`. Use extensionality with `z`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨_, ⟨t, rfl⟩, rfl⟩`. Conclude with `⟨β.equivFun t, (hkey t).symm⟩`. Introduce and unpack `⟨c, rfl⟩`. Use `⟨Φi (β.equivFun.symm c), ⟨_, rfl⟩, ?_⟩` and prove the remaining obligations.

Use `show γ.equivFun (Φi (β.equivFun.symm c)) = M *ᵥ c`. Rewrite using `[hkey, LinearEquiv.apply_symm_apply]`. Establish `hLen : HasLen v R (Qs ⧸ ((T.map (Matrix.mulVecLin Φ)).comap Qs.subtype)) (v (algebraMap R C M.det))`. Take `⟨m', c', ⟨f⟩, hf⟩` from `Smith.hasLen_coker_det (C := C) (v := v) hv M`. Conclude with `⟨m', c', ⟨((Submodule.quotEquivOfEq _ _ hrange).trans (Submodule.Quotient.equiv _ _ γ.equivFun hmapM)).trans f⟩, hf⟩`.

Establish `hXM : X = v (algebraMap R C M.det)` using `hasLen_unique hv hX hLen`. Take `⟨P, Q', a, hP, hQ', hD⟩` from `Smith.smith_mat hv n n Mᵀ`. Establish `hdiag : P * Mᵀ * Q' = Matrix.diagonal a`. Use extensionality with `j k`. Rewrite using `[hD, Matrix.diagonal_apply]`.

Distinguish the cases in `h : j = k`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Establish `: (k : ℕ) ≠ (j : ℕ)` using `fun e => h (Fin.ext e.symm)`. Simplify using `[h, this]`.

Establish `hprod : ∏ j, v (algebraMap R C (a j)) = X`. Rewrite using `[hXM, ← map_prod, ← map_prod, ← Matrix.det_diagonal, ← hdiag, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, map_mul, map_mul, map_mul, map_mul, hv.one_of_isUnit hP, hv.one_of_isUnit hQ', one_mul, mul_one]`. Use `set Pi' := P⁻¹ with hPi'`. Establish `hPP : P * Pi' = 1` using `Matrix.mul_nonsing_inv P hP`. Establish `hPP' : Pi' * P = 1` using `Matrix.nonsing_inv_mul P hP`.

Use `set ℓ : Fin n → (ι → R) →ₗ[R] R := fun l => (β.coord l).comp (Matrix.mulVecLin ε).rangeRestrict with hℓ`. Establish `hℓε : ∀ l x, ℓ l (ε *ᵥ x) = ℓ l x`. Introduce `l x`. Simplify using `only [hℓ, LinearMap.coe_comp, Function.comp_apply]`. Use `congr 1`.

Apply `Subtype.ext` to reduce the goal to its premises. Use `show ε *ᵥ (ε *ᵥ x) = ε *ᵥ x`. Rewrite using `[mulVec_mulVec, hε]`. Establish `hℓβ : ∀ l m, ℓ l (β m : ι → R) = if m = l then 1 else 0`. Introduce `l m`.

Simplify using `only [hℓ, LinearMap.coe_comp, Function.comp_apply]`. Establish `: (Matrix.mulVecLin ε).rangeRestrict (β m : ι → R) = β m`. Apply `Subtype.ext` to reduce the goal to its premises. Use `show ε *ᵥ (β m : ι → R) = β m`. Conclude with `hεT _ (β m).2`.

Rewrite using `[this, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]`. Use `set lam : Fin n → ι → R := fun j k => ∑ l, Pi' l j * ℓ l (Pi.single k 1) with hlam`. Establish `hlamdot : ∀ j x, lam j ⬝ᵥ x = ∑ l, Pi' l j * ℓ l x`. Introduce `j x`. Establish `e : lam j = fun k => (∑ l, Pi' l j • ℓ l) (Pi.single k 1)`.

Use function extensionality and compare the values at `k`. Simplify using `[hlam, LinearMap.sum_apply]`. Rewrite using `[e, dot_single]`. Simplify using `[LinearMap.sum_apply]`. Use `set y : Fin n → ι → R := fun l => ∑ m, P l m • (β m : ι → R) with hy`.

Establish `hyT : ∀ l, y l ∈ T` using `fun l => Submodule.sum_mem _ fun m _ => Submodule.smul_mem _ _ (β m).2`. Establish `hdotε : ∀ (w : ι → R) x, (w ᵥ* ε) ⬝ᵥ x = w ⬝ᵥ (ε *ᵥ x)` using `fun w x => (Matrix.dotProduct_mulVec w ε x).symm`. Establish `hlamε : ∀ j, lam j ᵥ* ε = lam j`. Introduce `j`. Apply `eq_of_dot` to reduce the goal to its premises.

Introduce `x`. Rewrite using `[hdotε, hlamdot, hlamdot]`. Simplify using `only [hℓε]`. Establish `hlamy : ∀ j l, lam j ⬝ᵥ y l = if j = l then 1 else 0`. Introduce `j l`.

Rewrite using `[hlamdot]`. Establish `e1 : ∀ l', ℓ l' (y l) = P l l'`. Introduce `l'`. Simplify using `only [hy, map_sum, map_smul, hℓβ, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]`. Simplify using `only [e1]`.

Use `congrFun (congrFun hPP l) j` as an intermediate fact. Rewrite `this` using `[Matrix.mul_apply, Matrix.one_apply]`. Establish `h2 : (if j = l then (1 : R) else 0) = if l = j then 1 else 0`. Apply the tactic sequence `by_cases h : j = l <;> simp [h, eq_comm]`. Rewrite using `[h2, ← this]`.

Conclude with `Finset.sum_congr rfl fun _ _ => mul_comm _ _`. Set `K : (ι → R) →ₗ[R] (Fin n → R)` to `{ toFun := fun w l => w ⬝ᵥ (β l : ι → R) map_add' := fun w w' => by funext l; simp [add_dotProduct] map_smul' := fun c w => by funext l; simp [smul_dotProduct] }`. Establish `hKapp : ∀ w l, K w l = w ⬝ᵥ (β l : ι → R)` using `fun _ _ => rfl`. Establish `hKlam : ∀ j, K (lam j) = fun l => Pi' l j`. Introduce `j`.

Use function extensionality and compare the values at `l`. Rewrite using `[hKapp, hlamdot]`. Simplify using `only [hℓβ, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]`. Use `set cvec : κ' → Fin n → R := fun k m => (γ m : κ' → R) k with hcvec`. Establish `hKrow : ∀ k, K ((Φ * ε) k) = Mᵀ *ᵥ cvec k`.

Introduce `k`. Use function extensionality and compare the values at `l`. Rewrite using `[hKapp]`. Establish `e1 : (Φ * ε) k ⬝ᵥ (β l : ι → R) = ((Φ * ε) *ᵥ (β l : ι → R)) k` using `rfl`. Rewrite using `[e1, ← mulVec_mulVec, hεT _ (β l).2, ← hΦiapp]`.

Establish `e2 : ((Φi (β l) : Qs) : κ' → R) = ∑ m, M m l • (γ m : κ' → R)`. Establish `h` using `γ.sum_repr (Φi (β l))`. Rewrite using `[← h]`. Simplify using `only [Submodule.coe_sum, Submodule.coe_smul, hM, LinearMap.toMatrix_apply]`. Rewrite using `[e2, Finset.sum_apply]`.

Simplify using `only [Pi.smul_apply, smul_eq_mul, mulVec, dotProduct, transpose_apply, hcvec]`. Use `set gs : Fin n → κ' → R := fun m k => γ.coord m ⟨Pq *ᵥ Pi.single k 1, hPqmem _⟩ with hgs`. Establish `hgsc : ∀ m m', ∑ k, gs m k * cvec k m' = if m' = m then 1 else 0`. Introduce `m m'`. Set `f : (κ' → R) →ₗ[R] R` to `(γ.coord m).comp (LinearMap.codRestrict Qs (Matrix.mulVecLin Pq) hPqmem)`.

Establish `hf : ∀ k, f (Pi.single k 1) = gs m k` using `fun k => rfl`. Establish `h1 : (fun k => f (Pi.single k 1)) ⬝ᵥ (γ m' : κ' → R) = f (γ m')` using `dot_single f _`. Establish `h2 : f (γ m') = if m' = m then 1 else 0`. Establish `: LinearMap.codRestrict Qs (Matrix.mulVecLin Pq) hPqmem (γ m' : κ' → R) = γ m'` using `Subtype.ext (hPqid _ (γ m').2)`. Simplify using `only [f, LinearMap.coe_comp, Function.comp_apply, this, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]`.

Rewrite using `[← h2, ← h1]`. Simplify using `only [dotProduct, hf, hcvec]`. Establish `hMrange : ∀ z, Mᵀ *ᵥ z ∈ Submodule.span R (Set.range fun k => Mᵀ *ᵥ cvec k)`. Introduce `z`. Establish `hz : z = ∑ k, (∑ m, z m * gs m k) • cvec k`.

Use function extensionality and compare the values at `m'`. Simplify using `only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`. Simplify using `only [mul_assoc, ← Finset.mul_sum, hgsc, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]`. Rewrite using `[hz, mulVec_sum]`.

Conclude with `Submodule.sum_mem _ fun k _ => by`. Rewrite using `[mulVec_smul]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)`. Establish `hmapN : (Submodule.span R (Set.range fun k => (Φ * ε) k)).map K = LinearMap.range (Matrix.mulVecLin Mᵀ)`. Rewrite using `[Submodule.map_span, ← Set.range_comp]`.

Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨k, rfl⟩`. Conclude with `⟨cvec k, (hKrow k).symm⟩`. Introduce and unpack `_ ⟨z, rfl⟩`.

Establish `e : (K ∘ fun k => (Φ * ε) k) = fun k => Mᵀ *ᵥ cvec k` using `funext hKrow`. Rewrite using `[e]`. Conclude with `hMrange z`. Establish `hmapS : (Submodule.span R (Set.range fun j => a j • lam j)).map K = LinearMap.range (Matrix.mulVecLin Mᵀ)`. Rewrite using `[Submodule.map_span, ← Set.range_comp]`.

Establish `e1 : (K ∘ fun j => a j • lam j) = fun j => fun l => (Pi' * Matrix.diagonal a) l j`. Use function extensionality and compare the values at `j l`. Simplify using `only [Function.comp_apply, map_smul, hKlam, Pi.smul_apply, smul_eq_mul, Matrix.mul_diagonal]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e1]`.

Establish `e2 : Pi' * Matrix.diagonal a = Mᵀ * Q'`. Rewrite using `[← hdiag, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hPP', Matrix.one_mul]`. Rewrite using `[e2]`. Establish `e3 : Submodule.span R (Set.range fun j => fun l => (Mᵀ * Q') l j) = LinearMap.range (Matrix.mulVecLin (Mᵀ * Q'))`. Rewrite using `[Matrix.range_mulVecLin]`.

Both sides reduce to the same expression. Rewrite using `[e3]`. Apply `le_antisymm` to reduce the goal to its premises. Introduce and unpack `_ ⟨z, rfl⟩; exact ⟨Q' *ᵥ z, by simp [mulVec_mulVec]⟩`. Introduce and unpack `_ ⟨z, rfl⟩`.

Use `⟨Q'⁻¹ *ᵥ z, ?_⟩` and prove the remaining obligations. Use `show (Mᵀ * Q') *ᵥ (Q'⁻¹ *ᵥ z) = Mᵀ *ᵥ z`. Rewrite using `[mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hQ', Matrix.mul_one]`. Establish `hKinj : ∀ w w', w ᵥ* ε = w → w' ᵥ* ε = w' → K w = K w' → w = w'`. Introduce `w w' hw hw' hK`.

Establish `hT0 : ∀ t ∈ T, w ⬝ᵥ t = w' ⬝ᵥ t`. Introduce `t ht`. Establish `: t = ∑ l, β.repr ⟨t, ht⟩ l • (β l : ι → R)`. Establish `h` using `congrArg Subtype.val (β.sum_repr ⟨t, ht⟩)`. Simplify using `only [Submodule.coe_sum, Submodule.coe_smul] at h`.

Conclude with `h.symm`. Rewrite using `[this, dotProduct_sum, dotProduct_sum]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[dotProduct_smul, dotProduct_smul]`. Use `congrFun hK l` as an intermediate fact.

Rewrite `this` using `[hKapp, hKapp]`. Rewrite using `[this]`. Apply `eq_of_dot` to reduce the goal to its premises. Introduce `x`. Rewrite using `[← hw, ← hw', hdotε, hdotε]`.

Conclude with `hT0 _ ⟨x, rfl⟩`. Establish `hrowε : ∀ k, (Φ * ε) k ᵥ* ε = (Φ * ε) k`. Introduce `k`. Use function extensionality and compare the values at `k'`. Simplify using `only [vecMul, dotProduct]`.

Use `congrFun (congrFun (show Φ * ε * ε = Φ * ε by rw [Matrix.mul_assoc, hε]) k) k'` as an intermediate fact. Rewrite `this` using `[Matrix.mul_apply]`. Conclude with `this`. Establish `hNle : ∀ w ∈ Submodule.span R (Set.range fun k => (Φ * ε) k), w ᵥ* ε = w`. Introduce `w hw`.

Proceed by induction on `hw using Submodule.span_induction with`. Consider the case `mem w hw => obtain ⟨k, rfl⟩ := hw`. Conclude with `hrowε k`. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => rw [add_vecMul, hx, hy]`.

Consider the case `smul c x _ hx => rw [smul_vecMul, hx]`. Establish `hSle : ∀ w ∈ Submodule.span R (Set.range fun j => a j • lam j), w ᵥ* ε = w`. Introduce `w hw`. Proceed by induction on `hw using Submodule.span_induction with`. Consider the case `mem w hw => obtain ⟨j, rfl⟩ := hw`.

Rewrite using `[smul_vecMul, hlamε]`. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => rw [add_vecMul, hx, hy]`. Consider the case `smul c x _ hx => rw [smul_vecMul, hx]`. Establish `hspan : Submodule.span R (Set.range fun k => (Φ * ε) k) = Submodule.span R (Set.range fun j => a j • lam j)`.

Apply `le_antisymm` to reduce the goal to its premises. Introduce `w hw`. Establish `hKw : K w ∈ (Submodule.span R (Set.range fun j => a j • lam j)).map K`. Rewrite using `[hmapS, ← hmapN]`. Conclude with `⟨w, hw, rfl⟩`.

Take `⟨s, hs, hsw⟩` from `hKw`. Rewrite using `[← hKinj s w (hSle s hs) (hNle w hw) hsw]`. Conclude with `hs`. Introduce `w hw`. Establish `hKw : K w ∈ (Submodule.span R (Set.range fun k => (Φ * ε) k)).map K`.

Rewrite using `[hmapN, ← hmapS]`. Conclude with `⟨w, hw, rfl⟩`. Take `⟨s, hs, hsw⟩` from `hKw`. Rewrite using `[← hKinj s w (hNle s hs) (hSle w hw) hsw]`. Conclude with `hs`.

Establish `hdvd : ∀ j, ∃ c, cp = a j * c`. Introduce `j`. Take `⟨u, hu⟩` from `hcp (lam j) (hlamε j)`. Establish `hmem : cp • lam j ∈ Submodule.span R (Set.range fun k => (Φ * ε) k)`. Rewrite using `[hu]`.

Establish `e : u ᵥ* (Φ * ε) = ∑ k, u k • (Φ * ε) k`. Use function extensionality and compare the values at `k'`. Simplify using `[vecMul, dotProduct, Finset.sum_apply]`. Rewrite using `[e]`. Conclude with `Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)`.

Establish `hK` using `Submodule.mem_map_of_mem (f := K) hmem`. Rewrite `hK` using `[hmapN]`. Take `⟨z, hz⟩` from `hK`. Establish `hz' : Mᵀ *ᵥ z = cp • fun l => Pi' l j`. Rewrite using `[← hKlam, ← map_smul]`.

Conclude with `hz`. Establish `h2 : Matrix.diagonal a *ᵥ (Q'⁻¹ *ᵥ z) = cp • Pi.single j 1`. Rewrite using `[← hdiag, mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hQ', Matrix.mul_one, ← mulVec_mulVec]`. Use `show P *ᵥ (Mᵀ *ᵥ z) = _`. Rewrite using `[hz']`.

Use function extensionality and compare the values at `l`. Simplify using `only [mulVec_smul, Pi.smul_apply, smul_eq_mul]`. Use `congrFun (congrFun hPP l) j` as an intermediate fact. Rewrite `this` using `[Matrix.mul_apply, Matrix.one_apply]`. Simplify using `only [mulVec, dotProduct, this, Pi.single_apply, eq_comm]`.

Establish `h3` using `congrFun h2 j`. Simplify using `only [Matrix.mulVec_diagonal, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one] at h3`. Conclude with `⟨_, h3.symm⟩`. Use `⟨lam, a, y, hlamε, fun l => hεT _ (hyT l), hlamy, hdvd, hprod, hspan⟩` and prove the remaining obligations.
-/
theorem block (hv : v.Integers R) {ι κ' : Type} [Fintype ι] [DecidableEq ι] [Fintype κ']
    [DecidableEq κ'] (Φ : Matrix κ' ι R)
    (ε : Matrix ι ι R) (hε : ε * ε = ε) (Pq : Matrix κ' κ' R) (Qs : Submodule R (κ' → R))
    (hPqmem : ∀ w, Pq *ᵥ w ∈ Qs) (hPqid : ∀ w ∈ Qs, Pq *ᵥ w = w) (hcomm : Φ * ε = Pq * Φ)
    (n : ℕ) (hnT : Module.finrank R (LinearMap.range (Matrix.mulVecLin ε)) = n)
    (hnQ : Module.finrank R Qs = n) (X : NNReal)
    (hX : HasLen v R (Qs ⧸ ((LinearMap.range (Matrix.mulVecLin ε)).map (Matrix.mulVecLin Φ)).comap
      Qs.subtype) X)
    (cp : R) (hcp : ∀ w : ι → R, w ᵥ* ε = w → ∃ u : κ' → R, cp • w = u ᵥ* (Φ * ε)) :
    ∃ (lam : Fin n → ι → R) (a : Fin n → R) (y : Fin n → ι → R),
      (∀ j, lam j ᵥ* ε = lam j) ∧ (∀ l, ε *ᵥ y l = y l) ∧
      (∀ j l, lam j ⬝ᵥ y l = if j = l then 1 else 0) ∧ (∀ j, ∃ c, cp = a j * c) ∧
      ∏ j, v (algebraMap R C (a j)) = X ∧
      Submodule.span R (Set.range fun k => (Φ * ε) k) =
        Submodule.span R (Set.range fun j => a j • lam j) := by
  classical
  have : IsDomain R := hv.hom_inj.isDomain
  have := ValuationRing.of_integers v hv
  set T := LinearMap.range (Matrix.mulVecLin ε) with hT
  have hQeq : Qs = LinearMap.range (Matrix.mulVecLin Pq) :=
    le_antisymm (fun w hw => ⟨w, hPqid w hw⟩) (by rintro _ ⟨w, rfl⟩; exact hPqmem w)
  have hTfg : T.FG := by rw [hT, LinearMap.range_eq_map]; exact Module.Finite.fg_top.map _
  have hQfg : Qs.FG := by rw [hQeq, LinearMap.range_eq_map]; exact Module.Finite.fg_top.map _
  have htf : ∀ {α : Type} (S : Submodule R (α → R)) (r : R) (x : S), r ≠ 0 → r • x = 0 → x = 0 := by
    rintro α S r ⟨x, hx⟩ hr h
    apply Subtype.ext
    funext i
    have := congrFun (congrArg Subtype.val h) i
    simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, Submodule.coe_zero,
      Pi.zero_apply] at this
    exact (mul_eq_zero.1 this).resolve_left hr
  have : Module.Finite R T := Module.Finite.iff_fg.2 hTfg
  have : Module.Finite R Qs := Module.Finite.iff_fg.2 hQfg
  have : Module.Free R T := L2.SecondCohomologyLattice.free_of_finite_torsionFree T (htf T)
  have : Module.Free R Qs := L2.SecondCohomologyLattice.free_of_finite_torsionFree Qs (htf Qs)
  set β := Module.finBasisOfFinrankEq R T hnT with hβ
  set γ := Module.finBasisOfFinrankEq R Qs hnQ with hγ
  have hεT : ∀ t ∈ T, ε *ᵥ t = t := by
    rintro _ ⟨x, rfl⟩
    show ε *ᵥ (ε *ᵥ x) = ε *ᵥ x
    rw [mulVec_mulVec, hε]
  have hΦT : ∀ t : T, Φ *ᵥ (t : ι → R) ∈ Qs := by
    rintro ⟨_, x, rfl⟩
    show Φ *ᵥ (ε *ᵥ x) ∈ Qs
    rw [mulVec_mulVec, hcomm, ← mulVec_mulVec]
    exact hPqmem _
  set Φi : T →ₗ[R] Qs :=
    LinearMap.codRestrict Qs ((Matrix.mulVecLin Φ).comp T.subtype) hΦT with hΦi
  have hΦiapp : ∀ t : T, ((Φi t : Qs) : κ' → R) = Φ *ᵥ (t : ι → R) := fun _ => rfl
  set M := LinearMap.toMatrix β γ Φi with hM

  have hrange : ((T.map (Matrix.mulVecLin Φ)).comap Qs.subtype) = LinearMap.range Φi := by
    ext q
    simp only [Submodule.mem_comap, Submodule.mem_map, LinearMap.mem_range]
    constructor
    · rintro ⟨t, ht, htq⟩
      exact ⟨⟨t, ht⟩, Subtype.ext htq⟩
    · rintro ⟨t, rfl⟩
      exact ⟨t, t.2, rfl⟩
  have hkey : ∀ t : T, γ.equivFun (Φi t) = M *ᵥ β.equivFun t := by
    intro t
    simp only [Module.Basis.equivFun_apply]
    rw [hM, LinearMap.toMatrix_mulVec_repr]
  have hmapM : (LinearMap.range Φi).map γ.equivFun.toLinearMap =
      LinearMap.range (Matrix.mulVecLin M) := by
    ext z
    constructor
    · rintro ⟨_, ⟨t, rfl⟩, rfl⟩
      exact ⟨β.equivFun t, (hkey t).symm⟩
    · rintro ⟨c, rfl⟩
      refine ⟨Φi (β.equivFun.symm c), ⟨_, rfl⟩, ?_⟩
      show γ.equivFun (Φi (β.equivFun.symm c)) = M *ᵥ c
      rw [hkey, LinearEquiv.apply_symm_apply]
  have hLen : HasLen v R (Qs ⧸ ((T.map (Matrix.mulVecLin Φ)).comap Qs.subtype))
      (v (algebraMap R C M.det)) := by
    obtain ⟨m', c', ⟨f⟩, hf⟩ := Smith.hasLen_coker_det (C := C) (v := v) hv M
    exact ⟨m', c', ⟨((Submodule.quotEquivOfEq _ _ hrange).trans
      (Submodule.Quotient.equiv _ _ γ.equivFun hmapM)).trans f⟩, hf⟩
  have hXM : X = v (algebraMap R C M.det) := hasLen_unique hv hX hLen

  obtain ⟨P, Q', a, hP, hQ', hD⟩ := Smith.smith_mat hv n n Mᵀ
  have hdiag : P * Mᵀ * Q' = Matrix.diagonal a := by
    ext j k
    rw [hD, Matrix.diagonal_apply]
    by_cases h : j = k
    · subst h; simp
    · have : (k : ℕ) ≠ (j : ℕ) := fun e => h (Fin.ext e.symm)
      simp [h, this]
  have hprod : ∏ j, v (algebraMap R C (a j)) = X := by
    rw [hXM, ← map_prod, ← map_prod, ← Matrix.det_diagonal, ← hdiag, Matrix.det_mul,
      Matrix.det_mul, Matrix.det_transpose, map_mul, map_mul, map_mul, map_mul,
      hv.one_of_isUnit hP, hv.one_of_isUnit hQ', one_mul, mul_one]
  set Pi' := P⁻¹ with hPi'
  have hPP : P * Pi' = 1 := Matrix.mul_nonsing_inv P hP
  have hPP' : Pi' * P = 1 := Matrix.nonsing_inv_mul P hP

  set ℓ : Fin n → (ι → R) →ₗ[R] R :=
    fun l => (β.coord l).comp (Matrix.mulVecLin ε).rangeRestrict with hℓ
  have hℓε : ∀ l x, ℓ l (ε *ᵥ x) = ℓ l x := by
    intro l x
    simp only [hℓ, LinearMap.coe_comp, Function.comp_apply]
    congr 1
    apply Subtype.ext
    show ε *ᵥ (ε *ᵥ x) = ε *ᵥ x
    rw [mulVec_mulVec, hε]
  have hℓβ : ∀ l m, ℓ l (β m : ι → R) = if m = l then 1 else 0 := by
    intro l m
    simp only [hℓ, LinearMap.coe_comp, Function.comp_apply]
    have : (Matrix.mulVecLin ε).rangeRestrict (β m : ι → R) = β m := by
      apply Subtype.ext
      show ε *ᵥ (β m : ι → R) = β m
      exact hεT _ (β m).2
    rw [this, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
  set lam : Fin n → ι → R := fun j k => ∑ l, Pi' l j * ℓ l (Pi.single k 1) with hlam
  have hlamdot : ∀ j x, lam j ⬝ᵥ x = ∑ l, Pi' l j * ℓ l x := by
    intro j x
    have e : lam j = fun k => (∑ l, Pi' l j • ℓ l) (Pi.single k 1) := by
      funext k; simp [hlam, LinearMap.sum_apply]
    rw [e, dot_single]
    simp [LinearMap.sum_apply]
  set y : Fin n → ι → R := fun l => ∑ m, P l m • (β m : ι → R) with hy
  have hyT : ∀ l, y l ∈ T := fun l =>
    Submodule.sum_mem _ fun m _ => Submodule.smul_mem _ _ (β m).2

  have hdotε : ∀ (w : ι → R) x, (w ᵥ* ε) ⬝ᵥ x = w ⬝ᵥ (ε *ᵥ x) := fun w x =>
    (Matrix.dotProduct_mulVec w ε x).symm
  have hlamε : ∀ j, lam j ᵥ* ε = lam j := by
    intro j
    apply eq_of_dot
    intro x
    rw [hdotε, hlamdot, hlamdot]
    simp only [hℓε]
  have hlamy : ∀ j l, lam j ⬝ᵥ y l = if j = l then 1 else 0 := by
    intro j l
    rw [hlamdot]
    have e1 : ∀ l', ℓ l' (y l) = P l l' := by
      intro l'
      simp only [hy, map_sum, map_smul, hℓβ, smul_eq_mul, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, if_true]
    simp only [e1]
    have := congrFun (congrFun hPP l) j
    rw [Matrix.mul_apply, Matrix.one_apply] at this
    have h2 : (if j = l then (1 : R) else 0) = if l = j then 1 else 0 := by
      by_cases h : j = l <;> simp [h, eq_comm]
    rw [h2, ← this]
    exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

  let K : (ι → R) →ₗ[R] (Fin n → R) :=
    { toFun := fun w l => w ⬝ᵥ (β l : ι → R)
      map_add' := fun w w' => by funext l; simp [add_dotProduct]
      map_smul' := fun c w => by funext l; simp [smul_dotProduct] }
  have hKapp : ∀ w l, K w l = w ⬝ᵥ (β l : ι → R) := fun _ _ => rfl
  have hKlam : ∀ j, K (lam j) = fun l => Pi' l j := by
    intro j; funext l
    rw [hKapp, hlamdot]
    simp only [hℓβ, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  set cvec : κ' → Fin n → R := fun k m => (γ m : κ' → R) k with hcvec
  have hKrow : ∀ k, K ((Φ * ε) k) = Mᵀ *ᵥ cvec k := by
    intro k; funext l
    rw [hKapp]
    have e1 : (Φ * ε) k ⬝ᵥ (β l : ι → R) = ((Φ * ε) *ᵥ (β l : ι → R)) k := rfl
    rw [e1, ← mulVec_mulVec, hεT _ (β l).2, ← hΦiapp]
    have e2 : ((Φi (β l) : Qs) : κ' → R) = ∑ m, M m l • (γ m : κ' → R) := by
      have h := γ.sum_repr (Φi (β l))
      rw [← h]
      simp only [Submodule.coe_sum, Submodule.coe_smul, hM, LinearMap.toMatrix_apply]
    rw [e2, Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul, mulVec, dotProduct, transpose_apply, hcvec]

  set gs : Fin n → κ' → R := fun m k => γ.coord m ⟨Pq *ᵥ Pi.single k 1, hPqmem _⟩ with hgs
  have hgsc : ∀ m m', ∑ k, gs m k * cvec k m' = if m' = m then 1 else 0 := by
    intro m m'
    let f : (κ' → R) →ₗ[R] R := (γ.coord m).comp
      (LinearMap.codRestrict Qs (Matrix.mulVecLin Pq) hPqmem)
    have hf : ∀ k, f (Pi.single k 1) = gs m k := fun k => rfl
    have h1 : (fun k => f (Pi.single k 1)) ⬝ᵥ (γ m' : κ' → R) = f (γ m') := dot_single f _
    have h2 : f (γ m') = if m' = m then 1 else 0 := by
      have : LinearMap.codRestrict Qs (Matrix.mulVecLin Pq) hPqmem (γ m' : κ' → R) = γ m' :=
        Subtype.ext (hPqid _ (γ m').2)
      simp only [f, LinearMap.coe_comp, Function.comp_apply, this, Module.Basis.coord_apply,
        Module.Basis.repr_self, Finsupp.single_apply]
    rw [← h2, ← h1]
    simp only [dotProduct, hf, hcvec]

  have hMrange : ∀ z, Mᵀ *ᵥ z ∈ Submodule.span R (Set.range fun k => Mᵀ *ᵥ cvec k) := by
    intro z
    have hz : z = ∑ k, (∑ m, z m * gs m k) • cvec k := by
      funext m'
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
      rw [Finset.sum_comm]
      simp only [mul_assoc, ← Finset.mul_sum, hgsc, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [hz, mulVec_sum]
    exact Submodule.sum_mem _ fun k _ => by
      rw [mulVec_smul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  have hmapN : (Submodule.span R (Set.range fun k => (Φ * ε) k)).map K =
      LinearMap.range (Matrix.mulVecLin Mᵀ) := by
    rw [Submodule.map_span, ← Set.range_comp]
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      exact ⟨cvec k, (hKrow k).symm⟩
    · rintro _ ⟨z, rfl⟩
      have e : (K ∘ fun k => (Φ * ε) k) = fun k => Mᵀ *ᵥ cvec k := funext hKrow
      rw [e]
      exact hMrange z
  have hmapS : (Submodule.span R (Set.range fun j => a j • lam j)).map K =
      LinearMap.range (Matrix.mulVecLin Mᵀ) := by
    rw [Submodule.map_span, ← Set.range_comp]
    have e1 : (K ∘ fun j => a j • lam j) = fun j => fun l => (Pi' * Matrix.diagonal a) l j := by
      funext j l
      simp only [Function.comp_apply, map_smul, hKlam, Pi.smul_apply, smul_eq_mul,
        Matrix.mul_diagonal]
      ring
    rw [e1]
    have e2 : Pi' * Matrix.diagonal a = Mᵀ * Q' := by
      rw [← hdiag, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hPP', Matrix.one_mul]
    rw [e2]
    have e3 : Submodule.span R (Set.range fun j => fun l => (Mᵀ * Q') l j) =
        LinearMap.range (Matrix.mulVecLin (Mᵀ * Q')) := by
      rw [Matrix.range_mulVecLin]; rfl
    rw [e3]
    apply le_antisymm
    · rintro _ ⟨z, rfl⟩; exact ⟨Q' *ᵥ z, by simp [mulVec_mulVec]⟩
    · rintro _ ⟨z, rfl⟩
      refine ⟨Q'⁻¹ *ᵥ z, ?_⟩
      show (Mᵀ * Q') *ᵥ (Q'⁻¹ *ᵥ z) = Mᵀ *ᵥ z
      rw [mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hQ', Matrix.mul_one]

  have hKinj : ∀ w w', w ᵥ* ε = w → w' ᵥ* ε = w' → K w = K w' → w = w' := by
    intro w w' hw hw' hK
    have hT0 : ∀ t ∈ T, w ⬝ᵥ t = w' ⬝ᵥ t := by
      intro t ht
      have : t = ∑ l, β.repr ⟨t, ht⟩ l • (β l : ι → R) := by
        have h := congrArg Subtype.val (β.sum_repr ⟨t, ht⟩)
        simp only [Submodule.coe_sum, Submodule.coe_smul] at h
        exact h.symm
      rw [this, dotProduct_sum, dotProduct_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [dotProduct_smul, dotProduct_smul]
      have := congrFun hK l
      rw [hKapp, hKapp] at this
      rw [this]
    apply eq_of_dot
    intro x
    rw [← hw, ← hw', hdotε, hdotε]
    exact hT0 _ ⟨x, rfl⟩
  have hrowε : ∀ k, (Φ * ε) k ᵥ* ε = (Φ * ε) k := by
    intro k
    funext k'
    simp only [vecMul, dotProduct]
    have := congrFun (congrFun (show Φ * ε * ε = Φ * ε by rw [Matrix.mul_assoc, hε]) k) k'
    rw [Matrix.mul_apply] at this
    exact this
  have hNle : ∀ w ∈ Submodule.span R (Set.range fun k => (Φ * ε) k), w ᵥ* ε = w := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem w hw => obtain ⟨k, rfl⟩ := hw; exact hrowε k
    | zero => simp
    | add x y _ _ hx hy => rw [add_vecMul, hx, hy]
    | smul c x _ hx => rw [smul_vecMul, hx]
  have hSle : ∀ w ∈ Submodule.span R (Set.range fun j => a j • lam j), w ᵥ* ε = w := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem w hw => obtain ⟨j, rfl⟩ := hw; rw [smul_vecMul, hlamε]
    | zero => simp
    | add x y _ _ hx hy => rw [add_vecMul, hx, hy]
    | smul c x _ hx => rw [smul_vecMul, hx]
  have hspan : Submodule.span R (Set.range fun k => (Φ * ε) k) =
      Submodule.span R (Set.range fun j => a j • lam j) := by
    apply le_antisymm
    · intro w hw
      have hKw : K w ∈ (Submodule.span R (Set.range fun j => a j • lam j)).map K := by
        rw [hmapS, ← hmapN]; exact ⟨w, hw, rfl⟩
      obtain ⟨s, hs, hsw⟩ := hKw
      rw [← hKinj s w (hSle s hs) (hNle w hw) hsw]
      exact hs
    · intro w hw
      have hKw : K w ∈ (Submodule.span R (Set.range fun k => (Φ * ε) k)).map K := by
        rw [hmapN, ← hmapS]; exact ⟨w, hw, rfl⟩
      obtain ⟨s, hs, hsw⟩ := hKw
      rw [← hKinj s w (hNle s hs) (hSle w hw) hsw]
      exact hs

  have hdvd : ∀ j, ∃ c, cp = a j * c := by
    intro j
    obtain ⟨u, hu⟩ := hcp (lam j) (hlamε j)
    have hmem : cp • lam j ∈ Submodule.span R (Set.range fun k => (Φ * ε) k) := by
      rw [hu]
      have e : u ᵥ* (Φ * ε) = ∑ k, u k • (Φ * ε) k := by
        funext k'; simp [vecMul, dotProduct, Finset.sum_apply]
      rw [e]
      exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
    have hK := Submodule.mem_map_of_mem (f := K) hmem
    rw [hmapN] at hK
    obtain ⟨z, hz⟩ := hK

    have hz' : Mᵀ *ᵥ z = cp • fun l => Pi' l j := by
      rw [← hKlam, ← map_smul]; exact hz
    have h2 : Matrix.diagonal a *ᵥ (Q'⁻¹ *ᵥ z) = cp • Pi.single j 1 := by
      rw [← hdiag, mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hQ',
        Matrix.mul_one, ← mulVec_mulVec]
      show P *ᵥ (Mᵀ *ᵥ z) = _
      rw [hz']
      funext l
      simp only [mulVec_smul, Pi.smul_apply, smul_eq_mul]
      have := congrFun (congrFun hPP l) j
      rw [Matrix.mul_apply, Matrix.one_apply] at this
      simp only [mulVec, dotProduct, this, Pi.single_apply, eq_comm]
    have h3 := congrFun h2 j
    simp only [Matrix.mulVec_diagonal, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul,
      mul_one] at h3
    exact ⟨_, h3.symm⟩
  refine ⟨lam, a, y, hlamε, fun l => hεT _ (hyT l), hlamy, hdvd, hprod, hspan⟩

end ReciprocityTheory.PGsh.Up.ED
