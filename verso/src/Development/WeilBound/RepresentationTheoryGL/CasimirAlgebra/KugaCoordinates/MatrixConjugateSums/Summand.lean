import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.IsStarRep
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OneParameterSubgroupExists

noncomputable section

set_option linter.unusedSectionVars false

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh
open scoped InnerProductSpace

namespace PositivityTheory.Rg.Cz.J

section LinAlg

variable {I G : Type} [Fintype I] [DecidableEq I] (T : G → Matrix I I ℂ)

def Stab (S : Submodule ℂ (EuclideanSpace ℂ I)) : Prop :=
  ∀ g, ∀ v ∈ S, WithLp.toLp 2 (T g *ᵥ v.ofLp) ∈ S

/- English proof (translation)
Rewrite using `[EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct, star_mulVec, conjTranspose_conjTranspose, dotProduct_comm x.ofLp, ← dotProduct_mulVec, dotProduct_comm]`.
-/
theorem inner_mulVec (M : Matrix I I ℂ) (s x : EuclideanSpace ℂ I) :
    ⟪s, WithLp.toLp 2 (M *ᵥ x.ofLp)⟫_ℂ = ⟪WithLp.toLp 2 (Mᴴ *ᵥ s.ofLp), x⟫_ℂ := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct, star_mulVec,
    conjTranspose_conjTranspose, dotProduct_comm x.ofLp, ← dotProduct_mulVec, dotProduct_comm]

variable {T}

/- English proof (translation)
Introduce `g v hv`. Rewrite `hv`, the goal using `[Submodule.mem_orthogonal]`. Introduce `u hu`. Take `⟨g', hg'⟩` from `hadj g`. Rewrite using `[inner_mulVec, ← hg']`.

Conclude with `hv _ (hS g' u hu)`.
-/
theorem stab_orth (hadj : ∀ g, ∃ g', T g' = (T g)ᴴ) {S : Submodule ℂ (EuclideanSpace ℂ I)} (hS : Stab T S) :
    Stab T Sᗮ := by
  intro g v hv
  rw [Submodule.mem_orthogonal] at hv ⊢
  intro u hu
  obtain ⟨g', hg'⟩ := hadj g
  rw [inner_mulVec, ← hg']
  exact hv _ (hS g' u hu)

/- English proof (translation)
Introduce `g v hv` and use `⟨hA g v hv.1, hB g v hv.2⟩`.
-/
theorem stab_inf {A B : Submodule ℂ (EuclideanSpace ℂ I)} (hA : Stab T A) (hB : Stab T B) : Stab T (A ⊓ B) :=
  fun g v hv => ⟨hA g v hv.1, hB g v hv.2⟩

variable (T) in

def Good (D : Submodule ℂ (I → ℂ)) (v₀ : I → ℂ) (S : Submodule ℂ (EuclideanSpace ℂ I)) : Prop :=
  Stab T S ∧ (∀ v ∈ S, v.ofLp ∈ D) ∧ ∃ w ∈ S, ⟪w, WithLp.toLp 2 v₀⟫_ℂ ≠ 0

/- English proof (translation)
Set `D' : Submodule ℂ (EuclideanSpace ℂ I)` to `D.comap (WithLp.linearEquiv 2 ℂ (I → ℂ)).toLinearMap`. Establish `hD' : Good T D v₀ D'`. Use `⟨fun g v hv => ?_, fun v hv => hv, WithLp.toLp 2 v₀, hv, ?_⟩` and prove the remaining obligations. Conclude with `hD g _ hv`. Rewrite using `[inner_self_ne_zero]`.

Introduce `h`. Conclude with `h0 (congrArg WithLp.ofLp h)`. Establish `hex : ∃ n, ∃ S, Good T D v₀ S ∧ Module.finrank ℂ S = n` using `⟨_, D', hD', rfl⟩`. Take `⟨S, hS, hn⟩` from `Nat.find_spec hex`. Conclude with `⟨S, hS, fun S' h' => hn ▸ Nat.find_min' hex ⟨S', h', rfl⟩⟩`.
-/
theorem exists_min {D : Submodule ℂ (I → ℂ)} (hD : ∀ g, ∀ v ∈ D, T g *ᵥ v ∈ D) {v₀ : I → ℂ} (hv : v₀ ∈ D)
    (h0 : v₀ ≠ 0) :
    ∃ S, Good T D v₀ S ∧ ∀ S', Good T D v₀ S' → Module.finrank ℂ S ≤ Module.finrank ℂ S' := by
  classical
  let D' : Submodule ℂ (EuclideanSpace ℂ I) := D.comap (WithLp.linearEquiv 2 ℂ (I → ℂ)).toLinearMap
  have hD' : Good T D v₀ D' := by
    refine ⟨fun g v hv => ?_, fun v hv => hv, WithLp.toLp 2 v₀, hv, ?_⟩
    · exact hD g _ hv
    · rw [inner_self_ne_zero]
      intro h; exact h0 (congrArg WithLp.ofLp h)
  have hex : ∃ n, ∃ S, Good T D v₀ S ∧ Module.finrank ℂ S = n := ⟨_, D', hD', rfl⟩
  obtain ⟨S, hS, hn⟩ := Nat.find_spec hex
  exact ⟨S, hS, fun S' h' => hn ▸ Nat.find_min' hex ⟨S', h', rfl⟩⟩

/- English proof (translation)
Distinguish the cases in `hg : ∃ w ∈ A, ⟪w, WithLp.toLp 2 v₀⟫_ℂ ≠ 0`. Conclude with `Or.inr (Submodule.eq_of_le_of_finrank_le hAS (hmin A ⟨hA, fun v hv => hS.2.1 v (hAS hv), hg⟩))`. Use `left push_neg at hg`. Establish `hB : Stab T (Aᗮ ⊓ S)` using `stab_inf (stab_orth hadj hA) hS.1`. Establish `hsum` using `Submodule.finrank_add_inf_finrank_orthogonal hAS`.

Distinguish the cases in `hg' : ∃ w ∈ Aᗮ ⊓ S, ⟪w, WithLp.toLp 2 v₀⟫_ℂ ≠ 0`. Use `hmin _ ⟨hB, fun v hv => hS.2.1 v hv.2, hg'⟩` as an intermediate fact. Conclude with `Submodule.finrank_eq_zero.1 (by omega)`. Use `exfalso push_neg at hg'`. Take `⟨w, hw, hne⟩` from `hS.2.2`.

Rewrite `hw` using `[← Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection hAS]`. Take `⟨x, hx, y, hy, rfl⟩` from `Submodule.mem_sup.1 hw`. Rewrite `hne` using `[inner_add_left, hg x hx, hg' y hy, add_zero]`. Conclude with `hne rfl`.
-/
theorem min_irred (hadj : ∀ g, ∃ g', T g' = (T g)ᴴ) {D : Submodule ℂ (I → ℂ)} {v₀ : I → ℂ}
    {S : Submodule ℂ (EuclideanSpace ℂ I)} (hS : Good T D v₀ S)
    (hmin : ∀ S', Good T D v₀ S' → Module.finrank ℂ S ≤ Module.finrank ℂ S')
    {A : Submodule ℂ (EuclideanSpace ℂ I)} (hA : Stab T A) (hAS : A ≤ S) : A = ⊥ ∨ A = S := by
  by_cases hg : ∃ w ∈ A, ⟪w, WithLp.toLp 2 v₀⟫_ℂ ≠ 0
  · exact Or.inr (Submodule.eq_of_le_of_finrank_le hAS (hmin A ⟨hA, fun v hv => hS.2.1 v (hAS hv), hg⟩))
  · left
    push_neg at hg
    have hB : Stab T (Aᗮ ⊓ S) := stab_inf (stab_orth hadj hA) hS.1
    have hsum := Submodule.finrank_add_inf_finrank_orthogonal hAS
    by_cases hg' : ∃ w ∈ Aᗮ ⊓ S, ⟪w, WithLp.toLp 2 v₀⟫_ℂ ≠ 0
    · have := hmin _ ⟨hB, fun v hv => hS.2.1 v hv.2, hg'⟩
      exact Submodule.finrank_eq_zero.1 (by omega)
    · exfalso
      push_neg at hg'
      obtain ⟨w, hw, hne⟩ := hS.2.2
      rw [← Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection hAS] at hw
      obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 hw
      rw [inner_add_left, hg x hx, hg' y hy, add_zero] at hne
      exact hne rfl

def Jm (S : Submodule ℂ (EuclideanSpace ℂ I)) : Matrix I (Fin (Module.finrank ℂ S)) ℂ :=
  Matrix.of fun i k => ((stdOrthonormalBasis ℂ S k : S) : EuclideanSpace ℂ I).ofLp i

/- English proof (translation)
Use extensionality with `i`. Simplify using `[Jm, mulVec, dotProduct, mul_comm]`.
-/
theorem Jm_mulVec (S : Submodule ℂ (EuclideanSpace ℂ I)) (w : Fin (Module.finrank ℂ S) → ℂ) :
    Jm S *ᵥ w = (∑ k, w k • ((stdOrthonormalBasis ℂ S k : S) : EuclideanSpace ℂ I)).ofLp := by
  ext i
  simp [Jm, mulVec, dotProduct, mul_comm]

/- English proof (translation)
Rewrite using `[Jm_mulVec, WithLp.toLp_ofLp]`. Conclude with `Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (stdOrthonormalBasis ℂ S k).2`.
-/
theorem Jm_mulVec_mem (S : Submodule ℂ (EuclideanSpace ℂ I)) (w : Fin (Module.finrank ℂ S) → ℂ) :
    WithLp.toLp 2 (Jm S *ᵥ w) ∈ S := by
  rw [Jm_mulVec, WithLp.toLp_ofLp]
  exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (stdOrthonormalBasis ℂ S k).2

/- English proof (translation)
Use extensionality with `k`. Rewrite using `[EuclideanSpace.inner_eq_star_dotProduct]`. Simplify using `[Jm, mulVec, dotProduct, mul_comm]`.
-/
theorem Jm_conj_mulVec (S : Submodule ℂ (EuclideanSpace ℂ I)) (x : EuclideanSpace ℂ I) :
    (Jm S)ᴴ *ᵥ x.ofLp = fun k => ⟪((stdOrthonormalBasis ℂ S k : S) : EuclideanSpace ℂ I), x⟫_ℂ := by
  ext k
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp [Jm, mulVec, dotProduct, mul_comm]

/- English proof (translation)
Use extensionality with `k l`. Establish `h` using `(stdOrthonormalBasis ℂ S).inner_eq_ite k l`. Rewrite `h` using `[Submodule.coe_inner, EuclideanSpace.inner_eq_star_dotProduct]`. Simplify using `only [dotProduct, Pi.star_apply] at h`. Rewrite using `[Matrix.mul_apply, Matrix.one_apply, ← h]`.

Simplify using `[Jm, mul_comm]`.
-/
theorem Jm_conj_mul (S : Submodule ℂ (EuclideanSpace ℂ I)) : (Jm S)ᴴ * Jm S = 1 := by
  ext k l
  have h := (stdOrthonormalBasis ℂ S).inner_eq_ite k l
  rw [Submodule.coe_inner, EuclideanSpace.inner_eq_star_dotProduct] at h
  simp only [dotProduct, Pi.star_apply] at h
  rw [Matrix.mul_apply, Matrix.one_apply, ← h]
  simp [Jm, mul_comm]

/- English proof (translation)
Rewrite using `[Jm_conj_mulVec, Jm_mulVec]`. Use `congr 1`. Establish `h` using `congrArg (fun z : S => (z : EuclideanSpace ℂ I)) ((stdOrthonormalBasis ℂ S).sum_repr' ⟨u, hu⟩)`. Simplify `h` using `[Submodule.coe_inner]`.
-/
theorem Jm_proj (S : Submodule ℂ (EuclideanSpace ℂ I)) {u : EuclideanSpace ℂ I} (hu : u ∈ S) :
    Jm S *ᵥ ((Jm S)ᴴ *ᵥ u.ofLp) = u.ofLp := by
  rw [Jm_conj_mulVec, Jm_mulVec]
  congr 1
  have h := congrArg (fun z : S => (z : EuclideanSpace ℂ I)) ((stdOrthonormalBasis ℂ S).sum_repr' ⟨u, hu⟩)
  simpa [Submodule.coe_inner] using h

/- English proof (translation)
Use `Matrix.toLin'.injective (LinearMap.ext fun w => ?_)` and prove the remaining obligations. Simplify using `only [Matrix.toLin'_apply, ← Matrix.mulVec_mulVec]`. Establish `h` using `Jm_proj S (hM _ (Jm_mulVec_mem S w))`. Simplify using `using h`.
-/
theorem Jm_colstab (S : Submodule ℂ (EuclideanSpace ℂ I)) (M : Matrix I I ℂ)
    (hM : ∀ v ∈ S, WithLp.toLp 2 (M *ᵥ v.ofLp) ∈ S) : Jm S * ((Jm S)ᴴ * (M * Jm S)) = M * Jm S := by
  refine Matrix.toLin'.injective (LinearMap.ext fun w => ?_)
  simp only [Matrix.toLin'_apply, ← Matrix.mulVec_mulVec]
  have h := Jm_proj S (hM _ (Jm_mulVec_mem S w))
  simpa using h

end LinAlg

section Main

/- English proof (translation)
Introduce `E _ _ a I _ _ R dR hR D hD v₀ hv₀ h0`. Establish `hadj : ∀ y, ∃ y', R y' = (R y)ᴴ` using `fun y => ⟨star y, hR.star y⟩`. Take `⟨S, hS, hmin⟩` from `exists_min (T := R) hD hv₀ h0`. Establish `hcol : ∀ y, Jm S * ((Jm S)ᴴ * (R y * Jm S)) = R y * Jm S` using `fun y => Jm_colstab S (R y) (hS.1 y)`. Set `mat : GL (Fin a) (Cinf E) →* Matrix (Fin (Module.finrank ℂ S)) (Fin (Module.finrank ℂ S)) ℂ` to `{ toFun := fun y => (Jm S)ᴴ * R y * Jm S map_one' := by simp only [hR.one, Matrix.mul_one, Jm_conj_mul] map_mul' := fun y z => by`.

Simplify using `only [hR.mul]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hcol z]`. Simplify using `only [Matrix.mul_assoc]`. Use `_ = _ := by simp only [Matrix.mul_assoc] }`.

Establish `hRJ : ∀ y, R y * Jm S = Jm S * mat y` using `fun y => by`. Rewrite using `[← hcol y]`. Simplify using `only [mat, MonoidHom.coe_mk, OneHom.coe_mk, Matrix.mul_assoc]`. Establish `hreg : ∀ k l, (fun y => mat y k l) ∈ regFun E a` using `fun k l => by`. Establish `e : (fun y => mat y k l) = ∑ m, ∑ i, (star (Jm S i k) * Jm S m l) • (fun y : GL (Fin a) (Cinf E) => R y i m)`.

Use function extensionality and compare the values at `y`. Simplify using `only [mat, MonoidHom.coe_mk, OneHom.coe_mk, Matrix.mul_apply, conjTranspose_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]`. Conclude with `Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun i _ => by ring`. Rewrite using `[e]`. Conclude with `Subalgebra.sum_mem _ fun m _ => Subalgebra.sum_mem _ fun i _ => Subalgebra.smul_mem _ (hR.reg i m) _`.

Take `⟨w₁, hw₁, hne₁⟩` from `hS.2.2`. Establish `hpos : 0 < Module.finrank ℂ S`. Use `Nat.pos_of_ne_zero fun h => hne₁ ?_` and prove the remaining obligations. Establish `: S = ⊥` using `Submodule.finrank_eq_zero.1 h`. Substitute `this` using the available equality.

Rewrite using `[(Submodule.mem_bot ℂ).1 hw₁, inner_zero_left]`. Set `f : (Fin (Module.finrank ℂ S) → ℂ) →ₗ[ℂ] EuclideanSpace ℂ I` to `(WithLp.linearEquiv 2 ℂ (I → ℂ)).symm.toLinearMap ∘ₗ Matrix.toLin' (Jm S)`. Establish `hf : ∀ w, f w = WithLp.toLp 2 (Jm S *ᵥ w)` using `fun w => rfl`. Establish `hfi : Function.Injective f` using `fun w w' h => by`. Rewrite `h` using `[hf, hf]`.

Establish `h2` using `congrArg (fun x => (Jm S)ᴴ *ᵥ x) (congrArg WithLp.ofLp h)`. Simplify `h2` using `[Matrix.mulVec_mulVec, Jm_conj_mul]`. Establish `hirr : ∀ W : Submodule ℂ (Fin (Module.finrank ℂ S) → ℂ), (∀ y, ∀ v ∈ W, mat y *ᵥ v ∈ W) → W = ⊥ ∨ W = ⊤` using `fun W hW => by`. Establish `hA : Stab R (W.map f)`. Introduce and unpack `y _ ⟨w, hw, rfl⟩`.

Use `⟨mat y *ᵥ w, hW y w hw, ?_⟩` and prove the remaining obligations. Rewrite using `[hf, hf]`. Simplify using `only [Matrix.mulVec_mulVec, ← hRJ]`. Establish `hAS : W.map f ≤ S`. Introduce and unpack `_ ⟨w, -, rfl⟩`.

Conclude with `Jm_mulVec_mem S w`. Break down `min_irred hadj hS hmin hA hAS with h | h` into its components or cases. Use `left`. Conclude with `Submodule.map_injective_of_injective hfi (h.trans (Submodule.map_bot f).symm)`. Use `right`.

Apply `Submodule.eq_top_of_finrank_eq` to reduce the goal to its premises. Rewrite using `[Module.finrank_fin_fun, LinearEquiv.finrank_eq (Submodule.equivMapOfInjective f hfi W), h]`. Set `Ξ : AlgRep E a` to `⟨Module.finrank ℂ S, mat, hreg, hpos, hirr⟩`. Use `⟨Ξ, Jm S, Jm_conj_mul S, fun w => hS.2.1 _ (Jm_mulVec_mem S w), ?_, hRJ, ?_, ?_⟩` and prove the remaining obligations. Introduce `h`.

Apply `hne₁` to reduce the goal to its premises. Establish `hc` using `Jm_conj_mulVec S (WithLp.toLp 2 v₀)`. Rewrite `hc` using `[WithLp.ofLp_toLp, h]`. Establish `hw` using `congrArg (fun z : S => (z : EuclideanSpace ℂ I)) ((stdOrthonormalBasis ℂ S).sum_repr' ⟨w₁, hw₁⟩)`. Simplify using `only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_inner] at hw`.

Rewrite using `[← hw, sum_inner]`. Use `Finset.sum_eq_zero fun k _ => ?_` and prove the remaining obligations. Rewrite using `[inner_smul_left, ← congrFun hc k, Pi.zero_apply, mul_zero]`. Introduce `y`. Establish `h1 : R y = (R (star y))ᴴ` using `by rw [← hR.star, star_star]`.

Establish `h2` using `congrArg conjTranspose (hRJ (star y))`. Simplify using `only [conjTranspose_mul, conjTranspose_conjTranspose, ← h1, mat, MonoidHom.coe_mk, OneHom.coe_mk] at h2`. Use `show (Jm S)ᴴ * R y = (Jm S)ᴴ * R y * Jm S * (Jm S)ᴴ`. Conclude with `h2.trans (by simp only [Matrix.mul_assoc])`. Introduce `X`.

Take `⟨c, -, hc0, -, hcX, -⟩` from `GlobalTheory.CompanionTheory.LieCurve.exists_curve E a X`. Use extensionality with `i k`. Establish `hL : HasDerivAt (fun t => (R (c t) * Jm S) i k) ((dR X * Jm S) i k) 0`. Simplify using `only [Matrix.mul_apply]`. Conclude with `HasDerivAt.fun_sum fun m _ => (hR.der c X hc0 hcX i m).mul_const _`.

Establish `hRr : HasDerivAt (fun t => (Jm S * Ξ.mat (c t)) i k) ((Jm S * Ξ.dmat X) i k) 0`. Simplify using `only [Matrix.mul_apply]`. Conclude with `HasDerivAt.fun_sum fun m _ => (Ξ.hasDerivAt_curve c X hc0 hcX m k).const_mul _`. Establish `e : (fun t => (R (c t) * Jm S) i k) = fun t => (Jm S * Ξ.mat (c t)) i k` using `funext fun t => by rw [hRJ]`. Rewrite `hL` using `[e]`.

Conclude with `hL.unique hRr`.
-/
theorem summand_holds : Summand := by
  intro E _ _ a I _ _ R dR hR D hD v₀ hv₀ h0
  have hadj : ∀ y, ∃ y', R y' = (R y)ᴴ := fun y => ⟨star y, hR.star y⟩
  obtain ⟨S, hS, hmin⟩ := exists_min (T := R) hD hv₀ h0
  have hcol : ∀ y, Jm S * ((Jm S)ᴴ * (R y * Jm S)) = R y * Jm S := fun y => Jm_colstab S (R y) (hS.1 y)
  let mat : GL (Fin a) (Cinf E) →* Matrix (Fin (Module.finrank ℂ S)) (Fin (Module.finrank ℂ S)) ℂ :=
    { toFun := fun y => (Jm S)ᴴ * R y * Jm S
      map_one' := by simp only [hR.one, Matrix.mul_one, Jm_conj_mul]
      map_mul' := fun y z => by
        simp only [hR.mul]
        calc (Jm S)ᴴ * (R y * R z) * Jm S = (Jm S)ᴴ * R y * (Jm S * ((Jm S)ᴴ * (R z * Jm S))) := by
              rw [hcol z]; simp only [Matrix.mul_assoc]
          _ = _ := by simp only [Matrix.mul_assoc] }
  have hRJ : ∀ y, R y * Jm S = Jm S * mat y := fun y => by
    rw [← hcol y]; simp only [mat, MonoidHom.coe_mk, OneHom.coe_mk, Matrix.mul_assoc]
  have hreg : ∀ k l, (fun y => mat y k l) ∈ regFun E a := fun k l => by
    have e : (fun y => mat y k l) =
        ∑ m, ∑ i, (star (Jm S i k) * Jm S m l) • (fun y : GL (Fin a) (Cinf E) => R y i m) := by
      funext y
      simp only [mat, MonoidHom.coe_mk, OneHom.coe_mk, Matrix.mul_apply, conjTranspose_apply, Finset.sum_apply,
        Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
      exact Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun i _ => by ring
    rw [e]
    exact Subalgebra.sum_mem _ fun m _ => Subalgebra.sum_mem _ fun i _ => Subalgebra.smul_mem _ (hR.reg i m) _
  obtain ⟨w₁, hw₁, hne₁⟩ := hS.2.2
  have hpos : 0 < Module.finrank ℂ S := by
    refine Nat.pos_of_ne_zero fun h => hne₁ ?_
    have : S = ⊥ := Submodule.finrank_eq_zero.1 h
    subst this
    rw [(Submodule.mem_bot ℂ).1 hw₁, inner_zero_left]
  let f : (Fin (Module.finrank ℂ S) → ℂ) →ₗ[ℂ] EuclideanSpace ℂ I :=
    (WithLp.linearEquiv 2 ℂ (I → ℂ)).symm.toLinearMap ∘ₗ Matrix.toLin' (Jm S)
  have hf : ∀ w, f w = WithLp.toLp 2 (Jm S *ᵥ w) := fun w => rfl
  have hfi : Function.Injective f := fun w w' h => by
    rw [hf, hf] at h
    have h2 := congrArg (fun x => (Jm S)ᴴ *ᵥ x) (congrArg WithLp.ofLp h)
    simpa [Matrix.mulVec_mulVec, Jm_conj_mul] using h2
  have hirr : ∀ W : Submodule ℂ (Fin (Module.finrank ℂ S) → ℂ), (∀ y, ∀ v ∈ W, mat y *ᵥ v ∈ W) →
      W = ⊥ ∨ W = ⊤ := fun W hW => by
    have hA : Stab R (W.map f) := by
      rintro y _ ⟨w, hw, rfl⟩
      refine ⟨mat y *ᵥ w, hW y w hw, ?_⟩
      rw [hf, hf]
      simp only [Matrix.mulVec_mulVec, ← hRJ]
    have hAS : W.map f ≤ S := by
      rintro _ ⟨w, -, rfl⟩
      exact Jm_mulVec_mem S w
    rcases min_irred hadj hS hmin hA hAS with h | h
    · left
      exact Submodule.map_injective_of_injective hfi (h.trans (Submodule.map_bot f).symm)
    · right
      apply Submodule.eq_top_of_finrank_eq
      rw [Module.finrank_fin_fun, LinearEquiv.finrank_eq (Submodule.equivMapOfInjective f hfi W), h]
  let Ξ : AlgRep E a := ⟨Module.finrank ℂ S, mat, hreg, hpos, hirr⟩
  refine ⟨Ξ, Jm S, Jm_conj_mul S, fun w => hS.2.1 _ (Jm_mulVec_mem S w), ?_, hRJ, ?_, ?_⟩
  · intro h
    apply hne₁
    have hc := Jm_conj_mulVec S (WithLp.toLp 2 v₀)
    rw [WithLp.ofLp_toLp, h] at hc
    have hw := congrArg (fun z : S => (z : EuclideanSpace ℂ I)) ((stdOrthonormalBasis ℂ S).sum_repr' ⟨w₁, hw₁⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_inner] at hw
    rw [← hw, sum_inner]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [inner_smul_left, ← congrFun hc k, Pi.zero_apply, mul_zero]
  · intro y
    have h1 : R y = (R (star y))ᴴ := by rw [← hR.star, star_star]
    have h2 := congrArg conjTranspose (hRJ (star y))
    simp only [conjTranspose_mul, conjTranspose_conjTranspose, ← h1, mat, MonoidHom.coe_mk, OneHom.coe_mk] at h2
    show (Jm S)ᴴ * R y = (Jm S)ᴴ * R y * Jm S * (Jm S)ᴴ
    exact h2.trans (by simp only [Matrix.mul_assoc])
  · intro X
    obtain ⟨c, -, hc0, -, hcX, -⟩ := GlobalTheory.CompanionTheory.LieCurve.exists_curve E a X
    ext i k
    have hL : HasDerivAt (fun t => (R (c t) * Jm S) i k) ((dR X * Jm S) i k) 0 := by
      simp only [Matrix.mul_apply]
      exact HasDerivAt.fun_sum fun m _ => (hR.der c X hc0 hcX i m).mul_const _
    have hRr : HasDerivAt (fun t => (Jm S * Ξ.mat (c t)) i k) ((Jm S * Ξ.dmat X) i k) 0 := by
      simp only [Matrix.mul_apply]
      exact HasDerivAt.fun_sum fun m _ => (Ξ.hasDerivAt_curve c X hc0 hcX m k).const_mul _
    have e : (fun t => (R (c t) * Jm S) i k) = fun t => (Jm S * Ξ.mat (c t)) i k := funext fun t => by rw [hRJ]
    rw [e] at hL
    exact hL.unique hRr

end Main

end PositivityTheory.Rg.Cz.J
