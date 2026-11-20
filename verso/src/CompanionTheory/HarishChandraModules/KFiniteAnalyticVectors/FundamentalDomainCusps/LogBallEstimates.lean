import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.FundamentalDomainCusps.HeightBoundSetup
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.TransferenceCoveringDivisor

open Matrix NumberField Topology
open scoped ComplexConjugate InnerProductSpace

noncomputable section

namespace CompanionTheory.D.gk.RF.PE

open Formalism.MainNotions.S

/- English proof (translation)
Establish `: Module.IsTorsionFree ℤ (Λ ⧸ S)` using `Module.IsTorsionFree.of_smul_eq_zero fun r m h => by`. Take `⟨x, rfl⟩` from `S.mkQ_surjective m`. Rewrite `h` using `[← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]`. Conclude with `(hS r x h).imp_right fun h' => (Submodule.Quotient.mk_eq_zero _).2 h'`. Establish `: Module.Free ℤ (Λ ⧸ S)` using `Module.free_of_finite_type_torsion_free'`.

Take `⟨s, hs⟩` from `Module.projective_lifting_property S.mkQ LinearMap.id S.mkQ_surjective`. Establish `hr : ∀ x, (LinearMap.id - s ∘ₗ S.mkQ : Λ →ₗ[ℤ] Λ) x ∈ S` using `fun x => by`. Rewrite using `[← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, LinearMap.sub_apply, map_sub, LinearMap.comp_apply, ← LinearMap.comp_apply S.mkQ s, hs]`. Simplify using the standard rewrite rules. Use `⟨f ∘ₗ LinearMap.codRestrict S _ hr, fun x => congrArg f (Subtype.ext ?_)⟩` and prove the remaining obligations.

Use `show (x : Λ) - s (S.mkQ x) = x`. Rewrite using `[Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero _).2 x.2, map_zero, sub_zero]`.
-/
theorem exists_extend {Λ : Type} [AddCommGroup Λ] [Module.Finite ℤ Λ] (S : Submodule ℤ Λ)
    (hS : ∀ (m : ℤ) x, m • x ∈ S → m = 0 ∨ x ∈ S) (f : S →ₗ[ℤ] ℤ) : ∃ g : Λ →ₗ[ℤ] ℤ, ∀ x : S, g x = f x := by
  have : Module.IsTorsionFree ℤ (Λ ⧸ S) := Module.IsTorsionFree.of_smul_eq_zero fun r m h => by
    obtain ⟨x, rfl⟩ := S.mkQ_surjective m
    rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h
    exact (hS r x h).imp_right fun h' => (Submodule.Quotient.mk_eq_zero _).2 h'
  have : Module.Free ℤ (Λ ⧸ S) := Module.free_of_finite_type_torsion_free'
  obtain ⟨s, hs⟩ := Module.projective_lifting_property S.mkQ LinearMap.id S.mkQ_surjective
  have hr : ∀ x, (LinearMap.id - s ∘ₗ S.mkQ : Λ →ₗ[ℤ] Λ) x ∈ S := fun x => by
    rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, LinearMap.sub_apply, map_sub, LinearMap.comp_apply,
      ← LinearMap.comp_apply S.mkQ s, hs]
    simp
  refine ⟨f ∘ₗ LinearMap.codRestrict S _ hr, fun x => congrArg f (Subtype.ext ?_)⟩
  show (x : Λ) - s (S.mkQ x) = x
  rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero _).2 x.2, map_zero, sub_zero]

/- English proof (translation)
Take `⟨D, hD, hDi⟩` from `exists_den (integralBasis E).traceDual`. Use `⟨D, hD, fun g => ⟨fun j => ∑ k, (g (Pi.single j (RingOfIntegers.basis E k)) : E) * (integralBasis E).traceDual k, fun j => ?_, fun u => ?_⟩⟩` and prove the remaining obligations. Rewrite using `[Finset.mul_sum]`. Use `IsIntegral.sum _ fun k _ => ?_` and prove the remaining obligations. Rewrite using `[mul_left_comm]`.

Conclude with `(isIntegral_intCast _).mul (hDi k)`. Set `c : Fin n → E` to `fun j => ∑ k, (g (Pi.single j (RingOfIntegers.basis E k)) : E) * (integralBasis E).traceDual k`. Set `A : (Fin n → 𝓞 E) →ₗ[ℤ] ℚ` to `Algebra.linearMap ℤ ℚ ∘ₗ g`. Set `B : (Fin n → 𝓞 E) →ₗ[ℤ] ℚ` to `AddMonoidHom.toIntLinearMap { toFun := fun u => Algebra.trace ℚ E (c ⬝ᵥ fun j => (u j : E)) map_zero' := by simp [dotProduct] map_add' := fun u u' => by`. Rewrite using `[← map_add, ← dotProduct_add]`.

Use `congr 2 }`. Establish `hAB : A = B` using `LinearMap.pi_ext' fun j => (RingOfIntegers.basis E).ext fun k => by show ((g (Pi.single j (RingOfIntegers.basis E k)) : ℤ) : ℚ) = Algebra.trace ℚ E (c ⬝ᵥ fun i => ((Pi.single j (RingOfIntegers.basis E k) : Fin n → 𝓞 E) i : E))`. Rewrite using `[dotProduct, Finset.sum_eq_single j (fun i _ hi => by simp [Pi.single_eq_of_ne hi]) (by simp), Pi.single_eq_same, Finset.sum_mul, map_sum, Finset.sum_eq_single k (fun l _ hl => ?_) (by simp)]`. Rewrite using `[mul_assoc, ← zsmul_eq_mul, map_zsmul, show ((RingOfIntegers.basis E k : 𝓞 E) : E) = integralBasis E k from (integralBasis_apply E k).symm, Module.Basis.trace_traceDual_mul]`. Simplify using the standard rewrite rules.

Rewrite using `[mul_assoc, ← zsmul_eq_mul, map_zsmul, show ((RingOfIntegers.basis E k : 𝓞 E) : E) = integralBasis E k from (integralBasis_apply E k).symm, mul_comm, Module.Basis.trace_mul_traceDual, if_neg (Ne.symm hl), smul_zero]`. Conclude with `LinearMap.congr_fun hAB u`.
-/
theorem dual_rep (E : Type) [Field E] [NumberField E] (n : ℕ) : ∃ D : ℕ, 1 ≤ D ∧ ∀ g : (Fin n → 𝓞 E) →ₗ[ℤ] ℤ,
    ∃ c : Fin n → E, (∀ j, IsIntegral ℤ ((D : E) * c j)) ∧
      ∀ u, (g u : ℚ) = Algebra.trace ℚ E (c ⬝ᵥ fun j => (u j : E)) := by
  classical
  obtain ⟨D, hD, hDi⟩ := exists_den (integralBasis E).traceDual
  refine ⟨D, hD, fun g => ⟨fun j => ∑ k, (g (Pi.single j (RingOfIntegers.basis E k)) : E) * (integralBasis E).traceDual k,
    fun j => ?_, fun u => ?_⟩⟩
  · rw [Finset.mul_sum]
    refine IsIntegral.sum _ fun k _ => ?_
    rw [mul_left_comm]
    exact (isIntegral_intCast _).mul (hDi k)
  · let c : Fin n → E := fun j => ∑ k, (g (Pi.single j (RingOfIntegers.basis E k)) : E) * (integralBasis E).traceDual k
    let A : (Fin n → 𝓞 E) →ₗ[ℤ] ℚ := Algebra.linearMap ℤ ℚ ∘ₗ g
    let B : (Fin n → 𝓞 E) →ₗ[ℤ] ℚ := AddMonoidHom.toIntLinearMap
      { toFun := fun u => Algebra.trace ℚ E (c ⬝ᵥ fun j => (u j : E))
        map_zero' := by simp [dotProduct]
        map_add' := fun u u' => by
          rw [← map_add, ← dotProduct_add]
          congr 2 }
    have hAB : A = B := LinearMap.pi_ext' fun j => (RingOfIntegers.basis E).ext fun k => by
      show ((g (Pi.single j (RingOfIntegers.basis E k)) : ℤ) : ℚ) =
        Algebra.trace ℚ E (c ⬝ᵥ fun i => ((Pi.single j (RingOfIntegers.basis E k) : Fin n → 𝓞 E) i : E))
      rw [dotProduct, Finset.sum_eq_single j (fun i _ hi => by simp [Pi.single_eq_of_ne hi]) (by simp),
        Pi.single_eq_same, Finset.sum_mul, map_sum, Finset.sum_eq_single k (fun l _ hl => ?_) (by simp)]
      · rw [mul_assoc, ← zsmul_eq_mul, map_zsmul, show ((RingOfIntegers.basis E k : 𝓞 E) : E) = integralBasis E k from
          (integralBasis_apply E k).symm, Module.Basis.trace_traceDual_mul]
        simp
      · rw [mul_assoc, ← zsmul_eq_mul, map_zsmul, show ((RingOfIntegers.basis E k : 𝓞 E) : E) = integralBasis E k from
          (integralBasis_apply E k).symm, mul_comm, Module.Basis.trace_mul_traceDual, if_neg (Ne.symm hl), smul_zero]
    exact LinearMap.congr_fun hAB u

variable (I : AutInst)

/- English proof (translation)
Use `LinearIndependent.span_eq_top_of_card_eq_finrank' (Fintype.linearIndependent_iff.2 fun r hr j => ?_) ?_` and prove the remaining obligations. Establish `h1 : ∀ k, r k * (if k = j then 1 else 0) = ∑ v, 2 * ((r k : ℂ) * I.φ v (integralBasis I.E k) * I.φ v ((integralBasis I.E).traceDual j)).re` using `fun k => by`. Use `trace_eq I hs (integralBasis I.E k * (integralBasis I.E).traceDual j)` as an intermediate fact. Rewrite `this` using `[Module.Basis.trace_mul_traceDual]`. Simplify using `only [mul_assoc, Complex.re_ofReal_mul, ← map_mul, mul_left_comm (2 : ℝ), ← Finset.mul_sum, ← this]`.

Apply the tactic sequence `split_ifs <;> simp`. Establish `h2` using `Finset.sum_congr (rfl : Finset.univ = _) fun k _ => h1 k`. Rewrite `h2` using `[Finset.sum_comm]`. Simplify using `only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h2`. Rewrite using `[h2]`.

Use `Finset.sum_eq_zero fun v _ => ?_` and prove the remaining obligations. Establish `h3` using `congrFun hr v`. Simplify using `only [Finset.sum_apply, Pi.smul_apply, Complex.real_smul, Pi.zero_apply] at h3`. Rewrite using `[← Finset.mul_sum, ← Complex.re_sum, ← Finset.sum_mul, h3]`. Simplify using the standard rewrite rules.

Rewrite using `[← Module.finrank_eq_card_basis (integralBasis I.E), ← Embeddings.card I.E ℂ, ← Fintype.card_of_bijective (emb_bij I hs), Module.finrank_pi_fintype, Fintype.card_prod]`. Simplify using the standard rewrite rules.
-/
theorem span_phi (hs : ∀ v (a : I.E), I.φ v (star a) = star (I.φ v a)) :
    Submodule.span ℝ (Set.range fun k => fun v => I.φ v (integralBasis I.E k)) = ⊤ := by
  classical
  refine LinearIndependent.span_eq_top_of_card_eq_finrank' (Fintype.linearIndependent_iff.2 fun r hr j => ?_) ?_
  · have h1 : ∀ k, r k * (if k = j then 1 else 0) =
        ∑ v, 2 * ((r k : ℂ) * I.φ v (integralBasis I.E k) * I.φ v ((integralBasis I.E).traceDual j)).re := fun k => by
      have := trace_eq I hs (integralBasis I.E k * (integralBasis I.E).traceDual j)
      rw [Module.Basis.trace_mul_traceDual] at this
      simp only [mul_assoc, Complex.re_ofReal_mul, ← map_mul, mul_left_comm (2 : ℝ), ← Finset.mul_sum, ← this]
      split_ifs <;> simp
    have h2 := Finset.sum_congr (rfl : Finset.univ = _) fun k _ => h1 k
    rw [Finset.sum_comm] at h2
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h2
    rw [h2]
    refine Finset.sum_eq_zero fun v _ => ?_
    have h3 := congrFun hr v
    simp only [Finset.sum_apply, Pi.smul_apply, Complex.real_smul, Pi.zero_apply] at h3
    rw [← Finset.mul_sum, ← Complex.re_sum, ← Finset.sum_mul, h3]
    simp
  · rw [← Module.finrank_eq_card_basis (integralBasis I.E), ← Embeddings.card I.E ℂ,
      ← Fintype.card_of_bijective (emb_bij I hs), Module.finrank_pi_fintype, Fintype.card_prod]
    simp

/- English proof (translation)
Unfold `atV`. Rewrite using `[← mulVec_smul]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Simplify using the standard rewrite rules.
-/
theorem atV_smul (v : InfinitePlace I.F) (a : I.E) (u : Fin I.n → I.E) : atV I v (a • u) = I.φ v a • atV I v u := by
  unfold atV
  rw [← mulVec_smul]
  congr 1
  funext i
  simp

/- English proof (translation)
Unfold `atV`. Rewrite using `[← mulVec_add]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Simplify using the standard rewrite rules.
-/
theorem atV_add (v : InfinitePlace I.F) (u u' : Fin I.n → I.E) : atV I v (u + u') = atV I v u + atV I v u' := by
  unfold atV
  rw [← mulVec_add]
  congr 1
  funext i
  simp

/- English proof (translation)
Rewrite using `[← Finset.univ_sum_single b]`. Use `Submodule.sum_mem _ fun v _ => ?_` and prove the remaining obligations. Establish `key : ∀ x ∈ Wv I W v, ∀ β : ℂ, (Pi.single v (β • x) : InfinitePlace I.F → Fin I.n → ℂ) ∈ Submodule.span ℝ {x : InfinitePlace I.F → Fin I.n → ℂ | ∃ u ∈ IntV I, u ∈ W ∧ x = fun v => atV I v u}`. Introduce `x hx`. Proceed by induction on `hx using Submodule.span_induction with`.

Consider the case `mem x hx`. Take `⟨w, hw, rfl⟩` from `hx`. Introduce `β`. Take `⟨c, hc, hci⟩` from `exists_den w`. Establish `hc0 : (c : ℂ) ≠ 0` using `by exact_mod_cast (by omega : c ≠ 0)`.

Set `L : (InfinitePlace I.F → ℂ) →ₗ[ℝ] (InfinitePlace I.F → Fin I.n → ℂ)` to `{ toFun := fun γ v' => γ v' • atV I v' ((c : I.E) • w) map_add' := fun _ _ => funext fun v' => add_smul _ _ _ map_smul' := fun r γ => funext fun v' => smul_assoc r (γ v') _ }`. Establish `e : (Pi.single v (β • atV I v w) : InfinitePlace I.F → Fin I.n → ℂ) = L (Pi.single v (β / c))`. Use function extensionality and compare the values at `v'`. Distinguish the cases in `h : v' = v`. Substitute `h show _ = (Pi.single v' (β / c) : InfinitePlace I.F → ℂ) v' • atV I v' ((c : I.E) • w)` using the available equality.

Rewrite using `[Pi.single_eq_same, Pi.single_eq_same, atV_smul, map_natCast, smul_smul, div_mul_cancel₀ _ hc0]`. Use `show _ = (Pi.single v (β / c) : InfinitePlace I.F → ℂ) v' • atV I v' ((c : I.E) • w)`. Rewrite using `[Pi.single_eq_of_ne h, Pi.single_eq_of_ne h, zero_smul]`. Rewrite using `[e]`. Establish `h1 : (Pi.single v (β / c) : InfinitePlace I.F → ℂ) ∈ Submodule.span ℝ (Set.range fun k => fun v => I.φ v (integralBasis I.E k))` using `by rw [span_phi I hs]; trivial`.

Use `Submodule.span_mono ?_ (Submodule.apply_mem_span_image_of_mem_span L h1)` and prove the remaining obligations. Introduce and unpack `_ ⟨_, ⟨k, rfl⟩, rfl⟩`. Use `⟨integralBasis I.E k • (c : I.E) • w, fun i => ?_, W.smul_mem _ (W.smul_mem _ hw),` and prove the remaining obligations. Use function extensionality and compare the values at `fun v' => (atV_smul I v' _ _).symm⟩`. Rewrite using `[integralBasis_apply]`.

Conclude with `(RingOfIntegers.basis I.E k).2.mul (hci i)`. Consider the case `zero => intro β`. Simplify using the standard rewrite rules. Consider the case `add x y _ _ ihx ihy => intro β`. Rewrite using `[smul_add, Pi.single_add]`.

Conclude with `Submodule.add_mem _ (ihx β) (ihy β)`. Consider the case `smul a x _ ih => intro β`. Rewrite using `[smul_smul]`. Conclude with `ih _`. Simplify using `using key _ (hb v) 1`.
-/
theorem mem_span_int (hs : ∀ v (a : I.E), I.φ v (star a) = star (I.φ v a)) (W : Submodule I.E (Fin I.n → I.E))
    (b : InfinitePlace I.F → Fin I.n → ℂ) (hb : ∀ v, b v ∈ Wv I W v) :
    b ∈ Submodule.span ℝ {x : InfinitePlace I.F → Fin I.n → ℂ | ∃ u ∈ IntV I, u ∈ W ∧ x = fun v => atV I v u} := by
  classical
  rw [← Finset.univ_sum_single b]
  refine Submodule.sum_mem _ fun v _ => ?_
  have key : ∀ x ∈ Wv I W v, ∀ β : ℂ, (Pi.single v (β • x) : InfinitePlace I.F → Fin I.n → ℂ) ∈ Submodule.span ℝ
      {x : InfinitePlace I.F → Fin I.n → ℂ | ∃ u ∈ IntV I, u ∈ W ∧ x = fun v => atV I v u} := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨w, hw, rfl⟩ := hx
      intro β
      obtain ⟨c, hc, hci⟩ := exists_den w
      have hc0 : (c : ℂ) ≠ 0 := by exact_mod_cast (by omega : c ≠ 0)
      let L : (InfinitePlace I.F → ℂ) →ₗ[ℝ] (InfinitePlace I.F → Fin I.n → ℂ) :=
        { toFun := fun γ v' => γ v' • atV I v' ((c : I.E) • w)
          map_add' := fun _ _ => funext fun v' => add_smul _ _ _
          map_smul' := fun r γ => funext fun v' => smul_assoc r (γ v') _ }
      have e : (Pi.single v (β • atV I v w) : InfinitePlace I.F → Fin I.n → ℂ) = L (Pi.single v (β / c)) := by
        funext v'
        by_cases h : v' = v
        · subst h
          show _ = (Pi.single v' (β / c) : InfinitePlace I.F → ℂ) v' • atV I v' ((c : I.E) • w)
          rw [Pi.single_eq_same, Pi.single_eq_same, atV_smul, map_natCast, smul_smul, div_mul_cancel₀ _ hc0]
        · show _ = (Pi.single v (β / c) : InfinitePlace I.F → ℂ) v' • atV I v' ((c : I.E) • w)
          rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne h, zero_smul]
      rw [e]
      have h1 : (Pi.single v (β / c) : InfinitePlace I.F → ℂ) ∈ Submodule.span ℝ
          (Set.range fun k => fun v => I.φ v (integralBasis I.E k)) := by rw [span_phi I hs]; trivial
      refine Submodule.span_mono ?_ (Submodule.apply_mem_span_image_of_mem_span L h1)
      rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
      refine ⟨integralBasis I.E k • (c : I.E) • w, fun i => ?_, W.smul_mem _ (W.smul_mem _ hw),
        funext fun v' => (atV_smul I v' _ _).symm⟩
      rw [integralBasis_apply]
      exact (RingOfIntegers.basis I.E k).2.mul (hci i)
    | zero => intro β; simp
    | add x y _ _ ihx ihy => intro β; rw [smul_add, Pi.single_add]; exact Submodule.add_mem _ (ihx β) (ihy β)
    | smul a x _ ih => intro β; rw [smul_smul]; exact ih _
  simpa using key _ (hb v) 1

/- English proof (translation)
The claim follows from `mulVec_diagonal _ _ _`.
-/
theorem Jm_mulVec {n : ℕ} (ε : Fin n → Bool) (x : Fin n → ℂ) (i : Fin n) :
    (Formalism.REAL.Jm ε *ᵥ x) i = (if ε i then 1 else -1) * x i := mulVec_diagonal _ _ _

/- English proof (translation)
Assume the negation of the conclusion as `h`. Take `⟨l, hl, hS⟩` from `Submodule.exists_le_ker_of_notMem h`. Establish `e : ∀ s, hf (Formalism.REAL.Jm ε) s (Formalism.REAL.Jm ε *ᵥ fun i => star (l (Pi.single i 1))) = star (l s)` using `fun s => by`. Rewrite using `[LinearMap.pi_apply_eq_sum_univ l s, star_sum, hf, dotProduct]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[Jm_mulVec, Jm_mulVec, smul_eq_mul, star_mul', Pi.star_apply]`. Establish `: (fun j => if i = j then (1 : ℂ) else 0) = Pi.single i 1`. Use function extensionality and compare the values at `j`. Simplify using `[Pi.single_apply, eq_comm]`. Rewrite using `[this]`.

Apply the tactic sequence `split_ifs <;> ring`. Use `hx _ fun w hw => by rw [e, show l w = 0 from hS hw, star_zero]` as an intermediate fact. Rewrite `this` using `[e]`. Conclude with `hl (star_eq_zero.1 this)`.
-/
theorem mem_of_perp_perp {n : ℕ} (ε : Fin n → Bool) (S : Submodule ℂ (Fin n → ℂ)) {x : Fin n → ℂ}
    (hx : ∀ b ∈ perp (Formalism.REAL.Jm ε) S, hf (Formalism.REAL.Jm ε) x b = 0) : x ∈ S := by
  classical
  by_contra h
  obtain ⟨l, hl, hS⟩ := Submodule.exists_le_ker_of_notMem h
  have e : ∀ s, hf (Formalism.REAL.Jm ε) s (Formalism.REAL.Jm ε *ᵥ fun i => star (l (Pi.single i 1))) = star (l s) := fun s => by
    rw [LinearMap.pi_apply_eq_sum_univ l s, star_sum, hf, dotProduct]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Jm_mulVec, Jm_mulVec, smul_eq_mul, star_mul', Pi.star_apply]
    have : (fun j => if i = j then (1 : ℂ) else 0) = Pi.single i 1 := by
      funext j; simp [Pi.single_apply, eq_comm]
    rw [this]
    split_ifs <;> ring
  have := hx _ fun w hw => by rw [e, show l w = 0 from hS hw, star_zero]
  rw [e] at this
  exact hl (star_eq_zero.1 this)

abbrev VR : Type := PiLp 2 fun _ : InfinitePlace I.F × Fin I.n => ℂ

def toV : (InfinitePlace I.F → Fin I.n → ℂ) →ₗ[ℝ] VR I where
  toFun b := WithLp.toLp 2 fun p => b p.1 p.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/- English proof (translation)
The claim follows from `(pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun v => (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => PiLp.norm_apply_le (toV I b) (v, i)`.
-/
theorem norm_le_toV (b : InfinitePlace I.F → Fin I.n → ℂ) : ‖b‖ ≤ ‖toV I b‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun v => (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i =>
    PiLp.norm_apply_le (toV I b) (v, i)

/- English proof (translation)
Rewrite using `[PiLp.inner_apply, Fintype.sum_prod_type]`. Use `Finset.sum_congr rfl fun v _ => ?_` and prove the remaining obligations. Rewrite using `[hf, dotProduct, Complex.re_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Use `show ⟪(Formalism.REAL.Jm (I.ε v) *ᵥ a v) i, b v i⟫_ℝ = _`.

Rewrite using `[Complex.inner, Jm_mulVec, Jm_mulVec]`. Use `congr 1`. Apply the tactic sequence `split_ifs <;> simp [mul_comm]`.
-/
theorem inner_toV (a b : InfinitePlace I.F → Fin I.n → ℂ) :
    ⟪toV I fun v => Formalism.REAL.Jm (I.ε v) *ᵥ a v, toV I b⟫_ℝ = ∑ v, (hf (Formalism.REAL.Jm (I.ε v)) (a v) (b v)).re := by
  rw [PiLp.inner_apply, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [hf, dotProduct, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  show ⟪(Formalism.REAL.Jm (I.ε v) *ᵥ a v) i, b v i⟫_ℝ = _
  rw [Complex.inner, Jm_mulVec, Jm_mulVec]
  congr 1
  split_ifs <;> simp [mul_comm]

end CompanionTheory.D.gk.RF.PE

namespace CompanionTheory.D.gk.RF

open Formalism.MainNotions.S PE

set_option maxHeartbeats 800000 in
/- English proof (translation)
Introduce `hT I`. Take `⟨hJ, hs, hh, hperp, -, -, -, -⟩` from `hT I`. Take `⟨D, hD, hdual⟩` from `dual_rep I.E I.n`. Take `⟨c₁, hc₁, hcJ⟩` from `exists_den fun p : Fin I.n × Fin I.n => I.J⁻¹ p.1 p.2`. Use `set c : ℕ := D * c₁ with hc`.

Establish `hc0 : (0 : ℝ) < c` using `by have : 0 < c := by positivity`. Conclude with `this` after adjusting the coercions. Use `⟨(Module.finrank ℝ (VR I) + 1) * c, by positivity, fun y W ρ t ht hρ hcov hlong b hb => ?_⟩` and prove the remaining obligations. Set `Λ : (InfinitePlace I.F → Fin I.n → ℂ) →ₗ[ℝ] (InfinitePlace I.F → Fin I.n → ℂ)` to `{ toFun := fun b v => uMat (y v)⁻¹ *ᵥ b v map_add' := fun _ _ => funext fun v => mulVec_add _ _ _ map_smul' := fun r _ => funext fun v => mulVec_smul _ r _ }`. Set `co : (Fin I.n → 𝓞 I.E) → Fin I.n → I.E` to `fun u i => u i`.

Set `ι : (Fin I.n → 𝓞 I.E) →ₗ[ℤ] VR I` to `AddMonoidHom.toIntLinearMap (AddMonoidHom.mk' (fun u => toV I (vecAt I y (co u))) fun u u' => by`. Rewrite using `[← map_add]`. Use `congr 1`. Use function extensionality and compare the values at `v`. Rewrite using `[show co (u + u') = co u + co u' from rfl]`.

Simplify using `only [vecAt, atV_add, mulVec_add, Pi.add_apply])`. Establish `hι : ∀ u, ι u = toV I (vecAt I y (co u))` using `fun _ => rfl`. Set `S : Submodule ℤ (Fin I.n → 𝓞 I.E)` to `{ carrier := {u | co u ∈ perp I.J W} add_mem' := fun ha hb => (perp I.J W).add_mem ha hb zero_mem' := (perp I.J W).zero_mem smul_mem' := fun m u hu => by`. Establish `: co (m • u) = (m : I.E) • co u` using `funext fun i => by simp [co]`. Use `show co (m • u) ∈ perp I.J W`.

Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ _ hu }`. Set `X : Submodule ℝ (VR I)` to `Submodule.span ℝ (S.map ι : Set (VR I))`. Set `M : Submodule ℤ X` to `(S.map ι).comap (X.subtype.restrictScalars ℤ)`. Establish `hXP : ∀ b : InfinitePlace I.F → Fin I.n → ℂ, (∀ v, b v ∈ Wv I (perp I.J W) v) → toV I (Λ b) ∈ X` using `fun b hb => by`.

Use `Submodule.span_mono ?_ (Submodule.apply_mem_span_image_of_mem_span (toV I ∘ₗ Λ) (mem_span_int I hs _ b hb))` and prove the remaining obligations. Introduce and unpack `_ ⟨_, ⟨u, hu, huW, rfl⟩, rfl⟩`. Conclude with `⟨fun i => ⟨u i, hu i⟩, huW, rfl⟩`. Establish `hdisc : DiscreteTopology M`. Use `discreteTopology_of_isOpen_singleton_zero (isOpen_singleton_of_finite_mem_nhds 0 (Metric.closedBall_mem_nhds _ one_pos) ?_)` and prove the remaining obligations.

Use `set K : ℝ := ∑ v, ∑ i, ∑ j, ‖(I.P v * uMat (y v)) i j‖`. Establish `hf1 : {u : Fin I.n → 𝓞 I.E | ∀ i, ∀ v, ‖I.φ v (u i)‖ ≤ K}.Finite` using `Set.Finite.pi' (t := fun _ : Fin I.n => {a : 𝓞 I.E | ∀ v, ‖I.φ v a‖ ≤ K}) fun _ => ((finite_bdd I hs K).preimage (f := fun a : 𝓞 I.E => (a : I.E)) RingOfIntegers.coe_injective.injOn).subset fun a ha => ⟨a.2, ha⟩`. Use `Set.Finite.of_finite_image (f := fun m : M => ((m : X) : VR I)) ((hf1.image ι).subset ?_) (Subtype.val_injective.comp Subtype.val_injective).injOn` and prove the remaining obligations. Introduce and unpack `_ ⟨m, hm, rfl⟩`. Take `⟨u, -, hu⟩` from `m.2`.

Use `⟨u, fun i v => ?_, hu⟩` and prove the remaining obligations. Establish `h1 : ‖vecAt I y (co u)‖ ≤ 1` using `(norm_le_toV I _).trans (by`. Rewrite using `[← hι, hu]`. Conclude with `mem_closedBall_zero_iff.1 hm)`. Establish `hP : IsUnit (I.P v).det` using `(Matrix.isUnit_iff_isUnit_det _).1 (I.P_unit v)`.

Establish `e : (I.P v * uMat (y v)) *ᵥ vecAt I y (co u) v = fun i => I.φ v (u i)`. Simplify using `only [vecAt, atV, mulVec_mulVec]`. Rewrite using `[Matrix.mul_assoc, ← Matrix.mul_assoc (uMat (y v)), uMat_mul_inv, Matrix.one_mul, Matrix.mul_nonsing_inv _ hP, one_mulVec]`. Rewrite using `[← congrFun e i, mulVec, dotProduct]`. Use `(norm_sum_le _ _).trans (le_trans (Finset.sum_le_sum fun j _ => ?_) ((Finset.single_le_sum (f := fun i => ∑ j, ‖(I.P v * uMat (y v)) i j‖) (fun _ _ => by positivity) (Finset.mem_univ i)).trans (Finset.single_le_sum (f := fun v => ∑ i, ∑ j, ‖(I.P v * uMat (y v)) i j‖) (fun _ _ => …` and prove the remaining obligations.

Rewrite using `[norm_mul]`. Conclude with `mul_le_of_le_one_right (norm_nonneg _) ((norm_le_pi_norm _ j).trans ((norm_le_pi_norm _ v).trans h1))`. Establish `hJu : IsUnit I.J.det` using `I.J_det.isUnit`. Take `⟨m, ⟨u, huS, hu⟩, hm⟩` from `PI.Tr2.coverDiv X M hdisc Submodule.span_span_coe_preimage (t / c) (by positivity) (fun z hz hz0 => by`. Establish `hX : ∀ u ∈ S, ι u ∈ X` using `fun u hu => Submodule.subset_span ⟨u, hu, rfl⟩`.

Set `F : S →ₗ[ℤ] ℝ` to `((innerₛₗ ℝ (z : VR I)).restrictScalars ℤ) ∘ₗ ι ∘ₗ S.subtype`. Establish `hF : ∀ u, F u ∈ LinearMap.range (Algebra.linearMap ℤ ℝ)` using `fun u => by`. Take `⟨k, hk⟩` from `hz ⟨ι u, hX u u.2⟩ ⟨u, u.2, rfl⟩`. Conclude with `⟨k, by rw [real_inner_comm] at hk; exact hk.symm⟩`. Set `e` to `LinearEquiv.ofInjective (Algebra.linearMap ℤ ℝ) (Int.cast_injective (α := ℝ))`.

Take `⟨g, hg⟩` from `exists_extend S (fun k x hx => by`. Distinguish the cases in `hk : k = 0`. Conclude with `Or.inl hk`. Establish `e1 : co (k • x) = (k : I.E) • co x` using `funext fun i => by simp [co]`. Establish `h1 : co (k • x) ∈ perp I.J W` using `hx`.

Rewrite `h1` using `[e1]`. Establish `hk' : (k : I.E) ≠ 0` using `Int.cast_ne_zero.2 hk`. Establish `h2 : co x ∈ perp I.J W` using `((perp I.J W).smul_mem_iff hk').1 h1`. Conclude with `Or.inr h2)`. Use the proof step `(e.symm.toLinearMap ∘ₗ F.codRestrict _ hF)`.

Establish `hgF : ∀ u : S, (g u : ℝ) = ⟪(z : VR I), ι u⟫_ℝ` using `fun u => by`. Rewrite using `[hg]`. Conclude with `congrArg Subtype.val (e.apply_symm_apply (F.codRestrict _ hF u))`. Take `⟨cv, hcv, hgc⟩` from `hdual g`. Use `set u₀ : Fin I.n → I.E := star (cv ᵥ* I.J⁻¹) with hu₀`.

Establish `hu₀f : ∀ u, hf I.J u₀ u = cv ⬝ᵥ u` using `fun u => by`. Rewrite using `[hf, hu₀, star_star, dotProduct_mulVec, vecMul_vecMul, Matrix.nonsing_inv_mul _ hJu, vecMul_one]`. Establish `hu₀i : (c : I.E) • u₀ ∈ IntV I` using `fun i => by`. Establish `: ((c : I.E) • u₀) i = star (∑ j, ((D : I.E) * cv j) * ((c₁ : I.E) * I.J⁻¹ j i))`. Rewrite using `[Pi.smul_apply, smul_eq_mul, hu₀, Pi.star_apply, ← star_natCast (R := I.E) c, ← star_mul', vecMul, dotProduct, Finset.mul_sum, hc]`.

Use `congr 1`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`.

Conclude with `isIntegral_star (IsIntegral.sum _ fun j _ => (hcv j).mul (hcJ (j, i)))`. Set `q : VR I` to `toV I fun v => Formalism.REAL.Jm (I.ε v) *ᵥ ((2 : ℂ) • vecAt I y u₀ v)`. Establish `hq : ∀ u : S, ⟪q, ι u⟫_ℝ = ⟪(z : VR I), ι u⟫_ℝ` using `fun u => by`. Rewrite using `[← hgF, hι, inner_toV]`. Establish `h1` using `congrArg (fun r : ℚ => (r : ℝ)) (hgc u)`.

Simplify using `only [Rat.cast_intCast] at h1`. Rewrite using `[h1, trace_eq I hs, ← hu₀f]`. Use `Finset.sum_congr rfl fun v _ => ?_` and prove the remaining obligations. Rewrite using `[← hh, ← hf_uMat (y v)⁻¹ (atV I v u₀)]`. Simplify using `only [hf, star_smul, smul_dotProduct, vecAt]`.

Simplify using `[co]`. Establish `hqX : ∀ x ∈ X, ⟪q - z, x⟫_ℝ = 0` using `fun x hx => by`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx => obtain ⟨u, hu, rfl⟩ := hx`. Rewrite using `[inner_sub_left, hq ⟨u, hu⟩, sub_self]`.

Consider the case `zero => simp`. Consider the case `add _ _ _ _ h1 h2 => rw [inner_add_right, h1, h2, add_zero]`. Consider the case `smul a _ _ h1 => rw [inner_smul_right, h1, mul_zero]`. Establish `hu₀W : (c : I.E) • u₀ ∉ W` using `fun hW => hz0 (by`. Establish `hW' : u₀ ∈ W` using `(W.smul_mem_iff (s := (c : I.E)) (by exact_mod_cast hc0.ne')).1 hW`.

Establish `h1 : ∀ x ∈ X, ⟪(z : VR I), x⟫_ℝ = 0` using `fun x hx => by`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨u, hu, rfl⟩` from `hx`. Establish `h2` using `hgc u`.

Rewrite `h2` using `[← hu₀f, show hf I.J u₀ _ = 0 from hu u₀ hW', map_zero]`. Rewrite using `[← hgF ⟨u, hu⟩, show g u = 0 by exact_mod_cast h2, Int.cast_zero]`. Consider the case `zero => simp`. Consider the case `add _ _ _ _ h1 h2 => rw [inner_add_right, h1, h2, add_zero]`. Consider the case `smul a _ _ h1 => rw [inner_smul_right, h1, mul_zero]`.

Conclude with `Subtype.ext (inner_self_eq_zero.1 (h1 _ z.2)))`. Set `zJ : InfinitePlace I.F → Fin I.n → ℂ` to `fun v => Formalism.REAL.Jm (I.ε v) *ᵥ fun i => (z : VR I) (v, i)`. Set `a : InfinitePlace I.F → Fin I.n → ℂ` to `fun v => (2 : ℂ) • vecAt I y u₀ v - zJ v`. Establish `hqa : q - z = toV I fun v => Formalism.REAL.Jm (I.ε v) *ᵥ a v` using `PiLp.ext fun p => by show (Formalism.REAL.Jm (I.ε p.1) *ᵥ ((2 : ℂ) • vecAt I y u₀ p.1)) p.2 - (z : VR I) p = (Formalism.REAL.Jm (I.ε p.1) *ᵥ a p.1) p.2`. Simplify using `only [a, zJ, Jm_mulVec, Pi.sub_apply]`.

Apply the tactic sequence `split_ifs <;> ring`. Establish `haW : ∀ v, uMat (y v) *ᵥ a v ∈ Wv I W v` using `fun v => mem_of_perp_perp _ _ fun b' hb' => by`. Rewrite `hb'` using `[← hperp]`. Establish `h1 : ∀ β : ℂ, (hf (Formalism.REAL.Jm (I.ε v)) (a v) (β • uMat (y v)⁻¹ *ᵥ b')).re = 0` using `fun β => by`. Establish `h2` using `hqX _ (hXP (Pi.single v (β • b')) fun v' => by`.

Distinguish the cases in `h : v' = v`. Substitute `h` using the available equality. Rewrite using `[Pi.single_eq_same]`. Conclude with `Submodule.smul_mem _ _ hb'`. Rewrite using `[Pi.single_eq_of_ne h]`.

Conclude with `Submodule.zero_mem _)`. Rewrite using `[hqa, inner_toV, Finset.sum_eq_single v (fun v' _ h => by`. Simplify using `[Λ, Pi.single_eq_of_ne h, hf]) (by simp)] at h2`. Simplify `h2` using `only [Λ, LinearMap.coe_mk, AddHom.coe_mk, Pi.single_eq_same, mulVec_smul]`. Rewrite using `[← hf_uMat (y v)⁻¹, mulVec_mulVec, uMat_inv_mul, one_mulVec]`.

Establish `h3` using `h1 1`. Establish `h4` using `h1 Complex.I`. Simplify using `only [hf, mulVec_smul, dotProduct_smul, smul_eq_mul, one_mul, Complex.I_mul_re, neg_eq_zero] at h3 h4`. Conclude with `Complex.ext h3 h4`. Take `⟨u', hu'i, hu'W, hu'⟩` from `hcov (fun v => ((c : ℂ) / 2) • uMat (y v) *ᵥ a v) fun v => Submodule.smul_mem _ _ (haW v)`.

Establish `h5` using `hlong ((c : I.E) • u₀ - u') (fun i => (hu₀i i).sub (hu'i i)) fun h => hu₀W (by simpa using W.add_mem h hu'W)`. Establish `e5 : vecAt I y ((c : I.E) • u₀ - u') = ((fun v => uMat (y v)⁻¹ *ᵥ ((c : ℂ) / 2) • uMat (y v) *ᵥ a v) - vecAt I y u') + ((c : ℂ) / 2) • zJ`. Use function extensionality and compare the values at `v`. Establish `: (c : I.E) • u₀ - u' = (c : I.E) • u₀ + (-1 : I.E) • u'` using `by simp [sub_eq_add_neg]`. Simplify using `only [this, vecAt, atV_add, atV_smul, mulVec_add, mulVec_smul, mulVec_mulVec, uMat_inv_mul, one_mulVec, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, a, map_natCast, map_neg, map_one]`.

Use `module`. Establish `h6 : ‖zJ‖ ≤ ‖z‖` using `(pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun v => (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => by`. Simplify using `only [zJ, Jm_mulVec, norm_mul]`. Apply the tactic sequence `have : ‖(if I.ε v i = true then (1 : ℂ) else -1)‖ = 1 := by split_ifs <;> simp`. Rewrite using `[this, one_mul]`.

Conclude with `PiLp.norm_apply_le (z : VR I) (v, i)`. Rewrite `h5` using `[e5]`. Establish `h7` using `h5.trans (norm_add_le_of_le hu' (norm_smul_le _ _))`. Rewrite `h7` using `[norm_div, Complex.norm_natCast, Complex.norm_two]`. Rewrite using `[div_le_iff₀ hc0]`.

Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left h6 hc0.le]) ⟨_, hXP b hb⟩`. Use `⟨co u, fun i => (u i).2, huS, ?_⟩` and prove the remaining obligations. Use `(norm_le_toV I _).trans (le_trans (le_of_eq ?_) (hm.trans ?_))` and prove the remaining obligations. Rewrite using `[map_sub, ← hι, hu]`. Both sides reduce to the same expression.

Establish `h1 : (Module.finrank ℝ X : ℝ) ≤ Module.finrank ℝ (VR I)` using `by exact_mod_cast X.finrank_le`. Rewrite using `[div_le_div_iff₀ (by positivity) ht, mul_assoc, mul_left_comm (c : ℝ), mul_div_cancel₀ _ hc0.ne']`. Use polynomial arithmetic with `[(Nat.cast_nonneg (Module.finrank ℝ X) : (0 : ℝ) ≤ _)]`.
-/
theorem covolume_orthogonal_complement : Transp → CovPerp := by
  classical
  intro hT I
  obtain ⟨hJ, hs, hh, hperp, -, -, -, -⟩ := hT I
  obtain ⟨D, hD, hdual⟩ := dual_rep I.E I.n
  obtain ⟨c₁, hc₁, hcJ⟩ := exists_den fun p : Fin I.n × Fin I.n => I.J⁻¹ p.1 p.2
  set c : ℕ := D * c₁ with hc
  have hc0 : (0 : ℝ) < c := by have : 0 < c := by positivity
                               exact_mod_cast this
  refine ⟨(Module.finrank ℝ (VR I) + 1) * c, by positivity, fun y W ρ t ht hρ hcov hlong b hb => ?_⟩
  let Λ : (InfinitePlace I.F → Fin I.n → ℂ) →ₗ[ℝ] (InfinitePlace I.F → Fin I.n → ℂ) :=
    { toFun := fun b v => uMat (y v)⁻¹ *ᵥ b v
      map_add' := fun _ _ => funext fun v => mulVec_add _ _ _
      map_smul' := fun r _ => funext fun v => mulVec_smul _ r _ }
  let co : (Fin I.n → 𝓞 I.E) → Fin I.n → I.E := fun u i => u i
  let ι : (Fin I.n → 𝓞 I.E) →ₗ[ℤ] VR I := AddMonoidHom.toIntLinearMap (AddMonoidHom.mk'
    (fun u => toV I (vecAt I y (co u))) fun u u' => by
      rw [← map_add]
      congr 1
      funext v
      rw [show co (u + u') = co u + co u' from rfl]
      simp only [vecAt, atV_add, mulVec_add, Pi.add_apply])
  have hι : ∀ u, ι u = toV I (vecAt I y (co u)) := fun _ => rfl
  let S : Submodule ℤ (Fin I.n → 𝓞 I.E) :=
    { carrier := {u | co u ∈ perp I.J W}
      add_mem' := fun ha hb => (perp I.J W).add_mem ha hb
      zero_mem' := (perp I.J W).zero_mem
      smul_mem' := fun m u hu => by
        have : co (m • u) = (m : I.E) • co u := funext fun i => by simp [co]
        show co (m • u) ∈ perp I.J W
        rw [this]; exact Submodule.smul_mem _ _ hu }
  let X : Submodule ℝ (VR I) := Submodule.span ℝ (S.map ι : Set (VR I))
  let M : Submodule ℤ X := (S.map ι).comap (X.subtype.restrictScalars ℤ)
  have hXP : ∀ b : InfinitePlace I.F → Fin I.n → ℂ, (∀ v, b v ∈ Wv I (perp I.J W) v) → toV I (Λ b) ∈ X := fun b hb => by
    refine Submodule.span_mono ?_ (Submodule.apply_mem_span_image_of_mem_span (toV I ∘ₗ Λ) (mem_span_int I hs _ b hb))
    rintro _ ⟨_, ⟨u, hu, huW, rfl⟩, rfl⟩
    exact ⟨fun i => ⟨u i, hu i⟩, huW, rfl⟩
  have hdisc : DiscreteTopology M := by
    refine discreteTopology_of_isOpen_singleton_zero
      (isOpen_singleton_of_finite_mem_nhds 0 (Metric.closedBall_mem_nhds _ one_pos) ?_)
    set K : ℝ := ∑ v, ∑ i, ∑ j, ‖(I.P v * uMat (y v)) i j‖
    have hf1 : {u : Fin I.n → 𝓞 I.E | ∀ i, ∀ v, ‖I.φ v (u i)‖ ≤ K}.Finite :=
      Set.Finite.pi' (t := fun _ : Fin I.n => {a : 𝓞 I.E | ∀ v, ‖I.φ v a‖ ≤ K}) fun _ =>
        ((finite_bdd I hs K).preimage (f := fun a : 𝓞 I.E => (a : I.E)) RingOfIntegers.coe_injective.injOn).subset
          fun a ha => ⟨a.2, ha⟩
    refine Set.Finite.of_finite_image (f := fun m : M => ((m : X) : VR I)) ((hf1.image ι).subset ?_)
      (Subtype.val_injective.comp Subtype.val_injective).injOn
    rintro _ ⟨m, hm, rfl⟩
    obtain ⟨u, -, hu⟩ := m.2
    refine ⟨u, fun i v => ?_, hu⟩
    have h1 : ‖vecAt I y (co u)‖ ≤ 1 := (norm_le_toV I _).trans (by
      rw [← hι, hu]; exact mem_closedBall_zero_iff.1 hm)
    have hP : IsUnit (I.P v).det := (Matrix.isUnit_iff_isUnit_det _).1 (I.P_unit v)
    have e : (I.P v * uMat (y v)) *ᵥ vecAt I y (co u) v = fun i => I.φ v (u i) := by
      simp only [vecAt, atV, mulVec_mulVec]
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc (uMat (y v)), uMat_mul_inv, Matrix.one_mul,
        Matrix.mul_nonsing_inv _ hP, one_mulVec]
    rw [← congrFun e i, mulVec, dotProduct]
    refine (norm_sum_le _ _).trans (le_trans (Finset.sum_le_sum fun j _ => ?_)
      ((Finset.single_le_sum (f := fun i => ∑ j, ‖(I.P v * uMat (y v)) i j‖) (fun _ _ => by positivity)
        (Finset.mem_univ i)).trans (Finset.single_le_sum (f := fun v => ∑ i, ∑ j, ‖(I.P v * uMat (y v)) i j‖)
          (fun _ _ => by positivity) (Finset.mem_univ v))))
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) ((norm_le_pi_norm _ j).trans ((norm_le_pi_norm _ v).trans h1))
  have hJu : IsUnit I.J.det := I.J_det.isUnit
  obtain ⟨m, ⟨u, huS, hu⟩, hm⟩ := PI.Tr2.coverDiv X M hdisc Submodule.span_span_coe_preimage (t / c)
    (by positivity) (fun z hz hz0 => by
      have hX : ∀ u ∈ S, ι u ∈ X := fun u hu => Submodule.subset_span ⟨u, hu, rfl⟩
      let F : S →ₗ[ℤ] ℝ := ((innerₛₗ ℝ (z : VR I)).restrictScalars ℤ) ∘ₗ ι ∘ₗ S.subtype
      have hF : ∀ u, F u ∈ LinearMap.range (Algebra.linearMap ℤ ℝ) := fun u => by
        obtain ⟨k, hk⟩ := hz ⟨ι u, hX u u.2⟩ ⟨u, u.2, rfl⟩
        exact ⟨k, by rw [real_inner_comm] at hk; exact hk.symm⟩
      let e := LinearEquiv.ofInjective (Algebra.linearMap ℤ ℝ) (Int.cast_injective (α := ℝ))
      obtain ⟨g, hg⟩ := exists_extend S (fun k x hx => by
        by_cases hk : k = 0
        · exact Or.inl hk
        · have e1 : co (k • x) = (k : I.E) • co x := funext fun i => by simp [co]
          have h1 : co (k • x) ∈ perp I.J W := hx
          rw [e1] at h1
          have hk' : (k : I.E) ≠ 0 := Int.cast_ne_zero.2 hk
          have h2 : co x ∈ perp I.J W := ((perp I.J W).smul_mem_iff hk').1 h1
          exact Or.inr h2)
        (e.symm.toLinearMap ∘ₗ F.codRestrict _ hF)
      have hgF : ∀ u : S, (g u : ℝ) = ⟪(z : VR I), ι u⟫_ℝ := fun u => by
        rw [hg]
        exact congrArg Subtype.val (e.apply_symm_apply (F.codRestrict _ hF u))
      obtain ⟨cv, hcv, hgc⟩ := hdual g
      set u₀ : Fin I.n → I.E := star (cv ᵥ* I.J⁻¹) with hu₀
      have hu₀f : ∀ u, hf I.J u₀ u = cv ⬝ᵥ u := fun u => by
        rw [hf, hu₀, star_star, dotProduct_mulVec, vecMul_vecMul, Matrix.nonsing_inv_mul _ hJu, vecMul_one]
      have hu₀i : (c : I.E) • u₀ ∈ IntV I := fun i => by
        have : ((c : I.E) • u₀) i = star (∑ j, ((D : I.E) * cv j) * ((c₁ : I.E) * I.J⁻¹ j i)) := by
          rw [Pi.smul_apply, smul_eq_mul, hu₀, Pi.star_apply, ← star_natCast (R := I.E) c, ← star_mul', vecMul,
            dotProduct, Finset.mul_sum, hc]
          congr 1
          refine Finset.sum_congr rfl fun j _ => ?_
          push_cast; ring
        rw [this]
        exact isIntegral_star (IsIntegral.sum _ fun j _ => (hcv j).mul (hcJ (j, i)))
      let q : VR I := toV I fun v => Formalism.REAL.Jm (I.ε v) *ᵥ ((2 : ℂ) • vecAt I y u₀ v)
      have hq : ∀ u : S, ⟪q, ι u⟫_ℝ = ⟪(z : VR I), ι u⟫_ℝ := fun u => by
        rw [← hgF, hι, inner_toV]
        have h1 := congrArg (fun r : ℚ => (r : ℝ)) (hgc u)
        simp only [Rat.cast_intCast] at h1
        rw [h1, trace_eq I hs, ← hu₀f]
        refine Finset.sum_congr rfl fun v _ => ?_
        rw [← hh, ← hf_uMat (y v)⁻¹ (atV I v u₀)]
        simp only [hf, star_smul, smul_dotProduct, vecAt]
        simp [co]
      have hqX : ∀ x ∈ X, ⟪q - z, x⟫_ℝ = 0 := fun x hx => by
        induction hx using Submodule.span_induction with
        | mem x hx => obtain ⟨u, hu, rfl⟩ := hx; rw [inner_sub_left, hq ⟨u, hu⟩, sub_self]
        | zero => simp
        | add _ _ _ _ h1 h2 => rw [inner_add_right, h1, h2, add_zero]
        | smul a _ _ h1 => rw [inner_smul_right, h1, mul_zero]
      have hu₀W : (c : I.E) • u₀ ∉ W := fun hW => hz0 (by
        have hW' : u₀ ∈ W := (W.smul_mem_iff (s := (c : I.E)) (by exact_mod_cast hc0.ne')).1 hW
        have h1 : ∀ x ∈ X, ⟪(z : VR I), x⟫_ℝ = 0 := fun x hx => by
          induction hx using Submodule.span_induction with
          | mem x hx =>
            obtain ⟨u, hu, rfl⟩ := hx
            have h2 := hgc u
            rw [← hu₀f, show hf I.J u₀ _ = 0 from hu u₀ hW', map_zero] at h2
            rw [← hgF ⟨u, hu⟩, show g u = 0 by exact_mod_cast h2, Int.cast_zero]
          | zero => simp
          | add _ _ _ _ h1 h2 => rw [inner_add_right, h1, h2, add_zero]
          | smul a _ _ h1 => rw [inner_smul_right, h1, mul_zero]
        exact Subtype.ext (inner_self_eq_zero.1 (h1 _ z.2)))

      let zJ : InfinitePlace I.F → Fin I.n → ℂ := fun v => Formalism.REAL.Jm (I.ε v) *ᵥ fun i => (z : VR I) (v, i)
      let a : InfinitePlace I.F → Fin I.n → ℂ := fun v => (2 : ℂ) • vecAt I y u₀ v - zJ v
      have hqa : q - z = toV I fun v => Formalism.REAL.Jm (I.ε v) *ᵥ a v := PiLp.ext fun p => by
        show (Formalism.REAL.Jm (I.ε p.1) *ᵥ ((2 : ℂ) • vecAt I y u₀ p.1)) p.2 - (z : VR I) p =
          (Formalism.REAL.Jm (I.ε p.1) *ᵥ a p.1) p.2
        simp only [a, zJ, Jm_mulVec, Pi.sub_apply]
        split_ifs <;> ring
      have haW : ∀ v, uMat (y v) *ᵥ a v ∈ Wv I W v := fun v => mem_of_perp_perp _ _ fun b' hb' => by
        rw [← hperp] at hb'
        have h1 : ∀ β : ℂ, (hf (Formalism.REAL.Jm (I.ε v)) (a v) (β • uMat (y v)⁻¹ *ᵥ b')).re = 0 := fun β => by
          have h2 := hqX _ (hXP (Pi.single v (β • b')) fun v' => by
            by_cases h : v' = v
            · subst h; rw [Pi.single_eq_same]; exact Submodule.smul_mem _ _ hb'
            · rw [Pi.single_eq_of_ne h]; exact Submodule.zero_mem _)
          rw [hqa, inner_toV, Finset.sum_eq_single v (fun v' _ h => by
            simp [Λ, Pi.single_eq_of_ne h, hf]) (by simp)] at h2
          simpa only [Λ, LinearMap.coe_mk, AddHom.coe_mk, Pi.single_eq_same, mulVec_smul] using h2
        rw [← hf_uMat (y v)⁻¹, mulVec_mulVec, uMat_inv_mul, one_mulVec]
        have h3 := h1 1
        have h4 := h1 Complex.I
        simp only [hf, mulVec_smul, dotProduct_smul, smul_eq_mul, one_mul, Complex.I_mul_re, neg_eq_zero] at h3 h4
        exact Complex.ext h3 h4
      obtain ⟨u', hu'i, hu'W, hu'⟩ := hcov (fun v => ((c : ℂ) / 2) • uMat (y v) *ᵥ a v) fun v =>
        Submodule.smul_mem _ _ (haW v)
      have h5 := hlong ((c : I.E) • u₀ - u') (fun i => (hu₀i i).sub (hu'i i))
        fun h => hu₀W (by simpa using W.add_mem h hu'W)
      have e5 : vecAt I y ((c : I.E) • u₀ - u') = ((fun v => uMat (y v)⁻¹ *ᵥ ((c : ℂ) / 2) • uMat (y v) *ᵥ a v) -
          vecAt I y u') + ((c : ℂ) / 2) • zJ := by
        funext v
        have : (c : I.E) • u₀ - u' = (c : I.E) • u₀ + (-1 : I.E) • u' := by simp [sub_eq_add_neg]
        simp only [this, vecAt, atV_add, atV_smul, mulVec_add, mulVec_smul, mulVec_mulVec, uMat_inv_mul, one_mulVec,
          Pi.add_apply, Pi.sub_apply, Pi.smul_apply, a, map_natCast, map_neg, map_one]
        module
      have h6 : ‖zJ‖ ≤ ‖z‖ := (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun v =>
        (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => by
          simp only [zJ, Jm_mulVec, norm_mul]
          have : ‖(if I.ε v i = true then (1 : ℂ) else -1)‖ = 1 := by split_ifs <;> simp
          rw [this, one_mul]
          exact PiLp.norm_apply_le (z : VR I) (v, i)
      rw [e5] at h5
      have h7 := h5.trans (norm_add_le_of_le hu' (norm_smul_le _ _))
      rw [norm_div, Complex.norm_natCast, Complex.norm_two] at h7
      rw [div_le_iff₀ hc0]
      nlinarith [mul_le_mul_of_nonneg_left h6 hc0.le]) ⟨_, hXP b hb⟩
  refine ⟨co u, fun i => (u i).2, huS, ?_⟩
  refine (norm_le_toV I _).trans (le_trans (le_of_eq ?_) (hm.trans ?_))
  · rw [map_sub, ← hι, hu]; rfl
  · have h1 : (Module.finrank ℝ X : ℝ) ≤ Module.finrank ℝ (VR I) := by exact_mod_cast X.finrank_le
    rw [div_le_div_iff₀ (by positivity) ht, mul_assoc, mul_left_comm (c : ℝ), mul_div_cancel₀ _ hc0.ne']
    nlinarith [(Nat.cast_nonneg (Module.finrank ℝ X) : (0 : ℝ) ≤ _)]

end CompanionTheory.D.gk.RF
