import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalIdealEqJointEigen

set_option autoImplicit false
noncomputable section
open MvPolynomial

namespace GlobalTheory.ExpCover

def transOp {L G W : Type} [CommRing L] [Mul G] [AddCommGroup W] [Module L W] (a : L) (t : Finset G) : (G → W) →ₗ[L] (G → W) where
  toFun v g := a • ∑ s ∈ t, v (g * s)
  map_add' v v' := by funext g; simp [Finset.sum_add_distrib, smul_add]
  map_smul' c v := by funext g; simp [Finset.smul_sum, smul_comm c]

set_option autoImplicit false in
/- English proof (translation)
Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => intro α _ c _`. Use function extensionality and compare the values at `j`. Conclude with `j.elim0`.

Consider the case `succ n ih`. Introduce `α hα c hc`. Establish `h0 : α 0 ≠ 0` using `hα.ne_zero 0`. Choose the witnesses or unpack the hypotheses as in `⟨x0, hx0⟩ : ∃ x0, α 0 x0 ≠ 0 := by`. Assume the negation of the conclusion as `h`.

Use `push_neg at h`. Conclude with `h0 (funext h)`. Establish `hea : emb (α 0 x0) ≠ 0` using `fun h => hx0 (hemb (by rw [h, map_zero]))`. Set `β : Fin n → X → O` to `fun j x => α 0 x0 * α j.succ x - α j.succ x0 * α 0 x`. Establish `hβ : LinearIndependent O β`.

Rewrite `hα`, the goal using `[Fintype.linearIndependent_iff]`. Introduce `d hd j`. Establish `hd' : ∀ x, ∑ k, d k * β k x = 0` using `fun x => by`. Simplify `congrFun hd x` using `[Finset.sum_apply]`. Establish `key` using `hα (Fin.cons (-(∑ k, d k * α k.succ x0)) (fun k => d k * α 0 x0)) (by`.

Use function extensionality and compare the values at `x`. Establish `e1 : ∑ k, d k * β k x = α 0 x0 * ∑ k, d k * α k.succ x - (∑ k, d k * α k.succ x0) * α 0 x`. Rewrite using `[Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]`. Conclude with `Finset.sum_congr rfl fun k _ => by simp only [β]; ring`. Establish `e2 : ∑ k, d k * α 0 x0 * α k.succ x = α 0 x0 * ∑ k, d k * α k.succ x`.

Rewrite using `[Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring`. Establish `h3` using `hd' x`. Rewrite `h3` using `[e1]`. Simplify using `only [Fin.sum_univ_succ, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Fin.cons_zero, Fin.cons_succ, Pi.zero_apply]`. Rewrite using `[e2]`.

Take the linear combination `h3)`. Use `key j.succ` as an intermediate fact. Simplify using `only [Fin.cons_succ] at this`. Conclude with `(mul_eq_zero.1 this).resolve_right hx0`. Establish `hS : ∀ x, c 0 * emb (α 0 x) + ∑ j : Fin n, c j.succ * emb (α j.succ x) = 0` using `fun x => by`.

Simplify `hc x` using `[Fin.sum_univ_succ]`. Establish `hrel : ∀ x, ∑ j, c j.succ * emb (β j x) = 0`. Introduce `x`. Establish `e : ∑ j, c j.succ * emb (β j x) = emb (α 0 x0) * ∑ j : Fin n, c j.succ * emb (α j.succ x) - (∑ j : Fin n, c j.succ * emb (α j.succ x0)) * emb (α 0 x)`. Rewrite using `[Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]`.

Conclude with `Finset.sum_congr rfl fun k _ => by simp only [β, map_sub, map_mul]; ring`. Rewrite using `[e]`. Take the linear combination `emb (α 0 x0) * hS x - emb (α 0 x) * hS x0`. Establish `htail` using `ih β hβ (fun j => c j.succ) hrel`. Establish `htail' : ∀ j : Fin n, c j.succ = 0` using `fun j => congrFun htail j`.

Establish `hc0 : c 0 = 0`. Use `hS x0` as an intermediate fact. Simplify using `only [htail', zero_mul, Finset.sum_const_zero, add_zero] at this`. Conclude with `(mul_eq_zero.1 this).resolve_right hea`. Use function extensionality and compare the values at `j`.

Use `Fin.cases ?_ (fun k => ?_) j` and prove the remaining obligations. Conclude with `hc0`. Conclude with `htail' k`.
-/
private lemma coeffs_eq_zero_of_linearIndependent_of_injective {O K X : Type} [CommRing O] [IsDomain O] [Field K]
    (emb : O →+* K) (hemb : Function.Injective emb) :
    ∀ (n : ℕ) (α : Fin n → X → O), LinearIndependent O α →
      ∀ c : Fin n → K, (∀ x, ∑ j, c j * emb (α j x) = 0) → c = 0 := by
  intro n
  induction n with
  | zero => intro α _ c _; funext j; exact j.elim0
  | succ n ih =>
    intro α hα c hc
    have h0 : α 0 ≠ 0 := hα.ne_zero 0
    obtain ⟨x0, hx0⟩ : ∃ x0, α 0 x0 ≠ 0 := by
      by_contra h
      push_neg at h
      exact h0 (funext h)
    have hea : emb (α 0 x0) ≠ 0 := fun h => hx0 (hemb (by rw [h, map_zero]))
    let β : Fin n → X → O := fun j x => α 0 x0 * α j.succ x - α j.succ x0 * α 0 x
    have hβ : LinearIndependent O β := by
      rw [Fintype.linearIndependent_iff] at hα ⊢
      intro d hd j
      have hd' : ∀ x, ∑ k, d k * β k x = 0 := fun x => by
        simpa [Finset.sum_apply] using congrFun hd x
      have key := hα (Fin.cons (-(∑ k, d k * α k.succ x0)) (fun k => d k * α 0 x0)) (by
        funext x
        have e1 : ∑ k, d k * β k x =
            α 0 x0 * ∑ k, d k * α k.succ x - (∑ k, d k * α k.succ x0) * α 0 x := by
          rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl fun k _ => by simp only [β]; ring
        have e2 : ∑ k, d k * α 0 x0 * α k.succ x = α 0 x0 * ∑ k, d k * α k.succ x := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
        have h3 := hd' x
        rw [e1] at h3
        simp only [Fin.sum_univ_succ, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Fin.cons_zero,
          Fin.cons_succ, Pi.zero_apply]
        rw [e2]
        linear_combination h3)
      have := key j.succ
      simp only [Fin.cons_succ] at this
      exact (mul_eq_zero.1 this).resolve_right hx0
    have hS : ∀ x, c 0 * emb (α 0 x) + ∑ j : Fin n, c j.succ * emb (α j.succ x) = 0 := fun x => by
      simpa [Fin.sum_univ_succ] using hc x
    have hrel : ∀ x, ∑ j, c j.succ * emb (β j x) = 0 := by
      intro x
      have e : ∑ j, c j.succ * emb (β j x) = emb (α 0 x0) * ∑ j : Fin n, c j.succ * emb (α j.succ x)
          - (∑ j : Fin n, c j.succ * emb (α j.succ x0)) * emb (α 0 x) := by
        rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun k _ => by simp only [β, map_sub, map_mul]; ring
      rw [e]
      linear_combination emb (α 0 x0) * hS x - emb (α 0 x) * hS x0
    have htail := ih β hβ (fun j => c j.succ) hrel
    have htail' : ∀ j : Fin n, c j.succ = 0 := fun j => congrFun htail j
    have hc0 : c 0 = 0 := by
      have := hS x0
      simp only [htail', zero_mul, Finset.sum_const_zero, add_zero] at this
      exact (mul_eq_zero.1 this).resolve_right hea
    funext j
    refine Fin.cases ?_ (fun k => ?_) j
    · exact hc0
    · exact htail' k

set_option autoImplicit false in
open MvPolynomial in

/- English proof (translation)
Set `N : Submodule (MvPolynomial I O) M` to `{ carrier := {y | ∀ g, (y : G → V) g ∈ U} add_mem' := fun {y z} hy hz g => by`. Simplify using `using U.add_mem (hy g) (hz g)`. Use the proof step `zero_mem' := fun g => by simp`. Use the proof step `smul_mem' := fun p y hy => by`. Proceed by induction on `p using MvPolynomial.induction_on with`.

Consider the case `C c`. Introduce `g`. Establish `h : (C c : MvPolynomial I O) • y = c • y`. Rewrite using `[← MvPolynomial.algebraMap_eq, algebraMap_smul]`. Rewrite using `[h, Submodule.coe_smul, Pi.smul_apply]`.

Conclude with `U.smul_mem c (hy g)`. Consider the case `add p q hp hq`. Introduce `g`. Rewrite using `[add_smul]`. Simplify using `using U.add_mem (hp g) (hq g)`.

Consider the case `mul_X p i hp`. Introduce `g`. Rewrite using `[mul_comm, mul_smul, hX i (p • y) g]`. Conclude with `U.smul_mem _ (U.sum_mem fun s _ => hp (g * s)) }`. Use `set z : M := a ^ J • x with hz_def`.

Set `A : Ideal (MvPolynomial I O)` to `N.comap (LinearMap.toSpanSingleton (MvPolynomial I O) M z)`. Establish `hA : ∀ p, p ∈ A ↔ p • z ∈ N` using `fun p => Iff.rfl`. Use `show z ∈ N`. Assume the negation of the conclusion as `hzN`. Establish `hAtop : A ≠ ⊤`.

Introduce `h`. Apply `hzN` to reduce the goal to its premises. Establish `h1' : (1 : MvPolynomial I O) ∈ A` using `h ▸ Submodule.mem_top`. Simplify using `using (hA 1).1 h1'`. Take `⟨m, hmax, hAm⟩` from `Ideal.exists_le_maximal A hAtop`.

Establish `key : ∃ θ : I → PadicAlgCl l, (∀ i, ‖θ i‖ ≤ 1) ∧ (∀ p, p ∈ m ↔ ‖eval₂ emb θ p‖ < 1) ∧ (∃ v ∈ S, v ≠ 0 ∧ ∀ i g, emb (cst i) • ∑ s ∈ tr i, v (g * s) = θ i • v g)` using `by haveI : Module.IsTorsionFree O V := Module.IsTorsionFree.of_smul_eq_zero fun r w h => by`. Establish `h' : emb r • b w = 0` using `by rw [← map_smulₛₗ, h, map_zero]`. Break down `smul_eq_zero.1 h' with h'' | h''` into its components or cases. Conclude with `Or.inl (hemb (by rw [h'', map_zero]))`. Conclude with `Or.inr (hb (by rw [h'', map_zero]))`.

Set `Z : Submodule (MvPolynomial I O) M` to `Submodule.span (MvPolynomial I O) {x}`. Set `ι : Z →ₗ[O] (G → V)` to `M.subtype ∘ₗ (Z.subtype.restrictScalars O)`. Establish `hι : Function.Injective ι` using `Subtype.val_injective.comp Subtype.val_injective`. Use `haveI : Module.IsTorsionFree O Z := hι.moduleIsTorsionFree _ (by simp)`. Use `haveI : Module.Finite O Z := Module.Finite.of_injective (Z.subtype.restrictScalars O) Subtype.val_injective`.

Use `haveI : Module.Free O Z := Module.free_of_finite_type_torsion_free'`. Set `B` to `Module.finBasis O Z`. Set `φ : MvPolynomial I O →ₐ[O] Module.End O Z` to `Algebra.lsmul O O Z`. Set `ρ : MvPolynomial I O →ₐ[O] Matrix (Fin (Module.finrank O Z)) (Fin (Module.finrank O Z)) O` to `(LinearMap.toMatrixAlgEquiv B).toAlgHom.comp φ`. Establish `hxZ : x ∈ Z` using `Submodule.subset_span rfl`.

Establish `hker : ∀ p ∈ RingHom.ker ρ, p • x = 0`. Introduce `p hp`. Establish `h0 : φ p = 0`. Establish `: ρ p = 0` using `hp`. Conclude with `(LinearMap.toMatrixAlgEquiv B).injective (by simpa [ρ] using this)`.

Use `congrArg Subtype.val (LinearMap.congr_fun h0 ⟨x, hxZ⟩)` as an intermediate fact. Simplify `this` using `[φ]`. Take `⟨θ, hθ1, hθm, c, hc0, hc⟩` from `_root_.GlobalTheory.maximal_ideal_eq_joint_eigen l O emb h1 hu I (Module.finrank O Z) ρ m hmax (fun p hp => hAm ((hA p).2 (by`. Rewrite using `[hz_def, smul_comm, hker p hp, smul_zero]`. Conclude with `N.zero_mem)))`.

Establish `hpS : ∀ p : MvPolynomial I O, (fun g => b (((p • x : M) : G → V) g)) ∈ S`. Introduce `p`. Proceed by induction on `p using MvPolynomial.induction_on with`. Consider the case `C r`. Establish `e : (fun g => b ((((C r : MvPolynomial I O) • x : M) : G → V) g)) = emb r • fun g => b ((x : G → V) g)`.

Use function extensionality and compare the values at `g`. Rewrite using `[← MvPolynomial.algebraMap_eq, algebraMap_smul]`. Simplify using `[map_smulₛₗ]`. Rewrite using `[e]`. Conclude with `S.smul_mem _ hx`.

Consider the case `add p q hp hq`. Establish `e : (fun g => b ((((p + q) • x : M) : G → V) g)) = (fun g => b (((p • x : M) : G → V) g)) + fun g => b (((q • x : M) : G → V) g)`. Use function extensionality and compare the values at `g`. Simplify using `[add_smul]`. Rewrite using `[e]`.

Conclude with `S.add_mem hp hq`. Consider the case `mul_X p i hp`. Establish `e : (fun g => b ((((p * X i) • x : M) : G → V) g)) = _root_.GlobalTheory.ExpCover.transOp (emb (cst i)) (tr i) (fun g => b (((p • x : M) : G → V) g))`. Use function extensionality and compare the values at `g`. Rewrite using `[mul_comm, mul_smul, hX]`.

Simplify using `[_root_.GlobalTheory.ExpCover.transOp, map_sum, map_smulₛₗ]`. Rewrite using `[e]`. Conclude with `hS i _ hp`. Establish `hZS : ∀ z ∈ Z, (fun g => b ((z : G → V) g)) ∈ S`. Introduce `z hz`.

Take `⟨p, rfl⟩` from `Submodule.mem_span_singleton.1 hz`. Conclude with `hpS p`. Set `f : Fin (Module.finrank O Z) → G → W` to `fun j g => b ((((B j : Z) : M) : G → V) g)`. Establish `hind : LinearIndependent (PadicAlgCl l) f` using `by haveI : Module.Free O V := Module.free_of_finite_type_torsion_free'`. Set `w` to `Module.finBasis O V`.

Establish `hw` using `hli _ w w.linearIndependent`. Set `L : Z →ₗ[O] (G × Fin (Module.finrank O V) → O)` to `LinearMap.pi fun p => (Finsupp.lapply p.2 ∘ₗ w.repr.toLinearMap) ∘ₗ (LinearMap.proj p.1 ∘ₗ ι)`. Establish `hL : Function.Injective L`. Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce `z hz`.

Apply `hι` to reduce the goal to its premises. Use function extensionality and compare the values at `g`. Apply `w.repr.injective` to reduce the goal to its premises. Use extensionality with `k`. Use `congrFun hz (g, k)` as an intermediate fact.

Simplify `this` using `[L]`. Establish `hα` using `B.linearIndependent.map' L (LinearMap.ker_eq_bot.2 hL)`. Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `c' hc'`. Establish `hfk : ∀ j g, f j g = ∑ k, emb ((L ∘ B) j (g, k)) • b (w k)`.

Introduce `j g`. Establish `e` using `congrArg b (w.sum_repr ((((B j : Z) : M) : G → V) g))`. Rewrite `e` using `[map_sum]`. Simplify using `only [map_smulₛₗ] at e`. Use `show b ((((B j : Z) : M) : G → V) g) = _`.

Rewrite using `[← e]`. Both sides reduce to the same expression. Establish `hzero : c' = 0` using `coeffs_eq_zero_of_linearIndependent_of_injective emb hemb _ _ hα c' fun p => by`. Establish `hg : ∑ j, c' j • f j p.1 = 0` using `by simpa [Finset.sum_apply] using congrFun hc' p.1`. Establish `hsum : ∑ k, (∑ j, c' j * emb ((L ∘ B) j (p.1, k))) • b (w k) = 0`.

Establish `e : ∑ k, (∑ j, c' j * emb ((L ∘ B) j (p.1, k))) • b (w k) = ∑ j, c' j • f j p.1`. Simplify using `only [hfk, Finset.smul_sum, Finset.sum_smul, smul_smul]`. Conclude with `Finset.sum_comm`. Rewrite using `[e, hg]`. Conclude with `(Fintype.linearIndependent_iff.1 hw) _ hsum p.2`.

Conclude with `fun j => congrFun hzero j`. Set `v : G → W` to `∑ j, c j • f j`. Establish `hv_apply : ∀ h, v h = ∑ j, c j • f j h` using `by intro h; simp [v, Finset.sum_apply]`. Use `⟨θ, hθ1, hθm, v, S.sum_mem fun j _ => S.smul_mem _ (hZS _ (B j).2), ?_, ?_⟩` and prove the remaining obligations. Introduce `hv0`.

Conclude with `hc0 (funext (Fintype.linearIndependent_iff.1 hind c hv0))`. Introduce `i g`. Establish `hXB : ∀ j, emb (cst i) • ∑ s ∈ tr i, f j (g * s) = ∑ k, emb (ρ (X i) k j) • f k g`. Introduce `j`. Establish `e1 : (X i : MvPolynomial I O) • B j = ∑ k, ρ (X i) k j • B k` using `by conv_lhs => rw [← B.sum_repr ((X i : MvPolynomial I O) • B j)]`.

Simplify using `[ρ, φ, LinearMap.toMatrixAlgEquiv_apply]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hX]`. Simplify using `[f, map_sum, map_smulₛₗ]`. Use `_ = b (((((X i : MvPolynomial I O) • B j : Z) : M) : G → V) g) := rfl`.

Use `_ = b ((((∑ k, ρ (X i) k j • B k : Z) : M) : G → V) g) := by rw [e1]`. Use `_ = ∑ k, emb (ρ (X i) k j) • f k g := by`. Simplify using `[f, map_sum, map_smulₛₗ, Submodule.coe_sum, Finset.sum_apply]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [hv_apply, Finset.smul_sum]`.

Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun s _ => smul_comm _ _ _`. Use `_ = ∑ j, c j • ∑ k, emb (ρ (X i) k j) • f k g := Finset.sum_congr rfl fun j _ => by rw [hXB]`. Use `_ = ∑ k, (∑ j, emb (ρ (X i) k j) * c j) • f k g := by`. Simplify using `only [Finset.smul_sum, Finset.sum_smul, smul_smul]`.

Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by rw [mul_comm]`. Use `_ = ∑ k, (θ i * c k) • f k g := by`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Use `congr 1`.

Use `congrFun (hc i) k` as an intermediate fact. Simplify `this` using `[Matrix.mulVec, dotProduct]`. Use `_ = θ i • v g := by`. Rewrite using `[hv_apply, Finset.smul_sum]`. Conclude with `Finset.sum_congr rfl fun k _ => by rw [smul_smul]`.

Take `⟨θ, hθ1, hθm, hv⟩` from `key`. Take `⟨x', hx'D, s, hs⟩` from `hloc m hmax θ hθ1 hθm hv (LocalizedModule.mk x 1)`. Rewrite `hs` using `[LocalizedModule.smul'_mk, LocalizedModule.mk_eq]`. Take `⟨u, hu⟩` from `hs`. Establish `hpow : (algebraMap O (MvPolynomial I O) a) ^ J • x = z`.

Rewrite using `[← map_pow, algebraMap_smul]`. Rewrite `hu` using `[hpow, one_smul]`. Establish `hmem : ((u : MvPolynomial I O) * (s : MvPolynomial I O)) • z ∈ N`. Rewrite using `[mul_smul]`. Express the relevant statement in the definitionally equal form `(u : MvPolynomial I O) • (s : MvPolynomial I O) • z ∈ N`.

Rewrite using `[← Submonoid.smul_def, ← Submonoid.smul_def, ← hu, Submonoid.smul_def]`. Conclude with `N.smul_mem _ (hD x' hx'D)`. Establish `hus` using `hAm ((hA _).2 hmem)`. Use `haveI := hmax.isPrime`. Break down `hmax.isPrime.mem_or_mem hus with h | h` into its components or cases.

Conclude with `u.2 h`. Conclude with `s.2 h`.
-/
theorem _root_.GlobalTheory.ExpCover.values_mem_of_local {l : ℕ} [Fact l.Prime] {O I G V W : Type} [CommRing O]
    [IsDomain O] [IsPrincipalIdealRing O] [Mul G]
    [AddCommGroup V] [Module O V] [Module.Finite O V] [AddCommGroup W] [Module (PadicAlgCl l) W]
    (M : Submodule O (G → V)) [hm : Module (MvPolynomial I O) M] [@IsScalarTower O (MvPolynomial I O) M _ hm.toSMul _]
    [Module.Finite O M]
    (emb : O →+* PadicAlgCl l) (hemb : Function.Injective emb)
    (h1 : ∀ c, ‖emb c‖ ≤ 1) (hu : ∀ c, ‖emb c‖ = 1 → IsUnit c) (b : V →ₛₗ[emb] W) (hb : Function.Injective b)
    (hli : ∀ (n : ℕ) (y : Fin n → V), LinearIndependent O y → LinearIndependent (PadicAlgCl l) fun j => b (y j))
    (tr : I → Finset G) (cst : I → O)
    (hX : ∀ i (f : M) g, (((X i : MvPolynomial I O) • f : M) : G → V) g = cst i • ∑ s ∈ tr i, (f : G → V) (g * s))
    (U : Submodule O V) (S : Submodule (PadicAlgCl l) (G → W))
    (hS : ∀ i, ∀ u ∈ S, _root_.GlobalTheory.ExpCover.transOp (emb (cst i)) (tr i) u ∈ S)
    (x : M) (hx : (fun g => b ((x : G → V) g)) ∈ S) (a : O) (J : ℕ) (D : Set M) (hD : ∀ y ∈ D, ∀ g, (y : G → V) g ∈ U)
    (hloc : ∀ (m : Ideal (MvPolynomial I O)) (hmax : m.IsMaximal) (θ : I → PadicAlgCl l), (∀ i, ‖θ i‖ ≤ 1) →
      (∀ p, p ∈ m ↔ ‖eval₂ emb θ p‖ < 1) →
      (∃ v ∈ S, v ≠ 0 ∧ ∀ i g, emb (cst i) • ∑ s ∈ tr i, v (g * s) = θ i • v g) →
      ∀ y : LocalizedModule (haveI := hmax.isPrime; m.primeCompl) M,
        ∃ x' ∈ D, ∃ s : (haveI := hmax.isPrime; m.primeCompl),
          LocalizedModule.mk x' s = (algebraMap O (MvPolynomial I O) a) ^ J • y) :
    ∀ g, ((a ^ J • x : M) : G → V) g ∈ U := by
  classical
  let N : Submodule (MvPolynomial I O) M :=
    { carrier := {y | ∀ g, (y : G → V) g ∈ U}
      add_mem' := fun {y z} hy hz g => by
        simpa using U.add_mem (hy g) (hz g)
      zero_mem' := fun g => by simp
      smul_mem' := fun p y hy => by
        induction p using MvPolynomial.induction_on with
        | C c =>
          intro g
          have h : (C c : MvPolynomial I O) • y = c • y := by
            rw [← MvPolynomial.algebraMap_eq, algebraMap_smul]
          rw [h, Submodule.coe_smul, Pi.smul_apply]
          exact U.smul_mem c (hy g)
        | add p q hp hq =>
          intro g
          rw [add_smul]
          simpa using U.add_mem (hp g) (hq g)
        | mul_X p i hp =>
          intro g
          rw [mul_comm, mul_smul, hX i (p • y) g]
          exact U.smul_mem _ (U.sum_mem fun s _ => hp (g * s)) }
  set z : M := a ^ J • x with hz_def
  let A : Ideal (MvPolynomial I O) := N.comap (LinearMap.toSpanSingleton (MvPolynomial I O) M z)
  have hA : ∀ p, p ∈ A ↔ p • z ∈ N := fun p => Iff.rfl
  show z ∈ N
  by_contra hzN
  have hAtop : A ≠ ⊤ := by
    intro h
    apply hzN
    have h1' : (1 : MvPolynomial I O) ∈ A := h ▸ Submodule.mem_top
    simpa using (hA 1).1 h1'
  obtain ⟨m, hmax, hAm⟩ := Ideal.exists_le_maximal A hAtop
  have key : ∃ θ : I → PadicAlgCl l, (∀ i, ‖θ i‖ ≤ 1) ∧ (∀ p, p ∈ m ↔ ‖eval₂ emb θ p‖ < 1) ∧
      (∃ v ∈ S, v ≠ 0 ∧ ∀ i g, emb (cst i) • ∑ s ∈ tr i, v (g * s) = θ i • v g) := by
    haveI : Module.IsTorsionFree O V := Module.IsTorsionFree.of_smul_eq_zero fun r w h => by
      have h' : emb r • b w = 0 := by rw [← map_smulₛₗ, h, map_zero]
      rcases smul_eq_zero.1 h' with h'' | h''
      · exact Or.inl (hemb (by rw [h'', map_zero]))
      · exact Or.inr (hb (by rw [h'', map_zero]))
    let Z : Submodule (MvPolynomial I O) M := Submodule.span (MvPolynomial I O) {x}
    let ι : Z →ₗ[O] (G → V) := M.subtype ∘ₗ (Z.subtype.restrictScalars O)
    have hι : Function.Injective ι := Subtype.val_injective.comp Subtype.val_injective
    haveI : Module.IsTorsionFree O Z := hι.moduleIsTorsionFree _ (by simp)
    haveI : Module.Finite O Z :=
      Module.Finite.of_injective (Z.subtype.restrictScalars O) Subtype.val_injective
    haveI : Module.Free O Z := Module.free_of_finite_type_torsion_free'
    let B := Module.finBasis O Z
    let φ : MvPolynomial I O →ₐ[O] Module.End O Z := Algebra.lsmul O O Z
    let ρ : MvPolynomial I O →ₐ[O] Matrix (Fin (Module.finrank O Z)) (Fin (Module.finrank O Z)) O :=
      (LinearMap.toMatrixAlgEquiv B).toAlgHom.comp φ
    have hxZ : x ∈ Z := Submodule.subset_span rfl
    have hker : ∀ p ∈ RingHom.ker ρ, p • x = 0 := by
      intro p hp
      have h0 : φ p = 0 := by
        have : ρ p = 0 := hp
        exact (LinearMap.toMatrixAlgEquiv B).injective (by simpa [ρ] using this)
      have := congrArg Subtype.val (LinearMap.congr_fun h0 ⟨x, hxZ⟩)
      simpa [φ] using this
    obtain ⟨θ, hθ1, hθm, c, hc0, hc⟩ := _root_.GlobalTheory.maximal_ideal_eq_joint_eigen l O emb h1 hu I
      (Module.finrank O Z) ρ m hmax (fun p hp => hAm ((hA p).2 (by
        rw [hz_def, smul_comm, hker p hp, smul_zero]; exact N.zero_mem)))
    have hpS : ∀ p : MvPolynomial I O, (fun g => b (((p • x : M) : G → V) g)) ∈ S := by
      intro p
      induction p using MvPolynomial.induction_on with
      | C r =>
        have e : (fun g => b ((((C r : MvPolynomial I O) • x : M) : G → V) g)) =
            emb r • fun g => b ((x : G → V) g) := by
          funext g
          rw [← MvPolynomial.algebraMap_eq, algebraMap_smul]
          simp [map_smulₛₗ]
        rw [e]; exact S.smul_mem _ hx
      | add p q hp hq =>
        have e : (fun g => b ((((p + q) • x : M) : G → V) g)) =
            (fun g => b (((p • x : M) : G → V) g)) + fun g => b (((q • x : M) : G → V) g) := by
          funext g; simp [add_smul]
        rw [e]; exact S.add_mem hp hq
      | mul_X p i hp =>
        have e : (fun g => b ((((p * X i) • x : M) : G → V) g)) =
            _root_.GlobalTheory.ExpCover.transOp (emb (cst i)) (tr i)
              (fun g => b (((p • x : M) : G → V) g)) := by
          funext g
          rw [mul_comm, mul_smul, hX]
          simp [_root_.GlobalTheory.ExpCover.transOp, map_sum, map_smulₛₗ]
        rw [e]; exact hS i _ hp
    have hZS : ∀ z ∈ Z, (fun g => b ((z : G → V) g)) ∈ S := by
      intro z hz
      obtain ⟨p, rfl⟩ := Submodule.mem_span_singleton.1 hz
      exact hpS p
    let f : Fin (Module.finrank O Z) → G → W := fun j g => b ((((B j : Z) : M) : G → V) g)
    have hind : LinearIndependent (PadicAlgCl l) f := by
      haveI : Module.Free O V := Module.free_of_finite_type_torsion_free'
      let w := Module.finBasis O V
      have hw := hli _ w w.linearIndependent
      let L : Z →ₗ[O] (G × Fin (Module.finrank O V) → O) :=
        LinearMap.pi fun p => (Finsupp.lapply p.2 ∘ₗ w.repr.toLinearMap) ∘ₗ (LinearMap.proj p.1 ∘ₗ ι)
      have hL : Function.Injective L := by
        rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
        intro z hz
        apply hι
        funext g
        apply w.repr.injective
        ext k
        have := congrFun hz (g, k)
        simpa [L] using this
      have hα := B.linearIndependent.map' L (LinearMap.ker_eq_bot.2 hL)
      rw [Fintype.linearIndependent_iff]
      intro c' hc'
      have hfk : ∀ j g, f j g = ∑ k, emb ((L ∘ B) j (g, k)) • b (w k) := by
        intro j g
        have e := congrArg b (w.sum_repr ((((B j : Z) : M) : G → V) g))
        rw [map_sum] at e
        simp only [map_smulₛₗ] at e
        show b ((((B j : Z) : M) : G → V) g) = _
        rw [← e]
        rfl
      have hzero : c' = 0 := coeffs_eq_zero_of_linearIndependent_of_injective emb hemb _ _ hα c' fun p => by
        have hg : ∑ j, c' j • f j p.1 = 0 := by simpa [Finset.sum_apply] using congrFun hc' p.1
        have hsum : ∑ k, (∑ j, c' j * emb ((L ∘ B) j (p.1, k))) • b (w k) = 0 := by
          have e : ∑ k, (∑ j, c' j * emb ((L ∘ B) j (p.1, k))) • b (w k) = ∑ j, c' j • f j p.1 := by
            simp only [hfk, Finset.smul_sum, Finset.sum_smul, smul_smul]
            exact Finset.sum_comm
          rw [e, hg]
        exact (Fintype.linearIndependent_iff.1 hw) _ hsum p.2
      exact fun j => congrFun hzero j
    let v : G → W := ∑ j, c j • f j
    have hv_apply : ∀ h, v h = ∑ j, c j • f j h := by intro h; simp [v, Finset.sum_apply]
    refine ⟨θ, hθ1, hθm, v, S.sum_mem fun j _ => S.smul_mem _ (hZS _ (B j).2), ?_, ?_⟩
    · intro hv0
      exact hc0 (funext (Fintype.linearIndependent_iff.1 hind c hv0))
    · intro i g
      have hXB : ∀ j, emb (cst i) • ∑ s ∈ tr i, f j (g * s) = ∑ k, emb (ρ (X i) k j) • f k g := by
        intro j
        have e1 : (X i : MvPolynomial I O) • B j = ∑ k, ρ (X i) k j • B k := by
          conv_lhs => rw [← B.sum_repr ((X i : MvPolynomial I O) • B j)]
          simp [ρ, φ, LinearMap.toMatrixAlgEquiv_apply]
        calc emb (cst i) • ∑ s ∈ tr i, f j (g * s)
            = b ((((X i : MvPolynomial I O) • ((B j : Z) : M) : M) : G → V) g) := by
              rw [hX]; simp [f, map_sum, map_smulₛₗ]
          _ = b (((((X i : MvPolynomial I O) • B j : Z) : M) : G → V) g) := rfl
          _ = b ((((∑ k, ρ (X i) k j • B k : Z) : M) : G → V) g) := by rw [e1]
          _ = ∑ k, emb (ρ (X i) k j) • f k g := by
              simp [f, map_sum, map_smulₛₗ, Submodule.coe_sum, Finset.sum_apply]
      calc emb (cst i) • ∑ s ∈ tr i, v (g * s)
          = ∑ j, c j • (emb (cst i) • ∑ s ∈ tr i, f j (g * s)) := by
            simp only [hv_apply, Finset.smul_sum]
            rw [Finset.sum_comm]
            exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun s _ => smul_comm _ _ _
        _ = ∑ j, c j • ∑ k, emb (ρ (X i) k j) • f k g :=
            Finset.sum_congr rfl fun j _ => by rw [hXB]
        _ = ∑ k, (∑ j, emb (ρ (X i) k j) * c j) • f k g := by
            simp only [Finset.smul_sum, Finset.sum_smul, smul_smul]
            rw [Finset.sum_comm]
            exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by rw [mul_comm]
        _ = ∑ k, (θ i * c k) • f k g := by
            refine Finset.sum_congr rfl fun k _ => ?_
            congr 1
            have := congrFun (hc i) k
            simpa [Matrix.mulVec, dotProduct] using this
        _ = θ i • v g := by
            rw [hv_apply, Finset.smul_sum]
            exact Finset.sum_congr rfl fun k _ => by rw [smul_smul]
  obtain ⟨θ, hθ1, hθm, hv⟩ := key
  obtain ⟨x', hx'D, s, hs⟩ := hloc m hmax θ hθ1 hθm hv (LocalizedModule.mk x 1)
  rw [LocalizedModule.smul'_mk, LocalizedModule.mk_eq] at hs
  obtain ⟨u, hu⟩ := hs
  have hpow : (algebraMap O (MvPolynomial I O) a) ^ J • x = z := by
    rw [← map_pow, algebraMap_smul]
  rw [hpow, one_smul] at hu
  have hmem : ((u : MvPolynomial I O) * (s : MvPolynomial I O)) • z ∈ N := by
    rw [mul_smul]
    change (u : MvPolynomial I O) • (s : MvPolynomial I O) • z ∈ N
    rw [← Submonoid.smul_def, ← Submonoid.smul_def, ← hu, Submonoid.smul_def]
    exact N.smul_mem _ (hD x' hx'D)
  have hus := hAm ((hA _).2 hmem)
  haveI := hmax.isPrime
  rcases hmax.isPrime.mem_or_mem hus with h | h
  · exact u.2 h
  · exact s.2 h

end GlobalTheory.ExpCover
