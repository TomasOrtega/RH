import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TprodMemTensSpan
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorPlaceActionInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MinFirst
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.KFixIrr.TensProj

open MvPolynomial Formalism.BasicNotions.TH

/- English proof (translation)
Apply `GlobalTheory.PiTensorCommute.eq_zero_of_forall_dualDistrib` to reduce the goal to its premises. Introduce `f`. Establish `hv : g (GlobalTheory.FactorKernel.contr w f T) = 0` using `hg _ fun L hL => by`. Rewrite using `[← GlobalTheory.FactorKernel.contr_atPl, hT L hL, map_zero]`. Establish `h` using `GlobalTheory.FactorKernel.dual_contr w f (f w) (GlobalTheory.RealLift.atPl (V := fun _ : ι => V) w g T)`.

Rewrite `h` using `[GlobalTheory.FactorKernel.contr_atPl, hv, map_zero, Function.update_eq_self]`. Conclude with `h.symm`.
-/
theorem atPl_eq_zero_of_common {ι : Type} [Fintype ι] [DecidableEq ι] {V : Type} [AddCommGroup V] [Module ℂ V]
    (w : ι) (F : Set (Module.End ℂ V)) (g : Module.End ℂ V) (hg : ∀ v, (∀ L ∈ F, L v = 0) → g v = 0)
    (T : ⨂[ℂ] _ : ι, V) (hT : ∀ L ∈ F, GlobalTheory.RealLift.atPl (V := fun _ : ι => V) w L T = 0) :
    GlobalTheory.RealLift.atPl (V := fun _ : ι => V) w g T = 0 := by
  apply GlobalTheory.PiTensorCommute.eq_zero_of_forall_dualDistrib
  intro f
  have hv : g (GlobalTheory.FactorKernel.contr w f T) = 0 := hg _ fun L hL => by
    rw [← GlobalTheory.FactorKernel.contr_atPl, hT L hL, map_zero]
  have h := GlobalTheory.FactorKernel.dual_contr w f (f w) (GlobalTheory.RealLift.atPl (V := fun _ : ι => V) w g T)
  rw [GlobalTheory.FactorKernel.contr_atPl, hv, map_zero, Function.update_eq_self] at h
  exact h.symm

/- English proof (translation)
Establish `e1 : L - c • 1 = L + (-c) • (1 : Module.End ℂ V)` using `by rw [neg_smul, sub_eq_add_neg]`. Establish `e2 : GlobalTheory.RealLift.atPl (V` using `fun _ : ι => V) w (1 : Module.End ℂ V) = 1 := by`. Unfold `GlobalTheory.RealLift.atPl`. Establish `: Function.update (fun i : ι => (LinearMap.id : V →ₗ[ℂ] V)) w (1 : Module.End ℂ V) = fun _ => LinearMap.id` using `Function.update_eq_self_iff.2 rfl`. Rewrite using `[this, PiTensorProduct.map_id]`.

Both sides reduce to the same expression. Rewrite using `[e1]`. Unfold `GlobalTheory.RealLift.atPl at e2 ⊢`. Rewrite using `[PiTensorProduct.map_update_add, PiTensorProduct.map_update_smul, e2]`. Simplify using `[sub_eq_add_neg]`.
-/
theorem atPl_sub_smul_one {ι : Type} [Fintype ι] [DecidableEq ι] {V : Type} [AddCommGroup V] [Module ℂ V]
    (w : ι) (L : Module.End ℂ V) (c : ℂ) (T : ⨂[ℂ] _ : ι, V) :
    GlobalTheory.RealLift.atPl (V := fun _ : ι => V) w (L - c • 1) T =
      GlobalTheory.RealLift.atPl (V := fun _ : ι => V) w L T - c • T := by
  have e1 : L - c • 1 = L + (-c) • (1 : Module.End ℂ V) := by rw [neg_smul, sub_eq_add_neg]
  have e2 : GlobalTheory.RealLift.atPl (V := fun _ : ι => V) w (1 : Module.End ℂ V) = 1 := by
    unfold GlobalTheory.RealLift.atPl
    have : Function.update (fun i : ι => (LinearMap.id : V →ₗ[ℂ] V)) w (1 : Module.End ℂ V) =
        fun _ => LinearMap.id := Function.update_eq_self_iff.2 rfl
    rw [this, PiTensorProduct.map_id]; rfl
  rw [e1]
  unfold GlobalTheory.RealLift.atPl at e2 ⊢
  rw [PiTensorProduct.map_update_add, PiTensorProduct.map_update_smul, e2]
  simp [sub_eq_add_neg]

end GlobalTheory.KFixIrr.TensProj

namespace GlobalTheory.KFixIrr.TensProj

open MvPolynomial Formalism.BasicNotions.TH

/- English proof (translation)
Establish `hex : ∀ n : ℕ, ∃ g : MvPolynomial σ ℂ →ₗ[ℂ] ↥(K ⊓ homogeneousSubmodule σ ℂ n), g ∘ₗ (K ⊓ homogeneousSubmodule σ ℂ n).subtype = LinearMap.id` using `fun n => LinearMap.exists_leftInverse_of_injective _ (Submodule.ker_subtype _)`. Use `choose g hg using hex`. Set `q : ℕ → MvPolynomial σ ℂ →ₗ[ℂ] MvPolynomial σ ℂ` to `fun n => (K ⊓ homogeneousSubmodule σ ℂ n).subtype ∘ₗ g n ∘ₗ homogeneousComponent n`. Establish `hq0 : ∀ f : MvPolynomial σ ℂ, ∀ N, f.totalDegree < N → ∑ i ∈ Finset.range (f.totalDegree + 1), q i f = ∑ i ∈ Finset.range N, q i f`. Introduce `f N hN`.

Apply `Finset.sum_subset (fun i hi => by simp only [Finset.mem_range] at hi ⊢; omega)` to reduce the goal to its premises. Introduce `i _ hi`. Establish `: f.totalDegree < i` using `by simp at hi; omega`. Simplify using `[q, homogeneousComponent_eq_zero _ _ this]`. Set `p : MvPolynomial σ ℂ →ₗ[ℂ] MvPolynomial σ ℂ` to `{ toFun := fun f => ∑ i ∈ Finset.range (f.totalDegree + 1), q i f map_add' := fun f f' => by`.

Rewrite using `[hq0 f (max (max f.totalDegree f'.totalDegree) (f + f').totalDegree + 1) (by omega), hq0 f' (max (max f.totalDegree f'.totalDegree) (f + f').totalDegree + 1) (by omega), hq0 (f + f') (max (max f.totalDegree f'.totalDegree) (f + f').totalDegree + 1) (by omega), ← Finset.sum_add_di …`. Simplify using `only [map_add]`. Use the proof step `map_smul' := fun c f => by`. Simplify using `only [RingHom.id_apply]`. Rewrite using `[hq0 f (max f.totalDegree (c • f).totalDegree + 1) (by omega), hq0 (c • f) (max f.totalDegree (c • f).totalDegree + 1) (by omega), Finset.smul_sum]`.

Simplify using `only [map_smul] }`. Use `⟨p, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `f show ∑ i ∈ Finset.range (f.totalDegree + 1), q i f ∈ K`. Conclude with `Submodule.sum_mem _ fun i _ => (g i (homogeneousComponent i f)).2.1`. Introduce `f hf show ∑ i ∈ Finset.range (f.totalDegree + 1), q i f = f conv_rhs => rw [← sum_homogeneousComponent f]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Establish `hm : homogeneousComponent i f ∈ K ⊓ homogeneousSubmodule σ ℂ i` using `⟨hK f hf i, homogeneousComponent_isHomogeneous i f⟩`. Use `congrArg (fun h => ((h ⟨_, hm⟩ : ↥(K ⊓ homogeneousSubmodule σ ℂ i)) : MvPolynomial σ ℂ)) (hg i)` as an intermediate fact. Simplify `this` using `[q]`. Introduce `f show (∑ i ∈ Finset.range (f.totalDegree + 1), q i f).totalDegree ≤ f.totalDegree`.

Use `(totalDegree_finset_sum _ _).trans (Finset.sup_le fun i hi => ?_)` and prove the remaining obligations. Establish `hi' : i ≤ f.totalDegree` using `by simp at hi; omega`. Establish `hh : (q i f).IsHomogeneous i` using `(g i (homogeneousComponent i f)).2.2`. Distinguish the cases in `h0 : q i f = 0`. Rewrite using `[h0, totalDegree_zero]`.

Conclude with `Nat.zero_le _`. Rewrite using `[hh.totalDegree h0]`. Conclude with `hi'`.
-/
theorem exists_proj_of_graded {σ : Type} (K : Submodule ℂ (MvPolynomial σ ℂ))
    (hK : ∀ f ∈ K, ∀ n, homogeneousComponent n f ∈ K) :
    ∃ p : MvPolynomial σ ℂ →ₗ[ℂ] MvPolynomial σ ℂ, (∀ f, p f ∈ K) ∧ (∀ f ∈ K, p f = f) ∧
      ∀ f, (p f).totalDegree ≤ f.totalDegree := by
  classical
  have hex : ∀ n : ℕ, ∃ g : MvPolynomial σ ℂ →ₗ[ℂ] ↥(K ⊓ homogeneousSubmodule σ ℂ n),
      g ∘ₗ (K ⊓ homogeneousSubmodule σ ℂ n).subtype = LinearMap.id := fun n =>
    LinearMap.exists_leftInverse_of_injective _ (Submodule.ker_subtype _)
  choose g hg using hex
  let q : ℕ → MvPolynomial σ ℂ →ₗ[ℂ] MvPolynomial σ ℂ := fun n =>
    (K ⊓ homogeneousSubmodule σ ℂ n).subtype ∘ₗ g n ∘ₗ homogeneousComponent n
  have hq0 : ∀ f : MvPolynomial σ ℂ, ∀ N, f.totalDegree < N →
      ∑ i ∈ Finset.range (f.totalDegree + 1), q i f = ∑ i ∈ Finset.range N, q i f := by
    intro f N hN
    apply Finset.sum_subset (fun i hi => by simp only [Finset.mem_range] at hi ⊢; omega)
    intro i _ hi
    have : f.totalDegree < i := by simp at hi; omega
    simp [q, homogeneousComponent_eq_zero _ _ this]
  let p : MvPolynomial σ ℂ →ₗ[ℂ] MvPolynomial σ ℂ :=
    { toFun := fun f => ∑ i ∈ Finset.range (f.totalDegree + 1), q i f
      map_add' := fun f f' => by
        rw [hq0 f (max (max f.totalDegree f'.totalDegree) (f + f').totalDegree + 1) (by omega),
          hq0 f' (max (max f.totalDegree f'.totalDegree) (f + f').totalDegree + 1) (by omega),
          hq0 (f + f') (max (max f.totalDegree f'.totalDegree) (f + f').totalDegree + 1) (by omega),
          ← Finset.sum_add_distrib]
        simp only [map_add]
      map_smul' := fun c f => by
        simp only [RingHom.id_apply]
        rw [hq0 f (max f.totalDegree (c • f).totalDegree + 1) (by omega),
          hq0 (c • f) (max f.totalDegree (c • f).totalDegree + 1) (by omega), Finset.smul_sum]
        simp only [map_smul] }
  refine ⟨p, ?_, ?_, ?_⟩
  · intro f
    show ∑ i ∈ Finset.range (f.totalDegree + 1), q i f ∈ K
    exact Submodule.sum_mem _ fun i _ => (g i (homogeneousComponent i f)).2.1
  · intro f hf
    show ∑ i ∈ Finset.range (f.totalDegree + 1), q i f = f
    conv_rhs => rw [← sum_homogeneousComponent f]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hm : homogeneousComponent i f ∈ K ⊓ homogeneousSubmodule σ ℂ i :=
      ⟨hK f hf i, homogeneousComponent_isHomogeneous i f⟩
    have := congrArg (fun h => ((h ⟨_, hm⟩ : ↥(K ⊓ homogeneousSubmodule σ ℂ i)) : MvPolynomial σ ℂ)) (hg i)
    simpa [q] using this
  · intro f
    show (∑ i ∈ Finset.range (f.totalDegree + 1), q i f).totalDegree ≤ f.totalDegree
    refine (totalDegree_finset_sum _ _).trans (Finset.sup_le fun i hi => ?_)
    have hi' : i ≤ f.totalDegree := by simp at hi; omega
    have hh : (q i f).IsHomogeneous i := (g i (homogeneousComponent i f)).2.2
    by_cases h0 : q i f = 0
    · rw [h0, totalDegree_zero]; exact Nat.zero_le _
    · rw [hh.totalDegree h0]; exact hi'

/- English proof (translation)
Establish `hh : ∀ i, fockAct1 P Q R S X (homogeneousComponent i f) ∈ homogeneousSubmodule (Ix P Q × Ix R S) ℂ i` using `fun i => GlobalTheory.FockAlg.MinFirst.kStable_homog i X hX _ (homogeneousComponent_isHomogeneous i f)`. Use `conv_lhs => rw [← sum_homogeneousComponent f, map_sum, map_sum]`. Repeatedly rewrite using `[homogeneousComponent_of_mem (hh _)]`. Rewrite using `[Finset.sum_ite_eq]`. Use `split_ifs with h`.

Both sides reduce to the same expression. Establish `: f.totalDegree < n` using `by simp at h; omega`. Rewrite using `[homogeneousComponent_eq_zero _ _ this, map_zero]`.
-/
theorem homogeneousComponent_fockAct1 {P Q R S : ℕ} (X : Mat P Q) (hX : IsKC X) (n : ℕ) (f : Pol P Q R S) :
    homogeneousComponent n (fockAct1 P Q R S X f) = fockAct1 P Q R S X (homogeneousComponent n f) := by
  classical
  have hh : ∀ i, fockAct1 P Q R S X (homogeneousComponent i f) ∈ homogeneousSubmodule (Ix P Q × Ix R S) ℂ i :=
    fun i => GlobalTheory.FockAlg.MinFirst.kStable_homog i X hX _ (homogeneousComponent_isHomogeneous i f)
  conv_lhs => rw [← sum_homogeneousComponent f, map_sum, map_sum]
  simp_rw [homogeneousComponent_of_mem (hh _)]
  rw [Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · have : f.totalDegree < n := by simp at h; omega
    rw [homogeneousComponent_eq_zero _ _ this, map_zero]

/- English proof (translation)
Rewrite `hf`, the goal using `[mem_chiOne]`. Introduce `X hX`. Rewrite using `[← homogeneousComponent_fockAct1 X hX, hf X hX, map_smul]`.
-/
theorem homogeneousComponent_mem_chiOne {P Q R S : ℕ} (x : ℚ) (f : Pol P Q R S) (hf : f ∈ chiOne P Q R S x) (n : ℕ) :
    homogeneousComponent n f ∈ chiOne P Q R S x := by
  rw [mem_chiOne] at hf ⊢
  intro X hX
  rw [← homogeneousComponent_fockAct1 X hX, hf X hX, map_smul]

end GlobalTheory.KFixIrr.TensProj

namespace GlobalTheory.KFixIrr

open MvPolynomial Formalism.BasicNotions.TH TensProj

/- English proof (translation)
Introduce `ι _ _ P Q R S x m T hT`. Take `⟨hchi, hdeg⟩` from `Submodule.mem_inf.1 hT`. Establish `hex : ∀ w, ∃ p : Pol P Q R S →ₗ[ℂ] Pol P Q R S, (∀ f, p f ∈ chiOne P Q R S (x w)) ∧ (∀ f ∈ chiOne P Q R S (x w), p f = f) ∧ ∀ f, (p f).totalDegree ≤ f.totalDegree` using `fun w => exists_proj_of_graded _ (homogeneousComponent_mem_chiOne (x w))`. Use `choose p hpK hpid hpdeg using hex`. Establish `hfix : ∀ w, GlobalTheory.RealLift.atPl (V` using `fun _ : ι => Pol P Q R S) w (p w) T = T := by`.

Introduce `w`. Establish `h0` using `atPl_eq_zero_of_common w {L | ∃ X : Mat P Q, IsKC X ∧ L = fockAct1 P Q R S X - ((x w : ℂ) * X.trace) • 1} (p w - 1) (fun v hv => by`. Establish `hv' : v ∈ chiOne P Q R S (x w)`. Rewrite using `[mem_chiOne]`. Introduce `X hX`.

Use `hv _ ⟨X, hX, rfl⟩` as an intermediate fact. Rewrite `this` using `[LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero]`. Then use the resulting hypothesis. Rewrite using `[LinearMap.sub_apply, Module.End.one_apply, hpid w v hv', sub_self])`. Use `T (by`. Introduce and unpack `L ⟨X, hX, rfl⟩`.

Rewrite using `[atPl_sub_smul_one, (mem_chiPart x T).1 hchi w X hX, sub_self])`. Establish `h1` using `atPl_sub_smul_one w (p w) 1 T`. Simplify using `only [one_smul] at h1`. Rewrite `h1` using `[h0]`. Conclude with `(sub_eq_zero.1 h1.symm)`.

Establish `hmap : ∀ s : Finset ι, PiTensorProduct.map (fun w => if w ∈ s then p w else (LinearMap.id : Pol P Q R S →ₗ[ℂ] Pol P Q R S)) T = T`. Introduce `s`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp [PiTensorProduct.map_id]`. Consider the case `insert a s ha ih`.

Establish `e : (fun w => if w ∈ insert a s then p w else (LinearMap.id : Pol P Q R S →ₗ[ℂ] Pol P Q R S)) = fun w => (Function.update (fun _ => (LinearMap.id : Pol P Q R S →ₗ[ℂ] Pol P Q R S)) a (p a) w) ∘ₗ (if w ∈ s then p w else LinearMap.id)`. Use function extensionality and compare the values at `w`. Distinguish the cases in `hw : w = a`. Substitute `hw` using the available equality. Simplify using `[ha]`.

Simplify using `[hw, Function.update_of_ne hw]`. Rewrite using `[e, PiTensorProduct.map_comp, LinearMap.comp_apply, ih]`. Conclude with `hfix a`. Establish `hT' : PiTensorProduct.map p T = T`. Use `hmap Finset.univ` as an intermediate fact.

Simplify using `using this`. Rewrite using `[← hT']`. Establish `hle : degLE ι P Q R S m ≤ (Submodule.span ℂ {U | ∃ g : ι → Formalism.BasicNotions.TH.Pol P Q R S, (∀ w, g w ∈ GlobalTheory.KFixIrr.chiOne P Q R S (x w)) ∧ ∑ w, (g w).totalDegree ≤ m ∧ U = PiTensorProduct.tprod ℂ g}).comap (PiTensorProduct.map p)`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `U ⟨f, hf, rfl⟩`.

Simplify using `only [SetLike.mem_coe, Submodule.mem_comap, PiTensorProduct.map_tprod]`. Conclude with `Submodule.subset_span ⟨fun w => p w (f w), fun w => hpK w _, (Finset.sum_le_sum fun w _ => hpdeg w (f w)).trans hf, rfl⟩`. Conclude with `hle hdeg`.
-/
theorem mem_span_tprod_chiOne : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (P Q R S : ℕ) (x : ι → ℚ) (m : ℕ)
    (T : ⨂[ℂ] _ : ι, Formalism.BasicNotions.TH.Pol P Q R S), T ∈ GlobalTheory.KFixIrr.chiPart ι P Q R S x ⊓ GlobalTheory.KFixIrr.degLE ι P Q R S m →
    T ∈ Submodule.span ℂ {U | ∃ g : ι → Formalism.BasicNotions.TH.Pol P Q R S, (∀ w, g w ∈ GlobalTheory.KFixIrr.chiOne P Q R S (x w)) ∧
      ∑ w, (g w).totalDegree ≤ m ∧ U = PiTensorProduct.tprod ℂ g} := by
  intro ι _ _ P Q R S x m T hT
  classical
  obtain ⟨hchi, hdeg⟩ := Submodule.mem_inf.1 hT
  have hex : ∀ w, ∃ p : Pol P Q R S →ₗ[ℂ] Pol P Q R S, (∀ f, p f ∈ chiOne P Q R S (x w)) ∧
      (∀ f ∈ chiOne P Q R S (x w), p f = f) ∧ ∀ f, (p f).totalDegree ≤ f.totalDegree := fun w =>
    exists_proj_of_graded _ (homogeneousComponent_mem_chiOne (x w))
  choose p hpK hpid hpdeg using hex

  have hfix : ∀ w, GlobalTheory.RealLift.atPl (V := fun _ : ι => Pol P Q R S) w (p w) T = T := by
    intro w
    have h0 := atPl_eq_zero_of_common w
      {L | ∃ X : Mat P Q, IsKC X ∧ L = fockAct1 P Q R S X - ((x w : ℂ) * X.trace) • 1}
      (p w - 1) (fun v hv => by
        have hv' : v ∈ chiOne P Q R S (x w) := by
          rw [mem_chiOne]
          intro X hX
          have := hv _ ⟨X, hX, rfl⟩
          rwa [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero] at this
        rw [LinearMap.sub_apply, Module.End.one_apply, hpid w v hv', sub_self])
      T (by
        rintro L ⟨X, hX, rfl⟩
        rw [atPl_sub_smul_one, (mem_chiPart x T).1 hchi w X hX, sub_self])
    have h1 := atPl_sub_smul_one w (p w) 1 T
    simp only [one_smul] at h1
    rw [h0] at h1
    exact (sub_eq_zero.1 h1.symm)

  have hmap : ∀ s : Finset ι,
      PiTensorProduct.map (fun w => if w ∈ s then p w else (LinearMap.id : Pol P Q R S →ₗ[ℂ] Pol P Q R S)) T = T := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [PiTensorProduct.map_id]
    | insert a s ha ih =>
      have e : (fun w => if w ∈ insert a s then p w else (LinearMap.id : Pol P Q R S →ₗ[ℂ] Pol P Q R S)) =
          fun w => (Function.update (fun _ => (LinearMap.id : Pol P Q R S →ₗ[ℂ] Pol P Q R S)) a (p a) w) ∘ₗ
            (if w ∈ s then p w else LinearMap.id) := by
        funext w
        by_cases hw : w = a
        · subst hw
          simp [ha]
        · simp [hw, Function.update_of_ne hw]
      rw [e, PiTensorProduct.map_comp, LinearMap.comp_apply, ih]
      exact hfix a
  have hT' : PiTensorProduct.map p T = T := by
    have := hmap Finset.univ
    simpa using this
  rw [← hT']

  have hle : degLE ι P Q R S m ≤ (Submodule.span ℂ {U | ∃ g : ι → Formalism.BasicNotions.TH.Pol P Q R S,
      (∀ w, g w ∈ GlobalTheory.KFixIrr.chiOne P Q R S (x w)) ∧ ∑ w, (g w).totalDegree ≤ m ∧
        U = PiTensorProduct.tprod ℂ g}).comap (PiTensorProduct.map p) := by
    refine Submodule.span_le.2 ?_
    rintro U ⟨f, hf, rfl⟩
    simp only [SetLike.mem_coe, Submodule.mem_comap, PiTensorProduct.map_tprod]
    exact Submodule.subset_span ⟨fun w => p w (f w), fun w => hpK w _,
      (Finset.sum_le_sum fun w _ => hpdeg w (f w)).trans hf, rfl⟩
  exact hle hdeg

end GlobalTheory.KFixIrr

end
