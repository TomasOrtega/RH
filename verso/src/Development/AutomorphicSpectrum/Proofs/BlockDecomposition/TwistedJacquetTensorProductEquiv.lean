import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.GenericProdIff
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OpenFns

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir.Leib GlobalTheory.CompanionTheory.Rodier
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.Rodier.PiCoinv

section Modules

variable {α : Type} {X : α → Type} [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)]

def pureSpan (K : ∀ a, Submodule ℂ (X a)) : Submodule ℂ (⨂[ℂ] a, X a) :=
  Submodule.span ℂ {t | ∃ (x : ∀ a, X a) (a : α), x a ∈ K a ∧ t = PiTensorProduct.tprod ℂ x}

/- English proof (translation)
Establish `key : ∀ s : Finset α, PiTensorProduct.tprod ℂ x - PiTensorProduct.tprod ℂ (fun a => if a ∈ s then y a else x a) ∈ pureSpan K`. Introduce `s`. Use `Finset.induction_on s ?_ ?_` and prove the remaining obligations. Simplify using the standard rewrite rules. Introduce `b s hb ih`.

Establish `hx : Function.update (fun a => if a ∈ s then y a else x a) b (x b) = (fun a => if a ∈ s then y a else x a)`. Rewrite using `[Function.update_eq_self_iff]`. Simplify using `[hb]`. Establish `hupd : (fun a => if a ∈ insert b s then y a else x a) = Function.update (fun a => if a ∈ s then y a else x a) b (y b)`. Use function extensionality and compare the values at `a`.

Distinguish the cases in `hab : a = b`. Substitute `hab` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Function.update_of_ne hab, Finset.mem_insert, hab]`. Establish `e : PiTensorProduct.tprod ℂ (Function.update (fun a => if a ∈ s then y a else x a) b (x b - y b)) = PiTensorProduct.tprod ℂ (fun a => if a ∈ s then y a else x a) - PiTensorProduct.tprod ℂ (fun a => if a ∈ insert b s then y a else x a)`.

Rewrite using `[MultilinearMap.map_update_sub, hx, hupd]`. Establish `hmem : PiTensorProduct.tprod ℂ (fun a => if a ∈ s then y a else x a) - PiTensorProduct.tprod ℂ (fun a => if a ∈ insert b s then y a else x a) ∈ pureSpan K`. Rewrite using `[← e]`. Conclude with `Submodule.subset_span ⟨_, b, by simpa using h b, rfl⟩`. Use `Submodule.add_mem _ ih hmem` as an intermediate fact.

Rewrite `this` using `[sub_add_sub_cancel]`. Then use the resulting hypothesis. Simplify using `using key Finset.univ`.
-/
theorem tprod_sub_mem [Fintype α] (K : ∀ a, Submodule ℂ (X a)) {x y : ∀ a, X a}
    (h : ∀ a, x a - y a ∈ K a) :
    PiTensorProduct.tprod ℂ x - PiTensorProduct.tprod ℂ y ∈ pureSpan K := by
  classical
  have key : ∀ s : Finset α, PiTensorProduct.tprod ℂ x -
      PiTensorProduct.tprod ℂ (fun a => if a ∈ s then y a else x a) ∈ pureSpan K := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · simp
    · intro b s hb ih
      have hx : Function.update (fun a => if a ∈ s then y a else x a) b (x b) =
          (fun a => if a ∈ s then y a else x a) := by
        rw [Function.update_eq_self_iff]
        simp [hb]
      have hupd : (fun a => if a ∈ insert b s then y a else x a) =
          Function.update (fun a => if a ∈ s then y a else x a) b (y b) := by
        funext a
        by_cases hab : a = b
        · subst hab
          simp
        · simp [Function.update_of_ne hab, Finset.mem_insert, hab]
      have e : PiTensorProduct.tprod ℂ
            (Function.update (fun a => if a ∈ s then y a else x a) b (x b - y b)) =
          PiTensorProduct.tprod ℂ (fun a => if a ∈ s then y a else x a) -
            PiTensorProduct.tprod ℂ (fun a => if a ∈ insert b s then y a else x a) := by
        rw [MultilinearMap.map_update_sub, hx, hupd]
      have hmem : PiTensorProduct.tprod ℂ (fun a => if a ∈ s then y a else x a) -
          PiTensorProduct.tprod ℂ (fun a => if a ∈ insert b s then y a else x a) ∈ pureSpan K := by
        rw [← e]
        exact Submodule.subset_span ⟨_, b, by simpa using h b, rfl⟩
      have := Submodule.add_mem _ ih hmem
      rwa [sub_add_sub_cancel] at this
  simpa using key Finset.univ

def rep (K : ∀ a, Submodule ℂ (X a)) (q : ∀ a, X a ⧸ K a) (a : α) : X a :=
  Function.surjInv (Submodule.mkQ_surjective (K a)) (q a)

/- English proof (translation)
Unfold `rep`. Conclude with `Function.surjInv_eq (Submodule.mkQ_surjective (K a)) (q a)`.
-/
theorem mkQ_rep (K : ∀ a, Submodule ℂ (X a)) (q : ∀ a, X a ⧸ K a) (a : α) :
    (K a).mkQ (rep K q a) = q a := by
  unfold rep
  exact Function.surjInv_eq (Submodule.mkQ_surjective (K a)) (q a)

def descendFun (K : ∀ a, Submodule ℂ (X a)) (q : ∀ a, X a ⧸ K a) : (⨂[ℂ] a, X a) ⧸ pureSpan K :=
  (pureSpan K).mkQ (PiTensorProduct.tprod ℂ (rep K q))

/- English proof (translation)
Unfold `descendFun`. Rewrite using `[Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]`. Conclude with `tprod_sub_mem K fun a => (Submodule.Quotient.eq _).1 ((mkQ_rep K q a).trans (hy a).symm)`.
-/
theorem descendFun_eq [Fintype α] (K : ∀ a, Submodule ℂ (X a)) (q : ∀ a, X a ⧸ K a) (y : ∀ a, X a)
    (hy : ∀ a, (K a).mkQ (y a) = q a) :
    descendFun K q = (pureSpan K).mkQ (PiTensorProduct.tprod ℂ y) := by
  unfold descendFun
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
  exact tprod_sub_mem K fun a => (Submodule.Quotient.eq _).1 ((mkQ_rep K q a).trans (hy a).symm)

/- English proof (translation)
Distinguish the cases in `hb : b = a`. Substitute `hb` using the available equality. Simplify using `[hw]`. Simplify using `[Function.update_of_ne hb, hy]`.
-/
theorem mkQ_update [DecidableEq α] (K : ∀ a, Submodule ℂ (X a)) {q : ∀ a, X a ⧸ K a} {y : ∀ a, X a}
    (hy : ∀ a, (K a).mkQ (y a) = q a) (a : α) {w : X a} {r : X a ⧸ K a} (hw : (K a).mkQ w = r) (b : α) :
    (K b).mkQ (Function.update y a w b) = Function.update q a r b := by
  by_cases hb : b = a
  · subst hb
    simp [hw]
  · simp [Function.update_of_ne hb, hy]

def descend [Fintype α] (K : ∀ a, Submodule ℂ (X a)) :
    MultilinearMap ℂ (fun a => X a ⧸ K a) ((⨂[ℂ] a, X a) ⧸ pureSpan K) where
  toFun := descendFun K
  map_update_add' := by
    intro _ q a u v
    obtain ⟨su, hu⟩ := Submodule.mkQ_surjective (K a) u
    obtain ⟨sv, hv⟩ := Submodule.mkQ_surjective (K a) v
    have hy := mkQ_rep K q
    rw [descendFun_eq K _ _ (mkQ_update K hy a (w := su + sv) (by rw [map_add, hu, hv])),
      descendFun_eq K _ _ (mkQ_update K hy a hu), descendFun_eq K _ _ (mkQ_update K hy a hv),
      MultilinearMap.map_update_add, map_add]
  map_update_smul' := by
    intro _ q a c u
    obtain ⟨su, hu⟩ := Submodule.mkQ_surjective (K a) u
    have hy := mkQ_rep K q
    rw [descendFun_eq K _ _ (mkQ_update K hy a (w := c • su) (by rw [map_smul, hu])),
      descendFun_eq K _ _ (mkQ_update K hy a hu), MultilinearMap.map_update_smul, map_smul]

def quotMap (K : ∀ a, Submodule ℂ (X a)) :
    ((⨂[ℂ] a, X a) ⧸ pureSpan K) →ₗ[ℂ] ⨂[ℂ] a, X a ⧸ K a :=
  (pureSpan K).liftQ (PiTensorProduct.map fun a => (K a).mkQ) (Submodule.span_le.2 (by
    rintro _ ⟨x, a, hx, rfl⟩
    show PiTensorProduct.map (fun a => (K a).mkQ) (PiTensorProduct.tprod ℂ x) = 0
    rw [PiTensorProduct.map_tprod]
    exact MultilinearMap.map_coord_zero _ a ((Submodule.Quotient.mk_eq_zero _).2 hx)))

def quotEquiv [Fintype α] (K : ∀ a, Submodule ℂ (X a)) :
    ((⨂[ℂ] a, X a) ⧸ pureSpan K) ≃ₗ[ℂ] ⨂[ℂ] a, X a ⧸ K a :=
  LinearEquiv.ofLinear (quotMap K) (PiTensorProduct.lift (descend K))
    (by
      refine PiTensorProduct.ext (MultilinearMap.ext fun q => ?_)
      show quotMap K (PiTensorProduct.lift (descend K) (PiTensorProduct.tprod ℂ q)) =
        PiTensorProduct.tprod ℂ q
      rw [PiTensorProduct.lift.tprod]
      show PiTensorProduct.map (fun a => (K a).mkQ) (PiTensorProduct.tprod ℂ (rep K q)) = _
      rw [PiTensorProduct.map_tprod]
      exact congrArg _ (funext (mkQ_rep K q)))
    (by
      refine Submodule.linearMap_qext _ (PiTensorProduct.ext (MultilinearMap.ext fun x => ?_))
      show PiTensorProduct.lift (descend K) (PiTensorProduct.map (fun a => (K a).mkQ)
        (PiTensorProduct.tprod ℂ x)) = (pureSpan K).mkQ (PiTensorProduct.tprod ℂ x)
      rw [PiTensorProduct.map_tprod, PiTensorProduct.lift.tprod]
      exact descendFun_eq K _ x fun _ => rfl)

end Modules

section Reps

variable {α : Type} [Fintype α] {Γ X : α → Type} [∀ a, Group (Γ a)] [∀ a, AddCommGroup (X a)]
  [∀ a, Module ℂ (X a)]

/- English proof (translation)
Unfold `twKer`. Apply `Submodule.span_le.2` to reduce the goal to its premises. Introduce and unpack `_ ⟨n, v, rfl⟩`. Proceed by induction on `v using PiTensorProduct.induction_on with`. Consider the case `smul_tprod r x`.

Establish `e1 : (piTensor π) (n : ∀ a, Γ a) (PiTensorProduct.tprod ℂ x) = PiTensorProduct.tprod ℂ (fun a => π a ((n : ∀ a, Γ a) a) (x a))` using `by show PiTensorProduct.map (fun a => π a ((n : ∀ a, Γ a) a)) (PiTensorProduct.tprod ℂ x) = _`. Rewrite using `[PiTensorProduct.map_tprod]`. Establish `e2 : ((piChar χ n : ℂˣ) : ℂ) = ∏ a, ((χ a ⟨(n : ∀ a, Γ a) a, n.2 a (Set.mem_univ a)⟩ : ℂˣ) : ℂ)`. Rewrite using `[← Units.coe_prod]`. Both sides reduce to the same expression.

Establish `e3` using `(MultilinearMap.map_smul_univ (PiTensorProduct.tprod ℂ) (fun a => ((χ a ⟨(n : ∀ a, Γ a) a, n.2 a (Set.mem_univ a)⟩ : ℂˣ) : ℂ)) x).symm`. Rewrite using `[map_smul, smul_comm, ← smul_sub]`. Apply `Submodule.smul_mem` to reduce the goal to its premises. Rewrite using `[e1, e2, e3]`. Apply `tprod_sub_mem` to reduce the goal to its premises.

Introduce `a`. Apply `Submodule.subset_span` to reduce the goal to its premises. Conclude with `⟨⟨(n : ∀ a, Γ a) a, n.2 a (Set.mem_univ a)⟩, x a, rfl⟩`. Consider the case `add v₁ v₂ h₁ h₂`. Rewrite using `[map_add, smul_add, add_sub_add_comm]`.

Conclude with `Submodule.add_mem _ h₁ h₂`.
-/
theorem twKer_piTensor_le (π : ∀ a, Representation ℂ (Γ a) (X a)) (H : ∀ a, Subgroup (Γ a))
    (χ : ∀ a, H a →* ℂˣ) :
    twKer (piTensor π) (piSub H) (piChar χ) ≤ pureSpan fun a => twKer (π a) (H a) (χ a) := by
  unfold twKer
  apply Submodule.span_le.2
  rintro _ ⟨n, v, rfl⟩
  induction v using PiTensorProduct.induction_on with
  | smul_tprod r x =>
    have e1 : (piTensor π) (n : ∀ a, Γ a) (PiTensorProduct.tprod ℂ x) =
        PiTensorProduct.tprod ℂ (fun a => π a ((n : ∀ a, Γ a) a) (x a)) := by
      show PiTensorProduct.map (fun a => π a ((n : ∀ a, Γ a) a)) (PiTensorProduct.tprod ℂ x) = _
      rw [PiTensorProduct.map_tprod]
    have e2 : ((piChar χ n : ℂˣ) : ℂ) =
        ∏ a, ((χ a ⟨(n : ∀ a, Γ a) a, n.2 a (Set.mem_univ a)⟩ : ℂˣ) : ℂ) := by
      rw [← Units.coe_prod]
      rfl
    have e3 := (MultilinearMap.map_smul_univ (PiTensorProduct.tprod ℂ)
      (fun a => ((χ a ⟨(n : ∀ a, Γ a) a, n.2 a (Set.mem_univ a)⟩ : ℂˣ) : ℂ)) x).symm
    rw [map_smul, smul_comm, ← smul_sub]
    apply Submodule.smul_mem
    rw [e1, e2, e3]
    apply tprod_sub_mem
    intro a
    apply Submodule.subset_span
    exact ⟨⟨(n : ∀ a, Γ a) a, n.2 a (Set.mem_univ a)⟩, x a, rfl⟩
  | add v₁ v₂ h₁ h₂ =>
    rw [map_add, smul_add, add_sub_add_comm]
    exact Submodule.add_mem _ h₁ h₂

/- English proof (translation)
Apply `Submodule.span_le.2` to reduce the goal to its premises. Introduce and unpack `_ ⟨x, a, hx, rfl⟩`. Establish `key : ∀ u ∈ twKer (π a) (H a) (χ a), PiTensorProduct.tprod ℂ (Function.update x a u) ∈ twKer (piTensor π) (piSub H) (piChar χ)`. Introduce `u hu`. Unfold `twKer at hu`.

Proceed by induction on `hu using Submodule.span_induction with`. Consider the case `mem u hu`. Take `⟨g, v, rfl⟩` from `hu`. Establish `hn : Pi.mulSingle a (g : Γ a) ∈ piSub H`. Use `(Subgroup.mem_pi _).2 fun b _ => ?_` and prove the remaining obligations.

Distinguish the cases in `hb : b = a`. Substitute `hb` using the available equality. Simplify using the standard rewrite rules. Rewrite using `[Pi.mulSingle_eq_of_ne hb]`. Conclude with `one_mem _`.

Set `n : piSub H` to `⟨Pi.mulSingle a (g : Γ a), hn⟩`. Establish `e1 : (piTensor π) (n : ∀ a, Γ a) (PiTensorProduct.tprod ℂ (Function.update x a v)) = PiTensorProduct.tprod ℂ (Function.update x a (π a (g : Γ a) v))` using `by show PiTensorProduct.map (fun b => π b ((n : ∀ a, Γ a) b)) (PiTensorProduct.tprod ℂ (Function.update x a v)) = _`. Rewrite using `[PiTensorProduct.map_tprod]`. Use `congr 1`. Use function extensionality and compare the values at `b`.

Distinguish the cases in `hb : b = a`. Substitute `hb` using the available equality. Simplify using `[n]`. Simplify using `[n, Function.update_of_ne hb, Pi.mulSingle_eq_of_ne hb]`. Establish `e2 : ((piChar χ n : ℂˣ) : ℂ) = ((χ a g : ℂˣ) : ℂ)`.

Establish `hu : (piChar χ n : ℂˣ) = ∏ b, χ b ⟨(n : ∀ a, Γ a) b, n.2 b (Set.mem_univ b)⟩` using `rfl`. Rewrite using `[hu, Finset.prod_eq_single a]`. Establish `: (⟨(n : ∀ a, Γ a) a, n.2 a (Set.mem_univ a)⟩ : H a) = g` using `Subtype.ext (by simp [n])`. Rewrite using `[this]`. Introduce `b _ hb`.

Establish `: (⟨(n : ∀ a, Γ a) b, n.2 b (Set.mem_univ b)⟩ : H b) = 1` using `Subtype.ext (by simp [n, Pi.mulSingle_eq_of_ne hb])`. Rewrite using `[this, map_one]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ a) h`. Establish `hw : PiTensorProduct.tprod ℂ (Function.update x a ((π a) (g : Γ a) v - ((χ a g : ℂˣ) : ℂ) • v)) = (piTensor π) (n : ∀ a, Γ a) (PiTensorProduct.tprod ℂ (Function.update x a v)) - ((piChar χ n : ℂˣ) : ℂ) • PiTensorProduct.tprod ℂ (Function.update x a v)`.

Rewrite using `[MultilinearMap.map_update_sub, MultilinearMap.map_update_smul, e1, e2]`. Rewrite using `[hw]`. Conclude with `Submodule.subset_span ⟨n, _, rfl⟩`. Consider the case `zero`. Rewrite using `[MultilinearMap.map_update_zero]`.

Conclude with `Submodule.zero_mem _`. Consider the case `add u₁ u₂ _ _ h₁ h₂`. Rewrite using `[MultilinearMap.map_update_add]`. Conclude with `Submodule.add_mem _ h₁ h₂`. Consider the case `smul c u _ h`.

Rewrite using `[MultilinearMap.map_update_smul]`. Conclude with `Submodule.smul_mem _ c h`. Use `key (x a) hx` as an intermediate fact. Rewrite `this` using `[Function.update_eq_self]`. Then use the resulting hypothesis.
-/
theorem pureSpan_le_twKer (π : ∀ a, Representation ℂ (Γ a) (X a)) (H : ∀ a, Subgroup (Γ a))
    (χ : ∀ a, H a →* ℂˣ) :
    (pureSpan fun a => twKer (π a) (H a) (χ a)) ≤ twKer (piTensor π) (piSub H) (piChar χ) := by
  classical
  apply Submodule.span_le.2
  rintro _ ⟨x, a, hx, rfl⟩
  have key : ∀ u ∈ twKer (π a) (H a) (χ a),
      PiTensorProduct.tprod ℂ (Function.update x a u) ∈ twKer (piTensor π) (piSub H) (piChar χ) := by
    intro u hu
    unfold twKer at hu
    induction hu using Submodule.span_induction with
    | mem u hu =>
      obtain ⟨g, v, rfl⟩ := hu
      have hn : Pi.mulSingle a (g : Γ a) ∈ piSub H := by
        refine (Subgroup.mem_pi _).2 fun b _ => ?_
        by_cases hb : b = a
        · subst hb
          simp
        · rw [Pi.mulSingle_eq_of_ne hb]
          exact one_mem _
      let n : piSub H := ⟨Pi.mulSingle a (g : Γ a), hn⟩
      have e1 : (piTensor π) (n : ∀ a, Γ a) (PiTensorProduct.tprod ℂ (Function.update x a v)) =
          PiTensorProduct.tprod ℂ (Function.update x a (π a (g : Γ a) v)) := by
        show PiTensorProduct.map (fun b => π b ((n : ∀ a, Γ a) b))
          (PiTensorProduct.tprod ℂ (Function.update x a v)) = _
        rw [PiTensorProduct.map_tprod]
        congr 1
        funext b
        by_cases hb : b = a
        · subst hb
          simp [n]
        · simp [n, Function.update_of_ne hb, Pi.mulSingle_eq_of_ne hb]
      have e2 : ((piChar χ n : ℂˣ) : ℂ) = ((χ a g : ℂˣ) : ℂ) := by
        have hu : (piChar χ n : ℂˣ) = ∏ b, χ b ⟨(n : ∀ a, Γ a) b, n.2 b (Set.mem_univ b)⟩ := rfl
        rw [hu, Finset.prod_eq_single a]
        · have : (⟨(n : ∀ a, Γ a) a, n.2 a (Set.mem_univ a)⟩ : H a) = g := Subtype.ext (by simp [n])
          rw [this]
        · intro b _ hb
          have : (⟨(n : ∀ a, Γ a) b, n.2 b (Set.mem_univ b)⟩ : H b) = 1 :=
            Subtype.ext (by simp [n, Pi.mulSingle_eq_of_ne hb])
          rw [this, map_one]
        · intro h
          exact absurd (Finset.mem_univ a) h
      have hw : PiTensorProduct.tprod ℂ (Function.update x a ((π a) (g : Γ a) v - ((χ a g : ℂˣ) : ℂ) • v)) =
          (piTensor π) (n : ∀ a, Γ a) (PiTensorProduct.tprod ℂ (Function.update x a v)) -
            ((piChar χ n : ℂˣ) : ℂ) • PiTensorProduct.tprod ℂ (Function.update x a v) := by
        rw [MultilinearMap.map_update_sub, MultilinearMap.map_update_smul, e1, e2]
      rw [hw]
      exact Submodule.subset_span ⟨n, _, rfl⟩
    | zero =>
      rw [MultilinearMap.map_update_zero]
      exact Submodule.zero_mem _
    | add u₁ u₂ _ _ h₁ h₂ =>
      rw [MultilinearMap.map_update_add]
      exact Submodule.add_mem _ h₁ h₂
    | smul c u _ h =>
      rw [MultilinearMap.map_update_smul]
      exact Submodule.smul_mem _ c h
  have := key (x a) hx
  rwa [Function.update_eq_self] at this

/- English proof (translation)
Conclude with `le_antisymm (twKer_piTensor_le π H χ) (pureSpan_le_twKer π H χ)`.
-/
theorem twKer_piTensor_eq (π : ∀ a, Representation ℂ (Γ a) (X a)) (H : ∀ a, Subgroup (Γ a))
    (χ : ∀ a, H a →* ℂˣ) :
    twKer (piTensor π) (piSub H) (piChar χ) = pureSpan fun a => twKer (π a) (H a) (χ a) := by
  exact le_antisymm (twKer_piTensor_le π H χ) (pureSpan_le_twKer π H χ)

end Reps

/- English proof (translation)
Introduce `α _ Γ X _ _ _ π H χ`. Conclude with `⟨(Submodule.quotEquivOfEq _ _ (twKer_piTensor_eq π H χ)).trans (quotEquiv fun a => twKer (π a) (H a) (χ a))⟩`.
-/
theorem twJacquet_piTensor_equiv : ∀ {α : Type} [Fintype α] {Γ X : α → Type} [∀ a, Group (Γ a)] [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (π : ∀ a, Representation ℂ (Γ a) (X a)) (H : ∀ a, Subgroup (Γ a)) (χ : ∀ a, H a →* ℂˣ), Nonempty (TwJacquet (piTensor π) (piSub H) (piChar χ) ≃ₗ[ℂ] ⨂[ℂ] a, TwJacquet (π a) (H a) (χ a)) := by
  intro α _ Γ X _ _ _ π H χ
  exact ⟨(Submodule.quotEquivOfEq _ _ (twKer_piTensor_eq π H χ)).trans
    (quotEquiv fun a => twKer (π a) (H a) (χ a))⟩

end GlobalTheory.CompanionTheory.Rodier.PiCoinv
