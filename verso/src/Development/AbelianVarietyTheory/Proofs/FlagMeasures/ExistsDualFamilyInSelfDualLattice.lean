import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPrincipalIdealRingOfHenselian
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG GlobalTheory.LocOver
open scoped Classical

noncomputable section

namespace GlobalTheory.SelfDualFrame

section Algebra

variable {E : Type} [CommRing E] (O : Subring E)

def consZero (n : ℕ) : (Fin n → O) →ₗ[O] (Fin (n + 1) → O) where
  toFun v := Fin.cons 0 v
  map_add' v w := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  map_smul' k v := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp

/- English proof (translation)
Introduce `n`. Proceed by induction on `n with`. Consider the case `zero`. Introduce `I _`. Rewrite using `[eq_top_iff]`.

Introduce `x _`. Rewrite using `[Subsingleton.elim x 0]`. Conclude with `I.zero_mem`. Consider the case `succ n ih`. Introduce `I hI`.

Establish `hJ : I.map (LinearMap.proj 0 : (Fin (n + 1) → O) →ₗ[O] O) = ⊤`. Use `hQ _ (fun d hd => ?_)` and prove the remaining obligations. Establish `h` using `hI (Pi.single 0 d) (fun x hx => by`. Establish `h1 : ∑ i, (Pi.single 0 d : Fin (n + 1) → E) i * (x i : E) = d * (x 0 : E)`. Rewrite using `[Finset.sum_eq_single 0]`.

Simplify using the standard rewrite rules. Introduce `b _ hb`. Simplify using `[Pi.single_apply, hb]`. Simplify using the standard rewrite rules. Rewrite using `[h1]`.

Conclude with `hd (x 0) ⟨x, hx, rfl⟩)`. Simplify using `using h 0`. Choose the witnesses or unpack the hypotheses as in `⟨x₁, hx₁, h1⟩ : ∃ x ∈ I, x 0 = 1 := by`. Establish `: (1 : O) ∈ I.map (LinearMap.proj 0 : (Fin (n + 1) → O) →ₗ[O] O)`. Rewrite using `[hJ]`.

Conclude with `Submodule.mem_top`. Take `⟨x, hx, e⟩` from `this`. Conclude with `⟨x, hx, e⟩`. Establish `hret : ∀ w : Fin (n + 1) → O, consZero O n (Fin.tail (w - w 0 • x₁)) = w - w 0 • x₁`. Introduce `w`.

Use extensionality with `i`. Use `Fin.cases ?_ (fun j => ?_) i` and prove the remaining obligations. Simplify using `[consZero, h1]`. Simplify using `[consZero, Fin.tail]`. Establish `hI₀ : I.comap (consZero O n) = ⊤`.

Use `ih _ (fun c hc => ?_)` and prove the remaining obligations. Establish `h` using `hI (Fin.cons (-∑ i, c i * (x₁ i.succ : E)) c) (fun w hw => by`. Establish `hm : Fin.tail (w - w 0 • x₁) ∈ I.comap (consZero O n)`. Rewrite using `[Submodule.mem_comap, hret]`. Conclude with `I.sub_mem hw (I.smul_mem _ hx₁)`.

Establish `h2` using `hc _ hm`. Rewrite using `[Fin.sum_univ_succ]`. Simplify using `only [Fin.cons_zero, Fin.cons_succ]`. Use `h2 using 1` and compare the differences between its conclusion and the goal. Simplify using `only [Fin.tail, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]`.

Use `push_cast`. Rewrite using `[neg_mul, Finset.sum_mul]`. Simplify using `only [mul_sub, Finset.sum_sub_distrib]`. Establish `e3 : ∀ i, c i * ((w 0 : E) * (x₁ i.succ : E)) = c i * (x₁ i.succ : E) * (w 0 : E)` using `fun i => by ring`. Simplify using `only [e3]`.

Use the proof step `ring)`. Introduce `i`. Simplify using `using h i.succ`. Rewrite using `[eq_top_iff]`. Introduce `w _`.

Establish `e : w = consZero O n (Fin.tail (w - w 0 • x₁)) + w 0 • x₁` using `by rw [hret]; abel`. Rewrite using `[e]`. Use `I.add_mem ?_ (I.smul_mem _ hx₁)` and prove the remaining obligations. Establish `: Fin.tail (w - w 0 • x₁) ∈ I.comap (consZero O n)` using `by rw [hI₀]; exact Submodule.mem_top`. Conclude with `this`.
-/
theorem eq_top_of_dual
    (hQ : ∀ J : Ideal O, (∀ d : E, (∀ j ∈ J, d * (j : E) ∈ O) → d ∈ O) → J = ⊤) :
    ∀ (n : ℕ) (I : Submodule O (Fin n → O)),
      (∀ c : Fin n → E, (∀ x ∈ I, ∑ i, c i * (x i : E) ∈ O) → ∀ i, c i ∈ O) → I = ⊤ := by
  intro n
  induction n with
  | zero =>
    intro I _
    rw [eq_top_iff]
    intro x _
    rw [Subsingleton.elim x 0]
    exact I.zero_mem
  | succ n ih =>
    intro I hI
    have hJ : I.map (LinearMap.proj 0 : (Fin (n + 1) → O) →ₗ[O] O) = ⊤ := by
      refine hQ _ (fun d hd => ?_)
      have h := hI (Pi.single 0 d) (fun x hx => by
        have h1 : ∑ i, (Pi.single 0 d : Fin (n + 1) → E) i * (x i : E) = d * (x 0 : E) := by
          rw [Finset.sum_eq_single 0]
          · simp
          · intro b _ hb; simp [Pi.single_apply, hb]
          · simp
        rw [h1]
        exact hd (x 0) ⟨x, hx, rfl⟩)
      simpa using h 0
    obtain ⟨x₁, hx₁, h1⟩ : ∃ x ∈ I, x 0 = 1 := by
      have : (1 : O) ∈ I.map (LinearMap.proj 0 : (Fin (n + 1) → O) →ₗ[O] O) := by
        rw [hJ]; exact Submodule.mem_top
      obtain ⟨x, hx, e⟩ := this
      exact ⟨x, hx, e⟩
    have hret : ∀ w : Fin (n + 1) → O, consZero O n (Fin.tail (w - w 0 • x₁)) = w - w 0 • x₁ := by
      intro w
      ext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [consZero, h1]
      · simp [consZero, Fin.tail]
    have hI₀ : I.comap (consZero O n) = ⊤ := by
      refine ih _ (fun c hc => ?_)
      have h := hI (Fin.cons (-∑ i, c i * (x₁ i.succ : E)) c) (fun w hw => by
        have hm : Fin.tail (w - w 0 • x₁) ∈ I.comap (consZero O n) := by
          rw [Submodule.mem_comap, hret]
          exact I.sub_mem hw (I.smul_mem _ hx₁)
        have h2 := hc _ hm
        rw [Fin.sum_univ_succ]
        simp only [Fin.cons_zero, Fin.cons_succ]
        convert h2 using 1
        simp only [Fin.tail, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        push_cast
        rw [neg_mul, Finset.sum_mul]
        simp only [mul_sub, Finset.sum_sub_distrib]
        have e3 : ∀ i, c i * ((w 0 : E) * (x₁ i.succ : E)) = c i * (x₁ i.succ : E) * (w 0 : E) :=
          fun i => by ring
        simp only [e3]
        ring)
      intro i
      simpa using h i.succ
    rw [eq_top_iff]
    intro w _
    have e : w = consZero O n (Fin.tail (w - w 0 • x₁)) + w 0 • x₁ := by rw [hret]; abel
    rw [e]
    refine I.add_mem ?_ (I.smul_mem _ hx₁)
    have : Fin.tail (w - w 0 • x₁) ∈ I.comap (consZero O n) := by rw [hI₀]; exact Submodule.mem_top
    exact this

end Algebra

section Local

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

/- English proof (translation)
Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible 𝒪[F]`. Take `⟨-, hO2, -, hPIR, hmem, -⟩` from `GlobalTheory.UnramOrder.order_facts L ϖ hϖ`. Establish `hcj : ∀ x ∈ L.O, L.cj x ∈ L.O` using `fun x hx => (hO2 x hx).1`. Establish `hz : ∀ u : F, (∀ t : F, algebraMap F E (t * u) ∈ L.O) → u = 0`. Introduce `u hu`.

Assume the negation of the conclusion as `h0`. Establish `h3` using `(hmem _).1 (hu ((ϖ : F)⁻¹ * u⁻¹))`. Rewrite `h3` using `[mul_assoc, inv_mul_cancel₀ h0, mul_one]`. Establish `hϖ0 : (ϖ : F) ≠ 0` using `fun h => hϖ.ne_zero (Subtype.ext h)`. Conclude with `hϖ.not_isUnit (IsUnit.of_mul_eq_one (a := ϖ) ⟨_, h3⟩ (Subtype.ext (by simp [hϖ0])))`.

Introduce `J hJ`. Take `⟨a, rfl⟩` from `(hPIR.principal J).principal`. Distinguish the cases in `hu : IsUnit (a : E)`. Take `⟨b, hb⟩` from `hu.exists_right_inv`. Establish `hbO : b ∈ L.O` using `hJ b (fun j hj => by`.

Take `⟨k, rfl⟩` from `Ideal.mem_span_singleton'.1 hj`. Use `push_cast`. Rewrite using `[show b * ((k : E) * a) = k by linear_combination (k : E) * hb]`. Conclude with `k.2)`. Conclude with `Ideal.span_singleton_eq_top.2 (IsUnit.of_mul_eq_one (a := a) ⟨b, hbO⟩ (Subtype.ext hb))`.

Use `exfalso haveI : Module.Finite F E := Module.finite_of_finrank_eq_succ L.rank`. Establish `hns : ¬ Function.Surjective (LinearMap.mulLeft F (a : E))` using `fun h => hu (by`. Take `⟨b, hb⟩` from `h 1`. Conclude with `IsUnit.of_mul_eq_one b hb)`. Establish `hni : ¬ Function.Injective (LinearMap.mulLeft F (a : E))` using `fun h => hns (LinearMap.injective_iff_surjective.1 h)`.

Choose the witnesses or unpack the hypotheses as in `⟨s, hs, hs0⟩ : ∃ s : E, (a : E) * s = 0 ∧ s ≠ 0 := by`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Conclude with `hni ((injective_iff_map_eq_zero _).2 (fun s h => hc s h))`. Establish `hts : ∀ t : F, algebraMap F E t * s ∈ L.O` using `fun t => hJ _ (fun j hj => by`.

Take `⟨k, rfl⟩` from `Ideal.mem_span_singleton'.1 hj`. Use `push_cast`. Rewrite using `[show algebraMap F E t * s * ((k : E) * a) = 0 by`. Take the linear combination `(algebraMap F E t * k) * hs]`. Conclude with `L.O.zero_mem)`.

Establish `hs1 : s ∈ L.O` using `by simpa using hts 1`. Take `⟨u, hu'⟩` from `(L.cj_fix (s + L.cj s)).1 (by rw [map_add, L.cj_cj, add_comm])`. Take `⟨m, hm⟩` from `(L.cj_fix (s * L.cj s)).1 (by rw [map_mul, L.cj_cj, mul_comm])`. Establish `hu0 : u = 0` using `hz u (fun t => by`. Establish `h4` using `L.O.add_mem (hts t) (hcj _ (hts t))`.

Use `h4 using 1` and compare the differences between its conclusion and the goal. Rewrite using `[map_mul, hu', map_mul, AlgEquiv.commutes]`. Use the proof step `ring)`. Establish `hm0 : m = 0` using `hz m (fun t => by`. Establish `h4` using `L.O.mul_mem (hts t) (hcj _ hs1)`.

Use `h4 using 1` and compare the differences between its conclusion and the goal. Rewrite using `[map_mul, hm]`. Use the proof step `ring)`. Rewrite `hu'` using `[hu0, map_zero]`. Rewrite `hm` using `[hm0, map_zero]`.

Establish `hss : s ^ 2 = 0` using `by linear_combination (-s) * hu' + hm`. Use `L.reduced` as an intermediate fact. Conclude with `hs0 (IsReduced.eq_zero s ⟨2, hss⟩)`.
-/
theorem ideal_eq_top_of_inv [IsNonarchimedeanLocalField F] [CharZero F] (L : LocE F E) :
    ∀ J : Ideal L.O, (∀ d : E, (∀ j ∈ J, d * (j : E) ∈ L.O) → d ∈ L.O) → J = ⊤ := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  obtain ⟨-, hO2, -, hPIR, hmem, -⟩ := GlobalTheory.UnramOrder.order_facts L ϖ hϖ
  have hcj : ∀ x ∈ L.O, L.cj x ∈ L.O := fun x hx => (hO2 x hx).1
  have hz : ∀ u : F, (∀ t : F, algebraMap F E (t * u) ∈ L.O) → u = 0 := by
    intro u hu
    by_contra h0
    have h3 := (hmem _).1 (hu ((ϖ : F)⁻¹ * u⁻¹))
    rw [mul_assoc, inv_mul_cancel₀ h0, mul_one] at h3
    have hϖ0 : (ϖ : F) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
    exact hϖ.not_isUnit (IsUnit.of_mul_eq_one (a := ϖ) ⟨_, h3⟩ (Subtype.ext (by simp [hϖ0])))
  intro J hJ
  obtain ⟨a, rfl⟩ := (hPIR.principal J).principal
  by_cases hu : IsUnit (a : E)
  · obtain ⟨b, hb⟩ := hu.exists_right_inv
    have hbO : b ∈ L.O := hJ b (fun j hj => by
      obtain ⟨k, rfl⟩ := Ideal.mem_span_singleton'.1 hj
      push_cast
      rw [show b * ((k : E) * a) = k by linear_combination (k : E) * hb]
      exact k.2)
    exact Ideal.span_singleton_eq_top.2 (IsUnit.of_mul_eq_one (a := a) ⟨b, hbO⟩ (Subtype.ext hb))
  · exfalso
    haveI : Module.Finite F E := Module.finite_of_finrank_eq_succ L.rank
    have hns : ¬ Function.Surjective (LinearMap.mulLeft F (a : E)) := fun h => hu (by
      obtain ⟨b, hb⟩ := h 1
      exact IsUnit.of_mul_eq_one b hb)
    have hni : ¬ Function.Injective (LinearMap.mulLeft F (a : E)) :=
      fun h => hns (LinearMap.injective_iff_surjective.1 h)
    obtain ⟨s, hs, hs0⟩ : ∃ s : E, (a : E) * s = 0 ∧ s ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact hni ((injective_iff_map_eq_zero _).2 (fun s h => hc s h))
    have hts : ∀ t : F, algebraMap F E t * s ∈ L.O := fun t => hJ _ (fun j hj => by
      obtain ⟨k, rfl⟩ := Ideal.mem_span_singleton'.1 hj
      push_cast
      rw [show algebraMap F E t * s * ((k : E) * a) = 0 by
        linear_combination (algebraMap F E t * k) * hs]
      exact L.O.zero_mem)
    have hs1 : s ∈ L.O := by simpa using hts 1
    obtain ⟨u, hu'⟩ := (L.cj_fix (s + L.cj s)).1 (by rw [map_add, L.cj_cj, add_comm])
    obtain ⟨m, hm⟩ := (L.cj_fix (s * L.cj s)).1 (by rw [map_mul, L.cj_cj, mul_comm])
    have hu0 : u = 0 := hz u (fun t => by
      have h4 := L.O.add_mem (hts t) (hcj _ (hts t))
      convert h4 using 1
      rw [map_mul, hu', map_mul, AlgEquiv.commutes]
      ring)
    have hm0 : m = 0 := hz m (fun t => by
      have h4 := L.O.mul_mem (hts t) (hcj _ hs1)
      convert h4 using 1
      rw [map_mul, hm]
      ring)
    rw [hu0, map_zero] at hu'
    rw [hm0, map_zero] at hm
    have hss : s ^ 2 = 0 := by linear_combination (-s) * hu' + hm
    have := L.reduced
    exact hs0 (IsReduced.eq_zero s ⟨2, hss⟩)

end Local

/- English proof (translation)
Introduce `F _ _ _ E _ _ _ _ M hM V _ _ H r Fr Λ hsd hfr`. Use `letI := hM.loc`. Use `haveI := hM.char0`. Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible 𝒪[F]`. Take `⟨-, hO2, -⟩` from `GlobalTheory.UnramOrder.order_facts M.L ϖ hϖ`.

Establish `hcj : ∀ x ∈ M.L.O, M.L.cj x ∈ M.L.O` using `fun x hx => (hO2 x hx).1`. Take `⟨-, -, hd⟩` from `hsd`. Take `⟨⟨hfΛ, hli, hprim⟩, -⟩` from `hfr`. Establish `hval : ∀ y ∈ Λ, ∀ a, H.h y (Fr.f a) ∈ M.L.O` using `fun y hy a => (hd y).1 hy _ (hfΛ a)`. Establish `hsum : ∀ (y : V) (g : Fin (r + 1) → V), H.h (∑ a, g a) y = ∑ a, H.h (g a) y` using `fun y g => map_sum (AddMonoidHom.mk' (fun x => H.h x y) (fun x x' => H.h_add_left x x' y)) g Finset.univ`.

Establish `hh2 : ∀ (y : V) (k : Fin (r + 1) → E), H.h y (∑ a, k a • Fr.f a) = ∑ a, M.L.cj (k a) * H.h y (Fr.f a)`. Introduce `y k`. Rewrite using `[H.h_herm, hsum, map_sum]`. Use `Finset.sum_congr rfl (fun a _ => ?_)` and prove the remaining obligations. Rewrite using `[H.h_smul_left, map_mul, ← H.h_herm]`.

Set `I : Submodule M.L.O (Fin (r + 1) → M.L.O)` to `{ carrier := {x | ∃ y ∈ Λ, ∀ a, (x a : E) = H.h y (Fr.f a)} add_mem' := by`. Introduce and unpack `x x' ⟨y, hy, e⟩ ⟨y', hy', e'⟩`. Use `⟨y + y', Λ.add_mem hy hy', fun a => ?_⟩` and prove the remaining obligations. Simplify using `only [Pi.add_apply, Subring.coe_add, H.h_add_left, e, e']`. Use the proof step `zero_mem' := ⟨0, Λ.zero_mem, fun a => by simp [H.h_zero_left]⟩`.

Use the proof step `smul_mem' := by`. Introduce and unpack `k x ⟨y, hy, e⟩`. Use `⟨k • y, Λ.smul_mem k hy, fun a => ?_⟩` and prove the remaining obligations. Simplify using `only [Pi.smul_apply, smul_eq_mul, Subring.coe_mul, e]`. Rewrite using `[Subring.smul_def, H.h_smul_left] }`.

Establish `hItop : I = ⊤`. Use `eq_top_of_dual M.L.O (ideal_eq_top_of_inv M.L) (r + 1) I (fun c hc => ?_)` and prove the remaining obligations. Use `set w := ∑ a, M.L.cj (c a) • Fr.f a with hwdef`. Establish `hw : ∀ y ∈ Λ, H.h y w ∈ M.L.O` using `fun y hy => by`. Establish `h1` using `hc (fun a => ⟨H.h y (Fr.f a), hval y hy a⟩) ⟨y, hy, fun a => rfl⟩`.

Rewrite using `[hwdef, hh2]`. Simplify `h1` using `[M.L.cj_cj]`. Establish `hwΛ : w ∈ Λ` using `(hd w).2 (fun y hy => by`. Rewrite using `[H.h_herm y w]`. Conclude with `hcj _ (hw y hy))`.

Establish `hwE : w ∈ Submodule.span E (Set.range Fr.f)` using `Submodule.sum_mem _ (fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩))`. Take `⟨d, hdw⟩` from `(Submodule.mem_span_range_iff_exists_fun M.L.O).1 (hprim w hwΛ hwE)`. Establish `heq : ∀ a, M.L.cj (c a) = d a`. Establish `h2` using `Fintype.linearIndependent_iff.1 hli (fun a => M.L.cj (c a) - (d a : E)) (by`. Simplify using `only [sub_smul, Finset.sum_sub_distrib]`.

Rewrite using `[← hwdef, ← hdw]`. Simplify using `[Subring.smul_def])`. Introduce `a`. Conclude with `sub_eq_zero.1 (h2 a)`. Introduce `a`.

Establish `h3` using `hcj _ (show M.L.cj (c a) ∈ M.L.O by rw [heq a]; exact (d a).2)`. Rewrite `h3` using `[M.L.cj_cj]`. Then use the resulting hypothesis. Establish `hmemb : ∀ b, ∃ y ∈ Λ, ∀ a, ((Pi.single b 1 : Fin (r + 1) → M.L.O) a : E) = H.h y (Fr.f a)` using `fun b => by`. Establish `h4 : (Pi.single b 1 : Fin (r + 1) → M.L.O) ∈ I` using `by rw [hItop]; exact Submodule.mem_top`. Conclude with `h4`.

Use `choose y hyΛ hy using hmemb`. Use `⟨y, hyΛ, fun a b => ?_⟩` and prove the remaining obligations. Rewrite using `[← hy b a, Pi.single_apply]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem exists_dual_family : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r : ℕ) (Fr : FrameD H r) (Λ : Submodule M.L.O V), H.IsSelfDual Λ → H.IsFrame Λ r Fr.f Fr.T → ∃ y : Fin (r + 1) → V, (∀ b, y b ∈ Λ) ∧ ∀ a b, H.h (y b) (Fr.f a) = if a = b then 1 else 0 := by
  intro F _ _ _ E _ _ _ _ M hM V _ _ H r Fr Λ hsd hfr
  letI := hM.loc
  haveI := hM.char0
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  obtain ⟨-, hO2, -⟩ := GlobalTheory.UnramOrder.order_facts M.L ϖ hϖ
  have hcj : ∀ x ∈ M.L.O, M.L.cj x ∈ M.L.O := fun x hx => (hO2 x hx).1
  obtain ⟨-, -, hd⟩ := hsd
  obtain ⟨⟨hfΛ, hli, hprim⟩, -⟩ := hfr
  have hval : ∀ y ∈ Λ, ∀ a, H.h y (Fr.f a) ∈ M.L.O := fun y hy a => (hd y).1 hy _ (hfΛ a)
  have hsum : ∀ (y : V) (g : Fin (r + 1) → V), H.h (∑ a, g a) y = ∑ a, H.h (g a) y := fun y g =>
    map_sum (AddMonoidHom.mk' (fun x => H.h x y) (fun x x' => H.h_add_left x x' y)) g Finset.univ
  have hh2 : ∀ (y : V) (k : Fin (r + 1) → E),
      H.h y (∑ a, k a • Fr.f a) = ∑ a, M.L.cj (k a) * H.h y (Fr.f a) := by
    intro y k
    rw [H.h_herm, hsum, map_sum]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [H.h_smul_left, map_mul, ← H.h_herm]
  let I : Submodule M.L.O (Fin (r + 1) → M.L.O) :=
    { carrier := {x | ∃ y ∈ Λ, ∀ a, (x a : E) = H.h y (Fr.f a)}
      add_mem' := by
        rintro x x' ⟨y, hy, e⟩ ⟨y', hy', e'⟩
        refine ⟨y + y', Λ.add_mem hy hy', fun a => ?_⟩
        simp only [Pi.add_apply, Subring.coe_add, H.h_add_left, e, e']
      zero_mem' := ⟨0, Λ.zero_mem, fun a => by simp [H.h_zero_left]⟩
      smul_mem' := by
        rintro k x ⟨y, hy, e⟩
        refine ⟨k • y, Λ.smul_mem k hy, fun a => ?_⟩
        simp only [Pi.smul_apply, smul_eq_mul, Subring.coe_mul, e]
        rw [Subring.smul_def, H.h_smul_left] }
  have hItop : I = ⊤ := by
    refine eq_top_of_dual M.L.O (ideal_eq_top_of_inv M.L) (r + 1) I (fun c hc => ?_)
    set w := ∑ a, M.L.cj (c a) • Fr.f a with hwdef
    have hw : ∀ y ∈ Λ, H.h y w ∈ M.L.O := fun y hy => by
      have h1 := hc (fun a => ⟨H.h y (Fr.f a), hval y hy a⟩) ⟨y, hy, fun a => rfl⟩
      rw [hwdef, hh2]
      simpa [M.L.cj_cj] using h1
    have hwΛ : w ∈ Λ := (hd w).2 (fun y hy => by
      rw [H.h_herm y w]
      exact hcj _ (hw y hy))
    have hwE : w ∈ Submodule.span E (Set.range Fr.f) :=
      Submodule.sum_mem _ (fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩))
    obtain ⟨d, hdw⟩ := (Submodule.mem_span_range_iff_exists_fun M.L.O).1 (hprim w hwΛ hwE)
    have heq : ∀ a, M.L.cj (c a) = d a := by
      have h2 := Fintype.linearIndependent_iff.1 hli (fun a => M.L.cj (c a) - (d a : E)) (by
        simp only [sub_smul, Finset.sum_sub_distrib]
        rw [← hwdef, ← hdw]
        simp [Subring.smul_def])
      intro a
      exact sub_eq_zero.1 (h2 a)
    intro a
    have h3 := hcj _ (show M.L.cj (c a) ∈ M.L.O by rw [heq a]; exact (d a).2)
    rwa [M.L.cj_cj] at h3
  have hmemb : ∀ b, ∃ y ∈ Λ, ∀ a, ((Pi.single b 1 : Fin (r + 1) → M.L.O) a : E) = H.h y (Fr.f a) :=
    fun b => by
      have h4 : (Pi.single b 1 : Fin (r + 1) → M.L.O) ∈ I := by rw [hItop]; exact Submodule.mem_top
      exact h4
  choose y hyΛ hy using hmemb
  refine ⟨y, hyΛ, fun a b => ?_⟩
  rw [← hy b a, Pi.single_apply]
  split_ifs <;> simp

end GlobalTheory.SelfDualFrame
