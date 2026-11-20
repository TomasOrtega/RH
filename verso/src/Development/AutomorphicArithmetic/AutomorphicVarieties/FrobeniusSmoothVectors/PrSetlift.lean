import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PresDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.InfPowBot

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

/- English proof (translation)
Introduce `_` and use `IsLocallyConstant.const _`.
-/
private theorem ac_const {Γ R : Type} [TopologicalSpace Γ] [CommRing R] (I : Ideal R) (c : R) :
    AdicCont I fun _ : Γ => c := fun _ => IsLocallyConstant.const _

/- English proof (translation)
Introduce `N` and use `by simp only [map_mul] exact (hf N).mul (hg N)`.
-/
private theorem ac_mul {Γ R : Type} [TopologicalSpace Γ] [CommRing R] {I : Ideal R} {f g : Γ → R}
    (hf : AdicCont I f) (hg : AdicCont I g) : AdicCont I fun s => f s * g s := fun N => by
  simp only [map_mul]
  exact (hf N).mul (hg N)

/- English proof (translation)
Introduce `N`. Establish `e : (fun s => Ideal.Quotient.mk (I ^ N) (∑ i ∈ S, f i s)) = ∑ i ∈ S, fun s => Ideal.Quotient.mk (I ^ N) (f i s)`. Use function extensionality and compare the values at `s`. Simplify using `only [map_sum, Finset.sum_apply]`. Rewrite using `[e]`.

Conclude with `Finset.sum_induction _ IsLocallyConstant (fun _ _ ha hb => ha.add hb) (IsLocallyConstant.const 0) (fun i _ => hf i N)`.
-/
private theorem ac_sum {Γ R ι : Type} [TopologicalSpace Γ] [CommRing R] {I : Ideal R} (S : Finset ι)
    {f : ι → Γ → R} (hf : ∀ i, AdicCont I (f i)) : AdicCont I fun s => ∑ i ∈ S, f i s := by
  intro N
  have e : (fun s => Ideal.Quotient.mk (I ^ N) (∑ i ∈ S, f i s)) = ∑ i ∈ S, fun s => Ideal.Quotient.mk (I ^ N) (f i s) := by
    funext s
    simp only [map_sum, Finset.sum_apply]
  rw [e]
  exact Finset.sum_induction _ IsLocallyConstant (fun _ _ ha hb => ha.add hb) (IsLocallyConstant.const 0) (fun i _ => hf i N)

/- English proof (translation)
Establish `hloc : ∀ a : C', IsUnit (p a) → IsUnit a`. Introduce `a ha`. Assume the negation of the conclusion as `hna`. Take `⟨b, hb⟩` from `hp (↑ha.unit⁻¹ : C)`. Establish `hK : a * b - 1 ∈ RingHom.ker (p : C' →+* C)`.

Rewrite using `[RingHom.mem_ker]`. Use `show p (a * b - 1) = 0`. Rewrite using `[map_sub, map_mul, map_one, hb, IsUnit.mul_val_inv, sub_self]`. Establish `hKm : RingHom.ker (p : C' →+* C) ≤ maximalIdeal C'` using `IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top _)`. Establish `ham : a ∈ maximalIdeal C'`.

Rewrite using `[IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]`. Conclude with `hna`. Establish `h1 : (1 : C') ∈ maximalIdeal C'`. Establish `h2` using `sub_mem (Ideal.mul_mem_right b _ ham) (hKm hK)`. Simplify using `using h2`.

Conclude with `(maximalIdeal.isMaximal C').ne_top ((Ideal.eq_top_iff_one _).2 h1)`. Set `Y : Fin n → Fin n → Γ → C'` to `fun i j => if ∀ s, x s i j = 0 then fun _ => 0 else Classical.choose (pr_sec O C' C p hp hk Γ (fun s => x s i j) (hx i j))`. Establish `hYc : ∀ i j, AdicCont (maximalIdeal C') (Y i j)`. Introduce `i j`. Distinguish the cases in `h : ∀ s, x s i j = 0`.

Simplify using `only [Y, if_pos h]`. Conclude with `fun _ => IsLocallyConstant.const _`. Simplify using `only [Y, if_neg h]`. Conclude with `(Classical.choose_spec (pr_sec O C' C p hp hk Γ (fun s => x s i j) (hx i j))).1`. Establish `hYp : ∀ i j s, p (Y i j s) = x s i j`.

Introduce `i j s`. Distinguish the cases in `h : ∀ s, x s i j = 0`. Simplify using `only [Y, if_pos h, map_zero]`. Conclude with `(h s).symm`. Simplify using `only [Y, if_neg h]`.

Conclude with `(Classical.choose_spec (pr_sec O C' C p hp hk Γ (fun s => x s i j) (hx i j))).2 s`. Establish `hY0 : ∀ i j, (∀ s, x s i j = 0) → ∀ s, Y i j s = 0`. Introduce `i j h s`. Simplify using `only [Y, if_pos h]`. Set `M : Γ → Matrix (Fin n) (Fin n) C'` to `fun s => Matrix.of fun i j => Y i j s`.

Establish `hMp : ∀ s, (M s).map p = (x s : Matrix (Fin n) (Fin n) C)`. Introduce `s`. Use extensionality with `i j`. Conclude with `hYp i j s`. Establish `hdet : ∀ s, IsUnit (M s).det`.

Introduce `s`. Apply `hloc` to reduce the goal to its premises. Establish `e : p (M s).det = ((M s).map p).det` using `RingHom.map_det (p : C' →+* C) (M s)`. Rewrite using `[e, hMp]`. Conclude with `Matrix.isUnits_det_units (x s)`.

Use `⟨fun s => Matrix.nonsingInvUnit (M s) (hdet s), fun i j => hYc i j, fun s => ?_, fun i j h s => hY0 i j h s⟩` and prove the remaining obligations. Apply `Units.ext` to reduce the goal to its premises. Conclude with `hMp s`.
-/
private theorem gl_lift {n : ℕ} (O : Type) [CommRing O] [IsLocalRing O] (C' : Type) [CommRing C'] [Algebra O C']
    [IsCO O C'] (C : Type) [CommRing C] [Algebra O C] [IsCO O C] (p : C' →ₐ[O] C) (hp : Function.Surjective p)
    (hk : maximalIdeal C' * RingHom.ker p = ⊥) (Γ : Type) [TopologicalSpace Γ] (x : Γ → GL (Fin n) C)
    (hx : ∀ i j, AdicCont (maximalIdeal C) fun s => x s i j) :
    ∃ y : Γ → GL (Fin n) C', (∀ i j, AdicCont (maximalIdeal C') fun s => y s i j) ∧
      (∀ s, GeneralLinearGroup.map (p : C' →+* C) (y s) = x s) ∧
      ∀ i j, (∀ s, x s i j = 0) → ∀ s, y s i j = 0 := by
  classical
  have hloc : ∀ a : C', IsUnit (p a) → IsUnit a := by
    intro a ha
    by_contra hna
    obtain ⟨b, hb⟩ := hp (↑ha.unit⁻¹ : C)
    have hK : a * b - 1 ∈ RingHom.ker (p : C' →+* C) := by
      rw [RingHom.mem_ker]
      show p (a * b - 1) = 0
      rw [map_sub, map_mul, map_one, hb, IsUnit.mul_val_inv, sub_self]
    have hKm : RingHom.ker (p : C' →+* C) ≤ maximalIdeal C' := IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top _)
    have ham : a ∈ maximalIdeal C' := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      exact hna
    have h1 : (1 : C') ∈ maximalIdeal C' := by
      have h2 := sub_mem (Ideal.mul_mem_right b _ ham) (hKm hK)
      simpa using h2
    exact (maximalIdeal.isMaximal C').ne_top ((Ideal.eq_top_iff_one _).2 h1)
  let Y : Fin n → Fin n → Γ → C' := fun i j =>
    if ∀ s, x s i j = 0 then fun _ => 0 else Classical.choose (pr_sec O C' C p hp hk Γ (fun s => x s i j) (hx i j))
  have hYc : ∀ i j, AdicCont (maximalIdeal C') (Y i j) := by
    intro i j
    by_cases h : ∀ s, x s i j = 0
    · simp only [Y, if_pos h]
      exact fun _ => IsLocallyConstant.const _
    · simp only [Y, if_neg h]
      exact (Classical.choose_spec (pr_sec O C' C p hp hk Γ (fun s => x s i j) (hx i j))).1
  have hYp : ∀ i j s, p (Y i j s) = x s i j := by
    intro i j s
    by_cases h : ∀ s, x s i j = 0
    · simp only [Y, if_pos h, map_zero]
      exact (h s).symm
    · simp only [Y, if_neg h]
      exact (Classical.choose_spec (pr_sec O C' C p hp hk Γ (fun s => x s i j) (hx i j))).2 s
  have hY0 : ∀ i j, (∀ s, x s i j = 0) → ∀ s, Y i j s = 0 := by
    intro i j h s
    simp only [Y, if_pos h]
  let M : Γ → Matrix (Fin n) (Fin n) C' := fun s => Matrix.of fun i j => Y i j s
  have hMp : ∀ s, (M s).map p = (x s : Matrix (Fin n) (Fin n) C) := by
    intro s
    ext i j
    exact hYp i j s
  have hdet : ∀ s, IsUnit (M s).det := by
    intro s
    apply hloc
    have e : p (M s).det = ((M s).map p).det := RingHom.map_det (p : C' →+* C) (M s)
    rw [e, hMp]
    exact Matrix.isUnits_det_units (x s)
  refine ⟨fun s => Matrix.nonsingInvUnit (M s) (hdet s), fun i j => hYc i j, fun s => ?_, fun i j h s => hY0 i j h s⟩
  apply Units.ext
  exact hMp s

/- English proof (translation)
Introduce `l _ k _ _ F C₀ n hF O _ _ C' _ _ _ C _ _ _ p B hp hk hcont`. Take `⟨r, hrc, hrm, -⟩` from `gl_lift O C' C p hp hk F.Γ (fun s => (B.r s).left) (fun i j => hcont i j)`. Establish `hg : ∀ v, ∃ a : GL (Fin n) C', GeneralLinearGroup.map (p : C' →+* C) a = B.g v`. Introduce `v`. Take `⟨y, -, hy, -⟩` from `gl_lift O C' C p hp hk Unit (fun _ => B.g v) (fun i j N => IsLocallyConstant.of_constant _ (fun _ _ => rfl))`.

Conclude with `⟨y (), hy ()⟩`. Establish `ht : ∀ v, ∃ y : F.Gv v → GL (Fin n) C', (∀ i j, AdicCont (maximalIdeal C') fun s => y s i j) ∧ (∀ s, GeneralLinearGroup.map (p : C' →+* C) (y s) = B.g v * (B.r (F.loc v s)).left * (B.g v)⁻¹) ∧ ∀ s, UpT (y s : Matrix (Fin n) (Fin n) C')`. Introduce `v`. Establish `hM : ∀ a b, AdicCont (maximalIdeal C) fun s : F.Gv v => (B.r (F.loc v s)).mat a b` using `fun a b N => (hcont a b N).comp_continuous (continuous_subtype_val.comp (hF.loc_cont v))`. Establish `hx : ∀ i j, AdicCont (maximalIdeal C) fun s : F.Gv v => ((B.g v * (B.r (F.loc v s)).left * (B.g v)⁻¹ : GL (Fin n) C) : Matrix (Fin n) (Fin n) C) i j`.

Introduce `i j`. Simplify using `only [Units.val_mul, Matrix.mul_apply]`. Conclude with `ac_sum _ (f := fun q s => (∑ a, (B.g v : Matrix (Fin n) (Fin n) C) i a * (B.r (F.loc v s)).mat a q) * ((B.g v)⁻¹ : GL (Fin n) C) q j) fun q => ac_mul (ac_sum _ (f := fun a s => (B.g v : Matrix (Fin n) (Fin n) C) i a * (B.r (F.loc v s)).mat a q) fun a => ac_mul (ac_const _ _) (hM …`. Take `⟨y, hyc, hym, hy0⟩` from `gl_lift O C' C p hp hk (F.Gv v) _ hx`. Use `⟨y, hyc, hym, fun s i j hij => hy0 i j (fun s' => B.tri v s' i j hij) s⟩` and prove the remaining obligations.

Use `choose g hgm using hg`. Use `choose t htc htm htt using ht`. Conclude with `⟨⟨r, hrc, hrm, g, hgm, t, htc, htt, htm⟩⟩`.
-/
theorem UpperTheory.V.Fr.pr_setlift :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ n : ℕ}, F.Ok C₀ → ∀ (O : Type) [CommRing O] [IsLocalRing O], ∀ (C' : Type) [CommRing C'] [Algebra O C'] [IsCO O C'] (C : Type) [CommRing C] [Algebra O C] [IsCO O C] (p : C' →ₐ[O] C) (B : Box F n C), Function.Surjective p → maximalIdeal C' * RingHom.ker p = ⊥ → B.Cont (maximalIdeal C) → Nonempty (SetLift p B) := by
  intro l _ k _ _ F C₀ n hF O _ _ C' _ _ _ C _ _ _ p B hp hk hcont
  obtain ⟨r, hrc, hrm, -⟩ := gl_lift O C' C p hp hk F.Γ (fun s => (B.r s).left) (fun i j => hcont i j)
  have hg : ∀ v, ∃ a : GL (Fin n) C', GeneralLinearGroup.map (p : C' →+* C) a = B.g v := by
    intro v
    obtain ⟨y, -, hy, -⟩ := gl_lift O C' C p hp hk Unit (fun _ => B.g v)
      (fun i j N => IsLocallyConstant.of_constant _ (fun _ _ => rfl))
    exact ⟨y (), hy ()⟩
  have ht : ∀ v, ∃ y : F.Gv v → GL (Fin n) C', (∀ i j, AdicCont (maximalIdeal C') fun s => y s i j) ∧
      (∀ s, GeneralLinearGroup.map (p : C' →+* C) (y s) = B.g v * (B.r (F.loc v s)).left * (B.g v)⁻¹) ∧
      ∀ s, UpT (y s : Matrix (Fin n) (Fin n) C') := by
    intro v
    have hM : ∀ a b, AdicCont (maximalIdeal C) fun s : F.Gv v => (B.r (F.loc v s)).mat a b :=
      fun a b N => (hcont a b N).comp_continuous (continuous_subtype_val.comp (hF.loc_cont v))
    have hx : ∀ i j, AdicCont (maximalIdeal C) fun s : F.Gv v => ((B.g v * (B.r (F.loc v s)).left * (B.g v)⁻¹ : GL (Fin n) C) : Matrix (Fin n) (Fin n) C) i j := by
      intro i j
      simp only [Units.val_mul, Matrix.mul_apply]
      exact ac_sum _ (f := fun q s => (∑ a, (B.g v : Matrix (Fin n) (Fin n) C) i a * (B.r (F.loc v s)).mat a q) * ((B.g v)⁻¹ : GL (Fin n) C) q j)
        fun q => ac_mul (ac_sum _ (f := fun a s => (B.g v : Matrix (Fin n) (Fin n) C) i a * (B.r (F.loc v s)).mat a q)
          fun a => ac_mul (ac_const _ _) (hM a q)) (ac_const _ _)
    obtain ⟨y, hyc, hym, hy0⟩ := gl_lift O C' C p hp hk (F.Gv v) _ hx
    refine ⟨y, hyc, hym, fun s i j hij => hy0 i j (fun s' => B.tri v s' i j hij) s⟩
  choose g hgm using hg
  choose t htc htm htt using ht
  exact ⟨⟨r, hrc, hrm, g, hgm, t, htc, htt, htm⟩⟩
