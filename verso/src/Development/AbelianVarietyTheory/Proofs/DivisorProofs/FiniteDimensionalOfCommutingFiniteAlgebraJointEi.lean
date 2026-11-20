import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfMemSpanK
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory Filter Topology

namespace GlobalTheory.FinEig

open Polynomial

variable {M : Type} [AddCommGroup M] [Module ℂ M]

/- English proof (translation)
Rewrite using `[← Submodule.fg_iff_finiteDimensional]`. Apply `Submodule.fg_of_fg_map_of_fg_inf_ker f` to reduce the goal to its premises. Establish `hle : (N ⊓ LinearMap.ker (g * f)).map f ≤ N ⊓ LinearMap.ker g`. Introduce and unpack `_ ⟨v, ⟨hvN, hv⟩, rfl⟩`. Conclude with `⟨hf v hvN, by simpa [LinearMap.mem_ker] using hv⟩`.

Use `haveI := Submodule.finiteDimensional_of_le hle`. Conclude with `(Submodule.fg_iff_finiteDimensional _).2 inferInstance`. Establish `hle : N ⊓ LinearMap.ker (g * f) ⊓ LinearMap.ker f ≤ N ⊓ LinearMap.ker f` using `fun v hv => ⟨hv.1.1, hv.2⟩ haveI := Submodule.finiteDimensional_of_le hle`. Conclude with `(Submodule.fg_iff_finiteDimensional _).2 inferInstance`.
-/
theorem fd_inf_ker_mul (N : Submodule ℂ M) (f g : Module.End ℂ M) (hf : ∀ v ∈ N, f v ∈ N)
    (h1 : FiniteDimensional ℂ ↥(N ⊓ LinearMap.ker f)) (h2 : FiniteDimensional ℂ ↥(N ⊓ LinearMap.ker g)) :
    FiniteDimensional ℂ ↥(N ⊓ LinearMap.ker (g * f)) := by
  rw [← Submodule.fg_iff_finiteDimensional]
  apply Submodule.fg_of_fg_map_of_fg_inf_ker f
  · have hle : (N ⊓ LinearMap.ker (g * f)).map f ≤ N ⊓ LinearMap.ker g := by
      rintro _ ⟨v, ⟨hvN, hv⟩, rfl⟩
      exact ⟨hf v hvN, by simpa [LinearMap.mem_ker] using hv⟩
    haveI := Submodule.finiteDimensional_of_le hle
    exact (Submodule.fg_iff_finiteDimensional _).2 inferInstance
  · have hle : N ⊓ LinearMap.ker (g * f) ⊓ LinearMap.ker f ≤ N ⊓ LinearMap.ker f :=
      fun v hv => ⟨hv.1.1, hv.2⟩
    haveI := Submodule.finiteDimensional_of_le hle
    exact (Submodule.fg_iff_finiteDimensional _).2 inferInstance

/- English proof (translation)
Proceed by induction on `hb using Algebra.adjoin_induction with`. Consider the case `mem x hx => exact hs x hx`. Consider the case `algebraMap r => intro v hv`. Simplify `N.smul_mem r hv` using `[Module.algebraMap_end_apply]`. Consider the case `add x y _ _ hx hy => intro v hv`.

Conclude with `N.add_mem (hx v hv) (hy v hv)`. Consider the case `mul x y _ _ hx hy => intro v hv`. Conclude with `hx _ (hy v hv)`.
-/
theorem adjoin_preserves (N : Submodule ℂ M) (s : Set (Module.End ℂ M)) (hs : ∀ u ∈ s, ∀ v ∈ N, u v ∈ N)
    {b : Module.End ℂ M} (hb : b ∈ Algebra.adjoin ℂ s) : ∀ v ∈ N, b v ∈ N := by
  induction hb using Algebra.adjoin_induction with
  | mem x hx => exact hs x hx
  | algebraMap r => intro v hv; simpa [Module.algebraMap_end_apply] using N.smul_mem r hv
  | add x y _ _ hx hy => intro v hv; exact N.add_mem (hx v hv) (hy v hv)
  | mul x y _ _ hx hy => intro v hv; exact hx _ (hy v hv)

/- English proof (translation)
Introduce `n`. Proceed by induction on `n with`. Consider the case `zero`. Introduce `q hq hq0`. Rewrite `hq0`, the goal using `[Polynomial.eq_C_of_natDegree_eq_zero hq]`.

Establish `ha : q.coeff 0 ≠ 0` using `fun e => hq0 (by rw [e, map_zero])`. Establish `hle : N ⊓ LinearMap.ker (aeval t (C (q.coeff 0))) ≤ ⊥`. Introduce `v hv`. Establish `h2` using `hv.2`. Simplify using `only [LinearMap.mem_ker, aeval_C, Module.algebraMap_end_apply] at h2`.

Simplify `(smul_eq_zero.1 h2).resolve_left ha` using `[Submodule.mem_bot]`. Conclude with `Submodule.finiteDimensional_of_le hle`. Consider the case `succ n ih`. Introduce `q hq hq0`. Establish `hdeg : 0 < q.degree`.

Rewrite using `[Polynomial.degree_eq_natDegree hq0, hq]`. Conclude with `Nat.succ_pos n` after adjusting the coercions. Take `⟨μ, hμ⟩` from `Complex.exists_root hdeg`. Establish `hfac` using `(Polynomial.mul_divByMonic_eq_iff_isRoot (a := μ) (p := q)).2 hμ`. Use `set q' := q /ₘ (X - C μ) with hq'`.

Establish `hq'0 : q' ≠ 0`. Introduce `e`. Apply `hq0` to reduce the goal to its premises. Rewrite using `[← hfac, e, mul_zero]`. Establish `hq'deg : q'.natDegree = n`.

Rewrite using `[hq', Polynomial.natDegree_divByMonic _ (Polynomial.monic_X_sub_C μ), hq, Polynomial.natDegree_X_sub_C]`. Both sides reduce to the same expression. Establish `hmul : aeval t q = (t - algebraMap ℂ (Module.End ℂ M) μ) * aeval t q'` using `by conv_lhs => rw [← hfac]`. Simplify using `[map_mul, map_sub, aeval_X, aeval_C]`. Rewrite using `[hmul]`.

Apply `fd_inf_ker_mul N _ _ _ (ih q' hq'deg hq'0) (h μ)` to reduce the goal to its premises. Conclude with `adjoin_preserves N {t} (by simpa using ht) (Polynomial.aeval_mem_adjoin_singleton ℂ t)`.
-/
theorem fd_inf_ker_aeval (N : Submodule ℂ M) (t : Module.End ℂ M) (ht : ∀ v ∈ N, t v ∈ N)
    (h : ∀ μ : ℂ, FiniteDimensional ℂ ↥(N ⊓ LinearMap.ker (t - algebraMap ℂ (Module.End ℂ M) μ))) :
    ∀ n : ℕ, ∀ q : ℂ[X], q.natDegree = n → q ≠ 0 → FiniteDimensional ℂ ↥(N ⊓ LinearMap.ker (aeval t q)) := by
  intro n
  induction n with
  | zero =>
    intro q hq hq0
    rw [Polynomial.eq_C_of_natDegree_eq_zero hq] at hq0 ⊢
    have ha : q.coeff 0 ≠ 0 := fun e => hq0 (by rw [e, map_zero])
    have hle : N ⊓ LinearMap.ker (aeval t (C (q.coeff 0))) ≤ ⊥ := by
      intro v hv
      have h2 := hv.2
      simp only [LinearMap.mem_ker, aeval_C, Module.algebraMap_end_apply] at h2
      simpa [Submodule.mem_bot] using (smul_eq_zero.1 h2).resolve_left ha
    exact Submodule.finiteDimensional_of_le hle
  | succ n ih =>
    intro q hq hq0
    have hdeg : 0 < q.degree := by
      rw [Polynomial.degree_eq_natDegree hq0, hq]; exact_mod_cast Nat.succ_pos n
    obtain ⟨μ, hμ⟩ := Complex.exists_root hdeg
    have hfac := (Polynomial.mul_divByMonic_eq_iff_isRoot (a := μ) (p := q)).2 hμ
    set q' := q /ₘ (X - C μ) with hq'
    have hq'0 : q' ≠ 0 := by
      intro e; apply hq0; rw [← hfac, e, mul_zero]
    have hq'deg : q'.natDegree = n := by
      rw [hq', Polynomial.natDegree_divByMonic _ (Polynomial.monic_X_sub_C μ), hq, Polynomial.natDegree_X_sub_C]; rfl
    have hmul : aeval t q = (t - algebraMap ℂ (Module.End ℂ M) μ) * aeval t q' := by
      conv_lhs => rw [← hfac]
      simp [map_mul, map_sub, aeval_X, aeval_C]
    rw [hmul]
    apply fd_inf_ker_mul N _ _ _ (ih q' hq'deg hq'0) (h μ)
    exact adjoin_preserves N {t} (by simpa using ht) (Polynomial.aeval_mem_adjoin_singleton ℂ t)

/- English proof (translation)
Proceed by induction on `T using Finset.induction_on with`. Consider the case `empty`. Introduce `N _ h`. Use `haveI := h 0`. Use `Submodule.finiteDimensional_of_le (S₂ := N ⊓ ⨅ u ∈ (∅ : Finset (Module.End ℂ M)), LinearMap.ker (u - algebraMap ℂ (Module.End ℂ M) ((0 : Module.End ℂ M → ℂ) u))) ?_` and prove the remaining obligations.

Introduce `v hv`. Use `⟨hv, ?_⟩` and prove the remaining obligations. Rewrite using `[SetLike.mem_coe, Submodule.mem_iInf]`. Introduce `u`. Rewrite using `[Submodule.mem_iInf]`.

Introduce `hu`. Simplify using `at hu`. Consider the case `insert t T htT ih`. Introduce `N hN h`. Take `⟨q, hq0, hq⟩` from `ha t (Finset.mem_insert_self t T)`.

Establish `key : ∀ μ : ℂ, FiniteDimensional ℂ ↥(N ⊓ LinearMap.ker (t - algebraMap ℂ (Module.End ℂ M) μ))`. Introduce `μ`. Apply `ih (fun u hu w hw => hc u (Finset.mem_insert_of_mem hu) w (Finset.mem_insert_of_mem hw)) (fun u hu => ha u (Finset.mem_insert_of_mem hu))` to reduce the goal to its premises. Introduce `u hu v hv`. Use `⟨hN u (Finset.mem_insert_of_mem hu) v hv.1, ?_⟩` and prove the remaining obligations.

Establish `h2 : (t - algebraMap ℂ (Module.End ℂ M) μ) v = 0` using `hv.2`. Establish `hcom` using `hc t (Finset.mem_insert_self t T) u (Finset.mem_insert_of_mem hu)`. Use `show (t - algebraMap ℂ (Module.End ℂ M) μ) (u v) = 0`. Rewrite `h2`, the goal using `[LinearMap.sub_apply, Module.algebraMap_end_apply]`. Rewrite using `[← Module.End.mul_apply, hcom, Module.End.mul_apply, ← map_smul, ← map_sub, h2, map_zero]`.

Introduce `c haveI := h (Function.update c t μ)`. Use `Submodule.finiteDimensional_of_le (S₂ := N ⊓ ⨅ u ∈ insert t T, LinearMap.ker (u - algebraMap ℂ (Module.End ℂ M) (Function.update c t μ u))) ?_` and prove the remaining obligations. Introduce `v hv`. Simplify using `only [Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker] at hv ⊢`. Take `⟨⟨hvN, hvt⟩, hvT⟩` from `hv`.

Use `⟨hvN, fun u hu => ?_⟩` and prove the remaining obligations. Break down `Finset.mem_insert.1 hu with rfl | hu'` into its components or cases. Simplify using `using hvt`. Establish `hne : u ≠ t` using `fun e => htT (e ▸ hu')`. Rewrite using `[Function.update_of_ne hne]`.

Conclude with `hvT u hu'`. Use `fd_inf_ker_aeval N t (hN t (Finset.mem_insert_self t T)) key _ q rfl hq0` as an intermediate fact. Rewrite `this` using `[hq, LinearMap.ker_zero, inf_top_eq]`. Then use the resulting hypothesis.
-/
theorem fd_of_finset (T : Finset (Module.End ℂ M)) (hc : ∀ u ∈ T, ∀ w ∈ T, u * w = w * u)
    (ha : ∀ u ∈ T, ∃ q : ℂ[X], q ≠ 0 ∧ aeval u q = 0) :
    ∀ N : Submodule ℂ M, (∀ u ∈ T, ∀ v ∈ N, u v ∈ N) →
      (∀ c : Module.End ℂ M → ℂ,
        FiniteDimensional ℂ ↥(N ⊓ ⨅ u ∈ T, LinearMap.ker (u - algebraMap ℂ (Module.End ℂ M) (c u)))) →
      FiniteDimensional ℂ ↥N := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    intro N _ h
    haveI := h 0
    refine Submodule.finiteDimensional_of_le (S₂ := N ⊓ ⨅ u ∈ (∅ : Finset (Module.End ℂ M)),
      LinearMap.ker (u - algebraMap ℂ (Module.End ℂ M) ((0 : Module.End ℂ M → ℂ) u))) ?_
    intro v hv
    refine ⟨hv, ?_⟩
    rw [SetLike.mem_coe, Submodule.mem_iInf]
    intro u
    rw [Submodule.mem_iInf]
    intro hu
    simp at hu
  | insert t T htT ih =>
    intro N hN h
    obtain ⟨q, hq0, hq⟩ := ha t (Finset.mem_insert_self t T)
    have key : ∀ μ : ℂ, FiniteDimensional ℂ ↥(N ⊓ LinearMap.ker (t - algebraMap ℂ (Module.End ℂ M) μ)) := by
      intro μ
      apply ih (fun u hu w hw => hc u (Finset.mem_insert_of_mem hu) w (Finset.mem_insert_of_mem hw))
        (fun u hu => ha u (Finset.mem_insert_of_mem hu))
      · intro u hu v hv
        refine ⟨hN u (Finset.mem_insert_of_mem hu) v hv.1, ?_⟩
        have h2 : (t - algebraMap ℂ (Module.End ℂ M) μ) v = 0 := hv.2
        have hcom := hc t (Finset.mem_insert_self t T) u (Finset.mem_insert_of_mem hu)
        show (t - algebraMap ℂ (Module.End ℂ M) μ) (u v) = 0
        rw [LinearMap.sub_apply, Module.algebraMap_end_apply] at h2 ⊢
        rw [← Module.End.mul_apply, hcom, Module.End.mul_apply, ← map_smul, ← map_sub, h2, map_zero]
      · intro c
        haveI := h (Function.update c t μ)
        refine Submodule.finiteDimensional_of_le (S₂ := N ⊓ ⨅ u ∈ insert t T,
          LinearMap.ker (u - algebraMap ℂ (Module.End ℂ M) (Function.update c t μ u))) ?_
        intro v hv
        simp only [Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker] at hv ⊢
        obtain ⟨⟨hvN, hvt⟩, hvT⟩ := hv
        refine ⟨hvN, fun u hu => ?_⟩
        rcases Finset.mem_insert.1 hu with rfl | hu'
        · simpa using hvt
        · have hne : u ≠ t := fun e => htT (e ▸ hu')
          rw [Function.update_of_ne hne]
          exact hvT u hu'
    have := fd_inf_ker_aeval N t (hN t (Finset.mem_insert_self t T)) key _ q rfl hq0
    rwa [hq, LinearMap.ker_zero, inf_top_eq] at this

end GlobalTheory.FinEig

namespace GlobalTheory.AutGrowth

/- English proof (translation)
Introduce `M _ _ S hS hB hE`. Use `letI : CommRing (Algebra.adjoin ℂ S) := Algebra.adjoinCommRingOfComm ℂ hS`. Establish `hcomm : ∀ x ∈ Algebra.adjoin ℂ S, ∀ y ∈ Algebra.adjoin ℂ S, x * y = y * x`. Introduce `x hx y hy`. Conclude with `congrArg Subtype.val (mul_comm (⟨x, hx⟩ : Algebra.adjoin ℂ S) ⟨y, hy⟩)`.

Take `⟨T, hT⟩ : (Algebra.adjoin ℂ S).FG` from `Subalgebra.fg_of_fg_toSubmodule ((Submodule.fg_iff_finiteDimensional _).2 hB)`. Establish `hTA : ∀ u ∈ T, u ∈ Algebra.adjoin ℂ S` using `fun u hu => hT ▸ Algebra.subset_adjoin hu`. Establish `key` using `GlobalTheory.FinEig.fd_of_finset T (fun u hu w hw => hcomm u (hTA u hu) w (hTA w hw)) (fun u hu => ((IsIntegral.of_finite ℂ (⟨u, hTA u hu⟩ : Algebra.adjoin ℂ S)).map (Algebra.adjoin ℂ S).val).isAlgebraic) ⊤ (fun _ _ _ _ => Submodule.mem_top) ?_`. Conclude with `Module.Finite.equiv Submodule.topEquiv`. Introduce `c`.

Establish `scal : ∀ b ∈ Algebra.adjoin ℂ S, ∃ μ : ℂ, ∀ v ∈ (⨅ u ∈ T, LinearMap.ker (u - algebraMap ℂ (Module.End ℂ M) (c u))), b v = μ • v`. Introduce `b hb`. Rewrite `hb` using `[← hT]`. Proceed by induction on `hb using Algebra.adjoin_induction with`. Consider the case `mem x hx`.

Use `⟨c x, fun v hv => ?_⟩` and prove the remaining obligations. Rewrite `hv` using `[Submodule.mem_iInf]`. Establish `h3` using `hv x`. Rewrite `h3` using `[Submodule.mem_iInf]`. Establish `h4` using `h3 hx`.

Rewrite `h4` using `[LinearMap.mem_ker, LinearMap.sub_apply, Module.algebraMap_end_apply, sub_eq_zero]`. Conclude with `h4`. Consider the case `algebraMap r => exact ⟨r, fun v _ => by simp [Module.algebraMap_end_apply]⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨μ₁, h₁⟩` from `hx`.

Take `⟨μ₂, h₂⟩` from `hy`. Conclude with `⟨μ₁ + μ₂, fun v hv => by rw [LinearMap.add_apply, h₁ v hv, h₂ v hv, add_smul]⟩`. Consider the case `mul x y _ _ hx hy`. Take `⟨μ₁, h₁⟩` from `hx`. Take `⟨μ₂, h₂⟩` from `hy`.

Conclude with `⟨μ₁ * μ₂, fun v hv => by`. Rewrite using `[Module.End.mul_apply, h₂ v hv, map_smul, h₁ v hv, smul_smul, mul_comm]⟩`. Set `c' : Module.End ℂ M → ℂ` to `fun s => if h : s ∈ Algebra.adjoin ℂ S then Classical.choose (scal s h) else 0`. Use `haveI := hE c'`. Use `Submodule.finiteDimensional_of_le (S₂ := ⨅ s ∈ S, LinearMap.ker (s - algebraMap ℂ (Module.End ℂ M) (c' s))) ?_` and prove the remaining obligations.

Introduce `v hv`. Use `replace hv := hv.2`. Simplify using `only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, Module.algebraMap_end_apply, sub_eq_zero]`. Introduce `s hs`. Establish `hsA : s ∈ Algebra.adjoin ℂ S` using `Algebra.subset_adjoin hs`.

Simplify using `only [c', dif_pos hsA]`. Conclude with `Classical.choose_spec (scal s hsA) v hv`.
-/
theorem finiteDimensional_of_commuting_finite_eigen :
    ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (S : Set (Module.End ℂ M)), (∀ s ∈ S, ∀ t ∈ S, s * t = t * s) →
      FiniteDimensional ℂ (Algebra.adjoin ℂ S) →
      (∀ c : Module.End ℂ M → ℂ, FiniteDimensional ℂ ↥(⨅ s ∈ S, LinearMap.ker (s - algebraMap ℂ (Module.End ℂ M) (c s)))) →
      FiniteDimensional ℂ M := by
  intro M _ _ S hS hB hE
  classical
  letI : CommRing (Algebra.adjoin ℂ S) := Algebra.adjoinCommRingOfComm ℂ hS
  have hcomm : ∀ x ∈ Algebra.adjoin ℂ S, ∀ y ∈ Algebra.adjoin ℂ S, x * y = y * x := by
    intro x hx y hy
    exact congrArg Subtype.val (mul_comm (⟨x, hx⟩ : Algebra.adjoin ℂ S) ⟨y, hy⟩)
  obtain ⟨T, hT⟩ : (Algebra.adjoin ℂ S).FG :=
    Subalgebra.fg_of_fg_toSubmodule ((Submodule.fg_iff_finiteDimensional _).2 hB)
  have hTA : ∀ u ∈ T, u ∈ Algebra.adjoin ℂ S := fun u hu => hT ▸ Algebra.subset_adjoin hu
  have key := GlobalTheory.FinEig.fd_of_finset T (fun u hu w hw => hcomm u (hTA u hu) w (hTA w hw))
    (fun u hu => ((IsIntegral.of_finite ℂ (⟨u, hTA u hu⟩ : Algebra.adjoin ℂ S)).map
      (Algebra.adjoin ℂ S).val).isAlgebraic) ⊤ (fun _ _ _ _ => Submodule.mem_top) ?_
  · exact Module.Finite.equiv Submodule.topEquiv
  intro c
  have scal : ∀ b ∈ Algebra.adjoin ℂ S, ∃ μ : ℂ, ∀ v ∈ (⨅ u ∈ T, LinearMap.ker (u - algebraMap ℂ (Module.End ℂ M) (c u))), b v = μ • v := by
    intro b hb
    rw [← hT] at hb
    induction hb using Algebra.adjoin_induction with
    | mem x hx =>
      refine ⟨c x, fun v hv => ?_⟩
      rw [Submodule.mem_iInf] at hv
      have h3 := hv x
      rw [Submodule.mem_iInf] at h3
      have h4 := h3 hx
      rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.algebraMap_end_apply, sub_eq_zero] at h4
      exact h4
    | algebraMap r => exact ⟨r, fun v _ => by simp [Module.algebraMap_end_apply]⟩
    | add x y _ _ hx hy =>
      obtain ⟨μ₁, h₁⟩ := hx; obtain ⟨μ₂, h₂⟩ := hy
      exact ⟨μ₁ + μ₂, fun v hv => by rw [LinearMap.add_apply, h₁ v hv, h₂ v hv, add_smul]⟩
    | mul x y _ _ hx hy =>
      obtain ⟨μ₁, h₁⟩ := hx; obtain ⟨μ₂, h₂⟩ := hy
      exact ⟨μ₁ * μ₂, fun v hv => by
        rw [Module.End.mul_apply, h₂ v hv, map_smul, h₁ v hv, smul_smul, mul_comm]⟩
  let c' : Module.End ℂ M → ℂ := fun s => if h : s ∈ Algebra.adjoin ℂ S then Classical.choose (scal s h) else 0
  haveI := hE c'
  refine Submodule.finiteDimensional_of_le
    (S₂ := ⨅ s ∈ S, LinearMap.ker (s - algebraMap ℂ (Module.End ℂ M) (c' s))) ?_
  intro v hv
  replace hv := hv.2
  simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, Module.algebraMap_end_apply, sub_eq_zero]
  intro s hs
  have hsA : s ∈ Algebra.adjoin ℂ S := Algebra.subset_adjoin hs
  simp only [c', dif_pos hsA]
  exact Classical.choose_spec (scal s hsA) v hv

end GlobalTheory.AutGrowth
