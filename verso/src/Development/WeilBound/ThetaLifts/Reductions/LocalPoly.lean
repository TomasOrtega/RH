import Development.WeilBound.ThetaLifts.CartanFactorisation.ExistsGreatestProperInvariantSubmoduleOfSide

noncomputable section

open ReciprocityTheory.ThetaSummability.Real ReciprocityTheory.ChartRestriction.G.ThK.Real FockH1Action MvPolynomial Matrix
open scoped InnerProductSpace

namespace PositivityTheory.ThKR.Join

open PositivityTheory.KReal PositivityTheory.ThKF.Unit

/- English proof (translation)
Establish `hp : ∀ (n : ℕ) y, j ((T ^ n) y) = (C ^ n) (j y)` using `fun n => by`. Proceed by induction on `n with`. Consider the case `zero => intro y`. Simplify using the standard rewrite rules. Consider the case `succ n ih => intro y`.

Rewrite using `[pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, h]`. Proceed by induction on `g using Polynomial.induction_on' with`. Consider the case `add p q hp hq => simp [hp, hq]`. Consider the case `monomial n a => simp [Polynomial.aeval_monomial, hp]`.
-/
theorem aeval_inter {V M : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup M] [Module ℂ M] (j : V →ₗ[ℂ] M)
    (T : Module.End ℂ V) (C : Module.End ℂ M) (h : ∀ y, j (T y) = C (j y)) (g : Polynomial ℂ) (y : V) :
    j (Polynomial.aeval T g y) = Polynomial.aeval C g (j y) := by
  have hp : ∀ (n : ℕ) y, j ((T ^ n) y) = (C ^ n) (j y) := fun n => by
    induction n with
    | zero => intro y; simp
    | succ n ih => intro y; rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, h]
  induction g using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial n a => simp [Polynomial.aeval_monomial, hp]

/- English proof (translation)
Establish `h0 : (C.restrict hU).charpoly.eval 0 ≠ 0` using `fun e => by`. Take `⟨m, h1, h2⟩` from `(LinearMap.charpoly_constantCoeff_eq_zero_iff (C.restrict hU)).1 (by rw [Polynomial.constantCoeff_apply, Polynomial.coeff_zero_eq_eval_zero, e])`. Conclude with `h1 (hi (h2.trans (map_zero _).symm))`. Use `⟨Polynomial.C ((C.restrict hU).charpoly.eval 0)⁻¹ * (C.restrict hU).charpoly, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Polynomial.eval_mul, Polynomial.eval_C, inv_mul_cancel₀ h0]`.

Use `aeval_inter U.subtype (C.restrict hU) C (fun _ => rfl) (C.restrict hU).charpoly ⟨x, hx⟩` as an intermediate fact. Rewrite `this` using `[LinearMap.aeval_self_charpoly]`. Rewrite using `[map_mul, Module.End.mul_apply, show Polynomial.aeval C (C.restrict hU).charpoly x = 0 from this.symm, map_zero]`.
-/
theorem poly_kill {M : Type} [AddCommGroup M] [Module ℂ M] (C : Module.End ℂ M) (U : Submodule ℂ M) [FiniteDimensional ℂ U]
    (hU : ∀ y ∈ U, C y ∈ U) (hi : Function.Injective (C.restrict hU)) {x : M} (hx : x ∈ U) :
    ∃ g : Polynomial ℂ, g.eval 0 = 1 ∧ Polynomial.aeval C g x = 0 := by
  have h0 : (C.restrict hU).charpoly.eval 0 ≠ 0 := fun e => by
    obtain ⟨m, h1, h2⟩ := (LinearMap.charpoly_constantCoeff_eq_zero_iff (C.restrict hU)).1
      (by rw [Polynomial.constantCoeff_apply, Polynomial.coeff_zero_eq_eval_zero, e])
    exact h1 (hi (h2.trans (map_zero _).symm))
  refine ⟨Polynomial.C ((C.restrict hU).charpoly.eval 0)⁻¹ * (C.restrict hU).charpoly, ?_, ?_⟩
  · rw [Polynomial.eval_mul, Polynomial.eval_C, inv_mul_cancel₀ h0]
  · have := aeval_inter U.subtype (C.restrict hU) C (fun _ => rfl) (C.restrict hU).charpoly ⟨x, hx⟩
    rw [LinearMap.aeval_self_charpoly] at this
    rw [map_mul, Module.End.mul_apply, show Polynomial.aeval C (C.restrict hU).charpoly x = 0 from this.symm, map_zero]

section Gen

variable {r s : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]

/- English proof (translation)
Set `V : Submodule ℂ A` to `cycK ρ f`. Set `ρV : Ix r s → Ix r s → Module.End ℂ V` to `fun a b => if h : sameBlock a b then (ρ a b).restrict (kSt_cycK ρ f a b h) else 0`. Establish `hρV : ∀ a b, sameBlock a b → ∀ v : V, ((ρV a b v : V) : A) = ρ a b v`. Introduce `a b h v`. Simplify using `only [ρV, dif_pos h]`.

Both sides reduce to the same expression. Set `ιV : V →ₗ[ℂ] M` to `ι ∘ₗ V.subtype`. Establish `hιV : ∀ a b, sameBlock a b → ∀ v, ιV (ρV a b v) = act (Eab a b) (ιV v)`. Introduce `a b h v`. Express the relevant statement in the definitionally equal form `ι ((ρV a b v : V) : A) = act (Eab a b) (ι (v : A))`.

Rewrite using `[hρV a b h, hι a b h]`. Establish `hadjV : AdjK ρV`. Introduce `a b h u v`. Rewrite using `[Submodule.coe_inner, Submodule.coe_inner, hρV a b h, hρV b a (sameBlock_symm' h)]`. Conclude with `hadj a b h _ _`.

Use `set c0 : ℝ := ((casW La : ℚ) : ℝ) with hc0`. Establish `hcc : (c0 : ℂ) = ((casW La : ℚ) : ℂ)` using `by simp [hc0]`. Establish `hcV : casK ρV = (c0 : ℂ) • (1 : Module.End ℂ V)`. Use `LinearMap.ext fun v => Subtype.ext ?_` and prove the remaining obligations. Establish `h1` using `casK_intertw (ρ := ρV) (ρ' := ρ) V.subtype (fun a b h v => hρV a b h v) v`.

Express the relevant statement in the definitionally equal form `((casK ρV v : V) : A) = (c0 : ℂ) • (v : A)`. Rewrite using `[hcc, ← cas_cyc hgl hw v v.2]`. Conclude with `h1`. Establish `hsV : StarK act (LinearMap.range ιV) c0`. Introduce `t ht x hx`.

Use `hs t ht x (Submodule.span_mono ?_ hx)` and prove the remaining obligations. Introduce and unpack `y ⟨a, b, hab, v, ⟨w, rfl⟩, rfl⟩`. Conclude with `⟨a, b, hab, _, ⟨(w : A), rfl⟩, rfl⟩`. Take `⟨hinj, hfin⟩` from `cas_bound_gl act hL ρV hadjV c0 hcV ιV hιV hsV`. Establish `hfV : f ∈ V` using `self_mem_cycK ρ f`.

Establish `hG : genG act (LinearMap.range ιV) = genG act (Submodule.span ℂ {ι f})`. Apply `le_antisymm` to reduce the goal to its premises. Use `genG_le' ?_ (genG_stable' _ _)` and prove the remaining obligations. Introduce and unpack `_ ⟨v, rfl⟩`. Establish `: V ≤ (genG act (Submodule.span ℂ {ι f})).comap ι`.

Use `sInf_le ⟨le_genG' _ _ (Submodule.mem_span_singleton_self _), fun a b h x hx => ?_⟩` and prove the remaining obligations. Rewrite using `[Submodule.mem_comap, hι a b h]`. Conclude with `genG_stable' _ _ _ _ hx`. Conclude with `this v.2`. Use `genG_le' ?_ (genG_stable' _ _)` and prove the remaining obligations.

Rewrite using `[Submodule.span_singleton_le_iff_mem]`. Conclude with `le_genG' _ _ ⟨⟨f, hfV⟩, rfl⟩`. Rewrite `hinj`, `hfin` using `[hG]`. Use `set G := genG act (Submodule.span ℂ {ι f}) with hGdef`. Set `C : Module.End ℂ M` to `casK (units act) - (c0 : ℂ) • 1`.

Establish `hC : ∀ x, C x = casK (units act) x - (c0 : ℂ) • x` using `fun x => rfl`. Establish `hC0 : ∀ x ∈ LinearMap.range ιV, C x = 0`. Introduce and unpack `_ ⟨v, rfl⟩`. Rewrite using `[hC, ← casK_intertw (ρ := ρV) (ρ' := units act) ιV hιV v, hcV]`. Simplify using the standard rewrite rules.

Use `⟨?_, fun N hNG hNs hne => ?_⟩` and prove the remaining obligations. Use `hC0 (ι f) ⟨⟨f, hfV⟩, rfl⟩` as an intermediate fact. Rewrite `this` using `[hC, sub_eq_zero, hcc]`. Conclude with `this`. Establish `hdis : ∀ x ∈ N, x ∈ LinearMap.range ιV → x = 0`.

Establish `hK : KSt ρ (V ⊓ N.comap ι)`. Introduce `a b h x hx`. Use `⟨kSt_cycK ρ f a b h x hx.1, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `ι (ρ a b x) ∈ N`. Rewrite using `[hι a b h]`.

Conclude with `hNs _ _ hx.2`. Break down `cyc_irred hadj hgl hw (V ⊓ N.comap ι) inf_le_left hK with h | h` into its components or cases. Introduce and unpack `_ hx ⟨v, rfl⟩`. Establish `: (v : A) ∈ V ⊓ N.comap ι` using `⟨v.2, hx⟩`. Rewrite `this` using `[h, Submodule.mem_bot]`.

Express the relevant statement in the definitionally equal form `ι (v : A) = 0`. Rewrite using `[this, map_zero]`. It suffices to derive a contradiction. Apply `hne` to reduce the goal to its premises. Use `le_antisymm hNG (genG_le' ?_ hNs)` and prove the remaining obligations.

Rewrite using `[Submodule.span_singleton_le_iff_mem]`. Establish `: f ∈ V ⊓ N.comap ι` using `h ▸ hfV`. Conclude with `this.2`. Introduce `x hx`. Take `⟨F, hF, hxF, hFK⟩` from `hfin x (hNG hx)`.

Establish `hKN : KSt (units act) (N ⊓ F)` using `fun a b h y hy => ⟨hNs _ _ hy.1, hFK a b h y hy.2⟩`. Establish `hCN : ∀ y ∈ N ⊓ F, C y ∈ N ⊓ F` using `fun y hy => (N ⊓ F).sub_mem (casK_mem hKN hy) ((N ⊓ F).smul_mem _ hy)`. Establish `: FiniteDimensional ℂ ↥(N ⊓ F)` using `Submodule.finiteDimensional_of_le inf_le_right`. Establish `hi : Function.Injective (C.restrict hCN)`. Rewrite using `[← LinearMap.ker_eq_bot, eq_bot_iff]`.

Introduce `y hy`. Establish `h1 : C (y : M) = 0` using `congrArg Subtype.val (LinearMap.mem_ker.1 hy)`. Establish `h2` using `hinj y (hNG y.2.1) (by rw [← hC, h1]; exact Submodule.zero_mem _)`. Conclude with `Subtype.ext (hdis y y.2.1 h2)`. Take `⟨g, g1, g2⟩` from `poly_kill C (N ⊓ F) hCN hi ⟨hx, hxF⟩`.

Use `⟨g.comp (Polynomial.X - Polynomial.C (c0 : ℂ)), by rw [← hcc]; simpa using g1, ?_⟩` and prove the remaining obligations. Rewrite using `[Polynomial.aeval_comp, map_sub, Polynomial.aeval_X, Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one]`. Conclude with `g2`.
-/
theorem local_poly (act : Mat r s →ₗ[ℂ] Module.End ℂ M) (hL : IsLie act) (La : Ix r s → ℚ)
    {A : Type} [NormedAddCommGroup A] [InnerProductSpace ℂ A] [FiniteDimensional ℂ A]
    (ρ : Ix r s → Ix r s → Module.End ℂ A) (ι : A →ₗ[ℂ] M) (f : A)
    (hadj : AdjK ρ) (hgl : GlK ρ) (hw : HwK ρ La f)
    (hι : ∀ a b, sameBlock a b → ∀ u, ι (ρ a b u) = act (Eab a b) (ι u))
    (hs : StarK act (LinearMap.range ι) ((casW La : ℚ) : ℝ)) :
    casK (units act) (ι f) = ((casW La : ℚ) : ℂ) • ι f ∧ ∀ N : Submodule ℂ M, N ≤ genG act (Submodule.span ℂ {ι f}) →
      (∀ W, ∀ x ∈ N, act W x ∈ N) → N ≠ genG act (Submodule.span ℂ {ι f}) →
      ∀ x ∈ N, ∃ g : Polynomial ℂ, g.eval ((casW La : ℚ) : ℂ) = 1 ∧ Polynomial.aeval (casK (units act)) g x = 0 := by
  classical
  let V : Submodule ℂ A := cycK ρ f
  let ρV : Ix r s → Ix r s → Module.End ℂ V := fun a b =>
    if h : sameBlock a b then (ρ a b).restrict (kSt_cycK ρ f a b h) else 0
  have hρV : ∀ a b, sameBlock a b → ∀ v : V, ((ρV a b v : V) : A) = ρ a b v := by
    intro a b h v
    simp only [ρV, dif_pos h]
    rfl
  let ιV : V →ₗ[ℂ] M := ι ∘ₗ V.subtype
  have hιV : ∀ a b, sameBlock a b → ∀ v, ιV (ρV a b v) = act (Eab a b) (ιV v) := by
    intro a b h v
    change ι ((ρV a b v : V) : A) = act (Eab a b) (ι (v : A))
    rw [hρV a b h, hι a b h]
  have hadjV : AdjK ρV := by
    intro a b h u v
    rw [Submodule.coe_inner, Submodule.coe_inner, hρV a b h, hρV b a (sameBlock_symm' h)]
    exact hadj a b h _ _
  set c0 : ℝ := ((casW La : ℚ) : ℝ) with hc0
  have hcc : (c0 : ℂ) = ((casW La : ℚ) : ℂ) := by simp [hc0]
  have hcV : casK ρV = (c0 : ℂ) • (1 : Module.End ℂ V) := by
    refine LinearMap.ext fun v => Subtype.ext ?_
    have h1 := casK_intertw (ρ := ρV) (ρ' := ρ) V.subtype (fun a b h v => hρV a b h v) v
    change ((casK ρV v : V) : A) = (c0 : ℂ) • (v : A)
    rw [hcc, ← cas_cyc hgl hw v v.2]
    exact h1
  have hsV : StarK act (LinearMap.range ιV) c0 := by
    intro t ht x hx
    refine hs t ht x (Submodule.span_mono ?_ hx)
    rintro y ⟨a, b, hab, v, ⟨w, rfl⟩, rfl⟩
    exact ⟨a, b, hab, _, ⟨(w : A), rfl⟩, rfl⟩
  obtain ⟨hinj, hfin⟩ := cas_bound_gl act hL ρV hadjV c0 hcV ιV hιV hsV
  have hfV : f ∈ V := self_mem_cycK ρ f
  have hG : genG act (LinearMap.range ιV) = genG act (Submodule.span ℂ {ι f}) := by
    apply le_antisymm
    · refine genG_le' ?_ (genG_stable' _ _)
      rintro _ ⟨v, rfl⟩
      have : V ≤ (genG act (Submodule.span ℂ {ι f})).comap ι := by
        refine sInf_le ⟨le_genG' _ _ (Submodule.mem_span_singleton_self _), fun a b h x hx => ?_⟩
        rw [Submodule.mem_comap, hι a b h]
        exact genG_stable' _ _ _ _ hx
      exact this v.2
    · refine genG_le' ?_ (genG_stable' _ _)
      rw [Submodule.span_singleton_le_iff_mem]
      exact le_genG' _ _ ⟨⟨f, hfV⟩, rfl⟩
  rw [hG] at hinj hfin
  set G := genG act (Submodule.span ℂ {ι f}) with hGdef
  let C : Module.End ℂ M := casK (units act) - (c0 : ℂ) • 1
  have hC : ∀ x, C x = casK (units act) x - (c0 : ℂ) • x := fun x => rfl
  have hC0 : ∀ x ∈ LinearMap.range ιV, C x = 0 := by
    rintro _ ⟨v, rfl⟩
    rw [hC, ← casK_intertw (ρ := ρV) (ρ' := units act) ιV hιV v, hcV]
    simp
  refine ⟨?_, fun N hNG hNs hne => ?_⟩
  · have := hC0 (ι f) ⟨⟨f, hfV⟩, rfl⟩
    rw [hC, sub_eq_zero, hcc] at this
    exact this
  · have hdis : ∀ x ∈ N, x ∈ LinearMap.range ιV → x = 0 := by
      have hK : KSt ρ (V ⊓ N.comap ι) := by
        intro a b h x hx
        refine ⟨kSt_cycK ρ f a b h x hx.1, ?_⟩
        change ι (ρ a b x) ∈ N
        rw [hι a b h]
        exact hNs _ _ hx.2
      rcases cyc_irred hadj hgl hw (V ⊓ N.comap ι) inf_le_left hK with h | h
      · rintro _ hx ⟨v, rfl⟩
        have : (v : A) ∈ V ⊓ N.comap ι := ⟨v.2, hx⟩
        rw [h, Submodule.mem_bot] at this
        change ι (v : A) = 0
        rw [this, map_zero]
      · exfalso
        apply hne
        refine le_antisymm hNG (genG_le' ?_ hNs)
        rw [Submodule.span_singleton_le_iff_mem]
        have : f ∈ V ⊓ N.comap ι := h ▸ hfV
        exact this.2
    intro x hx
    obtain ⟨F, hF, hxF, hFK⟩ := hfin x (hNG hx)
    have hKN : KSt (units act) (N ⊓ F) := fun a b h y hy => ⟨hNs _ _ hy.1, hFK a b h y hy.2⟩
    have hCN : ∀ y ∈ N ⊓ F, C y ∈ N ⊓ F := fun y hy =>
      (N ⊓ F).sub_mem (casK_mem hKN hy) ((N ⊓ F).smul_mem _ hy)
    have : FiniteDimensional ℂ ↥(N ⊓ F) := Submodule.finiteDimensional_of_le inf_le_right
    have hi : Function.Injective (C.restrict hCN) := by
      rw [← LinearMap.ker_eq_bot, eq_bot_iff]
      intro y hy
      have h1 : C (y : M) = 0 := congrArg Subtype.val (LinearMap.mem_ker.1 hy)
      have h2 := hinj y (hNG y.2.1) (by rw [← hC, h1]; exact Submodule.zero_mem _)
      exact Subtype.ext (hdis y y.2.1 h2)
    obtain ⟨g, g1, g2⟩ := poly_kill C (N ⊓ F) hCN hi ⟨hx, hxF⟩
    refine ⟨g.comp (Polynomial.X - Polynomial.C (c0 : ℂ)), by rw [← hcc]; simpa using g1, ?_⟩
    rw [Polynomial.aeval_comp, map_sub, Polynomial.aeval_X, Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one]
    exact g2

/- English proof (translation)
Use `sum_mem fun a _ => sum_mem fun b _ => ?_` and prove the remaining obligations. Use `split_ifs`. Conclude with `mul_mem (Algebra.subset_adjoin ⟨_, rfl⟩) (Algebra.subset_adjoin ⟨_, rfl⟩)`. Conclude with `zero_mem _`.
-/
theorem cas_mem (act : Mat r s →ₗ[ℂ] Module.End ℂ M) : casK (units act) ∈ Algebra.adjoin ℂ (Set.range act) := by
  refine sum_mem fun a _ => sum_mem fun b _ => ?_
  split_ifs
  · exact mul_mem (Algebra.subset_adjoin ⟨_, rfl⟩) (Algebra.subset_adjoin ⟨_, rfl⟩)
  · exact zero_mem _

/- English proof (translation)
Take `⟨hL, hn, A, _, _, _, ρ, ι, f, hadj, hgl, hw, hι, hgen, hs⟩` from `h`. Take `⟨hv, hC⟩` from `local_poly act hL La ρ ι f hadj hgl hw hι hs`. Rewrite `hC` using `[hgen]`. Use `⟨ι f, fun K h1 h2 t ht y => ?_⟩` and prove the remaining obligations. Establish `a1 : ∃ g : Polynomial ℂ, g.eval ((casW La : ℚ) : ℂ) = 1 ∧ ∀ x ∈ t, Polynomial.aeval (casK (units act)) g x = 0`.

Proceed by induction on `t with`. Consider the case `nil => exact ⟨1, by simp, by simp⟩`. Consider the case `cons z t ih`. Take `⟨g, g1, g2⟩` from `ih fun x hx => ht x (List.mem_cons_of_mem _ hx)`. Take `⟨g', g1', g2'⟩` from `hC K le_top h2 h1 z (ht z List.mem_cons_self)`.

Use `⟨g * g', by rw [Polynomial.eval_mul, g1, g1', one_mul], fun x hx => ?_⟩` and prove the remaining obligations. Break down `List.mem_cons.1 hx with rfl | hx` into its components or cases. Rewrite using `[map_mul, Module.End.mul_apply, g2', map_zero]`. Rewrite using `[mul_comm, map_mul, Module.End.mul_apply, g2 x hx, map_zero]`. Take `⟨g, g1, g2⟩` from `a1`.

Establish `a2 : genG act (Submodule.span ℂ {ι f}) ≤ (Subalgebra.toSubmodule (Algebra.adjoin ℂ (Set.range act))).map (LinearMap.applyₗ (ι f))`. Use `genG_le' ((Submodule.span_singleton_le_iff_mem _ _).2 ⟨1, one_mem (Algebra.adjoin ℂ (Set.range act)), rfl⟩) ?_` and prove the remaining obligations. Introduce and unpack `W _ ⟨u, hu, rfl⟩`. Conclude with `⟨act W * u, mul_mem (s := Algebra.adjoin ℂ (Set.range act)) (Algebra.subset_adjoin ⟨W, rfl⟩) hu, rfl⟩`. Take `⟨u, hu, e⟩` from `a2 (hgen ▸ Submodule.mem_top : y ∈ _)`.

Use `⟨u * Polynomial.aeval (casK (units act)) g, mul_mem hu ?_, ?_, fun x hx => ?_⟩` and prove the remaining obligations. Conclude with `Algebra.adjoin_le (S := Algebra.adjoin ℂ (Set.range act)) (Set.singleton_subset_iff.2 (cas_mem act)) (Polynomial.aeval_mem_adjoin_singleton ℂ _)`. Rewrite using `[Module.End.mul_apply, Module.End.aeval_apply_of_mem_apply_eq_smul hv, g1, one_smul]`. Conclude with `e`. Rewrite using `[Module.End.mul_apply, g2 x hx, map_zero]`.
-/
theorem side_nil {La : Ix r s → ℚ} {act : Mat r s →ₗ[ℂ] Module.End ℂ M} (h : Side La M act) :
    ∃ v : M, ∀ K : Submodule ℂ M, K ≠ ⊤ → (∀ W, ∀ x ∈ K, act W x ∈ K) → ∀ t : List M, (∀ x ∈ t, x ∈ K) → ∀ y,
      ∃ u ∈ Algebra.adjoin ℂ (Set.range act), u v = y ∧ ∀ x ∈ t, u x = 0 := by
  obtain ⟨hL, hn, A, _, _, _, ρ, ι, f, hadj, hgl, hw, hι, hgen, hs⟩ := h
  obtain ⟨hv, hC⟩ := local_poly act hL La ρ ι f hadj hgl hw hι hs
  rw [hgen] at hC
  refine ⟨ι f, fun K h1 h2 t ht y => ?_⟩
  have a1 : ∃ g : Polynomial ℂ, g.eval ((casW La : ℚ) : ℂ) = 1 ∧ ∀ x ∈ t, Polynomial.aeval (casK (units act)) g x = 0 := by
    induction t with
    | nil => exact ⟨1, by simp, by simp⟩
    | cons z t ih =>
      obtain ⟨g, g1, g2⟩ := ih fun x hx => ht x (List.mem_cons_of_mem _ hx)
      obtain ⟨g', g1', g2'⟩ := hC K le_top h2 h1 z (ht z List.mem_cons_self)
      refine ⟨g * g', by rw [Polynomial.eval_mul, g1, g1', one_mul], fun x hx => ?_⟩
      rcases List.mem_cons.1 hx with rfl | hx
      · rw [map_mul, Module.End.mul_apply, g2', map_zero]
      · rw [mul_comm, map_mul, Module.End.mul_apply, g2 x hx, map_zero]
  obtain ⟨g, g1, g2⟩ := a1
  have a2 : genG act (Submodule.span ℂ {ι f}) ≤
      (Subalgebra.toSubmodule (Algebra.adjoin ℂ (Set.range act))).map (LinearMap.applyₗ (ι f)) := by
    refine genG_le' ((Submodule.span_singleton_le_iff_mem _ _).2 ⟨1, one_mem (Algebra.adjoin ℂ (Set.range act)), rfl⟩) ?_
    rintro W _ ⟨u, hu, rfl⟩
    exact ⟨act W * u, mul_mem (s := Algebra.adjoin ℂ (Set.range act)) (Algebra.subset_adjoin ⟨W, rfl⟩) hu, rfl⟩
  obtain ⟨u, hu, e⟩ := a2 (hgen ▸ Submodule.mem_top : y ∈ _)
  refine ⟨u * Polynomial.aeval (casK (units act)) g, mul_mem hu ?_, ?_, fun x hx => ?_⟩
  · exact Algebra.adjoin_le (S := Algebra.adjoin ℂ (Set.range act)) (Set.singleton_subset_iff.2 (cas_mem act))
      (Polynomial.aeval_mem_adjoin_singleton ℂ _)
  · rw [Module.End.mul_apply, Module.End.aeval_apply_of_mem_apply_eq_smul hv, g1, one_smul]
    exact e
  · rw [Module.End.mul_apply, g2 x hx, map_zero]

end Gen

def Two (p q r s : ℕ) (c : ℂ) : Prop :=
  ∃ K : Submodule ℂ (Pol p q r s), K ≠ ⊤ ∧ (∀ W, ∀ x ∈ K, fockAct2 p q r s W x ∈ K) ∧
    (∀ N, K ≤ N → (∀ W, ∀ x ∈ N, fockAct2 p q r s W x ∈ N) → N = K ∨ N = ⊤) ∧
    ∃ v : Pol p q r s, ∀ t : List (Pol p q r s), (∀ x ∈ t, x ∈ K) → ∀ y,
      ∃ u ∈ Algebra.adjoin ℂ (Set.range (fockAct2 p q r s)), u v - y ∈ coinvSub (act1 p q r s) (chiTr c) ∧
        ∀ x ∈ t, u x ∈ coinvSub (act1 p q r s) (chiTr c)

/- English proof (translation)
Take `⟨K, h1, h2, h3, -⟩` from `exists_greatest_proper_invariant_submodule_of_side h`. Take `⟨v, hv⟩` from `side_nil h`. Establish `sj : Function.Surjective (thMkC p q r s c)` using `Submodule.mkQ_surjective _`. Establish `ak : ∀ W x, thMkC p q r s c (fockAct2 p q r s W x) = thAct p q r s c τ W (thMkC p q r s c x) - ((τ : ℂ) * W.trace) • thMkC p q r s c x` using `fun W x => by`. Rewrite using `[thAct_mk, twAct_apply, map_add, map_smul, add_sub_cancel_right]`.

Take `⟨v, rfl⟩` from `sj v`. Use `⟨K.comap (thMkC p q r s c), fun e => h1 (eq_top_iff.2 fun y _ => ?_), fun W x hx => ?_, fun N hN hs => ?_, v, fun t ht y => ?_⟩` and prove the remaining obligations. Take `⟨x, rfl⟩` from `sj y`. Conclude with `(e ▸ Submodule.mem_top : x ∈ K.comap (thMkC p q r s c))`. Use `show thMkC p q r s c _ ∈ K`.

Rewrite using `[ak]`. Conclude with `K.sub_mem (h2 W _ hx) (K.smul_mem _ hx)`. Distinguish the cases in `e : N.map (thMkC p q r s c) = ⊤`. Use `Or.inr (eq_top_iff.2 fun x _ => ?_)` and prove the remaining obligations. Take `⟨y, hy, e'⟩ : thMkC p q r s c x ∈ N.map (thMkC p q r s c)` from `e ▸ Submodule.mem_top`.

Establish `: x - y ∈ N` using `hN (show thMkC p q r s c (x - y) ∈ K by rw [map_sub, e', sub_self]; exact K.zero_mem)`. Simplify using `using N.add_mem this hy`. Use `Or.inl (le_antisymm (Submodule.map_le_iff_le_comap.1 (h3 _ ?_ e)) hN)` and prove the remaining obligations. Introduce and unpack `W _ ⟨y, hy, rfl⟩`. Conclude with `⟨_, by rw [twAct_apply]; exact N.add_mem (hs W y hy) (N.smul_mem _ hy), (thAct_mk ..).symm⟩`.

Establish `lift : ∀ u ∈ Algebra.adjoin ℂ (Set.range (thAct p q r s c τ)), ∃ u' ∈ Algebra.adjoin ℂ (Set.range (fockAct2 p q r s)), ∀ x, thMkC p q r s c (u' x) = u (thMkC p q r s c x)`. Introduce `u hu`. Proceed by induction on `hu using Algebra.adjoin_induction with`. Consider the case `mem u hu`. Take `⟨W, rfl⟩` from `hu`.

Use `⟨fockAct2 p q r s W + ((τ : ℂ) * W.trace) • 1, add_mem (Algebra.subset_adjoin ⟨W, rfl⟩) (Subalgebra.smul_mem _ (one_mem _) _), fun x => ?_⟩` and prove the remaining obligations. Rewrite using `[thAct_mk, twAct_apply]`. Both sides reduce to the same expression. Consider the case `algebraMap a => exact ⟨algebraMap ℂ _ a, Subalgebra.algebraMap_mem _ a, fun x => by simp⟩`. Consider the case `add a b _ _ ha hb`.

Take `⟨a', a1, a2⟩` from `ha`. Take `⟨b', b1, b2⟩` from `hb`. Conclude with `⟨a' + b', add_mem a1 b1, fun x => by simp [a2, b2]⟩`. Consider the case `mul a b _ _ ha hb`. Take `⟨a', a1, a2⟩` from `ha`.

Take `⟨b', b1, b2⟩` from `hb`. Conclude with `⟨a' * b', mul_mem a1 b1, fun x => by simp [a2, b2]⟩`. Take `⟨u, hu, e1, e2⟩` from `hv K h1 h2 (t.map (thMkC p q r s c)) (by`. Introduce `x hx`. Take `⟨z, hz, rfl⟩` from `List.mem_map.1 hx`.

Conclude with `ht z hz) (thMkC p q r s c y)`. Take `⟨u', hu', e⟩` from `lift u hu`. Use `⟨u', hu', (Submodule.Quotient.mk_eq_zero _).1 ?_, fun x hx => (Submodule.Quotient.mk_eq_zero _).1 ?_⟩` and prove the remaining obligations. Use `show thMkC p q r s c _ = 0`. Rewrite using `[map_sub, e, e1, sub_self]`.

Use `show thMkC p q r s c _ = 0`. Rewrite using `[e, e2 _ (List.mem_map_of_mem hx)]`.
-/
theorem two_of {p q r s : ℕ} {c : ℂ} (τ : ℚ) {La : Ix r s → ℚ} (h : Side La (ThC p q r s c) (thAct p q r s c τ)) :
    Two p q r s c := by
  obtain ⟨K, h1, h2, h3, -⟩ := exists_greatest_proper_invariant_submodule_of_side h
  obtain ⟨v, hv⟩ := side_nil h
  have sj : Function.Surjective (thMkC p q r s c) := Submodule.mkQ_surjective _
  have ak : ∀ W x, thMkC p q r s c (fockAct2 p q r s W x) =
      thAct p q r s c τ W (thMkC p q r s c x) - ((τ : ℂ) * W.trace) • thMkC p q r s c x := fun W x => by
    rw [thAct_mk, twAct_apply, map_add, map_smul, add_sub_cancel_right]
  obtain ⟨v, rfl⟩ := sj v
  refine ⟨K.comap (thMkC p q r s c), fun e => h1 (eq_top_iff.2 fun y _ => ?_), fun W x hx => ?_, fun N hN hs => ?_,
    v, fun t ht y => ?_⟩
  · obtain ⟨x, rfl⟩ := sj y
    exact (e ▸ Submodule.mem_top : x ∈ K.comap (thMkC p q r s c))
  · show thMkC p q r s c _ ∈ K
    rw [ak]
    exact K.sub_mem (h2 W _ hx) (K.smul_mem _ hx)
  · by_cases e : N.map (thMkC p q r s c) = ⊤
    · refine Or.inr (eq_top_iff.2 fun x _ => ?_)
      obtain ⟨y, hy, e'⟩ : thMkC p q r s c x ∈ N.map (thMkC p q r s c) := e ▸ Submodule.mem_top
      have : x - y ∈ N := hN (show thMkC p q r s c (x - y) ∈ K by rw [map_sub, e', sub_self]; exact K.zero_mem)
      simpa using N.add_mem this hy
    · refine Or.inl (le_antisymm (Submodule.map_le_iff_le_comap.1 (h3 _ ?_ e)) hN)
      rintro W _ ⟨y, hy, rfl⟩
      exact ⟨_, by rw [twAct_apply]; exact N.add_mem (hs W y hy) (N.smul_mem _ hy), (thAct_mk ..).symm⟩
  · have lift : ∀ u ∈ Algebra.adjoin ℂ (Set.range (thAct p q r s c τ)),
        ∃ u' ∈ Algebra.adjoin ℂ (Set.range (fockAct2 p q r s)), ∀ x, thMkC p q r s c (u' x) = u (thMkC p q r s c x) := by
      intro u hu
      induction hu using Algebra.adjoin_induction with
      | mem u hu =>
        obtain ⟨W, rfl⟩ := hu
        refine ⟨fockAct2 p q r s W + ((τ : ℂ) * W.trace) • 1,
          add_mem (Algebra.subset_adjoin ⟨W, rfl⟩) (Subalgebra.smul_mem _ (one_mem _) _), fun x => ?_⟩
        rw [thAct_mk, twAct_apply]; rfl
      | algebraMap a => exact ⟨algebraMap ℂ _ a, Subalgebra.algebraMap_mem _ a, fun x => by simp⟩
      | add a b _ _ ha hb =>
        obtain ⟨a', a1, a2⟩ := ha
        obtain ⟨b', b1, b2⟩ := hb
        exact ⟨a' + b', add_mem a1 b1, fun x => by simp [a2, b2]⟩
      | mul a b _ _ ha hb =>
        obtain ⟨a', a1, a2⟩ := ha
        obtain ⟨b', b1, b2⟩ := hb
        exact ⟨a' * b', mul_mem a1 b1, fun x => by simp [a2, b2]⟩
    obtain ⟨u, hu, e1, e2⟩ := hv K h1 h2 (t.map (thMkC p q r s c)) (by
      intro x hx
      obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hx
      exact ht z hz) (thMkC p q r s c y)
    obtain ⟨u', hu', e⟩ := lift u hu
    refine ⟨u', hu', (Submodule.Quotient.mk_eq_zero _).1 ?_, fun x hx => (Submodule.Quotient.mk_eq_zero _).1 ?_⟩
    · show thMkC p q r s c _ = 0
      rw [map_sub, e, e1, sub_self]
    · show thMkC p q r s c _ = 0
      rw [e, e2 _ (List.mem_map_of_mem hx)]

/- English proof (translation)
Take `⟨hn, hm, e1, e2, hP, hQ, hQ', hP'⟩` from `nm_facts h`. Establish `c1 : ((D.κ : ℂ) / 2) = (((D.κ : ℚ) / 2 : ℚ) : ℂ)` using `by push_cast; rfl`. Establish `c2 : (-((D.κ : ℂ) / 2)) = ((-((D.κ : ℚ) / 2) : ℚ) : ℂ)` using `by push_cast; rfl`. Establish `n1 : Nontrivial (ThV D)` using `nontrivial_of_pair _ _ c1 (c1 ▸ pair_pos hP hQ hn hm _ e1 e2)`. Establish `n2 : Nontrivial (ThV' D)` using `nontrivial_of_pair _ _ c2 (c2 ▸ pair_neg hQ' hP' hn hm _ (by linarith) (by linarith))`.

Conclude with `⟨two_of 0 (side_of ((D.κ : ℂ) / 2) _ _ 0 c1 rfl _ (combV h) n1), two_of _ (side_of (-((D.κ : ℂ) / 2)) _ _ _ c2 rfl _ (combV' h) n2)⟩`.
-/
theorem two_data (D : RealData) (h : D.Hyp) :
    Two D.P D.Q D.R D.S ((D.κ : ℂ) / 2) ∧ Two D.P' D.Q' D.R D.S (-((D.κ : ℂ) / 2)) := by
  obtain ⟨hn, hm, e1, e2, hP, hQ, hQ', hP'⟩ := nm_facts h
  have c1 : ((D.κ : ℂ) / 2) = (((D.κ : ℚ) / 2 : ℚ) : ℂ) := by push_cast; rfl
  have c2 : (-((D.κ : ℂ) / 2)) = ((-((D.κ : ℚ) / 2) : ℚ) : ℂ) := by push_cast; rfl
  have n1 : Nontrivial (ThV D) :=
    nontrivial_of_pair _ _ c1 (c1 ▸ pair_pos hP hQ hn hm _ e1 e2)
  have n2 : Nontrivial (ThV' D) :=
    nontrivial_of_pair _ _ c2 (c2 ▸ pair_neg hQ' hP' hn hm _ (by linarith) (by linarith))
  exact ⟨two_of 0 (side_of ((D.κ : ℂ) / 2) _ _ 0 c1 rfl _ (combV h) n1),
    two_of _ (side_of (-((D.κ : ℂ) / 2)) _ _ _ c2 rfl _ (combV' h) n2)⟩

end PositivityTheory.ThKR.Join

end
