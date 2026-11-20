import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MajorantOperators

namespace ReciprocityTheory.ChartRestriction.G.FD

namespace LatticeSpanMembership

open NumberField Complex Module
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r}

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Take `⟨f, hf0, hfW⟩` from `Submodule.exists_dual_map_eq_bot_of_lt_top (lt_top_iff_ne_top.mpr hne) inferInstance`. Choose the witnesses or unpack the hypotheses as in `⟨v, hv⟩ : ∃ v, f v ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push Not at h`.

Conclude with `hf0 (LinearMap.ext h)`. Set `g` to `LinearMap.toContinuousLinearMap f`. Use `set ρ : ℝ := 2 * (fdeg E : ℝ) ^ 2 * rdE E with hρ`. Establish `hρ0 : 0 ≤ ρ`. Establish `: 0 ≤ rdE E` using `Real.rpow_nonneg (abs_nonneg _) _`.

Check the signs of the components of the expression. Use `set t : ℝ := (‖g‖ * ρ + 1) / f v with ht`. Take `⟨α, hα⟩` from `(hD3 r X).1 (t • v)`. Establish `hfα : f (fun τ : X.Ψ => τ.1 (α : E)) = 0`. Establish `hmem : f (fun τ : X.Ψ => τ.1 (α : E)) ∈ Submodule.map f (Submodule.span ℝ (Set.range fun α : 𝓞 E => fun τ : X.Ψ => τ.1 (α : E)))` using `Submodule.mem_map_of_mem (Submodule.subset_span ⟨α, rfl⟩)`.

Rewrite `hmem` using `[hfW]`. Conclude with `hmem`. Establish `hnorm : ‖(fun τ : X.Ψ => τ.1 (α : E)) - t • v‖ ≤ ρ`. Use `(pi_norm_le_iff_of_nonneg hρ0).mpr fun τ => ?_` and prove the remaining obligations. Conclude with `hα τ`.

Establish `hle` using `g.le_opNorm ((fun τ : X.Ψ => τ.1 (α : E)) - t • v)`. Establish `hg : g ((fun τ : X.Ψ => τ.1 (α : E)) - t • v) = -(‖g‖ * ρ + 1)` using `by show f ((fun τ : X.Ψ => τ.1 (α : E)) - t • v) = _`. Rewrite using `[map_sub, map_smul, hfα, smul_eq_mul, ht, div_mul_cancel₀ _ hv, zero_sub]`. Rewrite `hle` using `[hg, norm_neg, Real.norm_eq_abs, abs_of_pos (by positivity)]`. Use polynomial arithmetic with `[norm_nonneg g, mul_le_mul_of_nonneg_left hnorm (norm_nonneg g)]`.
-/
theorem span_emb_int (hD3 : IntegerApproximationCount (E := E)) :
    Submodule.span ℝ (Set.range fun α : 𝓞 E => fun τ : X.Ψ => τ.1 (α : E)) = ⊤ := by
  by_contra hne
  obtain ⟨f, hf0, hfW⟩ :=
    Submodule.exists_dual_map_eq_bot_of_lt_top (lt_top_iff_ne_top.mpr hne) inferInstance
  obtain ⟨v, hv⟩ : ∃ v, f v ≠ 0 := by
    by_contra h
    push Not at h
    exact hf0 (LinearMap.ext h)
  let g := LinearMap.toContinuousLinearMap f
  set ρ : ℝ := 2 * (fdeg E : ℝ) ^ 2 * rdE E with hρ
  have hρ0 : 0 ≤ ρ := by
    have : 0 ≤ rdE E := Real.rpow_nonneg (abs_nonneg _) _
    positivity
  set t : ℝ := (‖g‖ * ρ + 1) / f v with ht
  obtain ⟨α, hα⟩ := (hD3 r X).1 (t • v)
  have hfα : f (fun τ : X.Ψ => τ.1 (α : E)) = 0 := by
    have hmem : f (fun τ : X.Ψ => τ.1 (α : E)) ∈ Submodule.map f (Submodule.span ℝ
        (Set.range fun α : 𝓞 E => fun τ : X.Ψ => τ.1 (α : E))) :=
      Submodule.mem_map_of_mem (Submodule.subset_span ⟨α, rfl⟩)
    rw [hfW] at hmem
    exact hmem
  have hnorm : ‖(fun τ : X.Ψ => τ.1 (α : E)) - t • v‖ ≤ ρ := by
    refine (pi_norm_le_iff_of_nonneg hρ0).mpr fun τ => ?_
    exact hα τ
  have hle := g.le_opNorm ((fun τ : X.Ψ => τ.1 (α : E)) - t • v)
  have hg : g ((fun τ : X.Ψ => τ.1 (α : E)) - t • v) = -(‖g‖ * ρ + 1) := by
    show f ((fun τ : X.Ψ => τ.1 (α : E)) - t • v) = _
    rw [map_sub, map_smul, hfα, smul_eq_mul, ht, div_mul_cancel₀ _ hv, zero_sub]
  rw [hg, norm_neg, Real.norm_eq_abs, abs_of_pos (by positivity)] at hle
  nlinarith [norm_nonneg g, mul_le_mul_of_nonneg_left hnorm (norm_nonneg g)]

/- English proof (translation)
Take `⟨y, hy0, hy⟩` from `exists_integral_multiples ℤ ℚ (L := E) {c}`. Establish `h` using `hy c (Finset.mem_singleton_self c)`. Rewrite `h` using `[zsmul_eq_mul]`. Use `⟨y.natAbs * y.natAbs, Nat.mul_pos (Int.natAbs_pos.mpr hy0) (Int.natAbs_pos.mpr hy0), ?_⟩` and prove the remaining obligations. Establish `e : ((y.natAbs * y.natAbs : ℕ) : E) = (y : E) * (y : E)`.

Rewrite using `[← Int.cast_natCast, Int.natAbs_mul_self, Int.cast_mul]`. Establish `hy' : IsIntegral ℤ (y : E)`. Simplify using `using (isIntegral_algebraMap : IsIntegral ℤ (algebraMap ℤ E y))`. Rewrite using `[e, mul_assoc]`. Conclude with `hy'.mul h`.
-/
theorem exists_nat_mul_int (c : E) : ∃ N : ℕ, 0 < N ∧ IsIntegral ℤ ((N : E) * c) := by
  obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ (L := E) {c}
  have h := hy c (Finset.mem_singleton_self c)
  rw [zsmul_eq_mul] at h
  refine ⟨y.natAbs * y.natAbs, Nat.mul_pos (Int.natAbs_pos.mpr hy0) (Int.natAbs_pos.mpr hy0), ?_⟩
  have e : ((y.natAbs * y.natAbs : ℕ) : E) = (y : E) * (y : E) := by
    rw [← Int.cast_natCast, Int.natAbs_mul_self, Int.cast_mul]
  have hy' : IsIntegral ℤ (y : E) := by
    simpa using (isIntegral_algebraMap : IsIntegral ℤ (algebraMap ℤ E y))
  rw [e, mul_assoc]
  exact hy'.mul h

/- English proof (translation)
Establish `hv : v ∈ Submodule.span E (X.Λ : Set (Fin r → E))` using `X.Λ_span ▸ Submodule.mem_top`. Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem v hv => exact ⟨1, one_pos, by simpa using hv⟩`. Consider the case `zero => exact ⟨1, one_pos, by simp⟩`. Consider the case `add v w _ _ ihv ihw`.

Take `⟨N1, h1, hv1⟩` from `ihv`. Take `⟨N2, h2, hw2⟩` from `ihw`. Use `⟨N1 * N2, Nat.mul_pos h1 h2, ?_⟩` and prove the remaining obligations. Establish `e : ((N1 * N2 : ℕ) : E) • (v + w) = N2 • ((N1 : E) • v) + N1 • ((N2 : E) • w)`. Rewrite using `[← Nat.cast_smul_eq_nsmul E N2, ← Nat.cast_smul_eq_nsmul E N1, smul_smul, smul_smul, smul_add, Nat.cast_mul, mul_comm (N2 : E)]`.

Rewrite using `[e]`. Conclude with `X.Λ.add_mem (X.Λ.toAddSubmonoid.nsmul_mem hv1 N2) (X.Λ.toAddSubmonoid.nsmul_mem hw2 N1)`. Consider the case `smul c v _ ihv`. Take `⟨N, hN, hv⟩` from `ihv`. Take `⟨M, hM, hc⟩` from `exists_nat_mul_int c`.

Use `⟨M * N, Nat.mul_pos hM hN, ?_⟩` and prove the remaining obligations. Take `⟨γ, hγ⟩ : ∃ γ : 𝓞 E, (γ : E) = (M : E) * c` from `⟨⟨_, hc⟩, rfl⟩`. Establish `h` using `X.Λ.smul_mem γ hv`. Rewrite `h` using `[← algebraMap_smul E γ ((N : E) • v)]`. Use `h using 1` and compare the differences between its conclusion and the goal.

Use `show ((M * N : ℕ) : E) • (c • v) = (γ : E) • ((N : E) • v)`. Rewrite using `[hγ, smul_smul, smul_smul]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_nat_smul_mem (v : Fin r → E) : ∃ N : ℕ, 0 < N ∧ (N : E) • v ∈ X.Λ := by
  have hv : v ∈ Submodule.span E (X.Λ : Set (Fin r → E)) := X.Λ_span ▸ Submodule.mem_top
  induction hv using Submodule.span_induction with
  | mem v hv => exact ⟨1, one_pos, by simpa using hv⟩
  | zero => exact ⟨1, one_pos, by simp⟩
  | add v w _ _ ihv ihw =>
    obtain ⟨N1, h1, hv1⟩ := ihv
    obtain ⟨N2, h2, hw2⟩ := ihw
    refine ⟨N1 * N2, Nat.mul_pos h1 h2, ?_⟩
    have e : ((N1 * N2 : ℕ) : E) • (v + w) = N2 • ((N1 : E) • v) + N1 • ((N2 : E) • w) := by
      rw [← Nat.cast_smul_eq_nsmul E N2, ← Nat.cast_smul_eq_nsmul E N1, smul_smul, smul_smul,
        smul_add, Nat.cast_mul, mul_comm (N2 : E)]
    rw [e]
    exact X.Λ.add_mem (X.Λ.toAddSubmonoid.nsmul_mem hv1 N2) (X.Λ.toAddSubmonoid.nsmul_mem hw2 N1)
  | smul c v _ ihv =>
    obtain ⟨N, hN, hv⟩ := ihv
    obtain ⟨M, hM, hc⟩ := exists_nat_mul_int c
    refine ⟨M * N, Nat.mul_pos hM hN, ?_⟩
    obtain ⟨γ, hγ⟩ : ∃ γ : 𝓞 E, (γ : E) = (M : E) * c := ⟨⟨_, hc⟩, rfl⟩
    have h := X.Λ.smul_mem γ hv
    rw [← algebraMap_smul E γ ((N : E) • v)] at h
    convert h using 1
    show ((M * N : ℕ) : E) • (c • v) = (γ : E) • ((N : E) • v)
    rw [hγ, smul_smul, smul_smul]
    congr 1
    push_cast
    ring

/- English proof (translation)
Unfold `Data.Λp`. Rewrite using `[AddSubgroup.mem_inf, AddMonoidHom.mem_ker]`. Both sides reduce to the same expression.
-/
theorem mem_Λp_iff {ξ μ : Fin r → E} : μ ∈ X.Λp ξ ↔ μ ∈ X.Λ ∧ herm X.Gm μ ξ = 0 := by
  unfold Data.Λp
  rw [AddSubgroup.mem_inf, AddMonoidHom.mem_ker]
  rfl

/- English proof (translation)
Take `⟨γ, hγ⟩ : ∃ γ : 𝓞 E, (γ : E) = α` from `⟨⟨_, hα⟩, rfl⟩`. Establish `h` using `X.Λ.smul_mem γ hv`. Rewrite `h` using `[← algebraMap_smul E γ v]`. Rewrite using `[← hγ]`. Conclude with `h`.
-/
theorem smul_int_mem {α : E} (hα : IsIntegral ℤ α) {v : Fin r → E} (hv : v ∈ X.Λ) : α • v ∈ X.Λ := by
  obtain ⟨γ, hγ⟩ : ∃ γ : 𝓞 E, (γ : E) = α := ⟨⟨_, hα⟩, rfl⟩
  have h := X.Λ.smul_mem γ hv
  rw [← algebraMap_smul E γ v] at h
  rw [← hγ]
  exact h

noncomputable def single (a : Fin r) : (X.Ψ → ℂ) →ₗ[ℝ] (X.Ψ → Fin r → ℂ) where
  toFun s τ := Pi.single a (s τ)
  map_add' s t := by
    funext τ
    simp [Pi.single_add]
  map_smul' c s := by
    funext τ b
    by_cases hb : b = a
    · subst hb
      simp
    · simp [Pi.single_eq_of_ne hb]

/- English proof (translation)
Establish `hsing : ∀ (a : Fin r) (s : X.Ψ → ℂ), single (X` using `X) a s ∈ Submodule.span ℝ (X.embV '' (X.Λ : Set (Fin r → E))) := by`. Introduce `a s`. Take `⟨N, hN, hNmem⟩` from `exists_nat_smul_mem (X := X) (Pi.single a 1)`. Establish `hgen : Submodule.span ℝ (Set.range fun α : 𝓞 E => fun τ : X.Ψ => τ.1 (α : E)) ≤ (Submodule.span ℝ (X.embV '' (X.Λ : Set (Fin r → E)))).comap (single (X` using `X) a) := by`. Rewrite using `[Submodule.span_le]`.

Introduce and unpack `_ ⟨α, rfl⟩`. Establish `hmem : (α : E) • ((N : E) • Pi.single a 1) ∈ X.Λ` using `smul_int_mem α.isIntegral_coe hNmem`. Establish `hN0 : (N : ℝ) ≠ 0` using `by exact_mod_cast hN.ne'`. Establish `e : single (X` using `X) a (fun τ : X.Ψ => τ.1 (α : E)) = (N : ℝ)⁻¹ • X.embV ((α : E) • ((N : E) • Pi.single a 1)) := by`. Use function extensionality and compare the values at `τ b`.

Simplify using `only [single, LinearMap.coe_mk, AddHom.coe_mk, Pi.smul_apply, Data.embV, Data.emb, smul_eq_mul]`. Distinguish the cases in `hb : b = a`. Substitute `hb` using the available equality. Establish `hNc : (N : ℂ) ≠ 0` using `by exact_mod_cast hN.ne'`. Simplify using `only [Pi.single_eq_same, mul_one, map_mul, map_natCast, Complex.real_smul]`.

Use `push_cast`. Clear the denominators using the available nonvanishing facts. Simplify using `[Pi.single_eq_of_ne hb]`. Rewrite using `[SetLike.mem_coe, Submodule.mem_comap]`. Use `show single (X := X) a (fun τ : X.Ψ => τ.1 (α : E)) ∈ _`.

Rewrite using `[e]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, hmem, rfl⟩)`. Conclude with `hgen (x := s) (by rw [span_emb_int hD3]; exact Submodule.mem_top)`. Establish `hv : v = ∑ a : Fin r, single (X` using `X) a (fun τ => v τ a) := by`. Use function extensionality and compare the values at `τ b`.

Rewrite using `[Finset.sum_apply, Finset.sum_apply]`. Simplify using `only [single, LinearMap.coe_mk, AddHom.coe_mk]`. Rewrite using `[Finset.sum_eq_single b (fun a _ hab => by rw [Pi.single_apply, if_neg (Ne.symm hab)]) (fun h => absurd (Finset.mem_univ b) h), Pi.single_eq_same]`. Rewrite using `[hv]`. Conclude with `Submodule.sum_mem _ fun a _ => hsing a _`.
-/
theorem mem_span_Λ (hD3 : IntegerApproximationCount (E := E)) (v : X.Ψ → Fin r → ℂ) :
    v ∈ Submodule.span ℝ (X.embV '' (X.Λ : Set (Fin r → E))) := by
  classical
  have hsing : ∀ (a : Fin r) (s : X.Ψ → ℂ),
      single (X := X) a s ∈ Submodule.span ℝ (X.embV '' (X.Λ : Set (Fin r → E))) := by
    intro a s
    obtain ⟨N, hN, hNmem⟩ := exists_nat_smul_mem (X := X) (Pi.single a 1)
    have hgen : Submodule.span ℝ (Set.range fun α : 𝓞 E => fun τ : X.Ψ => τ.1 (α : E)) ≤
        (Submodule.span ℝ (X.embV '' (X.Λ : Set (Fin r → E)))).comap (single (X := X) a) := by
      rw [Submodule.span_le]
      rintro _ ⟨α, rfl⟩
      have hmem : (α : E) • ((N : E) • Pi.single a 1) ∈ X.Λ := smul_int_mem α.isIntegral_coe hNmem
      have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
      have e : single (X := X) a (fun τ : X.Ψ => τ.1 (α : E)) =
          (N : ℝ)⁻¹ • X.embV ((α : E) • ((N : E) • Pi.single a 1)) := by
        funext τ b
        simp only [single, LinearMap.coe_mk, AddHom.coe_mk, Pi.smul_apply, Data.embV, Data.emb,
          smul_eq_mul]
        by_cases hb : b = a
        · subst hb
          have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
          simp only [Pi.single_eq_same, mul_one, map_mul, map_natCast, Complex.real_smul]
          push_cast
          field_simp
        · simp [Pi.single_eq_of_ne hb]
      rw [SetLike.mem_coe, Submodule.mem_comap]
      show single (X := X) a (fun τ : X.Ψ => τ.1 (α : E)) ∈ _
      rw [e]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, hmem, rfl⟩)
    exact hgen (x := s) (by rw [span_emb_int hD3]; exact Submodule.mem_top)
  have hv : v = ∑ a : Fin r, single (X := X) a (fun τ => v τ a) := by
    funext τ b
    rw [Finset.sum_apply, Finset.sum_apply]
    simp only [single, LinearMap.coe_mk, AddHom.coe_mk]
    rw [Finset.sum_eq_single b (fun a _ hab => by rw [Pi.single_apply, if_neg (Ne.symm hab)])
      (fun h => absurd (Finset.mem_univ b) h), Pi.single_eq_same]
  rw [hv]
  exact Submodule.sum_mem _ fun a _ => hsing a _

/- English proof (translation)
Use `set W := Submodule.span ℝ (X.embV '' (X.Λp ξ : Set (Fin r → E))) with hW`. Establish `hα : ∀ (α : 𝓞 E), ∀ v ∈ W, (fun τ : X.Ψ => τ.1 (α : E) • v τ) ∈ W`. Introduce `α`. Set `M : (X.Ψ → Fin r → ℂ) →ₗ[ℝ] (X.Ψ → Fin r → ℂ)` to `{ toFun := fun v τ => τ.1 (α : E) • v τ map_add' := fun v v' => by funext τ; simp [smul_add] map_smul' := fun c v => by`. Use function extensionality and compare the values at `τ`.

Use `show τ.1 (α : E) • (c • v τ) = c • (τ.1 (α : E) • v τ)`. Conclude with `smul_comm _ _ _ }`. Establish `hle : W ≤ W.comap M`. Rewrite using `[hW, Submodule.span_le]`. Introduce and unpack `_ ⟨μ, hμ, rfl⟩`.

Rewrite `hμ` using `[SetLike.mem_coe, mem_Λp_iff]`. Establish `hαμ : (α : E) • μ ∈ X.Λp ξ`. Rewrite using `[mem_Λp_iff]`. Conclude with `⟨smul_int_mem α.isIntegral_coe hμ.1, by rw [HermitianTraceFormVanishing.herm_smul_left, hμ.2, mul_zero]⟩`. Rewrite using `[SetLike.mem_coe, Submodule.mem_comap]`.

Establish `e : M (X.embV μ) = X.embV ((α : E) • μ)`. Use function extensionality and compare the values at `τ b`. Simplify using `[M, Data.embV, Data.emb]`. Rewrite using `[e]`. Conclude with `Submodule.subset_span ⟨_, hαμ, rfl⟩`.

Introduce `v hv`. Conclude with `hle hv`. Set `T : (X.Ψ → ℂ) →ₗ[ℝ] (X.Ψ → Fin r → ℂ)` to `{ toFun := fun s τ => s τ • w τ map_add' := fun s s' => by funext τ; simp [add_smul] map_smul' := fun c s => by`. Use function extensionality and compare the values at `τ`. Simplify using `only [Pi.smul_apply, RingHom.id_apply, Complex.real_smul]`.

Rewrite using `[← Complex.coe_smul c (s τ • w τ), smul_smul] }`. Establish `hle : Submodule.span ℝ (Set.range fun α : 𝓞 E => fun τ : X.Ψ => τ.1 (α : E)) ≤ W.comap T`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨α, rfl⟩`. Conclude with `hα α w hw`.

Conclude with `hle (x := s) (by rw [span_emb_int hD3]; exact Submodule.mem_top)`.
-/
theorem scal_closed (hD3 : IntegerApproximationCount (E := E)) {ξ : Fin r → E} {w : X.Ψ → Fin r → ℂ}
    (hw : w ∈ Submodule.span ℝ (X.embV '' (X.Λp ξ : Set (Fin r → E)))) (s : X.Ψ → ℂ) :
    (fun τ => s τ • w τ) ∈ Submodule.span ℝ (X.embV '' (X.Λp ξ : Set (Fin r → E))) := by
  set W := Submodule.span ℝ (X.embV '' (X.Λp ξ : Set (Fin r → E))) with hW

  have hα : ∀ (α : 𝓞 E), ∀ v ∈ W, (fun τ : X.Ψ => τ.1 (α : E) • v τ) ∈ W := by
    intro α
    let M : (X.Ψ → Fin r → ℂ) →ₗ[ℝ] (X.Ψ → Fin r → ℂ) :=
      { toFun := fun v τ => τ.1 (α : E) • v τ
        map_add' := fun v v' => by funext τ; simp [smul_add]
        map_smul' := fun c v => by
          funext τ
          show τ.1 (α : E) • (c • v τ) = c • (τ.1 (α : E) • v τ)
          exact smul_comm _ _ _ }
    have hle : W ≤ W.comap M := by
      rw [hW, Submodule.span_le]
      rintro _ ⟨μ, hμ, rfl⟩
      rw [SetLike.mem_coe, mem_Λp_iff] at hμ
      have hαμ : (α : E) • μ ∈ X.Λp ξ := by
        rw [mem_Λp_iff]
        exact ⟨smul_int_mem α.isIntegral_coe hμ.1, by rw [HermitianTraceFormVanishing.herm_smul_left, hμ.2, mul_zero]⟩
      rw [SetLike.mem_coe, Submodule.mem_comap]
      have e : M (X.embV μ) = X.embV ((α : E) • μ) := by
        funext τ b
        simp [M, Data.embV, Data.emb]
      rw [e]
      exact Submodule.subset_span ⟨_, hαμ, rfl⟩
    intro v hv
    exact hle hv
  let T : (X.Ψ → ℂ) →ₗ[ℝ] (X.Ψ → Fin r → ℂ) :=
    { toFun := fun s τ => s τ • w τ
      map_add' := fun s s' => by funext τ; simp [add_smul]
      map_smul' := fun c s => by
        funext τ
        simp only [Pi.smul_apply, RingHom.id_apply, Complex.real_smul]
        rw [← Complex.coe_smul c (s τ • w τ), smul_smul] }
  have hle : Submodule.span ℝ (Set.range fun α : 𝓞 E => fun τ : X.Ψ => τ.1 (α : E)) ≤ W.comap T := by
    rw [Submodule.span_le]
    rintro _ ⟨α, rfl⟩
    exact hα α w hw
  exact hle (x := s) (by rw [span_emb_int hD3]; exact Submodule.mem_top)

/- English proof (translation)
Take `⟨hξΛ, -, hξ0⟩` from `hξ`. Choose the witnesses or unpack the hypotheses as in `⟨η, hηΛ, hηξ⟩ : ∃ η ∈ X.Λ, herm X.Gm η ξ ≠ 0 := by`. Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Establish `hall : ∀ v : Fin r → E, herm X.Gm v ξ = 0`.

Introduce `v`. Establish `hv : v ∈ Submodule.span E (X.Λ : Set (Fin r → E))` using `X.Λ_span ▸ Submodule.mem_top`. Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem v hv => exact hcon v hv`. Consider the case `zero => simp [herm]`.

Consider the case `add v w _ _ ihv ihw => rw [HermitianTraceFormVanishing.herm_add_left, ihv, ihw, add_zero]`. Consider the case `smul c v _ ihv => rw [HermitianTraceFormVanishing.herm_smul_left, ihv, mul_zero]`. Apply `hξ0` to reduce the goal to its premises. Establish `hmv : X.Gm.mulVec (fun b => cc (ξ b)) = 0`. Use function extensionality and compare the values at `a`.

Use `hall (Pi.single a 1)` as an intermediate fact. Simplify `this` using `[herm, Pi.single_apply, Matrix.mulVec, dotProduct]`. Establish `h0` using `Matrix.eq_zero_of_mulVec_eq_zero X.Gm_det hmv`. Use function extensionality and compare the values at `b`. Use `congrFun h0 b` as an intermediate fact.

Simplify using `only [Pi.zero_apply] at this`. Establish `h2` using `congrArg cc this`. Simplify using `using h2`. Use `set d : E := (X.den : E) with hd`. Establish `hcint : IsIntegral ℤ (d * herm X.Gm η ξ)` using `X.Λ_int η hηΛ ξ hξΛ`.

Establish `hc0 : d * herm X.Gm η ξ ≠ 0`. Use `mul_ne_zero ?_ hηξ` and prove the remaining obligations. Introduce `h`. Apply `X.den_ne` to reduce the goal to its premises. Simplify `h` using `[hd]`.

Use `set c : E := d * herm X.Gm η ξ with hc`. Set `P : (X.Ψ → Fin r → ℂ) →ₗ[ℝ] (X.Ψ → Fin r → ℂ)` to `{ toFun := fun v τ => τ.1 c • v τ - (τ.1 d * hermC τ.1 X.Gm (v τ) (Data.emb τ.1 ξ)) • Data.emb τ.1 η map_add' := fun v v' => by`. Use function extensionality and compare the values at `τ`. Simplify using `only [Pi.add_apply, hermC_add_left, smul_add, mul_add, add_smul]`. Normalize the expressions using the abelian group laws.

Use the proof step `map_smul' := fun a v => by`. Use function extensionality and compare the values at `τ`. Simplify using `only [Pi.smul_apply, RingHom.id_apply]`. Rewrite using `[← Complex.coe_smul a (v τ), ← Complex.coe_smul a, hermC_smul_left]`. Use `module }`.

Establish `hPΛ : ∀ l ∈ X.Λ, P (X.embV l) ∈ X.embV '' (X.Λp ξ : Set (Fin r → E))`. Introduce `l hl`. Use `⟨c • l - (d * herm X.Gm l ξ) • η, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[SetLike.mem_coe, mem_Λp_iff]`. Use `⟨X.Λ.sub_mem (smul_int_mem hcint hl) (smul_int_mem (X.Λ_int l hl ξ hξΛ) hηΛ), ?_⟩` and prove the remaining obligations.

Rewrite using `[HermitianTraceFormVanishing.herm_sub_left, HermitianTraceFormVanishing.herm_smul_left, HermitianTraceFormVanishing.herm_smul_left, hc]`. Expand and normalize the polynomial expressions, which then agree. Use function extensionality and compare the values at `τ b`. Simplify using `[P, Data.embV, Data.emb, hermC_emb]`. Establish `hPv : P v = fun τ => τ.1 c • v τ`.

Use function extensionality and compare the values at `τ`. Simplify using `only [P, LinearMap.coe_mk, AddHom.coe_mk]`. Rewrite using `[hv τ, mul_zero, zero_smul, sub_zero]`. Establish `hmem : P v ∈ Submodule.span ℝ (X.embV '' (X.Λp ξ : Set (Fin r → E)))`. Establish `h1` using `mem_span_Λ hD3 v`.

Establish `h2 : Submodule.map P (Submodule.span ℝ (X.embV '' (X.Λ : Set (Fin r → E)))) ≤ Submodule.span ℝ (X.embV '' (X.Λp ξ : Set (Fin r → E)))`. Rewrite using `[Submodule.map_span, Submodule.span_le]`. Introduce and unpack `_ ⟨_, ⟨l, hl, rfl⟩, rfl⟩`. Conclude with `Submodule.subset_span (hPΛ l hl)`. Conclude with `h2 (Submodule.mem_map_of_mem h1)`.

Rewrite `hmem` using `[hPv]`. Establish `h3` using `scal_closed hD3 hmem (fun τ => (τ.1 c)⁻¹)`. Use `h3 using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `τ`. Rewrite using `[smul_smul, inv_mul_cancel₀ ((map_ne_zero τ.1).mpr hc0), one_smul]`.
-/
theorem Iperp_le (hD3 : IntegerApproximationCount (E := E)) {ξ : Fin r → E} (hξ : X.IsIso ξ)
    {v : X.Ψ → Fin r → ℂ} (hv : v ∈ X.Iperp ξ) :
    v ∈ Submodule.span ℝ (X.embV '' (X.Λp ξ : Set (Fin r → E))) := by
  classical
  obtain ⟨hξΛ, -, hξ0⟩ := hξ
  obtain ⟨η, hηΛ, hηξ⟩ : ∃ η ∈ X.Λ, herm X.Gm η ξ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hall : ∀ v : Fin r → E, herm X.Gm v ξ = 0 := by
      intro v
      have hv : v ∈ Submodule.span E (X.Λ : Set (Fin r → E)) := X.Λ_span ▸ Submodule.mem_top
      induction hv using Submodule.span_induction with
      | mem v hv => exact hcon v hv
      | zero => simp [herm]
      | add v w _ _ ihv ihw => rw [HermitianTraceFormVanishing.herm_add_left, ihv, ihw, add_zero]
      | smul c v _ ihv => rw [HermitianTraceFormVanishing.herm_smul_left, ihv, mul_zero]
    apply hξ0
    have hmv : X.Gm.mulVec (fun b => cc (ξ b)) = 0 := by
      funext a
      have := hall (Pi.single a 1)
      simpa [herm, Pi.single_apply, Matrix.mulVec, dotProduct] using this
    have h0 := Matrix.eq_zero_of_mulVec_eq_zero X.Gm_det hmv
    funext b
    have := congrFun h0 b
    simp only [Pi.zero_apply] at this
    have h2 := congrArg cc this
    simpa using h2
  set d : E := (X.den : E) with hd
  have hcint : IsIntegral ℤ (d * herm X.Gm η ξ) := X.Λ_int η hηΛ ξ hξΛ
  have hc0 : d * herm X.Gm η ξ ≠ 0 := by
    refine mul_ne_zero ?_ hηξ
    intro h
    apply X.den_ne
    simpa [hd] using h
  set c : E := d * herm X.Gm η ξ with hc
  let P : (X.Ψ → Fin r → ℂ) →ₗ[ℝ] (X.Ψ → Fin r → ℂ) :=
    { toFun := fun v τ => τ.1 c • v τ -
        (τ.1 d * hermC τ.1 X.Gm (v τ) (Data.emb τ.1 ξ)) • Data.emb τ.1 η
      map_add' := fun v v' => by
        funext τ
        simp only [Pi.add_apply, hermC_add_left, smul_add, mul_add, add_smul]
        abel
      map_smul' := fun a v => by
        funext τ
        simp only [Pi.smul_apply, RingHom.id_apply]
        rw [← Complex.coe_smul a (v τ), ← Complex.coe_smul a, hermC_smul_left]
        module }
  have hPΛ : ∀ l ∈ X.Λ, P (X.embV l) ∈ X.embV '' (X.Λp ξ : Set (Fin r → E)) := by
    intro l hl
    refine ⟨c • l - (d * herm X.Gm l ξ) • η, ?_, ?_⟩
    · rw [SetLike.mem_coe, mem_Λp_iff]
      refine ⟨X.Λ.sub_mem (smul_int_mem hcint hl) (smul_int_mem (X.Λ_int l hl ξ hξΛ) hηΛ), ?_⟩
      rw [HermitianTraceFormVanishing.herm_sub_left, HermitianTraceFormVanishing.herm_smul_left, HermitianTraceFormVanishing.herm_smul_left, hc]
      ring
    · funext τ b
      simp [P, Data.embV, Data.emb, hermC_emb]
  have hPv : P v = fun τ => τ.1 c • v τ := by
    funext τ
    simp only [P, LinearMap.coe_mk, AddHom.coe_mk]
    rw [hv τ, mul_zero, zero_smul, sub_zero]
  have hmem : P v ∈ Submodule.span ℝ (X.embV '' (X.Λp ξ : Set (Fin r → E))) := by
    have h1 := mem_span_Λ hD3 v
    have h2 : Submodule.map P (Submodule.span ℝ (X.embV '' (X.Λ : Set (Fin r → E)))) ≤
        Submodule.span ℝ (X.embV '' (X.Λp ξ : Set (Fin r → E))) := by
      rw [Submodule.map_span, Submodule.span_le]
      rintro _ ⟨_, ⟨l, hl, rfl⟩, rfl⟩
      exact Submodule.subset_span (hPΛ l hl)
    exact h2 (Submodule.mem_map_of_mem h1)
  rw [hPv] at hmem
  have h3 := scal_closed hD3 hmem (fun τ => (τ.1 c)⁻¹)
  convert h3 using 1
  funext τ
  rw [smul_smul, inv_mul_cancel₀ ((map_ne_zero τ.1).mpr hc0), one_smul]

/- English proof (translation)
Set `Q : (X.Ψ → Fin r → ℂ) →ₗ[ℝ] (X.Ψ → Fin r → ℂ)` to `{ toFun := fun v => X.ucomp z ξ v map_add' := fun v v' => by`. Use function extensionality and compare the values at `τ`. Use `show (v τ + v' τ) - (X.Hf z τ (v τ + v' τ) (Data.emb τ.1 ξ) / X.Hf z τ (Data.emb τ.1 ξ) (Data.emb τ.1 ξ)) • Data.emb τ.1 ξ = _`. Rewrite using `[UnipotentCoefficientShift.Hf_add_left, add_div, add_smul]`. Use `show _ = (v τ - _) + (v' τ - _)`.

Normalize the expressions using the abelian group laws. Use the proof step `map_smul' := fun a v => by`. Use function extensionality and compare the values at `τ`. Use `show a • v τ - (X.Hf z τ (a • v τ) (Data.emb τ.1 ξ) / X.Hf z τ (Data.emb τ.1 ξ) (Data.emb τ.1 ξ)) • Data.emb τ.1 ξ = a • (v τ - (X.Hf z τ (v τ) (Data.emb τ.1 ξ) / X.Hf z τ (Data.emb τ.1 ξ) (Data.emb τ.1 ξ)) • Data.emb τ.1 ξ)`. Rewrite using `[← Complex.coe_smul a (v τ), UnipotentCoefficientShift.Hf_smul_left, ← Complex.coe_smul a, mul_div_assoc]`.

Use `module }`. Establish `h1` using `Iperp_le hD3 hξ hu.1`. Establish `h2 : Submodule.map Q (Submodule.span ℝ (X.embV '' (X.Λp ξ : Set (Fin r → E)))) ≤ Submodule.span ℝ (Set.range fun μ : X.Λp ξ => X.ucomp z ξ (X.embV μ))`. Rewrite using `[Submodule.map_span, Submodule.span_le]`. Introduce and unpack `_ ⟨_, ⟨μ, hμ, rfl⟩, rfl⟩`.

Conclude with `Submodule.subset_span ⟨⟨μ, hμ⟩, rfl⟩`. Establish `h3` using `h2 (Submodule.mem_map_of_mem h1)`. Establish `e : Q u = u` using `MajorantOperators.ucomp_of_mem hu`. Rewrite `h3` using `[e]`. Then use the resulting hypothesis.
-/
theorem Uz_le_span (hD3 : IntegerApproximationCount (E := E)) {z : Frame X.Ψ r} {ξ : Fin r → E}
    (hξ : X.IsIso ξ) {u : X.Ψ → Fin r → ℂ} (hu : u ∈ X.Uz z ξ) :
    u ∈ Submodule.span ℝ (Set.range fun μ : X.Λp ξ => X.ucomp z ξ (X.embV μ)) := by
  let Q : (X.Ψ → Fin r → ℂ) →ₗ[ℝ] (X.Ψ → Fin r → ℂ) :=
    { toFun := fun v => X.ucomp z ξ v
      map_add' := fun v v' => by
        funext τ
        show (v τ + v' τ) - (X.Hf z τ (v τ + v' τ) (Data.emb τ.1 ξ) /
          X.Hf z τ (Data.emb τ.1 ξ) (Data.emb τ.1 ξ)) • Data.emb τ.1 ξ = _
        rw [UnipotentCoefficientShift.Hf_add_left, add_div, add_smul]
        show _ = (v τ - _) + (v' τ - _)
        abel
      map_smul' := fun a v => by
        funext τ
        show a • v τ - (X.Hf z τ (a • v τ) (Data.emb τ.1 ξ) /
          X.Hf z τ (Data.emb τ.1 ξ) (Data.emb τ.1 ξ)) • Data.emb τ.1 ξ =
            a • (v τ - (X.Hf z τ (v τ) (Data.emb τ.1 ξ) /
              X.Hf z τ (Data.emb τ.1 ξ) (Data.emb τ.1 ξ)) • Data.emb τ.1 ξ)
        rw [← Complex.coe_smul a (v τ), UnipotentCoefficientShift.Hf_smul_left, ← Complex.coe_smul a, mul_div_assoc]
        module }
  have h1 := Iperp_le hD3 hξ hu.1
  have h2 : Submodule.map Q (Submodule.span ℝ (X.embV '' (X.Λp ξ : Set (Fin r → E)))) ≤
      Submodule.span ℝ (Set.range fun μ : X.Λp ξ => X.ucomp z ξ (X.embV μ)) := by
    rw [Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨μ, hμ, rfl⟩, rfl⟩
    exact Submodule.subset_span ⟨⟨μ, hμ⟩, rfl⟩
  have h3 := h2 (Submodule.mem_map_of_mem h1)
  have e : Q u = u := MajorantOperators.ucomp_of_mem hu
  rwa [e] at h3

end LatticeSpanMembership

end ReciprocityTheory.ChartRestriction.G.FD
