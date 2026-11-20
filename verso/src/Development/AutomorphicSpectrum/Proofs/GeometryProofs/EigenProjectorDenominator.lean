import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlagLabelBasesExist

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Sandwich

open NumberField Polynomial GlobalTheory.CompanionTheory.Ar

variable {E : Type} [Field E] [NumberField E]

/- English proof (translation)
Take `⟨f, -, hroot, hder⟩` from `exists_sep_poly w`. Establish `key : ∀ p : ℤ[X], eval₂ (Int.castRingHom (𝓞 E)) w p = aeval w p` using `fun p => by`. Rewrite using `[aeval_def, algebraMap_int_eq]`. Establish `hF : (f.map (Int.castRingHom (𝓞 E))).IsRoot w`. Rewrite using `[IsRoot, eval_map, key]`.

Conclude with `hroot`. Use `set g := f.map (Int.castRingHom (𝓞 E)) /ₘ (X - C w) with hg`. Establish `hfac : (X - C w) * g = f.map (Int.castRingHom (𝓞 E))` using `(mul_divByMonic_eq_iff_isRoot).2 hF`. Use `⟨g.eval w, ?_, ?_⟩` and prove the remaining obligations. Establish `hd : (derivative (f.map (Int.castRingHom (𝓞 E)))).eval w = g.eval w`.

Rewrite using `[← hfac, derivative_mul]`. Simplify using the standard rewrite rules. Rewrite using `[← hd, derivative_map, eval_map, key]`. Conclude with `hder`. Introduce `Ω _ V _ _ ρ σ`.

Use `⟨eval₂ (scal V σ) (ρ w) g, eval₂_mem_opRing ρ σ w g, ?_, ?_⟩` and prove the remaining obligations. Establish `hcomm : ∀ k, Commute (scal V σ (g.coeff k)) (ρ w)` using `fun k => commute_scal σ (g.coeff k) (ρ w)`. Establish `h1 : ρ w - scal V σ w = eval₂ (scal V σ) (ρ w) (X - C w)`. Simplify using `[eval₂_sub]`. Rewrite using `[h1, ← eval₂_mul_noncomm _ _ hcomm, hfac, eval₂_map]`.

Establish `hc : (scal V σ).comp (Int.castRingHom (𝓞 E)) = ρ.comp (Int.castRingHom (𝓞 E))` using `RingHom.ext_int _ _`. Rewrite using `[hc, ← hom_eval₂, key, hroot, map_zero]`. Introduce `v hv`. Conclude with `eval₂_apply_of_eigen ρ σ w hv g`.
-/
theorem exists_uniform_factor (w : 𝓞 E) :
    ∃ x : 𝓞 E, x ≠ 0 ∧ ∀ (Ω : Type) [Field Ω] (V : Type) [AddCommGroup V] [Module Ω V]
      (ρ : 𝓞 E →+* Module.End Ω V) (σ : 𝓞 E →+* Ω),
      ∃ T ∈ opRing ρ σ, (ρ w - scal V σ w) * T = 0 ∧ ∀ v, ρ w v = σ w • v → T v = σ x • v := by
  obtain ⟨f, -, hroot, hder⟩ := exists_sep_poly w
  have key : ∀ p : ℤ[X], eval₂ (Int.castRingHom (𝓞 E)) w p = aeval w p := fun p => by
    rw [aeval_def, algebraMap_int_eq]
  have hF : (f.map (Int.castRingHom (𝓞 E))).IsRoot w := by
    rw [IsRoot, eval_map, key]
    exact hroot
  set g := f.map (Int.castRingHom (𝓞 E)) /ₘ (X - C w) with hg
  have hfac : (X - C w) * g = f.map (Int.castRingHom (𝓞 E)) :=
    (mul_divByMonic_eq_iff_isRoot).2 hF
  refine ⟨g.eval w, ?_, ?_⟩
  · have hd : (derivative (f.map (Int.castRingHom (𝓞 E)))).eval w = g.eval w := by
      rw [← hfac, derivative_mul]
      simp
    rw [← hd, derivative_map, eval_map, key]
    exact hder
  · intro Ω _ V _ _ ρ σ
    refine ⟨eval₂ (scal V σ) (ρ w) g, eval₂_mem_opRing ρ σ w g, ?_, ?_⟩
    · have hcomm : ∀ k, Commute (scal V σ (g.coeff k)) (ρ w) :=
        fun k => commute_scal σ (g.coeff k) (ρ w)
      have h1 : ρ w - scal V σ w = eval₂ (scal V σ) (ρ w) (X - C w) := by
        simp [eval₂_sub]
      rw [h1, ← eval₂_mul_noncomm _ _ hcomm, hfac, eval₂_map]
      have hc : (scal V σ).comp (Int.castRingHom (𝓞 E)) = ρ.comp (Int.castRingHom (𝓞 E)) :=
        RingHom.ext_int _ _
      rw [hc, ← hom_eval₂, key, hroot, map_zero]
    · intro v hv
      exact eval₂_apply_of_eigen ρ σ w hv g

/- English proof (translation)
Simplify using `[eigSp, Submodule.mem_iInf, LinearMap.mem_ker, sub_eq_zero]`.
-/
private theorem mem_eigSp_iff_geometry {Ω : Type} [Field Ω] {V : Type} [AddCommGroup V] [Module Ω V]
    (ρ : 𝓞 E →+* Module.End Ω V) (σ : 𝓞 E →+* Ω) (v : V) :
    v ∈ eigSp ρ σ ↔ ∀ a, ρ a v = σ a • v := by
  simp [eigSp, Submodule.mem_iInf, LinearMap.mem_ker, sub_eq_zero]

/- English proof (translation)
Proceed by induction on `W using Finset.induction_on with`. Consider the case `empty`. Use `⟨1, one_ne_zero, ?_⟩` and prove the remaining obligations. Introduce `Ω _ V _ _ ρ σ`. Conclude with `⟨1, (opRing ρ σ).one_mem, by simp, fun v _ => by simp⟩`.

Consider the case `@insert a W' ha ih`. Take `⟨x', hx', hT'⟩` from `ih`. Take `⟨xa, hxa, hTa⟩` from `exists_uniform_factor a`. Use `⟨xa * x', mul_ne_zero hxa hx', ?_⟩` and prove the remaining obligations. Introduce `Ω _ V _ _ ρ σ`.

Take `⟨T', hT'm, hT'k, hT'e⟩` from `hT' Ω V ρ σ`. Take `⟨Ta, hTam, hTak, hTae⟩` from `hTa Ω V ρ σ`. Use `⟨Ta * T', (opRing ρ σ).mul_mem hTam hT'm, ?_, ?_⟩` and prove the remaining obligations. Introduce `w hw`. Break down `Finset.mem_insert.1 hw with rfl | hw'` into its components or cases.

Rewrite using `[← mul_assoc, hTak, zero_mul]`. Establish `hc : Commute (ρ w - scal V σ w) Ta` using `(commute_opRing hTam w).symm.sub_left (commute_scal σ w Ta)`. Rewrite using `[← mul_assoc, hc.eq, mul_assoc, hT'k w hw', mul_zero]`. Introduce `v hv`. Apply the tactic sequence `have hva : ρ a v = σ a • v := (mem_eigSp_iff_geometry ρ σ v).1 hv a`.

Express the relevant statement in the definitionally equal form `Ta (T' v) = _`. Rewrite using `[hT'e v hv, map_smul, hTae v hva, smul_smul, map_mul, mul_comm (σ xa)]`.
-/
theorem exists_uniform_product (W : Finset (𝓞 E)) :
    ∃ x : 𝓞 E, x ≠ 0 ∧ ∀ (Ω : Type) [Field Ω] (V : Type) [AddCommGroup V] [Module Ω V]
      (ρ : 𝓞 E →+* Module.End Ω V) (σ : 𝓞 E →+* Ω),
      ∃ T ∈ opRing ρ σ, (∀ w ∈ W, (ρ w - scal V σ w) * T = 0) ∧ ∀ v ∈ eigSp ρ σ, T v = σ x • v := by
  classical
  induction W using Finset.induction_on with
  | empty =>
    refine ⟨1, one_ne_zero, ?_⟩
    intro Ω _ V _ _ ρ σ
    exact ⟨1, (opRing ρ σ).one_mem, by simp, fun v _ => by simp⟩
  | @insert a W' ha ih =>
    obtain ⟨x', hx', hT'⟩ := ih
    obtain ⟨xa, hxa, hTa⟩ := exists_uniform_factor a
    refine ⟨xa * x', mul_ne_zero hxa hx', ?_⟩
    intro Ω _ V _ _ ρ σ
    obtain ⟨T', hT'm, hT'k, hT'e⟩ := hT' Ω V ρ σ
    obtain ⟨Ta, hTam, hTak, hTae⟩ := hTa Ω V ρ σ
    refine ⟨Ta * T', (opRing ρ σ).mul_mem hTam hT'm, ?_, ?_⟩
    · intro w hw
      rcases Finset.mem_insert.1 hw with rfl | hw'
      · rw [← mul_assoc, hTak, zero_mul]
      · have hc : Commute (ρ w - scal V σ w) Ta :=
          (commute_opRing hTam w).symm.sub_left (commute_scal σ w Ta)
        rw [← mul_assoc, hc.eq, mul_assoc, hT'k w hw', mul_zero]
    · intro v hv
      have hva : ρ a v = σ a • v := (mem_eigSp_iff_geometry ρ σ v).1 hv a
      change Ta (T' v) = _
      rw [hT'e v hv, map_smul, hTae v hva, smul_smul, map_mul, mul_comm (σ xa)]

/- English proof (translation)
Introduce `E _ _`. Take `⟨S, hS⟩` from `(Module.Finite.fg_top : (⊤ : Submodule ℤ (𝓞 E)).FG)`. Take `⟨x, hx, hT⟩` from `exists_uniform_product S`. Establish `hint : IsIntegral ℤ x` using `Algebra.IsIntegral.isIntegral x`. Establish `hbot` using `Ideal.comap_ne_bot_of_integral_mem hx (Ideal.mem_span_singleton_self x) hint`.

Take `⟨c, hcmem, hc0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hbot`. Rewrite `hcmem` using `[Ideal.mem_comap, Ideal.mem_span_singleton, algebraMap_int_eq, eq_intCast]`. Take `⟨y0, hy0⟩` from `hcmem`. Choose the witnesses or unpack the hypotheses as in `⟨n, hn0, y, hy⟩ : ∃ n : ℕ, 0 < n ∧ ∃ y : 𝓞 E, x * y = (n : 𝓞 E) := by`. Break down `Int.natAbs_eq c with h | h` into its components or cases.

Use `⟨c.natAbs, Int.natAbs_pos.2 hc0, y0, ?_⟩` and prove the remaining obligations. Rewrite using `[← hy0]`. Use `conv_lhs => rw [h]`. Simplify using the standard rewrite rules. Use `⟨c.natAbs, Int.natAbs_pos.2 hc0, -y0, ?_⟩` and prove the remaining obligations.

Rewrite using `[mul_neg, ← hy0]`. Use `conv_lhs => rw [h]`. Simplify using the standard rewrite rules. Use `⟨n, hn0, ?_⟩` and prove the remaining obligations. Introduce `Ω _ _ V _ _ ρ σ`.

Take `⟨T, hTm, hTk, hTe⟩` from `hT Ω V ρ σ`. Establish `hall : ∀ v, ∀ a : 𝓞 E, ρ a (T v) = σ a • T v`. Introduce `v a`. Establish `ha : a ∈ Submodule.span ℤ (S : Set (𝓞 E))`. Rewrite using `[hS]`.

Discharge the goal by the elementary cases of `trivial`. Proceed by induction on `ha using Submodule.span_induction with`. Consider the case `mem w hw`. Establish `h` using `congrArg (fun U : Module.End Ω V => U v) (hTk w hw)`. Express the relevant statement in the definitionally equal form `(ρ w - scal V σ w) (T v) = 0 at h`.

Rewrite `h` using `[LinearMap.sub_apply, scal_apply, sub_eq_zero]`. Conclude with `h`. Consider the case `zero => simp`. Consider the case `add a b _ _ iha ihb`. Rewrite using `[map_add, map_add, LinearMap.add_apply, iha, ihb, add_smul]`.

Consider the case `smul m a _ ih`. Rewrite using `[map_zsmul, map_zsmul, LinearMap.smul_apply, ih, smul_assoc]`. Establish `hs : scal V σ y ∈ opRing ρ σ`. Simplify using `using eval₂_mem_opRing ρ σ 0 (C y)`. Use `⟨scal V σ y * T, (opRing ρ σ).mul_mem hs hTm, ?_, ?_⟩` and prove the remaining obligations.

Introduce `v`. Express the relevant statement in the definitionally equal form `scal V σ y (T v) ∈ eigSp ρ σ`. Rewrite using `[scal_apply]`. Apply the tactic sequence `exact Submodule.smul_mem _ _ ((mem_eigSp_iff_geometry ρ σ (T v)).2 (hall v))`. Introduce `v hv`.

Express the relevant statement in the definitionally equal form `scal V σ y (T v) = _`. Rewrite using `[scal_apply, hTe v hv, smul_smul, ← map_mul, mul_comm y x, hy, map_natCast]`.
-/
theorem exists_eigen_op_uniform : ∀ (E : Type) [Field E] [NumberField E], ∃ D : ℕ, 0 < D ∧
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] (V : Type) [AddCommGroup V] [Module Ω V]
      (ρ : 𝓞 E →+* Module.End Ω V) (σ : 𝓞 E →+* Ω),
      ∃ T ∈ opRing ρ σ, (∀ v, T v ∈ eigSp ρ σ) ∧ ∀ v ∈ eigSp ρ σ, T v = (D : Ω) • v := by
  intro E _ _
  obtain ⟨S, hS⟩ := (Module.Finite.fg_top : (⊤ : Submodule ℤ (𝓞 E)).FG)
  obtain ⟨x, hx, hT⟩ := exists_uniform_product S
  have hint : IsIntegral ℤ x := Algebra.IsIntegral.isIntegral x
  have hbot := Ideal.comap_ne_bot_of_integral_mem hx (Ideal.mem_span_singleton_self x) hint
  obtain ⟨c, hcmem, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  rw [Ideal.mem_comap, Ideal.mem_span_singleton, algebraMap_int_eq, eq_intCast] at hcmem
  obtain ⟨y0, hy0⟩ := hcmem
  obtain ⟨n, hn0, y, hy⟩ : ∃ n : ℕ, 0 < n ∧ ∃ y : 𝓞 E, x * y = (n : 𝓞 E) := by
    rcases Int.natAbs_eq c with h | h
    · refine ⟨c.natAbs, Int.natAbs_pos.2 hc0, y0, ?_⟩
      rw [← hy0]
      conv_lhs => rw [h]
      simp
    · refine ⟨c.natAbs, Int.natAbs_pos.2 hc0, -y0, ?_⟩
      rw [mul_neg, ← hy0]
      conv_lhs => rw [h]
      simp
  refine ⟨n, hn0, ?_⟩
  intro Ω _ _ V _ _ ρ σ
  obtain ⟨T, hTm, hTk, hTe⟩ := hT Ω V ρ σ
  have hall : ∀ v, ∀ a : 𝓞 E, ρ a (T v) = σ a • T v := by
    intro v a
    have ha : a ∈ Submodule.span ℤ (S : Set (𝓞 E)) := by
      rw [hS]
      trivial
    induction ha using Submodule.span_induction with
    | mem w hw =>
      have h := congrArg (fun U : Module.End Ω V => U v) (hTk w hw)
      change (ρ w - scal V σ w) (T v) = 0 at h
      rw [LinearMap.sub_apply, scal_apply, sub_eq_zero] at h
      exact h
    | zero => simp
    | add a b _ _ iha ihb =>
      rw [map_add, map_add, LinearMap.add_apply, iha, ihb, add_smul]
    | smul m a _ ih =>
      rw [map_zsmul, map_zsmul, LinearMap.smul_apply, ih, smul_assoc]
  have hs : scal V σ y ∈ opRing ρ σ := by
    simpa using eval₂_mem_opRing ρ σ 0 (C y)
  refine ⟨scal V σ y * T, (opRing ρ σ).mul_mem hs hTm, ?_, ?_⟩
  · intro v
    change scal V σ y (T v) ∈ eigSp ρ σ
    rw [scal_apply]
    exact Submodule.smul_mem _ _ ((mem_eigSp_iff_geometry ρ σ (T v)).2 (hall v))
  · intro v hv
    change scal V σ y (T v) = _
    rw [scal_apply, hTe v hv, smul_smul, ← map_mul, mul_comm y x, hy, map_natCast]

end GlobalTheory.CompanionTheory.Ar.Sandwich
