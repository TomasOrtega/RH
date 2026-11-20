import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.ChiQuadAlt

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.CyclotomicQExpansion GlobalTheory.KummerEisensteinGalois GlobalTheory.K4 GlobalTheory.LambdaValuationPowers
open scoped Matrix MatrixGroups TensorProduct

namespace UpperTheory.V.Z.Kato.Joint

variable {l : ℕ} [Fact l.Prime]

/- English proof (translation)
Simplify using `[Cg]`.
-/
private theorem cgp_refl (n : ℕ) (x : Qbar l) : Cg n x x := by simp [Cg]

/- English proof (translation)
Unfold `Cg at *`. Rewrite using `[norm_sub_rev]` and apply the resulting hypothesis.
-/
private theorem cgp_symm {n : ℕ} {x y : Qbar l} (h : Cg n x y) : Cg n y x := by
  unfold Cg at *
  rwa [norm_sub_rev]

/- English proof (translation)
Unfold `Cg at *`. Rewrite using `[add_sub_add_comm]`. Conclude with `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le h h')`.
-/
private theorem cgp_add {n : ℕ} {x y x' y' : Qbar l} (h : Cg n x y) (h' : Cg n x' y') : Cg n (x + x') (y + y') := by
  unfold Cg at *
  rw [add_sub_add_comm]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h h')

/- English proof (translation)
Unfold `Cg at *`. Rewrite using `[← sub_add_sub_cancel x y z]`. Conclude with `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le h h')`.
-/
private theorem cgp_trans {n : ℕ} {x y z : Qbar l} (h : Cg n x y) (h' : Cg n y z) : Cg n x z := by
  unfold Cg at *
  rw [← sub_add_sub_cancel x y z]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h h')

/- English proof (translation)
Simplify `ha) h` using `using cg_mul_left (k := 0) (Nat.zero_le _) (by simpa`.
-/
private theorem cgp_mul {n : ℕ} {a x y : Qbar l} (ha : ‖a‖ ≤ 1) (h : Cg n x y) : Cg n (a * x) (a * y) := by
  simpa using cg_mul_left (k := 0) (Nat.zero_le _) (by simpa using ha) h

/- English proof (translation)
Consider the cases of `T with`. Consider the case `T q => show Cg n (GlobalTheory.EisM.To k (χ q) q f i) (GlobalTheory.EisM.To k (χ q) q g i)`. Unfold `GlobalTheory.EisM.To GlobalTheory.EisM.Vo`. Use `cgp_add (h _) (cgp_mul ?_ ?_)` and prove the remaining obligations. Rewrite using `[norm_mul, norm_pow]`.

Conclude with `mul_le_one₀ (hχ q) (by positivity) (pow_le_one₀ (norm_nonneg _) (IsUltrametricDist.norm_natCast_le_one _ _))`. Use `split_ifs`. Conclude with `h _`. Conclude with `cgp_refl _ _`. Consider the case `U => exact h _`.

Consider the case `D d => exact cgp_mul (hχ d) (h i)`.
-/
private theorem fop_cg {k n : ℕ} {χ : ℕ → Qbar l} (hχ : ∀ d, ‖χ d‖ ≤ 1) (T : Letter) {f g : ℕ → Qbar l}
    (h : ∀ i, Cg n (f i) (g i)) (i : ℕ) : Cg n (fop k l χ T f i) (fop k l χ T g i) := by
  cases T with
  | T q =>
    show Cg n (GlobalTheory.EisM.To k (χ q) q f i) (GlobalTheory.EisM.To k (χ q) q g i)
    unfold GlobalTheory.EisM.To GlobalTheory.EisM.Vo
    refine cgp_add (h _) (cgp_mul ?_ ?_)
    · rw [norm_mul, norm_pow]
      exact mul_le_one₀ (hχ q) (by positivity)
        (pow_le_one₀ (norm_nonneg _) (IsUltrametricDist.norm_natCast_le_one _ _))
    · split_ifs
      · exact h _
      · exact cgp_refl _ _
  | U => exact h _
  | D d => exact cgp_mul (hχ d) (h i)

/- English proof (translation)
Introduce `hOp hStab l _ Ω _ _ _ ε X A N w j χ hS P hP`. Use `set F := FreeAlgebra.lift (Qbar l) (fop (w + 2) l fun d => ((χ d : ℤ_[l]) : Qbar l)) with hF`. Use `set G := FreeAlgebra.lift (Qbar l) (X.opV N l (Qbar l)) with hG`. Establish `hχ : ∀ d, ‖((χ d : ℤ_[l]) : Qbar l)‖ ≤ 1` using `fun d => by`. Rewrite using `[norm_algebraMap']`.

Conclude with `(χ d).2`. Establish `hw : ∀ x ∈ Submonoid.closure (FreeAlgebra.ι (Qbar l) '' {T | GlobalTheory.KZ.admitted N l T}), ∀ n : ℕ, (∀ f g : ℕ → Qbar l, (∀ i, Cg n (f i) (g i)) → ∀ i, Cg n (F x f i) (F x g i)) ∧ ∀ b, InChi X N w χ b → ∃ b', InChi X N w χ b' ∧ G x ((1 : Qbar l) ⊗ₜ[ℤ_[l]] b) = (1 : Qbar l) ⊗ₜ …`. Introduce `x hx n`. Proceed by induction on `hx using Submonoid.closure_induction with`. Consider the case `mem x hx`.

Take `⟨T, hT, rfl⟩` from `hx`. Rewrite using `[hF, hG, FreeAlgebra.lift_ι_apply, FreeAlgebra.lift_ι_apply]`. Use `⟨fun f g h i => fop_cg hχ T h i, fun b hb => ⟨X.op N l T b, hStab l Ω ε X N w χ hS.2.1 hS.2.2.1 hS.2.2.2.1 hS.2.2.2.2.1 T b hT hb, ?_, fun i => cgp_symm (hOp l Ω ε X A N w j χ hS n T b hT hb i)⟩⟩` and prove the remaining obligations. Rewrite using `[Tower.opV, LinearMap.baseChange_tmul]`. Consider the case `one`.

Rewrite using `[map_one, map_one]`. Conclude with `⟨fun f g h i => h i, fun b hb => ⟨b, hb, rfl, fun i => cgp_refl _ _⟩⟩`. Consider the case `mul x y _ _ hx hy`. Rewrite using `[map_mul, map_mul]`. Use `⟨fun f g h i => hx.1 _ _ (hy.1 f g h) i, fun b hb => ?_⟩` and prove the remaining obligations.

Take `⟨b', hb', e', c'⟩` from `hy.2 b hb`. Take `⟨b'', hb'', e'', c''⟩` from `hx.2 b' hb'`. Use `⟨b'', hb'', ?_, fun i => cgp_trans (hx.1 _ _ c' i) (c'' i)⟩` and prove the remaining obligations. Rewrite using `[Module.End.mul_apply, e', e'']`. Establish `hP' : P ∈ Submodule.span (Qbar l) (Submonoid.closure (FreeAlgebra.ι (Qbar l) '' {T | GlobalTheory.KZ.admitted N l T}) : Set (FreeAlgebra (Qbar l) Letter))`.

Rewrite using `[← Algebra.adjoin_eq_span]`. Conclude with `hP`. Use `clear hP`. Proceed by induction on `hP' using Submodule.span_induction with`. Consider the case `mem x hx`.

Use `⟨0, fun n _ Θ hΘ b hb i => ?_⟩` and prove the remaining obligations. Take `⟨b', hb', e', c'⟩` from `(hw x hx n).2 b hb`. Rewrite using `[e', Nat.sub_zero]`. Conclude with `cgp_trans (c' i) (cgp_symm (hΘ b' hb'.1 i))`. Consider the case `zero`.

Use `⟨0, fun n _ Θ hΘ b hb i => ?_⟩` and prove the remaining obligations. Simplify using `only [map_zero, LinearMap.zero_apply]`. Conclude with `cgp_refl _ _`. Consider the case `add x y _ _ hx hy`. Take `⟨c, hc⟩` from `hx`.

Take `⟨d, hd⟩` from `hy`. Use `⟨c + d, fun n hn Θ hΘ b hb i => ?_⟩` and prove the remaining obligations. Simplify using `only [map_add, LinearMap.add_apply, Pi.add_apply]`. Conclude with `cgp_add (cg_mono (by omega) (hc n (by omega) Θ hΘ b hb i)) (cg_mono (by omega) (hd n (by omega) Θ hΘ b hb i))`. Consider the case `smul a x _ hx`.

Take `⟨c, hc⟩` from `hx`. Take `⟨k, hk⟩` from `exists_le_l_pow l ‖a‖`. Use `⟨c + k, fun n hn Θ hΘ b hb i => ?_⟩` and prove the remaining obligations. Simplify using `only [map_smul, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul]`. Rewrite using `[← Nat.sub_sub]`.

Conclude with `cg_mul_left (by omega) hk (hc n (by omega) Θ hΘ b hb i)`.
-/
theorem thP : ThP := by
  intro hOp hStab l _ Ω _ _ _ ε X A N w j χ hS P hP
  set F := FreeAlgebra.lift (Qbar l) (fop (w + 2) l fun d => ((χ d : ℤ_[l]) : Qbar l)) with hF
  set G := FreeAlgebra.lift (Qbar l) (X.opV N l (Qbar l)) with hG
  have hχ : ∀ d, ‖((χ d : ℤ_[l]) : Qbar l)‖ ≤ 1 := fun d => by
    rw [norm_algebraMap']
    exact (χ d).2
  have hw : ∀ x ∈ Submonoid.closure (FreeAlgebra.ι (Qbar l) '' {T | GlobalTheory.KZ.admitted N l T}), ∀ n : ℕ,
      (∀ f g : ℕ → Qbar l, (∀ i, Cg n (f i) (g i)) → ∀ i, Cg n (F x f i) (F x g i)) ∧
      ∀ b, InChi X N w χ b → ∃ b', InChi X N w χ b' ∧
        G x ((1 : Qbar l) ⊗ₜ[ℤ_[l]] b) = (1 : Qbar l) ⊗ₜ[ℤ_[l]] b' ∧
        ∀ i, Cg n (F x (th X A N j n b) i) (th X A N j n b' i) := by
    intro x hx n
    induction hx using Submonoid.closure_induction with
    | mem x hx =>
      obtain ⟨T, hT, rfl⟩ := hx
      rw [hF, hG, FreeAlgebra.lift_ι_apply, FreeAlgebra.lift_ι_apply]
      refine ⟨fun f g h i => fop_cg hχ T h i, fun b hb => ⟨X.op N l T b,
        hStab l Ω ε X N w χ hS.2.1 hS.2.2.1 hS.2.2.2.1 hS.2.2.2.2.1 T b hT hb, ?_,
        fun i => cgp_symm (hOp l Ω ε X A N w j χ hS n T b hT hb i)⟩⟩
      rw [Tower.opV, LinearMap.baseChange_tmul]
    | one =>
      rw [map_one, map_one]
      exact ⟨fun f g h i => h i, fun b hb => ⟨b, hb, rfl, fun i => cgp_refl _ _⟩⟩
    | mul x y _ _ hx hy =>
      rw [map_mul, map_mul]
      refine ⟨fun f g h i => hx.1 _ _ (hy.1 f g h) i, fun b hb => ?_⟩
      obtain ⟨b', hb', e', c'⟩ := hy.2 b hb
      obtain ⟨b'', hb'', e'', c''⟩ := hx.2 b' hb'
      refine ⟨b'', hb'', ?_, fun i => cgp_trans (hx.1 _ _ c' i) (c'' i)⟩
      rw [Module.End.mul_apply, e', e'']
  have hP' : P ∈ Submodule.span (Qbar l)
      (Submonoid.closure (FreeAlgebra.ι (Qbar l) '' {T | GlobalTheory.KZ.admitted N l T}) : Set (FreeAlgebra (Qbar l) Letter)) := by
    rw [← Algebra.adjoin_eq_span]
    exact hP
  clear hP
  induction hP' using Submodule.span_induction with
  | mem x hx =>
    refine ⟨0, fun n _ Θ hΘ b hb i => ?_⟩
    obtain ⟨b', hb', e', c'⟩ := (hw x hx n).2 b hb
    rw [e', Nat.sub_zero]
    exact cgp_trans (c' i) (cgp_symm (hΘ b' hb'.1 i))
  | zero =>
    refine ⟨0, fun n _ Θ hΘ b hb i => ?_⟩
    simp only [map_zero, LinearMap.zero_apply]
    exact cgp_refl _ _
  | add x y _ _ hx hy =>
    obtain ⟨c, hc⟩ := hx
    obtain ⟨d, hd⟩ := hy
    refine ⟨c + d, fun n hn Θ hΘ b hb i => ?_⟩
    simp only [map_add, LinearMap.add_apply, Pi.add_apply]
    exact cgp_add (cg_mono (by omega) (hc n (by omega) Θ hΘ b hb i))
      (cg_mono (by omega) (hd n (by omega) Θ hΘ b hb i))
  | smul a x _ hx =>
    obtain ⟨c, hc⟩ := hx
    obtain ⟨k, hk⟩ := exists_le_l_pow l ‖a‖
    refine ⟨c + k, fun n hn Θ hΘ b hb i => ?_⟩
    simp only [map_smul, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul]
    rw [← Nat.sub_sub]
    exact cg_mul_left (by omega) hk (hc n (by omega) Θ hΘ b hb i)

end UpperTheory.V.Z.Kato.Joint

end
