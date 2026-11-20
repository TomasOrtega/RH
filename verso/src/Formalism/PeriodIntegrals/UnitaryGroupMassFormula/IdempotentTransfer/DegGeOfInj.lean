import Mathlib
import Formalism.HarderNarasimhan.FinalCor

noncomputable section

namespace PI.Dv.Tr

open Formalism.HN

section Dense

variable {ι : Type} [Fintype ι] {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/- English proof (translation)
Establish `hq : ∀ q : ι → ℚ, ‖∑ i, ((q i : ℝ)) • w i‖ ≤ C * ‖∑ i, ((q i : ℝ)) • v i‖`. Introduce `q`. Use `set N : ℕ := ∏ i, (q i).den with hN`. Establish `hNpos : (0 : ℝ) < N`. Rewrite using `[hN]`.

Conclude with `Finset.prod_pos fun i _ => (q i).den_pos` after adjusting the coercions. Establish `hint : ∀ i, ∃ a : ℤ, (a : ℝ) = (N : ℝ) * (q i : ℝ)`. Introduce `i`. Take `⟨k, hk⟩ : (q i).den ∣ N` from `Finset.dvd_prod_of_mem _ (Finset.mem_univ i)`. Use `⟨(q i).num * k, ?_⟩` and prove the remaining obligations.

Establish `h1` using `Rat.mul_den_eq_num (q i)`. Establish `h2 : ((N : ℚ) * q i) = (((q i).num * k : ℤ) : ℚ)`. Rewrite using `[hk]`. Use `push_cast`. Rewrite using `[show ((q i).den : ℚ) * (k : ℚ) * q i = (q i * (q i).den) * k by ring, h1]`.

Establish `h3 : (((N : ℚ) * q i : ℚ) : ℝ) = ((((q i).num * k : ℤ) : ℚ) : ℝ)` using `by rw [h2]`. Move the coercions through the operations in `at h3`. Rewrite using `[h3]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Use `choose a ha using hint`. Establish `hw : ∑ i, (a i : ℝ) • w i = (N : ℝ) • ∑ i, (q i : ℝ) • w i`. Rewrite using `[Finset.smul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[ha i, mul_smul]`.

Establish `hv : ∑ i, (a i : ℝ) • v i = (N : ℝ) • ∑ i, (q i : ℝ) • v i`. Rewrite using `[Finset.smul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[ha i, mul_smul]`. Use `h a` as an intermediate fact.

Rewrite `this` using `[hw, hv, norm_smul, norm_smul, Real.norm_of_nonneg hNpos.le]`. Establish `h' : (N : ℝ) * ‖∑ i, (q i : ℝ) • w i‖ ≤ (N : ℝ) * (C * ‖∑ i, (q i : ℝ) • v i‖)`. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `le_of_mul_le_mul_left h' hNpos`. Establish `hd : DenseRange (Pi.map fun _ : ι => (Rat.cast : ℚ → ℝ))` using `DenseRange.piMap fun _ => Rat.denseRange_cast`.

Establish `hcl : IsClosed {c : ι → ℝ | ‖∑ i, c i • w i‖ ≤ C * ‖∑ i, c i • v i‖}` using `isClosed_le (by fun_prop) (by fun_prop)`. Introduce `c`. Establish `hc : c ∈ closure (Set.range (Pi.map fun _ : ι => (Rat.cast : ℚ → ℝ)))`. Rewrite using `[hd.closure_range]`. Discharge the goal by the elementary cases of `trivial`.

Conclude with `(closure_minimal (by rintro _ ⟨q, rfl⟩; exact hq q) hcl) hc`.
-/
lemma real_ext (v : ι → E) (w : ι → F) (C : ℝ)
    (h : ∀ a : ι → ℤ, ‖∑ i, (a i : ℝ) • w i‖ ≤ C * ‖∑ i, (a i : ℝ) • v i‖) :
    ∀ c : ι → ℝ, ‖∑ i, c i • w i‖ ≤ C * ‖∑ i, c i • v i‖ := by
  classical
  have hq : ∀ q : ι → ℚ, ‖∑ i, ((q i : ℝ)) • w i‖ ≤ C * ‖∑ i, ((q i : ℝ)) • v i‖ := by
    intro q
    set N : ℕ := ∏ i, (q i).den with hN
    have hNpos : (0 : ℝ) < N := by
      rw [hN]
      exact_mod_cast Finset.prod_pos fun i _ => (q i).den_pos
    have hint : ∀ i, ∃ a : ℤ, (a : ℝ) = (N : ℝ) * (q i : ℝ) := by
      intro i
      obtain ⟨k, hk⟩ : (q i).den ∣ N := Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
      refine ⟨(q i).num * k, ?_⟩
      have h1 := Rat.mul_den_eq_num (q i)
      have h2 : ((N : ℚ) * q i) = (((q i).num * k : ℤ) : ℚ) := by
        rw [hk]
        push_cast
        rw [show ((q i).den : ℚ) * (k : ℚ) * q i = (q i * (q i).den) * k by ring, h1]
      have h3 : (((N : ℚ) * q i : ℚ) : ℝ) = ((((q i).num * k : ℤ) : ℚ) : ℝ) := by rw [h2]
      push_cast at h3
      rw [h3]
      push_cast
      ring
    choose a ha using hint
    have hw : ∑ i, (a i : ℝ) • w i = (N : ℝ) • ∑ i, (q i : ℝ) • w i := by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [ha i, mul_smul]
    have hv : ∑ i, (a i : ℝ) • v i = (N : ℝ) • ∑ i, (q i : ℝ) • v i := by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [ha i, mul_smul]
    have := h a
    rw [hw, hv, norm_smul, norm_smul, Real.norm_of_nonneg hNpos.le] at this
    have h' : (N : ℝ) * ‖∑ i, (q i : ℝ) • w i‖ ≤ (N : ℝ) * (C * ‖∑ i, (q i : ℝ) • v i‖) := by
      linarith
    exact le_of_mul_le_mul_left h' hNpos
  have hd : DenseRange (Pi.map fun _ : ι => (Rat.cast : ℚ → ℝ)) :=
    DenseRange.piMap fun _ => Rat.denseRange_cast
  have hcl : IsClosed {c : ι → ℝ | ‖∑ i, c i • w i‖ ≤ C * ‖∑ i, c i • v i‖} :=
    isClosed_le (by fun_prop) (by fun_prop)
  intro c
  have hc : c ∈ closure (Set.range (Pi.map fun _ : ι => (Rat.cast : ℚ → ℝ))) := by
    rw [hd.closure_range]
    trivial
  exact (closure_minimal (by rintro _ ⟨q, rfl⟩; exact hq q) hcl) hc

end Dense

section Inj

variable {R : Type} [Ring R] {V W : Type} [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
  {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/- English proof (translation)
The claim follows from `AddSubgroup.mem_map`.
-/
lemma mem_zl {ρ : V →+ E} {L : Submodule R V} {u : E} : u ∈ zl ρ L ↔ ∃ x ∈ L, ρ x = u :=
  AddSubgroup.mem_map

/- English proof (translation)
Use `hL.2` as an intermediate fact. Use `hM.2` as an intermediate fact. Use `set zL := zl ρ L with hzL`. Use `set zM := zl ρ' M with hzM`. Use `set n := Module.finrank ℤ zL with hn`.

Set `b` to `Module.finBasis ℤ zL`. Establish `hmemL : ∀ u : zL, ∃ x ∈ L, ρ x = (u : E)` using `fun u => mem_zl.mp u.2`. Use `choose x hxL hxe using fun i => hmemL (b i)`. Set `w : Fin n → F` to `fun i => ρ' (f (x i))`. Establish `hsumL : ∀ a : Fin n → ℤ, (∑ i, a i • x i) ∈ L` using `fun a => L.sum_mem fun i _ => L.toAddSubgroup.zsmul_mem (hxL i) (a i)`.

Establish `hw_comb : ∀ a : Fin n → ℤ, ∑ i, a i • w i = ρ' (f (∑ i, a i • x i))`. Introduce `a`. Simplify using `[w, map_sum, map_zsmul]`. Establish `hb_comb : ∀ a : Fin n → ℤ, ∑ i, a i • ((b i : zL) : E) = ρ (∑ i, a i • x i)`. Introduce `a`.

Simplify using `[map_sum, map_zsmul, hxe]`. Establish `hbound : ∀ a : Fin n → ℤ, ‖∑ i, (a i : ℝ) • w i‖ ≤ C * ‖∑ i, (a i : ℝ) • ((b i : zL) : E)‖`. Introduce `a`. Simplify using `only [Int.cast_smul_eq_zsmul]`. Rewrite using `[hw_comb, hb_comb]`.

Conclude with `hb _ (hsumL a)`. Establish `hreal` using `real_ext (fun i => ((b i : zL) : E)) w C hbound`. Establish `hgram` using `Formalism.F.gramDetLe E F (Fin n) (fun i => ((b i : zL) : E)) w C hreal`. Establish `hli : LinearIndependent ℤ w`. Rewrite using `[Fintype.linearIndependent_iff]`.

Introduce `a ha`. Rewrite `ha` using `[hw_comb]`. Establish `hy` using `hsumL a`. Establish `h1 : f (∑ i, a i • x i) = 0` using `hM.1 (hfM _ hy) M.zero_mem (by rw [ha, map_zero])`. Establish `h2` using `hinj _ hy h1`.

Establish `h3 : ∑ i, a i • b i = 0`. Apply `Subtype.ext` to reduce the goal to its premises. Establish `: ((∑ i, a i • b i : zL) : E) = ∑ i, a i • ((b i : zL) : E)` using `by simp`. Rewrite using `[this, hb_comb, h2, map_zero]`. Both sides reduce to the same expression.

Conclude with `(Fintype.linearIndependent_iff.mp b.linearIndependent) a h3`. Use `set N' : Submodule ℤ F := Submodule.span ℤ (Set.range w) with hN'`. Establish `hN'M : N' ≤ zM`. Rewrite using `[hN', Submodule.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`.

Conclude with `mem_zl.mpr ⟨f (x i), hfM _ (hxL i), rfl⟩`. Establish `hdisc : DiscreteTopology N'` using `DiscreteTopology.of_continuous_injective (f := Submodule.inclusion hN'M) (continuous_subtype_val.subtype_mk _) (Submodule.inclusion_injective _)`. Set `bN : Module.Basis (Fin n) ℤ N'` to `Module.Basis.span hli`. Establish `hbN : ∀ i, ((bN i : N') : F) = w i` using `fun i => by first`. Consider the case `exact Module.Basis.span_apply hli i`.

Consider the case `exact congrArg Subtype.val (Module.Basis.span_apply hli i)`. Consider the case `simp [bN]`. Establish `hcovN'` using `Formalism.F.covolEqGram F N' (Fin n) bN`. Establish `hcovL` using `Formalism.F.covolEqGram E zL (Fin n) b`. Establish `hrkN' : Formalism.F.rk N' = Formalism.F.rk zM`.

Establish `h1 : Formalism.F.rk N' = n`. Unfold `Formalism.F.rk`. Rewrite using `[Module.finrank_eq_card_basis bN, Fintype.card_fin]`. Rewrite using `[h1]`. Conclude with `hrk`.

Establish `hanti` using `Formalism.F.covolAntiSameRank F N' zM hM.2 hN'M hrkN'`. Establish `hposM` using `Formalism.F.covolPos F zM hM.2`. Establish `hposL` using `Formalism.F.covolPos E zL hL.2`. Establish `hbNeq : (fun i => ((bN i : N') : F)) = w` using `funext hbN`. Rewrite `hcovN'` using `[hbNeq]`.

Establish `hGb : 0 ≤ (Matrix.gram ℝ (fun i => ((b i : zL) : E))).det`. Assume the negation of the conclusion as `hneg`. Use `push Not at hneg`. Rewrite `hposL` using `[hcovL, Real.sqrt_eq_zero'.mpr hneg.le]`. Conclude with `lt_irrefl _ hposL`.

Establish `hle : Formalism.F.covol N' ≤ C ^ n * Formalism.F.covol zL`. Rewrite using `[hcovN', hcovL]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Real.sqrt_mul (by positivity), Fintype.card_fin, pow_mul, ← pow_mul, mul_comm 2 n, pow_mul, Real.sqrt_sq (by positivity)]`. Establish `hfin : Formalism.F.covol zM ≤ C ^ n * Formalism.F.covol zL` using `hanti.trans hle`.

Establish `hlog` using `Real.log_le_log hposM hfin`. Rewrite `hlog` using `[Real.log_mul (by positivity) hposL.ne', Real.log_pow]`. Unfold `deg rk Formalism.F.deg Formalism.F.rk`. Rewrite using `[← hzL, ← hzM, ← hn]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem deg_ge_of_inj (ρ : V →+ E) (ρ' : W →+ F) (L : Submodule R V) (M : Submodule R W)
    (hL : IsLat ρ L) (hM : IsLat ρ' M) (f : V →+ W) (hfM : ∀ x ∈ L, f x ∈ M)
    (hinj : ∀ x ∈ L, f x = 0 → x = 0) (hrk : rk ρ L = rk ρ' M) (C : ℝ) (hC : 0 < C)
    (hb : ∀ x ∈ L, ‖ρ' (f x)‖ ≤ C * ‖ρ x‖) :
    deg ρ L - (rk ρ L : ℝ) * Real.log C ≤ deg ρ' M := by
  classical
  have := hL.2
  have := hM.2
  set zL := zl ρ L with hzL
  set zM := zl ρ' M with hzM
  set n := Module.finrank ℤ zL with hn
  let b := Module.finBasis ℤ zL
  have hmemL : ∀ u : zL, ∃ x ∈ L, ρ x = (u : E) := fun u => mem_zl.mp u.2
  choose x hxL hxe using fun i => hmemL (b i)
  let w : Fin n → F := fun i => ρ' (f (x i))
  have hsumL : ∀ a : Fin n → ℤ, (∑ i, a i • x i) ∈ L := fun a =>
    L.sum_mem fun i _ => L.toAddSubgroup.zsmul_mem (hxL i) (a i)
  have hw_comb : ∀ a : Fin n → ℤ, ∑ i, a i • w i = ρ' (f (∑ i, a i • x i)) := by
    intro a
    simp [w, map_sum, map_zsmul]
  have hb_comb : ∀ a : Fin n → ℤ, ∑ i, a i • ((b i : zL) : E) = ρ (∑ i, a i • x i) := by
    intro a
    simp [map_sum, map_zsmul, hxe]
  have hbound : ∀ a : Fin n → ℤ, ‖∑ i, (a i : ℝ) • w i‖ ≤ C * ‖∑ i, (a i : ℝ) • ((b i : zL) : E)‖ := by
    intro a
    simp only [Int.cast_smul_eq_zsmul]
    rw [hw_comb, hb_comb]
    exact hb _ (hsumL a)
  have hreal := real_ext (fun i => ((b i : zL) : E)) w C hbound
  have hgram := Formalism.F.gramDetLe E F (Fin n) (fun i => ((b i : zL) : E)) w C hreal
  have hli : LinearIndependent ℤ w := by
    rw [Fintype.linearIndependent_iff]
    intro a ha
    rw [hw_comb] at ha
    have hy := hsumL a
    have h1 : f (∑ i, a i • x i) = 0 := hM.1 (hfM _ hy) M.zero_mem (by rw [ha, map_zero])
    have h2 := hinj _ hy h1
    have h3 : ∑ i, a i • b i = 0 := by
      apply Subtype.ext
      have : ((∑ i, a i • b i : zL) : E) = ∑ i, a i • ((b i : zL) : E) := by simp
      rw [this, hb_comb, h2, map_zero]
      rfl
    exact (Fintype.linearIndependent_iff.mp b.linearIndependent) a h3
  set N' : Submodule ℤ F := Submodule.span ℤ (Set.range w) with hN'
  have hN'M : N' ≤ zM := by
    rw [hN', Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact mem_zl.mpr ⟨f (x i), hfM _ (hxL i), rfl⟩
  have hdisc : DiscreteTopology N' :=
    DiscreteTopology.of_continuous_injective (f := Submodule.inclusion hN'M)
      (continuous_subtype_val.subtype_mk _) (Submodule.inclusion_injective _)
  let bN : Module.Basis (Fin n) ℤ N' := Module.Basis.span hli
  have hbN : ∀ i, ((bN i : N') : F) = w i := fun i => by
    first
    | exact Module.Basis.span_apply hli i
    | exact congrArg Subtype.val (Module.Basis.span_apply hli i)
    | simp [bN]
  have hcovN' := Formalism.F.covolEqGram F N' (Fin n) bN
  have hcovL := Formalism.F.covolEqGram E zL (Fin n) b
  have hrkN' : Formalism.F.rk N' = Formalism.F.rk zM := by
    have h1 : Formalism.F.rk N' = n := by
      unfold Formalism.F.rk
      rw [Module.finrank_eq_card_basis bN, Fintype.card_fin]
    rw [h1]
    exact hrk
  have hanti := Formalism.F.covolAntiSameRank F N' zM hM.2 hN'M hrkN'
  have hposM := Formalism.F.covolPos F zM hM.2
  have hposL := Formalism.F.covolPos E zL hL.2
  have hbNeq : (fun i => ((bN i : N') : F)) = w := funext hbN
  rw [hbNeq] at hcovN'
  have hGb : 0 ≤ (Matrix.gram ℝ (fun i => ((b i : zL) : E))).det := by
    by_contra hneg
    push Not at hneg
    rw [hcovL, Real.sqrt_eq_zero'.mpr hneg.le] at hposL
    exact lt_irrefl _ hposL
  have hle : Formalism.F.covol N' ≤ C ^ n * Formalism.F.covol zL := by
    rw [hcovN', hcovL]
    calc Real.sqrt (Matrix.gram ℝ w).det
        ≤ Real.sqrt (C ^ (2 * Fintype.card (Fin n)) * (Matrix.gram ℝ (fun i => ((b i : zL) : E))).det) :=
          Real.sqrt_le_sqrt hgram
      _ = C ^ n * Real.sqrt (Matrix.gram ℝ (fun i => ((b i : zL) : E))).det := by
          rw [Real.sqrt_mul (by positivity), Fintype.card_fin, pow_mul, ← pow_mul, mul_comm 2 n, pow_mul,
            Real.sqrt_sq (by positivity)]
  have hfin : Formalism.F.covol zM ≤ C ^ n * Formalism.F.covol zL := hanti.trans hle
  have hlog := Real.log_le_log hposM hfin
  rw [Real.log_mul (by positivity) hposL.ne', Real.log_pow] at hlog
  unfold deg rk Formalism.F.deg Formalism.F.rk
  rw [← hzL, ← hzM, ← hn]
  linarith

end Inj

end PI.Dv.Tr
