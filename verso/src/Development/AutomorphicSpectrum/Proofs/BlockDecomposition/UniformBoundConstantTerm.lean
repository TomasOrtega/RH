import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.AllLeaves
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.ConstantTermSteps.UnipGLMemAdelicBorel
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UfamConst
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LinearRecurrenceGrowthBoundStatement

noncomputable section

open scoped ENNReal
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.Conc
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm
open PositivityTheory.Rg.Rs.An PositivityTheory.Rg.Rs.ctstepglue

namespace GlobalTheory.CompanionTheory.Conc

/- English proof (translation)
Introduce `ω hω hωB t₀ Q hQ`. Take `⟨D, hD, hFD⟩` from `exists_isCompact_superset_unipFundamentalDomain (K := K) (n := n) (r := r)`. Use `set ω' := (fun p : (UPos n r → NumberField.AdeleRing (𝓞 K) K) × AdelicGLn.AdelicGL K n => unipGL p.1 * p.2) '' (D ×ˢ ω)`. Establish `hω' : IsCompact ω'` using `(hD.prod hω).image ((continuous_unipGL.comp continuous_fst).mul continuous_snd)`. Establish `hω'B : ω' ⊆ (adelicBorel (K` using `K) (n := n) : Set _) := by`.

Introduce and unpack `_ ⟨⟨X, b⟩, ⟨hX, hb⟩, rfl⟩`. Conclude with `mul_mem (unipGL_mem_adelicBorel r X) (hωB hb)`. Take `⟨C, hC⟩` from `h ω' hω' hω'B t₀ Q hQ`. Use `⟨max C 0, fun i b hb x hx q hq => ?_⟩` and prove the remaining obligations. Use `norm_ctn_le (f i) hD hFD _ (by positivity) fun X hX => ?_` and prove the remaining obligations.

Use `hC i (unipGL X * b) ⟨(X, b), ⟨hX, hb⟩, rfl⟩ x hx q hq` as an intermediate fact. Rewrite using `[← mul_assoc, ← mul_assoc]`. Conclude with `this.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)`.
-/
theorem ubnd_ctn {K : Type} [Field K] [NumberField K] {n : ℕ} {ι : Type}
    {r : ℕ} {f : ι → AdelicGLn.AdelicGL K n → ℂ} {m : ℕ → ℝ} (h : UBnd f m) :
    UBnd (fun i => An.ctn r (f i)) m := by
  intro ω hω hωB t₀ Q hQ
  obtain ⟨D, hD, hFD⟩ := exists_isCompact_superset_unipFundamentalDomain (K := K) (n := n) (r := r)
  set ω' := (fun p : (UPos n r → NumberField.AdeleRing (𝓞 K) K) × AdelicGLn.AdelicGL K n => unipGL p.1 * p.2) '' (D ×ˢ ω)
  have hω' : IsCompact ω' :=
    (hD.prod hω).image ((continuous_unipGL.comp continuous_fst).mul continuous_snd)
  have hω'B : ω' ⊆ (adelicBorel (K := K) (n := n) : Set _) := by
    rintro _ ⟨⟨X, b⟩, ⟨hX, hb⟩, rfl⟩
    exact mul_mem (unipGL_mem_adelicBorel r X) (hωB hb)
  obtain ⟨C, hC⟩ := h ω' hω' hω'B t₀ Q hQ
  refine ⟨max C 0, fun i b hb x hx q hq => ?_⟩
  refine norm_ctn_le (f i) hD hFD _ (by positivity) fun X hX => ?_
  have := hC i (unipGL X * b) ⟨(X, b), ⟨hX, hb⟩, rfl⟩ x hx q hq
  rw [← mul_assoc, ← mul_assoc]
  exact this.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)

/- English proof (translation)
Introduce `K _ _ n ι f m r D κ' κ pf hr hrn hf hB hκ hpf ω hω hωB t₀ Q hQ`. Take `⟨C₁, hC₁⟩` from `ubnd_ctn (r := r) hB ω hω hωB t₀ Q hQ`. Take `⟨C₂, hC₂0, hC₂⟩` from `GlobalTheory.T.linear_recurrence_growth_bound D κ' κ hκ`. Use `set E : ℝ := Real.exp (|m r| * (|t₀| + 1 + D)) with hE`. Use `⟨C₂ * (max C₁ 0 * E) * Real.exp (|κ| * (|t₀| + 1)), ?_⟩` and prove the remaining obligations.

Introduce `a b hb x hx q hq`. Take `⟨hp, hdD, hK, hroot⟩` from `hpf a`. Use `set p := pf a with hpdef`. Use `set φ := f a with hφdef`. Use `set d := p.natDegree with hd`.

Use `set S : ℝ := ∑ r' ∈ (Finset.range n).erase r, m r' * sr x r' with hS`. Establish `hrmem : r ∈ Finset.range n` using `Finset.mem_range.2 hrn`. Establish `hsum : ∀ (f : ℕ → ℝ) (y : Fin n → ℝ), (∀ r' ≠ r, f r' = m r') → (∀ r' ≠ r, sr y r' = sr x r') → ∑ r' ∈ Finset.range n, f r' * sr y r' = f r * sr y r + S`. Introduce `f y hf hy`. Rewrite using `[← Finset.add_sum_erase _ _ hrmem, hS]`.

Use `congr 1`. Use `Finset.sum_congr rfl fun r' h' => ?_` and prove the remaining obligations. Rewrite using `[hf r' (Finset.ne_of_mem_erase h'), hy r' (Finset.ne_of_mem_erase h')]`. Establish `h0 : 0 ≤ sr x r + t₀` using `by linarith [hx r]`. Use `set i : ℕ := ⌊sr x r + t₀⌋₊ with hi`.

Establish `hi1 : (i : ℝ) ≤ sr x r + t₀` using `Nat.floor_le h0`. Establish `hi2 : sr x r + t₀ < i + 1` using `Nat.lt_floor_add_one _`. Use `set x' : Fin n → ℝ := shift r x (-(i : ℝ)) with hx'`. Use `set g₀ : AdelicGLn.AdelicGL K n := b * tor K x' * q with hg₀`. Use `set u : ℕ → ℂ := fun k => ctn r φ (aR K n r k * g₀) with hu`.

Establish `hrecu : ∀ k, ∑ j ∈ Finset.range (d + 1), p.coeff j * u (k + j) = 0`. Introduce `k`. Use `hK (aR K n r k * g₀)` as an intermediate fact. Rewrite using `[← this]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Simplify using `only [hu, ← mul_assoc, aR_mul]`. Use `congr 4`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hmove : ∀ (t : ℝ) (h : AdelicGLn.AdelicGL K n), ctn r φ (aR K n r t * (b * h)) = ctn r φ (b * (aR K n r t * h))`.

Introduce `t h`. Take `⟨X, hX⟩` from `borel_aR (r := r) (hωB hb) t`. Establish `: aR K n r t * b = unipGL (-X) * (b * aR K n r t)`. Rewrite using `[hX, ← mul_assoc, ← unipGL_add, neg_add_cancel, unipGL_zero, one_mul]`. Rewrite using `[← mul_assoc, this, mul_assoc, ctn_unipGL_mul (hf.left a), ← mul_assoc]`.

Use `set M : ℝ := max C₁ 0 * E * Real.exp S with hM`. Establish `hM0 : 0 ≤ M` using `by positivity`. Establish `hinit : ∀ j < d, ‖u j‖ ≤ M`. Introduce `j hj`. Establish `e1 : u j = ctn r φ (b * tor K (shift r x ((j : ℝ) - i)) * q)`.

Simplify using `only [hu, hg₀, mul_assoc]`. Rewrite using `[hmove, ← mul_assoc (aR K n r j), ← tor_shift, hx', show shift r (shift r x (-(i : ℝ))) (j : ℝ) = shift r x ((j : ℝ) - i) from by`. Apply the tactic sequence `funext l; simp only [shift]; split_ifs <;> ring]`. Establish `hsr : ∀ r', sr (shift r x ((j : ℝ) - i)) r' = sr x r' + if r' = r then (j : ℝ) - i else 0` using `sr_shift hr hrn x _`. Establish `hx2 : ∀ r', -t₀ ≤ sr (shift r x ((j : ℝ) - i)) r'`.

Introduce `r'`. Rewrite using `[hsr]`. Use `split_ifs with h`. Substitute `h` using the available equality. Establish `: (0 : ℝ) ≤ j` using `Nat.cast_nonneg j`.

Combine the linear equalities and inequalities to obtain the conclusion. Simplify using `using hx r'`. Establish `hb1` using `hC₁ a b hb _ hx2 q hq`. Rewrite using `[e1]`. Use `hb1.trans ?_` and prove the remaining obligations.

Rewrite using `[hsum m _ (fun _ _ => rfl) (fun r' h => by rw [hsr, if_neg h, add_zero]), hsr, if_pos rfl, Real.exp_add, hM, ← mul_assoc]`. Establish `hjd : (j : ℝ) ≤ D` using `by exact_mod_cast (hj.le.trans hdD)`. Establish `hv : |sr x r + ((j : ℝ) - i)| ≤ |t₀| + 1 + D`. Apply the tactic sequence `rw [abs_le]; constructor <;> cases abs_cases t₀ <;> linarith`. Establish `hexp : Real.exp (m r * (sr x r + ((j : ℝ) - i))) ≤ E`.

Rewrite using `[hE]`. Apply `Real.exp_le_exp.2` to reduce the goal to its premises. Combine the equalities or inequalities in the displayed calculation. Establish `hC : C₁ ≤ max C₁ 0` using `le_max_left _ _`. Use `gcongr`.

Establish `hmain` using `hC₂ p hp hdD hroot u M hrecu hinit hM0 i`. Establish `heq : ctn r φ (b * tor K x * q) = u i`. Establish `: x = shift r x' (i : ℝ)`. Apply the tactic sequence `funext l; simp only [hx', shift]; split_ifs <;> ring`. Simplify using `only [hu, hg₀]`.

Use `conv_lhs => rw [this, tor_shift]`. Rewrite using `[mul_assoc b (tor K x') q, hmove]`. Simplify using `only [mul_assoc]`. Use `show ‖ctn r φ (b * tor K x * q)‖ ≤ _`. Rewrite using `[heq]`.

Use `hmain.trans ?_` and prove the remaining obligations. Rewrite using `[hsum (Function.update m r κ) x (fun r' h => Function.update_of_ne h _ _) (fun _ _ => rfl), Function.update_self, Real.exp_add, hM]`. Establish `hk : Real.exp (κ * i) ≤ Real.exp (κ * sr x r) * Real.exp (|κ| * (|t₀| + 1))`. Rewrite using `[← Real.exp_add]`. Apply `Real.exp_le_exp.2` to reduce the goal to its premises.

Establish `: |(i : ℝ) - sr x r| ≤ |t₀| + 1`. Apply the tactic sequence `rw [abs_le]; constructor <;> cases abs_cases t₀ <;> linarith`. Use `mul_le_mul_of_nonneg_left this (abs_nonneg κ)` as an intermediate fact. Establish `h2 : κ * ((i : ℝ) - sr x r) ≤ |κ| * |(i : ℝ) - sr x r|`. Rewrite using `[← abs_mul]`.

Conclude with `le_abs_self _`. Use the polynomial consequences of the given equalities and inequalities. Establish `hE0 : 0 ≤ max C₁ 0 * E` using `by positivity`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem ubnd_ctn_step : ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (ι : Type) (f : ι → AdelicGLn.AdelicGL K n → ℂ) (m : ℕ → ℝ) (r D : ℕ) (κ' κ : ℝ) (p : ι → ℂ[X]),
  0 < r → r < n → UFam f → UBnd f m → κ' < κ →
  (∀ i, (p i).Monic ∧ (p i).natDegree ≤ D ∧ An.Kill r (f i) (p i) ∧ ∀ z, (p i).IsRoot z → ‖z‖ ≤ Real.exp κ') →
  UBnd (fun i => An.ctn r (f i)) (Function.update m r κ) := by
  intro K _ _ n ι f m r D κ' κ pf hr hrn hf hB hκ hpf ω hω hωB t₀ Q hQ
  obtain ⟨C₁, hC₁⟩ := ubnd_ctn (r := r) hB ω hω hωB t₀ Q hQ
  obtain ⟨C₂, hC₂0, hC₂⟩ := GlobalTheory.T.linear_recurrence_growth_bound D κ' κ hκ
  set E : ℝ := Real.exp (|m r| * (|t₀| + 1 + D)) with hE
  refine ⟨C₂ * (max C₁ 0 * E) * Real.exp (|κ| * (|t₀| + 1)), ?_⟩
  intro a b hb x hx q hq
  obtain ⟨hp, hdD, hK, hroot⟩ := hpf a
  set p := pf a with hpdef
  set φ := f a with hφdef
  set d := p.natDegree with hd
  set S : ℝ := ∑ r' ∈ (Finset.range n).erase r, m r' * sr x r' with hS
  have hrmem : r ∈ Finset.range n := Finset.mem_range.2 hrn
  have hsum : ∀ (f : ℕ → ℝ) (y : Fin n → ℝ), (∀ r' ≠ r, f r' = m r') → (∀ r' ≠ r, sr y r' = sr x r') →
      ∑ r' ∈ Finset.range n, f r' * sr y r' = f r * sr y r + S := by
    intro f y hf hy
    rw [← Finset.add_sum_erase _ _ hrmem, hS]
    congr 1
    refine Finset.sum_congr rfl fun r' h' => ?_
    rw [hf r' (Finset.ne_of_mem_erase h'), hy r' (Finset.ne_of_mem_erase h')]
  have h0 : 0 ≤ sr x r + t₀ := by linarith [hx r]
  set i : ℕ := ⌊sr x r + t₀⌋₊ with hi
  have hi1 : (i : ℝ) ≤ sr x r + t₀ := Nat.floor_le h0
  have hi2 : sr x r + t₀ < i + 1 := Nat.lt_floor_add_one _
  set x' : Fin n → ℝ := shift r x (-(i : ℝ)) with hx'
  set g₀ : AdelicGLn.AdelicGL K n := b * tor K x' * q with hg₀
  set u : ℕ → ℂ := fun k => ctn r φ (aR K n r k * g₀) with hu
  have hrecu : ∀ k, ∑ j ∈ Finset.range (d + 1), p.coeff j * u (k + j) = 0 := by
    intro k
    have := hK (aR K n r k * g₀)
    rw [← this]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [hu, ← mul_assoc, aR_mul]
    congr 4
    push_cast; ring

  have hmove : ∀ (t : ℝ) (h : AdelicGLn.AdelicGL K n), ctn r φ (aR K n r t * (b * h)) = ctn r φ (b * (aR K n r t * h)) := by
    intro t h
    obtain ⟨X, hX⟩ := borel_aR (r := r) (hωB hb) t
    have : aR K n r t * b = unipGL (-X) * (b * aR K n r t) := by
      rw [hX, ← mul_assoc, ← unipGL_add, neg_add_cancel, unipGL_zero, one_mul]
    rw [← mul_assoc, this, mul_assoc, ctn_unipGL_mul (hf.left a), ← mul_assoc]
  set M : ℝ := max C₁ 0 * E * Real.exp S with hM
  have hM0 : 0 ≤ M := by positivity
  have hinit : ∀ j < d, ‖u j‖ ≤ M := by
    intro j hj
    have e1 : u j = ctn r φ (b * tor K (shift r x ((j : ℝ) - i)) * q) := by
      simp only [hu, hg₀, mul_assoc]
      rw [hmove, ← mul_assoc (aR K n r j), ← tor_shift, hx',
        show shift r (shift r x (-(i : ℝ))) (j : ℝ) = shift r x ((j : ℝ) - i) from by
          funext l; simp only [shift]; split_ifs <;> ring]
    have hsr : ∀ r', sr (shift r x ((j : ℝ) - i)) r' = sr x r' + if r' = r then (j : ℝ) - i else 0 :=
      sr_shift hr hrn x _
    have hx2 : ∀ r', -t₀ ≤ sr (shift r x ((j : ℝ) - i)) r' := by
      intro r'
      rw [hsr]
      split_ifs with h
      · subst h; have : (0 : ℝ) ≤ j := Nat.cast_nonneg j; linarith
      · simpa using hx r'
    have hb1 := hC₁ a b hb _ hx2 q hq
    rw [e1]
    refine hb1.trans ?_
    rw [hsum m _ (fun _ _ => rfl) (fun r' h => by rw [hsr, if_neg h, add_zero]), hsr, if_pos rfl,
      Real.exp_add, hM, ← mul_assoc]
    have hjd : (j : ℝ) ≤ D := by exact_mod_cast (hj.le.trans hdD)
    have hv : |sr x r + ((j : ℝ) - i)| ≤ |t₀| + 1 + D := by
      rw [abs_le]; constructor <;> cases abs_cases t₀ <;> linarith
    have hexp : Real.exp (m r * (sr x r + ((j : ℝ) - i))) ≤ E := by
      rw [hE]; apply Real.exp_le_exp.2
      calc m r * (sr x r + ((j : ℝ) - i)) ≤ |m r * (sr x r + ((j : ℝ) - i))| := le_abs_self _
        _ = |m r| * |sr x r + ((j : ℝ) - i)| := abs_mul _ _
        _ ≤ |m r| * (|t₀| + 1 + D) := mul_le_mul_of_nonneg_left hv (abs_nonneg _)
    have hC : C₁ ≤ max C₁ 0 := le_max_left _ _
    gcongr
  have hmain := hC₂ p hp hdD hroot u M hrecu hinit hM0 i
  have heq : ctn r φ (b * tor K x * q) = u i := by
    have : x = shift r x' (i : ℝ) := by
      funext l; simp only [hx', shift]; split_ifs <;> ring
    simp only [hu, hg₀]
    conv_lhs => rw [this, tor_shift]
    rw [mul_assoc b (tor K x') q, hmove]
    simp only [mul_assoc]
  show ‖ctn r φ (b * tor K x * q)‖ ≤ _
  rw [heq]
  refine hmain.trans ?_
  rw [hsum (Function.update m r κ) x (fun r' h => Function.update_of_ne h _ _) (fun _ _ => rfl),
    Function.update_self, Real.exp_add, hM]
  have hk : Real.exp (κ * i) ≤ Real.exp (κ * sr x r) * Real.exp (|κ| * (|t₀| + 1)) := by
    rw [← Real.exp_add]; apply Real.exp_le_exp.2
    have : |(i : ℝ) - sr x r| ≤ |t₀| + 1 := by
      rw [abs_le]; constructor <;> cases abs_cases t₀ <;> linarith
    have := mul_le_mul_of_nonneg_left this (abs_nonneg κ)
    have h2 : κ * ((i : ℝ) - sr x r) ≤ |κ| * |(i : ℝ) - sr x r| := by
      rw [← abs_mul]; exact le_abs_self _
    nlinarith
  have hE0 : 0 ≤ max C₁ 0 * E := by positivity
  calc C₂ * Real.exp (κ * i) * (max C₁ 0 * E * Real.exp S)
      ≤ C₂ * (Real.exp (κ * sr x r) * Real.exp (|κ| * (|t₀| + 1))) * (max C₁ 0 * E * Real.exp S) := by
        gcongr
    _ = C₂ * (max C₁ 0 * E) * Real.exp (|κ| * (|t₀| + 1)) * (Real.exp (κ * sr x r) * Real.exp S) := by ring

end GlobalTheory.CompanionTheory.Conc

end
