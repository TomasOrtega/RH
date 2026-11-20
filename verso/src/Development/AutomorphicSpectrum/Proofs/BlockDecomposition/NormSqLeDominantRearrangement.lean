import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.DiracOfDiracZeroModule
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CliffordHighestWeightVector
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DiracKHolds

noncomputable section

open Matrix Finset
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.DiracKType0

open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount GlobalTheory.CompanionTheory.RealCount.InjHw GlobalTheory.CompanionTheory.DiracK

variable {n : ℕ}

/- English proof (translation)
Use `set s : Equiv.Perm (Fin n) := Tuple.sort (fun i => -a i) with hs`. Establish `hanti : Antitone (a ∘ s)`. Introduce `i j hij`. Use `Tuple.monotone_sort (fun i => -a i) hij` as an intermediate fact. Simplify `this` using `[Function.comp]`.

Establish `hρ : Antitone (rhoV n)`. Introduce `i j hij`. Simplify using `only [rhoV]`. Establish `: ((i : ℕ) : ℝ) ≤ (j : ℕ)` using `by exact_mod_cast hij`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hmv : Monovary (a ∘ s) (rhoV n)` using `hanti.monovary hρ`. Establish `hr` using `hmv.sum_mul_comp_perm_le_sum_mul (σ := s.trans π)`. Establish `e1 : ∑ i, a i ^ 2 = ∑ i, (a ∘ s) i ^ 2` using `(Equiv.sum_comp s (fun i => a i ^ 2)).symm`. Establish `e2 : ∑ i, rhoV n (π i) ^ 2 = ∑ i, rhoV n i ^ 2` using `Equiv.sum_comp π (fun i => rhoV n i ^ 2)`. Establish `e3 : ∑ i, a i * rhoV n (π i) = ∑ i, (a ∘ s) i * rhoV n ((s.trans π) i)` using `(Equiv.sum_comp s (fun i => a i * rhoV n (π i))).symm`.

Establish `l : Formalism.REAL.nsq (a + rhoV n ∘ π) = ∑ i, a i ^ 2 + 2 * ∑ i, a i * rhoV n (π i) + ∑ i, rhoV n (π i) ^ 2`. Simplify using `only [Formalism.REAL.nsq, Formalism.REAL.dot, Pi.add_apply, Function.comp, Finset.mul_sum, ← Finset.sum_add_distrib]`. Conclude with `Finset.sum_congr rfl fun i _ => by ring`. Establish `r : nsq (domC a + rhoV n) = ∑ i, (a ∘ s) i ^ 2 + 2 * ∑ i, (a ∘ s) i * rhoV n i + ∑ i, rhoV n i ^ 2`. Simplify using `only [nsq, domC, Pi.add_apply, Finset.mul_sum, ← Finset.sum_add_distrib]`.

Conclude with `Finset.sum_congr rfl fun i _ => by`. Simplify using `only [hs, Function.comp]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[l, r, e1, e2, e3]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem norm_sq_le_dominant_rearrangement (a : Fin n → ℝ) (π : Equiv.Perm (Fin n)) :
    Formalism.REAL.nsq (a + rhoV n ∘ π) ≤ nsq (domC a + rhoV n) := by
  set s : Equiv.Perm (Fin n) := Tuple.sort (fun i => -a i) with hs
  have hanti : Antitone (a ∘ s) := by
    intro i j hij
    have := Tuple.monotone_sort (fun i => -a i) hij
    simpa [Function.comp] using this
  have hρ : Antitone (rhoV n) := by
    intro i j hij
    simp only [rhoV]
    have : ((i : ℕ) : ℝ) ≤ (j : ℕ) := by exact_mod_cast hij
    linarith
  have hmv : Monovary (a ∘ s) (rhoV n) := hanti.monovary hρ
  have hr := hmv.sum_mul_comp_perm_le_sum_mul (σ := s.trans π)
  have e1 : ∑ i, a i ^ 2 = ∑ i, (a ∘ s) i ^ 2 := (Equiv.sum_comp s (fun i => a i ^ 2)).symm
  have e2 : ∑ i, rhoV n (π i) ^ 2 = ∑ i, rhoV n i ^ 2 := Equiv.sum_comp π (fun i => rhoV n i ^ 2)
  have e3 : ∑ i, a i * rhoV n (π i) = ∑ i, (a ∘ s) i * rhoV n ((s.trans π) i) :=
    (Equiv.sum_comp s (fun i => a i * rhoV n (π i))).symm
  have l : Formalism.REAL.nsq (a + rhoV n ∘ π) =
      ∑ i, a i ^ 2 + 2 * ∑ i, a i * rhoV n (π i) + ∑ i, rhoV n (π i) ^ 2 := by
    simp only [Formalism.REAL.nsq, Formalism.REAL.dot, Pi.add_apply, Function.comp, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have r : nsq (domC a + rhoV n) =
      ∑ i, (a ∘ s) i ^ 2 + 2 * ∑ i, (a ∘ s) i * rhoV n i + ∑ i, rhoV n i ^ 2 := by
    simp only [nsq, domC, Pi.add_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by
      simp only [hs, Function.comp]
      ring
  rw [l, r, e1, e2, e3]
  linarith

/- English proof (translation)
Introduce `n lam V _ _ E1 E2 σ h ι _ _ c hc τ x hx hK`. Take `⟨hc1, hc2⟩` from `hc`. Establish `hcl : IsCliff c` using `⟨hc1, hc2⟩`. Establish `hp` using `h.pair`. Use `set L := lft (V := V) ι with hL`.

Use `set Rr := rgt (ι := ι) V with hRr`. Use `set p : Fin n → Fin n → Module.End ℂ (ι → V) := fun a b => L (pF E1 E2 a b) with hpdef`. Use `set k : Fin n → Fin n → Module.End ℂ (ι → V) := fun a b => L (kF E1 E2 a b) with hkdef`. Use `set g : Fin n → Fin n → Module.End ℂ (ι → V) := fun a b => Rr (c a b) with hgdef`. Use `set s : Fin n → Fin n → Module.End ℂ (ι → V) := fun a b => Rr (spinM c a b) with hsdef`.

Use `set D := dirac (pF E1 E2) c with hD`. Establish `hDe : D = ∑ a, ∑ b, p a b * g b a` using `rfl`. Establish `hks : ∀ a b c' d, k a b * s c' d = s c' d * k a b` using `fun a b c' d => lft_mul_rgt _ _`. Establish `hglK : Formalism.REAL.GlRel (kF E1 E2)` using `glRel_add E1 E2 hp.gl1 hp.gl2 hp.comm`. Establish `hGk : Formalism.REAL.GlRel k` using `glRel_map L.toRingHom hglK`.

Establish `hGs : Formalism.REAL.GlRel s` using `glRel_map Rr.toRingHom (spinM_glRel c hcl)`. Establish `hYe : yF (kF E1 E2) c = fun a b => k a b + s a b`. Use function extensionality and compare the values at `a b`. Conclude with `yF_eq _ _ a b`. Establish `hGY : Formalism.REAL.GlRel (yF (kF E1 E2) c)`.

Rewrite using `[hYe]`. Conclude with `glRel_add k s hGk hGs hks`. Establish `hCY` using `Formalism.REAL.compactCasimirOnHighestWeight_holds (ι → V) n (fun _ => true) _ τ x hGY hK`. Establish `hCK : Formalism.REAL.CasK (fun _ : Fin n => true) (yF (kF E1 E2) c) = Formalism.REAL.Cas (yF (kF E1 E2) c)`. Simplify using `[Formalism.REAL.CasK, Formalism.REAL.Cas]`.

Rewrite `hCY` using `[hCK, rhoC_true]`. Establish `hg : ∀ a b d e, g a b * g d e + g d e * g a b = if a = e ∧ b = d then (2 : ℂ) • (1 : Module.End ℂ (ι → V)) else 0`. Introduce `a b d e`. Establish `h1` using `congrArg Rr (cliff_hg hcl a b d e)`. Simplify using `only [map_add, map_mul] at h1`.

Rewrite using `[show g a b * g d e + g d e * g a b = Rr (c a b) * Rr (c d e) + Rr (c d e) * Rr (c a b) from rfl, h1]`. Use `split_ifs`. Rewrite using `[map_smul, map_one]`. Conclude with `map_zero Rr`. Establish `hpp : ∀ a b c' d, p a b * p c' d - p c' d * p a b = (if b = c' then k a d else 0) - (if d = a then k c' b else 0)`.

Introduce `a b c' d`. Establish `h1` using `congrArg L (bracket_p E1 E2 hp.gl1 hp.gl2 hp.comm a b c' d)`. Simplify using `only [map_sub, map_mul] at h1`. Establish `h2 : p a b * p c' d - p c' d * p a b = L (E1 a b - E2 a b) * L (E1 c' d - E2 c' d) - L (E1 c' d - E2 c' d) * L (E1 a b - E2 a b)` using `rfl`. Rewrite using `[h2]`.

Simplify using `only [map_sub]`. Rewrite using `[h1]`. Apply the tactic sequence `by_cases h5 : b = c' <;> by_cases h6 : d = a <;> simp [h5, h6, hkdef, kF]`. Establish `hsq` using `dirac_sq_ring p k g hg hpp (fun a b c' d => lft_mul_rgt _ _)`. Establish `hsE : ∀ d a, ((1 / 2 : ℂ) • ∑ e, g d e * g e a - if d = a then ((n : ℂ) / 2) • (1 : Module.End ℂ (ι → V)) else 0) = s d a`.

Introduce `d a`. Establish `: s d a = Rr (spinM c d a)` using `rfl`. Rewrite using `[this]`. Unfold `spinM`. Apply the tactic sequence `by_cases h1 : d = a <;> simp [h1, map_sub, map_smul, map_sum, map_mul, hgdef]`.

Simplify using `only [hsE] at hsq`. Rewrite `hsq` using `[← hDe]`. Establish `hCasY` using `cas_add k s hks`. Rewrite `hCasY` using `[← hYe]`. Establish `hCasP : (∑ a, ∑ b, p a b * p b a) + Formalism.REAL.Cas k = L (Formalism.REAL.Cas E1 + Formalism.REAL.Cas E1 + (Formalism.REAL.Cas E2 + Formalism.REAL.Cas E2))`.

Establish `h1` using `congrArg L (cas_p_add_k E1 E2)`. Simplify using `only [two_mul] at h1`. Rewrite using `[← h1]`. Simplify using `[Formalism.REAL.Cas, map_add, map_sum, map_mul, hpdef, hkdef, pF, kF]`. Establish `hCasS : Formalism.REAL.Cas s = (((n : ℂ) ^ 3 - n) / 4) • (1 : Module.End ℂ (ι → V))`.

Establish `h1` using `congrArg Rr (spinM_cas c hcl)`. Simplify using `only [map_smul, map_one] at h1`. Rewrite using `[← h1]`. Simplify using `[Formalism.REAL.Cas, map_sum, map_mul, hsdef]`. Establish `hTot : D * D + Formalism.REAL.Cas (yF (kF E1 E2) c) = L (Formalism.REAL.Cas E1 + Formalism.REAL.Cas E1 + (Formalism.REAL.Cas E2 + Formalism.REAL.Cas E2)) + (((n : ℂ) ^ 3 - n) / 4) • (1 : Module.End ℂ (ι → V))`.

Rewrite using `[← hCasP, ← hCasS, hsq, hCasY]`. Normalize the expressions using the abelian group laws. Use `set R : ℝ := ∑ a, (rhoV n a) ^ 2 with hR`. Use `set S : ℝ := (∑ a, (m0 lam a) ^ 2) / 4 with hS`. Establish `hv : ∀ b : Bool, GlobalTheory.Dec.gelfVal (infOf lam b) 2 = ((S - R : ℝ) : ℂ)`.

Introduce `b`. Rewrite using `[gelfVal_two_eq, infOf_sq, Complex.ofReal_sub, hS, hR]`. Use `push_cast`. Both sides reduce to the same expression. Establish `hC1 : ∀ v : V, Formalism.REAL.Cas E1 v = ((S - R : ℝ) : ℂ) • v`.

Introduce `v`. Rewrite using `[← gelA_two, h.ch1 2 v, hv]`. Establish `hC2 : ∀ v : V, Formalism.REAL.Cas E2 v = ((S - R : ℝ) : ℂ) • v`. Introduce `v`. Rewrite using `[← gelA_bar_two, h.ch2 2 v, hv]`.

Establish `hn : (((n : ℂ) ^ 3 - n) / 4) = ((3 * R : ℝ) : ℂ)`. Rewrite using `[hR, sum_rhoV_sq]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Use `set T : ℝ := Formalism.REAL.nsq (τ + rhoV n) - Formalism.REAL.nsq (rhoV n) with hT`.

Establish `hDD : D (D x) = ((4 * (S - R) + 3 * R - T : ℝ) : ℂ) • x`. Establish `h1` using `congrArg (fun f : Module.End ℂ (ι → V) => f x) hTot`. Simplify using `only [LinearMap.add_apply, Module.End.mul_apply, LinearMap.smul_apply, Module.End.one_apply] at h1`. Rewrite `h1` using `[hCY]`. Establish `h2 : L (Formalism.REAL.Cas E1 + Formalism.REAL.Cas E1 + (Formalism.REAL.Cas E2 + Formalism.REAL.Cas E2)) x = ((4 * (S - R) : ℝ) : ℂ) • x`.

Use function extensionality and compare the values at `i`. Simplify using `only [hL, lft_apply, LinearMap.add_apply, hC1, hC2, Pi.smul_apply]`. Use `push_cast`. Use `module`. Rewrite `h1` using `[h2, hn]`.

Rewrite using `[eq_sub_of_add_eq h1]`. Use `push_cast`. Use `module`. Establish `hsk` using `dirac_skew (pF E1 E2) c hp.unitP hc2 x (D x)`. Establish `hN : 0 < ∑ i, ‖x i‖ ^ 2`.

Take `⟨i, hi⟩` from `Function.ne_iff.mp hx`. Conclude with `Finset.sum_pos' (fun _ _ => by positivity) ⟨i, Finset.mem_univ _, by`. Establish `: x i ≠ 0` using `hi`. Use the proof step `positivity⟩`. Establish `hM : 0 ≤ ∑ i, ‖D x i‖ ^ 2` using `Finset.sum_nonneg fun _ _ => by positivity`.

Establish `hEq : ((∑ i, ‖D x i‖ ^ 2 : ℝ) : ℂ) = -(((4 * (S - R) + 3 * R - T) * ∑ i, ‖x i‖ ^ 2 : ℝ) : ℂ)`. Establish `e1 : ∑ i, ⟪dirac (pF E1 E2) c x i, D x i⟫_ℂ = ((∑ i, ‖D x i‖ ^ 2 : ℝ) : ℂ)`. Use `push_cast`. Conclude with `Finset.sum_congr rfl fun i _ => by`. Rewrite using `[inner_self_eq_norm_sq_to_K]`.

Both sides reduce to the same expression. Establish `e2 : ∑ i, ⟪x i, dirac (pF E1 E2) c (D x) i⟫_ℂ = (((4 * (S - R) + 3 * R - T) * ∑ i, ‖x i‖ ^ 2 : ℝ) : ℂ)`. Establish `: dirac (pF E1 E2) c (D x) = ((4 * (S - R) + 3 * R - T : ℝ) : ℂ) • x` using `hDD`. Rewrite using `[this]`. Use `push_cast`.

Rewrite using `[Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun i _ => by`. Rewrite using `[Pi.smul_apply, inner_smul_right, inner_self_eq_norm_sq_to_K]`. Use `push_cast`. Both sides reduce to the same expression.

Rewrite using `[← e1, hsk, e2]`. Establish `hEq' : (∑ i, ‖D x i‖ ^ 2) = -((4 * (S - R) + 3 * R - T) * ∑ i, ‖x i‖ ^ 2)`. Conclude with `hEq` after adjusting the coercions. Establish `hle : 4 * (S - R) + 3 * R - T ≤ 0`. Assume the negation of the conclusion as `hcon`.

Use `push_neg at hcon`. Use `mul_pos hcon hN` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hT' : T = ∑ a, (τ a + rhoV n a) ^ 2 - R`. Rewrite using `[hT, hR]`.

Simplify using `only [Formalism.REAL.nsq, Formalism.REAL.dot, Pi.add_apply, pow_two]`. Rewrite `hle` using `[hT']`. Establish `: ∑ a, (m0 lam a) ^ 2 = 4 * S`. Rewrite using `[hS]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[this]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem dirac_ineq0 : ∀ {n : ℕ} (lam : Fin n → ℤ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (E1 E2 : Fin n → Fin n → Module.End ℂ V) (σ : Matrix.unitaryGroup (Fin n) ℂ →* (V →ₗ[ℂ] V)),
    IsCoreMod0 (infOf lam) E1 E2 σ → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (c : Fin n → Fin n → Matrix ι ι ℂ),
      IsCliff c → ∀ (τ : Fin n → ℝ) (x : ι → V), x ≠ 0 → Formalism.REAL.KHighest (fun _ => true) (yF (kF E1 E2) c) τ x →
        ∑ a, (m0 lam a) ^ 2 ≤ ∑ a, (τ a + rhoV n a) ^ 2 := by
  intro n lam V _ _ E1 E2 σ h ι _ _ c hc τ x hx hK
  obtain ⟨hc1, hc2⟩ := hc
  have hcl : IsCliff c := ⟨hc1, hc2⟩
  have hp := h.pair

  set L := lft (V := V) ι with hL
  set Rr := rgt (ι := ι) V with hRr
  set p : Fin n → Fin n → Module.End ℂ (ι → V) := fun a b => L (pF E1 E2 a b) with hpdef
  set k : Fin n → Fin n → Module.End ℂ (ι → V) := fun a b => L (kF E1 E2 a b) with hkdef
  set g : Fin n → Fin n → Module.End ℂ (ι → V) := fun a b => Rr (c a b) with hgdef
  set s : Fin n → Fin n → Module.End ℂ (ι → V) := fun a b => Rr (spinM c a b) with hsdef
  set D := dirac (pF E1 E2) c with hD
  have hDe : D = ∑ a, ∑ b, p a b * g b a := rfl
  have hks : ∀ a b c' d, k a b * s c' d = s c' d * k a b := fun a b c' d => lft_mul_rgt _ _
  have hglK : Formalism.REAL.GlRel (kF E1 E2) := glRel_add E1 E2 hp.gl1 hp.gl2 hp.comm
  have hGk : Formalism.REAL.GlRel k := glRel_map L.toRingHom hglK
  have hGs : Formalism.REAL.GlRel s := glRel_map Rr.toRingHom (spinM_glRel c hcl)
  have hYe : yF (kF E1 E2) c = fun a b => k a b + s a b := by
    funext a b
    exact yF_eq _ _ a b
  have hGY : Formalism.REAL.GlRel (yF (kF E1 E2) c) := by
    rw [hYe]
    exact glRel_add k s hGk hGs hks
  have hCY := Formalism.REAL.compactCasimirOnHighestWeight_holds (ι → V) n (fun _ => true) _ τ x hGY hK
  have hCK : Formalism.REAL.CasK (fun _ : Fin n => true) (yF (kF E1 E2) c) = Formalism.REAL.Cas (yF (kF E1 E2) c) := by
    simp [Formalism.REAL.CasK, Formalism.REAL.Cas]
  rw [hCK, rhoC_true] at hCY

  have hg : ∀ a b d e, g a b * g d e + g d e * g a b = if a = e ∧ b = d then (2 : ℂ) • (1 : Module.End ℂ (ι → V)) else 0 := by
    intro a b d e
    have h1 := congrArg Rr (cliff_hg hcl a b d e)
    simp only [map_add, map_mul] at h1
    rw [show g a b * g d e + g d e * g a b = Rr (c a b) * Rr (c d e) + Rr (c d e) * Rr (c a b) from rfl, h1]
    split_ifs
    · rw [map_smul, map_one]
    · exact map_zero Rr
  have hpp : ∀ a b c' d, p a b * p c' d - p c' d * p a b =
      (if b = c' then k a d else 0) - (if d = a then k c' b else 0) := by
    intro a b c' d
    have h1 := congrArg L (bracket_p E1 E2 hp.gl1 hp.gl2 hp.comm a b c' d)
    simp only [map_sub, map_mul] at h1
    have h2 : p a b * p c' d - p c' d * p a b = L (E1 a b - E2 a b) * L (E1 c' d - E2 c' d) -
        L (E1 c' d - E2 c' d) * L (E1 a b - E2 a b) := rfl
    rw [h2]
    simp only [map_sub]
    rw [h1]
    by_cases h5 : b = c' <;> by_cases h6 : d = a <;> simp [h5, h6, hkdef, kF]
  have hsq := dirac_sq_ring p k g hg hpp (fun a b c' d => lft_mul_rgt _ _)
  have hsE : ∀ d a, ((1 / 2 : ℂ) • ∑ e, g d e * g e a - if d = a then ((n : ℂ) / 2) • (1 : Module.End ℂ (ι → V)) else 0) =
      s d a := by
    intro d a
    have : s d a = Rr (spinM c d a) := rfl
    rw [this]
    unfold spinM
    by_cases h1 : d = a <;> simp [h1, map_sub, map_smul, map_sum, map_mul, hgdef]
  simp only [hsE] at hsq
  rw [← hDe] at hsq
  have hCasY := cas_add k s hks
  rw [← hYe] at hCasY
  have hCasP : (∑ a, ∑ b, p a b * p b a) + Formalism.REAL.Cas k =
      L (Formalism.REAL.Cas E1 + Formalism.REAL.Cas E1 + (Formalism.REAL.Cas E2 + Formalism.REAL.Cas E2)) := by
    have h1 := congrArg L (cas_p_add_k E1 E2)
    simp only [two_mul] at h1
    rw [← h1]
    simp [Formalism.REAL.Cas, map_add, map_sum, map_mul, hpdef, hkdef, pF, kF]
  have hCasS : Formalism.REAL.Cas s = (((n : ℂ) ^ 3 - n) / 4) • (1 : Module.End ℂ (ι → V)) := by
    have h1 := congrArg Rr (spinM_cas c hcl)
    simp only [map_smul, map_one] at h1
    rw [← h1]
    simp [Formalism.REAL.Cas, map_sum, map_mul, hsdef]
  have hTot : D * D + Formalism.REAL.Cas (yF (kF E1 E2) c) =
      L (Formalism.REAL.Cas E1 + Formalism.REAL.Cas E1 + (Formalism.REAL.Cas E2 + Formalism.REAL.Cas E2)) +
        (((n : ℂ) ^ 3 - n) / 4) • (1 : Module.End ℂ (ι → V)) := by
    rw [← hCasP, ← hCasS, hsq, hCasY]
    abel

  set R : ℝ := ∑ a, (rhoV n a) ^ 2 with hR
  set S : ℝ := (∑ a, (m0 lam a) ^ 2) / 4 with hS
  have hv : ∀ b : Bool, GlobalTheory.Dec.gelfVal (infOf lam b) 2 = ((S - R : ℝ) : ℂ) := by
    intro b
    rw [gelfVal_two_eq, infOf_sq, Complex.ofReal_sub, hS, hR]
    push_cast
    rfl
  have hC1 : ∀ v : V, Formalism.REAL.Cas E1 v = ((S - R : ℝ) : ℂ) • v := by
    intro v
    rw [← gelA_two, h.ch1 2 v, hv]
  have hC2 : ∀ v : V, Formalism.REAL.Cas E2 v = ((S - R : ℝ) : ℂ) • v := by
    intro v
    rw [← gelA_bar_two, h.ch2 2 v, hv]
  have hn : (((n : ℂ) ^ 3 - n) / 4) = ((3 * R : ℝ) : ℂ) := by
    rw [hR, sum_rhoV_sq]
    push_cast
    ring
  set T : ℝ := Formalism.REAL.nsq (τ + rhoV n) - Formalism.REAL.nsq (rhoV n) with hT
  have hDD : D (D x) = ((4 * (S - R) + 3 * R - T : ℝ) : ℂ) • x := by
    have h1 := congrArg (fun f : Module.End ℂ (ι → V) => f x) hTot
    simp only [LinearMap.add_apply, Module.End.mul_apply, LinearMap.smul_apply, Module.End.one_apply] at h1
    rw [hCY] at h1
    have h2 : L (Formalism.REAL.Cas E1 + Formalism.REAL.Cas E1 + (Formalism.REAL.Cas E2 + Formalism.REAL.Cas E2)) x =
        ((4 * (S - R) : ℝ) : ℂ) • x := by
      funext i
      simp only [hL, lft_apply, LinearMap.add_apply, hC1, hC2, Pi.smul_apply]
      push_cast
      module
    rw [h2, hn] at h1
    rw [eq_sub_of_add_eq h1]
    push_cast
    module

  have hsk := dirac_skew (pF E1 E2) c hp.unitP hc2 x (D x)
  have hN : 0 < ∑ i, ‖x i‖ ^ 2 := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
    exact Finset.sum_pos' (fun _ _ => by positivity) ⟨i, Finset.mem_univ _, by
      have : x i ≠ 0 := hi
      positivity⟩
  have hM : 0 ≤ ∑ i, ‖D x i‖ ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
  have hEq : ((∑ i, ‖D x i‖ ^ 2 : ℝ) : ℂ) = -(((4 * (S - R) + 3 * R - T) * ∑ i, ‖x i‖ ^ 2 : ℝ) : ℂ) := by
    have e1 : ∑ i, ⟪dirac (pF E1 E2) c x i, D x i⟫_ℂ = ((∑ i, ‖D x i‖ ^ 2 : ℝ) : ℂ) := by
      push_cast
      exact Finset.sum_congr rfl fun i _ => by
        rw [inner_self_eq_norm_sq_to_K]
        rfl
    have e2 : ∑ i, ⟪x i, dirac (pF E1 E2) c (D x) i⟫_ℂ =
        (((4 * (S - R) + 3 * R - T) * ∑ i, ‖x i‖ ^ 2 : ℝ) : ℂ) := by
      have : dirac (pF E1 E2) c (D x) = ((4 * (S - R) + 3 * R - T : ℝ) : ℂ) • x := hDD
      rw [this]
      push_cast
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by
        rw [Pi.smul_apply, inner_smul_right, inner_self_eq_norm_sq_to_K]
        push_cast
        rfl
    rw [← e1, hsk, e2]
  have hEq' : (∑ i, ‖D x i‖ ^ 2) = -((4 * (S - R) + 3 * R - T) * ∑ i, ‖x i‖ ^ 2) := by
    exact_mod_cast hEq
  have hle : 4 * (S - R) + 3 * R - T ≤ 0 := by
    by_contra hcon
    push_neg at hcon
    have := mul_pos hcon hN
    linarith
  have hT' : T = ∑ a, (τ a + rhoV n a) ^ 2 - R := by
    rw [hT, hR]
    simp only [Formalism.REAL.nsq, Formalism.REAL.dot, Pi.add_apply, pow_two]
  rw [hT'] at hle
  have : ∑ a, (m0 lam a) ^ 2 = 4 * S := by
    rw [hS]
    ring
  rw [this]
  linarith

/- English proof (translation)
Introduce `n lam _ V _ _ E1 E2 σ hc ν hν`. Take `⟨x, hxh, hx⟩` from `(Submodule.ne_bot_iff _).1 hν`. Take `⟨S, hfd, hvS, -, hKS, -⟩` from `hc.der.2 x`. Establish `hGl : Formalism.REAL.GlRel (kF E1 E2)` using `GlobalTheory.CompanionTheory.RealMult.DiracProof.kF_gl hc.pair`. Establish `hK : Formalism.REAL.KHighest (fun _ => true) (kF E1 E2) ν x` using `hxh`.

Establish `hint : ∀ a, ∃ m : ℤ, ν a = m` using `fun a => GlobalTheory.CompanionTheory.RealMult.DiracProof.weight_int hc.der a (ν a) hx (hK.1 a)`. Use `choose m hm using hint`. Establish `hνm : wtR m = ν`. Use function extensionality and compare the values at `a`. Conclude with `(hm a).symm`.

Take `⟨ι, i1, i2, c, hcl, hconds⟩` from `GlobalTheory.T.parthasarathy_rao_varadarajan n`. Establish `hK' : Formalism.REAL.KHighest (fun _ => true) (kF E1 E2) (wtR m) x` using `by rwa [hνm]`. Take `⟨w, -, y, hy, hyh⟩` from `hconds V (kF E1 E2) S m x hGl hc.pair.unitK hfd hKS hvS hx hK'`. Establish `hn` using `dirac_ineq0 lam V E1 E2 σ hc ι c hcl _ y hy hyh`. Rewrite `hn` using `[hνm]`.

Establish `e1 : LSq lam = ∑ a, (m0 lam a) ^ 2`. Simplify using `only [LSq, nsq, m0, rhoV]`. Conclude with `Finset.sum_congr rfl fun a _ => by ring`. Establish `e2 : Formalism.REAL.nsq (ν - rhoV n + rhoV n ∘ w.symm) = ∑ a, (ν (w a) - rhoV n (w a) + rhoV n a) ^ 2`. Simplify using `only [Formalism.REAL.nsq, Formalism.REAL.dot]`.

Rewrite using `[← Equiv.sum_comp w]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Simplify using `only [Pi.add_apply, Pi.sub_apply, Function.comp, Equiv.symm_apply_apply]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e1]`.

Establish `h3` using `norm_sq_le_dominant_rearrangement (ν - rhoV n) w.symm`. Rewrite `h3` using `[e2]`. Conclude with `hn.trans h3`.
-/
theorem dirac_inequality_k_types : DiracInequalityWithoutSplitComponent := by
  intro n lam _ V _ _ E1 E2 σ hc ν hν
  obtain ⟨x, hxh, hx⟩ := (Submodule.ne_bot_iff _).1 hν
  obtain ⟨S, hfd, hvS, -, hKS, -⟩ := hc.der.2 x
  have hGl : Formalism.REAL.GlRel (kF E1 E2) := GlobalTheory.CompanionTheory.RealMult.DiracProof.kF_gl hc.pair
  have hK : Formalism.REAL.KHighest (fun _ => true) (kF E1 E2) ν x := hxh
  have hint : ∀ a, ∃ m : ℤ, ν a = m := fun a =>
    GlobalTheory.CompanionTheory.RealMult.DiracProof.weight_int hc.der a (ν a) hx (hK.1 a)
  choose m hm using hint
  have hνm : wtR m = ν := by
    funext a
    exact (hm a).symm
  obtain ⟨ι, i1, i2, c, hcl, hconds⟩ := GlobalTheory.T.parthasarathy_rao_varadarajan n
  have hK' : Formalism.REAL.KHighest (fun _ => true) (kF E1 E2) (wtR m) x := by rwa [hνm]
  obtain ⟨w, -, y, hy, hyh⟩ := hconds V (kF E1 E2) S m x hGl hc.pair.unitK hfd hKS hvS hx hK'
  have hn := dirac_ineq0 lam V E1 E2 σ hc ι c hcl _ y hy hyh
  rw [hνm] at hn
  have e1 : LSq lam = ∑ a, (m0 lam a) ^ 2 := by
    simp only [LSq, nsq, m0, rhoV]
    exact Finset.sum_congr rfl fun a _ => by ring
  have e2 : Formalism.REAL.nsq (ν - rhoV n + rhoV n ∘ w.symm) = ∑ a, (ν (w a) - rhoV n (w a) + rhoV n a) ^ 2 := by
    simp only [Formalism.REAL.nsq, Formalism.REAL.dot]
    rw [← Equiv.sum_comp w]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [Pi.add_apply, Pi.sub_apply, Function.comp, Equiv.symm_apply_apply]
    ring
  rw [e1]
  have h3 := norm_sq_le_dominant_rearrangement (ν - rhoV n) w.symm
  rw [e2] at h3
  exact hn.trans h3

end GlobalTheory.CompanionTheory.DiracKType0
