import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalDoubleCosets.TracePow

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL ValuativeRel Matrix MeasureTheory UpperTheory.ConvolutionTheory.Loc MulAction UpperTheory.Gal.LocD

/- English proof (translation)
Introduce `G _ _ _ _ _ _ B s p hp hper P κ hκ hs hB hne`. Take `⟨f₀, hf₀, g₀, h0⟩` from `hne`. Take `⟨K, hK, hKf⟩` from `GroundTheory.Automorphic.exists_forall_mul_left (R := ℂ) hf₀`. Use `set e : B → ℂ := fun b => P (fun x => f₀ ((b : G)⁻¹ * x)) g₀ / P f₀ g₀ with he`. Establish `hη : ∀ (b : B) (f : G → ℂ) (g : G), P (fun x => f ((b : G)⁻¹ * x)) g = e b * P f g`.

Introduce `b f g`. Take `⟨c, hc⟩` from `hB b`. Establish `hc0` using `hc f₀ g₀`. Establish `: e b = c`. Rewrite using `[he]`.

Simplify using `only`. Rewrite using `[hc0, mul_div_assoc, div_self h0, mul_one]`. Rewrite using `[this, hc]`. Establish `hpow : ∀ (n : ℕ) (f : G → ℂ) (g : G), P (f ∘ s^[n]) g = (κ : ℂ) ^ n * P f (s^[n] g)`. Introduce `n`.

Proceed by induction on `n with`. Consider the case `zero => intro f g`. Simplify using the standard rewrite rules. Consider the case `succ n ih`. Introduce `f g`.

Rewrite using `[Function.iterate_succ, ← Function.comp_assoc, hs, ih, Function.comp_apply, pow_succ]`. Expand and normalize the polynomial expressions, which then agree. Establish `hper' : s^[p] = id` using `funext hper`. Establish `hκ1 : κ = 1`. Establish `h1` using `hpow p f₀ g₀`.

Rewrite `h1` using `[hper', Function.comp_id, id]`. Establish `hk : (κ : ℂ) ^ p = 1`. Use `mul_right_cancel₀ h0 (h1.symm.trans (one_mul _).symm)` as an intermediate fact. Conclude with `this`. Establish `hk' : κ ^ p = 1` using `by exact_mod_cast hk`.

Conclude with `(pow_eq_one_iff_of_nonneg hκ.le hp.ne').1 hk'`. Establish `e1 : e 1 = 1`. Rewrite using `[he]`. Simplify using `only`. Simplify using `[div_self h0]`.

Establish `emul : ∀ b b' : B, e (b * b') = e b * e b'`. Introduce `b b'`. Establish `h` using `hη b (fun x => f₀ ((b' : G)⁻¹ * x)) g₀`. Rewrite `h` using `[hη b' f₀ g₀]`. Establish `h2 : e (b * b') * P f₀ g₀ = e b * e b' * P f₀ g₀`.

Rewrite using `[← hη, mul_assoc, ← h]`. Use `congr 1`. Use function extensionality and compare the values at `x`. Simplify using `[mul_assoc]`. Conclude with `mul_right_cancel₀ h0 h2`.

Set `η : B →* ℂ` to `{ toFun := e, map_one' := e1, map_mul' := emul }`. Use `⟨hκ1, η, fun b f g => hη b f g, ⟨K, K.isOpen, fun b hb => ?_⟩, fun b b' hbb => ?_⟩` and prove the remaining obligations. Use `show e b = 1`. Rewrite using `[he]`. Simplify using `only`.

Establish `hfix : (fun x => f₀ ((b : G)⁻¹ * x)) = f₀`. Use function extensionality and compare the values at `fun x => hKf _ (K.inv_mem (by exact hb)) x`. Rewrite using `[hfix, div_self h0]`. Use `show e b' = e b`. Establish `hg1 : s (s^[p - 1] g₀) = g₀`.

Rewrite using `[← Function.iterate_succ_apply' (f := s), Nat.succ_eq_add_one, Nat.sub_add_cancel hp, hper]`. Establish `hA` using `hη b (f₀ ∘ s) (s^[p - 1] g₀)`. Rewrite `hA` using `[hs, hg1]`. Establish `hfun : (fun x => (f₀ ∘ s) ((b : G)⁻¹ * x)) = (fun x => f₀ ((b' : G)⁻¹ * x)) ∘ s`. Use function extensionality and compare the values at `x`.

Simplify using `[hbb, map_mul, map_inv]`. Rewrite `hA` using `[hfun, hs, hg1, hη b' f₀ g₀]`. Establish `hκ0 : (κ : ℂ) ≠ 0` using `by exact_mod_cast hκ.ne'`. Establish `h3 : e b' * P f₀ g₀ = e b * P f₀ g₀`. Use `mul_left_cancel₀ hκ0 (hA.trans (by ring : e b * (↑κ * P f₀ g₀) = ↑κ * (e b * P f₀ g₀)))` as an intermediate fact.

Conclude with `this`. Conclude with `mul_right_cancel₀ h0 h3`.
-/
theorem UpperTheory.Gal.LocD.etaEx :
    EtaEx := by
  intro G _ _ _ _ _ _ B s p hp hper P κ hκ hs hB hne
  obtain ⟨f₀, hf₀, g₀, h0⟩ := hne
  obtain ⟨K, hK, hKf⟩ := GroundTheory.Automorphic.exists_forall_mul_left (R := ℂ) hf₀
  set e : B → ℂ := fun b => P (fun x => f₀ ((b : G)⁻¹ * x)) g₀ / P f₀ g₀ with he
  have hη : ∀ (b : B) (f : G → ℂ) (g : G), P (fun x => f ((b : G)⁻¹ * x)) g = e b * P f g := by
    intro b f g
    obtain ⟨c, hc⟩ := hB b
    have hc0 := hc f₀ g₀
    have : e b = c := by
      rw [he]; dsimp only; rw [hc0, mul_div_assoc, div_self h0, mul_one]
    rw [this, hc]
  have hpow : ∀ (n : ℕ) (f : G → ℂ) (g : G), P (f ∘ s^[n]) g = (κ : ℂ) ^ n * P f (s^[n] g) := by
    intro n
    induction n with
    | zero => intro f g; simp
    | succ n ih =>
      intro f g
      rw [Function.iterate_succ, ← Function.comp_assoc, hs, ih, Function.comp_apply, pow_succ]
      ring
  have hper' : s^[p] = id := funext hper
  have hκ1 : κ = 1 := by
    have h1 := hpow p f₀ g₀
    rw [hper', Function.comp_id, id] at h1
    have hk : (κ : ℂ) ^ p = 1 := by
      have := mul_right_cancel₀ h0 (h1.symm.trans (one_mul _).symm)
      exact this
    have hk' : κ ^ p = 1 := by exact_mod_cast hk
    exact (pow_eq_one_iff_of_nonneg hκ.le hp.ne').1 hk'
  have e1 : e 1 = 1 := by
    rw [he]; dsimp only; simp [div_self h0]
  have emul : ∀ b b' : B, e (b * b') = e b * e b' := by
    intro b b'
    have h := hη b (fun x => f₀ ((b' : G)⁻¹ * x)) g₀
    rw [hη b' f₀ g₀] at h
    have h2 : e (b * b') * P f₀ g₀ = e b * e b' * P f₀ g₀ := by
      rw [← hη, mul_assoc, ← h]
      congr 1
      funext x
      simp [mul_assoc]
    exact mul_right_cancel₀ h0 h2
  let η : B →* ℂ := { toFun := e, map_one' := e1, map_mul' := emul }
  refine ⟨hκ1, η, fun b f g => hη b f g, ⟨K, K.isOpen, fun b hb => ?_⟩, fun b b' hbb => ?_⟩
  · show e b = 1
    rw [he]
    dsimp only
    have hfix : (fun x => f₀ ((b : G)⁻¹ * x)) = f₀ :=
      funext fun x => hKf _ (K.inv_mem (by exact hb)) x
    rw [hfix, div_self h0]
  · show e b' = e b
    have hg1 : s (s^[p - 1] g₀) = g₀ := by
      rw [← Function.iterate_succ_apply' (f := s), Nat.succ_eq_add_one, Nat.sub_add_cancel hp,
        hper]
    have hA := hη b (f₀ ∘ s) (s^[p - 1] g₀)
    rw [hs, hg1] at hA
    have hfun : (fun x => (f₀ ∘ s) ((b : G)⁻¹ * x)) = (fun x => f₀ ((b' : G)⁻¹ * x)) ∘ s := by
      funext x
      simp [hbb, map_mul, map_inv]
    rw [hfun, hs, hg1, hη b' f₀ g₀] at hA
    have hκ0 : (κ : ℂ) ≠ 0 := by exact_mod_cast hκ.ne'
    have h3 : e b' * P f₀ g₀ = e b * P f₀ g₀ := by
      have := mul_left_cancel₀ hκ0 (hA.trans (by ring : e b * (↑κ * P f₀ g₀) = ↑κ * (e b * P f₀ g₀)))
      exact this
    exact mul_right_cancel₀ h0 h3
