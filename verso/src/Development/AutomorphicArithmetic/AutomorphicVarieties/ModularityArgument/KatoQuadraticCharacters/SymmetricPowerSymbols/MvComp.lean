import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.SymExOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.CycSpec
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.KaB
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.ComapLtOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.DifB

noncomputable section

open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4

namespace UpperTheory.V.Z.Kato.Sym

/- English proof (translation)
Take `⟨-, -, hlg, -, -, -, -⟩` from `lgB Ω ε X m hm`. Proceed by induction on `n with`. Consider the case `zero`. Simplify using `only [pow_zero, Nat.cast_zero, zero_mul, ka, map_one]`. Conclude with `hlg 1 1 0 one_ne_zero (by simp)`.

Consider the case `succ k ih`. Establish `hk : (θ ^ k) ^ m = io X (u ^ k)`. Rewrite using `[← pow_mul, mul_comm, pow_mul, hθ, map_pow]`. Rewrite using `[pow_succ, (kaB Ω ε X m hm (θ ^ k) (u ^ k) (pow_ne_zero _ hu) hk).2.2.2.2.2 θ u hu hθ h hh, ih]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
private theorem ka_pow {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (m : ℕ) (hm : 0 < m)
    (θ : Kb X) (u : X.K) (hu : u ≠ 0) (hθ : θ ^ m = io X u) (h : RingAut (Kb X)) (hh : InD X h) (n : ℕ) :
    ka X m (θ ^ n) h = (n : ZMod m) * ka X m θ h := by
  obtain ⟨-, -, hlg, -, -, -, -⟩ := lgB Ω ε X m hm
  induction n with
  | zero =>
    simp only [pow_zero, Nat.cast_zero, zero_mul, ka, map_one]
    exact hlg 1 1 0 one_ne_zero (by simp)
  | succ k ih =>
    have hk : (θ ^ k) ^ m = io X (u ^ k) := by
      rw [← pow_mul, mul_comm, pow_mul, hθ, map_pow]
    rw [pow_succ, (kaB Ω ε X m hm (θ ^ k) (u ^ k) (pow_ne_zero _ hu) hk).2.2.2.2.2 θ u hu hθ h hh, ih]
    push_cast
    ring

/- English proof (translation)
Introduce `Ω _ _ _ ε X m hm τ τ' s s' hadm hadm' u v P Q R hP hQ hR f f' hf hf'`. Use `haveI : NeZero m := ⟨hm.ne'⟩`. Take `⟨σ, hσ, θ, hθ, hkθ⟩` from `hf`. Take `⟨σ', hσ', θ', hθ', hkθ'⟩` from `hf'`. Take `⟨-, -, -, -, -, -, hcyc⟩` from `lgB Ω ε X m hm`.

Establish `f0 : (f : X.K) ≠ 0` using `f.ne_zero`. Establish `τf0 : τ' (f : X.K) ≠ 0` using `by simpa using f0`. Establish `r1 : (σ' θ) ^ m = io X (τ' (f : X.K))`. Rewrite using `[← map_pow, hθ, hσ']`. Establish `hPτ` using `mvPt Ω ε X m hm τ s hadm σ hσ u v P hP`.

Establish `hA'` using `mvPt Ω ε X m hm τ' s' hadm' σ' hσ' (τ u) (τ v) _ hPτ`. Establish `hB'` using `mvPt Ω ε X m hm τ' s' hadm' σ' hσ' (τ u) (τ v) Q hQ`. Establish `D1` using `difB Ω ε X m hm (τ u) (τ v) _ Q hPτ hQ`. Establish `D2` using `difB Ω ε X m hm (τ' (τ u)) (τ' (τ v)) _ _ hA' hB'`. Establish `KB` using `kaB Ω ε X m hm θ f f0 hθ`.

Use `set k := (cyc m s').val with hkdef`. Establish `KP` using `kaB Ω ε X m hm ((σ' θ) ^ k) (τ' (f : X.K) ^ k) (pow_ne_zero _ τf0) (by rw [← pow_mul, mul_comm, pow_mul, r1, map_pow])`. Establish `hA : Pt.mv (σ' * σ) (cyc m (s' * s)) P = Pt.mv σ' (cyc m s') (Pt.mv σ (cyc m s) P)`. Rewrite using `[(hcyc s' s).1]`. Simplify using `only [Pt.mv]`.

Use `congr 1`. Use function extensionality and compare the values at `h`. Rewrite using `[show σ⁻¹ * (σ'⁻¹ * h * σ') * σ = (σ' * σ)⁻¹ * h * (σ' * σ) by group]`. Expand and normalize the polynomial expressions, which then agree. Use `⟨σ' * σ, fun x => ?_, (σ' θ) ^ k * θ', ?_, fun h hh => ?_⟩` and prove the remaining obligations.

Use `show σ' (σ (io X x)) = io X (τ' (τ x))`. Rewrite using `[hσ x, hσ']`. Simplify using `only [Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_pow, mul_pow, ← hθ']`. Rewrite using `[← pow_mul, mul_comm k m, pow_mul, r1]`. Both sides reduce to the same expression.

Take `⟨hin, hconj⟩` from `KB.2.2.2.2.1 σ' τ' s' hadm' hσ' h hh`. Rewrite using `[KP.2.2.2.2.2 θ' f' f'.ne_zero hθ' h hh, ka_pow X m hm (σ' θ) (τ' (f : X.K)) τf0 r1 h hh k, hconj, hkθ _ hin, hkθ' h hh, hA, D2.2.2.2.1 R hR h hh, D1.2.2.2.2.2.2 τ' s' hadm' σ' hσ' h hh, hkdef, ZMod.natCast_zmod_val]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem mvComp : MvComp := by
  intro Ω _ _ _ ε X m hm τ τ' s s' hadm hadm' u v P Q R hP hQ hR f f' hf hf'
  haveI : NeZero m := ⟨hm.ne'⟩
  obtain ⟨σ, hσ, θ, hθ, hkθ⟩ := hf
  obtain ⟨σ', hσ', θ', hθ', hkθ'⟩ := hf'
  obtain ⟨-, -, -, -, -, -, hcyc⟩ := lgB Ω ε X m hm
  have f0 : (f : X.K) ≠ 0 := f.ne_zero
  have τf0 : τ' (f : X.K) ≠ 0 := by simpa using f0
  have r1 : (σ' θ) ^ m = io X (τ' (f : X.K)) := by
    rw [← map_pow, hθ, hσ']
  have hPτ := mvPt Ω ε X m hm τ s hadm σ hσ u v P hP
  have hA' := mvPt Ω ε X m hm τ' s' hadm' σ' hσ' (τ u) (τ v) _ hPτ
  have hB' := mvPt Ω ε X m hm τ' s' hadm' σ' hσ' (τ u) (τ v) Q hQ
  have D1 := difB Ω ε X m hm (τ u) (τ v) _ Q hPτ hQ
  have D2 := difB Ω ε X m hm (τ' (τ u)) (τ' (τ v)) _ _ hA' hB'
  have KB := kaB Ω ε X m hm θ f f0 hθ
  set k := (cyc m s').val with hkdef
  have KP := kaB Ω ε X m hm ((σ' θ) ^ k) (τ' (f : X.K) ^ k) (pow_ne_zero _ τf0)
    (by rw [← pow_mul, mul_comm, pow_mul, r1, map_pow])
  have hA : Pt.mv (σ' * σ) (cyc m (s' * s)) P = Pt.mv σ' (cyc m s') (Pt.mv σ (cyc m s) P) := by
    rw [(hcyc s' s).1]
    simp only [Pt.mv]
    congr 1
    funext h
    rw [show σ⁻¹ * (σ'⁻¹ * h * σ') * σ = (σ' * σ)⁻¹ * h * (σ' * σ) by group]
    ring
  refine ⟨σ' * σ, fun x => ?_, (σ' θ) ^ k * θ', ?_, fun h hh => ?_⟩
  · show σ' (σ (io X x)) = io X (τ' (τ x))
    rw [hσ x, hσ']
  · simp only [Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_pow, mul_pow, ← hθ']
    rw [← pow_mul, mul_comm k m, pow_mul, r1]
    rfl
  · obtain ⟨hin, hconj⟩ := KB.2.2.2.2.1 σ' τ' s' hadm' hσ' h hh
    rw [KP.2.2.2.2.2 θ' f' f'.ne_zero hθ' h hh, ka_pow X m hm (σ' θ) (τ' (f : X.K)) τf0 r1 h hh k,
      hconj, hkθ _ hin, hkθ' h hh, hA, D2.2.2.2.1 R hR h hh, D1.2.2.2.2.2.2 τ' s' hadm' σ' hσ' h hh,
      hkdef, ZMod.natCast_zmod_val]
    ring

end UpperTheory.V.Z.Kato.Sym

end
