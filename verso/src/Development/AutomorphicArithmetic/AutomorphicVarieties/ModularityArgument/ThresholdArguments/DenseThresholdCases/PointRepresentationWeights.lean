import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ResidueFlagPoints.CycIne
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LaArith
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AfDesc
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.PointTheoremBaseObject
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LitAut
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutomorphicFormHyp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.IsAutCsdA

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.CuspRep GlobalTheory.GalOfCusp
/- English proof (translation)
Introduce `hP l _ L Ω _ _ _ _ _ _ s V c n r B ι J hJ x ρ m hn2 hn4 hrep hc haut hv0 hm hfl ⟨k, hk, hw⟩`. Establish `hov : ∀ v : W.Vl l L, (s.A v).valuation (l : Ω) < 1` using `fun v => by`. Simplify using `using (s.hA v _).2 v.2`. Establish `hl : ∀ v : W.Vl l L, ((l : ℕ) : 𝓞 L) ∈ (s.w v).asIdeal` using `fun v => by`. Use `(s.hw v _).1 ?_` and prove the remaining obligations.

Simplify using `using hov v`. Use `hJ x (fun v j _ => -m v j) ρ hn2 hn4 ⟨fun v τ i j hij => ?_, fun v j => ?_⟩ hrep hc haut hv0 fun v => ⟨hfl v, fun i j hij => ?_⟩` and prove the remaining obligations. Use `hm v i j hij` as an intermediate fact. Simplify using `only`. Use linear arithmetic over natural numbers and integers.

Conclude with `UpperTheory.V.Loc.laArith hP.toClassicalTheorems.litN.aut.art (s.hw v) (hl v) _ (psi_cont x v j) (m v j) k hk (hw v j)`. Establish `hne : 1 - m v i + m v j ≠ 0`. Break down `lt_trichotomy i j with h | h | h` into its components or cases. Use `hm v i j h` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Substitute `h` using the available equality. Use linear arithmetic over natural numbers and integers. Use `hm v j i h` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Take `⟨g, hg, hg1⟩` from `cycIne L Ω l (s.A v) (hov v) ((1 - m v i + m v j) * k) (mul_ne_zero hne (by exact_mod_cast hk.ne'))`.

Establish `hgD : g ∈ Dec (F` using `L) (s.A v) := (GlobalTheory.WeilDeligne.Weil_le_Dec (s.hw v)) (GlobalTheory.WeilDeligne.ineIncl (s.hw v) ⟨g, hg⟩).2`. Establish `h1` using `hw v i ⟨g, hgD⟩ hg`. Establish `h2` using `hw v j ⟨g, hgD⟩ hg`. Establish `e : x.psi v i ⟨g, hgD⟩ = x.psi v j ⟨g, hgD⟩ * cycBar L Ω l g`. Rewrite using `[hij]`.

Both sides reduce to the same expression. Apply `hg1` to reduce the goal to its premises. Establish `e2 : x.psi v i ⟨g, hgD⟩ * cycBar L Ω l g ^ (-m v i) = (x.psi v j ⟨g, hgD⟩ * cycBar L Ω l g ^ (-m v j)) * cycBar L Ω l g ^ (1 - m v i + m v j)`. Rewrite using `[e, mul_assoc, mul_assoc, ← zpow_add, ← zpow_one_add]`. Use `congr 2`.

Expand and normalize the polynomial expressions, which then agree. Express the relevant statement in the definitionally equal form `(x.psi v i ⟨g, hgD⟩ * cycBar L Ω l g ^ (-m v i)) ^ k = 1 at h1`. Express the relevant statement in the definitionally equal form `(x.psi v j ⟨g, hgD⟩ * cycBar L Ω l g ^ (-m v j)) ^ k = 1 at h2`. Rewrite `h1` using `[e2, mul_pow, h2, one_mul]`. Rewrite using `[zpow_mul, zpow_natCast, h1]`.
-/
theorem UpperTheory.V.Ws.Pt.point_representation_weights :
    _root_.UpperTheory.V.Af.HypothesesH' → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : W.HidaSetting l L Ω) (V : s.Lev) (c : Coef l) (n : ℕ) (r : W.Resid V.frame c.O n) (B : W.UniversalOrdinaryDeterminantRing r) (ι : PadicAlgCl l ≃+* ℂ) (J : Ideal B.B), B.PointTheoremBaseObject ι J → ∀ (x : B.Pt) (ρ : G L Ω →* GL (Fin n) (PadicAlgCl l)) (m : W.Vl l L → Fin n → ℤ), 2 ≤ n → n ≤ 4 → x.IsRep ρ → Continuous ρ → _root_.UpperTheory.V.Z.Win.IsAutCsdA ι ρ → (∀ g ∈ Ine (F := L) (s.A s.v0), ρ g = 1) → (∀ v i j, i < j → m v j + 2 ≤ m v i) → (∀ v : W.Vl l L, W.HasFlag (ρ.comp (Dec (F := L) (s.A v)).subtype) (x.psi v)) → (∃ k : ℕ, 0 < k ∧ ∀ (v : W.Vl l L) i (g : Dec (F := L) (s.A v)), (g : G L Ω) ∈ Ine (F := L) (s.A v) → (x.psi v i g * cycBar L Ω l g ^ (-m v i)) ^ k = 1) → J ≤ RingHom.ker x := by
  intro hP l _ L Ω _ _ _ _ _ _ s V c n r B ι J hJ x ρ m hn2 hn4 hrep hc haut hv0 hm hfl ⟨k, hk, hw⟩
  have hov : ∀ v : W.Vl l L, (s.A v).valuation (l : Ω) < 1 := fun v => by
    simpa using (s.hA v _).2 v.2
  have hl : ∀ v : W.Vl l L, ((l : ℕ) : 𝓞 L) ∈ (s.w v).asIdeal := fun v => by
    refine (s.hw v _).1 ?_
    simpa using hov v
  refine hJ x (fun v j _ => -m v j) ρ hn2 hn4 ⟨fun v τ i j hij => ?_, fun v j => ?_⟩
    hrep hc haut hv0
    fun v => ⟨hfl v, fun i j hij => ?_⟩
  · have := hm v i j hij
    simp only
    omega
  · exact UpperTheory.V.Loc.laArith hP.toClassicalTheorems.litN.aut.art (s.hw v) (hl v) _ (psi_cont x v j) (m v j) k hk (hw v j)
  · have hne : 1 - m v i + m v j ≠ 0 := by
      rcases lt_trichotomy i j with h | h | h
      · have := hm v i j h
        omega
      · subst h
        omega
      · have := hm v j i h
        omega
    obtain ⟨g, hg, hg1⟩ := cycIne L Ω l (s.A v) (hov v) ((1 - m v i + m v j) * k)
      (mul_ne_zero hne (by exact_mod_cast hk.ne'))
    have hgD : g ∈ Dec (F := L) (s.A v) :=
      (GlobalTheory.WeilDeligne.Weil_le_Dec (s.hw v)) (GlobalTheory.WeilDeligne.ineIncl (s.hw v) ⟨g, hg⟩).2
    have h1 := hw v i ⟨g, hgD⟩ hg
    have h2 := hw v j ⟨g, hgD⟩ hg
    have e : x.psi v i ⟨g, hgD⟩ = x.psi v j ⟨g, hgD⟩ * cycBar L Ω l g := by
      rw [hij]; rfl
    apply hg1
    have e2 : x.psi v i ⟨g, hgD⟩ * cycBar L Ω l g ^ (-m v i) =
        (x.psi v j ⟨g, hgD⟩ * cycBar L Ω l g ^ (-m v j)) * cycBar L Ω l g ^ (1 - m v i + m v j) := by
      rw [e, mul_assoc, mul_assoc, ← zpow_add, ← zpow_one_add]
      congr 2
      ring
    change (x.psi v i ⟨g, hgD⟩ * cycBar L Ω l g ^ (-m v i)) ^ k = 1 at h1
    change (x.psi v j ⟨g, hgD⟩ * cycBar L Ω l g ^ (-m v j)) ^ k = 1 at h2
    rw [e2, mul_pow, h2, one_mul] at h1
    rw [zpow_mul, zpow_natCast, h1]
end
