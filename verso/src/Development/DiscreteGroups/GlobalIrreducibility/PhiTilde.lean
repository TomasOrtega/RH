import Mathlib
import Development.DiscreteGroups.GlobalIrreducibility.DzMatchCut
import Development.DiscreteGroups.GlobalIrreducibility.FLRight
import Development.DiscreteGroups.GlobalIrreducibility.DzRedInt
import Development.DiscreteGroups.GlobalIrreducibility.LConvSepI

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq
  GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Whittaker
open scoped Pointwise

namespace DiscreteGroups.sglob.DzRed

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {g : ℕ} [Fact g.Prime]
  (i : ℚ_[g] ≃+* w.adicCompletion E)

/- English proof (translation)
Use `show Matrix.GeneralLinearGroup.map i.toRingHom (Matrix.GeneralLinearGroup.map (algebraMap ℤ_[g] ℚ_[g]) (tilde κ)) = _`. Rewrite using `[map_tilde, map_tilde]`. Both sides reduce to the same expression.
-/
theorem phi_tilde {n : ℕ} (κ : GL (Fin n) ℤ_[g]) :
    Matrix.GeneralLinearGroup.map i.toRingHom (GlobalTheory.GLp.inc g n (tilde κ)) =
      tilde (Matrix.GeneralLinearGroup.map i.toRingHom (GlobalTheory.GLp.inc g n κ)) := by
  show Matrix.GeneralLinearGroup.map i.toRingHom (Matrix.GeneralLinearGroup.map (algebraMap ℤ_[g] ℚ_[g]) (tilde κ)) = _
  rw [map_tilde, map_tilde]
  rfl

/- English proof (translation)
The claim follows from `map_tilde _ κ`.
-/
theorem red_tilde {n : ℕ} (κ : GL (Fin n) ℤ_[g]) : GlobalTheory.GLp.red g n (tilde κ) = tilde (GlobalTheory.GLp.red g n κ) :=
  map_tilde _ κ

end DiscreteGroups.sglob.DzRed

namespace DiscreteGroups.sglob.DzType

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

/- English proof (translation)
Introduce `hCG E _ _ w g _ i hi ψ₀ hψ₀ ψ hψc hψ m τ hτ σ hσ hinf τ₀ ω hω hcell e he`. Take `⟨φ, hφ0, hφ⟩` from `hinf`. Establish `hφ' : ∀ (κ : GL (Fin (m + 1)) ℤ_[g]) (x : τ), φ (τ.ρ (GlobalTheory.GLp.red g (m + 1) κ) x) = σ.ρ (Matrix.GeneralLinearGroup.map i.toRingHom (GlobalTheory.GLp.inc g (m + 1) κ)) (φ x)` using `hφ`. Establish `hψ' : ∀ x : ℤ_[g], ψ (i (x : ℚ_[g])) = ψ₀ (PadicInt.toZMod x)` using `hψ`. Take `⟨x0, hx0⟩` from `DzRed.exists_psi_ne_one i hψ' hψ₀`.

Establish `hψ1 : ψ ≠ 1` using `fun h => hx0 (by rw [h, AddChar.one_apply])`. Establish `hnt : Nontrivial σ.V`. Choose the witnesses or unpack the hypotheses as in `⟨x, hx⟩ : ∃ x, φ x ≠ 0 := by`. Assume the negation of the conclusion as `hc`. Use `push Not at hc`.

Conclude with `hφ0 (LinearMap.ext hc)`. Conclude with `⟨⟨φ x, 0, hx⟩⟩`. Take `⟨L, hL0, hL⟩` from `hCG (w.adicCompletion E) ψ hψc hψ1 (m + 1) σ.V σ.ρ hnt hσ`. Take `⟨L', hL', x1, hx1⟩` from `DzRed.exists_functional_ne i hi hψ' hψ₀ τ hτ σ.ρ σ.irr φ hφ' hφ0 L hL hL0`. Take `⟨l', v', hl', hlv', hv'⟩` from `hcell`.

Use `choose s hs using GlobalTheory.GLp.Model.red_surjective (g := g) m`. Take `⟨I, hI, -, hpos⟩` from `LConv.exists_pos_isInvIntegral (w.adicCompletion E) m`. Use `⟨L'.comp φ, DzRed.cellFun i τ₀.ρ l' v' s, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `u hu x`. Take `⟨κ, hred, hmem, hsd⟩` from `DzRed.exists_lift_unipB i hi hψ' hu`.

Simplify using `only [LinearMap.comp_apply]`. Use `conv_lhs => rw [← hred]`. Rewrite using `[hφ', hL' _ hmem, hsd]`. Introduce `h`. Conclude with `hx1 (LinearMap.congr_fun h x1)`.

Use `⟨fun u hu x => DzRed.cellFun_unip i hi hψ' τ₀.ρ l' v' hl' hv' s hs hu x, fun b hb x => DzRed.cellFun_lower i τ₀.ρ l' v' hv' s hs x b hb, ?_⟩` and prove the remaining obligations. Rewrite using `[DzRed.cellFun_one i τ₀.ρ l' v' hv' s hs]`. Conclude with `hlv'`. Introduce `v`. Establish `hPE : I (DzRed.FL σ.ρ τ₀.ρ L' l' (φ v) v') = (ω (-1) : ℂ) ^ m * e * I (DzRed.FR σ.ρ τ₀.ρ L' l' (φ v) v')` using `he ω hω L' l' hL' hl' I hI (φ v) v'`.

Establish `intL` using `DzRed.integral_eq i hi I hI (DzRed.FL σ.ρ τ₀.ρ L' l' (φ v) v') (fun u hu x => DzRed.FL_left σ.ρ τ₀.ρ L' l' hL' hl' _ _ hu x) (fun x k hk => DzRed.FL_right i hi τ σ.ρ τ₀.ρ L' l' φ hφ' v' hv' v x hk) (fun x hx => DzRed.FL_supp i hi τ σ.ρ τ₀.ρ L' l' φ hψ' hψ₀ hτ hφ' hL' hl' v' v x h …`. Establish `intR` using `DzRed.integral_eq i hi I hI (DzRed.FR σ.ρ τ₀.ρ L' l' (φ v) v') (fun u hu x => DzRed.FR_left σ.ρ τ₀.ρ L' l' hL' hl' _ _ hu x) (fun x k hk => DzRed.FR_right i hi τ σ.ρ τ₀.ρ L' l' φ hφ' v' hv' v x hk) (fun x hx => DzRed.FR_supp i hi τ σ.ρ τ₀.ρ L' l' φ hψ' hψ₀ hτ hφ' hL' hl' v' v x h …`. Establish `tL : ∀ κ : Gn g m, DzRed.FL σ.ρ τ₀.ρ L' l' (φ v) v' (Matrix.GeneralLinearGroup.map i.toRingHom (GlobalTheory.GLp.inc g m (s κ))) = (L'.comp φ) (τ.ρ (tilde (corner κ)) v) * DzRed.cellFun i τ₀.ρ l' v' s (tilde κ)`. Introduce `κ`. Unfold `DzRed.FL`.

Rewrite using `[← DzRed.phi_corner, ← DzRed.phi_tilde, ← hφ', ← DzRed.phi_tilde, DzRed.red_tilde, DzRed.red_corner, hs, ← DzRed.cellFun_eq i τ₀.ρ l' v' hv' s hs, DzRed.red_tilde, hs]`. Both sides reduce to the same expression. Establish `tR : ∀ κ : Gn g m, DzRed.FR σ.ρ τ₀.ρ L' l' (φ v) v' (Matrix.GeneralLinearGroup.map i.toRingHom (GlobalTheory.GLp.inc g m (s κ))) = (L'.comp φ) (τ.ρ (corner κ) v) * DzRed.cellFun i τ₀.ρ l' v' s κ`. Introduce `κ`. Unfold `DzRed.FR`.

Rewrite using `[← DzRed.phi_corner, ← hφ', DzRed.red_corner, hs]`. Both sides reduce to the same expression. Simplify using `only [tL, tR] at intL intR`. Establish `hT` using `DzRed.isTestFun_indicator_unipotentKOne (k := w.adicCompletion E) (m := m)`. Establish `hI1 : I (Set.indicator ((unipB (w.adicCompletion E) (Fin m) : Set _) * (KOne (w.adicCompletion E) (Fin m) : Set _)) 1) ≠ 0`.

Introduce `h0`. Establish `h1mem : (1 : GL (Fin m) (w.adicCompletion E)) ∈ ((unipB (w.adicCompletion E) (Fin m) : Set (GL (Fin m) (w.adicCompletion E))) * (KOne (w.adicCompletion E) (Fin m) : Set (GL (Fin m) (w.adicCompletion E))))` using `Set.mem_mul.2 ⟨1, one_mem _, 1, one_mem _, one_mul 1⟩`. Apply the tactic sequence `have := (hpos _ hT (fun x => by rw [Set.indicator_apply]; split_ifs <;> simp)).2 (by rw [h0]; simp) 1`. Rewrite `this` using `[Set.indicator_of_mem h1mem]`. Simplify using `at this`.

Rewrite using `[finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype]`. Use `mul_left_cancel₀ hI1 ?_` and prove the remaining obligations. Rewrite using `[← intL, hPE, mul_left_comm, intR]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem lRed : LRed := by
  intro hCG E _ _ w g _ i hi ψ₀ hψ₀ ψ hψc hψ m τ hτ σ hσ hinf τ₀ ω hω hcell e he
  obtain ⟨φ, hφ0, hφ⟩ := hinf
  have hφ' : ∀ (κ : GL (Fin (m + 1)) ℤ_[g]) (x : τ), φ (τ.ρ (GlobalTheory.GLp.red g (m + 1) κ) x) =
      σ.ρ (Matrix.GeneralLinearGroup.map i.toRingHom (GlobalTheory.GLp.inc g (m + 1) κ)) (φ x) := hφ
  have hψ' : ∀ x : ℤ_[g], ψ (i (x : ℚ_[g])) = ψ₀ (PadicInt.toZMod x) := hψ
  obtain ⟨x0, hx0⟩ := DzRed.exists_psi_ne_one i hψ' hψ₀
  have hψ1 : ψ ≠ 1 := fun h => hx0 (by rw [h, AddChar.one_apply])
  have hnt : Nontrivial σ.V := by
    obtain ⟨x, hx⟩ : ∃ x, φ x ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hφ0 (LinearMap.ext hc)
    exact ⟨⟨φ x, 0, hx⟩⟩
  obtain ⟨L, hL0, hL⟩ := hCG (w.adicCompletion E) ψ hψc hψ1 (m + 1) σ.V σ.ρ hnt hσ
  obtain ⟨L', hL', x1, hx1⟩ := DzRed.exists_functional_ne i hi hψ' hψ₀ τ hτ σ.ρ σ.irr φ hφ' hφ0 L hL hL0
  obtain ⟨l', v', hl', hlv', hv'⟩ := hcell
  choose s hs using GlobalTheory.GLp.Model.red_surjective (g := g) m
  obtain ⟨I, hI, -, hpos⟩ := LConv.exists_pos_isInvIntegral (w.adicCompletion E) m
  refine ⟨L'.comp φ, DzRed.cellFun i τ₀.ρ l' v' s, ?_, ?_, ?_, ?_⟩
  · intro u hu x
    obtain ⟨κ, hred, hmem, hsd⟩ := DzRed.exists_lift_unipB i hi hψ' hu
    simp only [LinearMap.comp_apply]
    conv_lhs => rw [← hred]
    rw [hφ', hL' _ hmem, hsd]
  · intro h
    exact hx1 (LinearMap.congr_fun h x1)
  · refine ⟨fun u hu x => DzRed.cellFun_unip i hi hψ' τ₀.ρ l' v' hl' hv' s hs hu x,
      fun b hb x => DzRed.cellFun_lower i τ₀.ρ l' v' hv' s hs x b hb, ?_⟩
    rw [DzRed.cellFun_one i τ₀.ρ l' v' hv' s hs]
    exact hlv'
  · classical
    intro v
    have hPE : I (DzRed.FL σ.ρ τ₀.ρ L' l' (φ v) v') =
        (ω (-1) : ℂ) ^ m * e * I (DzRed.FR σ.ρ τ₀.ρ L' l' (φ v) v') :=
      he ω hω L' l' hL' hl' I hI (φ v) v'
    have intL := DzRed.integral_eq i hi I hI (DzRed.FL σ.ρ τ₀.ρ L' l' (φ v) v')
      (fun u hu x => DzRed.FL_left σ.ρ τ₀.ρ L' l' hL' hl' _ _ hu x)
      (fun x k hk => DzRed.FL_right i hi τ σ.ρ τ₀.ρ L' l' φ hφ' v' hv' v x hk)
      (fun x hx => DzRed.FL_supp i hi τ σ.ρ τ₀.ρ L' l' φ hψ' hψ₀ hτ hφ' hL' hl' v' v x hx) s hs
    have intR := DzRed.integral_eq i hi I hI (DzRed.FR σ.ρ τ₀.ρ L' l' (φ v) v')
      (fun u hu x => DzRed.FR_left σ.ρ τ₀.ρ L' l' hL' hl' _ _ hu x)
      (fun x k hk => DzRed.FR_right i hi τ σ.ρ τ₀.ρ L' l' φ hφ' v' hv' v x hk)
      (fun x hx => DzRed.FR_supp i hi τ σ.ρ τ₀.ρ L' l' φ hψ' hψ₀ hτ hφ' hL' hl' v' v x hx) s hs
    have tL : ∀ κ : Gn g m, DzRed.FL σ.ρ τ₀.ρ L' l' (φ v) v'
        (Matrix.GeneralLinearGroup.map i.toRingHom (GlobalTheory.GLp.inc g m (s κ))) =
        (L'.comp φ) (τ.ρ (tilde (corner κ)) v) * DzRed.cellFun i τ₀.ρ l' v' s (tilde κ) := by
      intro κ
      unfold DzRed.FL
      rw [← DzRed.phi_corner, ← DzRed.phi_tilde, ← hφ', ← DzRed.phi_tilde, DzRed.red_tilde, DzRed.red_corner, hs,
        ← DzRed.cellFun_eq i τ₀.ρ l' v' hv' s hs, DzRed.red_tilde, hs]
      rfl
    have tR : ∀ κ : Gn g m, DzRed.FR σ.ρ τ₀.ρ L' l' (φ v) v'
        (Matrix.GeneralLinearGroup.map i.toRingHom (GlobalTheory.GLp.inc g m (s κ))) =
        (L'.comp φ) (τ.ρ (corner κ) v) * DzRed.cellFun i τ₀.ρ l' v' s κ := by
      intro κ
      unfold DzRed.FR
      rw [← DzRed.phi_corner, ← hφ', DzRed.red_corner, hs]
      rfl
    simp only [tL, tR] at intL intR
    have hT := DzRed.isTestFun_indicator_unipotentKOne (k := w.adicCompletion E) (m := m)
    have hI1 : I (Set.indicator ((unipB (w.adicCompletion E) (Fin m) : Set _) *
        (KOne (w.adicCompletion E) (Fin m) : Set _)) 1) ≠ 0 := by
      intro h0
      have h1mem : (1 : GL (Fin m) (w.adicCompletion E)) ∈
          ((unipB (w.adicCompletion E) (Fin m) : Set (GL (Fin m) (w.adicCompletion E))) *
          (KOne (w.adicCompletion E) (Fin m) : Set (GL (Fin m) (w.adicCompletion E)))) :=
        Set.mem_mul.2 ⟨1, one_mem _, 1, one_mem _, one_mul 1⟩
      have := (hpos _ hT (fun x => by rw [Set.indicator_apply]; split_ifs <;> simp)).2 (by rw [h0]; simp) 1
      rw [Set.indicator_of_mem h1mem] at this
      simp at this
    rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype]
    refine mul_left_cancel₀ hI1 ?_
    rw [← intL, hPE, mul_left_comm, intR]
    ring

end DiscreteGroups.sglob.DzType
