import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ResidueFlagPoints.ResLeMemDec
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AutomorphicCharacters.AuCont

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

attribute [-instance] UpperTheory.V.UnitaryThreeInertia.Coef.isLocalRing in
/- English proof (translation)
Introduce `Ω _ _ _ l _ c D T c' h K X B n φ hφ y x hx hcont v i`. Establish `hxe : x = Link.pt φ y` using `AlgHom.ext fun b => hx b`. Substitute `hxe` using the available equality. Establish `hκc` using `auCont c' K.κ K.κ_cont`. Establish `hβc` using `auCont c' K.β K.β_cont`.

Establish `htw : Continuous fun g : G (↥T.L) Ω => ((K.twc n g : (PadicAlgCl l)ˣ) : PadicAlgCl l)`. Establish `he : (fun g : G (↥T.L) Ω => ((K.twc n g : (PadicAlgCl l)ˣ) : PadicAlgCl l)) = fun g => ((W.pushCh (algebraMap c'.O (PadicAlgCl l)) K.κ g : (PadicAlgCl l)ˣ) : PadicAlgCl l) * ((W.pushCh (algebraMap c'.O (PadicAlgCl l)) K.β g : (PadicAlgCl l)ˣ) : PadicAlgCl l) ^ n`. Use function extensionality and compare the values at `g`. Rewrite using `[K.twc_val]`. Simplify using `[W.pushCh]`.

Rewrite using `[he]`. Conclude with `(Units.continuous_val.comp hκc).mul ((Units.continuous_val.comp hβc).pow n)`. Establish `hval : Continuous fun g : ↥(Dec (K.s.A ↑v)) => (((Link.pt φ y).psi v i g : (PadicAlgCl l)ˣ) : PadicAlgCl l)`. Establish `heq : (fun g : ↥(Dec (K.s.A ↑v)) => (((Link.pt φ y).psi v i g : (PadicAlgCl l)ˣ) : PadicAlgCl l)) = fun g : ↥(Dec (K.s.A ↑v)) => ((K.twc n (g : G (↥T.L) Ω) : (PadicAlgCl l)ˣ) : PadicAlgCl l) * (X.P.map ↑y).ψ (K.e v) i (resLe T.F_le (g : G (↥T.L) Ω))`. Use function extensionality and compare the values at `g`.

Apply `hφ.psi_val y v i g` to reduce the goal to its premises. Rewrite using `[resLe_mem_Dec, ← K.hA v]`. Conclude with `g.2`. Rewrite using `[heq]`. Use `(htw.comp continuous_subtype_val).mul ?_` and prove the remaining obligations.

Unfold `PD.ψ`. Conclude with `((continuous_const.matrix_mul (hcont.comp continuous_subtype_val)).matrix_mul continuous_const).matrix_elem i i`. Rewrite using `[Units.continuous_iff]`. Use `⟨hval, ?_⟩` and prove the remaining obligations. Establish `hinv : (fun g : ↥(Dec (K.s.A ↑v)) => ((((Link.pt φ y).psi v i g)⁻¹ : (PadicAlgCl l)ˣ) : PadicAlgCl l)) = fun g => (((Link.pt φ y).psi v i g⁻¹ : (PadicAlgCl l)ˣ) : PadicAlgCl l)`.

Use function extensionality and compare the values at `g`. Rewrite using `[map_inv]`. Rewrite using `[hinv]`. Conclude with `hval.comp continuous_inv`.
-/
theorem UpperTheory.V.Ws.auPsiCont :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D) (c' : Coef l) (h : c.O ≤ c'.O) (K : Link T c' h) (X : Space (T.fr ∅) (inc h)) (B : W.UniversalOrdinaryDeterminantRing K.r) (n : ℕ) (φ : B.B →ₐ[c'.O] X.B), K.IsPhi X n B φ → ∀ (y : X.A →ₐ[c'.O] PadicAlgCl l) (x : B.Pt), (∀ b, x b = y (algebraMap X.B X.A (φ b))) → Continuous ((X.P.map (y : X.A →+* PadicAlgCl l)).r.comp (resLe T.F_le)) → ∀ (v : W.Vl l T.L) (i : Fin 4), Continuous (x.psi v i) := by
  intro Ω _ _ _ l _ c D T c' h K X B n φ hφ y x hx hcont v i
  have hxe : x = Link.pt φ y := AlgHom.ext fun b => hx b
  subst hxe
  have hκc := auCont c' K.κ K.κ_cont
  have hβc := auCont c' K.β K.β_cont
  have htw : Continuous fun g : G (↥T.L) Ω => ((K.twc n g : (PadicAlgCl l)ˣ) : PadicAlgCl l) := by
    have he : (fun g : G (↥T.L) Ω => ((K.twc n g : (PadicAlgCl l)ˣ) : PadicAlgCl l)) = fun g =>
        ((W.pushCh (algebraMap c'.O (PadicAlgCl l)) K.κ g : (PadicAlgCl l)ˣ) : PadicAlgCl l) *
          ((W.pushCh (algebraMap c'.O (PadicAlgCl l)) K.β g : (PadicAlgCl l)ˣ) : PadicAlgCl l) ^ n := by
      funext g
      rw [K.twc_val]
      simp [W.pushCh]
    rw [he]
    exact (Units.continuous_val.comp hκc).mul ((Units.continuous_val.comp hβc).pow n)
  have hval : Continuous fun g : ↥(Dec (K.s.A ↑v)) =>
      (((Link.pt φ y).psi v i g : (PadicAlgCl l)ˣ) : PadicAlgCl l) := by
    have heq : (fun g : ↥(Dec (K.s.A ↑v)) => (((Link.pt φ y).psi v i g : (PadicAlgCl l)ˣ) : PadicAlgCl l)) =
        fun g : ↥(Dec (K.s.A ↑v)) => ((K.twc n (g : G (↥T.L) Ω) : (PadicAlgCl l)ˣ) : PadicAlgCl l) *
          (X.P.map ↑y).ψ (K.e v) i (resLe T.F_le (g : G (↥T.L) Ω)) := by
      funext g
      apply hφ.psi_val y v i g
      rw [resLe_mem_Dec, ← K.hA v]
      exact g.2
    rw [heq]
    refine (htw.comp continuous_subtype_val).mul ?_
    unfold PD.ψ
    exact ((continuous_const.matrix_mul (hcont.comp continuous_subtype_val)).matrix_mul
      continuous_const).matrix_elem i i
  rw [Units.continuous_iff]
  refine ⟨hval, ?_⟩
  have hinv : (fun g : ↥(Dec (K.s.A ↑v)) => ((((Link.pt φ y).psi v i g)⁻¹ : (PadicAlgCl l)ˣ) : PadicAlgCl l)) =
      fun g => (((Link.pt φ y).psi v i g⁻¹ : (PadicAlgCl l)ˣ) : PadicAlgCl l) := by
    funext g
    rw [map_inv]
  rw [hinv]
  exact hval.comp continuous_inv
