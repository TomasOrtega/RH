import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.FinMulSupp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.ScalarTuples.JstdTrace

open NumberField UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob

/- English proof (translation)
Introduce `F _ _ Δ D hD ι hι t ht τ hτ γ j hγ hj`. Use `haveI := hD.real`. Establish `hreg : τ ^ 2 - 4 ≠ 0` using `cm_ne hτ`. Establish `htr : ∀ (g : DX Δ) (v : Pl F), HasTr g τ → HasTr ((ι g).1 v) (cv v τ)` using `fun g v hg => hasTr_map (cv v) (hι g v) hg`. Distinguish the cases in `hA : D.admitted t τ`.

Rewrite using `[show one (D.admitted t τ) = 1 from if_pos hA, one_mul]`. Use `gqD D hD ι hι t ht τ hτ hA γ j hγ hj γ (D.fSv t) ?_ (fun v => ((D.S v).cS : ℂ)) (fun v => gOrb (Ov v) (jstd ((cv v) τ)) 1 (toUnit QuadraticAlgebra.omega)) ?_` and prove the remaining obligations. Introduce `v u hu x`. Distinguish the cases in `hv : v ∈ D.Sg`. Establish `hS` using `hD.sig v hv`.

Establish `hu' : u ∈ (D.S v).J2` using `by simpa [Dat.J2v, hv] using hu`. Simplify using `only [Dat.fSv, if_pos hv]`. Rewrite using `[(hS.S_inv (t v) (ht v hv) u hu' _).2, (hS.S_inv (t v) (ht v hv) u⁻¹ (inv_mem hu') _).1]`. Establish `hu' : u ∈ KD ((cv v) Δ) (Ov v)` using `by simpa [Dat.J2v, hv] using hu`. Establish `hiff : u⁻¹ * x * u ∈ KD ((cv v) Δ) (Ov v) ↔ x ∈ KD ((cv v) Δ) (Ov v)`.

Rewrite using `[(KD ((cv v) Δ) (Ov v)).mul_mem_cancel_right hu', (KD ((cv v) Δ) (Ov v)).mul_mem_cancel_left (inv_mem hu')]`. Simplify using `only [Dat.fSv, if_neg hv, one]`. Distinguish the cases in `hx : x ∈ KD ((cv v) Δ) (Ov v)`. Rewrite using `[if_pos hx, if_pos (hiff.2 hx)]`. Rewrite using `[if_neg hx, if_neg (fun h => hx (hiff.1 h))]`.

Introduce `v jv hjv`. Establish `hgv : HasTr ((ι γ).1 v) (cv v τ)` using `htr γ v hγ`. Establish `hrv` using `cv_reg hreg v`. Take `⟨z, hz⟩` from `zEx hrv`. Use `⟨emb_comm hjv, ?_⟩` and prove the remaining obligations.

Distinguish the cases in `hv : v ∈ D.Sg`. Establish `hS` using `hD.sig v hv`. Take `⟨hF, -, hO, -, -⟩` from `hS.D_orb (t v) (ht v hv) _ _ jv hrv hgv hjv z hz`. Establish `e1 : D.fSv t v = (D.S v).fS (t v)`. Use function extensionality and compare the values at `g`.

Simplify using `[Dat.fSv, hv]`. Establish `e2 : D.J2v v = (D.S v).J2` using `by simp [Dat.J2v, hv]`. Rewrite using `[e1, e2]`. Use `⟨hF, fun _ => ?_, fun h => absurd hv h⟩` and prove the remaining obligations. Rewrite using `[hO, show one (Ind _ _ _) = 1 from if_pos (hA v hv), mul_one]`.

Establish `hL` using `hD.off v hv`. Establish `e1 : D.fSv t v = fun g => one (g ∈ KD ((cv v) Δ) (Ov v))`. Use function extensionality and compare the values at `g`. Simplify using `[Dat.fSv, hv]`. Establish `e2 : D.J2v v = KD ((cv v) Δ) (Ov v)` using `by simp [Dat.J2v, hv]`.

Rewrite using `[e1, e2]`. Use `⟨(finD _ _ _ _ hL hrv _ jv hgv hjv).1, fun h => absurd h hv, fun _ => ⟨(locD _ _ _ _ hL hrv _ jv hgv hjv (D.χ v) (hD.chi v).1 z hz).1, fun hK hu => ⟨if_pos hK, fun y hy => ?_⟩⟩⟩` and prove the remaining obligations. Establish `hy' : y⁻¹ * (ι γ).1 v * y ∈ ZD ((cv v) Δ) ⊔ KD ((cv v) Δ) (Ov v)`. Assume the negation of the conclusion as `hn`. Conclude with `hy (if_neg (fun h => hn (le_sup_right (a := ZD ((cv v) Δ)) h)))`.

Conclude with `(oneD _ _ _ _ hL hrv _ jv hgv hjv hK hu).2.1 y hy'`. Rewrite using `[show one (D.admitted t τ) = 0 from if_neg hA, zero_mul, mul_zero]`. Apply `gqOn_zero` to reduce the goal to its premises. Introduce `y`. Choose the witnesses or unpack the hypotheses as in `⟨v, hv, hI⟩ : ∃ v ∈ D.Sg, ¬ Ind (D.S v).H ((cv v) τ) (t v) := by`.

Simplify `hA` using `[Dat.admitted]`. Establish `heq : ((Quotient.out y)⁻¹ * ι γ * Quotient.out y).1 v = ((Quotient.out y).1 v)⁻¹ * (ι γ).1 v * (Quotient.out y).1 v` using `rfl`. Establish `hgtr : HasTr (((Quotient.out y)⁻¹ * ι γ * Quotient.out y).1 v) (cv v τ)`. Rewrite using `[heq]`. Conclude with `hasTr_conj (htr γ v hγ) _`.

Establish `hz : D.fSv t v (((Quotient.out y)⁻¹ * ι γ * Quotient.out y).1 v) = 0`. Simplify using `only [Dat.fSv, if_pos hv]`. Assume the negation of the conclusion as `hne`. Conclude with `hI ((hD.sig v hv).S_supp (t v) (ht v hv) _ _ hgtr hne)`. Conclude with `fin_mulSupp (D.fSv t) D.Sg (fun w hw k hk => by simp [Dat.fSv, hw, one, hk]) _ hz`.
-/
theorem UpperTheory.V.Z.Sym.Glob.gqS :
    UpperTheory.V.Z.Sym.Glob.GqS := by
  intro F _ _ Δ D hD ι hι t ht τ hτ γ j hγ hj
  haveI := hD.real
  have hreg : τ ^ 2 - 4 ≠ 0 := cm_ne hτ
  have htr : ∀ (g : DX Δ) (v : Pl F), HasTr g τ → HasTr ((ι g).1 v) (cv v τ) :=
    fun g v hg => hasTr_map (cv v) (hι g v) hg
  by_cases hA : D.admitted t τ
  · rw [show one (D.admitted t τ) = 1 from if_pos hA, one_mul]
    refine gqD D hD ι hι t ht τ hτ hA γ j hγ hj γ (D.fSv t) ?_ (fun v => ((D.S v).cS : ℂ))
      (fun v => gOrb (Ov v) (jstd ((cv v) τ)) 1 (toUnit QuadraticAlgebra.omega)) ?_
    · intro v u hu x
      by_cases hv : v ∈ D.Sg
      · have hS := hD.sig v hv
        have hu' : u ∈ (D.S v).J2 := by simpa [Dat.J2v, hv] using hu
        simp only [Dat.fSv, if_pos hv]
        rw [(hS.S_inv (t v) (ht v hv) u hu' _).2, (hS.S_inv (t v) (ht v hv) u⁻¹ (inv_mem hu') _).1]
      · have hu' : u ∈ KD ((cv v) Δ) (Ov v) := by simpa [Dat.J2v, hv] using hu
        have hiff : u⁻¹ * x * u ∈ KD ((cv v) Δ) (Ov v) ↔ x ∈ KD ((cv v) Δ) (Ov v) := by
          rw [(KD ((cv v) Δ) (Ov v)).mul_mem_cancel_right hu',
            (KD ((cv v) Δ) (Ov v)).mul_mem_cancel_left (inv_mem hu')]
        simp only [Dat.fSv, if_neg hv, one]
        by_cases hx : x ∈ KD ((cv v) Δ) (Ov v)
        · rw [if_pos hx, if_pos (hiff.2 hx)]
        · rw [if_neg hx, if_neg (fun h => hx (hiff.1 h))]
    · intro v jv hjv
      have hgv : HasTr ((ι γ).1 v) (cv v τ) := htr γ v hγ
      have hrv := cv_reg hreg v
      obtain ⟨z, hz⟩ := zEx hrv
      refine ⟨emb_comm hjv, ?_⟩
      by_cases hv : v ∈ D.Sg
      · have hS := hD.sig v hv
        obtain ⟨hF, -, hO, -, -⟩ := hS.D_orb (t v) (ht v hv) _ _ jv hrv hgv hjv z hz
        have e1 : D.fSv t v = (D.S v).fS (t v) := by
          funext g
          simp [Dat.fSv, hv]
        have e2 : D.J2v v = (D.S v).J2 := by simp [Dat.J2v, hv]
        rw [e1, e2]
        refine ⟨hF, fun _ => ?_, fun h => absurd hv h⟩
        rw [hO, show one (Ind _ _ _) = 1 from if_pos (hA v hv), mul_one]
      · have hL := hD.off v hv
        have e1 : D.fSv t v = fun g => one (g ∈ KD ((cv v) Δ) (Ov v)) := by
          funext g
          simp [Dat.fSv, hv]
        have e2 : D.J2v v = KD ((cv v) Δ) (Ov v) := by simp [Dat.J2v, hv]
        rw [e1, e2]
        refine ⟨(finD _ _ _ _ hL hrv _ jv hgv hjv).1, fun h => absurd h hv, fun _ =>
          ⟨(locD _ _ _ _ hL hrv _ jv hgv hjv (D.χ v) (hD.chi v).1 z hz).1, fun hK hu =>
            ⟨if_pos hK, fun y hy => ?_⟩⟩⟩
        have hy' : y⁻¹ * (ι γ).1 v * y ∈ ZD ((cv v) Δ) ⊔ KD ((cv v) Δ) (Ov v) := by
          by_contra hn
          exact hy (if_neg (fun h => hn (le_sup_right (a := ZD ((cv v) Δ)) h)))
        exact (oneD _ _ _ _ hL hrv _ jv hgv hjv hK hu).2.1 y hy'
  · rw [show one (D.admitted t τ) = 0 from if_neg hA, zero_mul, mul_zero]
    apply gqOn_zero
    intro y
    obtain ⟨v, hv, hI⟩ : ∃ v ∈ D.Sg, ¬ Ind (D.S v).H ((cv v) τ) (t v) := by
      simpa [Dat.admitted] using hA
    have heq : ((Quotient.out y)⁻¹ * ι γ * Quotient.out y).1 v =
        ((Quotient.out y).1 v)⁻¹ * (ι γ).1 v * (Quotient.out y).1 v := rfl
    have hgtr : HasTr (((Quotient.out y)⁻¹ * ι γ * Quotient.out y).1 v) (cv v τ) := by
      rw [heq]
      exact hasTr_conj (htr γ v hγ) _
    have hz : D.fSv t v (((Quotient.out y)⁻¹ * ι γ * Quotient.out y).1 v) = 0 := by
      simp only [Dat.fSv, if_pos hv]
      by_contra hne
      exact hI ((hD.sig v hv).S_supp (t v) (ht v hv) _ _ hgtr hne)
    exact fin_mulSupp (D.fSv t) D.Sg (fun w hw k hk => by simp [Dat.fSv, hw, one, hk]) _ hz
