import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.ExistsHasInfCharGL

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin GlobalTheory.BCWords

namespace PositivityTheory.Rg.Rs.PInfInd2A

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

/- English proof (translation)
Use `tensorSp_of_tens2 W₁ W₂ hψ` as an intermediate fact. Use `this using 2 with m` and compare the differences between its conclusion and the goal. Rewrite using `[CapFactor.lev_eq_leviEmb n h, levPair_eta]`.
-/
theorem tensorSp_levi {n : Fin 2 → ℕ} (h : ∑ i, n i = n 0 + n 1) (W₁ : Submodule ℂ (Sm E (n 0)))
    (W₂ : Submodule ℂ (Sm E (n 1))) (ψ : Sm E (n 0 + n 1))
    (hψ : (fun p => ψ.1 (lev (Ad E) (n 0) (n 1) p)) ∈ tens2 W₁ W₂) :
    (fun m => ψ.1 (leviEmb (Ad E) (stdBlocks n h) m)) ∈ tensorSp (blkV W₁ W₂) := by
  have := tensorSp_of_tens2 W₁ W₂ hψ
  convert this using 2 with m
  rw [CapFactor.lev_eq_leviEmb n h, levPair_eta]

/- English proof (translation)
Establish `h : ∑ i, n i = n 0 + n 1` using `CapFactor.two_sum n`. Establish `key` using `GlobalTheory.NormIndCap.qdet_block_levi n h (blkV W₁ W₂) τ 0 M hM w ψ (tensorSp_levi h W₁ W₂ ψ hψ) (CapFactor.levPair p)`. Establish `e1 : (fun p q : Fin (n 0) => Eop (a` using `n 0 + n 1) τ (stdBlocks n h ⟨0, p⟩) (stdBlocks n h ⟨0, q⟩)) = fun p q => Eop (a := n 0 + n 1) τ (Fin.castAdd (n 1) p) (Fin.castAdd (n 1) q) := by`. Use function extensionality and compare the values at `p q`. Rewrite using `[CapFactor.std_zero, CapFactor.std_zero]`.

Rewrite `key` using `[e1, ← CapFactor.lev_eq_leviEmb n h]`. Conclude with `key`.
-/
theorem capR_lev {n : Fin 2 → ℕ} (W₁ : Submodule ℂ (Sm E (n 0))) (W₂ : Submodule ℂ (Sm E (n 1))) (τ : E →+* ℂ)
    (M : Multiset ℂ) (hM : HasInfCharGL W₁ τ M) (w : ℂ) (ψ : Sm E (n 0 + n 1))
    (hψ : (fun p => ψ.1 (lev (Ad E) (n 0) (n 1) p)) ∈ tens2 W₁ W₂) (p : GA E (n 0) × GA E (n 1)) :
    (capR (n 0) (n 1) τ w ψ).1 (lev (Ad E) (n 0) (n 1) p) = (M.map (w + ·)).prod * ψ.1 (lev (Ad E) (n 0) (n 1) p) := by
  have h : ∑ i, n i = n 0 + n 1 := CapFactor.two_sum n
  have key := GlobalTheory.NormIndCap.qdet_block_levi n h (blkV W₁ W₂) τ 0 M hM w ψ (tensorSp_levi h W₁ W₂ ψ hψ)
    (CapFactor.levPair p)
  have e1 : (fun p q : Fin (n 0) => Eop (a := n 0 + n 1) τ (stdBlocks n h ⟨0, p⟩) (stdBlocks n h ⟨0, q⟩)) =
      fun p q => Eop (a := n 0 + n 1) τ (Fin.castAdd (n 1) p) (Fin.castAdd (n 1) q) := by
    funext p q
    rw [CapFactor.std_zero, CapFactor.std_zero]
  rw [e1, ← CapFactor.lev_eq_leviEmb n h] at key
  exact key

/- English proof (translation)
Establish `h : ∑ i, n i = n 0 + n 1` using `CapFactor.two_sum n`. Establish `key` using `GlobalTheory.NormIndCap.qdet_block_levi n h (blkV W₁ W₂) τ 1 M hM w ψ (tensorSp_levi h W₁ W₂ ψ hψ) (CapFactor.levPair p)`. Establish `e1 : (fun p q : Fin (n 1) => Eop (a` using `n 0 + n 1) τ (stdBlocks n h ⟨1, p⟩) (stdBlocks n h ⟨1, q⟩)) = fun p q => Eop (a := n 0 + n 1) τ (Fin.natAdd (n 0) p) (Fin.natAdd (n 0) q) := by`. Use function extensionality and compare the values at `p q`. Rewrite using `[CapFactor.std_one, CapFactor.std_one]`.

Rewrite `key` using `[e1, ← CapFactor.lev_eq_leviEmb n h]`. Conclude with `key`.
-/
theorem capS_lev {n : Fin 2 → ℕ} (W₁ : Submodule ℂ (Sm E (n 0))) (W₂ : Submodule ℂ (Sm E (n 1))) (τ : E →+* ℂ)
    (M : Multiset ℂ) (hM : HasInfCharGL W₂ τ M) (w : ℂ) (ψ : Sm E (n 0 + n 1))
    (hψ : (fun p => ψ.1 (lev (Ad E) (n 0) (n 1) p)) ∈ tens2 W₁ W₂) (p : GA E (n 0) × GA E (n 1)) :
    (capS (n 0) (n 1) τ w ψ).1 (lev (Ad E) (n 0) (n 1) p) = (M.map (w + ·)).prod * ψ.1 (lev (Ad E) (n 0) (n 1) p) := by
  have h : ∑ i, n i = n 0 + n 1 := CapFactor.two_sum n
  have key := GlobalTheory.NormIndCap.qdet_block_levi n h (blkV W₁ W₂) τ 1 M hM w ψ (tensorSp_levi h W₁ W₂ ψ hψ)
    (CapFactor.levPair p)
  have e1 : (fun p q : Fin (n 1) => Eop (a := n 0 + n 1) τ (stdBlocks n h ⟨1, p⟩) (stdBlocks n h ⟨1, q⟩)) =
      fun p q => Eop (a := n 0 + n 1) τ (Fin.natAdd (n 0) p) (Fin.natAdd (n 0) q) := by
    funext p q
    rw [CapFactor.std_one, CapFactor.std_one]
  rw [e1, ← CapFactor.lev_eq_leviEmb n h] at key
  exact key

/- English proof (translation)
Establish `h : ∑ i, n i = n 0 + n 1` using `CapFactor.two_sum n`. Use `set c := (M₁.map (u - (n 1 : ℂ) / 2 + ·)).prod * (M₂.map (u + (n 0 : ℂ) / 2 + ·)).prod with hc`. Establish `hlev : ∀ ψ : Sm E (n 0 + n 1), (∀ (x : BlockIx (n 0 + n 1) (n 0) → Ad E) g, ψ.1 (unip x * g) = ψ.1 g) → (fun p => ψ.1 (lev (Ad E) (n 0) (n 1) p)) ∈ tens2 W₁ W₂ → ∀ p, (cap τ u ψ).1 (lev (Ad E) (n 0) (n 1) p) = c * ψ.1 (lev (Ad E) (n 0) (n 1) p)`. Introduce `ψ hψ hT p`. Rewrite using `[CapFactor.cap_levi E (n 0) (n 1) τ u ψ hψ p]`.

Establish `hT' : (fun p => (capR (n 0) (n 1) τ (u - (n 1 : ℂ) / 2) ψ).1 (lev (Ad E) (n 0) (n 1) p)) ∈ tens2 W₁ W₂`. Establish `e : (fun p => (capR (n 0) (n 1) τ (u - (n 1 : ℂ) / 2) ψ).1 (lev (Ad E) (n 0) (n 1) p)) = (M₁.map (u - (n 1 : ℂ) / 2 + ·)).prod • (fun p => ψ.1 (lev (Ad E) (n 0) (n 1) p))`. Use function extensionality and compare the values at `fun p => capR_lev W₁ W₂ τ M₁ h₁ _ ψ hT p`. Rewrite using `[e]`. Conclude with `Submodule.smul_mem _ _ hT`.

Rewrite using `[capS_lev W₁ W₂ τ M₂ h₂ _ _ hT' p, capR_lev W₁ W₂ τ M₁ h₁ _ ψ hT p, hc]`. Expand and normalize the polynomial expressions, which then agree. Use `Subtype.ext (funext fun x => ?_)` and prove the remaining obligations. Take `⟨v, hv, m, k, g, rfl⟩` from `GlobalTheory.SpehInfChar.exists_iwasawa E n h x`. Take `⟨xv, rfl⟩` from `CapFactor.exists_unip_of_mem n h hv`.

Establish `hx : leviEmb (Ad E) (stdBlocks n h) m = lev (Ad E) (n 0) (n 1) (m 0, m 1)`. Rewrite using `[CapFactor.lev_eq_leviEmb n h, levPair_eta]`. Rewrite using `[hx]`. Use `set y := infGL E (n 0 + n 1) (Unitary.toUnits k) * finGL E (n 0 + n 1) g`. Establish `hcomm : Commute (cap τ u) (rt E (n 0 + n 1) y)`.

Rewrite using `[map_mul]`. Conclude with `(GlobalTheory.CapAdInv.cap_commute_rt_infGL E _ τ u _).mul_right (commute_cap_finRep τ u g)`. Use `set ψ := rt E (n 0 + n 1) y F`. Establish `hψ : ∀ (x : BlockIx (n 0 + n 1) (n 0) → Ad E) g', ψ.1 (unip x * g') = ψ.1 g'` using `fun x g' => by`. Simplify using `only [ψ, rt_apply, mul_assoc]`.

Conclude with `hF.1 x _`. Establish `hψT : (fun p => ψ.1 (lev (Ad E) (n 0) (n 1) p)) ∈ tens2 W₁ W₂` using `hF.2 k g`. Establish `h3` using `hlev ψ hψ hψT (m 0, m 1)`. Establish `h4 : (cap τ u ψ).1 (lev (Ad E) (n 0) (n 1) (m 0, m 1)) = (cap τ u F).1 (lev (Ad E) (n 0) (n 1) (m 0, m 1) * y)`. Rewrite using `[← rt_apply, ← Module.End.mul_apply, hcomm.eq]`.

Both sides reduce to the same expression. Establish `hcapInv` using `(CapStable.capStable E (n 0) (n 1) τ u F).2 hF.1`. Rewrite using `[mul_assoc, hcapInv, ← h4, h3]`. Simplify using `only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, ψ, rt_apply]`. Rewrite using `[hF.1]`.
-/
theorem casimir_on_parabolic_induction {n : Fin 2 → ℕ} (W₁ : Submodule ℂ (Sm E (n 0))) (W₂ : Submodule ℂ (Sm E (n 1))) (τ : E →+* ℂ)
    (M₁ M₂ : Multiset ℂ) (h₁ : HasInfCharGL W₁ τ M₁) (h₂ : HasInfCharGL W₂ τ M₂) (u : ℂ) (F : Sm E (n 0 + n 1))
    (hF : MemInd2 W₁ W₂ F) :
    cap τ u F = ((M₁.map (u - (n 1 : ℂ) / 2 + ·)).prod * (M₂.map (u + (n 0 : ℂ) / 2 + ·)).prod) • F := by
  have h : ∑ i, n i = n 0 + n 1 := CapFactor.two_sum n
  set c := (M₁.map (u - (n 1 : ℂ) / 2 + ·)).prod * (M₂.map (u + (n 0 : ℂ) / 2 + ·)).prod with hc
  have hlev : ∀ ψ : Sm E (n 0 + n 1), (∀ (x : BlockIx (n 0 + n 1) (n 0) → Ad E) g, ψ.1 (unip x * g) = ψ.1 g) →
      (fun p => ψ.1 (lev (Ad E) (n 0) (n 1) p)) ∈ tens2 W₁ W₂ → ∀ p,
      (cap τ u ψ).1 (lev (Ad E) (n 0) (n 1) p) = c * ψ.1 (lev (Ad E) (n 0) (n 1) p) := by
    intro ψ hψ hT p
    rw [CapFactor.cap_levi E (n 0) (n 1) τ u ψ hψ p]
    have hT' : (fun p => (capR (n 0) (n 1) τ (u - (n 1 : ℂ) / 2) ψ).1 (lev (Ad E) (n 0) (n 1) p)) ∈ tens2 W₁ W₂ := by
      have e : (fun p => (capR (n 0) (n 1) τ (u - (n 1 : ℂ) / 2) ψ).1 (lev (Ad E) (n 0) (n 1) p)) =
          (M₁.map (u - (n 1 : ℂ) / 2 + ·)).prod • (fun p => ψ.1 (lev (Ad E) (n 0) (n 1) p)) :=
        funext fun p => capR_lev W₁ W₂ τ M₁ h₁ _ ψ hT p
      rw [e]
      exact Submodule.smul_mem _ _ hT
    rw [capS_lev W₁ W₂ τ M₂ h₂ _ _ hT' p, capR_lev W₁ W₂ τ M₁ h₁ _ ψ hT p, hc]
    ring
  refine Subtype.ext (funext fun x => ?_)
  obtain ⟨v, hv, m, k, g, rfl⟩ := GlobalTheory.SpehInfChar.exists_iwasawa E n h x
  obtain ⟨xv, rfl⟩ := CapFactor.exists_unip_of_mem n h hv
  have hx : leviEmb (Ad E) (stdBlocks n h) m = lev (Ad E) (n 0) (n 1) (m 0, m 1) := by
    rw [CapFactor.lev_eq_leviEmb n h, levPair_eta]
  rw [hx]
  set y := infGL E (n 0 + n 1) (Unitary.toUnits k) * finGL E (n 0 + n 1) g
  have hcomm : Commute (cap τ u) (rt E (n 0 + n 1) y) := by
    rw [map_mul]
    exact (GlobalTheory.CapAdInv.cap_commute_rt_infGL E _ τ u _).mul_right (commute_cap_finRep τ u g)
  set ψ := rt E (n 0 + n 1) y F
  have hψ : ∀ (x : BlockIx (n 0 + n 1) (n 0) → Ad E) g', ψ.1 (unip x * g') = ψ.1 g' := fun x g' => by
    simp only [ψ, rt_apply, mul_assoc]
    exact hF.1 x _
  have hψT : (fun p => ψ.1 (lev (Ad E) (n 0) (n 1) p)) ∈ tens2 W₁ W₂ := hF.2 k g
  have h3 := hlev ψ hψ hψT (m 0, m 1)
  have h4 : (cap τ u ψ).1 (lev (Ad E) (n 0) (n 1) (m 0, m 1)) =
      (cap τ u F).1 (lev (Ad E) (n 0) (n 1) (m 0, m 1) * y) := by
    rw [← rt_apply, ← Module.End.mul_apply, hcomm.eq]
    rfl
  have hcapInv := (CapStable.capStable E (n 0) (n 1) τ u F).2 hF.1
  rw [mul_assoc, hcapInv, ← h4, h3]
  simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, ψ, rt_apply]
  rw [hF.1]

end PositivityTheory.Rg.Rs.PInfInd2A

end
