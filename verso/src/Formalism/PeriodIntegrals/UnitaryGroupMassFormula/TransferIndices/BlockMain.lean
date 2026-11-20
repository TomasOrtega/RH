import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TransferIndices.BlockHyp

noncomputable section

namespace PI.Dv.TIW

open Formalism.BasicNotions NumberField IsDedekindDomain PI.Dv

section Side

variable {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] {n : ℕ} {X Y : Submodule K V} {Φ Ψ : Fin n → V →ₗ[K] V}
  {Γ : Matrix (Fin n) (Fin n) K}

/- English proof (translation)
Use `set LX := L ⊓ X.restrictScalars (𝓞 K) with hLXd`. Use `set LY := L ⊓ Y.restrictScalars (𝓞 K) with hLYd`. Establish `hLX : Submodule.span K (LX : Set V) = X` using `cut_span L hLsp X`. Establish `hLY : Submodule.span K (LY : Set V) = Y` using `cut_span L hLsp Y`. Establish `fgLX : LX.FG` using `fg_cut L hL X`.

Establish `fgLY : LY.FG` using `fg_cut L hL Y`. Use `set LP := latPow (Fin n) LX with hLPd`. Establish `fgLP : LP.FG` using `Submodule.fg_pi fun _ => fgLX`. Establish `hLPsp : Submodule.span K (LP : Set (Fin n → V)) = Submodule.pi Set.univ fun _ : Fin n => X`. Rewrite using `[hLPd, span_latPow, hLX]`.

Establish `hLPX : ∀ x ∈ LP, x ∈ Submodule.pi Set.univ fun _ : Fin n => X` using `fun x hx i _ => (Submodule.mem_inf.mp (hx i (Set.mem_univ i))).2`. Use `set A := LP.map ((Φt Φ).restrictScalars (𝓞 K)) with hAd`. Establish `fgA : A.FG` using `fgLP.map _`. Establish `hAle : A ≤ LY`. Introduce and unpack `_ ⟨x, hx, rfl⟩`.

Use `Submodule.mem_inf.mpr ⟨?_, H.phi_mem x (hLPX x hx)⟩` and prove the remaining obligations. Simplify using `only [LinearMap.coe_restrictScalars, Φt_apply]`. Conclude with `L.sum_mem fun i _ => hΦL i (x i) (Submodule.mem_inf.mp (hx i (Set.mem_univ i))).1 (Submodule.mem_inf.mp (hx i (Set.mem_univ i))).2`. Establish `hAsp : Submodule.span K (A : Set V) = Y`. Rewrite using `[hAd, Submodule.map_coe, LinearMap.coe_restrictScalars, Submodule.span_image, hLPsp, H.map_phi]`.

Use `⟨hAle, hAsp, idx_nonneg_of_le hI w LY A fgLY fgA (hLY.trans hAsp.symm) hAle, ?_⟩` and prove the remaining obligations. Use `set Bt := LY.map ((LinearMap.pi Ψ).restrictScalars (𝓞 K)) with hBtd`. Establish `fgBt : Bt.FG` using `fgLY.map _`. Establish `hBle : Bt ≤ LP`. Introduce and unpack `_ ⟨y, hy, rfl⟩ j _`.

Establish `hy'` using `Submodule.mem_inf.mp hy`. Conclude with `Submodule.mem_inf.mpr ⟨hΨL j y hy'.1 hy'.2, H.h3 j y hy'.2⟩`. Establish `hBsp : Submodule.span K (Bt : Set (Fin n → V)) = Submodule.pi Set.univ fun _ : Fin n => X`. Rewrite using `[hBtd, Submodule.map_coe, LinearMap.coe_restrictScalars, Submodule.span_image, hLY, H.map_psi]`. Establish `hΨA : A.map ((LinearMap.pi Ψ).restrictScalars (𝓞 K)) = LP.map ((matV Γ).restrictScalars (𝓞 K))`.

Rewrite using `[hAd, ← Submodule.map_comp]`. Use extensionality with `z`. Simplify using `only [Submodule.mem_map, LinearMap.coe_comp, LinearMap.coe_restrictScalars, Function.comp_apply]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, hx, rfl⟩`.

Conclude with `⟨x, hx, (H.psiPhi x (hLPX x hx)).symm⟩`. Introduce and unpack `⟨x, hx, rfl⟩`. Conclude with `⟨x, hx, H.psiPhi x (hLPX x hx)⟩`. Establish `hmat` using `idx_matV hI w LX fgLX Γ H.det`. Rewrite `hmat` using `[← hLPd, ← hΨA]`.

Establish `hΨAsp : Submodule.span K ((A.map ((LinearMap.pi Ψ).restrictScalars (𝓞 K)) : Submodule (𝓞 K) (Fin n → V)) : Set (Fin n → V)) = Submodule.pi Set.univ fun _ : Fin n => X`. Rewrite using `[hΨA]`. Conclude with `span_map_matV Γ H.det LP X hLPsp`. Establish `hch` using `idx_chain hI w LP Bt (A.map ((LinearMap.pi Ψ).restrictScalars (𝓞 K))) fgLP fgBt (fgA.map _) (by rw [hLPsp, hBsp]) (by rw [hΨAsp, hBsp])`. Establish `hinj` using `idx_map_inj hI w (LinearMap.pi Ψ) LY A fgLY fgA (hLY.trans hAsp.symm) (fun y hy h0 => H.psi_inj y (Submodule.mem_inf.mp hy).2 h0) (fun y hy h0 => H.psi_inj y (Submodule.mem_inf.mp (hAle hy)).2 h0)`.

Establish `hnn` using `idx_nonneg_of_le hI w LP Bt fgLP fgBt (by rw [hLPsp, hBsp]) hBle`. Rewrite `hinj` using `[← hBtd]`. Rewrite `hch` using `[hmat, ← hinj]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem BlockHyp.side (hI : IdxCalc) (w : HeightOneSpectrum (𝓞 K)) (H : BlockHyp X Y Φ Ψ Γ)
    (L : Submodule (𝓞 K) V) (hL : L.FG) (hLsp : Submodule.span K (L : Set V) = ⊤)
    (hΦL : ∀ i, ∀ x ∈ L, x ∈ X → Φ i x ∈ L) (hΨL : ∀ j, ∀ y ∈ L, y ∈ Y → Ψ j y ∈ L) :
    (latPow (Fin n) (L ⊓ X.restrictScalars (𝓞 K))).map ((Φt Φ).restrictScalars (𝓞 K)) ≤
        L ⊓ Y.restrictScalars (𝓞 K) ∧
      Submodule.span K (((latPow (Fin n) (L ⊓ X.restrictScalars (𝓞 K))).map
        ((Φt Φ).restrictScalars (𝓞 K)) : Submodule (𝓞 K) V) : Set V) = Y ∧
      0 ≤ idxAt w (L ⊓ Y.restrictScalars (𝓞 K))
        ((latPow (Fin n) (L ⊓ X.restrictScalars (𝓞 K))).map ((Φt Φ).restrictScalars (𝓞 K))) ∧
      idxAt w (L ⊓ Y.restrictScalars (𝓞 K))
        ((latPow (Fin n) (L ⊓ X.restrictScalars (𝓞 K))).map ((Φt Φ).restrictScalars (𝓞 K))) ≤
        (Formalism.HN.rkK (L ⊓ X.restrictScalars (𝓞 K)) : ℤ) * vAdd w Γ.det := by
  set LX := L ⊓ X.restrictScalars (𝓞 K) with hLXd
  set LY := L ⊓ Y.restrictScalars (𝓞 K) with hLYd
  have hLX : Submodule.span K (LX : Set V) = X := cut_span L hLsp X
  have hLY : Submodule.span K (LY : Set V) = Y := cut_span L hLsp Y
  have fgLX : LX.FG := fg_cut L hL X
  have fgLY : LY.FG := fg_cut L hL Y
  set LP := latPow (Fin n) LX with hLPd
  have fgLP : LP.FG := Submodule.fg_pi fun _ => fgLX
  have hLPsp : Submodule.span K (LP : Set (Fin n → V)) = Submodule.pi Set.univ fun _ : Fin n => X := by
    rw [hLPd, span_latPow, hLX]
  have hLPX : ∀ x ∈ LP, x ∈ Submodule.pi Set.univ fun _ : Fin n => X := fun x hx i _ =>
    (Submodule.mem_inf.mp (hx i (Set.mem_univ i))).2
  set A := LP.map ((Φt Φ).restrictScalars (𝓞 K)) with hAd
  have fgA : A.FG := fgLP.map _
  have hAle : A ≤ LY := by
    rintro _ ⟨x, hx, rfl⟩
    refine Submodule.mem_inf.mpr ⟨?_, H.phi_mem x (hLPX x hx)⟩
    simp only [LinearMap.coe_restrictScalars, Φt_apply]
    exact L.sum_mem fun i _ => hΦL i (x i) (Submodule.mem_inf.mp (hx i (Set.mem_univ i))).1
      (Submodule.mem_inf.mp (hx i (Set.mem_univ i))).2
  have hAsp : Submodule.span K (A : Set V) = Y := by
    rw [hAd, Submodule.map_coe, LinearMap.coe_restrictScalars, Submodule.span_image, hLPsp, H.map_phi]
  refine ⟨hAle, hAsp, idx_nonneg_of_le hI w LY A fgLY fgA (hLY.trans hAsp.symm) hAle, ?_⟩

  set Bt := LY.map ((LinearMap.pi Ψ).restrictScalars (𝓞 K)) with hBtd
  have fgBt : Bt.FG := fgLY.map _
  have hBle : Bt ≤ LP := by
    rintro _ ⟨y, hy, rfl⟩ j _
    have hy' := Submodule.mem_inf.mp hy
    exact Submodule.mem_inf.mpr ⟨hΨL j y hy'.1 hy'.2, H.h3 j y hy'.2⟩
  have hBsp : Submodule.span K (Bt : Set (Fin n → V)) = Submodule.pi Set.univ fun _ : Fin n => X := by
    rw [hBtd, Submodule.map_coe, LinearMap.coe_restrictScalars, Submodule.span_image, hLY, H.map_psi]
  have hΨA : A.map ((LinearMap.pi Ψ).restrictScalars (𝓞 K)) = LP.map ((matV Γ).restrictScalars (𝓞 K)) := by
    rw [hAd, ← Submodule.map_comp]
    ext z
    simp only [Submodule.mem_map, LinearMap.coe_comp, LinearMap.coe_restrictScalars, Function.comp_apply]
    constructor
    · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, (H.psiPhi x (hLPX x hx)).symm⟩
    · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, H.psiPhi x (hLPX x hx)⟩
  have hmat := idx_matV hI w LX fgLX Γ H.det
  rw [← hLPd, ← hΨA] at hmat
  have hΨAsp : Submodule.span K ((A.map ((LinearMap.pi Ψ).restrictScalars (𝓞 K)) : Submodule (𝓞 K) (Fin n → V)) :
      Set (Fin n → V)) = Submodule.pi Set.univ fun _ : Fin n => X := by
    rw [hΨA]; exact span_map_matV Γ H.det LP X hLPsp
  have hch := idx_chain hI w LP Bt (A.map ((LinearMap.pi Ψ).restrictScalars (𝓞 K))) fgLP fgBt (fgA.map _)
    (by rw [hLPsp, hBsp]) (by rw [hΨAsp, hBsp])
  have hinj := idx_map_inj hI w (LinearMap.pi Ψ) LY A fgLY fgA (hLY.trans hAsp.symm)
    (fun y hy h0 => H.psi_inj y (Submodule.mem_inf.mp hy).2 h0)
    (fun y hy h0 => H.psi_inj y (Submodule.mem_inf.mp (hAle hy)).2 h0)
  have hnn := idx_nonneg_of_le hI w LP Bt fgLP fgBt (by rw [hLPsp, hBsp]) hBle
  rw [← hBtd] at hinj
  rw [hmat, ← hinj] at hch
  linarith

end Side

/- English proof (translation)
Introduce `K _ _ V _ _ _ _ n X Y Φ Ψ Γ hdet h1 h2 h3 h4 M N hMfg hNfg hMsp hNsp hΦM hΨM hΦN hΨN`. Use `haveI : FiniteDimensional K V := by`. Take `⟨s, hs⟩` from `hMfg`. Use `Module.finite_def.mpr ⟨s, ?_⟩` and prove the remaining obligations. Rewrite using `[← hMsp, ← hs, Submodule.span_span_of_tower]`.

Use `set Γk : Matrix (Fin n) (Fin n) K := Γ.map (algebraMap (𝓞 K) K) with hΓk`. Establish `hdetk : Γk.det = algebraMap (𝓞 K) K Γ.det` using `(RingHom.map_det _ _).symm`. Establish `H : BlockHyp X Y Φ Ψ Γk` using `⟨by rw [hdetk]; exact (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr hdet, fun i j x hx => by rw [h1 i j x hx]; rfl, h2, h3, h4⟩`. Establish `hrX : ∀ L : Submodule (𝓞 K) V, Submodule.span K (L : Set V) = ⊤ → Formalism.HN.rkK (L ⊓ X.restrictScalars (𝓞 K)) = Module.finrank K X` using `fun L hL => rk_cut L hL X`. Use `⟨by rw [rk_cut M hMsp Y, rk_cut M hMsp X, H.finrank], fun w => ?_⟩` and prove the remaining obligations.

Take `⟨hAle, hAsp, hA0, hA1⟩` from `H.side hI w M hMfg hMsp hΦM hΨM`. Take `⟨hBle, hBsp, hB0, hB1⟩` from `H.side hI w N hNfg hNsp hΦN hΨN`. Rewrite `hA1`, `hB1` using `[hdetk]`. Rewrite `hB1` using `[hrX N hNsp, ← hrX M hMsp]`. Use `set MX := M ⊓ X.restrictScalars (𝓞 K)`.

Use `set NX := N ⊓ X.restrictScalars (𝓞 K)`. Use `set MY := M ⊓ Y.restrictScalars (𝓞 K)`. Use `set NY := N ⊓ Y.restrictScalars (𝓞 K)`. Use `set A := (latPow (Fin n) MX).map ((Φt Φ).restrictScalars (𝓞 K))`. Use `set B := (latPow (Fin n) NX).map ((Φt Φ).restrictScalars (𝓞 K))`.

Establish `fgMX : MX.FG` using `fg_cut M hMfg X`. Establish `fgNX : NX.FG` using `fg_cut N hNfg X`. Establish `fgMY : MY.FG` using `fg_cut M hMfg Y`. Establish `fgNY : NY.FG` using `fg_cut N hNfg Y`. Establish `fgA : A.FG` using `(Submodule.fg_pi fun _ => fgMX).map _`.

Establish `fgB : B.FG` using `(Submodule.fg_pi fun _ => fgNX).map _`. Establish `sMY : Submodule.span K (MY : Set V) = Y` using `cut_span M hMsp Y`. Establish `sNY : Submodule.span K (NY : Set V) = Y` using `cut_span N hNsp Y`. Establish `c1` using `idx_chain hI w MY A NY fgMY fgA fgNY (sMY.trans hAsp.symm) (sNY.trans hAsp.symm)`. Establish `c2` using `idx_chain hI w A B NY fgA fgB fgNY (hAsp.trans hBsp.symm) (sNY.trans hBsp.symm)`.

Establish `hLX : ∀ L : Submodule (𝓞 K) V, ∀ x ∈ latPow (Fin n) (L ⊓ X.restrictScalars (𝓞 K)), x ∈ Submodule.pi Set.univ fun _ : Fin n => X` using `fun L x hx i _ => (Submodule.mem_inf.mp (hx i (Set.mem_univ i))).2`. Establish `c3` using `idx_map_inj hI w (Φt Φ) (latPow (Fin n) MX) (latPow (Fin n) NX) (Submodule.fg_pi fun _ => fgMX) (Submodule.fg_pi fun _ => fgNX) (by rw [span_latPow, span_latPow, cut_span M hMsp X, cut_span N hNsp X]) (fun x hx h0 => H.phi_inj x (hLX M x hx) h0) (fun x hx h0 => H.phi_inj x (hLX N …`. Establish `c4` using `idx_pi hI w (fun _ : Fin n => MX) (fun _ : Fin n => NX) (fun _ => fgMX) (fun _ => fgNX) (fun _ => by rw [cut_span M hMsp X, cut_span N hNsp X])`. Rewrite `c4` using `[Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]`. Establish `c5 : idxAt w B NY = -idxAt w NY B` using `idx_anti w B NY`.

Establish `key : idxAt w MY NY = idxAt w MY A + (n : ℤ) * idxAt w MX NX - idxAt w NY B`. Rewrite using `[c1, c2, c5, ← c3]`. Establish `: idxAt w (latPow (Fin n) MX) (latPow (Fin n) NX) = (n : ℤ) * idxAt w MX NX` using `c4`. Rewrite using `[this]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hD1 : -((Formalism.HN.rkK MX : ℤ) * vAdd w (algebraMap (𝓞 K) K Γ.det)) ≤ idxAt w MY NY - (n : ℤ) * idxAt w MX NX` using `by rw [key]; linarith`. Establish `hD2 : idxAt w MY NY - (n : ℤ) * idxAt w MX NX ≤ (Formalism.HN.rkK MX : ℤ) * vAdd w (algebraMap (𝓞 K) K Γ.det)` using `by rw [key]; linarith`. Establish `hfin : |((idxAt w MY NY - (n : ℤ) * idxAt w MX NX : ℤ) : ℝ)| ≤ (((Formalism.HN.rkK MX : ℤ) * vAdd w (algebraMap (𝓞 K) K Γ.det) : ℤ) : ℝ)`. Rewrite using `[abs_le]`. Prove the components needed by the constructor for the conclusion.

Conclude with `hD1` after adjusting the coercions. Conclude with `hD2` after adjusting the coercions. Move the coercions through the operations in `at hfin`. Conclude with `hfin`.
-/
theorem block_index_formula (hI : IdxCalc) : BlockIdx := by
  intro K _ _ V _ _ _ _ n X Y Φ Ψ Γ hdet h1 h2 h3 h4 M N hMfg hNfg hMsp hNsp hΦM hΨM hΦN hΨN
  haveI : FiniteDimensional K V := by
    obtain ⟨s, hs⟩ := hMfg
    refine Module.finite_def.mpr ⟨s, ?_⟩
    rw [← hMsp, ← hs, Submodule.span_span_of_tower]
  set Γk : Matrix (Fin n) (Fin n) K := Γ.map (algebraMap (𝓞 K) K) with hΓk
  have hdetk : Γk.det = algebraMap (𝓞 K) K Γ.det := (RingHom.map_det _ _).symm
  have H : BlockHyp X Y Φ Ψ Γk :=
    ⟨by rw [hdetk]; exact (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr hdet,
      fun i j x hx => by rw [h1 i j x hx]; rfl, h2, h3, h4⟩
  have hrX : ∀ L : Submodule (𝓞 K) V, Submodule.span K (L : Set V) = ⊤ →
      Formalism.HN.rkK (L ⊓ X.restrictScalars (𝓞 K)) = Module.finrank K X := fun L hL => rk_cut L hL X
  refine ⟨by rw [rk_cut M hMsp Y, rk_cut M hMsp X, H.finrank], fun w => ?_⟩
  obtain ⟨hAle, hAsp, hA0, hA1⟩ := H.side hI w M hMfg hMsp hΦM hΨM
  obtain ⟨hBle, hBsp, hB0, hB1⟩ := H.side hI w N hNfg hNsp hΦN hΨN
  rw [hdetk] at hA1 hB1
  rw [hrX N hNsp, ← hrX M hMsp] at hB1
  set MX := M ⊓ X.restrictScalars (𝓞 K)
  set NX := N ⊓ X.restrictScalars (𝓞 K)
  set MY := M ⊓ Y.restrictScalars (𝓞 K)
  set NY := N ⊓ Y.restrictScalars (𝓞 K)
  set A := (latPow (Fin n) MX).map ((Φt Φ).restrictScalars (𝓞 K))
  set B := (latPow (Fin n) NX).map ((Φt Φ).restrictScalars (𝓞 K))
  have fgMX : MX.FG := fg_cut M hMfg X
  have fgNX : NX.FG := fg_cut N hNfg X
  have fgMY : MY.FG := fg_cut M hMfg Y
  have fgNY : NY.FG := fg_cut N hNfg Y
  have fgA : A.FG := (Submodule.fg_pi fun _ => fgMX).map _
  have fgB : B.FG := (Submodule.fg_pi fun _ => fgNX).map _
  have sMY : Submodule.span K (MY : Set V) = Y := cut_span M hMsp Y
  have sNY : Submodule.span K (NY : Set V) = Y := cut_span N hNsp Y
  have c1 := idx_chain hI w MY A NY fgMY fgA fgNY (sMY.trans hAsp.symm) (sNY.trans hAsp.symm)
  have c2 := idx_chain hI w A B NY fgA fgB fgNY (hAsp.trans hBsp.symm) (sNY.trans hBsp.symm)
  have hLX : ∀ L : Submodule (𝓞 K) V, ∀ x ∈ latPow (Fin n) (L ⊓ X.restrictScalars (𝓞 K)),
      x ∈ Submodule.pi Set.univ fun _ : Fin n => X := fun L x hx i _ =>
    (Submodule.mem_inf.mp (hx i (Set.mem_univ i))).2
  have c3 := idx_map_inj hI w (Φt Φ) (latPow (Fin n) MX) (latPow (Fin n) NX)
    (Submodule.fg_pi fun _ => fgMX) (Submodule.fg_pi fun _ => fgNX)
    (by rw [span_latPow, span_latPow, cut_span M hMsp X, cut_span N hNsp X])
    (fun x hx h0 => H.phi_inj x (hLX M x hx) h0) (fun x hx h0 => H.phi_inj x (hLX N x hx) h0)
  have c4 := idx_pi hI w (fun _ : Fin n => MX) (fun _ : Fin n => NX) (fun _ => fgMX) (fun _ => fgNX)
    (fun _ => by rw [cut_span M hMsp X, cut_span N hNsp X])
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at c4
  have c5 : idxAt w B NY = -idxAt w NY B := idx_anti w B NY
  have key : idxAt w MY NY = idxAt w MY A + (n : ℤ) * idxAt w MX NX - idxAt w NY B := by
    rw [c1, c2, c5, ← c3]
    have : idxAt w (latPow (Fin n) MX) (latPow (Fin n) NX) = (n : ℤ) * idxAt w MX NX := c4
    rw [this]; ring
  have hD1 : -((Formalism.HN.rkK MX : ℤ) * vAdd w (algebraMap (𝓞 K) K Γ.det)) ≤
      idxAt w MY NY - (n : ℤ) * idxAt w MX NX := by rw [key]; linarith
  have hD2 : idxAt w MY NY - (n : ℤ) * idxAt w MX NX ≤
      (Formalism.HN.rkK MX : ℤ) * vAdd w (algebraMap (𝓞 K) K Γ.det) := by rw [key]; linarith
  have hfin : |((idxAt w MY NY - (n : ℤ) * idxAt w MX NX : ℤ) : ℝ)| ≤
      (((Formalism.HN.rkK MX : ℤ) * vAdd w (algebraMap (𝓞 K) K Γ.det) : ℤ) : ℝ) := by
    rw [abs_le]; constructor
    · exact_mod_cast hD1
    · exact_mod_cast hD2
  push_cast at hfin
  exact hfin

end PI.Dv.TIW
