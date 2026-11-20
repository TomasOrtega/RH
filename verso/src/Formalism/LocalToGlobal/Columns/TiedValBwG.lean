import Formalism.LocalToGlobal.Columns.TiedValLatG

open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.UG Formalism.L2.Forms

section Span

variable {K : Type} [Field K] [NumberField K] (Pl : Rows.Places K) (pw : Pl.Pl → HeightOneSpectrum (𝓞 K))
  (hval : ∀ w (x : K), x ≠ 0 → Pl.val w x = ((vAdd (pw w) x : ℤ) : WithTop ℤ))
  {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

include hval

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hx`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem y hy => exact lc_le_locP _ _ hy`. Consider the case `zero => exact zero_mem _`.

Consider the case `add y z _ _ hy hz => exact add_mem hy hz`. Consider the case `smul r y _ hy`. Take `⟨s, hs, hsy⟩` from `hy`. Take `⟨t, ht, hta⟩` from `(vl_mem_intW_iff Pl pw hval w (r : K)).1 r.2`. Take `⟨a, ha⟩` from `Submodule.mem_one.1 hta`.

Use `⟨t * s, lc_mul_notMem (pw w) ht hs, ?_⟩` and prove the remaining obligations. Establish `e : (t * s) • (r • y) = a • (s • y)`. Rewrite using `[Subring.smul_def, ← algebraMap_smul K (t * s), ← algebraMap_smul K a, ← algebraMap_smul K s, smul_smul, smul_smul, ha, Algebra.smul_def, map_mul]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e]`. Conclude with `A.smul_mem _ hsy`. Introduce and unpack `⟨t, ht, htx⟩`. Establish `h0 : algebraMap (𝓞 K) K t ≠ 0`. Introduce `h`.

Conclude with `lc_ne_zero_of_notMem (pw w) ht (by exact_mod_cast (FaithfulSMul.algebraMap_injective (𝓞 K) K) (h.trans (map_zero _).symm))`. Establish `e : x = (⟨_, vl_inv_mem_intW Pl pw hval w ht⟩ : intW Pl w) • (t • x)`. Rewrite using `[Subring.smul_def, ← algebraMap_smul K t, smul_smul, inv_mul_cancel₀ h0, one_smul]`. Rewrite using `[e]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span htx)`.
-/
theorem vl_mem_span_intW_iff (w : Pl.Pl) (A : Submodule (𝓞 K) V) (x : V) :
    x ∈ Submodule.span (intW Pl w) (A : Set V) ↔ x ∈ localization₂ (pw w).asIdeal A := by
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem y hy => exact lc_le_locP _ _ hy
    | zero => exact zero_mem _
    | add y z _ _ hy hz => exact add_mem hy hz
    | smul r y _ hy =>
      obtain ⟨s, hs, hsy⟩ := hy
      obtain ⟨t, ht, hta⟩ := (vl_mem_intW_iff Pl pw hval w (r : K)).1 r.2
      obtain ⟨a, ha⟩ := Submodule.mem_one.1 hta
      refine ⟨t * s, lc_mul_notMem (pw w) ht hs, ?_⟩
      have e : (t * s) • (r • y) = a • (s • y) := by
        rw [Subring.smul_def, ← algebraMap_smul K (t * s), ← algebraMap_smul K a, ← algebraMap_smul K s, smul_smul, smul_smul,
          ha, Algebra.smul_def, map_mul]
        congr 1
        ring
      rw [e]
      exact A.smul_mem _ hsy
  · rintro ⟨t, ht, htx⟩
    have h0 : algebraMap (𝓞 K) K t ≠ 0 := by
      intro h
      exact lc_ne_zero_of_notMem (pw w) ht (by exact_mod_cast (FaithfulSMul.algebraMap_injective (𝓞 K) K) (h.trans (map_zero _).symm))
    have e : x = (⟨_, vl_inv_mem_intW Pl pw hval w ht⟩ : intW Pl w) • (t • x) := by
      rw [Subring.smul_def, ← algebraMap_smul K t, smul_smul, inv_mul_cancel₀ h0, one_smul]
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.subset_span htx)

end Span

section DictF

variable {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K] (Pl : Rows.Places K)
  (pw : Pl.Pl → HeightOneSpectrum (𝓞 K))
  (hval : ∀ w (x : K), x ≠ 0 → Pl.val w x = ((vAdd (pw w) x : ℤ) : WithTop ℤ))
  {ι : Type} [Fintype ι] {n : ℕ} (emb : ι → E →+* K) (s : K →+* ℂ)

def vlBdF (B : ι → GL (Fin n) E) : ι → GL (Fin n) K := fun τ => inside₂ K n (bc (emb τ) (B τ))

/- English proof (translation)
Establish `h` using `evFr_coord (gramC J (embAt s emb)) s lam (vlBdF emb B) F.1`. Establish `e : (fun τ => (((vlBdF emb B τ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map s)ᵀ) = fun τ => atInf (embAt s emb) (((B τ)⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) τ`. Use function extensionality and compare the values at `τ`. Use `show ((((bc (emb τ) (B τ))⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ.map s)ᵀ = (((B τ)⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).map (s.comp (emb τ))`. Rewrite using `[← map_inv, bc_coe]`.

Use `Matrix.ext fun a b => ?_` and prove the remaining obligations. Both sides reduce to the same expression. Rewrite using `[← e]`. Conclude with `h`.
-/
theorem vl_coordF (J : Matrix (Fin n) (Fin n) E) (lam : ι → DomWeight n) (B : ι → GL (Fin n) E) (F : VV K lam) :
    evV emb J lam s F = fnOf _ (shiftOf lam)
      (fun τ => atInf (embAt s emb) (((B τ)⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) τ)
      (MvPolynomial.map s (actP lam (vlBdF emb B)⁻¹ F.1)) := by
  have h := evFr_coord (gramC J (embAt s emb)) s lam (vlBdF emb B) F.1
  have e : (fun τ => (((vlBdF emb B τ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map s)ᵀ) =
      fun τ => atInf (embAt s emb) (((B τ)⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) τ := by
    funext τ
    show ((((bc (emb τ) (B τ))⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ.map s)ᵀ =
      (((B τ)⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).map (s.comp (emb τ))
    rw [← map_inv, bc_coe]
    refine Matrix.ext fun a b => ?_
    rfl
  rw [← e]
  exact h

include hval

/- English proof (translation)
Establish `hbas : ∀ B : ι → GL (Fin n) E, (∀ τ, IsLocBasis (Pl.resChar w) (M τ : Set (Fin n → E)) (B τ)) → ∀ τ, IsBasisAt (pw w) (dualFr (tauLat emb τ (M τ))) (vlBdF emb B τ)` using `fun B hB τ => pb_isBasisAt_dualFr (pw w) _ (tauLatticeLattice_holds E K ι n emb τ (M τ) (hM τ)).fg _ (vl_isBasisAt_tauLat Pl pw hval emb τ w (M τ) (B τ) (hB τ))`. Establish `hlat : ∀ τ, Submodule.IsLattice K (dualFr (tauLat emb τ (M τ)))` using `fun τ => du_dualFr_lattice latticeBasisExists_holds _ (tauLatticeLattice_holds E K ι n emb τ (M τ) (hM τ))`. Establish `hmem : ∀ B : ι → GL (Fin n) E, (∀ τ, IsLocBasis (Pl.resChar w) (M τ : Set (Fin n → E)) (B τ)) → (F ∈ localization₂ (pw w).asIdeal (delK lam fun τ => dualFr (tauLat emb τ (M τ))) ↔ actP lam (vlBdF emb B)⁻¹ F.1 ∈ localization₂ (pw w).asIdeal (delStd K lam))`. Introduce `B hB`. Establish `h1 : F ∈ localization₂ (pw w).asIdeal (delK lam fun τ => dualFr (tauLat emb τ (M τ))) ↔ F.1 ∈ localization₂ (pw w).asIdeal (delP lam fun τ => dualFr (tauLat emb τ (M τ)))` using `Iff.rfl`.

Rewrite using `[h1, (nablaDeltaLocal_holds K ι n lam _ hlat (pw w) _ (hbas B hB)).2]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨G, hG, hGF⟩`. Establish `e : actP lam (vlBdF emb B)⁻¹ F.1 = G`. Rewrite using `[← hGF]`.

Use `show actP lam (vlBdF emb B)⁻¹ (actP lam (vlBdF emb B) G) = G`. Rewrite using `[← polyAction_mul, inv_mul_cancel, polyAction_one₂]`. Rewrite using `[e]`. Conclude with `hG`. Introduce `h`.

Use `⟨_, h, ?_⟩` and prove the remaining obligations. Use `show actP lam (vlBdF emb B) (actP lam (vlBdF emb B)⁻¹ F.1) = F.1`. Rewrite using `[← polyAction_mul, mul_inv_cancel, polyAction_one₂]`. Prove the components needed by the constructor for the conclusion. Introduce `h B hB`.

Conclude with `⟨_, vl_map_mem_intSpan Pl pw hval s w lam lam' hn ((hmem B hB).1 h), vl_coordF emb s J lam B F⟩`. Introduce `h`. Establish `: Fact (Pl.resChar w).Prime` using `⟨Pl.resChar_prime w⟩`. Use `choose B hB using fun τ => Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.LocB.exists_isLocBasis (Pl.resChar w) E (M τ) (hM τ).fg (hM τ).span_eq_top`. Take `⟨P, hP, hPe⟩` from `h B hB`.

Take `⟨G, hG, rfl⟩` from `vl_exists_of_mem_intSpan Pl pw hval s w lam lam' hn hP`. Rewrite `hPe` using `[vl_coordF emb s J lam B F]`. Establish `hinj` using `fnOf_injective (gramC J (embAt s emb)) (shiftOf lam) (fun τ => atInf (embAt s emb) (((B τ)⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) τ) (fun τ => Matrix.isUnits_det_units (Matrix.GeneralLinearGroup.map (embAt s emb τ) (B τ)⁻¹)) ⟨fun _ => 1, fun _ => by simp⟩ hPe`. Establish `hG' : actP lam (vlBdF emb B)⁻¹ F.1 = G` using `MvPolynomial.map_injective s s.injective hinj`. Rewrite using `[hmem B hB, hG']`.

Conclude with `hG`.
-/
theorem mem_localization_iff_forall_localBasis (w : Pl.Pl) (J : Matrix (Fin n) (Fin n) E) (lam lam' : ι → DomWeight n)
    (hn : ∀ τ, (lam τ).natW = (lam' τ).natW) (M : ι → Submodule (𝓞 E) (Fin n → E)) (hM : ∀ τ, Submodule.IsLattice E (M τ))
    (F : VV K lam) :
    F ∈ localization₂ (pw w).asIdeal (delK lam fun τ => dualFr (tauLat emb τ (M τ))) ↔
      ∀ B : ι → GL (Fin n) E, (∀ τ, IsLocBasis (Pl.resChar w) (M τ : Set (Fin n → E)) (B τ)) →
        ∃ P ∈ vlIntSpan s Pl w lam', evV emb J lam s F = fnOf _ (shiftOf lam)
          (fun τ => atInf (embAt s emb) (((B τ)⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) τ) P := by
  have hbas : ∀ B : ι → GL (Fin n) E, (∀ τ, IsLocBasis (Pl.resChar w) (M τ : Set (Fin n → E)) (B τ)) →
      ∀ τ, IsBasisAt (pw w) (dualFr (tauLat emb τ (M τ))) (vlBdF emb B τ) := fun B hB τ =>
    pb_isBasisAt_dualFr (pw w) _ (tauLatticeLattice_holds E K ι n emb τ (M τ) (hM τ)).fg _
      (vl_isBasisAt_tauLat Pl pw hval emb τ w (M τ) (B τ) (hB τ))
  have hlat : ∀ τ, Submodule.IsLattice K (dualFr (tauLat emb τ (M τ))) := fun τ =>
    du_dualFr_lattice latticeBasisExists_holds _ (tauLatticeLattice_holds E K ι n emb τ (M τ) (hM τ))
  have hmem : ∀ B : ι → GL (Fin n) E, (∀ τ, IsLocBasis (Pl.resChar w) (M τ : Set (Fin n → E)) (B τ)) →
      (F ∈ localization₂ (pw w).asIdeal (delK lam fun τ => dualFr (tauLat emb τ (M τ))) ↔
        actP lam (vlBdF emb B)⁻¹ F.1 ∈ localization₂ (pw w).asIdeal (delStd K lam)) := by
    intro B hB
    have h1 : F ∈ localization₂ (pw w).asIdeal (delK lam fun τ => dualFr (tauLat emb τ (M τ))) ↔
        F.1 ∈ localization₂ (pw w).asIdeal (delP lam fun τ => dualFr (tauLat emb τ (M τ))) := Iff.rfl
    rw [h1, (nablaDeltaLocal_holds K ι n lam _ hlat (pw w) _ (hbas B hB)).2]
    constructor
    · rintro ⟨G, hG, hGF⟩
      have e : actP lam (vlBdF emb B)⁻¹ F.1 = G := by
        rw [← hGF]
        show actP lam (vlBdF emb B)⁻¹ (actP lam (vlBdF emb B) G) = G
        rw [← polyAction_mul, inv_mul_cancel, polyAction_one₂]
      rw [e]
      exact hG
    · intro h
      refine ⟨_, h, ?_⟩
      show actP lam (vlBdF emb B) (actP lam (vlBdF emb B)⁻¹ F.1) = F.1
      rw [← polyAction_mul, mul_inv_cancel, polyAction_one₂]
  constructor
  · intro h B hB
    exact ⟨_, vl_map_mem_intSpan Pl pw hval s w lam lam' hn ((hmem B hB).1 h), vl_coordF emb s J lam B F⟩
  · intro h
    have : Fact (Pl.resChar w).Prime := ⟨Pl.resChar_prime w⟩
    choose B hB using fun τ => Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.LocB.exists_isLocBasis (Pl.resChar w) E (M τ) (hM τ).fg (hM τ).span_eq_top
    obtain ⟨P, hP, hPe⟩ := h B hB
    obtain ⟨G, hG, rfl⟩ := vl_exists_of_mem_intSpan Pl pw hval s w lam lam' hn hP
    rw [vl_coordF emb s J lam B F] at hPe
    have hinj := fnOf_injective (gramC J (embAt s emb)) (shiftOf lam)
      (fun τ => atInf (embAt s emb) (((B τ)⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) τ)
      (fun τ => Matrix.isUnits_det_units (Matrix.GeneralLinearGroup.map (embAt s emb τ) (B τ)⁻¹)) ⟨fun _ => 1, fun _ => by simp⟩ hPe
    have hG' : actP lam (vlBdF emb B)⁻¹ F.1 = G := MvPolynomial.map_injective s s.injective hinj
    rw [hmem B hB, hG']
    exact hG

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Conclude with `(mem_localization_iff_forall_localBasis Pl pw hval emb s w J lam lam' hn M hM F).1 h B hB`. Introduce and unpack `⟨P, hP, hPe⟩`. Establish `hbas : ∀ τ, IsBasisAt (pw w) (dualFr (tauLat emb τ (M τ))) (vlBdF emb B τ)` using `fun τ => pb_isBasisAt_dualFr (pw w) _ (tauLatticeLattice_holds E K ι n emb τ (M τ) (hM τ)).fg _ (vl_isBasisAt_tauLat Pl pw hval emb τ w (M τ) (B τ) (hB τ))`.

Establish `hlat : ∀ τ, Submodule.IsLattice K (dualFr (tauLat emb τ (M τ)))` using `fun τ => du_dualFr_lattice latticeBasisExists_holds _ (tauLatticeLattice_holds E K ι n emb τ (M τ) (hM τ))`. Take `⟨G, hG, rfl⟩` from `vl_exists_of_mem_intSpan Pl pw hval s w lam lam' hn hP`. Rewrite `hPe` using `[vl_coordF emb s J lam B F]`. Establish `hinj` using `fnOf_injective (gramC J (embAt s emb)) (shiftOf lam) (fun τ => atInf (embAt s emb) (((B τ)⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) τ) (fun τ => Matrix.isUnits_det_units (Matrix.GeneralLinearGroup.map (embAt s emb τ) (B τ)⁻¹)) ⟨fun _ => 1, fun _ => by simp⟩ hPe`. Establish `hG' : actP lam (vlBdF emb B)⁻¹ F.1 = G` using `MvPolynomial.map_injective s s.injective hinj`.

Establish `h1 : F ∈ localization₂ (pw w).asIdeal (delK lam fun τ => dualFr (tauLat emb τ (M τ))) ↔ F.1 ∈ localization₂ (pw w).asIdeal (delP lam fun τ => dualFr (tauLat emb τ (M τ)))` using `Iff.rfl`. Rewrite using `[h1, (nablaDeltaLocal_holds K ι n lam _ hlat (pw w) _ hbas).2]`. Use `⟨G, hG, ?_⟩` and prove the remaining obligations. Use `show actP lam (vlBdF emb B) G = F.1`. Rewrite using `[← hG', ← polyAction_mul, mul_inv_cancel, polyAction_one₂]`.
-/
theorem mem_localization_iff_forall_localBasis_of_valuation (w : Pl.Pl) (J : Matrix (Fin n) (Fin n) E) (lam lam' : ι → DomWeight n)
    (hn : ∀ τ, (lam τ).natW = (lam' τ).natW) (M : ι → Submodule (𝓞 E) (Fin n → E)) (hM : ∀ τ, Submodule.IsLattice E (M τ))
    (F : VV K lam) (B : ι → GL (Fin n) E) (hB : ∀ τ, IsLocBasis (Pl.resChar w) (M τ : Set (Fin n → E)) (B τ)) :
    F ∈ localization₂ (pw w).asIdeal (delK lam fun τ => dualFr (tauLat emb τ (M τ))) ↔
      ∃ P ∈ vlIntSpan s Pl w lam', evV emb J lam s F = fnOf _ (shiftOf lam)
        (fun τ => atInf (embAt s emb) (((B τ)⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) τ) P := by
  constructor
  · intro h
    exact (mem_localization_iff_forall_localBasis Pl pw hval emb s w J lam lam' hn M hM F).1 h B hB
  · rintro ⟨P, hP, hPe⟩
    have hbas : ∀ τ, IsBasisAt (pw w) (dualFr (tauLat emb τ (M τ))) (vlBdF emb B τ) := fun τ =>
      pb_isBasisAt_dualFr (pw w) _ (tauLatticeLattice_holds E K ι n emb τ (M τ) (hM τ)).fg _
        (vl_isBasisAt_tauLat Pl pw hval emb τ w (M τ) (B τ) (hB τ))
    have hlat : ∀ τ, Submodule.IsLattice K (dualFr (tauLat emb τ (M τ))) := fun τ =>
      du_dualFr_lattice latticeBasisExists_holds _ (tauLatticeLattice_holds E K ι n emb τ (M τ) (hM τ))
    obtain ⟨G, hG, rfl⟩ := vl_exists_of_mem_intSpan Pl pw hval s w lam lam' hn hP
    rw [vl_coordF emb s J lam B F] at hPe
    have hinj := fnOf_injective (gramC J (embAt s emb)) (shiftOf lam)
      (fun τ => atInf (embAt s emb) (((B τ)⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) τ)
      (fun τ => Matrix.isUnits_det_units (Matrix.GeneralLinearGroup.map (embAt s emb τ) (B τ)⁻¹)) ⟨fun _ => 1, fun _ => by simp⟩ hPe
    have hG' : actP lam (vlBdF emb B)⁻¹ F.1 = G := MvPolynomial.map_injective s s.injective hinj
    have h1 : F ∈ localization₂ (pw w).asIdeal (delK lam fun τ => dualFr (tauLat emb τ (M τ))) ↔
        F.1 ∈ localization₂ (pw w).asIdeal (delP lam fun τ => dualFr (tauLat emb τ (M τ))) := Iff.rfl
    rw [h1, (nablaDeltaLocal_holds K ι n lam _ hlat (pw w) _ hbas).2]
    refine ⟨G, hG, ?_⟩
    show actP lam (vlBdF emb B) G = F.1
    rw [← hG', ← polyAction_mul, mul_inv_cancel, polyAction_one₂]

end DictF

end Formalism.L2.Col
