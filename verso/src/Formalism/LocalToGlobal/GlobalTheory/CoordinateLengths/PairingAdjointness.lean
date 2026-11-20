import Formalism.LocalToGlobal.GlobalTheory.CoordinateLengths.PairingEqLimitPairing

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LemB

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms NumberField MvPolynomial Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

variable (D : D7)

def intSubm (w : D.what₂.places.Pl) {N : ℕ} (lam : D.what₂.Tau → DomWeight N) :
    Submodule (bwA_Ow D w) (MvPolynomial (D.what₂.Tau × Fin N × Fin N) ℂ) :=
  Submodule.span (bwA_Ow D w) (Formalism.L2.Forms.IntSpan D w lam : Set _)

/- English proof (translation)
Unfold `intSubm Formalism.L2.Forms.IntSpan tenSpan Formalism.L2.Forms.ten bwA_Ow`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Submodule.span_le]`. Introduce `p hp`. Rewrite `hp` using `[SetLike.mem_coe]`.

Proceed by induction on `hp using AddSubgroup.closure_induction with`. Consider the case `mem x hx`. Take `⟨r, f, hr, hf, rfl⟩` from `hx`. Establish `hfe : ∀ τ, rename (Prod.mk τ) (map (Int.castRingHom ℂ) (f τ)) = ∑ k, (b τ).repr ⟨f τ, hf τ⟩ k • rename (Prod.mk τ) (map (Int.castRingHom ℂ) ((b τ k : delSq ℤ N (lam τ)) : MvPolynomial (Fin N × Fin N) ℤ))`. Introduce `τ`.

Establish `h2` using `congrArg Subtype.val ((b τ).sum_repr ⟨f τ, hf τ⟩)`. Rewrite `h2` using `[Submodule.coe_sum]`. Simplify using `only [Submodule.coe_smul] at h2`. Use `conv_lhs => rw [← h2]`. Rewrite using `[map_sum, map_sum]`.

Simplify using `only [map_zsmul]`. Simplify using `only [hfe]`. Rewrite using `[Finset.prod_univ_sum, Fintype.piFinset_univ]`. Use `Submodule.smul_mem _ (⟨_, Subring.mem_map.2 ⟨r, hr, rfl⟩⟩ : ↥(Subring.map D.what₂.embLL (intW D.what₂.places w))) ?_` and prove the remaining obligations. Use `Submodule.sum_mem _ fun g _ => ?_` and prove the remaining obligations.

Simplify using `only [zsmul_eq_mul, Finset.prod_mul_distrib, ← Int.cast_prod]`. Rewrite using `[← zsmul_eq_mul]`. Apply `zsmul_mem` to reduce the goal to its premises. Apply `Submodule.subset_span` to reduce the goal to its premises. Conclude with `⟨g, rfl⟩`.

Consider the case `zero => exact Submodule.zero_mem _`. Consider the case `add x y _ _ hx hy => exact Submodule.add_mem _ hx hy`. Consider the case `neg x _ hx => exact Submodule.neg_mem _ hx`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨g, rfl⟩`.

Apply `Submodule.subset_span` to reduce the goal to its premises. Apply `AddSubgroup.subset_closure` to reduce the goal to its premises. Use `⟨1, fun τ => ((b τ (g τ) : delSq ℤ N (lam τ)) : MvPolynomial (Fin N × Fin N) ℤ), Subring.one_mem _, fun τ => (b τ (g τ)).2, ?_⟩` and prove the remaining obligations. Rewrite using `[map_one, one_smul]`.
-/
theorem intSubm_eq (w : D.what₂.places.Pl) {N : ℕ} (lam : D.what₂.Tau → DomWeight N) (κ : D.what₂.Tau → Type)
    [∀ τ, Fintype (κ τ)] (b : ∀ τ, Module.Basis (κ τ) ℤ (delSq ℤ N (lam τ))) :
    intSubm D w lam = tenSpan κ (fun τ k => MvPolynomial.map (Int.castRingHom ℂ)
      ((b τ k : delSq ℤ N (lam τ)) : MvPolynomial (Fin N × Fin N) ℤ)) (bwA_Ow D w) := by
  classical
  unfold intSubm Formalism.L2.Forms.IntSpan tenSpan Formalism.L2.Forms.ten bwA_Ow
  apply le_antisymm
  · rw [Submodule.span_le]
    intro p hp
    rw [SetLike.mem_coe] at hp
    induction hp using AddSubgroup.closure_induction with
    | mem x hx =>
      obtain ⟨r, f, hr, hf, rfl⟩ := hx
      have hfe : ∀ τ, rename (Prod.mk τ) (map (Int.castRingHom ℂ) (f τ)) =
          ∑ k, (b τ).repr ⟨f τ, hf τ⟩ k • rename (Prod.mk τ) (map (Int.castRingHom ℂ)
            ((b τ k : delSq ℤ N (lam τ)) : MvPolynomial (Fin N × Fin N) ℤ)) := by
        intro τ
        have h2 := congrArg Subtype.val ((b τ).sum_repr ⟨f τ, hf τ⟩)
        rw [Submodule.coe_sum] at h2
        simp only [Submodule.coe_smul] at h2
        conv_lhs => rw [← h2]
        rw [map_sum, map_sum]
        simp only [map_zsmul]
      simp only [hfe]
      rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
      refine Submodule.smul_mem _ (⟨_, Subring.mem_map.2 ⟨r, hr, rfl⟩⟩ : ↥(Subring.map D.what₂.embLL (intW D.what₂.places w))) ?_
      refine Submodule.sum_mem _ fun g _ => ?_
      simp only [zsmul_eq_mul, Finset.prod_mul_distrib, ← Int.cast_prod]
      rw [← zsmul_eq_mul]
      apply zsmul_mem
      apply Submodule.subset_span
      exact ⟨g, rfl⟩
    | zero => exact Submodule.zero_mem _
    | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
    | neg x _ hx => exact Submodule.neg_mem _ hx
  · rw [Submodule.span_le]
    rintro _ ⟨g, rfl⟩
    apply Submodule.subset_span
    apply AddSubgroup.subset_closure
    refine ⟨1, fun τ => ((b τ (g τ) : delSq ℤ N (lam τ)) : MvPolynomial (Fin N × Fin N) ℤ), Subring.one_mem _,
      fun τ => (b τ (g τ)).2, ?_⟩
    rw [map_one, one_smul]

/- English proof (translation)
Unfold `bwA_span`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨p, hp, rfl⟩`. Establish `h2` using `congrArg Subtype.val (b.sum_repr ⟨p, hp⟩)`.

Rewrite `h2` using `[Submodule.coe_sum]`. Simplify using `only [Submodule.coe_smul] at h2`. Rewrite using `[← h2, map_sum]`. Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_zsmul]`.

Apply `zsmul_mem` to reduce the goal to its premises. Apply `Submodule.subset_span` to reduce the goal to its premises. Conclude with `⟨i, rfl⟩`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨k, rfl⟩`.

Conclude with `Submodule.subset_span (Set.mem_image_of_mem _ (b k).2)`.
-/
theorem bwA_span_basis (O : Subring ℂ) {N : ℕ} (ν : Fin N → ℕ) {κ : Type} [Fintype κ]
    (b : Module.Basis κ ℤ (Formalism.GradedWeylDivisibility.weyl ℤ N N le_rfl ν)) :
    bwA_span (K := ℂ) O le_rfl ν = Submodule.span O (Set.range fun k => MvPolynomial.map (Int.castRingHom ℂ)
      ((b k : Formalism.GradedWeylDivisibility.weyl ℤ N N le_rfl ν) : MvPolynomial (Fin N × Fin N) ℤ)) := by
  unfold bwA_span
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨p, hp, rfl⟩
    have h2 := congrArg Subtype.val (b.sum_repr ⟨p, hp⟩)
    rw [Submodule.coe_sum] at h2
    simp only [Submodule.coe_smul] at h2
    rw [← h2, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [map_zsmul]
    apply zsmul_mem
    apply Submodule.subset_span
    exact ⟨i, rfl⟩
  · rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    exact Submodule.subset_span (Set.mem_image_of_mem _ (b k).2)

variable (u : D.what₂.Word)

/- English proof (translation)
Use `choose κ hκ b0 _ _ _ _ using fun τ => weyl_homogeneous_basis (r := D.R.N 0) (n := D.R.N 0) le_rfl ((D.fm u).lam 0 τ).natW (dominant_natWeight_antitone ((D.fm u).lam 0 τ))`. Set `_` to `hκ`. Set `b : ∀ τ, Module.Basis (κ τ) ℤ (delSq ℤ (D.R.N 0) ((D.fm u).lam 0 τ))` to `b0`. Take `⟨n, hn, hrel⟩` from `length_factor_local_basis D u A w hw v Lv c hLc0 B B' hB hB' hunit _ rfl`. Establish `hli : ∀ τ, τ ≠ (D.fm u).tauOf w v → LinearIndependent ℂ (fun k => MvPolynomial.map (Int.castRingHom ℂ) ((b τ k : delSq ℤ (D.R.N 0) ((D.fm u).lam 0 τ)) : MvPolynomial (Fin (D.R.N 0) × Fin (D.R.N 0)) ℤ))` using `fun τ _ => weyl_basis_lin_indep_field le_rfl ((D.fm u).lam 0 τ).natW (dominant_natWeight_antitone ((D.fm u).lam 0 τ)) ℂ (b0 τ)`.

Establish `ho : ∀ τ, τ ≠ (D.fm u).tauOf w v → bwA_N D ((D.fm u).tauOf w v) B B' τ = 1`. Introduce `τ h`. Unfold `bwA_N`. Rewrite using `[if_neg h]`. Establish `hcard : ∀ τ, Module.finrank ℤ (delSq ℤ (D.R.N 0) ((D.fm u).lam 0 τ)) = Fintype.card (κ τ)` using `fun τ => Module.finrank_eq_card_basis (b τ)`.

Use `⟨(∏ τ : {τ // τ ≠ (D.fm u).tauOf w v}, Fintype.card (κ τ.1)) * n, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[intSubm_eq D w ((D.fm u).lam 0) κ b]`. Use `(cls_len ((D.fm u).tauOf w v) κ _ (bwA_Ow D w) hli _ (bwA_span_basis (bwA_Ow D w) ((D.fm u).lam 0 ((D.fm u).tauOf w v)).natW (b0 ((D.fm u).tauOf w v))) (bwA_N D ((D.fm u).tauOf w v) B B') ho _ _).trans ?_` and prove the remaining obligations. Rewrite using `[hn]`. Simplify using the standard rewrite rules.

Establish `hprod : (∏ τ, Module.finrank ℤ (delSq ℤ (D.R.N 0) ((D.fm u).lam 0 τ))) = Module.finrank ℤ (delSq ℤ (D.R.N 0) ((D.fm u).lam 0 ((D.fm u).tauOf w v))) * ∏ τ : {τ // τ ≠ (D.fm u).tauOf w v}, Fintype.card (κ τ.1)`. Simplify using `only [hcard]`. Rewrite using `[← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ ((D.fm u).tauOf w v))]`. Use `congr 1`. Conclude with `Finset.prod_subtype (Finset.univ.erase ((D.fm u).tauOf w v)) (p := fun τ => τ ≠ (D.fm u).tauOf w v) (fun x => by simp) (fun τ => Fintype.card (κ τ))`.

Rewrite using `[hprod]`. Use `push_cast`. Take the linear combination `(∏ τ : {τ // τ ≠ (D.fm u).tauOf w v}, (Fintype.card (κ τ.1) : ℚ)) * hrel`.
-/
theorem cls_len_D (A : AtTTied u) (w : D.what₂.places.Pl) (hw : OverT D u w)
    (v : (D.mem u).A.vT) (Lv : LvTied u A 0 (Nat.zero_le _)) (c : (D.mem u).C.cls 0)
    (hLc0 : clsCrd D u 0 (Nat.zero_le _) c ≤ Ld D u 0 (Nat.zero_le _) c) (B B' : GL (Fin (D.R.N 0)) D.host.E)
    (hB : IsLocBasis (D.mem u).A.T (Ld D u 0 (Nat.zero_le _) c : Set _) B)
    (hB' : IsLocBasis (D.mem u).A.T (Lk A 0 (Nat.zero_le _) v c : Set _) B')
    (hunit : ((((B⁻¹ * B' : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E)).map
        (embT D ((D.fm u).tauOf w v))).det * (((D.mem u).A.T : ℂ))⁻¹ ∈ bwA_Ow D w ∧
      ((D.mem u).A.T : ℂ) * (((((B⁻¹ * B' : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E)).map
        (embT D ((D.fm u).tauOf w v))).det)⁻¹ ∈ bwA_Ow D w) :
    ∃ n : ℕ, Module.length (bwA_Ow D w)
      ((((intSubm D w ((D.fm u).lam 0)).map
            ((Formalism.L2.Forms.subP (bwA_N D ((D.fm u).tauOf w v) B B')).toLinearMap.restrictScalars (bwA_Ow D w))).map
          (scO (bwA_Ow D w) _ ((bwA_N D ((D.fm u).tauOf w v) B B' ((D.fm u).tauOf w v)).det ^
            ((D.fm u).lam 0 ((D.fm u).tauOf w v)).detShift))) ⧸
        ((intSubm D w ((D.fm u).lam 0)).map
            (scO (bwA_Ow D w) _ (((D.mem u).A.T : ℂ) ^ (D.fm u).bTop ((D.fm u).tauOf w v)))).comap
          (((intSubm D w ((D.fm u).lam 0)).map
            ((Formalism.L2.Forms.subP (bwA_N D ((D.fm u).tauOf w v) B B')).toLinearMap.restrictScalars (bwA_Ow D w))).map
          (scO (bwA_Ow D w) _ ((bwA_N D ((D.fm u).tauOf w v) B B' ((D.fm u).tauOf w v)).det ^
            ((D.fm u).lam 0 ((D.fm u).tauOf w v)).detShift))).subtype) = n ∧
      (D.R.k : ℚ) * n = (D.what₂.places.ramIdx w : ℚ) *
        ((∏ τ, Module.finrank ℤ (delSq ℤ (D.R.N 0) ((D.fm u).lam 0 τ)) : ℕ) : ℚ) *
        ((wsum ((D.fm u).lam 0 ((D.fm u).tauOf w v)) : ℚ) + (D.R.k : ℚ) * ((D.fm u).bTop ((D.fm u).tauOf w v) : ℚ)) := by
  classical
  choose κ hκ b0 _ _ _ _ using fun τ => weyl_homogeneous_basis (r := D.R.N 0) (n := D.R.N 0) le_rfl ((D.fm u).lam 0 τ).natW
    (dominant_natWeight_antitone ((D.fm u).lam 0 τ))
  let _ := hκ
  let b : ∀ τ, Module.Basis (κ τ) ℤ (delSq ℤ (D.R.N 0) ((D.fm u).lam 0 τ)) := b0
  obtain ⟨n, hn, hrel⟩ := length_factor_local_basis D u A w hw v Lv c hLc0 B B' hB hB' hunit _ rfl
  have hli : ∀ τ, τ ≠ (D.fm u).tauOf w v → LinearIndependent ℂ (fun k => MvPolynomial.map (Int.castRingHom ℂ)
      ((b τ k : delSq ℤ (D.R.N 0) ((D.fm u).lam 0 τ)) : MvPolynomial (Fin (D.R.N 0) × Fin (D.R.N 0)) ℤ)) := fun τ _ =>
    weyl_basis_lin_indep_field le_rfl ((D.fm u).lam 0 τ).natW (dominant_natWeight_antitone ((D.fm u).lam 0 τ)) ℂ (b0 τ)
  have ho : ∀ τ, τ ≠ (D.fm u).tauOf w v → bwA_N D ((D.fm u).tauOf w v) B B' τ = 1 := by
    intro τ h
    unfold bwA_N
    rw [if_neg h]
  have hcard : ∀ τ, Module.finrank ℤ (delSq ℤ (D.R.N 0) ((D.fm u).lam 0 τ)) = Fintype.card (κ τ) := fun τ =>
    Module.finrank_eq_card_basis (b τ)
  refine ⟨(∏ τ : {τ // τ ≠ (D.fm u).tauOf w v}, Fintype.card (κ τ.1)) * n, ?_, ?_⟩
  · rw [intSubm_eq D w ((D.fm u).lam 0) κ b]
    refine (cls_len ((D.fm u).tauOf w v) κ _ (bwA_Ow D w) hli _
      (bwA_span_basis (bwA_Ow D w) ((D.fm u).lam 0 ((D.fm u).tauOf w v)).natW (b0 ((D.fm u).tauOf w v)))
      (bwA_N D ((D.fm u).tauOf w v) B B') ho _ _).trans ?_
    rw [hn]
    simp
  · have hprod : (∏ τ, Module.finrank ℤ (delSq ℤ (D.R.N 0) ((D.fm u).lam 0 τ))) =
        Module.finrank ℤ (delSq ℤ (D.R.N 0) ((D.fm u).lam 0 ((D.fm u).tauOf w v))) *
          ∏ τ : {τ // τ ≠ (D.fm u).tauOf w v}, Fintype.card (κ τ.1) := by
      simp only [hcard]
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ ((D.fm u).tauOf w v))]
      congr 1
      exact Finset.prod_subtype (Finset.univ.erase ((D.fm u).tauOf w v)) (p := fun τ => τ ≠ (D.fm u).tauOf w v)
        (fun x => by simp) (fun τ => Fintype.card (κ τ))
    rw [hprod]
    push_cast
    linear_combination (∏ τ : {τ // τ ≠ (D.fm u).tauOf w v}, (Fintype.card (κ τ.1) : ℚ)) * hrel

end Formalism.L2.GlobalTheoryTheory.LemB
