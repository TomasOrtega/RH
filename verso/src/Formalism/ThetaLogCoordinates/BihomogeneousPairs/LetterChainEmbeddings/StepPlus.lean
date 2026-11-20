import Formalism.ThetaLogCoordinates.BihomogeneousPairs.LetterChainEmbeddings.PairStep

namespace Formalism.InvariantFactorPaths.KP.LL

open Formalism.GM

open MvPolynomial Finset Formalism.GM.M

section
variable {p : ℕ} [Fact p.Prime] {N r : ℕ} [NeZero r] {D : BlockData N}

/- English proof (translation)
Establish `h1 : D.Eplus p (r` using `r) = ehP (wU D) (xiVar N r D.T.t) (zP D r) (sP D r) := rfl`. Unfold `midGen`. Rewrite using `[h1]`. Simplify using `only [Nat.not_lt_zero, Finset.filter_false, Finset.prod_empty, List.drop_zero, mul_one]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sp_midGen_zero (j : Fin D.T.t → ℕ) (jp : ℕ) (x : MvPolynomial (BVar N r D.T.t) ℚ_[p]) :
    midGen p D 0 j jp x = (∏ i, D.Ehat p (r := r) i ^ j i) *
      (ehP (wU D) (xiVar N r D.T.t) (zP D r) (sP D r) ^ jp *
        (X (zP D r) ^ D.zPlus * PL p D (List.finRange D.T.t) j jp x)) := by
  have h1 : D.Eplus p (r := r) = ehP (wU D) (xiVar N r D.T.t) (zP D r) (sP D r) := rfl
  unfold midGen
  rw [h1]
  simp only [Nat.not_lt_zero, Finset.filter_false, Finset.prod_empty, List.drop_zero, mul_one]
  ring

/- English proof (translation)
Rewrite using `[mul_assoc]`. Both sides reduce to the same expression.
-/
theorem sp_gen_P (j : Fin D.T.t → ℕ) (jp : ℕ) (y : MvPolynomial (BVar N r D.T.t) ℚ_[p]) :
    (∏ i, D.Ehat p (r := r) i ^ j i) * D.Eplus p (r := r) ^ jp * Pplus p D jp y =
      (∏ i, D.Ehat p (r := r) i ^ j i) *
      (ehP (wU D) (xiVar N r D.T.t) (zP D r) (sP D r) ^ jp *
        tieP (wU D) (xiVar N r D.T.t) (zP D r) (sP D r) (D.LL.deg D.uPos - jp) (D.B - jp) D.zPlus y) := by
  rw [mul_assoc]
  rfl

/- English proof (translation)
Introduce `c d h`. Simplify using `only [wU, Sum.inl.injEq, Prod.mk.injEq] at h`. Conclude with `h.2`.
-/
theorem sp_wU_inj : Function.Injective (wU (r := r) D) := by
  intro c d h
  simp only [wU, Sum.inl.injEq, Prod.mk.injEq] at h
  exact h.2

/- English proof (translation)
Introduce `c d h`. Simplify using `only [xiVar, Sum.inl.injEq, Prod.mk.injEq] at h`. Conclude with `h.2`.
-/
theorem sp_xi_inj : Function.Injective (xiVar N r D.T.t) := by
  intro c d h
  simp only [xiVar, Sum.inl.injEq, Prod.mk.injEq] at h
  exact h.2

end

/- English proof (translation)
Introduce `hPS hLP hLin hComm hPar p _ N r _ D a u hB hr hdeg hBa hz hU hu`. Establish `key : ∀ (j : Fin D.T.t → ℕ) (jp : ℕ), D.LevelOK j jp → ∀ x ∈ Lat p D (r` using `r) j jp, ((p : ℚ_[p]) ^ u • midGen p D 0 j jp x ∈ MidP p (r := r) D) ∧ ((p : ℚ_[p]) ^ u • ((∏ i, D.Ehat p (r := r) i ^ j i) * D.Eplus p (r := r) ^ jp * Pplus p D jp (PL p D (List.finRange D.T.t) j jp x)) ∈ Mid p (r := r) D 0) := by`. Introduce `j jp hOK x hx`. Take `⟨T, hT⟩` from `(hLin p N r D (List.finRange D.T.t) j jp).1`. Establish `hcomm : ∀ (m : ℕ) (y : MvPolynomial (BVar N r D.T.t) ℚ_[p]), (tieF (wU D) (xiVar N r D.T.t) ^ m) (T y) = T ((tieF (wU D) (xiVar N r D.T.t) ^ m) y)`.

Introduce `m y`. Rewrite using `[hT, hT]`. Conclude with `(hComm p N r D hB (List.finRange D.T.t) j jp m y).2`. Establish `hps` using `hPS p (BVar N r D.T.t) r (wU D) (xiVar N r D.T.t) (zP D r) (sP D r) hr (fun c => ⟨by simp [wU, zP, scalZ], by simp [xiVar, zP, scalZ]⟩) (D.LL.deg D.uPos) D.B D.zPlus (Nat.log p (2 * a)) u (fun l => Submodule.map (T.restrictScalars ℤ_[p]) (Lat p D (r := r) j l)) (by`. Introduce and unpack `l _ ⟨y, hy, rfl⟩ m hm`.

Rewrite using `[LinearMap.restrictScalars_apply, hcomm]`. Establish `hb` using `biHom_plus (p := p) (D := D) j l y hy`. Rewrite `hb` using `[deg_U hB]`. Rewrite using `[tieF_pow_apply_eq_zero_of_min_lt (wU D) (xiVar N r D.T.t) sp_wU_inj sp_xi_inj wU_ne_xi hb m hm, map_zero])`. Use the proof step `(by`.

Introduce and unpack `l m hm _ ⟨y, hy, rfl⟩`. Rewrite using `[LinearMap.restrictScalars_apply, hcomm, ← map_smul]`. Use `⟨_, hLP p N r D hB hU j l m (Nat.log p (2 * a)) (Nat.log_mono_right ?_) y hy, rfl⟩` and prove the remaining obligations. Conclude with `le_trans (le_trans hm (min_le_left _ _)) (hdeg _))`. Use the proof step `(by`.

Use `le_trans (Nat.add_le_add_left (Nat.log_mono_right ?_) _) hu` and prove the remaining obligations. Use `hdeg D.uPos` as an intermediate fact. Use the proof step `omega)`. Use `jp hOK.2 (T x) ⟨x, hx, rfl⟩`. Prove the components needed by the constructor for the conclusion.

Rewrite using `[sp_midGen_zero, ← hT, ← mul_smul_comm]`. Use `span_map_mem (LinearMap.mulLeft ℚ_[p] (∏ i, D.Ehat p (r := r) i ^ j i)) _ _ ?_ _ hps.1` and prove the remaining obligations. Introduce and unpack `_ ⟨l', hl', _, ⟨y, hy, rfl⟩, rfl⟩`. Use `Submodule.subset_span ⟨j, l', ⟨hOK.1, hl'⟩, y, hy, ?_⟩` and prove the remaining obligations. Rewrite using `[LinearMap.mulLeft_apply, LinearMap.restrictScalars_apply, hT, sp_gen_P, hPar p N r D hB (List.finRange D.T.t) j j jp l' y (fun _ _ => rfl)]`.

Rewrite using `[sp_gen_P, ← hT, ← mul_smul_comm]`. Use `span_map_mem (LinearMap.mulLeft ℚ_[p] (∏ i, D.Ehat p (r := r) i ^ j i)) _ _ ?_ _ hps.2` and prove the remaining obligations. Introduce and unpack `_ ⟨l', hl', _, ⟨y, hy, rfl⟩, rfl⟩`. Use `Submodule.subset_span ⟨j, l', ⟨hOK.1, hl'⟩, y, hy, ?_⟩` and prove the remaining obligations. Rewrite using `[LinearMap.mulLeft_apply, LinearMap.restrictScalars_apply, hT, sp_midGen_zero, hPar p N r D hB (List.finRange D.T.t) j j jp l' y (fun _ _ => rfl)]`.

Set `S : MvPolynomial (BVar N r D.T.t) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (BVar N r D.T.t) ℚ_[p]` to `(p : ℚ_[p]) ^ u • LinearMap.id`. Prove the components needed by the constructor for the conclusion. Introduce `v hv`. Use `span_map_mem S _ (MidP p (r := r) D) ?_ v hv` and prove the remaining obligations. Introduce and unpack `_ ⟨j, jp, hOK, x, hx, rfl⟩`.

Conclude with `(key j jp hOK x hx).1`. Introduce `v hv`. Use `span_map_mem S _ (Mid p (r := r) D 0) ?_ v hv` and prove the remaining obligations. Introduce and unpack `_ ⟨j, jp, hOK, x, hx, rfl⟩`. Conclude with `(key j jp hOK x hx).2`.
-/
theorem StepPlus_of : PairStep → LatPlus → PLLin → CommPL → ParamPL → PlusCondition := by
  intro hPS hLP hLin hComm hPar p _ N r _ D a u hB hr hdeg hBa hz hU hu
  have key : ∀ (j : Fin D.T.t → ℕ) (jp : ℕ), D.LevelOK j jp → ∀ x ∈ Lat p D (r := r) j jp,
      ((p : ℚ_[p]) ^ u • midGen p D 0 j jp x ∈ MidP p (r := r) D) ∧
      ((p : ℚ_[p]) ^ u • ((∏ i, D.Ehat p (r := r) i ^ j i) * D.Eplus p (r := r) ^ jp *
        Pplus p D jp (PL p D (List.finRange D.T.t) j jp x)) ∈ Mid p (r := r) D 0) := by
    intro j jp hOK x hx
    obtain ⟨T, hT⟩ := (hLin p N r D (List.finRange D.T.t) j jp).1
    have hcomm : ∀ (m : ℕ) (y : MvPolynomial (BVar N r D.T.t) ℚ_[p]),
        (tieF (wU D) (xiVar N r D.T.t) ^ m) (T y) = T ((tieF (wU D) (xiVar N r D.T.t) ^ m) y) := by
      intro m y
      rw [hT, hT]
      exact (hComm p N r D hB (List.finRange D.T.t) j jp m y).2
    have hps := hPS p (BVar N r D.T.t) r (wU D) (xiVar N r D.T.t) (zP D r) (sP D r) hr
      (fun c => ⟨by simp [wU, zP, scalZ], by simp [xiVar, zP, scalZ]⟩)
      (D.LL.deg D.uPos) D.B D.zPlus (Nat.log p (2 * a)) u
      (fun l => Submodule.map (T.restrictScalars ℤ_[p]) (Lat p D (r := r) j l))
      (by
        rintro l _ ⟨y, hy, rfl⟩ m hm
        rw [LinearMap.restrictScalars_apply, hcomm]
        have hb := biHom_plus (p := p) (D := D) j l y hy
        rw [deg_U hB] at hb
        rw [tieF_pow_apply_eq_zero_of_min_lt (wU D) (xiVar N r D.T.t) sp_wU_inj sp_xi_inj wU_ne_xi hb m hm, map_zero])
      (by
        rintro l m hm _ ⟨y, hy, rfl⟩
        rw [LinearMap.restrictScalars_apply, hcomm, ← map_smul]
        refine ⟨_, hLP p N r D hB hU j l m (Nat.log p (2 * a)) (Nat.log_mono_right ?_) y hy, rfl⟩
        exact le_trans (le_trans hm (min_le_left _ _)) (hdeg _))
      (by
        refine le_trans (Nat.add_le_add_left (Nat.log_mono_right ?_) _) hu
        have := hdeg D.uPos
        omega)
      jp hOK.2 (T x) ⟨x, hx, rfl⟩
    constructor
    · rw [sp_midGen_zero, ← hT, ← mul_smul_comm]
      refine span_map_mem (LinearMap.mulLeft ℚ_[p] (∏ i, D.Ehat p (r := r) i ^ j i)) _ _ ?_ _ hps.1
      rintro _ ⟨l', hl', _, ⟨y, hy, rfl⟩, rfl⟩
      refine Submodule.subset_span ⟨j, l', ⟨hOK.1, hl'⟩, y, hy, ?_⟩
      rw [LinearMap.mulLeft_apply, LinearMap.restrictScalars_apply, hT, sp_gen_P,
        hPar p N r D hB (List.finRange D.T.t) j j jp l' y (fun _ _ => rfl)]
    · rw [sp_gen_P, ← hT, ← mul_smul_comm]
      refine span_map_mem (LinearMap.mulLeft ℚ_[p] (∏ i, D.Ehat p (r := r) i ^ j i)) _ _ ?_ _ hps.2
      rintro _ ⟨l', hl', _, ⟨y, hy, rfl⟩, rfl⟩
      refine Submodule.subset_span ⟨j, l', ⟨hOK.1, hl'⟩, y, hy, ?_⟩
      rw [LinearMap.mulLeft_apply, LinearMap.restrictScalars_apply, hT, sp_midGen_zero,
        hPar p N r D hB (List.finRange D.T.t) j j jp l' y (fun _ _ => rfl)]
  let S : MvPolynomial (BVar N r D.T.t) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (BVar N r D.T.t) ℚ_[p] :=
    (p : ℚ_[p]) ^ u • LinearMap.id
  constructor
  · intro v hv
    refine span_map_mem S _ (MidP p (r := r) D) ?_ v hv
    rintro _ ⟨j, jp, hOK, x, hx, rfl⟩
    exact (key j jp hOK x hx).1
  · intro v hv
    refine span_map_mem S _ (Mid p (r := r) D 0) ?_ v hv
    rintro _ ⟨j, jp, hOK, x, hx, rfl⟩
    exact (key j jp hOK x hx).2

end Formalism.InvariantFactorPaths.KP.LL
