import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetVecEq
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.WeilOperatorRationalTranslateMemThetaFunctions
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitInertFactorizationUnitaryLatticeStabiStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryCongruentOneDetSubOneMemIdealMulConjStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitSupportedUnitaryMovingToSelfDualSkewLStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdealMatrixApproxCongruentOneTranslateStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaPointMemStandardAndSkewLatticeOfEntriesMemStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIntertwinerStandardToSkewMemThetaSpaceStatement
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

noncomputable section

namespace GlobalTheory.FunObj.FixKey

/- English proof (translation)
Proceed by induction on `hy using AddSubgroup.closure_induction with`. Consider the case `mem x hx`. Take `⟨b, hb, t, ht, rfl⟩` from `hx`. Conclude with `AddSubgroup.subset_closure ⟨b, hb, s * t, mul_mem hs ht, by ring⟩`. Consider the case `zero => simp`.

Consider the case `add x y _ _ hx hy => rw [mul_add]`. Conclude with `add_mem hx hy`. Consider the case `neg x _ hx => rw [mul_neg]`. Conclude with `neg_mem hx`.
-/
theorem hatId_mul {D : D7} {I : Ideal (𝓞 D.host.E)} {s y : AE D} (hs : s ∈ OhE D) (hy : y ∈ hatId D I) :
    s * y ∈ hatId D I := by
  induction hy using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨b, hb, t, ht, rfl⟩ := hx
    exact AddSubgroup.subset_closure ⟨b, hb, s * t, mul_mem hs ht, by ring⟩
  | zero => simp
  | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
  | neg x _ hx => rw [mul_neg]; exact neg_mem hx

/- English proof (translation)
Introduce `_` and use `⟨1, one_pos, Nat.coprime_one_left q, 0, zero_mem _, by simp⟩`.
-/
theorem zeroAt_zero (D : D7) (q : ℕ) : ZeroAt D q 0 :=
  fun _ => ⟨1, one_pos, Nat.coprime_one_left q, 0, zero_mem _, by simp⟩

/- English proof (translation)
Introduce `q _ _ i j` and use `by rw [OneMemClass.coe_one, Units.val_one, sub_self]; exact zeroAt_zero D q`.
-/
theorem suppSplit_one (D : D7) (N : ℕ) : SuppSplit D ((1 : GA D N) : GL (Fin N) (AE D)) :=
  fun q _ _ i j => by rw [OneMemClass.coe_one, Units.val_one, sub_self]; exact zeroAt_zero D q

/- English proof (translation)
Introduce `q _ _ i j` and use `by rw [OneMemClass.coe_one, Units.val_one, sub_self]; exact zeroAt_zero D q`.
-/
theorem suppInert_one (D : D7) (N : ℕ) : SuppInert D ((1 : GA D N) : GL (Fin N) (AE D)) :=
  fun q _ _ i j => by rw [OneMemClass.coe_one, Units.val_one, sub_self]; exact zeroAt_zero D q

/- English proof (translation)
Use function extensionality and compare the values at `z`. Simplify using `only [Wd, U, Pi.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem wd_smul (D : D7) (T : Tor D) {N N' : ℕ} (x : VC D N N') (c : ℂ) (F : VC D N N' → ℂ) :
    Wd D T x (c • F) = c • Wd D T x F := by
  funext z; simp only [Wd, U, Pi.smul_apply, smul_eq_mul]; ring

/- English proof (translation)
Take `⟨hd, m, hm, h⟩` from `hF`. Conclude with `⟨hd.const_smul c, m, hm, fun x hx => by rw [wd_smul, h x hx]⟩`.
-/
theorem TT_smul {D : D7} {T : Tor D} {N N' : ℕ} (c : ℂ) {F : VC D N N' → ℂ} (hF : F ∈ TT D T N N') :
    c • F ∈ TT D T N N' := by
  obtain ⟨hd, m, hm, h⟩ := hF
  exact ⟨hd.const_smul c, m, hm, fun x hx => by rw [wd_smul, h x hx]⟩

/- English proof (translation)
Establish `h1` using `(GlobalTheory.InducedType.induced_type D).1`. Establish `k0 : KLat D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d)` using `VacMove.klat _ (VacMove.moves_one D a) (VacMove.moves_one D d)`. Take `⟨φ, hφ⟩` from `VacMove.wd_wd D (tor0 D ⊤ δ) x y`. Establish `h2` using `hφ e0`. Rewrite `h2` using `[VacMove.wd_fix h1 hc k0 he hy, VacMove.wd_fix h1 hc k0 he hx, VacMove.wd_fix h1 hc k0 he (add_mem hx hy)]`.

Establish `h3 : φ = 1`. Assume the negation of the conclusion as `hne'`. Apply `hne` to reduce the goal to its premises. Establish `: (φ - 1) • e0 = 0` using `by rw [sub_smul, one_smul, ← h2, sub_self]`. Conclude with `(smul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hne')`.

Rewrite using `[hφ, h3, one_smul]`.
-/
theorem weylTranslate_add_of_mem_baseLattice {D : D7} {δ : ℂ} (hc : Crv D ⊤ δ) {a d : ℕ} {e0 : VC D a d → ℂ}
    (he : e0 ∈ Th D (tor0 D ⊤ δ) (stdL D a) (stdL D d)) (hne : e0 ≠ 0) {x y : VC D a d}
    (hx : x ∈ La0 D (tor0 D ⊤ δ) a d) (hy : y ∈ La0 D (tor0 D ⊤ δ) a d) (F : VC D a d → ℂ) :
    Wd D (tor0 D ⊤ δ) x (Wd D (tor0 D ⊤ δ) y F) = Wd D (tor0 D ⊤ δ) (x + y) F := by
  have h1 := (GlobalTheory.InducedType.induced_type D).1
  have k0 : KLat D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) :=
    VacMove.klat _ (VacMove.moves_one D a) (VacMove.moves_one D d)
  obtain ⟨φ, hφ⟩ := VacMove.wd_wd D (tor0 D ⊤ δ) x y
  have h2 := hφ e0
  rw [VacMove.wd_fix h1 hc k0 he hy, VacMove.wd_fix h1 hc k0 he hx,
    VacMove.wd_fix h1 hc k0 he (add_mem hx hy)] at h2
  have h3 : φ = 1 := by
    by_contra hne'
    apply hne
    have : (φ - 1) • e0 = 0 := by rw [sub_smul, one_smul, ← h2, sub_self]
    exact (smul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hne')
  rw [hφ, h3, one_smul]

/- English proof (translation)
Introduce `i j`. Distinguish the cases in `h : i.1 = o + j.1`. Conclude with `⟨1, by simp [unitBlock, h]⟩`. Conclude with `⟨0, by simp [unitBlock, h]⟩`.
-/
theorem unitBlock_int (D : D7) (o a d : ℕ) : ∀ i j, ∃ b : 𝓞 D.host.E, unitBlock D o a d i j = (b : D.host.E) := by
  intro i j
  by_cases h : i.1 = o + j.1
  · exact ⟨1, by simp [unitBlock, h]⟩
  · exact ⟨0, by simp [unitBlock, h]⟩

/- English proof (translation)
Introduce `D δ t0 hc a d e0 hv W 𝔪 h𝔪 hcop hch o ho k hk hck`. Establish `h1` using `(GlobalTheory.InducedType.induced_type D).1`. Establish `he` using `hv.1`. Establish `hT` using `VacMove.vac_TT h1 hc he`. Establish `hk0 : W.Om k 1 e0 = e0`.

Take `⟨ks, ki, x, hkk, hks, hki, hss, hsi, hxq, hxd, hxu, η, hη, hx1⟩` from `GlobalTheory.T.exists_split_inert_factorization_unitaryLatticeStabilizer D k hk`. Establish `hi : W.Om ki 1 e0 = e0` using `W.inert ki 1 ((mem_intG ki).1 hki) ((mem_intG 1).1 (one_mem _)) hsi (suppInert_one D d)`. Establish `hs : W.Om ks 1 e0 = e0`. Establish `hm : Moves D (ks : GL (Fin a) (AE D)) (stdL D a)`. Simplify using `using VacMove.moves_mul_int hks (VacMove.moves_one D a)`.

Establish `hx : W.chV'.f x = 1` using `hch x hxu (by rw [hx1]; exact hatId_mul hη (GlobalTheory.T.unitary_congruent_one_det_sub_one_mem_ideal_mul_conj D 𝔪 hcop k hk hck))`. Rewrite using `[W.split ks 1 x 1 (stdL D a) (stdL D d) hss (suppSplit_one D d) (fun q hq hi => ⟨hxq q hq hi, by simpa using zeroAt_zero D q⟩) hxd (by simp) hm (VacMove.moves_one D d)]`. Simplify using `only [hx, map_one, one_zpow, mul_one, Units.val_one, one_mul]`. Conclude with `VacMove.iop_self D _ (La0 D (tor0 D ⊤ δ) a d) he`. Use `W.mul ks ki 1 1 e0 hT` as an intermediate fact.

Rewrite `this` using `[mul_one, ← hkk]`. Rewrite using `[this, hi, hs]`. Take `⟨g', x', hg's, hg'm, hx'q, hx'd⟩` from `GlobalTheory.T.exists_splitSupported_unitary_moving_to_selfDualSkewLattice D 𝔪 h𝔪 hcop d`. Establish `hsd : SD D (skewLat D 𝔪 d)` using `VacMove.sd_of_moves hg'm`. Establish `hJ : W.Om 1 g' e0 = ((W.chV.f x' ^ W.ep * W.chV'.f 1 ^ W.ep' : ℂˣ) : ℂ) • Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)) e0`.

Rewrite using `[W.split 1 g' 1 x' (stdL D a) (skewLat D 𝔪 d) (suppSplit_one D a) hg's (fun q hq hi => ⟨by simpa using zeroAt_zero D q, hx'q q hq hi⟩) (by simp) hx'd (VacMove.moves_one D a) hg'm]`. Both sides reduce to the same expression. Establish `hc0 : ((W.chV.f x' ^ W.ep * W.chV'.f 1 ^ W.ep' : ℂˣ) : ℂ) ≠ 0` using `Units.ne_zero _`. Establish `hJe : Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)) e0 = ((W.chV.f x' ^ W.ep * W.chV'.f 1 ^ W.ep' : ℂˣ) : ℂ)⁻¹ • W.Om 1 g' e0`. Rewrite using `[hJ, smul_smul, inv_mul_cancel₀ hc0, one_smul]`.

Establish `hJT : Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)) e0 ∈ TT D (tor0 D ⊤ δ) a d`. Rewrite using `[hJe]`. Conclude with `TT_smul _ (W.maps 1 g' e0 hT)`. Establish `hkJ : W.Om k 1 (Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)) e0) = Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)) e0`. Establish `e1` using `W.mul k 1 1 g' e0 hT`.

Establish `e2` using `W.mul 1 k g' 1 e0 hT`. Rewrite `e1` using `[mul_one, one_mul]`. Rewrite `e2` using `[one_mul, mul_one, hk0]`. Rewrite using `[hJe, W.smul _ _ _ _ (W.maps 1 g' e0 hT), ← e1, e2]`. Establish `hx₀` using `pt_unitBlock_mem (D := D) δ o a d`.

Take `⟨m, hm, hlift⟩` from `W.lift k 1 (unitBlock D o a d) _ hJT`. Take `⟨w, hw𝔪, hclose⟩` from `GlobalTheory.T.exists_ideal_matrix_approx_congruent_one_translate D 𝔪 h𝔪 k hk hck (unitBlock D o a d) (unitBlock_int D o a d) m hm`. Establish `hw` using `GlobalTheory.T.thetaPoint_mem_standard_and_skewLattice_of_entries_mem D δ 𝔪 w hw𝔪`. Establish `hBk : KLat D (tor0 D ⊤ δ) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d))` using `VacMove.klat _ (VacMove.moves_one D a) hg'm`. Establish `hJB` using `GlobalTheory.T.latticeIntertwiner_standard_to_skew_mem_thetaSpace D δ hc e0 he 𝔪 hsd`.

Establish `hWJ` using `hlift _ hclose`. Rewrite `hWJ` using `[hkJ, VacMove.pt_add, ← weylTranslate_add_of_mem_baseLattice hc he W.nz hx₀ hw.1, VacMove.wd_fix h1 hc hBk hJB hw.2]`. Unfold `cosetV`. Rewrite using `[W.smul _ _ _ _ (GlobalTheory.FinWeil.RatTransl.wd_mem_TT D h1 ⊤ δ hc a d _ _ hJT), hWJ]`.
-/
theorem om_cosetV_of_congOne : ∀ (D : D7) (δ t0 : ℂ), Crv D ⊤ δ → ∀ {a d : ℕ} (e0 : VC D a d → ℂ), oddE0 D ⊤ δ t0 a d e0 → ∀ (W : WeilO D ⊤ δ a d e0) (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ≠ ⊥ → IsCoprime 𝔪 (D.host.conj • 𝔪) → (∀ u, IntU D u → (u : AE D) - 1 ∈ hatId D (𝔪 * D.host.conj • 𝔪) → W.chV'.f u = 1) → ∀ o : ℕ, o + a ≤ d → ∀ k ∈ intG D a, CongOne D 𝔪 k → W.Om k 1 (cosetV D δ 𝔪 o a d e0) = cosetV D δ 𝔪 o a d e0 := by
  intro D δ t0 hc a d e0 hv W 𝔪 h𝔪 hcop hch o ho k hk hck
  have h1 := (GlobalTheory.InducedType.induced_type D).1
  have he := hv.1
  have hT := VacMove.vac_TT h1 hc he

  have hk0 : W.Om k 1 e0 = e0 := by
    obtain ⟨ks, ki, x, hkk, hks, hki, hss, hsi, hxq, hxd, hxu, η, hη, hx1⟩ := GlobalTheory.T.exists_split_inert_factorization_unitaryLatticeStabilizer D k hk
    have hi : W.Om ki 1 e0 = e0 :=
      W.inert ki 1 ((mem_intG ki).1 hki) ((mem_intG 1).1 (one_mem _)) hsi (suppInert_one D d)
    have hs : W.Om ks 1 e0 = e0 := by
      have hm : Moves D (ks : GL (Fin a) (AE D)) (stdL D a) := by
        simpa using VacMove.moves_mul_int hks (VacMove.moves_one D a)
      have hx : W.chV'.f x = 1 := hch x hxu (by rw [hx1]; exact hatId_mul hη (GlobalTheory.T.unitary_congruent_one_det_sub_one_mem_ideal_mul_conj D 𝔪 hcop k hk hck))
      rw [W.split ks 1 x 1 (stdL D a) (stdL D d) hss (suppSplit_one D d)
        (fun q hq hi => ⟨hxq q hq hi, by simpa using zeroAt_zero D q⟩) hxd (by simp) hm (VacMove.moves_one D d)]
      simp only [hx, map_one, one_zpow, mul_one, Units.val_one, one_mul]
      exact VacMove.iop_self D _ (La0 D (tor0 D ⊤ δ) a d) he
    have := W.mul ks ki 1 1 e0 hT
    rw [mul_one, ← hkk] at this
    rw [this, hi, hs]

  obtain ⟨g', x', hg's, hg'm, hx'q, hx'd⟩ := GlobalTheory.T.exists_splitSupported_unitary_moving_to_selfDualSkewLattice D 𝔪 h𝔪 hcop d
  have hsd : SD D (skewLat D 𝔪 d) := VacMove.sd_of_moves hg'm
  have hJ : W.Om 1 g' e0 = ((W.chV.f x' ^ W.ep * W.chV'.f 1 ^ W.ep' : ℂˣ) : ℂ) •
      Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)) e0 := by
    rw [W.split 1 g' 1 x' (stdL D a) (skewLat D 𝔪 d) (suppSplit_one D a) hg's
      (fun q hq hi => ⟨by simpa using zeroAt_zero D q, hx'q q hq hi⟩) (by simp) hx'd (VacMove.moves_one D a) hg'm]
    rfl
  have hc0 : ((W.chV.f x' ^ W.ep * W.chV'.f 1 ^ W.ep' : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  have hJe : Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)) e0 =
      ((W.chV.f x' ^ W.ep * W.chV'.f 1 ^ W.ep' : ℂˣ) : ℂ)⁻¹ • W.Om 1 g' e0 := by
    rw [hJ, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  have hJT : Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)) e0 ∈
      TT D (tor0 D ⊤ δ) a d := by
    rw [hJe]; exact TT_smul _ (W.maps 1 g' e0 hT)
  have hkJ : W.Om k 1 (Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)) e0) =
      Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)) e0 := by
    have e1 := W.mul k 1 1 g' e0 hT
    have e2 := W.mul 1 k g' 1 e0 hT
    rw [mul_one, one_mul] at e1
    rw [one_mul, mul_one, hk0] at e2
    rw [hJe, W.smul _ _ _ _ (W.maps 1 g' e0 hT), ← e1, e2]

  have hx₀ := pt_unitBlock_mem (D := D) δ o a d
  obtain ⟨m, hm, hlift⟩ := W.lift k 1 (unitBlock D o a d) _ hJT
  obtain ⟨w, hw𝔪, hclose⟩ := GlobalTheory.T.exists_ideal_matrix_approx_congruent_one_translate D 𝔪 h𝔪 k hk hck (unitBlock D o a d) (unitBlock_int D o a d) m hm
  have hw := GlobalTheory.T.thetaPoint_mem_standard_and_skewLattice_of_entries_mem D δ 𝔪 w hw𝔪
  have hBk : KLat D (tor0 D ⊤ δ) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)) :=
    VacMove.klat _ (VacMove.moves_one D a) hg'm
  have hJB := GlobalTheory.T.latticeIntertwiner_standard_to_skew_mem_thetaSpace D δ hc e0 he 𝔪 hsd
  have hWJ := hlift _ hclose
  rw [hkJ, VacMove.pt_add, ← weylTranslate_add_of_mem_baseLattice hc he W.nz hx₀ hw.1, VacMove.wd_fix h1 hc hBk hJB hw.2] at hWJ
  unfold cosetV
  rw [W.smul _ _ _ _ (GlobalTheory.FinWeil.RatTransl.wd_mem_TT D h1 ⊤ δ hc a d _ _ hJT), hWJ]

end GlobalTheory.FunObj.FixKey
