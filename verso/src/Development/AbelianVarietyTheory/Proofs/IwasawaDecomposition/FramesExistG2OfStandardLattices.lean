import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.FrameExistence.NormalFrameClauses
import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
import Formalism.LocalToGlobal.IndefiniteReal.FrameExistence.FramesExistOfDiagonalTypePlaces
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsDecompChainSpaceDefiniteAddNormalFrame
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAuxiliaryHyperbolicVectors
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompletelySplitPrimeHostPlaceProperties
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEqMulOfResSNeOne

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.NormalFramesLevels

open GlobalTheory.IndefiniteRowSideFullHecke.ChainMatrices GlobalTheory.StdFrames Formalism.IndefR.Mi

variable {D : D7}

def normalFrameVectorSequences (D : D7) : ∀ j : ℕ, (ℕ → (D.sp.Y j).V) × (ℕ → (D.sp.Y j).V) × (D.sp.Y j).V
  | 0 => (fun i => if h : i < D.R.rS then D.sp.hypE ⟨i, h⟩ else 0,
      fun i => if h : i < D.R.rS then D.sp.hypF ⟨i, h⟩ else 0, D.sp.zm)
  | j + 1 => if h : j + 1 < D.R.m then
      (Classical.choose (GlobalTheory.StandardGramVectors.exists_auxiliaryHyperbolicVectors D (j + 1) h),
        Classical.choose (Classical.choose_spec (GlobalTheory.StandardGramVectors.exists_auxiliaryHyperbolicVectors D (j + 1) h)),
        Classical.choose (Classical.choose_spec (Classical.choose_spec (GlobalTheory.StandardGramVectors.exists_auxiliaryHyperbolicVectors D (j + 1) h))))
    else (0, 0, 0)

/- English proof (translation)
Consider the cases of `j with`. Consider the case `zero => exact isAuxiliaryHyperbolicPart_initialChainSpace`. Consider the case `succ j`. Simplify using `only [normalFrameVectorSequences, dif_pos hj]`. Conclude with `Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (GlobalTheory.StandardGramVectors.exists_auxiliaryHyperbolicVectors D (j + 1) hj)))`.
-/
theorem normal_frame_level_conditions_at (j : ℕ) (hj : j < D.R.m) : IsAuxiliaryHeckeCharacter D j (normalFrameVectorSequences D j).1 (normalFrameVectorSequences D j).2.1 (normalFrameVectorSequences D j).2.2 := by
  cases j with
  | zero => exact isAuxiliaryHyperbolicPart_initialChainSpace
  | succ j =>
    simp only [normalFrameVectorSequences, dif_pos hj]
    exact Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (GlobalTheory.StandardGramVectors.exists_auxiliaryHyperbolicVectors D (j + 1) hj)))

def gam (D : D7) (j : ℕ) : GL (Fin (D.sp.X j).rank) (Ef D) := Classical.choose (exists_base (D.sp.X j))

/- English proof (translation)
Use extensionality with `x`. Simplify using `only [Formalism.L2.Herm.crdLat, l0X, Submodule.mem_map, Submodule.mem_comap, Formalism.L2.Herm.crd, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, rfl⟩`. Simplify using `using hy`.

Introduce `hx`. Conclude with `⟨_, hx, V.frame.equivFun.apply_symm_apply x⟩`.
-/
theorem crdLat_eq_l0X (V : HSp D) : Formalism.L2.Herm.crdLat V V.L0 = l0X V := by
  ext x
  simp only [Formalism.L2.Herm.crdLat, l0X, Submodule.mem_map, Submodule.mem_comap, Formalism.L2.Herm.crd,
    LinearMap.coe_restrictScalars, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro hx
    exact ⟨_, hx, V.frame.equivFun.apply_symm_apply x⟩

/- English proof (translation)
Take `⟨e, he, hM⟩` from `h`. Establish `h1` using `congrArg (cpt PP) (hM i j)`. Rewrite `h1` using `[map_mul, map_mul, (cpt_of_isIdemAt he).1, one_mul, one_mul]`. Use `cpt_ext fun Q => ?_` and prove the remaining obligations. Rewrite using `[map_mul, map_mul]`.

Distinguish the cases in `hQ : Q = PP`. Substitute `hQ` using the available equality. Rewrite using `[h1]`. Rewrite using `[(cpt_of_isIdemAt hei).2 Q hQ, zero_mul, zero_mul]`.
-/
theorem agree_all {PP : Pl D.host.E} {a b : ℕ} {M M' : Matrix (Fin a) (Fin b) (Ef D)} (h : AgreeAt PP M M')
    {ei : AE D} (hei : Formalism.L2.NTheta.IsIdemAt ei PP) (i : Fin a) (j : Fin b) :
    toEAf D ei * M i j = toEAf D ei * M' i j := by
  obtain ⟨e, he, hM⟩ := h
  have h1 := congrArg (cpt PP) (hM i j)
  rw [map_mul, map_mul, (cpt_of_isIdemAt he).1, one_mul, one_mul] at h1
  refine cpt_ext fun Q => ?_
  rw [map_mul, map_mul]
  by_cases hQ : Q = PP
  · subst hQ
    rw [h1]
  · rw [(cpt_of_isIdemAt hei).2 Q hQ, zero_mul, zero_mul]

end GlobalTheory.NormalFramesLevels

namespace GlobalTheory.NormalFramesLevels

open GlobalTheory.IndefiniteRowSideFullHecke.ChainMatrices GlobalTheory.StdFrames Formalism.IndefR.Mi

variable {D : D7}

/- English proof (translation)
The claim follows from `(GlobalTheory.Mem.Chr.splitsC_main D.R D.host (D.host.g l) (D.host.g_prime l) (D.nd.g_split l) PP (P.overP h)).1`.
-/
theorem absNorm_of_div (P : Formalism.L2.Host.PiBar D.host) {l : Fin 2} {PP : Pl D.host.E} (h : P.Div l PP) :
    Ideal.absNorm PP.asIdeal = D.host.g l :=
  (GlobalTheory.Mem.Chr.splitsC_main D.R D.host (D.host.g l) (D.host.g_prime l) (D.nd.g_split l) PP (P.overP h)).1

/- English proof (translation)
Introduce `hTm`. Establish `hg : ((D.host.g l : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal` using `P.overP h`. Establish `hmod : D.sp.T % D.host.g l = 1`. Rewrite using `[D.sp_T]`. Conclude with `D.T_mod_g D.u₀ l`.

Establish `hdiv` using `Nat.div_add_mod D.sp.T (D.host.g l)`. Rewrite `hdiv` using `[hmod]`. Establish `hE : ((D.sp.T : ℕ) : 𝓞 D.host.E) = ((D.host.g l : ℕ) : 𝓞 D.host.E) * ((D.sp.T / D.host.g l : ℕ) : 𝓞 D.host.E) + 1`. Conclude with `hdiv.symm` after adjusting the coercions. Rewrite `hTm` using `[hE]`.

Establish `h1 : (1 : 𝓞 D.host.E) ∈ PP.asIdeal` using `(Ideal.add_mem_iff_right _ (Ideal.mul_mem_right _ _ hg)).mp hTm`. Conclude with `PP.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h1)`.
-/
theorem T_not_mem (P : Formalism.L2.Host.PiBar D.host) {l : Fin 2} {PP : Pl D.host.E} (h : P.Div l PP) :
    ((D.sp.T : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal := by
  intro hTm
  have hg : ((D.host.g l : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := P.overP h
  have hmod : D.sp.T % D.host.g l = 1 := by
    rw [D.sp_T]
    exact D.T_mod_g D.u₀ l
  have hdiv := Nat.div_add_mod D.sp.T (D.host.g l)
  rw [hmod] at hdiv
  have hE : ((D.sp.T : ℕ) : 𝓞 D.host.E) =
      ((D.host.g l : ℕ) : 𝓞 D.host.E) * ((D.sp.T / D.host.g l : ℕ) : 𝓞 D.host.E) + 1 := by
    exact_mod_cast hdiv.symm
  rw [hE] at hTm
  have h1 : (1 : 𝓞 D.host.E) ∈ PP.asIdeal :=
    (Ideal.add_mem_iff_right _ (Ideal.mul_mem_right _ _ hg)).mp hTm
  exact PP.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h1)

/- English proof (translation)
Establish `: ((D.sp.T : ℕ) : D.host.E) = algebraMap (𝓞 D.host.E) D.host.E ((D.sp.T : ℕ) : 𝓞 D.host.E)` using `by simp`. Rewrite using `[this, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]`. Conclude with `T_not_mem P h`.
-/
theorem valuation_splitTraceElement_eq_one (P : Formalism.L2.Host.PiBar D.host) {l : Fin 2} {PP : Pl D.host.E} (h : P.Div l PP) :
    PP.valuation D.host.E ((D.sp.T : ℕ) : D.host.E) = 1 := by
  have : ((D.sp.T : ℕ) : D.host.E) = algebraMap (𝓞 D.host.E) D.host.E ((D.sp.T : ℕ) : 𝓞 D.host.E) := by simp
  rw [this, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]
  exact T_not_mem P h

def bI (D : D7) (j : ℕ) : ℕ := (D.R.m - 1 - j) / 2 + (D.R.m - 1 - j) % 2

def sgT (D : D7) (j : ℕ) : D.host.E := if Even j then -(D.sp.T : D.host.E) else (D.sp.T : D.host.E)

def kap (D : D7) (j i : ℕ) : D.host.E := if i + 1 = bI D j then sgT D j else 1

/- English proof (translation)
Proceed by induction on `i with`. Consider the case `zero => simp [nfScal, show ¬ bI D j ≤ 0 by omega]`. Consider the case `succ i ih`. Simplify using `only [nfScal, ih, kap]`. Distinguish the cases in `h1 : i + 1 = bI D j`.

Rewrite using `[if_pos h1, if_neg (by omega), if_pos (by omega), mul_one]`. Rewrite using `[if_neg h1, one_mul]`. Distinguish the cases in `h2 : bI D j ≤ i`. Rewrite using `[if_pos h2, if_pos (by omega)]`. Rewrite using `[if_neg h2, if_neg (by omega)]`.
-/
theorem nfScal_kap (j : ℕ) (hb : 0 < bI D j) (i : ℕ) :
    nfScal (kap D) (fun _ => 1) j i = if bI D j ≤ i then sgT D j else 1 := by
  induction i with
  | zero => simp [nfScal, show ¬ bI D j ≤ 0 by omega]
  | succ i ih =>
    simp only [nfScal, ih, kap]
    by_cases h1 : i + 1 = bI D j
    · rw [if_pos h1, if_neg (by omega), if_pos (by omega), mul_one]
    · rw [if_neg h1, one_mul]
      by_cases h2 : bI D j ≤ i
      · rw [if_pos h2, if_pos (by omega)]
      · rw [if_neg h2, if_neg (by omega)]

/- English proof (translation)
Establish `hT : (D.sp.T : D.host.E) ≠ 0`. Establish `hmod : D.sp.T % D.host.g 0 = 1` using `by rw [D.sp_T]; exact D.T_mod_g D.u₀ 0`. Establish `: D.sp.T ≠ 0` using `fun h => by rw [h] at hmod; simp at hmod`. Conclude with `this` after adjusting the coercions. Unfold `sgT`.

Use `split_ifs`. Conclude with `neg_ne_zero.2 hT`. Conclude with `hT`.
-/
theorem sgT_ne {j : ℕ} : sgT D j ≠ 0 := by
  have hT : (D.sp.T : D.host.E) ≠ 0 := by
    have hmod : D.sp.T % D.host.g 0 = 1 := by rw [D.sp_T]; exact D.T_mod_g D.u₀ 0
    have : D.sp.T ≠ 0 := fun h => by rw [h] at hmod; simp at hmod
    exact_mod_cast this
  unfold sgT; split_ifs
  · exact neg_ne_zero.2 hT
  · exact hT

/- English proof (translation)
Unfold `kap`. Use `split_ifs`. Conclude with `sgT_ne`. Conclude with `one_ne_zero`.
-/
theorem kap_ne (j i : ℕ) : kap D j i ≠ 0 := by
  unfold kap; split_ifs
  · exact sgT_ne
  · exact one_ne_zero

/- English proof (translation)
Substitute `h` using the available equality. Conclude with `hs`.
-/
theorem shape_cast {T : Type} (L : LevCh D T) (γ : ∀ j, GL (Fin (D.sp.X j).rank) (Ef D))
    (E Ev : ∀ j, ℕ → (D.sp.Y j).V) (z : ∀ j, (D.sp.Y j).V) (n j : ℕ) (h : n = j)
    (hT : GL (Fin (D.sp.Y n).rank) (EAf D) = GL (Fin (D.sp.Y j).rank) (EAf D)) (β : GL (Fin (D.sp.Y n).rank) (EAf D))
    (hs : ShapeY L n (γ n) (E n) (Ev n) (z n) β) : ShapeY L j (γ j) (E j) (Ev j) (z j) (hT ▸ β) := by
  subst h
  exact hs

/- English proof (translation)
Unfold `Seed.Frm.betaYOf`. Rewrite using `[dif_pos hj]`. Conclude with `shape_cast L γ E Ev z (min j D.R.m) j (Nat.min_eq_left hj) _ (βY j) hs`.
-/
theorem shape_betaYOf {T : Type} (L : LevCh D T) (γ : ∀ j, GL (Fin (D.sp.X j).rank) (Ef D))
    (E Ev : ∀ j, ℕ → (D.sp.Y j).V) (z : ∀ j, (D.sp.Y j).V) (βY : ∀ j, GL (Fin (Yc D j).rank) (EAf D)) (j : ℕ)
    (hj : j ≤ D.R.m) (hs : ShapeY L (min j D.R.m) (γ _) (E _) (Ev _) (z _) (βY j)) :
    ShapeY L j (γ j) (E j) (Ev j) (z j) (Seed.Frm.betaYOf βY j) := by
  unfold Seed.Frm.betaYOf
  rw [dif_pos hj]
  exact shape_cast L γ E Ev z (min j D.R.m) j (Nat.min_eq_left hj) _ (βY j) hs

end GlobalTheory.NormalFramesLevels

namespace GlobalTheory.NormalFramesLevels

open GlobalTheory.IndefiniteRowSideFullHecke.ChainMatrices GlobalTheory.StdFrames Formalism.IndefR.Mi

variable {D : D7}

/- English proof (translation)
Substitute `h` using the available equality. Conclude with `ht`.
-/
theorem transport_cast (Pg : Finset (Pl D.host.E)) (W : HSp D) (βW : GL (Fin W.rank) (Ef D)) (n : ℕ) (h : n = 0)
    (hT : GL (Fin (D.sp.Y n).rank) (EAf D) = GL (Fin (D.sp.Y 0).rank) (EAf D)) (β : GL (Fin (D.sp.Y n).rank) (EAf D))
    (ht : Transport Pg W (D.sp.Y n) βW β) : Transport Pg W (D.sp.Y 0) βW (hT ▸ β) := by
  subst h
  exact ht

/- English proof (translation)
Unfold `Seed.Frm.betaYOf`. Rewrite using `[dif_pos (Nat.zero_le _)]`. Conclude with `transport_cast Pg W βW (min 0 D.R.m) (Nat.zero_min _) (by rw [Nat.zero_min]) (βY 0) ht`.
-/
theorem transport_betaYOf (Pg : Finset (Pl D.host.E)) (W : HSp D) (βW : GL (Fin W.rank) (Ef D))
    (βY : ∀ j, GL (Fin (Yc D j).rank) (EAf D)) (ht : Transport Pg W (Yc D 0) βW (βY 0)) :
    Transport Pg W (D.sp.Y 0) βW (Seed.Frm.betaYOf βY 0) := by
  unfold Seed.Frm.betaYOf
  rw [dif_pos (Nat.zero_le _)]
  exact transport_cast Pg W βW (min 0 D.R.m) (Nat.zero_min _) (by rw [Nat.zero_min]) (βY 0) ht

section Gen

variable {R : Type} [CommRing R]

/- English proof (translation)
Establish `hx : x = βA.val * y * (βB⁻¹).val`. Rewrite using `[← hxy, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]`. Establish `h1 : x * (βB.val * y' * (βA⁻¹).val) = 1`. Rewrite using `[hx]`. Simplify using `only [Matrix.mul_assoc]`.

Rewrite using `[← Matrix.mul_assoc (βB⁻¹).val, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul, ← Matrix.mul_assoc y, hyy, Matrix.one_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one]`. Establish `h2 : (βB.val * y' * (βA⁻¹).val) * x = 1`. Rewrite using `[hx]`. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[← Matrix.mul_assoc (βA⁻¹).val, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul, ← Matrix.mul_assoc y', hy'y, Matrix.one_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one]`.

Use `⟨⟨x.submatrix e.symm id, (βB.val * y' * (βA⁻¹).val).submatrix id e.symm, ?_, ?_⟩, rfl, ?_⟩` and prove the remaining obligations. Rewrite using `[← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id, h1, Matrix.submatrix_one_equiv]`. Rewrite using `[← Matrix.submatrix_mul _ _ _ _ _ e.symm.bijective, h2, Matrix.submatrix_id_id]`. Establish `hy : (βA⁻¹).val * x * βB.val = y`. Rewrite using `[Matrix.mul_assoc, hxy, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]`.

Use `show (βA⁻¹).val.submatrix e.symm e.symm * x.submatrix e.symm id * βB.val = _`. Rewrite using `[← Matrix.submatrix_mul _ _ _ _ _ e.symm.bijective, ← hy]`. Use extensionality with `i k`. Simplify using `only [Matrix.mul_apply, Matrix.submatrix_apply, id]`.
-/
theorem exists_gl_of_transport {a b : ℕ} (x y : Matrix (Fin a) (Fin b) R) (y' : Matrix (Fin b) (Fin a) R)
    (βA : GL (Fin a) R) (βB : GL (Fin b) R) (hxy : x * βB.val = βA.val * y) (hyy : y * y' = 1) (hy'y : y' * y = 1)
    (e : Fin a ≃ Fin b) :
    ∃ ι : GL (Fin b) R, ι.val = x.submatrix e.symm id ∧
      (βA⁻¹).val.reindex e e * ι.val * βB.val = y.submatrix e.symm id := by
  have hx : x = βA.val * y * (βB⁻¹).val := by
    rw [← hxy, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
  have h1 : x * (βB.val * y' * (βA⁻¹).val) = 1 := by
    rw [hx]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (βB⁻¹).val, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul,
      ← Matrix.mul_assoc y, hyy, Matrix.one_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have h2 : (βB.val * y' * (βA⁻¹).val) * x = 1 := by
    rw [hx]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (βA⁻¹).val, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul,
      ← Matrix.mul_assoc y', hy'y, Matrix.one_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  refine ⟨⟨x.submatrix e.symm id, (βB.val * y' * (βA⁻¹).val).submatrix id e.symm, ?_, ?_⟩, rfl, ?_⟩
  · rw [← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id, h1, Matrix.submatrix_one_equiv]
  · rw [← Matrix.submatrix_mul _ _ _ _ _ e.symm.bijective, h2, Matrix.submatrix_id_id]
  · have hy : (βA⁻¹).val * x * βB.val = y := by
      rw [Matrix.mul_assoc, hxy, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
    show (βA⁻¹).val.submatrix e.symm e.symm * x.submatrix e.symm id * βB.val = _
    rw [← Matrix.submatrix_mul _ _ _ _ _ e.symm.bijective, ← hy]
    ext i k
    simp only [Matrix.mul_apply, Matrix.submatrix_apply, id]

/- English proof (translation)
Rewrite using `[Matrix.reindex_apply]`. Establish `: Formalism.UG.cT σ (x.submatrix e.symm id) = (Formalism.UG.cT σ x).submatrix id e.symm`. Use extensionality with `i k`. Simplify using `[Formalism.UG.cT]`. Rewrite using `[this, ← Matrix.submatrix_mul _ _ _ _ _ e.symm.bijective, ← Matrix.submatrix_mul _ _ _ _ _ e.symm.bijective, Matrix.submatrix_id_id]`.
-/
theorem cT_reindex_mul {a b : ℕ} (σ : R →+* R) (x : Matrix (Fin a) (Fin b) R) (G : Matrix (Fin a) (Fin a) R)
    (e : Fin a ≃ Fin b) :
    Formalism.UG.cT σ (x.submatrix e.symm id) * G.reindex e e * x.submatrix e.symm id = Formalism.UG.cT σ x * G * x := by
  rw [Matrix.reindex_apply]
  have : Formalism.UG.cT σ (x.submatrix e.symm id) = (Formalism.UG.cT σ x).submatrix id e.symm := by
    ext i k; simp [Formalism.UG.cT]
  rw [this, ← Matrix.submatrix_mul _ _ _ _ _ e.symm.bijective, ← Matrix.submatrix_mul _ _ _ _ _ e.symm.bijective,
    Matrix.submatrix_id_id]

end Gen

/- English proof (translation)
Take `⟨x, y, y', hiso, hxy, -, -, hyy', hy'y, hag⟩` from `ht`. Take `⟨ι, hι, hM⟩` from `exists_gl_of_transport x y y' βY0 βW hxy hyy' hy'y (finCongr hr)`. Use `⟨finCongr hr, ι, fun k => rfl, ?_, fun PP hPP ei hei => ?_⟩` and prove the remaining obligations. Rewrite using `[hι, Matrix.reindex_apply, ← Matrix.submatrix_map, ← Matrix.reindex_apply]`. Conclude with `(cT_reindex_mul _ x _ (finCongr hr)).trans hiso`.

Take `⟨hint, hres⟩` from `GlobalTheory.IdemRes.resS_idem_eq_one D ei PP hei`. Establish `hS : toEAf D ei • ((βY0⁻¹ : GL (Fin (D.sp.Y 0).rank) (Ef D)).val.reindex (finCongr hr) (finCongr hr) * ι.val * βW.val) = toEAf D ei • (1 : Matrix (Fin (D.sp.W j).rank) (Fin (D.sp.W j).rank) (Ef D))`. Rewrite using `[hM]`. Use extensionality with `a b`. Simplify using `only [Matrix.smul_apply, Matrix.submatrix_apply, id, smul_eq_mul]`.

Rewrite using `[agree_all (hag PP hPP) hei _ b, Matrix.of_apply, Matrix.one_apply]`. Use `congr 1`. Simplify using `[Fin.ext_iff]`. Rewrite using `[hS]`. Establish `hmem : ∀ a b, (toEAf D ei • (1 : Matrix (Fin (D.sp.W j).rank) (Fin (D.sp.W j).rank) (Ef D))) a b ∈ Formalism.L2.Herm.intAf D.host.F D.host.E` using `fun a b => by`.

Rewrite using `[Matrix.smul_apply, smul_eq_mul]`. Conclude with `mul_mem hint (one_entry_mem _ a b)`. Use `⟨hmem, ?_⟩` and prove the remaining obligations. Use extensionality with `a b`. Unfold `redM`.

Rewrite using `[dif_pos (hmem a b), Matrix.one_apply]`. Distinguish the cases in `hab : a = b`. Rewrite using `[if_pos hab]`. Substitute `hab` using the available equality. Use `hres using 2` and compare the differences between its conclusion and the goal.

Simplify using the standard rewrite rules. Rewrite using `[if_neg hab]`. Use `map_zero (Formalism.L2.DIV.resS D.host.F PP) using 2` and compare the differences between its conclusion and the goal. Simplify using `[hab]`.
-/
theorem vertexAt_of_transport (Pg : Finset (Pl D.host.E)) (j : ℕ) (hr : (D.sp.Y 0).rank = (D.sp.W j).rank)
    (βY0 : GL (Fin (D.sp.Y 0).rank) (Ef D)) (βW : GL (Fin (D.sp.W j).rank) (Ef D))
    (ht : Transport Pg (D.sp.W j) (D.sp.Y 0) βW βY0) :
    ∃ (e : Fin (D.sp.Y 0).rank ≃ Fin (D.sp.W j).rank) (ι : GL (Fin (D.sp.W j).rank) (Ef D)),
      VertexAt j βY0 βW e ι Pg := by
  obtain ⟨x, y, y', hiso, hxy, -, -, hyy', hy'y, hag⟩ := ht
  obtain ⟨ι, hι, hM⟩ := exists_gl_of_transport x y y' βY0 βW hxy hyy' hy'y (finCongr hr)
  refine ⟨finCongr hr, ι, fun k => rfl, ?_, fun PP hPP ei hei => ?_⟩
  · rw [hι, Matrix.reindex_apply, ← Matrix.submatrix_map, ← Matrix.reindex_apply]
    exact (cT_reindex_mul _ x _ (finCongr hr)).trans hiso
  · obtain ⟨hint, hres⟩ := GlobalTheory.IdemRes.resS_idem_eq_one D ei PP hei
    have hS : toEAf D ei • ((βY0⁻¹ : GL (Fin (D.sp.Y 0).rank) (Ef D)).val.reindex (finCongr hr) (finCongr hr) *
        ι.val * βW.val) = toEAf D ei • (1 : Matrix (Fin (D.sp.W j).rank) (Fin (D.sp.W j).rank) (Ef D)) := by
      rw [hM]
      ext a b
      simp only [Matrix.smul_apply, Matrix.submatrix_apply, id, smul_eq_mul]
      rw [agree_all (hag PP hPP) hei _ b, Matrix.of_apply, Matrix.one_apply]
      congr 1
      simp [Fin.ext_iff]
    rw [hS]
    have hmem : ∀ a b, (toEAf D ei • (1 : Matrix (Fin (D.sp.W j).rank) (Fin (D.sp.W j).rank) (Ef D))) a b ∈
        Formalism.L2.Herm.intAf D.host.F D.host.E := fun a b => by
      rw [Matrix.smul_apply, smul_eq_mul]
      exact mul_mem hint (one_entry_mem _ a b)
    refine ⟨hmem, ?_⟩
    ext a b
    unfold redM
    rw [dif_pos (hmem a b), Matrix.one_apply]
    by_cases hab : a = b
    · rw [if_pos hab]
      subst hab
      convert hres using 2
      simp
    · rw [if_neg hab]
      convert map_zero (Formalism.L2.DIV.resS D.host.F PP) using 2
      simp [hab]

end GlobalTheory.NormalFramesLevels

namespace GlobalTheory.NormalFramesLevels

open GlobalTheory.IndefiniteRowSideFullHecke.ChainMatrices GlobalTheory.StdFrames Formalism.IndefR.Mi

variable {D : D7}

def eC (D : D7) (j i : ℕ) : Fin (D.sp.Y j).rank → D.host.E := ⇑((D.sp.Y j).frame.repr ((normalFrameVectorSequences D j).1 i))

def evC (D : D7) (j i : ℕ) : Fin (D.sp.Y j).rank → D.host.E := ⇑((D.sp.Y j).frame.repr ((normalFrameVectorSequences D j).2.1 i))

def zC (D : D7) (j : ℕ) : Fin (D.sp.Y j).rank → D.host.E := ⇑((D.sp.Y j).frame.repr (normalFrameVectorSequences D j).2.2)

/- English proof (translation)
Take `⟨a, ha⟩` from `D.R.m_even`. Rewrite using `[Nat.even_iff]`. Use linear arithmetic over natural numbers and integers.
-/
theorem even_iff_odd_c {j : ℕ} (hj : j < D.R.m) : Even j ↔ (D.R.m - 1 - j) % 2 = 1 := by
  obtain ⟨a, ha⟩ := D.R.m_even
  rw [Nat.even_iff]
  omega

/- English proof (translation)
Use extensionality with `r l`. Simplify using `[xMat, ratM, xInY, frameMat, LinearMap.toMatrix_apply]`.
-/
theorem xMat_eq (j : ℕ) : xMat (D := D) j = ratM (frameMat (D.sp.Y j) (D.sp.X j) (D.sp.iXY j)) := by
  ext r l
  simp [xMat, ratM, xInY, frameMat, LinearMap.toMatrix_apply]

/- English proof (translation)
Unfold `colX`. Rewrite using `[dif_pos h, xMat_eq]`. Simplify using `only [mulM, Matrix.mul_apply, Matrix.mulVec, dotProduct]`.
-/
theorem colX_eq (j : ℕ) (γ : GL (Fin (D.sp.X j).rank) (Ef D)) (n : ℕ) (h : n < (D.sp.X j).rank)
    (r : Fin (D.sp.Y j).rank) : colX D j γ n r = (xMat (D := D) j).mulVec (fun i => γ.val i ⟨n, h⟩) r := by
  unfold colX
  rw [dif_pos h, xMat_eq]
  simp only [mulM, Matrix.mul_apply, Matrix.mulVec, dotProduct]

end GlobalTheory.NormalFramesLevels

namespace GlobalTheory.NormalFramesLevels

open GlobalTheory.IndefiniteRowSideFullHecke.ChainMatrices GlobalTheory.StdFrames Formalism.IndefR.Mi

variable {D : D7}

/- English proof (translation)
Rewrite using `[← (D.sp.Y j).herm.eq y x, h]`. Conclude with `hc`.
-/
theorem hT_swap {j : ℕ} (x y : (D.sp.Y j).V) {c : D.host.E} (h : (D.sp.Y j).hT y x = c) (hc : star c = c) :
    (D.sp.Y j).hT x y = c := by
  rw [← (D.sp.Y j).herm.eq y x, h]
  exact hc

/- English proof (translation)
Introduce `j hj`. Take `⟨hA, hB, hC⟩` from `normal_frame_level_conditions_at j hj`. Establish `hpar` using `even_iff_odd_c hj`. Simplify using `only [nAux] at hA hB hC`. Simplify using `only [eC, evC, zC, Seed.Frm.vecY_repr]`.

Use `⟨fun i hi l hl => ⟨?_, ?_, ?_⟩, fun hc => ?_, fun x i' hi' => ?_⟩` and prove the remaining obligations. Apply the tactic sequence `refine hT_swap _ _ (hA i hi l hl).2.2 ?_ split_ifs <;> simp`. Conclude with `(hA l hl i hi).1`. Conclude with `(hA l hl i hi).2.1`. Take `⟨h1, -, h3⟩` from `hC (hpar.2 hc)`.

Conclude with `⟨h1, fun i hi => ⟨(h3 i hi).1, (h3 i hi).2⟩⟩`. Unfold `adaptedVector split_ifs with h1 h2`. Simplify using `only [eC, Seed.Frm.vecY_repr]`. Conclude with `(hB _ h1 x).1`. Simplify using `only [zC, Seed.Frm.vecY_repr]`.

Conclude with `(hC (hpar.2 h2.1)).2.1 x`. Simplify using `only [evC, Seed.Frm.vecY_repr]`. Use `(hB _ ?_ x).2` and prove the remaining obligations. Distinguish the cases in `hc : (D.R.m - 1 - j) % 2 = 1`. Establish `: i' ≠ (D.R.m - 1 - j) / 2` using `fun h => h2 ⟨hc, h⟩`.

Use linear arithmetic over natural numbers and integers. Use linear arithmetic over natural numbers and integers.
-/
theorem normal_frame_level_conditions_C : IsAdaptedVectorSystem (eC D) (evC D) (zC D) := by
  intro j hj
  obtain ⟨hA, hB, hC⟩ := normal_frame_level_conditions_at j hj
  have hpar := even_iff_odd_c hj
  simp only [nAux] at hA hB hC
  simp only [eC, evC, zC, Seed.Frm.vecY_repr]
  refine ⟨fun i hi l hl => ⟨?_, ?_, ?_⟩, fun hc => ?_, fun x i' hi' => ?_⟩
  · refine hT_swap _ _ (hA i hi l hl).2.2 ?_
    split_ifs <;> simp
  · exact (hA l hl i hi).1
  · exact (hA l hl i hi).2.1
  · obtain ⟨h1, -, h3⟩ := hC (hpar.2 hc)
    exact ⟨h1, fun i hi => ⟨(h3 i hi).1, (h3 i hi).2⟩⟩
  · unfold adaptedVector
    split_ifs with h1 h2
    · simp only [eC, Seed.Frm.vecY_repr]
      exact (hB _ h1 x).1
    · simp only [zC, Seed.Frm.vecY_repr]
      exact (hC (hpar.2 h2.1)).2.1 x
    · simp only [evC, Seed.Frm.vecY_repr]
      refine (hB _ ?_ x).2
      by_cases hc : (D.R.m - 1 - j) % 2 = 1
      · have : i' ≠ (D.R.m - 1 - j) / 2 := fun h => h2 ⟨hc, h⟩
        omega
      · omega

end GlobalTheory.NormalFramesLevels

namespace GlobalTheory.NormalFramesLevels

open GlobalTheory.IndefiniteRowSideFullHecke.ChainMatrices GlobalTheory.StdFrames Formalism.IndefR.Mi

end GlobalTheory.NormalFramesLevels

end
