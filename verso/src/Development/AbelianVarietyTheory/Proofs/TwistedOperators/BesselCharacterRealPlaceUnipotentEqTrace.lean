import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ParRowZero
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BesselCharacterGenericCharacterLaws
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExtensionAdeleRealComponentsCmType
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicUnitaryRealMulFiniteDecomposition
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdelicStripSetMeasurableReadOnRealPart
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousKapSymm
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BesselCoords

open GlobalTheory.BesselChar

section Alg

variable {R : Type} [CommRing R] {n r : ℕ}

/- English proof (translation)
Use `choose a ha using h`. Establish `e1 : (U - 1) * E = E * (Matrix.of a)ᵀ`. Use extensionality with `k i`. Conclude with `congr_fun (ha i) k`. Rewrite using `[Matrix.mul_assoc, e1, ← Matrix.mul_assoc L, hL, Matrix.one_mul, sub_self]`.
-/
theorem cols_resid {L : Matrix (Fin r) (Fin n) R} {E : Matrix (Fin n) (Fin r) R} (hL : L * E = 1)
    {U : Matrix (Fin n) (Fin n) R} (h : ∀ i : Fin r, ∃ a : Fin r → R, (U - 1) *ᵥ (fun k => E k i) = E *ᵥ a) :
    (U - 1) * E - E * (L * (U - 1) * E) = 0 := by
  choose a ha using h
  have e1 : (U - 1) * E = E * (Matrix.of a)ᵀ := by
    ext k i
    exact congr_fun (ha i) k
  rw [Matrix.mul_assoc, e1, ← Matrix.mul_assoc L, hL, Matrix.one_mul, sub_self]

/- English proof (translation)
Establish `e2 : L *ᵥ (E *ᵥ a) = a` using `by rw [Matrix.mulVec_mulVec, hL, Matrix.one_mulVec]`. Rewrite using `[← Matrix.mulVec_mulVec, h, e2, sub_self]`.
-/
theorem vec_resid {L : Matrix (Fin r) (Fin n) R} {E : Matrix (Fin n) (Fin r) R} (hL : L * E = 1)
    {U : Matrix (Fin n) (Fin n) R} {z : Fin n → R} {a : Fin r → R} (h : (U - 1) *ᵥ z = E *ᵥ a) :
    (U - 1) *ᵥ z - E *ᵥ ((L * (U - 1)) *ᵥ z) = 0 := by
  have e2 : L *ᵥ (E *ᵥ a) = a := by rw [Matrix.mulVec_mulVec, hL, Matrix.one_mulVec]
  rw [← Matrix.mulVec_mulVec, h, e2, sub_self]

/- English proof (translation)
Establish `hm : (U - 1).map f = U.map f - 1`. Rewrite using `[Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _)]`. Rewrite using `[Matrix.map_sub _ (map_sub _), Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, hm]`.
-/
theorem cols_resid_map {S : Type} [CommRing S] (f : R →+* S) (L : Matrix (Fin r) (Fin n) R)
    (E : Matrix (Fin n) (Fin r) R) (U : Matrix (Fin n) (Fin n) R) :
    ((U - 1) * E - E * (L * (U - 1) * E)).map f =
      (U.map f - 1) * E.map f - E.map f * (L.map f * (U.map f - 1) * E.map f) := by
  have hm : (U - 1).map f = U.map f - 1 := by
    rw [Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _)]
  rw [Matrix.map_sub _ (map_sub _), Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, hm]

/- English proof (translation)
Establish `hm : (U - 1).map f = U.map f - 1`. Rewrite using `[Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _)]`. Rewrite using `[← hm, ← Matrix.map_mul, mulVec_map, mulVec_map, mulVec_map]`. Use function extensionality and compare the values at `i`. Simplify using `only [Pi.sub_apply, map_sub]`.
-/
theorem vec_resid_map {S : Type} [CommRing S] (f : R →+* S) (L : Matrix (Fin r) (Fin n) R)
    (E : Matrix (Fin n) (Fin r) R) (U : Matrix (Fin n) (Fin n) R) (z : Fin n → R) :
    (fun i => f ((((U - 1) *ᵥ z - E *ᵥ ((L * (U - 1)) *ᵥ z) : Fin n → R)) i)) =
      (U.map f - 1) *ᵥ (fun i => f (z i)) - E.map f *ᵥ ((L.map f * (U.map f - 1)) *ᵥ (fun i => f (z i))) := by
  have hm : (U - 1).map f = U.map f - 1 := by
    rw [Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _)]
  rw [← hm, ← Matrix.map_mul, mulVec_map, mulVec_map, mulVec_map]
  funext i
  simp only [Pi.sub_apply, map_sub]

/- English proof (translation)
Rewrite `h` using `[sub_eq_zero, Matrix.sub_mul, Matrix.one_mul, sub_eq_iff_eq_add']`. Conclude with `h`.
-/
theorem cols_of_resid {M : Matrix (Fin n) (Fin n) R} {E : Matrix (Fin n) (Fin r) R} {T : Matrix (Fin r) (Fin r) R}
    (h : (M - 1) * E - E * T = 0) : M * E = E + E * T := by
  rw [sub_eq_zero, Matrix.sub_mul, Matrix.one_mul, sub_eq_iff_eq_add'] at h
  exact h

/- English proof (translation)
Rewrite `h` using `[sub_eq_zero, Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_iff_eq_add']`. Conclude with `h`.
-/
theorem vec_of_resid {M : Matrix (Fin n) (Fin n) R} {E : Matrix (Fin n) (Fin r) R} {z : Fin n → R} {b : Fin r → R}
    (h : (M - 1) *ᵥ z - E *ᵥ b = 0) : M *ᵥ z = z + E *ᵥ b := by
  rw [sub_eq_zero, Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_iff_eq_add'] at h
  exact h

/- English proof (translation)
Simplify using `[coordSum, superSum]`.
-/
theorem coordSum_one (c : Fin r → R) (L : Matrix (Fin r) (Fin n) R) (E : Matrix (Fin n) (Fin r) R) (z : Fin n → R) :
    coordSum c L E z 1 = 0 := by
  simp [coordSum, superSum]

end Alg

/- English proof (translation)
Establish `key : ∀ j : Fin r, (L * (u - 1)) *ᵥ GlobalTheory.RealBessel.flagVec e z j.succ = a j`. Introduce `j`. Rewrite using `[← Matrix.mulVec_mulVec, ha j, Matrix.mulVec_mulVec, hL, Matrix.one_mulVec]`. Establish `hT : ∀ i j : Fin r, j.1 = i.1 + 1 → (L * (u - 1) * e : Matrix (Fin r) (Fin r) ℂ) i j = a i i`. Introduce `i j hij`.

Establish `hf : GlobalTheory.RealBessel.flagVec e z i.succ = fun k => e k j`. Establish `: i.succ = Fin.castSucc j` using `Fin.ext (by simp [hij])`. Rewrite using `[this, GlobalTheory.RealBessel.flagVec, Fin.snoc_castSucc]`. Use `congr_fun (key i) i` as an intermediate fact. Rewrite `this` using `[hf]`.

Rewrite using `[← this, Matrix.mul_apply]`. Simplify using `only [Matrix.mulVec, dotProduct]`. Establish `hb : ∀ i : Fin r, i.1 + 1 = r → ((L * (u - 1)) *ᵥ z) i = a i i`. Introduce `i hi`. Establish `hf : GlobalTheory.RealBessel.flagVec e z i.succ = z`.

Establish `: i.succ = Fin.last r` using `Fin.ext (by simp [hi])`. Rewrite using `[this, GlobalTheory.RealBessel.flagVec, Fin.snoc_last]`. Use `congr_fun (key i) i` as an intermediate fact. Rewrite `this` using `[hf]`. Then use the resulting hypothesis. Establish `hrow : ∀ i : Fin r, (∑ j : Fin r, if j.1 = i.1 + 1 then c i * (L * (u - 1) * e : Matrix (Fin r) (Fin r) ℂ) i j else 0) = if i.1 + 1 < r then c i * a i i else 0`.

Introduce `i`. Use `split_ifs with h`. Rewrite using `[Finset.sum_eq_single ⟨i.1 + 1, h⟩]`. Rewrite using `[if_pos rfl, hT i ⟨i.1 + 1, h⟩ rfl]`. Introduce `j _ hj`.

Rewrite using `[if_neg]`. Introduce `h'`. Conclude with `hj (Fin.ext h')`. Introduce `h'`. Conclude with `absurd (Finset.mem_univ _) h'`.

Use `Finset.sum_eq_zero fun j _ => ?_` and prove the remaining obligations. Rewrite using `[if_neg]`. Introduce `h'`. Use `j.2` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Unfold `coordSum superSum`. Simplify using `only [hrow]`. Rewrite using `[← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Use `i.2` as an intermediate fact.

Distinguish the cases in `h : i.1 + 1 < r`. Rewrite using `[if_pos h, if_neg (by omega), add_zero]`. Rewrite using `[if_neg h, if_pos (by omega), zero_add, hb i (by omega)]`.
-/
theorem coordSum_flag {n r : ℕ} (c : Fin r → ℂ) {L : Matrix (Fin r) (Fin n) ℂ} {e : Matrix (Fin n) (Fin r) ℂ}
    (hL : L * e = 1) (z : Fin n → ℂ) (u : Matrix (Fin n) (Fin n) ℂ) (a : Fin r → Fin r → ℂ)
    (ha : ∀ j : Fin r, (u - 1) *ᵥ GlobalTheory.RealBessel.flagVec e z j.succ = e *ᵥ a j) :
    coordSum c L e z u = ∑ j, c j * a j j := by
  have key : ∀ j : Fin r, (L * (u - 1)) *ᵥ GlobalTheory.RealBessel.flagVec e z j.succ = a j := by
    intro j
    rw [← Matrix.mulVec_mulVec, ha j, Matrix.mulVec_mulVec, hL, Matrix.one_mulVec]
  have hT : ∀ i j : Fin r, j.1 = i.1 + 1 → (L * (u - 1) * e : Matrix (Fin r) (Fin r) ℂ) i j = a i i := by
    intro i j hij
    have hf : GlobalTheory.RealBessel.flagVec e z i.succ = fun k => e k j := by
      have : i.succ = Fin.castSucc j := Fin.ext (by simp [hij])
      rw [this, GlobalTheory.RealBessel.flagVec, Fin.snoc_castSucc]
    have := congr_fun (key i) i
    rw [hf] at this
    rw [← this, Matrix.mul_apply]
    simp only [Matrix.mulVec, dotProduct]
  have hb : ∀ i : Fin r, i.1 + 1 = r → ((L * (u - 1)) *ᵥ z) i = a i i := by
    intro i hi
    have hf : GlobalTheory.RealBessel.flagVec e z i.succ = z := by
      have : i.succ = Fin.last r := Fin.ext (by simp [hi])
      rw [this, GlobalTheory.RealBessel.flagVec, Fin.snoc_last]
    have := congr_fun (key i) i
    rwa [hf] at this
  have hrow : ∀ i : Fin r, (∑ j : Fin r, if j.1 = i.1 + 1 then c i * (L * (u - 1) * e : Matrix (Fin r) (Fin r) ℂ) i j else 0) =
      if i.1 + 1 < r then c i * a i i else 0 := by
    intro i
    split_ifs with h
    · rw [Finset.sum_eq_single ⟨i.1 + 1, h⟩]
      · rw [if_pos rfl, hT i ⟨i.1 + 1, h⟩ rfl]
      · intro j _ hj
        rw [if_neg]
        intro h'
        exact hj (Fin.ext h')
      · intro h'; exact absurd (Finset.mem_univ _) h'
    · refine Finset.sum_eq_zero fun j _ => ?_
      rw [if_neg]
      intro h'
      have := j.2
      omega
  unfold coordSum superSum
  simp only [hrow]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have := i.2
  by_cases h : i.1 + 1 < r
  · rw [if_pos h, if_neg (by omega), add_zero]
  · rw [if_neg h, if_pos (by omega), zero_add, hb i (by omega)]

variable {D : D7}

/- English proof (translation)
Use extensionality with `i j`. Use `(GlobalTheory.StdUnn.RealComp.real_components D θ hθ).2.2.2 _ (fun ρ => ?_) ?_` and prove the remaining obligations. Conclude with `congr_fun (congr_fun (h2 ρ) i) j`. Conclude with `congr_fun (congr_fun h1 i) j`.
-/
theorem mat_eq_zero (θ : InfFam D) (hθ : IsInfFam θ) {m k : ℕ} (Y : Matrix (Fin m) (Fin k) (AE D))
    (h1 : Y.map (finPart D) = 0) (h2 : ∀ ρ, Y.map ((θ ρ).comp (infPart D)) = 0) : Y = 0 := by
  ext i j
  refine (GlobalTheory.StdUnn.RealComp.real_components D θ hθ).2.2.2 _ (fun ρ => ?_) ?_
  · exact congr_fun (congr_fun (h2 ρ) i) j
  · exact congr_fun (congr_fun h1 i) j

/- English proof (translation)
Use function extensionality and compare the values at `i`. Use `(GlobalTheory.StdUnn.RealComp.real_components D θ hθ).2.2.2 _ (fun ρ => ?_) ?_` and prove the remaining obligations. Conclude with `congr_fun (h2 ρ) i`. Conclude with `congr_fun h1 i`.
-/
theorem vec_eq_zero (θ : InfFam D) (hθ : IsInfFam θ) {m : ℕ} (Y : Fin m → AE D)
    (h1 : (fun i => finPart D (Y i)) = 0) (h2 : ∀ ρ, (fun i => (θ ρ).comp (infPart D) (Y i)) = 0) : Y = 0 := by
  funext i
  refine (GlobalTheory.StdUnn.RealComp.real_components D θ hθ).2.2.2 _ (fun ρ => ?_) ?_
  · exact congr_fun (h2 ρ) i
  · exact congr_fun h1 i

/- English proof (translation)
The claim follows from `RingHom.ext fun x => (GlobalTheory.StdUnn.RealComp.real_components D θ hθ).2.2.1 x ρ`.
-/
theorem comp_incA (θ : InfFam D) (hθ : IsInfFam θ) (ρ : D.what₂.Tau) :
    ((θ ρ).comp (infPart D)).comp (incA D) = tauE D ρ :=
  RingHom.ext fun x => (GlobalTheory.StdUnn.RealComp.real_components D θ hθ).2.2.1 x ρ

end GlobalTheory.BesselCoords

namespace GlobalTheory.BesselCoords

open GlobalTheory.BesselChar

local infixl:70 " *ₘ " => HMul.hMul

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `D θ hθ ψ A B ι d τ u hu a ha`. Take `⟨hgC, hgτ, hgρ⟩` from `GlobalTheory.PointAtPlaceHom.atTau_spec hθ B τ hu.1`. Take `⟨L, hL⟩` from `exists_leftInv d.e d.e_iso.1`. Establish `hfin : (Formalism.L2.Theta.mt B (atTau θ B τ u)).map (finPart D) = 1` using `GlobalTheory.StripBorel.mt_map_fin hgC`. Establish `hinf : ∀ ρ, (Formalism.L2.Theta.mt B (atTau θ B τ u)).map ((θ ρ).comp (infPart D)) = infMat D.sp.cm.sig B.gram (θ ρ) (atTau θ B τ u)` using `fun ρ => rfl`.

Establish `hmap : ∀ ρ {m k : ℕ} (X : Matrix (Fin m) (Fin k) D.host.E), (X.map (incA D)).map ((θ ρ).comp (infPart D)) = X.map (tauE D ρ)`. Introduce `ρ m k X`. Rewrite using `[Matrix.map_map, ← RingHom.coe_comp, comp_incA θ hθ ρ]`. Establish `hvec : ∀ ρ {m : ℕ} (x : Fin m → D.host.E), (fun i => ((θ ρ).comp (infPart D)) (incA D (x i))) = fun i => tauE D ρ (x i)`. Introduce `ρ m x`.

Use function extensionality and compare the values at `i`. Conclude with `(GlobalTheory.StdUnn.RealComp.real_components D θ hθ).2.2.1 (x i) ρ`. Establish `hL'` using `map_leftInv (incA D) hL`. Establish `hLτ` using `map_leftInv (tauE D τ) hL`. Establish `hperp : ((d.e.map (tauE D τ))ᴴ * gramAt D B τ) *ᵥ (fun k => tauE D τ (d.z k)) = 0`.

Establish `h0` using `mulVec_map (tauE D τ) (perpMat B d.e) d.z`. Rewrite `h0` using `[d.z_perpE]`. Establish `hm : (perpMat B d.e).map (tauE D τ) = (d.e.map (tauE D τ))ᴴ * gramAt D B τ`. Rewrite using `[perpMat, Matrix.map_mul]`. Use `congrArg₂ (· * ·) ?_ rfl` and prove the remaining obligations.

Use extensionality with `i j`. Simplify using `only [Formalism.UG.cT, Matrix.map_apply, Matrix.transpose_apply, Matrix.conjTranspose_apply]`. Conclude with `GlobalTheory.Mem.Isom.tauE_sig D τ _`. Rewrite `h0` using `[hm]`. Rewrite using `[h0]`.

Use function extensionality and compare the values at `i`. Conclude with `map_zero _`. Establish `h1 : Formalism.L2.Theta.mt B (atTau θ B τ u) *ₘ d.e.map (incA D) = d.e.map (incA D) + d.e.map (incA D) *ₘ (L.map (incA D) *ₘ (Formalism.L2.Theta.mt B (atTau θ B τ u) - 1) *ₘ d.e.map (incA D))`. Establish `hK : (Formalism.L2.Theta.mt B (atTau θ B τ u) - 1) *ₘ d.e.map (incA D) - d.e.map (incA D) *ₘ (L.map (incA D) *ₘ (Formalism.L2.Theta.mt B (atTau θ B τ u) - 1) *ₘ d.e.map (incA D)) = 0`. Use `mat_eq_zero θ hθ _ ?_ ?_` and prove the remaining obligations.

Rewrite using `[cols_resid_map, hfin]`. Simplify using the standard rewrite rules. Introduce `ρ`. Rewrite using `[cols_resid_map, hinf, hmap, hmap]`. Distinguish the cases in `hρ : ρ = τ`.

Substitute `hρ` using the available equality. Rewrite using `[hgτ]`. Conclude with `cols_resid (map_leftInv (tauE D ρ) hL) fun i => by`. Take `⟨a, -, h⟩` from `hu.2.1 i`. Conclude with `⟨a, h⟩`.

Rewrite using `[hgρ ρ hρ]`. Simplify using the standard rewrite rules. Conclude with `cols_of_resid hK`. Establish `h2 : Formalism.L2.Theta.mt B (atTau θ B τ u) *ᵥ ratV d.z = ratV d.z + d.e.map (incA D) *ᵥ ((L.map (incA D) *ₘ (Formalism.L2.Theta.mt B (atTau θ B τ u) - 1)) *ᵥ ratV d.z)`. Establish `hK : (Formalism.L2.Theta.mt B (atTau θ B τ u) - 1) *ᵥ ratV d.z - d.e.map (incA D) *ᵥ ((L.map (incA D) *ₘ (Formalism.L2.Theta.mt B (atTau θ B τ u) - 1)) *ᵥ ratV d.z) = 0`.

Use `vec_eq_zero θ hθ _ ?_ ?_` and prove the remaining obligations. Use `(vec_resid_map (finPart D) _ _ _ _).trans ?_` and prove the remaining obligations. Rewrite using `[hfin]`. Simplify using `only [sub_self, Matrix.zero_mulVec, Matrix.mul_zero, Matrix.mulVec_zero]`. Introduce `ρ`.

Use `(vec_resid_map ((θ ρ).comp (infPart D)) _ _ _ _).trans ?_` and prove the remaining obligations. Rewrite using `[hinf, hmap, hmap]`. Establish `hz : (fun i => ((θ ρ).comp (infPart D)) (ratV d.z i)) = fun i => tauE D ρ (d.z i)` using `hvec ρ d.z`. Rewrite using `[hz]`. Distinguish the cases in `hρ : ρ = τ`.

Substitute `hρ` using the available equality. Rewrite using `[hgτ]`. Take `⟨b, hb⟩` from `hu.2.2 _ hperp`. Conclude with `vec_resid (map_leftInv (tauE D ρ) hL) hb`. Rewrite using `[hgρ ρ hρ]`.

Simplify using `only [sub_self, Matrix.zero_mulVec, Matrix.mul_zero, Matrix.mulVec_zero]`. Conclude with `vec_of_resid hK`. Use `⟨coordSum (fun i => incA D (d.c i)) (L.map (incA D)) (d.e.map (incA D)) (ratV d.z) (Formalism.L2.Theta.mt B (atTau θ B τ u)), ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← coordSum_map, hfin, coordSum_one]`. Introduce `ρ hρ show ((θ ρ).comp (infPart D)) _ = 0`.

Rewrite using `[← coordSum_map, hinf, hgρ ρ hρ, coordSum_one]`. Use `show ((θ τ).comp (infPart D)) _ = _`. Rewrite using `[← coordSum_map, hinf, hgτ, hmap, hmap, hvec τ d.c]`. Establish `hz : (fun i => ((θ τ).comp (infPart D)) (ratV d.z i)) = fun i => tauE D τ (d.z i)` using `hvec τ d.z`. Rewrite using `[hz]`.

Conclude with `coordSum_flag _ hLτ _ u a ha`. Conclude with `besChar_eq ψ d _ _ _ h1 h2`.
-/
theorem besChar_atTau_coords : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) (d : BesDat A B ι) (τ : D.what₂.Tau) (u : Matrix (Fin B.rank) (Fin B.rank) ℂ),
  u ∈ GlobalTheory.RealBessel.unipRad (gramAt D B τ) (d.e.map (tauE D τ)) →
  ∀ a : Fin d.ρ → Fin d.ρ → ℂ, (∀ j : Fin d.ρ, (u - 1) *ᵥ GlobalTheory.RealBessel.flagVec (d.e.map (tauE D τ)) (fun k => tauE D τ (d.z k)) j.succ = d.e.map (tauE D τ) *ᵥ a j) →
  ∃ t : AE D, finPart D t = 0 ∧ (∀ ρ, ρ ≠ τ → θ ρ (infPart D t) = 0) ∧ θ τ (infPart D t) = ∑ j, tauE D τ (d.c j) * a j j ∧
    besChar ψ d (atTau θ B τ u) = ψ (Algebra.trace (AF D.host.F) (AE D) t) := by
  intro D θ hθ ψ A B ι d τ u hu a ha
  obtain ⟨hgC, hgτ, hgρ⟩ := GlobalTheory.PointAtPlaceHom.atTau_spec hθ B τ hu.1
  obtain ⟨L, hL⟩ := exists_leftInv d.e d.e_iso.1
  have hfin : (Formalism.L2.Theta.mt B (atTau θ B τ u)).map (finPart D) = 1 := GlobalTheory.StripBorel.mt_map_fin hgC
  have hinf : ∀ ρ, (Formalism.L2.Theta.mt B (atTau θ B τ u)).map ((θ ρ).comp (infPart D)) =
      infMat D.sp.cm.sig B.gram (θ ρ) (atTau θ B τ u) := fun ρ => rfl
  have hmap : ∀ ρ {m k : ℕ} (X : Matrix (Fin m) (Fin k) D.host.E),
      (X.map (incA D)).map ((θ ρ).comp (infPart D)) = X.map (tauE D ρ) := by
    intro ρ m k X
    rw [Matrix.map_map, ← RingHom.coe_comp, comp_incA θ hθ ρ]
  have hvec : ∀ ρ {m : ℕ} (x : Fin m → D.host.E),
      (fun i => ((θ ρ).comp (infPart D)) (incA D (x i))) = fun i => tauE D ρ (x i) := by
    intro ρ m x
    funext i
    exact (GlobalTheory.StdUnn.RealComp.real_components D θ hθ).2.2.1 (x i) ρ
  have hL' := map_leftInv (incA D) hL
  have hLτ := map_leftInv (tauE D τ) hL

  have hperp : ((d.e.map (tauE D τ))ᴴ * gramAt D B τ) *ᵥ (fun k => tauE D τ (d.z k)) = 0 := by
    have h0 := mulVec_map (tauE D τ) (perpMat B d.e) d.z
    rw [d.z_perpE] at h0
    have hm : (perpMat B d.e).map (tauE D τ) = (d.e.map (tauE D τ))ᴴ * gramAt D B τ := by
      rw [perpMat, Matrix.map_mul]
      refine congrArg₂ (· * ·) ?_ rfl
      ext i j
      simp only [Formalism.UG.cT, Matrix.map_apply, Matrix.transpose_apply, Matrix.conjTranspose_apply]
      exact GlobalTheory.Mem.Isom.tauE_sig D τ _
    rw [hm] at h0
    rw [h0]
    funext i
    exact map_zero _
  have h1 : Formalism.L2.Theta.mt B (atTau θ B τ u) *ₘ d.e.map (incA D) = d.e.map (incA D) +
      d.e.map (incA D) *ₘ (L.map (incA D) *ₘ (Formalism.L2.Theta.mt B (atTau θ B τ u) - 1) *ₘ d.e.map (incA D)) := by
    have hK : (Formalism.L2.Theta.mt B (atTau θ B τ u) - 1) *ₘ d.e.map (incA D) - d.e.map (incA D) *ₘ
        (L.map (incA D) *ₘ (Formalism.L2.Theta.mt B (atTau θ B τ u) - 1) *ₘ d.e.map (incA D)) = 0 := by
      refine mat_eq_zero θ hθ _ ?_ ?_
      · rw [cols_resid_map, hfin]; simp
      · intro ρ
        rw [cols_resid_map, hinf, hmap, hmap]
        by_cases hρ : ρ = τ
        · subst hρ
          rw [hgτ]
          exact cols_resid (map_leftInv (tauE D ρ) hL) fun i => by
            obtain ⟨a, -, h⟩ := hu.2.1 i
            exact ⟨a, h⟩
        · rw [hgρ ρ hρ]; simp
    exact cols_of_resid hK
  have h2 : Formalism.L2.Theta.mt B (atTau θ B τ u) *ᵥ ratV d.z = ratV d.z +
      d.e.map (incA D) *ᵥ ((L.map (incA D) *ₘ (Formalism.L2.Theta.mt B (atTau θ B τ u) - 1)) *ᵥ ratV d.z) := by
    have hK : (Formalism.L2.Theta.mt B (atTau θ B τ u) - 1) *ᵥ ratV d.z - d.e.map (incA D) *ᵥ
        ((L.map (incA D) *ₘ (Formalism.L2.Theta.mt B (atTau θ B τ u) - 1)) *ᵥ ratV d.z) = 0 := by
      refine vec_eq_zero θ hθ _ ?_ ?_
      · refine (vec_resid_map (finPart D) _ _ _ _).trans ?_
        rw [hfin]
        simp only [sub_self, Matrix.zero_mulVec, Matrix.mul_zero, Matrix.mulVec_zero]
      · intro ρ
        refine (vec_resid_map ((θ ρ).comp (infPart D)) _ _ _ _).trans ?_
        rw [hinf, hmap, hmap]
        have hz : (fun i => ((θ ρ).comp (infPart D)) (ratV d.z i)) = fun i => tauE D ρ (d.z i) := hvec ρ d.z
        rw [hz]
        by_cases hρ : ρ = τ
        · subst hρ
          rw [hgτ]
          obtain ⟨b, hb⟩ := hu.2.2 _ hperp
          exact vec_resid (map_leftInv (tauE D ρ) hL) hb
        · rw [hgρ ρ hρ]
          simp only [sub_self, Matrix.zero_mulVec, Matrix.mul_zero, Matrix.mulVec_zero]
    exact vec_of_resid hK
  refine ⟨coordSum (fun i => incA D (d.c i)) (L.map (incA D)) (d.e.map (incA D)) (ratV d.z)
    (Formalism.L2.Theta.mt B (atTau θ B τ u)), ?_, ?_, ?_, ?_⟩
  · rw [← coordSum_map, hfin, coordSum_one]
  · intro ρ hρ
    show ((θ ρ).comp (infPart D)) _ = 0
    rw [← coordSum_map, hinf, hgρ ρ hρ, coordSum_one]
  · show ((θ τ).comp (infPart D)) _ = _
    rw [← coordSum_map, hinf, hgτ, hmap, hmap, hvec τ d.c]
    have hz : (fun i => ((θ τ).comp (infPart D)) (ratV d.z i)) = fun i => tauE D τ (d.z i) := hvec τ d.z
    rw [hz]
    exact coordSum_flag _ hLτ _ u a ha
  · exact besChar_eq ψ d _ _ _ h1 h2

end GlobalTheory.BesselCoords
