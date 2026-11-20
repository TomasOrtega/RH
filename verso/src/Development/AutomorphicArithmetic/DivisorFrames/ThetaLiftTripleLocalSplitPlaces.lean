import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.StageGeoDefs
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AutomorphicArithmetic.DivisorFrames.ExistsIsSBHalfThetaOfSelfDualLattices
import Development.AutomorphicArithmetic.DivisorFrames.IdempotentSumFixesIffHalfEl
import Development.AutomorphicArithmetic.DivisorFrames.StdSectionFirstEqProdLocal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints GlobalTheory.Grid GlobalTheory.ChainFr GlobalTheory.SquareComm GlobalTheory.FinMatch
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Geo piW chrW unifAt latAtV At SInf)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.TripleRead (thO ptO)
open GlobalTheory.AdelicU (evFin splitPrime IsSplitBasis)
open GlobalTheory.BotMatch (evW)
open GlobalTheory.StageGeo
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

/- English proof (translation)
Establish `h1 : (m⁻¹).1 = Wi.submatrix e e`. Establish `: Wi.submatrix e e * m.1 = 1`. Rewrite using `[hm, Matrix.submatrix_mul_equiv, hW]`. Conclude with `Matrix.submatrix_one_equiv e`. Combine the equalities or inequalities in the displayed calculation.

Establish `h2 : (G * B)ᵀ * ((X * Gi)ᵀ).submatrix id e = ((X * B)ᵀ).submatrix id e`. Establish `: (G * B)ᵀ * ((X * Gi)ᵀ).submatrix id e = ((G * B)ᵀ * (X * Gi)ᵀ).submatrix id e` using `rfl`. Rewrite using `[this, ← Matrix.transpose_mul, Matrix.mul_assoc X, ← Matrix.mul_assoc Gi, hG, Matrix.one_mul]`. Rewrite using `[h2, GlobalTheory.SplitFlip.invT_val, h1, Matrix.transpose_submatrix, Matrix.submatrix_mul_equiv, ← Matrix.transpose_mul, Matrix.mul_assoc]`.
-/
private theorem fmFst_mat {k : Type} [Field k] {a n d : ℕ} (e : Fin n ≃ Fin d) (B G Gi : Matrix (Fin a) (Fin a) k) (hG : Gi * G = 1)
    (W Wi : Matrix (Fin d) (Fin d) k) (hW : Wi * W = 1) (m : GL (Fin n) k) (hm : m.1 = W.submatrix e e)
    (X : Matrix (Fin d) (Fin a) k) :
    (G * B)ᵀ * ((X * Gi)ᵀ).submatrix id e * (GlobalTheory.SplitFlip.invT m).1 = ((Wi * X * B)ᵀ).submatrix id e := by
  have h1 : (m⁻¹).1 = Wi.submatrix e e := by
    have : Wi.submatrix e e * m.1 = 1 := by
      rw [hm, Matrix.submatrix_mul_equiv, hW]; exact Matrix.submatrix_one_equiv e
    calc (m⁻¹).1 = (Wi.submatrix e e * m.1) * (m⁻¹).1 := by rw [this, Matrix.one_mul]
      _ = Wi.submatrix e e := by rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  have h2 : (G * B)ᵀ * ((X * Gi)ᵀ).submatrix id e = ((X * B)ᵀ).submatrix id e := by
    have : (G * B)ᵀ * ((X * Gi)ᵀ).submatrix id e = ((G * B)ᵀ * (X * Gi)ᵀ).submatrix id e := rfl
    rw [this, ← Matrix.transpose_mul, Matrix.mul_assoc X, ← Matrix.mul_assoc Gi, hG, Matrix.one_mul]
  rw [h2, GlobalTheory.SplitFlip.invT_val, h1, Matrix.transpose_submatrix, Matrix.submatrix_mul_equiv, ← Matrix.transpose_mul,
    Matrix.mul_assoc]

/- English proof (translation)
Use `⟨h.1, fun y => (h.2 y).trans (forall₂_congr fun x _ => ?_)⟩` and prove the remaining obligations. Establish `e : ∑ i, ∑ j, star (x i) * (sgn true V).gram i j * y j = -∑ i, ∑ j, star (x i) * V.gram i j * y j`. Rewrite using `[← Finset.sum_neg_distrib]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.sum_neg_distrib]`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Use `show star (x i) * (-V.gram i j) * y j = _`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `⟨fun ⟨b, hb⟩ => ⟨-b, by simp [hb]⟩, fun ⟨b, hb⟩ => ⟨-b, by simp [hb]⟩⟩`.
-/
private theorem selfDual_neg {D : D7} {V : HSp D} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    (h : IsSelfDualC V Λ) : IsSelfDualC (sgn true V) Λ := by
  refine ⟨h.1, fun y => (h.2 y).trans (forall₂_congr fun x _ => ?_)⟩
  have e : ∑ i, ∑ j, star (x i) * (sgn true V).gram i j * y j = -∑ i, ∑ j, star (x i) * V.gram i j * y j := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    show star (x i) * (-V.gram i j) * y j = _
    ring
  rw [e]
  exact ⟨fun ⟨b, hb⟩ => ⟨-b, by simp [hb]⟩, fun ⟨b, hb⟩ => ⟨-b, by simp [hb]⟩⟩

/- English proof (translation)
Introduce `D T A A' WW X ψ θ α β νH S hX hr Bs Vs Ws M hP hL t P τ hS b c ι hb hc hι hι0 φ hφ hφ' hφA g hvac`. Establish `hPS : ∀ v, v ∈ P ↔ ∃ w ∈ S t, w.under (𝓞 D.host.F) = v` using `fun v => by`. Prove the components needed by the constructor for the conclusion. Introduce `hv`. Conclude with `⟨splitPrime (τ ⟨v, hv⟩), (hS _).2 ⟨_, rfl⟩, GlobalTheory.AdelicU.splitPrime_under (τ ⟨v, hv⟩)⟩`.

Introduce and unpack `⟨w, hw, rfl⟩`. Take `⟨u, rfl⟩` from `(hS w).1 hw`. Rewrite using `[GlobalTheory.AdelicU.splitPrime_under (τ u)]`. Conclude with `u.2`. Establish `hτS : ∀ v : P, splitPrime (τ v) ∈ S t` using `fun v => (hS _).2 ⟨v, rfl⟩`.

Establish `hinj : Function.Injective fun v : P => splitPrime (τ v)` using `fun u v h => by`. Establish `h1` using `GlobalTheory.AdelicU.splitPrime_under (τ u)`. Establish `h2` using `GlobalTheory.AdelicU.splitPrime_under (τ v)`. Establish `h' : splitPrime (τ u) = splitPrime (τ v)` using `h`. Conclude with `Subtype.ext (h1.symm.trans (h' ▸ h2))`.

Take `⟨hh0, hh1⟩` from `UpperTheory.idempotentSum_fixes_iff_halfEl D (X.e t) (S t) (hX.idem t) P τ hPS hτS`. Take `⟨G, hG⟩ : ∃ G : Matrix (Fin A.rank) (Fin A.rank) D.host.E, G = (sgn true A).gram` from `⟨_, rfl⟩`. Establish `hdet : IsUnit G.det` using `by rw [hG]; exact (Formalism.L2.Theta.gram_det_ne (sgn true A)).isUnit`. Establish `hGi : ∀ v : P, (G⁻¹.map (incA D)).map (piW (τ v)) * (G.map (incA D)).map (piW (τ v)) = 1` using `fun v => by`. Rewrite using `[← Matrix.map_mul, ← Matrix.map_mul, Matrix.nonsing_inv_mul _ hdet, Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_one _ (map_zero _) (map_one _)]`.

Establish `hbG : ∀ v : P, ((b v)⁻¹).1 = ((G.map (incA D)).map (piW (τ v)) * X.rA.β.1.map (evW (τ v)))ᵀ` using `fun v => by`. Establish `e0 : (G.map (incA D)).map (piW (τ v)) = -A.gram.map (τ v)`. Use `Matrix.ext fun i j => ?_` and prove the remaining obligations. Establish `e1 : G i j = -A.gram i j` using `by rw [hG]; rfl`. Establish `e2 : ∀ y, piW (τ v) (incA D y) = τ v y` using `fun y => one_mul (τ v y)`.

Use `show piW (τ v) (incA D (G i j)) = -(τ v (A.gram i j))`. Rewrite using `[e2, e1, map_neg]`. Rewrite using `[hb, e0, Matrix.neg_mul, Matrix.transpose_neg]`. Establish `key : ∀ (x : WO A WW) (v : P), ((b v)⁻¹).1 * (ptO (sgn true A).gram (finCongr hr) x).map (piW (τ v)) * (GlobalTheory.SplitFlip.invT (c v)).1 = (((frMapO A WW X.rA.β X.rW.β x).map (evW (τ v)))ᵀ).submatrix id (finCongr hr)` using `fun x v => by`. Establish `e1 : (ptO G (finCongr hr) x).map (piW (τ v)) = ((Matrix.map x (piW (τ v)) * (G⁻¹.map (incA D)).map (piW (τ v)))ᵀ).submatrix id (finCongr hr)`.

Rewrite using `[← Matrix.map_mul]`. Both sides reduce to the same expression. Establish `e2 : (frMapO A WW X.rA.β X.rW.β x).map (evW (τ v)) = (X.rW.β⁻¹).1.map (evW (τ v)) * Matrix.map x (piW (τ v)) * X.rA.β.1.map (evW (τ v))`. Unfold `frMapO`. Rewrite using `[Matrix.map_mul, Matrix.map_mul]`.

Use `congr 2`. Use `Matrix.ext fun i j => ?_` and prove the remaining obligations. Conclude with `GlobalTheory.BotMatch.evW_toEAf (τ v) (x i j)`. Rewrite using `[← hG, hbG, e1, e2]`. Use `fmFst_mat (finCongr hr) _ _ _ (hGi v) (X.rW.β.1.map (evW (τ v))) _ ?_ (c v) (hc v) _` and prove the remaining obligations.

Rewrite using `[← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]`. Establish `hth` using `hX.fst t`. Rewrite `hth` using `[hvac]`. Use `UpperTheory.exists_isSBHalf_theta_of_selfDual_lattices D ψ true A WW _ (finCongr hr) Bs Vs Ws M hP X.rA.Λ X.rW.Λ hL (selfDual_neg hX.rigA.1) hX.rigW.1 P τ (fun v => (τ v).comp D.sp.cm.sig) (fun _ _ => rfl) (X.e t) hh0 hh1 (fun v => (b v)⁻¹) (fun v => GlobalTheory.SplitFlip.invT ( …` and prove the remaining obligations. Distinguish the cases in `hx : IsHalf (X.e t) x`.

Rewrite using `[if_pos hx]`. Use `(UpperTheory.stdSectionFirst_eq_prod_local D (X.e t) (S t) (hX.idem t) P (fun v => v.1) τ hS hinj (X.c t) (α t / β t) A WW X.rA.β X.rW.β A'.rank hr x hx).trans (Finset.prod_congr rfl fun v _ => ?_)` and prove the remaining obligations. Rewrite using `[hφA v]`. Conclude with `congrArg _ (key x v).symm`. Rewrite using `[if_neg hx]`.

Conclude with `if_neg fun h => hx h.1`.
-/
theorem UpperTheory.thetaLift_triple_local_split_places :
    ∀ (D : D7) (T : Type) (A A' WW : HSp D) (X : Tri T A A' WW) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D)
        (α β : T → ((AE D)ˣ →* Circle)) (νH : T → Formalism.L2.Host.HChar D.host.E) (S : T → Finset (HeightOneSpectrum (𝓞 D.host.E))),
        X.Is ψ θ α β νH S → ∀ (hr : A.rank + A'.rank = WW.rank) (Bs : Base D.host.F D.host.E)
        (Vs : Spc D.host.F D.host.E A.rank) (Ws : Spc D.host.F D.host.E (A.rank + A'.rank)) (M : Model D.sp.cm.sig Vs Ws),
        IsPair ψ true A WW (finCongr hr) Bs Vs Ws M → IsLat (finCongr hr) Vs Ws X.rA.Λ X.rW.Λ →
        ∀ (t : T) (P : Finset (HeightOneSpectrum (𝓞 D.host.F))) (τ : ∀ v : P, D.host.E →ₐ[D.host.F] Fv D.host.F v),
        (∀ w, w ∈ S t ↔ ∃ v : P, splitPrime (τ v) = w) →
        ∀ (b : ∀ v : P, GL (Fin A.rank) (Fv D.host.F v)) (c : ∀ v : P, GL (Fin (A.rank + A'.rank)) (Fv D.host.F v))
          (ι : ∀ v : P, ((Fin A.rank × Fin (A.rank + A'.rank) → Fv D.host.F v) → ℂ) →ₗ[ℂ]
            (Matrix (Fin A.rank) (Fin (A.rank + A'.rank)) (Fv D.host.F v) → ℂ)),
        (∀ v, ((b v)⁻¹).1 = -(A.gram.map (τ v) * X.rA.β.1.map (evW (τ v)))ᵀ) →
        (∀ v, (c v).1 = (X.rW.β.1.map (evW (τ v))).submatrix (finCongr hr) (finCongr hr)) →
        (∀ v, M.IsLinW ψ (τ v) (b v) (c v) (ι v)) → (∀ v : P, ι v (M.vac v) 0 = 1) →
        ∀ (φ : ∀ v : HeightOneSpectrum (𝓞 D.host.F), (Fin A.rank × Fin (A.rank + A'.rank) → Fv D.host.F v) → ℂ),
        (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) → (∀ v, v ∉ P → φ v = M.vac v) →
        (∀ v : P, ι v (φ v) = GlobalTheory.StdPairCone.stdA (chrW (α t / β t) (τ v)) (unifAt v.1) (X.c t (splitPrime (τ v))) A.rank A'.rank) →
        ∀ g : SInf D.host.F (Fin A.rank × Fin (A.rank + A'.rank)),
        X.vac = thO M ψ (sgn true A).gram (finCongr hr) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g M.vac) →
        X.f t = thO M ψ (sgn true A).gram (finCongr hr) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ) := by
  intro D T A A' WW X ψ θ α β νH S hX hr Bs Vs Ws M hP hL t P τ hS b c ι hb hc hι hι0 φ hφ hφ' hφA g hvac
  have hPS : ∀ v, v ∈ P ↔ ∃ w ∈ S t, w.under (𝓞 D.host.F) = v := fun v => by
    constructor
    · intro hv
      exact ⟨splitPrime (τ ⟨v, hv⟩), (hS _).2 ⟨_, rfl⟩, GlobalTheory.AdelicU.splitPrime_under (τ ⟨v, hv⟩)⟩
    · rintro ⟨w, hw, rfl⟩
      obtain ⟨u, rfl⟩ := (hS w).1 hw
      rw [GlobalTheory.AdelicU.splitPrime_under (τ u)]
      exact u.2
  have hτS : ∀ v : P, splitPrime (τ v) ∈ S t := fun v => (hS _).2 ⟨v, rfl⟩
  have hinj : Function.Injective fun v : P => splitPrime (τ v) := fun u v h => by
    have h1 := GlobalTheory.AdelicU.splitPrime_under (τ u)
    have h2 := GlobalTheory.AdelicU.splitPrime_under (τ v)
    have h' : splitPrime (τ u) = splitPrime (τ v) := h
    exact Subtype.ext (h1.symm.trans (h' ▸ h2))
  obtain ⟨hh0, hh1⟩ := UpperTheory.idempotentSum_fixes_iff_halfEl D (X.e t) (S t) (hX.idem t) P τ hPS hτS
  obtain ⟨G, hG⟩ : ∃ G : Matrix (Fin A.rank) (Fin A.rank) D.host.E, G = (sgn true A).gram := ⟨_, rfl⟩
  have hdet : IsUnit G.det := by rw [hG]; exact (Formalism.L2.Theta.gram_det_ne (sgn true A)).isUnit
  have hGi : ∀ v : P, (G⁻¹.map (incA D)).map (piW (τ v)) * (G.map (incA D)).map (piW (τ v)) = 1 := fun v => by
    rw [← Matrix.map_mul, ← Matrix.map_mul, Matrix.nonsing_inv_mul _ hdet, Matrix.map_one _ (map_zero _) (map_one _),
      Matrix.map_one _ (map_zero _) (map_one _)]
  have hbG : ∀ v : P, ((b v)⁻¹).1 = ((G.map (incA D)).map (piW (τ v)) * X.rA.β.1.map (evW (τ v)))ᵀ := fun v => by
    have e0 : (G.map (incA D)).map (piW (τ v)) = -A.gram.map (τ v) := by
      refine Matrix.ext fun i j => ?_
      have e1 : G i j = -A.gram i j := by rw [hG]; rfl
      have e2 : ∀ y, piW (τ v) (incA D y) = τ v y := fun y => one_mul (τ v y)
      show piW (τ v) (incA D (G i j)) = -(τ v (A.gram i j))
      rw [e2, e1, map_neg]
    rw [hb, e0, Matrix.neg_mul, Matrix.transpose_neg]
  have key : ∀ (x : WO A WW) (v : P),
      ((b v)⁻¹).1 * (ptO (sgn true A).gram (finCongr hr) x).map (piW (τ v)) * (GlobalTheory.SplitFlip.invT (c v)).1 =
      (((frMapO A WW X.rA.β X.rW.β x).map (evW (τ v)))ᵀ).submatrix id (finCongr hr) := fun x v => by
    have e1 : (ptO G (finCongr hr) x).map (piW (τ v)) =
        ((Matrix.map x (piW (τ v)) * (G⁻¹.map (incA D)).map (piW (τ v)))ᵀ).submatrix id (finCongr hr) := by
      rw [← Matrix.map_mul]; rfl
    have e2 : (frMapO A WW X.rA.β X.rW.β x).map (evW (τ v)) =
        (X.rW.β⁻¹).1.map (evW (τ v)) * Matrix.map x (piW (τ v)) * X.rA.β.1.map (evW (τ v)) := by
      unfold frMapO
      rw [Matrix.map_mul, Matrix.map_mul]
      congr 2
      refine Matrix.ext fun i j => ?_
      exact GlobalTheory.BotMatch.evW_toEAf (τ v) (x i j)
    rw [← hG, hbG, e1, e2]
    refine fmFst_mat (finCongr hr) _ _ _ (hGi v) (X.rW.β.1.map (evW (τ v))) _ ?_ (c v) (hc v) _
    rw [← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
  have hth := hX.fst t
  rw [hvac] at hth
  refine UpperTheory.exists_isSBHalf_theta_of_selfDual_lattices D ψ true A WW _ (finCongr hr) Bs Vs Ws M hP X.rA.Λ X.rW.Λ hL (selfDual_neg hX.rigA.1) hX.rigW.1
    P τ (fun v => (τ v).comp D.sp.cm.sig) (fun _ _ => rfl) (X.e t) hh0 hh1 (fun v => (b v)⁻¹)
    (fun v => GlobalTheory.SplitFlip.invT (c v)) ι (fun v => hι v) hι0 φ hφ hφ' g
    (GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst (α t / β t) (X.e t) (X.ideal S t) A WW X.rA.β X.rW.β) (X.f t) (fun x => ?_) hth
  by_cases hx : IsHalf (X.e t) x
  · rw [if_pos hx]
    refine (UpperTheory.stdSectionFirst_eq_prod_local D (X.e t) (S t) (hX.idem t) P (fun v => v.1) τ hS hinj (X.c t) (α t / β t) A WW X.rA.β X.rW.β
      A'.rank hr x hx).trans (Finset.prod_congr rfl fun v _ => ?_)
    rw [hφA v]
    exact congrArg _ (key x v).symm
  · rw [if_neg hx]
    exact if_neg fun h => hx h.1
