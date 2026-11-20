import Mathlib
import GroundTheory.AutomorphicForms.AdelicGLn
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicGLIwasawaDecompositionStandardParabolic
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OneMemGoodCT
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUnipLevIntegral

set_option maxSynthPendingDepth 1

noncomputable section

open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl GlobalTheory.CompanionTheory.CTFin Matrix

namespace GlobalTheory.CompanionTheory.CTFin.IwaAd

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `i j`. Express the relevant statement in the definitionally equal form `f ((1 + nilM x : Matrix (Fin a) (Fin a) R) i j) = (1 + nilM (fun p => f (x p)) : Matrix (Fin a) (Fin a) S) i j`. Simplify using `only [nilM, Matrix.add_apply, Matrix.of_apply, Matrix.one_apply, map_add]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem map_unip {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {a r : ℕ} (x : BlockIx a r → R) :
    GeneralLinearGroup.map f (unip x) = unip (fun p => f (x p)) := by
  apply Units.ext
  ext i j
  change f ((1 + nilM x : Matrix (Fin a) (Fin a) R) i j) =
    (1 + nilM (fun p => f (x p)) : Matrix (Fin a) (Fin a) S) i j
  simp only [nilM, Matrix.add_apply, Matrix.of_apply, Matrix.one_apply, map_add]
  split_ifs <;> simp

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `i j`. Express the relevant statement in the definitionally equal form `f (((lev R r s m : GL (Fin (r + s)) R) : Matrix _ _ R) i j) = ((lev S r s _ : GL (Fin (r + s)) S) : Matrix _ _ S) i j`. Rewrite using `[lev, lev, GlobalTheory.SmGL.val_emb₂, GlobalTheory.SmGL.val_emb₂]`. Take `⟨i, rfl⟩` from `(GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).surjective i`.

Take `⟨j, rfl⟩` from `(GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).surjective j`. Apply the tactic sequence `rcases i with i | i <;> rcases j with j | j <;> simp`.
-/
theorem map_lev {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (r s : ℕ)
    (m : GL (Fin r) R × GL (Fin s) R) :
    GeneralLinearGroup.map f (lev R r s m) =
      lev S r s (GeneralLinearGroup.map f m.1, GeneralLinearGroup.map f m.2) := by
  apply Units.ext
  ext i j
  change f (((lev R r s m : GL (Fin (r + s)) R) : Matrix _ _ R) i j) = ((lev S r s _ : GL (Fin (r + s)) S) : Matrix _ _ S) i j
  rw [lev, lev, GlobalTheory.SmGL.val_emb₂, GlobalTheory.SmGL.val_emb₂]
  obtain ⟨i, rfl⟩ := (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).surjective i
  obtain ⟨j, rfl⟩ := (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).surjective j
  rcases i with i | i <;> rcases j with j | j <;> simp

/- English proof (translation)
Take `⟨T, hT⟩` from `(GroundTheory.Automorphic.AdelicGLn.isCompact_integralFiniteGL E n).elim_finite_subcover (fun t : GL (Fin n) (Af E) => (fun z => t⁻¹ * z) ⁻¹' (L : Set (GL (Fin n) (Af E)))) (fun t => hL.preimage (continuous_const.mul continuous_id)) (fun c _ => Set.mem_iUnion.2 ⟨c, by simp [L.one …`. Use `⟨T, fun c hc => ?_⟩` and prove the remaining obligations. Take `⟨t, ht, hl⟩` from `Set.mem_iUnion₂.1 (hT hc)`. Conclude with `⟨t, ht, t⁻¹ * c, hl, by group⟩`.
-/
theorem exists_finset_cover (E : Type) [Field E] [NumberField E] (n : ℕ) (L : Subgroup (GL (Fin n) (Af E)))
    (hL : IsOpen (L : Set (GL (Fin n) (Af E)))) :
    ∃ T : Finset (GL (Fin n) (Af E)), ∀ c ∈ GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E n,
      ∃ t ∈ T, ∃ l ∈ L, c = t * l := by
  obtain ⟨T, hT⟩ := (GroundTheory.Automorphic.AdelicGLn.isCompact_integralFiniteGL E n).elim_finite_subcover
    (fun t : GL (Fin n) (Af E) => (fun z => t⁻¹ * z) ⁻¹' (L : Set (GL (Fin n) (Af E))))
    (fun t => hL.preimage (continuous_const.mul continuous_id))
    (fun c _ => Set.mem_iUnion.2 ⟨c, by simp [L.one_mem]⟩)
  refine ⟨T, fun c hc => ?_⟩
  obtain ⟨t, ht, hl⟩ := Set.mem_iUnion₂.1 (hT hc)
  exact ⟨t, ht, t⁻¹ * c, hl, by group⟩

/- English proof (translation)
Introduce `E _ _ _ r s L hL`. Take `⟨T, hT⟩` from `exists_finset_cover E (r + s) L hL`. Use `⟨T, fun g => ?_⟩` and prove the remaining obligations. Take `⟨b, hb, k, hy⟩` from `GlobalTheory.IwasawaAdelic.exists_upper_mul_unitary_inf E (r + s) (GeneralLinearGroup.map (pInf E) g)`. Establish `hb' : (((b⁻¹ : GL (Fin (r + s)) (Cinf E))) : Matrix (Fin (r + s)) (Fin (r + s)) (Cinf E)).BlockTriangular id`.

Use `letI : Invertible (b : Matrix (Fin (r + s)) (Fin (r + s)) (Cinf E)) := Units.invertible b`. Rewrite using `[Matrix.coe_units_inv]`. Conclude with `Matrix.blockTriangular_inv_of_blockTriangular hb`. Take `⟨xi, mi, hbi⟩` from `IwaFin.exists_unip_mul_lev r s b (fun i j hi hj => hb (show j < i from Fin.lt_def.2 (lt_of_lt_of_le hj hi))) (fun i j hi hj => hb' (show j < i from Fin.lt_def.2 (lt_of_lt_of_le hj hi)))`. Take `⟨xf, mf, c, hc, hf⟩` from `IwaFin.exists_unip_lev_integral E r s (GeneralLinearGroup.map (pFin E) g)`.

Take `⟨t, ht, l, hl, rfl⟩` from `hT c hc`. Establish `e1 : ∀ p, pInf E (sInf E (xi p) + sFin E (xf p)) = xi p` using `fun p => by`. Rewrite using `[map_add, show pInf E (sInf E (xi p)) = xi p from (infEq E).symm_apply_apply _, show pInf E (sFin E (xf p)) = 0 from map_zero (infEq E).symm, add_zero]`. Establish `e2 : ∀ p, pFin E (sInf E (xi p) + sFin E (xf p)) = xf p` using `fun p => by`. Rewrite using `[map_add, show pFin E (sInf E (xi p)) = 0 from rfl, show pFin E (sFin E (xf p)) = xf p from rfl, zero_add]`.

Use `⟨fun p => sInf E (xi p) + sFin E (xf p), (infGL E r mi.1 * finGL E r mf.1, infGL E s mi.2 * finGL E s mf.2), t, k, l, ht, hl, ga_ext ?_ ?_⟩` and prove the remaining obligations. Simplify using `only [map_mul, map_unip, map_lev, e1, pInf_infGL, pInf_finGL, mul_one, one_mul]`. Rewrite using `[hy, hbi]`. Simplify using `only [map_mul, map_unip, map_lev, e2, pFin_infGL, pFin_finGL, mul_one, one_mul]`. Rewrite using `[hf, mul_assoc, mul_assoc, mul_assoc]`.
-/
theorem iwasawa_finite_cosets : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (r s : ℕ) (L : Subgroup (GL (Fin (r + s)) (Af E))), IsOpen (L : Set (GL (Fin (r + s)) (Af E))) → ∃ T : Finset (GL (Fin (r + s)) (Af E)), ∀ g : GA E (r + s), ∃ (x : BlockIx (r + s) r → Ad E) (m : GA E r × GA E s) (t : GL (Fin (r + s)) (Af E)) (k : Kinf E (r + s)) (l : GL (Fin (r + s)) (Af E)), t ∈ T ∧ l ∈ L ∧ g = unip x * lev (Ad E) r s m * finGL E (r + s) t * infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) l := by
  intro E _ _ _ r s L hL
  obtain ⟨T, hT⟩ := exists_finset_cover E (r + s) L hL
  refine ⟨T, fun g => ?_⟩
  obtain ⟨b, hb, k, hy⟩ := GlobalTheory.IwasawaAdelic.exists_upper_mul_unitary_inf E (r + s)
    (GeneralLinearGroup.map (pInf E) g)
  have hb' : (((b⁻¹ : GL (Fin (r + s)) (Cinf E))) : Matrix (Fin (r + s)) (Fin (r + s)) (Cinf E)).BlockTriangular id := by
    letI : Invertible (b : Matrix (Fin (r + s)) (Fin (r + s)) (Cinf E)) := Units.invertible b
    rw [Matrix.coe_units_inv]
    exact Matrix.blockTriangular_inv_of_blockTriangular hb
  obtain ⟨xi, mi, hbi⟩ := IwaFin.exists_unip_mul_lev r s b
    (fun i j hi hj => hb (show j < i from Fin.lt_def.2 (lt_of_lt_of_le hj hi)))
    (fun i j hi hj => hb' (show j < i from Fin.lt_def.2 (lt_of_lt_of_le hj hi)))
  obtain ⟨xf, mf, c, hc, hf⟩ := IwaFin.exists_unip_lev_integral E r s (GeneralLinearGroup.map (pFin E) g)
  obtain ⟨t, ht, l, hl, rfl⟩ := hT c hc
  have e1 : ∀ p, pInf E (sInf E (xi p) + sFin E (xf p)) = xi p := fun p => by
    rw [map_add, show pInf E (sInf E (xi p)) = xi p from (infEq E).symm_apply_apply _,
      show pInf E (sFin E (xf p)) = 0 from map_zero (infEq E).symm, add_zero]
  have e2 : ∀ p, pFin E (sInf E (xi p) + sFin E (xf p)) = xf p := fun p => by
    rw [map_add, show pFin E (sInf E (xi p)) = 0 from rfl, show pFin E (sFin E (xf p)) = xf p from rfl, zero_add]
  refine ⟨fun p => sInf E (xi p) + sFin E (xf p),
    (infGL E r mi.1 * finGL E r mf.1, infGL E s mi.2 * finGL E s mf.2), t, k, l, ht, hl, ga_ext ?_ ?_⟩
  · simp only [map_mul, map_unip, map_lev, e1, pInf_infGL, pInf_finGL, mul_one, one_mul]
    rw [hy, hbi]
  · simp only [map_mul, map_unip, map_lev, e2, pFin_infGL, pFin_finGL, mul_one, one_mul]
    rw [hf, mul_assoc, mul_assoc, mul_assoc]

end GlobalTheory.CompanionTheory.CTFin.IwaAd
