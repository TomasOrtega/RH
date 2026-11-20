import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HostCmEmbeddingProperties
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DenseRangeUnits

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host GlobalTheory.CuspRep Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR GlobalTheory.Mem.Chr
open GlobalTheory.FrobDense

namespace GlobalTheory.CuspRep.NormTriv

section General

variable {L : Type} [Field L] [NumberField L]

abbrev cU (c : L ≃+* L) : Lˣ →* Lˣ := Units.map c.toMonoidHom

/- English proof (translation)
Use `Units.ext (Prod.ext ?_ ?_)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(1 : InfiniteAdeleRing L) - 0 + 0 = 1`. Simplify using the standard rewrite rules. Express the relevant statement in the definitionally equal form `(1 : Af L) - 1 + Neutral.B1.finiteSingle L v x = Neutral.B1.finiteSingle L v x`. Simplify using the standard rewrite rules.
-/
theorem finId_finSingle (v : HeightOneSpectrum (𝓞 L)) (x : (v.adicCompletion L)ˣ) :
    finId L (Units.map (Neutral.B1.finiteSingle L v) x) = localIdele L v x := by
  refine Units.ext (Prod.ext ?_ ?_)
  · change (1 : InfiniteAdeleRing L) - 0 + 0 = 1
    simp
  · change (1 : Af L) - 1 + Neutral.B1.finiteSingle L v x = Neutral.B1.finiteSingle L v x
    simp

/- English proof (translation)
Take `rfl` from `eq_conjSrc h`. Use `Units.ext (Subtype.ext ((map_update_one (conjSrc_injective c) (conjLoc c) v' _).trans ?_))` and prove the remaining obligations. Conclude with `congrArg (Function.update _ v') ((conjLoc_spec c v').2.1 k)`.
-/
theorem conjFin_finSingle (c : L ≃+* L) {v v' : HeightOneSpectrum (𝓞 L)} (h : ConjPl c v v') (k : Lˣ) :
    Units.map (conjFin c).toMonoidHom (Units.map (Neutral.B1.finiteSingle L v) (atFin v k)) =
      Units.map (Neutral.B1.finiteSingle L v') (atFin v' (cU c k)) := by
  classical
  obtain rfl := eq_conjSrc h
  refine Units.ext (Subtype.ext ((map_update_one (conjSrc_injective c) (conjLoc c) v' _).trans ?_))
  exact congrArg (Function.update _ v') ((conjLoc_spec c v').2.1 k)

def normFin (c : L ≃+* L) (χ : HChar L) : Ideles L →* ℂˣ :=
  (χ.1.comp (finId L)).comp ((MonoidHom.id _ * Units.map (conjFin c).toMonoidHom).comp (Units.map (pFin L).toMonoidHom))

/- English proof (translation)
The claim follows from `(χ.2.1.comp (continuous_finId L)).comp ((continuous_id.mul (Continuous.units_map _ (continuous_conjFin c))).comp (Continuous.units_map (pFin L).toMonoidHom continuous_snd))`.
-/
theorem continuous_normFin (c : L ≃+* L) (χ : HChar L) : Continuous (normFin c χ) :=
  (χ.2.1.comp (continuous_finId L)).comp
    ((continuous_id.mul (Continuous.units_map _ (continuous_conjFin c))).comp
      (Continuous.units_map (pFin L).toMonoidHom continuous_snd))

/- English proof (translation)
Express the relevant statement in the definitionally equal form `χ.1 (finId L (Units.map (Neutral.B1.finiteSingle L v) (atFin v k) * Units.map (conjFin c).toMonoidHom (Units.map (Neutral.B1.finiteSingle L v) (atFin v k)))) = _`. Rewrite using `[conjFin_finSingle c h, map_mul, map_mul, finId_finSingle, finId_finSingle]`. Both sides reduce to the same expression.
-/
theorem normFin_loc (c : L ≃+* L) (χ : HChar L) {v v' : HeightOneSpectrum (𝓞 L)} (h : ConjPl c v v') (k : Lˣ) :
    normFin c χ (localIdele L v (atFin v k)) = χ.locK v k * χ.locK v' (cU c k) := by
  change χ.1 (finId L (Units.map (Neutral.B1.finiteSingle L v) (atFin v k) *
    Units.map (conjFin c).toMonoidHom (Units.map (Neutral.B1.finiteSingle L v) (atFin v k)))) = _
  rw [conjFin_finSingle c h, map_mul, map_mul, finId_finSingle, finId_finSingle]
  rfl

/- English proof (translation)
Set `e : ∀ Q : S, Loc S →* Q.1.adicCompletion L` to `fun Q => (Pi.evalMonoidHom (fun Q : S => Q.1.adicCompletion L) Q).comp (MonoidHom.snd _ _)`. Establish `h2 : ∀ y : (Loc S)ˣ, ∏ Q : S, ψ (localIdele L Q.1 (Units.map (e Q) y)) = 1` using `fun y => (denseRange_units S).induction_on (p := fun y => ∏ Q : S, ψ (localIdele L Q.1 (Units.map (e Q) y)) = 1) y (isClosed_eq (continuous_finsetProd _ fun Q _ => hψ.comp ((GlobalTheory.Mem.UnrAe.continuous_localIdele Q.1).comp (Continuous.units_map _ ((continuous_apply Q).comp …`. Establish `h3` using `h2 (Units.map (proj S) (localIdele L v x))`. Rewrite `h3` using `[Finset.prod_eq_single_of_mem ⟨v, hv⟩ (Finset.mem_univ _)]`. Rewrite using `[← h3]`.

Use `congr 2`. Conclude with `Units.ext (Function.update_self v (x : v.adicCompletion L) (fun w : HeightOneSpectrum (𝓞 L) => (1 : w.adicCompletion L))).symm`. Introduce `Q _ hQ`. Establish `: Units.map (e Q) (Units.map (proj S) (localIdele L v x)) = 1` using `Units.ext (Function.update_of_ne (fun h => hQ (Subtype.ext h)) (x : v.adicCompletion L) (fun w : HeightOneSpectrum (𝓞 L) => (1 : w.adicCompletion L)))`. Rewrite using `[this, map_one, map_one]`.
-/
theorem loc_eq_one_of_prod {ψ : Ideles L →* ℂˣ} (hψ : Continuous ψ) (S : Finset (HeightOneSpectrum (𝓞 L)))
    (h : ∀ k : Lˣ, ∏ Q ∈ S, ψ (localIdele L Q (atFin Q k)) = 1) {v : HeightOneSpectrum (𝓞 L)} (hv : v ∈ S)
    (x : (v.adicCompletion L)ˣ) : ψ (localIdele L v x) = 1 := by
  classical
  let e : ∀ Q : S, Loc S →* Q.1.adicCompletion L := fun Q =>
    (Pi.evalMonoidHom (fun Q : S => Q.1.adicCompletion L) Q).comp (MonoidHom.snd _ _)
  have h2 : ∀ y : (Loc S)ˣ, ∏ Q : S, ψ (localIdele L Q.1 (Units.map (e Q) y)) = 1 := fun y =>
    (denseRange_units S).induction_on (p := fun y => ∏ Q : S, ψ (localIdele L Q.1 (Units.map (e Q) y)) = 1) y
      (isClosed_eq (continuous_finsetProd _ fun Q _ => hψ.comp ((GlobalTheory.Mem.UnrAe.continuous_localIdele Q.1).comp
        (Continuous.units_map _ ((continuous_apply Q).comp continuous_snd)))) continuous_const) fun k =>
      (Finset.prod_coe_sort S fun Q => ψ (localIdele L Q (atFin Q k))).trans (h k)
  have h3 := h2 (Units.map (proj S) (localIdele L v x))
  rw [Finset.prod_eq_single_of_mem ⟨v, hv⟩ (Finset.mem_univ _)] at h3
  · rw [← h3]
    congr 2
    exact Units.ext (Function.update_self v (x : v.adicCompletion L)
      (fun w : HeightOneSpectrum (𝓞 L) => (1 : w.adicCompletion L))).symm
  · intro Q _ hQ
    have : Units.map (e Q) (Units.map (proj S) (localIdele L v x)) = 1 :=
      Units.ext (Function.update_of_ne (fun h => hQ (Subtype.ext h)) (x : v.adicCompletion L)
        (fun w : HeightOneSpectrum (𝓞 L) => (1 : w.adicCompletion L)))
    rw [this, map_one, map_one]

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[Units.coe_prod]`. Set `ι : (∀ w : InfinitePlace L, w.Completion) →* AdeleRing (𝓞 L) L` to `MonoidHom.inl (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L)`. Express the relevant statement in the definitionally equal form `_ = ∏ w : InfinitePlace L, ι (Pi.mulSingle w (algebraMap L w.Completion k))`. Rewrite using `[← map_prod, Finset.univ_prod_mulSingle (fun w : InfinitePlace L => algebraMap L w.Completion k)]`.

Use `Prod.ext ?_ ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(1 : InfiniteAdeleRing L) - infEq L 1 + infEq L ((infEq L).symm _) = _`. Rewrite using `[map_one, sub_self, zero_add, RingEquiv.apply_symm_apply]`. Both sides reduce to the same expression. Express the relevant statement in the definitionally equal form `(1 : Af L) - 0 + 0 = 1`.

Simplify using the standard rewrite rules.
-/
theorem infId_pInf [IsTotallyComplex L] (k : Lˣ) :
    infId L (Units.map (pInf L).toMonoidHom (diagUnits L k)) = ∏ w, infIdele L w (atInf w k) := by
  classical
  apply Units.ext
  rw [Units.coe_prod]
  let ι : (∀ w : InfinitePlace L, w.Completion) →* AdeleRing (𝓞 L) L :=
    MonoidHom.inl (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L)
  change _ = ∏ w : InfinitePlace L, ι (Pi.mulSingle w (algebraMap L w.Completion k))
  rw [← map_prod, Finset.univ_prod_mulSingle (fun w : InfinitePlace L => algebraMap L w.Completion k)]
  refine Prod.ext ?_ ?_
  · change (1 : InfiniteAdeleRing L) - infEq L 1 + infEq L ((infEq L).symm _) = _
    rw [map_one, sub_self, zero_add, RingEquiv.apply_symm_apply]
    rfl
  · change (1 : Af L) - 0 + 0 = 1
    simp

end General

variable {L : Type} [Field L] [NumberField L] [IsCMField L]

local notation "𝐅" => maximalRealSubfield L
local notation "𝐜" => AlgEquiv.toRingEquiv (IsCMField.complexConj L)

/- English proof (translation)
Establish `h : (k : L) * IsCMField.complexConj L k ∈ 𝐅` using `(IsCMField.complexConj_eq_self_iff L _).1 (by rw [map_mul, IsCMField.complexConj_apply_apply, mul_comm])`. Conclude with `⟨Units.mk0 ⟨_, h⟩ fun e => (k * cU 𝐜 k).ne_zero (congrArg Subtype.val e), Units.ext rfl⟩`.
-/
theorem exists_norm (k : Lˣ) : ∃ t : (𝐅)ˣ, upF 𝐅 t = k * cU 𝐜 k := by
  have h : (k : L) * IsCMField.complexConj L k ∈ 𝐅 :=
    (IsCMField.complexConj_eq_self_iff L _).1 (by rw [map_mul, IsCMField.complexConj_apply_apply, mul_comm])
  exact ⟨Units.mk0 ⟨_, h⟩ fun e => (k * cU 𝐜 k).ne_zero (congrArg Subtype.val e), Units.ext rfl⟩

/- English proof (translation)
Rewrite using `[← under_eq_iff_conjPl (IsCMField.complexConj L) (Algebra.IsQuadraticExtension.finrank_eq_two _ _) (IsCMField.complexConj_ne_one _)]`. Simplify using `[aboveF]`.
-/
theorem mem_aboveF_iff (v Q : HeightOneSpectrum (𝓞 L)) :
    Q ∈ aboveF (L := L) 𝐅 (v.under (𝓞 𝐅)) ↔ Q = v ∨ ConjPl 𝐜 v Q := by
  rw [← under_eq_iff_conjPl (IsCMField.complexConj L) (Algebra.IsQuadraticExtension.finrank_eq_two _ _)
    (IsCMField.complexConj_ne_one _)]
  simp [aboveF]

/- English proof (translation)
Use `choose σ hσ hu using fun w => existsUnique_conjPl 𝐜 w`. Establish `hσσ : ∀ w, σ (σ w) = w` using `fun w => (hu _ _ fun x => by`. Rewrite using `[← hσ w (𝐜 x)]`. Conclude with `congrArg _ (IsCMField.complexConj_apply_apply L x)).symm`. Establish `hm : ∀ p, ∀ w ∈ aboveF (L` using `L) 𝐅 p, σ w ∈ aboveF (L := L) 𝐅 p := fun p w hw => by`.

Take `rfl : w.under (𝓞 𝐅) = p` from `by simpa [aboveF] using hw`. Conclude with `(mem_aboveF_iff w _).2 (Or.inr (hσ w))`. Establish `h1 : ∀ v x, normFin 𝐜 χ (localIdele L v x) = 1` using `fun v => loc_eq_one_of_prod (continuous_normFin _ χ) (aboveF (L := L) 𝐅 (v.under (𝓞 𝐅))) (fun k => by`. Take `⟨t, ht⟩` from `exists_norm k`. Establish `h2` using `h k t ht (v.under (𝓞 𝐅))`.

Rewrite `h2` using `[HChar.resFin, MonoidHom.finsetProd_apply]`. Simplify using `only [MonoidHom.comp_apply, ht, map_mul, Finset.prod_mul_distrib] at h2`. Rewrite using `[Finset.prod_congr rfl fun Q _ => normFin_loc _ χ (hσ Q) k, Finset.prod_mul_distrib, ← h2]`. Use `congr 1`. Conclude with `Finset.prod_nbij' σ σ (hm _) (hm _) (fun w _ => hσσ w) (fun w _ => hσσ w) fun _ _ => rfl)`.

Use the proof step `((mem_aboveF_iff v v).2 (Or.inl rfl))`. Establish `h3` using `eq_one_of_local _ (continuous_normFin 𝐜 χ) (finId L u) (by`. Express the relevant statement in the definitionally equal form `(1 : InfiniteAdeleRing L) - 0 + 0 = 1`. Use the proof step `simp) fun v => h1 v _`. Establish `e : Units.map (pFin L).toMonoidHom (finId L u) = u` using `Units.ext (by`.

Express the relevant statement in the definitionally equal form `(1 : Af L) - 1 + u = u`. Use the proof step `simp)`. Express the relevant statement in the definitionally equal form `χ.1 (finId L (Units.map (pFin L).toMonoidHom (finId L u) * Units.map (conjFin 𝐜).toMonoidHom (Units.map (pFin L).toMonoidHom (finId L u)))) = 1 at h3`. Rewrite `h3` using `[e]`. Then use the resulting hypothesis.
-/
theorem fin_eq_one (χ : HChar L) (h : ∀ (k : Lˣ) (t : (𝐅)ˣ), upF 𝐅 t = k * cU 𝐜 k → ∀ p, χ.resFin p t = 1)
    (u : (Af L)ˣ) : χ.1 (finId L (u * Units.map (conjFin 𝐜).toMonoidHom u)) = 1 := by
  choose σ hσ hu using fun w => existsUnique_conjPl 𝐜 w
  have hσσ : ∀ w, σ (σ w) = w := fun w => (hu _ _ fun x => by
    rw [← hσ w (𝐜 x)]
    exact congrArg _ (IsCMField.complexConj_apply_apply L x)).symm
  have hm : ∀ p, ∀ w ∈ aboveF (L := L) 𝐅 p, σ w ∈ aboveF (L := L) 𝐅 p := fun p w hw => by
    obtain rfl : w.under (𝓞 𝐅) = p := by simpa [aboveF] using hw
    exact (mem_aboveF_iff w _).2 (Or.inr (hσ w))
  have h1 : ∀ v x, normFin 𝐜 χ (localIdele L v x) = 1 := fun v =>
    loc_eq_one_of_prod (continuous_normFin _ χ) (aboveF (L := L) 𝐅 (v.under (𝓞 𝐅))) (fun k => by
      obtain ⟨t, ht⟩ := exists_norm k
      have h2 := h k t ht (v.under (𝓞 𝐅))
      rw [HChar.resFin, MonoidHom.finsetProd_apply] at h2
      simp only [MonoidHom.comp_apply, ht, map_mul, Finset.prod_mul_distrib] at h2
      rw [Finset.prod_congr rfl fun Q _ => normFin_loc _ χ (hσ Q) k, Finset.prod_mul_distrib, ← h2]
      congr 1
      exact Finset.prod_nbij' σ σ (hm _) (hm _) (fun w _ => hσσ w) (fun w _ => hσσ w) fun _ _ => rfl)
      ((mem_aboveF_iff v v).2 (Or.inl rfl))
  have h3 := eq_one_of_local _ (continuous_normFin 𝐜 χ) (finId L u) (by
    change (1 : InfiniteAdeleRing L) - 0 + 0 = 1
    simp) fun v => h1 v _
  have e : Units.map (pFin L).toMonoidHom (finId L u) = u := Units.ext (by
    change (1 : Af L) - 1 + u = u
    simp)
  change χ.1 (finId L (Units.map (pFin L).toMonoidHom (finId L u) *
    Units.map (conjFin 𝐜).toMonoidHom (Units.map (pFin L).toMonoidHom (finId L u)))) = 1 at h3
  rwa [e] at h3

/- English proof (translation)
Set `q : Loc (∅ : Finset (HeightOneSpectrum (𝓞 L))) →* Cinf L` to `(pInf L).toMonoidHom.comp (incl ∅)`. Establish `hq : Continuous q` using `(continuous_pi fun w => (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp ((continuous_apply w).comp continuous_fst) : Continuous fun y w => q y w)`. Establish `h2 : ∀ y, chiInf χ (Units.map q y * Units.map (starRingEnd (Cinf L)).toMonoidHom (Units.map q y)) = 1` using `fun y => (denseRange_units ∅).induction_on (p := fun y => chiInf χ (Units.map q y * Units.map (starRingEnd (Cinf L)).toMonoidHom (Units.map q y)) = 1) y (isClosed_eq ((continuous_chiInf χ).comp ((hq.units_map _).mul ((Continuous.units_map _ continuous_star).comp (hq.units_map _)) …`. Take `⟨t, ht⟩` from `exists_norm k`. Establish `e : Units.map q (Units.map (proj ∅) (diagUnits L k)) * Units.map (starRingEnd (Cinf L)).toMonoidHom (Units.map q (Units.map (proj ∅) (diagUnits L k))) = Units.map (pInf L).toMonoidHom (diagUnits L (upF 𝐅 t))`.

Rewrite using `[ht, map_mul, map_mul]`. Use `congr 1`. Conclude with `Units.ext (pInf_complexConj (k : L)).symm`. Rewrite using `[e, chiInf, MonoidHom.comp_apply, infId_pInf, map_prod, ← Finset.prod_fiberwise Finset.univ fun w : InfinitePlace L => w.comap (algebraMap 𝐅 L)]`. Use `Finset.prod_eq_one fun w _ => ?_` and prove the remaining obligations.

Establish `h3` using `h k t ht w`. Rewrite `h3` using `[HChar.resInf, MonoidHom.finsetProd_apply]`. Rewrite using `[← h3]`. Conclude with `Finset.prod_congr (by ext; simp [aboveInf]) fun _ _ => rfl`. Establish `h3` using `h2 (Units.map (proj ∅) (infId L u))`.

Establish `e : Units.map q (Units.map (proj ∅) (infId L u)) = u` using `Units.ext (by`. Express the relevant statement in the definitionally equal form `(infEq L).symm (1 - infEq L 1 + infEq L u) = u`. Use the proof step `simp)`. Rewrite `h3` using `[e]`. Then use the resulting hypothesis.
-/
theorem inf_eq_one (χ : HChar L) (h : ∀ (k : Lˣ) (t : (𝐅)ˣ), upF 𝐅 t = k * cU 𝐜 k → ∀ w, χ.resInf w t = 1)
    (u : (Cinf L)ˣ) : chiInf χ (u * Units.map (starRingEnd (Cinf L)).toMonoidHom u) = 1 := by
  classical
  let q : Loc (∅ : Finset (HeightOneSpectrum (𝓞 L))) →* Cinf L := (pInf L).toMonoidHom.comp (incl ∅)
  have hq : Continuous q := (continuous_pi fun w =>
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp
      ((continuous_apply w).comp continuous_fst) : Continuous fun y w => q y w)
  have h2 : ∀ y, chiInf χ (Units.map q y * Units.map (starRingEnd (Cinf L)).toMonoidHom (Units.map q y)) = 1 := fun y =>
    (denseRange_units ∅).induction_on
      (p := fun y => chiInf χ (Units.map q y * Units.map (starRingEnd (Cinf L)).toMonoidHom (Units.map q y)) = 1) y
      (isClosed_eq ((continuous_chiInf χ).comp ((hq.units_map _).mul
        ((Continuous.units_map _ continuous_star).comp (hq.units_map _)))) continuous_const) fun k => by
      obtain ⟨t, ht⟩ := exists_norm k
      have e : Units.map q (Units.map (proj ∅) (diagUnits L k)) *
          Units.map (starRingEnd (Cinf L)).toMonoidHom (Units.map q (Units.map (proj ∅) (diagUnits L k))) =
          Units.map (pInf L).toMonoidHom (diagUnits L (upF 𝐅 t)) := by
        rw [ht, map_mul, map_mul]
        congr 1
        exact Units.ext (pInf_complexConj (k : L)).symm
      rw [e, chiInf, MonoidHom.comp_apply, infId_pInf, map_prod,
        ← Finset.prod_fiberwise Finset.univ fun w : InfinitePlace L => w.comap (algebraMap 𝐅 L)]
      refine Finset.prod_eq_one fun w _ => ?_
      have h3 := h k t ht w
      rw [HChar.resInf, MonoidHom.finsetProd_apply] at h3
      rw [← h3]
      exact Finset.prod_congr (by ext; simp [aboveInf]) fun _ _ => rfl
  have h3 := h2 (Units.map (proj ∅) (infId L u))
  have e : Units.map q (Units.map (proj ∅) (infId L u)) = u := Units.ext (by
    change (infEq L).symm (1 - infEq L 1 + infEq L u) = u
    simp)
  rwa [e] at h3

/- English proof (translation)
Use `(CG.isCsd_ofChar χ).2 ((CG.thetaInv_one_iff χ).2 ⟨fun u => ?_, fun z => ?_⟩)` and prove the remaining obligations. Establish `h1` using `fin_eq_one χ (fun k t e => (h k t e).1) u`. Rewrite `h1` using `[map_mul, map_mul]`. Rewrite using `[map_inv, map_inv]`. Conclude with `(eq_inv_of_mul_eq_one_left h1).symm`.

Establish `h1 : ∀ t : ℝ, Complex.exp (t * dchi χ (z + star z)) = 1` using `fun t => by`. Establish `h2` using `inf_eq_one χ (fun k t e => (h k t e).2) (expU (t • z))`. Establish `e : Units.map (starRingEnd (Cinf L)).toMonoidHom (expU (t • z)) = expU (t • star z)` using `Units.ext (funext fun w => by`. Express the relevant statement in the definitionally equal form `starRingEnd ℂ (Complex.exp (t • z w)) = Complex.exp (t • star (z w))`. Rewrite using `[← Complex.exp_conj]`.

Use the proof step `simp)`. Rewrite `h2` using `[e, ← expU_add, ← smul_add]`. Rewrite using `[← Complex.real_smul, ← map_smul, ← chiInf_expU, h2, Units.val_one]`. Establish `h2 : HasDerivAt (fun t : ℝ => Complex.exp (t * dchi χ (z + star z))) (dchi χ (z + star z)) 0`. Simplify using `using ((Complex.ofRealCLM.hasDerivAt (x := 0)).mul_const (dchi χ (z + star z))).cexp`.

Rewrite `h2` using `[funext h1]`. Establish `h3` using `h2.unique (hasDerivAt_const _ _)`. Rewrite `h3` using `[map_add]`. Rewrite using `[map_neg]`. Conclude with `(eq_neg_of_add_eq_zero_left h3).symm`.
-/
theorem isCsd_of_norm (χ : HChar L)
    (h : ∀ (k : Lˣ) (t : (𝐅)ˣ), upF 𝐅 t = k * cU 𝐜 k → (∀ p, χ.resFin p t = 1) ∧ ∀ w, χ.resInf w t = 1) :
    (CG.ofChar χ).IsCsd := by
  refine (CG.isCsd_ofChar χ).2 ((CG.thetaInv_one_iff χ).2 ⟨fun u => ?_, fun z => ?_⟩)
  · have h1 := fin_eq_one χ (fun k t e => (h k t e).1) u
    rw [map_mul, map_mul] at h1
    rw [map_inv, map_inv]
    exact (eq_inv_of_mul_eq_one_left h1).symm
  · have h1 : ∀ t : ℝ, Complex.exp (t * dchi χ (z + star z)) = 1 := fun t => by
      have h2 := inf_eq_one χ (fun k t e => (h k t e).2) (expU (t • z))
      have e : Units.map (starRingEnd (Cinf L)).toMonoidHom (expU (t • z)) = expU (t • star z) :=
        Units.ext (funext fun w => by
          change starRingEnd ℂ (Complex.exp (t • z w)) = Complex.exp (t • star (z w))
          rw [← Complex.exp_conj]
          simp)
      rw [e, ← expU_add, ← smul_add] at h2
      rw [← Complex.real_smul, ← map_smul, ← chiInf_expU, h2, Units.val_one]
    have h2 : HasDerivAt (fun t : ℝ => Complex.exp (t * dchi χ (z + star z))) (dchi χ (z + star z)) 0 := by
      simpa using ((Complex.ofRealCLM.hasDerivAt (x := 0)).mul_const (dchi χ (z + star z))).cexp
    rw [funext h1] at h2
    have h3 := h2.unique (hasDerivAt_const _ _)
    rw [map_add] at h3
    rw [map_neg]
    exact (eq_neg_of_add_eq_zero_left h3).symm

/- English proof (translation)
Rewrite using `[etaFin]`. Use `split_ifs with hc`. Take `⟨P, hP⟩` from `Finset.card_eq_one.1 hc`. Choose the witnesses or unpack the hypotheses as in `rfl : P.under (𝓞 𝐅) = p := by`. Establish `: P ∈ aboveF (L` using `L) 𝐅 p := hP ▸ Finset.mem_singleton_self P`.

Simplify `this` using `[aboveF]`. Take `⟨Q, hQ, -⟩` from `existsUnique_conjPl 𝐜 P`. Take `rfl : Q = P` from `Finset.mem_singleton.1 (hP ▸ (mem_aboveF_iff P Q).2 (Or.inr hQ))`. Establish `h0 : Q.valuation L (k : L) ≠ 0` using `by simp`. Establish `e : Q.valuation L ((k * cU 𝐜 k : Lˣ) : L) = Q.valuation L (k : L) * Q.valuation L (k : L)`.

Rewrite using `[Units.val_mul, map_mul]`. Conclude with `congrArg _ (hQ k)`. Rewrite using `[← hr, ht, ordF, e, WithZero.log_mul h0 h0]`. Conclude with `Even.neg_one_zpow (Even.add_self _).neg`. Both sides reduce to the same expression.
-/
theorem etaFin_norm (hr : ∀ (P : HeightOneSpectrum (𝓞 L)) (t : (𝐅)ˣ), ordF P (upF 𝐅 t) = ordF (P.under (𝓞 𝐅)) t)
    {k : Lˣ} {t : (𝐅)ˣ} (ht : upF 𝐅 t = k * cU 𝐜 k) (p : HeightOneSpectrum (𝓞 𝐅)) : etaFin (L := L) 𝐅 p t = 1 := by
  rw [etaFin]
  split_ifs with hc
  · obtain ⟨P, hP⟩ := Finset.card_eq_one.1 hc
    obtain rfl : P.under (𝓞 𝐅) = p := by
      have : P ∈ aboveF (L := L) 𝐅 p := hP ▸ Finset.mem_singleton_self P
      simpa [aboveF] using this
    obtain ⟨Q, hQ, -⟩ := existsUnique_conjPl 𝐜 P
    obtain rfl : Q = P := Finset.mem_singleton.1 (hP ▸ (mem_aboveF_iff P Q).2 (Or.inr hQ))
    have h0 : Q.valuation L (k : L) ≠ 0 := by simp
    have e : Q.valuation L ((k * cU 𝐜 k : Lˣ) : L) = Q.valuation L (k : L) * Q.valuation L (k : L) := by
      rw [Units.val_mul, map_mul]
      exact congrArg _ (hQ k)
    rw [← hr, ht, ordF, e, WithZero.log_mul h0 h0]
    exact Even.neg_one_zpow (Even.add_self _).neg
  · rfl

/- English proof (translation)
Rewrite using `[etaInf, if_neg]`. Establish `e : algebraMap 𝐅 L t = k * IsCMField.complexConj L k` using `congrArg Units.val ht`. Rewrite using `[← ComplexEmbedding.lift_algebraMap_apply L w.embedding, e, map_mul, IsCMField.complexEmbedding_complexConj, Complex.mul_conj, Complex.ofReal_re, not_lt]`. Conclude with `Complex.normSq_nonneg _`.
-/
theorem etaInf_norm {k : Lˣ} {t : (𝐅)ˣ} (ht : upF 𝐅 t = k * cU 𝐜 k) (w : InfinitePlace 𝐅) : etaInf 𝐅 w t = 1 := by
  rw [etaInf, if_neg]
  have e : algebraMap 𝐅 L t = k * IsCMField.complexConj L k := congrArg Units.val ht
  rw [← ComplexEmbedding.lift_algebraMap_apply L w.embedding, e, map_mul, IsCMField.complexEmbedding_complexConj,
    Complex.mul_conj, Complex.ofReal_re, not_lt]
  exact Complex.normSq_nonneg _

end GlobalTheory.CuspRep.NormTriv

open GlobalTheory.CuspRep.NormTriv in

/- English proof (translation)
The claim follows from `host_isCMField H; (CG.ofChar χ).IsCsd := by intro R H χ h have := host_isCMField H obtain ⟨-, -, -, hr, -⟩ := GlobalTheory.Mem.HostCM.host_cm R H refine isCsd_of_norm χ fun k t ht => ?_ rcases h with h | h · exact ⟨fun p => h.1 p t, fun w => h.2 w t⟩ · exact ⟨fun p => (h.1 p t).t …`.
-/
theorem GlobalTheory.CuspRep.isCsd_ofChar_of_res : ∀ {R : Formalism.BasicNotions.Ranks} (H : Formalism.BasicNotions.Host R) (χ : HChar H.E),
    (χ.TrivOn H.F ∨ χ.ResEta H.F) → haveI := host_isCMField H; (CG.ofChar χ).IsCsd := by
  intro R H χ h
  have := host_isCMField H
  obtain ⟨-, -, -, hr, -⟩ := GlobalTheory.Mem.HostCM.host_cm R H
  refine isCsd_of_norm χ fun k t ht => ?_
  rcases h with h | h
  · exact ⟨fun p => h.1 p t, fun w => h.2 w t⟩
  · exact ⟨fun p => (h.1 p t).trans (etaFin_norm hr ht p), fun w => (h.2 w t).trans (etaInf_norm ht w)⟩
