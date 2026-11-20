import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RingEquivPlaceCorrespondencePlaceUnder

noncomputable section

open NumberField IsDedekindDomain Topology Matrix
open GlobalTheory.CuspRep
open scoped ContDiff

namespace GlobalTheory.IsoPull

section Ring

variable {R S R' S' : Type} [CommRing R] [CommRing S] [CommRing R'] [CommRing S'] {a : ℕ}

/- English proof (translation)
Use extensionality with `i j`. Conclude with `h _`.
-/
theorem map_map_comm (p : R →+* S) (p' : R' →+* S') (c : R →+* R') (c' : S →+* S') (h : ∀ x, p' (c x) = c' (p x))
    (g : GL (Fin a) R) :
    GeneralLinearGroup.map p' (GeneralLinearGroup.map c g) =
      GeneralLinearGroup.map c' (GeneralLinearGroup.map p g) := by
  ext i j
  exact h _

/- English proof (translation)
The claim follows from `Continuous.units_map _ (continuous_matrix fun i j => h.comp (continuous_id.matrix_elem i j))`.
-/
theorem continuous_mapGL [TopologicalSpace R] [IsTopologicalRing R] [TopologicalSpace S] [IsTopologicalRing S]
    (c : R →+* S) (h : Continuous c) : Continuous (GeneralLinearGroup.map (n := Fin a) c) :=
  Continuous.units_map _ (continuous_matrix fun i j => h.comp (continuous_id.matrix_elem i j))

/- English proof (translation)
Use extensionality with `i j`. Express the relevant statement in the definitionally equal form `c ((1 + nilM x : Matrix (Fin a) (Fin a) R) i j) = (1 + nilM fun p => c (x p) : Matrix (Fin a) (Fin a) S) i j`. Simplify using `only [nilM, Matrix.add_apply, Matrix.of_apply, Matrix.one_apply, map_add]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem map_unip {r : ℕ} (c : R →+* S) (x : BlockIx a r → R) :
    GeneralLinearGroup.map c (unip x) = unip fun p => c (x p) := by
  ext i j
  change c ((1 + nilM x : Matrix (Fin a) (Fin a) R) i j) =
    (1 + nilM fun p => c (x p) : Matrix (Fin a) (Fin a) S) i j
  simp only [nilM, Matrix.add_apply, Matrix.of_apply, Matrix.one_apply, map_add]
  split_ifs <;> simp

end Ring

section Sat

open Formalism.UG GlobalTheory.LFun GlobalTheory.PRep

/- English proof (translation)
Use `set G : GL (Fin n) F ≃* GL (Fin n) F' := Units.mapEquiv c.mapMatrix.toMulEquiv with hG`. Establish `hGv : ∀ g i j, (G g).1 i j = c (g.1 i j)` using `fun _ _ _ => rfl`. Establish `e : G (ConjPlace.dGL n ϖ j) = ConjPlace.dGL n (Units.map (c : F →* F') ϖ) j` using `Units.ext (Matrix.ext fun a b => by`. Rewrite using `[hGv]`. Simplify using `only [ConjPlace.dGL, diagJ, Matrix.diagonal_apply]`.

Apply the tactic sequence `split_ifs <;> simp)`. Use `(ConjPlace.Tj_apply O' (Units.map (c : F →* F') ϖ) j _).trans ?_` and prove the remaining obligations. Rewrite using `[ConjPlace.Tj_apply, ← e]`. Use `if_congr ⟨?_, ?_⟩ rfl rfl` and prove the remaining obligations. Introduce and unpack `⟨a, ha, b, hb, H⟩`.

Take `⟨a, rfl⟩` from `G.surjective a`. Take `⟨b, rfl⟩` from `G.surjective b`. Rewrite `H` using `[← map_mul, ← map_mul, G.apply_eq_iff_eq]`. Conclude with `⟨a, (hK a).2 ha, b, (hK b).2 hb, H⟩`. Introduce and unpack `⟨a, ha, b, hb, H⟩`.

Conclude with `⟨_, (hK a).1 ha, _, (hK b).1 hb, by rw [H, map_mul, map_mul]⟩`.
-/
theorem Tj_map {F F' : Type} [Field F] [Field F'] {n : ℕ} (c : F ≃+* F') {O : Subring F} {O' : Subring F'}
    (hK : ∀ g, g ∈ GLint (Fin n) O ↔ Units.mapEquiv c.mapMatrix.toMulEquiv g ∈ GLint (Fin n) O') (ϖ : Fˣ) (j : ℕ)
    (g : GL (Fin n) F) : Tj ℂ n O' (c ϖ) j (Units.mapEquiv c.mapMatrix.toMulEquiv g) = Tj ℂ n O ϖ j g := by
  classical
  set G : GL (Fin n) F ≃* GL (Fin n) F' := Units.mapEquiv c.mapMatrix.toMulEquiv with hG
  have hGv : ∀ g i j, (G g).1 i j = c (g.1 i j) := fun _ _ _ => rfl
  have e : G (ConjPlace.dGL n ϖ j) = ConjPlace.dGL n (Units.map (c : F →* F') ϖ) j :=
    Units.ext (Matrix.ext fun a b => by
      rw [hGv]
      simp only [ConjPlace.dGL, diagJ, Matrix.diagonal_apply]
      split_ifs <;> simp)
  refine (ConjPlace.Tj_apply O' (Units.map (c : F →* F') ϖ) j _).trans ?_
  rw [ConjPlace.Tj_apply, ← e]
  refine if_congr ⟨?_, ?_⟩ rfl rfl
  · rintro ⟨a, ha, b, hb, H⟩
    obtain ⟨a, rfl⟩ := G.surjective a
    obtain ⟨b, rfl⟩ := G.surjective b
    rw [← map_mul, ← map_mul, G.apply_eq_iff_eq] at H
    exact ⟨a, (hK a).2 ha, b, (hK b).2 hb, H⟩
  · rintro ⟨a, ha, b, hb, H⟩
    exact ⟨_, (hK a).1 ha, _, (hK b).1 hb, by rw [H, map_mul, map_mul]⟩

variable {K M : Type} [Field K] [NumberField K] [Field M] [NumberField M] {n : ℕ}
  {v : HeightOneSpectrum (𝓞 K)} {w : HeightOneSpectrum (𝓞 M)}
  {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/- English proof (translation)
Set `G : GL (Fin n) (v.adicCompletion K) ≃* GL (Fin n) (w.adicCompletion M)` to `Units.mapEquiv c.mapMatrix.toMulEquiv`. Establish `hG : ∀ g, G g = GeneralLinearGroup.map c.toRingHom g` using `fun g => Units.ext rfl`. Establish `hGv : ∀ g i j, (G g).1 i j = c (g.1 i j)` using `fun _ _ _ => rfl`. Establish `hO : ∀ x, c x ∈ Ov M w ↔ x ∈ Ov K v` using `fun x => by`. Express the relevant statement in the definitionally equal form `Valued.v (c x) ≤ 1 ↔ Valued.v x ≤ 1`.

Rewrite using `[hc]`. Establish `hK : ∀ g, g ∈ KGL v n ↔ G g ∈ KGL w n` using `fun g => by`. Simplify using `only [KGL, GlobalTheory.AdelicU.mem_GLint_iff, ← map_inv, hGv, hO]`. Establish `hf : ∀ g y, T.toLinearMap ((ρ.comp G.symm.toMonoidHom) g y) = ρ' g (T.toLinearMap y)` using `fun g y => by`. Express the relevant statement in the definitionally equal form `T (ρ (G.symm g) y) = ρ' g (T y)`.

Rewrite using `[← hT, ← hG, MulEquiv.apply_symm_apply]`. Establish `hTj` using `Tj_map (n := n) c hK`. Establish `key0 : ∀ x, IsSatVecGL v ρ x B → IsSatVecGL w (ρ.comp G.symm.toMonoidHom) x B`. Introduce and unpack `x ⟨h0, hx, hB, hH⟩`. Use `⟨h0, (mem_fixed_comp_symm _ hK).2 hx, hB, fun ϖ' hϖ' j hj => ?_⟩` and prove the remaining obligations.

Take `⟨p, rfl⟩` from `c.surjective ϖ'`. Establish `hp : IsUnifV K v p` using `(hc p).symm.trans hϖ'`. Take `⟨ϖ, rfl⟩ : ∃ ϖ : (v.adicCompletion K)ˣ, ϖ = p` from `⟨Units.mk0 p fun e => by simp [IsUnifV, e] at hp, rfl⟩`. Rewrite using `[heckeVec_comp_symm _ hK (Tj_mem_hecke hϖ' j).1 hx, hq, ← hH _ hp j hj]`. Conclude with `congrArg (fun t => heckeVec ρ _ t x) (funext (hTj ϖ j))`.

Establish `key : ∀ x, IsSatVecGL v ρ x B → IsSatVecGL w ρ' (T x) B` using `fun x hx => (key0 x hx).map T.toLinearMap hf ((map_ne_zero_iff T T.injective).2 hx.1)`. Prove the components needed by the constructor for the conclusion. Take `⟨x, hx⟩` from `h.exists_vec`. Conclude with `(Submodule.ne_bot_iff _).2 ⟨_, (key x hx).2.1, (key x hx).1⟩`. Introduce `y hy h0`.

Take `⟨x, rfl⟩` from `T.surjective y`. Use `key x (h.2 x (GlobalTheory.LGrp.mem_fixed.2 fun k hk => T.injective ?_) ((map_ne_zero_iff T T.injective).1 h0))` and prove the remaining obligations. Use `GlobalTheory.LGrp.mem_fixed.1 hy _ ((hK k).1 hk)` as an intermediate fact. Rewrite `this` using `[hG, hT]`. Then use the resulting hypothesis.
-/
theorem hasSatGL_of_ringEquiv (c : v.adicCompletion K ≃+* w.adicCompletion M) (hc : ∀ x, Valued.v (c x) = Valued.v x)
    (hq : qV M w = qV K v) {ρ : Representation ℂ (GL (Fin n) (v.adicCompletion K)) V}
    {ρ' : Representation ℂ (GL (Fin n) (w.adicCompletion M)) W} (T : V ≃ₗ[ℂ] W)
    (hT : ∀ g x, ρ' (GeneralLinearGroup.map c.toRingHom g) (T x) = T (ρ g x)) {B : Multiset ℂˣ}
    (h : HasSatGL v ρ B) : HasSatGL w ρ' B := by
  let G : GL (Fin n) (v.adicCompletion K) ≃* GL (Fin n) (w.adicCompletion M) := Units.mapEquiv c.mapMatrix.toMulEquiv
  have hG : ∀ g, G g = GeneralLinearGroup.map c.toRingHom g := fun g => Units.ext rfl
  have hGv : ∀ g i j, (G g).1 i j = c (g.1 i j) := fun _ _ _ => rfl
  have hO : ∀ x, c x ∈ Ov M w ↔ x ∈ Ov K v := fun x => by
    change Valued.v (c x) ≤ 1 ↔ Valued.v x ≤ 1
    rw [hc]
  have hK : ∀ g, g ∈ KGL v n ↔ G g ∈ KGL w n := fun g => by
    simp only [KGL, GlobalTheory.AdelicU.mem_GLint_iff, ← map_inv, hGv, hO]
  have hf : ∀ g y, T.toLinearMap ((ρ.comp G.symm.toMonoidHom) g y) = ρ' g (T.toLinearMap y) := fun g y => by
    change T (ρ (G.symm g) y) = ρ' g (T y)
    rw [← hT, ← hG, MulEquiv.apply_symm_apply]
  have hTj := Tj_map (n := n) c hK
  have key0 : ∀ x, IsSatVecGL v ρ x B → IsSatVecGL w (ρ.comp G.symm.toMonoidHom) x B := by
    rintro x ⟨h0, hx, hB, hH⟩
    refine ⟨h0, (mem_fixed_comp_symm _ hK).2 hx, hB, fun ϖ' hϖ' j hj => ?_⟩
    obtain ⟨p, rfl⟩ := c.surjective ϖ'
    have hp : IsUnifV K v p := (hc p).symm.trans hϖ'
    obtain ⟨ϖ, rfl⟩ : ∃ ϖ : (v.adicCompletion K)ˣ, ϖ = p :=
      ⟨Units.mk0 p fun e => by simp [IsUnifV, e] at hp, rfl⟩
    rw [heckeVec_comp_symm _ hK (Tj_mem_hecke hϖ' j).1 hx, hq, ← hH _ hp j hj]
    exact congrArg (fun t => heckeVec ρ _ t x) (funext (hTj ϖ j))
  have key : ∀ x, IsSatVecGL v ρ x B → IsSatVecGL w ρ' (T x) B := fun x hx =>
    (key0 x hx).map T.toLinearMap hf ((map_ne_zero_iff T T.injective).2 hx.1)
  constructor
  · obtain ⟨x, hx⟩ := h.exists_vec
    exact (Submodule.ne_bot_iff _).2 ⟨_, (key x hx).2.1, (key x hx).1⟩
  · intro y hy h0
    obtain ⟨x, rfl⟩ := T.surjective y
    refine key x (h.2 x (GlobalTheory.LGrp.mem_fixed.2 fun k hk => T.injective ?_) ((map_ne_zero_iff T T.injective).1 h0))
    have := GlobalTheory.LGrp.mem_fixed.1 hy _ ((hK k).1 hk)
    rwa [hG, hT] at this

end Sat

variable {K M : Type} [Field K] [NumberField K] [IsTotallyComplex K] [Field M] [NumberField M] [IsTotallyComplex M]
  {a : ℕ} (e : K ≃+* M)

def mapL : Lie K a →L[ℝ] Lie M a :=
  LinearMap.toContinuousLinearMap
    { toFun := fun X i j => cInf e (X i j)
      map_add' := fun X Y => by funext i j; simp
      map_smul' := fun t X => by funext i j; exact cInf_smul e t _ }

def mapK (k : Kinf K a) : Kinf M a :=
  ⟨k.1.map (cInf e), Matrix.mem_unitaryGroup_iff.2 (by
    have h : star (k.1.map (cInf e)) = (star k.1).map (cInf e) := by
      ext i j : 1
      exact (cInf_star e _).symm
    rw [h, ← Matrix.map_mul, Matrix.mem_unitaryGroup_iff.1 k.2]
    exact Matrix.map_one _ (map_zero _) (map_one _))⟩

def mapOp : Op K a → Op M a
  | .fin k => .fin (GeneralLinearGroup.map (cFin e) k)
  | .cpt k => .cpt (mapK e k)
  | .lie X => .lie (mapL e X)

/- English proof (translation)
Consider the cases of `o with`. Consider the case `fin k => exact congrArg Op.fin (Units.ext (Matrix.ext fun i j => cFin_symm e _))`. Consider the case `cpt k => exact congrArg Op.cpt (Subtype.ext (Matrix.ext fun i j => cInf_symm e _))`. Consider the case `lie X => exact congrArg Op.lie (funext₂ fun i j => cInf_symm e _)`.
-/
theorem mapOp_symm (o : Op K a) : mapOp e.symm (mapOp e o) = o := by
  cases o with
  | fin k => exact congrArg Op.fin (Units.ext (Matrix.ext fun i j => cFin_symm e _))
  | cpt k => exact congrArg Op.cpt (Subtype.ext (Matrix.ext fun i j => cInf_symm e _))
  | lie X => exact congrArg Op.lie (funext₂ fun i j => cInf_symm e _)

variable (a) in

def mapA : GA K a →* GA M a := GeneralLinearGroup.map (cAd e)

/- English proof (translation)
Use extensionality with `i j : 2`. Conclude with `cAd_symm e _`.
-/
theorem mapA_symm (g : GA K a) : mapA a e.symm (mapA a e g) = g := by
  ext i j : 2
  exact cAd_symm e _

/- English proof (translation)
The claim follows from `ga_ext (by rw [mapA, map_map_comm _ _ _ _ (pInf_cAd e), pInf_infGL, pInf_infGL]) (by rw [mapA, map_map_comm _ _ _ _ (pFin_cAd e), pFin_infGL, pFin_infGL, map_one])`.
-/
theorem mapA_infGL (y : GL (Fin a) (Cinf K)) :
    mapA a e (infGL K a y) = infGL M a (GeneralLinearGroup.map (cInf e) y) :=
  ga_ext (by rw [mapA, map_map_comm _ _ _ _ (pInf_cAd e), pInf_infGL, pInf_infGL])
    (by rw [mapA, map_map_comm _ _ _ _ (pFin_cAd e), pFin_infGL, pFin_infGL, map_one])

/- English proof (translation)
The claim follows from `ga_ext (by rw [mapA, map_map_comm _ _ _ _ (pInf_cAd e), pInf_finGL, pInf_finGL, map_one]) (by rw [mapA, map_map_comm _ _ _ _ (pFin_cAd e), pFin_finGL, pFin_finGL])`.
-/
theorem mapA_finGL (k : GL (Fin a) (Af K)) : mapA a e (finGL K a k) = finGL M a (GeneralLinearGroup.map (cFin e) k) :=
  ga_ext (by rw [mapA, map_map_comm _ _ _ _ (pInf_cAd e), pInf_finGL, pInf_finGL, map_one])
    (by rw [mapA, map_map_comm _ _ _ _ (pFin_cAd e), pFin_finGL, pFin_finGL])

/- English proof (translation)
The claim follows from `Units.ext (Matrix.ext fun _ _ => cAd_algebraMap e _)`.
-/
theorem mapA_ratGL (γ : GL (Fin a) K) :
    mapA a e (ratGL K a γ) = ratGL M a (GeneralLinearGroup.map e.toRingHom γ) :=
  Units.ext (Matrix.ext fun _ _ => cAd_algebraMap e _)

/- English proof (translation)
Take `⟨u, hu⟩` from `id hx`. Take `rfl : x = toL u.val` from `hu.symm`. Rewrite using `[show mapL e (toL u.val) = toL (GeneralLinearGroup.map (cInf e) u).val from rfl, chart_val, chart_val, map_mul, mapA_infGL]`. Conclude with `⟨rfl, val_mem_invSet _⟩`.
-/
theorem chart_map (φ : GA M a → ℂ) (g : GA K a) {x : Lie K a} (hx : x ∈ invSet K a) :
    chart (fun g => φ (mapA a e g)) g x = chart φ (mapA a e g) (mapL e x) ∧ mapL e x ∈ invSet M a := by
  obtain ⟨u, hu⟩ := id hx
  obtain rfl : x = toL u.val := hu.symm
  rw [show mapL e (toL u.val) = toL (GeneralLinearGroup.map (cInf e) u).val from rfl,
    chart_val, chart_val, map_mul, mapA_infGL]
  exact ⟨rfl, val_mem_invSet _⟩

/- English proof (translation)
Introduce `g` and use `((hφ (mapA a e g)).comp (mapL (a := a) e).contDiff.contDiffOn fun _ hx => (chart_map e φ g hx).2).congr fun _ hx => (chart_map e φ g hx).1`.
-/
theorem map_mem_Sm {φ : GA M a → ℂ} (hφ : φ ∈ Sm M a) : (fun g => φ (mapA a e g)) ∈ Sm K a := fun g =>
  ((hφ (mapA a e g)).comp (mapL (a := a) e).contDiff.contDiffOn
    fun _ hx => (chart_map e φ g hx).2).congr fun _ hx => (chart_map e φ g hx).1

variable (a) in

def pull : Sm M a ≃ₗ[ℂ] Sm K a where
  toFun φ := ⟨fun g => φ.1 (mapA a e g), map_mem_Sm e φ.2⟩
  invFun φ := ⟨fun g => φ.1 (mapA a e.symm g), map_mem_Sm e.symm φ.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv φ := Subtype.ext <| funext fun g => congrArg φ.1 (mapA_symm e.symm g)
  right_inv φ := Subtype.ext <| funext fun g => congrArg φ.1 (mapA_symm e g)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem pull_apply (φ : Sm M a) (g : GA K a) : (pull a e φ).1 g = φ.1 (mapA a e g) := rfl

/- English proof (translation)
The claim follows from `Subtype.ext <| funext fun g => congrArg φ.1 (map_mul (mapA a e) g h)`.
-/
theorem rt_pull (h : GA K a) (φ : Sm M a) : rt K a h (pull a e φ) = pull a e (rt M a (mapA a e h) φ) :=
  Subtype.ext <| funext fun g => congrArg φ.1 (map_mul (mapA a e) g h)

/- English proof (translation)
Use `Subtype.ext <| funext fun g => ?_` and prove the remaining obligations. Establish `e1 : chart (pull a e φ).1 g =ᶠ[𝓝 (oneL K a)] chart φ.1 (mapA a e g) ∘ mapL e` using `Filter.eventually_of_mem (isOpen_invSet.mem_nhds isUnit_one) fun x hx => (chart_map e φ.1 g hx).1`. Establish `h1 : mapL e (oneL K a) = oneL M a`. Use function extensionality and compare the values at `i j`. Express the relevant statement in the definitionally equal form `cInf e ((1 : Matrix (Fin a) (Fin a) (Cinf K)) i j) = (1 : Matrix (Fin a) (Fin a) (Cinf M)) i j`.

Rewrite using `[Matrix.one_apply, Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> simp`. Establish `h2` using `HasFDerivAt.comp (oneL K a) (f := mapL e) (by rw [h1]; exact (differentiableAt_chart φ.2 (mapA a e g)).hasFDerivAt) (mapL e).hasFDerivAt`. Express the relevant statement in the definitionally equal form `fderiv ℝ _ _ X = fderiv ℝ _ _ _`. Rewrite using `[e1.fderiv_eq, h2.fderiv]`.

Both sides reduce to the same expression.
-/
theorem lie_pull (X : Lie K a) (φ : Sm M a) : lie K a X (pull a e φ) = pull a e (lie M a (mapL e X) φ) := by
  refine Subtype.ext <| funext fun g => ?_
  have e1 : chart (pull a e φ).1 g =ᶠ[𝓝 (oneL K a)] chart φ.1 (mapA a e g) ∘ mapL e :=
    Filter.eventually_of_mem (isOpen_invSet.mem_nhds isUnit_one) fun x hx => (chart_map e φ.1 g hx).1
  have h1 : mapL e (oneL K a) = oneL M a := by
    funext i j
    change cInf e ((1 : Matrix (Fin a) (Fin a) (Cinf K)) i j) = (1 : Matrix (Fin a) (Fin a) (Cinf M)) i j
    rw [Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have h2 := HasFDerivAt.comp (oneL K a) (f := mapL e)
    (by rw [h1]; exact (differentiableAt_chart φ.2 (mapA a e g)).hasFDerivAt) (mapL e).hasFDerivAt
  change fderiv ℝ _ _ X = fderiv ℝ _ _ _
  rw [e1.fderiv_eq, h2.fderiv]
  rfl

/- English proof (translation)
Consider the cases of `o with`. Consider the case `fin k => exact (rt_pull e _ φ).trans (by rw [mapA_finGL]; rfl)`. Consider the case `cpt k`. Establish `e1 : GeneralLinearGroup.map (cInf e) (Unitary.toUnits k) = Unitary.toUnits (mapK e k)` using `Units.ext rfl`. Conclude with `(rt_pull e (infGL K a (Unitary.toUnits k)) φ).trans (by rw [mapA_infGL, e1]; rfl)`.

Consider the case `lie X => exact lie_pull e X φ`.
-/
theorem act_pull (o : Op K a) (φ : Sm M a) : act o (pull a e φ) = pull a e (act (mapOp e o) φ) := by
  cases o with
  | fin k => exact (rt_pull e _ φ).trans (by rw [mapA_finGL]; rfl)
  | cpt k =>
    have e1 : GeneralLinearGroup.map (cInf e) (Unitary.toUnits k) = Unitary.toUnits (mapK e k) :=
      Units.ext rfl
    exact (rt_pull e (infGL K a (Unitary.toUnits k)) φ).trans (by rw [mapA_infGL, e1]; rfl)
  | lie X => exact lie_pull e X φ

/- English proof (translation)
Rewrite using `[act_pull]`. Conclude with `congrArg (fun o => pull a e (act o φ)) (mapOp_symm e.symm o).symm`.
-/
theorem pull_act (o : Op M a) (φ : Sm M a) : pull a e (act o φ) = act (mapOp e.symm o) (pull a e φ) := by
  rw [act_pull]
  exact congrArg (fun o => pull a e (act o φ)) (mapOp_symm e.symm o).symm

/- English proof (translation)
Establish `h2 : ∀ z, lieS K a i j (atEmb (τ.comp e.toRingHom) z) (pull a e φ) = pull a e (lieS M a i j (atEmb τ z) φ)` using `fun z => by`. Establish `e' : ∀ x, mapL e (toL (Matrix.single i j x)) = toL (Matrix.single i j (cInf e x))` using `fun x => by`. Use function extensionality and compare the values at `k l`. Express the relevant statement in the definitionally equal form `cInf e (Matrix.single i j x k l) = Matrix.single i j (cInf e x) k l`. Rewrite using `[Matrix.single_apply, Matrix.single_apply]`.

Apply the tactic sequence `split_ifs <;> simp`. Rewrite using `[lieS_apply, lie_pull, e', cInf_atEmb, lieS_apply]`. Simplify using `only [Eop, LinearMap.smul_apply, LinearMap.sub_apply, h2, map_smul, map_sub]`.
-/
theorem Eop_pull (τ : M →+* ℂ) (i j : Fin a) (φ : Sm M a) :
    Eop (τ.comp e.toRingHom) i j (pull a e φ) = pull a e (Eop τ i j φ) := by
  have h2 : ∀ z, lieS K a i j (atEmb (τ.comp e.toRingHom) z) (pull a e φ) =
      pull a e (lieS M a i j (atEmb τ z) φ) := fun z => by
    have e' : ∀ x, mapL e (toL (Matrix.single i j x)) = toL (Matrix.single i j (cInf e x)) := fun x => by
      funext k l
      change cInf e (Matrix.single i j x k l) = Matrix.single i j (cInf e x) k l
      rw [Matrix.single_apply, Matrix.single_apply]
      split_ifs <;> simp
    rw [lieS_apply, lie_pull, e', cInf_atEmb, lieS_apply]
  simp only [Eop, LinearMap.smul_apply, LinearMap.sub_apply, h2, map_smul, map_sub]

/- English proof (translation)
Establish `h` using `map_qdet ((pull a e).conjAlgEquiv ℂ).toAlgHom (Eop τ) (u + ((a : ℂ) - 1) / 2)`. Establish `e1 : (fun i j => ((pull a e).conjAlgEquiv ℂ).toAlgHom (Eop τ i j)) = Eop (τ.comp e.toRingHom)`. Use function extensionality and compare the values at `i j`. Use `LinearMap.ext fun ψ => ?_` and prove the remaining obligations. Take `⟨ψ, rfl⟩` from `(pull a e).surjective ψ`.

Rewrite using `[Eop_pull]`. Express the relevant statement in the definitionally equal form `pull a e (Eop τ i j ((pull a e).symm (pull a e ψ))) = _`. Rewrite using `[LinearEquiv.symm_apply_apply]`. Rewrite `h` using `[e1]`. Rewrite using `[cap, ← h, cap]`.

Generalize the expression as in `Formalism.REAL.qdet (Eop (a := a) τ) (u + ((a : ℂ) - 1) / 2) = z`. Express the relevant statement in the definitionally equal form `pull a e (z ((pull a e).symm (pull a e φ))) = _`. Rewrite using `[LinearEquiv.symm_apply_apply]`.
-/
theorem cap_pull (τ : M →+* ℂ) (u : ℂ) (φ : Sm M a) :
    cap (τ.comp e.toRingHom) u (pull a e φ) = pull a e (cap τ u φ) := by
  have h := map_qdet ((pull a e).conjAlgEquiv ℂ).toAlgHom (Eop τ) (u + ((a : ℂ) - 1) / 2)
  have e1 : (fun i j => ((pull a e).conjAlgEquiv ℂ).toAlgHom (Eop τ i j)) = Eop (τ.comp e.toRingHom) := by
    funext i j
    refine LinearMap.ext fun ψ => ?_
    obtain ⟨ψ, rfl⟩ := (pull a e).surjective ψ
    rw [Eop_pull]
    change pull a e (Eop τ i j ((pull a e).symm (pull a e ψ))) = _
    rw [LinearEquiv.symm_apply_apply]
  rw [e1] at h
  rw [cap, ← h, cap]
  generalize Formalism.REAL.qdet (Eop (a := a) τ) (u + ((a : ℂ) - 1) / 2) = z
  change pull a e (z ((pull a e).symm (pull a e φ))) = _
  rw [LinearEquiv.symm_apply_apply]

/- English proof (translation)
Rewrite using `[← cap_pull]`. Use `congr 2`. Use extensionality with `x`. Simplify using the standard rewrite rules.
-/
theorem cap_pull' (σ : K →+* ℂ) (u : ℂ) (φ : Sm M a) :
    cap σ u (pull a e φ) = pull a e (cap (σ.comp e.symm.toRingHom) u φ) := by
  rw [← cap_pull]
  congr 2
  ext x
  simp

/- English proof (translation)
Proceed by induction on `hz using Algebra.adjoin_induction with`. Consider the case `mem x hx`. Take `⟨τ, u, rfl⟩` from `hx`. Conclude with `⟨_, Algebra.subset_adjoin ⟨_, _, rfl⟩, cap_pull' e τ u⟩`. Consider the case `algebraMap c => exact ⟨_, Subalgebra.algebraMap_mem _ c, fun φ => by simp⟩`.

Consider the case `add x y _ _ hx hy`. Take `⟨x', h1, h2⟩` from `hx`. Take `⟨y', h3, h4⟩` from `hy`. Conclude with `⟨x' + y', add_mem h1 h3, fun φ => by simp [h2, h4]⟩`. Consider the case `mul x y _ _ hx hy`.

Take `⟨x', h1, h2⟩` from `hx`. Take `⟨y', h3, h4⟩` from `hy`. Conclude with `⟨x' * y', mul_mem h1 h3, fun φ => by simp [h2, h4]⟩`.
-/
theorem Zalg_pull {z : Module.End ℂ (Sm K a)} (hz : z ∈ Zalg K a) :
    ∃ z' ∈ Zalg M a, ∀ φ, z (pull a e φ) = pull a e (z' φ) := by
  induction hz using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨τ, u, rfl⟩ := hx
    exact ⟨_, Algebra.subset_adjoin ⟨_, _, rfl⟩, cap_pull' e τ u⟩
  | algebraMap c => exact ⟨_, Subalgebra.algebraMap_mem _ c, fun φ => by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨x', h1, h2⟩ := hx
    obtain ⟨y', h3, h4⟩ := hy
    exact ⟨x' + y', add_mem h1 h3, fun φ => by simp [h2, h4]⟩
  | mul x y _ _ hx hy =>
    obtain ⟨x', h1, h2⟩ := hx
    obtain ⟨y', h3, h4⟩ := hy
    exact ⟨x' * y', mul_mem h1 h3, fun φ => by simp [h2, h4]⟩

omit [IsTotallyComplex K] [IsTotallyComplex M] in

/- English proof (translation)
Establish `h1 : ∀ y : GL (Fin a) (Cinf K), ‖toL (GeneralLinearGroup.map (cInf e) y).val‖ ≤ ‖toL y.val‖` using `fun y => (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun j => (norm_cInf_le e _).trans ((norm_le_pi_norm (toL y.val i) j).trans (norm_le_pi_norm (toL y.val) i))`. Unfold `height`. Rewrite using `[← map_inv]`. Combine the linear relations using `[h1 y, h1 y⁻¹]`.
-/
theorem height_map_le (y : GL (Fin a) (Cinf K)) : height (GeneralLinearGroup.map (cInf e) y) ≤ height y := by
  have h1 : ∀ y : GL (Fin a) (Cinf K), ‖toL (GeneralLinearGroup.map (cInf e) y).val‖ ≤ ‖toL y.val‖ := fun y =>
    (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun j =>
      (norm_cInf_le e _).trans ((norm_le_pi_norm (toL y.val i) j).trans (norm_le_pi_norm (toL y.val) i))
  unfold height
  rw [← map_inv]
  linarith [h1 y, h1 y⁻¹]

/- English proof (translation)
Use `le_antisymm (height_map_le e y) (le_of_eq_of_le ?_ (height_map_le e.symm _))` and prove the remaining obligations. Conclude with `congrArg height (Units.ext (Matrix.ext fun i j => (cInf_symm e _).symm))`.
-/
theorem height_map (y : GL (Fin a) (Cinf K)) : height (GeneralLinearGroup.map (cInf e) y) = height y := by
  refine le_antisymm (height_map_le e y) (le_of_eq_of_le ?_ (height_map_le e.symm _))
  exact congrArg height (Units.ext (Matrix.ext fun i j => (cInf_symm e _).symm))

/- English proof (translation)
Rewrite using `[pull_apply, map_mul, mapA_ratGL, h.left, pull_apply] level := by`. Use `h.level.preimage (continuous_mapGL (cFin e) (continuous_cFin e)) using 1` and compare the differences between its conclusion and the goal. Use extensionality with `k`. Conclude with `(Eq.congr_left (act_pull e (.fin k) φ)).trans (pull a e).injective.eq_iff`. Use `kfin := by`.

Use `h.kfin` as an intermediate fact. Use `Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ (Set.range fun k => cptRep M a k φ)).map (pull a e).toLinearMap) (Submodule.span_le.2 ?_)` and prove the remaining obligations. Introduce and unpack `_ ⟨k, rfl⟩`. Conclude with `⟨_, Submodule.subset_span ⟨_, rfl⟩, (act_pull e (.cpt k) φ).symm⟩`. Use `zfin := by`.

Use `h.zfin` as an intermediate fact. Use `Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ ((fun z : Module.End ℂ (Sm M a) => z φ) '' Zalg M a)).map (pull a e).toLinearMap) (Submodule.span_le.2 ?_)` and prove the remaining obligations. Introduce and unpack `_ ⟨z, hz, rfl⟩`. Take `⟨z', h1, h2⟩` from `Zalg_pull e hz`. Conclude with `⟨_, Submodule.subset_span ⟨z', h1, rfl⟩, (h2 φ).symm⟩`.

Use `growth g := by`. Take `⟨C, N, h1⟩` from `h.growth (mapA a e g)`. Use `⟨C, N, fun y => ?_⟩` and prove the remaining obligations. Rewrite using `[pull_apply, map_mul, mapA_infGL, ← height_map e]`. Conclude with `h1 _`.
-/
theorem isAutForm_pull {φ : Sm M a} (h : IsAutForm φ) : IsAutForm (pull a e φ) where
  left γ g := by rw [pull_apply, map_mul, mapA_ratGL, h.left, pull_apply]
  level := by
    convert h.level.preimage (continuous_mapGL (cFin e) (continuous_cFin e)) using 1
    ext k
    exact (Eq.congr_left (act_pull e (.fin k) φ)).trans (pull a e).injective.eq_iff
  kfin := by
    have := h.kfin
    refine Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ (Set.range fun k => cptRep M a k φ)).map
      (pull a e).toLinearMap) (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    exact ⟨_, Submodule.subset_span ⟨_, rfl⟩, (act_pull e (.cpt k) φ).symm⟩
  zfin := by
    have := h.zfin
    refine Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ ((fun z : Module.End ℂ (Sm M a) => z φ) ''
      Zalg M a)).map (pull a e).toLinearMap) (Submodule.span_le.2 ?_)
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨z', h1, h2⟩ := Zalg_pull e hz
    exact ⟨_, Submodule.subset_span ⟨z', h1, rfl⟩, (h2 φ).symm⟩
  growth g := by
    obtain ⟨C, N, h1⟩ := h.growth (mapA a e g)
    refine ⟨C, N, fun y => ?_⟩
    rw [pull_apply, map_mul, mapA_infGL, ← height_map e]
    exact h1 _

/- English proof (translation)
Take `⟨y, rfl⟩` from `hx`. Conclude with `⟨fun p => e (y p), funext fun p => (cAd_algebraMap e (y p)).symm⟩`.
-/
theorem map_mem_ratN {r : ℕ} {x : BlockIx a r → Ad K} (hx : x ∈ ratN K a r) :
    (fun p => cAd e (x p)) ∈ ratN M a r := by
  obtain ⟨y, rfl⟩ := hx
  exact ⟨fun p => e (y p), funext fun p => (cAd_algebraMap e (y p)).symm⟩

open MeasureTheory in

/- English proof (translation)
Introduce `r h0 h1 _ _ μ 𝓕 hμ hF g`. Use `borelize (BlockIx a r → Ad M)`. Set `β : (BlockIx a r → Ad K) ≃ₜ+ (BlockIx a r → Ad M)` to `{ toFun := fun x p => cAd e (x p) invFun := fun x p => cAd e.symm (x p) left_inv := fun x => funext fun p => cAd_symm e _ right_inv := fun x => funext fun p => cAd_symm e.symm _ map_add' := fun x y => funext fun p => map_add (cAd e) _ _ continuous_toFun := continuous_pi fun p => …`. Set `q : ratN M a r ≃ ratN K a r` to `{ toFun := fun y => ⟨β.symm y, map_mem_ratN e.symm y.2⟩ invFun := fun x => ⟨β x, map_mem_ratN e x.2⟩ left_inv := fun y => Subtype.ext (β.apply_symm_apply y) right_inv := fun x => Subtype.ext (β.symm_apply_apply x) }`. Set `m` to `β.toHomeomorph.toMeasurableEquiv`.

Establish `h2` using `hφ r h0 h1 (μ.map m) (m '' 𝓕) (β.isAddHaarMeasure_map μ) (hF.image_of_equiv m.toEquiv (MeasurePreserving.symm m ⟨m.measurable, rfl⟩).quasiMeasurePreserving q fun y x => by`. Express the relevant statement in the definitionally equal form `β (β.symm y + x) = y + β x`. Rewrite using `[map_add, β.apply_symm_apply]) (mapA a e g)`. Rewrite `h2` using `[m.measurableEmbedding.setIntegral_map, m.injective.preimage_image]`. Rewrite using `[← h2]`.

Use `congr 1`. Use function extensionality and compare the values at `x`. Use `beta_reduce`. Rewrite using `[map_mul, mapA, map_unip]`. Both sides reduce to the same expression.
-/
theorem isCuspidal_pull {φ : GA M a → ℂ} (hφ : IsCuspidal φ) : IsCuspidal fun g => φ (mapA a e g) := by
  intro r h0 h1 _ _ μ 𝓕 hμ hF g
  borelize (BlockIx a r → Ad M)
  let β : (BlockIx a r → Ad K) ≃ₜ+ (BlockIx a r → Ad M) :=
    { toFun := fun x p => cAd e (x p)
      invFun := fun x p => cAd e.symm (x p)
      left_inv := fun x => funext fun p => cAd_symm e _
      right_inv := fun x => funext fun p => cAd_symm e.symm _
      map_add' := fun x y => funext fun p => map_add (cAd e) _ _
      continuous_toFun := continuous_pi fun p => (continuous_cAd e).comp (continuous_apply p)
      continuous_invFun := continuous_pi fun p => (continuous_cAd e.symm).comp (continuous_apply p) }
  let q : ratN M a r ≃ ratN K a r :=
    { toFun := fun y => ⟨β.symm y, map_mem_ratN e.symm y.2⟩
      invFun := fun x => ⟨β x, map_mem_ratN e x.2⟩
      left_inv := fun y => Subtype.ext (β.apply_symm_apply y)
      right_inv := fun x => Subtype.ext (β.symm_apply_apply x) }
  let m := β.toHomeomorph.toMeasurableEquiv
  have h2 := hφ r h0 h1 (μ.map m) (m '' 𝓕) (β.isAddHaarMeasure_map μ)
    (hF.image_of_equiv m.toEquiv (MeasurePreserving.symm m ⟨m.measurable, rfl⟩).quasiMeasurePreserving q fun y x => by
      change β (β.symm y + x) = y + β x
      rw [map_add, β.apply_symm_apply]) (mapA a e g)
  rw [m.measurableEmbedding.setIntegral_map, m.injective.preimage_image] at h2
  rw [← h2]
  congr 1
  funext x
  beta_reduce
  rw [map_mul, mapA, map_unip]
  rfl

def pullSub (π : CuspSub M a) : CuspSub K a where
  V := π.V.map (pull a e).toLinearMap
  cusp := by rintro _ ⟨φ, hφ, rfl⟩; exact ⟨isAutForm_pull e (π.cusp φ hφ).1, isCuspidal_pull e (π.cusp φ hφ).2⟩
  stable := by
    rintro o _ ⟨φ, hφ, rfl⟩
    exact ⟨_, π.stable _ φ hφ, (act_pull e o φ).symm⟩
  ne_bot h := π.ne_bot ((Submodule.map_eq_bot_iff (e := pull a e)).1 h)
  irred W hW hs := by
    have h := π.irred (W.comap (pull a e).toLinearMap) (fun φ hφ => by
      obtain ⟨ψ, h1, h2⟩ := hW hφ
      rwa [← (pull a e).injective h2]) fun o φ hφ => by
      change pull a e (act o φ) ∈ W
      rw [pull_act]
      exact hs _ _ hφ
    have e1 := Submodule.map_comap_eq_of_surjective (f := (pull a e).toLinearMap) (pull a e).surjective W
    exact h.imp (fun h => by rw [← e1, h, Submodule.map_bot]) fun h => by rw [← e1, h]

/- English proof (translation)
Use `⟨h.1, ?_⟩` and prove the remaining obligations. Introduce and unpack `u _ ⟨φ, hφ, rfl⟩`. Express the relevant statement in the definitionally equal form `cap σ u (pull a e φ) = _ • pull a e φ`. Rewrite using `[cap_pull', h.2 u φ hφ, map_smul]`.
-/
theorem hasInfChar_pullSub {π : CuspSub M a} {σ : K →+* ℂ} {m : Multiset ℂ}
    (h : π.HasInfChar (σ.comp e.symm.toRingHom) m) : (pullSub e π).HasInfChar σ m := by
  refine ⟨h.1, ?_⟩
  rintro u _ ⟨φ, hφ, rfl⟩
  change cap σ u (pull a e φ) = _ • pull a e φ
  rw [cap_pull', h.2 u φ hφ, map_smul]

/- English proof (translation)
Rewrite `h`, the goal using `[CG.hasSat_mk]`. Use `hasSatGL_of_ringEquiv (locEquiv hw.symm) (valued_cLoc hw.symm) (qV_eq hw.symm) ((pull a e).submoduleMap π.V) (fun g x => Subtype.ext ?_) h` and prove the remaining obligations. Use `Eq.trans ?_ (pull_act e (.fin (locGL M a w g)) x.1).symm` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `_ = act (.fin (GeneralLinearGroup.map (cFin e.symm) (locGL M a w g))) (pull a e x.1)`. Rewrite using `[cFin_locGL hw.symm]`.

Both sides reduce to the same expression.
-/
theorem hasSat_pullSub {π : CuspSub M a} {v : HeightOneSpectrum (𝓞 K)} {w : HeightOneSpectrum (𝓞 M)}
    (hw : Over e v w) {B : Multiset ℂˣ} (h : (CG.mk π).HasSat w B) : (CG.mk (pullSub e π)).HasSat v B := by
  rw [CG.hasSat_mk] at h ⊢
  refine hasSatGL_of_ringEquiv (locEquiv hw.symm) (valued_cLoc hw.symm) (qV_eq hw.symm)
    ((pull a e).submoduleMap π.V) (fun g x => Subtype.ext ?_) h
  refine Eq.trans ?_ (pull_act e (.fin (locGL M a w g)) x.1).symm
  change _ = act (.fin (GeneralLinearGroup.map (cFin e.symm) (locGL M a w g))) (pull a e x.1)
  rw [cFin_locGL hw.symm]
  rfl

/- English proof (translation)
Introduce `_ _ _ _ _ _ _ _ e _ π` and use `⟨pullSub e.symm π, fun _ _ h => hasInfChar_pullSub e.symm h, fun _ _ h => hasSat_pullSub e.symm (fun _ => Iff.rfl) h⟩`.
-/
theorem exists_transport : ∀ (K M : Type) [Field K] [NumberField K] [IsTotallyComplex K] [Field M] [NumberField M] [IsTotallyComplex M] (e : K ≃+* M) (a : ℕ) (π : CuspSub K a), ∃ π' : CuspSub M a, (∀ (τ : M →+* ℂ) (m : Multiset ℂ), π.HasInfChar (τ.comp e.toRingHom) m → π'.HasInfChar τ m) ∧ ∀ (v : HeightOneSpectrum (𝓞 K)) (B : Multiset ℂˣ), (CG.mk π).HasSat v B → (CG.mk π').HasSat (HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv e) v) B :=
  fun _ _ _ _ _ _ _ _ e _ π => ⟨pullSub e.symm π, fun _ _ h => hasInfChar_pullSub e.symm h,
    fun _ _ h => hasSat_pullSub e.symm (fun _ => Iff.rfl) h⟩

end GlobalTheory.IsoPull

end
