import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MxAtOfMemDepLat
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FractionalIdealCompletionPropertiesAtPlace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PeriodIdealZpowCompletionAdeleConjIff
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LineVectorPairingMemInverseIdealCompletion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemMulInvIff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ModulusIdealOffS0Trivial
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open GlobalTheory.CharXFB

noncomputable section
namespace GlobalTheory.CharXFB.OffPl

variable {D : D7}

/- English proof (translation)
Proceed by induction on `hu using AddSubgroup.closure_induction with`. Consider the case `mem w hw`. Take `⟨α, hαi, hα, a, ha, s, hs, t, ht, rfl⟩` from `hw`. Proceed by induction on `hy using AddSubgroup.closure_induction with`. Consider the case `mem z hz`.

Take `⟨β, hβi, hβ, c, hc, x, hx, rfl⟩` from `hz`. Rewrite `hc` using `[Set.mem_singleton_iff]`. Substitute `hc` using the available equality. Rewrite using `[GlobalTheory.FinPl.LatMem.gen_mulVec]`. Take `⟨b, hb⟩` from `(hS.2 x).1 hx s hs`.

Use `AddSubgroup.subset_closure ⟨α * β, GlobalTheory.FinPl.LatMem.intAf_mul' hαi hβi, fun v hv => by rw [map_mul, hβ v hv, mul_zero], b • a, ?_, t, ht, ?_⟩` and prove the remaining obligations. Conclude with `Submodule.smul_mem (D.host.AA : Submodule (𝓞 D.host.E) D.host.E) b ha`. Use function extensionality and compare the values at `i`. Use `congr 1`. Rewrite using `[Algebra.smul_def]`.

Use `show _ = (b : D.host.E) * a * t i`. Rewrite using `[hb]`. Expand and normalize the polynomial expressions, which then agree. Consider the case `zero => rw [Matrix.mulVec_zero]`. Conclude with `zero_mem _`.

Consider the case `add z z' _ _ hz hz' => rw [Matrix.mulVec_add]`. Conclude with `add_mem hz hz'`. Consider the case `neg z _ hz => rw [Matrix.mulVec_neg]`. Conclude with `neg_mem hz`. Consider the case `zero => rw [Matrix.zero_mulVec]`.

Conclude with `zero_mem _`. Consider the case `add w w' _ _ hw hw' => rw [Matrix.add_mulVec]`. Conclude with `add_mem hw hw'`. Consider the case `neg w _ hw => rw [Matrix.neg_mulVec]`. Conclude with `neg_mem hw`.
-/
theorem latO_maps_at {S T : HSp D} {LS : Lat S} {LT : Lat T} (hS : IsSelfDualC S LS) {P Q : GlobalTheory.FinPl.Pl D → Prop}
    {u : WO S T} (hu : u ∈ latO S T (LS : Set _) (LT : Set _) P) {y : Fin S.rank → AE D} (hy : y ∈ latV S LS Q) :
    u *ᵥ y ∈ latA T LT Q := by
  induction hu using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hαi, hα, a, ha, s, hs, t, ht, rfl⟩ := hw
    induction hy using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨β, hβi, hβ, c, hc, x, hx, rfl⟩ := hz
      rw [Set.mem_singleton_iff] at hc
      subst hc
      rw [GlobalTheory.FinPl.LatMem.gen_mulVec]
      obtain ⟨b, hb⟩ := (hS.2 x).1 hx s hs
      refine AddSubgroup.subset_closure ⟨α * β, GlobalTheory.FinPl.LatMem.intAf_mul' hαi hβi,
        fun v hv => by rw [map_mul, hβ v hv, mul_zero], b • a, ?_, t, ht, ?_⟩
      · exact Submodule.smul_mem (D.host.AA : Submodule (𝓞 D.host.E) D.host.E) b ha
      · funext i
        congr 1
        rw [Algebra.smul_def]
        show _ = (b : D.host.E) * a * t i
        rw [hb]
        ring
    | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
    | add z z' _ _ hz hz' => rw [Matrix.mulVec_add]; exact add_mem hz hz'
    | neg z _ hz => rw [Matrix.mulVec_neg]; exact neg_mem hz
  | zero => rw [Matrix.zero_mulVec]; exact zero_mem _
  | add w w' _ _ hw hw' => rw [Matrix.add_mulVec]; exact add_mem hw hw'
  | neg w _ hw => rw [Matrix.neg_mulVec]; exact neg_mem hw

end GlobalTheory.CharXFB.OffPl

namespace GlobalTheory.CharXFB.OffPl
variable {D : D7}

/- English proof (translation)
Proceed by induction on `ht using AddSubgroup.closure_induction with`. Consider the case `mem w hw`. Take `⟨α, hαi, hα, a, ha, rfl⟩` from `hw`. Use `AddSubgroup.subset_closure ⟨α, hαi, fun w hw' => hα w hw', 1, rfl, fun k => a * d.a k q, ?_, ?_⟩` and prove the remaining obligations. Use `⟨0, Λ.zero_mem, Pi.single q a, fun p => ?_, ?_⟩` and prove the remaining obligations.

Distinguish the cases in `hp : p = q`. Substitute `hp` using the available equality. Simplify using `using ha`. Rewrite using `[Pi.single_eq_of_ne hp]`. Conclude with `(𝔟 p).zero_mem`.

Use function extensionality and compare the values at `k`. Simplify using `[Matrix.mulVec_single, mul_comm]`. Use function extensionality and compare the values at `k`. Simplify using `only [Pi.smul_apply, smul_eq_mul, ratV, one_mul]`. Use `show _ * (1 ⊗ₜ[D.host.F] d.a k q) = _`.

Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, mul_one]`. Consider the case `zero => rw [zero_smul]`. Conclude with `zero_mem _`. Consider the case `add x y _ _ hx hy => rw [add_smul]`. Conclude with `add_mem hx hy`.

Consider the case `neg x _ hx => rw [neg_smul]`. Conclude with `neg_mem hx`.
-/
theorem scaled_auxiliary_vector_mem_lattice_completion {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : GlobalTheory.ChiGrid.HermitianOrthogonalExtensionData A B c ε)
    (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (𝔟 : Fin c → FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) (q : Fin c)
    (v : GlobalTheory.FinPl.Pl D) {t : AE D} (ht : t ∈ GlobalTheory.SeeSaw.idV (𝔟 q) v) :
    t • ratV (fun k => d.a k q) ∈ latV B (d.lat Λ 𝔟) (· = v) := by
  induction ht using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hαi, hα, a, ha, rfl⟩ := hw
    refine AddSubgroup.subset_closure ⟨α, hαi, fun w hw' => hα w hw', 1, rfl, fun k => a * d.a k q, ?_, ?_⟩
    · refine ⟨0, Λ.zero_mem, Pi.single q a, fun p => ?_, ?_⟩
      · by_cases hp : p = q
        · subst hp; simpa using ha
        · rw [Pi.single_eq_of_ne hp]; exact (𝔟 p).zero_mem
      · funext k
        simp [Matrix.mulVec_single, mul_comm]
    · funext k
      simp only [Pi.smul_apply, smul_eq_mul, ratV, one_mul]
      show _ * (1 ⊗ₜ[D.host.F] d.a k q) = _
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  | zero => rw [zero_smul]; exact zero_mem _
  | add x y _ _ hx hy => rw [add_smul]; exact add_mem hx hy
  | neg x _ hx => rw [neg_smul]; exact neg_mem hx

/- English proof (translation)
Simplify using `only [hA, GlobalTheory.LineDual.pr, Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hA_eq_pr (T : HSp D) (y w : Fin T.rank → AE D) : hA T y w = GlobalTheory.LineDual.pr T w y := by
  simp only [hA, GlobalTheory.LineDual.pr, Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ => ?_
  ring

/- English proof (translation)
Simplify using `only [hA, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hA_smul_left (T : HSp D) (r : AE D) (y w : Fin T.rank → AE D) : hA T (r • y) w = r * hA T y w := by
  simp only [hA, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

/- English proof (translation)
Simplify using `only [hA, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hA_smul_right (T : HSp D) (r : AE D) (y w : Fin T.rank → AE D) : hA T y (r • w) = cA D r * hA T y w := by
  simp only [hA, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

/- English proof (translation)
Rewrite using `[hA_eq_pr]`. Conclude with `GlobalTheory.LineDual.pr_mem_intAt hM hw hy`.
-/
theorem hA_mem_intAt {T : HSp D} {M : Lat T} (hM : IsSelfDualC T M) {v : GlobalTheory.FinPl.Pl D} {y w : Fin T.rank → AE D}
    (hy : y ∈ latV T M (· = v)) (hw : w ∈ latV T M (· = v)) : hA T y w ∈ intAt D (· = v) := by
  rw [hA_eq_pr]
  exact GlobalTheory.LineDual.pr_mem_intAt hM hw hy

end GlobalTheory.CharXFB.OffPl

namespace GlobalTheory.CharXFB.OffPl
variable {D : D7}
open GlobalTheory.SeeSaw (idV FI conjFI)

/- English proof (translation)
Rewrite using `[map_inv₀, GlobalTheory.SeeSaw.conjFI_AA]`.
-/
theorem conjFI_AA_inv (D : D7) : conjFI D ((D.host.AA : FI D)⁻¹) = (D.host.AAbar : FI D)⁻¹ := by
  rw [map_inv₀, GlobalTheory.SeeSaw.conjFI_AA]

/- English proof (translation)
Take `⟨h1, h2, -, -, -, -, h7⟩` from `GlobalTheory.SeeSaw.idV_props D ψ hψ v`. Establish `hAb : (D.host.AAbar : FI D) ≠ 0`. Rewrite using `[← GlobalTheory.SeeSaw.conjFI_AA]`. Conclude with `(map_ne_zero (conjFI D)).2 (GlobalTheory.ChiGrid.StairConj.conj_AA_and_stA D).1.1`. Establish `hX : GlobalTheory.FinPlLoc.idem D (· = v) * hA T yT (u *ᵥ yS) ∈ idAt D (· = v)` using `Ideal.mul_mem_right _ _ (GlobalTheory.FinPlLoc.idem_mem_idAt _)`.

Establish `key : ∀ r ∈ idV 𝔟T v, ∀ s ∈ idV (D.host.AA : FI D)⁻¹ v, ∀ t ∈ idV 𝔟S v, r * (cA D s * (cA D t * hA T yT (u *ᵥ yS))) ∈ intAt D (· = v)`. Introduce `r hr s hs t ht`. Establish `e2 : u *ᵥ (t • yS) ∈ latA T ΛT (· = v)` using `latO_maps_at sdS hu (hyS t ht)`. Establish `e3 : s • (u *ᵥ (t • yS)) ∈ latV T ΛT (· = v)` using `((h7 T ΛT _).1 e2).2 s hs`. Establish `e4` using `hA_mem_intAt sdT (hyT r hr) e3`.

Rewrite `e4` using `[hA_smul_left, hA_smul_right, Matrix.mulVec_smul, hA_smul_right]`. Then use the resulting hypothesis. Establish `step1 : ∀ s ∈ idV (D.host.AA : FI D)⁻¹ v, ∀ t ∈ idV 𝔟S v, cA D s * (cA D t * (GlobalTheory.FinPlLoc.idem D (· = v) * hA T yT (u *ᵥ yS))) ∈ idV (1 * 𝔟T⁻¹) v`. Introduce `s hs t ht`. Establish `hmem` using `Ideal.mul_mem_left _ (cA D s) (Ideal.mul_mem_left _ (cA D t) hX)`. Use `(h2 𝔟T 1 h𝔟T one_ne_zero _ hmem).1 fun r hr => ?_` and prove the remaining obligations.

Establish `hr'` using `(GlobalTheory.FinPlLoc.mem_idAt_iff _ r).1 (GlobalTheory.LineDual.idV_mem_idAt hr)`. Establish `e : cA D s * (cA D t * (GlobalTheory.FinPlLoc.idem D (· = v) * hA T yT (u *ᵥ yS))) * r = r * (cA D s * (cA D t * hA T yT (u *ᵥ yS)))`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[e]`. Conclude with `(h1 _).2 (key r hr s hs t ht)`.

Establish `step2 : ∀ t ∈ idV 𝔟S v, cA D t * (GlobalTheory.FinPlLoc.idem D (· = v) * hA T yT (u *ᵥ yS)) ∈ idV (1 * 𝔟T⁻¹ * ((D.host.AAbar : FI D)⁻¹)⁻¹) v`. Introduce `t ht`. Establish `hmem` using `Ideal.mul_mem_left _ (cA D t) hX`. Use `(h2 _ _ (inv_ne_zero hAb) (mul_ne_zero one_ne_zero (inv_ne_zero h𝔟T)) _ hmem).1 fun a ha => ?_` and prove the remaining obligations. Establish `hs : cA D a ∈ idV (D.host.AA : FI D)⁻¹ v`.

Rewrite using `[GlobalTheory.SeeSaw.idV_cA_iff D v, GlobalTheory.SeeSaw.cA_cA, conjFI_AA_inv]`. Conclude with `ha`. Use `step1 (cA D a) hs t ht` as an intermediate fact. Rewrite `this` using `[GlobalTheory.SeeSaw.cA_cA]`. Rewrite using `[mul_comm _ a]`.

Conclude with `this`. Establish `hcS : conjFI D 𝔟S ≠ 0` using `(map_ne_zero (conjFI D)).2 h𝔟S`. Use `(h2 _ _ hcS (mul_ne_zero (mul_ne_zero one_ne_zero (inv_ne_zero h𝔟T)) (inv_ne_zero (inv_ne_zero hAb))) _ hX).1 fun a ha => ?_` and prove the remaining obligations. Establish `ht : cA D a ∈ idV 𝔟S v`. Rewrite using `[GlobalTheory.SeeSaw.idV_cA_iff D v, GlobalTheory.SeeSaw.cA_cA]`.

Conclude with `ha`. Use `step2 (cA D a) ht` as an intermediate fact. Rewrite `this` using `[GlobalTheory.SeeSaw.cA_cA]`. Rewrite using `[mul_comm _ a]`. Conclude with `this`.
-/
theorem pair_mem_idV (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) {S T : HSp D} {ΛS : Lat S} {ΛT : Lat T}
    (sdS : IsSelfDualC S ΛS) (sdT : IsSelfDualC T ΛT) {u : WO S T}
    (hu : u ∈ latO S T (ΛS : Set _) (ΛT : Set _) fun _ => True) {v : GlobalTheory.FinPl.Pl D} {yS : Fin S.rank → AE D}
    {yT : Fin T.rank → AE D} {𝔟S 𝔟T : FI D} (h𝔟S : 𝔟S ≠ 0) (h𝔟T : 𝔟T ≠ 0)
    (hyS : ∀ t ∈ idV 𝔟S v, t • yS ∈ latV S ΛS (· = v)) (hyT : ∀ r ∈ idV 𝔟T v, r • yT ∈ latV T ΛT (· = v)) :
    GlobalTheory.FinPlLoc.idem D (· = v) * hA T yT (u *ᵥ yS) ∈
      idV (1 * 𝔟T⁻¹ * ((D.host.AAbar : FI D)⁻¹)⁻¹ * (conjFI D 𝔟S)⁻¹) v := by
  obtain ⟨h1, h2, -, -, -, -, h7⟩ := GlobalTheory.SeeSaw.idV_props D ψ hψ v
  have hAb : (D.host.AAbar : FI D) ≠ 0 := by
    rw [← GlobalTheory.SeeSaw.conjFI_AA]
    exact (map_ne_zero (conjFI D)).2 (GlobalTheory.ChiGrid.StairConj.conj_AA_and_stA D).1.1
  have hX : GlobalTheory.FinPlLoc.idem D (· = v) * hA T yT (u *ᵥ yS) ∈ idAt D (· = v) :=
    Ideal.mul_mem_right _ _ (GlobalTheory.FinPlLoc.idem_mem_idAt _)
  have key : ∀ r ∈ idV 𝔟T v, ∀ s ∈ idV (D.host.AA : FI D)⁻¹ v, ∀ t ∈ idV 𝔟S v,
      r * (cA D s * (cA D t * hA T yT (u *ᵥ yS))) ∈ intAt D (· = v) := by
    intro r hr s hs t ht
    have e2 : u *ᵥ (t • yS) ∈ latA T ΛT (· = v) := latO_maps_at sdS hu (hyS t ht)
    have e3 : s • (u *ᵥ (t • yS)) ∈ latV T ΛT (· = v) := ((h7 T ΛT _).1 e2).2 s hs
    have e4 := hA_mem_intAt sdT (hyT r hr) e3
    rwa [hA_smul_left, hA_smul_right, Matrix.mulVec_smul, hA_smul_right] at e4
  have step1 : ∀ s ∈ idV (D.host.AA : FI D)⁻¹ v, ∀ t ∈ idV 𝔟S v,
      cA D s * (cA D t * (GlobalTheory.FinPlLoc.idem D (· = v) * hA T yT (u *ᵥ yS))) ∈ idV (1 * 𝔟T⁻¹) v := by
    intro s hs t ht
    have hmem := Ideal.mul_mem_left _ (cA D s) (Ideal.mul_mem_left _ (cA D t) hX)
    refine (h2 𝔟T 1 h𝔟T one_ne_zero _ hmem).1 fun r hr => ?_
    have hr' := (GlobalTheory.FinPlLoc.mem_idAt_iff _ r).1 (GlobalTheory.LineDual.idV_mem_idAt hr)
    have e : cA D s * (cA D t * (GlobalTheory.FinPlLoc.idem D (· = v) * hA T yT (u *ᵥ yS))) * r =
        r * (cA D s * (cA D t * hA T yT (u *ᵥ yS))) := by
      calc _ = cA D s * (cA D t * hA T yT (u *ᵥ yS)) * (GlobalTheory.FinPlLoc.idem D (· = v) * r) := by ring
        _ = _ := by rw [hr']; ring
    rw [e]
    exact (h1 _).2 (key r hr s hs t ht)
  have step2 : ∀ t ∈ idV 𝔟S v,
      cA D t * (GlobalTheory.FinPlLoc.idem D (· = v) * hA T yT (u *ᵥ yS)) ∈ idV (1 * 𝔟T⁻¹ * ((D.host.AAbar : FI D)⁻¹)⁻¹) v := by
    intro t ht
    have hmem := Ideal.mul_mem_left _ (cA D t) hX
    refine (h2 _ _ (inv_ne_zero hAb) (mul_ne_zero one_ne_zero (inv_ne_zero h𝔟T)) _ hmem).1 fun a ha => ?_
    have hs : cA D a ∈ idV (D.host.AA : FI D)⁻¹ v := by
      rw [GlobalTheory.SeeSaw.idV_cA_iff D v, GlobalTheory.SeeSaw.cA_cA, conjFI_AA_inv]; exact ha
    have := step1 (cA D a) hs t ht
    rw [GlobalTheory.SeeSaw.cA_cA] at this
    rw [mul_comm _ a]; exact this
  have hcS : conjFI D 𝔟S ≠ 0 := (map_ne_zero (conjFI D)).2 h𝔟S
  refine (h2 _ _ hcS (mul_ne_zero (mul_ne_zero one_ne_zero (inv_ne_zero h𝔟T)) (inv_ne_zero (inv_ne_zero hAb))) _ hX).1
    fun a ha => ?_
  have ht : cA D a ∈ idV 𝔟S v := by
    rw [GlobalTheory.SeeSaw.idV_cA_iff D v, GlobalTheory.SeeSaw.cA_cA]; exact ha
  have := step2 (cA D a) ht
  rw [GlobalTheory.SeeSaw.cA_cA] at this
  rw [mul_comm _ a]; exact this

end GlobalTheory.CharXFB.OffPl

namespace GlobalTheory.CharXFB.OffPl
variable {D : D7}
open GlobalTheory.SeeSaw (idV FI conjFI)

/- English proof (translation)
Use extensionality with `x`. Rewrite using `[GlobalTheory.SeeSaw.mem_conjFI, GlobalTheory.SeeSaw.conj_mem_conjFI]`.
-/
theorem conjFI_conjFI (D : D7) (𝔞 : FI D) : conjFI D (conjFI D 𝔞) = 𝔞 := by
  ext x; rw [GlobalTheory.SeeSaw.mem_conjFI, GlobalTheory.SeeSaw.conj_mem_conjFI]

/- English proof (translation)
Use extensionality with `x`. Rewrite using `[GlobalTheory.SeeSaw.mem_conjFI, ((GlobalTheory.ChiGrid.StairConj.conj_AA_and_stA D).2 T L P sc).2 x, bridge_star_holds D.R D.host]`.
-/
theorem conjFI_stA {T : Type} {L : LevCh D T} (P : GlobalTheory.ChiGrid.Places L) (sc : Consts) :
    conjFI D (P.stA sc) = P.stAbar sc := by
  ext x
  rw [GlobalTheory.SeeSaw.mem_conjFI, ((GlobalTheory.ChiGrid.StairConj.conj_AA_and_stA D).2 T L P sc).2 x, bridge_star_holds D.R D.host]

/- English proof (translation)
Rewrite using `[← conjFI_stA, conjFI_conjFI]`.
-/
theorem conjFI_stAbar {T : Type} {L : LevCh D T} (P : GlobalTheory.ChiGrid.Places L) (sc : Consts) :
    conjFI D (P.stAbar sc) = P.stA sc := by
  rw [← conjFI_stA, conjFI_conjFI]

/- English proof (translation)
Use extensionality with `x`. Rewrite using `[GlobalTheory.SeeSaw.mem_conjFI]`. Conclude with `(GlobalTheory.ChiGrid.StairConj.mem_coe_iff D (P.modul sc) x).symm`.
-/
theorem conjFI_modulBar {T : Type} {L : LevCh D T} (P : GlobalTheory.ChiGrid.Places L) (sc : Consts) :
    conjFI D ((P.modulBar sc : Ideal (𝓞 D.host.E)) : FI D) = ((P.modul sc : Ideal (𝓞 D.host.E)) : FI D) := by
  ext x
  rw [GlobalTheory.SeeSaw.mem_conjFI]
  exact (GlobalTheory.ChiGrid.StairConj.mem_coe_iff D (P.modul sc) x).symm

/- English proof (translation)
Rewrite using `[GlobalTheory.SeeSaw.idV_cA_iff D v _ s, conjFI_modulBar, GlobalTheory.ModulUnit.idV_modul_eq_one P sc v hv, GlobalTheory.SeeSaw.idV_cA_iff D v 1 s, map_one]`.
-/
theorem idV_modulBar_eq_one {T : Type} {L : LevCh D T} (P : GlobalTheory.ChiGrid.Places L) (sc : Consts) {v : GlobalTheory.FinPl.Pl D}
    (hv : v ∉ P.S0) (s : AE D) : s ∈ idV ((P.modulBar sc : Ideal (𝓞 D.host.E)) : FI D) v ↔ s ∈ idV 1 v := by
  rw [GlobalTheory.SeeSaw.idV_cA_iff D v _ s, conjFI_modulBar, GlobalTheory.ModulUnit.idV_modul_eq_one P sc v hv,
    GlobalTheory.SeeSaw.idV_cA_iff D v 1 s, map_one]

/- English proof (translation)
Establish `hp` using `p.2`. Unfold `GlobalTheory.ChiGrid.stairId`. Rewrite using `[map_mul, map_inv₀, map_pow, map_pow, hcA, hcB]`. Simplify using `only [Fin.val_rev, Fin.val_castLE]`. Take `⟨n, hn⟩ : ∃ n, 2 * σ + 2 - 1 - p.1 = n` from `⟨_, rfl⟩`.

Establish `e1 : 2 * (σ + 1) + 1 - 1 - (2 * (σ + 1) + 1 - 1 - (p.1 + 1)) = p.1 + 1` using `by omega`. Establish `e2 : 2 * (σ + 1) + 1 - 1 - (p.1 + 1) + 1 = n + 1` using `by omega`. Rewrite using `[hn, e1, e2]`. Simplify using `only [mul_inv, inv_inv, one_mul, pow_succ]`. Clear the denominators using the available nonvanishing facts.
-/
theorem stair_prod {A B : FI D} (hA : A ≠ 0) (hB : B ≠ 0) (hcA : conjFI D A = B) (hcB : conjFI D B = A)
    (σ : ℕ) (p : Fin (σ + 1)) (h1 : σ + 1 ≤ 2 * σ + 2 - 1) (h2 : σ + 1 ≤ 2 * (σ + 1) + 1 - 1) :
    1 * (GlobalTheory.ChiGrid.stairId A B (2 * σ + 2 - 1) (Fin.castLE h1 p))⁻¹ * ((D.host.AAbar : FI D)⁻¹)⁻¹ *
      (conjFI D (GlobalTheory.ChiGrid.stairId A B (2 * (σ + 1) + 1 - 1) (Fin.castLE h2 p).rev))⁻¹ = D.host.AAbar * A := by
  have hp := p.2
  unfold GlobalTheory.ChiGrid.stairId
  rw [map_mul, map_inv₀, map_pow, map_pow, hcA, hcB]
  simp only [Fin.val_rev, Fin.val_castLE]
  obtain ⟨n, hn⟩ : ∃ n, 2 * σ + 2 - 1 - p.1 = n := ⟨_, rfl⟩
  have e1 : 2 * (σ + 1) + 1 - 1 - (2 * (σ + 1) + 1 - 1 - (p.1 + 1)) = p.1 + 1 := by omega
  have e2 : 2 * (σ + 1) + 1 - 1 - (p.1 + 1) + 1 = n + 1 := by omega
  rw [hn, e1, e2]
  simp only [mul_inv, inv_inv, one_mul, pow_succ]
  field_simp

end GlobalTheory.CharXFB.OffPl

namespace GlobalTheory.CharXFB.OffPl
open GlobalTheory.SeeSaw (idV FI conjFI)

/- English proof (translation)
Introduce `D _ T L μ _ sc G W _ _ σ h h' u hu p v hv`. Take `⟨h1, h2, h3, -, h5, -, -⟩` from `GlobalTheory.SeeSaw.idV_props D W.ψ W.ψ_std v`. Establish `hA0 : G.pl.stA sc ≠ 0` using `((GlobalTheory.ChiGrid.StairConj.conj_AA_and_stA D).2 T L G.pl sc).1`. Establish `hB0 : G.pl.stAbar sc ≠ 0` using `by rw [← conjFI_stA]; exact (map_ne_zero _).2 hA0`. Establish `hAA : (D.host.AA : FI D) ≠ 0` using `(GlobalTheory.ChiGrid.StairConj.conj_AA_and_stA D).1.1`.

Establish `hAb : (D.host.AAbar : FI D) ≠ 0`. Rewrite using `[← GlobalTheory.SeeSaw.conjFI_AA]`. Conclude with `(map_ne_zero (conjFI D)).2 hAA`. Establish `hT1 : 1 ≤ 2 * σ + 2` using `by omega`. Establish `hS1 : 1 ≤ 2 * (σ + 1) + 1` using `by omega`.

Establish `hS2 : 2 * (σ + 1) + 1 ≤ D.R.m` using `by omega`. Establish `sdT : IsSelfDualC (G.V (.grid (2 * σ + 2) 0)) (G.Λ (.grid (2 * σ + 2) 0))` using `(G.isV (X := .grid (2 * σ + 2) 0) ⟨h', Nat.zero_le _⟩ (fun j hj => by injection hj with e; omega)).sd`. Establish `sdS : IsSelfDualC (negSp (G.V (.grid (2 * (σ + 1) + 1) 0))) (G.Λ (.grid (2 * (σ + 1) + 1) 0))` using `isSelfDualC_neg (G.isV (X := .grid (2 * (σ + 1) + 1) 0) ⟨hS2, Nat.zero_le _⟩ (fun j hj => by injection hj with e; omega)).sd`. Establish `hyS : ∀ t ∈ idV (stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * (σ + 1) + 1 - 1) (Fin.castLE (by omega) p : Fin (2 * (σ + 1) + 1 - 1)).rev) v, t • ratV (fun k => (G.colDec (2 * (σ + 1) + 1) hS1 hS2).a k (Fin.castLE (by omega) p : Fin (2 * (σ + 1) + 1 - 1)).rev) ∈ latV (negSp (G.V (. …`. Introduce `t ht`.

Use `scaled_auxiliary_vector_mem_lattice_completion (G.colDec _ hS1 hS2) (G.sp.P _).lat _ _ v ht` as an intermediate fact. Rewrite `this` using `[← G.sp.colLat _ hS1 hS2]`. Conclude with `this`. Establish `hyT : ∀ r ∈ idV (stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * σ + 2 - 1) (Fin.castLE (by omega) p : Fin (2 * σ + 2 - 1))) v, r • ratV (fun k => (G.colDec (2 * σ + 2) hT1 h').a k (Fin.castLE (by omega) p : Fin (2 * σ + 2 - 1))) ∈ latV (G.V (.grid (2 * σ + 2) 0)) (G.Λ (.grid (2 * σ …`. Introduce `r hr`.

Use `scaled_auxiliary_vector_mem_lattice_completion (G.colDec _ hT1 h') (G.sp.P _).lat _ _ v hr` as an intermediate fact. Rewrite `this` using `[← G.sp.colLat _ hT1 h']`. Conclude with `this`. Establish `hbS : stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * (σ + 1) + 1 - 1) (Fin.castLE (by omega) p : Fin (2 * (σ + 1) + 1 - 1)).rev ≠ 0`. Unfold `stairId`.

Conclude with `mul_ne_zero (pow_ne_zero _ hA0) (inv_ne_zero (pow_ne_zero _ hB0))`. Establish `hbT : stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * σ + 2 - 1) (Fin.castLE (by omega) p : Fin (2 * σ + 2 - 1)) ≠ 0`. Unfold `stairId`. Conclude with `mul_ne_zero (pow_ne_zero _ hA0) (inv_ne_zero (pow_ne_zero _ hB0))`. Establish `hX` using `pair_mem_idV W.ψ W.ψ_std sdS sdT hu.1 hbS hbT hyS hyT`.

Rewrite `hX` using `[stair_prod hA0 hB0 (conjFI_stA G.pl sc) (conjFI_stAbar G.pl sc)]`. Use `set X := GlobalTheory.FinPlLoc.idem D (· = v) * hA (G.V (.grid (2 * σ + 2) 0)) (ratV fun k => (G.colDec (2 * σ + 2) hT1 h').a k (Fin.castLE (by omega) p : Fin (2 * σ + 2 - 1))) (u *ᵥ ratV fun k => (G.colDec (2 * (σ + 1) + 1) hS1 hS2).a k (Fin.castLE (by omega) p : Fin (2 * (σ + 1 …`. Establish `hXI : X ∈ idAt D (· = v)` using `Ideal.mul_mem_right _ _ (GlobalTheory.FinPlLoc.idem_mem_idAt _)`. Establish `hmB : ((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : FI D) ≠ 0`. Introduce `h0`.

Use `conjFI_modulBar G.pl sc` as an intermediate fact. Rewrite `this` using `[h0, map_zero]`. Conclude with `(FractionalIdeal.coeIdeal_eq_zero.not.2 (G.pl.modul_ne_bot sc)) this.symm`. Establish `hX2 : X ∈ idV ((D.host.AA : FI D) * D.host.AAbar) v`. Establish `e : (D.host.AAbar : FI D) * G.pl.stA sc = (D.host.AA * D.host.AAbar) * ((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : FI D)⁻¹`.

Rewrite using `[GlobalTheory.ChiGrid.Places.stA]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `hX` using `[e]`. Establish `hall` using `(h2 _ _ hmB (mul_ne_zero hAA hAb) X hXI).2 hX`. Use `(h2 1 _ one_ne_zero (mul_ne_zero hAA hAb) X hXI).1 fun a ha => hall a ((idV_modulBar_eq_one G.pl sc hv a).2 ha)` as an intermediate fact.

Rewrite `this` using `[inv_one, mul_one]`. Then use the resulting hypothesis. Establish `hξ : D.host.xi0 ≠ 0` using `GlobalTheory.ChiGrid.cmHost_imaginaryGenerator_ne_zero`. Establish `hsI : GlobalTheory.FinPlLoc.idem D (· = v) * (incA D D.host.xi0 * hA (G.V (.grid (2 * σ + 2) 0)) (ratV fun k => (G.colDec (2 * σ + 2) hT1 h').a k (Fin.castLE (by omega) p : Fin (2 * σ + 2 - 1))) (u *ᵥ ratV fun k => (G.colDec (2 * (σ + 1) + 1) hS1 hS2).a k (Fin.castLE (by omega) p …` using `Ideal.mul_mem_right _ _ (GlobalTheory.FinPlLoc.idem_mem_idAt _)`. Establish `hdI : GlobalTheory.FinPlLoc.idem D (· = v) * (incA D D.host.xi0 * hA (G.V (.grid (2 * σ + 2) 0)) (ratV fun k => (G.colDec (2 * σ + 2) hT1 h').a k (Fin.castLE (by omega) p : Fin (2 * σ + 2 - 1))) (u *ᵥ ratV fun k => (G.colDec (2 * (σ + 1) + 1) hS1 hS2).a k (Fin.castLE (by omega) p …`. Rewrite using `[GlobalTheory.SeeSaw.dI, mul_assoc]`.

Use `(h3 _ _ hξ _).2 ⟨?_, hsI⟩` and prove the remaining obligations. Establish `e : incA D D.host.xi0⁻¹ * (GlobalTheory.FinPlLoc.idem D (· = v) * (incA D D.host.xi0 * hA (G.V (.grid (2 * σ + 2) 0)) (ratV fun k => (G.colDec (2 * σ + 2) hT1 h').a k (Fin.castLE (by omega) p : Fin (2 * σ + 2 - 1))) (u *ᵥ ratV fun k => (G.colDec (2 * (σ + 1) + 1) hS1 hS2).a k (Fi …`. Rewrite using `[hXdef]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[e]`.

Conclude with `hX2`. Use `(h5 _ hsI).1 hdI _ (GlobalTheory.FinPlLoc.idem_mem_intAt _)` as an intermediate fact. Rewrite `this` using `[mul_comm, ← mul_assoc, GlobalTheory.FinPlLoc.idem_mul_self]`. Then use the resulting hypothesis.
-/
theorem psi_pair_trivial_off : All fun {D} _ _ {sc} {G} W _ => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m) (u : WO (G.V (.grid (2 * σ + 2 + 1) 0)) (G.V (.grid (2 * σ + 2) 0))), u ∈ latRow G (2 * σ + 2) → ∀ (p : Fin (σ + 1)) (v : GlobalTheory.FinPl.Pl D), v ∉ G.pl.S0 → psiE W.ψ (GlobalTheory.FinPlLoc.idem D (· = v) * (incA D D.host.xi0 * hA _ (ratV fun k => (G.colDec (2 * σ + 2) (by omega) h').a k (Fin.castLE (by omega) p)) (u *ᵥ ratV fun k => (G.colDec (2 * (σ + 1) + 1) (by omega) (by omega)).a k (Fin.castLE (by omega) p : Fin (2 * (σ + 1) + 1 - 1)).rev))) = 1 := by
  intro D _ T L μ _ sc G W _ _ σ h h' u hu p v hv
  obtain ⟨h1, h2, h3, -, h5, -, -⟩ := GlobalTheory.SeeSaw.idV_props D W.ψ W.ψ_std v
  have hA0 : G.pl.stA sc ≠ 0 := ((GlobalTheory.ChiGrid.StairConj.conj_AA_and_stA D).2 T L G.pl sc).1
  have hB0 : G.pl.stAbar sc ≠ 0 := by rw [← conjFI_stA]; exact (map_ne_zero _).2 hA0
  have hAA : (D.host.AA : FI D) ≠ 0 := (GlobalTheory.ChiGrid.StairConj.conj_AA_and_stA D).1.1
  have hAb : (D.host.AAbar : FI D) ≠ 0 := by
    rw [← GlobalTheory.SeeSaw.conjFI_AA]; exact (map_ne_zero (conjFI D)).2 hAA
  have hT1 : 1 ≤ 2 * σ + 2 := by omega
  have hS1 : 1 ≤ 2 * (σ + 1) + 1 := by omega
  have hS2 : 2 * (σ + 1) + 1 ≤ D.R.m := by omega
  have sdT : IsSelfDualC (G.V (.grid (2 * σ + 2) 0)) (G.Λ (.grid (2 * σ + 2) 0)) :=
    (G.isV (X := .grid (2 * σ + 2) 0) ⟨h', Nat.zero_le _⟩ (fun j hj => by injection hj with e; omega)).sd
  have sdS : IsSelfDualC (negSp (G.V (.grid (2 * (σ + 1) + 1) 0))) (G.Λ (.grid (2 * (σ + 1) + 1) 0)) :=
    isSelfDualC_neg (G.isV (X := .grid (2 * (σ + 1) + 1) 0) ⟨hS2, Nat.zero_le _⟩
      (fun j hj => by injection hj with e; omega)).sd
  have hyS : ∀ t ∈ idV (stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * (σ + 1) + 1 - 1)
      (Fin.castLE (by omega) p : Fin (2 * (σ + 1) + 1 - 1)).rev) v,
      t • ratV (fun k => (G.colDec (2 * (σ + 1) + 1) hS1 hS2).a k (Fin.castLE (by omega) p : Fin (2 * (σ + 1) + 1 - 1)).rev)
        ∈ latV (negSp (G.V (.grid (2 * (σ + 1) + 1) 0))) (G.Λ (.grid (2 * (σ + 1) + 1) 0)) (· = v) := by
    intro t ht
    have := scaled_auxiliary_vector_mem_lattice_completion (G.colDec _ hS1 hS2) (G.sp.P _).lat _ _ v ht
    rw [← G.sp.colLat _ hS1 hS2] at this
    exact this
  have hyT : ∀ r ∈ idV (stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * σ + 2 - 1)
      (Fin.castLE (by omega) p : Fin (2 * σ + 2 - 1))) v,
      r • ratV (fun k => (G.colDec (2 * σ + 2) hT1 h').a k (Fin.castLE (by omega) p : Fin (2 * σ + 2 - 1)))
        ∈ latV (G.V (.grid (2 * σ + 2) 0)) (G.Λ (.grid (2 * σ + 2) 0)) (· = v) := by
    intro r hr
    have := scaled_auxiliary_vector_mem_lattice_completion (G.colDec _ hT1 h') (G.sp.P _).lat _ _ v hr
    rw [← G.sp.colLat _ hT1 h'] at this
    exact this
  have hbS : stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * (σ + 1) + 1 - 1)
      (Fin.castLE (by omega) p : Fin (2 * (σ + 1) + 1 - 1)).rev ≠ 0 := by
    unfold stairId; exact mul_ne_zero (pow_ne_zero _ hA0) (inv_ne_zero (pow_ne_zero _ hB0))
  have hbT : stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * σ + 2 - 1) (Fin.castLE (by omega) p : Fin (2 * σ + 2 - 1)) ≠ 0 := by
    unfold stairId; exact mul_ne_zero (pow_ne_zero _ hA0) (inv_ne_zero (pow_ne_zero _ hB0))
  have hX := pair_mem_idV W.ψ W.ψ_std sdS sdT hu.1 hbS hbT hyS hyT
  rw [stair_prod hA0 hB0 (conjFI_stA G.pl sc) (conjFI_stAbar G.pl sc)] at hX

  set X := GlobalTheory.FinPlLoc.idem D (· = v) * hA (G.V (.grid (2 * σ + 2) 0))
    (ratV fun k => (G.colDec (2 * σ + 2) hT1 h').a k (Fin.castLE (by omega) p : Fin (2 * σ + 2 - 1)))
    (u *ᵥ ratV fun k => (G.colDec (2 * (σ + 1) + 1) hS1 hS2).a k
      (Fin.castLE (by omega) p : Fin (2 * (σ + 1) + 1 - 1)).rev) with hXdef
  have hXI : X ∈ idAt D (· = v) := Ideal.mul_mem_right _ _ (GlobalTheory.FinPlLoc.idem_mem_idAt _)
  have hmB : ((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : FI D) ≠ 0 := by
    intro h0
    have := conjFI_modulBar G.pl sc
    rw [h0, map_zero] at this
    exact (FractionalIdeal.coeIdeal_eq_zero.not.2 (G.pl.modul_ne_bot sc)) this.symm
  have hX2 : X ∈ idV ((D.host.AA : FI D) * D.host.AAbar) v := by
    have e : (D.host.AAbar : FI D) * G.pl.stA sc =
        (D.host.AA * D.host.AAbar) * ((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : FI D)⁻¹ := by
      rw [GlobalTheory.ChiGrid.Places.stA]; ring
    rw [e] at hX
    have hall := (h2 _ _ hmB (mul_ne_zero hAA hAb) X hXI).2 hX
    have := (h2 1 _ one_ne_zero (mul_ne_zero hAA hAb) X hXI).1 fun a ha =>
      hall a ((idV_modulBar_eq_one G.pl sc hv a).2 ha)
    rwa [inv_one, mul_one] at this

  have hξ : D.host.xi0 ≠ 0 := GlobalTheory.ChiGrid.cmHost_imaginaryGenerator_ne_zero
  have hsI : GlobalTheory.FinPlLoc.idem D (· = v) * (incA D D.host.xi0 * hA (G.V (.grid (2 * σ + 2) 0))
      (ratV fun k => (G.colDec (2 * σ + 2) hT1 h').a k (Fin.castLE (by omega) p : Fin (2 * σ + 2 - 1)))
      (u *ᵥ ratV fun k => (G.colDec (2 * (σ + 1) + 1) hS1 hS2).a k
        (Fin.castLE (by omega) p : Fin (2 * (σ + 1) + 1 - 1)).rev)) ∈ idAt D (· = v) :=
    Ideal.mul_mem_right _ _ (GlobalTheory.FinPlLoc.idem_mem_idAt _)
  have hdI : GlobalTheory.FinPlLoc.idem D (· = v) * (incA D D.host.xi0 * hA (G.V (.grid (2 * σ + 2) 0))
      (ratV fun k => (G.colDec (2 * σ + 2) hT1 h').a k (Fin.castLE (by omega) p : Fin (2 * σ + 2 - 1)))
      (u *ᵥ ratV fun k => (G.colDec (2 * (σ + 1) + 1) hS1 hS2).a k
        (Fin.castLE (by omega) p : Fin (2 * (σ + 1) + 1 - 1)).rev)) ∈ idV (GlobalTheory.SeeSaw.dI D) v := by
    rw [GlobalTheory.SeeSaw.dI, mul_assoc]
    refine (h3 _ _ hξ _).2 ⟨?_, hsI⟩
    have e : incA D D.host.xi0⁻¹ * (GlobalTheory.FinPlLoc.idem D (· = v) * (incA D D.host.xi0 * hA (G.V (.grid (2 * σ + 2) 0))
      (ratV fun k => (G.colDec (2 * σ + 2) hT1 h').a k (Fin.castLE (by omega) p : Fin (2 * σ + 2 - 1)))
      (u *ᵥ ratV fun k => (G.colDec (2 * (σ + 1) + 1) hS1 hS2).a k
        (Fin.castLE (by omega) p : Fin (2 * (σ + 1) + 1 - 1)).rev))) = X := by
      rw [hXdef]
      calc _ = incA D (D.host.xi0⁻¹ * D.host.xi0) * X := by rw [hXdef, map_mul]; ring
        _ = X := by rw [inv_mul_cancel₀ hξ, map_one, one_mul]
    rw [e]; exact hX2
  have := (h5 _ hsI).1 hdI _ (GlobalTheory.FinPlLoc.idem_mem_intAt _)
  rwa [mul_comm, ← mul_assoc, GlobalTheory.FinPlLoc.idem_mul_self] at this

end GlobalTheory.CharXFB.OffPl
