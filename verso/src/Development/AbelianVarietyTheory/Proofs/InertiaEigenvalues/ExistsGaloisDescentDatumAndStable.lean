import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotentialPhiSub
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisEqMulKisinInfTameSemidirectStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BKGal.GalDescent

variable {l : ℕ} [hl : Fact l.Prime] {a : ℕ} [NeZero a] {e : ℕ} [NeZero e]
  {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
  [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K]
  {t : Wq l a →ₐ[ℤ_[l]] O} {ϖ : PiSys l e}
  {ι : Type} [Fintype ι] [DecidableEq ι]
  {G : Type} [Group G] [TopologicalSpace G] [TameDescentExponentData K l e a]
  {P : PhiMod O K l e a ι} {T : LocLat G ℚ_[l] K O}

def colMat (w : ι → Vec K a ι) : ZMod a → Matrix ι ι K⟦X⟧ := fun τ => Matrix.of fun i j => w j τ i

omit [NeZero e] in

/- English proof (translation)
Use extensionality with `τ i : 2`. Simplify using `only [Descent.matAct_apply, colMat, Finset.sum_apply, Pi.smul_apply', ringAct_apply, Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.smul_apply, smul_eq_mul]`. Conclude with `Finset.sum_congr rfl fun j _ => mul_comm _ _`.
-/
theorem matAct_eq_sum (γ : TameGal K l e a) (w : ι → Vec K a ι) (v : Vec K a ι) :
    Descent.matAct γ (colMat w) v = ∑ j, ringAct γ (fun σ => v σ j) • w j := by
  ext τ i : 2
  simp only [Descent.matAct_apply, colMat, Finset.sum_apply, Pi.smul_apply', ringAct_apply, Matrix.mulVec,
    dotProduct, Matrix.of_apply, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

/- English proof (translation)
The claim follows from `mem_ME_of_mem_M (P.bas_mem_M j)`.
-/
theorem bas_mem_ME (j : ι) : (bas j : Vec K a ι) ∈ ME P := mem_ME_of_mem_M (P.bas_mem_M j)

/- English proof (translation)
Rewrite using `[matAct_eq_sum]`. Conclude with `Submodule.sum_mem _ fun j _ => P.smul_tot_mem_Mext (fun τ => (rot_A.invE).ringAct_mem γ (fun σ => mem_tot.1 v.2 σ j) τ) (w j).2`.
-/
theorem matAct_mem_ME (γ : TameGal K l e a) (w : ι → ME P) (v : ME P) :
    Descent.matAct γ (colMat fun j => (w j).1) v.1 ∈ ME P := by
  rw [matAct_eq_sum]
  exact Submodule.sum_mem _ fun j _ => P.smul_tot_mem_Mext
    (fun τ => (rot_A.invE).ringAct_mem γ (fun σ => mem_tot.1 v.2 σ j) τ) (w j).2

/- English proof (translation)
Introduce `f f' hf`. Establish `h1 : galOA O h (ϖ.iTot t K f') = ϖ.iTot t K f` using `hc f' f fun τ => by`. Rewrite using `[show (fun σ => ((f' σ : A O K) : K⟦X⟧)) = ringAct γ⁻¹ (fun σ => (f σ : K⟦X⟧)) from funext hf, ← AlgHom.mul_apply, ← map_mul, mul_inv_cancel, map_one, AlgHom.one_apply]`. Apply `inclO_injective` to reduce the goal to its premises. Rewrite using `[← h1, ← galOW_inclO, ← galOW_inclO, ← galOW_mul, inv_mul_cancel, galOW_one]`.
-/
theorem covers_inv {h : GQ l} {γ : TameGal K l e a} (hc : Covers K t ϖ h γ) : Covers K t ϖ h⁻¹ γ⁻¹ := by
  intro f f' hf
  have h1 : galOA O h (ϖ.iTot t K f') = ϖ.iTot t K f := hc f' f fun τ => by
    rw [show (fun σ => ((f' σ : A O K) : K⟦X⟧)) = ringAct γ⁻¹ (fun σ => (f σ : K⟦X⟧)) from funext hf,
      ← AlgHom.mul_apply, ← map_mul, mul_inv_cancel, map_one, AlgHom.one_apply]
  apply inclO_injective
  rw [← h1, ← galOW_inclO, ← galOW_inclO, ← galOW_mul, inv_mul_cancel, galOW_one]

/- English proof (translation)
Establish `: (⟨_, hv⟩ : ME P) = ∑ j, (⟨(fun τ => (c j τ : K⟦X⟧)) • (w j).1, P.smul_tot_mem_Mext (fun τ => (c j τ).2) (w j).2⟩ : ME P)` using `Subtype.ext (by`. Rewrite using `[Submodule.coe_sum])`. Rewrite using `[this, map_sum]`. Conclude with `Finset.sum_congr rfl fun j _ => toW_smul t ϖ P (c j) (w j) _ fun τ => rfl`.
-/
theorem toW_sum_smul (c : ι → ZMod a → invE l e (A O K)) (w : ι → ME P)
    (hv : (∑ j, (fun τ => (c j τ : K⟦X⟧)) • (w j).1) ∈ ME P) :
    toW t ϖ P ⟨_, hv⟩ = ∑ j, ϖ.iW t K (c j) • toW t ϖ P (w j) := by
  have : (⟨_, hv⟩ : ME P) = ∑ j, (⟨(fun τ => (c j τ : K⟦X⟧)) • (w j).1,
      P.smul_tot_mem_Mext (fun τ => (c j τ).2) (w j).2⟩ : ME P) := Subtype.ext (by
    rw [Submodule.coe_sum])
  rw [this, map_sum]
  exact Finset.sum_congr rfl fun j _ => toW_smul t ϖ P (c j) (w j) _ fun τ => rfl

/- English proof (translation)
Take `⟨v, hvm⟩` from `v`. Set `f : ι → ZMod a → invE l e (A O K)` to `fun j τ => ⟨v τ j, mem_tot.1 hvm τ j⟩`. Set `f' : ι → ZMod a → invE l e (A O K)` to `fun j τ => ⟨ringAct γ (fun σ => v σ j) τ, (rot_A.invE).ringAct_mem γ (fun σ => mem_tot.1 hvm σ j) τ⟩`. Establish `e1 : (∑ j, (fun τ => (f j τ : K⟦X⟧)) • ((⟨bas j, bas_mem_ME j⟩ : ME P) : Vec K a ι)) ∈ ME P`. Rewrite using `[← eq_sum_bas v]`.

Conclude with `hvm`. Establish `e2 : (∑ j, (fun τ => (f' j τ : K⟦X⟧)) • (w j).1) ∈ ME P`. Rewrite using `[← matAct_eq_sum]`. Conclude with `hv`. Establish `hv1 : toW t ϖ P ⟨v, hvm⟩ = toW t ϖ P ⟨_, e1⟩` using `congrArg _ (Subtype.ext (eq_sum_bas v))`.

Establish `hv2 : toW t ϖ P ⟨_, hv⟩ = toW t ϖ P ⟨_, e2⟩` using `congrArg _ (Subtype.ext (matAct_eq_sum γ _ v))`. Rewrite using `[hv1, hv2, toW_sum_smul, toW_sum_smul, map_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Ident.act_smul, hw, UnitModel.galOW_iW_of_covers t ϖ hc (f j) (f' j) fun τ => rfl]`.
-/
theorem act_toW_sum (I : Ident t ϖ P T) {s : GQ l} {g : G} {γ : TameGal K l e a} (hc : Covers K t ϖ s γ)
    (w : ι → ME P) (hw : ∀ j, I.act s g (toW t ϖ P ⟨bas j, bas_mem_ME j⟩) = toW t ϖ P (w j)) (v : ME P)
    (hv : Descent.matAct γ (colMat fun j => (w j).1) v.1 ∈ ME P) :
    I.act s g (toW t ϖ P v) = toW t ϖ P ⟨_, hv⟩ := by
  obtain ⟨v, hvm⟩ := v
  let f : ι → ZMod a → invE l e (A O K) := fun j τ => ⟨v τ j, mem_tot.1 hvm τ j⟩
  let f' : ι → ZMod a → invE l e (A O K) := fun j τ =>
    ⟨ringAct γ (fun σ => v σ j) τ, (rot_A.invE).ringAct_mem γ (fun σ => mem_tot.1 hvm σ j) τ⟩
  have e1 : (∑ j, (fun τ => (f j τ : K⟦X⟧)) • ((⟨bas j, bas_mem_ME j⟩ : ME P) : Vec K a ι)) ∈ ME P := by
    rw [← eq_sum_bas v]; exact hvm
  have e2 : (∑ j, (fun τ => (f' j τ : K⟦X⟧)) • (w j).1) ∈ ME P := by
    rw [← matAct_eq_sum]; exact hv
  have hv1 : toW t ϖ P ⟨v, hvm⟩ = toW t ϖ P ⟨_, e1⟩ := congrArg _ (Subtype.ext (eq_sum_bas v))
  have hv2 : toW t ϖ P ⟨_, hv⟩ = toW t ϖ P ⟨_, e2⟩ := congrArg _ (Subtype.ext (matAct_eq_sum γ _ v))
  rw [hv1, hv2, toW_sum_smul, toW_sum_smul, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Ident.act_smul, hw, UnitModel.galOW_iW_of_covers t ϖ hc (f j) (f' j) fun τ => rfl]

/- English proof (translation)
Establish `h1 : s (g'⁻¹ * g) ∈ ϖ.GfieldInf a` using `hone _ (by`. Rewrite using `[map_mul, map_inv, ← inv_mul_cancel γ]`. Conclude with `hmul _ _ _ _ (covers_inv hc') hc)`. Establish `h2 : g = g' * (g'⁻¹ * g)` using `(mul_inv_cancel_left g' g).symm`. Rewrite using `[h2, map_mul, Ident.act_mul, H1 _ h1]`.
-/
theorem act_eq_of_covers (I : Ident t ϖ P T) (s : G →* GQ l)
    (hmul : ∀ k k' γ γ', Covers K t ϖ k γ → Covers K t ϖ k' γ' → Covers K t ϖ (k * k') (γ * γ'))
    (hone : ∀ k, Covers K t ϖ k 1 → k ∈ ϖ.GfieldInf a)
    (H1 : ∀ g : G, s g ∈ ϖ.GfieldInf a → ∀ v : ME P, I.act (s g) g (toW t ϖ P v) = toW t ϖ P v)
    {g g' : G} {γ : TameGal K l e a} (hc : Covers K t ϖ (s g) γ) (hc' : Covers K t ϖ (s g') γ) (v : ME P) :
    I.act (s g) g (toW t ϖ P v) = I.act (s g') g' (toW t ϖ P v) := by
  have h1 : s (g'⁻¹ * g) ∈ ϖ.GfieldInf a := hone _ (by
    rw [map_mul, map_inv, ← inv_mul_cancel γ]
    exact hmul _ _ _ _ (covers_inv hc') hc)
  have h2 : g = g' * (g'⁻¹ * g) := (mul_inv_cancel_left g' g).symm
  rw [h2, map_mul, Ident.act_mul, H1 _ h1]

/- English proof (translation)
Use `choose gOf hgOf using hex`. Use `choose w hwM hw using fun γ j => H2 (gOf γ) γ (hgOf γ) ⟨bas j, bas_mem_ME j⟩ (P.bas_mem_M j)`. Establish `hact : ∀ γ (v : ME P), I.act (s (gOf γ)) (gOf γ) (toW t ϖ P v) = toW t ϖ P ⟨_, matAct_mem_ME γ (w γ) v⟩` using `fun γ v => act_toW_sum I (hgOf γ) (w γ) (hw γ) v _`. Establish `hone' : ∀ j, (w 1 j).1 = bas j` using `fun j => congrArg Subtype.val (toW_injective t ϖ P ((hw 1 j).symm.trans (H1 _ (hone _ (hgOf 1)) _)))`. Establish `hmul' : ∀ γ δ j, (w (γ * δ) j).1 = Descent.matAct γ (colMat fun k => (w γ k).1) (w δ j).1` using `fun γ δ j => congrArg Subtype.val (toW_injective t ϖ P (show toW t ϖ P (w (γ * δ) j) = toW t ϖ P ⟨_, matAct_mem_ME γ (w γ) (w δ j)⟩ by`.

Establish `hc : Covers K t ϖ (s (gOf γ * gOf δ)) (γ * δ)`. Rewrite using `[map_mul]`. Conclude with `hmul _ _ _ _ (hgOf γ) (hgOf δ)`. Rewrite using `[← hw, act_eq_of_covers I s hmul hone H1 (hgOf (γ * δ)) hc, map_mul, Ident.act_mul, hw, hact]))`. Establish `hcomm : ∀ γ j, Descent.matAct γ (colMat fun k => (w γ k).1) (P.phi (bas j)) = P.phi (w γ j).1` using `fun γ j => by`.

Establish `e1` using `hact γ ⟨P.phi (bas j), mem_ME_of_mem_L (P.phi_mem_L (P.bas_mem_M j))⟩`. Rewrite `e1` using `[toW_phi t ϖ P (P.bas_mem_M j), Ident.act_phiW]`. Establish `e2` using `toW_phi t ϖ P (hwM γ j)`. Establish `e3 : I.act (s (gOf γ)) (gOf γ) (toW t ϖ P ⟨bas j, mem_ME_of_mem_M (P.bas_mem_M j)⟩) = toW t ϖ P ⟨(w γ j).1, mem_ME_of_mem_M (hwM γ j)⟩` using `hw γ j`. Rewrite `e1` using `[e3, ← e2]`.

Conclude with `congrArg Subtype.val (toW_injective t ϖ P e1).symm`. Use `⟨Descent.ofMatrix P (fun γ => colMat fun j => (w γ j).1) (fun γ τ i j => mem_tot.1 (hwM γ j) τ i) (fun τ => ?_) (fun γ δ τ => ?_) (fun γ τ => ?_), fun g γ hc v v' hv' => ?_⟩` and prove the remaining obligations. Use extensionality with `i j`. Simplify using `only [colMat, Matrix.of_apply, hone', bas, Pi.single_apply, Matrix.one_apply]`. Use extensionality with `i j`.

Simplify using `only [colMat, Matrix.of_apply, hmul', Descent.matAct_apply, Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.map_apply]`. Use `Matrix.ext fun i j => ?_` and prove the remaining obligations. Use `congrFun (congrFun (hcomm γ j) τ) i` as an intermediate fact. Simplify using `only [Descent.matAct_apply, PhiMod.phi_bas, Matrix.col_apply] at this`. Simplify using `only [PhiMod.phi_apply, Matrix.mulVec, dotProduct, frobV_apply] at this`.

Simplify `this` using `only [colMat, Matrix.of_apply, Matrix.mul_apply, Matrix.map_apply]`. Rewrite using `[act_eq_of_covers I s hmul hone H1 hc (hgOf γ) v, hact]`. Conclude with `congrArg _ (Subtype.ext hv'.symm)`.
-/
theorem exists_desc (I : Ident t ϖ P T) (s : G →* GQ l)
    (hex : ∀ γ : TameGal K l e a, ∃ g : G, Covers K t ϖ (s g) γ)
    (hmul : ∀ k k' γ γ', Covers K t ϖ k γ → Covers K t ϖ k' γ' → Covers K t ϖ (k * k') (γ * γ'))
    (hone : ∀ k, Covers K t ϖ k 1 → k ∈ ϖ.GfieldInf a)
    (H1 : ∀ g : G, s g ∈ ϖ.GfieldInf a → ∀ v : ME P, I.act (s g) g (toW t ϖ P v) = toW t ϖ P v)
    (H2 : ∀ (g : G) (γ : TameGal K l e a), Covers K t ϖ (s g) γ → ∀ v : ME P, v.1 ∈ P.M →
      ∃ v' : ME P, v'.1 ∈ P.M ∧ I.act (s g) g (toW t ϖ P v) = toW t ϖ P v') :
    ∃ Δ : Descent P, IsGalDesc s I Δ := by
  choose gOf hgOf using hex
  choose w hwM hw using fun γ j => H2 (gOf γ) γ (hgOf γ) ⟨bas j, bas_mem_ME j⟩ (P.bas_mem_M j)
  have hact : ∀ γ (v : ME P), I.act (s (gOf γ)) (gOf γ) (toW t ϖ P v) =
      toW t ϖ P ⟨_, matAct_mem_ME γ (w γ) v⟩ :=
    fun γ v => act_toW_sum I (hgOf γ) (w γ) (hw γ) v _
  have hone' : ∀ j, (w 1 j).1 = bas j := fun j => congrArg Subtype.val (toW_injective t ϖ P
    ((hw 1 j).symm.trans (H1 _ (hone _ (hgOf 1)) _)))
  have hmul' : ∀ γ δ j, (w (γ * δ) j).1 = Descent.matAct γ (colMat fun k => (w γ k).1) (w δ j).1 :=
    fun γ δ j => congrArg Subtype.val (toW_injective t ϖ P (show toW t ϖ P (w (γ * δ) j) =
        toW t ϖ P ⟨_, matAct_mem_ME γ (w γ) (w δ j)⟩ by
      have hc : Covers K t ϖ (s (gOf γ * gOf δ)) (γ * δ) := by
        rw [map_mul]; exact hmul _ _ _ _ (hgOf γ) (hgOf δ)
      rw [← hw, act_eq_of_covers I s hmul hone H1 (hgOf (γ * δ)) hc, map_mul, Ident.act_mul, hw, hact]))
  have hcomm : ∀ γ j, Descent.matAct γ (colMat fun k => (w γ k).1) (P.phi (bas j)) = P.phi (w γ j).1 :=
    fun γ j => by
      have e1 := hact γ ⟨P.phi (bas j), mem_ME_of_mem_L (P.phi_mem_L (P.bas_mem_M j))⟩
      rw [toW_phi t ϖ P (P.bas_mem_M j), Ident.act_phiW] at e1
      have e2 := toW_phi t ϖ P (hwM γ j)
      have e3 : I.act (s (gOf γ)) (gOf γ) (toW t ϖ P ⟨bas j, mem_ME_of_mem_M (P.bas_mem_M j)⟩) =
          toW t ϖ P ⟨(w γ j).1, mem_ME_of_mem_M (hwM γ j)⟩ := hw γ j
      rw [e3, ← e2] at e1
      exact congrArg Subtype.val (toW_injective t ϖ P e1).symm
  refine ⟨Descent.ofMatrix P (fun γ => colMat fun j => (w γ j).1) (fun γ τ i j => mem_tot.1 (hwM γ j) τ i)
    (fun τ => ?_) (fun γ δ τ => ?_) (fun γ τ => ?_), fun g γ hc v v' hv' => ?_⟩
  · ext i j
    simp only [colMat, Matrix.of_apply, hone', bas, Pi.single_apply, Matrix.one_apply]
  · ext i j
    simp only [colMat, Matrix.of_apply, hmul', Descent.matAct_apply, Matrix.mul_apply, Matrix.mulVec,
      dotProduct, Matrix.map_apply]
  · refine Matrix.ext fun i j => ?_
    have := congrFun (congrFun (hcomm γ j) τ) i
    simp only [Descent.matAct_apply, PhiMod.phi_bas, Matrix.col_apply] at this
    simp only [PhiMod.phi_apply, Matrix.mulVec, dotProduct, frobV_apply] at this
    simpa only [colMat, Matrix.of_apply, Matrix.mul_apply, Matrix.map_apply] using this
  · rw [act_eq_of_covers I s hmul hone H1 hc (hgOf γ) v, hact]
    exact congrArg _ (Subtype.ext hv'.symm)

/- English proof (translation)
Establish `key : ∀ (r : OA l O) (d : ι → OA l O), inclL t ϖ P (r • d) = inclO l O r • inclL t ϖ P d` using `fun r d => by`. Rewrite using `[inclL_apply, inclL_apply, ← Matrix.mulVec_smul]`. Conclude with `congrArg _ (funext fun i => map_mul _ _ _)`. Establish `hcol : ∀ j, inclL t ϖ P (Pi.single j 1) = toW t ϖ P ⟨P.phi (bas j), mem_ME_of_mem_L (P.phi_mem_L (P.bas_mem_M j))⟩` using `fun j => by`. Rewrite using `[toW_of_mx t ϖ P _ (Pi.single j 1) fun τ => ?_, inclL_apply]`.

Use `congr 1 ext1 j'`. Distinguish the cases in `h : j' = j`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using `[h]`.

Use `show P.phi (bas j) τ = _`. Rewrite using `[PhiMod.phi_bas]`. Use `ext1 i`. Simplify using `only [Matrix.mulVec, dotProduct, Matrix.col_apply]`. Rewrite using `[Finset.sum_eq_single j (fun x _ hx => by simp [Pi.single_apply, hx]) (by simp)]`.

Simplify using the standard rewrite rules. Introduce and unpack `_ ⟨c, rfl⟩`. Rewrite using `[pi_eq_sum_univ' c, map_sum, map_sum]`. Use `Submodule.sum_mem _ fun j _ => ?_` and prove the remaining obligations. Rewrite using `[key, Ident.act_smul, galOW_inclO, hcol, hΔ g γ hc _ ⟨Δ.act γ (P.phi (bas j)), mem_ME_of_mem_L (Δ.act_mem_ext γ le_rfl rot_A (P.phi_mem_L (P.bas_mem_M j)))⟩ rfl]`.

Take `⟨c', hc'⟩` from `toW_mem_LA t ϖ P (Δ.act_mem_ext γ le_rfl rot_A (P.phi_mem_L (P.bas_mem_M j)))`. Rewrite using `[← hc', ← key]`. Conclude with `⟨_, rfl⟩`.
-/
theorem stable_of_desc (I : Ident t ϖ P T) (s : G →* GQ l) {Δ : Descent P} (hΔ : IsGalDesc s I Δ) {g : G}
    {γ : TameGal K l e a} (hc : Covers K t ϖ (s g) γ) : ∀ v ∈ LA t ϖ P, I.act (s g) g v ∈ LA t ϖ P := by
  have key : ∀ (r : OA l O) (d : ι → OA l O), inclL t ϖ P (r • d) = inclO l O r • inclL t ϖ P d := fun r d => by
    rw [inclL_apply, inclL_apply, ← Matrix.mulVec_smul]
    exact congrArg _ (funext fun i => map_mul _ _ _)
  have hcol : ∀ j, inclL t ϖ P (Pi.single j 1) =
      toW t ϖ P ⟨P.phi (bas j), mem_ME_of_mem_L (P.phi_mem_L (P.bas_mem_M j))⟩ := fun j => by
    rw [toW_of_mx t ϖ P _ (Pi.single j 1) fun τ => ?_, inclL_apply]
    · congr 1
      ext1 j'
      by_cases h : j' = j
      · subst h; simp
      · simp [h]
    · show P.phi (bas j) τ = _
      rw [PhiMod.phi_bas]
      ext1 i
      simp only [Matrix.mulVec, dotProduct, Matrix.col_apply]
      rw [Finset.sum_eq_single j (fun x _ hx => by simp [Pi.single_apply, hx]) (by simp)]
      simp
  rintro _ ⟨c, rfl⟩
  rw [pi_eq_sum_univ' c, map_sum, map_sum]
  refine Submodule.sum_mem _ fun j _ => ?_
  rw [key, Ident.act_smul, galOW_inclO, hcol, hΔ g γ hc _ ⟨Δ.act γ (P.phi (bas j)),
    mem_ME_of_mem_L (Δ.act_mem_ext γ le_rfl rot_A (P.phi_mem_L (P.bas_mem_M j)))⟩ rfl]
  obtain ⟨c', hc'⟩ := toW_mem_LA t ϖ P (Δ.act_mem_ext γ le_rfl rot_A (P.phi_mem_L (P.bas_mem_M j)))
  rw [← hc', ← key]
  exact ⟨_, rfl⟩

/- English proof (translation)
Substitute `hg` using the available equality. Introduce `v hv`. Rewrite using `[map_mul, Ident.act_mul]`. Conclude with `h₁ _ (stable_of_desc I s hΔ hc v hv)`.
-/
theorem stable_of_factor (I : Ident t ϖ P T) (s : G →* GQ l) {Δ : Descent P} (hΔ : IsGalDesc s I Δ)
    {g g₁ g₂ : G} (hg : g = g₁ * g₂) {γ : TameGal K l e a} (hc : Covers K t ϖ (s g₂) γ)
    (h₁ : ∀ v ∈ LA t ϖ P, I.act (s g₁) g₁ v ∈ LA t ϖ P) : ∀ v ∈ LA t ϖ P, I.act (s g) g v ∈ LA t ϖ P := by
  subst hg
  intro v hv
  rw [map_mul, Ident.act_mul]
  exact h₁ _ (stable_of_desc I s hΔ hc v hv)

end GlobalTheory.BKGal.GalDescent

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem gal_res_eq {l : ℕ} [Fact l.Prime] {a e : ℕ} [NeZero a] [NeZero e] {ϖ : PiSys l e} {LL : FinExt l} [HasUnr a LL]
    [TameDescentExponentData ↥LL.1 l e a] {ι : Type} [Fintype ι] [DecidableEq ι] {P : PhiMod ↥(OL LL) ↥LL.1 l e a ι}
    {T : QLat LL} (I : Ident (thetaW a LL) ϖ P T) (x : ↥(GK (ϖ.field a))) (v : ι → OW l ↥(OL LL)) :
    Ident.gal (T := resF T (ϖ.field a)) (I.res (inclG (ϖ.field a)) (continuous_subtype_val.subtype_mk _)) x v =
      I.act (sQ l (inclG (ϖ.field a) x)) (inclG (ϖ.field a) x) v := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coe_inclG {l : ℕ} [Fact l.Prime] (F : FinExt l) (x : ↥(GK F)) : sQ l (inclG F x) = x := rfl

/- English proof (translation)
Introduce `v hv` and use `by have h := (hst x).1 v hv rwa [gal_res_eq] at h`.
-/
theorem act_mem_LA_of_stable {l : ℕ} [Fact l.Prime] {a e : ℕ} [NeZero a] [NeZero e] {ϖ : PiSys l e} {LL : FinExt l}
    [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] {ι : Type} [Fintype ι] [DecidableEq ι]
    {P : PhiMod ↥(OL LL) ↥LL.1 l e a ι} {T : QLat LL} (I : Ident (thetaW a LL) ϖ P T)
    (hst : Ident.Stable (T := resF T (ϖ.field a)) (I.res (inclG (ϖ.field a)) (continuous_subtype_val.subtype_mk _)))
    (x : ↥(GK (ϖ.field a))) : ∀ v ∈ LA (thetaW a LL) ϖ P,
      I.act (sQ l (inclG (ϖ.field a) x)) (inclG (ϖ.field a) x) v ∈ LA (thetaW a LL) ϖ P := fun v hv => by
  have h := (hst x).1 v hv
  rwa [gal_res_eq] at h

open GlobalTheory.BKGal.GalDescent in

/- English proof (translation)
Introduce `l _ a e _ _ ϖ LL _ _ ι _ _ P T I H1 H2`. Take `⟨c1, c2, c3, -, c5, c6, -⟩` from `GlobalTheory.T.galois_eq_mul_kisinInf_tameSemidirect l a e ϖ LL`. Establish `hmem : ∀ k : GQ l, k ∈ GK (Formalism.MainNotions.ElementDenominator.qlExt l)` using `fun k => by`. Express the relevant statement in the definitionally equal form `k ∈ (⊥ : IntermediateField ℚ_[l] (Om l)).fixingSubgroup`. Rewrite using `[IntermediateField.fixingSubgroup_bot]`.

Discharge the goal by the elementary cases of `trivial`. Establish `hex : ∀ γ : TameGal ↥LL.1 l e a, ∃ g : Gl l, Covers ↥LL.1 (thetaW a LL) ϖ (sQ l g) γ` using `fun γ => by`. Take `⟨k, -, hk⟩` from `c3 γ`. Conclude with `⟨⟨k, hmem k⟩, hk⟩`. Take `⟨Δ, hΔ⟩` from `exists_desc I (sQ l) hex c5 (fun k hk => (c6 k).1 hk) H1 H2`.

Use `⟨⟨Δ, hΔ⟩, fun hst g => ?_⟩` and prove the remaining obligations. Use `choose hOf hhOf kOf hkOf hgOf using c1`. Use `choose γOf hγOf using c2`. Establish `e1 : g = inclG (ϖ.field a) ⟨hOf g, hhOf g⟩ * ⟨kOf g, hmem _⟩`. Apply `Subtype.ext` to reduce the goal to its premises.

Rewrite using `[Subgroup.coe_mul]`. Conclude with `(hgOf g).trans (congrArg (· * kOf g) (coe_inclG (ϖ.field a) ⟨hOf g, hhOf g⟩).symm)`. Conclude with `stable_of_factor I (sQ l) hΔ e1 (hγOf _ (hkOf g)) (act_mem_LA_of_stable I hst _)`.
-/
theorem GlobalTheory.BKGal.GalDescent.exists_galDesc_and_stable : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (I : Ident (thetaW a LL) ϖ P T), (∀ g : Gl l, sQ l g ∈ ϖ.GfieldInf a → ∀ v : ME P, I.act (sQ l g) g (toW (thetaW a LL) ϖ P v) = toW (thetaW a LL) ϖ P v) → (∀ (g : Gl l) (γ : TameGal ↥LL.1 l e a), Covers ↥LL.1 (thetaW a LL) ϖ (sQ l g) γ → ∀ v : ME P, v.1 ∈ P.M → ∃ v' : ME P, v'.1 ∈ P.M ∧ I.act (sQ l g) g (toW (thetaW a LL) ϖ P v) = toW (thetaW a LL) ϖ P v') → (∃ Δ : Descent P, IsGalDesc (sQ l) I Δ) ∧ (Ident.Stable (T := resF T (ϖ.field a)) (I.res (inclG (ϖ.field a)) (continuous_subtype_val.subtype_mk _)) → ∀ g : Gl l, ∀ v ∈ LA (thetaW a LL) ϖ P, I.act (sQ l g) g v ∈ LA (thetaW a LL) ϖ P) := by
  intro l _ a e _ _ ϖ LL _ _ ι _ _ P T I H1 H2
  obtain ⟨c1, c2, c3, -, c5, c6, -⟩ := GlobalTheory.T.galois_eq_mul_kisinInf_tameSemidirect l a e ϖ LL
  have hmem : ∀ k : GQ l, k ∈ GK (Formalism.MainNotions.ElementDenominator.qlExt l) := fun k => by
    change k ∈ (⊥ : IntermediateField ℚ_[l] (Om l)).fixingSubgroup
    rw [IntermediateField.fixingSubgroup_bot]
    trivial
  have hex : ∀ γ : TameGal ↥LL.1 l e a, ∃ g : Gl l, Covers ↥LL.1 (thetaW a LL) ϖ (sQ l g) γ := fun γ => by
    obtain ⟨k, -, hk⟩ := c3 γ
    exact ⟨⟨k, hmem k⟩, hk⟩
  obtain ⟨Δ, hΔ⟩ := exists_desc I (sQ l) hex c5 (fun k hk => (c6 k).1 hk) H1 H2
  refine ⟨⟨Δ, hΔ⟩, fun hst g => ?_⟩
  choose hOf hhOf kOf hkOf hgOf using c1
  choose γOf hγOf using c2
  have e1 : g = inclG (ϖ.field a) ⟨hOf g, hhOf g⟩ * ⟨kOf g, hmem _⟩ := by
    apply Subtype.ext
    rw [Subgroup.coe_mul]
    exact (hgOf g).trans (congrArg (· * kOf g) (coe_inclG (ϖ.field a) ⟨hOf g, hhOf g⟩).symm)
  exact stable_of_factor I (sQ l) hΔ e1 (hγOf _ (hkOf g)) (act_mem_LA_of_stable I hst _)
